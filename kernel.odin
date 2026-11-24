// Minimal Lean 4 kernel PoC in Odin.
// Reads a lean4export NDJSON file (format 3.1.0) and type-checks
// axioms / definitions / theorems / opaques built from Sort, Pi, Lambda, App,
// Let, Proj and constants (with universe levels), plus inductive types with
// their recursors (iota reduction, K-like reduction, structure eta, projections).
// Nat literals (GMP-style shortcuts) and Quot are supported; the four Quot constants
// are trusted (type-checked, not compared to the canonical statements). String
// literals are typed but never expanded to String.mk.
// Recursors exported by Lean are type-checked and used, but NOT regenerated
// from the inductive declaration; universe-level constraints of inductive
// types are NOT checked (strict positivity is).
package main

import "core:encoding/json"
import "core:fmt"
import "core:unicode/utf8"
import "core:math/big"
import "core:os"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------- data

Level_Kind :: enum { Zero, Succ, Max, IMax, Param }
Level :: struct { kind: Level_Kind, a, b: int } // Param: a = name id

Expr_Kind :: enum { BVar, FVar, Sort, Const, App, Lam, Pi, Let, MData, Proj, NatLit, StrLit, Unsupported }
Expr :: struct {
	kind:       Expr_Kind,
	a, b, c, d: int,   // meaning depends on kind (see mk_* below)
	lbr:        int,   // loose bvar range
	us:         []int, // Const: level ids
}

Decl_Kind :: enum { Axiom, Def, Thm, Opaque, Induct, Ctor, Rec, Quot }
Rule :: struct { ctor, nfields, rhs: int }
Decl :: struct {
	kind:    Decl_Kind,
	lparams: []int,
	type:    int,
	value:   int,
	height:  int,  // unfolding height; -1 = never unfold
	// inductive / constructor / recursor data
	nparams, nindices, nmotives, nminors: int,
	ctors:   []int, // Induct: constructor names
	induct:  int,   // Ctor: its inductive type
	nfields: int,   // Ctor
	rules:   []Rule,// Rec
	k:       bool,  // Rec: K-like
	is_rec:  bool,  // Induct
	qkind:   int,   // Quot: 0 type, 1 mk, 2 lift, 3 ind
}

names:   [dynamic]string
lit_strs: [dynamic]string // literal payloads: decimal digits (NatLit) or raw text (StrLit)
levels:  [dynamic]Level
exprs:   [dynamic]Expr
env:     map[int]Decl
fv_type: [dynamic]int // fvar id -> type
fv_name: [dynamic]int

Kernel_Error :: struct { msg: string }
failure: Maybe(string) // first error of the current declaration

fail :: proc(format: string, args: ..any) -> bool {
	if failure == nil do failure = fmt.aprintf(format, ..args)
	return false
}

// ---------------------------------------------------------------- levels

level_hc: map[Level]int

add_level :: proc(l: Level) -> int {
	if id, ok := level_hc[l]; ok do return id
	append(&levels, l)
	level_hc[l] = len(levels) - 1
	return len(levels) - 1
}

level_str :: proc(l: int) -> string {
	lv := levels[l]
	switch lv.kind {
	case .Zero:  return "0"
	case .Succ:  return fmt.aprintf("S(%s)", level_str(lv.a))
	case .Max:   return fmt.aprintf("max(%s,%s)", level_str(lv.a), level_str(lv.b))
	case .IMax:  return fmt.aprintf("imax(%s,%s)", level_str(lv.a), level_str(lv.b))
	case .Param: return fmt.aprintf("%s", names[lv.a])
	}
	return "?"
}

level_never_zero :: proc(l: int) -> bool {
	lv := levels[l]
	switch lv.kind {
	case .Succ:  return true
	case .Max:   return level_never_zero(lv.a) || level_never_zero(lv.b)
	case .IMax:  return level_never_zero(lv.b)
	case .Zero, .Param: return false
	}
	return false
}

Term :: struct { atom: string, off: int } // atom "" = zero

collect_terms :: proc(l: int, k: int, out: ^[dynamic]Term) {
	lv := levels[l]
	switch lv.kind {
	case .Zero:  append(out, Term{"", k})
	case .Succ:  collect_terms(lv.a, k + 1, out)
	case .Max:   collect_terms(lv.a, k, out); collect_terms(lv.b, k, out)
	case .Param: append(out, Term{names[lv.a], k})
	case .IMax:
		if level_never_zero(lv.b) {
			collect_terms(lv.a, k, out); collect_terms(lv.b, k, out)
		} else if is_zero_level(lv.b) {
			append(out, Term{"", k})
		} else if is_zero_level(lv.a) {
			collect_terms(lv.b, k, out)
		} else if levels[lv.a].kind == .Succ && levels[levels[lv.a].a].kind == .Zero {
			collect_terms(lv.b, k, out)
		} else if level_equiv(lv.a, lv.b) {
			collect_terms(lv.a, k, out)
		} else {
			append(out, Term{fmt.aprintf("imax(%s,%s)", canon_level(lv.a), canon_level(lv.b)), k})
		}
	}
}

// conservative a <= b on normalized levels (never accepts a false inequality)
level_leq :: proc(a, b: int) -> bool {
	if level_leq_syn(a, b) do return true
	return level_sem(a, b, true)
}

// Semantic fallback: compare on every assignment of the parameters to 0..depth+2.
sem_memo: map[[3]int]bool
sem_n: int
nosem: string
nopf: string

level_eval :: proc(l: int, ps: []int, vs: []int) -> int {
	lv := levels[l]
	switch lv.kind {
	case .Zero: return 0
	case .Succ: return level_eval(lv.a, ps, vs) + 1
	case .Max:  return max(level_eval(lv.a, ps, vs), level_eval(lv.b, ps, vs))
	case .IMax:
		y := level_eval(lv.b, ps, vs)
		return y == 0 ? 0 : max(level_eval(lv.a, ps, vs), y)
	case .Param:
		for p, i in ps do if p == lv.a do return vs[i]
	}
	return 0
}

level_collect :: proc(l: int, ps: ^[dynamic]int, depth: ^int, cur: int) {
	lv := levels[l]
	switch lv.kind {
	case .Zero: depth^ = max(depth^, cur)
	case .Succ: level_collect(lv.a, ps, depth, cur + 1)
	case .Max, .IMax: level_collect(lv.a, ps, depth, cur); level_collect(lv.b, ps, depth, cur)
	case .Param:
		depth^ = max(depth^, cur)
		for p in ps^ do if p == lv.a do return
		append(ps, lv.a)
	}
}

level_sem :: proc(a, b: int, leq: bool) -> bool {
	sem_n += 1
	if nosem == (leq ? "leq" : "eq") || nosem == "all" do return false
	if trace_on && sem_n % 20000 == 0 { fmt.eprintfln("sem call %d: %s <=? %s", sem_n, canon_level(a), canon_level(b)) }
	k := [3]int{a, b, leq ? 1 : 0}
	if r, ok := sem_memo[k]; ok do return r
	ps := make([dynamic]int)
	defer delete(ps)
	depth := 0
	level_collect(a, &ps, &depth, 0)
	level_collect(b, &ps, &depth, 0)
	res := false
	if len(ps) <= 5 {
		res = true
		top := depth + 2
		vs := make([]int, len(ps))
		defer delete(vs)
		total := 1
		for _ in ps do total *= top + 1
		if trace_on || total > 5000 { fmt.eprintfln("sem ps=%d top=%d total=%d", len(ps), top, total) }
		for n in 0 ..< total {
			m := n
			for i in 0 ..< len(ps) { vs[i] = m % (top + 1); m /= top + 1 }
			x, y := level_eval(a, ps[:], vs), level_eval(b, ps[:], vs)
			if leq ? x > y : x != y { res = false; break }
		}
	}
	sem_memo[k] = res
	return res
}

level_leq_syn :: proc(a, b: int) -> bool {
	if level_equiv_syn(a, b) do return true
	// imax x y <= max x y, so it suffices to bound both parts
	if levels[a].kind == .Max || levels[a].kind == .IMax {
		return level_leq_syn(levels[a].a, b) && level_leq_syn(levels[a].b, b)
	}
	ma := normalize_level(a)
	mb := normalize_level(b)
	defer delete(ma)
	defer delete(mb)
	for atom, off in ma {
		if atom == "" {
			found := false
			for _, v in mb do if v >= off { found = true }
			if !found do return false
		} else {
			v, ok := mb[atom]
			if !ok || v < off do return false
		}
	}
	return true
}

is_zero_level :: proc(l: int) -> bool {
	if levels[l].kind == .Zero do return true
	return canon_level(l) == "+0"
}

canon_memo: map[int]string

canon_level :: proc(l: int) -> string {
	if r, ok := canon_memo[l]; ok do return r
	r := canon_level_raw(l)
	canon_memo[l] = r
	return r
}

canon_level_raw :: proc(l: int) -> string {
	m := normalize_level(l)
	defer delete(m)
	keys := make([dynamic]string)
	defer delete(keys)
	for k, v in m do append(&keys, fmt.aprintf("%s+%d", k, v))
	slice.sort(keys[:])
	return strings.join(keys[:], "|")
}

normalize_level :: proc(l: int) -> map[string]int {
	ts: [dynamic]Term
	defer delete(ts)
	collect_terms(l, 0, &ts)
	m := make(map[string]int)
	for t in ts {
		if t.atom == "" do continue
		if cur, ok := m[t.atom]; !ok || t.off > cur do m[t.atom] = t.off
	}
	zero := -1
	for t in ts do if t.atom == "" && t.off > zero { zero = t.off }
	maxoff := -1
	for _, v in m do if v > maxoff { maxoff = v }
	if zero > maxoff && zero >= 0 do m[""] = zero
	return m
}

level_equiv_syn :: proc(a, b: int) -> bool {
	if a == b do return true
	return canon_level(a) == canon_level(b)
}
level_equiv :: proc(a, b: int) -> bool { return level_equiv_syn(a, b) }
level_equiv_sem :: proc(a, b: int) -> bool {
	if level_equiv_syn(a, b) do return true
	r := level_sem(a, b, false)
	if trace_on && r { fmt.eprintfln("SEM-TRUE %s == %s", canon_level(a), canon_level(b)) }
	return r
}

level_inst :: proc(l: int, ps: []int, us: []int) -> int {
	lv := levels[l]
	switch lv.kind {
	case .Zero: return l
	case .Param:
		for p, i in ps do if p == lv.a do return us[i]
		return l
	case .Succ: return add_level(Level{.Succ, level_inst(lv.a, ps, us), 0})
	case .Max:  return add_level(Level{.Max, level_inst(lv.a, ps, us), level_inst(lv.b, ps, us)})
	case .IMax: return add_level(Level{.IMax, level_inst(lv.a, ps, us), level_inst(lv.b, ps, us)})
	}
	return l
}

// ---------------------------------------------------------------- expressions

Expr_Key :: struct { kind: Expr_Kind, a, b, c, d, us: int }
expr_hc: map[Expr_Key]int
us_intern: map[string]int

us_id :: proc(us: []int) -> int {
	s := fmt.tprint(us)
	id, ok := us_intern[s]
	if !ok {
		id = len(us_intern) + 1
		us_intern[strings.clone(s)] = id
	}
	return id
}

expr_key :: proc(e: Expr) -> Expr_Key {
	k := Expr_Key{kind = e.kind, a = e.a, b = e.b, c = e.c, d = e.d}
	if e.kind == .Lam || e.kind == .Pi || e.kind == .Let do k.a = 0 // binder names are irrelevant
	if len(e.us) > 0 {
		s := fmt.tprint(e.us)
		id, ok := us_intern[s]
		if !ok {
			id = len(us_intern) + 1
			us_intern[strings.clone(s)] = id
		}
		k.us = id
	}
	return k
}

decl_start_exprs: int
add_expr :: proc(e: Expr) -> int {
	k := expr_key(e)
	if id, ok := expr_hc[k]; ok do return id
	append(&exprs, e)
	expr_hc[k] = len(exprs) - 1
	return len(exprs) - 1
}

hc_register :: proc(i: int) {
	k := expr_key(exprs[i])
	if _, ok := expr_hc[k]; !ok do expr_hc[k] = i
}
mk_bvar :: proc(i: int) -> int { return add_expr(Expr{kind = .BVar, a = i, lbr = i + 1}) }
mk_fvar :: proc(i: int) -> int { return add_expr(Expr{kind = .FVar, a = i}) }
mk_sort :: proc(l: int) -> int { return add_expr(Expr{kind = .Sort, a = l}) }
mk_const :: proc(n: int, us: []int) -> int { return add_expr(Expr{kind = .Const, a = n, us = us}) }
mk_app :: proc(f, x: int) -> int {
	return add_expr(Expr{kind = .App, a = f, b = x, lbr = max(exprs[f].lbr, exprs[x].lbr)})
}
mk_binder :: proc(k: Expr_Kind, name, ty, body: int) -> int {
	return add_expr(Expr{kind = k, a = name, b = ty, c = body, lbr = max(exprs[ty].lbr, exprs[body].lbr - 1)})
}
mk_proj :: proc(tn, idx, st: int) -> int {
	return add_expr(Expr{kind = .Proj, a = tn, b = idx, c = st, lbr = exprs[st].lbr})
}
mk_let :: proc(name, ty, val, body: int) -> int {
	return add_expr(Expr{kind = .Let, a = name, b = ty, c = val, d = body,
		lbr = max(exprs[ty].lbr, exprs[val].lbr, exprs[body].lbr - 1)})
}

// Replace loose bvar `off` by closed term v (v has no loose bvars).
Inst_Key :: struct { e, v, off: int }
inst_cache: map[Inst_Key]int

instantiate :: proc(e: int, v: int, off: int = 0) -> int {
	if trace_on { pc_inst += 1; if pc_inst % 100000 == 0 { fmt.eprintfln("P inst %d", pc_inst) } }
	if exprs[e].lbr <= off do return e
	k := Inst_Key{e, v, off}
	if r, ok := inst_cache[k]; ok do return r
	r := instantiate_raw(e, v, off)
	inst_cache[k] = r
	return r
}

instantiate_raw :: proc(e: int, v: int, off: int = 0) -> int {
	ex := exprs[e]
	if ex.lbr <= off do return e
	switch ex.kind {
	case .BVar:
		if ex.a == off do return v
		if ex.a > off do return mk_bvar(ex.a - 1)
		return e
	case .App: return mk_app(instantiate(ex.a, v, off), instantiate(ex.b, v, off))
	case .Lam, .Pi: return mk_binder(ex.kind, ex.a, instantiate(ex.b, v, off), instantiate(ex.c, v, off + 1))
	case .Let: return mk_let(ex.a, instantiate(ex.b, v, off), instantiate(ex.c, v, off), instantiate(ex.d, v, off + 1))
	case .MData: return instantiate(ex.a, v, off)
	case .Proj: return mk_proj(ex.a, ex.b, instantiate(ex.c, v, off))
	case .FVar, .Sort, .Const, .Unsupported, .NatLit, .StrLit: return e
	}
	return e
}

// Replace fvar `fv` by bvar(off).
abs_cache: map[Inst_Key]int

abstract_fvar :: proc(e: int, fv: int, off: int = 0) -> int {
	k := Inst_Key{e, fv, off}
	if r, ok := abs_cache[k]; ok do return r
	r := abstract_fvar_raw(e, fv, off)
	abs_cache[k] = r
	return r
}

abstract_fvar_raw :: proc(e: int, fv: int, off: int = 0) -> int {
	ex := exprs[e]
	switch ex.kind {
	case .FVar: return ex.a == fv ? mk_bvar(off) : e
	case .App: return mk_app(abstract_fvar(ex.a, fv, off), abstract_fvar(ex.b, fv, off))
	case .Lam, .Pi: return mk_binder(ex.kind, ex.a, abstract_fvar(ex.b, fv, off), abstract_fvar(ex.c, fv, off + 1))
	case .Let: return mk_let(ex.a, abstract_fvar(ex.b, fv, off), abstract_fvar(ex.c, fv, off), abstract_fvar(ex.d, fv, off + 1))
	case .MData: return abstract_fvar(ex.a, fv, off)
	case .Proj: return mk_proj(ex.a, ex.b, abstract_fvar(ex.c, fv, off))
	case .BVar, .Sort, .Const, .Unsupported, .NatLit, .StrLit: return e
	}
	return e
}

Lvl_Key :: struct { e, ps, us: int }
lvl_cache: map[Lvl_Key]int

inst_expr_levels :: proc(e: int, ps: []int, us: []int) -> int {
	if len(ps) == 0 do return e
	k := Lvl_Key{e, us_id(ps), us_id(us)}
	if r, ok := lvl_cache[k]; ok do return r
	r := inst_expr_levels_raw(e, ps, us)
	lvl_cache[k] = r
	return r
}

inst_expr_levels_raw :: proc(e: int, ps: []int, us: []int) -> int {
	ex := exprs[e]
	switch ex.kind {
	case .Sort: return mk_sort(level_inst(ex.a, ps, us))
	case .Const:
		nus := make([]int, len(ex.us))
		for u, i in ex.us do nus[i] = level_inst(u, ps, us)
		return mk_const(ex.a, nus)
	case .App: return mk_app(inst_expr_levels(ex.a, ps, us), inst_expr_levels(ex.b, ps, us))
	case .Lam, .Pi: return mk_binder(ex.kind, ex.a, inst_expr_levels(ex.b, ps, us), inst_expr_levels(ex.c, ps, us))
	case .Let: return mk_let(ex.a, inst_expr_levels(ex.b, ps, us), inst_expr_levels(ex.c, ps, us), inst_expr_levels(ex.d, ps, us))
	case .MData: return inst_expr_levels(ex.a, ps, us)
	case .Proj: return mk_proj(ex.a, ex.b, inst_expr_levels(ex.c, ps, us))
	case .BVar, .FVar, .Unsupported, .NatLit, .StrLit: return e
	}
	return e
}

fresh_fvar :: proc(name, ty: int) -> int {
	append(&fv_type, ty)
	append(&fv_name, name)
	return mk_fvar(len(fv_type) - 1)
}

get_app :: proc(e: int) -> (head: int, args: [dynamic]int) {
	cur := e
	for exprs[cur].kind == .App {
		append(&args, exprs[cur].b)
		cur = exprs[cur].a
		if len(args) > 100000 { fmt.eprintfln("GET_APP spine too long from %d, cur=%d kind=%v", e, cur, exprs[cur].kind); os.exit(4) }
	}
	// args collected last-to-first; reverse
	for i in 0 ..< len(args) / 2 {
		args[i], args[len(args) - 1 - i] = args[len(args) - 1 - i], args[i]
	}
	return cur, args
}

expr_str :: proc(e: int, depth: int = 0) -> string {
	if depth > 6 do return "…"
	ex := exprs[e]
	switch ex.kind {
	case .BVar: return fmt.aprintf("#%d", ex.a)
	case .FVar: return fmt.aprintf("%s", names[fv_name[ex.a]])
	case .Sort: return fmt.aprintf("Sort %s", level_str(ex.a))
	case .Const: return names[ex.a]
	case .App: return fmt.aprintf("(%s %s)", expr_str(ex.a, depth + 1), expr_str(ex.b, depth + 1))
	case .Lam: return fmt.aprintf("(fun %s : %s => %s)", names[ex.a], expr_str(ex.b, depth + 1), expr_str(ex.c, depth + 1))
	case .Pi: return fmt.aprintf("(%s : %s) -> %s", names[ex.a], expr_str(ex.b, depth + 1), expr_str(ex.c, depth + 1))
	case .Let: return fmt.aprintf("(let %s := %s; %s)", names[ex.a], expr_str(ex.c, depth + 1), expr_str(ex.d, depth + 1))
	case .MData: return expr_str(ex.a, depth)
	case .Proj: return fmt.aprintf("%s.%d", expr_str(ex.c, depth + 1), ex.b)
	case .NatLit: return lit_strs[ex.a]
	case .StrLit: return fmt.aprintf("%q", lit_strs[ex.a])
	case .Unsupported: return "<unsupported>"
	}
	return "?"
}

// ---------------------------------------------------------------- reduction

whnf_core_cache: map[int]int
whnf_cache: map[int]int
infer_cache: map[int]int
defeq_cache: map[[2]int]bool

whnf_core :: proc(e: int) -> int {
	if r, ok := whnf_core_cache[e]; ok do return r
	r := whnf_core_raw(e)
	if !aborted && !fuel_out do whnf_core_cache[e] = r
	return r
}

wc_n: int
fuel: int
fuel_out: bool
FUEL_LIMIT :: 30_000_000
BUDGET0 :: 20_000
eff_limit: int = FUEL_LIMIT // current fuel cap; below FUEL_LIMIT while a budgeted strategy runs
aborted: bool              // a budgeted strategy ran out of its budget

budget_begin :: proc(budget: int) -> (saved, inner: int) {
	saved = eff_limit
	inner = min(saved, fuel + budget)
	eff_limit = inner
	return
}
// true if this strategy's own budget ran out (caches are dropped, the flag is reset)
budget_end :: proc(saved, inner: int) -> bool {
	eff_limit = saved
	if aborted && inner < saved {
		aborted = false
		return true
	}
	return false
}
whnf_core_raw :: proc(e: int) -> int {
	fuel += 1
	if fuel > eff_limit { if eff_limit >= FUEL_LIMIT { fuel_out = true } else { aborted = true } }
	if fuel & 0xfff == 0 && len(exprs) - wm_exprs > 12_000_000 { fuel_out = true }
	if fuel_out || aborted do return e
	if trace_on { wc_n += 1; if wc_n % 100000 == 0 { fmt.eprintfln("wc %d %s", wc_n, expr_str(e, 6)) } }
	cur := e
	for {
		ex := exprs[cur]
		#partial switch ex.kind {
		case .MData: cur = ex.a
		case .Let:   cur = instantiate(ex.d, ex.c)
		case .Proj:
			st := whnf(ex.c)
			if exprs[st].kind == .StrLit do st = whnf(str_lit_to_ctor(st))
			sh, sargs := get_app(st)
			defer delete(sargs)
			if exprs[sh].kind != .Const do return cur
			cd, found := env[exprs[sh].a]
			if !found || cd.kind != .Ctor || cd.nparams + ex.b >= len(sargs) do return cur
			cur = sargs[cd.nparams + ex.b]
		case .App:
			head, args := get_app(cur)
			defer delete(args)
			h := whnf_core(head)
			if exprs[h].kind == .Lam {
				body := h
				i := 0
				for i < len(args) && exprs[body].kind == .Lam {
					body = instantiate(exprs[body].c, args[i])
					i += 1
				}
				for j in i ..< len(args) do body = mk_app(body, args[j])
				cur = body
			} else {
				if exprs[h].kind == .Const {
					if r, ok := try_quot(h, args[:]); ok {
						cur = r
						continue
					}
					if r, ok := try_iota(h, args[:]); ok {
						cur = r
						continue
					}
				}
				if h == head do return cur
				r := h
				for a in args do r = mk_app(r, a)
				return r
			}
		case: return cur
		}
	}
}

// Unfold a definition at the head of e (one step). ok=false if impossible.
unfold_head :: proc(e: int) -> (res: int, ok: bool) {
	if trace_on { pc_unf += 1; if pc_unf % 100000 == 0 { fmt.eprintfln("P unf %d", pc_unf) } }
	head, args := get_app(e)
	defer delete(args)
	hx := exprs[head]
	if hx.kind != .Const do return e, false
	d, found := env[hx.a]
	if !found || d.kind != .Def || d.height < 0 do return e, false
	if len(d.lparams) != len(hx.us) do return e, false
	r := inst_expr_levels(d.value, d.lparams, hx.us)
	for a in args do r = mk_app(r, a)
	return whnf_core(r), true
}

head_height :: proc(e: int) -> int {
	head, args := get_app(e)
	defer delete(args)
	hx := exprs[head]
	if hx.kind != .Const do return -1
	d, found := env[hx.a]
	if !found || d.kind != .Def do return -1
	return d.height
}

whnf :: proc(e: int) -> int {
	if trace_on { pc_whnf += 1; if pc_whnf % 100000 == 0 { fmt.eprintfln("P whnf %d", pc_whnf) } }
	if r, ok := whnf_cache[e]; ok do return r
	r := whnf_raw(e)
	if !aborted && !fuel_out do whnf_cache[e] = r
	return r
}

whnf_raw :: proc(e: int) -> int {
	cur := whnf_core(e)
	for {
		if r, ok := reduce_nat(cur); ok do return r
		nxt, ok := unfold_head(cur)
		if !ok do return cur
		cur = nxt
	}
}

// ---------------------------------------------------------------- Nat literals and Quot

name_cache: map[string]int

find_name :: proc(s: string) -> (int, bool) {
	if id, ok := name_cache[s]; ok do return id, true
	for n, i in names do if n == s && i != 0 {
		name_cache[s] = i
		return i, true
	}
	return 0, false
}

mk_nat_lit :: proc(v: ^big.Int) -> int {
	str, _ := big.int_itoa_string(v)
	return add_expr(Expr{kind = .NatLit, a = intern_lit(str, false)})
}

lit_intern: map[string]int
intern_lit :: proc(s: string, is_str: bool) -> int {
	key := fmt.tprintf("%c%s", is_str ? 's' : 'n', s)
	if i, ok := lit_intern[key]; ok do return i
	append(&lit_strs, strings.clone(s))
	lit_intern[strings.clone(key)] = len(lit_strs) - 1
	return len(lit_strs) - 1
}

// value of a literal (or Nat.zero) as a big integer
nat_value :: proc(e: int) -> (v: big.Int, ok: bool) {
	ex := exprs[e]
	if ex.kind == .NatLit {
		if err := big.int_atoi(&v, lit_strs[ex.a]); err != nil do return v, false
		return v, true
	}
	if ex.kind == .Const {
		if z, f := find_name("Nat.zero"); f && z == ex.a {
			big.int_set_from_integer(&v, 0)
			return v, true
		}
	}
	return v, false
}

is_nat_zero_or_succ :: proc(e: int) -> bool {
	h, args := get_app(e)
	defer delete(args)
	if exprs[h].kind != .Const do return false
	if z, f := find_name("Nat.zero"); f && z == exprs[h].a && len(args) == 0 do return true
	if sc, f := find_name("Nat.succ"); f && sc == exprs[h].a && len(args) == 1 do return true
	return false
}

is_nat_form :: proc(e: int) -> bool {
	return exprs[e].kind == .NatLit || is_nat_zero_or_succ(e)
}

nat_is_zero :: proc(e: int) -> bool {
	if exprs[e].kind == .NatLit do return lit_strs[exprs[e].a] == "0"
	return exprs[e].kind == .Const
}

// predecessor of a non-zero literal or of `Nat.succ x`
nat_pred :: proc(e: int) -> int {
	if exprs[e].kind == .NatLit {
		c := nat_lit_to_ctor(e)
		return exprs[c].b
	}
	return exprs[e].b
}

// literal n  ->  Nat.zero  |  Nat.succ (literal n-1)
str_lit_to_ctor :: proc(e: int) -> int {
	ofl, ok1 := find_name("String.ofList")
	cons, ok2 := find_name("List.cons")
	nil_, ok3 := find_name("List.nil")
	chr, ok4 := find_name("Char")
	ofn, ok5 := find_name("Char.ofNat")
	if !(ok1 && ok2 && ok3 && ok4 && ok5) do return e
	u0 := make([]int, 1)
	ch := mk_const(chr, nil)
	lst := mk_app(mk_const(nil_, u0), ch)
	cs := lit_strs[exprs[e].a]
	runes := utf8.string_to_runes(cs, context.temp_allocator)
	for i := len(runes) - 1; i >= 0; i -= 1 {
		v: big.Int
		big.int_set_from_integer(&v, int(runes[i]))
		c := mk_app(mk_const(ofn, nil), mk_nat_lit(&v))
		big.int_destroy(&v)
		lst = mk_app(mk_app(mk_app(mk_const(cons, u0), ch), c), lst)
	}
	return mk_app(mk_const(ofl, nil), lst)
}

nat_lit_to_ctor :: proc(e: int) -> int {
	v, ok := nat_value(e)
	defer big.int_destroy(&v)
	z, _ := find_name("Nat.zero")
	sc, _ := find_name("Nat.succ")
	if !ok do return e
	if zero, _ := big.int_is_zero(&v); zero do return mk_const(z, nil)
	one: big.Int
	big.int_set_from_integer(&one, 1)
	defer big.int_destroy(&one)
	pred: big.Int
	defer big.int_destroy(&pred)
	big.int_sub(&pred, &v, &one)
	return mk_app(mk_const(sc, nil), mk_nat_lit(&pred))
}

// GMP-style shortcuts for Nat.succ and the binary Nat operations on literals.
reduce_nat :: proc(e: int) -> (res: int, ok: bool) {
	if fuel_out do return 0, false
	if trace_on { pc_rn += 1; if pc_rn % 3000 == 0 { fmt.eprintfln("P rn %d", pc_rn) } }
	h, args := get_app(e)
	defer delete(args)
	if exprs[h].kind != .Const do return e, false
	nm := names[exprs[h].a]
	if !strings.has_prefix(nm, "Nat.") do return e, false
	op := nm[4:]
	if op == "succ" && len(args) == 1 {
		x, ok1 := nat_value(whnf(args[0]))
		defer big.int_destroy(&x)
		if !ok1 do return e, false
		one: big.Int
		big.int_set_from_integer(&one, 1)
		defer big.int_destroy(&one)
		r: big.Int
		defer big.int_destroy(&r)
		big.int_add(&r, &x, &one)
		return mk_nat_lit(&r), true
	}
	unary := op == "log2"
	binary := false
	switch op {
	case "add", "sub", "mul", "div", "mod", "gcd", "beq", "ble", "land", "lor", "xor", "shiftLeft", "shiftRight", "pow":
		binary = true
	}
	if !(binary && len(args) == 2) && !(unary && len(args) == 1) do return e, false
	a, ok1 := nat_value(whnf(args[0]))
	defer big.int_destroy(&a)
	if !ok1 do return e, false
	b: big.Int
	defer big.int_destroy(&b)
	if binary {
		ok2: bool
		b, ok2 = nat_value(whnf(args[1]))
		if !ok2 do return e, false
	}
	r: big.Int
	defer big.int_destroy(&r)
	bzero, _ := big.int_is_zero(&b)
	switch op {
	case "add": big.int_add(&r, &a, &b)
	case "sub":
		if c, _ := big.int_compare(&a, &b); c < 0 { big.int_set_from_integer(&r, 0) } else { big.int_sub(&r, &a, &b) }
	case "mul": big.int_mul(&r, &a, &b)
	case "div":
		if bzero { big.int_set_from_integer(&r, 0) } else { big.int_div(&r, &a, &b) }
	case "mod":
		if bzero { big.int_copy(&r, &a) } else { big.int_mod(&r, &a, &b) }
	case "gcd": big.int_gcd(&r, &a, &b)
	case "land": big.int_bit_and(&r, &a, &b)
	case "lor": big.int_bit_or(&r, &a, &b)
	case "xor": big.int_bit_xor(&r, &a, &b)
	case "shiftLeft", "shiftRight", "pow":
		sh, err := big.int_get_i64(&b)
		if err != nil || sh < 0 || sh > 1 << 24 {
			// huge shift count: only the trivial results are computed
			a_zero, _ := big.int_is_zero(&a)
			bits, _ := big.count_bits(&a)
			if op == "shiftRight" && bits <= 1 << 24 { big.int_set_from_integer(&r, 0) }
			else if op == "shiftLeft" && a_zero { big.int_set_from_integer(&r, 0) }
			else do return e, false
		} else {
		if op == "shiftLeft" { big.int_shl(&r, &a, int(sh)) }
		else if op == "shiftRight" { big.int_shr(&r, &a, int(sh)) }
		else { big.int_pow(&r, &a, int(sh)) }
		}
	case "log2":
		if z, _ := big.int_is_zero(&a); z { big.int_set_from_integer(&r, 0) }
		else {
			bits, _ := big.count_bits(&a)
			big.int_set_from_integer(&r, bits - 1)
		}
	case "beq", "ble":
		c, _ := big.int_compare(&a, &b)
		truth := op == "beq" ? c == 0 : c <= 0
		tn, f1 := find_name("Bool.true")
		fn, f2 := find_name("Bool.false")
		if !f1 || !f2 do return e, false
		return mk_const(truth ? tn : fn, nil), true
	case: return e, false
	}
	return mk_nat_lit(&r), true
}

try_quot :: proc(h: int, args: []int) -> (res: int, ok: bool) {
	d, found := env[exprs[h].a]
	if !found || d.kind != .Quot || d.qkind < 2 do return 0, false
	mk_pos := d.qkind == 2 ? 5 : 4
	if len(args) <= mk_pos do return 0, false
	q := whnf(args[mk_pos])
	qh, qargs := get_app(q)
	defer delete(qargs)
	if exprs[qh].kind != .Const do return 0, false
	qd, f2 := env[exprs[qh].a]
	if !f2 || qd.kind != .Quot || qd.qkind != 1 || len(qargs) != 3 do return 0, false
	r := mk_app(args[3], qargs[2])
	for i in mk_pos + 1 ..< len(args) do r = mk_app(r, args[i])
	return r, true
}

// ---------------------------------------------------------------- iota

structure_like :: proc(name: int) -> (ind: Decl, ok: bool) {
	d, found := env[name]
	if !found || d.kind != .Induct || len(d.ctors) != 1 || d.nindices != 0 || d.is_rec do return d, false
	return d, true
}

// If major (of structure type, not a Prop) is not a constructor application,
// replace it by C params (proj 0 major) ... (proj n major).
expand_struct :: proc(major: int) -> int {
	saved := failure
	defer failure = saved
	t, ok := infer(major)
	if !ok do return major
	t = whnf(t)
	h, hargs := get_app(t)
	defer delete(hargs)
	if exprs[h].kind != .Const do return major
	ind, is_s := structure_like(exprs[h].a)
	if !is_s || len(hargs) != ind.nparams do return major
	if is_prop(t) do return major
	cd := env[ind.ctors[0]]
	r := mk_const(ind.ctors[0], exprs[h].us)
	for i in 0 ..< ind.nparams do r = mk_app(r, hargs[i])
	for i in 0 ..< cd.nfields do r = mk_app(r, mk_proj(exprs[h].a, i, major))
	return r
}

try_iota :: proc(rec_const: int, args: []int) -> (res: int, ok: bool) {
	rx := exprs[rec_const]
	d, found := env[rx.a]
	if !found || d.kind != .Rec || len(d.lparams) != len(rx.us) do return 0, false
	major_idx := d.nparams + d.nmotives + d.nminors + d.nindices
	if len(args) <= major_idx do return 0, false
	major := args[major_idx]
	if d.k {
		saved := failure
		t, ok1 := infer(major)
		if ok1 {
			t = whnf(t)
			h, hargs := get_app(t)
			defer delete(hargs)
			if exprs[h].kind == .Const {
				if ind, f2 := env[exprs[h].a]; f2 && ind.kind == .Induct && len(ind.ctors) == 1 && len(hargs) >= ind.nparams {
					nm := mk_const(ind.ctors[0], exprs[h].us)
					for i in 0 ..< ind.nparams do nm = mk_app(nm, hargs[i])
					t2, ok2 := infer(nm)
					if ok2 && def_eq(t2, t) do major = nm
				}
			}
		}
		failure = saved
	}
	major = whnf(major)
	if exprs[major].kind == .NatLit do major = nat_lit_to_ctor(major)
	if exprs[major].kind == .StrLit do major = whnf(str_lit_to_ctor(major))
	mh, margs := get_app(major)
	defer delete(margs)
	is_ctor := false
	if exprs[mh].kind == .Const {
		if cd, f := env[exprs[mh].a]; f && cd.kind == .Ctor do is_ctor = true
	}
	if !is_ctor {
		major = expand_struct(major)
		delete(margs)
		mh, margs = get_app(major)
		if exprs[mh].kind != .Const do return 0, false
		if cd, f := env[exprs[mh].a]; !f || cd.kind != .Ctor do return 0, false
	}
	cd := env[exprs[mh].a]
	rule: Rule
	rf := false
	for r in d.rules do if r.ctor == exprs[mh].a { rule = r; rf = true }
	if !rf || len(margs) != cd.nparams + rule.nfields do return 0, false
	r := inst_expr_levels(rule.rhs, d.lparams, rx.us)
	for i in 0 ..< d.nparams + d.nmotives + d.nminors do r = mk_app(r, args[i])
	for i in len(margs) - rule.nfields ..< len(margs) do r = mk_app(r, margs[i])
	for i in major_idx + 1 ..< len(args) do r = mk_app(r, args[i])
	return r, true
}

// ---------------------------------------------------------------- type inference

infer :: proc(e: int) -> (res: int, ok: bool) {
	if trace_on { pc_inf += 1; if pc_inf % 100000 == 0 { fmt.eprintfln("P inf %d", pc_inf) } }
	if r, hit := infer_cache[e]; hit do return r, true
	res, ok = infer_raw(e)
	if ok && !aborted && !fuel_out do infer_cache[e] = res
	return
}

infer_raw :: proc(e: int) -> (res: int, ok: bool) {
	if e < 0 || e >= len(exprs) do return 0, fail("reference to undefined expression %d", e)
	ex := exprs[e]
	switch ex.kind {
	case .BVar: return 0, fail("loose bound variable")
	case .FVar: return fv_type[ex.a], true
	case .Sort: return mk_sort(add_level(Level{.Succ, ex.a, 0})), true
	case .MData: return infer(ex.a)
	case .Const:
		d, found := env[ex.a]
		if !found do return 0, fail("unknown constant %s", names[ex.a])
		if len(d.lparams) != len(ex.us) do return 0, fail("wrong number of universe levels for %s", names[ex.a])
		return inst_expr_levels(d.type, d.lparams, ex.us), true
	case .App:
		ft := infer(ex.a) or_return
		ft = whnf(ft)
		if exprs[ft].kind != .Pi do return 0, fail("function expected: %s", expr_str(ex.a))
		at := infer(ex.b) or_return
		if !def_eq(at, exprs[ft].b) {
			return 0, fail("argument type mismatch: %s : %s, expected %s", expr_str(ex.b), expr_str(at), expr_str(exprs[ft].b))
		}
		return instantiate(exprs[ft].c, ex.b), true
	case .Lam:
		_ = ensure_sort(ex.b) or_return
		fv := fresh_fvar(ex.a, ex.b)
		bt := infer(instantiate(ex.c, fv)) or_return
		return mk_binder(.Pi, ex.a, ex.b, abstract_fvar(bt, exprs[fv].a)), true
	case .Pi:
		u := ensure_sort(ex.b) or_return
		fv := fresh_fvar(ex.a, ex.b)
		v := ensure_sort(instantiate(ex.c, fv)) or_return
		return mk_sort(add_level(Level{.IMax, u, v})), true
	case .Let:
		_ = ensure_sort(ex.b) or_return
		vt := infer(ex.c) or_return
		if !def_eq(vt, ex.b) do return 0, fail("let value type mismatch")
		return infer(instantiate(ex.d, ex.c))
	case .Proj:
		st := infer(ex.c) or_return
		st = whnf(st)
		sh, sargs := get_app(st)
		defer delete(sargs)
		if exprs[sh].kind != .Const do return 0, fail("projection of non-structure")
		if exprs[sh].a != ex.a do return 0, fail("projection type name does not match the structure")
		// a structure in Prop may only project proofs (data fields would allow eliminating into Type)
		prop_struct := is_prop(st)
		ind, found := env[exprs[sh].a]
		if !found || ind.kind != .Induct || len(ind.ctors) != 1 || ind.nindices != 0 || len(sargs) != ind.nparams {
			return 0, fail("projection of non-structure %s", expr_str(ex.c))
		}
		cd := env[ind.ctors[0]]
		c := inst_expr_levels(cd.type, cd.lparams, exprs[sh].us)
		for i in 0 ..< ind.nparams {
			c = whnf(c)
			if exprs[c].kind != .Pi do return 0, fail("bad constructor type in projection")
			c = instantiate(exprs[c].c, sargs[i])
		}
		for j in 0 ..< ex.b {
			c = whnf(c)
			if exprs[c].kind != .Pi do return 0, fail("projection index out of range")
			if prop_struct && exprs[exprs[c].c].lbr > 0 && !is_prop(exprs[c].b) {
				return 0, fail("invalid projection: a later field depends on a non-proof field of a Prop structure")
			}
			c = instantiate(exprs[c].c, mk_proj(ex.a, j, ex.c))
		}
		c = whnf(c)
		if exprs[c].kind != .Pi do return 0, fail("projection index out of range")
		if prop_struct && !is_prop(exprs[c].b) do return 0, fail("invalid projection: cannot project a non-proof field of a Prop structure")
		return exprs[c].b, true
	case .NatLit:
		n, ok := find_name("Nat")
		if !ok do return 0, fail("Nat literal but no `Nat` in the environment")
		return mk_const(n, nil), true
	case .StrLit:
		n, ok := find_name("String")
		if !ok do return 0, fail("string literal but no `String` in the environment")
		return mk_const(n, nil), true
	case .Unsupported: return 0, fail("unsupported expression kind")
	}
	return 0, fail("bad expr")
}

// infer type of `ty`, require it to be a Sort, return its level
ensure_sort :: proc(ty: int) -> (res: int, ok: bool) {
	if ty < 0 || ty >= len(exprs) do return 0, fail("reference to undefined expression %d", ty)
	t := infer(ty) or_return
	w := whnf(t)
	if exprs[w].kind != .Sort do return 0, fail("type expected: %s", expr_str(ty))
	return exprs[w].a, true
}

is_prop :: proc(ty: int) -> bool {
	saved := failure
	t, ok := infer(ty)
	if !ok { failure = saved; return false }
	w := whnf(t)
	return exprs[w].kind == .Sort && level_equiv(exprs[w].a, 0)
}

// ---------------------------------------------------------------- definitional equality

args_eq :: proc(a, b: [dynamic]int) -> bool {
	if len(a) != len(b) do return false
	for i in 0 ..< len(a) do if !def_eq(a[i], b[i]) do return false
	return true
}

try_eta_struct :: proc(a, b: int) -> bool {
	if trace_on { pc_eta += 1; if pc_eta % 3000 == 0 { fmt.eprintfln("P eta %d", pc_eta) } }
	hb, ab := get_app(b)
	defer delete(ab)
	if exprs[hb].kind != .Const do return false
	c, ok := env[exprs[hb].a]
	if !ok || c.kind != .Ctor do return false
	if _, is_s := structure_like(c.induct); !is_s do return false
	if len(ab) != c.nparams + c.nfields do return false
	saved := failure
	defer failure = saved
	ta, ok1 := infer(a)
	tb, ok2 := infer(b)
	if !ok1 || !ok2 || !def_eq(ta, tb) do return false
	for i in 0 ..< c.nfields {
		if !def_eq(mk_proj(c.induct, i, a), ab[c.nparams + i]) do return false
	}
	return true
}

def_eq :: proc(a0, b0: int) -> bool {
	if trace_on { pc_de += 1; if pc_de % 3000 == 0 { fmt.eprintfln("P de %d", pc_de) } }
	if a0 == b0 do return true
	k := [2]int{min(a0, b0), max(a0, b0)}
	if r, ok := defeq_cache[k]; ok do return r
	r := def_eq_raw(a0, b0)
	if !aborted && !fuel_out do defeq_cache[k] = r
	return r
}

trace_on: bool
trace_n: int
trace_depth: int

def_eq_raw :: proc(a0, b0: int) -> bool {
	fuel += 1
	if fuel > eff_limit { if eff_limit >= FUEL_LIMIT { fuel_out = true } else { aborted = true } }
	if fuel_out || aborted do return false
	if trace_on {
		trace_n += 1
		if trace_n > 4000000 do os.exit(3)
		fmt.eprintfln("%d defeq %d %d %s  =?=  %s", trace_depth, a0, b0, expr_str(a0, trace_depth==3 ? 12 : 3), expr_str(b0, trace_depth==3 ? 12 : 3))
	}
	if trace_on && trace_depth == 30 {
		dd :: proc(a, b: int, p: string) {
			x, y := exprs[a], exprs[b]
			if a == b do return
			if x.kind != y.kind { fmt.eprintfln("  DIFF %s kind %v vs %v : %s | %s", p, x.kind, y.kind, expr_str(a, 3), expr_str(b, 3)); return }
			switch x.kind {
			case .App: if x.a != y.a { dd(x.a, y.a, fmt.tprintf("%s%s", p, "f")) }; if x.b != y.b { dd(x.b, y.b, fmt.tprintf("%s%s", p, "a")) }
			case .Lam, .Pi: if x.b != y.b { dd(x.b, y.b, fmt.tprintf("%s%s", p, "t")) }; if x.c != y.c { dd(x.c, y.c, fmt.tprintf("%s%s", p, "b")) }
			case .NatLit: fmt.eprintfln("  DIFF lit %s %s", lit_strs[x.a], lit_strs[y.a])
			case .Const: fmt.eprintfln("  DIFF const %s %s us %v %v", names[x.a], names[y.a], x.us, y.us)
			case .BVar, .FVar, .Sort, .StrLit, .Let, .MData, .Proj, .Unsupported: fmt.eprintfln("  DIFF other %v %s | %s", x.kind, expr_str(a, 3), expr_str(b, 3))
			}
		}
		dd(a0, b0, "")
	}
	trace_depth += 1
	defer trace_depth -= 1
	if a0 == b0 do return true
	a := whnf_core(a0)
	b := whnf_core(b0)
	if a == b do return true
	ea, eb := exprs[a], exprs[b]

	if ea.kind == .Sort && eb.kind == .Sort do return level_equiv_sem(ea.a, eb.a)
	if ea.kind == eb.kind && (ea.kind == .Lam || ea.kind == .Pi) {
		if !def_eq(ea.b, eb.b) do return false
		fv := fresh_fvar(ea.a, ea.b)
		return def_eq(instantiate(ea.c, fv), instantiate(eb.c, fv))
	}
	// eta
	if ea.kind == .Lam && eb.kind != .Lam {
		fv := fresh_fvar(ea.a, ea.b)
		return def_eq(instantiate(ea.c, fv), mk_app(b, fv))
	}
	if eb.kind == .Lam && ea.kind != .Lam {
		fv := fresh_fvar(eb.a, eb.b)
		return def_eq(mk_app(a, fv), instantiate(eb.c, fv))
	}
	// proof irrelevance
	{
		saved := failure
		ta, ok := infer(a)
		if ok && is_prop(ta) {
			tb, ok2 := infer(b)
			if ok2 do return def_eq(ta, tb)
		}
		failure = saved
	}
	// literals
	if ea.kind == .NatLit && eb.kind == .NatLit do return lit_strs[ea.a] == lit_strs[eb.a]
	if ea.kind == .StrLit && eb.kind == .StrLit do return lit_strs[ea.a] == lit_strs[eb.a]
	if is_nat_form(a) && is_nat_form(b) {
		za, zb := nat_is_zero(a), nat_is_zero(b)
		if za || zb do return za && zb
		return def_eq(nat_pred(a), nat_pred(b))
	}
	if ea.kind == .NatLit && is_nat_zero_or_succ(b) do return def_eq(nat_lit_to_ctor(a), b)
	if eb.kind == .NatLit && is_nat_zero_or_succ(a) do return def_eq(a, nat_lit_to_ctor(b))
	if r, ok := reduce_nat(a); ok do return def_eq(r, b)
	if r, ok := reduce_nat(b); ok do return def_eq(a, r)
	if ea.kind == .StrLit && eb.kind != .StrLit && eb.kind != .FVar do return def_eq(str_lit_to_ctor(a), b)
	if eb.kind == .StrLit && ea.kind != .StrLit && ea.kind != .FVar do return def_eq(a, str_lit_to_ctor(b))
	// lazy delta
	ha, hb := head_height(a), head_height(b)
	if ha >= 0 || hb >= 0 {
		// same head constant: try comparing args first
		if ha >= 0 && hb >= 0 {
			h1, a1 := get_app(a)
			h2, a2 := get_app(b)
			defer delete(a1)
			defer delete(a2)
			if exprs[h1].kind == .Const && exprs[h2].kind == .Const && exprs[h1].a == exprs[h2].a &&
			   len(exprs[h1].us) == len(exprs[h2].us) {
				lv_ok := true
				for i in 0 ..< len(exprs[h1].us) do if !level_equiv(exprs[h1].us[i], exprs[h2].us[i]) do lv_ok = false
				if lv_ok {
					sv, ic := budget_begin(BUDGET0)
					r := args_eq(a1, a2)
					ab := budget_end(sv, ic)
					if fuel_out || aborted do return false
					if !ab && r do return true
				}
			}
		}
		if ha >= 0 && hb >= 0 && ha != hb && nopf != "1" {
			// portfolio: unfold the higher side first, and if that gets expensive the lower one, with growing budgets
			budget := BUDGET0
			for {
				na, nb := a, b
				if r, ok := unfold_head(ha > hb ? a : b); ok { if ha > hb { na = r } else { nb = r } }
				sv, ic := budget_begin(budget)
				r1 := def_eq(na, nb)
				ab := budget_end(sv, ic)
				if fuel_out || aborted do return false
				if !ab do return r1
				na, nb = a, b
				if r, ok := unfold_head(ha > hb ? b : a); ok { if ha > hb { nb = r } else { na = r } }
				sv, ic = budget_begin(budget)
				r2 := def_eq(na, nb)
				ab = budget_end(sv, ic)
				if fuel_out || aborted do return false
				if !ab do return r2
				budget *= 4
			}
		}
		na, nb := a, b
		if ha >= hb {
			if r, ok := unfold_head(a); ok do na = r
		}
		if hb >= ha {
			if r, ok := unfold_head(b); ok do nb = r
		}
		if na != a || nb != b do return def_eq(na, nb)
	}
	if try_eta_struct(a, b) || try_eta_struct(b, a) do return true
	{ // unit-like types: all elements are equal
		saved := failure
		ta, ok := infer(a)
		if ok {
			wt := whnf(ta)
			uh, uargs := get_app(wt)
			defer delete(uargs)
			if exprs[uh].kind == .Const {
				if ind, f := env[exprs[uh].a]; f && ind.kind == .Induct && len(ind.ctors) == 1 && ind.nindices == 0 && env[ind.ctors[0]].nfields == 0 && len(uargs) == ind.nparams {
					tb, ok2 := infer(b)
					if ok2 && def_eq(ta, tb) do return true
				}
			}
		}
		failure = saved
	}
	// structural comparison of neutral terms
	if ea.kind == .Proj && eb.kind == .Proj {
		return ea.b == eb.b && def_eq(ea.c, eb.c)
	}
	if ea.kind == .Const && eb.kind == .Const {
		if ea.a != eb.a || len(ea.us) != len(eb.us) do return false
		for i in 0 ..< len(ea.us) do if !level_equiv(ea.us[i], eb.us[i]) do return false
		return true
	}
	if ea.kind == .FVar && eb.kind == .FVar do return ea.a == eb.a
	if ea.kind == .App && eb.kind == .App {
		h1, a1 := get_app(a)
		h2, a2 := get_app(b)
		defer delete(a1)
		defer delete(a2)
		return def_eq(h1, h2) && args_eq(a1, a2)
	}
	return false
}

// ---------------------------------------------------------------- declarations


// Expected types of the four Quot constants (Lean fixes them in the kernel)
quot_expected_type :: proc(qk: int, lp: []int) -> (t: int, ok: bool) {
	nQuot, f1 := find_name("Quot");     nMk, f2 := find_name("Quot.mk"); nEq, f3 := find_name("Eq")
	nm := add_name("x")
	need := qk == 0 ? 1 : qk == 2 ? 2 : 1
	if len(lp) != need do return 0, false
	if qk > 0 && !f1 do return 0, false
	if qk == 3 && !f2 do return 0, false
	if qk == 2 && !f3 do return 0, false
	lv :: proc(n: int) -> []int { r := make([]int, 1); r[0] = add_level(Level{.Param, n, 0}); return r }
	u := add_level(Level{.Param, lp[0], 0})
	v := len(lp) > 1 ? add_level(Level{.Param, lp[1], 0}) : 0
	su, sv, prop := mk_sort(u), mk_sort(v), mk_sort(0)
	B :: mk_bvar
	Pi :: proc(a, b: int) -> int { return mk_binder(.Pi, add_name("x"), a, b) }
	A :: mk_app
	rel := Pi(B(0), Pi(B(1), prop))
	quot := mk_const(nQuot, lv(lp[0]))
	switch qk {
	case 0:
		return Pi(su, Pi(rel, su)), true
	case 1:
		return Pi(su, Pi(rel, Pi(B(1), A(A(quot, B(2)), B(1))))), true
	case 2:
		eqc := mk_const(nEq, lv(lp[1]))
		hyp := Pi(B(3), Pi(B(4), Pi(A(A(B(4), B(1)), B(0)), A(A(A(eqc, B(4)), A(B(3), B(2))), A(B(3), B(1))))))
		return Pi(su, Pi(rel, Pi(sv, Pi(Pi(B(2), B(1)), Pi(hyp, Pi(A(A(quot, B(4)), B(3)), B(3))))))), true
	}
	mk := mk_const(nMk, lv(lp[0]))
	beta := Pi(A(A(quot, B(1)), B(0)), prop)
	mkt := Pi(B(2), A(B(1), A(A(A(mk, B(3)), B(2)), B(0))))
	return Pi(su, Pi(rel, Pi(beta, Pi(mkt, Pi(A(A(quot, B(3)), B(2)), A(B(2), B(0))))))), true
}

lvl_declared :: proc(l: int, lp: []int) -> bool {
	lv := levels[l]
	switch lv.kind {
	case .Zero: return true
	case .Succ: return lvl_declared(lv.a, lp)
	case .Max, .IMax: return lvl_declared(lv.a, lp) && lvl_declared(lv.b, lp)
	case .Param:
		for p in lp do if p == lv.a do return true
		return false
	}
	return true
}

declared_visit :: proc(e: int, lp: []int, seen: ^map[int]bool) -> bool {
	if e in seen^ do return true
	seen[e] = true
	ex := exprs[e]
	#partial switch ex.kind {
	case .Sort: return lvl_declared(ex.a, lp)
	case .Const:
		for u in ex.us do if !lvl_declared(u, lp) do return false
	case .App: return declared_visit(ex.a, lp, seen) && declared_visit(ex.b, lp, seen)
	case .Lam, .Pi: return declared_visit(ex.b, lp, seen) && declared_visit(ex.c, lp, seen)
	case .Let: return declared_visit(ex.b, lp, seen) && declared_visit(ex.c, lp, seen) && declared_visit(ex.d, lp, seen)
	case .MData: return declared_visit(ex.a, lp, seen)
	case .Proj: return declared_visit(ex.c, lp, seen)
	}
	return true
}

// every universe parameter used by e must be declared
declared_ok :: proc(e: int, lp: []int) -> bool {
	seen := make(map[int]bool)
	defer delete(seen)
	if !declared_visit(e, lp, &seen) do return fail("undeclared universe level parameter")
	return true
}

has_dup :: proc(xs: []int) -> bool {
	for i in 0 ..< len(xs) do for j in i + 1 ..< len(xs) do if xs[i] == xs[j] do return true
	return false
}

check_decl :: proc(d: Decl) -> bool {
	if has_dup(d.lparams) do return fail("duplicate universe parameter")
	declared_ok(d.type, d.lparams) or_return
	_ = ensure_sort(d.type) or_return
	if d.kind == .Axiom do return true
	declared_ok(d.value, d.lparams) or_return
	vt := infer(d.value) or_return
	if !def_eq(vt, d.type) {
		return fail("value has type %s, expected %s", expr_str(vt), expr_str(d.type))
	}
	if d.kind == .Thm {
		t, ok := infer(d.type)
		if !ok do return false
		if !level_equiv(exprs[whnf(t)].a, 0) do return fail("theorem type is not a Prop (%s : %s)", expr_str(d.type), expr_str(t))
	}
	return true
}

// ---------------------------------------------------------------- recursor regeneration

mk_binders_raw :: proc(kind: Expr_Kind, fvs: []int, body: int) -> int {
	b := body
	for i := len(fvs) - 1; i >= 0; i -= 1 {
		fv := exprs[fvs[i]].a
		b = mk_binder(kind, fv_name[fv], fv_type[fv], abstract_fvar(b, fv))
	}
	return b
}

// While checking a nested inductive, auxiliary types are translated back to the
// original nested occurrences (e.g. Aux_1 = Array Syntax) before binders are built.
mk_binders :: proc(kind: Expr_Kind, fvs: []int, body: int) -> int {
	if xl == nil do return mk_binders_raw(kind, fvs, body)
	b := translate(xl, body)
	for i := len(fvs) - 1; i >= 0; i -= 1 {
		fv := exprs[fvs[i]].a
		b = mk_binder(kind, fv_name[fv], translate(xl, fv_type[fv]), abstract_fvar(b, fv))
	}
	return b
}

mk_apps :: proc(f: int, args: []int) -> int {
	r := f
	for a in args do r = mk_app(r, a)
	return r
}

param_levels :: proc(ps: []int) -> []int {
	r := make([]int, len(ps))
	for p, i in ps do r[i] = add_level(Level{.Param, p, 0})
	return r
}

Rec_Field :: struct { k: int, xs: [dynamic]int, idx: [dynamic]int } // k = -1: not recursive
Ctor_Info :: struct {
	name:   int,
	orig:   int, // constructor name used by the exported recursor rules
	fields: [dynamic]int,
	recs:   [dynamic]Rec_Field, // one per field
	minor:  int,
}

// Re-derive the recursors of an inductive block from the constructors and compare them
// (types and reduction rules) with the exported ones.
verify_block :: proc(block: []int, rec_names: []int, n_orig: int) -> bool {
	n := len(block)
	ind0 := env[block[0]]
	params := make([dynamic]int)
	defer delete(params)
	t := ind0.type
	for _ in 0 ..< ind0.nparams {
		t = whnf(t)
		if exprs[t].kind != .Pi do return fail("recursor check: bad inductive type")
		fv := fresh_fvar(exprs[t].a, exprs[t].b)
		append(&params, fv)
		t = instantiate(exprs[t].c, fv)
	}
	idx := make([][dynamic]int, n)
	majors := make([]int, n)
	ind_consts := make([]int, n)
	sort_level := 0
	for j in 0 ..< n {
		ind := env[block[j]]
		ind_consts[j] = mk_const(block[j], param_levels(ind.lparams))
		tt := ind.type
		for i in 0 ..< ind.nparams {
			tt = whnf(tt)
			if exprs[tt].kind != .Pi do return fail("recursor check: bad inductive type")
			tt = instantiate(exprs[tt].c, params[i])
		}
		for _ in 0 ..< ind.nindices {
			tt = whnf(tt)
			if exprs[tt].kind != .Pi do return fail("recursor check: bad inductive type")
			fv := fresh_fvar(exprs[tt].a, exprs[tt].b)
			append(&idx[j], fv)
			tt = instantiate(exprs[tt].c, fv)
		}
		tt = whnf(tt)
		if exprs[tt].kind != .Sort do return fail("recursor check: inductive type is not a sort")
		if j == 0 do sort_level = exprs[tt].a
		args := make([dynamic]int)
		defer delete(args)
		for p in params do append(&args, p)
		for i in idx[j] do append(&args, i)
		majors[j] = fresh_fvar(add_name("t"), mk_apps(ind_consts[j], args[:]))
	}
	is_prop_ind := !level_never_zero(sort_level)
	is_real_prop := is_zero_level(sort_level)

	// constructors: fields and recursive fields
	infos := make([][dynamic]Ctor_Info, n)
	total_ctors := 0
	for j in 0 ..< n {
		ind := env[block[j]]
		for cn in ind.ctors {
			cd := env[cn]
			ci := Ctor_Info{name = cn, orig = cn}
			if xl != nil { if o, f := xl.ctor_orig[cn]; f do ci.orig = o }
			ct := cd.type
			for i in 0 ..< cd.nparams {
				ct = whnf(ct)
				if exprs[ct].kind != .Pi do return fail("recursor check: bad constructor type")
				ct = instantiate(exprs[ct].c, params[i])
			}
			for _ in 0 ..< cd.nfields {
				ct = whnf(ct)
				if exprs[ct].kind != .Pi do return fail("recursor check: bad constructor type")
				fv := fresh_fvar(exprs[ct].a, exprs[ct].b)
				append(&ci.fields, fv)
				ct = instantiate(exprs[ct].c, fv)
			}
			append(&infos[j], ci)
			total_ctors += 1
		}
	}

	// large elimination?
	large := true
	if is_prop_ind {
		large = false
		if n == 1 {
			ci := infos[0]
			if len(ci) == 0 {
				large = true
			} else if len(ci) == 1 {
				large = true
				c := ci[0]
				cd := env[c.name]
				res := cd.type
				for i in 0 ..< cd.nparams {
					res = whnf(res)
					res = instantiate(exprs[res].c, params[i])
				}
				for fv in c.fields {
					res = whnf(res)
					res = instantiate(exprs[res].c, fv)
				}
				res = whnf(res)
				rh, rargs := get_app(res)
				defer delete(rargs)
				for fv in c.fields {
					if is_prop(fv_type[exprs[fv].a]) do continue
					in_idx := false
					for k in ind0.nparams ..< len(rargs) do if exprs[rargs[k]].kind == .FVar && exprs[rargs[k]].a == exprs[fv].a { in_idx = true }
					if !in_idx do large = false
				}
			}
		}
	}

	// locate exported recursors and fix the elimination universe
	rec_of := make([]Decl, n)
	rec_id := make([]int, n)
	for j in 0 ..< n {
		want := j < n_orig ? fmt.aprintf("%s.rec", names[block[j]]) : fmt.aprintf("%s.rec_%d", names[block[0]], j - n_orig + 1)
		found := false
		for rn in rec_names do if names[rn] == want { rec_id[j] = rn; rec_of[j] = env[rn]; found = true }
		if !found do return fail("recursor %s missing", want)
	}
	ind_lp := env[block[0]].lparams
	elim_level := 0
	{
		rd := rec_of[0]
		if large {
			if len(rd.lparams) != len(ind_lp) + 1 do return fail("recursor of %s: expected large elimination", names[block[0]])
			elim_level = add_level(Level{.Param, rd.lparams[0], 0})
			for p, i in ind_lp do if rd.lparams[i + 1] != p do return fail("recursor universe parameters differ")
		} else {
			if len(rd.lparams) != len(ind_lp) do return fail("recursor of %s: large elimination is not allowed", names[block[0]])
		}
	}
	elim_sort := mk_sort(elim_level)

	// motives
	motives := make([]int, n)
	for j in 0 ..< n {
		fvs := make([dynamic]int)
		defer delete(fvs)
		for i in idx[j] do append(&fvs, i)
		append(&fvs, majors[j])
		motives[j] = fresh_fvar(add_name("motive"), mk_binders(.Pi, fvs[:], elim_sort))
	}

	// minor premises
	minors := make([dynamic]int)
	defer delete(minors)
	for j in 0 ..< n {
		for &ci in infos[j] {
			cd := env[ci.name]
			ihs := make([dynamic]int)
			defer delete(ihs)
			for fv in ci.fields {
				ft := whnf(fv_type[exprs[fv].a])
				xs := make([dynamic]int)
				for exprs[ft].kind == .Pi {
					x := fresh_fvar(exprs[ft].a, exprs[ft].b)
					append(&xs, x)
					ft = whnf(instantiate(exprs[ft].c, x))
				}
				h, hargs := get_app(ft)
				rf := Rec_Field{k = -1, xs = xs}
				if exprs[h].kind == .Const {
					for b, k in block do if b == exprs[h].a {
						rf.k = k
						for q in cd.nparams ..< len(hargs) do append(&rf.idx, hargs[q])
					}
				}
				append(&ci.recs, rf)
				if rf.k >= 0 {
					body := mk_app(mk_apps(motives[rf.k], rf.idx[:]), mk_apps(fv, xs[:]))
					append(&ihs, fresh_fvar(add_name("ih"), mk_binders(.Pi, xs[:], body)))
				}
			}
			// result indices of the constructor
			res := cd.type
			for i in 0 ..< cd.nparams {
				res = whnf(res)
				res = instantiate(exprs[res].c, params[i])
			}
			for fv in ci.fields {
				res = whnf(res)
				res = instantiate(exprs[res].c, fv)
			}
			res = whnf(res)
			_, rargs := get_app(res)
			defer delete(rargs)
			capp := mk_const(ci.name, param_levels(cd.lparams))
			for p in params do capp = mk_app(capp, p)
			capp = mk_apps(capp, ci.fields[:])
			concl := mk_app(mk_apps(motives[j], rargs[cd.nparams:]), capp)
			all := make([dynamic]int)
			defer delete(all)
			for f in ci.fields do append(&all, f)
			for ih in ihs do append(&all, ih)
			ci.minor = fresh_fvar(add_name("minor"), mk_binders(.Pi, all[:], concl))
			append(&minors, ci.minor)
		}
	}

	head_fvs := make([dynamic]int) // params ++ motives ++ minors
	defer delete(head_fvs)
	for p in params do append(&head_fvs, p)
	for m in motives do append(&head_fvs, m)
	for m in minors do append(&head_fvs, m)

	for j in 0 ..< n {
		rd := rec_of[j]
		if rd.nparams != ind0.nparams || rd.nmotives != n || rd.nminors != total_ctors || rd.nindices != env[block[j]].nindices {
			return fail("recursor %s has wrong parameter/motive/minor/index counts", names[rec_id[j]])
		}
		expect_k := is_real_prop && n == 1 && len(infos[0]) == 1 && len(infos[0][0].fields) == 0
		if rd.k != expect_k do return fail("recursor %s has wrong K flag", names[rec_id[j]])
		fvs := make([dynamic]int)
		defer delete(fvs)
		for h in head_fvs do append(&fvs, h)
		for i in idx[j] do append(&fvs, i)
		append(&fvs, majors[j])
		concl := mk_app(mk_apps(motives[j], idx[j][:]), majors[j])
		gen_type := mk_binders(.Pi, fvs[:], concl)
		if !def_eq(gen_type, rd.type) {
			return fail("recursor %s: exported type differs from the derived type", names[rec_id[j]])
		}
		if len(rd.rules) != len(infos[j]) do return fail("recursor %s: wrong number of rules", names[rec_id[j]])
		for ci in infos[j] {
			rule: Rule
			rf := false
			for r in rd.rules do if r.ctor == ci.orig { rule = r; rf = true }
			if !rf || rule.nfields != len(ci.fields) do return fail("recursor %s: missing rule for %s", names[rec_id[j]], names[ci.name])
			ihvals := make([dynamic]int)
			defer delete(ihvals)
			for r, fi in ci.recs {
				if r.k < 0 do continue
				rargs := make([dynamic]int)
				defer delete(rargs)
				for h in head_fvs do append(&rargs, h)
				for q in r.idx do append(&rargs, q)
				append(&rargs, mk_apps(ci.fields[fi], r.xs[:]))
				rc := mk_const(rec_id[r.k], param_levels(rec_of[r.k].lparams))
				append(&ihvals, mk_binders(.Lam, r.xs[:], mk_apps(rc, rargs[:])))
			}
			margs := make([dynamic]int)
			defer delete(margs)
			for f in ci.fields do append(&margs, f)
			for v in ihvals do append(&margs, v)
			lam_fvs := make([dynamic]int)
			defer delete(lam_fvs)
			for h in head_fvs do append(&lam_fvs, h)
			for f in ci.fields do append(&lam_fvs, f)
			gen_rhs := mk_binders(.Lam, lam_fvs[:], mk_apps(ci.minor, margs[:]))
			if !def_eq(gen_rhs, rule.rhs) {
				return fail("recursor %s: rule for %s differs from the derived rule", names[rec_id[j]], names[ci.name])
			}
		}
	}
	return true
}

add_name :: proc(s: string) -> int {
	append(&names, s)
	return len(names) - 1
}

// ---------------------------------------------------------------- nested inductive types

Aux_Type :: struct {
	name:   int,
	jname:  int,         // the nested inductive (e.g. Array)
	us:     []int,       // its universe levels at the occurrence
	as:     [dynamic]int,// its parameters at the occurrence (mention the block parameters as fvars)
	ctors:  [dynamic]int,// names of the auxiliary constructors
	jctors: []int,       // constructors of jname
}

Nested :: struct {
	params:    [dynamic]int,
	block:     [dynamic]int, // original types followed by auxiliary types
	n_orig:    int,
	aux:       [dynamic]Aux_Type,
	ctor_orig: map[int]int,  // auxiliary constructor -> constructor of the nested type
	memo:      map[int]int,
	tmemo:     map[int]int,
	lparams:   []int,
	err:       bool,
}
xl: ^Nested

in_block :: proc(n: ^Nested, name: int) -> bool {
	for b in n.block do if b == name do return true
	return false
}

find_or_create_aux :: proc(n: ^Nested, jname: int, us: []int, as: []int) -> int {
	for a, i in n.aux {
		if a.jname != jname || len(a.us) != len(us) || len(a.as) != len(as) do continue
		same := true
		for u, k in us do if !level_equiv(u, a.us[k]) do same = false
		for x, k in as do if x != a.as[k] do same = false
		if same do return i
	}
	jd := env[jname]
	nm := add_name(fmt.aprintf("%s._nested_%d", names[n.block[0]], len(n.aux) + 1))
	t := inst_expr_levels(jd.type, jd.lparams, us)
	for x in as {
		t = whnf(t)
		t = instantiate(exprs[t].c, x)
	}
	ty := mk_binders_raw(.Pi, n.params[:], t)
	a := Aux_Type{name = nm, jname = jname, us = us, jctors = jd.ctors}
	for x in as do append(&a.as, x)
	d := Decl{kind = .Induct, lparams = n.lparams, type = ty, height = -1, nparams = len(n.params), nindices = jd.nindices, is_rec = true}
	for jc in jd.ctors {
		cn := add_name(fmt.aprintf("%s.ctor_%s", names[nm], names[jc]))
		append(&a.ctors, cn)
		n.ctor_orig[cn] = jc
	}
	d.ctors = a.ctors[:]
	env[nm] = d
	append(&n.aux, a)
	append(&n.block, nm)
	return len(n.aux) - 1
}

replace_nested :: proc(n: ^Nested, e: int) -> int {
	if r, ok := n.memo[e]; ok do return r
	ex := exprs[e]
	r := e
	switch ex.kind {
	case .App, .Const:
		h, args := get_app(e)
		defer delete(args)
		handled := false
		if exprs[h].kind == .Const {
			if jd, f := env[exprs[h].a]; f && jd.kind == .Induct && !in_block(n, exprs[h].a) && len(args) >= jd.nparams {
				mention := false
				for i in 0 ..< jd.nparams do if mentions(args[i], n.block[:]) do mention = true
				if mention {
					for i in 0 ..< jd.nparams do if exprs[args[i]].lbr > 0 {
						fail("invalid nested inductive occurrence (parameters depend on bound variables)")
						n.err = true
						return e
					}
					ai := find_or_create_aux(n, exprs[h].a, exprs[h].us, args[:jd.nparams])
					r = mk_const(n.aux[ai].name, param_levels(n.lparams))
					r = mk_apps(r, n.params[:])
					for i in jd.nparams ..< len(args) do r = mk_app(r, replace_nested(n, args[i]))
					handled = true
				}
			}
		}
		if !handled && ex.kind == .App do r = mk_app(replace_nested(n, ex.a), replace_nested(n, ex.b))
	case .Lam, .Pi: r = mk_binder(ex.kind, ex.a, replace_nested(n, ex.b), replace_nested(n, ex.c))
	case .Let: r = mk_let(ex.a, replace_nested(n, ex.b), replace_nested(n, ex.c), replace_nested(n, ex.d))
	case .MData: r = replace_nested(n, ex.a)
	case .Proj: r = mk_proj(ex.a, ex.b, replace_nested(n, ex.c))
	case .BVar, .FVar, .Sort, .NatLit, .StrLit, .Unsupported:
	}
	n.memo[e] = r
	return r
}

// substitute the block parameters in `e` (a term over the parameter fvars) by `actual`
subst_params :: proc(n: ^Nested, e: int, actual: []int) -> int {
	if len(n.params) == 0 do return e
	t := mk_binders_raw(.Lam, n.params[:], e)
	for a in actual[:len(n.params)] do t = instantiate(exprs[t].c, a)
	return t
}

translate :: proc(n: ^Nested, e: int) -> int {
	if r, ok := n.tmemo[e]; ok do return r
	ex := exprs[e]
	r := e
	switch ex.kind {
	case .App, .Const:
		h, args := get_app(e)
		defer delete(args)
		targs := make([dynamic]int)
		defer delete(targs)
		for a in args do append(&targs, translate(n, a))
		done := false
		if exprs[h].kind == .Const && len(args) >= len(n.params) {
			for a in n.aux {
				if a.name == exprs[h].a {
					r = mk_const(a.jname, a.us)
					for x in a.as do r = mk_app(r, subst_params(n, x, targs[:]))
					r = mk_apps(r, targs[len(n.params):])
					done = true
				}
				for cn, ci in a.ctors do if cn == exprs[h].a {
					r = mk_const(a.jctors[ci], a.us)
					for x in a.as do r = mk_app(r, subst_params(n, x, targs[:]))
					r = mk_apps(r, targs[len(n.params):])
					done = true
				}
			}
		}
		if !done {
			r = mk_apps(h, targs[:])
		}
	case .Lam, .Pi: r = mk_binder(ex.kind, ex.a, translate(n, ex.b), translate(n, ex.c))
	case .Let: r = mk_let(ex.a, translate(n, ex.b), translate(n, ex.c), translate(n, ex.d))
	case .MData: r = translate(n, ex.a)
	case .Proj: r = mk_proj(ex.a, ex.b, translate(n, ex.c))
	case .BVar, .FVar, .Sort, .NatLit, .StrLit, .Unsupported:
	}
	n.tmemo[e] = r
	return r
}

wm_exprs, wm_levels, wm_fv: int

// Drop everything the kernel created while checking declarations (ids above the watermark set
// after loading the export), together with all caches that may refer to it.
purge :: proc() {
	for i in wm_exprs ..< len(exprs) do delete_key(&expr_hc, expr_key(exprs[i]))
	resize(&exprs, wm_exprs)
	for i in wm_levels ..< len(levels) do delete_key(&level_hc, levels[i])
	resize(&levels, wm_levels)
	resize(&fv_type, wm_fv)
	resize(&fv_name, wm_fv)
	delete(inst_cache); inst_cache = nil
	delete(abs_cache); abs_cache = nil
	delete(lvl_cache); lvl_cache = nil
	delete(infer_cache); infer_cache = nil
	delete(whnf_cache); whnf_cache = nil
	delete(whnf_core_cache); whnf_core_cache = nil
	delete(defeq_cache); defeq_cache = nil
	delete(canon_memo); canon_memo = nil
	delete(sem_memo); sem_memo = nil
}

clear_caches :: proc() {
	clear(&infer_cache); clear(&whnf_cache); clear(&whnf_core_cache); clear(&defeq_cache)
}

// Eliminate nested occurrences (as Lean's kernel does), check the resulting mutual block and
// compare its recursors, translated back, with the exported ones.
check_nested :: proc(orig_block: []int, rec_names: []int, num_nested: int) -> bool {
	n := new(Nested)
	n.lparams = env[orig_block[0]].lparams
	for b in orig_block do append(&n.block, b)
	n.n_orig = len(orig_block)
	ind0 := env[orig_block[0]]
	t := ind0.type
	for _ in 0 ..< ind0.nparams {
		t = whnf(t)
		if exprs[t].kind != .Pi do return fail("bad inductive type")
		fv := fresh_fvar(exprs[t].a, exprs[t].b)
		append(&n.params, fv)
		t = instantiate(exprs[t].c, fv)
	}
	saved := make(map[int]Decl)
	defer delete(saved)
	cleanup :: proc(n: ^Nested, saved: map[int]Decl) {
		for k, d in saved do env[k] = d
		for a in n.aux {
			delete_key(&env, a.name)
			for c in a.ctors do delete_key(&env, c)
		}
		xl = nil
		clear_caches()
	}
	defer cleanup(n, saved)

	instantiate_params :: proc(n: ^Nested, ty: int, as: []int) -> int {
		t := ty
		for x in as {
			t = whnf(t)
			t = instantiate(exprs[t].c, x)
		}
		return t
	}
	// 1. constructors of the original types
	for tn in orig_block[:n.n_orig] {
		for cn in env[tn].ctors {
			cd := env[cn]
			saved[cn] = cd
			body := instantiate_params(n, cd.type, n.params[:])
			body = replace_nested(n, body)
			if n.err do return false
			cd.type = mk_binders_raw(.Pi, n.params[:], body)
			env[cn] = cd
		}
	}
	// 2. constructors of the auxiliary types (the list grows while we walk it)
	for k := 0; k < len(n.aux); k += 1 {
		a := n.aux[k]
		for jc, ci in a.jctors {
			jd := env[jc]
			ty := inst_expr_levels(jd.type, jd.lparams, a.us)
			ty = instantiate_params(n, ty, a.as[:])
			ty = replace_nested(n, ty)
			if n.err do return false
			env[a.ctors[ci]] = Decl{kind = .Ctor, lparams = n.lparams, type = mk_binders_raw(.Pi, n.params[:], ty),
				height = -1, nparams = len(n.params), nfields = jd.nfields, induct = a.name}
		}
	}
	if len(n.aux) != num_nested do return fail("expected %d nested occurrences, found %d", num_nested, len(n.aux))
	clear_caches()
	// 3. positivity and universe checks of the expanded block
	for tn in n.block {
		ind := env[tn]
		for cn in ind.ctors do check_ctor(env[cn], ind, n.block[:]) or_return
	}
	xl = n
	verify_block(n.block[:], rec_names, n.n_orig) or_return
	return true
}

// ---------------------------------------------------------------- inductive types

mentions :: proc(e: int, block: []int) -> bool {
	ex := exprs[e]
	switch ex.kind {
	case .Const:
		for b in block do if b == ex.a do return true
		return false
	case .App: return mentions(ex.a, block) || mentions(ex.b, block)
	case .Lam, .Pi: return mentions(ex.b, block) || mentions(ex.c, block)
	case .Let: return mentions(ex.b, block) || mentions(ex.c, block) || mentions(ex.d, block)
	case .MData: return mentions(ex.a, block)
	case .Proj: return mentions(ex.c, block)
	case .BVar, .FVar, .Sort, .Unsupported, .NatLit, .StrLit: return false
	}
	return false
}

// strict positivity of a constructor field type
check_field :: proc(d: int, block: []int) -> bool {
	if !mentions(d, block) do return true
	w := whnf(d)
	if exprs[w].kind == .Pi {
		if mentions(exprs[w].b, block) do return fail("non-positive occurrence of the inductive type in %s", expr_str(d))
		fv := fresh_fvar(exprs[w].a, exprs[w].b)
		return check_field(instantiate(exprs[w].c, fv), block)
	}
	h, args := get_app(w)
	defer delete(args)
	if exprs[h].kind == .Const {
		for b in block do if b == exprs[h].a {
			for x in args do if mentions(x, block) do return fail("invalid occurrence of the inductive type in %s", expr_str(d))
			return true
		}
	}
	return fail("invalid (nested?) occurrence of the inductive type in %s", expr_str(d))
}

ind_sort_level :: proc(ind: Decl) -> (res: int, ok: bool) {
	t := ind.type
	for _ in 0 ..< ind.nparams + ind.nindices {
		t = whnf(t)
		if exprs[t].kind != .Pi do return 0, fail("inductive type has too few arguments")
		t = instantiate(exprs[t].c, fresh_fvar(exprs[t].a, exprs[t].b))
	}
	t = whnf(t)
	if exprs[t].kind != .Sort do return 0, fail("inductive type does not end in a Sort")
	return exprs[t].a, true
}

check_ctor :: proc(c: Decl, ind: Decl, block: []int) -> bool {
	t := c.type
	params := make([dynamic]int)
	defer delete(params)
	for _ in 0 ..< c.nparams {
		t = whnf(t)
		if exprs[t].kind != .Pi do return fail("constructor has too few parameters")
		fv := fresh_fvar(exprs[t].a, exprs[t].b)
		append(&params, fv)
		t = instantiate(exprs[t].c, fv)
	}
	nf := 0
	ind_level := ind_sort_level(ind) or_return
	for {
		t = whnf(t)
		if exprs[t].kind != .Pi do break
		check_field(exprs[t].b, block) or_return
		if !is_zero_level(ind_level) {
			fl := ensure_sort(exprs[t].b) or_return
			if !level_leq(fl, ind_level) {
				return fail("universe level of constructor field %s is too large (%s vs %s)", names[exprs[t].a], level_str(fl), level_str(ind_level))
			}
		}
		fv := fresh_fvar(exprs[t].a, exprs[t].b)
		t = instantiate(exprs[t].c, fv)
		nf += 1
	}
	if nf != c.nfields do return fail("constructor field count mismatch")
	h, args := get_app(t)
	defer delete(args)
	if exprs[h].kind != .Const || exprs[h].a != c.induct do return fail("constructor result is not the inductive type")
	if len(args) != ind.nparams + ind.nindices do return fail("constructor result has wrong arity")
	for i in 0 ..< ind.nparams {
		if exprs[args[i]].kind != .FVar || exprs[args[i]].a != exprs[params[i]].a {
			return fail("constructor result parameters differ from the declared parameters")
		}
	}
	for i in ind.nparams ..< len(args) do if mentions(args[i], block) do return fail("index mentions the inductive type")
	return true
}

check_inductive :: proc(x: json.Value) -> (first: int, ok: bool) {
	types, _ := jobj(x, "types")
	ctors, _ := jobj(x, "ctors")
	recs, _ := jobj(x, "recs")
	added := make([dynamic]int)
	defer delete(added)
	defer if !ok do for n in added do delete_key(&env, n)

	block := make([dynamic]int)
	defer delete(block)
	ta := types.(json.Array)
	for t in ta {
		nm, _ := jobj(t, "name")
		append(&block, jint(nm))
	}
	first = block[0]
	{ // no name may be declared twice, neither against the environment nor within this block
		seen := make(map[int]bool)
		defer delete(seen)
		for group in ([]json.Value{types, ctors, recs}) {
			for item in group.(json.Array) {
				nm := jint(jget(item, "name"))
				if nm in env || nm in seen do return first, fail("duplicate declaration %s", names[nm])
				seen[nm] = true
			}
		}
	}
	for grp in ([]json.Value{types, ctors, recs}) {
		for item in grp.(json.Array) do if has_dup(jints(jget(item, "levelParams"))) do return first, fail("duplicate universe parameter")
	}
	{
		nn := 0
		for t in ta do nn = max(nn, jint(jget(t, "numNested")))
		if len(recs.(json.Array)) != len(ta) + nn do return first, fail("wrong number of recursors")
	}
	num_nested := 0
	for t in ta {
		nm, _ := jobj(t, "name"); ty, _ := jobj(t, "type"); lp, _ := jobj(t, "levelParams")
		d := Decl{kind = .Induct, lparams = jints(lp), type = jint(ty), height = -1}
		d.nparams = jint(jget(t, "numParams")); d.nindices = jint(jget(t, "numIndices"))
		d.ctors = jints(jget(t, "ctors"))
		if b, is_b := jget(t, "isRec").(json.Boolean); is_b do d.is_rec = b
		num_nested = max(num_nested, jint(jget(t, "numNested")))
		declared_ok(d.type, d.lparams) or_return
		_ = ensure_sort(d.type) or_return
		env[jint(nm)] = d
		append(&added, jint(nm))
	}
	for c in ctors.(json.Array) {
		nm, _ := jobj(c, "name"); ty, _ := jobj(c, "type"); lp, _ := jobj(c, "levelParams")
		d := Decl{kind = .Ctor, lparams = jints(lp), type = jint(ty), height = -1}
		d.nparams = jint(jget(c, "numParams")); d.nfields = jint(jget(c, "numFields"))
		d.induct = jint(jget(c, "induct"))
		declared_ok(d.type, d.lparams) or_return
		_ = ensure_sort(d.type) or_return
		ind, found := env[d.induct]
		if !found do return first, fail("constructor of unknown inductive")
		if ind.nparams != d.nparams do return first, fail("constructor parameter count mismatch")
		if num_nested == 0 do check_ctor(d, ind, block[:]) or_return
		env[jint(nm)] = d
		append(&added, jint(nm))
	}
	rec_decls := make([dynamic]Decl)
	defer delete(rec_decls)
	// pass 1: register recursors (rule right-hand sides may mention any recursor of the block)
	for r in recs.(json.Array) {
		nm, _ := jobj(r, "name"); ty, _ := jobj(r, "type"); lp, _ := jobj(r, "levelParams")
		d := Decl{kind = .Rec, lparams = jints(lp), type = jint(ty), height = -1}
		d.nparams = jint(jget(r, "numParams")); d.nindices = jint(jget(r, "numIndices"))
		d.nmotives = jint(jget(r, "numMotives")); d.nminors = jint(jget(r, "numMinors"))
		if b, is_b := jget(r, "k").(json.Boolean); is_b do d.k = b
		rules := make([dynamic]Rule)
		for ru in jget(r, "rules").(json.Array) {
			append(&rules, Rule{jint(jget(ru, "ctor")), jint(jget(ru, "nfields")), jint(jget(ru, "rhs"))})
		}
		d.rules = rules[:]
		declared_ok(d.type, d.lparams) or_return
		_ = ensure_sort(d.type) or_return
		env[jint(nm)] = d
		append(&added, jint(nm))
		append(&rec_decls, d)
	}
	rec_names := make([dynamic]int)
	defer delete(rec_names)
	for r in recs.(json.Array) do append(&rec_names, jint(jget(r, "name")))
	// pass 2: check the rules
	for d in rec_decls {
		for ru in d.rules {
			cd, f := env[ru.ctor]
			if !f || cd.kind != .Ctor || cd.nfields != ru.nfields do return first, fail("bad recursor rule")
			declared_ok(ru.rhs, d.lparams) or_return
			_ = infer(ru.rhs) or_return
		}
	}
	if num_nested > 0 {
		check_nested(block[:], rec_names[:], num_nested) or_return
	} else {
		verify_block(block[:], rec_names[:], len(block)) or_return
	}
	return first, true
}

// ---------------------------------------------------------------- JSON loading

jint :: proc(v: json.Value) -> int {
	#partial switch x in v {
	case json.Integer: return int(x)
	case json.Float:   return int(x)
	}
	return -1
}
jobj :: proc(v: json.Value, key: string) -> (json.Value, bool) {
	o, ok := v.(json.Object)
	if !ok do return nil, false
	r, found := o[key]
	return r, found
}
jget :: proc(v: json.Value, key: string) -> json.Value {
	r, _ := jobj(v, key)
	return r
}
jints :: proc(v: json.Value) -> []int {
	arr, ok := v.(json.Array)
	if !ok do return nil
	out := make([]int, len(arr))
	for x, i in arr do out[i] = jint(x)
	return out
}
set_at :: proc(arr: ^[dynamic]$T, i: int, v: T) {
	for len(arr) <= i do append(arr, T{})
	arr[i] = v
}

main :: proc() {
	if len(os.args) < 2 {
		fmt.eprintln("usage: kernel file.ndjson")
		os.exit(2)
	}
	data, err := os.read_entire_file(os.args[1], context.allocator)
	if err != nil {
		fmt.eprintln("cannot read file")
		os.exit(2)
	}
	nosem = os.get_env("NOSEM", context.allocator)
	nopf = os.get_env("NOPF", context.allocator)
	append(&names, "")                           // name 0 = anonymous
	append(&levels, Level{.Zero, 0, 0})          // level 0 = zero
	env = make(map[int]Decl)

	n_ok, n_fail, n_skip := 0, 0, 0
	// pass 0 loads names/levels/expressions; pass 1 checks the declarations, so that the
	// ids used by the export are never mixed with nodes the kernel creates while checking
	decl_lines := make([dynamic]string)
	for pass in 0 ..< 2 {
	if pass == 1 { delete(data); data = nil; wm_exprs, wm_levels, wm_fv = len(exprs), len(levels), len(fv_type) }
	text := pass == 0 ? string(data) : strings.join(decl_lines[:], "\n")
	for line in strings.split_lines_iterator(&text) {
		if len(strings.trim_space(line)) == 0 do continue
		if pass == 0 do free_all(context.temp_allocator)
		v, perr := json.parse(transmute([]byte)line, json.DEFAULT_SPECIFICATION, true, context.temp_allocator)
		if perr != .None {
			fmt.eprintln("json error:", perr)
			os.exit(2)
		}
		if _, ok := jobj(v, "meta"); ok do continue

		// ---- names
		if id, ok := jobj(v, "in"); ok {
			i := jint(id)
			if s, ok2 := jobj(v, "str"); ok2 {
				pre, _ := jobj(s, "pre")
				str, _ := jobj(s, "str")
				p := names[jint(pre)]
				nm := strings.clone(str.(json.String))
				full := len(p) == 0 ? nm : strings.concatenate({p, ".", nm})
				set_at(&names, i, full)
			} else if s, ok2 := jobj(v, "num"); ok2 {
				pre, _ := jobj(s, "pre")
				k, _ := jobj(s, "i")
				full := fmt.aprintf("%s.%d", names[jint(pre)], jint(k))
				set_at(&names, i, full)
			}
			continue
		}
		// ---- levels
		if id, ok := jobj(v, "il"); ok {
			i := jint(id)
			l: Level
			if x, ok2 := jobj(v, "succ"); ok2 { l = Level{.Succ, jint(x), 0} }
			else if x, ok2 := jobj(v, "max"); ok2 { a := jints(x); l = Level{.Max, a[0], a[1]} }
			else if x, ok2 := jobj(v, "imax"); ok2 { a := jints(x); l = Level{.IMax, a[0], a[1]} }
			else if x, ok2 := jobj(v, "param"); ok2 { l = Level{.Param, jint(x), 0} }
			set_at(&levels, i, l)
			if _, ok := level_hc[l]; !ok do level_hc[l] = i
			continue
		}
		// ---- expressions
		if id, ok := jobj(v, "ie"); ok {
			i := jint(id)
			e: Expr
			if x, ok2 := jobj(v, "bvar"); ok2 { e = Expr{kind = .BVar, a = jint(x), lbr = jint(x) + 1} }
			else if x, ok2 := jobj(v, "sort"); ok2 { e = Expr{kind = .Sort, a = jint(x)} }
			else if x, ok2 := jobj(v, "const"); ok2 {
				nm, _ := jobj(x, "name")
				us, _ := jobj(x, "us")
				e = Expr{kind = .Const, a = jint(nm), us = jints(us)}
			} else if x, ok2 := jobj(v, "app"); ok2 {
				f, _ := jobj(x, "fn")
				a, _ := jobj(x, "arg")
				e = Expr{kind = .App, a = jint(f), b = jint(a)}
				e.lbr = max(exprs[e.a].lbr, exprs[e.b].lbr)
			} else if x, ok2 := jobj(v, "lam"); ok2 {
				nm, _ := jobj(x, "name"); ty, _ := jobj(x, "type"); bd, _ := jobj(x, "body")
				e = Expr{kind = .Lam, a = jint(nm), b = jint(ty), c = jint(bd)}
				e.lbr = max(exprs[e.b].lbr, exprs[e.c].lbr - 1)
			} else if x, ok2 := jobj(v, "forallE"); ok2 {
				nm, _ := jobj(x, "name"); ty, _ := jobj(x, "type"); bd, _ := jobj(x, "body")
				e = Expr{kind = .Pi, a = jint(nm), b = jint(ty), c = jint(bd)}
				e.lbr = max(exprs[e.b].lbr, exprs[e.c].lbr - 1)
			} else if x, ok2 := jobj(v, "letE"); ok2 {
				nm, _ := jobj(x, "name"); ty, _ := jobj(x, "type"); vl, _ := jobj(x, "value"); bd, _ := jobj(x, "body")
				e = Expr{kind = .Let, a = jint(nm), b = jint(ty), c = jint(vl), d = jint(bd)}
				e.lbr = max(exprs[e.b].lbr, exprs[e.c].lbr, exprs[e.d].lbr - 1)
			} else if x, ok2 := jobj(v, "natVal"); ok2 {
				e = Expr{kind = .NatLit, a = intern_lit(x.(json.String), false)}
			} else if x, ok2 := jobj(v, "strVal"); ok2 {
				e = Expr{kind = .StrLit, a = intern_lit(x.(json.String), true)}
			} else if x, ok2 := jobj(v, "proj"); ok2 {
				e = Expr{kind = .Proj, a = jint(jget(x, "typeName")), b = jint(jget(x, "idx")), c = jint(jget(x, "struct"))}
				e.lbr = exprs[e.c].lbr
			} else if x, ok2 := jobj(v, "mdata"); ok2 {
				inner, _ := jobj(x, "expr")
				e = Expr{kind = .MData, a = jint(inner)}
				e.lbr = exprs[e.a].lbr
			} else {
				e = Expr{kind = .Unsupported}
			}
			refs: []int
			switch e.kind {
			case .App: refs = {e.a, e.b}
			case .Lam, .Pi: refs = {e.b, e.c}
			case .Let: refs = {e.b, e.c, e.d}
			case .MData: refs = {e.a}
			case .Proj: refs = {e.c}
			case .BVar, .FVar, .Sort, .Const, .Unsupported, .NatLit, .StrLit:
			}
			for r in refs do if r < 0 || r >= len(exprs) {
				fmt.eprintln("malformed export: forward/invalid expr reference at id", i)
				os.exit(2)
			}
			set_at(&exprs, i, e)
			hc_register(i)
			continue
		}
		if pass == 0 {
			append(&decl_lines, strings.clone(line))
			continue
		}
		// ---- declarations
		d: Decl
		name: int
		found := false
		if x, ok := jobj(v, "axiom"); ok {
			nm, _ := jobj(x, "name"); ty, _ := jobj(x, "type"); lp, _ := jobj(x, "levelParams")
			name = jint(nm); d = Decl{kind = .Axiom, lparams = jints(lp), type = jint(ty), height = -1}; found = true
		} else if x, ok := jobj(v, "def"); ok {
			nm, _ := jobj(x, "name"); ty, _ := jobj(x, "type"); vl, _ := jobj(x, "value"); lp, _ := jobj(x, "levelParams")
			hints, _ := jobj(x, "hints")
			h := 0
			#partial switch hv in hints {
			case json.String: h = hv == "abbrev" ? 1 << 30 : 0
			case json.Object: if r, ok2 := hv["regular"]; ok2 { h = jint(r) }
			}
			name = jint(nm); d = Decl{kind = .Def, lparams = jints(lp), type = jint(ty), value = jint(vl), height = h}; found = true
		} else if x, ok := jobj(v, "thm"); ok {
			nm, _ := jobj(x, "name"); ty, _ := jobj(x, "type"); vl, _ := jobj(x, "value"); lp, _ := jobj(x, "levelParams")
			name = jint(nm); d = Decl{kind = .Thm, lparams = jints(lp), type = jint(ty), value = jint(vl), height = -1}; found = true
		} else if x, ok := jobj(v, "opaque"); ok {
			nm, _ := jobj(x, "name"); ty, _ := jobj(x, "type"); vl, _ := jobj(x, "value"); lp, _ := jobj(x, "levelParams")
			name = jint(nm); d = Decl{kind = .Opaque, lparams = jints(lp), type = jint(ty), value = jint(vl), height = -1}; found = true
		}
		if x, ok := jobj(v, "quot"); ok {
			failure = nil; fuel = 0; fuel_out = false; aborted = false; eff_limit = FUEL_LIMIT
			nm := jint(jget(x, "name"))
			kind := jget(x, "kind").(json.String)
			qk := kind == "type" ? 0 : kind == "ctor" ? 1 : kind == "lift" ? 2 : 3
			if nm in env {
				fmt.printf("FAIL  quot %s: duplicate declaration\n", names[nm])
				n_fail += 1
				continue
			}
			qd := Decl{kind = .Quot, lparams = jints(jget(x, "levelParams")), type = jint(jget(x, "type")), height = -1, qkind = qk}
			good := !has_dup(qd.lparams)
			if good { good = declared_ok(qd.type, qd.lparams) }
			if good { _, good = ensure_sort(qd.type) }
			if good {
				et, eok := quot_expected_type(qk, qd.lparams)
				if !eok || !def_eq(et, qd.type) {
					good = false
					failure = "Quot constant has the wrong type"
				}
			} else if failure == nil { failure = "duplicate universe parameter" }
			if good {
				env[nm] = qd
				fmt.printf("OK    quot %s\n", names[nm])
				n_ok += 1
			} else {
				fmt.printf("FAIL  quot %s: %s\n", names[nm], failure.? or_else "?")
				n_fail += 1
			}
			free_all(context.temp_allocator)
			continue
		}
		if x, ok := jobj(v, "inductive"); ok {
			failure = nil; fuel = 0; fuel_out = false; aborted = false; eff_limit = FUEL_LIMIT
			first, good := check_inductive(x)
			if good {
				fmt.printf("OK    inductive %s (%d type(s), %d ctor(s), %d recursor(s))\n", names[first],
					len(jget(x, "types").(json.Array)), len(jget(x, "ctors").(json.Array)), len(jget(x, "recs").(json.Array)))
				n_ok += 1
			} else {
				fmt.printf("FAIL  inductive %s: %s\n", names[first], failure.? or_else "?")
				n_fail += 1
			}
			free_all(context.temp_allocator)
			continue
		}
		if !found {
			kind := "?"
			if o, ok := v.(json.Object); ok { for k in o { kind = k; break } }
			fmt.printf("-  skipped (%s declaration not supported)\n", kind)
			n_skip += 1
			continue
		}
		failure = nil
		decl_start_exprs = len(exprs)
		dup_decl := name in env
		fuel = 0; fuel_out = false; aborted = false; eff_limit = FUEL_LIMIT
		if len(os.args) > 2 do fmt.eprintfln("checking %s", names[name])
		trace_on = len(os.args) > 3 && os.args[3] == names[name]
		ok_decl := !dup_decl && check_decl(d)
		if dup_decl { failure = fmt.aprintf("duplicate declaration %s", names[name]) }
		if fuel_out { ok_decl = false; failure = "resource limit exceeded (fuel)" }
		if ok_decl {
			env[name] = d
			fmt.printf("OK    %s\n", names[name])
			n_ok += 1
		} else {
			fmt.printf("FAIL  %s: %s\n", names[name], failure.? or_else "?")
			n_fail += 1
		}
		free_all(context.temp_allocator)
		if len(exprs) - wm_exprs > 300_000 { purge() }
	}
	}
	fmt.printf("\n%d accepted, %d rejected, %d skipped\n", n_ok, n_fail, n_skip)
	if n_fail > 0 do os.exit(1)
}

pc_unf, pc_whnf, pc_rn, pc_inf, pc_de, pc_inst, pc_eta: int
