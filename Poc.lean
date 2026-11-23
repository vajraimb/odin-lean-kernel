prelude
set_option autoImplicit false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
universe u v w
unsafe axiom lcErased : Type
unsafe axiom lcAny : Type

noncomputable def Id' {α : Sort u} (a : α) : α := a
noncomputable def Comp {α : Sort u} {β : Sort v} {γ : Sort w} (g : β → γ) (f : α → β) : α → γ := fun x => g (f x)
noncomputable def K {α : Sort u} {β : Sort v} (a : α) (_ : β) : α := a

axiom P : Prop
axiom p : P
axiom q1 : P
axiom q2 : P

theorem idP : P → P := fun h => h
theorem useId : P := Id' p
theorem useComp : P → P := Comp (fun x => x) (fun x => x)
theorem useK : P := K p (fun (x : P) => x)
theorem letT : P := let x := p; x

noncomputable def Church := ∀ (α : Sort u), (α → α) → α → α
noncomputable def czero : Church.{u} := fun α _ z => z
noncomputable def csucc (n : Church.{u}) : Church.{u} := fun α s z => s (n α s z)
noncomputable def cone : Church.{u} := csucc czero.{u}

axiom T : (P → P) → Prop
theorem eta (g : P → P) (h : T g) : T (fun x => g x) := h

axiom U : P → Prop
axiom u : U q1
theorem proofIrrel : U q2 := u

noncomputable def L1 : Sort (max u v + 1) := Sort (max u v)
noncomputable def L2 : Sort (max v u + 1) := L1.{u, v}

-- ===================== inductive types =====================
inductive N : Type where
  | z : N
  | s : N → N

noncomputable def N.add (a b : N) : N := @N.rec (fun _ => N) b (fun _ ih => N.s ih) a

inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a

-- iota on a closed recursive term: 2 + 2 = 4
theorem two_two : Eq (N.add (N.s (N.s N.z)) (N.s (N.s N.z))) (N.s (N.s (N.s (N.s N.z)))) :=
  @Eq.refl N _

-- K-like reduction: the major premise is a variable h : Eq a a
theorem kRule {α : Sort u} (a : α) (h : Eq a a) :
    Eq (@Eq.rec α a (fun _ _ => N) N.z a h) N.z := @Eq.refl N _

inductive L (α : Type u) : Type u where
  | nil : L α
  | cons : α → L α → L α

noncomputable def L.length {α : Type u} (l : L α) : N :=
  @L.rec α (fun _ => N) N.z (fun _ _ ih => N.s ih) l

theorem len2 : Eq (@L.length N (L.cons N.z (L.cons N.z L.nil))) (N.s (N.s N.z)) := @Eq.refl N _

-- indexed family
inductive V (α : Type u) : N → Type u where
  | nil : V α N.z
  | cons {n : N} : α → V α n → V α (N.s n)

noncomputable def V.toL {α : Type u} {n : N} (v : V α n) : L α :=
  @V.rec α (fun _ _ => L α) L.nil (fun h _ ih => L.cons h ih) n v

theorem toL1 : Eq (@V.toL N (N.s N.z) (V.cons N.z V.nil)) (L.cons N.z L.nil) := @Eq.refl (L N) _

-- Prop inductives (small elimination only for Or / Exists)
inductive And' (a b : Prop) : Prop where
  | intro : a → b → And' a b

theorem and_left (a b : Prop) (h : And' a b) : a := @And'.rec a b (fun _ => a) (fun x _ => x) h

inductive Or' (a b : Prop) : Prop where
  | inl : a → Or' a b
  | inr : b → Or' a b

-- mutual inductive
mutual
inductive A : Type where
  | a0 : A
  | a1 : B → A
inductive B : Type where
  | b1 : A → B
end

theorem mutualRec :
    Eq (@A.rec (fun _ => N) (fun _ => N) N.z (fun _ ih => N.s ih) (fun _ ih => ih) (A.a1 (B.b1 A.a0)))
       (N.s N.z) := @Eq.refl N _

-- structure: Expr.proj, projection reduction and structure eta
structure Pr (α β : Type u) : Type u where
  mk ::
  fst : α
  snd : β

theorem projRed : Eq (Pr.fst (Pr.mk N.z (N.s N.z))) N.z := @Eq.refl N _
theorem structEta {α β : Type u} (p : Pr α β) : Eq p (Pr.mk p.fst p.snd) := @Eq.refl (Pr α β) _
-- structure eta via recursor on a variable
theorem structRec {α β : Type u} (p : Pr α β) :
    Eq (@Pr.rec α β (fun _ => α) (fun x _ => x) p) p.fst := @Eq.refl α _

-- ===================== more inductives: elimination rules and reflexive types =====================
inductive Ex' {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Ex' p            -- small elimination only (w is data)

inductive F' : Prop                              -- empty: large elimination
inductive T' : Prop where
  | intro : T'                                   -- large elimination

inductive Acc' {α : Sort u} (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : (y : α) → r y x → Acc' r y) : Acc' r x   -- reflexive, large elimination

inductive Ev : N → Prop where
  | zero : Ev N.z
  | step (n : N) : Ev n → Ev (N.s (N.s n))

-- reflexive data type: recursive field has a function type
inductive W (α : Type) (β : α → Type) : Type where
  | sup (a : α) (f : β a → W α β) : W α β

inductive Sg (α : Type u) (β : α → Type v) : Type (max u v) where
  | mk (fst : α) (snd : β fst) : Sg α β

-- ===================== Nat literals (kernel GMP-style shortcuts) =====================
inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

class OfNat (α : Type u) (_ : Nat) where
  ofNat : α
instance instOfNatNat (n : Nat) : OfNat Nat n := ⟨n⟩

inductive Bool : Type where
  | false : Bool
  | true : Bool

-- real definitions by recursion; the kernel must use the literal shortcut for big numbers
noncomputable def Nat.add (a b : Nat) : Nat := @Nat.rec (fun _ => Nat) a (fun _ ih => Nat.succ ih) b
noncomputable def Nat.mul (a b : Nat) : Nat := @Nat.rec (fun _ => Nat) Nat.zero (fun _ ih => Nat.add ih a) b
-- operations the kernel evaluates natively on literals (declared as axioms here)
axiom Nat.sub : Nat → Nat → Nat
axiom Nat.div : Nat → Nat → Nat
axiom Nat.mod : Nat → Nat → Nat
axiom Nat.gcd : Nat → Nat → Nat
axiom Nat.pow : Nat → Nat → Nat
axiom Nat.land : Nat → Nat → Nat
axiom Nat.lor : Nat → Nat → Nat
axiom Nat.xor : Nat → Nat → Nat
axiom Nat.shiftLeft : Nat → Nat → Nat
axiom Nat.shiftRight : Nat → Nat → Nat
axiom Nat.log2 : Nat → Nat
axiom Nat.beq : Nat → Nat → Bool
axiom Nat.ble : Nat → Nat → Bool

theorem nat_add_small : @Eq Nat (Nat.add (4 : Nat) (5 : Nat)) (9 : Nat) := @Eq.refl Nat _
theorem nat_add_big : @Eq Nat (Nat.add (12345678901234567890 : Nat) (98765432109876543210 : Nat))
    (111111111011111111100 : Nat) := @Eq.refl Nat _
theorem nat_mul_big : @Eq Nat (Nat.mul (18446744073709551616 : Nat) (18446744073709551616 : Nat))
    (340282366920938463463374607431768211456 : Nat) := @Eq.refl Nat _
theorem nat_pow : @Eq Nat (Nat.pow (2 : Nat) (128 : Nat))
    (340282366920938463463374607431768211456 : Nat) := @Eq.refl Nat _
theorem nat_ops : @Eq Nat
    (Nat.add (Nat.add (Nat.sub (3 : Nat) (5 : Nat)) (Nat.div (100 : Nat) (7 : Nat)))
      (Nat.add (Nat.mod (100 : Nat) (7 : Nat)) (Nat.gcd (12 : Nat) (18 : Nat))))
    (22 : Nat) := @Eq.refl Nat _
theorem nat_bits : @Eq Nat
    (Nat.add (Nat.land (12 : Nat) (10 : Nat)) (Nat.add (Nat.lor (12 : Nat) (10 : Nat)) (Nat.xor (12 : Nat) (10 : Nat))))
    (28 : Nat) := @Eq.refl Nat _
theorem nat_shift : @Eq Nat (Nat.shiftLeft (1 : Nat) (70 : Nat)) (1180591620717411303424 : Nat) := @Eq.refl Nat _
theorem nat_shr : @Eq Nat (Nat.shiftRight (1180591620717411303424 : Nat) (68 : Nat)) (4 : Nat) := @Eq.refl Nat _
theorem nat_ble : @Eq Bool (Nat.ble (3 : Nat) (5 : Nat)) Bool.true := @Eq.refl Bool _
theorem nat_beq : @Eq Bool (Nat.beq (3 : Nat) (4 : Nat)) Bool.false := @Eq.refl Bool _
theorem nat_succ : @Eq Nat (Nat.succ (4 : Nat)) (5 : Nat) := @Eq.refl Nat _
theorem nat_zero : @Eq Nat Nat.zero (0 : Nat) := @Eq.refl Nat _
-- iota on a literal major premise: the literal is converted to Nat.succ (Nat.succ ...)
theorem nat_rec_lit : @Eq Nat (@Nat.rec (fun _ => Nat) Nat.zero (fun _ ih => Nat.succ ih) (3 : Nat)) (3 : Nat) :=
  @Eq.refl Nat _

-- string literal (typed only)
axiom String : Type
axiom strP : String → Prop
theorem str_refl : @Eq String "ab" "ab" := @Eq.refl String _

-- ===================== quotients =====================
init_quot

axiom R : N → N → Prop
axiom hR : (a b : N) → R a b → @Eq N a b
theorem quot_lift_mk : @Eq N (@Quot.lift N R N (fun x => x) hR (Quot.mk R (N.s N.z))) (N.s N.z) := @Eq.refl N _
theorem quot_lift_two : @Eq N (@Quot.lift N R N (fun x => N.s x) (fun a b h => @Eq.rec N a (fun y _ => @Eq N (N.s a) (N.s y)) (@Eq.refl N _) b (hR a b h))
    (Quot.mk R N.z)) (N.s N.z) := @Eq.refl N _
