# Lean Kernel Arena results (odin-lean-kernel)

Test suite: lean-arena-tests.tar.gz (138 good, 92 bad). Run: `cd <extracted dir>; python3 run.py ./kernel 120`.

| expected | accepted | rejected | timeout |
|---|---|---|---|
| good (138) | 125 | 11 | 2 |
| bad (92) | 14 | 78 | 0 |

## Wrongly accepted (soundness bugs)

- bad/bugs/large-elim-param.ndjson
- bad/bugs/orphan-rec.ndjson
- bad/bugs/proj-of-imax-prop.ndjson
- bad/bugs/quot-bad-type.ndjson
- bad/other/extra-rec.ndjson
- bad/tutorial/019_tut06_bad01.ndjson
- bad/tutorial/090_projProp2.ndjson
- bad/tutorial/092_projProp4.ndjson
- bad/tutorial/093_projProp5.ndjson
- bad/tutorial/094_projProp6.ndjson
- bad/tutorial/132_dup_defs.ndjson
- bad/tutorial/133_dup_ind_def.ndjson
- bad/tutorial/134_dup_ctor_def.ndjson
- bad/tutorial/135_dup_rec_def.ndjson

## Wrongly rejected or timed out

- good/bugs/nat-shift-huge.ndjson (reject, 35.01s) FAIL  natShiftRightHuge: resource limit exceeded (fuel)
- good/perf/app-lam.ndjson (timeout, 120.1s) 
- good/perf/gf3-matrix-product.ndjson (timeout, 120.1s) 
- good/perf/ite-taken-branch.ndjson (reject, 112.07s) FAIL  ite_taken_branch_1: resource limit exceeded (fuel)
- good/perf/magma-list-deep-n36.ndjson (reject, 19.15s) FAIL  countermodel: resource limit exceeded (fuel)
- good/perf/magma-list-pair-n21.ndjson (reject, 21.02s) FAIL  countermodel: resource limit exceeded (fuel)
- good/perf/proj-lazy-struct.ndjson (reject, 20.2s) FAIL  proj_lazy_struct: resource limit exceeded (fuel)
- good/perf/short-circuit-and.ndjson (reject, 50.02s) FAIL  short_circuit_and_1: resource limit exceeded (fuel)
- good/tutorial/006_betaReduction.ndjson (reject, 0.0s) FAIL  betaReduction: value has type Sort imax(S(0),0), expected ((constType Sort 0) (a._@._internal._hyg.0 : S
- good/tutorial/007_betaReduction2.ndjson (reject, 0.0s) FAIL  betaReduction2: value has type (a._@._internal._hyg.0 : Sort 0) -> Sort 0, expected (p : Sort 0) -> ((co
- good/tutorial/055_reduceCtorParam.mk.ndjson (reject, 0.0s) FAIL  inductive reduceCtorParam: invalid (nested?) occurrence of the inductive type in ((constType (reduceCtor
- good/tutorial/119_reduceCtorParamRefl.mk.ndjson (reject, 0.0s) FAIL  inductive reduceCtorParamRefl: invalid (nested?) occurrence of the inductive type in ((constType (reduce
- good/tutorial/120_reduceCtorParamRefl2.mk.ndjson (reject, 0.0s) FAIL  inductive reduceCtorParamRefl2: invalid (nested?) occurrence of the inductive type in ((constType (reduc

## 更新：修复投影规则与重复定义

- bad: 误放行 14 -> 5，正确拒绝 78 -> 87
- good: 接受 125，拒绝 10，超时 3（60 秒限制）
- 仍误放行：large-elim-param, orphan-rec, quot-bad-type, extra-rec, tut06_bad01

## 更新：bad 测试全部拒绝

- bad: 误放行 5 -> 0，92 个全部正确拒绝
- good: 接受 125，拒绝 10，超时 3（60 秒限制），与上一轮相同
- 新增检查：Quot 四个常量的类型、重复宇宙参数、未声明宇宙参数、递归子数量（类型数加嵌套数）、可能为 Prop 的归纳类型的大消去限制

## 更新：opaque 提示的定义可以展开

- 根因：hints 为 opaque 的定义被当成不可展开，导致 beta 后类型比较和构造子参数归约失败
- good: 接受 125 -> 130，拒绝 10 -> 5（全是 fuel 耗尽），超时 3；bad: 92/92 拒绝

## 更新：预算化的惰性展开策略

- 同头比较：先在小预算内比较参数，超出预算则放弃并展开；高度不同时，先展开较高一侧，预算耗尽后换成展开较低一侧，预算逐轮放大 4 倍
- 修复巨大移位量的 Nat 字面量归约（shiftRight 与 shiftLeft 0）
- 每个声明开始时重置预算状态；运行器改用各测试 yaml 里的超时（上限 150 秒）
- good: 接受 134 / 138；bad: 92 / 92 拒绝
- 剩余：magma-list-deep-n36 与 magma-list-pair-n21 因表达式节点数超过内存上限被拒，app-lam 与 gf3-matrix-product 超时（常数因子问题）

## 更新：性能优化

- 哈希化 hash-cons 表和宇宙层级表，所有缓存改为按代数标记的直接映射有损缓存，清缓存变为 O(1)。
- Nat 字面量由十进制字符串改为大端字节串，线性时间读写（原先十进制转换为二次复杂度）。
- 字面量按 id 比较，去掉大字符串临时拷贝。

| 项目 | 优化前 | 优化后 |
|---|---|---|
| 完整 Init（58522 通过，24 拒绝，结果不变） | 271 s，5.3 GB | 128 s，2.7 GB |
| app-lam | 超时（>150 s） | 22 s |
| gf3-matrix-product | 超时 | 31 s |
| unfold-before-literal | 约 119 s | 73 s |
| Arena good | 134/138 | 136/138 |
| Arena bad | 92/92 拒绝 | 92/92 拒绝 |

仍失败：magma-list-deep-n36、magma-list-pair-n21（资源上限）。

## 更新：同时实例化（减少表达式创建）

- beta 归约与递归子规则展开时，一次性替换全部绑定变量（instantiate_n），不再逐个参数生成整份中间副本。
- magma-list-pair-n7 新建表达式 11.35M -> 7.16M（约 -37%），耗时 6.8 s -> 5.1 s。
- 表达式数量上限 12M -> 20M（8 GB 沙箱内更高会被 OOM 杀掉）。
- 完整 Init：58530 通过、16 拒绝（原 58522/24），151 s，3.5 GB。
- Arena：good 136/138，bad 92/92 拒绝，无回归。
- magma-list-pair-n21 / deep-n36 仍超限：n7 约每个四元组 3000 个表达式，n21 估计需要数亿个节点，需要节点回收或更好的缓存命中才能解决。

## 更新：缓存命中率分析

- 把有损缓存从 2^21 扩到 2^24 项，新建表达式数完全不变（7156502），说明未命中不是容量驱逐，而是项本身确实不同。
- whnf_core 的未命中几乎全是 lambda 头的 beta 红式：n7 每个四元组约 200 次，每次替换生成约 15 个新节点；项里带着 Nat.Lemmas 的 reflects_decide 证明体，每个四元组都不同，无法共享。
- whnf_core 对 Lam/Pi/Sort/Const/字面量/FVar 直接返回，不再进缓存：n7 5.1 s -> 4.4 s。
- 结论：n21、n36 的瓶颈是每次 beta 都要实例化大型证明项，需要惰性替换（闭包式求值）或节点回收，缓存调参无法解决。

## 更新：惰性替换（闭包求值，LAZY=1 启用）

- 新增基于闭包的弱头范式机（whnf_core_lazy）：beta、let 和递归子规则展开只往环境里压入 thunk（项 + 环境），不复制；只有最终需要的参数才通过 instantiate_env 代入并回读成项。被丢弃的证明项和未选中的 minor 不再被复制。
- thunk 与环境存放在草稿数组中，调用返回时截断；进入 exprs 的只有已代入的项，哈希化不变。
- BVar 在头部位置时先强制并走 whnf_core 缓存，避免丢失共享（否则 shared-subterm 呈指数级）；燃料仍按调用计数，与旧口径一致，否则预算策略会过早中止。
- 正确性：LAZY=1 下 Arena good 136/138、bad 92/92 拒绝，与默认模式一致。
- 效果有限：magma-list-pair-n7 新建表达式 7.16M -> 4.5M，耗时 4.7 s -> 3.5 s；但 unfold-before-literal 73 s -> 110 s，deep-n36 9.8 s -> 34 s，故默认仍用急切实现。
- n21 / n36 仍超限：剩余的表达式主要来自强制 major 与回读时必须复制的含证明的项（WhnfCore 3.5M、Unfold 0.95M）。要彻底解决需要让 Susp（延迟替换）节点成为 Expr 一类，并让 infer / def_eq 都识别它。

## 更新：区域回收（good 138/138）

根因不是单步开销，而是表达式池只增不减：n21 约 19.5 万个四元组，每个约 3000 个节点，合计数亿个节点，而其中绝大部分在一次 whnf / def_eq / infer 返回后就再也不可达。

- 区域回收（gc_region）：whnf、def_eq、infer 入口记下表达式池水位；返回时若新增超过 400 万个节点，只保留返回值可达的部分并滑到水位处，其余截断。调用者手里只有水位以下的 id，所以安全。
- 缓存失效：每个槽位记录它被填入时的回收轮次（born），缓存项记录写入时的轮次和它引用的最大 id；槽位被重用后旧缓存项自动失效。
- 修复一个潜在的错误结果：大数转字节串时，库函数读最高字节会越过最高 digit，读到未清零的内存，结果随内存布局变化（gf3-matrix-product 偶发失败）。现在屏蔽最高字节的多余位。
- 单声明燃料上限 3000 万 -> 30 亿（由超时兜底）。

| 项目 | 之前 | 现在 |
|---|---|---|
| Arena good（上限 400 s，按各测试官方超时） | 136/138 | 138/138 |
| Arena bad | 92/92 拒绝 | 92/92 拒绝 |
| magma-list-pair-n21 | 资源超限 | 38 s（官方超时 240 s） |
| magma-list-deep-n36 | 资源超限 | 187 s（官方超时 360 s） |
| unfold-before-literal | 73 s | 84 s |
| 完整 Init | 58530 / 16，151 s，3.5 GB | 58530 / 16，181 s，3.9 GB |

Init 仍拒绝的 16 个：4 个 Int32/Int64 的 instRx*HasSize_eq 触发资源上限，其余 12 个连带失败。
