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

## 更新：完整 Init 全部通过（58546 / 0）

被拒绝的 4 个声明是 Int32 / Int64 的 instRxcHasSize_eq、instRxiHasSize_eq（Int8、Int16 版本能过，说明开销随位宽增长）。

- 现象：报的是“资源上限”，实际燃料只用了约 200 万，触发的是单声明 2000 万新表达式的上限。展开直方图里 Nat.add._f、Nat.casesOn、Nat.add.match_1 各约 29 万次，跟踪里是一条从 2147483648（2^31）开始逐一减 1 的 Nat.rec 链。
- 根因：def_eq 比较 `Nat.sub A B` 与 `HSub.hSub A' B'`（A、B 含自由变量 lo、hi，形如 `BitVec.toNat (rotate 32 x)`，即 `(x + 2^31) % 2^32`）时，先对左侧尝试 Nat 字面量算术，于是把操作数求 whnf。x 是变量，`%` 和 `≤` 只能按结构递归逐个后继展开，要走 2^31 步。
- 官方内核在 lazy delta 里只对两侧都不含自由变量的项尝试 Nat 字面量算术，所以它直接展开右侧的 HSub.hSub，两边在 `Nat.sub` 处对齐后逐参数比较就结束了。
- 修复：Expr 增加 hasfv 标志（建节点时由子节点合成，不参与哈希与相等；Expr_Kind 改为 u8，结构体仍为 72 字节）；def_eq 中的 reduce_nat 仅在两侧都闭合时尝试。whnf 中的 reduce_nat 不加此限制（nat-shift-huge 的 Open 用例要求开项在操作数化为字面量后仍能归约）。
- 调试辅助：环境变量 `ONLY=<声明名>` 只检查一个声明、其余信任；`PROF=1` 下回收时打印展开次数超过 2000 的常量（UNFOLD 行）。

| 项目 | 之前 | 现在 |
|---|---|---|
| 完整 Init | 58530 / 16，181 s，3.9 GB | 58546 / 0，115 s，1.7 GB |
| Arena good（上限 400 s） | 138/138 | 138/138 |
| Arena bad | 92/92 拒绝 | 92/92 拒绝 |
| magma-list-deep-n36 | 187 s | 220 s |
| unfold-before-literal | 84 s | 97 s |

Arena 两个最慢用例本轮比上一轮慢约 15%，未做重复测量，不能区分是机器波动还是 hasfv 计算的开销。

## 更新：性能回退分析

上一轮 Arena 最慢的两个用例变慢约 15%，用交替重复的 CPU 时间（magma-list-deep-n21，每版 4 次）定位：

| 版本 | CPU 时间 (s) |
|---|---|
| 旧版（区域回收后） | 5.7 – 6.7 |
| 上一轮（Expr_Kind 改为 u8 + hasfv） | 6.1 – 6.6 |
| 去掉 hasfv，保留 u8 枚举 | 6.2 – 6.8 |
| 去掉 hasfv，枚举恢复默认 | 5.6 – 6.0 |
| u32 枚举，hasfv 放在 kind 之前 | 5.4 – 5.9 |

- 工作量没有变（app-lam 的新建表达式数和调用数两版完全一致），所以是每次访问的常数开销。
- hasfv 的计算本身几乎免费；变慢来自把 kind 改成 u8。1 字节枚举与相邻字段混在一个字里，kind 的读比较与 hash 取值要做零扩展和部分字读取，热路径上每次都付；去掉后恢复。
- 采用 u32 枚举 + bool 放在 kind 前面：结构体仍是 64 字节，速度不低于旧版。
- 完整 Init：58546 / 0，105 s（上一轮 115 s），1.7 GB；Arena good 138/138，bad 92/92 拒绝。
- 上一轮表里 unfold-before-literal 84 s 到 97 s 的差异主要是机器负载波动，旧版与新版重测都约 100 s。

## 实验：缩小 Expr 结构体 / 拆分冷字段（未采用）

目标：验证“把冷字段拆出去、让节点更小、缓存行利用率更高”是否有收益。做法：把 16 字节的切片 us 换成驻留表 id（4 字节），hasfv 压进同一个字的最高位，节点从 64 字节降到 48 字节；lbr 在 instantiate 里是热字段，没有拆。

| 版本 | 节点大小 | magma-list-deep-n21 | app-lam | 完整 Init | 峰值内存 (Init) |
|---|---|---|---|---|---|
| 当前（u32 枚举） | 64 B | 5.5 – 6.4 s | 26 – 30 s | 108 – 111 s | 1727 MB |
| us 换成 id + u16 枚举 | 48 B | 5.7 – 6.7 s | 32 – 33 s | 109 – 113 s | 1604 MB |
| 同上，u32 枚举，hasfv 单独一字节 | 56 B | 5.6 – 6.5 s | 27 – 28 s | 未测 | 3890 vs 4196 MB (app-lam) |
| 同上，u32 枚举，hasfv 压进 id 最高位 | 48 B | 未测 | 31 – 34 s | 114 – 117 s | 1604 MB |

- 内存省 7% – 14%，但时间持平或慢 3% – 20%，所以没有采用，kernel.odin 保持上一版。
- 原因推测：64 字节节点恰好与缓存行对齐，一次访问一条线；48 / 56 字节的节点会有一部分跨两条缓存行，下标计算也不再是移位。u16 枚举同样会慢一截，与 u8 枚举的现象一致。这是推测，没有用硬件计数器验证。
- 结论：想靠布局获益，要么保持 64 字节对齐，要么真正按访问模式拆成并行数组（kind/a/b 与 c/d/lbr 分开），而不是把整个结构体压小。后者没有做。

## 更新：在本地上下文里检查绑定，不再复制整个函数体

热点是 `AddExpr`。let 塔、单参数 beta 链和共享 lambda 参数都会对函数体做 Θ(n²) 的实例化拷贝。`app-lam` 没有推断缓存时是指数级的。

做法：

- 推断 lambda / pi / let 时把绑定压进本地 de Bruijn 上下文，直接检查函数体。let 只把检查得到的类型用值代入，不再把值代进整个函数体。上下文里的 let 在 whnf 里做 zeta。
- 开放的代入项在进入绑定词下时按深度提升（`lift`）。闭合代入项不提升，指针与旧路径相同。`instantiate_n` 同样提升开放参数（`Nat.below` 这类多参数归约会用到）。
- 含自由 bvar 的缓存键带上上下文戳。戳只增不减，弹出时恢复外层戳，同一上下文里的兄弟子项（`app-lam` 的共享参数）命中同一条缓存，后一个绑定词看不到前一个的条目。
- 定义等价仍然用新自由变元打开 lambda / pi。自由变元的类型记在创建时的深度上，读类型时按当前深度提升。不提升的话，共享的 `List #0` 会在更深层被当成当前证明变量，推断递归到栈溢出（`ite-taken-branch` 等）。

测量：`arena/bench.py` 的方法。用户态 CPU（`ru_utime`），`taskset -c 0`，`ulimit -s unlimited`，基线与新内核交错重复。基线是本改动之前的 `-o:speed` 构建。样本标准差。

| 用例 | 次数 | 基线 mean (sd) | 新内核 mean (sd) |
|---|---|---|---|
| let-ladder | 5 | 1.810 (0.043) | 0.016 (0.003) |
| app-lam | 5 | 19.313 (1.912) | 0.028 (0.006) |
| beta-ladder | 5 | 3.392 (0.241) | 1.884 (0.051) |
| magma-list-pair-n7 | 5 | 3.055 (0.150) | 3.009 (0.056) |
| magma-list-deep-n21 | 5 | 4.694 (0.185) | 4.722 (0.270) |
| magma-list-pair-n21 | 3 | 26.349 (0.593) | 25.618 (1.896) |
| magma-list-deep-n36 | 3 | 111.522 (0.889) | 111.662 (0.906) |
| gf3-matrix-product | 3 | 21.394 (0.202) | 21.300 (0.026) |
| unfold-before-literal | 3 | 54.032 (1.571) | 55.549 (2.461) |
| unfold-before-literal-fallback | 3 | 56.649 (1.922) | 55.427 (0.926) |
| shared-subterm | 5 | 0.054 (0.012) | 0.038 (0.007) |
| church-numerals | 5 | 0.039 (0.006) | 0.042 (0.014) |
| discarded-argument | 5 | 0.009 (0.003) | 0.004 (0.003) |

let-ladder、app-lam、beta-ladder 的差距大于方差。其余用例的均值差落在标准差里，不记为收益。beta-ladder 剩下的时间仍是急切 whnf 对梯子的拷贝。

正确性：`python3 arena/run.py ./kernel 400`（脚本自带 `ulimit -s unlimited` 与 `ulimit -v 7000000`；这套测试没有 yaml，超时上限用的是 400 秒）。good 138/138 接受，bad 92/92 拒绝，没有超时或崩溃。没有改检查规则，也没有跳过证明。

未做：

- 没有把默认切到 `LAZY=1`。它能再消掉 beta-ladder 的拷贝，但以前会拖慢 unfold-before-literal 和 deep-n36，这次没有重测那条组合。
- n21 / n36 仍是每次 beta 都实例化大证明项。要再降需要把延迟替换做成表达式节点。并行数组布局也没做。
- 环境里没有完整 Init 导出，这次没有 Init 数字。

## 更新：大函数体的 beta / let 交给闭包机

急切 whnf 在替换一个大函数体时，会复制代入变量能到达的每个节点。`beta-ladder` 因此是 Θ(n²)。`LAZY=1` 整段切到闭包机能消掉这次拷贝（beta-ladder 约 1.8 s → 0.03 s，deep-n36 约 101 s → 63 s），但 unfold-before-literal 从约 52 s 退到 75 s，因为小 beta 上闭包机的常数更大。

做法：仍从急切机出发。只有 let 体或即将代入的 lambda 体超过 96 个节点时，把这一次 whnf 的剩余部分交给闭包机。节点数走到预算就停，DAG 不会把它撑爆。`EAGER_BETA=1` 恢复旧的复制路径，`BETA_NODES` 可改阈值。96 是量出来的：64 会让 pair-n7 变慢，256 接不住 magma 的证明体。

对照的是上一轮（本地上下文推断、急切 beta）的 `-o:speed` 构建。用户态 CPU，`taskset -c 0`，交错重复。

| 用例 | 次数 | 上一轮 mean (sd) | 本轮 mean (sd) |
|---|---|---|---|
| beta-ladder | 3 | 1.775 (0.037) | 0.023 (0.005) |
| magma-list-deep-n21 | 3 | 3.499 (0.053) | 2.813 (0.031) |
| magma-list-pair-n21 | 2 | 21.872 (0.392) | 20.547 (0.259) |
| magma-list-deep-n36 | 2 | 104.355 (1.584) | 79.012 (2.169) |
| unfold-before-literal | 1 | 52.788 | 52.931 |
| magma-list-pair-n7 | 3 | 2.539 (0.276) | 2.532 (0.087) |

beta-ladder、deep-n21、deep-n36、pair-n21 的差距大于方差。unfold 和 pair-n7 落在方差里。全程 `rc=0`。

正确性：`python3 arena/run.py ./kernel 400`。good 138/138 接受，bad 92/92 拒绝。

未做：闭包机仍在返回时把中性项的参数强制回表达式，被丢掉的证明如果出现在最终脊柱上还是会被复制。要把 deep-n36 再降下去，需要延迟替换本身成为表达式节点。完整 Init 这次没有测。
