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
