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
