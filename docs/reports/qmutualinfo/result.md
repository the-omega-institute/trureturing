# 偏迹与互信息修复报告

**本轮端化：成。** 按用户本轮构建与门链判据，三项目标全部完成。
两个偏迹产生真正的 DensityState 边缘；互信息只收联合态；任意乘积密度态
（含奇异态）的互信息为零。一般联合态的互信息非负不在本次所选第三靶内。
本席 implementation 工件已 commit 并 push；此结算不宣称 PR 已合入。

产地：Codex implementation 席，lean4 skill；本席直接实施、单点自查，零独立评审席。
形式：deposit-uncovered；没有自写理论卷、摄入或 coverage 边。

## 目标与来源

保留两个偏迹定义、加性及 Kronecker 公式。新增偏迹保半正定、保迹，构造
marginalLeft（保留 B）与 marginalRight（保留 A）；quantumMutualInformation
只接受 DensityState (A × B)。旧三参数接口和 rfl 公式定理已移除。
非平凡目标为任意 productState 的互信息为零，包括奇异密度矩阵。

预登记见 preregistration-v1.md、preregistration-v2.md。第三方精确命中后，
在实施前改为 rule-11-upstream-wrapper；不把移植的数学申报为原创逃逸。
必要性是用户指定的 DensityState/偏迹 API 接线义务。
utility: none；全部声明为任意有限维的一般矩阵或态结果，无四类计算性内容。

## 先库后证收据

本树起点 f0ffd4b4ea；Lean v4.33.0，Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d。

| 范围与查询 | 结果与使用 |
| --- | --- |
| D5/S3/Quantum：partialTrace、partial_trace | 既有本模块；LocalObservationPartialTraceEquivalence.partialTraceFirst 及其消费者。没有通用保态或熵张量可加性命中。 |
| D5：entropy 与 tensor/prod/kronecker | 有经典 Shannon 熵结果；未命中本题的量子谱熵定理。 |
| 整个钉版 Mathlib：`rg -n -i 'partial.?trace\|mutual.?information\|von.?neumann.?entropy\|entropy.*kronecker\|log_kronecker'` | exit 1，零命中。只表明该检索范围未命中。 |
| Mathlib Matrix PosDef/Order/Kronecker | 精确复用 PosSemidef.submatrix、posSemidef_sum、PosSemidef.kronecker、trace_kronecker。 |
| Mathlib Log/NegMulLog | 精确复用 Real.negMulLog_mul；未移植上游同名自证引理。 |
| `gh api -X GET search/code -f 'q=partialTrace language:Lean'` | total_count=158，读取默认第一页 30 项。发现 csd-lean4、quantum-system、physlib、Lean-QIT；不声称穷尽。 |
| csd-lean4 固定版本源码 | 精确命中偏迹保态及无条件谱熵 Kronecker 可加性；移植必要证明，来源及完整许可见 blore2026partialtrace Library note 与 LICENSE 文件。 |
| quantum-system 固定版本 8562b28c0c6b0796ebbbdd2893d26213f687ed04 | 已读 KroneckerProduct.lean；matrixLog_kronecker_posDef 只覆盖正定矩阵，未用它冒充奇异态结论。 |

实际网络能力为 authenticated gh 和 curl，均取得源码；未修改宿主配置。
csd-lean4 的 toolchain/mathlib 与本仓完全相同；A17 依赖形的自动准入谓词
仍 open，使用 A17.2 移植形。上游根树含 LICENSE，不含 NOTICE；文件声明
Copyright (c) 2026 Zayn Blore，Apache-2.0，已保留。
退役条件：本仓钉版 Mathlib 出现对应声明时，删除移植证明并直接引用。

## 判形与有向依赖

本模块公开定理均按 bind-only、admission_basis=rule-11-upstream-wrapper、
escape_witness=none 报告。移植证明不是零内容，但其内容的来源为上游。
以下是每条公开定理的用途边，方向均为“消费者 → 前置”。

| 公开定理 | 具体义务与边 |
| --- | --- |
| partialTraceLeft_add | 保留既有偏迹线性 API；具名用途为 partialTraceLeft 的加法计算。 |
| partialTraceRight_add | 保留既有偏迹线性 API；具名用途为 partialTraceRight 的加法计算。 |
| partialTraceLeft_kronecker | marginalLeft_productState → 此式。 |
| partialTraceRight_kronecker | marginalRight_productState → 此式。 |
| trace_partialTraceLeft | marginalLeft → 此式。 |
| trace_partialTraceRight | marginalRight → 此式。 |
| partialTraceLeft_posSemidef | marginalLeft → 此式。 |
| partialTraceRight_posSemidef | marginalRight → 此式。 |
| marginalLeft_productState | quantumMutualInformation_productState → 此式。 |
| marginalRight_productState | quantumMutualInformation_productState → 此式。 |
| vonNeumannEntropy_productState | quantumMutualInformation_productState → 此式。 |
| quantumMutualInformation_productState | 用户第 3 项终点：实际边缘下乘积态互信息为零。 |

直接冻结的公开定理前置：上述声明均无（不应用 pinching 定理）。
冻结定义依赖是 QuantumRelativeEntropyDefectComposition.DensityState 与
VonNeumannEntropyPinching.vonNeumannEntropy；模块身份分别为
sha256:445d28204f4c839e9d5711f568c7f8a3259e36bcff54986168a827333cbdbb5d 与
sha256:7e20a9a8027e14e93fe22cd7900dc1a94b48a57dcb9f97b27d4815f8e9b61a00。
GID 前缀均为 D5/S3/Quantum/Divergence/。定义级身份：
- QuantumRelativeEntropyDefectComposition.DensityState：
  sha256:b8e1957ba4f81600248989dc21f0a107bcdd5ce2e68546c38b9164c4a09ac337。
- VonNeumannEntropyPinching.vonNeumannEntropy：
  sha256:9cf1e21822d8f3f61a5d349f41c4287a3ef43a0e8a600534b28ab8d06f437cd1。

两者是实际使用的定义，不以 import 关系冒充 pinching 定理的活推导边。

落点：Quantum 已注册为 S3；现有两个 D5 import 均 generality G。
目录文件计数：Information Lean 1，Blueprint Information 1（不计 .md），
Library/Quantum 16，均小于 48。

## 可复用的失败记录

serial-lean 按缺失 olean 选择模块；旧 trace 存在时曾恢复旧 olean，首个
status=complete 未核验新源码。该读数不算本轮证明通过。后续只清理本模块
的 olean 与 trace，再经同一 serial-lean 入口真实编译；没有清库或动两条重模块。
临时 lake 包装器只保存原始日志并原样转发参数/退出码，不跳检查。

CStarMatrix 的谱序与 Matrix 的半正定序不是定义相等；直接 change 失败，
Lean 打印的 marginal 公理闭包含 sorryAx。修复用
CStarMatrix.ofMatrixStarAlgEquiv / symm 的 map_nonneg，重新编译后
两个边缘态的闭包只有 propext、Classical.choice、Quot.sound。

谱熵移植保留特征值的多重集推导，避免把排序特征值逐项等同于乘积索引。
零特征值由 Mathlib Real.negMulLog_mul 处理，不增加正定假设。

乘积态边缘等式曾在 `rw` 阶段触发 CStarMatrix 的半透明类型转换错误；
改用显式矩阵迹等式和 `congrArg CStarMatrix.ofMatrix` 搬运已有 Kronecker
公式后通过。内部的表示还原使用 rfl；公开的乘积互信息定理实质依赖两个
边缘恢复引理与谱熵可加性，没有把定义展开当作第三项目标。

数学增量提交：2a54c67164（接口初稿，旧缓存读数无效）、
da01bbdc20（真实编译的保态转换）、dabc96708a（完整乘积态互信息证明）。
最后一次 serial-lean 真实重建本模块，Built 48s，退出 0；
哨兵 `SERIAL_LEAN status=complete built=1 failed=0 missing=1`。
主定理和两个边缘态打印的公理闭包仅为 propext、Classical.choice、Quot.sound。
完整 log 位于 runner attempt 的 serial-lean-build.log。

## 门链

按指定顺序运行：serial-lean → make lean-report → make emit → make deposit-uncovered。
四步最终退出码均为 0。lean-report 的报告 SHA-256：
5211a93b9d0f1811912e47d9ce206cb0674e6a8a68da3ec1fe5d65ab1b74bb28。
首轮 emit 因 FromLean 自动公式投影缺少新声明而退出 2；改用绑定声明的
FromAuthor 公式后退出 0，生成 1 篇 Blueprint，未改判官。

deposit 的 GID 为
D5/S3/Quantum/Information/PartialTraceMutualInformation.quantumMutualInformation_productState；
DEPOSIT_HEADER_CHECKED SL-012，LEDGER_ALIGN added=1 conflicts=0，
PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED reason=NO_ATOM。没有 coverage 边。
日志位于 runner attempt 的 lean-report.log、emit.log（失败）、
emit-author-formulas.log（成功）、deposit.log。
额外按用户要求运行 scribe-content-checks.sh，第三参数为精确 merge-base
bc401f09ba6919eb52582a8530c23612049e7de8，退出 0。判词：
`DESCRIBE_STATUS case=DESCRIBE-NODES status=classified nodes=11074 suspected_novel=0 formula_content_slots=66 formula_statements=32 red=0 observe=4982`。
`^RED` 行数为 0；OPEN projection / OBSERVE 不当成通过依据。
完整输出为 runner attempt 的 scribe-content-checks.log。

冻结模块 statement_id：
sha256:b39b445e3b813fed9a6aa4620394e2e19833848984a628545b0210c168467450；
accepted event 文件：
Golden/Frozen/accepted/d497a7e01310e9317dd1b4995b4bfb880a89b2ebe20afb032e47e11667c8368b.json。
文档与冻结提交 7fffa5f678。没有绕门、降级检查或新增公理。

Runner 工件目录：
/var/folders/wv/ht3wzsj138b4sxl3q4t0xdr40000gn/T/consensus-rnd/sshx/qmi2-1/attempt-1。
result.json 在临时文件写完后原子改名，随后以同样方式发布 completion.sentinel。
本报告副本 final-report.md 是结果 envelope 的 log_ref。

## 最终声明身份

以下 18 个公开声明与 11 个私有辅助的公理闭包均仅含
propext、Classical.choice、Quot.sound；以退出 0 的 canonical lean-report 为准。

| 公开声明 | statement_id |
| --- | --- |
| marginalLeft | sha256:7579934e8cf68c9a1e1f14470e58e70c66939704953b29e953ae8d75b92bef6a |
| productState | sha256:a227a004102880bc79685377a2fa13a3a5134389ff6544ba0c606ba4403fbb22 |
| marginalRight | sha256:bb5bad02426b231285a1d49fbc7f66f6f971cf3cd7ef3ee92fc2c21793f14ae7 |
| partialTraceLeft | sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d |
| partialTraceRight | sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77 |
| partialTraceLeft_add | sha256:e6760db4f2b81a485feb8f32a73a245853102feb954e6212826a771dd28dbaf3 |
| partialTraceRight_add | sha256:b9bdbbf9eb046a8b8b45384527347b653edead7fd52e914aa4b6ebbd144f8a39 |
| trace_partialTraceLeft | sha256:70e429b7996075b0f25052d5fb6f603c2ac2556abcf0d2510142499e0c5d267c |
| trace_partialTraceRight | sha256:2e0d10f59a41befee8bb5e380b1d8d7db7e14a2bbed6d47af5089807c0905813 |
| quantumMutualInformation | sha256:650358808a68c73893baf137ee9bae34238244b7e0906ce19e6b5fd68484ad75 |
| marginalLeft_productState | sha256:a9840d043b5a8d2b0917f100f01c7f02a319c9363b7ba18fc4050e59e2321393 |
| marginalRight_productState | sha256:cafa71401e68066df56033c6466fde4878d18496f8ef43e8f2600b6a0074ef76 |
| partialTraceLeft_kronecker | sha256:1fa42c02a50864971045c3c86abddd8fc906aca8723acb97552cdd92c7196b9d |
| partialTraceLeft_posSemidef | sha256:57037555d268cd6c22ff19563a5f64496a1d89f7e5d8b6b98943b78b84af873d |
| partialTraceRight_kronecker | sha256:a0838f79000777eac14a35e86139cd9f264a8cd9569370843c5210242ee58673 |
| partialTraceRight_posSemidef | sha256:534be990ab7c643fd18c2a086aa7a7b696bb02a8baa49a26c15e479b63e74944 |
| vonNeumannEntropy_productState | sha256:c282fec63ac9abe78f2927a141bb4576d82585b91d0085e4a160f9a9b6efd042 |
| quantumMutualInformation_productState | sha256:418f910430dfa25dba864e6db75676d2f44e0e9c1d6c3fc49302f5893813dc6f |
