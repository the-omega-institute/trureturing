# 摄入闭合探针卷

*(**非理论内容**。本卷是 SPEC-THEORY-INGEST-CLOSURE-001 的端到端探针:在真实 CI 上验证
`theory-ingest` lane 改造后的红/绿行为。验证完毕即撤销,**不入 dev**。)*

---

## 1. 探针要验证什么

改造后的 lane 判据是:排除 base-harness overlay 覆盖的路径之后,候选树上跑完 `make ingest`
是否已无残留。本卷用同一个 PR 制造前后两个状态,观察判词是否随之翻转。

**定义 1.1(闭合态)。** 候选树 T 称为**闭合的**,若在 T 上执行 canonical `make ingest` 之后,
排除 overlay 路径的 `git status --porcelain` 为空。

**定义 1.2(开放态)。** 候选树 T 称为**开放的**,若其理论输入已变更而对应消化账目未随之更新,
即 T 非闭合。

**命题 1.3(探针的两个观测点)。** 设 PR 的第一个提交只带理论卷与消化源登记而不带账目,
第二个提交补上 canonical `make ingest` 的全部产物。则第一状态为开放态、第二状态为闭合态;
若 lane 的判据成立,其结论应在两个状态间由红翻绿。

**注 1.4。** 旧形态下该观测不可执行:候选路径白名单会在判据之前就拒绝 `source.toml`,
两个状态都得到同一个红,故无法区分「账目未闭合」与「带了非白名单路径」。

## 2. 预期判词

**规格 2.1(开放态)。** 判词应含 `THEORY-INGEST-CLOSURE-001`,并点名未闭合的具体路径,
其中应出现本卷对应的 `Meta/Digestion/backfill/<source_id>/` 下条目与 `Meta/Digestion/atoms/` 下 CAS blob。

**规格 2.2(闭合态)。** lane 应绿,且不产生任何回写提交——改造后它已无 `contents: write`。

## 3. 撤销条款

**条目 3.1。** 本卷、其消化源登记、其 registry 序位与其账目,均随探针 PR 一并关闭,不合入 dev。
探针的产出是两次 CI 观测记录,不是仓库内容。
