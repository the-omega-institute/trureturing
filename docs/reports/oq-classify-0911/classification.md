# observer-quantum-v1 residual-open 分类

已分类 0 / 131。当前文件为分批提交的分类工作报告。

范围：base `875f99765a05f2f6819e7352062fd2ce8c6afa2d`，工作树分支 `lane/theory/oq-probe`。实数目录 `Meta/Digestion/backfill/observer-quantum-v1/residual-open/` 有 131 个 YAML。按完整 atom ID 字典序顺序处理；此顺序仅用于遍历，不是选题排序。每个计入完成数的 atom 必须实际成功执行 `make show-atom ATOM_ID=<完整 ID>` 并读完正文与 coverage。

产地：无 skill，Codex 主循环直接分类；零独立评审席，单点自查。用户已给出的黄金分账 bind 判定作为用户输入沿用，不重做其证明。

本席仅交付分类，不修改 Lean、理论源、atom、coverage、冻结状态，不执行 ingest、cover、deposit。通用证明席模板的 Lean 构建、公开定理 proof_shape / 依赖 / escape_witness / admission_basis 和 PR 成功条件不适用于本次报告；以任务专门要求为准。

## 读取工具收据

首次 `make show-atom ATOM_ID=c74925a3c3098b69` 返回 make exit 2：

```text
Unhandled exception: An error occurred trying to start process '/Users/chronoai/trureturing-oq-probe/tools/StrataLint.Cli/bin/Release/net10.0/StrataLint' with working directory '/Users/chronoai/trureturing-oq-probe'. No such file or directory
make: *** [show-atom] Error 1
```

这是 CLI 尚未构建；已启动 canonical `make -C tools dotnet`，构建后用完整 ID 重试。此失败不算已读、已分类。

当前理论源卷首使用「条件性重构」；旧 CAS `c74925a3…` 的卷首仍使用「强制出身」。分类的对象是 `show-atom` 输出的 CAS 正文，不以当前源卷替换旧 atom。

## 未主张

未主张任何数学命题已获 Lean 验证、任何 residual 已闭合、任何开放物理问题已解决；不选择、排序或推荐四个 τ=0 候选。未运行 `make lean`，耗时和 `LEAN_CACHE` 均为不适用；尚未打开的外部页面一律 `ASSUMED-UNVERIFIED`，不作命中依据。
