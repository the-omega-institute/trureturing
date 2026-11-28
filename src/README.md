# 在 D5 中使用 OmegaMath

D5 和 Reg 从本仓钉定的 OmegaMath release 导入数学模块。Lake 解析的源码版本记录在根 `lake-manifest.json` 的 `omegamath` 条目，依赖源码位于 `.lake/packages/omegamath/`。trureturing 在根 Lake 配置中直接钉定 Mathlib，Reg 继承这个版本。引用 Mathlib 的证明放在 D5。可用独立基础编译的通用数学和严格移植提交到 [OmegaMath 仓库](https://github.com/the-omega-institute/omegamath)。

升级发行版本时，将上游 Release 的 `omegamath-release.json` 保存到 `Meta/omegamath-release.json`，一并更新根与 Reg 的 Lake 锁文件。在宿主根目录运行 `make verify-omegamath-release`，核对上游源码 SHA、Lean 工具链和本平台下载的 archive SHA-256。校验通过后，命令解包，并用 Lake 的 `--no-cache --no-build` 检查 `OmegaInit`、`OmegaMathlib`、`OmegaMath`、`OmegaBuild` 和 `omegaBackendPlan` 的编译产物。

## 选择编译后端

按具体符号导入最小模块。普通消费模块可用两端共有的接口，例如 `OmegaMath.Data.Nat` 的 `Omega.Nat.square_mul`。需要官方 Mathlib 专有接口的模块导入 `OmegaBuild.Commands`，在全部 `import` 之后、首个数学声明之前写 `compile_only_with_mathlib`。直接和间接导入这个模块的消费者继承后端选择。两个完整的 Lean 示例和它们的编译要求见钉版依赖的 `src/README.md`。

在本仓编译实际使用的 D5 或 Reg 目标，使用 `make lean LEAN_TARGETS="D5.S0.Computability.GuardedWall"`。针对某个 D5 声明核对公理和库来源时，使用 `make lean-report-scoped LEAN_TARGETS="D5.S0.Computability.GuardedWall"`，按所选后端解读报告。[冻结状态与发布口径](../docs/develop/spec/golden-ledger-repo-spec.md#omega-claim-fidelity)
