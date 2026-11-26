# 官方 Init 的独立内核移植

从仓库根目录运行，使用 `lean-toolchain` 指定的 Lean。以下命令编译严格基础，然后生成一个可直接导入的模块目录。生成目录须尚未存在。

```sh
python3 src/OmegaChecks/strict_lake.py build +OmegaInit
python3 src/OmegaChecks/InitPort/build.py .lake/init-port Init.Prelude
LEAN_PATH=.lake/init-port/lib lean Example.lean
```

`Example.lean` 可以直接使用新生成的积类型与投影。

```lean
prelude
import OmegaInit.Prelude
open Omega

example (a : α) (b : β) : Omega.Eq (Prod.fst (Prod.mk a b)) a := Omega.rfl
```

生成的 `OmegaInit.Prelude` 提供 `Omega.Quot`、`Omega.Quot.mk`、`Omega.Quot.ind` 和 `Omega.Quot.lift`。普通导入支持两个消去子的构造子归约。Lean 内核按固定的根名称识别商类型和等式，在打开 `Omega` 命名空间的外部代码中可用 `Omega.Eq` 指定移植的等式。

位置参数接受一个或多个官方模块名。省略这些参数会扫描钉版工具链的所有 `Init` 模块，包括需要单独导入的模块。构建整个库可运行 `python3 src/OmegaChecks/InitPort/build.py .lake/init-port-all`。加上 `--seed PATH` 可选择另一个已编译的严格种子，默认读取 `.lake/build/omega-strict/lib/lean`。工具把种子的编译文件复制到独立临时目录，随后从钉版官方模块逐个翻译依赖、证明项、定义、归纳族和递归器。每个候选声明都在 Lean 内核中检查。环境变量 `OMEGA_PORT_HEARTBEATS` 为每个候选声明指定原始心跳预算，默认 5000。

`inventory.jsonl` 按顺序记下官方模块名、声明名、公开标记、移植结果和直接阻塞依赖。`added` 包含内核生成的构造子、递归器、私有及编译器内部声明。`existing` 表示复用种子中的声明。`interface-rejections.jsonl` 保存无法通过仓库官方对应检查的候选。公理、商原语、unsafe 或 partial 声明、未支持的表达式和依赖缺失均有逐项记录。

`lib/` 保存按官方定义模块组织的编译文件。程序对所选的基础库模块运行仓库的 `omegaAudit --exact-roots`，检查模块闭包、公开归属和可计算对应，逐声明检查公理并从空环境重放内核。全量构建还将 OmegaMath 和 OmegaMathlib 的下游源码编译到同一 `lib/`，验证普通 `import OmegaMath`，并审计其实际导入闭包。成功后输出目录才会出现。两次审计的读数分别保存在 `audit.txt` 和 `omegamath-audit.txt`。全量缺口表位于同一目录的 `init-gaps.tsv`。

这个独立制品用于内核类型检查、证明和定义归约。新生成声明的原生可执行代码、语法扩展、实例搜索和结构字段语法均不在移植覆盖范围内。

公开覆盖清单按官方定义模块和声明名逐项列出，重复生成的名字在各自模块有独立记录。
`init-inventory.json` 的 `summary` 按模块与名字的组合计数，`uniqueNames` 按名字去重。
全量构建也编译可单独导入的 OmegaMath 和 OmegaMathlib 源文件，一同审计它们的传递依赖。
缺口表的 `firstDependencyPath` 和 `reason` 记录本次移植实际遇到的阻塞。只有 `impliesAxiom` 非空的行另有内核证明，从该官方接口可推出所列公理。`logicalConsequence` 与 `logicalConsequenceWitness` 给出其他已验证的逻辑后果及其证明。`requiredBehavior` 非空时，证明还需要候选实现满足该项行为前提。

`init-public-reductions.tsv` 列出已移植声明到严格库封装实现的一条最短定义体依赖路径。`officialReductionMechanism` 记录钉版 Lean 的官方机制，包括公开定义体、自然数内建运算、归纳类型、构造子和递归器。盘点 JSON 同时保存路径 `publicReductionBoundary` 与机制。`Nat.Coprime` 的路径通向内建运算 `Nat.gcd`。`And.rec` 和 `Iff.rec` 在官方环境中使用递归器计算规则。具体输入是否需要走到路径终点取决于归约过程。

例如，普通导入 `OmegaInit.Data.Nat.Div.Basic` 后可用 `Omega.Nat.div_zero` 证明除数为零的等式。若需直接归约严格实现，可 `import all OmegaInit.Prelude`，并在证明所在节设置 `attribute [local semireducible] Omega.Nat.div Omega.Nat.ble Omega.Nat.sub Omega.Nat.pred`。

完整性验收从安装的钉版 Lean 和待验制品重新读取每个官方公开定义点。运行以下命令，退出码 0 表示全部非公理定义点已通过实际接口审计，或已在源码中逐项登记官方原类型推出公理的证明。遇到尚未解决的定义点，命令写出当前清单和缺口数，然后以退出码 1 结束。

```sh
python3 src/OmegaChecks/InitPort/report.py .lake/init-port-all --require-complete
```

逐项登记位于 `src/OmegaChecks/InitInventory.lean` 的 `OmegaChecks.InitBoundaries.reductions`。条目包含官方定义模块、声明、目标公理和见证。Lean 核对指定模块内保存的声明类型，并检查见证可将该类型的任意实现转为目标公理的同类型实现，并从空内核重放见证及其传递依赖。受理的结论为任意类型的选择、命题外延性，或由任意类型的无条件取值推出矛盾。编译器公理中也有可构造的类型，例如可以用任意已有类型实现 `lcAny : Type`。例如，对两个等价命题分别应用 `Classical.propComplete`，在同真或同假两种情形下得到命题相等。将 `WellFounded.extrinsicFix` 用于自关联的单位类型，令递归分支直接自调用，原接口就必须从 `Nonempty α` 返回 `α`。给定 `unsafeCast` 原类型的任意实现，可以将单位类型的元素送到任意类型，得到 `sorryAx`。报告中的 `reductionWitness` 指向对应 Lean 声明。原证明的公理闭包、未支持原语和编译器限制保留在缺口明细中，完整性验收只接受有见证的缺口。

公开定义点全部结清时，验收命令还逐模块复查实际公开公理记录，从空内核重放整个严格 Init，并以 `omegaAudit` 核验官方名称、定义模块、类型及计算接口。

缺口表的 `abstractedDependency` 标明归约中被全称量化的官方对象。例如，任选一个与 `Option.choice` 同类型的函数，若它在每个非空类型上返回的可选值都满足 `toList.length = 1`，就能从该值取出元素，构造 `Classical.choice`。Lean 会从官方声明的类型中抽出该选择函数，核对剩余命题、目标公理和见证的全部参数。

### 范围大小与双重否定消除

给定官方原类型的 `Std.Rxc.size_pos_iff_le` 或 `Std.Rxo.size_pos_iff_lt`，都能推出任意命题的双重否定消除，继而推出排中律。令范围的端点都为 `Unit.unit`，把端点比较定义成待证命题 `p`，把大小定义成 1。在 `¬¬p` 下，假设比较失败就得到矛盾，因而满足比较失败时大小为零的类定律。对大小为正应用官方接口即可得到 `p`。清单生成器会从空内核重放这两条归约及双重否定消除推出排中律的证明。[Lean 归约](../InitInventory.lean) · [官方范围接口](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Data/Range/Polymorphic/Basic.lean#L78)

同一检查也重放两世界 Kripke 反模型 `TwoWorlds.countermodel`。原子命题只在后继世界成立。根世界强制它的双重否定，也同时见证该命题及其否定都未被根世界强制。这排除了直觉主义命题逻辑中的双重否定消除和排中律。Sato 与 Garrigue 的 §4.2.2 在其依赖类型演算 CCω 中给出排中律反模型。§5 的归纳类型扩展覆盖列表。要用该结果判定 Lean 4.35 零公理内核中的不可导性，仍需证明模型支持该内核的一般归纳族、消去及定义等价规则。两个范围接口因此继续列入未解决项。[Kripke 语义与可靠性](https://plato.stanford.edu/entries/logic-intuitionistic/#KripBethSemaForIntuLogi) · [Sato 与 Garrigue 的模型](https://doi.org/10.1017/S0960129523000087)
