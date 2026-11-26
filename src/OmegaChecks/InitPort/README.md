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

example (a : α) (b : β) : Eq (Prod.fst (Prod.mk a b)) a := Omega.rfl
```

位置参数接受一个或多个官方模块名。省略这些参数会扫描钉版工具链的所有 `Init` 模块，包括需要单独导入的模块。构建整个库可运行 `python3 src/OmegaChecks/InitPort/build.py .lake/init-port-all`。加上 `--seed PATH` 可选择另一个已编译的严格种子，默认读取 `.lake/build/omega-strict/lib/lean`。工具把种子的编译文件复制到独立临时目录，随后从钉版官方模块逐个翻译依赖、证明项、定义、归纳族和递归器。每个候选声明都在 Lean 内核中检查。环境变量 `OMEGA_PORT_HEARTBEATS` 为每个候选声明指定原始心跳预算，默认 5000。

`inventory.jsonl` 按顺序记下官方模块名、声明名、公开标记、移植结果和直接阻塞依赖。`added` 包含内核生成的构造子、递归器、私有及编译器内部声明。`existing` 表示复用种子中的声明。`interface-rejections.jsonl` 保存无法通过仓库官方对应检查的候选。公理、商原语、unsafe 或 partial 声明、未支持的表达式和依赖缺失均有逐项记录。

`lib/` 保存按官方定义模块组织的编译文件。程序对所选的基础库模块运行仓库的 `omegaAudit --exact-roots`，检查模块闭包、公开归属和可计算对应，逐声明检查公理并从空环境重放内核。全量构建还将 OmegaMath 和 OmegaMathlib 的下游源码编译到同一 `lib/`，验证普通 `import OmegaMath`，并审计其实际导入闭包。成功后输出目录才会出现。两次审计的读数分别保存在 `audit.txt` 和 `omegamath-audit.txt`。全量缺口表位于同一目录的 `init-gaps.tsv`。

这个独立制品用于内核类型检查、证明和定义归约。新生成声明的原生可执行代码、语法扩展、实例搜索和结构字段语法均不在移植覆盖范围内。

公开覆盖清单按官方定义模块和声明名逐项列出，重复生成的名字在各自模块有独立记录。
`init-inventory.json` 的 `summary` 按模块与名字的组合计数，`uniqueNames` 按名字去重。
全量构建也编译可单独导入的 OmegaMath 和 OmegaMathlib 源文件，一同审计它们的传递依赖。
缺口表的 `firstDependencyPath` 和 `reason` 记录本次移植实际遇到的阻塞。只有 `impliesAxiom` 非空的行另有内核证明，从该官方接口可推出所列公理。

`init-public-reductions.tsv` 列出已移植声明到严格库封装实现的一条最短定义体依赖路径。`officialReductionMechanism` 记录钉版 Lean 的官方机制，包括公开定义体、自然数内建运算、归纳类型、构造子和递归器。盘点 JSON 同时保存路径 `publicReductionBoundary` 与机制。`Nat.Coprime` 的路径通向内建运算 `Nat.gcd`。`And.rec` 和 `Iff.rec` 在官方环境中使用递归器计算规则。具体输入是否需要走到路径终点取决于归约过程。

例如，普通导入 `OmegaInit.Data.Nat.Div.Basic` 后可用 `Omega.Nat.div_zero` 证明除数为零的等式。若需直接归约严格实现，可 `import all OmegaInit.Prelude`，并在证明所在节设置 `attribute [local semireducible] Omega.Nat.div Omega.Nat.ble Omega.Nat.sub Omega.Nat.pred`。
