# Omega 数学模块的架构与验证

`OmegaInit` 提供严格基础，`OmegaMathlib` 提供与钉版 Mathlib 对应的公开接口，`OmegaMath` 公开六卷的项目数学。项目数学与外部核验库位于 `src/`，严格后端的基础实现位于 `strict/`。Lean 导入使用模块名，例如 `import OmegaMath`。根包使用钉版工具链和依赖锁文件。宿主审计与混合消费示例位于 `OmegaChecks`。[Lake 配置](../lakefile.toml)

普通 Lake 构建和下游导入使用钉版官方 Lean Init 与 Mathlib。作者照常运行 `lake build`。编译器自动记录模块声明，官方构建照常编译带标记的模块及其下游；严格准入读取该记录并跳过这些模块。运行 `lake build +OmegaMath` 即可编译项目数学。Lake 从 `src/OmegaInit` 和 `src/OmegaMathlib` 读取与共享源码配套的官方名称别名。准入时，构建驱动在独立的工件目录中改用 `strict/OmegaInit` 和 `strict/OmegaMathlib`，以同一份项目数学源码做严格核验。[Lake 配置](../lakefile.toml) · [严格构建](OmegaChecks/strict_lake.py)

## 选择编译后端

`OmegaMathlib` 是钉版 Mathlib 已移植并核对过的严格子集。有共同接口时，消费模块写一份证明，在官方和严格后端编译。下面的等式使用 `OmegaMath` 的自然数乘法定理。

```lean
prelude
import OmegaMath.Data.Nat

example (a k : Omega.Nat) : Omega.Eq ((a.mul k).mul (a.mul k)) ((a.mul a).mul (k.mul k)) :=
  Omega.Nat.square_mul a k
```

需要完整的官方接口时，导入 `OmegaBuild.Commands`，在所有 import 之后、数学声明之前写一次 `compile_only_with_mathlib`。该模块可以直接组合 Mathlib 的类型、定理、实例、记号和 tactics 与官方端的 OmegaMath 结果。这里的 `Omega.Nat` 在官方端就是 `Nat`，可以直接传给 Mathlib 的阶乘。

```lean
import OmegaBuild.Commands
import OmegaMath.Data.Nat
import Mathlib.Data.Nat.Factorial.Basic

compile_only_with_mathlib

example (n : Omega.Nat) : Nat := Nat.factorial n
```

任何直接或间接导入阶乘模块的消费者都只走官方后端。它们无需重复标记，共同上游和独立分支仍然双编。移除模块或其依赖上的最后一个标记后，严格端会再次编译这份源码。官方端的编译错误始终失败。对同时支持两端的模块，严格端的编译或导出对照失败也会报告。

本仓定向核验使用 `python3 src/OmegaChecks/portable.py --backend both <消费模块名>`。结果列出只在官方端编译的模块，并给出到显式标记的 import 链。CI 按相同规则选择严格目标。下游 Lake 包中的两个例子由[集成测试](OmegaChecks/test_backend_plan.py)编译。

## 六卷与模块树

| 卷 | 内容 | 定义与定理的入口 |
| --- | --- | --- |
| I | 逻辑、自然数、整数与精确比值 | `OmegaInit`、`OmegaMath.Data.{Nat,Ratio,Int,IntRatio}` |
| II | 射影坐标、带符号的有理单位圆、Cayley 参数与旋转合成 | `OmegaMath.Projective`、`OmegaMath.Projective.Circle` |
| III | 整数四元数、射影三元数堆、PythSpinor 与三维 Cayley 旋转 | `OmegaMath.Algebra.Quaternion`、`OmegaMath.Ternion.Heap`、`OmegaMath.Geometry.Cayley3D` |
| IV | 二阶与有限阶 jet、单纯上边界与正合性 | `OmegaMath.Calculus.{Jet2,DFiniteJet}`、`OmegaMath.Topology.SimplicialCoboundary` |
| V | 二次扩张、Lagrange–Gram 与 Schur 恒等式、Bargmann 行列式、Haar 矩与 Chebyshev–Hecke 算子 | `OmegaMath.Algebra.QuadraticExt`、`OmegaMath.Matrix.LagrangeSchur`、`OmegaMath.Geometry.BargmannGram`、`OmegaMath.Harmonic.{ChebyshevHecke,PiFreeHaar}` |
| VI | 欧几里得算法、连分数、深度预算、整数矩阵、Hurwitz 分裂与 FRACTRAN | `OmegaMath.Arithmetic.{Euclidean,ContinuedFraction,DepthBudget}`、`OmegaMath.Matrix.Mat2`、`OmegaMath.Matrix.Mat2.Hurwitz`、`OmegaMath.Computability.{Fractran,QuaternionFractran}` |

下列树以模块名表示源文件。带子项的节点也可以是模块，例如 `OmegaMath.Projective` 和 `OmegaMath.Algebra.QuadraticExt.Polynomial`。同层模块用逗号列出。

```text
OmegaInit
├── Prelude, Core
└── Data
    ├── Nat
    │   └── Basic, Lemmas
    └── Int
        └── Basic, Lemmas, Order
OmegaMath
├── Algebra
│   ├── QuadraticExt
│   │   ├── Basic, Fibonacci, Operations, Ring, SpecialValues, Spinor
│   │   └── Polynomial
│   │       └── Monomials
│   └── Quaternion
│       └── Polynomial, Shell
├── Arithmetic
│   ├── ContinuedFraction
│   │   └── Convergents, Tangent
│   ├── DepthBudget
│   └── Euclidean
│       └── Division, GCD, Prime
├── Calculus
│   ├── DFiniteCompose
│   ├── DFiniteJet
│   │   └── Basic, Cayley, Coefficients, Identities
│   ├── Jet2
│   │   └── Basic, Fidelity, Operations, Scalar, Secant
│   └── MidpointDrift
├── Computability
│   ├── Fractran
│   │   └── Division
│   └── QuaternionFractran
├── Data
│   └── Int, IntRatio, Nat, Ratio
├── Geometry
│   ├── BargmannGram
│   │   └── Coordinates, Determinant, Fractions, Identities, Monomial, Polynomial, Scaling
│   ├── Cayley3D
│   │   └── Adjoint, Matrix, Recurrence
│   └── DualChartCayley, LieTriple, SphericalLaws
├── Harmonic
│   ├── AllDegreeHaar
│   │   └── Characters, Coefficients, Integration, MomentTable
│   ├── ChebyshevHecke
│   │   └── Character, Orbitals, Recurrence, S5, SpinShells, Traces
│   ├── HurwitzFreeGroup
│   │   └── Adjoint, ReducedDifference, Residue, Split5
│   └── PiFreeHaar
│       └── Hecke, Moments
├── Matrix
│   ├── LagrangeSchur
│   │   └── Diagonal, Gram, Order, Schur, Sequence, Vector
│   └── Mat2
│       └── Hurwitz
├── Projective
│   ├── Basic
│   └── Circle
│       └── Identity
├── Ternion
│   └── Heap
│       └── Core, Fidelity, Spinor
├── Topology
│   └── SimplicialCoboundary
└── Witnesses
    └── FlagshipWitnesses
```

## 导入与来源

严格模块使用 `module` 和 `prelude`，后者关闭隐式官方 `Init` 导入。可直接导入总入口，也可只导入所需专题。带符号的齐次坐标位于 `OmegaMath.Projective.Circle`。有限 `IntRatio` 用正分母的前驱存储分母，以交叉相乘定义等价，并将未定义值传递到运算结果。加法逆元律适用于有限分数，乘法逆元律还要求分子非零。[有理单位圆](OmegaMath/Projective/Circle.lean) · [精确比值](OmegaMath/Data/IntRatio.lean)

对于整数齐次坐标 `[P:Q]`，第 39 章的重叠度是 `Q²/(P²+Q²)`。两坐标均为零时读数未定义。比如 `[1:1]` 和 `[2:2]` 的读数都等价于 1/2。

- 计算读数时，导入 `OmegaMath.Projective.Basic`。这个模块定义 `Omega.Projective.kappa`，输入是坐标的绝对值。[定义](OmegaMath/Projective/Basic.lean) · [边界算例](OmegaChecks/Examples.lean)
- 证明同比例放大坐标保持读数时，导入 `OmegaMath.Projective`。严格文件用 `prelude` 关闭隐式官方 Init 导入，`open Omega` 后可直接写 `Nat` 和 `Ratio`。[缩放定理](OmegaMath/Projective.lean) · [对角坐标的消费示例](OmegaChecks/ProjectiveOverlap.lean)
- 混用两套数学时，可写 `open Omega renaming Nat → OmegaNat`，官方类型仍写 `Nat`。混合示例显式引入 Mathlib，审计程序则使用官方 Lean API。零公理承诺覆盖下文的严格入口及其传递依赖。[混用示例](OmegaChecks/Mixed.lean)

## 官方 Lean 的模块与名称

`OmegaInit` 对照本仓钉版 Lean 的 `Init`。模块名前缀从 `Init` 换成 `OmegaInit`，公开声明在官方完整名字前加 `Omega.`。Lake 从 `src/` 解析模块路径。类型和运算按它们在官方编译产物中的声明位置组织。

| 官方模块 | 官方声明 | 本仓源文件 | 本仓声明 |
| --- | --- | --- | --- |
| `Init.Prelude` | `Nat`、`Nat.add` | [Prelude.lean](../strict/OmegaInit/Prelude.lean) | `Omega.Nat`、`Omega.Nat.add` |
| `Init.Core` | `Nat.add_zero` | [Core.lean](../strict/OmegaInit/Core.lean) | `Omega.Nat.add_zero` |
| `Init.Data.Nat.Basic` | `Nat.add_comm` | [Basic.lean](../strict/OmegaInit/Data/Nat/Basic.lean) | `Omega.Nat.add_comm` |
| `Init.Data.Nat.Lemmas` | `Nat.mul_right_comm` | [Lemmas.lean](../strict/OmegaInit/Data/Nat/Lemmas.lean) | `Omega.Nat.mul_right_comm` |
| `Init.Data.Int.Basic` | `Int`、`Int.mul` | [Basic.lean](../strict/OmegaInit/Data/Int/Basic.lean) | `Omega.Int`、`Omega.Int.mul` |
| `Init.Data.Int.Lemmas` | `Int.add_assoc`、`Int.mul_eq_zero` | [Lemmas.lean](../strict/OmegaInit/Data/Int/Lemmas.lean) | `Omega.Int.add_assoc`、`Omega.Int.mul_eq_zero` |
| `Init.Data.Int.Order` | `Int.natAbs_mul` | [Order.lean](../strict/OmegaInit/Data/Int/Order.lean) | `Omega.Int.natAbs_mul` |

```lean
prelude
import OmegaInit.Data.Nat.Basic
open Omega

example (a b : Nat) : Eq (Nat.add a b) (Nat.add b a) := Nat.add_comm a b
```

审计器在单独的 Lean 环境中读取钉版工具链的官方编译产物，逐条核对公开声明的完整名字与定义模块。这一检查覆盖名称与归属。严格实现的传递公理由空内核重放另行核验。Omega 特有的精确比值及专题辅助引理归入 `OmegaMath`。[审计实现](OmegaChecks/Audit.lean) · [官方 Nat 基础定理](https://github.com/leanprover/lean4/blob/v4.35.0/src/lean/Init/Data/Nat/Basic.lean#L158)

### 查看移植覆盖和缺口

下面的命令核验当前严格基础库，并扫描钉版工具链中可独立导入的每个 `Init` 模块。JSON 包含每个公开声明的官方名称、所属模块、声明种类、官方实现的传递公理和严格端的对应模块。TSV 逐行列出尚无同名同模块对应项的非公理声明。[清单生成器](OmegaChecks/InitInventory.lean)

```sh
lake test -- OmegaInit
mkdir -p .lake/build/omega-checks
lean --run src/OmegaChecks/InitInventory.lean .lake/build/omega-strict/lib/lean \
  .lake/build/omega-checks/init-inventory.json .lake/build/omega-checks/init-gaps.tsv
```

表中的 `impliesAxiom` 记录已验证的归约。例如，给定原类型的 `Classical.choose` 实现，就能构造 `Classical.choice`。空值表示尚未登记此类归约。`upstreamAxioms` 记录官方实现使用的公理。同一类型有构造性证明时，严格库仍可收录。语法、别名和私有实现不计入公开声明数。[`Classical.choose` 的官方定义](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Classical.lean)

严格构建为 `Option`、`List` 和 `Sum` 读取钉版的归纳声明，并生成构造器布局。Lean 编译器和官方环境只在构建时使用。生成的严格模块可以独立导入，审计会检查其全部依赖并在空内核重放声明。[严格构建配置](OmegaChecks/strict_lake.py) · [归纳声明移植](OmegaChecks/InitCompiler.lean)

### 批量构建官方 Init 对象

从已编译的严格源码库出发，全量构建会遍历工具链中所有已安装的 `Init` 模块，按官方归属创建编译模块，并用生成的基础库重新编译项目的 `OmegaMath` 源码。基础库和下游均通过接口检查与内核重放后，生成器才发布输出目录。请选择尚未占用的输出路径。[生成器](OmegaChecks/InitPort/build.py) · [OmegaMath 下游构建](OmegaChecks/InitPort/omegamath.py)

```sh
lake test -- OmegaInit
python3 src/OmegaChecks/InitPort/build.py .lake/init-port-all
LEAN_PATH=.lake/init-port-all/lib lean Example.lean
```

`Example.lean` 可以通过公开入口使用生成对象。

```lean
module
prelude
import OmegaMath
import OmegaInit.Data.List.Basic

#check Omega.Nat.fib
#check Omega.Nat.div
#check Omega.List.length
#check Omega.List.reverse
```

输出目录中的 `init-gaps.tsv` 按官方模块和名称列出剩余非公理声明、此次尝试遇到的依赖和原因。`init-inventory.json` 列出全部公开声明。`audit.txt` 和 `omegamath-audit.txt` 分别保存基础库与 OmegaMath 导入闭包的内核审计。`init-public-reductions.tsv` 逐项列出普通导入时，到严格库封装实现的定义体依赖路径，以及该接口在官方环境中的计算机制。例如，公开导入 `OmegaInit.Data.Nat.Div.Basic` 后可应用 `Omega.Nat.div_zero`。直接展开严格除法实现的用法见 [生成说明](OmegaChecks/InitPort/README.md)。批量生成器只复制源码库已有的原生编译数据。可单独导入的官方模块保留对应的 `OmegaInit.*` 模块路径。

## 严格库与可替换接口

`OmegaInit` 可以导入本层模块。`OmegaMathlib` 可以导入本层与 `OmegaInit`。`OmegaMath` 可以导入三个严格库。审计器从编译产物读取每条导入边，并在空内核中重放选定的严格闭包。官方 Init 与 Mathlib 由外部核验器分别加载。[严格闭包审计](OmegaChecks/Audit.lean)

`OmegaMathlib` 按上游模块路径组织，例如 `OmegaMathlib.Data.Nat.Fib.Basic` 对应 `Mathlib.Data.Nat.Fib.Basic`。每个公开移植声明都须指向钉版上游的同名声明，核对声明所属模块、类型、公开参数和运算含义。使用另一种算法实现函数时，需要一个针对实际函数体、对全部输入成立的对应证明，并限定公开接口可观察的计算规则。项目自有接口位于 `OmegaMath`。例如群减法模块显式接收运算和群公理，保留在项目数学层。[声明检查](OmegaChecks/Interface.lean) · [群接口](OmegaMath/Algebra/Group/Basic.lean)

`OmegaChecks.NatCorrespondence` 证明严格自然数与标准自然数之间的双向转换、加法保持、序关系双向等价，以及 Fibonacci 数和二项式系数对任意输入的逐点一致。[自然数对应](OmegaChecks/NatCorrespondence.lean)

Zeckendorf 核验将零基权位 `i` 映射为 Fibonacci 下标 `i + 2`。Lean 证明两个规范性谓词等价、解码值一致、每个输入的编码等于 Mathlib 的 `Nat.zeckendorf`，并且每个 Mathlib 规范表示都可由严格编码表示。`lake test -- OmegaChecks.WDigitCorrespondence` 可单独运行。[对应证明](OmegaChecks/WDigitCorrespondence.lean)

## 下游核验

在仓库根目录执行以下命令。第一个入口检查三个严格库的联合闭包。第二个入口执行完整审计及拒绝用例。CI 根据候选变更和导入图选取受影响的库、见证模块和下游消费者，用同一范围恢复模块缓存、构建适用的环境并比较导出。共享的工具链、构建配置和核验逻辑变更触发完整审计。 CI 可从已成功的受保护 push 恢复相同输入的严格内核重放、共同接口比较和官方接口比较结果。命中官方接口时同时恢复对应的公理报告。日志中的 `Omega audit miss`、`recorded` 和 `hit` 分别表示执行新检查、保存通过结果和复用结果。[审计入口](OmegaChecks/check.py) · [双环境编译](OmegaChecks/portable.py)

```sh
lake test -- OmegaInit OmegaMathlib OmegaMath
python3 src/OmegaChecks/check.py --full
```

完整双编把官方侧公开声明、所属模块及传递公理依赖写入 `.lake/build/omega-checks/official-axioms.json`，局部双编写入同目录的 `selected-official-axioms.json`。CI 将本次比较生成的报告作为 `omega-official-axioms` 上传。

完整双端检查也沿导入图选取独立 `Reg` 包中依赖 Omega 的模块。先用 `make install-tools` 安装钉版检查器接口。官方端使用主库及检查器接口编译入选模块，严格端编译其中支持双端的子集。普通数学发布从主包构建。

移植者新增严格基础模块或修改其公开接口后，在仓库根目录运行以下命令。它编译 `strict/` 下的移植，从实际导入图和编译后的公开名称生成 `src/OmegaInit`、`src/OmegaMathlib` 及其根模块的官方别名文件。将生成文件和严格源码一同提交，双端准入检查会按相同规则核对内容。

```sh
python3 src/OmegaChecks/portable.py --regenerate-facades
```

下游源码只写一次接口名。例如 `import OmegaMathlib.Data.Nat.Fib.Basic` 在官方环境中加载 `Mathlib.Data.Nat.Fib.Basic`，`Omega.Nat.fib` 由编译后的公开名自动解析到 `Nat.fib`。普通构建读取已入库的官方别名文件，每个环境各有自己的编译产物。对于使用全输入等价证明的不同算法，普通导入只能依赖已核对的公开方程。显式展开实现或局部改写透明性的源码需要在两个后端分别验证。用以下命令可以在本地选择某个环境，或运行双编译和导出核对。

支持双端的消费者使用原始官方环境和严格环境分别编译。准入还为严格端口的共同公开计算规则生成一份独立的官方构建配置，在其中限制已封装实现的展开，并编译仓内的共同接口用例。以 Fibonacci 为例，普通官方发布允许用 `rfl` 计算 `fib 0`，严格环境和共同接口用例可用公开定理 `fib_zero`。下列双端核验命令同时准备这份配置。随后可用 `lake -f .lake/omega-common.toml env lean <文件>` 检查其他消费者是否只用到了共同计算规则。
```sh
python3 src/OmegaChecks/portable.py --backend strict OmegaChecks.Portable.Common
python3 src/OmegaChecks/portable.py --backend mathlib OmegaChecks.Portable.Common
python3 src/OmegaChecks/portable.py --backend both OmegaChecks.Portable.Common
```
