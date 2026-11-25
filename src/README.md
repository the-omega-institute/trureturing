# Omega 数学模块的架构与验证

D5 按专题存放并冻结项目自己的数学对象和定理。标准对象由 `OmegaMathlib` 提供，Lean 基础对象由 `OmegaInit` 提供。普通 Lake 构建使用钉版官方 Init 和 Mathlib，准入还会用严格端口编译同一份项目源码。[Lake 配置](../lakefile.toml) · [严格构建](OmegaChecks/strict_lake.py)

例如，导入 `OmegaMathlib.Data.Nat.Prime.Defs` 后，陈述中的 `OmegaMathlib.Nat.Prime p` 指向官方 `Nat.Prime p`，严格端则使用已核验的端口。两个命名空间中的引用由编译产物生成。项目自己的谓词可以作为 D5 定义冻结；来源审计会区分其实际声明与标准对象。[标准端口](../strict/OmegaMathlib/Data/Nat/Prime/Defs.lean) · [D5 素因子定理](../D5/S3/Arith/Euclidean/Prime.lean)

## 六卷的数学入口

| 卷 | 主题 | 实际定义与证明 |
| --- | --- | --- |
| I | 逻辑、自然数、整数与精确比值 | [严格基础](../strict/OmegaInit) · [精确算术](../D5/S0/Arithmetic/Exact) |
| II | 射影坐标、带符号有理单位圆、Cayley 参数 | [射影坐标](../D5/S3/Geometry/ProjectiveCoordinates) |
| III | 整数四元数、三元数堆与三维旋转 | [四元数](../D5/S0/Algebra/Quaternion.lean) · [三元数](../D5/S3/Geometry/Ternion) · [Cayley 旋转](../D5/S3/Geometry/Cayley3D) |
| IV | 微分 jet 与单纯上边界 | [微积分](../D5/S3/Calculus) · [上边界](../D5/S0/FiniteGeometry/Simplicial/Coboundary.lean) |
| V | 二次扩张、Schur 恒等式、Bargmann 行列式、Haar 矩 | [二次扩张](../D5/S0/Carrier/QuadraticExtension) · [矩阵](../D5/S3/Geometry/Matrices) · [Bargmann](../D5/S3/Geometry/BargmannGram) · [Fourier](../D5/S3/Fourier) |
| VI | 欧几里得算法、连分数、深度预算和 FRACTRAN | [欧几里得算法](../D5/S3/Arith/Euclidean) · [连分数](../D5/S3/Arith/ContinuedFractions) · [深度](../D5/S1/Depth/ArithmeticBudget.lean) · [FRACTRAN](../D5/S0/Computability/FractionPrograms) |

## 导入与来源

严格模块使用 `module` 和 `prelude`，后者关闭隐式官方 `Init` 导入。D5 直接导入所需专题。带符号的齐次坐标位于 `D5.S3.Geometry.ProjectiveCoordinates.Circle`。有限 `IntRatio` 用正分母的前驱存储分母，以交叉相乘定义等价，并将未定义值传递到运算结果。加法逆元律适用于有限分数，乘法逆元律还要求分子非零。[有理单位圆](../D5/S3/Geometry/ProjectiveCoordinates/Circle.lean) · [精确比值](../D5/S0/Arithmetic/Exact/IntRatio.lean)

对于整数齐次坐标 `[P:Q]`，第 39 章的重叠度是 `Q²/(P²+Q²)`。两坐标均为零时读数未定义。比如 `[1:1]` 和 `[2:2]` 的读数都等价于 1/2。

- 计算读数时，导入 `D5.S3.Geometry.ProjectiveCoordinates.Basic`。这个模块定义 `Omega.Projective.kappa`，输入是坐标的绝对值。[定义](../D5/S3/Geometry/ProjectiveCoordinates/Basic.lean) · [边界算例](OmegaChecks/Examples.lean)
- 证明同比例放大坐标保持读数时，导入 `D5.S3.Geometry.ProjectiveCoordinates.Scaling`。严格文件用 `prelude` 关闭隐式官方 Init 导入，`open Omega` 后可直接写 `Nat` 和 `Ratio`。[缩放定理](../D5/S3/Geometry/ProjectiveCoordinates/Scaling.lean) · [对角坐标的消费示例](OmegaChecks/ProjectiveOverlap.lean)
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

审计器在单独的 Lean 环境中读取钉版工具链的官方编译产物，逐条核对公开声明的完整名字与定义模块。这一检查覆盖名称与归属。严格实现的传递公理由空内核重放另行核验。Omega 特有的精确比值及专题辅助引理归入相应 D5 专题。[审计实现](OmegaChecks/Audit.lean) · [官方 Nat 基础定理](https://github.com/leanprover/lean4/blob/v4.35.0/src/lean/Init/Data/Nat/Basic.lean#L158)

## 严格库与可替换接口

`OmegaInit` 可以导入本层模块。`OmegaMathlib` 可以导入本层与 `OmegaInit`。D5 数学可导入这些端口及相应地层的 D5 模块。审计器从编译产物读取每条导入边，并在空内核中重放选定的严格闭包。官方 Init 与 Mathlib 由外部核验器分别加载。[严格闭包审计](OmegaChecks/Audit.lean)

`OmegaMathlib` 按上游模块路径组织，例如 `OmegaMathlib.Data.Nat.Fib.Basic` 对应 `Mathlib.Data.Nat.Fib.Basic`。每个公开移植声明都须指向钉版上游的同名声明，核对声明所属模块、类型、公开参数和运算含义。使用另一种算法实现函数时，需要一个针对实际函数体、对全部输入成立的对应证明，并限定公开接口可观察的计算规则。项目自有接口位于 D5。例如 D5 的群减法模块显式接收运算和群公理。[声明检查](OmegaChecks/Interface.lean) · [群接口](../D5/S0/Algebra/Groups/Basic.lean)

`OmegaChecks.NatCorrespondence` 证明严格自然数与标准自然数之间的双向转换、加法保持、序关系双向等价，以及 Fibonacci 数和二项式系数对任意输入的逐点一致。[自然数对应](OmegaChecks/NatCorrespondence.lean)

Zeckendorf 核验将零基权位 `i` 映射为 Fibonacci 下标 `i + 2`。Lean 证明两个规范性谓词等价、解码值一致、每个输入的编码等于 Mathlib 的 `Nat.zeckendorf`，并且每个 Mathlib 规范表示都可由严格编码表示。`lake test -- OmegaChecks.WDigitCorrespondence` 可单独运行。[对应证明](OmegaChecks/WDigitCorrespondence.lean)

## 下游核验

在仓库根目录执行以下命令。第一个入口检查两个严格基础库的联合闭包。第二个入口执行完整审计及拒绝用例。CI 根据候选变更和导入图选取受影响的库、见证模块和下游消费者，用同一范围恢复模块缓存、构建适用的环境并比较导出。共享的工具链、构建配置和核验逻辑变更触发完整审计。[审计入口](OmegaChecks/check.py) · [双环境编译](OmegaChecks/portable.py)

```sh
lake test -- OmegaInit OmegaMathlib
python3 src/OmegaChecks/check.py --full
```

完整双编把官方侧公开声明、所属模块及传递公理依赖写入 `.lake/build/omega-checks/official-axioms.json`，局部双编写入同目录的 `selected-official-axioms.json`。CI 将本次比较生成的报告作为 `omega-official-axioms` 上传。

完整双端检查也沿导入图选取独立 `Reg` 包中依赖 Omega 的模块。先用 `make install-tools` 安装钉版检查器接口。两端各用对应的主库及检查器接口编译这些模块，普通数学发布仍从主包构建。

移植者新增严格基础模块或修改其公开接口后，在仓库根目录运行以下命令。它编译 `strict/` 下的移植，从实际导入图和编译后的公开名称生成 `src/OmegaInit`、`src/OmegaMathlib` 及其根模块的官方别名文件。将生成文件和严格源码一同提交，双端准入检查会按相同规则核对内容。

```sh
python3 src/OmegaChecks/portable.py --regenerate-facades
```

下游源码只写一次接口名。例如 `import OmegaMathlib.Data.Nat.Fib.Basic` 在官方环境中加载 `Mathlib.Data.Nat.Fib.Basic`，`OmegaMathlib.Nat.fib` 由编译后的公开名自动解析到 `Nat.fib`。普通构建读取已入库的官方别名文件，每个环境各有自己的编译产物。对于使用全输入等价证明的不同算法，普通导入只能依赖已核对的公开方程。显式展开实现或局部改写透明性的源码需要在两个后端分别验证。用以下命令可以在本地选择某个环境，或运行双编译和导出核对。


所有入选消费者均以原始官方环境和严格环境编译。准入还为严格端口的共同公开计算规则生成一份独立的官方构建配置，在其中限制已封装实现的展开，并编译仓内的共同接口用例。以 Fibonacci 为例，普通官方发布允许用 `rfl` 计算 `fib 0`，严格环境和共同接口用例可用公开定理 `fib_zero`。下列双端核验命令同时准备这份配置。随后可用 `lake -f .lake/omega-common.toml env lean <文件>` 检查其他消费者是否只用到了共同计算规则。
```sh
python3 src/OmegaChecks/portable.py --backend strict OmegaChecks.Portable.Common
python3 src/OmegaChecks/portable.py --backend mathlib OmegaChecks.Portable.Common
python3 src/OmegaChecks/portable.py --backend both OmegaChecks.Portable.Common
```
