# Omega 数学模块的架构与验证

`OmegaInit` 提供严格基础，`OmegaMath` 公开六卷的数学模块。根目录的 Lake 配置以 `srcDir = "src"` 登记这两个库和 `OmegaChecks`。Lean 导入使用模块名，例如 `import OmegaMath`。根包使用钉版工具链和依赖锁文件。宿主审计与混合消费示例位于 `OmegaChecks`，D5 引用位于根目录的 `D5/`。[Lake 配置](../lakefile.toml)

## 六卷与模块树

| 卷 | 内容 | 定义与定理的入口 |
| --- | --- | --- |
| I | 逻辑、自然数、整数与精确比值 | `OmegaInit`、`OmegaMath.Data.{Nat,Ratio,Int,IntRatio}` |
| II | 射影坐标、带符号的有理单位圆、Cayley 参数与旋转合成 | `OmegaMath.Projective`、`OmegaMath.Projective.Circle` |
| III | 整数四元数、射影三元数堆、PythSpinor 与三维 Cayley 旋转 | `OmegaMath.Algebra.Quaternion`、`OmegaMath.Ternion.Heap`、`OmegaMath.Geometry.Cayley3D` |
| IV | 二阶与有限阶 jet、单纯上边界与正合性 | `OmegaMath.Calculus.{Jet2,DFiniteJet}`、`OmegaMath.Topology.SimplicialCoboundary` |
| V | 二次扩张、Lagrange–Gram 与 Schur 恒等式、Bargmann 行列式、Haar 矩与 Chebyshev–Hecke 算子 | `OmegaMath.Algebra.QuadraticExt`、`OmegaMath.Matrix.LagrangeSchur`、`OmegaMath.Geometry.BargmannGram`、`OmegaMath.Harmonic.{ChebyshevHecke,PiFreeHaar}` |
| VI | 欧几里得算法、连分数、深度预算、整数矩阵、Hurwitz 分裂、FRACTRAN 与标准实数桥接 | `OmegaMath.Arithmetic.{Euclidean,ContinuedFraction,DepthBudget}`、`OmegaMath.Matrix.Mat2`、`OmegaMath.Matrix.Mat2.Hurwitz`、`OmegaMath.Computability.{Fractran,QuaternionFractran}` 与 D5 的 `OmegaShadowBridge` |

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
│       └── Polynomial
├── Arithmetic
│   ├── ContinuedFraction
│   │   └── Convergents, Tangent
│   ├── DepthBudget
│   └── Euclidean
│       └── Division, GCD, Prime
├── Calculus
│   ├── DFiniteJet
│   │   └── Basic, Cayley, Coefficients, Identities
│   └── Jet2
│       └── Basic, Fidelity, Operations, Scalar, Secant
├── Computability
│   ├── Fractran
│   │   └── Division
│   └── QuaternionFractran
├── Data
│   └── Int, IntRatio, Nat, Ratio
├── Geometry
│   ├── BargmannGram
│   │   └── Coordinates, Determinant, Fractions, Identities, Monomial, Polynomial, Scaling
│   └── Cayley3D
│       └── Adjoint, Matrix, Recurrence
├── Harmonic
│   ├── ChebyshevHecke
│   │   └── Character, Orbitals, Recurrence, S5, SpinShells, Traces
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
└── Topology
    └── SimplicialCoboundary
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
| `Init.Prelude` | `Nat`、`Nat.add` | [Prelude.lean](OmegaInit/Prelude.lean) | `Omega.Nat`、`Omega.Nat.add` |
| `Init.Core` | `Nat.add_zero` | [Core.lean](OmegaInit/Core.lean) | `Omega.Nat.add_zero` |
| `Init.Data.Nat.Basic` | `Nat.add_comm` | [Basic.lean](OmegaInit/Data/Nat/Basic.lean) | `Omega.Nat.add_comm` |
| `Init.Data.Nat.Lemmas` | `Nat.mul_right_comm` | [Lemmas.lean](OmegaInit/Data/Nat/Lemmas.lean) | `Omega.Nat.mul_right_comm` |
| `Init.Data.Int.Basic` | `Int`、`Int.mul` | [Basic.lean](OmegaInit/Data/Int/Basic.lean) | `Omega.Int`、`Omega.Int.mul` |
| `Init.Data.Int.Lemmas` | `Int.add_assoc`、`Int.mul_eq_zero` | [Lemmas.lean](OmegaInit/Data/Int/Lemmas.lean) | `Omega.Int.add_assoc`、`Omega.Int.mul_eq_zero` |
| `Init.Data.Int.Order` | `Int.natAbs_mul` | [Order.lean](OmegaInit/Data/Int/Order.lean) | `Omega.Int.natAbs_mul` |

```lean
prelude
import OmegaInit.Data.Nat.Basic
open Omega

example (a b : Nat) : Eq (Nat.add a b) (Nat.add b a) := Nat.add_comm a b
```

审计器在单独的 Lean 环境中读取钉版工具链的官方编译产物，逐条核对公开声明的完整名字与定义模块。这一检查覆盖名称与归属。严格实现的传递公理由空内核重放另行核验。Omega 特有的精确比值及专题辅助引理归入 `OmegaMath`。[审计实现](OmegaChecks/Audit.lean) · [官方 Nat 基础定理](https://github.com/leanprover/lean4/blob/v4.35.0/src/lean/Init/Data/Nat/Basic.lean#L158)

## OmegaMath 的专题与来源

可独立使用的定义和定理放在 `OmegaMath` 对应专题下。只为一个 D5 证明服务的辅助结果可与该证明放在一起。来源标记以文件为单位。审计器在独立的上游环境中核对移植声明的名字和定义模块，严格闭包另经空内核重放。[审计实现](OmegaChecks/Audit.lean)

| 来源 | 模块位置 | 公开名称与来源标注 |
| --- | --- | --- |
| 从钉版 Mathlib 移植 | 保留上游定义所在模块的路径，把 `Mathlib` 换成 `OmegaMath` | 在上游声明的完整名字前加 `Omega.` |
| Omega 原创形式化 | 放在相关专题附近，可与移植模块同目录 | 在 `Omega` 命名空间中取名，模块文档第一行写 `Omega original.`，随后说明用途 |

## D5 冻结引用

十个零公理 D5 模块公开供书稿引用的结论。

| 卷 | 冻结模块 |
| --- | --- |
| II | [OmegaCircleClosure](../D5/S3/Quantum/AURICOmega/OmegaCircleClosure.lean) |
| III | [OmegaTernionHeap](../D5/S3/Quantum/AURICOmega/OmegaTernionHeap.lean) · [OmegaCayleyRotation](../D5/S3/Quantum/AURICOmega/OmegaCayleyRotation.lean) |
| IV | [OmegaJetCalculus](../D5/S3/Quantum/AURICOmega/OmegaJetCalculus.lean) · [OmegaSimplicialExactness](../D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness.lean) |
| V | [OmegaQuadraticAndSchur](../D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.lean) · [OmegaChebyshevHecke](../D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke.lean) · [OmegaBargmannHaarHecke](../D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.lean) |
| VI | [OmegaArithmeticHorizon](../D5/S3/Quantum/AURICOmega/OmegaArithmeticHorizon.lean) · [OmegaMatrixAndFractran](../D5/S3/Quantum/AURICOmega/OmegaMatrixAndFractran.lean) |

第 11 个冻结模块是 Layer 2 的 `OmegaShadowBridge`。它将精确算术和射影圆结论映到标准自然数、整数、有理数和实数。它导入 Mathlib，冻结记录包含 `propext` 和 `Quot.sound`，位于严格库闭包之外。[桥接源码](../D5/S3/Quantum/AURICOmega/OmegaShadowBridge.lean) · [冻结记录](../Golden/Frozen/state/D5/S3/Quantum/AURICOmega/OmegaShadowBridge.lean.json)

## 空内核审计

| 审计入口 | 传递闭包的模块数 | 声明数 |
| --- | ---: | ---: |
| `OmegaInit` | 10 | 163 |
| `OmegaMath` | 87 | 2,211 |
| `OmegaInit` 与 `OmegaMath` 合并去重 | 88 | 2,211 |

计数取自钉版 Lean 工具链的编译产物，包含总入口、传递依赖和重放的所有声明。`OmegaMath` 的 87 个模块包括 78 个 OmegaMath 模块和 9 个 OmegaInit 依赖模块。审计确认各闭包的公理、`Quot` 声明、不安全声明、官方 `Init` 模块和 Mathlib 模块的数量均为零。它逐条检查编译声明及其公理依赖，再在空内核环境中重放。上游名字匹配使用独立环境。[审计实现](OmegaChecks/Audit.lean)

在仓库根目录运行以下命令。Lake 驱动构建并重放两个入口的联合闭包。Python 脚本按源文件清单核对两个入口的传递闭包，并检查旧消费入口和拒绝用例。[复现脚本](OmegaChecks/check.py)

```sh
lake test -- OmegaInit OmegaMath
python3 src/OmegaChecks/check.py
```

主仓 CI 将受影响的严格模块传给同一个 Lake 驱动。驱动核验所选模块及其传递依赖。仅变更审计器时，驱动以 `OmegaInit.Prelude` 为回归入口。可用 `lake test -- OmegaMath.Projective` 核验单个专题。[Lake 配置](../lakefile.toml) · [驱动](OmegaChecks/Audit.lean)
