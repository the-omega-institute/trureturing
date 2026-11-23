# Omega 数学模块的架构与验证

本实验以 trureturing 的 `ff5118d67b7e`、官方 Lean 4.35.0 和 OmegaMath v0.1.2（`ab30975b2029`）为基线。仓库根目录的 `lakefile.toml` 用 `srcDir = "src"` 登记三个库目标，共用 trureturing 的工具链、Mathlib 依赖和锁文件。`OmegaInit` 可以由 Lake 单独构建。文件路径中的 `src/` 由 Lake 解析，Lean 导入仍然写模块名。

```text
trureturing/
  lakefile.toml
  D5/                           existing proofs
  src/
    OmegaInit.lean              strict foundation
    OmegaInit/
    OmegaMath.lean              public mathematics
    OmegaMath/Projective/Basic.lean  chapter 39 overlap
    OmegaMath/Projective.lean        scaling theorem
    OmegaChecks/                consumers, audit and experiment
```

## 依赖与入口

`OmegaInit`、`OmegaMath` 和 `OmegaChecks` 是同一 Lake 包中的三个库目标。前两个公开严格数学声明，第三个容纳消费示例和宿主审计程序。现有 D5 证明位于仓库根目录的 `D5/`，可以直接导入 `src/` 中的模块。定义与消费它的证明可以在同一提交中更新。日常源文件改动使用根包现有的依赖锁定。[Lake 配置](../lakefile.toml)

图中每个箭头表示左侧模块直接导入右侧模块。

```text
OmegaChecks.Mixed --> Mathlib.Data.Nat.Prime.Basic
                 +--> OmegaChecks.ProjectiveOverlap --> OmegaMath.Projective

OmegaMath --------------------------------------------> OmegaMath.Projective
OmegaMath.Projective ---------------------------------> OmegaMath.Projective.Basic
OmegaChecks.Examples ---------------------------------> OmegaMath.Projective.Basic
OmegaMath.Projective.Basic --> OmegaMath.Data.Ratio --> OmegaMath.Data.Nat
                                                             |
                                                             v
OmegaInit --> OmegaInit.Data.Nat --> OmegaInit.Data.Nat.Lemmas
                                              |
                                              v
                                    OmegaInit.Data.Nat.Basic
                                              |
                                              v
                                    OmegaInit.Core --> OmegaInit.Prelude

OmegaChecks.Audit --> Lean, Lean.Replay
```

对于整数齐次坐标 `[P:Q]`，第 39 章的重叠度是 `Q²/(P²+Q²)`。两坐标均为零时读数未定义。比如 `[1:1]` 和 `[2:2]` 的读数都等价于 1/2。

- 计算读数时，导入 `OmegaMath.Projective.Basic`。这个模块定义 `Omega.Projective.kappa`，输入是坐标的绝对值。[定义](OmegaMath/Projective/Basic.lean) · [边界算例](OmegaChecks/Examples.lean)
- 证明同比例放大坐标保持读数时，导入 `OmegaMath.Projective`。严格文件用 `prelude` 关闭隐式官方 Init 导入，`open Omega` 后可直接写 `Nat` 和 `Ratio`。[缩放定理](OmegaMath/Projective.lean) · [对角坐标的消费示例](OmegaChecks/ProjectiveOverlap.lean)
- 混用两套数学时，可写 `open Omega renaming Nat → OmegaNat`，官方类型仍写 `Nat`。混合示例显式引入 Mathlib，审计程序则使用官方 Lean API。零公理承诺覆盖下表的严格入口及其传递依赖。[混用示例](OmegaChecks/Mixed.lean)

## 官方 Lean 的模块与名称

`OmegaInit` 对照本仓钉版 Lean 的 `Init`。模块名前缀从 `Init` 换成 `OmegaInit`，公开声明在官方完整名字前加 `Omega.`。Lake 从 `src/` 解析模块路径。类型和运算按它们在官方编译产物中的声明位置组织。

| 官方模块 | 官方声明 | 本仓源文件 | 本仓声明 |
| --- | --- | --- | --- |
| `Init.Prelude` | `Nat`、`Nat.add` | [Prelude.lean](OmegaInit/Prelude.lean) | `Omega.Nat`、`Omega.Nat.add` |
| `Init.Core` | `Nat.add_zero` | [Core.lean](OmegaInit/Core.lean) | `Omega.Nat.add_zero` |
| `Init.Data.Nat.Basic` | `Nat.add_comm` | [Basic.lean](OmegaInit/Data/Nat/Basic.lean) | `Omega.Nat.add_comm` |
| `Init.Data.Nat.Lemmas` | `Nat.mul_right_comm` | [Lemmas.lean](OmegaInit/Data/Nat/Lemmas.lean) | `Omega.Nat.mul_right_comm` |

```lean
prelude
import OmegaInit.Data.Nat.Basic
open Omega

example (a b : Nat) : Eq (Nat.add a b) (Nat.add b a) := Nat.add_comm a b
```

审计器在单独的 Lean 环境中读取钉版工具链的官方编译产物，逐条核对公开声明的完整名字与定义模块。这一检查覆盖名称与归属。严格实现的传递公理由空内核重放另行核验。Omega 特有的精确比值及专题辅助引理归入 `OmegaMath`。[审计实现](OmegaChecks/Audit.lean) · [官方 Nat 基础定理](https://github.com/leanprover/lean4/blob/v4.35.0/src/lean/Init/Data/Nat/Basic.lean#L158)

## 主仓 CI

`OmegaInit` 和 `OmegaMath` 是 trureturing 的内部库。主仓的 `current` 检查从改动的 Lean 文件沿 `import` 找出受影响的模块，按根包的模块名构建 `src/` 下的代码，并为引用它的 D5 模块选择常规报告。缓存按同一模块名复用。`src/**/*.lean` 也适用主仓的文件行数检查。

严格库的额外条件由根包的 Lake 测试驱动检查。CI 将受影响的内部模块传给驱动，驱动在空内核中重放严格模块的传递声明，并拒绝公理和严格库范围以外的导入。只有变更包含 `src/` 下的 Lean 源文件时，CI 才选择内部库测试。只改审计器时用 `OmegaInit.Prelude` 做定向回归。在仓库根目录运行 `lake test -- OmegaMath.Projective` 可重放该模块及其传递依赖。驱动本身依赖官方 Lean API。[Lake 配置](../lakefile.toml) · [驱动](OmegaChecks/Audit.lean)

## 严格边界

| 审计入口 | 传递闭包的模块数 | 声明数 | 传递公理数 |
| --- | ---: | ---: | ---: |
| `OmegaInit` | 6 | 36 | 0 |
| `OmegaMath` | 9 | 49 | 0 |
| `OmegaChecks.ProjectiveOverlap` | 9 | 50 | 0 |

审计从编译产物读取完整导入集合，逐条检查声明，再把整个闭包交给空的 Lean 4.35.0 内核环境重放。三个入口的闭包均无官方 Init 或 Mathlib 模块。两个反例分别检验审计会拒绝未被使用的公理和遗漏 `prelude` 产生的隐式官方导入。信任基础包括官方内核的归纳类型、宇宙与定义相等规则。[审计实现](OmegaChecks/Audit.lean)

## 复现

在已安装主仓钉版工具的 worktree 根目录运行：

```sh
make lean LEAN_TARGETS=OmegaInit
python3 src/OmegaChecks/check.py
python3 src/OmegaChecks/check.py --incremental
```

最后一条用于独立实验 worktree。它临时创建一个独立专题，分别修改已提交的射影和基础源码，对射影模块分别测试等价改写证明和新增公开定理，逐次定向构建并恢复，再核对原始锁文件字节。测量以被观察模块的 `.olean` 修改时间为准。测试使用匹配的 Mathlib 依赖缓存。[复现脚本](OmegaChecks/check.py)

| 临时改动 | 被观察的 16 个模块中哪些重编 |
| --- | --- |
| 加入目标均未引用的独立专题 | 0 个 |
| 仅改写缩放定理的证明项，签名相同 | 1 个，即证明所在的射影模块 |
| 射影模块增加公开定理 | 4 个，包括射影模块、数学总入口和两个消费模块；只引用读数定义的算例复用 |
| 基础 Prelude 增加公开定理 | 14 个，包括 6 个基础模块、2 个 Omega 数学数据模块、读数定义、射影与数学入口及 3 个消费模块 |

四次实验中，原有 D5 定理和所观察的 `Mathlib.Data.Nat.Prime.Basic` 都复用产物。锁文件 SHA-256 为 `8550e44937f85a9be196a2917a075eeb8c22bf6c15baa83e72017c6fc4437a8e`，与分支起点相同。另在同一 worktree 的临时目录里，以两个互相通过本地路径引用的 Lake 包对照：基础包里添加未导入的文件时观测到 0 个模块重编；修改基础 Prelude 时 6 个模块重编，跨包的射影模块在其中，独立模块复用。实验范围是固定工具链、有缓存的定向本地构建。
