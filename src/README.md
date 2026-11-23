# 同一 Lake 包中的 Omega 模块实验

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

根配置沿用原默认目标 `Trureturing`。只计算读数的文件导入 `OmegaMath.Projective.Basic`，严格证明示例直接写 `prelude`、`import OmegaMath.Projective`，证明任意正整数对角坐标的读数为 1/2。混合示例在同一模块使用官方素数定理和 Omega 读数。根目录 D5 里的一个已有定理作为独立编译对照；脚本另外通过 Lean 的标准输入在内存中给同一份 D5 源码加入射影模块导入和证明，检验原路径能消费新库。[严格消费示例](OmegaChecks/ProjectiveOverlap.lean) · [混合示例](OmegaChecks/Mixed.lean)

## 复现

在已安装主仓钉版工具的 worktree 根目录运行：

```sh
make lean LEAN_TARGETS=OmegaInit
python3 src/OmegaChecks/check.py
python3 src/OmegaChecks/check.py --incremental
```

最后一条用于独立实验 worktree。它临时创建一个独立专题，分别修改已提交的射影和基础源码，对射影模块分别测试等价改写证明和新增公开定理，逐次定向构建并恢复，再核对原始锁文件字节。测量以被观察模块的 `.olean` 修改时间为准。测试使用匹配的 Mathlib 依赖缓存。[复现脚本](OmegaChecks/check.py)

| 临时改动 | 被观察的 12 个模块中哪些重编 |
| --- | --- |
| 加入目标均未引用的独立专题 | 0 个 |
| 仅改写缩放定理的证明项，签名相同 | 1 个，即证明所在的射影模块 |
| 射影模块增加公开定理 | 4 个，包括射影模块、数学总入口和两个消费模块；只引用读数定义的算例复用 |
| 基础 Prelude 增加公开定理 | 10 个，包括 4 个基础模块、读数定义、射影与数学入口及 3 个消费模块 |

四次实验中，原有 D5 定理和所观察的 `Mathlib.Data.Nat.Prime.Basic` 都复用产物。锁文件 SHA-256 为 `8550e44937f85a9be196a2917a075eeb8c22bf6c15baa83e72017c6fc4437a8e`，与分支起点相同。另在同一 worktree 的临时目录里，以两个互相通过本地路径引用的 Lake 包对照：基础包里添加未导入的文件时观测到 0 个模块重编；修改基础 Prelude 时 6 个模块重编，跨包的射影模块在其中，独立模块复用。实验范围是固定工具链、有缓存的定向本地构建。

## 严格边界

从新生成的编译产物加载并在空内核环境中重放。`OmegaInit` 共 4 个模块、47 条声明，`OmegaMath` 共 6 个模块、49 条声明，直接引用射影模块的严格消费示例共 6 个模块、50 条声明。三个入口的传递闭包均无官方 Init、Mathlib 或公理。专门注入的未使用公理和隐式官方 Init 导入均被拒绝。CLI、正式登记冻结和生产 CI 的耗时不在本次目录布局实验范围内。[审计实现](OmegaChecks/Audit.lean)
