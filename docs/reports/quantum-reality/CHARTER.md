## 这条线是什么(每轮不变的部分)

**仓库**:https://github.com/the-omega-institute/trureturing(公开,可匿名读)
**议题**:`/issues/6298`。**请先取评论链**;前四轮的判词全在里面。取不到就明说取不到,
不要从主帖反推——前三轮你都没取到,每次都如实标注了,那是正形,请保持。

**靶**:量子观察者假设能推出多少物理结构。产出**不是**灵感,而是三类可结算的东西:
1. **能推出的**——给出可直译 Lean 的陈述 + 逃逸见证(那条非平凡的中间命题叫什么);
2. **推不出的**——给出反驳或 no-go,并说清它反驳的**精确边界**(反驳了什么、没反驳什么);
3. **卷内的错**——卷里的断言与仓内已冻结的 Lean 声明矛盾,给出双方原文与 GID。

**假设 19.1 的实际内容**(别把它记成别的):两个线性实场 `q, r`,二次 Lagrangian
`½q̇² + ½ṙ² − (c₀²/2)|∇q|² − (c_h²/2)|∇r|² − (Ω₀²/2)q² − (Ω_h²/2)r² − λqr`,
加边界条件,再把隐藏场 `r` 做 Schur 消元。**它是线性响应装置,不是动力学原理。**

## 已结算的,不要重做

- **反例链 L1–L2.5 全部已冻结**:`TridiagonalChainInverse` / `ChainBlockPencil` /
  `ChainSchurResponse` / `IntegerFischerSelector` / `UniformResolventRemainder`。
- **L3 判 `refutes`**(第四轮):`effective n k b = diag(k − b·η_n, k)`,`η_n = t_n²/z_n`,
  `t_n = 1/D_{n+1}`,`D` 是整数递推 `D₀=1, D₁=4, D_{n+2}=4D_{n+1}−D_n`。
  每个有限 n 都非标量(`η_n > 0`),但 selector loss `≤ η_n²/2 ≤ ½·81^{−(n+1)}` 指数塌零。
  ⟹ **微观整数间隙不向实值 Schur 响应传递**;它**不**反驳整数层的 `integer_log_unique_maximum`。
- **离散被抹掉的三处已点名**:`chain_endpoint_sq_le`(精确整数递推 ⇝ `9^{−(n+1)}` 包络)、
  `chain_energy → chain_coercive`(边界几何 ⇝ 统一下界)、`remainder_bound`(`l2_opNorm_mul` 压成范数积)。
- **5040 的算术侧已冻结且更强**:`GoldenResource5040PriceInterval.
  golden_resource_5040_unique_maximum_of_price_interval` 证 5040 在**全体 n ≥ 1** 中唯一最优;
  另有 `GoldenDepthForcesPrimeSupport.prime_dvd_of_two_adic_depth`。
  **不要再为「区分 5040 与 7920」派题——已知结果不是靶。**
- **`c_eff` 的 no-go 已收窄并冻结为这个形状**(第 5 轮):
  「边界/整数微观离散本身,不能迫使一个随链长有统一正下界的有效传播系数差。」
  它**不**反驳:每个有限 n 的非标量性、`integer_log_unique_maximum`、不同裸 `c₀/k` 的 O(1) 差、
  cross-species 对称性强加的共同速度、以及「19.1 类存在不同 `c_eff`」这一事实。
  **更强的说法(「观察者假设只推出一个普适 `c_eff` 极限」)已被判为过强,不得冻结。**
- **`c_eff²` 不是包络的产物**:卷 (19.3)(19.4) 给 `Z = 1 + λ²/Ω_h⁴`、
  `c_eff² = (c₀² + λ²c_h²/Ω_h⁴)/(1 + λ²/Ω_h⁴)`,是低频领先阶**精确**系数
  (`QUANTUM-REALITY.md:1535–1548`)。19.1 的模型类**不收敛到同一常数**(同卷 `:1684`)。
- **量词边界**:允许 `b = b_n` 以 `9^{n+1}` 增长则 `b_n·η_n` 可保持 `O(1)`;
  该特化不是从观察者假设推出的。
- **一般 `(k,b)` 的 `no_uniform_gap` 封装判 bind-only,已否决,不要再提。**
- **周界图的压缩句(第 5 轮的正式产出)**:19.1 给 **response 与 conditional characteristic
  geometry**;**不给 universality、objective、causal completion 或 dynamics**。
  右栏五项各缺一条可点名的额外公理:observer→objective 桥、所有探针共享同一 `c_eff` 的
  cross-species principle、微观 gap 传成可观测 gap 的下敏感度公理、无隙极限下 §17 涨落界的替代估计、
  以及 Einstein 方程所需的三项(张量几何自由度 / 应力能普适耦合 / backreaction 方程)。
- **越界红线**:「二次经典场模型 ⟹ Born rule / 量子态 / 热涨落分布」**不成立**。
  19.1 只有两个线性实场与二次 Lagrangian;凡涉及量子统计的陈述,
  **必须先点名它额外用了正则量子化、态制备、测量规则中的哪一条**。
  不得因为卷名叫「Quantum Reality」就当成 19.1 的逻辑后果。
- **符号陷阱**:§19 的场耦合写作 `λ`,§305/306 的资源价格也写作 `λ`,
  **源码里没有任何定理把两者等同**。同名不同物,不许因符号相同就接上。

- **§19 场模型已落地(第 6、7 轮结算,PR #6508 MERGED)**:
  `D5/S3/Observer/BlockStructure/HiddenFieldResponse` 已冻结,内含 `hiddenDen`、
  `hidden_field_solve_eq`、`hidden_field_schur_response`,以及三条**具名伴随结果**
  `c_eff_sq_sub_bare` / `c_eff_sq_bounds` / `principal_symbol_eq_zero_iff`
  (后三条判形为 bind-only,docstring 逐条标明)。**不要再问这三条的落地形状,那一页已翻过。**
  `hiddenDen Oh ch kSq omega := Oh^2 + ch^2*kSq - omega^2`;`hiddenDen ≠ 0` 在该模块里是**显式假设**。
- **低频窗口 ⟹ 非共振:数学为真,但判形 bind-only,不冻结**(第 7 轮点名的缺口)。
  `|c_h²·kSq − ω²| < Ω_h²` 蕴含 `0 < hiddenDen`,故窗口内消元不必另设非共振假设;
  已实现且三方绿(`EXIT=0`、零 `sorryAx`),20 万次取样零反例。
  但三条证明分别是 mathlib 引理实例化 + `linarith`、`ne_of_gt` 投影、以及对冻结定理的**去假设化**,
  三种 `admission_basis` 逐条不成立,故**不单独首冻**;源码存档在 `/issues/6298`,
  等第一个真正的 §19 下游内容模块出现时作其私有引理。
  **这一条计入第 5⁴ 条「连续两次 bind-only 即停手」的第一次。**
- **下敏感度桥:universal 版已判与 L3 族不相容**(第 7 轮)。
  `UniformLowerSensitivity κ micro obs := 0 < κ ∧ ∀ n, κ·micro n ≤ obs n`
  与链族矛盾(族内 `micro ≥ 1` 而 `obs` 指数塌零),两端**都已冻结**
  (`integer_log_unique_maximum` 与 `ChainResponseSelectorGap` 的几何界)。
  **不得偷偷允许 `κ = κ_n → 0`**——那不是右栏缺的那条公理。
  右栏第三项的地位因此待重判(本轮 Q2)。
- **§17 未发现卷内错,但 theorem factoring 可精化**(第 6、7 轮均未找到卷内错)。
  定理 17.3 把 (17.5) 与 (17.6) 放在同一个 `ν_a ≥ ν_* > 0` 之下;
  **(17.5) 的右端是 `β⁻¹`,不含 `ν_*`,证明只用 `x·coth x ≥ 1`**,
  而 `coth x ≥ 1` 配 `ν_a ≥ ν_*` 是 (17.6) 才需要的((17.6) 的系数含 `ℏν_*/2`)。
  `ν_* → 0` 时**首先失效的是假设**,不是逐 n 的结论;卷自己的 Cor. 17.1 已写明这一点。
  **这不是卷内错**,不得报成错误。

## 纪律(违反则该轮判词作废)

- **禁模糊措辞代替测量**:不许「很可能 / 大概 / 应该是」。要么给读数与出处,要么明写
  「我没验证 X,因为 Y」。
- **区分「读了源码」与「跑了构建」**。你只能读公开 URL,读不到本地未推送内容;
  凡结论依赖未推送改动,标 `ASSUMED-UNVERIFIED`。
- **不为了让管线有活干而造题**。**「这条该停」「这个已被更强的冻结定理覆盖」是本轮允许的最好答案之一**
  ——上一轮你就是这么答的 Q3,它替我省下了一个白派的席位。
- **凡你自己额外指定的模型或参数特化,必须明标它不是从观察者假设推出的**。
- 候选进管线前先答一句「文献/仓内有没有这条陈述」;口径只能是「所查来源未找到」,
  **不得写成「文献中不存在」**。

## 交付格式

markdown,分段回答下面每个问题,最后必须有一段 `我没核实的部分`。
凡给出可直译 Lean 的陈述,同时给:逃逸见证的名字、它**不是**哪条冻结定理的平凡推论、mathlib 支撑面。
