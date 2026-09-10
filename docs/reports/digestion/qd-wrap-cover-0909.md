# B1.1 / B3 / B4：忠实性复核与上游包装

实施结算：三个最薄上游包装均已 kernel 验证并冻结；B3、B4 两个靶 atom 已 `absorbed-closed`。B1.1 的两个既有子 atom 已分别闭合，父 atom 仍为无覆盖边的 `residual-open`，被 canonical cover 的既有分解校验拒绝。故父靶闭合数为 **2/3**，不冒称全部 cover；没有触发预登记数学停止判据 2/3/4，工具阻塞单列如下。此报告为开 PR 前的已推送交付快照，PR/CI 最终状态由 runner result 记录。

产地：无 skill，单 Codex worker 直接实施与自查，零独立评审席；前两席的判形继承自 `qd-family-triage-0909.md`，不是本席独立共识。LANE #6160；分支 `lane/math/qd-wrap-cover-0909`；起点 `4ee990c9cb7eb3c8692f0c3f6e5be53cf28f9c85`。

已完整读取 CLAUDE.md、两份 brief note、standing-math-loop 第八至十二节和前席报告。前席探针源码从两个已提交的 triage 分支读取；报告中相对链接的附件没有一并带入本树，不冒称那些链接在本树可用。所有临时文件和原始运行日志在 runner attempt 目录中。初始已有暂存报告与未跟踪的 `candidates.json`、`family.json`；提交只定向 add。

## 第 0 步：写 Lean 之前的逐子句映射

开工三次 `make show-atom ATOM_ID=<完整 id>` 均 EXIT=0，当时 `coverage_gids=[]`。以下映射是实施前登记；编译通过之后还须按实际声明再次对账。任一项不能兑现即该条 `partial`，不 deposit、不 cover。三条既判 `proof_shape=bind-only`、`escape_witness=null`；本席只允许 `admission_basis=rule-11-upstream-wrapper`，遇到新数学引理、归纳或估计即停止该条。

共同对象：保留冻结的 `sourceThetaCoefficient` / `sourceJensenPolynomial`。实系数模型的复化必须在声明中识别为 `(sourceJensenPolynomial d).comp (C (-1) * X) |>.reflect d`。反射多项式在零点有正确顶系数值；只在非零处使用倒数公式。次数只用 `natDegree ≤ d`，不假设原 P 的次数恰为 d。B3/B4 的 `h0 : sourceThetaCoefficient 0 = 1` 对应源设置逐字的 `a_0=1`（QUANTUM-RH 的固定对象节），不是本席新证的分析桥。其系数正性由冻结 `source_theta_normalization h0` 第四投影得到，不另作全阶正实现假设。

### B1.1

atom `1e414ffb45d7fcaa9536a956298c4e291f91a2e310f112d2cf8419518caefd1a`。

拟落点 `D5/S3/Zeros/Jensen/SourceJensenIntegralExtension`；主声明 `source_jensen_integral_extension`。Binder：任意 `d : ℕ`、`2 ≤ d`；积分和高度的自变量为全部 `x : ℝ`，包括零与负数。保留 B1 的非退化范围，不新增源归一化前件。

| atom 子句逐字原文 | 拟声明的对应项 | 状态与边界 |
| --- | --- | --- |
| `R_d(x) = \int_0^x d\alpha_d^{\,d-1}q_{d-1}(u/\alpha_d)\,du.` | `sourcePrimitive d x` 的定义 | equivalent；有向区间积分，任意实 x；d≥2 保证 α 非零 |
| `q_d(x)=R_d(x)+\beta_d,` | 主声明的全 x 积分等式 | equivalent；实模型复化等于实际 source reflect，无 x≠0 假设 |
| `\beta_d=(-1)^d\frac{d!}{d^d}a_d.` | `sourceConstant` 定义及 `sourceQ.eval 0 = sourceConstant` | equivalent；d≥2，保留符号、阶乘及 d^d |
| `已知前 \(d-1\) 阶，整个导数 \(q_d'\) 已经确定；新增的实际信息只进入一个积分常数。` | 导数多项式等式与上列积分等式合取；任意替代常数 b 的多项式仍有同一导数 | equivalent；直接给 B1 的完整导数，不仅给某点导数 |
| `但“只增加一个数”不等于这一步容易。` | 无复杂度或可解性保证 | equivalent；这是否认推论的评语，无新增数学结论 |
| `这个数会同时改变全部极值点的高度，因此可能影响整个多项式的实根结构。` | 对任意实 b、全部实 x 给平移后值 `R_d(x)+b`、导数不变、零点 iff `R_d(x)=-b`；每个实 x 均有使其为根和不为根的两个常数 | equivalent；包含所有临界点。这里只论允许常数平移的族，不断言实际 theta 常数可自由选择，也不声称每次变化都破坏全实根性 |

准入两半：`intervalIntegral.integral_eq_sub_of_hasDerivAt`，本地 `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1148`；必要的 atom 原文为 `q_d(x)=R_d(x)+\beta_d,` 与 `R_d(x) = \int_0^x d\alpha_d^{\,d-1}q_{d-1}(u/\alpha_d)\,du.`。上游 FTC 的函数/导数需绑定到指定的相邻源多项式。常数平移、零点 iff 和两常数见证均为环及逻辑归一化，不新增根估计。

### B3

atom `2bc63109d666c92a11aa641dbeae45bc08e3f4f939bc5ce4406a75e5d86d03b6`。

拟落点 `D5/S3/Zeros/Jensen/SourceJensenPositiveExtension`；主声明 `source_jensen_positive_extension`。Binder：`n : ℕ`、`d=n+2`，任意 `λ : Fin (n+1) → ℝ`、互异、严格正且均为前阶 q 的根；`h0` 如共同设置。节点定义为 `tᵢ=((d-1)/d)λᵢ`，由 B1.1 的导数项消去临界点假设。互异代替排序只放宽枚举方式，结论对任意顺序成立。

| atom 子句逐字原文 | 拟声明的对应项 | 状态与边界 |
| --- | --- | --- |
| `在上述有限假设下：` | 上述前阶 λ binders、正性、互异、root 假设；缩放 t 定义 | equivalent；不只输入任意临界点，更不假设目标 charpoly |
| `q_d\text{ 全部为正实根} \iff \eta_{d,i}\ge0 \quad\forall i.` | `PositiveSplit q ↔ ∀ i, 0 ≤ η i` | equivalent；`Splits` 加所有实根严格正；两方向，η 允许等于零，q 的重根允许 |
| `而当这些数非负时，可以构造：` | 任意 `∀ i, 0 ≤ η i` 推出同一指定 arrow 的性质 | equivalent；不是存在一个未指定矩阵 |
| `K_d= ... >0,`（B14 的完整矩阵见 CAS 原文） | arrow 的首对角 `a₁/d`、其余对角 t、对称非对角 `Real.sqrt η`、其余零；结论 `PosDef` | equivalent；严格正定，不是半正定；平方根只在 η≥0 分支使用 |
| `\det(xI-K_d)=q_d(x).` | 上述 arrow 的 `charpoly = sourceQ d` | equivalent；多项式恒等式，包含节点 t 和零点，不仅限 Schur 分母非零处 |

η 是原文 `-d*q(tᵢ)/q''(tᵢ)`；分母非零须从全部互异临界点及次数证明，不能靠 Lean 除零全函数化。

准入两半：`Matrix.det_fromBlocks₂₂` — `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean:384`；`Lagrange.eq_interpolate` / `Lagrange.eval_interpolate_not_at_node` — `.lake/packages/mathlib/Mathlib/LinearAlgebra/Lagrange.lean:362` / `:685`；`Matrix.IsHermitian.posDef_iff_eigenvalues_pos` — `.lake/packages/mathlib/Mathlib/Analysis/Matrix/PosDef.lean:71`。必要原文为 B14 指定的 `a_1/d`、`\sqrt{\eta_{d,i}}`、`t_i` 箭头矩阵严格 `>0`，以及 `\det(xI-K_d)=q_d(x).`；上游分块行列式和谱判据需专门化为这个矩阵。留数方向沿前席已验的 `Polynomial.Splits.eval_derivative_div_eval_of_ne_zero`（`.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Splits.lean:654`）及导数唯一性，不引入 Laguerre 乘法归纳。前席不用的 `laguerre_mul` 不进入生产模块。

### B4

atom `c0a72a217fb966246fd4a48a809795cdc539435d1e88d1a10d041a9bcd9ed98d`。

拟落点 `D5/S3/Zeros/Jensen/SourceJensenCouplingBudget`；主声明 `source_jensen_coupling_budget`。与 B3 同样的实际前阶根、缩放节点、源规范；不额外假设 η 非负，代数预算无需它。

| atom 子句逐字原文 | 拟声明的对应项 | 状态与边界 |
| --- | --- | --- |
| `在定理 B3 的设置下：` | 与 B3 同样的 d≥2、h0、互异严格正前阶 λ 及 t 定义 | equivalent；临界性由 B1 接出，分母非零有证明 |
| `\sum_{i=1}^{d-1}\eta_{d,i} = \frac{d-1}{d^2}\left(a_1^2-2a_2\right)` | `Fin (n+1)` 全和等于 `(n+1)/(n+2)^2*(a₁²-2a₂)` | equivalent；1-based 枚举改为 Fin 的 0-based，项数仍恰 d−1 |
| `= -\frac{d-1}{12d^2}\chi_4.` | 同一和等于 `-(n+1)/(12*(n+2)^2)*(sourceThetaMoment 2-3*(sourceThetaMoment 1)^2)` | equivalent；moment 下标 k 指 2k 阶；χ₄ 为原文 m₄−3m₂²，负号、12、d² 均保持 |

准入两半：`Lagrange.coeff_eq_sum` — `.lake/packages/mathlib/Mathlib/LinearAlgebra/Lagrange.lean:495`；必要原文是完整 B18：`\sum_{i=1}^{d-1}\eta_{d,i} = \frac{d-1}{d^2}\left(a_1^2-2a_2\right) = -\frac{d-1}{12d^2}\chi_4.`。取前席的 `R=q-d⁻¹Xq′+(a₁/d²)q′`；R 的次数/节点值/系数只做规范化，和式为上游系数公式实例；χ₄ 换元为环归一化。若除此还需新数学命题，停止，不包装成 content。

## 布局、用途与检索边界

三个模块的理由：分别是积分、正定箭头构造、系数和预算；逐条首冻后不再编辑旧模块。共同的源 Q 定义由积分模块给出，后两条直接消费；B4 使用与 B3 同一 η 定义，不另造数值对象。域 `S3/Zeros` 已由 `git ls-tree origin/dev --name-only D5/S3/` 实查存在。开工目录直接文件数：Lean 5/48、Blueprint 10/48、Frozen/state 5/48；预计三模块后分别 8/48、16/48、8/48。阈值本地读取于 `RepositoryRules.Structure.cs:68`，没有改预算。

所有拟公开定义是符号多项式/积分/矩阵，所有拟定理量化无界 d 和任意根元组；无有界枚举、检查器、数值归约或单个已认证有限实例，故逐声明 `utility: none`。常数平移的存在见证是任意 x 的符号构造，不是枚举有限样本。生产模块只保留该 atom 需要的公开结果及其实际 API 定义；规范化 helper 私有。

已读落点既有五个 Lean 模块全文。D5 全树按反射、Jensen、留数、插值系数和、FTC、箭头关键词粗筛；既有 FTC 消费者属于其它函数，未发现这三条源对象的现成 coverage。正则阳性 `\bsource_jensen_degree_lowering\b` 为 1 命中，阴性 `\bqd_wrap_missing_control\b` 为 0；这不是检索穷尽声明。含 Unicode 下标的名字不用末尾 `\b` 当存在性判据；`det_fromBlocks₂₂` 已直接阅读声明原文。

本地 Mathlib pin `db584cd6d46c92f209a44c0f1c829460d327499d`；Lean `leanprover/lean4:v4.33.0`。`Matrix.IsHermitian.charpoly_eq` 的本树行号是 Spectrum.lean:155（不照抄前席 :154）。所有生产 anchors 必须引用实际直接 import 的模块。

冻结前置实查：`NormalizedJensenDegreeLowering` 的 pin `sha256:ee43a04a542df25237818cbfeeb29bb1abaed956f90db04822d08e8f413d50b4`；`SourceThetaMomentBounds` 的 pin `sha256:9de7bd223c662525a590ce1366b1efcfc26700544e7bb42d0e6fb229b51f67f1`；`SourceJensenPrincipalBlockObstruction` 的 pin `sha256:5e43098caa9fb48b4fccd8adc30e337ff93668044d5dcfc06acab33dc8970f3c`。作用域分别为任意实系数的归一化降阶、h0 下的源系数严格正性、源多项式系数边界；都不承担实际 RH 的分析桥。

## 非空对照（实施前的精确算术）

这些是报告中的代数样本，不是公开有限实例：取 d=2、a₀=1、a₁=3、a₂=4，则 q₂=x²−3x+2，q₁=x−3，λ=3、t=3/2、q₂(t)=−1/4、q₂″=2、η=1/4。箭头矩阵为 [[3/2,1/2],[1/2,3/2]]，本征值 1、2；预算 (9−8)/4=1/4，m₂=6、m₄=96、χ₄=−12。R₂=x²−3x、β₂=2。换 a₂=6 后 β₂=3、q₂(t)=3/4、η=−3/4、判别式 −3，全部正实根结论不成立。把 β₂ 错设为 0 后 x=0 即反例。将两个数值关系改作假前件（例如仍声称 β₂=0 或 a₂=6 时预算为 1/4）会给不同的等式读数；不以原理只需正例代替双侧检查。这些不是实际 theta 数值计算。

## 运行结算

B1.1 实际声明已按上表逐项复核：全部 equivalent，无 not-covered。`source_jensen_integral_extension` 的六组合取依次是实际源复化识别、完整导数、零点常数、全实数积分式、任意常数平移的导数/值/零点 iff、任意实 x 的两常数见证。没有排除 x=0 或负 x，没有改变 d≥2。

B1.1 `make lean` 第三次 EXIT=0（27.901 秒）；前两次 EXIT=2 是 map/reflect 改写及 simp 心跳问题，改为指定改写闭合，未改预算。公理仅 `[propext, Classical.choice, Quot.sound]`。首次 emit 因 report 过期退出，`make lean-report` EXIT=0（102.810 秒）；第二次 emit 因公式 `\foralld` 缺空格退出；修正显式空格后第三次 emit EXIT=0（77.451 秒），生成公式已人工逐行核对。首次 deposit 因 origin/dev 非祖先退出；合入 `9dbd613904` 无冲突并推送 merge `3f196f3609` 后重试。第二次 deposit 已通过头部检查并首次冻结该模块，但 cover 返回 EXIT=2、`partial-closed deletable=false gaps=chain-migration-incomplete,chain-migration-incomplete`。

该父 atom 在开工 HEAD 中已经有两个 chain_atoms；本席未创建分解。`ae0bab9f69ee727493c512081c7cf2ec5c7992e536f73c885d5b43ff5e848dd8` 是表中积分定义和 B6；`2ddc623648638e26a2ab88e8751cc1159762a5ec1a6aa6b15028686d37699552` 是表中完整导数、常数信息、难易评语和极值/实根散文。两次额外 `make show-atom` EXIT=0，逐字核对确认分别对应既有忠实性表前三行和后三行，均由同一主声明完整承载，故按 canonical cover 逐个闭合，再重试父 atom；不删链、不把散文静默 settle。

15 个显式声明（含私有 helper）的逐声明用途理由、公理与 statement_id 见 [declaration-audit.json](qd-wrap-cover-0909/declaration-audit.json)，全部 `utility: none`。主声明身份为 `sha256:a8936b9e14aa7a92fc0e635fc797651d50954edfd7b5a05df5349a1a55a1455e`。anchors=实际第 9 行直接 import；其余 proofs 均是 FTC/反射/系数绑定，helpers 不单独申请准入。

ASSUMED-UNVERIFIED：源规范 a₀=1 的分析证明不在本席；未打开外部论文网页；无独立评审；前席日志不重放。nonclaims：不证明 RH，不主张新数学内容，不以编译绿代替忠实性，不把 rule-11 的必要性等同于可证性，不以 refutes 新造准入依据。

B1.1 积分公式子 atom `ae0bab9f…`：`make cover` EXIT=0（174.578 秒），`ledger_changed=true`，已迁入 absorbed-closed；本次提交携带首次冻结、镜像和这条 coverage。该子 atom 已提交推送 `347db77617`。散文子 atom `2ddc6236…` 随后 `make cover` EXIT=0（175.723 秒），`ledger_changed=true`，同样迁入 absorbed-closed。其难易评语在 Scribe 保留为不作复杂度推论的边界，不伪造复杂度谓词或估计；它的数学断言对应上表后三行。父 atom 的后续重试与判词见下节。

### B1.1 父 atom 的工具阻塞

散文子 atom 已提交推送 `ded5c67dbd`。父 atom 重试 `make cover` EXIT=2（58.115 秒），原文为：

```text
COVER_INVALID digest status is invalid: entry 1e414ffb45d7fcaa9536a956298c4e291f91a2e310f112d2cf8419518caefd1a has multiple clauses but newly claims absorbed with unresolved_subitems=[]; decompose the uncovered clauses before absorption
```

随后 `make decompose ATOM_ID=<父完整 id> DRY_RUN=1` EXIT=0（13.208 秒）：两个计划片段为 `[0,269)`、`[269,552)`，child_id 与现存链逐项一致，均 `reused=true`，`cas_objects=0 ledger_updates=0`。因此更正中间诊断：不是缺分解，也不是忠实性缺口；canonical dry run 确认已有同一字节计划，而 cover 仍拒绝父 atom。

定位：`DigestionStatusEvaluator.cs:130` 的新吸收门消费 `VerifiedClausePlanParents`；`DigestionLedgerAligner.cs:277` 可跳过继承源的计划重验。本席未修改判官、源字节、baseline 或链来绕过拒绝，保留第一次 deposit 生成的失败 disposition。**B1.1 的公式与散文子 atom 已 cover，父 atom 未 cover（工具阻塞）；不计父条成功，不冒称其为忠实性 partial。** 先结算这条并继续 B3/B4。

报告补写时一次 Python stdin 编码错误 EXIT=1，报告未改；改用结构化 patch 补写，不静默漏账。

### B3 实际声明复核

`source_jensen_positive_extension` 的 binder 是 `n : ℕ`、源规范 `h0`、`lam : Fin (n+1) → ℝ`、互异、严格正、前阶根等式；正文没有额外 `hcrit`、`hno` 或目标 charpoly 假设。`d=n+2`，`t=scale d * lam`。实际结论先给全部节点严格正及二阶导数非零，再给上表 B13 的 iff 和 B14 的指定 arrow `PosDef ∧ charpoly=sourceQ d`。逐行复核上表五项全部 equivalent，两个方向、严格正定、η≥0、重根和零耦合边界保持。

`make lean` 第一次在 C# 前置因不存在的 `Eta` 宏退出；改用既有 DSL 的命名符号 `mathrm{eta}`。第二次仅 Lean binder `λ` 是保留 token，改名 `lam`；第三次 EXIT=0（26.163 秒），全部数学证明仍沿前席上游绑定路线，公理仅标准三项。未改预算或关闭 linter；剩余空格/letI 风格 warning 不影响 kernel 判词。

补充精确边界对照：d=2、a₁=3、a₂=9/2，q₂=(x−3/2)²，η=0，K=diag(3/2,3/2)>0，预算与 χ₄ 都为 0；Python Fraction 实算断言通过，已写入 exact-arithmetic-controls.json。它是通用系数样本，不是实际 theta 数值或公开有限实例。

B3 的 `make lean-report` EXIT=0（95.141 秒）、`make emit` EXIT=0（67.678 秒）；生成镜像的全部假设、η 定义和指定矩阵已对照核读。18 个显式声明的逐声明用途理由与公理已加入 declaration-audit.json，全部 `utility: none`；`sed -n '5p;9p'` 确认 anchor 与直接 import 都是 `Mathlib.LinearAlgebra.Matrix.SchurComplement`。

B3 首次 deposit 因 origin/dev 再次前移、非当前 HEAD 祖先而 EXIT=2。合入当时最新 `e7e63c615460da48effcb4a76f96a3a6730af75d`，merge `bb51a6467a` 已推送；已读取新 CONTEXT 全文和 spec 增量。后续事务显式使用这个已合入的 SHA 作为 BASE，保持同一轮检查基准；不修改预算常数。

容量口径更正：前文 5/10/5 与预计 8/16/8 是三个目录的物理文件数。实查 `RepositoryRules.Structure.cs:100` 起的 `IsCapacityExcluded`：Blueprint 的生成 md、Frozen/state 都免计容量。因此正式 SL-003 计费为 Lean 与 Scribe 源各预计 8/48，余量各 40；Frozen/state 没有这项文件槽费用。初始物理计数不冒称机器计费计数。


B3 deposit EXIT=0（773.666 秒，含上游 inspector producer 变更后必需的全量报告）。atom 从空 coverage 的 residual-open 迁入 absorbed-closed，声明身份为 `sha256:aff726c2285de50e35bd19fe5256d773f97e4d4aa967a601cee7df2aeb215989`。随后显式 cover 识别同一已存在的边，EXIT=0（117.378 秒）；整条已提交推送 `f3888ae03c`。

### B4 实际声明复核

`source_jensen_coupling_budget` 与 B3 使用相同的 `n`、源规范 `h0`、互异严格正前阶根 `lam` 及缩放节点 `t`。三个结论依次是每个二阶导数分母非零、同一 `sourceCoupling` 全和的系数表达式、同一全和的四阶累积量表达式。表中三项全部 equivalent；没有耦合非负假设，保留负号、12、d²、恰 d−1 项和 moment 的 2k 下标约定。

本条首次 `make lean` EXIT=0（28.126 秒），`make lean-report` EXIT=0（79.597 秒）。逐声明审计新增 7 项，全批共 40 个显式声明（含私有 helper），公理均限于 `[propext, Classical.choice, Quot.sound]`，用途均为 `none`。B4 的 `anchors` 与第 9 行实际直接 import 都是 `Mathlib.LinearAlgebra.Lagrange`。`nodal_derivative` 和 `residue_sum` 分别实例化上游插值唯一性与系数和式，其余 helper 是源系数、次数和环规范化；没有新的归纳或根估计。

`make emit` EXIT=0（65.360 秒）；生成公式的全部 binder、两个预算等式、η 与 χ₄ 定义及分母非零子句均已逐项核对。三条公开定理在源码中使用的六条冻结定理前置，已实读当前状态片和接受事件中的声明身份，记录于 [frozen-dependencies.json](qd-wrap-cover-0909/frozen-dependencies.json)；其作用域与 GID、声明 statement_id 均逐项列出，不以模块 pin 冒充声明身份。

B4 deposit EXIT=0（278.206 秒），`ledger_changed=true`；atom 已从空 coverage 的 residual-open 迁入 absorbed-closed。声明身份 `sha256:354c620e951865fbc0c9968f4cfedd0d198d23ef766d931d63fb93f93f5884e7`；模块 pin `sha256:30c717d3ad66b80f8338b201f787b65cdcc28792a3e3573b7d1107d7c78447cd`；接受事件 `72ce68de0e295382af7f46043605c339e55e1e9317a57f8cf31af56e68bbbc6e`。

随后的显式 `make cover` EXIT=0（97.656 秒），canonical playbook 把 `already has coverage` 识别为 `coverage-already-applied` 幂等成功；末尾 emit 完成。最终三个模块行数为 173/386/192，Lean 与 Scribe 源目录各计费 8/48、余量各 40；全批没有新域、预算改动或裸 lake。

## 必要性原文（CAS 字节，不缩写矩阵）

### B1.1：准入必要性所引的原文字节

```text
## 推论 B1.1：高阶延拓是一项带常数的积分问题

定义：

$$
\boxed{
R_d(x)
=
\int_0^x
d\alpha_d^{\,d-1}q_{d-1}(u/\alpha_d)\,du.
}
$$

那么：

$$
\boxed{
q_d(x)=R_d(x)+\beta_d,
\qquad
\beta_d=(-1)^d\frac{d!}{d^d}a_d.
}
\tag{B6}
$$

这很重要：

**已知前 \(d-1\) 阶，整个导数 \(q_d'\) 已经确定；新增的实际信息只进入一个积分常数。**

但“只增加一个数”不等于这一步容易。

这个数会同时改变全部极值点的高度，因此可能影响整个多项式的实根结构。

---

```

### B3：准入必要性所引的原文字节

```text
## 定理 B3：一步正延拓的精确判据

在上述有限假设下：

$$
\boxed{
q_d\text{ 全部为正实根}
\iff
\eta_{d,i}\ge0
\quad\forall i.
}
\tag{B13}
$$

而当这些数非负时，可以构造：

$$
\boxed{
K_d=
\begin{pmatrix}
a_1/d&\sqrt{\eta_{d,1}}&\cdots&\sqrt{\eta_{d,d-1}}\\
\sqrt{\eta_{d,1}}&t_1&&0\\
\vdots&&\ddots&\\
\sqrt{\eta_{d,d-1}}&0&&t_{d-1}
\end{pmatrix}>0,
}
\tag{B14}
$$

使：

$$
\det(xI-K_d)=q_d(x).
$$

```

### B4：准入必要性所引的原文字节

```text
## 定理 B4：新增耦合总预算

在定理 B3 的设置下：

$$
\boxed{
\sum_{i=1}^{d-1}\eta_{d,i}
=
\frac{d-1}{d^2}
\left(a_1^2-2a_2\right)
=
-\frac{d-1}{12d^2}\chi_4.
}
\tag{B18}
$$

```
