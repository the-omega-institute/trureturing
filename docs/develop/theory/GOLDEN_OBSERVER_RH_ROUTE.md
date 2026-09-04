# 黄金观察者黎曼猜想：最新研究综述与形式化线路图
## 自由研究线开题卷；不是证明声明

检索与仓库取阅截点：2026-08-30，Asia/Singapore。  
仓库基线：公开仓库 `the-omega-institute/trureturing` 的 `dev` 分支；本文独立取阅了开放心脏、选定 Weil 内核模块及两份理论卷。用户给出的“约 197 个 Weil/临界线模块”作为规模基线使用；本文没有把目录规模重新计数当作数学证据。  
总裁决：截至本卷截点，经典黎曼猜想仍未解决；Clay Mathematics Institute 仍将其列为未解决的 Millennium Prize Problem。2026 年出现了非常强的新比例定理、有限 Weil 压缩、可认证窗口正性和新的形式化成果，但没有一项把“几乎所有、有限窗口、有限高度、有限矩阵、条件谱极限”提升为“每一个非平凡零点都在临界线”。

## 证据标签

- `[literature-attested]`：有可核论文、预印本、期刊、官方项目页或公开代码源；同时标明同行评审、预印本或项目自述状态。
- `[repo-derived | GID: ...]`：直接来自 Lean 内核文件及其 GID。
- `[repo-derived | path: ... | GID: not present]`：来自仓库理论卷；它是热层说明，不是 kernel theorem。
- `[suspected-novel]`：本卷作出的仓库专属综合、坐标选择或研究治理设计；不主张文献优先权，不得写成“已知定理”。
- “已闭合”只表示 Lean 声明无 `sorry` 且通过仓库构建与 `#print axioms` 审计；本文给出的拟议声明未经本地仓库编译，不冒充已闭合。

# 第一部　2024–2026 最新研究地图

## 一、总图：发生了什么，尚未发生什么

### 1. 当前最强的直接比例结果

[literature-attested | very recent preprint]

Levent Alpöge 与 Ralph Furman 在 2026 年预印本中证明：按重数计，至少三分之二的黎曼 zeta 非平凡零点既简单又位于临界线；至少六分之五的零点彼此不同。作者还报告利用 Montgomery–Taylor 型窗口将相应常数提高到约 $0.6725$ 与 $0.8362$。方法的核心不是假定 Weil 形式全局正定，而是研究 Weil Hermitian form 的有限压缩，通过秩—迹不等式和离线共轭轨道的惯性控制取得比例结论。

出处：Levent Alpöge, Ralph Furman, “More than two thirds of the zeta zeros are simple and on the critical line,” 2026, arXiv:2608.13637v2。

状态判断：

- 这是 2026-08-30 时极新的预印本，尚不应按长期同行评审定理的社会学确定性书写。
- 即使比例达到 $99.999\%$，仍不能排除一个无限稀疏的离线零点集，因此比例定理不推出 RH。
- 该工作自述有 Lean 4 形式化。公开仓库 `anthropics/zeta-23-lean` 的 README 宣称对应最终结果已经形式化；但本次取阅到的顶层 `Zeta23/Unconditional.lean` 可见导出面仍显示较早的“三分之二在线、二分之一简单、四分之三不同”常数。故在本仓消费前，必须固定具体 commit、成功构建并定位最终导出 theorem，不能仅凭 README 写“完整强度已进入内核”。

### 2. RH 的公共状态没有改变

[literature-attested]

Clay Mathematics Institute 在 2026 年仍将 RH 列为 Millennium Prize Problem。有限高度核验、比例定理、随机矩阵拟合、有限算子谱和形式化的条件结论都没有构成 Clay 意义下的全局证明。

出处：Clay Mathematics Institute, “Riemann Hypothesis,” 2026 年仍在官方 Millennium Prize Problems 名录中；无 arXiv 号。

## 二、Weil／Li 正性方向的新进展

### 1. 经典基准线

[literature-attested]

Weil 路线把 RH 转写为显式公式所定义的二次型在适当测试函数代数上的非负性。Li 路线把 RH 转写为全部 Li 系数 $\lambda_n$ 的非负性。两者不是“数值上经常正”即足够，而是需要对完整测试类或全部 $n$ 作一致断言。

经典出处：

- André Weil, “Sur les ‘formules explicites’ de la théorie des nombres premiers,” 1952, Comm. Sém. Math. Univ. Lund, 252–265；无 arXiv 号。
- Xian-Jin Li, “The Positivity of a Sequence of Numbers and the Riemann Hypothesis,” 1997, Journal of Number Theory 65, 325–333；无 arXiv 号。
- Enrico Bombieri, “Remarks on Weil’s quadratic functional in the theory of prime numbers I,” 2000/2001, Rendiconti Lincei 11, 183–233；无 arXiv 号。
- Enrico Bombieri, “A variational approach to the explicit formula,” 2003, Communications on Pure and Applied Mathematics 56, 1151–1164；无 arXiv 号。

### 2. 有限窗口、可认证正性与极小谱隙

[literature-attested | 2026 preprint]

Marcus Chuk 把支撑限制在有限窗口中的 Weil 正性问题约化为有限 PSD 矩阵／算子压缩问题，并给出上下两侧的可认证界。作者报告：

- 在窗口参数 $L=0.8$ 时得到约
  $Q(f)\ge 8.9\times10^{-18}\lVert f\rVert_2^2$，
  同时有约 $2.27\times10^{-17}$ 的上界；
- 在 $L=2$ 时，最优常数的无条件上界已降至约 $3.2\times10^{-283}$；
- 大窗口下的谱隙可以快得惊人地塌缩，点值包络会遭遇双指数频率障碍。

出处：Marcus Chuk, “Weil positivity in compact windows: certified two-sided bounds and a Landau–Widom decay law,” 2026, arXiv:2608.24827。

批判性含义：这不是“窗口增大后越来越接近证明 RH”的单调成功故事。有限窗口正性可能长期成立，而最小特征值迅速逼近零；用更多位小数重复认证同一 $L$，其边际数学信息可能趋近于零。这正是第四部 DECT 停止规则必须捕捉的情形。

### 3. 有限 Guinand–Weil 字典与尾项预算

[literature-attested | 2026 preprint]

Akiva Groskin 给出从有限 Galerkin 向量到带限 Guinand–Weil 测试函数的精确字典，使有限零点和等于有限矩阵二次型；被截去的 archimedean 尾项表现为正的 Cauchy–Stieltjes 增量，并有显式数量级

$B_T\sim\frac{(2N+1)\rho\log T}{\pi^2T}$。

出处：Akiva Groskin, “A finite Guinand–Weil dictionary and archimedean tail order for the truncated Weil quadratic form,” 2026, arXiv:2607.02828v3。

该工作的价值不是“有限矩阵代替了无限问题”，而是把以下三件事分开：

1. 有限矩阵恒等式；
2. 截断误差的符号与上界；
3. 从固定 $(N,T)$ 到全测试类极限所需的一致性。

本仓的 `Budget`、`ZetaExplicit`、`ZeroSum` 与 `TestFunctions` 子族正好可以消费这种分层。

### 4. Screw function、模型空间和谱算子重述

[literature-attested]

Masatoshi Suzuki 在 2026 年把 Weil 二次型、screw function、de Branges／模型空间及若干 Connes 型构造放在统一框架中，并提出其自伴算子极限应以 zeta 零点纵坐标为谱的猜想。框架中的许多恒等式无条件成立，但最终谱识别仍是猜想，而不是 RH 证明。

出处：Masatoshi Suzuki, “Weil’s quadratic form via the screw function,” 2026, arXiv:2606.09096v2。

Alain Connes 与 Walter D. van Suijlekom 研究下有界自伴卷积算子的最低简单偶基态，并在明确前件下证明其 Fourier 变换只有实零点；同时分析有限 Toeplitz 压缩和 spectral-action 型回声。

出处：Alain Connes, Walter D. van Suijlekom, “Quadratic Forms, Real Zeros and Echoes of the Spectral Action,” 2025, arXiv:2511.23257。

Alain Connes、Caterina Consani 与 Henri Moscovici 构造有限秩自伴扰动，其数值谱可逼近低位 zeta 零点。决定性缺口仍是有限对象向极限对象的严格收敛，以及相应行列式／谱函数与 completed zeta 或 $\Xi$ 的精确同一。

出处：Alain Connes, Caterina Consani, Henri Moscovici, “Zeta Spectral Triples,” 2025, arXiv:2511.22755。

综述出处：Alain Connes, “The Riemann Hypothesis: Past, Present and a Letter Through Time,” 2026, arXiv:2602.04022。

### 5. Li 系数的 2024–2026 状态

[literature-attested]

本次检索未找到一个获得广泛承认、并在 2024–2026 年改变 RH 证明状态的 Li 系数正性突破。近期最清楚的结构性前件仍包括 Suzuki 把 Li 系数表示成模型空间中具体函数范数的等价刻画：

出处：Masatoshi Suzuki, “Li coefficients as norms of functions in a model space,” 2023, arXiv:2301.05779。

2024 年有 Keiper–Li 系数的大规模数值计算与渐近调查，但有限个正系数不可能推出全部正性。对本仓更诚实的路线是先形式化：

- 前 $N$ 个 Li 系数的有限定义；
- 有理／区间算术证书；
- Li 核与 Weil 测试函数的有限恒等式；
- 明确写出“有限 $N$ 不蕴含 RH”。

结论：2024–2026 的真正进步重心主要在有限 Weil 压缩、谱／算子重述、尾项控制和比例定理，而不是已解决的 Li 全正性。

## 三、de Bruijn–Newman 常数

### 1. 已建立的区间

[literature-attested]

Brad Rodgers 与 Terence Tao 已证明

$\Lambda\ge0$。

出处：Brad Rodgers, Terence Tao, “The de Bruijn–Newman constant is non-negative,” 2018/2020, arXiv:1801.05914, Forum of Mathematics, Pi 8 (2020)。

D.H.J. Polymath 给出无条件上界

$\Lambda\le0.22$。

出处：D.H.J. Polymath, “Effective approximation of heat flow evolution of the Riemann $\xi$ function, and a new upper bound for the de Bruijn–Newman constant,” 2019, arXiv:1904.12438。

Dave Platt 与 Tim Trudgian 严格核验 RH 至高度 $3\cdot10^{12}$，并结合上述有效框架得到

$\Lambda\le0.2$。

出处：Dave Platt, Tim Trudgian, “The Riemann hypothesis is true up to $3\cdot10^{12}$,” 2020/2021, arXiv:2004.09765, Bulletin of the London Mathematical Society 53 (2021)。

因此截至 2026-08-30，保守、已建立的公开区间仍是

$0\le\Lambda\le0.2$。

由于 RH 等价于 $\Lambda\le0$，再结合 $\Lambda\ge0$，当前可写成：

$\mathrm{RH}\Longleftrightarrow\Lambda=0$。

### 2. 2026 年的候选改进

[literature-attested | public non-archival candidate]

Jude Gomila 在 2026-08-19 发布技术说明，声称通过计算机辅助证书把上界改进为

$\Lambda\le0.1787854$。

出处：Jude Gomila, “$\Lambda\le0.1787854$ — a new bound for the de Bruijn–Newman constant, explained,” 2026；arXiv 号检索未证实，期刊发表检索未证实。

裁决：该候选应进入“待复核外部证书”账，不应在开题卷中替换公认的 $0.2$。至少需要稳定论文版本、代码与证书哈希、独立复算、误差模型审计及同行评审状态。

### 3. 对黄金观察者线路的意义

de Bruijn–Newman 热流提供另一种“全局极限参数”。它警告本线：

- 有限高度的零点全部在线，不等于 $\Lambda=0$；
- 很小的正上界不等于零；
- 连续改进小数位可能有工程价值，但若没有新的定理级机制，就不构成通往 RH 的可证明边际进展。

## 四、随机矩阵与算术量子混沌

### 1. Pair correlation 的无条件进展

[literature-attested]

Siegfred Alan C. Baluyot、Daniel Alan Goldston、Ade Irma Suriajaya 与 Caroline L. Turnage-Butterbaugh 给出无条件 Montgomery 型 pair-correlation 定理。论文还说明，在额外薄盒或强零密度假设下，可取得至少约 $61.7\%$ 的简单零点比例，但该机制本身不把这些简单零点定位到临界线。

出处：Siegfred Alan C. Baluyot, Daniel Alan Goldston, Ade Irma Suriajaya, Caroline L. Turnage-Butterbaugh, “An unconditional Montgomery Theorem for Pair Correlation of Zeros of the Riemann Zeta Function,” 2023/2024, arXiv:2306.04799, Acta Arithmetica 214 (2024)。

Daniel Alan Goldston、Junghun Lee、Jordan Schettler 与 Ade Irma Suriajaya 在不预设 RH 的形式下研究 pair-correlation conjecture，并证明适当的完整 PCC 将推出渐近 $100\%$ 的零点既简单又在临界线。

出处：Daniel Alan Goldston, Junghun Lee, Jordan Schettler, Ade Irma Suriajaya, “Pair Correlation Conjecture for the Zeros of the Riemann Zeta-Function I: Simple and Critical Zeros,” 2025，2026 年修订，arXiv:2503.15449v4。

逻辑边界：密度 $100\%$ 仍允许密度零但无限的离线异常集，所以它仍弱于 RH。

### 2. CUE 矩与 zeta 矩的匹配

[literature-attested]

Alexander Grover、Francesco Mezzadri 与 Nick Simm 研究 CUE 特征多项式高阶导数矩，并与 zeta 导数矩对应；部分低阶结果无条件成立，更一般的移动矩在 Lindelöf 型条件下取得。

出处：Alexander Grover, Francesco Mezzadri, Nick Simm, “Higher order derivative moments of CUE characteristic polynomials and the Riemann zeta function,” 2026, arXiv:2604.03051。

这类结果强化 GUE/CUE 字典和算术量子混沌的统计可信度，但没有生成一个其自伴性能够强迫所有 zeta 零点实部为 $1/2$ 的算子。

### 3. 当前诚实定位

随机矩阵／量子混沌目前提供三种东西：

1. 局部间距、相关函数和矩的高精度预测；
2. 有限矩阵或有限压缩中天然实谱的模型；
3. 寻找 Hilbert–Pólya 算子的设计原则。

它目前没有提供：

1. completed zeta 与某个自伴算子的严格谱行列式同一；
2. 有限矩阵逼近向无界自伴算子的强 resolvent 收敛；
3. 排除极稀疏离线零点的全局机制。

因此本仓若消费此方向，应把目标写成“有限谱恒等式、收敛模式、误差界、行列式极限”，不能把数值谱吻合命名为 RH 证明。

## 五、形式化侧：Lean／mathlib 与外部项目

### 1. mathlib 的 zeta 基建

[literature-attested | official formal library]

当前 mathlib 的 `Mathlib.NumberTheory.LSeries.RiemannZeta` 已包括：

- `riemannZeta`；
- completed zeta 及去极点的 entire 版本 `completedRiemannZeta₀`；
- 在极点外的解析性／可微性；
- functional equation；
- 在 $\Re s>1$ 与 Dirichlet 级数的一致；
- 平凡零点、留数等基本结果；
- `RiemannHypothesis` 的正式命题定义。

其 RH 定义的实质是：若 $\zeta(s)=0$，且该零点不是负偶数平凡零点，也不是极点位置，则 $\Re s=1/2$。mathlib 形式化了命题和大量底层解析结构，没有证明该命题。

出处：Lean mathematical library, `Mathlib.NumberTheory.LSeries.RiemannZeta`, 2026 当前文档；无 arXiv 号。

David Loeffler 与 Michael Stoll 系统说明了 Lean 中 zeta 与 $L$-函数的形式化框架，包括 Dirichlet 算术级数、解析延拓、functional equation 及 RH 的形式陈述。

出处：David Loeffler, Michael Stoll, “Formalizing zeta and L-functions in Lean,” 2025, arXiv:2503.00959, Annals of Formalized Mathematics 1 (2025)。

重要缺口：普通 mathlib 并未提供一个本仓可直接调用、且规范与本仓完全一致的 canonical Guinand–Weil explicit formula／Weil positivity equivalence。

### 2. 本仓的 mathlib 接口状态

[repo-derived | GID: `D5/S3/Weil/Convention`]

该模块固定：

- 本仓 Fourier 采用 angular-frequency 规范；
- 与 mathlib 频率变量的换算含 $2\pi$；
- `criticalAbscissa := 1/2`；
- `classicalZeta := riemannZeta`。

它仍把

- `compactSupportFourierLaplaceEntireStatus`
- `canonicalWeilExplicitFormulaStatus`

标成 `.missing`。

与此同时，本仓后续模块已经有特定接口下的 `weil_explicit_formula`。这不应草率写成自相矛盾；更可能表示 `Convention` 账本所指的是更强、规范唯一的 canonical theorem。开工前应审计该状态字段究竟是否过期，还是刻意区分“特定桥接定理”与“规范公式”。

### 3. PrimeNumberTheoremAnd 的完成度

[literature-attested | public Lean repository]

`AlexKontorovich/PrimeNumberTheoremAnd` 的当前 `main` 中：

- `MediumPNT.lean` 可见最终 `MediumPNT` theorem；本次文件级检索未发现 `sorry`。其误差规模约为 $Y\exp(-(\log Y)^{1/10})$，属于已闭合的中等强度 PNT。
- `StrongPNT.lean` 至少仍有两个活 `sorry`，包括 `LogDerivZetaLogSquaredBoundSmallt`，以及 `I3NewBound` 附近的缺口。
- 因此，诚实状态是“MediumPNT 文件已闭合；原来的 classical strong-error 目标在该仓主线中未完成”，而不是给出一个没有语义的完成百分比。

项目出处：Alex Kontorovich et al., `PrimeNumberTheoremAnd`, GitHub public repository；论文／统一 arXiv 号检索未证实。

另有独立仓库 `math-inc/strongpnt` 自述包含约 25,000 行、约 1,100 个 lemma、无 `sorry` 的 AI 生成 strong-PNT 形式化。它不是 `PrimeNumberTheoremAnd/main` 的完成证据；在独立构建、依赖固定和 `#print axioms` 审计前，只能写“项目自述已完成”。

### 4. RH 及相邻结果的形式化尝试

[literature-attested]

- `AlexKontorovich/Lean-RH`：Brandon Gomes 与 Alex Kontorovich 的 “Riemann Hypothesis in Lean (with or without mathlib)” 仓库，重点是用 Dirichlet eta／zeta 接口精确陈述 RH，并比较独立公理化与 mathlib 版本；不是 RH 证明。arXiv 号检索未证实。
- `anthropics/zeta-23-lean`：公开宣称形式化 Alpöge–Furman 2026 比例定理。应固定 commit 后核对最终导出 theorem 与常数。
- 本仓 `D5/S3/Weil/ZetaBridge/ClassicExplicitFormula.lean` 已导入 `Zeta23`，说明本仓已在消费相邻外部形式化，但该依赖的来源 commit、导出 API 与 axioms 应进入固定账。
- 本次检索未发现一个获得公认、完整 kernel-checked 的 RH 证明；凡声称“Lean 已证明 RH”的材料，若不能给出可构建源树、无 `sorry`／自定义不受控公理审计和准确 theorem statement，均不得进入 literature-attested 栏。

# 第二部　黄金观察者路线的批判性评估

## 一、开放心脏与现有内核究竟说了什么

### 1. O-5 的实际 Lean 陈述

[repo-derived | GID: `D5/X_Frontier/Hearts`]

仓库定义：

- $\phi=(1+\sqrt5)/2$；
- `structuralPole := 1 / phi ^ 3`；
- `structuralZero := 1 / (2 * phi ^ 2)`；
- `eulerGerm` 为黄金 Beatty／指数层构造的 Euler germ。

唯一 `sorry` 是 `o5_independence`，其命题要求存在 $Z_{\rm qc}$，满足：

1. $Z_{\rm qc}$ 在 $\Re s>0$ 上亚纯；
2. 当 $\Re s>1/\phi^2$ 时，$Z_{\rm qc}(s)=\texttt{eulerGerm}(s)$；
3. 若
   $1/(2\phi^3)<\Re s<1/\phi^2$，
   且 $Z_{\rm qc}$ 在 $s$ 解析并且 $Z_{\rm qc}(s)=0$，
   则
   $\Re s=1/(2\phi^2)$。

必须指出：该 theorem 没有断言 `structuralPole` 真的是极点。`structuralPole` 在心脏中只是定义；极点结论目前只存在于理论卷的因子分解叙述中。

另一个形式化风险是：Lean 中的无限乘积和无限和是全定义对象。`eulerGerm` 作为函数可被定义，不自动意味着其在种子半平面收敛、解析或等于任何 Euler product。O-5 存在性不能靠“定义已通过类型检查”取得。

### 2. O-6 的实际 Lean 陈述

[repo-derived | GID: `D5/X_Frontier/Hearts`]

`o6WeilPositivityStatement` 目前是一个 `def : Prop`，而不是已证 theorem：

$ \forall Z\,g\,h_{\rm conv},\quad
   \Re\operatorname{zeroSum}(Z,g*\widetilde g,h_{\rm conv})\ge0.$

其中：

- $Z:\texttt{ZeroData}$；
- $g:\texttt{WeilTestFunction}$；
- `hZero : SymmetricConvergent Z (convolutionSquare g)`。

它看起来像 Weil 1952 的卷积平方正性，但目前没有 kernel theorem 证明

$\mathrm{RH}\Longleftrightarrow\texttt{o6WeilPositivityStatement}$。

## 二、O-5 与经典 RH：三层答案，而不是一个“是／否”

### 1. 纯 kernel 层答案：当前没有等价定理

[repo-derived]

当前 Lean DAG 中：

- 没有 `o5_independence → RiemannHypothesis`；
- 没有 `RiemannHypothesis → o5_independence`；
- 没有把 `eulerGerm` 与 completed zeta 因子严格连接的 theorem。

因此在内核事实层，O-5 与 RH 是两个尚未形式连接的命题。“independence” 是路线命名，不是已证明的逻辑独立性；没有任何 ZFC／Lean 基础中的独立性结论。

### 2. 理论卷层答案：零点定位部分被设计成 RH 等价形

[repo-derived | path: `docs/develop/theory/PZG_BEDC.md` | GID: not present]

该理论卷的命题 6.19 声称在

$\Re s>1/(2\phi^3)$

有因子分解

$Z_{\rm qc}(s)
 =\zeta(\phi^2s)\,
  \zeta(\phi^3s)\,
  \zeta(2\phi^2s)^{-1}\,
  e^{H_2(s)},$

其中 $H_2$ 绝对收敛。

命题 6.20 由此识别：

- 结构零点 $s_*=1/(2\phi^2)$；
- 结构极点 $p_*=1/\phi^3$。

命题 6.31 给出 divisor order 恒等式：

$\operatorname{ord}_{s_0}Z_{\rm qc}
 =\operatorname{ord}_{\phi^2s_0}\zeta
 +\operatorname{ord}_{\phi^3s_0}\zeta
 -\operatorname{ord}_{2\phi^2s_0}\zeta.$

命题 6.32 与勘误 E3 明确主张：该截段零点定位不是 RH 的弱形，而是经 functional equation 反射和无消去分析后与完整 RH 等价。

关键纪律：这些是理论卷命题，不是 Lean kernel theorem。它们是 O-5 路线的数学蓝图，不是仓库已冻结事实。

### 3. 全 O-5 不是“仅仅 RH”

即使上述因子分解及无消去逻辑正确，O-5 心脏还要求：

$Z_{\rm qc}\text{ 在整个 }\Re s>0\text{ 上亚纯。}$

而理论卷给出的因子分解窗口只到

$\Re s>1/(2\phi^3)$。

因此最诚实的分类是：

- O-5 的“窗口内零点定位”部分：在理论卷因子分解成立后，设计目标是与 RH 等价；
- O-5 的完整 Lean 命题：等于上述定位义务，再加一项继续到 $\Re s>0$ 的额外亚纯延拓义务；
- 除非额外延拓能由独立、无 RH 的定理得到，否则完整 O-5 不能直接称为“RH 的等价改写”；
- 它也不是一个已证明的“弱 RH”。

## 三、$\phi$ 结构如何映到临界线语言

### 1. 数值几何

$\phi\approx1.618034$，

$1/\phi^2\approx0.381966$，

$1/\phi^3\approx0.236068$，

$1/(2\phi^2)\approx0.190983$，

$1/(2\phi^3)\approx0.118034$。

O-5 的严格窗口是：

$1/(2\phi^3)<\Re s<1/\phi^2$。

### 2. 自然缩放不是把结构极点送到 $1$，而是把 germ 的收敛边送到 $1$

[suspected-novel | repo-specific synthesis]

取自然坐标

$w=\phi^2s$。

则：

| 黄金 $s$-坐标 | $w=\phi^2s$ | zeta 语言 |
|---|---:|---|
| 上边界 $1/\phi^2$ | $1$ | $\zeta(w)$ 的经典极点边 |
| 结构极点 $1/\phi^3$ | $1/\phi$ | $\zeta(\phi w)$ 的极点 |
| 结构零点 $1/(2\phi^2)$ | $1/2$ | 临界线及 $1/\zeta(2w)$ 的结构零 |
| 下边界 $1/(2\phi^3)$ | $1/(2\phi)$ | $\zeta(\phi w)$ 的临界线 |

理论卷因子分解变为

$Z_{\rm qc}(w/\phi^2)
 =\zeta(w)\,
  \zeta(\phi w)\,
  \zeta(2w)^{-1}\,
  e^{H_2(w/\phi^2)}.$

这解释了为什么结构极点不应被强行映到 $1$：它不是第一尺度 $\zeta(w)$ 的极点，而是第二尺度 $\zeta(\phi w)$ 的极点。黄金结构本质上是两个 zeta 尺度 $w$ 与 $\phi w$，再加一个 doubling 尺度 $2w$。

### 3. 条件等价的直接零点论证

假定上述因子分解、亚纯阶数规则和指数因子非零已经形式化。

若 RH 成立：

- $\zeta(w)$ 在窗口内部的非平凡零点只能有 $\Re w=1/2$；
- $\zeta(\phi w)$ 的 RH 临界线是 $\Re w=1/(2\phi)$，恰是严格窗口的下边界，不在内部；
- $1/\zeta(2w)$ 的结构零来自 $\zeta(2w)$ 在 $2w=1$ 的极点，即 $w=1/2$；
- 在 RH 下，$\zeta(2w)$ 的非平凡零点对应 $\Re w=1/4$，位于窗口下方，只会在更左区域制造极点。

故窗口内解析零点只能落在 $\Re w=1/2$，即

$\Re s=1/(2\phi^2)$。

反之若 RH 假：

- 由 functional equation 与共轭对称，可选一个非平凡零点 $\rho$ 满足 $\Re\rho>1/2$；
- 令 $s=\rho/\phi^2$，则 $w=\rho$ 位于 O-5 的严格窗口；
- $\zeta(w)=0$；
- 因 $\Re(2\rho)>1$，Euler product 区域给出 $\zeta(2\rho)\ne0$，所以分母不能消去该零；
- $e^{H_2}$ 不为零；
- $\zeta(\phi\rho)$ 在该点没有极点。

于是 $Z_{\rm qc}(s)=0$，但 $\Re s\ne1/(2\phi^2)$，违反 O-5 定位。

这给出理论层最短的“定位部分 $\Longleftrightarrow$ RH”证明路线。正式 Lean 证明仍应使用 `meromorphicOrderAt`／divisor order，而不能在可能为零或极点的点上作非受控除法。

### 4. 其他变换为什么不是主坐标

缩放 $w=\phi^3s$ 会把结构极点送到 $1$，却把结构零线送到 $\phi/2$，不是 $1/2$。

不存在一个纯缩放同时满足

$p_*=1/\phi^3\mapsto1$，

$s_*=1/(2\phi^2)\mapsto1/2$，

因为

$s_*/p_*=\phi/2\ne1/2$。

确实存在仿射变换

$T(s)=\phi^5s-\phi$

同时把 $p_*$ 送到 $1$、把 $s_*$ 送到 $1/2$；但它把 germ 上边界 $1/\phi^2$ 送到 $\phi^2$，并破坏 Euler 因子中的纯尺度关系。除非另有定理运输 functional equation、Dirichlet 系数和 divisor，不能只凭“几何上对齐”使用该仿射坐标。

### 5. 黄金谱参数

[suspected-novel | repo-specific synthesis]

定义

$\gamma_\phi(s):=-i(\phi^2s-1/2)$。

则

$\Im\gamma_\phi(s)=0
 \Longleftrightarrow
 \Re s=1/(2\phi^2)$。

这正是仓库经典定义

$\operatorname{spectralParameter}(\rho)=-i(\rho-1/2)$

在缩放 $w=\phi^2s$ 下的拉回。它是把 O-5 接入现有 `CriticalLine`、`ZeroSum` 和 off-line orbit API 的自然接口。

## 四、O-6 作为经典 Weil 路线：可达部分与真正硬核

### 1. 已有冻结基建

[repo-derived | selected frozen GIDs]

- `D5/S3/Weil/TestFunctions`：偶、复值、$C^\infty$、紧支撑测试函数及卷积平方。
- `D5/S3/Weil/FourierLaplace`：Fourier–Laplace 变换和对称性。
- `D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity`：
  `fourierLaplace_convolutionSquare_real` 与
  `fourierLaplace_convolutionSquare_real_nonnegative`。
- `D5/S3/Weil/ZeroSum`：非平凡零点、谱参数、`ZeroData`、有限对称截断、`SymmetricConvergent` 与 `zeroSum`。
- `D5/S3/Weil/ZetaBridge/ClassicExplicitFormula`：特定接口下的 `weil_explicit_formula`。
- `D5/S3/Weil/WeilIdentity`：显式公式和两种重排；注释标记 D5-T0018-F 已 discharge。
- `D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine`：
  临界线单项非负、有限截断和非负及 critical/off-line 分裂。
- `D5/S3/Weil/ZetaBridge/ConvolutionSquareOffLineOrbits`：
  四点离线轨道贡献为实数；没有证明其为负。
- `D5/S3/Weil/ZetaBridge/PrimeArchimedeanEnergyIdentity`：
  把零点侧卷积平方能量改写为极点／边界项、archimedean jump、算术 jump 与 coherent mass 阈值，正性等价于一种 prime–archimedean Poincaré 型不等式。

这些结果不应重证。新增工作必须组合它们。

### 2. 第一处语义缺口：`ZeroData` 可能没有 inhabitant

[repo-derived | GID: `D5/S3/Weil/ZeroSum`]

`ZeroData` 要求：

- 无重复、穷尽全部非平凡零点的枚举；
- 重数；
- functional-equation／共轭闭包；
- 局部有限性。

文件明确写明：“No inhabitant is asserted here.”

故当前只能说：

- `ZeroData` 并未被证明为空；
- 也未被证明非空；
- 若它为空，则 O-6 的外层全称量化自动成立。

因此心脏注释中任何“非空洞”语义都尚未由 kernel 支持。形式命题闭合与数学非空洞是两件事。

### 3. 第二处语义缺口：收敛前件按测试函数逐个外置

O-6 只对带有

`hZero : SymmetricConvergent Z (convolutionSquare g)`

的实例提出非负义务。若某个 $g$ 没有已构造的收敛见证，该 $g$ 不会反驳 O-6。

经典 Weil 判据需要证明所选完整测试类的零点和确实存在，并且与显式公式的规范极限一致。当前 `Convention` 仍把“紧支撑 Fourier–Laplace entire 性”的 canonical status 标成 missing，这个缺口不能靠给 theorem 多加一个 `hZero` 参数永久绕开。

### 4. 第三处语义缺口：测试类是否足够完备

本仓 `WeilTestFunction` 本身已经要求偶性，O-6 再只测试其 `convolutionSquare`。经典文献常从更一般的 hermitian 测试代数出发。

必须单独证明：

- 任意经典 admissible 正型测试能否由本仓偶测试函数卷积平方逼近或表示；
- 对称化是否不损失检测离线轨道的能力；
- 本仓 angular-frequency 规范与经典 Mellin／Fourier 规范精确一致。

在该密度／因子分解定理完成前，不能直接把 O-6 命名为“经典 Weil 判据本身”。

### 5. 正向方向：RH 推 O-6，近期可达

若 RH 成立，则每个 `ZeroData.zero n` 的实部为 $1/2$。冻结模块已经证明每个临界线卷积平方项为实且非负，也证明相应有限截断和非负。由 `SymmetricConvergent` 把有限非负实部的极限送入闭集 $[0,\infty)$，即可得到 O-6。

这个方向：

- 不需要测度；
- 不需要新显式公式；
- 不需要构造离线分离函数；
- 数学内容主要是有限和与极限的闭性。

它是近期最诚实的 O-6 theorem。

### 6. 反向方向：O-6 推 RH，是经典难核

若有离线零点，`ConvolutionSquareOffLineOrbits` 目前只告诉我们四点轨道总贡献为实数，不告诉我们它必为负。要从离线轨道制造 O-6 反例，需要：

1. 构造紧支撑平滑 $g$；
2. 使 $g*\widetilde g$ 在目标离线轨道上产生可控负方向；
3. 同时控制所有其他零点、极点、素数项和 archimedean 项；
4. 证明本仓受限测试类对该方向足够稠密；
5. 通过无限零点和的收敛／截断极限。

这就是 Weil 等价的 hard separator theorem。它不是“再加几个 positivity lemma”即可完成的工程尾项。

## 五、O-5 与 O-6 的依赖关系，以及先证哪个

### 1. 当前 Lean DAG

两条心脏当前没有 kernel 依赖：

- O-5 不消费 O-6；
- O-6 不消费 O-5；
- PZG 理论卷中的因子分解尚未成为桥接 GID。

因此不能写“O-5 是 O-6 的 lemma”或“O-6 已由 O-5 化约”。

### 2. 数学角色

- O-6 是经典 zeta 的直接 Weil 路线，消费现有约 197 模块和最新有限压缩文献。
- O-5 是黄金 Euler germ 的控制实验。它只有在因子分解正式建立后，才把其窗口零点命题接回经典 RH。
- O-5 的完整延拓区域比其 RH 等价窗口更大，因此它带有额外负担。
- O-5 不能替代 O-6 的测试函数完备性或 off-line separator；O-6 也不能自动构造黄金 germ 的亚纯延拓。

### 3. 推荐顺序

编译顺序与科学接受顺序必须分开：

1. 立即关闭黄金坐标的有限代数义务 R-A、R-B、R-C。
2. 立即关闭 O-6 空洞性诊断 R-D 与 RH 定位 lemma R-E。
3. 构造 canonical `ZeroData` 和至少一个实际卷积平方收敛见证；在此之前不得宣传 O-6 “非空洞闭合”。
4. 再接受 R-F：RH $\Rightarrow$ O-6。
5. 推进有限窗口 PSD、Galerkin 字典和尾项预算。
6. 并行形式化 PZG 命题 6.19、6.31、6.32，决定 O-5 定位部分能否真正化为 RH。
7. O-6 反向 separator 与 O-5 的 $\Re s>0$ 全延拓均保持远期 open。

主线应是 O-6 基建；O-5 桥接是并行控制线。原因不是 O-5“不重要”，而是 O-6 已有冻结消费者、近期文献接口和可闭合的一向定理，而 O-5 的核心等式仍停留在理论卷。

# 第三部　形式化线路图

## 一、架构纪律

### 1. 新模块落点

不应把依赖 `D5/X_Frontier/Hearts` 的 theorem 回写到冻结的 `D5/S3/Weil` 下，否则会倒置层级。拟议落点：

`D5/X_Frontier/GoldenObserver/`

定义统一放在：

`D5/X_Frontier/GoldenObserver/Core.lean`

R-A—R-F 每条恰有一个 public theorem、一个模块、一个稳定 GID。可使用同模块 private lemma，但不得另导出平行 API。

### 2. 定义 Core

拟议 GID：`D5/X_Frontier/GoldenObserver/Core`

该文件只放定义，不放 theorem：

    import D5.X_Frontier.Hearts

    namespace D5.X_Frontier.GoldenObserver

    open D5.X_Frontier.Hearts

    noncomputable def goldenNaturalScale (s : ℂ) : ℂ :=
      (((phi ^ 2 : ℝ) : ℂ) * s)

    noncomputable def goldenSpectralParameter (s : ℂ) : ℂ :=
      -Complex.I * (goldenNaturalScale s - (1 : ℂ) / 2)

    end D5.X_Frontier.GoldenObserver

不另定义第二套 `phi`、`structuralZero` 或 critical-line 谓词。

## 二、近期 elementary 义务波 R-A—R-F

以下是拟议的精确声明类型，不是已构建代码。每条都必须以仓库构建、无 `sorry`、`#print axioms` 不含 `sorryAx` 为准。

### R-A　自然缩放命中临界半线

[suspected-novel | proposed GID: `D5/X_Frontier/GoldenObserver/GoldenNaturalScale`]

    import D5.X_Frontier.GoldenObserver.Core

    namespace D5.X_Frontier.GoldenObserver

    open D5.X_Frontier.Hearts

    theorem golden_natural_scale_hits_half :
        goldenNaturalScale (structuralZero : ℂ) = (1 : ℂ) / 2

    end D5.X_Frontier.GoldenObserver

闭合性质：

- 纯 $\sqrt5$ 与域代数；
- 无测度、级数、拓扑或 zeta；
- 可由 $\phi^2=\phi+1$、$\phi\ne0$ 和 `field_simp`／`nlinarith` 闭合。

消费者：R-C 与中期黄金因子分解字典。

### R-B　黄金窗口的严格次序

[suspected-novel | proposed GID: `D5/X_Frontier/GoldenObserver/GoldenBandOrder`]

    import D5.X_Frontier.Hearts

    namespace D5.X_Frontier.GoldenObserver

    open D5.X_Frontier.Hearts

    theorem golden_band_order :
        1 / (2 * phi ^ 3) < structuralZero ∧
        structuralZero < structuralPole ∧
        structuralPole < 1 / phi ^ 2

    end D5.X_Frontier.GoldenObserver

闭合性质：

- 先证明 $2<\sqrt5<3$，继而 $1<\phi<2$；
- 纯有序域运算；
- 不使用 O-5 `sorry`。

消费者：因子分解域包含关系、结构极点与严格窗口定位。

### R-C　黄金谱参数的实谱等价

[suspected-novel | proposed GID: `D5/X_Frontier/GoldenObserver/GoldenSpectralCoordinate`]

    import D5.X_Frontier.GoldenObserver.GoldenNaturalScale

    namespace D5.X_Frontier.GoldenObserver

    open D5.X_Frontier.Hearts

    theorem golden_spectral_im_eq_zero_iff (s : ℂ) :
        (goldenSpectralParameter s).im = 0 ↔
          s.re = structuralZero

    end D5.X_Frontier.GoldenObserver

闭合性质：

- 展开复乘法和虚部；
- 调用 R-A 或等价实代数；
- 不重新证明经典 `spectralParameter` 定理。

消费者：把 O-5 线运输到现有 `CriticalLine` 和 off-line orbit 语言。

### R-D　O-6 空类型诊断

[repo-audit proposition | proposed GID: `D5/X_Frontier/GoldenObserver/ZeroDataVacuityAudit`]

    import D5.X_Frontier.Hearts

    namespace D5.X_Frontier.GoldenObserver

    open D5.X_Frontier.Hearts
    open D5.S3.Weil.ZeroSum

    theorem o6_vacuous_if_zeroData_empty
        (h : ¬ Nonempty ZeroData) :
        o6WeilPositivityStatement

    end D5.X_Frontier.GoldenObserver

精确证明只有命题逻辑：

- 展开 O-6；
- 对任意 $Z$，由 $h\langle Z\rangle$ 导出矛盾；
- 从矛盾消去。

它不证明 `ZeroData` 为空，也不反驳 O-6。它只把当前编码的空洞风险变成 kernel-visible 事实。

消费者：O-6 nonvacuity CI gate。若没有机器门要求后续同时导入 `canonicalZeroData_nonempty`，该 wrapper 没有可达消费者，不应进入冻结层。

### R-E　RH 将任意 `ZeroData` 零点定位到临界线

[repo-derived composition | proposed GID: `D5/X_Frontier/GoldenObserver/RhLocatesZeroData`]

    import D5.X_Frontier.Hearts

    namespace D5.X_Frontier.GoldenObserver

    open D5.S3.Weil.Convention
    open D5.S3.Weil.ZeroSum

    theorem zeroData_zero_on_critical_line_of_rh
        (hRH : RiemannHypothesis)
        (Z : ZeroData)
        (n : ℕ) :
        (Z.zero n).re = criticalAbscissa

    end D5.X_Frontier.GoldenObserver

闭合路线：

- `Z.zero_isNontrivial n` 给出该点是 zeta 非平凡零点；
- 排除负偶数平凡零点和 $s=1$；
- 直接应用 mathlib 的 `RiemannHypothesis` 定义；
- 不调用显式公式或零点计数。

消费者：R-F。

### R-F　RH 推出本仓 O-6

[repo-derived composition | proposed GID: `D5/X_Frontier/GoldenObserver/RhImpliesO6`]

    import D5.X_Frontier.GoldenObserver.RhLocatesZeroData
    import D5.S3.Weil.ZetaBridge.ConvolutionSquareCriticalLine

    namespace D5.X_Frontier.GoldenObserver

    open D5.X_Frontier.Hearts
    open D5.S3.Weil.TestFunctions
    open D5.S3.Weil.ZeroSum

    theorem riemannHypothesis_implies_o6WeilPositivityStatement :
        RiemannHypothesis → o6WeilPositivityStatement

    end D5.X_Frontier.GoldenObserver

闭合路线：

1. 固定 $Z,g,h_{\rm conv}$；
2. 用 R-E 把每个枚举零点定位到 $\Re\rho=1/2$；
3. 复用
   `critical_line_zero_summand_real_nonnegative`
   和
   `truncatedCriticalConvolutionSquareSum_re_nonnegative`；
4. 证明一般对称截断与临界截断在 RH 下相等；
5. 由 `SymmetricConvergent` 取得复极限；
6. 对实部取极限，使用闭集 $[0,\infty)$。

允许在同模块加入 private 的有限和重写和闭集极限 lemma，但不得导出第二条公开 theorem。

科学接受门：R-F 即使在 `ZeroData` 空时也能形式成立。仓库不得在 canonical `ZeroData` inhabitant 和至少一条实际收敛路线完成前把它宣传为“非空洞的 Weil 正性结果”。

## 三、近期义务波的统一验收

R-A—R-F 每条必须满足：

1. 一个 public theorem、一个模块、一个稳定拟议 GID；
2. 不调用 `o5_independence`；
3. `#print axioms` 不出现 `sorryAx` 或新自定义 axiom；
4. 不增加测度前件；
5. 不私自给 `ZeroData` 增加 `[Nonempty ZeroData]` 或 `[Fintype ...]`；
6. 不复制冻结模块已有 theorem；
7. 在提交说明中写出唯一消费者；
8. 声明固定后若需改变数学内容，新开 GID，不原地漂移；
9. 若实际 API 证明 R-F 需要新的全局解析定理，则 R-F 从“近期 elementary”降级，不用 `sorry` 强行维持计划。

## 四、中期里程碑

### M1　Canonical `ZeroData` 与非空洞性

目标不是选取前 $N$ 个已知零点，而是构造满足当前 structure 的全枚举：

- 证明非平凡零点集合可数；
- 构造无重复穷尽枚举；
- 定义解析重数；
- 证明共轭与 $1-\rho$ 闭包；
- 从零点离散性／Riemann–von Mangoldt 基建取得局部有限性；
- 给出

    theorem canonicalZeroData_nonempty :
        Nonempty ZeroData

该工作消费 `ZetaRvm`、`ZetaExplicit/ZeroSummability` 和 mathlib 解析零点 API。它不是 R-A—R-F 的 elementary 波，应单列预算。

### M2　枚举不变性与卷积平方收敛

需要证明：

- 任意两个 `ZeroData` 对同一内在零点多重集给出相同有限 cutoff 和；
- `zeroSum` 与枚举选择无关；
- 每个 admissible `convolutionSquare g` 都有 canonical `SymmetricConvergent`；
- 零点和与 `weil_explicit_formula` 使用相同截断规范。

完成后，O-6 中的 `hZero` 才能从“调用者任选前件”逐步移至可派生事实。

### M3　精确 Weil 判据

分为两向：

- 已规划：RH $\Rightarrow$ O-6；
- 真正 open：O-6 $\Rightarrow$ RH。

反向所需的公开目标应先固定为一个 separator theorem，而不是直接打开 RH：

    theorem offLineZero_yields_negative_weil_square
        (Z : ZeroData)
        (hOff : ∃ n, (Z.zero n).re ≠ criticalAbscissa) :
        ∃ g : WeilTestFunction,
          ∃ hZero : SymmetricConvergent Z (convolutionSquare g),
            (zeroSum Z (convolutionSquare g) hZero).re < 0

该声明不是近期义务；它把难核准确暴露出来。若本仓偶卷积平方测试类不足，该 theorem 可能为假，必须先修正测试代数，而不是无限调 tactic。

### M4　受限测试类的有限 PSD 计划

建立参数化对象 `WeilWindow L`，依次完成：

1. 有限基、有限 Galerkin matrix；
2. 二次型恒等式；
3. 矩阵 PSD 与受限测试类正性的等价；
4. 有理或区间 LDL／Cholesky 证书；
5. archimedean 尾项和零点截断误差；
6. $N,T,L$ 改变时的单调性或显式非单调性。

移植 Chuk／Groskin 前先固定：

- angular frequency 还是 ordinary frequency；
- $2\pi$ 因子；
- Fourier 变换号号；
- completed zeta／gamma 因子；
- 零点按重数还是按不同点计数；
- 窗口参数 $L$ 的定义。

任何一个规范未桥接，都不得把外部矩阵证书直接解释成本仓 O-6 证书。

### M5　黄金 germ 与 completed zeta 的桥

按以下顺序，不跳步：

1. 证明 `eulerGerm` 在 $\Re s>1/\phi^2$ 的收敛和解析性；
2. 形式化 Beatty／指数计数重组；
3. 在 $\Re s>1/(2\phi^3)$ 证明 PZG 命题 6.19 的因子分解；
4. 形式化 $H_2$ 的绝对／局部一致收敛和 $e^{H_2}\ne0$；
5. 用 meromorphic order 证明命题 6.31；
6. 在严格窗口中证明无消去；
7. 得到“窗口零点定位 $\Longleftrightarrow$ RH”；
8. 最后单独研究从 $1/(2\phi^3)$ 向 $\Re s>0$ 的亚纯延拓。

若希望 heart 同时断言结构极点，应新增 O-5′ GID，例如显式加入

$\operatorname{ord}_{1/\phi^3}Z_{\rm qc}=-1$，

而不是修改原 O-5 statement。

### M6　有限 Li 正性层

先做有限对象：

- completed $\xi$ 的导数／Taylor API；
- $\lambda_n$ 的有限定义；
- 前 $N$ 个 Li 系数的 exact arithmetic 或 interval certificate；
- Li 核与有限 Weil Gram matrix 的恒等式；
- 明确 theorem 名称含 `upTo N`，禁止省略有限性。

全体 $n$ 的正性继续标记 RH-level open。

### M7　黄金 germ 的零点计数

不能直接把经典 `ZetaRvm` 名字替换成 `eulerGerm`。需要重新证明：

- 解析／亚纯函数的阶与增长；
- 边界上的非零性；
- argument-principle contour 合法性；
- 极点和结构零点的计数；
- 因子分解所诱导的零点计数关系。

在因子分解已证明的窗口内可以拉回经典计数；窗口外没有自动运输。

### M8　外部形式化消费

对 `Zeta23`、`zeta-23-lean`、`strongpnt` 等依赖采用：

- 精确 commit；
- source tree digest；
- Lean 与 mathlib 版本；
- 成功构建记录；
- 最终 theorem 的完整类型；
- `#print axioms`；
- 与本仓计数规范的桥 theorem。

外部仓 README 不得作为 theorem witness。

## 五、远期诚实 open

### 1. 全局 O-6 反向

这与经典 RH hard core 同级。有限矩阵、有限窗口、有限高度和比例定理都不能自动给出 separator。

### 2. O-5 的全半平面延拓

PZG 因子分解即使在 $\Re s>1/(2\phi^3)$ 完全正确，也没有解决 $\Re s>0$ 的全部延拓。自然边界、额外奇点或因子重组失败都必须由定理排除。

### 3. 有限窗口到全部测试函数

不能由“对一串 $L$ 证了 PSD”归纳出所有 $L$。Chuk 报告的极小谱隙说明，纯数值外推尤其危险。

### 4. Hilbert–Pólya 极限

必须证明：

- 真实 Hilbert 空间；
- 稠密定义域；
- 闭／本质自伴；
- resolvent 或谱测度收敛；
- 行列式与 $\Xi$ 的严格同一。

低位谱拟合不承担这些义务。

### 5. de Bruijn–Newman

$\Lambda=0$ 仍 open。把 $0.2$ 改到 $0.1787854$，即使候选最终成立，也不是证明零。

### 6. Gödel 边界

目前没有公认 theorem 证明 RH 独立于 ZFC、Lean 所用基础或其他标准基础系统。Gödel 不完备性只说明足够强的一致可递归理论存在不可判定句；它不说明 RH 就是其中之一。

因此：

- 不得把“可能独立”用作未证明分析步骤的豁免；
- Lean 只能核查从声明公理到结论的推演；
- 若未来真有 RH 独立性 theorem，那将改变基础论定位；当前没有这项结果；
- “数学很难”与“形式系统原则上不可证明”是不同命题。

# 第四部　与 DECT、GFPT 的接口及 suspected-novel 账

## 一、DECT：路线、前视承诺与预算包络

[repo-derived | path: `docs/develop/theory/DEFINITION_ESCAPE_COMPLETION_THEORY.md` | GID: not present]

DECT 是 Definition-Escape Completion Theory。其适用于本线的核心不是口号，而是：

- 先固定定义语言 $\Gamma$；
- 先固定目标、收益坐标、预算与停止条件；
- 不在看到失败后重写成功标准；
- 当固定语言的 blind kernel 阻止前进时，换 $\Gamma$，而不是在同一坐标中无限投入。

### 1. 路线注册表

建议预注册五条 $\Gamma$：

- $\Gamma_{\rm Weil}$：全测试类 Weil criterion 与 separator；
- $\Gamma_{\rm finitePSD}$：有限窗口、Galerkin、尾项和可认证 PSD；
- $\Gamma_{\rm Li}$：有限 Li 系数与 Weil–Li 字典；
- $\Gamma_{\rm spectral}$：自伴算子、resolvent、谱行列式；
- $\Gamma_{\rm golden}$：黄金 germ 因子分解、divisor 与延拓。

路线切换不是失败掩饰。每条路线必须保留其已得 theorem、反例、误差证书和不可达理由。

### 2. 预注册进度向量

[suspected-novel]

使用定理级而不是“投入小时数”的进度向量：

$P=
(N_{\rm closed},
 V_{\rm ZeroData},
 C_{\rm conv},
 L_{\max}^{\rm cert},
 B_T,
 \delta_{\rm PSD},
 A_{\rm external})$，

其中：

- $N_{\rm closed}$：新增且有消费者的 kernel GID 数；
- $V_{\rm ZeroData}\in\{0,1\}$：canonical inhabitant 是否已闭合；
- $C_{\rm conv}$：已有 canonical convergence 的测试子类覆盖；
- $L_{\max}^{\rm cert}$：在固定规范下取得严格证书的最大窗口；
- $B_T$：预注册 $(N,T,L)$ 下的尾项上界；
- $\delta_{\rm PSD}$：经区间证书得到的最小谱隙下界；
- $A_{\rm external}$：已固定、构建并完成 axioms 审计的外部 theorem 数。

不得在结果出来后把“多算了若干位”新增为成功坐标。

### 3. 初始预算包络

[suspected-novel]

义务波 E0：

- 至多 1 个 definitions-only Core 文件；
- 恰好 6 个 public theorem 模块 R-A—R-F；
- 0 个新 axiom；
- 0 个测度依赖；
- 0 次外部依赖升级；
- 0 次修改 `Hearts.lean`；
- 失败输出必须是缺失 API、反例或 statement 修订建议，不得留 `sorry`。

义务波 E1：

- 目标只限 canonical `ZeroData`、非空洞性和枚举不变性；
- 若局部有限性需要本仓尚无的全局零点计数 theorem，则停止 E1，把缺口移至中期 analytic 账；
- 不把前若干已计算零点包装成全体 `ZeroData`。

有限窗口波 F：

- 在计算前冻结 $(L,N,T)$、基、规范和容许误差；
- 只接受 exact rational 或 outward-rounded interval certificate；
- 数值失败后不得缩小窗口并仍称原目标成功；
- 每次扩大 $L$ 必须同时报告 $\delta_{\rm PSD}$ 与 $B_T$。

黄金桥波 G：

- 第一门是 factorization；
- 第二门是 divisor order；
- 第三门才是 RH 等价定位；
- 若有限 Euler 系数在预注册阶数内不匹配，立即冻结反例并停止，不以重定义 `eulerGerm` 消除差异。

### 4. 停止与换 $\Gamma$

出现任一条件即停止当前路线的下一轮同类投入：

1. 连续两个冻结波没有任何 theorem 状态从 open 变为 closed；
2. 只增加小数位，没有增加 $L$、降低可证明尾项或关闭逻辑缺口；
3. 同一缺失 lemma 已被三个下游模块分别局部假设；
4. 为通过测试而修改测试类、窗口或规范；
5. 外部依赖的最终 theorem 类型无法固定；
6. 当前语言的 blind kernel 已被反例证明非空。

停止后允许换 $\Gamma$，但必须保留原路线的失败证书。重新开放只允许基于：

- 新发表 theorem；
- 新的正式 API；
- 已预注册阈值被跨越；
- 原反例前件被一个独立 theorem 排除。

## 二、GFPT：治理不动点接口

[repo-derived | path: `docs/develop/theory/GOVERNANCE_FIXED_POINT_THEORY.md` | GID: not present]

GFPT 是 Governance Fixed-Point Theory，v1.0，2026-08-29。其 G-A—G-H 当前均为 open，不能把理论卷中的 theorem skeleton 冒充 kernel 事实。

对本线最重要的三条纪律是：

1. 当前状态是派生输出坐标，不得成为自身派生输入；
2. 地址漂移是表示事件，不是旧真值的重新裁决；
3. 规则合取封死合法修复时，增加窄、类型化通道，不改写旧规则的放行集。

### 1. 前视声明

每个 R／M 义务在证明搜索前固定：

- 完整 theorem type；
- GID；
- imports；
- 唯一消费者；
- 允许使用的冻结 GID；
- 禁止使用的 open heart；
- 成功判据和预算。

证明失败后改变 theorem type，必须新建 GID；不得保留旧名字并悄悄弱化结论。

### 2. 状态盲派生

研究状态应从以下事实派生：

- Lean 构建结果；
- `#print axioms`；
- source digest；
- theorem 完整类型；
- 已固定依赖。

“作者在账本中写 closed”不能成为派生器判断 closed 的输入。否则状态校验成为自读不动点问题。

### 3. 地址漂移

外部仓库的 `main`、`dev` 或浮动 tag 不是稳定 theorem 地址。消费外部形式化必须记录：

- commit；
- 模块；
- theorem 名；
- theorem type；
- source digest。

外部项目升级导致地址变化，只能追加新的 import receipt；不能据此改写旧 theorem 曾经是否通过。

### 4. 单命题单模块

R-A—R-F 的设计遵循：

- Core 只定义共享词汇；
- 每个 theorem 独立模块；
- 不为同一概念建立两个可供下游选择的同义谓词；
- 不添加隐藏 `Fintype`、`Nonempty`、测度或拓扑前件；
- 不把“更容易证明的 wrapper”保留在没有消费者的 API 中。

### 5. 不修改开放心脏

`o5_independence` 的 statement 应视为已有地址。若研究发现必须增加结构极点或缩小延拓域：

- 新建 O-5′；
- 写明与 O-5 的逻辑关系；
- 保留旧心脏；
- 不原地把困难命题改成已证明的较弱命题。

### 6. 窄通道原则

若 `Zeta23` 的外部 theorem 与本仓计数规范不同，应新增一个有名 bridge theorem，携带精确前件。不得全局放宽：

- 零点按重数／不同点的区分；
- simple zero 的定义；
- 对称截断规范；
- angular-frequency 规范。

## 三、suspected-novel 声明账

以下全部只是本卷的研究综合；不主张首次发现，不进入 literature-attested 栏。

### N-1　自然黄金坐标

[suspected-novel]

以 $w=\phi^2s$ 而不是“把结构极点送到 1”的缩放作为主坐标。理由是它同时把 germ agreement edge 送到 $\Re w=1$，把结构零线送到 $\Re w=1/2$，并把理论因子分解变成透明的三因子字典。

### N-2　两尺度 zeta 解释

[suspected-novel]

把

$\zeta(w)\zeta(\phi w)/\zeta(2w)$

解释为：

- 第一尺度经典零点；
- 黄金缩放尺度的极点／边界；
- doubling 尺度的结构零与潜在消去。

这是对 PZG 命题 6.19 的仓库接口解释，不是已形式化定理。

### N-3　黄金谱参数

[suspected-novel]

$\gamma_\phi(s)=-i(\phi^2s-1/2)$

作为 O-5 与现有 `spectralParameter` API 的唯一桥接坐标。

### N-4　O-5 的三层分类

[suspected-novel]

将 O-5 区分为：

1. 当前 kernel 中未桥接的开放命题；
2. 理论因子分解下与 RH 等价的窗口零点定位；
3. 额外要求 $\Re s>0$ 亚纯延拓的完整 heart。

该分类避免把“定位等价”误写成“完整 O-5 已等价”。

### N-5　O-6 空洞性审计

[suspected-novel]

把 `ZeroData` inhabitant 和 canonical convergence 设为 O-6 的语义验收门，而不满足于全称命题的类型闭合。

### N-6　Weil 研究进度向量

[suspected-novel]

采用

$(N_{\rm closed},V_{\rm ZeroData},C_{\rm conv},
L_{\max}^{\rm cert},B_T,\delta_{\rm PSD},A_{\rm external})$

度量定理进展，禁止用 CPU 时间、矩阵阶数或输出小数位代替逻辑进展。

### N-7　有限 Euler／divisor 早期否证器

[suspected-novel]

在投入全解析延拓前，先对 PZG 因子分解做有限素数系数、局部 Euler 指数和 meromorphic divisor 的一致性检查。任何固定阶反例都应立即终止当前黄金桥 statement，而不是等待大型解析证明失败。

## 四、立项裁决

### 主线

立项 O-6 基建线：

1. 修复非空洞语义；
2. 证明 RH $\Rightarrow$ 本仓 O-6；
3. 建立有限窗口 PSD 与尾项证书；
4. 精确暴露 O-6 $\Rightarrow$ RH 所需的 separator theorem；
5. 消费 2025–2026 的有限 Weil 压缩与外部形式化。

### 并行控制线

立项 O-5 字典线，但不直接攻 `o5_independence`：

1. 先闭合 R-A—R-C；
2. 证明 Euler germ 收敛；
3. 核验并形式化 PZG 命题 6.19；
4. 建立 divisor order 与窗口定位等价；
5. 把 $\Re s>0$ 延拓保留为独立远期义务。

### 暂不接受的说法

- “O-5 已与 RH 等价”；
- “O-5 是较弱 RH”；
- “O-5 与 RH 已证明独立”；
- “O-6 已经是非空洞的经典 Weil criterion”；
- “有限窗口 PSD 趋势证明全局正性”；
- “多数／密度一的零点在线证明 RH”；
- “Lean 已证明 RH”；
- “Gödel 表明 RH 不可证”。

### 最终研究命题

本卷支持继续研究，但只支持以下诚实定位：

- O-6 是仓库当前最成熟的经典主线；
- O-5 是具有明确两尺度 zeta 字典的高价值控制线；
- 两者当前没有 kernel 依赖；
- 近期可以关闭坐标、空洞审计和 RH 正向蕴含；
- 全局 O-6 反向、O-5 全延拓和 RH 本身继续明确标记 open；
- 每轮投入必须以 theorem 状态变化为边际收益，否则依 DECT 冻结并换 $\Gamma$；
- 所有新 statement、地址和外部依赖依 GFPT 前视固定，失败不得通过改写旧真来消除。

---

# 追加部一　定义侦察四构思(orchestrator 亲研,2026-08-30)

> 产地:claude 主循环在五遍扫描全部 RH 冻结面(Weil 核心、环面-曲率族、零点几何族、O-5 心脏、OACTC 165–173 部)后的自研综合;每条按 DECT 纪律给可证伪预测,suspected-novel 自标。本部为预登记:先写判据与预测,后开证。

## 一(A)　预算过滤的 RH 与零点观察成本

依 OACTC 173 的加权集合覆盖与 `finite_toroidal_spectral_tomography`,对紧窗口内零点 $\rho$ 定义**观察成本** $c(\rho)=\inf\{\sum_{D\in\mathcal D}c(D):\mathcal D\ \text{有限},\ \rho\ \text{的重数被}\ \mathcal D\ \text{层析认证}\}$(层析定理保证有限)。定义谓词族 $\mathrm{RH}_B$:预算 $\le B$ 可认证窗口内零点全临界。则 $\mathrm{RH}=\varinjlim_B \mathrm{RH}_B$。**价值**:DECT 预算包络从元纪律变为定理对象——「边际认证窗口/边际预算」曲线可形式化,平台期即盲核的分析版。〔suspected-novel(作为形式化对象);有限窗口验证思想 literature-attested〕
**可证伪预测**:若定义得当,认证窗对 $B$ 单调且黄金通道($c=\ell_5=4\log\varphi$,OACTC 172)出现在小预算最优覆盖中;若连单调性都须附加条件,则成本定义选错切面。

## 二(B)　曲率–账本对偶桥

`unitarity_line_iff`(临界线=尺度账本半密度归一后的酉轨迹)与 `interior_curvature_criterion`(RH ⟺ Riesz 曲率测度恒零)是两条互不 import 的等价刻画。**猜想(桥)**:内部曲率测度等于账本非酉亏损的二阶变分;`off_line_curvature_dipole` 的偶极矩即单零点的账本失衡荷。〔suspected-novel(仓内两真源之间的恒等桥)〕
**可证伪预测**:在共同玩具载体(有限零点集+显式账本)上,两侧可各自实算并逐点比对;若连玩具上都对不上,桥假,弃之(预算上限:两席位轮)。

## 三(C)　O-5 重释:最廉观察者的深度迭代 vs 全体观察者的宽度覆盖

实算(初等):$\beta(v)=\lfloor(v+1)\varphi\rfloor-1-v\psi=\sqrt5\,v+r(v)$,其中 $r(v)=(\varphi-1)-\operatorname{frac}((v+1)\varphi)\in(\varphi-2,\varphi-1]$ **有界**。故 eulerGerm 的指数格是 $\sqrt5$-准等差 Beatty 调制格,而 $\sqrt5=\sqrt{D_5}$、$\ell_5=4\log\varphi$——**germ 的 Witt 级联形如同一条黄金测地线在全部重整化深度的迭代观察**。O-5 由此重述:**深度迭代最廉通道,能否替代宽度覆盖全体判别式**(OACTC 172 已证 P₅ 单独不完备,但那是深度 1)。〔重释 suspected-novel;$\beta$ 的算术是可即刻 kernel 化的事实〕
**可证伪预测**:W-C1(下)必须一次过;若 Beatty 余项无界,则整个重释的地基错。

## 四(D)　F-RH 框架:RH 型命题 = 观察者族逃逸残差的 tempered 性

OACTC 165.3 的 $\mathcal A_{\mathrm{tor}}=\bigcap_T\ker\mathcal P_T$ 是 DECT 逃逸残差的字面实例。公理化:观察者族 $F$ 之 $\mathrm{Escape}(F)$;**$F$-RH** := $\mathrm{Escape}(F)$ 全 tempered。素观察者与环面观察者的残差可在有限窗口机器比较;DECT 对角定理暗示可数族残差恒非空——**RH 型命题从来不是「无逃逸」而是「逃逸受控」**。〔框架 suspected-novel〕
**可证伪预测**:细化单调性 W-D1 必须无条件成立,否则 Escape 的定义切面错。

## 义务清单(预登记,elementary 优先)

- **W-C1(β 格,首发)**:$\forall v,\ \beta(v)=\sqrt5\,v+r(v)\ \wedge\ r(v)\in(\varphi-2,\varphi-1]$;推论:格点间距 $\beta(v{+}1)-\beta(v)\in\{\sqrt5+\varphi-2,\sqrt5+\varphi-1\}$ 二值(Beatty 二距性)。
- **W-D1(Escape 反单调)**:$F\subseteq F'\Rightarrow \mathrm{Escape}(F')\subseteq\mathrm{Escape}(F)$;及与 165.3 实例的一致性。
- **W-A1(认证窗单调)**:玩具成本模型上认证窗对预算的单调性与并集封闭。
- **W-B1(桥之玩具)**:有限零点集上账本亏损二阶变分与曲率测度的显式比对载体构造。

后续增订继续严格追加于本节之后。

---

# 追加部二　平行侦察席报告(nyxid gpt-pro,盲于追加部一)

> 产地与独立性:本部为 nyxid gpt-pro 侦察席交付原文(company 池,mode:chat;主池 extraction 故障三败后换池,禁表格后成功)。**其 brief 只含冻结面材料,发出于追加部一写就之前,席位对 orchestrator 的四构思零可见**——故下述收敛为真独立、且跨模型族(GPT vs Claude)。
> **收敛注记(orchestrator 判)**:追加部一 A↔本部 W-D(认证失速/FiniteCertificateStall)、一 B↔本部 W-A(曲率-松弛相位桥)、一 C↔本部 W-F(黄金环面指标扩张)三对相撞;本部独有增量:provenance bitmask(直接回应 OACTC 172 的 P₅ 不完备性)、多尺度 cosh 指纹、射影 jet 尾历史态。两部义务合并去重后进 W 队列,命名以本部 proposed GID 为准、判据以追加部一的可证伪预测为准。

A. 残差地图

A.0 口径、对象空间与诚实边界

取阅截点为 2026-08-30 的公开 dev。以下把已冻结声明当依赖地址，不重证。唯一例外必须明说：GID D5/X_Frontier/Hearts 中 o5_independence 的 statement 已冻结而 proof body 仍是 sorry；o6WeilPositivityStatement 只是待证 Prop。本文绝不把二者写成已闭合定理。

为避免把“RH 的真假”这个一位目标误当成“零点定位”，取强目标
T(x) = （来源标签 base/twist/golden，零点位置的有限多重集，解析阶数）。
RH 只是 T 的“全部 base 零点实部为 1/2”投影。于是某坐标足以判 RH，不代表它足以定位 T。

对象空间 X 取四个有类型的纤维之不交和：单个 divisor atom、反射零点载体、环面因子状态、有限正性 completion。某坐标不适用于某纤维时返回同一个 none；这只是总化类型，不把对象身份塞进 q。

当前操作性概念 q_cert 取现有 theorem 面向消费者的粗商，而不是所有原始函数图：
- q_tor^0：completedZeta×twist 是否对所选/全部 index 同时为零；暂不含导数塔。
- q_temp：Re(s-1/2)=0 是否成立。
- q_curv^cert：临界支撑/flatness 的真假、偶极总质量与符号类别；若显式保留整条曲率函数，则记作更强的 q_curv^raw。
- q_budget^cert：固定有限层的可行/PSD/区间证书及“slack∈[0,1]”；不把隐藏 completion 或全部矩写入地址。
- q_gold^0：O-5 的结构实部类别、或单一黄金环面 P5 是否为零；经典 zeta 与 eulerGerm 尚无 kernel bridge 时返回 unbridged。

因此下列每对都注明它属于哪个商。若某个已冻结 raw lift 已能切开，我明确标“已有切刀”，不冒充新盲核。

A-R1 纵向别名：两个不同的临界线零点。

取 x=1/2+14.134725…i，y=1/2+21.022039…i；这是经典前两个经严格计算框架覆盖的 zeta 零点，T(x)≠T(y) 因为高度不同。q_tor^0 对二者都给“全 period 消失”；q_temp 都为 true；q_curv^cert 都给“临界支撑/零 damping defect”；q_budget^cert 若未绑定点级 compact coordinate 则二者同为 none；若只消费 chebyshev_slack_bounds 的区间结论，则二者同为 admissible；q_gold^0 对两者都是 unbridged；即使采用理论级 w=phi^2 s 拉回，其拉回点 x/phi^2、y/phi^2 也只共享结构实部 1/(2 phi^2)，仍无纵向地址。这些坐标都没有纵向地址。

冻结坐标：D5/S3/Analytic/Adelic/ToroidalTemperednessCriterion；D5/S3/Analytic/Adelic/FiniteToroidalSpectralTomography；D5/S3/Analytic/Adelic/RelativeCurvatureSupportCriterion；D5/S3/Zeros/Symmetry/CriticalDampingFlatness；D5/S3/Weil/CayleyLaguerre/ChebyshevSlackPositivity。数值出处：DLMF 25.10；Platt–Trudgian, “The Riemann hypothesis is true up to 3·10^12”, 2021。

裁决：在只含 criterion Boolean/区间状态的 Gamma_cert 中是疑似盲核。简单加入 Im(s) 会成为近乎身份编码；合格换语应是局部 amplitude/phase、计数地址或有限 projective jet。D5/S3/Analytic/Adelic/ToroidalCechCompletion 已说明 raw ratio-atlas 并不盲，故这不是整个仓库语言的绝对盲核。

A-R2 镜像侧别名：同一假想离线轨道的 right 与 left。

令 delta>0，x=1/2+delta+i gamma，y=1/2-delta+i gamma，并条件性假设二者是同一反射零点轨道；这不是断言离线 zeta 零点存在。T 区分左右位置。q_tor^0 对二者都为 invisible；q_temp 都为 false；completionBarycenter、半径 |delta| 与整条“成对偶极”是轨道级相同对象；只读 delta^2 的正预算也相同。

冻结坐标：D5/S3/Zeros/Symmetry/BarycenterDefectDecomposition；D5/S3/Analytic/Adelic/OffLineCurvatureDipole；D5/S3/Analytic/Adelic/ToroidalTemperednessCriterion。

裁决：可去残差，而且已有切刀。antiCoordinate(right)=delta，antiCoordinate(left)=-delta。新定义若只是重命名 antiCoordinate，应以“平凡/冗余”拒绝。

A-R3 单尺度阻尼碰撞：不同离线载体给同一 scalar defect。

在 tau=1，令 X 的实部偏移多重集为 {+1,-1}；令 b=arcosh((cosh(1)+1)/2)，Y 的偏移多重集为 {+b,+b,-b,-b}。则
D_X=2(cosh(1)-1)=4(cosh(b)-1)=D_Y，
但 T 的支撑和重数不同。两者的 q_temp 都是“非全临界”，每个反射偶极总曲率质量都为 0，单尺度 q_curv^cert 相同；若把它们作为条件性零载体，q_tor^0 也同为 invisible。

冻结坐标：D5/S3/Zeros/Symmetry/CriticalDampingFlatness；D5/S3/Analytic/Adelic/OffLineCurvatureDipole；D5/S3/Analytic/Adelic/RelativeCurvatureSupportCriterion。

裁决：可去残差。保留 tau↦D(tau) 的整函数会切开，但那成本过高；有限多尺度 fingerprint 是低成本历史提升。单个 tau 的 flatness theorem 只判 D=0，不声称正值可反演载体。

A-R4 Chebyshev 平方相位别名：x 与 a^2/x。

取 a>0、0<x<a，令 y=a^2/x>a，z_a(u)=(u-a)/(u+a)。直接代数给 z_a(y)=-z_a(x)。由 T_N(-z)=(-1)^N T_N(z)，对每个 N 都有
1-T_N(z_a(x))^2 = 1-T_N(z_a(y))^2。
若 x=(t-gamma)^2、a=delta^2，则两点分别落在偶极负核与正翼，T 必须区分，纯非负 slack 却永远不区分。

冻结坐标：D5/S3/Weil/CayleyLaguerre/ChebyshevSlackPositivity；D5/S3/Analytic/Adelic/OffLineCurvatureDipole。

裁决：对“平方 slack-only”语言是严格盲核；对 q_curv^raw 的联合语言则可去，因为曲率符号已切开。最小新增量应是一个 phase bit，而不是另造整条曲率函数。

A-R5 黄金单通道的因子来源别名。

固定同一参数 s，比较两个代数因子状态：x=(Lambda(s)=0, Lambda(s,chi_5)≠0)，y=(Lambda(s)≠0, Lambda(s,chi_5)=0)。二者都给 P5(s)=Lambda(s)Lambda(s,chi_5)=0；所有只依赖同一 s 的 tempered/曲率标签也相同，但 T 的 sourceTag 分别是 base 与 twist。这里是单乘积观察者的代数反模型，不断言两种解析状态会在同一真实 s 同时可实现。

冻结/热层坐标：GID D5/S3/Analytic/Adelic/ToroidalTemperednessCriterion 的 nonvanishing 机制；GID D5/S3/Analytic/Adelic/FiniteToroidalSpectralTomography；GID D5/S3/Analytic/Adelic/ToroidalCechCompletion；OACTC 第 166、167、172 部的 P_D=Lambda·Lambda_D 与黄金通道并集结论。

裁决：可去残差。记录 period-zero 与 twist-zero 的有限 provenance bitmask，或加入一个在 s 非零的第二通道，即可切开；只继续计算 P5 的更多小数位没有 DECT 增益。

A-R6 有限矩层级别名：同质量、同均值、不同支撑。

取 0<c<1，mu_0=delta_0，mu_c=(delta_{-c}+delta_c)/2。两者的 0 阶矩均为 1、1 阶矩均为 0，且都为偶正测度；但 T 的支撑不同，2 阶矩分别为 0 与 c^2。任何只到 N=1 的 moment/Toeplitz/预算 feasibility 坐标把二者放在同一纤维。Caratheodory 尺度协变只运输读数，不凭空恢复缺失矩。

冻结坐标：D5/S3/Weil/Budget/AtomicMomentHierarchyConvergence；D5/S3/Weil/Budget/FiniteMomentInfeasibilityCertificate；D5/S3/Weil/Budget/CaratheodoryScaleCovariance；D5/S3/Weil/Budget/MultiscaleLoewnerConstraint。

裁决：可去残差，下一矩已切开。更一般地，有限 N 的碰撞不是 full hierarchy 的盲核；atomic_moment_hierarchy_converges 只在 determining-family、compactness/cluster 与 optimizer 前件下给极限，不给“某个有限 N 已完备”。

A-R7 零值别名：同一点的一重 germ 与二重 germ。

固定 rho，并令 u 在 rho 邻域解析且 u(rho)≠0，取 f1(s)=(s-rho)u(s)，f2(s)=(s-rho)^2u(s)。q_tor^0 都只读“值为零”；q_temp、支撑位置、正 period energy 的局部极小位置也相同；T 的解析阶数分别为 1、2。

冻结坐标：D5/S3/Analytic/Adelic/ToroidalJetDepth；D5/S3/Analytic/Adelic/FiniteToroidalSpectralTomography；OACTC 第 168–170 部导数塔。

裁决：可去残差，而且已有切刀。toroidal_jet_depth_eq_vanishing_order 正好把第一可见导数层等同于 xi 的 vanishing order。若新定义只把这个 Nat 改名，应拒绝。

A-R8 边界盲核证人，不计作非平凡 RH 零点残差。

GID D5/S3/Zeros/PrimeRefinement/LocalNonzeroContinuationZero 在 s=-2 给出：每个 prime Euler factor 与每个有限 Euler window 都非零，而解析延拓后的 riemannZeta 为零。与 s=2 的“同样全部有限局部因子非零、全局 zeta 非零”相比，有限局部 Boolean 语言无法决定全局零性。配合 GID D5/S3/Zeros/PrimeRefinement/FinitePrimeExtractionZeroPersistence（任意有限 prime extraction 保持已有 strip zero），两向信息共同表明有限局部窗口既不能消除全局零，也不能由局部 nonzero 反推全局 nonzero。它不属于 T_nontrivial 的残差，因为 -2 是 trivial zero；但它严格否证“继续加有限素数 nonzero 标签最终会自动得到全局 continuation zero”的方法论。

裁决：这是 Gamma_Euler-local 的语言盲核证人。要换到 analytic continuation、meromorphic divisor 或 Cech gluing 语言；不是再扩一个 prime window。

总分类：A-R2、A-R7 已由冻结定义去除；A-R3、A-R4、A-R5、A-R6 可由低成本定义去除；A-R1 是 Gamma_cert 的疑似盲核但不是 Gamma_raw 的绝对盲核；A-R8 是有限局部 Euler 语言的严格边界证人。

B. 新连接

B-1 黄金 germ 与 toroidal twist：只能做“归一化 cofactor chart”，不能直接把 eulerGerm 塞进 RH 锚。

精确陈述形：设 Omega 是 O-5 窗口，且另有已证明的因子分解
Zqc(s)=xiReading(phi^2 s)·G(s)，
其中 G 在 Omega 全纯且处处非零。令 w=phi^2 s，period(golden,w)=Zqc(w/phi^2)，twist(golden,w)=G(w/phi^2)。则在 phi^2 Omega 上 period=xiReading·twist，singleton chart 覆盖该窗口；可直接消费 toroidal_cech_completion，并把 Zqc 的零除子在窗口内无消去地拉回 xi 零除子。

关键否定：当前 O-5 只给“存在 meromorphic Zqc、与 eulerGerm 在右半平面相等、窗口零点落在结构线”，没有给上述 factorization、G 非零或 divisor 无消去。eulerGerm 本身还可能有零/极点，故不是现成的 pointwise-nonvanishing twist；xiReading 与 completedRiemannZeta 之间的端点正规化也必须另有非零 bridge。把 golden index 加到一个已经 pointwise-nonvanishing 的 family 在类型上当然可证，但只增加观察通道，不增加 RH 锚的逻辑强度；若想 singleton 全局实例化 rh_iff_all_toroidal_eisenstein_tempered，还需 G 在全部相关参数非零，这远强于现状。

依赖：D5/X_Frontier/Hearts；D5/S3/Analytic/Adelic/ToroidalTemperednessCriterion；D5/S3/Analytic/Adelic/ToroidalCechCompletion；D5/S3/Analytic/Adelic/FiniteToroidalSpectralTomography；docs/develop/theory/GOLDEN_OBSERVER_RH_ROUTE.md 的 M5。

可证性预判：index 扩张与窗口重参数化高；给定 factorization 后的 gluing 高；上述 product factorization、G 非零、divisor 无消去是中长期解析义务；由当前 O-5 单独推出该连接不可证。

B-2 曲率偶极与 Chebyshev slack 的精确“幅相分解”。

令 x=(t-gamma)^2，a=delta^2，z=(x-a)/(x+a)，kappa=2(x-a)/(x+a)^2。对 N=1，T_1(z)=z，故
((x+a)kappa/2)^2 + (1-T_1(z)^2)=1，
sign(kappa)=sign(z)。
也就是说，slack_1 是归一化曲率的幅度余量，而偶极符号是它丢掉的 phase。再结合 A-R4 的 x↔a^2/x，可得到“所有平方 Chebyshev slack 相同但曲率相位相反”的显式逃逸对。

依赖：D5/S3/Analytic/Adelic/OffLineCurvatureDipole；D5/S3/Weil/CayleyLaguerre/ChebyshevSlackPositivity。

可证性预判：纯 field_simp/ring，极高；不触及 RH。它的研究价值是告诉预算层恰好缺一位符号，而不是宣称 slack 正性会推出临界线刚性。

B-3 DECT 边际捕获与有限正性认证生命周期。

精确有限命题：固定有限候选 completion 宇宙 U、目标审计标签 T、逐层读数 q_N，并令 d_{N+1} 是新增矩/Loewner/PSD 约束。设 R_N=E(q_N;T)。由 DECT 恒等式，
R_{N+1}=R_N∩ker d_{N+1}，
因此
card(R_N)-card(R_{N+1})
= card{(x,y)∈R_N : d_{N+1}(x)≠d_{N+1}(y)}。
右侧就是机器可核的 marginal information。它为 0 的准确含义只是“本层没有切开当前冻结 witness universe 中任何 residual pair”，应触发冻结/换候选或换 Gamma；它不等于“RH 已完备”。若给每层登记计算成本 cost、数值不稳定罚项 instability，可用 DECT 价值函数 V(d)=(card(R_N)-card(R_{N+1}))/(1+cost+instability) 排序；分子必须来自冻结 residual witness，而不能用目标标签直接构造 d。

预算层对应：multiscale_loewner_constraint 供应合法增量；finite_moment_infeasibility_certificate 供应有限终止型排除证书；atomic_moment_hierarchy_converges 供应带强前件的极限收敛，但没有有效收敛率，也不允许从一个很小的 frontier gap 推出全局充分性。

依赖：docs/develop/theory/DEFINITION_ESCAPE_COMPLETION_THEORY.md；D5/S3/Weil/Budget/MultiscaleLoewnerConstraint；D5/S3/Weil/Budget/FiniteMomentInfeasibilityCertificate；D5/S3/Weil/Budget/AtomicMomentHierarchyConvergence。

可证性预判：抽象 Finset 定理极高；把每个实际 PSD 层生成 canonical finite witness receipt 为中；连续 completion 空间的完备离散化与有效 tail rate 为难，不应伪装成已解决。

B-4 toroidal jet depth、无分岔与 completion velocity 的历史提升。

精确条件命题形：给反射协变的 C1 family F(tau,s)，令 F(tau0,·)=xiReading。若某个 toroidal family 在 s0 有非零 twist chart，且 toroidal jet depth 为 1，则由 toroidal_jet_depth_eq_vanishing_order 得 xi 在 s0 为一重零；补上 analyticOrderNatAt=1 推出 ds F(tau0,s0)≠0 的桥后，simple_zero_no_bifurcation 给出局部零支留在临界线，zero_completion_velocity 给出
rho'(tau0)=-partial_tau F/partial_s F，
并由局部临界线结论得到 Re rho'(tau0)=0。

这把“值为零”提升为 DECT/Yu Deng 式历史态：（首次可见层，completion 导数，spatial 导数，速度）。它不证明任意 zeta 零简单，也不排除多重零处的离线分岔。

依赖：D5/S3/Analytic/Adelic/ToroidalJetDepth；D5/S3/Zeros/Symmetry/SimpleZeroNoBifurcation；D5/S3/Analytic/Adelic/ZeroCompletionVelocity；D5/S3/Zeros/NormalJetFormula。

可证性预判：order-one 到 derivative-nonzero 的 API 桥为中低；组合 theorem 为中；多重零的统一 Weierstrass/branch 版本为难。

C. 新定义候选

C-1 ToroidalVanishingProfile：有限通道的零因子 provenance。

CUT：切 A-R5；也细化 A-R1 的“所有 period 都是 0”粗 Boolean，但不保证单独定位高度。

ADMIT：只读取冻结 selected、period、twist 的点值，不调用 IsNontrivialZero、RH、critical line 或 T；对 index 重命名自然；成本是 2·|selected| 个 bit；比保存全部函数图有严格压缩。

Lean 骨架：

    universe u v w

    structure ToroidalVanishingProfile (Index : Type u)
        [DecidableEq Index] where
      selected : Finset Index
      periodZero : Finset Index
      twistZero : Finset Index

    def toroidalVanishingProfile
        {Index : Type u} {Point : Type v} {Scalar : Type w}
        [DecidableEq Index] [DecidableEq Scalar] [Zero Scalar]
        (selected : Finset Index)
        (period twist : Index → Point → Scalar) (s : Point) :
        ToroidalVanishingProfile Index where
      selected := selected
      periodZero := selected.filter fun i => period i s = 0
      twistZero := selected.filter fun i => twist i s = 0

三病自检：不平凡，因为代数状态 (0,1) 与 (1,0) 的 bitmask 不同；不泄漏，因为定义体没有 base-zero/RH 接口；非身份编码，因为输出有限 bitmask，不含 s、函数图或对象序列化。

状态：[literature-attested ingredients] Hecke–Zagier product periods；Cornelissen–Lorscheid, “Toroidal automorphic forms, Waldspurger periods and double Dirichlet series”, arXiv:0906.5284。[suspected-novel] 把 period-zero/twist-zero 双 bitmask 作为本仓 DECT 定义与证书 API。

可证伪预测 5′：若好，黄金通道的 twist-only false positives 会被一个非零 twist witness 立即分开，且 profile 在 index 等价下保持；若坏，实际 selected family 在目标窗口总给同一 bitmask、或下游仍只消费 conjunction，边际 Capture=0，应删除而非保留装饰性结构。

C-2 PhaseBearingSlack：给平方 slack 补最小相位位。

CUT：精确切 A-R4；在镜像/偶极语境也切 A-R2 的符号投影，但已有 antiCoordinate 时不得重复消费。

ADMIT：由 compact coordinate z 与 Chebyshev 读数直接生成；尊重 z↦-z 对称；成本一实数加一 bit；不保存 x 或完整载体。

Lean 骨架：

    universe u

    structure PhaseBearingSlack (R : Type u) where
      slack : R
      nonnegativePhase : Bool

    def phaseBearingSlack {R : Type u} [LinearOrderedField R]
        (cheb : R → R) (z : R) : PhaseBearingSlack R where
      slack := 1 - (cheb z) ^ 2
      nonnegativePhase := decide (0 ≤ z)

三病自检：不平凡，因为 z 与 -z 的 squared slack 相同而 phase bit 通常相反；不泄漏，因为不读零点、RH 或 line label；有压缩，因为输出不含 x、gamma、delta 或曲率整函数。若 downstream 已有 antiCoordinate/curvature sign，定义相对该 q 为冗余，应只在 Budget 层拥有一个消费者。

状态：[literature-attested ingredients] Chebyshev parity 与 phase/magnitude 分离是标准构件；冻结范围定理由 GID D5/S3/Weil/CayleyLaguerre/ChebyshevSlackPositivity 给出。[suspected-novel] 该二元读数及其曲率消费者关系。

可证伪预测 5′：若好，A-R4 的 reciprocal pair 在 N=1 即被稳定切开，且额外成本不随 N 增长；若坏，phase bit 总能由现有 q_curv 计算且没有 Budget-only consumer，则它是冗余包装，应拒绝合入。

C-3 MultiscaleDampingFingerprint：有限尺度的 cosh 历史。

CUT：切 A-R3 的单尺度碰撞；对更高阶有限矩碰撞只减少残差，不宣称完备。

ADMIT：只读 finite carrier 的 realPart 与预先冻结的 scales；对 carrier 置换不变；成本 O(n·|Zero|)；n 个实数远小于保存整条 tau↦D(tau) 或完整零点多重集。

Lean 骨架：

    universe u

    noncomputable def multiscaleDampingFingerprint
        {Zero : Type u} [Fintype Zero] {n : Nat}
        (realPart : Zero → ℝ) (scale : Fin n → ℝ) : Fin n → ℝ :=
      fun k =>
        D5.S3.Zeros.Symmetry.CriticalDampingFlatness.criticalDampingDefect
          realPart (scale k)

三病自检：不平凡，因为新增尺度可使原先相等的 exponential sums 分离；不泄漏，因为没有“是否为 zeta zero”或 T；非身份编码，因为固定 n 时只保留有限变换样本。scales 必须前视固定，禁止看见碰撞后逐样本挑点。

状态：[literature-attested ingredients] 双边 Laplace/cosh 变换、有限矩问题与指数和辨识。[suspected-novel] 作为 RH curvature residual 的有限 fingerprint 和 DECT gain 单元。

可证伪预测 5′：若好，在冻结的小型反射载体库中，每个早期新尺度产生正 marginal Capture，随后可测地平台化；若坏，跨大量自然 scale set 仍存在高质量碰撞，或 gain 对 scale 微扰极不稳定，应把该平台解释为 blind-kernel 信号，转向 measure/transform language，而不是无限加尺度。

C-4 FiniteCertificateStep：正性认证的可机读边际步骤。

CUT：对 A-R6，加入二阶矩后 certificateReading 可把 mu_0 与 mu_c 分开；一般用途是显式记录某一预算层究竟删掉了哪些 finite candidates。

ADMIT：before/after 必须由前视冻结、target-free 的约束生成；对 Candidate 等价重命名自然；membership 是一 bit，marginalInformation 是一个 Nat；计算只需有限集合。Candidate 若直接用 T 标签命名，审计应拒绝。

Lean 骨架：

    universe u

    structure FiniteCertificateStep (Candidate : Type u)
        [DecidableEq Candidate] where
      before : Finset Candidate
      after : Finset Candidate
      monotone : after ⊆ before

    def certificateReading {Candidate : Type u} [DecidableEq Candidate]
        (step : FiniteCertificateStep Candidate) (x : Candidate) : Bool :=
      decide (x ∈ step.after)

    def marginalInformation {Candidate : Type u} [DecidableEq Candidate]
        (step : FiniteCertificateStep Candidate) : Nat :=
      step.before.card - step.after.card

三病自检：不平凡，因为真正新增约束可令 after 为 proper subset；不泄漏，因为生成器不能访问 T，T 只允许在离线 DECT 评分器中评估 Capture；非身份编码，因为公开读数是 membership/gain，不是 completion 全序列化。若有限候选网格不是问题的 canonical 对象，只能称实验 receipt，不能称数学完备证书。

状态：[literature-attested ingredients] cutting-plane、constraint generation、truncated moment/SDP hierarchy。[suspected-novel] 将其绑定到 DECT residual capture 与本仓 positivity lifecycle。

可证伪预测 5′：若好，重复扩大矩阵但 after 不变时会得到精确 0 gain，CI 能阻止“算得更多即进展”的伪叙事；若坏，结论随任意 discretization 大变，说明 Candidate 宇宙不自然，应改用连续 frontier gap、rank 或正式 infeasibility certificate。

C-5 ProjectiveJetFingerprint：去规范化的有限 toroidal jet。

CUT：确定性切 A-R7 的 multiplicity alias；对 A-R1 提供可检验的纵向分辨力，但不猜测任何固定 r 必然区分全部零点。

ADMIT：输入是某个已选 nonvanishing toroidal chart 的 period 原始导数；用首个非零导数归一化后，对 test-vector 的非零常数缩放不变；成本为 order 加 r 个复数；不输出 s 或完整 Taylor germ。

Lean 骨架：

    universe u

    structure ProjectiveJetFingerprint (K : Type u) (r : Nat) where
      order : Nat
      tail : Fin r → K

    noncomputable def projectiveToroidalJet
        (period : ℂ → ℂ) (s : ℂ) (m r : Nat)
        (_earlierVanish : ∀ j < m, iteratedDeriv j period s = 0)
        (_anchorNonzero : iteratedDeriv m period s ≠ 0) :
        ProjectiveJetFingerprint ℂ r where
      order := m
      tail := fun k =>
        iteratedDeriv (m + k.1 + 1) period s /
          iteratedDeriv m period s

三病自检：不平凡，因为 order 或 normalized tail 可变；m 必须由 earlierVanish+anchorNonzero 或冻结 toroidal depth 证书产生，禁止调用者任意写入；不泄漏，因为不引用 xi-zero、RH、criticalAbscissa 或 T；非身份编码，因为有限 r 截断且不含点本身。chart 必须由 C-1 的 twist-nonzero provenance 选择，否则在 twist zero 上会把来源污染当成 base jet。

状态：[literature-attested ingredients] analytic/projective jets；Cornelissen–Lorscheid 的 toroidal derivative tower；冻结 GID D5/S3/Analytic/Adelic/ToroidalJetDepth。[suspected-novel] 将首个可见层后的 projective tail 作为 DECT history state。

可证伪预测 5′：若好，低位已认证零点的 fingerprint 会在小 r 下分开，并对 period 乘非零常数严格不变；若坏，结果强依赖 chart、归一化不稳定或长期同值，则它不是地址，应回到 Cech amplitude/zero-counting language。

C 节总 ADMIT 裁决：C-1、C-2、C-3、C-5 是可进入数学 API 的候选；C-4 是治理/证书 API，不能进入 RH 前件。任何候选若没有明确下游 theorem 消费者，按 DECT 平凡病直接淘汰。

D. 义务清单 W-A 至 W-F

W-A：proposed GID D5/X_Frontier/DefinitionEscapeRH/CurvatureSlackPhaseBridge。
单一 theorem：在 a>0、x≥0 下证明 normalized curvature 与 N=1 slack 的恒等式；再在 0<x<a、y=a^2/x 下同一结论中证明 slack 相等而 phase 相反。只用 field_simp、ring 与 GID OffLineCurvatureDipole、ChebyshevSlackPositivity 的命名约定；不触及 zeta。

W-B：proposed GID D5/X_Frontier/DefinitionEscapeRH/ToroidalProvenanceCut。
单一 theorem：若 selected 中 i 满足 period i s=base s·twist i s 且 twist i s≠0，则 i∈periodZero ↔ base s=0，并且 i∉twistZero。它是 C-1 切 A-R5 的最小证书；只用 mul_eq_zero。

W-C：proposed GID D5/X_Frontier/DefinitionEscapeRH/MultiscaleFingerprintAppend。
单一 theorem：向 scales 追加一个尺度后，旧 fingerprint 是新 fingerprint 的前缀；若两载体在新增尺度 defect 不同，则新 fingerprint 不同。有限函数外延即可，不证明“总存在分离尺度”。

W-D：proposed GID D5/X_Frontier/DefinitionEscapeRH/FiniteCertificateStall。
单一 theorem：对 step.monotone，marginalInformation step=0 ↔ step.after=step.before。它把“边际信息为零”固定成精确有限命题，不外推未来层或连续 completion。

W-E：proposed GID D5/X_Frontier/DefinitionEscapeRH/ProjectiveJetScaleInvariance。
单一 theorem：c≠0 时，period 与 c·period 在同一点、同一 anchor order 上产生相同 ProjectiveJetFingerprint。消费 iteratedDeriv_const_mul；这是 C-5 自然性的入场门。

W-F：proposed GID D5/X_Frontier/DefinitionEscapeRH/GoldenToroidalIndexExtension。
单一 theorem：若原 twist family pointwise nonvanishing，则以 Sum/Option 加入任意 golden candidate 后仍 pointwise nonvanishing，且原 RH toroidal criterion 的右侧共同零条件由 restriction 得回。该 theorem 只闭合 index plumbing；结论中必须明写“不证明 eulerGerm 是 nonvanishing twist，也不证明 O-5 factorization”。

执行顺序：W-A、W-B、W-D、W-C、W-E、W-F。每模块一个 public theorem，先固定完整类型与唯一消费者；全部 #print axioms；不得 import 或调用 o5_independence；任何需要新的全局解析前件时立即从 elementary 波退出，而不是加 sorry。

后续增订继续严格追加于本节之后。

---

# 追加部三　W-C1 勘正(席位保真门拒因驱动,2026-08-30)

形式化席 la60 在 pre-deposit 保真门将追加部一的 W-C1 **整体拒绝**:其子句 3(二距集 $\{\sqrt5+\varphi-2,\ \sqrt5+\varphi-1\}$)在逐字 Hearts 定义下为**假**——orchestrator 在 $r$ 差分方向上犯符号错。席位零 deposit、如实 AU(未对子句 1/2 作完成声明),拒因质量为本卷树立保真门标杆。

**勘正推导**:$\beta(v{+}1)-\beta(v)=\Delta\mathrm{beatty}(v)-\psi=\Delta\mathrm{beatty}(v)+(\varphi-1)$,而 Beatty 增量 $\Delta\in\{1,2\}$,故

$$\boxed{\ \beta(v{+}1)-\beta(v)\in\{\varphi,\ \varphi^2\}\ }$$

——黄金格的相邻间距**恰为黄金幂**,比原错写更强地支撑构思 C(数值验:$\beta(2)-\beta(1)=4.236\ldots-2.618\ldots=\varphi$)。

**W-C1′(重述,取代 W-C1 进入义务队列)**:子句 1、2 不变($\beta(v)=\sqrt5\,v+r(v)$,$r(v)=(\varphi-1)-\operatorname{fract}((v{+}1)\varphi)\in(\varphi-2,\varphi-1]$);子句 3 改为二距集 $\{\varphi,\varphi^2\}$,并加推论 3′:$\Delta=1\Leftrightarrow$ 间距 $=\varphi$(Beatty 编码即黄金/白银步的 Sturmian 词)。

后续增订继续严格追加于本节之后。


---

# 增订三　W-B1 判决:blocked(盲核发现)与 W-B2 预登记

> 产地(第 9′ 条):skill=consensus-rnd:sshx;实施=codex-cli 单席(sci-la86-wb1,1811s,三态诚实出口 brief);orchestrator 亲验信封读数与两侧实算;零评审席,强度按单席折算。判决日:2026-09-01。

## 一　判决:W-B1 = blocked,非 proved 非 refuted

依 §二(B) 预登记判据在共同玩具载体上开庭。玩具:$Z=\{\rho_+,\rho_-\}$,$\rho_+=3/4$,$\rho_-=1/4=1-\overline{\rho_+}$,重数各 1;账本 $A=\mathbb N$,$\mathrm{length}(n)=n$,$a=1$;$\delta=1/4$,$\gamma=0$。

**两侧各自实算均成功**(这不是失败的一部分,是判决的原料):
- 曲率侧(`interior_curvature_criterion` 的字面特化):$\mu = 2\pi\,\delta_{i/4}$,总质量 $2\pi$;偶极核 $\kappa(\gamma)=-2/\delta^2$,$\int\kappa=0$。
- 账本侧(`scalingLedger`/`halfDensityReading` 的字面特化):条目 $\pm 1/4$(镜像对相消),归一化范数 $e^{\mp 1/4}$,冻结范数形 $N(u)=e^{-u}$。

**阻断在猜想自身的词汇缺口**:「账本非酉亏损的二阶变分」在仓内**无冻结定义**。四个自然候选给出互不相容的常数——$(\log N)''(0)=0$、$(N-1)''(0)=1$、$(N^2-1)''(0)=4$、$((N-1)^2)''(0)=2$;与曲率侧质量 $2\pi$ 逐点比对分别要求归一化常数 无解、$2\pi$、$\pi/2$、$\pi$。另缺两件:零点→账本地址的 canonical 映射;标量 Hessian→$\mathrm{Measure}\ \mathbb C$ 的嵌入(两侧 codomain 本不相同:测度 vs $\mathbb R\to\mathbb R$)。

**裁决(席位的诚实出口,orchestrator 追认)**:在此刻选定 loss、地址映射、嵌入或归一化中的任何一个,都等于**把被检验的桥安装成定义**,使「相等」退化为重言——那是美冒充证明(第 3 条)。故不发 Lean 桥定理,亦不发反驳定理:**猜想在当前词汇表下尚不是命题**。这是第 5″ 条盲核的字面实例:消它的不是预算,是换定义。预算记账:两席轮上限,已用一轮;第二轮不用于 grind,保留给 W-B2 之后的重测。

## 二　W-B2 预登记(定义义务:先独立论证,再重测)

**义务**:为「账本非酉亏损」选定一个二阶变分定义,**选择理由必须独立于桥**——即从账本自身的几何/信息语义(如:亏损作为偏离酉轨迹的局部能量,其自然二次型)推导,不得引用「哪个候选使玩具相等」作为依据;同时给出零点→账本地址映射与标量→测度嵌入的 canonical 形,并说明其对镜像对相消(`ZeroGeometry`)的相容性。
**可证伪预测(写在任何重测之前)**:若定义选择正确,W-B1 玩具上两侧**不经额外调参**逐点相等(允许一个全局常数,该常数须在定义处一次性固定);若独立论证选出的定义仍对不上,桥假,弃之——且此时的弃是**有内容的弃**(排除了「定义没选对」这一可去混淆,判死的是结构盲核)。
**边界**:W-B2 是定义义务而非定理义务;其交付物是定义 + 论证 + 相容性引理,重测(W-B3)另行开单。

后续增订继续严格追加于本节之后。

---

# 增订四　W-B3 判决:桥假,结案(B 线全弧收官)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;W-B2 定义席(sci-la88-wb2)与 W-B3 重测席(sci-la89-wb3)均为 codex-cli 单席;orchestrator 亲验各信封、rollout 独立性抽查、两侧读数;零评审席。判决日:2026-09-01/02。

## 一　判决:§二(B) 猜想(桥)= **refuted**(kernel 判死,负向结案)

按增订三预登记的两步走完:
1. **W-B2(定义,独立论证)**:选定 $((N-1)^2)''(0)$,$N(u)=e^{-u}$,沿账本位移率求值——论证纯内在($\log N$ 仿射故曲率恒零;未平方候选带号非中心能量;范数坐标下到酉轨迹的平方距离是自然局部能量,偶、可加、免校准),先于任何玩具比对固定。机器恒等式 $V(d)=2d^2$;地址 $\rho-\mathrm{mirror}(\rho)$;嵌入 $\mathrm{ofReal}(w)\cdot\delta_\rho$;镜像相容六定理(`D5/S3/Weil/LedgerDeficitSecondVariation`)。
2. **W-B3(重测,冻结定义字面特化)**:双例开庭——$Z_1=\{3/4,1/4\}$:曲率 $2\pi\,\delta_{i/4}$(质量 $2\pi$)vs 亏损 $\tfrac1{32}\delta_{3/4}+\tfrac1{32}\delta_{1/4}$(质量 $\tfrac1{16}$);$Z_2=\{1,0\}$:曲率 $2\pi\,\delta_{i/2}$ vs 亏损 $\tfrac12\delta_1+\tfrac12\delta_0$(质量 $1$)。`no_global_mass_normalization` 与 `curvature_ledger_bridge_refuted`(`D5/S3/Weil/CurvatureLedgerBridgeRefutation`,std3):$\neg\exists$ 全局常数同时匹配两例($c=2\pi$ 与 $c=32\pi$ 互斥),支撑失配独立成立。

## 二　弃的内容(这不是空手而归)

- **可去混淆已消**:「定义没选对」被 W-B2 的独立论证排除——判死的是**结构盲核**:内部曲率原子的质量是常量 $2\pi\cdot\mathrm{mult}$(计数型,对位移不敏感),账本亏损二阶变分随位移平方变(能量型,对位移二次敏感);二者不是同一个量的两个坐标,任何标量归一都救不回。`off_line_curvature_dipole` 的偶极矩若要成为「账本失衡荷」,须换**非标量**的对应(如位移加权的曲率矩),那是新猜想,须另行预登记。
- **正资产清单**:B 线全弧沉淀七个冻结真值节点(定义模块六定理 + 桥反驳二定理中的可复用读出),外加一条方法论判例——**盲核的完整处置**:发现词汇缺口(W-B1 blocked)→ 独立定义(W-B2)→ 判死结构(W-B3),每步预登记、每步 kernel 化;「弃一个美的猜想」全程无一步靠语气,全靠读数。
- **预算记账**:增订三预算「两席轮」如约用尽(W-B1 一轮 + W-B3 一轮;W-B2 为增订三新立义务,另计一轮)。B 线关闭,不再续测;若未来提出非标量对应,按新义务预登记,不复用本线预算。

后续增订继续严格追加于本节之后。

---

# 增订五　B 线结案后的第一开放边:定义逃逸初等波预登记(W-A、W-C、W-B)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;六席思考面板(codex-cli ×4 teleology/parsimony/fidelity/natural-ownership、nyxid GPT PRO ×1 worth、隔离 subagent ×1 proportional-containment)并发盲评,全部 `revise`,meta-judge 由 orchestrator 收敛;本节三条子句的 Lean 陈述由 orchestrator 在钉版工具链亲跑探针确认为真(标准三公理)后才写入,以免重蹈追加部三 W-C1 的假子句先例。判决日:2026-09-02。lane issue:#4589。

## 〇　为什么是这三条

增订四已判死 §二(B) 的标量桥。追加部二 §D 的义务 W-A…W-F 被消化成整节 atom(24–27 KB),单定理模块无法逐字 cover;故按增订三/四的先例,把本波要派的义务逐条重述为可独立消化的小节,每节一条公开定理、一条写在跑之前的可证伪预测。选题依据:两侧皆锚定冻结声明、初等策略可闭合、自然目录未满或裂桶成本可计价、有具名消费者。W-D 依 §C 自判「C-4 是治理/证书 API,不能进入 RH 前件」不入本波;W-E 排在 W-B 之后(需 C-1 的 provenance 位与同一裂桶);W-F 待真实黄金分解消费者出现。

## 一　W-A 预登记:曲率–slack 相位桥(`CurvatureSlackPhaseBridge`)

**义务**:对 $a>0$、$x\ge 0$,令 $z=\frac{x-a}{x+a}$(即 `chebyshev_slack_bounds` 的 compactCoordinate),$\kappa=\frac{2(x-a)}{(x+a)^2}$(即 `off_line_curvature_dipole` 第一合取项的曲率公式在 $x=(t-\gamma)^2$、$a=\delta^2$ 下的字面形),$\mathrm{slack}_1=1-T_1(z)^2$。单一公开定理证明:$\bigl(\tfrac{(x+a)\kappa}{2}\bigr)^2+\mathrm{slack}_1=1$ 且 $\tfrac{(x+a)\kappa}{2}=z$;并在 $0<x<a$、$y=a^2/x$ 下于同一结论中证明 $z(y)=-z(x)$、$\mathrm{slack}_1(y)=\mathrm{slack}_1(x)$、$z(x)<0<z(y)$(相位相反)。模块须 `import` 上述两冻结模块,并以具名引理把 $\kappa$ 与 `off_line_curvature_dipole` 的曲率公式在 $x=(t-\gamma)^2$、$a=\delta^2$ 下字面对接;不触及 zeta、零点或 RH。
**可证伪预测(写在跑之前)**:若正确,该定理以 `field_simp`/`ring`/`nlinarith` 级初等策略在钉版工具链闭合,公理集为标准三条;若任一子句为假,整条 W-A 作废,不得削弱子句以求闭合。
**边界**:只闭合 A-R4 倒数对「slack 相等、相位相反」这一读数,把 C-2 的 phase bit 挣成定理;不主张其外任何 RH 前件。

## 二　W-C 预登记:多尺度阻尼指纹的追加律(`MultiscaleFingerprintAppend`)

**义务**:复用冻结 `criticalDampingDefect`,定义指纹 $F(\mathrm{realPart},\mathrm{scale}):\mathrm{Fin}\,n\to\mathbb R$,$F_k=\mathrm{criticalDampingDefect}(\mathrm{realPart},\mathrm{scale}_k)$。单一公开定理:对任意有限载体与追加尺度 $\tau'$(`Fin.snoc scale τ'`),(i) 旧指纹是新指纹在 `Fin.castSucc` 上的前缀;(ii) 两个载体(允许不同的有限指标类型)若在 $\tau'$ 处 defect 不等,则扩展后指纹不等。不证明「总存在分离尺度」。
**可证伪预测(写在跑之前)**:若 C-3 有内容,则 A-R3 的单尺度碰撞在第二尺度被切开:取 X 的中心化偏移多重集 $\{+1,-1\}$、Y 为 $\{+b,+b,-b,-b\}$ 且 $\cosh b=(\cosh 1+1)/2$,则 $D_X(1)=D_Y(1)=2(\cosh 1-1)$ 而 $D_X(2)-D_Y(2)=2(\cosh 1-1)^2>0$;模块须以具名定理在钉版工具链兑现这两式。若两式任一在 kernel 下不成立,则 C-3「早期新尺度产生正 Capture」的预测被证伪,C-3 应退出而非再加尺度。
**边界**:不主张有限矩层级完备,不引入 measure/transform 语言,不触及 zeta 零点是否存在。

## 三　W-B 预登记:环面零因子 provenance 切刀(`ToroidalProvenanceCut`)

**义务**:按 C-1 骨架定义 `ToroidalVanishingProfile`(selected / periodZero / twistZero 三个 Finset)与构造子 `toroidalVanishingProfile`(以 `Finset.filter` 取 period、twist 在 $s$ 处为零的 index)。单一公开定理(挣得该定义):对无零因子的标量类型,若 $i\in\mathrm{selected}$、$\mathrm{period}_i(s)=\mathrm{base}(s)\cdot\mathrm{twist}_i(s)$ 且 $\mathrm{twist}_i(s)\ne 0$,则 $i\in\mathrm{periodZero}\iff\mathrm{base}(s)=0$,且 $i\notin\mathrm{twistZero}$。只用 `mul_eq_zero` 与 `Finset.mem_filter`。
**可证伪预测(写在跑之前)**:若 D5 已存在**可寻址**的等强陈述(逐 index 的 profile 成员刻画,而非 `toroidal_common_zero_locus` 那样在 pointwiseNonvanishing 下的全局集合相等),则本义务的交付物是 bind 报告而非新模块;若 `Analytic/Adelic` 已满(24/24,写入时实测),则须裂桶并如实计价,不得为躲容量放进语义错误的目录。定理本身预期以 `simp [mul_eq_zero]` 级策略闭合。
**边界**:只闭合 index plumbing 的最小证书,为 C-5 的 chart 选择提供 twist 非零 provenance;不主张任何黄金通道的 twist 非零,不触及 eulerGerm 与 O-5。

## 四　预算与结算

三条各一席位轮(codex-cli,独立 worktree,各自 PR);任一席以 `open` 出口即在本卷下一增订登记其阻断面,不复用预算 grind。研究席另行开单(非标量测度值输运 N-M1,草稿不入库),其采纳与否由 owner 裁决。

后续增订继续严格追加于本节之后。

---

# 增订六　第二波预登记:偶极总变差、投影 jet 尺度不变性、黄金环面 index 扩张(W-G、W-E、W-F)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;选题沿用 la91 面板的常设 refill 规则(#4589),不重开面板;两条子句各由一席 codex-cli 探针在钉版工具链整证(标准三公理)后才写入,探针不入库;W-G 的来源是研究席(nyxid GPT PRO)N-M1 草稿中唯一有独立内容的恒等式,桥式解释未采纳(见 #4589 批注)。判决日:2026-09-02。

## 〇　为什么是这两条

增订五的 W-A、W-C 已两阶段落地,W-B 在评审。按常设规则补位:候选须两侧锚定冻结/Mathlib 声明、探针可闭合、有具名消费者、桶未满或裂桶已存在。W-G 把 N-M1 研究草稿里可独立成立的分析事实从桥式叙事中剥出来单独入库;W-E 是 C-5 自然性的入场门,其定义须在 W-B 建立的 `Analytic/Toroidal` 桶内落户。W-F 只闭合 index plumbing,三条探针皆已在钉版工具链整证;W-D1 待 Escape(F) 定义就绪后另立增订。

## 一　W-G 预登记:离线曲率偶极的总变差(`OffLineCurvatureDipoleTotalVariation`)

**义务**:对 $\delta>0$、任意 $\gamma\in\mathbb R$,取 `off_line_curvature_dipole` 第一合取项给出的冻结曲率密度 $\kappa_{\delta,\gamma}(t)=2\,\frac{(t-\gamma)^2-\delta^2}{((t-\gamma)^2+\delta^2)^2}$。单一公开定理证明 $\int_{\mathbb R}|\kappa_{\delta,\gamma}(t)|\,dt=\frac4\delta$。证明须 `import` 并消费冻结定理的可积性、零总质量与符号轮廓(核内负、翼上正、零点 $\gamma\pm\delta$),不得重证这些合取项;原函数 $F(t)=-\frac{2(t-\gamma)}{(t-\gamma)^2+\delta^2}$ 给出核积分 $-2/\delta$,零总质量给出翼积分 $2/\delta$。
**可证伪预测(写在跑之前)**:若正确,定理以有限区间微积分基本定理(`intervalIntegral.integral_eq_sub_of_hasDerivAt`)、可测补集分拆(`integral_add_compl`)与 `Integrable.abs` 在钉版 Mathlib 闭合,公理集为标准三条;若总变差不等于 $4/\delta$ 或需要额外可积性假设,则 N-M1 草稿的位移次数论证($d^5\cdot$总变差的齐次度 4)失去前提,须撤回该草稿。
**边界**:只闭合一个关于冻结偶极的 $L^1$ 恒等式;不主张任何曲率→账本亏损的输运或 RH 前件。

## 二　W-E 预登记:投影 jet 指纹的尺度不变性(`ProjectiveJetScaleInvariance`)

**义务**:按 C-5 骨架定义 `ProjectiveJetFingerprint`(order 与 `Fin r → K` 的 tail)与构造子 `projectiveToroidalJet`(首个非零导数归一化后的 $r$ 个投影系数,anchor 阶 $m$ 由 earlierVanish 与 anchorNonzero 两个假设给出)。单一公开定理:对 $c\ne0$,`period` 与 $z\mapsto c\cdot\mathrm{period}(z)$ 在同一点 $s$、同一 anchor 阶 $m$ 上产生相同的指纹(order 与 tail 皆相等);两个假设经具名引理转移到 $c\cdot\mathrm{period}$(消费 `iteratedDeriv_const_mul_field` 与 `mul_ne_zero`)。
**可证伪预测(写在跑之前)**:若正确,归一化后的 tail 逐分量为 $\frac{c\,f^{(m+k+1)}(s)}{c\,f^{(m)}(s)}$ 约去 $c$,定理以 `iteratedDeriv_const_mul_field` 与 `mul_div_mul_left` 级引理闭合,公理集为标准三条;若在钉版 Mathlib 中该引理需要 `ContDiff` 前提而无法免除,则义务改标 `open` 并记录所需前提。
**边界**:只闭合 test-vector 非零常数缩放下的不变性;anchor 阶 $m$ 由假设给出,不主张它由 `ToroidalJetDepth` 的深度证书产生(那是另一条义务),不触及 zeta 零点、RH 或 C-1 的 chart 选择。

## 三　W-F 预登记:黄金环面 index 扩张(`GoldenToroidalIndexExtension`)

**义务**:设 twist 族 $\{\mathrm{twist}_i\}_{i\in I}$ 与 period 族满足冻结分解 $\mathrm{period}_i(s)=\xi(s)\,\mathrm{twist}_i(s)$(`xiReading`),且在窗口 $\Omega$ 上逐点非零($\forall s\in\Omega,\ \exists i,\ \mathrm{twist}_i(s)\ne0$)。以 `Sum Index Unit` 加入任意一个黄金候选对 $(\mathrm{goldenPeriod},\mathrm{goldenTwist})$(仅假设其同样按 $\xi$ 分解)。单一公开定理证明:(i) 扩张族在 $\Omega$ 上仍逐点非零;(ii) 扩张族的窗口公共零点集 $\{s\in\Omega\mid\forall j,\ \mathrm{period}'_j(s)=0\}$ 等于原族的窗口公共零点集(两侧皆经冻结 `toroidal_common_zero_locus` 化为 $\xi$ 的零点集);并以具名引理证明:当原族全局逐点非零时,冻结 `rh_iff_all_toroidal_eisenstein_tempered` 右侧的共同零条件在扩张族与原族之间等价(经同一 RH 左侧传递)。证明须 `import` 并消费上述两冻结定理,不重证任何解析内容。
**可证伪预测(写在跑之前)**:若正确,定理只用 `Sum.elim`、`Sum.inl` 见证与冻结定理的两次实例化闭合,公理集为标准三条,无任何 Mathlib 解析引理;若窗口公共零点集相等需要黄金候选 twist 非零,则本义务的「任意候选」措辞为假,须收窄。
**边界**:结论中明写——不证明 eulerGerm 是非零 twist、不证明 O-5 分解、不识别 goldenTwist 为 eulerGerm 或 Zqc、不加强 RH;全局等价引理只在原族**全局**逐点非零时成立,窗口版不蕴含它;不 `import` 或调用 `o5_independence`。

## 四　预算与结算

三条各一席位轮(codex-cli,独立 worktree,各自 PR-1 deposit;cover 另开 PR-2,消费已在 base 的收据);任一席以 `open` 出口即在下一增订登记阻断面。W-G 的自然归属为 `Analytic/Adelic`(已满 24/24),落户于其裂桶兄弟 `Analytic/ReflectedSpectrum`(偶极的反射谱语境)或席位按路径策略选定的裂桶;W-E 与 W-F 落户 `Analytic/Toroidal`(W-B 所建)。

后续增订继续严格追加于本节之后。

---

# 增订七　主线第一步:`ZeroData` 非空洞性的精确边界(M1-a、M1-b)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;la101 第三波六席面板(codex ×2、GPT PRO ×2、隔离 subagent ×2,GPT PRO 与 codex 各有载体失败已在 #4589 逐席披露)收敛后由 orchestrator 撰写;研究探针为一席隔离 subagent(`lake env lean`,0 sorry,标准三公理),其证明文件存 orchestrator scratchpad,不入库。判决日:2026-09-02。lane issue:#4589。

## 〇　为什么是这一条

第三部 §四 立项裁决把「修复非空洞语义」列为 O-6 主线第一步;§M1 与 R-D 指出:凡对 `Z : ZeroData` 量化的 O-6 陈述,在 `ZeroData` 可居留性未定前皆可能空洞。探针把这个问题压缩成一条精确等价与一个具名缺口:可居留性**恰**等价于非平凡零点集无穷,而后者不在钉版 Mathlib 与本仓中。本增订只预登记可在钉版工具链闭合的那一半,并把另一半诚实记为缺失载体,不以公理补。

## 一　M1-a 预登记:`ZeroData` 可居留性等价于非平凡零点无穷(`ZeroDataNonemptyIffInfinite`)

**义务**:单一公开定理 `nonempty_zeroData_iff_infinite : Nonempty ZeroData ↔ {ρ : ℂ | IsNontrivialZero ρ}.Infinite`,其中 `ZeroData`、`IsNontrivialZero` 为冻结 `D5/S3/Weil/ZeroSum` 的定义。正向:`zero : ℕ → ℂ` 单射且逐项非平凡零点,故零点集无穷。反向:由钉版 Mathlib `NumberTheory/LSeries/ZetaZeros`(零点集闭、离散、紧交有限)与 Lindelöf 可数性得非平凡零点集可数,无穷可数集给出枚举;重数由 `analyticOrderAt` 的存在与唯一性给出;反射置换与共轭置换由 `riemannZeta_one_sub`、`riemannZeta_conj` 及重数守恒引理给出;局部有限由紧交有限给出。模块须消费上述 Mathlib 与冻结声明,不重证零点集拓扑。
**可证伪预测(写在跑之前)**:若正确,定理以 `Set.Countable`/`Denumerable` 枚举、`analyticOrderAt` 引理与 `Equiv.Perm` 构造在钉版工具链闭合,公理集为标准三条;若 `ZeroData` 的某一字段(如共轭置换的重数守恒)在钉版 Mathlib 无对应引理,则该字段名与所缺引理名记入下一增订,义务改标 `open`,不得削弱字段。
**边界**:本义务不证明零点集无穷,不给出任何一个零点,不主张 O-6 非空洞;它只把「非空洞」精确地归约为 M1-b。

## 二　M1-b 具名缺失载体(open,不派席):非平凡零点无穷

**缺口**:`nontrivialZeros_infinite : {ρ : ℂ | IsNontrivialZero ρ}.Infinite`。钉版 Mathlib `ZetaZeros.lean` 无 `Infinite` 或 $N(T)$ 下界;本仓 `D5/S3/Weil/ZetaRvm` 只有上界计数。其经典来源为 Hardy(1914)临界线上无穷零点或 Riemann–von Mangoldt 计数下界,属解析数论重型载体,不是初等波。
**可证伪预测(写在跑之前)**:若 M1-a 落地而 M1-b 仍缺,则本仓一切「∀ Z : ZeroData, …」形式的 O-6 陈述在 kernel 意义上仍是条件性的;主线「修复非空洞语义」的出口只有三种——上游 Mathlib 补入无穷性、本仓以外部形式化(标 `literature-attested` 并 import)接入、或在本卷显式改写 O-6 为以 `Set.Infinite` 为前件的条件陈述;**不得**以公理或 `ASSUMED-UNVERIFIED` 冒充已闭合。
**边界**:本节不是义务,不占席位;它只使 R-D 的「空类型诊断」有了精确的判据。

## 三　预算与结算

M1-a 一席位轮(codex-cli,独立 worktree,PR-1 deposit;cover 另开 PR-2);M1-b 不占预算,待 owner 在三种出口中裁决。

后续增订继续严格追加于本节之后。

---

# 增订八　R-F 路线勘误与 M2 枚举不变性(M2-a、M2-b、M2-c)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;R-F 探针一席(codex-cli,`lake env lean`,0 sorry,标准三公理)与 M2 探针一席(codex-cli,同上)在暖树上整证后由 orchestrator(claude 主循环)撰写,无面板席;两份证明文件存 orchestrator scratchpad,不入库。判决日:2026-09-02。lane issue:#4589。

## 〇　为什么是这一节

第三部 §四 立项裁决的主线第二步(RH ⟹ 本仓 O-6,R-F)已由探针整证并按 `GoldenObserverRoute` 转写先例落为 `D5/S3/Weil/ZetaBridge/RhImpliesWeilPositivity`(PR #4754);探针同时暴露了 §R-F 闭合路线文本的两处缺陷。atom 不可变,故勘误以本节追加发布,旧节一个字节不动。§M2 是主线第一步「修复非空洞语义」的另一半:`hZero` 前件的可派生性与枚举无关性。M2 探针证明它们在冻结栈上可闭合,且其中的收敛前件已由冻结的 `Zeta23.WeilEF` 绝对可和性直接给出——这使 O-6 的 `hZero` 从「调用者任选前件」变为可派生事实。

## 一　R-F 路线勘误(不改 atom,只追加)

**勘误一**:§R-F 闭合路线第 3 步引用的 `truncatedCriticalConvolutionSquareSum_re_nonnegative` 在 D5 不存在;实际冻结定理为 `D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine.critical_line_truncated_sum_real_nonnegative`。
**勘误二**:第 5–6 步不能经 `critical_offline_split_tendsto_explicit_formula` 闭合——该定理另需 `ArchimedeanConvergent (convolutionSquare g)` 前提且指向显式公式表达式;实际闭合用冻结的 `truncatedZeroSum_tendsto` 与闭集 `Set.Ici 0` 的极限引理。
**勘误三**:`o6WeilPositivityStatement` 定义于 `D5/X_Frontier/Hearts`,可冻结模块不得 import X_Frontier,故 R-F 的落地陈述是该定义体的逐字转写(定理名保留 atom 所给),并以导入 Hearts 的 scratch 文件 `exact` 出 `RiemannHypothesis → o6WeilPositivityStatement` 作忠实见证(exit 0,不入库)。
**边界**:本勘误不改变 §R-F 的义务、预测或科学接受门;R-F 在 `ZeroData` 空时亦形式成立,仍不得宣传为非空洞 Weil 正性结果。

## 二　M2-a 预登记:对称截断和的枚举不变性(`ZeroSumEnumerationInvariance`)

**义务**:公开定理 `truncatedZeroSum_enum_invariant (Z Z' : ZeroData) (g : WeilTestFunction) (T : ℝ) : truncatedZeroSum Z g T = truncatedZeroSum Z' g T`,其中 `ZeroData`、`truncatedZeroSum` 为冻结 `D5/S3/Weil/ZeroSum` 的定义。闭合路线:由 `zero_injective` 与 `zero_exhaustive` 得两枚举间的 `ℕ ≃ ℕ`(冻结 `ClassicExplicitFormula.zeroEquiv`),重数经 `multiplicity_eq_zeroMult` 一致,`symmetricIndices T` 沿该等价传输,`Finset.sum_equiv` 收尾。落点须在 `ClassicExplicitFormula` 下游(否则 import 成环),建议 `D5/S3/Weil/ZetaBridge/ZeroSumEnumerationInvariance`。
**可证伪预测(写在跑之前)**:若正确,定理只依赖 `ZeroSum`、`ClassicExplicitFormula` 两冻结模块与钉版 Mathlib 的有限和重排,公理集为标准三条;若某 `ZeroData` 字段不足以确定 `symmetricIndices` 的传输(例如 `gamma` 的定义不随枚举等价交换),则该字段名记入下一增订,义务改标 `open`。
**边界**:本义务不证明任何收敛,不涉及 `zeroSum`。

## 三　M2-b 预登记:`zeroSum` 与 `SymmetricConvergent` 的枚举不变性(同模块)

**义务**:同模块两条公开定理 `symmetricConvergent_enum_invariant (Z Z' : ZeroData) (g : WeilTestFunction) : SymmetricConvergent Z g ↔ SymmetricConvergent Z' g` 与 `zeroSum_enum_invariant (Z Z' : ZeroData) (g : WeilTestFunction) (h : SymmetricConvergent Z g) (h' : SymmetricConvergent Z' g) : zeroSum Z g h = zeroSum Z' g h'`,二者由 M2-a 与冻结的 `zeroSum_eq_of_tendsto`、`truncatedZeroSum_tendsto` 直接得出。
**可证伪预测(写在跑之前)**:若 M2-a 落地,则本义务在钉版工具链上为初等推论,公理集为标准三条;若 `zeroSum` 的 `choose` 定义使等式不可由极限唯一性得到,则记入下一增订并改标 `open`。
**边界**:不主张任何枚举是 canonical;只主张零点和不依赖枚举。

## 四　M2-c 预登记:每个 `ZeroData` 对每个 Weil 测试函数对称收敛(`SymmetricConvergentOfZetaSummable`)

**义务**:单一公开定理 `symmetricConvergent_of_zeroData (Z : ZeroData) (g : WeilTestFunction) : SymmetricConvergent Z g`。闭合路线:冻结的 `Zeta23.WeilEF.EF_lit_zetaZeroConfig` 给出重数加权零点项的绝对可和性;经 `ClassicExplicitFormula.zeroEquiv` 将其转写到 `Z` 的枚举,`HasSum` 沿等价传输,`tendsto_symmetricIndices` 把对称截断和的极限接到该和。落点 `D5/S3/Weil/ZetaBridge/`。
**可证伪预测(写在跑之前)**:若正确,定理为冻结重型结果的中等提取,公理集为标准三条,且 §M2 第 3 条(canonical `SymmetricConvergent`)由此**强于**原文(对所有 `g`,不限卷积平方);若 `EF_lit_zetaZeroConfig` 的光滑性/紧支前提与 `WeilTestFunction` 不匹配,则记所缺前提名并改标 `open`。
**边界**:本义务不改 O-6 的陈述;`hZero` 前件的消去(改写 O-6)是后续独立义务,须先经本条冻结。

## 五　预算与结算

M2-a/M2-b 一席位轮(同模块,codex-cli,独立 worktree,PR-1 deposit 绑 M2-a atom;M2-b 两 atom 以 PR-1b 收据绑定后 PR-2 cover),M2-c 一席位轮(独立模块)。勘误不占预算。

后续增订继续严格追加于本节之后。

---

# 增订九　M5 第 1 步勘误与 M3 separator 阶梯(M3-a、M3-b、M3-c;M3-d 具名缺口)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;研究席一席(GPT PRO,`chatgpt-pro-pool`,advisory,给出分解与文献)+ 探针两席(codex-cli,`lake env lean`,0 sorry,标准三公理:M5 探针、M3 探针),由 orchestrator(claude 主循环)核对约定并撰写;证明文件存 orchestrator scratchpad,不入库。判决日:2026-09-02。lane issue:#4589。

## 〇　为什么是这一节

第三部 §四 主线第四步要求「精确暴露 O-6 ⟹ RH 所需的 separator theorem」。研究席指出并经探针在 kernel 确认:对本仓测试类(实轴上偶、C^∞、紧支),separator 的障碍**不是偶性**而是**实轴零点**——离线非实零点的四点轨道可被偶测试函数强制为负,而实轴上的离线零点其轨道退化为两点、贡献恒非负。故 separator 的诚实形态必须显式带实轴排除依赖,而该依赖(实区间 (0,1) 上 ζ 非零)在钉版 Mathlib 与本仓皆缺。本节把阶梯前三级预登记为义务,第四级记为具名缺口。

## 一　M5 第 1 步勘误(不改 atom,只追加)

§M5 第 1 步「证明 `eulerGerm` 在 Re s>1/φ² 的收敛和解析性」相对 dev 已陈旧:`D5/S3/Analytic/EulerGerm/{GermProductConvergence,GermProductAnalytic,GoldenGermProductAbscissa}` 与 `D5/S3/Analytic/GoldenEulerBeta` 已冻结该步(并行控制线由其他驱动者推进,已含因子分解、延拓与零点集模块)。探针核实:β(0)=0、β(1)=φ²、缺口集恰为 {φ, φ²},绝对收敛横坐标恰为 1/φ²;唯一未落地的是 Hearts 字面索引 `eulerGerm` 到冻结 `germLocalFactor` 乘积的 13 行传输,不构成独立义务。本卷 lane 不进入并行控制线。

## 二　M3-a 预登记:指定谱值对使离线轨道贡献为负(`PrescribedPairNegativeOrbit`)

**义务**:公开定理 `prescribed_pair_gives_negative_zero_orbit (Z : ZeroData) (n : ℕ) (hOff : (Z.zero n).re ≠ criticalAbscissa) (hIm : (Z.zero n).im ≠ 0) (g : WeilTestFunction) (hz : fourierLaplace g (Z.gamma n) = 1) (hcz : fourierLaplace g (conj (Z.gamma n)) = -1) : (∑ k ∈ ({n, Z.reflection n, Z.conjugation n, Z.conjugation (Z.reflection n)} : Finset ℕ), zeroSummand Z (convolutionSquare g) k).re = -4 * (Z.multiplicity n : ℝ)`。闭合路线:`hIm` 给出共轭指标与 `n` 不同,与 `hOff` 一起由冻结 `zero_orbit_card_four_of_off_line` 得四指标互异;冻结 `off_line_zero_orbit_sum_eq_four_mul_re` 与 `convolutionSquare` 的变换因子分解 G(z)·conj G(conj z) 把实部化为 −4·重数。落点 `D5/S3/Weil/ZetaBridge/`。
**可证伪预测(写在跑之前)**:若正确,定理只消费冻结的轨道和与因子分解引理,公理集为标准三条;若四指标在某 `ZeroData` 下不互异(重数或置换退化),则定理对该情形为假,须以 `hIm` 之外的显式前提修正并记入下一增订。
**边界**:不构造任何测试函数;只把「指定两个谱值」翻译成轨道贡献的符号。

## 三　M3-b 预登记:偶测试函数变换的有限插值(`EvenTestFunctionFiniteInterpolation`)

**义务**:公开定理 `even_weilTestFunction_finite_interpolation (S : Finset ℂ) (hsep : ∀ ⦃z w : ℂ⦄, z ∈ S → w ∈ S → z ≠ w → z ≠ -w) (a : S → ℂ) : ∃ g : WeilTestFunction, ∀ z : S, fourierLaplace g z.1 = a z`。闭合路线:符号分离使 z ↦ z² 在 S 上单射;取缩放的偶紧支 seed,使其变换在所有节点非零;偶阶导数的变换为 (−1)^r z^{2r}·Φ(z),在平方节点上作 Lagrange 插值(Mathlib `Lagrange.interpolate`),复合得偶、C^∞、紧支的 g。落点 `D5/S3/Weil/TestFunctions/`(与冻结 `FinitePaleyWienerInterpolation` 同桶)。
**可证伪预测(写在跑之前)**:若正确,定理在钉版工具链闭合且不引入新公理;若某有限符号分离集上求值泛函线性相关(平方节点 Vandermonde 退化),则定理为假——这与 `hsep` 矛盾,故实际的可证伪面是「seed 变换在全部节点非零」这一步能否闭合。
**边界**:不控制 S 之外的谱值;不给出任何衰减估计。

## 四　M3-c 预登记:实轴离线零点的轨道贡献恒非负(与 M3-a 同模块)

**义务**:同模块两条公开定理 `real_off_line_zero_orbit_sum_re (Z : ZeroData) (n : ℕ) (hReal : (Z.zero n).im = 0) (hOff : (Z.zero n).re ≠ criticalAbscissa) (g : WeilTestFunction) : (∑ k ∈ ({n, Z.reflection n, Z.conjugation n, Z.conjugation (Z.reflection n)} : Finset ℕ), zeroSummand Z (convolutionSquare g) k).re = 2 * (Z.multiplicity n : ℝ) * Complex.normSq (fourierLaplace g (Z.gamma n))` 与 `prescribed_pair_impossible_for_real_zero (Z : ZeroData) (n : ℕ) (hReal : (Z.zero n).im = 0) (g : WeilTestFunction) (hz : fourierLaplace g (Z.gamma n) = 1) (hcz : fourierLaplace g (conj (Z.gamma n)) = -1) : False`。
**可证伪预测(写在跑之前)**:若正确,则对任何允许实轴离线零点的抽象 `ZeroData`,偶测试类上的 Weil 正性不能分离该零点——separator 在无实轴排除时为假,这是 kernel 可见的否定性事实;若某 `ZeroData` 的实轴零点轨道不退化为两点,则本条为假并须修正轨道基数引理的前提。
**边界**:本条不断言 zeta 有或没有实轴非平凡零点。

## 五　M3-d 具名缺失载体(open,不派席):非平凡零点不在实轴

**缺口**:`IsNontrivialZero.im_ne_zero {ρ : ℂ} (hρ : IsNontrivialZero ρ) : ρ.im ≠ 0`,即实 0<s<1 时 ζ(s) ≠ 0(经典:η(s)>0 且 ζ(s)=η(s)/(1−2^{1−s})<0)。钉版 Mathlib 仅有 `riemannZeta_ne_zero_of_one_le_re`;本仓 `D5/S3/Zeros/Symmetry/ZeroOrbitDegeneracy` 已记同一缺口。
**可证伪预测(写在跑之前)**:若 M3-a/b/c 落地而 M3-d 仍缺,则本仓任何形如「离线零点 ⟹ 存在负 Weil 平方和」的 separator 只能以 `(Z.zero n).im ≠ 0` 为显式前件陈述;**不得**以公理补入实轴排除。
**边界**:本节不是义务,不占席位。

## 六　预算与结算

M3-a/M3-c 一席位轮(同模块,codex-cli,独立 worktree,PR-1 deposit 绑 M3-a atom;M3-c 两 atom 以 PR-1b 收据后 PR-2 cover),M3-b 一席位轮(独立模块)。截断 separator(以 `symmetricIndices T` 为界)待三条冻结后另立增订。勘误与具名缺口不占预算。

后续增订继续严格追加于本节之后。

---

# 增订十　黄金 Euler germ 线:窗口内局部因子的零点(G-a、G-b 预登记;G-c 具名缺口;第 6 步疑似为假)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;方向修订由用户 2026-09-02 给出(「黄金 Euler germ 才是正经线路」);两席 codex-cli 探针(窗口数值扫描 + Lean 条件判据;零点认证可行性 + 字典引理,`lake env lean` exit 0,标准三公理),数值零点由 orchestrator 独立复算确认;由 orchestrator(claude 主循环)撰写。判决日:2026-09-02。lane issue:#4589。本节进入 `D5/S3/Analytic/EulerGerm/` 桶(其他驱动者活线),只做其尚未冻结的边。

## 〇　为什么是这一节

冻结的 `golden_germ_second_order_factorization` 给出 continuedGerm(s) = ζ(φ²s)·ζ(φ³s)·ζ(2φ²s)⁻¹·G3(s),G3 在 Re s > 1/φ⁴ 绝对收敛。绝对收敛乘积为零当且仅当某因子为零,故 §M5 第 6 步「严格窗口内无消去」精确等价于每个 `germLocalFactor s p` 在窗口内非零。**数值证据强烈指向该步为假**:p=2 的局部因子在 σ∈[0.12,0.40]、t∈[0,60] 内有 ≥10 个零点(如 s₀ ≈ 0.23815329946211908 + 5.256712292901926 i,80 位精度残差 ≤ 1e-57;orchestrator 以 float64、V=400 独立复算 |f₂(s₀)| ≈ 6e-16,邻点 ≈ 1e-2),p=3 有 12 个候选,p=5 无;在 s₀ 处三个 ζ 型因子的模为 0.287、0.947、0.553,故不是 ζ 因子的消去。**含义**:连续延拓的 germ 在窗口内有不来自 ζ 的零点,「窗口零点定位 ⟺ RH」必须改写为含局部因子零因子(= G3 零因子)的亚纯 divisor 恒等式。kernel 侧:实轴上局部因子恒非零;精确尾项阈值 σ₀ = 0.4311(冻结的 2/3 为粗切口);G3 延拓只到 Re s > 1/φ⁴ ≈ 0.146,窗口下沿 1/(2φ³) ≈ 0.118 尚无冻结覆盖。

## 一　G-a 预登记:G3 的零集等于局部因子零集之并(`LocalFactorZeroDivisor`)

**义务**:公开定理 `G3_eq_zero_iff_exists_local_factor_zero (s : ℂ) (hs : 1 / Real.goldenRatio ^ 4 < s.re) : (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))) * (1 + (p : ℂ) ^ (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ)))⁻¹ * germLocalFactor s p) = 0 ↔ ∃ p : Nat.Primes, germLocalFactor s p = 0`,乘积表达式与冻结 `golden_germ_second_order_factorization` 的 G3 逐字相同。闭合路线:冻结的偏差可和性给出绝对收敛;两个规范化因子由模 < 1 非零;钉版 Mathlib 的 `tprod` 零/非零引理收尾。落点 `D5/S3/Analytic/EulerGerm/`。
**可证伪预测(写在跑之前)**:若正确,定理只消费冻结的第二阶因子分解模块与钉版 Mathlib,公理集为标准三条;若 `tprod` 的零判据在钉版缺失或 G3 表达式与冻结 `let` 不同构,则记所缺引理名并改标 `open`。
**边界**:不断言任何局部因子有零点。

## 二　G-b 预登记:局部因子的解析性与最小模零点判据(同模块)

**义务**:同模块两条公开定理 `germLocalFactor_analyticOnNhd_pos (p : ℕ) (hp : p.Prime) : AnalyticOnNhd ℂ (fun s : ℂ => germLocalFactor s p) {s : ℂ | 0 < s.re}` 与 `exists_zero_in_ball_of_boundary_norm_gt_center {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (Metric.closedBall c r)) (hgap : ∀ z ∈ Metric.sphere c r, ‖f c‖ < ‖f z‖) : ∃ z ∈ Metric.ball c r, f z = 0`。闭合路线:后者由最大模原理施于 1/f(Mathlib `Analysis.Complex.AbsMax`);前者由局部一致收敛的级数解析性。
**可证伪预测(写在跑之前)**:若正确,二者在钉版工具链闭合且公理集为标准三条;若 `AbsMax` 的形式不支持闭球上 `AnalyticOnNhd` 的边界最大值陈述,则记所缺引理名并改标 `open`。
**边界**:本条把「认证一个零点」归约为两条不等式(中心上界、边界一致下界),不证明任何具体不等式。

## 三　G-c 具名缺失载体(open,不派席):s₀ 附近零点的 kernel 认证

**缺口**:`germLocalFactor_two_has_zero_near_candidate : ∃ z ∈ Metric.ball (⟨23815329946211908/10^17, 5256712292901926/10^15⟩ : ℂ) (1/10^8), germLocalFactor z 2 = 0`。由 G-b 归约为:存在有理 L 使 ‖germLocalFactor c 2‖ < L 且圆周上 L ≤ ‖germLocalFactor z 2‖。钉版 Mathlib 无 Rouché/辐角原理,亦无可供 kernel 使用的定向舍入超越函数包络(log 2、exp、sin/cos 的有理封闭);`norm_num`/`positivity`/`bound` 不提供该层。成本:一次性手工证书为重型;可复用管线需新基础设施。
**可证伪预测(写在跑之前)**:若 kernel 得到闭盘上 ‖germLocalFactor z 2‖ 的正下界,或圆周上零点计数为 0,则 G-c 为假且本节「第 6 步疑似为假」的数值判断须撤回;某一包络方法的失败本身不构成否证。
**边界**:本节不是义务,不占席位;零点的单性与唯一性未验证。

## 四　对 §M5 第 6–7 步的诚实改写(不改旧 atom)

在 G-c 认证之前,「窗口内无消去」记为 **疑似为假(数值)**;「窗口零点定位 ⟺ RH」的正确目标形态是:在 Re s > 1/φ⁴ 上,continuedGerm 的零因子 = ζ(φ²s)、ζ(φ³s) 的零因子 − ζ(2φ²s) 的零因子 + G3 的零因子,而 G-a 把最后一项化为局部因子零因子;RH 只约束前两项。任何省略 G3 零因子的「等价」陈述列入暂不接受的说法。

## 五　预算与结算

G-a/G-b 一席位轮(同模块,codex-cli,独立 worktree,PR-1 deposit 绑 G-a atom;G-b 两 atom 以 PR-1b 收据后 PR-2 cover);G-c 不占预算,待认证基础设施或 owner 裁决。

后续增订继续严格追加于本节之后。

---

# 增订十一　M3 separator 阶梯第四级:截断 separator(M3-e 预登记)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;探针一席(codex-cli,`lake env lean`,0 sorry,标准三公理,在 dev 新增量上整证)后由 orchestrator(claude 主循环)撰写;证明文件存 orchestrator scratchpad,不入库。判决日:2026-09-03。lane issue:#4589。

## 〇　为什么是这一节

增订九预登记的 M3-a(指定谱值对 ⇒ 离线轨道贡献 = −4·重数)、M3-b(偶测试函数变换的有限插值)、M3-c(实轴离线零点轨道恒非负)已全部冻结并消化闭合。研究席给出的阶梯第四级——以对称截断 `symmetricIndices T` 为界的 separator——探针在冻结栈上以精确陈述整证:用反射类代表点 rep(k)=min(k, reflection k) 构造符号分离的频率集,在目标轨道代表点插值 1/−1、其余轨道 0,由 M3-b 得 g;偶性把值传输到整个轨道,γ 的单射性使非零值只出现在目标四点;截断的反射/共轭封闭引理把四点全放进截断;M3-a 给出 −4·重数。**此级不含任何新的解析输入**;它把「离线零点 ⇒ 负 Weil 平方和」在有限截断内彻底闭合,剩下的只是极限(M3-f,重型:需 Burnol 式卷积幂与余项估计)。

## 一　M3-e 预登记:截断 separator(`OffLineZeroNegativeTruncatedWeilSquare`)

**义务**:单一公开定理 `offLineZero_yields_negative_truncated_weil_square (Z : ZeroData) (n : ℕ) (T : ℝ) (hn : n ∈ Z.symmetricIndices T) (hOff : (Z.zero n).re ≠ criticalAbscissa) (hIm : (Z.zero n).im ≠ 0) : ∃ g : WeilTestFunction, (truncatedZeroSum Z (convolutionSquare g) T).re < 0`。闭合路线:反射类代表点集 S 的符号分离性由代表点的极小性证得;冻结 `even_weilTestFunction_finite_interpolation` 给出 g;冻结 `fourierLaplace_convolutionSquare_complex`、`gamma_reflection`/`gamma_conjugation`、`reflection_mem_symmetricIndices`/`conjugation_mem_symmetricIndices`、`zero_symmetries_commute`、`mirror_index_fixed_iff_critical`、`multiplicity_pos` 与冻结 `prescribed_pair_gives_negative_zero_orbit` 收尾。落点 `D5/S3/Weil/ZetaBridge/`。
**可证伪预测(写在跑之前)**:若正确,定理只消费上列冻结声明与钉版 Mathlib 的有限和引理,公理集为标准三条;若某 `ZeroData` 的截断不在反射/共轭下封闭(与冻结封闭引理矛盾)或 γ 非单射,则本条为假并须修正前提。
**边界**:本条不涉及极限、不断言 `SymmetricConvergent`、不给出 `zeroSum` 的符号;`hIm` 是 M3-d 具名缺口(实轴排除)的显式替身,不得省略。

## 二　M3-f 具名目标(不在本节预登记):完整 separator

`offLineZero_yields_negative_weil_square (Z) (hOff : ∃ n, (Z.zero n).re ≠ criticalAbscissa) : ∃ g, ∃ hZero, (zeroSum Z (convolutionSquare g) hZero).re < 0`——由 M2-c 知 `hZero` 对所有 g 成立,故只差极限:须控制截断外零点的贡献(Burnol 式卷积幂 g^{⋆N} 使目标轨道贡献 −4·重数·1 而其余衰减为 O(4^{−N}))。所需解析输入:有界带上变换的衰减估计与卷积幂的变换公式;记为下一增订的探针对象,成本重型。

## 三　预算与结算

M3-e 一席位轮(codex-cli,独立 worktree,PR-1 deposit;cover 另开 PR-2);M3-f 不占本节预算。

后续增订继续严格追加于本节之后。

---

# 增订十二　黄金 germ 线:局部因子的通用缩放与 G3 的 sharp 横坐标(G-d、G-e 预登记;G-f、G-g 具名目标)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;研究席一席(GPT PRO,advisory:给出分解与文献)+ 探针一席(codex-cli,`lake env lean`,0 sorry,标准三公理,含 β 值的 kernel 证书),关键代数由 orchestrator 独立验算(β(3)=2+3φ=φ⁴、β(4)=3+4φ=2φ³+1、β(5)=φ⁵;缩放检验 f₅((log2/log5)·s₀)≈0);由 orchestrator(claude 主循环)撰写。判决日:2026-09-03。lane issue:#4589。

## 〇　为什么是这一节

增订十把 G3 的零集化为局部因子零集之并,并以数值证据指出 p=2、3 的局部因子在窗口内有零点。本节记录两条把这一现象**结构化**的初等事实:①所有局部因子是同一个整函数 Φ(z)=Σ_v e^{−β(v)z} 沿 z=(log p)s 的截取,故各 p 的零点集互为相似像(这解释了为何 p=5 在窗口内无零点:缩放因子 log 2/log 5 把 p=2 的零点压到窗口下方);②β(3)=φ⁴=φ²+φ³ 使前四项精确因子化为 (1+x)(1+y),φ⁴ 处的广义 Euler 系数恰为 0,G3 的领头修正项是 −p^{−2φ³s},其绝对收敛横坐标**恰为 1/(2φ³)——黄金窗口的下沿**(冻结的 1/φ⁴ 只是充分界)。这使第二阶因子分解精确覆盖整个严格窗口,补上了增订十指出的下切片缺口。

## 一　G-d 预登记:局部因子的通用缩放(`LocalFactorUniversalScaling`)

**义务**:公开定理 `germLocalFactor_prime_scaling (p q : Nat.Primes) (s : ℂ) : germLocalFactor s p = germLocalFactor ((((Real.log p / Real.log q : ℝ)) : ℂ) * s) q`。闭合路线:正实底 `cpow` 的主支恒等式 `(p:ℂ)^w = exp(w·log p)`(Mathlib `Complex.cpow_def_of_ne_zero`、`Complex.natCast_log`),逐项相等后 `tsum_congr`。落点 `D5/S3/Analytic/EulerGerm/`。
**可证伪预测(写在跑之前)**:若正确,定理只消费 `GoldenLocalFactor` 与钉版 Mathlib,公理集为标准三条;推论:任一 p 的零点 s₀ 给出 f_q 在 (log p/log q)·s₀ 的零点(数值已验)。若 `cpow` 对自然数底出现非主支相位,则本条为假并须改写为显式 `exp` 形。
**边界**:不断言任何零点存在。

## 二　G-e 预登记:次模展开与 G3 的 sharp 横坐标(同模块)

**义务**:同模块两条公开定理 `germLocalFactor_next_mode_expansion (s : ℂ) (p : Nat.Primes) (hs : 0 < s.re) : let x := (p:ℂ)^(-s·φ²); let y := (p:ℂ)^(-s·φ³); (1 - y) * (1 + x)⁻¹ * germLocalFactor s p - 1 = -y^2 + (1 - y) * (1 + x)⁻¹ * ∑' k : ℕ, (p:ℂ)^(-s * (o5Beta (k+4) : ℂ))` 与 `second_normalized_factor_deviation_norm_summable_sharp (s : ℂ) (hs : 1 / (2 * Real.goldenRatio ^ 3) < s.re) : Summable (fun p : Nat.Primes => ‖(1 - (p:ℂ)^(-s·φ³)) * (1 + (p:ℂ)^(-s·φ²))⁻¹ * germLocalFactor s p - 1‖)`(表达式与冻结 `let G3` 的因子逐字相同)。闭合路线:o5Beta 0..3 = 0, φ², φ³, φ⁴ 与 (1+x)(1+y)=1+x+y+xy;Re s>0 上 ‖x‖<1;四模 tsum 拆分;尾项由冻结 `o5_beta_growth`/`o5_beta_power_law` 与不等式 2φ³+1+k ≤ o5Beta(k+4) 控制;`Nat.Primes.summable_rpow` 以指数 2φ³·Re s > 1 收尾。
**可证伪预测(写在跑之前)**:若正确,G3 在 Re s > 1/(2φ³) 绝对收敛,第二阶因子分解可延拓至整个严格窗口;若 o5Beta 4 ≠ 2φ³+1 或尾项下界不成立,则 sharp 横坐标不同于 1/(2φ³),须以实际值改写。
**边界**:本条不重做冻结的第二阶因子分解本身,只给出其收敛域的精确边界;将因子分解延拓到 Re s > 1/(2φ³) 的定理另立义务。

## 三　具名目标(不在本节预登记)

- **G-f**:p ≥ 5 时局部因子在拉回临界线 σ = 1/(2φ²) 上非零(三角界:前三模精确 + 增长界,中等);数值:p=2、3 在 σ=1/(2φ²)、|t|≤60 的最小模分别 0.0144、0.0102(非零,但无 kernel 界)。
- **G-g**:修正的 RH 等价形:令 D_primary := D_cg − D_3 + D_22 − D_loc(divisor 记号,`MeromorphicOn.divisor`),则 D_primary = D_2,且 RH ⟺ U 上所有 D_primary>0 的点实部 = 1/(2φ²)。重型;须先冻结 divisor 恒等式。
- **G-c**(增订十)仍 open。

## 四　预算与结算

G-d/G-e 一席位轮(同模块,codex-cli,独立 worktree,PR-1 deposit 绑 G-d atom;G-e 两 atom 以 PR-1b 收据后 PR-2 cover)。具名目标不占预算。

后续增订继续严格追加于本节之后。

---

# 增订十三　G-f 与 M3-f 第二级预登记(临界线上 p ≥ 5 局部因子非零;测试函数变换的闭带衰减)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;研究席一席(GPT PRO 公司池,advisory,M3-f 极限步阶梯)+ 探针两席(codex-cli,`lake env lean`,0 sorry,标准三公理:G-f 探针 522 行、M3-f 前两级探针),由 orchestrator(claude 主循环)撰写。判决日:2026-09-03。lane issue:#4589。

## 〇　为什么是这一节

增订十二把「p ≥ 5 时局部因子在拉回临界线上非零」列为具名目标 G-f;探针以精确陈述整证(前四模精确 + 冻结 √5 斜率增长界,有理包络 599/600),故本节预登记为义务。增订十一把完整 separator 记为具名目标 M3-f;研究席给出的阶梯第一级(卷积幂的变换公式)经探针核实**已在冻结模块 `D5/S3/Fourier/ConvolutionPowerAmplification` 中**(`fourierLaplace_convolve_complex`、`convolutionSuccPower`、`fourierLaplace_convolutionSuccPower`),不另立义务、只绑定;第二级——测试函数变换在闭带 |Im w| ≤ η 上的一致衰减 C/(1+Re w²)——探针整证,本节预登记。研究席特别指出:极限步所需的是**闭带**一致估计,只在更小带成立的引理不够(零点频率可逼近带边)。

## 一　G-f 预登记:p ≥ 5 时局部因子在拉回临界线上非零(`LocalFactorCriticalLineNonvanishing`)

**义务**:单一公开定理 `germLocalFactor_critical_line_nonzero_of_five_le {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (t : ℝ) : germLocalFactor ((((1 / (2 * Real.goldenRatio ^ 2) : ℝ) : ℂ) + Complex.I * (t : ℂ))) p ≠ 0`。闭合路线:三角不等式 ‖f_p‖ ≥ 1 − Σ_{v≥1} p^{−σ₀β(v)},σ₀=1/(2φ²);前四模用冻结 `o5_beta_closed_form` 精确求值(p^{−1/2}, p^{−φ/2}, p^{−φ²/2}, …),v ≥ 4 的尾项由冻结 `o5_beta_growth`(√5 斜率)化为几何级数;p=5 时总和 < 1 的有理证书 599/600;更大素数单调更好。落点 `D5/S3/Analytic/EulerGerm/`。
**可证伪预测(写在跑之前)**:若正确,定理只消费 `GoldenLocalFactor`/`GoldenEulerBeta` 与钉版 Mathlib 的 rpow 单调性,公理集为标准三条;数值余量 p=5: 0.040、p=7: 0.279、p=11: 0.489。若某 t 使 p=5 局部因子在该线上为零,则本条为假且三角界的某一项估计必错。
**边界**:不对 p=2、3 作任何断言(二者在 |t| ≤ 60 数值非零,最小模 0.0144 / 0.0102,无 kernel 界);h-only 的三角引理在 s=0 处为假(两个发散 tsum 均取 0),故任何通用三角引理须带 0 < Re s。

## 二　M3-f 第二级预登记:测试函数变换的闭带衰减(`FourierLaplaceClosedStripDecay`)

**义务**:单一公开定理 `fourierLaplace_decay_closedStrip (b : WeilTestFunction) (η : ℝ) (hη : 0 ≤ η) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, |w.im| ≤ η → ‖fourierLaplace b w‖ ≤ C / (1 + w.re ^ 2)`。闭合路线:紧支给出 ‖exp(−I w x)‖ ≤ exp(η|x|);两次分部积分(Mathlib `integral_mul_deriv_eq_deriv_mul_of_integrable`、`ContDiff.iterate_deriv`、`HasCompactSupport.deriv`)得 ‖(I w)² B(w)‖ ≤ ∫ exp(η|x|)‖b''‖;取 C = C₀ + C₂(C_j = ∫ exp(η|x|)‖b^{(j)}‖)并用 |w|² ≥ Re w² 收尾。落点 `D5/S3/Weil/TestFunctions/`(或 `D5/S3/Weil/`,与 `FourierLaplace` 同层)。
**可证伪预测(写在跑之前)**:若正确,定理只消费 `TestFunctions`/`FourierLaplace` 与钉版 Mathlib,公理集为标准三条;若分部积分的边界项因支撑非紧而不消失(与 `WeilTestFunction` 定义矛盾),则本条为假。
**边界**:不涉及零点、不涉及 zeroSum;η 任意非负,极限步取 η = 1/2。

## 三　具名目标(不在本节预登记)

- **M3-f-3**:峰函数 b 与有限例外 killer k 的存在(`exists_peak_and_finite_exception_killer`):B(γ_n)=B(conj γ_n)=1,K(γ_n)=1,K(conj γ_n)=−1,K 在有限例外轨道上为 0,且例外集外 ‖B‖ ≤ 1/2(由第二级衰减 + 局部有限)。中等。
- **M3-f-4**:`burnol_power_tail_bound`——g_N = b^{⋆N} ⋆ k 的轨道外 tsum ≤ 4^{−N}·(convolutionSquare k 的绝对可和 majorant,来自冻结 `EF_zero_sum_summable`)。**承重引理,重型**。
- **M3-f-5**:完整 separator(取 N 使 4^{−N}S < 4·重数,严格)。重型。
- **G-g**(增订十二)、**G-c**(增订十)、**M3-d**(增订九)仍 open。

## 四　预算与结算

G-f 一席位轮、M3-f 第二级一席位轮(各 codex-cli,独立 worktree,PR-1 deposit;cover 另开 PR-2);具名目标不占预算。

后续增订继续严格追加于本节之后。

---

# 增订十四　M3 separator 阶梯收口:完整 separator(M3-f-3、M3-f-4、M3-f-5 预登记)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;研究席一席(GPT PRO 公司池,advisory,阶梯设计)+ 探针一席(codex-cli,`lake env lean`,0 sorry,标准三公理,828 行,在 dev 新增量上整证第 3–5 级);由 orchestrator(claude 主循环)撰写。判决日:2026-09-03。lane issue:#4589。

## 〇　为什么是这一节

增订十一预登记的截断 separator(M3-e)与增订十三预登记的闭带衰减(M3-f 第二级)之后,只剩极限步。探针按研究席的路线 A 在冻结栈上一次整证了第 3–5 级:峰函数 b 与有限例外 killer k 的存在;Burnol 卷积幂的轨道外尾项界 4^{−(N+1)}·majorant(majorant 由冻结 `EF_lit_zetaZeroConfig` 的绝对可和性传输到任意 `ZeroData`,与 M2-c 同一机制);以及**完整 separator**:离线非实零点 ⇒ 存在偶测试函数使 `zeroSum` 实部严格为负。与冻结的 R-F(RH ⇒ 本仓 O-6 正性)合起来,对本仓测试类而言,「偶测试类上的 Weil 正性 ⟺ 所有非实零点在临界线」只差 M3-d(实轴零点排除)这一条经典事实——本节**不**断言该等价,只预登记三条定理。

## 一　M3-f-5 预登记:完整 separator(`OffLineNonrealZeroNegativeWeilSquare`)

**义务**:公开定理 `offLineNonrealZero_yields_negative_weil_square (Z : ZeroData) (n : ℕ) (hOff : (Z.zero n).re ≠ criticalAbscissa) (hIm : (Z.zero n).im ≠ 0) : ∃ g : WeilTestFunction, ∃ hZero : SymmetricConvergent Z (convolutionSquare g), (zeroSum Z (convolutionSquare g) hZero).re < 0`。闭合路线:M3-f-3 给出 b、k、E;令 S := Σ'_j ‖zeroSummand Z (convolutionSquare k) j‖(由冻结 EF 可和性有限);取 N 使 (1/4)^{N+1}·S < 4·重数;g := convolve (convolutionSuccPower b N) k;`SymmetricConvergent` 由冻结 M2-c 给出;把绝对收敛的全和拆为轨道 + 补集:轨道贡献 = −4·重数(冻结 M3-a 与卷积幂变换公式),补集由 M3-f-4 界住;实部严格为负。落点 `D5/S3/Weil/ZetaBridge/`(或按容量规则分桶)。
**可证伪预测(写在跑之前)**:若正确,定理只消费冻结的 `ConvolutionPowerAmplification`、`EvenTestFunctionFiniteInterpolation`、`PrescribedPairNegativeOrbit`、`SymmetricConvergentOfZetaSummable`、闭带衰减(增订十三)与钉版 Mathlib,公理集为标准三条;若卷积幂在本仓测试类中不封闭、或 EF 可和性不能传输到任意 `ZeroData` 的 `zeroSummand`,则本条为假并须记所缺引理。
**边界**:`hIm` 不可省略(M3-d 具名缺口);本条不断言 O-6 ⟹ RH,不断言任何零点存在。

## 二　M3-f-3 与 M3-f-4 预登记(同模块两条公开定理)

**义务**:`exists_peak_and_finite_exception_killer (Z : ZeroData) (n : ℕ) (hOff : (Z.zero n).re ≠ criticalAbscissa) (hIm : (Z.zero n).im ≠ 0) : ∃ b k : WeilTestFunction, ∃ E : Finset ℕ, (∀ j, j ∈ E ↔ Z.reflection j ∈ E) ∧ (∀ j, j ∈ E ↔ Z.conjugation j ∈ E) ∧ zeroOrbit Z n ⊆ E ∧ fourierLaplace b (Z.gamma n) = 1 ∧ fourierLaplace b (conj (Z.gamma n)) = 1 ∧ fourierLaplace k (Z.gamma n) = 1 ∧ fourierLaplace k (conj (Z.gamma n)) = -1 ∧ (∀ j ∉ E, ‖fourierLaplace b (Z.gamma j)‖ ≤ 1 / 2 ∧ ‖fourierLaplace b (conj (Z.gamma j))‖ ≤ 1 / 2) ∧ (∀ j ∈ E, j ∉ zeroOrbit Z n → fourierLaplace k (Z.gamma j) = 0 ∧ fourierLaplace k (conj (Z.gamma j)) = 0)` 与 `burnol_power_tail_bound (Z : ZeroData) (n : ℕ) (b k : WeilTestFunction) (E : Finset ℕ) (N : ℕ) (hB : ∀ i ∉ E, ‖fourierLaplace b (Z.gamma i)‖ ≤ 1 / 2 ∧ ‖fourierLaplace b (conj (Z.gamma i))‖ ≤ 1 / 2) (hK : ∀ i ∈ E, i ∉ zeroOrbit Z n → fourierLaplace k (Z.gamma i) = 0 ∧ fourierLaplace k (conj (Z.gamma i)) = 0) : Summable (fun j : {j : ℕ // j ∉ zeroOrbit Z n} => zeroSummand Z (convolutionSquare (convolve (convolutionSuccPower b N) k)) j.1) ∧ ‖∑' j : {j : ℕ // j ∉ zeroOrbit Z n}, zeroSummand Z (convolutionSquare (convolve (convolutionSuccPower b N) k)) j.1‖ ≤ (1 / 4 : ℝ) ^ (N + 1) * ∑' j : ℕ, ‖zeroSummand Z (convolutionSquare k) j‖`(`zeroOrbit` 为本仓已有或本模块定义的四点轨道 Finset;若为本模块新定义,须在同模块以消费它的定理使其 earn its freeze)。
**可证伪预测(写在跑之前)**:若正确,二者在钉版工具链闭合且公理集为标准三条;若 E = symmetricIndices R 的反射/共轭封闭性不成立(与冻结封闭引理矛盾),或闭带衰减的常数依赖于 t,则本条为假。
**边界**:M3-f-3 的 E 是有限例外集,不断言其大小;M3-f-4 的界对每个 N 成立,不断言最优常数。

## 三　预算与结算

一席位轮(同模块三条公开定理,codex-cli,独立 worktree;deposit 绑 M3-f-5 atom;M3-f-3/4 走 PR-1b 收据后 PR-2 cover);该 lane 须在增订十三的闭带衰减模块合入后开工,以绑定而非重证。

后续增订继续严格追加于本节之后。
---

# 增订十五　黄金 germ 线 G-g:窗口零点除子与 RH 的修正等价(G-g-1 / G-g-2 / G-g-3 预登记)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;探针一席(codex-cli,`lake env lean`,0 sorry,标准三公理,274 行,在 `Zeta23`/钉版 Mathlib 上整证三条);去重检索由同席执行(`git grep -iE 'RiemannHypothesis' -- 'D5/**/*.lean'`:命中 `Observer/RiemannNamingStabilityReduction`、`CayleyLaguerre/CompactifiedSquaredDistanceSupport`、`TestFunctions/LiCurvatureCriterion`,均为与 germ 无关的 RH ↔ 判据,无等价或更强者);散文由 orchestrator(claude 主循环)撰写。判决日:2026-09-03。lane issue:#4589。

## 〇　为什么不是「窗口内零点全在线上 ⟺ RH」

冻结的三阶分解(`golden_germ_third_order_factorization`)在 Re s > 1/φ⁵ 上把唯一延拓 germ 写成 ζ(φ²s)·ζ(φ³s)·ζ(2φ²s)⁻¹·(ζ(2φ³s)⁻¹·ζ((2φ²+φ³)s)·G3(s))。在开窗口 W = {1/(2φ³) < Re s < 1/φ²} 内逐因子核算:ζ(φ²s) 的零点回拉到 Re s = β/φ²,RH 下恰在 Re s = 1/(2φ²);ζ(φ³s) 的零点回拉到 β/φ³,RH 下落在 W 的下边界 1/(2φ³)(开窗口不含);ζ(2φ²s)⁻¹ 的极点回拉到 β/(2φ²) < 1/(2φ³)(RH 下不在 W),但 ζ(2φ²s) 在 s = 1/(2φ²) 的极点使该倒数因子在线上贡献一个实零点;ζ(2φ³s)⁻¹ 与 ζ((2φ²+φ³)s) 在 W 内回拉实部 > 1,无零点;ζ(φ³s) 在 s = 1/φ³ ∈ W 有极点(Mathlib 的 `riemannZeta 1` 取有限值,故延拓 germ 作为全函数在该点取的是约定值)。剩下 G3:增订十/十二已数值证实 p = 2, 3 的局部因子在 W 内有零点,而 G3 的零点恰由局部因子零点构成,故 **G3 在 W 内确实消失**,「germ 在 W 内的零点全在线上」本身对 RH 既非必要亦非充分。修正后的三条:(1) RH ⟹ W 内 **G3 不消失处** 的 germ 零点全在 Re s = 1/(2φ²);(2) 逆向须附加「G3 在右半带零点的回拉点不消失」这一未知假设,否则一个恰与局部因子零点重合的离线 ζ 零点不产生见证;(3) 右半带无零点 ⟹ 完整 RH,由函数方程给出。三条都对任意 G : ℂ → ℂ 陈述(G-g-1/2),把冻结 G3 的实例化留作推论,以免在义务里复制 `let` 绑定的乘积表达式。

## 一　G-g-1 预登记:RH ⟹ 窗口内残余无零点处的零点线约束(`GoldenGermWindowZeroCriterion`)

**义务**:公开定理 `golden_window_zero_on_line_of_rh (hRH : RiemannHypothesis) (G : Complex -> Complex) (s : Complex) (hlo : 1 / (2 * Real.goldenRatio ^ 3) < s.re) (hhi : s.re < 1 / Real.goldenRatio ^ 2) (hzero : riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s) * riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s) * (riemannZeta (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s))⁻¹ * ((riemannZeta (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s))⁻¹ * riemannZeta ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) : Complex) * s)) * G s) = 0) (hG : G s ≠ 0) : s.re = 1 / (2 * Real.goldenRatio ^ 2)`。闭合路线:`mul_eq_zero`/`inv_eq_zero` 拆因子;ζ(φ²s) = 0 由冻结 `Zeta23.RH_implies_on_line`(或 Mathlib `RiemannHypothesis` 直接)得 Re(φ²s) = 1/2;ζ(φ³s) = 0 同理得 Re s = 1/(2φ³) 与 hlo 矛盾;ζ(2φ²s) = 0 时 Re(2φ²s) ∈ (1/φ, 2):≥ 1 由 `riemannZeta_ne_zero_of_one_le_re` 排除,< 1 由 RH 得 1/2 < 1/φ 矛盾,而 2φ²s = 1 恰给出结论;其余两个 ζ 因子回拉实部 > 1;G s = 0 由 hG 排除。落点 `D5/S3/Analytic/EulerGerm/`(origin/dev 现 19/24)。
**可证伪预测(写在跑之前)**:若正确,定理只消费 `D5.S3.Weil.ZetaCore.Statement`、`Mathlib.NumberTheory.LSeries.Nonvanishing`、`Mathlib.NumberTheory.Real.GoldenRatio`,公理集为标准三条;若 Mathlib 的 `RiemannHypothesis` 定义不含 `s ≠ 1` 侧条件、或 `riemannZeta 1 = 0` 使 2φ²s = 1 情形不可判,则本条按 open 记。
**边界**:本条对任意 G 成立,不断言 G3 的任何性质;不断言 RH;窗口是开区间,ζ(φ³s) 回拉到下边界的零点不在射程内。

## 二　G-g-2 预登记:条件逆命题(右半带,同模块第二条公开定理)

**义务**:公开定理 `golden_window_zero_right_half_strip_converse (G : Complex -> Complex) (hResidual : forall rho : Complex, riemannZeta rho = 0 -> (1 : Real) / 2 < rho.re -> rho.re < 1 -> G (rho / ((Real.goldenRatio ^ 2 : Real) : Complex)) ≠ 0) (hConfinement : forall s : Complex, 1 / (2 * Real.goldenRatio ^ 3) < s.re -> s.re < 1 / Real.goldenRatio ^ 2 -> riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s) * riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s) * (riemannZeta (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s))⁻¹ * ((riemannZeta (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s))⁻¹ * riemannZeta ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) : Complex) * s)) * G s) = 0 -> G s ≠ 0 -> s.re = 1 / (2 * Real.goldenRatio ^ 2)) : forall rho : Complex, riemannZeta rho = 0 -> (1 : Real) / 2 < rho.re -> rho.re < 1 -> False`。闭合路线:取 s := ρ/φ²,由 1/2 < Re ρ 得 1/(2φ) < Re ρ 故 s ∈ W;乘积首因子 ζ(φ²·ρ/φ²) = ζ ρ = 0(`mul_div_cancel_left₀`);hResidual 给 G s ≠ 0;hConfinement 得 Re s = 1/(2φ²) 即 Re ρ = 1/2,与 1/2 < Re ρ 矛盾。
**可证伪预测(写在跑之前)**:若正确,标准三公理、零 sorry;若 W 的下边界 1/(2φ³) 与 1/(2φ) 的比较方向写反(须 1/(2φ) > 1/(2φ³)·φ²… 即 β > 1/(2φ) ≈ 0.309 蕴含 s ∈ W),则本条为假。
**边界**:hResidual 是**未知假设**(G3 在回拉点不消失),本条不断言其成立,也不断言 G3 的零点集;结论只是右半带无零点,完整 RH 由 G-g-3 接手。

## 三　G-g-3 预登记:右半带无零点 ⟹ RH(`RightHalfStripRiemannReduction`,落 `D5/S3/Weil/ZetaBridge/`)

**义务**:公开定理 `golden_right_half_strip_implies_rh (hRight : forall rho : Complex, riemannZeta rho = 0 -> (1 : Real) / 2 < rho.re -> rho.re < 1 -> False) : RiemannHypothesis`。闭合路线:Re ρ ≥ 1 由 `riemannZeta_ne_zero_of_one_le_re` 排除;1/2 < Re ρ < 1 由假设排除;0 < Re ρ < 1/2 以 `riemannZeta_one_sub`(s := 1 − ρ)反射到右半带;Re ρ ≤ 0 时 ρ ≠ 0(`riemannZeta_zero`),对 t := 1 − ρ 用函数方程,ζ t、Γ t(`Complex.Gamma_ne_zero_of_re_pos`)、(2π)^(−t)(`Complex.cpow_def_of_ne_zero` + `Complex.exp_ne_zero`)皆非零,故 cos(πt/2) = 0,`Complex.cos_eq_zero_iff` 给出 ρ = −2(n+1),与 Mathlib 的非平凡性矛盾。落点 `D5/S3/Weil/ZetaBridge/`(origin/dev 现 20/24)。
**可证伪预测(写在跑之前)**:若正确,定理只消费钉版 Mathlib(`riemannZeta_one_sub`、`riemannZeta_ne_zero_of_one_le_re`、`riemannZeta_zero`、`Complex.cos_eq_zero_iff`),标准三公理;若 `riemannZeta_one_sub` 的侧条件 `s ≠ -n` 在 Re ρ ≤ 0 分支中不可满足(t = 1 − ρ 的实部 ≥ 1,故可满足),则本条为假。
**边界**:本条是纯 Mathlib 归约,不含黄金结构;它把 G-g-2 的结论升为完整 RH,但 G-g-2 的 hResidual 仍是未知假设,故三条合起来**不构成 RH 的证明路径**,只把「germ 窗口除子 ⟺ RH」的真实缺口定位到 G3 在回拉点的非消失性(G-c 类问题的对偶)。

## 四　预算与结算

两席位轮,可并行:席 A 在 `EulerGerm/GoldenGermWindowZeroCriterion.lean` 同模块证 G-g-1 与 G-g-2(deposit 绑 G-g-1 atom;G-g-2 走 PR-1b 收据后 PR-2 cover);席 B 在 `ZetaBridge/RightHalfStripRiemannReduction.lean` 证 G-g-3(deposit 绑其 atom)。二者互不依赖。

后续增订继续严格追加于本节之后。
---

# 增订十六　M3-d 缺口的阶梯:ζ 在 (0,1) 无实零点(M3-d-1 / M3-d-2 / M3-d-3 / M3-d-4 预登记)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;探针一席(codex-cli,`lake env lean`,125 行,标准三公理):在钉版 Mathlib 上**未找到** Dirichlet eta / 交错 ζ 级数在 0 < Re s 上的延拓恒等式(逐条检索 `LSeries`、`HurwitzZetaEven`(`hasSum_nat_cosZeta` 等皆要求 1 < Re s)、`riemannZeta_one_sub`、`completedRiemannZeta0`),故 M3-d-1 为**本仓须自证**的新引理;探针已在该恒等式为假设的条件下整证 M3-d-2、M3-d-3,并无条件证得 M3-d-4。散文由 orchestrator(claude 主循环)撰写。判决日:2026-09-03。lane issue:#4589。

## 〇　为什么是这一节

增订九把「非平凡零点无实零点」记为具名缺口 M3-d;增订十一(M3-e)与增订十四(M3-f-5)的 separator 因此都带 `hIm : (Z.zero n).im ≠ 0`。经典事实是:对实 0 < x < 1,(1 − 2^{1−x}) ζ(x) = Σ (−1)^n (n+1)^{−x}(交错级数,项递减趋零,和为正),而 1 − 2^{1−x} < 0,故 ζ(x) < 0 ≠ 0。钉版 Mathlib 只在 Re s > 1 给出 ζ 的级数表示;交错级数在 0 < Re s 的**部分和极限**等于 (1 − 2^{1−s}) ζ(s) 这一延拓恒等式(M3-d-1)须在本仓证明。它不是黄金结构,是纯 Mathlib 内容;证出即可去掉两条 separator 的 `hIm`。**参考路线(非义务,供实施席选择)**:(a) Re s > 1 时由 `zeta_eq_tsum_one_div_nat_add_one_cpow` 拆偶奇项得恒等式;(b) 交错部分和在 {0 < Re s} 上局部一致收敛(配对相邻项得绝对收敛的差分级数,用 `Complex.cpow` 的 Lipschitz 型估计),故极限函数在该半平面解析;(c) 右侧 (1 − 2^{1−s}) ζ(s) 在 {0 < Re s} 解析(`differentiableAt_riemannZeta`,s = 1 处两侧皆取有限值);(d) 由 `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` 从 Re s > 1 延拓到 0 < Re s。探针估计 250–450 行;若 (b) 的局部一致性在钉版 API 下不可达,本条按 open 记,不得以 `sorry` 或公理代替。

## 一　M3-d-1 预登记:交错级数的延拓恒等式(`RealAxisNonvanishing`,落 `D5/S3/Weil/ZetaBridge/`)

**义务**:公开定理 `tendsto_alternating_partialSums_eta (s : ℂ) (hs : 0 < s.re) : Filter.Tendsto (fun N ↦ ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n * ((n + 1 : ℂ) ^ (-s))) Filter.atTop (nhds ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s))`。落点 `D5/S3/Weil/ZetaBridge/`(origin/dev 现 21/24;若满则 `D5/S3/Weil/ZetaCore/`)。
**可证伪预测(写在跑之前)**:若正确,定理只消费钉版 Mathlib(`riemannZeta` 的 Re s > 1 级数表示、`differentiableAt_riemannZeta`、解析延拓唯一性)与至多本仓 `ZetaCore`,公理集为标准三条;若交错部分和在 {0 < Re s} 的局部一致收敛在钉版 API 下写不出(探针标记的缺口),则本条为 open,不得降级为「Re s > 1 版」冒充。
**边界**:不断言 `tsum`(交错级数在 Re s ≤ 1 非无条件可和,`tsum` 会取 0);极限以部分和的 `Tendsto` 陈述;s = 1 处等式两侧按 Mathlib 约定的有限值成立。

## 二　M3-d-2 预登记:ζ 在 (0,1) 无实零点(同模块第二条公开定理)

**义务**:公开定理 `riemannZeta_ne_zero_of_real_mem_Ioo (x : ℝ) (h0 : 0 < x) (h1 : x < 1) : riemannZeta (x : ℂ) ≠ 0`。
**可证伪预测(写在跑之前)**:若正确,由 M3-d-1 取 s = x 实、交错级数 `Antitone.alternating_series_le_tendsto` 类引理给出极限 > 0(探针已在 M3-d-1 为假设时整证此步,43 行),1 − 2^{1−x} < 0 得 ζ(x) < 0;若 M3-d-1 为 open,本条随之 open。
**边界**:只覆盖开区间 (0,1);x = 1 为极点;x ≤ 0 见 M3-d-4。

## 三　M3-d-3 预登记:`ZeroData` 的非平凡零点虚部非零(同模块第三条公开定理)

**义务**:公开定理 `ZeroData.im_ne_zero (Z : ZeroData) (n : ℕ) (h : IsNontrivialZero (Z.zero n)) : (Z.zero n).im ≠ 0`(`ZeroData`、`IsNontrivialZero` 取 `D5/S3/Weil/ZeroSum.lean` 的定义:ζ ρ = 0 ∧ 0 < Re ρ ∧ Re ρ < 1)。
**可证伪预测(写在跑之前)**:若正确,由 M3-d-2 直接得到(虚部为零 ⟹ ρ 实 ⟹ 与 M3-d-2 矛盾;探针已整证此蕴含);此后 `OffLineZeroNegativeTruncatedWeilSquare` 与 M3-f-5 的 `hIm` 可由本条供给(推论另行增订,不在本节义务内)。
**边界**:本条不断言 `ZeroData` 非空(M1-b 仍 open),只是类型正确的蕴含。

## 四　M3-d-4 预登记:实轴上 (0,1) 之外的 ζ 零点皆平凡(同模块第四条公开定理;探针已无条件整证)

**义务**:公开定理 `riemannZeta_real_zero_outside_Ioo (x : ℝ) (hout : ¬ (0 < x ∧ x < 1)) (hz : riemannZeta (x : ℂ) = 0) : ∃ n : ℕ, x = -2 * (n + 1)`。
**可证伪预测(写在跑之前)**:若正确,只消费 `riemannZeta_ne_zero_of_one_le_re`、`riemannZeta_one_sub`、`riemannZeta_zero` 与本仓已冻结的完成 ζ 非零引理(探针用了 `ZetaRvm.CountByIntegral` 中的一条;实施席须 grep 其名并绑定,不得重证),标准三公理;若函数方程分支需要 x = 0 之外的额外侧条件而不可满足,则本条为假。
**边界**:与 M3-d-2 合起来给出实轴零点的完整分类,但不涉及非实零点。

## 五　预算与结算

一席位轮(codex-cli,独立 worktree,四条公开定理同模块;deposit 绑 M3-d-2 atom,其余三条走 PR-1b 收据后 PR-2 cover)。M3-d-1 为难点,给足 3 小时;若席位以 open 归位,把它的具名缺口(哪一步在钉版 API 下写不出)追加为增订,并保留 M3-d-4 单独 deposit。

后续增订继续严格追加于本节之后。
---

# 增订十七　黄金 germ 线 G-g 收口:三阶残余的零点恰为局部因子零点,RH 下延拓 germ 的窗口零点集(G-g-4 / G-g-5 / G-g-6 预登记)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;探针一席(codex-cli,`lake env lean`,标准三公理,以 `golden_window_zero_on_line_of_rh` 与三阶分解的可和性为显式假设整证三条——因该两模块在探针树未编译;实施席须改为直接消费冻结定理);去重由同席执行:dev 已有 `LocalFactorZeroDivisor.G3_eq_zero_iff_exists_local_factor_zero`,但它针对**二阶**残余,三阶残余无对应;`GermProductNonvanishing.germ_product_ne_zero_of_local_factors_ne_zero` 只在 Re s > 1/φ² 且针对原始乘积。散文由 orchestrator(claude 主循环)撰写。判决日:2026-09-03。lane issue:#4589。

## 〇　为什么是这一节

增订十五把「窗口零点 ⟺ RH」的真实缺口定位到三阶残余 G3 在回拉点的非消失性。本节证明 G3 的零点**恰**是局部因子的零点(Mathlib 的 `tprod_one_add_ne_zero_of_summable` + `tprod_of_exists_eq_zero`,配合冻结的偏差可和性;其余四个 Kp 因子在 Re s > 0 上因 |x|,|y| < 1 而非零),于是在 RH 下,延拓 germ 在开窗口内的零点集有一个**精确**描述:ζ(φ²s) 的回拉零点(必在线上)与局部因子零点之并。这把「残余不消失」这个抽象假设换成了「s 不是任何 p 的局部因子零点」这个可数值检验的条件;而 p = 2, 3 的局部因子零点在窗口内确实存在(增订十/十二),故窗口零点集**不只**是回拉的临界线零点——这是 germ 线对 RH 等价陈述的最终修正形态。**边界**:不断言线上的每个点都是零点;不断言局部因子零点与 ζ 回拉零点不重合;不构成 RH 的证明路径。**容量**:`D5/S3/Analytic/EulerGerm/` 现 22/24,本模块落地后 23/24;此后 germ 线新模块须开分桶(第 8 条裂由压力)。

## 一　G-g-4 预登记:G-g-1 对冻结三阶残余的实例化(`GoldenGermThirdOrderWindowZeroCriterion`,落 `D5/S3/Analytic/EulerGerm/`)

**义务**:公开定理 `golden_continued_germ_window_zero_on_line_of_rh (hRH : RiemannHypothesis) : let Kp : Complex -> Nat.Primes -> Complex := fun s p => let x := (p : Complex) ^ (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)); let y := (p : Complex) ^ (-s * ((Real.goldenRatio ^ 3 : Real) : Complex)); (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) * (1 - y) * (1 + x)⁻¹ * germLocalFactor s p; let G3 : Complex -> Complex := fun s => ∏' p : Nat.Primes, Kp s p; ∀ continuedGerm : {s : Complex // 1 / Real.goldenRatio ^ 5 < s.re} -> Complex, ((∀ s, 1 / Real.goldenRatio ^ 2 < s.1.re -> continuedGerm s = ∏' p : Nat.Primes, germLocalFactor s.1 p) ∧ (∀ s, continuedGerm s = riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) * riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s.1) * (riemannZeta (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s.1))⁻¹ * ((riemannZeta (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s.1))⁻¹ * riemannZeta ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) : Complex) * s.1)) * G3 s.1))) -> ∀ s, 1 / (2 * Real.goldenRatio ^ 3) < s.1.re -> s.1.re < 1 / Real.goldenRatio ^ 2 -> continuedGerm s = 0 -> G3 s.1 ≠ 0 -> s.1.re = 1 / (2 * Real.goldenRatio ^ 2)`。
**可证伪预测(写在跑之前)**:若正确,证明只是把冻结 `golden_germ_third_order_factorization` 第二合取的公式改写进 `golden_window_zero_on_line_of_rh`(G := G3),标准三公理;若 `let` 绑定的 Kp/G3 与冻结定理的字面不一致导致 `rw` 失败,则本条须按冻结字面修正而非改冻结。
**边界**:对任意满足公式的 `continuedGerm` 成立,不依赖 ∃! 的唯一性。

## 二　G-g-5 预登记:三阶残余为零 ⟺ 某局部因子为零(同模块第二条公开定理)

**义务**:公开定理 `golden_third_residual_eq_zero_iff_exists_local_factor_zero (s : Complex) (hs : 1 / Real.goldenRatio ^ 5 < s.re) : let Kp : Complex -> Nat.Primes -> Complex := fun s p => let x := (p : Complex) ^ (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)); let y := (p : Complex) ^ (-s * ((Real.goldenRatio ^ 3 : Real) : Complex)); (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) * (1 - y) * (1 + x)⁻¹ * germLocalFactor s p; let G3 : Complex -> Complex := fun s => ∏' p : Nat.Primes, Kp s p; G3 s = 0 ↔ ∃ p : Nat.Primes, germLocalFactor s p = 0`。
**可证伪预测(写在跑之前)**:若正确,消费冻结三阶分解的第一合取(‖Kp − 1‖ 可和)与 Mathlib `tprod_one_add_ne_zero_of_summable`、`tprod_of_exists_eq_zero`、`multipliable_one_add_of_summable`,标准三公理;若 Kp 的四个非局部因子在 Re s > 1/φ⁵ 上有零点(即 |x| 或 |y| ≥ 1),则本条为假——实际 |x| = p^{−φ² Re s} < 1。
**边界**:只在 Re s > 1/φ⁵ 陈述(三阶分解的定义域);不涉及零点重数。

## 三　G-g-6 预登记:RH 下延拓 germ 的窗口零点集(同模块第三条公开定理)

**义务**:公开定理 `golden_continued_germ_window_zero_iff_of_rh (hRH : RiemannHypothesis) : let Kp : Complex -> Nat.Primes -> Complex := fun s p => let x := (p : Complex) ^ (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)); let y := (p : Complex) ^ (-s * ((Real.goldenRatio ^ 3 : Real) : Complex)); (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) * (1 - y) * (1 + x)⁻¹ * germLocalFactor s p; let G3 : Complex -> Complex := fun s => ∏' p : Nat.Primes, Kp s p; ∀ continuedGerm : {s : Complex // 1 / Real.goldenRatio ^ 5 < s.re} -> Complex, (∀ s, continuedGerm s = riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) * riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s.1) * (riemannZeta (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s.1))⁻¹ * ((riemannZeta (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s.1))⁻¹ * riemannZeta ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) : Complex) * s.1)) * G3 s.1)) -> ∀ s, 1 / (2 * Real.goldenRatio ^ 3) < s.1.re -> s.1.re < 1 / Real.goldenRatio ^ 2 -> (continuedGerm s = 0 ↔ ((riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) = 0 ∧ s.1.re = 1 / (2 * Real.goldenRatio ^ 2)) ∨ ∃ p : Nat.Primes, germLocalFactor s.1 p = 0))`。
**可证伪预测(写在跑之前)**:若正确,由 G-g-4 与 G-g-5 加 RH 下其余四个 ζ 因子在窗口内非零(回拉实部 > 1/2 或 > 1)得到;若 ζ(φ³s) 在开窗口内于 RH 下仍有零点(回拉实部 = 1/(2φ³) 恰为下边界,不在开窗口),则本条为假。
**边界**:等价式右侧的「线上」子句必须与 ζ(φ²s) = 0 合取,不得把整条线并入零点集;s = 1/(2φ²) 处 ζ(2φ²s)⁻¹ 的行为按 Mathlib 约定值处理,若该点使等价式失效须如实报 open 并附反例。

## 四　预算与结算

一席位轮(codex-cli,独立 worktree,三条公开定理同模块;deposit 绑 G-g-6 atom,G-g-4/5 走 PR-1b 收据后 PR-2 cover)。实施须 import 冻结的 `GoldenGermThirdOrderFactorization` 与 `GoldenGermWindowZeroCriterion` 并消费其定理,不得把探针的 `hCrit`/`hSummable` 假设留在公开陈述中。

后续增订继续严格追加于本节之后。
---

# 增订十八　勘误:M3-d-1 在 s = 1 处为假(Mathlib 约定值),改以 s ≠ 1 预登记(M3-d-1′)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;实施席 codex-cli(flight `la134-impl-m3d`)在动手前核出反例并按增订十六 §五 的回退条款只 deposit 了 M3-d-4(#4995);本节勘误由 orchestrator(claude 主循环)撰写。判决日:2026-09-03。lane issue:#4589。

## 〇　反例与勘误

增订十六 §一 的 M3-d-1 断言对一切 0 < Re s 成立。**反例 s = 1**:钉版 Mathlib 给 `riemannZeta 1` 一个有限约定值,右侧 (1 − 2^{1−1})·ζ(1) = 0·ζ(1) = 0,而左侧交错调和级数的部分和收敛到 log 2 > 0。故原子 `cd9f047e…` 的陈述为假,按「atoms 不删」总则原文不动、本节追加新原子;M3-d-2(实零点)与 M3-d-3(虚部非零)只用到实 x ∈ (0,1) ≠ 1,不受影响,其义务原子不变。**这不是 Mathlib 的缺陷**:(1 − 2^{1−s})ζ(s) 在 s = 1 的真值 log 2 是可去奇点的极限值,而 Mathlib 以 `riemannZeta 1` 的约定值参与乘积后得到 0;正确的陈述须排除 s = 1 或改用极限形式。

## 一　M3-d-1′ 预登记:交错级数的延拓恒等式(s ≠ 1)

**义务**:公开定理 `tendsto_alternating_partialSums_eta_of_ne_one (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) : Filter.Tendsto (fun N ↦ ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n * ((n + 1 : ℂ) ^ (-s))) Filter.atTop (nhds ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s))`。落点 `D5/S3/Weil/ZetaBridge/`(模块 `AlternatingZetaContinuation`,与 M3-d-2、M3-d-3 同模块;M3-d-4 已于 `RealAxisNonvanishing` 单独 deposit)。
**可证伪预测(写在跑之前)**:若正确,证明为 Re s > 1 上的偶奇拆分恒等式 + 交错部分和在 {0 < Re s} 上的局部一致收敛(配对相邻项)+ 两侧在连通开集 {0 < Re s} ∖ {1} 上解析 + 解析延拓唯一性,只消费钉版 Mathlib,标准三公理;若 {0 < Re s} ∖ {1} 的连通性或配对项的 cpow 差分估计在钉版 API 下写不出,则本条按 open 记,不得以 `sorry` 或公理代替。
**边界**:s = 1 被显式排除(反例见 §〇);不断言 `tsum`;M3-d-2 取 s = x ∈ (0,1) 实,自动满足 s ≠ 1。

## 二　结算

原子 `cd9f047e…`(M3-d-1 原式)记为**已证伪(refuted,反例 s = 1)**,不 cover;M3-d-1′、M3-d-2、M3-d-3 由 la135 席位同模块实施(deposit 绑 M3-d-2)。

后续增订继续严格追加于本节之后。
---

# 增订十九　M3-d 收口:去掉 separator 的 `hIm`(M3-d-3′ / M3-e′ / M3-f-6 预登记),并开新桶 `D5/S3/Weil/Separator/`

> 产地(第 9′ 条):skill=consensus-rnd:sshx;前提为 #5004(la135 席位,codex-cli)已冻结的 `AlternatingZetaContinuation.ZeroData.im_ne_zero`(M3-d-3,kernel 已证,但其带点定理名不能作 GID,`make cover` 判 `PLAYBOOK_INVALID GID does not resolve to a Lean module`——增订十六命名之误);本节由 orchestrator(claude 主循环)撰写,三条皆为对冻结定理的一行绑定,不需探针。判决日:2026-09-03。lane issue:#4589。

## 〇　为什么是这一节

`ZeroData` 的字段 `zero_isNontrivial : ∀ n, IsNontrivialZero (zero n)` 与已冻结的 `ZeroData.im_ne_zero` 合起来,给出每个 `Z.zero n` 的虚部非零;于是增订十一(M3-e)与增订十四(M3-f-5)两条 separator 里的 `hIm` 假设可以去掉。本节把这三件事登记为三条一行定理,同时给 M3-d-3 一个不带点、可作 GID 的别名以便消化账闭合。**容量**:`D5/S3/Weil/ZetaBridge/` 已 23/24,本节按第 8 条「裂由压力」开新桶 `D5/S3/Weil/Separator/`,随首个真实模块出生。

## 一　M3-d-3′ 预登记:`ZeroData` 零点虚部非零(可寻址别名;`OffLineZeroNegativeWeilSquare`,落 `D5/S3/Weil/Separator/`)

**义务**:公开定理 `zeroData_im_ne_zero (Z : ZeroData) (n : ℕ) : (Z.zero n).im ≠ 0`。
**可证伪预测(写在跑之前)**:若正确,证明为 `ZeroData.im_ne_zero Z n (Z.zero_isNontrivial n)` 一行,标准三公理;若 `ZeroData` 无 `zero_isNontrivial` 字段(与 `D5/S3/Weil/ZeroSum.lean` 字面矛盾)则本条为假。
**边界**:本条比 M3-d-3 少一个假设(由结构字段供给),是其别名而非重证;M3-d-3 的 atom `1087916e…` 因 GID 语法留 residual-open,本条 atom 由本模块 cover。

## 二　M3-e′ 预登记:截断 separator 去掉 `hIm`(同模块第二条公开定理)

**义务**:公开定理 `offLineZero_negative_truncated_weil_square (Z : ZeroData) (n : ℕ) (T : ℝ) (hn : n ∈ Z.symmetricIndices T) (hOff : (Z.zero n).re ≠ criticalAbscissa) : ∃ g : WeilTestFunction, (truncatedZeroSum Z (convolutionSquare g) T).re < 0`。
**可证伪预测(写在跑之前)**:若正确,证明为冻结 `offLineZero_yields_negative_truncated_weil_square Z n T hn hOff (zeroData_im_ne_zero Z n)` 一行;若冻结定理的参数顺序或 `hIm` 类型与此不合,按冻结字面调整调用而非改陈述。
**边界**:不断言零点存在;不断言 O-6 ⟹ RH。

## 三　M3-f-6 预登记:完整 separator 去掉 `hIm`(同模块第三条公开定理)

**义务**:公开定理 `offLineZero_yields_negative_weil_square (Z : ZeroData) (n : ℕ) (hOff : (Z.zero n).re ≠ criticalAbscissa) : ∃ g : WeilTestFunction, ∃ hZero : SymmetricConvergent Z (convolutionSquare g), (zeroSum Z (convolutionSquare g) hZero).re < 0`。
**可证伪预测(写在跑之前)**:若正确,证明为冻结 `offLineNonrealZero_yields_negative_weil_square Z n hOff (zeroData_im_ne_zero Z n)` 一行,标准三公理。
**边界**:这是 separator 阶梯的最终形态——**任一**离线非平凡零点(不论虚部)都给出一个偶测试函数使完整 Weil 平方零和的实部为负;它仍不构成 O-6 ⟹ RH 的证明(O-6 本身与 Weil 判据的等价未在本仓形式化)。

## 四　预算与结算

一席位轮(codex-cli,独立 worktree,三条一行定理同模块,新桶 `D5/S3/Weil/Separator/`;同 PR deposit(绑 M3-f-6 atom)+ 三条 cover)。预计 ≤ 40 分钟。

后续增订继续严格追加于本节之后。
---

# 增订二十　Weil 平方正性判据与 RH 的等价(相对于一个零点枚举 `ZeroData`;W-1 / W-2 预登记)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;本节由 orchestrator(claude 主循环)据已冻结定理推出,两条皆为对冻结定理的短绑定(约 30 行 + 5 行),不需探针:消费 G-g-3(`RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh`,#4946)、M3-f-6(`Separator/OffLineZeroNegativeWeilSquare.offLineZero_yields_negative_weil_square`,增订十九,la141 在飞)、R-F(`RhImpliesWeilPositivity.riemannHypothesis_implies_o6WeilPositivityStatement`,#4761)与 `ZeroData` 的 `zero_exhaustive` 字段。判决日:2026-09-03。lane issue:#4589。

## 〇　为什么是这一节

separator 阶梯到 M3-f-6 为止说的是:**任一**离线非平凡零点都给出一个偶测试函数 g,使 Weil 平方零和 `zeroSum Z (g⋆g)` 的实部为负。取逆否:若对一切 g 该实部非负(本仓 O-6 的形式化陈述),则 `ZeroData` 里没有离线零点;而 `ZeroData` 的 `zero_exhaustive` 保证每个非平凡零点都被枚举,G-g-3 又把「右半带无零点」升为完整 `RiemannHypothesis`。反向由 R-F 给出。于是在**给定一个 `ZeroData`** 的前提下,本仓的 Weil 平方正性陈述与 Mathlib 的 `RiemannHypothesis` 等价。**诚实边界**:①`ZeroData` 的存在性未证(它要求 ζ 非平凡零点的一个可数枚举带重数、反射与共轭对称、局部有限——与 M1-b「零点无穷」同层,本仓 `ZeroSum.lean` 明写 "No inhabitant is asserted");②等价的右侧是**本仓定义**的 `zeroSum`/`convolutionSquare`/`WeilTestFunction` 上的正性,不冒充文献中 Weil 显式公式判据的字面形式;③本节**不构成 RH 的证明**,它把 RH 与一个可对每个 g 独立检验的不等式族捆在一起——那族不等式本身与 RH 同难。

## 一　W-1 预登记:Weil 平方正性 ⟹ RH(`WeilSquarePositivityCriterion`,落 `D5/S3/Weil/Separator/`)

**义务**:公开定理 `weilSquarePositivity_implies_rh (Z : ZeroData) (hPos : ∀ (g : WeilTestFunction) (hZero : SymmetricConvergent Z (convolutionSquare g)), 0 ≤ (zeroSum Z (convolutionSquare g) hZero).re) : RiemannHypothesis`。
**可证伪预测(写在跑之前)**:若正确,证明为:用 G-g-3 化归到右半带;对右半带零点 ρ(ζ ρ = 0,1/2 < Re ρ < 1)由 `Z.zero_exhaustive` 取 n 使 `Z.zero n = ρ`,`hOff` 由 1/2 < Re ρ ≠ criticalAbscissa(= 1/2,`D5/S3/Weil/Convention.lean:42`)得到,M3-f-6 给出 g、hZero 与实部 < 0,与 hPos 矛盾;标准三公理。若 `zero_exhaustive` 的形状不是 `∀ {rho}, IsNontrivialZero rho → ∃ n, zero n = rho`(与 `ZeroSum.lean` 字面矛盾),则本条为假。
**边界**:见 §〇;不断言任何 `ZeroData` 存在。

## 二　W-2 预登记:RH ⟺ Weil 平方正性(同模块第二条公开定理)

**义务**:公开定理 `rh_iff_weilSquarePositivity (Z : ZeroData) : RiemannHypothesis ↔ ∀ (g : WeilTestFunction) (hZero : SymmetricConvergent Z (convolutionSquare g)), 0 ≤ (zeroSum Z (convolutionSquare g) hZero).re`。
**可证伪预测(写在跑之前)**:⟹ 为冻结 `riemannHypothesis_implies_o6WeilPositivityStatement hRH Z`,⟸ 为 W-1;若 R-F 的量词顺序与此不合,按冻结字面调整调用而非改陈述。
**边界**:同 §〇。

## 三　预算与结算

一席位轮(codex-cli,独立 worktree,`D5/S3/Weil/Separator/` 第二个模块;须在 la141(增订十九模块)合入后开工以绑定 M3-f-6;同 PR deposit(绑 W-2 atom)+ 两条 cover)。预计 ≤ 40 分钟。

后续增订继续严格追加于本节之后。
---

# 增订二十一　germ 窗口零点的线上/线外二分:线上只剩 ζ(φ²s) 回拉零点与 p = 2, 3 的局部因子(G-g-7 / G-g-8 预登记)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;本节两条皆为对冻结定理的短绑定(G-g-6 `GermWindow.golden_continued_germ_window_zero_iff_of_rh`(#5042)+ G-f `LocalFactorCriticalLineNonvanishing.germLocalFactor_critical_line_nonzero_of_five_le`(#4942)),由 orchestrator(claude 主循环)撰写,不需探针。判决日:2026-09-03。lane issue:#4589。

## 〇　为什么是这一节

G-g-6 给出 RH 下开窗口零点集 = 线上 ζ(φ²s) 回拉零点 ∪ 局部因子零点;G-f 给出 p ≥ 5 的局部因子在回拉临界线上不为零。合起来:**线上**的 germ 零点要么是 ζ(φ²s) 的回拉零点,要么是 p = 2 或 p = 3 的局部因子零点(这两个素数的线上取值本仓只有数值读数,G-c 类问题);**线外**(仍在开窗口内)的 germ 零点只能是局部因子零点。这把「RH 与窗口零点」的关系压到一个可数值检验的残余:若 p = 2, 3 的局部因子在线上处处非零(数值上待查),则 RH 下线上零点恰是 ζ 回拉零点。**边界**:线上点自动落在开窗口内(1/(2φ³) < 1/(2φ²) < 1/φ²),G-g-7 不再带窗口假设;两条都相对于满足冻结公式的任意 `continuedGerm`;不构成 RH 证明路径。**容量**:`D5/S3/Analytic/GermWindow/` 现 1/24。

## 一　G-g-7 预登记:线上零点二分(`GoldenGermWindowLineDichotomy`,落 `D5/S3/Analytic/GermWindow/`)

**义务**:公开定理 `golden_continued_germ_line_zero_iff_of_rh (hRH : RiemannHypothesis) : let Kp : Complex -> Nat.Primes -> Complex := fun s p => let x := (p : Complex) ^ (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)); let y := (p : Complex) ^ (-s * ((Real.goldenRatio ^ 3 : Real) : Complex)); (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) * (1 - y) * (1 + x)⁻¹ * germLocalFactor s p; let G3 : Complex -> Complex := fun s => ∏' p : Nat.Primes, Kp s p; ∀ continuedGerm : {s : Complex // 1 / Real.goldenRatio ^ 5 < s.re} -> Complex, (∀ s, continuedGerm s = riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) * riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s.1) * (riemannZeta (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s.1))⁻¹ * ((riemannZeta (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s.1))⁻¹ * riemannZeta ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) : Complex) * s.1)) * G3 s.1)) -> ∀ s, s.1.re = 1 / (2 * Real.goldenRatio ^ 2) -> (continuedGerm s = 0 ↔ (riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) = 0 ∨ germLocalFactor s.1 2 = 0 ∨ germLocalFactor s.1 3 = 0))`。
**可证伪预测(写在跑之前)**:若正确,由 G-g-6(线上点满足窗口假设)与 G-g-5/G-g-6 的局部因子分支:∃ p 局部因子为零 ⟹ p = 2 ∨ p = 3(p ≥ 5 由 G-f 排除,须把线上点写成 `((1/(2φ²) : ℝ) : ℂ) + I * t` 的形状,`Complex.re_add_im`);反向 p ∈ {2,3} 的零给出 ∃ p;标准三公理。若 G-f 的陈述不是对一切实 t 的线上点(与冻结字面矛盾),则本条为假。
**边界**:不断言 p = 2, 3 的线上零点存在或不存在。

## 二　G-g-8 预登记:线外零点只能是局部因子零点(同模块第二条公开定理)

**义务**:公开定理 `golden_continued_germ_off_line_zero_iff_of_rh (hRH : RiemannHypothesis) : let Kp : Complex -> Nat.Primes -> Complex := fun s p => let x := (p : Complex) ^ (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)); let y := (p : Complex) ^ (-s * ((Real.goldenRatio ^ 3 : Real) : Complex)); (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) * (1 - y) * (1 + x)⁻¹ * germLocalFactor s p; let G3 : Complex -> Complex := fun s => ∏' p : Nat.Primes, Kp s p; ∀ continuedGerm : {s : Complex // 1 / Real.goldenRatio ^ 5 < s.re} -> Complex, (∀ s, continuedGerm s = riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) * riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s.1) * (riemannZeta (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s.1))⁻¹ * ((riemannZeta (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s.1))⁻¹ * riemannZeta ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) : Complex) * s.1)) * G3 s.1)) -> ∀ s, 1 / (2 * Real.goldenRatio ^ 3) < s.1.re -> s.1.re < 1 / Real.goldenRatio ^ 2 -> s.1.re ≠ 1 / (2 * Real.goldenRatio ^ 2) -> (continuedGerm s = 0 ↔ ∃ p : Nat.Primes, germLocalFactor s.1 p = 0)`。
**可证伪预测(写在跑之前)**:若正确,由 G-g-6 与「线上」子句被 `s.1.re ≠ 1/(2φ²)` 否定直接得到;标准三公理。
**边界**:同 §〇。

## 三　预算与结算

一席位轮(codex-cli,独立 worktree,两条同模块;同 PR deposit(绑 G-g-7 atom)+ 两条 cover)。预计 ≤ 60 分钟。

后续增订继续严格追加于本节之后。
---

# 增订二十二　零点无穷 ⟹ Weil 平方正性 ⟺ RH,不再相对于具体的 `ZeroData`(W-3 / W-4 预登记)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;探针一席(codex-cli,`probe-zerodata`,533s)核出 `Nonempty ZeroData ↔ {ρ | IsNontrivialZero ρ}.Infinite` 已于 2026-09-02 由本 lane 冻结(`ZetaBridge/ZeroDataNonemptyIffInfinite.nonempty_zeroData_iff_infinite`,M1-a),Z1–Z4(可数性、离散性、重数、置换、装配)无需重做;本节两条皆为对冻结 W-2(`Separator/WeilSquarePositivityCriterion.rh_iff_weilSquarePositivity`,#5069)与 M1-a 的短绑定,由 orchestrator(claude 主循环)撰写。判决日:2026-09-03。lane issue:#4589。

## 〇　为什么是这一节

W-2 把 RH 与 Weil 平方正性绑在一起,但量词落在一个给定的 `Z : ZeroData` 上。M1-a 给出 `ZeroData` 恰在非平凡零点集无穷时可居;于是只要假设**零点无穷**(M1-b,本仓仍 open;另一 lane `rh-canonical-zero-data-nonvacuity-*` 由显式 Riemann–von Mangoldt 假设推它),等价就可以对**一切** `Z`(W-3)或**某个** `Z`(W-4)陈述,不再依赖谁提供了枚举。**诚实边界**:①`hInf` 未在本仓证明(M1-b);②`ZeroData` 的构造用了 `Classical.choice`(非构造性枚举),W-3/W-4 只是量词层面的收口;③右侧仍是本仓定义的正性;④不构成 RH 证明。

## 一　W-3 预登记:∀-形(`WeilSquarePositivityCriterionOfInfinite`,落 `D5/S3/Weil/Separator/`)

**义务**:公开定理 `rh_iff_forall_zeroData_weilSquarePositivity (hInf : {rho : ℂ | IsNontrivialZero rho}.Infinite) : RiemannHypothesis ↔ ∀ Z : ZeroData, ∀ (g : WeilTestFunction) (hZero : SymmetricConvergent Z (convolutionSquare g)), 0 ≤ (zeroSum Z (convolutionSquare g) hZero).re`。
**可证伪预测(写在跑之前)**:若正确,⟹ 对任意 Z 用 W-2 的 ⟹;⟸ 由 `nonempty_zeroData_iff_infinite.mpr hInf` 取一个 Z,再用 W-2 的 ⟸;标准三公理。若 M1-a 的陈述不是 `Nonempty ZeroData ↔ {rho | IsNontrivialZero rho}.Infinite`(与 `ZeroDataNonemptyIffInfinite.lean:237` 字面矛盾),则本条为假。
**边界**:见 §〇。

## 二　W-4 预登记:∃-形(同模块第二条公开定理)

**义务**:公开定理 `rh_iff_exists_zeroData_weilSquarePositivity (hInf : {rho : ℂ | IsNontrivialZero rho}.Infinite) : RiemannHypothesis ↔ ∃ Z : ZeroData, ∀ (g : WeilTestFunction) (hZero : SymmetricConvergent Z (convolutionSquare g)), 0 ≤ (zeroSum Z (convolutionSquare g) hZero).re`。
**可证伪预测(写在跑之前)**:⟹ 取 M1-a 给出的 Z 与 W-2 的 ⟹;⟸ 对给定的 Z 用 W-2 的 ⟸;标准三公理。
**边界**:同 §〇。

## 三　预算与结算

一席位轮(codex-cli,独立 worktree,两条同模块,`Separator/` 第三个模块;同 PR deposit(绑 W-3 atom)+ 两条 cover)。预计 ≤ 40 分钟。

后续增订继续严格追加于本节之后。
---

# 增订二十三　截断 Weil 平方正性 ⟺ RH:有限对称零和版本(W-5 / W-6 / W-7 预登记)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;本节三条皆为对冻结定理的短绑定——W-5 消费 M3-e′(`Separator/OffLineZeroNegativeWeilSquare.offLineZero_negative_truncated_weil_square`,#5052)、G-g-3(`ZetaBridge/RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh`)、`ZeroData.mem_symmetricIndices`(`ZeroSum.lean:145`)与 `zero_exhaustive`;W-6 消费 R-F 证明所用的两条公开冻结定理 `ConvolutionSquareCriticalLine.critical_line_truncated_sum_real_nonnegative` 与 `zeroData_zero_on_critical_line_of_rh`(R-F 内部的 `hnonneg` 步骤,那一步是证明内部的 `have`,不可寻址);W-7 合之。由 orchestrator(claude 主循环)撰写,不需探针。判决日:2026-09-03。lane issue:#4589。

## 〇　为什么是这一节

W-2 的正性陈述里带着 `SymmetricConvergent` 这个收敛义务和一个极限量 `zeroSum`;截断版本 `truncatedZeroSum Z g T`(`ZeroSum.lean:194`,对 `Z.symmetricIndices T` 的**有限**求和)没有收敛义务,对每个 T 是一个有限和。separator 的截断形(M3-e′)与 R-F 证明内部的截断非负步骤合起来,给出**不含极限**的等价:RH ⟺ 对一切截断高度 T 与一切偶测试函数 g,截断平方零和实部非负。这比 W-2 更接近可数值检验的形态(固定 T、固定 g 是一个有限计算),尽管仍相对于一个 `ZeroData`。**诚实边界**:同增订二十(相对于未证存在的 `ZeroData`;右侧是本仓定义;不构成 RH 证明);另外 `truncatedZeroSum` 的求和范围 `symmetricIndices T` 由 `spectralRadius ≤ T` 决定,不是按虚部截断。

## 一　W-5 预登记:截断正性 ⟹ RH(`TruncatedWeilSquarePositivityCriterion`,落 `D5/S3/Weil/Separator/`)

**义务**:公开定理 `truncatedWeilSquarePositivity_implies_rh (Z : ZeroData) (hPos : ∀ (T : ℝ) (g : WeilTestFunction), 0 ≤ (truncatedZeroSum Z (convolutionSquare g) T).re) : RiemannHypothesis`。
**可证伪预测(写在跑之前)**:若正确,证明为:G-g-3 化归到右半带零点 ρ;`zero_exhaustive` 取 n;取 T := spectralRadius (Z.zero n),由 `Z.mem_symmetricIndices` 得 n ∈ Z.symmetricIndices T(≤ 自反);`hOff` 由 1/2 < Re ρ;M3-e′ 给 g 与实部 < 0,与 `hPos T g` 矛盾;标准三公理。若 `mem_symmetricIndices` 的右侧不是 `spectralRadius (Z.zero n) ≤ T` 型(与 `ZeroSum.lean:145–147` 字面不合)则按冻结字面调整证明而非改陈述。
**边界**:见 §〇。

## 二　W-6 预登记:RH ⟹ 截断正性(同模块第二条公开定理)

**义务**:公开定理 `rh_implies_truncatedWeilSquarePositivity (hRH : RiemannHypothesis) (Z : ZeroData) : ∀ (T : ℝ) (g : WeilTestFunction), 0 ≤ (truncatedZeroSum Z (convolutionSquare g) T).re`。
**可证伪预测(写在跑之前)**:若正确,证明与 R-F 内部 `hnonneg` 同形:RH 下 `zeroData_zero_on_critical_line_of_rh` 使 `symmetricIndices T` 的临界线过滤为全集(`Finset.filter_true_of_mem`),再用 `critical_line_truncated_sum_real_nonnegative Z g T` 的第二分量;标准三公理。这两条都是公开冻结定理,本条不重证它们;R-F 自身只暴露极限版,故本条不是重复。
**边界**:同 §〇。

## 三　W-7 预登记:RH ⟺ 截断正性(同模块第三条公开定理)

**义务**:公开定理 `rh_iff_truncatedWeilSquarePositivity (Z : ZeroData) : RiemannHypothesis ↔ ∀ (T : ℝ) (g : WeilTestFunction), 0 ≤ (truncatedZeroSum Z (convolutionSquare g) T).re`。
**可证伪预测(写在跑之前)**:⟹ 为 W-6,⟸ 为 W-5。
**边界**:同 §〇。

## 四　预算与结算

一席位轮(codex-cli,独立 worktree,三条同模块,`Separator/` 第四个模块;同 PR deposit(绑 W-7 atom)+ 三条 cover)。预计 ≤ 60 分钟。

后续增订继续严格追加于本节之后。
---

# 增订二十四　高度 T 的窗口判据:「半径 ≤ T 的零点全在线上」⟺「高度 T 的截断 Weil 平方正性」(W-8 / W-9 预登记)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;本节两条皆为对冻结定理的短绑定——W-8 消费 M3-e′(`Separator/OffLineZeroNegativeWeilSquare.offLineZero_negative_truncated_weil_square`)、`ConvolutionSquareCriticalLine.critical_line_truncated_sum_real_nonnegative`、`Finset.filter_true_of_mem`;W-9 消费 `zeroData_zero_on_critical_line_of_rh`、G-g-3、`zero_exhaustive`、`ZeroData.mem_symmetricIndices`。由 orchestrator(claude 主循环)撰写,不需探针。判决日:2026-09-03。lane issue:#4589。

## 〇　为什么是这一节

W-7 把 RH 与「一切高度 T 的截断正性」绑在一起;本节把量词拆开:**固定** T,`Z.symmetricIndices T`(谱半径 ≤ T 的零点指标,有限集)内的零点全在临界线上,当且仅当高度 T 的截断 Weil 平方零和对一切偶测试函数实部非负。这是「RH 到高度 T」的**逐高度**判据,两边都是关于有限零点集与有限和的陈述;W-9 再把「对一切 T 的逐高度线上性」与 RH 等价。**诚实边界**:相对于给定 `ZeroData`;`symmetricIndices T` 按谱半径 `‖Z.gamma n‖ ≤ T` 截断(`ZeroSum.lean:145–147`),不是按虚部;不构成 RH 证明。

## 一　W-8 预登记:逐高度判据(`HeightWindowWeilSquareCriterion`,落 `D5/S3/Weil/Separator/`)

**义务**:公开定理 `heightWindow_rh_iff_truncatedWeilSquarePositivity (Z : ZeroData) (T : ℝ) : (∀ n ∈ Z.symmetricIndices T, (Z.zero n).re = criticalAbscissa) ↔ ∀ g : WeilTestFunction, 0 ≤ (truncatedZeroSum Z (convolutionSquare g) T).re`。
**可证伪预测(写在跑之前)**:若正确,⟹ 由 `Finset.filter_true_of_mem`(临界线过滤 = 全集)与 `critical_line_truncated_sum_real_nonnegative Z g T` 的第二分量,展开 `truncatedZeroSum`;⟸ 取逆否:若某 n ∈ symmetricIndices T 离线,M3-e′ 给 g 使截断和实部 < 0;标准三公理。
**边界**:同 §〇。

## 二　W-9 预登记:RH ⟺ 一切高度的线上性(同模块第二条公开定理)

**义务**:公开定理 `rh_iff_forall_heightWindow (Z : ZeroData) : RiemannHypothesis ↔ ∀ T : ℝ, ∀ n ∈ Z.symmetricIndices T, (Z.zero n).re = criticalAbscissa`。
**可证伪预测(写在跑之前)**:⟹ 由 `zeroData_zero_on_critical_line_of_rh`;⟸ 由 G-g-3:右半带零点 ρ 经 `zero_exhaustive` 为某 `Z.zero n`,取 T := ‖Z.gamma n‖ 使 n ∈ symmetricIndices T(`mem_symmetricIndices`,自反),得 Re ρ = 1/2 与 1/2 < Re ρ 矛盾;标准三公理。
**边界**:同 §〇。

## 三　预算与结算

一席位轮(codex-cli,独立 worktree,两条同模块,`Separator/` 第五个模块;同 PR deposit(绑 W-8 atom)+ 两条 cover)。预计 ≤ 40 分钟。

后续增订继续严格追加于本节之后。
---

# 增订二十五　素数侧的 Weil 判据:RH ⟺ 显式公式右侧(极点项 − 素数项 + 阿基米德项)对一切卷积平方非负(W-10 / W-11 预登记)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;本节两条皆为对冻结定理的短绑定——冻结显式公式 `ZetaBridge/ClassicExplicitFormula.weil_explicit_formula (Z) (g) (hZero) (hArch) : zeroSum Z g hZero = poleTerm g - primeTerm g + archimedeanTerm g hArch`、M2-c `ZetaBridge/SymmetricConvergentOfZetaSummable.symmetricConvergent_of_zeroData (Z) (g) : SymmetricConvergent Z g`、W-2 `Separator/WeilSquarePositivityCriterion.rh_iff_weilSquarePositivity`;`poleTerm`/`primeTerm`/`archimedeanTerm`/`ArchimedeanConvergent` 定义于 `D5/S3/Weil/PrimePoleTerms.lean`(素数项为 Λ(n)/√n 加权的 g(±log n) 级数,阿基米德项为 digamma 加权的 Fourier–Laplace 积分)。由 orchestrator(claude 主循环)撰写,不需探针。判决日:2026-09-04。lane issue:#4589。

## 〇　为什么是这一节

W-2 的正性陈述在零点侧;冻结的显式公式把零点和搬到素数侧:`zeroSum Z g = poleTerm g − primeTerm g + archimedeanTerm g`。对卷积平方 g⋆g,零点侧的 `SymmetricConvergent` 由 M2-c 无条件供给,于是 RH 与**素数侧**表达式的非负性等价——这才是文献中 Weil 判据的形状(零点信息完全消失,只剩极点、素数幂与 Γ 因子)。**诚实边界**:①阿基米德积分的可积性 `ArchimedeanConvergent (g⋆g)` 在本仓尚无冻结定理供给(W-11 探针另查;钉版 Mathlib 未见 digamma 增长界),故 W-10 以 `hArch` 为显式假设;②仍相对于一个 `ZeroData`(M1-b);③定义域为本仓 `WeilTestFunction`(偶、C^∞、紧支),不冒充文献中更宽的测试函数类;④不构成 RH 证明。

## 一　W-11 预登记:卷积平方的显式公式(`ExplicitFormulaWeilCriterion`,落 `D5/S3/Weil/Separator/`)

**义务**:公开定理 `explicitFormula_weilSquare (Z : ZeroData) (g : WeilTestFunction) (hArch : ArchimedeanConvergent (convolutionSquare g)) : zeroSum Z (convolutionSquare g) (symmetricConvergent_of_zeroData Z (convolutionSquare g)) = poleTerm (convolutionSquare g) - primeTerm (convolutionSquare g) + archimedeanTerm (convolutionSquare g) hArch`。
**可证伪预测(写在跑之前)**:若正确,证明为冻结 `weil_explicit_formula Z (convolutionSquare g) (symmetricConvergent_of_zeroData Z (convolutionSquare g)) hArch` 一行;若 `zeroSum` 的 `hZero` 参数为 proof-irrelevant 使两侧按定义相等,则 `rfl`/`exact` 即闭合;标准三公理。
**边界**:见 §〇。

## 二　W-10 预登记:素数侧判据(同模块第二条公开定理)

**义务**:公开定理 `rh_iff_explicitFormulaPositivity (Z : ZeroData) (hArch : ∀ g : WeilTestFunction, ArchimedeanConvergent (convolutionSquare g)) : RiemannHypothesis ↔ ∀ g : WeilTestFunction, 0 ≤ (poleTerm (convolutionSquare g) - primeTerm (convolutionSquare g) + archimedeanTerm (convolutionSquare g) (hArch g)).re`。
**可证伪预测(写在跑之前)**:若正确,由 W-2 与 W-11 逐 g 改写:`(rh_iff_weilSquarePositivity Z)` 的右侧在 `hZero := symmetricConvergent_of_zeroData Z (convolutionSquare g)` 下与素数侧表达式相等(需说明 `∀ hZero` 与取特定 `hZero` 的等价——`SymmetricConvergent` 是 Prop,proof-irrelevance 使 `zeroSum Z g hZero` 不依赖 hZero 的具体证明);标准三公理。
**边界**:见 §〇;`hArch` 为假设,不断言其成立。

## 三　预算与结算

一席位轮(codex-cli,独立 worktree,两条同模块,`Separator/` 第六个模块;同 PR deposit(绑 W-10 atom)+ 两条 cover)。预计 ≤ 40 分钟。W-11′(`ArchimedeanConvergent (g⋆g)` 无条件成立)由探针评估可行性后另行增订。

后续增订继续严格追加于本节之后。
---

# 增订二十六　阿基米德可积性无条件成立,素数侧 Weil 判据去掉 `hArch`(W-12 / W-13 预登记)

> 产地(第 9′ 条):skill=consensus-rnd:sshx;探针一席(codex-cli,`probe-arch`,`lake env lean` exit 0,标准三公理)在暖树上整证 W-12,消费冻结的闭带衰减 `FourierLaplaceClosedStripDecay.fourierLaplace_decay_closedStrip`(η = 0)、`FourierLaplaceEntire.fourierLaplace_entire`(实轴连续性)、以及本仓 `Zeta23` 层已冻结的 digamma 竖线增长界与可积性(`ZetaExplicit/FullLine.integrable_mul_logDeriv_Gammaℝ_of_decay`、`ZetaExplicit/GammaRBracket.gammaR_bracket`、`ZetaGamma/GammaStirlingVert.digamma_stirling`、`ZetaExplicit/VerticalLine.digamma_growth_strip`);钉版 Mathlib 无 digamma 连续性/增长界(仅定义与特殊值,`Digamma.lean:31` 留有 TODO),故 W-12 是本仓自证。散文由 orchestrator(claude 主循环)撰写。判决日:2026-09-04。lane issue:#4589。探针 import:`D5.S3.Fourier.FourierLaplaceEntire`, `D5.S3.Weil.PrimePoleTerms`, `D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay`, `D5.S3.Weil.ZetaExplicit.FullLine`。

## 〇　为什么是这一节

增订二十五把素数侧判据 W-10 挂在 `hArch : ∀ g, ArchimedeanConvergent (g⋆g)` 上。探针证明该可积性对**每个**测试函数无条件成立:Fourier–Laplace 变换在实轴 O(1/(1+t²)) 衰减(M3-f-2,η=0),digamma 在竖线上至多对数增长(本仓 Zeta23 层),乘积可积。于是 W-13 把 W-10 的假设去掉:RH ⟺ 素数侧表达式对一切卷积平方非负,**只剩** `ZeroData`(M1-b)这一个相对项。**诚实边界**:①仍相对于 `ZeroData`;②测试函数类为本仓 `WeilTestFunction`;③不构成 RH 证明。

## 一　W-12 预登记:每个 Weil 测试函数的阿基米德积分可积(`ArchimedeanConvergence`,落 `D5/S3/Weil/Separator/`)

**义务**:公开定理 `archimedeanConvergent_of_weilTestFunction (g : WeilTestFunction) : ArchimedeanConvergent g`。
**可证伪预测(写在跑之前)**:若正确,证明为探针路线(连续 + 二次衰减 + digamma 竖线界 ⟹ `Integrable`),消费上列冻结定理,标准三公理;若 `gammaR_bracket` 给出的恒等式与 `archimedeanIntegrand` 的 digamma 形状(`(digamma (1/4 + I t/2)).re − log π`)不一致,则按冻结字面调整证明而非改陈述。
**边界**:对一切 `g : WeilTestFunction`(不只卷积平方)。

## 二　W-13 预登记:无条件素数侧判据(同模块第二条公开定理)

**义务**:公开定理 `rh_iff_primeSidePositivity (Z : ZeroData) : RiemannHypothesis ↔ ∀ g : WeilTestFunction, 0 ≤ (poleTerm (convolutionSquare g) - primeTerm (convolutionSquare g) + archimedeanTerm (convolutionSquare g) (archimedeanConvergent_of_weilTestFunction (convolutionSquare g))).re`。
**可证伪预测(写在跑之前)**:由 W-10(`rh_iff_explicitFormulaPositivity Z (fun g => archimedeanConvergent_of_weilTestFunction (convolutionSquare g))`)一行得到;`archimedeanTerm` 对其可积性证明参数 proof-irrelevant。
**边界**:同 §〇。

## 三　预算与结算

一席位轮(codex-cli,独立 worktree,两条同模块,`Separator/` 第七个模块;同 PR deposit(绑 W-13 atom)+ 两条 cover;须在增订二十五的 la153 模块合入后开工以绑定 W-10)。预计 ≤ 60 分钟(W-12 约 100 行,探针证明可复用)。

后续增订继续严格追加于本节之后。
