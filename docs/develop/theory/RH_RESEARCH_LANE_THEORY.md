  (7.1)-(7.12), Lemmas 7.2-7.3 and Section 8. The literal normalization was
  independently checked by (CO14), and the omitted Gaussian tail is retained.
* Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v1,
  Theorems 1.1-1.4 and Section 8.2. Results stated under RH are not used.
* Connes, Consani, *Spectral triples and zeta-cycles*, arXiv:2106.01715v1,
  Lemma 2.2 and Proposition 2.3, for the actual form core.
* Dusson, Sigal, Stamm, *Analysis of the Feshbach-Schur method for the Fourier
  spectral discretizations of Schrodinger operators*, arXiv:2008.10871v2.
  The elimination principle is classical; its Schrodinger regularity
  assumptions are not silently imported into the Weil problem.
* DLMF 5.7.6, digamma partial fractions, and the Gamma integral and recurrence,
  for the elementary resolvent and Mellin computations.


---

## [PR #5602] CERTIFIED_PROLATE_MODEL_AND_POLYNOMIAL_MELLIN_DICTIONARY

# 2026-09-06：真实 prolate 模型的可认证构造及其与算术最低模态的首次本线定量对接

本节的“首次”仅指本 PR 的交付顺序，不是数学优先权声明。此前已认证的 129 维 dyadic 候选记为 k。它与文献 prolate 模型是不同对象。本节给出后者的独立谱认证、有限多项式 Fourier 端点公式以及实际的 L2 比较，避免在这两个对象之间省略识别误差。

新增 Lean owner 为 `D5/S3/Weil/ZetaBridge/WeilPolynomialMellinWindow.lean`，有同名 Scribe。实际执行源为 `research/weil_ground_mode/certify_prime3_prolate_model.py`，输入 `prime3_prolate_proposal.json`，输出 `prime3_prolate_model_certificate.json`。Lean 保存实际 `Zeta23.paperFT` 的多项式算术窗口公式与可积性；prolate 自伴实现、无限 Legendre 尾、谱投影运输及完整数值结论仍属于下面的纸面与区间证明。Lean/Scribe 编译及传递公理审查未运行。

## 1. 开放问题与跨作者取阅

Connes、Consani、Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1，(7.5)-(7.6)、Lemma 7.3 和 Section 8，把真实最低 Weil 模态与明确 prolate 候选的足够精确比较列为剩余障碍。该文的模型极限不证明真实算术模态的极限。本节只处理一个含素数窗口的同模型校准，并提供任意有限尺度可复用的评价方法。

本轮读取 loning 的 #5296 的实际理论正文 B10.3-B10.4、B13.4：谱分离与边界读出非消失需要分别证明；所有振幅必须在同一空间组合后再平方。因此这里保持真实 Mellin 合成的全部混合项，在真实函数空间中算范数，不把独立矩阵的相似特征值当作模型识别。

同时检查了 AlyciaBHZ 的 #5882、#5895 最新 PR 说明，它们已在实现复数射影误差和 Rouché/readout 证书，故本节不再新建相同抽象定理。#5602 在 `6e95a93cffddabd62c06ebc1e50f57d6913c3c03` 已有 Neumann 比较、同一候选的 <0.01 射影包络和有限 dyadic prolate 族的纸面定义。本节消除的是“prolate 数据尚无严格可执行评价”的具体缺口。没有将那些未运行的 Lean 文件标作已冻结事实。

## 2. 固定文献中的实际 prolate 对象

令 lambda>1，c=lambda^2，a=log(lambda)。在 x=lambda*t 坐标下，文献的

\[
PW_\lambda=-\partial_x((\lambda^2-x^2)\partial_x)+(2\pi\lambda x)^2
\]

变为 [-1,1] 上的正规 prolate 实现

\[
J_q=-\partial_t((1-t^2)\partial_t)+q^2t^2,
\qquad q=2\pi c.
\tag{PM1}
\]

使用偶 Legendre 正交归一基

\[
e_r(t)=\sqrt{(4r+1)/2}\,P_{2r}(t),\qquad r\ge0.
\]

未扰动实现定义为此正交基上的自伴对角算子，特征值 (2r)(2r+1)，其多项式核心在图范数中稠密。q^2*t^2 是有界非负乘法算子，因此在同一个算子域上得到自伴 J_q，有限 Legendre 和保持为核心；resolvent 紧性也被有界扰动保留。这选定的是端点正规、无对数奇分支的 Legendre/prolate 实现。可以从 Legendre 方程与分部积分识别其微分形式，或直接由上述对角实现定义后加入实际乘法势。DLMF 30.2、30.3、30.8 给出相应正规 spheroidal 函数及三项递推。DLMF 的特征值参数与这里可能相差 q^2；特征函数不变，数值证书始终使用 (PM1)。

令

\[
\alpha_j=\frac{j+1}{\sqrt{(2j+1)(2j+3)}},\qquad\alpha_{-1}=0.
\]

由 t*P_j 的标准三项递推直接得到实际无限三对角矩阵

\[
A_{rr}=2r(2r+1)+q^2(\alpha_{2r}^2+\alpha_{2r-1}^2),\qquad
A_{r,r+1}=q^2\alpha_{2r}\alpha_{2r+1}.
\tag{PM2}
\]

本节需要偶谱中编号 0 和 2 的正规特征函数 psi_0、psi_4，它们分别对应文献的 h_(0,lambda)、h_(4,lambda)。选择单位 L2 范数并使零阶 Legendre 系数为正。定义

\[
H(t)=\psi_4(t)-\frac{(\psi_4)_0}{(\psi_0)_0}\psi_0(t),
\qquad h_\lambda(x)=H(x/\lambda).
\tag{PM3}
\]

因为 integral(e_0)=sqrt(2)，而其他 e_r 的积分为零，(PM3) 严格满足零积分。其直线是 span{h_(0,lambda),h_(4,lambda)} 中唯一的零积分直线。任何对两个非零模式的独立重归一化都会给出同一条直线。本文比较的是之后的单位函数，因此省略的整体非零系数不会改变比较对象；最终 Xi 极限的尺度系数仍须用此前已经校准的文献归一化，不能任意缩小。

## 3. 有限提案如何认证整个无限 prolate 谱

保留 r=0,...,K-1。遗漏空间的最小未扰动 Legendre 能量是

\[
H_K=2K(2K+1).
\]

非负势给出整个遗漏形式块 Q_K J_q Q_K >=H_K I。由于 (PM2) 三对角，跨低高空间仅有一条非零耦合，系数

\[
b_K=q^2\alpha_{2K-2}\alpha_{2K-1}.
\]

对 s<H_K，真实 Schur 形式介于两个实际有限矩阵之间：

\[
A_K-sI-\frac{b_K^2}{H_K-s}e_{K-1}e_{K-1}^*
\preceq S(s)\preceq A_K-sI.
\tag{PM4}
\]

这里两个端点矩阵都明确计算，并用区间 LDL 的符号统计其负惯性。当两者非奇异且负指标相同，单调性和上下夹逼保证 S(s) 非奇异且具有同一负指标，因而认证实际 J_q 在 s 以下的全部特征值数量。不能只用有限 A_K 的 Sturm 计数代替这个双端点检查。

本次 c=3、K=32、H_K=4160。提案来自一次不受信任的高精度有限 eigsy 计算，之后每个坐标和中心都固定为分母 2^250 的有理数。独立 verifier 不调用 eigensolver。它在两个中心 mu_j 的 mu_j-1、mu_j+1 处检查 (PM4) 的两个惯性：

\[
\begin{array}{c|c|c}
\text{目标偶谱编号}&\text{mu-1 两端点计数}&\text{mu+1 两端点计数}\\
0&(0,0)&(1,1)\\
2&(2,2)&(3,3)
\end{array}
\]

显示用中心约为 18.088872829041046 和 158.048541836992256。实际比较使用完整 dyadic 中心与定向区间，非显示小数。

对归一化的有限提案 v，完整无限算子残差为

\[
r^2=\|(A_K-\mu)v\|^2+b_K^2|v_{K-1}|^2.
\tag{PM5}
\]

最后一项严格保留。两次认证的残差平方上端点分别小于 1.384e-61 与 1.861e-55。除目标简单特征值以外，全部谱与 mu 的距离至少为 1；谱定理因此给出正交投影误差 <=r，选择真实单位特征函数的符号后有

\[
\|\psi_j-v_j\|\le\sqrt2r_j<10^{-25},\qquad j=0,4.
\tag{PM6}
\]

残差本身不足以识别第几条谱线；编号来自前面完整空间的惯性计数。正的零阶系数及 (PM6) 又固定了符号，并认证 (psi_0)_0 非零。

## 4. 同一零积分模型的误差运输

记 r=v_(4,0)/v_(0,0)，d=v_(0,0)>epsilon_0。若 (PM6) 的误差为 epsilon_j，则

\[
\left|\frac{(\psi_4)_0}{(\psi_0)_0}-r\right|
\le\Delta_r:=\frac{\epsilon_4+|r|\epsilon_0}{d-\epsilon_0}.
\]

故实际零积分组合与有限组合之差满足

\[
\|H-(v_4-rv_0)\|\le
\epsilon_4+(|r|+\Delta_r)\epsilon_0+\Delta_r.
\tag{PM7}
\]

不需要给积分误差、比值或基函数逼近设置未检查的输入字段。

对 h 支撑于 [-lambda,lambda]，定义实际算术窗口

\[
p_h(x)=4e^{x/2}\sum_{1\le m\le\lambda e^{-x}}h(me^x),
\qquad -a\le x\le a,
\]

并在窗口外置零。最后明确偶化 p_h^+(x)=(p_h(x)+p_h(-x))/2。有限 prolate 模式的 Fourier 特征值一般不同，不能预先假定未偶化的 p_h 已严格为偶。

单个 m 的误差用 t=m*exp(x) 代换，有

\[
\int_{-a}^{a-\log m} e^x|\delta h(me^x)|^2dx
=\frac1m\int_{m/\lambda}^{\lambda}|\delta h(t)|^2dt.
\]

所以对 c=lambda^2 为整数的任何有限尺度，

\[
\boxed{\|p_h^+-p_{\widetilde h}^+\|_2
\le4\sqrt\lambda\left(\sum_{m=1}^{c}m^{-1/2}\right)
\|H-\widetilde H\|_{L^2[-1,1]}.}
\tag{PM8}
\]

此处 h(x)=H(x/lambda)，因此 sqrt(lambda) 的缩放因子被保留。偶化是正交投影，范数不增。若 rhs=e<n=||p_tilde^+||，则真实模型非零，且

\[
\left\|\frac{p_h^+}{\|p_h^+\|}-
\frac{p_{\widetilde h}^+}{\|p_{\widetilde h}^+\|}\right\|
\le\frac{2e}{n}.
\tag{PM9}
\]

证明直接使用反三角不等式，分母 n 独立认证为正。误差链 (PM4)-(PM9) 对参数化有限尺度有效；本次程序只实例化 c=3，没有暗示已逐尺度认证全部 c。

## 5. 多项式算术窗口的完整有限 Fourier 公式

由 Legendre 提案可精确构造偶多项式

\[
\widetilde h(t)=\sum_{r=0}^{d-1}A_rt^{2r}.
\]

定义 s=1/2+iz、t_r=s+2r。每个算术单项的 Fourier 积分为

\[
4A_rm^{2r}\int_{-a}^{a-\log m}e^{t_rx}dx
=4A_rm^{2r}\frac{e^{t_r(a-\log m)}-e^{-at_r}}{t_r}.
\tag{PM10}
\]

对 Im(z)<1/2，Re(t_r)>0，所有分母均非零。有限求和给出

\[
\boxed{\widehat p(z)=4\sum_{m=1}^{M}\sum_{r<d}
A_rm^{2r}\frac{e^{t_r(a-\log m)}-e^{-at_r}}{t_r}.}
\tag{PM11}
\]

条件是全部包含的 m 满足 log(m)<=2a。主 Lean 声明 `polynomial_mellin_window_paperFT` 使用原始 `Zeta23.paperFT` 证明 (PM11)。`polynomial_mellin_fourier_integrable` 对全部复 z 先证明实际 integrand 可积；`mellin_monomial_polynomial_value` 证明指数坐标确实等于 exp(x/2)*(m*exp(x))^(2r)。这些结论无需任何未知谱、零点、积分精度或 Fourier 识别假设。

合并 m 项，还可把纸面公式写成一个有限 Dirichlet 字典：

\[
\widehat p(z)=4\sum_{r<d} A_r
\frac{e^{at_r}D_M(s)-e^{-at_r}S_M(2r)}{t_r},
\quad D_M(s)=\sum_{m=1}^Mm^{-s},\quad S_M(2r)=\sum_{m=1}^Mm^{2r}.
\tag{PM12}
\]

式 (PM12) 未另设 Lean 公共包装；实际 verifier 使用等价的 (PM11)。它不调用 zeta 值。表观 t_r=0 奇点可去；Lean 定理在所需半平面内直接排除了分母为零，不依赖 totalized division。

## 6. 保留完整混合项的函数范数与实际校准

在 c=3 处，m=3 只贡献一个端点，Lebesgue 积分为零。令 b=a-log2<0。实际 p_tilde^+ 的解析表达只在 -a、b、-b、a 处切换。每段是有限个 exp(plus-or-minus(2r+1/2)*x) 的线性组合。

平方后先合并所有指数及其完整系数，包括全部交叉项；对每个精确有理指数 t 使用

\[
\int_l^r e^{tx}dx=(e^{tr}-e^{tl})/t\quad(t\ne0),\qquad
\int_l^r1\,dx=r-l.
\]

这给出 ||p_tilde^+|| 的定向区间，无求积误差。固定候选 k 的余弦系数使用已有相位约定；其与 p_tilde^+ 的内积通过 (PM11) 的 65 个实际余弦频率值精确计算。所有有限和先在同一函数中形成，平方时没有舍弃混合项。

本次显示值为

\[
\|p_{\widetilde h}^+\|=2.90193861714445\ldots,
\qquad
\left\langle k,\frac{p_{\widetilde h}^+}{\|p_{\widetilde h}^+\|}\right\rangle
=-0.999999377793547947\ldots.
\]

这里的原始范数采用 (PM3) 的整体标度，不是此前文献校准常数下的范数。单位直线与该常数无关。实符号对齐后的多项式模型距离平方为

\[
2-2|\langle k,p_{\widetilde h}^+/\|p_{\widetilde h}^+\|\rangle|
\in[1.24441290410519742709\ldots,1.24441290410519742710\ldots]10^{-6}
< (112/100000)^2.
\]

(PM9) 的真实 prolate/多项式模型误差小于 3.376e-24。因此对真正的偶化 prolate 模型，执行器证明

\[
\boxed{\inf_{\sigma\in\{-1,1\}}
\left\|k-\sigma\frac{p_{h_\lambda}^+}{\|p_{h_\lambda}^+\|}\right\|
<\frac{113}{100000}=0.00113,
\qquad \lambda=\sqrt3.}
\tag{PM13}
\]

结合本卷已有、记录在组合 Neumann-even/log-weighted-odd 证书中的实际 Weil 结论 ||u/<k,u>-k||<1/100，三角不等式给出

\[
\boxed{\inf_{\sigma\in\{-1,1\}}
\left\|\frac{u}{\langle k,u\rangle}-
\sigma\frac{p_{h_\lambda}^+}{\|p_{h_\lambda}^+\|}\right\|
<\frac{1113}{100000}=0.01113.}
\tag{PM14}
\]

新程序独立运行的是 (PM13)；(PM14) 继承此前真实 Weil 形式及无限耦合证书的纸面/区间范围。这里未重新运行整个 Weil LDL 程序，也未把其域接口变为 Lean 公理。

## 7. 实际验证、研究价值和剩余承重问题

在 110 位和 130 位定向区间精度分别运行同一 verifier，全部八组有限惯性端点检查、两个含完整无限尾的残差检验、分母正性、函数范数和有理误差门均通过。提案生成可使用任意不受信任的数值方法；证书只依赖固定 dyadic 数据、标准区间四则/exp/log/sqrt 和明确的纸面算子界。它依赖 mpmath.iv、Python 与整数实现的正确性，未被 Lean 内核重放。

最终 verifier SHA-256：`42dceb5c81f9aabdc12b51a99d29f0929d81e712f815b49b13bbf9bb5ec56039`。
提案 SHA-256：`242c9897bbd247ef0485039e6dcde819a351c5900ceac52fecc420934c1896db`。
固定 Weil 候选依赖 SHA-256：`8bb067fc5499b0f2e1e48836e7a82237a15504109f82a856c72478d1096d69d0`。

本轮提供了实际文献模型的严格可执行评价，以及它与已认证算术候选的一条具体误差桥。此前任意 dyadic 候选与 prolate 模型的对应尚未量化；(PM13) 在一个含素数尺度消除了这一缺口。它没有证明该距离为零，也没有把这个固定小数外推成尺度衰减律。

研究主体接下来应对同一 p_(h_lambda)^+ 或其带认证误差的有限多项式版本，计算实际 Weil 形式、完整候选正交补以及目标 Fourier 灵敏度。需要沿明确 lambda_n->infinity 的序列证明真实 ground/model 差的条带紧集一致预算消失，而不能仅凭已知 prolate/Xi 模型极限完成拼接。所有整体归一化因子、偶化、低频候选误差、算术 Schur 松弛和高频尾都必须保持对应。Legendre/Galerkin/Schur/区间工具本身是经典方法，本节不作首次发现声明。

参考：

- Connes, Consani, Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1, (7.5)-(7.12), Lemma 7.3, Section 8. https://arxiv.org/html/2511.22755v1
- NIST DLMF 30.2, 30.3 and 30.8, regular spheroidal differential equation, eigenvalues and Ferrers/Legendre expansions. https://dlmf.nist.gov/30.2 ; https://dlmf.nist.gov/30.3 ; https://dlmf.nist.gov/30.8
- Mathlib pinned commit `db584cd6d46c92f209a44c0f1c829460d327499d`, `integral_exp_mul_complex` and interval integrability; existing repository `Zeta23.paperFT`.
- loning #5296, theory source at `9adc8b7e64469344089ce298cb3ab3478aebb21c`, B10.3-B10.4 and B13.4; AlyciaBHZ #5882 and #5895, PR-level scope audit for existing projective/readout formalizations.
