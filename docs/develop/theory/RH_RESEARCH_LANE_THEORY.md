- Connes, Consani, Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1, (7.5)-(7.12), Lemma 7.3, Section 8. https://arxiv.org/html/2511.22755v1
- NIST DLMF 30.2, 30.3 and 30.8, regular spheroidal differential equation, eigenvalues and Ferrers/Legendre expansions. https://dlmf.nist.gov/30.2 ; https://dlmf.nist.gov/30.3 ; https://dlmf.nist.gov/30.8
- Mathlib pinned commit `db584cd6d46c92f209a44c0f1c829460d327499d`, `integral_exp_mul_complex` and interval integrability; existing repository `Zeta23.paperFT`.
- loning #5296, theory source at `9adc8b7e64469344089ce298cb3ab3478aebb21c`, B10.3-B10.4 and B13.4; AlyciaBHZ #5882 and #5895, PR-level scope audit for existing projective/readout formalizations.


---

## [PR #5602] PRIME_MELLIN_INTERTWINING_AND_PARITY_RESIDUAL

# 2026-09-06：真实素数作用的全尺度对数约化与偶化修正的定量保存

Lean：`D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining.lean`。
Scribe：`Blueprint/D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining.scribe.cs`。
独立执行源：`research/weil_ground_mode/certify_prime3_mellin_parity.py`。
精确回归：`research/weil_ground_mode/test_mellin_prime_intertwining.py`。

本节不继续提高固定窗口的最低特征值精度，而是消除明确模型上的一个实际算术作用计算：带原始 Lambda(n)/sqrt(n) 系数的整个单向素数幂平移，可以精确化为对数 seed 的 Mellin 合成。随后把这一结果运输到实际偶化模型，保留其完整奇部分修正。主恒等式对任意窗口尺度成立，未使用未知最低模态、谱间隔或 RH。其算术核心是已有的经典除数恒等式，不作数学首创声明。

## 1. 文献和当前库中的承重位置

Connes 的 2026 年综述 *The Riemann Hypothesis: Past, Present and a Letter Through Time*, arXiv:2602.04022，Sections 6.4-6.6，仍明确区分 prolate 模型的 Xi 极限与真实最低 Weil 模态的充分精确逼近。其 Section 6.4 解释 E 映射、Poisson 关系和近 radical 的来源。这与 Connes-Consani-Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1，Section 8 的两个缺口一致。因此本节研究实际算术作用与 E 的相容性，未将两种算子的自伴性或相似谱图当作模型识别。

本轮读取 loning 的 #5326 实际正文 C13.1-C13.3：固定矩形零点计数需要真实的边界逼近误差与非零下界，局部收敛不能由单个有限深度覆盖所有高度。还读取 AlyciaBHZ 的 #5895 新真源 `NormalizedReadoutDisk.lean`，固定在 `04eaf09b47c39f7688a8df498c4fe30e0663dcbd`：它已保留归一化分子、分母共享误差的协方差。因此本节不重复编写射影、误差球或 Rouché 包装，而补入这些消费者之前的实际 prime/model 算术。

Mathlib 固定版本 `db584cd6d46c92f209a44c0f1c829460d327499d` 已有 `ArithmeticFunction.vonMangoldt_sum`。新证明直接复用它，并复用 `WeilPolynomialMellinWindow.mellin_monomial_polynomial_value` 证明与原多项式模型的逐点一致性。

## 2. 同一窗口、原始系数与明确模型

令 a>=0、lambda=exp(a)，取自然数 M>=exp(2a)。通常采用整数 c=lambda^2=M。设 h: R->C 在 t>lambda 时为零。定义

\[
E_{a,M}h(x)=1_{[-a,a]}(x)\,4e^{x/2}
\sum_{m=1}^{M}h(me^x).
\tag{MP1}
\]

h 的上部支撑使所有不满足 me^x<=lambda 的项自动为零。任意更大的 M 给出同一个窗口模型。定义原始单向 prime block

\[
B_+f(x)=1_{[-a,a]}(x)
\sum_{n=1}^{M}\frac{\Lambda(n)}{\sqrt n}f(x+\log n).
\tag{MP2}
\]

对窗口内零延拓的函数，B_- = B_+^* 是反向平移，S=B_++B_- 是无符号素数块；实际 Weil 算子中的素数贡献是 -S。Lambda(1)=0，所以 n=1 不增加项。对窗口支撑的输入，n>exp(2a) 的平移为零；等于 exp(2a) 的项至多改变端点，L2 算子不变。这一支撑结论不用于任意未截断的输入函数。

为使反射逐点成立，这里使用闭区间。原 `polynomialMellinWindow` 使用左开右闭区间。新 Lean `polynomial_window_agreement` 对截断偶多项式 seed 证明两者在 x!=-a 处逐点相等，因此代表同一个 L2 函数。它不引入第二套 Fourier 定义。一般超额 M 的旧端点求积公式仍须先删除空支撑项；当 M=exp(2a) 为整数时，旧公式的全部 cutoff 条件直接满足。

## 3. 全尺度精确素数作用

新主声明 `prime_forward_mellin_identity` 证明

\[
\boxed{B_+E_{a,M}h=E_{a,M}((\log t)h)-X E_{a,M}h,\qquad Xf(x)=xf(x).}
\tag{MP3}
\]

该恒等式在全部实 x 上逐点成立。Lean 陈述甚至允许 a 为任意实数；负半宽时压缩区间为空。研究应用取 a>0。

证明先处理 x 在窗口内。正整数 n 的平移不会越过左端点；越过右端点时，seed 支撑使原始有限和为零。精确半密度抵消为

\[
\frac{\Lambda(n)}{\sqrt n}\,4e^{(x+\log n)/2}
=4e^{x/2}\Lambda(n).
\]

于是左侧等于

\[
4e^{x/2}\sum_{n,m=1}^{M}\Lambda(n)h(nme^x).
\]

若 nm>M，则 M>=exp(2a)、x>=-a 给出 nme^x>exp(a)，该项确实为零。按 k=nm 重新分组，得到

\[
4e^{x/2}\sum_{k=1}^{M}
\left(\sum_{n\mid k}\Lambda(n)\right)h(ke^x)
=4e^{x/2}\sum_{k=1}^{M}\log k\,h(ke^x).
\]

最后使用 log(k exp(x))=log(k)+x 得到 (MP3)。窗口外两端因同一压缩均为零。所有求和有限，复振幅保持到最后；没有对素数项先取绝对值，也没有遗漏 p^j、j>1 的素数幂。

该结果是原始 prime action 的计算恒等式，不是 prime positivity，也没有证明完整 Weil 形式小。其作用是使后续 Gamma/pole 抵消面对一个明确的 log-seed，而非一个待估计的重复素数双重求和。

## 4. 偶化以后的完整修正

记 Rf(x)=f(-x)、P_+=(I+R)/2、P_-=(I-R)/2，并设

\[
p=E_{a,M}h,\quad e=P_+p,\quad r=P_-p,\quad g=E_{a,M}((\log t)h).
\]

有限 prolate 模式的压缩 Fourier 特征值不必相同，所以一般 r!=0。源文件独立定义两个方向的素数平移，并证明

\[
\boxed{S e=(I+R)g-2Xr-(I+R)B_+r.}
\tag{MP4}
\]

这是 `prime_even_mellin_identity`。推导使用 R B_+ R=B_-、e=p-r 及 e 的偶性：

\[
S e=(I+R)B_+e=(I+R)(g-Xp-B_+r),
\]

而 (I+R)Xp=2Xr。最后一等式中的 x 因子随反射变号，不能漏掉。

定义完整偶化修正

\[
\mathcal C_h=2Xr+(I+R)B_+r.
\tag{MP5}
\]

在 L2([-a,a]) 上，每个压缩平移范数不超过一。若 V_a 是 B_+ 的独立范数上界，例如有限绝对权重和，则

\[
\boxed{\|\mathcal C_h\|_2\le2(a+V_a)\|r\|_2.}
\tag{MP6}
\]

这是 (MP4) 的纸面 L2 推论；本次 Lean 保存的是完整逐点恒等式。对实际 prolate seed 或有限多项式 seed，有限合成在窗口内分段光滑且有界，所以全部配对合法。更一般地，正半轴上的 L2 seed 也可由 t=m exp(x) 的变换逐项证明合成可积。

实际素数二次型因此满足

\[
\boxed{
q_{\rm prime}(e)
=-2\Re\langle e,g\rangle
+2\Re\langle e,Xr+B_+r\rangle.
}
\tag{MP7}
\]

当 e 非零时，省略奇部分造成的归一化能量误差最多为 2(a+V_a)||r||/||e||。这一上界不保证误差相对于真实最低能量或最低谱间隔足够小。

## 5. 真正 prolate 模型上的已执行检验

本次保留同一个 lambda=sqrt(3) 的零积分 prolate 直线，沿用前节 (PM1)-(PM9)，没有重新定义候选或调用未知 Weil ground vector。新 verifier 在载入前校验原 prolate verifier、其 dyadic proposal 和原算术源的 SHA-256，并实际重放整个 prolate 认证，包括遗漏 Legendre 块的惯性夹逼及完整残差。单位模式误差仍严格小于 10^-25。

由有限 Legendre 模型形成的 p_tilde 在 -a、b=a-log2、-b、a 上分段。每段 e_tilde 和 r_tilde 是有限个 exp(plus-or-minus(2j+1/2)x) 的和。g_tilde 的每项还带 x+log(m)。程序完整展开混合项后，使用 exp(tx) 和 x exp(tx) 的端点原函数计算范数、内积，没有数值求积。实际 prime energy 另从原平移积分

\[
-\frac{2\log2}{\sqrt2}\int_{-a}^{a-\log2}
\widetilde e(x)\widetilde e(x+\log2)\,dx
\]

独立算出，而非先设定为 (MP7) 的右侧。

从有限多项式回到真正 prolate 函数时，也控制了 log-seed 误差。全部被使用的 seed 参数 t 都在 [lambda^-1,lambda]，因此 |log(t)|<=a。若 prolate seed 在 [-1,1] 上的误差为 delta_H，令

\[
C=4\sqrt\lambda\sum_{m=1}^{3}m^{-1/2},\qquad \epsilon=C\delta_H.
\]

则 ||p-p_tilde||<=epsilon，||g-g_tilde||<=a epsilon，偶、奇投影各自也满足相同的 epsilon 预算。这个步骤只作用于有界的实际 prime/log-seed 配对，不把 L2 误差当作完整无界 Gamma 形式的误差。

令 n=||e_tilde||，并用 Q>=||g_tilde||，V=log2/sqrt2。程序选用独立的 Q=a C(1+|ratio|)。设

\[
Z=-\langle e,S e\rangle+2\Re\langle e,g\rangle,
\qquad\widetilde Z=-\langle\widetilde e,S\widetilde e\rangle
+2\Re\langle\widetilde e,\widetilde g\rangle.
\]

使用 ||S||<=2V，得到

\[
|Z-\widetilde Z|\le
[2V(2n+\epsilon)+2(an+Q+a\epsilon)]\epsilon=:\Delta_Z.
\]

且 |Z_tilde|<=2Vn^2+2nQ、| ||e||^2-n^2 |<=(2n+epsilon)epsilon。验证 n>epsilon 后，归一化误差预算为

\[
\boxed{
\left|\frac Z{\|e\|^2}-\frac{\widetilde Z}{n^2}\right|
\le\frac{\Delta_Z}{(n-\epsilon)^2}
+\frac{(2Vn^2+2nQ)(2n+\epsilon)\epsilon}{n^2(n-\epsilon)^2}.
}
\tag{MP8}
\]

实际算出的 (MP8) 上界小于 4.495e-23。它保留归一化分母变化，未把历史 norm JSON 当作新计算输入。

## 6. 认证的有理结论与能量尺度

对真正的 prolate 模型，定向区间验证给出

\[
\boxed{\frac{76}{10^6}<\frac{\|r\|_2}{\|e\|_2}<\frac{77}{10^6}.}
\tag{MP9}
\]

因此未偶化的算术模型确实具有非零奇部分。对实际归一化素数能量，

\[
\boxed{-\frac{18173952}{10^9}
<\frac{q_{\rm prime}(e)}{\|e\|^2}
<-\frac{18173950}{10^9}.}
\tag{MP10}
\]

更重要的是，对省略奇修正的实际能量差，有

\[
\boxed{-\frac{44}{10^8}
<\frac{q_{\rm prime}(e)+2\Re\langle e,g\rangle}{\|e\|^2}
<-\frac{43}{10^8}.}
\tag{MP11}
\]

显示用的多项式值约为 -4.3582252062e-7。前面的误差预算已经将该区间运输到真正 prolate 模型。其绝对值严格大于 7U，其中 U=560909/10^13 是此前真实 Weil 最低值的上界。这个比较仅说明该模型修正在现有研究所需的能量尺度上不能忽略；它没有给出模型完整 Rayleigh 商或新的最低特征值区间。

同时 (MP6) 给出可实际使用的算子作用预算

\[
\boxed{\|\mathcal C_h\|_2/\|e\|_2<159/10^6.}
\tag{MP12}
\]

(MP11) 是有符号实际配对的认证；(MP12) 是较粗的范数上界。两者不可互换。保留修正后，后续可以继续利用它与 Gamma/pole 项的抵消。

## 7. 形式化范围与复验

`prime_forward_mellin_identity` 对任意尺度、任意复 seed、完整有限 cutoff 和所有实 x 给出 (MP3) 的证明脚本。`prime_even_mellin_identity` 保存完整 (MP4)。`polynomial_window_agreement` 接回既有多项式模型。独立新定义只描述这次需要的实际 E 和平移作用；既有 von Mangoldt、Fourier 与 Weil 对象保持不变。

`test_mellin_prime_intertwining.py` 实际执行 258 组精确函数回归，每组同时检查两个恒等式。乘法坐标、支撑测试都用有理数；对数用素因子指数向量表示，系数是精确复有理根式，不使用浮点容差。测试覆盖整数及非整数 lambda、额外无效 cutoff、窗口内外和端点。错误半密度、删除高阶素数幂、删除奇修正和不足 cutoff 四个指定变体均有实际失败见证。这些回归是开发检查，不能替代 Lean 内核证明。

新定向区间 verifier 在 110 位和 130 位分别实际运行通过。没有运行 GitHub CI、Lean elaboration、Scribe emission 或传递公理报告。定向区间证书依赖 mpmath.iv、Python 和前节说明的 prolate 算子识别及谱估计。没有将它标为完整内核结果。

新 verifier SHA-256：`16e0de27325376e8c7627297d406bc4720b3708f5826c8f7cd7096e6c9d59961`。
精确回归源 SHA-256：`7101362a568224039fe339838d7a355c54beffba923ab7745d46652bc1919ade`。
原 prolate verifier SHA-256：`42dceb5c81f9aabdc12b51a99d29f0929d81e712f815b49b13bbf9bb5ec56039`。

## 8. 下一条实际残差等式及剩余开放问题

对当前分段光滑的实际模型，每个固定尺度有有限个断点，零延拓 Fourier 变换为 O(1/|t|)。Gamma 乘子为 O(log(2+|t|))，所以其乘积属于 L2。加上有限有界素数与 pole 项，可用同一 Friedrichs 配对识别其算子域。这是纸面定义域论证，未包含在本次 Lean 声明中。

于是对明确 e=P_+E h 和任意实 mu，完整残差可准确写成

\[
\boxed{
(A_a-\mu)e
=A_\Gamma e+A_{\rm pole}e-(I+R)E((\log t)h)
+\mathcal C_h-\mu e.
}
\tag{MP13}
\]

本节已把原始素数作用从该等式中的未知算术双重和，约化为显式 log-seed 与完全保留的奇修正。真正需要继续攻克的是 (MP13) 中 Gamma/pole/log-seed 的相消，以及其同候选正交补之间的定量关系。经典的全局 E-radical 或 Poisson 说法有自身的 Schwartz、零值、零积分与边界条件，不能直接作用于截断 prolate 函数并删除这些修正。

(MP3)-(MP4) 已具有参数族形式，(MP9)-(MP12) 目前只在 lambda=sqrt(3) 兑现数值认证。尚未证明无界尺度上的 small residual/gap、simple-even ground family 或真实 ground Fourier 的 Xi 极限。此次结果不会自动绕过前面的固定内缩平移障碍，也不表示素数范数预算本身已统一有界。

参考：

- A. Connes, *The Riemann Hypothesis: Past, Present and a Letter Through Time*, arXiv:2602.04022, Sections 6.4-6.6. https://arxiv.org/html/2602.04022
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1, Lemma 7.3 and Section 8. https://arxiv.org/html/2511.22755v1
- Mathlib `ArithmeticFunction.vonMangoldt_sum`, pinned `db584cd6d46c92f209a44c0f1c829460d327499d`, `Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean`.
- loning #5326, `3beb435bf9ca8aa35aa6079ea4033a9c2e6c9007`, actual theory C13; AlyciaBHZ #5895, `04eaf09b47c39f7688a8df498c4fe30e0663dcbd`, actual `NormalizedReadoutDisk.lean`.
