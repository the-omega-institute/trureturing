# 公共等价质量的最大剥离、指数余量与终端信息

## 0. 对象、结论与文献位置

本卷研究一条固定有限标记产生器的实际输出律。公共等价质量可以永久保留；需要估计的是有限前缀尚未兑现的质量，以及初始隐状态后验相对于其终端后验的剩余信息。主结论不要求隐状态最终可识别，不要求标记乘积严格为正，也不要求平均转移不可约或非周期。

复合论证由三步组成：最大剥离使剩余行的闭支撑面不含等价概率对；有限多个不相容支撑面给出固定产生器的正分离量；有限时域亲和质量的递推给出指数余量。其成本因子保留为 $\sqrt{t(1-t)}$，直接支付终端信息积分中的 $dt/t$。

等价有限测度、有限语言等价和公共等价子分布沿用 Chen–Kiefer [CK]；有限检验与支撑剖面的背景见 Kiefer–Sistla [KS]；成本帐篷与正权积分表示见 Reid–Williamson [RW]。本卷的指数结论由下文的剥离证明承担，不作为上述文献中定理的转述。原始二进制应用沿用加权熵矩到实际擦除尾的同律接口 [EWM]，以及多字响应的尾证书接口 [MW]。这些支撑结论在新的复合证明中明确注明来源，不主张全球优先权。

## 1. 有限标记产生器与等价有限测度

**定义 1.1（产生器、行质量与全部柱集）。** 设 $\Sigma$ 是非空有限字母表，隐状态集为 $[d]=\{1,\ldots,d\}$，$d\geq1$。对每个 $y\in\Sigma$ 给定实矩阵 $B_y\geq0$，并要求

$$
B=\sum_{y\in\Sigma}B_y,\qquad B\mathbf1=\mathbf1.
$$

所有行均按行向量理解。非负子分布 $r$ 满足 $|r|:=r\mathbf1\leq1$。对有限词 $w=y_1\cdots y_n$，令 $B_w=B_{y_1}\cdots B_{y_n}$；空词 $\varepsilon$ 满足 $B_\varepsilon=I$。行 $r$ 诱导未来输出有限测度 $\mu_r$，其柱集质量为

$$
\mu_r([w])=rB_w\mathbf1=|rB_w|.
$$

一致性来自 $\sum_y rB_wB_y\mathbf1=rB_w\mathbf1$；空柱集的质量是 $|r|$。记 $u\equiv v$ 表示所有有限词，包括空词，都满足 $uB_w\mathbf1=vB_w\mathbf1$。这等价于 $\mu_u=\mu_v$，尤其蕴含 $|u|=|v|$。全部行不等式均逐坐标解释。

**定义 1.3（最大公共等价质量及原始证书缺口）。** 对任意非负子分布行 $r,v$，定义

$$
c(r,v)=
\max\{|u|:0\leq u\leq r,\ 0\leq z\leq v,\ u\equiv z\},
$$

以及对 $n\geq0$ 定义

$$
G_n(r,v)=
\sum_{w\in\Sigma^n}
\bigl[\min(|rB_w|,|vB_w|)-c(rB_w,vB_w)\bigr].
$$

最大值的存在性在定理 3.1 证明开头的「共同有限时域与最大对存在性」步骤中证明。每项满足 $0\leq c(rB_w,vB_w)\leq\min(|rB_w|,|vB_w|)$，所以 $G_n\geq0$。$n=0$ 的和只有空词一项。

这些是 [CK, Section 4] 的公共等价子分布量在任意成本质量下的写法。它们保留两条原始行，既不要求两行质量相等，也不把等价解释成相同隐状态。等价对可以相加；若 $u\equiv z$，则对任意词 $w$ 有 $uB_w\equiv zB_w$。

## 2. 最大剥离与闭支撑面的正分离

**定义 2.1（闭支撑面）。** 固定 $L=2d$。对非空 $S\subseteq[d]$，令

$$
D(S)=\{\alpha\geq0:|\alpha|=1,\ \alpha_j=0\text{ 对 }j\notin S\},
\qquad
Q_L(\alpha)=(\alpha B_w\mathbf1)_{w\in\Sigma^L}.
$$

$D(S)$ 是闭概率单纯形；允许其边界行的支撑严格小于 $S$。$Q_L(\alpha)$ 是概率向量。称 $(S,T)$ 不相容，若

$$
Q_L(D(S))\cap Q_L(D(T))=\varnothing.
$$

相容恰好表示两个闭面中存在未来输出等价的概率行；这一对应在定理 3.1 证明开头的「共同有限时域与最大对存在性」步骤中证明。

**引理 2.2（最大剥离排除闭面上的等价对）。** 选取实现 $c(r,v)$ 的对 $u,z$，置 $R=r-u$、$S'=v-z$。则 $c(R,S')=0$。若 $|R|,|S'|>0$，则 $(\operatorname{supp}R,\operatorname{supp}S')$ 不相容，包括闭面的所有边界概率行。

证明。若剩余行中还有正质量等价对，便可把它加到 $u,z$，与最大性矛盾。若上述闭面相容，取其中等价概率行 $\alpha,\beta$。每个 $\alpha_j>0$ 的坐标都满足 $R_j>0$，每个 $\beta_j>0$ 的坐标都满足 $S'_j>0$。因此可取

$$
0<\eta\leq
\min\left(
\min_{\alpha_j>0}\frac{R_j}{\alpha_j},
\min_{\beta_j>0}\frac{S'_j}{\beta_j}
\right).
$$

此时 $\eta\alpha\leq R$、$\eta\beta\leq S'$，且二者等价、质量均为 $\eta$，再次矛盾。边界概率行的零坐标不需除法；这正是闭面而非仅相对内部也被排除的原因。

**定义 2.3（固定产生器剖面）。** 若存在不相容非空支撑对，定义

$$
\zeta=
\min_{\substack{S,T\ne\varnothing\\(S,T)\ \mathrm{不相容}}}
\ \min_{\alpha\in D(S),\ \beta\in D(T)}
\operatorname{TV}(Q_L(\alpha),Q_L(\beta)),
\qquad
\kappa=1-\frac{\zeta^2}{2},
$$

其中有限概率向量的 $\operatorname{TV}(p,q)=\frac12\sum_j|p_j-q_j|$。每对不相容闭面的像是紧且不相交的集合，故其距离最小值严格为正。非空支撑对只有有限多个，于是

$$
0<\zeta\leq1,\qquad \frac12\leq\kappa<1.
$$

这是一条固定产生器内由最大剥离产生的正量，不是附加的正性假设。其定义未要求有限预测状态空间，也未给出跨参数族的正下界。

**引理 2.4（全等价退化情形）。** 若没有不相容非空支撑对，则每个单点状态的未来输出律相同，所有概率行彼此等价，且对任意 $r,v,n$ 有 $c(r,v)=\min(|r|,|v|)$ 和 $G_n(r,v)=0$。

证明。两个单点闭面各只含对应 Dirac 行；它们相容就意味着这两行等价。线性性使任意概率行等价。若 $a=|r|$、$b=|v|$ 均为正，令 $h=\min(a,b)$，则 $u=(h/a)r$、$z=(h/b)v$ 是质量 $h$ 的可行等价对；若一行质量为零，结论由零对成立。相同论证用于每个前缀的两行，得到 $G_n=0$。此情形无需定义 $\zeta$。

**引理 2.5（剥离剩余行的亲和质量损失）。** 在定义 2.3 的情形，若 $c(R,S')=0$，则

$$
\sum_{z\in\Sigma^L}\sqrt{|RB_z|\,|S'B_z|}
\leq\kappa\sqrt{|R|\,|S'|}.
$$

对任意非负行 $R,S'$ 及任意 $s\geq0$，还成立无损系数版本

$$
\sum_{z\in\Sigma^s}\sqrt{|RB_z|\,|S'B_z|}
\leq\sqrt{|R|\,|S'|}.
$$

证明。对概率向量 $p,q$，令 $A(p,q)=\sum_j\sqrt{p_jq_j}$。Cauchy–Schwarz 给出

$$
2\operatorname{TV}(p,q)
\leq
\sqrt{\sum_j(\sqrt{p_j}-\sqrt{q_j})^2
      \sum_j(\sqrt{p_j}+\sqrt{q_j})^2}
=2\sqrt{1-A(p,q)^2}.
$$

因此

$$
A(p,q)\leq\sqrt{1-\operatorname{TV}(p,q)^2}
\leq1-\frac12\operatorname{TV}(p,q)^2.
$$

若两条剩余行的质量均为正，引理 2.2 使其归一化行处于不相容闭面；长度 $L$ 输出的总变差至少为 $\zeta$，代入即得第一式。若一行质量为零，两边都为零。第二式直接来自 Cauchy–Schwarz 及

$$
\sum_{z\in\Sigma^s}|RB_z|=|R|,
\qquad
\sum_{z\in\Sigma^s}|S'B_z|=|S'|.
$$

这里仅用有限时域的亲和损失，未声称剩余行的完整未来测度互相奇异。

## 3. 原始证书的无条件固定产生器指数界

**定理 3.1（公共等价质量最大剥离定理）。** 对定义 1.1 的任意固定有限标记产生器，若存在不相容支撑对，则上述 $L=2d$ 及定义 2.3 的 $\kappa<1$ 满足：对任意非负子分布行 $r,v$ 和每个 $n\geq0$，

$$
0\leq G_n(r,v)
\leq\sqrt{|r|\,|v|}\ \kappa^{\lfloor n/L\rfloor}.
$$

若没有不相容支撑对，则所有 $G_n$ 恒为零。两种结论均不要求平稳性、不可约性、非周期性、路径合并性或标记乘积正性。

证明。**共同有限时域与最大对存在性。** 取 $L=2d$。任意两条实数行在全部长度 $L$ 柱集上的线性读数相等，当且仅当它们在全部有限柱集上的线性读数相等。

令

$$
V_m=\operatorname{span}\{B_w\mathbf1:|w|\leq m\}.
$$

$V_0$ 的维数为一，且

$$
V_{m+1}=\operatorname{span}\bigl(V_m\cup\{B_yv:y\in\Sigma,\ v\in V_m\}\bigr).
$$

若 $V_m=V_{m+1}$，则 $V_m$ 对每个 $B_y$ 不变，故已包含全部柱集向量。维数至多为 $d$，所以至迟 $V_{d-1}$ 已稳定。另一方面，对 $|w|\leq L$，

$$
\sum_{z\in\Sigma^{L-|w|}}B_{wz}\mathbf1
=B_wB^{L-|w|}\mathbf1=B_w\mathbf1.
$$

长度 $L$ 的等式因而蕴含全部较短等式，继而蕴含整个稳定空间上的等式。逆向立即成立。这是 [CK, Proposition 3(c) 与 Appendix A] 的有限语言等价机制；上述线性论证直接适用于实数项，不借用有理编码的算法复杂度结论。

由上述共同有限时域，等价条件给出有限个闭线性等式，行不等式给出有界闭集，零对可行；故定义 1.3 的最大值存在。定义 2.1 中的相容也因此恰好表示两个闭面中存在未来输出等价的概率行。

**原始行最大剥离递推。** 先处理有不相容对的情形。在空前缀处选取最大等价对，得到

$$
r=U_\varepsilon+R_\varepsilon,\qquad
v=V_\varepsilon+S_\varepsilon,\qquad
U_\varepsilon\equiv V_\varepsilon,\qquad
c(R_\varepsilon,S_\varepsilon)=0.
$$

在每个长度 $kL$ 的前缀 $w$ 处维持不变量

$$
rB_w=U_w+R_w,\qquad vB_w=V_w+S_w,\qquad
U_w\equiv V_w,\qquad c(R_w,S_w)=0,
$$

且四行均非负。对长度 $L$ 的扩展词 $z$，先将四行乘以 $B_z$，再从 $R_wB_z,S_wB_z$ 中选取最大等价对 $a_{wz},b_{wz}$。定义

$$
\begin{aligned}
U_{wz}&=U_wB_z+a_{wz},&
V_{wz}&=V_wB_z+b_{wz},\\
R_{wz}&=R_wB_z-a_{wz},&
S_{wz}&=S_wB_z-b_{wz}.
\end{aligned}
$$

等价在乘法与加法下保持，引理 2.2 使新的剩余行仍满足 $c=0$，故不变量归纳成立。特别地，所有累计剥离行始终逐坐标受原始行 $rB_w,vB_w$ 支配。每个有限深度仅需有限个已证明存在的最大对。

置

$$
A_k=\sum_{w\in\Sigma^{kL}}\sqrt{|R_w|\,|S_w|}.
$$

初始 $A_0\leq\sqrt{|r|\,|v|}$。每次剥离从两行中减去相同非负质量，因此不会增大剩余质量的乘积。引理 2.5 遂给出

$$
\begin{aligned}
A_{k+1}
&\leq
\sum_{w\in\Sigma^{kL}}\sum_{z\in\Sigma^L}
\sqrt{|R_wB_z|\,|S_wB_z|}\\
&\leq\kappa A_k
\leq\kappa^{k+1}\sqrt{|r|\,|v|}.
\end{aligned}
$$

最后写 $n=kL+s$，$0\leq s<L$。对末尾 $s$ 个符号只传播上述分解，不再要求剥离；在每个长度 $n$ 的前缀 $a$ 仍有原始行分解及 $U_a\equiv V_a$。令 $h_a=|U_a|=|V_a|$。累计等价对对原始 $c(rB_a,vB_a)$ 可行，所以

$$
c(rB_a,vB_a)\geq h_a,
\qquad
\min(|rB_a|,|vB_a|)
=h_a+\min(|R_a|,|S_a|).
$$

从而原始证书的该项满足

$$
\min(|rB_a|,|vB_a|)-c(rB_a,vB_a)
\leq\min(|R_a|,|S_a|)
\leq\sqrt{|R_a|\,|S_a|}.
$$

求和并应用引理 2.5 的系数一余段界，得到 $G_n(r,v)\leq A_k$，即所需结论。累计对不必实现原始 $c$ 的最大值；其可行性给出的是这里所需的上界方向。零行使相应乘积和缺口同时为零，$n=0$ 也已包含。无不相容对的情形由引理 2.4 完成。

## 4. 终端后验、永久歧义与精确成本积分

**定义 4.1（实际初始状态与输出）。** 给定定义 1.1 的产生器和任意概率行 $\pi$，令 $J$ 是先取 $H_0\sim\pi$，再按标记边转移产生 $Y_0,Y_1,\ldots$ 的实际联合律；其输出边缘律记为 $P$。设

$$
\mathcal F_n=\sigma(Y_0,\ldots,Y_{n-1}),\qquad
\mathcal F_\infty=\sigma(Y_j:j\geq0),
\qquad
p_n(i)=J(H_0=i\mid\mathcal F_n).
$$

$\mathcal F_0$ 是平凡场，$p_\infty(i)=J(H_0=i\mid\mathcal F_\infty)$。全部熵和 KL 采用自然对数，$0\log0=0$。定义

$$
\ell_n=
H_J(H_0\mid\mathcal F_n)-H_J(H_0\mid\mathcal F_\infty)
=\mathbb E_J D_{\mathrm{KL}}(p_\infty\Vert p_n).
$$

最后的等式来自 $p_n=\mathbb E[p_\infty\mid\mathcal F_n]$。若 $p_n(i)=0$，则同一事件上 $p_\infty(i)=0$ 几乎处处；对非负交叉熵用条件期望，得到 $\mathbb E[-p_\infty(i)\log p_n(i)]=\mathbb E[-p_n(i)\log p_n(i)]$。所以不需要假设后验坐标有正下界。终端条件熵可以严格为正；它在 $\ell_n$ 中明确扣除。

**定义 4.2（成本帐篷与证书）。** 对 $0<t<1$ 令

$$
\psi(u,t)=\min((1-t)u,t(1-u)),\qquad
b_{i,n}(t)=\mathbb E_J\psi(p_n(i),t),\qquad
\delta_{i,n}(t)=b_{i,n}(t)-b_{i,\infty}(t).
$$

在同一产生器上取两条成本行

$$
r_{i,t}=(1-t)\pi_i e_i,\qquad
v_{i,t}=t(\pi-\pi_i e_i),
$$

其中 $e_i$ 是第 $i$ 个 Dirac 行。定义

$$
c_{i,n}(t)=\sum_{w\in\Sigma^n}c(r_{i,t}B_w,v_{i,t}B_w),
\qquad
g_{i,n}(t)=b_{i,n}(t)-c_{i,n}(t).
$$

成本行是实际联合律的一对加权子测度，未改变产生器或观察字段。零前缀质量不需定义条件行，其对应质量项为零。

## 5. 精确成本因子与指数期望终端 KL

**定理 5.1（期望终端信息的固定产生器指数界）。** 对定义 4.1 的任意实际初始概率行 $\pi$，在存在不相容支撑对的情形，定理 3.1 的常数满足

$$
g_{i,n}(t)
\leq
\sqrt{\pi_i(1-\pi_i)t(1-t)}\
\kappa^{\lfloor n/L\rfloor}
$$

对每个 $i,n$ 和 $0<t<1$ 同时成立。记

$$
K_\pi=\frac{\pi_{\mathrm{circ}}}{2}
\sum_{i=1}^d\sqrt{\pi_i(1-\pi_i)},
$$

其中 $\pi_{\mathrm{circ}}$ 是圆周率，则

$$
\begin{gathered}
0\leq\ell_n=\mathbb E_JD_{\mathrm{KL}}(p_\infty\Vert p_n)
\leq K_\pi\kappa^{\lfloor n/L\rfloor},\\
\sum_{n\geq0}\ell_n\leq\frac{K_\pi L}{1-\kappa},\qquad
\sum_{n\geq R}\ell_n
\leq\frac{K_\pi L}{1-\kappa}\kappa^{\lfloor R/L\rfloor}
\quad(R\geq0).
\end{gathered}
$$

若没有不相容支撑对，则 $p_n=p_\infty=\pi$ 几乎处处，全部 $\ell_n$ 为零。

证明。**成本面积与公共子测度。** 对全部状态 $i$、$n\geq0$ 和 $0<t<1$，

$$
\begin{gathered}
b_{i,n}(t)=
\sum_{w\in\Sigma^n}\min(|r_{i,t}B_w|,|v_{i,t}B_w|),\\
c_{i,n}(t)\leq b_{i,\infty}(t)\leq b_{i,n}(t),\\
0\leq\delta_{i,n}(t)\leq g_{i,n}(t)
=G_n(r_{i,t},v_{i,t})\leq t(1-\pi_i)\leq t,\\
\ell_n=\sum_{i=1}^d\int_0^1\delta_{i,n}(t)\,\frac{dt}{t}.
\end{gathered}
$$

$p_n(i)=\mathbb E[p_\infty(i)\mid\mathcal F_n]$，而 $\psi(\cdot,t)$ 凹，故 $\delta\geq0$。在一个前缀上，两个实际加权假设的质量分别为 $|r_{i,t}B_w|$、$|v_{i,t}B_w|$，得到第一式。

在完整未来上，两个假设相对于实际边缘律 $P$ 的密度是 $(1-t)p_\infty(i)$ 和 $t(1-p_\infty(i))$，其重叠质量正是 $b_{i,\infty}(t)$。每个前缀中的可行等价对诱导同一未来有限测度；行支配和矩阵非负性使它同时受两个实际尾测度支配。给该测度接上前缀，再对互不相交的前缀柱集求和，得到实际完整未来上的公共子测度。因此各前缀最大质量之和不超过 $b_{i,\infty}(t)$。这证明证书方向，并由帐篷的第二分支得到 $g\leq b_{i,n}\leq t(1-\pi_i)$。

对 $0<u<1$ 在 $t=u$ 处分段，

$$
\int_0^1\psi(u,t)\,\frac{dt}{t}
=u(1-u)+u[-\log u-1+u]
=-u\log u.
$$

$u=0,1$ 时帐篷恒为零，等式仍成立。这是 [RW, Corollary 3 与 Theorem 14] 的成本积分机制在单个熵坐标上的端点写法。对每个后验应用非负 Tonelli，得到其条件熵表达；两份条件熵都有限，且逐成本差非负，因而可相减得到最后一式。再次应用 Tonelli 还得

$$
\sum_{n\geq0}\ell_n
=\sum_{i=1}^d\int_0^1
\left(\sum_{n\geq0}\delta_{i,n}(t)\right)\frac{dt}{t},
$$

作为非负扩展量的等式。永久 Bayes 歧义 $b_{i,\infty}(t)$ 始终被扣除，没有以完美隐状态分类代替终端后验。

这些面积与公共子测度公式是指数定理的输入接口；单凭其定性趋零，不能推出可求和率。

**精确成本因子与终端积分。** 成本行的质量分别为 $(1-t)\pi_i$ 和 $t(1-\pi_i)$。把它们代入定理 3.1，即得精确的成本因子。再用上述成本面积与公共子测度公式，并直接支付端点权重：

$$
\begin{aligned}
\int_0^1\sqrt{t(1-t)}\,\frac{dt}{t}
&=\int_0^{\pi_{\mathrm{circ}}/2}2\cos^2u\,du\\
&=\frac{\pi_{\mathrm{circ}}}{2},
\qquad t=\sin^2u.
\end{aligned}
$$

于是得到 $\ell_n$ 的指数界。每块恰有 $L$ 个整数，几何求和给出总和界；从包含 $R$ 的整块开始求和，给出尾界。$\pi_i=0$ 或 $1$ 时两个后验帐篷及证书缺口均为零，对应 $K_\pi$ 项也为零。成本端点 $t=0,1$ 可按零帐篷延拓，不需在端点赋予 $dt/t$ 有限值。

无不相容对时，所有初始状态的完整未来律相同，故 $H_0$ 与输出未来独立，后验始终是 $\pi$，结论成立。

**推论 5.2（成本一致率及其限度）。** 在定理 5.1 的非退化情形，令 $\rho=\kappa^{1/L}$、$C=1/(4\kappa)$。则 $g_{i,n}(t)\leq C\rho^n$ 对全部 $i,t,n$ 成立。

证明。$\pi_i(1-\pi_i)\leq1/4$、$t(1-t)\leq1/4$，且 $\kappa^{\lfloor n/L\rfloor}\leq\kappa^{-1}\rho^n$。

期望信息界使用的是更精确的 $\sqrt{t(1-t)}$ 因子。若只保留与 $t$ 无关的指数包络，直接积分 $dt/t$ 会失去可积性；另用 $g\leq t$ 才会得到带对数惩罚的粗界。这里的精确面积避免了额外的 $n$ 因子。

率对一个固定产生器的全部成本与状态一致，且对每条固定实际初始律成立。它不提供跨 $d$ 或跨产生器参数的统一率，不提供常数与半径的高效取得，也不声称存在有限预测状态表示。率的来源是最大剥离后的闭面分离与亲和递推，不是平均转移的本原性、有限线性维数或后验收敛本身。

## 6. 原始完整 $\Theta_N$ 与发射比特时钟

**定义 6.1（完整合法二进制域及实际联合律）。** 对每个有限 $N\geq1$，取 $\lambda\in\mathbb R^{1\times N}$、$M_0,M_1\in\mathbb R^{N\times N}$，保留整个域

$$
\begin{aligned}
\Theta_N=\{(\lambda,M_0,M_1):\;&
\lambda\geq0,\quad\lambda\mathbf1=1,\quad M_0,M_1\geq0,\\
&A=M_0+M_1,\quad A\mathbf1=\mathbf1,\quad
\lambda A=\lambda,\quad
\lambda M_1^2\mathbf1=0\}.
\end{aligned}
$$

矩阵项均为实数。对应实际双侧平稳标记边联合律为

$$
J_\theta[H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=x_a,\ldots,X_b=x_b]
=\lambda_{h_a}\prod_{j=a}^{b}(M_{x_j})_{h_jh_{j+1}},
$$

输出边缘律满足 $P_\theta[X_{a:b}=w]=\lambda M_w\mathbf1$。合法性约束使实际输出没有相邻 $11$；不把它加强为原始矩阵的逐项 $M_1^2=0$。全部零平稳质量状态仍在原始呈现中。

直接取 $B_0=M_0$、$B_1=M_1$、$d=N$、$\pi=\lambda$、$L=2N$。定理 3.1 与 5.1 在这一实际产生器上应用，无需先取本原分量、改换字母表或重标时间。下文的 $n,r,R$ 始终是原始发射比特的整数尺度。

**定义 6.2（可见熵矩与隐状态余量）。** 在同一实际律上设

$$
\begin{aligned}
\mathcal P^-&=\sigma(X_j:j\leq-1),&
h_k&=H_{P_\theta}(X_0\mid X_{-k:-1}),\\
h&=H_{P_\theta}(X_0\mid\mathcal P^-),&
a_k&=h_k-h\geq0,\\
R_n&=\sum_{k\geq n}a_k,&
T_{P_\theta}&=\sum_{k\geq0}(k+1)a_k=\sum_{n\geq0}R_n.
\end{aligned}
$$

空块在 $k=0$ 时给出无条件熵。$\ell_n$ 使用 $J_\theta$ 的实际 $H_0$ 与 $\mathcal F_n=\sigma(X_{0:n-1})$。定义隐状态松弛量

$$
s_n=I_{J_\theta}(H_0;X_{n:\infty}\mid X_{-\infty:n-1})\geq0.
$$

**定义 6.4（实际完整反侧半线擦除字段）。** 对同一 $P_\theta$ 定义

$$
\begin{aligned}
q&=\mathbb E_{P_\theta}[X_0\mid\sigma(X_j:j\ne0)],\\
p_{L,r}&=\mathbb E_{P_\theta}[X_0\mid\sigma(X_{-r:-1},X_{1:\infty})],\\
p_{R,r}&=\mathbb E_{P_\theta}[X_0\mid\sigma(X_{-\infty:-1},X_{1:r})],\\
e_L(r)&=\mathbb E_{P_\theta}(q-p_{L,r})^2,\qquad
e_R(r)=\mathbb E_{P_\theta}(q-p_{R,r})^2,\\
\tau_{P_\theta}(R)&=\sum_{r\geq R}(e_L(r)+e_R(r)).
\end{aligned}
$$

$r=0$ 的有限侧为空块。两条完整反侧半线均未缩短，字段未加入隐状态、分量标签或估计标签。

沿用 [EWM] 的同律熵到完整半线擦除比较：

$$
e_L(r),e_R(r)\leq\frac12R_r,\qquad
\tau_{P_\theta}(R)
\leq\sum_{r\geq R}R_r
=\sum_{k\geq R}(k-R+1)a_k.
$$

该支撑比较适用于任意实际双侧平稳二进制律，右侧可为无限量。它通过有限外部块的 Bernoulli KL 比较、向联合块的熵链式提升、条件投影极限及反向律相同的块熵差得到；其前提没有有限隐状态同步或正标记词。此处只复用该接口。

**定理 6.5（每条原始有限律的加权熵矩与实际尾预算）。** 对每个 $N\geq1$ 和每个固定 $\theta\in\Theta_N$，若其原始标记产生器存在不相容支撑对，则上述 $L=2N$、$\kappa$、$K_\lambda$ 给出

$$
\begin{gathered}
R_n,\ s_n\leq\ell_n
\leq K_\lambda\kappa^{\lfloor n/L\rfloor},\\
T_{P_\theta}\leq\sum_{n\geq0}\ell_n
\leq\frac{K_\lambda L}{1-\kappa}<\infty,\\
\tau_{P_\theta}(R)\leq\eta_\theta(R)
:=\frac{K_\lambda L}{1-\kappa}\kappa^{\lfloor R/L\rfloor}
<\infty,\qquad
\eta_\theta(R)\longrightarrow0.
\end{gathered}
$$

若没有不相容支撑对，则 $\ell_n=R_n=s_n=0$，$T_{P_\theta}=0$、$\tau_{P_\theta}(R)=0$，可取 $\eta_\theta(R)=0$。

证明。**同律熵余量分解。** 上述实际平稳有限标记律满足

$$
\ell_n=R_n+s_n,\qquad 0\leq R_n,s_n\leq\ell_n.
$$

平稳性及条件熵链式法则给出，对每个有限 $m\geq1$，

$$
I_{P_\theta}(\mathcal P^-;X_{n:n+m-1}\mid X_{0:n-1})
=\sum_{k=n}^{n+m-1}a_k.
$$

给定实际切口状态 $H_0$，标记边过去与整个输出未来条件独立。对有限尾块应用互信息链式法则，得到

$$
\begin{aligned}
I_{J_\theta}(H_0;X_{n:n+m-1}\mid X_{0:n-1})
&=I_{P_\theta}(\mathcal P^-;X_{n:n+m-1}\mid X_{0:n-1})\\
&\quad+I_{J_\theta}(H_0;X_{n:n+m-1}\mid X_{-\infty:n-1}).
\end{aligned}
$$

令 $m\to\infty$，条件互信息对递增尾场的连续性给出所述恒等式。左侧不超过有限的 $H_J(H_0)$，故不会出现无限量相减。此分解是可见熵矩与终端隐状态信息之间的同律支撑关系；$s_n$ 是非负隐信息，不能混同于平方损失的有符号差。

**原始比特尾预算。** 将原始矩阵和先验直接代入定理 5.1，用上述同律熵余量分解控制 $R_n,s_n$，再用 [EWM] 的两侧比较及非负求和。$R$ 起始的尾求和由定理 5.1 支付。这些都是同一实际 $J_\theta/P_\theta$ 上的期望量；$\eta_\theta$ 是确定性原始比特半径函数，其构造没有使用负荷最优性或有限取得假设。

可见量 $T_{P_\theta}$ 只依赖输出律；$\ell_n,K_\lambda,\kappa$ 可以依赖所选有限呈现。本结论没有把呈现相关常数解释成可见律的最小常数。若熵以比特计量，[EWM] 的自然对数熵项需乘 $\ln2$；平方损失与发射比特尺度不重标。

## 7. 边界与适用范围

所有剥离行都是受原始柱集行支配的解析子分布。剥离只用于证明，未删去实际律中的公共输出质量，未定义替代的平稳产生器。终端歧义由 $H(H_0\mid\mathcal F_\infty)$ 与 $b_{i,\infty}(t)$ 扣除，不能把本结果解释成它们趋于零。

结构零与零质量词给出零质量项；一条输入行质量为零时，证书及亲和乘积均为零。零先验坐标在信息积分中也严格贡献零，不需剪裁原始 $\Theta_N$。全等价情形单独处理，因此不从空的不相容集合取最小值。

可约与周期平稳产生器在定理 6.5 内直接适用。没有对 $A$、某个 $M_w$ 或某对路径施加正性与合并要求；隐藏周期未被换算成新的时间单位。

条件期望的零质量纤维版本不影响任何期望，Bernoulli 端点按通常有限测度及 KL 约定处理。合法相邻位为一会在实际完整外部场上强制 $X_0=0$；截断字段只有在保留了对应邻位时才能沿用这一强制结论。特别地，$r=0$ 不允许从缺失一侧的邻位替截断后验作决定。

全部有限柱集用 $\lambda M_w\mathbf1$，不是迹或闭环权重；零半径、原始开路径端点及区间接缝仍由原始实际边联合律承担。没有对内部路径重新拼接，也没有在原始二进制约束之外引入块律。

定理 3.1 的量词是每条固定产生器存在自己的 $L,\kappa$；定理 6.5 是对每个固定 $\theta$ 的结论。闭支撑面分离未提供整个 $\Theta_N$ 上的统一正量，跨参数变化还可能改变相容支撑对集合。紧参数域不能代替这项缺失的统一估计。本卷不主张统一 $N$ 率、参数族统一半径、高效常数取得、隐呈现最小性、有限预测态表示或经验学习收益。

## 8. 多字响应接口及未解变分目标

沿用 [MW, Theorem 3.1] 的记号：$C=[1,L_C]$，$f_C$ 是有界条件零方向，

$$
\mathbb E_{P_\theta}[f_C\mid\sigma(X_j:j\notin C)]=0,
\qquad
F=\max|f_C|,
\qquad
I_R=[1-R,L_C+R].
$$

$U_{R,r}$ 是该定理定义的有限响应。在该定理的同律有限取得与有限边缘信息假设下，其尾证书形式为

$$
|U_{R,r}|
\leq F\eta_\theta(R)
+2(L_C+2R)F\sqrt{\frac{c_\star}{r+1}}.
$$

定理 6.5 为这一既有接口提供实际 $\tau_{P_\theta}(R)\leq\eta_\theta(R)<\infty$ 且 $\eta_\theta(R)\to0$ 的确定性尾界；供给该尾界本身不要求取得。应用响应定理时，产生器、条件零方向、边缘信息及开路径接缝必须全部属于同一实际律。

尾界不构造非零完整响应，不决定响应符号，也不给出覆盖任意假设取得者的生产性方向。原有限负荷变分问题的既定记号 $c_\star,C_N,U_{N,r},\kappa_m$ 下，仍须决定精确有限取得者是否存在，或在每个有限 $N$ 的整个 $\Theta_N$ 上证明 $C_N<c_\star$；其既有严格分离判据为

$$
\forall N\geq1\ \exists r,m\geq1:
\quad U_{N,r}<\frac{\kappa_m}{m+1}.
$$

本卷没有证明任一变分分支。逐律尾预算不等于统一优化误差，不把上比较反向使用，也不把某条充分证书的失效解释成实际尾或可见熵矩的发散。新的指数结论支付的是固定有限律的终端信息与实际尾供给；生产性、严格全域最大值及有限取得仍是独立数学义务。

## 9. 支撑文献与引用边界

[CK] Taolue Chen、Stefan Kiefer，*On the Total Variation Distance of Labelled Markov Chains*，[arXiv:1405.2852v1](https://arxiv.org/html/1405.2852v1)。Section 2 给出有限标记边模型、全部柱集等价及 Proposition 3；Section 4 定义公共等价子分布并证明传播与上下证书，Theorem 7 给出极限一致；Appendix A 给出有限线性检验论证。有理项约束服务其复杂度结论。本卷对实项与不等成本质量的结论由相应直接证明承担，不将其极限定理当作指数率。

[KS] Stefan Kiefer、A. Prasad Sistla，*Distinguishing Hidden Markov Chains*，[arXiv:1507.02314v2](https://arxiv.org/html/1507.02314v2)。Section 4.1 的 profile、Section 5 的有限检验与支撑限制说明正分离的结构；其可辨识假设下的指数监测结论见 Theorem 4.7。该监测定理未用于这里可能重叠的初始状态律。本卷从最大剥离后的不相容闭面直接证明亲和递推。

[RW] Mark D. Reid、Robert C. Williamson，*Information, Divergence and Risk for Binary Experiments*，[arXiv:0901.0356v1](https://arxiv.org/html/0901.0356v1)。Section 2.3 的 Corollary 3 与 Section 5.2 的 Theorem 14 给出积分核与成本帐篷。本卷显式证明单坐标权重 $dt/t$ 的端点恒等式，不给该文归属任何有限标记产生器的率定理。

[EWM] [实际擦除影响的加权熵矩接口](FIB_LEGAL_EDGE_LOAD_ENTROPY_ERASURE_INFLUENCE_WEIGHTED_MOMENT.md)。所复用结论是同一实际双侧平稳二进制律上的 $e_L(r),e_R(r)\leq R_r/2$ 及其加权尾求和。条件信息、Bernoulli KL 与投影极限是其支撑；本卷新增的是通过指数终端信息为每条原始有限呈现支付该熵矩。

[MW] [多字响应稳定性与消失尾证书](FIB_LEGAL_EDGE_LOAD_MULTIWORD_RESPONSE_STABILITY_AND_VANISHING_TAIL_CERTIFICATE.md)，Theorem 3.1。仅作为同律确定性实际尾的消费者；它的条件零性、取得条件、有限边缘信息与生产性响应义务没有由尾率代替。

## 追加锚（本行以下为增补区）
