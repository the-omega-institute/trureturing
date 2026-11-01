# 情境时空算术的量子扩展：读出闭合与共同酉实现

[总目](../CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) · [前卷](330_350_SMALL_BUDGET_AND_CORRECTIONS.md)


<a id="entry-1055"></a>

## 追加锚（本行以下为增补区）

<a id="section-351"></a>

## 351. 近似闭合读数空间的条件扩张与有界提取限制

第350节修正一个已经给定的相容代数，并保持其维数。本节处理两种能够增加维数的条件：在与已有代数对易的重数空间中分裂一个投影，或者在两个中心角之间加入相容的非对角连接。两种构造都直接控制新增代数的完整复单位球。最后给出一个精确矩阵例子，说明从一个指定残余生成整个代数，仍不保证固定预算的多项式能取得扩张所需的平均读数。

**定义 351.1（近包含、平均与误差参数）。** 设 $d\ge1$，$V\subseteq\operatorname{Herm}_d$ 是包含 $I$ 的实线性子空间，$W=V+iV$，并令

$$
\mu=\sup_{u,v\in W_1}\operatorname{dist}(uv,W),
\qquad
\nu(B,W)=\sup_{b\in B_1}\operatorname{dist}(b,W).
$$

所有范数均为普通算子范数，$B_1$ 表示完整复单位球；距离的目标是整个线性空间 $W$。沿用第350节的自伴乘法缺陷时，$\mu\le4\eta$。设 $A\subseteq M_d(\mathbb C)$ 是含单位的精确 $C^*$-子代数，$\nu(A,W)\le\alpha$，记

$$
\gamma=\alpha(2+\alpha)
+\mu(2+\mu)(1+\alpha)^2.
\tag{351.1}
$$

因此 $\alpha,\mu\le\gamma/2$。$E_A,E_{A'}$ 分别表示到 $A$ 及其交换子代数 $A'$ 的保迹条件期望。它们是范数一映射，可分别写成 $U(A')$ 与 $U(A)$ 上的酉共轭平均，因而彼此交换。

**定理 351.2（可见重数残余给出严格扩张）。** 在定义351.1下，假设 $\gamma\le1/400000$，并存在 $a\in V_1$ 满足

$$
E_A(a)=0,
\qquad \|E_{A'}(a)\|\ge\frac12.
\tag{351.2}
$$

则存在含单位的环境代数 $B\supsetneq A$，使

$$
\nu(B,W)\le200\gamma.
\tag{351.3}
$$

具体地，若所分裂的表示块为 $M_n\otimes I_m$，则 $\dim_{\mathbb C}B=\dim_{\mathbb C}A+n^2$。常数不依赖环境维数、块尺寸或表示重数。

证明。对 $A$ 的任意最小中心投影 $r$，定义

$$
T_r(x)=rE_{A'}(x)r
=\int_{U(A)}(ru)x(ru)^*\,du.
$$

它是到 $rA'r$ 的收缩投影。对 $x\in W_1$，每个 $ru\in A_1$ 可由某个 $v\in W$ 以误差 $\alpha$ 近似，且 $\|v\|\le1+\alpha$。先替换两侧因子，再两次近似乘积，得到

$$
\operatorname{dist}((ru)x(ru)^*,W)
\le\alpha(2+\alpha)+\mu(2+\mu)(1+\alpha)^2=\gamma.
$$

在商空间 $M_d/W$ 中对原来的连续共轭映射积分，遂有

$$
\operatorname{dist}(T_r(x),W)\le\gamma\|x\|
\qquad(x\in W).
\tag{351.4}
$$

这一步不要求最近点选择具有可测性。

令 $c=E_{A'}(a)$。由两期望交换，$E_A(c)=0$。在表示

$$
A=\bigoplus_j(M_{n_j}\otimes I_{m_j}),
\qquad
c=\bigoplus_j(I_{n_j}\otimes c_j)
$$

中，每个 $c_j$ 自伴且归一化迹为零。由式(351.2)，可选一个块使 $\|c_j\|\ge1/2$；令 $r$ 为该块的中心投影，$c_r=T_r(a)$。若 $m,M$ 是 $c_r$ 在 $r\mathcal H$ 上的极端特征值，则

$$
m\le0\le M,
\qquad \Delta=M-m\ge\frac12.
$$

该块非零且无迹，两个端点不同。矩阵

$$
x_0=\frac{c_r-mr}{\Delta}
$$

属于 $rA'r$，在该角中具有精确谱端点 $0,1$，并满足 $\operatorname{dist}(x_0,W)\le2\gamma+\alpha\le4\gamma$。

设一般的 $x\in rA'r$ 自伴，$0\le x\le r$，谱端点为 $0,1$，且到 $W$ 的距离不超过 $\epsilon=4\gamma$。取 $v\in V$ 以误差 $\epsilon$ 近似 $x$，再取 $t\in V$ 以误差 $\mu\|v\|^2$ 近似 $v^2$。取厄米部分保证这两次选择合法。于是

$$
\|t-x^2\|\le h,
\qquad
h=\epsilon(2+\epsilon)+\mu(1+\epsilon)^2\le9\gamma.
$$

令 $y=T_r(t)$。由于 $T_r$ 固定 $x^2$，式(351.4)给出

$$
\|y-x^2\|\le h,
\qquad
\operatorname{dist}(y,W)\le\gamma(1+h).
$$

若 $m_y,M_y$ 是 $y$ 在该角中的极端特征值，则 $|m_y|\le h$、$|M_y-1|\le h$。重新归一化

$$
x_+=\frac{y-m_yr}{M_y-m_y}
$$

恢复精确端点，且

$$
\begin{aligned}
\operatorname{dist}(x_+,W)
&\le\frac{\gamma(1+h)+\alpha h}{1-2h}
\le2\gamma,\\
\|x_+-x^2\|
&\le\frac{4h}{1-2h}\le45\gamma.
\end{aligned}
\tag{351.5}
$$

所以这一步可以反复执行，而距离界不会逐轮累加。令 $\kappa=45\gamma$，以 $\theta_{i,k}$ 表示第 $k$ 步按大小排序的特征值。Weyl 不等式给出

$$
\theta_{i,k+1}\le\theta_{i,k}^2+\kappa,
\qquad 0\le\theta_{i,k}\le1.
$$

当 $\gamma>0$ 时，区间 $[0,2\kappa]$ 在这个上界递推下不变；在 $[2\kappa,1-2\kappa]$ 中，每步至少下降 $\kappa/2$。每个有序指标若曾进入 $[0,1-2\kappa]$，就在有限步后进入低端区间并留在那里；否则始终位于高端。指标只有有限个，故存在同一个有限步 $N$，使全部特征值位于

$$
[0,2\kappa]\cup[1-2\kappa,1].
$$

迭代步数可以依赖维数和谱，本结论只要求误差界与维数无关。两个精确端点始终保留，因此 $q=1_{[1/2,1]}(x_N)$ 是 $r$ 的非零真子投影，属于 $A'$，并满足

$$
\operatorname{dist}(q,W)\le90\gamma+4\gamma=94\gamma.
\tag{351.6}
$$

若 $\gamma=0$，则 $A\subseteq W$ 且 $W$ 已为精确有限维 $C^*$-代数。对非零无迹块 $c_r$ 作角内谱分解，直接得到这样的 $q\in W$，距离为零。

置 $B=C^*(A,q)$。在所选块中，$q=I_n\otimes p$ 将重数空间分成两个非零部分，故 $M_n\otimes I_m$ 扩大成两个独立的 $M_n$ 系数块，维数增加 $n^2$。对任意 $b\in B_1$，将其中一个系数复制到另一重数部分，并保留所有未改变的块，可写成

$$
b=a_0+dq,
\qquad a_0\in A_1,\quad d\in A,\quad\|d\|\le2.
$$

以误差 $\alpha,2\alpha,\epsilon_q=94\gamma$ 分别近似 $a_0,d,q$，再近似一次乘积，得到

$$
\begin{aligned}
\operatorname{dist}(b,W)
&\le3\alpha+2(1+\alpha)\epsilon_q
+2\mu(1+\alpha)(1+\epsilon_q)\\
&\le\gamma(190.5+188.5\gamma+47\gamma^2)
\le200\gamma.
\end{aligned}
$$

这控制的是全部复收缩，没有按块数求和。证毕。

**引理 351.3（有谱间隙的符号函数仍接近读数空间）。** 设 $s=s^*$、$\|s\|\le1$，并有参数 $0<\tau\le1$ 满足

$$
\min|\operatorname{spec}(s)|\ge\tau,
\qquad \operatorname{dist}(s,W)\le\epsilon,
\qquad
\epsilon\le\frac\tau2,\quad
\mu\le\frac{\tau^2}{128}.
$$

则

$$
\operatorname{dist}(\operatorname{sign}(s),W)
\le\frac{2\epsilon}{\tau}+\frac{192\mu}{\tau^3}.
\tag{351.7}
$$

证明。取 $v\in V$ 满足 $\|v-s\|\le\epsilon$，并置 $w=v/2$。由 $0<\tau\le1$，有 $\|w\|\le3/4$，且最小奇异值至少为 $\tau/4$。令 $\delta=\tau^2/16$、$z=I-w^2$，则 $0\le z\le(1-\delta)I$。取自伴 $y\in W$ 使 $\|y-z\|\le\mu$，记 $q=\|y\|$。假设保证

$$
(1+\mu)q\le1-\delta+2\mu+\mu^2
\le1-\frac\delta2=:r<1.
$$

沿第350节的幂级数构造，令 $F(t)=(1-t)^{-1/2}=\sum c_kt^k$，其中 $c_k\ge0$。从 $t_0=w$ 出发，在 $W$ 中选择

$$
\|t_{k+1}-t_ky\|\le\mu\|t_k\|q.
$$

归纳给出 $\|t_k\|\le\|w\|((1+\mu)q)^k$ 及

$$
\|t_k-wy^k\|\le\|w\|q^k((1+\mu)^k-1).
$$

因此 $b=\sum c_kt_k\in W$ 收敛，且

$$
\|b-wF(y)\|\le\|w\|F'(r)\mu q.
$$

对 $z^k-y^k$ 使用保持因子次序的伸缩求和，不要求 $z,y$ 对易，得到 $\|F(z)-F(y)\|\le F'(r)\mu$。由 $wF(z)=\operatorname{sign}(v)$，

$$
\operatorname{dist}(\operatorname{sign}(v),W)
\le2\mu F'(r)
=\frac{128\sqrt2\,\mu}{\tau^3}
\le\frac{192\mu}{\tau^3}.
$$

最后，对可逆自伴矩阵使用对称积分

$$
\operatorname{sign}(X)
=\lim_{R\to\infty}\frac1\pi
\int_{-R}^{R}(X-itI)^{-1}\,dt.
$$

$s,v$ 的谱均避开 $(-\tau/2,\tau/2)$；预解式恒等式将两积分之差的被积函数范数界定为 $\epsilon/((\tau/2)^2+t^2)$。积分后得到 $\|\operatorname{sign}(v)-\operatorname{sign}(s)\|\le2\epsilon/\tau$，从而证明式(351.7)。上述估计也包含 $\epsilon=0$ 或 $\mu=0$ 的情形。证毕。

**定理 351.4（有谱间隙的相容连接给出严格扩张）。** 在定义351.1下，假设 $\gamma\le10^{-8}$。设 $P,Q\in Z(A)$ 是非零互补中心投影，且某个 $a\in V_1$ 的角块 $h=PaQ:Q\mathcal H\to P\mathcal H$ 为双射，全部奇异值至少为 $1/4$。令 $x$ 为 $h$ 的极分解部分，并额外要求

$$
x(QAQ)x^*=PAP.
\tag{351.8}
$$

则 $B=C^*(A,x)\supsetneq A$，并且

$$
\dim_{\mathbb C}B=\dim_{\mathbb C}A+2\dim_{\mathbb C}(QAQ),
\qquad
\nu(B,W)\le12500\gamma\le\frac1{8000}.
\tag{351.9}
$$

奇异值不必彼此接近；双射、谱间隙及式(351.8)都是本定理的明确前提。

证明。与式(351.4)的两侧因子近似相同，对全部 $u\in W$ 有

$$
\operatorname{dist}(PuQ,W)\le\gamma\|u\|.
\tag{351.10}
$$

故 $\operatorname{dist}(h,W)\le\gamma$。令 $s=h+h^*$，则 $\|s\|\le1$、$\min|\operatorname{spec}(s)|\ge1/4$，并且 $\operatorname{dist}(s,W)\le2\gamma$。引理351.3给出

$$
\operatorname{dist}(\operatorname{sign}(s),W)
\le16\gamma+12288\mu\le6160\gamma=:e.
$$

由于 $\operatorname{sign}(s)=x+x^*$，再对一个范数不超过 $1+e$ 的 $W$ 近邻使用式(351.10)，得到

$$
\operatorname{dist}(x,W)
\le e+\gamma(1+e)\le6200\gamma=:e_x.
$$

令 $C=QAQ$。从 $Q\mathcal H\oplus Q\mathcal H$ 到 $\mathcal H$ 的映射 $(\xi,\zeta)\mapsto x\xi+\zeta$ 为酉映射。它将 $M_2(C)$ 识别为

$$
B=\{xc_{11}x^*+xc_{12}+c_{21}x^*+c_{22}:c_{ij}\in C\}.
$$

两个对角角块恰为 $A=PAP\oplus QAQ$，两个非对角角块各增加 $\dim C$ 个复维数。若 $b\in B_1$，四个角系数都是收缩。两个对角项各到 $W$ 的距离不超过 $\alpha$；对 $c\in C_1$，近似 $x,c$ 并使用乘法缺陷，得到

$$
\operatorname{dist}(xc,W)
\le e_x+(1+e_x)\alpha
+\mu(1+e_x)(1+\alpha).
$$

取伴随给出另一非对角项的相同界。因此

$$
\begin{aligned}
\nu(B,W)
&\le2e_x+(4+2e_x)\alpha
+2\mu(1+e_x)(1+\alpha)\\
&\le12403\gamma+12400.5\gamma^2+3100\gamma^3
\le12500\gamma.
\end{aligned}
$$

弱不等式包含 $\gamma=0$，并控制全部复单位球。证毕。

<a id="entry-1057"></a>

### 351.5 两个扩张条件仍不能覆盖全部残余

若 $a\in V_1$ 自伴且 $\|a\|=1$，记其中心压缩为 $D_Z(a)=\sum_jz_jaz_j$。当 $\|D_Z(a)\|\le1/2$ 时，中心符号酉 $s=\sum_j\varepsilon_jz_j$ 的平均给出某个 $s$ 满足 $\|a-sas\|\ge1/2$。取 $P=(I+s)/2,Q=(I-s)/2$，由 $a-sas=2(PaQ+QaP)$ 得到 $\|PaQ\|\ge1/4$。这提供一个整体角块，避免逐条矩阵元的维数损失，但范数下界只控制最大奇异值。

例如取 $W=M_4$、$A=\mathbb CP\oplus\mathbb CQ$，其中 $P,Q$ 均秩二。令 $h=PhQ$ 的奇异值为 $1,0$，$a=h+h^*$。此时 $\eta=\alpha=0$，$E_A(a)=E_{A'}(a)=0$，而 $\|h\|=1$。它不是满支撑连接；对任意满支撑部分等距 $x:Q\mathcal H\to P\mathcal H$ 及实数 $t\ge0$，

$$
\|h-tx\|\ge\max\{|1-t|,t\}\ge\frac12.
$$

这只限制该指定角块的近似方式，没有证明支撑分裂是所有扩张方法的必要步骤。

小交换子代数平均也不保证小中心压缩。取 $W=M_4$、$A=M_2\otimes I_2$，以及无迹自伴酉 $s,r$，令 $a=s\otimes r$。则 $E_A(a)=E_{A'}(a)=0$，但 $Z(A)=\mathbb CI$，故 $D_Z(a)=a$。这个残余位于一个因子内部，没有可用的非平凡中心分割。上述两个例子中的 $A$ 都不是最大近包含代数；它们不排除实质利用最大性的构造。

**命题 351.5（一个生成残余的有界多项式平均仍可趋零）。** 对 $n\ge2$，令 $\mathcal H=\mathbb C^n\otimes\mathbb C^n$、$V=\operatorname{Herm}(\mathcal H)$、$W=M_{n^2}$、$A=M_n\otimes I_n$，并置

$$
\Omega=\frac1{\sqrt n}\sum_i e_i\otimes e_i,
\quad p=|\Omega\rangle\langle\Omega|,
\quad t=n^{-2},
\quad a=\frac{p-tI}{1-t},
\quad q_n=\frac{1+t}{1-t}.
$$

记 $\tau_m=\operatorname{Tr}/m$ 为归一化迹。则 $\eta=\nu(A,W)=0$，$\|a\|=1$，$E_A(a)=E_{A'}(a)=0$，$\operatorname{dist}(a,A)\ge1/2$，而 $C^*(A,a)=W$。定义

$$
R=E_{A'}(\operatorname{Id}-E_A)
=E_{A'}-\tau_{n^2}(\,\cdot\,)I.
$$

对所有有限和

$$
z=\sum_j\lambda_j u_{j,0}a u_{j,1}\cdots a u_{j,k_j},
\qquad
u_{j,l}\in A_1,\quad k_j\le K,\quad
\sum_j|\lambda_j|\le L,
$$

都有

$$
\|R(z)\|\le\frac{2L}{n^2}q_n^K.
\tag{351.11}
$$

若 $y=(\operatorname{Id}-E_A)z$ 还满足 $\|y\|\ge c>0$，则

$$
\left\|E_{A'}\!\left(\frac{y}{\|y\|}\right)\right\|
\le\frac{2L}{cn^2}q_n^K.
\tag{351.12}
$$

因此，对不随 $n$ 改变的 $K,L,c$，这类构造无法统一保证定理351.2所需的 $1/2$ 门槛。

证明。$p$ 的两个归一化偏迹均为 $I/n^2$；$a$ 的特征值为 $1$ 及 $-1/(n^2-1)$，从而得到所列范数与平均恒等式。对任意 $b\in A$，条件期望的收缩性给出 $\|b\|=\|E_A(b-a)\|\le\|b-a\|$，故 $1=\|a\|\le\|a-b\|+\|b\|\le2\|a-b\|$，证明所列距离下界。对任意收缩 $b,c\in M_n$，矩阵单位展开给出

$$
\begin{aligned}
p(b\otimes I)p&=\tau_n(b)p,\\
E_{A'}((b\otimes I)p(c\otimes I))
&=\frac1{n^2}I\otimes(cb)^{\mathsf T},\\
\|R((b\otimes I)p(c\otimes I))\|
&=\frac1{n^2}\|(cb)^{\mathsf T}-\tau_n(cb)I\|
\le\frac2{n^2}.
\end{aligned}
$$

含至少一个 $p$ 的乘积因此缩成模长不超过一的标量乘以 $(b\otimes I)p(c\otimes I)$；不含 $p$ 的乘积属于 $A$，被 $R$ 消去。将一个含 $k$ 次 $a$ 的词按 $a=(p-tI)/(1-t)$ 展开，其绝对系数总和不超过

$$
(1-t)^{-k}\sum_{l=0}^k\binom kl t^{k-l}=q_n^k.
$$

三角不等式证明式(351.11)，归一化即得式(351.12)。这些估计也适用于保持相同次数及总变差预算的范数极限和平均。

另一方面，$p=(1-t)a+tI$，且

$$
(E_{ij}\otimes I)p(E_{kl}\otimes I)
=\frac1n|i,j\rangle\langle l,k|.
$$

这些元素张成全部矩阵单位，故 $C^*(A,a)=M_{n^2}$。恢复归一化矩阵单位时出现的系数 $n$，说明精确生成与固定系数预算没有矛盾。证毕。

<a id="entry-1058"></a>

### 351.6 最大性路线的当前边界与来源

对 $\delta_*=1/2000$，在所有满足 $\nu(A,W)\le\delta_*$ 的环境代数中选择最大维数者是合法的：$\mathbb CI$ 给出非空候选；第350节的条件期望残差级数在使用同维唯一性之前，已经证明 $E_A|_W$ 满射，故每个候选都满足 $\dim A\le\dim W$。可能维数是有限非空集合。

当 $\eta$ 足够小时，定理350.2可将这个最大候选共轭到 $\nu(A,W)\le4240\eta$。若还未同维，就存在 $V\cap\ker E_A$ 中的自伴范数一残余。定理351.2与351.4分别排除这个最大候选上满足其额外前提的两种配置，因为它们都会构造更大、仍处于粗近包含门槛内的代数。但这里尚未证明所有残余必落入这两类，也未证明 $E_A|_W$ 单射。

命题351.5的例子已经满足零乘法缺陷及精确近包含。它排除的仅是从一个预先指定残余出发、保持所列次数与系数预算的平均提取路线；其中 $A$ 并不最大。选择其他残余、实质利用最大性，或者证明另一种允许放大误差的控制机制，仍在该命题之外。这里的次数与系数预算只定义所列矩阵表达式的范围，不直接等同于一般量子算法或物理控制的成本。

最大维数、投影分裂与矩阵角合并的策略可与 Kitaev，*Almost-idempotent quantum channels and approximate $C^*$-algebras*，[arXiv:2405.02434v2，第8、9节](https://arxiv.org/abs/2405.02434v2)比较。该文的标量主定理以内部双线性乘法及相应近似代数公理为前提；矩阵层范数属于后续扩张版本。本节使用环境乘积距离、精确条件期望及实际矩阵的谱函数，逐项给出所需估计，没有将缺少的内部乘法或压缩空间同构作为已知输入。引理351.3复用第350节的幂级数方法，并显式跟踪谱间隙对误差的影响。

这些是所声明条件下的解析构造与路线限制，不承担一般非交换稳定性、复量子规则重建或时空构造的结论，也不据此提出文献原创性声明。

<a id="entry-1059"></a>

## 追加锚（本行以下为增补区）

<a id="section-352"></a>

## 352. 三维预测接口与无界精确量子记忆

第73、77节的预测维数衡量线性响应需要多少个方向，第79、345节另要求物理编码和合法续接。本节给出一个固定初态、固定两种命令的过程族：其全部预测始终只需三个实线性坐标，精确实现所需的量子记忆维数却趋于无穷。与此同时，一个 qubit 的终端读出误差可以趋于零。下界使用已有的半正定秩理论；这里将它接到同一个可执行续接接口，并区分精确容量、近似容量与允许读出的次数。

<a id="entry-1061"></a>

### 352.1 固定操作、初态与容量合同

**定义 352.1（多边形循环读出）。** 固定整数 $n\ge3$，记

$$
\theta_n=\frac{2\pi}{n},\qquad
c_n=\cos\frac\pi n,\qquad
p_k^{(n)}=
\frac{c_n-\cos(k\theta_n-\pi/n)}{1+c_n}
\quad(k\ge0).
\tag{352.1}
$$

装置从一份固定初态开始，接受两种命令：$a$ 推进一步而不输出，$b$ 读取一个比特，并在两种结果后都重置到初态。从初态或重置态执行 $a^kb$ 时，输出 $1$ 的概率规定为 $p_k^{(n)}$。各次读出后重置，因而这也指定了全部有限命令树的联合输出律，允许测试者根据已得结果选择后续命令。

$n$ 是已知的设计参数；每个 $n$ 可以选用自己的固定初态、门与读出。这里计量持续记忆的 Hilbert 维数，不计这些固定实参数的描述长度或实现精度成本。

竞争实现必须使用固定的、与步数和未输入历史无关的操作：$a$ 是一条 CPTP 映射，$b$ 是一份二结果量子仪器。所有跨命令保留的内部寄存器都计入记忆，包括经典控制态和计数器。允许每步使用随后丢弃的新鲜辅助系统；不提供免费的持久环境、外部钟、预共享持久随机标签或额外历史输入。测试者可以保存自己的输出历史并据此选择 $a$ 或 $b$，但装置只接收当前命令。比较对象是这些实验的经典输出记录，未要求保留额外的终端量子输出或参考系统接口。

记 $d_n$ 为在此合同下精确实现全部有限实验的最小持续 Hilbert 维数。直和中的经典标签同样占据这个总维数。竞争者不必在物理上使用与目标相同的重置方式；只要全部可访问记录相同即可。

式（352.1）确实给合法概率。它以 $n$ 为周期，在这些离散角上余弦的最大值是 $c_n$，最小值不小于 $-1$，故

$$
0\le p_k^{(n)}\le1,\qquad
p_0^{(n)}=p_1^{(n)}=0.
\tag{352.2}
$$

<a id="entry-1062"></a>

### 352.2 预测维数固定，精确量子容量无界

**定理 352.2（三维预测的量子实现分离）。** 对定义352.1的每个 $n\ge3$，全部未归一化分支概率具有最小实线性维数恰为 $3$ 的表示。精确量子实现存在，并满足

$$
\frac12\operatorname{rank}_{\mathrm{psd}}^{\mathbb R}(S_n)
\le d_n\le n,
\qquad
\lim_{n\to\infty}d_n=\infty,
\tag{352.3}
$$

其中 $S_n$ 是正 $n$ 边形的松弛矩阵，$\operatorname{rank}_{\mathrm{psd}}^{\mathbb R}$ 使用实对称正半定因子。因此不存在一个只由线性预测维数决定、覆盖这整个过程族的有限精确量子记忆上界。

证明。先给实际实现。取 $\{|j\rangle:0\le j<n\}$，令循环酉矩阵 $V_n$ 把 $|j\rangle$ 送到 $|j+1\bmod n\rangle$。初态取 $|0\rangle\langle0|$，推进使用 $\rho\mapsto V_n\rho V_n^\dagger$。令

$$
D_1=\sum_{j=0}^{n-1}p_j^{(n)}|j\rangle\langle j|,
\qquad D_0=I-D_1,
\qquad
\mathcal J_r(\rho)=\operatorname{tr}(D_r\rho)
|0\rangle\langle0|.
\tag{352.4}
$$

式（352.2）使 $D_0,D_1$ 成为 POVM；两条测量后制备映射完全正，且其和保迹。这给出对所有输入矩阵合法、在指定初态上实现目标的 $n$ 维装置，故 $d_n\le n$。

线性预测使用 $v=(t,x,y)\in\mathbb R^3$，初始向量为 $v_0=(1,1,0)$。推进固定 $t$，并把 $(x,y)$ 旋转 $\theta_n$。读出泛函及分支更新为

$$
\begin{aligned}
\ell_1(t,x,y)
&=\frac{c_nt-\cos(\pi/n)x-\sin(\pi/n)y}{1+c_n},\\
\ell_0(t,x,y)&=t-\ell_1(t,x,y),\\
B_rv&=\ell_r(v)v_0.
\end{aligned}
\tag{352.5}
$$

允许的未归一化向量落在

$$
C_n=\operatorname{cone}\{
(1,\cos(j\theta_n),\sin(j\theta_n)):0\le j<n
\}.
\tag{352.6}
$$

推进置换这些生成射线；两项 $\ell_r$ 在 $C_n$ 上非负，且和为 $t$。所以式（352.5）保持这个锥，并正确给出零质量分支以及任意有限分支的概率。测试者的自适应选择只决定接下来复合哪一个固定线性映射，不增加装置的预测坐标。

这三个坐标也是必要的。取实际历史 $a^i$ 和后续事件 $a^jb_1$，其中 $b_1$ 表示读取结果为 $1$，得到有限 Hankel 块

$$
H_n=\bigl(p_{i+j}^{(n)}\bigr)_{0\le i,j<n}.
\tag{352.7}
$$

式（352.1）展开后恰有 $1,e^{i\theta_n},e^{-i\theta_n}$ 三个不同且系数非零的 Fourier 频率。长度 $n$ 的对应字符线性独立，故 $H_n$ 的复秩及实秩均为 $3$。任意 $r$ 维实线性表示都把这个历史—未来矩阵分解经过 $\mathbb R^r$，于是 $r\ge3$。这证明最小值恰为 $3$；其中 $t$ 是质量坐标，归一化截面上的自由坐标只有两个。

再看任意 $d$ 维量子实现。令其固定初态为 $\rho$、推进通道为 $\Phi$，读出 $1$ 的效应为 $F$。由于历史 $a^i$ 与未来 $a^jb_1$ 使用同一装置，必须有

$$
p_{i+j}^{(n)}
=\operatorname{tr}(\rho_iF_j),
\qquad
\rho_i=\Phi^i(\rho),\qquad
F_j=(\Phi^*)^j(F).
\tag{352.8}
$$

$\rho_i,F_j$ 都是 $d$ 阶复 Hermitian 正半定矩阵。这一步只使用首次读出，所以即使竞争者读出后采用另一种内部状态更新，该必要条件仍成立。

把式（352.7）的列按 $j\mapsto-j\bmod n$ 重排，再乘正数 $1+c_n$，得到

$$
(S_n)_{ij}
=c_n-\cos((i-j)\theta_n-\pi/n).
\tag{352.9}
$$

它正是顶点 $v_i=(\cos(i\theta_n),\sin(i\theta_n))$、面法向量
$u_j=(\cos(j\theta_n+\pi/n),\sin(j\theta_n+\pi/n))$
对应的松弛矩阵：正 $n$ 边形的全部面不等式为 $u_j\cdot v\le c_n$。正比例缩放和列置换不改变半正定秩，所以式（352.8）给出

$$
\operatorname{rank}_{\mathrm{psd}}^{\mathbb C}(S_n)\le d.
\tag{352.10}
$$

这里不能把复因子直接当成实因子。对复矩阵 $A$ 定义

$$
\mathfrak R(A)=
\begin{pmatrix}
\operatorname{Re}A&-\operatorname{Im}A\\
\operatorname{Im}A&\operatorname{Re}A
\end{pmatrix}.
\tag{352.11}
$$

若 $A$ Hermitian 正半定，则 $\mathfrak R(A)$ 实对称正半定；并且对两个 Hermitian 因子，

$$
\operatorname{tr}(\mathfrak R(A)\mathfrak R(B))
=2\operatorname{tr}(AB).
\tag{352.12}
$$

对式（352.8）的两族因子作此变换，再把其中一族乘 $1/2$，就得到尺寸 $2d$ 的实半正定分解。因此

$$
\operatorname{rank}_{\mathrm{psd}}^{\mathbb R}(S_n)\le2d.
\tag{352.13}
$$

最后使用 Fawzi、Gouveia、Parrilo、Robinson、Thomas 的 *Positive Semidefinite Rank*，[arXiv:1407.4095v1，推论5.13、例5.14](https://arxiv.org/html/1407.4095v1#S5.SS2)：固定平面维数时，多边形面的数量趋于无穷，松弛矩阵的实半正定秩必趋于无穷。该结论来自有限尺寸半正定提升的代数边界次数界，并不要求多边形顶点一般位置或代数独立；因此适用于这里的正多边形。结合式（352.13）即得式（352.3）。实、复半正定秩的比较也见该文第2.2节。

半正定分解在本证明中只提供必要下界；任意一份分解不自动给出把全部 $\rho_i$ 按同一循环送到后继的 CPTP 映射。因此这里没有把 $d_n$ 宣称为 $S_n$ 的半正定秩，也没有确定 $d_n$ 的精确增长率。证毕。

<a id="entry-1063"></a>

### 352.3 一个 qubit 的趋零误差及其视界范围

**命题 352.3（同一低维近似的完整记录误差）。** 对每个 $n\ge3$，存在一个定义352.1接口下的 qubit 装置，使任意次数推进后的一次终端读出，其最坏总变差误差恰为

$$
\delta_n=\frac{1-\cos(\pi/n)}2
\sim\frac{\pi^2}{4n^2}.
\tag{352.14}
$$

对这个指定装置，允许任意有限自适应命令树、每条分支至多 $H$ 次读出时，完整经典记录的最坏总变差误差恰为

$$
1-(1-\delta_n)^H.
\tag{352.15}
$$

证明。用 Pauli 矩阵 $X,Y,Z$，取

$$
\rho_0=\frac{I+X}{2},\qquad
U_n=e^{-i\theta_nZ/2},\qquad
N_n=\cos(\pi/n)X+\sin(\pi/n)Y,
\qquad F_q=\frac{I-N_n}{2}.
\tag{352.16}
$$

推进为 $U_n$ 共轭，读取效应为 $F_q,I-F_q$，任一结果后都制备 $\rho_0$。这些是合法的量子操作，产生

$$
q_k^{(n)}=\frac{1-\cos(k\theta_n-\pi/n)}2.
\tag{352.17}
$$

对离散可达角逐项相减，得到

$$
0\le q_k^{(n)}-p_k^{(n)}
=\frac{(1-c_n)(1+\cos(k\theta_n-\pi/n))}{2(1+c_n)}
\le\frac{1-c_n}{2}=\delta_n.
\tag{352.18}
$$

$k=0,1$ 时取等，证明式（352.14）。这个界对全部 $k\ge0$ 一致，不随推进次数累积；它以式（352.16）的固定精确门为前提，没有另行估计门实现噪声。

对于一棵允许的命令树，在两份输出历史仍相同的时候，使用相同的测试者随机性和命令，并最大耦合下一次读出的两个 Bernoulli 变量。此前每次读出后两边分别回到各自初态，所以当前条件概率仍是一对式（352.18），不因旧历史变成另一种未知状态。每次读出条件于尚未分歧的历史，保持相同输出的概率至少 $1-\delta_n$。至多 $H$ 次读出后，分歧概率至多式（352.15）；耦合不等式给相同的完整记录总变差上界。允许提前停止时，可用不产生分歧的虚拟末步补齐这个估计。

反向取连续 $H$ 次命令 $b$，中间不推进。目标由 $p_0^{(n)}=0$ 总是输出全零，qubit 装置则每次重置后以概率 $\delta_n$ 输出 $1$，故全零记录的概率为 $(1-\delta_n)^H$。对一个点质量的总变差正好是其余记录的总质量，得到式（352.15）的等号。证毕。

上述两个精确误差值属于式（352.16）的指定实现，未声称它在所有 qubit 装置中最优。它们已经足以区分两种极限：固定 $H$ 时，近似误差随 $n\to\infty$ 趋零；固定 $n$ 时，同一实现的最坏记录误差随 $H\to\infty$ 趋于 $1$。因此一次终端查询的统一近似，不自动成为任意多次读出的统一近似。

<a id="entry-1064"></a>

### 352.4 正性几何承担的额外容量

本例的三维预测表示保存质量与两个旋转坐标。精确物理实现还要求同一批可达态、未来效应及固定推进通道共同合法；正多边形的每条面约束都进入有限历史—未来矩阵的正因子化。矩阵的普通秩只数线性方向，半正定秩则限制这些方向能否同时由低维密度矩阵和正效应实现。这给出了超出预测坐标计数的容量约束。这里的容量包括所有持续保存的经典和量子寄存器；若把经典存储视为免费资源，本定理不提供不可约相干记忆的下界。

[相位边界卷第350节](../RECURSIVE_RELATIONAL_OBSERVATION_PHASE_BOUNDARY.md)的正弦平方过程已有三维线性预测与无界经典状态数的分离，但始终允许一个 qubit 精确实现。本节改变的概率剖面使同一类推进／读出接口出现无界的精确量子容量；证明依靠式（352.9）的整个松弛矩阵，不由经典随机矩阵的周期下界推断量子下界。两处的固定初态量词都不要求竞争者实现一个事先指定的完整制备多面体。

半正定秩与量子实现的关系、低普通秩与高半正定秩的分离均为成熟结果。上述来源第3.2节讨论量子信息解释，第5.2节给多边形下界；本节的用途是把这一工具接回完整的固定操作过程，并同时写出低维近似及其多次读取范围，不作全球原创性或 Lean 核验声明。这里的容量结论是可执行响应族的结果，没有从观察者存在重建量子公理，也不替代第349—351节仍缺少的一般近代数存在性证明。

<a id="entry-1065"></a>

## 追加锚（本行以下为增补区）

<a id="section-353"></a>

## 353. 周期读出的酉正规形与物理归一化障碍

第352节把固定三维线性预测与无界精确量子记忆分开，但半正定分解只给出了容量下界。若要求一份装置用同一个推进操作实现全部响应，还必须处理动态相容性、态的归一化和读出效应的上界。本节先从严格周期的记录中提取一个不增加容量的有限阶酉实现，再给出一个尺寸三的等变半正定分解仍不足以使用三维量子记忆实现的具体例子。

<a id="entry-1067"></a>

### 353.1 固定推进、周期记录与实际重置

**定义 353.1（周期读取合同）。** 固定整数 $n\ge1$、非空有限结果集合 $Y$，以及满足

$$
p_y(k+n)=p_y(k),\qquad
p_y(k)\ge0,\qquad
\sum_{y\in Y}p_y(k)=1
\quad(k\ge0)
\tag{353.1}
$$

的一组概率。装置接受不输出的推进命令 $a$ 和读取命令 $b$；初态或上一次读取后推进 $k$ 次时，读取结果为 $y$ 的概率是 $p_y(k)$。目标在每个结果后重置，因此这也指定了全部有限自适应命令树的经典记录律。

实现使用固定初态、一条与步数无关的 CPTP 推进映射及固定量子仪器。所有持续保存的经典与量子寄存器计入总 Hilbert 维数；不额外输入步数、时钟或历史。竞争者可以在内部使用不同的状态更新，只须匹配全部可访问记录。固定门参数可以依赖已知概率族；参数描述、精度与计算成本不由这里的维数计量。没有额外的终端量子输出或参考系统合同。

**定理 353.2（不增维的有限阶酉正规形）。** 若定义353.1的目标有 $d$ 维精确量子实现，则存在 $D\le d$ 维精确实现，其初态纯、推进为一个满足 $U^n=I_D$ 的固定酉共轭，读取为固定 POVM 后实际重置到该纯初态。在初态的循环子空间上，还可令 $U$ 的特征值互异。因此，允许任意 CPTP 推进的最小持续维数，等于上述有限阶酉推进模型的最小持续维数。

证明。取任意 $d$ 维实现的初态 $\rho$、推进 $\Phi$ 以及首次读出的效应 $F_y$，于是

$$
F_y\ge0,\qquad \sum_yF_y=I,\qquad
\operatorname{tr}\!\left(F_y\Phi^k(\rho)\right)=p_y(k).
\tag{353.2}
$$

先去除对记录不可见的瞬态。令

$$
r_M=\frac1M\sum_{\ell=0}^{M-1}\Phi^{\ell n}(\rho).
\tag{353.3}
$$

密度矩阵集紧，取一条收敛子列，极限记为 $r$。由
$\|\Phi^n(r_M)-r_M\|_1\le2/M$，得到 $\Phi^n(r)=r$。对每个 $k,y$，周期性使式（353.3）每一项在推进 $k$ 次后的读数均为 $p_y(k)$，故极限保持式（353.2）。置 $r_i=\Phi^i(r)$，下标按模 $n$ 解释。

令

$$
\sigma=\frac1n\sum_{i=0}^{n-1}r_i,\qquad
S=\operatorname{supp}\sigma.
\tag{353.4}
$$

$\Phi(\sigma)=\sigma$，且 $\sigma$ 在 $S$ 上严格正。由固定 Kraus 表及 $\Phi(\sigma)$ 在 $S^\perp$ 上为零，每个 Kraus 算子都把 $S$ 送入 $S$，所以 $\Phi$ 限制到 $\mathcal L(S)$ 后仍完全正且保迹。所有 $r_i$ 都支撑于 $S$。以下逆矩阵、迹和单位均在 $S$ 上取。

定义

$$
\begin{aligned}
\Psi(X)&=\sigma^{-1/2}\Phi(\sigma^{1/2}X\sigma^{1/2})\sigma^{-1/2},\\
\tau(X)&=\operatorname{tr}(\sigma X),\\
X_i&=\sigma^{-1/2}r_i\sigma^{-1/2}.
\end{aligned}
\tag{353.5}
$$

$\Psi$ 完全正且保单位，$\tau$ 是忠实状态，$\tau\Psi=\tau$，并有 $\Psi(X_i)=X_{i+1}$、$X_i\ge0$、$\tau(X_i)=1$。不要求 $\Psi$ 对普通迹保迹。

Schwarz 不等式给

$$
Z_i=\Psi(X_i^2)-X_{i+1}^2\ge0,\qquad
\tau(Z_i)=\tau(X_i^2)-\tau(X_{i+1}^2).
\tag{353.6}
$$

沿周期相加为零，每项又非负，因此 $\tau(Z_i)=0$。忠实性给 $Z_i=0$。这正是自伴 $X_i$ 的乘法域等号条件。具体地，写 $\Psi(X)=V^\dagger(X\otimes I)V$、$V^\dagger V=I$；式（353.6）的等号使
$(I-VV^\dagger)(X_i\otimes I)V=0$。与其伴随一起使用，得到对任意 $B$ 的左右乘法恒等式。故 $\Psi$ 在

$$
A=C^*(I,X_0,\ldots,X_{n-1})\subseteq\mathcal L(S)
\tag{353.7}
$$

上是一份保单位 $*$-同态。它循环置换生成元，且 $\Psi^n$ 固定全部生成元，所以 $\alpha=\Psi|_A$ 是满足 $\alpha^n=\operatorname{id}_A$ 的 $*$-自同构。

写有限维代数的表示为

$$
A\simeq\bigoplus_j(M_{r_j}\otimes I_{m_j}),\qquad
\sum_jr_jm_j=\dim S.
\tag{353.8}
$$

每个简单块只保留一份，得到忠实表示
$\pi:A\to\bigoplus_jM_{r_j}\subseteq M_D$，其中 $D=\sum_jr_j\le d$。自同构只置换同阶简单块并作块内酉共轭，因此由某个 $V_0\in U(D)$ 实现。$\alpha^n=\operatorname{id}$ 使 $V_0^n$ 属于 $\pi(A)'=Z(\pi(A))$。取谱分解并逐谱值选根：

$$
V_0^n=\sum_z zP_z,\qquad
C=\sum_z c_zP_z,\qquad |c_z|=1,\qquad c_z^n=z^{-1}.
\tag{353.8a}
$$

$C$ 是 $V_0^n$ 的谱函数，因此属于该中心并与 $V_0$ 对易。于是 $U=CV_0$ 仍实现 $\alpha$，且 $U^n=C^nV_0^n=I_D$。这里使用同一谱值上的一致选根，而非任意选取一个中心内的 $n$ 次根。

还须恢复状态与效应的物理归一化。$\tau$ 在 $\pi(A)$ 上由唯一的块对角正定矩阵 $T$ 表示，满足

$$
\tau(a)=\operatorname{tr}(T\pi(a)),\qquad
T>0,\qquad \operatorname{tr}T=1.
\tag{353.9}
$$

$\tau\alpha=\tau$ 和迹配对的非退化性给 $U^\dagger TU=T$。对每个结果，在 $A$ 上取正泛函

$$
\varphi_y(a)=\operatorname{tr}(F_y\sigma^{1/2}a\sigma^{1/2}).
\tag{353.10}
$$

其和为 $\tau$，故它们在 $\pi(A)$ 中的迹密度 $B_y$ 满足 $B_y\ge0$、$\sum_yB_y=T$。于是

$$
\rho'=T^{1/2}\pi(X_0)T^{1/2},\qquad
E_y=T^{-1/2}B_yT^{-1/2}
\tag{353.11}
$$

分别是密度矩阵和一份 POVM。由于 $T$ 与 $U$ 对易，直接计算得

$$
\operatorname{tr}(E_yU^k\rho'U^{-k})
=\operatorname{tr}(B_y\pi(X_k))
=\varphi_y(X_k)=p_y(k).
\tag{353.12}
$$

最后可将初态取纯，而不再增加维数。在 $U$ 的一组本征基中令

$$
D_0=\operatorname{diag}(\rho'_{jj}),\qquad
C_y=E_y\circ(\rho')^{\mathsf T},\qquad
\psi_j=\sqrt{\rho'_{jj}},
\tag{353.13}
$$

其中 $\circ$ 表示逐项乘积。Schur 乘积定理给 $C_y\ge0$，且 $\sum_yC_y=D_0$。删除 $\rho'_{jj}=0$ 的坐标；正半定性保证其对应行列没有响应贡献。剩余空间中
$\widetilde E_y=D_0^{-1/2}C_yD_0^{-1/2}$ 是 POVM，$\|\psi\|=1$。若 $U$ 的本征值为 $\lambda_j$，则

$$
\begin{aligned}
\operatorname{tr}(E_yU^k\rho'U^{-k})
&=\sum_{i,j}(E_y)_{ij}\rho'_{ji}\overline{\lambda_i^k}\lambda_j^k\\
&=\langle U^k\psi,\widetilde E_yU^k\psi\rangle.
\end{aligned}
\tag{353.14}
$$

再压缩到 $\operatorname{span}\{U^k\psi:k\ge0\}$，其维数不增、该子空间被 $U$ 保持，POVM 压缩仍和为单位；该循环子空间中每个不同本征值只保留一个方向。

每个结果后的新分支取
$\mathcal J_y(\omega)=\operatorname{tr}(\widetilde E_y\omega)|\psi\rangle\langle\psi|$，它们完全正且总和保迹。新装置实际重置，因此式（353.14）逐次给正确的条件概率，覆盖所有有限自适应经典记录。一般 CPTP 类包含这一酉实现类，而上述构造不增加维数，故两个最小值相等。证毕。

上述正规形也给出一个准确的归一化条件。对 $K\subseteq\mathbb Z_n$，置
$\chi_K(k)=(e^{2\pi\mathrm i tk/n})_{t\in K}$。最小持续维数恰为满足以下条件的最小 $|K|$：存在 $w_t>0$ 及 Hermitian 矩阵 $C_y$，使

$$
\sum_{t\in K}w_t=1,\qquad
C_y\ge0,\qquad
\sum_yC_y=\operatorname{diag}(w),\qquad
p_y(k)=\chi_K(k)^\dagger C_y\chi_K(k)\quad(0\le k<n).
\tag{353.14a}
$$

必要性来自纯初态、互异频率的正规形及式（353.13）。反向取
$U=\operatorname{diag}(e^{2\pi\mathrm i t/n})$、$\psi_t=\sqrt{w_t}$，以及
$E_y=\operatorname{diag}(w)^{-1/2}C_y\operatorname{diag}(w)^{-1/2}$，即得到合法 POVM 与所需酉实现。零权坐标可直接删除。对于二结果，式（353.14a）要求同一个对角概率矩阵满足 $0\le C_1\le\operatorname{diag}(w)$；分别为两个结果找到正半定分解，并未自动给出这个共同上界。固定 $K$ 后，这些是线性与半正定约束，但本节没有据此求得一般 $n$ 的最小 $K$。

<a id="entry-1068"></a>

### 353.2 周期性给出的等变容量约束

**推论 353.3（任意 CPTP 推进的对数下界）。** 第352节的最小精确记忆维数满足

$$
d_n\ge\ln(n/2)\qquad(n\ge3),
\tag{353.15}
$$

其中 $\ln$ 是自然对数。这个必要界不要求原实现的推进预先酉、可逆或等变。

证明。由定理353.2，取维数 $D\le d_n$、$U^n=I$ 的实现，初态记为 $\rho$，结果 $1$ 的效应记为 $F$。沿用第352节的 $\theta=2\pi/n$、$c=\cos(\pi/n)$，令

$$
A_i=U^i\rho U^{-i},\qquad
B_j=(1+c)U^jFU^{-j}.
\tag{353.16}
$$

它们给正多边形的松弛分解

$$
\operatorname{tr}(A_iB_j)
=c-\cos((i-j)\theta-\pi/n)=S_{ij}.
\tag{353.17}
$$

这是由同一个 $U$ 同时推进两族因子的旋转等变分解。为明确连接到提升定理，取面法向量
$u_j=(\cos(j\theta+\pi/n),\sin(j\theta+\pi/n))$，定义

$$
\Pi(X)=-\frac2n\sum_j u_j\operatorname{tr}(B_jX),\qquad
L=\{X:\operatorname{tr}(B_jX)=c-u_j\cdot\Pi(X)\ \text{对全部 }j\}.
\tag{353.18}
$$

这里 $X$ 遍历 Hermitian 矩阵。由 $\sum_ju_j=0$ 及 $\sum_ju_ju_j^{\mathsf T}=(n/2)I_2$，每个 $A_i$ 位于 $L$，且 $\Pi(A_i)$ 正好是对应顶点。反向，对 $X\in L$ 且 $X\ge0$，全部多边形面不等式成立。因此 $\Pi(L\cap\mathbf H_D^+)$ 恰为正 $n$ 边形：一边由面不等式给出，另一边由包含全部顶点及凸性给出。$U$ 共轭保持 $L$，并在 $\Pi$ 下成为平面旋转，所以这是尺寸 $D$ 的旋转等变 Hermitian 半正定提升。

Fawzi、Saunderson、Parrilo 的 *Equivariant semidefinite lifts of regular polygons*，[arXiv:1409.4379v1，定理9](https://arxiv.org/html/1409.4379v1#Thmthm9)证明每份此类提升的尺寸至少为 $\ln(n/2)$。故 $d_n\ge D\ge\ln(n/2)$。证毕。

也可在 $U$ 的本征基中把

$$
(1+c)p_k=\|\sqrt{1+c}\,F^{1/2}U^k\rho^{1/2}\|_{\mathrm{HS}}^2
$$

写成共享至多 $D$ 个频率的 Hermitian 平方和，再使用该文第4节的频率稀疏性下界。这里获得的额外约束来自整条周期响应必须由同一个通道续接，没有把任意一份低秩分解宣布为物理实现。

<a id="entry-1069"></a>

### 353.3 三维分解与四维装置的准确分界

**命题 353.4（四周期响应的归一化阈值）。** 对 $0\le s\le1$，取定义353.1中的二结果响应

$$
(p_1(0),p_1(1),p_1(2),p_1(3))=(0,0,s,s),\qquad
p_0(k)=1-p_1(k),\qquad n=4.
\tag{353.19}
$$

令 $d(s)$ 为其最小总持续 Hilbert 维数，则

$$
s_*=\frac8{(2+\sqrt2)^2}=12-8\sqrt2,\qquad
d(s)=\begin{cases}
1,&s=0,\\
3,&0<s\le s_*,\\
4,&s_*<s\le1.
\end{cases}
\tag{353.20}
$$

而对每个 $s>0$，历史—未来矩阵 $(p_1(i-j))_{0\le i,j<4}$ 的实、复半正定秩均为 $3$，并允许尺寸 $3$ 的旋转等变分解。

证明。先证明完整 CPTP 类的下界。由定理353.2，任何 $d\le3$ 维实现都可改为 $U^4=I$、纯初态 $\psi$ 和效果 $F$。两个零概率使 $F$ 同时消去 $\psi,U\psi$。这两向量必须线性独立，否则初态是 $U$ 的本征态，全部响应恒零。因此二维不可能；三维时 $F=\lambda|v\rangle\langle v|$，其中 $0<\lambda\le1$、$\|v\|=1$。

在初态的循环子空间中，$U$ 有至多三个互异的四次单位根本征值。写

$$
g_k=\sqrt\lambda\langle v,U^k\psi\rangle
=\sum_{j\in K}a_j\,\mathrm i^{jk},\qquad
\sum_{j\in K}|a_j|\le1,\qquad |K|\le3.
\tag{353.21}
$$

系数界来自
$\sum_j|a_j|=\sqrt\lambda\sum_j|v_j||\psi_j|\le\sqrt\lambda\le1$。
若 $|K|\le2$，$g_0=g_1=0$ 的 Vandermonde 方程强制 $g$ 恒零。故非零情形有三个频率；乘以一个单位模字符可将 $K$ 平移到 $\{0,1,2\}$，不改变概率或系数绝对值和。其二次多项式在 $1,\mathrm i$ 处为零，所以

$$
g(z)=t(z-1)(z-\mathrm i),\qquad
|t|(2+\sqrt2)\le1.
\tag{353.22}
$$

于是 $|g_2|^2=|g_3|^2=8|t|^2\le s_*$，证明三维不能达到更大幅度。

这个界可达。令

$$
b=(\mathrm i,-(1+\mathrm i),1),\qquad L_0=2+\sqrt2,\qquad
\psi_j=\sqrt{|b_j|/L_0},\qquad
v_j=\overline{b_j/|b_j|}\sqrt{|b_j|/L_0},\qquad
U=\operatorname{diag}(1,\mathrm i,-1).
\tag{353.23}
$$

两向量归一化，且
$\langle v,U^k\psi\rangle=(\mathrm i^k-1)(\mathrm i^k-\mathrm i)/L_0$。
对 $0<s\le s_*$，取 $F=(s/s_*)|v\rangle\langle v|$，它满足 $0\le F\le I$，产生所需概率。读取后重置到 $\psi$ 即给合法仪器。对任意 $s\le1$，四个正交态上的循环置换及效果 $\operatorname{diag}(0,0,s,s)$ 给四维实现；$s=0$ 时一维足够。因此式（353.20）成立。

最后核对分解的尺寸。置 $c=1/\sqrt2$，令 $v_i$ 为正方形顶点、$u_j$ 为其面法向量，沿用式（353.17）的方向。取实三维向量

$$
a_i=(1,v_i),\qquad b_j=(-c,u_j)/\sqrt{2c}.
\tag{353.24}
$$

由于 $u_j\cdot v_i$ 只取 $\pm c$，有
$(a_i\cdot b_j)^2=c-u_j\cdot v_i$。所以 $a_ia_i^{\mathsf T},b_jb_j^{\mathsf T}$ 给尺寸 $3$ 的实半正定分解，旋转由 $\operatorname{diag}(1,R_{\pi/2})$ 实现。将后一族因子乘以 $s/(2c)$ 就给式（353.19）的历史—未来矩阵。

尺寸 $2$ 的复分解不可能。若存在，则每个非零列因子 $B_j$ 都与两条相邻非零行因子迹积为零。$B_j$ 满秩会迫使这两条行因子为零；故 $B_j$ 秩一，这两条行因子都支撑于它的一维核，于是互为正比例。对应矩阵两行就应成比例，但它们的零位置不同，矛盾。实分解是复分解的特例，结合三维实构造，两个半正定秩都恰为 $3$。证毕。

第352节在 $n=4$ 时的幅度为

$$
s=2\sqrt2-2>12-8\sqrt2=s_*,
\qquad d_4=4.
\tag{353.25}
$$

因此即使保留旋转对称性，尺寸三的半正定分解也不能自动变为同维的归一化量子装置。式（353.21）的系数预算同时使用了初态归一化和 $F\le I$，正是单独的正因子化未要求的物理约束。

<a id="entry-1070"></a>

### 353.4 来源、接口范围与未解决的上界

有限维量子通道外围空间的块结构与可逆作用已有成熟理论，可对照 Wolf–Pérez-García，*The Inverse Eigenvalue Problem for Quantum Channels*，[arXiv:1005.4545v1，定理8](https://arxiv.org/html/1005.4545v1#Thmtheorem8)。该外围结构定理本身允许外围之外存在收缩模态。[相位边界卷第15节](../RECURSIVE_RELATIONAL_OBSERVATION_PHASE_BOUNDARY.md)曾将其用于全部输入与参考的精确档案接收；那里的合同不同，并额外排除全部非零严格收缩谱。本节只要求指定读出概率严格周期，允许原通道存在不可见的收缩部分，以式（353.3）替换初态后再提取不增加维数的记录实现。证明中的 Schwarz 等号、乘法域、有限维代数分解及 Schur 乘积均是成熟工具。

Fawzi–Saunderson–Parrilo 同文的定理2及第3节还给出正 $2^m$ 边形尺寸 $2m-1$ 的等变半正定提升。本节没有把它宣称为第352节过程的 $O(\log n)$ 维物理实现。命题353.4已在 $n=4$ 给出同尺寸直接转换失败的例子；它不排除用更大常数倍维数或不同构造完成对数维实现。该匹配上界仍缺归一化与实际通道构造。

定理353.2保留的是一个固定推进、读出后重置的经典记录接口。它不把原系统的噪声、环境、量子输出或参考纠缠恢复出来；其纯初态化也没有扩展到多个非交换推进操作。严格周期的结论不附带近似周期下的稳定性界。上述结果不承担一般近代数问题、量子公理重建、全球原创性或 Lean 核验声明。

<a id="entry-1071"></a>

## 追加锚（本行以下为增补区）

<a id="section-354"></a>

## 354. 多控制记录的共同酉实现与纯初态的容量代价

第353节把单一周期推进化为同容量的酉推进与纯初态。多个控制必须同时作用于同一份记忆，不能分别纯化后再拼接。本节先证明有限群记录接口仍允许不增加总持续维数的共同酉实现，但保留混合初态；再用一个具有层析完备记录的三维例子检验纯初态要求。

<a id="entry-1073"></a>

### 354.1 有限群记录合同与共同实现

**定义 354.1（有限群控制记录）。** 固定有限群 $G$、有限控制字母表 $\mathsf A$ 及生成 $G$ 的标签 $g_a$，允许用群中全部元素作为字母。固定非空有限结果集 $Y$ 与概率族 $p_y(g)\ge0$、$\sum_yp_y(g)=1$。对按时间排列的字串 $w=(a_1,\ldots,a_k)$，约定

$$
g_w=g_{a_k}\cdots g_{a_1},
\qquad g_\varnothing=e.
\tag{354.1}
$$

从初态或上次读取后执行 $w$，下一次结果为 $y$ 的概率是 $p_y(g_w)$；目标在每个结果后重置。这个规则指定全部有限自适应命令树的经典记录律。实现使用固定初态、每个字母的一条固定 CPTP 映射以及一份固定读取仪器，所有持续保存的经典和量子寄存器计入总 Hilbert 维数。装置只收到当前字母或读取命令，没有免费群标签、时钟、历史或持久环境。竞争者可以改变内部读后更新，只须匹配上述完整记录。门参数和精度成本不由此维数计量，合同不含额外量子输出或未操作参考接口。

**定理 354.2（有限群记录的共同酉正规形）。** 若定义354.1的记录接口有 $d$ 维精确 CPTP 实现，则有 $D\le d$ 维实现，使用一份固定的、允许混合的初态 $\sigma$、每个字母的一份固定酉矩阵 $U_a$、一份固定 POVM $(E_y)$，并在读取后实际重置到 $\sigma$。所有字串与全部有限自适应经典记录都保持。各个 $U_a$ 作用于同一个 $D$ 维空间，但此结论不要求这些矩阵在全部输入上构成 $G$ 的普通表示。

证明。取原实现初态 $\rho$、推进 $\Phi_a$ 和首次读取效应 $F_y$，则对全部字串有

$$
\operatorname{tr}(F_y\Phi_w(\rho))=p_y(g_w),
\qquad
\Phi_w=\Phi_{a_k}\circ\cdots\circ\Phi_{a_1}.
\tag{354.2}
$$

原仪器在读取后的行为不进入这条必要条件。

在有限维通道空间与有限群的乘积中取

$$
\mathscr S=\overline{\{(\Phi_w,g_w):w\in\mathsf A^*\}},
\qquad
(T,g)(R,h)=(T\circ R,gh).
\tag{354.3}
$$

有限维 CPTP 映射集合紧，复合连续，所以 $\mathscr S$ 是紧半群。第二坐标只标记证明中的通道极限，没有加入物理寄存器。群有限且离散，因此式（354.2）连续延拓为

$$
\operatorname{tr}(F_yT(\rho))=p_y(g)
\quad\text{对每个 }(T,g)\in\mathscr S.
\tag{354.4}
$$

以下的秩是 $M_d(\mathbb C)$ 上复线性超算子的秩。选 $(T,h)\in\mathscr S$ 使其秩 $r$ 最小。保迹使 $r\ge1$，且 $\operatorname{rank}T^2=r$。于是

$$
M_d=\operatorname{ran}T\oplus\ker T,
\qquad T=A_0\oplus0,
\tag{354.5}
$$

其中 $A_0$ 在 $\operatorname{ran}T$ 上可逆。令 $m$ 为 $h$ 的阶。由紧性，取相邻间隔至少二的严格递增整数 $n_j$，使 $T^{mn_j}\to L$。所有这些幂的群标签都是 $e$，故 $(L,e)\in\mathscr S$。极限在 $\ker T$ 上为零、像包含于 $\operatorname{ran}T$，最小秩又给 $\operatorname{rank}L=r$，所以 $L=B_0\oplus0$ 且 $B_0$ 可逆。由

$$
A_0^{m(n_{j+1}-n_j)}
=A_0^{mn_{j+1}}(A_0^{mn_j})^{-1}\longrightarrow I,
$$

得到一份共同的 CPTP 幂等映射

$$
(P,e)\in\mathscr S,\qquad
P=I_{\operatorname{ran}T}\oplus0,\qquad
P^2=P,\qquad \operatorname{rank}P=r.
\tag{354.6}
$$

这里的投影作用于算子空间，不是原 Hilbert 空间上的正交投影。

记 $V=\operatorname{ran}P$。角半群

$$
\mathscr C=\{(PTP,g):(T,g)\in\mathscr S\}
\tag{354.7}
$$

以 $(P,e)$ 为单位。每个成员的秩既不超过 $r$，又由最小性不小于 $r$，因此在 $V$ 上可逆，并在 $\ker P$ 上为零。限制到 $V$ 将它识别为 $\operatorname{GL}(V)\times G$ 的紧子半群。任意拓扑群的紧子半群都是群：对其中任意 $z$，取 $z^{n_j}\to\ell$ 且相邻间隔至少二，则在环境群中

$$
z^{n_{j+1}-n_j}\to1,\qquad
z^{n_{j+1}-n_j-1}\to z^{-1};
$$

后者都是半群中的非负整数幂，闭性使逆元也在其中。

因而每个压缩推进 $B_a=P\Phi_aP$ 有一份 CPTP 映射 $Q_a=PQ_aP$，满足

$$
Q_aB_a=B_aQ_a=P.
\tag{354.8}
$$

它们在同一个 $V$ 上互逆，不是对各个控制分别选择空间。并且插入的每个 $P$ 标签均为 $e$，式（354.4）给

$$
\operatorname{tr}\!\left(
F_yB_{a_k}\cdots B_{a_1}(P(\rho))
\right)=p_y(g_w).
\tag{354.9}
$$

不需要 $P$ 与原 $\Phi_a$ 对易。

对 CPTP 幂等映射 $P$，外围空间恰为 $V$。使用 Wolf–Pérez-García，*The Inverse Eigenvalue Problem for Quantum Channels*，[arXiv:1005.4545v1，定理8(1)、式(22)](https://arxiv.org/html/1005.4545v1#Thmtheorem8)，得到一个共同的正交分解

$$
\mathbb C^d
=H_0\oplus\bigoplus_{j=1}^s
(\mathbb C^{n_j}\otimes\mathbb C^{m_j}),
\qquad
V=0\oplus\bigoplus_{j=1}^s(M_{n_j}\otimes\tau_j),
\tag{354.10}
$$

其中 $\tau_j>0$ 是迹一矩阵。该文对保迹 Schwarz 映射采用对偶 Schwarz 条件，CPTP 映射满足它。本节只对共同的 $P$ 应用一次该结构定理。

令 $K=\bigoplus_j\mathbb C^{n_j}$、$\mathcal A=\bigoplus_jM_{n_j}\subseteq M_D$，则

$$
D=\dim K=\sum_jn_j\le\sum_jn_jm_j\le d.
\tag{354.11}
$$

所有经典块仍逐块计入维数，只去除固定张量因子 $\tau_j$。定义 CPTP 映射

$$
\begin{aligned}
\beta:M_D&\longrightarrow M_d,
&
\beta(X)&=0\oplus\bigoplus_jX_{jj}\otimes\tau_j,\\
\kappa:M_d&\longrightarrow M_D,
&
\kappa(Z)&=\bigoplus_j\operatorname{Tr}_{\mathbb C^{m_j}}(\Pi_jZ\Pi_j)
+\operatorname{tr}(\Pi_0Z)\omega,
\end{aligned}
\tag{354.12}
$$

其中 $\Pi_0,\Pi_j$ 为显示块的正交投影，$\omega\in\mathcal A$ 为任意固定密度矩阵。块消相干、偏迹、固定态制备均完全正；按总迹直接核对两映射保迹。它们满足

$$
\kappa\beta|_{\mathcal A}=\operatorname{id}_{\mathcal A},
\qquad
\beta\kappa|_V=\operatorname{id}_V.
\tag{354.13}
$$

在同一个 $\mathcal A$ 上，$L_a=\kappa B_a\beta$ 与 $R_a=\kappa Q_a\beta$ 是互逆 CPTP 映射。其迹对偶 $\alpha_a=L_a^\dagger$、$\gamma_a=R_a^\dagger$ 互逆且完全正保单位。Schwarz 不等式及其在逆映射下的对应给

$$
\alpha_a(x^\dagger x)\ge\alpha_a(x)^\dagger\alpha_a(x),
\qquad
\gamma_a(\alpha_a(x)^\dagger\alpha_a(x))\ge x^\dagger x.
\tag{354.14}
$$

对第一式施 $\gamma_a$ 给反向不等式，所以两者取等。由 $\gamma_a$ 单射，$\alpha_a$ 在 Schwarz 不等式中取等；极化得到乘法保持。因此 $\alpha_a$ 是有限维 $C^*$-代数自同构。它只能置换同阶简单块，并在块内作酉共轭；该作用保持普通块迹，其迹对偶也为自同构。所以存在 $K$ 上的一份酉矩阵 $U_a$，使

$$
L_a(X)=U_aXU_a^\dagger
\quad(X\in\mathcal A).
\tag{354.15}
$$

同一块分解适用于全部字母。选择这些实现酉矩阵无需把项目相位或块中心乘子提升为普通群表示。

最后置

$$
\sigma=\kappa(P(\rho)),\qquad E_y=\beta^\dagger(F_y).
\tag{354.16}
$$

$\sigma$ 是 $\mathcal A$ 内的密度矩阵；$\beta^\dagger$ 完全正保单位，故 $E_y\ge0$ 且 $\sum_yE_y=I_D$。对每个字母有 $\beta(U_aXU_a^\dagger)=B_a\beta(X)$，按字串归纳并用式（354.9），得到

$$
\operatorname{tr}(E_yU_w\sigma U_w^\dagger)=p_y(g_w).
\tag{354.17}
$$

定义 $\mathcal J_y(X)=\operatorname{tr}(E_yX)\sigma$。这些分支完全正且总和保迹，每个非零概率分支都实际重置到 $\sigma$。任意有限自适应树的一条结果路径，其条件概率相乘为 $\prod_i p_{y_i}(g_{w_i})$，与目标一致。极限映射与分解只选择固定装置参数，不是运行时需存储时钟或群标签的过程。证毕。

这是一条精确存在性结论，没有给出有效综合成本或近似稳定性。它保留声明的经典记录，不恢复原通道、环境或额外参考接口。第274节的固定因子压缩以及相位边界卷第15—16节的单通道外围投影已有对应工具；这里增加的是由整个通道半群选出一个共同可逆空间，并对全部字串保持响应的连接。

<a id="entry-1074"></a>

### 354.2 完整响应秩迫使最小实现保留群作用

**定理 354.3（满算子秩下的可逆性）。** 在定义354.1的接口中，令 $P=(p_y(g))_{y,g}$。若 $\operatorname{rank}_{\mathbb R}P=d^2$，则任意 $d$ 维精确 CPTP 实现的全部推进映射都为酉共轭。它们的共轭作用只依赖字串的群乘积，并构成 $G$ 在整个 $M_d$ 上的真实作用。这个结论不要求实现的初态纯。

证明。为每个 $g$ 选一条代表字串，恒等元选空字，记其首次读取前状态为 $\tau_g$，固定首次读取效应为 $E_y$。分解

$$
P_{y,g}=\operatorname{tr}(E_y\tau_g)
\tag{354.18}
$$

通过 $d^2$ 维实空间 $\operatorname{Herm}_d$，秩取满迫使 $\{\tau_g\}$ 与 $\{E_y\}$ 各自张成全部空间。若字串 $u,v$ 代表同一群元素，对任意代表字串 $w_t$，先执行 $w_t$ 再执行 $u$ 或 $v$，全部读取概率相等；效应张成性给 $\Phi_u(\tau_t)=\Phi_v(\tau_t)$。状态张成性继而给 $\Phi_u=\Phi_v$ 于全部 Hermitian 矩阵，复线性使等式延伸到 $M_d$。特别是群恒等字串对应空字的恒等通道，代表逆元的字串给每个推进的 CPTP 逆。

这些通道的迹对偶是互逆的完全正保单位映射，式（354.14）的双 Schwarz 论证表明它们是 $M_d$ 的自同构。全矩阵代数自同构由酉共轭实现，其迹对偶也如此。原通道因此已是酉共轭。任意读后更新均不能改变首次读取前的上述约束。证毕。

<a id="entry-1075"></a>

### 354.3 混合三维记忆与同维纯初态的不相容

**定理 354.4（有限控制下纯初态需要额外容量）。** 存在定义354.1的一份有限群记录接口，其一般 CPTP 最小持续维数恰为 $3$，纯初态且允许一般 CPTP 推进的最小持续维数恰为 $4$；若再要求推进全部为酉操作，最小维数介于 $4$ 与 $9$ 之间。特别地，多控制合同不允许把定理354.2的初态无条件改纯并同时保持维数。

证明。令 $\varphi=(1+\sqrt5)/2$，固定正二十面体顶点

$$
(0,\pm1,\pm\varphi),\qquad
(\pm1,\pm\varphi,0),\qquad
(\pm\varphi,0,\pm1).
\tag{354.19}
$$

取其旋转群 $G\cong A_5$，标准实正交表示记为 $R_g\in SO(3)$；全部群元素作为控制字母。置

$$
D=\begin{pmatrix}-1&0&0\\0&0&0\\0&0&1\end{pmatrix},
\qquad
A=\begin{pmatrix}0&-1&1\\1&0&-1\\-1&1&0\end{pmatrix},
\qquad
\rho=\frac I3+\frac{D+\mathrm iA}{20}.
\tag{354.20}
$$

$H=D+\mathrm iA$ 为 Hermitian 矩阵，直接计算 $\det(tI-H)=t(t^2-4)$，故

$$
\operatorname{spec}(\rho)=
\left\{\frac7{30},\frac13,\frac{13}{30}\right\}.
\tag{354.21}
$$

所以 $\rho$ 是严格正的迹一三维态。

以下保留所需的表示论计算。按 $A_5$ 的共轭类排列，令 $\bar\varphi=(1-\sqrt5)/2$，有

$$
\begin{array}{c|rrrrr}
 &1A&2A&3A&5A&5B\\ \hline
\text{类大小}&1&15&20&12&12\\
1&1&1&1&1&1\\
3&3&-1&0&\varphi&\bar\varphi\\
3'&3&-1&0&\bar\varphi&\varphi\\
4&4&0&1&-1&-1\\
5&5&1&-1&0&0
\end{array}
\tag{354.22}
$$

这些行是实际表示的特征标。旋转角的迹公式 $1+2\cos\theta$ 给标准 $R$ 的三维行；由 $S_5$ 中奇置换的共轭交换两个五阶类，得到另一实三维表示 $R'$。五点置换表示去掉常数方向给四维行。实对称无迹矩阵上的共轭作用给五维行，其特征标由

$$
\chi_5(g)=\frac{\chi_R(g)^2+\chi_R(g^2)}2-1
\tag{354.23}
$$

计算，平方交换两个五阶类。按类大小加权并除以 $60$，式（354.22）各行内积为单位矩阵，因此均复不可约且互不等价。维数平方和 $1+9+9+16+25=60$ 证明其穷尽全部复不可约表示。故普通三维表示只能为 $1\oplus1\oplus1$、$R$ 或 $R'$。这是标准 $A_5$ 特征标计算；可对照 Etingof 等，[《Introduction to Representation Theory》第3.1、3.5、3.8节，第41—42页](https://math.mit.edu/~etingof/replect.pdf)。

标准共轭的实表示分解为

$$
\operatorname{Herm}_3
=\mathbb RI
\oplus \mathrm i\,\mathfrak{so}(3,\mathbb R)
\oplus \operatorname{Sym}_0(3,\mathbb R)
\cong1\oplus3\oplus5.
\tag{354.24}
$$

中间分量通过反对称矩阵的轴向量与 $R$ 等价；最后分量由式（354.23）给出。它们两两不等价、各出现一次，复化仍不可约，所以实交织自映射也只能在各分量上乘实标量。

$\rho$ 在这三个分量中都有非零投影。因此 $\rho_g=R_g\rho R_g^T$ 的实轨道张成整个 $\operatorname{Herm}_3$。具体地，各不可约分量的特征标投影是群作用的实线性组合，保持轨道张成空间；每个非零投影再由不可约性生成整个分量。群平均给

$$
\frac1{60}\sum_g\rho_g=\frac I3.
\tag{354.25}
$$

定义固定的六十结果 POVM、控制与读取分支：

$$
F_h=\frac{\rho_h}{20},\qquad
\Phi_a(X)=R_aXR_a^T,\qquad
\mathcal J_h(X)=\operatorname{tr}(F_hX)\rho.
\tag{354.26}
$$

各 $F_h\ge0$，式（354.25）给 $\sum_hF_h=I$。每个分支完全正，总和保迹，非零概率结果后实际重置到 $\rho$。其响应为

$$
p_h(g)=\frac1{20}\operatorname{tr}(\rho_h\rho_g).
\tag{354.27}
$$

任意有限自适应记录按重置逐次相乘，故这是一份完整实现。持续存储只有这个三维系统；六十个控制标签来自当前命令，装置不保存累计群元素或准备标签。

响应矩阵 $P=(p_h(g))_{h,g}$ 是轨道的 Gram 矩阵乘 $1/20$。由轨道张成性，

$$
\operatorname{rank}_{\mathbb R}P=9.
\tag{354.28}
$$

任意 $d$ 维 CPTP 竞争实现都通过 $\operatorname{Herm}_d$ 因子化其首次读取概率，因此 $9\le d^2$。这给一般容量下界 $d\ge3$，由式（354.26）达到。

现在假设一个纯初态竞争实现的维数不超过三。其维数必为三，定理354.3迫使它的全部推进为酉共轭，并在 $M_3$ 上给出群作用 $\beta_g$。记初态为 $\sigma_e$，代表字串后的状态为 $\sigma_g$，读取效应为 $E_h$。响应矩阵秩九迫使两族各张成 $\operatorname{Herm}_3$，故存在唯一实线性同构

$$
S:\operatorname{Herm}_3\longrightarrow\operatorname{Herm}_3,
\qquad
S(\rho_g)=\sigma_g,
\qquad
S\operatorname{Ad}(R_g)=\beta_gS.
\tag{354.29}
$$

其良定义由记录直接保证：若 $\sum_gc_g\rho_g=0$，则 $\sum_gc_g\sigma_g$ 与全部 $E_h$ 的迹配对为零，层析张成性迫使它为零。满秩再给 $S$ 可逆。由于轨道各态迹一，$S$ 保迹；源作用固定空间只有 $\mathbb RI$，交织使目标固定空间也一维，而 $\beta_g$ 固定单位，所以 $S(I)=I$。

还需排除项目表示留下的额外三维模型。选酉代表 $V_g$，$V_e=I$，使 $\beta_g=\operatorname{Ad}(V_g)$，于是

$$
V_gV_k=c(g,k)V_{gk},
\qquad c(g,k)\in U(1).
\tag{354.30}
$$

取行列式 $d_g=\det V_g$，则 $d_gd_k/d_{gk}=c(g,k)^3$。选三阶循环子群 $H\subset A_5$，其指数为二十。$H$ 的项目作用有一条共同不变复直线：取生成元酉代表的一个本征向量 $v$，其余代表均为该生成元幂的标量倍。对左陪集 $x\in G/H$ 选代表 $r_x$ 并令 $v_x=V_{r_x}v$。存在唯一相位 $m(g,x)$ 使

$$
V_gv_x=m(g,x)v_{gx}.
$$

在以陪集为正交基的二十维辅助证明空间上定义 $W_ge_x=m(g,x)e_{gx}$。这些是酉单项矩阵，式（354.30）直接给 $W_gW_k=c(g,k)W_{gk}$。因此若 $e_g=\det W_g$，则 $e_ge_k/e_{gk}=c(g,k)^{20}$。利用 $7\cdot3-20=1$，置

$$
q_g=\frac{d_g^7}{e_g},
\qquad
\frac{q_gq_k}{q_{gk}}=c(g,k),
\qquad
\widetilde V_g=q_g^{-1}V_g.
\tag{354.31}
$$

于是 $\widetilde V$ 是普通酉表示，共轭作用仍为 $\beta$。二十维空间只用于证明消去标量乘子，不是实现中的额外存储。这也不使用未声明的 Schur 乘子分类；项目表示与乘子的一般定义可对照 Etingof–Gelaki–Nikshych–Ostrik，[《Tensor Categories》例7.4.9，印刷页136](https://math.mit.edu/~etingof/egnobookfinal.pdf#page=153)。

由式（354.22），$\widetilde V$ 只能为全平凡、$R$ 或 $R'$。平凡表示不能生成九维轨道。$R'$ 的 Hermitian 共轭表示为 $1\oplus3'\oplus5$，与式（354.24）不等价，不能由可逆 $S$ 交织；在五阶类上，其共轭特征标 $\bar\varphi^2$ 与 $\varphi^2$ 已不同。因此目标表示酉等价于 $R$，可选竞争者基底使二者一致。

式（354.29）的 $S$ 现在与标准共轭对易。实 Schur 引理、各分量只出现一次以及 $S(I)=I$，给

$$
\sigma_e=S(\rho)
=\frac I3+\frac{aD+\mathrm i\,bA}{20},
\qquad
a,b\in\mathbb R\setminus\{0\}.
\tag{354.32}
$$

这些矩阵都不可能是纯态。若 $\sigma=zz^\dagger$，写 $z=u+\mathrm iv$，$u,v\in\mathbb R^3$，则其实部与虚部分别为

$$
B=uu^T+vv^T,\qquad C=vu^T-uv^T=[u\times v]_\times.
\tag{354.33}
$$

因此虚部的轴向量 $n=u\times v$ 必满足 $Bn=0$。但对式（354.32），

$$
n=\frac b{20}(1,1,1)^T,\qquad
B=\operatorname{diag}\!\left(\frac13-\frac a{20},\frac13,\frac13+\frac a{20}\right),
\qquad
(Bn)_2=\frac b{60}\ne0.
\tag{354.34}
$$

这与纯态条件矛盾。由定理354.3，这个排除覆盖一般 CPTP 推进的纯初态三维竞争者，而不只覆盖预先选定的控制矩阵。

四维可以达到纯初态且一般 CPTP 推进的下界。令 $K=\mathbb C|f\rangle\oplus\mathbb C^3$，其中 $|f\rangle$ 是与三维核心正交的单位初始化状态，取它为固定纯初态。对任意算子 $X=\begin{pmatrix}x&r\\s&Z\end{pmatrix}$，定义

$$
\begin{aligned}
\widehat\Phi_a(X)
&=0\oplus R_a(Z+x\rho)R_a^T,\\
\widehat E_h
&=p_h(e)|f\rangle\langle f|\oplus F_h,\\
\widehat{\mathcal J}_h(X)
&=\operatorname{tr}(\widehat E_hX)|f\rangle\langle f|.
\end{aligned}
\tag{354.34a}
$$

推进先丢弃两个正交块之间的相干，再将初始化块的迹制备为 $\rho$、把原核心保持，最后对核心作 $R_a$ 共轭。各步完全正；输出迹为 $\operatorname{tr}Z+x=\operatorname{tr}X$，所以推进是 CPTP。效应非负且总和为 $I_4$，读取后实际重置到同一个纯初始化态。

空字串直接从初始化块读取，给出 $p_h(e)$；任何非空字串都把初态送到 $0\oplus\rho_{g_w}$，因为第一步制备对应的轨道态，后续步骤在核心内按群乘积推进。故全部字串响应及每次重置后的自适应记录都保持。第四个状态计入总容量，没有附赠的外部标志或时钟。结合已证下界，纯初态的一般 CPTP 最小维数恰为四。这里的推进在整个 $M_4$ 上不可逆：它把初始化态与核心中的 $\rho$ 送到同一个状态，因此不构成纯初态的酉推进实现。

最后，取 $\rho$ 的一份纯化 $|\Psi\rangle\in\mathbb C^3\otimes\mathbb C^3$，用 $R_a\otimes I_3$ 推进、$F_h\otimes I_3$ 读取，并取分支

$$
\widehat{\mathcal J}_h(X)
=\operatorname{tr}((F_h\otimes I_3)X)\,|\Psi\rangle\langle\Psi|.
\tag{354.35}
$$

每次读取都重置整个联合系统，故全部自适应记录保持。两份三维寄存器均计入持续容量，得到九维上界。证毕。

若分别记一般实现、纯初态且一般推进、纯初态且酉推进的最小维数，所得结论准确为

$$
d_{\mathrm{all}}=3,
\qquad
d_{\mathrm{pure,CPTP}}=4,
\qquad
4\le d_{\mathrm{pure,unitary}}\le9.
\tag{354.36}
$$

没有确定纯初态且酉推进的准确最小值，也没有宣称九维最优。混合态的标准纯化仍然存在；本例证明的是：在要求同一组多控制记录全部保持、并计入全部持久寄存器时，纯化不能总在原最小容量内完成。

<a id="entry-1076"></a>

### 354.4 来源与适用范围

共同酉正规形使用成熟的紧矩阵半群、幂等通道外围结构、完全正序同构及有限维代数工具。Wolf–Pérez-García 的原定理承担式（354.10）的块分解；式（354.3）—（354.9）承担由同一记录合同取得共同可逆空间的连接。该结果不要求原控制共有忠实固定态，也不从一份平均通道的固定态推出每个原控制分别固定它。

$A_5$ 的三维表示、特征标与 Schur 引理属于标准有限群表示论，见上述 Etingof 教材。项目的[观察者 adelic 完成常数卷定理26.1](../OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY.md)已经使用 $3,3'$ 及相关外幂分解；本节不将这些成分视作新表示论。新增接口论证由合法态与 POVM、完整响应秩、对全部竞争实现的群作用约束及纯态相容性矛盾共同构成。定理354.4的二十维陪集空间只是项目乘子证明，不与九维物理纯化容量混用。

本节保持有限群、精确字串响应和读取后重置的经典接口。它没有把“可逆”和“纯”重新定义成同一个条件，也没有推出量子公理、一般时空结构或多边形过程的对数维上界。近似群关系、有限观测窗口、无限群以及纯初态且酉推进容量的准确数值仍在显示结论之外。上述推导为理论正文与解析论证，不作全球原创性或 Lean 核验声明。

<a id="entry-1077"></a>

## 追加锚（本行以下为增补区）
