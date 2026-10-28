# AURIC FIB 环境实测记录的 Shannon 熵率

## 1. 模型、来源与条件范围

本文研究同一五维平均通道的一族实测环境仪器，在每次结果均实际取得、只允许经典记录更新的任务中，精确恢复所需的完整终端记录的 Shannon 熵。所有对数以二为底。本文只给普通、未执行的条件符号推导；数学源接口取自所供应的原卷，未对其链接原文或版本作独立认证，也没有形式内核验证。

称所供应的 *AURIC FIB environment instruments and terminal record memory* 为原卷。其定义 1.3、假设 1.4、定义 1.5、定理 2.2 规定以下实际模型；其定理 3.3、4.1、16.1 提供精确摘要判据及实现。下述模型和这些通用纠错接口是复用，本文的实质推导是把原卷的维数二 Strong Tits 接口转为实际非对称公平字律的统一正 Shannon 熵率。

**定义 1.1（五维仪器及恢复权限）。** 令

$$
\begin{gathered}
H=\mathbb C^5,\qquad
(e_0,e_1,e_2,e_3,e_4)=(|000\rangle,|100\rangle,|010\rangle,|001\rangle,|101\rangle),\\
q=2^{-1/2},\quad u=q(e_0+e_3),\quad v=q(e_1+e_4),\quad z=e_2,\\
R=\operatorname{span}\{u,v,z\},\qquad
B(x_0,x_1,x_2)=x_0u+x_1v+x_2z,\quad B^\dagger B=I_3,\quad P_R=BB^\dagger.
\end{gathered}
$$

环境 $E=\mathbb C^2$ 的正交基为 $f_0,f_1$，准备态为 $f_0$。全输入等距映射由

$$
\begin{aligned}
\mathcal V e_0&=u\otimes f_0,& \mathcal V e_1&=u\otimes f_1,\\
\mathcal V e_2&=v\otimes(f_0+f_1)/\sqrt2,&
\mathcal V e_3&=z\otimes f_1,& \mathcal V e_4&=z\otimes f_0
\end{aligned}
$$

给定。五个像正交归一，故可补成 $H\otimes E$ 上的酉算子 $\mathsf U$，满足 $\mathsf U(x\otimes f_0)=\mathcal Vx$。测量 $f$ 基的全五维 Kraus 算子是

$$
\begin{aligned}
K_0&=|u\rangle\langle e_0|+q|v\rangle\langle e_2|+|z\rangle\langle e_4|,\\
K_1&=|u\rangle\langle e_1|+q|v\rangle\langle e_2|+|z\rangle\langle e_3|,
\end{aligned}
$$

即

$$
K_0=\begin{pmatrix}
q&0&0&0&0\\0&0&1/2&0&0\\0&0&0&0&1\\q&0&0&0&0\\0&0&1/2&0&0
\end{pmatrix},\qquad
K_1=\begin{pmatrix}
0&q&0&0&0\\0&0&1/2&0&0\\0&0&0&1&0\\0&q&0&0&0\\0&0&1/2&0&0
\end{pmatrix}.
$$

对固定实数 $\theta$，记 $c=\cos\theta,s=\sin\theta$。保持同一准备与相互作用，实际测量

$$
g_0=cf_0-isf_1,\qquad g_1=-isf_0+cf_1.
$$

所得全算子为 $A_0=cK_0+isK_1$、$A_1=isK_0+cK_1$。原卷定理 2.2 的恒等式在整个复代数上成立：

$$
\sum_{j=0}^1 A_jXA_j^\dagger
=K_0XK_0^\dagger+K_1XK_1^\dagger=\Phi_\circ(X),\qquad X\in M_5(\mathbb C).
$$

理由是基变换矩阵 $\begin{pmatrix}c&is\\is&c\end{pmatrix}$ 酉，展开后的两个复交叉项各自抵消；把各算子张量 $I_Z$ 后仍成立。这是所有复输入及任意未触动参考上的平均通道相等。

每一步准备新环境，重复同一固定测量仪器，实际取得二元结果后丢弃环境，只允许结果更新经典记录。已知步数为 $n$。终端可根据完整记录选任意 $H$ 上确定 CPTP 解码器；要求对每个有限参考 $Z$ 及每个 $\mathbb C^3\otimes Z$ 上的态恢复其 $B\otimes I_Z$ 嵌入，允许只要求对结果和经典随机性平均后成功。恢复对象是 $R$ 上未知 qutrit 及其参考。没有中间量子反馈、适应仪器、量子环境保留、参考读取、输入相关量子侧信息或成功后选择。

**定义 1.2（实际限制矩阵与公平取得）。** 原卷定理 2.2 给出

$$
\begin{gathered}
U_0=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\quad
U_1=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix},\quad
W=U_0^\dagger U_1=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix},\\
W^\dagger=W,\quad W^2=I_3,\quad
K_jB=qBU_j,\\
a=V_0=cU_0+isU_1=U_0e^{i\theta W},\quad
b=V_1=isU_0+cU_1=aW,\quad A_jB=qBV_j.
\end{gathered}
$$

由于 $W$ 是自伴对合，$V_0,V_1$ 均酉，且 $B^\dagger A_j^\dagger A_jB=I_3/2$。因此每个已有历史之后，条件系统态仍在 $R$，下一实际结果的概率仍为 $1/2$，包括与 $Z$ 纠缠的输入。归纳得每条长 $n$ 历史的概率为 $2^{-n}$。公平性只在 $R$ 上主张；例如 $K_0^\dagger K_0=\operatorname{diag}(1,0,1/2,0,1)$，全 $H$ 上的仪器不是两个缩放酉算子。

## 2. 实际类律与普通离散群的精确对应

**定义 2.1（类、重数与熵）。** 对按时间排序的实际历史 $h=(h_1,\ldots,h_n)$，最早因子放在右侧，令

$$
Q_h=V_{h_n}\cdots V_{h_1},\quad Q_{\varnothing}=I_3,\quad
C_n=[Q_{\mathsf H_n}],\quad
\mathcal C_n=\{[Q_h]:h\in\{0,1\}^n\},\quad m_n=|\mathcal C_n|.
$$

方括号是全 qutrit 矩阵相差模一标量的等价类。实际公平历史 $\mathsf H_n$ 诱导

$$
k_{n,C}=|\{h:[Q_h]=C\}|,\qquad
p_{n,C}=2^{-n}k_{n,C},\qquad
H_n=H_{\rm Sh}(C_n)=-\sum_Cp_{n,C}\log_2p_{n,C},\quad H_0=0.
$$

于是

$$
H_n=n-2^{-n}\sum_Ck_{n,C}\log_2k_{n,C},\qquad
0\le H_n\le\log_2m_n\le n.
\tag{2.1}
$$

第一式来自将真正概率代入熵定义。上界来自对数凹性：$\sum_Cp_C\log_2(1/p_C)\le\log_2\sum_Cp_C/p_C=\log_2m_n$。重数一般不能用均匀支持律替换。

**引理 2.2（固定步数的精确对应）。** 置

$$
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\qquad T=\xi^\perp,\qquad
 t_1=(1,-1,0)^{\mathsf T}/\sqrt2,\quad t_2=(1,1,-2)^{\mathsf T}/\sqrt6.
$$

在这个固定正交基中令 $\alpha=a|_T$、$\gamma=b|_T$，则

$$
\begin{gathered}
U_{0,T}=\begin{pmatrix}1/2&\sqrt3/2\\\sqrt3/2&-1/2\end{pmatrix},\quad
U_{1,T}=\begin{pmatrix}-1/2&\sqrt3/2\\-\sqrt3/2&-1/2\end{pmatrix},\quad
W_T=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\\
\alpha=\begin{pmatrix}e^{-i\theta}/2&\sqrt3e^{i\theta}/2\\
\sqrt3e^{-i\theta}/2&-e^{i\theta}/2\end{pmatrix},\qquad
\gamma=\alpha W_T.
\end{gathered}
$$

视 $\Gamma_\theta=\langle\alpha,\gamma\rangle\le U(2)$ 为带计数测度的可数离散抽象矩阵群，并令 $\mu=(\delta_\alpha+\delta_\gamma)/2$。对每个固定 $n$，$\mu^{*n}$ 的支持与 $\mathcal C_n$ 一一对应，概率完全相同，故

$$
H(\mu^{*n})=H_n.
\tag{2.2}
$$

证明。原卷式 (11.2) 的关键是保留共同直线的相位。两实际字母在 $\xi$ 上都是 $e^{i\theta}$；所有矩阵共同约化 $\mathbb C\xi\oplus T$。若同长的 $Q_h=\lambda Q_g$，作用到 $\xi$ 得 $\lambda=1$。若普通限制矩阵相等，再加上共同的 $e^{in\theta}$ 直线块，便得全矩阵相等。因此同一步数内

$$
[Q_h]=[Q_g]\quad\Longleftrightarrow\quad Q_h=Q_g
\quad\Longleftrightarrow\quad Q_h|_T=Q_g|_T.
$$

实际乘积概率为 $2^{-n}$，合并相等普通限制产品所得重数正是 $k_{n,C}$，证明结论。这没有把 $U(2)$ 等式换成 $PU(2)$ 等式，也没有把跨长度限制等式宣告为全 qutrit 射影等式。群的紧闭包及其 Haar 概率不参与下面的正则表示。$\square$

**引理 2.3（实际熵率与下确界）。** 对每个实角，极限存在且

$$
h_{\rm Sh}(\theta)=\lim_{n\to\infty}\frac{H_n}n
=\inf_{n\ge1}\frac{H_n}n.
\tag{2.3}
$$

证明。取独立的长 $m,n$ 普通群产品 $X,Y$。$YX$ 是两者的确定函数，分布是 $\mu^{*(m+n)}$。利用 (2.2) 及独立性，$H_{m+n}\le H_m+H_n$。固定 $M\ge1$，写 $n=tM+s$，$0\le s<M$，则 $H_n\le tH_M+H_s\le tH_M+M$，所以 $\limsup H_n/n\le H_M/M$。对 $M$ 取下确界，再用每个 $H_n/n$ 都不小于该下确界，便得 (2.3)。这个结论针对真实重数律。$\square$

## 3. 唯一外部群条件与统一结论

**约定 3.1（条件性 Strong Tits 供应接口）。** 原卷定理 12.2 已对实际 $\Gamma_\theta\le GL_2(\mathbb C)$ 证明：$\theta\notin(\pi/2)\mathbb Z$ 时该群非 virtually solvable，即不含有限指数可解子群。这里直接复用该实际群结论。其双向生成对应为原卷式 (12.9)：

$$
W=a^{-1}b,\quad U_0=W(aWa^{-1})W,\quad
U_1=U_0W,\quad e^{i\theta W}=U_0a,\quad a=U_1We^{i\theta W},\quad b=aW.
$$

原卷以这些对应及实际旋转的闭包论证建立非虚可解性；本文不从支持增长或稠密性单独推断熵率。

唯一外部群定理条件记为 (ST2)，严格采用原卷 §13 所引用的 Breuillard，*A Strong Tits Alternative*，Theorem 1.1，arXiv:0804.1395v1，PDF 第 1 页的陈述：对每个维数 $d$，存在整数 $N(d)$，使任意域 $K$ 中任意有限、对称、含单位的 $F\subseteq GL_d(K)$，或 $\langle F\rangle$ 虚可解，或 $F^{N(d)}$ 含两个自由生成非交换自由群的元素。本文以这份所供应陈述为条件；未打开外部原文，也未另行认证其版本或陈述。以下所有依赖该接口的结论均有这个条件。

固定 $N=N(2)\ge1$。每个非有界角都可将 (ST2) 用于

$$
F=\{I_2,\alpha,\gamma,\alpha^{-1},\gamma^{-1}\}.
$$

该集合有限、对称、含单位、全由可逆二阶复矩阵组成，且生成的正是原卷定理 12.2 的群。故有 $x,y\in F^N$ 自由生成秩二自由群。由于 $I_2\in F$，它们各可用至多 $N$ 个字母表示；由对称性，$x^{-1},y^{-1}$ 也有相同长度界。元素可随角变化，但 $N$ 不变。

**定理 3.2（统一严格正的实际 Shannon 熵率）。** 在约定 3.1 的条件下，定义

$$
d_N=\frac{2-\sqrt3}{8N^2},\qquad r_N=1-d_N,\qquad
c_N=-2\log_2r_N>0.
\tag{3.1}
$$

则每个 $\theta\notin(\pi/2)\mathbb Z$、每个 $n\ge1$ 都有

$$
H_n(\theta)\ge c_N n,\qquad
c_N\le h_{\rm Sh}(\theta)\le h_0(\theta)\le1,
\quad h_0(\theta)=\lim_{n\to\infty}\frac{\log_2m_n(\theta)}n.
\tag{3.2}
$$

有界角恰为 $\theta\in(\pi/2)\mathbb Z$，它们的 Shannon 熵率均为零。这是对所有非有界角的同一个正下界，允许角任意接近有界集合，没有依赖角的起始步数。$N$ 及常数的数值只具有存在性。定理的完整证明由 §§4–6 给出；$h_0$ 的存在性是原卷定理 15.3，或由 $m_{m+n}\le m_mm_n$ 用引理 2.3 的同一分块论证得到。

## 4. 自由树梯度估计与实际字母的转移

**引理 4.1（独立的自由树正则表示估计）。** 在 $\ell^2(\Gamma_\theta)$ 上令

$$
(\lambda(g)f)(t)=f(g^{-1}t),\qquad
\mathcal A=\lambda(x)+\lambda(x^{-1})+\lambda(y)+\lambda(y^{-1}).
$$

则每个 $f\in\ell^2(\Gamma_\theta)$ 满足

$$
\sum_{s\in\{x,x^{-1},y,y^{-1}\}}\|\lambda(s)f-f\|_2^2
\ge(8-4\sqrt3)\|f\|_2^2.
\tag{4.1}
$$

证明。$\lambda$ 为同一普通离散群的酉表示，$\lambda(g)\delta_h=\delta_{gh}$。自由子群 $\langle x,y\rangle$ 的左作用轨道是自由作用轨道；每个轨道的四字母无向图为四正则树，否则删去立即回退的闭路会给非空约化自由字等于单位。

先取有限支持 $f$。在每个与支持相交的轨道任选根，将所有边从父亲指向孩子。$\mathcal A$ 自伴，且每条无向边恰贡献

$$
2\operatorname{Re}\big(\overline{f(p)}f(q)\big)
\le 2|f(p)||f(q)|
\le\frac{|f(p)|^2}{\sqrt3}+\sqrt3|f(q)|^2.
$$

这里 $p$ 为父、$q$ 为子，末式是平方非负的不等式。非根顶点有三个孩子和一个父亲，汇总系数为 $3/\sqrt3+\sqrt3=2\sqrt3$；根有四个孩子且无父亲，其系数是 $4/\sqrt3\le2\sqrt3$。支持外的值为零，只有有限条边有非零贡献，故

$$
\langle\mathcal A f,f\rangle\le2\sqrt3\|f\|_2^2.
$$

四个酉算子的和有界，有限支持向量稠密，所以上式延拓至整个空间。展开每个梯度平方，并用 $\mathcal A$ 自伴得

$$
\sum_s\|\lambda(s)f-f\|_2^2
=8\|f\|_2^2-2\langle\mathcal A f,f\rangle
\ge(8-4\sqrt3)\|f\|_2^2.
$$

这直接证明所需估计，不另引谱隙定理。$\square$

**引理 4.2（逆字母消去及 $N^2$ 常数）。** 对实际字母有

$$
\|\lambda(\alpha)f-f\|_2^2+\|\lambda(\gamma)f-f\|_2^2
\ge\frac{2-\sqrt3}{N^2}\|f\|_2^2.
\tag{4.2}
$$

证明。固定 $f$，记 $D_g=\|\lambda(g)f-f\|_2$。酉性给 $D_{g^{-1}}=D_g$。若 $s=g_1\cdots g_k$，在同一表示中准确展开

$$
\lambda(s)-I=\sum_{j=1}^k
\lambda(g_1\cdots g_{j-1})(\lambda(g_j)-I).
$$

作用到 $f$ 后由三角不等式及酉性，$D_s\le\sum_jD_{g_j}$。对四个自由生成字母分别用长度至多 $N$ 的 $F$ 表达式，单位项为零，逆项等于相应正向项，故

$$
D_s^2\le N^2(D_\alpha^2+D_\gamma^2).
$$

将四式相加并用 (4.1)，得到 $4N^2(D_\alpha^2+D_\gamma^2)\ge(8-4\sqrt3)\|f\|_2^2$，即 (4.2)。没有切换表示，也没有假定逆字母属于实际测量字母。$\square$

## 5. 辅助惰性律的平方范数与碰撞熵

**引理 5.1（原算子范数一与辅助收缩）。** 定义

$$
P=\frac{\lambda(\alpha)+\lambda(\gamma)}2,\qquad
L=\frac{I+P}2=\frac I2+\frac{\lambda(\alpha)}4+\frac{\lambda(\gamma)}4.
$$

实际算子满足 $\|P\|=1$；辅助算子满足

$$
\|Lf\|_2^2\le r_N\|f\|_2^2,\qquad
\|L\|\le\sqrt{r_N}<1.
\tag{5.1}
$$

证明。因为 $\gamma=\alpha W_T$，且 $W_T$ 是非单位对合，

$$
P=\lambda(\alpha)\frac{I+\lambda(W_T)}2.
$$

后一因子是非零正交投影：$\delta_e+\delta_{W_T}$ 是其非零不动向量。因此 $P$ 的范数恰为一，不能直接宣称原平均算子严格收缩。

对任意 Hilbert 空间中的向量 $u_i$ 与非负权重 $w_i$、$\sum_iw_i=1$，展开内积可得精确方差恒等式

$$
\left\|\sum_iw_iu_i\right\|^2
=\sum_iw_i\|u_i\|^2-\sum_{i<j}w_iw_j\|u_i-u_j\|^2.
$$

取 $u_0=f,u_1=\lambda(\alpha)f,u_2=\lambda(\gamma)f$ 和权重 $1/2,1/4,1/4$，三向量等范数，所以

$$
\|Lf\|_2^2=\|f\|_2^2-
\frac{D_\alpha^2+D_\gamma^2}{8}
-\frac{\|\lambda(\alpha)f-\lambda(\gamma)f\|_2^2}{16}
\le r_N\|f\|_2^2
$$

由 (4.2) 即得。由于 $N\ge1$ 及 $0<2-\sqrt3<1$，$0<r_N<1$。这里 $r_N$ 控制平方范数，$\sqrt{r_N}$ 才是算子范数上界。$\square$

**引理 5.2（辅助分布的熵下界）。** 只为证明定义群上的辅助概率

$$
\nu=\frac{\delta_e+\mu}2,
$$

并令 $Z_n$ 的分布为 $\nu^{*n}$。则

$$
\sum_g\Pr(Z_n=g)^2\le r_N^n,\qquad
H(Z_n)\ge-n\log_2r_N.
\tag{5.2}
$$

证明。每个 $\nu^{*n}$ 有限支持，其概率向量在本表示中是 $L^n\delta_e$。由 (5.1) 逐次应用，平方范数不超过 $r_N^n$。对有限概率向量 $q$，省去零项，凸函数 $-\log_2$ 的 Jensen 不等式给

$$
H(q)=\sum_gq_g(-\log_2q_g)
\ge-\log_2\left(\sum_gq_g^2\right).
$$

由此得 (5.2)。这是明确指定的辅助非对称惰性律的结论；没有借用对称随机游走的谱或熵。辅助单位步没有改变实际仪器、许可操作或实际取得次数。$\square$

## 6. 二项激活的精确移除与所有步数的下界

**引理 6.1（辅助律与实际公平律的精确熵比较）。** 令 $K_n\sim\operatorname{Bin}(n,1/2)$。存在同一概率实现使

$$
\operatorname{Law}(Z_n\mid K_n=k)=\mu^{*k},\qquad
\nu^{*n}=\sum_{k=0}^n\binom nk2^{-n}\mu^{*k}.
\tag{6.1}
$$

并且

$$
\begin{aligned}
H(Z_n)&=\mathbb E H_{K_n}+H(K_n)-H(K_n\mid Z_n),\\
\mathbb E H_{K_n}&\le H(Z_n)
\le\mathbb E H_{K_n}+\log_2(n+1).
\end{aligned}
\tag{6.2}
$$

这些式子允许 $\Gamma_\theta$ 内出现跨长度相等。

证明。在辅助过程的每个位置取独立公平激活位；激活时再取一个独立的实际公平字母 $\alpha$ 或 $\gamma$，不激活时取单位。$K_n$ 是激活位置数。给定任意恰含 $k$ 个位置的激活图样，删除单位后，按时间排列的剩余 $k$ 个字母仍独立公平，乘积律为 $\mu^{*k}$。对所有这种图样平均，得到条件律及二项混合式。由引理 2.2，每个条件律的熵正是实际长 $k$ 类的 $H_k$。

变量 $K_n,Z_n$ 均有限值，链式法则给 $H(Z_n,K_n)=H(K_n)+\mathbb E H_{K_n}=H(Z_n)+H(K_n\mid Z_n)$。条件熵非负且不超过 $H(K_n)$，又 $K_n$ 只有 $n+1$ 个可能值，得 (6.2)。如果不同长度的普通限制产品相等，$Z_n$ 的混合会合并它们，式中 $H(K_n\mid Z_n)$ 正好保留这部分不确定性；没有假设各长度的支持不交，也没有要求该跨长度识别对应全 qutrit 射影识别。每个给定 $k$ 的实际对应仍完全精确。$\square$

**引理 6.2（惰性熵率恰为实际熵率的一半）。** 若 $h=h_{\rm Sh}(\theta)$，则

$$
\lim_{n\to\infty}\frac{\mathbb E H_{K_n}}n=rac h2,
\qquad
\lim_{n\to\infty}\frac{H(Z_n)}n=rac h2.
\tag{6.3}
$$

证明。由 (2.3)，每个 $k\ge0$ 有 $H_k\ge hk$，且 $H_k/k\to h$。给定 $\varepsilon>0$，存在有限 $B_\varepsilon\ge0$ 使所有 $k\ge0$ 都有

$$
H_k\le(h+\varepsilon)k+B_\varepsilon.
$$

只需对足够大的 $k$ 用极限，对其余有限个值取一个共同余量。此存在量可依赖角，但不会进入最终常数。由 $\mathbb E K_n=n/2$，

$$
\frac{hn}2\le\mathbb E H_{K_n}
\le\frac{(h+\varepsilon)n}2+B_\varepsilon.
$$

除以 $n$、令 $n\to\infty$ 再令 $\varepsilon\downarrow0$，证明第一式。利用 (6.2) 及 $\log_2(n+1)/n\to0$ 得第二式。没有用一个角统一的收敛起点。$\square$

证明定理 3.2。对任意非有界角，(5.2) 与 (6.3) 给

$$
\frac{h_{\rm Sh}(\theta)}2\ge-\log_2r_N,
\qquad h_{\rm Sh}(\theta)\ge c_N>0.
$$

(2.3) 随即给每个 $n\ge1$ 的 $H_n\ge c_Nn$。所有角的同一常数仅依赖 (ST2) 的维数二整数 $N$；极限证明中的 $B_\varepsilon$ 没有出现在结论。由 (2.1) 取极限得 $h_{\rm Sh}\le h_0\le1$。在 $\theta\in(\pi/2)\mathbb Z$，原卷定理 12.1 给 $m_n\le6$，故 $0\le H_n\le\log_2 6$、熵率零。$n=0$ 总有 $H_0=0$。这也证明零率角恰为有界角，且最终所有正整数步数的下界不含额外起始条件。$\square$

## 7. 有界、极大与实际碰撞角

**命题 7.1（零率与极大率区域）。** 对 $\theta=k\pi/2$，原卷式 (12.7) 为

$$
V_j=i^kU_{j\mathbin\oplus(k\bmod2)}.
$$

同长公共相位和公平标签互换只重命名类律，故所有这些角的类律与 $\theta=0$ 相同。其最小字母表序列为 $1,2,4,6,6,\ldots$，固定比特序列为 $0,1,2,3,3,\ldots$；$H_1=1,H_2=2$，而所有 $H_n\le\log_2 6$。零率不表示每个有限步数的熵为零。

对任意角，以下条件等价：$h_{\rm Sh}=1$；每个有限步数都无两条不同历史的同长碰撞；每个 $n$ 都有 $H_n=n$。这些条件也等价于原卷的 $h_0=1$，但这不意味着一般角有 $h_{\rm Sh}=h_0$。

证明。无碰撞时每个 $k_{n,C}=1$，实际类律均匀，故 $H_n=n$、$h_{\rm Sh}=1$。若某步数 $\ell$ 有碰撞，某个重数至少为二，式 (2.1) 给 $H_\ell<\ell$，再由 (2.3) 得 $h_{\rm Sh}\le H_\ell/\ell<1$。$h_0$ 的相应等价性是原卷定理 15.3，也可由 $m_\ell<2^\ell$ 及支持下确界公式得到。有界角的陈述由原卷定理 12.1 和公平类律得出。$\square$

原卷定理 14.1–14.2 给出以下极大率的充分区域：全部非有界有理角 $\theta/\pi\in\mathbb Q\setminus\tfrac12\mathbb Z$；以及 $\cos\theta\ne0$ 时 $z_\theta=i\tan\theta$ 超越，或其原始不可约多项式 $f\in\mathbb Z[X]$ 满足 $f(1)$ 为偶数的角。在这些区域，所有 $H_n=n$，最小离散完整记录熵为 $n$。奇数 $f(1)$ 只表示所用模二剩余映射不适用，不是碰撞的充分条件。$\theta=\pi/6$ 更强的跨长度注入性由原卷定理 8.2 提供，本文不将其扩展到所有角。

**命题 7.2（非极大但严格正的实际碰撞例）。** 取原卷定理 15.1 的

$$
s_*=(\sqrt5-1)/2,\qquad \theta_*=\arcsin s_*\in(0,\pi/2).
$$

该角 $\theta_*/\pi$ 无理，实际全 qutrit 上有

$$
a^5b=ba^5,\qquad m_6(\theta_*)\le63,
$$

且实际熵满足

$$
H_6(\theta_*)\le6-\frac1{32},\qquad
c_N\le h_{\rm Sh}(\theta_*)\le1-\frac1{192}<1,
\qquad
h_{\rm Sh}(\theta_*)\le h_0(\theta_*)\le\frac{\log_2 63}{6}.
\tag{7.1}
$$

证明。保留源定理的实际矩阵对应：$\det a_T=-1$、$\operatorname{tr}(ia_T)=s_*=2\cos(2\pi/5)$，所以 $ia_T\in SU(2)$ 的两个特征值是 $e^{\pm2\pi i/5}$，从而 $a_T^5=-iI_2$。在共同直线 $\mathbb C\xi$ 上 $a^5$ 是 $e^{5i\theta_*}$。这两个标量块都与保持分解的 $b$ 对易，故全 qutrit 上 $a^5b=ba^5$；不需要两个块的标量相等。

在最早因子靠右的约定中，实际历史 $(1,0,0,0,0,0)$ 的产品是 $a^5b$，历史 $(0,0,0,0,0,1)$ 的产品是 $ba^5$，两者各有概率 $1/64$。故某类重数至少二，且至少合并这两个历史给 $m_6\le63$。由 (2.1)，

$$
H_6=6-\frac1{64}\sum_Ck_{6,C}\log_2k_{6,C}
\le6-\frac{2\log_2 2}{64}=6-\frac1{32}.
$$

利用 (2.3) 得 $h_{\rm Sh}\le H_6/6\le1-1/192$。该角非有界，定理 3.2 给正下界。原卷支持界和支持下确界公式另给 $h_0\le\log_2(63)/6$。

无理性可按原卷的独立判据核对：若 $\theta_*/\pi$ 有理，把 $e^{i\theta_*}$ 与 $i$ 放入同一分圆域，则它的嵌入将 $s_*=(e^{i\theta_*}-e^{-i\theta_*})/(2i)$ 送到 $[-1,1]$ 内的实正弦或其负值。但 $s_*$ 的不可约多项式 $X^2+X-1$ 的另一共轭是 $-(\sqrt5+1)/2<-1$，且该嵌入可延拓到分圆域，矛盾。原卷还给出 $i\tan\theta_*$ 的原始不可约多项式 $X^4-X^2-1$，其在 $X=1$ 处的值为奇数 $-1$。这仅是一个实际碰撞例。未断言剩余历史全为单例，也未给出精确 $H_6$、精确重数表、精确 $h_{\rm Sh}$ 或 $h_0$。$\square$

## 8. 完整视图的精确熵最优值

**定理 8.1（已有精确摘要判据的熵应用）。** 在定义 1.1 的权限下，对任意角与已知步数 $n$，离散完整解码可见视图 $Y$ 的最小 Shannon 熵为

$$
\min_YH_{\rm Sh}(Y)=H_n(\theta).
\tag{8.1}
$$

此处允许可数视图及无穷熵，任意随机经典压缩，任意全 $H$ 终端 CPTP 解码器，以及仅平均后精确成功。对明确免费、取值于有限或标准 Borel 空间且独立于所有标签的共享种子 $S$，

$$
\min_YH_{\rm Sh}(Y\mid S)=H_n(\theta).
\tag{8.2}
$$

证明。先明确所复用的原卷定理 3.3、16.1 的假设及来源。给定完整视图值 $y$，压缩核为 $r(y\mid h)$，条件错误为 $F_h=\sqrt{w_{y,h}}Q_h$，其中 $w_{y,h}=r(y\mid h)/\sum_g r(y\mid g)$。平均恢复恒等式的 Choi 矩阵是嵌入 $\iota(X)=BXB^\dagger$ 的秩一矩阵。原卷以正性证明，每个正概率视图的条件恢复通道必须单独等于 $\iota$。若其全 $H$ 解码 Kraus 算子是 $d_\ell$，秩一 Choi 性再迫使

$$
d_\ell BF_h=c_{\ell h}B,\qquad
F_h^\dagger F_k
=\sum_\ell\overline{c_{\ell h}}c_{\ell k}I_3.
$$

后一式使用 $\sum_\ell d_\ell^\dagger d_\ell=I_5$ 与 $B^\dagger B=I_3$。这是原卷对应 Knill–Laflamme，quant-ph/9604034v1，Theorem 3.2、(19)–(20) 的全 qutrit 码及所有复交叉项。对正条件权重的 $h,k$，它要求 $Q_h^\dagger Q_k$ 为模一标量，故同一个正概率视图只能包含一个全 qutrit 射影类。这个必要性已覆盖任意全 $H$ 解码及平均成功，并非假设竞争解码器为酉。

因而 $C_n$ 是 $Y$ 的几乎处处函数。有限类变量与离散视图的链式法则给

$$
H(Y)=H(C_n)+H(Y\mid C_n)\ge H_n,
$$

对可数无穷熵也作为非负扩展熵成立。

为达到界，逐步积累真实前缀类，收到 $j$ 后更新 $[Q]\mapsto[V_jQ]$。这在射影类上良定义。原卷定理 4.1 的单射 $[Q]\mapsto[V_0^{n-t}Q]$ 将长 $t$ 的类注入终端 $\mathcal C_n$，所以已知确定时钟配固定时间表即可在每个前缀使用不超过 $m_n$ 个寄存值，无额外历史档案。终端变量恰为 $C_n$，其实际熵就是 $H_n$。

为每个终端类选一个实际代表 $Q_C$，用

$$
D_C=BQ_C^\dagger B^\dagger+(I_5-P_R),\qquad
\mathcal D_C=\operatorname{Ad}_{D_C}.
\tag{8.3}
$$

其在 $R$ 和 $R^\perp$ 的两个正交块均酉，故定义全 $H$ 通道。若 $Q_h=\lambda Q_C$，$D_CBQ_h=\lambda B$；对于任意 qutrit–参考态 $\rho$，

$$
(D_C\otimes I_Z)(BQ_h\otimes I_Z)\rho
(BQ_h\otimes I_Z)^\dagger(D_C\otimes I_Z)^\dagger
=(B\otimes I_Z)\rho(B\otimes I_Z)^\dagger.
$$

所以逐历史和平均均精确恢复，且没有后选择。

若免费种子 $S$ 与标签独立，原卷的秩一 Choi 正性先迫使几乎每个种子条件下精确恢复。独立性保留每条有限历史的条件概率 $2^{-n}$；有限条历史可取共同满测集。在其中每个种子值上同一类决定性给 $H(Y\mid S=s)\ge H_n$，积分即得 (8.2) 的下界。不使用种子的类积累器达到等号。相关可见种子须与其他载体联合计入完整视图。$\square$

**约定 8.2（可测视图与既有纠错接口的边界）。** 对标准 Borel 完整视图及可测解码通道，原卷定理 16.1 的结论是几乎处处可测确定 $C_n$。具体地，取各历史的条件视图测度 $\nu_h$、$\lambda=\sum_h\nu_h$ 及密度 $f_h=d\nu_h/d\lambda$；在一个共同满测集上 $\sum_hf_h=1$，且所有正密度的历史属于同类。分组密度 $f_C=\sum_{h:[Q_h]=C}f_h$ 的唯一正值类便给可测类函数。该论证积分非负 Choi 二次型，因此不要求连续点有正概率。本文没有对连续视图给微分熵下界或有限字母表结论。

原卷对应 Gregoratti–Werner，*Quantum Lost and Found*，quant-ph/0209025v1，§II.C.1 Proposition 2 的细标记条件是 $t_j=V_j/\sqrt2$、$t_j^\dagger t_j=I_3/2$。其系统在此对应 $R\cong\mathbb C^3$。*On quantum error-correction by classical feedback in discrete time*，quant-ph/0403092v1，Proposition 2、(10)–(12)、Figure 1(c) 的对应是早期纠正均取恒等的延迟纠正特例。这两个接口及原卷所引 *Minimal record dilations* 的 Theorem 2.2、Assumption 2.3 是已有单步原则及资源许可，不把原卷的全 $H$ Kraus 误作缩放酉，也不单靠细标记可纠正来许可粗化。式 (8.1) 是既有精确摘要判据与普通熵链式法则的应用，不单列为新的通用纠错原理。

由 (8.1)，最小完整离散记录熵率恰为 $h_{\rm Sh}$。原卷已有的有限字母表最优值仍为 $m_n$，固定二进制寄存器最优值仍为 $\lceil\log_2m_n\rceil$；它们的渐近率是 $h_0$。这些量与一般重数下的 Shannon 熵分别定义，不能相互等同。

## 9. 成本、来源归属与未解边界

**约定 9.1（资源分别计量）。** 所有实际方案仍处理 $n$ 次已测标签及 $n$ 次新环境准备。测量、取得与通信，校准、已知步数、确定时钟、静态控制说明或表格、精确矩阵和逆操作的精度、逆控制的实现均是另外的资源。原卷前缀实现可使用至多 $2nm_n$ 个转移表项及 $m_n$ 个终端逆控制；没有主张这些规模最优或有界。

凡随本次历史变化并对解码可见的时钟、程序、控制选择、种子、外部档案、工作缓冲都作为一个联合完整视图计量，不能移动载体来降低 (8.1)。丢弃的私有随机性已平均到压缩核；只有明确独立、单独免费供应的共享种子适用条件熵解释。

$\nu$ 的激活位和 $K_n$ 只存在于证明比较中。式 (6.2) 的 $\log_2(n+1)$ 是辅助长度不确定性的上界，没有给实际仪器增加单位字母、闲置步、测量、逆字母或恢复资源。实际正率结论始终针对恰好 $n$ 次原有公平取得。

Shannon 熵不是固定比特数，不是某个二元前缀码的精确平均码长，也不是全装置价格；若另行编码，整数码长、前缀条件及编码实现另计。精确条件逆仅恢复 $R$ 及未触动参考，并不提供任意五维输入的通道逆或未知输入的额外副本。

**约定 9.2（供应与推导的对应）。** 原卷定理 2.2、定义 3.1、式 (11.2) 供应实际全模型、受限公平性和同长普通群对应；原卷定理 12.2 供应实际群非虚可解性；§13 按约定 3.1 供应条件性 (ST2)。自由树根与非根权重估计、短字梯度转移、辅助惰性方差收缩及二项激活的完整移除在 §§4–6 内独立写明，不再引未证群引理、等长差群结论或谱引理。原卷 §§14–15 供应已知极大区域及全 qutrit 碰撞例；§§3–4、16 供应完整视图的必要性及可达类积累器。以上来源的外部文献仅以所供应精确接口使用，没有外部核验或优先权检索。

**定义 9.3（剩余问题及证据上限）。** 未由本文确定的是一般角的精确 Shannon 熵率、它与 $h_0$ 的更细关系、例外无理角的精确重数与类序列，以及奇数 $f(1)$ 区域的完整碰撞分类。没有宣称一般 $h_{\rm Sh}=h_0$。统一正下界已相对 (ST2) 得到，但未给出 $N(2)$ 的数值、最佳统一常数或寻找短自由生成元的算法。没有用关于角的连续性推断零率或正率；有界集合本身的零率与邻近非有界角的统一正下界可以同时成立。

近似恢复、后选择、适应仪器、中间反馈、保留量子环境或量子摘要、读取参考、不同输入任务、不同标签概率及其他实际仪器均超出这里的结论。本文不声称物理实现、有限精度实现、经验机器学习结论、全资源最优性或广泛原创性。所得是有限维明确模型内、依赖所供应源事实及条件性 Strong Tits 接口的未执行符号论证。

## 追加锚（本行以下为增补区）

## 10. 同一平均作用的读出、反馈与在线时域

**定义 10.1（扩展的恢复菜单）。** 对第 1 节的同一系统—环境作用，记 $W_n^{(\theta)}(\varepsilon)$ 为终端纠正菜单中的最小在线峰值状态数：每轮取得实际标签，只允许经典更新，末端可作任意全 $H$ CPTP 纠正，要求嵌入输入及全部未触碰参考的不折半钻石误差至多 $\varepsilon$。所有运行相关且仍影响未来处理的历史变量均计入状态；已知终点、静态表和精确控制说明另计。随机种子与平均成功的权限采用《[近似在线恢复记忆](AURIC_FIB_APPROXIMATE_ONLINE_RECOVERY_MEMORY.md)》定义 2.4 的合同，以下简称 AOM。

另定义反馈菜单：取得本轮实际标签后，允许立即施加依标签的系统酉，再进入下一轮。它增加了操作权限，不与前一个菜单混为同一优化问题。

**定理 10.2（读出合同的记忆标度与有限位时域）。** 第 1 节全部 $\theta$ 的未纠正平均系统作用均为 $\Phi_\circ^n$。在定义 10.1 的终端菜单下，

$$
W_n^{(0)}(0)\le6,\qquad
W_n^{(\pi/6)}(0)=2^n,
$$

$$
W_n^{(\pi/6)}(\varepsilon)
=\Theta_\varepsilon(n^{3/2})
\qquad(0<\varepsilon<1/4\text{ 固定},\ n\to\infty).
\tag{10.1}
$$

第三式复用 AOM 推论 27.1 的正谱隙及其实际前向比较条件；前两式不需要该谱输入。若记录至多有 $B$ 个定长位，置

$$
n_{\max}(B,\varepsilon)
=\sup\{n\ge0:W_n^{(\pi/6)}(\varepsilon)\le2^B\}.
$$

则在相同固定正误差与谱条件下，

$$
n_{\max}(B,\varepsilon)
=\Theta_\varepsilon(2^{2B/3})\qquad(B\to\infty).
\tag{10.2}
$$

在反馈菜单中，每个固定角均有不需累计历史或终点计数的常数状态控制，能在每个有限完成周期后精确恢复任意嵌入输入及参考关联。

证明。全复输入上的 Kraus 混合恒等式已在第 1 节证明，故无纠正平均作用相同，包括任意参考。$\theta=0$ 时只保留置换积 $P\in S_3$，新标签 $j$ 令 $P\mapsto U_jP$，末端作 $BP^\dagger B^\dagger+(I-P_R)$；至多六个状态即可。第 7 节与第 8 节的精确类判据、实际字单射给 $\theta=\pi/6$ 的精确宽度 $2^n$，也见《[近似终端记录熵](AURIC_FIB_APPROXIMATE_TERMINAL_RECORD_ENTROPY.md)》定理 9.2。AOM 推论 27.1 给 (10.1) 的固定正误差匹配界，不在此重证其谱和因果合并估计。

具体存在 $c_\varepsilon,C_\varepsilon>0$ 及 $n_0$，使 $n\ge n_0$ 时 $c_\varepsilon n^{3/2}\le W_n^{(\pi/6)}(\varepsilon)\le C_\varepsilon n^{3/2}$。下界使任何可行大时域满足 $n\le c_\varepsilon^{-2/3}2^{2B/3}$；取足够小的常数倍 $2^{2B/3}$ 并向下取整，上界保证该时域可行。有限个 $n<n_0$ 不影响渐近式，得到 (10.2)。这个反演不需要先假定 $W_n$ 单调。

反馈分支是标准环境辅助纠错的本模型实例。第 1 节给 $A_j(\theta)B=BV_j(\theta)/\sqrt2$ 且 $V_j$ 酉。立即施加

$$
D_j=BV_j(\theta)^\dagger B^\dagger+(I-P_R)
$$

是合法全空间酉，并且 $D_jA_j(\theta)B=B/\sqrt2$。故每个校正分支在任意参考上恰是 $\iota\otimes\operatorname{id}$ 的一半。迭代后每条历史给权重 $2^{-n}$ 的原输入，总平均仍为原输入。当前标签至多一位，加上固定采集、校正与返回阶段只需常数状态；这个无限循环无需保存 $n$。若要求自行在指定第 $n$ 轮停止，停止计数是额外任务。环境辅助纠错的先例与条件对应见第 8 节所引 Gregoratti–Werner，特别是 *On quantum error-correction by classical feedback in discrete time*，[quant-ph/0403092](https://arxiv.org/abs/quant-ph/0403092)，Proposition 2。$\square$

**命题 10.3（标签熵与输入信息的不同用途）。** 在上述每个固定读出角下，让有限经典变量 $X$ 标记任意一族嵌入输入态，允许各态与不受触碰的参考纠缠。则实际未纠正历史满足

$$
H(\mathsf H_n)=n,\qquad I(X;\mathsf H_n)=0.
$$

但这不使 (10.1) 的纠正记录无用。

证明。第 1 节已证明每个输入、每个历史前缀之后的实际标签均条件公平，故对每个 $x$ 有 $P(\mathsf H_n=h\mid X=x)=2^{-n}$，给出独立性和熵。这个历史指定输入所经历的 $Q_h$；已知它便可逆转，纠正关系与辨认输入标签是不同任务。该独立性是公平分支的直接应用，不是额外的通用量子信息定理。$\square$

**约定 10.4（组合归属与资源）。** 本节的 repo-derived 综合为同一未纠正平均作用下的不同在线时域与反馈合同，匹配率本身归于 AOM，精确类归于本卷第 7—8 节，反馈原理归于所引文献。状态数 $n^{3/2}$ 对应 $(3/2)\log_2n+O_\varepsilon(1)$ 位，不是 $n^{3/2}$ 位；反馈改变有效编码演化为恒等，不保持“反馈后的作用仍是 $\Phi_\circ^n$”这一不存在的等式。常数持久状态不减少实际轮数、新环境准备、测量、门合成、标签复位或其物理成本。式 (10.2) 只描述既定合同的恢复时域，不提供秒数或完全自治的校准与停止资源界。

## 追加锚（本行以下为增补区）
