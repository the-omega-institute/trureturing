# 纯态 ECQC 的素数维反例族

## §0. 记号与引用结果

全文使用自然对数，约定 $0\log 0=0$。有限联合分布 $P$ 的经典互信息为

$$
I(P)=H(P_A)+H(P_B)-H(P),\qquad H(q)=-\sum_x q(x)\log q(x).
$$

密度矩阵 $\rho_{AB}$ 的量子互信息为

$$
I(A:B)_\rho=S(\rho_A)+S(\rho_B)-S(\rho_{AB}),\qquad
S(\rho)=-\operatorname{tr}(\rho\log\rho),
$$

其中 $\rho_A=\operatorname{tr}_B\rho_{AB}$、$\rho_B=\operatorname{tr}_A\rho_{AB}$。

Iqbal，*On the CQC Conjecture: A sufficient condition and an extension*，
[arXiv:2509.08286v2](https://arxiv.org/abs/2509.08286v2)，ECQC 猜想要求在素数维 $p$ 的完整互无偏基族 $\mathcal M$ 上满足

$$
\min_{S\subseteq\mathcal M,\ |S|=p}\sum_{M\in S}I(M^A:M^B)\leq I(A:B).
$$

此断言以 Conjecture 2.1 引用；所引 v2 全文将同一断言编号为 Conjecture 3.1。其纯态限制只允许 $\rho_{AB}=|\psi\rangle\langle\psi|$。

对奇素数 $p$，置 $\mathbb F_p=\mathbb Z/p\mathbb Z$、$\omega=\exp(2\pi i/p)$，以及 $\mathcal J_p=\{\infty\}\sqcup\mathbb F_p$。计算基的列为 $m_{\infty,b}(x)=\mathbf1_{x=b}$；对 $a,b,x\in\mathbb F_p$，令

$$
m_{a,b}(x)=v_{a,b}(x)=\frac{\omega^{ax^2+bx}}{\sqrt p}.
$$

这些 $p+1$ 个基构成完整的 Clifford 互无偏基族：每个基正交归一，不同基任意两列的内积模平方均为 $1/p$。这是 Ivanović，*Geometrical description of quantal state determination*，1981，
[DOI:10.1088/0305-4470/14/12/019](https://doi.org/10.1088/0305-4470/14/12/019)，与 Wootters–Fields，*Optimal state-determination by mutually unbiased measurements*，1989，
[DOI:10.1016/0003-4916(89)90322-9](https://doi.org/10.1016/0003-4916(89)90322-9) 的构造。

双方使用同一个列基。对归一化向量 $\psi\in\mathbb C^{\mathbb F_p\times\mathbb F_p}$，其联合分布定义为

$$
P_i^\psi(b,c)=\left|\sum_{x,y\in\mathbb F_p}
\overline{m_{i,b}(x)}\,\overline{m_{i,c}(y)}\,\psi(x,y)\right|^2,
\qquad i\in\mathcal J_p.
$$

纯态 ECQC 断言记作 $\mathcal C_p$：对所有满足 $\sum_{x,y}|\psi(x,y)|^2=1$ 的 $\psi$，均有

$$
\inf\left\{\sum_{i\in S}I(P_i^\psi):
S\subseteq\mathcal J_p,\ |S|=p\right\}
\leq I(A:B)_{|\psi\rangle\langle\psi|}.
$$

这里候选集合有限且非空，故下确界就是最小值。

Appleby，*Properties of the extended Clifford group with applications to SIC-POVMs and MUBs*，
[arXiv:0909.5233](https://arxiv.org/abs/0909.5233)，式 (76)、(77)、(219) 给出扩展 Clifford 群的幺正及反幺正表示和对 Wootters–Fields 基的作用。若 $u^2=-1$，标量反辛矩阵 $uI$ 固定每个基的标签并置换其列；对应反幺正算子为置换 $|x\rangle\mapsto|ux\rangle$ 与标准复共轭的复合，允许一个全局相位。这一基对称性是引用的文献中间结果。

仓内结果[《Pure-state ECQC fails in dimension five》](https://github.com/the-omega-institute/trureturing/blob/7670255ef3464286b2f7086c075743a5e749f6ef/Blueprint/D5/S3/Quantum/Information/PureStateECQCRefutation.md) 给出 $p=5$、$u=2$ 的纯态反例，其差额为 $3\log 5$。下面给出素数维家族及其精确差额。

## §1. 素数维反例族

**定理 1.** 对每个满足 $p\equiv1\pmod4$ 的素数 $p$，存在 $u\in\mathbb F_p$ 满足 $u^2=-1$。对每个这样的 $u$，向量

$$
|\psi_u\rangle=\frac1{\sqrt p}\sum_{x\in\mathbb F_p}|x\rangle\otimes|ux\rangle,
\qquad
\psi_u(x,y)=\begin{cases}p^{-1/2}&y=ux,\\0&y\ne ux\end{cases}
$$

归一化，并且对每个 $i\in\mathcal J_p$ 及每个 $b,c\in\mathbb F_p$ 都有

$$
P_i^{\psi_u}(b,c)=\frac1p\mathbf1_{c=ub}.
$$

因此每个测量的两个边缘分布都均匀，且

$$
I(P_i^{\psi_u})=\log p\quad(i\in\mathcal J_p),\qquad
I(A:B)_{|\psi_u\rangle\langle\psi_u|}=2\log p.
$$

特别地，

$$
\min_{S\subseteq\mathcal J_p,\ |S|=p}\sum_{i\in S}I(P_i^{\psi_u})
-I(A:B)_{|\psi_u\rangle\langle\psi_u|}
=(p-2)\log p>0,
$$

故 $\neg\mathcal C_p$：纯态 ECQC 在每个这样的素数维都失败。

证明。素数 $p\equiv1\pmod4$ 时，$-1$ 是 $\mathbb F_p$ 中的平方。固定任一平方根 $u$，则 $u\ne0$、$u^{-1}=-u$，所以 $x\mapsto ux$ 是双射。向量有 $p$ 个模平方为 $1/p$ 的非零分量，故其范数平方为一。

Appleby 的扩展 Clifford 作用公式所给的逐基对称性，可在这里的列记号下写成 $U_u\overline{v_{a,b}}=v_{a,ub}$，其中 $U_u|x\rangle=|ux\rangle$；它表明 $(1\otimes U_u)|\Psi^+\rangle$ 在每个相同基中具有置换后的完全关联。这一步是上述文献结果的具体应用。以下计算同时固定关联图及其概率。

计算基的振幅直接等于 $p^{-1/2}\mathbf1_{c=ub}$。二次相位基 $a\in\mathbb F_p$ 的振幅则为

$$
\begin{aligned}
\langle v_{a,b}|\otimes\langle v_{a,c}|\psi_u\rangle
&=p^{-3/2}\sum_{x\in\mathbb F_p}
\omega^{-a(1+u^2)x^2-(b+uc)x}\\
&=p^{-3/2}\sum_{x\in\mathbb F_p}\omega^{-(b+uc)x}\\
&=p^{-1/2}\mathbf1_{b+uc=0}.
\end{aligned}
$$

第二个等号使用 $1+u^2=0$。最后一个等号使用本原 $p$ 次单位根的几何和：系数为零时和为 $p$，系数非零时和为零。由于 $u^2=-1$，条件 $b+uc=0$ 等价于 $c=ub$。取模平方即得所有基上的联合分布公式。

关联图是双射图，故两个边缘分布均为 $1/p$，联合分布恰有 $p$ 个非零项，每项为 $1/p$。两个边缘熵及联合熵均为 $\log p$，经典互信息因此等于 $\log p$。

对 $|\psi_u\rangle\langle\psi_u|$ 作两种偏迹均得到 $I_p/p$：前者利用 $x\mapsto ux$ 的单射性消去非对角项，后者利用其双射性得到每个对角项 $1/p$。两者的熵均为 $\log p$；全局密度矩阵秩一，其熵为零。因此量子互信息为 $2\log p$。

任取 $p$ 个测量，信息和都为 $p\log p$，所以最小值也为 $p\log p$。素数条件和 $p\equiv1\pmod4$ 给出 $p\geq5$，故 $(p-2)\log p>0$。这给出 $\mathcal C_p$ 的反例。$\square$

## 追加锚（本行以下为增补区）
