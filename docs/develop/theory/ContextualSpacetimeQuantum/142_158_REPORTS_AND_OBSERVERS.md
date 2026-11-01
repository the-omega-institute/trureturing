# 情境时空算术的量子扩展：报告历史、隐状态与有限观察者

[总目](../CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) · [前卷](121_141_COHERENT_PREFIXES.md) · [续卷](159_179_LONG_HORIZON_PREDICTION.md)


<a id="entry-632"></a>

## 追加锚（本行以下为增补区）

<a id="section-142"></a>

## 142. 任意有限内部长度的总奇偶一位与条件端点纠缠的精确范围

**命题 142.1（固定加减基总奇偶记录的全长度分类）。** 取命题 130.1 的纯边界生成器，令
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
0<\alpha<1,\qquad \alpha^2+\alpha=1,\qquad B=M=\mathbb C^2,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1),
$$
$$
\Xi_0=m_0,\qquad
\Xi_{n+1}=(I_{B^{\otimes n}}\otimes T)\Xi_n.
$$
各空间均取正交标准基。对任意有限整数 $g\ge1$，在任何测量之前恰好发出 $g+2$ 个输出，次序为
$$
B_L\otimes B_1\otimes\cdots\otimes B_g\otimes B_R\otimes M.
$$
$L,R$ 分别是第一位和最后一位已发出的 qubit，左端点之前没有被忽略的前缀；端点空间始终是完整的 $B_L\otimes B_R=\mathbb C^2\otimes\mathbb C^2$。生成过程中不读取、测量或重置记忆，最终记忆取偏迹且不可访问。每个内部输出在同一事先固定的局部正交基
$$
|\eta_r\rangle=\frac{|0\rangle+(-1)^r|1\rangle}{\sqrt2}
\quad(r=0,1)
$$
中测量一次。全部测量完成、结果已成为经典记录后，仅保留总奇偶位
$$
b=\bigoplus_{k=1}^g r_k\in\{0,1\}.
$$
这一位没有附加翻转通道。结果不用于反馈、后续选基或端点操作；测后的内部系统、原始记录及奇偶记录的其他副本均不可访问，不允许环境重新耦合或记录的相干重组。

以 $\operatorname{adj}$ 表示共轭转置，$\operatorname{outer}(u,v)=u\operatorname{adj}(v)$，$\operatorname{outer}(u)=\operatorname{outer}(u,u)$。对 $r=(r_1,\ldots,r_g)$，定义实际分支
$$
\chi_r=(I_{B_L}\otimes\langle\eta_{r_1}|\otimes\cdots\otimes
\langle\eta_{r_g}|\otimes I_{B_R}\otimes I_M)\Xi_{g+2},
\qquad Q_r=\operatorname{Tr}_M\operatorname{outer}(\chi_r),
$$
$$
Q_{g,b}=\sum_{r:\,\bigoplus_k r_k=b}Q_r,\qquad
q_{g,b}=\operatorname{Tr}Q_{g,b}.
$$
可分密度采用命题 132.1 的有限凸乘积密度和定义，纠缠指不可分；右偏转置约定为
$$
\operatorname{PT}_R(|ij\rangle\langle kl|)=|il\rangle\langle kj|.
$$
则对所有有限整数 $g\ge1$ 及 $b\in\{0,1\}$，
$$
q_{g,b}=\frac12+(-1)^b\alpha^{g+2},\qquad 0<q_{g,b}<1.
$$
因此 $\rho_{g,b}=Q_{g,b}/q_{g,b}$ 总有定义，且
$$
\rho_{g,b}\text{ 纠缠}
\quad\Longleftrightarrow\quad
\operatorname{PT}_R(\rho_{g,b})\not\ge0
\quad\Longleftrightarrow\quad g\in\{1,2\},
$$
$$
\rho_{g,b}\text{ 可分}
\quad\Longleftrightarrow\quad
\operatorname{PT}_R(\rho_{g,b})>0
\quad\Longleftrightarrow\quad g\ge3.
$$
这里 $>0$ 指严格正定。两个事件之和满足
$$
Q_{g,0}+Q_{g,1}
=\operatorname{Tr}_{B_1,\ldots,B_g,M}\operatorname{outer}(\Xi_{g+2})
=\theta^{P_0}_{0;1,g,1},\qquad P_0=\operatorname{outer}(m_0),
$$
是命题 133.1 的可分无条件端点密度；各 $\rho_{g,b}$ 则是按总奇偶位条件化的密度。本命题的量词仅涉及上述固定基与总奇偶函数。

证明。写 $P_j=\operatorname{outer}(m_j)$、$E_{ij}=|i\rangle\langle j|$。命题 131.1 的矩阵单位展开及两个通道为
$$
T A\operatorname{adj}(T)
=\sum_{i,j=0}^1 A_{ij}E_{ij}\otimes\operatorname{outer}(m_i,m_j),
\qquad
\mathcal M(A)=A_{00}P_0+A_{11}P_1,
$$
$$
\Gamma_1(A)=\operatorname{Tr}_M(T A\operatorname{adj}(T))
=\begin{pmatrix}A_{00}&sA_{01}\\sA_{10}&A_{11}\end{pmatrix}.
$$
令
$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
\mathcal L(A)=\operatorname{Tr}_B\bigl[(X\otimes I_M)T A\operatorname{adj}(T)\bigr],
$$
$$
U=\operatorname{outer}(m_0,m_1)=\begin{pmatrix}s&0\\\alpha&0\end{pmatrix},
\qquad V=\operatorname{adj}(U).
$$
上面的展开给出复线性映射
$$
\mathcal L(A)=A_{01}U+A_{10}V,
\qquad
\mathcal L(E_{00})=\mathcal L(E_{11})=0,\quad
\mathcal L(E_{01})=U,\quad\mathcal L(E_{10})=V,
$$
$$
\mathcal L(U)=\alpha V,\qquad \mathcal L(V)=\alpha U.
$$
从 $g=1$ 起逐次作用便得，对任意复矩阵 $A$，
$$
\mathcal L^g(A)=
\begin{cases}
\alpha^{g-1}(A_{01}U+A_{10}V),&g\text{ 为奇数},\\
\alpha^{g-1}(A_{01}V+A_{10}U),&g\text{ 为偶数}.
\end{cases}
$$
特别地，$\mathcal L^{g+2}=\alpha^2\mathcal L^g$ 对 $g\ge1$ 成立。

单个实际测量结果对记忆的 Kraus 算子及分支映射为
$$
K_r=(\langle\eta_r|\otimes I_M)T
=\frac{m_0\langle0|+(-1)^r m_1\langle1|}{\sqrt2},
\qquad
\Phi_r(A)=K_rA\operatorname{adj}(K_r)
=\frac{\mathcal M(A)+(-1)^r\mathcal L(A)}2.
$$
已发出因子上的测量与其后只作用于记忆及新输出的等距交换，故先发出全部输出再测量的协议，仍可按位置次序计算为 $\Phi_{r_g}\circ\cdots\circ\Phi_{r_1}$。保持这个复合次序并分配有限和，得到
$$
\sum_{r\in\{0,1\}^g}\Phi_{r_g}\circ\cdots\circ\Phi_{r_1}
=(\Phi_0+\Phi_1)^g=\mathcal M^g,
$$
$$
\sum_{r\in\{0,1\}^g}(-1)^{\sum_k r_k}
\Phi_{r_g}\circ\cdots\circ\Phi_{r_1}
=(\Phi_0-\Phi_1)^g=\mathcal L^g.
$$
这里没有交换 $\mathcal M$ 与 $\mathcal L$。因而奇偶事件的实际记忆映射为
$$
\mathcal S_{g,b}
:=\sum_{r:\,\bigoplus_k r_k=b}\Phi_{r_g}\circ\cdots\circ\Phi_{r_1}
=\frac{\mathcal M^g+(-1)^b\mathcal L^g}{2}.
$$
相应的内部事件效应是
$$
\sum_{r:\,\bigoplus_k r_k=b}\bigotimes_{k=1}^g\operatorname{outer}(\eta_{r_k})
=\frac{I_{B^{\otimes g}}+(-1)^bX^{\otimes g}}2.
$$
此效应来自完整局部仪器结果的经典合并，事件算子中没有不同原始记录之间的振幅交叉项。

令 $\Omega=T P_0\operatorname{adj}(T)$ 为首个已发出端点与记忆的联合密度。再发出右端点并忽略最终记忆给出
$$
Q_{g,b}
=\bigl(\operatorname{Id}_{B_L}\otimes(\Gamma_1\circ\mathcal S_{g,b})\bigr)(\Omega)\ge0.
$$
这里最后的 $\Gamma_1$ 将活动记忆转为已发出的右端点。与命题 137.1 的系数公式对照，置
$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
D_r=\frac1{\sqrt2}\operatorname{diag}(1,(-1)^r),\qquad
C_r=s^{g+3}JD_{r_1}J\cdots D_{r_g}J,
$$
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1C_{ij}|i\rangle_L\otimes|j\rangle_R.
$$
该命题的两记忆列公式恰给
$$
Q_r=\operatorname{outer}(\operatorname{vec}_{LR}(C_r))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(C_rE_{00})).
$$
因此上述通道式就是陈述中的 $\sum_{r:\,\bigoplus_k r_k=b}Q_r$，保留了两条最终记忆列及其实际 Born 权重。其正性来自这些实际分支的正算子和。

对左端点取迹，有 $\operatorname{Tr}_{B_L}\Omega=\mathcal M(P_0)$；该矩阵的两个非对角元均为 $\alpha^2s$。由 $\operatorname{Tr}U=\operatorname{Tr}V=s$，
$$
\operatorname{Tr}\mathcal L^g(\mathcal M(P_0))
=2\alpha^{g-1}\alpha^2s^2=2\alpha^{g+2}.
$$
$\mathcal M$ 与 $\Gamma_1$ 保迹，故
$$
q_{g,b}=\frac12\left(1+(-1)^b\,2\alpha^{g+2}\right).
$$
由 $\alpha^3=\sqrt5-2<1/2$ 及 $0<\alpha^{g+2}\le\alpha^3$，两个概率均严格位于 $0$ 与 $1$ 之间。求和消去带符号项，所得 $\theta^{P_0}_{0;1,g,1}$ 由命题 133.1 可分。这一步求得的是无条件密度。

下面求条件态的偏转置。定义
$$
z_n=\frac{1-(-\alpha^2)^n}{1+\alpha^2}\quad(n\ge0),\qquad
z_0=0,\quad z_1=1,\quad z_{n+1}=1-\alpha^2z_n.
$$
命题 131.1 写 $\sigma_n=\mathcal M^n(P_0)=(1-p_n)P_0+p_nP_1$，其中 $p_n=\alpha^2z_n$，所以 $1-p_n=z_{n+1}$。由于 $\mathcal M(E_{00})=P_0$，对 $g\ge1$ 有
$$
\mathcal M^g(E_{00})=\sigma_{g-1}=z_gP_0+(1-z_g)P_1.
$$
又 $\mathcal M(E_{11})=P_1$、$\mathcal M(P_1)=P_0$，故 $g=1$ 时直接用 $z_0=0$，$g\ge2$ 时用 $\sigma_{g-2}$，统一得到
$$
\mathcal M^g(E_{11})=z_{g-1}P_0+(1-z_{g-1})P_1.
$$
置
$$
H(z)=\begin{pmatrix}1-\alpha^2z&\alpha^2z\\\alpha^2z&\alpha^2z\end{pmatrix},\qquad
h=\begin{pmatrix}1\\\alpha\end{pmatrix},\quad e=\begin{pmatrix}1\\0\end{pmatrix},
\qquad c_g=s\alpha^{g-1},
$$
$$
D=\alpha\begin{pmatrix}1&s\\1&0\end{pmatrix},\qquad
\phi=|00\rangle+|11\rangle.
$$
实际首步满足 $Tm_0=\operatorname{vec}_{LM}(D)=(D\otimes I_M)\phi$，且 $\det D=-\alpha^2s\ne0$。对四个矩阵单位逐一应用刚才的公式，得到
$$
\begin{aligned}
\Gamma_1\mathcal M^g(E_{00})&=H(z_g),&
\Gamma_1\mathcal M^g(E_{11})&=H(z_{g-1}),\\
\Gamma_1\mathcal M^g(E_{01})&=0,&
\Gamma_1\mathcal M^g(E_{10})&=0,\\
\Gamma_1\mathcal L^g(E_{00})&=0,&
\Gamma_1\mathcal L^g(E_{11})&=0,\\
\Gamma_1\mathcal L^g(E_{01})&=c_gW_g,&
\Gamma_1\mathcal L^g(E_{10})&=c_g\operatorname{adj}(W_g),
\end{aligned}
\qquad
W_g=\begin{cases}he^{\mathsf T},&g\text{ 为奇数},\\eh^{\mathsf T},&g\text{ 为偶数}.
\end{cases}
$$
这里 $\Gamma_1(U)=s he^{\mathsf T}$、$\Gamma_1(V)=s eh^{\mathsf T}$。将 $\operatorname{outer}(\phi)=\sum_{i,j}E_{ij}\otimes E_{ij}$ 展开，便得
$$
2Q_{g,b}=(D\otimes I_{B_R})\mathcal K_{g,b}\operatorname{adj}(D\otimes I_{B_R}),
$$
$$
\mathcal K_{g,b}=
\begin{pmatrix}
H(z_g)&(-1)^b c_gW_g\\
(-1)^b c_g\operatorname{adj}(W_g)&H(z_{g-1})
\end{pmatrix}.
$$
此合同只是矩阵恒等式，协议中没有执行 $D$ 或其逆作为局部操作。

右偏转置将每个二阶块转置，故保持两个实对称对角块，并反转非对角秩一块的方向。令 $Z=\operatorname{diag}(1,-1)$，则
$$
\mathcal K_{g,1}=(Z\otimes I)\mathcal K_{g,0}(Z\otimes I),\qquad
\operatorname{PT}_R(\mathcal K_{g,1})
=(Z\otimes I)\operatorname{PT}_R(\mathcal K_{g,0})(Z\otimes I).
$$
此外，偏转置与左因子合同交换，因而
$$
\operatorname{PT}_R(\rho_{g,b})
=\frac1{2q_{g,b}}(D\otimes I)
\operatorname{PT}_R(\mathcal K_{g,b})\operatorname{adj}(D\otimes I).
$$
可逆合同及正数缩放保持 Hermitian 矩阵的正、负、零惯性指数，所以两种 $b$ 有相同的 PPT 或 NPT 分类；这一论证不要求两个实际归一化密度有相同的谱。

当 $g=1$ 时，$z_1=1$、$z_0=0$，$\operatorname{PT}_R(\mathcal K_{1,b})$ 在 $00,11$ 指标上的主子式为
$$
\det\begin{pmatrix}\alpha&(-1)^b s\alpha\\(-1)^b s\alpha&0\end{pmatrix}
=-\alpha^3<0.
$$
所以两个分支均为 NPT。

当 $g\ge2$ 时，递推使所用的两个 $z$ 均在 $(0,1]$ 内。令
$$
d(z)=1-2\alpha^2z.
$$
由 $2\alpha^2<1$ 得 $d(z)>0$，且
$$
\det H(z)=\alpha^2z\,d(z)>0,\qquad H(z)>0.
$$
二阶逆矩阵给出
$$
H(z)^{-1}=\frac1{\alpha^2z\,d(z)}
\begin{pmatrix}\alpha^2z&-\alpha^2z\\-\alpha^2z&1-\alpha^2z\end{pmatrix},
$$
$$
e^{\mathsf T}H(z)^{-1}e=\frac1{d(z)},\qquad
h^{\mathsf T}H(z)^{-1}h=\frac{1-\alpha z}{z\,d(z)}.
$$
后一式的分子在约去 $\alpha^2$ 前为
$$
\alpha^2z-2\alpha^3z+\alpha^2(1-\alpha^2z)
=\alpha^2(1-\alpha z).
$$

为判定整个偏转置，写 $A=H(z_g)$、$B=H(z_{g-1})$，其右上块在奇数 $g$ 时为 $(-1)^b c_g e h^{\mathsf T}$，在偶数 $g$ 时为 $(-1)^b c_g h e^{\mathsf T}$。一般地，$A>0$ 时有可逆合同
$$
\begin{pmatrix}I&0\\-R^\dagger A^{-1}&I\end{pmatrix}
\begin{pmatrix}A&R\\R^\dagger&B\end{pmatrix}
\begin{pmatrix}I&-A^{-1}R\\0&I\end{pmatrix}
=\begin{pmatrix}A&0\\0&B-R^\dagger A^{-1}R\end{pmatrix}.
$$
若 $R=\lambda uv^\dagger$ 且 $B>0$，下块再经 $B^{-1/2}$ 合同成为
$$
I-ww^\dagger,\qquad
w=|\lambda|\sqrt{u^\dagger A^{-1}u}\,B^{-1/2}v.
$$
在 $w$ 的正交补上此矩阵为恒等，在其方向上的特征值为 $1-\|w\|^2$；$w=0$ 时它就是恒等。因此整个分块矩阵正半定当且仅当
$$
|\lambda|^2(u^\dagger A^{-1}u)(v^\dagger B^{-1}v)\le1,
$$
严格小于时整个矩阵正定，严格大于时存在负二次型。代入上述两个方向及逆二次型，定义
$$
z_*=
\begin{cases}z_{g-1},&g\text{ 为奇数},\\z_g,&g\text{ 为偶数},\end{cases}
\qquad
F_g=z_*d(z_g)d(z_{g-1})-c_g^2(1-\alpha z_*),
$$
便得
$$
\operatorname{PT}_R(\mathcal K_{g,b})\ge0\quad\Longleftrightarrow\quad F_g\ge0,
\qquad
\operatorname{PT}_R(\mathcal K_{g,b})>0\quad\Longleftrightarrow\quad F_g>0.
$$
这使用了两个正定对角块及秩一 Schur 补，而非一般矩阵的行列式符号判据。特别地，$g=2$ 时 $z_2=\alpha$、$z_1=1$、$c_2^2=\alpha^3$、$d(1)=\alpha^3$，故
$$
F_2=\alpha^4(1-2\alpha^3)-\alpha^3(1-\alpha^2)
=-2\alpha^7<0.
$$
这与命题 140.1（C）的两内部位 NPT 结论一致。

最后给出对所有 $g\ge3$ 的统一严格界。对每个 $n\ge2$，有
$$
\alpha\le z_n\le2\alpha^2.
$$
事实上 $z_2=\alpha$，且 $\alpha\le2\alpha^2$ 由 $\alpha>1/2$ 得到。递减映射 $z\mapsto1-\alpha^2z$ 在该区间的最大值为
$$
1-\alpha^3=2\alpha^2,
$$
最小值满足
$$
1-2\alpha^4-\alpha=\alpha^2(1-2\alpha^2)>0.
$$
它因此将该区间映入自身，归纳即得所述全 $n$ 界。又由 $\alpha^2+\alpha=1$ 化简可得精确恒等式
$$
1-4\alpha^4=\alpha^2+\alpha^7.
$$
所以对 $g\ge3$，两个 $z_g,z_{g-1}$ 均满足
$$
d(z)\ge1-4\alpha^4=\alpha^2+\alpha^7>\alpha^2.
$$
同时
$$
z_*\ge\alpha,\qquad
c_g^2=\alpha^{2g-1}\le\alpha^5,\qquad
0<1-\alpha z_*\le1-\alpha^2=\alpha.
$$
代入 Schur 标量得到
$$
F_g>\alpha\cdot\alpha^2\cdot\alpha^2-\alpha^5\cdot\alpha
=\alpha^5-\alpha^6=\alpha^7>0
\qquad(g\ge3).
$$
这直接涵盖每个有限整数 $g\ge3$，从而两个实际条件密度的整个右偏转置均严格正定。

可分密度的右偏转置必为正半定，因为有限凸乘积和逐项变为正矩阵与其正转置的张量积。因此 $g=1,2$ 的 NPT 排除可分性。对 $g\ge3$，$\rho_{g,b}$ 已由实际分支和及正概率归一化为完整 $\mathbb C^2\otimes\mathbb C^2$ 上的密度，适用命题 141.1 所引并使用的二维 PPT 充分性：M. Horodecki、P. Horodecki、R. Horodecki，*Separability of Mixed States: Necessary and Sufficient Conditions*，[arXiv:quant-ph/9605038v2，定理 3，PDF 第 8 页](https://arxiv.org/pdf/quant-ph/9605038v2)，Physics Letters A 223，1–8（1996），[DOI:10.1016/S0375-9601(96)00706-2](https://doi.org/10.1016/S0375-9601(96)00706-2)。该文可分态闭包定义与本卷有限凸和定义的一致性已在命题 141.1 证明，故这里得到的正是陈述中的可分性。命题 137.1 对所有完整加减基记录给出的纠缠性，并不使同一奇偶事件内的经典混合仍然纠缠；以上实际事件算子与统一 Schur 界给出了该混合的精确范围。证毕。

<a id="entry-634"></a>

## 追加锚（本行以下为增补区）

<a id="section-143"></a>

## 143. 确定性一位记录的两内部位唯一性与三内部位全划分障碍

**命题 143.1（全部布尔二分下的条件端点纠缠）。** 沿用命题 130.1、137.1 的纯边界生成器，取
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
t=1+\alpha,\qquad t^2=t+1,\qquad 1<t<2,
$$
$$
B=M=\mathbb C^2,\qquad
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,
\qquad T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1),
$$
$$
\Xi_0=m_0,\qquad
\Xi_{n+1}=(I_{B^{\otimes n}}\otimes T)\Xi_n.
$$
各空间取正交标准基。对有限整数 $g\ge1$，先恰好发出 $g+2$ 个输出，次序为
$$
B_L\otimes B_1\otimes\cdots\otimes B_g\otimes B_R\otimes M.
$$
$L,R$ 分别为第一个和最后一个已发出的单量子比特因子，端点的联合空间始终是完整的 $B_L\otimes B_R=\mathbb C^2\otimes\mathbb C^2$；左端点之前没有被忽略的前缀。生成过程中不读取、测量或重置记忆，最终记忆取偏迹且不可访问。每个内部输出在事先固定的加减基
$$
|\eta_{r_k}\rangle=\frac{|0\rangle+(-1)^{r_k}|1\rangle}{\sqrt2}
\quad(r_k\in\{0,1\})
$$
中测量一次。全部测量完成、结果成为经典记录 $r=(r_1,\ldots,r_g)$ 后，仅保留事先指定的确定性满射
$$
f:\{0,1\}^g\longrightarrow\{0,1\}
$$
的值，不附加随机通道。测后的内部系统、原始记录及报告的其他副本均不可访问；结果不用于反馈、后续选基或端点操作，不允许环境重新耦合或记录的相干重组。

以 $\operatorname{adj}$ 表示共轭转置，$\operatorname{outer}(v)=v\operatorname{adj}(v)$，并取命题 137.1 的逐行向量化约定
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1 C_{ij}|i\rangle_L\otimes|j\rangle_R,
\qquad 00,01,10,11\text{ 为坐标次序}.
$$
记
$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
Z=\operatorname{diag}(1,-1),\qquad E_0=\operatorname{diag}(1,0),\qquad
\kappa_g=s^{g+3}2^{-g/2}>0,
$$
$$
C_r=\kappa_g JZ^{r_1}J\cdots Z^{r_g}J,
\qquad
Q_r=\operatorname{outer}(\operatorname{vec}_{LR}(C_r))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(C_rE_0)),
\qquad q_r=\operatorname{Tr}Q_r.
$$
这里 $Q_r$ 正是实际测量分支对最终记忆取偏迹所得的算子，两个外积保留两条未读记忆列及其原权重。对非空记录集 $S\subseteq\{0,1\}^g$，先定义
$$
Q_S=\sum_{r\in S}Q_r,\qquad q_S=\operatorname{Tr}Q_S=\sum_{r\in S}q_r,
$$
再在 $q_S>0$ 时定义 $\theta_S=Q_S/q_S$。可分性采用命题 132.1 的有限凸乘积密度和定义，纠缠指不可分；右偏转置为
$$
\operatorname{PT}_R(|ij\rangle\langle kl|)=|il\rangle\langle kj|.
$$
右偏转置正半定称为 PPT，否则称为 NPT。两个报告的记录集为 $S_b=f^{-1}(b)$。将 $f$ 与 $1-f$ 视为同一个无标号二分，则有以下结论。

对所有有限 $g\ge1$，每个非空 $S$ 都有 $q_S>0$，且
$$
\theta_S=\sum_{r\in S}\frac{q_r}{q_S}\theta_{\{r\}},\qquad
q_{S_0}+q_{S_1}=1.
$$
集合的基数不作为其概率。当 $g=1$ 时，唯一二分 $\{0\}\mid\{1\}$ 的两个报告均 NPT。当 $g=2$ 时，全部七个二分中恰有一个使两个报告均纠缠，即
$$
\{00,11\}\mid\{01,10\};
$$
等价地，成功的满射恰为 $f(r)=r_1\mathbin{\oplus}r_2$ 及其补。其余六个二分中，四个 $1\mid3$ 二分恰有一个纠缠报告，两个非奇偶 $2\mid2$ 二分的两个报告均可分。当 $g=3$ 时，任意至少含四条记录的 $S$ 均给可分密度 $\theta_S$；因此全部 $127$ 个二分均不能使两个报告同时纠缠，其中 $35$ 个 $4\mid4$ 二分的两个报告均可分。特别地，断言
$$
\forall g\ge1\ \exists\text{满射 }f:\{0,1\}^g\to\{0,1\},\quad
\theta_{f^{-1}(0)}\text{ 与 }\theta_{f^{-1}(1)}\text{ 均纠缠}
$$
被 $g=3$ 反驳。本命题不判定各个 $g\ge4$ 是否存在这样的满射；命题 142.1 在这些长度对总奇偶函数的结论仍限于该函数。

证明。命题 137.1 的实际分支公式在上述加减基上给出
$$
\chi_r=\operatorname{vec}_{LR}(C_r)\otimes|0\rangle_M
+s\operatorname{vec}_{LR}(C_rE_0)\otimes|1\rangle_M.
$$
对两条正交记忆列取偏迹正是所定义的 $Q_r$。$J,Z$ 均可逆且 $\kappa_g>0$，故每个 $C_r$ 可逆，从而
$$
q_r=\|C_r\|_F^2+\alpha\|C_rE_0\|_F^2>0,
\qquad \sum_{r\in\{0,1\}^g}q_r=1.
$$
后一式由该完整测量的正交完备性及 $\|\Xi_{g+2}\|=1$ 得到。记录已成为经典数据，合并事件只求 $Q_r$ 之和，没有不同记录间的振幅交叉项。于是每个非空事件的概率为正，满射的两报告均有正概率，归一化权重恰为陈述中的 $q_r/q_S$。

为处理整个记录集，使用同一个代数合同
$$
F=J^{-1}\otimes I_{B_R},\qquad
N_r=\kappa_g^{-1}J^{-1}C_r=Z^{r_1}J\cdots Z^{r_g}J.
$$
若
$$
v_r=\operatorname{vec}_{LR}(N_r)=(a,b,c,d)^{\mathsf T},\qquad
w_r=(a,0,c,0)^{\mathsf T},\qquad
P_r=\operatorname{outer}(v_r)+\alpha\operatorname{outer}(w_r),
$$
则
$$
P(S):=\sum_{r\in S}P_r
=\kappa_g^{-2}FQ_S\operatorname{adj}(F),\qquad
R(S):=\operatorname{PT}_R(P(S)).
$$
这是对整个事件的共同正数缩放与可逆左局部合同，没有分别归一化记录。其迹不替代实际概率 $q_S$。可逆局部合同及其逆均保持有限个正乘积算子之和，而右偏转置与左局部合同交换。因此 $Q_S$ 与 $P(S)$ 及各自的正迹归一化具有相同的可分性与 PPT 分类。$F$ 仅用于代数论证，协议没有增加端点操作。

所有 $N_r$ 都是实矩阵。直接对单条记录取右偏转置得
$$
R(\{r\})=
\begin{pmatrix}
ta^2&ab&tac&bc\\
ab&b^2&ad&bd\\
tac&ad&tc^2&cd\\
bc&bd&cd&d^2
\end{pmatrix}.
$$
记
$$
H=\begin{pmatrix}
0&0&0&-1\\
0&0&1&0\\
0&1&0&0\\
-1&0&0&0
\end{pmatrix}.
$$
偏转置只把 $\operatorname{outer}(v_r)$ 的 $00,11$ 与 $01,10$ 位置及其对称位置互换，变化分别为 $-\det N_r$ 和 $\det N_r$。另一方面，$w_r=(a,c)^{\mathsf T}\otimes|0\rangle$，故记忆项 $\alpha\operatorname{outer}(w_r)$ 在右偏转置下不变。由 $\det J=\det Z=-1$，得到适用于任意记录集的恒等式
$$
R(S)=P(S)+\left(\sum_{r\in S}\det N_r\right)H,
\qquad \det N_r=(-1)^{g+r_1+\cdots+r_g}.
$$
因此，只要 $S$ 中 $r_1+\cdots+r_g$ 为偶数与奇数的记录数相等，就有 $R(S)=P(S)\ge0$。这里平衡的是行列式的计数，并不要求原始 Born 概率相等。该正半定结论允许奇异矩阵。

翻转第一条记录位，记作 $\tau(r)=(1-r_1,r_2,\ldots,r_g)$，给出
$$
N_{\tau(r)}=ZN_r,\qquad
P(\tau S)=(Z\otimes I)P(S)(Z\otimes I),\qquad
R(\tau S)=(Z\otimes I)R(S)(Z\otimes I).
$$
故这对记录集保持分类。对 $g=3$，若以二进制整数表示记录，$\tau$ 就是与 $4$ 作异或。

每个原始记录的 NPT 可直接使用命题 137.1 的可逆分支论证。具体地，令 $G_r=C_r^{-1}\otimes I$、$z=(|01\rangle-|10\rangle)/\sqrt2$，则
$$
\operatorname{PT}_R\bigl(G_rQ_r\operatorname{adj}(G_r)\bigr)
=\begin{pmatrix}
t&0&0&0\\
0&0&1&0\\
0&1&0&0\\
0&0&0&1
\end{pmatrix},\qquad
\operatorname{adj}(z)\operatorname{PT}_R\bigl(G_rQ_r\operatorname{adj}(G_r)\bigr)z=-1.
$$
因左局部合同与右偏转置交换，$x_r=\operatorname{adj}(G_r)z$ 满足
$$
\operatorname{adj}(x_r)\operatorname{PT}_R(Q_r)x_r=-1,
\qquad
\operatorname{adj}(x_r)\operatorname{PT}_R(\theta_{\{r\}})x_r=-\frac1{q_r}<0.
$$
这证明所有单点事件 NPT，特别是 $g=1$ 的唯一二分成功。

现完整处理 $g=2$。由 $N_r=Z^{r_1}JZ^{r_2}J$ 得
$$
\begin{array}{c|rrrr}
r&a&b&c&d\\\hline
00&2&1&1&1\\
01&0&1&1&1\\
10&2&1&-1&-1\\
11&0&1&-1&-1
\end{array}.
$$
对偶事件 $E_2=\{00,11\}$，上述公共矩阵公式给出
$$
R(E_2)=\begin{pmatrix}
4t&2&2t&0\\
2&2&2&0\\
2t&2&2t&2\\
0&0&2&2
\end{pmatrix},\qquad
\det R(E_2)=-32(t-1)=-32\alpha<0.
$$
负的全阶主子式排除正半定性，奇事件 $\{01,10\}=\tau E_2$ 亦然。这与命题 140.1（C）的奇偶 NPT 结论一致。由于 $\det F=(\det J^{-1})^2=1$，对两个实际归一化报告分别有
$$
\det\operatorname{PT}_R(\theta_S)
=\frac{\kappa_2^8}{q_S^4}(-32\alpha)<0.
$$
另两个 $2\mid2$ 二分恰为
$$
\{00,01\}\mid\{10,11\},\qquad
\{00,10\}\mid\{01,11\}.
$$
其每个块都有一条偶记录与一条奇记录，故由平衡恒等式均 PPT；这也符合命题 140.1（A）的固定原始坐标删除结论。

四个 $1\mid3$ 二分的单点侧已证 NPT。将三元块按其缺失记录标识，第一位翻转把缺失 $10$、$11$ 分别化为缺失 $00$、$01$。两代表的矩阵为
$$
R(\{01,10,11\})=\begin{pmatrix}
4t&2&-2t&-1\\
2&3&-2&-1\\
-2t&-2&3t&3\\
-1&-1&3&3
\end{pmatrix},\qquad
R(\{00,10,11\})=\begin{pmatrix}
8t&4&0&-1\\
4&3&0&-1\\
0&0&3t&3\\
-1&-1&3&3
\end{pmatrix}.
$$
以 $\Delta_k(M)$ 表示按固定次序取 $M$ 左上角 $k\times k$ 主子矩阵的行列式，两行完整顺序主子式为
$$
\begin{array}{c|rrrr}
\text{缺失记录}&\Delta_1&\Delta_2&\Delta_3&\Delta_4\\\hline
00&4t&12t-4&12t+24&80-25t\\
01&8t&24t-16&24t+72&336-153t
\end{array}.
$$
这些值由行列式展开及 $t^2=t+1$ 得到。$1<t<2$ 使每项严格为正，故两矩阵均由 Sylvester 判据正定，第一位翻转覆盖另两组三元块。

下面处理 $g=3$ 的全部四元块。把四条偶记录记为 $e_A,e_B,e_C,e_D$，并按第一位翻转的对应次序记四条奇记录为 $o_A,o_B,o_C,o_D$。直接乘 $Z^{r_1}JZ^{r_2}JZ^{r_3}J$ 所得八个整数向量为
$$
\begin{array}{c|c|rrrr}
\text{标记}&r&a&b&c&d\\\hline
e_A&000&3&2&2&1\\
e_B&101&1&2&0&-1\\
e_C&110&1&0&-2&-1\\
e_D&011&-1&0&0&1\\\hline
o_A&100&3&2&-2&-1\\
o_B&001&1&2&0&1\\
o_C&010&1&0&2&1\\
o_D&111&-1&0&0&-1
\end{array}.
$$
置 $E=\{e_A,e_B,e_C,e_D\}$、$O=\{o_A,o_B,o_C,o_D\}$。全部四元子集按所含偶记录数分成
$$
\binom84=70
=\underbrace{\binom42\binom42}_{36}
+\underbrace{2}_{E,O}
+\underbrace{\binom43\binom41}_{16}
+\underbrace{\binom41\binom43}_{16}.
$$
其中 $36$ 个平衡块已经由 $R(S)=P(S)\ge0$ 处理，无需其主子式严格为正。第一位翻转交换 $E,O$，并交换最后两类。故剩余只需处理 $E$ 及全部十六个
$$
S_{ij}=(E\setminus\{e_i\})\cup\{o_j\},\qquad i,j\in\{A,B,C,D\}.
$$
令 $M_E=R(E)/2$、$M_{ij}=R(S_{ij})/2$。公共矩阵项已由 $R(\{r\})$ 给出，具体说，对这些四元块 $S$，
$$
M_S=\frac12\sum_{r\in S}
\begin{pmatrix}
ta_r^2&a_rb_r&ta_rc_r&b_rc_r\\
a_rb_r&b_r^2&a_rd_r&b_rd_r\\
ta_rc_r&a_rd_r&tc_r^2&c_rd_r\\
b_rc_r&b_rd_r&c_rd_r&d_r^2
\end{pmatrix},\qquad
M_E=\begin{pmatrix}
6t&4&2t&2\\
4&4&0&0\\
2t&0&4t&2\\
2&0&2&2
\end{pmatrix}.
$$
下列十七行逐一标明矩阵，并列出其全部四个顺序主子式：
$$
\begin{array}{c|rrrr}
M&\Delta_1&\Delta_2&\Delta_3&\Delta_4\\\hline
M_E&6t&24t-16&16t+80&224-64t\\
M_{AA}&6t&24t-16&10t+32&4t+36\\
M_{AB}&2t&8t-4&6t+12&4t+28\\
M_{AC}&2t&4t-1&10t+16&4t+28\\
M_{AD}&2t&4t-1&4t+6&3t+10\\
M_{BA}&10t&40t-36&22t+236&796-316t\\
M_{BB}&6t&24t-16&26t+80&116-28t\\
M_{BC}&6t&12t-9&12t+54&130-45t\\
M_{BD}&6t&12t-9&10t+40&76-8t\\
M_{CA}&10t&60t-49&34t+240&636-172t\\
M_{CB}&6t&36t-25&18-8t&42-21t\\
M_{CC}&6t&24t-16&32-6t&100-44t\\
M_{CD}&6t&24t-16&12-2t&28-12t\\
M_{DA}&10t&60t-49&64t+354&1090-453t\\
M_{DB}&6t&36t-25&34t+120&284-40t\\
M_{DC}&6t&24t-16&30t+108&316-108t\\
M_{DD}&6t&24t-16&26t+80&196-44t
\end{array}.
$$
为给出各行的统一展开式，写
$$
M=\begin{pmatrix}
tx&y&tp&h\\
y&z&k&u\\
tp&k&tv&w\\
h&u&w&2
\end{pmatrix},\qquad
A=xv-p^2,\qquad D=2z-u^2,
$$
$$
C=v(2y^2-2uyh+zh^2)+x(2k^2-2ukw+zw^2)
-2p\bigl(2yk-u(yw+hk)+zhw\bigr).
$$
这里各 $M$ 的右下角为 $2$，因为八个向量都满足 $d_r^2=1$。逐阶展开得到
$$
\begin{aligned}
\Delta_1&=tx,\\
\Delta_2&=txz-y^2,\\
\Delta_3&=t^2zA-t(xk^2+vy^2-2pyk),\\
\Delta_4&=t^2AD-tC+(yw-hk)^2.
\end{aligned}
$$
将八个向量按相应 $S$ 代入公共矩阵项，再用 $t^2=t+1$ 约化，即逐行得到上表。两组三元块及此十七行中的每个主子式都是一次式 $L(t)$；所列系数均满足 $L(1)\ge0$、$L(2)\ge0$ 且两者不同时为零。因此
$$
L(t)=(2-t)L(1)+(t-1)L(2)>0\qquad(1<t<2).
$$
例如 $42-21t=21(2-t)>0$，其在 $t=2$ 的零值不属于参数范围。故这十七个实对称矩阵全由 Sylvester 判据正定，翻转合同覆盖其余十七个非平衡块；加上 $36$ 个平衡块，全部 $70$ 个四元块都 PPT。

这里的实矩阵判据确实作用于所需的复 Hermitian 正性：对实对称 $A$ 与任意复向量 $x+iy$，有
$$
(x+iy)^*A(x+iy)=x^{\mathsf T}Ax+y^{\mathsf T}Ay.
$$
因而实二次型的非负性等价于复二次型的非负性，实正定也给出复正定。平衡块的正半定性则直接来自正外积之和。可分复密度的偏转置必正半定，因为正乘积项 $U\otimes V$ 变为 $U\otimes V^{\mathsf T}\ge0$，故前面的 NPT 均排除可分性。对所有已证 PPT 的块，$\theta_S$ 是完整 $\mathbb C^2\otimes\mathbb C^2$ 上的正迹一密度，可使用命题 141.1 已采用的二维 PPT 充分性，得到可分性。所用结果为 M. Horodecki、P. Horodecki、R. Horodecki，*Separability of Mixed States: Necessary and Sufficient Conditions*，[arXiv:quant-ph/9605038v2，定理 3，PDF 第 8 页](https://arxiv.org/pdf/quant-ph/9605038v2)，Physics Letters A 223，1–8（1996），[DOI:10.1016/S0375-9601(96)00706-2](https://doi.org/10.1016/S0375-9601(96)00706-2)。该文的闭包定义与此处有限凸和定义的一致性已由命题 141.1 的有限维紧性论证给出。因此上述三元块、平衡块与全部四元块得到的都是本命题所定义的可分性。

最后，把 $g=3$ 的四元块结论推广到较大记录集。若 $S\subseteq\{0,1\}^3$ 且 $n=|S|\ge4$，则未归一化算子有恒等式
$$
Q_S=\binom{n-1}{3}^{-1}
\sum_{\substack{A\subseteq S\\|A|=4}}Q_A.
$$
事实上，固定 $r\in S$ 后，包含 $r$ 的四元子集由其余 $n-1$ 条记录中任选三条唯一确定，恰有 $\binom{n-1}{3}$ 个。将右边每个 $Q_A$ 展开为原始 $Q_r$ 之和，每个 $Q_r$ 的系数因而恰为一。已证每个 $Q_A$ 属于有限正乘积和组成的可分正锥，该锥对有限求和与非负数乘法封闭，所以 $Q_S$ 也在该锥内。由 $q_S>0$，$\theta_S$ 可分。这一步使用已可分四元块的正组合；它不以向一个 PPT 算子添加任意原始正算子为封闭性依据。

每个八记录二分必有一块的基数至少为四，故至少一个报告可分。为明确穷尽范围，把含 $000$ 的块作为第一块，并要求其补非空，恰有 $2^7-1=127$ 个无标号非平凡二分；按较小块的基数计数为
$$
\begin{array}{c|rrrr}
\text{块大小}&1\mid7&2\mid6&3\mid5&4\mid4\\\hline
\text{二分数}&8&28&56&35
\end{array},\qquad 8+28+56+35=127.
$$
全部 $127$ 个二分都由上述至少四元块的结论排除两个报告同时纠缠，$4\mid4$ 的两块则均可分。同理，四记录的无标号二分共有 $2^3-1=7$ 个，前面列出的三个 $2\mid2$ 与四个 $1\mid3$ 已穷尽它们，得到恰一个成功、四个单侧纠缠、两个双侧可分的分类。$g=3$ 的全二分障碍即给陈述中的全有限长度存在断言的反例。证毕。

<a id="entry-636"></a>

## 追加锚（本行以下为增补区）

<a id="section-144"></a>

## 144. 全端点预测的射影历史商与共同前后缀下的记录合并

**命题 144.1（两记忆列的标量射线判据与精确充分记录）。** 沿用命题 130.1、137.1 的纯边界过程，取
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
0<\alpha<1,\qquad \alpha^2+\alpha=1,\qquad B=M=\mathbb C^2,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1),
$$
$$
\Xi_0=m_0,\qquad
\Xi_{n+1}=(I_{B^{\otimes n}}\otimes T)\Xi_n.
$$
各空间取正交标准基。对任意有限整数 $g\ge0$，从这个纯初态恰好发出 $g+2$ 个输出，在全部生成之后测量内部位置；完整次序为
$$
B_L\otimes B_1\otimes\cdots\otimes B_g\otimes B_R\otimes M.
$$
$L,R$ 是第一个和最后一个已发出的 qubit，端点空间始终为完整的 $B_L\otimes B_R=\mathbb C^2\otimes\mathbb C^2$，左端点之前没有被忽略的前缀。最终记忆取偏迹且不可访问，生成途中不读取、测量或重置记忆。每个内部位置仅在事先固定的加减基
$$
|\eta_b\rangle=\frac{|0\rangle+(-1)^b|1\rangle}{\sqrt2}
\quad(b=0,1)
$$
中测量一次，全部结果成为原始经典记录 $r=(r_1,\ldots,r_g)\in\{0,1\}^g$。生成及内部测量没有反馈、端点操作或记录的相干重组。测后的内部系统与最终记忆均不可再访问；对已完成记录作确定性经典处理后，除所声明的保留标签外，不访问原始记录及其他副本。以下端点预测指这一制备完成后的实验，不要求重建旧的经典词或被测位置的仪器。

以 $\dagger$ 表示伴随，$\operatorname{outer}(x)=xx^\dagger$，并按左行右列约定
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1 C_{ij}|i\rangle_L\otimes|j\rangle_R,
\qquad 00,01,10,11\text{ 为坐标次序}.
$$
记
$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
Z=\operatorname{diag}(1,-1),\qquad E_0=\operatorname{diag}(1,0),\qquad
\kappa_g=s^{g+3}2^{-g/2},
$$
$$
N_r=Z^{r_1}J\cdots Z^{r_g}J,\qquad N_\varnothing=I_2,
\qquad C_r=\kappa_g JN_r.
$$
直接采用命题 137.1 的实际分支公式：
$$
\chi_r=\operatorname{vec}_{LR}(C_r)\otimes|0\rangle_M
+s\operatorname{vec}_{LR}(C_rE_0)\otimes|1\rangle_M,
$$
$$
Q_r=\operatorname{Tr}_M\operatorname{outer}(\chi_r)
=\operatorname{outer}(\operatorname{vec}_{LR}(C_r))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(C_rE_0)),
\qquad q_r=\operatorname{Tr}Q_r>0,\qquad \theta_r=Q_r/q_r.
$$
两个记忆列及其相对系数 $\alpha$ 都保留，$q_r$ 是该完整记录的实际 Born 概率，$\sum_rq_r=1$。对任意非零复二阶矩阵 $C$，也用同一代数式定义
$$
Q(C)=\operatorname{outer}(\operatorname{vec}_{LR}(C))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(CE_0)),\qquad
\operatorname{Tr}Q(C)=\|C\|_F^2+\alpha\|CE_0\|_F^2>0.
$$
称两个非零矩阵射影相同，是指它们相差一个非零复标量。对每个 $N_r$，选取 $N_r,-N_r$ 中按逐行次序遇到的第一个非零元素为正的那个，记为整数矩阵签名 $\sigma(r)$。

固定 $g$，定义完整记录的精确端点预测等价为
$$
r\sim_g v
\quad\Longleftrightarrow\quad
\operatorname{Tr}(E\theta_r)=\operatorname{Tr}(E\theta_v)
\quad\text{对每个 }E\in\mathcal L(B_L\otimes B_R),\ 0\le E\le I.
$$
这也就是每个有限端点 POVM 的全部结果分布相同。对确定性函数 $f:\{0,1\}^g\to\mathcal B$，仅考虑其有限像中的标签 $b$，定义实际事件及条件密度
$$
Q_b=\sum_{r:f(r)=b}Q_r,\qquad
q_b=\operatorname{Tr}Q_b=\sum_{r:f(r)=b}q_r>0,\qquad
\theta_b=Q_b/q_b.
$$
称 $f$ 逐记录精确充分，是指对每个端点效应 $E$，存在仅依赖保留标签的预测值 $\widehat p_E(b)\in[0,1]$，满足
$$
\widehat p_E(f(r))=\operatorname{Tr}(E\theta_r)
\qquad\text{对每条完整记录 }r.
$$
这一要求保留每条原始记录所条件化的概率，而不只是给出合并事件的平均概率。

则对任意非零 $C,D\in\mathbb C^{2\times2}$，包括奇异矩阵，均有标量射线判据
$$
\frac{Q(D)}{\operatorname{Tr}Q(D)}=\frac{Q(C)}{\operatorname{Tr}Q(C)}
\quad\Longleftrightarrow\quad
D=zC\quad\text{存在 }z\in\mathbb C\setminus\{0\}.
$$
因此，对每个固定 $g\ge0$ 及 $r,v\in\{0,1\}^g$，
$$
r\sim_g v
\quad\Longleftrightarrow\quad \theta_r=\theta_v
\quad\Longleftrightarrow\quad N_v=\pm N_r
\quad\Longleftrightarrow\quad \sigma(v)=\sigma(r).
$$
这些条件成立时还满足 $C_v=\pm C_r$、$Q_v=Q_r$、$q_v=q_r$。$f$ 逐记录精确充分当且仅当每个非空纤维中的 $\theta_r$ 全部相同；此时实际 Born 加权的 $\theta_b$ 就是该共同密度。签名 $\sigma$ 因而是此任务的最粗充分有限标签，在有效标签双射重命名的意义下唯一，其标签数恰为
$$
K_g=\bigl|\{\sigma(r):r\in\{0,1\}^g\}\bigr|,
$$
即不同射影整数矩阵的个数。两个相同端点密度也保持对同一后续端点 CPTP 操作及测量的预测相同，所用协议只能访问端点和已保留标签。

进一步有
$$
(ZJ)^3=-I_2,\qquad N_{0111}=N_{1110}=-J.
$$
固定长度 $g=0,1,2,3$ 时没有不同记录的射影碰撞，首次碰撞发生于 $g=4$。任意有限二进制词 $u,r,v$ 满足
$$
N_{urv}=N_uN_rN_v.
$$
故中间词的射影相同在任意共同前缀 $u$ 与共同后缀 $v$ 下保持。特别地，若中间词 $r,w$ 等长且 $N_w=\pm N_r$，则在内部长度同为 $G=|u|+|r|+|v|$ 的两个完整协议中，
$$
Q_{uwv}=Q_{urv},\qquad q_{uwv}=q_{urv},\qquad
\theta_{uwv}=\theta_{urv}.
$$
因此每个 $g\ge4$ 都有不同完整记录可无损合并，$K_g<2^g$。这里的上下文是完整协议内的共同测量标签词；结论没有给出仅作用于已保留端点态的逐步闭合动力学，也不授予访问已丢弃记忆或内部系统的能力。

证明。加减基在命题 137.1 中给 $D_k=2^{-1/2}Z^{r_k}$，代入该命题即得所列 $C_r$、$\chi_r$ 及 $Q_r$。由 $\det J=\det Z=-1$，
$$
N_r\in\operatorname{GL}_2(\mathbb Z),\qquad
\det N_r=(-1)^{g+\sum_k r_k},\qquad \kappa_g>0.
$$
所以所有 $C_r$ 非零且可逆，命题 137.1 的迹公式给 $q_r>0$，完整测量的完备性给 $\sum_rq_r=1$，包括 $g=0$ 的空记录。这里没有把第二记忆列并入第一列或各自重新归一化。

先证一般的标量射线判据。令 $P=I_{B_L}\otimes E_0$，则 $P=P^\dagger=P^2$，且
$$
P\operatorname{vec}_{LR}(C)=\operatorname{vec}_{LR}(CE_0).
$$
在全部四阶复矩阵的线性空间上定义
$$
\mathcal L(X)=X+\alpha PXP,\qquad
\mathcal R(Y)=Y-\frac{\alpha}{1+\alpha}PYP.
$$
利用 $P^2=P$ 展开两种复合，均有
$$
\begin{aligned}
\mathcal R(\mathcal L(X))
&=X+\left(\alpha-\frac{\alpha}{1+\alpha}
-\frac{\alpha^2}{1+\alpha}\right)PXP=X,\\
\mathcal L(\mathcal R(Y))
&=Y+\left(\alpha-\frac{\alpha}{1+\alpha}
-\frac{\alpha^2}{1+\alpha}\right)PYP=Y.
\end{aligned}
$$
故 $\mathcal L$ 代数可逆，$\mathcal L^{-1}=\mathcal R$。置 $c=\operatorname{vec}_{LR}(C)$、$d=\operatorname{vec}_{LR}(D)$，便有 $Q(C)=\mathcal L(cc^\dagger)$、$Q(D)=\mathcal L(dd^\dagger)$。若两个归一化密度相同，取正数
$$
\lambda=\frac{\operatorname{Tr}Q(D)}{\operatorname{Tr}Q(C)}>0,
$$
则 $Q(D)=\lambda Q(C)$。施加线性的 $\mathcal R$ 得 $dd^\dagger=\lambda cc^\dagger$。对任意非零向量 $h$，$hh^\dagger$ 的像恰为 $\mathbb C h$：它的每个像向量是 $h$ 的倍数，而 $hh^\dagger h=\|h\|^2h\ne0$。于是 $d=zc$，其中 $z\ne0$，再比较外积得 $|z|^2=\lambda$。向量化单射，故 $D=zC$。反之，$D=zC$ 直接给 $Q(D)=|z|^2Q(C)$ 及相同的归一化密度。证明只用 $c,d$ 非零，没有要求 $C,D$ 可逆。

这个逆仅用于代数比较。事实上，取标准基 $e_0=|00\rangle$、$e_1=|01\rangle$ 及正迹一算子
$$
Y=\operatorname{outer}\left(\frac{e_0+e_1}{\sqrt2}\right).
$$
由于 $Pe_0=e_0$、$Pe_1=0$，$\mathcal R(Y)$ 在这两个坐标上的主子矩阵及其行列式为
$$
\frac12\begin{pmatrix}(1+\alpha)^{-1}&1\\1&1\end{pmatrix},\qquad
-\frac{\alpha}{4(1+\alpha)}<0,
\qquad \operatorname{Tr}\mathcal R(Y)=1-\frac{\alpha}{2(1+\alpha)}\ne1.
$$
因此 $\mathcal R$ 不是正映射，也不是完全正或保迹映射，不能作为任意输入态的物理恢复通道。

对固定长度的两条记录，刚证的判据及 $J$ 可逆、$\kappa_g>0$ 给
$$
\theta_v=\theta_r\quad\Longleftrightarrow\quad
N_v=zN_r\quad(z\ne0).
$$
$N_r$ 至少有一个非零实元素，比较该处元素说明 $z$ 为实数。再取行列式，
$$
z^2=\frac{\det N_v}{\det N_r}\in\{1,-1\}.
$$
实非零 $z$ 的平方为正，故 $z^2=1$、$z=\pm1$。反向蕴含直接成立。两个 $C$ 的尺度 $\kappa_g$ 相同，所以连未归一化 $Q$ 及其迹也相同。选首个非零元素为正恰好消去这个符号歧义，得到签名等价式。

现在识别预测任务。密度相同显然给所有效应的 Born 概率相同。若 $\Delta=\theta_r-\theta_v$ 为非零 Hermitian 矩阵，则 $\operatorname{Tr}\Delta=0$。其非零实特征值不可能全同号，所以至少有一个正特征值。令 $E_+$ 为全部正特征空间的正交投影，就有
$$
0\le E_+\le I,\qquad
\operatorname{Tr}(E_+\theta_r)-\operatorname{Tr}(E_+\theta_v)
=\operatorname{Tr}(E_+\Delta)
=\sum_{\lambda_j(\Delta)>0}\lambda_j(\Delta)>0.
$$
这给出区分效应，故所有效应相同当且仅当密度相同。每个效应属于二结果 POVM $(E,I-E)$，每个有限 POVM 又由效应组成，因而两种预测表述等价。

为逐字适用定理 54.3 的有限实验族，取 $X=\{0,1\}^g$、实验长度上限 $H=1$，在端点的四个标准基向量 $e_0,e_1,e_2,e_3$ 上选取下列 $16$ 个秩一投影作为二元测量的第一个效应：
$$
\begin{gathered}
F_j=\operatorname{outer}(e_j)\quad(0\le j\le3),\\
F_{jk}^{+}=\operatorname{outer}\left(\frac{e_j+e_k}{\sqrt2}\right),\qquad
F_{jk}^{i}=\operatorname{outer}\left(\frac{e_j+i e_k}{\sqrt2}\right)
\quad(0\le j<k\le3).
\end{gathered}
$$
每个协议是 $(F,I-F)$，共 $4+2\binom42=16$ 个协议。若 $\theta_{jk}=\langle e_j|\theta|e_k\rangle$，则其第一个结果概率满足
$$
\begin{aligned}
p_j&=\theta_{jj},\\
p_{jk}^{+}&=\frac{\theta_{jj}+\theta_{kk}}2+\operatorname{Re}\theta_{jk},\\
p_{jk}^{i}&=\frac{\theta_{jj}+\theta_{kk}}2-\operatorname{Im}\theta_{jk}.
\end{aligned}
$$
所以这 $16$ 个数确定全部对角元和全部非对角元的实、虚部，下三角由 Hermitian 性确定。该有限菜单的响应签名相同恰等价于密度相同，因而恰等价于全部端点效应的预测相同。这里的信息完备性是这些显式公式的结论；信息完备测量的一般术语参见 G. M. D'Ariano、P. Perinotti、M. F. Sacchi，*Informationally Complete Measurements and Group Representation*，Journal of Optics B: Quantum and Semiclassical Optics 6，S487–S491（2004），[DOI:10.1088/1464-4266/6/6/005](https://doi.org/10.1088/1464-4266/6/6/005)。菜单收集各个二元实验的分布，不要求不同实验存在联合结果分布。

定理 54.3 现在直接适用于这个有限菜单：$f$ 充分当且仅当其纤维不跨越响应签名类，而这里的类已被识别为 $\theta_r$ 相同的类，亦即 $\sigma(r)$ 相同的类。对实际事件，经典结果合并的线性性给 $Q_b=\sum_{f(r)=b}Q_r$，且没有不同 $r$ 的振幅交叉项；因此
$$
\theta_b=\sum_{r:f(r)=b}\frac{q_r}{q_b}\theta_r,\qquad
\sum_{r:f(r)=b}\frac{q_r}{q_b}=1.
$$
若纤维中的密度共同等于 $\theta$，这个实际 Born 加权和就等于 $\theta$，取 $\widehat p_E(b)=\operatorname{Tr}(E\theta_b)$ 即满足每条记录的要求。若同一纤维包含不同密度，刚才的区分效应给出两个不同概率，一个共同预测值不可能同时等于它们。合并后的平均概率仍存在，但不满足逐记录要求。故由定理 54.3 的最小性结论，任意充分标签都必须细化 $\sigma$ 的纤维，$\sigma$ 本身充分且恰有 $K_g$ 个有效值；达到这个数的充分标签恰与 $\sigma$ 双射重命名。这没有以纤维大小代替其 Born 权重。

若 $\theta_r=\theta_v$，对同一个端点 CPTP 映射 $\Phi$ 及其输出上的任意效应 $F$，有
$$
\operatorname{Tr}(F\Phi(\theta_r))=\operatorname{Tr}(F\Phi(\theta_v)).
$$
有限次端点操作与测量也逐分支保持这个结论：每条指定结果路径的未归一化算子由同一串线性测量分支映射和通道得到，相同输入给相同算子及其迹。协议若根据先前端点结果或共同保留标签选取后续操作，逐路径仍用同一个映射。此论证的输入只是所保留的端点密度与标签，不包括已丢弃记录、被测内部系统或最终记忆。

为了明确严格于只保留纠缠这一性质，取 $g=2$ 的记录 $00$ 与 $11$。由上面的矩阵乘积，亦即命题 140.1（C）的同一分支，
$$
\kappa_2^{-1}C_{00}=\begin{pmatrix}3&2\\2&1\end{pmatrix},\qquad
\kappa_2^{-1}C_{11}=\begin{pmatrix}-1&0\\0&1\end{pmatrix}.
$$
两条记忆列的迹分别给 $q_{00}=\kappa_2^2(18+13\alpha)$、$q_{11}=\kappa_2^2(2+\alpha)$。效应 $E=|01\rangle\langle01|$ 因而满足
$$
\operatorname{Tr}(E\theta_{00})=\frac4{18+13\alpha}>0,
\qquad \operatorname{Tr}(E\theta_{11})=0.
$$
两条分支均由命题 137.1 纠缠，却能由端点实验区分。命题 140.1（C）已经证明合并为奇偶报告仍保留条件纠缠，但这两个同为偶记录的概率不同，所以该报告不满足此处的精确预测充分性。

最后处理词关系。直接相乘得
$$
ZJ=\begin{pmatrix}1&1\\-1&0\end{pmatrix},\qquad
(ZJ)^2=\begin{pmatrix}0&1\\-1&-1\end{pmatrix},\qquad
(ZJ)^3=\begin{pmatrix}-1&0\\0&-1\end{pmatrix}=-I_2.
$$
于是
$$
N_{0111}=J(ZJ)^3=-J=(ZJ)^3J=N_{1110}.
$$
对较短长度，把 $N_r$ 的四个元素按逐行次序记为 $(a,b,c,d)$。从空词的 $I_2$ 出发，附加一位的整数乘法为
$$
N_{r0}=\begin{pmatrix}a+b&a\\c+d&c\end{pmatrix},\qquad
N_{r1}=\begin{pmatrix}a-b&a\\c-d&c\end{pmatrix}.
$$
这给出长度不超过三的全部值：
$$
\begin{array}{c|c|rrrr}
g&r&a&b&c&d\\\hline
0&\varnothing&1&0&0&1\\\hline
1&0&1&1&1&0\\
1&1&1&1&-1&0\\\hline
2&00&2&1&1&1\\
2&01&0&1&1&1\\
2&10&2&1&-1&-1\\
2&11&0&1&-1&-1\\\hline
3&000&3&2&2&1\\
3&001&1&2&0&1\\
3&010&1&0&2&1\\
3&011&-1&0&0&1\\
3&100&3&2&-2&-1\\
3&101&1&2&0&-1\\
3&110&1&0&-2&-1\\
3&111&-1&0&0&-1
\end{array}.
$$
各长度的 $2^g$ 条记录均已列出；在每个固定长度内，选首个非零元素为正后，四元组两两不同。因此 $g\le3$ 没有射影碰撞，而所列两条长度四的不同记录给出首次碰撞。

按定义连接有限乘积，结合律立即给 $N_{urv}=N_uN_rN_v$，空词情形也成立。若 $N_w=zN_r$，则
$$
N_{uwv}=N_u(zN_r)N_v=zN_{urv}.
$$
故射影关系在任意共同上下文中保持。若 $|r|=|w|$，前面已证 $z=\pm1$，两条完整记录的内部长度同为 $G$，于是
$$
C_{uwv}=\kappa_G JN_{uwv}=\pm\kappa_G JN_{urv}=\pm C_{urv}.
$$
分别对两记忆列取外积，符号同时消去，便得到相同的实际 $Q$、$q$ 及 $\theta$。这些式子比较的是从 $m_0$ 开始、各自恰好发出 $G+2$ 位的完整协议；共同前缀是其中已测内部位置的标签，并非左端点之前被忽略的输出，共同后缀也不是作用于旧右端点的通道。因而该乘法恒等式不提供在擦除最终记忆后继续生成的状态更新律。

对每个 $g\ge4$，在 $0111$ 与 $1110$ 前面同加 $0^{g-4}$，就得到两条不同的长度 $g$ 记录及相同的实际条件端点密度，故 $K_g<2^g$。所证的是该关系及其所有共同上下文中的保持性；没有断言这一条改写生成全部词关系，也没有由它确定一般正规形或 $K_g$ 的增长律。证毕。

<a id="entry-638"></a>

## 追加锚（本行以下为增补区）
<a id="section-145"></a>

## 145. 丢弃相关记忆后的逐结果延长与非选择物理闭合

**命题 145.1（未知左滤波制备族的唯一代数延长、仪器障碍与非选择通道）。** 取命题 130.1、137.1 的纯边界生成器，在各个二维空间的正交标准基中令
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
\alpha+\alpha^2=1,\qquad 0<\alpha<1,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle_{\rm out}\otimes m_j\quad(j=0,1).
$$
从纯记忆 $m_0$ 恰好发出两个输出 $L,R$，记
$$
\Xi_2=(I_L\otimes T)Tm_0\in B_L\otimes B_R\otimes M,
\qquad B_L=B_R=M=\mathbb C^2.
$$
本命题另行允许如下制备族：对任意复二阶矩阵 $F$，只要 $F^\dagger F\le I_2$，就在 $L$ 上施加单 Kraus 成功分支 $F$，保留未归一化联合向量
$$
\chi_F=(F\otimes I_R\otimes I_M)\Xi_2.
$$
成功旗标相同，滤波设置 $F$ 不作为后续仪器的可用标签。这里允许全部这样的复收缩，包括奇异矩阵与零矩阵；这是新增的制备假设，并非命题 138.1、139.1 的内部测量策略所已允许的端点操作。

以 $\dagger$ 表示伴随，$\mathsf T$ 表示普通转置，沿用命题 137.1 的左行右列约定
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1C_{ij}|i\rangle_L|j\rangle_R,
\qquad 00,01,10,11\text{ 为坐标次序}.
$$
定义
$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
Z=\operatorname{diag}(1,-1),\qquad E_0=|0\rangle\langle0|,
\qquad C_0=s^3J,\qquad C=FC_0,
$$
$$
Q(C)=|\operatorname{vec}_{LR}(C)\rangle\langle\operatorname{vec}_{LR}(C)|
+\alpha|\operatorname{vec}_{LR}(CE_0)\rangle
\langle\operatorname{vec}_{LR}(CE_0)|.
$$
此式对包括零在内的全部复矩阵 $C$ 定义。实际端点输入是 $\operatorname{Tr}_M|\chi_F\rangle\langle\chi_F|$；一旦取偏迹，端点仪器不得访问该记忆或其副本。

比较协议则保留同一个 $\chi_F$ 中的原始相关记忆，对它施加 $T$ 再发出一个输出 $R'$，在旧 $R$ 上测量固定正交基
$$
|\eta_b\rangle=\frac{|0\rangle+(-1)^b|1\rangle}{\sqrt2},
\qquad b\in\{0,1\},\qquad A_b=Z^bJ,
$$
保留结果 $b$、$L,R'$，对最终记忆 $M'$ 取偏迹。其未归一化向量和端点算子定义为
$$
\chi_{F,b}=(I_L\otimes\langle\eta_b|_R\otimes I_{R'}\otimes I_{M'})
(I_{LR}\otimes T)\chi_F,
\qquad Q_{F,b}=\operatorname{Tr}_{M'}|\chi_{F,b}\rangle\langle\chi_{F,b}|.
$$
$F$ 始终只作用于 $L$。将输入 $L,R$ 与输出 $L,R'$ 按标准基识别为 $\mathbb C^4$。端点二结果量子仪器在这里指一对定义于全部 $M_4(\mathbb C)$ 的复线性完全正映射 $\mathcal I_0,\mathcal I_1$，其和保迹；两映射固定而不依赖 $F$。

则实际制备及比较分支满足
$$
\chi_F=\operatorname{vec}_{LR}(C)\otimes|0\rangle_M
+s\operatorname{vec}_{LR}(CE_0)\otimes|1\rangle_M,
\qquad \operatorname{Tr}_M|\chi_F\rangle\langle\chi_F|=Q(C),
$$
$$
C_b=\frac{s}{\sqrt2}CA_b,\qquad
\chi_{F,b}=\operatorname{vec}_{LR'}(C_b)\otimes|0\rangle_{M'}
+s\operatorname{vec}_{LR'}(C_bE_0)\otimes|1\rangle_{M'},
\qquad Q_{F,b}=\frac{\alpha}{2}Q(CA_b).
$$
两记忆列及其相对系数 $\alpha$ 均不可省略。设
$$
q_F=\operatorname{Tr}Q(C)=\|C\|_F^2+\alpha\|CE_0\|_F^2,\qquad
q_{F,b}=\operatorname{Tr}Q_{F,b}
=\frac{\alpha}{2}\bigl(\|CA_b\|_F^2+\alpha\|CA_bE_0\|_F^2\bigr).
$$
这里 $q_F\in[0,1]$ 是滤波成功概率，$q_{F,b}$ 是成功且报告 $b$ 的联合概率，$q_{F,0}+q_{F,1}=q_F$。若 $F\ne0$，则 $q_F,q_{F,0},q_{F,1}>0$，报告条件概率为 $q_{F,b}/q_F$，报告后的密度为 $Q_{F,b}/q_{F,b}$。若 $F=0$，全部算子和概率均为零，不定义条件密度。

不存在上述端点仪器使
$$
\mathcal I_b(Q(FC_0))=Q_{F,b}
\quad\text{对每个 }F\in M_2(\mathbb C),\ F^\dagger F\le I_2,
\quad b=0,1
$$
同时成立。不过，去掉完全正性要求后，每个分支有唯一的复线性延拓。令
$$
P=I_L\otimes E_0,\qquad
\mathcal L(X)=X+\alpha PXP,\qquad
\mathcal L^{-1}(Y)=Y-\frac{\alpha}{1+\alpha}PYP,
\qquad \operatorname{Ad}_B(X)=BXB^\dagger,
$$
则该延拓为
$$
\widehat{\mathcal I}_b
=\frac{\alpha}{2}\mathcal L\circ
\operatorname{Ad}_{I_L\otimes A_b^{\mathsf T}}\circ\mathcal L^{-1}
=\operatorname{Id}_L\otimes\phi_b.
$$
其中对任意彼此独立的复数 $x,y,z,w$，令 $e=(-1)^b$，有
$$
\phi_b\!\begin{pmatrix}x&y\\z&w\end{pmatrix}
=\frac12\begin{pmatrix}
\alpha x+e(y+z)+w&\alpha^2x+e\alpha z\\
\alpha^2x+e\alpha y&\alpha^2x
\end{pmatrix},
\qquad
\operatorname{Tr}\phi_b(X)=\operatorname{Tr}(|\eta_b\rangle\langle\eta_b|X).
$$
所以只要求下一报告的概率时，端点测量 $I_L\otimes|\eta_b\rangle\langle\eta_b|$ 已能实现它；障碍在于同时保留正确报告及其条件输出。

另一方面，忘掉报告后的唯一延拓是完全正保迹通道
$$
\widehat{\mathcal I}_0+\widehat{\mathcal I}_1
=\operatorname{Id}_L\otimes\mathcal T,\qquad
\mathcal T(X)=X_{00}\tau_0+X_{11}E_0,
\qquad
\tau_0=\begin{pmatrix}\alpha&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix}.
$$
它在右端点测量计算基，随后分别制备 $\tau_0$ 或 $E_0$，消除 $L:R'$ 间的纠缠。它的有效 Kraus 分解不实现上面指定的两个逐结果分支。

证明。由 $\|m_0\|^2=\alpha+\alpha^2=1$、$\|m_1\|^2=1$ 及输出标准基的正交性，$T^\dagger T=I_2$。直接应用两次等距得
$$
Tm_0=s|0\rangle m_0+\alpha|1\rangle m_1,
\qquad
\Xi_2=\alpha|00\rangle m_0+s\alpha|01\rangle m_1
+\alpha|10\rangle m_0.
$$
在正交记忆基上展开，利用 $s\alpha=s^3$、$\alpha^2=s^4$，得到
$$
\Xi_2=s^3(|00\rangle+|01\rangle+|10\rangle)|0\rangle_M
+s^4(|00\rangle+|10\rangle)|1\rangle_M
=\operatorname{vec}_{LR}(C_0)|0\rangle_M
+s\operatorname{vec}_{LR}(C_0E_0)|1\rangle_M.
$$
对任意复矩阵 $F,C_0$，逐坐标有
$$
(F\otimes I_R)\operatorname{vec}_{LR}(C_0)=\operatorname{vec}_{LR}(FC_0).
$$
这给出 $\chi_F$ 的两列；对 $M$ 取偏迹时只消去正交记忆列之间的交叉项，第二列的外积系数是 $s^2=\alpha$，从而得到实际的 $Q(FC_0)$。这一步没有先把任意 $C$ 的代数定义当成物理制备。$F^\dagger F\le I_2$ 保证 $F$ 与 $\sqrt{I_2-F^\dagger F}$ 可组成完整制备操作，且
$$
q_F=\|\chi_F\|^2
=\langle\Xi_2|(F^\dagger F\otimes I_R\otimes I_M)|\Xi_2\rangle\le1.
$$

为推导比较分支，把 $C$ 的两列记为 $u,v\in\mathbb C^2$，故
$$
\chi_F=(u|0\rangle_R+v|1\rangle_R)|0\rangle_M
+s u|0\rangle_R|1\rangle_M.
$$
这里 $u,v$ 属于 $L$，其系数可以为任意复数。对原始记忆应用 $T$，再用 $\langle\eta_b|$ 收缩旧 $R$，逐项得到
$$
\chi_{F,b}
=\frac{s}{\sqrt2}\bigl((u+ev)|0\rangle_{R'}+u|1\rangle_{R'}\bigr)|0\rangle_{M'}
+\frac{\alpha}{\sqrt2}(u+ev)|0\rangle_{R'}|1\rangle_{M'}.
$$
由于
$$
A_b=\begin{pmatrix}1&1\\e&0\end{pmatrix},\qquad
CA_b=(u+ev,\ u),\qquad s^2=\alpha,
$$
这恰是所列 $C_b$ 的两记忆列。$\eta_b$ 的分量为实数，bra 系数为 $1/\sqrt2,e/\sqrt2$；它不对 $u,v$ 取共轭。取最终记忆偏迹，外积才带复共轭，且两个分支都保留同一个因子 $s^2/2=\alpha/2$。$L$ 上的 $F$ 与这次发出和旧 $R$ 测量作用于不同张量因子，故也可在这些操作之后施加同一个 $F$。全过程没有更换或重置原始记忆。

迹等于两列范数平方之和，给出全部概率式。比较协议中的等距保范数，两个 $\eta_b$ 完备，所以 $\sum_bq_{F,b}=\|\chi_F\|^2=q_F$。$C_0$ 与两个 $A_b$ 都可逆，因而 $F\ne0$ 时 $C\ne0$、$CA_b\ne0$，每个范数和严格为正。$F=0$ 时全部向量为零。这证明了包括奇异与零滤波在内的实际分支和归一化边界。

现在才讨论端点线性延拓。$P^2=P$，展开两种复合时 $PXP$ 的额外系数均为
$$
\alpha-\frac{\alpha}{1+\alpha}-\frac{\alpha^2}{1+\alpha}=0,
$$
故所列 $\mathcal L^{-1}$ 确为代数逆。又有
$$
P\operatorname{vec}_{LR}(C)=\operatorname{vec}_{LR}(CE_0),\qquad
\mathcal L(|\operatorname{vec}_{LR}(C)\rangle\langle\operatorname{vec}_{LR}(C)|)=Q(C).
$$
$\det C_0=-s^6\ne0$。对任意 $D\in M_2(\mathbb C)$，取实数
$$
t=\max\{1,\|DC_0^{-1}\|_{\rm op}\}>0,\qquad
F=t^{-1}DC_0^{-1}.
$$
则 $F^\dagger F\le I_2$ 且 $D=tFC_0$。两个实际分支的公式都是二次齐次的：
$$
Q(tFC_0)=t^2Q(FC_0),\qquad
Q(tFC_0A_b)=t^2Q(FC_0A_b).
$$
因此，一个线性映射若在全部允许的收缩 $F$ 上满足要求，就在全部 $D$ 上被迫满足
$$
\mathcal I_b(Q(D))=\frac{\alpha}{2}Q(DA_b).
$$
$D=0$ 对应 $F=0$，两边都为零，不需除以概率。

为说明这一约束确定全部算子，令 $h_0,\ldots,h_3$ 为 $\mathbb C^4$ 标准基，$E_{jk}=|h_j\rangle\langle h_k|$。取下列 $16$ 个未归一化秩一外积：
$$
D_j=|h_j\rangle\langle h_j|\quad(0\le j\le3),\qquad
D_{jk}^{+}=|h_j+h_k\rangle\langle h_j+h_k|,\qquad
D_{jk}^{i}=|h_j+i h_k\rangle\langle h_j+i h_k|
\quad(0\le j<k\le3).
$$
它们给出
$$
D_{jk}^{+}-D_j-D_k=E_{jk}+E_{kj},\qquad
D_{jk}^{i}-D_j-D_k=-iE_{jk}+iE_{kj}.
$$
右边连同四个对角矩阵构成 Hermitian 矩阵空间的实基，所以这 $4+2\binom42=16$ 个外积在实数上张成全部 Hermitian 矩阵。每个向量都可唯一写成某个复二阶矩阵的 $\operatorname{vec}_{LR}$；上一段的正数缩放把它对应的 $Q$ 化为允许的实际输入的正倍数。可逆且保持 Hermitian 性的 $\mathcal L$ 因而把它们送到另一组实张成族。最后每个复矩阵 $X$ 都有分解
$$
X=\frac{X+X^\dagger}{2}
+i\frac{X-X^\dagger}{2i},
$$
两项中的矩阵均为 Hermitian，故复线性性确定全部 $M_4(\mathbb C)$ 上的值。这里用到的是全部未知复左收缩产生的张成族，而不是任意固定有限原始记录集的张成性。

逐坐标的向量化恒等式为
$$
\operatorname{vec}_{LR'}(DA_b)
=(I_L\otimes A_b^{\mathsf T})\operatorname{vec}_{LR}(D).
$$
因此 $\widehat{\mathcal I}_b$ 的所列复合确实把 $Q(D)$ 送到 $\alpha Q(DA_b)/2$，由刚证的唯一性，任何候选仪器都必须等于它。普通转置来自右乘的指标次序；伴随只出现在 $\operatorname{Ad}$ 中。特别地，$A_b$ 是实矩阵，但 $F,D$ 无须为实。

写 $\mathcal L=\operatorname{Id}_L\otimes\lambda$，其中 $\lambda(X)=X+\alpha E_0XE_0$。由 $(1+\alpha)^{-1}=\alpha$，对独立复矩阵元有
$$
\lambda^{-1}\!\begin{pmatrix}x&y\\z&w\end{pmatrix}
=\begin{pmatrix}\alpha x&y\\z&w\end{pmatrix},\qquad
A_b^{\mathsf T}=\begin{pmatrix}1&e\\1&0\end{pmatrix}.
$$
两侧相乘，再施加 $\alpha\lambda/2$，就得到陈述中的 $\phi_b$，这里没有施加 $z=\overline y$ 的限制。利用 $\alpha+\alpha^2=1$ 取迹得
$$
\operatorname{Tr}\phi_b(X)=\frac{x+w+e(y+z)}2
=\operatorname{Tr}(|\eta_b\rangle\langle\eta_b|X).
$$
在左端点各矩阵块上应用此式，得到对全部 $Y\in M_4(\mathbb C)$ 的迹恒等式
$$
\operatorname{Tr}\widehat{\mathcal I}_b(Y)
=\operatorname{Tr}\bigl((I_L\otimes|\eta_b\rangle\langle\eta_b|)Y\bigr).
$$
两效应为正且和为恒等，因此实际 $Q(C)$ 上的报告概率确有端点测量实现。

然而取合法端点密度
$$
Y=|0\rangle_L\langle0|\otimes|+\rangle_R\langle+|,
\qquad |+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2}.
$$
在 $L=0$ 的右端点块上将 $x=y=z=w=1/2$、$b=1$ 代入，利用 $1-\alpha=\alpha^2$ 及 $\alpha-\alpha^2=\alpha^3$，得到
$$
\widehat{\mathcal I}_1(Y)
=|0\rangle_L\langle0|\otimes
\frac{\alpha^2}{4}\begin{pmatrix}-1&-\alpha\\-\alpha&1\end{pmatrix},
\qquad
\langle00|\widehat{\mathcal I}_1(Y)|00\rangle=-\frac{\alpha^2}{4}<0.
$$
因此这个唯一延拓连正映射都不是，更不可能完全正，所要求的端点仪器不存在。

这个 $Y$ 不在实际制备域内，甚至不在该域所生成的正锥内。事实上，$\mathcal L^{-1}(Y)$ 在同一块上为
$$
\frac12\begin{pmatrix}\alpha&1\\1&1\end{pmatrix},\qquad
\det\left(\frac12\begin{pmatrix}\alpha&1\\1&1\end{pmatrix}\right)
=\frac{\alpha-1}{4}=-\frac{\alpha^2}{4}<0.
$$
若 $Y=\sum_k t_kQ(F_kC_0)$ 且 $t_k\ge0$，施加 $\mathcal L^{-1}$ 后右边是非负系数的秩一外积和，必为正半定，与此行列式矛盾；归一化兼容密度的有限正混合亦归入同一正锥。收敛的正混合或概率积分也不能给出 $Y$，因为施加连续线性映射 $\mathcal L^{-1}$ 后，每个向量上的二次型仍是非负数的极限或积分。该计算同时说明代数逆 $\mathcal L^{-1}$ 不是正的物理恢复映射。虽然 $Y$ 不是某个 $F$ 产生的输入，定义在全部端点算子上的量子仪器必须在它上面保持正性；制备族已把该仪器的线性取值唯一固定，所以这个域外密度是有效的否定依据。对每个实际制备，$Q_{F,b}$ 始终是两个正外积之和，没有物理联合过程把实际合法制备送成负算子。

最后相加两个分支公式，含 $e$ 的项消去，得到
$$
(\phi_0+\phi_1)(X)
=\begin{pmatrix}\alpha x+w&\alpha^2x\\\alpha^2x&\alpha^2x\end{pmatrix}
=x\tau_0+wE_0.
$$
为明确在全部算子上的等式，令 $e_{ij}=|i\rangle\langle j|$ 为右端点四个矩阵单位。刚才的相加及以下 Kraus 和在这四个输入上的像分别均为
$$
e_{00}\longmapsto\tau_0,\qquad e_{11}\longmapsto E_0,\qquad
 e_{01}\longmapsto0,\qquad e_{10}\longmapsto0.
$$
左因子保持不变，所以对 $|i\rangle_L\langle k|\otimes e_{jl}$ 的全部 $16$ 个矩阵单位等式成立，进而对每个复四阶矩阵成立。具体地，取
$$
K_0=\alpha(|0\rangle+|1\rangle)\langle0|,\qquad
K_1=s^3|0\rangle\langle0|,\qquad K_2=|0\rangle\langle1|.
$$
直接乘法给
$$
\sum_{j=0}^2 K_jXK_j^\dagger
=X_{00}\bigl(\alpha^2(|0\rangle+|1\rangle)(\langle0|+\langle1|)
+\alpha^3E_0\bigr)+X_{11}E_0=\mathcal T(X),
$$
因为 $\alpha^2+\alpha^3=\alpha$。而
$$
\tau_0=2\alpha^2|+\rangle\langle+|+\alpha^3E_0,
\qquad 2\alpha^2+\alpha^3=1,
\qquad \operatorname{Tr}\tau_0=1,\qquad \det\tau_0=\alpha^5>0,
$$
$$
\sum_{j=0}^2K_j^\dagger K_j
=(2\alpha^2+\alpha^3)E_0+|1\rangle\langle1|=I_2.
$$
Kraus 和在任意附加恒等因子后仍把正算子送到正算子，故完全正；最后一个等式给出保迹性。端点 Kraus 算子恰为 $I_L\otimes K_j$。对任意密度 $\rho_{LR}$，记其两个右对角块为
$$
\rho_L^{jj}=(I_L\otimes\langle j|)\rho_{LR}(I_L\otimes|j\rangle)\ge0.
$$
则
$$
(\operatorname{Id}_L\otimes\mathcal T)(\rho_{LR})
=\rho_L^{00}\otimes\tau_0+\rho_L^{11}\otimes E_0,
\qquad \operatorname{Tr}\rho_L^{00}+\operatorname{Tr}\rho_L^{11}=1.
$$
将非零左块按迹归一化，即为有限凸乘积密度和，证明 $L:R'$ 可分。这只消除该分割上的纠缠；若 $L$ 与另一个外部系统纠缠，这个结论不要求它们的纠缠消失。

每个 $F$ 已有由原始相关记忆给出的正分支，且端点输入通过上述代数延拓确定它们。若只给定一个已知 $F\ne0$，还可定义依赖该设置的替换仪器
$$
\mathcal R_b^{F}(X)=\operatorname{Tr}(X)\,\frac{Q_{F,b}}{q_F}.
$$
若 $Q_{F,b}/q_F=\sum_j\lambda_j|v_j\rangle\langle v_j|$ 是谱分解，则 $\sqrt{\lambda_j}|v_j\rangle\langle h_k|$（$0\le k\le3$）给出该映射的 Kraus 算子，所以它完全正。由 $\sum_b\operatorname{Tr}(Q_{F,b}/q_F)=1$，两映射之和保迹，并在 $Q(FC_0)$ 上给 $Q_{F,b}$；但它随 $F$ 改变，故不满足同一未知设置族上的要求。同样，报告概率的端点测量、忘记报告后的 Kraus 通道以及任何该通道的其他有效 Kraus 分解，都不等于指定的 $\widehat{\mathcal I}_b$：若某个有效二结果分解在全部允许输入上给出这些分支，唯一性又会迫使其负的 $b=1$ 分支成立。保留原始相关记忆足以实施这个下一实验；只保留端点且不提供 $F$ 标签，不能对该整个制备族实施带报告的正确延长。关于已完成端点实验的预测等价和代数状态更新，因而不蕴含这种物理仪器闭合。证明不对固定有限原始记录族单独断言同样障碍，也不确定其他辅助资源的最小容量或任意环境干预的动力学。证毕。

本命题所用仪器概念的成熟参考为 E. B. Davies、J. T. Lewis，*An operational approach to quantum probability*，Communications in Mathematical Physics 17，239–260（1970），[DOI:10.1007/BF01647093](https://doi.org/10.1007/BF01647093)。初始系统与环境相关、约化动力学的兼容域以及全空间正性要求之间的区分，参见 P. Pechukas，*Reduced Dynamics Need Not Be Completely Positive*，Physical Review Letters 73，1060–1062（1994），[DOI:10.1103/PhysRevLett.73.1060](https://doi.org/10.1103/PhysRevLett.73.1060)。测量后制备与破坏纠缠通道的术语参见 M. Horodecki、P. W. Shor、M. B. Ruskai，*Entanglement Breaking Channels*，Reviews in Mathematical Physics 15，629–641（2003），[DOI:10.1142/S0129055X03001709](https://doi.org/10.1142/S0129055X03001709)。这些引文提供概念背景；本命题的具体结论由所给 $T$、制备族、矩阵恒等式及负二次型推出。

<a id="entry-640"></a>

## 追加锚（本行以下为增补区）

<a id="section-146"></a>

## 146. 独立报告翻转下端点延长仪器的精确噪声阈值

**命题 146.1（未知复左收缩族的一步带噪延长、闭阈值与 Kraus 实现）。** 沿用命题 145.1 的制备族及命题 130.1、137.1 的纯边界生成器。所有矩阵均在复数域上，$\dagger$ 表示共轭转置，$\mathsf T$ 表示普通转置，$\operatorname{outer}(v)=vv^\dagger$。置
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
\alpha+\alpha^2=1,\qquad 1+\alpha=\alpha^{-1},\qquad 1-\alpha=\alpha^2,
$$
$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
Z=\operatorname{diag}(1,-1),\qquad E_0=\operatorname{diag}(1,0),\qquad
E_1=\operatorname{diag}(0,1),\qquad C_0=s^3J.
$$
各二维空间取正交标准基，向量化仍为
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1 C_{ij}|i\rangle_L|j\rangle_R,
\qquad 00,01,10,11\text{ 为坐标次序}.
$$
从初始记忆 $m_0=s|0\rangle+\alpha|1\rangle$ 出发，以
$$
m_1=|0\rangle,\qquad T|j\rangle=|j\rangle_{\rm out}\otimes m_j
$$
恰好发出 $L,R$ 两个输出，再在 $L$ 上施加任意单 Kraus 成功分支 $F\in M_2(\mathbb C)$，$F^\dagger F\le I_2$，不归一化。成功旗标相同，后续端点仪器只接收成功制备的端点，不取得设置 $F$ 或原始相关记忆及其副本。全部复收缩，包括奇异矩阵和 $F=0$，都在量词范围内；这个端点滤波假设来自命题 145.1 的另行扩大的制备族，并非命题 138.1、139.1 的内部测量策略所授权的操作。令 $C=FC_0$，由该实际制备所得的未归一化输入为
$$
Q(C)=\operatorname{outer}(\operatorname{vec}_{LR}(C))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(CE_0)).
$$

比较协议保留这个成功制备中的同一个原始相关记忆，再用 $T$ 发出 $R'$，在旧 $R$ 上测量
$$
|\eta_b\rangle=\frac{|0\rangle+(-1)^b|1\rangle}{\sqrt2},\qquad b\in\{0,1\},
$$
并对最终记忆取偏迹。随后引入与制备及该测量独立的经典位 $e$，满足 $\Pr(e=1)=\varepsilon$，$0\le\varepsilon\le1$；只保留报告 $y=b\mathbin\oplus e$，丢弃 $b,e$ 的全部其他副本。以命题 145.1 的实际尖锐分支记号写成
$$
Q_b(C):=Q_{F,b}=\frac{\alpha}{2}Q(CZ^bJ),
$$
其中输出向量化在 $L,R'$ 上。带噪报告的实际未归一化分支是
$$
R_0(C)=(1-\varepsilon)Q_0(C)+\varepsilon Q_1(C),\qquad
R_1(C)=\varepsilon Q_0(C)+(1-\varepsilon)Q_1(C).
$$
这里混合的是带各自 Born 权重的算子，不是分别归一化的两个密度。

按标准基识别输入 $L,R$ 与输出 $L,R'$ 的四维空间。存在不依赖 $F$ 的复线性完全正映射 $\mathcal J_0,\mathcal J_1:M_4(\mathbb C)\to M_4(\mathbb C)$，使 $\mathcal J_0+\mathcal J_1$ 保迹并满足
$$
\mathcal J_y(Q(FC_0))=R_y(FC_0)
\quad\text{对全部 }F^\dagger F\le I_2\text{ 及 }y\in\{0,1\},
$$
当且仅当
$$
(1-2\varepsilon)^2\le\alpha,
\qquad\text{即}\qquad
\frac{1-\sqrt\alpha}{2}\le\varepsilon\le\frac{1+\sqrt\alpha}{2}.
$$
更精确地，令 $\lambda=1-2\varepsilon$、$\nu_y=(-1)^y\lambda$。对每个 $\varepsilon\in[0,1]$，在整个所声明制备族上的兼容性已经迫使唯一的复线性延拓
$$
\widehat{\mathcal J}_y=\operatorname{Id}_L\otimes\psi_{\nu_y},\qquad
\psi_\nu\!\begin{pmatrix}x&u\\v&w\end{pmatrix}
=\frac12\begin{pmatrix}
\alpha x+w+\nu(u+v)&\alpha^2x+\nu\alpha v\\
\alpha^2x+\nu\alpha u&\alpha^2x
\end{pmatrix},
$$
其中 $x,u,v,w$ 是相互独立的复数。这两个延拓恰在上述闭区间内完全正。

在允许区间内，置 $\delta_\nu=\alpha-\nu^2\ge0$，可取右端点 Kraus 算子
$$
K_1(\nu)=\frac1{\sqrt2}\begin{pmatrix}\nu&1\\\nu\alpha&0\end{pmatrix},\qquad
K_2(\nu)=\frac{\sqrt{\delta_\nu}}{\sqrt2}\begin{pmatrix}1&0\\\alpha&0\end{pmatrix},\qquad
K_3(\nu)=\frac{\alpha^2}{\sqrt2}\begin{pmatrix}0&0\\1&0\end{pmatrix}.
$$
带报告标签 $y$ 的六个算子 $I_L\otimes K_j(\nu_y)$ 组成一个固定端点仪器。对任意 $\varepsilon\in[0,1]$，其强制代数延拓的报告效应和非选择和分别为
$$
H_y=\frac{I_2+\nu_y X_{\rm P}}2,\qquad
X_{\rm P}=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
\operatorname{Tr}\widehat{\mathcal J}_y(Y)=\operatorname{Tr}((I_L\otimes H_y)Y),
$$
$$
\widehat{\mathcal J}_0+\widehat{\mathcal J}_1
=\operatorname{Id}_L\otimes\mathcal T,\qquad
\mathcal T\!\begin{pmatrix}x&u\\v&w\end{pmatrix}
=x\tau_0+wE_0,\qquad
\tau_0=\begin{pmatrix}\alpha&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix}.
$$
所有这些报告效应构成有效 POVM，且 $\mathcal T$ 始终是同一个完全正保迹通道；这两个事实各自均不蕴含指定带报告分支的完全正性。结论只涉及上述固定制备族、独立经典翻转和一次延长。

证明。命题 130.1 的等距以及命题 145.1 对命题 137.1 空内部记录的实际展开给出
$$
\Xi_2=s^3(|00\rangle+|01\rangle+|10\rangle)|0\rangle_M
+s^4(|00\rangle+|10\rangle)|1\rangle_M,
$$
$$
\chi_F=\operatorname{vec}_{LR}(C)|0\rangle_M
+s\operatorname{vec}_{LR}(CE_0)|1\rangle_M.
$$
这保留了两个记忆列；命题 145.1 的计算直接适用于全部复 $F$，不需要 $F^{-1}$。记 $C=(c_0,c_1)$，则
$$
q(C):=\operatorname{Tr}Q(C)=(1+\alpha)\|c_0\|^2+\|c_1\|^2,
\qquad 0\le q(C)\le1,\qquad q(C_0)=\alpha^3(3+2\alpha)=1.
$$
$C_0$ 可逆，故 $q(C)=0$ 恰当 $F=0$。比较协议在同一个 $\chi_F$ 上继续；命题 145.1 已从 $T$ 与旧 $R$ 的 bra 收缩得到其最终记忆两列的系数矩阵
$$
D_b=\frac{s}{\sqrt2}(c_0+\sigma c_1,\ c_0)
=\frac{s}{\sqrt2}CZ^bJ,\qquad sD_bE_0,\qquad \sigma=(-1)^b.
$$
取最终记忆偏迹即为 $Q(D_b)=Q_b(C)$。这直接引用同一相关动力学的分支，不把偏迹后的端点重新与独立记忆拼接。

置 $h(C)=\operatorname{Re}(c_0^\dagger c_1)$。利用 $\alpha(1+\alpha)=1$，展开范数得
$$
\begin{aligned}
q_b(C):=\operatorname{Tr}Q_b(C)
&=\frac{\alpha}{2}\bigl((1+\alpha)\|c_0+\sigma c_1\|^2+\|c_0\|^2\bigr)\\
&=\frac{q(C)}2+\sigma h(C),\qquad q_0(C)+q_1(C)=q(C).
\end{aligned}
$$
若 $F\ne0$，两个 $Z^bJ$ 均可逆，故 $q_b(C)>0$。独立翻转并忘记旧经典标签时，对同一报告的未归一化分支求和，正是所述 $R_y$，且
$$
r_y(C):=\operatorname{Tr}R_y(C)=\frac{q(C)}2+\nu_yh(C),\qquad
r_0(C)+r_1(C)=q(C).
$$
非零 $F$ 时 $r_y(C)>0$；成功条件下报告概率为 $r_y(C)/q(C)$，报告后的端点密度为 $R_y(C)/r_y(C)$。例如令 $\theta_b=Q_b(C)/q_b(C)$，则
$$
\frac{R_0(C)}{r_0(C)}
=\frac{(1-\varepsilon)q_0(C)}{r_0(C)}\theta_0
+\frac{\varepsilon q_1(C)}{r_0(C)}\theta_1.
$$
这两个条件权重一般不同于 $1-\varepsilon,\varepsilon$。当 $F=0$ 时所有未归一化算子及概率均为零，以上任何条件密度都不作定义。

现用命题 145.1 已证的兼容输入张成性。具体地，令 $P=I_L\otimes E_0$，则
$$
\mathcal L(Y)=Y+\alpha PYP,\qquad
\mathcal L^{-1}(Y)=Y-\alpha^2PYP,
\qquad Q(C)=\mathcal L(\operatorname{outer}(\operatorname{vec}_{LR}(C))).
$$
其中 $\alpha/(1+\alpha)=\alpha^2$。对任意复矩阵 $D$，命题 145.1 的正数缩放
$$
t=\max\{1,\|DC_0^{-1}\|_{\rm op}\},\qquad F=t^{-1}DC_0^{-1}
$$
满足 $F^\dagger F\le I_2$ 且 $D=tFC_0$。$Q$ 和每个 $R_y$ 都按 $t^2$ 缩放，因此线性兼容性从实际收缩族延至全部 $D$。该命题用四维标准基 $h_j$ 以及 $h_j+h_k,h_j+i h_k$ 的 $16$ 个外积证明 Hermitian 实张成；可逆的 $\mathcal L$ 及上述逐项正缩放给出实际兼容输入的同样张成性。每个复矩阵都是两个 Hermitian 矩阵的复线性组合，所以这也确定全部 $M_4(\mathbb C)$ 上的作用。这里的带符号线性组合只用于唯一性证明，不增加物理制备假设。

命题 145.1 的唯一尖锐延拓为 $\widehat{\mathcal I}_b=\operatorname{Id}_L\otimes\phi_b$。其右因子方向由
$$
\operatorname{vec}(CZ^bJ)=(I_L\otimes (Z^bJ)^{\mathsf T})\operatorname{vec}(C),
\qquad (Z^bJ)^{\mathsf T}=JZ^b=\begin{pmatrix}1&\sigma\\1&0\end{pmatrix}
$$
固定。该命题对四个独立复矩阵元给出的 $\phi_b$ 正是本命题 $\psi_\sigma$ 的公式。将两个尖锐延拓按实际经典翻转作线性组合，$\sigma$ 项变为 $\nu_y$，常数项不变，遂得到 $\widehat{\mathcal J}_y=\operatorname{Id}_L\otimes\psi_{\nu_y}$；它满足全部兼容性等式，由张成性也是唯一延拓。这个等式不施加 $v=\overline u$ 的限制，亦不把 $\mathcal L^{-1}$ 当作可实施的恢复映射。

为判定完全正性，记右端点矩阵单位 $e_{ij}=|i\rangle\langle j|$。取未归一化向量 $\Omega=|00\rangle+|11\rangle$，第一因子是输入参考，第二因子是通道输出。直接代入四个矩阵单位，得到
$$
\begin{aligned}
\mathsf C_\nu
&:=(\operatorname{Id}_{\rm ref}\otimes\psi_\nu)(\operatorname{outer}(\Omega))
=\sum_{i,j=0}^1e_{ij}\otimes\psi_\nu(e_{ij})\\
&=\frac12\begin{pmatrix}
\alpha&\alpha^2&\nu&0\\
\alpha^2&\alpha^2&\nu\alpha&0\\
\nu&\nu\alpha&1&0\\
0&0&0&0
\end{pmatrix}.
\end{aligned}
$$
对实数 $\nu$ 置 $\delta=\alpha-\nu^2$、$v_0=(1,\alpha)^{\mathsf T}$。$2\mathsf C_\nu$ 的前三维块以第三个对角元 $1$ 为 Schur 主元，其余二阶 Schur 补为
$$
\begin{pmatrix}
\alpha-\nu^2&\alpha^2-\alpha\nu^2\\
\alpha^2-\alpha\nu^2&\alpha^2-\alpha^2\nu^2
\end{pmatrix}
=\delta v_0v_0^{\mathsf T}+\alpha^4E_1.
$$
更直接地，对任意 $r,t,u,k\in\mathbb C$ 有精确恒等式
$$
2\begin{pmatrix}r\\t\\u\\k\end{pmatrix}^{\!\dagger}
\mathsf C_\nu\begin{pmatrix}r\\t\\u\\k\end{pmatrix}
=|u+\nu r+\nu\alpha t|^2
+\delta|r+\alpha t|^2+\alpha^4|t|^2.
$$
这里使用 $\alpha^3+\alpha^4=\alpha^2$。若 $\delta\ge0$，右边非负；若 $\delta<0$，取
$$
z_\nu=(1,0,-\nu,0)^{\mathsf T},\qquad
z_\nu^\dagger\mathsf C_\nu z_\nu=\frac{\alpha-\nu^2}{2}<0.
$$
因此 $\mathsf C_\nu\ge0$ 恰当 $\nu^2\le\alpha$。前三维主块的行列式为 $\alpha^4(\alpha-\nu^2)/8$，全四阶行列式则恒为零，不能用后者判定阈值。

若 $\psi_\nu$ 完全正，依定义 $\operatorname{Id}_{\rm ref}\otimes\psi_\nu$ 必将正算子 $\operatorname{outer}(\Omega)$ 送到正算子，所以负二次型已经排除 $\nu^2>\alpha$。若某个兼容端点分支 $\mathcal J_y$ 完全正，则唯一性迫使其等于 $\operatorname{Id}_L\otimes\psi_{\nu_y}$。将它与完全正的嵌入 $X\mapsto E_0\otimes X$ 及对 $L$ 的偏迹复合，所得恰为 $\psi_{\nu_y}$，故后者也必须完全正。两份 $\nu_y^2$ 都等于 $\lambda^2$，于是 $\lambda^2\le\alpha$ 是端点仪器存在的必要条件。$z_\nu$ 只是强制映射的 Choi 二次型测试向量，不是原始制备产生的负态；对任意允许的 $F$ 和 $\varepsilon\in[0,1]$，实际 $Q_b(C)$ 是正外积之和，$R_y(C)$ 是其非负混合，始终正半定。区间外所排除的是全空间完全正延拓，本论证不对 $\psi_\nu$ 的普通正性另作分类。

反之，设 $\delta=\alpha-\nu^2\ge0$，取陈述中的 $K_j(\nu)$。这三个矩阵的第一列依次为 $\nu v_0/\sqrt2$、$\sqrt\delta v_0/\sqrt2$、$\alpha^2|1\rangle/\sqrt2$，第二列依次为 $|0\rangle/\sqrt2,0,0$。因此在四个独立矩阵单位上逐项有
$$
\begin{aligned}
\sum_{j=1}^3 K_j e_{00}K_j^\dagger
&=\frac12(\alpha v_0v_0^\dagger+\alpha^4E_1)
=\frac12\begin{pmatrix}\alpha&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix}
=\psi_\nu(e_{00}),\\
\sum_{j=1}^3 K_j e_{01}K_j^\dagger
&=\frac\nu2\begin{pmatrix}1&0\\\alpha&0\end{pmatrix}
=\psi_\nu(e_{01}),\\
\sum_{j=1}^3 K_j e_{10}K_j^\dagger
&=\frac\nu2\begin{pmatrix}1&\alpha\\0&0\end{pmatrix}
=\psi_\nu(e_{10}),\\
\sum_{j=1}^3 K_j e_{11}K_j^\dagger
&=\frac12 E_0=\psi_\nu(e_{11}).
\end{aligned}
$$
复线性性遂给出全部 $X\in M_2(\mathbb C)$ 上的 Kraus 恒等式。每个 Kraus 项在任意辅助空间上扩张后都是由 $I_{\rm anc}\otimes K_j$ 作合同，因而保持正半定；有限和完全正。张量上左端点恒等即给出所需端点分支的完全正性。这个充分性直接来自所列算子，不需要从 Choi 正性反推完全正性的定理。

还须证明这两分支组成同一个保迹仪器。直接乘法以及
$$
\alpha(1+\alpha^2)+\alpha^4=\alpha+\alpha^3+\alpha^4=1
$$
给出
$$
\sum_{j=1}^3 K_j(\nu)^\dagger K_j(\nu)
=\frac12\begin{pmatrix}1&\nu\\\nu&1\end{pmatrix}
=\frac{I_2+\nu X_{\rm P}}2.
$$
取 $\nu_0=\lambda$、$\nu_1=-\lambda$，两个效应相加为 $I_2$，从而
$$
\sum_{y=0}^1\sum_{j=1}^3
(I_L\otimes K_j(\nu_y))^\dagger(I_L\otimes K_j(\nu_y))=I_4.
$$
所以总映射保迹；每个分支效应介于零与恒等之间，分支不增迹。这一个仪器只依赖给定的 $\varepsilon$，其右 Kraus 算子从旧 $R$ 映到新 $R'$，保持 $L$ 不变，不访问 $F,b,e$ 或已丢弃的记忆。结合已证的兼容性，它对全部复收缩都给出正确未归一化输出。两个边界 $\lambda=\pm\sqrt\alpha$ 均使 $K_2=0$，其余公式仍成立，没有除以 $\delta$ 的步骤，故两个等号边界都允许。由 $\lambda=1-2\varepsilon$ 解不等式即得陈述中的闭区间。

最后，对全部实数 $\nu\in[-1,1]$，直接从 $\psi_\nu$ 的公式取迹，得到
$$
\operatorname{Tr}\psi_\nu(X)=\frac{x+w+\nu(u+v)}2
=\operatorname{Tr}\left(\frac{I_2+\nu X_{\rm P}}2 X\right).
$$
效应的特征值为 $(1+\nu)/2,(1-\nu)/2$。故即使不满足完全正阈值，两个报告概率仍可由端点 POVM 实现，但这不提供指定条件输出。又有
$$
(\psi_\lambda+\psi_{-\lambda})(X)=x\tau_0+wE_0=\mathcal T(X),
\qquad \operatorname{Tr}\tau_0=1,\qquad \det\tau_0=\alpha^5>0.
$$
这正是命题 145.1 已证明的计算基测量后制备通道，故对每个噪声参数均完全正保迹。在 $\varepsilon=1/2$ 时，$\lambda=0$，两个分支都等于 $(\operatorname{Id}_L\otimes\mathcal T)/2$；在 $\varepsilon=0$ 或 $1$ 时，$\lambda^2=1>\alpha$，负 Choi 期望恰为 $(\alpha-1)/2=-\alpha^2/2$，尽管报告 POVM 和非选择通道仍有效。交换报告标签使 $\lambda$ 变号，所以允许区间关于 $1/2$ 对称。对 $0<|\lambda|\le\sqrt\alpha$，效应差 $H_0-H_1=\lambda X_{\rm P}$ 非零，仪器保留非零报告对比度；完全抹去报告并非必要。上述存在性与障碍只比较这一制备族的一步延长，不推及其他制备、其他噪声或多步闭合。证毕。

本命题的 Choi 矩阵与完全正映射术语参见 Man-Duen Choi，*Completely positive linear maps on complex matrices*，Linear Algebra and its Applications 10（3），285–290（1975），[DOI:10.1016/0024-3795(75)90075-0](https://doi.org/10.1016/0024-3795(75)90075-0)。此引文提供成熟背景；所述固定制备族的阈值、闭边界及 Kraus 算子由本命题的矩阵恒等式给出。

<a id="entry-642"></a>

## 追加锚（本行以下为增补区）
<a id="section-147"></a>

## 147. 任意有限报告的端点复现、最大二元因子与精确饱和

**命题 147.1（有限报告的逐行完全正判据、唯一随机分解与饱和恢复）。** 沿用命题 145.1、146.1 的全部复左收缩制备族和向量化约定。具体地，各二维空间取正交标准基，$\dagger$ 表示共轭转置，$\mathsf T$ 表示普通转置，$\operatorname{outer}(v)=vv^\dagger$，并置
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
\alpha+\alpha^2=1,\qquad 0<s<1,
$$
$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
Z=\operatorname{diag}(1,-1),\qquad E_0=\operatorname{diag}(1,0),\qquad C_0=s^3J,
\qquad \operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1C_{ij}|i\rangle_L|j\rangle_R.
$$
从纯初始记忆 $m_0=s|0\rangle+\alpha|1\rangle$ 出发，以 $m_1=|0\rangle$、$T|j\rangle=|j\rangle_{\rm out}\otimes m_j$ 恰好发出 $L,R$，随后在 $L$ 上施加任意单 Kraus 成功分支 $F\in M_2(\mathbb C)$，$F^\dagger F\le I_2$。包括奇异 $F$ 与 $F=0$，不对成功分支归一化；保留共同成功旗标，而不向后续端点仪器提供 $F$。这是命题 145.1 明定的扩大的制备族，不由命题 138.1、139.1 的有限内部记录策略推出。记 $C=FC_0$，端点仪器只取得约化输入
$$
Q(C)=\operatorname{outer}(\operatorname{vec}_{LR}(C))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(CE_0)).
$$
比较协议则保留该制备的同一个原始相关记忆，用 $T$ 再发出一次 $R'$，在旧 $R$ 上测量固定基
$$
|\eta_b\rangle=\frac{|0\rangle+(-1)^b|1\rangle}{\sqrt2},\qquad b\in\{0,1\},
$$
再对最终记忆取偏迹，实际尖锐分支为命题 146.1 的
$$
Q_b(C)=\frac\alpha2 Q(CZ^bJ),
$$
其中输出向量化在 $L,R'$ 上。所有步骤无反馈；端点仪器不能访问原始记忆及其副本。

任取非空有限集合 $Y$ 和列随机矩阵 $W:Y\leftarrow\{0,1\}$，即 $W(y\mid b)\ge0$、$\sum_yW(y\mid b)=1$。在实际尖锐记录完成后，给定 $b$ 按 $W(\cdot\mid b)$ 独立于其余系统及制备设置抽取报告，只保留 $y$ 与量子输出 $L,R'$，不保留 $b$、处理随机性或已丢弃记忆的可访问副本。定义
$$
R_y(C)=\sum_{b=0}^1W(y\mid b)Q_b(C),\qquad
c_y=W(y\mid0)+W(y\mid1),\qquad d_y=W(y\mid0)-W(y\mid1).
$$
称 $W$ 对此制备族可由端点仪器复现，是指存在一个不依赖 $F$ 的仪器 $(\mathcal J_y)_{y\in Y}$：每个 $\mathcal J_y:M_4(\mathbb C)\to M_4(\mathbb C)$ 复线性且完全正，$\sum_y\mathcal J_y$ 保迹，并且
$$
\mathcal J_y(Q(FC_0))=R_y(FC_0)
\qquad(F^\dagger F\le I_2,\ y\in Y).
$$
这里按标准基识别输入 $L,R$ 与输出 $L,R'$。要求是每个未归一化分支相等，等价于完整报告与量子输出的联合算子 $\sum_y|y\rangle\langle y|\otimes R_y(C)$ 相等。每个上述 $W$ 都能处理原实验已完成的记录；本定义限制的是只从约化端点输入复现这个联合算子，不是对经典处理本身的物理许可分类。

令
$$
B_s(t\mid b)=\frac{1+(-1)^{t+b}s}{2},\qquad t,b\in\{0,1\}.
$$
则以下三项等价：$W$ 可由端点仪器复现；对每个 $y$ 有 $d_y^2\le\alpha c_y^2$；存在列随机矩阵 $V:Y\leftarrow\{0,1\}$ 使 $W=VB_s$。该随机因子唯一，且
$$
V(y\mid t)=\frac{c_y+(-1)^t d_y/s}{2}.
$$
不论 $W$ 是否满足完全正判据，制备族上的分支匹配都迫使唯一的全空间复线性延拓。以命题 146.1 的
$$
\psi_\nu\!\begin{pmatrix}x&u\\v&w\end{pmatrix}
=\frac12\begin{pmatrix}
\alpha x+w+\nu(u+v)&\alpha^2x+\nu\alpha v\\
\alpha^2x+\nu\alpha u&\alpha^2x
\end{pmatrix}
\qquad(x,u,v,w\in\mathbb C)
$$
表示，该延拓恰为
$$
\widehat{\mathcal J}_y=
\begin{cases}
c_y(\operatorname{Id}_L\otimes\psi_{d_y/c_y}),&c_y>0,\\
0,&c_y=0.
\end{cases}
$$
对于具有相同二元输入的报告矩阵，定义 $A\preceq B$ 表示 $A=SB$，其中 $S$ 为列随机的输出处理矩阵；互相满足此关系称为随机后处理等价。$B_s$ 是全部可由端点仪器复现的有限报告在此关系下的最大元，最大性按随机后处理等价理解，不要求字面报告字母表唯一。

进一步，对每个可由端点仪器复现的 $W$，两条件列的总变差满足
$$
\operatorname{TV}(W(\cdot\mid0),W(\cdot\mid1))
:=\frac12\sum_{y\in Y}|d_y|\le s.
$$
等号成立当且仅当每个非零行满足 $|d_y|=sc_y$，也当且仅当 $W$ 与 $B_s$ 随机后处理等价。等号时，按 $d_y$ 的正负作确定性分组即恢复 $B_s$，零行可任意分组；所恢复的是这个极端带噪报告，不是原始尖锐记录 $b$。总变差比较的是 $W$ 的条件列，不假定实际尖锐 Born 先验均匀，也不表示量子迹距离。仅有此总变差上界不足以推出端点复现：例如
$$
W_* =\begin{pmatrix}1/10&0\\9/10&1\end{pmatrix}
$$
的总变差为 $1/10<s$，却不满足逐行判据。结论只涉及所声明制备族的一次延长和这个报告与量子输出联合算子，不要求恢复与已丢弃记忆、不可访问制备标签或任意未来干预的关联，亦不附加熵、容量、最小记忆、多步闭合或普适经典性结论。

证明。命题 145.1、146.1 从命题 130.1 的字面生成器及命题 137.1 的空内部记录得到
$$
\chi_F=\operatorname{vec}_{LR}(C)|0\rangle_M
+s\operatorname{vec}_{LR}(CE_0)|1\rangle_M.
$$
继续使用同一个相关记忆时，固定 $b$ 的最终记忆两列系数矩阵是 $D_b=(s/\sqrt2)CZ^bJ$ 与 $sD_bE_0$，故其偏迹正是上述 $Q_b(C)$；这两个记忆列始终保持原振幅。写 $C=(r,t)$，引用命题 146.1 已由这些列证明的 Born 权重等式，得
$$
q(C):=\operatorname{Tr}Q(C)=(1+\alpha)\|r\|^2+\|t\|^2,
\qquad h(C)=\operatorname{Re}(r^\dagger t),
$$
$$
q_b(C):=\operatorname{Tr}Q_b(C)
=\frac{\|r+(-1)^bt\|^2+\alpha\|r\|^2}{2}
=\frac{q(C)}2+(-1)^bh(C),\qquad q_0(C)+q_1(C)=q(C).
$$
收缩条件给 $0\le q(C)\le1$，$C_0$ 可逆给 $q(C)=0$ 当且仅当 $F=0$；若 $F\ne0$，上式两个平方范数不可能同时为零，故两个 $q_b(C)$ 都严格为正。经典处理的条件独立性因此给
$$
p_y(C):=\operatorname{Tr}R_y(C)=\frac{c_yq(C)}2+d_yh(C),\qquad
\sum_yp_y(C)=q(C).
$$
当 $F\ne0$ 时，$p_y(C)=0$ 恰当该报告行全零。对 $p_y(C)>0$，成功条件下的报告概率为 $p_y(C)/q(C)$，报告态为
$$
\frac{R_y(C)}{p_y(C)}
=\sum_{b=0}^1\frac{W(y\mid b)q_b(C)}{p_y(C)}\,
\frac{Q_b(C)}{q_b(C)}.
$$
故归一化尖锐态的混合权重含有实际 Born 权重，不能直接以原始 $W(y\mid b)$ 代替。当 $F=0$ 时所有分支及概率为零，不定义任何条件态；零行亦不定义报告态。

现直接使用命题 145.1、146.1 对同一个全部复收缩族证明的张成性和唯一尖锐延拓。其适用性依赖于 $C_0$ 可逆、任意复 $D$ 可正缩放为 $FC_0$，以及可逆线性算子
$$
\mathcal L(A)=A+\alpha PAP,\qquad
\mathcal L^{-1}(A)=A-\alpha^2PAP,\qquad P=I_L\otimes E_0
$$
把四维秩一外积的 Hermitian 实张成族送到兼容输入的张成族。因此兼容等式确定整个 $M_4(\mathbb C)$ 上的复线性映射，不只确定兼容的正算子。该族包括全部复 $F$，无需任何 $F^{-1}$；固定原始有限记录集本身没有在这里承担张成性。由前述命题，尖锐分支的延拓是 $\operatorname{Id}_L\otimes\psi_{(-1)^b}$；其中右乘 $Z^bJ$ 对应右 Hilbert 因子的 $(Z^bJ)^{\mathsf T}=JZ^b$，所以独立复矩阵元 $u,v$ 的方向正是陈述中的方向。

将这两个尖锐延拓按一行 $W$ 线性相加，利用 $\psi_\nu$ 对实参数 $\nu$ 的仿射性，若 $c_y>0$ 就得
$$
\sum_bW(y\mid b)(\operatorname{Id}_L\otimes\psi_{(-1)^b})
=c_y(\operatorname{Id}_L\otimes\psi_{\nu_y}),\qquad \nu_y=d_y/c_y.
$$
它已匹配该行的所有实际未归一化分支，张成性保证唯一。若 $c_y=0$，非负性迫使整行及 $d_y$ 为零，张成性迫使延拓为零，无需定义 $\nu_y$。

命题 146.1 已对相互独立的复矩阵元证明 $\psi_\nu$ 完全正当且仅当 $\nu^2\le\alpha$，并在此闭区间给出 $K_j(\nu)$ 的 Kraus 分解，包括 $\nu=\pm s$ 时 $K_2=0$ 的边界。对 $c_y>0$，若全端点映射 $\widehat{\mathcal J}_y$ 完全正，将它依次与 $A\mapsto E_0\otimes A$、对 $L$ 的偏迹复合并除以 $c_y$，便得到完全正的 $\psi_{\nu_y}$。故 $d_y^2\le\alpha c_y^2$ 必要。反之，该不等式使
$$
\sqrt{c_y}\,I_L\otimes K_j(\nu_y)\qquad(j=1,2,3)
$$
给出所需分支的 Kraus 算子，零行取零映射。命题 146.1 的效应恒等式给
$$
\mathsf E_y=I_L\otimes\frac{c_yI_2+d_yX_{\rm P}}2,\qquad
X_{\rm P}=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$
列随机性给 $\sum_yc_y=2$、$\sum_yd_y=0$，故 $\sum_y\mathsf E_y=I_4$。这些完全正分支之和保迹，组成同一个与 $F$ 无关的仪器。这证明端点复现与逐行不等式的等价，包含全部零行和阈值边界。

为求随机因子，写
$$
B_s=\frac12\begin{pmatrix}1+s&1-s\\1-s&1+s\end{pmatrix},\qquad
\det B_s=s>0.
$$
若 $W=VB_s$，逐行比较和与差，必有
$$
V(y\mid0)+V(y\mid1)=c_y,\qquad
s\bigl(V(y\mid0)-V(y\mid1)\bigr)=d_y.
$$
解这两个等式即得唯一的所列 $V$。由于 $s>0$，其非负性恰等价于 $|d_y|\le sc_y$，也就是逐行完全正判据；两个列和分别为
$$
\sum_yV(y\mid t)=\frac{\sum_yc_y+(-1)^t\sum_yd_y/s}{2}=1.
$$
反过来，在该判据下这样定义 $V$，它列随机，且直接相乘给
$$
(VB_s)(y\mid b)=\frac{c_y+(-1)^bd_y}{2}=W(y\mid b).
$$
零行给出 $V$ 的零行，乘积方向为从 $b$ 经 $B_s$ 到 $t$ 再经 $V$ 到 $y$。

这一分解也在量子输出上实现所要求的等式。先做 $B_s$ 对应的边界仪器
$$
\mathcal I_t=\operatorname{Id}_L\otimes\psi_{(-1)^ts},\qquad t=0,1,
$$
再以 $V(y\mid t)$ 处理其报告并丢弃 $t$。它的第 $y$ 个分支在整个 $M_4(\mathbb C)$ 上满足
$$
\sum_tV(y\mid t)\mathcal I_t=\widehat{\mathcal J}_y,
$$
因为两系数的和为 $c_y$、乘上 $s$ 的差为 $d_y$；零行情形两边同为零。因此复现的是每个量子分支以及完整联合算子，非仅报告概率。$B_s$ 本身满足判据，而每个可复现 $W$ 都有 $W\preceq B_s$，所以它是所述最大元；同一等价类可有分裂后的更多标签，不是唯一字母表。另由 $d_y=s(V(y\mid0)-V(y\mid1))$ 可见
$$
\operatorname{TV}(W(\cdot\mid0),W(\cdot\mid1))
=s\operatorname{TV}(V(\cdot\mid0),V(\cdot\mid1)).
$$
$V$ 的两列总变差可以达到 $1$，例如 $W=B_s$ 时 $V=I_2$；上界 $s$ 针对的是 $W$。

最后逐行求和得到
$$
\frac12\sum_y|d_y|\le\frac s2\sum_yc_y=s,\qquad
s-\operatorname{TV}(W(\cdot\mid0),W(\cdot\mid1))
=\frac12\sum_y(sc_y-|d_y|).
$$
右边为有限个非负数的和，故等号恰当每个亏量为零。零行自动满足，非零行则有 $d_y=\pm sc_y\ne0$。将正号行放入 $Y_+$、负号行放入 $Y_-$，零行任意分入两者，记 $C_\pm=\sum_{y\in Y_\pm}c_y$。饱和及列和给
$$
C_++C_-=2,\qquad sC_+-sC_-=\sum_yd_y=0,
\qquad C_+=C_-=1.
$$
于是
$$
\sum_{y\in Y_+}W(y\mid b)=\frac{1+(-1)^bs}{2},\qquad
\sum_{y\in Y_-}W(y\mid b)=\frac{1-(-1)^bs}{2}.
$$
定义确定性列随机矩阵 $U$，在 $Y_+$ 上输出 $0$、在 $Y_-$ 上输出 $1$，便有 $UW=B_s$。同一分组还给 $\sum_{y\in Y_+}\widehat{\mathcal J}_y=\mathcal I_0$、$\sum_{y\in Y_-}\widehat{\mathcal J}_y=\mathcal I_1$，故极端报告的对应量子分支亦被恢复。

反之，任意列随机 $U$ 都满足有限和三角不等式
$$
\sum_t\left|\sum_yU(t\mid y)d_y\right|
\le\sum_{t,y}U(t\mid y)|d_y|=\sum_y|d_y|.
$$
若 $UW=B_s$，便有 $s=\operatorname{TV}(B_s(\cdot\mid0),B_s(\cdot\mid1))\le\operatorname{TV}(W(\cdot\mid0),W(\cdot\mid1))\le s$，所以必须饱和。结合总有的 $W=VB_s$，即得饱和与随机后处理等价的双向结论。全论证对任意非空有限 $Y$ 逐行成立，不需要字母表大小的上界。

为区分逐行判据与总体总变差，$W_*$ 的两行有
$$
(c_0,d_0)=(1/10,1/10),\qquad
(c_1,d_1)=(19/10,-1/10),\qquad
(\nu_0,\nu_1)=(1,-1/19).
$$
第一行违反 $\nu_0^2\le\alpha$，第二行满足该式，而 $\sum_yc_y\nu_y=0$ 且总变差仅为 $1/10$。由 $\alpha^2+\alpha=1$ 和 $0<\alpha<1$ 可得 $\alpha>1/2$，故 $1/10<s$ 及 $1/19^2<\alpha$。对每个非零 $F$，第一行的实际概率为 $q_0(C)/10>0$，不能作为不可能事件略去。

事实上，对任意列随机 $W$，即使违反完全正判据，也有 $|d_y|\le c_y$，故上述 $\mathsf E_y$ 的两个右因子特征值为 $(c_y\pm d_y)/2=W(y\mid0),W(y\mid1)\ge0$，且 $\sum_y\mathsf E_y=I_4$。从 $\psi_\nu$ 的迹式得到 $\operatorname{Tr}\widehat{\mathcal J}_y(A)=\operatorname{Tr}(\mathsf E_yA)$；对任意固定输出密度 $\tau$，映射 $A\mapsto\operatorname{Tr}(\mathsf E_yA)\tau$ 组成一个可实现这些概率的仪器。其完全正性可直接看出：若 $\mathsf E_y=\sum_j e_j|u_j\rangle\langle u_j|$、$\tau=\sum_k t_k|v_k\rangle\langle v_k|$ 为谱分解，则 $\sqrt{e_jt_k}|v_k\rangle\langle u_j|$ 是 Kraus 算子。但这不保证输出为所需的 $R_y(C)$。

此外，对所有 $W$，强制延拓的非选择和总为
$$
\sum_y\widehat{\mathcal J}_y
=\operatorname{Id}_L\otimes(2\psi_0)
=\operatorname{Id}_L\otimes\mathcal T,
$$
其中 $\mathcal T$ 是命题 146.1 已证明的完全正保迹通道。因而有效 POVM 和有效非选择和各自都不足以保证指定分支完全正；$W_*$ 与尖锐恒等报告 $W=I_2$ 都体现这个区别。命题 146.1 的负 Choi 二次型排除的是兼容族所迫使的全空间完全正延拓，实际 $Q_b(C)$ 与 $R_y(C)$ 始终是正算子，并无实际分支产生负态的结论。证毕。

<a id="entry-644"></a>

## 追加锚（本行以下为增补区）
<a id="section-148"></a>

## 148. 同一相关记忆的兼容锥与全部有限报告历史

**命题 148.1（联合提升不变性与固定端点仪器的有限历史复现）。** 沿用命题 130.1、137.1 的输出在前、活动记忆在后的次序，以及命题 147.1 的全部复左收缩制备族。记
$$
a=\frac{\sqrt5-1}{2},\qquad s=\sqrt a,\qquad a+a^2=1,\qquad
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
Z=\operatorname{diag}(1,-1),\qquad E_0=\operatorname{diag}(1,0),\qquad C_0=s^3J.
$$
这里 $a$ 即前述命题的 $\alpha$。各 qubit 均取固定正交标准基，$\dagger$ 表示共轭转置，$\operatorname{outer}(v)=vv^\dagger$，向量化采用左行右列约定
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1C_{ij}|i\rangle_L\otimes|j\rangle_R.
$$
原过程从同一个纯记忆 $m_0=s|0\rangle+a|1\rangle$ 出发，以
$$
T|0\rangle=|0\rangle_{\rm out}\otimes(s|0\rangle+a|1\rangle)_M,
\qquad T|1\rangle=|1\rangle_{\rm out}\otimes|0\rangle_M
$$
先发出 $L,R_0$，再在 $L$ 上施加任意 $F\in M_2(\mathbb C)$、$F^\dagger F\le I_2$ 的单 Kraus 成功分支。包括奇异 $F$ 与 $F=0$，保留共同成功旗标。置 $C=FC_0$，成功后实际联合向量与端点算子为
$$
\chi(C)=\operatorname{vec}_{LR}(C)\otimes|0\rangle_M
+s\operatorname{vec}_{LR}(CE_0)\otimes|1\rangle_M,
\qquad Q(C)=\operatorname{Tr}_M\operatorname{outer}(\chi(C)).
$$
模拟器只取得 $Q(C)$ 与成功旗标，不取得 $F$ 的描述、原始记忆或其副本。所有分支在归一化以前比较。

任取非空有限报告集 $Y$，固定同一个列随机矩阵 $W:Y\leftarrow\{0,1\}$，即 $W(y\mid b)\ge0$、$\sum_yW(y\mid b)=1$。每一步，原过程先对仍与端点相关的同一个活动记忆应用 $T$，发出下一右端点 $R_k$；随后在将退役的 $R_{k-1}$ 上测量固定基
$$
|\eta_b\rangle=\frac{|0\rangle+(-1)^b|1\rangle}{\sqrt2},\qquad b\in\{0,1\},
$$
丢弃该退役 qubit，并给定 $b_k$ 按 $W(\cdot\mid b_k)$ 抽取报告 $y_k$。这些经典随机抽取在给定原始记录后相互独立，且独立于其余系统及制备设置；不以任何原始结果或报告反馈选基、改动 $W$ 或操作记忆。原始结果只用于本步报告处理，保留的历史为 $h=(y_1,\ldots,y_m)$。每个有限时刻的比较对象恰为历史 $h$ 与 $L,R_m$ 的联合未归一化块，不包括原始记忆、退役 qubit、不可访问的纯化或任意插入干预。

按标准基将各个 $L,R_k$ 识别为同一个四维空间，定义
$$
A_b=Z^bJ,\qquad P=I_L\otimes E_0,\qquad
\mathcal L(X)=X+aPXP,\qquad
\mathcal L^{-1}(X)=X-a^2PXP,
$$
$$
\mathcal K=\left\{\sum_{j=1}^N\lambda_jQ(C_j):
N<\infty,\ \lambda_j\ge0,\ C_j\in M_2(\mathbb C)\right\}
=\mathcal L(\operatorname{PSD}_4),
$$
其中允许空和，$\operatorname{PSD}_4$ 是四维正半定算子锥。令
$$
Vv=v\otimes|0\rangle_M+sPv\otimes|1\rangle_M,
\qquad \Gamma(X)=V\mathcal L^{-1}(X)V^\dagger\quad(X\in\mathcal K).
$$
则 $\mathcal K$ 是闭凸锥，$\Gamma(X)\ge0$、$\operatorname{Tr}_M\Gamma(X)=X$，且任意上述正分解均给出
$$
\Gamma(X)=\sum_j\lambda_j\operatorname{outer}(\chi(C_j)).
$$
因此 $\Gamma$ 指定了一个不依赖分解的兼容联合提升；这不是所有可能联合扩张的唯一性断言，也不是在全部 $\operatorname{PSD}_4$ 上可实施的恢复映射。

定义从 $L,R,M$ 到 $L,R',M'$ 的实际原始分支算子
$$
B_b=(I_L\otimes\langle\eta_b|_R\otimes I_{R'}\otimes I_{M'})
(I_L\otimes I_R\otimes T),
\qquad
\mathcal H_y(\Omega)=\sum_bW(y\mid b)B_b\Omega B_b^\dagger.
$$
并置 $c_y=W(y\mid0)+W(y\mid1)$、$d_y=W(y\mid0)-W(y\mid1)$。对四个相互独立的复矩阵元定义
$$
\psi_\nu\!\begin{pmatrix}x&u\\v&w\end{pmatrix}
=\frac12\begin{pmatrix}
a x+w+\nu(u+v)&a^2x+\nu a v\\
a^2x+\nu a u&a^2x
\end{pmatrix},\qquad
\mathcal I_y=
\begin{cases}
c_y(\operatorname{Id}_L\otimes\psi_{d_y/c_y}),&c_y>0,\\
0,&c_y=0.
\end{cases}
$$
这是命题 147.1 的唯一复线性端点分支。对每个列随机 $W$，即使它不满足全空间完全正判据，仍有
$$
\mathcal I_yQ(C)=\frac a2\sum_bW(y\mid b)Q(CA_b),\qquad
\mathcal I_y(\mathcal K)\subseteq\mathcal K,\qquad
\mathcal H_y\Gamma(X)=\Gamma(\mathcal I_yX)\quad(X\in\mathcal K).
$$
锥不变性本身不等于全空间完全正性。

令 $\Omega_\varnothing=\Gamma(Q(C))$，以实际报告更新 $\Omega_{hy}=\mathcal H_y(\Omega_h)$，并定义 $R_h(C)=\operatorname{Tr}_M\Omega_h$。则对每个有限 $m\ge0$、每条 $h\in Y^m$ 同时有
$$
\Omega_h=\Gamma(R_h(C)),\qquad R_h(C)\in\mathcal K,
\qquad R_{hy}(C)=\mathcal I_y(R_h(C)),
$$
$$
\begin{aligned}
R_{(y_1,\ldots,y_m)}(C)
&=\left(\frac a2\right)^m
\sum_{b_1,\ldots,b_m\in\{0,1\}}
\left[\prod_{k=1}^m W(y_k\mid b_k)\right]
Q(CA_{b_1}\cdots A_{b_m})\\
&=(\mathcal I_{y_m}\circ\cdots\circ\mathcal I_{y_1})(Q(C)).
\end{aligned}
$$
空乘积、空记录和零次复合分别取恒等矩阵、唯一空记录和恒等映射。因此复现包括每个有限历史与最终端点的完整联合算子 $\sum_{h\in Y^m}|h\rangle\langle h|\otimes R_h(C)$。

存在一个不依赖 $F$、每步反复作用于完整 $M_4(\mathbb C)$ 并更新当前 $R$ 的固定完全正端点仪器，对全部复收缩 $F$ 复现上述所有有限历史，当且仅当
$$
d_y^2\le a c_y^2\qquad\text{对每个 }y\in Y.
$$
零行和等号均包括在内；满足时该仪器就是 $(\mathcal I_y)_y$，无需额外的时间长度条件。

写 $q_F=\operatorname{Tr}Q(C)$。有
$$
q_F=\|C\|_F^2+a\|CE_0\|_F^2\le1,\qquad
\sum_{h\in Y^m}\operatorname{Tr}R_h(C)=q_F,\qquad
\sum_y\operatorname{Tr}R_{hy}(C)=\operatorname{Tr}R_h(C).
$$
若 $F\ne0$，每条有限原始记录都有严格正权重；报告历史 $h$ 的迹严格为正当且仅当它使用的每一行 $W(y_k\mid\cdot)$ 非零。此条件在 $m=0$ 时为空条件。若 $F=0$，所有联合块和端点块均为零。只在相应分母严格为正时定义
$$
\Pr(h\mid\mathrm{success})=\frac{\operatorname{Tr}R_h(C)}{q_F},\qquad
\Pr(y\mid h,\mathrm{success})=
\frac{\operatorname{Tr}R_{hy}(C)}{\operatorname{Tr}R_h(C)},
\qquad \rho_h=\frac{R_h(C)}{\operatorname{Tr}R_h(C)}.
$$
这些结论也按正线性性适用于有限正初始混合，但其实际初始联合态必须是所指定的 $\Gamma(X)$；若将混合作为成功子态，还要求 $\operatorname{Tr}X\le1$。结论不扩大到任意初始联合扩张。

允许操作的边界可由一个右端点幺正精确显示：$|00\rangle\langle00|\in\mathcal K$，但在右端点作用 Hadamard 后得到的 $|0+\rangle\langle0+|$ 不属于 $\mathcal K$。因而该锥并不对任意端点干预封闭。这里的模拟器量子寄存器与随长度增加的保留经典历史是不同资源；上述结论不判定经典状态表示、量子记忆最小性或总记录存储量，也不涉及无限历史条件化。

证明。命题 130.1 给出 $T^\dagger T=I_M$。命题 137.1 的空内部记录和命题 147.1 的成功制备展开，在本命题完全相同的 $m_0,T$、输出次序及复向量化下，给出实际初态 $\chi(FC_0)$；所以 $\Omega_\varnothing=\operatorname{outer}(\chi(C))$，且收缩条件使其迹不超过一。

先在联合向量层验证延长。对任意复 $C$，将其两列写为 $r,t\in\mathbb C^2$，于是
$$
\chi(C)=r\otimes|0\rangle_R\otimes|0\rangle_M
+t\otimes|1\rangle_R\otimes|0\rangle_M
+s r\otimes|0\rangle_R\otimes|1\rangle_M.
$$
记 $e=(-1)^b$。在 $T$ 发出 $R'$ 后，按 $\langle\eta_b|$ 收缩退役 $R$；bra 使用共轭系数 $\overline{\eta_{b,0}}=1/\sqrt2$、$\overline{\eta_{b,1}}=e/\sqrt2$，不对列向量 $r,t$ 取共轭。对每个左指标 $i$，所得四个 $(R',M')=(0,0),(0,1),(1,0),(1,1)$ 系数依次为
$$
\frac{s}{\sqrt2}(C_{i0}+eC_{i1}),\qquad
\frac{a}{\sqrt2}(C_{i0}+eC_{i1}),\qquad
\frac{s}{\sqrt2}C_{i0},\qquad 0.
$$
这是逐项将 $T|0\rangle=s|00\rangle+a|01\rangle$、$T|1\rangle=|10\rangle$ 代入所得，没有在下一次发出以前擦除活动记忆。因为
$$
CA_b=(r+et,\ r),\qquad a=s^2,
$$
这四个系数恰给出字面的联合恒等式
$$
B_b\chi(C)=\frac{s}{\sqrt2}\chi(CA_b).
$$
再次延长是在已有系数矩阵的右侧乘新的 $A_b$，故时间较早的结果在乘积中位于较晚因子的左侧。该恒等式保留两条记忆列及其相干交叉项，强于仅比较端点偏迹。

现证锥和提升的陈述。由 $P^2=P$ 及 $a-a^2-a^3=0$，两种次序复合 $X\mapsto X+aPXP$ 与 $X\mapsto X-a^2PXP$ 都给恒等映射。又
$$
P\operatorname{vec}(C)=\operatorname{vec}(CE_0),\qquad
Q(C)=\mathcal L(\operatorname{outer}(\operatorname{vec}(C))).
$$
四维正半定矩阵的有限谱分解写作 $S=\sum_j\lambda_jv_jv_j^\dagger$，$\lambda_j\ge0$；将每个 $v_j$ 按既定次序还原为矩阵 $C_j$，便有 $\mathcal L(S)=\sum_j\lambda_jQ(C_j)$。反向包含由同一个等式立即得到。由此 $\mathcal K=\mathcal L(\operatorname{PSD}_4)$，且是凸锥。若 $X_n\in\mathcal K$ 收敛于 $X$，连续的逆映射给 $\mathcal L^{-1}(X_n)\to\mathcal L^{-1}(X)$；正半定锥闭，故后者正半定，$X\in\mathcal K$。这里使用的是可逆性，不是一般线性映射都保持闭集的断言。

对 $S=\mathcal L^{-1}(X)\ge0$，合同 $VSV^\dagger$ 正半定，而对记忆取偏迹给
$$
\operatorname{Tr}_M(VSV^\dagger)=S+aPSP=\mathcal L(S)=X.
$$
因 $V\operatorname{vec}(C)=\chi(C)$，任一正分解都给所列 $\Gamma(X)$，且逆映射唯一使它与分解的选择无关。还可直接核对
$$
V^\dagger V=I_4+aP,\qquad
\operatorname{Tr}\Gamma(X)=\operatorname{Tr}((I_4+aP)S)
=\operatorname{Tr}\mathcal L(S)=\operatorname{Tr}X.
$$
此等式是提升在兼容锥上的迹恒等式，不将 $V$ 称为等距。

应用命题 147.1 前，核对其全部制备与报告假设：本命题同样允许所有复收缩 $F$，取相同可逆的 $C_0=s^3J$、共同成功旗标、相同的固定 $\eta_b$，且只以一个有限非空列随机 $W$ 独立处理原始结果；模拟器没有 $F$ 或原始记忆。本命题的 $a$、$\mathcal L$ 与该命题的 $\alpha$、$\mathcal L$ 一致，右乘 $A_b$ 在右 Hilbert 因子上对应 $A_b^{\mathsf T}=JZ^b$，故 $\psi_\nu$ 中独立复元 $u,v$ 的方向也一致。因此该命题给出唯一全空间复线性分支 $\mathcal I_y$ 及其一步匹配。这个代数匹配对任意复矩阵 $D$ 都成立：令
$$
t_D=\max\{1,\|DC_0^{-1}\|_{\rm op}\},\qquad
F_D=t_D^{-1}DC_0^{-1},
$$
则 $F_D^\dagger F_D\le I_2$、$D=t_DF_DC_0$；$Q$ 的二次齐次性和 $\mathcal I_y$ 的线性性把一步等式延伸到 $D$。因而即使历史中的系数矩阵未写成允许收缩，仍可使用
$$
\mathcal I_yQ(D)=\frac a2\sum_bW(y\mid b)Q(DA_b).
$$
零行两边为零，不定义 $d_y/c_y$。该式对所有 $W$ 给出锥不变性，不需要完全正前提。

由已证联合子分支恒等式，在每个生成元上有
$$
\begin{aligned}
\mathcal H_y\Gamma(Q(D))
&=\sum_bW(y\mid b)\operatorname{outer}(B_b\chi(D))\\
&=\frac a2\sum_bW(y\mid b)\operatorname{outer}(\chi(DA_b))
=\Gamma(\mathcal I_yQ(D)).
\end{aligned}
$$
两边对有限正和均为线性，故此交织恒等式扩展到整个 $\mathcal K$。特别地，它比较的是下一步需要的实际联合态，不是从端点态相等推断任意隐藏关联相等。

对报告历史长度作同时归纳。空历史时 $R_\varnothing=Q(C)\in\mathcal K$，$\Omega_\varnothing=\Gamma(R_\varnothing)$。假设某个实际历史 $h$ 满足这两个性质。经典抽取的条件独立性和没有反馈保证，无论此前是哪条原始记录，下一报告 $y$ 都作用同一个 $\mathcal H_y$；由交织恒等式及锥不变性，
$$
\Omega_{hy}=\mathcal H_y\Gamma(R_h)=\Gamma(\mathcal I_yR_h),\qquad
\mathcal I_yR_h\in\mathcal K.
$$
取本式的记忆偏迹，得到 $R_{hy}=\mathcal I_yR_h$，再代回即得 $\Omega_{hy}=\Gamma(R_{hy})$。这也适用于零块，归纳从未除以迹。逐次展开分支和给出陈述中的有限乘积公式；不同步骤的 $W$ 因子相乘，正是所假设的条件独立随机处理。因而所有有限 $m$ 的结论来自归纳。实际活动记忆始终留在 $\Omega_h$ 中；$R_h$ 的偏迹仅用于端点比较，并非在原过程下一步以前施行擦除或重置。

若逐行不等式成立，命题 147.1 的完全正及 Kraus 结论直接给出 $\mathcal I_y$ 为完全正分支、$\sum_y\mathcal I_y$ 保迹，包括零行与 $|d_y|=sc_y$ 的边界。因此同一个固定仪器可以逐步作用在当前端点寄存器上，刚才的归纳证明它复现全部有限联合块。反之，若存在所要求的全部复 $F$、全部有限长度的固定端点仪器，其长度一的每个分支就满足命题 147.1 的匹配等式；该命题的唯一性迫使分支等于这里的 $\mathcal I_y$。任一行违反不等式即使这个强制分支不完全正，故仪器不可能存在。这里不重新要求更强的时间阈值。

最后核对权重及边界。记忆偏迹消去不同正交记忆列之间的交叉项，故对任意非零 $D$，
$$
\operatorname{Tr}Q(D)=\|D\|_F^2+a\|DE_0\|_F^2>0.
$$
这是严格正迹，不是正定性。$C_0$ 与每个 $A_b$ 都可逆，所以 $F\ne0$ 时任意有限原始乘积 $CA_{b_1}\cdots A_{b_m}$ 非零。原始分支的正因子 $(a/2)^m$ 保证其权重严格为正。对于一条报告历史，若某个被用行全零，有限和的每个系数都为零；若每个被用行非零，可逐步选取一个 $b_k$ 使 $W(y_k\mid b_k)>0$，该原始词在和中有严格正系数和严格正迹，因此整个报告块的迹严格为正。空记录与零 $F$ 分别给所述边界。

从 $T^\dagger T=I_M$ 和测量基完备性得到 $\sum_bB_b^\dagger B_b=I_{LRM}$，再用 $W$ 的列和，有
$$
\sum_y\operatorname{Tr}\mathcal H_y(\Omega)=\operatorname{Tr}\Omega
\qquad(\Omega\ge0).
$$
逐前缀应用并用 $\operatorname{Tr}\Omega_h=\operatorname{Tr}R_h$，就得到所有迹的守恒式与陈述中的条件概率。非选择的后继量子态已经演化；这些式子不声称 $\sum_yR_{hy}=R_h$。同样，报告条件态的混合必须使用原始分支的 Born 权重。具体地，写 $D_{\mathbf b}=CA_{b_1}\cdots A_{b_m}$、$w_{h,\mathbf b}=\prod_kW(y_k\mid b_k)$，在正分母处有
$$
\rho_h=\sum_{\mathbf b}
\frac{(a/2)^m w_{h,\mathbf b}\operatorname{Tr}Q(D_{\mathbf b})}
{\operatorname{Tr}R_h}\,
\frac{Q(D_{\mathbf b})}{\operatorname{Tr}Q(D_{\mathbf b})}.
$$
零权重项省去；在非零 $F$ 情形所写原始分母均正。有限正初始混合的结论由同样的联合提升和正线性性得出，而不引入额外的初始联合态。若 $z$ 是继续执行同一协议的有限报告词、$\mathcal I_z$ 是对应次序的复合，且 $0\le E\le I_4$ 是最后一次端点效应，则正前缀处的联合条件概率为 $\operatorname{Tr}(E\mathcal I_z(R_h))/\operatorname{Tr}R_h$；这只在继续协议的末端施测，不许可在中途插入任意操作。

为证所附干预边界，记 $E_{00}=|0\rangle\langle0|\in M_2(\mathbb C)$。由 $a(1+a)=1$，
$$
|00\rangle\langle00|=aQ(E_{00})\in\mathcal K.
$$
右 Hadamard 将其变为 $X_+=|0+\rangle\langle0+|$。$\mathcal L^{-1}(X_+)$ 在左指标为 $0$ 的右二阶块为
$$
\frac12\begin{pmatrix}1-a^2&1\\1&1\end{pmatrix}
=\frac12\begin{pmatrix}a&1\\1&1\end{pmatrix},\qquad
\det=\frac{a-1}{4}<0.
$$
故 $\mathcal L^{-1}(X_+)$ 非正半定，$X_+\notin\mathcal K$。同一个逆像还是形式表达式 $V\mathcal L^{-1}(X_+)V^\dagger$ 在记忆 $|0\rangle$ 上的压缩，因此该表达式也非正半定；这排除了把所给 $\Gamma$ 公式当作全正半定锥上的正恢复映射。此计算仅说明命题的代数适用边界，没有在所定义的原协议中添加这次幺正操作。证毕。

<a id="entry-646"></a>

## 追加锚（本行以下为增补区）

<a id="section-149"></a>

## 149. 单步有限报告的端点纠缠与右通道的纠缠破坏判据

**命题 149.1（固定单滤波下的逐报告纠缠分类与旗标通道判据）。** 沿用命题 130.1、137.1、145.1—148.1 的纯记忆、输出次序及复向量化。各 qubit 取正交标准基，$\dagger$ 表示共轭转置，$\mathsf T$ 表示普通转置，$\operatorname{outer}(v)=vv^\dagger$，并置
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
\alpha+\alpha^2=1,\qquad
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
Z=\operatorname{diag}(1,-1),\qquad
E_0=\operatorname{diag}(1,0),\qquad E_1=\operatorname{diag}(0,1).
$$
初始记忆为 $m_0=s|0\rangle+\alpha|1\rangle$，$m_1=|0\rangle$，等距为 $T|j\rangle=|j\rangle_{\rm out}\otimes m_j$。先恰好发出 $L,R_0$，再对 $L$ 施加一个固定的复成功 Kraus 算子 $F$，$F^\dagger F\le I_2$，保留共同成功事件。以下关于制备态的断言分别量化于每一个这样的固定 $F$，包括奇异矩阵和零矩阵；模拟器仅接收约化端点与成功旗标，不取得经典 $F$ 标签、原始记忆或其副本；这里不把若干不同 $F$ 的隐藏随机选择平均为单次制备。记
$$
C_0=s^3J,\qquad C=FC_0,\qquad
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1C_{ij}|i\rangle_L\otimes|j\rangle_R,
$$
$$
\chi(C)=\operatorname{vec}_{LR_0}(C)\otimes|0\rangle_M
+s\operatorname{vec}_{LR_0}(CE_0)\otimes|1\rangle_M,\qquad
Q(C)=\operatorname{outer}(\operatorname{vec}(C))
+\alpha\operatorname{outer}(\operatorname{vec}(CE_0)),\qquad
q_F=\operatorname{Tr}Q(C).
$$
$\chi(C)$ 是实际成功后的联合向量，$Q(C)$ 是其记忆偏迹。端点使用完整 $\mathbb C^2\otimes\mathbb C^2$，不要求滤波后的态仍在原来的无 $11$ 支撑内。

保留同一个原始相关记忆，以 $T$ 发出 $R_1$，在退役的 $R_0$ 上测量固定基
$$
|\eta_b\rangle=\frac{|0\rangle+(-1)^b|1\rangle}{\sqrt2},\qquad b\in\{0,1\},
$$
对最终记忆取偏迹。给定 $b$，以一个固定的有限列随机矩阵 $W:Y\leftarrow\{0,1\}$ 独立于其余系统和制备设置抽取报告 $y$；$Y$ 非空，$W(y\mid b)\ge0$、$\sum_yW(y\mid b)=1$，全过程无反馈。只保留 $y,L,R_1$。命题 145.1、147.1、148.1 的实际单步分支与其 Born 权重为
$$
Q_b(C)=\frac\alpha2 Q(CZ^bJ),\qquad
R_y(C)=\sum_{b=0}^1W(y\mid b)Q_b(C),\qquad
r_y(C)=\operatorname{Tr}R_y(C),\qquad \sum_yr_y(C)=q_F.
$$
这里相加的是未归一化算子。写
$$
c_y=W(y\mid0)+W(y\mid1),\qquad
 d_y=W(y\mid0)-W(y\mid1),\qquad
 d_y^2\le\alpha c_y^2\quad(y\in Y).
$$
按命题 147.1 的逐行完全正判据，匹配全部复收缩制备的固定端点仪器为 $\mathcal I_y=\operatorname{Id}_L\otimes\phi_y$，其中
$$
\phi_y=\begin{cases}c_y\psi_{d_y/c_y},&c_y>0,\\0,&c_y=0,\end{cases}
\qquad
\psi_\nu\!\begin{pmatrix}x&u\\v&w\end{pmatrix}
=\frac12\begin{pmatrix}
\alpha x+w+\nu(u+v)&\alpha^2x+\nu\alpha v\\
\alpha^2x+\nu\alpha u&\alpha^2x
\end{pmatrix},
\qquad x,u,v,w\in\mathbb C.
$$
定义保留有限正交旗标的右通道
$$
\mathcal J_W:\mathcal L(R_0)\longrightarrow\mathcal L(\mathbb C^Y\otimes R_1),\qquad
\mathcal J_W(X)=\sum_{y\in Y}|y\rangle\langle y|\otimes\phi_y(X).
$$
可分密度按命题 132.1、133.1 的有限凸乘积密度和定义：在指定分割 $U\mid V$ 上，$\rho=\sum_{k=1}^N p_k\rho_k^U\otimes\rho_k^V$，其中 $p_k\ge0$、$\sum_kp_k=1$，两因子皆为正半定单位迹算子；不可分者称为纠缠态。称 $\mathcal J_W$ 为纠缠破坏通道（EB），是指对每个有限维辅助空间 $A$ 及每个 $A\otimes R_0$ 上的密度 $\sigma$，$(\operatorname{Id}_A\otimes\mathcal J_W)(\sigma)$ 均在 $A\mid(\mathbb C^Y\otimes R_1)$ 上可分。这是右通道的性质；$\operatorname{Id}_L\otimes\mathcal J_W$ 把 $L$ 保持不变，其相对于另一个外部参考的 EB 性不是此定义。

在上述假设下，有以下四项结论。

1. 若 $F\ne0$，则 $r_y(C)>0$ 当且仅当 $c_y>0$。对这样的报告，成功条件下的报告概率为 $r_y(C)/q_F$，而条件端点密度 $R_y(C)/r_y(C)$ 在 $L\mid R_1$ 上纠缠，当且仅当 $\operatorname{rank}F=2$ 且 $d_y\ne0$。
2. 若 $F\ne0$，保留报告的完整归一化输出
$$
\rho_F^W=(\operatorname{Id}_L\otimes\mathcal J_W)\bigl(Q(C)/q_F\bigr)
$$
在 $L\mid(\mathbb C^Y\otimes R_1)$ 上纠缠，当且仅当 $\operatorname{rank}F=2$ 且存在 $y$ 使 $d_y\ne0$。
3. $\mathcal J_W$ 是 EB，当且仅当 $W(\cdot\mid0)=W(\cdot\mid1)$。
4. 丢弃旗标给出命题 145.1、147.1 的同一个通道
$$
\mathcal T:=\operatorname{Tr}_Y\circ\mathcal J_W,\qquad
\mathcal T\!\begin{pmatrix}x&u\\v&w\end{pmatrix}
=x\tau_0+wE_0,\qquad
\tau_0=\begin{pmatrix}\alpha&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix}.
$$
此右通道对每个有限维辅助输入均为 EB。对不满足逐行 CP 不等式的实际列随机 $W$，总和 $\sum_y\phi_y=\mathcal T$ 及实际算子恒等式 $\sum_yR_y(C)=(\operatorname{Id}_L\otimes\mathcal T)(Q(C))$ 仍成立；其各个强制端点分支则不必完全正。

若 $F=0$，所有上述实际算子均为零，不定义成功条件密度；若 $c_y=0$，该报告算子为零，不定义报告条件密度。第一、二项仅分类这一次延长的输出。

证明。命题 147.1 的一步匹配与命题 148.1 的同记忆联合收缩均适用：纯初态、$T$、复 $F$ 的全部允许范围、固定 $\eta_b$、给定 $b$ 的独立报告及无反馈假设完全相同。故可直接使用所列 $Q_b(C)$ 与 $\mathcal I_y(Q(C))=R_y(C)$。各 $\phi_y$ 完全正且其和保迹，添加正交旗标后仍完全正保迹，所以 $\mathcal J_W$ 确为右通道。尤其 $Q_b(C)$ 同时保留两个正交记忆列的外积，系数分别为 $\alpha/2$ 与 $\alpha^2/2$。

先沿用命题 147.1 的事件计数。每个 $Z^bJ$ 可逆，故 $C\ne0$ 时
$$
q_b(C):=\operatorname{Tr}Q_b(C)
=\frac\alpha2\left(\|CZ^bJ\|_F^2
+\alpha\|CZ^bJE_0\|_F^2\right)>0.
$$
$C_0$ 可逆给出 $C\ne0$ 当且仅当 $F\ne0$，并给出 $\operatorname{rank}C=\operatorname{rank}F$。因此非负和 $r_y(C)=\sum_bW(y\mid b)q_b(C)$ 严格为正恰当该行非零，即 $c_y>0$。若写 $C=(r,t)$，同一 Born 公式还给
$$
q_F=(1+\alpha)\|r\|^2+\|t\|^2,\qquad
q_b(C)=q_F/2+(-1)^b\operatorname{Re}(r^\dagger t),\qquad
r_y(C)=c_yq_F/2+d_y\operatorname{Re}(r^\dagger t).
$$
在正分母处，条件混合准确为
$$
\frac{R_y(C)}{r_y(C)}
=\sum_{b=0}^1\frac{W(y\mid b)q_b(C)}{r_y(C)}
\frac{Q_b(C)}{q_b(C)}.
$$
故须先相加未归一化算子，再除以其总迹。

固定一行，简记 $c=c_y$、$d=d_y$，在 $00,01,10,11$ 次序下置 $D(c,d)=D_y:=R_y(I_2)$。从两列公式代入 $C=I_2$，使用 $\alpha(1+\alpha)=1$，逐项得到
$$
D_y=\frac12\begin{pmatrix}
c&\alpha c&d&0\\
\alpha c&\alpha c&\alpha d&0\\
d&\alpha d&c&0\\
0&0&0&0
\end{pmatrix}.
$$
对任意复 $C$，$\operatorname{vec}(CA)=(C\otimes I_2)\operatorname{vec}(A)$；将它同时用于 $A=Z^bJ$ 及 $A=Z^bJE_0$，得
$$
R_y(C)=(C\otimes I_2)D_y(C^\dagger\otimes I_2).
$$
这是全复矩阵恒等式，不限制 $C$ 的支撑。可分正算子的有限乘积分解在左合同下仍为有限正乘积和。

以 $\operatorname{PT}_{R_1}(|ij\rangle\langle kl|)=|il\rangle\langle kj|$ 定义右偏转置。逐块转置给
$$
D_y^{\operatorname{PT}_{R_1}}
=\frac12\begin{pmatrix}
c&\alpha c&d&\alpha d\\
\alpha c&\alpha c&0&0\\
d&0&c&0\\
\alpha d&0&0&0
\end{pmatrix},\qquad
\det\left(D_y^{\operatorname{PT}_{R_1}}\big|_{\{00,11\}}\right)
=-\frac{\alpha^2d^2}{4}.
$$
若 $c>0$、$d\ne0$，向量
$$
h=|11\rangle-\frac{\alpha d}{c}|00\rangle
\quad\text{满足}\quad
h^\dagger D_y^{\operatorname{PT}_{R_1}}h
=-\frac{\alpha^2d^2}{2c}<0.
$$
偏转置与左合同可交换，故若 $C$ 可逆，令 $k=((C^\dagger)^{-1}\otimes I_2)h$，则
$$
k^\dagger R_y(C)^{\operatorname{PT}_{R_1}}k
=h^\dagger D_y^{\operatorname{PT}_{R_1}}h<0.
$$
这里传递的是负二次型方向，未要求任意左合同后同一个坐标主子式仍负；逆矩阵仅用于此代数等式。若 $B\ge0$，谱分解 $B=\sum_j\lambda_jz_jz_j^\dagger$ 给出 $B^{\mathsf T}=\sum_j\lambda_j\overline{z_j}\,\overline{z_j}^{\dagger}\ge0$。因此有限正乘积和的右偏转置必正半定，正迹归一化也不改变负二次型的符号。由此 $\operatorname{rank}C=2$、$d\ne0$ 时条件态纠缠；此论证只用偏转置正性的必要条件。

若 $d=0$，则
$$
D(c,0)=\frac c2\left((1+\alpha)E_0\otimes\tau_0+E_1\otimes E_0\right),\qquad
\operatorname{Tr}\tau_0=1,\qquad \det\tau_0=\alpha^5>0.
$$
$\tau_0$ 的首个对角元 $\alpha>0$，故它是正定密度。于是任意左合同均保留上述有限正乘积和；正迹时按各项的迹归一化即得可分密度。若 $C$ 非零且秩一，写 $C=\ell v^{\mathsf T}$，$\ell,v\in\mathbb C^2\setminus\{0\}$，这里 $\mathsf T$ 是普通转置。因此 $\operatorname{vec}(C)=\ell\otimes v$，且每个尖锐子分支为
$$
Q_b(C)=\operatorname{outer}(\ell)\otimes
\frac\alpha2\left[
\operatorname{outer}(JZ^bv)
+\alpha\operatorname{outer}(E_0JZ^bv)\right].
$$
按 $W(y\mid b)$ 相加仍有同一个正左因子，正迹时是乘积密度。结合零矩阵及前述正概率判据，第一项得证。这里秩二判据指 $F$；事实上对每个允许的非零行，$D_y$ 前三维主块满足
$$
\det\left(D_y\big|_{\{00,01,10\}}\right)
=\frac{\alpha^3c(c^2-d^2)}8>0,
$$
因为 $d^2\le\alpha c^2<c^2$。由最后一行、列为零，$D_y$ 的秩为三；可逆 $C$ 的报告态也秩三。

对任意有限旗标块态，可分性恰等价于每个正迹块归一化后的可分性。必要性来自右侧局部压缩 $I_L\otimes\langle y|\otimes I_{R_1}$：它把有限正乘积和送为有限正乘积和。充分性可显式写出：若
$$
\frac{R_y(C)}{r_y(C)}=\sum_kp_{yk}A_{yk}\otimes B_{yk},\qquad
\sum_kp_{yk}=1,
$$
则在 $L,\mathbb C^Y,R_1$ 次序下
$$
\rho_F^W=\sum_{\substack{y\in Y\\r_y(C)>0}}\sum_k
\frac{r_y(C)}{q_F}p_{yk}\,
A_{yk}\otimes\bigl(|y\rangle\langle y|\otimes B_{yk}\bigr)
$$
是有限凸乘积密度和，因 $\sum_yr_y(C)=q_F$。这说明旗标的对角性本身不蕴含此分割上的可分性。应用第一项即得第二项。

为证明第四项，直接引用命题 145.1 的总通道公式及命题 147.1 对任意列随机 $W$ 的总和恒等式：$\sum_yc_y=2$、$\sum_yd_y=0$ 消去全部对比项，给出 $\sum_y\phi_y=2\psi_0=\mathcal T$。有限辅助空间的可分分解正是命题 133.1 所用的正对角块论证：对 $A\otimes R_0$ 上任意密度 $\sigma$，置
$$
A_j=(I_A\otimes\langle j|)\sigma(I_A\otimes|j\rangle)\ge0,\qquad
w_j=\operatorname{Tr}A_j,\qquad w_0+w_1=1.
$$
于是
$$
(\operatorname{Id}_A\otimes\mathcal T)(\sigma)
=A_0\otimes\tau_0+A_1\otimes E_0
=\sum_{\substack{j=0,1\\w_j>0}}w_j\frac{A_j}{w_j}\otimes\tau_j,
\qquad \tau_1=E_0.
$$
正半定且迹零的块为零，故省略它们后，右式是明确的有限凸乘积密度分解。这证明任意有限辅助系统上的 EB 性，也证明保留 $L$ 与另一个外部参考的纠缠并不在此消除范围内。总和等式本身只用列随机性，故亦适用于逐行 CP 域外的 $W$；这不改变命题 147.1 对其独立分支的完全正判据。

若所有 $d_y=0$，则两列相同，记 $p_y=W(y\mid0)=W(y\mid1)$。此时 $c_y=2p_y$，从而
$$
\phi_y=p_y\mathcal T,\qquad
\mathcal J_W(X)=\left(\sum_yp_y|y\rangle\langle y|\right)\otimes\mathcal T(X).
$$
将旗标密度附在刚才分解的右因子上，对每个有限辅助输入仍可分，故 $\mathcal J_W$ 是 EB。

反之，设某个 $d_y\ne0$。取实际允许的固定滤波
$$
F_*=\frac14J^{-1},\qquad
\|F_*\|_{\rm op}\le\|F_*\|_F=\frac{\sqrt3}{4}<1,\qquad
C=F_*C_0=\kappa I_2,\qquad \kappa=\frac{s^3}{4}.
$$
其成功概率为
$$
q_{F_*}=\kappa^2\operatorname{Tr}Q(I_2)
=\frac{\alpha^3}{16}(2+\alpha)=\frac\alpha{16}>0,
\qquad 2+\alpha=\alpha^{-2}.
$$
因此可在 EB 定义中取辅助 $A=L$ 及物理兼容输入
$$
\sigma_*=\frac{Q(I_2)}{2+\alpha}
=\frac{\operatorname{outer}(|00\rangle+|11\rangle)
+\alpha\operatorname{outer}(|00\rangle)}{2+\alpha}.
$$
由第一、二项，该输入的带旗标输出纠缠，遂反驳 EB。这给出第三项的必要性，所用输入正是原相关记忆经 $F_*$ 成功制备的约化密度。

具体取命题 147.1 的允许边界
$$
W=B_s=\frac12\begin{pmatrix}1+s&1-s\\1-s&1+s\end{pmatrix}.
$$
两行分别为 $(c_y,d_y)=(1,s),(1,-s)$，均满足 $d_y^2=\alpha c_y^2$。因 $\operatorname{Tr}D_y=(2+\alpha)/2$，各个实际成功与报告的联合概率、成功条件下的报告概率以及归一化输出为
$$
r_y(\kappa I_2)=\kappa^2\frac{2+\alpha}{2}=\frac\alpha{32},\qquad
\frac{r_y(\kappa I_2)}{q_{F_*}}=\frac12,\qquad
\theta_y=\frac{2D_y}{2+\alpha}.
$$
其右偏转置的 $00,11$ 主子式精确为
$$
\det\left(\theta_y^{\operatorname{PT}_{R_1}}\big|_{\{00,11\}}\right)
=-\frac{\alpha^2s^2}{(2+\alpha)^2}=-\alpha^7<0.
$$
若改取 $B_t=\frac12\begin{pmatrix}1+t&1-t\\1-t&1+t\end{pmatrix}$，$0<|t|<s$，同一子式为 $-\alpha^2t^2/(2+\alpha)^2<0$。因此允许域内部任意小的非零对比度也保留此纠缠，没有非零幅度下界。每个允许分支局部作用于右因子，故可分输入的有限正乘积和经其作用仍是有限正乘积和；这里保留的是已有纠缠。

最后，固定 $F$ 的限定可由同一计算显示。以相等的隐藏先验选择
$$
F_0=\frac14J^{-1},\qquad F_1=\frac14ZJ^{-1}.
$$
两者皆为可逆收缩，分别给 $C_0'=\kappa I_2$、$C_1'=\kappa Z$，成功概率同为 $\alpha/16$。忘记这一选择后，报告的平均未归一化算子是
$$
\frac{R_y(C_0')+R_y(C_1')}{2}
=\frac{\kappa^2}{2}\left[D(c_y,d_y)
+(Z\otimes I_2)D(c_y,d_y)(Z\otimes I_2)\right]
=\kappa^2D(c_y,0).
$$
其每个正迹报告块由上面的乘积分解可分。这是由 $F_0/\sqrt2,F_1/\sqrt2$ 给出的平均多 Kraus 成功制备，属于单个固定 $F$ 分类之外。证毕。

本命题中可分态的偏转置正性必要条件参见 Asher Peres，*Separability Criterion for Density Matrices*，Physical Review Letters 77，1413–1415（1996），[DOI:10.1103/PhysRevLett.77.1413](https://doi.org/10.1103/PhysRevLett.77.1413)；纠缠破坏通道与测量后制备的术语参见 M. Horodecki、P. W. Shor、M. B. Ruskai，*Entanglement Breaking Channels*，Reviews in Mathematical Physics 15，629–641（2003），[DOI:10.1142/S0129055X03001709](https://doi.org/10.1142/S0129055X03001709)。

<a id="entry-648"></a>

## 追加锚（本行以下为增补区）

<a id="section-150"></a>

## 150. 全部报告历史保留下的兼容端点四步可分性与右通道五步纠缠破坏

**命题 150.1（固定报告仪器的两个尖锐统一消纠缠时域）。** 沿用命题 145.1—149.1 的制备与命题 148.1 的同记忆连续协议，置
$$
a=\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt a,\qquad a+a^2=1,\qquad
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
Z=\operatorname{diag}(1,-1),\qquad E_0=\operatorname{diag}(1,0).
$$
各 qubit 取固定正交标准基，$\dagger$ 为共轭转置，$\mathsf T$ 为普通转置，$\operatorname{outer}(v)=vv^\dagger$，且
$$
\operatorname{vec}(C)=\sum_{i,j=0}^1C_{ij}|i\rangle_L|j\rangle_R,\qquad
Q(C)=\operatorname{outer}(\operatorname{vec}(C))
+a\operatorname{outer}(\operatorname{vec}(CE_0)).
$$
原始记忆从 $m_0=s|0\rangle+a|1\rangle$ 出发，以 $m_1=|0\rangle$、
$T|j\rangle=|j\rangle_{\rm out}\otimes m_j$ 先发出 $L,R_0$，随后只在 $L$ 上施加一个固定的复成功 Kraus 算子 $F$，$F^\dagger F\le I_2$。保留共同成功事件，记
$$
C_0=s^3J,\qquad C=FC_0,\qquad
\chi(C)=\operatorname{vec}(C)\otimes|0\rangle_M
+s\operatorname{vec}(CE_0)\otimes|1\rangle_M,\qquad
q_F=\operatorname{Tr}Q(C).
$$
这里 $\chi(C)$ 是成功后的实际联合向量，允许所有复 $F$，包括奇异与零矩阵；端点始终使用完整的 $\mathbb C^2\otimes\mathbb C^2$，不限制在原来的无 $11$ 支撑内。每一个制备各自固定同一个 $F$，不对不同 $F$ 作隐藏混合。

固定非空有限报告集 $Y$ 及同一个列随机矩阵 $W:Y\leftarrow\{0,1\}$。每一步只在仍与端点相关的原始活动记忆上应用 $T$，发出 $R_k$，再在退役的 $R_{k-1}$ 上测量
$$
|\eta_b\rangle=\frac{|0\rangle+(-1)^b|1\rangle}{\sqrt2}.
$$
给定原始结果 $b_k$，按 $W(\cdot\mid b_k)$ 使用新的独立经典随机性产生 $y_k$。这些随机抽取给定原始记录后相互独立，并独立于其余系统和制备设置。全过程不反馈、不重置记忆、不插入后续端点干预；全部报告 $h=(y_1,\ldots,y_m)$ 始终保存在右侧。令
$$
c_y=W(y\mid0)+W(y\mid1),\qquad
d_y=W(y\mid0)-W(y\mid1),\qquad d_y^2\le a c_y^2\quad(y\in Y).
$$
取命题 147.1、148.1 的固定右端点仪器
$$
\phi_y=\begin{cases}c_y\psi_{d_y/c_y},&c_y>0,\\0,&c_y=0,\end{cases}
\qquad
\psi_\nu\begin{pmatrix}x&u\\v&w\end{pmatrix}
=\frac12\begin{pmatrix}
a x+w+\nu(u+v)&a^2x+\nu a v\\
a^2x+\nu a u&a^2x
\end{pmatrix},
\qquad x,u,v,w\in\mathbb C.
$$
对 $m\ge0$ 定义
$$
\Psi_h^W=\phi_{y_m}\circ\cdots\circ\phi_{y_1},\qquad
R_h^W(C)=(\operatorname{Id}_L\otimes\Psi_h^W)(Q(C)),
$$
$$
\mathcal J_W^{(m)}(X)=\sum_{h\in Y^m}\Psi_h^W(X)\otimes|h\rangle\langle h|,
\qquad
\rho_F^{W,m}=\frac1{q_F}\sum_{h\in Y^m}R_h^W(C)\otimes|h\rangle\langle h|
\quad(q_F>0).
$$
空历史的复合为恒等映射。右输出次序取 $R_m,\mathbb C^{Y^m}$；共同成功旗标亦在右侧，其固定纯态因子不影响下列分割。$\mathcal J_W^{(m)}$ 是从一个右 qubit 到右 qubit 与全部报告历史的完全正保迹通道。

可分性采用命题 132.1、141.1、149.1 的有限凸乘积密度和定义。对未归一化正算子，则使用有限正乘积和 $\sum_k A_k\otimes B_k$，$A_k,B_k\ge0$；零算子允许为空和。称右通道为 EB，是指对每个有限维辅助空间 $A$ 和每个 $A\otimes R_0$ 上的密度 $\sigma$，其输出在 $A\mid(R_m\otimes\mathbb C^{Y^m})$ 上可分。这不是要求 $\operatorname{Id}_L\otimes\mathcal J_W^{(m)}$ 相对于另一个外部参考也是 EB。

在这些假设下，对每个这样的 $W$，每个固定允许的 $F\ne0$ 及每条正概率实际报告历史，$m\ge4$ 时条件密度 $R_h^W(C)/\operatorname{Tr}R_h^W(C)$ 在 $L\mid R_m$ 上可分，且保留全部历史的 $\rho_F^{W,m}$ 在 $L\mid(R_m\otimes\mathbb C^{Y^m})$ 上可分。对任意有限辅助输入，整个右通道 $\mathcal J_W^{(m)}$ 在 $m\ge5$ 时为 EB。

这两个统一界均由
$$
B_s(t\mid b)=\frac{1+(-1)^{t+b}s}{2},\qquad t,b\in\{0,1\}
$$
取到：对 $W=B_s$，命题中的“对全部固定允许 $F$ 的每条正概率实际历史均可分”成立当且仅当 $m\ge4$，而 $\mathcal J_{B_s}^{(m)}$ 为 EB 当且仅当 $m\ge5$。这里的阈值是对实际族的全称性质及对任意参考输入的通道性质的阈值，不是每个 $F$ 或每个 $W$ 各自必须达到的时间。非零秩一 $F$ 的端点态从制备时已经是乘积态；两列相同的无信息 $W$ 在一步即为 EB。

若 $F=0$，所有实际块为零，不存在成功条件密度。若 $F\ne0$，$\operatorname{Tr}R_h^W(C)>0$ 恰当所用每一行 $W(y_k\mid\cdot)$ 非零；零行所涉历史没有条件密度。$m$ 计延长次数，全部 $m$ 个报告仍可访问，保留历史的寄存器随 $m$ 增长。

证明。先将既有一步结论与连续过程的对象对齐。命题 145.1、146.1 的字面制备给出 $T^\dagger T=I_2$、$\chi(FC_0)$ 及
$$
q_F=\|C\|_F^2+a\|CE_0\|_F^2,\qquad 0\le q_F\le1,\qquad
q_F>0\ \Longleftrightarrow\ C\ne0\ \Longleftrightarrow\ F\ne0.
$$
两个正交记忆列的范数均计入此式。命题 148.1 在同一个 $T$ 下对任意复 $C$ 逐系数证明：下一次发出后，以退役端点的未归一化 bra $\langle0|+(-1)^b\langle1|$ 收缩，所得向量为 $s\chi(CZ^bJ)$；归一化 bra 则给 $(s/\sqrt2)\chi(CZ^bJ)$。故较早的结果在系数矩阵的右乘积中位于较晚因子的左侧。该命题的兼容联合提升归纳适用于这里完全相同的固定制备、固定 $W$ 与无反馈协议，因而实际块恰为
$$
R_h^W(C)=\left(\frac a2\right)^m
\sum_{\mathbf b\in\{0,1\}^m}
\left[\prod_{k=1}^m W(y_k\mid b_k)\right]
Q(CZ^{b_1}J\cdots Z^{b_m}J)
=(\operatorname{Id}_L\otimes\Psi_h^W)(Q(C)).
$$
这使用实际相关联合态在每个历史处的同一提升，而不只是一步边缘态相等。每个 $Z^bJ$ 可逆，故非零 $C$ 的每条原始历史权重严格为正；非负有限和遂给出所述非零行判据。其迹是成功与报告历史的联合概率，除以 $q_F$ 才是成功条件下的报告概率。求和中没有先归一化原始态。

这里复线性映射的矩阵元方向与命题 145.1—148.1 一致：右乘 $Z^bJ$ 对应右 Hilbert 因子的 $JZ^b$。若记 $\mathcal L_0(X)=X+aE_0XE_0$，其代数逆是 $\mathcal L_0^{-1}(X)=X-a^2E_0XE_0$，则那些命题的一步匹配亦写为
$$
\phi_y=\frac a2\sum_bW(y\mid b)\,
\mathcal L_0\circ\operatorname{Ad}_{JZ^b}\circ\mathcal L_0^{-1}.
$$
该逆只用于代数表示。命题 146.1、147.1 的逐行 CP 结论在 $d_y^2\le ac_y^2$ 下直接给出各 $\phi_y$ 完全正，包括边界与零行，其效应为 $(c_yI_2+d_yX_{\rm P})/2$，其中 $X_{\rm P}=\begin{pmatrix}0&1\\1&0\end{pmatrix}$。由 $\sum_yc_y=2$、$\sum_yd_y=0$，这些效应之和为 $I_2$，所以各分支迹不增且和保迹。复合仍完全正且迹不增；在有限历史和中依次对最后一个报告求和，得 $\mathcal J_W^{(m)}$ 保迹。添加正交旗标保持完全正性。这一保迹论证不要求不同时间的报告概率独立。

先取 $W=B_s$，简记 $\psi_t=\psi_{(-1)^ts}$、
$\Psi_h=\psi_{t_m}\circ\cdots\circ\psi_{t_1}$，并定义两个不同的未归一化算子
$$
D_h=(\operatorname{Id}\otimes\Psi_h)(Q(I_2)),\qquad
H_h=(\operatorname{Id}\otimes\Psi_h)
\bigl(\operatorname{outer}(|00\rangle+|11\rangle)\bigr).
$$
$D_h$ 属于实际制备公式的代数族，$H_h$ 是参考因子在前的 Choi 算子；这里没有在相同长度把两者等同。命题 149.1 的复左合同恒等式在每个历史处同样成立，因为所有后续映射只作用于右因子：
$$
R_h^{B_s}(C)=(C\otimes I_2)D_h(C^\dagger\otimes I_2).
$$
特别地，所有 $D_h\ge0$，既可由实际正分支和得出，也可由完全正映射作用于 $Q(I_2)\ge0$ 得出。

长度相差一步的精确关系如下。令 $e_t=(-1)^t$，
$$
L_t=\frac1{\sqrt2}\begin{pmatrix}a&a\\e_ts&0\end{pmatrix},
\qquad \det L_t=-\frac{e_tas}{2}\ne0.
$$
直接将 $\psi_t$ 作用于四个右矩阵单位，得到
$$
H_t=\frac12\begin{pmatrix}
a&a^2&e_ts&0\\
a^2&a^2&e_tsa&0\\
e_ts&e_tsa&1&0\\
0&0&0&0
\end{pmatrix}
=(L_t\otimes I_2)Q(I_2)(L_t^\dagger\otimes I_2).
$$
第二个等式亦由将 $L_t$ 代入 $Q$ 的两个外积直接相乘得到。后续映射与左合同可交换，故对每条有限后缀 $h$，
$$
H_{(t,h)}=(L_t\otimes I_2)D_h(L_t^\dagger\otimes I_2).
$$
左合同保持有限正乘积和；$L_t$ 可逆，其逆合同也保持此锥，所以它在两个方向保持可分性。按
$$
\operatorname{PT}_R(|ij\rangle\langle kl|)=|il\rangle\langle kj|
$$
定义右偏转置，左合同与其交换。可逆合同保持 Hermitian 二次型的正、负、零惯性，因此上述关系也在两个方向保持 PPT 与 NPT。

在使用行列式之前，证明正算子在此维数下的一个性质：若 $X\ge0$ 作用于完整的 $\mathbb C^2\otimes\mathbb C^2$，则 $X^{\operatorname{PT}_R}$ 至多有一个负特征值。事实上，任取一个二维复子空间，按向量化将它的两个独立向量识别为独立的二阶复矩阵 $A,B$。齐次二次多项式
$$
p(z,w)=\det(zA+wB)
$$
有一个非零的复齐次零点：若它恒为零，取 $(z,w)=(1,0)$；若不恒为零且 $p(1,0)=0$，仍取此点；其余情形 $p(z,1)$ 是首项系数非零的二次复多项式，故存在根。矩阵 $zA+wB$ 因 $A,B$ 独立且 $(z,w)\ne(0,0)$ 而非零，又因行列式为零而秩一，于是对应非零乘积向量 $u\otimes v$。若 $X^{\operatorname{PT}_R}$ 有至少两个负特征值，其负谱子空间中有这样的二维子空间和乘积向量，然而逐坐标有
$$
\langle u\otimes v,X^{\operatorname{PT}_R}(u\otimes v)\rangle
=\langle u\otimes\overline v,X(u\otimes\overline v)\rangle\ge0,
$$
与该非零向量位于负谱子空间矛盾。这证明至多一个负特征值。于是当 $\det(X^{\operatorname{PT}_R})>0$ 时，四个特征值均非零，而恰有一个负值会令行列式为负，所以它们全正。此推理以 $X\ge0$ 和完整复二 qubit 维数为前提，不是任意 Hermitian 矩阵的正行列式判据。

现在给出四步的有限代数证书。置 $M_h=2^{|h|}D_h$，则
$$
M_\varnothing=Q(I_2)=
\begin{pmatrix}
1+a&0&0&1\\
0&0&0&0\\
0&0&0&0\\
1&0&0&1
\end{pmatrix}.
$$
向历史右端追加一位 $t$ 时，对 $M_h$ 的每个二阶块施加同一替换
$$
\begin{pmatrix}x&u\\v&w\end{pmatrix}
\longmapsto
\begin{pmatrix}
a x+w+e_ts(u+v)&a^2x+e_tsa v\\
a^2x+e_tsa u&a^2x
\end{pmatrix}.
$$
此即 $2\psi_t$ 的块规则。对每个二阶块取普通转置得到 $M_h^{\operatorname{PT}_R}$，记
$\delta_h=\det(M_h^{\operatorname{PT}_R})$。定义六个数
$$
\begin{aligned}
\mathsf A_\pm&=2a^{19}\bigl(225+177a\ \pm s(15+663a)\bigr),\\
\mathsf B_\pm&=2a^{22}\bigl(-19+231a\ \pm s(105+67a)\bigr),\\
\mathsf C_\pm&=2a^{24}\bigl(81+4a\ \pm s(17-24a)\bigr).
\end{aligned}
$$
从 $M_\varnothing$ 依上述规则相继替换四次，按行列式的排列展开式求和，并用 $a^2=1-a$、$s^2=a$ 归约，得到完整的首位为零的八历史表：
$$
\begin{array}{c|c}
h&\delta_h\\ \hline
0000&\mathsf A_+\\
0001&\mathsf B_+\\
0010&\mathsf C_+\\
0011&\mathsf B_-\\
0100&\mathsf B_+\\
0101&\mathsf C_-\\
0110&\mathsf B_-\\
0111&\mathsf A_-
\end{array}
$$
这张表的每一项仅含所列块替换和四阶行列式的有限展开。其余八条无需另列，因为
$$
\psi_{-\nu}=\psi_\nu\circ\operatorname{Ad}_Z,\qquad
(I_2\otimes Z)Q(I_2)(I_2\otimes Z)
=(Z\otimes I_2)Q(I_2)(Z\otimes I_2).
$$
后续右映射与左 $Z$ 合同可交换，故翻转历史首位将 $D_h$ 变为
$(Z\otimes I_2)D_h(Z\otimes I_2)$，而不改变其偏转置行列式。表因而覆盖全部十六条长度四历史。

六个数的符号可由有理界直接证明。函数 $r^2+r-1$ 在正半轴严格递增，在 $8/13$ 与 $34/55$ 处的值分别为 $-1/169$ 与 $1/3025$，故
$$
\frac8{13}<a<\frac{34}{55}.
$$
对三组括号分别取
$$
(x,y)=(225+177a,15+663a),\quad
(-19+231a,105+67a),\quad
(81+4a,17-24a).
$$
三者均有 $x>0$；第二组可直接用 $a>8/13$，其余显然。各自平方差为
$$
\begin{aligned}
(225+177a)^2-a(15+663a)^2
&=501633-811152a>\frac{10647}{55}>0,\\
(-19+231a)^2-a(105+67a)^2
&=44141-68072a>\frac{113307}{55}>0,\\
(81+4a)^2-a(17-24a)^2
&=7969-1625a>\frac{76609}{11}>0.
\end{aligned}
$$
每一行的严格下界均由 $a<34/55$ 代入得到。因此 $x>|sy|$，$x+sy$ 与 $x-sy$ 全部严格为正，六个 $\mathsf A_\pm,\mathsf B_\pm,\mathsf C_\pm$ 均正。所有 $D_h\ge0$，故刚证的负特征值数目性质说明全部十六个长度四的 $D_h$ 都有正定右偏转置。由可逆左合同，全部三十二个长度五的 $H_{(t,h)}$ 也有正定右偏转置。这些行列式全为严格正值，此证书不需处理任何零行列式情形。

从 PPT 到可分性使用命题 141.1 所引的二维结论：M. Horodecki、P. Horodecki、R. Horodecki，*Separability of Mixed States: Necessary and Sufficient Conditions*，[arXiv:quant-ph/9605038v2，定理 3，PDF 第 8 页](https://arxiv.org/pdf/quant-ph/9605038v2)，Physics Letters A 223，1–8（1996）。它断言完整 $\mathbb C^2\otimes\mathbb C^2$ 上的密度可分当且仅当其偏转置为正。这里 $D_h,H_h$ 为正算子，所论块的偏转置正定，故它们非零且迹严格为正；先除以各自的迹即可适用该定理。

所引文第 3 页以有限凸乘积和的迹范数闭包定义可分态；命题 141.1 已证明这与本卷定义一致，其有限维理由也适用于这里。具体地，乘积密度集合 $\mathcal P$ 紧，位于迹一 Hermitian 四阶矩阵的十五维实仿射空间中。任一含多于十六个正权重的有限和 $\sum_i p_iR_i$，由仿射相关性可取不全为零的实数 $c_i$，满足 $\sum_i c_i=0$、$\sum_i c_iR_i=0$。取
$$
\lambda=\min_{c_i>0}\frac{p_i}{c_i},\qquad p_i'=p_i-\lambda c_i,
$$
保持权重非负、和为一及所表示的态，并至少消去一项。重复即把项数降至十六项。因此 $\operatorname{conv}(\mathcal P)$ 是紧集 $\Delta_{15}\times\mathcal P^{16}$ 在有限和连续映射下的像，故在迹范数中闭。这说明 PPT 充分性给出真正的有限凸乘积分解；乘回严格正迹后，得到每个所论 $D_h,H_h$ 的有限正乘积和。反之，正矩阵的转置仍正，故任意有限正乘积和的右偏转置为正。

四步实际族的结论现在由左合同直接传递。对任意复 $C$，包括奇异 $C$，将 $D_h$ 的有限正乘积和逐项以 $C$ 左合同，仍是有限正乘积和；在正迹分支归一化，即得实际条件态的可分性。保留全部历史也可分：这正是命题 149.1 的有限正交旗标论证，对每个分支的右因子附加 $|h\rangle\langle h|$，并用权重 $\operatorname{Tr}R_h(C)/q_F$ 合并各有限分解即可。反向的逐旗标压缩也保持有限正乘积和。

为把五步 Choi 结论用于所有有限辅助输入，现明确给出分支重建。对任一复线性右分支 $\Psi_h$，按参考在前的次序有
$$
H_h=\sum_{i,j=0}^1|i\rangle\langle j|\otimes
\Psi_h(|i\rangle\langle j|).
$$
若 $H_h=\sum_{k=1}^N A_k\otimes B_k$、$A_k,B_k\ge0$，比较参考矩阵单位的系数，并对任意 $X=\sum_{ij}X_{ij}|i\rangle\langle j|$ 线性重建，得
$$
\Psi_h(X)=\sum_k\left(\sum_{i,j}(A_k)_{ij}X_{ij}\right)B_k
=\sum_k\operatorname{Tr}(A_k^{\mathsf T}X)B_k.
$$
$A_k^{\mathsf T}\ge0$。对任意有限辅助 $A$ 与密度 $\sigma\ge0$，令
$f_k(X)=\operatorname{Tr}(A_k^{\mathsf T}X)$、
$S_k=(\operatorname{Id}_A\otimes f_k)(\sigma)$。任取 $u\in A$，输入压缩
$$
\sigma_u=(\langle u|\otimes I_2)\sigma(|u\rangle\otimes I_2)\ge0
$$
给
$$
\langle u,S_ku\rangle
=\operatorname{Tr}(A_k^{\mathsf T}\sigma_u)\ge0.
$$
最后的不等式可由 $A_k^{\mathsf T}$ 的有限正谱分解逐项得到。因此 $S_k\ge0$，并有
$$
(\operatorname{Id}_A\otimes\Psi_h)(\sigma)=\sum_k S_k\otimes B_k.
$$
这是每个有限辅助空间上的有限正乘积和。它不要求分支保迹，因而同样证明迹不增分支的纠缠破坏性质；输出迹为正时再归一化，零输出无条件密度。反之，若分支对所有辅助输入有此性质，将它作用于归一化最大纠缠密度
$\operatorname{outer}(|00\rangle+|11\rangle)/2$，就得到可分的未归一化输出 $H_h/2$，所以 $H_h$ 必可分。

有限正交旗标通道为 EB 当且仅当每个分支具有刚才的性质。必要性来自在右侧压缩到指定旗标，充分性来自把各分支的 $B_k$ 换成 $B_k\otimes|h\rangle\langle h|$ 并合并有限和；通道保迹使总输出为密度。这也说明即使报告完整保留，全部长度五的 Choi 块可分仍足以得到 $\mathcal J_{B_s}^{(5)}$ 对每个有限辅助输入为 EB。

为证明两个界的尖锐性，对同一块规则只迭代三次，得到
$$
\delta_{011}=2a^{16}\bigl(15-a-s(4+24a)\bigr).
$$
这里 $15-a>0$、$4+24a>0$，而
$$
(15-a)^2-a(4+24a)^2
=610-1007a<-\frac{126}{13}<0
$$
由 $a>8/13$ 得出。所以 $\delta_{011}<0$，$D_{011}^{\operatorname{PT}_R}$ 不是正半定，$D_{011}$ 为 NPT。负行列式本身已排除正半定性，不需要把任意正行列式当成充分条件。可逆左合同还给
$$
H_{0011}=(L_0\otimes I_2)D_{011}(L_0^\dagger\otimes I_2),\qquad
\det\bigl((2^4H_{0011})^{\operatorname{PT}_R}\bigr)=a^6\delta_{011}<0.
$$
因此四步的 $0011$ Choi 分支为 NPT；对最大纠缠参考输入，它是一个正迹输出，故逐旗标压缩排除 $\mathcal J_{B_s}^{(4)}$ 为 EB。这一参考输入用于全参考域的否定，不把它认作实际制备输入。

实际族的尖锐性由命题 149.1 的同一个固定物理滤波给出：
$$
F_*=\frac14J^{-1}=\frac14\begin{pmatrix}0&1\\1&-1\end{pmatrix},\qquad
\|F_*\|_{\rm op}^2\le\|F_*\|_F^2=\frac3{16}<1,\qquad
F_*C_0=\frac{s^3}{4}I_2.
$$
故 $F_*^\dagger F_*\le I_2$，它可逆，且
$$
R_h^{B_s}(F_*C_0)=\frac{a^3}{16}D_h,\qquad
q_{F_*}=\frac{a^3}{16}(2+a)=\frac a{16}>0.
$$
同一三步块展开取迹得实际 $011$ 事件的联合及条件概率
$$
\Pr(\mathrm{success},011)
=\frac{a^3}{128}(5a-4s+2sa),\qquad
\Pr(011\mid\mathrm{success})
=\frac{a^2}{8}(5a-4s+2sa).
$$
二者严格为正：$F_*\ne0$ 且 $B_s$ 的每个元素均正，实际原始历史和的每项具有严格正迹与严格正系数。其归一化条件态因 $\delta_{011}<0$ 而 NPT。因此三步实际族的全称可分性不成立，所用是同一个允许的 $F_*$ 与真实正概率事件。

超过上述时域以后，无需再逐长度展开矩阵。任一后续步骤只以完全正分支作用右端点，并把新的经典旗标附在右因子上；它把每个有限正乘积和送为有限正乘积和。所以四步后的全部实际分支与旗标态持续可分，五步后的全参考通道持续为 EB。反过来，同一 $F_*$ 的正概率 NPT 历史 $011$ 的任意较早前缀也必须纠缠：若某前缀可分，后续指定右侧 CP 分支不能产生该 NPT 输出。前缀概率为正，由它至少包含这个正概率后继事件即知。这排除实际全称性质在 $m=0,1,2,3$ 成立。类似地，若某个 $m\le4$ 的完整历史通道已为 EB，在右侧继续到四步仍为 EB，与 $H_{0011}$ 矛盾。因而得到所述两个当且仅当阈值。实际族四步全可分与右通道四步非 EB 的同时成立，恰由它们不同的输入量词解释。

最后转回任意允许的有限 $W$。命题 147.1 的最大报告分解在这里给
$$
V(y\mid t)=\frac{c_y+(-1)^t d_y/s}{2}\ge0,\qquad
\sum_yV(y\mid t)=1,\qquad
W(y\mid b)=\sum_{t=0}^1V(y\mid t)B_s(t\mid b).
$$
其非负性来自 $|d_y|\le sc_y$，列和来自 $\sum_yc_y=2$、$\sum_yd_y=0$；零行仍给零行。对每条完整原始历史 $\mathbf b$，有限分配律给出
$$
\prod_{k=1}^mW(y_k\mid b_k)
=\sum_{\mathbf t\in\{0,1\}^m}
\prod_{k=1}^m\bigl[V(y_k\mid t_k)B_s(t_k\mid b_k)\bigr].
$$
将它代入已经证明的实际未归一化历史和，保持量子端点不动，得到
$$
R_{\mathbf y}^{W}(C)
=\sum_{\mathbf t\in\{0,1\}^m}
\left[\prod_{k=1}^mV(y_k\mid t_k)\right]R_{\mathbf t}^{B_s}(C).
$$
这是带全部 Born 权重的相关历史恒等式，不将历史概率替换为边缘概率的乘积。在全复算子空间，命题 147.1 的 $\phi_y=\sum_tV(y\mid t)\psi_t$ 经有限次分配也给
$$
\Psi_{\mathbf y}^{W}
=\sum_{\mathbf t\in\{0,1\}^m}
\left[\prod_{k=1}^mV(y_k\mid t_k)\right]\Psi_{\mathbf t}.
$$
故完整 $W$ 通道由完整 $B_s$ 通道对每一历史旗标独立施加 $V$ 得到，始终保留全部处理后的 $m$ 个报告。有限正和及右侧局部经典处理保持有限正乘积和，从而传递实际四步和全参考五步的两个上界。$B_s$ 本身已在允许域内，并给上述反例，故这两个统一界不可降低。

阈值并不逐个约束每个滤波或每个报告矩阵。若非零 $F$ 秩一，则 $C=\ell v^{\mathsf T}$，从定义直接有
$$
Q(C)=\operatorname{outer}(\ell)\otimes
\bigl(\operatorname{outer}(v)+a\operatorname{outer}(E_0v)\bigr),
$$
所有后继分支仍有相同的左正因子，正迹时为乘积密度。若 $W$ 两列相同，写 $W(y\mid0)=W(y\mid1)=p_y$，则命题 149.1 的单步分解给
$$
\phi_y=p_y\mathcal T,\qquad
\mathcal T=2\psi_{\nu=0},\qquad
\mathcal T\begin{pmatrix}x&u\\v&w\end{pmatrix}
=x\begin{pmatrix}a&a^2\\a^2&a^2\end{pmatrix}+wE_0.
$$
这是测量计算基后制备两个密度的右通道；其对任意有限辅助输入的正对角块分解已由命题 149.1 给出，附加报告密度仍在右侧，故一步即为 EB。整个论证只消除所声明左／右分割的纠缠。若另取外部参考与不动的 $L$ 纠缠，并让 $R_0$ 独立，则 $\operatorname{Id}_L\otimes\mathcal J_W^{(m)}$ 保留该参考与 $L$ 的纠缠，说明右通道的 EB 性不等于含不动 $L$ 的扩大通道相对于该外部参考的 EB 性。证毕。

<a id="entry-650"></a>

## 追加锚（本行以下为增补区）

<a id="section-151"></a>

## 151. 有限纠缠破坏分块后的隐状态预测与逐报告端点复现

**命题 151.1（保留全部旗标的有限分块与有限经典隐状态实现）。** 设 $R=\mathbb C^2$，取固定的非空有限报告集 $Y$，$r=|Y|$，以及固定的复线性完全正仪器
$$
\phi_y:M_2(\mathbb C)\longrightarrow M_2(\mathbb C)\quad(y\in Y),
\qquad \mathcal T=\sum_{y\in Y}\phi_y\quad\text{保迹}.
$$
各个时刻使用同一个仪器，不依赖时间或已见历史，不反馈、不重置、不插入其他操作。所有报告均保留。各次右端点按固定计算基识别为 $R$，任意有限维参考 $A$ 保持不动。对有限词 $p=(p_1,\ldots,p_\ell)$，规定
$$
\phi_p=\phi_{p_\ell}\circ\cdots\circ\phi_{p_1},\qquad
\phi_\varnothing=\operatorname{Id}_R.
$$
固定整数 $b\ge1$。完整块词 $h\in Y^b$ 的分支记为 $\Psi_h=\phi_h$，参考因子在前的未归一化 Choi 算子为
$$
H_h=\sum_{u,v=0}^1|u\rangle\langle v|\otimes\Psi_h(|u\rangle\langle v|).
$$
假设每个完整块都满足有限可分性
$$
\operatorname{EB}_{\rm BLOCK}(b):\qquad
H_h=\sum_{k=1}^{n_h}A_{hk}\otimes B_{hk},\qquad
A_{hk},B_{hk}\ge0\quad(h\in Y^b),
$$
其中允许零算子为空和。此假设等价于完整旗标通道
$$
X\longmapsto\sum_{h\in Y^b}\Psi_h(X)\otimes|h\rangle\langle h|
$$
对任意有限参考为纠缠破坏通道，分割为 $A\mid(R\otimes\mathbb C^{Y^b})$；这里采用命题 150.1 的有限正乘积和定义。

则存在一个固定有限集合 $J=\{1,\ldots,N\}$、块报告函数 $h:J\to Y^b$、非零正效应 $E_j$ 及右密度 $\sigma_j$，满足
$$
1\le N\le16r^b,\qquad
\sum_{j\in J}E_j=I_2,\qquad
\Psi_h(X)=\sum_{j\in J_h}\operatorname{Tr}(E_jX)\sigma_j
\quad(X\in M_2(\mathbb C)),\qquad
J_h=\{j\in J:h(j)=h\}.
$$
这些对象给出整个首个 $b$ 步的输入、报告及块末端点仪器的另一种实现：测量 $\{E_j\}$，保留其内部标签 $j$，报告 $h(j)$，在该块末端点被请求时制备 $\sigma_j$。对任意未归一化正输入 $\omega_{AR}$，令
$$
A_j=(\operatorname{Id}_A\otimes[X\mapsto\operatorname{Tr}(E_jX)])(\omega_{AR}).
$$
则 $A_j\ge0$、$\sum_jA_j=\operatorname{Tr}_R\omega_{AR}$，且
$$
(\operatorname{Id}_A\otimes\Psi_h)(\omega_{AR})
=\sum_{j\in J_h}A_j\otimes\sigma_j.
$$
对标量密度输入 $\rho_R$，初始隐标签概率就是 $p_j=\operatorname{Tr}(E_j\rho_R)$。

从这个首块完成时刻起，只需有限经典隐状态即可精确预测所规定的未来。块边界转移矩阵为
$$
K_{ji}=\operatorname{Tr}(E_j\sigma_i),\qquad
K_{ji}\ge0,\qquad \sum_jK_{ji}=1.
$$
为了逐个发出报告并允许在任意后续报告处终止，定义
$$
d_{i,p}=\operatorname{Tr}\phi_p(\sigma_i),\qquad
\mathsf S=\{(i,p):i\in J,\ p\in\bigcup_{\ell=0}^{b-1}Y^\ell,\ d_{i,p}>0\},
\qquad
\sigma_{i,p}=\frac{\phi_p(\sigma_i)}{d_{i,p}}.
$$
特别地 $d_{i,\varnothing}=1$、$\sigma_{i,\varnothing}=\sigma_i$。将每个转移的报告显式列入，令
$$
\begin{aligned}
P\bigl(y,(i,py)\mid(i,p)\bigr)
&=\frac{d_{i,py}}{d_{i,p}}
&&\bigl(|p|<b-1,\ d_{i,py}>0\bigr),\\
P\bigl(y,(j,\varnothing)\mid(i,p)\bigr)
&=\frac{K_{ji}}{d_{i,p}}
&&\bigl(|p|=b-1,\ j\in J_{py}\bigr).
\end{aligned}
$$
其余报告与后继状态对的概率均为零。这个转移核在 $\mathsf S$ 上时间齐次；词 $p$ 的长度已经记录相位。进入时刻以后的状态数满足
$$
M:=|\mathsf S|\le N\sum_{\ell=0}^{b-1}r^\ell
\le16r^b\sum_{\ell=0}^{b-1}r^\ell.
$$
若 $b=1$，没有内部转移，只有
$P(y,(j,\varnothing)\mid(i,\varnothing))=K_{ji}$，其中 $h(j)=(y)$；若 $r=1$，每一长度只有一个词，$M\le Nb$。

精确性同时包含每条完整报告前缀、未归一化端点算子及其与任意有限参考的关联。具体地，对 $m\ge1$、$h_1,\ldots,h_m\in Y^b$ 及 $|p|<b$，在时刻 $mb+|p|$ 有
$$
\begin{aligned}
W_{h_1,\ldots,h_m,p}
&:=(\operatorname{Id}_A\otimes
(\phi_p\circ\Psi_{h_m}\circ\cdots\circ\Psi_{h_1}))(\omega_{AR})\\
&=\sum_{\substack{j_1\in J_{h_1},\ldots,j_m\in J_{h_m}}}
\left(\prod_{t=2}^m K_{j_tj_{t-1}}\right)
A_{j_1}\otimes\phi_p(\sigma_{j_m}).
\end{aligned}
$$
$m=1$ 时空乘积取一。该算子正是上述隐状态实现的报告分支，因而在时间 $b$ 及其以后任选一个终止时刻，对 $A,R$ 的每个联合终端实验都相同，也允许实验及终止选择依赖已经报告的历史。任意报告事件先对相应未归一化块求和，只在实际迹严格为正时条件化。

这里的进入仪器实现整个首块，而不是先运行原首块、再从其已经产生的端点及报告无扰动地取出 $j$。若首块报告必须逐个发出，可以先抽取 $j$，再依次发出 $h(j)$ 的字母；这给出首块报告的正确边缘前缀概率，但不承诺时间 $b$ 以前的中间量子端点相等。参考仍是量子系统；$A_j$ 可以互不交换，不是标量概率。端点密度 $\sigma_{i,p}$ 只在选定的终止时间制备，或用于该次端点实验的 Born 响应，不承诺在多个时间同时提供端点副本。

对命题 147.1—150.1 的每个固定可准入 $W$，取其同一个右仪器 $\phi_y$，可令 $b=5$。特别地，对命题 147.1 的最大二元报告 $B_s$，$r=2$，上述存在性上界为
$$
N\le16\cdot2^5=512,\qquad
M\le512(1+2+4+8+16)=15872.
$$
这两个数不是最小值，亦不指定该应用的任何显式 Choi 乘积分解。非选择通道为 EB、受限制备族已经可分、输出态交换以及有限隐状态这几件事均须区别；以下证明中的非选择例与保留 Pauli 旗标的反例说明这些边界。

证明。先从有限可分 Choi 块提取支持。正矩阵的所有特征值非负，故非零正矩阵的迹严格为正；正矩阵迹零则矩阵为零。每个 $H_h$ 的分解中，任一因子为零的乘积项都先删除。若 $H_h=0$，比较四个输入矩阵单位的块得 $\Psi_h=0$，此支不需任何标签。若 $H_h\ne0$，则
$$
\frac{H_h}{\operatorname{Tr}H_h}
=\sum_k
\frac{\operatorname{Tr}A_{hk}\operatorname{Tr}B_{hk}}{\operatorname{Tr}H_h}
\frac{A_{hk}}{\operatorname{Tr}A_{hk}}\otimes
\frac{B_{hk}}{\operatorname{Tr}B_{hk}}
$$
是二 qubit 乘积密度的有限凸组合。直接应用命题 141.1 证明中的有限凸支持消元：该集合位于实仿射维数十五的迹一 Hermitian 空间，超过十六个正权重时的仿射相关消元保持所表示的态，并减少正权重项数。因此每个非零块可取至多十六个乘积项。乘回总迹后再删除零项，将所有块的剩余项编成 $j\in J$，并令 $h(j)$ 保留其所属完整报告词。由 $|Y^b|=r^b$ 得 $N\le16r^b$。这一步使用已有的支持界，不要求各乘积因子为实矩阵或纯态。

对一个保留项暂记两因子为 $A_{hk},B_{hk}$，定义
$$
\sigma_{hk}=\frac{B_{hk}}{\operatorname{Tr}B_{hk}},\qquad
E_{hk}=\operatorname{Tr}(B_{hk})A_{hk}^{\mathsf T}.
$$
$\mathsf T$ 为输入计算基中的普通转置，而非伴随。若 $A_{hk}=\sum_\nu\lambda_\nu v_\nu v_\nu^\dagger$，则
$A_{hk}^{\mathsf T}=\sum_\nu\lambda_\nu\overline v_\nu\overline v_\nu^\dagger\ge0$，故 $E_{hk}$ 为非零正效应候选，$\sigma_{hk}$ 为密度。记 $e_{uv}=|u\rangle\langle v|$；在参考在前的 Choi 次序中，输入 $(u,v)$ 块给出
$$
\Psi_h(e_{uv})=\sum_k(A_{hk})_{uv}B_{hk},\qquad
\operatorname{Tr}(E_{hk}e_{uv})
=(E_{hk})_{vu}
=\operatorname{Tr}(B_{hk})(A_{hk})_{uv}.
$$
因此 $\Psi_h(e_{uv})=\sum_k\operatorname{Tr}(E_{hk}e_{uv})\sigma_{hk}$。四个 $e_{uv}$ 是全部复二阶矩阵的复基，对相互独立的复系数线性延伸，便得陈述中的所有 $X$ 的公式；并未只在实对称或 Hermitian 输入上比较。普通转置正是使这个系数恒等式成立的因素。

依完整词逐步求和，有 $\sum_{h\in Y^b}\Psi_h=\mathcal T^b$。各分支完全正，其和保迹；因而对每个复矩阵 $X$，
$$
\operatorname{Tr}\left(\left(\sum_jE_j\right)X\right)
=\sum_h\operatorname{Tr}\Psi_h(X)
=\operatorname{Tr}\mathcal T^b(X)=\operatorname{Tr}X.
$$
取 $X=e_{uv}$ 逐元比较，得到 $\sum_jE_j=I_2$。所以各个 $E_j\le I_2$，确为同一有限 POVM 的效应，且 $N\ge1$。对密度输入，$\operatorname{Tr}(E_j\rho)\ge0$ 可由正压缩 $E_j^{1/2}\rho E_j^{1/2}$ 的迹看出，总和为一。测量后按 $j$ 制备 $\sigma_j$ 是完全正操作：若
$E_j=\sum_u e_{ju}|u_j\rangle\langle u_j|$、$\sigma_j=\sum_v t_{jv}|v_j\rangle\langle v_j|$ 为谱分解，则
$$
L_{juv}=\sqrt{e_{ju}t_{jv}}\,|v_j\rangle\langle u_j|
$$
给出该分支的 Kraus 算子，且 $\sum_{j,u,v}L_{juv}^\dagger L_{juv}=I_2$。保留 $j$ 并把其报告函数取为 $h(j)$，就是整个首块仪器的一种实现。

现在保留任意有限参考。按输入矩阵单位展开
$$
\omega_{AR}=\sum_{u,v=0}^1\omega_{uv}\otimes e_{uv},\qquad
A_j=\sum_{u,v=0}^1(E_j)_{vu}\omega_{uv}.
$$
第二式也恰等于正压缩后的偏迹
$$
A_j=\operatorname{Tr}_R\left[
(I_A\otimes\sqrt{E_j})\omega_{AR}(I_A\otimes\sqrt{E_j})\right],
$$
因为每个 $e_{uv}$ 的系数满足
$\operatorname{Tr}(\sqrt{E_j}e_{uv}\sqrt{E_j})=\operatorname{Tr}(E_je_{uv})=(E_j)_{vu}$。合同保持正性，正算子的偏迹为正，故 $A_j\ge0$。由 $\sum_jE_j=I_2$，逐系数求和得 $\sum_jA_j=\sum_u\omega_{uu}=\operatorname{Tr}_R\omega_{AR}$。再将已证的复矩阵单位重建式应用于右因子，得到
$$
(\operatorname{Id}_A\otimes\Psi_h)(\omega_{AR})
=\sum_{u,v}\omega_{uv}\otimes\Psi_h(e_{uv})
=\sum_{j\in J_h}A_j\otimes\sigma_j.
$$
此处没有把 $\omega_{uv}$ 或 $A_j$ 当成相互交换的标量。也由此验证假设的 EB 等价性：每块 Choi 可分时，上式对任意有限参考给出有限正乘积和，附上右侧旗标仍如此；反过来，将完整旗标通道作用于归一化最大纠缠输入，再局部压缩至旗标 $h$，得到可分的 $H_h/2$。通道保迹使总体输出迹为一。这与命题 150.1 的全参考及旗标判据一致。

进入以后，正密度 $\sigma_i$ 与正效应 $E_j$ 给
$$
K_{ji}=\operatorname{Tr}(\sqrt{E_j}\sigma_i\sqrt{E_j})\ge0,
\qquad \sum_jK_{ji}=\operatorname{Tr}\sigma_i=1,
\qquad
\Psi_h(\sigma_i)=\sum_{j\in J_h}K_{ji}\sigma_j.
$$
对完整块数作归纳。首块就是上面的参考恒等式。若已经得到 $m$ 块的和，下一块只作用于其中的右因子，用最后一个公式替换 $\Psi_{h_{m+1}}(\sigma_{j_m})$，每项便乘入 $K_{j_{m+1}j_m}$，参考系数 $A_{j_1}$ 保持不动。因此
$$
(\operatorname{Id}_A\otimes(\Psi_{h_m}\circ\cdots\circ\Psi_{h_1}))(\omega_{AR})
=\sum_{\substack{j_1\in J_{h_1},\ldots,j_m\in J_{h_m}}}
\left(\prod_{t=2}^mK_{j_tj_{t-1}}\right)
A_{j_1}\otimes\sigma_{j_m}.
$$
较早标签位于每个 $K$ 的列指标，较晚标签位于行指标；这固定了时间次序。取迹给真正的报告历史权重，各个报告块没有被当作独立抽样的边缘事件。对所有完整块历史求和，列和为一及 $\sum_j\operatorname{Tr}A_j=\operatorname{Tr}\omega_{AR}$ 保证总迹守恒。

接着证明逐个报告的实现。每个 $\phi_p(\sigma_i)$ 因完全正性而正半定，所以 $d_{i,p}\ge0$；若 $d_{i,p}=0$，正谱的非负特征值和为零，故 $\phi_p(\sigma_i)=0$，任意后继复合均把它送为零。删除这些状态不会失去任何正权重路径，也不用归一化零算子。若 $d_{i,p}>0$，$\sigma_{i,p}$ 是固定密度。对内部相位 $|p|<b-1$，保迹性给
$$
\sum_{y\in Y}d_{i,py}
=\operatorname{Tr}\mathcal T(\phi_p(\sigma_i))=d_{i,p}.
$$
因此所有报告与后继对的转移概率之和为一。对每个 $d_{i,py}>0$ 的报告，算子级等式为
$$
\frac{d_{i,py}}{d_{i,p}}\sigma_{i,py}
=\frac{\phi_{py}(\sigma_i)}{d_{i,p}}
=\phi_y(\sigma_{i,p}).
$$
若 $d_{i,py}=0$，右边也是零，省去该后继同样满足等式。沿任一正权重内部前缀，概率比相乘消去中间分母，乘积恰为 $d_{i,p}/d_{i,\varnothing}=d_{i,p}$；一条前缀有正迹时，其全部较早前缀也有正迹，因为零算子的后继恒为零。

在最后相位 $|p|=b-1$，对每个报告 $y$，完整块重建给
$$
\sum_{j\in J_{py}}K_{ji}\sigma_j
=\Psi_{py}(\sigma_i)=\phi_y(\phi_p(\sigma_i)).
$$
先对每个 $y$ 取迹，再对 $y$ 求和，得到
$$
\sum_{y\in Y}\sum_{j\in J_{py}}K_{ji}
=\operatorname{Tr}\mathcal T(\phi_p(\sigma_i))=d_{i,p}.
$$
故最后相位的全部报告与后继对仍归一化。比只核迹更强的是每个报告分别满足
$$
\sum_{j\in J_{py}}\frac{K_{ji}}{d_{i,p}}\sigma_j
=\frac{\Psi_{py}(\sigma_i)}{d_{i,p}}
=\phi_y(\sigma_{i,p}).
$$
其迹是当前隐状态下实际下一报告概率；该迹正时再归一化，就得到实际条件端点。若该报告概率为零，左侧非负系数的和为零，每个系数均为零。内部比值乘至此步后，整块路径的权重恰为 $K_{ji}$。当 $b=1$ 时 $p=\varnothing$、分母为一，上述最后相位论证直接给全部转移，不需任何内部步骤。当 $r=1$ 时仅有一个可能报告；每个内部比值为一，最后相位的后继系数列和为一，同样适用。

将 $\phi_p$ 作用于完整块归纳式的右因子，得到陈述中的 $W_{h_1,\ldots,h_m,p}$。每项若 $d_{j_m,p}>0$，可重写为
$$
\left[d_{j_m,p}\left(\prod_{t=2}^mK_{j_tj_{t-1}}\right)A_{j_1}\right]
\otimes\sigma_{j_m,p};
$$
若 $d_{j_m,p}=0$，该项为零。括号内是正参考算子。刚证的内部比值及最后报告算子恒等式恰好逐步产生这些系数，故经典转移复现每个停止前缀的完整算子，而非仅复现整块概率。状态集合是有限的，转移只依赖 $(i,p)$；数每个长度的至多 $r^\ell$ 个前缀即得 $M$ 的界。相位已经由 $|p|$ 决定，不再另乘一个 $b$。

为了明确终端实验和条件化，令 $z$ 表示任何长度至少为 $b$ 的完整已报词，$W_z$ 为上式相应块。对依赖该词的任意联合效应 $0\le G_z\le I_{A\otimes R}$，实际与实现中的该词及终端事件共同权重都为 $\operatorname{Tr}(G_zW_z)$。若输入的迹为一，这就是概率；未归一化成功子态则给共同成功权重。对同一时刻的事件 $C\subseteq Y^n$，令
$$
W_C=\sum_{z\in C}W_z,\qquad
\Pr(\text{终端事件}\mid C)
=\frac{\sum_{z\in C}\operatorname{Tr}(G_zW_z)}{\operatorname{Tr}W_C}
\quad\bigl(\operatorname{Tr}W_C>0\bigr).
$$
这包括先按历史选终端 POVM，再对每个结果使用其效应。若停止时刻依赖报告，只须对该有限停止规则的终止词逐项使用同一等式；这些词不互为严格前缀，所对应停止事件互斥。历史条件化从未用等权平均替代实际迹权重。所有零概率历史都由正零算子处理，不定义其条件态。

首块若须顺序发出报告，抽到 $j$ 后依次输出 $h(j)$。对长度 $\ell\le b$ 的首块前缀 $p$ 及密度 $\rho$，其边缘概率为
$$
\sum_{j:h(j)\text{ 以前缀 }p\text{ 开始}}\operatorname{Tr}(E_j\rho)
=\sum_{z\in Y^{b-\ell}}\operatorname{Tr}\Psi_{pz}(\rho)
=\operatorname{Tr}\mathcal T^{b-\ell}(\phi_p(\rho))
=\operatorname{Tr}\phi_p(\rho).
$$
对带参考输入的报告边缘，取 $\rho=\operatorname{Tr}_A\omega_{AR}$ 给相同等式。这是整个首块的实现及其报告边缘化，不把未来块末密度提前认作当前端点。时间 $b$ 前输入纠缠可以尚未消失；整段前入口量子过程的经典实现是另一命题。进入以后若在一块开头先按 $K_{ji}$ 抽取未来 $j$，其块词概率虽正确，却一般不能在中间时刻用 $\sigma_j$ 作为响应；上面的 $\sigma_{i,p}$ 与最后报告重建正为保留中间端点而设。

这种实现自己保存测量产生的 $j$，不要求原仪器的环境实际具有同一经典标签。特别地，$\sigma_j$ 可以非正交，报告及输出密度一般不能揭示 $j$，上述构造不提供从原仪器不透明输出恢复它的通道。标量输入下，观察者条件于记录所持有的是有限隐集上的概率向量：例如首块 $h$ 的后验为
$$
\pi_j(h)=\frac{\mathbf1_{\{j\in J_h\}}\operatorname{Tr}(E_j\rho)}
{\operatorname{Tr}\Psi_h(\rho)}
\quad\bigl(\operatorname{Tr}\Psi_h(\rho)>0\bigr).
$$
有限隐集的信念空间是实概率单纯形，跨任意初始态这些向量可以连续变化，并不只有有限种观察者预测状态。对一个固定输入，有限字母表上的全部有限词是可数集，故其实际可达后验至多可数，可以无限，不能自动称为不可数连续统。带参考时需保留正算子系数，而不把量子参考经典化。完整报告档案仍随时间增长；有限隐支持并不推出有限确定性预测商、最少状态数、最小记忆位数、有限精度转移表或可从原环境访问的标签。

作为同一结论内的非交换说明，取命题 145.1 的非选择右通道作为单报告仪器，令 $b=1$，并沿用该命题的 $\alpha$：
$$
\mathcal T(X)=X_{00}\tau_0+X_{11}E_0,\qquad
\tau_0=\begin{pmatrix}\alpha&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix},\qquad
E_0=|0\rangle\langle0|,\qquad \alpha+\alpha^2=1.
$$
该命题已证明 $\tau_0$ 为密度，$\operatorname{Tr}\tau_0=1$、$\det\tau_0=\alpha^5>0$。取两个隐状态的响应依次为 $\tau_0,E_0$，入口效应依次为 $E_0,|1\rangle\langle1|$，直接代入 $K_{ji}=\operatorname{Tr}(E_j\sigma_i)$ 得
$$
K=\begin{pmatrix}\alpha&1\\\alpha^2&0\end{pmatrix},\qquad
[\tau_0,E_0]:=\tau_0E_0-E_0\tau_0
=\begin{pmatrix}0&-\alpha^2\\\alpha^2&0\end{pmatrix}\ne0.
$$
所以有限隐状态响应不要求输出代数交换。此处是右端点通道 $\mathcal T$；命题 130.1、133.1 原始记忆通道的制备态 $P_0=|m_0\rangle\langle m_0|$ 有非对角元 $\alpha^{3/2}$，而这里为 $\alpha^2$，两通道不可混同。

非选择 EB 也不能替代逐完整报告块的假设。取报告集 $\{0,1,2,3\}$，令 $U_y$ 依次为 $I_2$ 及三个 Pauli 矩阵，分支为
$$
\phi_y(X)=\frac14U_yXU_y^\dagger.
$$
对计算基的四个矩阵单位求和，两个对角单位均送为 $I_2/2$，两个非对角单位送为零，故
$$
\sum_y\phi_y(X)=\operatorname{Tr}(X)\frac{I_2}{2}.
$$
对任意有限参考，该非选择通道送 $\omega_{AR}$ 为
$\operatorname{Tr}_R(\omega_{AR})\otimes I_2/2$，所以为 EB。然而每个长度 $n\ge1$ 的完整报告词都给
$$
\phi_{(y_1,\ldots,y_n)}(X)
=4^{-n}U_{y_n}\cdots U_{y_1}XU_{y_1}^\dagger\cdots U_{y_n}^\dagger.
$$
作用于最大纠缠参考密度时，这是正权重 $4^{-n}$ 乘以局部幺正像，归一化后仍有 Schmidt 秩二，因而仍纠缠。其 Choi 算子是同一纠缠纯态的正倍数，不可能为有限正乘积和。于是保留每个旗标时，没有任何有限 $b$ 满足这里的块假设，尽管非选择通道一步已经 EB。

最后对齐本卷的具体应用及较弱前提。对命题 147.1 的逐行可准入 $W$，各 $\phi_y$ 完全正且和保迹；命题 148.1 对同一相关记忆的联合提升归纳，已经把所有实际有限报告历史及端点算子等同于同一个仪器的按时间复合。命题 150.1 则对这个固定仪器证明 $\mathcal J_W^{(5)}$ 对任意有限参考为 EB，完整五步报告仍在右侧。对其参考在前的 Choi 输入逐旗标压缩，恰给这里每个长度五的 $H_h$ 的有限可分性，所以本命题可取 $b=5$。对 $B_s$ 的二元字母表代入计数式，就得 $512$ 与 $15872$ 两个上界。这里的应用使用全参考五步结论；只用该命题的兼容族四步可分性不足以满足假设，且其 $B_s$ 四步非 EB 结论已经说明两者严格有别。这是有限实数表的存在性结论，没有在此给出该五步应用的精确分解、有限精度算法或最优性结论。

定理 16.5 的经典路径依赖指定理想投影与初始经典相关结构，第 70.4 节依赖每步实际插入构型投影，命题 78.9 的四标签描述则从首次实际秩一 Lüders 查询后开始；这些前提各自给出相应过程，不能单独推出此处保留全部报告的有限块及块内任意参考算子恒等式。命题 118.16 另要求控制器可由记录确定其状态描述，并对每个动作验证受控 Markov 充分性；本命题的隐标签通常不能由观察历史确定，也未允许反馈动作。命题 133.1 的分解依赖实际忽略中间输出，不能代替保留旗标的假设，正如上述 Pauli 例所示。命题 144.1 的射影历史商针对已完成制备后的确定性充分记录，本命题的有限隐支持不宣称那个确定性商只有有限多个跨时域类别。所证的算子相等只用于规定过程中的一个选定终端实验，不扩展到中途任意插入操作、同时输出多个时刻的端点副本或普遍的经典现实断言。证毕。

本命题所用可分 Choi、纠缠破坏及测量后制备的成熟等价性，参见 M. Horodecki、P. W. Shor、M. B. Ruskai，*Entanglement Breaking Channels*，Reviews in Mathematical Physics 15，629–641（2003），[arXiv:quant-ph/0302031v2，定理 4，PDF 第 4—6 页](https://arxiv.org/pdf/quant-ph/0302031v2)，[DOI:10.1142/S0129055X03001709](https://doi.org/10.1142/S0129055X03001709)。其中（A）、（B）、（C）、（D）给出测量后制备、EB、可分 Choi 与秩一 Kraus 的等价性，保迹情形另要求效应构成 POVM；此处各块分支本身不要求保迹，归一化来自所有完整报告块之和。十六项支持界直接使用命题 141.1 的有限凸支持论证，按时间的块历史和逐报告实现由上面的恒等式给出，不附加文献新颖性主张。

<a id="entry-652"></a>

## 追加锚（本行以下为增补区）

<a id="section-152"></a>

## 152. 两隐状态经典生成与有限确定性观察者的锐误差地板

**命题 152.1（逐支纠缠破坏的二元过程与有限更新记忆的统一预测界）。** 固定实数 $0<p<1/2$，令 $R=\mathbb C^2$、$E_i=|i\rangle\langle i|$、$I_2=E_0+E_1$，初态固定为 $\rho=I_2/2$。报告字母表为 $\{0,1\}$，每次使用同一个复线性仪器，对所有 $X\in M_2(\mathbb C)$ 定义
$$
\phi_0(X)=pX_{00}E_0+(1-p)X_{11}E_1,
\qquad
\phi_1(X)=(1-p)X_{00}E_0+pX_{11}E_1.
$$
没有反馈、重置或中间插入的其他操作。记
$$
(c_{bi})_{b,i=0}^1=
\begin{pmatrix}p&1-p\\1-p&p\end{pmatrix},
\qquad K_{bi}=\sqrt{c_{bi}}E_i.
$$
每个报告分支使用两个分别列出的秩一 Kraus 算子 $K_{b0},K_{b1}$，即 $\phi_b(X)=\sum_{i=0}^1K_{bi}XK_{bi}^{\dagger}$。这使每支完全正且不增迹，其效应分别为
$$
F_0=pE_0+(1-p)E_1,\qquad
F_1=(1-p)E_0+pE_1,\qquad F_0+F_1=I_2.
$$
非选择通道为计算基退相干 $X\mapsto X_{00}E_0+X_{11}E_1$。特别地，这里没有用单个对角 Kraus 算子替代每支的两个秩一算子。

令 $\mathcal W=\bigcup_{N\ge0}\{0,1\}^N$ 包含空词 $\varnothing$；词按报告的时间顺序书写，连接记为 $wv$，且
$$
\phi_w=\phi_{w_{|w|}}\circ\cdots\circ\phi_{w_1},
\qquad \phi_{\varnothing}=\operatorname{Id}.
$$
令 $z(w),o(w)$ 分别为零、一的出现次数，并定义
$$
d(w)=z(w)-o(w),\qquad
L_0(w)=p^{z(w)}(1-p)^{o(w)},\qquad
L_1(w)=(1-p)^{z(w)}p^{o(w)},\qquad
\kappa=\frac{1-p}{p}>1.
$$
对任意有限维参考 $A$ 和任意正算子
$$
\Omega_{AR}=\sum_{i,j=0}^1A_{ij}\otimes|i\rangle\langle j|\ge0,
$$
每个 $A_{ii}\ge0$；对所有非空 $w$，有
$$
\phi_w(X)=L_0(w)X_{00}E_0+L_1(w)X_{11}E_1,
\qquad
(\operatorname{Id}_A\otimes\phi_w)(\Omega_{AR})
=L_0(w)A_{00}\otimes E_0+L_1(w)A_{11}\otimes E_1.
$$
因此每个非空报告分支均为纠缠破坏操作：其参考扩张输出是有限正乘积和，非零输出归一化后可分。参考块无须相互交换。这个关于任意输入的公式只断言非空词；空词的恒等操作仍可保持输入纠缠。

对于上面指定的对角初态 $I_2/2$，以下公式则对全部 $w\in\mathcal W$ 成立，包括空词：
$$
Q_w:=\phi_w(I_2/2)=\frac{L_0(w)E_0+L_1(w)E_1}{2},\qquad
P(w):=\operatorname{Tr}Q_w=\frac{L_0(w)+L_1(w)}2>0,
\qquad
\sum_{|w|=N}P(w)=1\quad(N\ge0).
$$
令
$$
q_1(w)=\frac{L_1(w)}{L_0(w)+L_1(w)}
=\frac{\kappa^{d(w)}}{1+\kappa^{d(w)}},
\qquad
\rho_w=\frac{Q_w}{P(w)}=(1-q_1(w))E_0+q_1(w)E_1.
$$
给定历史 $w$ 后下一实际报告为零的概率是
$$
P(0\mid w)=f(d(w)),\qquad
f(d)=p+(1-2p)\frac{\kappa^d}{1+\kappa^d}\quad(d\in\mathbb Z).
$$
对每个有限未来词 $v$，包括空词，完整条件词概率和其末端归一化态分别为
$$
P(v\mid w)=\frac{P(wv)}{P(w)}
=\frac{L_0(w)L_0(v)+L_1(w)L_1(v)}{L_0(w)+L_1(w)},
\qquad
\rho_{wv}=
\frac{E_0+\kappa^{d(w)+d(v)}E_1}{1+\kappa^{d(w)+d(v)}}.
$$
以全部有限未来报告律相等定义有限历史上的预测等价关系，即
$$
w\sim u\quad\Longleftrightarrow\quad
P(v\mid w)=P(v\mid u)\ \text{对所有 }v\in\mathcal W.
$$
则 $w\sim u$ 当且仅当 $d(w)=d(u)$；加入上述每个未来词末端的归一化端点态仍得到同一等价关系。可达商恰为 $\mathbb Z$，零、一报告的更新分别为 $d\mapsto d+1$ 与 $d\mapsto d-1$。在固定长度 $N$，恰有 $N+1$ 个不同可达类 $-N,-N+2,\ldots,N$。跨长度的等价不要求未归一化算子 $Q_w$ 或过去词概率 $P(w)$ 相同。

该报告过程同时有一个精确的两隐状态经典生成实现：起初一次性均匀抽取 $I\in\{0,1\}$ 并始终保留它；给定 $I$，各步使用新的独立随机性，满足
$$
\Pr(0\mid I=0)=p,\qquad \Pr(0\mid I=1)=1-p.
$$
其全部有限词概率恰为 $P(w)$，后验为 $\Pr(I=i\mid w)=L_i(w)/(L_0(w)+L_1(w))$。两个后验质量在每个有限词后均严格为正，所以隐标签 $I$ 不是已观察历史的确定函数。

现在把观察者限定为任意一个非空有限集 $S$、固定初态 $s_0\in S$、两个固定的确定性全函数 $T_0,T_1:S\to S$，以及固定读出 $a:S\to[0,1]$。允许 $a$ 取任意精确实数。递归状态为
$$
s(\varnothing)=s_0,\qquad s(wb)=T_b(s(w))\quad(b\in\{0,1\}).
$$
全部随历史演化且可读的记忆均须包含在 $S$ 内；没有可免费读取的完整档案、无界时钟、生成器隐标签或共享隐藏随机种子。该观察者用 $a(s(w))$ 预测下一报告为零的概率，定义
$$
\mathcal E(S,s_0,T_0,T_1,a)
=\sup_{w\in\mathcal W}|a(s(w))-f(d(w))|,
\qquad \delta=\frac12-p>0.
$$
则每个这样的有限确定性观察者均有
$$
\mathcal E(S,s_0,T_0,T_1,a)\ge\delta,
\qquad
\inf_{\substack{S\ne\varnothing\ \text{有限},\ s_0\in S\\
T_0,T_1:S\to S,\ a:S\to[0,1]}}
\mathcal E(S,s_0,T_0,T_1,a)=\delta.
$$
一个单状态观察者取恒定读出 $a=1/2$ 即达到这个下确界。对该观察者，每个有限词的误差都严格小于 $\delta$，但其上确界等于 $\delta$；不要求存在达到上确界的有限词。二元分布的总变差距离恰等于所定义的绝对概率误差。特别地，$p=1/3$ 时锐界为 $1/6$。

此界的量词覆盖所有可能的有限报告历史，包括概率任意小的历史；它不是平均、典型、几乎必然、有限视界、分类风险或遗憾界。初态及均匀隐先验固定如上，观察者的更新和读出时间齐次且确定；结论不扩张到任意先验、随机观察者、免费时钟或时间依赖的更新与读出。有限视界 $H$ 内存在精确的有限计数器，因而统一无限视界的限制不可省略。这里的整数商是从指定初态出发的有限前缀商，不是无限过去上的因果状态基数结论；两隐状态只给生成实现，不声称隐状态数最小、量子记忆最小或普遍经典性。

证明。由 $E_iXE_i=X_{ii}E_i$ 得所列两个 Kraus 项之和恰为 $\phi_b(X)$，这个等式对全部复矩阵成立。完全正性由 Kraus 表示得到，且
$$
\sum_iK_{bi}^{\dagger}K_{bi}=F_b\le I_2,
\qquad \sum_{b,i}K_{bi}^{\dagger}K_{bi}=I_2,
$$
故各支不增迹，总通道保迹。两支相加给退相干公式。若误用单个
$D_b=\sqrt{c_{b0}}E_0+\sqrt{c_{b1}}E_1$，则
$$
D_b|0\rangle\langle1|D_b^{\dagger}
=\sqrt{p(1-p)}\,|0\rangle\langle1|\ne0,
\qquad \phi_b(|0\rangle\langle1|)=0.
$$
因此单个对角 Kraus 确实定义了保留非对角相干的另一仪器，不能与这里的逐支退相干混用。

参考块的正性来自压缩：对任意 $u\in A$，
$$
\langle u,A_{ii}u\rangle
=\langle u\otimes i,\Omega_{AR}(u\otimes i)\rangle\ge0.
$$
将右侧四个矩阵单位逐个代入 $\phi_b$，非对角块消失，得到
$$
(\operatorname{Id}_A\otimes\phi_b)(\Omega_{AR})
=c_{b0}A_{00}\otimes E_0+c_{b1}A_{11}\otimes E_1.
$$
这是正乘积和，不需要把 $A_{00},A_{11}$ 同时对角化。它们可以不交换，参考系统仍是量子系统。每个后续报告只把两个右对角分量分别再乘以 $c_{b0},c_{b1}$，按非空词长度归纳即得 $L_i(w)$ 的一般输入公式及参考公式。若 $\Omega_{AR}\ne0$，则
$$
\operatorname{Tr}\Omega_{AR}=\operatorname{Tr}A_{00}+\operatorname{Tr}A_{11}>0,
$$
且两个 $L_i(w)>0$，所以每个非空输出的迹均严格为正。删去迹零的正因子项，并将各项除以其迹，便把归一化输出写成乘积密度的凸组合；零输入的输出为零。特别地每个一步分支已经纠缠破坏。空词不经过任何这样的消相干步骤，其参考输出仍为 $\Omega_{AR}$，故上述一般输入结论没有偷偷包含恒等分支。

对指定 $I_2/2$，非空词的 $Q_w$ 公式由一般输入式直接得到；空词则由 $L_0(\varnothing)=L_1(\varnothing)=1$ 单独核实。$0<p<1$ 保证每个 $P(w)>0$。逐位置求和或用二项式展开，给出
$$
\sum_{|w|=N}L_0(w)=(p+(1-p))^N=1,
\qquad
\sum_{|w|=N}L_1(w)=((1-p)+p)^N=1.
$$
因此每个长度的词概率和为一，包括 $N=0$；又因 $c_{0i}+c_{1i}=1$，有 $P(w0)+P(w1)=P(w)$，这些词律具有前缀一致性。直接相除可得
$$
\frac{L_1(w)}{L_0(w)}=\left(\frac{1-p}{p}\right)^{z(w)-o(w)}=\kappa^{d(w)},
$$
故得到 $q_1(w)$ 和 $\rho_w$。下一零报告的条件概率由效应 $F_0$ 给出
$$
\operatorname{Tr}(F_0\rho_w)
=p(1-q_1(w))+(1-p)q_1(w)=f(d(w)).
$$
连接词满足 $L_i(wv)=L_i(w)L_i(v)$ 及 $d(wv)=d(w)+d(v)$，故条件词概率和条件末端态均等于陈述中的表达式。对于 $v=\varnothing$，两式分别给一和 $\rho_w$。

这些公式已证明相同 $d$ 决定所有有限未来报告律及归一化末端态。反过来，
$$
f(d+1)-f(d)
=(1-2p)\frac{(\kappa-1)\kappa^d}{(1+\kappa^d)(1+\kappa^{d+1})}>0.
$$
所以不同整数 $d$ 的下一零报告概率已不同，不会落在同一预测类。每个 $d\ge0$ 由 $0^d$ 达到，每个 $d<0$ 由 $1^{-d}$ 达到；固定长度 $N$ 时，$z=0,\ldots,N$ 给 $d=2z-N$，且每个词都有正概率。这同时证明商为 $\mathbb Z$、指定的两个更新以及固定长度的 $N+1$ 个类。

这一商的充分性和区分类义也可直接置于既有 `causal_state_factorization` 的假设中：以有限词为过去集，以 $w\mapsto(P(v\mid w))_{v\in\mathcal W}$ 为未来律映射，以任一能恢复该映射的确定摘要为接口。该结果给出摘要的可达像到未来律可达像的唯一因子；不同未来律须有不同接口值。此处已经由显式公式把未来律可达像识别为 $\mathbb Z$，无需另加一个有限状态假设或重建因子化定理。它只约束这些有限前缀及指定的未来律。归一化之所以关键，可由同为 $d=0$ 的 $\varnothing$ 与 $01$ 看出：
$$
Q_{\varnothing}=I_2/2,\qquad P(\varnothing)=1,
\qquad
Q_{01}=p(1-p)I_2/2,\qquad P(01)=p(1-p),
\qquad
\rho_{\varnothing}=\rho_{01}=I_2/2.
$$
因此相同预测类并没有抹掉过去发生该词的权重差异。

再看生成实现。给定 $I=0$ 或 $I=1$，独立条件发射的词概率分别为 $L_0(w),L_1(w)$；均匀混合即为 $P(w)$。Bayes 公式遂给两项所述后验，而 $L_i(w)>0$ 排除了任何有限词完全揭示 $I$ 的可能。这正是《情境时空算术·机器学习》命题30.4中一维重复噪声示范的计数或对数赔率摘要：取潜在无噪声答案为 $1-I$、翻转噪声率为 $p$，对数后验赔率为 $d(w)\log\kappa$。依该卷命题32.1的目标变量区分，$q_1(w)$ 是潜在标签的后验，实际下一报告的零概率则是 $p+(1-2p)q_1(w)$，两者不能替换。依定理32.3，本过程的动作及发射协议固定，无另需读取的动态控制状态；故这里的后验充分性并未省去一个随历史变化的策略模式。命题30.4的计数表示也不表示计数取值有限，且其一般显式后验表成本须按勘误32.5理解为所指定表示的上界。

现在先固定任意一个符合陈述的有限观察者，再选择依赖于它的历史。将既有 `finite_orbit_and_readout_eventually_periodic` 应用于有限集 $S$ 上的自映射 $T_0$、读出 $a$ 和初态 $s_0$，得到整数 $n\ge0$、$\ell\ge1$，满足 $n+\ell\le|S|$，且零输入轨道从 $n$ 起以 $\ell$ 为周期。重复该周期等式便有
$$
s(0^{n+k\ell})=s(0^n)\quad(k\ge0).
$$
这里直接使用有限轨道结论，不要求读出值有限精度，也不要求零输入轨道最终固定。

对任意整数 $m\ge1$，取两条历史
$$
w_m^-=0^n1^{n+m\ell},\qquad
w_m^+=0^{n+2m\ell}1^{n+m\ell}.
$$
两个零前缀的观察者状态相同，再按相同时间顺序读入共同的一串 $n+m\ell$ 个一，确定性给出
$$
s(w_m^-)=T_1^{\,n+m\ell}(s(0^n))
=T_1^{\,n+m\ell}(s(0^{n+2m\ell}))
=s(w_m^+)=:s_m.
$$
幂号在此表示函数迭代。实际计数却为
$$
d(w_m^-)=-m\ell,\qquad d(w_m^+)=m\ell.
$$
两条词的长度分别为 $2n+m\ell$ 与 $2n+3m\ell$，不相等，但都属于所定义上确界的范围且概率严格为正。允许 $s_m$ 及 $a(s_m)$ 随 $m$ 改变；论证不取这列读出的极限。

令 $t_m=\kappa^{m\ell}>1$。用同一读出值 $a(s_m)$ 对两项真概率的三角不等式，得到
$$
\begin{aligned}
\mathcal E
&\ge\max\{|a(s_m)-f(-m\ell)|,\ |a(s_m)-f(m\ell)|\}\\
&\ge\frac{f(m\ell)-f(-m\ell)}2
=\delta\frac{t_m-1}{t_m+1}.
\end{aligned}
$$
第二步只使用 $|x-y|\le|x-a|+|a-y|\le2\max\{|x-a|,|a-y|\}$，即已有半直径论证的基本不等式。这里没有把带有限状态及折扣条件的 ML 定理17.5整体应用于无限的有限历史集合。

由于 $\kappa^\ell>1$，有 $t_m\to\infty$，故右端趋于 $\delta$。等价地，对任意 $0\le\varepsilon<\delta$，可取 $m\ge1$ 使
$$
\kappa^{m\ell}>\frac{\delta+\varepsilon}{\delta-\varepsilon},
$$
从而 $\mathcal E>\varepsilon$。这样的 $m$ 存在，例如由
$(\kappa^\ell)^m\ge1+m(\kappa^\ell-1)$ 可知左端无界。若 $\mathcal E<\delta$，取 $\varepsilon=\mathcal E$ 即矛盾，因此每个有限观察者都满足 $\mathcal E\ge\delta$；所需历史可以随观察者和精度要求改变，状态数只影响这些历史的选择而不改变地板。

另一方面，单点集上的两个更新皆为恒等，取 $a=1/2$，则每个有限整数 $d$ 都有
$$
\left|\frac12-f(d)\right|
=\delta\frac{|\kappa^d-1|}{1+\kappa^d}<\delta.
$$
沿 $0^N$ 或 $1^N$ 令 $N\to\infty$，误差趋于 $\delta$，所以该单状态观察者的上确界恰为 $\delta$。结合下界，得到所有有限观察者的最优统一误差及其达到者。对二元预测分布直接计算
$$
\operatorname{TV}\bigl((a,1-a),(f,1-f)\bigr)
=\tfrac12\bigl(|a-f|+|(1-a)-(1-f)|\bigr)=|a-f|,
$$
即可得到同一总变差结论；代入 $p=1/3$ 给 $\delta=1/6$。

最后明确有限视界边界。对任意整数 $H\ge0$，令
$$
S_H=\{-H,-H+1,\ldots,H\},\qquad
s_0=0,\qquad
T_0(j)=\min\{H,j+1\},\qquad
T_1(j)=\max\{-H,j-1\},\qquad a(j)=f(j).
$$
对长度至多 $H$ 的历史，归纳中每个真正计数都在 $[-H,H]$，且在尚需进行的前 $H$ 步内不会因截断丢失计数，故 $s(w)=d(w)$，下一报告预测完全精确。$H=0$ 时仅要求空词处精确，也成立。这不反驳上面的界，因为那里的同状态历史长度没有预先统一上限。精确实数读出已获允许，所以所证障碍来自固定有限状态的更新记忆，而非舍入精度。任意参考的正块公式只表明所指定右侧分支逐支纠缠破坏，不把参考经典化，也不把生成器持有的隐标签赠予观察者。整个显式构造与下界不以命题146.1—151.1的分块、输入族或支持界为数学前提；它具体体现命题151.1所区分的有限生成隐支持与可访问的递归充分观察者状态。证毕。

本命题的后验引用为[《情境时空算术·机器学习》命题30.4、命题32.1、定理32.3及勘误32.5](../CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)；半直径步骤仅引用该卷定理17.5证明中的三角不等式，不沿用其有限状态与折扣假设。所直接使用的抽象结果分别为 [`causal_state_factorization`](../../../../D5/S3/ObserverMemory/PredictionFactors/CausalStateFactorization.lean) 和 [`finite_orbit_and_readout_eventually_periodic`](../../../../D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound.lean)，应用域及参数已在证明中给出。关于有限记忆的相关问题，T. Berg、O. Ordentlich、O. Shayevitz，*Binary Hypothesis Testing with Deterministic Finite-Memory Decision Rules*，2020 IEEE International Symposium on Information Theory，1259–1264，[arXiv:2005.07445](https://arxiv.org/abs/2005.07445)，[DOI:10.1109/ISIT44484.2020.9174505](https://doi.org/10.1109/ISIT44484.2020.9174505)，研究长时间极限中的二元假设分类 Bayes 错误及其随状态数的变化；其损失不同于本命题对全部有限历史的下一报告概率误差上确界，不能将这里的 $1/2-p$ 地板归于该文。上述逐式推导不附加新颖性或穷尽文献的主张。

<a id="entry-654"></a>

## 追加锚（本行以下为增补区）

<a id="section-153"></a>

## 153. 正混合下的有限后缀观察与无限精确预测商

**命题 153.1（正潜在混合允许任意精度的有限确定性因果后缀观察者，而精确预测商仍无限）。** 固定时间齐次、无控制的二元协议，取实数 $0<p<1/2$ 与 $0<r<1/2$。令 $E_i=|i\rangle\langle i|$、$I_2=E_0+E_1$，并定义
$$
c_{00}=c_{11}=p,\qquad c_{01}=c_{10}=1-p,\qquad
P_{ji}=\begin{cases}1-r,&j=i,\\ r,&j\ne i.\end{cases}
$$
对每个 $b,i,j\in\{0,1\}$ 分别取秩一 Kraus 算子
$$
K_{bji}=\sqrt{c_{bi}P_{ji}}\;|j\rangle\langle i|,
\qquad
\phi_b(X)=\sum_{i,j=0}^1K_{bji}XK_{bji}^{\dagger}
=\sum_{i,j=0}^1c_{bi}P_{ji}X_{ii}E_j
\quad(X\in M_2(\mathbb C)).
$$
每支使用四个独立的 Kraus 项，不能先把它们相加成一个算子再取共轭作用。每支完全正，其效应满足
$$
pI_2\le\phi_b^*(I_2)=\sum_i c_{bi}E_i\le(1-p)I_2,
\qquad \sum_b\phi_b^*(I_2)=I_2.
$$
非选择通道是先退相干再按 $P$ 翻转。词 $w=b_1\cdots b_n$ 按时间顺序书写，置 $\phi_w=\phi_{b_n}\circ\cdots\circ\phi_{b_1}$、$\phi_\varnothing=\operatorname{Id}$。对任意有限维参考 $A$ 及任意正联合算子 $\Omega\ge0$，每个非空词的 $(\operatorname{Id}_A\otimes\phi_w)(\Omega)$ 都是有限正乘积和；非零输入的输出归一化后可分。空词在一般输入上仍为恒等作用，可以保留纠缠。这项逐支纠缠破坏结论与下面从固定初态 $I_2/2$ 出发的标量预测结论分别成立；可分不等于参考独立，也不意味着标量后验能恢复初始参考相关性。

标量过程固定初态为 $I_2/2$。取列向量约定，令
$$
M_b=P\operatorname{diag}(c_{b0},c_{b1}),\qquad
v_\varnothing=\binom{1/2}{1/2},\qquad
v_w=M_{b_n}\cdots M_{b_1}v_\varnothing,
$$
$$
Q_w=\phi_w(I_2/2)=\operatorname{diag}(v_w),\qquad
Z_w=\mathbf1^{\mathsf T}v_w,\qquad
q_w=\frac{(v_w)_1}{Z_w},\qquad
\rho(q)=(1-q)E_0+qE_1.
$$
则 $Z_w\ge p^{|w|}>0$，$\sum_{|w|=n}Z_w=1$，且 $0<q_w<1$，包括空词。给定历史后下一零报告概率及收到 $b$ 后的归一化递推分别为
$$
f(q)=p+(1-2p)q,\qquad
\widetilde q=\frac{c_{b1}q}{c_{b0}(1-q)+c_{b1}q},\qquad
q'=r+(1-2r)\widetilde q.
$$
即旧隐藏位先发射，随后混合；先混合后发射是另一仪器。

令
$$
\eta=1-2r\in(0,1),\quad
\lambda=\log\frac{1-p}{p}>0,\quad
B=\log\frac{1-r}{r}>0,\quad
\sigma(x)=\frac{e^x}{1+e^x},\quad
\ell_w=\log\frac{q_w}{1-q_w},
$$
$$
G(x)=\log\frac{r+(1-r)e^x}{(1-r)+re^x},\qquad
F_b(x)=G\bigl(x+(-1)^b\lambda\bigr),\qquad
F_w=F_{b_n}\circ\cdots\circ F_{b_1},\quad F_\varnothing=\operatorname{Id}.
$$
则 $\ell_w=F_w(0)$，$G$ 为奇函数，严格递增，值域为 $(-B,B)$，且 $0<G'(x)\le\eta$。对任意共同报告词 $u$，有
$$
|F_u(x)-F_u(y)|\le\eta^{|u|}|x-y|\qquad(x,y\in\mathbb R).
$$

对整数 $k\ge0$，定义有限观察者的全部动态记忆为
$$
S_k=\bigcup_{j=0}^k\{0,1\}^j,\qquad s_0=\varnothing,\qquad
T_b(s)=\operatorname{tail}_{\min(k,|s|+1)}(sb),
$$
其中 $\operatorname{tail}_m$ 取时间顺序下最后 $m$ 个符号，$\operatorname{tail}_0=\varnothing$。因此 $k=0$ 时两个更新恒取空词。每个状态的后验、端点及下一零报告读出是固定表
$$
h_k(s)=\sigma(F_s(0)),\qquad R_k(s)=\rho(h_k(s)),\qquad a_k(s)=f(h_k(s)).
$$
状态递推为 $s(\varnothing)=\varnothing$、$s(wb)=T_b(s(w))$，令 $\widehat q_w=h_k(s(w))$。这些表是随 $p,r,k$ 固定的数学常数，不是另行动态存储的实数后验。所有填充阶段的长度信息已包含在 $S_k$，没有外置时钟或可读取的历史档案；连同初始空词及所有短词，指定状态总数恰为
$$
|S_k|=\sum_{j=0}^k2^j=2^{k+1}-1.
$$

长度 $n\le k$ 时读出精确。对全部有限历史，置 $E_k=\min(1,B\eta^k/4)$，有
$$
D(\rho(q_w),R_k(s(w)))=|q_w-\widehat q_w|\le E_k,
$$
$$
\operatorname{TV}\bigl((f(q_w),1-f(q_w)),(a_k(s(w)),1-a_k(s(w)))\bigr)
=(1-2p)|q_w-\widehat q_w|\le(1-2p)E_k.
$$
这里 $D(U,V)=\tfrac12\|U-V\|_1$，$\operatorname{TV}(\mu,\nu)=\tfrac12\sum_y|\mu(y)-\nu(y)|$。给定任意 $\varepsilon>0$，取
$$
k=\max\!\left(0,\left\lceil\frac{\log(C/\varepsilon)}{-\log\eta}\right\rceil\right),
\qquad C=\frac{(1-2p)B}{4},
$$
即可使全部有限历史的下一报告误差不超过 $\varepsilon$；端点精度使用同式的 $C=B/4$。若报告读出另以 $\bar a_k:S_k\to[0,1]$ 近似，且 $|\bar a_k(s)-a_k(s)|\le\delta$，则报告误差至多 $\min(1,C\eta^k+\delta)$；符号更新不累积舍入误差。若 $p,r$ 有理，全部 $h_k(s),a_k(s)$ 可用概率递推精确计算为有理数，不需计算对数。对任意实参数只断言固定精确实数表的数学存在，不断言不可计算实参数的有效构造、最小状态数或位复杂度。

然而，以所有有限未来报告律相等定义的精确预测商仍有无限多个类，任何固定有限状态的确定性观察者都不能精确预测每个有限历史的下一报告。混合是本模型的额外假设，不由纠缠破坏推出；本命题不以第152节的误差下界为前提。量词只涉及固定 $p,r$、固定初态、时间齐次无控制协议与全部有限历史，包括稀有历史；不主张 $r\to0$ 的一致界、历史重建、最优记忆或普遍经典性。边界值 $r=1/2$ 或 $p=1/2$ 不在严格预测区分的结论内。

**证明。** 对任意复矩阵 $X$，逐个矩阵单位相乘给
$$
K_{bji}XK_{bji}^\dagger=c_{bi}P_{ji}X_{ii}E_j,\qquad
K_{bji}^\dagger K_{bji}=c_{bi}P_{ji}E_i.
$$
按 $i,j$ 求和，利用 $\sum_jP_{ji}=1$，即得所列分支、效应与完全正性；再用 $\sum_bc_{bi}=1$ 得总效应为 $I_2$，以及总通道
$$
\sum_b\phi_b(X)=\sum_{i,j}P_{ji}X_{ii}E_j.
$$
这就是退相干后翻转。特别地，它对非对角矩阵单位的输出为零，不能由合并 Kraus 振幅代替。

现在独立取任意 $\Omega\ge0$ 于 $A\otimes\mathbb C^2$，写成 $\Omega=\sum_{i,i'}\Omega_{ii'}\otimes|i\rangle\langle i'|$。每个对角块由压缩为正：对任意 $u\in A$，
$$
\langle u,\Omega_{ii}u\rangle
=\langle u\otimes i,\Omega(u\otimes i)\rangle\ge0.
$$
一次分支给 $\sum_{i,j}c_{bi}P_{ji}\Omega_{ii}\otimes E_j$。对非空词长度归纳，得到
$$
(\operatorname{Id}_A\otimes\phi_w)(\Omega)
=\sum_{i_0,\ldots,i_n\in\{0,1\}}
\left(\prod_{t=1}^n c_{b_t i_{t-1}}P_{i_t i_{t-1}}\right)
\Omega_{i_0i_0}\otimes E_{i_n}.
$$
所有系数严格为正，两个参考块为正，无须彼此交换。效应下界在每一步给输出迹至少为前一步的 $p$ 倍，故非零正输入在词 $w$ 后的迹至少为 $p^n\operatorname{Tr}\Omega>0$。删去迹零项，把其余正因子除以各自迹，即把归一化输出写成乘积密度矩阵的凸组合。零输入输出为零。空词没有经过这些分支，作用仍为 $\operatorname{Id}_A\otimes\operatorname{Id}$；以上非空公式不用于推断空词可分。

再回到指定初态。$Q_\varnothing=I_2/2$；分支公式按长度归纳给 $v_{wb}=M_bv_w$ 及 $Q_w=\operatorname{diag}(v_w)$。$v_\varnothing$ 两分量严格为正，而 $M_b$ 的每项严格为正，所以所有有限词的两分量都为正，后验及其对数赔率均有定义。又
$$
Z_{wb}=c_{b0}(v_w)_0+c_{b1}(v_w)_1,
\qquad pZ_w\le Z_{wb}\le(1-p)Z_w,
\qquad Z_{w0}+Z_{w1}=Z_w.
$$
由 $Z_\varnothing=1$ 归纳，得到 $Z_w\ge p^{|w|}$ 和各固定长度的概率总和为一，包括长度零。除以 $Z_w$ 得条件报告权重；对 $b=0$ 即为 $f(q_w)$。旧位在看到 $b$ 后的条件质量为 $\widetilde q$，再按 $P$ 翻转给 $q'=r+\eta\widetilde q$。由于 $0<\widetilde q<1$，每次非空更新后 $r<q'<1-r$。相反次序使用 $\operatorname{diag}(c_{b0},c_{b1})P$；例如输入 $E_0$ 时本仪器报告零的概率是 $p$，反序为 $p+(1-2p)r>p$。两者在均匀初态上的首报告权重都为 $1/2$，不能据此认同递推。

发射一步把赔率乘以 $c_{b1}/c_{b0}$，其对数增加 $(-1)^b\lambda$；翻转一步把旧赔率 $e^x$ 变为 $[r+(1-r)e^x]/[(1-r)+re^x]$，遂得 $\ell_{wb}=F_b(\ell_w)$。将 $G(-x)$ 的分子、分母同时乘以 $e^x$，得
$$
G(-x)=\log\frac{re^x+1-r}{(1-r)e^x+r}=-G(x),\qquad G(0)=0,
$$
$$
\lim_{x\to+\infty}G(x)=B,\qquad
\lim_{x\to-\infty}G(x)=-B.
$$
直接对两项对数求导：
$$
G'(x)=\frac{(1-r)e^x}{r+(1-r)e^x}
-\frac{re^x}{(1-r)+re^x}
=\frac{\eta e^x}{(r+(1-r)e^x)((1-r)+re^x)}.
$$
分母除以 $e^x$ 恰为
$$
r(1-r)(e^x+e^{-x})+r^2+(1-r)^2
=1+r(1-r)(e^x+e^{-x}-2)\ge1,
$$
因为 $e^x+e^{-x}-2=(e^{x/2}-e^{-x/2})^2\ge0$，等号仅在 $x=0$。因此 $0<G'(x)\le\eta<1$，且 $G'(0)=\eta$。严格递增性、连续性与上述两端极限共同给出值域恰为 $(-B,B)$。每个平移后的 $F_b$ 都具有同一个全局 Lipschitz 常数 $\eta$。若 $u=d_1\cdots d_m$，逐次对 $F_{d_t}$ 用均值定理，归纳得
$$
|F_{d_t}\cdots F_{d_1}(x)-F_{d_t}\cdots F_{d_1}(y)|
\le\eta^t|x-y|\qquad(0\le t\le m).
$$
$t=0$ 是恒等式。这证明的是任意共同词的复合收缩，不把不同报告的更新当作一个映射的幂。

这一常数也与经典正核理论精确一致。对严格正二向量，Hilbert 距离是
$$
d_{\mathrm H}(u,v)=\log\frac{\max_i u_i/v_i}{\min_i u_i/v_i}
=\left|\log\frac{u_1}{u_0}-\log\frac{v_1}{v_0}\right|.
$$
正对角乘法同时消去比值中的相同因子，故为等距映射。$P$ 的输出对数赔率为 $G$，其值域给射影直径的上确界 $2B$；具体交比也给
$$
\max_{i,i',j,j'}\frac{P_{ji}P_{j'i'}}{P_{ji'}P_{j'i}}
=\frac{(1-r)^2}{r^2}=e^{2B},
$$
因为这些比值只可能为 $1$、$(1-r)^2/r^2$ 或其倒数。正核的 Birkhoff 系数公式由下列 Atar–Zeitouni 式(9)–(12)及 Le Gland–Oudjane 最终版引理3.8给出；代入即为
$$
\tanh\frac{2B}{4}=\frac{e^B-1}{e^B+1}
=\frac{(1-r)/r-1}{(1-r)/r+1}=1-2r=\eta.
$$
上面的直接导数证明同时给出本例的全局界及其在零点的极限斜率，无需另加未经证明的一般收缩步骤。

对观察者的符号递推归纳：若 $n<k$，向整个已存历史追加一个符号后长度仍不超过 $k$；若 $n\ge k$，向最后 $k$ 个符号追加后再取尾，所得正是新历史的最后 $k$ 个符号。$k=0$ 时每一步都为空。因此 $s(w)=w$ 当 $|w|\le k$，否则 $s(w)=\operatorname{tail}_k(w)$。不同长度的词是不交的状态，计数为所列几何和，且每个状态可由其同名报告词达到。短词、空词和填充长度均已计入；固定的 $T_0,T_1,h_k,R_k,a_k$ 不读取额外动态记忆。

当 $n\le k$，同一初值和完整词给 $\widehat q_w=q_w$。当 $n>k$，写 $w=tu$、$|u|=k$、$|t|\ge1$。由 $G$ 的值域，$|\ell_t|<B$；表沿同一 $u$ 从零重新计算，故
$$
|\ell_w-F_u(0)|=|F_u(\ell_t)-F_u(0)|
\le\eta^k|\ell_t|\le B\eta^k.
$$
此式包括 $k=0$ 的恒等复合。$\sigma'(x)=e^x/(1+e^x)^2\le1/4$，因为 $(1+e^x)^2-4e^x=(e^x-1)^2\ge0$。均值定理及概率差至多一给 $|q_w-\widehat q_w|\le E_k$。两个对角态之差的特征值为 $\pm(q_w-\widehat q_w)$，所以迹距离恰为该绝对差。二元报告 TV 也恰为零报告概率差，再用 $f$ 的斜率得 $(1-2p)E_k$。此界还蕴含较松的 $\min(1,(1-2p)B\eta^k/4)$，不混淆两种截断。若 $C\le\varepsilon$，所选 $k=0$ 已有 $C\eta^k\le\varepsilon$；否则所选整数满足 $k(-\log\eta)\ge\log(C/\varepsilon)$，指数化即得同一不等式。对端点换用 $C=B/4$。舍入后的界用一次三角不等式，更新仍只在符号状态上进行，故不存在逐步后验舍入项。对有理 $p,r$，从 $1/2$ 开始，每步概率递推仅用有理数加乘和严格正分母的除法；有限多词因而给有理有限表。

还可在同一证明内比较一次端点替换后的完整未来。对固定整数 $H\ge0$，明确取原仪器的报告及终端端点通道
$$
\mathcal C_H(X)=\sum_{u\in\{0,1\}^H}|u\rangle\langle u|\otimes\phi_u(X).
$$
它保留每一个未来报告旗标和一个终端量子端点；若指定一次终端 POVM 查询，就对这个端点应用同一测量通道，所有未来旗标仍保留。以下两输入使用同一个 $\mathcal C_H$（有查询时也使用同一个复合通道）。每支完全正且总仪器保迹，按 $H$ 归纳有 $\sum_{|u|=H}\operatorname{Tr}\phi_u(X)=\operatorname{Tr}X$，所以 $\mathcal C_H$ 完全正保迹。$H=0$ 时仅有空旗标，$\mathcal C_0$ 在端点上就是恒等。令 $A_i=\mathcal C_H(E_i)$，于是 $A_i\ge0$、$\operatorname{Tr}A_i=1$。线性性给
$$
\Omega_H(q):=\mathcal C_H(\rho(q))=(1-q)A_0+qA_1,
$$
$$
D(\Omega_H(q_w),\Omega_H(\widehat q_w))
=\frac{|q_w-\widehat q_w|}{2}\|A_1-A_0\|_1
\le |q_w-\widehat q_w|\le E_k,
$$
其中 $\|A_1-A_0\|_1\le\|A_1\|_1+\|A_0\|_1=2$；加入指定终端查询时，其同一复合通道的两项输出仍正且迹一，论证不变。这只从两个指定端点态开始，不重构任意初始相关参考，也不由无条件界推出后选择不扩张。

一次初始端点替换后精确继续，与每一步用后缀读出重新生成报告是不同操作。取 $p=1/3,r=1/4,k=0$，初始端点本来精确，但滚动恒定读出为 $1/2$，两步报告独立均匀。真实首报告零的概率为 $1/2$，其后验是 $1/4+(1/2)(2/3)=7/12$，下一零概率是 $1/3+(1/3)(7/12)=19/36$；故 $P(00)=19/72$。对称性及每个首报告概率为 $1/2$ 给出完整的两报告律（依次为 $00,01,10,11$）
$$
P_2=\frac1{72}(19,17,17,19),\qquad
\widehat P_2=\frac1{72}(18,18,18,18).
$$
所以单个 $00$ 事件的概率差为 $|19/72-1/4|=1/72$，而整个两报告律的
$$
\operatorname{TV}(P_2,\widehat P_2)=\frac12\frac{1+1+1+1}{72}=\frac1{36}.
$$
若只在初始时替换同一个 $I_2/2$ 再按原仪器精确继续，两输出则完全相同。对本模型的指定共同未来词另用已证复合收缩，还可把上面的对数赔率误差界乘以 $\eta^H$；这项条件更新事实来自显式递推，而非无条件迹距离界。

最后证明无限精确区分。令 $a_0=0$、$a_{n+1}=F_0(a_n)$。由 $\lambda>0$、$G(0)=0$ 和严格递增性，$a_1=G(\lambda)>a_0$。若 $n\ge1$ 且 $a_n>a_{n-1}$，严格递增的 $F_0$ 给
$$
a_{n+1}=F_0(a_n)>F_0(a_{n-1})=a_n.
$$
从而对所有有限 $n$ 严格递增；不需要假设某个轨道区间上 $F_0(x)-x>0$。虽然 $0\le a_n<B$，有界性不会造成有限时重复。$\sigma$ 和 $f$ 都严格递增，所以 $0^n$ 的下一报告律 $f(\sigma(a_n))$ 两两不同，且每个词的概率至少为 $p^n>0$。若观察者只有有限状态，取比状态数多的这些前缀，必有两个不同长度的零词落在同一状态；固定读出在两处相同，与真实下一报告律不同矛盾。完整未来预测等价要求每个有限未来词概率相同，特别要求下一报告律相同，故这些前缀也属于两两不同的完整未来类。此处只需商的无限性，不把有混合时的有序词商识别为第152节的整数计数商。证毕。

本命题的 Kraus、Born 与正概率条件化约定使用本量子卷假设1.2及[《情境时空算术·机器学习》定义20.5](../CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)；分支迹与效应 Born 权重的通式见既有 [`finite_kraus_instrument_born_marginal`](../../../../D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal.lean)，此处取单一设置、二元报告和四项 Kraus 指标。旧位发射后的 Bayes 乘权及归一化使用 ML 定理30.3证明中的一步公式；该定理的固定假设标签并非本节会翻转的隐藏位，混合步骤已在本节单独推导。共同词的几何误差传播对应 ML 定义21.1与定理21.2中 $L=\eta$、每步闭合及求值误差为零的情形；ML 定理21.6在其有限载体、联合核误差与共同策略假设下给出完整记录累计界 $1-(1-\varepsilon)^H$，命题21.7说明终端状态收缩不能消去已经写入的记录差异，只用于上述滚动生成的边界区分，不充当后验或 Kraus 定理。一次端点替换的正保迹传播是本量子卷定理50.4证明所用数据处理原则的具体两端点情形，已由正性、线性与迹范数直接算出。本量子卷命题124.10给出的静态任务满足 $e_k=\tfrac2{15}4^{-k}>0$ 且 $e_k\to0$，只用于区分任意精度的有限表示与精确有限表示，不作为本节动态收缩或下界的前提。

正核工具的文献来源为 R. Atar、O. Zeitouni，*Exponential stability for nonlinear filtering*，*Annales de l'Institut Henri Poincaré, Probabilités et Statistiques* 33(6) (1997), 697–725，[原刊扫描](https://www.numdam.org/item/AIHPB_1997__33_6_697_0.pdf)，印刷页703–704式(9)–(12)分别给出 Hilbert 度量、Birkhoff 系数、核表示与交比直径；F. Le Gland、N. Oudjane，*Stability and uniform approximation of nonlinear filters using the Hilbert metric and application to particle filters*，*The Annals of Applied Probability* 14(1) (2004), 144–187，[DOI:10.1214/aoap/1075828050](https://doi.org/10.1214/aoap/1075828050)，[最终刊版作者 PDF](https://www.irisa.fr/aspi/legland/pub/legland04a.pdf)，其中引理3.8、式(11)，印刷页152–153，给出 $\tau(K)=\tanh(H(K)/4)$；这里的编号专指最终刊版。有限窗口方法参见 A. D. Kara、S. Yüksel，*Near Optimality of Finite Memory Feedback Policies in Partially Observed Markov Decision Processes*，*Journal of Machine Learning Research* 23(11) (2022), 1–46，[期刊页](https://jmlr.org/papers/v23/20-1152.html)、[论文](https://jmlr.org/papers/volume23/20-1152/20-1152.pdf)，第3节第10–12页以固定重启先验及有限观察、动作窗口构造有限信念集合，第2.2节定理5第7页及第12页讨论使用期望滤波误差而非对所有观察实现的一致误差。本节的全历史界来自上述具体正二态核的逐词证明，不把该文的期望结论提升为一致结论；Hilbert 遗忘及有限窗口方法均为既有工具，不附加优先性主张。

<a id="entry-656"></a>

## 追加锚（本行以下为增补区）

<a id="section-154"></a>

## 154. 正混合二元仪器的区间稠密阈值与有限观察者状态阶

**命题 154.1（全有限历史下一报告精度的区间阈值、普适状态下界与因果网格上界）。** 固定已知实参数 $0<p<1/2$、$0<r<1/2$，使用命题153.1的时间齐次、无控制二元协议及固定先验 $I_2/2$。具体地，在 $M_2(\mathbb C)$ 上令 $E_i=|i\rangle\langle i|$、$I_2=E_0+E_1$，并取
$$
c_{00}=c_{11}=p,\qquad c_{01}=c_{10}=1-p,\qquad
P_{ji}=\begin{cases}1-r,&j=i,\\r,&j\ne i,\end{cases}
$$
$$
K_{bji}=\sqrt{c_{bi}P_{ji}}\,|j\rangle\langle i|,
\qquad
\phi_b(X)=\sum_{i,j=0}^1K_{bji}XK_{bji}^{\dagger}
=\sum_{i,j=0}^1c_{bi}P_{ji}X_{ii}E_j.
$$
$c_{bi}$ 的指标依次为报告和旧隐藏位；每支的四个 Kraus 项分别求共轭作用再相加。物理次序为旧隐藏位先发射报告，再按 $P$ 翻转到新隐藏位。报告词 $w=b_1\cdots b_n$ 按时间顺序书写，$\phi_w=\phi_{b_n}\circ\cdots\circ\phi_{b_1}$，空操作 $\phi_\varnothing=\operatorname{Id}$。令
$$
v_\varnothing=\binom{1/2}{1/2},\qquad
v_{wb}=P\operatorname{diag}(c_{b0},c_{b1})v_w,\qquad
Z_w=\mathbf1^{\mathsf T}v_w,\qquad q_w=\frac{(v_w)_1}{Z_w}.
$$
这里 $\phi_w(I_2/2)=\operatorname{diag}(v_w)$，$Z_w$ 是词的标量 Born 概率，满足 $Z_w\ge p^{|w|}>0$；这不是对 $v_w$ 各分量的同一下界。所有 $q_w\in(0,1)$，且 $q_\varnothing=1/2$。下一零报告的条件概率为
$$
f(q)=p+dq,\qquad d=1-2p>0.
$$

观察者由有限非空集合 $S$、固定初态 $s_0\in S$、两个固定确定性更新 $T_b:S\to S$ 及固定读出 $t:S\to[0,1]$ 组成。规定
$$
T_w=T_{b_n}\circ\cdots\circ T_{b_1},\qquad
T_\varnothing=\operatorname{Id},\qquad
\mathcal E(S,s_0,T_0,T_1,t)
=\sup_{w\in\{0,1\}^{*}}\bigl|t(T_w(s_0))-f(q_w)\bigr|.
$$
上确界取遍每一个有限词，包括空词及任意低概率的词。所有可读的演化记忆均计入 $S$；不另给可读时钟、历史档案、随机种子或连续运行寄存器。对 $\varepsilon>0$ 定义
$$
N_{\min}(\varepsilon)
=\min\left\{|S|:\mathcal E(S,s_0,T_0,T_1,t)\le\varepsilon\right\}.
$$
下述有限构造保证取最小值的集合是非空的正整数集合。所计成本为观察者状态基数，不是物理隐藏态数、存储位数或固定表的描述成本；观察者可依赖已知的 $p,r,\varepsilon$，但同一观察者用于所有词长。

置
$$
\eta=1-2r\in(0,1),\qquad
\lambda=\log\frac{1-p}{p}>0,\qquad
q_+=\frac{d-r+\sqrt{r^2+\eta d^2}}{2d},
$$
$$
a=\log\frac{q_+}{1-q_+},\qquad I=[-a,a],\qquad
\sigma(x)=\frac{e^x}{1+e^x},\qquad h(x)=f(\sigma(x)),
$$
$$
J=[f(1-q_+),f(q_+)],\qquad
L=d(2q_+-1)=\sqrt{r^2+\eta d^2}-r.
$$
则 $1/2<q_+<1$、$a>0$、$L>0$。沿用命题153.1的对数赔率及更新
$$
\ell_w=\log\frac{q_w}{1-q_w},\qquad\ell_\varnothing=0,\qquad
\ell_{wb}=F_b(\ell_w),\qquad
F_b(x)=G\bigl(x+(-1)^b\lambda\bigr),\qquad
G(x)=\log\frac{r+(1-r)e^x}{(1-r)+re^x}.
$$
区间 $I$ 对两个更新均正向不变，且
$$
\overline{\{\ell_w:w\in\{0,1\}^{*}\}}=I
\quad\Longleftrightarrow\quad r\le p(1-p).
$$
在此重叠区域，包括等号边界，每个固定深度 $n\ge0$ 的可达集合都是 $I$ 的 $a\eta^n$-网：
$$
\forall x\in I\ \exists w\in\{0,1\}^{n}:
\quad |x-\ell_w|\le a\eta^n.
$$
有限历史的并集是可数稠密集，不等于整个非退化区间；其下一报告预测值的闭包恰为 $J$，长度为 $L$。因此对重叠区域中每组固定参数和每个 $\varepsilon>0$，
$$
\left\lceil\frac{L}{2\varepsilon}\right\rceil
\le N_{\min}(\varepsilon)
\le 2\left\lceil\frac{da}{8(1-\eta)\varepsilon}\right\rceil+1
\le\frac{da}{4(1-\eta)\varepsilon}+3.
$$
下界适用于上述全部有限确定性观察者；上界由一个因果网格观察者实现，并且单独对整个 $0<p,r<1/2$ 参数域成立。于是固定重叠参数下
$$
N_{\min}(\varepsilon)=\Theta_{p,r}(\varepsilon^{-1})
\qquad(\varepsilon\downarrow0).
$$
这是上下界的同阶结论，不给出锐常数或精确最小值。

**证明。** 本节与命题153.1具有相同的 $c_{bi}$、列向量转移约定、先验和操作次序，故直接使用其复 Kraus 仪器、标量 Born 递推及全局对数赔率收缩结论。特别地，每一步 $pZ_w\le Z_{wb}\le(1-p)Z_w$，从 $Z_\varnothing=1$ 得所有词的正标量概率；隐藏位 $1$ 的质量归一化后给 $q_w$，空词仍给 $q_\varnothing=1/2$。其导数公式在本参数约定下为
$$
G'(x)=\frac{\eta}{1+r(1-r)(e^x+e^{-x}-2)},
\qquad 0<G'(x)\le\eta<1.
$$
分母至少为一，因为 $e^x+e^{-x}-2=(e^{x/2}-e^{-x/2})^2\ge0$。于是每个 $F_b$ 严格递增且为 $\eta$-Lipschitz，任意同词复合的常数为 $\eta^{|w|}$。又 $G$ 为奇函数，故
$$
F_1(x)=-F_0(-x),\qquad F_0(x)>F_1(x),\qquad
0<h'(x)=\frac{de^x}{(1+e^x)^2}\le\frac d4.
$$
这里最后一个不等式使用 $(1+e^x)^2\ge4e^x$。

先确定不变区间。报告零时的概率更新为
$$
H_0(q)=r+\eta\frac{(1-p)q}{p+dq},\qquad 0\le q\le1.
$$
分母 $p+dq>0$，且
$$
q-H_0(q)=\frac{H(q)}{p+dq},\qquad
H(q)=dq^2+(r-d)q-rp.
$$
该二次式的判别式、根的乘积及两个端点读数分别为
$$
(r-d)^2+4drp=r^2+\eta d^2,\qquad
-\frac{rp}{d}<0,\qquad
H(1/2)=-\frac{\eta d}{4}<0,\qquad H(1)=r(1-p)>0.
$$
所以恰有一个正根，且它就是所列的 $q_+\in(1/2,1)$。由 $H_0(q_+)=q_+$ 及对数赔率坐标转换，$F_0(a)=a$；对称性给 $F_1(-a)=-a$，收缩性保证各自不动点的唯一性。严格递增性及 $F_0>F_1$ 因而给出两个完整像区间
$$
F_0(I)=[G(\lambda-a),a],\qquad
F_1(I)=[-a,G(a-\lambda)],\qquad F_b(I)\subseteq I.
$$
由于 $0\in I$，每个有限历史的 $\ell_w$ 都在 $I$ 内。

两个像覆盖 $I$ 当且仅当其内侧端点相接或重叠。利用 $G(a-\lambda)=-G(\lambda-a)$ 及 $G$ 严格递增、$G(0)=0$，此条件等价于
$$
G(\lambda-a)\le0\quad\Longleftrightarrow\quad a\ge\lambda.
$$
当 $y>x$ 时，
$$
[F_0(y)-y]-[F_0(x)-x]\le-(1-\eta)(y-x)<0.
$$
因此 $F_0(x)-x$ 严格递减，零点为 $a$，从而 $a\ge\lambda$ 等价于 $F_0(\lambda)\ge\lambda$。再经严格递增的 $\sigma$，并用 $\sigma(\lambda)=1-p$，它等价于 $H_0(1-p)\ge1-p$。记 $D=(1-p)^2+p^2>0$，直接通分得
$$
H_0(1-p)-(1-p)
=r+\eta\frac{(1-p)^2}{D}-(1-p)
=\frac{d[p(1-p)-r]}{D}.
$$
因 $d,D>0$，覆盖条件恰为 $r\le p(1-p)$，等号确实属于覆盖区域。

在覆盖条件下，任取 $n\ge1$ 和 $x\in I$，置 $x_n=x$。对 $k=n,n-1,\ldots,1$ 依次利用 $F_0(I)\cup F_1(I)=I$，选择 $b_k\in\{0,1\}$ 与 $x_{k-1}\in I$ 使 $x_k=F_{b_k}(x_{k-1})$。于是
$$
x=F_{b_n}\circ\cdots\circ F_{b_1}(x_0).
$$
这里倒向选择的顺序为 $b_n,\ldots,b_1$，对应的时间顺序词是 $w=b_1\cdots b_n$。将同一复合的初值 $x_0$ 换成实际先验坐标 $0$，由命题153.1的共同词收缩得
$$
|x-\ell_w|\le\eta^n|x_0|\le a\eta^n.
$$
$n=0$ 时可达集合为 $\{0\}$，而 $|x|\le a=a\eta^0$，所以网结论也包含深度零。由于 $\eta^n\to0$，可达有限历史在 $I$ 中稠密；历史集合可数，而 $a>0$ 的区间不可数，故只可说闭包等于 $I$。连续严格递增的 $h$ 将 $I$ 映到 $J$，从而预测值闭包为 $J$，且其长度
$$
h(a)-h(-a)=d(2q_+-1)=\sqrt{r^2+\eta d^2}-r>0.
$$

反之，若 $r>p(1-p)$，则 $a<\lambda$。置 $g=G(\lambda-a)>0$；由 $F_0(-a)<F_0(a)=a$ 还知 $g<a$。每个非空词的最后一次更新把其值放进
$$
F_0(I)\cup F_1(I)=[-a,-g]\cup[g,a].
$$
空词只增加点 $0$。这两个闭区间与 $\{0\}$ 的有限并仍闭，且遗漏非空开区间 $(0,g)$，所以全部有限历史的闭包也遗漏 $(0,g)$。这就证明了稠密性的反向必要条件。

现在在重叠区域取任意满足 $\mathcal E\le\varepsilon$ 的 $N$ 状态观察者。有限闭集并
$$
U=\bigcup_{s\in S}[t(s)-\varepsilon,t(s)+\varepsilon]
$$
包含每一个可达预测值 $f(q_w)$。由闭性，它也包含这些值的闭包 $J$。有限区间并的长度不超过各区间长度之和，故
$$
L=|J|\le |U|\le\sum_{s\in S}2\varepsilon=2N\varepsilon.
$$
因此 $N\ge\lceil L/(2\varepsilon)\rceil$。这个论证只用固定有限读出及对所有词的误差条件，不限制更新采用网格或后缀，也不要求误差上确界由某个词达到。对固定参数，$L>0$ 给出非零的下界常数。

为构造上界，现在只假设 $0<p,r<1/2$，不要求像区间覆盖。对任意整数 $M\ge1$ 取状态标签及其固定坐标
$$
S_M=\{-M,-M+1,\ldots,M\},\qquad
x_j=\frac{ja}{M},\qquad s_0=0.
$$
令 $R_M:I\to\{x_j:j\in S_M\}$ 为最近网格点映射，等距时固定选择较小标签。对每个输入报告，定义固定表
$$
T_b(j)=k\quad\Longleftrightarrow\quad x_k=R_M(F_b(x_j)),
\qquad t(j)=h(x_j).
$$
坐标两两不同，故标签 $k$ 唯一；不变性保证 $F_b(x_j)\in I$，且对所有 $y\in I$ 都有
$$
|R_M(y)-y|\le\frac a{2M}.
$$
这包含两个端点及每个网格中点；若统一改用较大标签处理等距，误差界相同。状态更新只读取当前整数标签和当前报告，所以是同一个有限因果观察者，$|S_M|=2M+1$。

任取有限时域 $H\ge0$ 和时间顺序词 $b_1\cdots b_H$，记 $j_n=T_{b_n}\circ\cdots\circ T_{b_1}(0)$、$\widehat\ell_n=x_{j_n}$，其中 $j_0=0$。真实轨迹 $\ell_{b_1\cdots b_n}$ 和网格轨迹 $\widehat\ell_n$ 均在 $I$，初始误差为零。在[《情境时空算术·机器学习》定义21.1、定理21.2](../CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)中，取摘要映射为 $\operatorname{Id}_I$，精确更新为 $F_b$，近似更新为 $R_M\circ F_b$，并代入
$$
e_0=0,\qquad\delta_{\rm close}=0,\qquad
\delta_{\rm eval}=\frac a{2M},\qquad
L_{\rm ML}=\eta,\qquad L_o=\frac d4,\qquad\varepsilon_o=0.
$$
此处 $L_{\rm ML}$ 是所引定理的共同 Lipschitz 常数，与本命题的区间长度 $L$ 区分。所有缺陷界在 $I$ 上成立，两条轨迹均不退出此域；故直接应用该有限时域定理，对每个 $0\le n\le H$ 得
$$
e_n:=|\ell_{b_1\cdots b_n}-\widehat\ell_n|,
\qquad e_{n+1}\le\eta e_n+\frac a{2M}\quad(0\le n<H),
$$
$$
e_n\le\frac a{2M}\sum_{k=0}^{n-1}\eta^k
=\frac{a(1-\eta^n)}{2M(1-\eta)},\qquad
|h(\ell_{b_1\cdots b_n})-t(j_n)|
\le\frac{da(1-\eta^n)}{8M(1-\eta)}
\le\frac{da}{8M(1-\eta)}.
$$
$n=0$ 的和为空，两个初始读出同为 $1/2$；无需填充历史或额外记录长度。状态集和两张更新表完全不依赖 $H$，故对任意有限时域应用同一个定理，就得到同一个观察者对全部有限词的误差界，而非随词长更换观察者。取
$$
M=\left\lceil\frac{da}{8(1-\eta)\varepsilon}\right\rceil\ge1
$$
即得所陈述的上界。该构造也证明 $N_{\min}(\varepsilon)$ 的定义域内总存在可行观察者，由正整数的良序性取到最小基数。在重叠区域与前面的普适下界合并，再用 $\lceil u\rceil\le u+1$，得到完整不等式链及固定参数下的 $\Theta_{p,r}(\varepsilon^{-1})$。

上述成本约定下，运行时只有整数标签 $j$ 演化；实坐标和读出是定义有限固定表的常数，不是另一个运行中的实数寄存器。有限个精确实数表项的存在不等于对任意实参数的有效综合，也不衡量求表时的计算量、轨道枚举成本或表项描述长度。若另将读出舍入并截到 $[0,1]$，使 $|\bar t(j)-t(j)|\le\delta_{\rm out}$，同一更新表仍给
$$
|\bar t(T_w(0))-f(q_w)|
\le\frac{da}{8M(1-\eta)}+\delta_{\rm out}.
$$
读出误差只加一次，因为它不反馈到更新；内部网格舍入则按已用的几何和累积。若要求有理读出，可把总容差各分一半，取 $\delta_{\rm out}\le\varepsilon/2$ 及
$$
M=\left\lceil\frac{da}{4(1-\eta)\varepsilon}\right\rceil.
$$
有理数稠密性及有限状态数保证可同时选择这些有理读出，截断不增大误差。这时仍为 $O_{p,r}(\varepsilon^{-1})$ 状态，但显示的状态上界变为 $2\lceil da/[4(1-\eta)\varepsilon]\rceil+1$；前面较小的常数属于允许精确读出的观察者类。

在闭合边界 $p=1/3,r=2/9=p(1-p)$，直接代入给
$$
q_+=\frac23,\qquad a=\lambda=\log2,\qquad
\eta=\frac59,\qquad J=\left[\frac49,\frac59\right],\qquad L=\frac19.
$$
两个像恰在零点相接，结论为
$$
\frac1{18\varepsilon}\le N_{\min}(\varepsilon)
\le2\left\lceil\frac{3\log2}{32\varepsilon}\right\rceil+1
\le\frac{3\log2}{16\varepsilon}+3.
$$
同一概率递推按时间顺序给 $q_0=16/27$、$q_{01}=26/57$、$q_{10}=31/57$，两个逆序词的后验不同。作为重叠条件之外的对照，$p=1/3,r=1/4$ 时
$$
q_+=\frac{1+\sqrt{17}}8<\frac23,
\qquad a<\lambda,\qquad G(\lambda-a)>0,
$$
其中根的比较可由 $17<(13/3)^2$ 得到，故前述开缺口确实存在。这个缺口不确定其余闭包的分形维数，也不给出重叠区域以外的最优成本指数。命题153.1的后缀构造提供另一上界，不能替代这里对任意有限观察者的下界；本命题不证明后缀最优性。全部误差只指固定协议和先验下、每个有限历史后的下一报告误差，不涉及整个滚动生成律的误差、控制或参考近似、量子记忆最小值、平稳平均损失，也不声称参数一致常数。证毕。

本命题的物理仪器、条件化与共同词收缩直接取自本卷命题153.1；网格误差传播直接应用[《情境时空算术·机器学习》定义21.1及定理21.2](../CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)。有限收缩映射族的不变紧集与 Hausdorff 收缩为既有方法，参见 J. E. Hutchinson，*Fractals and Self Similarity*，*Indiana University Mathematics Journal* 30 (1981), 713–747，[DOI:10.1512/iumj.1981.30.30055](https://doi.org/10.1512/iumj.1981.30.30055)，[作者重排版](https://maths-people.anu.edu.au/~john/Assets/Research%20Papers/fractals_self-similarity.pdf)，第3.1节(3)及第3.2节(1)，该重排版第10–12页。这里的倒向选词证明已直接给出每个深度的网半径，状态下界只用有限闭区间覆盖的长度次可加性。

<a id="entry-658"></a>

## 追加锚（本行以下为增补区）

<a id="section-155"></a>

## 155. 全有限历史后验闭包的覆盖数与因果观察者成本

**命题 155.1（正混合二元模型的全历史状态成本与内部覆盖数同阶）。** 固定 $0<p<1/2$、$0<r<1/2$，沿用命题153.1与154.1的二元仪器、先验 $I_2/2$ 及时间顺序约定。具体地，$c_{00}=c_{11}=p$、$c_{01}=c_{10}=1-p$，$P_{ii}=1-r$、$P_{ji}=r$（$j\ne i$）；旧隐藏位 $i$ 先发射报告 $b$，再翻转到新隐藏位 $j$，各项
$$
K_{bji}=\sqrt{c_{bi}P_{ji}}\,|j\rangle\langle i|,
\qquad
\phi_b(X)=\sum_{i,j=0}^1K_{bji}XK_{bji}^{\dagger}
$$
分别作共轭作用后相加。对时间顺序词 $w=b_1\cdots b_n$，令
$$
\phi_w=\phi_{b_n}\circ\cdots\circ\phi_{b_1},\qquad
v_\varnothing=\binom{1/2}{1/2},\qquad
v_{wb}=P\operatorname{diag}(c_{b0},c_{b1})v_w,
$$
$$
Z_w=\mathbf1^{\mathsf T}v_w,\qquad
q_w=\frac{(v_w)_1}{Z_w},\qquad
\ell_w=\log\frac{q_w}{1-q_w}.
$$
空词作用为恒等，$Z_\varnothing=1$、$\ell_\varnothing=0$。命题153.1已经给出 $\phi_w(I_2/2)=\operatorname{diag}(v_w)$、$Z_w\ge p^{|w|}>0$ 及 $0<q_w<1$；以下对全部有限词条件化。

取命题154.1中的常数及不变区间
$$
d=1-2p,\qquad \eta=1-2r,\qquad
\lambda=\log\frac{1-p}{p},\qquad
q_+=\frac{d-r+\sqrt{r^2+\eta d^2}}{2d},
$$
$$
a=\log\frac{q_+}{1-q_+}>0,\qquad I=[-a,a],\qquad
G(x)=\log\frac{r+(1-r)e^x}{(1-r)+re^x},\qquad
F_b(x)=G\bigl(x+(-1)^b\lambda\bigr).
$$
直接使用前两命题的 $\ell_{wb}=F_b(\ell_w)$、$F_b(I)\subseteq I$ 及共同 Lipschitz 常数 $\eta<1$。下一零报告的概率为
$$
h(x)=p+\frac{d}{1+e^{-x}},\qquad
\Pr(0\mid w)=h(\ell_w).
$$
定义全有限历史后验的对数赔率集合及其闭包
$$
\mathcal O=\{\ell_w:w\in\{0,1\}^{*}\},\qquad
C=\overline{\mathcal O}\subseteq\mathbb R.
$$
此处包括空词；$C$ 不以平稳分布的支撑或仅以渐近吸引集代替。对 $\delta>0$，采用中心属于 $C$、球为闭球的内部覆盖数
$$
N_C(\delta)=\min\left\{|Q|:
\varnothing\ne Q\subseteq C\text{ 为有限集},\quad
C\subseteq\bigcup_{q\in Q}[q-\delta,q+\delta]\right\}.
$$

观察者仍取命题154.1的类别：有限非空状态集 $S$、固定初态 $s_0\in S$、固定确定性更新 $T_0,T_1:S\to S$ 和固定读出 $t:S\to[0,1]$。令 $T_w=T_{b_n}\circ\cdots\circ T_{b_1}$、$T_\varnothing=\operatorname{Id}$，并取
$$
N_{\min}(\varepsilon)=\min\left\{|S|:
\sup_{w\in\{0,1\}^{*}}
|t(T_w(s_0))-h(\ell_w)|\le\varepsilon\right\}
\qquad(\varepsilon>0).
$$
所有可读的演化记忆均计入 $S$，没有另行可读的时钟、历史档案、随机种子或演化实数寄存器。允许在固定表及读出中使用精确实常数；所计成本只是 $|S|$。观察者可依赖 $p,r,\varepsilon$，但同一初态、更新表和读出必须适用于全部有限词长。

则 $C$ 为包含 $0$ 的非空紧集，$F_b(C)\subseteq C$，上述两个最小值均存在。置
$$
A=\frac d4,\qquad
\mu=\frac{d}{4\cosh^2(a/2)}=d q_+(1-q_+)>0.
$$
对每个 $\varepsilon>0$ 有
$$
N_C\!\left(\frac{2\varepsilon}{\mu}\right)
\le N_{\min}(\varepsilon)
\le N_C\!\left(\frac{(1-\eta)\varepsilon}{A}\right).
$$
进一步定义
$$
B(c)=
\begin{cases}
\lceil2/c\rceil,&0<c<1,\\
1,&c\ge1.
\end{cases}
$$
则同尺度比较为
$$
\frac{N_C(\varepsilon)}{B(\mu/2)}
\le N_{\min}(\varepsilon)
\le B\!\left(\frac{1-\eta}{A}\right)N_C(\varepsilon),
\qquad
N_{\min}(\varepsilon)=\Theta_{p,r}\bigl(N_C(\varepsilon)\bigr)
\quad(\varepsilon\downarrow0).
$$
这些常数只取充分界，不作最优性断言。以
$$
\underline D_C=\liminf_{\delta\downarrow0}
\frac{\log N_C(\delta)}{\log(1/\delta)},\qquad
\overline D_C=\limsup_{\delta\downarrow0}
\frac{\log N_C(\delta)}{\log(1/\delta)}
$$
定义下、上盒维数，则
$$
\liminf_{\varepsilon\downarrow0}
\frac{\log N_{\min}(\varepsilon)}{\log(1/\varepsilon)}
=\underline D_C,\qquad
\limsup_{\varepsilon\downarrow0}
\frac{\log N_{\min}(\varepsilon)}{\log(1/\varepsilon)}
=\overline D_C.
$$
不要求这两个维数相同。若共同盒维数 $D$ 存在，则仅由该条件得到
$$
N_{\min}(\varepsilon)=\varepsilon^{-D+o(1)};
$$
该条件本身不把 $o(1)$ 提升为 $N_{\min}(\varepsilon)=\Theta(\varepsilon^{-D})$。

**证明。** 由命题154.1的区间不变性及 $\ell_\varnothing=0$，$\mathcal O\subseteq I$。因此 $C$ 是紧区间 $I$ 的闭子集，非空且含 $0$。追加报告作用最后，故 $F_b(\mathcal O)\subseteq\mathcal O$。对任意 $x\in C$ 取 $x_n\in\mathcal O$ 趋于 $x$，连续性给 $F_b(x_n)\to F_b(x)$；闭性遂给 $F_b(x)\in C$。对每个 $\delta>0$，以所有 $x\in C$ 为中心的开 $\delta$-球覆盖 $C$，紧性给有限子覆盖，换成同心闭球仍覆盖。故内部有限网存在，其可能基数构成非空正整数集；良序性给最小基数及实现它的网，并不要求这些网包含 $0$。

下一报告读出在整个 $I$ 上给出双向距离控制。求导得
$$
h'(x)=\frac{de^x}{(1+e^x)^2}
=\frac{d}{4\cosh^2(x/2)}.
$$
由 $|x|\le a$ 得 $\mu\le h'(x)\le A$。又 $e^a=q_+/(1-q_+)$，所以
$$
\frac{1}{4\cosh^2(a/2)}
=\frac{e^a}{(1+e^a)^2}=q_+(1-q_+).
$$
对 $x\le y$ 在 $[x,y]\subseteq I$ 上积分，并交换两点处理 $x>y$，得到
$$
\mu|x-y|\le |h(x)-h(y)|\le A|x-y|
\qquad(x,y\in I).
$$

先证下界。取任意误差至多 $\varepsilon$ 的有限观察者，记其可达状态集为
$$
S_{\rm reach}=\{T_w(s_0):w\in\{0,1\}^{*}\}.
$$
对每个 $s\in S_{\rm reach}$ 选择一个达到它的有限词 $w_s$，置 $x_s=\ell_{w_s}\in\mathcal O\subseteq C$。任意有限词 $w$ 若达到 $s$，它与 $w_s$ 使用同一读出 $t(s)$，所以
$$
|h(\ell_w)-h(x_s)|
\le |h(\ell_w)-t(s)|+|t(s)-h(x_s)|
\le2\varepsilon,
\qquad
|\ell_w-x_s|\le\frac{2\varepsilon}{\mu}.
$$
这正是[《观察者闭合谱》第15节](../OBSERVER_CLOSURE_SPECTRUM.md)及[《情境时空算术·机器学习》命题39.3](../CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)所用的同纤维半直径障碍，在此应用于下一报告读出。有限闭区间并
$$
U=\bigcup_{s\in S_{\rm reach}}
\left[x_s-\frac{2\varepsilon}{\mu},x_s+\frac{2\varepsilon}{\mu}\right]
$$
包含 $\mathcal O$，故也包含 $C=\overline{\mathcal O}$。去掉重复中心后得到内部闭球网，中心数不超过 $|S_{\rm reach}|\le|S|$。于是 $N_C(2\varepsilon/\mu)\le|S|$，对任意可行观察者成立。所选 $x_s$ 只是覆盖的证明见证，不声称任意观察者的状态中实际存有或能解码出这个后验。

再证因果上界。令
$$
\delta=\frac{(1-\eta)\varepsilon}{A}>0,
\qquad Q=\{q_1,\ldots,q_N\}\subseteq C,
\qquad N=N_C(\delta),
$$
其中 $Q$ 是最小内部 $\delta$-网，枚举固定。对 $x\in C$，令 $R(x)$ 为使 $|x-q_j|$ 最小的首个 $q_j$。有限非空性保证选择存在且唯一，闭球覆盖保证
$$
R:C\to Q,\qquad |R(x)-x|\le\delta\quad(x\in C).
$$
取状态集 $S=Q$，初态、更新与读出为
$$
s_0=R(0),\qquad T_b(q)=R(F_b(q)),\qquad t(q)=h(q).
$$
因 $F_b(C)\subseteq C$，所有表项均有定义。$q_j$ 可等价地用有限标签 $j$ 表示；演化的只有此标签。这里没有给 $0$ 另加一个启动状态。

任取有限词 $b_1\cdots b_H$，记其长度 $n$ 前缀为 $w_n$，并令
$$
\widehat\ell_0=R(0),\qquad
\widehat\ell_{n+1}=R(F_{b_{n+1}}(\widehat\ell_n)),\qquad
e_n=|\ell_{w_n}-\widehat\ell_n|.
$$
两条轨迹始终在 $C\subseteq I$，且 $e_0=|R(0)|\le\delta$，一般不能把它设为零。在[《情境时空算术·机器学习》定义21.1及定理21.2](../CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)中，以 $C$ 为所声明域、摘要为 $\operatorname{Id}_C$、精确更新为 $F_b$、近似更新为 $R\circ F_b$，代入
$$
\delta_{\rm close}=0,\qquad
\delta_{\rm eval}=\delta,\qquad
L_{\rm ML}=\eta,\qquad L_o=A,\qquad\varepsilon_o=0.
$$
所需的共同 Lipschitz 性只属于精确映射 $F_b$；求值缺陷界在整个 $C$ 成立，输出为 $h$。直接应用该定理的含初始误差公式，得
$$
e_{n+1}\le\eta e_n+\delta\quad(0\le n<H),\qquad
e_n\le\eta^n\delta+\delta\frac{1-\eta^n}{1-\eta}
\le\frac{\delta}{1-\eta}\quad(0\le n\le H).
$$
$n=0$ 时几何和为空，初始误差项仍保留。因而包括空词在内，
$$
|t(T_{w_n}(s_0))-h(\ell_{w_n})|
=|h(\widehat\ell_n)-h(\ell_{w_n})|
\le A e_n\le\varepsilon.
$$
同一组 $Q,R,s_0,T_0,T_1,t$ 不依赖 $H$；任取有限词应用此界，即得对全部有限词的一致结论。舍入更新不必收缩，亦未断言 $\widehat\ell_n=R(\ell_{w_n})$。这给出一个至多 $N_C(\delta)$ 状态的可行观察者，也使可行基数集非空；再用正整数良序性得到 $N_{\min}(\varepsilon)$ 的存在及上界。[ML 命题39.4](../CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)区分静态近似读出与动态实现；这里的因果性由明确的固定更新表和共同词误差递推承担。

同尺度比较只需实直线上的一个覆盖事实。对任意非空紧集 $C\subseteq\mathbb R$、$\delta>0$ 和 $0<c<1$，取实现 $N_C(\delta)$ 的内部网。把每个覆盖区间 $[q-\delta,q+\delta]$ 分成
$$
m=\lceil2/c\rceil
$$
个闭子区间，各长 $2\delta/m\le c\delta$。在每个与 $C$ 相交的子区间中选择一个实际属于 $C$ 的点；同一交集中的任一点与所选点相距至多 $c\delta$。由这些点作中心的闭 $c\delta$-球便覆盖 $C$；公共端点也在覆盖内，重复中心可以删除。因此
$$
N_C(c\delta)\le\lceil2/c\rceil N_C(\delta)
\qquad(0<c<1).
$$
$c\ge1$ 时扩大半径不增加最小基数，故统一有 $N_C(c\delta)\le B(c)N_C(\delta)$。将它先用于半径 $2\varepsilon/\mu$、比例 $\mu/2$，再用于半径 $\varepsilon$、比例 $(1-\eta)/A$，得到
$$
N_C(\varepsilon)
\le B(\mu/2)N_C(2\varepsilon/\mu)
\le B(\mu/2)N_{\min}(\varepsilon),
$$
$$
N_{\min}(\varepsilon)
\le N_C((1-\eta)\varepsilon/A)
\le B((1-\eta)/A)N_C(\varepsilon).
$$
这里用的是实直线区间的有限细分性质，不把此常数尺度比较推广到任意非倍增度量空间。

固定 $p,r$ 后两侧常数与精度无关，故
$$
\log N_{\min}(\varepsilon)
=\log N_C(\varepsilon)+O_{p,r}(1).
$$
除以趋于无穷的 $\log(1/\varepsilon)$，分别取下极限、上极限即得两种指数相等。若二者均为 $D$，此式等价于 $\log N_{\min}(\varepsilon)=(D+o(1))\log(1/\varepsilon)$，指数化给所述 $\varepsilon^{-D+o(1)}$；其中剩余项未必有界，故不能仅凭维数存在就得到纯幂的双边常数界。此处没有计算缺口区域中未经确定的维数。若另由命题154.1知 $C=I$，则内部覆盖数为 $N_I(\delta)=\lceil a/\delta\rceil$：长度次可加性给下界，把 $I$ 等分为该数量的子区间并取各中点给上界。因此恢复该命题在 $r\le p(1-p)$ 下的 $\Theta_{p,r}(\varepsilon^{-1})$ 结论，重叠阈值直接沿用该命题。

空词与覆盖约定在有缺口时仍不可省略。命题154.1已经证明，若 $g=G(\lambda-a)>0$，则每个非空历史的对数赔率都在 $[-a,-g]\cup[g,a]$，故
$$
0\in C\subseteq\{0\}\cup[-a,-g]\cup[g,a],\qquad
C\cap(-g,g)=\{0\}.
$$
于是 $0$ 在 $C$ 中孤立；任何包含于 $I$ 且满足 $K=F_0(K)\cup F_1(K)$ 的吸引集都位于两个像区间中，不能包含该初始点。另以 $\{0,2\}$ 为例，半径 $1$ 的内部闭球须有两个中心，因为每个许可中心距另一点为 $2$；外部中心 $1$ 的一个球虽能覆盖却不许可。半径 $2$ 时以 $0$ 为中心的闭球已包含两点，故一个中心足够。这也说明内部中心和闭端点约定贯穿上述三处覆盖论证。

有限固定实数表的存在不蕴含任意实参数下的可计算构造或位复杂度。若另把读出近似为 $\bar t$ 且 $|\bar t(q)-h(q)|\le\varepsilon_{\rm out}$，同一递推仅给总误差至多 $A\delta/(1-\eta)+\varepsilon_{\rm out}$，须另分配读出误差预算。这里的上下界只属于固定协议、固定先验下的有限确定性下一报告观察者，不给量子物理记忆下界、熵成本、平稳平均误差、整个未来报告律的近似、自适应实验保证或最小精确后验商的刻画。证毕。

本命题的仪器与后验递推复用本卷命题153.1，不变区间及有缺口时的像区间复用命题154.1；误差传播使用 ML 定义21.1、定理21.2，半纤维下界及静态近似与因果实现的区分使用上述观察者闭合谱第15节、ML 命题39.3–39.4。稳定动力的有限符号近似方法参见 G. Pola、A. Girard、P. Tabuada，*Approximately bisimilar symbolic models for nonlinear control systems*，[arXiv:0706.0246](https://arxiv.org/abs/0706.0246)，[DOI:10.1016/j.automatica.2008.02.021](https://doi.org/10.1016/j.automatica.2008.02.021)；A. Girard、G. Pola、P. Tabuada，*Approximately bisimilar symbolic models for incrementally stable switched systems*，[arXiv:0807.5022](https://arxiv.org/abs/0807.5022)。这些文献提供既有的稳定性与量化方法背景，此处的全有限历史内部覆盖数比较由以上具体证明给出。S. E. Marzen、J. P. Crutchfield，*Nearly maximally predictive features and their dimensions*，[DOI:10.1103/PhysRevE.95.051301](https://doi.org/10.1103/PhysRevE.95.051301)，以及 A. M. Jurgens、J. P. Crutchfield，*Divergent predictive states: The statistical complexity dimension of stationary, ergodic hidden Markov processes*，[DOI:10.1063/5.0050460](https://doi.org/10.1063/5.0050460)，分别讨论预测特征的失真与维数、平稳遍历隐藏 Markov 过程预测特征的信息维数；其平均或平稳支撑约定不替代这里包括启动历史的逐词一致误差与内部覆盖约定。

<a id="entry-660"></a>

## 追加锚（本行以下为增补区）

<a id="section-156"></a>

## 156. 混合趋零时低于静态地板的有限观察者成本发散

**命题 156.1（正混合的有限可近似性与趋零混合的必要状态发散）。** 固定 $0<p<1/2$，置
$$
d=1-2p>0,\qquad \Delta=\frac d2=\frac12-p,
\qquad \kappa=\frac{1-p}{p}>1.
$$
在整个 $0\le r<1/2$ 参数族中，隐藏字母表均为 $\{0,1\}$，旧隐藏位 $i$ 先发射报告 $b$，再翻转到新隐藏位 $j$，其中
$$
c_{00}=c_{11}=p,\qquad c_{01}=c_{10}=1-p,
\qquad P_{ji}(r)=\begin{cases}1-r,&j=i,\\r,&j\ne i.\end{cases}
$$
协议时间齐次且无控制，初态固定为 $I_2/2$。具体地，令 $E_i=|i\rangle\langle i|$、$I_2=E_0+E_1$，在 $M_2(\mathbb C)$ 上分别取 Kraus 项
$$
K_{bji}^{(r)}=\sqrt{c_{bi}P_{ji}(r)}\,|j\rangle\langle i|,
\qquad
\phi_b^{(r)}(X)=\sum_{i,j=0}^1K_{bji}^{(r)}X(K_{bji}^{(r)})^\dagger
=\sum_{i,j=0}^1c_{bi}P_{ji}(r)X_{ii}E_j.
$$
各 Kraus 项分别作共轭作用后求和。$r=0$ 时非零项恰为命题152.1的两个对角秩一项，隐藏位保持不变；$0<r<1/2$ 时恰为命题153.1的四项仪器。两种情形中的每个非空报告分支均为测量制备操作；空操作仍为恒等。因而整个比较都在同一逐支测量制备族内，生成器的物理潜在空间始终只有两个经典状态。

令 $\mathcal W=\{0,1\}^{*}$，包括空词 $\varnothing$；词 $w=b_1\cdots b_h$ 按时间顺序书写，
$$
\phi_w^{(r)}=\phi_{b_h}^{(r)}\circ\cdots\circ\phi_{b_1}^{(r)},
\qquad \phi_\varnothing^{(r)}=\operatorname{Id}.
$$
以下列向量、词质量和后验均依赖 $r$：
$$
v_\varnothing=\binom{1/2}{1/2},\qquad
v_{wb}=P(r)\operatorname{diag}(c_{b0},c_{b1})v_w,
\qquad Z_w=\mathbf1^{\mathsf T}v_w,\qquad
q_w=\frac{(v_w)_1}{Z_w}.
$$
它们满足 $\phi_w^{(r)}(I_2/2)=\operatorname{diag}(v_w)$。下一报告为零的条件概率记为
$$
f_r(w)=\frac{Z_{w0}}{Z_w}=p+dq_w.
$$
空词有 $Z_\varnothing=1$、$q_\varnothing=1/2$、$f_r(\varnothing)=1/2$。

有限确定性观察者 $\mathcal A=(S,s_0,T_0,T_1,t)$ 的状态集 $S$ 非空且有限，初态 $s_0\in S$ 固定，两张报告标记更新表 $T_0,T_1:S\to S$ 和读出 $t:S\to[0,1]$ 固定。令
$$
s_{\mathcal A}(\varnothing)=s_0,\qquad
s_{\mathcal A}(wb)=T_b(s_{\mathcal A}(w)),\qquad
\mathcal E_r(\mathcal A)=\sup_{w\in\mathcal W}
\bigl|t(s_{\mathcal A}(w))-f_r(w)\bigr|.
$$
全部可读的演化记忆均计入 $S$；没有另行可读的历史档案、时钟、隐藏位或演化实数寄存器。固定表可含任意精确实数常量，并可依赖 $p,r,\varepsilon$，但运行中不改变；同一观察者用于全部有限词长，包括空词和任意小概率的历史。对 $\varepsilon>0$ 定义扩展值状态成本
$$
N_{\min}^{(r)}(\varepsilon)=
\begin{cases}
\min\{|S|:\mathcal E_r(\mathcal A)\le\varepsilon\},&\text{存在这样的有限观察者},\\
\infty,&\text{不存在这样的有限观察者}.
\end{cases}
$$
所计的是 $|S|$，不计固定表的描述长度。则：

(a) 对每个固定 $0<r<1/2$ 和每个 $\varepsilon>0$，有 $N_{\min}^{(r)}(\varepsilon)<\infty$。

(b) 对每个固定 $0<\varepsilon<\Delta$ 和每个整数 $N\ge1$，存在 $r_N=r_N(p,\varepsilon)>0$，使
$$
\forall r\in\bigl(0,\min\{r_N,1/2\}\bigr),
\qquad N_{\min}^{(r)}(\varepsilon)>N.
$$
即在固定 $p,\varepsilon$ 下，
$$
\lim_{r\downarrow0}N_{\min}^{(r)}(\varepsilon)=\infty.
$$
每个 $r$ 的观察者允许单独重新选择；结论仍排除这个邻域内的每一张至多 $N$ 状态的表及每一个实数读出。

(c) 对每个 $\varepsilon\ge\Delta$ 和全部 $0\le r<1/2$，有 $N_{\min}^{(r)}(\varepsilon)=1$。在静态端点 $r=0$，有限观察者的最优全历史误差恰为
$$
\inf_{\mathcal A\text{ 为有限确定性观察者}}\mathcal E_0(\mathcal A)=\Delta,
$$
此值由单状态、恒定读出 $1/2$ 达到。因此 $0<\varepsilon<\Delta$ 时 $N_{\min}^{(0)}(\varepsilon)=\infty$。这里的地板是误差上确界，有限词上的误差无须达到它。

**证明。** 先核对同一参数族的条件化。$P(r)$ 的每列和为一且各项非负，$c_{bi}\ge p>0$。从 $v_\varnothing$ 的两个正分量出发，发射乘权保持正性，且 $P_{ii}(r)=1-r>0$，故每个 $v_w$ 的两个分量仍严格为正，包括 $r=0$。于是
$$
Z_{wb}=\sum_i c_{bi}(v_w)_i\ge pZ_w,
\qquad Z_\varnothing=1,
\qquad Z_w\ge p^{|w|}>0.
$$
特别地每个有限词都可条件化，$0<q_w<1$，并由 $b=0$ 的质量比得到 $f_r(w)=p+dq_w\in[p,1-p]$。这里的时间顺序是 $P(r)\operatorname{diag}(c_{b0},c_{b1})$，与命题152.1在 $r=0$、命题153.1在 $r>0$ 的约定逐项相同。各支还可写成
$$
\phi_b^{(r)}(X)=\sum_i c_{bi}X_{ii}\,\tau_i^{(r)},
\qquad \tau_i^{(r)}=\sum_jP_{ji}(r)E_j,
$$
其中 $\tau_i^{(r)}$ 为对角密度算子。这一测量制备形式及其非空复合正是前两命题的逐支结论；$r=0$ 时 $\tau_i^{(0)}=E_i$，空词则不经过任何测量。

命题153.1已经对每个固定正 $r$、每个正容差，给出一个对全部有限历史满足该容差的有限确定性后缀观察者。其初态、填充期和所有可读动态记忆都已计入有限状态集，读出是固定表，所近似的正是相同先验下的 $p+dq_w$。故该观察者属于这里的类别，直接得到(a)；非空可行基数集是正整数集，因而最小值存在。此应用只取正容差。

为证(b)，固定 $0<\varepsilon<\Delta$。对每一个固定的有限词 $w$，矩阵 $P(r)\operatorname{diag}(c_{b0},c_{b1})$ 的各项都是 $r$ 的多项式，有限个矩阵的乘积仍如此。因此 $v_w$ 的分量和 $Z_w$ 均为 $r$ 的多项式，而刚才的正分母下界给出
$$
\lim_{r\downarrow0}f_r(w)=f_0(w)
\qquad(w\text{ 固定}).
$$
空词的空乘积也满足此式。这只是逐个固定词的连续性，没有关于所有词长的一致收敛断言。

由命题152.1的实际静态公式，记 $k(w)=\#0(w)-\#1(w)$，便有
$$
f_0(w)=p+d\frac{\kappa^{k(w)}}{1+\kappa^{k(w)}}.
$$
因为 $2\varepsilon<d$ 且 $\kappa>1$，可以选定一个整数 $m\ge1$，使
$$
g_m:=d\frac{\kappa^m-1}{\kappa^m+1}>2\varepsilon.
$$
存在性来自 $\kappa^m\to\infty$，左侧趋于 $d$。此后 $m$ 只依赖 $p,\varepsilon$，不依赖观察者、$r$ 或 $N$。

任取整数 $N\ge1$，定义有限非空指标集
$$
\mathcal I_N=\{(n,\ell)\in\mathbb Z^2:n\ge0,\ \ell\ge1,\ n+\ell\le N\}.
$$
它有 $N(N+1)/2$ 个元素，且包含 $(0,1)$。对每个 $(n,\ell)\in\mathcal I_N$ 固定两条时间顺序词
$$
w^-(n,\ell)=0^n1^{n+m\ell},
\qquad
w^+(n,\ell)=0^{n+2m\ell}1^{n+m\ell}.
$$
在静态模型中，二者的计数分别为 $-m\ell$、$m\ell$，故
$$
f_0(w^+(n,\ell))-f_0(w^-(n,\ell))
=d\frac{\kappa^{m\ell}-1}{\kappa^{m\ell}+1}
\ge g_m>2\varepsilon.
$$
这里用 $\ell\ge1$ 及 $x\mapsto(x-1)/(x+1)$ 在 $x>0$ 上递增。

每一对词已经固定，故其预测差由上述逐词连续性在 $r=0$ 连续。其静态差严格大于 $2\varepsilon$，于是存在 $\rho_{n,\ell}>0$，使所有
$0<r<\min\{\rho_{n,\ell},1/2\}$ 都满足
$$
f_r(w^+(n,\ell))-f_r(w^-(n,\ell))>2\varepsilon.
$$
有限非空族的正数最小值仍正；取
$$
r_N=\min\left\{\frac12,\ \min_{(n,\ell)\in\mathcal I_N}\rho_{n,\ell}\right\}>0.
$$
于是 $0<r<\min\{r_N,1/2\}$ 时，整族词对同时具有严格大于 $2\varepsilon$ 的预测间隙。这个邻域只由 $p,\varepsilon,N$ 确定。

在此邻域内固定任意一个 $r$，再任取 $1\le|S|\le N$ 的观察者。将命题152.1所引用的既有有限轨道结论 `finite_orbit_and_readout_eventually_periodic` 应用于它的 $T_0$、初态 $s_0$ 和读出 $t$，得到 $n\ge0$、$\ell\ge1$，满足
$$
n+\ell\le|S|\le N,\qquad
T_0^{\,u+\ell}(s_0)=T_0^{\,u}(s_0)\quad(u\ge n).
$$
幂号表示函数迭代；这里使用的是状态相等，而不仅是读出相等。重复周期等式 $2m$ 次，得到
$$
s_{\mathcal A}(0^{n+2m\ell})=s_{\mathcal A}(0^n).
$$
由于 $(n,\ell)\in\mathcal I_N$，这就是前面预先固定的一对词的零前缀。给相同状态追加共同后缀 $1^{n+m\ell}$，实际的确定性更新 $T_1$ 给出
$$
s_{\mathcal A}(w^+(n,\ell))
=T_1^{\,n+m\ell}(s_{\mathcal A}(0^{n+2m\ell}))
=T_1^{\,n+m\ell}(s_{\mathcal A}(0^n))
=s_{\mathcal A}(w^-(n,\ell)).
$$
记该共同状态的读出为 $a$。三角不等式对任意实数 $a$ 都成立，因此
$$
\begin{aligned}
\mathcal E_r(\mathcal A)
&\ge\max\{|a-f_r(w^-(n,\ell))|,\ |a-f_r(w^+(n,\ell))|\}\\
&\ge\frac{f_r(w^+(n,\ell))-f_r(w^-(n,\ell))}{2}
>\varepsilon.
\end{aligned}
$$
由此排除该邻域内所有至多 $N$ 状态的观察者，包括依赖 $r$ 重新设计的表和任意精确实数读出。由于每个整数 $N\ge1$ 都有这样的整个正邻域，得到(b)的完整极限量词；它不只是某个趋零序列上的无界性。论证只对有限多个固定词取共同连续性邻域，没有交换全历史上确界与 $r\downarrow0$ 极限。

最后，对任意 $0\le r<1/2$，单状态观察者令两个更新均为恒等、读出恒为 $1/2$。由 $f_r(w)\in[p,1-p]$，对包括空词在内的每个历史均有
$$
|1/2-f_r(w)|\le\frac12-p=\Delta.
$$
故 $\varepsilon\ge\Delta$ 时一个状态可行，而非空状态集至少有一个元素，最小值恰为一，包含阈值等号。静态端点的精确下界及单状态达到者直接复用命题152.1：每个有限观察者的误差上确界至少为 $\Delta$，恒定读出 $1/2$ 的上确界等于 $\Delta$。该恒定观察者对每个有限词的误差严格小于 $\Delta$，只是沿越来越长的词逼近它。因此(c)不要求某个有限词达到地板。

全历史条件不能换成有限视界条件。若只要求 $|w|\le H$，以所有长度至多 $H$ 的二元词为状态，短词按报告追加，长度为 $H$ 的状态取自环，初态为空词，固定读出为各状态所对应的 $f_r(w)$，便在该视界内精确。其状态数 $2^{H+1}-1$ 不依赖 $r$，而读出表可以依赖 $r$。这与(b)的全历史量词不同。上述结论不给出随 $r$ 的发散速率、单调性或正混合下的精确最优状态数；(a)的有限存在性仅断言 $\varepsilon>0$。证毕。

本命题的静态模型、固定先验下的锐地板及同状态词对来自本卷命题152.1，正混合下全有限历史的有限观察者存在性来自命题153.1。有限轨道步骤直接使用该静态命题所引的 [`finite_orbit_and_readout_eventually_periodic`](../../../../D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound.lean)。正混合近似的共同报告序列误差传播见[《情境时空算术·机器学习》定义21.1、定理21.2](../CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)；命题154.1、155.1给出固定正 $r$ 的区间与覆盖数比较，其参数相关的上界增长不单独蕴含这里的必要状态发散。

有限记忆的相邻问题参见 T. Berg、O. Shayevitz、O. Ordentlich，*Binary Hypothesis Testing with Deterministic Finite-Memory Decision Rules*，[arXiv:2005.07445](https://arxiv.org/abs/2005.07445)：其目标是长时间极限的假设检验 Bayes 错误。稳定动力的有限符号近似参见 G. Pola、A. Girard、P. Tabuada，*Approximately bisimilar symbolic models for nonlinear control systems*，[arXiv:0706.0246](https://arxiv.org/abs/0706.0246)。前者的渐近分类损失、后者的动力系统近似目标均不替代本命题对全部有限历史的下一报告预测误差；这里的趋零必要性由上面的有限词间隙与轨道应用给出。

<a id="entry-662"></a>

## 追加锚（本行以下为增补区）

<a id="section-157"></a>

## 157. 混合趋零时有限确定性观察者的显式对数状态下界

**命题 157.1（有限词排除阈值与必要状态数）。** 固定 $0<p<1/2$，置
$$
d=1-2p,\qquad \Delta=\frac d2,\qquad
\kappa=\frac{1-p}{p}>1.
$$
沿用命题153.1、156.1的时间齐次无控制协议：旧隐藏位 $i\in\{0,1\}$ 先发射报告 $b$，随后以概率 $0\le r<1/2$ 翻转为新隐藏位 $j$，其中
$$
c_{00}=c_{11}=p,\qquad c_{01}=c_{10}=1-p,
\qquad
P_{ji}(r)=\begin{cases}1-r,&j=i,\\r,&j\ne i.\end{cases}
$$
初态为 $I_2/2$，词按时间顺序书写。列向量、词质量和新隐藏位的后验为
$$
v_\varnothing^{(r)}=\binom{1/2}{1/2},\qquad
v_{wb}^{(r)}=P(r)\operatorname{diag}(c_{b0},c_{b1})v_w^{(r)},
\qquad Z_w^{(r)}=\mathbf1^{\mathsf T}v_w^{(r)},\qquad
q_w^{(r)}=\frac{(v_w^{(r)})_1}{Z_w^{(r)}}.
$$
命题156.1的正质量论证给出 $Z_w^{(r)}\ge p^{|w|}>0$，下一报告为零的条件概率是
$$
f_r(w)=\frac{Z_{w0}^{(r)}}{Z_w^{(r)}}=p+dq_w^{(r)}\in[p,1-p],
\qquad f_r(\varnothing)=\frac12.
$$

观察者仍严格取命题156.1的类别：$\mathcal O=(S,s_0,T_0,T_1,t)$，$S$ 非空有限，初态 $s_0\in S$、确定性全函数 $T_b:S\to S$ 及静态实数读出 $t:S\to[0,1]$ 固定，
$$
s_{\mathcal O}(\varnothing)=s_0,\qquad
s_{\mathcal O}(wb)=T_b(s_{\mathcal O}(w)),\qquad
\mathcal E_r(\mathcal O)=\sup_{w\in\{0,1\}^{*}}
|t(s_{\mathcal O}(w))-f_r(w)|.
$$
全部可读的演化记忆均计入 $S$，不另有可读历史、时钟、隐藏位或演化实数寄存器；固定表可含任意精确实数，并可对每个 $r$ 分别设计，但同一张表须适用于包括空词及任意稀有历史在内的全部有限词。$N_{\min}^{(r)}(\varepsilon)$ 是使 $\mathcal E_r(\mathcal O)\le\varepsilon$ 的最小有限状态数，不存在可行有限观察者时取 $\infty$。

固定 $0<\varepsilon<\Delta$，令
$$
\gamma=\frac{\Delta-\varepsilon}{4}>0,
\qquad K\in\mathbb Z_{\ge1},\qquad
\kappa^K\ge\frac{3\Delta+\varepsilon}{\Delta-\varepsilon},
\qquad H_N=2N+3K\quad(N\in\mathbb Z_{\ge1}).
$$
这样的 $K$ 存在，且只依赖 $p,\varepsilon$。对每个整数 $N\ge1$ 及每个 $0<r<1/2$，有较强的有限词排除结论
$$
p r(\kappa^{H_N}-1)\le\gamma
\quad\Longrightarrow\quad
\forall\mathcal O\ (|S|\le N),\quad
\exists w\in\{0,1\}^{*},\quad |w|\le H_N,\quad
|t(s_{\mathcal O}(w))-f_r(w)|\ge\varepsilon+\gamma>\varepsilon.
$$
特别地，原阈值
$$
0<r<\frac12,\qquad
r\le\frac{\gamma p^{H_N}}{H_N}
$$
也排除每个至多 $N$ 状态的观察者，包含右侧阈值的等号。每个可行有限观察者的状态数 $m$ 必须严格满足
$$
m>\frac12\left(
\frac{\log(1+\gamma/(p r))}{\log\kappa}-3K\right).
$$
同一不等式适用于扩展值 $m=N_{\min}^{(r)}(\varepsilon)$，并且
$$
\liminf_{r\downarrow0}
\frac{N_{\min}^{(r)}(\varepsilon)}{\log(1/r)}
\ge\frac1{2\log\kappa}
>\frac1{2\log(1/p)}.
$$
所有对数均为自然对数；这里只断言必要下界，不断言相配的上界或最优速率。

**证明。** 先保留一个直接的条件耦合估计。对长度 $L\ge1$，令 $B_1,\ldots,B_L$ 为相互独立的 $\operatorname{Bernoulli}(r)$ 翻转变量，且与初始均匀隐藏位及全部发射随机种子独立。第 $j$ 步先从旧位发射第 $j$ 个报告，再按 $B_j$ 翻转。置
$$
\mathsf A_L=\{B_1=\cdots=B_L=0\}.
$$
此事件包括最后一次已观察发射之后、下一次预测之前的第 $L$ 次翻转。把正混合与静态过程放在共同初始位和发射种子上；在 $\mathsf A_L$ 上，两条过程直至第 $L$ 次翻转后的隐藏位及全部 $L$ 个报告相同。若 $\mathbb P_r(w,\mathsf A_L)$ 表示指定报告词与该事件的联合概率，则独立种子构造给
$$
\mathbb P_r(w,\mathsf A_L)=(1-r)^L\mathbb P_0(w),
\qquad
\mathbb P_r(I_L=i,w,\mathsf A_L)
=(1-r)^L\mathbb P_0(I_0=i,w),
$$
其中 $I_L$ 是末次翻转后的新隐藏位。故给定 $w,\mathsf A_L$ 的新位后验恰是静态后验。这里不要求、也不推断 $\mathsf A_L$ 与正混合过程的报告词 $w$ 独立。

令 $\theta_w=\mathbb P_r(\mathsf A_L^c\mid w)$。按是否发生翻转分解新位后验，再使用下一发射种子的独立性，得到
$$
f_r(w)=(1-\theta_w)f_0(w)+\theta_w g_w,
\qquad g_w\in[p,1-p].
$$
当条件补事件质量为零时，可任选该区间中的 $g_w$。由命题156.1的分母下界，
$$
\begin{aligned}
|f_r(w)-f_0(w)|
&\le\theta_w
=\frac{\mathbb P_r(w,\mathsf A_L^c)}{Z_w^{(r)}}\\
&\le\frac{\mathbb P_r(\mathsf A_L^c)}{p^L}
=\frac{1-(1-r)^L}{p^L}
\le\frac{Lr}{p^L}.
\end{aligned}
$$
于是对任意整数 $H\ge1$，
$$
\sup_{|w|\le H}|f_r(w)-f_0(w)|\le\frac{Hr}{p^H}.
$$
空词的误差恰为零。此估计只控制有限时域；其随 $H$ 增长的右侧不能变成对全部词长一致的小误差界。特别地，不能把未条件化的翻转概率 $Lr$ 直接当成后验误差界而省去词质量分母。

下面直接应用既有的有限时域误差传播，取得更紧的比较。命题153.1的旧位 Bayes 更新在 $q\in[0,1]$ 上写成
$$
h_0(q)=\frac{(1-p)q}{p+dq},\qquad
h_1(q)=\frac{pq}{1-p-dq},\qquad
F_{b,r}(q)=r+(1-2r)h_b(q).
$$
$h_b$ 把 $[0,1]$ 映入自身，$F_{b,r}$ 把它映入 $[r,1-r]\subseteq[0,1]$。两个分母均至少为 $p$，并且
$$
h_0'(q)=\frac{p(1-p)}{(p+dq)^2},\qquad
h_1'(q)=\frac{p(1-p)}{(1-p-dq)^2},\qquad
0<h_b'(q)\le\frac{1-p}{p}=\kappa.
$$
因此两个 $h_b$ 均为 $\kappa$-Lipschitz，且
$$
|F_{b,r}(q)-h_b(q)|=r|1-2h_b(q)|\le r.
$$
在[《情境时空算术·机器学习》定义21.1、定理21.2](../CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)中，所声明域取 $[0,1]$，摘要取恒等映射，精确更新取 $F_{b,r}$，模型更新与实际求值更新均取 $h_b$。两条轨迹从同一个 $1/2$ 出发、沿同一报告词演化，始终在该域内；代入
$$
\delta_{\rm close}=r,\qquad \delta_{\rm eval}=0,\qquad
 e_0=0,\qquad L_{\rm Lip}=\kappa.
$$
输出取 $q\mapsto p+dq$，其 Lipschitz 常数为 $d$，输出求值误差为零。该定理遂对每个长度 $L\ge0$ 的词给出
$$
|f_r(w)-f_0(w)|
\le d r\sum_{j=0}^{L-1}\kappa^j
=p r(\kappa^L-1),
\qquad \kappa-1=\frac d p.
$$
$L=0$ 时取空和，等式两侧的界均为零。这里的两条后验轨迹仅用于比较两个物理参数的预测函数，不是给有限观察者增加一个未计数的后验寄存器。这个几何界也只在固定有限时域内使用。

现在固定 $N\ge1$、满足较强阈值的 $0<r<1/2$，再任取 $1\le|S|\le N$ 的观察者。直接把命题152.1、156.1所引的有限轨道定理应用于实际 $T_0$、读出 $t$ 及初态 $s_0$，得整数 $n\ge0$、$\ell\ge1$，使
$$
n+\ell\le|S|\le N,\qquad
T_0^{j+\ell}(s_0)=T_0^j(s_0)\quad(j\ge n).
$$
这是状态相等而非仅仅读出相等。定义整数
$$
A=\ell\left\lceil\frac{2K}{\ell}\right\rceil,
\qquad t_{\rm len}=n+\left\lfloor\frac A2\right\rfloor,
\qquad u=0^n1^{t_{\rm len}},\qquad
v=0^{n+A}1^{t_{\rm len}}.
$$
这里 $t_{\rm len}$ 是后缀长度，与读出函数 $t$ 区分。$A$ 是 $\ell$ 的倍数，重复周期等式给 $T_0^{n+A}(s_0)=T_0^n(s_0)$；再用同一个实际更新 $T_1$ 追加共同后缀，便有
$$
s_{\mathcal O}(v)=T_1^{t_{\rm len}}(T_0^{n+A}(s_0))
=T_1^{t_{\rm len}}(T_0^n(s_0))=s_{\mathcal O}(u).
$$
由向上取整及整数性，
$$
2K\le A\le2K+\ell-1,
\qquad
\left\lfloor\frac A2\right\rfloor\ge K,
\qquad
\left\lceil\frac A2\right\rceil\ge K.
$$
又由 $n\le N-\ell$，
$$
\begin{aligned}
|v|&=2n+A+\left\lfloor\frac A2\right\rfloor\\
&\le2N+3K-\ell-1+\left\lfloor\frac{\ell-1}{2}\right\rfloor
\le H_N-2<H_N,\\
|u|&=|v|-A<|v|.
\end{aligned}
$$
故 $H_N$ 是同时适用于所有这些观察者的简单保守词长界。

记 $k(w)=\#0(w)-\#1(w)$。命题152.1、156.1的静态公式等价于
$$
f_0(w)=f_0(k(w)),\qquad
f_0(k)=\frac12+\Delta\frac{\kappa^k-1}{\kappa^k+1}
\quad(k\in\mathbb Z).
$$
该函数随 $k$ 严格递增，且 $f_0(-k)=1-f_0(k)$。上述两词满足
$$
k(u)=-\left\lfloor\frac A2\right\rfloor\le-K,
\qquad k(v)=\left\lceil\frac A2\right\rceil\ge K.
$$
因此它们的静态半间隙有下界
$$
\frac{f_0(v)-f_0(u)}2
\ge\Delta\frac{\kappa^K-1}{\kappa^K+1}
\ge\frac{\Delta+\varepsilon}{2}
=\varepsilon+2\gamma.
$$
中间的不等式恰由 $\kappa^K\ge(3\Delta+\varepsilon)/(\Delta-\varepsilon)$ 得到，包括等号。两词长度不超过 $H_N$，故较强阈值及后验比较分别给
$$
|f_r(u)-f_0(u)|\le\gamma,\qquad
|f_r(v)-f_0(v)|\le\gamma,
\qquad
\frac{f_r(v)-f_r(u)}2\ge\varepsilon+\gamma.
$$
设共同状态的读出为 $a=t(s_{\mathcal O}(u))=t(s_{\mathcal O}(v))$。对任意实数 $a$，三角不等式给
$$
\max\{|a-f_r(u)|,|a-f_r(v)|\}
\ge\frac{|f_r(v)-f_r(u)|}{2}
\ge\varepsilon+\gamma>\varepsilon.
$$
于是 $u,v$ 中至少一词就是所需见证。见证可以依赖观察者，$H_N$ 和两种有限词比较估计则不依赖它；论证覆盖任意读出与任意更新表，也覆盖对每个 $r$ 重新设计的表。

为核对原阈值，若 $H=H_N\ge1$ 且 $r\le\gamma p^H/H$，则
$$
p r(\kappa^H-1)
\le\frac{\gamma p}{H}\bigl((1-p)^H-p^H\bigr)
<\gamma.
$$
这里 $0<(1-p)^H-p^H<1$ 且 $p/H<1$，故右端严格小于 $\gamma$，即使原阈值取等号也成立。前面的条件耦合估计亦直接给出 $Hr/p^H\le\gamma$，与同一词对的半间隙论证相容。

若状态数 $m<\infty$ 的观察者可行，则取 $N=m$ 时较强排除条件必须严格失败：
$$
p r(\kappa^{2m+3K}-1)>\gamma.
$$
由于 $\log\kappa>0$，移项取对数即得陈述中的严格必要状态数不等式。若可行有限基数集非空，它在正整数中有最小元，故该式适用于 $N_{\min}^{(r)}(\varepsilon)$；若为空，$N_{\min}^{(r)}(\varepsilon)=\infty$ 自动满足这个有限实数下界。此步骤不以有限观察者存在性为前提。

最后置 $x=\log(1/r)$，当 $r\downarrow0$ 时 $x\to\infty$，且
$$
\log\left(1+\frac{\gamma}{p r}\right)
=x+\log\left(\frac\gamma p+r\right),
\qquad
\frac{\log(1+\gamma/(p r))}{x}\longrightarrow1.
$$
将逐个 $r$ 的必要下界除以正数 $x$，直接取扩展实数下极限，得到 $1/(2\log\kappa)$。无须假设 $N_{\min}^{(r)}(\varepsilon)/x$ 有界，也无须假设状态成本单调或有限。因为 $1<\kappa<1/p$，此下界蕴含系数 $1/(2\log(1/p))$ 的较弱下界。命题153.1、156.1另行给出的正 $r$、正容差有限存在性与这里相容，但不是此下界证明的前提。

若 $\varepsilon\ge\Delta$，命题156.1的单状态恒定读出 $1/2$ 对全部 $0\le r<1/2$ 可行；这一边界包含等号。本命题不对 $\varepsilon=0$ 作断言。所测量的是在全部有限词上控制最坏预测误差所必需的确定性观察者基数，不是潜在生成器的状态数、熵或物理比特数。潜在载体始终为两个经典状态，各非空报告分支已为测量制备操作，故本下界不描述量子到经典的转变。固定有限视界、典型路径、平均或期望误差、随机观察者以及带外置时钟或自适应干预的任务有不同量词。特别地，隐藏位缓慢切换并不蕴含典型路径上的滤波初始先验遗忘缓慢。这个必要系数不构成全参数域的锐对数定律；在更窄精度区间证明更强下界仍是不同问题。证毕。

本命题的模型及正质量条件化取自命题153.1、156.1，静态后验取自命题152.1、156.1。状态周期步骤直接使用这些命题所引的 [`finite_orbit_and_readout_eventually_periodic`](../../../../D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound.lean)，具体代入为有限集 $S$、自映射 $T_0$、初态 $s_0$ 及读出 $t$；有限时域后验比较直接使用[《情境时空算术·机器学习》定义21.1、定理21.2](../CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)，其域、缺陷和输出常数已在证明中给出。

相邻文献中的损失与极限须分别理解。T. Berg、O. Ordentlich、O. Shayevitz，*Binary Hypothesis Testing with Deterministic Finite-Memory Decision Rules*，[arXiv:2005.07445](https://arxiv.org/abs/2005.07445)，第I节式(4)–(8)及定理1，研究有限状态二元检验的长时间分类错误与状态数指数。V. Sharan、S. Kakade、P. Liang、G. Valiant，*Prediction with a Short Memory*，[arXiv:1612.02526](https://arxiv.org/abs/1612.02526)，推论1，研究下一观测预测的平均损失。P. Chigansky，*Stability of the nonlinear filter for slowly switching Markov chains*，[arXiv:math/0411596](https://arxiv.org/abs/math/0411596)，第1节的几乎处处稳定指数、定理1.1及例1.2，研究初始先验扰动的渐近遗忘；在其假设下，慢切换并不迫使该指数趋于零。这三类结论均不替代这里对每个有限报告词的预测误差要求，也不作为上述状态下界的前提。

<a id="entry-664"></a>

## 追加锚（本行以下为增补区）
<a id="section-158"></a>

## 158. 平衡报告块与逆混合率的必要观察者状态成本

**命题 158.1（低于半静态地板时的逆混合率下界，repo-derived）。** 固定 $0<p<1/2$，记
$$
d=1-2p,\qquad \Delta=\frac d2,\qquad
\kappa=\frac{1-p}{p}>1,\qquad \lambda=\log\kappa>0.
$$
沿用命题153.1、156.1、157.1的二元时间齐次无控制协议：旧隐藏位 $i$ 先发射报告 $b$，然后翻转为新隐藏位 $j$，其中
$$
c_{00}=c_{11}=p,\qquad c_{01}=c_{10}=1-p,\qquad
P_{ji}(r)=\begin{cases}1-r,&j=i,\\r,&j\ne i.\end{cases}
$$
这里 $0<r<1/2$，每个 $b,i,j\in\{0,1\}$ 对应一个单独的秩一 Kraus 算子，仪器为
$$
K_{bji}^{(r)}=\sqrt{c_{bi}P_{ji}(r)}\,|j\rangle\langle i|,
\qquad
\phi_b^{(r)}(X)=\sum_{i,j=0}^1K_{bji}^{(r)}X(K_{bji}^{(r)})^\dagger
\quad(X\in M_2(\mathbb C)).
$$
初态固定为 $I_2/2$。对时间顺序词 $w$，定义
$$
v_\varnothing^{(r)}=\binom{1/2}{1/2},\qquad
v_{wb}^{(r)}=P(r)\operatorname{diag}(c_{b0},c_{b1})v_w^{(r)},
\qquad Z_w^{(r)}=\mathbf1^{\mathsf T}v_w^{(r)},
$$
$$
q_w^{(r)}=\frac{(v_w^{(r)})_1}{Z_w^{(r)}},\qquad
x_w^{(r)}=\log\frac{q_w^{(r)}}{1-q_w^{(r)}},\qquad
h(x)=p+\frac d{1+e^{-x}}=\frac12+\Delta\tanh\frac x2.
$$
下一零报告的条件概率为 $f_r(w)=h(x_w^{(r)})$。

观察者为 $\mathcal O=(S,s_0,T_0,T_1,t)$，其中 $S$ 非空有限，$s_0\in S$、确定性全函数 $T_b:S\to S$ 和静态读出 $t:S\to[0,1]$ 固定，且
$$
s_{\mathcal O}(\varnothing)=s_0,\qquad
s_{\mathcal O}(wb)=T_b(s_{\mathcal O}(w)),\qquad
\mathcal E_r(\mathcal O)=\sup_{w\in\{0,1\}^{*}}
|t(s_{\mathcal O}(w))-f_r(w)|.
$$
全部可读的演化记忆均计入 $S$，包括任何可读时钟、档案和随机种子状态；不允许从 $S$ 之外读取演化信息。这里的更新与读出是确定性的，不另取随机观察者类别。每组 $p,r,\varepsilon$ 可分别选择观察者及含任意精确实数的固定表，但每张表必须同时满足包括空词及任意稀有历史在内的全部有限词误差要求。定义 $N_{\min}^{(r)}(\varepsilon)$ 为满足 $\mathcal E_r(\mathcal O)\le\varepsilon$ 的最小有限状态数；不存在这样的有限观察者时取 $\infty$。

固定
$$
0<\varepsilon<\frac\Delta2,
$$
再选一个固定整数 $a\ge1$，使
$$
g_a=\Delta\tanh\frac{a\lambda}{4}>2\varepsilon.
$$
由于 $\tanh(a\lambda/4)\to1$，这样的 $a$ 存在。置
$$
D_a=\kappa^a-\kappa^{-a}>0,\qquad
C_a=d\,aD_a>0,\qquad
c=\frac{g_a-2\varepsilon}{2C_a}>0.
$$
则存在 $r_0\in(0,1/2)$，使
$$
\forall r\in(0,r_0),\qquad
N_{\min}^{(r)}(\varepsilon)\ge\frac c r.
$$
这里先固定 $p,\varepsilon,a$，再选择 $r_0$；$c,r_0$ 不依赖观察者。此结论在较窄精度区间内加强命题157.1的必要下界，不改变该命题在 $0<\varepsilon<\Delta$ 上的结论。

**证明。** 对任意复矩阵 $X$，每个独立 Kraus 项都满足
$$
K_{bji}^{(r)}X(K_{bji}^{(r)})^\dagger
=c_{bi}P_{ji}(r)X_{ii}|j\rangle\langle j|.
$$
故从对角输入出发，新对角元 $j$ 恰为 $\sum_i c_{bi}P_{ji}(r)(v_w^{(r)})_i$，给出陈述中的列向量递推。这里求和的是各 Kraus 项的共轭作用，不是先将 Kraus 算子相加再共轭。由 $P(r)$ 每列和为一及 $c_{bi}\ge p$，
$$
Z_{wb}^{(r)}=\sum_i c_{bi}(v_w^{(r)})_i\ge pZ_w^{(r)},
\qquad Z_w^{(r)}\ge p^{|w|}>0.
$$
初态两分量严格为正，递推保持严格正性，所以每个有限词的 $q_w^{(r)}\in(0,1)$，其对数赔率均有定义。下一零报告的条件概率为 $p+dq_w^{(r)}=h(x_w^{(r)})$；空词给 $x_\varnothing^{(r)}=0$、$f_r(\varnothing)=h(0)=1/2$。

旧位发射报告零时将赔率乘以 $\kappa$，发射报告一时乘以 $\kappa^{-1}$；随后翻转。于是精确的对数赔率更新为
$$
F_{b,r}(x)=G_r\bigl(x+(-1)^b\lambda\bigr),\qquad
G_r(z)=\log\frac{(1-r)e^z+r}{re^z+1-r}.
$$
这也说明末次已报发射后的翻转已经包含在预测状态中。$G_r$ 为奇函数，$G_r(0)=0$，并且
$$
G_r'(z)=\frac{1-2r}{1+2r(1-r)(\cosh z-1)}.
$$
令 $\eta=1-2r\in(0,1)$，便有
$$
0<G_r'(z)\le\eta<1,\qquad
|G_r(z)|\le\eta|z|<|z|\quad(z\ne0).
$$
因此每个 $F_{b,r}$ 严格递增且为 $\eta$-Lipschitz。又
$$
0<h'(x)=\frac{d e^{-x}}{(1+e^{-x})^2}\le\frac d4.
$$
这些界对各自的全部实数自变量成立；在 $r=0$ 时 $G_0=\operatorname{id}$，不具有上述严格收缩性。

固定平衡词 $v=0^a1^a$，置
$$
I=[-a\lambda,0],\qquad A_r=F_{0,r}^{\circ a},\qquad
B_r(x)=-A_r(x),\qquad H_r=F_{1,r}^{\circ a}\circ F_{0,r}^{\circ a}.
$$
先证相关映射的保域性。若 $x\in I$，记 $x_j=F_{0,r}^{\circ j}(x)$。归纳给出
$$
-(a-j)\lambda\le x_j\le j\lambda\qquad(0\le j\le a).
$$
确实，$j=0$ 正是 $x\in I$；若结论在 $j<a$ 时成立，则送入下一次 $G_r$ 的数满足
$$
x_j+\lambda\in[-(a-j-1)\lambda,(j+1)\lambda].
$$
此区间包含零，$G_r$ 保持符号并将绝对值压向零，所以输出仍在该区间。特别地，$A_r(I)\subseteq[0,a\lambda]$，$A_r(-a\lambda)\ge0$。从零出发的第一步严格为正，往后保持正性；每次正输入经 $G_r$ 严格缩小，故
$$
u:=A_r(0)\in(0,a\lambda).
$$
$G_r$ 的奇性还给 $F_{1,r}(x)=-F_{0,r}(-x)$，迭代后得到
$$
F_{1,r}^{\circ a}(x)=-A_r(-x),\qquad H_r(x)=-A_r(-A_r(x))=B_r^2(x).
$$
所以 $B_r:I\to I$ 为 $\eta^a$-Lipschitz，$H_r:I\to I$ 为 $\eta^{2a}$-Lipschitz。

闭区间 $I$ 非空且完备，直接对 $B_r$ 应用 Banach 不动点定理，得到唯一不动点 $x_r\in I$，且
$$
B_r(x_r)=x_r,\qquad A_r(x_r)=-x_r.
$$
由于 $A_r$ 递增，
$$
B_r(0)=-u<0,\qquad
B_r(-a\lambda)=-A_r(-a\lambda)\ge-u>-a\lambda,
$$
两端点都不是不动点，故 $-a\lambda<x_r<0$。$x_r$ 也是 $H_r=B_r^2$ 的不动点；再由 $H_r$ 的严格收缩性及同一 Banach 定理，它是 $H_r$ 在 $I$ 内的唯一不动点，并且
$$
H_r^n(0)\longrightarrow x_r\qquad(n\to\infty).
$$
这里对每个固定 $r>0$ 分别应用收缩定理，不把 $\eta^{2a}<1$ 当作对 $r\downarrow0$ 一致的严格收缩常数。

下面估计反射不动点的位置及整块位移。上行归纳已经表明每次送入 $G_r$ 的数都在 $[-a\lambda,a\lambda]$。下行从任意 $y_0\in[0,a\lambda]$ 开始，记 $y_j=F_{1,r}^{\circ j}(y_0)$，同理归纳得
$$
-j\lambda\le y_j\le(a-j)\lambda\qquad(0\le j\le a).
$$
在第 $j+1$ 步，输入 $y_j-\lambda$ 落在 $[-(j+1)\lambda,(a-j-1)\lambda]$，该区间仍包含零且包含于 $[-a\lambda,a\lambda]$。因此上下两程的所有中间输入都受同一个紧区间控制。

对 $|z|\le a\lambda$，有恒等式
$$
G_r(z)-z
=\log(1-r+re^{-z})-\log(1-r+re^z).
$$
两个对数自变量均至少为 $1-r$，对数函数在它们之间的导数至多为 $1/(1-r)$；又 $|e^z-e^{-z}|\le D_a$，所以
$$
|G_r(z)-z|\le\frac{rD_a}{1-r}.
$$
沿上行的 $a$ 步，将每步写成 $x_{j+1}=x_j+\lambda+[G_r(x_j+\lambda)-(x_j+\lambda)]$ 并求和，得到对所有 $x\in I$ 成立的界
$$
|A_r(x)-(x+a\lambda)|\le\frac{arD_a}{1-r}.
$$
在 $x=x_r$ 处使用精确方程 $A_r(x_r)=-x_r$，便有
$$
|2x_r+a\lambda|\le\frac{arD_a}{1-r},\qquad
x_r\longrightarrow-\frac{a\lambda}{2}\quad(r\downarrow0).
$$
这一步只比较一个不动点方程和有限步缺陷，没有 Taylor 余项，也没有交换迭代极限与参数极限。

对整个平衡块，上下两程的 $2a$ 个有符号增量相消。把同一逐步缺陷界相加，得
$$
|H_r(x)-x|\le\frac{2arD_a}{1-r}\le4arD_a
\qquad(x\in I, 0<r<1/2).
$$
现在直接应用既有的输出轨迹误差定理 [`output_trajectory_error`](../../../../D5/S3/Observer/MetricGeometry/OutputTrajectoryError.lean)：其域与映射取
$$
Y=I,\quad Z=\mathbb R,\quad
\tau=H_r,\quad \sigma=\operatorname{id}_{\mathbb R},\quad
\pi:I\hookrightarrow\mathbb R,\quad
q_{\rm out}=h|_I,\quad o=h.
$$
在该定理中代入 $L=1$、$M=d/4$、一步缺陷 $\delta=4arD_a$、读出不匹配量零，并取初态 $0\in I$。恒等比较轨迹始终为零，真实块轨迹由保域性始终在 $I$，故全部假设成立。定理给出对每个整数 $n\ge0$ 的估计
$$
\left|h(H_r^n(0))-\frac12\right|
\le\frac d4\,(4arD_a)\sum_{j=0}^{n-1}1^j
=C_a n r.
$$
$n=0$ 时空和为零。等价地，在[《情境时空算术·机器学习》定义21.1、定理21.2](../CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)中，取精确域 $I$、摘要为到 $\mathbb R$ 的包含映射、精确更新 $H_r$、模型更新及实际求值更新均为恒等映射，闭合缺陷 $4arD_a$、求值缺陷零、初始误差零、Lipschitz 常数一；输出为 $h$，输出 Lipschitz 常数 $d/4$，输出求值误差零，即得到同一估计。这里使用的比较轨迹是数学上的误差参照，没有给观察者增加演化实数寄存器。

令
$$
g_r=\frac12-h(x_r)>0.
$$
由已证的不动点位置极限及 $h$ 的连续性，
$$
g_r\longrightarrow\frac12-h\!\left(-\frac{a\lambda}{2}\right)
=\Delta\tanh\frac{a\lambda}{4}=g_a>2\varepsilon.
$$
因此可选 $r_0\in(0,1/2)$，使
$$
g_r-2\varepsilon\ge\frac{g_a-2\varepsilon}{2}
\qquad(0<r<r_0).
$$
此选择只依赖先前固定的 $p,\varepsilon,a$。

固定任意这样的 $r$，再固定任意误差至多 $\varepsilon$ 的 $m=|S|$ 状态观察者。对有限集 $S$ 上的块更新
$$
U=T_1^{\circ a}\circ T_0^{\circ a}
$$
及其初态 $s_0$、读出 $t$，直接应用 [`finite_orbit_and_readout_eventually_periodic`](../../../../D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound.lean)，得到整数 $n\ge0$、$\ell\ge1$，使
$$
n+\ell\le m,\qquad
U^{j+\ell}(s_0)=U^j(s_0)\quad(j\ge n).
$$
反复使用该状态等式，得 $U^{n+k\ell}(s_0)=U^n(s_0)$ 对所有 $k\ge0$ 成立。这是完整观察者状态相同；固定读出因而相同。记该读出为 $t_*=t(U^n(s_0))$。对应历史是有限词 $v^{n+k\ell}$，它的真实对数赔率为 $H_r^{n+k\ell}(0)$，故可行性给
$$
|t_*-h(H_r^n(0))|\le\varepsilon,\qquad
|t_*-h(H_r^{n+k\ell}(0))|\le\varepsilon\quad(k\ge0).
$$
因为 $\ell\ge1$，在当前固定 $r$ 与当前固定观察者下令 $k\to\infty$，Banach 收敛及 $h$ 连续性给
$$
|t_*-h(x_r)|\le\varepsilon.
$$
这里每个被使用的有限词都有质量至少 $p^{2a(n+k\ell)}>0$；没有断言无限周期报告路径具有正概率。若 $n=0$，第一条误差约束就是空词约束，已包含在观察者定义中。

最后连用三角不等式和轨迹误差界，得到
$$
\begin{aligned}
g_r
&\le\left|\frac12-h(H_r^n(0))\right|
 +|h(H_r^n(0))-t_*|+|t_*-h(x_r)|\\
&\le C_a n r+2\varepsilon
\le C_a m r+2\varepsilon.
\end{aligned}
$$
由于 $C_a r>0$，
$$
m\ge\frac{g_r-2\varepsilon}{C_a r}
\ge\frac{g_a-2\varepsilon}{2C_a r}=\frac c r.
$$
有限轨道定理计数的是自映射 $U$ 的应用次数，即平衡块数 $n$，并不额外乘以词长 $2a$；这 $2a$ 步已计入整块位移估计。上述论证适用于每一个可行观察者，包括对各 $p,r,\varepsilon$ 分别重新设计的精确实数表。因此，可行有限基数集非空时，其最小元满足同一下界；该集合为空时 $N_{\min}^{(r)}(\varepsilon)=\infty$ 自动满足下界。证毕。

本命题的模型、条件化与对数赔率坐标使用本卷命题153.1、156.1、157.1；块轨迹误差与有限状态周期界分别使用上述输出轨迹定理、ML 定理21.2与有限轨道定理。Banach 步骤使用非空完备度量空间上的收缩映射定理，见钉版 Mathlib 的 [`Contracting.lean`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Topology/MetricSpace/Contracting.lean) 中 `ContractingWith.fixedPoint_isFixedPt`、`ContractingWith.fixedPoint_unique` 与 `ContractingWith.tendsto_iterate_fixedPoint`。本命题给出这些既有结果在所列平衡块模型中的普通推导，不作新颖性断言。

相邻文献的对象与量词不同。P. Chigansky，*Stability of the nonlinear filter for slowly switching Markov chains* (2006)，[arXiv:math/0411596](https://arxiv.org/abs/math/0411596)，第1节、定理1.1及二元例1.2，讨论不同初始先验所产生滤波器之差的几乎处处渐近指数；慢切换时该遗忘指数可以保持非零负极限。M. E. Hellman、T. M. Cover，*Learning with Finite Memory*，*The Annals of Mathematical Statistics* 41 (1970), 765–782，[原文](https://isl.stanford.edu/~cover/papers/paper018.pdf)，第0节（第765页）以长时间假设检验错误概率为损失，并允许随机化的时间齐次有限状态更新。这不同于这里的确定性逐词预测误差；上述所引结论不充当本命题的最坏有限词观察者基数界，也不作为该界的前提。

结论仅限 $0<\varepsilon<\Delta/2$ 及充分小的正 $r$。本命题不对 $\varepsilon=0$ 或 $\varepsilon\ge\Delta/2$ 作出相同速率断言，不给匹配上界、最优 $a$ 或最优常数、状态成本单调性、关于容差的一致界或有限精度表的位成本。固定 $r$ 后的周期子序列极限与不动点的小 $r$ 位置估计各自独立成立，未交换两种极限。成本对象是观察者的全部演化可读状态数，潜在生成器的状态数始终为二；这不是熵、物理比特或能量下界。即使 $r=0$，每个非空报告分支也已经是测量制备映射，故此成本发散不描述量子到经典的转变。
