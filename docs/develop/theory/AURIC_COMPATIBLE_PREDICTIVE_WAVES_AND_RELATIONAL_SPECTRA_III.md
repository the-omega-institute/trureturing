# 相容预测波与关系谱 III：原完整纤维的精确最小最大分支

## 1. 原问题、忠实提升与接触族

**定义 1.1（原模型及范数约定）。** 母卷指《[相容预测波与关系谱](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md)》。固定母卷 §17.1、§29.1 的复 Hilbert 空间、五维原仪器、等距嵌入 $B$、酉矩阵 $U$、输入正交基 $(q,r,f)$ 及 $P_+=qq^\dagger+rr^\dagger$。原菜单只给擦除分支标签后的全深度效果 $J_j=(\mathcal G^\dagger)^j(P)$。对 $0<t<1$ 置 $d=t^2$，令

$$
\mathcal F_t=\{T:M_3(\mathbb C)\longrightarrow M_5(\mathbb C)\text{ CPTP}:
T^\dagger(J_j)=Y_j\ (j\ge0)\},\qquad
r(d)=\inf_{R\ \mathrm{CPTP}}\sup_{T\in\mathcal F_{\sqrt d}}
\|R-\mathcal GT\|_\diamond.
\tag{III.1.1}
$$

$Y_j$ 是母卷 (35.1) 的完整输入效果算子。$T$ 的五维输出支持及 Kraus 秩不受额外限制，$R:M_3\to M_5$ 为任意共同 CPTP 重建。采用不除以二的范数

$$
\|\Lambda\|_\diamond=
\sup_{n\ge1}\sup_{0\ne X\in M_n(\mathbb C)\otimes M_3(\mathbb C)}
\frac{\|(\operatorname{id}_{M_n}\otimes\Lambda)(X)\|_1}{\|X\|_1},
\qquad \|X\|_1=\operatorname{Tr}\sqrt{X^\dagger X}.
\tag{III.1.2}
$$

所以输入为全部复矩阵，参考为任意有限且未触动的系统。下文仅在这一量子模型及所给完整算子数据的前提内求解 (III.1.1)。

**定义 1.2（母卷的完整状态纤维及原域对应）。** 在后继正交基 $(a,h,g)=(Uq,Ur,Uf)$ 中，令

$$
\begin{gathered}
C=(a+h)(a+h)^\dagger=
\begin{pmatrix}1&1&0\\1&1&0\\0&0&0\end{pmatrix},\qquad
E=\frac1{16}
\begin{pmatrix}1&3&\sqrt6\\3&9&3\sqrt6\\\sqrt6&3\sqrt6&6\end{pmatrix},\\
\alpha=\frac{2+\sqrt2}{\sqrt{12}},\qquad
\gamma=\frac{2-\sqrt2}{\sqrt{12}},\qquad
k=\alpha a+\gamma h,\qquad
N=\operatorname{span}_{\mathbb C}\{k,g\}.
\end{gathered}
\tag{III.1.3}
$$

$N$ 为固定原负扇区，不能自由旋转。沿用母卷 [§35](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md#35-原通道完整纤维的后继约化) 的忠实集合

$$
\begin{aligned}
\mathcal K_d=\{\rho=A+D:;& A,D\succeq0,\quad\operatorname{ran}D\subseteq N,
\quad\operatorname{Tr}\rho=1,\\
& a^\dagger Aa=d,\quad\operatorname{Tr}(C\rho)=d,
\quad\operatorname{Tr}(E\rho)=(6-5d)/16\}.
\end{aligned}
\tag{III.1.4}
$$

特别地，$D_{kk}=k^\dagger Dk$，且每个忠实提升均满足

$$
\rho_{aa}-d=\alpha^2D_{kk}\ge0,\qquad
P_NCP_N=\frac43kk^\dagger.
\tag{III.1.5}
$$

母卷定理 35.4–35.5 供应的对应为

$$
\begin{gathered}
\omega=V^\dagger(A\oplus D)V,\qquad
T_\omega(X)=BP_+XP_+B^\dagger+(f^\dagger Xf)\omega,\\
S_\rho(X)=B[UP_+XP_+U^\dagger+(f^\dagger Xf)\rho]B^\dagger,
\qquad \mathcal GT_\omega=S_\rho,\\
R_\sigma=S_\sigma,\qquad
\|S_\rho-R_\sigma\|_\diamond=\|\rho-\sigma\|_1,\\
r(d)=\min_{\sigma\succeq0,\ \operatorname{Tr}\sigma=1}
\max_{\rho\in\mathcal K_d}\|\rho-\sigma\|_1.
\end{gathered}
\tag{III.1.6}
$$

这里 $Vx=(D_+x,D_-x)$ 是母卷定义 35.1 的酉识别 $\mathbb C^5\simeq\mathbb C^3\oplus N$；$D_\pm$ 与提升变量 $D$ 不同。所有极值均达到，中心 $\sigma$ 允许不属于 $\mathcal K_d$。该约化的下界对任意共同重建成立：母卷定理 35.5 将任意 $R$ 的 $ff^\dagger$ 输出压缩成一个密度中心，且不增加相应迹距离。因此本卷对所有密度中心的下界也约束所有原 CPTP 重建；本卷构造的 $R_\sigma$ 则在全部复输入及全部有限参考上达到相应上界。

母卷 [§36](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md#36-复完整纤维的全部极端边界) 的三个极端层 $\mathsf P,\mathsf R_0,\mathsf R_+$ 都保留在 (III.1.4) 内。上界证明不将该集合替换为纯态、实态或有界秩的子集。

**定义 1.3（原纤维的四个复纯接触候选）。** 对

$$
0<u<\min\{1-d,4d\}
\tag{III.1.7}
$$

及 $\epsilon,\delta\in\{1,-1\}$，置

$$
\begin{gathered}
x_\epsilon=-\frac{u}{2\sqrt d}
 +\epsilon\,\mathrm i\sqrt{u-\frac{u^2}{4d}},\qquad
b_\epsilon=\sqrt d+3x_\epsilon,\\
y_{\epsilon,\delta}=\delta\,\mathrm i\sqrt{1-d-u}
\cdot\frac{b_\epsilon}{|b_\epsilon|},\qquad
\psi_{\epsilon,\delta}=\sqrt d\,a+x_\epsilon h+y_{\epsilon,\delta}g,
\qquad \rho_{\epsilon,\delta}=\psi_{\epsilon,\delta}\psi_{\epsilon,\delta}^\dagger,\\
M_d(u)=\begin{pmatrix}d&-u/2&0\\-u/2&u&0\\0&0&1-d-u\end{pmatrix}.
\end{gathered}
\tag{III.1.8}
$$

物理提升使用母卷 §29 的 $p=Bq$、$c_5=(e_0+e_1-e_3-e_4)/2$，即

$$
\phi_{\epsilon,\delta}=\sqrt d\,p+x_\epsilon Br+y_{\epsilon,\delta}c_5
=V^\dagger(\psi_{\epsilon,\delta},0).
\tag{III.1.9}
$$

标量 $c$ 在下文表示半径的一半，不表示物理向量 $c_5$。

**定义 1.4（数学供应与归属）。** 本卷的承重对象是 (III.1.4) 的具体矩阵、原平面 $N$、参数分支及其匹配上下界，归为 `repo-derived`。母卷 [§37](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md#37-纯截面的精确中心混合活动世界与关系切口) 的纯截面、混合活动障碍，以及 [§38](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md#38-完整纤维的固定重建风险严格上界与未决中心) 的固定中心风险和全域界直接复用。

成熟中间工具仅在这些具体分支的证明内使用：等期望纯态系综与秩一支配沿用母卷定理 37.2 的构造；有限维谱分解、逆矩阵凸性及带下限的标量水位分配用于本卷定理 4.2 的具体矩阵族。通道表示及范数背景的文献供应为 Watrous, *The Theory of Quantum Information*，[第二章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf) 定理 2.22、2.26、推论 2.27，以及[第三章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf) 命题 3.44、定理 3.51。母卷 §38.4 给出的 Chiribella [极端谱面结果](https://arxiv.org/html/2311.10929v1) 只供应母卷 §36 的支撑扰动背景。本卷不把这些通用工具、其改写或单个有理应用作为独立的新一般理论，也不据此主张文献全域新颖性。

## 2. 小参数分支的完整提升证书

**定理 2.1（小参数的精确原通道半径）。** 令

$$
d_s=\frac{500}{7333+828\sqrt2}.
\tag{III.2.1}
$$

对每个 $0<d\le d_s$，置

$$
q=5d,\qquad w=\frac{a-2h}{\sqrt5},\qquad
z_0=\frac{2a+h}{\sqrt5},\qquad
c=\sqrt{q(1-q)},\qquad
\sigma=qww^\dagger+(1-q)gg^\dagger.
\tag{III.2.2}
$$

则 $\sigma$ 是秩二密度矩阵，且

$$
r(d)=2\sqrt{5d(1-5d)}.
\tag{III.2.3}
$$

原共同重建 $R_\sigma$ 达到该值。$d_s$ 是下面提升证书的充分端点；此定理不断言它是该半径表达式可能成立的最大端点。

**证明。** 本域内 $0<q<1$，故 $c>0$，且

$$
S=\sigma+cI\succ0,\qquad Z=S^{-1}=
\operatorname{diag}\left(\frac1{q+c},\frac1c,\frac1{1-q+c}\right)_{(w,z_0,g)}.
\tag{III.2.4}
$$

首先在本证明内固定所消费的逆球工具，包含奇异复密度的情形。若任意密度 $\rho$ 满足 $\kappa_\rho=\operatorname{Tr}(Z\rho)\le1$，则

$$
B_0=\rho^{1/2}(Z-\kappa_\rho I)\rho^{1/2}
\tag{III.2.5}
$$

为迹零 Hermitian。非零时它的最小、最大 Rayleigh 值跨越零，在两相应特征向量之间选取一个零 Rayleigh 单位向量。压缩至其正交补后迹仍为零，归纳得一个使 $B_0$ 对角全零的正交基 $(e_j)$。若某次压缩为零，任意正交基即可。置 $p_j=\|\rho^{1/2}e_j\|^2$，丢弃 $p_j=0$ 的列，则

$$
\rho=\sum_jp_jv_jv_j^\dagger,\qquad
v_j=\rho^{1/2}e_j/\sqrt{p_j},\qquad
\sum_jp_j=1,\qquad v_j^\dagger Zv_j=\kappa_\rho\le1.
\tag{III.2.6}
$$

这不要求 $\rho$ 可逆，也不要求系综的每项分别满足原矩约束。秩一支配判据给 $v_jv_j^\dagger\preceq S$：经 $S^{-1/2}$ 合同变换，左侧唯一非零特征值为 $v_j^\dagger S^{-1}v_j\le1$。$v_jv_j^\dagger-\sigma$ 在 $v_j^\perp$ 上非正，故至多有一个正特征值；它又迹零且不超过 $cI$，所以迹范数至多 $2c$。凸性得到

$$
\operatorname{Tr}(Z\rho)\le1
\quad\Longrightarrow\quad \|\rho-\sigma\|_1\le2c.
\tag{III.2.7}
$$

这是母卷定理 37.2 所用成熟系综方法在当前 $Z$ 的应用。对迹零三阶 Hermitian 矩阵，正负谱中至少一侧只有一个非零特征值，因而 $\|H\|_1=2\|H\|_{\rm op}$；所以 (III.2.7) 同时给 $\sigma-cI\preceq\rho\preceq\sigma+cI$。

现在直接检验完整提升，而不只检验 $D=0$ 截面。置

$$
T=\sqrt{\frac{q}{1-q}},\quad
\lambda=\frac1{1-q+c},\quad
\mu=3\left(\frac1{q+c}-\lambda\right),\quad
\nu=2\left(\frac1{q+c}-\lambda\right).
\tag{III.2.8}
$$

$T$ 是此处的正实标量，与原通道的字母无关。由 $q=T^2/(1+T^2)$、$c=T/(1+T^2)$ 得

$$
\lambda+(\mu+\nu)d=1.
\tag{III.2.9}
$$

对 $A$ 扇区及 $D$ 扇区分别设

$$
W_A=\lambda I+\mu aa^\dagger+\nu C,\qquad
W_D=\lambda I_N+\nu(P_NCP_N)|_N.
\tag{III.2.10}
$$

在正交基 $(w,z_0,g)$ 及 $(k,g)$ 直接展开给出精确余量

$$
\begin{aligned}
W_A-Z&=L_z z_0z_0^\dagger,
&L_z&=\frac{(1+T^2)(5-6T)}{T(1+T)},\\
W_D-(P_NZP_N)|_N&=L_Dkk^\dagger,
&L_D&=\frac{(1+T^2)[50-(69+6\sqrt2)T]}{30T(1+T)}.
\end{aligned}
\tag{III.2.11}
$$

第二式为压缩恒等式，不要求 $Z$ 保持 $N$。例如其 $gg$ 差为零，$kk$ 差由 $k=\alpha a+\gamma h$、$C|_N=(4/3)kk^\dagger$ 给出；第一式的 $wz_0$ 差及 $ww,gg$ 差均为零。这些矩阵恒等式也固定了全部混合提升的系数。

对所有 $T>0$，$L_z\ge0$ 恰当且仅当 $T\le5/6$，等号只在 $T=5/6$；$L_D\ge0$ 恰当且仅当

$$
T\le T_s:=\frac{50}{69+6\sqrt2}<\frac56,
\qquad \frac{T_s^2}{5(1+T_s^2)}=d_s.
\tag{III.2.12}
$$

因此 $0<d<d_s$ 时两系数严格为正；$d=d_s$ 时 $L_D=0$ 而 $L_z>0$。作为系数的另一个零点，$T=5/6$ 对应 $d=5/61$，它不属于本定理的完整提升适用域。

任取 (III.1.4) 中的复 $A,D$。由原约束、(III.2.9) 及 (III.2.11)，

$$
\begin{aligned}
1-\operatorname{Tr}(Z\rho)
&=\operatorname{Tr}((W_A-Z)A)
 +\operatorname{Tr}((W_D-P_NZP_N)D)\\
&=L_z z_0^\dagger Az_0+L_DD_{kk}\ge0.
\end{aligned}
\tag{III.2.13}
$$

这里 $\operatorname{Tr}(W_AA)+\operatorname{Tr}(W_DD)=\lambda\operatorname{Tr}\rho+\mu A_{aa}+\nu\operatorname{Tr}(C\rho)=1$。所以 (III.2.7) 覆盖每个复混合 $\rho\in\mathcal K_d$，给半径上界 $2c$。

下界使用两个实际原相容纯态

$$
\psi_\pm=\sqrt d\,(a-2h)\pm\mathrm i\sqrt{1-5d}\,g
=\sqrt q\,w\pm\mathrm i\sqrt{1-q}\,g.
\tag{III.2.14}
$$

它们范数一，$aa=d$，且

$$
\psi_\pm^\dagger C\psi_\pm=d,\qquad
16\psi_\pm^\dagger E\psi_\pm
=25d+6(1-5d)=6-5d.
\tag{III.2.15}
$$

取 $A=\psi_\pm\psi_\pm^\dagger,D=0$ 即为忠实提升；原五维纯向量为 $\sqrt d\,(p-2Br)\pm\mathrm i\sqrt{1-5d}\,c_5$，代入 (III.1.6) 给原 CPTP 通道。两密度的中点为 $\sigma$，而它们的差在 $(w,g)$ 平面上具有特征值 $2c,-2c$，故相互迹距离为 $4c$。任意密度中心的两项最坏距离至少为 $2c$，无论该中心是否属于 $\mathcal K_d$。结合 (III.1.6)，上界与原全部共同重建的下界相等。∎

## 3. 中参数的代数分支与匹配原接触

**定义 3.1（代数参数及中心）。** 令

$$
\begin{aligned}
F_6(x)&=225x^6-60x^5+131x^4+112x^3-161x^2+44x-3,\\
D_6(x)&=25x^6+16x^5+23x^4-56x^3+31x^2-8x+1,\\
P_6(x)&=10x^6-30x^5+21x^4-12x^3+12x^2-6x+1,\\
G_4(x)&=15x^4+4x^3+16x^2-12x+1,\\
J_4(x)&=-15x^4-32x^3+36x^2-16x+3,\\
d(x)&=\frac{(x^2+2x-1)^2(5x^2-4x+1)}{D_6(x)},\qquad
x_m=2-\sqrt3.
\end{aligned}
\tag{III.3.1}
$$

$x_0$ 表示 $F_6$ 在 $(1/10,11/100)$ 中的唯一根，$d_b=d(x_0)$。根的存在、唯一性及分母正性在定理 3.2 中证明。对 $0<x\le x_m$ 定义

$$
\begin{gathered}
a_x=(1-x)^2,\quad b_x=-2x^2,\quad h_x=2x,\\
\Delta=a_xh_x-b_x^2=2x(1-2x)(1+x^2),\qquad
g_x=\frac{\Delta}{a_x+b_x},\qquad
T_x=\begin{pmatrix}a_x&b_x&0\\b_x&h_x&0\\0&0&g_x\end{pmatrix},\\
Q=\operatorname{Tr}(T_x^2),\quad L=\operatorname{Tr}T_x,\quad
\kappa=\frac LQ,\quad
c=\frac{L^2-Q}{3Q},\quad
\sigma_x=\kappa T_x-cI.
\end{gathered}
\tag{III.3.2}
$$

$a_x,h_x$ 是标量，与基向量 $a,h$ 不同。

**定理 3.2（中参数的精确完整半径）。** 对每个 $2/7\le d\le d_b$，存在唯一 $x\in[x_0,x_m]$ 满足 $d=d(x)$。此时 (III.3.2) 的 $\sigma_x$ 是密度矩阵，并且

$$
r(d)=2c=\frac{2(L^2-Q)}{3Q}.
\tag{III.3.3}
$$

中心在 $2/7\le d<d_b$ 时秩三，在 $d=d_b$ 时秩二；$R_{\sigma_x}$ 达到原全部复通道问题的值。左端点为

$$
d(x_m)=\frac27,\qquad
c(x_m)=\frac27+\frac{4\sqrt3}{21},\qquad
r(2/7)=\frac47+\frac{8\sqrt3}{21}.
\tag{III.3.4}
$$

**证明。** 先给精确根与符号证书。对一个实多项式 $f$，令 $f_0=f/\operatorname{lc}(f)$、$f_1=f_0'$，再递归 $f_{j+1}=-\operatorname{rem}(f_{j-1},f_j)$ 直至非零常数。以 $V_f(v)$ 表示该序列在 $v$ 处去掉零值后的变号数。下面的符号字串按此递归顺序排列；前面三个六次式的次数为 $6,5,4,3,2,1,0$，后面两个四次式的次数为 $4,3,2,1,0$。所有端点均为有理数，表中没有零值。

| $f$ | 端点 $v$ | 序列符号 | $V_f(v)$ |
| --- | --- | --- | --- |
| $F_6$ | $0$ | $-+++-+-$ | $4$ |
| $F_6$ | $1/10$ | $-++--+-$ | $4$ |
| $F_6$ | $11/100$ | $+++--+-$ | $3$ |
| $F_6$ | $67/250$ | $+---+--$ | $3$ |
| $P_6$ | $0$ | $+--+-++$ | $4$ |
| $P_6$ | $67/250$ | $+--+--+$ | $4$ |
| $D_6$ | $0$ | $+--++--$ | $3$ |
| $D_6$ | $67/250$ | $+--++--$ | $3$ |
| $G_4$ | $1/10$ | $---+-$ | $2$ |
| $G_4$ | $67/250$ | $--+--$ | $2$ |
| $J_4$ | $1/10$ | $-+++-$ | $2$ |
| $J_4$ | $67/250$ | $-+++-$ | $2$ |

此表的有理余式递归与下列有理锚值给出 Sturm 符号证书：

$$
\begin{gathered}
F_6(0)=-3,\quad F_6(1/10)=-\frac{3411}{40000},\quad
F_6(11/100)=\frac{2383360209}{40000000000},\\
P_6(0)=D_6(0)=1,\qquad
G_4(1/10)=-\frac{69}{2000},\qquad
J_4(1/10)=\frac{3453}{2000}.
\end{gathered}
\tag{III.3.5}
$$

于是 $F_6$ 在 $[0,67/250]$ 恰有一个根，且位于 $(1/10,11/100)$；$P_6,D_6$ 在该区间严格为正，$G_4<0,J_4>0$ 在 $[1/10,67/250]$ 成立。$x_m<67/250$ 由 $(433/250)^2<3$ 得到，故上述符号覆盖所需的全部区间。特别地 $F_6<0$ 在 $(0,x_0)$，$F_6\ge0$ 在 $[x_0,x_m]$，且只有 $x_0$ 取零。

直接微分并因式分解为

$$
d'(x)=\frac{-16x(2x-1)(x^2+2x-1)P_6(x)}{D_6(x)^2}<0
\qquad(0<x\le x_m).
\tag{III.3.6}
$$

此处 $2x-1<0$、$x^2+2x-1<0$，其他因子严格为正。又 $d(0)=1$，代入 $x^2-4x+1=0$ 给 $d(x_m)=2/7$。因此 $d$ 连续严格递减，给所述唯一参数；并有精确夹界

$$
\frac12<\frac{73178097881}{84846680125}
=d(11/100)<d_b<d(1/10)=\frac{81133}{91297}<1.
\tag{III.3.7}
$$

其次验证中心正性及逆矩阵。因为 $0<x\le x_m<1/2$、$a_x>0$、$\Delta>0$、$a_x+b_x=1-2x-x^2>0$，所以 $T_x\succ0$。而

$$
\begin{gathered}
Q=\frac{(1+x^2)D_6(x)}{(x^2+2x-1)^2},\qquad
L=\frac{(1+x^2)(5x^2-1)}{x^2+2x-1},\\
\kappa=\frac{(5x^2-1)(x^2+2x-1)}{D_6(x)},\qquad
c=-\frac{8x(x-1)(2x-1)(x^2+2x-1)}{3D_6(x)}.
\end{gathered}
\tag{III.3.8}
$$

$\kappa>0$，且正特征值至少有两个，故 $L^2>Q$、$c>0$。$\operatorname{Tr}\sigma_x=\kappa L-3c=1$。令 $p_x=c/\kappa$，则

$$
\begin{aligned}
p_x&=-\frac{8x(x-1)(2x-1)}{3(5x^2-1)},\\
\det((T_x)_{ah}-p_xI_2)
&=-\frac{2x(2x-1)F_6(x)}{9(5x^2-1)^2},\\
\operatorname{Tr}((T_x)_{ah}-p_xI_2)
&=-\frac{J_4(x)}{3(5x^2-1)}>0,\\
g_x-p_x&=
\frac{2x(2x-1)G_4(x)}{3(5x^2-1)(x^2+2x-1)}>0.
\end{aligned}
\tag{III.3.9}
$$

在 $[x_0,x_m]$ 上，$5x^2-1<0$，故行列式非负，其余两项严格为正；实对称二阶块的两个特征值遂均非负。$x>x_0$ 时行列式严格为正；$x=x_0$ 时恰一个 $ah$ 特征值为零，另一个及 $g$ 特征值仍严格为正。这证明密度正性及准确秩，并没有在分支相遇处预设全秩。

二阶逆矩阵还给

$$
T_x^{-1}=\lambda_0I+\mu_0aa^\dagger+\nu_0C,\qquad
\lambda_0=\frac{1-2x-x^2}{\Delta},\quad
\mu_0=\frac{-1+4x-x^2}{\Delta},\quad
\nu_0=\frac{2x^2}{\Delta}.
\tag{III.3.10}
$$

$\mu_0\le0$ 恰在此处的 $x\le x_m$；在 $x=x_m$ 为零，在 $0<x<x_m$ 时严格为负。设

$$
S=\sigma_x+cI=\kappa T_x\succ0,\qquad
Z=S^{-1}=\lambda I+\mu aa^\dagger+\nu C
=T_x^{-1}/\kappa.
\tag{III.3.11}
$$

这里 $\lambda=\lambda_0/\kappa,\mu=\mu_0/\kappa,\nu=\nu_0/\kappa$。

为了同时得到矩条件及下界，置 $M=T_x^2/Q$、$u=M_{hh}$。矩阵乘法给

$$
M_{aa}=d(x),\qquad
u=\frac{b_x^2+h_x^2}{Q}>0,\qquad
M_{ah}=\frac{b_x(a_x+h_x)}Q=-\frac u2,\qquad
M_{gg}=\frac{g_x^2}Q=1-d-u>0.
\tag{III.3.12}
$$

$ah$ 主块严格正，故 $du-u^2/4>0$，即 $u<4d$。所以 $M=M_d(u)$，且 (III.1.7) 成立。原两个矩为

$$
\operatorname{Tr}(CM)=d-u+u=d,\qquad
16\operatorname{Tr}(EM)=d-3u+9u+6(1-d-u)=6-5d.
\tag{III.3.13}
$$

因此 $M$ 本身可取忠实分解 $A=M,D=0$。又

$$
\operatorname{Tr}(ZM)=\frac{\operatorname{Tr}T_x}{\kappa Q}=1,
\qquad \lambda+(\mu+\nu)d=1.
\tag{III.3.14}
$$

任意复 $\rho\in\mathcal K_d$ 都满足 $\rho_{aa}\ge d$，故

$$
\operatorname{Tr}(Z\rho)
=1+\mu(\rho_{aa}-d)\le1.
\tag{III.3.15}
$$

定理 2.1 证明内的逆球步骤于是给整个复完整纤维的上界 $2c$。

下面建立匹配下界；这个原接触构造也用于大参数分支。由 (III.1.8)，

$$
|x_\epsilon|^2=u,\quad
\Re x_\epsilon=-\frac{u}{2\sqrt d},\quad
|b_\epsilon|^2=d+6u>0,\quad
\Re(b_\epsilon\overline{y_{\epsilon,\delta}})=0.
\tag{III.3.16}
$$

所以四个 $\psi_{\epsilon,\delta}$ 单位化，且各自满足

$$
|\langle a,\psi_{\epsilon,\delta}\rangle|^2=d,\qquad
\psi_{\epsilon,\delta}^\dagger C\psi_{\epsilon,\delta}
=|\sqrt d+x_\epsilon|^2=d,\qquad
16\psi_{\epsilon,\delta}^\dagger E\psi_{\epsilon,\delta}
=|b_\epsilon+\sqrt6y_{\epsilon,\delta}|^2=6-5d.
\tag{III.3.17}
$$

取 $A=\rho_{\epsilon,\delta},D=0$，即为四个原相容世界；(III.1.9) 的物理纯提升及 (III.1.6) 给四个原 CPTP 通道。先对 $\delta$ 平均消去 $g$ 相干，再对 $\epsilon$ 平均消去 $ah$ 的虚部，得到

$$
\frac14\sum_{\epsilon,\delta}\rho_{\epsilon,\delta}=M_d(u).
\tag{III.3.18}
$$

对当前 $Z$，以及一般任何满足 $Z=(\sigma+cI)^{-1}$、$Z=\lambda I+\mu aa^\dagger+\nu C$、$\lambda+(\mu+\nu)d=1$ 的正逆矩阵，这四个原态都有 $\psi_j^\dagger Z\psi_j=1$。下标 $j$ 在此遍历四对符号。置 $f_j=Z\psi_j\ne0$，则

$$
(\rho_j-\sigma)f_j=cf_j.
\tag{III.3.19}
$$

若它们的逆变换协方差满足

$$
\mathcal Q:=ZM_d(u)Z=\eta I-W,\qquad
W\succeq0,\qquad W\sigma=0,
\tag{III.3.20}
$$

那么对任意密度中心 $\sigma'$，包括复中心及集合外中心，

$$
\begin{aligned}
\frac14\sum_j\left[f_j^\dagger(\rho_j-\sigma')f_j-c\|f_j\|^2\right]
&=\operatorname{Tr}(\mathcal Q(\sigma-\sigma'))\\
&=\operatorname{Tr}(W\sigma')\ge0.
\end{aligned}
\tag{III.3.21}
$$

至少一个原接触的 Rayleigh 商不小于 $c$。由于 $\rho_j-\sigma'$ 迹零，其迹范数至少为 $2c$。这一步不要求 $\sigma'$ 的谱或 $\mathcal Q$ 的余量严格为正，也不要求中心属于 $\mathcal K_d$。

在本分支中直接相乘为

$$
ZMZ=\frac1{\kappa^2Q}I,
\tag{III.3.22}
$$

故可取 $\eta=1/(\kappa^2Q)$、$W=0$，得到所需匹配下界，包括 $x=x_0$ 的奇异密度中心。结合 (III.1.6) 即证 (III.3.3)。将 $x=x_m$ 代入 (III.3.8) 给 (III.3.4)。∎

## 4. 大参数的单下限模分支

**定义 4.1（正根及谱中心）。** 固定 $d_b<d<1$，置 $\beta=1-d$。对 $0<u<\beta$ 定义

$$
\begin{gathered}
R=\sqrt{(d-u)^2+u^2},\qquad
m_+=\frac{d+u+R}{2},\qquad
m_-=\frac{d+u-R}{2},\qquad m_g=\beta-u,\\
z=m_-+2\sqrt{m_+m_g},\qquad
c(u)=\frac{z+\sqrt{z^2+8m_-}}4,\\
K(u)=\frac{1+2c(u)}{\sqrt{m_+}+\sqrt{m_g}},\qquad
A(u)=K(u)\sqrt{m_+},\qquad B(u)=K(u)\sqrt{m_g}.
\end{gathered}
\tag{III.4.1}
$$

这里 $R$ 是标量，$B(u)$ 是标量，均不改变定义 1.1 中同字母的通道或等距嵌入。所有平方根取非负实分支；在开区间内 $m_+,m_-,m_g$ 均严格为正。令

$$
F_d(u)=\frac1{c(u)}+
\left(\frac1{A(u)}-\frac1{c(u)}\right)
\frac{1-(d-2u)/R}{2}-\frac1{B(u)}.
\tag{III.4.2}
$$

所选根必须满足

$$
F_d(u)=0,\qquad A(u)>c(u),\qquad B(u)>c(u),\qquad
c(u)\ge K(u)\sqrt{m_-}.
\tag{III.4.3}
$$

定义 $M_d(u)$ 的正交谱投影

$$
\begin{gathered}
\Pi_+=\begin{pmatrix}
\frac{1+(d-u)/R}{2}&-\frac{u}{2R}&0\\
-\frac{u}{2R}&\frac{1-(d-u)/R}{2}&0\\
0&0&0
\end{pmatrix},\qquad
\Pi_g=gg^\dagger,\qquad \Pi_-=I-\Pi_+-\Pi_g,\\
\sigma=(A-c)\Pi_++(B-c)\Pi_g.
\end{gathered}
\tag{III.4.4}
$$

由于 $d>d_b>1/2$ 及 $u<\beta<d$，上述三个特征值中 $m_+$ 严格大于 $m_-$ 和 $m_g$，$R>0$，投影没有退化歧义。

**定理 4.2（大参数的唯一可容许根及精确原通道半径）。** 对每个 $d_b<d<1$，(III.4.3) 恰有一个可容许根 $u\in(0,1-d)$；其最后一个不等式实际上严格成立。相应 (III.4.4) 是秩二密度矩阵，核为 $\operatorname{ran}\Pi_-$，并满足

$$
r(d)=2c(u).
\tag{III.4.5}
$$

$R_\sigma$ 是达到该值的共同 CPTP 重建。该分支在 $d\downarrow d_b$ 时与定理 3.2 的中心及半径连续相接；相遇处允许 $c=K\sqrt{m_-}$，密度中心仍为秩二。

**证明。** 先证明全局根选择，再建立原问题的上下证书。以下逆矩阵凸性及标量下限分配是成熟凸优化工具在 $M_d(u)$ 上的消费；凸最优化条件的一般充分性背景可参见 Boyd–Vandenberghe, [*Convex Optimization*](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf) §5.5.3。这里直接给出所需的矩阵凸性、全局充分性、端点和严格性论证。

对任意固定 $c>0$，考虑

$$
G(c,u)=\min_{S\succeq cI,\ \operatorname{Tr}S=1+3c}
\operatorname{Tr}(M_d(u)S^{-1}),\qquad 0\le u\le\beta.
\tag{III.4.6}
$$

可行集等价于 $S=\sigma+cI$，$\sigma$ 为任意密度矩阵；它紧且不依赖 $u$。因为 $d\ge1/2$，$0<u<\beta$ 蕴含 $u<4d$，故 $M_d(u)\succ0$。在两个端点，$M_d(u)$ 为秩二且半正定。

对任意 Hermitian 方向 $H$，沿正定锥的二阶导数为

$$
\frac{d^2}{ds^2}\operatorname{Tr}(M(S+sH)^{-1})\bigg|_{s=0}
=2\operatorname{Tr}(XY^2),\qquad
X=S^{-1/2}MS^{-1/2},\quad Y=S^{-1/2}HS^{-1/2}.
\tag{III.4.7}
$$

$M\succeq0$ 时该值非负；$M\succ0,H\ne0$ 时严格为正。因此目标凸，内点 $u$ 的最小矩阵唯一。任一最小矩阵的酉轨道都是可行的；对 $S\mapsto e^{isH}Se^{-isH}$ 求一阶导数得 $[M,S^{-1}]=0$，即 $[M,S]=0$。所以在 $M$ 的本征基中，问题化为

$$
\min\sum_i\frac{m_i}{s_i},\qquad s_i\ge c,\quad \sum_i s_i=1+3c.
\tag{III.4.8}
$$

标量一阶条件给唯一分配

$$
s_i=\max\{c,K\sqrt{m_i}\},\qquad
\sum_i\max\{c,K\sqrt{m_i}\}=1+3c.
\tag{III.4.9}
$$

右端比三个下限之和大一，故至少有一个自由模，$K>0$ 由迹唯一确定。零质量模必须在下限：若给它多余迹，可以把该迹移向一个正质量模而严格降低目标。正质量模上的标量严格凸性给唯一分配；相同 $m_i$ 给相同 $s_i$，所以即使 $M$ 有重特征值，所得矩阵也唯一。这同时处理两个秩二端点。

也可直接检验 (III.4.9) 的全局充分性。令 $\eta=1/K^2$，在下限模上取 $W_i=\eta-m_i/c^2\ge0$，自由模上取 $W_i=0$。于是

$$
-S^{-1}MS^{-1}=-\eta I+W,\qquad
W\succeq0,\qquad W(S-cI)=0.
\tag{III.4.10}
$$

对任意其他可行 $S'$，凸性给

$$
\begin{aligned}
\operatorname{Tr}(M(S')^{-1})-\operatorname{Tr}(MS^{-1})
&\ge\operatorname{Tr}((-\eta I+W)(S'-S))\\
&=\operatorname{Tr}(W(S'-cI))\ge0.
\end{aligned}
\tag{III.4.11}
$$

所以这不是只给必要条件的驻点计算。标量凸余量亦有精确形式

$$
\frac m{s'}-\frac m{s}+\frac{m(s'-s)}{s^2}
=\frac{m(s'-s)^2}{s's^2}\ge0,
\tag{III.4.12}
$$

与上述矩阵凸性相容。

下面说明对 $u$ 的严格凹性。由于 $M_d(u)$ 仿射依赖 $u$，$G(c,u)$ 是仿射函数族的下确界，因而凹。若在两个不同的内部参数之间有凹性等号，中间点的唯一最小矩阵也同时最小化两个端点的目标。这个共同矩阵 $S$ 必须同时与

$$
M_d(0)=\operatorname{diag}(d,0,\beta),\qquad
M'_d=\begin{pmatrix}0&-1/2&0\\-1/2&1&0\\0&0&-1\end{pmatrix}
\tag{III.4.13}
$$

对易。$d>1/2$ 时第一个矩阵的三个特征值不同，所以 $S$ 先为对角，第二个对易式再给 $S_{aa}=S_{hh}$。$d=1/2$ 时第一个对易式还允许 $ag$ 条目 $z$，但第二个对易式的 $hg$ 条目为 $z/2$，迫使 $z=0$；其 $ah$ 条目仍迫使两个对角值相等。因此两种情形都只有

$$
S=\operatorname{diag}(s,s,t).
\tag{III.4.14}
$$

若 $s>c$，$ah$ 块内任意小的无迹 Hermitian 变分均可行；自由模的一阶条件要求该块的 $M$ 是标量块，但它的 $ah=-u/2\ne0$，矛盾。若 $s=c$，则 $t=1+c$，所有额外迹都在 $g$ 模。将少量迹从 $g$ 转向 $ah$ 块的最大特征向量，其目标方向导数为

$$
-\frac{m_+}{c^2}+\frac{m_g}{(1+c)^2}<0,
\tag{III.4.15}
$$

因为 $m_+\ge d>\beta-u=m_g$。这也矛盾。所以 $G(c,u)$ 在内部严格凹；连续凹性因而排除包括端点在内的任何非平凡平顶区间。

以固定密度变量 $S=\sigma+cI$ 表示 (III.4.6)，目标在 $c>0$、$0\le u\le\beta$ 和紧密度集上连续，故 $G$ 连续。最小矩阵的唯一性和紧性还给其连续依赖性：任意收敛参数序列的最小矩阵子列极限必最小化极限目标，只能等于唯一极限最小矩阵。

对 $c_2>c_1>0$，在同一密度 $\sigma$ 的谱上有

$$
(\sigma+c_1I)^{-1}-(\sigma+c_2I)^{-1}
\succeq \frac{c_2-c_1}{(1+c_1)(1+c_2)}I.
\tag{III.4.16}
$$

因为 $0\preceq\sigma\preceq I$。在 $c_1$ 的最小密度上比较得统一严格下降

$$
G(c_2,u)\le G(c_1,u)
-\frac{c_2-c_1}{(1+c_1)(1+c_2)}.
\tag{III.4.17}
$$

所以

$$
H(c)=\max_{0\le u\le\beta}G(c,u)
\tag{III.4.18}
$$

连续且严格下降。

置 $c_0=\sqrt{d\beta}$、$c_1=\sqrt\beta$。在 $u=0,c=c_0$ 时，(III.4.9) 的唯一最小矩阵为

$$
S_0=\operatorname{diag}(d+c_0,c_0,\beta+c_0),\qquad
G(c_0,0)=\frac d{d+c_0}+\frac\beta{\beta+c_0}=1.
\tag{III.4.19}
$$

这里两个正质量模的比例同为 $\sqrt d+\sqrt\beta$，零质量模在下限。因此 $H(c_0)\ge1$。另一方面，$S=aa^\dagger+c_1I$ 在所有 $u$ 都可行，且

$$
\operatorname{Tr}(M_d(u)S^{-1})
=\frac d{1+c_1}+\frac\beta{c_1}=1.
\tag{III.4.20}
$$

故 $H(c_1)\le1$。连续性和严格下降给唯一

$$
c_*\in[c_0,c_1],\qquad H(c_*)=1.
\tag{III.4.21}
$$

还须证明最大点在内部，而非只假定一个驻点。记唯一最小矩阵的逆为 $Z(c,u)$。因目标对 $u$ 仿射，两个最小点之间的比较给，对于 $v>0$，

$$
v\operatorname{Tr}(M'_dZ(c,u+v))
\le G(c,u+v)-G(c,u)
\le v\operatorname{Tr}(M'_dZ(c,u)).
\tag{III.4.22}
$$

由最小矩阵连续性，$u$ 导数在内部及端点的单侧均为

$$
G_u=\operatorname{Tr}(M'_dZ)=Z_{hh}-\Re Z_{ah}-Z_{gg}.
\tag{III.4.23}
$$

在 $u=0$，$h$ 模是零质量下限模，$Z_{hh}=1/c$、$Z_{ah}=0$。对于 $c_0\le c\le c_1$，$g$ 模自由。事实上它的下限阈值为

$$
\frac{\sqrt\beta}{\sqrt d-\sqrt\beta}>\sqrt\beta=c_1
\quad(d>1/2),
\tag{III.4.24}
$$

由 $K\sqrt\beta>c$ 及 $K=(1+2c)/(\sqrt d+\sqrt\beta)$ 等价得到；$d=1/2$ 时分母为零，两个正模始终同时自由。因此 $G_u(c,0)=1/c-1/S_g>0$。

在 $u=\beta$，零质量 $g$ 模在下限，$Z_{gg}=1/c$。最大模必自由，且其 $S_+$ 严格大于 $S_-$；又 $\Pi_{+,ah}=-u/(2R)<0$，故

$$
Z_{ah}=\left(\frac1{S_+}-\frac1{S_-}\right)\frac{-u}{2R}>0,
\qquad Z_{hh}\le\frac1c.
\tag{III.4.25}
$$

于是 $G_u(c,\beta)<0$。严格凹性连同这两个单侧导数表明，在 $c=c_*$ 时存在唯一内部最大点 $u_*$，且 $G_u(c_*,u_*)=0$。这给出了一个全局存在性证明。

现在确定恰好哪个模在下限。对任意内部 $u$，$m_+>m_g,m_-$，且至少一个模自由，故加模必自由。若 $g$ 模在下限，则与 (III.4.25) 相同的计算仍给 $Z_{ah}>0$、$Z_{hh}\le1/c$、$Z_{gg}=1/c$，从而 $G_u<0$；它不能出现在内部驻点。所以加模和 $g$ 模均自由。

假设减模也不受下限约束，包括恰好等于自由分配值的边界情形。则无下限解为

$$
S=\frac{1+3c}{\operatorname{Tr}\sqrt M}\sqrt M,\qquad
G(c,u)=\frac{(\operatorname{Tr}\sqrt M)^2}{1+3c}.
\tag{III.4.26}
$$

函数 $u\mapsto(\operatorname{Tr}\sqrt{M_d(u)})^2$ 在内部严格凹。为见此，可将它写为 $\min_{S\succ0,\operatorname{Tr}S=1}\operatorname{Tr}(MS^{-1})$；唯一最小矩阵为 $\sqrt M/\operatorname{Tr}\sqrt M$。凹性等号会给两个不同 $u$ 的同一归一化平方根，平方后两者 $M$ 成正比例；因 $\operatorname{Tr}M=1$，比例只能为一，矛盾。

对于当前 $d>d_b$，定理 3.2 证明的严格单调性给唯一 $x\in(0,x_0)$ 满足 $d=d(x)$。仍有 $T_x\succ0$，且 $M=T_x^2/Q=M_d(u_x)$ 在内部。由 (III.3.10)，$T_x^{-1}$ 属于 $I,aa^\dagger,C$ 的实线性张成，而 $M'_d$ 对这三个矩阵的迹配对均为零。因此无下限目标在 $u_x$ 的导数为零；严格凹性说明它是唯一驻点及全局最大点。

若无下限驻点还满足 $G=1$，(III.4.26) 就迫使

$$
1+3c=\frac{L^2}{Q},\qquad S=\frac LQ T_x=\kappa T_x.
\tag{III.4.27}
$$

但 $F_6(x)<0$ 在 $(0,x_0)$，(III.3.9) 的行列式严格为负，所以 $\sigma=S-cI$ 的 $ah$ 块不定。这不可能满足 $S\succeq cI$。因此减模确在下限，而加模与 $g$ 模自由。在 $d>d_b$，减模的下限不等式必须严格；若取等号，三个模又同时等于无下限分配值，产生同一矛盾。

现在最小矩阵必为

$$
S=A\Pi_++c\Pi_-+B\Pi_g,\qquad
A=K\sqrt{m_+}>c,\quad B=K\sqrt{m_g}>c,\quad
c>K\sqrt{m_-},\quad A+B=1+2c.
\tag{III.4.28}
$$

$G=1$ 等价于

$$
\frac{m_-}{c}+\frac{(\sqrt{m_+}+\sqrt{m_g})^2}{1+2c}=1
\quad\Longleftrightarrow\quad
2c^2-(m_-+2\sqrt{m_+m_g})c-m_-=0.
\tag{III.4.29}
$$

$m_->0$，所以此二次式只有一个正根，正是 (III.4.1) 的 $c(u)$。而

$$
Z=\frac1c(\Pi_++\Pi_-)+
\left(\frac1A-\frac1c\right)\Pi_++\frac1B\Pi_g
\tag{III.4.30}
$$

给

$$
G_u=\frac1c+\left(\frac1A-\frac1c\right)
\frac{1-(d-2u)/R}{2}-\frac1B=F_d(u).
\tag{III.4.31}
$$

前面构造的 $(c_*,u_*)$ 因此产生 (III.4.3) 的可容许根。

反过来，任何满足 (III.4.3) 的根，依 (III.4.28) 都给可行的下限分配矩阵；(III.4.10)–(III.4.11) 使它成为全局最小矩阵。二次式给 $G=1$，根方程给 $G_u=0$。严格凹性于是给 $H(c)=1$，(III.4.17) 迫使 $c=c_*$，再由严格凹性给 $u=u_*$。所以没有第二个可容许根；只求出一个形式驻点或若干取样根并不足以替代这一步。

接着证明这个全局下限解确实解决完整原状态问题。由 $F_d(u)=0$，

$$
Z_{hh}-Z_{ah}=Z_{gg},\qquad
Z=\lambda I+\mu aa^\dagger+\nu C,
\quad \lambda=1/B,\quad \nu=Z_{ah},
\tag{III.4.32}
$$

且

$$
\mu=Z_{aa}-Z_{hh}
=\left(\frac1A-\frac1c\right)\frac{d-u}{R}<0.
\tag{III.4.33}
$$

这里 $A>c$、$d-u>0$。矩阵 $M_d(u)$ 具有 (III.3.13) 的原矩，并由 (III.4.29) 满足 $\operatorname{Tr}(ZM)=1$，故

$$
\lambda+(\mu+\nu)d=1,\qquad
\operatorname{Tr}(Z\rho)=1+\mu(\rho_{aa}-d)\le1
\quad(\rho\in\mathcal K_d).
\tag{III.4.34}
$$

此不等式使用完整提升必有的 $\rho_{aa}\ge d$，对全部复混合态成立。定理 2.1 证明内的逆球步骤给 $\|\rho-\sigma\|_1\le2c$，其中 $\sigma=S-cI$ 正是 (III.4.4)。它的两个正特征值为 $A-c,B-c$，和为一，故准确秩为二。

对于下界，$0<u<\beta<d<4d$，所以定义 1.3 的四个实际原纯态及其物理提升全部可用。它们的均值为 $M_d(u)$。本征分解直接给

$$
\begin{gathered}
ZM_d(u)Z=\eta\Pi_++\xi\Pi_-+\eta\Pi_g
=\eta I-W,\\
\eta=1/K^2,\qquad \xi=m_-/c^2<\eta,\qquad
W=(\eta-\xi)\Pi_-\succeq0,\qquad W\sigma=0.
\end{gathered}
\tag{III.4.35}
$$

因此 (III.3.19)–(III.3.21) 的 Rayleigh 下界直接覆盖任意密度中心。再用 (III.1.6)，便得原全部 CPTP 重建的下界 $2c$，与完整上界匹配。

最后处理分支相遇。$x=x_0$ 时，(III.3.9) 说明 $\sigma_{x_0}$ 恰有一个零 $ah$ 特征值，另一个及 $g$ 特征值为正。$S=\kappa T_{x_0}$ 始终正定。写 $M=T_{x_0}^2/Q$ 的谱值，则

$$
S_+=K\sqrt{m_+}>c,\qquad
S_g=K\sqrt{m_g}>c,\qquad
S_-=c=K\sqrt{m_-},\qquad K=\kappa\sqrt Q.
\tag{III.4.36}
$$

所以它也满足 (III.4.9) 的全局下限条件、$G=1$ 及 $G_u=0$；(III.3.22) 给协方差余量 $W=0$。$d_b>1/2$，故前面的严格凹性和 $H$ 的唯一根在 $d=d_b$ 仍适用，唯一识别出此相遇解。

为得到连续相接，把 $u=\beta v$ 改写为 $0\le v\le1$ 的固定紧区间。$G$ 及 $H$ 对 $(d,c)$ 连续，在 $d_b$ 邻域根由正下界 $\sqrt{d(1-d)}$ 和上界 $\sqrt{1-d}$ 夹住。任意 $d\downarrow d_b$ 的根及最大点子列极限必满足极限的 $H=1$ 及最大化条件；两者的唯一性迫使极限为 (III.4.36)。唯一最小矩阵的连续性再给中心与半径的相接。这里从未对奇异密度 $\sigma_{x_0}$ 求逆，始终求逆的是 $\sigma+cI\succ0$。∎

## 5. 一个有理参数的分支应用

**命题 5.1（$d=49/92$ 的精确原风险）。** 取 $d=49/92$，则定理 3.2 的参数为 $x=1/5$，且

$$
\sigma=\begin{pmatrix}
14/23&-7/46&0\\-7/46&7/46&0\\0&0&11/46
\end{pmatrix},\qquad
c=\frac{14}{23},\qquad r(49/92)=\frac{28}{23}.
\tag{III.5.1}
$$

**证明。** $x_0<11/100<1/5<x_m$，因此这是中分支的应用。代入 (III.3.1)–(III.3.2) 即得 (III.5.1)，其中密度矩阵迹一，$ah$ 主块行列式为 $147/2116>0$，$gg=11/46>0$。带半径平移的有理矩阵及其逆为

$$
\begin{gathered}
S=\sigma+cI=\frac1{46}
\begin{pmatrix}56&-7&0\\-7&35&0\\0&0&39\end{pmatrix},\\
Z=S^{-1}=\begin{pmatrix}230/273&46/273&0\\46/273&368/273&0\\0&0&46/39\end{pmatrix}
=\frac{46}{39}I-\frac{46}{91}aa^\dagger+\frac{46}{273}C,
\qquad SZ=I.
\end{gathered}
\tag{III.5.2}
$$

原矩及 $\rho_{aa}\ge49/92$ 给

$$
\operatorname{Tr}(Z\rho)=1-\frac{46}{91}
\left(\rho_{aa}-\frac{49}{92}\right)\le1
\quad(\rho\in\mathcal K_{49/92}).
\tag{III.5.3}
$$

这已经是全部复混合态的上证书。取

$$
u=\frac{49}{230},\qquad
M=M_{49/92}(u)=\begin{pmatrix}
49/92&-49/460&0\\-49/460&49/230&0\\0&0&117/460
\end{pmatrix}.
\tag{III.5.4}
$$

则 $0<u<\min\{1-d,4d\}$，且

$$
M_{aa}=\frac{49}{92},\qquad
\operatorname{Tr}(CM)=\frac{49}{92},\qquad
\operatorname{Tr}(EM)=\frac{307}{1472}
=\frac{6-5(49/92)}{16},\qquad
\operatorname{Tr}(ZM)=1,\qquad ZMZ=\frac{23}{65}I.
\tag{III.5.5}
$$

定义 1.3 给出四个具有该均值的原复纯态及原 CPTP 提升。(III.3.21) 取 $W=0$ 给所有密度中心的匹配下界，再经 (III.1.6) 给原通道的精确值。此有理式是分支定理的具体应用，不构成另一个通用中心定理。∎

## 6. 保留的中央问题与物理假设

**定义 6.1（已确定参数域及未决关系）。** 在 $(0,d_s]\cup[2/7,1)$ 上，本卷给出的精确原风险为

$$
r(d)=\begin{cases}
2\sqrt{5d(1-5d)},&0<d\le d_s,\\
2(L^2-Q)/(3Q),&2/7\le d\le d_b,\quad x\in[x_0,x_m],\ d=d(x),\\
2c(u),&d_b<d<1,\quad u\text{ 为 (III.4.3) 的唯一可容许根}.
\end{cases}
\tag{III.6.1}
$$

原问题仍要求对每个 $0<d<1$ 求 (III.1.1) 的精确值；未决域是

$$
d_s<d<\frac27.
\tag{III.6.2}
$$

在该域尚需选出实际达到的密度 $\sigma_*(d)$ 及 $c_*(d)$，证明

$$
\sigma_*(d)-c_*(d)I\preceq\rho\preceq\sigma_*(d)+c_*(d)I
\quad\text{对每个复 }\rho\in\mathcal K_d,
\tag{III.6.3}
$$

并给出对所有密度中心的匹配半径下界 $2c_*(d)$。母卷定理 36.4 允许把包含检验等价地放在全部 $\mathsf P\cup\mathsf R_0\cup\mathsf R_+$ 上，却不允许丢弃两个混合极端层。$d_s$ 不带最大性断言；定理 3.2 的参数方程也不在中央域选出一个未经证明的中心。

**定义 6.2（中央问题所保留的混合活动约束）。** 中央问题保留母卷定理 37.2–37.4 的全部已知约束。它们在 $d_0=5/61$ 给出的完整纯截面及纯族半径为 $60/61$、密度中心唯一为

$$
\bar\sigma=\frac{25}{61}ww^\dagger+\frac{36}{61}gg^\dagger,
\tag{III.6.4}
$$

但完整原风险满足 $r(5/61)>60/61$。每个完整最优密度中心及每个完整最优共同 CPTP 重建都具有活动混合原世界，其后继满足 $\rho_{aa}>d_0$。此参数严格位于 (III.6.2)：$d_s<5/61$ 等价于 $30500<36665+4140\sqrt2$，而 $5/61<2/7$ 等价于 $35<122$。

这些供应的作用分别是：纯接触对将达到纯族半径的中心唯一固定为 $\bar\sigma$；母卷定理 37.3 的忠实混合世界排除该固定中心覆盖完整集合，紧性给严格全局差；母卷定理 37.4 的中心扰动论证给活动混合态的必要性。固定 $\bar\sigma$ 的某个加性超额不是优化后 $r(5/61)$ 的同量加性下界。中央问题必须同时处理该混合活动条件与 (III.6.3)，而不是再次求纯族中心。

**定义 6.3（量子结构与取得性边界）。** 本卷保留母卷定义 38.3 的模型假设：复 Hilbert 空间、密度矩阵、CPTP 动力学与组合、Born 效果配对，以及已给的原全深度算子数据。半径分支刻画这些假设下相容预测的最坏风险，不给额外原生操作、效果、标签历史、返回环境、副本或参考控制的取得程序。与中央最小最大关系并存的物理问题仍是：哪些实际取得的关系数据能够控制隐藏的 $\rho_{aa}$ 及母卷 (37.14) 的实相干，同时保持原擦除标签菜单及共同来源条件？本卷的条件数学不把量子结构或该数据取得性作为结论。

## 追加锚（本行以下为增补区）

## 7. 中央域的实际混合态与严格优化间隙

**定义 7.1（参数、原模型与复数范围）。** 以下沿用定义 1.1–1.2 的原仪器、固定平面 $N$、完整复纤维 $\mathcal K_d$ 及不除以二的风险 $r(d)$。母卷定理 35.4–35.5 的忠实原域提升、任意共同 CPTP 重建的压缩下界及全部有限未触动参考的等号直接适用。§§2–5 和 (III.6.1) 的既有分支直接引用，不重新推导。中央区间仍为 (III.6.2)。本节固定

$$
d=\frac5{61},\qquad \beta=\frac{56}{61},\qquad
\lambda=\frac1{1000},\qquad t=\sqrt d,\qquad \chi=\sqrt2.
\tag{III.7.1}
$$

$t$ 是原前驱参数，$\lambda$ 是混合权重；后继的正超额另记为 $s=\rho_{aa}-d$。三者不作同一坐标使用。仍令 $\alpha=(2+\chi)/\sqrt{12}$、$\gamma=(2-\chi)/\sqrt{12}$，所以

$$
k=\alpha a+\gamma h,\qquad \ell=-\gamma a+\alpha h,
\qquad N=\ell^\perp=\operatorname{span}_{\mathbb C}\{k,g\}.
$$

定义下列实数和向量：

$$
\begin{gathered}
Z_2=\frac{2640+1440\chi}{32269},\qquad
N_2=Z_2+\beta=\frac{32264+1440\chi}{32269},\qquad
\zeta=\sqrt{Z_2}=\frac{6\sqrt d(5\alpha+\gamma)}{23},\\
\nu=\frac{\zeta k+\mathrm i\sqrt\beta\,g}{\sqrt{N_2}},\qquad
\mu=\frac{4Z_2}{3N_2},\qquad S=\frac{244+16\chi}{253},\\
x=\sqrt{d-\lambda\mu}-\sqrt d,\qquad b_\lambda=\sqrt d+3x,\\
u=\frac{\lambda(3+2\chi)\mu}{2\sqrt6\,b_\lambda},\qquad
v=\sqrt{\beta-\lambda-x^2-u^2},\\
\psi=\sqrt d\,a+xh+(u+\mathrm iv)g,\qquad
A=\psi\psi^\dagger,\quad D=\lambda\nu\nu^\dagger,\quad \rho_\lambda=A+D.
\end{gathered}
\tag{III.7.2}
$$

这里 $u$ 为标量，$\nu$ 为单位向量；所有平方根取非负根。此式是母卷 (37.5) 在混合权重 $\lambda$ 的取值，不改变其原平面。正性及分母非零由下面的有理界给出。

**命题 7.2（显式实际 $\mathsf R_+$ 态及原前驱）。** (III.7.2) 定义了原完整 $\mathcal K_{5/61}$ 内的秩二极端态，且

$$
s=\frac{\lambda\alpha^2 Z_2}{N_2}>0,\qquad
\det(\rho_{\lambda,\{a,h\}})
=\frac{\lambda Z_2}{N_2}(\gamma\sqrt d-\alpha x)^2>0,
\qquad \det\rho_\lambda=\det B_d(\rho_\lambda)=0.
\tag{III.7.3}
$$

它有原域 $M_3(\mathbb C)\to M_5(\mathbb C)$ 的 CPTP 前驱，保持全部原深度效果算子数据。这里没有断言它是未知最优中心的接触态。

证明。先给出足够的精确有理界：

$$
\begin{gathered}
\frac{1414213}{10^6}<\chi<\frac{1414214}{10^6},\qquad
\sqrt d>\frac{286299}{10^6},\qquad \sqrt6>\frac{2449489}{10^6},\\
0<\mu<\frac{181785}{10^6},\qquad
-\frac{318}{10^6}<x<0,\qquad b_\lambda>\frac{285345}{10^6},\\
0<u<\frac{758}{10^6},\qquad v>\frac{9576179}{10^7}.
\end{gathered}
\tag{III.7.4}
$$

首行来自正有理数的平方比较。为固定严格裕量，四个平方差分别为

$$
\begin{gathered}
2-\left(\frac{1414213}{10^6}\right)^2=\frac{1590631}{10^{12}},\qquad
\left(\frac{1414214}{10^6}\right)^2-2=\frac{309449}{250000000000},\\
d-\left(\frac{286299}{10^6}\right)^2=\frac{5838539}{61000000000000},\qquad
6-\left(\frac{2449489}{10^6}\right)^2=\frac{3638879}{10^{12}}.
\end{gathered}
$$

函数 $4(2640+1440z)/(3(32264+1440z))$ 在本区间严格递增；代入 $z=1414214/10^6$，其值与 $181785/10^6$ 的差为 $1761113/3062541800000>0$。特别地 $d-\lambda\mu>0$。置 $a_0=286299/10^6$、$\delta_0=318/10^6$，则

$$
2a_0\delta_0-\delta_0^2-\frac1{1000}\frac{181785}{10^6}
=\frac{5001}{25000000000}>0.
$$

因 $\sqrt d>\delta_0$，这说明 $d-\lambda\mu>(\sqrt d-\delta_0)^2$，给出 $x>-\delta_0$ 及 $b_\lambda>285345/10^6$。代入 $u$ 的正表达式得到

$$
u<\frac{17658679733}{23298314623500}<\frac{758}{10^6},\qquad
\frac{758}{10^6}-\frac{17658679733}{23298314623500}
=\frac{1442751613}{23298314623500000}>0.
$$

最后

$$
\beta-\frac1{1000}-\left(\frac{318}{10^6}\right)^2
-\left(\frac{758}{10^6}\right)^2-\left(\frac{9576179}{10^7}\right)^2
=\frac{419660699}{6100000000000000}>0,
$$

所以 $v$ 存在且满足 (III.7.4)。这些比较也排除所有零分母。

由构造 $A,D\succeq0$、$\operatorname{ran}D\subseteq N$，并有

$$
\|\nu\|^2=1,\qquad \|\psi\|^2=1-\lambda,\qquad
\operatorname{Tr}\rho_\lambda=1,\qquad a^\dagger Aa=d.
$$

$\nu^\dagger C\nu=\mu$，故

$$
\operatorname{Tr}(C\rho_\lambda)=(\sqrt d+x)^2+\lambda\mu=d.
$$

用定义 1.2 的原 $E$，直接展开给

$$
16\nu^\dagger E\nu=6-2\chi\mu,\qquad
b_\lambda^2+6(\beta-\lambda-x^2)=6-5d-\lambda(6+3\mu).
$$

因此

$$
\begin{aligned}
16\operatorname{Tr}(E\rho_\lambda)
&=b_\lambda^2+6(\beta-\lambda-x^2)
 +2\sqrt6\,b_\lambda u+\lambda(6-2\chi\mu)\\
&=6-5d.
\end{aligned}
$$

原恒等式 $E+2F=3I/4+3C/8$ 再给 $\operatorname{Tr}(F\rho_\lambda)=(6+11d)/32$，所以没有遗漏原 $F$ 矩。$\ell^\dagger\psi=-\gamma\sqrt d+\alpha x<0$，而 $\nu\in N$，故 $\psi,\nu$ 线性独立，$\rho_\lambda$ 秩二。其 $aa$ 条目和 $ah$ 主行列式展开为 (III.7.3)。因 $D\ell=0$，$B_d(\rho_\lambda)$ 恰为秩一 $A$ 在 $(a,\ell)$ 上的 Gram 矩阵，其 $00$ 条目为 $d$，所以行列式为零。母卷定理 36.2 的原极端层判据于是给 $\rho_\lambda\in\mathsf R_+$。

为写明原五维前驱，记母卷的物理向量为 $p=Bq,c_{\rm ph},b_{\rm ph},k_-$；它们的固定扇区识别满足

$$
Vp=(a,0),\quad VBr=(h,0),\quad Vc_{\rm ph}=(g,0),\quad
Vk_-=(0,k),\quad Vb_{\rm ph}=(0,g).
$$

取

$$
\eta_+=\sqrt d\,p+xBr+(u+\mathrm iv)c_{\rm ph},\qquad
\eta_-=\frac{\zeta k_-+\mathrm i\sqrt\beta\,b_{\rm ph}}{\sqrt{N_2}}.
\tag{III.7.5}
$$

三个 Kraus 算子 $BP_+$、$\eta_+f^\dagger$、$\sqrt\lambda\,\eta_-f^\dagger$ 的伴随平方和为

$$
P_++(\|\eta_+\|^2+\lambda\|\eta_-\|^2)ff^\dagger
=P_++ff^\dagger=I_3.
$$

故它们定义原域 CPTP 通道 $T_\lambda$。$V\eta_+=(\psi,0)$、$V\eta_-=(0,\nu)$，所以其后继为 $S_{\rho_\lambda}$。这正是母卷 (35.6) 的分扇区提升：$\omega=V^\dagger(A\oplus D)V$，$T_\lambda(X)=BP_+XP_+B^\dagger+(f^\dagger Xf)\omega$。已给的迹、$A_{aa}$、$E,F$ 矩使母卷 (35.3) 的三个完整输入效果算子逐块相等；母卷定理 35.2 的递推给出所有后续深度，故 $T_\lambda\in\mathcal F_{\sqrt d}$。这不是只在某个输入态上相等的提升。∎

**定理 7.3（完整复原风险的定量严格下界）。** 对原擦除标签菜单、原全深度数据、任意共同 CPTP 重建和全部有限未触动参考，

$$
r\left(\frac5{61}\right)>
\frac{60}{61}+\frac3{968000000}.
\tag{III.7.6}
$$

中心允许为任意复密度矩阵，包括 $\mathcal K_d$ 外的中心。

证明。先在母卷定理 37.2 的纯截面中心 $\bar\sigma$ 取得严格距离，再量化移动中心的代价。令

$$
\begin{gathered}
w_0=(a-2h)/\sqrt5,\qquad
\bar\sigma=\frac{25}{61}w_0w_0^\dagger+\frac{36}{61}gg^\dagger,\qquad
r_0=\frac{60}{61},\quad c_0=\frac{30}{61},\quad H=\bar\sigma+c_0I,\\
f_*=\frac{61\sqrt d}{165}(5a+h)+\mathrm i\frac{61\sqrt\beta}{66}g,\qquad
L=\|f_*\|^2=\frac{1952}{1815},\\
K=\sqrt{\frac{61}{5445}},\qquad D_0=\sqrt{\frac{854}{1089}},\qquad B_0=\frac{S^2}{N_2}.
\end{gathered}
\tag{III.7.7}
$$

直接代入 $Hf_*=\sqrt d\,a+\mathrm i\sqrt\beta\,g$，所以 $f_*^\dagger Hf_*=1$。由 (III.7.2)，

$$
|f_*^\dagger\nu|^2=B_0,\qquad
F_*:=f_*^\dagger\rho_\lambda f_*
=\left(\frac5{33}+Kx+D_0v\right)^2+D_0^2u^2+\lambda B_0.
\tag{III.7.8}
$$

所需另三个严格界为

$$
0<K<\frac{106}{1000},\qquad
D_0>\frac{8855538}{10^7},\qquad B_0>\frac{104485}{100000}.
$$

前两界的平方裕量为 $9001/272250000$、$4372393871/27225000000000000$。第三界由 $\chi$ 的上下界分别代入分子、分母得到

$$
B_0>\frac{16939455689471509}{16212330653750000},\qquad
\frac{16939455689471509}{16212330653750000}-\frac{104485}{100000}
=\frac{4011801643}{32424661307500000}>0.
$$

由 $x<0$，(III.7.8) 中的实部严格大于正有理数

$$
W=\frac5{33}-\frac{106}{1000}\frac{318}{10^6}
+\frac{8855538}{10^7}\frac{9576179}{10^7}
=\frac{1649180962783483}{1650000000000000}>0.
$$

从而

$$
\begin{aligned}
F_*&>W^2+\frac{104485}{100000000}>\frac{20001}{20000},\\
W^2+\frac{104485}{100000000}-\frac{20001}{20000}
&=\frac{6327132455939915137611289}{2722500000000000000000000000000}>0.
\end{aligned}
\tag{III.7.9}
$$

Rayleigh 商及迹零 qutrit 恒等式 $\|X\|_1=2\|X\|_{\rm op}$ 给

$$
\|\rho_\lambda-\bar\sigma\|_1
>r_0+\frac1{10000L}
=r_0+\frac{363}{3904000}>r_0+e,\qquad e=\frac1{11000}.
\tag{III.7.10}
$$

最后一步的有理差为 $89/42944000>0$。这一步只涉及固定中心，尚不是 (III.7.6)。

现在使用实际纯态对

$$
P_\pm=\varphi_\pm\varphi_\pm^\dagger,\qquad
\varphi_\pm=\sqrt{\frac{25}{61}}w_0\pm\mathrm i\sqrt{\frac{36}{61}}g.
\tag{III.7.11}
$$

母卷定理 37.2 已给它们的原域提升和可行性。它们的中点是 $\bar\sigma$，$Q=(P_+-P_-)/2$ 满足 $\|Q\|_F^2=r_0^2/2$。对任意迹零复 Hermitian 三阶矩阵 $X$，把谱写为 $p,-u_0,-v_0$、$p=u_0+v_0$、$u_0,v_0\ge0$，或整体反号，得到成熟谱比较

$$
2\|X\|_F^2\le\|X\|_1^2\le\frac83\|X\|_F^2.
\tag{III.7.12}
$$

零特征值也包括在内。若任意复密度 $\sigma$ 到两个 $P_\pm$ 的迹距离都至多为 $R$，Hilbert–Schmidt 平行四边形恒等式给

$$
\begin{aligned}
2\|\sigma-\bar\sigma\|_F^2+r_0^2
&=\|P_+-\sigma\|_F^2+\|P_--\sigma\|_F^2\le R^2,\\
\|\sigma-\bar\sigma\|_1^2&\le\frac43(R^2-r_0^2).
\end{aligned}
\tag{III.7.13}
$$

该估计没有使用实性、满秩或 $\sigma\in\mathcal K_d$。

取 $R=\max_{\rho\in\mathcal K_d}\|\rho-\sigma\|_1$、$\eta=R-r_0\ge0$。由 (III.7.10)、三角不等式及 (III.7.13)，

$$
e<\eta+\sqrt{\frac43(2r_0\eta+\eta^2)}.
$$

右侧在 $\eta\ge0$ 严格递增。解相应的等式，或在 $\eta<e$ 时平方并解二次不等式，得到

$$
\eta>g(e):=
\frac{3e^2}{\sqrt{(4r_0+3e)^2+3e^2}+4r_0+3e}.
\tag{III.7.14}
$$

若 $\eta\ge e$，同一结论也直接成立。这里

$$
16-\bigl[(4r_0+3e)^2+3e^2\bigr]=\frac{58322428837}{112560250000}>0,
\qquad 4-(4r_0+3e)=\frac{43817}{671000}>0.
$$

所以 (III.7.14) 分母小于 $8$，$g(e)>3e^2/8=3/968000000$。母卷定理 35.5 保证最小密度中心达到；将上述严格估计用于该达到中心即得 (III.7.6)。

对任何原共同 CPTP 重建 $\mathcal R$，不预设其输出支持或 Kraus 秩，母卷定理 35.5 的压缩

$$
\mathcal C_B(Y)=B^\dagger YB+
\operatorname{Tr}((I_5-BB^\dagger)Y)gg^\dagger,\qquad
\sigma=\mathcal C_B(\mathcal R(ff^\dagger))
$$

产生一个任意许可的复密度中心，并给

$$
\sup_{T\in\mathcal F_{\sqrt d}}\|\mathcal R-\mathcal GT\|_\diamond
\ge\max_{\rho\in\mathcal K_d}\|\rho-\sigma\|_1.
$$

全部有限未触动参考已包含在同一定理的原 diamond 等号和下界内。因此本结论覆盖原通道问题的全部量词，不是纯态、实态或受限重建子问题的优化。∎

## 8. 原完整源上的两个三次包含多项式

**定义 8.1（六实坐标的九个原不等式）。** 对任意 $0<d<1$，令 $\tau=3-2\sqrt2$、$J=\operatorname{diag}(1,1,\sqrt6)$、$G=J^2=\operatorname{diag}(1,1,6)$。对 $\mathbf x=(s,y,w,v,m,n)\in\mathbb R^6$ 置 $z=1-d-s-y$ 以及

$$
\mathscr R(\mathbf x)=J\rho(\mathbf x)J=
\begin{pmatrix}
d+s&-(s+y)/2+\mathrm iv&4s-3w+\mathrm im\\
-(s+y)/2-\mathrm iv&y&w+\mathrm in\\
4s-3w-\mathrm im&w-\mathrm in&6z
\end{pmatrix}.
\tag{III.8.1}
$$

令 $U_0=-(s+y)/2+\mathrm iv$、$V_0=4s-3w+\mathrm im$、$W_0=w+\mathrm in$。七个非空主子式和另外两个约束完整写为

$$
\begin{aligned}
g_1&=d+s,&g_2&=y,&g_3&=6z,\\
g_4&=(d+s)y-(s+y)^2/4-v^2,\\
g_5&=6(d+s)z-(4s-3w)^2-m^2,\\
g_6&=6yz-w^2-n^2,\\
g_7&=6(d+s)yz+2\Re(U_0W_0\overline{V_0})
 -(d+s)(w^2+n^2)-y((4s-3w)^2+m^2)
 -6z((s+y)^2/4+v^2),\\
g_8&=s,\\
g_9&=d(y-\tau^2s)-v^2-\frac{[y+(1+2\tau)s]^2}{4}.
\end{aligned}
\tag{III.8.2}
$$

所有 $g_i$ 都是 $\mathbb Q(\sqrt2,d)$ 上的实多项式，源变量总次数至多三。记 $X_d=\{\mathbf x:g_i(\mathbf x)\ge0, 1\le i\le9\}$。这里 $v,m,n$ 保留全部三个虚相干坐标，不要求为零。

**命题 8.2（源与中心的忠实坐标）。** $\mathbf x\mapsto J^{-1}\mathscr R(\mathbf x)J^{-1}$ 是 $X_d$ 到全部复 $\mathcal K_d$ 的仿射双射，包括低秩边界。可以在优化中选实对称中心，但其全部五个实坐标必须保留：

$$
\Sigma=J\sigma J=
\begin{pmatrix}
a_c&b_c&p_c\\b_c&h_c&q_c\\p_c&q_c&6(1-a_c-h_c)
\end{pmatrix}\succeq0,\qquad
\operatorname{Tr}(G^{-1}\Sigma)=1.
\tag{III.8.3}
$$

$p_c,q_c$ 分别包含 $ag,hg$ 相干；中心没有源的 $E,C,F$ 矩或 $s\ge0$ 约束。合同变换后的密度条件是加权迹一，不能换成 $\operatorname{Tr}\Sigma=1$。

证明。母卷定理 35.6 已从原矩给出

$$
\Re\rho_{ah}=-(s+y)/2,\qquad
\Re\rho_{ag}+3\Re\rho_{hg}=4s/\sqrt6.
$$

逆坐标为

$$
(s,y,w,v,m,n)=
(\rho_{aa}-d,\rho_{hh},\sqrt6\Re\rho_{hg},\Im\rho_{ah},
\sqrt6\Im\rho_{ag},\sqrt6\Im\rho_{hg}).
$$

Hermitian 矩阵半正定等价于所有非空主子式非负，故 $g_1,\ldots,g_7$ 正好给 $\rho\succeq0$。$g_8$ 给原超额，且

$$
B_d(\rho)=
\begin{pmatrix}d&a^\dagger\rho\ell\\\ell^\dagger\rho a&\ell^\dagger\rho\ell\end{pmatrix},
\qquad \ell=\alpha(h-\tau a),\qquad \det B_d(\rho)=\alpha^2g_9.
\tag{III.8.4}
$$

因 $d>0$，$g_9\ge0$ 等价于该 $B_d$ 半正定，包含其行列式为零的面。于是母卷定理 35.4–35.6 给所述双射及原域提升。$\operatorname{Tr}(G^{-1}\mathscr R)=1$ 自动成立。

$\mathcal K_d$ 对复共轭封闭。对任意复密度 $\sigma$，令 $\sigma_{\mathbb R}=(\sigma+\overline\sigma)/2$；它仍是密度，迹范数凸性及源的共轭对称性给 $\max_\rho\|\rho-\sigma_{\mathbb R}\|_1\le\max_\rho\|\rho-\sigma\|_1$。实对称迹一三阶矩阵有五个自由坐标，经过 $J$ 合同正好得到 (III.8.3)。这只平均中心，并未平均或删减对手。∎

**命题 8.3（正半径的两个三次式恰为全域包含）。** 对 (III.8.3) 的任意候选中心和 $c>0$，置

$$
q_+(\mathbf x)=\det(\Sigma+cG-\mathscr R(\mathbf x)),\qquad
q_-(\mathbf x)=\det(\mathscr R(\mathbf x)-\Sigma+cG).
\tag{III.8.5}
$$

则在 $X_d$ 上 $q_+\ge0,q_-\ge0$ 恰等价于

$$
\sigma-cI\preceq\rho\preceq\sigma+cI\quad(\rho\in\mathcal K_d),
\tag{III.8.6}
$$

因而恰等价于该中心的原完整风险至多 $2c$。源为任意复态，允许源与包含矩阵的秩退化及相切。

证明。两个行列式分别是 (III.8.6) 上、下侧差矩阵的合同行列式，故必要性立即成立。为证充分性，固定任一源，置 $\Delta=\rho-\sigma$、$T_2=\operatorname{Tr}(\Delta^2)$。$\Delta$ Hermitian 且迹零，所以成熟三阶特征多项式恒等式给

$$
\frac{q_+}{6}=c^3-\frac c2T_2-\det\Delta,
\qquad \frac{q_-}{6}=c^3-\frac c2T_2+\det\Delta.
\tag{III.8.7}
$$

因 $c>0$，两式非负蕴含 $T_2\le2c^2$。$M_\pm=cI\pm\Delta$ 的三个基本对称系数于是满足

$$
e_1(M_\pm)=3c>0,\qquad
e_2(M_\pm)=3c^2-T_2/2\ge2c^2>0,\qquad e_3(M_\pm)\ge0.
$$

对任何 $z_0>0$，$\det(z_0I+M_\pm)=z_0^3+e_1z_0^2+e_2z_0+e_3>0$。若 $M_\pm$ 有负特征值，取其绝对值作为 $z_0$ 就与此矛盾。因此 $M_\pm\succeq0$，即所需包含。即使 $e_3=0$ 论证仍有效，没有假定行列式严格正。母卷定理 35.5 给原风险等价。

$c=0$ 时这个一般的逐点行列式推序蕴含不成立：取两个密度 $\rho=\operatorname{diag}(1,0,0)$、$\sigma=\operatorname{diag}(0,1,0)$，则 $\Delta=\operatorname{diag}(1,-1,0)$ 的两侧行列式都为零，包含却不成立。此例只说明一般谱蕴含的边界，不声称它属于本源。对实际 $0<d<1$，母卷 (38.2) 的原两世界下界 $r(d)\ge2\sqrt{d(1-d)}>0$ 保证每个最优 $c=r(d)/2$ 严格正，所以 (III.8.5) 适用于全部实际最优值。∎

## 9. 相切全域上证书与有限极端下证书

**定义 9.1（完整输入域与九生成元预序）。** 固定 $d$、五个中心坐标和 $c>0$，令

$$
K_{\rm in}=\mathbb Q(\sqrt2,d,a_c,b_c,h_c,p_c,q_c,c)
\subseteq\mathbb R
$$

带实际实数序。取实数内与该序相容的实闭包 $K_{\rm rc}\subseteq\mathbb R$。系数条件涉及全部这些输入，不只涉及 $d$。在 $K_{\rm rc}[\mathbf x]$ 内定义

$$
\mathcal P(g)=\left\{
\sum_{\epsilon\in\{0,1\}^9}\sigma_\epsilon(\mathbf x)
\prod_{i=1}^9g_i(\mathbf x)^{\epsilon_i}:
\sigma_\epsilon\text{ 为有限平方和}\right\}.
\tag{III.9.1}
$$

共 $2^9=512$ 种平方自由乘积；每个元素在原 $X_d$ 上非负。

**命题 9.2（原两个三次式的相切有限存在接口）。** 对每个固定 $q\in\{q_+,q_-\}$，$q\ge0$ 在 $X_d$ 全域成立，当且仅当存在整数 $m\ge0$ 和 $S_q,T_q\in\mathcal P(g)$，使精确多项式恒等式

$$
qT_q=q^{2m}+S_q
\tag{III.9.2}
$$

成立。可以对源变量的各组成项次数取统一有限上限

$$
\mathcal B=
2^{\,2^{\left(2^{\,3^{\,4^6}}+11^{\,2^6}3^{\,2\cdot16^6}\right)}}.
\tag{III.9.3}
$$

这是每个固定候选中心、半径和参数的证书存在与恒等式验证接口，不是实际达到中心或实际最优半径的数据。

证明。若存在 (III.9.2)，却有原可行 $\mathbf x$ 满足 $q(\mathbf x)<0$，则左边非正而右边严格正，矛盾。这也包含 $m=0$，其右边含常数一。没有在 $q=0$ 处分母相除，也没有要求 $q$ 严格正。

反向使用 Lombardi–Perrucci–Roy，[*An elementary recursive bound for effective Positivstellensatz and Hilbert 17-th problem*, arXiv:1404.2338v3](https://arxiv.org/html/1404.2338v3) 的定理 1.2.9。其有序系数域取 $K_{\rm in}$，实闭扩张可取 $\mathbb R$；符号条件三元组准确取为

$$
\mathcal F_{\ne}=\{q\},\qquad
\mathcal F_{\ge}=\{g_1,\ldots,g_9,-q\},\qquad
\mathcal F_{=}=\varnothing.
\tag{III.9.4}
$$

其实点恰为原源内 $q<0$ 的点。若该集合为空，定理 1.2.9 给不可相容恒等式 $q^{2m}+N_q=0$；无等式理想项。将 $N_q$ 中 $-q$ 的偶次幂吸收进平方项，奇次幂写成 $-q$ 乘偶次幂；同样把各 $g_i$ 的偶次幂吸收进平方项，即得 $N_q=S_q-qT_q$。原定理允许正的 $K_{\rm in}$ 权重乘平方；在 $K_{\rm rc}$ 中吸收其正平方根，得到 (III.9.1)。若 $q$ 恒等为零，可直接取 $m=1,S_q=T_q=0$。

为固定次数及括号，原文定义 1.2.7–1.2.8 将不可相容式的次数定义为单项式乘积部分以及锥、理想中每个组成项的最大总次数，而非仅化简后相消多项式的次数。定理 1.4.2 对 $k$ 个变量、每式次数至多 $D$、按记号 1.3.1 模正负号计数 $s_{\rm pol}$ 的界为

$$
2^{\,2^{\left(
2^{\max\{2,D\}^{\,4^k}}
+s_{\rm pol}^{\,2^k}\max\{2,D\}^{\,16^k\operatorname{bit}(D)}
\right)}}.
\tag{III.9.5}
$$

本源 $k=6,D=3,\operatorname{bit}(3)=2$，且 (III.9.4) 的多项式模正负号至多十类，因为 $q,-q$ 属同一类。以十一代入这个单调界是保守上限，恰得 (III.9.3)。分组及把偶次幂吸收进平方不增加组成项次数；因此该界适用于 $q^{2m}$、$S_q$ 及 $qT_q$ 的组成项，也可保守地用于 $T_q$ 的组成项。这里没有 Archimedean 假设、Putinar 层级有限收敛假设、一般位置或严格互补假设。源或目标的相切及秩边界均由同一符号条件包含。

只有全部输入代数时，才可把这里的系数取为实代数数，即代数于 $\mathbb Q$；一般输入对应的是完整有序输入域的实闭包。对代数输入，给出的有限平方和与恒等式可在实代数数的精确运算中验证。对任意没有有效表示的超越输入，存在性不构成有效的精确算术算法。(III.9.3) 虽有限却极大，不给低阶证书、可行计算代价或最优中心。∎

**命题 9.3（至多六个共轭配对极端接触的下界）。** 假设给出 $n\le6$ 个代表

$$
(\rho_j,\varepsilon_j,v_j,p_j),\qquad
\rho_j\in\mathcal K_d,\quad\varepsilon_j\in\{+1,-1\},\quad
v_j\in\mathbb C^3,\quad\|v_j\|=1,\quad p_j\ge0,\quad\sum_jp_j=1.
$$

每个代表表示 $(\rho_j,v_j)$ 与 $(\overline\rho_j,\overline v_j)$ 的等权配对。定义

$$
Q_j=\Re(v_jv_j^\dagger),\qquad
M=\sum_jp_j\varepsilon_jQ_j,\qquad
A_*=\sum_jp_j\varepsilon_jv_j^\dagger\rho_jv_j.
\tag{III.9.6}
$$

若存在实数 $\kappa$ 使

$$
M\preceq\kappa I,\qquad A_*-\kappa=c,
\tag{III.9.7}
$$

则对所有复密度中心 $\theta$ 都有 $\max_{\rho\in\mathcal K_d}\|\rho-\theta\|_1\ge2c$。若同一中心和 $c>0$ 还满足命题 9.2 的两个上证书，则原完整最小最大半径恰为 $2c$。

反之，在每个原实际最优值 $c=r(d)/2>0$，可选实对称最优中心 $\sigma$ 和这样至多六个配对代表，并可令每个 $\rho_j$ 属于母卷的极端层 $\mathsf P\cup\mathsf R_0\cup\mathsf R_+$，满足活动条件

$$
(\rho_j-\sigma)v_j=\varepsilon_jc\,v_j\quad(p_j>0),\qquad
(\kappa I-M)\sigma=0.
\tag{III.9.8}
$$

允许 $\sigma$ 位于密度正锥的边界，允许重特征值和零接触权重。

证明。对任意复密度 $\theta$，原迹零 qutrit 恒等式及 Rayleigh 原理给

$$
\frac12\max_{\rho\in\mathcal K_d}\|\rho-\theta\|_1
\ge\varepsilon_jv_j^\dagger(\rho_j-\theta)v_j.
$$

对它的共轭代表也成立，配对平均右边为 $\varepsilon_jv_j^\dagger\rho_jv_j-\varepsilon_j\operatorname{Tr}(Q_j\theta)$。再按 $p_j$ 平均，得到

$$
\frac12\max_{\rho\in\mathcal K_d}\|\rho-\theta\|_1
\ge A_*-\operatorname{Tr}(M\theta)\ge A_*-\kappa=c.
\tag{III.9.9}
$$

实对称 $M\preceq\kappa I$ 同时是复 Hermitian 序，所以最后一步覆盖所有复中心。没有要求 $\theta\in\mathcal K_d$。母卷定理 35.5 将其传至所有原共同 CPTP 重建。

证明存在性时，在五维实仿射空间 $\mathcal A=\{\sigma=\sigma^{\mathsf T}\in M_3(\mathbb R):\operatorname{Tr}\sigma=1\}$ 上考虑

$$
f(\sigma)=\max_{\rho\in\mathcal K_d,\ \varepsilon=\pm1,\ \|v\|=1}
\varepsilon v^\dagger(\rho-\sigma)v.
\tag{III.9.10}
$$

该函数在整个 $\mathcal A$ 有限、凸且 Lipschitz；只有在密度子集上才将它解释为半迹风险。指标集 $\mathcal K_d\times\{+1,-1\}\times\{v\in\mathbb C^3:\|v\|=1\}$ 紧，指标和仿射函数连续。Boyd–Duchi–Pilanci–Vandenberghe 的作者版 [*Subgradients*](https://web.stanford.edu/class/ee364b/lectures/subgradients_notes.pdf)，§3.5 的紧指标最大值次梯度规则给 $\partial f(\sigma)$ 为活动仿射梯度的凸包。§2.5 的约束最小规则适用，因为 $\operatorname{dom}f=\mathcal A$，最优点在该定义域内部；它可以在密度集边界。于是存在活动梯度的凸组合 $-M$，使

$$
-\operatorname{Tr}(M(\theta-\sigma))\ge0
\quad\text{对每个实对称密度 }\theta.
\tag{III.9.11}
$$

这里仿射空间的切空间是五维迹零实对称空间，$-M$ 表示梯度在该空间的投影。取 $\kappa=\lambda_{\max}(M)$；实特征向量已达到 $M$ 在全部实密度上的最大期望，所以 (III.9.11) 意味 $\operatorname{Tr}(M\sigma)=\kappa$，并给 $M\preceq\kappa I$。两个正半定矩阵 $\kappa I-M$ 与 $\sigma$ 的乘积迹为零，故乘积为零，得到 (III.9.8) 的第二式。正锥边界的法锥由这个条件承担，不能在边界强加 $M=\kappa I$。

在五维切空间对活动梯度作 Caratheodory 的仿射依赖消去，可保留至多六项：若更多项有正权重，其梯度仿射相关，沿一个保持总权重及梯度的非零权重方向移动至某权重为零，迭代即可。该操作保持投影梯度。重新形成的完整矩阵 $M$ 与原矩阵至多相差一个 $I$ 的倍数，对应地调整 $\kappa$ 即可。每项仍活动，故 $A_*-\operatorname{Tr}(M\sigma)=c$；不需要为 $A_*$ 再增加一个维数。于是 (III.9.7) 成立。

最后对各活动 $(\varepsilon_j,v_j)$，在实际紧凸 $\mathcal K_d$ 上最大化线性泛函 $\rho\mapsto\varepsilon_jv_j^\dagger\rho v_j$。它的暴露面非空，可取该面的极端点；暴露面的极端点也是 $\mathcal K_d$ 的极端点。替换为此点不改变梯度和活动值。母卷定理 36.2 给原三个极端层，且共轭仍保持极端性及活动性。最优全域包含使 $cI-\varepsilon_j(\rho_j-\sigma)\succeq0$；其在 $v_j$ 上期望为零就给第一条 (III.9.8)。全证明不假定中心满秩、接触特征值单重、严格互补或唯一性。∎

**推论 9.4（有理参数的正权 $\mathsf R_+$ 接触义务）。** 在 $d=5/61$，若命题 9.3 的匹配最优下证书选自原三个极端层，则至少一个正权代表属于 $\mathsf R_+$。若不要求极端支持，只能由此推出至少一个正权可行代表满足 $s>0$。

证明。若所有正权代表均在 $\mathcal K_d^0$，母卷定理 37.2 在 $\bar\sigma$ 的完整截面上界给

$$
A_*-\operatorname{Tr}(M\bar\sigma)
=\sum_jp_j\varepsilon_jv_j^\dagger(\rho_j-\bar\sigma)v_j\le\frac{30}{61}.
$$

又 $M\preceq\kappa I$，所以 $A_*-\kappa\le A_*-\operatorname{Tr}(M\bar\sigma)\le30/61$，与定理 7.3 的 $c=r(d)/2>30/61$ 矛盾。因此有正权代表的 $s>0$。在极端层中 $\mathsf P,\mathsf R_0$ 都有 $s=0$，其余恰为 $\mathsf R_+$；未作极端选择时，正超额本身不能推出极端性。命题 7.2 的显式态给出实际 $\mathsf R_+$ 世界，却未被本推论指定为未知最优证书中的某一接触。∎

**命题 9.5（代数输入的存在范围）。** 对代数于 $\mathbb Q$ 的 $0<d<1$，可以在实代数数中选择最优中心、半径、命题 9.2 的两个有限证书及命题 9.3 的匹配接触数据；这个存在性不选出它们的数值或分支。

证明。先在实数内用紧达到性、命题 8.3、9.2–9.3 得到一组匹配数据。固定这组有限证书的幂次、组成项次数、平方项数及接触数。把所有复变量拆成实部和虚部，将恒等式逐系数相等、源的九不等式、中心和 $\kappa I-M$ 的主子式、单位向量、权重、活动等式及 $A_*-\kappa=c>0$ 写成有限多项式符号条件。其系数都在实代数数中，该实闭域存在实数扩张解。若它在实代数数中无解，LPR 定理 1.2.9 的有序扩张等价性将排除实数扩张解，矛盾。故存在实代数数解；两侧匹配证书保证其达到原最优值。该论证并不对任意超越参数给有效表示，也不提供一个已展开的代数中心。∎

## 10. 充分延拓方法的边界与中央缺口

**命题 10.1（原源上的 CP 加余正充分上证书）。** 对任一方向 $\epsilon\in\{+1,-1\}$，若存在完全正映射 $\Phi_3,\Psi_3:M_3\to M_3$、$\Phi_2,\Psi_2:M_2\to M_3$ 及 $T_0\succeq0$，使六实变量上的仿射恒等式

$$
cI+\epsilon(\sigma-\rho(\mathbf x))
=\Phi_3(\rho(\mathbf x))+\Psi_3(\rho(\mathbf x)^{\mathsf T})
+sT_0+\Phi_2(B_d(\rho(\mathbf x)))
+\Psi_2(B_d(\rho(\mathbf x))^{\mathsf T})
\tag{III.10.1}
$$

成立，则该方向的全复源包含成立。两个方向都成立时给原完整风险上界 $2c$。此为充分证书，不主张每个正确的标量包含都有这种延拓。

证明。原可行源的 $\rho,B_d$ 及其转置都半正定，$s\ge0$；完全正映射尤其正，故右侧半正定。逐仿射系数相等只需常数和六个方向的七个矩阵等式。四个映射的 Choi 矩阵大小依次为 $9\times9,9\times9,6\times6,6\times6$，加上 $3\times3$ 的 $T_0$；这些有限正约束本身只给充分方向。

为说明不能从标量正性跳到完全正性，置

$$
L(\mathbf x)=\rho(\mathbf x)\oplus s\oplus B_d(\rho(\mathbf x))
=L_0+\sum_{i=1}^6x_iL_i.
$$

七个系数线性独立。其任意非零半正定齐次组合 $u_0L_0+\sum x_iL_i$ 的第一块迹为 $u_0$，故 $u_0\ge0$。若 $u_0=0$，第一块半正定且迹零，必须为零；由 (III.8.1) 的独立坐标，所有 $x_i$ 为零，其他块也为零，矛盾。因此 $u_0>0$，除以它就是一个实际可行源。由此原标量包含等价于系数线性映射在该系数张成空间上的正性；延拓到整个 $M_3\oplus\mathbb C\oplus M_2$ 的完全正或可分解映射则是更强要求，没有在此建立其必要性。

Helton–Klep–McCullough，[arXiv:1003.0908v2](https://arxiv.org/html/1003.0908v2)，定理 3.5 针对实对称 monic 线性矩阵束及有界的矩阵层级源域：$n$-正性对应第 $n$ 层包含，完全正性对应全部矩阵层级包含。这里的源坐标是六个经典实数；原物理参考量词已由母卷定理 35.5 的态/diamond 约化处理，不供应将这些坐标替换为任意矩阵的权限。Kellner–Theobald–Trabandt，[arXiv:1308.5076v3](https://arxiv.org/html/1308.5076v3)，命题 4.4、4.7、定理 4.8 同样区分正性、完全正充分条件及标量包含，不能将其充分条件反读为本源的等价条件。

其例 5.1 的一般差别可由精确矩阵直接看出。取标量矩阵束

$$
A^\nu(x)=\begin{pmatrix}1&0&x_1/\nu\\0&1&x_2/\nu\\x_1/\nu&x_2/\nu&1\end{pmatrix},\qquad
B(x)=\begin{pmatrix}1+x_1&x_2\\x_2&1-x_1\end{pmatrix}.
$$

标量域分别为半径 $\nu$ 和一的圆盘，故 $\nu=1$ 时相同。用 Pauli 矩阵 $Z=\operatorname{diag}(1,-1)$、$X=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$，在第二矩阵层级置 $X_1=\nu Z/\sqrt2,X_2=\nu X/\sqrt2$。源矩阵的 Schur 补为 $I_2-(X_1^2+X_2^2)/\nu^2=0$，所以源仍半正定；目标有特征值 $1-\sqrt2\nu$，在 $\nu=1$ 严格负。因此这个一般标量包含不能有完全正系数匹配。它是方法量词的反例，不是本 $\mathcal K_d$ 的不可延拓证明。

Horodecki–Horodecki–Horodecki，[quant-ph/9605038v2](https://arxiv.org/html/quant-ph/9605038v2)，定理 3 及证明式 (17) 所用的正映射分解只覆盖完整矩阵代数的 $2\to2$、$2\to3$、$3\to2$ 低维情形。源中有一个 $M_2$ 块不意味着受约束的整个直和或 $M_3\to M_3$ 块都有这种正或可分解延拓。故不能由这些定理将 (III.10.1) 与原标量包含认作等价；本节只使用其充分方向。∎

**命题 10.2（逆迹上证书只排除混合上接触）。** 若 $c>0$、$H=\sigma+cI\succ0$，且某密度 $\rho$ 满足 $\rho\preceq H$、$H-\rho$ 奇异、$\operatorname{rank}\rho\ge2$，则

$$
\operatorname{Tr}(H^{-1}\rho)>1.
\tag{III.10.2}
$$

因此要求对全部源有 $\operatorname{Tr}(H^{-1}\rho)\le1$ 的上证书不能同时容纳这样的秩至少二的上接触。该结论不排除混合下接触，也不是所有逆度量证书的不可能性定理。

证明。$W=H^{-1/2}\rho H^{-1/2}$ 满足 $0\preceq W\preceq I$；$H-\rho$ 奇异使 $W$ 有特征值一，秩至少二使另有严格正特征值，故 $\operatorname{Tr}W>1$，即 (III.10.2)。下接触没有前述奇异上差的假设。例如一般密度 $\sigma=\operatorname{diag}(1,0,0)$、$c=1$、$\rho=\operatorname{diag}(0,1/2,1/2)$ 给下接触，$H-\rho\succ0$，而 $\operatorname{Tr}(H^{-1}\rho)=1$。这个方向性例子不声称属于原 $\mathcal K_d$ 或描述其最优中心。∎

**定义 10.3（保留的实际构造问题与物理前提）。** (III.7.6) 是中央域内原完整复问题的定量优化下界，独立于是否已给出实际最优中心。§§8–9 给正确的全域上、下证书接口及有限存在性；它们没有给出 $d=5/61$ 的实际五坐标达到中心、精确半径、两份展开的预序恒等式或匹配接触向量和权重。全中央区间 $d_s<d<2/7$ 的原精确值和全部分支仍待确定；有限存在性不能替代这些具体构造。

数学来源的范围如下：原源、三极端层、原域提升、纯截面及既有分支分别直接消费母卷 §§35–38 与本卷 §§1–6；定理 7.3 的定量原模型推导和 §§8–9 的原源应用为 `repo-derived`。三阶谱代数、平行四边形恒等式、有限维凸几何、上述 LPR 定理、次梯度规则及正映射文献只作为这些应用的成熟中间工具，不单列为新的通用理论，也不作全域文献优先权主张。

复 Hilbert 空间、密度矩阵、Born 效果配对、CPTP 动力学和组合、完整原算子数据与原生取得权限仍是定义 1.1 和 6.3 的供应前提。所有态和原提升保持同一原擦除标签菜单，没有新增标签历史、返回环境、相位控制、制备参考或相关副本权限。母卷 $Q_a$ 的数学存在仍不同于其原生取得。隐藏超额 $s$ 与 $\Re(\rho_{ag}+3\rho_{hg})=4s/\sqrt6$ 的关系刻画一个条件盲区；这些风险与证书结果不推出量子原则的物理起源、经验有效性或信息守恒。

## 追加锚（本行以下为增补区）


## 11. 中央域内带非零虚相干的实际混合 Gram 族

**定义 11.1（原域、参数及固定四维投影）。** 本节直接使用 (III.1.3)–(III.1.6) 和母卷定理 35.4–35.6 的完整原通道约化。特别地，$r(d)$ 是不除以二的原 diamond 风险，双侧密度包含的标量 $c$ 对应风险 $2c$；不将两者混同。固定 $0<d<2/7$，令

$$
\begin{gathered}
r_H=-\frac{341}{1000},\quad t_H=\frac{19}{1000},\quad
\nu=-\frac34(2r_H+r_H^2+t_H^2)=\frac{848037}{2000000},\quad U=d\nu,\\
T=1-d(1+r_H^2+t_H^2)-U,\qquad
\ell=-\gamma a+\alpha h,\\
L_4=(1+3r_H,\ 3t_H,\ (\alpha+3\gamma)\sqrt\nu,\ 0)^{\mathsf T},\quad
H_0=\frac{4\alpha^2\nu}{\sqrt6},\quad N_0=L_4^{\mathsf T}L_4,\\
w_4=\frac1{1000}(232,743,159,492)^{\mathsf T},\quad
v_4=w_4-L_4\frac{L_4^{\mathsf T}w_4}{N_0},\\
a_4=\frac{H_0L_4}{N_0},\quad b_4=\frac{v_4}{\sqrt{v_4^{\mathsf T}v_4}},\quad
K=1+r_H^2+t_H^2+\nu+\frac{H_0^2}{N_0},\\
u_4=\sqrt d\,a_4+\sqrt{1-Kd}\,b_4=(u_1,u_2,u_3,u_4)^{\mathsf T}.
\end{gathered}
\tag{III.11.1}
$$

这里 $L_4,a_4,b_4,w_4,v_4$ 都与 $d$ 无关；$\ell$ 是原平面 $N$ 的法向量，$L_4$ 不是它。定义两个共同实现的 Gram 列

$$
\begin{aligned}
\psi&=\sqrt d\,a+\sqrt d(r_H+\mathrm i t_H)h+(u_1+\mathrm i u_2)g,\\
\chi&=\sqrt U\,k+(u_3+\mathrm i u_4)g,\\
A&=\psi\psi^\dagger,\qquad D=\chi\chi^\dagger,\qquad
\rho_R(d)=A+D.
\end{aligned}
\tag{III.11.2}
$$

**定理 11.2（整段中央域中的实际 $\mathsf R_+$ 世界）。** (III.11.1) 的所有分母与根式在 $0<d<2/7$ 合法，且 (III.11.2) 属于原 $\mathcal K_d$ 的 $\mathsf R_+$ 层。它的 $ah$ 虚部非零，不是仅在实截面或松弛源上成立的构造。

证明。$N_0>0$，因为 $\nu>0$、$\alpha+3\gamma>0$。投影的第四分量为 $(v_4)_4=123/250$，所以 $v_4^{\mathsf T}v_4>0$。精确展开得

$$
K=\frac{10500452933072035211}{5902051516513500000}
 +\frac{99478421530098761}{590205151651350000}\sqrt2
 <\frac{21}{10}.
\tag{III.11.3}
$$

最后一个不等式可用 $\sqrt2<99/70$ 作纯有理比较。因此 $1-Kd>2/5$。由 $L_4^{\mathsf T}b_4=0$、$\|b_4\|=1$，

$$
\|u_4\|^2=d\frac{H_0^2}{N_0}+1-Kd=T,\qquad
(\sqrt d L_4)^{\mathsf T}u_4=dH_0.
\tag{III.11.4}
$$

$A,D\succeq0$、$D\ell=0$、$A_{aa}=d$。下面是原矩的逐项恒等式，其中 $E$、$C$、$F$ 均为母卷的固定算子：

$$
\begin{aligned}
\operatorname{Tr}\rho_R&=d(1+r_H^2+t_H^2)+U+\|u_4\|^2=1,\\
\operatorname{Tr}(C\rho_R)&=d[(1+r_H)^2+t_H^2]+\frac43U=d,\\
16\operatorname{Tr}(E\rho_R)-(6-5d)
 &=6(\|u_4\|^2-T)
   +2\sqrt6[(\sqrt d L_4)^{\mathsf T}u_4-dH_0]=0,\\
\operatorname{Tr}(F\rho_R)&=(6+11d)/32.
\end{aligned}
\tag{III.11.5}
$$

最后一行直接使用原恒等式 $E+2F=3I/4+3C/8$，没有增加独立矩假设。这证明的是 (III.1.4) 的忠实分解。另有

$$
\begin{gathered}
s=(\rho_R)_{aa}-d=\alpha^2U>0,\qquad
\Im(\rho_R)_{ah}=-t_Hd\ne0,\\
\det(\rho_R)_{ah}
 =dU\bigl[(\gamma-\alpha r_H)^2+\alpha^2t_H^2\bigr]>0.
\end{gathered}
\tag{III.11.6}
$$

两列给秩至多二，正的 $ah$ 主行列式给秩恰二。由于 $D\ell=0$ 且 $A$ 秩一，原 $B_d(\rho_R)$ 是 $A$ 在 $(a,\ell)$ 上的压缩，$00$ 条目为 $d$，因而秩一、行列式为零。母卷定理 36.2 的穷尽判据给 $\rho_R\in\mathsf R_+$。所有 $ag,hg$ 实部及虚部都来自这同两列，不能把这些坐标的分别可达值当作联合可达值。∎

**命题 11.3（显式原五维 CPTP 提升与输入量词）。** 令母卷 §17、§29 的 $p=Bq$、$b_5=Bf$、$c_5=(e_0+e_1-e_3-e_4)/2$、$k_-=(e_0-e_1-e_3+e_4)/2$。取

$$
\begin{gathered}
\eta_+=\sqrt d\,p+\sqrt d(r_H+\mathrm i t_H)Br+(u_1+\mathrm i u_2)c_5,\\
\eta_-=\sqrt U\,k_-+(u_3+\mathrm i u_4)b_5,\qquad
\omega=\eta_+\eta_+^\dagger+\eta_-\eta_-^\dagger,\\
T_R(X)=BP_+XP_+B^\dagger+(f^\dagger Xf)\omega.
\end{gathered}
\tag{III.11.7}
$$

则 $T_R\in\mathcal F_{\sqrt d}$，且 $\mathcal GT_R=S_{\rho_R}$。

证明。原酉扇区识别满足 $V\eta_+=(\psi,0)$、$V\eta_-=(0,\chi)$，所以 $\omega=V^\dagger(A\oplus D)V\succeq0$ 且迹一。三个 Kraus 算子为 $BP_+,\eta_+f^\dagger,\eta_-f^\dagger$；其伴随平方之和为 $P_++ff^\dagger=I_3$。由 (III.11.5)，母卷 (35.3) 的三个完整输入效果算子一致，原递推 $J_{j+2}=(J_j+J_{j+1})/2$ 给全部深度。原约化 (III.1.6) 同时给全部复输入和任意有限未触动参考的范数对应；本命题只代入其已给的提升定理。数学上的 CPTP 存在性没有授予新的原生制备或控制权限。∎

## 12. 四个实际复世界的有理谱松弛下证书

**定义 12.1（纯世界、测试方向与权重）。** 对 $0<d\le1/5$，令

$$
\begin{gathered}
z_P=1/71,\quad e_P=\frac{z_P^2-1-2\mathrm iz_P}{1+z_P^2},\quad
h_P=e_P-1,\quad c_P=1+3h_P,\\
K_P=1+|h_P|^2=\frac{12603}{2521}<5,\\
\psi_P(d)=\sqrt d\,(a+h_Ph)-\mathrm i\frac{c_P}{|c_P|}\sqrt{1-K_Pd}\,g,
\qquad \rho_P(d)=\psi_P(d)\psi_P(d)^\dagger,\\
z_1=(31766229,\ -64269590-1846560\mathrm i,\ -1939739+69664583\mathrm i)^{\mathsf T},\\
z_2=(57802052,\ 3859327+535105\mathrm i,\ 24677326+77683792\mathrm i)^{\mathsf T},\\
N_1=9999999999434151,\quad N_2=9999999915674198,\quad
v_j=z_j/\sqrt{N_j},\quad Q_j=\Re(v_jv_j^\dagger),\\
p=\frac{19111437}{20000000},\quad \kappa=\frac{24681541}{50000000},\quad
M=pQ_1+(1-p)Q_2,\\
\mathcal A(d)=p\,v_1^\dagger\rho_P(d)v_1
 +(1-p)\,v_2^\dagger\rho_R(d)v_2,\qquad
\mathcal L(d)=2[\mathcal A(d)-\kappa].
\end{gathered}
\tag{III.12.1}
$$

这里 $N_j=z_j^\dagger z_j$，$c_P\ne0$，$1-K_Pd>0$。母卷 (36.2) 中取相位 $e_P$ 和符号 $-1$ 正好给 $\rho_P\in\mathsf P$，故不重证其原矩；其物理提升把 $(a,h,g)$ 换为 $(p,Br,c_5)$。四个源为 $\rho_P,\overline{\rho_P},\rho_R,\overline{\rho_R}$，对应测试向量为 $v_1,\overline{v_1},v_2,\overline{v_2}$，权重分别为 $p/2,p/2,(1-p)/2,(1-p)/2$。符号均为上侧 $+1$。

**定理 12.2（所有复中心的严格有理下界）。** 对 (III.12.1) 的整个参数域，$r(d)\ge\mathcal L(d)$。特别地，

$$
r(5/61)>\frac{9840437}{10000000},\qquad
r(5/61)>\frac{60}{61}+\frac1{2300}.
\tag{III.12.2}
$$

这里的中心包括 $\mathcal K_d$ 外的任意复密度，原共同重建的支持及 Kraus 秩不受限制。测试向量只承担下界，不断言是未知最优中心的精确接触特征向量。

证明。令 $H_\kappa=\kappa I-M$。若 $z_{j,k}=x_{j,k}+\mathrm iy_{j,k}$，则它的每个条目直接为

$$
(H_\kappa)_{kl}=\kappa\delta_{kl}
 -\frac{p(x_{1,k}x_{1,l}+y_{1,k}y_{1,l})}{N_1}
 -\frac{(1-p)(x_{2,k}x_{2,l}+y_{2,k}y_{2,l})}{N_2}.
$$

因此测试向量归一化中的 $\sqrt{N_j}$ 在投影矩阵和平方重叠中消去，谱松弛矩阵本身完全有理。以下按索引 $1,2,3,12,13,23,123$ 列出它的全部七个非空主子式；它们都是严格正的有理数：

$$
\begin{gathered}
\frac{7867508498723060657759781477390598461}{20576131512568619351381825254300000000} ,\\
\frac{299122429737761496914346347905800179}{3035822682182255314138302086700000000} ,\\
\frac{56900376400638296666296852438067}{92592591806558787081218213644350000000} ,\\
\frac{30207711956028049121175789354460818423996073309325089243599369233251}{423377188022519379252924478684925174660936742443421259668490000000000000000} ,\\
\frac{14062781798865141551118779238517841276895305173348862488947483355461}{423377188022519379252924478684925174660936742443421259668490000000000000000} ,\\
\frac{292160993171583027904572172761990335889546947876998036563217443945121}{34293552229824069719486882773478939147535876137917122033147690000000000000000} ,\\
\frac{618514033372853461521719821714793759110953797853557529975036864474169}{190519734610133720663816015408216328597421534099539566850820500000000000000000000000} .
\end{gathered}
\tag{III.12.3}
$$

因此 $H_\kappa\succ0$，这在复 Hermitian 序中同样成立。对任意复密度 $\theta$，迹零三阶 Hermitian 差满足

$$
\frac12\max_{\rho\in\mathcal K_d}\|\rho-\theta\|_1
\ge\mathcal A(d)-\operatorname{Tr}(M\theta)
\ge\mathcal A(d)-\kappa.
\tag{III.12.4}
$$

第一步是将四个实际世界各自的单位向量 Rayleigh 下界按上述正权平均；共轭对使中心项恰为实对称 $M$，但没有把 $\theta$ 取实。第二步只用 $\theta\succeq0$、$\operatorname{Tr}\theta=1$，不需要 $\theta\in\mathcal K_d$。对原任意共同重建 $R$，(III.1.6) 的 CPTP 压缩 $\theta=\mathcal C_B(R(ff^\dagger))$ 给相同下界。

在 $d_0=5/61$，由 (III.11.1)、(III.12.1) 的代数式有以下严格有理包围：

$$
\begin{aligned}
\frac{24641317150913}{25000000000000}
 &<\mathcal A(d_0)<\frac{98565268603653}{100000000000000},\\
\frac{19680874641461}{20000000000000}
 &<\mathcal L(d_0)<\frac{49202186603653}{50000000000000},\\
\frac{54646837}{125000000000}
 &<\mathcal L(d_0)-\frac{60}{61}
 <\frac{437174697}{1000000000000},\\
\frac{41731625894889}{50000000000000}
 &<1-Kd_0<\frac{83463251789779}{100000000000000},\\
\frac{201748328164701}{100000000000000}
 &<K<\frac{100874164082351}{50000000000000}.
\end{aligned}
\tag{III.12.5}
$$


以下给出 (III.12.5) 所需正根的额外有理包围。表中两个整数端点均除以 $10^{30}$；根式的精确定义由 (III.11.1)、(III.12.1) 给出，各根都严格落在相应开区间。

| 正根 | 下端整数 | 上端整数 |
| --- | --- | --- |
| $\sqrt2$ | $1414213562373095048801688724209$ | $1414213562373095048801688724210$ |
| $\sqrt{12}$ | $3464101615137754587054892683011$ | $3464101615137754587054892683012$ |
| $\sqrt6$ | $2449489742783178098197284074705$ | $2449489742783178098197284074706$ |
| $\sqrt\nu$ | $651167029263613745506844291696$ | $651167029263613745506844291697$ |
| $\sqrt{v_4^{\mathsf T}v_4}$ | $913528122393979964815381474708$ | $913528122393979964815381474709$ |
| $|c_P|$ | $4999523975753419711193654821834$ | $4999523975753419711193654821835$ |
| $\sqrt{5/61}$ | $286299167156934108956082682474$ | $286299167156934108956082682475$ |
| $\sqrt{1-5K_P/61}$ | $768263601874638040994829888470$ | $768263601874638040994829888471$ |
| $\sqrt{1-5K/61}$ | $913582244736502118999256729565$ | $913582244736502118999256729566$ |

将这些平方夹逼用于固定系数，再按 (III.12.7) 传播，给出 (III.12.5)；每一步只含有理运算及已指明的正根。

这些是明确代数式的包围，不是最优半径的包围。根式全部取正根；一种纯有理验证规则是：对正有理区间 $[l,u]$，用 $q_-^2\le l\le u\le q_+^2$、$q_-\ge0$ 给 $\sqrt{[l,u]}\subseteq[q_-,q_+]$，再以区间加、乘、除传播，除法只在分母严格正时使用。下述定义 12.3 把同一计算化为固定系数及两项参数根式，避免依赖逐点拟合。将 (III.12.5) 的下端分别与 $9840437/10000000$ 和 $60/61+1/2300$ 作有理比较即得 (III.12.2)。∎

**定义 12.3（下界曲线的精确固定系数）。** 在 $(a,h,g)$ 坐标内置

$$
\begin{gathered}
A_P=(1,h_P,0)^{\mathsf T},\qquad
B_P=(0,0,-\mathrm i c_P/|c_P|)^{\mathsf T},\\
A_1=(1,r_H+\mathrm i t_H,(a_4)_1+\mathrm i(a_4)_2)^{\mathsf T},\quad
B_1=(0,0,(b_4)_1+\mathrm i(b_4)_2)^{\mathsf T},\\
A_2=(\alpha\sqrt\nu,\gamma\sqrt\nu,(a_4)_3+\mathrm i(a_4)_4)^{\mathsf T},\quad
B_2=(0,0,(b_4)_3+\mathrm i(b_4)_4)^{\mathsf T},\\
P_P=|v_1^\dagger A_P|^2,\quad Q_P=|v_1^\dagger B_P|^2,\quad
W_P=2\Re\bigl(\overline{v_1^\dagger A_P}\,v_1^\dagger B_P\bigr),\\
P_R=\sum_{j=1}^2|v_2^\dagger A_j|^2,\quad
Q_R=\sum_{j=1}^2|v_2^\dagger B_j|^2,\quad
W_R=2\Re\sum_{j=1}^2\overline{v_2^\dagger A_j}\,v_2^\dagger B_j,\\
C_0=pQ_P+(1-p)Q_R-\kappa,\\
C_1=p(P_P-K_PQ_P)+(1-p)(P_R-KQ_R),\quad
W_p=pW_P,\quad W_r=(1-p)W_R.
\end{gathered}
\tag{III.12.6}
$$

每一系数都是已给整数、正平方根及四维投影的闭式表达，没有隐藏的拟合参数。由于

$$
\begin{gathered}
\psi_P=\sqrt d A_P+\sqrt{1-K_Pd}B_P,\\
\psi=\sqrt d A_1+\sqrt{1-Kd}B_1,\qquad
\chi=\sqrt d A_2+\sqrt{1-Kd}B_2,
\end{gathered}
$$

平方展开直接给

$$
\mathcal L(d)=2\left[C_0+C_1d+
 W_p\sqrt{d(1-K_Pd)}+W_r\sqrt{d(1-Kd)}\right].
\tag{III.12.7}
$$

**定理 12.4（闭参数段的统一严格混合超额）。** 在整个 $I=[163/2000,33/400]\subset(d_s,2/7)$ 上，

$$
r(d)>2\sqrt{5d(1-5d)}+\frac1{5000}.
\tag{III.12.8}
$$

证明。给定 (III.12.6) 的精确表达，下表的开区间端点均为有理数；平方根的有理平方夹逼和区间运算给出这些系数包围：

| 量 | 下端 | 上端 |
| --- | --- | --- |
| $C_0$ | $-24581/40000000000$ | $-153631/250000000000$ |
| $C_1$ | $23720337951/200000000000$ | $29650422439/250000000000$ |
| $W_p$ | $266952177409/125000000000$ | $2135617419273/1000000000000$ |
| $W_r$ | $48039403853/1000000000000$ | $24019701927/500000000000$ |
| $K$ | $2017483281647/1000000000000$ | $126092705103/62500000000$ |

这些数连同 $K_P=12603/2521$ 足以作整段导数包围。具体地，令 $f_0(d)=2\sqrt{5d(1-5d)}$、$g=\mathcal L-f_0$，则

$$
g'(d)=2C_1+
 W_p\frac{1-2K_Pd}{\sqrt{d(1-K_Pd)}}+
 W_r\frac{1-2Kd}{\sqrt{d(1-Kd)}}-
 \frac{5(1-10d)}{\sqrt{5d(1-5d)}}.
\tag{III.12.9}
$$

分母在 $I$ 严格正。将表中端点及 $d\in I$ 代入各正根的平方夹逼、按分子符号作有向乘除，可得

$$
\frac{160352118}{10^9}<g'(d)<\frac{397714349}{10^9}<\frac25.
\tag{III.12.10}
$$

所以 $|g'|<2/5$。又 $f_0(5/61)=60/61$，(III.12.5) 给 $g(5/61)>54646837/125000000000$，而 $\max_{d\in I}|d-5/61|=13/24400$。中值定理遂给

$$
\begin{aligned}
g(d)&>\frac{54646837}{125000000000}-\frac25\frac{13}{24400}
 >\frac1{5000},\\
\frac{224059941}{10^{12}}
 &<\frac{54646837}{125000000000}-\frac25\frac{13}{24400}
 <\frac{112029971}{500000000000}.
\end{aligned}
\tag{III.12.11}
$$

与 $r\ge\mathcal L$ 结合即得结论。整个论证是同一组实际世界与同一谱松弛矩阵的参数化使用；有限网格或局部接触方程不参与全称推断。∎

## 13. 有理点上的完整原源充分上证书

**定义 13.1（五方向密度中心及半径）。** 本节固定 $d_0=5/61$。沿用 $J=\operatorname{diag}(1,1,\sqrt6)$、$G=J^2$，令

$$
\begin{gathered}
\eta=10^{-7},\qquad
\widetilde\Sigma=\frac1{10^{10}}
\begin{pmatrix}
808433928&-1566599523&16957772\\
-1566599523&3035928498&39165659\\
16957772&39165659&36933825444
\end{pmatrix},\\
\Sigma=(1-3\eta)\widetilde\Sigma+\eta G,\qquad
\sigma=J^{-1}\Sigma J^{-1},\\
c_0=\frac{19701}{40000},\qquad \delta_0=\frac3{1000000},\qquad
c=c_0+\delta_0=\frac{30783}{62500}.
\end{gathered}
\tag{III.13.1}
$$

$\Sigma$ 的有理性指缩放坐标；原正交基中的 $ag,hg$ 条目还各除以 $\sqrt6$。全部五个中心方向都已指定。加权迹 $\operatorname{Tr}(G^{-1}\Sigma)=1$，且 $\Sigma_{11}<5/61$，所以此中心在 $\mathcal K_{d_0}$ 外。

**定义 13.2（十个有理正矩阵的完整数据）。** 下文各 $C_\epsilon,\widehat C_\epsilon$ 为九阶，$D_\epsilon,\widehat D_\epsilon$ 为六阶，$T_\epsilon$ 为三阶，$\epsilon\in\{+1,-1\}$。每个显示矩阵都整体乘 $10^{-10}$；列出所有行列，未隐去任何非零条目。全部条目为实数；帽号标记转置输入项，不是矩阵自身的转置。以输入指标优先、输出指标其次的顺序划分三阶块。

$$
C_{+}=\frac1{10^{10}}\begin{pmatrix}
24085156108&19446016060&447102484&14967275258&19743766612&1558087911&-11508299&159605438&-6063541028\\
19446016060&20527276926&-305543285&12105331066&18387786530&-864291745&10340635&-87477045&-4912827530\\
447102484&-305543285&157616181&277542803&35189881&514133196&-1973728&54741098&-113789357\\
14967275258&12105331066&277542803&9301365918&12280333112&967732198&-7023223&99236529&-3768312985\\
19743766612&18387786530&35189881&12280333112&17426151237&223413860&627776&23677168&-4979716313\\
1558087911&-864291745&514133196&967732198&223413860&1678721503&-6186759&178953827&-396786769\\
-11508299&10340635&-1973728&-7023223&627776&-6186759&102218&-592535&2767374\\
159605438&-87477045&54741098&99236529&23677168&178953827&-592535&19135118&-40789202\\
-6063541028&-4912827530&-113789357&-3768312985&-4979716313&-396786769&2767374&-40789202&1526812302
\end{pmatrix}.
$$

$$
\widehat C_{+}=\frac1{10^{10}}\begin{pmatrix}
137205&-9559835&-32852392&-296500&-5015904&22641206&3438760&-3469386&-61044\\
-9559835&783661327&1516901138&21814178&412475728&-671281624&-152734189&114715621&5960091\\
-32852392&1516901138&36169796934&160376954&782354136&-34420940571&-3938493744&4973528719&-12273001\\
-296500&21814178&160376954&1093386&11454074&-135614262&-17185395&19985970&82444\\
-5015904&412475728&782354136&11454074&217127710&-336944953&-78622782&58038560&3149740\\
22641206&-671281624&-34420940571&-135614262&-336944953&33621884540&3762208669&-4838180119&18599696\\
3438760&-152734189&-3938493744&-17185395&-78622782&3762208669&429092286&-543281169&1447629\\
-3469386&114715621&4973528719&19985970&58038560&-4838180119&-543281169&696659440&-2528772\\
-61044&5960091&-12273001&82444&3149740&18599696&1447629&-2528772&64035
\end{pmatrix}.
$$

$$
D_{+}=\frac1{10^{10}}\begin{pmatrix}
1722523160&5448698091&325874503&3265726442&3897237233&172582530\\
5448698091&17242021081&1030429207&10330534990&12331276285&545643423\\
325874503&1030429207&61728934&617817828&737103515&32694370\\
3265726442&10330534990&617817828&6191533262&7388967373&327191930\\
3897237233&12331276285&737103515&7388967373&8819419007&390332080\\
172582530&545643423&32694370&327191930&390332080&17319348
\end{pmatrix}.
$$

$$
\widehat D_{+}=\frac1{10^{10}}\begin{pmatrix}
5301385825&-7449355595&-816487940&8583388548&-829021221&-348927676\\
-7449355595&10472153137&1147001852&-12060989093&1167254054&490217715\\
-816487940&1147001852&125820916&-1321973236&127523673&53770495\\
8583388548&-12060989093&-1321973236&13897260210&-1342167853&-564945693\\
-829021221&1167254054&127523673&-1342167853&130853989&54520654\\
-348927676&490217715&53770495&-564945693&54520654&22982117
\end{pmatrix}.
$$

$$
T_{+}=\frac1{10^{10}}\begin{pmatrix}
27847041&-745314694&38323428\\
-745314694&19960138786&-1026478237\\
38323428&-1026478237&52848611
\end{pmatrix}.
$$

$$
C_{-}=\frac1{10^{10}}\begin{pmatrix}
15076832675&644408782&-236997979&1105485184&11558062128&-108393879&-17055876&-19245488&9155733128\\
644408782&2225838406&470714505&539904727&244613303&207879367&-6271221&1194897&-617434396\\
-236997979&470714505&7036273384&-44627060&-71809273&3500351095&-4253384&247304&-219872052\\
1105485184&539904727&-44627060&2194558902&786672134&-1854421&-28617275&-18935558&-204727725\\
11558062128&244613303&-71809273&786672134&11448101816&-189016568&-18151931&3026182&8745853633\\
-108393879&207879367&3500351095&-1854421&-189016568&2580684934&-29505360&-136862309&-201311058\\
-17055876&-6271221&-4253384&-28617275&-18151931&-29505360&177936953&95164692&-4248451\\
-19245488&1194897&247304&-18935558&3026182&-136862309&95164692&68896484&3681326\\
9155733128&-617434396&-219872052&-204727725&8745853633&-201311058&-4248451&3681326&7248123072
\end{pmatrix}.
$$

$$
\widehat C_{-}=\frac1{10^{10}}\begin{pmatrix}
3561277701&1449512428&-37553907&1439267480&465537946&-40211264&-4473623&-5791877&53322714\\
1449512428&2493898472&382464449&200513426&1509451426&123644038&7182390&-6571805&-334773006\\
-37553907&382464449&11033862973&-129710168&-191091704&4330258924&893336202&282908695&196141669\\
1439267480&200513426&-129710168&2374951943&668071022&-72117980&-35971223&-18037364&176713350\\
465537946&1509451426&-191091704&668071022&2353582411&-178833997&-17253737&-19156908&-866714795\\
-40211264&123644038&4330258924&-72117980&-178833997&2646393661&351935716&250569263&130119907\\
-4473623&7182390&893336202&-35971223&-17253737&351935716&250330865&114297080&266156\\
-5791877&-6571805&282908695&-18037364&-19156908&250569263&114297080&74607056&4062433\\
53322714&-334773006&196141669&176713350&-866714795&130119907&266156&4062433&489243657
\end{pmatrix}.
$$

$$
D_{-}=\frac1{10^{10}}\begin{pmatrix}
6451372806&1465805860&249310080&2804233814&516368270&131966715\\
1465805860&4201210684&-760283791&614616002&2039918254&-386932955\\
249310080&-760283791&20718852257&59582086&-398143734&10341100326\\
2804233814&614616002&59582086&3012658060&1132300831&20304997\\
516368270&2039918254&-398143734&1132300831&1468565836&-209246611\\
131966715&-386932955&10341100326&20304997&-209246611&5164531625
\end{pmatrix}.
$$

$$
\widehat D_{-}=\frac1{10^{10}}\begin{pmatrix}
6356204576&1476956059&85967239&3032686236&663934997&40405645\\
1476956059&4485465931&-1091096764&9049849&1869852558&-531874923\\
85967239&-1091096764&23195679085&121286739&-508038600&11565980383\\
3032686236&9049849&121286739&3369102718&953720314&44923038\\
663934997&1869852558&-508038600&953720314&1254598720&-254624166\\
40405645&-531874923&11565980383&44923038&-254624166&5770272884
\end{pmatrix}.
$$

$$
T_{-}=\frac1{10^{10}}\begin{pmatrix}
4676171991&1914266775&-64220381\\
1914266775&3269909832&664531419\\
-64220381&664531419&6120801000
\end{pmatrix}.
$$

**命题 13.3（精确 LDL 正性）。** 定义 13.1 的 $\Sigma$ 及定义 13.2 的十个矩阵都严格正定。取无主元交换的单位下三角 LDL 分解，按从左上到右下的次序，其枢轴如下。为使大整数保持可读性，每行给一个枢轴，顺序属于紧邻的矩阵。

证明。对任一显示的有理对称矩阵 $X$，以下递推唯一给出其单位下三角因子 $L_X$ 和枢轴 $h_j$：

$$
\begin{aligned}
(L_X)_{jj}&=1,\\
h_j&=X_{jj}-\sum_{k<j}(L_X)_{jk}^2h_k,\\
(L_X)_{ij}&=\frac{X_{ij}-\sum_{k<j}(L_X)_{ik}(L_X)_{jk}h_k}{h_j}
\quad(i>j).
\end{aligned}
\tag{III.13.2}
$$

所有输入条目已完整给出，因此此递推也完整指定 $L_X$，不需要外部因子文件。依次代入产生下列有理数，且重构恒等式 $X=L_X\operatorname{diag}(h_j)L_X^{\mathsf T}$ 逐条成立。每个分子与分母都正，故全部分解合法，Sylvester/LDL 判据给严格正定。

$\Sigma$ 的枢轴：

$$
\begin{gathered}
\frac{1010543356837277}{12500000000000000},\\
\frac{2347591912082712376162614707}{161686937093964320000000000000000},\\
\frac{35299979719763239847334817956066606231477499}{293448989010339047020326838375000000000000000} .
\end{gathered}
$$

$C_{+}$ 的枢轴：

$$
\begin{gathered}
\frac{6021289027}{2500000000},\\
\frac{14531891078634805051}{30106445135000000000},\\
\frac{1664688802018739475507875923}{290637821572696101020000000000},\\
\frac{6897573287672091336839988862863}{3329377604037478951015751846000000000},\\
\frac{17753527619333961657426947676258157}{68975732876720913368399888628630000000000},\\
\frac{2085598981679368214963141214203691949641}{110959547620837260358918422976613481250000000},\\
\frac{72134060395412590169707702271414955627537799}{667391674137397828788205188545181423885120000000000},\\
\frac{37029777921197531112693400148002633584820728869}{360670301977062950848538511357074778137688995000000000},\\
\frac{1903148135689509843296618698983582231118764077183}{14242222277383665812574384672308705224931049565000000000} .
\end{gathered}
$$

$\widehat C_{+}$ 的枢轴：

$$
\begin{gathered}
\frac{27441}{2000000000},\\
\frac{1613180714381}{137205000000000},\\
\frac{46849206692268907388339}{20164758929762500000000},\\
\frac{428245358387464686979930839}{117123016730672268470847500000000},\\
\frac{1111616683525283404383971836831}{4282453583874646869799308390000000000},\\
\frac{112258108436406721598437403474581094841}{44464667341011336175358873473240000000000},\\
\frac{84477111576388784389856589754659037416241}{748387389576044810656249356497207298940000000000},\\
\frac{43708330357321342663410493055058924366905207}{422385557881943921949282948773295187081205000000000},\\
\frac{112735705777605488133962123560285581276889169429}{874166607146426853268209861101178487338104140000000000} .
\end{gathered}
$$

$D_{+}$ 的枢轴：

$$
\begin{gathered}
\frac{43063079}{250000000},\\
\frac{11469750363691679}{17225231600000000000},\\
\frac{653088375116149226639}{114697503636916790000000000},\\
\frac{9437252048373716221352317}{3265441875580746133195000000000},\\
\frac{31395752622745948435547757509}{188745040967474324427046340000000000},\\
\frac{9781352251812040534422531973199}{44851075175351354907925367870000000000} .
\end{gathered}
$$

$\widehat D_{+}$ 的枢轴：

$$
\begin{gathered}
\frac{212055433}{400000000},\\
\frac{24025416963279}{53013858250000000},\\
\frac{1500188358222882859}{300317712040987500000000},\\
\frac{8790853578992595604746727}{3000376716445765718000000000000},\\
\frac{58426189263118070001047019377}{351634143159703824189869080000000000},\\
\frac{127307850317617365850777023923989}{584261892631180700010470193770000000000} .
\end{gathered}
$$

$T_{+}$ 的枢轴：

$$
\begin{gathered}
\frac{27847041}{10000000000},\\
\frac{33681004711859}{27847041000000000},\\
\frac{3959244562000983821}{673620094237180000000000} .
\end{gathered}
$$

$C_{-}$ 的枢轴：

$$
\begin{gathered}
\frac{603073307}{400000000},\\
\frac{16571665265265996263}{75384163375000000000},\\
\frac{32799446988180295279784852469}{47347615043617132180000000000},\\
\frac{459298354067815103096423216723596409819}{2295961289172620669584939672830000000000},\\
\frac{46947061929308800165665211140081955373467555173}{183719341627126041238569286689438563927600000000},\\
\frac{54002154629189440147147600399500978939810235052145029773}{652042526795955557856461265834471602409271599625000000000},\\
\frac{171696808847011668263885683136440169431863248886735801236166219989}{9720387833254099226486568071910176209165842309386105359140000000000},\\
\frac{2959564518402012572475493715959946227021908823633370533484390179513753}{429242022117529170659714207841100423579658122216839503090415549972500000000},\\
\frac{3180532647146943845755252359405619851799774863923500841610921571047351859291}{118382580736080502899019748638397849080876352945334821339375607180550120000000000} .
\end{gathered}
$$

$\widehat C_{-}$ 的枢轴：

$$
\begin{gathered}
\frac{3561277701}{10000000000},\\
\frac{847547342245639711}{4451597126250000000},\\
\frac{74247673635497924437403026787}{67803787379651176880000000000},\\
\frac{25469956798887517660926534033596268497}{148495347270995848874806053574000000000},\\
\frac{131678764995894183525145748115870959734940029087}{1273497839944375883046326701679813424850000000000},\\
\frac{61880217121055448793325391407682038595841892488972040807}{658393824979470917625728740579354798674700145435000000000},\\
\frac{21839284005250595843828286758137448102267874343363418932553868213}{1237604342421108975866507828153640771916837849779440816140000000000},\\
\frac{1474475324051422235187113244257530930445494465755891166650433184875097}{218392840052505958438282867581374481022678743433634189325538682130000000000},\\
\frac{441091364240563885360876200721998256921908475859038244548643390382374909671}{14744753240514222351871132442575309304454944657558911666504331848750970000000000} .
\end{gathered}
$$

$D_{-}$ 的枢轴：

$$
\begin{gathered}
\frac{3225686403}{5000000000},\\
\frac{3119373692477989963}{8064216007500000000},\\
\frac{256246420058081142936987542921}{124774947699119598520000000000},\\
\frac{229784383726350630792770548094335446153}{1281232100290405714684937714605000000000},\\
\frac{65653172139763974446516851753972521691373063}{919137534905402523171082192377341784612000000000},\\
\frac{1973078223374982700836431627713159762098745110930467}{6565317213976397444651685175397252169137306300000000000} .
\end{gathered}
$$

$\widehat D_{-}$ 的枢轴：

$$
\begin{gathered}
\frac{198631393}{312500000},\\
\frac{1053165595035899551}{2542481830400000000},\\
\frac{120569009103422814173520193}{52658279751794977550000000},\\
\frac{435211697343045931327021055043590053}{2411380182068456283470403860000000000},\\
\frac{15660847841692705498788618582216808561735571}{217605848671522965663510527521795026500000000000},\\
\frac{595333981104743175515483857284908138596352052460271}{1957605980211588187348577322777101070216946375000000000} .
\end{gathered}
$$

$T_{-}$ 的枢轴：

$$
\begin{gathered}
\frac{4676171991}{10000000000},\\
\frac{3875414494541671629}{15587239970000000000},\\
\frac{22973347197750174970641778549}{38754144945416716290000000000} .
\end{gathered}
$$

这也证明 $\sigma\succ0$。其迹由 $\operatorname{Tr}(G^{-1}\widetilde\Sigma)=1$ 给出，故中心确为密度矩阵。∎

**定理 13.4（整个原复纤维的充分双侧上界）。** 上述中心满足

$$
\sigma-cI\preceq\rho\preceq\sigma+cI\quad(\rho\in\mathcal K_{5/61}),
\qquad r(5/61)\le2c=\frac{30783}{31250}=0.985056.
\tag{III.13.3}
$$

本证书只主张充分性，不主张正映射分解是原包含问题的必要条件、损失为零的 CP 延拓或最优半径。

证明。对输入 $X\in M_n(\mathbb C)$ 和按输入指标划分的 $3n$ 阶矩阵 $C$，约定

$$
\Phi_C(X)=\sum_{i,j=1}^n X_{ij}C_{ij},\qquad C_{ij}\in M_3(\mathbb C).
\tag{III.13.4}
$$

若 $C\succeq0$，将其 Gram 列按输入指标重排为 Kraus 矩阵便给 $\Phi_C(X)=\sum_lK_lXK_l^\dagger$。这是 Choi/Kraus 正性的成熟工具，文献范围同定义 1.4 的 Watrous 第二章；这里没有要求此映射保迹。复 Hermitian 正矩阵的普通转置仍正，因此 $\Phi_{\widehat C}(X^{\mathsf T})$ 也是所需的正项。

对原六坐标 $\mathbf x=(s,y,w,v,m,n)$，记 $\mathscr R=J\rho J$ 为 (III.8.1)，并令

$$
\begin{gathered}
B(\mathbf x)=\begin{pmatrix}
d_0&-[y+(1+2\tau)s]/2+\mathrm iv\\
-[y+(1+2\tau)s]/2-\mathrm iv&y-\tau^2s
\end{pmatrix},\\
H_B=\begin{pmatrix}1&0\\\tau&1/\alpha\end{pmatrix},\qquad
B=H_B B_{d_0}(\rho)H_B^{\mathsf T}\succeq0,\\
\mathcal P_\epsilon(\mathbf x)=
\Phi_{C_\epsilon}(\mathscr R)+\Phi_{\widehat C_\epsilon}(\mathscr R^{\mathsf T})
+\Phi_{D_\epsilon}(B)+\Phi_{\widehat D_\epsilon}(B^{\mathsf T})+sT_\epsilon\succeq0.
\end{gathered}
\tag{III.13.5}
$$

这里合同矩阵的左下条目是 $+\tau$。正性使用实际共同源的 $\mathscr R\succeq0$、$B\succeq0$、$s\ge0$，而非把这些块视为可分别自由选取的实验输入。

为了完整指定残差各条目，写 $\mathscr R=R_0+\sum_jx_jR_j$、$B=B_0+\sum_jx_jB_j$，其常数和六个系数矩阵为

$$
\begin{gathered}
R_0=\operatorname{diag}(d_0,0,6(1-d_0)),\quad B_0=\operatorname{diag}(d_0,0),\\
R_s=\begin{pmatrix}1&-1/2&4\\-1/2&0&0\\4&0&-6\end{pmatrix},\quad
R_y=\begin{pmatrix}0&-1/2&0\\-1/2&1&0\\0&0&-6\end{pmatrix},\quad
R_w=\begin{pmatrix}0&0&-3\\0&0&1\\-3&1&0\end{pmatrix},\\
R_v=\mathrm i\begin{pmatrix}0&1&0\\-1&0&0\\0&0&0\end{pmatrix},\quad
R_m=\mathrm i\begin{pmatrix}0&0&1\\0&0&0\\-1&0&0\end{pmatrix},\quad
R_n=\mathrm i\begin{pmatrix}0&0&0\\0&0&1\\0&-1&0\end{pmatrix},\\
B_s=\begin{pmatrix}0&-(1+2\tau)/2\\-(1+2\tau)/2&-\tau^2\end{pmatrix},\quad
B_y=\begin{pmatrix}0&-1/2\\-1/2&1\end{pmatrix},\quad
B_v=\mathrm i\begin{pmatrix}0&1\\-1&0\end{pmatrix},\quad B_w=B_m=B_n=0.
\end{gathered}
\tag{III.13.6}
$$

令 $\mathcal F_\epsilon(X,Y)=\Phi_{C_\epsilon}(X)+\Phi_{\widehat C_\epsilon}(X^{\mathsf T})+\Phi_{D_\epsilon}(Y)+\Phi_{\widehat D_\epsilon}(Y^{\mathsf T})$，则下列式子完整给出两个仿射残差，包括它们在 $\mathbb Q(\sqrt2)+\mathrm i\mathbb Q(\sqrt2)$ 中的每个系数：

$$
\begin{aligned}
E_{\epsilon,0}&=\epsilon\Sigma+c_0G-\epsilon R_0-\mathcal F_\epsilon(R_0,B_0),\\
E_{\epsilon,j}&=-\epsilon R_j-\mathcal F_\epsilon(R_j,B_j)
 -\mathbf1_{j=s}T_\epsilon,\\
E_\epsilon(\mathbf x)&=E_{\epsilon,0}+\sum_jx_jE_{\epsilon,j}
 =\epsilon\Sigma+c_0G-\epsilon\mathscr R-\mathcal P_\epsilon(\mathbf x).
\end{aligned}
\tag{III.13.7}
$$

以下表中的整数除以 $10^{12}$，分别上界常数、$s,y,w,v,m,n$ 系数的算子范数：

| $\epsilon$ | 常数 | $s$ | $y$ | $w$ | $v$ | $m$ | $n$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $+1$ | $1185537$ | $907363$ | $801100$ | $400$ | $300$ | $0$ | $200$ |
| $-1$ | $1181030$ | $906031$ | $800550$ | $700$ | $100$ | $100$ | $100$ |

为说明这是一份有理不等式证书，所有 $E_{\epsilon,j}$ Hermitian，故可用

$$
\|E_{\epsilon,j}\|_{\rm op}
 \le\max_a\sum_b|(E_{\epsilon,j})_{ab}|,
\qquad |u+\mathrm iz|\le|u|+|z|.
\tag{III.13.8}
$$

将 (III.13.6)–(III.13.7) 的条目代入，并对每个 $\sqrt2$ 使用

$$
\frac{1414213562373095048801688724209}{10^{30}}
 <\sqrt2<
\frac{1414213562373095048801688724210}{10^{30}},
\tag{III.13.9}
$$

即可按三行绝对值和分别比较上表；(III.13.9) 的两个端点平方分别小于和大于二。因此表格是明确条目的有理行和界，不是数值特征值或求解器判词。

实际密度正性给 $0\le\rho_{ii}\le1$、$|\rho_{ij}|\le1/2$，故

$$
|s|\le1,\quad |y|\le1,\quad |w|,|m|,|n|\le\sqrt6/2<5/4,
\quad |v|\le1/2.
\tag{III.13.10}
$$

这些粗界同时适用于所有原复源。将表格按它们加权，得到

$$
\begin{aligned}
\|E_+(\mathbf x)\|_{\rm op}&\le\frac{28949}{10000000000}<\delta_0,\\
\|E_-(\mathbf x)\|_{\rm op}&\le\frac{1444393}{500000000000}<\delta_0.
\end{aligned}
\tag{III.13.11}
$$

由 $G\succeq I$ 和 $\mathcal P_\epsilon\succeq0$，

$$
\epsilon\Sigma+cG-\epsilon\mathscr R
 =\mathcal P_\epsilon+E_\epsilon+\delta_0G\succeq0.
\tag{III.13.12}
$$

两种符号给全部原源上的双侧区间。合同 $J^{-1}$ 和 (III.1.6) 将它传到不除以二的迹风险、diamond 风险和全部有限未触动参考，得 (III.13.3)。此过程既未假定 $\Sigma\in J\mathcal K_dJ$，也未把 CP/co-CP 充分条件当作损失为零的全问题约化。∎

**推论 13.5（原问题的严格点括号及其非匹配性）。**

$$
\frac{9840437}{10000000}<r(5/61)\le\frac{30783}{31250}.
\tag{III.13.13}
$$

证明。定理 12.2 和定理 13.4 的原问题量词与范数对应相同，故可直接组合。下证书是 $M\prec\kappa I$ 的谱松弛，以上中心只被证明可行；上下端不相等，所以这里既没有选出最优中心，也没有证明任何测试方向是最优接触。∎


## 14. 完整原虚坐标的精确纤维与奇异边界

**定义 14.1（三实投影及虚向量）。** 对任意 $0<d<1$，保留 (III.8.1) 的全部六个原实坐标，写

$$
\begin{gathered}
J=\operatorname{diag}(1,1,\sqrt6),\quad G=J^2,\quad
\mathscr R=J\rho J=S+\mathrm i\operatorname{cross}(t),\quad t=(-n,m,-v)^{\mathsf T},\\
S=S(s,y,w)=\begin{pmatrix}
d+s&-(s+y)/2&4s-3w\\
-(s+y)/2&y&w\\
4s-3w&w&6(1-d-s-y)
\end{pmatrix},\\
\operatorname{cross}(t)=\begin{pmatrix}
0&-t_3&t_2\\t_3&0&-t_1\\-t_2&t_1&0
\end{pmatrix},\quad E_{33}=e_3e_3^{\mathsf T},\\
b=d(y-\tau^2s)-\frac{[y+(1+2\tau)s]^2}{4},\quad
\mathcal P_d=\{(s,y,w):S\succeq0,\ s\ge0,\ b\ge0\},\\
A_S=S_{\{a,h\}},\quad \delta=\det A_S,\quad
L=\ell^{\mathsf T}J^{-1}SJ^{-1}\ell,\qquad a_S=\det S.
\end{gathered}
\tag{III.14.1}
$$

$D$ 在下文的 $\Phi(S,D,b)$ 中表示任意实对称目标矩阵，与原提升 (III.11.2) 中的正矩阵 $D$ 作用不同。$a_S$ 也不同于单位基向量 $a$。

**定理 14.2（精确实投影、椭球及全部秩层）。** 原完整 $\mathcal K_d$ 在 $(s,y,w)$ 上的投影恰为 $\mathcal P_d$。对每个该投影点，原虚坐标纤维恰由

$$
S+\mathrm i\operatorname{cross}(t)\succeq0,\qquad t_3^2\le b
\tag{III.14.2}
$$

给出。若 $S\succ0$，第一条又恰等价于 $t^{\mathsf T}St\le a_S$。若 $\operatorname{rank}S=2$，取任一实单位核向量 $u$，则精确纤维为

$$
t=\theta u,\qquad \theta^2\le e_2(S),\qquad \theta^2u_3^2\le b,
\quad e_2(S)=\sum_{|I|=2}\det S_I.
\tag{III.14.3}
$$

若秩一，则只有 $t=0$；秩零不属于原投影。

证明。对实向量测试 $\mathscr R\succeq0$ 给 $S\succeq0$。原 (III.8.4) 的合同矩阵 (III.13.5) 给

$$
\det B_d(\rho)=\alpha^2(b-v^2),\qquad
\frac{L}{\alpha^2}=(1+\tau)y+\tau^2d+\tau(1+\tau)s>0,
\qquad \delta-b=\frac{sL}{\alpha^2}.
\tag{III.14.4}
$$

因 $d>0$，$B_d\succeq0$ 的条件就是 $v^2\le b$；其另一对角条件已由该行列式条件推出。反之，对 $\mathcal P_d$ 中任一点取 $t=0$，即得 (III.8.1)–(III.8.2) 的一个实际原源。由命题 8.2 的忠实双射，投影是精确的，且每个允许的 $t$ 都有原域提升。

对任意实对称三阶矩阵 $D$，直接按行列式展开有多项式恒等式

$$
\det(D+\mathrm i\operatorname{cross}(t))
 =\det D-t^{\mathsf T}Dt.
\tag{III.14.5}
$$

当 $S\succ0$ 时，合同 $S^{-1/2}$ 把第一条变为 $I+\mathrm iK$，其中 $K$ 为实反对称矩阵。三维叉乘的合同恒等式给 $\mathrm iK$ 的特征值 $0,\eta,-\eta$，其中 $\eta^2=t^{\mathsf T}St/\det S$。所以 $I+\mathrm iK\succeq0$ 恰等价于 $\eta\le1$，包含等号边界，得到所述椭球。这是只在 $S\succ0$ 使用的合同；不会对奇异 $S$ 求逆。

若 $S$ 秩二，$u^{\mathsf T}\mathscr Ru=0$ 和正性给 $\mathscr Ru=0$，于是 $\operatorname{cross}(t)u=0$，即 $t=\theta u$。在以 $u$ 为第三轴的实正交基中，正的二阶实块加纯虚反对称部分，其行列式为两个正特征值之积减 $\theta^2$。该积正是 $e_2(S)>0$，故得到 (III.14.3) 的充分性及必要性。若秩一，二维实核必须同时被 $\operatorname{cross}(t)$ 消去；非零三维反对称矩阵的核只有一维，故只能 $t=0$。最后，$S_{11}=d+s>0$ 且 $\operatorname{Tr}(G^{-1}S)=1$，排除秩零。∎

**定义 14.3（分层的精确虚最大值）。** 对任意实对称 $D$，在定理 14.2 的真实虚纤维上定义

$$
\Phi(S,D,b)=\max_t t^{\mathsf T}Dt.
\tag{III.14.6}
$$

其值非负，因为 $t=0$ 可行。若 $S\succ0,b=0$，记 $D_A=D_{\{a,h\}}$，则

$$
\Phi(S,D,0)=a_S\max\{0,\lambda_{\max}(D_A,A_S)\}.
\tag{III.14.7}
$$

这里 $\lambda_{\max}(D_A,A_S)=\lambda_{\max}(A_S^{-1/2}D_AA_S^{-1/2})$，只在 $A_S\succ0$ 时使用。若 $S$ 秩二，定义

$$
q_u=\begin{cases}
\min\{e_2(S),b/u_3^2\},&u_3\ne0,\\
e_2(S),&u_3=0,
\end{cases}
\qquad
\Phi(S,D,b)=\max\{0,u^{\mathsf T}Du\}\,q_u.
\tag{III.14.8}
$$

若秩一，则 $\Phi=0$。式中没有在 $u_3=0$ 时进行除法。

**命题 14.4（零超额的冗余薄板及其确定性条件）。** 在所有实际源秩上，$s=0$ 时约束 $t_3^2\le b$ 冗余。若另有 $S\succ0$，

$$
\Phi(S,D,b)=a_S\max\{0,\lambda_{\max}(S^{-1/2}DS^{-1/2})\}.
\tag{III.14.9}
$$

奇异 $s=0$ 必须使用 (III.14.8) 或秩一公式，不能使用 (III.14.9) 的逆矩阵。

证明。由 (III.14.4)，$s=0$ 给 $b=\delta$。当 $S\succ0$，椭球上 $t_3^2$ 的最大值是 $a_S(S^{-1})_{33}=\operatorname{adj}(S)_{33}=\delta$。当秩二，$\operatorname{adj}(S)=e_2(S)uu^{\mathsf T}$，所以 (III.14.3) 给最大值 $e_2(S)u_3^2=\delta$；秩一时 $t=0$ 且 $b=\delta=0$。正定情形去掉冗余约束后，谱分解和缩放球上的 Rayleigh 商给 (III.14.9)；零向量给零备选值。原 $\mathsf R_0$ 的复混合态仍包含在此纤维，中心可取实从未将它们删除。∎

## 15. 原纤维的无损齐次 SDP 与零薄板非达到性

**定理 15.1（正定正薄板域的无损实提升及达到对偶）。** 对定理 14.2 的 $S\succ0,b>0$ 和任意实对称 $D$，

$$
\begin{aligned}
\Phi(S,D,b)
 &=\max\{\operatorname{Tr}(DX):X\succeq0,\
       \operatorname{Tr}(SX)\le a_S,\ X_{33}\le b,\ X\in\operatorname{Sym}_3(\mathbb R)\}\\
 &=\min\{a_S\lambda+b\mu:\lambda,\mu\ge0,\
       \lambda S+\mu E_{33}-D\succeq0\}.
\end{aligned}
\tag{III.15.1}
$$

两次最大值与这个最小值均达到。实提升的无损性属于这个固定原虚纤维的齐次两约束问题，不是一般两约束 S 引理或原源 CP 延拓的无损性结论。

证明。$X=tt^{\mathsf T}$ 给原虚向量的可行提升。反过来，因 $S\succ0$，可行 $X$ 的迹被 $a_S/\lambda_{\min}(S)$ 界住，故可行集非空紧凸，线性目标有极端最优点。若一个极端点秩 $r\ge2$，其支撑上的实对称扰动空间维数为 $r(r+1)/2\ge3$；至多两个活动标量不等式对扰动施加至多两个齐次线性条件。取其共同核中的非零扰动，沿正负方向充分小地移动，保持支撑内正性、活动等式及所有非活动严格不等式，便与极端性矛盾。因此存在秩至多一的最优 $X$。秩一时写成 $tt^{\mathsf T}$，秩零时取 $t=0$，即得无损性。

普通有限维 SDP 对偶以 $\lambda,\mu\ge0$ 对应两个上界，拉格朗日函数为

$$
a_S\lambda+b\mu+
\operatorname{Tr}[(D-\lambda S-\mu E_{33})X].
\tag{III.15.2}
$$

对 $X\succeq0$ 的上确界有限恰要求所示对偶 PSD 条件。因为 $a_S>0,b>0$，充分小的 $X=\varepsilon I\succ0$ 同时使两个不等式严格，故原 SDP 满足 Slater 条件；取充分大的 $\lambda$ 和任意正 $\mu$ 也给严格对偶可行点。有限值及 Slater 强对偶给相等并给对偶达到。也可在相等后利用 $a_S,b>0$ 将对偶次水平集限制为紧集。这使用成熟锥对偶与 Slater 工具，例如 Boyd–Vandenberghe, [*Convex Optimization*](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf)，§5.2.3、§5.9；支撑扰动的维数论证已在本源上完整给出，不将通用工具冒称本项目发明。∎

**命题 15.2（零薄板的正确约化及三维对偶达到判据）。** 若 $S\succ0,b=0$，(III.14.7) 是达到的二维问题；其一乘子对偶同样达到。定义

$$
\begin{gathered}
\lambda_* =\max\{0,\lambda_{\max}(D_A,A_S)\},\\
A_* =\lambda_*A_S-D_A,\qquad
\beta_* =\lambda_*S_{\{a,h\},g}-D_{\{a,h\},g}.
\end{gathered}
\tag{III.15.3}
$$

未约化三维对偶的下确界仍为 $a_S\lambda_*$，但其最小值存在当且仅当 $\beta_*\in\operatorname{ran}A_*$。因此不能在 $b=0$ 无条件使用 (III.15.1) 的三维“min”。

证明。$b=0$ 强制 $t_3=0$，由 $A_S\succ0$ 的二维 Rayleigh 商直接得 (III.14.7)。二维对偶是 $\min\{a_S\lambda:\lambda\ge0,\lambda A_S-D_A\succeq0\}$，显然在 $\lambda_*$ 达到。三维对偶的左上块必须正，故必有 $\lambda\ge\lambda_*$。在 $\lambda=\lambda_*$，正半定块矩阵的精确 Schur 判据是

$$
\beta_*\in\operatorname{ran}A_*,\qquad
\mu\ge D_{gg}-\lambda_*S_{gg}+\beta_*^{\mathsf T}A_*^\dagger\beta_*.
\tag{III.15.4}
$$

另取 $\mu\ge0$ 即可。若范围条件失败，则此处没有任何有限 $\mu$ 可行。对每个 $\lambda>\lambda_*$，左上块严格正，所以总有有限 $\mu$ 使对偶可行；令 $\lambda\downarrow\lambda_*$ 给同一下确界，却不能在端点达到。这正是缺少三维严格原可行性的后果，不能用对偶值相等代替达到性。∎

**命题 15.3（实际中央源排除两种错误边界推广）。** 以下两个例子都属于原 $\mathcal K_d$，各自中心是实际密度中心；因此奇异源和零薄板的分支不是只为抽象锥边界保留的形式例外。

证明。第一个例子取 $d=1/4$，令

$$
\begin{gathered}
s=\frac{3+2\sqrt2}{32},\quad y=\frac{11-2\sqrt2}{32},\quad w=1/4,\quad v=m=n=0,\\
S=\begin{pmatrix}
(11+2\sqrt2)/32&-7/32&(2\sqrt2-3)/8\\
-7/32&(11-2\sqrt2)/32&1/4\\
(2\sqrt2-3)/8&1/4&15/8
\end{pmatrix}.
\end{gathered}
\tag{III.15.5}
$$

这里 $b=0$，$s>0$，加权迹一；$S$ 的顺序主子式为

$$
\frac{11+2\sqrt2}{32},\quad\frac1{16},\quad
\frac{45}{2048}+\frac{51\sqrt2}{1024},
$$

均严格正，所以 $S\succ0$，定理 14.2 给实际原源。取

$$
\begin{gathered}
c=1/1000,\quad \varepsilon=1/10000,\quad
D_+=\begin{pmatrix}0&0&\varepsilon\\0&0&0\\\varepsilon&0&18c\end{pmatrix},\qquad
\Sigma=S-cG+D_+.
\end{gathered}
\tag{III.15.6}
$$

$\operatorname{Tr}(G^{-1}\Sigma)=1$，且 $\Sigma$ 的顺序主子式为

$$
\frac{1371}{4000}+\frac{\sqrt2}{16},\quad
\frac{123627}{2000000},\quad
\frac{8710548429}{400000000000}+\frac{79352581\sqrt2}{1600000000},
$$

均正，故这是严格正的合法中心。在这个实际 $D_+=\Sigma+cG-S$ 上，$\lambda_*=0$、$A_*=0$ 而 $\beta_*=(-\varepsilon,0)^{\mathsf T}\ne0$。于是 $\Phi=0$，未约化三维对偶下确界为零却不达到。这个例子不声称 $c$ 已覆盖完整源；它反驳的是将三维达到公式无条件推广到 $b=0$。

第二个例子也取 $d=1/4$，但令 $s=y=w=v=m=n=0$。则

$$
S=\operatorname{diag}(1/4,0,9/2),\quad b=0,\quad
\Sigma=S,\quad c=1/10,\quad D_-=S-\Sigma+cG=cG.
\tag{III.15.7}
$$

该实际源及中心均对应密度 $\operatorname{diag}(1/4,0,3/4)$。秩二核为 $e_2$，$e_2(S)=9/8$，由 (III.14.8)，真实 $\Phi=9/80$。若将 (III.15.1) 的提升盲目用于奇异 $S$，约束 $\operatorname{Tr}(SX)\le\det S=0$、$X_{33}\le0$ 却允许任意 $X=k e_2e_2^{\mathsf T}$、$k\ge0$，目标为 $k/10$ 无上界。遗漏的是秩二纤维中的 $\theta^2\le e_2(S)$，不能由把正定椭球公式中的 $\det S$ 置零来补回。

此外，秩一确实在中央域出现：$d=1/5,s=w=v=m=n=0,y=4/5$ 给 $S=\frac15(1,-2,0)^{\mathsf T}(1,-2,0)$，其唯一虚向量为零。以上 $1/4$、$1/5$ 都严格位于 $(d_s,2/7)$，故分层覆盖与原目标的参数域直接相关。∎


## 16. 两个全源三次式与有限四次内层候选

**定理 16.1（全五中心方向的精确三实源外层条件）。** 给定 $0<d<1$、$c>0$ 及任意实对称加权归一中心

$$
\Sigma=\begin{pmatrix}
a_c&b_c&p_c\\b_c&h_c&q_c\\p_c&q_c&6(1-a_c-h_c)
\end{pmatrix}\succeq0,\qquad \sigma=J^{-1}\Sigma J^{-1},
\tag{III.16.1}
$$

令 $D_+=\Sigma+cG-S$、$D_-=S-\Sigma+cG$。则原完整包含恰等价于

$$
\begin{aligned}
\det D_+&\ge\Phi(S,D_+,b),\\
\det D_-&\ge\Phi(S,D_-,b)
\end{aligned}
\qquad\text{对每个 }(s,y,w)\in\mathcal P_d.
\tag{III.16.2}
$$

这里 $\Phi$ 按正定、零薄板、秩二及秩一各分支定义，没有要求 $D_+$ 或 $D_-$ 正定，也没有要求中心属于 $\mathcal K_d$。实中心的五方向平均论证仅引用命题 8.2；源仍保留原全部六个实坐标。

证明。命题 8.3 已证明 $c>0$ 时两个三次行列式非负恰等价于原双侧序包含，不重证这个原桥梁。对固定实投影，两个差矩阵为 $D_+-\mathrm i\operatorname{cross}(t)$ 和 $D_-+\mathrm i\operatorname{cross}(t)$。(III.14.5) 对两种符号给同一形式 $\det D_\pm-t^{\mathsf T}D_\pm t$。定理 14.2 精确穷尽对应的实际虚纤维，故在它上取最大值恰得 (III.16.2)。该步骤消去三个虚变量，没有将它们取零。原加权迹一、$c>0$ 和成对条件都不可省；$c=0$ 的一般谱反例已由命题 8.3 给出。∎

**定义 16.2（正内部的一变量多项式）。** 固定一个 $S\succ0,b>0,s>0$ 的投影点及任意实对称 $D$。写

$$
\begin{gathered}
A(\lambda)=\lambda A_S-D_A,\quad
\beta(\lambda)=\lambda S_{\{a,h\},g}-D_{\{a,h\},g},\\
\lambda_0=\max\{0,\lambda_{\max}(D_A,A_S)\},\\
F_0(\lambda)=\det(\lambda S-D),\qquad
F_1(\lambda)=\det(\lambda A_S-D_A),\\
P(\lambda)=a_S F_1(\lambda)^2
 -b\bigl[F_0'(\lambda)F_1(\lambda)-F_0(\lambda)F_1'(\lambda)\bigr].
\end{gathered}
\tag{III.16.3}
$$

在对偶域 $\lambda\ge0$ 内，$A(\lambda)\succeq0$ 恰要求 $\lambda\ge\lambda_0$。各多项式的系数由已给 $S,D,b$ 决定；$F_0$ 为首项系数 $a_S>0$ 的三次式，$F_1$ 为首项系数 $\delta>0$ 的二次式。

**定理 16.3（有限四次、三次、二次候选的完整内层求值）。** 在定义 16.2 的域上，构造下列有限非负实数集合，保留重根对应的候选值：

$$
\Lambda=\{0,\lambda_0\}
 \cup\{\lambda\ge0:F_0(\lambda)=0\}
 \cup\{\lambda\ge0:P(\lambda)=0\}
 \cup\{\lambda\ge0:F_1(\lambda)=0\}.
\tag{III.16.4}
$$

对每个候选作以下精确过滤及赋值。若 $A(\lambda)\not\succeq0$ 则丢弃。若 $A(\lambda)\succ0$，令

$$
\mu_\lambda=\max\{0,-F_0(\lambda)/F_1(\lambda)\}.
\tag{III.16.5}
$$

若 $A(\lambda)$ 奇异，则必须先满足 $\beta(\lambda)\in\operatorname{ran}A(\lambda)$，否则丢弃；满足时令

$$
\mu_\lambda=\max\{0,D_{gg}-\lambda S_{gg}
 +\beta(\lambda)^{\mathsf T}A(\lambda)^\dagger\beta(\lambda)\}.
\tag{III.16.6}
$$

对赋值后的每项还保留完整条件 $\lambda S+\mu_\lambda E_{33}-D\succeq0$。那么

$$
\Phi(S,D,b)=\min_{\lambda\in\Lambda\text{ 且通过过滤}}
  [a_S\lambda+b\mu_\lambda].
\tag{III.16.7}
$$

这个有限最小集合非空。特别地，在这个正内部域，$P$ 的首项系数严格为正：

$$
[\lambda^4]P=a_S\delta(\delta-b)
 =\frac{a_S\delta sL}{\alpha^2}>0.
\tag{III.16.8}
$$

证明。按最后一个对角条目展开得到精确恒等式

$$
\det(\lambda S+\mu E_{33}-D)=F_0(\lambda)+\mu F_1(\lambda).
\tag{III.16.9}
$$

当 $A\succ0$，Schur 补给

$$
\mu\ge D_{gg}-\lambda S_{gg}+\beta^{\mathsf T}A^{-1}\beta
 =-F_0/F_1.
$$

因为此处分母 $F_1>0$，这才允许进行除法，并得到最小非负 $\mu$ 的 (III.16.5)。当 $A$ 奇异，精确 PSD Schur 判据是范围条件加 (III.16.6) 的下界。对二阶秩一正矩阵，

$$
A^\dagger=\frac{A}{(\operatorname{Tr}A)^2};
$$

若 $A=0$，必须 $\beta=0$，取 $A^\dagger=0$；这时 (III.16.6) 仍适用。范围条件等价于 $(I-AA^\dagger)\beta=0$。因此即使二次根重复，零行列式也没有替代范围检验；不存在在 $F_1=0$ 时静默约掉分母的步骤。

定理 15.1 保证对偶最优达到。在 $A\succ0,\mu_\lambda>0$ 的开区间上，约化目标的导数为

$$
\frac{d}{d\lambda}(a_S\lambda-bF_0/F_1)=\frac{P(\lambda)}{F_1(\lambda)^2}.
\tag{III.16.10}
$$

所以正 $\lambda$ 的内部最小值必须是四次根。在 $A\succ0,\mu_\lambda=0$ 的开区间上，目标为严格递增的 $a_S\lambda$，不会有新的内部最小值。其有限边界只能是 $\lambda=0$、零乘子转换 $F_0=0$ 或奇异块 $F_1=0$；$\lambda_0$ 明列出左可行端点。目标至少为 $a_S\lambda$，所以 $\lambda\to\infty$ 时发散，不存在漏掉的无穷端点最优。最后由 (III.14.4) 展开首项得到 (III.16.8)，保证 $P$ 真正为四次，不能整式为零。三次及二次式也因各自正首项系数不会整式为零。这穷尽了每个最优所在分支，证明有限列表完整。∎

**命题 16.4（内层列表的全边界路由）。** 对定理 16.1 的每个实际实源，按以下互相覆盖的公式求 $\Phi$，没有丢弃任何原边界：秩一用 $\Phi=0$；秩二用 (III.14.8)；$S\succ0,b=0$ 用 (III.14.7)；$S\succ0,b>0,s=0$ 用 (III.14.9)；$S\succ0,b>0,s>0$ 用定理 16.3。

证明。$\mathcal P_d$ 中 $s,b\ge0$，$S\succeq0$ 且秩零不存在，所以这些情形穷尽。秩二且 $u_3\ne0,b=0$ 时 $q_u=0$；$u_3=0,b=0$ 时仍有整段 $\theta^2\le e_2(S)$，不可一概取零。秩二的三阶伴随公式、秩一的二维核论证和零薄板的范围条件均由 §§14–15 给出。当 $s=0$，(III.16.8) 的四次首项消失，故另用有正定性假设的单椭球公式；它不是无条件的四次正首项域。这一列表只需在固定系数域上的实根、符号、PSD 和范围判别。对代数输入，可在其有序系数域的实闭包内执行有限根选取；对任意未给可计算表示的实参数，不另作算法可计算性断言。∎

## 17. 保留的完整中央目标与模型前提

**定义 17.1（仍待构造的外层原最小最大关系）。** 原目标保持为：对每个

$$
\frac{500}{7333+828\sqrt2}=d_s<d<\frac27,
\tag{III.17.1}
$$

求实际达到的五实坐标密度中心 $\sigma_*(d)$ 和半径 $c_*(d)>0$，证明所有六实坐标原源上的

$$
\sigma_*(d)-c_*(d)I\preceq\rho\preceq\sigma_*(d)+c_*(d)I,
\qquad
r(d)=2c_*(d),
\tag{III.17.2}
$$

并给对所有复密度中心、因而对所有原共同 CPTP 重建的匹配下证书。三实源外层全称优化与五实中心最小化仍未求解，包含 $d=5/61$。定理 16.3 只是固定实投影及固定中心后的有限虚内层求值，不是这两个外层的有限最优解。定理 13.4 的可行中心与定理 12.2 的松弛下界没有相遇，故也没有完成 (III.17.2)。§9 的接触存在性、实代数存在性及预序/Positivstellensatz 接口是既有供应，不将它们重新列为本中央目标的实际构造。

**假设 17.2（量子结构、共同实现与取得性）。** §§11–16 条件地使用原复 Hilbert 空间、密度矩阵、Born 效果配对、CPTP 动力学与组合、同一固定原源，以及原擦除标签菜单的精确全深度输入效果数据。它们都保留为前提。所有 Gram 列、六坐标、原 CPTP 提升及风险证书属于同一原家族；正性证书不引入新的原生制备、相位控制、复制、相关副本、参考制备、返回环境、标签历史或源独立权限。存在正映射、效果、通道或数学提升不等于已经取得对应的操作或精确数据。

**定义 17.3（成果范围与数学归属）。** 新的具体内容是 (III.11.1)–(III.11.7) 的整段实际混合族、(III.12.1)–(III.12.11) 的四世界谱松弛及统一超额、(III.13.1)–(III.13.13) 的完整充分上证书，以及 §§14–16 对原六坐标纤维的分层消元与有限内层构造，归为 `repo-derived`。有限维谱分解、PSD 主子式与 Schur 补、Moore–Penrose 范围判据、Kraus/Choi 表示、支撑秩扰动、凸紧性及 Slater 对偶均是成熟工具，在相应证明中归属并限定其条件；不主张这些工具或源特定应用具有文献优先权。本卷给出普通条件数学，没有新增 Lean/kernel 结论。

仍存的起源问题是：哪些实际取得的关系数据在原菜单与共同来源条件下能够约束隐藏的 $s$ 和 $\Re(\rho_{ag}+3\rho_{hg})=4s/\sqrt6$，并解释为何应采用这里预设的复量子组合与 Born 配对？这些上下界与无损内层关系没有推出量子原则的物理起源、经验有效性、信息守恒，或完整持续目标的满足。

## 追加锚（本行以下为增补区）

## 18. 原复源的余因子与人口上限

以下均在原正交基 $(a,h,g)$ 中使用未作 $J$ 合同的矩阵。原集合始终是 (III.1.4) 的 $\mathcal K_d$，$0<d<1$；其忠实坐标、全部复极端层、五维提升及任意共同重建的约化分别由命题 8.2、母卷定理 36.2 和 (III.1.6) 供应。§§19–20 的两段精确解使用同一集合；§§21–22 给出该集合的另一种完整包含判据。

**命题 18.1（实际源的共同块余因子不等式）。** 记

$$
\begin{gathered}
\tau=3-2\sqrt2>0,\quad \alpha=(2+\sqrt2)/\sqrt{12},\quad
\ell=\alpha(-\tau,1,0)^{\mathsf T},\\
s=\rho_{aa}-d,\quad y=\rho_{hh},\quad v=\Im\rho_{ah},\quad
A=\rho_{\{a,h\}},\quad \delta=\det A,\quad L_\rho=\ell^\dagger\rho\ell.
\end{gathered}
\tag{III.18.1}
$$

每个实际源满足

$$
\begin{gathered}
A=\begin{pmatrix}d+s&-(s+y)/2+\mathrm iv\\-(s+y)/2-\mathrm iv&y\end{pmatrix},\\
\frac{L_\rho}{\alpha^2}=(1+\tau)y+\tau(1+\tau)s+\tau^2d>0,\\
\det B_d(\rho)=\alpha^2\delta-sL_\rho\ge0,\qquad
\delta\ge sL_\rho/\alpha^2.
\end{gathered}
\tag{III.18.2}
$$

若 $\operatorname{rank}\rho\le2$，则对任意正定块对角矩阵

$$
H=\begin{pmatrix}H_2&0\\0&h_g\end{pmatrix}\succ0
\quad(H_2\in\operatorname{Herm}_2(\mathbb C),\ h_g>0)
\tag{III.18.3}
$$

有

$$
\begin{aligned}
\det(H-\rho)
&=\det H\,[1-\operatorname{Tr}(H^{-1}\rho)]
  +h_g\delta+\operatorname{Tr}\bigl(H_2\operatorname{adj}(\rho)_{ah}\bigr)\\
&\ge h_gs\bigl[(1+\tau)y+\tau(1+\tau)s+\tau^2d\bigr]
 -\det H\,[\operatorname{Tr}(H^{-1}\rho)-1].
\end{aligned}
\tag{III.18.4}
$$

证明。原 $C$ 矩给 $\Re\rho_{ah}=-(s+y)/2$。直接展开 $\ell^\dagger\rho\ell$ 即得 (III.18.2) 第二式；其中 $y,s\ge0$ 且 $d>0,\tau>0$，所以严格为正。$B_d$ 是 (III.8.4) 的同一矩阵，因而

$$
B_d(\rho)=
\begin{pmatrix}
d&\alpha[-\tau(d+s)-(s+y)/2+\mathrm iv]\\
\alpha[-\tau(d+s)-(s+y)/2-\mathrm iv]&L_\rho
\end{pmatrix}.
$$

其行列式展开为 $\alpha^2\delta-sL_\rho$，得到全部源恒等式，没有对 $A$ 求逆。

三阶行列式的混合展开恒等式为

$$
\det(H-\rho)=\det H-\operatorname{Tr}(\operatorname{adj}(H)\rho)
 +\operatorname{Tr}(H\operatorname{adj}(\rho))-\det\rho.
$$

这里 $H$ 可逆，所以第二项等于 $\det H\operatorname{Tr}(H^{-1}\rho)$。秩至多二时 $\det\rho=0$。由 $\rho\succeq0$ 的谱分解，$\operatorname{adj}(\rho)\succeq0$：秩二时其唯一非零特征值为两个正特征值之积，秩一时整个伴随矩阵为零。因此其 $ah$ 主块半正定，且

$$
\operatorname{Tr}(H\operatorname{adj}(\rho))
=h_g\operatorname{adj}(\rho)_{gg}
 +\operatorname{Tr}(H_2\operatorname{adj}(\rho)_{ah})
\ge h_g\delta.
$$

再用 (III.18.2) 即得 (III.18.4)。这是原源的充分行列式下界；原 $ag,hg,ah$ 的全部复相干仍在 $\rho$ 和伴随矩阵内。奇异 $A$、纯态及 $\det B_d=0$ 都不要求额外除法。∎

**命题 18.2（原人口上限所给的完整下侧包含）。** 对每个实际 $\rho\in\mathcal K_d$，

$$
\rho_{gg}\ge1-5d.
\tag{III.18.5}
$$

因此，当 $0<d<1/10$，令

$$
q=5d,\quad \beta=1-q,\quad c=\sqrt{q\beta},\quad
w=(a-2h)/\sqrt5,\quad z_0=(2a+h)/\sqrt5,\quad
\sigma=qww^\dagger+\beta gg^\dagger,
\tag{III.18.6}
$$

则所有复混合源都满足 $\rho-\sigma+cI\succeq0$。

证明。写 $u_0=y+(1+2\tau)s$。由原 $B_d$ 条件 (III.8.2)，

$$
\frac{u_0^2}{4}+v^2
\le d\bigl[u_0-(1+\tau)^2s\bigr]\le du_0.
\tag{III.18.7}
$$

$s,y\ge0$ 给 $u_0\ge0$；上式给 $u_0\le4d$，包括 $u_0=0$。又 $s+y\le u_0$，所以 $\rho_{gg}=1-d-s-y\ge1-5d$。这里没有以人口条件替代原源正性；它只是完整原约束的一个推论。

下面在这个人口约束上消费等期望纯态分解，给出下侧包含的全部符号条件。一般地，设 $0<q<1/2$、$\beta=1-q$、$c=\sqrt{q\beta}$，且 $w,z_0,g$ 正交。对任意密度 $\rho$，置 $p=\rho_{gg}$。迹零 Hermitian 矩阵

$$
B_0=\rho^{1/2}(gg^\dagger-pI)\rho^{1/2}
$$

有一个对角全零的正交基：若它不为零，在最小和最大 Rayleigh 向量之间取一个零 Rayleigh 单位向量；在其正交补上的压缩仍迹零，归纳即可。压缩为零时任取余下基。故对该基 $(e_j)$，丢弃 $p_j=\|\rho^{1/2}e_j\|^2=0$ 的项，得到

$$
\rho=\sum_jp_j\psi_j\psi_j^\dagger,\quad
\psi_j=\rho^{1/2}e_j/\sqrt{p_j},\quad
\sum_jp_j=1,\quad |\langle g,\psi_j\rangle|^2=p.
\tag{III.18.8}
$$

该构造同定理 2.1 的等期望步骤，对奇异密度也成立；此处每项只须保留 $g$ 期望，不须分别保留其他原矩。

设 $K=cI-\sigma$。在 $(w,z_0,g)$ 中，$K$ 的特征值为 $c-q,c,c-\beta$。因 $q<1/2$，前两个严格正，最后一个严格负，三者均非零。对纯向量 $\psi=(u,t)$，其中 $u\in\operatorname{span}\{w,z_0\}$、$|t|^2=p$，正的左上块 $K_2+uu^\dagger$ 的 Schur 补是

$$
c-\beta+\frac{p}{1+u^\dagger K_2^{-1}u}.
$$

于是 $K+\psi\psi^\dagger\succeq0$ 恰等价于

$$
1+\psi^\dagger K^{-1}\psi\le0.
$$

这里不等号的方向来自 $c-\beta<0$。并且

$$
\begin{aligned}
1+\psi^\dagger K^{-1}\psi
&\le f(p):=1+\frac{1-p}{c-q}+\frac{p}{c-\beta},\\
f'(p)&=\frac1{c-\beta}-\frac1{c-q}<0,\qquad
f(\beta)=0.
\end{aligned}
\tag{III.18.9}
$$

最后一等式以公分母展开后用 $c^2=q\beta$ 得到。因此 $p\ge\beta$ 时每个纯分量均满足下侧包含，凸性和 (III.18.8) 给全部密度的结论，包括 $p=\beta$ 与 $p=1$。代入 (III.18.5) 即为所需原源结论。

$q=1/2$ 时该逆矩阵论证不使用，因为 $K$ 有零特征值；此时 $K\succeq0$ 直接给结论。$q>1/2$ 时不能沿用此论证或结论：$\rho=qz_0z_0^\dagger+\beta gg^\dagger$ 满足同一 $g$ 人口，但 $\rho-\sigma+cI$ 在 $w$ 方向的值 $c-q<0$。§19 的整个参数域严格满足 $q<1/2$。∎

**命题 18.3（从实际低秩叶到全部复混合源）。** 若固定 $\sigma,c$ 的两侧 Loewner 包含在原三个极端层上成立，则它们在全部 $\mathcal K_d$ 上成立。这个结论包含原秩三非极端态和奇异 $ah$ 块态。

证明。母卷定理 36.2 已给三个极端层的完整分类，均秩至多二。为明确有限凸分解所覆盖的对象，使用同一定理中的仿射提升

$$
M(\rho)=\rho\oplus[s]\oplus B_d(\rho)\succeq0.
\tag{III.18.10}
$$

在其仿射像上有八个独立实等式。若某点不是极端点，存在非零齐次等式方向 $X$，其三个块分别支撑于该点的三个块支撑内；这也可由任何非平凡凸分解的差直接得到。支撑内的正特征值严格正，所以沿 $\pm X$ 充分小移动仍可行。沿该直线取最大的闭可行区间，两个端点均存在：原密度集紧，且 $X$ 的第一块非零，因为提升的逆是第一块投影。原点是两端点的正权凸组合。

至少一个块的秩在每个端点严格下降；否则三个块在原支撑上仍严格正，端点可以继续延伸，与最大性矛盾。沿每条分解树路径，整数

$$
\operatorname{rank}\rho+\mathbf1_{s>0}+\operatorname{rank}B_d(\rho)\le6
$$

严格下降，故有限步即止于没有非零支撑等式方向的极端叶。秩三点的支撑 Hermitian 维数至少为 $9+0+1>8$，确实总有这样的非零方向，不能作为叶遗漏。终端叶由原分类恰为 $\mathsf P,\mathsf R_0,\mathsf R_+$。两侧矩阵不等式对 $\rho$ 都是仿射的，故逐层凸组合传回根节点。§21 还给奇异 $ah$ 块直接分解为原纯态的公式。这个有限分解证明不把源替换成实态，也不把必要秩界单独当成极端性的充分条件。∎

## 19. 小参数纯态对分支的精确证书区间

**定理 19.1（直到二次代数端点的原完整半径）。** 令 $T_{\rm low}$ 为

$$
Q_2(T)=(-651+516\sqrt2)T^2+(6785-4840\sqrt2)T-4950+3500\sqrt2
\tag{III.19.1}
$$

的唯一正根，并定义

$$
d_{\rm low}=\frac{T_{\rm low}^2}{5(1+T_{\rm low}^2)}.
\tag{III.19.2}
$$

则

$$
\frac{19}{25}<T_{\rm low}<\frac{77}{100}<\frac56,
\qquad d_s<d_{\rm low}<\frac5{61}.
\tag{III.19.3}
$$

对每个 $0<d\le d_{\rm low}$，(III.18.6) 的秩二密度中心满足

$$
\sigma-cI\preceq\rho\preceq\sigma+cI\quad(\rho\in\mathcal K_d),
\qquad r(d)=2c=2\sqrt{5d(1-5d)}.
\tag{III.19.4}
$$

特别地，$(d_s,d_{\rm low}]$ 由同一原纯态对中心和半径覆盖。$d_{\rm low}$ 是下述余因子证书的充分界限，不断言它是实际最小最大分支的最大端点或相变点。

证明。$Q_2$ 的首项系数严格正，常数项严格负，所以两个实根异号，恰有一个正根。以下完全有理的平方比较固定根的位置：

$$
\begin{gathered}
Q_2(19/25)=\frac{-105886+74776\sqrt2}{625}<0,\qquad
105886^2-2\cdot74776^2=28944644>0,\\
Q_2(77/100)=\frac{-1115279+791364\sqrt2}{10000}>0,\qquad
1115279^2-2\cdot791364^2=-8666713151<0.
\end{gathered}
\tag{III.19.5}
$$

$T_s=50/(69+6\sqrt2)<19/25$，且 $T\mapsto T^2/[5(1+T^2)]$ 严格递增；定理 2.1 已给 $d(T_s)=d_s$，而 $d(5/6)=5/61$。这证明 (III.19.3)。本域的 $T=\sqrt{5d/(1-5d)}\le T_{\rm low}<1$，所以 $q=5d<1/2$、$c>0$。命题 18.2 已给全部源的下侧包含。

为证明上侧，取 $H=\sigma+cI\succ0$。在 $(w,z_0,g)$ 中，其三个特征值及行列式是

$$
\begin{gathered}
h_w=\frac{T(T+1)}{1+T^2},\quad h_z=\frac{T}{1+T^2},\quad
h_g=\frac{1+T}{1+T^2},\\
\Delta_H=\det H=\frac{T^2(T+1)^2}{(1+T^2)^3}.
\end{gathered}
\tag{III.19.6}
$$

从原 $ah$ 的实部直接得到

$$
\rho_{z_0z_0}=\frac{4d+2s-y}{5},\qquad
\rho_{ww}=q+3s-6\rho_{z_0z_0}.
$$

故完整复源上的逆期望恰为

$$
\begin{gathered}
\operatorname{Tr}(H^{-1}\rho)-1=A_s s+A_y(y-4d),\\
A_s=\frac{(5-3T)(1+T^2)}{5T(T+1)},\qquad
A_y=\frac{(5-6T)(1+T^2)}{5T(T+1)}>0.
\end{gathered}
\tag{III.19.7}
$$

这是一个恒等式，未要求源在 $(w,z_0,g)$ 中对角。写

$$
S=s/d,\quad Y=y/d,\quad u=Y+(1+2\tau)S,\quad
K_T=A_s-(1+2\tau)A_y.
$$

(III.18.7) 除以 $d^2$ 给实际源必在

$$
0\le u\le4,\qquad
0\le S\le S_{\max}(u):=\frac{u(4-u)}{4(1+\tau)^2}.
\tag{III.19.8}
$$

对秩至多二源，(III.18.4) 的右侧因而是

$$
\begin{aligned}
\mathcal B_T(S,u)
={}&h_gd^2S\bigl[(1+\tau)u+\tau^2-(1+\tau)^2S\bigr]\\
&-\Delta_Hd\bigl[K_TS+A_y(u-4)\bigr].
\end{aligned}
\tag{III.19.9}
$$

固定 $T,u$ 时，$S^2$ 的系数是 $-h_gd^2(1+\tau)^2<0$，所以它在 (III.19.8) 的整个闭区间上凹，最小值必在一个端点。当 $S_{\max}=0$，只需检验这个单点；否则凹性给它不小于两端点值的较小者。两个端点精确为

$$
\begin{aligned}
\mathcal B_T(0,u)&=\Delta_Hd A_y(4-u)\ge0,\\
\mathcal B_T(S_{\max},u)
&=\frac{d(4-u)T(T+1)}{80(1+T^2)^2(1+\tau)^2}\,N(T,u),\\
N(T,u)&=T\bigl[u^3+4\tau u^2+(4\tau^2-48\tau-12)u
 -96(1+\tau)^2\bigr]\\
&\hspace{1em}+40\tau u+80(1+\tau)^2.
\end{aligned}
\tag{III.19.10}
$$

这些式子由 (III.19.6)–(III.19.9)、$d=T^2/[5(1+T^2)]$ 代入并通分得到；所有分母在 $T>0$ 时严格正。没有在 $u=0,4$ 或 $S_{\max}=0$ 约掉相应零因子。

现在在整个 $[0,4]$ 上证明这个三次式非负，而非只检验有限采样。其关于 $u$ 的判别式为

$$
\operatorname{disc}_uN(T,u)=-5120T(T-1)Q_2(T).
\tag{III.19.11}
$$

在 $T=T_{\rm low}$，$u^3,u^2,u,1$ 的系数符号依次为 $+,+,-,+$。常数项为 $16(5-6T)(1+\tau)^2>0$。线性项系数为 $T(4\tau^2-48\tau-12)+40\tau$；括号严格负，且在 $T=19/25$ 的值为

$$
\frac{1328-1088\sqrt2}{25}<0,
$$

所以在更大的 $T_{\rm low}$ 仍严格负。$N(T_{\rm low},-u)$ 的系数符号为 $-,+,+,+$，Descartes 符号法则给恰一个负根，按重数计。判别式为零意味着有实重根：非实重根及其共轭会需要至少四次。该重根不为零，也不能是那个重数恰一的负根，因而是正的二重根 $u_*$。它不能是三重根，因为还存在负根。

此外

$$
\partial_uN(T_{\rm low},0)<0,\qquad
\partial_uN(T_{\rm low},4)
=T_{\rm low}(36-16\tau+4\tau^2)+40\tau>0.
$$

导数是首项正、常数负的二次式，恰有一个正根；故 $0<u_*<4$。比较三次式的 $u^2$ 系数，得到完整因式分解

$$
N(T_{\rm low},u)=T_{\rm low}(u-u_*)^2(u+4\tau+2u_*)\ge0
\quad(u\ge0).
\tag{III.19.12}
$$

最后令 $N_T=\partial_TN$。它作为 $u$ 的多项式满足

$$
\begin{gathered}
\partial_u^2N_T=6u+8\tau>0\quad(0\le u\le4),\\
N_T(0)=-96(1+\tau)^2<0,\qquad
N_T(4)=-80(1+4\tau+\tau^2)<0.
\end{gathered}
\tag{III.19.13}
$$

凸函数位于端点连线以下，所以 $N_T(u)<0$ 在整个闭区间成立。$N$ 对 $T$ 仿射，遂有

$$
N(T,u)=N(T_{\rm low},u)+(T-T_{\rm low})N_T(u)
\ge N(T_{\rm low},u)\ge0
$$

对所有 $0<T\le T_{\rm low},0\le u\le4$ 成立。因此 (III.19.9) 非负，给每个实际极端源的 $\det(H-\rho)\ge0$。下侧矩阵已由命题 18.2 半正定，故其行列式非负；命题 8.3 的逐点成对三次式判据在 $c>0$ 下给上侧也半正定。命题 18.3 再将两侧包含传至全部原复混合源。

匹配下界取原纯态

$$
\psi_\pm=\sqrt d(a-2h)\pm\mathrm i\sqrt{1-5d}\,g
=\sqrt q\,w\pm\mathrm i\sqrt\beta\,g,\qquad
\rho_\pm=\psi_\pm\psi_\pm^\dagger.
\tag{III.19.14}
$$

其范数为一，且 $aa=d$、$|\sqrt d-2\sqrt d|^2=d$，以及

$$
16\psi_\pm^\dagger E\psi_\pm
=|-5\sqrt d\pm\mathrm i\sqrt{6\beta}|^2
=25d+6\beta=6-5d.
$$

故可取忠实提升 $A_{\rm lift}=\rho_\pm,D_{\rm lift}=0$。相应原五维向量为 $\sqrt d(p-2Br)\pm\mathrm i\sqrt\beta\,c_5$，与 (III.1.9) 使用同一 $V$ 识别。两密度中点恰为 $\sigma$，差的非零特征值为 $2c,-2c$，其相互迹距离为 $4c$。三角不等式给任意复密度中心至少一项距离不小于 $2c$，没有将竞争中心限制在 $\mathcal K_d$ 或块对角集合。

这个下界还有显式正锥法锥证书。取

$$
v_\pm=(w\pm\mathrm ig)/\sqrt2,\quad p_\pm=1/2,\quad
M=\sum_\pm p_\pm\Re(v_\pm v_\pm^\dagger)
=\frac{ww^\dagger+gg^\dagger}{2}.
\tag{III.19.15}
$$

则 $(\rho_\pm-\sigma)v_\pm=cv_\pm$，$v_\pm^\dagger\rho_\pm v_\pm=1/2+c$，并有

$$
M\preceq\tfrac12I,\qquad (\tfrac12I-M)\sigma=0,
\qquad \sum_\pm p_\pm v_\pm^\dagger\rho_\pm v_\pm-\tfrac12=c.
$$

这正是命题 9.3 的秩二中心边界条件，而非满秩中心的内点驻定假设。原通道、全部竞争重建与全部有限未触动参考由 (III.1.6) 及 §24 的对应保留，故 (III.19.4) 是原风险的精确值。∎

## 20. 靠近七分之二的四纯接触分支

**定义 20.1（四次端点与原中心参数）。** 令

$$
\begin{aligned}
F_4(x)={}&(-45+30\sqrt2)x^4+(-41+36\sqrt2)x^3\\
&+(100-72\sqrt2)x^2+(-53+36\sqrt2)x+9-6\sqrt2,
\end{aligned}
\tag{III.20.1}
$$

$x_\dagger$ 为其在 $(2694/10000,2695/10000)$ 中的唯一根。沿用定义 3.1 的 $D_6,F_6,P_6,J_4,G_4$，并写

$$
\begin{gathered}
x_m=2-\sqrt3,\qquad
d(x)=\frac{(x^2+2x-1)^2(5x^2-4x+1)}{D_6(x)},\qquad
d_{\rm high}=d(x_\dagger),\\
a_x=(1-x)^2,\quad b_x=-2x^2,\quad h_x=2x,\quad
\Delta=2x(1-2x)(1+x^2),\quad g_x=\frac{\Delta}{1-2x-x^2},\\
T_x=\begin{pmatrix}a_x&b_x&0\\b_x&h_x&0\\0&0&g_x\end{pmatrix},\quad
Q=\operatorname{Tr}T_x^2,\quad L=\operatorname{Tr}T_x,\\
\kappa_x=L/Q,\qquad c=(L^2-Q)/(3Q),\qquad
\sigma_x=\kappa_xT_x-cI.
\end{gathered}
\tag{III.20.2}
$$

$T_x$ 是正矩阵参数，不是通道；$Q$ 在本节表示这个平方迹，§21 的 $Q$ 另有明确的局部定义。

**定理 20.2（四次充分端点到 $2/7$ 的精确原风险）。** $x\mapsto d(x)$ 是从 $[x_m,x_\dagger]$ 到 $[d_{\rm high},2/7]$ 的严格递减双射。对该区间每个 $d=d(x)$，$\sigma_x$ 是秩三密度矩阵，且

$$
\sigma_x-cI\preceq\rho\preceq\sigma_x+cI\quad(\rho\in\mathcal K_d),
\qquad r(d)=2c.
\tag{III.20.3}
$$

$[d_{\rm high},2/7)$ 与定理 3.2 使用同一原中心及半径参数化。$d_{\rm high}$ 是本节充分余因子证书的界限，不是已证明的实际转折点或最大分支界限。

证明。先给可恢复的精确根和严格符号证书。取有理闭区间

$$
I=[267/1000,27/100].
$$

对每个所列多项式 $f$，令 $f_0=f/\operatorname{lc}(f)$、$f_1=f_0'$，依次取 $f_{j+1}=-\operatorname{rem}(f_{j-1},f_j)$，至非零常数为止；不再对中间余式乘负因子。系数域为实际正平方根所定序的 $\mathbb Q(\sqrt2)$。$V_f$ 仍按去零后的变号数定义。除了定义 3.1 的五个多项式，再令

$$
\begin{aligned}
R_4(x)&=15x^4+64x^3-84x^2+32x-3,\\
R_6(x)&=225x^6-120x^5-x^4+544x^3-497x^2+152x-15,\\
R_{4g}(x)&=15x^4+8x^3+20x^2-24x+5.
\end{aligned}
\tag{III.20.4}
$$

以下符号串及端点值均针对上述确定的有理余式递归。六次式的余式次数为 $6,5,4,3,2,1,0$，四次式为 $4,3,2,1,0$；表中没有零值。

| $f$ | $267/1000$ 的符号串 | $27/100$ 的符号串 | 两端 $V_f$ |
| --- | --- | --- | --- |
| $F_6$ | $+---+--$ | $+---+--$ | $3,3$ |
| $D_6$ | $+--++--$ | $+--++--$ | $3,3$ |
| $P_6$ | $+--+--+$ | $+--+--+$ | $4,4$ |
| $J_4$ | $-+++-$ | $-+++-$ | $2,2$ |
| $G_4$ | $--+--$ | $--+--$ | $2,2$ |
| $R_4$ | $++---$ | $++---$ | $1,1$ |
| $R_6$ | $++---++$ | $++---++$ | $2,2$ |
| $R_{4g}$ | $+--+-$ | $+--+-$ | $3,3$ |
| $F_4$ | $-+--+$ | $++--+$ | $3,2$ |

原多项式而非首一化多项式的左端锚值为

$$
\begin{array}{c|c}
f&f(267/1000)\\ \hline
F_6&2726277789378321/40000000000000000\\
D_6&6228118965939049/40000000000000000\\
P_6&9469779616889569/100000000000000000\\
J_4&121815792237/200000000000\\
G_4&-182201505037/200000000000\\
R_4&170028450963/200000000000\\
R_6&16862229327841521/40000000000000000\\
R_{4g}&49257025363/200000000000
\end{array}
\tag{III.20.5}
$$

所以前八式在整个 $I$ 无根，且符号依次为 $+,+,+,+,-,+,+,+$。这是 Sturm 定理对实际精确多项式的应用；递归、端点、次数和符号均已指定，可以直接在有序系数域中重建余式，不涉及浮点特征值或网格检验。

$F_4$ 在 $I$ 恰有一个根。更细的符号由

$$
\begin{aligned}
F_4(2694/10000)
 &=\frac{117596413983471-83150438656314\sqrt2}{125000000000000}>0,\\
F_4(2695/10000)
 &=\frac{3006768505431-2126287097754\sqrt2}{3200000000000}<0
\end{aligned}
\tag{III.20.6}
$$

确定：两个分子中正有理项平方减去两倍根号系数平方，分别为

$$
925684297018622637074649>0,\qquad
-1536798898487227193271<0.
$$

因 $267/1000<x_m<268/1000<2694/10000$，有 $F_4\ge0$ 在 $[x_m,x_\dagger]$，且只有右端取零。这里 $x_m$ 的夹界可由 $1732/1000<\sqrt3<1733/1000$ 的平方比较得到。

在整个 $I$，$0<x<1/2$、$1-2x-x^2>0$、$5x^2-1<0$、$x^2+2x-1<0$，所以 $T_x\succ0$。式 (III.3.8) 是本参数化的代数恒等式，仍给

$$
\begin{gathered}
Q=\frac{(1+x^2)D_6}{(x^2+2x-1)^2}>0,\qquad
L=\frac{(1+x^2)(5x^2-1)}{x^2+2x-1}>0,\\
\kappa_x=\frac{(5x^2-1)(x^2+2x-1)}{D_6}>0,\qquad
c=-\frac{8x(x-1)(2x-1)(x^2+2x-1)}{3D_6}>0.
\end{gathered}
\tag{III.20.7}
$$

也可由 $T_x\succ0$ 的三个正特征值直接得到 $L^2>Q$。迹恒等式给 $\operatorname{Tr}\sigma_x=1$。为验证严格密度正性，令 $t_x=c/\kappa_x$；式 (III.3.9) 给

$$
\begin{aligned}
\det((T_x)_{ah}-t_xI_2)
 &=-\frac{2x(2x-1)F_6}{9(5x^2-1)^2}>0,\\
\operatorname{Tr}((T_x)_{ah}-t_xI_2)
 &=-\frac{J_4}{3(5x^2-1)}>0,\\
g_x-t_x&=\frac{2x(2x-1)G_4}{3(5x^2-1)(x^2+2x-1)}>0.
\end{aligned}
\tag{III.20.8}
$$

二阶实对称块的迹及行列式同时严格正，故两个特征值严格正；$g$ 特征值也严格正。因此本域的 $\sigma_x\succ0$，包括两个端点。

下侧包含可用更强的 $\sigma_x\prec cI$。对此应取

$$
p_x=2c/\kappa_x.
\tag{III.20.9}
$$

完整的二阶块及 $g$ 方向判据为

$$
\begin{aligned}
2p_x-a_x-h_x
 &=-\frac{R_4}{3(5x^2-1)}>0,\\
(p_x-a_x)(p_x-h_x)-b_x^2
 &=-\frac{2x(2x-1)R_6}{9(5x^2-1)^2}>0,\\
p_x-g_x
 &=-\frac{2x(2x-1)R_{4g}}{3(5x^2-1)(x^2+2x-1)}>0.
\end{aligned}
\tag{III.20.10}
$$

所有严格符号均由同一个 $I$ 上的证书和已列分母符号得到。因此 $p_xI-T_x\succ0$，即 $cI-\sigma_x\succ0$；任意密度 $\rho$ 都有 $\rho-\sigma_x+cI\succ0$。这里的 $p_x$ 由 $cI-\sigma_x=2cI-\kappa_xT_x$ 唯一决定。

参数映射的微分恒等式为

$$
d'(x)=\frac{-16x(2x-1)(x^2+2x-1)P_6(x)}{D_6(x)^2}<0
\quad(x\in I).
\tag{III.20.11}
$$

又 $d(x_m)=2/7$，所以在 $[x_m,x_\dagger]$ 得所述严格递减双射。特别地

$$
d_{\rm high}>d(27/100)=\frac{8526260729}{30505438685}>\frac14,
\tag{III.20.12}
$$

最后一个差为 $3599604231/122021754740>0$。所有 $d$ 均为合法的 $0<d<1$。

现在证明上侧包含。$H=\sigma_x+cI=\kappa_xT_x\succ0$，其逆是同一个原效应线性组合

$$
\begin{gathered}
Z=H^{-1}=\lambda I+\mu aa^\dagger+\nu C,\\
\lambda=\frac{1-2x-x^2}{\kappa_x\Delta},\quad
\mu=\frac{-1+4x-x^2}{\kappa_x\Delta},\quad
\nu=\frac{2x^2}{\kappa_x\Delta}.
\end{gathered}
\tag{III.20.13}
$$

$\mu\ge0$ 在 $[x_m,x_\dagger]$，且只在左端为零。置 $M=T_x^2/Q$、$u=M_{hh}$。矩阵乘法仍给

$$
M_{aa}=d(x),\quad M_{ah}=-u/2,\quad M_{gg}=1-d-u>0,
\qquad \operatorname{Tr}(ZM)=1.
\tag{III.20.14}
$$

$\operatorname{Tr}(CM)=d$，故 $\lambda+(\mu+\nu)d=1$。对任何原源遂有

$$
\operatorname{Tr}(Z\rho)=\lambda+\mu(d+s)+\nu d=1+\mu s.
$$

这里 $\mu\ge0$，所以不能用 $\operatorname{Tr}(Z\rho)\le1$ 作为上证书。对实际秩至多二源，命题 18.1 却给

$$
\begin{aligned}
\det(H-\rho)
&\ge h_gs\,[\tau^2d-\mu\kappa_x^2\Delta],\qquad h_g=\kappa_xg_x>0,\\
Q[\tau^2d-\mu\kappa_x^2\Delta]
&=-\frac{2(1+x^2)F_4(x)}{x^2+2x-1}\ge0.
\end{aligned}
\tag{III.20.15}
$$

第一式舍去的额外项为 $h_gs[(1+\tau)y+\tau(1+\tau)s]\ge0$；第二式是把 (III.20.2)、(III.20.7)、(III.20.13) 代入后的精确因式分解。$\det H/h_g=\kappa_x^2\Delta$，所有通分分母均已证明非零。$s=0$ 与 $F_4(x_\dagger)=0$ 直接包含在非严格不等式中。因下侧包含已经成立，成对三次式命题 8.3 给每个实际极端源的上侧包含。命题 18.3 将两侧一起传至全部复混合原源。

匹配下界须保留原四个复纯接触。由 $M\succ0$ 的 $ah$ 块，

$$
0<u<\min\{1-d,4d\},\qquad
\det M_{ah}=du-u^2/4>0.
$$

对 $\epsilon,\eta\in\{+1,-1\}$，令

$$
\begin{gathered}
H_\epsilon=-\frac{u}{2\sqrt d}
 +\epsilon\mathrm i\sqrt{u-u^2/(4d)},\quad B_\epsilon=\sqrt d+3H_\epsilon,\\
G_{\epsilon,\eta}=\eta\mathrm i\sqrt{1-d-u}\,B_\epsilon/|B_\epsilon|,\quad
\psi_{\epsilon,\eta}=\sqrt d\,a+H_\epsilon h+G_{\epsilon,\eta}g.
\end{gathered}
\tag{III.20.16}
$$

这里 $|B_\epsilon|^2=d+6u>0$，不存在相位分母为零。逐项有

$$
\begin{gathered}
|H_\epsilon|^2=u,\quad \Re H_\epsilon=-u/(2\sqrt d),\quad
\Re(B_\epsilon\overline{G_{\epsilon,\eta}})=0,\\
\|\psi_{\epsilon,\eta}\|^2=1,\quad
|\sqrt d+H_\epsilon|^2=d,\quad
|B_\epsilon+\sqrt6G_{\epsilon,\eta}|^2=6-5d.
\end{gathered}
\tag{III.20.17}
$$

故每个 $\rho_j=\psi_j\psi_j^\dagger$ 都以 $A_{\rm lift}=\rho_j,D_{\rm lift}=0$ 属于原 $\mathsf P$；五维纯提升正是 $\sqrt d\,p+H_\epsilon Br+G_{\epsilon,\eta}c_5$。先平均 $\eta$ 消去 $g$ 相干，再平均 $\epsilon$ 消去 $ah$ 虚部，得到 $(1/4)\sum_j\rho_j=M$。

各接触的 $aa,C$ 期望均为 $d$，所以 $\psi_j^\dagger Z\psi_j=1$。置 $f_j=Z\psi_j\ne0$。由 $Hf_j=\psi_j$，

$$
(\rho_j-\sigma_x)f_j=cf_j,\qquad
\frac14\sum_j f_jf_j^\dagger=ZMZ=\eta_0I,
\qquad \eta_0=\frac1{\kappa_x^2Q}>0.
\tag{III.20.18}
$$

对任意复密度中心 $\theta$，

$$
\frac14\sum_j\left[f_j^\dagger(\rho_j-\theta)f_j-c\|f_j\|^2\right]
=\operatorname{Tr}(\eta_0I(\sigma_x-\theta))=0.
\tag{III.20.19}
$$

至少一项的 Rayleigh 商不小于 $c$；迹零三阶 Hermitian 的迹范数至少为该 Rayleigh 商的两倍，故全体复中心的最坏距离至少 $2c$。这不是只在所选参数中心族内的下界。

显式正常化的正权法锥数据为

$$
v_j=f_j/\|f_j\|,\quad p_j=\|f_j\|^2/(12\eta_0)>0,\quad
\sum_jp_j=1,\quad
\sum_jp_j\Re(v_jv_j^\dagger)=I/3.
\tag{III.20.20}
$$

由 (III.20.18) 求迹得权重总和；事实上 $Z^2$ 是实 $ah$ 块加 $g$ 标量，四接触具有同样的三个对角及 $ah$ 实部，所以 $\|f_j\|^2=3\eta_0$，每个 $p_j=1/4$。活动方程给

$$
\sum_jp_jv_j^\dagger\rho_jv_j-1/3=c,\qquad
(I/3-I/3)\sigma_x=0.
$$

这是命题 9.3 对全秩中心的全局法锥证书。结合原通道对应，得到 (III.20.3)，包括 $d=d_{\rm high}$ 和 $d=2/7$。∎

## 21. 保留全部复相干的两类原面

**定义 21.1（固定原 $ah$ 块的实矩纤维）。** 在本节写

$$
\begin{gathered}
\rho=\begin{pmatrix}A&b\\b^\dagger&z\end{pmatrix},\qquad
A=A(s,y,v)=\begin{pmatrix}d+s&-(s+y)/2+\mathrm iv\\-(s+y)/2-\mathrm iv&y\end{pmatrix},\\
z=1-d-s-y,\quad q_b=(1,3)^{\mathsf T},\quad
h_b=4s/\sqrt6,\quad Q_b=q_b^\dagger A q_b=d-2s+6y,\\
\beta_B(s,y)=d(y-\tau^2s)-[y+(1+2\tau)s]^2/4.
\end{gathered}
\tag{III.21.1}
$$

$q_b$ 是本节的二分量矩向量，不是原输入向量 $q$。两个原矩恰给

$$
\Re\rho_{ah}=-(s+y)/2,\qquad \Re(q_b^\dagger b)=h_b,
\qquad v^2\le\beta_B(s,y).
\tag{III.21.2}
$$

当 $A\succ0$，定义

$$
\begin{gathered}
b_0=h_bAq_b/Q_b,\quad
U_b=\begin{pmatrix}-3&\mathrm i&0\\1&0&\mathrm i\end{pmatrix},\quad
\mathcal E=\Re(U_b^\dagger A^{-1}U_b),\quad
m=z-h_b^2/Q_b.
\end{gathered}
\tag{III.21.3}
$$

这里 $m$ 是纤维的标量平方半径参数，与 (III.8.1) 的虚坐标同字母但不同用途；$\mathcal E$ 也不同于原测量效果 $E$。

**定理 21.2（实际完整实矩纤维）。** 若 $A\succ0$，则每个满足原实矩的复列 $b$ 唯一地写成

$$
b=b_0+U_bx,\qquad x\in\mathbb R^3.
\tag{III.21.4}
$$

而且 $Q_b>0$、$\mathcal E\succ0$，并有

$$
\begin{gathered}
b^\dagger A^{-1}b=h_b^2/Q_b+x^{\mathsf T}\mathcal E x,\\
\rho\succeq0\quad\Longleftrightarrow\quad
x^{\mathsf T}\mathcal E x\le m.
\end{gathered}
\tag{III.21.5}
$$

$m>0$ 给三实维闭椭球，$m=0$ 给单点 $b=b_0$，$m<0$ 给空纤维。这是全部复 $b$ 的纤维，不是把源限制为实矩阵。

证明。直接将原效果 $16E=(1,3,\sqrt6)^{\mathsf T}(1,3,\sqrt6)$ 的期望展开，代入 $\operatorname{Tr}\rho=1$ 和 $\Re\rho_{ah}=-(s+y)/2$，得到

$$
16\operatorname{Tr}(E\rho)=6-5d-8s+2\sqrt6\Re(q_b^\dagger b).
$$

与原矩相等恰给 $\Re(q_b^\dagger b)=4s/\sqrt6$。$Q_b>0$ 来自 $A\succ0$ 和 $q_b\ne0$。故 $q_b^\dagger b_0=h_b$，并且

$$
\Re(q_b^\dagger U_bx)=0\quad(x\in\mathbb R^3).
$$

$U_b$ 在实数上单射：$U_bx=(-3x_1+\mathrm ix_2,x_1+\mathrm ix_3)^{\mathsf T}=0$ 迫使三个 $x_j$ 全零。它的像正好是 $\mathbb C^2$ 中实线性泛函 $b\mapsto\Re(q_b^\dagger b)$ 的三维核。具体逆坐标为

$$
x_1=\Re(b_h-b_{0h}),\quad x_2=\Im(b_a-b_{0a}),\quad
x_3=\Im(b_h-b_{0h});
$$

剩余实分量自动是 $-3x_1$。因此 (III.21.4) 既存在又唯一，$\Im\rho_{ag}$、$\Im\rho_{hg}$ 均保留，$\Im\rho_{ah}=v$ 另在 $A$ 内保留。

实正交恒等式为

$$
\Re(b_0^\dagger A^{-1}U_bx)
=\frac{h_b}{Q_b}\Re(q_b^\dagger U_bx)=0.
$$

这里只用实部为零，没有要求相应复内积为零。因此展开二次型给 (III.21.5) 第一式。对任何非零实 $x$，$U_bx\ne0$，故 $x^{\mathsf T}\mathcal E x=(U_bx)^\dagger A^{-1}(U_bx)>0$。为固定全部虚部符号，若 $\delta=\det A>0$，则

$$
\mathcal E=\frac1\delta
\begin{pmatrix}
Q_b&-v&-3v\\-v&y&(s+y)/2\\-3v&(s+y)/2&d+s
\end{pmatrix},\qquad
\det\mathcal E=Q_b/\delta^2>0.
\tag{III.21.6}
$$

最后，对 $A\succ0$ 的完整复块矩阵作 Schur 补，$\rho\succeq0$ 恰等价于 $z-b^\dagger A^{-1}b\ge0$，即所述椭球。严格内点给秩三，边界给秩二；$m=0$ 不需除以 $m$，$m<0$ 时因左侧二次型非负而无解。∎

**定义 21.3（两类实际外层域与原纯族）。** 第一类外层域用两个实变量 $(y,v)$：

$$
\Gamma_0(d)=\{(y,v):A(0,y,v)\succ0,\quad 1-d-y\ge0\}.
\tag{III.21.7}
$$

对它取 $s=0$、$h_b=0$、$m=z=1-d-y$，并取 (III.21.4)–(III.21.5) 的整个纤维。此处 $\delta=dy-y^2/4-v^2>0$ 已保证原 $B_d\succ0$。

第二类外层域用两个实变量 $(s,y)$，保留两个 $v$ 符号：

$$
\begin{gathered}
s>0,\quad \beta_B(s,y)\ge0,\qquad
v_\pm=\pm\sqrt{\beta_B(s,y)},\\
A(s,y,v_\pm)\succ0,\qquad
m=1-d-s-y-h_b^2/Q_b\ge0.
\end{gathered}
\tag{III.21.8}
$$

满足这些条件的点组成 $\Gamma_+(d)$。对每个符号取整个实际椭球纤维；$v_+=v_-=0$ 时两个表示重合。这类纤维恰在原 $s>0,\det B_d=0$ 的面上。$m,Q_b$ 不依赖 $v$ 的符号，但 $A,b_0,\mathcal E$ 及随后的条件矩阵依赖它，不能只检验一个符号。

另外保留母卷的全部原纯族 $\mathsf P$，用如下显式参数作全称测试：

$$
\begin{gathered}
H_\theta=\sqrt d(e^{\mathrm i\theta}-1),\quad
Y_\theta=|H_\theta|^2,\quad C_\theta=\sqrt d+3H_\theta,\quad
Z_\theta=1-d-Y_\theta\ge0,\\
\psi_{\theta,\eta}=\sqrt d\,a+H_\theta h
 +\eta\mathrm i C_\theta\sqrt{Z_\theta}/|C_\theta|\,g,
\quad \eta\in\{+1,-1\},\quad -\pi\le\theta\le\pi.
\end{gathered}
\tag{III.21.9}
$$

$|C_\theta|^2=d(13-12\cos\theta)\ge d>0$。$d\le1/5$ 时全部角度均满足 $Z_\theta\ge0$；$d>1/5$ 时条件恰为 $\cos\theta\ge(3d-1)/(2d)$。$Z_\theta=0$ 时两符号相同。

**定理 21.4（两类实际面加全部原纯族的充要性）。** 对任意密度中心 $\sigma$ 及 $c\ge0$，原全域双侧包含成立，当且仅当它在定义 21.3 的两个完整纤维族以及全部 $\mathsf P$ 上成立。

证明。两个外层域中的每个纤维点都满足原 $\rho\succeq0$、迹一、$C,E$ 矩、$s\ge0$ 和 $B_d\succeq0$，所以由命题 8.2 都是实际原源。原纯族也属于同一集合，必要性成立。

对充分性，母卷分类给每个 $\mathsf R_0$ 极端点以 $s=0,A\succ0,\det B_d>0$ 落在 $\Gamma_0$，每个 $\mathsf R_+$ 极端点以 $s>0,A\succ0,\det B_d=0$ 落在 $\Gamma_+$，其余极端点全为 $\mathsf P$。因测试的是整个实际 $s=0$ 面，无须再施加只用于筛选 $\mathsf R_0$ 极端点的 $\mathfrak J\ne0$。

这些测试还明确覆盖秩三非极端点。对任一固定外层点，若 $m>0$ 且 $x^{\mathsf T}\mathcal E x<m$，取任意 $e$ 满足 $e^{\mathsf T}\mathcal E e=1$。直线 $x+te$ 与椭球边界的两个交点参数为

$$
t_\pm=-e^{\mathsf T}\mathcal E x
 \pm\sqrt{(e^{\mathsf T}\mathcal E x)^2+m-x^{\mathsf T}\mathcal E x},
\qquad t_-<0<t_+.
$$

故

$$
x=\frac{t_+}{t_+-t_-}(x+t_-e)
 +\frac{-t_-}{t_+-t_-}(x+t_+e).
\tag{III.21.10}
$$

$\rho$ 对 $x$ 仿射，所以同样是两个实际秩二边界态的正权凸组合。$m=0$ 已是单点秩二纤维。这个分解保留固定外层的全部联合约束。

还须处理 $A$ 奇异的所有实际源。因 $d+s>0$，其秩只能为一；(III.18.2) 与 $L_\rho>0$ 强制 $s=0,\det B_d=0$。写

$$
A=uu^\dagger,\quad u=(\sqrt d,H)^{\mathsf T},\quad
|\sqrt d+H|^2=d,\quad z=1-d-|H|^2\ge0.
$$

块正性要求 $b$ 落在 $\operatorname{ran}A$，所以唯一地写成 $b=ut$，且 $|t|^2\le z$。这可直接从 $\rho$ 的二阶支撑块得到，不对 $A$ 求逆。原实矩变为

$$
\Re((\sqrt d+3H)t)=0.
$$

$\sqrt d+3H\ne0$，所以当 $z>0$ 时，全部允许 $t$ 恰为线段

$$
t=\lambda\mathrm i\overline{(\sqrt d+3H)}\sqrt z/|\sqrt d+3H|,
\qquad -1\le\lambda\le1.
\tag{III.21.11}
$$

端点对应 (III.21.9) 的两纯态，源是它们以 $(1+\lambda)/2,(1-\lambda)/2$ 为权重的凸组合（按相反的 $g$ 振幅符号配对）。$z=0$ 时 $t=0$，源本身纯。$H=0$、$y=v=0$ 也由此覆盖，且从未除以 $y$ 或 $z$。因此奇异 $A$ 极端点都由原 $\mathsf P$ 测试，非极端奇异点也没有遗漏。

最后，对未在这两个面上的任意实际点，命题 18.3 的有限支撑分解把它分成原三个极端层的叶，包括全部原秩三点。每个叶均已覆盖，双侧 Loewner 约束随凸组合保持，充分性成立。这里既没有用两个面上的独立坐标拼出非实际源，也没有仅凭“极端点足够”删除其非极端纤维。∎

## 22. 两实源外层上的精确单乘子判据

**定义 22.1（五实中心与两个方向）。** 可以在优化中选取实对称中心，但保留其五个自由坐标：

$$
\sigma=\begin{pmatrix}a_c&b_c&p_c\\b_c&h_c&q_c\\p_c&q_c&1-a_c-h_c\end{pmatrix}\succeq0,
\qquad b_c^{\rm col}=(p_c,q_c)^{\mathsf T}.
\tag{III.22.1}
$$

它没有原源的 $C,E$ 矩约束，允许奇异且允许在 $\mathcal K_d$ 外。这里 $b_c$ 的标量条目与列 $b_c^{\rm col}$ 已分开。固定 $c>0$，对定义 21.3 的每个外层点，分别置

$$
\begin{array}{c|cc}
& C_\pm & p_\pm\\ \hline
+&\sigma_{ah}+cI_2-A&\sigma_{gg}+c-z\\
-&A-\sigma_{ah}+cI_2&z-\sigma_{gg}+c
\end{array}
\tag{III.22.2}
$$

“$+$”表示 $\sigma+cI-\rho\succeq0$，“$-$”表示 $\rho-\sigma+cI\succeq0$；其非对角块分别为 $-(b-b_c^{\rm col})$ 和 $+(b-b_c^{\rm col})$。

**定理 22.2（每个实际椭球的充要四阶实 LMI）。** 若固定外层点有 $A\succ0,m>0$，对每一个方向，该方向在整个实际纤维上成立，当且仅当 $C=C_\pm\succ0$，且存在一个实标量 $\lambda_\pm\ge0$ 使

$$
\begin{pmatrix}
\lambda_\pm\mathcal E-D&-\ell_b\\
-\ell_b^{\mathsf T}&p_\pm-\gamma-\lambda_\pm m
\end{pmatrix}\succeq0,
\tag{III.22.3}
$$

其中

$$
\begin{gathered}
w_b=b_0-b_c^{\rm col},\qquad
D=\Re(U_b^\dagger C^{-1}U_b),\quad
\ell_b=\Re(U_b^\dagger C^{-1}w_b),\quad
\gamma=w_b^\dagger C^{-1}w_b.
\end{gathered}
\tag{III.22.4}
$$

$C$ 可以是复 Hermitian；$D,\mathcal E$ 是实对称三阶矩阵，$\ell_b$ 为实三列，$\gamma$ 为实数，故 (III.22.3) 是真正的四阶实对称 LMI。

证明。若整个纤维上的块矩阵半正定，其主块必有 $C\succeq0$。若 $C$ 奇异，其复秩至多一，复范围作为实空间的维数至多二。正半定块矩阵要求每个 $b-b_c^{\rm col}$ 均在该范围内；但 $m>0$ 时实椭球有内点，任意两个列差的实线性张成包含 $U_b\mathbb R^3$，其维数为三。这个范围要求矛盾。因此 $C\succ0$ 是必要结论，而非人为加入的严格条件，也不依赖中心本身是否满秩。

对这个正定 $C$，完整复块 Schur 补将方向包含化为

$$
(b-b_c^{\rm col})^\dagger C^{-1}(b-b_c^{\rm col})\le p_\pm
\quad\text{当 }x^{\mathsf T}\mathcal E x\le m.
$$

代入实际参数化并取实二次型，恰为

$$
x^{\mathsf T}Dx+2\ell_b^{\mathsf T}x+\gamma-p_\pm\le0
\quad\text{当 }x^{\mathsf T}\mathcal E x-m\le0.
\tag{III.22.5}
$$

此处消费成熟的单实二次约束 S 引理，来源为 Boyd–Vandenberghe, [*Convex Optimization*](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf)，附录 B.2，印刷页 655，式 (B.6)–(B.7) 及其蕴含形式。其原假设是实有限维二次型且前件存在严格可行点；本应用准确对应

$$
F_1=\mathcal E,\quad g_1=0,\quad h_1=-m,\qquad
F_2=D,\quad g_2=\ell_b,\quad h_2=\gamma-p_\pm.
$$

因 $m>0$，$x=0$ 严格满足前件，满足 Slater 假设。原定理于是给 (III.22.5) 当且仅当存在 $\lambda_\pm\ge0$ 使 $\lambda_\pm M(f_1)-M(f_2)\succeq0$，恰是 (III.22.3)。为核对符号，该矩阵在 $(x,1)$ 上的二次值是

$$
p_\pm-\gamma-2\ell_b^{\mathsf T}x-x^{\mathsf T}Dx
 -\lambda_\pm(m-x^{\mathsf T}\mathcal E x).
$$

它对所有 $x$ 非负正好给相应全局二次证书。没有使用多约束 S 引理、复矩阵 S 引理、正映射或 CP 延拓的无损性。∎

**命题 22.3（单点、空纤维与零块边界）。** 若 $A\succ0,m=0$，则对每个方向的精确条件是

$$
C_\pm\succeq0,\qquad w_b\in\operatorname{ran}C_\pm,\qquad
p_\pm\ge w_b^\dagger C_\pm^\dagger w_b,
\tag{III.22.6}
$$

$C^\dagger$ 表示 Moore–Penrose 逆。若 $C_\pm=0$，条件恰为 $w_b=0,p_\pm\ge0$。若 $m<0$，纤维为空，不施加任何包含条件。

证明。$m=0$ 时 $\mathcal E\succ0$ 强迫 $x=0$，所以只需检验单个完整块矩阵。对 $C$ 作酉谱分解，任一零特征方向若与非对角列有非零内积，对该方向和最后一个坐标取充分小且符号相反的分量便使二次型为负。因此列必须在 $C$ 的范围内；在正特征方向完成平方，则最后一个 Schur 余量恰为 $p-w_b^\dagger C^\dagger w_b\ge0$。这也证明充分性。$C=0$ 时没有正特征方向，得到所列特例。这里 $m=0$ 是源纤维的零半径，不是 $c=0$；S 引理的严格可行前提在此失败，故不套用定理 22.2。$m<0$ 的空性由定理 21.2 直接得到。∎

**推论 22.4（原完整包含的两实外层充要关系）。** 对每个 $0<d<1$、(III.22.1) 的任意中心及 $c>0$，以下条件一起恰等价于原全域包含：对每个 (III.21.9) 的原纯态检验两侧三阶 Loewner 不等式；对 $\Gamma_0$ 每个 $(y,v)$ 及 $\Gamma_+$ 每个 $(s,y)$ 的两个 $v$ 符号，按定理 22.2 或命题 22.3 分别检验两个方向。

证明。定理 21.4 已证明所测源族的必要性和充分性，定理 22.2、命题 22.3 给每个纤维的完全等价替换。奇异 $A$ 不进入逆矩阵公式，由 (III.21.11) 的原纯族分解承担；$d>0$ 排除 $A=0$，$L_\rho>0$ 排除原 $L_\rho=0$ 层。纯态上侧可等价写为

$$
\psi^\dagger(\sigma+cI)^{-1}\psi\le1,
$$

因为 $\sigma+cI\succ0$；纯态下侧仍须检验，不能从这个逆期望单独推出。中心奇异不妨碍这一步，但也不会消除 $m=0$ 时的范围条件。$v=0$、$s=0$、$z=0$、$y=0$ 和纯族 $Z_\theta=0$ 的边界分别由所列闭不等式、单点公式或纯态公式覆盖。

精确量词是：对每个外层点及每个方向，存在该点、该方向自己的标量乘子。这里不要求也不推出一个乘子覆盖全部外层点，两个方向的乘子也无需相同；没有把外层全称量词换成有限网格。该关系保留五实中心最小化以及每类两实源变量的全称条件，尚不是有限外层最优候选或原最小最大值的构造。∎

**命题 22.5（原源中的非退化证书及奇异块边界）。** 下列实例固定了上述实 LMI 和范围条件在原家族内的含义。

证明。先取 $d=y=1/4,s=v=0$，则

$$
A=\begin{pmatrix}1/4&-1/8\\-1/8&1/4\end{pmatrix}\succ0,
\quad z=m=1/2,\quad b_0=0,\quad
\mathcal E=\begin{pmatrix}112/3&0&0\\0&16/3&8/3\\0&8/3&16/3\end{pmatrix}.
$$

这是 $\Gamma_0$ 的实际纤维。对 $\sigma=I/3,c=1$，两个方向在 $\lambda_+=\lambda_-=1$ 的 LMI 中均有 $\ell_b=0,\gamma=0$，且

$$
\begin{gathered}
D_+=\begin{pmatrix}6672/667&0&0\\0&624/667&-72/667\\0&-72/667&624/667\end{pmatrix},\\
D_-=\begin{pmatrix}4848/475&0&0\\0&528/475&72/475\\0&72/475&528/475\end{pmatrix}.
\end{gathered}
\tag{III.22.7}
$$

最后对角项分别为 $1/3,2/3$。$\mathcal E-D_+$ 的第一个特征值为 $112/3-6672/667>0$，其余两个为 $8/3-696/667>0$、$8-552/667>0$；$\mathcal E-D_-$ 相应为 $112/3-4848/475>0$、$8/3-456/475>0$、$8-600/475>0$。因此两张四阶 LMI 均严格正，证明这个固定实际纤维的两方向证书。

为检验严格 $C$ 的必要性，在同一 $A,z$ 下取

$$
b=(\mathrm i\sqrt{3/32},0)^{\mathsf T}.
$$

$\det A=3/64$ 且 $b^\dagger A^{-1}b=1/2=z$，故这是实际秩二原源，原实矩仍为零。取合法正密度

$$
\sigma_+=\begin{pmatrix}6/25&-1/8&0\\-1/8&1/4&0\\0&0&51/100\end{pmatrix},\qquad c=1/100.
$$

它的 $ah$ 行列式为 $71/1600>0$，第三对角为正，迹一。此时 $C_+=\operatorname{diag}(0,1/100)$、$p_+=1/50$，但完整上侧差的 $(a,g)$ 主子式为 $-3/32$，故不正。下侧也有同一源上的实例：取

$$
\sigma_-=\begin{pmatrix}13/50&-1/8&0\\-1/8&1/4&0\\0&0&49/100\end{pmatrix},\qquad c=1/100.
$$

其 $ah$ 行列式为 $79/1600>0$，也是正密度；现在 $C_-=\operatorname{diag}(0,1/100)$、$p_-=1/50$，完整下侧差的同一主子式仍为 $-3/32$。因此两个方向都不能在 $m>0$ 省去严格性或范围条件。

另一方面，取 $d=1/4,s=v=0,y=3/4,z=m=0$，

$$
A_0=\begin{pmatrix}1/4&-3/8\\-3/8&3/4\end{pmatrix}\succ0,\quad b_0=0,\quad
\sigma_0=\begin{pmatrix}6/25&-3/8&0\\-3/8&37/50&0\\0&0&1/50\end{pmatrix}.
$$

$\det A_0=3/64$，$\det(\sigma_0)_{ah}=1479/40000>0$，故原源与中心均合法。对 $c=1/100$，完整上侧差正好为 $\operatorname{diag}(0,0,3/100)\succeq0$。因此在 $m=0$ 必须保留合法的 $C_+=0$ 分支。此例只证明这个单点的上侧包含，不声称两个方向同时成立或该中心覆盖全 $\mathcal K_d$。∎

## 23. 实际混合上接触处的截断余因子损失

**命题 23.1（严格损失的准确范围）。** 设 $\rho$ 是原 $\mathsf R_+$ 中的秩二源，$s>0$，且 $H=\operatorname{diag}(H_2,h_g)\succ0$。则

$$
J_\rho:=\operatorname{adj}(\rho)_{ah}\succeq0,\qquad
\operatorname{Tr}(H_2J_\rho)>0.
\tag{III.23.1}
$$

若它是实际上侧接触，即 $H-\rho\succeq0$ 且 $\det(H-\rho)=0$，那么仅保留 $h_g\delta$ 的截断证书

$$
\mathcal T_0(H,\rho)=\det H\,[1-\operatorname{Tr}(H^{-1}\rho)]+h_g\delta
\tag{III.23.2}
$$

严格为负。在 $\mathsf R_+$，(III.18.4) 的右侧与此截断值相同。

证明。$s>0$ 时，原实矩 $\Re(b_a+3b_h)=4s/\sqrt6>0$ 强制 $b\ne0$。若 $z=\rho_{gg}=0$，正半定矩阵的零对角方向必须为核方向，迫使 $b=0$，矛盾，故 $z>0$。

秩二正矩阵的伴随矩阵非零、秩一、半正定，其范围恰为 $\ker\rho$。若 $J_\rho=0$，伴随矩阵的正性还强制其 $ah$ 到 $g$ 的交叉块为零，所以它只能支持在 $g$ 方向。于是 $g\in\ker\rho$，给 $z=0$，仍矛盾。因此 $J_\rho$ 非零，$H_2\succ0$ 给 $\operatorname{Tr}(H_2J_\rho)>0$。

秩二的精确行列式恒等式给

$$
\mathcal T_0(H,\rho)
=\det(H-\rho)-\operatorname{Tr}(H_2J_\rho).
\tag{III.23.3}
$$

故在所述实际接触处严格负。$\mathsf R_+$ 满足 $\det B_d=0$，所以 $\delta=sL_\rho/\alpha^2$；这说明共同不等式在这里恰好只丢失了 (III.23.1) 的严格正项。∎

**命题 23.2（$5/61$ 的实际原源及精确正损失）。** 在 $d=5/61$，令

$$
\begin{gathered}
U_0=5d/12,\qquad s=\alpha^2U_0
=\frac{25}{1464}+\frac{25\sqrt2}{2196},\\
y=d/9+\gamma^2U_0=\frac{115}{4392}-\frac{25\sqrt2}{2196},\qquad
v=0,\qquad z=\frac{1921}{2196}.
\end{gathered}
\tag{III.23.4}
$$

用 (III.21.1)–(III.21.3) 的 $A,Q_b,h_b,b_0,m$，置

$$
b=b_0+\mathrm i\sqrt{m\delta/y}\,(1,0)^{\mathsf T},\qquad
\rho=\begin{pmatrix}A&b\\b^\dagger&z\end{pmatrix}.
\tag{III.23.5}
$$

这是原 $\mathsf R_+$ 的实际源，而且

$$
\operatorname{Tr}J_\rho
=\frac{811378025}{16659036072}
 +\frac{2998925\sqrt2}{2082379509}>0.
\tag{III.23.6}
$$

证明。所有所用分母及平方根可精确检验：

$$
\begin{aligned}
\delta&=\frac{125}{66978}-\frac{250\sqrt2}{301401}>0,\\
Q_b&=\frac{25}{122}-\frac{50\sqrt2}{549}>0,\\
m&=\frac{46027}{53802}-\frac{1100\sqrt2}{80703}>0,\\
\frac{m\delta}{y}
 &=\frac{17903150}{297482787}-\frac{566900\sqrt2}{297482787}>0.
\end{aligned}
\tag{III.23.7}
$$

$y=(115-50\sqrt2)/4392>0$。这些严格不等式直接由 $1<\sqrt2<3/2$ 及正分母给出；$d+s>0$ 和 $\delta>0$ 证明 $A\succ0$。$b_0$ 为实列，添加的纯虚列不改变原实矩。又

$$
\Re(b_0^\dagger A^{-1}\mathrm i e_1)=0,\qquad
(A^{-1})_{11}=y/\delta,
$$

所以 $b^\dagger A^{-1}b=h_b^2/Q_b+m=z$。Schur 补给 $\rho\succeq0$、$\operatorname{rank}\rho=2$。代入 $s,y,v$ 得

$$
d(y-\tau^2s)-[y+(1+2\tau)s]^2/4=0,
$$

故 $\det B_d=0$。迹一和 $C,E$ 两矩已由同一参数化保证。这证明源属于 (III.8.1)–(III.8.2)，而不是某个自由替代的松弛。

也可直接给原忠实分解：$L_\rho>0$，取

$$
A_{\rm lift}=\rho\ell\ell^\dagger\rho/L_\rho,\qquad
D_{\rm lift}=\rho-A_{\rm lift}.
\tag{III.23.8}
$$

Cauchy–Schwarz 给 $0\preceq A_{\rm lift}\preceq\rho$，且 $D_{\rm lift}\ell=0$。因 $\det B_d=0$，有 $(A_{\rm lift})_{aa}=|a^\dagger\rho\ell|^2/L_\rho=d$。故 $D_{\rm lift}$ 支持于原固定 $N=\ell^\perp$，(III.1.4) 的全部条件成立；原极端分类遂给 $\rho\in\mathsf R_+$。

伴随矩阵的两个相关对角条目之和可直接写成

$$
\operatorname{Tr}J_\rho=z(d+s+y)-\|b\|^2.
$$

此处

$$
\|b\|^2=\frac{h_b^2}{Q_b^2}q_b^{\mathsf T}A^2q_b+\frac{m\delta}{y},
$$

通分并使用 (III.23.4)、(III.23.7) 即得 (III.23.6)，两项都严格正。对 $H_2=I_2$ 这就是明确的正损失，对任意正定 $H_2$ 则由命题 23.1 仍严格正。

这个实际源还能给一个确实的上侧接触，而不指定未知最优中心。令 $t=\lambda_{\max}(\rho)>0$、$H=tI$，则 $H-\rho\succeq0$ 且行列式为零。若要纯代数表示，可令 $e_2(\rho)$ 为三个二阶主子式之和，并取 $t=(1+\sqrt{1-4e_2(\rho)})/2$；因为 $\rho$ 正、秩二、迹一，该根号恰是两个非零特征值之差的绝对值。此时 $\mathcal T_0=-t\operatorname{Tr}J_\rho<0$。这仅实例化了实际接触处的证书损失，没有识别原最小最大问题的接触。∎

**定义 23.3（方法障碍的边界）。** 命题 23.1 排除的是：在正定块对角 $H$ 的实际秩二 $\mathsf R_+$ 上侧接触处，要求截断表达式 (III.23.2) 非负作为上证书。它没有证明未知最优 $H$ 必须块对角，没有证明每个中央 $d$ 都有这种上侧接触，也没有把正权 $\mathsf R_+$ 接触自动判作上侧而非下侧。保留完整 $\operatorname{Tr}(H_2J_\rho)$、允许一般五实中心或使用 §§21–22 的精确条件，不受这个截断方法结论排除。

## 24. 原风险、共同实现与尚未求解的中间区间

**命题 24.1（五维提升、合法共同重建及全部参考）。** §§18–23 的所有源、接触和中心证书都消费原 (III.1.6) 的同一通道对应；定理 19.1、20.2 的 $2c$ 因而是全部原共同 CPTP 重建的精确 diamond 风险，参考量词为任意有限且未触动的系统。

证明。对任何本节涉及的实际源，原 $B_d\succeq0$ 与 $L_\rho>0$ 给

$$
A_{\min}=\rho\ell\ell^\dagger\rho/L_\rho,\qquad
0\preceq A_{\min}\preceq\rho,\quad (A_{\min})_{aa}\le d\le\rho_{aa}.
$$

若 $\rho_{aa}>(A_{\min})_{aa}$，令

$$
\theta=\frac{d-(A_{\min})_{aa}}{\rho_{aa}-(A_{\min})_{aa}},\quad
A_{\rm lift}=(1-\theta)A_{\min}+\theta\rho,\quad
D_{\rm lift}=\rho-A_{\rm lift}.
$$

则 $0\le\theta\le1$、$(A_{\rm lift})_{aa}=d$，且 $D_{\rm lift}\ell=0$。若分母为零，两个端值均为 $d$，直接取 $A_{\rm lift}=\rho,D_{\rm lift}=0$。故所有边界都具有原固定 $N$ 内的忠实提升。以原酉识别 $V$ 定义

$$
\omega=V^\dagger(A_{\rm lift}\oplus D_{\rm lift})V,\qquad
T_\omega(X)=BP_+XP_+B^\dagger+(f^\dagger Xf)\omega.
\tag{III.24.1}
$$

$\omega$ 是五维密度，取其谱分解可将 $T_\omega$ 写成 $BP_+$ 和各 $\sqrt{\lambda_j}w_jf^\dagger$ 的 Kraus 和，伴随平方和为 $P_++ff^\dagger=I_3$，所以 CPTP。母卷定理 35.2–35.4 的原三个完整效果算子与递推给全部深度数据及 $\mathcal GT_\omega=S_\rho$。这不是只在一个输入上匹配原数据。

对任意候选密度 $\sigma$，取

$$
R_\sigma(X)=B[UP_+XP_+U^\dagger+(f^\dagger Xf)\sigma]B^\dagger.
\tag{III.24.2}
$$

其 Kraus 算子为 $BUP_+$ 和 $\sqrt{\mu_j}Bu_jf^\dagger$，其中 $\sigma=\sum_j\mu_ju_ju_j^\dagger$。伴随平方和仍为 $I_3$，即使 $\sigma$ 秩二也合法。

对任意有限 $n$ 和任意复矩阵 $X\in M_n\otimes M_3$，

$$
\begin{gathered}
X_{ff}=(I_n\otimes f^\dagger)X(I_n\otimes f),\\
(\operatorname{id}_n\otimes(S_\rho-R_\sigma))(X)
=X_{ff}\otimes B(\rho-\sigma)B^\dagger,\\
\|X_{ff}\|_1\le\|X\|_1,\qquad
\|X_{ff}\otimes B(\rho-\sigma)B^\dagger\|_1
=\|X_{ff}\|_1\|\rho-\sigma\|_1.
\end{gathered}
\tag{III.24.3}
$$

压缩的迹范数理想性质和张量乘法给每个有限参考的统一上界，输入 $ff^\dagger$ 已达到等号。因此 $\|S_\rho-R_\sigma\|_\diamond=\|\rho-\sigma\|_1$，没有引入参考维数截断。

反过来，对任意原 CPTP $R:M_3\to M_5$，不限制输出支持、Kraus 秩或重建形式，原 CPTP 压缩

$$
\mathcal C_B(Y)=B^\dagger YB+\operatorname{Tr}((I_5-BB^\dagger)Y)gg^\dagger
$$

给复密度 $\theta=\mathcal C_B(R(ff^\dagger))$。在 $ff^\dagger$ 上求值，再用通道对 Hermitian 差的迹范数收缩性，得到

$$
\|R-S_\rho\|_\diamond
\ge\|R(ff^\dagger)-B\rho B^\dagger\|_1
\ge\|\theta-\rho\|_1.
\tag{III.24.4}
$$

故两个匹配接触下界约束所有原共同重建。原迹零三阶恒等式 $\|\rho-\sigma\|_1=2\|\rho-\sigma\|_{\rm op}$ 固定风险因子为 $2c$。这些对应是母卷定理 35.5 的既有供应；此处只明确它们在两个参数区间和完整条件判据上的消费，未将其重新计作新通道理论。∎

**定义 24.2（保留的未解目标与充分端点）。** 定理 19.1、20.2 连同 §§2–4 的既有分支，在原 $0<d<1$ 中留下的精确中心缺口为

$$
d_{\rm low}<d<d_{\rm high}.
\tag{III.24.5}
$$

该区间包含 $5/61$，因为 $d_{\rm low}<5/61<1/4<d_{\rm high}$。尚未构造这一整段的实际达到五实坐标中心、精确半径、全复源上证书及对全部复中心的匹配下证书；实际分支转折和两个充分区间的最大性也未确定。两端 $d_{\rm low},d_{\rm high}$ 均已包含在各自精确解中，但这不把它们宣告为真实转折。

§§11–13 的实际混合族、四世界下界和可行上界仍各自有效；特别地，$5/61$ 的已证严格超额和量化界没有被截断余因子障碍替代。§§14–16 的三实源外层、虚椭球及有限四次内层公式也仍有效。§§21–22 另给每类两实源外层的精确充要条件；它保留外层全称量词和五实中心最小化，没有求出 (III.24.5) 的最优解。下一项具体数学义务是在两个实际外层域同时构造中心、半径及各方向逐点乘子（包含单点范围条件），并给实际纯/混合接触的正权法锥证书使上下值相等。

**假设 24.3（同一复源与操作取得边界）。** 本批条件地使用原复 Hilbert 空间、密度与 Born 配对、CP/TP 通道、原复量子组合、固定五维仪器、原平面 $N$ 及擦除标签菜单的精确完整输入效果数据。所有坐标、矩关系、凸分解、提升与证书属于同一个 $\rho$、同一个原实现及相同数据，未把独立可达坐标拼为共同可达状态。实中心的可选性只来自原集合的共轭对称和凸性；原对手仍保留全部复坐标。

这些数学结果不授予新的制备、相位控制、采集、仪器分支、独立或相关复制、参考制备、返回环境或标签历史权限。全部有限未触动参考是原范数量词，不等于实际取得一个新参考资源。存在效果、正映射、通道、重建或提升也不等于取得它。Hilbert/Born/CP 与精确数据、菜单和组合仍为前提；上述区间与条件判据没有推出物理量子原则的起源、经验有效性或信息守恒，也没有终结持续的量子起源目标。

**定义 24.4（数学归属）。** 原源上的块余因子应用、两个充分参数区间及全复匹配证书、两类实际面的完整实矩纤维、五实中心的逐点充要 LMI，以及限定的实际接触损失，属于源特定综合推导 `repo-derived`。三阶混合行列式、谱分解、等期望纯态分解、Schur 补、Moore–Penrose 范围判据、凸分解、Descartes/Sturm 实根工具、Rayleigh 原理和单实约束 S 引理均为成熟中间工具，按各证明的精确假设消费；不主张这些工具或本应用的文献优先权。通道表示、完全有界迹范数背景沿用定义 1.4 的 Watrous 文献，S 引理的原假设映射在定理 22.2 内给出。这里的成果是普通条件数学，不新增 Lean/kernel 结论。

仍待回答的起源关系是：在原操作菜单、共同来源和实际取得条件下，哪些联合关系能约束源纤维中隐藏的超额与复相干，并解释采用复量子组合及 Born 配对的理由？两段精确风险与完整条件判据描述这些前提下的预测不确定性，没有把数学表示的存在当成该物理结构的来源。

## 追加锚（本行以下为增补区）

## 25. 原归一化源帽与不丢失奇异块的上侧矩阵

**定义 25.1（同一原源的归一化形状）。** 以下固定定义 1.1–1.2 的原五维仪器、固定平面 $N$、全部复状态纤维 $\mathcal K_d$、全部原完整输入效果数据及不除以二的风险。源与中心都保留复数范围；中心不要求属于源纤维。对 $0<d\le1/10$，写

$$
\begin{gathered}
\rho=\begin{pmatrix}A&b\\b^\dagger&z\end{pmatrix},\quad
A=dA_n,\quad
A_n=\begin{pmatrix}1+S&-(S+Y)/2+\mathrm iV\\-(S+Y)/2-\mathrm iV&Y\end{pmatrix},\\
S=s/d,\quad Y=y/d,\quad V=v/d,\quad
z=1-d(1+S+Y),\quad q_b=(1,3)^{\mathsf T},\\
\tau=3-2\sqrt2,\quad \kappa=(1+\tau)^2,\quad
u=Y+(1+2\tau)S,\quad S_{\max}(u)=\frac{u(4-u)}{4\kappa},\\
Q=5d,\quad\beta=1-Q,\quad x=\sqrt{Q/\beta},\quad
c=\sqrt{Q\beta}=\frac{x}{1+x^2},\quad
w=(a-2h)/\sqrt5,\quad z_0=(2a+h)/\sqrt5,\\
\sigma(d)=Qww^\dagger+\beta gg^\dagger
=\begin{pmatrix}d&-2d&0\\-2d&4d&0\\0&0&1-5d\end{pmatrix}.
\end{gathered}
\tag{III.25.1}
$$

$A$ 是源的 $ah$ 主块，不是定义 1.2 的提升分量 $A_{\rm lift}$。将 (III.1.6) 的原酉识别记为 $V_{\rm phys}:\mathbb C^5\to\mathbb C^3\oplus N$；它与归一化虚坐标 $V$ 不同。$T_0=5^{-1/2}\begin{pmatrix}1&2\\-2&1\end{pmatrix}$ 将 $(w,z_0)$ 坐标送到 $(a,h)$ 坐标。为每个归一化形状定义

$$
\begin{gathered}
L_x=\left(\frac5x-4+S+Y\right)
\operatorname{diag}\left(x,\frac{x}{1+x}\right)-T_0^{\mathsf T}A_nT_0
=\begin{pmatrix}l_1&-k_0-\mathrm iV\\-k_0+\mathrm iV&l_2\end{pmatrix},\\
l_1=(6/5-x)(4-S-Y)+3S/5,\qquad k_0=(4+7S-Y)/10,\\
l_2=\frac{21-24x}{5(1+x)}+\left(\frac{x}{1+x}-\frac25\right)S
 +\left(\frac{x}{1+x}+\frac15\right)Y,\qquad
\widehat L_x=T_0L_xT_0^{\mathsf T}.
\end{gathered}
\tag{III.25.2}
$$

**命题 25.2（实际相关源帽与两个行列式端点）。** 每个实际原复源必满足

$$
\begin{gathered}
S,Y\ge0,\quad \Re(q_b^{\mathsf T}b)=4dS/\sqrt6,\quad
V^2\le u-u^2/4-\kappa S,\\
0\le u\le4,\quad0\le S\le S_{\max}(u),\quad
Y=u-(1+2\tau)S\ge0,\quad S+Y=u-2\tau S\le4,\quad z\ge\beta.
\end{gathered}
\tag{III.25.3}
$$

对 $4/5\le x\le5/6$，在这个闭源帽上 $l_2>0$、$l_1\ge0$，且 $l_1=0$ 恰在 $S=0,Y=4$。代入 $Y=u-(1+2\tau)S$，令

$$
P_x(S,u)=l_1l_2-k_0^2-u+u^2/4+\kappa S.
\tag{III.25.4}
$$

则 $P_x$ 对 $S$ 严格凹，并且

$$
\begin{aligned}
\det L_x&=P_x(S,u)+u-u^2/4-\kappa S-V^2\ge P_x(S,u),\\
P_x(0,u)&=\frac{(4-u)(5-6x)}{1+x}\left(1-\frac{x(4-u)}5\right),\\
P_x(S_{\max}(u),u)&=\frac{(4-u)F_x(u)}{2560(1+x)},
\end{aligned}
\tag{III.25.5}
$$

其中下列系数精确定义同一个三次式，而非数值拟合：

$$
\begin{gathered}
F_x(u)=a_3(x)u^3+a_2(x)u^2+a_1(x)u+a_0(x),\\
a_3=-(21+6\sqrt2)x^2+(70+40\sqrt2)x+60+40\sqrt2,\\
a_2=-(444+72\sqrt2)x^2+360x+80,\\
a_1=(-960+384\sqrt2)x^2+(-160-640\sqrt2)x+1040-160\sqrt2,\\
a_0=12288x^2-25600x+12800=512(5-6x)(5-4x).
\end{gathered}
\tag{III.25.6}
$$

证明。命题 18.1 和 (III.21.2) 直接给同一个 $\rho$ 的归一化关系

$$
\frac{\det B_d(\rho)}{\alpha^2d^2}
=Y-\tau^2S-\frac{[Y+(1+2\tau)S]^2}4-V^2
=u-u^2/4-\kappa S-V^2\ge0.
$$

故 $u\ge0$、$u\le4$ 且 $S\le S_{\max}(u)$。反过来，这些帽条件给

$$
Y\ge u-\frac{(1+2\tau)u}{\kappa}=\frac{\tau^2u}{\kappa}\ge0,
\qquad S\le1/\kappa,
$$

但这里只把帽作为实际源的必要外域；没有断言每个帽点都存在满足原实矩的 $b$。$S+Y=u-2\tau S\le4$ 给人口下限。原 $\rho\succeq0$、复 $b$ 及其原实矩仍同时保留。

直接用 $T_0$ 旋转 $A_n$，其对角为 $(1+3S+6Y)/5,(4+2S-Y)/5$，上非对角为 $k_0+\mathrm iV$，得到 (III.25.2)。在指定 $x$ 区间，$l_2$ 的常数项及两个变量系数均严格正；$l_1$ 的表达式给所述等号条件。

固定 $u$，$l_1,l_2$ 的 $S$ 系数依次为

$$
b_1=\frac{3+12\tau}{5}-2\tau x\ge\frac35+\frac{11\tau}{15}>0,
\qquad b_2=-\frac{3+2\tau}{5}-\frac{2\tau x}{1+x}<0.
$$

因此 $P_x$ 的 $S^2$ 系数为 $b_1b_2-(4+\tau)^2/25<0$。将 $S=0$ 与 $S=u(4-u)/(4\kappa)$ 分别代入 (III.25.4)，用 $\tau=3-2\sqrt2$ 通分，得到 (III.25.5) 和全部系数 (III.25.6)。因原帽余量非负，第一行也成立。凹性给闭区间内的值不小于两端点连线；$u=0,4$ 时区间退化为单点，直接用未约掉 $4-u$ 的恒等式。没有对 $A$、$S$、$S_{\max}$ 或 $4-u$ 求逆。∎

## 26. 唯一代数二重根与精确隔离

**定理 26.1（原帽端点的唯一正二重根）。** 存在唯一

$$
(x_*,u_*)\in(4/5,5/6)\times(0,4),\qquad
F_{x_*}(u_*)=\partial_uF_{x_*}(u_*)=0.
\tag{III.26.1}
$$

它是实代数数对，且

$$
\begin{gathered}
\frac{403}{500}<x_*<\frac{807}{1000},\qquad
\frac7{10}<u_*<\frac{71}{100},\\
d_*:=\frac{x_*^2}{5(1+x_*^2)},\qquad
\frac{162409}{2062045}<d_*<\frac{651249}{8256245}<\frac1{10},\\
F_{x_*}(u)=a_3(x_*)(u-u_*)^2
 \left(u+\frac{a_2(x_*)}{a_3(x_*)}+2u_*\right)\ge0\quad(u\ge0).
\end{gathered}
\tag{III.26.2}
$$

最后一式只有一个非负零点 $u_*$，其重数恰为二；最后一因子严格正。十进表示为 $d_*\approx0.07883057453397067$，定义由 (III.25.6)、(III.26.1) 及有理隔离给出。

证明。在 $4/5\le x\le5/6$，系数满足

$$
a_3>73,\qquad a_2\ge a_2(5/6)=215/3-50\sqrt2>5/6,
\qquad -704<a_1<0.
\tag{III.26.3}
$$

这些界直接由二次式得到：$a_3$ 递增，$a_2,a_1$ 递减，再在两端代入即可。因此 $F'_x(0)<0$、$F'_x(4)=48a_3+8a_2+a_1>0$，而 $F''_x(u)=6a_3u+2a_2>0$ 对所有 $u\ge0$ 成立。每个 $x$ 恰有一个正的全局极小点 $u(x)\in(0,4)$。

在左端，精确展开为

$$
\frac{F_{4/5}(u)}{2560(1+4/5)}
=\left(\frac{641}{28800}+\frac{71\sqrt2}{4800}\right)u^3
 +\left(\frac{131}{7200}-\frac{\sqrt2}{100}\right)u^2
 +\left(\frac{31}{480}-\frac{37\sqrt2}{400}\right)u+\frac1{25}.
$$

用 $7/5<\sqrt2<17/12$ 逐系数比较，它不小于 $(3u^3-5u+3)/75$。多项式 $3u^3-5u+3$ 在非负半轴的最小值为 $(27-10\sqrt5)/9>0$，后一个符号由 $27^2>100\cdot5$ 给出。因此左端严格正。在右端 $x=5/6$，$a_0=0,a_1<0$，故某个足够小的正 $u$ 使 $F_x(u)<0$。

为证明唯一性，固定 $0\le u<4$，在 $S=S_{\max}(u),V=0$ 上有 $l_1,l_2>0$，并且

$$
\partial_xl_1=S+Y-4<0,\qquad
\partial_xl_2=\frac{S+Y-9}{(1+x)^2}<0,\qquad \partial_xk_0=0.
\tag{III.26.4}
$$

因而 (III.25.5) 的 $F_x(u)/[2560(1+x)]=\det L_x/(4-u)$ 严格随 $x$ 递减。这一步只在 $u<4$ 使用除法。在紧区间 $[0,4]$ 上取最小值得到连续函数 $m(x)$；其极小点都在 $(0,4)$，所以将任一较小 $x$ 的极小点代入较大 $x$，即得 $m$ 严格递减。上述异号端值给恰一个零点 $x_*$；严格凸性给唯一的 $u_*$。任何 (III.26.1) 的正解都必须是这个极小点零值，故对整个指定矩形唯一。

隔离只需下列有理比较。令 $x_l=403/500,x_h=807/1000$、$u_l=7/10,u_h=71/100$，则

$$
\begin{gathered}
4a_2(x_l)F_{x_l}(u_l)-F'_{x_l}(u_l)^2>260,
\qquad F_{x_h}(u_l)<-29/10,\\
F'_{x_l}(u_l)<-1/2,\qquad F'_{x_h}(u_h)>5,\\
\partial_xF'_x(u_l)<-2300,\quad
\partial_xF'_x(u_h)<-2300\quad(x_l\le x\le x_h).
\end{gathered}
\tag{III.26.5}
$$

这里每个固定点的表达式在 $\mathbb Q(\sqrt2)$ 内，混合导数对 $x$ 仿射；代入两个 $x$ 端点并用

$$
\frac{7071}{5000}<\sqrt2<\frac{14143}{10000},\qquad
\left(\frac{7071}{5000}\right)^2<2<
\left(\frac{14143}{10000}\right)^2
$$

作有理上下界即可得到全部严格符号。因 $F''_{x_l}\ge2a_2(x_l)>0$，完成平方给

$$
F_{x_l}(u)\ge F_{x_l}(u_l)+F'_{x_l}(u_l)(u-u_l)
 +a_2(x_l)(u-u_l)^2
\ge F_{x_l}(u_l)-\frac{F'_{x_l}(u_l)^2}{4a_2(x_l)}>0.
$$

于是 $x_l<x_*<x_h$。混合导数符号将 $F'_{x_l}(u_l)<0$ 传播到 $x_*$，并将 $F'_{x_h}(u_h)>0$ 反向传播到 $x_*$；严格凸性即给 $u_l<u_*<u_h$。映射 $x\mapsto x^2/[5(1+x^2)]$ 的导数为 $2x/[5(1+x^2)^2]>0$，其两端值正是 (III.26.2) 的有理数。

由二重根方程和三次式的首两项系数，展开即得 (III.26.2) 的因式分解；余项恰为 $F_{x_*}(u_*)+(u-u_*)F'_{x_*}(u_*)=0$。$a_3,a_2,u_*>0$ 使最后一因子严格正，$F''_{x_*}(u_*)>0$ 排除三重根。

为给代数性一个不依赖小数的消元式，置

$$
\Delta(x)=a_2^2a_1^2-4a_3a_1^3-4a_2^3a_0-27a_3^2a_0^2
 +18a_3a_2a_1a_0.
\tag{III.26.6}
$$

这是 $\mathbb Q(\sqrt2)[x]$ 中的非零八次多项式，首项系数为 $1504537804800+1062744883200\sqrt2$。二重根给 $\Delta(x_*)=0$，且

$$
u_*=
\left.\frac{9a_3a_0-a_2a_1}{2(a_2^2-3a_3a_1)}\right|_{x=x_*}.
\tag{III.26.7}
$$

分母严格正，因为 $a_3>0,a_1<0$。故 $x_*,u_*,d_*$ 均为实代数数。∎

## 27. 完整复源的双侧包含与唯一密度中心

**定理 27.1（纯接触分支直到实际首次端点）。** 对每个 $0<d\le d_*$，(III.25.1) 的秩二密度中心满足

$$
\sigma(d)-c(d)I\preceq\rho\preceq\sigma(d)+c(d)I
\quad(\rho\in\mathcal K_d),\qquad
r(d)=2\sqrt{5d(1-5d)}.
\tag{III.27.1}
$$

它是全部复密度中心中的唯一最优中心；竞争中心可以在 $\mathcal K_d$ 外，可以有任意复相干。两侧包含覆盖所有源秩、任意复 $b$、两个 $v$ 符号、奇异 $ah$ 块及秩三非极端态。

证明。先在 $x=x_*$ 检验 $L_x$。由 (III.25.5)、(III.26.2)，$P_x$ 的两个 $S$ 端值均非负；严格凹性给整个闭区间 $P_x\ge0$，退化的 $u=0,4$ 已包括。加上帽余量给 $\det L_{x_*}\ge0$，又 $l_2>0,l_1\ge0$，故 $L_{x_*}\succeq0$。

固定任一归一化帽形状，有

$$
\partial_xL_x=
\operatorname{diag}\left(S+Y-4,\frac{S+Y-9}{(1+x)^2}\right)\preceq0.
\tag{III.27.2}
$$

因此对所有 $0<x\le x_*$，$L_x\succeq L_{x_*}\succeq0$。帽与 $d$ 无关；这里只比较同一归一化形状的矩阵，没有把不同实际源的坐标拼接为一个共同实现。

令 $H=\sigma+cI=\operatorname{diag}(H_2,h_g)$，其中

$$
\begin{gathered}
h_g=\beta+c=\frac{1+x}{1+x^2}>1,\qquad
H_2/h_g=T_0\operatorname{diag}\left(x,\frac{x}{1+x}\right)T_0^{\mathsf T},\\
p=h_g-z=d(5/x-4+S+Y)>0,\qquad
pH_2-h_gA=dh_g\widehat L_x,\qquad M=zA-bb^\dagger\succeq0.
\end{gathered}
\tag{III.27.3}
$$

最后一个关系来自实际 $\rho\succeq0$ 对正标量 $z\ge\beta>0$ 的 Schur 补。对 $H-\rho$ 再用其正标量 $p$ 作 Schur 补，得到精确式

$$
H_2-A-\frac{bb^\dagger}{p}
=\frac{dh_g\widehat L_x+M}{p}\succeq0.
\tag{III.27.4}
$$

这证明全部实际复源的上侧包含，不需 $A^{-1}$，也不需把源分解为低秩态。

下侧沿用命题 18.2 的人口条件；为确定后面的等号，保留其 Schur 补的精确正项。对 $0<d<1/10$ 有 $Q<c<\beta$。令

$$
p_l=z+c-\beta\ge c>0,\qquad T=(1-z)I_2-A\succeq0.
$$

后者由 $A\succeq0,\operatorname{Tr}A=1-z$ 得到。下侧矩阵的 Schur 补恰为

$$
\begin{aligned}
A+cI_2-Qww^\dagger-\frac{bb^\dagger}{p_l}
={}&\frac{(\beta-Q)(z-\beta)}{p_l}I_2
 +Q(I_2-ww^\dagger)\\
&+\frac{\beta-c}{p_l}T+\frac{M}{p_l}\succeq0.
\end{aligned}
\tag{III.27.5}
$$

标量恒等式为 $(c-Q)-(\beta-c)(1-z)/p_l=(\beta-Q)(z-\beta)/p_l$，只用 $Q+\beta=1,c^2=Q\beta$。所有系数非负，且 $z>\beta$ 时第一项严格正。在 $d=1/10$，$cI-\sigma\succeq0$ 直接给下侧包含，不使用退化的 $c-Q$。所以这侧实际上在整个 $0<d\le1/10$ 成立。

匹配下界消费 (III.19.14) 的两个实际原纯源

$$
\psi_\pm=\sqrt Q\,w\pm\mathrm i\sqrt\beta\,g,\qquad
\rho_\pm=\psi_\pm\psi_\pm^\dagger.
\tag{III.27.6}
$$

它们在整个 $0<d\le1/10$ 均可取 $A_{\rm lift}=\rho_\pm,D_{\rm lift}=0$；原 $aa,C,E$ 矩分别为 $d,d,(6-5d)/16$，原固定 $N$ 条件不变。用实际复投影而非只对实中心的投影实部，置

$$
\begin{gathered}
v_\pm=(w\pm\mathrm ig)/\sqrt2,\quad \Pi_\pm=v_\pm v_\pm^\dagger,
\quad p_+=p_-=1/2>0,\\
(\rho_\pm-\sigma)v_\pm=cv_\pm,\quad
\operatorname{Tr}(\Pi_\pm\rho_\pm)=1/2+c,\\
M_0=(\Pi_++\Pi_-)/2=(ww^\dagger+gg^\dagger)/2,\quad
I/2-M_0=z_0z_0^\dagger/2\succeq0,\quad (I/2-M_0)\sigma=0.
\end{gathered}
\tag{III.27.7}
$$

由迹零 Hermitian 差的变分范数公式，对每个复密度 $\theta$，

$$
\frac12\max_{\rho\in\mathcal K_d}\|\rho-\theta\|_1
\ge\frac12\max_\pm\|\rho_\pm-\theta\|_1
\ge\max_\pm\operatorname{Tr}(\Pi_\pm(\rho_\pm-\theta))
\ge\frac12+c-\operatorname{Tr}(M_0\theta)
=c+\frac12\theta_{z_0z_0}\ge c.
\tag{III.27.8}
$$

这是对全部中心的正权法锥下证书，两个权重均严格正，不要求中心满足源矩。若两纯源到 $\theta$ 的距离都不超过 $2c$，等号迫使 $\theta_{z_0z_0}=0$。密度正性使整个 $z_0$ 行列为零。在 $(w,g)$ 上写 $\theta=\begin{pmatrix}\eta&b_0\\\overline b_0&1-\eta\end{pmatrix}$，其中 $b_0\in\mathbb C$，两项范数条件给

$$
(\eta-Q)^2+|b_0+\mathrm ic|^2\le c^2,\qquad
(\eta-Q)^2+|b_0-\mathrm ic|^2\le c^2.
$$

平均后 $(\eta-Q)^2+|b_0|^2\le0$，所以 $\theta=\sigma$。这个唯一可能中心结论在全部 $0<d\le1/10$ 都成立，独立于上侧包含是否成立。

最后，三阶迹零 Hermitian 矩阵的正、负谱质量相等，且至少一侧仅有一个非零特征值，故 $\|D\|_1=2\|D\|_{\rm op}$。双侧包含给上界 $2c$，(III.27.8) 给所有复中心的下界及唯一性；原通道约化 (III.1.6) 给 (III.27.1)。∎

## 28. 首次端点的实际复混合族与固定平面提升

**定义 28.1（固定代数混合形状及其全部相位）。** 用定理 26.1 的同一对 $(x_*,u_*)$ 定义

$$
\begin{gathered}
S_0=\frac{u_*(4-u_*)}{4\kappa},\quad
Y_0=u_*-(1+2\tau)S_0,\quad
A_0=\begin{pmatrix}1+S_0&-(S_0+Y_0)/2\\-(S_0+Y_0)/2&Y_0\end{pmatrix},\\
l_{1*}=l_1(x_*,S_0,Y_0),\quad k_*=(4+7S_0-Y_0)/10,\quad
r_0=(k_*+2l_{1*},-2k_*+l_{1*})^{\mathsf T},\\
R_0=r_0^{\mathsf T}A_0r_0,\quad Q_0=q_b^{\mathsf T}A_0r_0,\quad
H_0=1+S_0+Y_0.
\end{gathered}
\tag{III.28.1}
$$

$r_0$ 是 $ah$ 坐标中的二分量实向量，不是原输入基向量 $r$。以下 $\widehat L_x$ 均在这一固定形状 $S_0,Y_0,V=0$ 上求值。对每个 $0<d\le1/10$，令

$$
\begin{gathered}
z_d=1-dH_0,\quad h_d=4dS_0/\sqrt6,\quad
b_R(d)=\sqrt{dz_d/R_0}\,A_0r_0,\quad
t_d=\frac{h_d}{q_b^{\mathsf T}b_R(d)},\\
\epsilon_\pm(d)=t_d\pm\mathrm i\sqrt{1-t_d^2},\quad
b_\pm(d)=\epsilon_\pm(d)b_R(d),\quad
\rho_{R,\pm}(d)=\begin{pmatrix}dA_0&b_\pm(d)\\b_\pm(d)^\dagger&z_d\end{pmatrix}.
\end{gathered}
\tag{III.28.2}
$$

所有根式取非负根。

**命题 28.2（整个参数段上的实际秩二复混合源）。** (III.28.1)–(III.28.2) 的分母、根式及两个不同相位在整个 $0<d\le1/10$ 合法。每个 $\rho_{R,\pm}(d)$ 是原 $\mathsf R_+$ 极端层内的实际秩二密度，$A=dA_0\succ0$，$s=dS_0>0$、$\det B_d=0$；其 $ag,hg$ 虚相干都非零。它们具有原固定 $N$ 提升及五维原前驱。

证明。二重根及 (III.25.5) 给 $\det L_{x_*}=0$，$l_{1*},l_{2*}>0$。由矩阵乘法，

$$
T_0^{\mathsf T}r_0=\sqrt5(k_*,l_{1*})^{\mathsf T},\qquad
L_{x_*}(k_*,l_{1*})^{\mathsf T}
=(0,\det L_{x_*})^{\mathsf T}=0.
\tag{III.28.3}
$$

故 $\widehat L_{x_*}r_0=0$。$S_0=S_{\max}(u_*)>0$ 且

$$
\det A_0=S_0[(1+\tau)Y_0+\tau(1+\tau)S_0+\tau^2]>0,
\tag{III.28.4}
$$

所以 $A_0\succ0$。

为把相位存在性固定在整个段而非单个样本上，用 (III.26.2) 的闭隔离盒及 $7071/5000<\sqrt2<14143/10000$ 在 (III.28.1) 中作有理区间代入，得到

$$
\begin{gathered}
\frac{419445}{10^6}<S_0<\frac{426877}{10^6},\quad
\frac{126619}{10^6}<Y_0<\frac{146769}{10^6},\quad
\frac{1579880}{10^6}<l_{1*}<\frac{1635321}{10^6},\\
\frac{19}{5}<(r_0)_a<4,\quad \frac15<(r_0)_h<\frac3{10},\\
\frac{27}{5}<(A_0r_0)_a<\frac{28}{5},\quad
-\frac{11}{10}<(A_0r_0)_h<-1,\quad
20<R_0<22,\quad Q_0>\frac{21}{10}>2.
\end{gathered}
\tag{III.28.5}
$$

例如先以 $S_0=u_*(4-u_*)/(4\kappa)$ 取得第一界，再以 $Y_0=u_*-(1+2\tau)S_0$ 取得第二界；将两者代入 $l_{1*}=(6/5-x_*)(4-S_0-Y_0)+3S_0/5$，继而依次代入 $k_*,r_0,A_0r_0,R_0,Q_0$。每次乘法取四个有理端积的最小、最大值，除法只除以同号的正区间，得到以上外向界。因此这些界只用有理不等式和隔离盒，不依赖小数近似。

有 $z_{1/10}>21/25$；并且定义

$$
E_0(d)=z_dQ_0^2-\frac83dS_0^2R_0
=Q_0^2-d\left(H_0Q_0^2+\frac83S_0^2R_0\right).
\tag{III.28.6}
$$

由 (III.28.5) 及 $S_0<43/100$，

$$
E_0(1/10)>
\frac{21}{25}\left(\frac{21}{10}\right)^2
-\frac4{15}\left(\frac{43}{100}\right)^2\!22
>\frac{12}{5}>0.
\tag{III.28.7}
$$

$z_d$ 与 $E_0(d)$ 都随 $d$ 严格递减，所以上述正界在整个指定段成立。又 $q_b^{\mathsf T}b_R=\sqrt{dz_d/R_0}\,Q_0>0$，故

$$
0<t_d^2=\frac{(8/3)dS_0^2R_0}{z_dQ_0^2}<1.
\tag{III.28.8}
$$

两个相位不同、模为一。由 (III.28.5) 的两个非零分量，$b_\pm$ 的两项虚部都非零。此处设 $V=0$ 只是这个实际见证族的形状，没有将完整源限制到实截面。

用 $A_0\succ0$ 计算，$b_\pm^\dagger(dA_0)^{-1}b_\pm=z_d$，或者直接写

$$
\rho_{R,\pm}=G_\pm(dA_0)G_\pm^\dagger,\qquad
G_\pm=\begin{pmatrix}I_2\\
\overline{\epsilon_\pm}\sqrt{z_d/(dR_0)}\,r_0^{\mathsf T}
\end{pmatrix}.
\tag{III.28.9}
$$

这给正性和秩恰二。迹为一，原 $C$ 矩为 $d$；$\Re(q_b^{\mathsf T}b_\pm)=h_d$ 结合 (III.21.2) 给原 $E$ 矩 $(6-5d)/16$。帽余量恰为零，故 $\det B_d=0$；其左上项 $d>0$，右下项

$$
L_\rho=\ell^\dagger\rho\ell
=d\alpha^2[(1+\tau)Y_0+\tau(1+\tau)S_0+\tau^2]>0.
$$

因此 $B_d\succeq0$ 且秩一。连同 $s>0,A\succ0,\operatorname{rank}\rho=2$，这正是母卷 §36 的原 $\mathsf R_+$ 层。

实际固定平面提升是 §24 公式在这个饱和边界的直接取值：

$$
A_{\rm lift}=\frac{\rho\ell\ell^\dagger\rho}{L_\rho},\qquad
D_{\rm lift}=\rho-A_{\rm lift},\qquad
\omega_{R,\pm}=V_{\rm phys}^\dagger(A_{\rm lift}\oplus D_{\rm lift})V_{\rm phys}.
\tag{III.28.10}
$$

若 $u_\ell=\rho^{1/2}\ell/\sqrt{L_\rho}$，则 $\|u_\ell\|=1$，
$D_{\rm lift}=\rho^{1/2}(I-u_\ell u_\ell^\dagger)\rho^{1/2}\succeq0$，且 $D_{\rm lift}\ell=0$。于是其范围位于固定 $N=\ell^\perp$，没有旋转 $N$。$\det B_d=0$ 给 $(A_{\rm lift})_{aa}=d$；两提升分量各秩一。原 $V_{\rm phys}$ 满足 $V_{\rm phys}^\dagger V_{\rm phys}=I_5,V_{\rm phys}V_{\rm phys}^\dagger=I_3\oplus P_N$，所以 $\omega_{R,\pm}$ 是合法五维秩二原源。相应 $T_{\omega_{R,\pm}}$ 由 (III.24.1) 给出，并满足全部原深度数据。∎

## 29. 端点的全部接触与严格连续离开

**定理 29.1（四个上接触、两个下接触）。** 在 $d=d_*$，相对于唯一中心 $\sigma(d_*)$，上侧矩阵 $\sigma+cI-\rho$ 奇异的实际原源恰为

$$
\rho_+(d_*),\quad\rho_-(d_*),\quad
\rho_{R,+}(d_*),\quad\rho_{R,-}(d_*).
\tag{III.29.1}
$$

下侧矩阵 $\rho-\sigma+cI$ 奇异的实际原源恰为前两个纯源。这里的上、下接触按两侧 Loewner 矩阵分别定义；匹配下证书 (III.27.7) 只使用两个严格正的纯源权重，不要求两个混合接触有正权。

证明。在 $x=x_*$，(III.25.5) 的 $S=0$ 端点对所有 $u<4$ 严格正，因为 $x_*<5/6$ 且 $1-x_*(4-u)/5>0$。另一端点由 (III.26.2) 只有 $u=u_*$ 和 $u=4$ 两个可能零值。$0<u<4$ 时 $S_{\max}>0$，严格凹性使任何严格内部 $S$ 的 $P_x$ 大于端点连线，故严格正。把非负帽余量加回后，$\det L_{x_*}=0$ 只能在

$$
(S,Y,V)=(0,4,0)\quad\text{或}\quad(S_0,Y_0,0).
\tag{III.29.2}
$$

在混合端点，帽余量迫使 $V^2=0$；在 $u=4$ 也如此。$u=0$ 的唯一帽点由 (III.25.5) 直接严格正。因 $l_2>0$，两个奇异 $L$ 均为秩一。

对任意实际上接触，$p>0$，(III.27.4) 是两个半正定项之和，故其非零核向量同时位于 $\widehat L$ 与 $M$ 的核。外层形状因此必为 (III.29.2)。在第一种形状 $A=Qww^\dagger,z=\beta$，原正性给 $b=w\zeta$、$|\zeta|\le c$，原实矩给 $\Re\zeta=0$。沿 $w$ 的上 Schur 补为 $c-|\zeta|^2/c$，接触迫使 $|\zeta|=c$，恰得到两个 $\rho_\pm$。

在第二种形状，$\ker\widehat L=\mathbb Cr_0$。$r_0^\dagger M r_0=0$ 恰为

$$
|r_0^\dagger b|^2=z_ddR_0.
\tag{III.29.3}
$$

由 $A=dA_0\succ0$，Cauchy–Schwarz 链
$|r_0^\dagger b|^2\le(r_0^\dagger A r_0)(b^\dagger A^{-1}b)\le z_d(r_0^\dagger A r_0)$
的等号迫使 $b=\epsilon\sqrt{dz_d/R_0}A_0r_0$、$|\epsilon|=1$。原实矩随即给 $\Re\epsilon=t_{d_*}$；因 $0<t_{d_*}<1$，只有定义 28.1 的两个相位。反过来，这两源满足 (III.29.3) 且 $\widehat L_{x_*}r_0=0$，故 (III.27.4) 沿 $r_0$ 为零；定理 27.1 的全域正性使其确为上接触。这同时排除了额外秩三或非极端上接触。

下侧由 (III.27.5) 看出：$z>\beta$ 时第一项严格正，所以没有接触。若 $z=\beta$，则 $S+Y=4$，而 $S+Y=u-2\tau S\le4$ 迫使 $u=4,S=0,Y=4,V=0$。在同一 $b=w\zeta$ 形状上，下 Schur 补沿 $w$ 也是 $c-|\zeta|^2/c$，故只有两个纯接触。∎

**定理 29.2（整段严格离开而非单点违反）。** 对每个

$$
d_*<d\le\frac1{10},\qquad
r(d)>2\sqrt{5d(1-5d)}.
\tag{III.29.4}
$$

特别地，$d_*$ 是初始纯接触中心与半径分支的真实首次离开点；本结论不指定离开后的最优中心或半径公式。

证明。保持定义 28.1 的同一固定代数形状，$d_*<d\le1/10$ 对应 $x_*<x\le1$。$S_0+Y_0<4$ 使 (III.27.2) 的两个对角导数严格负，非对角项不变，所以

$$
\widehat L_x-\widehat L_{x_*}\prec0,\qquad
r_0^{\mathsf T}\widehat L_xr_0<0.
$$

命题 28.2 已在整个参数段给实际复混合源。这里
$p=h_g-z_d=d(5/x-4+S_0+Y_0)>0$，包括 $x=1$。其上 Schur 补沿 $r_0$ 的值精确为

$$
r_0^{\mathsf T}\left(H_2-dA_0-\frac{b_\pm b_\pm^\dagger}{p}\right)r_0
=\frac{dh_g}{p}\,r_0^{\mathsf T}\widehat L_xr_0<0,
\tag{III.29.5}
$$

因为 (III.29.3) 在所有这些 $d$ 都成立。原三阶矩阵的显式负向量为 $(r_0,b_\pm^\dagger r_0/p)^{\mathsf T}$。因此 $\|\rho_{R,\pm}(d)-\sigma(d)\|_1>2c(d)$，端点 $d=1/10$ 也包括。

这仍需排除另一中心把风险降回 $2c$。定理 27.1 证明中的两个实际纯源，对全部 $0<d\le1/10$ 给所有复中心的下界 $2c$，并迫使任何风险不超过 $2c$ 的中心恰为 $\sigma(d)$。另一方面，原 $\mathcal K_d$ 由密度条件、仿射矩、$s\ge0,B_d\succeq0$ 给非空闭有界集，故紧；全部复密度中心也紧。最坏风险函数关于中心在迹范数下为 $1$-Lipschitz，因此最小值达到。若 $r(d)=2c$，达到中心只能是 $\sigma(d)$，与实际混合源的严格违反矛盾。因此每个参数都有严格最小最大超额，而不是仅有一个非最优中心的采样反例。∎

## 30. 原五维共同重建、全参考转移与剩余中央目标

**推论 30.1（原通道及任意有限未触动参考上的精确结论）。** 对定义 1.1 的全部原 CPTP 源 $T:M_3(\mathbb C)\to M_5(\mathbb C)$，保持全部 $j\ge0$ 的输入效果算子等式，不限制输出支持或 Kraus 秩。对全部共同 CPTP 重建 $R:M_3\to M_5$，定理 27.1 的 $2c(d)$ 是 $0<d\le d_*$ 的原最小最大 diamond 风险，达到它的一个重建是

$$
R_{\sigma(d)}(X)=B[UP_+XP_+U^\dagger+(f^\dagger Xf)\sigma(d)]B^\dagger.
\tag{III.30.1}
$$

定理 29.2 的严格超额也是这一原共同重建问题的严格超额。范数保持 (III.1.2) 的全部有限 $n$ 及全部复矩阵 $X$，没有正输入限制或参考维数截断；唯一性结论只针对密度中心，不另断言共同 CPTP 重建唯一。

证明。直接消费母卷定理 35.2–35.5、(III.1.6) 及命题 24.1 的同一双向对应。纯接触的实际五维向量是

$$
\phi_\pm=\sqrt d(Bq-2Br)\pm\mathrm i\sqrt\beta\,c_5,
\qquad c_5=(e_0+e_1-e_3-e_4)/2,\qquad
V_{\rm phys}\phi_\pm=(\psi_\pm,0).
$$

混合源使用 (III.28.10)。两者都由原
$T_\omega(X)=BP_+XP_+B^\dagger+(f^\dagger Xf)\omega$
实现；谱 Kraus 算子 $BP_+$ 与 $\sqrt{\lambda_j}w_jf^\dagger$ 的伴随平方和为 $I_3$。同一原三个完整效果矩及其递推给所有深度 $Y_j$，并有 $\mathcal GT_\omega=S_\rho$。这不是只匹配 $ff^\dagger$ 输入的数据；母卷的反向对应也覆盖任意复 Kraus 源，不以这些显式前驱限制对手。

(III.30.1) 是 (III.24.2) 在此中心上的取值，Kraus 算子为 $BUP_+$ 和 $\sqrt{\mu_j}Bu_jf^\dagger$。对于每个有限 $n$、每个 $X\in M_n(\mathbb C)\otimes M_3(\mathbb C)$，既有 (III.24.3) 精确给

$$
(\operatorname{id}_n\otimes(S_\rho-R_\sigma))(X)
=X_{ff}\otimes B(\rho-\sigma)B^\dagger,\qquad
X_{ff}=(I_n\otimes f^\dagger)X(I_n\otimes f),
\qquad \|X_{ff}\|_1\le\|X\|_1.
$$

迹范数的压缩理想性质、张量奇异值乘法及 $B^\dagger B=I$ 给上界，$n=1,X=ff^\dagger$ 达到等号。反过来，每个不受形式限制的原共同 CPTP $R$ 经同一

$$
\mathcal C_B(Y)=B^\dagger YB+\operatorname{Tr}[(I_5-BB^\dagger)Y]gg^\dagger
$$

得到任意复密度 $\theta=\mathcal C_B(R(ff^\dagger))$，未要求它在 $\mathcal K_d$ 内；(III.24.4) 给
$\|R-S_\rho\|_\diamond\ge\|\theta-\rho\|_1$。
所以全部复中心的匹配下界、唯一可能中心及严格离开均转移至原重建问题。上述通道与范数对应是既有供应，此处只把新端点和实际新混合接触接回同一原问题。∎

**命题 30.2（旧充分端点与新首次转折的精确关系）。** 定理 19.1 的 $d_{\rm low}$ 严格小于 $d_*$，而 $d_*<5/61<d_{\rm high}$。定理 19.1、20.2 的充分端点及既有结论保持成立；定义 24.2 所列的未解区间现在缩为

$$
d_*<d<d_{\rm high}.
\tag{III.30.2}
$$

其中 $(d_*,1/10]$ 已有定理 29.2 的严格超额，但尚无完整达到中心与精确半径，故未被计作已求解区间。

证明。(III.19.3) 给 $T_{\rm low}<77/100<4/5<x_*$，严格递增映射 $x\mapsto x^2/[5(1+x^2)]$ 给 $d_{\rm low}<d_*$。同一映射将 $5/6$ 送到 $5/61$，故 $x_*<5/6$ 给 $d_*<5/61$；$5/61<d_{\rm high}$ 沿用定义 24.2。定理 27.1 将同一中心的精确初始分支延伸至 $d_*$，定理 29.2 则证明它紧接着严格失效。因此这里确定的是该初始分支的真实首次转折，不是把旧余因子充分端点改称实际转折，也没有断言 $d_{\rm high}$ 的最大性或下一接触型持续存在。∎

**定义 30.3（未决关系及模型前提）。** (III.30.2) 中仍待确定实际达到的全部五实坐标中心、精确原半径、覆盖全部复源的上证书及对全部复中心的匹配正权下证书。$5/61$ 的既有定量括号、实际混合超额及 §§14–16、§§21–22 的完整条件消元继续适用；没有一个既有可行上中心在这里被断言为最优。新的具体起点是 (III.29.1) 的实际纯/混合接触及其全部相位，后继接触方程仍须在两个实际外层域同时通过全称包含，并满足正权法锥条件；端点已有两个混合接触不自动给它们在后继最优证书中的正权或持续性。

本节条件数学保持原复 Hilbert 空间、密度及 Born 配对、CP/TP、原复组合、固定五维仪器、固定 $N$、擦除标签原菜单及精确完整输入效果数据。所有帽坐标、相位、提升和接触来自同一实际 $\rho$ 及原实现。全部有限未触动参考只是原范数量词；数学存在的效果、通道或提升不授予新的制备、相位控制、采集、仪器分支、标签历史、独立或相关副本、参考制备、返回环境或其他操作。没有引入噪声或有限精度模型，也没有由这些条件结论推出 Hilbert/Born/CP 的起源、物理完成或信息守恒。

**定义 30.4（数学归属）。** 归一化原帽上的精确二重根端点、全复双侧证书、无中心限制的唯一性、实际复混合接触的完整分类及整段严格离开是本原源的综合推导 `repo-derived`。PSD 主块与 Schur 补、Cauchy–Schwarz 等号、凹函数端点界、三次判别式与实根隔离、紧性达到和迹范数变分原理均作为成熟中间工具在相应证明内使用，不单列为新的通用理论。原通道/Kraus 与完全有界迹范数的文献供应沿用定义 1.4 的 Watrous 第二、三章；原极端层、提升及通道等价直接复用母卷 §§35–36 和本卷 §24。这里不主张这些工具或源特定应用的文献优先权。

## 追加锚（本行以下为增补区）
