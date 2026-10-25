# 相容预测波与关系谱 III：原完整纤维的精确最小最大分支

## 1. 原问题、忠实提升与接触族

**定义 1.1（原模型及范数约定）。** 母卷指《[相容预测波与关系谱](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md)》。固定母卷 §17.1、§29.1 的复 Hilbert 空间、五维原仪器、等距嵌入 $B$、酉矩阵 $U$、输入正交基 $(q,r,f)$ 及 $P_+=qq^\dagger+rr^\dagger$。原菜单只给擦除分支标签后的全深度效果 $J_j=(\mathcal G^\dagger)^j(P)$。对 $0<t<1$ 置 $d=t^2$，令

$$
\mathcal F_t=\{T:M_3(\mathbb C)\longrightarrow M_5(\mathbb C)\text{ CPTP}:
T^\dagger(J_j)=Y_j\ (j\ge0)\},\qquad
r(d)=\inf_{R\ {m CPTP}}\sup_{T\in\mathcal F_{\sqrt d}}
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
y_{\epsilon,\delta}=\delta\,\mathrm i\sqrt{1-d-u},
\frac{b_\epsilon}{|b_\epsilon|},\qquad
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
