# AURIC FIB：固定观测路径上的最优恢复系数与固定解码器障碍

本文给出 **UNEXECUTED：可错、未经执行的条件符号数学**。经典极小极大值、实际缺陷和一个可行变化解码器来自下列明确来源接口；本文在这些接口下证明，对同一条实际仪器路径的全部共同 CPTP 解码器，最优误差满足

$$
\varepsilon_\star(\mathcal N_0)=Q,\qquad
Q-Dt-C_{\rm low}t^2
\le\varepsilon_\star(\mathcal N_t)
\le\varepsilon(\mathcal R_t,\mathcal N_t)
\le Q-Dt+Lt^2.
\tag{0.1}
$$

这里 $D>0$ 是固定的精确一阶系数。因而最优值在零点的右导数是 $-D$，同一路径上的根缺陷首项系数是 $D/\sqrt\gamma$。另一个结论是：任何单个固定解码器都不能从 $Q$ 获得严格正的一阶改善；允许解码器随已知的 $t$ 共同调节，才能取得上述负导数。

本文没有 Lean 或 kernel 证明，没有执行算术、公式测试、数值求根或优化；普通符号证明及来源接口是全部数学证据。来源简称为 [S《固定忠实三态的恢复缺陷平方根阶尖锐性》](AURIC_FIB_SQUARE_ROOT_RECOVERY_DEFECT_SHARPNESS.md)、[R《实际仪器保留量子输出的稳健恢复障碍》](AURIC_FIB_ROBUST_ACTUAL_QUANTUM_RECOVERY.md) 和 [C《零保真缺陷下的严格正经典恢复间隙》](AURIC_FIB_ZERO_DEFECT_CLASSICAL_RECOVERY_GAP.md)。C 定理 2.1 的全有限 POVM 经典最优值、S §§4–6 的可行解码器及其达到系数、S 定理 7.2 的平方根指数尖锐性均为继承结果。这里补足的是对任意量子解码器的统一下证书，以及固定解码器与变化解码器的量词区别；这些结论不附带外部真实性、文献查全或优先权认证。

## 1. 固定三态、实际路径和恢复目标

**定义 1.1（固定三个量子比特态）。** 以下 $M_n$ 表示 $n$ 阶复矩阵代数，信道指复线性、完全正、保迹映射（CPTP）。输入和保留系统分别为 $\mathcal H_A=\mathbb C^2$、$\mathcal H_B=\mathbb C^2$，记录空间 $C_{\rm rec}=\mathbb C^2$ 的基为 $+,-$。这是一族三个量子比特态，每个态位于同一个二维空间。令

$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\qquad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
\rho(x,y,z)=\frac{I_2+xX+yY+zZ}{2}.
$$

固定

$$
\begin{aligned}
\sigma_0&=\rho(u,0,0)=\begin{pmatrix}1/2&1/4\\1/4&1/2\end{pmatrix},\\
\sigma_+&=\rho(v,0,w)=\begin{pmatrix}3/4&\sqrt3/8\\\sqrt3/8&1/4\end{pmatrix},\\
\sigma_-&=\rho(v,0,-w)=\begin{pmatrix}1/4&\sqrt3/8\\\sqrt3/8&3/4\end{pmatrix},\qquad
u=w=\frac12,\quad v=\frac{\sqrt3}{4}.
\end{aligned}
\tag{1.1}
$$

三态迹一，特征值依次为 $3/4,1/4$ 以及两次 $(4+\sqrt7)/8,(4-\sqrt7)/8$。因此全族有固定共同忠实下界

$$
\sigma_i\succeq\mu I_2,\qquad \mu=\frac{4-\sqrt7}{8}>0.
\tag{1.2}
$$

锚 $\sigma_0$ 的 $1/4$ 下界只属于该锚。以下状态、维数、记录数和共同下界都不随参数改变。

**定义 1.2（指定的实际弱仪器）。** 对 $0\le t<1/\sqrt2$，令

$$
a_t=\sqrt{1-t^2},\quad k_t=1-2t^2,\quad
K_+(t)=\begin{pmatrix}a_t&0\\0&t\end{pmatrix},\quad
K_-(t)=\begin{pmatrix}t&0\\0&a_t\end{pmatrix},
$$

$$
\mathcal N_t(\Theta)=
|+\rangle\langle+|\otimes K_+(t)\Theta K_+(t)^\dagger+
|-\rangle\langle-|\otimes K_-(t)\Theta K_-(t)^\dagger.
\tag{1.3}
$$

每个实际记录恰有一个 Kraus 算子。由
$K_+^\dagger K_++K_-^\dagger K_-=I_2$，此联合信道完全正且保迹。解码器接收实际两记录与保留量子比特组成的全部四维输出，没有未记录环境或额外 Kraus 指标。

**定义 1.3（共同解码竞争与经典比较量）。** 对整个 $M_4$ 上到 $M_2$ 的复线性 CPTP 映射 $\mathcal R$，定义

$$
\varepsilon(\mathcal R,\mathcal N_t)
=\max_{i\in\{0,+,-\}}\frac12
\|\mathcal R\mathcal N_t(\sigma_i)-\sigma_i\|_1,
\qquad
\varepsilon_\star(\mathcal N_t)
=\inf_{\mathcal R:M_4\to M_2\ \mathrm{CPTP}}
\varepsilon(\mathcal R,\mathcal N_t).
\tag{1.4}
$$

其中 $\|\Theta\|_1=\operatorname{Tr}\sqrt{\Theta^\dagger\Theta}$。共同指每个已知 $t$ 只能选择一个不依赖未知标签 $i$ 的映射。下确界允许任意复杂相位、混合输出和非酉操作，也允许每个 $t$ 独立选择映射。误差只检验三个指定态，使用全部实际分支平均后的输出。量子比特 Bloch 残差为 $f$ 时，差矩阵的特征值是 $\pm\|f\|_2/2$，故半迹误差为 $\|f\|_2/2$。

经典比较量为

$$
Q=\inf_{\substack{(F_y)\text{ 任意有限 POVM}\\
\vartheta_y\text{ 任意输入空间密度矩阵}}}
\max_i\frac12\left\|
\sum_y\operatorname{Tr}(F_y\sigma_i)\vartheta_y-\sigma_i
\right\|_1.
\tag{1.5}
$$

它允许任意有限结果数、零效应和混合制备。这个定义不会授权更换 (1.3) 的实际仪器，也不把 (1.4) 的量子解码器限制为经典制备。

**定义 1.4（同一路径的实际缺陷）。** 令

$$
\begin{aligned}
E_+(t)&=\operatorname{diag}(1-t^2,t^2),&
E_-(t)&=\operatorname{diag}(t^2,1-t^2),\\
p_i(\xi)&=\operatorname{Tr}(E_\xi(t)\sigma_i),&
F_{ij}&=\|\sqrt{\sigma_i}\sqrt{\sigma_j}\|_1,\\
C_{ij}(t)&=\sum_{\xi=+,-}\sqrt{p_i(\xi)p_j(\xi)},&
G_t&=\frac13\sum_{i<j}(C_{ij}(t)-F_{ij}).
\end{aligned}
\tag{1.6}
$$

$F_{ij}$ 是根保真度。S 命题 3.3 给出以下实际公式。写 $r=t^2$，则

$$
\begin{aligned}
\delta_0(r)&=\delta_{0+}(t)=\delta_{0-}(t)
=\frac{\sqrt{3-2r}+\sqrt{1+2r}-\sqrt3-1}{2\sqrt2},\\
\delta_{\rm side}(r)&=\delta_{+-}(t)
=\frac{\sqrt{3+4r-4r^2}-\sqrt3}{2},\\
G_t&=\frac{2\delta_0(t^2)+\delta_{\rm side}(t^2)}3,\\
\gamma&=\frac{(1-1/\sqrt3)/\sqrt2+1/\sqrt3}{3}>0,
\qquad \lim_{t\downarrow0}\frac{G_t}{t^2}=\gamma.
\end{aligned}
\tag{1.7}
$$

为明确同一实现与严格正性，实际概率为锚的 $(1/2,1/2)$、$+$ 态的 $(3/4-r/2,1/4+r/2)$ 和 $-$ 态的反序。继承的固定输入根保真值为
$F_{0+}=F_{0-}=(\sqrt3+1)/(2\sqrt2)$、$F_{+-}=\sqrt3/2$。将这些概率代入 (1.6)，两个经典根重叠分别为
$[\sqrt{3-2r}+\sqrt{1+2r}]/(2\sqrt2)$ 和 $\sqrt{3+4r-4r^2}/2$，即得 (1.7)。两缺陷在零点取零，而且

$$
\delta_0'(r)=\frac{1/\sqrt{1+2r}-1/\sqrt{3-2r}}{2\sqrt2}>0,
\qquad
\delta_{\rm side}'(r)=\frac{1-2r}{\sqrt{3+4r-4r^2}}>0
\quad(0<r<1/2).
\tag{1.8}
$$

故整个 $0<t<1/\sqrt2$ 上 $G_t>0$。零点的加权导数为 $\gamma$，由导数定义给出 (1.7) 的极限。这只是重述并接合 S 的实际缺陷接口，不是另换测量。族的最优化缺陷
$\Delta=\inf_F\frac13\sum_{i<j}(C_{ij}(F)-F_{ij})$ 为零，因为同一坐标 PVM 对每一对都等号成立；这个 $\Delta$ 不能替换正 $t$ 的实际 $G_t$。

## 2. 继承的精确根、支撑常数与余项常数

**来源接口 2.1（C 的全有限经典最优值）。** C 定理 2.1 给出唯一的 $T\in(v,u)$，满足

$$
u-T=\sqrt{(T-v)^2+w^2(1-\sqrt{1-T^2})^2}.
\tag{2.1}
$$

设

$$
b=\sqrt{1-T^2},\qquad e=u-T,\qquad d=T-v,\qquad h=u-v=e+d.
$$

于是

$$
T^2+b^2=1,\qquad e^2=d^2+w^2(1-b)^2,\qquad
Q=e/2>0.
\tag{2.2}
$$

达到经典值的方案为 $P_\pm=(I_2\pm Z)/2$ 后制备

$$
\omega_\pm=\frac{I_2+TX\pm bZ}{2}.
\tag{2.3}
$$

两态纯，三个误差均为 $Q$。本文直接复用该全有限 POVM 最优值，不重复其全局经典优化证明。参数对应为 C 的 $t_\star=T,c_\star=b,d_\star=d$；C 仿射重建中的平移变量 $t$ 在本文记为 $\tau$，与仪器参数 $t$ 区分。

**定义 2.2（固定常数）。** 使用与 C 式 (2.9)、S 式 (4.1) 相同的常数，定义

$$
\begin{aligned}
\beta&=\frac{w^2(1-b)}b,& A&=d+\beta T,&
\ell&=e+A=h+\beta T,\\
\alpha&=\frac A\ell,& \kappa&=\frac\beta\ell,&
\eta&=uT+\frac{hd}{\beta},\\
D&=\kappa\eta b=\frac{b(hd+u\beta T)}\ell,&
M&=\frac{2b(eu+vd)}\ell.
\end{aligned}
\tag{2.4}
$$

再定义与 S §6 一致的区间与余项常数，以及新的下余项常数

$$
\begin{aligned}
r_0&=\min\left\{\frac14,\frac{T}{2M}\right\},&
V&=1+2M,\\
H&=6+6M+6M^2,&
L&=\frac{V^2/e+H}{4},&
C_{\rm low}&=\kappa(\eta^2+T+b).
\end{aligned}
\tag{2.5}
$$

因为 $v<T<u=1/2$，有 $e,d,h,T>0$、$1/2<b<1$、$1-b>0$，所以列出的所有分母严格正，$\beta,A,\ell,\kappa,\eta,D,M,r_0,V,H,L,C_{\rm low}$ 都严格正且有限。又 $1-\alpha=e/\ell>0$，因此 $0<\alpha<1$。本文的 $h$ 是 Bloch 参数、$\gamma$ 是 (1.7) 的路径缺陷系数、$H$ 是二阶导数界常数，均不使用 R 的同名谱间隙、Frobenius 块相干量或 Hilbert 空间含义。$A$ 是正标量，酉矩阵元素将用不同的 $\mathsf A_t,\mathsf B_t$ 表示。

## 3. 全复代数竞争的无损分支约化

**引理 3.1（分支限制与反向扩张）。** 任意允许解码器在实际路径上的作用，都由两个整个 $M_2$ 上的 CPTP 分支决定；任意这样的分支对都有整个 $M_4$ 上的 CPTP 扩张。

证明。对原解码器定义

$$
\Phi_\xi(\Theta)=\mathcal R(|\xi\rangle\langle\xi|\otimes\Theta).
\tag{3.1}
$$

嵌入 $\Theta\mapsto|\xi\rangle\langle\xi|\otimes\Theta$ 完全正且保迹，故各 $\Phi_\xi$ 复线性 CPTP。实际记录块对角性和线性给出

$$
\mathcal R\mathcal N_t(\Theta)
=\Phi_+(K_+\Theta K_+^\dagger)+\Phi_-(K_-\Theta K_-^\dagger).
\tag{3.2}
$$

反向，若两个分支有 Kraus 矩阵 $A_{\xi,j}$，则

$$
\mathcal R(\mathsf W)=\sum_{\xi=+,-}\Phi_\xi(\mathsf W_{\xi\xi}),\qquad
\mathsf W_{\xi\xi}=(\langle\xi|\otimes I_2)\mathsf W(|\xi\rangle\otimes I_2)
\tag{3.3}
$$

具有矩形 Kraus $A_{\xi,j}(\langle\xi|\otimes I_2)$，其伴随乘积和为
$\sum_\xi|\xi\rangle\langle\xi|\otimes\sum_j A_{\xi,j}^\dagger A_{\xi,j}=I_4$。因此 (3.3) 在整个 $M_4$ 上完全正、保迹，包括记录相干输入。对实际竞争而言，记录非对角行为不参与 (3.2)；但任意其他完整扩张仍必须满足 CP 和 TP。$\square$

**引理 3.2（对称平均及下界方向）。** 可无损地将下确界限制为输入记录去相干、对记录交换与 $X$ 协变、且对共轭 Kraus 变换不变的解码器。每个原解码器都有一个此类代表 $\overline{\mathcal R}$，满足

$$
\varepsilon(\overline{\mathcal R},\mathcal N_t)
\le\varepsilon(\mathcal R,\mathcal N_t)
\quad\text{对全部 }t.
\tag{3.4}
$$

证明。令 $S_{\rm rec}$ 交换两记录，$W_{\rm rec}=S_{\rm rec}\otimes X$。实际实 Kraus 给出

$$
\mathcal N_t(X\Theta X)=W_{\rm rec}\mathcal N_t(\Theta)W_{\rm rec},\qquad
\mathcal N_t(\Theta^{\mathsf T})=\mathcal N_t(\Theta)^{\mathsf T}.
$$

定义

$$
\mathcal R^X(\mathsf W)=X\mathcal R(W_{\rm rec}\mathsf W W_{\rm rec})X,
\qquad
\mathcal R^K(\mathsf W)=\bigl(\mathcal R(\mathsf W^{\mathsf T})\bigr)^{\mathsf T}.
\tag{3.5}
$$

第一式由酉共轭保持 CPTP。若原映射的任意复矩形 Kraus 为 $L_j$，第二式的 Kraus 是逐项复共轭 $\overline{L_j}$，因为
$(L_j\mathsf W^{\mathsf T}L_j^\dagger)^{\mathsf T}=\overline{L_j}\mathsf W L_j^{\mathsf T}$，其伴随乘积和仍为 $I_4$。这里不宣称单次转置是 CP。

$X$ 固定锚并交换两个侧态，转置固定每个输入。仪器协变性与迹范数不变性使四个映射 $\mathcal R,\mathcal R^X,\mathcal R^K,(\mathcal R^X)^K$ 的最大族误差相同。两个变换因 $X,W_{\rm rec}$ 为实矩阵而对易，所以四者平均同时不变。迹范数凸性给出平均误差不增。再在输入端复合记录去相干映射不改变实际重建，也保持两对称性。整个平均操作不依赖 $t$，固定映射经它仍为固定映射。

约化类是原类的子集，所以原下确界不大于约化下确界；每个原映射又有误差不增的约化代表，所以约化下确界不大于原下确界。两者相等，且对约化代表的统一下界按 (3.4) 转移给每个原映射。$\square$

**引理 3.3（一般仿射分支与实际加权合成）。** 对上述代表写 $\Phi=\Phi_+$。其一般形式为

$$
\Phi:(x,y,z)\longmapsto(r+px+qz,\lambda y,s+\nu x+mz),
\qquad r,p,q,\lambda,s,\nu,m\in\mathbb R,
\tag{3.6}
$$

并有 $\Phi_-=\operatorname{Ad}_X\circ\Phi\circ\operatorname{Ad}_X$。实际重建为

$$
(x,y,z)\longmapsto(\tau+ax,\,2a_tt\lambda y,\,cz),\qquad
\tau=r+k_tq,\quad a=2a_ttp,\quad c=m+k_ts.
\tag{3.7}
$$

证明。分支转置协变使 $y$ 符号翻转与仿射作用对易，恰好消去 $y$ 平移及 $y$ 与 $xz$ 的交叉系数，其余实系数全保留。这没有要求实 Kraus、纯态输出、酉性或极端点。

对未归一化矩阵 $(P I_2+Q_xX+Q_yY+Q_zZ)/2$，(3.6) 的线性延拓把平移分别乘以迹 $P$。实际两分支为

$$
\begin{aligned}
K_+\rho(x,y,z)K_+^\dagger
&=\frac12\left[\frac{1+k_tz}{2}I_2+a_ttxX+a_ttyY+\frac{k_t+z}{2}Z\right],\\
K_-\rho(x,y,z)K_-^\dagger
&=\frac12\left[\frac{1-k_tz}{2}I_2+a_ttxX+a_ttyY+\frac{z-k_t}{2}Z\right].
\end{aligned}
\tag{3.8}
$$

两式的迹分别为实际 Born 概率 $(1+k_tz)/2,(1-k_tz)/2$。负分支仿射式是
$(x,y,z)\mapsto(r+px-qz,\lambda y,-s-\nu x+mz)$。把 (3.8) 的迹与三个坐标代入两个线性延拓并相加，$X$ 坐标为 $r+k_tq+2a_ttpx$，$Y$ 坐标为 $2a_tt\lambda y$，$Z$ 坐标为 $(m+k_ts)z$，即 (3.7)。未归一化分支已经含有 Born 权重，不再条件归一化或二次加权。$\square$

设 $\Phi(|0\rangle\langle0|)$、$\Phi(|1\rangle\langle1|)$ 的 Bloch 坐标为 $(x_0,0,z_0)$、$(x_1,0,z_1)$。由 (3.6) 得到以后关键的精确关系

$$
\begin{aligned}
x_0&=r+q,& z_0&=s+m,& q&=(x_0-x_1)/2,&s&=(z_0+z_1)/2,\\
\tau&=x_0-2t^2q,&c&=z_0-2t^2s,& |q|&\le1,&|s|&\le1.
\end{aligned}
\tag{3.9}
$$

最后两个界来自两个输出均为密度矩阵。这些等式对每个 $t$ 的每个代表逐点成立，所有系数都允许随 $t$ 任意变化。

## 4. 对全部共同 CPTP 解码器的统一下证书

**引理 4.1（继承支撑恒等式的量子适用性）。** 对任意实 $(a,\tau,c)$，若

$$
R_{\rm B}=\max\left\{|\tau+ua-u|,
\sqrt{(\tau+va-v)^2+w^2(c-1)^2}\right\},
$$

则

$$
R_{\rm B}\ge e+\kappa(1-\eta a-T\tau-bc).
\tag{4.1}
$$

证明。锚范数给出 $R_{\rm B}\ge L_0=u-ua-\tau$。由 (2.2)，向量 $(d/e,-w(1-b)/e)$ 为单位向量，故侧态范数给出

$$
R_{\rm B}\ge L_1=
\frac{d(\tau+va-v)+w^2(1-b)(1-c)}e.
$$

按 $\alpha,1-\alpha$ 取正凸组合。其 $a,\tau,c$ 系数分别为

$$
\frac{-uA+vd}\ell=-\kappa\eta,\qquad
\frac{-A+d}\ell=-\kappa T,\qquad
-\frac{w^2(1-b)}\ell=-\kappa b.
$$

在 $(a,\tau,c)=(0,T,b)$ 处，$L_0=L_1=e$ 且 $T^2+b^2=1$，常数项也相同。因此整个仿射恒等式为

$$
\alpha L_0+(1-\alpha)L_1=e+\kappa(1-\eta a-T\tau-bc),
\tag{4.2}
$$

即 C 式 (2.11) 的参数重记。这个推导只用了范数支撑，对所有实参数成立；没有把 C 为经典测量制备建立的 $|a|+\sqrt{\tau^2+c^2}\le1$ 约束加到量子重建上。对 (3.7)，$R_{\rm B}$ 正是两倍最大半迹误差。$\square$

**引理 4.2（任意分支的伴随收缩约束）。** 设 $\Phi$ 为任意量子比特 CPTP 分支，$x_0=\operatorname{Tr}(X\Phi(|0\rangle\langle0|))$，$p=\operatorname{Tr}(X\Phi(X))/2$。则

$$
|p|\le\sqrt{1-x_0^2}.
\tag{4.3}
$$

证明。令 $J=\Phi^*(X)$，其中 $\Phi^*$ 为迹伴随。保迹使其含幺，完全正使其正。因 $I_2\pm X\succeq0$，有 $I_2\pm J\succeq0$。所以 $J$ 为 Hermitian 收缩，谱分解逐特征值给出 $J^2\preceq I_2$。这是对同一 Hermitian 矩阵的谱论断，不是对不对易矩阵擅自平方保序。又

$$
J_{00}=x_0,\qquad
p=\frac12\operatorname{Tr}(JX)=\operatorname{Re}J_{01}.
$$

取 $J^2\preceq I_2$ 的 $00$ 条目，得
$x_0^2+|J_{01}|^2\le1$，从而 (4.3)。任意复 Kraus、混合输出和非酉分支都包含在此证明中。$\square$

**命题 4.3（统一支撑上界）。** 对每个约化代表和 $0\le t<1/\sqrt2$，有

$$
\mathcal F:=\eta a+T\tau+bc
\le\sqrt{T^2+(b+2\eta a_tt)^2}+2(T+b)t^2.
\tag{4.4}
$$

证明。输出态的 Bloch 球约束给出 $x_0^2+z_0^2\le1$。代入 (3.9) 并用 (4.3)，得到

$$
\begin{aligned}
\mathcal F
&=Tx_0+bz_0+2\eta a_ttp-2t^2(Tq+bs)\\
&\le Tx_0+(b+2\eta a_tt)\sqrt{1-x_0^2}+2(T+b)t^2\\
&\le\sqrt{T^2+(b+2\eta a_tt)^2}+2(T+b)t^2.
\end{aligned}
\tag{4.5}
$$

第一步不等式使用 $T,b,\eta,a_t>0$、$t\ge0$、$|q|,|s|\le1$。第二步是单位向量 $(x_0,\sqrt{1-x_0^2})$ 与 $(T,b+2\eta a_tt)$ 的 Cauchy–Schwarz。这里只对支撑值作上估计，放宽部分联合信道约束在这个方向上合法；不宣称该上界在正 $t$ 可达到。$\square$

**定理 4.4（每个原解码器的精确根式下证书）。** 对每个原始、未必对称的完整输出共同 CPTP 解码器 $\mathcal R$，以及整个 $0\le t<1/\sqrt2$，有

$$
\begin{aligned}
\varepsilon(\mathcal R,\mathcal N_t)
&\ge Q+\frac\kappa2\left[
1-\sqrt{T^2+(b+2\eta a_tt)^2}-2(T+b)t^2\right]\\
&\ge Q-Dt-C_{\rm low}t^2.
\end{aligned}
\tag{4.6}
$$

同样的两个下界适用于 $\varepsilon_\star(\mathcal N_t)$。

证明。先按引理 3.2 平均，记其误差为 $\overline\varepsilon\le\varepsilon(\mathcal R,\mathcal N_t)$。引理 4.1 给出 $2\overline\varepsilon\ge e+\kappa(1-\mathcal F)$，命题 4.3 控制 $\mathcal F$，再除以二并使用 $Q=e/2$，即得 (4.6) 第一行，方向适用于每个原映射。

由 $T^2+b^2=1$，根式为
$\sqrt{1+4\eta ba_tt+4\eta^2a_t^2t^2}$。正平方根在 $1$ 的切线不等式 $\sqrt q\le1+(q-1)/2$ 对每个 $q\ge0$ 成立，所以第一行至少为

$$
Q-\kappa\eta ba_tt-\kappa(\eta^2a_t^2+T+b)t^2
\ge Q-Dt-C_{\rm low}t^2,
$$

其中使用 $0<a_t\le1$、$D=\kappa\eta b>0$ 及 (2.5)。所有常数独立于解码器，故取全部解码器的下确界保持不等式。这是逐点统一证书，允许解码器随 $t$ 不连续地改变，不要求它接近零点最优面、可微、酉或极端。根式证书是明确下界，不是正参数最优值的精确公式。$\square$

## 5. 继承的共同变化解码器及闭区间上证书

**定义 5.1（同一个变化参数与完整矩阵）。** 在 $0\le t\le r_0$ 上，取 S 定义 4.1、引理 4.2 及定义 4.3 的

$$
s_t=T-Mt,\qquad b_t=\sqrt{1-s_t^2},\qquad
\mathsf A_t=\sqrt{\frac{1+b_t}{2}},\qquad
\mathsf B_t=\frac{s_t}{\sqrt{2(1+b_t)}}.
\tag{5.1}
$$

由区间定义，$T/2\le s_t\le T<1/2$，$b_t\ge b>1/2$。令

$$
U_+(t)=\begin{pmatrix}\mathsf A_t&-\mathsf B_t\\
\mathsf B_t&\mathsf A_t\end{pmatrix},\qquad
U_-(t)=\begin{pmatrix}\mathsf A_t&\mathsf B_t\\
-\mathsf B_t&\mathsf A_t\end{pmatrix}.
\tag{5.2}
$$

按记录优先的四维基，完整矩形 Kraus 为

$$
L_+(t)=\begin{pmatrix}\mathsf A_t&-\mathsf B_t&0&0\\
\mathsf B_t&\mathsf A_t&0&0\end{pmatrix},\qquad
L_-(t)=\begin{pmatrix}0&0&\mathsf A_t&\mathsf B_t\\
0&0&-\mathsf B_t&\mathsf A_t\end{pmatrix},
$$

$$
\mathcal R_t(\mathsf W)=\sum_{\xi=+,-}L_\xi(t)\mathsf W L_\xi(t)^\dagger
=\sum_{\xi=+,-}U_\xi(t)\mathsf W_{\xi\xi}U_\xi(t)^\dagger.
\tag{5.3}
$$

**引理 5.2（完整合法性与实际重建）。** $\mathcal R_t:M_4\to M_2$ 为 CPTP，且

$$
\mathcal R_t\mathcal N_t:\quad
(x,y,z)\longmapsto(k_ts_t+2a_ttb_tx,\,2a_tty,\,b_tz).
\tag{5.4}
$$

证明。$\mathsf B_t^2=(1-b_t)/2$，所以
$\mathsf A_t^2+\mathsf B_t^2=1$、$2\mathsf A_t\mathsf B_t=s_t$。矩阵 (5.2) 的列正交归一，故二者为全量子比特酉矩阵，并且 $U_-=U_+^\dagger$。由 (5.3) 的 Kraus 形式，映射完全正；其伴随乘积和为

$$
L_+^\dagger L_++L_-^\dagger L_-
=|+\rangle\langle+|\otimes I_2+|-\rangle\langle-|\otimes I_2=I_4,
\tag{5.5}
$$

证明整个代数上的保迹性，而不只在占用列上规定操作。逐 Pauli 共轭为

$$
\begin{array}{c|ccc}
 &X&Y&Z\\ \hline
U_+(\,\cdot\,)U_+^\dagger&b_tX-s_tZ&Y&s_tX+b_tZ\\
U_-(\,\cdot\,)U_-^\dagger&b_tX+s_tZ&Y&-s_tX+b_tZ
\end{array}
\tag{5.6}
$$

代入 (3.8) 的实际未归一化分支，$X$ 坐标中 $s_t$ 的贡献为
$s_t[(k_t+z)-(z-k_t)]/2=k_ts_t$，另有 $2a_ttb_tx$；$Z$ 坐标中两个相干项相消，剩余 $b_tz$；$Y$ 坐标相加为 $2a_tty$。这证明 (5.4)。对每个 $t$，它是三个输入共享的一个映射，没有输入标签、成功后选择或附加信息。$\square$

**引理 5.3（三个实际误差的同斜率平衡）。** 令

$$
(\xi_0,\zeta_0)=(u,0),\qquad
(\xi_+,\zeta_+)=(v,w),\qquad
(\xi_-,\zeta_-)=(v,-w),
$$

$$
f_i(t)=\bigl(k_ts_t+2a_ttb_t\xi_i-\xi_i,\ (b_t-1)\zeta_i\bigr),
\qquad g_i(t)=\frac{\|f_i(t)\|_2}{2}.
\tag{5.7}
$$

则 $\varepsilon(\mathcal R_t,\mathcal N_t)=\max_i g_i(t)$，且

$$
g_i(0)=Q,\qquad g_i'(0)=-D\quad(i=0,+,-).
\tag{5.8}
$$

证明。(5.4) 与半迹规范给出误差表达式。零点向量为

$$
f_0(0)=(-e,0),\qquad
f_\pm(0)=(d,\pm(b-1)w),
\qquad \|f_i(0)\|_2=e>0.
\tag{5.9}
$$

有 $s'_0=-M,k'_0=0,a_0=1,b'_0=MT/b$，故

$$
f_i'(0)=\left(-M+2b\xi_i,\frac{MT}{b}\zeta_i\right),\qquad
 g_i'(0)=\frac{f_i(0)\cdot f_i'(0)}{2e}.
\tag{5.10}
$$

正数 $e$ 保证这里范数可微。由定义，

$$
bu-\frac M2
=\frac{b[u(e+A)-(eu+vd)]}{\ell}
=\frac{b(hd+u\beta T)}\ell=D.
\tag{5.11}
$$

因此锚导数为 $M/2-bu=-D$。任一侧态则满足

$$
\begin{aligned}
2e g_\pm'(0)
&=d(-M+2bv)+(b-1)w^2\frac{MT}{b}\\
&=-M(d+\beta T)+2bvd=-MA+2bvd\\
&=e(M-2bu)=-2eD,
\end{aligned}
\tag{5.12}
$$

最后一行使用 $M(e+A)=2b(eu+vd)$。这正是 S 引理 5.2 的达到系数。三个等式使用同一 $s_t$ 与同一对完整酉，未拼接分别可达而不相容的解码器。$\square$

**引理 5.4（实际闭区间的向量余项）。** 对每个 $i$ 及整个 $[0,r_0]$，有

$$
\|f_i'(0)\|_2\le V,\qquad
\|f_i''(t)\|_2\le H,
$$

$$
f_i(t)=f_i(0)+tf_i'(0)+R_i(t),\qquad
R_i(t)=\int_0^t(t-\tau)f_i''(\tau)\,d\tau,\qquad
\|R_i(t)\|_2\le\frac H2t^2.
\tag{5.13}
$$

证明。区间上 $t\le1/4$、$a_t>1/2$、$T/2\le s_t\le T<1/2$、$b_t>1/2$，并且 $a_t,b_t\le1$。对光滑向量坐标求导，得

$$
b_t'=\frac{Ms_t}{b_t},\quad b_t''=-\frac{M^2}{b_t^3},\quad
 a_t'=-\frac t{a_t},\quad a_t''=-\frac1{a_t^3}.
$$

因此 $|b_t'|\le M,|b_t''|\le8M^2,|a_t'|\le1,|a_t''|\le8$。置 $j(t)=ta_t$，则

$$
|j|\le1/4,\qquad |j'|\le2,\qquad |j''|\le4,
\qquad |(k_ts_t)''|=|-4s_t+8Mt|\le2+2M.
$$

所有输入有 $2|\xi_i|\le1,|\zeta_i|\le1/2$。乘积法则给出

$$
\begin{aligned}
|f_{i,x}''(t)|
&\le(2+2M)+2|\xi_i|\bigl(|j''|b_t+2|j'||b_t'|+|j||b_t''|\bigr)\\
&\le6+6M+2M^2,\\
|f_{i,z}''(t)|&\le4M^2.
\end{aligned}
\tag{5.14}
$$

欧氏范数不超过坐标绝对值之和，得到 $H$。零点的 (5.10) 给出
$|f_{i,x}'(0)|\le M+1$、$|f_{i,z}'(0)|\le M/2$，因为 $T/b<1$；故范数至多 $1+3M/2\le V$。各坐标在整个闭区间二次连续可微，逐分量积分两次给出 (5.13) 的精确表示，再对积分取范数得 $Ht^2/2$。这是 S 引理 6.1 的区间估计，所用分母下界在区间上有效。$\square$

**命题 5.5（匹配的统一上证书）。** 对整个 $0\le t\le r_0$，

$$
Q-Dt-Lt^2\le g_i(t)\le Q-Dt+Lt^2
\quad(i=0,+,-),
$$

$$
Q-Dt-Lt^2\le\varepsilon(\mathcal R_t,\mathcal N_t)
\le Q-Dt+Lt^2.
\tag{5.15}
$$

证明。写 $f=f_i(0),v_i=f_i'(0)$，引理 5.3 给出
$\|f\|_2=e$、$f\cdot v_i=-2eD$。对任意 $q\ge0$，切线不等式
$\sqrt q\le e+(q-e^2)/(2e)$ 给出

$$
\|f+tv_i\|_2
\le e-2Dt+\frac{\|v_i\|_2^2}{2e}t^2.
$$

加上 (5.13) 的余项，再除以二，得到
$g_i(t)\le Q-Dt+[V^2/(4e)+H/4]t^2=Q-Dt+Lt^2$。另以固定单位向量 $f/e$ 支撑范数，

$$
\|f_i(t)\|_2\ge(f/e)\cdot f_i(t)
\ge e-2Dt-Ht^2/2.
$$

除以二并用 $L\ge H/4$，得到下界。证明没有对正 $t$ 处可能为零的残差范数求倒数，故不需要另加非零区间。三个误差同时处于同一上下界，最大值也如此。这接合的是 S 引理 6.2 已有的达到余项，不把它重新计为任意解码器最优性。$\square$

## 6. 精确最优一阶系数与同路径根缺陷极限

**定理 6.1（全部解码器竞争的精确一阶结算）。** 在定义 1.1–1.4 的固定模型中，对每个 $0\le t\le r_0$，有

$$
Q-Dt-C_{\rm low}t^2
\le\varepsilon_\star(\mathcal N_t)
\le\varepsilon(\mathcal R_t,\mathcal N_t)
\le Q-Dt+Lt^2.
\tag{6.1}
$$

特别地，

$$
\begin{aligned}
\varepsilon_\star(\mathcal N_0)&=Q,\\
\lim_{t\downarrow0}\frac{Q-\varepsilon_\star(\mathcal N_t)}t&=D>0,\\
\left.\frac{d^+}{dt}\varepsilon_\star(\mathcal N_t)\right|_{t=0}&=-D,\\
\lim_{t\downarrow0}\frac{Q-\varepsilon_\star(\mathcal N_t)}{\sqrt{G_t}}
&=\frac D{\sqrt\gamma},\\
0\le\varepsilon(\mathcal R_t,\mathcal N_t)-\varepsilon_\star(\mathcal N_t)
&\le(L+C_{\rm low})t^2.
\end{aligned}
\tag{6.2}
$$

证明。定理 4.4 给出第一界；(5.5) 的合法性使下确界方向为
$\varepsilon_\star\le\varepsilon(\mathcal R_t,\mathcal N_t)$；命题 5.5 给出最后一界。零点二者为 $Q$，于是最优值恰为 $Q$。对正 $t$，重排 (6.1) 得

$$
D-Lt\le\frac{Q-\varepsilon_\star(\mathcal N_t)}t
\le D+C_{\rm low}t.
\tag{6.3}
$$

两端趋于 $D$，证明极限存在及右导数。它不是从某个达到方案的导数推定最优导数，而是从任意解码器的统一下界和共同可行上界夹出。

由 (1.7)–(1.8)，正路径有 $G_t>0$，并且
$\sqrt{G_t}/t=\sqrt{G_t/t^2}\to\sqrt\gamma>0$。将 (6.3) 的极限除以这个极限，得到根缺陷比值。最后，可行性给出非负遗憾；以达到上界减去最优下界，得到二次遗憾界。整个论证未选取光滑最优解，也未交换下确界与导数。$\square$

**推论 6.2（渐近常数的严格上下侧）。** 记 $K_{\rm path}=D/\sqrt\gamma$。对任意固定实数 $K<K_{\rm path}$，所有充分小的正 $t$ 都满足

$$
\varepsilon_\star(\mathcal N_t)<Q-K\sqrt{G_t}.
\tag{6.4}
$$

对任意 $K>K_{\rm path}$，所有充分小的正 $t$ 都满足

$$
\varepsilon_\star(\mathcal N_t)\ge Q-K\sqrt{G_t}.
\tag{6.5}
$$

证明。按定理 6.1，实际比值 $(Q-\varepsilon_\star)/\sqrt{G_t}$ 趋于 $K_{\rm path}$；分别与严格较小、严格较大的 $K$ 比较，再乘以正的 $\sqrt{G_t}$，即得结论。等号选择 $K=K_{\rm path}$ 是否在整个去心邻域满足 (6.5) 保持 **OPEN**；一阶极限不控制下一阶的符号。$\square$

$K_{\rm path}$ 是这一实际路径上的精确首项系数。R 定理 9.2 的 $Q-\sqrt{12G}$ 是任意实际有限仪器上的既有粗下界；S 定理 7.2 已结算较大指数的统一失败。这些结果的量词不同，不能把本路径系数称为所有仪器或所有忠实族的最佳通用常数。

**命题 6.3（固定参数的最小值存在性）。** 每个固定 $0\le t<1/\sqrt2$ 的下确界均达到，也有对称最优代表。

证明。采用输入优先 Choi 约定，映射 $M_4\to M_2$ 的 Choi 矩阵满足 $J_{\mathcal R}\succeq0$、$\operatorname{Tr}_{\rm out}J_{\mathcal R}=I_4$，故总迹为 $4$。这个有限维 Hermitian 空间中的集合闭且有界，因此紧。对固定 $t$，三个重建态依 Choi 矩阵线性变化，有限最大半迹误差连续，所以取得最小值。对称平均不增误差，故给出对称最优代表。紧性只给存在性，不给唯一性、光滑选择或最优值导数；导数已由 (6.1) 单独证明。$\square$

## 7. 零点最优面的占用唯一性与扩张非唯一性

**定理 7.1（原始未平均解码器的占用态被唯一强制）。** 对任意原始完整输出 CPTP 映射，令
$\Phi_\xi(\Theta)=\mathcal R(|\xi\rangle\langle\xi|\otimes\Theta)$。则

$$
\varepsilon(\mathcal R,\mathcal N_0)=Q
\quad\Longleftrightarrow\quad
\Phi_+(|0\rangle\langle0|)=\omega_+,\qquad
\Phi_-(|1\rangle\langle1|)=\omega_-.
\tag{7.1}
$$

证明。设原映射零点最优。记其两个实际占用输出为 $A_+,A_-$。对称平均的正分支占用态是

$$
\overline A_+=\frac14\left(A_++XA_-X+A_+^{\mathsf T}+XA_-^{\mathsf T}X\right).
\tag{7.2}
$$

其误差 $\overline\varepsilon\le Q$。对平均代表，$t=0$ 时 $a=0,\tau=x_0,c=z_0$。引理 4.1 给出

$$
2\overline\varepsilon\ge e+\kappa[1-(Tx_0+bz_0)].
$$

Bloch 球与 $T^2+b^2=1$ 给出 $Tx_0+bz_0\le1$。结合 $2\overline\varepsilon\le e$ 及 $\kappa>0$，必须等号成立。单位向量 $(T,0,b)$ 与一个长度不超过一的 Bloch 向量内积为一，强制后者等于 $(T,0,b)$。因此 $\overline A_+=\omega_+$ 为秩一态。

若正迹一矩阵的有限正权平均为秩一投影 $P$，每个矩阵在 $P$ 正交补上的期望都为零，因为其非负加权和为零。正性进一步消去其交叉项，迹一再迫使该矩阵就是 $P$。将此事实用于 (7.2)，得到 $A_+=\omega_+$、$XA_-X=\omega_+$，即 $A_-=\omega_-$。这一步把平均代表的纯态结论严格转回原始任意复映射。

反向，若两个占用态满足 (7.1)，则实际零点重建为

$$
\mathcal R\mathcal N_0(\rho(x,y,z))
=\frac{1+z}{2}\omega_++\frac{1-z}{2}\omega_-,
\qquad (x,y,z)\longmapsto(T,0,bz).
\tag{7.3}
$$

由根方程三个半迹误差都为 $e/2=Q$。未使用的分支输入和记录非对角行为不改变此式，只要整个映射本身合法即可。此定理针对固定坐标仪器 $\mathcal N_0$，不分类所有全局经典最优测量。$\square$

**命题 7.2（所有复、混合分支扩张的 Choi 描述）。** 写

$$
\psi=\begin{pmatrix}\mathsf A_0\\\mathsf B_0\end{pmatrix},\qquad
\psi_\perp=\begin{pmatrix}-\mathsf B_0\\\mathsf A_0\end{pmatrix},\qquad
P=|\psi\rangle\langle\psi|=\omega_+,\quad
P_\perp=|\psi_\perp\rangle\langle\psi_\perp|.
\tag{7.4}
$$

采用输入优先约定
$J_\Phi=\sum_{i,j=0}^1|i\rangle\langle j|\otimes\Phi(|i\rangle\langle j|)$。满足 $\Phi(|0\rangle\langle0|)=P$ 的分支恰由下列 Choi 块给出：

$$
J_\Phi=\begin{pmatrix}P&C\\C^\dagger&\mathsf B\end{pmatrix},\qquad
C=PC,\quad\operatorname{Tr}C=0,\quad
\operatorname{Tr}\mathsf B=1,\quad \mathsf B\succeq C^\dagger C.
\tag{7.5}
$$

等价地，存在任意复数 $\zeta$、$|\zeta|\le1$，使

$$
C=\zeta|\psi\rangle\langle\psi_\perp|,
\qquad
\mathsf B=
\begin{cases}
|\zeta|^2P_\perp+(1-|\zeta|^2)\theta,&|\zeta|<1,\\
P_\perp,&|\zeta|=1,
\end{cases}
\tag{7.6}
$$

其中 $\theta$ 是任意二维密度矩阵。

证明。块正性使第一块中任意 $\ker P$ 向量被整个 Choi 矩阵湮灭，故 $(I-P)C=0$，即 $C=PC$。这个约定下不能误写为 $C=CP$。保迹约束是每个输入块的输出迹给出 $I_2$，故为 $\operatorname{Tr}P=1,\operatorname{Tr}C=0,\operatorname{Tr}\mathsf B=1$。由 $C=PC$ 写 $C=|\psi\rangle\langle\chi|$，零迹使 $\langle\chi|\psi\rangle=0$，所以 $C$ 具有 (7.6) 的形式。

在 $P$ 的一维支撑上作 Schur 补，块正性等价于 $\mathsf B-C^\dagger C\succeq0$。具体地，对任意输出向量 $\chi$，取块向量 $(-C\chi,\chi)$，利用 $PC=C$，其 Choi 二次型为 $\chi^\dagger(\mathsf B-C^\dagger C)\chi$，所以此条件必要。其充分性也可直接从因子分解看出：

$$
\begin{pmatrix}P&C\\C^\dagger&C^\dagger C\end{pmatrix}
=\begin{pmatrix}P\\C^\dagger\end{pmatrix}\begin{pmatrix}P&C\end{pmatrix}\succeq0,
$$

再加上 $\operatorname{diag}(0,\mathsf B-C^\dagger C)$。而 $C^\dagger C=|\zeta|^2P_\perp$，取迹得 $|\zeta|\le1$。若严格小于一，余项除以其迹 $1-|\zeta|^2$ 恰为任意密度矩阵 $\theta$；若等于一，正余项迹零，必须为零。反向，每个 (7.6) 都满足块正性与全部 TP 迹约束，因而给出 CPTP 分支。这是必要且充分的描述，包含任意复相位和混合的未占用输出。

负分支可经 $\widehat\Phi_-=\operatorname{Ad}_X\circ\Phi_-\circ\operatorname{Ad}_X$ 转成同一问题，因为 $\widehat\Phi_-(|0\rangle\langle0|)=P$。因此两个分支可各自选择以上扩张，再由引理 3.1 取得合法的记录去相干全代数解码器。原映射在记录非对角输入上的其他扩张仍须独立满足 CP、TP；本参数化没有把它们宣称为任意可指定。$\square$

**命题 7.3（零面支撑最大化的准确含义）。** 对正分支，(7.6) 给出

$$
p=\frac12\operatorname{Tr}(X\Phi(X))
=\operatorname{Re}\operatorname{Tr}(XC)=b\operatorname{Re}\zeta,
\qquad -b\le p\le b.
\tag{7.7}
$$

对固定的对称零点最优代表，$\mathcal F$ 的零点导数为 $2\eta p$，最大值为 $2\eta b$，恰由 $\zeta=1,\mathsf B=P_\perp$ 的酉分支达到。

证明。$\Phi(X)=C+C^\dagger$，且
$\langle\psi_\perp|X|\psi\rangle=\mathsf A_0^2-\mathsf B_0^2=b$，所以 (7.7) 成立。迹伴随中 $J_{10}=\operatorname{Tr}(XC)$、$J_{01}$ 为其共轭，与 (4.3) 的实部公式一致。每个 $p\in[-b,b]$ 可取实 $\zeta=p/b$ 及任意允许的 $\theta$ 达到；转置不变代表可选实 $\zeta$ 和实 $\mathsf B$，一般分支则允许复数。

对固定代表，(3.9) 与定理 7.1 给出
$\tau=T-2t^2q,c=b-2t^2s,a=2a_ttp$，故 $\mathcal F'(0)=2\eta p$。由于 $\eta,b>0$，最大化强制 $\operatorname{Re}\zeta=1$，结合 $|\zeta|\le1$ 即 $\zeta=1$。此时 $\mathsf B=P_\perp$，Choi 为秩一，信道为两列 $\psi,\psi_\perp$ 的酉 $U_+(0)$ 共轭；负分支取其 $X$ 相关者。这是约化零面上支撑最大化分支的结论，不是整个零面唯一，也不是实际固定映射最大误差导数的最小化。$\square$

## 8. 原始任意复固定解码器的一阶障碍

**定理 8.1（固定映射不能产生正一阶改善）。** 对每个不随 $t$ 改变的原始完整输出共同 CPTP 解码器 $\mathcal R$，

$$
\limsup_{t\downarrow0}\frac{Q-\varepsilon(\mathcal R,\mathcal N_t)}t\le0.
\tag{8.1}
$$

若其零点误差等于 $Q$，则最大误差的右导数存在且非负。特别地，不存在固定映射和 $c>0$ 使
$\varepsilon(\mathcal R,\mathcal N_t)=Q-ct+o(t)$。

证明。固定线性映射与连续的仪器路径复合，误差随 $t$ 连续。定理 6.1 保证零点误差至少为 $Q$。若严格大于 $Q$，则 (8.1) 的比值趋于负无穷。以下只需处理零点最优映射，定理 7.1 使其原始占用输出恰为 $\omega_\pm$，无须平均或实性假设。

令其两个分支为 $\Phi_\pm$，写

$$
S_\Phi=\Phi_+(X)+\Phi_-(X)=s_xX+s_yY+s_zZ.
\tag{8.2}
$$

它是 Hermitian 且迹零，因为各分支保 Hermitian 并保迹，故 $s_x,s_y,s_z$ 都是实数。由 (3.8)，对三个输入 $(\xi_i,0,\zeta_i)$，每个实际未归一化分支在零点的导数均为 $\xi_iX/2$：对角概率只含 $t^2$，而相干项的导数来自 $a_tt$。固定解码后输出矩阵的导数因此为 $\xi_iS_\Phi/2$，其 Bloch 导数为 $\xi_i(s_x,s_y,s_z)$。

原始三维残差在零点为

$$
\widetilde f_0(0)=(-e,0,0),\qquad
\widetilde f_\pm(0)=(d,0,\pm(b-1)w),
$$

其范数都为 $e>0$。各单态半迹误差在零点可微，内积求导得

$$
\widetilde g_0'(0)=-\frac{u s_x}{2},\qquad
\widetilde g_\pm'(0)=
\frac{v[d s_x\pm(b-1)w s_z]}{2e}.
\tag{8.3}
$$

任意复操作引入的 $s_y$ 与零点残差正交，所以不贡献这个一阶范数导数。两个侧导数的最大值至少为均值 $vd s_x/(2e)$。三个函数在零点同取 $Q$，有限个可微函数的右侧最大值满足

$$
\left.\frac{d^+}{dt}\max_i\widetilde g_i(t)\right|_{0}
=\max_i\widetilde g_i'(0),
$$

因为各函数为 $Q+t\widetilde g_i'(0)+o(t)$，有限个余项的最大绝对值仍为 $o(t)$。因此

$$
\left.\frac{d^+}{dt}\varepsilon(\mathcal R,\mathcal N_t)\right|_0
\ge\max\left\{-\frac{u s_x}{2},\frac{vd s_x}{2e}\right\}\ge0.
\tag{8.4}
$$

最后一步对 $s_x\ge0$ 用第二项，对 $s_x\le0$ 用第一项，且 $u,v,d,e$ 全正。这个证明直接适用于原始未平均、任意复和混合非酉映射。除以正 $t$ 并改变符号，即得 (8.1)。$\square$

**推论 8.2（支撑最优、冻结极小极大与变化最优的区别）。** 对固定的对称零点最优代表，三个误差导数为

$$
g_0'(0)=-up,\qquad g_+'(0)=g_-'(0)=\frac{vd}{e}p,
\qquad
\varepsilon'(0+) = \max\{-up,vd p/e\}\ge0.
\tag{8.5}
$$

其冻结导数的最小值为零，而变化竞争的最优值导数为 $-D<0$。

证明。固定代表有 $a'_0=2p,\tau'_0=c'_0=0$，直接代入残差或取 (8.3) 的 $s_x=2p,s_z=0$，得 (8.5)。命题 7.3 的支撑最大化分支为 $p=b$，其侧误差导数为 $vdb/e>0$；所以这个支撑最大化的固定酉并不改善实际最大误差。取 $p=0$ 可得到零导数，例如两个分支分别为 $\Theta\mapsto\operatorname{Tr}(\Theta)\omega_\pm$，由引理 3.1 扩张为固定 CPTP 解码器；它在零点最优，且 (8.5) 的三个导数均为零。

相比之下，§5 的允许变化族以 $s_t=T-Mt$ 改变占用制备方向，同时 $b_t'=Ms_t/b_t$。这个沿纯态圆的切向运动给残差增加一阶项，恰把三个竞争导数一起平衡到 $-D$。因此

$$
\forall\,\mathcal R\text{ 固定},\quad
\limsup_{t\downarrow0}\frac{Q-\varepsilon(\mathcal R,\mathcal N_t)}t\le0,
\qquad
\lim_{t\downarrow0}\frac{Q-\varepsilon(\mathcal R_t,\mathcal N_t)}t=D>0
\tag{8.6}
$$

是相容的不同量词。只优化被冻结的零点最优映射的导数，会漏掉允许的制备切向运动。本文没有使用这种导数与下确界互换；定理 6.1 用独立的统一夹逼处理全部变化选择。$\square$

## 9. 结论范围、开放问题与方法解释

**边界 9.1（已结算的量词）。** 精确系数只针对 (1.1) 的固定三个忠实态、(1.3) 的同一实际两记录路径和 (1.4) 的有限族半迹极小极大目标。下界遍及整个复代数上的全部共同 CPTP 映射，上界只用其中一个合法变化族。全代数 CPTP 定义不把误差目标升级为任意输入、任意未触参考或 diamond 恢复。所有量都来自同一实际实现；没有隐藏输入标签、未记录环境、额外量子摘要、独立逐态操作、替代测量、成功后选择或重复 Born 权重。

**边界 9.2（正参数最优性保持 OPEN）。** 固定正 $t$ 的精确最优值、所有最优映射的分类、分支酉是否足够、光滑最优选择、二阶最优系数均保持 **OPEN**。紧性只保证每个参数处存在最优映射，二次遗憾只保证显示解码器与最优值相差至多二阶。零点占用态唯一，但未占用输入的复、混合 CPTP 扩张非唯一；记录相干扩张仍受完整 CP、TP 约束。这里不分类所有经典全局最优测量，也不由零点支撑最大化推断正参数最优。

**边界 9.3（首项常数与通用性）。** $D/\sqrt\gamma$ 是同路径首项系数，等号常数在整个去心邻域的下界是否成立保持 **OPEN**。其他实际路径、其他族、变化维数或奇异输入上的最优值与最佳常数，尤其跨全部仪器或全部忠实族的最佳通用常数，都未由此决定。S 已有的指数尖锐性不是本系数证明的新成果。实际正 $G_t$ 与族最优化 $\Delta=0$ 必须持续区分。

**边界 9.4（普适协议与资源桥梁保持 OPEN）。** R §11、C §5 的另一个任务要求在原有固定公平仪器、时间顺序、保留量子系统、全输入及参考误差、完整视图计数和独立种子权限下，对每个实际协议构造共同 POVM，并证明缺陷与协议误差及资源的定量联系。这里侧态与锚的记录概率不同，不能将 (1.3) 当作输入无关的公平历史路径。本文未给出这个普适映射或资源函数，也未给出近似寄存器或记忆定律、平均近似到逐种子同误差的结论、近似忠实代数迁移。分别最优的成对测量、独立边缘、删除量子输出或更换实际仪器都不补足该桥梁；桥梁未建立也不等于所有未来桥梁不可能。

**解释 9.5（学习方法中的量词提醒）。** 固定表示或读出与允许整族共同重调的方案，需要分别写清“同一个固定映射”和“每个参数可选择一个共同映射”的量词。本模型证明了这两类选择在一阶改善上的区别；迁移到机器学习仍须证明具体任务、状态、观察、保留系统及允许操作的对应。这里没有这样的学习任务或操作、表示桥梁，没有经验性能或普遍学习定理，也没有物理取得、制备、精度、通信、控制合成、运行时间或总成本证书。

## 10. 来源对应与标准方法归属

C 命题 1.3 提供固定三态与共同等号测量；C 定理 2.1 提供全部有限 POVM/制备上的 $Q=e/2$、唯一根 $T$ 和达到态 $\omega_\pm$。其式 (2.7)、(2.9)、(2.11) 分别对应本文 (2.2)、(2.4)、(4.2)。变量 $t_\star,c_\star,d_\star$ 对应 $T,b,d$，其仿射平移 $t$ 对应本文 $\tau$。本文仅复用支撑恒等式中不依赖经典可行域的部分。

S 定义 1.1、1.3、1.4 固定模型与量词，S §3 提供实际路径、概率、正缺陷公式和 $\gamma$，S §§4–6 提供 $M,D,s_t$、完整酉解码器及 $r_0,V,H,L$ 区间余项。本文 §5 保留这部分达到构造的可检查证明，使其能与任意解码器的下证书在同一区间相接。S 定理 7.1、边界 8.2 将达到系数与尚未结算的最优系数区分；本文定理 4.4、6.1 补足后者，未重命名 S 定理 7.2 的指数反证。

R 定义 1.3、定理 9.2 提供完整联合输出、任意共同 CPTP 竞争与 $Q-\sqrt{12G}$ 的既有下界；R 命题 9.3 给出固定输入的根保真值。该粗界是背景，不是本文精确下证书的必要前提。R 的锚下界 $1/4$ 不是共同忠实下界；其谱间隙 $\gamma$ 和 Frobenius 块相干量 $h$ 也不与本文同名量混用。R §11、C §5 的协议和资源义务仍按其原权限保留。

新增综合步骤是：对任意 CPTP 分支的正含幺伴随使用 Hermitian 收缩约束，将相干系数与占用态的 Bloch 坐标绑定，再代入既有支撑泛函，取得原始全部解码器的统一根式与二次下余项。结合继承上证书，才确定精确最优一阶系数。零面占用态唯一性、复混合扩张和原始固定映射障碍分别在 §§7–8 证明。Bloch 表示、Kraus 扩张、共轭 Kraus 对称、凸平均、正含幺伴随、Hermitian 谱序、Cauchy–Schwarz、Choi 正性、一维支撑 Schur 补、范数支撑、积分余项和有限维紧性均为标准工具。

根保真接口的原始文献归属，仅按 S、R、C 的转述理解为 Nuradha、Mishra、Leditzky、Wilde 的 *Multivariate Fidelities* 以及 Fuchs、Caves 的 *Mathematical Techniques for Quantum Communication Theory*；精确恢复背景引用 Gregoratti、Werner 的 *Quantum Lost and Found* 与 Knill、Laflamme 的 *A Theory of Quantum Error-Correcting Codes*。本文没有核验这些外部原文、版本、链接或文献完备性，不附带外部新颖性或世界优先权结论。全文只承担已列接口和量词下的未经执行条件符号论证，不构成 kernel、经验、物理、资源或更大研究目标完成证书。

## 追加锚（本行以下为增补区）
