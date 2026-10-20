# AURIC FIB 全输入带旗标仪器的精确支撑面、严格距离间隙与倾斜投影上界

本文研究同一五维寄存器上、保留二值经典旗标及量子输出的全复输入仪器模拟，采用任意未读取有限参考和不折半菱形范数。归一化参考见证与首次完整 PVM 的共同右支撑给出 $L=48(\sqrt2-1)/(41+24\sqrt2)>1/4$，相应支撑泛函的全局最大值恰为 $65/(41+24\sqrt2)$。本文分类一个包含全部实际协议的紧外部松弛中的整个支撑极大面，并以同一通道的相干测试证明 $d_*\ge L+\delta_{\rm joint}>L$，其中正数 $\delta_{\rm joint}$ 由明确的有限维变分式定义，但未求值。一个实际倾斜 PVM 与独立群混合又给出 $d_*<1-1/\sqrt2-1/1000000$。支撑最大值及其面上最小误差均有有限深度实现；原全局精确 $d_*$ 及有限或几乎必然终止类中的最优距离取到仍为 OPEN。闭包紧性只给出闭包通道的抽象极小者。

## 1. 数学对象、操作菜单与原问题

**约定 1.1（范围与来源）。** 本文讨论有限维复 Hilbert 空间上的条件数学模型。内积对第一变量共轭线性，$\operatorname{Ad}_L(X)=LXL^\dagger$，$\|X\|_1=\operatorname{Tr}\sqrt{X^\dagger X}$。证明是普通符号数学证明，未附形式核验器证书。文末固定身份的源甲提供实际矩阵及已有接口；其引用的文献陈述按该固定文本使用，不作外部认证或优先权判断。源甲 §§17–22 提供原始全输入问题、旧模拟器及其精确误差、停止与闭包接口。本文给出归一化见证、共同右支撑的完整分支界、覆盖所有首次 PVM 秩分拆的全局精确支撑值，以及具体倾斜 PVM 模拟器的完整误差分析；不声称逐个秩分拆的最优值均已求出。另一个所供符号论证（下称源乙）提供完整支撑极大面与联合相干分离路线；本文将其纳入同一模型，给出所需全部证明。

**定义 1.2（实际五维仪器）。** 取 $H=\mathbb C^5$，固定正交基 $(e_0,e_1,e_2,e_3,e_4)$，并令

$$
\begin{gathered}
q=1/\sqrt2,\quad s=e_2,\quad S=|s\rangle\langle s|,\quad
P=|e_0\rangle\langle e_0|+|e_4\rangle\langle e_4|,\quad
Q=|e_1\rangle\langle e_1|+|e_3\rangle\langle e_3|,\\
P_0=P,\quad P_1=Q,\quad P+Q+S=I_5,\\
u=q(e_0+e_3),\quad v=q(e_1+e_4),\quad z=e_2,\\
K_0=|u\rangle\langle e_0|+q|v\rangle\langle s|+|z\rangle\langle e_4|,\qquad
K_1=|u\rangle\langle e_1|+q|v\rangle\langle s|+|z\rangle\langle e_3|.
\end{gathered}
$$

这些是源甲定义 1.3、2.1 与定理 2.2 的实际矩阵。为明确其测量含义，环境 $E=\mathbb C^2$ 以正交基 $(f_0,f_1)$ 的 $f_0$ 为准备态，准备子空间上的相互作用为

$$
\begin{aligned}
\mathcal V e_0&=u\otimes f_0,& \mathcal V e_1&=u\otimes f_1,&
\mathcal V e_2&=v\otimes(f_0+f_1)/\sqrt2,\\
\mathcal V e_3&=z\otimes f_1,& \mathcal V e_4&=z\otimes f_0.
\end{aligned}
$$

五个像正交归一，所以 $\mathcal V$ 是等距映射；补全定义域与像的正交基即可得到 $H\otimes E$ 上的幺正扩张。测量环境正交基

$$
g_0=\cos\theta f_0-i\sin\theta f_1,\qquad
g_1=-i\sin\theta f_0+\cos\theta f_1
$$

给出实际分支

$$
A_0(\theta)=\cos\theta K_0+i\sin\theta K_1,\qquad
A_1(\theta)=i\sin\theta K_0+\cos\theta K_1.
$$

目标保留测量所得的经典旗标及量子输出：

$$
\mathcal J_\theta(X)=\bigoplus_{j=0}^1 A_j(\theta)XA_j(\theta)^\dagger.
\tag{1.1}
$$

直和表示对角二值经典旗标，不授予模拟器新的量子存储器。输入是整个 $M_5$，包括与任意不被读取的有限参考 $Z$ 纠缠的输入；目标不是仅在 $R=\operatorname{span}\{u,v,z\}$ 上的编码仪器。两分支的迹之和为输入迹，因为 $K_0^\dagger K_0=P+S/2$、$K_1^\dagger K_1=Q+S/2$，而分支重组矩阵是幺正的。

**定义 1.3（允许的模拟器及范数）。** 模拟器只在原寄存器 $H$ 上使用任意幺正操作、完整 Lüders PVM $\{R_a\}$ 的操作 $X\mapsto R_aXR_a$、与输入独立的可测经典随机性、按既往结果选择操作的经典反馈，以及把最终经典记录粗化为旗标 $j$。每次运行保留所有结果及全部概率质量，量子输出是剩余的同一寄存器。禁止增加量子寄存器或能级、重置、非投影 Lüders 操作、任意 CPTP 后处理原语、参考读取及成功后选择。

$\mathfrak S_{\rm fin}$ 表示存在统一有限操作深度上界的协议；$\mathfrak S_{\rm as}$ 表示在每个输入上几乎必然有限终止的协议；$\mathfrak S_{\rm cl}=\overline{\mathfrak S_{\rm fin}}^{\diamond}$。独立经典随机选择可预先采样为标准 Borel 随机带，包括每个可能有限反馈历史处的选择。固定整条带后得到确定的有限分叉量子结果树。闭包只包含归一化通道的极限，不把不终止的无限乘积当作原语。

采用源甲定义 17.2 的不折半范数：

$$
\|\Lambda\|_\diamond=
\sup_{k\ge1}\sup_{X\ne0}
\frac{\|(\Lambda\otimes\operatorname{id}_{\mathbb C^k})(X)\|_1}{\|X\|_1}.
\tag{1.2}
$$

内层包括任意复算符。原问题是确定

$$
d_*(\theta)=\inf_{\mathcal T\in\mathfrak S_{\rm fin}}
\|\mathcal J_\theta-\mathcal T\|_\diamond.
\tag{1.3}
$$

**定理 1.4（全协议下界与实际严格上界）。** 对每个实数 $\theta$，三个模拟器类给出相同、与角度无关的下确界 $d_*$。令

$$
N=3+4\sqrt2,\qquad N^2=41+24\sqrt2,\qquad
L=\frac{48(\sqrt2-1)}{41+24\sqrt2}.
$$

再令 $\beta_{\rm joint}=L+\delta_{\rm joint}$ 为定理 3.10 的紧变分常数。则 $\delta_{\rm joint}>0$，而且

$$
\boxed{\frac14<L<L+\delta_{\rm joint}\le d_*
<1-\frac1{\sqrt2}-\frac1{1000000}.}
\tag{1.4}
$$

下界对每一个实际有限深度、几乎必然终止协议及其菱形闭包成员成立。定理 3.3 的同一归一化输入与输出投影给出精确支撑最大值 $65/N^2$；定理 3.7 将紧外部松弛中的整个极大面分类为两个实际单 PVM 仪器之间的线段。命题 3.8 说明，只合并支撑测试与输入 $S$ 的完整输出测试仍只能给出 $L$；引理 3.9 的相干测试在整个面上至少为 $U_0=1-1/\sqrt2>L$，由紧性得到上述正的统一间隙。$\delta_{\rm joint}$ 尚无求出的数值或显式正下界。

严格上界来自定义 4.1、4.3 及命题 4.2 的实际有限深度成员，每次运行恰有一次非平凡完整 PVM；其精确误差是定理 6.2 的一变量最大值。等式 $d_*=L$ 已被排除。原问题 (1.3) 的精确值、匹配的全局最优性证书，以及有限深度或几乎必然终止类中的距离取到仍为 OPEN。支撑泛函的取到不结算这些距离问题。证明由 §§2–8 给出。

## 2. 角度、极分解及停止边界

**引理 2.1（全输入等距对应）。** 定义

$$
\begin{gathered}
F=|e_0\rangle\langle e_1|+|e_1\rangle\langle e_0|
 +|e_3\rangle\langle e_4|+|e_4\rangle\langle e_3|+S,\qquad
D_\theta=\cos\theta I_5+i\sin\theta F,\\
u_-=q(e_0-e_3),\qquad v_-=q(e_1-e_4),\\
T_0=[u\ \ u_-\ \ v\ \ v_-\ \ z],\qquad
T_1=[u_-\ \ u\ \ v\ \ z\ \ v_-],\qquad H_j=P_j+qS.
\end{gathered}
$$

则 $D_\theta,T_0,T_1$ 均为全五维幺正矩阵，并且

$$
A_j(\theta)=K_jD_\theta,\quad K_j=T_jH_j,\qquad
\widehat{\mathcal J}(X)=\bigoplus_j H_jXH_j.
\tag{2.1}
$$

对每个模拟器类，合法初始幺正预合成和按旗标的末端幺正后合成，给出 $\mathcal J_\theta$、$\mathcal J_0$、$\widehat{\mathcal J}$ 的等距模拟问题。

证明。$F$ 交换 $e_0,e_1$ 及 $e_3,e_4$，固定 $s$，故 $F^\dagger=F$、$F^2=I$，并由定义 1.2 的 dyad 得到 $K_0F=K_1$、$K_1F=K_0$。于是 $D_\theta^\dagger D_\theta=I$ 且 $K_jD_\theta=A_j(\theta)$，从而

$$
\mathcal J_\theta=\mathcal J_0\circ\operatorname{Ad}_{D_\theta}.
$$

两个 $T_j$ 的列分别是正交归一的完整五维基。逐列作用给出 $T_j(P_j+qS)=K_j$。输出上的分块幺正 $\bigoplus_j T_j$ 把 $\widehat{\mathcal J}$ 变成 $\mathcal J_0$；在操作菜单中它只是按已知经典旗标施加 $T_j$。这些操作及其逆都合法，保持终止性质。幺正左右乘保持所有复算符的迹范数，也保持与任意参考张量后的范数，故保持菱形范数。连续性把同一双射延伸到闭包。没有角度例外。$\square$

**引理 2.2（几乎必然终止的有限逼近）。** 有

$$
\mathfrak S_{\rm fin}\subseteq\mathfrak S_{\rm as}\subseteq\mathfrak S_{\rm cl},
\qquad \overline{\mathfrak S_{\rm as}}^{\diamond}=\mathfrak S_{\rm cl}.
\tag{2.2}
$$

到固定目标的距离下确界在三类上相同。

证明。这是源甲定理 18.2 的接口；以下给出所需范数与量词。对几乎必然终止协议，深度 $n$ 未终止路径的平均效应记为 $R_n$。完整结果树给出 $0\le R_n\le I_5$。在 $I_5/5$ 上几乎必然终止意味着 $\operatorname{Tr}R_n\to0$。把这些未终止路径立即停止，保留当时寄存器并赋固定旗标，得到合法的有限深度通道 $\mathcal T_n$。原续行与替代分别是效应同为 $R_n$ 的 CP 映射：整体不终止残余效应为正，且在忠实输入 $I_5/5$ 上迹为零，故该残余效应为零；因此未终止路径的实际续行恰好耗尽 $R_n$，无需另假设每个条件态上的统一终止界。

任意有限维 CP 映射 $\Psi$ 都满足

$$
\|\Psi\|_\diamond=\|\Psi^\dagger(I)\|_\infty.
\tag{2.3}
$$

为证明，堆叠 Kraus 算符为 $V$，则 $\Psi(X)=\operatorname{Tr}_E(VXV^\dagger)$，$V^\dagger V=\Psi^\dagger(I)$。迹范数对偶性及 $\|Y\otimes I_E\|_\infty=\|Y\|_\infty$ 给出偏迹的迹范数压缩性，对复算符及任意参考均成立。乘以 $V$ 与 $V^\dagger$ 的范数上界为 $\|V\|_\infty^2$，得到 (2.3) 的上界；以 $V^\dagger V$ 最大特征值的单位特征向量作输入则取到反向不等式。输入输出维度有限，故积分定义的 CP 映射同样有有限 Kraus 表示。这里的 Kraus 堆叠仅用于证明，不向协议添加辅助系统。因此

$$
\|\mathcal T-\mathcal T_n\|_\diamond
\le2\|R_n\|_\infty\le2\operatorname{Tr}R_n\longrightarrow0.
\tag{2.4}
$$

这证明第二个包含关系；第一个显然，取闭包得到其余等式。距离函数连续且有限深度类稠密，故三个下确界相同。不要求统一停止时限或有限期望时长，也不授予无限非终止操作。$\square$

**引理 2.3（从所有态测试到所有复测试）。** 设有限维复线性映射 $\Lambda$ 保持伴随。若对每个有限参考 $Z$ 及其与输入的每个归一化态 $\xi$ 都有 $\|(\Lambda\otimes\operatorname{id}_Z)(\xi)\|_1\le c_0$，则 $\|\Lambda\|_\diamond\le c_0$。证明纯态上的该界已经足够，因为迹范数凸性给出混合态上的同一界。

证明。对任意参考上的复算符 $X$，另加一个只用于范数测试的二值参考，取 Hermitian 块

$$
Y=\frac12\begin{pmatrix}0&X\\X^\dagger&0\end{pmatrix}.
$$

由奇异值分解，$\|Y\|_1=\|X\|_1$。保持伴随性保证输出仍有同样块形，故 $\|(\Lambda\otimes\operatorname{id})(Y)\|_1=\|(\Lambda\otimes\operatorname{id})(X)\|_1$。写 $Y=Y_+-Y_-$，两部分为正，且 $\operatorname{Tr}Y_++\operatorname{Tr}Y_-=\|Y\|_1$。把每个非零部分按迹归一化，应用所有态及有限参考的假设，再用三角不等式，即得输出范数至多 $c_0\|X\|_1$。这正是 (1.2) 的所有复测试上界。额外参考与 Jordan 分解均是分析工具，不是模拟原语。$\square$

## 3. 共同右支撑、精确支撑泛函与全协议下界

**定义 3.1（归一化输入与支撑泛函）。** 在引理 2.1 的规范坐标中工作，目标为 $\widehat{\mathcal J}(X)=\bigoplus_jH_jXH_j$，其中 $H_j=P_j+qS$。取同一输入密度及其五维未读取参考纯化

$$
\rho=\frac{\sqrt2(P+Q)+3S}{N},\qquad
|\psi_\rho\rangle=\sum_{k=0}^4\sqrt{\rho_{kk}}\,e_k\otimes e_k,
\qquad N=3+4\sqrt2.
\tag{3.1}
$$

输出优先向量化记为 $|B\rangle\!\rangle=\sum_kBe_k\otimes e_k$，故 $\langle\!\langle B|C\rangle\!\rangle=\operatorname{Tr}(B^\dagger C)$。置

$$
\begin{gathered}
b_j=|H_j\sqrt\rho\rangle\!\rangle,\qquad a_j=\sqrt2\,b_j,\qquad
\Pi=\bigoplus_{j=0}^1|a_j\rangle\langle a_j|,\\
\omega=(\widehat{\mathcal J}\otimes\operatorname{id})(|\psi_\rho\rangle\langle\psi_\rho|),\qquad
\mathcal F(\mathcal T)=\operatorname{Tr}\!\left[\Pi(\mathcal T\otimes\operatorname{id})(|\psi_\rho\rangle\langle\psi_\rho|)\right],\\
C_j=2P_j+3S.
\end{gathered}
\tag{3.2}
$$

这里 $\operatorname{Tr}\rho=(4\sqrt2+3)/N=1$，且 $\rho$ 严格正定，故纯化归一化。又因 $H_j^2=P_j+S/2$，

$$
\|b_j\|^2=\operatorname{Tr}(\rho H_j^2)
=\frac{2\sqrt2+3/2}{N}=\frac12.
$$

因此 $a_j$ 是单位向量，其三个非零 Schmidt 平方权重为 $2\sqrt2/N,2\sqrt2/N,3/N$，并非等权。不同旗标使 $\Pi$ 成为正交投影，而且

$$
\omega=\frac12\bigoplus_j|a_j\rangle\langle a_j|,
\qquad \operatorname{Tr}\omega=\operatorname{Tr}(\Pi\omega)=1.
\tag{3.3}
$$

赋给旗标 $j$ 的末端 Kraus 矩阵 $B$ 对泛函的贡献为

$$
\begin{aligned}
f_j(B)
&=|\langle a_j,|B\sqrt\rho\rangle\!\rangle\rangle|^2
 =2|\operatorname{Tr}(\rho H_jB)|^2
 =\frac{|\operatorname{Tr}(C_j^\dagger B)|^2}{N^2},\\
\sqrt2\,\rho H_j&=C_j/N.
\end{aligned}
\tag{3.4}
$$

第一等式后的迹来自 $\operatorname{Tr}(\sqrt\rho H_jB\sqrt\rho)$ 的循环性；内积中第一变量的共轭及所有归一化因子均已包含。一个规范模拟器的 $\mathcal F$ 是这些非负贡献的总和或积分；固定经典带时 Kraus 矩阵不含带的概率权，积分才引入该权。末端粗化合并正的 Kraus–Choi 项，不把不同记录的 Kraus 矩阵相干相加。

**引理 3.2（共同右支撑的完整分支界）。** 令 $E$ 为非零输入投影，$B_t=B_tE$ 为有限或可数末端矩阵族，赋旗标 $j_t\in\{0,1\}$，并满足

$$
\sum_tB_t^\dagger B_t=E.
$$

在 $EH$ 上记 $A_j=EC_j^\dagger C_jE$。则

$$
\sum_t|\operatorname{Tr}(C_{j_t}^\dagger B_t)|^2
\le\max_{0\le p\le1}
\left[\operatorname{Tr}_{EH}\sqrt{pA_0+(1-p)A_1}\right]^2.
\tag{3.5}
$$

这是实际子树的必要上界；满足所列代数条件的更大矩阵族只作为外部松弛，不是新增操作原语。

证明。对 $EH$ 上任意正定 $Y$，其分数幂在 $E^\perp H$ 上以零延伸。对从 $EH$ 到 $H$ 的矩阵 $C_jEY^{-1/2}$ 与 $BY^{1/2}$ 用 Hilbert–Schmidt Cauchy–Schwarz。由 $B=BE$ 及迹的循环性，二者内积为

$$
\operatorname{Tr}_{EH}(Y^{-1/2}EC_j^\dagger BY^{1/2})
=\operatorname{Tr}(C_j^\dagger B),
$$

平方范数分别是 $\operatorname{Tr}_{EH}(A_jY^{-1})$ 与 $\operatorname{Tr}_{EH}(YB^\dagger B)$。故

$$
|\operatorname{Tr}(C_j^\dagger B)|^2
\le\operatorname{Tr}_{EH}(A_jY^{-1})\,
   \operatorname{Tr}_{EH}(YB^\dagger B).
\tag{3.6}
$$

若两个旗标均有 $\operatorname{Tr}_{EH}(A_jY^{-1})\le1$，对后代求和及使用完整效应恒等式就给出上界 $\operatorname{Tr}_{EH}Y$。可数族由非负部分和的极限给出同一结论。右侧 $Y$ 幂的放置由共同右支撑决定，不能任意换成左侧加权。

为构造这样的 $Y$，固定 $\varepsilon>0$，记

$$
A_{j,\varepsilon}=A_j+\varepsilon I_{EH},\qquad
A_\varepsilon(p)=pA_{0,\varepsilon}+(1-p)A_{1,\varepsilon},\qquad
h_\varepsilon(p)=\operatorname{Tr}_{EH}\sqrt{A_\varepsilon(p)}.
$$

正函数 $h_\varepsilon$ 在闭区间上取到最大值且可微。这里不要求矩阵可交换：若 $Z=\sqrt{A_\varepsilon(p)}$，由 $Z^2=A_\varepsilon(p)$ 得

$$
ZZ'+Z'Z=A_0-A_1.
$$

在正定 $Z$ 的本征基中，线性映射 $X\mapsto ZX+XZ$ 的各系数乘以两个正本征值之和，因此可逆，给出平方根的可微性。左乘 $Z^{-1}$ 后取迹即得

$$
h_\varepsilon'(p)=\frac12\operatorname{Tr}_{EH}
\left[A_\varepsilon(p)^{-1/2}(A_0-A_1)\right].
\tag{3.7}
$$

取一个最大点 $p_*$，令 $h=h_\varepsilon(p_*)$，$Y=h\sqrt{A_\varepsilon(p_*)}$，并置 $t_j=\operatorname{Tr}_{EH}(A_{j,\varepsilon}Y^{-1})$。直接由定义有

$$
p_*t_0+(1-p_*)t_1=1,\qquad
h_\varepsilon'(p_*)=\frac h2(t_0-t_1).
$$

内点最大时 $t_0=t_1=1$。若 $p_*=0$，右导数非正，故 $t_0\le t_1=1$；若 $p_*=1$，左导数非负，故 $t_1\le t_0=1$。所以在包括两个端点的所有情形中，

$$
\operatorname{Tr}_{EH}(A_jY^{-1})\le t_j\le1.
$$

式 (3.6) 因而把后代总和界为

$$
\operatorname{Tr}_{EH}Y=h^2=\max_p h_\varepsilon(p)^2.
$$

最后令 $\varepsilon\downarrow0$。若 $r=\operatorname{rank}E$，标量正则化使每个本征值增加 $\varepsilon$，而 $0\le\sqrt{\lambda+\varepsilon}-\sqrt\lambda\le\sqrt\varepsilon$。于是对所有 $p$ 一致有

$$
0\le\operatorname{Tr}_{EH}\sqrt{A(p)+\varepsilon I_{EH}}
      -\operatorname{Tr}_{EH}\sqrt{A(p)}\le r\sqrt\varepsilon,
\qquad A(p)=pA_0+(1-p)A_1.
$$

设 $M=\max_j\|A_j\|_\infty$，无正则化的迹至多 $r\sqrt M$。平方迹的差因此一致至多

$$
r\sqrt\varepsilon\,(2r\sqrt M+r\sqrt\varepsilon)\longrightarrow0.
$$

最大值随之收敛，得到 (3.5)，也覆盖奇异压缩及端点最大。证明没有把松弛的最优矩阵族宣称为可实现协议。$\square$

**定理 3.3（所有实际协议的精确支撑值）。** 对定义 3.1 的同一泛函，

$$
\max_{\mathcal T\in\mathfrak S_{\rm fin}}\mathcal F(\mathcal T)
=\max_{\mathcal T\in\mathfrak S_{\rm as}}\mathcal F(\mathcal T)
=\max_{\mathcal T\in\mathfrak S_{\rm cl}}\mathcal F(\mathcal T)
=\frac{65}{N^2}.
\tag{3.8}
$$

最大值由一次实际完整 PVM 取到，且在引理 2.1 的坐标对应下对所有角度有相同结论。

证明。先固定一条完整输入独立经典带，考虑有限深度树。删除零投影与恒等 PVM；首次非平凡完整 PVM 前只有一个幺正乘积 $U$。若该 PVM 为 $\{R_a\}$，置

$$
E_a=U^\dagger R_aU,\qquad r_a=\operatorname{rank}E_a>0,\qquad
\sigma_a=\operatorname{Tr}(E_aS)=\|E_as\|^2.
$$

其任一末端后代有 $B_t=M_tR_aU$，故 $B_tE_a=B_t$，而同一实际子树满足

$$
\sum_{t\succ a}B_t^\dagger B_t=E_a,\qquad
\sum_aE_a=I_5,\qquad \sum_ar_a=5,\qquad
0\le\sigma_a\le1,\qquad\sum_a\sigma_a=1.
\tag{3.9}
$$

第一式可从叶端逆向归纳：停止节点的续行效应为 $I_5$，幺正节点共轭 $I_5$ 仍为 $I_5$，完整 PVM 节点求和为 $\sum_bR_bI_5R_b=I_5$。不同结果后的控制和整棵子树可以完全不同。故右支撑、总效应、秩及 $S$ 方向的分配都来自同一个首次测量，不能分别换成不同实现的最优读数。

对任意秩 $r$ 的投影 $E$，引理 3.2 中的混合压缩为 $EM(p)E$，其中

$$
M(p)=4pP+4(1-p)Q+9S\le4I_5+5S.
$$

记 $\sigma=\operatorname{Tr}(ES)$。$ESE=|Es\rangle\langle Es|$ 的唯一可能非零本征值为 $\sigma$，所以 $4E+5ESE$ 在 $EH$ 上的本征值为 $4+5\sigma$ 及 $r-1$ 个 $4$。由正矩阵次序下的本征值单调性，再逐项开方求和，每个完整分支的未归一化重叠至多

$$
g_r(\sigma)=\left[2(r-1)+\sqrt{4+5\sigma}\right]^2.
\tag{3.10}
$$

这里两个可能末端旗标使用同一个 $E$。

若首次 PVM 的秩分拆为 $3+2$，令 $\sigma$ 为秩三分支的 $S$ 重叠；另一个由 (3.9) 必为 $1-\sigma$。总上界为

$$
G(\sigma)=\left[4+\sqrt{4+5\sigma}\right]^2
          +\left[2+\sqrt{9-5\sigma}\right]^2.
$$

在整个 $[0,1]$ 上，

$$
G'(\sigma)=5\left[\frac4{\sqrt{4+5\sigma}}
                  -\frac2{\sqrt{9-5\sigma}}\right]>0,
$$

因为第一比值至少为 $4/3$，第二至多为 $1$。所以

$$
G(\sigma)\le G(1)=49+16=65.
\tag{3.11}
$$

这是同一对正交结果对共同 $S$ 方向的联合分配界。

若各秩至多三但分拆不是 $3+2$，则 $\sum_ar_a^2\le11$：有秩三时其余为 $1+1$；没有秩三时 $r_a\le2$，故 $r_a^2\le2r_a$，总和至多十。先展开 (3.10)，再用平方根的切线界，得到

$$
\begin{aligned}
g_r(\sigma)
&=4(r-1)^2+4(r-1)\sqrt{4+5\sigma}+4+5\sigma\\
&\le4(r-1)^2+4(r-1)(2+5\sigma/4)+4+5\sigma\\
&=4r^2+5r\sigma.
\end{aligned}
$$

于是总上界至多 $4\cdot11+5\cdot3\sum_a\sigma_a=59<65$。这覆盖 $3+1+1$、$2+2+1$、$2+1+1+1$ 及五个一。先展开避免把松切线直接平方后遗漏正的二次项。

剩下的非平凡分拆为 $4+1$，需使用引理 3.2 的更强压缩界。$M(p)$ 的全空间谱为

$$
9,\quad4p,\quad4p,\quad4(1-p),\quad4(1-p).
$$

压缩到任意四维子空间后，第 $k$ 个递减本征值不超过全空间第 $k$ 个递减本征值：Rayleigh 极小极大原理中，限于该四维空间的试验子空间只是全空间试验子空间的子集。因此当 $p\ge1/2$ 时，压缩平方根的迹至多

$$
3+4\sqrt p+2\sqrt{1-p}
=3+2\left(2\sqrt p+\sqrt{1-p}\right)
\le3+2\sqrt5,
$$

最后对向量 $(2,1)$ 与 $(\sqrt p,\sqrt{1-p})$ 用 Cauchy–Schwarz。$p\le1/2$ 时交换 $P,Q$ 即得同一界。故秩四分支至多 $(3+2\sqrt5)^2=29+12\sqrt5$。秩一分支至多九，因为 $M(p)\le9I_5$。总和至多

$$
38+12\sqrt5<65;
\qquad \sqrt5<9/4\ \text{由}\ 5<81/16\ \text{得出}.
\tag{3.12}
$$

这些是两个有效上界之和，不要求它们同时可达，也不假定任意秩四续行为合法原语。只用较粗的 $g_4$ 不足以给出所需结论。

非平凡完整 PVM 至少有两个正秩部分，因此以上穷尽所有可能。若整条带没有非平凡 PVM，它以一个幺正 $V$ 和确定旗标 $j$ 停止。$C_j$ 的非零奇异值为 $3,2,2$；在奇异基中幺正对角元模至多一，故

$$
|\operatorname{Tr}(C_j^\dagger V)|\le7,
\qquad |\operatorname{Tr}(C_j^\dagger V)|^2\le49<65.
\tag{3.13}
$$

空操作序列也包括在内。于是每条有限深度确定带的总未归一化重叠至多六十五。

现在对输入独立经典带积分。贡献的非负性允许 Tonelli 求和及积分，覆盖非原子带分布。反馈处的随机选择可在各个可能有限历史上预采样；这不使带的分布依赖输入。末端随机旗标可并入带，或分成含概率平方根的 Kraus 项。粗化只合并正项，所有分支与全部概率质量均保留。由 (3.4)，每个实际有限深度模拟器满足 $\mathcal F(\mathcal T)\le65/N^2$。

这个固定输入及投影的线性泛函连续，且

$$
|\mathcal F(\mathcal T)-\mathcal F(\mathcal T')|
\le\|\mathcal T-\mathcal T'\|_\diamond.
$$

引理 2.2 的有限逼近因而把该上界传到 $\mathfrak S_{\rm cl}$ 和 $\mathfrak S_{\rm as}$。也可直接处理可数树：固定带的未终止残余效应为正，整体在 $I_5/5$ 上的几乎必然终止使其积分迹为零，故几乎每条带的残余效应为零。该带各首次结果下的残余为正且总和为零，故分别为零；(3.9) 的可数后代效应和仍然成立。没有非平凡 PVM 的带不能留下正权重的不停止幺正路径。这不要求每条带共享深度上界、有限期望时长或对每个条件态另加停止假设。

最后给出实际取到者。规范坐标中测量完整 Lüders PVM $\{P+S,Q\}$，分别报告零、一并保留寄存器。末端矩阵

$$
B_0=P+S,\qquad B_1=Q
$$

的效应和为 $I_5$，且

$$
\operatorname{Tr}(C_0^\dagger B_0)=7,\qquad
\operatorname{Tr}(C_1^\dagger B_1)=4,
\qquad 7^2+4^2=65.
\tag{3.14}
$$

这是原菜单中的单次实际 PVM，已经同时达到 (3.11) 的共同 $S$ 分配界及总上界。它属于三个类，故 (3.8) 中均为最大值。

为明确所有角度的见证，令 $\mathsf W=\bigoplus_jT_j$ 为输出坐标幺正，取

$$
|\psi_{\rho,\theta}\rangle=(D_\theta^\dagger\otimes I)|\psi_\rho\rangle,
\qquad
\Pi_\theta=(\mathsf W\otimes I)\Pi(\mathsf W^\dagger\otimes I).
\tag{3.15}
$$

实际目标输出为 $(\mathsf W\otimes I)\omega(\mathsf W^\dagger\otimes I)$。对任意模拟器施加引理 2.1 的逆对应，即得到规范泛函，故同一上界及最大值覆盖每个实 $\theta$。实际取到者在最前施加 $D_\theta$、测量上述 PVM、末端按报告旗标施加 $T_j$。$\mathsf W$ 只表达按经典旗标的合法反馈，没有引入可供协议使用的相干旗标量子系统；参考始终不被读取。$\square$

**定理 3.4（全协议距离下界）。** 对每个 $\theta\in\mathbb R$ 和每个 $\mathcal T\in\mathfrak S_{\rm fin}\cup\mathfrak S_{\rm as}\cup\mathfrak S_{\rm cl}$，

$$
\|\mathcal J_\theta-\mathcal T\|_\diamond
\ge L=\frac{48(\sqrt2-1)}{41+24\sqrt2}>\frac14>\frac29.
\tag{3.16}
$$

证明。在规范坐标中，模拟器对 (3.1) 的输出 $\sigma$ 与 $\omega$ 均归一化。定理 3.3 给出 $x=\operatorname{Tr}(\Pi\sigma)\le65/N^2$。二值测量 $\{\Pi,I-\Pi\}$ 将目标送到 $(1,0)$，模拟器送到 $(x,1-x)$，不折半的经典距离为

$$
2(1-x)\ge2\left(1-\frac{65}{N^2}\right)
=\frac{48(\sqrt2-1)}{41+24\sqrt2}=L.
$$

对 Hermitian $Y=Y_+-Y_-$，每个测量效应 $M$ 满足 $|\operatorname{Tr}(MY)|\le\operatorname{Tr}[M(Y_++Y_-)]$；对完整测量求和即证迹范数压缩性。因此 $\|\omega-\sigma\|_1\ge L$。归一化纯化是菱形范数允许的一个有限参考输入，故提供同一下界；使用一个态测试不限制 (1.2) 中更大的任意复算符上确界。式 (3.15) 及合法幺正对应把它传给所有角度。

所有分母为正。$L>1/4$ 等价于 $168\sqrt2>233$。平方比较给出 $\sqrt2>7/5$，所以 $168\sqrt2>1176/5>233$；又有 $1/4-2/9=1/36>0$。这是符号严格比较。定理 3.3 及引理 2.2 已包含可测带、反馈、停止与闭包量词，故结论具有所述全协议范围。$\square$

**命题 3.5（支撑取到与距离取到的区别）。** 定理 3.3 的实际支撑最大者在输入 $S$ 上的不折半输出误差恰为一，因而其菱形误差至少为一，不能取到下界 $L$。

证明。规范目标在 $S$ 上输出 $(S/2,S/2)$；(3.14) 的实际协议输出 $(S,0)$。两旗标差块为 $-S/2,S/2$，迹范数之和恰为一。另一方面，$\sqrt2<3/2$ 给出 $N^2<77<130$，所以 $65/N^2>1/2$，从而 $L=2(1-65/N^2)<1$。幺正对应在实际角度输入 $D_\theta^\dagger S D_\theta$ 上保留同一误差。

所以线性泛函达到最大值不意味着随后二值测量的迹范数下界取等，也不意味着该纯化给出模拟器的最大菱形误差。这个特定输入、特定投影的重叠优化已经有实际协议精确达到；只收紧同一重叠最大值不能继续提高 $L$。全局距离需要不同分离测试或对完整输出误差的进一步共同约束。$\square$

**命题 3.6（紧的首次 PVM Choi 外部松弛）。** 以下均在规范坐标中，记未归一化支撑分数

$$
\mathcal G(\mathcal T)=N^2\mathcal F(\mathcal T).
$$

对每个有序正秩分拆 $r_1+\cdots+r_m=5$、$m\ge2$，取两两正交、和为 $I_5$ 的投影 $E_a$，其秩为 $r_a$。对每个 $a$ 取两个 CP 操作 $\Psi_{a0},\Psi_{a1}:M_5\to M_5$，只要求

$$
\sum_{j=0}^1\Psi_{aj}^\dagger(I_5)=E_a,
\qquad \mathcal T_j=\sum_a\Psi_{aj}.
\tag{3.17}
$$

所有这样得到的带旗标通道组成 $\mathcal K_{\rm pvm}$。另令 $\mathcal K_{\rm unit}$ 只包含一个全五维幺正、报告一个确定旗标的通道，并置

$$
\mathcal K=\mathcal K_{\rm pvm}\cup\mathcal K_{\rm unit},
\qquad \mathcal C=\operatorname{conv}(\mathcal K).
$$

$\mathcal C$ 是非空紧凸集，并且

$$
\mathfrak S_{\rm fin}\subseteq\mathfrak S_{\rm as}
\subseteq\mathfrak S_{\rm cl}\subseteq\mathcal C,
\qquad \max_{\mathcal T\in\mathcal C}\mathcal G(\mathcal T)=65.
\tag{3.18}
$$

式 (3.17) 的一般 CP 后代只定义外部松弛，不是合法后处理原语。尤其不能把没有首次非平凡分拆的情况扩张为任意秩五 CP 通道；那里只允许 $\mathcal K_{\rm unit}$，再作输入独立的经典混合。

证明。对 (3.17) 的任意 Kraus 表示 $B_{ajt}$，有 $\sum_{j,t}B_{ajt}^\dagger B_{ajt}=E_a$。若 $x\in\ker E_a$，则

$$
\sum_{j,t}\|B_{ajt}x\|^2=\langle x,E_ax\rangle=0.
$$

非负项分别为零，故每个 $B_{ajt}=B_{ajt}E_a$。同一首次结果的全部后代共享右支撑与完整效应，这正是引理 3.2 的条件。

固定一个秩分拆时，满足投影恒等式、正交性、和及秩条件的投影元组是有限维闭有界集；秩可由投影的迹固定，故该集合紧。输出优先的非归一化 Choi 矩阵定义为

$$
J(\Psi)=\sum_{k,\ell}\Psi(|e_k\rangle\langle e_\ell|)
 \otimes |e_k\rangle\langle e_\ell|.
$$

CP 条件是 $J(\Psi)\ge0$，而效应条件成为闭约束

$$
\sum_j\operatorname{Tr}_{\rm out}J(\Psi_{aj})=E_a^{\mathsf T}.
$$

正性给出 $0\le\operatorname{Tr}J(\Psi_{aj})\le r_a$，所以所有 Choi 矩阵均有界。投影与 Choi 矩阵的联合可行集因此紧，连续求和所给的通道像也紧。五的正秩分拆只有有限多个；幺正群与二值确定旗标的乘积同样紧，所以 $\mathcal K$ 紧。带旗标保持伴随映射所成的实向量空间维数有限，记为 $D$。Carathéodory 定理将其凸包中每一点表示为至多 $D+1$ 个 $\mathcal K$ 中的点的凸组合；允许零权补足个数后，$\mathcal C$ 是紧单纯形与 $\mathcal K^{D+1}$ 的连续像，因而紧。

再核对实际协议的包含关系。固定实际有限深度协议的一条输入独立经典带；若没有非平凡 PVM，得到的就是 $\mathcal K_{\rm unit}$ 中一个通道。否则首次 PVM 前的幺正乘积为 $U$，其结果投影为 $R_a$。定理 3.3 的完整树论证给出 $E_a=U^\dagger R_aU$、$B_t=M_tR_aU$，以及同一实际子树的 $\sum_{t\succ a}B_t^\dagger B_t=E_a$。按末端旗标分组即满足 (3.17)，所以固定带通道属于 $\mathcal K$。任意可测、与输入独立的带积分属于闭凸集 $\mathcal C$：若其积分在外，有限维分离线性泛函会严格分离积分与 $\mathcal C$，却无法分离全部位于 $\mathcal K$ 的被积通道，矛盾。故 $\mathfrak S_{\rm fin}\subseteq\mathcal C$；闭性及引理 2.2 给出其余包含关系。这一步涵盖非原子经典随机性，并不假定任意松弛通道实际可实现。

最后，上述共同右支撑使引理 3.2 及定理 3.3 中的每个秩分拆估计逐字适用于 $\mathcal K_{\rm pvm}$：$3+2$ 的联合上界为 $G(\sigma)\le65$；其余所有秩至多三的分拆至多 $59<65$；$4+1$ 至多 $38+12\sqrt5<65$。$\mathcal K_{\rm unit}$ 的界为 $49<65$。这些证明只用了相同右支撑、完整效应与投影分拆，均未使用一般 CP 后代的合法性，故不需重作推导。线性性把上界传到 $\mathcal C$，而 (3.14) 的实际协议达到六十五。这是覆盖全部分拆的全局精确最大值，所列严格较小的分拆上界不被称作各分拆的精确最优值。$\square$

**定理 3.7（整个支撑极大面与全部后代取等条件）。** 定义两个实际仪器

$$
\begin{array}{ll}
\mathcal A_{+,0}=\operatorname{Ad}_{P+S},&
\mathcal A_{+,1}=\operatorname{Ad}_Q,\\
\mathcal A_{-,0}=\operatorname{Ad}_P,&
\mathcal A_{-,1}=\operatorname{Ad}_{Q+S},
\end{array}
\qquad
\mathcal T_t=t\mathcal A_++(1-t)\mathcal A_-,\quad 0\le t\le1.
$$

则完整的暴露面恰为

$$
\{\mathcal T\in\mathcal C:\mathcal G(\mathcal T)=65\}
=\{\mathcal T_t:0\le t\le1\}.
\tag{3.19}
$$

两个端点分别测量 $\{P+S,Q\}$、$\{P,Q+S\}$，按所列顺序报告旗标并保留寄存器；经典混合实现整条线段。因此三个实际类中的全部支撑最大者也恰为这条线段。

证明。先考察 $\mathcal K$ 中分数为六十五的通道。命题 3.6 的严格界排除纯幺正与除 $3+2$ 外的所有分拆。记秩三投影为 $E_3$；(3.11) 的严格单调性迫使 $\operatorname{Tr}(E_3S)=1$，故 $E_3s=s$，互补秩二投影 $E_2=I-E_3$ 满足 $E_2s=0$。两支的分数必须分别达到各自上界四十九与十六。

对秩三支，连续分支表达式有一个最大点 $p\in[0,1]$。令 $M(p)=4pP+4(1-p)Q+9S$。分数四十九要求

$$
\operatorname{Tr}_{E_3H}\sqrt{E_3M(p)E_3}
=7=\operatorname{Tr}_{E_3H}\sqrt{4E_3+5S}.
$$

这里两个被开方矩阵有正次序关系。一般地，若 $0\le A\le B$ 且 $\operatorname{Tr}\sqrt A=\operatorname{Tr}\sqrt B$，有序本征值单调性及平方根严格递增性迫使每个对应本征值相等；于是正矩阵 $B-A$ 的迹为零，故 $A=B$。应用之得到

$$
E_3M(p)E_3=4E_3+5S,
\qquad E_3[(1-p)P+pQ]E_3=0.
\tag{3.20}
$$

若 $0<p<1$，方括号的核恰为 $SH$，正性会把三维 $E_3H$ 放进该一维核中，矛盾。若 $p=1$，有 $QE_3=0$，故 $E_3\le P+S$，同秩给出 $E_3=P+S$。若 $p=0$，同理 $E_3=Q+S$。这确定了首次 PVM 的两种规范方向，而非仅展示一个取等实例。

还须确定这些方向的所有 Kraus 后代及其旗标。先取 $E_3=P+S$。在该子空间上选

$$
Y=14P+21S=7C_0|_{E_3H},\qquad
\alpha_j=\operatorname{Tr}_{E_3H}(E_3C_j^2E_3Y^{-1}).
$$

则 $\operatorname{Tr}Y=49$、$\alpha_0=1$、$\alpha_1=3/7$。对后代 $B=B E_3$ 写 $d_B=\operatorname{Tr}(YB^\dagger B)\ge0$。式 (3.6) 及完整效应说明总亏损为

$$
49-\sum_B|\operatorname{Tr}(C_{j_B}^\dagger B)|^2
=\sum_B\left[(1-\alpha_{j_B})d_B+
\alpha_{j_B}d_B-|\operatorname{Tr}(C_{j_B}^\dagger B)|^2\right].
\tag{3.21}
$$

每一项均非负。取等迫使每个旗标一后代的 $d_B=0$，由 $Y$ 在支撑上正定知该后代为零。每个非零旗标零后代必须在 Hilbert–Schmidt Cauchy–Schwarz 中取等，亦即

$$
BY^{1/2}=\lambda C_0E_3Y^{-1/2},\qquad
B=\lambda C_0E_3Y^{-1}=(\lambda/7)E_3.
\tag{3.22}
$$

完整效应又给出这些标量的模平方和为一。所以整支操作恰为旗标零上的 $\operatorname{Ad}_{P+S}$，无论 Kraus 记录怎样细分。

互补支为 $E_2=Q$。取 $Y=8Q$，其迹为十六；旗标一的系数为一，旗标零的系数为零。同一非负亏损分解排除全部旗标零后代，Cauchy–Schwarz 取等迫使其余后代均为 $Q$ 的标量倍数，模平方和为一。故此支恰为旗标一上的 $\operatorname{Ad}_Q$，整个通道是 $\mathcal A_+$。交换 $P,Q$ 与两个旗标得到 $\mathcal A_-$。证明允许任意 CP 后代，故包含一切实际自适应后代；对可数族，非负亏损和为零仍逐项强制上述结论。

任意 $\mathcal T\in\mathcal C$ 都有有限凸组合表示。若 $\mathcal G(\mathcal T)=65$，所有正权分量都必须达到六十五，因此只可能是刚分类的两个端点。反之，两个实际端点及其经典混合均达到六十五。由 (3.18) 以及整段属于 $\mathfrak S_{\rm fin}$，三个实际类的面与 (3.19) 相同。若从实际树本身描述取等，经典带上的非负支撑亏损积分为零，故几乎每条有权带都取等；定理 3.3 的忠实输入与残余效应论证使几乎必然终止类的这些带具有完整可数后代效应，所以其非零后代亦服从 (3.22) 及互补支条件。这里不对零测度异常带作额外停止断言。$\square$

**命题 3.8（同一通道的旗标、输出与相干关系；仅支撑加 $S$ 测试的限制）。** 对整个极大面，用同一个 $t$，在每个复矩阵上有

$$
\begin{aligned}
\mathcal T_{t,0}(X)&=PXP+t(PXS+SXP)+tSXS,\\
\mathcal T_{t,1}(X)&=QXQ+(1-t)(QXS+SXQ)+(1-t)SXS.
\end{aligned}
\tag{3.23}
$$

其效应为 $P+tS$、$Q+(1-t)S$，在 $S$ 上的完整带旗标输出为 $(tS,(1-t)S)$，故

$$
e_S(\mathcal T_t):=\|(\widehat{\mathcal J}-\mathcal T_t)(S)\|_1
=2|t-1/2|.
\tag{3.24}
$$

对正输入，每旗标的量子输出均在 $P_j+S$ 中；在这些子空间之外的输出泄漏为零。两旗标的目标相干系数均为 $q$，而极大面上分别为 $t$ 与 $1-t$；它们之和为一，不能同时等于 $q$，因为 $2q=\sqrt2>1$。特别地，精确的 $S$ 输出迫使 $t=1/2$，此时两个相干系数都是 $1/2$。

更精确地，对任意通道记

$$
b(\mathcal T)=2\left[1-\frac{\mathcal G(\mathcal T)}{N^2}\right],
\qquad B_S(\mathcal T)=\max\{b(\mathcal T),e_S(\mathcal T)\}.
\tag{3.25}
$$

这里函数 $b(\mathcal T)$ 与 §4 的控制标量 $b$ 不同。则

$$
\min_{\mathcal T\in\mathfrak S_{\rm fin}}B_S(\mathcal T)
=\min_{\mathcal T\in\mathfrak S_{\rm as}}B_S(\mathcal T)
=\min_{\mathcal T\in\mathfrak S_{\rm cl}}B_S(\mathcal T)=L.
\tag{3.26}
$$

证明。展开两个端点的 Kraus 操作并作凸组合即得 (3.23)；取迹和代入 $S$ 得效应与 (3.24)。这些 Kraus 的像均在相应 $P_j+S$，给出输出支撑结论；相干系数的比较也是同一展开的直接结果。所有这些约束来自同一仪器，未把不同实现的最优边缘拼合。

定理 3.4 的二值支撑测量论证其实给出 $\|\widehat{\mathcal J}-\mathcal T\|_\diamond\ge b(\mathcal T)$；定理 3.3 又使实际类上 $b\ge L$。所以 $B_S\ge L$。但实际公平混合 $\mathcal T_{1/2}$ 满足 $\mathcal G=65$，并且 $\mathcal T_{1/2}(S)=\widehat{\mathcal J}(S)$，连同旗标及量子输出都精确相等。于是同一个有限深度协议有 $b=L$、$e_S=0$，从而 $B_S=L$。这证明三个最小值及有限取到。这一反例只限制指定的“两个测试取最大值”证书，不排除利用其他信息的联合论证；它同时说明命题 3.5 的一个端点有 $S$ 误差，不能替代整个极大面的分析。$\square$

**引理 3.9（固定相干测试与面上精确最小误差）。** 令

$$
\psi_*=\frac{e_0+e_1}{2}+\frac{s}{\sqrt2},\qquad
h(\mathcal T)=\|(\widehat{\mathcal J}-\mathcal T)(|\psi_*\rangle\langle\psi_*|)\|_1,
\qquad U_0=1-\frac1{\sqrt2}.
\tag{3.27}
$$

$\psi_*$ 为单位系统向量，不需参考。$h$ 连续、凸，并且对所有通道都不超过相应菱形误差。整个支撑极大面满足

$$
h(\mathcal T_t)\ge U_0>L,
\qquad
\min_{0\le t\le1}\|\widehat{\mathcal J}-\mathcal T_t\|_\diamond=U_0,
\tag{3.28}
$$

后一个最小值由实际公平混合 $\mathcal T_{1/2}$ 取到。

证明。对通道作变换

$$
(\mathscr R\mathcal T)_j(X)=F\mathcal T_{1-j}(FXF)F.
$$

它固定 $\widehat{\mathcal J}$，把 $\mathcal T_t$ 变成 $\mathcal T_{1-t}$，而 $F\psi_*=\psi_*$。迹范数的幺正不变性给出 $h(\mathcal T_t)=h(\mathcal T_{1-t})$，再由凸性知 $h(\mathcal T_t)\ge h(\mathcal T_{1/2})$。

置 $\epsilon=q-1/2>0$。在中点，差映射的旗标 $j$ 为 $\epsilon(P_jXS+SXP_j)$。对 $X=|\psi_*\rangle\langle\psi_*|$，其两个正交向量 $P_j\psi_*$、$S\psi_*$ 的范数分别为 $1/2$ 与 $1/\sqrt2$，每旗标差块的两个非零特征值因而为 $\pm\epsilon/(2\sqrt2)$。每块迹范数为 $\epsilon/\sqrt2$，合计

$$
h(\mathcal T_{1/2})=\sqrt2\epsilon=U_0.
$$

为证这是完整菱形范数而非仅系统态误差，取任意有限参考上的单位纯向量 $\psi$，写

$$
x_0=(P\otimes I)\psi,\quad x_1=(Q\otimes I)\psi,
\quad x_S=(S\otimes I)\psi,
\quad p_0=\|x_0\|^2,\ p_1=\|x_1\|^2,\ w=\|x_S\|^2.
$$

三向量正交且 $p_0+p_1+w=1$。旗标 $j$ 的差输出是 $\epsilon(|x_j\rangle\langle x_S|+|x_S\rangle\langle x_j|)$，其迹范数为 $2\epsilon\sqrt{p_jw}$，包括任一向量为零的端点。两块合计满足

$$
2\epsilon\sqrt w(\sqrt{p_0}+\sqrt{p_1})
\le2\epsilon\sqrt{2w(1-w)}\le\sqrt2\epsilon=U_0.
$$

凸性涵盖所有混合态，引理 2.3 涵盖任意复算符和有限参考。上面的 $\psi_*$ 又达到 $U_0$，故中点的完整菱形误差恰为 $U_0$；整个面上 $h$ 的下界给出 (3.28) 的最小值。最后

$$
U_0-L=
\frac{(\sqrt2-1)(41-24\sqrt2)}{\sqrt2(41+24\sqrt2)}>0,
\tag{3.29}
$$

因为 $\sqrt2<3/2$ 使 $24\sqrt2<36<41$。这同样给出完整的符号严格比较。$\square$

**定理 3.10（非有效的统一严格间隙与定性稳定性）。** 在命题 3.6 的同一个紧外部松弛上定义

$$
B(\mathcal T)=\max\{b(\mathcal T),h(\mathcal T)\},\qquad
\beta_{\rm joint}=\min_{\mathcal T\in\mathcal C}B(\mathcal T),\qquad
\delta_{\rm joint}=\beta_{\rm joint}-L.
\tag{3.30}
$$

则 $\delta_{\rm joint}>0$，且对每个实际有限深度、几乎必然终止及闭包模拟器，

$$
\|\mathcal J_\theta-\mathcal T\|_\diamond
\ge\beta_{\rm joint}=L+\delta_{\rm joint}>L
\qquad(\theta\in\mathbb R).
\tag{3.31}
$$

(3.30) 是明确的有限维紧变分定义；这里没有求解该优化，也没有给出 $\delta_{\rm joint}$ 的数值、显式正闭式下界或有效稳定模量。

证明。先在规范坐标中。命题 3.6 给出整个 $\mathcal C$ 上 $\mathcal G\le65$，所以 $b\ge L$，进而 $B\ge L$。$b$ 连续，$h$ 连续，$\mathcal C$ 非空且紧，故 (3.30) 的最小值由某个 $\mathcal T^\circ\in\mathcal C$ 取到。若 $\beta_{\rm joint}=L$，则

$$
L\le b(\mathcal T^\circ)\le B(\mathcal T^\circ)=L.
$$

于是 $\mathcal G(\mathcal T^\circ)=65$。定理 3.7 迫使它位于整个已分类的面中，引理 3.9 却给出 $B(\mathcal T^\circ)\ge h(\mathcal T^\circ)\ge U_0>L$，矛盾。因此 $\beta_{\rm joint}>L$。这排除的是趋近 $L$ 的全部实际通道序列，而不只是若干已展示的协议在 $L$ 处不取等。

对同一个实际通道，$b$ 来自输入 $\psi_\rho$ 及输出二值支撑测量，$h$ 来自输入 $\psi_*$ 的完整输出；两者均不超过同一个完整菱形误差。由实际类包含在 $\mathcal C$ 中，

$$
\|\widehat{\mathcal J}-\mathcal T\|_\diamond
\ge B(\mathcal T)\ge\min_{\mathcal C}B=\beta_{\rm joint}.
$$

较大的外部松弛上的最小值给出实际问题的下界，方向并未反转，也未声称松弛极小者可实施。角度为 $\theta$ 时，支撑测试用 (3.15)，相干测试输入为 $D_\theta^\dagger\psi_*$；用按旗标的输出坐标幺正消去 $T_j$ 后得到相同的两个读数。引理 2.1–2.2 因而把同一个正数传到所有角度与三个实际类。取共同下确界得到 $d_*\ge L+\delta_{\rm joint}>L$。

还可给出等价的定性稳定说明。令 $m=(L+U_0)/2$，则存在 $\eta>0$ 使

$$
\mathcal T\in\mathcal C,\quad \mathcal G(\mathcal T)>65-\eta
\quad\Longrightarrow\quad h(\mathcal T)>m.
\tag{3.32}
$$

否则可选支撑分数趋向六十五、却有 $h\le m$ 的序列；紧性给出收敛子列，其极限支撑极大且 $h\le m<U_0$，与定理 3.7 和引理 3.9 矛盾。把通道分为 $\mathcal G\le65-\eta$ 与其补集，分别使用 $b\ge L+2\eta/N^2$ 与 $h>m$，得到

$$
B(\mathcal T)\ge L+
\min\left\{\frac{2\eta}{N^2},\frac{U_0-L}{2}\right\}>L.
\tag{3.33}
$$

这里只给出正间隙的形式，未给出 $\eta$ 的有效取值。证书没有求出 $\beta_{\rm joint}$，没有匹配倾斜上界，也没有识别原问题的最优实际仪器。它所增加的是整个支撑面与相干测试之间的统一分离；已经精确的单一支撑值本身没有被收紧。$\square$

## 4. 一次倾斜完整 PVM 的实际五维实现

**定义 4.1（精确参数及完整控制）。** 暂取 $0<\tau\le1/100$，最终选择 $\tau_0=1/10000$。定义

$$
c=\sqrt{1-\tau},\quad \alpha=\sqrt\tau,\quad k=2\sqrt2,\quad
d=\sqrt{1+7\tau},\quad h=\frac{1-\tau}{d},\quad b=\frac{k\tau}{d}.
\tag{4.1}
$$

这些是精确符号控制规格。取 $f=e_1,g=e_3$，使 $(f,g)$ 是 $QH$ 的正交基。置

$$
\begin{gathered}
r=cs+\alpha f,\quad w=cf-\alpha s,\qquad
R_0=P+|r\rangle\langle r|,\quad R_1=|g\rangle\langle g|+|w\rangle\langle w|,\\
y=(cf-k\alpha s)/d,\qquad \zeta=(k\alpha f+cs)/d,\\
U_0=P+|g\rangle\langle g|+|s\rangle\langle r|+|f\rangle\langle w|,\\
U_1=P+|g\rangle\langle g|+|y\rangle\langle w|+|\zeta\rangle\langle r|.
\end{gathered}
\tag{4.2}
$$

**命题 4.2（实际 PVM、全五维幺正及无损分支）。** $\{R_0,R_1\}$ 是秩三、二的完整正交 PVM，$U_0,U_1$ 是全五维幺正。测量后按结果 $i$ 施加 $U_i$ 并报告 $i$，其末端矩阵为

$$
L_0=P+|s\rangle\langle r|,\qquad
L_1=|g\rangle\langle g|+|y\rangle\langle w|,
\qquad \sum_iL_i^\dagger L_i=I_5.
\tag{4.3}
$$

证明。$c^2+\alpha^2=1$ 使 $(r,w)$ 为 $\operatorname{span}\{s,f\}$ 的正交基，与 $PH$ 及 $g$ 正交。因此 $R_0R_1=0$，$R_0+R_1=I_5$。又有 $d^2=c^2+k^2\alpha^2$，故 $(y,\zeta)$ 也是同一平面的正交基。$U_0$ 固定 $PH$ 和 $g$，把 $(r,w)$ 送到 $(s,f)$；$U_1$ 固定前三个方向，把 $(w,r)$ 送到 $(y,\zeta)$。每个都是完整正交基之间的映射，故两个方向的幺正恒等式均成立。

更显式地，在整个 $H$ 的有序基 $(e_0,e_4,g,s,f)$ 中，

$$
U_0=I_3\oplus\begin{pmatrix}c&\alpha\\-\alpha&c\end{pmatrix},\qquad
U_1=I_3\oplus\frac1d\begin{pmatrix}
c^2+k\tau&(1-k)c\alpha\\(k-1)c\alpha&c^2+k\tau
\end{pmatrix}.
\tag{4.4}
$$

第二个二维块的列正交，其平方列范数的分子为

$$
(c^2+k\tau)^2+(k-1)^2c^2\tau
=(c^2+\tau)(c^2+k^2\tau)=d^2.
$$

于是对未被选中子空间的作用也已完全指定。乘以 $R_i$ 即得 (4.3)；$L_i^\dagger L_i=R_i$，所以两结果全部保留并严格迹保持。展开还得到

$$
\begin{aligned}
L_0&=P+cS+\alpha|s\rangle\langle f|,\\
L_1&=Q+(h-1)|f\rangle\langle f|+bS
-\frac{c\alpha}{d}|f\rangle\langle s|
-\frac{kc\alpha}{d}|s\rangle\langle f|.
\end{aligned}
\tag{4.5}
$$

这里不需要任意 CPTP 后处理或丢弃结果。$\square$

**定义 4.3（独立群混合的操作序列）。** 从紧群

$$
\mathcal G_0=U(PH)\times U(QH)\times U(SH)
$$

的归一化 Haar 分布独立抽取 $V$，另抽取独立公平位 $\varepsilon\in\{0,1\}$，令 $W=VF^\varepsilon$。每次运行依次施加 $W^\dagger$、测量 (4.2) 的完整 PVM、施加实际条件幺正 $U_i$、施加 $W$，报告 $j=i\mathbin\oplus\varepsilon$。旗标 $j$ 上的末端矩阵为

$$
W L_{j\mathbin\oplus\varepsilon}W^\dagger.
\tag{4.6}
$$

平均所得仪器记为 $\widehat{\mathcal T}_\tau$。这是输入独立的实际协议混合，每个成员均只用原五维寄存器。对原始目标，末端再按报告旗标施加 $T_j$，并在最前施加 $D_\theta$，得到

$$
\mathcal T_{\tau,\theta}
=\left(\bigoplus_j\operatorname{Ad}_{T_j}\right)
\circ\widehat{\mathcal T}_\tau\circ\operatorname{Ad}_{D_\theta}.
\tag{4.7}
$$

$F$ 正规化 $\mathcal G_0$ 并交换 $P,Q$。群混合因此同时包含块幺正对称性与旗标交换对称性；$V$ 与 $H_j$ 对易，$FH_jF=H_{1-j}$，所以规范目标 $\widehat{\mathcal J}$ 具有同一协变性。这是对具体可实现协议的混合，不以抽象对称通道的可实现性作前提。

## 5. 实际混合的完整复通道

**定理 5.1（精确平均与效应）。** 定义实系数

$$
\begin{gathered}
A=\frac{1+h+(h-1)^2/6}{2},\qquad B=\frac{(h-1)^2}{12},\qquad
C=\frac c2+\frac{b(1+h)}4,\qquad D=\frac{1-\tau+b^2}{2},\\
E=\frac\tau4,\qquad F_c=\frac{(1-\tau)\tau}{4(1+7\tau)},\qquad G=8F_c.
\end{gathered}
\tag{5.1}
$$

$F_c$ 是系数，与反射矩阵 $F$ 不同。对所有复矩阵 $X\in M_5$，旗标 $j$ 的精确操作为

$$
\begin{aligned}
\widehat{\mathcal T}_{\tau,j}(X)
={}&A P_jXP_j+B\operatorname{Tr}(P_jX)P_j
 +C(P_jXS+SXP_j)+DSXS\\
 &+E\operatorname{Tr}(P_{1-j}X)S
 +F_c\operatorname{Tr}(SX)P_j
 +G\operatorname{Tr}(P_jX)S.
\end{aligned}
\tag{5.2}
$$

并有

$$
A+2B+E+G=1,\qquad D+2F_c=1/2,
\tag{5.3}
$$

其旗标 $j$ 的效应为 $(1-E)P_j+EP_{1-j}+S/2$。

证明。先不交换块与旗标，只平均 $V$。块间独立相位使 (4.5) 第一行的对角块与 $|s\rangle\langle f|$ 之间交叉项消失。$Vf$ 在复二维 $QH$ 单位球上均匀，故 $\mathbb E|f\rangle\langle f|=Q/2$。未交换的旗标零操作为

$$
\operatorname{Ad}_{P+cS}(X)+\frac\tau2\operatorname{Tr}(QX)S.
\tag{5.4}
$$

对旗标一，记 $H_f=|f\rangle\langle f|$。复二维四阶矩为

$$
\mathbb E(H_fXH_f)=\frac{QXQ+\operatorname{Tr}(QX)Q}{6}.
\tag{5.5}
$$

具体推导如下。独立坐标相位杀去不匹配的指标项。设 $m_4=\mathbb E|f_1|^4$，$m_{22}=\mathbb E|f_1|^2|f_2|^2$。单位范数与坐标交换给出 $m_4+m_{22}=1/2$。把第一坐标换成 $(f_1+f_2)/\sqrt2$ 的幺正不变性给出 $m_4=m_4/2+m_{22}$，所以 $m_4=1/3,m_{22}=1/6$。这些匹配矩分别给出 $X$ 的同指标与异指标项，逐矩阵元即为 (5.5)。所用的是复球面，且没有假设 $X$ 为实、Hermitian 或正矩阵。

将 $L_1$ 的对角块 $Q+(h-1)H_f+bS$ 与两条非对角 dyad 分开。相对块相位使前者与后两者的交叉项消失；两条 dyad 的互交叉项带有两倍相对相位，也消失。令 $t=h-1$，(5.5) 给出对角块平均在 $QXQ$ 上的系数 $1+t+t^2/6=h+t^2/6$，在 $\operatorname{Tr}(QX)Q$ 上的系数 $t^2/6$。$Q$–$S$ 交叉系数为 $b(1+t/2)=b(1+h)/2$，$SXS$ 系数为 $b^2$。两条 dyad 的平方项分别为

$$
\frac{c^2\tau}{2d^2}\operatorname{Tr}(SX)Q,
\qquad \frac{k^2c^2\tau}{2d^2}\operatorname{Tr}(QX)S.
$$

这些项穷尽了 $L_1XL_1^\dagger$ 的平均。现在把 (5.4) 与块、旗标交换后的旗标一操作各取一半，即得到 (5.1)–(5.2) 的旗标零；另一个旗标相同地交换 $P,Q$。因 $k^2=8$，最后两系数之比为八。每个系数来自同一组实际 $L_0,L_1$，而不是来自独立的可行松弛。

也可直接核对迹：$A+2B=(3+h^2)/4$，且

$$
\begin{aligned}
A+2B+E+G
 &=\frac{3+\tau+(c^4+8c^2\tau)/d^2}{4}
 =\frac{3+\tau+c^2}{4}=1,\\
D+2F_c
 &=\frac{c^2+(8\tau^2+c^2\tau)/d^2}{2}
 =\frac{c^2+\tau}{2}=1/2,
\end{aligned}
$$

其中 $d^2=c^2+8\tau$。对 (5.2) 取迹得到所述效应。完全正性已由实际 Kraus 混合保证，(5.3) 再次保证归一化。所有推导是复线性恒等式，因而也在张量任意恒等参考后成立。$\square$

## 6. 覆盖任意参考及复测试的精确误差公式

**引理 6.1（统一符号与行列式条件）。** 对 $0<\tau\le1/100$，置

$$
a=1-A-B/2=\frac{1-h}{2}-\frac{(1-h)^2}{8},\qquad
\beta=2F_c,\qquad \delta=q-C.
\tag{6.1}
$$

则

$$
0\le a\le9\tau/4,\quad 0\le\beta\le\tau/2,\quad
\delta>1/8,\quad \delta^2>a\beta.
\tag{6.2}
$$

证明。凸性给出 $1/d\ge1-7\tau/2$，而 $0<h\le1$。因此

$$
h\ge(1-\tau)(1-7\tau/2)
=1-9\tau/2+7\tau^2/2\ge1-9\tau/2.
$$

令 $x_h=1-h$，则 $0\le x_h\le9\tau/2<4$，所以 $a=x_h/2-x_h^2/8$ 介于零与 $9\tau/4$。$\beta=(1-\tau)\tau/[2(1+7\tau)]$ 给出另一界。由 $c,h\le1,d\ge1$ 有 $C\le1/2+\sqrt2\tau$，所以用可由平方检验的 $q>2/3$、$\sqrt2<3/2$ 得到

$$
\delta>\frac16-\frac{3}{200}=\frac{91}{600}>\frac18.
$$

最后

$$
a\beta\le9\tau^2/8\le9/80000<1/64<\delta^2.
$$

这些都是整个参数区间的有限不等式。$\square$

**定理 6.2（显示族的精确菱形范数）。** 对 $0<\tau\le1/100$，定义 $p=(1-\sigma)/2$ 及

$$
\Phi_\tau(\sigma)
=2\left[ap+\beta\sigma+
\sqrt{(ap-\beta\sigma)^2+4\delta^2p\sigma}\right],\qquad 0\le\sigma\le1.
\tag{6.3}
$$

则

$$
\|\mathcal J_\theta-\mathcal T_{\tau,\theta}\|_\diamond
=\|\widehat{\mathcal J}-\widehat{\mathcal T}_\tau\|_\diamond
=\max_{0\le\sigma\le1}\Phi_\tau(\sigma).
\tag{6.4}
$$

这是此具体平均仪器的精确误差表达式，不是所有允许协议的最优值公式。

证明。记 $\Delta=\widehat{\mathcal J}-\widehat{\mathcal T}_\tau$。对密度 $\varrho$，以任意纯化定义

$$
f_\Delta(\varrho)=\|(\Delta\otimes\operatorname{id})(|\psi_\varrho\rangle\langle\psi_\varrho|)\|_1.
$$

纯化间的参考等距映射只添加零奇异值，故此定义无歧义。此函数关于 $\varrho$ 凹：若 $\varrho=\sum_\ell\lambda_\ell\varrho_\ell$，取公共有限参考中的纯化 $\psi_\ell$，则

$$
\Psi=\sum_\ell\sqrt{\lambda_\ell}\,\psi_\ell\otimes|\ell\rangle
$$

纯化 $\varrho$。对最后的参考标签退相干，将输出变为加权分量输出的直和；退相干是有限个幺正共轭的平均，压缩迹范数。因此

$$
f_\Delta(\varrho)\ge\sum_\ell\lambda_\ell f_\Delta(\varrho_\ell).
\tag{6.5}
$$

$\Delta$ 对块幺正和同时交换 $P,Q$、旗标的群作用协变，所以 $f_\Delta$ 在该群的输入轨道上不变。群平均后的密度恰为

$$
\varrho_\sigma=\frac{1-\sigma}{4}(P+Q)+\sigma S,
\qquad \sigma=\operatorname{Tr}(S\varrho).
\tag{6.6}
$$

有限维 Hermitian 矩阵空间中，紧轨道的凸包紧，群平均可表示为有限个轨道点的凸组合；(6.5) 因而已经足够，不需要无限维参考。得出 $f_\Delta(\varrho_\sigma)\ge f_\Delta(\varrho)$。任何有限参考上的纯输入 Schmidt 秩至多五，其输出范数等于某个五维参考纯化的值；混合输入由凸性不能超过纯输入最大值。因此 (6.6) 覆盖所有归一化态输入及所有有限参考的上确界。

取 (6.6) 的纯化

$$
\psi_\sigma=\sqrt{p/2}\sum_{i\in\{0,1,3,4\}}e_i\otimes e_i
+\sqrt\sigma\,s\otimes s.
$$

在旗标 $j$ 中，令 $v_j=|P_j\rangle\!\rangle/\sqrt2$、$v_S=|S\rangle\!\rangle$。目标分支向量为 $\sqrt p\,v_j+q\sqrt\sigma\,v_S$。用 (5.2) 相减，在 $\operatorname{span}\{v_j,v_S\}$ 上得到完整主块

$$
M_j=\begin{pmatrix}
ap&\delta\sqrt{p\sigma}\\
\delta\sqrt{p\sigma}&\beta\sigma
\end{pmatrix}.
\tag{6.7}
$$

特别是 $B$ 项在 $v_j$ 上也有贡献 $Bp/2$，故第一项是 $a=1-A-B/2$。第二项用 $q^2-D=1/2-D=2F_c$。除主块外，所有非零谱如下，各空间相互正交并与主块正交：

| 子空间 | 特征值 | 重数 |
| --- | --- | --- |
| $P_jH_{\rm out}\otimes P_jH_{\rm ref}$ 中 $v_j$ 的正交补 | $-Bp/2$ | $3$ |
| $P_jH_{\rm out}\otimes SH_{\rm ref}$ | $-F_c\sigma$ | $2$ |
| $SH_{\rm out}\otimes P_jH_{\rm ref}$ | $-Gp/2$ | $2$ |
| $SH_{\rm out}\otimes P_{1-j}H_{\rm ref}$ | $-Ep/2$ | $2$ |

每旗标的 $25$ 维空间还剩 $14$ 个零特征值；退化端点可以有更多零特征值。由 (5.3)，

$$
a=3B/2+E+G,
$$

故这些次块的绝对迹之和为 $ap+\beta\sigma$。主块特征值为

$$
\lambda_\pm=\frac{ap+\beta\sigma\pm
\sqrt{(ap-\beta\sigma)^2+4\delta^2p\sigma}}2.
$$

引理 6.1 给出 $\det M_j=(a\beta-\delta^2)p\sigma<0$，只要 $0<\sigma<1$。因此两特征值异号，其绝对值和为根式。端点 $\sigma=0,1$ 时主块为非负对角块，同一个根式仍给出迹范数。两个旗标谱相同，于是总范数为 (6.3)。特别地 $\Phi_\tau(0)=2a$、$\Phi_\tau(1)=4\beta$；两个端点没有被排除。连续性给出闭区间上的最大值。

最后，$\Delta$ 保持伴随，引理 2.3 的 Hermitian 双参考块与 Jordan 分解把已证的所有归一化态及参考上界扩展到 (1.2) 的任意复测试，给出 $\max_\sigma\Phi_\tau(\sigma)$ 的菱形上界。反之，每个 $\psi_\sigma$ 本身都是允许的菱形范数测试。于是规范目标的等号成立；引理 2.1 把它传给原始角度目标。所有证明中的纯化与参考操作只服务于范数计算，不是模拟器的附加能力。$\square$

## 7. 全区间不等式及严格有理证书

**定理 7.1（统一上界与选定参数）。** 对 $0<\tau\le1/100$，

$$
\max_{0\le\sigma\le1}\Phi_\tau(\sigma)
\le1-\frac1{\sqrt2}
-\frac{3-2\sqrt2}{8}\tau+79\tau^2.
\tag{7.1}
$$

特别地，实际参数 $\tau_0=1/10000$ 满足

$$
\|\mathcal J_\theta-\mathcal T_{\tau_0,\theta}\|_\diamond
<1-\frac1{\sqrt2}-\frac1{1000000}
\qquad(\theta\in\mathbb R).
\tag{7.2}
$$

证明。除引理 6.1 的界外，还需更精确的 $C$ 下界。在整个参数区间，

$$
c\ge1-\tau/2-\tau^2.
\tag{7.3}
$$

其右端非负，且以 $R_c=1-\tau/2-\tau^2$ 记之，有

$$
(1-\tau)-R_c^2=\tau^2(7/4-\tau-\tau^2)\ge0,
$$

因为 $\tau+\tau^2\le101/10000<7/4$；平方即可证明 (7.3)。$1/d\ge1-7\tau/2$ 已由凸性得到。以下乘法因子的下界均非负，故

$$
\frac{1+h}{d}\ge(2-9\tau/2)(1-7\tau/2)
=2-23\tau/2+63\tau^2/4\ge2-23\tau/2.
$$

代入 $C=c/2+k\tau(1+h)/(4d)$ 得

$$
C\ge\frac12+(\sqrt2-1/4)\tau
-\left(\frac12+\frac{23\sqrt2}{4}\right)\tau^2
\ge\frac12+(\sqrt2-1/4)\tau-10\tau^2.
\tag{7.4}
$$

最后用 $\sqrt2<3/2$ 使括号小于 $73/8<10$。记 $\epsilon_0=q-1/2$，于是

$$
\delta\le\epsilon_0-(\sqrt2-1/4)\tau+10\tau^2.
\tag{7.5}
$$

现在固定任意 $\sigma\in[0,1]$，不预设最大值所在位置。令

$$
x=\sigma-1/2,\quad u=a(1-\sigma)/2,\quad v=\beta\sigma,
\quad M=a/2+\beta,\quad \nu=\beta-a/2.
$$

则 $2(u+v)=M+2\nu x$，根式中的数为

$$
(u-v)^2+\delta^2/2-2\delta^2x^2\ge0.
$$

在正点 $\delta^2/2$ 对平方根使用凹函数切线界，得到

$$
2\sqrt{(u-v)^2+\delta^2/2-2\delta^2x^2}
\le\sqrt2\delta+\frac{\sqrt2}{\delta}(u-v)^2-2\sqrt2\delta x^2.
$$

$u,v\ge0$，且 $u\le a/2,v\le\beta$，所以 $|u-v|\le M$。配方又给出对所有实数 $x$ 成立的界

$$
2\nu x-2\sqrt2\delta x^2\le\frac{\nu^2}{2\sqrt2\delta}.
$$

因此，包括两个端点在内一致有

$$
\Phi_\tau(\sigma)\le\sqrt2\delta+M
+\frac{\sqrt2}{\delta}M^2+\frac{\nu^2}{2\sqrt2\delta}.
\tag{7.6}
$$

由引理 6.1，$M\le13\tau/8<2\tau$，$|\nu|\le M<2\tau$。再用 $\delta>1/8$ 与 $1<\sqrt2<3/2$，逐项得到

$$
\frac{\sqrt2}{\delta}M^2\le48\tau^2,\qquad
\frac{\nu^2}{2\sqrt2\delta}\le16\tau^2.
$$

式 (7.5) 给出

$$
\sqrt2\delta\le1-q-(2-\sqrt2/4)\tau+15\tau^2.
$$

把这些界和 $M\le13\tau/8$ 代入 (7.6)，用

$$
2-\sqrt2/4-13/8=(3-2\sqrt2)/8,
\qquad 15+48+16=79
$$

即得对所有 $\sigma$ 成立的 (7.1)。它是有限、统一的上界，不含小参数余项，也不是数值求最大值。

最后给出完全有理的严格余量：

$$
71^2=5041>5000=2\cdot50^2
\quad\Longrightarrow\quad \sqrt2<71/50
\quad\Longrightarrow\quad \gamma:=\frac{3-2\sqrt2}{8}>\frac1{50}.
$$

对实际选择 $\tau_0=1/10000$，

$$
79\tau_0^2<100\tau_0^2=\tau_0/100,
\qquad
-\gamma\tau_0+79\tau_0^2
<-\tau_0/50+\tau_0/100
=-\frac1{1000000}.
$$

由定理 6.2 得 (7.2)。该严格证书只在选定参数作上述断言，不声称整个参数区间都改进。构造属于有限深度类，故其误差给出 $d_*$ 的严格上界；定理 3.10 在定理 3.4 的基础上给出严格高于 $L$ 的统一下界，引理 2.1–2.2 给出角度和三个类的共同量词，完成定理 1.4。$\square$

## 8. 精确支撑、未决距离与资源边界

**约定 8.1（已有具体误差与较小任务）。** 源甲定理 19.1 已证明：在角度零，公平混合 PVM $\{P+S,Q\}$ 与 $\{P,Q+S\}$，然后按旗标施加 $T_j$，所得具体模拟器具有精确误差 $1-1/\sqrt2$。本文直接复用这个已有精确误差，不把它作为新定理或最优性前提。定义 4.1、4.3 及命题 4.2 在连续端点 $\tau=0$ 退化为其规范版本；系数为 $A=1,B=0,C=D=1/2,E=F_c=G=0$。定理 7.1 证明这个具体旧候选在原菜单中并非全局最优，与源甲把精确 $d_*$ 留作未决问题相容。

新的效应是 $(1-E)P_j+EP_{1-j}+S/2$，因此倾斜构造允许小的旗标统计误差。原完整仪器逼近问题没有要求统计必须精确，不能把精确统计静默加入优化限制。源甲 §20 中精确实现统计、丢旗标的平均通道和限制到 $R$ 的编码仪器仍是三个较小任务；它们不提供 (1.1) 的全输入、带旗标且保留量子输出的模拟。

定理 3.3 的确定单 PVM 是另一个实际协议，其作用是精确达到支撑泛函上界。公平混合与倾斜构造则承担距离上界；这三种作用不能互换。式 (3.16) 的 $L$ 是精确支撑测试给出的基础下界；定理 3.10 进一步给出 $L+\delta_{\rm joint}>L$。较弱的 $2/9$ 只由 $L>1/4>2/9$ 作为数值推论保留。公平混合正是整个支撑面中使完整距离最小的中点，其误差 $U_0$ 仍严格大于倾斜构造的误差。

**命题 8.2（受限族和闭包的存在性）。** 限制族的数

$$
d_{\rm family}=\min_{0\le\tau\le1/100}\max_{0\le\sigma\le1}\Phi_\tau(\sigma)
\tag{8.1}
$$

有定义并在该实际族中取到，其中端点按连续延伸解释。$\mathfrak S_{\rm cl}$ 中也存在取到 $d_*$ 的通道。这两个存在性结论均不识别 $d_*$ 的值，也不保证全局距离极小者具有有限深度或几乎必然终止实现。

证明。所有系数在所述紧参数矩形上连续；引理 6.1 的正 $\delta$ 条件在 $\tau=0$ 也成立，$a=\beta=0$，故定理 6.2 的谱证明与范数公式连续延伸。连续函数在紧区间上的最大值关于参数连续，因此 (8.1) 有最小值。每个参数对应定义 4.1、4.3 及命题 4.2 的实际协议，包括上述零端点，所以这里确为族内取到，而非松弛可行性。

另一方面，固定有限输入输出维度的归一化通道的 Choi 矩阵为正半定、具有固定偏迹及固定迹，因而构成有限维紧集；经典旗标的分块限制也是闭的。非空闭子集 $\mathfrak S_{\rm cl}$ 因而紧，连续的菱形距离在其中取到最小值。引理 2.2 识别该最小值与三个类的共同下确界。闭包中抽象存在一个通道，不提供可停止的协议，也不证明 $\mathfrak S_{\rm as}=\mathfrak S_{\rm cl}$。$\square$

**定义 8.3（已排除的端点与仍为 OPEN 的精确距离义务）。** 原目标保持为 (1.3) 的全输入、带旗标、保留五维量子输出的精确 $d_*$，以及实际有限或几乎必然终止取到问题。本文已证明 $d_*\ge L+\delta_{\rm joint}>L$，所以 $d_*=L$ 以及合法协议误差趋向 $L$ 均已被排除。尚未求出 $\delta_{\rm joint}$ 的数值、有效正下界或 (3.32) 的有效模量；(3.30) 的极小者也未被识别或证明可实施。

倾斜族的全局最优性仍为 OPEN。例如，一个足够但尚未证明的义务是

$$
\|\widehat{\mathcal J}-\mathcal T\|_\diamond\ge d_{\rm family}
\quad\text{对每个实际 }\mathcal T\in\mathfrak S_{\rm fin}.
\tag{8.2}
$$

这里不断言该义务为真；其他首次 PVM 方向及反馈后代仍可产生不同候选。本文没有求出选定参数误差的一变量最大值的闭式值、最佳 $\tau$、完整可实现通道集合或最优自适应策略，也没有给出与严格下界匹配的实际协议。Schmidt 数、正确效应及一般 CP 后代松弛中的可行点都不能替代实际实现。

定理 3.3 解决的是所选线性支撑泛函的全局最大值，定理 3.7 进一步给出紧外部松弛中整个极大面的全部通道；不是逐个秩分拆的最优值表。命题 3.8 用同一个合法中点证明，单一支撑证书加 $S$ 的完整输出证书仍只能给出 $L$。引理 3.9 识别面上的精确最小误差 $U_0$，定理 3.10 再以整个面的相干约束和紧性得到非有效正间隙。它们没有把分别可达的边缘读数当作共同实现。

精确支撑值、面上最小误差、严格但未求值的全协议下界、具体倾斜族的精确误差公式及严格有理上界分别承担不同结论。原全局精确 $d_*$、匹配的最优性证书，以及有限深度和几乎必然终止类是否取到该共同下确界，均仍为 OPEN。命题 8.2 的闭包极小者只是一条闭包通道，不保证任一实际停止类中的取到，也不证明 $\mathfrak S_{\rm as}=\mathfrak S_{\rm cl}$。

**约定 8.4（实际模型、操作资源与恢复任务边界）。** 支撑最大者使用一次完整秩三/二 Lüders PVM；倾斜上界协议还使用输入独立的理想块幺正 Haar 随机性、一个独立公平位及固定有限次数的五维幺正。加上 $D_\theta$ 和按旗标的 $T_j$ 仍有统一有限深度。两结果与全部概率保留，末端输出仍是经典旗标和原五维寄存器。没有增加量子寄存器、能级、重置、非投影原语、任意 CPTP 后处理、参考读取或成功后选择。引理 3.2 及命题 3.6 的代数与 Choi 松弛只限制实际协议，并不授权其中的一般 CP 后处理；其紧性只用于方向正确的下界比较。

精确连续随机性与精确控制是该理想菜单允许的资源；本文不给出有限支持随机实现、有限精度、控制获取、校准、物理可实现性或总成本界。环境 $E$ 用于定义目标实际仪器，不是模拟菜单可调用的附加系统。源甲 §21 的张量辅助维度二、总维度十及直和总维度六属于分别扩大的菜单；本文未取得这些额外权限，也不混淆两种容量。

源甲 §§1–16 的重复标签恢复以编码输入 $R$ 和终端恢复为对象。其 §§23–25 进一步在同一编码恢复任务中采用带符号近格角 $\eta$、至多六值的经典排列状态及一次终端幺正，给出平均校正通道的误差界 $\min\{2,2n\delta^2/3\}$，其中 $\delta=\operatorname{dist}(\theta,(\pi/2)\mathbb Z)$。该任务实际取得每一步标签，只作中间经典更新，恢复的是编码 qutrit 及未读取参考；其有理角实例允许角度随有限时域和容差选择。六只计持续经典历史状态，不计标签取得、准备、通信、校准、精确控制或外给时域；误差界不作逐历史保证，也不提供固定非零角的任意长时域结论。本文的单次全输入距离界与这些编码终端恢复命题具有不同目标和量词，彼此不结算。

所有参考、纯化、Kraus 堆叠和范数证明中的退相干均是分析工具。普通证明不称为 kernel 验证，不据此提出经验机器学习、物理、全球优先权或原精确距离目标已经完成的主张。

**约定 8.5（固定来源身份与标准工具）。** 源甲为 *AURIC FIB environment instruments and terminal record memory*，全文 UTF-8 SHA-256 为 `1d1344bd0aa7df5107940e9126aed9321a5cf1c214d082980657b35c97b851a1`。本文引用该固定文本的定义 1.3、2.1、17.1–17.2、命题 17.3、定理 2.2、18.2、19.1 及 §§20–22；编码恢复的范围按 §§1–16、23–25 理解。引理 2.1 的实际矩阵与极分解、引理 2.2 的停止逼近，以及约定 8.1 的旧精确误差均由这些来源接口复用。

源乙提供的完整支撑极大面、同一通道的旗标与相干关系、合法中点反例及紧性严格间隙论证，是命题 3.6 至定理 3.10 所采用的数学内容。本文完整展开其证明；这些所供结果不被重命名为独立发现。

源甲约定 22.1 对秩权重、Schmidt 截断及仪器后处理的文献对应保留原有适用边界；本文不把其中低维充分性或更宽后处理权限转移到五维菜单。目标每个旗标操作的 Kraus 秩为一，而实际 Kraus 矩阵的矩阵秩为三，两者不同。共同右支撑引理中的一般矩阵族仅为必要外界，最终支撑取到另由实际 PVM 给出。

Cauchy–Schwarz、正平方根的迹微分、Rayleigh 极小极大原理、正交基补全、Haar 矩、Choi 正性、Carathéodory 定理、纯化、迹范数压缩、凸性和有限维紧性是标准中间工具。本文将它们用于明确实际矩阵的共同支撑与联合秩分拆、完整取等分类、相干分离及倾斜 PVM 的误差分析；这些应用和综合不自动构成一般机制的发现。本文没有外部文献真实性核验、全球新颖性或优先权结论。最终有 $L<d_*<1-1/\sqrt2-1/1000000$，更有 (3.30)–(3.31) 定义并证明的 $d_*\ge L+\delta_{\rm joint}>L$。精确支撑结论为 (3.8)，完整极大面为 (3.19)；原精确距离及实际取到保持定义 8.3 的 OPEN 边界。

## 追加锚（本行以下为增补区）
