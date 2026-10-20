# AURIC FIB：固定忠实三态的恢复缺陷平方根阶尖锐性

本文在一个固定的忠实量子比特三态族上，构造实际的两记录、保留量子比特仪器 $\mathcal N_t$，以及每个 $t$ 对应的一个共同完整输出 CPTP 解码器 $\mathcal R_t$。输入、维数和族大小都不随 $t$ 改变。在一个显式正区间上，同一实际实现满足

$$
0<G_t\le Ct^2,\qquad
\varepsilon_\star(\mathcal N_t)
\le\varepsilon(\mathcal R_t,\mathcal N_t)\le Q-ct,
\qquad C,c>0.
$$

因此，对任意 $\alpha>1/2$ 和任意有限实数 $K$，以实际缺陷为参数的统一下界 $\varepsilon_\star\ge Q-KG^\alpha$ 即使只要求在任意小的正缺陷邻域内成立，也会被这个固定族的实际路径反驳。结合既有的 $Q-\sqrt{12G}$ 下界，同一路径上的最优恢复间隙被夹在 $\sqrt G$ 的两个固定正常数倍之间。

本文给出可错的、未经执行的条件符号数学。经典基准的精确值及其达到方案直接复用[《零保真缺陷下的严格正经典恢复间隙》](AURIC_FIB_ZERO_DEFECT_CLASSICAL_RECOVERY_GAP.md)定理 2.1，完整量子输出上的稳健下界直接复用[《实际仪器保留量子输出的稳健恢复障碍》](AURIC_FIB_ROBUST_ACTUAL_QUANTUM_RECOVERY.md)定理 9.2。以下分别简称经典伴卷和稳健伴卷。本文的增量是实际弱仪器的共同相干解码构造、同时平衡三个误差的参数斜率、全区间余项以及固定族的指数反证，不是重做经典全局极小极大证明。

## 1. 固定输入、实际缺陷与恢复量词

**定义 1.1（固定忠实三态与半迹距离）。** 令 $A=B=\mathbb C^2$，记录空间为 $C_{\rm rec}=\mathbb C^2$，其基标记为 $+,-$。使用标准 Pauli 矩阵

$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\qquad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

写 $\rho(x,y,z)=(I_2+xX+yY+zZ)/2$，固定

$$
\begin{aligned}
\sigma_0&=\begin{pmatrix}1/2&1/4\\1/4&1/2\end{pmatrix}
          =\rho(u,0,0),\\
\sigma_+&=\begin{pmatrix}3/4&\sqrt3/8\\\sqrt3/8&1/4\end{pmatrix}
          =\rho(v,0,w),\\
\sigma_-&=\begin{pmatrix}1/4&\sqrt3/8\\\sqrt3/8&3/4\end{pmatrix}
          =\rho(v,0,-w),\qquad
u=w=\frac12,\quad v=\frac{\sqrt3}{4}.
\end{aligned}
\tag{1.1}
$$

这里 $\|H\|_1=\operatorname{Tr}\sqrt{H^\dagger H}$，误差使用半迹距离 $\frac12\|\rho-\sigma\|_1$。Bloch 向量差为 $q$ 时，差矩阵 $q\cdot(X,Y,Z)/2$ 的平方为 $|q|^2I_2/4$，故特征值为 $\pm|q|/2$，半迹距离为 $|q|/2$。

**引理 1.2（固定忠实性）。** 三个输入都是忠实密度矩阵，并有共同正下界

$$
\sigma_i\succeq\mu I_2,\qquad
\mu=\frac{4-\sqrt7}{8}>0.
\tag{1.2}
$$

证明。三态迹一。$\sigma_0$ 的 Bloch 长度为 $1/2$，所以特征值为 $3/4,1/4$；另外两个态的长度均为 $\sqrt{v^2+w^2}=\sqrt7/4$，所以特征值为 $(4+\sqrt7)/8,(4-\sqrt7)/8$。由于 $2<\sqrt7<4$，$\mu$ 严格正且小于 $1/4$，证明所述下界。后文借用的锚下界 $1/4$ 只属于 $\sigma_0$，不作为共同下界。$\square$

**定义 1.3（实际仪器和根保真缺陷）。** 一般的实际有限仪器写为

$$
\mathcal N(H)=\sum_x|x\rangle\langle x|\otimes\mathcal I_x(H),
\qquad
\mathcal I_x(H)=\sum_aK_{xa}HK_{xa}^\dagger,\qquad
E_x=\sum_aK_{xa}^\dagger K_{xa},\quad \sum_xE_x=I_A.
\tag{1.3}
$$

保留量子输出为 $B$，解码器取得全部实际记录 $x$；未记录的 $a$ 和丢弃环境不属于解码输入。对同一实际效应 $E$ 定义

$$
\begin{aligned}
p_i(x)&=\operatorname{Tr}(E_x\sigma_i),&
F_{ij}&=\|\sqrt{\sigma_i}\sqrt{\sigma_j}\|_1,\\
C_{ij}(E)&=\sum_x\sqrt{p_i(x)p_j(x)},&
\delta_{ij}(E)&=C_{ij}(E)-F_{ij},\\
G(E)&=\frac{\delta_{0+}(E)+\delta_{0-}(E)+\delta_{+-}(E)}3.
\end{aligned}
\tag{1.4}
$$

$F$ 是根保真度，不是其平方。经典与稳健伴卷所用的根保真测量表示保证各 $\delta_{ij}\ge0$。族的最优化缺陷

$$
\Delta=\inf_{F\text{ 为有限 POVM}}
\frac{C_{0+}(F)+C_{0-}(F)+C_{+-}(F)}3
-\frac{F_{0+}+F_{0-}+F_{+-}}3
\tag{1.5}
$$

与实际 $G(E)$ 不同；$0\le\Delta\le G(E)$。本族存在共同等号坐标测量，故 $\Delta=0$，但下文每个正 $t$ 的实际 $G_t$ 严格正。不能用 $\Delta$ 替换实际缺陷。

**定义 1.4（共同完整输出解码与经典基准）。** 对整个 $M(C_{\rm rec}\otimes B)$ 上到 $M(A)$ 的任意 CPTP 映射 $\mathcal R$，定义

$$
\varepsilon(\mathcal R,\mathcal N)
=\max_{i\in\{0,+,-\}}\frac12
\|\mathcal R\mathcal N(\sigma_i)-\sigma_i\|_1,
\qquad
\varepsilon_\star(\mathcal N)=
\inf_{\mathcal R\text{ 为共同完整输出 CPTP 映射}}
\varepsilon(\mathcal R,\mathcal N).
\tag{1.6}
$$

共同指 $\mathcal R$ 不依赖未知输入标签 $i$。误差比较的是全部实际分支平均后的重建。下确界包括所有这种 CPTP 解码器，不限于本文为取得上界而构造的分支酉操作。作为比较，定义

$$
Q=\inf_{\substack{(F_y)\text{ 任意有限 POVM}\\
\eta_y\text{ 为 }A\text{ 上任意密度矩阵}}}
\max_i\frac12
\left\|\sum_y\operatorname{Tr}(F_y\sigma_i)\eta_y-\sigma_i\right\|_1.
\tag{1.7}
$$

结果数任意有限，混合制备和零效应均允许。$Q$ 的优化是纯经典中介的数学比较任务；它不授权替换指定实际仪器。

## 2. 直接复用的精确经典基准

**来源接口 2.1（参数对应与既有结论）。** 经典伴卷定理 2.1 的参数在本文中是

$$
T=t_\star,\qquad b=c_\star=\sqrt{1-T^2},\qquad
e=u-T,\qquad d=d_\star=T-v,\qquad h=u-v=e+d.
\tag{2.1}
$$

$T$ 是 $(v,u)$ 中满足

$$
u-T=\sqrt{(T-v)^2+w^2(1-\sqrt{1-T^2})^2}
\tag{2.2}
$$

的唯一根。因此 $e,d,b,h$ 均严格正，$0<T<1/2$、$1/2<b<1$，并且

$$
e^2=d^2+w^2(1-b)^2.
\tag{2.3}
$$

本文的 $t$ 是仪器弱化参数，与常数 $T$ 不同；本文的 $h$ 是上述 Bloch 参数，不是稳健伴卷定义 4.1 的 Frobenius 块相干量。经典伴卷已经对 (1.7) 的全部有限方案证明

$$
Q=\frac e2>0.
\tag{2.4}
$$

其达到方案是坐标 PVM $P_\pm=(I_2\pm Z)/2$ 后制备

$$
\omega_\pm=\frac{I_2+TX\pm bZ}{2}.
\tag{2.5}
$$

两个制备态均为纯态，三个半迹误差都等于 $Q$。稳健伴卷接口 9.1 以相同的 $u=w=1/2,v=\sqrt3/4$ 重述了此结果。这里直接复用该全局精确值，不再证明其有限对称化、必要可行域或全局支撑下界。

**来源接口 2.2（实际输出的既有下界）。** 稳健伴卷定理 9.2 对固定三态 (1.1) 的每个实际有限仪器给出

$$
\varepsilon_\star(\mathcal N)\ge
\max\{0,Q-\sqrt{12G(E)}\}.
\tag{2.6}
$$

该结论允许任意有限结果数、任意有限维保留 $B$，且下确界取遍整个记录与量子联合输出上的所有共同 CPTP 解码器。其常数使用锚 $\sigma_0\succeq I_2/4$、其他态的上界 $\sigma_\pm\preceq I_2$，不是把 $1/4$ 误认作共同最小特征值。以下将 (2.6) 应用于同一实际路径，保持这些量词。

## 3. 两记录弱仪器的实际概率与精确缺陷

**定义 3.1（固定路径）。** 对 $0\le t<1/\sqrt2$，令

$$
a_t=\sqrt{1-t^2},\qquad k_t=1-2t^2,\qquad
K_+(t)=\begin{pmatrix}a_t&0\\0&t\end{pmatrix},\qquad
K_-(t)=\begin{pmatrix}t&0\\0&a_t\end{pmatrix},
\tag{3.1}
$$

并取实际仪器

$$
\mathcal N_t(H)=
|+\rangle\langle+|\otimes K_+(t)HK_+(t)^\dagger+
|-\rangle\langle-|\otimes K_-(t)HK_-(t)^\dagger.
\tag{3.2}
$$

每个记录恰有一个 Kraus 算子，没有被暗中保留的额外 Kraus 指标。

**引理 3.2（实际 CPTP 性与全部 Born 概率）。** (3.2) 是完整保留两记录和量子比特 $B$ 的实际 CPTP 仪器，其效应为

$$
E_+(t)=\operatorname{diag}(1-t^2,t^2),\qquad
E_-(t)=\operatorname{diag}(t^2,1-t^2).
\tag{3.3}
$$

全部实际概率为

$$
\begin{array}{c|cc}
 &p_i(+)&p_i(-)\\ \hline
0&1/2&1/2\\
+&3/4-t^2/2&1/4+t^2/2\\
-&1/4+t^2/2&3/4-t^2/2
\end{array}
\tag{3.4}
$$

证明。联合 Kraus 为 $|+\rangle\otimes K_+(t)$ 和 $|-\rangle\otimes K_-(t)$，因此完全正；其伴随乘积和为 $E_++E_-=I_2$，因此保迹。对 $\rho(x,y,z)$，由两个对角元 $(1+z)/2,(1-z)/2$ 得

$$
\operatorname{Tr}(E_\pm(t)\rho(x,y,z))=\frac{1\pm k_tz}{2}.
\tag{3.5}
$$

分别代入 $z=0,w,-w$ 就是 (3.4)。所有概率正且每行和一。$t=0$ 时是坐标 PVM 仪器；$0<t<1/\sqrt2$ 时两个效应的两个特征值均在 $(0,1)$，所以非投影。特别地，侧态的记录概率不同于锚，不能把该仪器解释为输入无关的公平历史。$\square$

**命题 3.3（实际根式、严格正性及统一二次上界）。** 令 $G_t=G(E(t))$、$r=t^2$。则

$$
\begin{aligned}
\delta_{0+}(t)=\delta_{0-}(t)
&=\frac{\sqrt{3-2r}+\sqrt{1+2r}-\sqrt3-1}{2\sqrt2},\\
\delta_{+-}(t)
&=\frac{\sqrt{3+4r-4r^2}-\sqrt3}{2},\\
G_t&=\frac13\left[
\frac{\sqrt{3-2r}+\sqrt{1+2r}-\sqrt3-1}{\sqrt2}
+\frac{\sqrt{3+4r-4r^2}-\sqrt3}{2}\right].
\end{aligned}
\tag{3.6}
$$

在整个 $0<t<1/\sqrt2$ 上有

$$
0<G_t\le Ct^2,\qquad
C=\frac{1/\sqrt2+1/\sqrt3}{3}>0.
\tag{3.7}
$$

还存在精确正极限

$$
\lim_{t\downarrow0}\frac{G_t}{t^2}
=\gamma,\qquad
\gamma=\frac{(1-1/\sqrt3)/\sqrt2+1/\sqrt3}{3}>0.
\tag{3.8}
$$

证明。稳健伴卷命题 9.3 给出固定根保真度

$$
F_{0+}=F_{0-}=\frac{\sqrt3+1}{2\sqrt2},\qquad
F_{+-}=\frac{\sqrt3}{2}.
\tag{3.9}
$$

这些值也由经典伴卷命题 1.3 的共同等号坐标测量及其概率得到。用 (3.4) 的实际概率，锚与任一侧态的经典根重叠为

$$
\sqrt{\frac12\left(\frac34-\frac r2\right)}
+\sqrt{\frac12\left(\frac14+\frac r2\right)}
=\frac{\sqrt{3-2r}+\sqrt{1+2r}}{2\sqrt2}.
$$

两个侧态的两项乘积相同，故它们的根重叠为

$$
2\sqrt{\left(\frac34-\frac r2\right)
\left(\frac14+\frac r2\right)}
=\frac{\sqrt{3+4r-4r^2}}2.
$$

减去 (3.9) 并平均，得到 (3.6)，没有换用比较测量。

把各缺陷视为 $r$ 的函数。当 $0<r<1/2$ 时，其导数分别为

$$
\frac{1/\sqrt{1+2r}-1/\sqrt{3-2r}}{2\sqrt2}>0,
\qquad
\frac{1-2r}{\sqrt{3+4r-4r^2}}>0.
\tag{3.10}
$$

第一式使用 $1+2r<3-2r$。两缺陷在 $r=0$ 为零，所以每个都严格正。

为取得全区间上界，先丢掉 $\sqrt{3-2r}-\sqrt3\le0$，再有理化，得到

$$
\delta_{0+}(t)\le
\frac{\sqrt{1+2r}-1}{2\sqrt2}
=\frac{r}{\sqrt2(\sqrt{1+2r}+1)}
\le\frac{r}{2\sqrt2}.
\tag{3.11}
$$

另一方面，$3+4r-4r^2\ge3$，故

$$
\delta_{+-}(t)
=\frac{2r(1-r)}{\sqrt{3+4r-4r^2}+\sqrt3}
\le\frac{r}{\sqrt3}.
\tag{3.12}
$$

两次 (3.11) 与一次 (3.12) 的平均就是 (3.7)，端点 $r=0$ 也成立。最后，(3.6) 的 $r$ 函数在零点可微且取零；把 (3.10) 的零点导数按同样权重平均，恰得 $\gamma$。因 $G_t=G_{\sqrt r}$、$r=t^2$，导数定义给出 (3.8)。$\sqrt3>1$ 使 $\gamma$ 严格正。所有根号取正实根，此处没有使用数值拟合或无余项级数。$\square$

## 4. 一个共同的完整输出相干解码器

**定义 4.1（固定正常数与共同变化参数）。** 使用 §2 的常数，令

$$
\begin{aligned}
\beta&=\frac{w^2(1-b)}b,&
A&=d+\beta T,&
\ell&=e+A=h+\beta T,\\
M&=\frac{2b(eu+vd)}{\ell},&
D&=\frac{b(hd+u\beta T)}{\ell},&
r_0&=\min\left\{\frac14,\frac{T}{2M}\right\}.
\end{aligned}
\tag{4.1}
$$

$e,d,b,h,\beta,A,\ell,M,D$ 都是严格正且有限的固定常数，因为每个分子、分母由已列正量相加或相乘组成，且 $1-b>0$。定义

$$
s_t=T-Mt,\qquad b_t=\sqrt{1-s_t^2}\qquad(0\le t\le r_0).
\tag{4.2}
$$

于是 $T/2\le s_t\le T<1/2$，从而 $1/2<b\le b_t\le1$。以下全部矩阵及导数在这个闭区间内有定义。一个以后要用的恒等式是

$$
bu-\frac M2
=\frac{b[u(e+A)-(eu+vd)]}{\ell}
=\frac{b[(u-v)d+u\beta T]}{\ell}=D>0.
\tag{4.3}
$$

**引理 4.2（完整酉矩阵及相位）。** 令

$$
\mathsf A_t=\sqrt{\frac{1+b_t}{2}},\qquad
\mathsf B_t=\frac{s_t}{\sqrt{2(1+b_t)}},
\qquad
U_+(t)=\begin{pmatrix}\mathsf A_t&-\mathsf B_t\\
\mathsf B_t&\mathsf A_t\end{pmatrix},\quad
U_-(t)=\begin{pmatrix}\mathsf A_t&\mathsf B_t\\
-\mathsf B_t&\mathsf A_t\end{pmatrix}.
\tag{4.4}
$$

它们是完整的复酉矩阵，满足 $U_-=U_+^\dagger$，并且
$U_+|0\rangle$、$U_-|1\rangle$ 的 Bloch 向量分别是 $(s_t,0,b_t)$、$(s_t,0,-b_t)$。

证明。由 $s_t^2=1-b_t^2$ 得

$$
\mathsf B_t^2=\frac{1-b_t}{2},\qquad
\mathsf A_t^2+\mathsf B_t^2=1,\qquad
2\mathsf A_t\mathsf B_t=s_t.
\tag{4.5}
$$

每个矩阵的两列长度一且内积零，行列式为一，证明酉性。占用列明确为 $(\mathsf A_t,\mathsf B_t)^{\mathsf T}$ 和 $(\mathsf B_t,\mathsf A_t)^{\mathsf T}$；纯实向量 $(a,b)^{\mathsf T}$ 的 Bloch 向量是 $(2ab,0,a^2-b^2)$，代入即得断言。另两列的符号也已在 (4.4) 中固定，因此并未把一个只在占用向量上定义的制备擅自当成有相干扩张的操作。$t=0$ 时这两个占用列的纯态正是 (2.5)。$\square$

**定义 4.3（整个联合代数上的解码器）。** 按基
$(|+\rangle|0\rangle,|+\rangle|1\rangle,|-\rangle|0\rangle,|-\rangle|1\rangle)$，定义两个 $2\times4$ 矩形 Kraus 算子

$$
\begin{aligned}
L_+(t)&=U_+(t)(\langle+|\otimes I_2)
=\begin{pmatrix}\mathsf A_t&-\mathsf B_t&0&0\\
\mathsf B_t&\mathsf A_t&0&0\end{pmatrix},\\
L_-(t)&=U_-(t)(\langle-|\otimes I_2)
=\begin{pmatrix}0&0&\mathsf A_t&\mathsf B_t\\
0&0&-\mathsf B_t&\mathsf A_t\end{pmatrix}.
\end{aligned}
\tag{4.6}
$$

令

$$
\mathcal R_t(Y)=L_+(t)YL_+(t)^\dagger+L_-(t)YL_-(t)^\dagger
=U_+(t)Y_{++}U_+(t)^\dagger+
U_-(t)Y_{--}U_-(t)^\dagger,
\tag{4.7}
$$

其中 $Y_{xx}=(\langle x|\otimes I_2)Y(|x\rangle\otimes I_2)$。

**命题 4.4（完整 CPTP 性和精确仿射重建）。** (4.7) 是整个四维输入代数上的 CPTP 映射，且

$$
\mathcal R_t\mathcal N_t:\quad
(x,y,z)\longmapsto
(k_ts_t+2a_ttb_tx,\ 2a_tty,\ b_tz).
\tag{4.8}
$$

证明。Kraus 形式证明完全正，酉性给出

$$
L_+^\dagger L_++L_-^\dagger L_-
=(|+\rangle\langle+|+|-\rangle\langle-|)\otimes I_2
=I_{C_{\rm rec}\otimes B},
\tag{4.9}
$$

故保迹。这个等式在整个输出代数上成立，包括具有记录非对角块的算子；没有只在实际占用子空间上规定解码再省去保迹扩张。

把未归一化 Hermitian 分支写为 $(pI_2+q_xX+q_yY+q_zZ)/2$。实际矩阵乘法给出

$$
\begin{aligned}
K_+\rho(x,y,z)K_+^\dagger
&=\frac12\left[
\frac{1+k_tz}{2}I_2+a_ttxX+a_ttyY+\frac{k_t+z}{2}Z\right],\\
K_-\rho(x,y,z)K_-^\dagger
&=\frac12\left[
\frac{1-k_tz}{2}I_2+a_ttxX+a_ttyY+\frac{z-k_t}{2}Z\right].
\end{aligned}
\tag{4.10}
$$

例如第一式的对角元是 $a_t^2(1+z)/2,t^2(1-z)/2$，非对角元是 $a_tt(x-iy)/2$，与右式一致；第二式交换两个对角乘子，非对角乘子不变。式中的 $p$ 就是各实际分支迹，所以已经包含 Born 权重。

由 (4.4) 与 (4.5)，逐 Pauli 共轭得到

$$
\begin{array}{c|ccc}
 &X&Y&Z\\ \hline
U_+(\,\cdot\,)U_+^\dagger&b_tX-s_tZ&Y&s_tX+b_tZ\\
U_-(\,\cdot\,)U_-^\dagger&b_tX+s_tZ&Y&-s_tX+b_tZ
\end{array}
\tag{4.11}
$$

将 (4.10) 的两个未归一化分支分别代入 (4.11) 后相加，$X$ 系数为
$2a_ttb_tx+s_t[(k_t+z)-(z-k_t)]/2=2a_ttb_tx+k_ts_t$；
$Z$ 系数中两个 $a_ttx$ 项抵消，剩余 $b_tz$；
$Y$ 系数为 $2a_tty$，总迹为一。这证明 (4.8)。

每个固定 $t$ 的 $\mathcal R_t$ 是同一个解码器，未读取输入标签，也未读取任何未记录指标；它把两个实际分支相加，没有成功后选择、条件归一化后的第二次加权或额外 Born 因子。$t=0$ 时，(4.8) 变成 $(x,y,z)\mapsto(T,0,bz)$，正是来源达到方案的经典重建。$\square$

## 5. 同一参数斜率同时改善三个误差

**定义 5.1（实际重建残差）。** 记

$$
(x_0,z_0)=(u,0),\qquad
(x_+,z_+)=(v,w),\qquad (x_-,z_-)=(v,-w),
$$

并令

$$
f_i(t)=\left(
k_ts_t+2a_ttb_tx_i-x_i,\ (b_t-1)z_i
\right),\qquad
g_i(t)=\frac{\|f_i(t)\|_2}{2}.
\tag{5.1}
$$

由 (4.8)，$g_i(t)$ 就是 $\mathcal R_t\mathcal N_t$ 在第 $i$ 个输入上的实际半迹误差，所以

$$
\varepsilon(\mathcal R_t,\mathcal N_t)=\max_i g_i(t).
\tag{5.2}
$$

**引理 5.2（平衡的严格负一阶变化）。** 对定义 4.1 的同一个 $s_t=T-Mt$，有

$$
g_i(0)=Q,\qquad g_i'(0)=-D<0
\quad(i=0,+,-).
\tag{5.3}
$$

证明。在零点，

$$
f_0(0)=(-e,0),\qquad
f_\pm(0)=(d,\pm(b-1)w).
\tag{5.4}
$$

(2.3) 使三个向量的范数都等于 $e>0$，所以范数在此可微，且 $g_i(0)=e/2=Q$。又有 $s'_0=-M$、$k'_0=0$、$a_0=1$、$b'_0=MT/b$，故

$$
f_i'(0)=\left(-M+2bx_i,\ \frac{MT}{b}z_i\right),\qquad
g_i'(0)=\frac{f_i(0)\cdot f_i'(0)}{2e}.
\tag{5.5}
$$

锚的导数为 $(M-2bu)/2=-D$，使用了 (4.3)。任一侧态的导数为

$$
\frac{d(-M+2bv)+(b-1)w^2MT/b}{2e}
=\frac{-M(d+\beta T)+2bvd}{2e}
=\frac{-MA+2bvd}{2e}.
\tag{5.6}
$$

定义 $M$ 的恒等式 $M(e+A)=2b(eu+vd)$ 给出

$$
-MA+2bvd=e(M-2bu)=-2eD.
\tag{5.7}
$$

所以两个侧态的导数也等于 $-D$。这些等式使用同一仪器、同一 $s_t$ 以及同一对完整酉矩阵，并未拼接分别最优而互不相容的三个解码器。$\square$

**命题 5.3（冻结参数为何在此酉形式内失败）。** 只在 (4.4) 的对称实酉形式内，若把 $s_t$ 改成任意可微函数，保持 $s_0=T$，并记 $m=s'_0$，则

$$
g_0'(0)=-\frac{m+2bu}{2},\qquad
g_+'(0)=g_-'(0)=\frac{mA+2bvd}{2e}.
\tag{5.8}
$$

三个误差的一阶变化都严格负，当且仅当

$$
-2bu<m<-\frac{2bvd}{A}.
\tag{5.9}
$$

证明。此时 $b'_0=-mT/b$，代替 (5.5) 后，锚的内积给出第一式；侧态的内积为
$d(m+2bv)-(b-1)w^2mT/b=m(d+\beta T)+2bvd$，给出第二式。由于 $e,A>0$，两个严格负号分别等价于 (5.9) 的左右不等式。又

$$
uA-vd=(u-v)d+u\beta T=hd+u\beta T>0,
$$

所以 (5.9) 是非空区间。引理 5.2 说明 $m=-M$ 在此区间内，并将三个导数平衡为同一个 $-D$。若固定制备参数，即 $m=0$，锚的导数为 $-bu<0$，两个侧态的导数却为 $bvd/e>0$。因此固定 $s_t=T$ 的这组相位不能使最大误差在零点右侧一阶下降。这个障碍只属于所显示的酉形式，不是对其他相位、一般 CPTP 解码器或其他仪器的不可能性定理。$\square$

## 6. 全闭区间的导数界与实际余项

**引理 6.1（统一向量余项）。** 定义固定正常数

$$
V=1+2M,\qquad H=6+6M+6M^2,\qquad
L=\frac{V^2/e+H}{4}.
\tag{6.1}
$$

对每个 $i$ 和整个 $0\le t\le r_0$，有

$$
\|f_i'(0)\|_2\le V,\qquad
\sup_{0\le\tau\le r_0}\|f_i''(\tau)\|_2\le H,
\tag{6.2}
$$

以及精确积分余项表示

$$
f_i(t)=f_i(0)+tf_i'(0)+R_i(t),\qquad
R_i(t)=\int_0^t(t-\tau)f_i''(\tau)\,d\tau,\qquad
\|R_i(t)\|_2\le\frac H2t^2.
\tag{6.3}
$$

证明。在此闭区间内，$T/2\le s_\tau\le T<1/2$、$b_\tau>1/2$、$a_\tau>1/2$ 且 $\tau\le1/4$。求导得到

$$
b_\tau'=\frac{Ms_\tau}{b_\tau},\qquad
b_\tau''=-\frac{M^2}{b_\tau^3},\qquad
a_\tau'=-\frac{\tau}{a_\tau},\qquad
a_\tau''=-\frac1{a_\tau^3}.
\tag{6.4}
$$

因此

$$
|b_\tau'|\le M,\quad |b_\tau''|\le8M^2,\quad
|a_\tau'|\le1,\quad |a_\tau''|\le8.
\tag{6.5}
$$

令 $j(\tau)=\tau a_\tau$。由 $a_\tau\le1$ 和上述界，

$$
|j|\le\frac14,\qquad
|j'|=|a_\tau+\tau a_\tau'|\le2,\qquad
|j''|=|2a_\tau'+\tau a_\tau''|\le4.
\tag{6.6}
$$

又有

$$
|(s_\tau k_\tau)''|
=|-4s_\tau+8M\tau|\le2+2M.
\tag{6.7}
$$

所有输入满足 $2|x_i|\le1,|z_i|\le1/2$。据 (5.1)，第一坐标的二阶导数为
$(s_\tau k_\tau)''+2x_i(jb_\tau)''$。乘积法则与 (6.5)–(6.7) 给出

$$
\begin{aligned}
|f_{i,x}''(\tau)|
&\le(2+2M)
+2|x_i|\bigl(|j''|b_\tau+2|j'||b_\tau'|+|j||b_\tau''|\bigr)\\
&\le2+2M+4+4M+2M^2
=6+6M+2M^2.
\end{aligned}
\tag{6.8}
$$

第二坐标满足

$$
|f_{i,z}''(\tau)|=|z_i b_\tau''|\le4M^2.
\tag{6.9}
$$

欧氏范数不超过坐标绝对值之和，故 (6.8) 与 (6.9) 之和给出 $H$。在零点，(5.5) 还给出

$$
|f_{i,x}'(0)|\le M+1,\qquad
|f_{i,z}'(0)|\le M/2,
$$

因为 $2b|x_i|\le1$ 且 $T/b<1$。于是 $\|f_i'(0)\|_2\le1+3M/2\le V$。各分量在闭区间上二次连续可微，对其导数积分两次得到 (6.3) 的恒等式，再对积分用 (6.2)，得
$\|R_i(t)\|_2\le H\int_0^t(t-\tau)\,d\tau=Ht^2/2$。这是整个区间上的实际余项控制。$\square$

**引理 6.2（两个范数支撑不等式与误差夹逼）。** 在整个 $[0,r_0]$ 上，对三个 $i$ 同时成立

$$
Q-Dt-Lt^2\le g_i(t)\le Q-Dt+Lt^2.
\tag{6.10}
$$

因此同样有

$$
Q-Dt-Lt^2
\le\varepsilon(\mathcal R_t,\mathcal N_t)
\le Q-Dt+Lt^2.
\tag{6.11}
$$

证明。固定任意 $i$，简写 $f=f_i(0)$、$v_i=f_i'(0)$。引理 5.2 给出

$$
\|f\|_2=e,\qquad f\cdot v_i=-2eD.
\tag{6.12}
$$

正平方根在 $e^2>0$ 的切线支撑不等式是
$\sqrt q\le e+(q-e^2)/(2e)$，适用于每个 $q\ge0$。取
$q=\|f+tv_i\|_2^2$ 得

$$
\|f+tv_i\|_2
\le e+\frac{f\cdot v_i}{e}t+\frac{\|v_i\|_2^2}{2e}t^2.
\tag{6.13}
$$

这也包括 $f+tv_i=0$，没有对该向量的范数求倒数。由三角不等式加上 (6.3)，再除以二，

$$
g_i(t)\le Q-Dt+
\left(\frac{V^2}{4e}+\frac H4\right)t^2
=Q-Dt+Lt^2.
\tag{6.14}
$$

另一个支撑不等式来自单位向量 $f/e$：对任意向量 $q$，
$\|q\|_2\ge(f/e)\cdot q$。应用于 (6.3) 得

$$
\begin{aligned}
\|f_i(t)\|_2
&\ge\frac f e\cdot(f+tv_i+R_i(t))\\
&\ge e-2Dt-\|R_i(t)\|_2
\ge e-2Dt-\frac H2t^2.
\end{aligned}
\tag{6.15}
$$

除以二且用 $L\ge H/4$，得到 (6.10) 的下界。即使下界为负，支撑不等式仍然有效。三个误差分别处于同一上下界内，它们的有限最大值也如此，证明 (6.11)。特别地，

$$
\lim_{t\downarrow0}
\frac{\varepsilon(\mathcal R_t,\mathcal N_t)-Q}{t}=-D.
\tag{6.16}
$$

这是所构造解码器实际达到误差的右导数，不是未知最优值函数的导数。$\square$

## 7. 显式统一区间、平方根夹逼与指数反证

**定理 7.1（同一实际路径的严格改善）。** 令

$$
c=\frac D2,\qquad
t_0=\min\left\{r_0,\frac{D}{2L},\frac QD\right\}>0.
\tag{7.1}
$$

连同 (3.7) 的 $C$，这些常数只依赖固定三态。对整个 $0<t<t_0$，有

$$
\begin{aligned}
0<G_t&\le Ct^2,\\
\varepsilon_\star(\mathcal N_t)
&\le\varepsilon(\mathcal R_t,\mathcal N_t)\le Q-ct,\\
\frac c{\sqrt C}\sqrt{G_t}
&\le Q-\varepsilon_\star(\mathcal N_t)
\le\sqrt{12}\sqrt{G_t}.
\end{aligned}
\tag{7.2}
$$

此外，所达到误差有精确首项比值

$$
\lim_{t\downarrow0}
\frac{Q-\varepsilon(\mathcal R_t,\mathcal N_t)}{\sqrt{G_t}}
=\frac D{\sqrt\gamma}>0.
\tag{7.3}
$$

证明。$r_0,D,L,Q$ 全部严格正且有限，故 $t_0>0$，并且 $t_0\le1/4<1/\sqrt2$，所以仪器物理参数和解码器参数在同一区间内合法。命题 3.3 直接给出第一行。由 $t<t_0\le D/(2L)$，有 $Lt^2\le Dt/2$，故 (6.11) 的上界为 $Q-Dt/2=Q-ct$。又 $t_0\le Q/D$，所以 $Q-ct\ge Q/2>0$，该上界在所用区间内没有负误差问题。

定义 4.3 已证明 $\mathcal R_t$ 属于 (1.6) 的完整竞争类，因此下确界的方向是

$$
\varepsilon_\star(\mathcal N_t)
\le\varepsilon(\mathcal R_t,\mathcal N_t),
\quad\text{从而}\quad
Q-\varepsilon_\star(\mathcal N_t)\ge ct.
\tag{7.4}
$$

由 $G_t\le Ct^2$ 可知 $t\ge\sqrt{G_t}/\sqrt C$，这给出 (7.2) 最后一行的左界。对同一个 $\mathcal N_t$ 使用来源接口 (2.6)，又得到
$Q-\varepsilon_\star(\mathcal N_t)\le\sqrt{12G_t}$，即右界。这里的两个界比较的是同一实际路径上的同一个最优值，没有把另一个仪器的最优误差或缺陷拼接进来。

最后，(6.11) 给出

$$
D-Lt\le
\frac{Q-\varepsilon(\mathcal R_t,\mathcal N_t)}t
\le D+Lt.
$$

结合 $G_t/t^2\to\gamma>0$，得到 (7.3)。精确系数 $D/\sqrt\gamma$ 属于所显示解码器；(7.2) 只确定最优间隙的平方根阶，没有推出它的首项系数、可微性或最优解码器。$\square$

**定理 7.2（每个较大指数在任意正缺陷邻域内失败）。** 固定三态 (1.1)。对每个实数 $\alpha>1/2$、每个有限实数 $K$ 和每个 $\eta>0$，存在 $0<t<t_0$，使

$$
0<G_t<\eta,\qquad
\varepsilon_\star(\mathcal N_t)<Q-KG_t^\alpha.
\tag{7.5}
$$

因此不存在任何这种 $K$，能使 $\varepsilon_\star(\mathcal N)\ge Q-KG(E)^\alpha$ 对此固定族的全部实际有限仪器统一成立，甚至不能只对全部充分小的实际正缺陷成立。

证明。先设 $K\le0$。定理 7.1 给出
$\varepsilon_\star(\mathcal N_t)\le Q-ct<Q\le Q-KG_t^\alpha$。
由 $G_t\le Ct^2$，只要再选 $t<\sqrt{\eta/C}$ 就有 $G_t<\eta$；其严格正性已由命题 3.3 保证。

再设 $K>0$。由于 $2\alpha-1>0$，可选正 $t$ 满足

$$
t<\min\left\{
t_0,\sqrt{\frac\eta C},
\left(\frac{c}{KC^\alpha}\right)^{1/(2\alpha-1)}
\right\}.
\tag{7.6}
$$

所有上界均严格正。于是

$$
KG_t^\alpha\le KC^\alpha t^{2\alpha}<ct,
$$

从而 $\varepsilon_\star(\mathcal N_t)\le Q-ct<Q-KG_t^\alpha$，并有 $0<G_t<\eta$。这证明全部量词。

等价地，若假设所述统一下界成立，正确的下确界方向 (7.4) 会迫使

$$
ct\le Q-\varepsilon_\star(\mathcal N_t)
\le KG_t^\alpha\le KC^\alpha t^{2\alpha}.
$$

除以 $t>0$ 后右端为 $KC^\alpha t^{2\alpha-1}$，随 $t\downarrow0$ 趋零，与固定 $c>0$ 矛盾。该论证依赖实际 $G_t>0$ 且趋零，不是把只在零缺陷端点的事实冒充局部正缺陷反例。$\square$

## 8. 构造机制、归属与未决边界

**解释 8.1（二阶读数变化与一阶相干改善）。** 在本构造内，(3.3) 与 (3.4) 的变化只含 $t^2$，因此测量记录的 Born 概率在零点的一阶变化为零，实际根保真缺陷从二阶开始，且系数是严格正的 $\gamma$。但是 (4.10) 的两个保留分支都有 $a_ttx$、$a_tty$ 相干项，其量级为一阶；完整分支酉解码把它们组合成 (4.8) 中的 $2a_ttb_tx$ 项。再以同一个 $s_t=T-Mt$ 调整两侧制备方向，引理 5.2 才能同时抵消三个误差的竞争，得到共同的严格负导数。冻结参数的失败及其可修正性都已在命题 5.3 的限定形式内说明。

这个机制只解释此处实际仪器和固定任务。若用于学习或表示研究，需要另行建立具体任务、表示、可见记录、保留系统与允许操作之间的对应，验证哪些任务关系被相干分支保留。它只提供方法上的启发，不给出普遍机器学习定理、训练收益或经验性能断言。

**边界 8.2（最优性与操作类型）。** 本文求出了所构造解码器的误差右导数和首项比值，并沿同一路径给出最优间隙的平方根阶。没有求出正缺陷时的精确 $\varepsilon_\star$，没有证明 $\mathcal R_t$ 最优，也没有证明最佳平方根系数、最优值的导数或所有实际仪器的完整最优权衡。输入忠实性、维数与族大小始终固定；没有依靠趋于奇异的输入或增长维数制造反例，也没有分类其他族或奇异输入。

目标始终是三个指定态的半迹极小极大误差。本文没有任意输入、任意未触参考或 diamond 恢复结论，不能把这里的非投影效应和任意共同终端 CPTP 解码器改称另一种受限 PVM 菜单中的操作。也不能将固定编码子空间的全输入任务、整个物理输入空间的任务与本有限族任务互换。所有分支均使用实际 Born 权重，保留系统是实际量子比特；没有隐藏输入标签、未记录环境、额外量子摘要、成功后选择或替代仪器。

**边界 8.3（普适协议及资源桥梁仍为 OPEN）。** 稳健伴卷 §11 与经典伴卷 §5 所保留的普适近似义务，要求在其原有固定公平仪器、时间顺序、量子输出、完整记录及种子权限下，把每个允许实际协议映射为一个合法共同 POVM，并证明所需缺陷与协议误差和资源之间的定量关系。本文的 $\mathcal N_t$ 是明确给定的另一条实际路径，概率并非输入无关公平历史；不能把它代入那个模型并暗改权限。

这里没有构造普适协议到共同测量的映射，没有给出相应资源控制函数，也没有近似记忆或寄存器定律。分别最优的成对测量、独立边缘、删除保留量子输出，或在比较中更换实际仪器，都不完成该桥梁。此处的平方根指数结算不宣称完成更大研究目标。数学上的 CPTP 矩阵构造也不包含物理取得、测量通信、精度、控制合成、运行时间或总成本结论。

**归属 8.4（既有接口与标准方法）。** 固定三态及忠实性来自经典伴卷命题 1.3，$T,Q$ 和达到制备来自其定理 2.1；本文 §2 给出了与稳健伴卷接口 9.1 的完整参数对应。根保真及实际仪器定义沿用两伴卷的定义，(2.6) 的完整输出、任意共同解码器量词来自稳健伴卷定理 9.2，固定成对保真值来自其命题 9.3。本文只把这些明确接口接到两记录弱仪器的共同相干解码、全区间估计和指数反证上，没有重复计算既有全局经典最优值。

根保真测量表示的原始归属按两伴卷对 Nuradha、Mishra、Leditzky、Wilde 的《Multivariate Fidelities》以及 Fuchs、Caves 的《Mathematical Techniques for Quantum Communication Theory》的转述理解；这不是对其原文、版本、链接或文献查全性的独立认证。Bloch 表示、Kraus 完全正性、酉共轭、范数支撑不等式、正平方根切线和 Taylor 积分余项都是标准方法。本文的综合推导不附带世界优先权、外部文献完备性或 Lean kernel 核验声明，结论只在所列来源接口、模型与量词下成立。

## 追加锚（本行以下为增补区）
