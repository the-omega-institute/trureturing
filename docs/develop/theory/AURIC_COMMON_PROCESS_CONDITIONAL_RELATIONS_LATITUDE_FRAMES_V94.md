# 同源条件化关系、共同量子过程与互补三轴的精确修复

## 1. 有限关系接口

**定义 1.1（共同相干截口）。** 设 $A,B$ 是非零有限维复内积空间。记 $M(A)$ 为 $A$ 上的复矩阵代数，$\operatorname{Herm}(A)$ 为其自伴部分，$\mathcal D(A)=\{\rho\ge0:\operatorname{Tr}\rho=1\}$。伴随记作 $\dagger$，在同一个声明的正交基下转置记作 $\mathsf T$。矩阵正序、迹、张量嵌入以及共同复方向都是本定义的结构，不由“全部内容位于 $\Omega$ 内”这一集合归属单独推出。

本卷接续 [V93](AURIC_ENDOGENOUS_FIBER_BALANCE_SUPPORT_RECURSION_QUANTUM_RELATION_FIELD_V93.md) 命题 17.3 的具体缺口：规范补全即使对单个未知输入保持正性与迹，也不自动成为同一个物理过程。共同正延拓复用 [V92](AURIC_BINARY_SPECTRAL_COMPATIBILITY_GLOBAL_QUANTUM_EXTENSION_ELLIPTIC_RELATIONS_V92.md)，闭环定向复用 [V87](AURIC_RELATIVE_ANCHOR_EXCHANGE_RELATION_FIELD_V87.md)。V92 的有限正延拓、其 §18 的 Choi 对应以及文献 [HJR12] 的共同通道插值在下文只作已知中间结果使用。新的有限对象是同一纬线的三态、其内部互补闭合及这两种资料的精确最坏迹距离修复。

**假设 1.2（继承关系的供应条件）。** 原始历史具有同一正比较核；零区别对合法续接相容；共同锐三轴在各实际接口上供应同一个正交复方向；独立准备的比较核相乘。共同正核的商与完备化供应内积载体，锐三轴的共同复方向供应复标量，积核的最小表示供应张量积。这里分别调用 [V78](AURIC_ENDOGENOUS_RELATIONAL_QUANTUM_THEORY_UNIFIED_RELATIONAL_AXIOMS_V78_SYNTHESIS.md) §§3–5、9 的接口和 [V53](AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md) 的锐三轴结果，不把正核、共同方向或独立性省略为未注明的结论。

**定义 1.3（有限准备—后继资料）。** 给定有限非空指标集 $L$，输入 $\rho_j\in\mathcal D(A)$、候选输出 $\sigma_j\in\operatorname{Herm}(B)$，以及 $p_j>0$、$\sum_jp_j=1$。定义内部平均

$$
\tau=\sum_{j\in L}p_j\rho_j.
\tag{1.1}
$$

将 $A$ 限制为 $\tau$ 的支撑，则 $\tau>0$，且所有 $\rho_j$ 均支撑于 $A$。事实上，若 $v\in\ker\tau$，则 $\sum_jp_j\langle v,\rho_jv\rangle=0$；各项非负而各 $p_j>0$，故 $\rho_jv=0$。限制没有删去任何已给准备。以下所有逆均在这个共同支撑上取。

权重 $p_j$ 是构成内部平均的凸坐标，可取有限菜单的均匀权；不同严格正权给出同一资格的事实由定理 7.1 证明，不另要求外部随机源。

“共同过程”要求同一个线性映射实现全部 $j$，而非 $\forall j\,\exists\Phi_j$ 或 $\forall j,k\,\exists\Phi_{jk}$。一个准备是 $\Omega$ 内的条件接口；这里没有把 $j$ 当作过程可以暗中读取的额外经典标签。

## 2. 唯一候选 C94：同源条件化相容

**定义 2.1（内部准备菜单）。** 在与 $A$ 同维且基已对齐的内部参考 $R$ 上定义

$$
F_j=p_j\tau^{-\mathsf T/2}\rho_j^{\mathsf T}\tau^{-\mathsf T/2},
\qquad F_j\ge0,\qquad\sum_jF_j=I_R.
\tag{2.1}
$$

这里 $\tau^{-\mathsf T/2}=(\tau^{\mathsf T})^{-1/2}$。令

$$
|\Gamma_\tau\rangle
=(\tau^{\mathsf T/2}\otimes I_A)\sum_k|k\rangle_R|k\rangle_A.
\tag{2.2}
$$

其范数为一，参考边际为 $\tau^{\mathsf T}$，并且

$$
\operatorname{Tr}_R[(F_j\otimes I_A)|\Gamma_\tau\rangle\langle\Gamma_\tau|]
=p_j\rho_j.
\tag{2.3}
$$

等式来自 $\operatorname{Tr}_R[(E\otimes I)|\Gamma_\tau\rangle\langle\Gamma_\tau|]=\tau^{1/2}E^{\mathsf T}\tau^{1/2}$。式 (2.3) 是同一份内部关系的条件化，不是复制未知输入的操作。

**定义 2.2（同源条件化相容候选 C94）。** 对任意 $Y\in\operatorname{Herm}(R)$ 与 $H_j\in\operatorname{Herm}(B)$，定义

$$
\begin{aligned}
W(Y,H)&=Y\otimes I_B+\sum_jF_j\otimes H_j,\\
b(Y,H)&=\operatorname{Tr}(\tau^{\mathsf T}Y)
 +\sum_jp_j\operatorname{Tr}(\sigma_jH_j).
\end{aligned}
\tag{2.4}
$$

本卷只有以下一个候选：

$$
\boxed{\quad b(Y,H)\le\lambda_{\max}(W(Y,H))
\quad\text{对所有 }Y,H.\quad}
\tag{C94}
$$

同一条件作用于 $(-Y,-H)$ 给出下谱界。$W=0$ 时要求 $b=0$，因此同一算符内容的不同表达不能给不同响应。候选比较的两个元，是由准备—后继资料定义的响应 $b$ 与由同一准备菜单定义的合成关系 $W$。它将 V92 的静态谱界施加于同一准备关系的条件输出，不另给每个输入选择一份无关全态。

## 3. 共同条件化与纬线的精确实现边界

**定义 3.1（纬线资料及其互补闭合）。** 固定 $0<z<1$、$s=\sqrt{1-z^2}$、$\theta_j=2\pi j/3$，$j=0,1,2$。以 $X,Y,Z$ 表示 Pauli 矩阵，定义

$$
\begin{aligned}
r_j&=(s\cos\theta_j,s\sin\theta_j,z),\\
\rho_j&=\frac{I+r_j\cdot(X,Y,Z)}2,\\
u_j(a,q)&=(as\cos\theta_j,-as\sin\theta_j,q),\\
\sigma_j(a,q)&=\frac{I+u_j(a,q)\cdot(X,Y,Z)}2.
\end{aligned}
\tag{3.1}
$$

$a,q$ 起初为实数。三态取等权 $1/3$；其内部平均为 $(I+zZ)/2$。式 (2.1) 的三项恰为

$$
F_j=\frac13
\begin{pmatrix}1&e^{i\theta_j}\\e^{-i\theta_j}&1\end{pmatrix}.
\tag{3.2}
$$

因而内部校准菜单与纬度 $z$ 无关，纬度仍由同一来源的参考边际保留，不能随菜单归一化一并删除。

互补闭合资料增加 $\rho_{j,-}=I-\rho_j$、$\rho_{j,+}=\rho_j$，并指定输出 $\sigma_{j,+}(a,b)=\sigma_j(a,bz)$、$\sigma_{j,-}(a,b)=I-\sigma_{j,+}(a,b)$。六态取等权 $1/6$，其内部平均为 $I/2$。互补态是分别声明的准备；本定义不假定存在把任意未知态送至其互补态的通用物理门。

**定理 3.2（同源条件化、三态边界与互补加强）。** 对定义 1.3 的任意资料，C94 当且仅当存在一个完全正保迹映射 $\Phi:M(A)\to M(B)$，使 $\Phi(\rho_j)=\sigma_j$ 对全部 $j$ 同时成立。因此候选自身排除不归一或非正的候选输出。

对定义 3.1 的三态，C94 当且仅当

$$
\boxed{|q+za^2|\le1-a^2.}
\tag{3.3}
$$

特别地，对镜像保留资料 $a=\eta,q=\eta z$、$0\le\eta\le1$，

$$
\boxed{\text{三态共用一个过程}\iff\eta\le\frac1{1+z}.}
\tag{3.4}
$$

对互补闭合六态，精确镜像目标 $a=b=\eta$ 满足 C94 当且仅当 $\eta\le1/3$。但三态或六态中的任意一对，在整个 $0\le\eta\le1$ 上均可由对该对专用的一个完全正保迹过程实现。

证明。先处理 C94 的已知表示步骤。V92 定理 4.1 的正延拓证明适用于任意有限维实线性读出映射，而不依赖其各分量必须为部分迹。具体将密度态 $J\in\mathcal D(R\otimes B)$ 映为

$$
\mathcal A(J)=\left(\operatorname{Tr}_B J,
 \big(\operatorname{Tr}_R[(F_j\otimes I)J]\big)_j\right).
\tag{3.5}
$$

该像非空、紧且凸。其对偶方向 $(Y,H)$ 的支撑函数是 $\lambda_{\max}(W(Y,H))$。因此 C94 当且仅当

$$
\operatorname{Tr}_B J=\tau^{\mathsf T},\qquad
\operatorname{Tr}_R[(F_j\otimes I)J]=p_j\sigma_j
\tag{3.6}
$$

对同一个 $J\ge0$ 成立。若目标不在像内，取其到像的最近点，差向量所定义的支撑方向便严格违反 C94；这正是 V92 的最近点分离步骤，不是新的分离定理。

令

$$
C=(\tau^{-\mathsf T/2}\otimes I)J(\tau^{-\mathsf T/2}\otimes I).
\tag{3.7}
$$

则 $C\ge0$ 且 $\operatorname{Tr}_B C=I_R$。V92 §18 的有限 Choi 对应给同一个通道

$$
\Phi(U)=\operatorname{Tr}_R[(U^{\mathsf T}\otimes I)C].
\tag{3.8}
$$

式 (2.1)、(3.6) 及部分迹对参考因子的循环性给 $p_j\Phi(\rho_j)=p_j\sigma_j$。反过来，若有同一个 $\Phi$，取 $J=(\operatorname{id}_R\otimes\Phi)(|\Gamma_\tau\rangle\langle\Gamma_\tau|)$ 即得 (3.6)。共同通道插值本身属于 [HJR12]；这里使用内部平均把它接成同一准备菜单的状态延拓。

再求三态的精确边界。记 $R_\theta$ 为 Bloch 空间绕 $Z$ 的旋转。输入满足 $r_{j+1}=R_{2\pi/3}r_j$，目标满足 $u_{j+1}=R_{-2\pi/3}u_j$。若一个通道实现全部资料，对它作相应三循环平均仍实现全部资料。平均后的仿射 Bloch 映射必须为

$$
(x,y,w)\longmapsto
(a x+c y,c x-a y,bw+t).
\tag{3.9}
$$

对精确实相位目标，三个不共线的横向点迫使 $c=0$；故 $q=bz+t$。相应非归一 Choi 矩阵为

$$
C_{a,b,t}=\frac12
\begin{pmatrix}
1+b+t&0&0&0\\
0&1-b-t&2a&0\\
0&2a&1-b+t&0\\
0&0&0&1+b-t
\end{pmatrix}.
\tag{3.10}
$$

它的正性恰为

$$
1+b\ge|t|,\qquad
1-b\ge\sqrt{t^2+4a^2}.
\tag{3.11}
$$

这是标准 qubit Choi 正性在本资料上的中间计算。必要性已含 $|q|\le1$。在固定 $q=bz+t$ 后，允许的 $b$ 位于

$$
\begin{aligned}
b_-&=\max\left\{\frac{q-1}{1+z},\frac{-q-1}{1-z}\right\},\\
b_+&=\min\left\{\frac{1-q}{1-z},\frac{1+q}{1+z}\right\}.
\end{aligned}
\tag{3.12}
$$

在该区间，$f(b)=(1-b)^2-(q-bz)^2$ 是凸二次函数；端点值为 $f(b_-)=-4b_-$、$f(b_+)=0$。所以 (3.11) 蕴含

$$
a^2\le-b_-=
\min\left\{\frac{1-q}{1+z},\frac{1+q}{1-z}\right\},
\tag{3.13}
$$

这正是 (3.3)。反过来，(3.3) 给 $a^2\le1$；取 $b=-a^2$、$t=q+za^2$，立即满足 (3.11)，所以充分性也成立。

达到上边界 $q=1-(1+z)a^2$ 的通道有两条 Kraus：

$$
K_0=\begin{pmatrix}0&1\\a&0\end{pmatrix},\qquad
K_1=\begin{pmatrix}\sqrt{1-a^2}&0\\0&0\end{pmatrix}.
\tag{3.14}
$$

它们满足 $\sum K_\alpha^\dagger K_\alpha=I$，Bloch 映射为 $(ax,-ay,-a^2w+1-a^2)$。将两条 Kraus 同时改为 $XK_\alpha X$ 达到下边界；按同一权重混合两通道得到两边界之间全部 $q$。当 $a$ 为负时同一矩阵公式仍有效。

代入 $a=\eta,q=\eta z$，(3.13) 的第一项较小，故 $\eta^2(1+z)+\eta z\le1$。左侧减一分解为 $(\eta+1)((1+z)\eta-1)$，得到 (3.4)。

对互补六态，每一对的平均都是同一个 $I/2$，其输出平均也为 $I/2$；共同通道必须满足 $\Phi(I/2)=I/2$。因此 $t=0$。又 $0<z<1$ 保证三条 $r_j$ 线性无关，精确镜像目标迫使 $a=b=\eta$。式 (3.11) 成为 $1-\eta\ge2\eta$，即 $\eta\le1/3$。

最后，任意两条输入纯射线与其转置后的两条纯射线有相同重叠模长。适当选择射线代表相位后，两份二阶 Gram 矩阵相同，故存在只为该对选择的酉将两态送至两份转置态。再接 $D_\eta(U)=\eta U+(1-\eta)\operatorname{Tr}(U)I/2$ 即得目标。对正交、重合及互补对同样成立。两态转换的标准背景见 [CJW04] 的定理 1–2；这里没有把各对的酉视为同一个酉。证毕。

## 4. 三态资料的最小共同修复

**定义 4.1（固定输入的修复距离）。** 对定义 3.1 的精确镜像目标 $\sigma_j(\eta,\eta z)$，定义

$$
D_3(z,\eta)=\min_{\Phi\ {\rm CPTP}}
\max_{j=0,1,2}\frac12\|\Phi(\rho_j)-\sigma_j(\eta,\eta z)\|_1.
\tag{4.1}
$$

这是修复全部指定输出所需的最小最坏迹距离，输入、标签及同一过程量词保持固定；它不是寻找每个输入各自最佳过程后的平均误差。

**定理 4.2（三态修复的唯一三次根与达到）。** 若 $0\le\eta\le(1+z)^{-1}$，则 $D_3(z,\eta)=0$。若 $(1+z)^{-1}<\eta\le1$，令 $a_*$ 为

$$
2(1+z)a^3+[2\eta z-(1+z)]a-(1-z)\eta=0
\tag{4.2}
$$

的唯一正根，则

$$
\sqrt{\frac{1-\eta z}{1+z}}<a_*<\eta,
\tag{4.3}
$$

$$
\boxed{D_3(z,\eta)=\frac12
\sqrt{(1-z^2)(a_*-\eta)^2+
 [1-(1+z)a_*^2-\eta z]^2}.}
\tag{4.4}
$$

式 (3.14) 在 $a=a_*$ 时达到该值。此外，令 $\eta_*=(1+z)^{-1}$，固定 $z$，则

$$
D_3(z,\eta_*+\varepsilon)
=\frac{(2+z)\sqrt{1-z^2}}{2\sqrt{5-z^2}}\,
\varepsilon+O(\varepsilon^2)
\quad(\varepsilon\downarrow0).
\tag{4.5}
$$

证明。迹范数的凸性与酉不变性允许先对通道作三循环平均而不增加最坏误差。再作 $\Phi\mapsto(\Phi+T\Phi T)/2$，其中 $T(U)=U^{\mathsf T}$，可消去 (3.9) 的 $c$。若 $\Phi(U)=\sum K_\alpha U K_\alpha^\dagger$，则 $T\Phi T$ 的 Kraus 是 $\overline K_\alpha$，所以该平均仍为通道。它仅为通道集合的数学对称论证，不把单独转置声明为实际可执行的门。

qubit 迹距离是 Bloch 欧氏距离的一半，故定理 3.2 将问题精确化为

$$
\frac12\min_{|q+za^2|\le1-a^2}
\sqrt{s^2(a-\eta)^2+(q-\eta z)^2}.
\tag{4.6}
$$

由于可行域只依赖 $a^2$，可取 $a\ge0$。令 $a_0=\sqrt{(1-\eta z)/(1+z)}$。若 $0\le a\le a_0$，最优 $q=\eta z$，这一段最优端点为 $a_0$。若 $a\ge a_0$，最优 $q=1-(1+z)a^2$；$a>\eta$ 同时增大两项误差，故只需 $a\in[a_0,\eta]$。在此区间最小化

$$
f(a)=s^2(a-\eta)^2+[1-(1+z)a^2-\eta z]^2.
\tag{4.7}
$$

其端点导数满足 $f'(a_0)<0<f'(\eta)$，而

$$
\begin{aligned}
f'(a)&=2(1+z)\{2(1+z)a^3+[2\eta z-(1+z)]a-(1-z)\eta\},\\
f''(a)&=2s^2+8(1+z)^2a^2
 -4(1+z)[1-(1+z)a^2-\eta z]>0
\end{aligned}
\tag{4.8}
$$

在该区间成立。故有唯一内部最小点，得到 (4.2)–(4.4)。式 (4.2) 的三次式常数项为负、首项为正，非零系数只有一次符号改变；或者直接考察其导数的唯一正临界点，可知它在整个正半轴也只有这个正根。边界 Kraus 给出达到。

为证明 (4.5)，将 (4.6) 的加权坐标改为 $(sa,q)$。可行域上边界在 $(\eta_*,z\eta_*)$ 的切线法向量与 $(2/s,1)$ 同向，目标随 $\eta$ 的速度为 $(s,z)$。其沿单位法向量的速度为

$$
\frac{2+z}{\sqrt{4/s^2+1}}
=\frac{(2+z)s}{\sqrt{5-z^2}}.
$$

边界为光滑严格凸曲线，且 (4.8) 在阈值点的驻点导数非零，隐函数定理给最优点随 $\varepsilon$ 光滑变化。欧氏距离的一阶项为上述法向速度，迹距离再除以二，得 (4.5)。证毕。

## 5. 互补闭合的精确修复与最佳三轴

**定义 5.1（互补六态的修复距离）。** 令 $\sigma_{j,\pm}$ 为定义 3.1 在 $a=b=\eta$ 时的互补目标，定义

$$
D_6(z,\eta)=\min_{\Phi\ {\rm CPTP}}
\max_{j,\epsilon\in\{+,-\}}
\frac12\|\Phi(\rho_{j,\epsilon})-\sigma_{j,\epsilon}\|_1.
\tag{5.1}
$$

**定理 5.2（内部互补框架的尖锐共同过程缺额）。** 对 $0<z<1$、$0\le\eta\le1$，

$$
\boxed{
D_6(z,\eta)=
\begin{cases}
0,&\eta\le1/3,\\[1mm]
\dfrac{(3\eta-1)z\sqrt{1-z^2}}
 {2\sqrt{1+3z^2}},&\eta>1/3.
\end{cases}}
\tag{5.2}
$$

在 $\eta>1/3$ 时，设

$$
a_* =\frac{\eta(1-3z^2)+2z^2}{1+3z^2},
\qquad b_*=1-2a_*.
\tag{5.3}
$$

达到最优值的同一个通道为

$$
\Phi_*(U)=a_*XUX+\frac{1-a_*}{2}(U+ZUZ).
\tag{5.4}
$$

对固定 $\eta>1/3$，$D_6(z,\eta)$ 的唯一最大纬度为 $z=1/\sqrt3$，最大值为 $(3\eta-1)/6$。该纬度的三条 $r_j$ 彼此正交，六态构成一个旋转后的三轴互补框架。

证明。设一个通道的 Bloch 仿射形式为 $r\mapsto Ar+t$。定义 spin-flip 线性映射 $S(U)=YU^{\mathsf T}Y$；它在 Bloch 向量上作用为 $r\mapsto-r$。若 $\Phi$ 有 Kraus $K_\alpha$，则 $S\Phi S$ 有 Kraus $Y\overline K_\alpha Y$，因此仍为通道。六态资料在同时反号下闭合，故平均 $\Phi$ 与 $S\Phi S$ 不增加最坏误差，并消去 $t$。这一论证使用两侧反酉共轭保持通道集合，不要求 $S$ 自身为量子通道。

再如定理 4.2 作三循环与转置双侧平均，通道可取为

$$
(x,y,w)\mapsto(ax,-ay,bw),\qquad
-1\le b\le1-2|a|.
\tag{5.5}
$$

目标 $\eta\ge0$ 允许取 $a\ge0$。问题成为

$$
D_6=\frac12\min_{-1\le b\le1-2a,\ a\ge0}
\sqrt{s^2(a-\eta)^2+z^2(b-\eta)^2}.
\tag{5.6}
$$

若 $\eta>1/3$，目标 $(\eta,\eta)$ 位于直线 $2a+b=1$ 外。将该点按度量 $\operatorname{diag}(s^2,z^2)$ 投影到这条直线，得到 (5.3)，并得到距离

$$
\frac{3\eta-1}{2\sqrt{4/s^2+1/z^2}},
$$

即 (5.2)。当 $\eta\in[1/3,1]$ 时，$a_*$ 在其两个端点值 $1/3$ 与 $(1-z^2)/(1+3z^2)$ 之间，故 $0<a_*<1$，投影点确实位于 (5.5) 的合法边界线段。对整个半平面的距离是任何合法通道的下界；式 (5.4) 的 Pauli 混合具有 Bloch 系数 $(a_*,-a_*,1-2a_*)$，恰好达到投影点。这证明全局最优性。阈值内由定理 3.2 达到零。

最后令 $u=z^2\in(0,1)$，则

$$
\left(\frac{z\sqrt{1-z^2}}{\sqrt{1+3z^2}}\right)^2
=\frac{u(1-u)}{1+3u},\qquad
\frac{d}{du}\frac{u(1-u)}{1+3u}
=\frac{1-2u-3u^2}{(1+3u)^2}.
\tag{5.7}
$$

分子在 $(0,1)$ 的唯一零点为 $u=1/3$，且两侧符号一正一负，故最大值唯一。此时 $r_j\cdot r_k=(3z^2-1)/2=0$，而系数等于 $1/3$。证毕。

## 6. 二元失败、三维提升与退化边界

**定理 6.1（同一有限资料中的标量盲区与二元关系见证）。** 定义 3.1 的镜像资料在全部 $0\le\eta\le1$ 上通过任意 Hermitian 实线性组合的迹范数不增测试：

$$
\left\|\sum_jc_j\sigma_j\right\|_1
\le\left\|\sum_jc_j\rho_j\right\|_1
\quad(c_j\in\mathbb R),
\tag{6.1}
$$

对互补闭合资料也成立。然而六态在 $\eta>1/3$ 时违反 C94；当 $1/3<\eta<1$ 时，该违反可在同一参考—输出记录的二元块中表示为三维单位球外点；$\eta=1$ 时由零对角与非零交叉项直接见证非正。

证明。令 $T_\eta(U)=\eta U^{\mathsf T}+(1-\eta)\operatorname{Tr}(U)I/2$。它对 $0\le\eta\le1$ 为正且保迹，并实现所有目标的线性表。若 $U=U_+-U_-$ 为 Hermitian Jordan 分解，则

$$
\|T_\eta(U)\|_1
\le\operatorname{Tr}T_\eta(U_+)+\operatorname{Tr}T_\eta(U_-)
=\|U\|_1.
\tag{6.2}
$$

所以 (6.1) 不含完整正性所需的参考关系。

六态张成全部 $\operatorname{Herm}(\mathbb C^2)$，故实现它们的线性映射只能是 $T_\eta$。其归一 Choi 表为

$$
J_\eta=\frac{1-\eta}{4}I_4+\frac\eta2\,\mathsf F,
\tag{6.3}
$$

其中 $\mathsf F$ 交换两个内部 qubit。在反对称单位向量 $|\psi_-\rangle=(|01\rangle-|10\rangle)/\sqrt2$ 上读数为 $(1-3\eta)/4$。这复用标准转置非完全正的见证 [BDPS03]，在本资料中它是全部六态共同过程失败的具体二元读口 $P_-,I-P_-$。

在两条历史 $|01\rangle,|10\rangle$ 上压缩得到

$$
G_\eta=\frac14
\begin{pmatrix}1-\eta&2\eta\\2\eta&1-\eta\end{pmatrix},
\qquad q_\eta=\operatorname{Tr}G_\eta=\frac{1-\eta}{2}.
\tag{6.4}
$$

当 $\eta<1$ 时，保留尺度 $q_\eta$，再写

$$
\frac{G_\eta}{q_\eta}=\frac{I+v_\eta\cdot(X,Y,Z)}2,
\qquad v_\eta=\left(\frac{2\eta}{1-\eta},0,0\right).
\tag{6.5}
$$

二元块非负当且仅当 $|v_\eta|\le1$，恰好给 $\eta\le1/3$。这里三维是二元 Hermitian 关系的三个实坐标；整体记录仍位于四维复载体，未被压成物理三维空间。$\eta=1$ 时 $q_\eta=0$ 而交叉项非零，直接违反正矩阵的零对角约束，不作除零归一化。证毕。

**定理 6.2（共同实现的秩退化与有限精度）。** 在本有限家族内，三态与六态的精确可实现阈值不能跨退化端点连续外推；但两种最优修复距离在相应退化极限均可趋零。

证明。$z=0$ 时输入全部位于赤道，$X\rho_jX=\rho_j^{\mathsf T}$，同一酉实现 $\eta=1$；互补闭合仍在赤道，结论相同。$z=1$ 时三态全为 $|0\rangle\langle0|$，互补闭合只再增加 $|1\rangle\langle1|$；转置在这些输入上为恒等，故 $\eta=1$ 也可实现。相反，任意 $0<z<1$ 的六态阈值始终为 $1/3$，而三态阈值在 $z\uparrow1$ 时趋 $1/2$。

式 (5.2) 给 $D_6\to0$ 当 $z\downarrow0$ 或 $z\uparrow1$。三态修复距离在 $z\downarrow0$ 时不超过通道 $D_\eta\circ\operatorname{Ad}_X$ 的误差 $\eta z\le z$；在 $z\uparrow1$ 时，用常值输出 $(I+\eta zZ)/2$ 的通道给上界 $\eta\sqrt{1-z^2}/2\to0$。因此精确兼容资格的跳跃不产生固定正的观测误差下界。证毕。

**定理 6.3（V93 上方块完成的精确物理化成本）。** 设 $\Psi(U)=(U+U^{\mathsf T})/2$，即 [V93](AURIC_ENDOGENOUS_FIBER_BALANCE_SUPPORT_RECURSION_QUANTUM_RELATION_FIELD_V93.md) 命题 17.3 的上方二位块规则。定义

$$
\Xi_\eta(U)=\eta\Psi(U)+(1-\eta)\operatorname{Tr}(U)I/2,
\qquad 0\le\eta\le1.
\tag{6.6}
$$

若要求把这一规则实现为未知输入上的同一个通道，则精确资格为 $\eta\le1/2$。对六个 Pauli 轴纯准备 $\rho_{i,\pm}=(I\pm\sigma_i)/2$，$i=x,y,z$，固定目标 $\Xi_\eta(\rho_{i,\pm})$，有

$$
\boxed{\min_{\Phi\ {\rm CPTP}}\max_{i,\epsilon}
\frac12\|\Phi(\rho_{i,\epsilon})-\Xi_\eta(\rho_{i,\epsilon})\|_1
=\frac{(2\eta-1)_+}{6}.}
\tag{6.7}
$$

当 $\eta>1/2$ 时，达到通道是

$$
\Phi_\eta(U)=\frac{\eta+1}{3}U+
\frac{2-\eta}{6}(XUX+ZUZ).
\tag{6.8}
$$

同一数值也是将最大值扩展到全部 qubit 密度态后的最优最坏距离。因此六轴有限资料已见证这个线性过程的全输入修复成本；原规则 $\eta=1$ 的该距离为 $1/6$。

证明。$\Xi_\eta$ 的 Bloch 系数为 $(\eta,0,\eta)$。其非归一 Choi 矩阵对角化给四个本征值

$$
\frac{1+2\eta}{2},\quad\frac12,\quad\frac12,\quad
\frac{1-2\eta}{2}.
$$

故它为通道当且仅当 $\eta\le1/2$，这时 (6.7) 为零。

为证明任意通道的下界，写其 Bloch 映射为 $r\mapsto Ar+t$，设六项迹距离均不超过 $\delta$。对每个轴的正负准备，取两个误差向量之差，得到

$$
\|(A-\operatorname{diag}(\eta,0,\eta))e_i\|\le2\delta.
\tag{6.9}
$$

任意通道的归一 Choi 表在 singlet 上的非负响应给

$$
A_{xx}+A_{zz}-A_{yy}\le1.
\tag{6.10}
$$

平移 $t$ 不贡献该方向的期望，因为 singlet 的两端边际都是 $I/2$。因此

$$
2\eta-1\le
|\eta-A_{xx}|+|\eta-A_{zz}|+|A_{yy}|
\le6\delta.
\tag{6.11}
$$

这是对全部通道的下界，无须先假定最优通道对称。式 (6.8) 的三个非负权之和为一，其 Bloch 系数为

$$
\left(\frac{\eta+1}{3},\frac{2\eta-1}{3},\frac{\eta+1}{3}\right).
$$

三个轴的输出误差模长都等于 $(2\eta-1)/3$，迹距离均为其一半，达到下界。 进一步令 $\epsilon=(2\eta-1)/3$，达到通道与目标的 Bloch 差矩阵为 $\epsilon\operatorname{diag}(-1,1,-1)$。它在任意 Bloch 向量 $r$ 上的误差为 $\epsilon|r|/2$，故全部纯输入都达到同一个距离，混合输入的误差不超过它。这证明全输入最大值与六轴最大值相同。

若将二位块重新嵌回 V93 的三位载体，先保留两个对角块、在上方块使用 (6.8)、在第三维保持原值，便给一个全三位通道。反过来，任何全三位通道在这些上方块输入上的输出，可再经“保留上方块并把第三维质量送至 $I_2/2$”的完全正保迹回缩；该回缩固定目标且收缩迹距离。因此增加第三维输出不能降低 (6.7)。此处求的是额外指定的未知输入过程，不改变 V93 中规范代表作为推断对象的定义。证毕。

## 7. 换内部平均与同一过程的身份

**定理 7.1（同一资料的全支撑换锚与零资格不变）。** 对定理 3.2 的同一输入输出资料，任意两组严格正权 $p,p'$ 产生的 C94 具有相同真假值。若它们的内部平均分别为 $\tau,\tau'$，实现同一通道的共同记录之间满足

$$
J_{\tau'}=(L_{\tau'\leftarrow\tau}\otimes I)J_\tau
 (L_{\tau'\leftarrow\tau}^\dagger\otimes I),
\qquad
L_{\tau'\leftarrow\tau}=\tau'^{\mathsf T/2}\tau^{-\mathsf T/2}.
\tag{7.1}
$$

对第三个全支撑内部平均 $\tau''$，有 $L_{\tau''\leftarrow\tau'}L_{\tau'\leftarrow\tau}=L_{\tau''\leftarrow\tau}$。但增加互补准备会改变资料本身；它不是式 (7.1) 的换权。

证明。定理 3.2 对每组正权都将 C94 等价为同一组等式 $\Phi(\rho_j)=\sigma_j$，所以零资格不变。固定该 $\Phi$ 的非归一 Choi 矩阵 $C$，则 $J_\tau=(\tau^{\mathsf T/2}\otimes I)C(\tau^{\mathsf T/2}\otimes I)$，代入得到 (7.1)。相邻可逆因子相消给组合律。对三态，均匀内部平均为 $(I+zZ)/2$；加入互补准备后平均为 $I/2$，但要求同时满足的输入输出等式已增加。定理 3.2 的两个不同阈值正是这项新增约束的结果，不能解释为同一资料的归一化规范差异。证毕。

## 8. 由候选接回有限量子理论的条件链

**定义 8.1（同一关系理论的闭合对象）。** 在假设 1.2 的接口上，将无输入、输出为 $A$ 的正归一准备表示为 $\rho\in\mathcal D(A)$；将一个结果的读口表示为 $0\le E\le I$；将完整菜单表示为 $\sum_eE_e=I$；将后继表示为一族完全正映射 $\mathcal I_e$，其中 $\sum_e\mathcal I_e$ 保迹。C94 对每个声明的准备—后继族要求同一个过程实现，不允许每次根据输入态另选过程。

下列标准表示均作为定理 3.2 的候选接续使用，其前件与证明接口分别如下。

1. **Hilbert 空间、复方向与叠加。** 同一正历史核的零空间商给正内积，完备化给 Hilbert 空间。共同锐三轴在实载体上满足 $A_iA_j+A_jA_i=2\delta_{ij}I$ 时，$J=A_1A_2A_3$ 满足 $J^2=-I$、$J^\dagger=-J$ 并与各 $A_i$ 对易，因而供应共同复方向。这里的共同锐三轴与跨接口对齐仍是明确前件；C94 不从孤立的集合 $\Omega$ 强迫它们存在。

2. **Born 读出与状态。** [V79](AURIC_BINARY_REVERSAL_COMPATIBILITY_FINITE_PHASE_CERTIFICATES_AND_QUANTUM_READOUT_RECONSTRUCTION_V79.md) 的非负性、总强度支配、二元相干反向与共同相位校准给 $w_e(x)=\langle x,E_ex\rangle$。在完整效果接口上，非负、归一、细分可加、代表无关的响应由迹对偶写成 $p(E)=\operatorname{Tr}(\rho E)$；秩一正测试给 $\rho\ge0$，单位测试给迹一。密度态的极点是秩一投影，所以纯准备和锐射线给 $p_\phi(\psi)=|\langle\phi,\psi\rangle|^2$。这些反向相干与细分前件不能由“定义概率为平方”替代。

3. **通道、仪器与更新。** C94 的共同记录经 (3.7)–(3.8) 给 $\Phi(U)=\sum_\alpha K_\alpha U K_\alpha^\dagger$、$\sum_\alpha K_\alpha^\dagger K_\alpha=I$。将结果标签纳入正交输出记录，并对保留标签的整个后继施加 C94。对输出的标签块投影取得正 Choi 块 $J_e$，其秩一分解及未读细记录给 $\mathcal I_e(U)=\sum_\alpha K_{e\alpha}UK_{e\alpha}^\dagger$，$E_e=\sum_\alpha K_{e\alpha}^\dagger K_{e\alpha}$。故 $p_e=\operatorname{Tr}(\rho E_e)$；当 $p_e>0$ 时条件输出为 $\mathcal I_e(\rho)/p_e$。零概率结果不作条件化。同一效果可有不同的 $K_{e\alpha}$，因而效果本身不决定唯一测后态。

4. **理想投影更新。** 若锐读口 $P$ 的单细分支算符 $M$ 除了 $M^\dagger M=P$，还在 $\operatorname{Ran}P$ 上仅作一个共同相位，则 $M=e^{i\theta}P$，所以条件输出是 $P\rho P/\operatorname{Tr}(\rho P)$。没有此理想性前件，重复性或同一个效果不足以唯一选定 Lüders 更新。

5. **复合与结果树。** 独立准备的积核给最小张量表示；对全部内部有限参考使用同一个正记录给完整正性。若后段 Kraus 为 $L_\beta$，前段为 $K_\alpha$，复合分支为 $L_\beta K_\alpha$，且 $\sum_{\alpha,\beta}(L_\beta K_\alpha)^\dagger L_\beta K_\alpha=I$。独立复合分支为 $K_\alpha\otimes L_\beta$，同样归一。因此有限串接、独立并接及保留全部标签的结果树闭合。张量前件不由无信号或标量边际相同自动取得。

6. **可逆性与运动方程。** 若有限同维的通道 $\Phi$ 有同一个完全正保迹逆 $\Psi$，其全部 Kraus $K_\alpha,L_\beta$ 满足恒等通道的 Kraus 关系 $L_\beta K_\alpha=c_{\beta\alpha}I$。取非零系数，得到可逆 $K_\alpha$ 与 $L_\beta$；保持该 $\beta$，每个 $K_\gamma$ 都与同一个 $K_\alpha$ 成比例。因此 $\Phi(U)=VUV^\dagger$，保迹给 $V$ 酉。对光滑内部历史的酉提升 $V(t)$，$H(t)=i\hbar\dot V(t)V(t)^\dagger$ 为自伴，$i\hbar\dot\psi=H(t)\psi$。加法时钟与一参数群才进一步给常生成元；C94 不指定实际时钟、Hamiltonian 或 $\hbar$ 的数值。

这些等式给一个完整的有限数学表示：准备、读出、条件后继、复合及可逆运动使用同一套对象。它们不把每个数学上允许的通道都认作某个具体内部安装已经可取得的控制资源。连续无限维、具体动力学、相对论场和经验对应不属于这里有限接口的结论。

## 9. 数学引文与归属

**文献 9.1（共同过程插值与先例）。** [HJR12] Teiko Heinosaari, Maria A. Jivulescu, David Reeb, Michael M. Wolf, *Extending quantum operations*, Journal of Mathematical Physics 53, 102208 (2012), [arXiv:1205.0641](https://arxiv.org/html/1205.0641), DOI [10.1063/1.4755845](https://doi.org/10.1063/1.4755845)。其定理 1、§6.1、定理 5–6 分别给子空间完整正性、保迹延拓的额外约束以及两态转换结果。共同通道插值、正锥对偶、Choi 条件与完全正映射的标准表示均为 `literature-attested`，不作为本卷的新一般定理。

**文献 9.2（两态与有限态族的转换）。** [CJW04] Anthony Chefles, Richard Jozsa, Andreas Winter, *On the existence of physical transformations between sets of quantum states*, International Journal of Quantum Information 2, 11–21 (2004), [arXiv:quant-ph/0307227](https://arxiv.org/html/quant-ph/0307227), DOI [10.1142/S0219749904000031](https://doi.org/10.1142/S0219749904000031)。定理 1 的 qubit 两态迹范数判据与定理 2 的纯态 Gram 转换判据为 `literature-attested`；它们不把“每对存在过程”提升为“全族共用同一过程”。

**文献 9.3（转置与物理近似）。** [BDPS03] Francesco Buscemi, Giacomo Mauro D'Ariano, Paolo Perinotti, Massimiliano F. Sacchi, *Optimal realization of the transposition maps*, Physics Letters A 314, 374–379 (2003), [arXiv:quant-ph/0304175](https://arxiv.org/html/quant-ph/0304175), DOI [10.1016/S0375-9601(03)00954-X](https://doi.org/10.1016/S0375-9601(03)00954-X)。其 §2 给任意有限维纯态转置的最优通用保真度近似。转置正而非完全正、qubit 通用转置近似及相应 $1/3$ 阈值为 `literature-attested`。本卷固定有限纬线输入的最坏迹距离目标与该全文纯态通用保真度目标不同。

**文献 9.4（相位协变转置的邻近问题）。** Francesco Buscemi, Giacomo Mauro D'Ariano, Chiara Macchiavello, *Economical realization of phase covariant devices in arbitrary dimensions*, Journal of the Optical Society of America B 24, 363–370 (2007), [arXiv:quant-ph/0606120](https://arxiv.org/html/quant-ph/0606120), DOI [10.1364/JOSAB.24.000363](https://doi.org/10.1364/JOSAB.24.000363)。原文以等模赤道态及其保真度为相位协变克隆、转置与估计的目标，属于 `literature-attested` 的相邻研究。本文的非赤道有限资料、互补输入与最坏迹距离目标分别按定义 3.1、4.1、5.1 固定。

**文献 9.5（本卷推导的范围）。** 内部准备菜单使用标准的来源纯化条件化与非最大纠缠 Choi 接口，不作为新一般工具。定理 3.2 的纬线三态联合约束，定理 4.2 的唯一根修复，定理 5.2 的互补框架修复与最佳纬度，定理 6.3 对 V93 指定完成的六轴修复，以及定理 6.2、7.1 的退化和换锚接口，按这里明确的有限对象及目标作 `repo-derived` 推导。该归属指本文所给的综合推导，不声明文献原创优先权。它们使用既有正延拓、Choi 表示、凸对称平均及 qubit 通道数学；未将这些中间工具改名认作新增内容。

## 追加锚（本行以下为增补区）
