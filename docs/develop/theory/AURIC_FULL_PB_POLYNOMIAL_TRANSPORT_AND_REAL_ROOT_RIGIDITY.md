# AURIC：全 PB 多项式运输与实根刚性

**定义 0.1（原域、候选与外卷记号）。** 称[《原多项式零响应与 Cayley 原域边界》](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)为原多项式卷，称[《配平三角的共同取向与秩一响应续卷》](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md)为配平主卷，称[《任意维小窗口单位桥》](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md)为单位桥卷，称[《任意维静态量子重构》](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md)为静态重构卷，称[《中央响应平方与径向一致》](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md)为中央响应平方卷，称[《移位单位铅笔与非中央平方的配对一致》](AURIC_SHIFTED_UNIT_PENCILS_AND_NONCENTRAL_REFERENCE_CONSISTENCY.md)为移位单位铅笔卷。本卷编号为 §§1–5；带卷名的编号只指相应外卷。原多项式卷 §§8–11 的通勤图成果及 §§12–14 的自由词无正交锚成果均为外卷既有结果。

一般原候选准确沿用配平主卷定义 128.1、183.1 及单位桥卷的同一 $(E,C,u,N,\mathcal P,S,D)$：$E$ 是自身含单位实 JB 完成 $X$ 中的含单位范数稠密实 Jordan 子代数，$C=E\cap X_+$，原正实线性评价族分离 $E$ 并准确决定 $C$，$S(a,b)=a\circ b$。A1 为全部原有向 Hermitian 二表正性，A2 为相加三表及其排列的实部正性和指定相加向量的零二次值，A3 为 $S(u,u)=u$ 和同一固定有理 $0<\theta\le1$ 下 $0\le e\le\theta u\Rightarrow S(e,e)\le e$；全部原 P2、完整 PB 及其元素式取配平主卷 (128.3)、(128.4)、(128.6)。保留全部原输入、评价及零／不等／次归一质量，不给未知一般 $D$ 预付可加、齐次、连续、可测、单位平移或完成延拓。

本卷全路径定理固定原多项式卷定义 8.1 的标准模型。对每个整数 $n\ge2$、区间坐标 $t\in[0,1]$，令

$$
\begin{aligned}
E_n&=\left\{\lambda I_n+\sum_{k=1}^{m}t^kA_k:
 \lambda\in\mathbb R,\ m\in\mathbb N_0,\ A_k\in M_n(\mathbb C)_{\rm sa}\right\},\\
\mathcal A_n&=\{F\in C([0,1],M_n(\mathbb C)):F(0)\in\mathbb C I_n\},\\
X_n&=(\mathcal A_n)_{\rm sa},\qquad u=I_n,\qquad
S(F,G)=F\circ G=(FG+GF)/2,\\
D_*(F,G)&=\frac{\mathrm i}{2}(FG-GF),\qquad
C_n=E_n\cap(X_n)_+,\qquad
N(F)=\sup_{0\le t\le1}\|F(t)\|_{\rm op}.
\end{aligned}
\tag{0.1}
$$

原评价为 $\mathcal A_n$ 上全部数学正泛函在 $E_n$ 的限制及其非负质量倍数；它们分离原域并准确决定锥，质量不归一。$m$ 遍取全部有限次数，没有共同次数上界，零点只容许实标量矩阵。原多项式卷定义 8.1 已给稠密性、不完备性和无非平凡原投影；静态重构卷定义 35.1、定理 35.2 以 $\mathcal A=\mathcal A_n$、$\mathcal A_0=E_n+\mathrm iE_n$、$\kappa=1$ 供应全部原 A1–A3、P2、全有限复正表与完整 PB，且 $S-\mathrm iD_*$ 就是同一参考乘法。数学读取不成为实际准备，点纤维矩阵不成为原轴。以下是这个固定完整模型中的普通纸面数学推导；一般未知 $D$ 的命题仅限 §4 的单边结论。

## 1. 全部原全 PB 外层对的多项式运输

**定义 1.1（全 PB 图与复编码）。** 沿用原多项式卷 §§8–11 的同一完整矩阵模型

$$
E_n,\quad X_n,\quad u=I_n,\quad
D_*(F,G)=\frac {\mathrm i}{2}(FG-GF),
$$

以及静态重构卷 35.1–35.2 所支付的 A1–A3、P2 与完整 PB。定义无向图
$\mathcal H_n$，其顶点是全部 $E_n^2$，但对每一个原有自伴三元组
$p,q,r\in E_n$ 都加入一条边

$$
 (q+\nu,r+\omega)\ \longleftrightarrow\ (q-\nu,r-\omega),
\qquad
\nu=D_*(p,q)-p\circ r,\quad
\omega=p\circ q+D_*(p,r).
\tag{1.1}
$$

这里不要求任何交换性、零内层响应、零 Jordan 预算、共同生成代数、范数、次数、链长或满秩条件。边本身是完整 PB 的实际外层响应比较，$\nu,\omega$ 是该三元组的实际预算，不是把两个旧输出相等写入定义。原多项式卷定义 8.2 的图满足 $\mathcal G_n\subseteq\mathcal H_n$；$\mathcal H_n$ 还包含该外卷 §§8–11 没有授予的非通勤与非零内层边。连通分量只指任意有限条边组成的路径，包含长度零，不取路径极限或完成中的闭包。对有序对写

$$
\mathbf Z(x,y)=x+\mathrm i y.
$$

直接展开 (1.1)，没有使用交换性，得到

$$
\mathbf Z(q+\nu,r+\omega)=(I_n+\mathrm i p)\mathbf Z(q,r),
\qquad
\mathbf Z(q-\nu,r-\omega)=(I_n-\mathrm i p)\mathbf Z(q,r).
\tag{1.2}
$$

例如，$\nu+\mathrm i\omega=\mathrm i p q-p r=\mathrm i p(q+\mathrm i r)$。因此 (1.2) 是对全部全 PB 边的精确编码，而不是给未知一般 $D$ 增添连续性或完成延拓。

**定理 1.2（全 PB 图上的线性轮廓精确分量）。** 取任意 $n\ge2$、任意自伴常矩阵 $A,B\in M_n(\mathbb C)_{\rm sa}$，只要求

$$
Z_0=A+\mathrm iB\ne0.
\tag{1.3}
$$

则在全 PB 图中

$$
\boxed{
\operatorname{Comp}_{\mathcal H_n}(tA,tB)=
\left\{\bigl(t(cA-sB),\ t(sA+cB)\bigr):c,s\in\mathbb R,\ c^2+s^2=1\right\}.}
\tag{1.4}
$$

不要求 $A^2+B^2$ 可逆，亦不要求 $A,B$ 或任何外层标签彼此通勤。除半周外的每个整体转角由一条边实现，半周由两条边实现。

证明。设一条全 PB 边与 $(tA,tB)$ 相邻。按需要交换边的两个端点，存在 $\varepsilon\in\{1,-1\}$、$p\in E_n$ 及 $Z=q+\mathrm i r$，使

$$
 (I_n+\varepsilon\mathrm i p)Z=tZ_0.
\tag{1.5}
$$

写 $p(0)=\lambda I_n$。由 (0.1) 的零点条件，(1.5) 在 $t=0$ 给 $Z(0)=0$，故 $Z=tW$；这里 $W$ 只是系数恒等式中的复矩阵多项式，不是送回原 $D$ 的新输入。区间上的等式因此给出多项式恒等式

$$
(I_n+\varepsilon\mathrm i p)W=Z_0.
\tag{1.6}
$$

对每一个实数 $s$，$p(s)$ 是 Hermitian，故其谱值为实数，且

$$
\left\|(I_n+\varepsilon\mathrm i p(s))^{-1}\right\|_{\rm op}
=\max_j(1+\lambda_j(p(s))^2)^{-1/2}\le1.
\tag{1.7}
$$

由 (1.6) 得 $\|W(s)\|_{\rm op}\le\|Z_0\|_{\rm op}$ 在整条实轴成立。每个矩阵元是有界复系数多项式，遂为常数；记该常矩阵为 $C$。在零点取 (1.6) 得

$$
C=(1+\varepsilon\mathrm i\lambda)^{-1}Z_0.
\tag{1.8}
$$

同一条边的另一端编码为

$$
(I_n-\varepsilon\mathrm i p)tC
 =t(2C-Z_0)
 =t\frac{1-\varepsilon\mathrm i\lambda}{1+\varepsilon\mathrm i\lambda}Z_0.
\tag{1.9}
$$

这个商是模一复数。注意 (1.9) 只使用 $pC$ 已由 (1.6) 固定；不需要从 $C$ 可逆推出 $p$ 是标量。因此第一步的任意演员即使非通勤、非标量、带有非零内层响应，其外层仍只留下同一个整体相位。相位倍乘保持 (1.3)，对路径长度归纳得到 (1.4) 的左包含。

反向取任意 $\rho\in\mathbb C$ 且 $|\rho|=1$。当 $\rho\ne-1$ 时存在 $\mu\in\mathbb R$ 使 $\rho=(1-\mathrm i\mu)/(1+\mathrm i\mu)$。取原演员 $p=\mu I_n$，并以

$$
Z=\frac{t}{1+\mathrm i\mu}Z_0
$$

的 Hermitian 实部和虚部分别作 $q,r$。因 $t$ 在零点消失，$q,r\in E_n$；(1.2) 的两端正是 $tZ_0$ 与 $\rho tZ_0$。当 $\rho=-1$ 时连续取两条 $\mu=1$ 的边。恒等转角取长度零，故右包含成立。∎

## 2. 任意多项式轮廓的根判据

**定理 2.1（全 PB 多项式运输的实根当且仅当）。** 取任意 $n\ge2$，设 $f\in\mathbb R[T]\setminus\{0\}$ 且 $f(0)=0$，取 $A,B\in M_n(\mathbb C)_{\rm sa}$ 使 $Z_0=A+\mathrm iB\ne0$。令

$$
\mathcal O_f(Z_0)=
\left\{f(t)(cA-sB,\ sA+cB):c^2+s^2=1\right\}.
\tag{2.1}
$$

则

$$
\boxed{
\operatorname{Comp}_{\mathcal H_n}(fA,fB)=\mathcal O_f(Z_0)
\quad\Longleftrightarrow\quad
f\text{ 的全部复根都是实根（按重数计）。}}
\tag{2.2}
$$

证明。先设所有根实。考虑任意相邻边，并按端点方向写成

$$
 (I_n+\varepsilon\mathrm i p)Z=fZ_0,
\qquad p\in E_n,\quad Z=q+\mathrm i r.
\tag{2.3}
$$

令 $M_\varepsilon=I_n+\varepsilon\mathrm i p$。在每个实数 $s$ 处，$M_\varepsilon(s)$ 可逆，因为 $p(s)$ Hermitian。若 $\xi\in\mathbb R$ 是 $f$ 的根，重数为 $m$，则在局部商环

$$
\mathbb C[T]/((T-\xi)^m)
$$

中，$\det M_\varepsilon(\xi)\ne0$ 使其行列式的类为单位，伴随矩阵公式给 $M_\varepsilon$ 的类可逆，而右端的类为零，所以 (2.3) 给出 $Z\equiv0\pmod{(T-\xi)^m}$。这一步只是有限多项式环中的可逆矩阵消元；它没有在原域加入 $\xi$ 或调用未知响应。所有根均实且相互素的根因子合并后，得到逐矩阵元的整除关系

$$
Z=fW,\qquad W\in M_n(\mathbb C[T]).
\tag{2.4}
$$

把 (2.4) 代回 (2.3) 并在多项式环中消去非零的 $f$，得

$$
M_\varepsilon W=Z_0.
\tag{2.5}
$$

同 (1.7)，$W$ 在整条实轴有界，故 $W=C$ 为常矩阵。零点给出 (1.8)，另一端仍由 (1.9) 变成同一轮廓乘以模一标量。对任意有限路径归纳，得到分量包含于 (2.1)。

反向仍只需标量演员。给定任意模一 $\rho\ne-1$，取 $\mu\in\mathbb R$ 使 $\rho=(1-\mathrm i\mu)/(1+\mathrm i\mu)$，并令

$$
Z=\frac{f(t)}{1+\mathrm i\mu}Z_0.
$$

由于 $f(0)=0$，其 Hermitian 实部和虚部属于 $E_n$，(1.2) 给出从 $fZ_0$ 到 $\rho fZ_0$ 的一条边；$-1$ 仍由两边得到。因此实根条件下 (2.2) 成立。

现在设 $f$ 有非实根 $a+\mathrm ib$，其中 $b>0$。写

$$
f(T)=g(T)((T-a)^2+b^2),
\qquad g\in\mathbb R[T],\qquad g(0)=0,
\tag{2.6}
$$

最后一个等式由 $f(0)=0$ 与 $a^2+b^2>0$ 得到。取合法的实标量演员

$$
p(T)=\frac{T-a}{b}I_n
$$

和复矩阵多项式

$$
Z(T)=-\mathrm i b\,g(T)(T-a+\mathrm ib)Z_0.
\tag{2.7}
$$

因为 $g(0)=0$，把 $Z$ 的点态 Hermitian 实部、虚部分别记为 $q,r$ 后，$q,r\in E_n$；这里 $`Z^*`$ 只表示逐点共轭转置。直接相乘给

$$
(I_n+\mathrm i p)Z=fZ_0,
\qquad
(I_n-\mathrm i p)Z=-g(T)(T-a+\mathrm ib)^2Z_0.
\tag{2.8}
$$

故 (2.8) 是一条合法的全 PB 边，而第二端不在 (2.1)。若它等于某个常数 $\rho fZ_0$，在 $Z_0$ 的任一非零矩阵元上取值并在多项式环中约去非零的 $g$，便会要求

$$
-\frac{(T-a+\mathrm ib)^2}{(T-a)^2+b^2}
=-\frac{T-a+\mathrm ib}{T-a-\mathrm ib}
$$

为常数，这是不可能的。于是一个全 PB 边就离开了整体轮廓，(2.2) 的“仅当”成立。∎

## 3. 同一完整模型中的应用与逃逸

**命题 3.1（旁观者分块在全 PB 图中仍不可达）。** 在原多项式卷 §10 的 $n=4$ 原模型中，令

$$
a=t\sigma_x\otimes I_2,\quad b=t\sigma_y\otimes I_2,\quad
\widetilde a=t\sigma_x\otimes\sigma_z,\quad
\widetilde b=t\sigma_y\otimes\sigma_z.
\tag{3.1}
$$

则 $(\widetilde a,\widetilde b)\notin\operatorname{Comp}_{\mathcal H_4}(a,b)$。

证明。这里 $Z_0=\sigma_x\otimes I_2+\mathrm i\sigma_y\otimes I_2\ne0$，故定理 1.2 给出的分量只是

$$
\bigl(t(c\sigma_x-s\sigma_y)\otimes I_2,
t(s\sigma_x+c\sigma_y)\otimes I_2\bigr),\quad c^2+s^2=1.
$$

若 (3.1) 的目标属于其中一项，则第一坐标要求
$\sigma_x\otimes\sigma_z=(c\sigma_x-s\sigma_y)\otimes I_2$，与原多项式卷命题 10.1 所用的部分迹和 Pauli 线性无关性矛盾。这里的图已经允许任意非通勤演员和非零内层全 PB 边，所以该分离比原多项式卷命题 10.1 的通勤图分离更强。另一方面，显式模型仍有

$$
D_*(a,b)=D_*(\widetilde a,\widetilde b)=-t^2\sigma_z\otimes I_2.
\tag{3.2}
$$

因此它不是旧 $D$ 值不同的反例，也不是 PB、可加性或完整量子来源的不可能性定理。∎

**命题 3.2（三次轮廓的整体相位轨道逃逸）。** 取 $f(t)=t(1+t^2)$。对任意非零
$Z_0=A+\mathrm iB$，令

$$
Z=t(1-\mathrm it)Z_0,\qquad
q=\frac{Z+Z^*}{2},\quad r=\frac{Z-Z^*}{2\mathrm i}.
\tag{3.3}
$$

取原标量演员 $p=tI_n$，则

$$
(I_n+\mathrm ip)Z=fZ_0,\qquad
(I_n-\mathrm ip)Z=t(1-\mathrm it)^2Z_0.
\tag{3.4}
$$

所以一个合法全 PB 边从轮廓 $fZ_0$ 直接逃出其整体 SO$(2)$ 相位轨道；这条边本身仍是合法的有限运输，被破坏的是整体相位轨道刚性。在 $f\in\mathbb R[T]\setminus\{0\}$、$f(0)=0$ 的轮廓类中，一次多项式只有零根，二次多项式除零根外的另一根也必为实数，故它们的全部复根（按重数计）均为实根。由定理 2.1，整体相位轨道逃逸的首个可能轮廓次数准确为三，本例实现它。该次数只属于上述实多项式轮廓类，不主张资源、物理或其他函数类的最小性。∎

## 4. 未知旧关系的一步边界

**命题 4.1（P2 对单条全 PB 边的旁观者压缩）。** 沿用定义 0.1 中一般原候选的准确锥、决定锥的评价族和全部原 P2，在已给忠实、锥准确的 JC 包含及其忠实算子表示中记原标签为其像。设 $P$ 是该表示的环境正交投影，且对某条候选全 PB 边的中点标签 $q,r$ 有

$$
qP=rP=0.
\tag{4.1}
$$

对任意原演员 $p$，未知总映射 $D$ 满足

$$
P D(p,q)P=P D(p,r)P=0,\qquad
P(p\circ q)P=P(p\circ r)P=0,
$$

从而

$$
P\nu P=P\omega P=0,\qquad
\nu=D(p,q)-p\circ r,\quad\omega=p\circ q+D(p,r).
\tag{4.2}
$$

证明。对每个支撑在 $P$ 上的环境向量 $\xi$，读取 $\phi_\xi(x)=\langle\xi,x\xi\rangle$ 限制到原 $E$ 后是数学正实线性泛函。配平主卷引理 129.1 由原评价准确决定锥，使每个这样的读取都能合法读取同一原 P2；它不必是实际准备，零向量和任意非负质量倍数亦保留。由 (4.1)，$\phi_\xi(q^2)=\phi_\xi(r^2)=0$。分别读取原二表 $(p,q)$、$(p,r)$，半正定矩阵的一个对角元为零，迫使相应的复非对角元为零；其虚部和实部分别给

$$
\phi_\xi(D(p,q))=\phi_\xi(D(p,r))=0,\qquad
\phi_\xi(p\circ q)=\phi_\xi(p\circ r)=0.
$$

四个算子均自伴，对 $P$ 的像内全部向量作复极化，得到四个压缩恒等式，再代入 (4.2)。这里只压缩固定的原输出，没有对 $P$ 调用旧 $D$，也没有把数学环境投影 $P$ 当作原事件或原演员。∎

在 (3.1) 的原多项式模型中，若尝试用一条未知全 PB 边直接连接两个端点，中点必为真正原标签

$$
q=t\sigma_x\otimes p_+,\qquad r=t\sigma_y\otimes p_+,\qquad
p_+=\frac{I_2+\sigma_z}{2}.
$$

固定任意 $0<t\le1$，只在此点的数学矩阵读取中令 $P=I_2\otimes p_-$、$p_-=(I_2-\sigma_z)/2$，则 $q(t)P=r(t)P=0$。定义 0.1 的原评价族包含全部 $\phi_{t,\xi}(F)=\langle\xi,F(t)\xi\rangle$ 及其非负质量倍数，故上述零对角和极化论证对这些合法点读取直接给

$$
P\nu(t)P=P\omega(t)P=0.
$$

然而端点差的半量在这同一点的压缩下是

$$
P\frac{a(t)-\widetilde a(t)}2P=t\sigma_x\otimes p_-\ne0,\qquad
P\frac{b(t)-\widetilde b(t)}2P=t\sigma_y\otimes p_-\ne0.
$$

这与候选边所需的位移矛盾。因此任何满足原 P2 的未知 $D$ 都不能用一条全 PB 边完成这两个端点的连接。这里没有在点纤维上定义 $D$，没有假定响应下降，也没有把常矩阵 $P$ 作为原多项式域的全局投影或原演员。这个结论只是一条边的必要条件；它没有把未知 $D$ 的任意有限路径分类，也没有替代定理 1.2 在显式完整 $`D_*`$ 模型中的全路径结论。

## 5. 消费者、来源与完整边界

**定义 5.1（模型、既有识别与来源合同）。** 原多项式卷定义 8.1 至定义 11.2 的完整原矩阵模型、所有原评价和质量、投影稀缺、完整 PB、通勤图端点分离及来源合同均按外卷原量词复用。本卷在该模型上研究全 PB 图 $\mathcal H_n$ 和多项式轮廓判据；原多项式卷 §§8–11 的成果不改作未知一般 $D$ 的结论。[《配平三角的共同取向与秩一响应续卷》](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md)定义 240.1（原资料、数学商与任意原像）、定理 240.2（有限商类型与一般 JC 载体）及定理 248.1（一般原 JB 候选内生支付特殊表示前件），供应一般 JB 背景和忠实、含单位、等距、锥准确的 JC 包含；不要求整个完成等于环境自伴部。[《任意维静态量子重构》](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md)定义 35.1（参考族，不是任意原 D 的免费前件）、定理 35.2（实方向盲区及全 PB 的尺度选择），以原多项式卷定义 8.1、亦即本卷定义 0.1 的 $\kappa=1$ 参数供应本卷显式标准 C* 参考模型的完整静态条件和 PB，不是一般 JB 载体定理。配平主卷 128.1、183–185 的原候选、单位行、SO$(2)$ 标签对称和完整 PB 元素式仍是同一承重来源；这些引用不是新增公理。

中央响应平方卷 §§53–59 是 $a^2\in Z(X)$、$\|a\|<1$ 分支的带权中央平方与 Gram 模块：54.1 给 $T_a^2=-a^2$ 的自身平面关系，55.1 给原中央系数模块及其输出返回，56.1 给中央 Gram 横向窗口，57.1 给带权三元消费者。首槽单位移位与第二槽 $h$ 分量的配对关系则准确来自[《移位单位铅笔与非中央平方的配对一致》](AURIC_SHIFTED_UNIT_PENCILS_AND_NONCENTRAL_REFERENCE_CONSISTENCY.md)定理 2.1（同一原行的配对移位铅笔）：对原 $h^2=u$、$x\in V_h$、该卷奇周期列 $r_n$ 及全部实 $s,v$，同一旧值为 $D(sh+vu,x+r_n(su+vh))=sJ_hx$。这些已取得的条件结果分别按其原前件复用，不混同为一般单位平移。

中央响应平方卷 §§60–67 已支付：对任意真实原实子空间 $W_0\subset E$，若每个 $x\in W_0$ 满足 $x^2\in\mathbb Ru$，则同一个旧 $D|_{W_0^2}$ 实交替双线性，不要求 $D(W_0,W_0)\subset W_0$；每对原正交单位方向及其响应生成闭合三轴，四方向窗口仍可不闭合。该卷 §§68–75 的带单位余量界由 §§76–78 的实际旧值识别接全：引理 76.2 用一次真正横向／纯输入 PB 得到 $D(x,Tu+y)=x\times y$；定理 77.1 对其原生成三轴 $U$ 的全部实 $s,t$ 及 $x,y\in U$ 给出

$$
D(su+x,tu+y)=x\times y.
\tag{5.1}
$$

因此该三轴窗中的全部 $P>W$ 余量也为零，不再留下这个分支的单位平移或输出闭合缺口。推论 77.2 进一步给任意上述标量平方片 $W_0$ 上的同一旧值 $D(su+x,tu+y)=D(x,y)$ 及其仿射片上的实交替双线性，不要求输出闭合；推论 78.1 在实际生成的四维窗 $\mathbb Ru+U$ 复化上识别内在 $M_2(\mathbb C)$ 乘法、准确锥、原 $R$ 和全部有限复 Gram 正性。这些都是已取得的条件结论，按其真正原单位轴和原输入范围复用，不在本卷重复证明。一般非标量平方输入、全原 $E$ 的旧响应拼接及实际来源生产者仍须另付。

在 (0.1) 的指定原域中，原多项式卷定义 11.1 已说明原 $h^2=u$ 只有 $h=\pm u$，故标量平方窗口至多为单位实线，不能从点纤维的 Pauli 矩阵制造上述真正原三轴。中央卷的局部旧 $D$ 识别与本卷固定 $`D_*`$ 的全 PB 图分量定理保持各自的前件和量词；(5.1) 不覆盖本卷 (1.4) 或 (2.2)。

原多项式卷 §§12–14 的自由词原域是另一份完整标准模型：其同一非零标准响应满足全部原 A1–A3、P2 和完整 PB，而整个原 $E$ 没有非零 Jordan 正交对。因此该外卷已排除所有先供应非零精确原正交锚的有限原域方法；这个全原域入口障碍既不依赖也不分类本卷的多项式运输图。自由词模型中的 $D$ 本来双线性；它不是非可加／全 PB 反模型，不是实际来源反模型，也不代替本卷的实根充要判据。

全原候选的七项量子消费者仍逐项按中央响应平方卷定义 52.1 的表及配平主卷定义 250.1 的完整合同消费：其一，复 Hilbert、可观测量和叠加仍须全域旧 $D$ 实双线性及静态重构卷 32.2、23.1、33.2 的复正表、原 $R$ 与结合乘法；其二，态、效果、质量和 Born 只在原实际完整菜单与严格正质量上使用，零、不等和次归一质量保留；其三，native、真实相关联合与张量仍须同一实际共同来源；其四，整台递归同源参考的 CP、箭头下降和所有成功／失败／记录输出仍须原运输；其五，完整仪器、TP、Kraus、更新和 Lüders 仍须完整实际输出接口及各自校准；其六，全部历史、未来、遗忘、停止、拒绝、销毁及真实双向返回仍保持原定义；其七，物理动力学、Hamiltonian、物理钟、能量、作用量和共同正 $\hbar$ 仍需各自来源。定理 1.2、2.1 只给数学标签图的有限路径，命题 4.1 只给未知 $D$ 的一步必要条件；三者都不供应上述七项中的实际 producer、ready、menu、full-output/future return 或物理尺度。

七项消费者同时逐行采用 C139 定义 155.1、复用命题 155.2 的全部原递归合同；上述说明不替代任一行的前件，也不把局部旧值识别当作全域识别。

同一完整根候选逐句保持 [C139 定义 155.1](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md)所纳入的 147.1–147.3、139.1–139.2 及全部递归原前件，即同一 $\mathsf Q^{\rm root}_{46}$，根关系仍为

$$
s=(3,7,1,2,4,5,6,8,9),\qquad
\operatorname{tr}(L_r^\dagger L_r)=2,\qquad
\|U_si_rL_r\|_{\rm HS}^2\le2
\quad(r\in\mathfrak K_{\rm r}).
\tag{5.2}
$$

整个原根类、$\rho=0$、$k=0$、全部静态十一端点、XV23.2 与全原 E1 的等价、同一 ready 两标量词及 176 有界长度选项各守原域；零活动量、零根响应及其合法未来不删，根迹不作准备。静态各入口的全部原 $E,u,\mathcal P,S,D$、准确锥／范数、全实部式、原输出辨识，以及有限响应、指定完整 II$_1$ 和整个 $F_3$ 域等分支均按该定义原样消费，不以摘要替代其前件。

原 $\Omega/\mathrm{native}$ 的全部对象、准备、事件、设备、程序／过程、全词与跨标签同一 $K/J/q$，原 $J,S,U,D_{\rm network},C,G,M_j,N_j,AS,R_2$ 及完整模式网络，中心／经典／不等维块与静默域、零／不等／次归一质量、真实乘积和全部相关联合、参考／副本及递归同源引用、控制、ready、旗标、环境、钟／单位、同一 $\sigma,t_0$ 和 $B/B_{\rm cl}$ 均保留。所有原菜单、固定支持 $S$ 的全质量及每个已量化切口、全部合法顺序／自适应／并行历史、全输出／细记录和每个仍合法未来、真正分组遗忘、失败／拒绝／停止／销毁／泄漏、同数两侧和真实逆向返回不缩减；未定义请求不补零，同矩阵的不同原程序分别承担覆盖。

共同根、实际端口、原角／二十七模适配器、完整坐标分区、真实彩票及每条所用平衡行、每个原 $(\xi,g,s)$ 先 $`g^*`$ 再 $`d_s^*`$ 最后同一原根的次序与菜单归属，均保持 C139 定义 155.1 的完整来源。原 $\mathrm C_{12}$、mark、预定有限强度尺、$\mathrm A_{12}$、全背景 $\mathrm{BI}_{12}$、最小可见／实尺度、P9 各支独立 $W_e$、原强度和质量校准、接受归属、其它块 AS／EC、菜单外 OB、真实忠实二维到三维全质量角和非零一维块不删；两只独立九叶彩票 $(6,2,0)/9$、$(4,4,0)/9$、各自第九空程序、十六拒绝叶及相干 $I_3/3$ 返回不改成经典细测。C139 150–156 的实际混合、反差连通、全实对偶张成校准和相应标量整台返回，以及 C139 固定实源卷 50–73、C128 385–392 的原下降、参考、递归支持与旧值恢复，均按各自原合同作为已取得结果复用；这些已得结果不供应尚缺的 CountRead 终端到 active-AS、all-old-menu 或 full-output/all-future true-ready 生产者。

**定义 5.2（候选归属与未结算桥）。** 定理 1.2、2.1、命题 3.1–4.1 是在已付静态模型中的 $\texttt{repo-derived}$ 运输综合。成熟工具只是矩阵谱定理、Hermitian Cayley 因子在实轴上的逆范数界、有限多项式根因子与局部商环可逆性、基本 Pauli 计算；van de Wetering 的 JC 通勤结果、Hanche–Olsen–Størmer 的 JC/JB 表示工具与中心读取只按原多项式卷 §§8–11、中央响应平方卷 §§53–59 已列前件使用，不承担 (1.4) 或 (2.2) 的优先权。全 PB 图的“所有演员”是显式 $`D_*`$ 模型中的数学许可，不是从原 $\Omega$ 生成新的物理演员。

因此，在定义 1.1 的指定全 PB 图中，即使允许任意非通勤演员、非零 PB 内层响应和任意有限步数，也不能到达 (3.1) 的独立旁观者块端点。这个止点只限制该图的运输策略；没有证明一般未知旧 $D$ 的全局双线性、取向、原 $R$、一般首槽单位平移、完整七项消费者、上述实际生产者、真实返回或量子起源不可能。中央响应平方卷 §§60–80 已取得的条件结论完整保留，包括全部生成三轴窗的带单位旧值识别；一般非标量平方输入、全原 $E$ 及实际来源的剩余合同亦保留。其他多三元组网络或等式组合仍未被这些图分量和单边结论排除。数学矩阵、函数系数、旁观者投影或多项式外推不成为实际准备、过程、记录、失败、停止、销毁、联合、时钟、能量、作用量或 $\hbar$。

**定义 5.3（完整白话）。** 同一个完整的原矩阵世界里，先把所有合法的全 PB 外层比较都放进一张图；不论演员是否通勤、内层响应是否为零，每条边在两个标签的复记号上都只是左乘一个 $I\pm\mathrm ip$。从线性轮廓 $f(t)=t$ 开始：原演员在零点只能是实标量，Hermitian Cayley 因子的逆在整条实轴上不放大，约掉 $t$ 后的多项式只能是常量。因此只要常矩阵对不全为零，不论它的非零秩是多少，都只能让两个标签一起转同一个整体相位；不要求满秩或可逆，也不要求交换性、零内层响应、次数上界或路径长度上界，这个结论包括每一条有限路径。

对任意非零实多项式 $f$ 且 $f(0)=0$，整体相位轨道刚性的准确条件是它的全部复根都落在实轴上，并保留每个根的全部重数。实根条件下，每个重因子都能在有限多项式环里消去，之后由实轴有界性和原标量零点再次只留下整体相位；出现一对非实共轭根时，一条合法全 PB 边就能扭出该轨道，而这条边仍是有限运输。区间外实数的取值只用于已知矩阵多项式系数恒等式及其界的数学证明，不扩张原输入区间 $[0,1]$，不增加原输入或未知 $D$ 调用，也不解释为物理时间。

旁观者块的“不转／半周”要求因此在一个已经允许全部全 PB 演员的显式模型中仍不可达，而同一模型的两端旧响应可以完全相同。中央卷已从真正原单位轴取得的多方向双线性、三轴生成、整个带单位三轴窗的旧值识别及内在复矩阵乘法各守原范围；不能用本模型点纤维中的数学轴替换它们的原轴。这些几何描述原标签之间的数学关系，不制造真实准备、菜单、仪器、历史、未来、返回、计数、时钟或物理尺度；同一完整根候选、七项消费者及完整量子起源目标继续按原来源合同保留。

## 追加锚（本行以下为增补区）

## 6. 完整 C* 原域上的独立条件分支

**定义 6.1（原候选及引文身份）。** 本节起另取任意已完成的含单位复 C* 代数 $A$，原域准确为 $E=A_{\rm sa}$，原结构为

$$
S(a,b)=a\circ b=(ab+ba)/2,\qquad C=A_+,\quad u=1,\quad N(a)=\|a\|.
\tag{6.1}
$$

AH 指[《原原子有限测试分离与同一 PB 的静态重构续卷》](https://github.com/the-omega-institute/trureturing/blob/b1a95e41b9622e9f720e51f9bb899841f5b74ca1/docs/develop/theory/AURIC_ORIGINAL_ATOMIC_SEPARATION_AND_PB_RECONSTRUCTION_CONTINUATION.md)，直接引用版本固定为 `b1a95e41b9622e9f720e51f9bb899841f5b74ca1`。完整原候选严格取 AH42.2，以及 AH66.1 中原关系式 (66.2)–(66.3)；AH 的矩阵模型式 (66.1) 只在下文 UHF 应用中另行要求，不加入一般 $A$ 的前件。以下 W、CC、PT 分别指《任意维小窗口单位桥》、《中央响应平方与径向一致续卷》、《配平三角的共同取向与秩一响应续卷》，直接读取身份为 `3b10aed60f60e4901bae6cf2e160bf439d642e64`。各被引正文内部的简称、逐层引文和固定上游版本保持原身份，不由这些直接读取版本覆盖。

同一原正实线性评价族 $\mathcal P$ 分离 $E$ 并准确决定 $C$；保留同一 $\Omega/\mathrm{native}$、每个原标签、每份原评价及全部质量 $m_\gamma=\gamma(1)$，包括零、不等、次归一和原表示意义下的非正常评价。未知量始终是同一个任意总映射 $D:E^2\to E$。记 $\mathsf H_A(D)$ 为上述完整原关系的合取，其全部有向 A1/P2 为

$$
\begin{pmatrix}
\gamma(a^2)&\gamma(a\circ b)-i\gamma D(a,b)\\
\gamma(b\circ a)-i\gamma D(b,a)&\gamma(b^2)
\end{pmatrix}\succeq0
\quad(a,b\in E,\ \gamma\in\mathcal P),
\tag{6.2}
$$

包含两种次序。A2 保留全部相加三表 $(a+b,a,b)$ 及其排列在整个 $\mathbb R^3$ 上的实部正性和指定相加零方向；A3 保留 $1^2=1$ 及同一固定有理 $0<\vartheta\le1$ 下全部 $0\le x\le\vartheta1\Rightarrow x^2\le x$。每个实际原三元组 $(c;x,y)$ 的完整 PB 为

$$
\begin{gathered}
v=D(c,x)-c\circ y,\qquad w=c\circ x+D(c,y),\\
D(x+v,y+w)-D(x-v,y-w)=-2x\circ v-2y\circ w.
\end{gathered}
\tag{6.3}
$$

所有内外层调用、零、重复、缩放、平移、任意实幅度和背景都在量词内。不预给 $D$ 输入连续性、可测性、齐次性、可加性、协变性、压缩自然性、商下降、双对偶延拓或有限子代数输出闭合。本分支不改变 §§1–5 的多项式原域、指定 $D_*$ 或运输图结论，也不把它们推广到一般未知 $D$。

**定义 6.2（整体角分类与三个 Peirce 块）。** 设 $p\in A$ 为投影，$q=1-p$。对普通符号 $\sigma\in\{\pm1\}$，在全部 $E^2$ 上定义比较映射 $K_\sigma(x,y)=\sigma i[x,y]/2$，不把它认作未知 $D$。本分支的附加条件仅是同一旧映射在整个实际角上的分类：

$$
D(x,y)=K_\sigma(x,y)=\frac{\sigma i}{2}[x,y]
\quad(x,y\in(pAp)_{\rm sa}).
\tag{6.4}
$$

这要求整个 $pAp$，不是仅一份有限矩阵子代数。取实际 $h,e\in(pAp)_{\rm sa}$，满足 $h^2=e^2=p$、$he=-eh$，并记 $p_\pm=(p\pm h)/2$、$\jmath=\sigma i$。于是 $p_+,p_-,q$ 是两两正交且和为 $1$ 的三个实际投影；允许 $p=1$，零角的全部结论取零。

角闭合及准确接口直接复用 W119.2–119.3：角内原输入的输出仍在角中，角单位为 $p$，锥和范数为继承的准确锥与范数，每个原评价标签保留为限制，质量为 $\gamma(p)$；不合并同值限制、不删零限制、不除以角质量。W 式 (120.2) 的全部 PB 因内外层闭合逐值继承。它们不生产实际角准备或压缩仪器；(6.4) 的分类供应仍须来自其自身适用定理。

## 7. 任意环境输入的混合非对角块

**定理 7.1（局部反射的全部混合 Peirce 块）。** 在定义 6.1–6.2 下，对每个实 $R$ 和任意环境自伴输入 $b\in A_{\rm sa}$，存在自伴 $r\in pAp$，使同一实际旧输出满足

$$
\boxed{D(Rh,b)=K_\sigma(Rh,b)+r,\qquad [h,r]=0.}
\tag{7.1}
$$

准确地，写 $b_{st}=p_sbp_t$，其中 $s,t\in\{+,-,q\}$、$p_q=q$，并令 $r_\pm=p_\pm rp_\pm$，则相对于 $p_+\oplus p_-\oplus q$，有

$$
D(Rh,b)=
\begin{pmatrix}
r_+&\jmath R b_{+-}&\jmath R b_{+q}/2\\
-\jmath R b_{-+}&r_-&-\jmath R b_{-q}/2\\
-\jmath R b_{q+}/2&\jmath R b_{q-}/2&0
\end{pmatrix}.
\tag{7.2}
$$

此处保留真正非零的环境交叉块 $pbq,qbp$；未假定 $b\in pAp$ 或 $[p,b]=0$。

证明。AH43.1 由 Hermitian 性和原评价分离给反对称性及零槽；准确锥又把同一张原 P2 送给每个数学正读取 $\phi$，从而

$$
|\phi D(x,y)|\le\sqrt{B_\phi(x,y)},\qquad
B_\phi(x,y)=\phi(x^2)\phi(y^2)-\phi(x\circ y)^2.
\tag{7.3}
$$

这是对原输出的数学读取，不把向量态添加为物理准备。$R=0$ 或 $p=0$ 由零槽成立。以下固定 $R\ne0,p\ne0$、实际 $b$ 及同一个输出

$$
a=Rh,\quad g=D(a,b),\quad k=a\circ b,\quad
j=D(h,e)=\jmath he,\quad n=p+h=2p_+.
\tag{7.4}
$$

已知乘法直接给 $j^2=p$、$e\circ j=0$、$n\circ j=j$。对任意有限实 $t,\alpha$，使用真正原三元组 $(a;te+\alpha n,b)$。角分类只支付其中的已知内调用：

$$
D(a,te+\alpha n)=Rt j,\qquad a\circ(te+\alpha n)=R\alpha n.
\tag{7.5}
$$

另一实际内值保持为 $g$。因此两份真正外层标签准确为

$$
\begin{aligned}
R_+&=t(e+Rj)-k+\alpha n,&S_+&=b+g+R\alpha n,\\
R_-&=t(e-Rj)+k+\alpha n,&S_-&=b-g-R\alpha n.
\end{aligned}
\tag{7.6}
$$

只展开已知 Jordan 运算，完整 PB 的原右端为

$$
\begin{aligned}
D(R_+,S_+)-D(R_-,S_-)
&=-2(te+\alpha n)\circ(Rt j-k)-2b\circ(R\alpha n+g)\\
&=2t e\circ k-2b\circ g-2\alpha(Rt j+V),\\
V&=R\,n\circ b-n\circ k.
\end{aligned}
\tag{7.7}
$$

对两份未知外值分别使用同一 $\phi$ 的 (7.3)，其差的绝对读取至多为 $\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}$。这里没有把任何外值换成比较响应。

为准确提取大 $\alpha$ 系数，令实半内积 $\langle X,Y\rangle_\phi=\phi(X\circ Y)$。对固定自伴 $A,B,n$、实 $\theta$，置 $C_0=B-\theta A$，有纯标量多项式恒等式

$$
\begin{aligned}
B_\phi(A+\alpha n,B+\theta\alpha n)
&=B_\phi(A+\alpha n,C_0)\\
&=\alpha^2B_\phi(n,C_0)+2\alpha\{\langle A,n\rangle_\phi\langle C_0,C_0\rangle_\phi
-\langle A,C_0\rangle_\phi\langle n,C_0\rangle_\phi\}
+B_\phi(A,C_0).
\end{aligned}
\tag{7.8}
$$

这由 Gram 行列式展开即得，半内积退化时也成立。将 (7.7) 的预算除以 $|\alpha|$，只取这些标量多项式的首项，包括首项为零的情形。记 $Z=b+Rk$，得

$$
\begin{aligned}
2|\phi(Rt j+V)|\le{}&\sqrt{B_\phi(n,Z+g-Rt e-R^2t j)}\\
&+\sqrt{B_\phi(n,Z-g+Rt e-R^2t j)}.
\end{aligned}
\tag{7.9}
$$

在一份忠实含单位 Hilbert 表示中计算，内积第一槽共轭线性；此表示不延拓未知 $D$。由 $h$ 在三个块上的值 $1,-1,0$ 和 $n$ 的值 $2,0,0$，直接相乘给

$$
\begin{gathered}
p_+Vp_-=R p_+bp_-,\qquad p_+Vq=(R/2)p_+bq,\\
p_+Vp_+=0,\qquad (1-p_+)V(1-p_+)=0,
\qquad V=V^*.
\end{gathered}
\tag{7.10}
$$

取单位 $\xi\in(p_-+q)H$，先设 $d=\|p_-\xi\|>0$，令

$$
\eta=j\xi/d\in p_+H,\qquad \|\eta\|=1,\qquad
j\xi=d\eta,\quad e\xi=-\jmath d\eta.
\tag{7.11}
$$

对 $\delta>0$，取向量 $(\xi+\delta\eta)/\sqrt{1+\delta^2}$ 的数学态 $\phi_\delta$，并令实正交投影 $P_\eta^{\mathbb R}z=z-\operatorname{Re}\langle\eta,z\rangle\eta$。任一固定自伴 $W$ 的三个 Gram 条目给出准确等式

$$
\begin{aligned}
\phi_\delta(n^2)&=\frac{4\delta^2}{1+\delta^2},\qquad
\phi_\delta(W^2)=\frac{\|W\xi+\delta W\eta\|^2}{1+\delta^2},\\
\phi_\delta(n\circ W)&=\frac{2\delta\operatorname{Re}\langle\eta,W\xi+\delta W\eta\rangle}{1+\delta^2},\\
B_{\phi_\delta}(n,W)&=\frac{4\delta^2}{(1+\delta^2)^2}
\|P_\eta^{\mathbb R}(W\xi+\delta W\eta)\|^2.
\end{aligned}
\tag{7.12}
$$

又由 (7.10) 及 $j$ 的非对角性，

$$
\phi_\delta(Rt j+V)=\frac{2\delta}{1+\delta^2}
\{Rt d+\operatorname{Re}\langle\eta,V\xi\rangle\}.
\tag{7.13}
$$

把 (7.12)–(7.13) 代入 (7.9)，约去正因子 $2\delta/(1+\delta^2)$，在固定 $t$ 后令 $\delta\downarrow0$。因 $P_\eta^{\mathbb R}(j\xi)=0$，记

$$
A_\xi=\operatorname{Re}\langle\eta,V\xi\rangle,\qquad
z_\pm=P_\eta^{\mathbb R}((Z\pm g)\xi),\qquad u_\xi=e\xi/d=-\jmath\eta,
$$

便得到同一固定 $g$ 的不等式

$$
2|Rt d+A_\xi|\le\|z_+-Rt d u_\xi\|+\|z_-+Rt d u_\xi\|.
\tag{7.14}
$$

这里 $\|u_\xi\|=1$ 且 $\operatorname{Re}\langle\eta,u_\xi\rangle=0$。对固定单位向量 $u$、固定 $z$ 和非零实 $\lambda$，平方差有理化给

$$
\|\lambda L u+z\|-|\lambda|L
=\frac{2\lambda L\operatorname{Re}\langle u,z\rangle+\|z\|^2}
{\|\lambda L u+z\|+|\lambda|L}
\longrightarrow\operatorname{sgn}(\lambda)\operatorname{Re}\langle u,z\rangle.
\tag{7.15}
$$

令 $\epsilon=\operatorname{sgn}R$、$B_\xi=\operatorname{Re}\langle u_\xi,g\xi\rangle$。在 (7.14) 取 $t=L\to+\infty$，两份右侧范数各减 $|R|dL$ 后的极限分别为 $-\epsilon\operatorname{Re}\langle u_\xi,z_+\rangle$、$\epsilon\operatorname{Re}\langle u_\xi,z_-\rangle$，和为 $-2\epsilon B_\xi$；左侧减 $2|R|dL$ 的极限为 $2\epsilon A_\xi$。取 $t=-L\to-\infty$，两份范数的极限逐项反号，和为 $2\epsilon B_\xi$，左侧极限为 $-2\epsilon A_\xi$。两向一起迫使

$$
A_\xi=-B_\xi,\qquad
\operatorname{Im}\langle\eta,g\xi\rangle
=\sigma\operatorname{Re}\langle\eta,V\xi\rangle.
\tag{7.16}
$$

再使用第二份实际伴轴 $e'=j$。由整体角分类，$j'=D(h,j)=-e$，所以 $\eta'=j'\xi/d=\jmath\eta$；同一 $a,b,g,k,V,Z$ 均未更换。设 $G=\langle\eta,g\xi\rangle$、$L_0=\langle\eta,V\xi\rangle$。第一伴轴给 $\operatorname{Im}G=\sigma\operatorname{Re}L_0$；第二伴轴将二者变成 $-\jmath G,-\jmath L_0$，给 $-\sigma\operatorname{Re}G=\operatorname{Im}L_0$。故

$$
G=\jmath L_0,\qquad
\langle j p_-\xi,(g-\jmath V)\xi\rangle=0
\quad(\xi\in(p_-+q)H).
\tag{7.17}
$$

二次齐次性把单位向量结论扩到全部向量；$p_-\xi=0$ 时末式自身为零。令 $M=g-\jmath V$。在 (7.17) 取 $\xi=u+z$，$u\in p_-H,z\in qH$，减去 $z=0$ 的等式，得 $\langle ju,Mz\rangle=0$。$j:p_-H\to p_+H$ 为酉映射，故 $p_+Mq=0$。

取 $z=0$，令 $T=p_-jMp_-$。其二次型 $Q_T(u)=\langle u,Tu\rangle$ 恒零；不要求 $T$ 自伴的复极化公式为

$$
4\langle u,Tv\rangle=Q_T(u+v)-Q_T(u-v)-iQ_T(u+iv)+iQ_T(u-iv)=0.
\tag{7.18}
$$

于是 $T=0$，再用 $j$ 的上述酉性得 $p_+Mp_-=0$。结合 (7.10)，已经识别 $p_+gp_-$ 与 $p_+gq$。

接着取 $\widetilde h=-h$、$\widetilde R=-R$、$\widetilde e=e$。角符号仍为同一个 $\sigma$；演员 $\widetilde R\widetilde h=a$ 和实际输出 $D(a,b)=g$ 完全相同，新的 $\widetilde n=p-h$ 只交换两个角块的角色。刚才的证明因此给 $p_-gq=-\jmath R p_-bq/2$。对 $\xi\in qH$，$a\xi=0$，(7.3) 直接给 $\langle\xi,g\xi\rangle=0$，自伴极化给 $qgq=0$。其余反向块由 $g=g^*$ 得到。

最后 $K_\sigma(a,b)$ 的三个对角块本来为零，非对角块准确如 (7.2)。相减只剩 $r=p_+gp_++p_-gp_-$，它属于 $(pAp)_{\rm sa}$ 并与 $h$ 交换。忠实表示将这些等式返回原 $A$，证明 (7.1)–(7.2)。所有极限只作用于固定 $g$ 的显式标量多项式或向量范数；没有让外层 $D(R_\pm,S_\pm)$、任何变化输入或响应穿过极限。∎

## 8. 块对角环境整行及两份外层缺陷

**定理 8.1（保留任意补角背景的完整行）。** 在定理 7.1 的条件下，若任意环境 $b=b^*$ 满足 $[p,b]=0$，则对所有实 $R$，

$$
D(Rh,b)=K_\sigma(Rh,b).
\tag{8.1}
$$

补角输入 $qbq$ 任意，不要求零、有限谱、有限阶段或有限维。

证明。$R=0$ 或 $p=0$ 已知。其余固定 $a=Rh,g=D(a,b),k=a\circ b$。由 (7.2) 和 $pbq=0$，有 $a,g,k\in pAp$。使用真正原三元组 $(b;a,0)$；反对称性给内值 $D(b,a)=-g$，零槽给 $D(b,0)=0$，所以

$$
D(a-g,k)-D(a+g,-k)=2a\circ g.
\tag{8.2}
$$

两份实际外层对现在均在已分类的整个角内，故此时才可代入 (6.4)，得到

$$
2a\circ g=K_\sigma(a-g,k)-K_\sigma(a+g,-k)
=2K_\sigma(a,k)=\frac{\jmath}{2}[a^2,b]=0.
\tag{8.3}
$$

这里 $a^2=R^2p$。同时 $a\circ K_\sigma(a,b)=\jmath[a^2,b]/4=0$；(7.1) 的 $r$ 与 $a$ 交换，所以 $ar=0$。$a$ 在角单位 $p$ 下可逆，逆为 $h/R$，遂有 $r=0$。整个论证没有把未知 $D(a,pbp+qbq)$ 拆成两项。∎

**命题 8.2（精确外层缺陷、范数与右支撑边界）。** 保持定理 7.1 的任意环境输入，设 $R\ne0$，保留同一 $a,b,g,k,r$。定义两份真正外层缺陷

$$
E_+=D(a-g,k)-K_\sigma(a-g,k),\qquad
E_-=D(a+g,-k)-K_\sigma(a+g,-k).
\tag{8.4}
$$

则完整原 PB 给出

$$
\boxed{E_+-E_-=2Rhr,\qquad \|E_+-E_-\|=2|R|\|r\|.}
\tag{8.5}
$$

对于这一份原输入和原输出，以下四项等价：$D(Rh,b)=K_\sigma(Rh,b)$；$r=0$；$p_+gp_+=0=p_-gp_-$；$E_+=E_-$。此外，两份复外层标签满足

$$
\begin{aligned}
W_+&=(a-g)+\jmath k=a-r+\jmath ba,&W_+p&=W_+,\\
W_-&=(a+g)-\jmath k=a+r-\jmath ba,&W_-p&=W_-,\\
qW_+&=\jmath qba,&qW_-&=-\jmath qba.
\end{aligned}
\tag{8.6}
$$

证明。(8.2) 对一般 $b$ 仍是实际 PB。比较响应的双线性只用于已知 $K_\sigma$，直接给

$$
K_\sigma(a-g,k)-K_\sigma(a+g,-k)
=2K_\sigma(a,k)=2a\circ K_\sigma(a,b).
\tag{8.7}
$$

从 (8.2) 相减即得 $E_+-E_-=2a\circ r=2Rhr$。因 $r\in pAp$ 且 $h^2=p$，C* 恒等式给 $\|hr\|^2=\|rh^2r\|=\|r^2\|=\|r\|^2$，故范数等式成立。四项等价由 (7.1)–(7.2) 及 $R\ne0$ 立即得到。最后将 $g=\jmath(ab-ba)/2+r$、$k=(ab+ba)/2$ 逐项代入，得到 (8.6)。∎

**定义 8.3（尚未支付的同一关系）。** 一般环境输入上尚须从原关系推出的正是 (8.4) 中 $E_+=E_-$，等价地须消去同一输出的两份对角块。式 (8.5) 识别缺口，没有证明该等式，不将它增加为独立公理。在定理 8.1 中两份缺陷分别为零，因为两份实际外层对属于 $pAp$；一般情形只有复标签的右支撑。

具体地，若 $qba\ne0$，则 (8.6) 的 $qW_\pm$ 非零，而且

$$
q(a-g)p=\jmath qba/2,\qquad qkp=qba/2,\qquad
q(a+g)p=-\jmath qba/2,\qquad q(-k)p=-qba/2.
\tag{8.8}
$$

因此 $W_\pm p=W_\pm$ 不把它们的自伴实、虚标签变成 $pAp$ 中的两对输入，不能对 (8.4) 直接调用角分类。$R\ne0$ 时，$qba=0$ 等价于 $qbp=0$，再由 $b=b^*$ 等价于 $[p,b]=0$；这准确说明定理 8.1 所用的支撑入口。

AH5.3 与 PT171.1 的秩一接口另有真实有限秩原提升：由输入及同一输出产生的两向量连同秩一轴位于一个至多三维原角。这里没有那个前件；有限阶段的矩阵秩二角可以在表示中无限维，右理想关系 (8.6) 不生产上述有限角。本命题既未给完整原公理的反模型，也未给一般环境整行或奇数阶段 UHF 的全域分类。

## 9. 既有 UHF 分类供应的直接应用

**推论 9.1（全部实际偶角的混合结论）。** 设 $A$ 是任意无限 UHF，具有 AH66.1 的实际递增满矩阵模型，并满足定义 6.1 的完整原候选；不要求阶段大小为偶。对 AH71.1 的每个实际有限阶段非零偶秩投影 $p$，取任意实际 $h,e\in(pAp)_{\rm sa}$，$h^2=e^2=p,he=-eh$。则定理 7.1、8.1 和命题 8.2 同时成立，且符号是 AH72.1 已取得的同一个普通 $\sigma$。

证明。AH71.2 以 W119.2–119.3 和 W 式 (120.2) 支付整个 $pAp$ 的原接口，再由 AH70.1 支付该整个角的 (6.4)；AH72.1 已支付所有这些实际角的共同符号。直接代入上述三个结果即可，不重证偶维分类或符号拼接，也不假定 $D$ 保持某个有限矩阵阶段。∎

特别，$A=M_{3^\infty}$ 中任一阶段矩阵秩二投影 $p$ 的整个角是 $M_2\otimes M_{3^\infty}$，可直接消费 AH71.2；实际 $h=E_{11}-E_{22}$、$e=E_{12}+E_{21}$ 满足所需关系。环境输入仍遍取整个完成 $A_{\rm sa}$。例如有限阶段 $b=E_{13}+E_{31}$ 确有非零 $p_+bq$，(7.2) 的相应旧响应为 $\jmath R E_{13}/2$；这说明混合结论保留真正环境联系，而非只讨论角内输入。若要由 AH71.2 的更大实际偶角分类读取其余响应，须先有某个实际有限阶段的偶秩投影 $s$，使同一 $h,b\in(sAs)_{\rm sa}$；首个 $M_3$ 阶段的本例不满足此前件，因为 $h,b$ 的共同支撑为 $1$，在所有后续三倍嵌入中仍为奇秩全支撑。一般完成输入的剩余对角桥仍未支付。

**定义 9.2（几何简化与先例范围）。** 新条件结论只用局部 $p_+,p_-,q$ 三块几何及 $(e,j)$、$(j,-e)$ 两份实际伴轴。一旦整个实际角已有分类，定理 7.1 不要求全局半单位投影、全单位 Pauli 对、迹分离、窗口供应或新的输入正则性。减少的是此条件推导所需的额外几何供应，不是原 A1–A3/P2/PB 的独立条数；没有公理最少性、普遍不可能性或完整量子起源结论。

CC147–150 在全单位框架 $h^2=e^2=1$ 下已有实际大标签 PB、共享 Gram 预算、两向范数一次项及双伴轴极化；本证明在局部角单位 $p$ 和任意实强度 $R$ 下重新支付真实外标签及 $q$ 交叉块。CC133–134 的横向行与中央框架、CC159.1 的交叠取向、AH59–60 的全单位反射行及其迹／窗前件均各守原域，不把全单位轴免费替换为 $h^2=p$。此处新增综合归为 $\texttt{repo-derived}$，不将上述已得结论另算新定理。

## 10. 成熟归属与完整量子来源边界

**定义 10.1（证明中间工具的归属）。** Peirce 分解与角乘法规则取 Hanche-Olsen–Størmer，[*Jordan Operator Algebras*](https://hanche.folk.ntnu.no/joa/joa-m.pdf)，§2.6.2、Lemma 2.6.3；完整角接口仍直接消费 W119.2–119.3。忠实 C* 表示、态分离、正泛函和 GNS 的成熟表示背景归于 Gelfand–Naimark，*On the imbedding of normed rings into the ring of operators in Hilbert space*，Mat. Sbornik **12(54)** (1943)，197–217，以及 Segal，*Irreducible representations of operator algebras*，Bull. Amer. Math. Soc. **53** (1947)，73–88；UHF 归纳模型的背景沿 AH75.2 所引 Blackadar，[*Operator Algebras*](https://bruceblackadar.com/Mathematics/Cycr.pdf)，II.8.2。实 Gram 行列式、复极化及固定向量范数一次项为成熟 Hilbert 几何，所需具体恒等式已在 (7.8)、(7.12)、(7.15)、(7.18) 展开，不给这些中间工具新增内容名义。

Alfsen–Shultz，[*Orientation in operator algebras*](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/)，PNAS **95**，6596–6601，DOI `10.1073/pnas.95.12.6596`，Dynamical Correspondences 与 Theorem 1，给取向和相容乘法的成熟背景。其 dynamical correspondence 明确要求从 JB 代数线性赋值到 skew order derivations；本分支不能借该定理给任意总 $D$ 补上线性。这里不提出文献穷尽、历史原创或外部开放问题解决主张。

**定义 10.2（同一全文来源谓词与准确消费者）。** 本分支保留的物理来源谓词准确为 AH28.1、64.2、75.1 的 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$：固定 SQ47.1–47.13 的全部定义、合同、公式和量词，以及其中每项递归纳入的、逐项固定版本的上游全文，同时作严格合取。SQ 指《零维紧中心的同一原响应与平方酉轨道闭包分类》；SQ47.1 的主源身份按其自身 1.3、39、41.1 解析，保留 `dcaebc0b9ca5a3a463fd8cfd161d38967df28668` 与 `0aa11dbc3dc337d667b98900673e07d67b99bf46` 的相应层级；其 OP/PT/PB/SM/C/AQ/R3/W/FR/XV/SF 单项身份保持 `f24d1138a7b994da16abd9a47affedea64ea44ce`。AH22.1 的 `2addd6f369b7387226c2b0cc984623dd3efe40a1` 和其保留的 AH12.1 上游 `39a0505470ea889dd9d4301ad60cd9506a5e8b58` 同样不被直接 AH 读取身份压平。

此为同一已有谓词的原位引用，不另造较短合同；原根、静默和其他静态分支也不改为 UHF。以下仅说明消费者范围，不替代任何被纳入全文、任一项原前件或量词。

在满足 (6.4) 的整个 $pAp$ 上，AH64.1、75.1 中已有的同响应代入计算给出静态后端；UHF 应用的角分类由 AH71.2 供应：$x\star y=x\circ y-iD(x,y)$ 复线性延为该角的通常或相反 C* 乘法，保持伴随、准确锥、单位 $p$ 和范数；全部有限角内旧复 Gram 为正，每个原限制评价有数学 GNS，向量平方范数为 $\gamma(p)$，零角质量为零向量。若环境本身满足 AH70.1 的偶维模型前件，AH75.1 已给全环境后端。本次部分混合定理不另支付一般环境的全域实双线性、同一旧结合乘法、全部有限旧复 Gram 或动力学。

实际 Born 只在原事件绑定的完整菜单和正质量上归一：全局菜单 $\sum_ke_k=1$ 用 $\gamma(e_k)/\gamma(1)$；角菜单 $\sum_ke_k=p$ 还须原实际条件化及 $\gamma(p)>0$。所有零、不等、次归一、中心、经典、不等维和静默支保持；数学向量态、角质量及 Peirce 系数不是实际准备或菜单 producer。

真正相关联合与张量解释仍须同一实际共同来源、忠实同向交换的局部腿、共同生成、分离、重数和全部相关输入；共同符号、数学角、相同边缘或分别可达不代付。typed CP、箭头下降与整台递归参考保持系统、整个环境、全部成功／失败／细记录／port／post-port 输出及每份输出的每个仍合法未来，连同原真支持、支持内补、交织夹界、全部所需有限深度和正精度。

完整仪器、TP、Kraus、更新和 Lüders 各守实际 typed 全菜单、完整单位分区、接受端、校准及原表示／收敛条件；所有输出和未来均保留，只有严格正的实际输出质量可归一。合法历史、真正分组遗忘、停止、拒绝、销毁、泄漏、真实同数两侧和逆向 Return、完整 CountRead 的活动 ready 及 producer 均保持全文合同；同矩阵不合并原程序、记录、读序或未来权限，未定义请求不补零。

正常性、指定前对偶、无限菜单和记录的可数可加及收敛各须原扩展来源。物理动力学仍须保持原域的实际流、同一连续可逆过程及实际逆、物理钟与单位、适用酉实现和生成元域、Hamiltonian 能量解释及同一正 $\hbar$。有限 PB 参数 $t,\alpha,R,\delta$ 不成为物理时间、能量、控制或作用量；局部 Peirce 系数也不成为一条物理定律。

**定义 10.3（完整直观解释）。** 始终盯住同一张未知旧表中同一个问题的答案 $D(Rh,b)$：小角内部的整张表已经认识，但输入 $b$ 仍可伸到角外，并与环境保留真实交叉连线。先在原规则允许的范围内放入任意大的有限标签，完整 PB 要求两份真实外层调用的差受到同一个二表预算约束；在同一数学读取里轻轻混入另一块，再分别向正、负两个方向放大标签，两边的范数一次项便锁住答案的一个读数。换用同一小角中第二根实际伴轴，才能把实、虚两种读数合起来，认回全部跨块响应，连角与环境之间的连线也一起认回；整个过程没有让变化输入穿过未知函数取极限。剩下的自由度准确只在小角的两个对角块；若环境输入与角支撑分块，哪怕补角背景任意，另一份真正 PB 的两次外调用仍落在已认识的整个角中，于是对角余量也消失。一般输入则只得到两个复外标签的右支撑，不能因此假装它们的自伴标签都回到小角；两份外层缺陷是否相等仍是原问题的一笔未付关系，其差的范数准确等于余量范数乘 $2|R|$。这使条件几何只需局部三块和两根伴轴，却没有少掉任何原公理，也没有完成奇数阶段环境的全表识别；已经完整分类的角有其数学乘法、正 Gram 和 GNS，而真实准备、完整 Born 菜单、共同相关联合、整台递归仪器的全部输出未来、Return、CountRead、正常性、物理钟和动力学，仍须同一完整原来源谓词逐项承担。

## 追加锚（本行以下为增补区）

## 11. Jordan 特征关系与同一输出的核支撑

**定义 11.1（原域、读取与支撑记号）。** 全部采用定义 6.1 的同一已完成含单位复 C* 代数 $A$、完整原域 $E=A_{\rm sa}$、准确锥 $A_+$、原单位、范数及任意总映射 $D:E^2\to E$。完整 $\mathsf H_A(D)$ 不变：全部有向 A1/P2、相加三表及全部排列的 A2、同一固定有理小窗口的 A3，以及每个实际原三元组的完整 PB (6.3) 同时保留。每个原标签、原评价和全部零、不等、次归一及非正常质量保持；不增加输入正则性、线性、协变性、压缩自然性、商下降或双对偶延拓。

AH43.1 的反对称性、零槽和数学正读取直接复用。对任意未归一的数学正实线性泛函 $\phi$，记

$$
B_\phi(u,v)=\phi(u^2)\phi(v^2)-\phi(u\circ v)^2,
\qquad |\phi D(u,v)|^2\le B_\phi(u,v).
\tag{11.1}
$$

实正泛函在需要时取其复线性正延拓。正读取只检验原来的同一输出，不成为新增实际准备。固定一份忠实含单位表示 $A\subseteq B(\mathcal H)$，内积第一槽共轭线性。对自伴 $b$，以 $q_b$ 表示 $\ker b$ 上的 Hilbert 正交投影，$s_b=1-q_b$。这些表示中的辅助投影无须属于 $A$，不作为 $D$ 的输入。

**定理 11.2（单输入特征关系支付核支撑）。** 设原 $a,b\in E$ 和实数 $\lambda$ 满足精确元素等式 $a\circ b=\lambda b$。对同一个固定输出 $g=D(a,b)$，有

$$
\boxed{(1+\lambda^2)\phi(b\circ g)^2
\le\lambda^2\phi(b^2)\phi(g^2)\quad(\phi\ge0),
\qquad gq_b=q_bg=0.}
\tag{11.2}
$$

特别，$g=s_bgs_b$；若 $p\in A$ 是实际投影且 $b=pbp$，则 $g=pgp\in(pAp)_{\rm sa}$，不要求 $a\in pAp$。本定理不要求角分类。

证明。原零槽使实际 $\operatorname{PB}(a;b,0)$ 的内构造为 $v=g,w=\lambda b$；因此准确的两份外调用及其差是

$$
L_+=D(b+g,\lambda b),\quad L_-=D(b-g,-\lambda b),
\qquad L_+-L_-=-2b\circ g.
\tag{11.3}
$$

此时未假定 $g$ 或外标签有任何角支撑。固定同一 $\phi$，置 $B=\phi(b^2),G=\phi(g^2),C=\phi(b\circ g)$。已知乘法展开给

$$
\begin{aligned}
B_\phi(b+g,\lambda b)
 &=\lambda^2\{(B+2C+G)B-(B+C)^2\},\\
B_\phi(b-g,-\lambda b)
 &=\lambda^2\{(B-2C+G)B-(B-C)^2\}\\
 &=\lambda^2(BG-C^2).
\end{aligned}
\tag{11.4}
$$

首行也等于末项。$BG-C^2\ge0$ 是正泛函的实 Cauchy–Schwarz。不等式 (11.1) 分别用于这两份真实外值，再读取 (11.3)，得到

$$
2|C|\le |\phi L_+|+|\phi L_-|
\le2|\lambda|\sqrt{BG-C^2}.
\tag{11.5}
$$

平方移项即得 (11.2) 的标量界；没有除以 $\lambda$、$B$、$G$ 或任何质量。

令 $q=q_b$。对每个 $\eta\in\ker b$，原输入 $(a,b)$ 的向量读取在 (11.1) 中第二平方为零，所以 $\langle\eta,g\eta\rangle=0$。在 $\ker b$ 上对固定自伴 $g$ 作复极化，得到

$$
qgq=0,\qquad g\eta\in(\ker b)^\perp
=\overline{\operatorname{ran}b}.
\tag{11.6}
$$

末等式来自 $(\operatorname{ran}b)^\perp=\ker b^*=\ker b$。

固定这样的 $\eta$，再固定任意 $\zeta\in\mathcal H$。只改变数学读取

$$
\phi_\varepsilon(y)=\langle\eta+\varepsilon\zeta,
 y(\eta+\varepsilon\zeta)\rangle,\qquad\varepsilon\in\mathbb R.
\tag{11.7}
$$

因 $b\eta=0$，准确有

$$
\begin{aligned}
\phi_\varepsilon(b^2)&=\varepsilon^2\|b\zeta\|^2,\\
\phi_\varepsilon(g^2)&=\|g\eta+\varepsilon g\zeta\|^2,\\
\phi_\varepsilon(b\circ g)&=
\varepsilon\operatorname{Re}\langle b\zeta,g\eta\rangle
+\varepsilon^2\operatorname{Re}\langle b\zeta,g\zeta\rangle.
\end{aligned}
\tag{11.8}
$$

在 (11.2) 取此读取，对非零 $\varepsilon$ 除以 $\varepsilon^2$，再对每个固定 $\zeta$ 取标量极限，得

$$
(1+\lambda^2)\bigl(\operatorname{Re}\langle b\zeta,g\eta\rangle\bigr)^2
\le\lambda^2\|b\zeta\|^2\|g\eta\|^2.
\tag{11.9}
$$

由 (11.6)，可选 $\zeta_n$ 使 $b\zeta_n\to g\eta$。将每个 $\zeta_n$ 代入已经成立的 (11.9)，再取这些向量的范数极限，得到

$$
(1+\lambda^2)\|g\eta\|^4\le\lambda^2\|g\eta\|^4,
\qquad g\eta=0.
\tag{11.10}
$$

无需 $\zeta_n$ 有界或 $\operatorname{ran}b$ 闭合。由全部核向量得 $gq=0$，自伴性给 $qg=0$。若 $b=pbp$，则 $(1-p)\mathcal H\subseteq\ker b$，故 $g=pgp$；忠实性将这个等式返回原 $A$。

$\lambda=0$ 时 (11.5) 直接给 $C=0$，(11.9)–(11.10) 仍成立。$b=0$ 时原零槽给 $g=0$；零泛函、零向量以及任意非负质量倍数都已包含。所有极限只读取固定的 $b,g,L_+,L_-$；没有对变化输入上的未知 $D$ 取极限，也没有对 $q_b,s_b$ 调用 $D$。∎

**证明内零值 11.3（特征投影与正交乘积）。** 后面的证明消费以下两个直接后果，不另把有限秩先例重复计为新分类。若实际投影 $r\in A$ 满足 $ar=ra=\alpha r$，则

$$
D(a,tr)=D(tr,a)=0\quad(t\in\mathbb R).
\tag{11.11}
$$

确实，$t\ne0$ 时 $a\circ(tr)=\alpha(tr)$，11.2 先使 $d=D(a,tr)=rdr$。对 $\xi\in r\mathcal H$，两输入分别作用为 $\alpha\xi,t\xi$，原 P2 的实 Gram 行列式为零，故 $\langle\xi,d\xi\rangle=0$。在 $r\mathcal H$ 内极化及 $d=rdr$ 给 $d=0$；$t=0$ 用零槽，反向用反对称性。无需 $r$ 具有 Hilbert 有限秩。

若原自伴 $a,b$ 满足 $ab=ba=0$，则

$$
D(a,b)=0.
\tag{11.12}
$$

这里 $a\circ b=0$，11.2 给 $g=s_bgs_b$。由 $ab=0$ 及 $a$ 的有界性，$a$ 消灭 $\overline{\operatorname{ran}b}=s_b\mathcal H$。在此空间内读取原 $(a,b)$ 的 P2，第一平方为零，故 $g$ 的二次型为零；极化及已有支撑给 $g=0$。这不是仅有 $a\circ b=0$ 时的零响应断言，反对易输入仍可有非零响应。

## 12. 任意补角背景下的完整单边混合响应

**定理 12.1（正确实际角中的单边识别）。** 设 $e,f\in A$ 为正交实际投影，$P=e+f,Q=1-P$。明确假定同一 $D$ 在整个实际 $PAP$ 上满足 (6.4)，记其普通符号为 $\sigma$，$\jmath=\sigma i$。取任意

$$
\alpha\in\mathbb R,\quad c=c^*\in QAQ,\quad x\in eAf,
\qquad a=\alpha e+c,\quad b=x+x^*.
\tag{12.1}
$$

则完整原响应准确为

$$
\boxed{D(a,b)=\frac{\jmath\alpha}{2}(x-x^*)
=\frac{\jmath}{2}[a,b].}
\tag{12.2}
$$

$c$ 任意自伴，不要求标量或有限谱；$x$ 不要求可逆、闭值域或在某个有限矩阵阶段。角分类的前件是整个 $PAP$，不是一份矩阵子代数。

证明。固定 $g=D(a,b)$，置 $\lambda=\alpha/2$。实际乘法给 $ab=\alpha x,ba=\alpha x^*$，所以 $a\circ b=\lambda b$。定理 11.2 和 (11.11) 先支付

$$
g=PgP,\qquad g\ker b=0,\qquad D(a,e)=0.
\tag{12.3}
$$

又因 $af=fa=0$，对 $f\mathcal H$ 内向量读取原 $(a,b)$ 的 P2，第一平方为零；极化给 $fgf=0$。这是固定输出的压缩等式。

重新使用同一个实际 $\operatorname{PB}(a;b,0)$。其两份外调用仍准确是 (11.3)，现在 (12.3) 已保证四个外标签全部在 $PAP$ 中。此时才能代入角分类，得到

$$
\begin{aligned}
L_+&=\frac{\jmath\lambda}{2}[g,b],\\
L_-&=\frac{\jmath}{2}[b-g,-\lambda b]
=\frac{\jmath\lambda}{2}[g,b].
\end{aligned}
\qquad b\circ g=0.
\tag{12.4}
$$

接着取真正原三元组 $\operatorname{PB}(a;b,e)$。由 (12.3)，其实际内构造及全部外标签为

$$
\begin{gathered}
v=g-\alpha e,\qquad w=\lambda b,\\
(b+g-\alpha e,\ e+\lambda b),\qquad
(b-g+\alpha e,\ e-\lambda b).
\end{gathered}
\tag{12.5}
$$

它们也全部在同一个已分类的 $PAP$ 中。只展开已知比较响应，外值之差为 $\jmath([b,w]+[v,e])=\jmath[g,e]$。原右端由 $b\circ e=b/2$ 和 (12.4) 给

$$
-2b\circ(g-\alpha e)-2e\circ(\lambda b)
=\alpha b/2,
\qquad \jmath[g,e]=\alpha b/2.
\tag{12.6}
$$

令 $g_0=\jmath\alpha(x-x^*)/2,d=g-g_0$。$g_0$ 自伴且在 $PAP$ 中。因 $[x-x^*,e]=-b$、$\jmath^2=-1$，有 $\jmath[g_0,e]=\alpha b/2$；于是 $[d,e]=0$。又 $fg_0f=0=fgf$，故

$$
d=ede=d^*.
\tag{12.7}
$$

由 $x^2=(x^*)^2=0$，直接相乘给 $b\circ g_0=0$。因此 $b\circ d=0$。在 $eAf$、$fAe$ 两块分别压缩，得到

$$
dx=0,\quad x^*d=0,\qquad db=bd=0.
\tag{12.8}
$$

确实 $db=dx\in eAf,bd=x^*d\in fAe$，故它们不能在两块之间互相抵消。

还须使用强于 $g=PgP$ 的核结论。若 $b\eta=0$，则

$$
xf\eta+x^*e\eta=0.
\tag{12.9}
$$

两个加项分别在正交的 $e\mathcal H,f\mathcal H$ 内，故各为零，遂有 $g_0\eta=0$。结合 (12.3)，$d$ 也消灭 $\ker b$。另一方面，$bd=0$ 使 $\operatorname{ran}d\subseteq\ker b$，因而 $d^2=0$。自伴性及 C* 恒等式给 $\|d\|^2=\|d^2\|=0$，所以 $g=g_0$。

证明没有除以 $\alpha$；$\alpha=0$ 已包含，也可直接用 $ab=ba=0$ 和 (11.12)。$x=0$、任一零投影及 $P=0$ 均由零槽处理。不存在对 $x$ 的逆、极分解、有限秩提升或未知 $D$ 的加法展开。∎

## 13. 一般局部反对易输入与任意环境余项

**定理 13.1（局部对合的整个反对易子空间）。** 设实际投影 $P$ 的整个 $PAP$ 已以符号 $\sigma$ 分类，$\jmath=\sigma i$。取任意

$$
e=e^*\in PAP,\quad e^2=P,\quad Q=1-P,\quad
c=c^*\in QAQ,\quad\lambda\in\mathbb R,
\tag{13.1}
$$

则对每个 $a=a^*\in PAP$、$ae+ea=0$，有

$$
\boxed{D(a,\lambda e+c)=\frac{\jmath}{2}[a,\lambda e].}
\tag{13.2}
$$

不要求 $a^2$ 为 $P$ 的实倍数，也不要求 $a$ 可逆。

证明。固定 $H=\lambda e+c,T=D(H,a)$。因 $H\circ a=0$，定理 11.2 先给 $T=PTP$。两个真正的零第二外槽 PB 分别为

$$
\begin{aligned}
\operatorname{PB}(H;a,0):\quad
&D(a+T,0)-D(a-T,0)=-2a\circ T,\\
\operatorname{PB}(a;H,0):\quad
&D(H-T,0)-D(H+T,0)=2H\circ T.
\end{aligned}
\tag{13.3}
$$

零槽使左边均为零，故 $a\circ T=H\circ T=0$。若 $\lambda=0$，则 $H=c$ 与 $a$ 的乘积双向为零，(11.12) 已给 (13.2)。以下设 $\lambda\ne0$；由 $T=PTP,cT=Tc=0$，有

$$
eT+Te=0.
\tag{13.4}
$$

取实际投影 $r_+=(P+e)/2$。它满足 $Hr_+=r_+H=\lambda r_+$，所以 (11.11) 给 $D(H,r_+)=0$。现在使用实际 $\operatorname{PB}(H;r_+,a)$：

$$
\begin{gathered}
v=0,\qquad w=\lambda r_++T,\\
(r_+,\ a+\lambda r_++T),\qquad
(r_+,\ a-\lambda r_+-T).
\end{gathered}
\tag{13.5}
$$

全部外标签确在同一已分类的 $PAP$ 内。角公式使左边成为 $\jmath[r_+,T]$；右边由 $a\circ T=0,a\circ r_+=a/2$ 成为 $-\lambda a$。由 (13.4)，$[r_+,T]=eT$，从而

$$
\jmath eT=-\lambda a,\qquad T=\jmath\lambda ea.
\tag{13.6}
$$

第二式由左乘 $e$、$e^2=P$ 和 $\jmath^{-1}=-\jmath$ 得到。反对称性及 $ae=-ea$ 遂给 $D(a,H)=-T=\jmath\lambda ae=\jmath[a,\lambda e]/2$。零角、零 $a$ 和零 $r_+$ 包含于上述等式；没有延拓 $D$ 的定义域。∎

例如在 $M_3(B)$ 的 $12$ 角内，取 $e=E_{12}+E_{21}$。整个反对易自伴子空间准确写成

$$
a=(E_{11}-E_{22})u+i(E_{12}-E_{21})v,
\qquad u,v\in B_{\rm sa}.
\tag{13.7}
$$

这里 $E_{ij}z$ 表示矩阵单元张量 $z$，不要求 $u,v$ 交换。直接块相乘验证 $a=a^*,ae+ea=0$；反向由一般自伴 $2\times2$ 块的反对易等式得到对角块互负、非对角块反自伴，故 (13.7) 无遗漏。定理 13.1 允许任意 $c=E_{33}w,w=w^*\in B$，但仍明确要求整个 $12$ 角的分类前件。

## 14. 三块应用、原行残差与尚缺的联合关系

**应用 14.1（任意系数的两条混合边）。** 设 $A=M_3(B)$，$B$ 为任意含单位复 C* 代数，原 $D$ 满足完整 $\mathsf H_A(D)$。令 $p_{ij}=E_{ii}+E_{jj}$、$h=E_{11}-E_{22}$。若整个 $p_{13}Ap_{13}$ 已以 $\sigma_{13}$ 分类，则 12.1 取 $e=E_{11},f=E_{33},\alpha=R,c=-RE_{22}$ 给

$$
D(Rh,b_{13}(x))=\frac{\sigma_{13}iR}{2}
(E_{13}x-E_{31}x^*),\quad
b_{13}(x)=E_{13}x+E_{31}x^*\quad(x\in B).
\tag{14.1}
$$

若整个 $p_{23}Ap_{23}$ 已以 $\sigma_{23}$ 分类，则取 $e=E_{22},f=E_{33},\alpha=-R,c=RE_{11}$ 给

$$
D(Rh,b_{23}(y))=-\frac{\sigma_{23}iR}{2}
(E_{23}y-E_{32}y^*),\quad
b_{23}(y)=E_{23}y+E_{32}y^*\quad(y\in B).
\tag{14.2}
$$

这两式保留任意完成系数，并非只给标量边或有限阶段边。对一般 $B$，这里没有供应任何角分类，也没有断言两符号相同。

在三进 UHF $A=M_{3^\infty}=M_3(B)$、$B=M_{3^\infty}$ 中，三个标准 $p_{ij}$ 是实际阶段矩阵秩二投影。AH71.2 供应各个**整个完成角**的分类，AH72.1 供应同一个 $\sigma$，故 (14.1)–(14.2) 对全部 $x,y\in B$ 无额外角分类假设。这里直接消费既有供应和共同符号，不重作偶维分类或符号拼接；阶段矩阵秩二不等于表示中的 Hilbert 有限秩。

若三个整个标准角都已用同一个 $\sigma$ 分类，则对固定 $R$，旧行在集合

$$
\mathcal T=\bigcup_{i=1}^3\{E_{ii}z:z=z^*\in B\}
\ \cup\!\bigcup_{1\le i<j\le3}
\{E_{ij}z+E_{ji}z^*:z\in B\}
\tag{14.3}
$$

的每个元素上等于 $K_\sigma(Rh,\cdot)$：$11,22$ 块与 $12$ 边直接在完整 $12$ 角内；$33$ 块由 (11.12)；$13,23$ 边由 (14.1)–(14.2)。这只是逐个实际输入的识别。

**边界 14.2（块和仍是原来的缺口）。** $\mathcal T$ 的实线性张成等于 $A_{\rm sa}$，因为自伴矩阵可按三个对角块与三条自伴边分解。但未知旧行不因此成为实线性；尤其尚未从原关系证明

$$
D(Rh,b_{13}(x)+b_{23}(y))
=D(Rh,b_{13}(x))+D(Rh,b_{23}(y)).
\tag{14.4}
$$

不能将单边公式相加来计算左边。对于 §§7–8 的局部反射及其任意环境输入，已识别的非对角块与可能的对角余量 $r$ 仍按 (7.1)–(7.2) 保留。定理 12.1 消去其单边族上的余量，不消去任意环境 $b$ 的余量；一般目标仍是 $D(Rh,b)=K_\sigma(Rh,b)$，亦即 (8.4) 的两份实际外层缺陷相等。

例如在具有忠实有限数学迹 $\tau$ 且 (14.3) 已识别的场合，一条足以接回整行、但仍须从原关系支付的联合关系是

$$
\tau(D(Rh,b)t)+\tau(bD(Rh,t))=0
\quad(b\in A_{\rm sa},\ t\in\mathcal T).
\tag{14.5}
$$

其充分性只是既有迹分离机制：若 (14.5) 得到，则比较内导子的迹循环恒等式给 $\tau(r_b t)=0$，其中 $r_b=D(Rh,b)-K_\sigma(Rh,b)$。只在线性泛函 $\tau(r_b\,\cdot)$ 上使用 $\mathcal T$ 的实张成，得 $\tau(r_b^2)=0$；忠实性才给 $r_b=0$。本节没有证明 (14.5)，没有将其增列为公理，也没有取得一般两点共同导子见证。分别成立的单点读数不代替这条联合关系。

## 15. 来源归属、几何范围与完整量子来源

**定义 15.1（成熟工具与本地综合的差额）。** 定理 11.2 的承重点是精确特征关系下的同一原输出核支撑；定理 12.1、13.1 消费它使实际外标签进入已分类的整个角，再识别指定混合族。它们归为 $\texttt{repo-derived}$ 的条件纸面综合，不声称文献穷尽、历史原创或外部开放问题解决。直接 PB 代入、Gram 展开、复极化、$\overline{\operatorname{ran}b}=(\ker b)^\perp$ 及自伴平方零蕴含零都是证明工具，不单列为新增内容。

OP46–47 的 $a\circ b=\lambda b$ 用于特定 $M_2$ 多项式原域的点像和既有小像窗口，不供应 11.2 的任意完成 C* 原域核结论。W119.2–119.3 的角闭合以前提两输入都在该角中；这里的 $a$ 可在角外，故必须先支付 (11.2)。PT132.1–132.2 的特征射线零值和 AH5.3 的完整秩一行各守真实 Hilbert 秩一及其原有限角前件；它们的已覆盖情形直接复用，不将模块投影偷换为紧算子秩一。W94.1 的正负锥单位行、中央块卷128.2 的中央旁观者中性也保持原前件，不据此预付一般非中央混合行。

Peirce 分解及角乘法术语沿 W119 所引 Hanche-Olsen–Størmer，[*Jordan Operator Algebras*](https://hanche.folk.ntnu.no/joa/joa-m.pdf)，§2.6.2、Lemma 2.6.3；本节所需块乘法均已在证明中直接核对。忠实表示、正泛函与数学 GNS 的成熟归属沿定义 10.1。Alfsen–Shultz，[*Orientation in operator algebras*](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/)，Dynamical Correspondences、Theorem 1，给线性 dynamical correspondence 与相容 C* 乘法的既有接口；其线性及 skew order derivation 前件没有在这里被赠给任意总 $D$。局部或两点导子分类不能替代尚缺的共同见证，不将这些成熟分类包装为本节的新结论。

**定义 15.2（同一个完整来源谓词）。** 完整物理来源准确保持定义 10.2 及 AH28.1、64.2、75.1 的 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$：SQ47.1–47.13 的全部定义、合同、公式、量词及其逐项递归纳入、逐层固定版本的上游全文同时合取；简称、固定版本及原根、静默和其他静态分支均沿原定义。此处的说明不替代该谓词，不把它压缩为消费者清单。

静态 $S-iD$ 乘法、全部有限旧复 Gram 和数学 GNS 仍只在已经整体分类的域按 AH64.1、75.1 消费；部分混合值识别没有构成一般环境的结合乘法或全域线性。角质量是原 $\gamma(P)$，零角质量仍给零向量。实际 Born 保留原事件绑定、实际完整菜单及严格正的相应质量；向量读取和支撑投影不生产准备、菜单或条件化。

真正联合保留同一实际共同来源及全部相关输入；typed CP 和递归参考保留整个环境、全部成功、失败、细记录、port、post-port 输出及每份输出的每个仍合法未来。完整仪器、TP、Kraus、更新、Lüders、合法历史、真正分组遗忘、停止、拒绝、销毁、泄漏、同数两侧和逆向 Return、完整 CountRead 的活动 ready 与 producer、正常性、指定前对偶、无限菜单和记录收敛，以及物理动力学、实际连续可逆流、物理钟、单位、能量及共同正 $\hbar$，全部保留原全文条件。数学读取参数、局部角和非零边不供应这些来源；本分支没有完整奇数阶段 UHF 分类、kernel 证书或完整量子起源结论。

**定义 15.3（完整直观解释）。** 始终固定原表里同一个问题的答案：当两个实际输入满足精确的 Jordan 特征关系时，两份真实外响应共享的预算比普通 Cauchy–Schwarz 更紧，多出的那一份约束不允许答案在第二输入的核里留下任何作用；先沿每个固定方向轻微改变数学读取，再在像的闭包内逼近，就能消灭整片核，而不让未知函数经过输入极限。这样，一条混合边真正属于哪个角便先被认清，即使第一输入还带着任意补角背景，也能把后续实际外调用合法送入已认识的整个角；投影标签锁住标准的非零边，余量既把向量送进核、又消灭核，只能为零。一般局部反对易族也由同一办法回到正确角内，无需虚构全局半单位、任意模块的有限秩支撑或可逆系数。这使单边的几何更直接，却没有把不同边同时出现时的同一个答案拆成可相加的几份：块和及任意环境整行仍欠真正的联合关系，而已分类域以外的静态重构、真实准备与完整 Born 菜单、共同联合、递归仪器的全部输出未来、Return、CountRead、正常性及物理动力学，继续由同一个完整原来源谓词逐项承担。

## 追加锚（本行以下为增补区）

## 16. 等右 Gram 的相反双边与同一输出刚性

**定义 16.1（完整原关系与双边输入域）。** 沿用定义 6.1–6.2 的完整原候选及其引文身份。具体取任意含单位复 C* 代数 $B$、$A=M_3(B)$，原域准确为 $E=A_{\rm sa}$，$S(u,v)=u\circ v=(uv+vu)/2$、$C=A_+$、单位 $1_A$、$N=\|\cdot\|$。同一原正实线性评价族 $\mathcal P$ 分离 $E$ 并准确决定 $C$；原 $\Omega/\mathrm{native}$、每个原标签、每份评价及全部零、不等、次归一和原表示意义下的非正常质量保持。未知量始终是同一个任意总映射 $D:E^2\to E$。

完整 $\mathsf H_A(D)$ 保留全部有向 A1/P2：

$$
\begin{pmatrix}
\gamma(u^2)&\gamma(u\circ v)-i\gamma D(u,v)\\
\gamma(v\circ u)-i\gamma D(v,u)&\gamma(v^2)
\end{pmatrix}\succeq0
\quad(u,v\in E,\ \gamma\in\mathcal P),
\tag{16.1}
$$

包括两种次序。A2 仍为全部相加三元组 $(u_1,u_2,u_3)=(u+v,u,v)$ 及其排列：实表 $(\gamma(u_i\circ u_j))_{i,j=1}^3$ 在整个 $\mathbb R^3$ 上半正定，$(1,-1,-1)$ 及相应排列给零二次值；A3 仍为 $1_A^2=1_A$，以及同一固定有理 $0<\vartheta\le1$ 下全部 $0\le u\le\vartheta1_A\Rightarrow u^2\le u$。对每个原 $c,u,v\in E$，全部实际内外层 PB 是

$$
\begin{gathered}
V=D(c,u)-c\circ v,\qquad W=c\circ u+D(c,v),\\
D(u+V,v+W)-D(u-V,v-W)=-2u\circ V-2v\circ W.
\end{gathered}
\tag{16.2}
$$

零、重复、全部实幅度、缩放、平移、背景及嵌套调用均在原量词内。不预给 $D$ 输入连续性、可测性、齐次性、可加性、协变性、压缩自然性、商下降、双对偶延拓或有限阶段输出闭合。

令 $E_{ij}z$ 表示矩阵单元张量 $z\in B$，并固定

$$
\begin{gathered}
p=E_{11}+E_{22},\quad q=E_{33},\quad
h=E_{11}-E_{22},\quad e=E_{12}+E_{21},\\
h^2=e^2=p,\qquad he=-eh,\qquad
K_\sigma(u,v)=\frac{\sigma i}{2}[u,v],\quad\sigma\in\{1,-1\}.
\end{gathered}
\tag{16.3}
$$

对一般 $B$，明确要求同一个旧 $D$ 在**整个完成角** $pAp$ 上满足 (6.4)，普通符号为 $\sigma$。这不是仅一份 $M_2$ 子代数的分类，也不要求 $13$ 或 $23$ 角分类。对任意完成系数 $x,y\in B$，定义

$$
\begin{gathered}
b_+(x)=E_{13}x+E_{31}x^*,\qquad
b_-(y)=E_{23}y+E_{32}y^*,\\
\mathcal B_{\rm bal}
=\{b_+(x)+b_-(y):x,y\in B,\ x^*x=y^*y\}.
\end{gathered}
\tag{16.4}
$$

等右 Gram 是所研究的二元输入对 $(Rh,b)$ 中第二输入的限制，不是新公理。$L_a z=a\circ z$；若 $a=Rh$，则 $L_ab_+=(R/2)b_+$、$L_ab_-=-(R/2)b_-$。当 $R\ne0$ 且 $x,y\ne0$ 时，两个相反模同时存在，$b_++b_-$ 不属于单一特征空间。

**定理 16.2（配平双边的完整原响应）。** 在定义 16.1 下，对任意 $R\in\mathbb R$ 和 $x,y\in B$，只要 $`x^*x=y^*y`$，就有

$$
\boxed{
D(Rh,b_+(x)+b_-(y))
=\frac{\sigma iR}{2}
\bigl(E_{13}x-E_{31}x^*-E_{23}y+E_{32}y^*\bigr)
=K_\sigma(Rh,b_+(x)+b_-(y)).}
\tag{16.5}
$$

系数不要求可逆、正规、相互交换、闭值域或属于某个有限矩阵阶段；两种 $\sigma$ 和正、负、零 $R$ 全部包括。

证明。原零槽直接复用 AH43.1。$B=0$、$R=0$ 或 $x=y=0$ 时结论为零；若 $x=0$ 或 $y=0$，等右 Gram 及 C* 恒等式迫使两者皆零。以下固定非零 $R$ 和给定的 $x,y$，始终记

$$
a=Rh,\quad b=b_+(x)+b_-(y),\quad
g=D(a,b),\quad K=K_\sigma(a,b).
\tag{16.6}
$$

只消费继承的主定理 7.1：对这个任意环境输入 $b$，同一输出已满足

$$
g=K+r,\qquad r=\operatorname{diag}(r_1,r_2,0),
\qquad r_1=r_1^*,\ r_2=r_2^*\in B.
\tag{16.7}
$$

主定理使用的正是 $pAp$ 的整体分类及完整原关系；此处不把 (16.7) 作为新假设。固定一份忠实含单位表示 $B\subseteq B(\mathcal H)$，使 $A$ 作用于 $\mathcal H^3$，内积第一槽共轭线性。AH43.1 的准确锥接口给每个未归一数学向量读取

$$
|\langle\xi,g\xi\rangle|^2
\le\|a\xi\|^2\|b\xi\|^2
-\bigl(\operatorname{Re}\langle a\xi,b\xi\rangle\bigr)^2
\quad(\xi\in\mathcal H^3).
\tag{16.8}
$$

这些读取不增加实际准备；其质量为 $\|\xi\|^2$，不作归一化。对任意 $w\in\mathcal H$ 和 $s\in\{1,-1\}$，取

$$
\eta_w=(xw,-yw,0),\qquad
\zeta_{s,w}=(xw,-yw,s iRw).
\tag{16.9}
$$

直接块相乘及等右 Gram 给

$$
\begin{gathered}
b\eta_w=(0,0,(x^*x-y^*y)w)=0,\\
a\zeta_{s,w}=R(xw,yw,0),\qquad
b\zeta_{s,w}=s iR(xw,yw,0)=s i\,a\zeta_{s,w}.
\end{gathered}
\tag{16.10}
$$

由 (16.8)，$\langle\eta_w,g\eta_w\rangle=0$；由 $b\eta_w=0$，也有 $\langle\eta_w,K\eta_w\rangle=0$。故 $\langle\eta_w,r\eta_w\rangle=0$。因 $r$ 的第三行列为零，固定 $s,w$ 并写 $\zeta=\zeta_{s,w}$ 后，准确得到

$$
\langle\zeta,r\zeta\rangle=0,\qquad
k_0:=\langle\zeta,K\zeta\rangle
=-\sigma s\|a\zeta\|^2
=-\sigma s R^2(\|xw\|^2+\|yw\|^2).
\tag{16.11}
$$

若 $xw=yw=0$，则 $\zeta=(0,0,s iRw)$，(16.7) 已给 $r\zeta=0$。其余情形 $k_0\ne0$。为处理此情形，对任意 $\xi\in\mathcal H^3$ 只读取固定的 $K,r,g$，记

$$
\begin{aligned}
k(\xi)&=\langle\xi,K\xi\rangle
=-\sigma\operatorname{Im}\langle a\xi,b\xi\rangle,\\
\rho(\xi)&=\langle\xi,r\xi\rangle,\\
C(\xi)&=\|a\xi\|^2\|b\xi\|^2-|\langle a\xi,b\xi\rangle|^2\ge0,\\
P(\xi)&=C(\xi)-2k(\xi)\rho(\xi)-\rho(\xi)^2\ge0.
\end{aligned}
\tag{16.12}
$$

最后一个不等式准确等价于原 (16.8)，因为 $\langle\xi,g\xi\rangle=k(\xi)+\rho(\xi)$。由 (16.10)–(16.11)，$C(\zeta)=P(\zeta)=0$。置固定向量 $v=r\zeta$，并仅改变读取向量 $\xi_\varepsilon=\zeta+\varepsilon v$，$\varepsilon\in\mathbb R$。自伴性给

$$
\rho(\xi_\varepsilon)
=2\varepsilon\|v\|^2+\varepsilon^2\langle v,rv\rangle.
\tag{16.13}
$$

复 Gram 行列式在第二向量减去第一向量的任意复倍数时不变。由 $(b-s i a)\zeta=0$，取 $d=(b-s i a)v$，得到准确多项式恒等式

$$
C(\xi_\varepsilon)
=\varepsilon^2\left(
\|a\xi_\varepsilon\|^2\|d\|^2
-|\langle a\xi_\varepsilon,d\rangle|^2\right).
\tag{16.14}
$$

因此 $C(\xi_\varepsilon)$ 没有常数项和一次项，$\rho(\xi_\varepsilon)^2$ 也没有一次项，而 $P(\xi_\varepsilon)$ 的一次系数正是

$$
-4k_0\|v\|^2.
\tag{16.15}
$$

这是常数项为零、对正负全部实 $\varepsilon$ 均非负的实多项式，故一次系数只能为零：否则在足够小且与该系数异号的 $\varepsilon$ 上取负。$k_0\ne0$ 遂给 $v=0$。连同零向量分支，对每个 $w$ 及两种 $s$ 都有

$$
r\zeta_{s,w}=(r_1xw,-r_2yw,0)=0,
\qquad r_1x=0,\quad r_2y=0,\quad rb=br=0.
\tag{16.16}
$$

末尾 $br=0$ 也由 $rb=0$ 取伴随得到。全程 $a,b,g,K,r$ 是 (16.6)–(16.7) 中同一批固定元素；不同 $w,s,\varepsilon$ 只改变数学读取，没有出现变化输入上的未知 $D$。

还须排除 $r$ 藏在 $b$ 的核上。令 $q_b$ 为表示中 $\ker b$ 的 Hilbert 正交投影，不要求 $q_b\in A$，也不对它调用 $D$。由 $br=rb=0$，有 $r=q_brq_b$。对每个 $\xi\in\ker b$，(16.8) 给 $\langle\xi,g\xi\rangle=0$；固定自伴输出的复极化给 $q_bgq_b=0$。又 $bq_b=q_bb=0$，所以 $q_bKq_b=0$。于是

$$
r=q_brq_b=q_b(g-K)q_b=0.
\tag{16.17}
$$

忠实性将等式返回原 $A$，得到 (16.5)。不需要 $\operatorname{ran}b$ 或 $\operatorname{ran}x$ 闭合，没有取逆、极分解、输入极限或未知行的加法展开。∎

**核边界 16.3（压缩与消灭核的区别）。** 证明只取得 $q_bgq_b=0$，没有使用或推出一般 $gq_b=0$。例如 $x=y=1_B$、$R\ne0$ 时，对非零 $w$，$\eta_w=(w,-w,0)$ 满足 $b\eta_w=0$，而标准量子响应本身满足

$$
K_\sigma(Rh,b)\eta_w=(0,0,-\sigma iRw)\ne0.
\tag{16.18}
$$

两侧核支撑 (16.17) 是先由 $rb=br=0$ 对**余量**取得的；不能把定理 11.2 的单一 Jordan 特征关系前件赠给这里的相反双模之和。

## 17. 三进 UHF 的实际应用、复用范围与剩余输入

**推论 17.1（没有额外角分类假设的三进应用）。** 取 $A=M_{3^\infty}=M_3(B)$、$B=M_{3^\infty}$，原 $D$ 满足定义 6.1 的完整 $\mathsf H_A(D)$。则 AH72.1 的同一个普通符号 $\sigma$ 对全部 $R\in\mathbb R$、全部 $x,y\in B$ 且 $`x^*x=y^*y`$ 满足 (16.5)。

证明。$p=E_{11}+E_{22}$ 是实际有限阶段矩阵秩二投影。AH71.2 以 W119.2–119.3、W 式 (120.2) 继承完整角接口，再分类整个 $pAp\cong M_2(B)$；AH72.1 供应共同 $\sigma$。这支付定义 16.1 的唯一角分类前件，故直接应用 16.2。所有完成系数均在其量词内；没有分类 $13$、$23$ 角的额外前提，也没有有限阶段输出闭合假设。∎

特别，$y=x$ 及 $y=ux$（任意 $u\in B$ 酉）都属于此族，$u,x$ 不必交换；这里只验证 $`(ux)^*(ux)=x^*x`$，不对未知 $D$ 使用酉协变。$x=y=1_B$ 时，若投影 $t$ 同时支撑 $h,b$，则 $h^2=p$ 给 $t\ge p$，$b^2q=2q$ 给 $t\ge q$，所以 $t=1$。在三进模型后续阶段中，这仍是奇秩全支撑；不能直接把这一实际输入对放进某个已分类的实际偶角。

**边界 17.2（未配平双边及任意环境整行）。** 对一般 $x,y$，记 $G=x^*x-y^*y$，则 (16.9) 的向量准确满足

$$
b\eta_w=(0,0,Gw),\qquad
b\zeta_{s,w}=s i\,a\zeta_{s,w}+(0,0,Gw).
\tag{17.1}
$$

当 $Gw\ne0$ 时，前者不再是核向量，后者不再是复等号向量；(16.11) 的零余量读数和 (16.14) 的二阶起始因子未获支付。本节没有据此否定不等 Gram 输入的标准响应，而是将它们保留为未结范围。任意环境 $b\in A_{\rm sa}$ 的对角块、$12$ 边及其与双边的任意和，也未由本定理取得旧行可加性。一般 $R\ne0$ 的首个未付原关系仍准确是定义 8.3 中的 $E_+=E_-$；式 (8.5) 仍以 $E_+-E_-=2Rhr$ 度量它，16.2 只在 $\mathcal B_{\rm bal}$ 上证明 $r=0$。

**归属 17.3（既有结论与被消费的成熟事实）。** AH 的直接身份保持 `b1a95e41b9622e9f720e51f9bb899841f5b74ca1`；W、CC 的直接身份保持定义 6.1 所用的 `3b10aed60f60e4901bae6cf2e160bf439d642e64`；OP46–47 按 AH42.1 的引用链取 `bef9bba367a24ab5e250491dcb88ed85ebc29cf7`，各自递归引文不被压平。AH43.1 供应同表数学正读取与零槽；主定理 7.1 供应局部反射的全部非对角块。W119–120 的两输入同角闭合、CC147–150 的全单位框架和 AH59–60 的全单位反射及迹／窗前件，各守原范围。OP46–47 是指定 $M_2$ 多项式原域的既有小像及横向结论；AH5.3 的秩一行要求真实 Hilbert 秩一和原有限角提升。它们不把任意完成 $B$ 的模块块免费变成有限秩几何。定理 12.1–13.1 和应用 14.1 的已成范围直接复用，不把分别识别两条边当作其和的识别。

忠实 C* 表示、态分离和数学 GNS 沿定义 10.1 的 Gelfand–Naimark、Segal；Peirce 角术语沿 Hanche-Olsen–Størmer，[*Jordan Operator Algebras*](https://hanche.folk.ntnu.no/joa/joa-m.pdf)，§2.6.2、Lemma 2.6.3；UHF 归纳模型沿 Blackadar，[*Operator Algebras*](https://bruceblackadar.com/Mathematics/Cycr.pdf)，II.8.2.2(iv)。复 Cauchy–Schwarz、Gram 行列式的列消元、复极化和非负实多项式零点的一次系数事实仅在上述证明内消费，不单列为新数学。这里的 $\texttt{repo-derived}$ 差额是：在原主定理留下的两份对角余量上，用等右 Gram 同时供应核向量与两个复等号向量，识别同一个相反双模之和的旧响应。归属限于所引范围内的条件纸面综合，不主张文献穷尽、历史原创或外部开放问题解决。

## 18. 量子对应、完整来源与三块直观

**对应 18.1（同一混合值与已有静态后端）。** 对定理 16.2 的这一份实际输入对，准确有

$$
S(a,b)-iD(a,b)
=\frac{ab+ba}{2}+\frac\sigma2(ab-ba)
=\begin{cases}ab,&\sigma=1,\\ba,&\sigma=-1.\end{cases}
\tag{18.1}
$$

这是 (16.5) 的直接代入。在已整体分类的 $pAp$ 上，AH64.1、75.1 的既有后端给通常或相反 C* 乘法、全部有限旧复 Gram 正性及每份原限制评价的数学 GNS；其循环向量平方范数为 $\gamma(p)$，零角质量仍给零向量。式 (18.1) 增加指定混合值的识别，没有在一般环境上构造全域双线性、结合乘法、全部有限旧复 Gram 或物理动力学。

Alfsen–Shultz，[*Orientation in operator algebras*](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/)，PNAS **95**，6596–6601，DOI `10.1073/pnas.95.12.6596`，Dynamical Correspondences、Theorem 1，给相容乘法的成熟对应；其前件是从含单位 JB 代数到 skew order derivations 的**线性** dynamical correspondence，不能据此给任意总 $D$ 补上线性，也不能把一般 C* 范数域替换成 von Neumann 原域。

**定义 18.2（不变的全文来源谓词）。** 完整物理来源严格保持定义 10.2、15.2 及 AH28.1、64.2、75.1 的同一个 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$：SQ47.1–47.13 的全部定义、合同、公式、量词，及逐项递归纳入、逐层固定版本的上游全文同时合取。SQ 的主源身份仍按其自身 1.3、39、41.1、47.1 解析；`dcaebc0b9ca5a3a463fd8cfd161d38967df28668`、`0aa11dbc3dc337d667b98900673e07d67b99bf46` 的相应层级、OP/PT/PB/SM/C/AQ/R3/W/FR/XV/SF 的 `f24d1138a7b994da16abd9a47affedea64ea44ce`，以及 AH22.1、12.1 保留的 `2addd6f369b7387226c2b0cc984623dd3efe40a1`、`39a0505470ea889dd9d4301ad60cd9506a5e8b58` 全部不变。原根、静默及其他静态分支不改为三进模型；以下消费者说明不替代被纳入的任何全文。

实际 Born 仍要求原事件绑定的实际完整菜单及严格正的相应质量；角菜单另需真实条件化，零质量不作除法。真正相关联合、张量与 typed CP 仍保留同一实际共同来源、全部相关输入、整台递归参考、原真支持及支持内补、全部所需有限深度和每个正精度。完整仪器、TP、Kraus、更新和 Lüders 保留各自完整 typed 菜单、接受端、校准、表示及收敛条件，并量化整个环境、全部成功／失败／细记录／port／post-port 输出和每份输出的每个仍合法未来。

合法历史、真正分组遗忘、停止、拒绝、销毁、泄漏、同数两侧及逆向真实 Return、完整 CountRead 的活动 ready 和 producer，仍由同一全文合同承担；相同算子不合并原程序、记录、读序和未来权限，未定义请求不补零。正常性、指定前对偶、无限菜单及记录收敛，以及保持原域的实际连续可逆流、实际逆、物理钟和单位、适用生成元域、Hamiltonian 能量解释及共同正 $\hbar$ 均保留原前件。数学读取、$R$、$s$、$\varepsilon$ 和三块坐标不生产这些来源；本节没有完整奇数阶段 UHF 分类、物理来源满足性、kernel 证书或完整量子起源结论。

**解释 18.3（完整直观解释）。** 把三个块想成两条带相反方向标记的通道和一个共同环境端点：第一输入在前两块分别取 $R$ 与 $-R$，在环境块取零；第二输入让两条边同时接到这个端点，因此必须研究原表对这整个输入给出的同一个答案，不能把两条已知单边答案相加。完整原关系和已经认识的整个小角先锁住答案的跨块部分，只留下前两块各自的对角余量。等右 Gram 说两条边对每个共同端点向量有相同的平方强度；它一方面造出两边恰好抵消的核向量，迫使余量在该向量上的读数为零，另一方面只在环境分量添上正、负纯虚幅度，就造出复 Cauchy–Schwarz 恰好取等的向量，同时保持余量读数为零。若余量还把这种向量送到非零处，就沿这个像轻轻改变数学读取：原预算在等号处没有一次松动，余量却产生一个非零一次项，正负两个方向必有一边违反正性。所以两份对角余量都必须消灭各自的边；剩下的余量只能藏在整个第二输入的核上，而原 P2 又消灭它在核上的压缩，最终只能为零。这个有限三块论证允许每块内部无限维、系数退化和非闭值域，不需要求逆，也不让未知函数经过输入极限。简化来自两种关系共同约束同一输出，没有减少原公理条数；不等 Gram 的双边、任意环境整行及完整量子起源仍未结清。已分类角有其复代数、正 Gram 和数学 Hilbert 表示，真实准备与完整 Born 菜单、共同联合、整台仪器全部输出未来、Return、CountRead、正常性和物理动力学仍须同一个完整来源谓词逐项成立。

## 追加锚（本行以下为增补区）

## 19. 标量总右 Gram 的实际双反射

**定义 19.1（完整原条件与第二个整体角前件）。** 本增补逐句采用定义 6.1、16.1 的同一个完整 $\mathsf H_A(D)$，以及定义 6.2 的整体角分类含义和引文身份。具体地，$B$ 为任意含单位复 C* 代数，$A=M_3(B)$，完整原域为 $E=A_{\rm sa}$，$S(a,b)=(ab+ba)/2$，准确锥为 $A_+$，单位和范数为原单位和 C* 范数。原正实线性评价族分离 $E$ 并准确决定锥，保留同一 $\Omega/\mathrm{native}$、每个原标签、每份评价及全部零、不等、次归一和原表示意义下的非正常质量。未知量始终是同一个任意总映射 $D:E^2\to E$。

这里的完整条件包括 (6.2)、(16.1) 的全部有向 A1/P2 及两种次序，全部相加三表及其排列在整个 $\mathbb R^3$ 上的 A2 和相加零方向，以及同一固定有理 $0<\vartheta\le1$ 的 A3。每个实际原三元组 $(c;z,t)$ 的全部内外调用均满足

$$
\begin{gathered}
v=D(c,z)-c\circ t,\qquad w=c\circ z+D(c,t),\\
D(z+v,t+w)-D(z-v,t-w)=-2z\circ v-2t\circ w.
\end{gathered}
\tag{19.1}
$$

全部零、重复、实幅度、缩放、平移、背景和嵌套调用仍在原量词内。不预给 $D$ 输入连续性、可测性、齐次性、可加性、协变性、压缩自然性、商下降、双对偶延拓或有限阶段输出闭合。

取与 (16.3) 相同的实际元素

$$
p=E_{11}+E_{22},\quad q=E_{33},\quad
h=E_{11}-E_{22},\quad e=E_{12}+E_{21},\quad
K_\sigma(z,t)=\frac{\sigma i}{2}[z,t],\quad \sigma\in\{\pm1\}.
\tag{19.2}
$$

明确要求同一旧 $D$ 在整个完成角 $pAp$ 上以 $\sigma$ 分类。对任意完成系数 $x,y\in B$，本节研究的输入族为

$$
b=E_{13}x+E_{23}y+E_{31}x^*+E_{32}y^*,\qquad
x^*x+y^*y=\mu1_B,\qquad \mu\ge0.
\tag{19.3}
$$

这是输入族限制，不是对原候选增加公理；不要求 $x^*x=y^*y$。若 $\mu>0$，定义原代数中的实际元素

$$
u=\frac{E_{13}x+E_{23}y}{\sqrt\mu},\qquad
P_0=uu^*,\qquad P=P_0+q,\qquad H_b=u+u^*,\qquad f=P_0-q.
\tag{19.4}
$$

对一般 $B$，还明确要求同一个旧 $D$ 在**整个实际完成角 $PAP$** 上也满足

$$
D(z,t)=K_\sigma(z,t)\qquad(z,t\in(PAP)_{\rm sa}),
\tag{19.5}
$$

其中 $\sigma$ 与 $pAp$ 的符号相同。这是第二个整体角分类前件，不能由坐标同构或自由协变补入。第 20 节在三进 UHF 中从原条件供应它，包括任意完成 $x,y$ 所产生的实际 $P$。

**定理 19.2（双反射消去标量总右 Gram 族的余量）。** 在定义 19.1 下，对所有实 $R$，同一个实际原输出满足

$$
\boxed{
D(Rh,b)=K_\sigma(Rh,b)
=\frac{\sigma iR}{2}
\bigl(E_{13}x-E_{31}x^*-E_{23}y+E_{32}y^*\bigr).}
\tag{19.6}
$$

$x,y$ 不要求可逆、正规、相互交换或位于某个有限矩阵阶段。结论同时包括两条边非零且右 Gram 不等的情形。

证明。反对称性及零槽直接复用 AH43.1。零代数或 $R=0$ 时用零槽；$\mu=0$ 时，两个正元之和为零给 $x^*x=y^*y=0$，C* 恒等式给 $x=y=0$，故 $b=0$。以下设 $\mu>0$，固定同一个 $a=Rh$、$b$ 和 $g=D(a,b)$。

标量总右 Gram 使 (19.4) 成为实际的局部反射构造：

$$
\begin{gathered}
u^*u=q,\quad u^2=0,\quad uu^*=P_0\le p,\quad P_0q=qP_0=0,\\
H_b^2=f^2=P,\quad H_bf=-fH_b,\quad b=\sqrt\mu H_b,\quad b^2=\mu P.
\end{gathered}
\tag{19.7}
$$

这里 $u$ 是原代数中的部分等距，$P_0$ 是投影；所用部分等距和矩阵单位事实为成熟 C* 工具，归属见 22.1。

首先直接消费定理 7.1：第一反射为 $h$，实际伴轴为 $e$，整体角是已分类的 $pAp$，第二输入仍为完整的 $b$。于是

$$
g=K_\sigma(a,b)+r,\qquad
r=r^*\in pAp,\qquad [h,r]=0.
\tag{19.8}
$$

其次在同一个原代数 $A$ 中再次消费定理 7.1：第一反射改为实际 $H_b$，实际伴轴为 $f$，整体角是 (19.5) 的 $PAP$，实强度为 $\sqrt\mu$，第二输入为原来的 $a$。没有对 $D$ 提取强度因子。该定理给

$$
D(b,a)=K_\sigma(b,a)+s,\qquad
s=s^*\in PAP,\qquad [H_b,s]=0.
\tag{19.9}
$$

两份公式读的是同一旧表的两个反向值。反对称性给 $r=-s$，故

$$
r\in PAP,\qquad [b,r]=0,\qquad qr=rq=0.
\tag{19.10}
$$

末项来自 (19.8) 的 $r\in pAp$。因此

$$
r=PrP=P_0rP_0.
\tag{19.11}
$$

在 $[b,r]=0$ 左乘 $q$，利用 $qb=\sqrt\mu u^*$ 和 $qr=0$，得到 $u^*r=0$。于是

$$
r=P_0r=uu^*r=0.
\tag{19.12}
$$

代回 (19.8) 得 (19.6)。两次应用的第二输入都是实际原标签；证明未将 $b$ 的两个模分别送入未知行后相加，也未使用输入极限、$x$ 或 $y$ 的逆或闭值域假设。∎

**范围 19.3（同时双模及与 16.2 的互补）。** 对 $R\ne0$，$L_{Rh}b_+(x)=(R/2)b_+(x)$、$L_{Rh}b_-(y)=-(R/2)b_-(y)$；两边均非零时，(19.6) 识别的是同时包含两个相反模的一个实际输入。它直接关闭该输入上定义 8.3 的 $E_+=E_-$，而不是假定 (14.4) 的旧行可加性。

两个输入族互不包含。例如 $x=2\cdot1_B,y=1_B$ 满足 (19.3) 的 $\mu=5$，右 Gram 不等。反向在三进 $B$ 的一个实际 $M_3$ 中取 $t=\operatorname{diag}(1,2,0)$、$x=y=t$，则 16.2 的等右 Gram 成立，$x^*x+y^*y=2t^2$ 不是标量。两条件相交时准确为 $x^*x=y^*y=(\mu/2)1_B$；这里没有替换或削弱 16.2。

标量总右 Gram 也允许非标量完成系数和退化的单边：给定 $0\le T\le1_B$ 及任意酉元 $v,w\in B$，取

$$
x=\sqrt\mu\,vT^{1/2},\qquad
y=\sqrt\mu\,w(1_B-T)^{1/2}.
\tag{19.13}
$$

直接计算得 $x^*x=\mu T$、$y^*y=\mu(1_B-T)$。只在已知乘法中检验输入条件，不对未知 $D$ 使用酉协变。定理本身量化所有满足 (19.3) 的完成 $x,y$，不把 (19.13) 当作其穷尽参数化。

## 20. 实际内在偶维模型供应整个第二角与共同符号

**推论 20.1（三进 UHF 的全部标量总右 Gram 双边）。** 设 $A=M_{3^\infty}=M_3(B)$、$B=M_{3^\infty}$，同一原总映射满足完整 $\mathsf H_A(D)$。则 AH72.1 的同一个普通符号 $\sigma$ 对所有实 $R$、所有完成 $x,y\in B$ 及所有满足 (19.3) 的 $\mu\ge0$，给出 (19.6)。这里无需另加 $PAP$ 分类或 $P$ 位于原有限矩阵阶段的假设。

证明。$\mu=0$ 已由零槽支付，以下取 $\mu>0$。标准 $p=E_{11}+E_{22}$ 属于原第一矩阵阶段且秩为二；AH71.2 分类整个完成 $pAp$，AH72.1 给它上述共同 $\sigma$。这支付定理 19.2 的第一角前件。

对 (19.4) 的任意实际 $P$，W119.2–119.3 供应同一原 $D$ 的角闭合及准确接口：

$$
D((PAP)_{\rm sa},(PAP)_{\rm sa})\subseteq(PAP)_{\rm sa},\qquad
C_P=(PAP)_+=A_+\cap PAP,\qquad
1_{PAP}=P,\qquad N_P=\|\cdot\|_A|_{PAP}.
\tag{20.1}
$$

每个原评价标签仍作为限制 $\gamma_P$ 保留，准确质量为 $\gamma(P)$；同值限制不合并，零限制不删除，不除以任何质量。原有向 P2、A2 的全部三表与排列以及同一个 $\vartheta$ 的 A3 均继承。W 式 (120.2) 的完整 PB 逐值继承：角内三输入的两份内输出由 (20.1) 留在角内，Jordan 运算和实际外标签也在角内，两份外输出再次由 (20.1) 留在角内。这使用任意**实际原投影**的接口；完整原域使这里的 $P$ 确是原标签。

现在给这个具体角供应 AH66.1 所需的实际偶维模型。记 $\iota:B\to qAq$ 为 $\iota(z)=E_{33}z$。成熟矩阵单位接口给保单位 * 同构

$$
\begin{aligned}
\Phi:M_2(B)&\longrightarrow PAP,\\
\Phi\begin{pmatrix}z_{11}&z_{12}\\z_{21}&z_{22}\end{pmatrix}
&=u\iota(z_{11})u^*+u\iota(z_{12})
+\iota(z_{21})u^*+\iota(z_{22}).
\end{aligned}
\tag{20.2}
$$

所用实际矩阵单位为 $P_0,u,u^*,q$，单位之和为 $P$。为明确该接口覆盖整个角，对 $T\in PAP$，其四个逆坐标是

$$
\Phi^{-1}(T)=
\begin{pmatrix}
\iota^{-1}(u^*Tu)&\iota^{-1}(u^*Tq)\\
\iota^{-1}(qTu)&\iota^{-1}(qTq)
\end{pmatrix}.
\tag{20.3}
$$

各括号确在 $qAq$ 内。此式只明确成熟角同构的参数对应，不另立分类或新矩阵单位定理。

取 $B$ 的实际递增含单位矩阵模型 $B_n\cong M_{3^n}(\mathbb C)$，其并在 $B$ 中范数稠密。则

$$
\mathcal A_n^P=\Phi(M_2(B_n))\subseteq PAP,\qquad
\mathcal A_n^P\cong M_{2\cdot3^n}(\mathbb C),\qquad
1_{\mathcal A_n^P}=P,\qquad
PAP=\overline{\bigcup_n\mathcal A_n^P}^{\|\cdot\|}.
\tag{20.4}
$$

这些是真正位于原 $A$ 中的递增有限全矩阵子代数，各矩阵阶数为偶。密度仅使用已知 * 同构的等距性与 $B_n$ 的密度。于是 AH70.1 **直接作用于实际载体 $PAP$、限制的同一个 $D_P$ 和模型 (20.4)**，供应唯一普通符号 $\sigma_P$，使

$$
D(z,t)=\frac{\sigma_P i}{2}[z,t]
\qquad(z,t\in(PAP)_{\rm sa}).
\tag{20.5}
$$

这里没有先把 $D$ 声明为对 $\Phi$ 协变，也没有让任何输入极限穿过 $D$；不要求 $D((\mathcal A_n^P)_{\rm sa},(\mathcal A_n^P)_{\rm sa})$ 留在 $\mathcal A_n^P$。AH70.1 自身分类整个完成载体，已支付所需推论。本步骤不把 AH71.1 的有限阶段投影条件赠给 $P$，也不声称 AH72.1 已经直接比较了这个 $P$。

最后比较两份**同一原输出**。实际共同子角满足

$$
P_0AP_0\subseteq pAp\cap PAP,\qquad
z\longmapsto u\iota(z)u^*:\ B\overset{*}{\cong}P_0AP_0.
\tag{20.6}
$$

取实际 $B_1=M_3$ 的矩阵单位 $e_{ij}^B$，令 $d=e_{11}^B-e_{22}^B$、$t=e_{12}^B+e_{21}^B$；两者自伴且交换子非零。令

$$
\alpha=u\iota(d)u^*,\qquad \beta=u\iota(t)u^*.
\tag{20.7}
$$

这两个自伴原标签在共同子角中，且 $[\alpha,\beta]=u\iota([d,t])u^*\ne0$；非零性也可左乘 $u^*$、右乘 $u$ 直接检验。第一角的既有分类与 (20.5) 因而同时给

$$
D(\alpha,\beta)
=\frac{\sigma i}{2}[\alpha,\beta]
=\frac{\sigma_P i}{2}[\alpha,\beta],
\qquad \sigma_P=\sigma.
\tag{20.8}
$$

这支付 (19.5) 的同号前件。直接应用定理 19.2 得全部结论。共同子角的非交换性在这里来自 $B=M_{3^\infty}$；对一般交换 $B$，不能用这个比较凭空认定两个可能符号相同。∎

## 21. 第一行骨架与全部二表的一个精确边界

**命题 21.1（本输入族中仍须支付第二反射行）。** 仅有全部有向 A1/P2、A2/A3、整个 $pAp$ 的标准分类，以及指定对 $(a,b)$ 的 (19.8) 骨架，不能推出 (19.6)。下面的同一个六维总映射在标量总右 Gram、不等右 Gram 的实际输入上展示这一点，并有一份明确的完整 PB 失败。

这只隔离定理 19.2 中第二遍 7.1 的作用。一般的局部契约不足性已由 AH73–74 支付；单对正性留下非标准输出的先例还有 PT134.2，以及运输续卷110.2的固定八阶元组。本例不重立“PB 不可删”的一般独立性结论，不声称满足完整原候选或所有其他局部反射的 7.1 结论。

证明。另取 $B=M_2(\mathbb C)$、$A=M_3(B)=M_6(\mathbb C)$，原评价取全部数学正泛函，仍保留它们的原标签和全部非负质量；这给分离且准确决定锥的评价族。置

$$
\begin{gathered}
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad Z=\operatorname{diag}(1,-1),\\
x=\operatorname{diag}(2,1),\quad y=\operatorname{diag}(1,2),\quad
m=5,\quad \alpha_0=3/5,\quad\beta_0=4/5,\quad\tau=1/4,\\
a=h,\quad b=b_+(x)+b_-(y),\quad
K=K_1(a,b),\quad r=\operatorname{diag}(\tau X,-\tau X,0),\quad g=K+r.
\end{gathered}
\tag{21.1}
$$

这里 $x^*x+y^*y=5I_2$，而 $x^*x-y^*y=3Z\ne0$；$r\ne0$，$r\in pAp$ 且 $[h,r]=0$。先证明这一对的全部向量 P2。

实际等距列

$$
U=\frac1{\sqrt m}\binom{x}{y},\qquad
V=\frac1{\sqrt m}\binom{y}{-x}
\tag{21.2}
$$

满足 $U^*U=V^*V=I_2$、$U^*V=0$，并给 $p\mathbb C^6$ 的正交分解。每个原向量唯一写成 $\xi=(Uz+Vv,w)$，$z,v,w\in\mathbb C^2$。相对于 $U,V,q$ 三块，

$$
a=\begin{pmatrix}\alpha_0 Z&\beta_0 I_2&0\\
\beta_0 I_2&-\alpha_0 Z&0\\0&0&0\end{pmatrix},\quad
b=\sqrt m\begin{pmatrix}0&0&I_2\\0&0&0\\I_2&0&0\end{pmatrix},\quad
r=\begin{pmatrix}0&\tau X&0\\\tau X&0&0\\0&0&0\end{pmatrix}.
\tag{21.3}
$$

内积第一槽共轭线性。记

$$
\begin{gathered}
F=\alpha_0 Zz+\beta_0v,\qquad G=\beta_0z-\alpha_0Zv,\qquad
L=\|z\|^2+\|v\|^2=\|F\|^2+\|G\|^2,\\
k=\langle\xi,K\xi\rangle=-\sqrt m\operatorname{Im}\langle F,w\rangle,
\qquad \rho=\langle\xi,r\xi\rangle=2\tau\operatorname{Re}\langle z,Xv\rangle.
\end{gathered}
\tag{21.4}
$$

复 Gram 的非负余量准确为

$$
\begin{aligned}
\mathcal C&=\|a\xi\|^2\|b\xi\|^2-|\langle a\xi,b\xi\rangle|^2\\
&=m\{L\|z\|^2+\|G\|^2\|w\|^2
+\|F\|^2\|w\|^2-|\langle F,w\rangle|^2\}.
\end{aligned}
\tag{21.5}
$$

由 $v=(\beta_0/\alpha_0)Zz-(1/\alpha_0)ZG$ 及 $XZ$ 反自伴，

$$
|\rho|\le\frac{2|\tau|}{\alpha_0}\|z\|\|G\|.
\tag{21.6}
$$

置非负实量

$$
A_0=\sqrt{mL}\|z\|,\quad
B_0=\sqrt m\|G\|\|w\|,\quad
t_0=\frac{2|\tau|}{\alpha_0\sqrt m}=\frac{\sqrt5}{6}.
\tag{21.7}
$$

复 Cauchy–Schwarz、$\|F\|,\|G\|\le\sqrt L$ 和 (21.5)–(21.6) 给

$$
\mathcal C\ge A_0^2+B_0^2,\quad
2|k\rho|\le2t_0A_0B_0,\quad
\rho^2\le t_0^2A_0^2.
\tag{21.8}
$$

所有式子在 $L=0$ 或任一零向量时仍成立，没有除以这些量。候选输出 $g=K+r$ 的原实 Gram 预算减去输出平方，因而满足

$$
\begin{aligned}
&\|a\xi\|^2\|b\xi\|^2-
\bigl(\operatorname{Re}\langle a\xi,b\xi\rangle\bigr)^2
-\langle\xi,g\xi\rangle^2\\
&\quad=\mathcal C-2k\rho-\rho^2\\
&\quad\ge(B_0-t_0A_0)^2+(1-2t_0^2)A_0^2
=(B_0-t_0A_0)^2+\frac{13}{18}A_0^2\ge0.
\end{aligned}
\tag{21.9}
$$

两份平方对角非负，反向输出取 $-g$，故这一对的两种有向二表均正。有限维每个正泛函是向量正泛函的有限非负和，二表对泛函线性且正二表之和仍正，于是覆盖全部正泛函和全部质量，包括零质量；不存在仅验证向量态而漏掉其他读取的问题。

现在在整个 $A_{\rm sa}^2$ 定义同一个总映射

$$
\widetilde D(c,d)=
\begin{cases}
g,&(c,d)=(a,b),\\
-g,&(c,d)=(b,a),\\
K_1(c,d),&\text{其他实际有序对}.
\end{cases}
\tag{21.10}
$$

$a,b$ 非零、自伴且不同，故两例无冲突。未改动的对由 AH63.1 的载体无关反向 P2 计算给标准复 Gram；两份改动由 (21.9) 支付，故全部有向 A1/P2 成立。A2 的实三表及相加零方向只用已知 Jordan 实部，A3 由 C* 谱序成立。因为 $b\notin pAp$，整个 $pAp$ 的旧表仍等于 $K_1$，而指定对满足 (19.8)。它还满足

$$
x^*r_1x+y^*r_2y=0,\qquad q_b r q_b=0,
\tag{21.11}
$$

其中 $r_1=\tau X,r_2=-\tau X$，$q_b$ 是 $\ker b$ 的正交投影。首式由 $xXx=yXy=2X$ 得到；在 (21.3) 中 $\ker b$ 正是 $V$ 块，而 $r$ 的 $VV$ 块为零，给次式。$q_bKq_b=0$ 也由 $bq_b=q_bb=0$ 得到。

最后检验实际 $\operatorname{PB}(b;a,0)$。其内值为 $-g,0$，置 $k_a=a\circ b$，两份真正外层对为 $(a-g,k_a)$、$(a+g,-k_a)$。这里

$$
k_a=\tfrac12b_+(x)-\tfrac12b_-(y),\qquad
\pm k_a\notin\{a,b\}.
\tag{21.12}
$$

所以这两份外值均属于 (21.10) 的标准分支。比较响应的已知双线性给

$$
\begin{aligned}
\widetilde D(a-g,k_a)-\widetilde D(a+g,-k_a)
&=2K_1(a,k_a)=2a\circ K,\\
2a\circ g-2a\circ K
&=2ar=2\tau\operatorname{diag}(X,X,0)\ne0.
\end{aligned}
\tag{21.13}
$$

完整 PB 的右端要求 $2a\circ g$，故在这份实际三元组上失败。相应原评价族分离该非零差额。本例没有满足完整 PB，也没有满足以 $b$ 为第一反射所应有的 (19.9)；定理 19.2 使用的正是这笔尚未由第一行骨架和原 P2 支付的约束。∎

## 22. 复用归属、量子对应与不变的完整来源

**归属 22.1（短综合及检索范围）。** 本增补直接消费已给定理 7.1 两次、AH43.1 的反对称性和零槽、W119.2–119.3 及 W 式 (120.2) 的整个实际角接口，以及 AH70.1、71.2、72.1 的既有分类。AH 的直接身份固定为 `b1a95e41b9622e9f720e51f9bb899841f5b74ca1`，W 固定为 `3b10aed60f60e4901bae6cf2e160bf439d642e64`，各自递归引文保持自身版本。有限维或已有更强整体分类覆盖的情形直接复用 AH42.4 等结果，不把它们的特例再次计为新分类。

对本卷 §§6–18、上述 AH66–74 和 W119–120，以及仓内 D5、Blueprint、Library、Problems、理论卷、Evidence、Meta/Digestion 的双反射、标量总右 Gram、实际部分等距角和固定 P2 余量条目所作有限范围检索，未找到 (19.3) 全部完成双边输入及 (20.4) 实际第二角供应的同一现成结论。命题 21.1 的比较范围包含 PT134.1–134.2 和运输续卷110.1–110.2、155.2；其直接读取身份为主分支 `b4182b140eecab883c8ce7b7064496580eac35bd`，这些正文内部固定引文不变。一般弱条件不足的已有结论仍按各自原范围引用，不由本例重新取得新意。

成熟部分等距、等价投影与矩阵单位角接口归于 Blackadar，[*Operator Algebras*](https://bruceblackadar.com/Mathematics/Cycr.pdf)，II.2.3.5、II.3.3.4、II.6.6.8；实际 UHF 归纳模型取 II.8.2.2(iv)。(20.2)–(20.3) 只是明确这些工具在本题中的实际参数。复 Gram、矩阵正性凸锥和正泛函的有限维谱分解也只在证明中消费。没有重证或另命名这些成熟工具。

本增补的结果归为 $\texttt{repo-derived}$ 的**简短纸面应用综合**：用第二个实际反射重新读取同一个旧输出，并以整个实际第二角的内在偶维模型支付调用条件。这覆盖一个含不等右 Gram 的同时双模输入族；不将两次既有定理应用、普通角同构或共同非零交换子比较包装为新的基础分类定理。本文不提出文献穷尽、历史原创、外部开放问题解决或新增 Lean 声明准入主张，也不具有 kernel 核验证书。

**对应 22.2（指定混合值与既有静态后端）。** 在定理 19.2、推论 20.1 识别的这一份实际输入对上，准确有

$$
S(a,b)-iD(a,b)
=\frac{ab+ba}{2}+\frac\sigma2(ab-ba)
=\begin{cases}ab,&\sigma=1,\\ba,&\sigma=-1.\end{cases}
\tag{22.1}
$$

在已经整体分类的 $pAp$ 和 $PAP$ 上，AH64.1、75.1 的既有消费者给通常或相反 C* 乘法、全部有限旧复 Gram 正性，以及每份原限制评价的数学 GNS。两角单位分别为 $p,P$，循环向量平方范数分别为 $\gamma(p),\gamma(P)$；零角质量给零向量。共同符号使两份角内公式在实际交叠上相容。角同构、局部相容和 (22.1) 的单对识别没有取得整个三进环境的旧行可加性、全域双线性、结合乘法或全部有限旧复 Gram。

Alfsen–Shultz，[*Orientation in operator algebras*](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/)，PNAS **95**，6596–6601，DOI `10.1073/pnas.95.12.6596`，Dynamical Correspondences、Theorem 1，给取向与 Jordan 相容复乘法的成熟对应。其 dynamical correspondence 是到 skew order derivations 的**线性**映射；此原始前件不能由本节的部分输出识别替代，也不能用它给任意总 $D$ 补上线性或物理时间演化。

**定义 22.3（严格引用整个原来源谓词）。** 完整物理来源**准确取定义 18.2 的同一个 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$，逐句、逐公式、逐量词及逐层固定身份全文纳入**，连同它严格引用的定义 10.2、15.2、AH28.1、64.2、75.1 及固定 SQ47.1–47.13 全文和每项递归纳入的上游全文同时合取。此处不另定义缩短谓词，不改动任何内层固定提交、来源身份、原根、静默或其他静态分支。下列范围说明不替代该全文中的任何一项。

标量总右 Gram、数学部分等距和角内 GNS 不供应实际准备、相干控制或 Born 菜单。实际 Born 仍需原事件绑定、实际完整菜单、原质量及严格正的相应归一质量；角菜单另需真实条件化，零质量不作除法。真正相关联合和张量仍须同一实际共同来源、全部相关输入、忠实同向交换腿、共同生成、分离与所需重数。数学角交叠不生产这些来源。

typed CP、整台递归参考、完整仪器、TP、Kraus、更新和 Lüders 保留其全部原前件，量化整个环境、全部成功／失败／细记录／port／post-port 输出及每份完整输出的每个仍合法未来。合法历史、停止、拒绝、销毁、泄漏、真正分组遗忘、同数两侧及逆向真实 Return、完整 CountRead 的活动 ready 和 producer 不变；相同算子不合并原程序、记录、读序、原零集或未来权限，未定义请求不补零。

正常性、指定前对偶、无限菜单和记录收敛，以及保持原域的实际连续可逆流、实际逆、物理钟和单位、适用生成元域、Hamiltonian 能量解释与同一正 $\hbar$，仍由定义 18.2 的整个原谓词承担。$R,\mu,u$ 和本证明中的矩阵坐标没有生产这些物理来源。

**边界 22.4（完整目标及首个未付关系）。** 推论 20.1 关闭了标量总右 Gram 双边族上的余量，与等右 Gram 的 16.2 合用仍只覆盖两个指定输入族。对于两条件都不满足的完成 $x,y$，以及带任意对角背景、$12$ 边或这些部分任意混合的环境输入，本节没有识别一般 $D(Rh,b)$。对一般 $R\ne0$，原未付关系仍是定义 8.3 的同一个 $E_+=E_-$，其差仍准确为 (8.5) 的 $2Rhr$；不把该等式添作新公理。完整奇数阶段 UHF 全表分类和完整量子起源目标保持未结。

**解释 22.5（两个实际反射的完整白话）。** 把前两块看成带相反标记的两条通道，第三块看成共同端点。第一对象在前两块上分别取正、负的同一幅度；标量总右 Gram 使第二对象把两条边合成一条等距通道。除去各自的非零幅度后，两个对象各自在自己的实际支撑上是反射，原来的完整关系便能从两边读取同一个答案：第一遍只留下前两块内部的余量，第二遍又要求这份余量与第二面反射交换，并且只能留在合成通道和共同端点内。余量在共同端点上已经为零，而第二反射恰好交换这个端点与合成通道；若余量在通道上还非零，交换前后就不可能一致，因此也必须为零，已经没有地方容纳它。两条边是同时进入原表的一个输入，没有先把两个答案相加；三进 UHF 所需的第二张整角旧表，由实际角自身的偶维矩阵模型和共同交叠中的同一个非零交换子支付。这个证明更短，也覆盖了一个不等右 Gram 的新输入族，简化来自支撑交换几何，没有减少原公理条数；标量总右 Gram 是输入限制。零幅度直接由原零槽处理。已分类的角具有数学复代数、正 Gram 和 Hilbert 表示，真实准备、完整 Born 菜单、共同相关联合、整台递归仪器全部输出及未来、Return、CountRead、正常性和物理动力学继续由定义 18.2 的整个同源谓词逐项承担，完整量子起源目标没有被这些局部结果替代。

## 追加锚（本行以下为增补区）

## 23. 保留整个实际演员的局部谱对探针

**定义 23.1（同一原条件与局部谱对）。** 全部采用定义 6.1、16.1、19.1 的同一个完整 $\mathsf H_A(D)$：$A$ 为含单位复 C* 代数，原域准确为 $E=A_{\rm sa}$，$S(x,y)=x\circ y=(xy+yx)/2$，原锥为 $A_+$，原单位、范数、$\Omega/\mathrm{native}$、每个原标签、每份分离且准确决定锥的原评价及其全部零、不等、次归一和原表示意义下的非正常质量不变。全部有向 A1/P2、相加三表及全部排列和相加零方向的 A2、同一个固定有理小窗口的 A3，以及每个原三元组的全部实际内外层 PB (19.1)，均保持原量词。未知量仍为同一个任意总映射 $D:E^2\to E$；没有输入线性、齐次、正则性、协变、压缩自然性、商下降、双对偶延拓或有限阶段输出闭合前件。

设实际投影 $P\in A$ 的**整个** $PAP$ 已按 (6.4) 以同一个普通符号 $\sigma\in\{\pm1\}$ 分类，记 $\jmath=\sigma i$。取实际 $c=c^*\in PAP$、正交投影 $l,m\le P$ 及实际自伴 $e\in PAP$，满足

$$
cl=lc=\lambda l,\quad cm=mc=-\lambda m,\quad
\lambda\in\mathbb R\setminus\{0\},\qquad
 e=(l+m)e(l+m),\quad e^2=l+m,\quad el=me.
\tag{23.1}
$$

正 $\lambda$ 是正谱对；允许负 $\lambda$ 仅为交换两格时继续保留原演员 $c$。$c$ 在 $P-l-m$ 上任意；尤其不要求 $c^2=\lambda^2P$。定义原元素

$$
j=\jmath(l-m)e,\quad n=2l.
\tag{23.2}
$$

直接相乘给 $j=j^*$、$j^2=e^2=l+m$、$ej=-je$、$e\circ j=0$、$n\circ j=j$。整个 $PAP$ 的分类准确支付

$$
\begin{gathered}
D(c,e)=\lambda j,\quad D(c,j)=-\lambda e,\quad D(c,n)=0,\\
c\circ e=c\circ j=0,
\qquad c\circ n=\lambda n,\\
D(c,Te+\alpha n)=\lambda Tj
\quad(T,\alpha\in\mathbb R).
\end{gathered}
\tag{23.3}
$$

最后一式在已分类的整个角内逐值成立；它不是对未知环境行使用齐次或可加性。

**定理 23.2（单个局部谱对识别一整条非对角块）。** 在定义 23.1 下，对任意实际环境输入 $t=t^*\in A$，同一个固定旧输出满足

$$
\boxed{\quad l\bigl(D(c,t)-K_\sigma(c,t)\bigr)(1-l)=0.\quad}
\tag{23.4}
$$

这里 $1-l$ 包括 $m$、同一角的其余谱块及整个补角；不压缩演员 $c$ 或第二输入 $t$。

证明。AH43.1 供应反对称性、零槽和同表正读取。对每个数学正实线性泛函 $\phi$，记

$$
B_\phi(X,Y)=\phi(X^2)\phi(Y^2)-\phi(X\circ Y)^2,
\qquad |\phi D(X,Y)|\le\sqrt{B_\phi(X,Y)}.
\tag{23.5}
$$

这只读取原输出，未增加物理准备或归一化原质量。若 $l+m=0$，结论为零。否则固定实际 $c,t$ 及同一个

$$
g=D(c,t),\qquad k=c\circ t,\qquad
V=\lambda n\circ t-n\circ k,\qquad Z=t+\lambda k.
\tag{23.6}
$$

对每个有限实 $T,\alpha$，使用真正原三元组 $\operatorname{PB}(c;Te+\alpha n,t)$。内值准确为 $\lambda Tj,g$，内构造为 $v=\lambda Tj-k,w=\lambda\alpha n+g$，故两份实际外层对是

$$
\begin{aligned}
R_+&=T(e+\lambda j)-k+\alpha n,&
S_+&=t+g+\lambda\alpha n,\\
R_-&=T(e-\lambda j)+k+\alpha n,&
S_-&=t-g-\lambda\alpha n.
\end{aligned}
\tag{23.7}
$$

完整 PB 的原右端只按已知 Jordan 乘法展开：

$$
\begin{aligned}
D(R_+,S_+)-D(R_-,S_-)
&=-2(Te+\alpha n)\circ(\lambda Tj-k)
  -2t\circ(\lambda\alpha n+g)\\
&=2T e\circ k-2t\circ g-2\alpha(\lambda Tj+V).
\end{aligned}
\tag{23.8}
$$

这里使用的恰是 $e\circ j=0,n\circ j=j$；没有平方 $c$ 的步骤。对两份未知外值分别用同一 $\phi$ 的 (23.5)，得到

$$
|\phi(2Te\circ k-2t\circ g-2\alpha(\lambda Tj+V))|
\le\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}.
\tag{23.9}
$$

为完整支付首项提取，置实半内积 $\langle X,Y\rangle_\phi=\phi(X\circ Y)$。对固定自伴 $A_0,B_0,n$ 和实 $\theta$，令 $C_0=B_0-\theta A_0$；直接展开 Gram 行列式得

$$
\begin{aligned}
B_\phi(A_0+\alpha n,B_0+\theta\alpha n)
&=B_\phi(A_0+\alpha n,C_0)\\
&=\alpha^2B_\phi(n,C_0)
 +2\alpha\{\langle A_0,n\rangle_\phi\langle C_0,C_0\rangle_\phi
 -\langle A_0,C_0\rangle_\phi\langle n,C_0\rangle_\phi\}
 +B_\phi(A_0,C_0).
\end{aligned}
\tag{23.10}
$$

在正号对取 $A_0=T(e+\lambda j)-k,B_0=t+g,\theta=\lambda$，有 $C_0=Z+g-\lambda Te-\lambda^2Tj$；在负号对取 $A_0=T(e-\lambda j)+k,B_0=t-g,\theta=-\lambda$，有 $C_0=Z-g+\lambda Te-\lambda^2Tj$。固定 $T,\phi$，将 (23.9) 除以 $|\alpha|$，令 $|\alpha|\to\infty$，得到

$$
\begin{aligned}
2|\phi(\lambda Tj+V)|\le{}&
\sqrt{B_\phi(n,Z+g-\lambda Te-\lambda^2Tj)}\\
&+\sqrt{B_\phi(n,Z-g+\lambda Te-\lambda^2Tj)}.
\end{aligned}
\tag{23.11}
$$

首项为零时，(23.10) 除以 $\alpha^2$ 仍趋零，其非负平方根亦趋零；没有非零首项或非退化半内积假设。

在一份忠实含单位表示 $A\subseteq B(\mathcal H)$ 中计算，内积第一槽共轭线性。$cl=lc=\lambda l,n=2l$ 逐块给

$$
\begin{gathered}
lVl=0,\qquad(1-l)V(1-l)=0,\qquad V=V^*,\\
lV(1-l)=\lambda lt(1-l)-lk(1-l)
=\tfrac12l[c,t](1-l).
\end{gathered}
\tag{23.12}
$$

因此 $V$ 相对 $l\oplus(1-l)$ 完全非对角，即使 $c$ 在余块上任意。取单位 $\xi\in(1-l)\mathcal H$，先设 $d=\|m\xi\|>0$。由于 $j$、$e$ 只交换 $l,m$，定义

$$
\eta=j\xi/d\in l\mathcal H,\quad\|\eta\|=1,
\qquad j\xi=d\eta,\quad e\xi=-\jmath d\eta.
\tag{23.13}
$$

对 $\delta>0$，以 $(\xi+\delta\eta)/\sqrt{1+\delta^2}$ 作数学向量读取 $\phi_\delta$。记实正交投影
$\Pi_\eta z=z-\operatorname{Re}\langle\eta,z\rangle\eta$。任意固定自伴 $W$ 满足

$$
\begin{aligned}
\phi_\delta(n^2)&=\frac{4\delta^2}{1+\delta^2},&
\phi_\delta(W^2)&=\frac{\|W\xi+\delta W\eta\|^2}{1+\delta^2},\\
\phi_\delta(n\circ W)&=
\frac{2\delta\operatorname{Re}\langle\eta,W\xi+\delta W\eta\rangle}{1+\delta^2},&
B_{\phi_\delta}(n,W)&=
\frac{4\delta^2}{(1+\delta^2)^2}
\|\Pi_\eta(W\xi+\delta W\eta)\|^2.
\end{aligned}
\tag{23.14}
$$

又由 (23.12) 和 $j$ 的非对角性，

$$
\phi_\delta(\lambda Tj+V)
=\frac{2\delta}{1+\delta^2}
\bigl(\lambda Td+\operatorname{Re}\langle\eta,V\xi\rangle\bigr).
\tag{23.15}
$$

在 (23.11) 逐项代入 (23.14)–(23.15)，约去正因子 $2\delta/(1+\delta^2)$。固定 $T$ 后令 $\delta\downarrow0$，用 $\Pi_\eta(j\xi)=0$，得

$$
\begin{gathered}
A_\xi=\operatorname{Re}\langle\eta,V\xi\rangle,
\quad z_\pm=\Pi_\eta((Z\pm g)\xi),
\quad u_\xi=e\xi/d=-\jmath\eta,\\
\|u_\xi\|=1,\quad\operatorname{Re}\langle\eta,u_\xi\rangle=0,\\
2|\lambda Td+A_\xi|
\le\|z_+-\lambda Td\,u_\xi\|
  +\|z_-+\lambda Td\,u_\xi\|.
\end{gathered}
\tag{23.16}
$$

为提取两向范数一次项，对固定 $\|u\|=1,z$ 和实 $\rho\ne0$，有准确有理化等式

$$
\|\rho L u+z\|-|\rho|L
=\frac{2\rho L\operatorname{Re}\langle u,z\rangle+\|z\|^2}
       {\|\rho Lu+z\|+|\rho|L}
\longrightarrow\operatorname{sgn}(\rho)\operatorname{Re}\langle u,z\rangle
\quad(L\to+\infty).
\tag{23.17}
$$

令 $\epsilon=\operatorname{sgn}\lambda$，$B_\xi=\operatorname{Re}\langle u_\xi,g\xi\rangle$。在 (23.16) 取 $T=L$，左右均减去 $2|\lambda|dL$。左侧极限为 $2\epsilon A_\xi$；右侧两项的极限分别为
$-\epsilon\operatorname{Re}\langle u_\xi,z_+\rangle$ 和
$\epsilon\operatorname{Re}\langle u_\xi,z_-\rangle$，和为 $-2\epsilon B_\xi$。取 $T=-L$，左侧极限为 $-2\epsilon A_\xi$，右侧两项依次反号，和为 $2\epsilon B_\xi$。两向不等式一起给

$$
A_\xi=-B_\xi,\qquad
\operatorname{Im}\langle\eta,g\xi\rangle
=\sigma\operatorname{Re}\langle\eta,V\xi\rangle.
\tag{23.18}
$$

这里 $\operatorname{Re}\langle u_\xi,z_\pm\rangle
=\operatorname{Re}\langle u_\xi,(Z\pm g)\xi\rangle$，因为被减去的是 $\eta$ 的实倍数；共同的 $Z$ 因而消去。符号 $\epsilon$ 的保留使证明同时覆盖负 $\lambda$。

第二次使用实际伴轴 $e'=j$，仍以同一个 $c$ 为演员、同一个 $t$ 为第二输入。此时 $j'=\jmath(l-m)j=-e$，且 (23.3) 对应为 $D(c,e')=\lambda j',D(c,j')=-\lambda e'$；$n,g,k,V,Z,d$ 全不改变，$\eta'=j'\xi/d=\jmath\eta$。设 $G=\langle\eta,g\xi\rangle$、$L_0=\langle\eta,V\xi\rangle$。第一伴轴给 $\operatorname{Im}G=\sigma\operatorname{Re}L_0$；第二伴轴给
$\operatorname{Im}(-\jmath G)=\sigma\operatorname{Re}(-\jmath L_0)$，即 $-\sigma\operatorname{Re}G=\operatorname{Im}L_0$。故

$$
G=\jmath L_0,\qquad
\langle jm\xi,(g-\jmath V)\xi\rangle=0
\quad(\xi\in(1-l)\mathcal H).
\tag{23.19}
$$

由二次齐次性，单位向量结论扩到全部 $d>0$ 的向量。$d=0$ 时末式左边本来就是零；不在该情形定义 $\eta$ 或除以 $d$。

令 $M=g-\jmath V$、$r_0=1-l-m$。在 (23.19) 取 $\xi=u+z$，其中 $u\in m\mathcal H,z\in r_0\mathcal H$，再减去 $z=0$ 的等式，得 $\langle ju,Mz\rangle=0$。$j:m\mathcal H\to l\mathcal H$ 是满的等距映射，故 $lMr_0=0$。对 $z=0$，算子 $T_0=mjMm$ 的二次型 $Q(u)=\langle u,T_0u\rangle$ 恒零；不要求 $T_0$ 自伴，复极化给

$$
4\langle u,T_0v\rangle
=Q(u+v)-Q(u-v)-iQ(u+iv)+iQ(u-iv)=0.
\tag{23.20}
$$

故 $T_0=0$，同一满等距性给 $lMm=0$。合并得 $l(g-\jmath V)(1-l)=0$；(23.12) 使它正是 (23.4)。忠实性返回原 $A$。所有极限只作用于显式标量多项式和固定元素 $g,k,V,Z$ 的向量范数；没有把任一变化输入上的未知外响应移入极限。∎

## 24. 有限对称谱演员的中心化余量行

**定理 24.1（有限谱局部反对易演员）。** 保留完整原条件和整个实际 $PAP$ 的同号分类。设 $c=c^*\in PAP$ 在角单位 $P$ 下可逆，谱为有限的非零集合，另有实际 $f=f^*\in PAP$ 满足

$$
f^2=P,\qquad fc=-cf.
\tag{24.1}
$$

则对每个任意环境 $t=t^*\in A$，存在 $s=s^*\in PAP$，使同一个实际旧输出满足

$$
\boxed{D(c,t)=K_\sigma(c,t)+s,\qquad [c,s]=0.}
\tag{24.2}
$$

$P=0,c=0$ 的零角按零槽取 $s=0$。此为余量行，不宣称一般环境整行已有 $s=0$。

证明。以下设 $P\ne0$。角内酉元 $f$ 的共轭把 $c$ 变成 $-c$，所以谱对称。写互异正数 $\lambda_1,\ldots,\lambda_N$，并在同一**实际原代数**中取有限谱投影

$$
\begin{gathered}
l_j=1_{\{\lambda_j\}}(c),\qquad
m_j=1_{\{-\lambda_j\}}(c),\qquad p_j=l_j+m_j,\\
P=\sum_{j=1}^N p_j,\qquad
c=\sum_{j=1}^N\lambda_j(l_j-m_j),\qquad
fl_j=m_jf,\quad fp_j=p_jf.
\end{gathered}
\tag{24.3}
$$

这些投影由角内有限 Lagrange 多项式演算得到，属于 $PAP\subset A$；没有调用表示外或双对偶谱投影。令

$$
e_j=fp_j,\qquad j_j=\jmath(l_j-m_j)e_j.
\tag{24.4}
$$

则 $e_j=e_j^*$、$e_j^2=p_j$ 且交换 $l_j,m_j$。整个 $PAP$ 的分类逐值支付 $D(c,e_j)=\lambda_jj_j,D(c,j_j)=-\lambda_je_j,D(c,2l_j)=0$，虽 $c$ 在其余 $p_k$ 上仍有不同谱值。固定 $g=D(c,t)$、$M=g-K_\sigma(c,t)$，用定理 23.2 得 $l_jM(1-l_j)=0$。

对负谱块准确取 $(l,m,\lambda,e,j,n)=(m_j,l_j,-\lambda_j,e_j,-j_j,2m_j)$。演员仍是**原来的 $c$**，实际内值是

$$
D(c,e_j)=(-\lambda_j)(-j_j),\quad
D(c,-j_j)=\lambda_je_j=-(-\lambda_j)e_j,\quad
c\circ(2m_j)=-\lambda_j(2m_j).
\tag{24.5}
$$

这些是整个角的已证公式，不从 $D(-c,t)$ 推断 $D(c,t)$。定理 23.2 的负 $\lambda$ 版本给 $m_jM(1-m_j)=0$。因 $M=M^*$，所有反向块也为零。

令 $Q=1-P$。$c$ 在 $P\mathcal H$ 上有界可逆，故 $\ker c=Q\mathcal H$。对每个 $\xi\in Q\mathcal H$，原 $(c,t)$ 的 P2 读取第一平方为零，给 $\langle\xi,g\xi\rangle=0$；在该子空间内极化得 $QgQ=0$。又 $QK_\sigma(c,t)Q=0$，故 $QMQ=0$。有限分割 (24.3) 连同 $Q$ 已穷尽单位，遂有原元素等式

$$
M=\sum_{j=1}^N(l_jMl_j+m_jMm_j)=:s\in(PAP)_{\rm sa},
\qquad[c,s]=0.
\tag{24.6}
$$

求和只分解固定的一个输出算子，未对未知 $D$ 的输入作和式展开。∎

## 25. 有限非标量总右 Gram 的完整双边响应

**定义 25.1（实际双边与正可逆有限谱输入族）。** 取 $A=M_3(B)$，$B$ 为任意含单位复 C* 代数；$p,q,h,e$ 保持 (19.2)。原条件完整取定义 23.1。对任意完成系数 $x,y\in B$，置

$$
\begin{gathered}
c_0=x^*x+y^*y,\qquad
v=E_{13}x+E_{23}y,\qquad b=v+v^*,\\
\iota(z)=E_{33}z:\ B\overset{*}{\cong}qAq.
\end{gathered}
\tag{25.1}
$$

本节输入限制为 $c_0$ 正、可逆且谱有限；写互异正数的谱为 $\{\mu_1,\ldots,\mu_N\}$，不要求 $N=1$。在已知 C* 乘法中定义

$$
u=v\iota(c_0^{-1/2}),\quad d=\iota(c_0^{1/2}),\quad
P_0=uu^*,\quad P=P_0+q,\quad f=P_0-q.
\tag{25.2}
$$

对一般 $B$，明确假定同一旧 $D$ 在整个 $pAp$ 和整个实际 $PAP$ 上均以**同一个** $\sigma$ 分类。谱限制及这两份角分类的条件不被改写为新的原公理；25.3 在奇数阶段 UHF 中供应角分类。

**定理 25.2（有限总右 Gram 双边族）。** 在定义 25.1 下，对全部实 $R$，同一个实际旧输出满足

$$
\boxed{\begin{aligned}
D(Rh,b)&=K_\sigma(Rh,b)\\
&=\frac{\sigma iR}{2}
\bigl(E_{13}x-E_{31}x^*-E_{23}y+E_{32}y^*\bigr).
\end{aligned}}
\tag{25.3}
$$

系数是任意满足该输入限制的完成元素；无需 $x,y$ 正规、彼此交换、右 Gram 相等或位于某个有限矩阵阶段。

证明。零代数、$R=0$ 或 $x=y=0$ 时直接用零槽；在非零代数中后者不属可逆 $c_0$ 的分支，仍保留其原零输入结论。以下设 $B\ne0,R\ne0$ 且 $c_0$ 正可逆有限谱。由 $v^*v=\iota(c_0)$、$pv=v=vq$、$qv=vp=0$，已知乘法准确给

$$
\begin{gathered}
u^*u=q,\quad u^2=0,\quad P_0=uu^*\le p,
\quad P_0q=0,\quad v=ud,\quad v^*=du^*,\\
b=ud+du^*,\qquad
b^2=u\iota(c_0)u^*+\iota(c_0),\qquad
f=f^*,\quad f^2=P,\quad fb=-bf.
\end{gathered}
\tag{25.4}
$$

特别 $P_0$ 是原代数中的实际投影。$b$ 在 $PAP$ 中的逆为 $u\iota(c_0^{-1/2})+\iota(c_0^{-1/2})u^*$：两种乘法次序均给 $P_0+q=P$。因此其表示中的核准确为 $(1-P)\mathcal H$。

为明确有限谱的实际实现，令 $z_j=1_{\{\mu_j\}}(c_0)\in B$、$r_j=\iota(z_j)$，并取

$$
\begin{gathered}
P_j=ur_ju^*+r_j,\qquad H_j=ur_j+r_ju^*,\\
H_j=H_j^*,\quad H_j^2=P_j,\quad
\sum_jP_j=P,\quad bP_j=\sqrt{\mu_j}\,H_j,\\
l_j=(P_j+H_j)/2,\quad m_j=(P_j-H_j)/2,\qquad
b=\sum_j\sqrt{\mu_j}(l_j-m_j).
\end{gathered}
\tag{25.5}
$$

不同 $P_j$ 正交；$l_j,m_j$ 是正交的实际谱投影，且 $fl_j=m_jf$。这些等式证明 $b$ 的角内谱正是 $\{\pm\sqrt{\mu_j}:1\le j\le N\}$，并支付定理 24.1 的有限谱及实际反对易前件。没有把归一化的 $b$ 代入未知 $D$。

现在固定 $a=Rh$、$g=D(a,b)$。第一遍直接消费 7.1，使用实际 $h,e$、整个 $pAp$ 的分类及完整环境输入 $b$：

$$
g=K_\sigma(a,b)+r,\qquad
r=r^*\in pAp,\qquad[h,r]=0.
\tag{25.6}
$$

第二遍对实际有序对 $(b,a)$ 使用定理 24.1，整个角为 $PAP$、实际反对易元为 $f$，给

$$
D(b,a)=K_\sigma(b,a)+s,\qquad
s=s^*\in PAP,\qquad[b,s]=0.
\tag{25.7}
$$

这里 $D$ 的首输入就是整个 $b$，未提取 $\sqrt{\mu_j}$、$c_0^{1/2}$ 或任何谱投影。反对称性只比较同一旧表的反向值，得 $r=-s$。故

$$
r\in PAP,\quad[b,r]=0,\quad qr=rq=0,\qquad
r=PrP=P_0rP_0.
\tag{25.8}
$$

在 $[b,r]=0$ 左乘 $q$，由 $qb=du^*$、$qr=0$ 得

$$
0=q[b,r]=du^*r.
\tag{25.9}
$$

$d$ 在 $qAq$ 中的逆是 $\iota(c_0^{-1/2})$，而 $u^*r=qu^*r$，所以 $u^*r=0$。再用 $r=P_0r=uu^*r$ 得 $r=0$，证明 (25.3)。

若恰有一条边为零而 $c_0$ 仍可逆，上述 $u^*u=q$ 和全部等式照常成立：从未求 $x$ 或 $y$ 的逆，也未除以其范数。若允许退化的 $c_0=0$，则两个正元之和为零及 C* 恒等式给 $x=y=0$，仍由零槽得同式。这里没有覆盖其余非可逆总右 Gram。∎

**推论 25.3（奇数阶段 UHF 的任意完成系数）。** 设非零无限 UHF $B$ 带有实际递增含单位模型 $B_n\cong M_{d_n}(\mathbb C)$，其并在 $B$ 中范数稠密；各 $d_n$ 为奇数。取 $A=M_3(B)$，同一原总映射 $D$ 满足完整 $\mathsf H_A(D)$。则 AH72.1 的同一个普通符号 $\sigma$ 使 (25.3) 对所有实 $R$ 及所有满足正可逆有限谱总右 Gram 的完成 $x,y\in B$ 成立，不另要求任何角分类或 $P$ 位于原有限阶段。

证明。$A_n=M_3(B_n)$ 是 $A$ 的实际满矩阵模型；$p$ 在每个阶段的矩阵秩为 $2d_n$，故 AH71.2 分类整个 $pAp$，AH72.1 供应共同 $\sigma$。这只使用其已有实际偶角结论，不声称整个奇数阶段 $A$ 已分类。

对 (25.2) 的具体实际 $P$，完整原域保证 $P\in E$。W119.2–119.3 准确给

$$
\begin{gathered}
D((PAP)_{\rm sa},(PAP)_{\rm sa})\subseteq(PAP)_{\rm sa},\qquad
(PAP)_+=A_+\cap PAP,\qquad 1_{PAP}=P,\\
N_P=\|\cdot\|_A|_{PAP},\qquad
\gamma_P=\gamma|_{(PAP)_{\rm sa}},\qquad m_\gamma^P=\gamma(P).
\end{gathered}
\tag{25.10}
$$

保留每个原评价标签，不合并同值限制、不删零限制、不除以质量。限制评价准确决定角锥并分离角内元素；有向 P2、A2 的全部三表及排列、同一个有理窗口的 A3 均继承。对任意角内原三元组，内层输出由 (25.10) 留在角中，Jordan 运算及实际外标签亦留在角中，外输出再次由同式闭合。因此 W 式 (120.2) 的**全部实际 PB** 逐值继承。

(20.2)–(20.8) 的角供应只用 $u^*u=q,uu^*=P_0\le p$ 及 $B$ 的实际模型，不用总右 Gram 是标量。对本节的实际 $u$，其完整参数仍为

$$
\begin{aligned}
\Phi:M_2(B)&\overset{*}{\cong}PAP,\\
\Phi((z_{ij}))&=u\iota(z_{11})u^*+u\iota(z_{12})
 +\iota(z_{21})u^*+\iota(z_{22}),\\
\Phi^{-1}(T)&=
\begin{pmatrix}
\iota^{-1}(u^*Tu)&\iota^{-1}(u^*Tq)\\
\iota^{-1}(qTu)&\iota^{-1}(qTq)
\end{pmatrix}.
\end{aligned}
\tag{25.11}
$$

实际矩阵单位是 $P_0,u,u^*,q$，单位之和是 $P$。乘法和伴随由 $u^*u=q$ 逐项保持；四个逆坐标在 $qAq$ 内。展开 $T=(P_0+q)T(P_0+q)$，分别用 $P_0=uu^*$，便得 $\Phi\Phi^{-1}(T)=T$；反向逐坐标给恒等。这支付覆盖**整个**实际角的成熟 * 同构，而非仅一份子代数。

因此有真正位于原 $A$ 中的模型

$$
\mathcal A_n^P=\Phi(M_2(B_n)),\qquad
\mathcal A_n^P\cong M_{2d_n}(\mathbb C),\quad
1_{\mathcal A_n^P}=P,\qquad
PAP=\overline{\bigcup_n\mathcal A_n^P}^{\|\cdot\|}.
\tag{25.12}
$$

密度仅来自已知 * 同构的等距性。AH70.1 直接作用于此实际载体、同一个限制总映射 $D_P$ 和刚继承的完整原条件，给唯一普通符号 $\sigma_P$，使

$$
D(z,t)=\frac{\sigma_P i}{2}[z,t]
\quad(z,t\in(PAP)_{\rm sa}).
\tag{25.13}
$$

没有先声明 $D$ 对 $\Phi$ 协变，没有让输入极限穿过 $D$，也没有有限阶段输出闭合假设。

最后准确重复 (20.6)–(20.8) 的非零交叠比较。$P_0AP_0\subseteq pAp\cap PAP$，且 $z\mapsto u\iota(z)u^*$ 是 $B\overset{*}{\cong}P_0AP_0$。无限 UHF 的某个实际矩阵阶段阶数至少为二，可取其中自伴 $d_B,t_B$ 使 $[d_B,t_B]\ne0$；例如两条矩阵坐标上的对角差和对称非对角元。令

$$
\alpha=u\iota(d_B)u^*,\quad\beta=u\iota(t_B)u^*,
\qquad [\alpha,\beta]=u\iota([d_B,t_B])u^*\ne0.
\tag{25.14}
$$

非零性可左乘 $u^*$、右乘 $u$ 检验。两份已分类的整个角对**同一原输出**给

$$
D(\alpha,\beta)=\frac{\sigma i}{2}[\alpha,\beta]
              =\frac{\sigma_P i}{2}[\alpha,\beta],
\qquad \sigma_P=\sigma.
\tag{25.15}
$$

这支付定义 25.1 的第二整体角及同号前件，故定理 25.2 适用。特别包括 $B=M_{3^\infty}$；$P$、$x$、$y$ 均不必属于原有限阶段。∎

**输入族 25.4（无需交换的完成参数）。** 对任意正可逆有限谱 $c_0\in B$、任意 $0\le T\le1_B$ 及任意酉元 $v_0,w_0\in B$，准确取

$$
x=v_0T^{1/2}c_0^{1/2},\qquad
y=w_0(1_B-T)^{1/2}c_0^{1/2}.
\tag{25.16}
$$

因子次序给

$$
x^*x=c_0^{1/2}Tc_0^{1/2},\qquad
y^*y=c_0^{1/2}(1_B-T)c_0^{1/2},\qquad
x^*x+y^*y=c_0.
\tag{25.17}
$$

所以不要求 $[T,c_0]=0$；$T=0,1_B$ 给一边为零的端点。参数检验只使用已知乘法，不对旧 $D$ 作酉协变、求和或取极限。

这个族包含真正不在任何原有限阶段的系数，而不是仅有 AH42.4 已覆盖的有限维例子。例如在标准 $B=M_{3^\infty}$ 中，取首个张量因子的非交换秩一投影 $r,s$，以及第 $n\ge2$ 个张量因子的秩一投影 $s_n$，令

$$
c_0=\mu r+\nu(1_B-r),\quad
\mu,\nu>0,\quad\mu\ne\nu,\qquad
T=\tfrac13s+\sum_{n=2}^{\infty}2\,3^{-n}s_n.
\tag{25.18}
$$

这是已知 C* 代数中范数收敛的正级数，$0\le T\le(2/3)1_B$，且 $[T,c_0]=(\mu-\nu)[s,r]/3\ne0$。对每个 $n\ge2$，在该张量因子取 $z_n$ 使 $[s_n,z_n]\ne0$，则 $[T,z_n]=2\,3^{-n}[s_n,z_n]\ne0$。任何首 $N$ 个因子中的元素都与 $n>N$ 的 $z_n$ 交换，故 $T$ 不在任何这样的有限阶段。取 (25.16) 的 $v_0=w_0=1_B$；若 $x$ 或 $y$ 在某个原有限阶段，则由 (25.17) 和同一阶段之后的 $c_0^{-1/2}$ 分别得到 $T$ 或 $1_B-T$ 也在某个有限阶段，矛盾。因此两系数都是真正的完成元素，而总右 Gram 仍只有两个正谱值。这一构造不向未知 $D$ 传递任何级数极限。

## 26. 归属、准确量子对应与保留的全局边界

**归属 26.1（可复用探针与成熟谱工具）。** 本节的 $\texttt{repo-derived}$ 条件纸面综合由一份局部谱对探针、有限实际谱分割及两份支撑的交集组成。23.2 保留整个 $c$ 并支付全部真实外标签，故不把 7.1 的标量平方前件直接删掉；24.1 只对固定输出作有限谱块分解；25.2 以实际 $b$ 的中心化余量和第一局部反射的支撑余量比较，25.3 的第二角供应复用 (20.2)–(20.8) 的实际内在偶维模型和非零交叠。标量总右 Gram 的 19.2–20.1 是 $N=1$ 的已成范围，等右 Gram 的 16.2 仍保留其无需可逆或有限谱的原范围。

仓内已有的 PBIdempotentSupport 原二表角支撑、PBActualOuterBudget 实际外层预算、W119.2–119.3、120.2 及 AH43.1、70.1、71.2、72.1 均按原前件直接复用。谱混合响应卷 40–41 的有限谱背景行及 55–56 的窗缺陷定位要求实际**全单位**框架；CC147–150 的双伴轴与一次范数预算同样有其原框架前件。它们不直接供应 (23.1) 中仅一对局部谱格且余块任意的整个演员行。有限维、连续迹或已有更强全域分类覆盖的情形直接消费 AH42.4 等既有结论，不将有限维特例、成熟谱演算或普通角同构另算基础分类。

AH 的直接身份仍为 `b1a95e41b9622e9f720e51f9bb899841f5b74ca1`，W、CC 的直接身份仍为 `3b10aed60f60e4901bae6cf2e160bf439d642e64`；各自递归固定引文不被覆盖。对照的谱混合响应卷和 D5/Blueprint 数学源码取 `d2e4fc3127389e556fa518d82d6d849de98d74f5`。成熟工具归于 Blackadar，[*Operator Algebras*](https://bruceblackadar.com/Mathematics/Cycr.pdf)，II.2.3.1–4 的连续函数演算与谱映射、II.2.3.5 的部分等距支撑、II.3.3.4 的等价投影、II.6.6.8 的矩阵单位记号及 II.8.2.2(iv) 的 UHF 模型。有限谱上的特征函数是连续函数，也可直接用有限 Lagrange 多项式取得，故本文使用的是原代数中的实际投影。忠实表示、正读取和数学 GNS 沿定义 10.1 的 Gelfand–Naimark、Segal；Peirce 规则沿该处 Hanche-Olsen–Størmer §2.6.2、Lemma 2.6.3。Gram 展开、范数有理化及复极化已在证明中逐式给出。这些成熟工具不承担本文局部原响应结论的优先权；本文不主张文献穷尽、历史原创、外部开放问题解决或原独立公理减少。

**对应 26.2（已识别的乘法值与已有后端）。** 对 25.2–25.3 的每一实际输入对 $a=Rh,b$，准确有

$$
S(a,b)-iD(a,b)
=\frac{ab+ba}{2}+\frac\sigma2(ab-ba)
=\begin{cases}ab,&\sigma=1,\\ba,&\sigma=-1.\end{cases}
\tag{26.1}
$$

24.1 的一般余量行本身只给 $S(c,t)-iD(c,t)$ 等于相应通常或相反乘法值再减 $is$；仅在 25.2 消去同一余量后，才得到 (26.1)。不能把中心化余量的存在当作整行标准化。

在已经整体分类的 $pAp$ 和 $PAP$ 上，AH64.1、75.1 给 $S-iD$ 的复线性延拓为通常或相反 C* 乘法，伴随、准确锥、单位和范数不变；所有有限旧复 Gram 为正，每个原限制评价有数学 GNS，循环向量平方范数分别为 $\gamma(p),\gamma(P)$，零角质量对应零向量。共同符号使这些角乘法在实际交叠上相容。单对公式 (26.1) 没有给整个奇数阶段环境的全域双线性、结合乘法或全部有限旧复 Gram。

Alfsen–Shultz，[*Orientation in operator algebras*](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/)，PNAS **95**，6596–6601，DOI `10.1073/pnas.95.12.6596`，Dynamical Correspondences、Theorem 1，提供取向与 Jordan 相容 C* 乘法的成熟对应；其 dynamical correspondence 是从含单位 JB 代数到 skew order derivations 的**线性**映射。局部谱行不赠予该全域前件，也不赠予物理时间或正常性。

**定义 26.3（与 22.3、18.2 完全相同的全文来源谓词）。** 本节的完整物理来源准确就是定义 22.3 所严格引用的定义 18.2 的同一个 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$，**整个 18.2 连同其引用的 10.2、15.2、AH28.1、64.2、75.1、SQ47.1–47.13 及每项逐层固定版本的递归上游全文，逐句、逐公式、逐量词同时纳入**。这里是原谓词的身份保持，不定义缩短替代谓词。

SQ 主源仍按其自身 1.3、39、41.1、47.1 解析；`dcaebc0b9ca5a3a463fd8cfd161d38967df28668` 与 `0aa11dbc3dc337d667b98900673e07d67b99bf46` 的对应层级、OP/PT/PB/SM/C/AQ/R3/W/FR/XV/SF 的 `f24d1138a7b994da16abd9a47affedea64ea44ce`、AH22.1 保留的 `2addd6f369b7387226c2b0cc984623dd3efe40a1` 及 AH12.1 上游 `39a0505470ea889dd9d4301ad60cd9506a5e8b58` 均原样保持。AH42.1 中 OP 等直接身份 `bef9bba367a24ab5e250491dcb88ed85ebc29cf7` 也不被本节直接 AH/W 读取身份压平。原根、静默及其他静态分支不改为 UHF。下文范围说明不替代其中任何被纳入的全文或原前件。

实际准备、相干控制、原事件绑定的实际完整 Born 菜单、质量及角菜单的真实条件化仍须原来源；只在严格正的相应实际质量上归一，零、不等、次归一和非正常质量均保留。真正相关联合与张量须同一实际共同来源、全部相关输入、忠实同向交换局部腿、共同生成、分离和所需重数；数学谱投影、相同边缘和角交叠不生产这些关系。

typed CP、箭头下降、整台递归同源参考、原真支持与支持内补、交织夹界、每个所需有限深度及正精度，仍保留全部原前件。完整仪器、TP、Kraus、更新和 Lüders 仍要求其完整 typed 菜单、完整单位分区、接受端、校准、表示与收敛条件，并量化**整个环境、全部成功／失败／细记录／port／post-port 输出，以及每份完整输出的每个仍合法未来**，不以有限谱角替代任何一份输出或未来。

合法顺序／自适应／并行历史、真正分组遗忘、停止、拒绝、销毁、泄漏、同数两侧和逆向真实 Return、完整 CountRead 的活动 ready 与 producer 全部保持。相同算子不合并原程序、记录、读序、原零集或未来权限；未定义请求不补零。正常性、指定前对偶、无限菜单和记录的可数可加及收敛，仍需原扩展来源。保持原域的实际连续可逆流、实际逆、物理钟和单位、适用酉实现及生成元域、Hamiltonian 能量解释、作用量与共同正 $\hbar$，仍由整个原谓词逐项承担。$\lambda_j,\mu_j,R,T,\alpha,\delta$、数学部分等距和谱格都不生产这些物理来源。

**边界 26.4（有限谱闭合及首个仍未支付的关系）。** 在奇数阶段 UHF 应用中，25.3 关闭正可逆**有限谱**总右 Gram 的整个双边输入族，不要求两条右 Gram 相等或总 Gram 为标量。这不以有限谱逼近推广到无限谱总 Gram，也不覆盖一般非可逆总 Gram；16.2 已有的等右 Gram 退化族和先前已识别单边仍各守其原范围。含任意对角背景、$12$ 边及这些部分任意和的环境输入亦未取得一般旧行可加性。

对本节所闭合的输入，定义 8.3 的两份实际外层缺陷确有 $E_+=E_-$，因为 25.2 给 $r=0$。对一般未覆盖的 $R\ne0,b=b^*\in A$，首个未付关系仍是同一份实际 $E_+=E_-$，差仍准确为 (8.5) 的 $2Rhr$；这里没有将该等式添作公理。全奇数阶段 UHF 分类、从混合整行接回全域分类，以及完整量子起源及其整个来源满足性，均保持原目标与未结边界。

**解释 26.5（一个谱对探针与支撑交集的完整白话）。** 把同一个对象的有限谱想成若干对正负刻度，每对刻度之间已有一条实际交换通道；只探查其中一对时，整个对象仍坐在原来的位置，其余所有刻度和角外环境都保留，不能先把对象压进这两个格子。原完整 PB 比较两份真实外响应，同一个二表预算先随一个有限标签放大，再在数学读取中轻轻混入另一格；向正、负两边观察范数的一次项，并换用第二条实际伴通道，就能锁住这一谱格接向所有其余格子的整条连线，不需要整个对象平方为一个标量。有限多对刻度把这些连线全部锁住后，同一个答案只可能留下各刻度内部的余量。对于两条同时接向共同端点的边，正可逆有限总右 Gram 允许在已知代数中辨认一条实际等距通道和它的支撑；这是构造通道，并没有把因子从未知响应中抽出来。第一面局部反射要求余量只在前两块内，有限谱探针从反向的同一个答案又要求余量留在合成通道和共同端点内，并与整个第二对象交换。它在共同端点上已经为零，第二对象又以可逆强度连接端点和通道，所以通道上也不能剩任何余量。奇数阶段 UHF 所需的第二张整角旧表，由这个实际角自己的偶维模型及交叠中的同一个非零交换子供应；无需假装原输入落在某个有限阶段。简化是一份可复用探针加支撑交集，没有减少原公理。这里总右 Gram 可以有限非标量，两个系数本身则可以是真正的完成元素；无限谱总 Gram、任意背景整行和全局量子起源仍未闭合。已分类角保有复乘法、正 Gram 和数学 Hilbert 表示，真实准备与完整 Born 菜单、共同相关联合、整台递归仪器的全部输出和未来、Return、CountRead、正常性及物理动力学，仍须同一个完整原来源谓词逐项成立。

## 追加锚（本行以下为增补区）

## 27. 有限非可逆总右 Gram 的自然支撑响应

### 27.1 原条件、记号与来源谓词的身份保持

本节在 §§23–26 的同一原条件上追加。令 $B$ 为含单位复 $C^*$-代数，$A=M_3(B)$，$E=A_{\rm sa}$，$a\circ b=(ab+ba)/2$，$p=E_{11}+E_{22}$，$q=E_{33}$，
$$
 h=E_{11}-E_{22},\qquad e_{12}=E_{12}+E_{21},\qquad \iota(z)=E_{33}z .
$$
未知量仍是一个**总的任意映射** $D:E^2\to E$。原正实线性评价族 $\mathcal P$ 分离 $E$ 并准确决定 $A_+$；每个原标签、每份评价及质量 $m_\gamma=\gamma(1)$ 全部保留，包括零、不等、次归一和原表示意义下的非正常质量。

完整 $\mathsf H_A(D)$ 逐项不变：所有有向 A1/P2 及两种次序
$$
\begin{pmatrix}
\gamma(a^2)&\gamma(a\circ b)-i\gamma D(a,b)\\
\gamma(b\circ a)-i\gamma D(b,a)&\gamma(b^2)
\end{pmatrix}\succeq0\qquad(a,b\in E,\ \gamma\in\mathcal P),
$$
全部相加三表 $(a+b,a,b)$ 及其排列在整个 $\mathbb R^3$ 上的 A2 实部正性，具体即每个排列 $(a_1,a_2,a_3)$ 的实矩阵 $(\gamma(a_i\circ a_j))_{i,j=1}^3$ 半正定，并保留指定相加零方向；$1^2=1$ 及固定有理 $0<\vartheta\le1$ 下的 A3：$0\le a\le\vartheta1\Rightarrow a^2\le a$。对每个实际三元组 $(c;x,y)$，以及由任何内值、外值、缩放、平移和背景再次形成的每一个实际嵌套调用，均保留同一个 PB
$$
 v=D(c,x)-c\circ y,\qquad w=c\circ x+D(c,y),\qquad
 D(x+v,y+w)-D(x-v,y-w)=-2x\circ v-2y\circ w.
$$
不加入输入线性、齐次性、连续性、可测性、协变性、压缩自然性、商下降、双对偶延拓或有限阶段输出闭合。

完整物理来源谓词也只作身份保持：本文的 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$ **就是**定义 26.3 的谓词，按定义 22.3、18.2 的逐句、逐公式、逐量词递归全文纳入，包含其固定的 AH28.1、64.2、75.1、SQ47.1–47.13 及每一项固定版本的上游全文；不定义缩短替代物，不改动任何 pinned layer、原根、静默或其他静态分支。

下文消费 AH43.1 的反对称性、零槽和数学正读取，消费 §§7、24 已完成的定理，其中 24.1 是下述响应定理的明确数学前件。$K_\sigma(a,b)=\sigma i[a,b]/2$，其中 $\sigma\in\{\pm1\}$ 是同一实际角的符号。

### 27.2 自然支撑构造

给定 $x,y\in B$，置
$$
 c_0=x^*x+y^*y,\qquad v=E_{13}x+E_{23}y,\qquad b=v+v^* .
$$
假设 $\operatorname{sp}(c_0)$ 为有限集。若 $c_0\ne0$，写其正谱为 $\{\mu_1,\ldots,\mu_N\}\subset(0,\infty)$，并令
$$
 e_c=1_{(0,\infty)}(c_0),\qquad
 g(0)=0,\quad g(\mu_j)=\mu_j^{-1/2},\qquad
 Q=\iota(e_c),\quad d=\iota(c_0^{1/2}),\quad u=v\,\iota(g(c_0)).
$$
这里 $e_c$ 和 $g(c_0)$ 是实际 $B$ 元素：有限谱函数由有限 Lagrange 多项式给出。记号 $e_c$ 专门避免与固定的 $e_{12}$ 混淆。

由
$$
 (1-e_c)c_0(1-e_c)=(x(1-e_c))^*x(1-e_c)+(y(1-e_c))^*y(1-e_c)=0
$$
及正元平方为零即元为零，得 $x(1-e_c)=y(1-e_c)=0$。所以 $v=vQ$，$v^*=Qv^*$，并且
$$
 g(c_0)c_0g(c_0)=e_c,\qquad
 u^*u=Q,\qquad P_0:=uu^*\le p,\qquad P:=P_0+Q.
$$
因此 $P_0,Q,P$ 是实际投影，且
$$
 ud=v,\qquad b=ud+du^*,\qquad f:=P_0-Q=f^*,\qquad f^2=P,\qquad fb=-bf.
$$
在 $QAQ\cong e_cBe_c$ 内，$d$ 的逆是 $\iota(g(c_0))$；这只是支撑角内的逆，绝不是 $c_0$ 在整个 $B$ 中可逆。由此
$$
 b^{-1}_{PAP}=u\,\iota(g(c_0))+\iota(g(c_0))u^*.
$$
若 $z_j=1_{\{\mu_j\}}(c_0)$、$Q_j=\iota(z_j)$，则实际谱块
$$
 P_j=uQ_ju^*+Q_j,\quad H_j=uQ_j+Q_ju^*,\quad
 H_j^2=P_j,\quad b=\sum_j\sqrt{\mu_j}\,H_j,
$$
且 $l_j=(P_j+H_j)/2,\ m_j=(P_j-H_j)/2$ 是实际投影，$f l_j=m_jf$。故 $b$ 在单位为 $P$ 的 $PAP$ 中可逆，谱是有限的非零对称集 $\{\pm\sqrt{\mu_j}\}$。这些等式只用已知 $C^*$-乘法。

### 27.3 支撑角已分类时的完整响应

**定理 27.1（有限总右 Gram 的自然支撑响应）。** 在 §27.1 的完整原条件下，假设 $c_0\ne0$ 且 $\operatorname{sp}(c_0)$ 有限，同一个 $D$ 在整个 $pAp$ 与整个实际 $PAP$ 上都以同一个 $\sigma$ 分类。则对所有 $R\in\mathbb R$，
$$
\boxed{
D(Rh,b)=K_\sigma(Rh,b)=\frac{\sigma iR}{2}
\bigl(E_{13}x-E_{31}x^*-E_{23}y+E_{32}y^*\bigr).}
$$

**证明。** $R=0$ 时由零槽成立。以下 $R\ne0$。对实际有序对 $(Rh,b)$ 使用已完成的 §7.1（同一原 PB、同一任意环境输入），得到
$$
 g:=D(Rh,b)=K_\sigma(Rh,b)+r,\qquad r=r^*\in pAp,\qquad [h,r]=0. \tag{27.1}
$$
对反向有序对 $(b,Rh)$ 使用已完成的定理 24.1；§27.2 已给出其实际 actor $b\in PAP$ 的有限非零对称谱、实际对合 $f^2=P$ 及 $fb=-bf$。于是
$$
 D(b,Rh)=K_\sigma(b,Rh)+s,\qquad s=s^*\in PAP,\qquad [b,s]=0. \tag{27.2}
$$
反对称性比较的是同一旧表的同一反向输出，故 $r=-s$。于是
$$
 r\in PAP,\qquad [b,r]=0,\qquad Qr=rQ=0,\qquad r=PrP=P_0rP_0. \tag{27.3}
$$
因 $qb=du^*$、$qr=0$，$[b,r]=0$ 给出
$$
 0=q[b,r]=du^*r. \tag{27.4}
$$
$d^{-1}=\iota(g(c_0))$ 只存在于 $QAQ$，而 $u^*r=Qu^*r$ 具有左支撑 $Q$。左乘这个角内逆得到 $u^*r=0$。再由 (27.3)，
$$
 r=P_0r=uu^*r=0.
$$
代回 (27.1)，并直接计算
$[h,b]=E_{13}x-E_{23}y-E_{31}x^*+E_{32}y^*$，即得所示公式。证明从未对 $x$ 或 $y$ 求逆、从未把 $D$ 的输入拆开相加，也未让未知 $D$ 穿过输入极限。若 $c_0=0$，则 $x=y=0$，$b=0$，同一零槽给出同一盒装公式；零代数按同样等式成立。∎

### 27.4 无限奇数阶段 UHF 中不再需要第二角前件

**推论 27.2（实际无限奇数阶段 UHF）。** 设 $B=\overline{\bigcup_nB_n}$ 是无限 UHF，$B_n\cong M_{d_n}(\mathbb C)$，各 $d_n$ 为奇数；特别包括 $M_{3^\infty}$。若 $D$ 满足 §27.1 的完整 $\mathsf H_A(D)$，则定理 27.1 对所有 $x,y\in B$ 且 $\operatorname{sp}(x^*x+y^*y)$ 有限成立，不要求该 Gram 可逆，也不要求 $x,y$ 属于任何原有限阶段。

**证明。** $p=E_{11}+E_{22}$ 在实际有限阶段 $A_n=M_3(B_n)$ 中的秩为 $2d_n$，因而为偶数。W119.2–119.3、W120.2 把完整原候选的所有原评价标签、原质量（包括零与非正常质量）、准确锥、单位、范数、A1/P2、A2、A3 及每一个实际 PB 逐值限制到整个 $pAp$；AH71.2 与 AH72.1 因而给出整个 $pAp$ 的同一符号 $\sigma$。这一步不要求 $D$ 保持任何有限阶段。

若 $c_0=0$，结论已由定理 27.1 的零槽分支给出。以下 $e_c\ne0$。使用 AH67.2 式 (67.3) 的成熟近投影酉共轭构造：存在实际酉 $w\in B$、某 $N$ 和实际 $e_0\in B_N$，使 $we_cw^*=e_0$。令 $k=\operatorname{rank}_{B_N}(e_0)\ge1$，并对 $n\ge N$ 定义
$$
 C_n=w^*e_0B_ne_0w\subset e_cBe_c.
$$
这是实际递增的整个角子代数，单位为 $e_c$，且
$$
 C_n\cong M_{k\,d_n/d_N}(\mathbb C),\qquad
 e_cBe_c=\overline{\bigcup_{n\ge N}C_n}^{\|\cdot\|}. \tag{27.5}
$$
密度只来自 $e_0B_ne_0$ 在 $e_0Be_0$ 中的压缩密度及实际酉共轭；没有把未知 $D$ 对任何逼近列取极限。因 $d_n$ 无界，$e_cBe_c$ 非交换。

§27.2 的实际矩阵单位 $P_0,u,u^*,Q$ 给出整个角的明确同构
$$
 \Phi:M_2(e_cBe_c)\longrightarrow PAP,\qquad
 \Phi((z_{ij}))=u\iota(z_{11})u^*+u\iota(z_{12})+\iota(z_{21})u^*+\iota(z_{22}). \tag{27.6}
$$
逆坐标为
$$
 \Phi^{-1}(T)=
 \begin{pmatrix}\iota^{-1}(u^*Tu)&\iota^{-1}(u^*TQ)\\
 \iota^{-1}(QTu)&\iota^{-1}(QTQ)\end{pmatrix}. \tag{27.7}
$$
四个坐标确在 $QAQ$ 中，且 $P_0+Q=P$；逐项相乘即证 $\Phi$ 覆盖整个 $PAP$。由 (27.5) 得实际递增有限全矩阵子代数
$$
 \mathcal A_n^P=\Phi(M_2(C_n))\cong M_{2k\,d_n/d_N}(\mathbb C),\qquad
 1_{\mathcal A_n^P}=P,\qquad
 PAP=\overline{\bigcup_{n\ge N}\mathcal A_n^P}^{\|\cdot\|}. \tag{27.8}
$$
它们的阶数全为偶数。W119–120 的完整实际角限制适用于这个具体 $P$，所以 AH70.1 直接作用于实际载体 $PAP$ 和同一个限制 $D_P$，给出某个 $\sigma_P$ 的整个角分类。这里没有假定 $D$ 对 $\Phi$ 协变，也没有假定输出落在 $\mathcal A_n^P$。

为比较符号，取 $n$ 使 $k\,d_n/d_N\ge2$，在实际 $C_n$ 中取自伴 $a_0,\beta_0$ 使 $[a_0,\beta_0]\ne0$，并令
$$
 \alpha=u\iota(a_0)u^*,\qquad \beta=u\iota(\beta_0)u^*.
$$
则 $\alpha,\beta\in P_0AP_0\subseteq pAp\cap PAP$，且交换子非零。两份整个角分类对同一原输出给出
$$
 D(\alpha,\beta)=\frac{\sigma i}{2}[\alpha,\beta]
 =\frac{\sigma_P i}{2}[\alpha,\beta],\qquad \sigma_P=\sigma. \tag{27.9}
$$
故定理 27.1 的全部前件已由实际模型支付。注意这里没有声称 $P$ 或 $e_c$ 位于某个原有限阶段；只有 AH67.2 式 (67.3) 的实际酉共轭和 (27.5) 的实际角模型被使用。∎

### 27.5 一个真正非有限阶段的非可逆有限谱族

**命题 27.3（完成系数与非可逆有限谱 Gram）。** 在 $B=M_{3^\infty}$ 中取一个实际有限阶段的非零真投影 $e_c$，并在其角 $e_cBe_c$ 的某个尾部 $M_{3^\infty}$ 中取第一尾因子的秩一投影 $r,s$，满足 $[r,s]\ne0$，以及后续各因子的秩一投影 $s_n$（$n\ge2$）。令
$$
 c_0=\mu r+\nu(e_c-r),\qquad \mu,\nu>0,\quad \mu\ne\nu, \tag{27.10}
$$
并令
$$
 T=\frac13s+\sum_{n=2}^{\infty}2\,3^{-n}s_n. \tag{27.11}
$$
级数在范数中收敛，$0\le T\le(2/3)e_c$，而 $[T,c_0]=(\mu-\nu)[T,r]\ne0$。取
$$
 x=T^{1/2}c_0^{1/2},\qquad y=(e_c-T)^{1/2}c_0^{1/2}. \tag{27.12}
$$
则两系数均不属于任何原有限阶段，且
$$
 x^*x=c_0^{1/2}Tc_0^{1/2},\qquad y^*y=c_0^{1/2}(e_c-T)c_0^{1/2},\qquad x^*x+y^*y=c_0. \tag{27.13}
$$
证明。这个 $c_0$ 在整个 $B$ 中非可逆而在 $e_cBe_c$ 中正且有限谱；(27.12) 不要求 $T$ 与 $c_0$ 交换。先取 $K$ 使 $e_c\in B_K$，命题中的尾部副本取在 $B_K$ 之后，尾部元素均以 $e_c$ 为支撑。对 $T$ 或某一系数属于 $B_N$ 的任一假设，先选共同后续阶段 $B_L$，使其包含 $B_N,e_c,r,s$ 及有限支撑逆 $c_0^{-1/2}=\mu^{-1/2}r+\nu^{-1/2}(e_c-r)$。在此共同阶段之后的尾因子 $n\ge2$ 取支撑于 $e_c$ 的 $z_n$，使 $[s_n,z_n]\ne0$；则 $z_n$ 与 $e_cB_Le_c$ 中每个元素交换，且 $[T,z_n]=2\,3^{-n}[s_n,z_n]\ne0$。由于 $T=e_cTe_c$，若 $T\in B_N$，就有 $T\in e_cB_Le_c$，与此非零交换子矛盾；因此 $T$ 不在任何原有限阶段。若 $x\in B_N$，在上述共同阶段中由 (27.13) 得 $T=c_0^{-1/2}x^*x c_0^{-1/2}\in e_cB_Le_c\subset B_L$，矛盾；若 $y\in B_N$，则 $T=e_c-c_0^{-1/2}y^*y c_0^{-1/2}\in e_cB_Le_c$，同样矛盾。因此两系数都是真正完成元素，而响应定理仍适用。这个族说明“自然支撑”允许非可逆 Gram 和无限阶段系数。∎

### 27.6 乘法对应、成熟归属与全局边界

对定理 27.1 的实际输入 $a=Rh,b=v+v^*$，有
$$
 S(a,b)-iD(a,b)=\frac{ab+ba}{2}+\frac{\sigma}{2}(ab-ba)
 =\begin{cases}ab,&\sigma=1,\\ba,&\sigma=-1.\end{cases} \tag{27.14}
$$
这只是该输入对的准确静态值。已分类的两个角按 AH64.1、75.1 带有相应的通常或相反 $C^*$-乘法、准确锥、单位、范数、原质量和数学 GNS；角质量分别是 $pAp$ 的 $\gamma(p)$ 与 $PAP$ 的 $\gamma(P)$，零质量仍给零向量。

实际投影的有限谱函数、等价投影、部分等距与矩阵单位可归于 Blackadar, *Operator Algebras*, II.2.3.1–5、II.6.6.8、II.8.2.2(iv)，以及 Bratteli, “Inductive limits of finite dimensional $C^*$-algebras,” *Trans. Amer. Math. Soc.* 171 (1972), 195–234；UHF 归纳极限的成熟背景亦见 Glimm, “On a certain class of operator algebras,” *Trans. Amer. Math. Soc.* 95 (1960), 318–340。AH67.2 式 (67.3)、AH70.1、AH71.2、AH72.1 与 W119.2–119.3、W120.2 只按其既有前件消费；本节不把成熟角构造计作新响应定理。

本节没有把自然支撑角、谱分解或 GNS 变成真实准备、实际 Born 菜单、共同来源或联合张量；也没有产生递归整台仪器的全部输出、每份输出的全部未来、Return、CountRead、正常性、指定前对偶、动力学、物理钟或共同正 $\hbar$。无限谱总 Gram、一般非可逆但非有限谱 Gram、任意背景的整行及全局奇数阶段 UHF 分类仍未由此结清；未支付的全局关系仍是 §§8、22、26 所标出的两份实际外层缺陷相等式 $E_+=E_-$。本节只说明：携带实际通道的支撑角足以完成这一个有限谱族，整个 $B$ 的可逆性是多余的。

**完整白话。** 把 $x,y$ 的总右 Gram 看成一盏只在真实支撑 $e_c$ 上点亮的灯：灯外 $x$ 和 $y$ 都已经为零，所以不必把整盏 $B$ 当成可逆的；在灯亮的角里，用有限谱函数把每个非零亮度开方、再倒数，就把两条边合成一条实际等距通道 $u$，它和共同端点 $Q$ 组成真正的二乘角。第一面反射 $h$ 只可能留下前两块的对角余量，反向把同一个 $b$ 当作演员时，有限的正负谱对又迫使余量同时落在这张支撑角里并与 $b$ 交换；余量在端点 $Q$ 上已经没有位置，而 $b$ 在支撑角内把端点和通道以非零有限谱强度接起来，因此余量连通道也不能占据，只能完全消失。这个过程始终对同一个实际输出使用原来的全部 P2、A1–A3 和每一次真实 PB，没有把两个边的答案相加，没有把未知响应对输入取极限，也没有把数学角偷换成物理准备或 Born 菜单；无限 UHF 中即使 $e_c,x,y$ 都不在任何原有限阶段，实际酉共轭仍给出整个支撑角的偶维矩阵模型，所以同一个符号可以由真实交叠锁定。得到的是所有有限谱总右 Gram（包括非可逆、非标量）的这条响应，完整无限谱、任意环境整行和整个量子起源仍由原来的递归来源谓词逐项承担。

## 28. 不平移原演员的相异谱值探针

**定义 28.1（完整原关系与实际谱差）。** 本节起保持定义 6.1 与 §27.1 的同一个完整 $\mathsf H_A(D)$，包括其全部递归固定引文。$A$ 是含单位复 $C^*$-代数，原域准确为 $E=A_{\rm sa}$，$S(x,y)=x\circ y=(xy+yx)/2$，原单位为 $1$，原范数为 $\|\cdot\|$，原锥准确为 $A_+$。同一 $\Omega/\mathrm{native}$、全部原输入与评价标签保持；原正实线性评价族 $\mathcal P$ 分离 $E$ 并准确决定锥。每份原评价及其质量 $m_\gamma=\gamma(1)$ 全部保留，包括零、不等、次归一和原表示意义下的非正常评价。未知量仍是同一个任意总映射 $D:E^2\to E$。

具体地，全部有向 A1/P2 及两种次序仍为

$$
\begin{pmatrix}
\gamma(x^2)&\gamma(x\circ y)-i\gamma D(x,y)\\
\gamma(y\circ x)-i\gamma D(y,x)&\gamma(y^2)
\end{pmatrix}\succeq0
\qquad(x,y\in E,\ \gamma\in\mathcal P).
\tag{28.1}
$$

A2 保留每份相加三表 $(x+y,x,y)$ 及全部排列 $(x_1,x_2,x_3)$：实矩阵 $(\gamma(x_i\circ x_j))_{i,j=1}^3$ 在全部实系数 $\mathbb R^3$ 上半正定，$(1,-1,-1)$ 及相应排列仍给指定零二次值。A3 保留 $1^2=1$，以及同一个固定有理 $0<\vartheta\le1$ 下的全部 $0\le x\le\vartheta1\Rightarrow x^2\le x$。对每个实际原三元组 $(c;x,y)$，完整 PB 仍是

$$
\begin{gathered}
v=D(c,x)-c\circ y,\qquad w=c\circ x+D(c,y),\\
D(x+v,y+w)-D(x-v,y-w)=-2x\circ v-2y\circ w.
\end{gathered}
\tag{28.2}
$$

每个实际内值、外值、零、重复、有限实幅度、缩放、平移、背景以及它们再形成的全部嵌套调用均在原量词内。不增加未知 $D$ 的可加性、齐次性、连续性、可测性、协变性、单位平移中性、压缩自然性、商下降、双对偶延拓或有限输出子代数闭合。

固定实际投影 $P\in A$，记 $C=PAP$。附加数学前件严格是同一 $D$ 在**整个实际完成角**上的分类

$$
D(x,y)=K_\sigma(x,y),\qquad
K_\sigma(x,y)=\frac{\jmath}{2}[x,y],\qquad
\jmath=\sigma i,\quad\sigma\in\{1,-1\},
\quad x,y\in C_{\rm sa}.
\tag{28.3}
$$

$K_\sigma$ 作为比较映射在全部 $E^2$ 上有定义；(28.3) 只识别角内旧值。W119.2–119.3、W 式 (120.2) 的实际角支撑及完整继承按定义 6.2 直接复用：单位是 $P$，锥和范数准确继承，每个原评价标签限制到角内，质量为 $\gamma(P)$，同值限制不合并、零限制不删除、质量不归一；全部角内实际 PB 的继承不要求输出留在有限矩阵阶段。

取原演员 $c=c^*\in C$，以及实际正交投影 $l,m\le P$、实际 $e=e^*\in C$，满足

$$
\begin{gathered}
cl=lc=al,\qquad cm=mc=bm,\qquad a,b\in\mathbb R,\quad a\ne b,\\
e=(l+m)e(l+m),\qquad e^2=l+m,\qquad el=me.
\end{gathered}
\tag{28.4}
$$

(28.4) 的通道条件正是 $l,m$ 在 $C$ 内的实际投影等价：若实际 $w^*w=m$、$ww^*=l$，则 $w=lwm$、$w^2=0$，取 $e=w+w^*$ 即得该条件；反向取 $w=lem$，由 $e^2=l+m$、$el=me$ 得 $w^*w=m$、$ww^*=l$。

非平凡情形 $l,m$ 均非零；若其中一个为零，实际等价关系迫使另一个也为零，以下行等式平凡。$c$ 在 $P-l-m$ 上任意。置

$$
\mu=\frac{a+b}{2},\qquad \lambda=\frac{a-b}{2}\ne0,
\qquad j=\jmath(l-m)e,\qquad n=2l.
\tag{28.5}
$$

已知乘法逐项给出

$$
\begin{gathered}
j=j^*,\quad j^2=e^2=l+m,\quad e\circ j=0,\quad n\circ j=j,\\
c\circ e=\mu e,\quad c\circ j=\mu j,\quad c\circ n=an.
\end{gathered}
\tag{28.6}
$$

对每个有限实 $T,\alpha$，整个角分类逐值支付

$$
D(c,Te+\alpha n)=\lambda Tj,\qquad
c\circ(Te+\alpha n)=\mu Te+a\alpha n.
\tag{28.7}
$$

$a,b$ 可同号或异号，也允许恰有一个为零。这里没有把演员改为 $c-\mu P$，也没有对一般环境行抽取系数或拆分输入。

**定理 28.2（相异谱值锁定一个谱格的完整非对角行）。** 在定义 28.1 下，对每个任意实际环境输入 $t=t^*\in A$，有

$$
\boxed{\quad l\bigl(D(c,t)-K_\sigma(c,t)\bigr)(1-l)=0.\quad}
\tag{28.8}
$$

$1-l$ 包含 $m$、同一角的全部其余部分和整个 $1-P$；两份原输入始终是完整的 $c,t$。

证明。复用 AH43.1 的反对称性、零槽及数学正读取。对每个未归一的数学正实线性泛函 $\phi$，记

$$
B_\phi(X,Y)=\phi(X^2)\phi(Y^2)-\phi(X\circ Y)^2,
\qquad |\phi D(X,Y)|\le\sqrt{B_\phi(X,Y)}.
\tag{28.9}
$$

该读取来自同一原二表：对固定复系数 $z_1,z_2$，其二次型是原自伴元素

$$
|z_1|^2X^2+|z_2|^2Y^2
+2\operatorname{Re}(\overline z_1z_2)X\circ Y
+2\operatorname{Im}(\overline z_1z_2)D(X,Y).
$$

原评价全部读为非负，准确锥使该元素为正，故可由任意 $\phi\ge0$ 读取同一二表。Hermitian 性与分离性给反对称性，零对角及分离性给零槽，行列式给 (28.9)。这些数学读取不增添实际准备，也不改变任何原质量。

固定 $c,t$ 及其同一个输出，置

$$
g=D(c,t),\qquad k=c\circ t,\qquad
V=a\,n\circ t-n\circ k,\qquad Z=t+ak.
\tag{28.10}
$$

对每个有限实 $T,\alpha$，真正调用 $\operatorname{PB}(c;Te+\alpha n,t)$。(28.7) 给实际内构造 $v=\lambda Tj-k$、$w=\mu Te+a\alpha n+g$；因此全部实际外层标签为

$$
\begin{aligned}
R_+&=T(e+\lambda j)-k+\alpha n,&
S_+&=t+g+\mu Te+a\alpha n,\\
R_-&=T(e-\lambda j)+k+\alpha n,&
S_-&=t-g-\mu Te-a\alpha n.
\end{aligned}
\tag{28.11}
$$

保留 $\alpha$ 依赖的完整 PB 右端，直接展开得

$$
\begin{aligned}
D(R_+,S_+)-D(R_-,S_-)
&=-2(Te+\alpha n)\circ(\lambda Tj-k)
  -2t\circ(\mu Te+a\alpha n+g)\\
&=2T e\circ k-2\mu Tt\circ e-2t\circ g
  -2\alpha(\lambda Tj+V).
\end{aligned}
\tag{28.12}
$$

$T^2$ 项因 $e\circ j=0$ 为零，$\alpha T$ 项使用 $n\circ j=j$。对两份未知实际外值分别应用同一个 $\phi$ 的 (28.9)，先得到

$$
\left|\phi\bigl(2T e\circ k-2\mu Tt\circ e-2t\circ g
 -2\alpha(\lambda Tj+V)\bigr)\right|
\le\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}.
\tag{28.13}
$$

以下只消元已知的标量 Gram。令 $\langle X,Y\rangle_\phi=\phi(X\circ Y)$；对固定自伴 $A_0,B_0,n$ 和实 $\theta$，置 $C_0=B_0-\theta A_0$，则

$$
\begin{aligned}
B_\phi(A_0+\alpha n,B_0+\theta\alpha n)
&=B_\phi(A_0+\alpha n,C_0)\\
&=\alpha^2B_\phi(n,C_0)+B_\phi(A_0,C_0)\\
&\quad+2\alpha\bigl\{
\langle A_0,n\rangle_\phi\langle C_0,C_0\rangle_\phi
-\langle A_0,C_0\rangle_\phi\langle n,C_0\rangle_\phi\bigr\}.
\end{aligned}
\tag{28.14}
$$

这是半内积 Gram 行列式的列消元及二次展开，退化时同样成立。正号对取
$A_0=T(e+\lambda j)-k$、$B_0=t+g+\mu Te$、$\theta=a$；负号对取
$A_0=T(e-\lambda j)+k$、$B_0=t-g-\mu Te$、$\theta=-a$。由 $a-\mu=\lambda$，得到准确的

$$
C_+=Z+g-\lambda Te-a\lambda Tj,
\qquad C_-=Z-g+\lambda Te-a\lambda Tj.
\tag{28.15}
$$

这一步消去的是标量预算中的共同中点，演员没有改变。对固定 $T,\phi$，将 (28.13) 除以 $|\alpha|$，只在 (28.14) 的标量多项式中令 $|\alpha|\to\infty$，得

$$
2|\phi(\lambda Tj+V)|
\le\sqrt{B_\phi(n,C_+)}+\sqrt{B_\phi(n,C_-)}.
\tag{28.16}
$$

每个 Gram 多项式非负；除以 $\alpha^2$ 后趋向其二次系数，非负平方根连续，所以首项为零时对应根号也趋零。没有除以 $a$、$b$、质量或首项 Gram。

在一份忠实含单位表示 $A\subseteq B(\mathcal H)$ 内计算，内积第一槽共轭线性。由 $cl=lc=al$ 和 $n=2l$，

$$
\begin{gathered}
V=V^*,\qquad lVl=0,\qquad(1-l)V(1-l)=0,\\
lV(1-l)=a\,lt(1-l)-lk(1-l)
=\tfrac12l[c,t](1-l).
\end{gathered}
\tag{28.17}
$$

因此 $V$ 相对 $l\oplus(1-l)$ 完全非对角，未对余块上的 $c$ 施加条件。

取单位 $\xi\in(1-l)\mathcal H$。先设 $d=\|m\xi\|>0$，令

$$
\eta=j\xi/d\in l\mathcal H,\quad\|\eta\|=1,
\qquad j\xi=d\eta,\qquad e\xi=-\jmath d\eta.
\tag{28.18}
$$

对 $\delta>0$，用向量 $\xi_\delta=(\xi+\delta\eta)/\sqrt{1+\delta^2}$ 作数学读取 $\phi_\delta$。在底层实 Hilbert 空间令
$\Pi_\eta z=z-\operatorname{Re}\langle\eta,z\rangle\eta$。每个固定自伴 $W$ 满足

$$
\begin{aligned}
\phi_\delta(n^2)&=\frac{4\delta^2}{1+\delta^2},&
\phi_\delta(W^2)&=\frac{\|W\xi+\delta W\eta\|^2}{1+\delta^2},\\
\phi_\delta(n\circ W)&=
\frac{2\delta\operatorname{Re}\langle\eta,W\xi+\delta W\eta\rangle}{1+\delta^2},&
B_{\phi_\delta}(n,W)&=
\frac{4\delta^2}{(1+\delta^2)^2}
\|\Pi_\eta(W\xi+\delta W\eta)\|^2.
\end{aligned}
\tag{28.19}
$$

$j,V$ 的非对角性又给

$$
\phi_\delta(\lambda Tj+V)=\frac{2\delta}{1+\delta^2}
\bigl(\lambda Td+\operatorname{Re}\langle\eta,V\xi\rangle\bigr).
\tag{28.20}
$$

代入 (28.16)，约去正因子 $2\delta/(1+\delta^2)$，在固定 $T$ 后令 $\delta\downarrow0$。因为 $\Pi_\eta(j\xi)=0$，两份 $-a\lambda Tj$ 项在此时消失。记

$$
A_\xi=\operatorname{Re}\langle\eta,V\xi\rangle,\qquad
z_\pm=\Pi_\eta((Z\pm g)\xi),\qquad
\nu=e\xi/d=-\jmath\eta.
$$

于是 $\|\nu\|=1$、$\operatorname{Re}\langle\eta,\nu\rangle=0$，并且

$$
2|\lambda Td+A_\xi|
\le\|z_+-\lambda Td\,\nu\|+\|z_-+\lambda Td\,\nu\|.
\tag{28.21}
$$

对固定单位向量 $\nu$、固定 $z$ 及非零实 $\rho$，平方差有理化给

$$
\|\rho L\nu+z\|-|\rho|L
=\frac{2\rho L\operatorname{Re}\langle\nu,z\rangle+\|z\|^2}
{\|\rho L\nu+z\|+|\rho|L}
\longrightarrow\operatorname{sgn}(\rho)\operatorname{Re}\langle\nu,z\rangle
\quad(L\to+\infty).
\tag{28.22}
$$

令 $\epsilon=\operatorname{sgn}\lambda$、$B_\xi=\operatorname{Re}\langle\nu,g\xi\rangle$。在 (28.21) 取 $T=L$，左右各减去 $2|\lambda|dL$，两边极限分别为

$$
2\epsilon A_\xi,\qquad
-\epsilon\operatorname{Re}\langle\nu,z_+\rangle
+\epsilon\operatorname{Re}\langle\nu,z_-\rangle=-2\epsilon B_\xi.
$$

在 $T=-L$ 时，两边极限分别为 $-2\epsilon A_\xi$、$2\epsilon B_\xi$。实投影 $\Pi_\eta$ 不改变与 $\nu$ 的实配对，共同的 $Z$ 因此消去。两向不等式一起迫使 $A_\xi=-B_\xi$。由 $\nu=-\jmath\eta$，准确得到

$$
\operatorname{Im}\langle\eta,g\xi\rangle
=\sigma\operatorname{Re}\langle\eta,V\xi\rangle.
\tag{28.23}
$$

$\epsilon$ 的保留同时覆盖负 $\lambda$。

再使用另一份实际伴轴 $e'=j$、$j'=\jmath(l-m)j=-e$。整个角分类给
$D(c,e')=\lambda j'$、$c\circ e'=\mu e'$，所以刚才的全部实际 PB 推导适用。$c,t,g,k,V,Z,n,d$ 不变，$\eta'=j'\xi/d=\jmath\eta$。设
$G=\langle\eta,g\xi\rangle$、$L_0=\langle\eta,V\xi\rangle$。第二伴轴的 (28.23) 是

$$
\operatorname{Im}(-\jmath G)=\sigma\operatorname{Re}(-\jmath L_0),
\qquad -\sigma\operatorname{Re}G=\operatorname{Im}L_0.
$$

它与第一伴轴的 $\operatorname{Im}G=\sigma\operatorname{Re}L_0$ 合为 $G=\jmath L_0$，故

$$
\langle jm\xi,(g-\jmath V)\xi\rangle=0
\qquad(\xi\in(1-l)\mathcal H).
\tag{28.24}
$$

固定算子的二次齐次性把单位向量结论扩到全部 $d>0$ 的向量；$d=0$ 时左边本来为零，不定义 $\eta$、不除以 $d$。

令 $M=g-\jmath V$、$r_0=1-l-m$。在 (28.24) 取 $\xi=u+z$，其中 $u\in m\mathcal H$、$z\in r_0\mathcal H$，减去 $z=0$ 的等式，得 $\langle ju,Mz\rangle=0$。$j:m\mathcal H\to l\mathcal H$ 是满等距，故 $lMr_0=0$。在 $z=0$ 时，$T_0=mjMm$ 的二次型 $Q(u)=\langle u,T_0u\rangle$ 恒零。不要求 $T_0$ 自伴，复极化给

$$
4\langle u,T_0v\rangle
=Q(u+v)-Q(u-v)-iQ(u+iv)+iQ(u-iv)=0.
\tag{28.25}
$$

因此 $T_0=0$，同一满等距性给 $lMm=0$。合并得到 $l(g-\jmath V)(1-l)=0$，再由 (28.17) 得到 (28.8)，忠实性将等式返回 $A$。

所有极限只作用于显式标量 Gram 多项式或固定元素 $g,k,V,Z$ 的向量范数。没有对变化输入上的任何未知 $D$ 取极限。$a=0$、$b=0$、两种 $\sigma$、负 $\lambda$、首项 Gram 为零及 $d=0$ 均已包含。∎

## 29. 有限实际谱分割与完整核压缩

**定理 29.1（有限匹配供应下的支撑与交换余量）。** 保持定义 28.1 的完整原条件及整个 $C=PAP$ 的分类。设角内原演员具有有限非标量谱

$$
c=\sum_{i=1}^r a_i p_i,\qquad r\ge2,\qquad
\sum_{i=1}^r p_i=P,
\tag{29.1}
$$

其中 $a_i\in\mathbb R$ 两两不同，$p_i\ne0$ 为两两正交的实际谱投影。零谱值若存在，是单位 $P$ 下的一个内部谱格。假定每个 $a_i\ne0$ 的谱格有如下实际有限匹配：存在 $j(i)\ne i$、有限正交分割 $p_i=\sum_{\alpha=1}^{N_i}l_{i\alpha}$，以及 $m_{i\alpha}\le p_{j(i)}$、$w_{i\alpha}\in C$，使

$$
w_{i\alpha}^*w_{i\alpha}=m_{i\alpha},\qquad
w_{i\alpha}w_{i\alpha}^*=l_{i\alpha}.
\tag{29.2}
$$

比较投影 $m_{i\alpha}$ 不必彼此正交，可以反复使用同一小投影。这里 $p_{j(i)}\ne0$ 指实际投影非零，不要求其谱值 $a_{j(i)}$ 非零。

记实际非零谱支撑 $S=\sum_{a_i\ne0}p_i$。则对每个任意环境 $t=t^*\in A$，同一个输出满足

$$
\boxed{D(c,t)=K_\sigma(c,t)+s,\qquad
s=s^*\in SAS\subseteq C,\qquad[c,s]=0.}
\tag{29.3}
$$

不要求谱对称、反对易反射或 $c$ 在 $C$ 中可逆。

证明。有限谱投影确在原代数中，由角内 Lagrange 演算给

$$
p_i=\prod_{j\ne i}\frac{c-a_jP}{a_i-a_j}\in C.
\tag{29.4}
$$

固定 $M=D(c,t)-K_\sigma(c,t)=M^*$。对 (29.2) 的一对 $l,m,w$，有 $w=lwm$，且 $lm=0$，故 $w^2=(w^*)^2=0$。实际 $e=w+w^*$ 满足 $e^2=l+m$、$el=me$；不变的演员 $c$ 在两格取值 $a_i\ne a_{j(i)}$。定理 28.2 给 $lM(1-l)=0$。因为 $1-p_i\le1-l_{i\alpha}$，有限求和只分解这一个固定输出，得到

$$
p_iM(1-p_i)=\sum_\alpha l_{i\alpha}M(1-p_i)=0
\qquad(a_i\ne0).
\tag{29.5}
$$

自伴性给反向块也为零。因此全部非零谱格之间、这些格与其余部分之间的余量块均为零。

令 $q=1-S$。在忠实表示中，$q\mathcal H=\ker c$：正交有限谱分解使 $c\xi=0$ 当且仅当每个 $a_i\ne0$ 的 $p_i\xi=0$。$q$ 包含整个 $1-P$ 和内部零谱格；若无内部零格，后者取零。对每个 $\xi\in q\mathcal H$，原 $(c,t)$ 的 (28.9) 第一平方为零，故 $\langle\xi,D(c,t)\xi\rangle=0$。对这个固定自伴输出在整个 $q\mathcal H$ 上极化，得到

$$
qD(c,t)q=0,\qquad qK_\sigma(c,t)q=0,\qquad qMq=0.
\tag{29.6}
$$

这是**整个核压缩**，同时消去内部零格与角外之间的交叉压缩，不能只分别检查两个对角块。结合 (29.5) 及其伴随，有

$$
M=\sum_{a_i\ne0}p_iMp_i=:s\in(SAS)_{\rm sa},\qquad[c,s]=0.
\tag{29.7}
$$

它是固定原输出的有限分块，不是对未知行输入的可加展开。∎

(29.6) 不断言 $D(c,t)q=0$；标准交换子本身可以有接向核的非零行。被限制到 $S$ 上的是余量 $s$。若 $c=0$，原零槽给整行零。若 $c=aP\ne0$ 在单位 $P$ 下只有一个谱值，(29.1) 不成立，本节不作其任意环境整行结论；不能将 $1-P$ 添作分类角 $C$ 内的第二个零谱投影。

## 30. 内在 UHF 模型的实际单侧匹配与逐谱格标量余量

**定理 30.1（有限非标量谱的逐格标量余量）。** 保持定义 28.1 的完整原条件及整个实际 $C=PAP\ne0$ 的同号分类。另设这个角自身具有实际递增含单位满矩阵 UHF 模型

$$
C=\overline{\bigcup_n C_n}^{\|\cdot\|},\qquad
C_n\cong M_{d_n}(\mathbb C),\qquad 1_{C_n}=P,
\qquad d_n\longrightarrow\infty.
\tag{30.1}
$$

不要求阶段大小为偶，也不要求 $C$ 是环境 $A$ 的预定有限阶段角。对 (29.1) 的每个有限非标量谱原演员 $c\in C_{\rm sa}$ 和每个任意环境 $t=t^*\in A$，存在唯一的一组实数 $\rho_i=\rho_i(c,t)$，使

$$
\boxed{D(c,t)=K_\sigma(c,t)+\sum_{a_i\ne0}\rho_i p_i.}
\tag{30.2}
$$

特别，余量支撑在 $S=\operatorname{supp}(c)$、与 $c$ 交换，并在每个非零谱格上为实标量。$c$ 无须可逆或具有反对易反射，完整谱格的数学迹无须相等。

证明。先在这个**实际内在载体 $C$、单位 $P$** 中消费 AH67.2 式 (67.3) 的近投影酉构造及有限矩阵秩工具；成熟归属为 Blackadar，*Operator Algebras*，II.2.3.1–5、II.3.3.4–5、II.8.2.2(iv)。为明确每次使用都产生实际匹配，给出其参数。

对任意实际投影 $r\in C$，取某个 $C_n$ 中自伴 $h_r$，使 $\|h_r-r\|<\varepsilon<1/4$。其谱包含于
$[-\varepsilon,\varepsilon]\cup[1-\varepsilon,1+\varepsilon]$，所以有限矩阵函数演算给

$$
r_0=1_{(1/2,\infty)}(h_r)\in C_n,\qquad
\|r_0-h_r\|\le\varepsilon,\qquad\|r_0-r\|<2\varepsilon<1.
$$

在 $C$ 内置

$$
x_r=r_0r+(P-r_0)(P-r),\qquad
\nu_r=x_r(x_r^*x_r)^{-1/2}.
\tag{30.3}
$$

准确有 $x_r^*x_r=x_rx_r^*=P-(r-r_0)^2$，故 $x_r$ 可逆，$\nu_r$ 是单位为 $P$ 的实际酉。由 $x_rr=r_0x_r$ 及 $x_r^*x_r$ 与 $r$ 交换，得

$$
\nu_r r\nu_r^*=r_0.
\tag{30.4}
$$

这只是 AH 式 (67.3) 在 $C$ 中的成熟构造，不对未知 $D$ 使用酉协变。

现在取任意两个非零实际投影 $r,v\in C$。分别作 (30.3)–(30.4)，得 $\nu_r,\nu_v$ 及有限阶段的 $r_0,v_0$；把后两者放进一个共同后续 $C_N\cong M_{d_N}$。将 $r_0$ 分成秩一投影 $L_1,\ldots,L_k$，只从 $v_0$ 取**一个**秩一投影 $M_0\le v_0$。有限矩阵正交基给每个 $\alpha$ 的实际部分等距 $V_\alpha\in C_N$，满足

$$
V_\alpha^*V_\alpha=M_0,\qquad
V_\alpha V_\alpha^*=L_\alpha.
$$

定义

$$
l_\alpha=\nu_r^*L_\alpha\nu_r,\qquad
m=\nu_v^*M_0\nu_v,\qquad
w_\alpha=\nu_r^*V_\alpha\nu_v.
\tag{30.5}
$$

于是全部元素实际属于 $C$，并且

$$
r=\sum_{\alpha=1}^k l_\alpha,\qquad
l_\alpha l_\beta=0\ (\alpha\ne\beta),\qquad
0\ne m\le v,\qquad
w_\alpha^*w_\alpha=m,\quad
w_\alpha w_\alpha^*=l_\alpha.
\tag{30.6}
$$

这是单侧完全分割：每次都可使用同一个 $m$。若使用 AH67.1 的相容归一数学迹 $\tau_C$，每块的迹为 $1/d_N$；$r$、$v$ 的整迹分别由它们在 $C_N$ 中的秩决定，可以不同。这里没有把 $v$ 分成与 $r$ 同样数量的完全匹配，也不假设不等整迹的投影等价。两个酉各自把一个投影放进有限阶段，不要求同时共轭全部原谱投影。

对 (29.1) 的每个 $i$，任选一个 $j\ne i$。由于 $p_j\ne0$，将 (30.6) 用于 $r=p_i,v=p_j$ 就实际支付 (29.2)，并允许 $a_j=0$。定理 29.1 因而给同一个固定余量

$$
s=D(c,t)-K_\sigma(c,t)=s^*\in SAS,\qquad[c,s]=0.
\tag{30.7}
$$

还须约束每个内部块，而不只求得交换性。固定 $a_i\ne0$，取任意实际非零投影 $r\le p_i$。对 $r$ 和同一个非零 $p_j$ 再作 (30.6)，把 $r$ 分成 $l_\alpha$，各块与反复使用的 $m\le p_j$ 实际等价。它们在**同一个原演员 $c$** 上仍有谱值 $a_i\ne a_j$；$e_\alpha=w_\alpha+w_\alpha^*$ 满足定理 28.2 的所有条件。于是逐块有 $l_\alpha s(1-l_\alpha)=0$，有限求和给

$$
rs(1-r)=0,\qquad(1-r)sr=0,\qquad[r,s]=0.
\tag{30.8}
$$

零投影的等式也成立。因此 $s_i=p_i s p_i$ 与 $p_iCp_i$ 中的**每个实际投影**交换；这里只改变已知的探针标签，始终读取原来的同一个 $D(c,t)$。

为使用角中心，令 (30.4) 对 $p_i$ 的实际酉为 $\nu_i$，并取 $p_i^0=\nu_i p_i\nu_i^*\in C_{n_i}$。对 $N\ge n_i$，已知代数中存在实际满矩阵模型

$$
B_N^i=\nu_i^*p_i^0C_Np_i^0\nu_i\subseteq p_iCp_i,
\quad 1_{B_N^i}=p_i,
\quad B_N^i\cong M_{k_i d_N/d_{n_i}}(\mathbb C),
\quad k_i=\operatorname{rank}_{C_{n_i}}(p_i^0)\ge1.
\tag{30.9}
$$

这些代数递增，其并在整个 $p_iCp_i$ 中范数稠密：先在 $C_N$ 内逼近已知的 $\nu_i y\nu_i^*$，再用 $p_i^0$ 压缩，最后共轭回去。有限矩阵谱分解给其每个自伴元素为有限实投影和。由 (30.8)，$s_i$ 与这些自伴元素全都交换。对于任意 $y=y^*\in p_iCp_i$，取上述 $y_N\to y$；只使用固定算子的乘法极限

$$
\|[s_i,y]\|\le 2\|s_i\|\|y-y_N\|\longrightarrow0.
\tag{30.10}
$$

故 $s_i\in Z(p_iCp_i)$。

现在直接消费 AH67.1 的成熟满矩阵极限标量中心结论，应用载体是 (30.9) 的整个 $p_iCp_i$、单位是 $p_i$；该结论不使用矩阵阶数的偶性。令 $\tau_i$ 为这个角的相容归一数学迹，则

$$
Z(p_iCp_i)=\mathbb C p_i,\qquad
s_i=\rho_i p_i,\qquad \rho_i=\tau_i(s_i)\in\mathbb R.
\tag{30.11}
$$

实系数来自 $s_i=s_i^*$。这些辅助数学迹的归一化不改变任何原评价质量。内部零格已由 (29.6) 消去，故 (30.7) 给 (30.2)；各 $p_i\ne0$ 又给系数唯一性。以上未使用输入极限通过 $D$、反对易反射或 $c$ 在单位 $P$ 下的逆。∎

## 31. 精确外层缺陷与实际角返回的整行

**命题 31.1（同一原 PB 的未付等式）。** 在定理 29.1 的条件下，固定任意 $t=t^*$，记 $g=D(c,t)$、$k=c\circ t$、$s=g-K_\sigma(c,t)$。定义两份真正外层缺陷

$$
E_+=D(c-g,k)-K_\sigma(c-g,k),\qquad
E_-=D(c+g,-k)-K_\sigma(c+g,-k).
\tag{31.1}
$$

则有精确恒等式

$$
\boxed{E_+-E_-=2cs.}
\tag{31.2}
$$

对这份原输入，$D(c,t)=K_\sigma(c,t)$、$s=0$ 与 $E_+=E_-$ 三者等价。在定理 30.1 的范围内，进一步有

$$
E_+-E_-=2\sum_{a_i\ne0}a_i\rho_i p_i,
\qquad
\|E_+-E_-\|=2\max_{a_i\ne0}|a_i\rho_i|.
\tag{31.3}
$$

证明。真正的 $\operatorname{PB}(t;c,0)$ 使用内值 $D(t,c)=-g$、$D(t,0)=0$，所以

$$
D(c-g,k)-D(c+g,-k)=2c\circ g.
\tag{31.4}
$$

只对已知比较映射使用双线性，逐项相消给

$$
\begin{aligned}
K_\sigma(c-g,k)-K_\sigma(c+g,-k)
&=2K_\sigma(c,k)\\
&=\frac{\jmath}{2}[c^2,t]
=2c\circ K_\sigma(c,t).
\end{aligned}
\tag{31.5}
$$

相减并用 $[c,s]=0$ 得 $2c\circ s=2cs$。若 $cs=0$，左、右乘各非零谱投影给 $a_i p_i s p_i=0$；逐个非零实数 $a_i$ 消去后，(29.7) 给 $s=0$。这不要求 $c$ 在整个 $C$ 中可逆。反向直接成立。定理 30.1 将其化为正交有限谱和，范数即 (31.3)。∎

**定理 31.2（实际返回条件下的整行与任意补角背景）。** 在定理 29.1 的条件下，若这份实际输入满足

$$
(1-P)tS=0,\qquad S=\operatorname{supp}(c),
\tag{31.6}
$$

则

$$
\boxed{D(c,t)=K_\sigma(c,t).}
\tag{31.7}
$$

特别包括 $[P,t]=0$ 且补角背景 $(1-P)t(1-P)$ 任意的情形；不要求该背景有限谱或有限阶段。(31.6) 也允许内部零谱格与角外之间的任意自伴背景，因为它只限制非零谱支撑向角外的连线。

证明。由 $c=ScS$，(31.6) 给 $(1-P)tc=0$，其伴随给 $ct(1-P)=0$。同时 $(1-P)ct=0=tc(1-P)$ 本来成立。因此 $ct,tc\in C$，从而 $k,K_\sigma(c,t)\in C_{\rm sa}$；定理 29.1 的 $s\in C$ 又给 $g\in C$。两份实际外层对 $(c-g,k)$、$(c+g,-k)$ 此时全在 $C_{\rm sa}^2$，故整个角分类逐份给 $E_+=E_-=0$。命题 31.1 遂给 $s=0$。没有将 $t$ 的任何背景从未知响应中拆出。∎

**边界 31.3（右支撑不能代付角返回）。** 对定理 29.1 的一般环境输入，仍有准确复标签

$$
\begin{aligned}
W_+&=(c-g)+\jmath k=c-s+\jmath tc,&W_+S&=W_+,\\
W_-&=(c+g)-\jmath k=c+s-\jmath tc,&W_-S&=W_-,\\
(1-P)W_+&=\jmath(1-P)tc,&
(1-P)W_-&=-\jmath(1-P)tc.
\end{aligned}
\tag{31.8}
$$

这些等式直接代入 $g=\jmath(ct-tc)/2+s$ 即得。若 $(1-P)tS\ne0$，必有某个 $a_i\ne0$ 使 $(1-P)tp_i\ne0$，而
$(1-P)tc p_i=a_i(1-P)tp_i\ne0$。于是两份 $W_\pm$ 都不在 $C$ 中；它们的自伴实虚标签不能全部送入 (28.3)。因此右理想关系 $W_\pm S=W_\pm$ 不消去两份实际缺陷。对一般 $t$，首个仍未支付的原关系准确是 (31.1) 的 $E_+=E_-$，在定理 30.1 中等价于每个 $\rho_i=0$。这里没有把这条等式增加为公理，也没有给出满足全部 $\mathsf H_A(D)$ 的反模型。

## 32. 谱差几何、量子对应及同一完整来源

**归属 32.1（被消费的工具与结论范围）。** 本增补的数学差额归为 $\texttt{repo-derived}$：在同一完整原 PB 中保留 $\mu$、$\lambda$ 和全部外标签，利用相异谱值而非相反谱值支付 (28.8)；在实际内在 UHF 载体中，以单侧分割和可重复小块匹配约束同一个输出，再以任意子投影及成熟角中心缩为 (30.2)。这是证明与条件几何的简化，不是原 A1–A3/P2/PB 独立条数减少，不主张文献优先权、穷尽检索或外部开放问题解决。

AH 的直接身份严格为 `b1a95e41b9622e9f720e51f9bb899841f5b74ca1`，W、CC 的直接身份严格为 `3b10aed60f60e4901bae6cf2e160bf439d642e64`，各被引正文的递归版本保持自身身份。AH43.1 供应原二表的数学正读取、反对称性及零槽；AH67.1、67.2 式 (67.3) 供应已知代数中的偏迹、角中心及近投影酉构造。W119.2–119.3 与 W 式 (120.2) 供应整个实际角的准确接口与全部实际 PB 继承。CC147–150 的双伴轴与两向一次范数预算具有实际全单位框架前件；定理 28.2 在局部谱格和任意余块上逐项支付实际标签，不将该前件直接删去。定理 23.2 的相反谱对是本探针 $\mu=0$ 的已成范围；24.1 的有限对称谱余量仍直接复用，不另计新分类。

成熟有限谱函数演算、部分等距、投影等价和近投影酉共轭归于 Blackadar，[*Operator Algebras*](https://bruceblackadar.com/Mathematics/Cycr.pdf)，II.2.3.1–5、II.3.3.4–5；变重数 UHF 满矩阵模型取 II.8.2.2(iv)。其中近投影共轭的地址是 II.3.3.5。(30.3)–(30.6) 明确给出其在本题的实际参数，不以一般迹比较代替有限矩阵秩匹配。忠实表示、正泛函及数学 GNS 沿定义 10.1 的 Gelfand–Naimark、Segal，Peirce 角术语沿该处 Hanche-Olsen–Størmer §2.6.2、Lemma 2.6.3；Gram 列消元、固定向量范数一次项及复极化只在上述证明中作为成熟工具消费。

若**整个环境**已有 AH70.1 的偶维满矩阵模型，直接复用其更强全域分类，任意环境行已全部识别。有限维环境及 AH42.4 已覆盖的本质连续迹情形也直接复用既有更强结果；这些不是新分类案例。若只有 $C$ 的内在模型有偶数阶段，W 的完整角继承及 AH70.1 直接供应的只是整个 $C$ 的分类；环境任意输入的余量仍按上述定理处理。实际有限阶段偶角及其共同符号由 AH71.2、72.1 原样供应，不重证分类或符号拼接。

一般 $A=M_3(B)$、任意 $B$ 不自动供应 (30.1)；完整奇数单位 UHF 也不因具有矩阵模型便获得 (28.3)。$c$ 在已分类角内部可以带任意有限谱背景，始终保留整个演员；这不将第二输入的任意背景搬进一个已分类角，不使用单位平移中性或输入可加性。有限谱逼近也不能穿过未知 $D$ 推出无限谱演员结论。

[C133W §§42–43](https://github.com/the-omega-institute/trureturing/blob/13d69713c20f58174d6bbfd07a12be95802faed7/docs/develop/theory/AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md) 中的原始有序关系 $(R)$ 及第三标记返回 $(C3)$ 属于另一套对象和量词。其 $(R)+(C3)$ 下的 $(C1)$、UC 与仿射复 Hilbert 结论，既不取消 $(C3)$ 前件，也不提供该 $(R)$ 与本节原 PB 的对应映射。将它用于这里仍须证明保留对象、原标签、操作、全部量词和结论方向的桥梁；本节结论不以该未给出的桥梁承重。

**对应 32.2（已证明行上的普通量子代数）。** 对定理 29.1 的同一实际输入，准确有

$$
S(c,t)-iD(c,t)
=\begin{cases}ct,&\sigma=1,\\tc,&\sigma=-1\end{cases}-is.
\tag{32.1}
$$

因此已经识别的非对角块等于通常乘法或相反乘法的相应块；定理 30.1 的整行还保留 $-i\sum_{a_i\ne0}\rho_i p_i$。只有余量为零时，例如满足 (31.6) 的定理 31.2，才有完整行

$$
S(c,t)-iD(c,t)=
\begin{cases}ct,&\sigma=1,\\tc,&\sigma=-1.\end{cases}
\tag{32.2}
$$

在已经整体分类的 $C$ 上，AH64.1、75.1 的既有消费者给 $S-iD$ 的复线性延拓为通常或相反 $C^*$-乘法，保持伴随、准确锥、单位 $P$ 和原范数；全部有限角内旧复 Gram 正，每个原限制评价有数学 GNS，循环向量平方范数准确为 $\gamma(P)$，零质量给零向量。数学正泛函、角及 Hilbert 表示不成为实际准备。局部行和共同符号没有给整个未知环境增加全域双线性、结合乘法或全部有限旧复 Gram。

Alfsen–Shultz，[*Orientation in operator algebras*](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/)，PNAS **95**，6596–6601，DOI `10.1073/pnas.95.12.6596`，Dynamical Correspondences、Theorem 1，提供 Jordan 相容乘法与取向的成熟对应。该 dynamical correspondence 的前件是到 skew order derivations 的**线性**映射；(30.2) 的部分行不代付这个全域前件，也不供应物理时间。

**定义 32.3（与 §27.1 完全相同的递归全文来源谓词）。** 本节的完整物理来源谓词**就是 §27.1 的同一个** $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$。沿其身份关系，整个定义 26.3、22.3、18.2 及其严格引用的 10.2、15.2、AH28.1、64.2、75.1、固定 SQ47.1–47.13 和每一项逐层固定版本的递归上游全文，逐句、逐公式、逐量词同时纳入。这里没有另造缩短谓词，也不以以下范围说明替代任何被纳入全文。

SQ 主源按其自身 1.3、39、41.1、47.1 解析，`dcaebc0b9ca5a3a463fd8cfd161d38967df28668` 与 `0aa11dbc3dc337d667b98900673e07d67b99bf46` 保持其相应层级；OP/PT/PB/SM/C/AQ/R3/W/FR/XV/SF 的 `f24d1138a7b994da16abd9a47affedea64ea44ce`、AH22.1 保留的 `2addd6f369b7387226c2b0cc984623dd3efe40a1`、AH12.1 上游 `39a0505470ea889dd9d4301ad60cd9506a5e8b58` 和 AH42.1 中 OP 等直接身份 `bef9bba367a24ab5e250491dcb88ed85ebc29cf7` 全部保持。原根、静默和其他静态分支不改为 UHF，各内层来源不被直接 AH/W/CC 身份压平。

实际准备、相干控制、原事件绑定的实际完整 Born 菜单、全部原质量及角菜单的真实条件化仍须其完整来源；只在严格正的相应实际质量上归一，零、不等、次归一和非正常质量均保留。数学谱格、正泛函和 GNS 不产生这些来源。真正相关联合与张量仍须同一实际共同来源、全部相关输入、忠实同向交换腿、共同生成、分离与所需重数；数学等价投影、相同边缘或分别可达不代付共同实现。

typed CP、箭头下降、整台递归同源参考、原真支持和支持内补、交织夹界、全部所需有限深度及每个正精度，保留各自全部原前件。完整仪器、TP、Kraus、更新、Lüders 仍须完整 typed 菜单、完整单位分区、接受端、校准、表示和收敛条件，量化**整个环境、全部成功／失败／细记录／port／post-port 输出，以及每份完整输出的每个仍合法未来**。只有严格正的实际输出质量可归一，任何失败或零分支不删除。

合法顺序、自适应与并行历史、真正分组遗忘、停止、拒绝、销毁、泄漏、同数两侧及逆向真实 Return、完整 CountRead 的活动 ready 与 producer 均保留原全文合同。相同算子不合并原程序、记录、读取次序、原零集或未来权限，未定义请求不补零。正常性、指定前对偶、无限菜单和记录的可数可加及收敛仍须原扩展来源。物理动力学仍须保持原域的实际连续可逆流及实际逆、物理钟与单位、适用酉实现和一般生成元域、Hamiltonian 能量解释、作用量与共同正 $\hbar$。谱差、数学匹配通道及证明中的有限参数均不生产这些物理来源。

**边界 32.4（连续目标与准确余项）。** 定理 28.2 关闭相异实际等价谱格的一整条非对角行；定理 30.1 关闭实际 UHF 分类角内有限非标量谱演员的内部非中央余量；定理 31.2 只在实际角返回 (31.6) 上关闭整行。一般环境输入上，首个仍未支付的推理是从原完整关系推出 (31.1) 的两份实际缺陷相等，即 $E_+=E_-$；(31.2) 仅准确识别它与 $s$ 的关系。非零标量演员 $c=aP$、无限谱演员、一般混合环境整行、从混合行接回完整奇数阶段 UHF 分类，以及完整量子起源和整个物理来源谓词的满足性，都未由这些有限谱结论取得。$c=0$ 保持原零槽结论，§§16、19、25、27 的已识别输入族及其原范围全部保留。

**解释 32.5（谱值差与可重复小块的完整白话）。** 把同一个对象的谱值看成房间上的刻度：现在不要求两间房恰好位于零点两侧且距离相等，只要求刻度不同，并能在实际代数里找到交换两块地面的通道。探查时始终保留整个对象和整个环境输入，不先压进两间房，也不把对象的刻度平移；完整 PB 的两份真实外响应各受同一个二表预算约束，先放大有限标签，Gram 消元便准确抵消共同中点，再轻轻改变数学读取、向正负两个方向提取范数的一次项，并换用相差四分之一转的第二条实际伴通道，就能认出这一小块通向所有其余房间及角外环境的完整连线。UHF 的作用是把任一待测房间或其中任一真实子投影有限地切成小块，每块都能与另一种刻度房间中的同一小块匹配；另一房间的小块可以反复使用，不需要两间整房同样大，也不要求把两间整房等数量配完。这些匹配都由已知代数中的实际酉元和有限矩阵部分等距给出，没有要求未知响应随坐标变化。把约束汇总到同一个固定答案后，余量只能留在非零刻度内部；再探查每个房间的任意子投影，它就只能在每个房间均匀取一个实数。零刻度房间连同角外环境由原 P2 的整个核压缩处理，其中二者之间的交叉压缩也一并消去，不能把角外另算成分类角内的第二个谱格。但一般环境输入下，这些非零房间里的实数还没有被证明消失，准确欠下的是两份真实外层缺陷相等；只有非零谱支撑向角外的连线确实返回已分类角内时，全部实际外标签才可用角分类，整行余量随之为零，而补角背景仍可任意。简化来自谱值之差、实际小块匹配和固定输出的分块几何，没有减少任何原独立公理；已知的完整偶维 UHF 和有限维分类直接沿用，完整奇数阶段全表及量子起源仍保留原目标。已经识别的行具有准确的通常或相反量子乘法值，已分类角具有正 Gram 和数学 Hilbert 表示，但真实准备、完整 Born 菜单、共同相关来源、整台仪器的全部输出与未来、Return、CountRead、正常性、指定前对偶、物理钟、动力学及共同正 $\hbar$，仍由同一个完整递归来源谓词逐项承担。
## 33. 固定输出在相反谱对附近的定性局部稳定性

### 33.1 同一原关系与显式固定输出约束

本增补保持定义 6.1、28.1 及 §27.1 的同一个完整 $\mathsf H_A(D)$ 和其中全部递归固定引文：$A$ 是含单位复 $C^*$-代数，$E=A_{\rm sa}$，$S(x,y)=x\circ y=(xy+yx)/2$，原单位、范数、锥准确为 $1,\|\cdot\|,A_+$。同一 $\Omega/\mathrm{native}$、全部原输入与评价标签不变；原正实线性评价族 $\mathcal P$ 分离 $E$ 并准确决定锥。每份原评价及质量 $m_\gamma=\gamma(1)$ 均保留，包括零、不等、次归一和原表示意义下的非正常评价。未知量仍是同一个任意总映射 $D:E^2\to E$。

全部有向 A1/P2 包含所有 $x,y\in E$、两种次序和每个 $\gamma\in\mathcal P$ 的

$$
\begin{pmatrix}
\gamma(x^2)&\gamma(x\circ y)-i\gamma D(x,y)\\
\gamma(y\circ x)-i\gamma D(y,x)&\gamma(y^2)
\end{pmatrix}\succeq0.
$$

A2 保留每份相加三表 $(x+y,x,y)$ 及其全部排列 $(x_1,x_2,x_3)$：实矩阵 $(\gamma(x_i\circ x_j))_{i,j=1}^3$ 在全部 $\mathbb R^3$ 上半正定，$(1,-1,-1)$ 及相应排列给指定零二次值。A3 保留 $1^2=1$ 及同一个固定有理 $0<\vartheta\le1$ 下的全部 $0\le x\le\vartheta1\Rightarrow x^2\le x$。每个实际原三元组 $(h;x,y)$ 的完整 PB 为

$$
\begin{gathered}
\nu=D(h,x)-h\circ y,\qquad w=h\circ x+D(h,y),\\
D(x+\nu,y+w)-D(x-\nu,y-w)=-2x\circ\nu-2y\circ w.
\end{gathered}
$$

全部实际内外层调用、零、重复、任意有限实幅度、缩放、平移、背景及由它们再次形成的嵌套调用均保留。不加入 $D$ 的可加性、齐次性、连续性、可测性、协变性、单位平移中性、压缩自然性、商下降、双对偶延拓或有限输出子代数闭合。沿 AH43.1 的同表数学正读取，准确锥将原二表交给每个数学正泛函；Hermitian 性与分离性给反对称性，零对角二表给零槽。

对固定自伴 $c,t,g$，置 $k=c\circ t$，记 $\mathsf{P2}(c,t;g)$ 为

$$
M_\phi(c,t;g)=
\begin{pmatrix}
\phi(c^2)&\phi(k)-i\phi(g)\\
\phi(k)+i\phi(g)&\phi(t^2)
\end{pmatrix}\succeq0
\qquad(\phi\ge0).
$$

这里及下文的 $\phi\ge0$ 遍取所有数学正泛函，包括零泛函和任意非负质量，且不要求正常性。反向输出取 $-g$ 时，反向二表是同一表的行列同时交换。写

$$
B_\phi(X,Y)=\phi(X^2)\phi(Y^2)-\phi(X\circ Y)^2\ge0
\qquad(X=X^*,\ Y=Y^*).
$$

因平方对角非负，固定二表条件准确等价于

$$
\phi(g)^2\le B_\phi(c,t)\qquad(\phi\ge0).
\tag{33.1}
$$

在实际模型中，$g=D(c,t)$ 满足它，且对全部状态的读取给 $\|g\|\le\|c\|\,\|t\|$。

**定义 33.1（相反谱对附近的固定输出类）。** 固定 $0\le M<\infty$、$\lambda_*>0$ 及 $\varepsilon\ge0$。$\mathfrak F_{M,\lambda_*}(\varepsilon)$ 的数据为含单位复 $C^*$-代数 $A$、投影 $P$、实际角 $C=PAP$、$c,c^\flat\in C_{\rm sa}$、$t,g\in A_{\rm sa}$、正交投影 $l,m\le P$、$e=e^*\in C$，以及 $\sigma\in\{1,-1\}$、$\lambda\in\mathbb R$，满足

$$
\begin{gathered}
e^2=l+m,\qquad el=me,\\
c^\flat l=lc^\flat=\lambda l,\qquad
c^\flat m=mc^\flat=-\lambda m,\\
\lambda_*\le|\lambda|\le M,\qquad
\|c\|,\|c^\flat\|,\|t\|\le M,\qquad
\|c-c^\flat\|\le\varepsilon,\qquad\|g\|\le M^2.
\end{gathered}
$$

自伴性和 $e^2=l+m$ 给 $e=(l+m)e(l+m)$。$c^\flat$ 在 $P-l-m$ 上没有额外谱条件。置

$$
\jmath=\sigma i,\qquad j=\jmath(l-m)e,\qquad n=2l,
\qquad K_\sigma(x,y)=\frac{\jmath}{2}[x,y].
$$

除 (33.1) 外，对每个有限 $T,\alpha\in\mathbb R$、分别对两条轴

$$
x=Te+\alpha n\quad\hbox{和}\quad x=Tj+\alpha n,
$$

令

$$
\begin{gathered}
h=K_\sigma(c,x),\quad r=c\circ x,\quad k=c\circ t,\\
R_+=x+h-k,\quad R_-=x-h+k,\\
S_+=t+r+g,\quad S_-=t-r-g,\\
L=-2x\circ(h-k)-2t\circ(r+g).
\end{gathered}
$$

要求全部数学正泛函同时满足显式标量 PB 预算

$$
|\phi(L)|\le
\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}
\qquad(\phi\ge0).
\tag{33.2}
$$

每个被开式非负，所有 $\alpha$ 依赖均保留在实际标签和 $L$ 中。实际 $\mathsf H_A(D)$ 元组若整个 $C$ 已按 (28.3) 以同一 $\sigma$ 分类，则 $D(c,x)=K_\sigma(c,x)$，原 $\operatorname{PB}(c;x,t)$ 与两份实际外层 P2 正好给 (33.2)。这个固定输出类允许更大的普通元素集合：它只保留 $g$、已知乘法和上述不等式，不携带响应映射，也不携带 $D(c^\flat,t)$。

定义

$$
\omega_{M,\lambda_*}(\varepsilon)=
\sup_{\mathfrak F_{M,\lambda_*}(\varepsilon)}
\bigl\|l\bigl(g-K_\sigma(c,t)\bigr)(1-l)\bigr\|,
\tag{33.3}
$$

空类的上确界取 $0$。因 $\|K_\sigma(c,t)\|\le\|c\|\,\|t\|\le M^2$，有

$$
0\le\omega_{M,\lambda_*}(\varepsilon)\le2M^2.
\tag{33.4}
$$

### 33.2 统一定性局部稳定性及纸面证明

**定理 33.2（固定输出的相反谱对稳定性）。** 对每个有限 $M\ge0$ 和 $\lambda_*>0$，

$$
\boxed{\displaystyle\lim_{\varepsilon\downarrow0}
\omega_{M,\lambda_*}(\varepsilon)=0.}
\tag{33.5}
$$

结论统一包含两种 $\sigma$。它只针对定义 33.1 的近相反谱对，不声称任意相异 $a,b$ 下具有同一模数。

**证明。** 先在稳定性证明中应用定理 23.2、28.2 的已成精确计算。这里只需说明那份计算如何消费新的固定输出约束，不另立精确行结论为新定理。设类中 $c=c^\flat$。已知代数给

$$
\begin{gathered}
c\circ e=c\circ j=0,\qquad c\circ n=\lambda n,\\
K_\sigma(c,Te+\alpha n)=\lambda Tj,\qquad
K_\sigma(c,Tj+\alpha n)=-\lambda Te.
\end{gathered}
\tag{33.6}
$$

固定第一轴，置 $V=\lambda n\circ t-n\circ k$、$Z=t+\lambda k$。于是
$L=2Te\circ k-2t\circ g-2\alpha(\lambda Tj+V)$。为明确极限次序，先固定 $T,\phi$。对自伴 $A_0,B_0,n$ 和实 $\theta$，置 $C_0=B_0-\theta A_0$，则实半内积 $\langle X,Y\rangle_\phi=\phi(X\circ Y)$ 给

$$
\begin{aligned}
B_\phi(A_0+\alpha n,B_0+\theta\alpha n)
&=\alpha^2B_\phi(n,C_0)+B_\phi(A_0,C_0)\\
&\quad+2\alpha\{\langle A_0,n\rangle_\phi\langle C_0,C_0\rangle_\phi
-\langle A_0,C_0\rangle_\phi\langle n,C_0\rangle_\phi\}.
\end{aligned}
$$

这是 (28.14) 的 Gram 列消元。正号对取 $A_0=T(e+\lambda j)-k$、$B_0=t+g$、$\theta=\lambda$；负号对取 $A_0=T(e-\lambda j)+k$、$B_0=t-g$、$\theta=-\lambda$。(28.15) 在共同中点 $\mu=0$ 时准确成为
$C_\pm=Z\pm g\mp\lambda Te-\lambda^2Tj$。
将 (33.2) 除以 $|\alpha|$，只在这个标量多项式中令 $|\alpha|\to\infty$，得到 (28.16) 的同一不等式

$$
\begin{aligned}
2|\phi(\lambda Tj+V)|\le{}&
\sqrt{B_\phi(n,Z+g-\lambda Te-\lambda^2Tj)}\\
&+\sqrt{B_\phi(n,Z-g+\lambda Te-\lambda^2Tj)}.
\end{aligned}
\tag{33.7}
$$

退化 Gram 也包含：非负多项式除以 $\alpha^2$ 后趋于非负二次系数，平方根在零处连续，故首项为零时对应根号趋零。没有除以首项、质量或谱值。

在忠实含单位表示 $A\subseteq B(\mathcal H)$ 中，内积第一槽共轭线性。(28.17) 给

$$
V=V^*,\qquad lVl=(1-l)V(1-l)=0,\qquad
lV(1-l)=\tfrac12l[c,t](1-l).
$$

取 $\|\xi\|=1$ 的 $\xi\in(1-l)\mathcal H$，先设 $d=\|m\xi\|>0$，置
$\eta=j\xi/d\in l\mathcal H$、$\nu=e\xi/d=-\jmath\eta$。两者均为单位向量，$j\xi=d\eta$，且 $\operatorname{Re}\langle\eta,\nu\rangle=0$。对 $\delta>0$，
$\xi_\delta=(\xi+\delta\eta)/\sqrt{1+\delta^2}$ 才是这里所用的单位向量。令
$\Pi_\eta z=z-\operatorname{Re}\langle\eta,z\rangle\eta$。
对应向量态 $\phi_\delta$ 的 (28.19)–(28.20) 明确为

$$
\begin{gathered}
\phi_\delta(n^2)=\frac{4\delta^2}{1+\delta^2},\qquad
\phi_\delta(W^2)=\frac{\|W\xi+\delta W\eta\|^2}{1+\delta^2},\\
\phi_\delta(n\circ W)=
\frac{2\delta\operatorname{Re}\langle\eta,W\xi+\delta W\eta\rangle}{1+\delta^2},\\
B_{\phi_\delta}(n,W)=\frac{4\delta^2}{(1+\delta^2)^2}
\|\Pi_\eta(W\xi+\delta W\eta)\|^2,\\
\phi_\delta(\lambda Tj+V)=\frac{2\delta}{1+\delta^2}
\bigl(\lambda Td+\operatorname{Re}\langle\eta,V\xi\rangle\bigr)
\qquad(W=W^*).
\end{gathered}
$$

代入 (33.7)，约去正因子 $2\delta/(1+\delta^2)$，仍固定有限 $T$ 后令 $\delta\downarrow0$。
$\Pi_\eta(j\xi)=0$ 消去两份 $-\lambda^2Tj$ 项。置
$A_\xi=\operatorname{Re}\langle\eta,V\xi\rangle$、
$z_\pm=\Pi_\eta((Z\pm g)\xi)$，得到

$$
2|\lambda Td+A_\xi|
\le\|z_+-\lambda Td\,\nu\|+\|z_-+\lambda Td\,\nu\|.
$$

这正是 (28.21)。固定单位 $\nu$、固定 $z$ 和非零实 $\rho$ 时，(28.22) 的有理化给

$$
\|\rho L\nu+z\|-|\rho|L
=\frac{2\rho L\operatorname{Re}\langle\nu,z\rangle+\|z\|^2}
{\|\rho L\nu+z\|+|\rho|L}
\longrightarrow\operatorname{sgn}(\rho)\operatorname{Re}\langle\nu,z\rangle.
$$

令 $\epsilon_\lambda=\operatorname{sgn}\lambda$、$B_\xi=\operatorname{Re}\langle\nu,g\xi\rangle$。
先取 $T=L$，左右减去 $2|\lambda|dL$ 后令 $L\to+\infty$，得
$2\epsilon_\lambda A_\xi\le-2\epsilon_\lambda B_\xi$；再取 $T=-L$，同法得
$-2\epsilon_\lambda A_\xi\le2\epsilon_\lambda B_\xi$。实投影不改变与 $\nu$ 的实配对，共同的 $Z$ 相消。两向合为 $A_\xi=-B_\xi$；由于 $\nu=-\jmath\eta$，准确得到 (28.23)

$$
\operatorname{Im}\langle\eta,g\xi\rangle
=\sigma\operatorname{Re}\langle\eta,V\xi\rangle.
\tag{33.8}
$$

保留 $\epsilon_\lambda$ 同时覆盖正负 $\lambda$。整个次序是先固定 $T$ 取 $|\alpha|\to\infty$，再固定 $T$ 取 $\delta\downarrow0$，最后分别取 $T=\pm L$；没有对未知响应取输入极限。

第二轴是 $e'=j$、$j'=\jmath(l-m)j=-e$，同一约束 (33.2) 对它成立。
$c,t,g,k,V,Z,n,d$ 不变，$\eta'=j'\xi/d=\jmath\eta$。
写 $G=\langle\eta,g\xi\rangle$、$L_0=\langle\eta,V\xi\rangle$，第二轴给
$\operatorname{Im}(-\jmath G)=\sigma\operatorname{Re}(-\jmath L_0)$，即
$-\sigma\operatorname{Re}G=\operatorname{Im}L_0$。
与 (33.8) 合并为 $G=\jmath L_0$，所以

$$
\langle j\xi,(g-\jmath V)\xi\rangle=0
\qquad(\xi\in(1-l)\mathcal H).
\tag{33.9}
$$

这里先对单位向量证明，再由固定算子的二次齐次性推广到任意 $\xi$；$d=0$ 时 $j\xi=0$，式子本来成立，不定义 $\eta$、不除以 $d$。

令 $M_0=g-\jmath V$、$r_0=1-l-m$。
在 (33.9) 取 $\xi=u+z$，$u\in m\mathcal H$、$z\in r_0\mathcal H$，减去 $z=0$ 的式子，得
$\langle ju,M_0z\rangle=0$。$j:m\mathcal H\to l\mathcal H$ 是满等距，故 $lM_0r_0=0$。
对 $z=0$，$T_0=mjM_0m$ 的二次型 $Q(u)=\langle u,T_0u\rangle$ 恒零；即使 $T_0$ 非自伴，复极化仍给

$$
4\langle u,T_0v\rangle
=Q(u+v)-Q(u-v)-iQ(u+iv)+iQ(u-iv)=0.
$$

故 $lM_0m=0$。最后由 $l\jmath V(1-l)=lK_\sigma(c,t)(1-l)$，得到零误差行
$l(g-K_\sigma(c,t))(1-l)=0$。$l=m=0$ 时此式平凡。这份已成计算只应用于固定元素和两轴预算。

现在以 C*-超积证明稳定性。若 (33.5) 不成立，由上确界定义可取 $\delta_0>0$、$\varepsilon_q\downarrow0$ 及各类中的数据，使

$$
\bigl\|l_q\bigl(g_q-K_{\sigma_q}(c_q,t_q)\bigr)(1-l_q)\bigr\|\ge\delta_0.
\tag{33.10}
$$

取子列使 $\sigma_q=\sigma$ 固定，再取自由超滤子 $\mathcal U$。各 $A_q$ 非零，否则该坐标的行范数为零。构造
$A_{\mathcal U}=\prod_q A_q/\{(a_q):\lim_{\mathcal U}\|a_q\|=0\}$，无下标表示有界序列的商类。投影及 $e^2=l+m,el=me$ 等关系逐坐标传递，且 $c=c^\flat$。
有界实数列 $\lambda_q$ 有实超极限 $\lambda$；绝对值的连续性给

$$
|\lambda|=\lim_{\mathcal U}|\lambda_q|\ge\lambda_*>0.
$$

同时 $\|(\lambda_q-\lambda)l_q\|,\|(\lambda_q-\lambda)m_q\|\to_{\mathcal U}0$，故商中确有
$cl=\lambda l$、$cm=-\lambda m$。所有范数界保留，$g=[g_q]$ 只是有界自伴元；没有定义任何 $D_{\mathcal U}$。

须把 **(33.1) 和 (33.2) 两者** 传到商代数的所有状态。先取坐标状态的超积
$\phi_{\mathcal U}([a_q])=\lim_{\mathcal U}\phi_q(a_q)$。
对任意固定有限 $T,\alpha$ 和任一轴，所有标签都是有界序列的有限乘法与实线性组合；两式中的多项式、绝对值及非负平方根都与超极限相容。平方根在 $[0,\infty)$ 上包括零点连续。因此两式首先对每个超积状态成立。

随后消费 Goldbring–Hart，[*On Tsirelson pairs of C*-algebras*，arXiv:2210.15509v3](https://arxiv.org/pdf/2210.15509v3)，§2.2 Lemma 2.3 的状态弱星稠密性。这里写出所需的分离论证，以明确正谱端点和正代表：超积状态集合是凸的，因为对 $0\le\theta\le1$，

$$
\theta[\phi_q]_{\mathcal U}+(1-\theta)[\psi_q]_{\mathcal U}
=[\theta\phi_q+(1-\theta)\psi_q]_{\mathcal U}.
$$

若其弱星闭包 $X$ 不是全部状态空间，Hahn–Banach 分离给自伴 $a$ 及状态 $\rho$，使
$\rho(a)>\sup_{\chi\in X}\chi(a)$。
平移为 $b=a+\|a\|1\ge0$ 保留严格分离。
正元 $b$ 有有界的坐标正代表：取 $b^{1/2}$ 的任一有界提升 $(y_q)$，置 $b_q=y_q^*y_q$，便有 $b=[b_q]$、$b_q\ge0$。
每个 $b_q$ 的最大谱值 $\|b_q\|$ 由一个状态 $\chi_q$ 达到（在单生成交换子代数上取端点态，再作状态延拓）。故超积状态 $\chi$ 满足

$$
\chi(b)=\lim_{\mathcal U}\|b_q\|=\|b\|\ge\rho(b),
$$

与严格分离矛盾。这里在正元上取最大正谱值，没有把任意自伴元的范数误当正谱端点，也没有声称每个商状态本身具有坐标状态表示。该稠密性是被消费的成熟引理。

对固定 $T,\alpha$ 和一条轴，(33.1) 的两边是关于状态的弱星连续多项式；(33.2) 的两边是有限多项式再接绝对值、连续非负平方根。两式因而同时从超积状态传到所有商状态。任一非零数学正泛函为 $\phi=\phi(1)\rho$；若 $\phi(1)=0$，则 $\phi=0$。用两式的正齐次性便覆盖所有正泛函。每组有限参数分别处理，不需要把实参数可数化、作对角化或假设一致参数收敛。

商中数据于是满足上面的零误差计算，给 $l(g-K_\sigma(c,t))(1-l)=0$。然而 C*-超积范数给

$$
\begin{aligned}
\bigl\|l\bigl(g-K_\sigma(c,t)\bigr)(1-l)\bigr\|
&=\lim_{\mathcal U}
\bigl\|l_q\bigl(g_q-K_\sigma(c_q,t_q)\bigr)(1-l_q)\bigr\|\\
&\ge\delta_0>0,
\end{aligned}
$$

矛盾。所用范数公式也可直接由商范数得到：加入超滤零序列不改变范数超极限；反向对任意 $\eta>0$，在属于 $\mathcal U$ 的集合上保留范数至多为该极限加 $\eta$ 的代表，其余坐标置零，即得同一商类的相应上界。故矛盾发生在商范数中。证毕。

## 34. 正谱两块标量余量的尖锐 P2 区间

### 34.1 全复参数铅笔与闭区间

对 §33.1 的固定二表关系，令 $z=x+iy$，定义

$$
F_z=t^2-2x(c\circ t)+|z|^2c^2+2yg.
$$

准确有
$(-\bar z,1)M_\phi(c,t;g)(-z,1)^{\mathsf T}=\phi(F_z)$，从而

$$
\mathsf{P2}(c,t;g)\quad\Longleftrightarrow\quad
F_z\succeq0\quad(z\in\mathbb C).
\tag{34.1}
$$

正泛函分离正锥给右向结论；反向中，任一标量列 $(\alpha,\beta)$ 在 $\beta\ne0$ 时是 $\beta(-z,1)$，在 $\beta=0$ 时二次值为 $|\alpha|^2\phi(c^2)\ge0$。因此等价式包含零首对角项及零泛函，不依赖除以它们。

**定理 34.1（加权两块标量余量的锐平衡区间）。** 取 $a,b,v>0$、$a\ne b$、$\sigma\in\{1,-1\}$ 和实数 $\rho_1,\rho_2$，在 $M_2(\mathbb C)$ 中置

$$
c=\begin{pmatrix}a&0\\0&b\end{pmatrix},\qquad
t=v\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
s=\begin{pmatrix}\rho_1&0\\0&\rho_2\end{pmatrix},\qquad
g=K_\sigma(c,t)+s.
$$

则对全部正泛函成立的 $\mathsf{P2}(c,t;g)$ 准确等价于

$$
\boxed{\quad s=r\begin{pmatrix}a&0\\0&-b\end{pmatrix},\qquad
|r|\le\frac{2v\sqrt{ab}}{a+b}.\quad}
\tag{34.2}
$$

结论包括两个端点、$r=0$、两种 $\sigma$、零泛函和任意质量；只分类这一份固定系数族，不对 $D$ 的不同输入调用施加线性关系。

**证明。** 取未归一向量 $\xi=(\sqrt b,\sqrt a)$ 的正泛函 $\omega_\xi(X)=\xi^*X\xi$，则

$$
\begin{gathered}
\omega_\xi(c^2)=ab(a+b),\quad
\omega_\xi(t^2)=v^2(a+b),\\
\omega_\xi(c\circ t)=v\sqrt{ab}(a+b),\quad
\omega_\xi(K_\sigma(c,t))=0.
\end{gathered}
$$

所以 $\det M_{\omega_\xi}=-(b\rho_1+a\rho_2)^2$。
必要的平衡式是 $b\rho_1+a\rho_2=0$，即 $\rho_1=ar,\rho_2=-br$；它没有分别强迫两余量为零。

对任意复向量 $\eta=(u,w)$，定义

$$
A_\eta=a|u|^2-b|w|^2,\qquad
B_\eta=2\sqrt{ab}\operatorname{Im}(\bar u w).
$$

记 $K=K_\sigma(c,t)$。直接计算给

$$
\omega_\eta(s)=rA_\eta,\qquad
\omega_\eta(K)=\frac{\sigma(b-a)v}{2\sqrt{ab}}B_\eta.
$$

二维 Gram 的 Lagrange 恒等式给

$$
\begin{aligned}
\omega_\eta(c^2)\omega_\eta(t^2)
-\omega_\eta(c\circ t)^2-\omega_\eta(K)^2
&=v^2|au^2-bw^2|^2\\
&=v^2(A_\eta^2+B_\eta^2).
\end{aligned}
$$

减去 $2\omega_\eta(K)\omega_\eta(s)+\omega_\eta(s)^2$，得到包含全部复相位的准确恒等式

$$
\boxed{
\det M_{\omega_\eta}
=v^2\left(B_\eta+
\frac{\sigma(a-b)r}{2v\sqrt{ab}}A_\eta\right)^2
+\left(v^2-\frac{(a+b)^2r^2}{4ab}\right)A_\eta^2.
}
\tag{34.3}
$$

区间 (34.2) 内两项非负，两个平方对角也非负，故所有向量正泛函的二表均正。端点处第二系数恰为零，仍剩下一项平方；$\eta=0$ 给零表，其余向量的两个对角项严格正。有限维谱定理将每个正泛函写成向量正泛函的有限非负和，相应二表逐项相加仍正，故充分性覆盖所有正泛函和全部质量。

必要性不漏复相位：$(A_\eta,B_\eta)$ 映满 $\mathbb R^2$。取 $\sqrt a\,u=L$、$\sqrt b\,w=iM$，$L,M\in\mathbb R$，则
$A_\eta+iB_\eta=(L+iM)^2$，而复平方映满 $\mathbb C$。
若 (34.3) 的第二系数为负，取 $A_\eta=1$、$B_\eta=-\sigma(a-b)r/(2v\sqrt{ab})$，使第一平方为零、行列式为负，矛盾。这证明必要性。

为在下节的实际消费者中使用全参数正证书，仍对平衡数据置

$$
J_\sigma=
\begin{pmatrix}
\dfrac b{a+b}&\dfrac{\sigma ir}{2v}\\
-\dfrac{\sigma ir}{2v}&\dfrac a{a+b}
\end{pmatrix},\qquad H_\sigma=1-J_\sigma.
$$

准确有

$$
\det J_\sigma=\det H_\sigma
=\frac{ab}{(a+b)^2}-\frac{r^2}{4v^2},\qquad
cJ_\sigma t-tJ_\sigma c=\sigma i s.
\tag{34.4}
$$

两矩阵对角为正，所以锐区间正好保证 $0\le J_\sigma\le1$，包括端点。
对 $z=x+iy$，已知乘法展开给

$$
\begin{aligned}
&(t-\bar zc)^*J_\sigma(t-\bar zc)
-(t-zc)^*J_\sigma(t-zc)\\
&\hspace{3em}=-2iy(cJ_\sigma t-tJ_\sigma c)=2\sigma ys.
\end{aligned}
$$

于是以下两个正平方给同一全复参数证书：

$$
\begin{aligned}
Q_z&=(t-zc)^*H_\sigma(t-zc)
+(t-\bar zc)^*J_\sigma(t-\bar zc)\succeq0,\\
Q_{x+iy}
&=t^2-2x(c\circ t)+(x^2+y^2)c^2+iy[c,t]+2\sigma ys\\
&=F_{x+i\sigma y}.
\end{aligned}
\tag{34.5}
$$

$(x,y)\mapsto(x,\sigma y)$ 为双射，故再由 (34.1) 得全部 P2。
特别地，$\sigma=-1$ 时逐点身份是 $Q_{x+iy}=F_{x-iy}$。这是在证明与消费者中使用的初等正平方恒等式，不另立独立分类结论。证毕。

### 34.2 有理内点

取定理 34.1 的固定有理数据

$$
a=1,\quad b=2,\quad v=1,\quad r=\tfrac12,\qquad
c_0=\operatorname{diag}(1,2),\quad
t_0=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
s_0=\operatorname{diag}(\tfrac12,-1),\quad
g_0=K_\sigma(c_0,t_0)+s_0.
\tag{34.6}
$$

此时 $|r|=1/2<2\sqrt2/3$，且

$$
J_\sigma=\begin{pmatrix}2/3&\sigma i/4\\-\sigma i/4&1/3\end{pmatrix},\qquad
H_\sigma=\begin{pmatrix}1/3&-\sigma i/4\\\sigma i/4&2/3\end{pmatrix},\qquad
\det J_\sigma=\det H_\sigma=\frac{23}{144}>0.
\tag{34.7}
$$

又 $c_0J_\sigma t_0-t_0J_\sigma c_0=\sigma i s_0$。
所以 (34.5) 对这一非零余量给完整复平面的正证书，而非有限相位检查。

## 35. 尖锐区间在实际三维 PB 中的非延拓消费者

**命题 35.1（保留非零角外背景的固定 P2 数据不可延拓）。** 在 $A=M_3(\mathbb C)$ 中，对任意固定实数 $\beta\ne0$ 及任意 $\sigma\in\{1,-1\}$，取

$$
\begin{gathered}
\widetilde c=c_0\oplus0,\qquad
\widetilde t=t_0\oplus\beta,\qquad
\widetilde s=s_0\oplus0,\\
\widetilde g=K_\sigma(\widetilde c,\widetilde t)+\widetilde s,
\qquad P=\operatorname{diag}(1,1,0),\qquad C=PAP.
\end{gathered}
\tag{35.1}
$$

则 $\mathsf{P2}(\widetilde c,\widetilde t;\widetilde g)$ 对全部正泛函成立；但不存在满足完整 $\mathsf H_A(D)$、整个 $C$ 的同号分类 (28.3)，并且在这份实际外部输入上有 $D(\widetilde c,\widetilde t)=\widetilde g$ 的总映射 $D$。

**证明。** 完整算子铅笔准确为

$$
\widetilde F_z=F_z\oplus\beta^2\succeq0\qquad(z\in\mathbb C).
\tag{35.2}
$$

第一块由定理 34.1 及其 (34.5)、(34.7) 的证书给正；第三块为非零常数 $\beta^2$。由 (34.1)，全部正泛函都给正二表，包含跨越三维坐标的向量和全部复相位。第三块始终保留。$\widetilde t\notin C$，所以这份原输入确在角外，不能先压缩背景来套用角内分类。

若所述总映射存在，直接应用原命题 31.1 和定理 31.2 的实际外调用接口。具体地，

$$
\widetilde k=\widetilde c\circ\widetilde t=(3t_0/2)\oplus0,
$$

而同一份 $\operatorname{PB}(\widetilde t;\widetilde c,0)$ 的内值是
$D(\widetilde t,\widetilde c)=-\widetilde g$、$D(\widetilde t,0)=0$。两份实际外层对为
$(\widetilde c-\widetilde g,\widetilde k)$、$(\widetilde c+\widetilde g,-\widetilde k)$，其中

$$
\begin{aligned}
\widetilde c-\widetilde g
&=\begin{pmatrix}1/2&\sigma i/2\\-\sigma i/2&3\end{pmatrix}\oplus0,\\
\widetilde c+\widetilde g
&=\begin{pmatrix}3/2&-\sigma i/2\\\sigma i/2&1\end{pmatrix}\oplus0.
\end{aligned}
\tag{35.3}
$$

它们全部落在 $C_{\rm sa}^2$，没有分解未知 $D$ 的任何输入。记这些实际外值的比较缺陷为

$$
\begin{aligned}
E_+&=D(\widetilde c-\widetilde g,\widetilde k)
-K_\sigma(\widetilde c-\widetilde g,\widetilde k),\\
E_-&=D(\widetilde c+\widetilde g,-\widetilde k)
-K_\sigma(\widetilde c+\widetilde g,-\widetilde k).
\end{aligned}
$$

整个角分类逐值给 $E_+=E_-=0$。
然而同一个实际 PB 要求两份外值的差为 $2\widetilde c\circ\widetilde g$；已知比较映射的差为
$2K_\sigma(\widetilde c,\widetilde k)=2\widetilde c\circ K_\sigma(\widetilde c,\widetilde t)$。
因此原 (31.2) 在这份数据上准确要求

$$
E_+-E_-=2\widetilde c\widetilde s
=\operatorname{diag}(1,-4,0)\ne0,
\tag{35.4}
$$

矛盾。这里实际非零谱支撑为 $S=P$，且 $(1-P)\widetilde tS=0$，正是原定理 31.2 的返回条件；补角背景非零并未妨碍实际外调用返回。证毕。

本命题是定理 34.1 的尖锐固定数据族相对于**完整 PB 加整个已分类角**的非延拓应用，没有构造满足完整公理的反模型，也没有重新分类 $M_2$ 或 $M_3$。原 AH42.4 已覆盖的有限维全域分类直接复用；命题 31.1、定理 31.2 是这里被消费的既有接口。

## 36. 准确量子对应、完整来源与两笔独立余项

### 36.1 已识别块与通常或相反乘法

置

$$
\Pi_\sigma(c,t)=
\begin{cases}ct,&\sigma=1,\\tc,&\sigma=-1.\end{cases}
$$

已知代数中始终有
$S(c,t)-iK_\sigma(c,t)=\Pi_\sigma(c,t)$。
因此定理 33.2 对同一固定输入、固定输出给准确的近似块对应

$$
\begin{aligned}
&\bigl\|l\bigl((S(c,t)-ig)-\Pi_\sigma(c,t)\bigr)(1-l)\bigr\|\\
&\hspace{4em}=\bigl\|l\bigl(g-K_\sigma(c,t)\bigr)(1-l)\bigr\|
\le\omega_{M,\lambda_*}(\varepsilon).
\end{aligned}
\tag{36.1}
$$

$g-K_\sigma(c,t)$ 自伴，所以反向交叉块也受同一界控制。两个对角块
$l(g-K_\sigma(c,t))l$、$(1-l)(g-K_\sigma(c,t))(1-l)$ 不由此控制。实际 $\mathsf H_A(D)$ 数据满足定义 33.1 时，直接取 $g=D(c,t)$ 使用此式；没有把 $D$ 搬到商或变化输入上。

对定理 34.1 的固定数据，准确有

$$
S(c,t)-ig=\Pi_\sigma(c,t)-is.
\tag{36.2}
$$

尖锐 P2 区间描述其中的对角自由度；在命题 35.1 的实际返回条件下，原 §31 的跨调用关系排除非零 $s$。一般环境中只有已证明 $s=0$ 的输入才取得完整行 $S(c,t)-iD(c,t)=\Pi_\sigma(c,t)$。

在已经整体分类的 $C$ 上，AH64.1、75.1 的既有消费者给 $S-iD$ 的复线性延拓为通常或相反 $C^*$-乘法，保持伴随、准确锥、单位 $P$ 和原范数；全部有限角内旧复 Gram 正。每个原限制评价有数学 GNS，循环向量平方范数准确为 $\gamma(P)$，零角质量给零向量。这是普通量子代数与数学 Hilbert 表示的准确对应。局部交叉块或单对固定数据没有供应整个未知环境的双线性、结合乘法或全部有限旧复 Gram。真实效果菜单及 Born 概率仍按下述同一物理来源消费，而非由数学向量态生产。

### 36.2 同一个递归全文物理来源谓词

**定义 36.1（来源的全文身份保持）。** 本增补的 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$ **就是定义 32.3 的同一个谓词**，严格沿

$$
32.3\ \Longrightarrow\ \S27.1\ \Longrightarrow\ 26.3
\ \Longrightarrow\ 22.3\ \Longrightarrow\ 18.2
\ \Longrightarrow\ \{10.2,15.2,\mathrm{AH}28.1,64.2,75.1\}
\ \Longrightarrow\ \mathrm{SQ}47.1\text{--}47.13
$$

的全文身份关系，将其中**每份定义、合同、公式、量词及逐项递归纳入、逐层固定版本的全部上游全文，逐句、逐公式、逐量词同时合取**。箭头表示原定义的完整纳入，既非另造较短谓词，也非只保留编号范围；以下范围说明不替代任何被纳入的全文或原前件。

直接 AH 身份保持 `b1a95e41b9622e9f720e51f9bb899841f5b74ca1`；W、CC、PT 的原直接身份保持 `3b10aed60f60e4901bae6cf2e160bf439d642e64`。SQ 主源仍按其自身 1.3、39、41.1、47.1 解析，`dcaebc0b9ca5a3a463fd8cfd161d38967df28668` 与 `0aa11dbc3dc337d667b98900673e07d67b99bf46` 保持相应层级。OP/PT/PB/SM/C/AQ/R3/W/FR/XV/SF 的 `f24d1138a7b994da16abd9a47affedea64ea44ce`、AH22.1 保留的 `2addd6f369b7387226c2b0cc984623dd3efe40a1`、AH12.1 上游 `39a0505470ea889dd9d4301ad60cd9506a5e8b58`、AH42.1 中 OP 等直接身份 `bef9bba367a24ab5e250491dcb88ed85ebc29cf7` 全部保持。原根、静默和其他静态分支不改为 UHF；各内层来源不被直接读取身份压平。

实际准备、相干控制、原事件绑定的实际完整 Born 菜单及全部原质量保留各自来源。对实际全局菜单 $\sum_j e_j=1$，只有 $\gamma(1)>0$ 才以 $\gamma(e_j)/\gamma(1)$ 归一；角菜单 $\sum_j e_j=P$ 另需原实际条件化及 $\gamma(P)>0$。零、不等、次归一和非正常质量均保留。真正相关联合与张量仍须同一实际共同来源、全部相关输入、忠实同向交换腿、共同生成、分离与所需重数；相同边缘、分别可达、数学谱格、等价投影和 GNS 不代付共同实现。

typed CP、箭头下降、整台递归同源参考、原真支持和支持内补、交织夹界、全部所需有限深度与每个正精度保留全部原前件。完整仪器、TP、Kraus、更新和 Lüders 仍须完整 typed 菜单、完整单位分区、接受端、校准、表示及收敛条件，量化**整个环境、全部成功／失败／细记录／port／post-port 输出，以及每份完整输出的每个仍合法未来**。只有严格正的实际输出质量可归一，失败和零分支不删除。

合法顺序、自适应与并行历史、真正分组遗忘、停止、拒绝、销毁、泄漏、同数两侧及逆向真实 Return、完整 CountRead 的活动 ready 与 producer 全部保留。相同算子不合并原程序、记录、读取次序、原零集或未来权限；未定义请求不补零。正常性、指定前对偶、无限菜单及记录的可数可加和收敛仍须原扩展来源。物理动力学仍须保持原域的实际连续可逆流及实际逆、物理钟与单位、适用酉实现、一般生成元域、Hamiltonian 能量解释、作用量及共同正的物理 $\hbar$。超积中的所有数学状态、正泛函、GNS、固定有限参数和代数范数尺度 $M$ 都不产生这些物理来源。

### 36.3 贡献归属与两个独立的未付条件

本增补的条件纸面推导为固定输出的相反谱对定性稳定性，以及加权两块标量余量的尖锐区间在当前实际 PB 非延拓例中的应用。定理 23.2、28.2 的精确零误差计算和原命题 31.1、定理 31.2 的返回接口均为被消费的既有结果。Goldbring–Hart §2.2 Lemma 2.3 的超积状态稠密性、C*-超积与商范数、有限维谱定理、Gram 列消元、二维 Lagrange 恒等式、固定向量范数的一次项、复极化及正平方展开是证明中的成熟工具。忠实表示、正泛函和数学 GNS 的归属沿定义 10.1。这里不主张文献优先权或穷尽检索，也不将标量泛函 P2 升格为算子二正性。

[单位桥卷 W 命题 94.3](https://github.com/the-omega-institute/trureturing/blob/3e79ddab3b75e7023ab3e7f4ebc56f681bfb0a03/docs/develop/theory/AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md) 已以 $b=\sigma_x,d=\sigma_z$ 说明：固定 P2 与逐特征空间的必要零条件不能推出整个支撑零面。本卷命题 21.1 已给满足全部有向 A1/P2、A2/A3 和指定角分类而明确违反完整 PB 的弱条件总映射。因而一般的“P2 必要条件不足”不是这里另行取得的结论。这里保留的是具体加权系数族的**准确闭区间**和命题 35.1 的**当前实际外调用消费者**。

一般混合行与增长谱窗口仍有两笔独立义务：

1. **精确余量的跨调用消去。** 在原定理 29.1 的有限谱条件下，$c=\sum_i a_ip_i$、$S=\sum_{a_i\ne0}p_i$、$g=D(c,t)=K_\sigma(c,t)+s$，其中 $s=s^*\in SAS$、$[c,s]=0$。原命题 31.1 对两份实际缺陷

   $$
   E_+=D(c-g,k)-K_\sigma(c-g,k),\qquad
   E_-=D(c+g,-k)-K_\sigma(c+g,-k),\qquad k=c\circ t
   $$

   给 $E_+-E_-=2cs$，且 $E_+=E_-$ 当且仅当 $s=0$；在原定理 30.1 的逐格标量范围，这又当且仅当所有非零谱格的 $\rho_i=0$。原定理 31.2 在 $(1-P)tS=0$ 上已支付该相等。一般非返回输入仍有原 (31.8)

   $$
   \begin{aligned}
   W_+&=(c-g)+\jmath k=c-s+\jmath tc,&W_+S&=W_+,\\
   W_-&=(c+g)-\jmath k=c+s-\jmath tc,&W_-S&=W_-,\\
   (1-P)W_\pm&=\pm\jmath(1-P)tc.
   \end{aligned}
   $$

   若 $(1-P)tS\ne0$，则 $(1-P)tc\ne0$，两份外层对不能全部放入已分类的 $C$。右支撑不代付返回；首个一般混合行缺口仍准确是 **$E_+=E_-$，或其适用范围内的逐格 $\rho_i=0$**，不是只剩误差累加。这里没有把该相等增加为公理。

2. **近似误差的可累加性。** 定理 33.2 没有显式收敛率。由 $\omega_{M,\lambda_*}(\varepsilon)\to0$ 不能推出增长谱窗口中的 $N\omega_{M,\lambda_*}(\varepsilon)^2\to0$，也不能用已有 $N\kappa^2\to0$ 的其他误差预算替代响应误差。它只在 $c^\flat l=\lambda l,c^\flat m=-\lambda m$ 且 $|\lambda|\ge\lambda_*$ 的近相反谱对上成立；原定理 28.2 的一般相异谱值精确结论不自动给出任意 $a\ne b$ 的近似模数。

非零标量演员的未覆盖输入、无限谱演员、一般混合环境整行、接回完整奇数阶段 UHF 全域分类，以及完整量子起源与整个物理来源谓词的满足性，均保持原未解边界。$c=0$ 的原零槽及 §§16、19、25、27、28–32 已识别输入族完整保留。以上简化属于条件几何与固定输出的组织，没有减少原独立公理，也没有给任意总 $D$ 添加正则性或延拓。

### 36.4 完整白话

把谱格看成带刻度的房间，把 $g$ 看成未知规则对同一个实际问题已经写下的答案：第一幅图中，两间可以互相搬运的小房间在参考演员 $c^\flat$ 上分别带 $\lambda$ 与 $-\lambda$，两刻度的距离始终至少为 $2\lambda_*$，趋于零的是演员扰动 $\|c-c^\flat\|$，而不是这道谱隙。我们不要求未知规则随输入连续，只把每份固定答案与全部有限探针放入 C*-超积；在那里演员误差消失，原来两根相差四分之一转的伴轴就把答案从一间房通向整个补角的交叉部分锁成已知交换子。所有商状态都必须得到约束，状态稠密性负责这一步，却不把数学状态变成物理准备；房间内部的均匀余量也没有因此消失。第二幅图改用两个不同的正刻度：即使所有正泛函和复相位都读取同一张二表，余量仍可按两刻度一正一负地平衡，并沿准确的一整段闭区间移动，正平方证书覆盖了每一个复参数。把这份有理数据放进真正三维环境时，第三间房保留非零背景，原问题仍来自角外；完整 PB 却将这个答案送入另外两份真实调用，这两份调用恰好返回已经认识的整个角，于是它们的缺陷都为零，与当前非零余量要求的缺陷差冲突。一般不能返回时，仍欠这两份实际缺陷为何相等；若要用许多近似小房间拼起无限谱，还另欠误差怎样累加。这两笔账不能互相替代。所得的通常或相反乘法值、正 Gram 和数学 Hilbert 表示各守已证明范围，真实准备、完整 Born 菜单、同一共同相关来源、整台仪器全部输出及未来、Return、CountRead、正常性、前对偶、物理钟、动力学和共同正 $\hbar$ 仍须原来的完整来源逐项供应。

## 追加锚（本行以下为增补区）

## 37. 两份原外调用的无预匹配符号刚性

### 37.1 完整原关系、已付单位行与固定余量

**定义 37.1（同一原域与完整原条件）。** 以下保持定义 6.1、28.1 的同一个完整 $\mathsf H_A(D)$ 及其全部递归固定引文。$A$ 是含单位复 $C^*$-代数，$E=A_{\rm sa}$，$S(x,y)=x\circ y=(xy+yx)/2$；原单位、范数与准确锥分别为 $1,\|\cdot\|,A_+$。同一 $\Omega/\mathrm{native}$、全部原输入及评价标签保持，原正实线性评价族 $\mathcal P$ 分离 $E$ 并准确决定锥。每份原评价及质量 $m_\gamma=\gamma(1)$ 保留，包括零、不等、次归一及原表示意义下的非正常评价。未知量仍是同一个任意总映射 $D:E^2\to E$。

全部有向 A1/P2 要求所有原 $x,y$、两种次序和每个 $\gamma\in\mathcal P$ 的

$$
\begin{pmatrix}
\gamma(x^2)&\gamma(x\circ y)-i\gamma D(x,y)\\
\gamma(y\circ x)-i\gamma D(y,x)&\gamma(y^2)
\end{pmatrix}\succeq0.
\tag{37.1}
$$

A2 保留相加三表 $(x+y,x,y)$ 及全部排列 $(x_1,x_2,x_3)$：实矩阵 $(\gamma(x_i\circ x_j))_{i,j=1}^3$ 在全部 $\mathbb R^3$ 上半正定，$(1,-1,-1)$ 及相应排列给指定相加零二次值。A3 保留 $1^2=1$，以及同一个固定有理 $0<\vartheta\le1$ 下全部 $0\le x\le\vartheta1\Rightarrow x^2\le x$。对每个实际原三元组 $(h;x,y)$，完整 PB 仍为

$$
\begin{gathered}
v=D(h,x)-h\circ y,\qquad w=h\circ x+D(h,y),\\
D(x+v,y+w)-D(x-v,y-w)=-2x\circ v-2y\circ w.
\end{gathered}
\tag{37.2}
$$

全部实际内值、外值、零、重复、任意有限实幅度、缩放、平移、背景及由它们再次形成的每个嵌套调用均保留。不附加 $D$ 的输入可加性、齐次性、连续性、可测性、协变性、压缩自然性、商下降、双对偶延拓或有限阶段输出闭合。

AH 的直接身份仍为 `b1a95e41b9622e9f720e51f9bb899841f5b74ca1`；W、CC、PT 的原直接身份仍为 `3b10aed60f60e4901bae6cf2e160bf439d642e64`，各内部引文按自身固定身份解析。AH43.1 的反对称性、零槽、比例零值及同表数学正读取直接复用。PT183.2 的完整证明在 PT §§183–184，已由 AH43.3、式 (43.5) 准确实例化到 $X_{\rm JB}=E=A_{\rm sa}$、恒等稠密包含。因此对所有原 $b\in E$、$\mu\in\mathbb R$，**全局单位行 $D(\mu1,b)=0$ 已经成立**，不是未付条件。PT185.1 同时供应全部 $SO(2)$ 标签旋转不变性、各槽奇性、同一仿射轴上的零值及 $D(a,\lambda a^2)=0$；这些既有结果不在这里重证。

**定义 37.2（有限谱固定行与完整原外标签）。** 固定实际投影 $P$，并假定同一 $D$ 在整个实际角 $C=PAP$ 上已按 (28.3) 分类为

$$
D(x,y)=K_\sigma(x,y),\qquad
K_\sigma(x,y)=\frac{\jmath}{2}[x,y],\qquad
\jmath=\sigma i,\quad\sigma\in\{1,-1\},\quad x,y\in C_{\rm sa}.
$$

W119.2–119.3 和 W 式 (120.2) 的整个实际角支撑与完整继承直接复用：角单位为 $P$，锥、范数准确继承，原评价标签限制后仍逐份保留，质量为 $\gamma(P)$；同值限制不合并、零限制不删除、质量不归一。

令 $c=c^*\in C$ 具有有限谱，实际非零谱支撑为 $S\le P$。对固定任意 $t=t^*\in A$，使用如下已经取得的余量资料：

$$
g=D(c,t)=K_\sigma(c,t)+s,\qquad
s=s^*\in SAS,\qquad[c,s]=0.
\tag{37.3}
$$

定理 29.1 的实际有限匹配是这些资料的一个充分来源；定理 30.1 的内在 UHF 条件还给逐谱格实标量余量，以下不需要这一加强。这里允许一般交换块余量，不预设 $p_i s p_i$ 是标量。写

$$
c=\sum_{i=1}^r\lambda_i p_i,\qquad
S=\sum_i p_i,\qquad
c_S^{-1}=\sum_i\lambda_i^{-1}p_i\in SAS,
\tag{37.4}
$$

其中非零谱值 $\lambda_i$ 两两不同；$P-S$ 可有内部零谱格。$S=0$ 时约定 $c=s=c_S^{-1}=0$。

保留原 $\operatorname{PB}(t;c,0)$ 真正生成的整对外输入，定义

$$
\begin{gathered}
k=c\circ t,\qquad a_+=c-g,\qquad a_-=c+g,\\
E_+=D(a_+,k)-K_\sigma(a_+,k),\qquad
E_-=D(a_-,-k)-K_\sigma(a_-,-k).
\end{gathered}
\tag{37.5}
$$

原命题 31.1 的计算只使用 (37.3)、反对称性、零槽及这个 PB，故直接给

$$
E_+-E_-=2cs.
\tag{37.6}
$$

同一 PB 也给 $D(a_+,k)-D(a_-,-k)=2c\circ g$。由于 $a_+^2-a_-^2=-4c\circ g$，准确有

$$
M_+:=a_+^2+k^2+2D(a_+,k)
=a_-^2+k^2+2D(a_-,-k)=:M_-.
\tag{37.7}
$$

对应复标签始终是原标签

$$
\begin{aligned}
W_+&=a_++\jmath k=c-s+\jmath tc,&W_+S&=W_+,\\
W_-&=a_--\jmath k=c+s-\jmath tc,&W_-S&=W_-.
\end{aligned}
\tag{37.8}
$$

这里没有压缩外输入、拆分未知 $D$ 的输入或重新放置标签。

### 37.2 两个独立普通符号的联合消费者

**定理 37.3（两份完整原响应无需预匹配取向）。** 在定义 37.1–37.2 下，若存在两个普通标量符号 $\varepsilon_+,\varepsilon_-\in\{1,-1\}$，使

$$
D(a_+,k)=K_{\varepsilon_+}(a_+,k),\qquad
D(a_-,-k)=K_{\varepsilon_-}(a_-,-k),
\tag{37.9}
$$

则

$$
\boxed{s=0,\qquad E_+=E_-=0.}
\tag{37.10}
$$

若其中任一符号不同于 $\sigma$，还必有 $(1-S)tS=0$。因此 $(1-S)tS\ne0$ 时，两份普通响应的符号只能都为 $\sigma$。条件 (37.9) 针对两份**完整原调用**；它不是仅一块压缩的响应，也不是中心投影上的分段符号，且没有从一般 $\mathsf H_A(D)$ 自动取得。

**证明。** 对自伴 $a,b$ 和普通符号 $\varepsilon$，已知乘法恒等式为

$$
a^2+b^2+2K_\varepsilon(a,b)
=(a+\varepsilon ib)^*(a+\varepsilon ib).
\tag{37.11}
$$

于是每份 $M_\pm$ 在 $\varepsilon_\pm=\sigma$ 时等于 $W_\pm^*W_\pm$，在 $\varepsilon_\pm=-\sigma$ 时等于 $W_\pm W_\pm^*$。两份平方仍由 (37.7) 相等。分四种符号情况消费这个相等。

若 $\varepsilon_+=\varepsilon_-=\sigma$，两缺陷各自为零。(37.6) 给 $cs=0$，以 (37.4) 的实际角逆左乘得到 $s=0$；这是 §31 的既有同号消费者。

若 $\varepsilon_+=\sigma$、$\varepsilon_-=-\sigma$，则

$$
W_+^*W_+=W_-W_-^*.
$$

令 $R=1-S$。右支撑 $W_+S=W_+$ 使左边在 $SAS$，故

$$
(RW_-)(RW_-)^*=RW_-W_-^*R=0.
$$

$C^*$ 恒等式给 $RW_-=0$。由 (37.8)、$Rc=Rs=0$，得到 $Rtc=0$；右乘实际 $c_S^{-1}$ 得 $RtS=0$。另一混合情况 $\varepsilon_+=-\sigma$、$\varepsilon_-=\sigma$ 给 $W_+W_+^*=W_-^*W_-$，同理得到 $RW_+=0$ 和 $RtS=0$。自伴性给 $StR=0$，于是 $ct,tc\in SAS$，再由 (37.3) 得 $g,k,a_\pm\in SAS\subseteq C$。整个原 $C$ 的分类逐份给两原外响应为 $K_\sigma$，故 $E_+=E_-=0$，(37.6) 给 $s=0$。这里消费的正是 §31.2 的已付返回论证。

最后，若 $\varepsilon_+=\varepsilon_-=-\sigma$，令 $U=s-\jmath tc$，则 $W_\pm=c\mp U$。两份左平方相等，直接展开得到

$$
0=W_+W_+^*-W_-W_-^*=-4cs-2\jmath[c^2,t],
\qquad 2cs=-\jmath[c^2,t].
\tag{37.12}
$$

由 $[c,s]=0$ 及有限谱投影演算，$s=\sum_i p_i s p_i$。对每个非零谱格压缩 (37.12)，得到

$$
2\lambda_i p_i s p_i=-\jmath p_i[c^2,t]p_i=0.
$$

每个 $\lambda_i\ne0$，故消去全部自伴块余量后有 $s=0$，继而 $[c^2,t]=0$。在有限集合 $\{0\}\cup\{\lambda_i^2\}_i$ 上作实多项式插值，取 $f(0)=0$、$f(\lambda_i^2)=1$，便有原代数内的准确身份 $S=f(c^2)$。因此 $[S,t]=0$，即 $RtS=0$。两份完整外调用又都进入 $C$，原分类给 $E_+=E_-=0$。这不要求正负谱值的平方互异，插值只在不同平方值上进行。$S=0$ 时所有结论直接来自原零槽。∎

分别有两个整个已分类的实际角、各自容纳 $(a_+,k)$ 与 $(a_-,-k)$ 并给一个普通标量取向，是 (37.9) 的一个充分来源；无需预先有共同角或预先匹配取向。这里的新推断是两个原平方联合约束普通符号，不是新作角分类。

在这种来源下，结论后还可读取每个供应角的实际位置。此时 $s=0$，若任一 $W_\pm\in QAQ$，则

$$
W_\pm^*W_\pm=H:=c(1+t^2)c\ge c^2.
\tag{37.13}
$$

$H$ 在单位为 $S$ 的实际角 $SAS$ 中可逆。由 $QH=H$ 得 $QS=QHH^{-1}=S$，原标签式再给 $(1-Q)tS=0$；于是该角事后承载两份原标签。这个结论不把事后的共同承载提前当作 (37.9) 的前提。

## 38. 原标签的实际承载接口与既有偶角消费者

### 38.1 成熟角承载条件在两份原标签上的实例

**接口 38.1（保留实际位置的等价条件）。** 对定义 37.2 的固定元素及任意实际投影 $Q\in A$，下列条件等价：

$$
\begin{gathered}
a_+,k,a_-,-k\in QAQ;\\
W_+,W_-\in QAQ;\\
S\le Q\quad\hbox{且}\quad(1-Q)tS=0.
\end{gathered}
\tag{38.1}
$$

这是实际角和自伴实虚部的中间接口。前两项由 $W_\pm$ 的自伴实虚部互相恢复。若两标签在角中，$W_++W_-=2c$ 给 $Qc=c=cQ$；乘 $c_S^{-1}$ 得 $S\le Q$，因此 $s\in QAQ$。由 $W_+=c-s+\jmath tc$ 又得 $tc\in QAQ$；右乘 $c_S^{-1}$ 得 $tS\in QAQ$，故 $(1-Q)tS=0$。反向，$S\le Q$ 与 $(1-Q)tS=0$ 给 $tc\in QAQ$，伴随给 $ct\in QAQ$，$c,s$ 也在此角中，故两标签及其全部自伴实虚部均在角中。$S=0$ 包含在同一接口内。

特别，在三进 UHF 中存在真共同承载角，准确等价于存在

$$
0\ne e=e^2=e^*\in A,\qquad e\le1-S,\qquad etS=0.
\tag{38.2}
$$

由真承载角取 $e=1-Q$；反向取 $Q=1-e$ 并消费 (38.1)。这是原标签位置条件，不能由重新摆放一个与 $S$ 等价的投影代替。

### 38.2 真承载角的实际偶化及已付分类

在 $A=M_{3^\infty}$ 中，任意非零真承载投影 $Q$ 均可扩大为仍然真的实际偶承载投影 $\widetilde Q$。这里只消费 AH67.2 式 (67.3) 的成熟近投影酉共轭和有限矩阵秩。取实际酉 $u\in A$，使 $Q_0=uQu^*\in M_{3^m}$，记其秩为 $k$。若 $k$ 偶，取 $\widetilde Q_0=Q_0$；若 $k$ 奇，在该阶段给它加一个正交秩一投影。后一情形因 $3^m$ 奇且 $k<3^m$，必有 $k+1<3^m$。于是

$$
Q\le\widetilde Q=u^*\widetilde Q_0u<1,
\qquad
\widetilde QA\widetilde Q
=\overline{\bigcup_{\ell\ge m}u^*\widetilde Q_0M_{3^\ell}\widetilde Q_0u}^{\|\cdot\|}.
\tag{38.3}
$$

右边每个实际满矩阵阶段以 $\widetilde Q$ 为单位，大小为 $\operatorname{rank}(\widetilde Q_0)3^{\ell-m}$，全为偶数。W119–120 给同一 $D$ 的整个角继承，AH70.1 因而分类整个 $\widetilde QA\widetilde Q$。共轭只构造已知实际载体，不对未知 $D$ 使用协变性，也不声称 $D$ 保持某个有限阶段。

因此，对定理 29–30 的有限非标量谱资料，若两份原标签有真共同承载角，就已有更大实际已分类角可供 §31.2 的返回论证使用。其符号与原 $C$ 的符号可在同一 $SAS$ 的一个非零交换子上比较：$S\ne0$ 时，AH67.2 将 $S$ 送入有限阶段，整个 $SAS$ 的内在满矩阵阶段大小无界，故确有这样的实际交换子。两种分类读取同一个旧 $D$ 值，强制符号一致。于是两份原缺陷为零，再由 (31.2) 消去 $s$。固定 $P$ 的返回可以失败而较大角的返回成立，但这只是原返回消费者更换已支付的实际载体，不另计新的无条件分类。实际有限阶段偶角及共同取向仍由 AH71.2–72.1 直接供应。

接口 (38.1)、实际偶化、闭值域公式、投影等价及角内矩阵模型在这里都只是原调用的承载工具；它们不单列为新的基础定理。下一节检验的是这些工具是否自动供应所需的原位置。

## 39. 满足完整原关系的三进 UHF 原标签安置障碍

**定理 39.1（小支撑、各自闭值域和三份容量不推出真角安置）。** 对每个整数 $N\ge2$ 和普通符号 $\sigma\in\{1,-1\}$，在实际代数 $A=M_{3^\infty}$ 中，存在 $P=S$、$c=p_1+2p_2$、$t=t^*$ 及全域标准映射 $D=K_\sigma$，满足完整 $\mathsf H_A(D)$，并且

$$
\tau(S)=\frac2{3^N},\qquad SAS\cong M_2(M_{3^\infty}),
\qquad s=E_+=E_-=0.
\tag{39.1}
$$

两份完整原标签 $W_\pm=(1\pm\jmath t)c$ 各有原代数中的闭值域投影 $q_\pm\sim S$，但任何实际投影 $Q\ge q_+,q_-$ 都等于 $1$。甚至每个单独的完整 $W_\pm$ 都不属于任何真角 $QAQ$。同时 $3\tau(S)\le1$，并可在原有限阶段放置三份两两正交、各与完整 $S$ 实际等价的副本。

**证明。** 采用实际张量模型

$$
A=\overline{\bigcup_m M_{3^m}}^{\|\cdot\|},\qquad
\Delta=C(X),\qquad X=\{0,1,2\}^{\mathbb N},
$$

其中 $\Delta$ 是标准对角，$X$ 带均匀乘积测度 $\mu$。有限矩阵归一迹相容，给出 AH67.1 的忠实数学迹 $\tau$。有限级删除非对角矩阵元的映射相容、正、含单位、收缩，因而延成标准对角条件期望 $\mathbb E:A\to\Delta$。有限级双模性质经范数密度给 $\Delta$ 双模性质，且 $\tau\mathbb E=\tau$。故 $x\ge0$、$\mathbb E(x)=0$ 蕴涵 $\tau(x)=0$，再由迹忠实性给 $x=0$。这是本构造消费的成熟 AF 对角期望接口。

在 $M_{3^N}$ 中取两个不同的对角秩一投影 $p_1,p_2$，令

$$
S=P=p_1+p_2,\qquad R=1-S,\qquad c=p_1+2p_2.
$$

其整个实际角为 $M_2\otimes M_{3^\infty}$。固定 $0<\delta<\tau(S)$。在 $R$ 对应的 clopen 集 $X_R$ 中枚举非空 clopen 基 $(B_m)_{m\ge1}$。依次处理：若 $B_m$ 与此前已选的有限并相交，则跳过；否则在 $B_m$ 内选非空柱集，测度小于 $\delta2^{-(m+1)}$。每个非空开集均有任意小的子柱集，故选择可行。

把所选柱集依次记为 $C_n$。它们两两不交，且每个非空开集包含某个 $B_m$，后者或已与所选集合相交，或在该步从其中选取了一个子柱集；因此 $\bigcup_n C_n$ 在 $X_R$ 中稠密，并有

$$
\sum_n\mu(C_n)<\delta.
\tag{39.2}
$$

选择必有无限多次。否则有限 clopen 并稠密于 $X_R$，只能等于 $X_R$，与其测度小于 $\delta<\tau(S)<\tau(R)$ 矛盾。置 $r_n=1_{C_n}\in\Delta$，每个 $r_n$ 是某个实际有限阶段的对角投影。

递归取两两正交的实际对角 $s_n\le S$，使 $\tau(s_n)=\tau(r_n)$。第 $n$ 步将 $S,r_n,s_1,\ldots,s_{n-1}$ 放进共同有限阶段 $M_{3^{L_n}}$。由 (39.2)，剩余投影 $S-\sum_{j<n}s_j$ 的迹严格大于 $\tau(r_n)$。这些迹均为整数秩除以 $3^{L_n}$，故可在剩余对角中精确取与 $r_n$ 同秩的 $s_n$。同一矩阵阶段的矩阵单位提供实际 $v_n\in RAS$，满足

$$
v_n^*v_n=s_n,\qquad v_nv_n^*=r_n.
\tag{39.3}
$$

在已知代数中定义范数收敛级数

$$
b=\sum_{n\ge1}2^{-n}v_n\in RAS,\qquad t=b+b^*.
\tag{39.4}
$$

初始投影和终止投影分别正交，所以 $bs_n=2^{-n}v_n$，且 $tS=b$。

若实际投影 $e\le R$ 满足 $eb=0$，则右乘 $s_n$ 得 $ev_n=0$，继而 $er_n=0$。期望双模性给 $\mathbb E(e)r_n=0$，又有 $\mathbb E(e)=R\mathbb E(e)R$。连续函数 $\mathbb E(e)$ 遂在 $X_R$ 的稠密并 $\bigcup_n C_n$ 上为零，也在 $X\setminus X_R$ 上为零，故 $\mathbb E(e)=0$。期望忠实性给 $e=0$。因此

$$
S\le Q,\quad(1-Q)tS=0\quad\Longrightarrow\quad Q=1,
\tag{39.5}
$$

因为 $e=1-Q\le R$ 满足 $eb=0$。这在原代数内排除所有真共同承载投影。

现在在整个原域上取 $D=K_\sigma$。余量和两缺陷都为零，两份原标签为 $W_\pm=(1\pm\jmath t)c$，且

$$
H=W_\pm^*W_\pm=c(1+t^2)c\ge c^2\ge S.
$$

在单位为 $S$ 的实际角 $SAS$ 中作连续函数演算，取得 $H^{-1}$、$H^{-1/2}$，置

$$
u_\pm=W_\pm H^{-1/2},\qquad
q_\pm=W_\pm H^{-1}W_\pm^*.
\tag{39.6}
$$

直接相乘得 $u_\pm^*u_\pm=S$、$u_\pm u_\pm^*=q_\pm$。故 $q_\pm$ 是实际投影，且 $q_\pm\sim S$。又 $W_\pm=u_\pm H^{1/2}$，其中 $H^{1/2}$ 在 $SAS$ 中可逆，所以在任意忠实表示中 $W_\pm$ 的像正是 $u_\pm S\mathcal H$，为闭子空间，像投影就是原代数中的 $q_\pm$；未借用双对偶支撑。特别 $\tau(q_\pm)=\tau(S)<1$。

若 $Q\ge q_+,q_-$，则 $QW_\pm=W_\pm$。相加给 $Qc=c$，右乘 $c_S^{-1}$ 得 $S\le Q$；相减给 $Qtc=tc$，再右乘 $c_S^{-1}$ 得 $(1-Q)tS=0$。由 (39.5)，$Q=1$。若只有一个完整 $W_\pm\in QAQ$，则 $QH=H$，乘 $H^{-1}$ 同样得 $S\le Q$，该标签式随即给 $(1-Q)tS=0$，仍有 $Q=1$。取自伴实虚部说明对应原外输入整对也不属于任何真角。各自的左值域投影虽小，却不提供完整标签的双侧承载。

三份副本已经在 $M_{3^N}$ 中存在：$S$ 的矩阵秩为 $2$，而 $6\le3^N$，可在其补投影中再取两个相互正交的秩二投影。有限矩阵部分等距使它们各与完整 $S$ 等价。这支付三份实际副本容量，却不改变原来放置的 $tS=b$。

最后逐类核对完整 $\mathsf H_A(D)$。验证对任意正泛函成立，故适用于任意已给分离且准确决定锥的原评价族，保留其全部标签与质量；也可取全部正泛函为该族。对 $D=K_1$，有向二表是 $(\gamma(x_i x_j))_{i,j=1}^2$ 的通常正 Gram，其中 $(x_1,x_2)=(x,y)$；任意复系数的二次值为 $\gamma((\alpha_1x+\alpha_2y)^*(\alpha_1x+\alpha_2y))\ge0$。对 $D=K_{-1}$，二表是其复共轭，仍正。交换原次序同样成立。每份相加三表及全部排列的 A2 实二次型为

$$
\gamma\!\left(\left(\sum_j\alpha_jx_j\right)^2\right)\ge0
\qquad(\alpha_j\in\mathbb R),
$$

指定相加零方向使括号内元素为零。A3 的 $1^2=1$ 及 $0\le x\le\vartheta1\le1\Rightarrow x^2\le x$ 来自同一个原代数的谱演算。

任取原三元组 $(h;x,y)$，令 $z=x+\jmath y$，以全域 $K_\sigma$ 形成原 $v,w$。不要求任何交换或有限阶段前件，直接展开得到

$$
v+\jmath w=\jmath hz,
\qquad
z\pm(v+\jmath w)=(1\pm\jmath h)z,
$$

$$
\begin{aligned}
&(x\pm v)^2+(y\pm w)^2
       +2K_\sigma(x\pm v,y\pm w)\\
&\qquad=(z\pm(v+\jmath w))^*(z\pm(v+\jmath w))
=z^*(1+h^2)z.
\end{aligned}
\tag{39.7}
$$

两式相等，消去平方差正好给 (37.2)。这个符号恒等式对所有实际原输入成立，故覆盖全部有限实幅度、背景、缩放、平移、零、重复，以及每次由实际内外值再次形成的嵌套调用。每个原评价读取相同元素等式，包含全部原质量和非正常评价；无质量除法，也没有只核对一张 P2 表。定理得证。∎

有限截断 $b_m=\sum_{n\le m}2^{-n}v_n$、$t_m=b_m+b_m^*$ 属于实际有限阶段，并有真承载投影

$$
Q_m=S+\sum_{n\le m}r_n,\qquad
\tau(Q_m)<\tau(S)+\delta<1.
\tag{39.8}
$$

这些投影可按 §38.2 扩大为真偶承载投影，而极限 $t$ 不存在这样的真承载投影。范数收敛只用于已知元素、乘法、迹和条件期望；没有从 $t_m\to t$ 向未知 $D$ 传递任何响应。

定理 39.1 反驳的是“小支撑加各自闭值域加三份容量自动支付原标签真角安置”的推断。它的 $s,E_+,E_-$ 本来全为零，且全域 $D$ 就是标准量子响应；因此它不是非零余量的完整原公理反模型，也不反驳一般混合行最终刚性的可能性。

## 40. 局部几何、准确量子对应及完整来源边界

### 40.1 已有 R5 几何在实际 Pauli 块上的参数对应

这里 R5 指[《有向面积与三元返回》§12](https://github.com/the-omega-institute/trureturing/blob/aef46ce7497cf8ee6bef9bb7356a4483f3bfe6f0/docs/develop/theory/AURIC_R5_022_ORIENTED_AREA_AND_TERNARY_RETURN.md)，直接身份为 `aef46ce7497cf8ee6bef9bb7356a4483f3bfe6f0`。其定义 12.1、定理 12.2 已给：任意实 $V$ 上的非零交替双线性 $D:V^2\to V$ 若对整个原 $V$ 满足

$$
D(D(a,b),d)\in\operatorname{span}_{\mathbb R}\{a,b\},
\qquad
D(a,D(a,b))\in\mathbb R D(a,b)\Rightarrow D(a,b)=0,
\tag{40.1}
$$

则整个原 $V$ 三维，$g_D(a,b)=-\tfrac12\operatorname{Tr}_V(L_aL_b)$ 正定，并有精确返回和叉积描述。这个现成结果的双线性、交替性、非零性、同域闭合及两个全域条件都须支付；不从它倒推本卷一般任意总 $D$ 的双线性。

具体地，在一个已经整体分类的实际 $C=PAP$ 内，取实际 Pauli 矩阵子代数 $B\cong M_2(\mathbb C)$，单位为 $Q\le P$。它可以由 §28 的实际等价谱格通道产生；$B$ 只是实际子代数，不把较大的整个 $QAQ$ 偷换成二阶矩阵代数。选通常 Pauli 轴 $\tau_1,\tau_2,\tau_3\in B$，记

$$
\rho(a)=\sum_{j=1}^3a_j\tau_j,\qquad
V=B_{\rm sa}\cap\ker\operatorname{Tr}_2,
\qquad a\in\mathbb R^3.
$$

整个 $C$ 的分类在 $B$ 上逐值给

$$
\rho(a)\circ\rho(b)=(a\cdot b)Q,
\qquad
D(\rho(a),\rho(b))=-\sigma\rho(a\times b).
\tag{40.2}
$$

因此同一个原 $D$ 在 $V$ 上非零、闭合、交替双线性。其二次返回为

$$
D(D(\rho(a),\rho(b)),\rho(d))
=\rho\bigl((a\cdot d)b-(b\cdot d)a\bigr),
$$

故 P 成立。若 $w=D(\rho(a),\rho(b))\ne0$，则 $w$ 与 $\rho(a)$ 正交且后者非零，$D(\rho(a),w)$ 非零且与 $w$ 正交，因而不在 $\mathbb Rw$，故 N 成立。行算符在此参数下为 $L_{\rho(a)}=-\sigma(a\times\cdot)$，准确有

$$
g_D(\rho(a),\rho(b))=a\cdot b.
\tag{40.3}
$$

这支付 R5 §12 的每个前件，直接复用其局部几何和 §12.8 的 Pauli/Born 消费者；不另作包装定理或重复叉积分类。这里的简化是：在上述实际 Pauli 块的全部旧响应已识别后，局部取向可看成同一把尺上的两个手性，二次返回不依赖手性；§37 则在原外标签上把普通取向解释成右平方或左平方，二者由同一次 PB 比较。前者描述已付局部三维关系，后者消费实际环境中的两份原调用，量词不同。

还须保持复乘法约定。R5 §4 使用 $\circ+iD$，本卷及 AH 使用 $\star_F=\circ-iD$；在同一已识别块上

$$
\star_{\rm R5}=\circ+iD=(\star_F)^{\rm op},\qquad
x\star_F y=\begin{cases}xy,&\sigma=1,\\yx,&\sigma=-1.\end{cases}
\tag{40.4}
$$

两者有同一 Jordan 平方、伴随、准确正锥、范数与实评价；普通乘法和相反乘法的身份不能因同一 Born 配对而混淆。

全 $A_{\rm sa}$ 保留中央单位，且一般环境还可含高阶块，不能直接当作 R5 的这个无中心三维 $V$；一般 $\Omega$ 也没有自动得到同一实线性域及全域 P、N。已付 $D(\mu1,b)=0$ 不提供一般输入可加性。相对单位 $P\ne1$ 的混合行另有位置依赖：即使全域标准 $K_\sigma$，也准确有

$$
K_\sigma(c+\lambda P,t)
=K_\sigma(c,t)+\lambda K_\sigma(P,t).
\tag{40.5}
$$

故 $[P,t]\ne0$ 时不能使用未经修正的局部单位平移中性。若要在未知行之间运输，须另证保留标签的修正余量身份，例如比较 $D(c+\lambda P,t)-K_\sigma(c+\lambda P,t)$ 与 $D(c,t)-K_\sigma(c,t)$；这里未从完整 PB 推出这样的运输式，也不将它增加为公理。

### 40.2 与通常量子代数和原 Born 菜单的准确关系

定理 37.3 识别的完整原行具有

$$
S(c,t)-iD(c,t)=\begin{cases}ct,&\sigma=1,\\tc,&\sigma=-1.\end{cases}
\tag{40.6}
$$

在整个已分类实际角上，AH64.1、75.1 的既有消费者给 $S-iD$ 的复线性延拓为通常或相反 $C^*$-乘法，保留伴随、准确正锥、原单位和范数；全部有限角内旧复 Gram 正。每份原限制评价有数学 GNS，循环向量平方范数准确为 $\gamma(P)$，零角质量给零向量。单行识别不提供未知整个环境的双线性、结合乘法或全部有限旧复 Gram。

在 (40.2) 的实际 Pauli 块上，若 $m=\gamma(Q)>0$，同一原评价的限制唯一写成

$$
\gamma(\alpha Q+\rho(a))=m(\alpha+r\cdot a),\qquad |r|\le1.
$$

对 $|n|=1$ 的数学二元效果 $p_n=(Q+\rho(n))/2$，其未归一原质量准确为

$$
\gamma(p_n)=m\frac{1+r\cdot n}{2}.
\tag{40.7}
$$

正线性读出、Bloch 球、Pauli 密度矩阵和平方半角形式直接复用 R5 §4、§12.8；不新作 Born 定理。$m=0$ 时整个限制为零，不定义 $r$、不作除法。只有这些效果确为原事件绑定的实际完整角菜单，并有原真实条件化时，$\gamma(p_n)/\gamma(Q)$ 才是相应原条件概率。数学正泛函、谱格、GNS 和 Pauli 表示不制造实际准备或实际菜单。

同样，局部数学酉旋转不等于已供应物理门，数学投影夹心的 CP 不指定原仪器的唯一更新；复合正锥、真正相关联合、完整参考、原成功及失败记录的共同质量预算仍需其自身来源。Alfsen–Shultz，[*Orientation in operator algebras*](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/)，Dynamical Correspondences、Theorem 1 的成熟相容乘法对应要求到 skew order derivations 的线性映射，不能为未知总 $D$ 补上线性或物理时间。

### 40.3 完全不变的递归全文物理来源谓词

**定义 40.1（与定义 36.1 完全相同的全文谓词）。** 本增补的完整物理来源谓词 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$ **就是定义 36.1 的同一个谓词**。这里 $S$ 在谓词参数中仍指原对称响应；谱支撑投影 $S$ 不替换这个参数。严格沿

$$
36.1\ \Longrightarrow\ 32.3\ \Longrightarrow\ \S27.1
\ \Longrightarrow\ 26.3\ \Longrightarrow\ 22.3\ \Longrightarrow\ 18.2
\ \Longrightarrow\ \{10.2,15.2,\mathrm{AH}28.1,64.2,75.1\}
\ \Longrightarrow\ \mathrm{SQ}47.1\text{--}47.13
$$

的全文身份关系，将其中**每份定义、合同、公式、量词及逐项递归纳入、逐层固定版本的全部上游全文，逐句、逐公式、逐量词同时合取**。箭头表示原定义的完整纳入，不是另造较短谓词，也不是只保留编号范围；以下范围说明不替代任何被纳入全文或原前件。

AH 的直接身份保持 `b1a95e41b9622e9f720e51f9bb899841f5b74ca1`；W、CC、PT 的原直接身份保持 `3b10aed60f60e4901bae6cf2e160bf439d642e64`。SQ 主源仍按自身 1.3、39、41.1、47.1 解析，`dcaebc0b9ca5a3a463fd8cfd161d38967df28668` 与 `0aa11dbc3dc337d667b98900673e07d67b99bf46` 保持各自层级。OP/PT/PB/SM/C/AQ/R3/W/FR/XV/SF 的 `f24d1138a7b994da16abd9a47affedea64ea44ce`、AH22.1 保留的 `2addd6f369b7387226c2b0cc984623dd3efe40a1`、AH12.1 上游 `39a0505470ea889dd9d4301ad60cd9506a5e8b58`，以及 AH42.1 中 OP 等直接身份 `bef9bba367a24ab5e250491dcb88ed85ebc29cf7` 全部保持。R5 的直接读取身份不覆盖这些内层身份。原根、全部静默和其他静态分支不改为 UHF 或三维 Pauli 对象。

同一 $\Omega/\mathrm{native}$ 中的原对象、准备、事件、设备、程序／过程、比较权 $q$、跨标签全词共同 $K/J$、parent、ready、合法控制、旗标、原中心、经典及不等维块、无轴对象、每个中间切口和全部模式网络均保留全文身份。网络中的 $D_{\rm network}$ 不是本响应 $D$；网络中的 $C$ 不是数学正锥。原根类、十一端点、所有配置、实际逆等距边、全静默 ready、零活动、终端标签及原读器合同均不被数学矩阵取代。未定义请求不补成零箭头。

实际准备、相干控制、原事件绑定的实际完整 Born 菜单及全部原质量保留各自来源。对实际全局菜单 $\sum_j e_j=1$，只有 $\gamma(1)>0$ 才以 $\gamma(e_j)/\gamma(1)$ 归一；角菜单 $\sum_j e_j=P$ 另需原真实条件化及 $\gamma(P)>0$。零、不等、次归一和非正常质量均保留。真正相关联合与张量仍须同一实际共同来源、全部相关输入、忠实同向交换腿、共同生成、分离及所需重数；相同边缘、分别可达、数学谱格、等价投影和 GNS 不代付共同实现。

typed CP、箭头下降、整台递归同源参考、原真支持与支持内补、交织夹界、全部所需有限深度及每个正精度保留全部原前件。完整仪器、TP、Kraus、更新和 Lüders 仍须完整 typed 菜单、完整单位分区、接受端、校准、表示及收敛条件，量化**整个环境、全部成功／失败／细记录／port／post-port 输出，以及每份完整输出的每个仍合法未来**。只有严格正的实际输出质量可归一，失败和零分支不删除；局部角或数个谱格不替代任何一份完整输出。

合法顺序、自适应与并行历史、真正分组遗忘、停止、拒绝、销毁、泄漏、同数两侧及逆向真实 Return、完整 CountRead 的活动 ready 与 producer 全部保留。相同算子、当前读数或纤维像不合并不同原程序、历史、记录、读取次序、原 $q$ 零集或未来权限。正常性、指定前对偶、无限菜单与记录的可数可加及收敛仍须原扩展来源。物理动力学仍须保持原域的实际连续可逆流及实际逆、物理钟与单位、适用酉实现、一般生成元域、Hamiltonian 能量解释、作用量及共同正的物理 $\hbar$。数学迹尺、局部旋转角、有限幅度、条件期望、范数收敛和代数尺度都不生产这些物理来源，也不证明整个谓词的满足性。

### 40.4 数学归属及两笔独立未付条件

本增补的 $\texttt{repo-derived}$ 数学差额是两份完整原外调用的普通符号联合消费者，以及在全域标准 $D$、完整 $\mathsf H_A(D)$ 中对自动真角安置的准确反例。前者不要求预先匹配两个符号，适用于一般支撑交换块余量；后者保留实际小支撑、各自闭值域和三份容量，却排除原标签的所有真承载角。两者不构成一般混合行分类或非零余量的完整原公理反模型。

有限谱函数演算、部分等距、投影等价、近投影酉共轭和 UHF 归纳模型是成熟工具，归于 Blackadar，[*Operator Algebras*](https://bruceblackadar.com/Mathematics/Cycr.pdf)，II.2.3.1–5、II.3.3.4–5、II.8.2.2(iv)；近投影酉共轭的准确地址为 II.3.3.5。忠实迹和有限级偏迹直接复用 AH67.1，标准对角期望的所需性质已在 §39 的实际构造中给出。角继承、偶维分类、共同取向及全单位行分别复用 W119–120、AH70–72 和 PT183–185；R5 §12 的三维入口及其 Pauli/Born 消费者只在 §40.1 已支付的局部域上使用。承载等价、偶化、闭值域公式、矩阵秩匹配及 R5 参数代入均不另计为新基础定理。不主张文献穷尽、历史优先权、外部开放问题解决、独立公理数减少或完整量子起源。

两笔原义务仍各自保留：

1. 在一般环境输入上，若没有取得两份完整原调用的普通响应 (37.9)，首个一般混合行关系仍是原 (31.1) 的 **$E_+=E_-$**。原 (31.2) 将它准确等同于 $s=0$；在定理 30.1 的范围内又等同于全部非零谱格的 $\rho_i=0$。§37 给足以消去它的条件，§39 否定自动真角安置这一供应路线，却没有从完整 $\mathsf H_A(D)$ 普遍支付普通响应。重新放置等价投影、抽象矩阵单位、改造标签或有限阶段近似都还需要准确的新旧原响应运输；不能以原位置之外的调用替代 (37.5)。
2. §36.3 的独立定量义务不变：定理 33.2 只给近相反谱对、固定 $|\lambda|\ge\lambda_*>0$ 的 $\omega_{M,\lambda_*}(\varepsilon)\to0$，没有显式率，不能据此推出增长分割中的 $N\omega_{M,\lambda_*}(\varepsilon)^2\to0$，也不能借用其他误差的 $N\kappa^2\to0$。定理 28.2 的一般相异谱值精确结论不自动给任意 $a\ne b$ 的近似模数。精确符号消费者和载体反例都没有支付这笔可累加性义务。

非零相对标量演员 $c=aP$ 的未覆盖混合输入、无限谱演员、一般混合整行、从这些行接回完整奇数阶段 UHF 全域分类，以及完整量子起源和整个物理来源谓词的满足性，均保留原目标。全局 $P=1$ 的标量行已由 PT183.2 关闭，不能再次报为未解。$c=0$ 及前文已识别输入族保持各自完整原范围。

### 40.5 完整直观

把原演员的非零谱支撑想成已经放好的几间带刻度的房，环境操作可以把房中的东西送到外面；同一次 PB 形成的两张原标签必须按原来的摆放读取，不能换成搬到方便位置后的新标签。每张标签的右侧都落在原房间中，而普通量子响应的两个取向分别把原平方读成右平方或左平方。两次都与原取向同号时，已有的分类直接消去余量；两次符号不同，平方相等便把一张标签的右侧限制传到另一张的左侧，正平方为零排除外面的连线，使环境返回已认识的角；两次都反号时，相等先把整块余量锁到 $c^2$ 的交换子上，逐个非零刻度读取就消去所有块余量，再用有限谱多项式认回原支撑，返回也随之成立。因此不用事先把两个角和两个方向匹配好，但仍必须真正知道两个完整原调用各有普通响应。小房间和充足空间不能提供这份证据：三进 UHF 中可让总迹很小的、互相分离的落点遍布整个补空间，每一步都在实际有限矩阵里精确匹配，范数极限后却没有任何非零实际投影能完整避开它们。于是两张标签各自都有良好的实际闭值域，三份完整房间也放得下，完整原标签仍装不进任何真角；这个例子本身已经使用全域标准量子响应，否定的是自动安置路线，不是否定一般原关系最终能约束响应。已经识别的实际 Pauli 块则有更简洁的图景：二次作用返回原两轴平面，非零响应不能再次塌回自己的直线，R5 的既有结果用同一关系读出一把正尺，两个取向就是这把尺上的两个手性；这一局部三维图景不能吞掉中央单位、更高阶环境或全部历史。全局单位行早已为零，相对房间单位却会与通往外面的环境输入产生标准交换子，因而不能把局部单位平移当作免费中性。所得通常或相反乘法、正性与数学 Hilbert/Born 表示都守住已识别范围；一般两份原缺陷为何相等，以及许多近似谱格的误差怎样累加，仍是两笔不同的问题。真实准备、完整 Born 菜单、同一共同相关来源、整台仪器全部输出和每个合法未来、Return、CountRead、正常性、指定前对偶、物理钟、动力学及共同正 $\hbar$，继续由同一个完整递归来源谓词逐项承担，没有因局部几何更短而消失。

## 追加锚（本行以下为增补区）
## 41. 两份有限探针对分离背景非对角输入的固定输出刚性

### 41.1 原完整问题与较弱的固定输出接口

原全域问题保持定义 6.1、28.1、37.1 的同一个完整 $\mathsf H_A(D)$，包括全部递归固定引文、同一 $\Omega/\mathrm{native}$、原域 $E=A_{\rm sa}$、原对称响应 $S(x,y)=x\circ y=(xy+yx)/2$、单位 $1$、范数及准确锥 $A_+$。原评价族 $\mathcal P$ 仍分离 $E$ 并准确决定锥；全部原评价标签及质量 $\gamma(1)$ 保留，包括零、不等、次归一和原表示意义下的非正常评价。全部有向 A1/P2、两种次序、A2 的相加三表及全部排列与指定零方向、同一有理 $0<\vartheta\le1$ 下的 A3，以及每个实际三元组和全部实际嵌套调用的完整 PB 均不改动。未知量仍为同一个任意总映射 $D:E^2\to E$，不增加输入连续性、可加性、齐次性、可测性、协变性、压缩自然性、商下降、双对偶延拓或有限阶段输出闭合。

以下另取只有固定元素和标量不等式的较弱接口。它不是完整 $\mathsf H_A(D)$ 的重定义，也不把所求整行作为新前件。新推断是这个接口中的有限充分性，不是原返回输入的再次分类。

**定义 41.1（全部实际探针的固定输出预算）。** 设 $A$ 为含单位复 $C^*$-代数，$P$ 为实际投影，$C=PAP$。取非零正交投影 $p,q\le P$，并置

$$
S=p+q,\qquad c=p+2q,\qquad
K_\sigma(u,v)=\frac{\sigma i}{2}[u,v],\qquad \sigma\in\{1,-1\}.
\tag{41.1}
$$

这里的 $S$ 是谱支撑投影，不替换原对称响应或物理来源谓词的同名字母。取实际自伴 $t\in A$ 及一般自伴块余量

$$
s=s_p+s_q,\qquad s_p=s_p^*\in pAp,\quad s_q=s_q^*\in qAq,
\qquad g=K_\sigma(c,t)+s.
\tag{41.2}
$$

不要求 $p\sim q$，也不要求 $s_p,s_q$ 为标量。对任一实际 $x=x^*\in C$，准确沿用 §33.1 的标签

$$
\begin{gathered}
h=K_\sigma(c,x),\qquad r=c\circ x,\qquad k=c\circ t,\\
R_+=x+h-k,\qquad R_-=x-h+k,\\
S_+=t+r+g,\qquad S_-=t-r-g,\\
L=-2x\circ(h-k)-2t\circ(r+g).
\end{gathered}
\tag{41.3}
$$

对每个数学正泛函 $\phi$，令

$$
B_\phi(U,V)=\phi(U^2)\phi(V^2)-\phi(U\circ V)^2\ge0
\qquad(U=U^*,\ V=V^*).
\tag{41.4}
$$

非负性是已知乘法所给实半内积 $\phi(U\circ V)$ 的 Cauchy–Schwarz 不等式。所有数学正泛函均在量词内，包括零泛函和任意非负质量，且不要求正常性；没有质量归一。固定二表条件为 §33.1 的同一个

$$
\mathsf{P2}(c,t;g):\qquad
\phi(g)^2\le B_\phi(c,t)\qquad(\phi\ge0).
\tag{41.5}
$$

给定探针 $x$ 的显式 PB 预算为

$$
|\phi(L)|\le
\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}
\qquad(\phi\ge0).
\tag{41.6}
$$

“全部探针类”要求 (41.5) 及每个实际 $x\in C_{\rm sa}$ 的 (41.6)。这个类只携带 $c,t,g$、已知乘法及上述标量不等式；不携带任何响应映射、任何已知外值或以 $t$ 为演员的 PB。对实际完整 $\mathsf H_A(D)$ 数据，若整个实际 $C$ 已按 (28.3) 同号分类，取 $g=D(c,t)$，则 AH43.1 的同表数学正读取给 (41.5)，原 $\operatorname{PB}(c;x,t)$ 和两份实际外层 P2 给 (41.6)。正读取由原评价准确决定锥支付，如 (28.9) 前的二表二次型所示；它不增添原物理评价标签或准备。

定义 33.1 只保留了 $x=Te+\alpha n$ 与 $x=Tj+\alpha n$ 两个大伴轴族。本节的全部探针类在探针量词上另有要求；下述依赖 $s_p,s_q$ 的探针不保证属于那两个轴族，不能把 §33 的两族预算直接当成对任意 $x$ 的现成假设。本节也不使用其近相反谱前件、范数上界或稳定性模数。

### 41.2 两个明确斜率的有限充分定理

**定理 41.2（一般块余量的两探针消去）。** 保持 (41.1)–(41.5)，另要求原输入准确具有形状

$$
t=\tau+b,\qquad \tau=ptq+qtp,\qquad
b=b^*=(1-S)b(1-S).
\tag{41.7}
$$

即 $ptp=qtq=0$，且 $S$ 与 $1-S$ 之间没有连线；整个补块 $b$ 任意。置

$$
d_\pm=\frac{1\pm\sqrt{10}}3,\qquad
v=K_\sigma(c,\tau),\qquad
u_d=\frac{v}{d-3/2},\qquad
z_d=\frac{s_p}{d-1}+\frac{s_q}{d-2},\qquad
x_d=u_d+z_d\quad(d=d_+,d_-).
\tag{41.8}
$$

若仅在这两份实际探针 $x_{d_+},x_{d_-}$ 上，对全部数学正泛函成立 (41.6)，则

$$
\boxed{s=0,\qquad g=K_\sigma(c,t).}
\tag{41.9}
$$

因此全部探针类在 (41.7) 上具有该刚性。这里不要求通道可逆、满支撑或有稠密值域，也不要求任一余量块交换于其整个角。投影等价在此受限定理中不需要；这不删除原全域目标中其他定理的匹配前件。

**证明。** 两个 $d$ 是 $3d^2-2d-3=0$ 的不同实根。将 $0,1,3/2,2$ 逐一代入，该多项式的值分别为 $-3,-2,3/4,5$，均非零，故 (41.8) 所有分母非零。根关系给

$$
d-\frac1d=\frac23,\qquad
(d-3/2)\left(3/2+\frac1d\right)=-\frac14.
\tag{41.10}
$$

$v,u_d,z_d,x_d$ 均为原代数中的实际自伴元素，且支撑在 $S$，从而 $x_d\in C_{\rm sa}$。每份固定数据的探针范数有限；不要求对全部数据有统一范数界。探针依赖同一固定余量，合法性由“对全部实际 $x$”的量词保证，不是先规定一份与数据无关的探针。

写 $T=p\tau q$，则 $\tau=T+T^*$、$T\in pAq$，且

$$
v=\frac{\sigma i}{2}(-T+T^*),\qquad
c\circ\tau=\frac32\tau,\qquad
K_\sigma(c,v)=-\frac14\tau,\qquad
\tau\circ v=0.
\tag{41.11}
$$

前三式由 $cT=T$、$Tc=2T$ 及其伴随直接得出。最后一式由 $T^2=(T^*)^2=0$ 展开即得，也等于 $\sigma i[c,\tau^2]/4=0$。这些恒等式同时覆盖两个 $\sigma$。由于 $cb=bc=0$，原输入并未改动而有

$$
k=\frac32\tau,\qquad K_\sigma(c,t)=v,\qquad g=v+s.
\tag{41.12}
$$

固定一个根 $d$，在原标签 (41.3) 中取 $x=x_d$。$z_d$ 与 $c$ 交换，因此 (41.10)–(41.12) 给

$$
\begin{aligned}
h-k
&=-\frac{\tau}{4(d-3/2)}-\frac32\tau=\frac{\tau}{d},\\
r+g
&=\frac32u_d+cz_d+v+s=d(u_d+z_d)=dx_d.
\end{aligned}
\tag{41.13}
$$

第二式逐块使用 $cz_d+s=dz_d$ 和 $v=(d-3/2)u_d$。因而两对完整原标签准确为

$$
\begin{aligned}
R_+&=x_d+\tau/d,& S_+&=b+dR_+,\\
R_-&=x_d-\tau/d,& S_-&=b-dR_-.
\end{aligned}
\tag{41.14}
$$

这没有删去 $t$ 中的背景：$b$ 仍在两个 $S$ 标签中。$R_\pm=SR_\pm S$，所以 $bR_\pm=R_\pm b=0$。

对任意数学正泛函 $\psi$，定义另一份被 (41.5)–(41.6) 量词允许的数学正读取

$$
\phi_S(a)=\psi(SaS).
\tag{41.15}
$$

其正性来自 $SaS\ge0$ 对 $a\ge0$ 成立；质量为 $\psi(S)$，允许为零。由 (41.14) 的实际乘法，

$$
\begin{gathered}
\phi_S(S_\pm^2)=d^2\phi_S(R_\pm^2),\\
\phi_S(R_+\circ S_+)=d\phi_S(R_+^2),\qquad
\phi_S(R_-\circ S_-)=-d\phi_S(R_-^2),\\
B_{\phi_S}(R_+,S_+)=B_{\phi_S}(R_-,S_-)=0.
\end{gathered}
\tag{41.16}
$$

补块平方 $b^2$ 被 $S$ 的数学读取消去，零质量与退化 Gram 无须另作除法。

另一方面，$bx_d=x_db=0$，(41.11)、(41.13) 给完整右端

$$
L=-2(d+d^{-1})x_d\circ\tau
=-2(d+d^{-1})z_d\circ\tau\in SAS.
\tag{41.17}
$$

在 (41.6) 中使用 (41.15)，由 (41.16) 得 $\psi(L)=\phi_S(L)=0$。所有正泛函分离自伴元素，故 $L=0$。实数 $d\ne0$ 满足 $d+d^{-1}\ne0$，于是

$$
z_d\circ\tau=0\qquad(d=d_+,d_-).
\tag{41.18}
$$

这是两条关系，不是在同一条关系中取消未知通道。令 $A_0=s_pT$、$B_0=Ts_q$，读取 (41.18) 的 $p,q$ 块并乘以非零标量分母，得到

$$
(d-2)A_0+(d-1)B_0=0\qquad(d=d_+,d_-).
\tag{41.19}
$$

两式相减并除以非零实数 $d_+-d_-$，给 $A_0+B_0=0$；回代任一式给 $-A_0=0$，从而 $A_0=B_0=0$。取伴随还得 $T^*s_p=s_qT^*=0$，所以

$$
s\tau=\tau s=0,\qquad st=ts=0.
\tag{41.20}
$$

这里只取消非零实数，从未取消 $T$。因此即使 $T=0$ 或具有零通道，推断仍成立；但 (41.20) 本身尚未排除落在零通道上的余量。

最后使用全部正泛函的原固定 P2。由 $[c,s]=0$、$st=ts=0$，有 $vs=sv=0$。对任意数学正泛函 $\psi$ 定义

$$
\phi_s(a)=\psi(sas).
\tag{41.21}
$$

$s=s^*$ 保证它为正，质量 $\psi(s^2)$ 允许为零。直接得到

$$
\phi_s(t^2)=0,\qquad \phi_s(c\circ t)=0,
\qquad B_{\phi_s}(c,t)=0.
\tag{41.22}
$$

(41.5) 遂给实数 $\phi_s(g)=0$，即

$$
0=\psi(sgs)=\psi(s^3)\qquad(\psi\ge0).
\tag{41.23}
$$

$s^3$ 自伴，分离性给 $s^3=0$，继而 $s^4=0$。两次 $C^*$-恒等式给 $\|s^2\|^2=\|s^4\|=0$ 及 $\|s\|^2=\|s^2\|=0$，故 $s=0$。这同时消去全部零通道余量。证明没有使用任何极限、响应映射或压缩未知响应的操作。∎

### 41.3 尖锐 P2 区间和三维分离背景的一探针消费者

**命题 41.3（任一斜率均排除非零平衡标量余量）。** 取定理 34.1 在 $a=1,b=2,v=1$ 的整个固定系数族，以 $\varrho$ 表示该定理的标量参数 $r$，避免与探针标签 $r=c\circ x$ 混淆：

$$
c_0=\begin{pmatrix}1&0\\0&2\end{pmatrix},\quad
\tau_0=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
s_0=\begin{pmatrix}\varrho&0\\0&-2\varrho\end{pmatrix},\quad
g_0=K_\sigma(c_0,\tau_0)+s_0.
\tag{41.24}
$$

已有定理 34.1 准确供应

$$
\mathsf{P2}(c_0,\tau_0;g_0)
\quad\Longleftrightarrow\quad
|\varrho|\le\frac{2\sqrt2}{3}.
\tag{41.25}
$$

对该闭区间中的每个 $\varrho\ne0$，仅用 $d=d_+$ 或仅用 $d=d_-$ 的一份 (41.8) 探针，(41.6) 就已失败。这个结论还适用于命题 35.1 的实际 $M_3$ 数据 $c=c_0\oplus0$、$t=\tau_0\oplus\beta$、$s=s_0\oplus0$，其中 $\beta\ne0$、$\varrho=1/2$，背景保持原值。

**证明。** 不重证 (41.25) 的尖锐区间及端点证书。对任一根 $d$，探针准确为

$$
x_d=\begin{pmatrix}
\dfrac{\varrho}{d-1}&\dfrac{-\sigma i}{2(d-3/2)}\\[3pt]
\dfrac{\sigma i}{2(d-3/2)}&\dfrac{-2\varrho}{d-2}
\end{pmatrix}.
\tag{41.26}
$$

由 (41.14)、(41.17) 的已付乘法，得到

$$
S_+=dR_+,\qquad S_-=-dR_-,\qquad
L=\frac{\varrho(d^2+1)}{(d-1)(d-2)}\,\tau_0.
\tag{41.27}
$$

因此两笔 Gram 预算对每个正泛函都为零。单位向量 $\xi=(1,1)/\sqrt2$ 的正泛函满足 $\phi(\tau_0)=1$；(41.27) 的系数对 $\varrho\ne0$ 非零，故其 (41.6) 左边严格正，右边为零。结论覆盖两种 $\sigma$ 及 (41.25) 的全部非零点，包括端点。

对命题 35.1，使用实际探针 $x_d\oplus0$ 和向量 $(1,1,0)/\sqrt2$。完整标签是 $R_\pm=(R_\pm)_0\oplus0$、$S_+=d(R_+)_0\oplus\beta$、$S_-=-d(R_-)_0\oplus\beta$；完整右端是 (41.27) 的 $L\oplus0$。第三维背景没有从 $t$ 或任一 $S$ 标签中删去，但该支持在前两维的正读取使两笔 Gram 恰为零，仍有相同矛盾。命题 35.1 已支付这份非零背景数据的全部正泛函 P2，不以忽略第三维代替它的正性。∎

命题 35.1 已通过原 $\operatorname{PB}(t;c,0)$ 和整个已分类角的两份已知外值证明非延拓。这里的消费者准确加强为：上述数据连只有 $c,t,g$ 的较弱固定输出预算也不能满足；既不新作 P2 例子，也不将它称作完整 $\mathsf H_A(D)$ 的反模型。一般块余量需要两条独立加权关系；这里的平衡标量约束预先关联了两块，才使任一探针单独足够。

### 41.4 最强既有复用、实际差额与未覆盖输入

在原已分类角及完整 $\mathsf H_A(D)$ 的设置中，(41.7) 给 $tS=\tau\in C$，故 $(1-P)tS=0$。原定理 31.2 的返回消费者早已支付这类整行：$k,g,c\pm g$ 都在 $C$，原 $\operatorname{PB}(t;c,0)$ 的两份外响应由角分类已知，(31.2) 给 $2cs=0$ 并消去 $s$。在原等价谱格的设置中，定理 29.1 所需匹配也已支付。因此本节不把“分离背景的返回输入在完整 H 下刚性”重报为新行分类；§37 的普通外响应消费者也不是这里重新证明的对象。

真正的前件差额是：定理 41.2 不给任何 $D$，不预给两份外响应的值，不使用以 $t$ 为演员的 PB；只从一份固定 P2 和两份明确 $c$-演员预算推出 $s=0$。原定理 31.2 的全 H 前件不能直接应用于这个较弱接口；两份零面积读数、两条权重不同的算子关系和最终 P2 零通道读取支付了缺失推断。定理 41.2 是有限充分性命题，不声称两份探针在所有数据中最少，也不声称存在与全部固定输出预算相容而不能延拓为某个完整映射的数据。

(41.7) 是实质限制。对较弱固定输出类，含 $ptp\ne0$ 或 $qtq\ne0$ 的输入，以及带 $(1-S)tS\ne0$ 真连线的输入，均未由本证明覆盖；此时 (41.13)–(41.14) 的精确比例没有得到支付。完整 H 中已经满足 §31.2 返回条件的对角输入仍直接复用旧结果，不因较弱接口的缺口重新列为全 H 未解。

$b$ 可以有任意范数和谱，也可包含 $P-S$ 与 $1-P$ 之间的自伴耦合；禁止的是从 $S$ 接向整个 $1-S$ 的连线。故允许 $t\notin PAP$，但这不等于允许真正从非零谱支撑通向角外的环境耦合。即使 $PAP=M_2(\mathbb C)\subseteq A$，一般 $t$ 的角内对角项及通向 $1-P$ 的连线也未被删除。若整个 $A=M_2(\mathbb C)$，本节只处理相对 $c=\operatorname{diag}(1,2)$ 的零对角 $t$；已有有限维全 H 分类不补给缺少 $D$ 的较弱类以任意输入结论。

一般全 H 混合输入的首个未付关系仍准确是 (31.1) 的

$$
\begin{gathered}
E_+=D(c-g,k)-K_\sigma(c-g,k),\qquad
E_-=D(c+g,-k)-K_\sigma(c+g,-k),\qquad k=c\circ t,\\
E_+=E_-,\qquad E_+-E_-=2cs.
\end{gathered}
\tag{41.28}
$$

在原有限谱余量接口下，所求相等当且仅当 $s=0$；定理 30.1 的逐格标量范围中又等价于全部非零谱格 $\rho_i=0$。这里没有把 (41.28) 的相等增为公理。原 §39 的真角安置障碍也保持原结论，不能以重放等价投影或有限阶段近似改造这些原标签。

§36.3、40.4 的独立定量义务不变：定理 33.2 的 $\omega_{M,\lambda_*}(\varepsilon)\to0$ 没有显式率，不能据此支付增长有限分割中的 $N\omega_{M,\lambda_*}(\varepsilon)^2\to0$，也不能借用其他误差的 $N\kappa^2\to0$。本节有限而精确的两探针证明没有提供这类误差累加界。一般任意输入的固定输出刚性、一般全 H 混合整行、无限谱演员、非零相对标量演员的未覆盖混合输入、接回完整奇数阶段 UHF 全域分类，以及完整量子起源，均保留原未解目标。

全局单位行 $D(\mu1,b)=0$ 已由 PT183.2、AH43.3 的既有接口支付，如 §37.1 所述，不是这里的剩余条件。它不提供输入可加性；相对单位 $P\ne1$ 的未经修正平移中性也不由它得到，准确标准修正仍是 (40.5) 的 $\lambda K_\sigma(P,t)$。本证明没有使用原始相对单位平移中性、残差缩放不变性、幅度间响应关系或任何未知响应的正则性。

### 41.5 通常／相反行、成熟工具与局部几何的复用

对定理 41.2 的固定三元组，准确有

$$
c\circ t-ig=c\circ t-iK_\sigma(c,t)
=\begin{cases}ct,&\sigma=1,\\tc,&\sigma=-1.\end{cases}
\tag{41.29}
$$

若三元组来自原实际模型，$g=D(c,t)$，这就是同一旧响应的通常或相反乘法行。只有固定三元组时，它不供应响应总映射，更不供应全域双线性、结合乘法、全部有限旧复 Gram 或动力学。整个已经分类的 $C$ 的通常／相反 $C^*$-乘法、伴随、准确锥、原单位范数和数学 GNS，直接复用 §36.1、40.2 所消费的 AH64.1、75.1；每份原限制评价的循环向量平方范数仍准确为 $\gamma(P)$，零角质量仍给零向量。

实际 Pauli 块及 R5 的三维几何只按 §40.1 式 (40.2)–(40.4) 的已付入口使用：R5 定义 12.1、定理 12.2 的非零交替双线性、同域闭合及全部 P、N 前件不删，Pauli/Born 消费者直接复用其 §12.8 与本卷 (40.7)，不另立包装定理或重作分类。R5 的 $\circ+iD$ 与本卷 $\circ-iD$ 在同一已识别块上仍互为相反乘法；同一 Jordan 平方和 Born 配对不抹去这个符号约定。R5 的直接身份仍为 `aef46ce7497cf8ee6bef9bb7356a4483f3bfe6f0`，不覆盖任何内层来源身份。

本节的 $\texttt{repo-derived}$ 差额仅为上述较弱接口中的两探针有限充分性，以及尖锐 P2 族的一探针预算消费者。Peirce 块乘法、实 Gram 与 Cauchy–Schwarz、正泛函分离和 $C^*$-恒等式均为成熟工具：沿定义 10.1、归属 32.1、§36.3，Peirce 术语归于 Hanche-Olsen–Størmer，[*Jordan Operator Algebras*](https://hanche.folk.ntnu.no/joa/joa-m.pdf)，§2.6.2、Lemma 2.6.3；正泛函与表示背景归于其中所引 Gelfand–Naimark、Segal，亦见 Blackadar，[*Operator Algebras*](https://bruceblackadar.com/Mathematics/Cycr.pdf)。本节不将自己的两探针推断归给这些成熟来源，不主张历史优先权、独立外部检索覆盖、穷尽检索或外部开放问题解决，也不把标量泛函二表正性升格为算子二正性。

### 41.6 与定义 40.1、36.1 完全相同的递归全文来源

**定义 41.4（物理来源的同一全文身份）。** 本节所用 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$ **就是定义 40.1（位于 §40.3）及定义 36.1（位于 §36.2）的同一个谓词**，不是另造一个较短谓词。谓词中的 $S$ 仍为原对称响应，不是 (41.1) 的投影。严格沿

$$
40.1\ \Longrightarrow\ 36.1\ \Longrightarrow\ 32.3
\ \Longrightarrow\ \S27.1\ \Longrightarrow\ 26.3
\ \Longrightarrow\ 22.3\ \Longrightarrow\ 18.2
\ \Longrightarrow\ \{10.2,15.2,\mathrm{AH}28.1,64.2,75.1\}
\ \Longrightarrow\ \mathrm{SQ}47.1\text{--}47.13
$$

的全文身份关系，将其中**每份定义、合同、公式、量词及逐项递归纳入、逐层固定版本的全部上游全文，逐句、逐公式、逐量词同时合取**。箭头保持原定义的完整纳入；下列范围说明不替代任何被纳入全文、原前件或量词。

AH 的直接身份保持 `b1a95e41b9622e9f720e51f9bb899841f5b74ca1`；W、CC、PT 的原直接身份保持 `3b10aed60f60e4901bae6cf2e160bf439d642e64`。SQ 主源仍按自身 1.3、39、41.1、47.1 解析，`dcaebc0b9ca5a3a463fd8cfd161d38967df28668` 与 `0aa11dbc3dc337d667b98900673e07d67b99bf46` 保持各自层级。OP/PT/PB/SM/C/AQ/R3/W/FR/XV/SF 的 `f24d1138a7b994da16abd9a47affedea64ea44ce`、AH22.1 保留的 `2addd6f369b7387226c2b0cc984623dd3efe40a1`、AH12.1 上游 `39a0505470ea889dd9d4301ad60cd9506a5e8b58`，以及 AH42.1 中 OP 等直接身份 `bef9bba367a24ab5e250491dcb88ed85ebc29cf7` 全部保持。各内层身份不被直接 AH/W/CC/PT 或 R5 身份压平；原根、全部静默及其他静态分支不改为 UHF 或三维 Pauli 对象。

同一 $\Omega/\mathrm{native}$ 中的原对象、准备、事件、设备、程序／过程、比较权 $q$、跨标签全词共同 $K/J$、parent、ready、合法控制、旗标、原中心、经典及不等维块、无轴对象、每个中间切口和全部模式网络均保持全文身份。网络中的 $D_{\rm network}$ 不是本响应 $D$，网络中的 $C$ 不是数学正锥。原根类、十一端点、所有配置、实际逆等距边、全静默 ready、零活动、终端标签及原读器合同均不由数学矩阵替代；未定义请求不补成零箭头。

实际准备、相干控制、原事件绑定的实际完整 Born 菜单及全部原质量保留各自来源。实际全局菜单 $\sum_j e_j=1$ 只在 $\gamma(1)>0$ 时用 $\gamma(e_j)/\gamma(1)$；角菜单 $\sum_j e_j=P$ 另需原真实条件化及 $\gamma(P)>0$。零、不等、次归一和非正常质量均保留。真正相关联合与张量仍须同一实际共同来源、全部相关输入、忠实同向交换腿、共同生成、分离及所需重数；相同边缘、分别可达、数学谱格、等价投影和 GNS 不代付共同实现。

typed CP、箭头下降、整台递归同源参考、原真支持与支持内补、交织夹界、全部所需有限深度及每个正精度保留全部原前件。完整仪器、TP、Kraus、更新和 Lüders 仍须完整 typed 菜单、完整单位分区、接受端、校准、表示及收敛条件，量化**整个环境、全部成功／失败／细记录／port／post-port 输出，以及每份完整输出的每个仍合法未来**。只有严格正的实际输出质量可归一；失败、零分支及任何完整输出均不删除，数个谱格不替代完整输出。

合法顺序、自适应与并行历史、真正分组遗忘、停止、拒绝、销毁、泄漏、同数两侧及逆向真实 Return、完整 CountRead 的活动 ready 与 producer 全部保留。相同算子、当前读数或纤维像不合并原程序、历史、记录、读取次序、原 $q$ 零集或未来权限。正常性、指定前对偶、无限菜单及记录的可数可加和收敛仍须原扩展来源。物理动力学仍须保持原域的实际连续可逆流及实际逆、物理钟与单位、适用酉实现、一般生成元域、Hamiltonian 能量解释、作用量及共同正的物理 $\hbar$。

(41.15)、(41.21) 仅将既有数学正泛函复合于已知的正夹心映射；它们不压缩未知 $D$、不生产实际准备、条件化或仪器，也不改变任何原质量。两份有限探针、零 Gram、数学迹尺、局部旋转、条件期望、范数和有限幅度都不生产上述物理来源，亦不证明整个谓词的满足性。

### 41.7 两条比例读数与零通道的完整白话

把 $p,q$ 看成刻度为一和二的两间房，把固定答案中的 $s$ 看成仍留在各自房内的误差；每间房可以很复杂，误差不必是一个数，两房之间的通道也可以完全不通。受限定理只让输入在两房之间走动，并允许外面保留任意背景，暂不允许从这两房真正接向外界的连线。简化在于不用继续放大参数或对未知规则取极限，而是选两个明确的实数斜率，根据同一固定误差造出两份实际合法探针；每份探针都让两对原外标签在房内严格成比例，因此两笔 Gram 面积都为零。原预算于是给两条权重不同的误差连线关系，合起来使误差与输入相乘都为零，不需要把通道当成可逆。误差仍可能躲在通道完全不通的地方，所以最后还要用原 P2 通过误差本身作数学读取，才能消去这部分；不能只凭“乘通道为零”就宣布误差消失。已有的两块平衡标量余量只剩一个共同参数，任一斜率便能把所有非零参数排除，三维例子的外部背景也始终留在原输入与标签里。这不是新作一遍完整 H 下的返回分类，而是说明更少的固定答案不等式已经足够；房内对角输入及房间真正接向环境时，这套比例尚未得到，一般两份原缺陷为什么相等仍欠证明，许多近似房间拼接时误差怎样累加则是另一笔独立问题。已经识别的行准确等于通常或相反量子乘法，现成 Pauli、Hilbert 和 Born 对应继续按原入口使用；数学读取没有制造真实准备、完整菜单、共同相关来源、整台仪器全部输出及未来、Return、CountRead、正常性、指定前对偶、物理钟、动力学或共同正 $\hbar$，因而这里没有得到一套完整的新量子公理系统。

## 追加锚（本行以下为增补区）
## 42. 真环境耦合的平衡三维星形输入：零探针的有限正读取刚性

### 42.1 固定原输入、完整标签与预算

**定义 42.1（平衡星形的固定输出接口）。** 在已给乘法、伴随和准确正锥的 $A=M_3(\mathbb C)$ 中，取

$$
P=\operatorname{diag}(1,1,0),\qquad C=PAP,\qquad c=\operatorname{diag}(1,2,0),\qquad
t=\begin{pmatrix}0&0&1\\0&0&\sqrt2\\1&\sqrt2&0\end{pmatrix}.
\tag{42.1}
$$

固定 $\sigma\in\{1,-1\}$、$\rho\in\mathbb R$，定义

$$
a\circ b=\frac{ab+ba}{2},\qquad K_\sigma(a,b)=\frac{\sigma i}{2}[a,b],\qquad s=\rho\operatorname{diag}(1,-2,0),\qquad g=K_\sigma(c,t)+s.
\tag{42.2}
$$

每份读取 $\phi$ 都是 $A$ 上的数学正复线性泛函；其全部质量 $\phi(1)\ge0$ 均保留，包括零。对每个原实际探针 $x=x^*\in C$，沿用 (41.3) 的完整标签

$$
\begin{gathered}
h=K_\sigma(c,x),\quad r=c\circ x,\quad k=c\circ t,\\
R_+=x+h-k,\quad R_-=x-h+k,\quad S_+=t+r+g,\quad S_-=t-r-g,\\
L=-2x\circ(h-k)-2t\circ(r+g),\\
B_\phi(U,V)=\phi(U^2)\phi(V^2)-\phi(U\circ V)^2\ge0\quad(U=U^*,\ V=V^*).
\end{gathered}
\tag{42.3}
$$

这里 $B_\phi\ge0$ 来自实 Gram 的 Cauchy–Schwarz。原固定二表和每份探针预算分别为

$$
\mathsf{P2}:\quad \phi(g)^2\le B_\phi(c,t),\qquad
\mathsf{PB}_x:\quad |\phi(L)|\le\sqrt{B_\phi(R_+,S_+)}+\sqrt{B_\phi(R_-,S_-)}
\quad(\phi\ge0).
\tag{42.4}
$$

这个接口只有固定 $c,t,g$ 和已知乘法，不含未知映射 $D$，也不预给两份外响应。它准确使用 §41.1 的同一固定输出预算；若完整原模型的实际角 $C$ 已同号分类，$g=D(c,t)$ 且数据为 (42.1)–(42.2)，则按 §41.1 的原 PB、外层 P2 及 AH43.1 同表读取取得这些预算，不增加物理评价标签或准备。

这里 $PtP=0$ 而 $(1-P)tP\ne0$，两条角外连线均非零。定理 41.2 的无外边前件不成立；不能把它的比例式或返回消费者用于此输入，也没有把环境压缩掉。

### 42.2 零探针刚性及明确的有限反证读取

**定理 42.2（平衡星形的有限刚性）。** 对定义 42.1 的每个 $\sigma,\rho$，以下三项等价：$\rho=0$；$\mathsf{P2}$ 及每个 $x\in C_{\rm sa}$ 的 $\mathsf{PB}_x$ 对全部数学正泛函成立；仅 $\mathsf{PB}_0$ 对全部数学正泛函成立。第三项排除非零 $\rho$ 的证明不使用 P2。

具体地，置以下标准复内积下的正交单位向量及实数：

$$
u=\frac13(2\sqrt2,-1,0)^{\mathsf T},\quad e=\frac13(1,2\sqrt2,0)^{\mathsf T},\quad f=(0,0,1)^{\mathsf T},\quad \theta=\frac83\rho,
\tag{42.5}
$$

$$
\begin{aligned}
D_\rho&=\frac{2+12\rho^2}{9},& E_\rho&=\frac{2+4\rho^2}{9},\\
A_\rho&=3\sqrt{D_\rho+\theta^2E_\rho},&
\Lambda_\rho&=\sqrt2\left(1+\frac{64\rho^2}{9}\right),\\
M_\rho&=3\left(\sqrt3+\frac32+2|\rho|\right)(1+\theta^2),&
\delta_\rho&=\Lambda_\rho-A_\rho.
\end{aligned}
\tag{42.6}
$$

若 $\rho\ne0$，则 $\delta_\rho>0$。取同一个原零探针及有限正读取

$$
x=0,\quad \varepsilon=\varepsilon_\rho=\frac{\delta_\rho}{2M_\rho}>0,\quad
\eta=i\sigma e+\theta f,\quad \xi=u+\varepsilon\eta,\quad \phi_\xi(a)=\xi^*a\xi,\quad \phi_\xi(1)=1+\varepsilon^2(1+\theta^2).
\tag{42.7}
$$

则原预算的实际违反量满足

$$
|\phi_\xi(L)|-\sqrt{B_{\phi_\xi}(R_+,S_+)}-\sqrt{B_{\phi_\xi}(R_-,S_-)}\ge\frac{\delta_\rho^2}{4M_\rho}>0.
\tag{42.8}
$$

**证明。** 先给完整有限余项所需的初等面积估计。将 $\mathbb C^3$ 看成内积为 $\operatorname{Re}(a^*b)$ 的实 Hilbert 空间，定义

$$
\mathcal A(a,b)=\sqrt{\|a\|^2\|b\|^2-\operatorname{Re}(a^*b)^2}.
\tag{42.9}
$$

$a\ne0$ 时，设 $\Pi_a$ 是到实正交补 $a^\perp$ 的投影，则 $\mathcal A(a,b)=\|a\|\|\Pi_ab\|$。投影的三角不等式及收缩性给

$$
\mathcal A(a,b+q d)\le\mathcal A(a,b)+q\|a\|\|d\|\quad(q\ge0).
\tag{42.10}
$$

$a=0$ 时两边相应面积均为零，故仍成立。对自伴 $U,V$，直接由 $\phi_\xi(U^2)=\|U\xi\|^2$、$\phi_\xi(U\circ V)=\operatorname{Re}((U\xi)^*V\xi)$ 得 $\sqrt{B_{\phi_\xi}(U,V)}=\mathcal A(U\xi,V\xi)$，无需除以任何 Gram 对角或质量。

取 $x=0$，则 $h=r=0$，完整标签为 $R_+=-k$、$R_-=k$、$S_\pm=t\pm g$、$L=-(tg+gt)$。在前两维与第三维的原分块中，写

$$
v=\binom1{\sqrt2},\quad w=\binom{1/2}{\sqrt2},\quad s_0=\rho\operatorname{diag}(1,-2),\qquad
t=\begin{pmatrix}0&v\\v^*&0\end{pmatrix},\quad k=\begin{pmatrix}0&w\\w^*&0\end{pmatrix},\quad g=\begin{pmatrix}s_0&i\sigma w\\-i\sigma w^*&0\end{pmatrix}.
\tag{42.11}
$$

由 (42.5)，$w=(3/2)e$，逐项相乘给

$$
ku=0,\quad ke=\frac32f,\quad kf=\frac32e,\quad tu=\frac{\sqrt2}{3}f,\quad gu=su=\frac{2\rho}{3}u+\frac{2\sqrt2\rho}{3}e.
\tag{42.12}
$$

原 $L$ 的角块为 $i\sigma(vw^*-wv^*)$，环境列为 $-s_0v$，环境对角为零。因此在完整正交基 $(u,e,f)$ 下，全部系数为

$$
L=\begin{pmatrix}
0&i\sigma\sqrt2/2&-4\sqrt2\rho/3\\
-i\sigma\sqrt2/2&0&7\rho/3\\
-4\sqrt2\rho/3&7\rho/3&0
\end{pmatrix}.
\tag{42.13}
$$

确实，$v$ 在 $(u,e)$ 下为 $(\sqrt2/3,5/3)$，$w$ 为 $(0,3/2)$，而 $-s_0v$ 的两坐标是 $-4\sqrt2\rho/3,7\rho/3$。由此 $u^*Lu=\eta^*L\eta=0$；后一等式使用 $\eta$ 的 $e$ 坐标纯虚、$f$ 坐标实及 $L_{ef}$ 实。于是对任意有限 $\varepsilon>0$，准确有

$$
2\operatorname{Re}(\eta^*Lu)=-\sqrt2-\frac{8\sqrt2\rho\theta}{3}=-\Lambda_\rho,\qquad |\phi_{u+\varepsilon\eta}(L)|=\varepsilon\Lambda_\rho.
\tag{42.14}
$$

再令

$$
a_0=k\eta=\frac32(\theta e+i\sigma f),\quad
b_\pm=(t\pm g)u=\frac{\sqrt2}{3}f\ \pm\left(\frac{2\rho}{3}u+\frac{2\sqrt2\rho}{3}e\right),\quad d_\pm=(t\pm g)\eta.
\tag{42.15}
$$

正交性给 $\|b_\pm\|^2=D_\rho$、$\|a_0\|^2=(9/4)(1+\theta^2)$、$\operatorname{Re}(a_0^*b_\pm)=\pm\sqrt2\rho\theta$。故

$$
\mathcal A(a_0,b_\pm)^2=\frac94\left(D_\rho+\theta^2E_\rho\right),\qquad \mathcal A(a_0,b_+)+\mathcal A(a_0,b_-)=A_\rho,
\tag{42.16}
$$

其中 $E_\rho=D_\rho-8\rho^2/9$。由 $ku=0$ 和面积的齐次性，两笔真实预算之和准确等于

$$
\varepsilon\mathcal A(a_0,b_++\varepsilon d_+)+\varepsilon\mathcal A(a_0,b_-+\varepsilon d_-)
\le\varepsilon A_\rho+\varepsilon^2\|a_0\|(\|d_+\|+\|d_-\|).
\tag{42.17}
$$

此式保留全部环境项。由星形块平方得 $\|t\|=\|v\|=\sqrt3$、$\|K_\sigma(c,t)\|=\|w\|=3/2$，且 $\|s\|=2|\rho|$，所以

$$
\|d_+\|+\|d_-\|\le2(\|t\|+\|g\|)\|\eta\|
\le2\left(\sqrt3+\frac32+2|\rho|\right)\sqrt{1+\theta^2}.
\tag{42.18}
$$

乘以 $\|a_0\|=(3/2)\sqrt{1+\theta^2}$，(42.17) 即不超过 $\varepsilon A_\rho+\varepsilon^2M_\rho$。严格差额来自完整多项式恒等式

$$
A_\rho^2=\frac{18+236\rho^2+256\rho^4}{9},\qquad \Lambda_\rho^2-A_\rho^2=\frac{20}{9}\rho^2+\frac{5888}{81}\rho^4.
\tag{42.19}
$$

两根量均正，故非零 $\rho$ 给 $\delta_\rho>0$，且 $M_\rho>0$。选择 (42.7) 的有限 $\varepsilon$，由 (42.14)、(42.17)–(42.19) 得违反量至少为 $\varepsilon\delta_\rho-\varepsilon^2M_\rho=\delta_\rho^2/(4M_\rho)>0$。这证明第三项蕴涵第一项，没有用 P2、除以 $\rho$ 或通道，也没有对未知响应取极限。

反向证明保留全部探针。$\rho=0$ 时 $g=K_\sigma(c,t)$。任意正泛函的复 Cauchy–Schwarz 与 $UV=U\circ V-i\sigma K_\sigma(U,V)$ 给

$$
|\phi(K_\sigma(U,V))|^2\le B_\phi(U,V)\qquad(U=U^*,\ V=V^*).
\tag{42.20}
$$

取 $U=c,V=t$ 得 P2。对任意原 $x\in C_{\rm sa}$，记 $a=h-k$、$b=r+g$、$Z=x+i\sigma t$。直接展开，或取已付 (39.7) 的演员为 $c$，得到

$$
a+i\sigma b=i\sigma cZ,\qquad R_\pm+i\sigma S_\pm=(1\pm i\sigma c)Z,\qquad
(R_\pm+i\sigma S_\pm)^*(R_\pm+i\sigma S_\pm)=Z^*(1+c^2)Z.
\tag{42.21}
$$

左端为 $R_\pm^2+S_\pm^2+2K_\sigma(R_\pm,S_\pm)$，两个平方和之差是 $4x\circ a+4t\circ b=-2L$。相减即 $K_\sigma(R_+,S_+)-K_\sigma(R_-,S_-)=L$；施以 $\phi$、三角不等式及 (42.20)，得每个 $x$ 的原 PB。全部零质量和退化情形包含在 Cauchy–Schwarz 内；这里的交换子只是已知乘法中的比较量，不是假定未知外响应。第二项蕴涵第三项由 $x=0$ 的包含关系，等价性得证。∎

### 42.3 全复参数 P2 的非零证书及其明确失败预算

**命题 42.3（P2 单独不足）。** 在 (42.1)–(42.2) 中取 $\rho=1/2$，则两种 $\sigma$ 的全部正泛函 P2 均成立，但 (42.7) 的一个正读取违反原零探针 PB。

**证明。** 取任意 $z=X+iY$，记 $\mathcal R=X^2+Y^2$。固定二表与矩阵铅笔为

$$
H_\phi=\begin{pmatrix}\phi(c^2)&\phi(k)-i\phi(g)\\\phi(k)+i\phi(g)&\phi(t^2)\end{pmatrix},\qquad F_w=t^2-2\operatorname{Re}(w)k+|w|^2c^2+2\operatorname{Im}(w)g.
\tag{42.22}
$$

其对角非负，$\det H_\phi=B_\phi(c,t)-\phi(g)^2$，故 P2 等价于 $H_\phi\ge0$。列 $(-w,1)$ 的二次值是 $\phi(F_w)$；其复数倍涵盖第二坐标非零的所有列，第二坐标为零的列由 $\phi(c^2)\ge0$ 处理。因此全部 $w$ 的 $F_w\ge0$ 等价于全部数学正泛函 P2，反向使用正泛函决定准确锥。这是列的齐次参数化，不除以任何质量或表对角。

令 $s=\operatorname{diag}(1/2,-1,0)$，展开得

$$
Q_z=(t-zc)^*(t-zc)+2\sigma Y s=F_{X+i\sigma Y}.
\tag{42.23}
$$

这个参数替换为复平面的双射。$Q_z$ 的右下角为 $3$；若 $c_0=\operatorname{diag}(1,2)$，其左上块为 $vv^*+\mathcal R c_0^2+2\sigma Y s_0$，右上列为 $-\overline zc_0v$。减去 $\mathcal R c_0vv^*c_0/3$，Schur 补准确为

$$
D_z=\begin{pmatrix}
1+2\mathcal R/3+\sigma Y&\sqrt2(1-2\mathcal R/3)\\
\sqrt2(1-2\mathcal R/3)&2+4\mathcal R/3-2\sigma Y
\end{pmatrix}.
\tag{42.24}
$$

$$
(D_z)_{11}=\frac23X^2+\frac23(Y+3\sigma/4)^2+\frac58>0,\qquad \det D_z=\frac{16}{3}X^2+\frac{10}{3}Y^2\ge0.
\tag{42.25}
$$

行列式由 $2[(1+2\mathcal R/3)^2-Y^2]-2(1-2\mathcal R/3)^2=16\mathcal R/3-2Y^2$ 得到。对任意 $a,b\in\mathbb C$，$D_z$ 的二次型可配成 $(D_z)_{11}|a+(D_z)_{12}b/(D_z)_{11}|^2+(\det D_z)/(D_z)_{11}|b|^2$，所以 $D_z\ge0$，包括 $z=0$。再将 $Q_z$ 的环境坐标配方，二次型等于该 Schur 二次型加 $3|b+(-zv^*c_0)a/3|^2$（此处 $a\in\mathbb C^2,b\in\mathbb C$），故 $Q_z\ge0$。这里只除以确定正的系数，全部复参数及全部原质量的 P2 证书成立。

而 (42.6)–(42.7) 准确化为

$$
\theta=\frac43,\quad \Lambda_{1/2}=\frac{25\sqrt2}{9},\quad A_{1/2}=\frac{\sqrt{93}}3,\quad
M_{1/2}=\frac{25}{3}\left(\sqrt3+\frac52\right),\quad \varepsilon_{1/2}=\frac{25\sqrt2-3\sqrt{93}}{150(\sqrt3+5/2)}>0.
\tag{42.26}
$$

这里 $\Lambda_{1/2}^2-A_{1/2}^2=413/81>0$。取 $x=0$、$\xi=u+\varepsilon_{1/2}(i\sigma e+4f/3)$，质量为 $1+(25/9)\varepsilon_{1/2}^2$；定理 42.2 给实际违反量至少 $\delta_{1/2}^2/(4M_{1/2})>0$。因此这个例子只分离 P2 与固定输出 PB，不是满足完整 PB 或完整原公理的反模型。∎

### 42.4 已知量子行、真实推断及保留的全局缺口

本节的新增关系是这个真环境耦合平衡星形中，单个原零探针加一份明确有限移动的数学正读取已消去余量；不是重复 §41 的分离背景结论，也不使用任意三维输入的分类。对所得完整行，包括原来的两条环境边，准确有

$$
c\circ t-ig=\begin{cases}ct,&\sigma=1,\\tc,&\sigma=-1.\end{cases}
\tag{42.27}
$$

$M_3$ 的乘法、正锥、伴随及数学正读取本来已给；单行身份不构造未知总响应，不证明全域双线性、结合乘法或全部有限旧复 Gram。已分类角的通常／相反 $C^*$-乘法及数学 GNS/Hilbert，仍直接复用 §36.1、40.2 的 AH64.1、75.1；循环向量平方范数仍为原 $\gamma(P)$，零质量仍为零向量。Born 数学配对要成为原概率，仍需实际完整事件菜单与真实来源。R5 §12 只按 §40.1 已付的非零交替双线性、同域及全域 P、N 前件复用，不能倒推这些前件；其 $\circ+iD$ 与本卷 $\circ-iD$ 的相反关系不变。

一般原有限谱接口的首个未付关系仍为 (41.28)：

$$
E_+=D(c-g,k)-K_\sigma(c-g,k),\quad E_-=D(c+g,-k)-K_\sigma(c+g,-k),\quad
E_+-E_-=2cs,\qquad \boxed{E_+=E_-}.
\tag{42.28}
$$

本定理仅在指定星形上给 $s=0$，从而在适用的完整模型中给这份局部相等；一般输入的方框关系没有被增作公理，也未被普遍证明。任意三维输入、其他对角或环境耦合、一般混合整行、非零相对标量演员的未覆盖输入、无限谱演员及完整奇数阶段 UHF 分类仍须原桥梁。全局单位行 PT183.2/AH43.3 已付，不重开；相对单位的标准修正仍为 $K_\sigma(c+\lambda P,t)=K_\sigma(c,t)+\lambda K_\sigma(P,t)$，未添加平移中性、残差缩放或响应运输。

独立定量义务也不变：$\omega_{M,\lambda_*}(q)\to0$ 不能推出增长分割中的 $N\omega_{M,\lambda_*}(q)^2\to0$；本节有限位移不提供任意输入的统一率、可累加界或任意相异谱值模数，也不能借用另一误差的 $N\kappa^2$ 界。§39 的原标签真角安置障碍没有消失。局部有限结论不等于一般重构、普适简化或全局独立公理数减少。

### 42.5 完全相同的递归全文来源与数学归属

**定义 42.4（完整来源的同一身份）。** 本节 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$ **就是定义 41.4 的同一个谓词**，因而也是定义 40.1、36.1 的同一个谓词；$S$ 仍指原对称响应。严格沿 $41.4\Rightarrow40.1\Rightarrow36.1\Rightarrow32.3\Rightarrow\S27.1\Rightarrow26.3\Rightarrow22.3\Rightarrow18.2\Rightarrow\{10.2,15.2,\mathrm{AH}28.1,64.2,75.1\}\Rightarrow\mathrm{SQ}47.1\text{--}47.13$ 的全文身份，将每份定义、合同、公式、量词及逐项递归纳入、逐层固定版本的全部上游全文，逐句、逐公式、逐量词同时合取。这里是原谓词的完整身份，不以编号范围或以下说明替代任何条款。

定义 41.4 的各层固定身份全部保留：AH 的 `b1a95e41b9622e9f720e51f9bb899841f5b74ca1`，W/CC/PT 的 `3b10aed60f60e4901bae6cf2e160bf439d642e64`，SQ 自身 §§1.3、39、41.1、47.1 下各自层级的 `dcaebc0b9ca5a3a463fd8cfd161d38967df28668` 与 `0aa11dbc3dc337d667b98900673e07d67b99bf46`，OP/PT/PB/SM/C/AQ/R3/W/FR/XV/SF 的 `f24d1138a7b994da16abd9a47affedea64ea44ce`，AH22.1 的 `2addd6f369b7387226c2b0cc984623dd3efe40a1`、AH12.1 上游的 `39a0505470ea889dd9d4301ad60cd9506a5e8b58` 及 AH42.1 内的 `bef9bba367a24ab5e250491dcb88ed85ebc29cf7`；R5 的 `aef46ce7497cf8ee6bef9bb7356a4483f3bfe6f0` 不覆盖内层身份。

同一 $\Omega/\mathrm{native}$ 的全部原对象、准备、事件、程序、设备、比较权 $q$、跨标签全词共同 $K/J$、parent、ready、控制、旗标、中心、经典及不等维块、无轴对象、中间切口、模式网络、根类、十一端点、配置、实际逆等距边、静默及零活动、终端标签和读器合同都保留；网络 $D,C$ 不换成本响应或数学正锥，未定义请求不补零箭头。实际准备、相干控制、完整 Born 菜单及所有原质量不由向量读取制造；全局归一须 $\gamma(1)>0$，角归一另须真实条件化及 $\gamma(P)>0$，零、不等、次归一和非正常质量不删除。真正相关联合、张量仍须同一实际共同来源、全部相关输入、忠实同向交换腿、共同生成、分离及重数，相同边缘或分别可达不支付联合实现。

typed CP、箭头下降、整台递归同源参考、原真支持与支持内补、交织夹界、每个所需有限深度及每个正精度不变。完整仪器、TP、Kraus、更新及 Lüders 保留完整 typed 菜单、单位分区、接受端、校准、表示与收敛前件，并量化整个环境、全部成功／失败／细记录／port／post-port 输出及每份完整输出的每个仍合法未来；只有严格正实际输出质量可归一，失败和零分支及完整输出均不删。合法顺序、自适应、并行历史、真实分组遗忘、停止、拒绝、销毁、泄漏、同数两侧、逆向真实 Return 和含活动 ready、producer 的完整 CountRead 均不被矩阵相等或当前读取替代；原程序、历史、记录、读取次序、$q$ 零集和未来权限不合并。正常性、指定前对偶、可数可加、无限菜单记录和收敛，及实际连续可逆流与逆、物理钟单位、酉实现、生成元域、Hamiltonian 能量、作用量和共同正物理 $\hbar$ 各保留原来源。有限向量位移不证明整个谓词的满足性。

实 Gram、Cauchy–Schwarz、实正交投影和 Schur 配方是成熟初等工具，正泛函背景沿 §41.5 所引 Blackadar《Operator Algebras》；(42.21) 复用已付 (39.7) 的标准乘法恒等式。Alfsen–Shultz《Orientation in operator algebras》的动力学对应需到斜序导子的线性映射，不能为本接口补上线性或物理动力学。本节不使用此前提未付的重构定理，也不把标量二表正性升格为未知映射的完全正性。平衡星形的有限差额 (42.19) 及其原预算消费者是本库关系推导；它不归给一般 Gram 文献，不作历史优先权、穷尽检索、外部开放问题或完整新公理系统主张。

### 42.6 完整直观

把刻度为一和二的两间房与外面的第三间房看成同一个三维系统：两条真实连线都在，而且配比恰好使原二表容许一正一负的平衡误差。新的有限结论是，原探针只取零就足够，只需把数学正读取的位置移动一次：先找两份原 $R$ 都送到零的房内方向 $u$，此时原输入 $t$ 仍把它送进环境；再按文中明确的有限幅度，加入带四分之一转相位的房内方向和与误差相配的环境方向。原 $L$ 的读数准确长出一次项，两笔完整 Gram 面积的一次项也能逐个算清；普通实投影的三角不等式包住全部有限余项，而两边平方之差是对任何非零误差都严格正的二次项加四次项，所以指定的这一次正读取确实违反原预算，没有删连线、归一质量、取消通道或对未知规则取极限。误差为二分之一时，全部复参数的原 P2 仍由明确矩阵证书通过，却被这份预算排除，说明补上的正是 P2 留下的有限缺口。余量为零时，同一个已知乘法恒等式又保证全部原探针预算，所得整行准确是通常或相反量子乘法；但任意环境输入为何有相同的两份原缺陷，以及增长谱分割的误差如何累加，仍是不同的未付桥梁。真实准备、完整 Born 菜单、同一共同相关来源、整台仪器全部输出及每个合法未来、Return、CountRead、正常性、指定前对偶、物理钟、动力学和共同正的作用量尺度，也继续由同一个完整递归来源谓词承担，因此这一步是明确有限几何的简化，尚未完成全局量子起源。

## 追加锚（本行以下为增补区）
## 43. 分离背景两探针的平方根稳定性与幂次尖锐性

### 43.1 固定输出、原质量与两份近似预算

沿用 §§41.1–41.2 的固定输出接口，以 $\Sigma$ 表示 (41.1) 的支撑投影，避免与原对称响应 $S$ 混淆。设 $A$ 为含单位复 $C^*$-代数，$P$ 为实际投影，$p,q\le P$ 为非零正交投影，置
$$
\Sigma=p+q,\quad c=p+2q,\quad K_\sigma(u,v)=\frac{\sigma i}{2}[u,v],\quad \sigma\in\{1,-1\},
$$
$$
T=ptq\in pAq,\quad \tau=T+T^*,\quad t=\tau+b,\quad b=b^*=(1-\Sigma)b(1-\Sigma),
\qquad s=s_p+s_q,\quad s_p=s_p^*\in pAp,\quad s_q=s_q^*\in qAq,\quad g=K_\sigma(c,t)+s.
\tag{43.1}
$$
不要求 $p\sim q$ 或余量为标量；$b$ 无范数、谱或秩限制，可含 $P-\Sigma$ 与 $1-P$ 之间的任意耦合，禁止的是 $\Sigma$ 与 $1-\Sigma$ 之间的连线。对自伴元素保留 $u\circ v=(uv+vu)/2$，以及原来的
$$
B_\phi(U,V)=\phi(U^2)\phi(V^2)-\phi(U\circ V)^2,\qquad
\phi(g)^2\le B_\phi(c,t)\quad(\phi\ge0).
\tag{43.2}
$$
这里及下文的量词包含全部数学正泛函、零泛函、任意非负有限质量及非正常正泛函，不作原质量归一。固定二表 P2 保持精确。对 $x=x^*\in PAP$，原标签准确仍是 (41.3)：
$$
\begin{gathered}
h=K_\sigma(c,x),\quad r=c\circ x,\quad k=c\circ t,\quad R_\pm=x\pm(h-k),\quad S_\pm=t\pm(r+g),\\
L=-2x\circ(h-k)-2t\circ(r+g).
\end{gathered}
$$
只取 (41.8) 的两份实际探针；其分母非零已由 §41.2 支付：
$$
d_\pm=\frac{1\pm\sqrt{10}}3,\qquad v=K_\sigma(c,\tau),\qquad
x_d=\frac{v}{d-3/2}+z_d,\quad z_d=\frac{s_p}{d-1}+\frac{s_q}{d-2}\quad(d=d_+,d_-).
\tag{43.3}
$$
探针可以依赖同一固定余量。以 $R_{d,\pm},S_{d,\pm},L_d$ 记其完整原标签；对同一 $\eta\ge0$，仅将这两份预算改为
$$
|\phi(L_d)|\le\sqrt{B_\phi(R_{d,+},S_{d,+})}+\sqrt{B_\phi(R_{d,-},S_{d,-})}+\eta\phi(1)
\quad(\phi\ge0,\ d=d_+,d_-).
\tag{43.4}
$$
这不是对完整 $\mathsf H_A(D)$ 的重定义，不假定任何响应映射、外响应值或以 $t$ 为演员的 PB。

**定理 43.1（统一平方根界）。** 在 (43.1)–(43.4) 下，
$$
\boxed{\ \|s_p\|\le\sqrt{\eta/2},\qquad \|s_q\|\le\sqrt{\sqrt{10}\,\eta/2},\qquad
\|s\|\le10^{1/4}\sqrt{\eta/2}.\ }
\tag{43.5}
$$
此为显式有效而不主张最优的常数；与代数、维数、秩、$\sigma$、$T$ 的核和值域及 $b$ 的大小无关，不要求 $t,\tau,T$ 有统一范数界。

### 43.2 保留背景的零面积读数与两条加权方程

**证明。** 直接复用 (41.13)–(41.17) 的精确探针恒等式，不重证该块代数：
$$
\begin{gathered}
R_{d,\pm}=x_d\pm\tau/d=\Sigma R_{d,\pm}\Sigma,\quad
S_{d,+}=b+dR_{d,+},\quad S_{d,-}=b-dR_{d,-},\\
L_d=-2(d+d^{-1})\tau\circ z_d\in\Sigma A\Sigma.
\end{gathered}
\tag{43.6}
$$
对任意正泛函 $\psi$，取正读取 $\phi_\Sigma(a)=\psi(\Sigma a\Sigma)$，其质量准确为 $\psi(\Sigma)$。$b$ 仍在两个完整 $S$ 标签中；由 (43.6) 的实际乘法及 $\Sigma b^2\Sigma=0$，
$$
\phi_\Sigma(S_{d,\pm}^2)=d^2\phi_\Sigma(R_{d,\pm}^2),\qquad
\phi_\Sigma(R_{d,\pm}\circ S_{d,\pm})=\pm d\phi_\Sigma(R_{d,\pm}^2).
$$
因此**两项实际 Gram 同时为零**，(43.4) 给 $|\psi(L_d)|\le\eta\psi(\Sigma)$。每个 $\Sigma A\Sigma$ 的状态均可由 $a\mapsto\omega(\Sigma a\Sigma)$ 正延拓；自伴元素的状态范数公式遂给
$$
\|L_d\|\le\eta,\qquad |d+d^{-1}|=\frac{2\sqrt{10}}3,\qquad
\|\tau\circ z_d\|\le\frac{3\eta}{4\sqrt{10}}.
\tag{43.7}
$$
状态只作数学范数分离；零质量无需除法，未使用正常性。令 $X=s_pT$、$Y=Ts_q$、$F_d=2p(\tau\circ z_d)q$，读取 $pAq$ 块得
$$
\frac{X}{d-1}+\frac{Y}{d-2}=F_d,\qquad \|F_d\|\le M:=\frac{3\eta}{2\sqrt{10}}.
\tag{43.8}
$$
置 $r_0=\sqrt{10}$、$\alpha_\pm=(d_\pm-1)^{-1}$、$\beta_\pm=(d_\pm-2)^{-1}$。精确系数及行列式为
$$
\begin{gathered}
\alpha_+=(r_0+2)/2,\quad\alpha_-=-(r_0-2)/2,\quad |\alpha_+|+|\alpha_-|=r_0,\\
\beta_+=-(r_0+5)/5,\quad\beta_-=(r_0-5)/5,\quad |\beta_+|+|\beta_-|=2,\\
\Delta=\alpha_+\beta_--\alpha_-\beta_+=-6/r_0.
\end{gathered}
$$
在 Banach 空间 $pAq$ 中解这两条标量系数方程：
$$
X=\frac{\beta_-F_{d_+}-\beta_+F_{d_-}}{\Delta},\quad
Y=\frac{-\alpha_-F_{d_+}+\alpha_+F_{d_-}}{\Delta},\qquad
\boxed{\ \|s_pT\|\le\frac{2M}{|\Delta|}=\frac\eta2,\quad
\|Ts_q\|\le\frac{r_0M}{|\Delta|}=\frac{\sqrt{10}}4\eta.\ }
\tag{43.9}
$$
这里仅除以非零标量，从未取消或求逆 $T$。

### 43.3 矩形通道的 P2 恢复

**引理 43.2（正确角上的矩形恢复）。** 设 $e,f$ 为 $C^*$-代数中的投影，$a=a^*\in eAe$、$U\in eAf$、$\kappa>0$。若每个 $eAe$ 的状态均满足 $|\omega(a)|^2\le\kappa\omega(UU^*)$，则
$$
\|aU\|\ge\frac{\|a\|^2}{\sqrt\kappa}.
\tag{43.10}
$$
**证明。** 令 $m=\|a\|$；$m=0$ 时直接成立。否则取固定 $\epsilon_0\in\{1,-1\}$ 及角状态 $\omega_n$，使 $\omega_n(a)\to\epsilon_0m$。由 $-me\le a\le me$，
$$
(a-\epsilon_0me)^2\le2m(me-\epsilon_0a),\qquad
\delta_n:=\|(\pi_n(a)-\epsilon_0m)\xi_n\|\longrightarrow0
$$
对其 GNS 循环单位向量成立。正确角元素是 $C_0=UU^*\in eAe$；假设给 $\liminf_n\omega_n(C_0)\ge m^2/\kappa$。$C_0$ 固定且有界，故
$$
|\omega_n(aC_0a)-m^2\omega_n(C_0)|\le2m\|C_0\|\delta_n\longrightarrow0,
\qquad \liminf_n\omega_n(aC_0a)\ge m^4/\kappa.
$$
由 $aC_0a=(aU)(aU)^*$ 及 $C^*$-恒等式，$\|aU\|^2=\|aC_0a\|\ge m^4/\kappa$。不要求 $U$ 为方块、单射、满射、可逆或有闭值域。∎

续证定理。对 $pAp$ 或 $qAq$ 的任意状态，分别用 $\phi(a)=\omega(pap)$ 或 $\omega(qaq)$ 读取精确 P2。两者的 $\phi(c\circ t)=0$；其 $\phi(c^2)$ 分别为 $1,4$，$\phi(t^2)$ 分别为 $\omega(TT^*),\omega(T^*T)$，$\phi(g)$ 分别为 $\omega(s_p),\omega(s_q)$。因此
$$
|\omega(s_p)|^2\le\omega(TT^*),\qquad
|\omega(s_q)|^2\le4\omega(T^*T).
\tag{43.11}
$$
第二角的因子必须是 $4$，来自 $c^2q=4q$。引理分别取 $(a,U,\kappa)=(s_p,T,1)$、$(s_q,T^*,4)$，给
$$
\|s_p\|^2\le\|s_pT\|\le\eta/2,\qquad
\|s_q\|^2\le2\|s_qT^*\|=2\|Ts_q\|\le\sqrt{10}\,\eta/2.
$$
正交角满足 $\|s_p+s_q\|=\max\{\|s_p\|,\|s_q\|\}$，从而得到 (43.5)，也包括 $\eta=0$。引理已涵盖零通道；状态范数和 GNS 极限都只涉及每份数据中固定、已知的 $C^*$ 元素，不涉及未知 $D$ 的输入正则性或极限。∎

### 43.4 精确全正 P2 家族的幂次消费者

**命题 43.3（$1/2$ 幂次不可统一提高）。** 在 $M_2(\mathbb C)$ 中取 $p=E_{11}$、$q=E_{22}$、$P=1$、$c=\operatorname{diag}(1,2)$、$\tau_0=E_{12}+E_{21}$，并对 $\varepsilon>0$ 置
$$
t_\varepsilon=2\varepsilon\tau_0,\qquad s_\varepsilon=\varepsilon\operatorname{diag}(1,-2),\qquad
b=0,\qquad g_\varepsilon=K_\sigma(c,t_\varepsilon)+s_\varepsilon.
\tag{43.12}
$$
定理 34.1 的精确全正 P2 族直接供应此例：其参数 $(a,b,v,r)=(1,2,2\varepsilon,\varepsilon)$ 满足 $|r|=\varepsilon\le4\sqrt2\varepsilon/3$。这已覆盖两种 $\sigma$、全部复相位、任意质量与零泛函，不重证该尖锐区间。

**证明。** 两份实际探针准确为
$$
x_{d,\varepsilon}=\frac{\sigma i\varepsilon}{d-3/2}
\begin{pmatrix}0&-1\\1&0\end{pmatrix}
+\varepsilon\operatorname{diag}\big((d-1)^{-1},-2(d-2)^{-1}\big).
$$
由 (43.6) 且 $b=0$，两个 Gram 对**每个**正泛函均为零。此时 $z_d$ 两个对角元之和为 $-\varepsilon d/((d-1)(d-2))$，故
$$
L_d=2\varepsilon^2\frac{d^2+1}{(d-1)(d-2)}\tau_0,\qquad
\|L_d\|=2\varepsilon^2\kappa_d,\quad
\kappa_d=\left|\frac{d^2+1}{(d-1)(d-2)}\right|,
$$
$$
\kappa_+=\frac{2(10+\sqrt{10})}{7\sqrt{10}-20},\qquad
\kappa_-=\frac{2(10-\sqrt{10})}{20+7\sqrt{10}},\qquad
\kappa=\max\{\kappa_+,\kappa_-\}=\kappa_+.
\tag{43.13}
$$
取 $\eta_\varepsilon=2\kappa\varepsilon^2$。正泛函满足 $|\phi(L_d)|\le\|L_d\|\phi(1)\le\eta_\varepsilon\phi(1)$，故两份完整预算对全部质量成立；不是有限状态抽样。另一方面 $\|s_\varepsilon\|=2\varepsilon$，对任意 $\alpha>1/2$，
$$
\frac{\|s_\varepsilon\|}{\eta_\varepsilon^\alpha}
=2(2\kappa)^{-\alpha}\varepsilon^{1-2\alpha}\longrightarrow\infty\quad(\varepsilon\downarrow0).
$$
所以固定 $M_2$ 上也不存在统一的 $C_\alpha\eta^\alpha$ 界。这只证明幂次尖锐性，不证明 (43.5) 的系数最优，也不是块数增长时的收敛率或完整公理反模型。∎

### 43.5 乘法对应、成熟归属与完整来源边界

固定行准确有 $c\circ t-ig=ct-is$（$\sigma=1$）或 $tc-is$（$\sigma=-1$），故距通常或相反乘法行的范数误差恰为 $\|s\|$，受 (43.5) 控制。已分类角的 $C^*$、Hilbert/GNS、Pauli 与 Born 对应只按 §§40.1–41.5 的原入口复用；固定输出不供应全域响应、双线性、任意输入混合或完整量子起源。

本节保持 (43.1) 的支撑形状，未覆盖 $ptp\ne0$、$qtq\ne0$ 或 $(1-\Sigma)t\Sigma\ne0$ 的一般固定输出输入；完整 H 中已有 §31.2 返回消费者者仍直接复用。原任意总 $D$、准确锥、分离评价族、全部 A1–A3/P2、内外嵌套 PB 及其全部原质量不被修改。一般全 H 混合输入中，(41.28) 定义的同两份 $E_\pm$ 之相等 $E_+=E_-$ 仍未支付；已知差额 $E_+-E_-=2cs$ 不被改为相等公理。本界不支付增长有限分割中的 $N\omega_{M,\lambda_*}(\varepsilon)^2\to0$，不分类一般环境运输、无限谱演员或完整奇数阶段 UHF 全域。

精确标签及比例恒等式归于 §41.2，精确 P2 家族归于定理 34.1；这里的定量推断使用成熟的正压缩、自伴状态范数公式、Gelfand–Naimark–Segal 表示和 $C^*$-恒等式。Peirce 块结构及表示背景的文献归属保持 §41.5 的 Hanche-Olsen–Størmer 与 Blackadar；不将本节定量界归给这些文献，不主张历史优先权或文献穷尽性。

物理来源**严格就是定义 41.4 的同一个** $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$，$S$ 为原对称响应；沿 $41.4\Rightarrow40.1\Rightarrow36.1\Rightarrow32.3\Rightarrow\S27.1\Rightarrow26.3\Rightarrow22.3\Rightarrow18.2\Rightarrow\{10.2,15.2,\mathrm{AH}28.1,64.2,75.1\}\Rightarrow\mathrm{SQ}47.1\text{--}47.13$，将每份定义、合同、公式、量词及逐项递归纳入、逐层固定版本的**全部上游全文逐句、逐公式、逐量词同时合取**。定义 41.4 的 AH/W/CC/PT、SQ 两层主源、OP/PT/PB/SM/C/AQ/R3/W/FR/XV/SF、AH22.1、AH12.1、AH42.1 及 R5 等各内层固定身份均原样保留；此处说明不替代其中任何全文或前件。

AH 的直接身份为 `b1a95e41b9622e9f720e51f9bb899841f5b74ca1`，W、CC、PT 为 `3b10aed60f60e4901bae6cf2e160bf439d642e64`；SQ 主源按其自身 1.3、39、41.1、47.1 解析，保留 `dcaebc0b9ca5a3a463fd8cfd161d38967df28668`、`0aa11dbc3dc337d667b98900673e07d67b99bf46` 的相应层级。OP/PT/PB/SM/C/AQ/R3/W/FR/XV/SF 的 `f24d1138a7b994da16abd9a47affedea64ea44ce`、AH22.1 的 `2addd6f369b7387226c2b0cc984623dd3efe40a1`、AH12.1 的 `39a0505470ea889dd9d4301ad60cd9506a5e8b58`、AH42.1 中 OP 等直接身份 `bef9bba367a24ab5e250491dcb88ed85ebc29cf7` 均不被直接读取身份压平；R5 的原直接身份仍按 §41.5。原根、全部静默和其他静态分支不改为 UHF 或三维 Pauli 对象。

同一 $\Omega/\mathrm{native}$ 的对象、准备、事件、设备、程序、比较权、共同 $K/J$、parent、ready、控制、旗标、中心、经典及不等维块、无轴对象、全部中间切口、模式网络、原根类、十一端点、配置、逆等距边、全静默、零活动、终端及读器合同均保持；未定义请求不补零。实际相干控制、事件绑定的完整 Born 菜单、全部原质量和真实条件化仍须原来源：全局菜单仅在 $\gamma(1)>0$ 时归一，角菜单另须真实条件化及 $\gamma(P)>0$。真正联合与张量须同一实际共同来源、全部相关输入、忠实同向交换腿、共同生成、分离及重数，不能由相同边缘、分别可达或 GNS 代付。

typed CP、箭头下降、递归同源整台参考、真支持、支持内补、交织夹界、全部所需有限深度和每个正精度保留原前件。完整仪器、TP、Kraus、更新及 Lüders 仍须完整 typed 菜单、单位分区、接受端、校准、表示及收敛，量化整个环境、全部成功／失败／细记录／port／post-port 输出及每份完整输出的每个仍合法未来；只对严格正的实际输出质量归一，不删零分支或失败。合法顺序、自适应、并行历史、真正分组遗忘、停止、拒绝、销毁、泄漏、同数两侧及逆向真实 Return、完整 CountRead 的活动 ready 和 producer 全部保留，不凭相同算子或读数合并历史、记录、读取次序、比较权零集或未来权限。正常性、指定前对偶、无限菜单和记录的可数可加及收敛仍须原扩展来源；物理动力学仍须原域实际连续可逆流及实际逆、物理钟与单位、适用酉实现、一般生成元域、Hamiltonian 能量解释、作用量及共同正的物理 $\hbar$。数学读取、状态及 GNS 不制造这些物理来源，也不证明整个来源谓词满足。

把 $p,q$ 看成刻度分别为一和二的两间房，$T$ 是可能有核、甚至完全不通的门，$s_p,s_q$ 是各房内不必为数值的误差；外部背景始终留在原输入与标签里，只允许它完全处于两房之外。几何简化是两条独立斜率配合一份二次正性约束：每个斜率使两对完整标签在支持读数中成比例，两笔 Gram 面积便同时为零，近似预算直接限制相应算子；两组不同权重再分别限制误差穿门的两个乘积。精确 P2 在两房给出系数一与四的平方读数界，矩形 GNS 引理把它们转换成误差范数的平方控制，同时涵盖门的零通道，不需要门可逆或值域闭合。这便得到平方根界，而精确二维全正家族说明这个幂次确实不能提高。过程中没有删改背景、改变原质量或对未知响应取极限；两房内的对角输入、真正接向环境的连线、块数增长时的误差累加与完整物理来源仍须各自的额外推断，不能由这项有限几何结论代付。

## 追加锚（本行以下为增补区）

## 44. 两角正性证书续卷入口

§§44–50 的完整正文见[《全 PB 两角正性证书续卷》](AURIC_FULL_PB_TWO_CORNER_POSITIVE_CERTIFICATE_CONTINUATION.md)，编号与来源定位见该卷读法说明。

## 追加锚（本行以下为增补区）
