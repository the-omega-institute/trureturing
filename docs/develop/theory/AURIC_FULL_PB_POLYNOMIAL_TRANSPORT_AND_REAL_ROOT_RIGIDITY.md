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
