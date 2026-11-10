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



## 28. 两个完整角约束同一输出的三项正证书

**定义 28.1（完整原候选与实际双角）。** 本节保持定义 6.1、16.1 的同一个完整原候选。准确地，$A$ 是已完成的含单位复 C* 代数，$E=A_{\rm sa}$，$S(a,b)=a\circ b=(ab+ba)/2$，$C=A_+$，$u=1$，$N=\|\cdot\|$。原正实线性评价族 $\mathcal P$ 分离 $E$ 并准确决定 $C$；保留同一个原 $\Omega/\mathrm{native}$、每个原标签、每份原评价及质量 $m_\gamma=\gamma(1)$，包括零、不等、次归一及原表示意义下的非正常评价。未知量仍是同一个任意总映射 $D:E^2\to E$。

完整 $\mathsf H_A(D)$ 同时要求全部实际输入、两种次序及原评价的有向 A1/P2：

$$
\begin{pmatrix}
\gamma(a^2)&\gamma(a\circ b)-i\gamma D(a,b)\\
\gamma(b\circ a)-i\gamma D(b,a)&\gamma(b^2)
\end{pmatrix}\succeq0
\quad(a,b\in E,\ \gamma\in\mathcal P).
\tag{28.1}
$$

A2 要求对每个 $a,b\in E$ 及每份原 $\gamma\in\mathcal P$，$a_1=a+b,a_2=a,a_3=b$ 的实表 $(\gamma(a_i\circ a_j))_{i,j=1}^3$ 在整个 $\mathbb R^3$ 上半正定，$(1,-1,-1)$ 给零二次值，并保留全部排列及其对应零方向。A3 要求 $1^2=1$，以及同一个固定有理 $0<\vartheta\le1$ 下全部 $0\le z\le\vartheta1\Rightarrow z^2\le z$。对每个实际原三元组 $(c;a,b)$，完整 PB 要求

$$
\begin{gathered}
v=D(c,a)-c\circ b,\qquad w=c\circ a+D(c,b),\\
D(a+v,b+w)-D(a-v,b-w)=-2a\circ v-2b\circ w.
\end{gathered}
\tag{28.2}
$$

它等价于同两份外标签的原平方式 PB；全部内外值、零、重复、任意实幅度、缩放、平移、背景和嵌套调用均在原量词内。不预给 $D$ 齐次、可加、连续、可测、协变、压缩自然性、商下降、双对偶延拓或有限阶段输出闭合，也不预给全部复三表正性。

取实际投影 $p,s\in A$ 及实际自伴元素

$$
\begin{gathered}
h,e\in pAp,\quad h^2=e^2=p,\quad he=-eh,\\
k,f\in sAs,\quad k^2=f^2=s,\quad kf=-fk,\\
q=1-p,\qquad t=1-s,\qquad
K_\sigma(a,b)=\frac{\sigma i}{2}[a,b].
\end{gathered}
\tag{28.3}
$$

本节的双角前件是同一个旧 $D$ 在**两个整个实际完成角**中都已分类，而且使用同一个普通符号 $\sigma\in\{1,-1\}$：

$$
D|_{(pAp)_{\rm sa}^2}=K_\sigma|_{(pAp)_{\rm sa}^2},\qquad
D|_{(sAs)_{\rm sa}^2}=K_\sigma|_{(sAs)_{\rm sa}^2}.
\tag{28.4}
$$

两个有限矩阵片段的分类不代付 (28.4)。角闭合及完整角接口直接消费 W119.2–119.3 和 W 式 (120.2)，其原评价标签不合并，角质量分别为原 $\gamma(p),\gamma(s)$，零限制不删除、不归一。AH42.2、66–72 和 W 的引文身份沿定义 6.1、17.3，内部固定上游不变。

**定理 28.2（同一余项的交角与严格正间隙）。** 在定义 28.1 下，对全部实 $R,T$，固定实际余项

$$
r=D(Rh,Tk)-K_\sigma(Rh,Tk).
\tag{28.5}
$$

则

$$
\boxed{r=r^*\in pAp\cap sAs,\qquad [r,h]=[r,k]=0.}
\tag{28.6}
$$

只由原输入定义的三项正元满足

$$
\boxed{L=q+ptp+pkqkp=1-(pkp)^2\ge0,\qquad Lr=0.}
\tag{28.7}
$$

特别，若 $\|pkp\|<1$，则不增加任何响应公理便有

$$
\boxed{D(Rh,Tk)=K_\sigma(Rh,Tk)\quad(R,T\in\mathbb R).}
\tag{28.8}
$$

证明。AH43.1 的原反对称性与零槽已支付。$R=0$ 或 $T=0$ 时 $r=0$，全部余项结论成立。其余对实际对 $(Rh,Tk)$ 应用定理 7.1，得 $r\in(pAp)_{\rm sa}$、$[r,h]=0$。再把同一定理用于实际对 $(Tk,Rh)$ 及第二份框架 $(k,f)$，得

$$
D(Tk,Rh)=K_\sigma(Tk,Rh)+\widetilde r,
\qquad\widetilde r\in(sAs)_{\rm sa},\quad[\widetilde r,k]=0.
\tag{28.9}
$$

$D$ 与比较映射各自反对称，故 $\widetilde r=-r$。这证明 (28.6)：两次约束指向的是同一个固定旧输出，不是两份可分别选择的误差。没有用 $D(Rh,Tk)=RTD(h,k)$。

三个加项分别为投影 $q$、$(tp)^*(tp)$ 和 $(qkp)^*(qkp)$，故均为正。又由 $k^2=s$，

$$
\begin{aligned}
ptp&=p-psp=p-pk^2p,\\
pk^2p&=(pkp)^2+pkqkp,\\
q+ptp+pkqkp&=q+p-(pkp)^2=1-(pkp)^2.
\end{aligned}
\tag{28.10}
$$

同一 $r$ 满足 $pr=r$、$sr=r$，因而 $qr=tr=0$。逐项作用于这一个元素，得到

$$
qr=0,\qquad ptpr=ptr=0,\qquad
pkqkpr=pkqkr=pkqrk=0.
\tag{28.11}
$$

最后一步只用 $kr=rk$。于是 $Lr=0$。自伴元 $pkp$ 的 C* 谱演算给

$$
L\ge\bigl(1-\|pkp\|^2\bigr)1.
\tag{28.12}
$$

当右侧系数严格正时，$L$ 在原 $A$ 内可逆，左乘 $L^{-1}$ 给 $r=0$。零角情形由零槽处理；若 $p=0$ 则 $h=0$，若 $s=0$ 则 $k=0$。证明没有变化输入的 $D$ 极限。∎

**几何 28.3（三个平方范数的联合检测）。** 在任意忠实含单位 Hilbert 表示中，对每个向量 $\xi$，(28.7) 准确写成

$$
\|q\xi\|^2+\|tp\xi\|^2+\|qkp\xi\|^2
=\langle\xi,L\xi\rangle
\ge(1-\|pkp\|^2)\|\xi\|^2.
\tag{28.13}
$$

它依次检查角外分量、进入第一角后留在第二角外的分量，以及经实际 $k$ 作用后离开第一角的分量。严格间隙不容许三者同时遗漏非零向量。余项的像恰被 (28.11) 同时送进这三个核。三个平方范数是数学表示中的几何，不是三份新物理读数、准备或仪器。若间隙条件失败，本定理既不构造非标准 $D$，也不否定原分类；尤其没有以 $C^*(1,h,k)$ 内的本质性控制可能位于其外的 $r\in A$。

## 29. 复用整个第二角供应的准确参数

**定义 29.1（同一完成列与记号对应）。** 取

$$
B=M_{3^\infty},\qquad A=M_3(B),\qquad
p=E_{11}+E_{22},\quad q=E_{33},\quad
h=E_{11}-E_{22},\quad e=E_{12}+E_{21}.
\tag{29.1}
$$

原 $D$ 满足定义 28.1 的完整 $\mathsf H_A(D)$，不增加任何正则性或代数性前件。对任意完成系数取

$$
x,y\in B,\qquad x^*x+y^*y=1_B,\qquad
w=E_{13}x+E_{23}y,\quad u=ww^*,\quad s=u+q.
\tag{29.2}
$$

不要求等右 Gram、可逆、正规、相互交换或有限阶段性。所用整个第二角及同一普通符号**直接复用推论 20.1 的证明 (20.1)–(20.8)**：在定义 19.1 中取 $\mu=1$，其部分等距 $u$、投影 $P_0$、角单位 $P$ 分别对应本节的 $w,u,s$。于是 $w^*w=q$、$u\le p$，且同一个旧 $D$ 在整个 $pAp$ 和整个 $sAs$ 上都等于 $K_\sigma$。这些是同一实际原代数中的角，不把抽象同构当作 $D$ 的协变性，也不把完成投影 $u$ 当作有限阶段投影。

为读取下两节的实际输入，沿用 (20.2) 的同一个坐标接口；记 $z_q=E_{33}z$，准确写成

$$
\Phi:M_2(B)\longrightarrow sAs,\qquad
\Phi\begin{pmatrix}a&b\\c&d\end{pmatrix}
=w a_q w^*+w b_q+c_q w^*+d_q.
\tag{29.3}
$$

这是整个完成角的保单位 $*$-同构；其逆坐标、实际偶维稠密模型、角内全部原调用继承和同号供应均已由 (20.1)–(20.8) 支付。具体地，(20.6)–(20.8) 的共同子角在此为 $uAu\subseteq pAp\cap sAs$，其中 $z\mapsto w z_q w^*$ 带入非交换的 $B$，同一对原标签的同一个非零交换子迫使符号相同。这不是为新输入重立一个角分类、矩阵单位或取向定理。

**复用 29.2（供给新输入的前件）。** AH71.2、72.1 与上述 20.1 的完整角供应已经支付定理 28.2 的 (28.4)。下文的伴轴 $f=i(w-w^*)$ 不同于定义 19.1 中的 $f=P_0-q$；两者都位于同一个已分类的整个 $sAs$ 中。下两节只核对新的 $k_\theta,k_c$ 与此伴轴的实际平方、反交换及压缩，保留原输入的全部相关背景；不重复计入纯双边或第二角供应成果。

## 30. 任意归一化列的全部实旋转输入

**推论 30.1（完成列的全部旋转及其相关背景）。** 对定义 29.1 的每份原完成列及每个实 $\theta$，定义实际自伴输入与伴轴

$$
k_\theta=\cos\theta\,(u-q)+\sin\theta\,(w+w^*),
\qquad f=i(w-w^*).
\tag{30.1}
$$

则对全部 $R,T,\theta\in\mathbb R$，有

$$
\boxed{D(Rh,Tk_\theta)=\frac{\sigma i}{2}[Rh,Tk_\theta].}
\tag{30.2}
$$

证明。在 (29.3) 的坐标中，$u-q,w+w^*,f$ 分别为 $\operatorname{diag}(1,-1)$、$\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$、$\left(\begin{smallmatrix}0&i\\-i&0\end{smallmatrix}\right)$，三者平方均为角单位且两两反交换。故 $k_\theta^2=f^2=s$、$k_\theta f=-fk_\theta$；它们都是同一实际完成 $A$ 中的元素。又

$$
pk_\theta p=\cos\theta\,u,\qquad
\|pk_\theta p\|=|\cos\theta|.
\tag{30.3}
$$

这里 $q\ne0$、$w^*w=q$ 保证 $u\ne0$、$\|u\|=1$。若 $\sin\theta\ne0$，严格间隙及复用 29.2 支付定理 28.2 的所有前件，给 (30.2)。若 $\sin\theta=0$，则 $[p,k_\theta]=0$，直接以任意环境输入 $b=Tk_\theta$ 消费定理 8.1，仍给同式。$R=0$ 或 $T=0$ 用原零槽。两分支共同覆盖全部实 $\theta$，没有让 $D$ 沿 $\theta$ 连续延拓。∎

当 $\cos\theta=0$ 时，输入为 $T\sin\theta\,(w+w^*)$；这是 19.2、20.1 已支付的整个标量总右 Gram 纯双边族的子情形，全部归一化完成列和任意实幅度均已覆盖，不作为这里的新内容。$\sin\theta=0$ 的分块背景也直接复用 8.1。这里增加的是保留 $\sin\theta\cos\theta\ne0$ 相关背景时的原值识别。

例如任意酉 $v\in B$ 下

$$
x=\frac{\sqrt3}{2}1_B,\qquad y=\frac12v,
\qquad x^*x=\frac34 1_B\ne\frac14 1_B=y^*y
\tag{30.4}
$$

取 $\theta=\pi/4$、$T\ne0$ 时，$Tk_\theta$ 的 $33$ 块为 $-T1_B/\sqrt2$，$12$ 块为 $T\sqrt3\,v^*/(4\sqrt2)$；这些非零相关背景完整保留。该实际输入既不是 16.2 的纯等右 Gram 双边，也不是 19.2、20.1、25.2 或 27.1–27.2 的纯双边输入。若改取 $\theta=\pi/2$，同一列便是已付纯双边，不能再次计为新输入成果。未知 $D$ 始终没有被拆成两条单边响应之和。

对未缩为零的两根轴，$h^2=p$、$k_\theta^2=s$，而 $p+s=1+u\ge1$。若一实际投影同时支撑 $h,k_\theta$，则它支撑各自的平方，故大于 $p,s$；又 $s\ge q$，只能为 $1$。因此不是将两输入同时装入一个已付真偶角来应用其分类。零幅度支仍由零槽保留，不用此共同支撑论断。

## 31. 保留原输入的非标量算子振幅

**推论 31.1（严格收缩算子振幅的完整混合值）。** 对定义 29.1 的任意完成归一化列，任取

$$
c=c^*\in B,\quad\|c\|<1,\qquad
 d=(1_B-c^2)^{1/2},\quad c_q=E_{33}c,\quad d_q=E_{33}d,
\tag{31.1}
$$

定义同一个实际原输入

$$
\begin{aligned}
k_c&=w c_q w^*+w d_q+d_q w^*-c_q\\
&=\begin{pmatrix}
x c x^*&x c y^*&x d\\
y c x^*&y c y^*&y d\\
d x^*&d y^*&-c
\end{pmatrix}\in A_{\rm sa}.
\end{aligned}
\tag{31.2}
$$

则对所有实 $R,T$，不另加等 Gram 或角分类假设，有

$$
\boxed{D(Rh,Tk_c)=\frac{\sigma i}{2}[Rh,Tk_c].}
\tag{31.3}
$$

证明。连续 C* 谱演算只用于已知 $c$，给 $d=d^*\ge0$、$cd=dc$、$c^2+d^2=1_B$。在同一准确坐标 (29.3) 中，

$$
k_c=\Phi\begin{pmatrix}c&d\\d&-c\end{pmatrix},\qquad
f=\Phi\begin{pmatrix}0&i1_B\\-i1_B&0\end{pmatrix}.
\tag{31.4}
$$

逐块相乘得两矩阵的平方均为 $I_2$，乘积之和为零；故 $k_c^2=f^2=s$、$k_cf=-fk_c$。同时

$$
pk_cp=w c_q w^*,\qquad
\|w c_q w^*\|=\|c\|<1.
\tag{31.5}
$$

范数的一向界来自 $\|w\|=1$；反向由 $w^*(w c_q w^*)w=c_q$ 得到。复用 29.2 已支付两个完整角的共同符号，因此定理 28.2 直接给 (31.3)，包括负幅度与零槽。没有对未知 $D$ 作算子振幅展开或输入极限。∎

这里两条环境边的实际系数是 $xd,yd$，准确满足

$$
(xd)^*(xd)+(yd)^*(yd)
=d(x^*x+y^*y)d=1_B-c^2.
\tag{31.6}
$$

各自右 Gram 可以不同，$c$ 不必与 $x,y$ 交换；(31.2) 的相关对角块和 $12$ 背景全部保留。响应识别针对原来的 $k_c$，没有把 $xd,yd$ 重新归一后代入另一标签，也没有用未知响应的齐次性处理任意右乘算子。$c=0$ 是 19.2、20.1 已支付的纯双边情形，不计新增；$c$ 为严格收缩实标量时给 30.1 中正弦非负的一支标量旋转，30.1 另外保留全部符号的正弦。非零算子 $c$ 所规定的对角、$12$ 背景和原边系数共同组成 (31.2) 的同一个输入。可另取标量端点 $c=\pm1_B$、$d=0$，此时由 $[p,k_c]=0$ 及 8.1 得同式；不据此扩展到任意 $\|c\|=1$ 的非标量边界。

**范围 31.2（与既有纯双边族的准确范围）。** 本节没有取得任意环境整行。16.2 允许 $x^*x=y^*y$ 任意退化且总右 Gram 不限有限谱；27.2 已覆盖奇数阶段 UHF 中所有有限谱总右 Gram 的纯双边，包括非可逆、非标量总 Gram 及不等右 Gram。两项的原输入域都超出本节归一化列的纯双边子情形；30.1、31.1 则保留指定关联背景，供应另一类原输入。(30.4) 的列取 $\theta=\pi/4$、$T\ne0$ 时有非零 $33$ 和 $12$ 背景，不属于这些纯双边族。反向取 $B$ 中非零真投影 $r_0$，$b_+(r_0)+b_-(r_0)$ 同时由 16.2 和 27.2 支付，总右 Gram 为 $2r_0$，不等于任何纯双边 $T(w+w^*)$ 的 $T^2 1_B$。若非零 $Tk_c$ 等于这个旧纯双边输入，其 $33$ 块先迫使 $c=0$；若非零 $Tk_\theta$ 等于它，则 $33$ 块先迫使 $\cos\theta=0$。两种情形都遇到同一非标量总 Gram 障碍；这只比较输入族，不削弱既有识别。

特别，纯双边 $y=2x$ 的总右 Gram 为 $5x^*x$；凡其谱有限，原值均已由 27.2 支付，不要求它为标量或可逆。常数归一化列 $x=1_B/\sqrt5,y=2\cdot1_B/\sqrt5$ 的全部纯双边实幅度也是 19.2、20.1 已有子情形。一般无限谱 $5x^*x$ 不能靠有限谱逼近、这份归一化或标量 $T$ 传入未知 $D$；除非另有已付结果适用，仍不在这些纯双边结论内。$\|c\|=1$ 的一般非标量输入、任意背景与任意双边的和、一般奇数阶段 UHF 全域分类和一般原域自动双线性均未由本节取得。

## 32. 复用边界与承重差额

**归属 32.1（条件纸面综合）。** 定理 7.1 的环境非对角识别、定理 8.1 的分块环境整行、定理 16.2 的任意等右 Gram 双边、定理 19.2 和推论 20.1 的整个标量总右 Gram 纯双边族、23.2 的局部谱对探针、24.1 的有限对称谱中心化余量行、25.2–25.3 的正可逆有限总右 Gram 双边及实际整个角供应、27.1–27.2 的全部有限总右 Gram 自然支撑纯双边，以及 AH70 的偶维完成模型分类、AH71–72 的实际偶角及同号、W119–120 的完整角继承，均属已成复用。(20.1)–(20.8) 已供应本节整个第二角与共同符号；定义 29.1 只写其参数对应和应用坐标，不另计构造、分类或符号拼接成果。命题 21.1 保持其全部 P2 与明确 PB 失败的准确范围，不能当作完整 $\mathsf H_A(D)$ 的反模型。

本节 $\texttt{repo-derived}$ 差额是一般实际双角的三项正证书 (28.7)：在 (28.6) 的同一个固定余项上，三项各自消灭它，而总和为 $1-(pkp)^2$，严格压缩遂使它为零。对原三进对象，复用整个第二角供应后，这给出 (30.2)、(31.3) 保留相关对角和 $12$ 背景时的原混合值识别。纯双边的 $\cos\theta=0$ 或 $c=0$ 子族全部计为 19.2、20.1 的复用，$\sin\theta=0$ 子族计为 8.1 的复用；不将两次 7.1 的应用或已付角供应另立为新基础定理。相关背景结论没有把未知行拆开，也没有宣称本族包含全部 16.2 等 Gram 族。正间隙是所选输入的可验证数学性质，不是新增的 $D$ 公理。

C* 正平方、连续函数演算、正元严格下界与可逆性、矩阵单位和忠实表示的成熟工具沿定义 10.1、15.1、17.3 的既有归属使用；所有本次所需乘法等式已在证明内展开。Peirce 术语沿 Hanche-Olsen–Størmer，*Jordan Operator Algebras*，§2.6.2、Lemma 2.6.3；UHF 模型沿 AH75.2 所引 Blackadar，*Operator Algebras*，II.8.2.2(iv)。不援引未核对适用范围的局部导子、两投影或极分解分类来消除原余项。Alfsen–Shultz 的 dynamical correspondence 仍有定义 18.1 已说明的线性前件，不能反向给任意总 $D$ 补上线性。没有文献穷尽、历史原创、外部开放问题解决、Lean/kernel 核验或物理最低成本主张。

[《无锚三相配平的有界轨道与有限历史预算》定理 40.1](AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md#40-原支配残差的个别标记桥与普遍消失) 的纯三相位受支配残差消失、41.1 的任意仿射漂移推广及 41.2–41.3 的同对象对称化与共同反例归约均属已付复用。该卷定理 43.3 进一步支付：任意真实含幺 magma、任意 $U$、处处有限非负零对角且可有向的总核，在全部有序且保留原括号的完整 $(R)$ 和两个普遍第三标记返回 $\mathrm C_3$ 下，具有完整 $\mathrm C_1,\mathrm C_2,\mathrm{UC}$ 及同一原 $M$ 上的完整仿射复 Hilbert 表示；对称性、全部有限负型和平方根三角均为结论，原实际漂移保持任意。这个 $(R)+\mathrm C_3$ 标定桥不再列为缺口；原始 $(R)\Rightarrow\mathrm C_3$ 仍未解决。本节的 C* 角几何不代付该原始返回或任何实际物理来源。

## 33. 不缩减的全文来源与七项量子消费者

**定义 33.1（逐层固定的完整合取）。** 完整物理来源严格保持定义 10.2、15.2、18.2 及 AH28.1、57.1、64.2、75.1 的同一个 $\mathcal C_{47}^{\rm pin}(\Omega;S,D)$：SQ47.1–47.13 的全部定义、合同、公式、量词和每项递归纳入的固定上游全文同时合取；原根、所有静默及其他原静态分支不改为本节三进对象。SQ 主源沿其 1.3、39、41.1、47.1 解析，`dcaebc0b9ca5a3a463fd8cfd161d38967df28668` 与 `0aa11dbc3dc337d667b98900673e07d67b99bf46` 的相应层级不变，OP/PT/PB/SM/C/AQ/R3/W/FR/XV/SF 单项身份仍为 `f24d1138a7b994da16abd9a47affedea64ea44ce`。AH22.1 的 `2addd6f369b7387226c2b0cc984623dd3efe40a1` 及其保留的 AH12.1 上游 `39a0505470ea889dd9d4301ad60cd9506a5e8b58` 不被直接读取身份压平。

同时完整纳入 AH64.3 第1–7项全文；按 AH77.3 的完整来源补充，合取 SF105.1 第1–7项和式 (105.1)–(105.7)，包括 SF96.1 及每项全部递归上游；合取 PB153.2 全文，包括 PB147.3、141.3、137.3、122.1 及每项固定上游。AH77.3 的直接读取身份为 `b448aaa7fafd2045f8bbe541c39ee9a9c4e6b777`；其中 SF105.1、PB153.2 仍按 AH66.1 的 `02b9b7f3691360aa745ed531ba77a61c78e60a7b` 读取，各自内部身份不变。SF98.1 所定 SF96.1 仍为 `efef304808f06caec5026b013ca9707c8495aa23`，SM86.1、78.2、43.2、49.1、61.1、69.1，C199.2、194.2、186.1–186.7、181.3、171.1–171.7、160.3、155.1、145.1–145.7，PT122.1，A8.3–8.4、14.2、30.1、53.1，R3 8.1–8.5、80.1，W95.2、116.1及递归全文，仍按 SF98.1 的 `23dae741512cdf450fc5b2d76b63ed51780f9915` 与各自原文钉版解释。SF 的 PT 为原多项式 PB 运输卷，SQ 的 PT 为配平三角卷，不因简称相同而合并。

以下七项说明每项准确前件与所得结论；它们与上述全文共同合取，不替代任何未逐行重印的原来源量词，也不宣称这些物理前件已经由数学角供应。

1. **复 Hilbert、可观测量与实际相干叠加。** 在已整体分类的 $pAp,sAs$ 上，已有 AH64.1、75.1 的计算给 $a\star b=a\circ b-iD(a,b)$，复双线性延成通常或相反 C* 乘法，保伴随、准确锥、角单位和范数；全部有限旧复 Gram 为正，每个原限制评价有数学 GNS，向量平方范数分别为原 $\gamma(p),\gamma(s)$，零角质量给零向量。每份新混合对只另外得到

   $$
   S(Rh,Tk)-iD(Rh,Tk)
   =\begin{cases}(Rh)(Tk),&\sigma=1,\\(Tk)(Rh),&\sigma=-1,
   \end{cases}
   \tag{33.1}
   $$

   其中 $k=k_\theta$ 或 $k_c$。这不构造全环境的双线性、结合乘法或全部有限旧复 Gram。实际相干仍须同一 $\Omega/\mathrm{native}$、具名可取得标签、指定跨评价配对、全词共同 $K/J/q$、parent/ready、合法控制和实际相干准备。SF105.1 式 (105.1) 中同一复 $V$、半正定 Hermitian $K$、全部原 $\xi_\gamma$ 和总集合映射 $J_a$ 保持全部原标签、全部 $z,w\in V$、空词与任意有限词及正夹读量词，词先实际复合再取有限复线性包；不改为逐评价独立核，不预给 $J$ 线性、$J_0=0$ 或 $J_1=I$。共同全词的可见恢复仍按原词消费者，不从数学 GNS 推出实际准备或全 $B(H)$ 的可取得像。

2. **原态、效果、Born、全菜单与质量。** 准确锥给数学效果区间及未归一权 $\gamma(e)$；实际 Born 仍须同一原事件绑定、接受归属和实际完整菜单 $\sum_j e_j=1$，并且 $m_\gamma>0$，才有 $p_\gamma(j)=\gamma(e_j)/m_\gamma$。角菜单还须原实际条件化、$\sum_je_j=p$ 或 $s$ 及严格正角质量，才用对应的原角质量作分母。全部原准备、共同根、真实独立抽签、mark、$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定处处有限强度尺、P9每支独立 $W_e$、全部原目标、每个原中间切口和固定支持全质量不删。互探的有限维／最小可见／实尺度范围、各块自身 AS/EC、菜单外 OB 及忠实二维到三维全质量适配器仍按原来源。具名分析沿先原 $g^*$、再原 $d_s^*$、最后同一原根的合法实际读取顺序；同矩阵不合并不同程序。原零、不等、次归一质量、中心比较权、经典、不等维、静默及非正常支保留，零质量不作除法。一般原态不自动成为指定物理表示的正常密度算子；无限菜单另守正常性、前对偶、可数可加和收敛。

3. **真正相关联合、复合与张量。** 张量识别只在同一个实际非零有序相关联合中，原全词 $K/J$、交叉零、同一旧局部乘法、忠实同向交换的局部腿、共同实现、联合生成分离及所需重数齐备时消费。每个要求局部全矩阵的消费者仍须完整全矩阵前件；全部相关输入、所有实际非零中央对、经典、不等维、静默块、实际副本和每层递归同源参考保持。合格局部全矩阵 $M_d,M_r$ 共同生成的联合才识别为 $M_d\otimes M_r$；具体 Hilbert 重数或不可约性另守原条件。相同边缘、分别可达、共同符号、数学同构、$p,s$ 两角及一个辅助张量表示均不供应实际共同来源。

4. **typed CP、Kraus 与整台递归参考。** 每条实际原细分支 $r:A_0\to B_0$ 的全部合法 typed 前后接、真实未归一后上下文、每份完整输出的每个仍合法未来和每份原评价，须满足 SF式 (105.3) 的 $\gamma_{A_0}(\beta_r b)=\gamma_{B_0}^{r}(b)$、反变合法复合、typed分区、全未来自然性、质量运输及原箭头商下降，才接 C13950–52 的唯一正次单位回溯。CP 还须原完整同标签单位区间比较，或整台实际箭头可再次应用的完整参考规则；单独正延拓不等于 CP。SF式 (105.4)–(105.6) 的两端共同真支持、忠实同向交换系统腿与 $M_2$ 腿、三颗实际投影及 $I_2$ 的实张成、全部支持内补、所有原相关正输入与决定锥评价上的交织夹界、每个所需有限深度和每个正精度、精确根身份与累计支持运输全部保留。累计支持不换成新环境单位，下一层携带整个系统和环境及全部成功／失败／细记录／port／post-port输出和各自全部合法未来；真遗忘、实际返回及合法复合也在原规则类。C13958–64、66–73 已付的混合身份、完整有限参考链和条件 CP 直接复用，不重列为缺口；有限深度全称不要求一条物理无限链。Kraus、密度和迹类公式只在合格有限全矩阵域，或另付适用正常物理表示、指定前对偶及分解收敛域消费；一般子代数不自动是全 $B(H)$，也不自动有可数 Kraus 和，其指标不自动是原细记录。在上述原过程前件及合格有限全矩阵表示中，已有消费者给

   $$
   \beta_r(b)=\sum_\nu V_{r\nu}^*bV_{r\nu},\qquad
   V_{r\nu}:\mathcal H_{A_0}\to\mathcal H_{B_0};
   \tag{33.2}
   $$

   一般表示域只使用其实际已付的正规性和收敛版本，不把 (33.2) 无条件扩展到本节整个三进代数。

5. **完整仪器、TP、条件更新与 Lüders。** 全输入运输、完整 typed 菜单和接受端、整个环境及上述全部输出未来、真正分组遗忘、AC、精确 $N_u$、X/Xs、每份原平方根词和自身接受条件均须来自同一原仪器。正夹心只给代数入口，数学平方根不等于可执行原词；正次单位仅给 TNI，完整 typed 单位分区 $\sum_r\beta_r(u_{B_r})=u_{A_0}$ 才给 TP，不同输出类型按原接头处理。Lüders 另需同一完整输出的投影效果、像内每条射线保持及完整输出校准，同效果、同概率或统计重复性不代付。只有严格正的实际输出质量可归一；零和失败输出保留类型、记录及全部未来。细输出相加须真实粗事件及分组接头，密度／迹类／Kraus 式仍守第4项准确表示与收敛前件。在该合格密度域内，既有消费者的未归一输出为 $\rho_r=\sum_\nu V_{r\nu}\rho V_{r\nu}^*$；$\operatorname{Tr}\rho_r>0$ 时更新为 $\rho_r/\operatorname{Tr}\rho_r$。在另已支付上述 Lüders 射线及完整输出校准的同一表示中，才将该原分支识别为 $\rho\mapsto P\rho P$，正输出质量时取 $P\rho P/\operatorname{Tr}(\rho P)$，不把任意同效果分支替换成它。

6. **全部合法历史、全未来、真遗忘与真实 Return。** 全部合法顺序、自适应、并行历史，每份完整输出的每个仍合法未来，整个环境、参考副本、细记录和泄漏，停止、拒绝、销毁，真正分组遗忘、同数两侧及同数逆向真实 Return 全部保持。CountRead 要求实际读后活动 ready、同一接受叶的完整活动输出、第一合法消费者，以及读后同一完整活动输入对全部合法未来的真实返回；终端表、分母、地址、失败及输出类型不改成旧 ready。负提升两条活路的分别受控实现和相干聚合分别供应；数学负号不制造活路。原精确正生成 $B$ 与另名闭正生成 $B_{\rm cl}$ 保持区别，两只独立九叶彩票、各自第九空程序、十六拒绝叶与相干 $I_3/3$ 返回保留身份和记录。既有 native 初始取得、指定有限树、被动精确混合解码、CountRead 精确表的支持事件及整支质量、C13965 的同一有限返回数值刚性和 C13950–73 的下降／参考成果均在原平稳、真实同源、同初始版本和准确适用域继续使用；它们不是缺失的成果，也不代付完整输出全未来 Return。C128385–392 的经典自对障碍、补元平衡、单位／交替恢复及其明确实双线性前件下的原子切向分类同样作为复用，不给当前任意总 $D$ 偷加该前件。无限历史、无限或非离散记录、可数可加、正常性、指定前对偶及收敛仍须原扩展来源。相同数学算子不合并原程序、读序、原 $q$ 零集、AC方向或未来权限；未定义请求保持未定义。在上述合法复合、每层完整来源及过程绑定均齐备的域，已有消费者给一条实际有限历史的未归一质量 $\gamma_{A_0}(\beta_{r_1}\cdots\beta_{r_n}(u_{A_n}))$；真正分组才允许对细历史质量求和，原真返回等式才允许返回识别，不以该公式制造合法历史或返回设备。

7. **动力、物理钟、能量与共同正作用量。** 同一旧全域乘法、保持原域的实际流、真实相位及原门序列、同一实际连续可逆 CPTP 一参数过程和实际逆、物理钟及单位、所需强连续酉实现、一般无界生成元域、Hamiltonian 能量解释、共同仪器及同一个正 $\hbar$ 齐备后，才在原适用表示与可微域消费 SF式 (105.7)：

   $$
   U(t)=e_\star^{-itH/\hbar},\qquad
   i\hbar\dot\psi=H\psi,\qquad
   i\hbar\dot\rho=[H,\rho]_\star,\qquad
   \dot b=2D(H,b)/\hbar.
   \tag{33.3}
   $$

   向量微分限于相应自伴生成元域，密度微分限于适用迹类可微域，观测量限于实际可微域；相反取向仍用识别后的同一乘法。原 $\sigma,t_0,d$、固定域、resolvent 和 $3s+r\le1$ 保留自身设备、参数、定义域及量纲，不与本节取向、$c,d,\theta,R,T$ 或三项证书混同。数学指数、范数路径、逆元、迹、辅助钟或有界内导子不供应实际流、能量解释、控制成本、无界域及跨装置共同作用量。

**边界 33.2（实际接受关联与完整目标）。** 对字面旧程序 $\tau;T_P$ 的指定接受族，尚须在全部原准备、中间切口、参考／副本、允许的分析词和分析树、原坐标、完整菜单及固定支持全质量的域中，给该指定接受族到同一原实际完整菜单与接受端的、准备无关的准确接受关联，保持原支持和未归一标尺。它是当前接受族的关联要求，不被加强成两台整仪器或全部历史恒等；C13923.3 式 (23.7) 的原前接菜单事件是一个明确充分接口。矩阵相等、存在某张菜单、纯态校准、合法逆字和精确矩阵综合均不生产这份关联。本节也没有构造 CountRead 的同一接受完整活动输出、读后 ready、第一合法消费者及全输入／全合法未来 Return。这是所述原接口的未付供应，不是整个 $\Omega$ 的不存在断言。

同一原 $\Omega$ 的所有准备、事件、标签、质量、参考、副本、相关联合、控制、钟、旗标、切口、全菜单、固定支持、记录、拒绝、停止、销毁、泄漏、遗忘、两侧与逆向 Return、所有输出及每个合法未来均保留。七项须在同一个原实现上共同成立，不分别换源；不用 Hilbert、Born、CP 或量子相干控制反向制造物理 producer。一般原域的 PB153.2 联合预算、一般奇数 UHF／混合行分类及完整量子起源目标继续未决，已付《无锚三相配平的有界轨道与有限历史预算》40.1–41.1 的各自残差类及 43.3 的完整 $(R)+\mathrm C_3$ 仿射几何不在此未决清单内；原始 $(R)\Rightarrow\mathrm C_3$ 仍保留。

## 34. 三块联合几何与完整中文解释

**解释 34.1（同一答案不能在两个角里各藏一份误差）。** 原世界、原表和问题都不换：第一输入在前两块分别指向正、负方向，第三块为零；第二输入可以同时连向这两块，也可以带着与这些连线相关的对角和横向背景。每个适用小角里的整张表及单角对环境答案的约束均由既有定理支付，但这些知识不能让未知函数自动把两条边相加。

这里让两份已有角知识对准同一个答案。先从第一根轴看，标准交换子之外的余量只能留在第一角里，并与第一根轴交换；再交换两输入，从第二根轴看，同一余量还必须留在第二角里，并与第二根轴交换。反对称性保证两边谈的是同一件东西，不能一边选一个余量。接下来只用三个非负平方：看角外、看进第一角后仍在第二角外、看经第二根轴后又跑出第一角。每一项都消灭这个固定余量；三项相加却是单位减去第一角中第二轴压缩的平方。只要该压缩严格短于单位，三项共同检测便有严格余地，非零向量无处同时隐藏，余量只能为零。

具体在三块完成代数中，两条边组成一根归一化列，只要求总平方强度为一，不再要求两边各分一半。它产生一个实际部分等距，把第三块和前两块中的一份投影配成第二个完整二阶角；每块内部仍可无限维，系数也可来自任意完成层。整个第二角和共同取向直接由 20.1 的既有供应取得：(20.6)–(20.8) 在两个角的实际共同子角中带入 $B$ 的一对不交换标签，对同一个旧输出比较两份公式。定义 29.1 只说明记号对应；不重建或重计这份已付供应，也不把完成投影误当有限阶段或给未知函数添坐标协变。

标量旋转的全部角度都能处理：连线与相关背景同时非零时，压缩长度严格小于一；纯双边时直接复用 19.2、20.1，连线恰为零时直接复用 8.1，不必让未知函数通过角度极限。更进一步，让转角振幅换成任意严格收缩的自伴算子 $c$，同时保留由它规定的 $\sqrt{1-c^2}$ 连线以及整份相关背景，压缩长度就准确为 $\|c\|$。因此本节认回的是这整份原输入的旧响应，两边平方强度可以不同、系数可以不交换；没有先换成一根标准化新边再冒称回答了原问题。两输入的共同支撑为整个单位，故也不是把它们塞进一个真偶角来重复旧分类。

几何的简洁限于这份有限三项正证书和它实际覆盖的输入。16.2 已识别任意等右 Gram，27.2 已识别所有有限谱总右 Gram 的纯双边，包括退化和非标量输入；这些原输入域超出本节归一化列的纯双边子情形，不重复计为新增。未被其他已付结果覆盖的无限谱纯双边、任意背景和任意双边的和仍不能由此推出；这里的相关背景族也不属于既有纯双边输入，不能据此宣称全体输入上的强弱关系。这些三块或二阶角是关系结构，不是物理三维、三台读器或新准备；较大的结构仍是同一个原 C* 角网及其未知全响应。已分类角内的复乘法、正 Gram 和数学 Hilbert 表示照用，指定混合值有所增加；全环境复乘法、实际 Born 全菜单、真正相关联合、typed 仪器全部输出未来、读后真实返回、正常性、物理钟和共同作用量仍须上述完整原来源逐项供应。完整量子起源目标没有缩小，也没有被这份部分输入定理宣布完成。

## 追加锚（本行以下为增补区）
