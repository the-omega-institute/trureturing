# Auric · FIB-ATOM 续篇：二元来源的三维二阶关系完成

从 $(2,3)$ 的递归读出，到距离、接缝与相位结构

**定义 0.1（关系完成的适用对象）。** 本卷的原始对象是有序树，组成是树的一个观察，数量又是组成的一个观察。所谓关系完成，是在明确的来源族、操作族和目标读出下，补足支持这些任务的关系变量。线性响应空间的维数、确定状态的内在维数、概率族的参数数目和位置空间的维数分别定义，不互相替代。下列条目给出 FIB 合同中的综合推导；对称幂、Gram 关系、网络消元、Gaussian 积分、Bloch 表示及正矩阵几何作为注明来源的经典中间步骤使用，不作为独立的新理论。

## 1. 连续数量读出与二元组成

**定义 1.1（自由来源、组成与推进）。** 采用自由有序二叉树

$$
T::=\alpha\mid\beta\mid\langle T,T\rangle,
\qquad
\rho(\alpha)=\beta,\quad
\rho(\beta)=\langle\beta,\alpha\rangle,\quad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
$$

其组成映射及数量行向量为

$$
c(\alpha)=\binom10,\qquad c(\beta)=\binom01,\qquad
c\langle s,t\rangle=c(s)+c(t),\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad \ell=(2,3).
$$

于是 $c(\rho T)=Mc(T)$。对任意实组成 $c=(a,b)^T$ 定义 $y_n=\ell M^nc$；树来源的实际组成属于 $\mathbb N^2\setminus\{0\}$。组成相同不意味着树相同。例如 $\langle\alpha,\beta\rangle$ 与 $\langle\beta,\alpha\rangle$ 左右次序不同，但均观察为 $(1,1)^T$。本定义取自 [FIB 关系延拓几何，定义 1.1、1.3](https://github.com/the-omega-institute/trureturing/blob/b19dc63ed2b2007d8d6de4c50366815f0d032ba4/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md)。

**定理 1.2（两次连续数量的组成恢复）。** 对上述任意实组成，

$$
y_0=2a+3b,\qquad y_1=3a+5b,\qquad
 y_2=5a+8b=y_0+y_1.
$$

前两个读数唯一决定组成，且

$$
O=\begin{pmatrix}2&3\\3&5\end{pmatrix},\quad
\det O=1,\quad
O^{-1}=\begin{pmatrix}5&-3\\-3&2\end{pmatrix},\quad
a=5y_0-3y_1,\quad b=-3y_0+2y_1.
$$

整数组成的恢复无需分母。三个连续读数只在二维平面 $y_2-y_0-y_1=0$ 上变化。

证明。乘出 $\ell M=(3,5)$、$\ell M^2=(5,8)$。行列式为 $10-9=1$，所列逆矩阵直接给恢复式。更一般地，若读出行是 $q=(p,q_2)$，则两步观察矩阵为

$$
\begin{pmatrix}p&q_2\\q_2&p+q_2\end{pmatrix},
\qquad \det=p^2+pq_2-q_2^2.
$$

行列式非零就可恢复，故此性质不由数字 $2,3$ 独占；整数无分母恢复则需该整数行列式为 $\pm1$。第三个读数与前两个之间的等式排除了第三个独立输入。$\square$

**定理 1.3（原子数量序列的精确线性最小性）。** 约定 $F_0=0,F_1=1$，$F_{n+2}=F_{n+1}+F_n$。对 $c=c(\alpha)$，有 $y_n=F_{n+3}=2,3,5,8,\ldots$。在固定有限维实线性合同

$$
y_n=r^TA^nv\qquad(n\ge0)
$$

下，其最小状态维数为 $2$。

证明。$M^2=M+I$ 给 $y_{n+2}=y_{n+1}+y_n$，初值为 $2,3$，故得到所列 Fibonacci 序列。取 $A=M,v=(1,0)^T,r^T=\ell$ 给二维上界。任一 $d$ 维实现的两阶 Hankel 矩阵分解为

$$
\begin{pmatrix}y_0&y_1\\y_1&y_2\end{pmatrix}
=\begin{pmatrix}r^T\\r^TA\end{pmatrix}
\begin{pmatrix}v&Av\end{pmatrix}.
$$

左侧为 $\left(\begin{smallmatrix}2&3\\3&5\end{smallmatrix}\right)$，行列式为 $1$，秩为 $2$，所以 $d\ge2$。这里的秩论证遵循 [FIB 关系延拓几何，第六章](https://github.com/the-omega-institute/trureturing/blob/b19dc63ed2b2007d8d6de4c50366815f0d032ba4/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md) 的联合 Hankel 与线性实现合同；它不限制非线性编码的容量。$\square$

## 2. 对称二阶关系的三维线性完成

**定义 2.1（二阶关系提升）。** 令

$$
\nu_2:\mathbb R^2\longrightarrow\mathbb R^3,\qquad
\nu_2(a,b)=(a^2,ab,b^2)^T=(U,V,W)^T.
$$

三个坐标分别记录第一来源的自身关系、两来源的交叉关系和第二来源的自身关系。本卷在这一层取对称关系；若有序关系的交换产生独立信息，反对称部分须另行保留。经典支撑是 $\operatorname{Sym}^2(\mathbb R^2)$ 的三维性；[Mathlib 的对称代数定义](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/SymmetricAlgebra/Basic.html) 给出将张量乘法交换化的代数背景，本卷所用坐标和维数论证如下。

**定理 2.2（全部 FIB 二次读出的最小线性关系空间）。** 任意齐次二次读出

$$
f(a,b)=\lambda a^2+\mu ab+\nu b^2
$$

唯一写为 $f=L_f\nu_2$，其中 $L_f(U,V,W)=\lambda U+\mu V+\nu W$。若一个映射 $E:\mathbb R^2\to\mathbb R^d$ 使每个这样的 $f$ 都能经线性函数读出，则 $d\ge3$。

证明。所列公式给存在性。若 $\lambda a^2+\mu ab+\nu b^2$ 恒为零，在 $(1,0),(0,1),(1,1)$ 处依次得到 $\lambda=0,\nu=0,\mu=0$，所以这三个函数线性独立，并给因子化的唯一性。$E$ 的 $d$ 个坐标函数所张成的空间至多 $d$ 维，却必须包含这三个独立函数，故 $d\ge3$。此结论要求线性读取全部齐次二次响应；它不声称原始组成有三个确定性自由度。$\square$

**命题 2.3（确定组成的锥面与信息边界）。** $\nu_2$ 的像恰是

$$
\left\{(U,V,W):U,W\ge0,\ UW=V^2\right\}.
$$

对应矩阵 $\left(\begin{smallmatrix}U&V\\V&W\end{smallmatrix}\right)=cc^T$ 为秩至多一的实半正定矩阵；非零部分秩为一，内在维数为二。树组成的像进一步满足 $V\ge0$ 及整数来源限制。

证明。正向由平方和 $UW=a^2b^2$ 得到。反向若 $U>0$，取 $a=\sqrt U,b=V/\sqrt U$；等式保证 $b^2=W$。若 $U=0$，必有 $V=0$，取 $a=0,b=\sqrt W$。非零向量 $c$ 与 $-c$ 得到同一矩阵，除此之外秩一分解只差该符号；局部参数仍为二维。矩阵 $\operatorname{diag}(-1,0)$ 虽行列式为零却不是半正定，故并非所有行列式为零的矩阵都在像内。$\square$

## 3. Fibonacci 二阶闭合与平方序列的三维最小性

**定理 3.1（同一组成推进的二阶交换式）。** 对定义 2.1，

$$
\nu_2(Mc)=T\nu_2(c),\qquad
T=\begin{pmatrix}0&0&1\\0&1&1\\1&2&1\end{pmatrix}.
$$

这给出从 $c\mapsto Mc$ 到 $\nu_2(c)\mapsto T\nu_2(c)$ 的交换关系，并不增加原始输入。

证明。$Mc=(b,a+b)^T$，故三个输出分别为

$$
b^2=W,\qquad b(a+b)=V+W,\qquad
(a+b)^2=U+2V+W.
$$

恰为矩阵 $T$ 的三个分量。$\square$

**定理 3.2（实际平方读出的精确三维合同）。** 序列

$$
z_n=F_{n+3}^2=4,9,25,64,169,\ldots
$$

在固定有限维实矩阵、线性输出的合同 $z_n=r^TA^nv$ 中，最小维数为 $3$，且满足

$$
z_{n+3}=2z_{n+2}+2z_{n+1}-z_n.
$$

证明。置

$$
q_n=(y_n^2,y_ny_{n+1},y_{n+1}^2)^T.
$$

由 $y_{n+2}=y_n+y_{n+1}$，有 $q_{n+1}=Tq_n$、$q_0=(4,6,9)^T$ 和 $z_n=(1,0,0)q_n$，给三维上界。三阶 Hankel 矩阵为

$$
H=\begin{pmatrix}4&9&25\\9&25&64\\25&64&169\end{pmatrix},
\qquad
\det H=4(4225-4096)-9(1521-1600)+25(576-625)=2.
$$

任一 $d$ 维实现都有

$$
H=
\begin{pmatrix}r^T\\r^TA\\r^TA^2\end{pmatrix}
\begin{pmatrix}v&Av&A^2v\end{pmatrix},
$$

所以 $3=\operatorname{rank}H\le d$。直接乘法给 $T^3-2T^2-2T+I=0$，作用于 $q_n$ 后取首分量便得递推。若允许非线性输出，保留 $(y_n,y_{n+1})$ 并平方首分量仍足够；三维结论仅约束所声明的线性合同。$\square$

## 4. 固定共同来源的二阶统计与交叉信息

**假设 4.1（共同来源概率）。** 在一个固定概率空间上，随机有序树的组成为 $c=(a,b)^T$，且 $\mathbb E a^2,\mathbb E b^2<\infty$。定义原点二阶矩

$$
S=\mathbb E[cc^T]=\begin{pmatrix}U&V\\V&W\end{pmatrix},
\quad U=\mathbb E a^2,\quad V=\mathbb E ab,\quad W=\mathbb E b^2.
$$

Cauchy–Schwarz 保证交叉矩有限。概率是来源模型的假设，不意味着原始对象在本体上随机，也不意味着已有精确物理测量。

**定理 4.2（树来源二阶统计具有三维内部）。** 允许概率混合非空有序树时，二阶矩向量的可行集合在 $\mathbb R^3$ 中有非空内部，但只构成实半正定锥的受限子集。

证明。取四棵树 $\alpha,\beta,\langle\alpha,\beta\rangle,\langle\alpha,\alpha\rangle$。其二阶向量依次为

$$
v_0=(1,0,0),\quad v_1=(0,0,1),\quad
v_2=(1,1,1),\quad v_3=(4,0,0).
$$

以列顺序 $v_1-v_0,v_2-v_0,v_3-v_0$ 排列，得到

$$
\begin{pmatrix}-1&0&3\\0&1&0\\1&1&0\end{pmatrix},\qquad \det=-3.
$$

因此四点仿射无关，概率混合的四面体有非空三维内部。另一方面，对任意实 $r$，$r^TSr=\mathbb E(r^Tc)^2\ge0$；又因树组成 $a,b\ge0$，有 $V\ge0$。例如 $\left(\begin{smallmatrix}1&-1/2\\-1/2&1\end{smallmatrix}\right)$ 正定而不满足这一必要条件，所以树矩集合不能等同于全部半正定锥。非负未归一权重生成的树矩锥也有这些额外限制。$\square$

**命题 4.3（相同边缘不足以代替共同来源交叉矩）。** 来源 $A$ 在 $(1,1),(2,2)$ 上各取概率 $1/2$；来源 $B$ 在 $(1,2),(2,1)$ 上各取概率 $1/2$。两者的两个边缘分布分别完全相同，且 $U=W=5/2$，但

$$
V_A=5/2,\qquad V_B=2,\qquad
\mathbb E_A(a+b)^2=10,\qquad \mathbb E_B(a+b)^2=9.
$$

证明。任意非负整数对 $(a,b)$ 满足 $a+b>0$ 时，都可把 $a$ 片 $\alpha$ 叶与 $b$ 片 $\beta$ 叶以任意合法二叉括号组成一棵非空树，所列四个组成均可实现。两边缘都在 $1,2$ 上各有一半质量。逐项计算交叉积并使用 $\mathbb E(a+b)^2=U+2V+W$ 得到结论。因此共同来源的交叉关系不能由两个独立边缘替代。保存 $S$ 恰能保存全部二阶响应；它不恢复任意联合分布，也不保证任意树拼接合法。严格共同接缝的额外条件见 [FIB 关系延拓几何，第五章](https://github.com/the-omega-institute/trureturing/blob/b19dc63ed2b2007d8d6de4c50366815f0d032ba4/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md)。$\square$

## 5. 三次平方响应恢复同源二阶矩

**假设 5.1（统一来源推进）。** 对假设 4.1 的同一来源分布施加确定推进 $M$，定义

$$
s_n=\mathbb E[(\ell M^nc)^2].
$$

每个 $s_n$ 都以同一初始概率律为基准，不把三种未关联的制备当作同一个联合来源。

**定理 5.2（三量二阶恢复）。** 有

$$
\begin{pmatrix}s_0\\s_1\\s_2\end{pmatrix}
=\begin{pmatrix}4&12&9\\9&30&25\\25&80&64\end{pmatrix}
\begin{pmatrix}U\\V\\W\end{pmatrix}.
$$

该观察矩阵行列式为 $-2$，并有

$$
\begin{aligned}
U&=40s_0+24s_1-15s_2,\\
V&=\frac{-49s_0-31s_1+19s_2}{2},\\
W&=15s_0+10s_1-6s_2.
\end{aligned}
$$

证明。展开 $(2a+3b)^2,(3a+5b)^2,(5a+8b)^2$ 后取期望，得到观察矩阵。其行列式展开为 $-2$。还可令

$$
q=\frac{s_2-s_0-s_1}{2}=\mathbb E(y_0y_1),\qquad
S_y=\begin{pmatrix}s_0&q\\q&s_1\end{pmatrix}.
$$

由 $y_2=y_0+y_1$ 得到交叉式；由 $(y_0,y_1)^T=Oc$ 得 $S_y=OSO^T$，所以

$$
S=O^{-1}S_yO^{-T}.
$$

乘出这三个分量即为所列逆式。$\square$

**假设 5.3（统计取得合同）。** 若把定理 5.2 用于实际取样，须另给统一制备或统一来源分布、有限二阶矩、取样误差及读出干扰的合同。定理只给理想响应之间的代数逆，不断言未知单体可经三次无扰动读出取得这些精确期望。有限样本估计也须按相同逆矩阵传播误差，而不能把估计值自动当作真实矩。

## 6. 同源二阶量的距离、面积与三角边界

**定义 6.1（关系量的内积读法）。** 在一个实内积空间中，对两个向量 $u,v$ 令

$$
U=\|u\|^2,\quad V=\langle u,v\rangle,\quad W=\|v\|^2,
\qquad G(u,v)=\begin{pmatrix}U&V\\V&W\end{pmatrix}.
$$

定义三角形 $(0,u,v)$ 的面积为所张平行四边形面积的一半，即 $\operatorname{Area}(0,u,v)=\tfrac12\sqrt{UW-V^2}$。这是经典 Gram 与 Cauchy–Schwarz 结构在本卷二阶关系中的读法；Cauchy–Schwarz 的文献背景见 [Axler《Linear Algebra Done Right》的仓内条目](../../../Library/Quantum/axler2024innerproduct.md)。平方可积实随机变量构成的 $L^2$ 空间也是这样的内积空间。

**定理 6.2（FIB 同源响应的距离与退化判据）。** 在定义 6.1 下，

$$
\|u-v\|^2=U+W-2V,\qquad
\det G=4\operatorname{Area}(0,u,v)^2.
$$

行列式为零当且仅当 $u,v$ 线性相关，包含零向量情形；行列式正当且仅当它们张成非退化二维平面。对假设 5.1 的 $L^2$ 向量 $y_0,y_1$，还必有

$$
\left|\frac{s_2-s_0-s_1}{2}\right|\le\sqrt{s_0s_1},
$$

等价地，

$$
|\sqrt{s_0}-\sqrt{s_1}|\le\sqrt{s_2}\le\sqrt{s_0}+\sqrt{s_1}.
$$

证明。展开范数平方得第一式。若 $u\ne0$，写 $v=(V/U)u+v_\perp$，则 $UW-V^2=U\|v_\perp\|^2$；若 $u=0$，行列式也为零。这既证明 Gram 非负与相关判据，也给所定义面积的等式。对 $y_0,y_1$，其 Gram 矩阵恰为定理 5.2 的 $S_y$。Cauchy–Schwarz 给 $|\mathbb E y_0y_1|\le\sqrt{s_0s_1}$，而 $\|y_0+y_1\|_{L^2}^2=s_2$。把绝对值不等式改写为

$$
(\sqrt{s_0}-\sqrt{s_1})^2\le s_2\le(\sqrt{s_0}+\sqrt{s_1})^2
$$

并取非负平方根便得到等价形式。$\square$

**命题 6.3（数量递加不规定正交长度）。** 若把 $2,3,5$ 指定为欧氏三角形的三边，则该三角形退化。若两个正交位移长度为 $2,3$，它们的合位移长度为 $\sqrt{13}$。

证明。$2+3=5$ 是三角不等式的等号，只能给共线的退化三角形。对正交位移 $\langle u,v\rangle=0$，范数展开给 $\|u+v\|^2=4+9=13$。因此 $y_2=y_0+y_1$ 的数量关系本身不能充当正交空间位移的长度相加。$\square$

## 7. 二阶矩推进、面积不变量与 Lorentz 锥

**定理 7.1（FIB 二阶面积保持而非欧氏等距）。** 同一共同来源经 $c\mapsto Mc$ 后，

$$
S'=MSM^T,\qquad \det S'=\det S.
$$

对 $\mathbb R^2$ 中的两个向量，$\det(Mu,Mv)=-\det(u,v)$，故面积绝对值保持、定向翻转，两步恢复定向。不存在正定实矩阵 $Q$ 使 $M^TQM=Q$。

证明。线性映射可移出期望，给合同式；$\det M=-1$，所以行列式乘子为 $(\det M)^2=1$。二维有向面积式是列矩阵行列式的乘法性，只适用于这里指定的二维坐标。$M$ 的特征值为

$$
\phi=\frac{1+\sqrt5}{2}>1,\qquad \psi=-\phi^{-1}.
$$

若存在所述 $Q$，对非零 $\phi$ 特征向量 $e$ 有 $\phi^2e^TQe=e^TQe$。正定性使 $e^TQe>0$，迫使 $\phi^2=1$，矛盾。因此面积不变量不等于正定长度的守恒。$\square$

**定理 7.2（FIB 矩坐标中的实正锥与尺度截面）。** 对任意实对称矩阵 $S$，置

$$
\tau=\frac{U+W}{2},\quad x=V,\quad z=\frac{U-W}{2},\qquad
S=\begin{pmatrix}\tau+z&x\\x&\tau-z\end{pmatrix}.
$$

则 $\det S=\tau^2-x^2-z^2$，其二次型符号为 $(1,2)$。一般实半正定锥的条件为

$$
\tau\ge\sqrt{x^2+z^2}.
$$

该锥的 $\operatorname{tr}S=1$ 截面是 $\tau=1/2$、$x^2+z^2\le1/4$ 的圆盘。

证明。行列式直接展开。特征值为 $\tau\pm\sqrt{x^2+z^2}$，两者非负恰为所列锥条件。迹等于 $2\tau$，代入就给圆盘。三个矩坐标因此是一个带尺度的关系锥，非三个平等的欧氏轴。矩阵与 Lorentz 二次型的经典联系可见 John Baez，[*The Octonions*, §3.3 “$\mathbb OP^1$ and Lorentzian Geometry”](https://math.ucr.edu/home/baez/octonions/node11.html)：该节同时讨论实与复等情形，复 Hermitian 情形对应四维 Lorentz 二次型；本条的实三坐标结论由上述直接展开取得。实际树来源只占此圆盘或锥的受限部分。此外 $M$ 不保持迹一截面，例如 $S=I/2$ 推进后的迹为 $3/2$；重新归一化是另一个操作。$\square$

## 8. 三端口互易边界与精确二次消元

**假设 8.1（无接地的差值代价）。** 设三个实端口值为 $p_0,p_1,p_2$，只允许共同平移不变、互易的二次差值代价。令 $u=p_1-p_0,v=p_2-p_0$，取非负连接系数 $k_{01},k_{02},k_{12}$，定义

$$
E_\partial=\frac12\bigl[k_{01}u^2+k_{02}v^2+k_{12}(u-v)^2\bigr].
$$

它仅涉及两个独立差值，其二次矩阵为

$$
\begin{pmatrix}k_{01}+k_{12}&-k_{12}\\-k_{12}&k_{02}+k_{12}\end{pmatrix}.
$$

三连接系数描述二次边界响应，并不构成三维嵌入或位置空间假设。非负系数保证代价非负；负连接系数不属于此被动网络合同。

**定理 8.2（FIB 接缝模型中的星形内部消元）。** 另设一个内部实变量 $z$，取 $c_i>0$、$C=c_0+c_1+c_2$，定义

$$
E(z)=\frac12\sum_{i=0}^2c_i(z-p_i)^2.
$$

唯一极小点及精确边界响应为

$$
z_* =\frac{\sum_i c_ip_i}{C},\qquad
\min_zE(z)=\frac12\sum_{i<j}\frac{c_ic_j}{C}(p_i-p_j)^2.
$$

证明。设 $P=\sum_i c_ip_i$，则完成平方给

$$
E(z)=\frac C2(z-P/C)^2+
\frac12\left(\sum_i c_ip_i^2-\frac{P^2}{C}\right).
$$

$C>0$ 保证唯一极小点。又

$$
C\sum_i c_ip_i^2-P^2
=\sum_{i<j}c_ic_j(p_i^2+p_j^2-2p_ip_j),
$$

故极小值恰为所列式。这是经典 star–mesh、Y–$\Delta$ 与 Kron reduction 在本卷二次边界模型中的中间消元：参见 [Dörfler–Bullo 的仓内文献条目](../../../Library/GraphInvariants/dorflerbullo2013kron.md) 及其 [*Kron Reduction of Graphs with Applications to Electrical Networks*, §2.1](https://arxiv.org/abs/1102.2950)。内部变量的二次响应被转移到保留端口，原内部来源本身不由极小值反演。$\square$

**假设 8.3（拼接的共同接缝）。** 应用定理 8.2 拼接两个区域时，公共端口必须是同一个实际变量，公共约束与因子必须保持且只计入一次，所有被消去的内部变量须有合法共同实现。满足这些条件，二次极小化可以用边界响应代替内部；此处只断言所声明二次代价的等价，不断言任意动态初态、相位或来源的完整等价。该接缝条件与基础卷定义 5.2 相同。

## 9. 声明复相位后的关系闭合与 Bloch 截面

**假设 9.1（复相位关系合同）。** 增加复 Hermitian 关系矩阵、正性和归一化合同，写

$$
H=\frac12\begin{pmatrix}s+z&x-iy\\x+iy&s-z\end{pmatrix},
\qquad s,x,y,z\in\mathbb R.
$$

相位坐标 $y$ 是新增关系变量，不由原生非负整数树组成免费取得。正性、归一化、混合来源及可执行操作各是独立条件。

**定理 9.2（相位合同中的球体、纯态与最小代数闭合）。** 在假设 9.1 下，

$$
\det H=\frac{s^2-x^2-y^2-z^2}{4},\qquad \operatorname{tr}H=s.
$$

当 $s=1$ 时，$H\ge0$ 当且仅当 $x^2+y^2+z^2\le1$；秩一纯态对应球面 $S^2$，其内在维数为二，混合态填满三维球体。若另对 Hermitian 实线性空间声明

$$
A\diamond B=\frac{AB-BA}{2i},
$$

则包含 $I,M,J$ 且对 $\diamond$ 封闭的最小空间为 $\operatorname{span}_{\mathbb R}\{I,X,Y,Z\}$，其中

$$
J=X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

证明。行列式与迹由展开得到，特征值为 $(s\pm\sqrt{x^2+y^2+z^2})/2$，故得到迹一球体。迹一时秩一恰为半径一；每个内部点 $r=Rn$、$0\le R<1$ 是两纯态方向 $n,-n$ 的混合，权重为 $(1+R)/2,(1-R)/2$。该经典 Bloch 表示作为本卷复关系合同的中间步骤，参见 [IBM Quantum Learning，Bloch sphere](https://quantum.cloud.ibm.com/learning/en/courses/general-formulation-of-quantum-information/density-matrices/bloch-sphere)。非零 spinor 的归一化投影 $ww^\dagger/\|w\|^2$ 只有秩一，不能单独填满球体。

对 Hermitian 矩阵，$\operatorname{tr}(AB)/2$ 为实；在无迹部分，$X,Y,Z$ 以此内积正交归一。乘法给

$$
X\diamond Y=Z,\qquad Y\diamond Z=X,\qquad Z\diamond X=Y.
$$

又 $Z=I+2J-2M$，所以包含 $I,M,J$ 的实线性空间必须包含 $I,X,Z$；封闭性再给 $Y=Z\diamond X$。四个矩阵实线性独立，全部 Hermitian 二阶矩阵又恰由它们张成，故得到最小闭合空间。酉共轭保持迹内积和 $\diamond$，因为共轭保持乘法且迹循环。标准的 $SU(2)/\{\pm I\}\cong SO(3)$ 对应参见 Baez，[*The Octonions*, Introduction](https://math.ucr.edu/home/baez/octonions/node1.html)；spinor 与旋转、Lorentz 对应的背景还见 [*This Week’s Finds*, Week 196](https://math.ucr.edu/home/baez/week196.html)。$U(2)$ 的标量相位在共轭中完全消失，故不同酉矩阵不一定给不同旋转。上述代数闭合没有证明实际菜单能执行任意复线性组合或酉操作。原有 $J$ 的实际观察作用是 [FIB 自校准关系数学，定义 3.1、推论 3.2、第四章](https://github.com/the-omega-institute/trureturing/blob/b19dc63ed2b2007d8d6de4c50366815f0d032ba4/docs/develop/theory/FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md) 中的关系分离与恢复，其结论不包含任意相位控制。$\square$

**命题 9.3（实二次观察的相位盲核）。** 两个不同矩阵

$$
H_\pm=\frac12\begin{pmatrix}1&\mp i\\\pm i&1\end{pmatrix}
$$

均半正定且迹为一，但对每个实列向量 $r$，有 $r^TH_+r=r^TH_-r$。任意实线性变换后再作实二次观察也不能区分它们。

证明。其特征值为 $1,0$。差矩阵是纯虚反对称矩阵，对实 $r$ 的二次型为零。实矩阵合同 $A(H_+-H_-)A^T$ 仍为纯虚反对称矩阵，实二次型仍为零；实线性组合的探针也仍是实探针。这里说相等的是允许观察，而非两矩阵相等。另一种相位不可分合同见 [Fibonacci 相干运输边界，命题 2.3](https://github.com/the-omega-institute/trureturing/blob/b19dc63ed2b2007d8d6de4c50366815f0d032ba4/docs/develop/theory/FIBONACCI_COHERENT_TRANSPORT_BOUNDARY.md)：计算基置换和实际计算基对角 Kraus 分支使相同对角元的态在全部有限自适应协议中不可分。只要求效果对角不够，该量子仪器命题也不能扩大成所有量子操作的相位盲性。$\square$

## 10. 高阶响应维数与二阶选择的未证条件

**定理 10.1（FIB 幂读出的精确阶数容量）。** 对整数 $k\ge1$，齐次 $k$ 次关系的标准单项式为

$$
a^k,a^{k-1}b,\ldots,ab^{k-1},b^k,
$$

线性空间维数为 $k+1$。实际序列 $F_{n+3}^k$ 在固定有限维实线性合同中的最小精确维数也为 $k+1$。

证明。固定 $b=1$ 时，单项式的线性关系变成一个在所有实 $a$ 上为零的次数至多 $k$ 的多项式，故全部系数为零。这是经典 $\operatorname{Sym}^k(\mathbb R^2)$ 的维数步骤。对实际序列，Binet 公式给

$$
F_{n+3}=A\phi^n+B\psi^n,\qquad
A=\frac{\phi^3}{\sqrt5},\quad B=-\frac{\psi^3}{\sqrt5},\quad
\psi=-\phi^{-1}.
$$

$A,B$ 非零，因而

$$
F_{n+3}^k=\sum_{j=0}^k c_j\lambda_j^n,
\quad c_j=\binom kj A^{k-j}B^j\ne0,\quad
\lambda_j=\phi^{k-j}\psi^j=(-1)^j\phi^{k-2j}.
$$

$|\lambda_j|$ 随 $j$ 严格递减，所以这 $k+1$ 个实数两两不同。取 $V_{ij}=\lambda_j^i$，$0\le i,j\le k$，则相应 Hankel 矩阵满足

$$
H_{ij}=F_{i+j+3}^k,\qquad H=V\operatorname{diag}(c_0,\ldots,c_k)V^T.
$$

Vandermonde 行列式 $\prod_{i<j}(\lambda_j-\lambda_i)$ 非零，且全部 $c_j$ 非零，故 $\det H\ne0$。任何 $d$ 维线性实现均将它分解为 $(k+1)\times d$ 与 $d\times(k+1)$ 两矩阵之积，所以 $d\ge k+1$。反向取对角状态矩阵 $\operatorname{diag}(\lambda_j)$、初态全一、输出系数 $c_j$，得到 $k+1$ 维上界；也可用对称幂推进。于是 $k=1,2,3,4$ 分别给 $2,3,4,5$ 维。有关幂读出、Bloch 与二次网络步骤的仓内先例见 [FIB 原子递归全息边界几何](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md)，本条用于本卷阶数选择的边界。$\square$

**假设 10.2（二阶选择的待证条件）。** 若欲从原生 FIB 观察与运输推出“最小关系边界必为有限的、正的、相位完备的二阶边界”，还须定义完整任务族、运输操作、共同接缝与来源条件，并证明二阶摘要在这些任务和递归拼接下闭合，且相位与所需旋转能由原生操作取得。定理 10.1 给每一指定幂的线性容量，未证明任务止于二阶。二阶多项式次数也不是空间微分算子的二阶；几何候选、稳定性候选或数字 $2,3$ 均不能补足这一选择原则。

## FIB-ATOM 续篇二：二阶关系的任务闭包、精确全息消元与相位几何

## 11. 有限共同来源的代数面积分解

**定义 11.1（有限来源与原点矩）。** 取有限共同来源组成 $c_i=(a_i,b_i)^T$、概率 $p_i\ge0$、$\sum_i p_i=1$。原始有序树、组成 $c_i$ 和数量 $\ell c_i$ 属于不同观察层。记

$$
m_0=1,\qquad m=\sum_i p_ic_i,\qquad
S=\sum_i p_ic_ic_i^T.
$$

$S$ 是原点二阶矩，而协方差是 $S-mm^T$。

**定理 11.2（FIB 共同来源的成对面积平方）。** 对定义 11.1，

$$
\det S=\sum_{i<j}p_ip_j(a_ib_j-b_ia_j)^2.
$$

故 $\det S=0$ 当且仅当正权重的非零来源全部共线于过原点的同一直线。若没有非零正权来源，该条件按空集解释；非空树来源不含零组成。共同施加 $M$ 后，各对有向面积翻号，但此行列式不变。

证明。展开

$$
\det S=\sum_{i,j}p_ip_j(a_i^2b_j^2-a_ib_i a_jb_j).
$$

$i=j$ 项为零。将 $i<j$ 的两项配对，得到 $p_ip_j(a_i^2b_j^2+a_j^2b_i^2-2a_ib_i a_jb_j)$，即所列平方。非负权重下和为零恰为每个正权对的行列式为零。选一个非零正权向量，其余非零正权向量都与它线性相关，反向也直接成立。推进时 $\det(Mc_i,Mc_j)=\det M\det(c_i,c_j)=-\det(c_i,c_j)$，平方和不变。它是代数关系面积的保持式，不是能量守恒定律。$\square$

## 12. 仿射嫁接的六维任务闭包

**定义 12.1（有限质量矩与时间有序词）。** 对有限非负、未必归一的权重 $p_i$，置

$$
m_0=\sum_i p_i,\quad m=\sum_i p_ic_i,\quad S=\sum_i p_ic_ic_i^T.
$$

仿射操作为 $c\mapsto Ac+t$。树组成域取

$$
D=\{(a,b)\in\mathbb N^2:a+b>0\},
$$

每个元素均可由非空树实现。指定原生推进 $M$ 与固定组成嫁接 $G(a,b)=(a+1,b)$；在树上可用 $T\mapsto\langle T,\alpha\rangle$ 实现该组成嫁接。有限词 $w=(o_1,\ldots,o_N)$ 按时间先执行 $o_1$，最后执行 $o_N$，即 $T_w=o_N\circ\cdots\circ o_1$。此推进与固定嫁接的定义对应 [GraftAffineClosure 的 `step`、`quantity`、`run`](https://github.com/the-omega-institute/trureturing/blob/9e834a13e0760767641dd65bbdcc92521589baf3/D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.lean)：`run` 从初态依次累积执行，布尔值假为推进、真为加固定组成。本章的目标改为平方数量，不引用该源中的 gcd 结论来代替平方响应的维数证明。

**定理 12.2（仿射操作的矩合同）。** 若权重不随操作改变，则

$$
\begin{aligned}
m_0'&=m_0,\\
m'&=Am+m_0t,\\
S'&=ASA^T+Am\,t^T+t\,m^TA^T+m_0tt^T.
\end{aligned}
$$

故六个线性统计分量 $(m_0,m_a,m_b,S_{11},S_{12},S_{22})$ 对仿射操作闭合。归一概率 $m_0=1$ 后只有五个可变统计参数，这与六维齐次线性载体不同。

证明。对每个来源展开 $(Ac_i+t)(Ac_i+t)^T$ 并按权重求和即可。等价地，令

$$
\bar c=\binom1c,\qquad
\bar S=\begin{pmatrix}m_0&m^T\\m&S\end{pmatrix},\qquad
\bar A=\begin{pmatrix}1&0_{1\times2}\\t&A\end{pmatrix}.
$$

则 $\bar S'=\bar A\bar S\bar A^T$。矩统计是六个单项式 $(1,a,b,a^2,ab,b^2)$ 的加权和。质量等于一时，首坐标固定，余下五坐标在一个仿射超平面中变化；不能把固定常数当成第六个可变统计参数。$\square$

**定理 12.3（全部来源、全部嫁接词的精确六维最小性）。** 取目标 $f(a,b)=(2a+3b)^2$。全部有限词的响应函数在 $D$ 上张成的最小实线性函数空间为

$$
\mathcal V=\operatorname{span}_{\mathbb R}\{1,a,b,a^2,ab,b^2\},\qquad \dim\mathcal V=6.
$$

若要求对所有 $c\in D$ 同时成立的线性状态编码 $E:D\to\mathbb R^d$、固定线性操作矩阵 $B_M,B_G$ 与线性输出 $r^T$，满足 $E(Mc)=B_ME(c)$、$E(Gc)=B_GE(c)$、$f(c)=r^TE(c)$，则最小 $d$ 为 $6$。

证明。令响应空间为 $\mathcal W=\operatorname{span}\{f\circ T_w\}$。它对操作拉回封闭：在时间词前加 $M$ 或 $G$，就分别得到 $(f\circ T_w)\circ M$ 或 $(f\circ T_w)\circ G$。纯 $M$ 的前三个响应正是定理 5.2 的三个二次多项式，其系数行列式为 $-2$，故 $a^2,ab,b^2\in\mathcal W$。作嫁接差分 $\Delta_Gq=q\circ G-q$，有

$$
\Delta_Ga^2=2a+1,\qquad \Delta_G^2a^2=2.
$$

因此 $1,a\in\mathcal W$，再由 $a\circ M=b$ 得 $b\in\mathcal W$。仿射代入不增加多项式次数，故所有响应均属于 $\mathcal V$，从而两空间相等。

为证明独立性，设

$$
\alpha+\beta a+\gamma b+\delta a^2+\eta ab+\theta b^2=0
$$

在 $D$ 上恒成立。固定任意正整数 $b$，让 $a$ 遍历全部正整数，得到一元多项式有无限多个根；于是 $\delta=0$、$\beta+\eta b=0$、$\alpha+\gamma b+\theta b^2=0$。再让 $b$ 遍历全部正整数，得其余五个系数也为零。这用的是域中完整的正整数网格，而非仅凭“来源无限”推独立性。

取 $E(c)=(1,a,b,a^2,ab,b^2)^T$，仿射代入给固定六维线性操作，实现上界。任何所声明的 $d$ 维编码使每个响应成为 $E$ 的坐标函数的线性组合，故 $6=\dim\mathcal W\le d$。该下界是全部来源通用响应的下界，不等同于某个固定初态的词 Hankel 秩；后者须另证。确定组成仍可用二维非线性更新和平方输出编码。$\square$

**定理 12.4（中心化与平移的不变量区别）。** 当 $m_0=1$ 时，

$$
\det\bar S=\det(S-mm^T),\qquad
C:=S-mm^T\longmapsto ACA^T.
$$

因此中心化协方差对平移不变，在 $\det A=\pm1$ 时其行列式也不变；原点矩的行列式对平移一般不保持。

证明。以块下三角矩阵 $L=\left(\begin{smallmatrix}1&0\\-m&I\end{smallmatrix}\right)$ 作合同，有 $L\bar SL^T=\operatorname{diag}(1,S-mm^T)$，且 $\det L=1$，得行列式等式。代入定理 12.2 的 $S'$ 和 $m'=Am+t$，交叉项抵消，得到协方差合同。取 $(1,0),(0,1)$ 各一半，原点矩为 $I/2$，行列式 $1/4$；共同平移 $t=(1,0)$ 后原点矩为 $\left(\begin{smallmatrix}5/2&1/2\\1/2&1/2\end{smallmatrix}\right)$，行列式 $1$。这直接排除把第十一章的原点面积保持推广到平移。$\square$

## 13. 筛选任务与有限二阶摘要的失效

**命题 13.1（相同二阶矩而筛选后的二阶响应不同）。** 取 $b=1$，来源 $P$ 的 $a$ 在 $1,3$ 上分别有概率 $1/4,3/4$；来源 $Q$ 的 $a$ 在 $2,4$ 上分别有概率 $3/4,1/4$。两者全部总次数至多二的联合矩相同，但按 $a^2$ 重权后归一化的新二阶响应不同。

证明。两者都有

$$
m_0=1,\quad m_a=5/2,\quad m_b=1,\quad
S_{aa}=7,\quad S_{ab}=5/2,\quad S_{bb}=1.
$$

而

$$
\mathbb E_Pa^4=\tfrac14+\tfrac34\,81=61,\qquad
\mathbb E_Qa^4=\tfrac34\,16+\tfrac14\,256=76.
$$

重权概率定义为 $p_i'=p_i a_i^2/7$，因而新的 $a$ 二阶矩分别为 $61/7,76/7$。所有 $(a,1)$ 均是可实现的非空树组成。这一筛选是新增任务，不是裸 $M$ 推进或固定嫁接；它要求四阶信息。因此第十二章的动态闭包不能在不改任务合同的情况下扩展为筛选充分性。相关的“动态充分不等于拼接充分”区分见 [FIB 关系延拓几何，定理 5.4](https://github.com/the-omega-institute/trureturing/blob/b19dc63ed2b2007d8d6de4c50366815f0d032ba4/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md)。$\square$

**定理 13.2（无限值域与反复乘法的容量障碍）。** 若实函数线性空间 $\mathcal A$ 含 $1$、含一个无限值域函数 $g$，并对逐点乘法封闭，则 $\dim\mathcal A=\infty$。在包含反复 $a^2$ 赋权的全部树来源任务中，有限次数矩不能构成通用乘法闭包。

证明。乘法封闭使 $1,g,g^2,\ldots$ 全部属于 $\mathcal A$。若有限线性关系 $\sum_{j=0}^N\lambda_jg^j=0$ 非平凡，则非零实多项式 $P(t)=\sum_j\lambda_jt^j$ 在无限集合 $g(D)$ 上全为零，违反非零多项式只有有限多个根。因此这些幂线性独立。对树域，$g(a,b)=a^2$ 有无限值域，反复赋权需要这些幂，正好触发该障碍。这一经典代数步骤用于当前 FIB 任务闭包的下界，并不说明任意单次筛选必然需要无穷维。受限任务或受限来源族仍可有限闭合；例如固定有限来源集合上的全部实函数空间至多为来源数维，并对逐点乘法封闭。$\square$

## 14. 连续 Gaussian 合同的精确全息消元

**假设 14.1（独立声明的连续幅度来源）。** 本章另取连续实变量 $x\in\mathbb R^r$，相对于 Lebesgue 测度定义正关系核

$$
K(x)=\exp\left(-\frac12x^TJx+h^Tx+\kappa\right),\qquad J=J^T.
$$

边界维数 $r$ 固定且有限。总积分非零有限的条件为 $J>0$。这是假设新的连续来源族，不把非负整数树组成自动解释为 Gaussian 随机变量。Gaussian 乘积与边缘的经典来源见 Rasmussen–Williams，[*Gaussian Processes for Machine Learning*, Appendix A.2，式 (A.4)–(A.9)](https://gaussianprocess.org/gpml/chapters/RWA.pdf)。Giscard、Choo、Thwaite、Jaksch，[*Exact Inference on Gaussian Graphical Models of Arbitrary Topology using Path-Sums*, §2](https://arxiv.org/abs/1410.7165) 采用 $J,h$ 的 canonical Gaussian 表示，并研究正定协方差下的精确边缘；下列带常数项的消元由完成平方给出。

**定理 14.2（同一联合核的有限边界消元）。** 对边界变量 $x$ 与内部变量 $y\in\mathbb R^q$，取联合精度和线性项

$$
J=\begin{pmatrix}A&B\\B^T&D\end{pmatrix},\qquad
h=\binom{h_x}{h_y},\qquad D>0.
$$

则对每个固定 $x$，内部积分有限并给

$$
\int_{\mathbb R^q}K(x,y)\,dy
=\exp\left(-\frac12x^TJ_\partial x+h_\partial^Tx+\kappa_\partial\right),
$$

其中

$$
\begin{aligned}
J_\partial&=A-BD^{-1}B^T,\\
h_\partial&=h_x-BD^{-1}h_y,\\
\kappa_\partial&=\kappa+\frac12h_y^TD^{-1}h_y+
\frac q2\log(2\pi)-\frac12\log\det D.
\end{aligned}
$$

仅 $D>0$ 不保证 $J_\partial>0$；若还要求全部变量可归一化，则须联合 $J>0$，等价于 $D>0$ 且 $J_\partial>0$。

证明。令 $\eta=h_y-B^Tx$，指数中含 $y$ 的部分为

$$
-\tfrac12(y-D^{-1}\eta)^TD(y-D^{-1}\eta)
+\tfrac12\eta^TD^{-1}\eta.
$$

正定 $D$ 的谱分解将积分化为 $q$ 个一维 Gaussian 积分，产生因子 $(2\pi)^{q/2}(\det D)^{-1/2}$。展开 $\eta$ 的二次式，就得到三个边界参数。对联合二次型再作无平移的同一完成平方，其正定性恰等价于 $D$ 与 Schur 补都正定；例如 $A=0,B=0,D=I$ 有合法内部积分而边界精度为零，不能在整个 $x$ 空间归一化。对于一般对称 $J$，谱分解表明若有负特征值，沿该坐标指数二次增长；若有零特征值，沿该坐标为常数或线性指数，至少一端积分发散。所以有限总积分恰需 $J>0$。$\square$

**定理 14.3（Gaussian 来源的任务完整性与离族边界）。** 对同一联合 Gaussian 来源，若合成后的联合精度正定，则严格共享变量上的核乘积与合法内部积分保持非退化 Gaussian 形式。有限总积分下，消元顺序不改变最终边界核。中心 Gaussian $N(0,S)$、$S>0$ 的全部高阶矩由 $S$ 决定，特别是

$$
\mathbb E(a^2b^2)=S_{11}S_{22}+2S_{12}^2.
$$

但任意非 Gaussian 筛选和一般 Gaussian 混合不保证保持这一来源族。

证明。对真实共享的同一变量，核相乘使指数中的二次、线性、常数项分别相加；再用定理 14.2 消内部变量。正核的 Tonelli 定理使迭代积分等于共同积分；在有限总积分条件下，所有所需有限边缘与 Fubini 换序都合法。这要求因子来自同一个联合来源、共享变量确实相同且每个因子只计入一次，不能把两个独立取得的边缘强行相乘来制造未声明的联合律。共享隐变量若属于同一联合 Gaussian 系统，合法消去它们仍闭合；共享本身不是破坏 Gaussian 的充分条件。

完成平方给矩母函数

$$
\mathbb E e^{t^Tc}=\exp(\tfrac12t^TSt).
$$

它在原点附近解析，逐次微分确定全部矩。$t_1^2t_2^2$ 的系数为 $S_{11}S_{22}/4+S_{12}^2/2$，乘 $2!2!$ 得所列四阶式。此刻二阶信息足够是来源族的定理，不能推广到第十三章的一般树来源。

作为离族实例，用 $1+x_1^4$ 对非退化 Gaussian 重权并归一，核的对数增加 $\log(1+x_1^4)$，它不是二次多项式。等权混合 $N(u,C)$ 与 $N(-u,C)$、$u\ne0$，核的对数增加 $\log\cosh(u^TC^{-1}x)$，也不是二次多项式。两者均可离开单一 Gaussian 族。$\square$

**定理 14.4（Gaussian 参数与原始矩的非线性对应）。** 对二维未归一 Gaussian 核，参数族有六个实参数：$J$ 的三个、$h$ 的两个、$\kappa$ 的一个。设质量 $m_0>0$ 有限，且原始矩给

$$
\mu=m/m_0,\qquad C=S/m_0-\mu\mu^T>0.
$$

则在 Gaussian 族内部有唯一对应

$$
J=C^{-1},\qquad h=J\mu,\qquad
\kappa=\log m_0-\frac r2\log(2\pi)+\frac12\log\det J
-\frac12\mu^TJ\mu.
$$

证明。将核写成

$$
K(x)=m_0(2\pi)^{-r/2}(\det C)^{-1/2}
\exp\bigl[-\tfrac12(x-\mu)^TC^{-1}(x-\mu)\bigr]
$$

并展开指数便得到对应；反向由 Gaussian 积分得到同一质量、均值和协方差。此对应含求逆、乘除及对数，故六参数 Gaussian 族不是第十二章六维多项式线性函数空间的同义对象，Gaussian 核的线性张成也不由这六个参数数目决定。若固定中心且任务不观察核总质量，保留 $J$ 的三个参数即可；其中仍包括协方差的整体规模。忽略总质量 $m_0$ 不等于忽略协方差尺度。$\square$

**定理 14.5（固定有限边界上的非退化极限）。** 若 $J_j\to J>0$、$h_j\to h$、$\kappa_j\to\kappa$，且存在 $\lambda>0$ 使 $J_j\ge\lambda I$，则对应核 $K_j$ 在紧集上一致收敛于 $K$，并在 $L^1(\mathbb R^r)$ 中收敛。

证明。指数是系数收敛的有限维二次多项式，故紧集上一致收敛，指数函数保持该结论。参数收敛给 $\|h_j\|\le H$、$\kappa_j\le K_0$ 的统一有限界。由

$$
-\frac\lambda2\|x\|^2+H\|x\|+K_0
\le-\frac\lambda4\|x\|^2+\frac{H^2}{\lambda}+K_0,
$$

全部核及极限都有同一个可积 Gaussian 上界，支配收敛定理给 $\int|K_j-K|\to0$。若 $\det J_j\to0$ 或质量发散，不能套用此论证，例如 $e^{-x^2/(2j)}$ 的质量趋于无穷。无限维界面没有这里的固定 Lebesgue 测度与统一有限维控制，须另给条件。$\square$

## 15. Gaussian 区分合同给出的正矩阵尺子

**假设 15.1（零均值统计区分）。** 取二维非退化 Gaussian 来源 $N(0,S)$，$S\in\operatorname{SPD}_2(\mathbb R)$。用相对熵 $D_{\mathrm{KL}}$ 衡量两分布的局部区分，并令对称矩阵 $U,V$ 为协方差切向量。此选择给统计尺子，不由裸 FIB 组成唯一规定。一般正矩阵迹度量的来源是 Hiai–Petz，[*Riemannian metrics on positive definite matrices related to means*, 式 (0.2)–(0.5)](https://arxiv.org/abs/0809.4974)；该文式 (0.2) 为无 $1/2$ 的迹形式，本章采用 Gaussian 相对熵给出的半迹规范化。

**定理 15.2（FIB 连续来源的 Fisher 常数与合同不变性）。** 在假设 15.1 下，

$$
D_{\mathrm{KL}}(N(0,S)\Vert N(0,T))
=\frac12\left[\operatorname{tr}(T^{-1}S)-2+
\log\frac{\det T}{\det S}\right].
$$

当 $T=S+\varepsilon U>0$ 且 $\varepsilon\to0$ 时，

$$
D_{\mathrm{KL}}=
\frac{\varepsilon^2}{4}\operatorname{tr}(S^{-1}US^{-1}U)
+O(\varepsilon^3).
$$

因此 Fisher 度量为

$$
g_S(U,V)=\frac12\operatorname{tr}(S^{-1}US^{-1}V),
$$

并对任意可逆实 $A$ 满足

$$
g_{ASA^T}(AUA^T,AVA^T)=g_S(U,V).
$$

证明。两 Gaussian 对数密度的差为

$$
\tfrac12\log(\det T/\det S)+
\tfrac12x^T(T^{-1}-S^{-1})x.
$$

在 $N(0,S)$ 下取期望并用 $\mathbb E x^TBx=\operatorname{tr}(BS)$，得到第一式。令 $L=S^{-1}U$；它相似于实对称矩阵 $S^{-1/2}US^{-1/2}$，所以小 $\varepsilon$ 下逆矩阵与对数行列式展开合法。分别展开为

$$
\begin{aligned}
\operatorname{tr}(I+\varepsilon L)^{-1}
 &=2-\varepsilon\operatorname{tr}L+
\varepsilon^2\operatorname{tr}L^2+O(\varepsilon^3),\\
\log\det(I+\varepsilon L)
 &=\varepsilon\operatorname{tr}L-
\frac{\varepsilon^2}{2}\operatorname{tr}L^2+O(\varepsilon^3).
\end{aligned}
$$

线性项抵消，得到半个 $\varepsilon^2g_S(U,U)$。也可从统计 score 直接识别 Fisher：协方差方向 $U$ 的 score 是

$$
\frac12\left[x^TS^{-1}US^{-1}x-\operatorname{tr}(S^{-1}U)\right].
$$

由第十四章 Gaussian 矩母函数的四阶微分，两个二次型的协方差为 $2\operatorname{tr}(BSC S)$，其中 $B,C$ 为对称系数矩阵；代入 $B=S^{-1}US^{-1},C=S^{-1}VS^{-1}$，得所列 $g$。该二次型对非零 $U$ 为正，因为 $\operatorname{tr}[(S^{-1/2}US^{-1/2})^2]$ 是实对称矩阵全部特征值平方之和。最后代入 $(ASA^T)^{-1}=A^{-T}S^{-1}A^{-1}$ 并用迹循环，得合同不变性。$A$ 保持这把关系尺子不等于它保持组成向量的欧氏长度。$\square$

## 16. 实正二阶关系的规模与双曲形状

**定理 16.1（选定 Fisher 尺子下的规模—形状分解）。** 每个实二维正定矩阵唯一写为

$$
S=e^s\widehat S,\qquad s=\frac12\log\det S,\qquad \det\widehat S=1.
$$

在定理 15.2 的度量下，

$$
g=ds^2+g_{\mathrm{shape}},\qquad
\widehat S=\begin{pmatrix}t+z&x\\x&t-z\end{pmatrix},\quad
 t^2-x^2-z^2=1,\ t>0,
$$

且形状度量为切平面上的

$$
g_{\mathrm{shape}}=dx^2+dz^2-dt^2.
$$

因此整个所声明的正矩阵 Riemannian 空间等距于 $\mathbb R\times\mathbb H^2$，其中双曲曲率规范化为 $-1$。三个实二阶参数分成一个规模参数与两个形状方向。

证明。标量分解由行列式直接给出且唯一。微分得

$$
S^{-1}dS=ds\,I+\widehat S^{-1}d\widehat S,\qquad
\operatorname{tr}(\widehat S^{-1}d\widehat S)=d\log\det\widehat S=0.
$$

代入半迹形式，交叉项为零，$\frac12\operatorname{tr}(ds^2I)=ds^2$。令 $L=\widehat S^{-1}d\widehat S$，其迹为零。二阶矩阵恒等式 $\tfrac12\operatorname{tr}L^2=-\det L$ 给

$$
g_{\mathrm{shape}}=-\det(d\widehat S)=dx^2+dz^2-dt^2.
$$

约束的切向量满足 $t\,dt=x\,dx+z\,dz$；因 $t^2=1+x^2+z^2$，该形式对每个非零切向量正定。取极坐标

$$
t=\cosh R,\quad x=\sinh R\cos\theta,\quad z=\sinh R\sin\theta,
$$

度量化为 $dR^2+\sinh^2R\,d\theta^2$，这是标准双曲平面；经典旋转度量的曲率式 $-f''/f$ 在 $f(R)=\sinh R$ 时为 $-1$。规模坐标遍历 $\mathbb R$，与形状约束完全独立，所以是度量乘积，不只是拓扑分解。矩阵行列式的 Lorentz 背景见第七章所引 Baez §3.3；半迹常数及乘积分解由本证明确定，不由该网页代替。此结论使用全部实正定矩阵及可逆连续合同模型，实际树来源的可达子集不因此变成整个 $\mathbb R\times\mathbb H^2$。$\square$

## 17. FIB 归一化极限与不收缩的形状距离

**定理 17.1（共同推进的形状距离公式）。** 对行列式一的实正定矩阵 $P,Q$，在第十六章的度量下，真正的路径距离为

$$
d(P,Q)=\operatorname{arcosh}\left(\frac12\operatorname{tr}(P^{-1}Q)\right).
$$

其反双曲余弦参数至少为一。若 $S_n=M^nS_0(M^T)^n$、$T_n=M^nT_0(M^T)^n$，则各自的行列式一形状满足

$$
d(\widehat S_n,\widehat T_n)=d(\widehat S_0,\widehat T_0).
$$

证明。共同合同 $A=P^{-1/2}$ 的行列式为一，把 $P$ 送到 $I$，把 $Q$ 送到 $Q'=P^{-1/2}QP^{-1/2}$；第十五章已证明它是等距映射。$Q'$ 为行列式一正定矩阵，特征值为 $\lambda,\lambda^{-1}$，所以 $\operatorname{tr}Q'/2\ge1$。在第十六章坐标中 $Q'$ 的时间坐标为 $t=\operatorname{tr}Q'/2=\cosh R$。从原点 $I$ 到此点的径向曲线长度为 $R$。任一分段光滑曲线的长度元由 $dR^2+\sinh^2R\,d\theta^2$ 给出，至少为 $|dR|$，所以任一路径长度至少为 $R$，径向曲线达到下界。于是距离恰为 $\operatorname{arcosh}(\operatorname{tr}Q'/2)$；迹循环给 $\operatorname{tr}Q'=\operatorname{tr}(P^{-1}Q)$。这证明的是路径长度的极小性，并非仅证明某个迹表达式不变。

因 $|\det M^n|=1$，推进保持每个来源矩的行列式，形状在同一个 $M^n$ 合同下推进。合同不变性保持上述路径长度，也可直接用迹循环保持距离公式，得第二结论。$\square$

**定理 17.2（趋向同一秩一坐标边界不消除内在距离）。** 在 $M$ 的正交特征基中，$M=\operatorname{diag}(\phi,-\phi^{-1})$。若初态

$$
S_0=\begin{pmatrix}a&b\\b&d\end{pmatrix}>0,
$$

则

$$
S_n=\begin{pmatrix}a\phi^{2n}&(-1)^nb\\(-1)^nb&d\phi^{-2n}\end{pmatrix},
\qquad \frac{S_n}{\operatorname{tr}S_n}\longrightarrow
\begin{pmatrix}1&0\\0&0\end{pmatrix}.
$$

若 $S_0=I$，则 $d(I,M^{2n})=2n\log\phi$，$n\ge0$。不同初态的迹归一坐标可以相互趋近而保持严格正的固定形状距离。

证明。对角矩阵合同直接给三项；正定性给 $a,d>0$、$ad-b^2>0$。除以迹后，第一项趋一、交叉项趋零、第二项趋零。$M$ 实对称且 $\det M^2=1$，故 $S_n=M^{2n}$ 是行列式一矩阵，其特征值为 $\phi^{2n},\phi^{-2n}$；定理 17.1 的参数为 $\cosh(2n\log\phi)$，得距离式。

取同一特征基中的 $S_0=I$、$T_0=\operatorname{diag}(e^\delta,e^{-\delta})$，$\delta\ne0$。两条迹归一轨迹都趋向上述秩一矩阵，但形状距离恒为 $|\delta|>0$。一般地，迹一正定矩阵趋向非零秩一边界时，$\det R\to0$，其行列式一代表 $\widehat R=R/\sqrt{\det R}$ 满足 $\operatorname{tr}\widehat R/2=1/(2\sqrt{\det R})\to\infty$，距 $I$ 趋无穷。所以秩一射线是无限距离的理想边界。每个有限 $n$ 的合同仍可逆，并未自动丢弃全部形状信息；有限读口精度或噪声须另建合同。改变坐标或量具也不自动恢复被观察遗忘的绝对来源。$\square$

## 18. 复正关系的三维双曲形状与各向同性

**假设 18.1（正 Hermitian 形状与选定尺子）。** 增加完整复关系合同，取

$$
H=\begin{pmatrix}t+z&x-iy\\x+iy&t-z\end{pmatrix}>0,
\qquad
\det H=t^2-x^2-y^2-z^2.
$$

对 Hermitian 切向量选择

$$
g_H(U,V)=\frac12\operatorname{Re}\operatorname{tr}(H^{-1}UH^{-1}V).
$$

这是指定的 affine-invariant 度量。此选择不免费成为量子 Fisher 度量，也不由裸 FIB 的统计合同唯一导出。矩阵与 Lorentz 形式的经典对应参见 Baez [§3.3](https://math.ucr.edu/home/baez/octonions/node11.html)，其 $SL(2,\mathbb C)$ 合同作用保持该行列式，除去中心 $\{\pm I\}$ 对应保时向、保定向的 Lorentz 群。

**定理 18.2（复关系形状的双曲三维性）。** 在假设 18.1 下，行列式一的截面

$$
t^2-x^2-y^2-z^2=1,\qquad t>0
$$

以所选度量等距于标准 $\mathbb H^3$，其切向度量为

$$
dx^2+dy^2+dz^2-dt^2.
$$

该形状空间齐次，且每点的稳定群在单位切方向上可迁移任意方向。因此三方向等价是这一新增关系形状模型内的定理。

证明。$H^{-1/2}UH^{-1/2}$ 是 Hermitian 矩阵，故所定义二次度量为其特征值平方和的一半，严格正于非零 $U$。对任意可逆复 $A$，合同 $H\mapsto AHA^\dagger$ 保持该度量，证明仍是逆矩阵公式与迹循环。行列式一切向量满足 $\operatorname{tr}(H^{-1}dH)=0$。二阶矩阵迹恒等式给

$$
\tfrac12\operatorname{Re}\operatorname{tr}[(H^{-1}dH)^2]
=-\det(dH)=dx^2+dy^2+dz^2-dt^2.
$$

令 $\mathbf q=(x,y,z)$，切平面约束为 $t\,dt=\mathbf q\cdot d\mathbf q$，且 $t^2=1+\|\mathbf q\|^2$，所以这一限制为正定。写 $t=\cosh R,\mathbf q=\sinh R\,n$、$n\in S^2$，度量为 $dR^2+\sinh^2R\,g_{S^2}$，即标准曲率 $-1$ 的双曲三空间。

任意行列式一 $H$ 都可用 $A=H^{-1/2}$ 送到 $I$，且 $\det A=1$，故空间齐次。在 $I$ 处切向量为无迹 Hermitian 矩阵 $U=u\cdot\sigma$，其中 $\sigma=(X,Y,Z)$，并有 $g_I(U,U)=\|u\|^2$。同模长的两个非零 $U,V$ 具有相同谱 $\pm\|u\|$，谱定理给将其对应本征基匹配的酉矩阵。乘一个整体相位可使其行列式为一，不改变共轭；因此 $SU(2)$ 在单位切方向上传递作用。再以合同搬回 $H$，得到各点各向同性。$SU(2)$ 对三方向旋转的中心双覆盖见第九章所引 Baez Introduction。上述方向是正关系形状的切向量，不是物理位置空间的轴。$\square$

**定理 18.3（正射线的 Bloch 截面及其 Klein 度量）。** 对上述行列式一 $H$，置

$$
\rho=H/\operatorname{tr}H=\frac12(I+r\cdot\sigma),\qquad
r=\frac{(x,y,z)}t,\qquad \|r\|<1.
$$

迹一正定截面与行列式一截面参数化同一族正射线。将行列式一形状度量经此对应搬到开球，得到

$$
g_{\mathrm{Klein}}=
\frac{\|dr\|^2}{1-\|r\|^2}+
\frac{(r\cdot dr)^2}{(1-\|r\|^2)^2}.
$$

证明。任一正射线有唯一迹一代表，也有唯一行列式一代表。由约束，$t=(1-\|r\|^2)^{-1/2}$、$(x,y,z)=tr$。因此

$$
dt=t^3(r\cdot dr),\qquad d\mathbf q=t\,dr+r\,dt.
$$

代入 $\|d\mathbf q\|^2-dt^2$ 并合并交叉项，恰得所列形式。这是标准 Klein 球坐标的双曲度量，不是通常欧氏球度量，也不是 Poincaré 球坐标的表达式；这里搬运的是正射线的行列式一形状度量，不能与在整个正锥上直接限制到迹一超平面的度量混同。van Oostrum，[*Bures–Wasserstein geometry for positive-definite Hermitian matrices and their trace-one subset*](https://arxiv.org/abs/2001.08056) 研究另一个度量，不能据其迹一坐标推出本条的 Klein 形式。

三参数的实正二阶矩包括一维规模，而此复行列式一模型的三参数全是形状方向。第九章的纯迹一态位于球面，秩一且不正定，不属于这里的双曲内部；混合正定态才能遍历开球。$\square$

## 19. 实原语的相位取得障碍

**命题 19.1（不交换的实操作仍有相位盲核）。** 取 $0<\epsilon<1$，令

$$
H_\pm=\begin{pmatrix}1&\mp i\epsilon\\\pm i\epsilon&1\end{pmatrix}.
$$

两者不同且正定。由实 $M,J$ 组成的任意有限词、实线性组合及实二次读口，均不能区分它们。允许操作相互不交换，并不足以取得复相位。

证明。$H_\pm$ 的特征值为 $1\pm\epsilon>0$。对每个实列向量 $r$，纯虚反对称交叉项抵消，所以

$$
r^TH_+r=r^TH_-r=r_1^2+r_2^2.
$$

任意实 $A$ 之后，读数 $r^TAH_\pm A^Tr$ 仍是同一个实探针 $A^Tr$ 的二次读数。实矩阵的乘积和实线性组合仍实；尽管 $MJ\ne JM$，差矩阵的纯虚反对称部分仍在这个观察族的盲核内。若有限自适应协议仅根据这些同样的记录选择后续实合同及读口，按历史长度归纳，两来源也始终给同样的记录。使用复向量探针或相位敏感仪器会改合同，不能算作原合同免费已有的能力。$\square$

**假设 19.2（相位操作与实际运输的待证桥）。** 本卷未证明原生树替换、组成嫁接与真实读口能取得或控制任意复相位；代数中加入 $i$ 或 $\diamond$ 不构成可执行操作的证明。本卷也未证明正矩阵关系距离等于实际空间运输距离。若引用相干运输命题 2.3，其适用族仍仅为计算基置换、实际计算基对角 Kraus 分支及同类读出；单独效果对角的仪器与一般量子仪器不在其结论内。要跨过上述两桥，须另给实际操作、观测和运输定义，并证明它们与本卷矩阵合同、度量对应。

## 20. 任务闭包、有限边界与几何解释的条件整合

**定义 20.1（相对于任务的完整关系边界）。** 给定来源域 $X$、指定可执行操作及其合法性条件、目标读数与拼接任务，摘要 $\eta:X\to B$ 为完整边界，是指目标读数、每个操作的合法性与后继摘要都由 $\eta$ 决定；若还有拼接，实际共享接缝与共同来源约束也须经摘要保留，使边界替代保持全部指定任务。这里“完整”总以指定任务为量词范围，不表示恢复全部原始树或所有可能任务。

**定理 20.2（FIB 合同改变时的条件关系完成）。** 对本卷各个已声明的任务与来源，成立如下整体关系：原生组成是二维观察；全部齐次二阶线性响应的最小载体是三维；加入固定组成嫁接并要求全部来源、全部有限词响应后，最小载体为包括质量的六维线性矩空间；加入无限值域和反复乘法闭包后，通用线性函数空间为无限维；若改为固定有限边界的非退化 Gaussian 来源并只用合法 Gaussian 合成与消元，则有限参数核可以保存完整的指定边界响应。在零均值 Gaussian 区分尺子下，实正二阶矩的几何为规模乘双曲二维形状；另加复正关系与半迹尺子后，行列式一形状为各向同性的双曲三空间。上述结论分别带着各自合同，互不提供未声明假设。

证明。定理 1.2 给组成的两量恢复，定理 2.2 与 3.2 分别给通用二次响应和实际平方序列的三维上下界。定理 12.3 给嫁接任务的六维上下界；质量坐标固定为一时，定理 12.2 给五个可变矩参数。命题 13.1 证明二阶矩不足以预测新增筛选，定理 13.2 在无限值域与反复乘法条件下排除有限线性闭包。定理 14.2–14.5 保证同一正 Gaussian 联合核的有限、合法消元、来源内高阶确定性与非退化极限；这里完整的是指定保留变量的核，不是所有来源信息。定理 15.2 从相对熵取得半迹尺子，定理 16.1 和 17.1 给实形状的度量、距离；定理 18.2–18.3 在新增复合同中给三维形状与各向同性。命题 19.1 表明这一复合同不由实原语的非交换性推出。

这些摘要的动态充分性也可直接按纤维检验：若相同摘要的来源给相同目标、相同合法性及相同后继摘要，则在每个实际摘要值上选择任一代表即可定义读出与更新；纤维条件保证定义不依赖代表。按词长归纳，所有合法有限任务遂可由边界执行。反之，完整边界立即要求这些纤维性质。拼接还需同一实际接缝的一一对应，不能由动态更新充分性单独推出。因此各合同下的维数与几何结论，只在其任务纤维保持条件内构成关系完成。$\square$

**假设 20.3（原生任务闭合的待证断言）。** 设欲定义一个由原生 FIB 观察、递归、嫁接与严格拼接生成的任务族 $\mathcal T$。待证断言是：存在在全部 $\mathcal T$ 下闭合的有限、正、二阶完整边界，且不需无限高阶关系。必须先确定 $\mathcal T$ 是否包含第十三章式筛选或反复赋权、来源族是否满足第十四章式闭合限制；未给这些条件时，有限二阶选择没有由前文推出。

**假设 20.4（相位取得和控制的待证断言）。** 在假设 20.3 的实际任务系统中，待证断言是：原生允许操作可取得相位敏感关系，并实现解释各向同性所需的旋转控制。须给实际读口、干扰、制备和可执行操作与复 Hermitian 模型的映射，证明取得和控制，而不只证明代数闭包。第九章与第十八章给关系模型内部结构，第十九章留下原生取得障碍。

**假设 20.5（关系距离忠实于实际运输的待证断言）。** 待证断言是：存在明确位置与运输模型，使关系形状的路径距离忠实表示实际运输距离，并保持所需接缝与递归。须说明对象、共同来源、允许路径、代价、观察精度及距离对应。欧氏点源的稳定窗口若使用欧氏体积和欧氏 Laplace 算子，其传播核与稳定性结论属于欧氏合同；赋予双曲关系几何以位置含义后，须重新推导相应体积、传播核和稳定条件。三维二阶线性载体与三维复形状的两个“三”不能合成空间三维性的证明；二阶多项式次数也不推出空间二阶微分律。上述任务、相位、运输三座桥均为待证断言，前文没有证明它们。

## 追加锚（本行以下为增补区）
## 21. 完整树来源与三周期观察的分层

**定义 21.1（有序树、替换与第三个轨道来源）。** 在定义 1.1 的自由有序二叉树上继续保留叶标签、左右次序和全部括号。记

$$
T_n=\rho^n\alpha,\qquad
\gamma:=\rho\beta=\rho^2\alpha
=\langle\beta,\alpha\rangle
=\langle\rho\alpha,\alpha\rangle.
$$

这里 $\gamma$ 是一棵复合树的名称，不是新增的自由叶。所用完整规则是

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle u,v\rangle=\langle\rho u,\rho v\rangle.
$$

本章至第二十九章的树来源、五模式和即时读者均引用 [FIB 关系延拓几何，钉版定义 1.1、1.3，第 2、7 章](https://github.com/the-omega-institute/trureturing/blob/9b663cb5b80c3665ada4ace252420164c33be38c/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md)。后文的商、函数与几何各自另给合同，不改动这一完整来源。

**命题 21.2（来源递归持续增长）。** 完整来源满足

$$
T_0=\alpha,\qquad T_1=\beta,\qquad
T_{n+2}=\langle T_{n+1},T_n\rangle.
$$

特别地，$\rho\gamma=\langle\gamma,\beta\rangle\ne\alpha$。轨道没有三周期，也不枚举全部自由树。

证明。零层递归是第二替换规则；对等式施加保持括号的 $\rho$，归纳得全部递归。这一步复用所引来源定理 1.2，而把其增长与后文周期商相比较。设 $L(T)$ 为树的叶数，则 $L(T_0)=L(T_1)=1$ 且

$$
L(T_{n+2})=L(T_{n+1})+L(T_n).
$$

所有叶数为正，所以从 $T_1$ 起叶数严格增长；$T_0,T_1$ 的叶标签又不同，轨道各树两两不同。$\rho\gamma$ 有三片叶，与一片叶的 $\alpha$ 不同。树 $\langle\alpha,\beta\rangle$ 有两片叶，但轨道中唯一两叶树是 $\gamma=\langle\beta,\alpha\rangle$，左右顺序不同。因此自由树的生成描述不等于单起点轨道的枚举。$\square$

**命题 21.3（第二替换规则不可省）。** 仅指定 $\rho\alpha=\beta$ 以及替换保持配对，不能唯一确定 $\rho^2\alpha$。

证明。任意指定一棵树作为 $\rho\beta$，都可按树结构递归扩展成保持配对的替换。例如令 $\widetilde\rho\alpha=\beta$、$\widetilde\rho\beta=\alpha$，并逐节点扩展。它满足同一个第一替换规则，却给 $\widetilde\rho^2\alpha=\alpha$；定义 21.1 则给 $\rho^2\alpha=\gamma$。两棵树不同，故第一规则不足。三周期的来源若要出现，必须说明额外观察或商，而不能由 $\beta=\rho\alpha$ 这一个等式推出。$\square$

## 22. 三步恒等观察的通用模二商

**定义 22.1（加法观察的代数扩张）。** 将组成加法的载体扩到 $\mathbb Z^2$，仅用于群与商的分析。负组成不因此成为可实现树。设 $A$ 为加法群，$\pi:\mathbb Z^2\to A$ 为群同态；即使 $A$ 不交换，$\pi$ 的像仍交换。称 $\pi$ 为三步恒等观察，是指对所有 $v\in\mathbb Z^2$ 有 $\pi(M^3v)=\pi(v)$。

**定理 22.2（三步恒等的精确因子化）。** 在定义 22.1 下，以下条件等价：$\pi M^3=\pi$；$\pi$ 消去 $2\mathbb Z^2$；存在唯一同态 $\bar\pi:\mathbb F_2^2\to A$ 使

$$
\pi=\bar\pi\,r,\qquad
r:\mathbb Z^2\longrightarrow\mathbb Z^2/2\mathbb Z^2=\mathbb F_2^2.
$$

因而模二商是全部此类加法观察的通用商，但一个特定观察的像可以少于四个元素。

证明。直接乘法给

$$
M^3=\begin{pmatrix}1&2\\2&3\end{pmatrix},\qquad
M^3-I=\begin{pmatrix}0&2\\2&2\end{pmatrix}=2M,
\qquad
\det M=-1,\qquad
M^{-1}=\begin{pmatrix}-1&1\\1&0\end{pmatrix}.
$$

$M$ 在 $\mathbb Z^2$ 上可逆，所以 $(M^3-I)\mathbb Z^2=2M\mathbb Z^2=2\mathbb Z^2$。同态性使 $\pi(M^3v)=\pi(v)$ 当且仅当 $\pi((M^3-I)v)=0$，从而得到前两个条件等价。若 $\pi$ 消去偶向量，定义 $\bar\pi([v])=\pi(v)$；代表之差为偶向量保证良定义。反向因子化必消去偶向量，且 $r$ 满射保证 $\bar\pi$ 唯一。

像由两个阶至多二的元素 $u=\pi(1,0)$、$v=\pi(0,1)$ 生成，故至多四类。只有在 $u,v$ 非零且 $u\ne v$，亦即它们在这个二元向量群内独立时，$0,u,v,u+v$ 才两两不同。允许进一步合并的观察不受四类下界约束。$\square$

**命题 22.3（三步观察不自动下降为一步动力）。** 通用商上由 $rM=\bar M r$ 定义的线性作用满足 $\bar M^3=I$，在三个非零元素上恰为三周期。对于进一步观察 $\bar\pi$，一步作用在其像上良定义，当且仅当 $\ker\bar\pi$ 对 $\bar M$ 不变。满足三步恒等但丢失一个独立生成元的非平凡进一步商，不满足此一步下降条件。

证明。令 $\bar\alpha=(1,0)$、$\bar\beta=(0,1)$、$\bar\gamma=(1,1)$，则

$$
\bar M\bar\alpha=\bar\beta,\qquad
\bar M\bar\beta=\bar\gamma,\qquad
\bar M\bar\gamma=\bar\alpha.
$$

若两个商代表之差属于核，后继相同商类的条件正是 $\bar M(\ker\bar\pi)\subseteq\ker\bar\pi$。由于 $\bar M^3=I$，这个包含也给等号。$\mathbb F_2^2$ 的一维子空间各由一个非零向量生成，三个这样的子空间被 $\bar M$ 循环置换，所以不变子空间只有 $0$ 和全空间。核为 $0$ 时保留四类；核为全空间时只剩零类；三种核为一维的二类商没有一步下降。

例如 $\pi(a,b)=a\bmod2$ 满足 $\pi M^3=\pi$，但 $\pi(0,0)=\pi(0,1)=0$，而 $\pi M(0,0)=0$、$\pi M(0,1)=1$。它的三步相同读数不供应一步后继的函数。通用周期商与一个任意进一步观察必须分别判断。$\square$

## 23. 三个非零角色、对称关系与有向时间

**定义 23.1（模二角色及零角色）。** 在通用商 $V_2=\mathbb F_2^2$ 上，以 $\oplus$ 表示加法，并沿用 $0,\bar\alpha,\bar\beta,\bar\gamma$ 的名称。角色是组成的模二观察，不是树身份。零角色也不等于空来源：例如非空树 $\langle\alpha,\alpha\rangle$ 的组成为 $(2,0)$，角色为零。

**定理 23.2（三角色关系与时间方向的分离）。** 三个非零角色满足

$$
\bar\alpha\oplus\bar\beta=\bar\gamma,\quad
\bar\beta\oplus\bar\gamma=\bar\alpha,\quad
\bar\gamma\oplus\bar\alpha=\bar\beta,\quad
x\oplus x=0.
$$

任意两个不同非零角色唯一补出第三个；关系 $\bar\alpha\oplus\bar\beta\oplus\bar\gamma=0$ 对全部 $S_3$ 角色置换不变。此完整角色置换群由 $GL(2,\mathbb F_2)\cong S_3$ 实现；其中保持指定一步循环 $\bar M$ 的置换只有 $C_3=\{I,\bar M,\bar M^2\}$，每个换位都把 $\bar M$ 共轭成 $\bar M^{-1}$。

证明。所列加法逐坐标模二计算即得。不同非零向量的和不为零，也不等于任何一个加数，所以只能是第三个非零向量。每个可逆线性变换置换三个非零元素，且若固定它们便固定一组基，故这个作用忠实。第一个基向量有三个非零像，第二个有两个不在同一条线上的像，故可逆变换有 $3\cdot2=6$ 个。它们的忠实作用因而恰为全部 $S_3$；这是小有限域一般线性群的经典对应，此处计数已给出所需实例。

将 $\bar M$ 看作循环 $(\bar\alpha\ \bar\beta\ \bar\gamma)$。与它交换的置换由 $\bar\alpha$ 的像唯一决定，因为其余两像必须沿同一循环传递；三种选择恰给 $I,\bar M,\bar M^2$。换位把该三循环的次序反转，故其共轭为逆循环。于是补第三角色的关系具有全置换对称，而指定时间前进只保留循环对称；前者不能抹去后者的正反方向。$\square$

## 24. 五模式的实际组成与稳定类型

**定义 24.1（单窗组成与类型）。** 三位按低到高打印，位置分别代表 $\alpha,\beta,\gamma$ 的组成贡献。对 $w=b_0b_1b_2$ 定义

$$
d(w)=b_0\binom10+b_1\binom01+b_2\binom11
=\binom{b_0+b_2}{b_1+b_2},\qquad
\theta(w)=\binom{b_0\oplus b_2}{b_1\oplus b_2}\in V_2.
$$

这里 $b_i\in\{0,1\}$，$d$ 的加法是整数加法，$\theta$ 的加法是模二加法。五模式仍是所引来源定义 2.1 的字母表。

**命题 24.2（五模式数值表与分层不变量）。** 单窗对应关系为

| 模式 | 低到高三位 | $d(w)$ | $\theta(w)$ | 零层数量 $\ell d(w)$ |
| --- | --- | --- | --- | --- |
| $\mathrm{null}$ | $000$ | $(0,0)$ | $0$ | $0$ |
| $[2]$ | $100$ | $(1,0)$ | $\bar\alpha$ | $2$ |
| $[3]$ | $010$ | $(0,1)$ | $\bar\beta$ | $3$ |
| $[25]$ | $101$ | $(2,1)$ | $\bar\beta$ | $7$ |
| $[5]$ | $001$ | $(1,1)$ | $\bar\gamma$ | $5$ |

第 $j$ 个窗口的实际贡献是 $M^{3j}d(w)$，类型仍为 $\theta(w)$。$[25]$ 与 $[3]$ 同类型但不同数量；它们相差两个 $\alpha$ 的零层组成，零层数量差为四。

证明。将三位代入定义 24.1，得表中全部组成和类型；数量以 $\ell=(2,3)$ 计算，故 $[25]$ 的名字不表示十进制二十五。三个贡献向量依次为 $c(\alpha)$、$Mc(\alpha)$、$M^2c(\alpha)$。来源第 $j$ 窗口整体移动三步 $j$ 次，因此实际贡献为 $M^{3j}d(w)$。定理 22.2 给 $M^3\equiv I\pmod2$，遂有

$$
r(M^{3j}d(w))=r(d(w))=\theta(w).
$$

这表示固定模式在窗口层数变化时类型不变，不表示其数量不变。实际数量为

$$
\ell M^{3j}d(w)=\sum_{k=0}^2 b_kF_{3j+k+3}.
$$

对任意非零非负组成，$\ell M=(3,5)$ 比 $\ell$ 在两个坐标上都大，故随推进数量严格增长。两个模式在第 $j$ 窗口的数量差为 $2F_{3j+3}$，只有在 $j=0$ 时是四。一般有限窗词的累计类型是各实际窗口类型的异或和，不能把单窗不变量误当累计类型恒定。$\square$

## 25. 类型纤维、必要接缝与角色置换的提升障碍

**定义 25.1（高到低窗口的旧、新接缝）。** 在钉版即时读者中，旧接缝 $s_{\mathrm{old}}$ 是此前较高窗口的最低位。新输入较低窗口的最高位 $b_2$ 必须满足 $s_{\mathrm{old}}b_2=0$；读入后输出新接缝 $s_{\mathrm{new}}=b_0$。这里三位的印刷次序仍低到高，不能按印刷次序误读接缝方向。

**定理 25.2（粗类型的动态反例与单窗恢复）。** 仅保留 $\theta$ 不能决定实际窗口的后续合法性。对一个窗口，若另保留它的新接缝 $s=b_0$，则可唯一恢复三位：写 $\theta=(p,q)$，有

$$
b_0=s,\qquad b_2=p\oplus s,\qquad
b_1=q\oplus p\oplus s.
$$

此恢复在五模式上单射；在其两元素 $\bar\beta$ 纤维上，最坏情况下至少需要一个二值区别。

证明。从旧接缝零开始，单窗 $[3]$ 与 $[25]$ 都合法且均给类型 $\bar\beta$。但 $[3]$ 的新接缝为零，之后读 $[5]$ 合法；$[25]$ 的新接缝为一，而 $[5]$ 的最高位为一，故 $[25][5]$ 非法。因此相同类型产生不同的合法延拓，违反定义 20.1 的纤维条件。

恢复公式直接解 $p=b_0\oplus b_2$、$q=b_1\oplus b_2$。它事实上在全部八种三位串上给 $(\theta,s)$ 的逆，限制到五模式后仍单射。五个实际像依次是

$$
(0,0),\quad(\bar\alpha,1),\quad
(\bar\beta,0),\quad(\bar\beta,1),\quad
(\bar\gamma,0).
$$

任何能区分 $[3]$ 与 $[25]$ 的附加摘要，在同一个类型纤维中必须至少取两个值；$s$ 恰提供这个区别。公式恢复的是一个完整窗口。完整长词还需各窗口的顺序、层数及接缝；仅保留长词的累计类型和最后一位接缝，不因此恢复全部数量或历史。$\square$

**命题 25.3（角色全对称不能在原五模式上免费提升）。** 原五模式到非零角色的纤维大小依次为 $1,2,1$，故完整 $S_3$ 角色置换不能由五模式集合上的双射作用实现。端位置互换 $b_0\leftrightarrow b_2$ 保持五模式集合，诱导 $\bar\alpha\leftrightarrow\bar\gamma$、$\bar\beta$ 固定，但不保持原高到低守卫合同。若要求模式集合对三位置的全部置换封闭，包含原五模式的最小集合有七个模式，必须加入 $110,011$。

证明。若模式双射 $F$ 提升角色置换 $P$，即 $\theta F=P\theta$，则 $F$ 必在对应纤维间给双射。交换 $\bar\alpha,\bar\beta$ 要求大小一与大小二纤维双射，不可能；所以全群无此提升。

端位置互换将 $100,001$ 交换，将 $000,010,101$ 固定。由定义 24.1，它在模二组成上满足 $(p,q)\mapsto(p,p\oplus q)$，正给所述角色交换。然而原非法词 $[2][5]$ 在此变成合法词 $[5][2]$：前者的相邻接缝位均为一，后者较高窗最低位为零。故保持字母集合并不保持原方向的延拓合法性；同时反转读向等另一个合同必须单独说明。

全部位置置换保持占位数。零占位的轨道只有 $000$；一个占位的轨道是已有的 $100,010,001$；两个占位的 $101$ 的轨道还包含 $110,011$。这七种构成所需最小闭合集合，无需加入三占位串 $111$。新增的两串都有相邻占位，违反原窗口内无 $11$ 条件。因此七模式是更换语法后的候选集合，不能作为原五模式的免费对称扩张。$\square$

## 26. 四类型的完整实响应代数与概率边界

**定义 26.1（类型响应与共同分布）。** 对 $x=(a,b)\in V_2$，定义实值角色函数

$$
\chi_1(x)=(-1)^a,\qquad
\chi_2(x)=(-1)^b,\qquad
\chi_3(x)=(-1)^{a+b}=\chi_1(x)\chi_2(x).
$$

函数内积取均匀平均 $\langle f,g\rangle=\tfrac14\sum_{x\in V_2}f(x)g(x)$。另取一个固定共同来源的类型概率 $p(x)$，$p(x)\ge0$、$\sum_xp(x)=1$，并记 $r_i=\mathbb E_p\chi_i$。均匀内积是函数空间的定义，不要求实际来源分布均匀。

**定理 26.2（有限类型的完整线性响应与乘法闭包）。** 四个函数 $1,\chi_1,\chi_2,\chi_3$ 是全部实类型响应 $\mathbb R^{V_2}$ 的正交归一基；零均值子空间为三维。第三个非平凡响应不属于前两个的实线性张成。所有逐点乘积仍在这个四维代数内，故此有限类型任务无需无限高阶线性边界。

证明。按 $0,\bar\alpha,\bar\beta,\bar\gamma$ 的行次序，四个函数的值矩阵是

$$
C=\begin{pmatrix}
1&1&1&1\\
1&-1&1&-1\\
1&1&-1&-1\\
1&-1&-1&1
\end{pmatrix},\qquad C^TC=4I.
$$

所以各函数范数为一、互相正交，并且共有四个，形成四点上的全部函数空间之基。后三个的均匀均值为零，构成常数函数的三维正交补。若 $\chi_3$ 是 $\chi_1,\chi_2$ 的实线性组合，与 $\chi_3$ 取内积会给 $1=0$，故不可能。将常数也加入前两个的张成，结论仍相同。

逐点乘法满足

$$
\chi_i^2=1,\qquad
\chi_1\chi_2=\chi_3,\qquad
\chi_2\chi_3=\chi_1,\qquad
\chi_3\chi_1=\chi_2.
$$

因此任何次数的多项式响应都归约到四个基函数。这里使用的经典中间工具是二元 Boolean Fourier 奇偶基和特征函数的对称差乘法，见 Ryan O'Donnell，[*Analysis of Boolean Functions*，§§1.2–1.4](https://arxiv.org/html/2105.10386v1#Ch1.S3)，固定版本 [arXiv:2105.10386v1](https://arxiv.org/abs/2105.10386v1)。所列矩阵和乘法表把该工具接到当前四类型合同。

这不反驳定理 13.2：类型函数只有有限值域，其平方也会归约；那里要求原始无限来源上的无限值域函数及反复乘法闭包。只有更换为此有限商后的任务代数才是四维，不能由此声称原始树的全部任务有限闭合。$\square$

**定理 26.3（完整类型分布的三参数恢复与正性）。** 同一来源的三个响应唯一恢复四个类型概率：

$$
\begin{aligned}
p(0)&=\tfrac14(1+r_1+r_2+r_3),\\
p(\bar\alpha)&=\tfrac14(1-r_1+r_2-r_3),\\
p(\bar\beta)&=\tfrac14(1+r_1-r_2-r_3),\\
p(\bar\gamma)&=\tfrac14(1-r_1-r_2+r_3).
\end{aligned}
$$

可行参数集由这四个括号非负的条件精确给出，是四面体单纯形而不是球。$r_3=\mathbb E(\chi_1\chi_2)$ 一般不同于 $r_1r_2$；对于此二位分布，两者相等当且仅当两位独立。

证明。令概率列为 $p$，则 $(1,r_1,r_2,r_3)^T=C^Tp$。因 $C^TC=4I$，逆变换为 $p=\tfrac14C(1,r_1,r_2,r_3)^T$，得全部公式。反向这些数总和为一；四个非负条件正是它们构成概率的充要条件。四种确定类型的响应坐标为

$$
(1,1,1),\quad(-1,1,-1),\quad
(1,-1,-1),\quad(-1,-1,1).
$$

四列 $(1,r_1,r_2,r_3)^T$ 构成可逆矩阵，故这些顶点仿射独立，全部混合的像恰为它们的四面体。

两位各自的边缘律为 $\Pr(a)=\tfrac12(1+r_1(-1)^a)$、$\Pr(b)=\tfrac12(1+r_2(-1)^b)$。若 $r_3=r_1r_2$，恢复式变成

$$
p(a,b)=\tfrac14(1+r_1(-1)^a)(1+r_2(-1)^b),
$$

即边缘乘积；反向独立直接给期望乘法。具体地，$p(0)=p(\bar\gamma)=1/2$ 的两个边缘均匀，$r_1=r_2=0$、$r_3=1$；均匀四类型分布也给 $r_1=r_2=0$，却给 $r_3=0$。所以逐点乘法决定第三个函数，不等于两个边缘期望决定第三个期望。

恢复的对象仅为类型分布。确定模式 $[3]$ 与 $[25]$ 的类型分布完全相同，历史接缝却不同；单叶 $\alpha$ 与三叶树 $\langle\alpha,\langle\alpha,\alpha\rangle\rangle$ 也同属 $\bar\alpha$，树和数量却不同。因此三个响应不能补回商所遗忘的树、窗口或类型与接缝的联合关系。$\square$

## 27. 平移与循环对称下的四点等距几何

**假设 27.1（额外的忠实类型距离）。** 在 $V_2$ 上另给度量 $d$，要求不同类型有严格正距离，并要求

$$
d(x\oplus s,y\oplus s)=d(x,y),\qquad
d(\bar Mx,\bar My)=d(x,y)
\quad(x,y,s\in V_2).
$$

第一条是所有类型平移的等距性，第二条是 FIB 模二循环的等距性。这是新增距离合同，不将类型平移自动解释为原生嫁接的物理运输，也不声称原始树观察已经提供此距离。

**定理 27.2（四类型距离的唯一尺度与三维最小实现）。** 在假设 27.1 下，存在 $\ell_*>0$ 使所有不同类型的距离都为 $\ell_*$。该四点度量可等距嵌入欧氏三空间，且不能等距嵌入欧氏二维或更低维。一个单位外接球表示为

$$
z(x)=\frac1{\sqrt3}\bigl(\chi_1(x),\chi_2(x),\chi_3(x)\bigr),
$$

其不同顶点内积为 $-1/3$，距离平方为 $8/3$；一般边长 $\ell_*$ 以 $\ell_*\sqrt{3/8}\,z(x)$ 实现。

证明。以 $s=x$ 平移，$d(x,y)=d(0,x\oplus y)$。不同点的差为非零向量，而 $\bar M$ 在三个非零向量上传递循环。于是这三种从零出发的距离相等，全部非对角距离同为 $\ell_*>0$。

每个 $z(x)$ 的平方范数为一。对 $x\ne y$，记 $v=x\oplus y\ne0$，特征函数乘法给

$$
z(x)\cdot z(y)=\tfrac13\sum_{i=1}^3\chi_i(v)=-\tfrac13,
$$

因为任意非零类型的三个特征值恰有一个正一、两个负一。因此距离平方为 $1+1-2(-1/3)=8/3$，所给缩放达到任意 $\ell_*$。

再证明任意实现的维数下界。设欧氏点 $v_0,v_1,v_2,v_3$ 两两相距 $\ell_*$，平移到重心零，令 $G_{ij}=v_i\cdot v_j$。因 $\sum_jv_j=0$，每行 $G$ 的和为零，且

$$
\sum_{j=0}^3\|v_i-v_j\|^2
=4\|v_i\|^2+\sum_{j=0}^3\|v_j\|^2
=3\ell_*^2.
$$

左右比较不同 $i$ 得各点范数相同。记共同平方范数 $R^2$，上式给 $8R^2=3\ell_*^2$；对 $i\ne j$，等距式给 $G_{ij}=R^2-\ell_*^2/2=-\ell_*^2/8$。因此

$$
G=\frac{\ell_*^2}{2}\left(I_4-\frac14\mathbf1\mathbf1^T\right).
$$

括号是投向重心零三维子空间的正交投影，秩为三。若坐标矩阵的行是四个点，则 $G=VV^T$ 的秩至多嵌入空间维数，故维数至少三。上面的 $z$ 表示达到下界。Gram 与等距单纯形的经典线性代数在此作为距离合同的中间步骤，秩结论已从所声明的四点条件推得。$\square$

**命题 27.3（有限等距结论的精确范围）。** 三个非零角色自身不迫使欧氏三维：它们的等距子空间可实现为平面等边三角形。四类型距离的最小三维实现也不推出连续旋转群、连续位置空间或 Bloch 球。

证明。边长 $\ell_*$ 的三个点可取

$$
(0,0),\qquad(\ell_*,0),\qquad
(\ell_*/2,\sqrt3\,\ell_*/2).
$$

四点下界使用了零类型及全部六条等距边，不能仅由三角色的数目得到。另一方面，忠实四点度量上的每个等距双射都是四点的置换，最多只有 $24$ 个；保持四面体顶点集合的欧氏旋转也只能诱导其中的置换，故这个有限对象没有供应全部连续 $SO(3)$ 作用。第 26.3 条的概率族是顶点的凸包，边界有平面面片，并不是第九章的 Bloch 球体。把欧氏嵌入的周围连续空间也列为状态或位置，需要新增来源与任务，不能由四点嵌入本身取得。$\square$

## 28. 有向四元数提升与来源遗忘

**定义 28.1（标准有向乘法的附加合同）。** 在实四元数代数 $\mathbb H$ 中增加规则

$$
i^2=j^2=k^2=-1,\qquad ij=k,\quad ji=-k,
\qquad jk=i,\quad kj=-i,\quad ki=j,\quad ik=-j.
$$

乘法结合但不交换，单位为 $1$。其八元子群为 $Q_8=\{\pm1,\pm i,\pm j,\pm k\}$。给自由树定义乘法求值

$$
E(\alpha)=i,\qquad E(\beta)=j,\qquad
E\langle u,v\rangle=E(u)E(v).
$$

因此 $E(\gamma)=ji=-k$。乘法表是经典四元数结构，见 John C. Baez，[*The Octonions*，§2.1 “The Fano plane”](https://math.ucr.edu/home/baez/octonions/node4.html)；这里将它作为 FIB 有向递归的一个附加提升，不以四类型唯一推出此乘法。

**定理 28.2（FIB 轨道的三周期提升与模二回接）。** 对 $x_n=E(T_n)$，来源递归给

$$
x_{n+2}=x_{n+1}x_n,\qquad
x_0=i,\quad x_1=j,\quad x_2=-k,\qquad
x_{n+3}=x_n.
$$

其虚部方向 $i,j,-k$ 张成三维实空间。商群 $Q_8/\{\pm1\}$ 与 $V_2$ 同构，将 $[i],[j],[-k]$ 分别接到 $\bar\alpha,\bar\beta,\bar\gamma$；对任意树，这个忘号商中的 $[E(T)]$ 恰等于组成类型 $r(c(T))$。

证明。命题 21.2 的配对次序与求值定义直接给非交换递归。乘法表给

$$
ji=-k,\qquad(-k)j=i,\qquad i(-k)=j.
$$

这三式不断循环，归纳得轨道 $i,j,-k,i,j,-k,\ldots$。三个方向是标准虚部基中一个基向量换号，故实线性独立。此三周期发生在求值中，完整树的叶数仍按命题 21.2 增长。

$\{\pm1\}$ 是中心子群。商中 $[i]^2=[j]^2=[k]^2=[1]$，且 $[i][j]=[k]=[j][i]$，因为相反次序只差被消去的符号。四个商类 $[1],[i],[j],[k]$ 因而给二元二维向量群；$[-k]=[k]$。将两叶的商类接到两组成基，再按树结构归纳：配对求值的商类是两子树商类相加，恰与组成类型的相加相同。这证明全部树的忘号回接，但没有将全部树当成轨道；上述有向递归的周期结论只使用 $T_n$。也未以此宣称 $\rho$ 在所有四元数求值上具有某个未给出的统一作用。$\square$

**命题 28.3（有向提升的能力与连续旋转的附加条件）。** 求值 $E$ 能保留部分次序信息，但不能恢复自由树的全部次序与括号。它只是标准附加乘法的一种提升；若进一步使用完整实四元数及其范数，单位四元数的共轭才给连续旋转结构，而这一结构不由四类型或离散 FIB 轨道免费取得。

证明。$E\langle\alpha,\beta\rangle=k$、$E\langle\beta,\alpha\rangle=-k$，所以有向符号能分开这一对次序。可是结合性使不同树

$$
\langle\langle\alpha,\alpha\rangle,\beta\rangle,\qquad
\langle\alpha,\langle\alpha,\beta\rangle\rangle
$$

都求值为 $(ii)j=i(ij)=-j$，故括号已被忘掉。仅有四类型的加法表也没有指定符号的乘法规则；$V_2$ 自身就是没有这套有向符号的闭合加法模型，因而标准提升不能称为唯一强迫。

连续部分还使用 $q=q_0+q_1i+q_2j+q_3k$ 的实坐标、共轭 $\bar q$ 和范数 $|q|^2=q\bar q=\sum q_i^2$。对单位 $q$，映射 $v\mapsto qv\bar q$ 保持虚部和范数。若 $q=\cos(\theta/2)+n\sin(\theta/2)$，其中 $n$ 为单位虚向量，四元数乘法的标量积、向量积表达给

$$
qv\bar q=\cos\theta\,v
+(1-\cos\theta)(n\cdot v)n
+\sin\theta\,(n\times v).
$$

这是绕 $n$ 的角度 $\theta$ 旋转。轴角表示说明全部三维旋转可由这类实参数取得；$q$ 与 $-q$ 给相同共轭。若单位 $q$ 的共轭固定全部虚向量，它与 $i,j$ 都交换；由乘法表，其虚系数必须全零，故 $q=\pm1$。这给中心双覆盖的核。单位四元数为 $SU(2)$、双覆盖 $SO(3)$ 的经典对应见 Baez [Introduction](https://math.ucr.edu/home/baez/octonions/node1.html)，所用公式把该对应的范数与有向乘法前提写明。离散子群 $Q_8$ 和轨道三个值不包含这些连续角度；实际允许操作是否实现它们仍需新增合同。$\square$

## 29. 实际模二即时读者的五态与九态完成

**定义 29.1（固定即时输出与总化错误合同）。** 完整采用钉版来源定义 7.1 的读者：单位位固定为零；窗口从高到低输入；三位仍低到高打印；允许高端 $\mathrm{null}$ 填充；空词合法并输出零；每个合法有限前缀立即输出，没有 $\mathrm{End}$ 与最高窗非空守卫。活态为 $(s,x)$，其中 $s\in\{0,1\}$、$x=(a,b)\in V_2$，初态 $(0,(0,0))$。令 $A=M^3$，整数更新为 $x'=Ax+d_\sigma$，取模二后为 $x'=x\oplus\theta(\sigma)$。接缝和合法边为

| 模式 | 允许的旧接缝 $s$ | 新接缝 | 模二组成位移 |
| --- | --- | --- | --- |
| $\mathrm{null}$ | $0,1$ | $0$ | $0$ |
| $[2]$ | $0,1$ | $1$ | $\bar\alpha$ |
| $[3]$ | $0,1$ | $0$ | $\bar\beta$ |
| $[25]$ | $0$ | $1$ | $\bar\beta$ |
| $[5]$ | $0$ | $0$ | $\bar\gamma$ |

非法边进入吸收态 $\bot$，其后每个动作仍到 $\bot$。合法输出是 $\ell x\bmod2=b$，错误输出为不同于 $0,1$ 的独立标签 $\mathrm{err}$。两个状态行为相同，是指从它们出发，对全部有限后续词（包括空词）给相同即时输出。此最小确定性 Moore 语义复用所引来源定义 3.1、3.3；以下给模二实例的全部可达性与区分性证明。

**定理 29.2（窗口合同的精确五态商）。** 五窗口动作使全部八个活态以及错误态可达。仅使用这些窗口时，活态行为相同当且仅当它们具有同一个 $(s,b)$，故最小确定性即时输出机恰有四个活行为类与一个错误类，共五态。

证明。表中 $A\equiv I$，所以每次合法更新只异或模式位移。全部活态的可达代表如下，词按实际高到低输入顺序书写：

| 可达词 | 接缝 $s$ | 组成 $x$ | 当前合法输出 $b$ |
| --- | --- | --- | --- |
| $\varepsilon$ | $0$ | $0$ | $0$ |
| $[3]$ | $0$ | $\bar\beta$ | $1$ |
| $[5]$ | $0$ | $\bar\gamma$ | $1$ |
| $[3][5]$ | $0$ | $\bar\alpha$ | $0$ |
| $[2]$ | $1$ | $\bar\alpha$ | $0$ |
| $[3][2]$ | $1$ | $\bar\gamma$ | $1$ |
| $[5][2]$ | $1$ | $\bar\beta$ | $1$ |
| $[3][5][2]$ | $1$ | $0$ | $0$ |

前四个词始终在接缝零上，$[3]$ 与 $[5]$ 的位移分别为 $\bar\beta,\bar\gamma$，其和为 $\bar\alpha$。从这四种组成追加 $[2]$，接缝变一，组成异或 $\bar\alpha$，所以得到后四态。词 $[2][5]$ 非法，给可达错误态。表中无遗漏，因为活态空间总共只有 $2\cdot4=8$ 个点。

在摘要 $(s,b)$ 上，全部更新可写成

$$
\begin{aligned}
\mathrm{null}:&(s,b)\mapsto(0,b),\\
[2]:&(s,b)\mapsto(1,b),\\
[3]:&(s,b)\mapsto(0,b\oplus1),\\
[25]:&(0,b)\mapsto(1,b\oplus1),\\
[5]:&(0,b)\mapsto(0,b\oplus1),
\end{aligned}
$$

最后两种在 $s=1$ 时到错误。当前输出也是 $b$，故相同 $(s,b)$ 经任意后续词仍同摘要或同时错误；词长归纳给行为相同。这构造了五态实现的上界。

反向，同接缝而 $b$ 不同，由空词输出区分；接缝不同，由后缀 $[5]$ 的合法输出与错误标签区分；错误与任意活态由当前标签区分。这些测试使四个活类与错误两两不同。每类又有上述可达历史，任何确定性实现若合并两类，之后同一后缀便不能给不同输出，矛盾。因此至少五态，且达到上界。此即钉版来源定理 7.4 的 $m=2$ 实例；其一般公式 $2m^2/\gcd(m,2)+1$ 与本证明相符，经典整除语言计数的任务边界仍按来源定义 7.1 所附文献保留。五模式的字母表大小同为五，是另一个数量，未参与这个最小性推导。$\square$

**定义 29.3（保持历史接缝的额外原子动作）。** 改变任务族，另允许动作

$$
\mu(s,x)=(s,\bar Mx),\qquad \mu(\bot)=\bot.
$$

它只推进组成，按定义保留历史接缝，不等于窗口重编码。该合同取自钉版来源定义 7.5。例如 $[2]$ 的状态为 $(1,\bar\alpha)$，施加 $\mu$ 得 $(1,\bar\beta)$；单窗 $[3]$ 则给 $(0,\bar\beta)$。组成相同，守卫状态仍不同。

**定理 29.4（增加原子动作后的精确九态边界）。** 在窗口加 $\mu$ 的合同中，最小确定性即时输出机恰有八个活态与一个错误态，共九态。当前读数和一次原子读数恢复模二组成：

$$
y_0=b,\qquad y_1=\ell\bar Mx=a\oplus b,\qquad
b=y_0,\quad a=y_0\oplus y_1.
$$

证明。$\ell\equiv(0,1)$、$\ell M=(3,5)\equiv(1,1)$，因此得到两读数与逆式。原窗口的九个可达状态在新增动作后仍可达。若同接缝的两组成 $b$ 不同，空词区分；若 $b$ 相同而 $a$ 不同，一次 $\mu$ 后的输出 $a\oplus b$ 区分。不同接缝仍由 $[5]$ 区分，错误仍由当前独立标签区分。因此所有八个活态和错误态的行为两两不同。保留 $(s,a,b)$ 与吸收错误的确定性更新已给九态上界；可达、两两区分给任何实现的九态下界。

原五态商中，初态与词 $[3][5]$ 的状态都具有 $(s,b)=(0,0)$，差别仅是 $a=0$ 或 $1$。一次 $\mu$ 给不同输出，明确显示旧行为商不能承受新动作。钉版来源定理 7.6 的一般计数 $2m^2+1$ 在 $m=2$ 时同样给九；这里的恢复与区分证明限定为所声明的原子动作，不宣称实际树替换、接缝搬运或规范位串重编码已由同一个矩阵获得。$\square$

**定理 29.5（有限类型路线与二阶几何路线的条件汇合）。** 对本卷分别声明的来源、观察与任务，以下连接成立：完整 FIB 树来源持续增长；其三步恒等加法观察通过模二四类型因子化；三个非零类型构成全置换对称的补第三关系，但一步时间循环仅保留 $C_3$。实际五模式在类型纤维上仍需接缝区别；其完整模二即时数量任务有五态，增加保持接缝的原子动作后有九态。四类型的完整实函数代数为四维，去常数响应为三维；若另假设忠实距离的全部类型平移与循环等距性，四状态的欧氏最小嵌入维数为三。标准有向四元数则给带符号的轨道提升。上述有限类型路线与实、复二阶关系几何同在有条件的关系完成框架内，但没有由共同出现的维数三推出真实位置空间三维。

证明。命题 21.2 与定理 22.2 分别给来源增长和通用因子化；命题 22.3 说明任意进一步商的一步下降仍需核不变。定理 23.2 将角色关系对称与指定时间方向分开。命题 24.2 给实际窗口组成、类型与数量，定理 25.2 给同类型不同合法延拓的反例及新接缝的单窗恢复。定理 29.2、29.4 给同一实际高读表的两个精确任务商。定理 26.2、26.3 给完整函数代数及有限共同类型分布，不恢复被商去的来源或接缝。定理 27.2 的秩三下界使用额外四点距离假设；定理 28.2 使用额外有向乘法，命题 28.3 给其来源遗忘与连续结构的条件。

与这些有限对象相比，第二章的三维是齐次二次线性关系空间，确定来源的像仍有约束；第十六章的实正矩几何含规模一维与形状二维；第十八章的复行列式一三维全为形状方向，正性、复相位和尺子各已另设。第二十七章的三维来自四点等距 Gram 秩，第二十六章的三维来自四点函数空间去常数，第二十八章的三维来自选定四元数虚部。不同空间的对象、任务、运算与度量不同，数值维数相等不给它们的实际来源对应；第十九章的实观察相位盲核也仍存在。故各条可以通过已给映射分别用于关系完成，不能用三个或更多个“三”的并列替代未证的物理桥。$\square$

**假设 29.6（有限类型到实际运输的待证桥）。** 对一个欲解释为实际 FIB 观察与运输的系统，仍待定义并证明以下断言。其一，原生观察与运输任务为何应通过 $r\circ c$ 的类型商，且此商在所需操作下确实充分；第二十三章的角色闭合不承担这个选择。其二，类型边界如何保留全部必需的实际接缝及共同来源关系；单窗 $\theta+s$ 的恢复不能代替长历史与联合接缝证明。其三，四点等距关系如何扩展到连续局部位置空间，扩展保留哪些距离、拼接、操作与局部传播条件；有限单纯形的欧氏三维嵌入不承担此扩展。其四，有限类型任务如何与正二阶、相位取得、允许旋转及实际空间运输建立忠实对应；须同时说明第 20.3–20.5 条的任务闭合、相位操作和路径代价，不能由离散四元数求值或复矩阵代数免费获得。

这些断言须有明确的实际对象、观察、合法操作、共享接缝、精度和代价合同，并证明相关纤维性质与距离对应。前文只给条件数学及其反例边界，没有证明这些断言，也没有宣布真实空间必为三维。二阶多项式次数与空间微分阶数的区别继续保留；有限类型距离路线与实、复矩几何路线的桥接分别承担上述义务。

## 追加锚（本行以下为增补区）

## 30. 精确三次端点任务与二阶范数读出

**定义 30.1（组成二次读出与端点差商）。** 对实数 $a,b$ 定义

$$
Q(a,b)=a^2+ab+b^2,
\qquad
G=\begin{pmatrix}1&1/2\\1/2&1\end{pmatrix},
\qquad Q(a,b)=(a,b)G(a,b)^T.
$$

当 $(a,b)$ 是组成向量时，$Q$ 是该向量的二次读出；当 $a,b$ 是一个实标量的两个端点时，同一个多项式参与三次变化的因子化。这两个用法的对象不同。对 $a\ne b$ 定义有限差商 $D_3(a,b)=(a^3-b^3)/(a-b)$；其在整个 $\mathbb R^2$ 上的多项式延拓定义为 $\widetilde D_3=Q$。对角值指这个延拓的值，不指在 $a=b$ 时对零作除法。

**定理 30.2（二阶关系足够承担精确三次端点因子）。** 在定义 30.1 下，

$$
a^3-b^3=(a-b)Q(a,b),\qquad
D_3(a,b)=Q(a,b)\quad(a\ne b),\qquad
\widetilde D_3(a,a)=3a^2.
$$

而且

$$
Q(a,b)=\left(a+\frac b2\right)^2+\frac34b^2
=\frac34(a+b)^2+\frac14(a-b)^2,
$$

$$
\frac12(a^2+b^2)\le Q(a,b)\le\frac32(a^2+b^2).
$$

所以 $\|(a,b)\|_Q=\sqrt{Q(a,b)}$ 是二维实向量空间上的范数。它通过第二章的 $\nu_2(a,b)=(a^2,ab,b^2)$ 线性读出，三个二次分量没有增加一个原始实坐标。若沿用第四章同一来源的有限二阶矩，则 $\mathbb E Q(a,b)=U+V+W$。

证明（30.2）。展开 $(a-b)(a^2+ab+b^2)$，交叉三次项相消，剩下 $a^3-b^3$；在非对角上可除以 $a-b$，在对角上代入多项式给 $3a^2$。这是一条有限端点恒等式，没有近似余项。两种平方分解也由展开得到。矩阵 $G$ 在方向 $(1,1)$、$(1,-1)$ 上的特征值分别为 $3/2,1/2$；也可直接以

$$
Q-\tfrac12(a^2+b^2)=\tfrac12(a+b)^2\ge0,
\qquad
\tfrac32(a^2+b^2)-Q=\tfrac12(a-b)^2\ge0
$$

得到界及其达到条件。第一界使 $Q=0$ 当且仅当 $a=b=0$。

令 $R_Q(a,b)=(a+b/2,\sqrt3\,b/2)$，这是可逆实线性映射，且 $Q(a,b)=\|R_Q(a,b)\|_2^2$。因此齐次性与正定性直接成立。对任意 $u,v\in\mathbb R^2$，欧氏内积的 Cauchy–Schwarz 不等式给

$$
\|R_Q u+R_Q v\|_2^2
\le \|R_Q u\|_2^2+2\|R_Q u\|_2\|R_Q v\|_2+\|R_Q v\|_2^2,
$$

开平方得到三角不等式。这里复用第六章的内积中间工具。最后 $Q=(1,1,1)\nu_2$，有限二阶矩允许逐项取期望，遂得 $U+V+W$。本条将经典因式分解和正二次型用于已声明的 FIB 二阶关系读出，不赋予这些工具新的独创性。$\square$

**命题 30.3（标量端点距离与组成范数的分型）。** $d_Q(u,v)=\sqrt{Q(u-v)}$ 是 $\mathbb R^2$ 上由该范数产生的平移不变距离。对于实标量端点 $a,b$，其通常距离是 $|a-b|$；$\sqrt{Q(a,b)}$ 不等于这条端点距离。

证明（30.3）。范数的正定、对称与三角不等式分别给 $d_Q$ 的三条距离性质；共同平移不改变向量差。对标量取 $a=b=1$，端点距离为零，而 $\sqrt{Q(1,1)}=\sqrt3$，已经排除等同。若将标量轴另嵌入二维，例如 $a\mapsto(a,0)$，则 $d_Q((a,0),(b,0))=|a-b|$；这是向量差的范数，仍不是将两个标量端点直接放入 $Q(a,b)$。$\square$

## 31. 分圆三周期与相位平面的唯一不变尺子

**定义 31.1（第三分圆多项式与相位坐标）。** 取

$$
\Phi_3(t)=t^2+t+1,\qquad
\omega=-\frac12+\frac{\sqrt3}{2}i,
\qquad z_Q(a,b)=a-b\omega.
$$

有 $\omega^2+\omega+1=0$、$\omega^3=1$、$\overline\omega=\omega^2$。经典第三分圆表达式可参见钉版 Mathlib 的 [Polynomial.cyclotomic_three](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean#L382)。经典 Eisenstein 整数环为 $\mathbb Z[\omega]$，其范数 $N(m+n\omega)=m^2-mn+n^2$ 见 Greg McShane，[*Eisenstein integers and equilateral ideal triangles*, arXiv:2403.14375v1，§1.1](https://arxiv.org/abs/2403.14375v1)。这一引用只承担整数环范数这一中间工具，不承担 FIB 树读出、窗口操作或实际几何的桥接。

**定理 31.2（端点二次因子与三周期不变型）。** 对实 $a,b$，

$$
a^3-b^3=(a-b)(a-\omega b)(a-\omega^2b),
\qquad Q(a,b)=|z_Q(a,b)|^2.
$$

相位平面中乘以 $\omega$，在 $z_Q$ 坐标下由

$$
C=\begin{pmatrix}0&1\\-1&-1\end{pmatrix}
$$

表示，并满足 $C^2+C+I=0$、$C^3=I$、$C^TGC=G$。全部满足 $C^THC=H$ 的实对称双线性型恰为 $H=\lambda G$，$\lambda\in\mathbb R$；其中正定型恰对应 $\lambda>0$。

证明（31.2）。以 $\omega+\omega^2=-1$、$\omega\omega^2=1$ 展开后两个因子，得 $a^2+ab+b^2$。它们对实 $a,b$ 互为共轭，因此其积是 $|a-b\omega|^2$。尤其 $a^3-1=(a-1)\Phi_3(a)$。所引整数范数的二次表达式在这里沿用到实系数，取 $(m,n)=(a,-b)$，所以正号交叉项与通常 $m+n\omega$ 的负号交叉项相容。

又有

$$
\omega(a-b\omega)=b+(a+b)\omega
=z_Q(b,-a-b),
$$

故所给 $C$ 正确。矩阵乘法给

$$
C^2=\begin{pmatrix}-1&-1\\1&0\end{pmatrix},\qquad
C^2+C+I=0,
$$

再乘 $C-I$ 得 $C^3=I$。复绝对值在乘 $\omega$ 后不变，故 $Q(Cv)=Q(v)$；对称二次型的系数比较给 $C^TGC=G$。

为证明唯一性而不限于正定情形，写 $H=\begin{pmatrix}u&v\\v&w\end{pmatrix}$。直接计算

$$
C^THC=\begin{pmatrix}w&w-v\\w-v&u-2v+w\end{pmatrix}.
$$

与 $H$ 相等要求 $u=w$、$2v=w$，且这些条件使最后一个等式也成立。因此 $H=wG$；反向每个标量倍都不变。由 $G$ 的正特征值，$wG$ 正定当且仅当 $w>0$；$w=0$ 是零型，$w<0$ 是负定型。这证明的是指定二维作用 $C$ 下的结论，并不把任意 $C_3$ 表示的度量都判成一个参数。$\square$

**命题 31.3（三角色的二维相位实现与基向量符号）。** 令 $\mathsf A=1$、$\mathsf B=\omega$、$\mathsf\Gamma=\omega^2$，则三者之和为零、模长均为一，任意不同两者的实内积为 $-1/2$，故夹角为 $120^\circ$，乘 $\omega$ 循环三者。这是二维实平面上的相位实现。组成坐标映射 $z_Q$ 则把组成基 $c(\beta)=(0,1)$ 送到 $-\omega$，并不把它送到 $\mathsf B$。

证明（31.3）。三次单位根关系给和为零及循环。复平面视为实内积空间，内积为 $\operatorname{Re}(u\overline v)$；不同三次单位根之比为 $\omega$ 或 $\omega^2$，实部均为 $-1/2$。最后 $z_Q(0,1)=-\omega$。所以后文若另定义树读出 $h(\beta)=\omega$，那是另一个映射；不能在未说明节点规则的情况下把 $h$ 与 $z_Q\circ c$ 视为同一个坐标化。三角色的相位循环也没有引入第三个物理方向。$\square$

## 32. 原生增长与相位旋转的共同有限域

**定理 32.1（实动力分离而模二作用相合）。** 沿用原生组成推进 $M$ 与第 31.2 条的 $C$，有

$$
M^2-M-I=0,\qquad C^2+C+I=0,\qquad C\equiv M\pmod2,
$$

$$
M^3-I=2M=(M-I)(M^2+M+I),\qquad
M-I=M^{-1},\qquad M^2+M+I=2M^2.
$$

模二共同作用是三周期，实 $M$ 却既非三周期，也不保持 $Q$。原生 $M$ 及其组成合同引用 [FIB 关系延拓几何，钉版定义 1.1、1.3](https://github.com/the-omega-institute/trureturing/blob/61dcb1249a11ddc6745686bc6bc9cbc85d0e7936/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md)。

证明（32.1）。$M^2=\begin{pmatrix}1&1\\1&2\end{pmatrix}=M+I$，因此 $M(M-I)=I$ 且 $M^3=2M+I$。$M$ 与 $I$ 交换，通常三次因式分解可直接用于它们；代入 $M^2=M+I$ 得其余等式。$C$ 的负号模二消失，两个矩阵相同，两条二次多项式也都化成 $t^2+t+1$。故模二下 $M^3=C^3=I$，并由第二十三章的非零角色轨道知周期恰为三。

实矩阵 $M^3=\begin{pmatrix}1&2\\2&3\end{pmatrix}\ne I$。取组成 $(2,3)$，下一步为 $(3,5)$，而

$$
Q(2,3)=19,\qquad Q(3,5)=49.
$$

它们不等，排除 $M$ 保持这条相位尺子。进一步 $\det M=-1$、$\det C=1$，相似矩阵必须同列式，故它们不可能在实数域相似。模二类型的共同动力没有给出实增长与实旋转的共轭。$\square$

**定义 32.2（四元素域与选择的角色识别）。** 在 $\mathbb F_2[t]$ 中取

$$
\mathbb F_4=\mathbb F_2[t]/(t^2+t+1),\qquad
\eta=[t],\qquad
\iota:\mathbb F_2^2\longrightarrow\mathbb F_4,
\quad \iota(\bar a,\bar b)=\bar a+\bar b\eta.
$$

这一定义选择 $\bar\alpha\mapsto1$、$\bar\beta\mapsto\eta$；选择另一个根 $\eta^2$ 会给另一个识别。下文固定这一选择，不把域乘法认作原始树的有序配对。

**定理 32.3（模二加法关系与三周期乘法的相容）。** 定义 32.2 给一个域，元素恰为 $0,1,\eta,\eta^2$，且

$$
\eta^2=\eta+1,\qquad \eta^3=1,\qquad
\iota(\bar\gamma)=\eta^2,\qquad
\iota(\bar Mv)=\eta\,\iota(v).
$$

加法仍是第二十三章的异或；任意两个不同非零元素之和为第三个。乘 $\eta$ 实现已指定的三角色循环。

证明（32.3）。$t^2+t+1$ 在 $0,1$ 处均取一，没有根；二次多项式若可约必有一次因子，因而必有根，所以它不可约。任一剩余类唯一写成 $\bar a+\bar b\eta$，给四个元素，且不可约多项式商是域；在本例也可直接看 $1$ 自逆、$\eta\eta^2=1$，所以全部非零元素有逆。关系 $\eta^2=\eta+1$ 给 $\eta^3=\eta^2+\eta=1$。由所选基，$\bar\gamma=(1,1)$ 对应 $1+\eta=\eta^2$。对任意 $v=(\bar a,\bar b)$，

$$
\eta(\bar a+\bar b\eta)=\bar b+(\bar a+\bar b)\eta
=\iota(\bar Mv).
$$

域加法是逐系数模二加法，所以补第三关系没有改变。域乘法则是为表达这个循环增加的代数结构：树配对在组成商上是相加，不是相乘。$\square$

**命题 32.4（约化的合法定义域）。** 向 $\mathbb F_4$ 的含单位模二约化可以从整数二次环建立，不能从整个 $\mathbb R$ 或 $\mathbb C$ 建立。

证明（32.4）。若含单位环同态 $f:\mathbb R\to\mathbb F_4$ 或 $f:\mathbb C\to\mathbb F_4$ 存在，则 $f(2)=0$，但其定义域内 $2$ 可逆，于是 $1=f(2\cdot(1/2))=0$，矛盾。第三十三章将以 $\mathbb Z[\phi]/(2)$ 和 $\mathbb Z[\omega]/(2)$ 给出实际约化；不在实数或复数上定义这种同态。$\square$

## 33. 全树增长读出、负加法相位读出与模二交换

**定义 33.1（两种递归读出及其值域载体）。** 在第二十一章的完整自由有序树上取 $\phi=(1+\sqrt5)/2$，定义

$$
\begin{aligned}
g(\alpha)&=1,& g(\beta)&=\phi,&
g(\langle s,t\rangle)&=g(s)+g(t),\\
h(\alpha)&=1,& h(\beta)&=\omega,&
h(\langle s,t\rangle)&=-h(s)-h(t).
\end{aligned}
$$

这里 $g:T\to\mathbb Z[\phi]\subset\mathbb R$，$h:T\to\mathbb Z[\omega]\subset\mathbb C$。所用原生树、替换与组成仍为 [FIB 关系延拓几何，钉版定义 1.1、1.3](https://github.com/the-omega-institute/trureturing/blob/61dcb1249a11ddc6745686bc6bc9cbc85d0e7936/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md)。写“取值于”这两个环只指定余域，不断言树像填满环。$g$ 是增长观察，不是原生数量 $2a+3b$；$h$ 是新增的节点负加法合同，不是原始树语法本身的改写。

**定理 33.2（两种读出的全树等变）。** 对每一棵完整树 $t$，若 $c(t)=(a,b)$，则

$$
g(t)=a+b\phi>0,\qquad
g(\rho t)=\phi g(t),\qquad
h(\rho t)=\omega h(t).
$$

因此 $g(\rho^nt)=\phi^ng(t)$、$h(\rho^nt)=\omega^nh(t)$，特别 $h(\rho^3t)=h(t)$。这些读出等式不把三步后的树认作原树。

证明（33.2）。先对组成式与正性作结构归纳。两片叶分别给 $1=1+0\phi>0$ 和 $\phi=0+1\phi>0$；若式对 $s,t$ 成立，则组成相加与 $g$ 的相加给节点式，且两个正数之和为正。故对全部非空树成立。

等变也须在完整树上归纳，而不能仅检查单起点轨道。对叶 $\alpha$，

$$
g(\rho\alpha)=g(\beta)=\phi=\phi g(\alpha),\qquad
h(\rho\alpha)=h(\beta)=\omega=\omega h(\alpha).
$$

对叶 $\beta$，$\rho\beta=\langle\beta,\alpha\rangle$，所以

$$
g(\rho\beta)=\phi+1=\phi^2=\phi g(\beta),
\qquad
h(\rho\beta)=-\omega-1=\omega^2=\omega h(\beta).
$$

设两种等变式都对 $s,t$ 成立。替换保持有序配对，于是

$$
\begin{aligned}
g(\rho\langle s,t\rangle)
&=g(\rho s)+g(\rho t)
=\phi g(s)+\phi g(t)=\phi g(\langle s,t\rangle),\\
h(\rho\langle s,t\rangle)
&=-h(\rho s)-h(\rho t)
=-\omega h(s)-\omega h(t)=\omega h(\langle s,t\rangle).
\end{aligned}
$$

这完成全部构造子的结构归纳。对推进次数再作归纳给迭代式，$\omega^3=1$ 给三步相位相同。$g>0$ 与 $\phi>1$ 使增长值沿任何树轨道严格增长，也直接排除来源三周期；第二十一章的叶数论证仍适用。$\square$

**命题 33.3（相位不由未加深度的整数组成决定，也不完整编码树）。** 两棵同组成为 $(2,1)$ 的树满足

$$
h(\langle\alpha,\langle\alpha,\beta\rangle\rangle)=\omega,
\qquad
h(\langle\langle\alpha,\alpha\rangle,\beta\rangle)=2-\omega.
$$

同时，不同有序树 $\langle\alpha,\beta\rangle$ 与 $\langle\beta,\alpha\rangle$ 的 $h$ 值相同。因此 $h$ 既不是 $c$ 的函数，也不是全树单射编码。

证明（33.3）。内层 $h(\langle\alpha,\beta\rangle)=-1-\omega=\omega^2$，故第一棵值为 $-1-\omega^2=\omega$。另一内层 $h(\langle\alpha,\alpha\rangle)=-2$，故第二棵值为 $2-\omega$。两值之差 $2-2\omega\ne0$；叶计数均为两片 $\alpha$、一片 $\beta$。同组成不同相位排除 $h=\widehat h\circ c$。负加法在一个节点仍交换，所以 $h(\langle\alpha,\beta\rangle)=h(\langle\beta,\alpha\rangle)=\omega^2$，而自由有序树保留左右次序，二者不同。$\square$

**定理 33.4（两个整数二次环的共同约化与来源交换式）。** 存在含单位环同态

$$
r_g:\mathbb Z[\phi]\to\mathbb F_4,\quad
r_g(m+n\phi)=\bar m+\bar n\eta,
\qquad
r_h:\mathbb Z[\omega]\to\mathbb F_4,\quad
r_h(m+n\omega)=\bar m+\bar n\eta,
$$

其核分别为理想 $(2)=2\mathbb Z[\phi]$ 与 $(2)=2\mathbb Z[\omega]$。于是两个整数环模该理想的商都同构于 $\mathbb F_4$，并对全部树给

$$
r_g(g(t))=r_h(h(t))=\iota(r(c(t))),
\qquad r:\mathbb Z^2\to\mathbb F_2^2.
$$

推进后这一公共值乘以 $\eta$。这些交换式的每条约化箭头都从整数环或整数组成出发。

证明（33.4）。因为 $\phi$ 无理，每个 $m+n\phi$ 的整数系数唯一；以 $\phi^2=\phi+1$ 降次，$\mathbb Z[\phi]\cong\mathbb Z[t]/(t^2-t-1)$。严格地，首一多项式的整系数除法给唯一一次余式，余式在 $\phi$ 处为零只能两系数为零，所以这是精确的核。类似地，$\omega$ 的虚部非零保证 $m+n\omega$ 的系数唯一，以 $\omega^2=-\omega-1$ 得 $\mathbb Z[\omega]\cong\mathbb Z[t]/(t^2+t+1)$。

把两种一次余式的系数模二，两个乘法关系都化成 $\eta^2=\eta+1$，所以所给映射确为环同态。目标中 $1,\eta$ 是 $\mathbb F_2$ 基，一次余式约化为零当且仅当两个系数都是偶数，这正是理想 $(2)$；两个映射均满射，因为其像包含 $1,\eta$。商环同构由此得到。这里的满射是环到其商的满射，不是 $g$ 或 $h$ 的树像满射。

再对树证明公共值。叶 $\alpha$ 给一，叶 $\beta$ 给 $\eta$，与组成的约化一致。若结论对两子树成立，$g$ 在节点相加，而 $h$ 在节点的负号在特征二中消失，故二者约化都给两子树公共值之和；组成也恰相加。结构归纳完成交换式。第 33.2 条与 $r_g(\phi)=r_h(\omega)=\eta$，或第 32.3 条与 $c\rho=Mc$，均给推进乘 $\eta$。这使原生增长、相位三周期与四类型在此有限域内相合，不把实数与复数本身约化到域。$\square$

**命题 33.5（余域不等于树像）。** $g$ 的所有树值为正，故其像不是整个 $\mathbb Z[\phi]$。对于 $h$，另有初等商

$$
\mathbb Z[\omega]/(1-\omega)\cong\mathbb F_3,
\qquad m+n\omega\longmapsto m+n\pmod3,
$$

每棵树的像均为一，因而 $h$ 也不满射到 $\mathbb Z[\omega]$。本条不分类其完整树像。

证明（33.5）。$-1$ 属于 $\mathbb Z[\phi]$ 而不可能等于正的树值。对于第二个商，将 $\omega$ 置为一，关系 $\omega^2+\omega+1=0$ 化成 $3=0$，故映射到 $\mathbb F_3$ 良定义且满射。其核恰为 $(1-\omega)$：若 $m+n\equiv0\pmod3$，则

$$
m+n\omega=n(\omega-1)+(m+n),\qquad
3=(1-\omega)(2+\omega),
$$

两项均在该理想中；反向 $(1-\omega)$ 的像为零。叶 $\alpha,\beta$ 的商值均为一；若两子树商值为一，节点商值为 $-1-1=1$ 于 $\mathbb F_3$。归纳得全部树值均为一，所以例如环中的零没有树原像。此商仅用于排除满射，不与模二四类型商混同。$\square$

## 34. 窗口正选择、相位符号与七值轨道完成

**定义 34.1（窗口的正位置选择）。** 对低到高打印的三位 $w=b_0b_1b_2$，$b_j\in\{0,1\}$，定义形式选择多项式与两种读出

$$
P_w(t)=b_0+b_1t+b_2t^2,\qquad
p_{\mathrm{win}}(w)=P_w(\omega)\in\mathbb Z[\omega],
\qquad
\theta_4(w)=P_w(\eta)\in\mathbb F_4.
$$

这是所选位置相位的正线性和，独立于第三十三章树节点的负加法规则。原生五模式、整数贡献 $d(w)$、零层数量 $q_0(w)=\ell d(w)$ 与高到低守卫保持 [FIB 关系延拓几何，钉版定义 2.1、7.1](https://github.com/the-omega-institute/trureturing/blob/61dcb1249a11ddc6745686bc6bc9cbc85d0e7936/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md) 的合同。$P_w$ 也可作为全部八种三位串的形式记录，但形式记录不使非法位串成为原生模式。

**定理 34.2（实际五模式的符号区别与树、窗口合同分离）。** 实际表为

| 模式 | 三位 | $d(w)$ | $q_0(w)$ | $p_{\mathrm{win}}(w)$ | $\theta_4(w)$ | 新接缝 $b_0$ |
| --- | --- | --- | --- | --- | --- | --- |
| $\mathrm{null}$ | $000$ | $(0,0)$ | $0$ | $0$ | $0$ | $0$ |
| $[2]$ | $100$ | $(1,0)$ | $2$ | $1$ | $1$ | $1$ |
| $[3]$ | $010$ | $(0,1)$ | $3$ | $\omega$ | $\eta$ | $0$ |
| $[25]$ | $101$ | $(2,1)$ | $7$ | $-\omega$ | $\eta$ | $1$ |
| $[5]$ | $001$ | $(1,1)$ | $5$ | $\omega^2$ | $\eta^2$ | $0$ |

在全部三位串上，$r_h(p_{\mathrm{win}}(w))=\theta_4(w)=\iota(\theta(w))$。若树 $t$ 的整数组成恰为 $d(w)$，则 $r_h(h(t))=\theta_4(w)$，但这只给模二相同，不给直接的树相位与窗口相位相同。具体地，

$$
c(\langle\alpha,\gamma\rangle)=(2,1)=d(101),
\qquad
h(\langle\alpha,\gamma\rangle)=\omega,
\qquad P_{101}(\omega)=-\omega.
$$

$[3]$ 与 $[25]$ 的窗口相位互为相反数，范数与类型却相同；这些粗量仍不足以预测实际后续守卫。

证明（34.2）。逐位代入 $P_w$，并用 $1+\omega^2=-\omega$ 得五个相位值；用 $1+\eta^2=\eta$ 得 $101$ 的类型，其他行直接读出。组成 $d=(b_0+b_2,b_1+b_2)$ 给数量与接缝列，故 $[25]$ 仍是数量七，而非二十五。一般三位串满足

$$
P_w(\eta)=b_0+b_1\eta+b_2(1+\eta)
=(\bar b_0+\bar b_2)+(\bar b_1+\bar b_2)\eta
=\iota(\theta(w)).
$$

环同态 $r_h$ 逐系数约化并送 $\omega$ 到 $\eta$，故给第一条约化等式；再以第 33.4 条的树交换式给具有同组成树的模二等式。

另一方面 $\gamma=\langle\beta,\alpha\rangle$ 的 $h$ 值为 $\omega^2$，所以 $h(\langle\alpha,\gamma\rangle)=-1-\omega^2=\omega$，而正位置选择给 $1+\omega^2=-\omega$；它们在复数中不同，在模二中相同。这个具体见证阻止将两种递归合同偷换为一个读出。

最后 $|\omega|^2=|-\omega|^2=1$，两者模二都为 $\eta$，但相位符号不同。高到低读者的新接缝分别为零、一，之后输入 $[5]$ 的最高位为一：$[3][5]$ 合法，$[25][5]$ 非法。相位范数或四类型若遗忘此区别，不能恢复守卫；即使保留更多相位，也须按实际接缝合同证明其足够性。$\square$

**定理 34.3（相位轨道的最小七值完成与反向位置循环）。** 包含实际五个相位值且对乘 $\omega$ 封闭的最小集合为

$$
\mathcal P_7=\{0,1,\omega,\omega^2,-1,-\omega,-\omega^2\}.
$$

以形式位串实现时，原五模式之外恰需 $110,011$；$111$ 的相位为零，与 $000$ 碰撞，不在最小七位串集合内。乘 $\omega$ 对应位置选择的循环

$$
R_{\mathrm{win}}(b_0,b_1,b_2)=(b_2,b_0,b_1),
\qquad P_{R_{\mathrm{win}}w}(\omega)=\omega P_w(\omega).
$$

原生实际高到低语法没有因此获得这个动作。

证明（34.3）。实际相位集含 $0$ 及 $1,\omega,\omega^2$ 的完整轨道，还含 $-\omega$。其轨道必须补上 $-\omega^2,-1$，三个正相位与三个负相位两两不同：正相位的三次方为一，负相位的三次方为负一。加零共七值，且该集合已经对乘 $\omega$ 封闭，因此最小。

剩余三种位串的形式读出全部如下；位权和只是 $2b_0+3b_1+5b_2$ 的形式值，不是给非法串授予原生数量语义。

| 非原生位串 | 形式位权和 | $P_w(\omega)$ | $P_w(\eta)$ |
| --- | --- | --- | --- |
| $110$ | $5$ | $1+\omega=-\omega^2$ | $1+\eta=\eta^2$ |
| $011$ | $8$ | $\omega+\omega^2=-1$ | $\eta+\eta^2=1$ |
| $111$ | $10$ | $1+\omega+\omega^2=0$ | $1+\eta+\eta^2=0$ |

故两种缺失负相位由 $110,011$ 实现，$111$ 只重复已有零相位。包含原五位串的最小循环闭合集合是零占位轨道、单占位轨道、双占位轨道的并，共七串；$111$ 自成另一轨道。七串到 $\mathcal P_7$ 由表给一一对应。这与第 25.3 条的全部位置置换完成具有同一个七串集合，因为三位的单占位和双占位在三循环下各已遍历全部三个选择；它不说明位置置换与相位乘法是同一实际读者动作。

对任意三位，

$$
\omega P_w(\omega)=b_2+b_0\omega+b_1\omega^2,
$$

所以 $R_{\mathrm{win}}$ 的方向确为 $(b_2,b_0,b_1)$。相反循环 $(b_1,b_2,b_0)$ 对应乘 $\omega^2$。新增的 $110,011$ 都有相邻占位，违反窗口内无 $11$ 的原始条件；而循环把实际 $101$ 送到非法 $110$，已排除它是五模式上的动作。即使另给七串语法，跨窗接缝及可执行性仍须另外定义和证明。$\square$

## 35. 三循环的共同方向、相对平面与两种独立权重

**定义 35.1（实三循环及固定参考分解）。** 在带标准欧氏内积的 $\mathbb R^3$ 上取

$$
P=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix},
\qquad P(x,y,z)=(y,z,x),\qquad
\mathbf1=(1,1,1)^T.
$$

令 $E_{\parallel}=\mathbb R\mathbf1$、$E_{\perp}=\{(x,y,z):x+y+z=0\}$，相应的欧氏正交投影为

$$
\Pi_{\parallel}=\tfrac13\mathbf1\mathbf1^T,
\qquad \Pi_{\perp}=I-\Pi_{\parallel}.
$$

这里共同方向与相对平面是这个表示的子空间，不是已取得的三个物理方向。将 $P$ 作用在窗口位向量上时，其方向是第 34.3 条的反向循环，即 $P_{Pw}(\omega)=\omega^2P_w(\omega)$。

**定理 35.2（分圆平面与二阶范数的显式连接）。** 对独立实标量 $r,s$，

$$
P^3=I,\qquad
\det(rI-sP)=r^3-s^3=(r-s)(r^2+rs+s^2).
$$

$\mathbb R^3=E_{\parallel}\oplus E_{\perp}$，$P$ 在共同方向上为恒等，在相对平面的特征多项式为 $\Phi_3$。定义

$$
L:\mathbb R^2\to E_{\perp},\quad
L(x,y)=(x,y,-x-y),\qquad
L=\begin{pmatrix}1&0\\0&1\\-1&-1\end{pmatrix}.
$$

则 $L$ 是到相对平面的线性同构，且

$$
PL=LC,\qquad L^TL=2G,\qquad
\|L(x,y)\|_2^2=2Q(x,y).
$$

因此相对平面上的 $rI-sP$ 行列式正是 $r^2+rs+s^2$；两个行列式因子来自空间直和，不来自两个标量空间的相加。

证明（35.2）。三次坐标循环回到原位，故 $P^3=I$。矩阵

$$
rI-sP=\begin{pmatrix}r&-s&0\\0&r&-s\\-s&0&r\end{pmatrix}
$$

的行列式展开只有对角积 $r^3$ 与三循环积 $-s^3$，给因式分解。任意向量以其坐标均值乘 $\mathbf1$ 加一个零和向量，唯一分成两个所列子空间；两者对 $P$ 不变，$P\mathbf1=\mathbf1$。

$L$ 的前两坐标为输入，故单射；每个零和向量 $(x,y,z)$ 有 $z=-x-y$，故满射到平面。直接计算

$$
PL(x,y)=(y,-x-y,x)=LC(x,y),
\qquad
L^TL=\begin{pmatrix}2&1\\1&2\end{pmatrix}=2G.
$$

所以平面上的 $P$ 与 $C$ 共轭，特征多项式为 $t^2+t+1$，而

$$
\det(rI_2-sC)
=\det\begin{pmatrix}r&-s\\s&r+s\end{pmatrix}
=r^2+rs+s^2.
$$

共同线上的因子是 $r-s$，不变直和使行列式为两块行列式之积。$L$ 同时证明相位坐标中的 $Q$ 与所选三维欧氏参考的平面限制相差系数二；这是明确的表示桥，不是实际空间同一性。$\square$

**命题 35.3（三变量三次式的共同、相对分解）。** 对实 $x,y,z$，

$$
x^3+y^3+z^3-3xyz
=(x+y+z)(x^2+y^2+z^2-xy-yz-zx),
$$

$$
x^2+y^2+z^2-xy-yz-zx
=\tfrac12\bigl((x-y)^2+(y-z)^2+(z-x)^2\bigr).
$$

后一个因子等于 $\tfrac32\|\Pi_{\perp}(x,y,z)\|_2^2$，在共同线上为零；在相对平面 $z=-x-y$ 上，欧氏平方长度为 $2Q(x,y)$，该二次因子为 $3Q(x,y)$。

证明（35.3）。展开乘积，三种纯三次项留下，六种混合项两两相消，另留下 $-3xyz$。展开三个差的平方给第二式。设 $v=(x,y,z)$，投影恒等式给

$$
\tfrac32\|\Pi_{\perp}v\|_2^2
=\tfrac32\left(x^2+y^2+z^2-\tfrac13(x+y+z)^2\right)
=x^2+y^2+z^2-xy-yz-zx.
$$

共同线上的投影为零，相对平面上的投影为自身；第 35.2 条给两个平面读出。因此该三次分解辨别一个共同线性量与一个相对二次量，没有将二次因子变成第三个独立输入。$\square$

**定理 35.4（三循环与全位置置换都留下两种尺度）。** 对实对称正定矩阵 $H$，条件 $P^THP=H$ 当且仅当

$$
H=\lambda_{\parallel}\Pi_{\parallel}
+\lambda_{\perp}\Pi_{\perp},
\qquad \lambda_{\parallel}>0,\quad\lambda_{\perp}>0.
$$

两个权重独立；即使要求全部三位置置换 $S_3$ 都为 $H$ 等距，也不能迫使它们相等。若另存在一个对固定欧氏参考正交、同时满足 $R^THR=H$ 的线性映射 $R$，把参考单位共同向量 $e_{\parallel}=\mathbf1/\sqrt3$ 送到某个参考单位相对向量 $u_{\perp}\in E_{\perp}$，则必有 $\lambda_{\parallel}=\lambda_{\perp}$。不增加这种额外等距性时，权重相等须作为独立假设。

证明（35.4）。将 $H$ 写成一般对称矩阵。循环共轭把三个对角元循环置换，把三个无序坐标对的非对角元也循环置换，所以不变条件恰使对角元同为 $d$、非对角元同为 $e$。因此

$$
H=(d-e)I+e\mathbf1\mathbf1^T
=(d+2e)\Pi_{\parallel}+(d-e)\Pi_{\perp}.
$$

共同线上特征值为 $d+2e$，相对平面上两个特征值均为 $d-e$；正定当且仅当这两个数都正。反向任取两个正数，以 $e=(\lambda_{\parallel}-\lambda_{\perp})/3$、$d=(\lambda_{\parallel}+2\lambda_{\perp})/3$ 构造此型，就满足全部条件。每个位置置换均固定 $\mathbf1$ 且保持其欧氏正交补，因而保持两个投影。故例如 $2\Pi_{\parallel}+\Pi_{\perp}$ 已是全 $S_3$ 不变的权重不等反例。

在额外条件下，$e_{\parallel}^THe_{\parallel}=\lambda_{\parallel}$，$u_{\perp}^THu_{\perp}=\lambda_{\perp}$。由于 $Re_{\parallel}=u_{\perp}$ 且 $R$ 为 $H$ 等距，这两值相等。参考正交性明确保证所讨论的方向比较使用同一欧氏单位尺度；任意可逆变换不能代替该条件。例如对任意不等的两正权重，取一个欧氏正交映射 $O$ 将共同方向与一个相对方向交换，$R=H^{-1/2}OH^{1/2}$ 仍满足 $R^THR=H$，但送 $e_{\parallel}$ 到 $\sqrt{\lambda_{\parallel}/\lambda_{\perp}}\,u_{\perp}$，没有保持参考单位长度。故单说“有一个混合方向的 $H$ 等距变换”不足以推出权重相等。上述额外对称的实际可执行性及其物理解释也没有由 $C_3$ 或 $S_3$ 取得。$\square$

## 36. 三次观察的分支纤维与两因子摘要

**定义 36.1（两种精确恢复任务）。** 对复数取观察 $q_3(z)=z^3$；对实二元端点取观察

$$
F(a,b)=(d,\kappa),\qquad d=a-b,\qquad \kappa=Q(a,b).
$$

任务能由观察恢复，当且仅当它在每个非空观察纤维上恒定。这一集合论判据复用 [FIB 关系延拓几何，钉版定义 11.1](https://github.com/the-omega-institute/trureturing/blob/61dcb1249a11ddc6745686bc6bc9cbc85d0e7936/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md)。可计算、可取得及可认证恢复仍是额外要求，不由纤维恒定性自动提供。

**定理 36.2（复三次纤维及其离散分支信息）。** 对任意 $w\in\mathbb C$，$q_3^{-1}(0)=\{0\}$；若 $w\ne0$，其纤维恰为三个不同点 $\{z,\omega z,\omega^2z\}$，其中 $z$ 为任意一个三次根。因此非零来源相位及来源本身不能只由 $z^3$ 恢复。

若离散来源随机变量 $Z$ 在每个非零三次纤维上的条件分布均匀，令 $W=Z^3$，则保留来源所缺的离散条件信息为

$$
H(Z\mid W)=\Pr(Z\ne0)\log_2 3.
$$

特别地，单个非零三点纤维上均匀分布或无零质量的条件均匀分布给 $\log_2 3$ 比特；任意分布没有这个统一数值。为最坏情况下的三分支配固定长度二进制标签，至少需要二比特。

证明（36.2）。$z^3=0$ 在域中只可能 $z=0$。对于 $w\ne0$，写极坐标 $w=\rho e^{i\vartheta}$，$\rho>0$，取 $z=\rho^{1/3}e^{i\vartheta/3}$，给一个根。任意另一根 $u$ 与 $z$ 的比满足 $(u/z)^3=1$，因

$$
t^3-1=(t-1)(t-\omega)(t-\omega^2)
$$

只能取三个单位根；三者不同且 $z\ne0$，所以三个根不同。例 $1,\omega,\omega^2$ 的三次方均为一，相位不同，立即违反相位任务的纤维恒定性。

信息论断言限于离散来源或一个有限离散分支标签。对离散 $Z$，定义条件熵为对 $W$ 值的条件概率熵平均。零纤维只有一个点，熵为零；每个非零纤维条件概率为 $1/3$，其熵为 $-3(1/3)\log_2(1/3)=\log_2 3$，总非零权重为 $\Pr(Z\ne0)$，即得公式。等价地，每个非零纤维任选一个固定编号的三个分支，以离散标签 $B\in\{0,1,2\}$ 记录，零纤维固定标签零；在这样的离散合同下 $H(B\mid W)$ 给相同公式。这没有使用连续相位的微分熵。若非零条件概率为 $p_0,p_1,p_2$，熵为 $-\sum_jp_j\log_2p_j$，可小于 $\log_2 3$，集中在一支时为零。固定长度 $m$ 比特只有 $2^m$ 个码字，要三支不同须 $2^m\ge3$，故 $m\ge2$；例如 $00,01,10$ 达到此下界。$\square$

**命题 36.3（实数与有限域中的三次任务不同）。** $x\mapsto x^3$ 在 $\mathbb R$ 上单射；在 $\mathbb F_4$ 中，三个非零元素的三次方均为一，而零的三次方为零。

证明（36.3）。若实 $a^3=b^3$，第 30.2 条给 $(a-b)Q(a,b)=0$。当 $(a,b)\ne(0,0)$ 时 $Q(a,b)>0$，必有 $a=b$；零对也同样满足相等。因此实三次没有非零三分支纤维。有限域中非零元素恰为 $1,\eta,\eta^2$，由 $\eta^3=1$ 得它们都立方为一。该有限域观察的非零纤维有三个元素，与复三次相似的计数发生在另一个载体上；不把这三种任务的来源或熵合同混同。$\square$

**定理 36.4（实两因子摘要的完整纤维与非负域恢复）。** 对 $F$ 的全实定义域，像恰为

$$
\{(d,\kappa)\in\mathbb R^2:\kappa\ge d^2/4\}.
$$

记 $s_+=a+b$，则

$$
s_+^2=\frac{4\kappa-d^2}{3},\qquad
(a,b)=\left(\frac{s_++d}{2},\frac{s_+-d}{2}\right).
$$

等号 $\kappa=d^2/4$ 时纤维为单点，其 $s_+=0$；严格不等时恰有两个点 $(a,b)$ 与 $(-b,-a)$。若定义域限制为非负实数 $a,b\ge0$，则像恰为 $\kappa\ge d^2$，每个像点有唯一原像，包括原点。

证明（36.4）。第 30.2 条给 $\kappa=(3s_+^2+d^2)/4$。因此全实像必须满足第一不等式；反向，任取满足该不等式的实 $(d,\kappa)$，令 $s_+=\pm\sqrt{(4\kappa-d^2)/3}$，代入所给逆公式，便得到实 $a,b$ 且 $F(a,b)=(d,\kappa)$。当根为零时两个选择合一，给唯一点 $(d/2,-d/2)$；当根为正时两个选择不同，反号的和把 $(a,b)$ 送到 $(-b,-a)$。由于 $d$ 与 $s_+$ 已唯一决定 $a,b$，没有其他原像。

对非负实域，$a,b\ge0$ 当且仅当 $s_+\ge|d|$。于是 $\kappa=(3s_+^2+d^2)/4\ge d^2$。反向 $\kappa\ge d^2$ 使正根 $s_+=\sqrt{(4\kappa-d^2)/3}\ge|d|$，所给两坐标均非负；负根除 $d=\kappa=0$ 外不能非负，故原像唯一，原点仍只有零对。这些是实数域范围，不是整数树组成的充分检验。整数恢复还要求 $d\in\mathbb Z$、$s_+\in\mathbb Z$ 且 $s_+\equiv d\pmod2$，以及非空树所需 $a+b>0$；例如 $(d,\kappa)=(0,1)$ 满足两个实范围，却要求 $a=b=1/\sqrt3$，不是整数组成。$\square$

## 37. 有限三次总变化、非交换边界与条件汇合

**定理 37.1（有限实路径的精确三次总变化任务）。** 对任意有限实路径 $x_0,\ldots,x_N$，$N\ge0$，令 $\Delta x_k=x_{k+1}-x_k$，则

$$
\sum_{k=0}^{N-1}\Delta x_k\,Q(x_{k+1},x_k)
=\sum_{k=0}^{N-1}(x_{k+1}^3-x_k^3)
=x_N^3-x_0^3.
$$

其中空和为零。仅针对所声明的有向三次总变化任务，两个端点足够；闭合路径给总变化零，不给路径恢复。

证明（37.1）。对每一步将第 30.2 条代入，得 $\Delta x_kQ(x_{k+1},x_k)=x_{k+1}^3-x_k^3$，重复端点也因 $\Delta x_k=0$ 而正确。有限求和中每个内部 $x_k^3$ 出现一次正号、一次负号，相消后只剩末端减首端。$N=0$ 时两边均零。故有向总变化在固定端点的全部路径纤维上恒定，第 36.1 条的任务判据给充分性。它不含可达路径、接缝合法性或非有向代价的断言。$\square$

**命题 37.2（端点摘要无法恢复最大值、变差与额外路径任务）。** 对任意 $R>0$，等长路径 $(0,0,0)$ 与 $(0,R,0)$ 的端点及三次总变化完全相同，但最大值分别为零、$R$，总变差分别为零、$2R$；平方增量代价分别为零、$2R^2$。将有限三次每步因子任意改成单个端点平方，一般失去恒等式。

证明（37.2）。两路径起终点均零，故第 37.1 条的总变化均零。直接取最大值、计算 $\sum_k|x_{k+1}-x_k|$ 和 $\sum_k(x_{k+1}-x_k)^2$，得三个差异。更一般地，随 $R$ 改变，中间峰值与变差无界，仍有相同端点。因此这些任务在端点纤维上不恒定，无法由端点摘要恢复；失败条件或共同接缝若是额外路径数据，也须独立说明与保留，而不是由有向总变化取得。

交叉项 $ab$ 是 $Q=a^2+ab+b^2$ 的确切系数。若删去它，单步 $(b,a)=(1,2)$ 的立方差为七，$(a-b)(a^2+b^2)$ 却为五；若只取右端平方则为四，左端平方则为一。对该对不等端点任何正确因子必须等于 $Q$，因为可以除以 $a-b$；任意端点平方替换不能给全域相同的有限律。即使引入势函数 $x^3/3$，它在整个 $\mathbb R$ 上无下界，因为 $x\to-\infty$ 时趋于负无穷；这条代数恒等式没有提供物理作用量、能量正性或稳定性假设。$\square$

**定理 37.3（安全的有序三次展开与朴素因式分解的反例）。** 在任意实或复结合代数中，对元素 $A,B$ 有

$$
A^3-B^3=A^2(A-B)+A(A-B)B+(A-B)B^2.
$$

若 $AB=BA$，则还可写成 $(A-B)(A^2+AB+B^2)$。交换是这一通常因式分解的充分条件，却不是某一对元素偶然满足该等式的必要条件。

证明（37.3）。只保留既定因子次序展开，右边为

$$
A^3-A^2B+A^2B-AB^2+AB^2-B^3=A^3-B^3.
$$

相消不需要交换。若 $AB=BA$，可以把首两项中的 $A-B$ 移到最左，三项的其余因子分别为 $A^2,AB,B^2$，得通常因式分解。对一般 $A,B$，其朴素左因子版本与真正立方差的差恰为

$$
(A-B)(A^2+AB+B^2)-(A^3-B^3)
=A(AB-BA)+(AB-BA)(A+B).
$$

这由有序展开，或把差写为 $A^2B-BA^2+AB^2-BAB$ 得到。这个差可以在非交换时为零，不能把充分条件倒写成必要条件。

具体失败取 $2\times2$ 矩阵单位 $A=E_{12}$、$B=E_{21}$。它们满足 $A^2=B^2=0$、$AB=E_{11}$、$BA=E_{22}$，故

$$
A^3-B^3=0,\qquad
(A-B)(A^2+AB+B^2)=(E_{12}-E_{21})E_{11}=-E_{21}\ne0.
$$

若改用朴素右因子版本，则 $E_{11}(E_{12}-E_{21})=E_{12}\ne0$，也失败。为明确交换非必要，另取

$$
A=E_{12},\qquad B=E_{23}
\quad\text{于 }3\times3\text{ 矩阵代数}.
$$

此时 $AB-BA=E_{13}\ne0$，但 $E_{12}E_{13}=0$ 且 $E_{13}(E_{12}+E_{23})=0$，故朴素左因子式确与立方差同为零。安全有序式则对所有这些元素都成立。自由有序树的构造子、第二十八章增加合同后的四元数乘法及实际操作的复合各有自己的类型与规则；不能因标量三次恒等式成立，就把它们自动视为可交换实端点。$\square$

**定理 37.4（共同分圆核心的有条件关系完成）。** 在本卷已声明的对象与合同内，$\Phi_3$ 同时组织三次端点的二阶因子、二维相位三周期及 FIB 模二四类型；原生增长与相位读出共享 $\mathbb F_4$ 约化，但不共享实增长尺子。实际五模式的窗口正选择能保留 $[3]$ 与 $[25]$ 的相位符号区别，范数或类型则丢失它；两模式的实际接缝区别仍在。三循环表示提供共同一维与相对二维的直和，循环对称只规定相对平面内的等尺子，不能规定共同方向与相对方向权重相等。立方观察或两因子摘要能恢复哪些任务，由各自实际纤维决定；有限实路径的端点只承担已声明的三次总变化任务。

证明（37.4）。第 31.2 条把三次端点的二次因子识别为 $|a-b\omega|^2$，同时求出具体 $C$ 的全部不变对称型；第 32.1–32.3 条把 $M$ 与 $C$ 的模二作用接到所选 $\mathbb F_4$ 乘法，并以列式与 $Q$ 的实际取值排除实动力等同。第 33.2 条的完整结构归纳保证两种全树等变，第 33.4 条将它们接到同一模二组成；第 33.3 条又以同组成见证排除未加深度的树相位恢复。因此共同有限域是这些指定映射的共同观察，并非来源的完整身份或实几何同一性。

第 34.2 条的实际五行给 $\omega$ 与 $-\omega$、相同范数与模二类型、不同新接缝；第 34.3 条说明相位轨道完成引入非法窗口，故它没有授予原生相位控制。第 35.2 条的 $L$ 同时给 $PL=LC$ 与 $L^TL=2G$，明确连接相位平面与相对平面；第 35.4 条保留两种独立权重，并给权重相等所需的额外参考兼容条件。因此 $1+2$ 是此表示的直和，不是物理各向同性的证明。第 36.2–36.4 条完整分类所用纤维，限定了相位分支信息和实非负恢复的条件；第 37.1–37.3 条则限定精确总变化的任务与标量交换边界。逐项组合这些已给映射和条件即得陈述，不把不同对象的数目、维数或相似公式当作额外桥梁。经典分圆、整数环、范数、纤维与有序展开在上述连接中承担中间工具，不据此宣称世界新颖性。$\square$

**假设 37.5（尚待建立的原生、取得与运输桥）。** 若要把这些关系解释为原生 FIB 的完整边界或实际空间运输，须另行定义来源、允许操作、目标、共同接缝与量具，并证明下列断言：所需任务在选定二阶或有限类型边界上闭合，包含实际合法域、联合来源及接缝；相位可由原生操作取得并按所需方式控制，而非仅在外加环与负加法规则中表达；共同方向与相对方向具有足以支持所需各向同性的实际对称；离散角色或有限纤维模型能在所需连续局部运输中保留距离、拼接及资源；关系距离与实际运输距离有明确且保真的对应。原生二阶选择及反复操作是否无需无界高阶、有限模型如何延伸到连续对象，也仍需各自的假设与证明。前述有限恒等式、三周期商、七值完成及端点任务不证明这些断言，也不因可作无界多次迭代而自动提供物理或无限极限结论。

## 追加锚（本行以下为增补区）
