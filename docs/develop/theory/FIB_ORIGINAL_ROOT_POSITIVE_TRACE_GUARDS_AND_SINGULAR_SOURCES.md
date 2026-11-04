# FIB 原根正迹守卫与奇异源层

## 1. 完整目标、原时钟与原根问题

本卷研究完整三次增益域的原根源可行域。正迹递推给出若干整族源配置的守卫失败，四个初始 $M$ 的唯一正迹奇异层有实际合法碰撞，而纯 $J$ 叶的同源守卫可以完全分类。这些是通向完整原根问题的结构性部分结果；完整可行域的空与非空均未在此判定。

**定义 1.1（原始模型）。** 两个允许的单步作用为

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

合法源集合为

$$
\mathcal P=\left\{
P=\begin{pmatrix}a&b\\c&1-a\end{pmatrix}:
0<a<1,\quad b,c>0,\quad bc=a(1-a)
\right\}.
\tag{1.1}
$$

它恰是严格逐项正、秩一、迹一的实二阶矩阵集合，包含合法的对称源和非对称源，不对条目另设有界性条件。完整世界及其恢复目标均为

$$
W=(P,g,\delta)\in\mathcal W_3,
\qquad P\in\mathcal P,\quad
0\ne g\in\mathbb R[T],\quad\deg g\le3,\quad\delta\in\mathbb R.
\tag{1.2}
$$

这里 $g\ne0$ 指整个多项式非零；允许正负两种符号、实际次数零至三、采样点根与重根，漂移 $\delta$ 是任意实常数。按时间先后执行 $E_1,\ldots,E_i\in\{M,J\}$ 时，累计矩阵和读数为

$$
A_0=I,\qquad A_i=E_iA_{i-1}=E_i\cdots E_1,
\qquad z_i=g(i)\operatorname{tr}(A_iP)+\delta.
\tag{1.3}
$$

初读计入预算。至多八次总读数使用原时钟 $0,\ldots,7$；只有一条不可重置、不可复制的轨迹，每个单独的 $M$ 或 $J$ 之后立即读数。不允许跳读、空作用读数、未读的复合作用、重编号时钟或额外传感器。确定性策略可任意依赖整个实际历史选择动作、停止及返回完整目标，不要求这些函数连续或可测。

**定义 1.2（失败与平移）。** 对实际历史 $H$，令 $\mathcal F(H)$ 为实现该历史全部动作和读数的完整目标集合。若 $K\subseteq\mathcal F(H)$，定义

$$
\begin{aligned}
L_0(K,H)&\Longleftrightarrow |K|\ge2,\\
L_s(K,H)&\Longleftrightarrow L_0(K,H)\ \land\
\bigwedge_{E\in\{M,J\}}\exists z\in\mathbb R:
L_{s-1}\bigl(K\cap\mathcal F(H,E,z),(H,E,z)\bigr).
\end{aligned}
\tag{1.4}
$$

$s$ 不超过剩余原时钟预算。该递归同时保留两个动作、实际响应子纤维和提前停止；它对兼容目标集合的包含关系向上单调。每个未选动作的响应只是固定世界的数学预测，不是额外取得的读数。

任意实际初读 $a_0$ 满足 $a_0=g(0)+\delta$。映射

$$
(P,g,\delta)\longmapsto(P,g,\delta-a_0)
\tag{1.5}
$$

将整个初读 $a_0$ 的纤维双射到初读零域 $\mathcal I_0$，并在每条动作词上将全部读数减去 $a_0$。逆映射给漂移加回 $a_0$；源、增益、动作、响应分割和原时钟均被保留。因此初读零是可逆坐标选择，不是初始增益为零或漂移为零的承诺。初读零域上的完整策略可通过实际取得的 $a_0$ 平移到全域。

本卷复用 [IV 定义 1.1–1.2、定理 9.3、定义 13.1–13.2、定理 13.3 与第 14 节](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md) 的原根系统。完整问题仍是：是否不存在覆盖全部 $\mathcal W_3$ 的至多八读确定性协议，从而需要至少九读；或者是否存在这样的至多八读协议。这里的至少九读只表示下界，不附带九读上界。

## 2. 二百五十六槽与一个共同核

**定义 2.1（原根源元组与响应矩阵）。** 取

$$
\mathcal S=\{(w,e):w\in\{J,M\}^7,\ e\in\{0,1\}\},
\qquad
\mathcal V=\bigcup_{i=1}^7\{J,M\}^i.
\tag{2.1}
$$

共有 $256$ 个槽和 $254$ 个非空前缀。固定一个合法源元组

$$
\mathbf P=(P_q)_{q\in\mathcal S}\in\mathcal P^{\mathcal S}.
$$

允许不同槽的源重复，包括同一叶的两个源相同。对于按时间排列的前缀 $v=E_1\cdots E_i$，令

$$
A_v=E_i\cdots E_1,\qquad
\mathcal D_v=\{(w,e):v\text{ 是 }w\text{ 的前缀}\}.
\tag{2.2}
$$

槽按 $J<M$、$0<1$ 的字典序排列，$q_v$ 为 $\mathcal D_v$ 的首槽。定义

$$
\begin{aligned}
t_v(P)&=\operatorname{tr}(A_vP),\\
\ell_v(P)&=(t_v(P)-1,\ i\,t_v(P),\ i^2t_v(P),\ i^3t_v(P)).
\end{aligned}
\tag{2.3}
$$

四维系数块 $x_q=(x_{q0},x_{q1},x_{q2},x_{q3})^{\mathsf T}$ 对应

$$
g_q(T)=x_{q0}+x_{q1}T+x_{q2}T^2+x_{q3}T^3,
\qquad\delta_q=-x_{q0}.
\tag{2.4}
$$

其初读为零，在前缀 $v$ 的读数恰为 $\ell_v(P_q)x_q$。完整世界合法还须 $x_q\ne0$。这是 IV 定义 9.1 的坐标变换，保留任意增益形状和漂移。

令 $x=(x_q)_q\in\mathbb R^{1024}$。唯一的联合响应矩阵 $B=B(\mathbf P)$ 每行由 $v\in\mathcal V$ 和 $q\in\mathcal D_v\setminus\{q_v\}$ 标记：

$$
(Bx)_{v,q}=\ell_v(P_q)x_q-\ell_v(P_{q_v})x_{q_v}.
\tag{2.5}
$$

其他槽块的行系数为零。深度 $i$ 的行数是 $2^i(2^{8-i}-1)=256-2^i$，故七层行数依次为

$$
(254,252,248,240,224,192,128),\qquad
B\in\mathbb R^{1538\times1024}.
\tag{2.6}
$$

若 $P_q=(\begin{smallmatrix}a_q&b_q\\c_q&1-a_q\end{smallmatrix})$，则

$$
t_v(P_q)=(A_v)_{22}
+((A_v)_{11}-(A_v)_{22})a_q
+(A_v)_{21}b_q+(A_v)_{12}c_q.
\tag{2.7}
$$

所以矩阵条目是 $768$ 个环境源坐标的整数仿射多项式。全部 $256$ 个等式 $b_qc_q=a_q(1-a_q)$ 及严格源不等式仍须保留；$768$ 是环境坐标数，不是无约束合法源空间的维数。

**定义 2.2（完整守卫）。** 令

$$
G_qx=x_q,\qquad
D_wx=x_{(w,0)}-x_{(w,1)},\qquad
\mathcal U=\ker B(\mathbf P).
\tag{2.8}
$$

$G_q$ 和 $D_w$ 均为 $4\times1024$ 的常矩阵。$D_w$ 保留全部四个系数差，不能用一个指定系数或一次采样之差代替。在初读零坐标中，同一叶的两个完整目标不同，当且仅当

$$
P_{(w,0)}\ne P_{(w,1)}\quad\text{或}\quad D_wx\ne0.
\tag{2.9}
$$

若源不同，完整目标已不同；若源相同，四维系数差非零恰好保证完整目标不同，漂移差等于常数系数差的负值。

**复用定理 2.3（IV 的精确源投影）。** 记 $r=\operatorname{rank}B$，$[B;T]$ 表示竖直拼接。该固定源元组能实现完整原根失败系统，当且仅当

$$
\begin{aligned}
\operatorname{rank}[B;G_q]&>r&& (q\in\mathcal S),\\
P_{(w,0)}\ne P_{(w,1)}\quad\text{或}\quad
\operatorname{rank}[B;D_w]&>r&& (w\in\{J,M\}^7).
\end{aligned}
\tag{2.10}
$$

用 $\Phi(\mathbf P)$ 表示这组全部守卫，并令

$$
\mathfrak S_7=\{\mathbf P\in\mathcal P^{\mathcal S}:\Phi(\mathbf P)\}.
\tag{2.11}
$$

则 $\mathfrak S_7\ne\varnothing$ 当且仅当每个全域至多八读确定性协议失败；$\mathfrak S_7=\varnothing$ 当且仅当存在一个全域至多八读协议。

为说明本卷使用该已证投影的确切接口，$Bx=0$ 等价于所有共享响应方程

$$
\ell_v(P_q)x_q=z_v\quad(q\in\mathcal D_v),
\qquad z_v=\ell_v(P_{q_v})x_{q_v}.
\tag{2.12}
$$

此等价在整个线性核上成立，包括含零块的向量。对任意线性映射 $T$，秩与零化度给出

$$
\operatorname{rank}[B;T]-\operatorname{rank}B
=\operatorname{rank}(T|_{\mathcal U}).
\tag{2.13}
$$

例如将 $(Bx,Tx)$ 的像投影到 $\operatorname{im}B$，其核恰为 $\{(0,Tu):u\in\mathcal U\}$，即得此式。因此每个必需守卫是相应映射在同一个 $\mathcal U$ 上非零。全部守卫成立后，IV 定理 13.3 的有限子空间回避才给出一个同时合法的向量：对每个必需映射 $T_j$ 选 $u_j\in\mathcal U$ 和分量 $L_j$ 使 $L_j(u_j)\ne0$；则

$$
u(t)=\sum_{j=1}^m t^{j-1}u_j
\tag{2.14}
$$

的每个 $L_j(u(t))$ 都是非零多项式，因为其 $t^{j-1}$ 系数就是 $L_j(u_j)$。在这些有限根集之外取同一个 $t$，即可同时使全部 $G_qx$ 和全部适用的 $D_wx$ 非零。这里 $256\le m\le384$；分别找到不同映射的见证，不等于已得到同时合法世界。

其原根含义也仍按 IV：每叶的两个不同固定目标实现其全部祖先读数；每个选定响应子纤维包含相应后代目标族。沿 (1.4) 向上归纳，两个动作与所有停止节点均得到失败。反向展开 $L_7(\mathcal I_0,(0))$ 则选出这样的固定叶对和共同祖先响应。初读平移 (1.5) 将此结论双向输运到全域。这些是复用的源投影与有限树结论，秩与零化度及有限子空间回避本身不计为本卷新结果。

若需显式区分全部秩层，可沿用 IV 的平方子式记法

$$
\mu_k(C)=\sum_{|I|=|J|=k}\det(C_{I,J})^2,\qquad\mu_0(C)=1,
$$

超出矩阵行列数时取零。令

$$
s_w=2(a_{(w,0)}-a_{(w,1)})^2
+(b_{(w,0)}-b_{(w,1)})^2+(c_{(w,0)}-c_{(w,1)})^2.
$$

则 (2.10) 等价于有限公式

$$
\bigvee_{r=0}^{1024}\left[
\mu_r(B)>0\ \land\ \mu_{r+1}(B)=0
\ \land\ \bigwedge_q\mu_{r+1}([B;G_q])>0
\ \land\ \bigwedge_w\bigl(s_w>0\ \lor\ \mu_{r+1}([B;D_w])>0\bigr)
\right].
\tag{2.15}
$$

它消去 $1024$ 个增益及漂移自由坐标和 $254$ 个共享响应，保留上述全部合法源约束。此处的规模计数及公式不提供可行性值或计算资源界。若 $\mathcal U=\{0\}$，全部增益守卫均失败；该秩层并未被排除在定义之外。

## 3. 正迹与固定源差多项式

**引理 3.1（严格正迹）。** 对任意合法源 $P$ 及任意累计矩阵 $A_i$，矩阵 $A_iP$ 严格逐项正，因而

$$
t_i(P)=\operatorname{tr}(A_iP)>0,\qquad t_0(P)=1.
\tag{3.1}
$$

**证明。** $M,J$ 都是非负可逆矩阵，其乘积 $A_i$ 亦然。可逆性使 $A_i$ 每行至少有一个正项；用该行乘严格正矩阵 $P$ 的任一列得到严格正数。因此 $A_iP$ 的每个条目均正，特别是迹正。无需源对称性，也无需给迹设统一上下界。∎

**定义 3.2（路径响应矩阵）。** 对原时钟前缀 $v=E_1\cdots E_k$ 及固定源 $P$，令 $R_v(P)$ 为 $k\times4$ 矩阵，其第 $i$ 行为

$$
(t_i(P)-1,\ i\,t_i(P),\ i^2t_i(P),\ i^3t_i(P))\quad(1\le i\le k).
\tag{3.2}
$$

若 $h(T)=h_0+h_1T+h_2T^2+h_3T^3$，则 $R_v(P)h=0$ 等价于

$$
t_i(P)h(i)=h(0)=c_0\quad(0\le i\le k).
\tag{3.3}
$$

其中时钟零的等式自动成立。

**引理 3.3（同一个联合核上的桥梁）。** 固定任意合法源元组，任取 $x\in\mathcal U$。若 $q,r\in\mathcal D_v$ 且 $P_q=P_r=P$，则 $h=g_q-g_r$ 满足 (3.3)。因此 $\operatorname{rank}R_v(P)=4$ 蕴含 $x_q=x_r$，且此结论对 $\mathcal U$ 中每个向量均成立。

**证明。** 对 $v$ 的每个非空祖先 $v_i$，$q,r$ 都在 $\mathcal D_{v_i}$ 中，(2.5) 使它们的读数同等于该前缀的参考响应。相减后得到

$$
t_i(P)(g_q(i)-g_r(i))-(g_q(0)-g_r(0))=0,
$$

因为漂移差恰为 $-h(0)$。这就是 (3.3)，包括时钟零。若 $R_v(P)$ 满列秩，其核只有零，故全部四个系数差均零。论证对零块亦成立，并包括 $q$ 或 $r$ 是参考槽的情况。它只比较同一条已规定历史的共同祖先，没有比较两个未取得动作的读数。∎

## 4. 任意位置的五个连续 M

**定理 4.1（五个连续 $M$ 的统一满秩）。** 对任意 $P\in\mathcal P$，若原时钟前缀 $v$ 含五个连续 $M$ 动作，则 $R_v(P)$ 秩为四。该固定源论证事实上只需 $P$ 严格正、迹一；在原根应用中仍保留合法秩一条件。

**证明。** 设 $h$ 满足 (3.3)，五个 $M$ 位于动作 $j+1,\ldots,j+5$。若 $c_0=0$，严格正迹立即给出 $h(j)=\cdots=h(j+5)=0$，次数至多三的 $h$ 只能为零。

现设 $c_0\ne0$。由 $M^2=M+I$，该段迹满足斐波那契递推。令

$$
s=t_j>0,\qquad r=\frac{t_{j+1}}{t_j}>0.
$$

原时钟 $j,\ldots,j+5$ 的六个迹依次是

$$
s(1,\ r,\ 1+r,\ 1+2r,\ 2+3r,\ 3+5r).
\tag{4.1}
$$

定义四阶前向差分

$$
\Delta^4f_n=f_{n+4}-4f_{n+3}+6f_{n+2}-4f_{n+1}+f_n.
$$

三次或更低次多项式的四阶差分恒零，而 $h(i)=c_0/t_i$。因此倒数迹从 $j$ 和 $j+1$ 开始的两个四阶差分都必须为零。

置

$$
N(r)=6r^4+15r^3-18r^2-29r-8.
\tag{4.2}
$$

所需完整有理恒等式为

$$
1-\frac4r+\frac6{1+r}-\frac4{1+2r}+\frac1{2+3r}
=\frac{N(r)}{r(1+r)(1+2r)(2+3r)}.
\tag{4.3}
$$

为核定全部分子系数，将左边五项依次乘正分母，所得贡献分别为

$$
\begin{aligned}
&6r^4+13r^3+9r^2+2r,\\
&-24r^3-52r^2-36r-8,\\
&36r^3+42r^2+12r,\\
&-12r^3-20r^2-8r,\\
&2r^3+3r^2+r.
\end{aligned}
\tag{4.4}
$$

相加正好得到 (4.2)。第一个四阶差分为

$$
\frac{N(r)}{s\,r(1+r)(1+2r)(2+3r)}.
\tag{4.5}
$$

第二个同形，只须将 $s$ 替换为 $sr$，将 $r$ 替换为 $r'=1+1/r$。全部分母严格正，故必要条件是 $N(r)=N(r')=0$。

$N$ 恰有一个正零点 $\alpha$。确实，

$$
\frac{N(r)}{r^2}=6r^2+15r-18-\frac{29}r-\frac8{r^2}
\tag{4.6}
$$

在 $r>0$ 严格递增：每个非常数项均严格递增；其在零处和正无穷处的极限分别为负无穷与正无穷。连续性给出存在和唯一性。设 $\varphi=(1+\sqrt5)/2$，由 $\varphi^2=\varphi+1$ 得

$$
N(3/2)=-11<0,\qquad N(\varphi)=\varphi+1=\varphi^2>0,
\qquad \frac32<\alpha<\varphi.
\tag{4.7}
$$

若 $N(r)=0$，则 $r=\alpha$，而

$$
r'=1+\frac1\alpha>1+\frac1\varphi=\varphi>\alpha.
$$

由 (4.6) 的严格递增性，$N(r')>0$，与第二个零条件矛盾。故非零 $c_0$ 分支也不可能，最终 $h=0$，即满列秩。$j$ 及临时段内指标仅用于证明原时钟恒等式，不是轨迹重置。∎

## 5. 初始四个 M 的精确奇异层

**定理 5.1（行列式、唯一正迹例外与精确秩）。** 对原始前缀 $M^4$，令 $\tau=\operatorname{tr}(MP)>0$。则

$$
\det R_{M^4}(P)=12N(\tau).
\tag{5.1}
$$

当 $\tau\ne\alpha$ 时秩为四，当 $\tau=\alpha$ 时秩恰为三。唯一性指正迹参数 $\alpha$，不指唯一源矩阵。

**证明。** 五个原时钟的迹为

$$
(t_0,t_1,t_2,t_3,t_4)
=(1,\tau,1+\tau,1+2\tau,2+3\tau).
\tag{5.2}
$$

置 $f_i=1/t_i$。将 $R_{M^4}$ 第 $i$ 行提出 $t_i$，余下四列是 $(1-f_i,i,i^2,i^3)$，$i=1,2,3,4$。为求其行列式，考虑在节点 $0,1,2,3,4$ 上以 $1,T,T^2,T^3,f$ 为列的五阶取值矩阵，其中最后一列为 $f_i$。其余四行减去时钟零行，沿第一列展开后留下 $(i,i^2,i^3,f_i-1)$。将最后一列移至第一列发生三次换位，再将该列变号一次，故其行列式恰等于 $(1-f_i,i,i^2,i^3)$ 的行列式，符号为正。

上述五节点的 Vandermonde 乘积为 $288$，$f$ 的四次插值首项系数为 $\Delta^4f_0/24$，故该四阶行列式为 $12\Delta^4f_0$。乘回 $t_1t_2t_3t_4$，再代入 (4.3)，正好得到 $12N(\tau)$。这也固定了行列式的符号。

前三行在系数列 $1,2,3$ 上的子式为

$$
\tau(1+\tau)(1+2\tau)
\det\begin{pmatrix}1&1&1\\2&4&8\\3&9&27\end{pmatrix}
=12\tau(1+\tau)(1+2\tau)>0.
\tag{5.3}
$$

所以即使四阶行列式为零，秩仍至少为三。结合 (4.7) 的唯一正零点，便得全部正迹层上的精确秩。特别地，$12N(3/2)=-132$，与 IV 命题 13.4 的 $P_*=(\begin{smallmatrix}1/2&1/2\\1/2&1/2\end{smallmatrix})$ 例子一致。∎

**定理 5.2（合法非对称奇异源与实际碰撞）。** 该奇异层有合法非对称源；在其上有非零三次或更低次增益，使原始 $M^4$ 的五次读数全部为零。

**证明。** 定义

$$
\begin{aligned}
s_\alpha&=\alpha-\tfrac12>1,\\
b_\alpha&=\frac{s_\alpha+\sqrt{s_\alpha^2-1}}2,\qquad
c_\alpha=\frac{s_\alpha-\sqrt{s_\alpha^2-1}}2,\\
P_\alpha&=\begin{pmatrix}1/2&b_\alpha\\c_\alpha&1/2\end{pmatrix}.
\end{aligned}
\tag{5.4}
$$

平方根实且非零，又小于 $s_\alpha$，故 $b_\alpha,c_\alpha>0$ 且不相等。它们的乘积为 $1/4$，所以 $P_\alpha$ 迹一、行列式零、秩一、严格正且非对称。直接取迹得 $\operatorname{tr}(MP_\alpha)=b_\alpha+c_\alpha+1/2=\alpha$。

取完整多项式

$$
\begin{aligned}
H_\alpha(T)={}&-\frac{(T-1)(T-2)(T-3)}6
+\frac{T(T-2)(T-3)}{2\alpha}\\
&-\frac{T(T-1)(T-3)}{2(1+\alpha)}
+\frac{T(T-1)(T-2)}{6(1+2\alpha)}.
\end{aligned}
\tag{5.5}
$$

四项恰是节点 $0,1,2,3$ 对应倒数迹

$$
1,\quad\frac1\alpha,\quad\frac1{1+\alpha},\quad\frac1{1+2\alpha}
$$

的 Lagrange 插值项，因而 $H_\alpha(0)=1$，多项式非零且次数至多三。等式 $N(\alpha)=0$ 由 (4.3) 等价于五个倒数迹的四阶差分为零。前三次插值在节点四处满足同一差分关系，因此

$$
H_\alpha(4)=\frac1{2+3\alpha}.
\tag{5.6}
$$

所以两个不同的合法完整世界

$$
(P_\alpha,H_\alpha,-1),\qquad
(P_\alpha,2H_\alpha,-2)
\tag{5.7}
$$

在原时钟 $0,1,2,3,4$ 沿 $M^4$ 全部读零：每处都有 $t_iH_\alpha(i)=1$，包括初读。它们增益及漂移确实不同。

定理 5.1 使该层的路径核一维，而 $H_\alpha$ 的系数向量非零且属于核，故

$$
\ker R_{M^4}(P)=\mathbb R H_\alpha\quad(\tau=\alpha).
\tag{5.8}
$$

这里右边以多项式与其四维系数向量作自然识别。非奇异层的核为零。第五个 $M$ 由定理 4.1 消去此一维歧义。因此统一五步定理中的五不能在初始纯 $M$ 前缀上降为四。这是固定初始前缀的锐性：不声称先前混合历史或之后其他观测不能解除四个 $M$ 的歧义，(5.7) 也不是原根失败树。∎

**推论 5.3（同 $M$ 迹类的增益刚性）。** 任取合法全源元组和 $x\in\mathcal U$。若 $q,r\in\mathcal D_{M^5}$，并且

$$
\operatorname{tr}(MP_q)=\operatorname{tr}(MP_r)=\tau,
\tag{5.9}
$$

则 $x_q=x_r$，且 $\delta_q=\delta_r$，即使 $P_q\ne P_r$。在 $\mathcal D_{M^4}$ 上，$\tau\ne\alpha$ 时同样成立；$\tau=\alpha$ 时精确的可能差异为

$$
g_q-g_r=\lambda H_\alpha,\qquad
\delta_q-\delta_r=-\lambda\quad(\lambda\in\mathbb R).
\tag{5.10}
$$

**证明。** 迹一与 $M^2=M+I$ 使全部纯 $M$ 迹序列只取决于初值 $1,\tau$。两槽的源虽可不同，但在这些共同祖先上的迹完全相同。其共享读数相减，仍得到 (3.3)。原始 $M^5$ 用定理 4.1，原始 $M^4$ 用定理 5.1 和 (5.8)，再由 $H_\alpha(0)=1$ 得漂移差公式。该论证对任意其余源及每个联合核向量均成立。源不同的完整目标即使具有相同增益和漂移仍然不同；此刚性不取得未知源，也不把纯 $M$ 路径变成全目标解码器。∎

## 6. 三个 JJ 回返与混合词

**定理 6.1（允许交叠的三个回返）。** 若前缀 $v$ 含至少一个 $M$，且含至少三个起点不同的 $JJ$，则对每个合法源 $P$，$R_v(P)$ 秩为四。$JJ$ 出现次数按起始位置计，允许交叠。特别地，含连续四个 $J$ 的混合词满足此条件。

**证明。** 若 $JJ$ 位于动作 $i+1,i+2$，则 $J^2=I$ 给出 $A_{i+2}=A_i$ 和 $t_{i+2}=t_i>0$。(3.3) 因而给出 $h(i+2)=h(i)$。多项式

$$
Q_h(T)=h(T+2)-h(T)
\tag{6.1}
$$

次数至多二，三个不同出现起点给出三个不同零点，故 $Q_h$ 恒零。交叠只共享动作，不会合并不同起点的原时钟。若 $h$ 非常数，设其首项为 $a_dT^d$，其中 $d\ge1$，则 $Q_h$ 首项为 $2da_dT^{d-1}\ne0$。因此 $h$ 必为常数 $c_0$。

若 $c_0\ne0$，(3.3) 强迫全部前缀迹为一。下面排除这一点，并覆盖第一个 $M$ 的每种位置。写

$$
P=\begin{pmatrix}a&b\\c&d\end{pmatrix},\qquad
 d=1-a>0,\qquad\sigma=b+c.
$$

若第一个 $M$ 在时钟 $m>1$，之前全是 $J$。时钟一的迹为 $\sigma$，故全一条件给出 $\sigma=1$。若之前 $J$ 的数量为偶数，累计矩阵为 $I$，此 $M$ 的迹为

$$
\operatorname{tr}(MP)=\sigma+d=1+d>1.
$$

若之前数量为奇数，则累计矩阵为 $J$，此 $M$ 的迹为

$$
\operatorname{tr}(MJP)=1+b>1.
$$

若第一个动作就是 $M$，其迹须为一，而第二个动作若为 $M$，则 $\operatorname{tr}(M^2P)=1+\operatorname{tr}(MP)=2$；若为 $J$，则 $\operatorname{tr}(JMP)=1+c>1$。定理中的词至少有两个动作，故这些情形穷尽。全一迹均不可能，必有 $c_0=0$，于是 $h=0$。

每个回返使用的是单词内部连续实际执行的两个 $J$，不要求取得任何分叉动作的响应。∎

## 7. 任意起始原时钟的六步交替

**定理 7.1（六个交替动作的统一满秩）。** 若前缀 $v$ 含连续的 $MJMJMJ$ 或 $JMJMJM$，则对每个合法源 $P$，$R_v(P)$ 秩为四。交替段可位于任意允许的原时钟起点。

**证明。** 设交替段位于动作 $j+1,\ldots,j+6$，$h$ 满足 (3.3)。若 $c_0=0$，七个严格正迹使 $h$ 在 $j,\ldots,j+6$ 全部为零，故 $h=0$。现设 $c_0\ne0$。置

$$
C=A_jP,\qquad s=\operatorname{tr}C>0,\qquad
U=JM=\begin{pmatrix}1&1\\0&1\end{pmatrix},\quad
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix}.
\tag{7.1}
$$

$C$ 全部条目严格正。必须依原始时间先后计算左乘矩阵。若交替段以 $M$ 开始，偶数长度的左因子为 $U^k$，奇数长度为 $MU^k$，且

$$
U^k=\begin{pmatrix}1&k\\0&1\end{pmatrix},\qquad
MU^k=\begin{pmatrix}0&1\\1&k+1\end{pmatrix}.
\tag{7.2}
$$

对应的完整迹行是

$$
\begin{aligned}
t_{j+2k}&=s+kC_{21}&&(k=0,1,2,3),\\
t_{j+2k+1}&=C_{12}+C_{21}+(k+1)C_{22}&&(k=0,1,2).
\end{aligned}
\tag{7.3}
$$

若以 $J$ 开始，左因子为 $L^k$ 和 $JL^k$，且

$$
L^k=\begin{pmatrix}1&0\\k&1\end{pmatrix},\qquad
JL^k=\begin{pmatrix}k&1\\1&0\end{pmatrix}.
\tag{7.4}
$$

此时迹行是

$$
\begin{aligned}
t_{j+2k}&=s+kC_{12}&&(k=0,1,2,3),\\
t_{j+2k+1}&=C_{12}+C_{21}+kC_{11}&&(k=0,1,2).
\end{aligned}
\tag{7.5}
$$

两种情况下，四个偶数位置迹均为 $s+kr$，其中 $r>0$；三个奇数位置迹构成等差数列。

令

$$
\kappa=\frac{r}{2s}>0,\qquad
H(n)=\frac{s}{c_0}h(j+n).
\tag{7.6}
$$

这是次数至多三的多项式。在整数 $n=0,\ldots,6$ 处，由 (3.3) 得 $H(n)=s/t_{j+n}>0$；尤其在 $n=0,2,4,6$ 处，$H(n)=1/(1+\kappa n)$。定义

$$
Q(n)=n(n-2)(n-4)(n-6),\qquad D=Q(-1/\kappa)>0.
\tag{7.7}
$$

$D$ 的四个因子都负，所以严格正。多项式 $(1+\kappa n)H(n)-1$ 次数至多四，且在四个偶数节点为零，故为 $Q$ 的一个常数倍。在 $n=-1/\kappa$ 代入，其值为 $-1$，确定该倍数为 $-1/D$。因此有精确的多项式恒等式

$$
(1+\kappa n)H(n)=1-\frac{Q(n)}D.
\tag{7.8}
$$

把右边再除以 $1+\kappa n$ 的表观极点是可去的，因为 (7.8) 已是多项式恒等式。负实参数处的代入仅为代数证明步骤，不是取得负时钟的读数。

各所需节点的全部 $Q$ 值为

$$
Q(0)=Q(2)=Q(4)=Q(6)=0,\qquad
Q(1)=-15,\quad Q(3)=9,\quad Q(5)=-15.
\tag{7.9}
$$

故

$$
\begin{aligned}
H(1)&=\frac{D+15}{D(1+\kappa)},\\
H(3)&=\frac{D-9}{D(1+3\kappa)},\\
H(5)&=\frac{D+15}{D(1+5\kappa)}.
\end{aligned}
\tag{7.10}
$$

在倒取 $D-9$ 之前，$H(3)>0$ 与分母严格正已经强迫 $D>9$；$D=9$ 或 $D<9$ 均直接违背该正值条件。于是合法倒取三个正数，得到精确严格二阶差分

$$
\begin{aligned}
\frac1{H(1)}-\frac2{H(3)}+\frac1{H(5)}
&=2D(1+3\kappa)\left(\frac1{D+15}-\frac1{D-9}\right)\\
&=-\frac{48D(1+3\kappa)}{(D+15)(D-9)}<0.
\end{aligned}
\tag{7.11}
$$

另一方面，$1/H(n)=t_{j+n}/s$，三个奇数位置迹由 (7.3) 或 (7.5) 构成等差数列，同一个二阶差分必须为零，矛盾。故 $h=0$。

全过程只用次数至多三及乘积次数至多四，没有假定任何首项系数非零；低次、多项式次数下降的情况同样受 (7.8) 及矛盾约束。$n$ 只是描述原时钟 $j,\ldots,j+6$ 的代数变量，没有改变采集时钟。∎

## 8. 整个源元组上的统一守卫失败

**定义 8.1（已排除同源叶的词族）。** 定义七动作词集合

$$
\begin{aligned}
\mathcal W_{\mathrm{bad}}=\{w\in\{J,M\}^7:\ &
w\text{ 含 }MMMMM,\\
&\text{或含 }M\text{ 且至少有三个起点不同的 }JJ,\\
&\text{或含 }MJMJMJ\text{ 或 }JMJMJM\}.
\end{aligned}
\tag{8.1}
$$

这里第二个条件允许交叠；该定义与以下证明均无需枚举词表。

**定理 8.2（任意其余源、每个秩层上的完整差映射消失）。** 对任意合法 $256$ 源元组，只要存在 $w\in\mathcal W_{\mathrm{bad}}$ 使

$$
P_{(w,0)}=P_{(w,1)},
$$

就有

$$
D_w|_{\mathcal U}=0,\qquad
\operatorname{rank}[B;D_w]=\operatorname{rank}B,
\qquad\Phi(\mathbf P)\text{ 不成立}.
\tag{8.2}
$$

另外，对任何满足上述模式之一的前缀 $v$，其下任意两个同源槽 $q,r\in\mathcal D_v$ 都满足：对每个 $x\in\mathcal U$，$x_q=x_r$。

**证明。** 固定任意合法元组，并任取该元组的一个 $x\in\mathcal U$。同源两槽的差多项式由引理 3.3 满足全部共同祖先方程。依 $w$ 或 $v$ 所含模式，定理 4.1、6.1、7.1 中相应结果给出该差多项式为零，故全部四个系数相等。由于 $x$ 在整个 $\mathcal U$ 上任意，得到整个四分量映射 $D_w|_{\mathcal U}$ 恒零，而非某个采样、某个系数或某个选定向量上为零。用 (2.13) 即得秩增量零，包括 $B$ 的任意秩下降层和零核层。

该叶源相同，使 (2.10) 的源不同备选也为假，所以这一必需守卫失败，无论所有其他增益和叶守卫是否成立。其余 $254$ 个源从未受限制，可以各自在全合法域中任取。同一证明用于任何所述前缀下的同源两槽，得到最后的断言。∎

例如 $w=M^7$ 时，任意共同合法源放在这两个槽、任意另外 $254$ 个合法源放在其余槽，均被排除。这严格扩展 IV 命题 13.4 的全部槽同取 $P_*$ 的单个例子，并未附加共同增益或共同漂移承诺。必要条件是

$$
\mathbf P\in\mathfrak S_7\ \Longrightarrow\
P_{(w,0)}\ne P_{(w,1)}\quad
(w\in\mathcal W_{\mathrm{bad}}).
\tag{8.3}
$$

此条件没有约束不同叶之间的源重复。若同一叶的两个源不同，则完整目标已经不同，该叶无需 $D_w$ 守卫；不能将 (8.2) 用来额外要求一个系数差。定理也不判定这些不同源槽的增益守卫。

## 9. J 七次叶的精确同源分类

**定理 9.1（条件秩增量恰为一或零）。** 固定任意合法全源元组，设 $w_J=J^7$ 的两源相同，均为

$$
P=\begin{pmatrix}a&b\\c&1-a\end{pmatrix},\qquad
\sigma=\operatorname{tr}(JP)=b+c.
\tag{9.1}
$$

独立于其余 $254$ 个源，有以下精确结论。

若 $\sigma\ne1$，则

$$
\operatorname{rank}[B;D_{w_J}]=\operatorname{rank}B,
\tag{9.2}
$$

同源分离守卫失败，元组不属于 $\mathfrak S_7$。

若 $\sigma=1$，则

$$
\operatorname{rank}[B;D_{w_J}]=\operatorname{rank}B+1,
\qquad
\operatorname{rank}[B;G_{(w_J,e)}]>\operatorname{rank}B
\quad(e=0,1).
\tag{9.3}
$$

即该叶分离守卫和两个槽各自的增益守卫自动成立。此断言不判定任何剩余守卫。

**证明。** 沿 $J^7$，偶数时钟迹为一，奇数时钟迹为 $\sigma$。其 $JJ$ 回返至少有三个不同起点，故定理 6.1 证明中的周期多项式论证使任何路径核多项式 $h$ 成为常数；这里没有 $M$，不使用该定理的混合词全一迹排除。剩余方程仅为

$$
(\sigma-1)h(0)=0.
\tag{9.4}
$$

所以 $\sigma\ne1$ 时路径核为零、响应矩阵秩四；$\sigma=1$ 时路径核精确为常数多项式的直线

$$
\ker R_{J^7}(P)=\mathbb R e_0,
\qquad e_0=(1,0,0,0)^{\mathsf T}.
\tag{9.5}
$$

后一情形首列为零，系数列 $1,2,3$ 在时钟 $1,2,3$ 的子式为 $12\ne0$，故秩恰为三。

当 $\sigma\ne1$ 时，对每个 $x\in\mathcal U$ 用引理 3.3 得 $D_{w_J}x=0$，再用 (2.13) 得 (9.2)。

当 $\sigma=1$ 时，局部路径论证给出上界

$$
D_{w_J}(\mathcal U)\subseteq\mathbb R e_0.
\tag{9.6}
$$

还须证明该直线在完整核中确实可达，且两个增益守卫都成立。分别对 $q=(w_J,0)$ 和 $q=(w_J,1)$ 定义局部化向量 $u^{(q)}$：仅槽 $q$ 的系数块为 $e_0$，其余全部槽块为零。若 $B$ 的某行前缀不含槽 $q$，该行作用自然为零；若其前缀包含槽 $q$，此前缀必为某个 $J^i$，且

$$
\ell_{J^i}(P)e_0=t_i(P)-1=0.
\tag{9.7}
$$

因此无论 $q$ 是该行比较的非参考槽，还是整批比较共用的参考槽，其正项或负项均为零。特别是 $q$ 为参考槽时，所有使用该参考槽的行同时被消去。故两个局部化向量都属于同一个完整核 $\mathcal U$，不依赖任一其他源。

现在

$$
\begin{aligned}
G_{(w_J,0)}u^{((w_J,0))}&=e_0,\\
G_{(w_J,1)}u^{((w_J,1))}&=e_0,\\
D_{w_J}u^{((w_J,0))}&=e_0,\qquad
D_{w_J}u^{((w_J,1))}=-e_0.
\end{aligned}
\tag{9.8}
$$

两个增益限制分别非零；结合 (9.6)，$D_{w_J}|_{\mathcal U}$ 的秩精确为一。由 (2.13) 得 (9.3) 的全部结论。此处证明的是完整核上的准确秩增量，未用独立路径拟合替代联合核。∎

**定理 9.2（两族完整合法几何与实际常增益碰撞）。** 在合法源域内，$\sigma=1$ 的源恰为

$$
P^{\mathrm R}(a)=\begin{pmatrix}a&a\\1-a&1-a\end{pmatrix}
\quad\text{或}\quad
P^{\mathrm L}(a)=\begin{pmatrix}a&1-a\\a&1-a\end{pmatrix},
\qquad0<a<1.
\tag{9.9}
$$

第一族满足 $P^{\mathrm R}J=P^{\mathrm R}$，第二族满足 $JP^{\mathrm L}=P^{\mathrm L}$；两族仅在 $a=1/2$ 的 $P_*$ 相交。每个这样的源都有不同合法完整世界在 $J^7$ 上全部八读相同。

**证明。** $b+c=1$ 与秩一条件 $bc=a(1-a)$ 表明 $b,c$ 是

$$
z^2-z+a(1-a)=(z-a)(z-(1-a))
\tag{9.10}
$$

的两根，故 $\{b,c\}=\{a,1-a\}$，恰得 (9.9)。反之两个显示矩阵逐项正、迹一、行列式零且秩一，并有 $b+c=1$。第一族两列相同，右乘 $J$ 不变；第二族两行相同，左乘 $J$ 不变。两族相等必须对角参数相同并有 $a=1-a$，故交点只有 $a=1/2$，此处并无额外秩例外。

因 $J$ 偶次为 $I$、奇次为 $J$，这些源沿 $J^7$ 的全部迹都为一。于是

$$
(P,1,-1),\qquad(P,2,-2)
\tag{9.11}
$$

是两个不同的合法完整目标，其增益为非零常数，在原时钟 $0,\ldots,7$ 全部读零。

(9.11) 是一条固定词的实际碰撞。定理 9.1 中 $u^{(q)}$ 的其他零块只用于证明单个限制映射非零，它们并非每槽增益都非零的 $256$ 世界实现；两者均不构成原根失败证书。必须对同一源元组证明全部剩余守卫，之后才能用 (2.14) 取得一个同时合法向量。∎

## 10. 必要条件、适用边界与完整缺口

**推论 10.1（每个原根见证必须满足的结构）。** $\mathfrak S_7$ 中任意元组必须满足 (8.3)。若其 $J^7$ 叶源相同，则共同源必须属于 (9.9) 两族；在该条件下，可以从此同一元组的剩余待验清单中移去这两个 $G$ 守卫和该叶 $D$ 守卫，因为定理 9.1 已将它们证明为真。其联合核还必须满足推论 5.3 的初始 $M^5$ 同迹刚性，以及初始 $M^4$ 的唯一 $H_\alpha$ 例外线。

**证明。** 第一项为定理 8.2 的逆否表述；第二项为定理 9.1 的完整二分和定理 9.2 的合法几何；最后一项就是推论 5.3。这些都是对同一个源元组及同一个联合核的结论，没有更换分支或系数向量。∎

这些条件是必要条件，尚非 $\Phi$ 的充分条件。具体地，词 $MMJMMJM$ 没有五连 $M$、没有 $JJ$，也没有六步交替子词，本卷未评价它的同源守卫。更根本地，每叶都取不同源的合法元组绕过全部新同源叶排除，而其 $256$ 个增益守卫仍未被联合判定。其他未落在上述模式中的混合词同样需要新的分析。

不等源的共享读数耦合具有形式

$$
t_i(P)g(i)-g(0)=t_i(Q)g'(i)-g'(0).
\tag{10.1}
$$

当两条迹序列不同，它不能直接化为 (3.3) 的一个正迹序列乘一个差多项式。因此本卷的倒数递推、周期及插值矛盾不评价所有剩余增益限制，也没有将所有分支接成一个共同合法向量。分别给各叶拟合响应或给各守卫找向量，均不能替代 (2.12) 与 (2.14) 的同一联合实现。

完整任务仍须给出以下两种成果之一：一个合法 $256$ 源元组满足全部 $G$ 和适用的完整 $D$ 守卫，从而重建同一个全系数向量、全部共享响应和固定世界的失败树；或者证明每个合法源元组至少失败一个必需守卫，从而得到 $\mathfrak S_7$ 为空。这里两者均未获得，也未给出全域八读解码器、九读上界、取得未知源或未知源类标签的方法。

上述所有定理只在严格逐项正域中陈述。任意小的正条目、非对称及无额外有界性限制的源仍被覆盖；零条目的非负边界未由此证明。正迹使倒数合法，交替段的严格正斜率又给出 $\kappa>0$，不能静默将严格正性改为非负性。

所有除法都在其条件得到后进行：$c_0$ 首先分零与非零，五 $M$ 的 $s,r,1+r,1+2r,2+3r$ 及移位版本均正；$N(r)=0$ 的正奇异层被保留并精确处理。四 $M$ 的平方根及插值分母由 $\alpha>3/2$ 保证合法。交替证明先有 $D>0$，再由中间正值推出 $D>9$，才倒取 $D-9$；负节点的表观极点由多项式恒等式消去。$J^7$ 直接处理 $\sigma=1$，没有除以 $\sigma-1$。

没有除掉任何单独世界的增益采样值，也没有给它预设符号或根。$h(i)/c_0>0$ 是非零差常数分支中由正迹推得的事实，不是对两个世界各自增益的符号承诺。次数始终为至多界，常数、一次、二次、三次及所有首项消失情况均包含在证明内。

固定源满秩是对指定源之后的条件可识别性。它约束固定世界是否能共享已经规定的实际前缀，不等于从未知源读数中取得该源。初始平移仍保留任意漂移和原时钟；没有引入共同第五响应、指定数值祖先、共同增益、共同漂移或指定根的承诺。局部锐性碰撞和纯 $J$ 碰撞也没有被提升为全原根失败。

## 11. 数学来源、对应与新意范围

本卷相对于复用的 IV 给出专用的正迹满秩定理、精确四 $M$ 奇异层及合法碰撞、同 $M$ 迹类的系数刚性、整族联合源守卫失败，以及 $J^7$ 同源叶在完整核上的精确分类。有限维线性代数、秩与零化度、Lagrange 插值、有限差分、Vandermonde 行列式、有限子空间回避和多项式零点论证均为标准工具。IV 的源投影及其可行域定义作为既有结果直接复用，不将其重新表述计为新增一般定理。

| 永久数学来源 | 本卷使用的确切对应与条件 |
| --- | --- |
| [IV 定义 1.1–1.2、定理 9.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md) | 完整目标、两个原子动作、原时钟、立即读数、失败递归、实际子纤维与提前停止；初读零到任意初读的双向平移。没有引入其局部三目标分析的共同第五响应假设。 |
| [IV 定义 9.1、13.1–13.2，式 (13.1)–(13.10)](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md) | 全部合法源、$256$ 槽、$254$ 前缀、$1538\times1024$ 的一个 $B$、$768$ 环境坐标及 $256$ 秩一方程；初读零系数与漂移接口，参考槽消元，逐槽增益和完整四分量同源差。 |
| [IV 定理 13.3，式 (13.12)–(13.21)](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md) | 每个秩层的源秩守卫等价、一个共同核、全部守卫成立后的一个同时合法向量、固定世界及共享祖先重建。本卷证明特定限制映射恒零，或在条件纯 $J$ 叶精确秩一；不以独立叶拟合替代该接口。 |
| [IV 命题 13.4，式 (13.23)–(13.25)](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md) | 其 $P_*$ 的 $M$ 迹为 $3/2$，本卷一般行列式给出同一个 $-132$。五连 $M$ 结论覆盖任意合法共同源及任意其余槽，且四 $M$ 的正奇异迹被显式保留。 |
| [IV 第 11、12、14 节](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md) | 保留局部条件系统与完整原根系统的区别，复用 $\mathfrak S_7$ 的原始完成判据。源已供应的条件恢复不承担未知源采集，已有文献对应不承担本卷的原根可行性结论。 |

本卷没有进行外部文献检索，新增性只按上述给定来源的对应范围陈述，不作全球首创或文献穷尽声明。这里的结论为符号数学推导，未以数值实验、枚举、通用神经网络、形式证明助手或 Lean kernel 核验作为证据，亦不附带稳定性或资源保证。完整原根八读存在与至少九读必要的二选一仍未判定。

## 追加锚（本行以下为增补区）

## 12. 三个初始 J 的全部混合七字词与五个新增同源排除

**定义 12.1（原单槽路径映射与两个词族）。** Retain the legal source domain, original clocks and complete $B,G,D$ of Definitions 2.1–2.2. For a seven-action chronological word $w$, write

$$
T_w(P):\mathbb R^4\longrightarrow\mathbb R^7,\qquad
(T_w(P)x)_i=\ell_{w_{\le i}}(P)x\quad(1\le i\le7).
\tag{12.1}
$$


This is exactly $R_w(P)$ of Definition 3.2. Put

$$
\begin{aligned}
\mathcal W_{JJJ}&=\{JJJz:z\in\{J,M\}^4,\ z\ne JJJJ\},\\
\mathcal W_{\mathrm{new}}&=\{JJJMJMJ,JJJMJMM,JJJMMJM,JJJMMMJ,JJJMMMM\},\\
\mathcal W_{\mathrm{old}}&=
\{J^4z:z\in\{J,M\}^3,\ z\ne JJJ\}
\cup\{JJJMJJJ,JJJMJJM,JJJMMJJ\}.
\end{aligned}
\tag{12.2}
$$


**定理 12.2（三个初始 J 的混合七字词逐源单射）。** For every legal $P$ and every $w\in\mathcal W_{JJJ}$,

$$
\ker T_w(P)=\{0\},\qquad\operatorname{rank}T_w(P)=4.
\tag{12.3}
$$


The family has fifteen words: the ten in $\mathcal W_{\mathrm{old}}$ are supplied directly by Theorem 6.1; the five new instances are exactly $\mathcal W_{\mathrm{new}}$. No unit-signature, source symmetry, bounded-entry, gain-sign or exact-degree premise is imposed.

Proof. Splitting the suffix after the initial $JJJ$ gives the disjoint union of the two sets in (12.2). Every old word contains an $M$ and at least three occurrences of $JJ$ counted by distinct starting positions, including overlaps. The first seven old words have four initial $J$'s; each of the other three has an additional $JJ$ after its first $M$. Apply Theorem 6.1 directly to these ten instances.

It remains to prove the five instances whose first $M$ is at clock four. Write

$$
P=\begin{pmatrix}a&b\\c&1-a\end{pmatrix},\qquad
s=b+c>0,\qquad bc=a(1-a),\qquad0<a<1,
\tag{12.4}
$$


and $t_i=\operatorname{tr}(A_{w_{\le i}}P)>0$ by the positive-trace result 3.1. Let a polynomial $g$ of degree at most three represent a vector in $\ker T_w(P)$. Its equations are

$$
t_i g(i)=g(0)\quad(1\le i\le7).
\tag{12.5}
$$


If $g(0)=0$, the seven distinct roots force $g=0$. For a nonzero local kernel element one may therefore divide by its nonzero $g(0)$ within this proof, obtaining

$$
g(0)=1,\qquad g(i)=t_i^{-1}>0\quad(1\le i\le7).
\tag{12.6}
$$


This normalization only tests a linear kernel element and adds no original-world sign or initial-value promise. The first three actual $J$ actions give the four interpolation values $g(0)=1,g(1)=s^{-1},g(2)=1,g(3)=s^{-1}$. Their unique polynomial of degree at most three is

$$
g(z)=1+(s^{-1}-1)\frac{z(2z-5)(z-2)}3.
\tag{12.7}
$$


Indeed the displayed cubic has those four values, so uniqueness follows from four distinct roots of the difference. Its seventh value is $(105-104s)/s$, which is positive by (12.6). Hence $s<105/104$. Its fourth value is $(8-7s)/s$. At clock four the cumulative matrix is $MJ$, whose trace is $1+b$, so

$$
1+b=\frac{s}{8-7s},\qquad
b=\frac{8(s-1)}{8-7s}.
\tag{12.8}
$$


Here $8-7s>0$ from $s<105/104$. Since $b>0$, setting $e=s-1$ gives

$$
0<e<\frac1{104},\qquad
b=\frac{8e}{1-7e},\qquad
g(5)=\frac{25-24s}{s}=\frac{1-24e}{1+e}>0.
\tag{12.9}
$$


All denominators used here are strictly positive; no unknown gain sample is discarded.

If the fifth action is $J$, the cumulative matrix is $JMJ$ and its trace is $a+s$. The fifth equation then forces

$$
a+s=\frac{s}{25-24s},\qquad
a=\frac{24(1+e)e}{1-24e}.
\tag{12.10}
$$


Using $0<e<1/104$ gives the strict rational bounds

$$
\begin{aligned}
b&<\frac{832}{97}e,&c&<s<\frac{105}{104},
&bc&<\frac{840}{97}e,\\
24e&<a<\frac{63}{208},&&
&a(1-a)&>24e\frac{145}{208}=\frac{435}{26}e.
\end{aligned}
\tag{12.11}
$$


For the upper bound on $a$, bound the positive factors $1+e$, $e$, and $(1-24e)^{-1}$ by their values at $1/104$; their product is $63/208$. The lower bound is immediate from $(1+e)/(1-24e)>1$. The $b$ bound uses $1-7e>97/104$, and the bound on $bc$ follows by multiplying the positive upper bounds for $b,c$. Since $840/97<435/26$, (12.11) contradicts $bc=a(1-a)$. This treats both new words with fifth action $J$.

If the fifth action is $M$, its cumulative matrix is $M^2J$ and its trace is $1+b+s$. Substitution of (12.8) and $g(5)=(25-24s)/s$ into its equation gives

$$
217-384s+168s^2=0.
\tag{12.12}
$$


More explicitly, $1+b=s/(8-7s)$, so the equation is
$(9-7s)(25-24s)=8-7s$, which expands to (12.12). But at $s=1+e$ its left-hand side is

$$
1-48e+168e^2>1-\frac{48}{104}=\frac7{13}>0.
\tag{12.13}
$$


This contradiction treats the other three new words. Both fifth actions are exhausted, so no nonzero local kernel element exists. The argument uses clocks zero through seven on each actual word, not responses from its unselected sibling actions. ∎

**定理 12.3（五个新词在同一完整核上的同源守卫失败）。** Fix any complete legal $256$-source tuple and its original whole $V=\ker B=\mathcal U$, with all $254$ prefixes and the full $1538\times1024$ matrix. If for any $w\in\mathcal W_{\mathrm{new}}$ its two slot sources are equal, then

$$
D_w|_V=0,\qquad
\operatorname{rank}[B;D_w]=\operatorname{rank}B.
\tag{12.14}
$$


Consequently that original same-source separation guard fails. Any tuple satisfying every original guard must have unequal sources at each of these five leaves; together with the ten supplied instances the same necessity holds on all of $\mathcal W_{JJJ}$.

Proof. For any $x\in V$, the full matrix equations make the two slots realize the same response at every ancestor of their leaf. When their fixed sources agree at $P$, subtracting those equations says that the complete four-component coefficient difference is in $\ker T_w(P)$. By Theorem 12.2 this difference is zero, including its constant coefficient and thus its normalized drift difference. Since $x$ is arbitrary in the original $V$, this proves $D_w|_V=0$. A linear map vanishing on $\ker B$ has all rows in the row space of $B$, giving the rank equality. Equal sources also make the source-inequality alternative false, so Definition 2.2's applicable full guard fails. For the ten old instances use Theorem 6.1 and the existing Theorem 8.2 directly. The other $254$ sources are unrestricted in every such comparison; no separate branch witness or restricted kernel was substituted for $V$. ∎

Section 12 is a repository-derived synthesis from this volume's Definitions 2.1–2.2 and 3.2, positive-trace result 3.1, Theorem 6.1, and the same-source interface used in Theorem 8.2. The full original consumer agrees with [IV, Definitions 13.1–13.2 and Theorem 13.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md). The mathematical source version is `1eef3601bb81023352394a59bcb682b0c9b57cd8`; no external priority or exhaustive literature claim is made. The fifteen-word statement retains ten supplied cases and adds exactly the five instances named in (12.2), through the explicit model-specific interpolation and positivity contradictions above. No separate generic readout-space or finite-subspace theorem is introduced.

These exclusions give no nonvanishing gain guard for any slot, and no acquisition of an unknown source. They do not prove a common full-tree response space has a nonzero projection onto the affected slots, produce a simultaneous legal coefficient vector, or decide the complete original-root problem. Unequal leaf sources may distinguish complete targets even when gain coefficients agree; different leaves may repeat sources. Arbitrary real constant drift, nonzero gains of any degree at most three and either sign, degree drops, sampled or repeated roots, all original clocks, both actions and early stops remain in the original domain.

## 追加锚（本行以下为增补区）

## 13. Fifth-M fibers in the original absolute-response model

**定义 13.1（Carrier, history and actual fiber）。** Let $V$ be any finite-dimensional real vector space and let $X,D\in V^*$ be independent. Fix $e>-4$, and set

$$
\begin{aligned}
A&=(1-e)X+\frac{23}{16}D,& d&=\frac{5e-2}{10},\\
p(s)&=X\left[\frac{s^3-9s^2+23s}{15}
 -\frac{e s(s-5)(s-7)}{24}\right]
 +D\frac{s^3-18s^2+107s}{96}.
\end{aligned}
\tag{13.1}
$$

The initial response is zero, and the first three chronological actions are $JJJ$, with common responses

$$
A-\frac D2,\qquad \frac{24-25e}{20}X+\frac{25}{16}D,
\qquad A+\frac D2.
\tag{13.2}
$$

Their span has rank two. Indeed their difference contains $D$; if $e\ne1$, the first contains $X$ modulo $D$, and if $e=1$, the middle has $X$ coefficient $-1/20$.

The next two chronological actions are $MM$. Fix their absolute response forms by

$$
Y_4-A=uX+\frac v{16}D,\\qquad
Y_{5M}-A=wX+\frac z{16}D.
\tag{13.3}
$$

Thus the fixed parent is the five-tuple $(e,u,v,w,z)$; $v,z$ use the displayed factor-sixteen convention. A fiber consists of fixed legal sources $P$ of Definition 1.1 and linear maps $g\in V^*[s]$, $\deg g\le3$, with one constant drift $\delta\in V^*$, realizing these five responses as identities on $V$. Evaluation at a carrier vector gives the original scalar model. In particular every vector with $(X,D)\ne(0,0)$ gives a nonzero entire gain, since a zero gain and zero initial response would make all three responses (13.2) zero. No sign, exact-degree, nonzero-sample or simple-root condition is added.

Write the fixed source as

$$
P=\begin{pmatrix}a&b\\c&1-a\end{pmatrix},\qquad
 t=b+c,\quad R=1+b,\quad x=R/t.
\tag{13.4}
$$

The traces at clocks zero through five are exactly $(1,t,1,t,R,R+t)$: $J^3=J$, $MJ=\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)$ and $M^2J=\left(\begin{smallmatrix}1&1\\2&1\end{smallmatrix}\right)$. A signature $(R,t)$ is legal precisely when

$$
t>0,\quad R>1,\quad t-R+1>0,\quad
0<q:=(R-1)(t-R+1)\le\frac14.
\tag{13.5}
$$

Its complete source inverse is

$$
b=R-1,\\qquad c=t-R+1,\\qquad
 a=a_\pm=\frac{1\pm\sqrt{1-4q}}2.
\tag{13.6}
$$

Both roots are retained, and coincide exactly at $q=1/4$. These are actual positive rank-one matrices, rather than unrestricted lifted matrices. The distinction between realizable factors and an unrestricted lifted nullspace is also required in [Choudhary--Mitra, Proposition 1 and Remark 5, version 2](https://arxiv.org/html/1402.2637v2); that general criterion does not supply the fiber classification below.

**定理 13.2（Entire interpolation and exact affine charts）。** Define

$$
L(s)=\frac{s(s-2)(2s-5)}3,\qquad
W(s)=\frac{s(s-2)(s-4)}6,\qquad \eta=1-\frac1t.
$$

All gains and drifts with the initial and first-three responses above, for a fixed source, are exactly

$$
g(s)=Q-A+p(s)+\eta[-Q L(s)+D W(s)],
\qquad \delta=A-Q,
\qquad Q\in V^*.
\tag{13.7}
$$

Put

$$
C=(8-7t)R-t,\\qquad B_5=(25-24t)R+24t(1-t).
\tag{13.8}
$$

The two remaining absolute equations are exactly the form equalities

$$
\begin{aligned}
C Q&=t\left[(u-dR)X+\frac{v-11R}{16}D\right],\\
B_5 Q&=t[w-e(R+t)]X+
 \frac{tz-(52t-40)(R+t)}{16}D.
\end{aligned}
\tag{13.9}
$$

Away from $C=B_5=0$, define

$$
\begin{aligned}
F&=C[w-e(R+t)]-B_5(u-dR),\\
G&=C[tz-(52t-40)(R+t)]-tB_5(v-11R).
\end{aligned}
\tag{13.10}
$$

Then $F=G=0$ is necessary and sufficient for (13.9). There $Q=mX+(N/16)D$ is unique, with the two charts

$$
\begin{array}{c|cc}
 &m&N\\ \hline
 C\ne0&t(u-dR)/C&t(v-11R)/C\\
 B_5\ne0&t[w-e(R+t)]/B_5&[tz-(52t-40)(R+t)]/B_5.
\end{array}
\tag{13.11}
$$

Proof. The four values at clocks $0,1,2,3$ uniquely interpolate a polynomial of degree at most three. Substitution into (13.7) gives respectively $g(0)=Q-A$, $tg(1)=Q-D/2$, $g(2)=Q-A+p(2)$ and $tg(3)=Q+D/2$, proving both directions. At the next two clocks it gives

$$
\begin{aligned}
g(4)&=(8/t-7)Q+dX+11D/16,\\
g(5)&=(25/t-24)Q+eX+(13/4-5/(2t))D.
\end{aligned}
\tag{13.12}
$$

Multiplying these by the actual traces $R,R+t$, and adding the same $A-Q$, proves (13.9). Independence of $X,D$ gives (13.10) and (13.11). If just one of $C,B_5$ is zero, the other equation fixes $Q$ and the eliminants force the zero-chart right-hand side to vanish. Thus no zero-chart constraint is lost. Only $t>0$ and a stated nonzero chart coefficient have been divided by. In particular no gain sample, leading gain coefficient or carrier-vector coordinate has been divided by. ∎

## 14. The twelve fixed-parent moving-source normal forms

**定义 14.1（Algebraic constants and factors）。** Put

$$
\begin{gathered}
Z(h)=100h^2-421h+320,\qquad
 h_\pm=\frac{421\pm\sqrt{49241}}{200},\qquad h'=\frac{421}{100}-h,\\
e_h=\frac{8h-14}{13}=\frac{48h-50}{50h-45}
 =\frac{71\pm\sqrt{49241}}{325},\qquad
 a_e=\frac{24-25e_h}{5},\qquad r=\sqrt{\frac{24}{17}},\quad k\in\{r,-r\},\\
\alpha(s,k)=k(8/7-s)-1/7,\qquad
\beta(s,k)=1-s+k(25/24-s),\\
L_A(s,k)=x(t-s)-\alpha(s,k),\qquad
L_B(s,k)=(x+1)(t-s)-\beta(s,k).
\end{gathered}
\tag{14.1}
$$

In $e_h$, the signs of $h$ and $e_h$ are paired. Both $e_h$ exceed $-4$. The symbol $k$ is a root of $17k^2=24$, unrelated to a supplier's $\kappa$. In every row below $e=e_h$, $d=(5e_h-2)/10$, and $R=xt$.

**定理 14.2（Exhaustive moving-source parents）。** A fixed parent has a positive-dimensional set of actual positive source signatures if and only if it is one of the following twelve distinct tuples. Its entire actual signature fiber is the stated curve restricted by (13.5) and the critical deletions specified below; there are no additional isolated actual signatures at these parents.

| Family | Parent coefficients | Signature curve |
| --- | --- | --- |
| $V(h)$, two parents | $u=w=dh/(8-7h)$, $v=z=11h/(8-7h)$ | $t=h$ |
| $A(h,k)$, four parents | With $\alpha=\alpha(h,k)$, $\gamma=\beta(0,-k)$, $\beta'=\beta(h',-k)$: $u=-(e_h+a_e\alpha)/24$, $v=-(25\alpha+13)/6$, $w=e_h-a_e\alpha(\gamma-1)$, $z=(100\beta'-11)/7$ | $t=h+\alpha/x$ |
| $B(h,k)$, four parents | With $\beta=\beta(h,k)$, $\gamma=\alpha(0,-k)$, $\alpha'=\alpha(h',-k)$: $u=-(e_h+a_e\gamma)/24$, $v=-(25\alpha'+13)/6$, $w=e_h-a_e\gamma(h+\beta-1)$, $z=(100\beta-11)/7$ | $t=h+\beta/(x+1)$ |
| $H(h)$, two parents | $\alpha=(25-24h)/17$, $\beta=(7h-8)/17$, $u=w=0$, $v=z=(100h-141)/17$ | $t=h+\alpha/x+\beta/(x+1)$ |

The labels $A$ and $B$ also describe, respectively, the rational graphs $R=\alpha t/(t-h)$ and $R=-t+\beta t/(t-h)$. In $H$, $\alpha+\beta=1-h$ and the original-coordinate equation is

$$
H_h(R,t)=(t-h)R^2+t(t-1)R-\alpha t^2=0.
\tag{14.2}
$$

It has total degree three in $(R,t)$. The coefficient of $(t-h)$ multiplies $R^2$.

For $A(h,r)$, $B(h,r)$ and both $H(h)$, delete $x=r$. There is no positive critical deletion in the other six rows. All remaining signatures reconstruct uniquely by (13.6), (13.7) and (13.11). The two $V$ histories have

$$
Q=-\frac h{8-7h}(dX+11D/16),\qquad g(4)=g(5)=0.
\tag{14.3}
$$

They are the fixed-$t$ root-$(4,5)$ histories; no additional guard obstruction is asserted here for them.

## 15. Algebraic exhaustiveness, including all degree drops

**引理 15.1（Rational graph and denominator exhaustion）。** Under $R=tx$, let $\widehat F=F/t$ and $\widehat G=G/t^2$, using only $t>0$. For arbitrary parent coefficients, with $\ell=25e-24$, they are

$$
\begin{aligned}
\widehat F={}&-\frac\ell5x(x+1)t^2
 +\left[(9e/2-5)x^2+(5e+24u-7w-24/5)x+e+24u\right]t\\
 &+(8w-25u)x-24u-w,\\
\widehat G={}&100x(x+1)t^2
 +\left[-421x^2+(24v-7z-380)x+24v+52\right]t\\
 &+320x^2+(-25v+8z+280)x-24v-z-40.
\end{aligned}
\tag{15.1}
$$

Every common curve with nonconstant $x$ is a rational graph

$$
t=h+\frac\alpha x+\frac\beta{x+1},
\qquad Z(h)=0,\\qquad e=e_h.
\tag{15.2}
$$

There is at most one such curve at any fixed parent. A constant positive $x$ supports no varying-$t$ component.

Proof. The polynomial $500\widehat F+\ell\widehat G$ is linear in $t$. Its $x^2t$ and $x^2$ coefficients are $7604-8275e$ and $8000e-7680$, which cannot both vanish. A common irreducible factor varying in $x$ must therefore be linear in $t$ over $\mathbb R(x)$. Its unique rational root has reduced denominator dividing $x(x+1)$, by the rational-root theorem applied to $\widehat G$ over $\mathbb R[x]$. If this root grew at infinity, its $100x^2t^2$ term would dominate every other term of $\widehat G$, an impossibility. If it tended to zero, the $320x^2$ term would dominate. Its finite nonzero limit $h$ thus satisfies $Z(h)=0$. The leading $x^2$ coefficient of $\widehat F$ then gives $e=(48h-50)/(50h-45)=e_h$. Partial fractions give (15.2). A rational root of a nonzero linear polynomial in $t$ is unique; isolated zeros of its leading coefficient cannot add another varying-$x$ curve. For constant $x>0$, the leading $t^2$ coefficient of $\widehat G$ is $100x(x+1)>0$, ruling out a curve. This reasoning remains valid at $e=24/25$ and does not assume either quadratic has nonvanishing leading degree in another coordinate. ∎

**引理 15.2（The four denominator cases）。** The reduced denominators $1$, $x$, $x+1$ and $x(x+1)$ in (15.2) give exactly $V$, $A$, $B$ and $H$ in Theorem 14.2.

Proof. The two universal common zeros of (15.1) are

$$
p_k=(k,t_k),\qquad t_k=\frac{8-1/k}{7},\qquad k=\pm r.
\tag{15.3}
$$

Indeed $C/t=(8-7t)x-1$ and $B_5/t=(25-24t)(x+1)-1$ vanish simultaneously precisely at these two points: eliminating $t$ gives $17x^2=24$. Therefore (13.10) vanishes there for every parent, without asserting actual compatibility.

If $\alpha\ne0$ and $\beta=0$, the primitive common factor is $L=x(t-h)-\alpha$. The leading $x^2$ coefficients in (15.1), and then the $t^2$ coefficients, force the cofactors to have the shapes

$$
\widehat F=a_e L[(x+1)t-\gamma],\qquad
\widehat G=100L[(x+1)(t-h')-\beta'].
\tag{15.4}
$$

The two cofactors meet at at most one point, since their difference determines $x+1$ by division by $h'\ne0$. Hence at least one of $p_r,p_{-r}$ lies on $L=0$. Both cannot: subtracting their $L$ values would give $h=8/7$, whereas $Z(8/7)\ne0$. Say $p_k$ lies on $L$. It fixes $\alpha=k(8/7-h)-1/7$. The other basepoint must lie on both cofactors, fixing $\gamma=\beta(0,-k)$ and $\beta'=\beta(h',-k)$. Constant and linear coefficients in (15.4) give exactly the four parent coordinates in row $A$. Conversely multiplication proves (15.4) at those coordinates, using only $Z(h)=0$ and $17k^2=24$.

If $\alpha=0$ and $\beta\ne0$, the same degree comparison gives

$$
\widehat F=a_e L_B(h,k)[xt-\gamma],\qquad
\widehat G=100L_B(h,k)[x(t-h')-\alpha'].
\tag{15.5}
$$

Containing both basepoints would now give $h=25/24$, again impossible. Containing $p_k$ fixes $\beta=\beta(h,k)$; the other basepoint gives $\gamma=\alpha(0,-k)$ and $\alpha'=\alpha(h',-k)$. Coefficient comparison yields exactly row $B$, and (15.5) proves sufficiency.

If both residues are nonzero, the primitive factor

$$
\Lambda=x(x+1)t-[hx^2+(h+\alpha+\beta)x+\alpha]
$$

has degree two in $x$. Its cofactors can depend only on $t$. The leading $x^2$ coefficients force

$$
\widehat F=a_e t\Lambda,\qquad
\widehat G=100(t-h')\Lambda.
\tag{15.6}
$$

The constant-in-$t$ coefficients of $\widehat F$ give $8w-25u=0$ and $24u+w=0$, hence $u=w=0$. Its $x^0t$ and $xt$ coefficients then give $\alpha=-e_h/a_e=(25-24h)/17$ and $h+\alpha+\beta=1$. The corresponding coefficients of $\widehat G$ give $v=z=(100h-141)/17$. Thus this is exactly $H$, and here $\Lambda=x(x+1)t-(hx^2+x+\alpha)$. In original coordinates (15.6) is precisely $F=a_eH_h$, $G=100(t-h')H_h$.

If both residues vanish, set $t=h$ in (15.1). After the $x^2$ coefficients vanish, each remaining pair is a linear system for its parent coordinates. The determinant, up to a nonzero scalar, is

$$
D_0(h)=168h^2-384h+217.
$$

It has no common root with $Z$. Solving gives row $V$. These arguments give all four denominator cases without dividing by a potentially vanishing resultant or by a gain coefficient. All $A,B,H$ residues displayed are nonzero; this also follows from the strict rational coefficient bounds in Section 18. ∎

**命题 15.3（Entire actual fibers and distinct parent labels）。** At each listed parent, no actual signature lies off its stated curve. The twelve parent tuples are distinct.

Proof. In (15.4) and (15.5), the common zeros outside the shared curve consist only of the other universal basepoint, by the unique cofactor intersection. In (15.6), the two cofactors $t$ and $t-h'$ have no common zero. For $V$, write $\widehat F=(t-h)F_V$, $\widehat G=(t-h)G_V$. Their cofactor resultant is

$$
\operatorname{Res}_t(F_V,G_V)
=-\frac{16(300h-863)}{65(7h-8)}x(x+1)(17x^2-24).
\tag{15.7}
$$

Its scalar is nonzero at either root of $Z$. Thus the only positive off-curve candidate is $p_r$. Section 16 rejects every such basepoint for these twelve parents, and specifies exactly the on-curve deletions. Distinct $h$ give distinct $e_h$. For fixed $h$, the four reduced-denominator patterns are distinct; within $A$ or $B$, the two nonzero residues are distinct. If two parent labels coincided, they would give two distinct varying-$x$ curves at that parent, contradicting Lemma 15.1. The positive intervals proved below establish actual moving arcs in every row. ∎

## 16. Critical sources and illegal projected components

**定理 16.1（The separate fixed-source critical chart）。** The only legal signature with $C=B_5=0$ is

$$
x_c=r,\qquad t_c=\frac{8-1/r}{7}=\frac{96-\sqrt{102}}{84},
\qquad R_c=\frac{8r-1}{7}.
\tag{16.1}
$$

It is actual if and only if all four original parent tests hold:

$$
u=dR_c,\qquad v=11R_c,\qquad
w=e(R_c+t_c),\qquad
z=(52-40/t_c)(R_c+t_c).
\tag{16.2}
$$

When (16.2) holds, $Q$ in (13.7) is arbitrary in $V^*$ for the prefix-only equations. There are exactly two fixed source matrices at this signature, each with an affine gain/drift fiber isomorphic to $V^*$. This is gain freedom over a fixed source, not a moving-source curve.

None of the twelve parents of Theorem 14.2 passes (16.2). The point lies on $A(h,k)$ or $B(h,k)$ precisely when $k=r$, and on both $H$ curves; these six rows have the required puncture.

Proof. The simultaneous zero equations were solved in (15.3); their negative-$x$ solution is illegal. At the positive solution

$$
b_c=\frac{8(r-1)}7>0,\qquad
c_c=\frac{16-8r-1/r}{7}>0.
$$

The elementary bounds $1<r<6/5$ give $b_c<8/35<1/4$ and $0<c_c<1$, the latter upper bound following from $8r+1/r>9$. Thus $0<b_cc_c<1/4$, giving two distinct diagonal roots. At $C=B_5=0$, (13.9) is exactly (16.2); if it holds there is no residual equation on $Q$. Formula (13.7) is injective in $Q$ through $g(0)=Q-A$, so the asserted affine dimension follows.

To check critical compatibility of the moving curves, note a useful necessary condition: if all four right-hand sides of (13.9) vanish at a common zero of $C,B_5$, then both gradients $dF,dG$ vanish there. This follows directly by differentiating (13.10). In (15.4), at $p_k$ the first cofactor equals $25k/12\ne0$ and $\partial_tL_A=k\ne0$, so $d\widehat F\ne0$. At the other basepoint the shared factor is nonzero and the first cofactor has $t$ derivative $1-k\ne0$, again giving nonzero gradient. In (15.5) the corresponding values are $16k/7\ne0$, $\partial_tL_B=k+1\ne0$, and the off-curve cofactor's $t$ derivative is $-k\ne0$. In (15.6), $t_k\ne0$ and $\partial_t\Lambda=k(k+1)\ne0$, so again $d\widehat F\ne0$. For $V$, neither $t_k$ equals $h$; the $t$ derivative of $F_V$ is $a_ex(x+1)\ne0$ at either basepoint. Hence every candidate fails a necessary original test. Since $F=t\widehat F$, $G=t^2\widehat G$ and $t_k>0$, these gradient tests are equivalent in the two coordinates. The factor formulas also prove the stated incidence and deletions. ∎

**定义 16.2（Residual quartic）。** For arbitrary parent coefficients, define the residual polynomial

$$
\mathcal K(t)=\frac{\operatorname{Res}_R(F,G)}{t^2D_0(t)},
\qquad D_0(t)=168t^2-384t+217.
\tag{16.3}
$$

This is a polynomial of degree at most four, including the identically zero polynomial. For an explicit determinant definition, write $F=f_2R^2+f_1R+f_0$, $G=g_2R^2+g_1R+g_0$; the numerator is the determinant of the Sylvester matrix with rows $(f_2,f_1,f_0,0)$, $(0,f_2,f_1,f_0)$, $(g_2,g_1,g_0,0)$, $(0,g_2,g_1,g_0)$. In particular $f_2=-(50et-45e-48t+50)/10$, so simultaneous leading-degree drops are explicit. The remaining $f_i$ are given by (13.10); the other three coefficients are

$$
\begin{aligned}
g_2&=Z(t),\\
g_1&=100t^3+(24v-7z-380)t^2+(-25v+8z+280)t,\\
g_0&=(24v+52)t^3+(-24v-z-40)t^2.
\end{aligned}
$$

The substitution $R=tx$ gives $\operatorname{Res}_R(F,G)=t^2\operatorname{Res}_x(\widehat F,\widehat G)$. The two universal basepoints give the factor $D_0$. Expanding the four-row determinant gives degree at most eight before these factors are removed, hence degree at most four in (16.3). The polynomial $g_2$ is not identically zero, and $f_2$ cannot be identically zero for any $e$, since its two coefficients would require both $e=24/25$ and $e=10/9$. Thus the usual resultant common-factor criterion applies over $\mathbb R(t)$, including every specialization in the parent coefficients. This definition retains all degree drops; it does not assert actual compatibility at a resultant root.

**定理 16.3（Both universal illegal families and their finite residuals）。** The condition $\mathcal K\equiv0$ holds exactly for the ten $A,B,H$ parents and the following two families, valid for every real $e$:

$$
\begin{array}{c|cccc|c}
 &u&v&w&z&\text{common projected factor}\\ \hline
 I_0&-e/24&-13/6&e&12&R\\
 I_-&9(2-5e)/70&-99/7&(2-5e)/70&-11/7&R+t.
\end{array}
\tag{16.4}
$$

Their common projected lines are illegal and give no moving positive source. Each nevertheless retains at most one regular actual signature candidate:

$$
\begin{array}{c|cc}
 &t&R\\ \hline
 I_0&\displaystyle\frac{320e}{175e-68}
 &\displaystyle-\frac{t(600t^2-3096t+2581)}{6Z(t)}\\[2mm]
 I_-&\displaystyle\frac{100e-40}{75e-52}
 &\displaystyle\frac{t(2012t-2107)}{7Z(t)}.
\end{array}
\tag{16.5}
$$

Only values passing (13.5), the regular chart conditions and the original equations are actual; both diagonal roots must then be retained. Neither family has a compatible critical gain fiber. Their joint sixteen-slot incidence is not decided by this list.

Proof. A common factor constant in $x$ must have $x=0$ or $x=-1$, by the leading $t^2$ coefficient in (15.1). Setting the remaining coefficients to zero gives exactly (16.4). Explicitly,

$$
\begin{aligned}
G|_{I_0}&=R\left[Z(t)R+t(100t^2-516t+2581/6)\right],\\
G|_{I_-}&=(R+t)\left[Z(t)R+t(2107-2012t)/7\right],
\end{aligned}
\tag{16.6}
$$

and $F$ has the same respective factor. After cancelling that illegal factor, the two residual equations are linear in $R$, with determinants

$$
\begin{aligned}
\operatorname{Res}_R(F/R,G/R)|_{I_0}
 &=\frac{D_0(t)}{24}[(175e-68)t-320e],\\
\operatorname{Res}_R(F/(R+t),G/(R+t))|_{I_-}
 &=\frac{8D_0(t)}{35}[(75e-52)t-100e+40].
\end{aligned}
\tag{16.7}
$$

At a $D_0$ root the residual $G$ equation has nonzero $R$ coefficient, so its unique root is the corresponding universal basepoint; the positive-$R$ one fails $v=11R$ since both displayed $v$'s are negative. If a residual linear factor also vanishes there, its value is still included in (16.5) and subjected to all original tests. A zero denominator in either $t$ expression leaves a nonzero constant in that linear factor, so gives no root. At $Z(t)=0$ the respective residual constants in (16.6) become $t(661-570t)/6$ and $t(2107-2012t)/7$, neither of which vanishes at a root of $Z$. Thus there is no missing finite-$R$ case at these poles. Away from these exceptional values the residual $G$ equation gives exactly (16.5), and (16.7) tests the other equation.

If $\mathcal K\equiv0$, the two polynomials have a common factor of positive $R$ degree over $\mathbb R(t)$. Its curve either varies in $x$, already exhausted by Lemmas 15.1–15.2, or is one of $x=0,-1$. The former can only be $A,B,H$: the $V$ curves have constant $t$ and do not divide a polynomial over $\mathbb R(t)$ as a positive-$R$-degree factor. Conversely (15.4)–(15.6) and (16.6) give all the asserted zero resultants. This proves completeness of the quartic-zero list. ∎

**推论 16.4（All continuous actual fibers）。** Every continuous actual prefix fiber has either a moving signature in Theorem 14.2 or a fixed source with the affine gain freedom of Theorem 16.1. At every other parent its regular source pool is finite. The cases $e=24/25$, $t=1$, $t=8/7$, $t=25/24$, $Z(t)=0$, $C=0$ alone, $B_5=0$ alone and $q=1/4$ are all retained.

Proof. The actual equations are semialgebraic in the fixed source and coefficient parameters; a positive-dimensional signature set has an algebraic common-curve component, classified above. For fixed legal $(R,t)$ there are at most two sources, and at a regular signature (13.11) makes $Q$ unique. Thus continuous fixed-source freedom is exactly the simultaneous zero chart. At fixed $t$, a varying-$R$ fiber requires every coefficient of both polynomials to vanish, which is precisely $V$; otherwise the univariate common zeros are finite. At all other degree-drop strata, Lemma 15.1 and the two affine charts apply without a generic-degree assumption. Equality $q=1/4$ joins source sheets but does not change the rank of (13.9). A zero-dimensional semialgebraic source set is finite. ∎

## 17. Exact maximal positive-signature intervals

**定义 17.1（Endpoint polynomials）。** For each curve let $q(x)=b(x)c(x)$, where $b=xt-1$ and $c=(1-x)t+1$. The symbols $L,U$ below are row-specific; the strictly positive source-entry domain before imposing $q\le1/4$ is exactly $(L,U)$.

For $A$, use its residue $\alpha$ and put

$$
\begin{aligned}
b&=hx+\alpha-1,&
N_A&=-hx^2+(h-\alpha+1)x+\alpha,& c&=N_A/x,\\
E_A(x)&=x-4(hx+\alpha-1)N_A.
\end{aligned}
\tag{17.1}
$$

If $\alpha<1$, set $L=(1-\alpha)/h$; otherwise $L=0$. Let $U$ be the unique zero of $N_A$ greater than $L$.

For $B$, use its residue $\beta$ and put

$$
\begin{aligned}
S_B&=hx^2+(h+\beta-1)x-1,&
T_B&=-hx^2+(1-\beta)x+h+\beta+1,\\
b&=S_B/(x+1),&c&=T_B/(x+1),\\
E_B(x)&=(x+1)^2-4S_BT_B.
\end{aligned}
\tag{17.2}
$$

Let $L$ be the unique positive zero of $S_B$, and $U$ the unique zero of $T_B$ greater than $L$.

For $H$, use its two residues and put

$$
\begin{aligned}
S_H&=hx^2+\alpha-1,&
T_H&=-hx^3+hx^2+(2-\alpha)x+\alpha,\\
b&=S_H/(x+1),&c&=T_H/[x(x+1)],\\
L&=\sqrt{(1-\alpha)/h},&
E_H(x)&=x(x+1)^2-4S_HT_H.
\end{aligned}
\tag{17.3}
$$

Let $U$ be the unique zero of $T_H$ greater than $L$.

For $V$, put $L=1/h$, $U=1+1/h$. In its $h_+$ row put

$$
d_1=\frac{h+2-\sqrt{h^2-1}}{2h},\qquad
 d_2=\frac{h+2+\sqrt{h^2-1}}{2h}.
\tag{17.4}
$$

For each of the six rows $A(h,r)$, $B(h,r)$ and $H(h)$, let $d_1$ be the unique root of its $E$ polynomial in $(r,3/2)$, and $d_2$ its unique root in $(3/2,U)$. Their exact order is

$$
L<r<d_1<3/2<d_2<U.
\tag{17.5}
$$

For $A(h_+,-r)$, let $d$ be the unique root of $E_A$ in $(0,U)$. For $B(h_+,-r)$, let $\xi$ be the unique point of $(L,U)$ with $b=c$, equivalently

$$
(2x-1)[h(x+1)+\beta]-2(x+1)=0.
\tag{17.6}
$$

Let $d_1,d_2$ be the unique roots of $E_B$ in $(L,\xi)$ and $(\xi,U)$, respectively. The following theorem proves all existence, uniqueness and order assertions in this definition, so these are exact algebraic endpoints rather than numerical approximations.

**定理 17.2（Complete maximal-interval table）。** The entire actual positive signature fiber at the twelve parents consists exactly of the following intervals. The rightmost column counts actual source/unique-gain connected components, including both diagonal sheets.

| Fixed parent | Number of parents | Maximal signature intervals per parent | Interval count per parent | Source/gain components per parent |
| --- | --- | --- | --- | --- |
| $V(h_-)$ | $1$ | $(L,U)$ | $1$ | $2$ |
| $V(h_+)$ | $1$ | $(L,d_1]\ \cup\ [d_2,U)$ | $2$ | $2$ |
| $A(h_-,-r)$ | $1$ | $(L,U)$ | $1$ | $2$ |
| $A(h_+,-r)$ | $1$ | $[d,U)$ | $1$ | $1$ |
| $A(h,r)$, each $h$ | $2$ | $(L,r)\ \cup\ (r,d_1]\ \cup\ [d_2,U)$ | $3$ | $4$ |
| $B(h_-,-r)$ | $1$ | $(L,U)$ | $1$ | $2$ |
| $B(h_+,-r)$ | $1$ | $(L,d_1]\ \cup\ [d_2,U)$ | $2$ | $2$ |
| $B(h,r)$, each $h$ | $2$ | $(L,r)\ \cup\ (r,d_1]\ \cup\ [d_2,U)$ | $3$ | $4$ |
| $H(h)$, each $h$ | $2$ | $(L,r)\ \cup\ (r,d_1]\ \cup\ [d_2,U)$ | $3$ | $4$ |

In particular the disjoint totals over these twelve fixed-parent labels are exactly $26$ maximal signature intervals and $35$ actual source/regular-gain connected components. The separate critical affine fibers of Theorem 16.1 and finite source pools at other parents are outside these totals.

## 18. Root order and sign proof for the interval table

**引理 18.1（Exact coefficient bounds and entry positivity）。** The following strict rational inequalities hold:

$$
\frac{995}{1000}<h_-<\frac{996}{1000},\qquad
\frac{3214}{1000}<h_+<\frac{3215}{1000},\qquad
\frac{1188}{1000}<r<\frac{1189}{1000}.
\tag{18.1}
$$

They give the residue bounds

$$
\begin{array}{c|cc}
(h,k)&\alpha(h,k)&\beta(h,k)\\ \hline
(h_-,r)&(31/1000,34/1000)&(5/100,7/100)\\
(h_-,-r)&(-32/100,-31/100)&(-6/100,-4/100)\\
(h_+,r)&(-261/100,-259/100)&(-481/100,-478/100)\\
(h_+,-r)&(23/10,7/3)&(36/100,38/100).
\end{array}
\tag{18.2}
$$

Every $(L,U)$ in Definition 17.1 exists and is exactly the strictly positive source-entry domain.

Proof. Evaluation of $Z$ at the four rational endpoints in (18.1) isolates its two roots, and squaring the positive rational bounds isolates $r$. Substitution into the affine residue formulas, bounding the products by their rational endpoints, proves (18.2).

For $A$ with $\alpha<1$, $b$ is positive exactly for $x>L$. At $L$, $c=t=h/(1-\alpha)>0$. For a negative residue the bounds imply

$$
(-\alpha)h<(1-\alpha)^2;
\tag{18.3}
$$

for example in the large negative case the left side is less than $(261/100)(13/4)$, and the right side exceeds $(359/100)^2$. The small negative case has left side less than $32/100$ and right side greater than $(131/100)^2$. Since $c'=-h-\alpha/x^2$, (18.3) makes $c$ strictly decreasing for $x\ge L$; positive $\alpha$ makes it decreasing directly. It tends to $-\infty$, so has precisely the asserted zero $U$. For $A(h_+,-r)$, $\alpha>1$: $b>0$ for all $x>0$, while $c$ decreases from $+\infty$ to $-\infty$. This gives its $L=0$ and unique $U$.

For $B$, the quadratic $S_B$ has positive leading coefficient and negative constant term, so exactly one positive zero $L$. At that point $R=1$ and $t=1/L>0$, so $T_B(L)>0$. The concave quadratic $T_B$ has exactly one zero after $L$ and remains negative thereafter. Before $L$ the entry $b$ is negative, and after $U$ the entry $c$ is negative. On $(L,U)$ their positivity also proves $t=b+c>0$.

For $H$, $\alpha<1$ and $S_H$ changes sign exactly at the displayed $L$. The other entry can be written $c=(1-x)t+1$, with

$$
c'=-h-\frac\alpha{x^2}-\frac{2\beta}{(x+1)^2}.
\tag{18.4}
$$

For $h_-$, $0<\alpha<1$ and $-7/100<\beta<0$, so $c'<-h+14/100<0$. For $h_+$, $\alpha<0$, $\beta>0$ and $x\ge L$ give $(-\alpha)/x^2\le(-\alpha)h/(1-\alpha)<h$, again giving strict decrease. At $L$, $b=0$, $R=1$ and $c=t=1/L>0$; at infinity $c$ tends to $-\infty$. This proves the unique $U$. The $V$ assertion is immediate from $b=hx-1$, $c=h+1-hx$. ∎

**引理 18.2（Strict concavity except for the monotone A row）。** The function $q=bc$ is strictly concave on every positive-entry interval except $A(h_+,-r)$, where it is strictly decreasing from $+\infty$ to zero.

Proof. For $A$, direct differentiation gives

$$
q''=-2h^2+\frac{2\alpha(\alpha-1)}{x^3}.
\tag{18.5}
$$

For $0<\alpha<1$ both terms are negative. For $\alpha<0$, use $x\ge(1-\alpha)/h$ and (18.3) to make the second term strictly less than $2h^2$. The remaining $A(h_+,-r)$ has

$$
q'=-2h^2x+h(h-2\alpha+2)-\frac{\alpha(\alpha-1)}{x^2}.
\tag{18.6}
$$

Here $h(h-2\alpha+2)<2$, by $h<643/200$ and $\alpha>23/10$. If $x\ge1/4$, the magnitude of the first negative term exceeds $128/25>2$. If $0<x\le1/4$, the magnitude of the last negative term exceeds $16(23/10)(13/10)>2$. Hence $q'<0$ everywhere. Also $b\to\alpha-1>0$, $c\sim\alpha/x$ at zero, so $q\to+\infty$ there, and $q\to0$ at $U$.

For $B$, with $y=x+1$, differentiation gives

$$
q''=-\frac2{y^4}\left[h^2y^4-\beta(3\beta-4h-3)y+6\beta^2\right].
\tag{18.7}
$$

Call the bracket $K(y)$. For either positive $\beta$, (18.2) gives $3\beta-4h-3<0$, so $K>0$. For the small negative $\beta$, it gives $\beta(3\beta-4h-3)<1/2<h^2$, and $y>1$ gives $K>0$. For the large negative residue $B(h_+,r)$, $S_B(1)=2h+\beta-2<0$, so $L>1$ and $y>2$. Using $16/5<h<13/4$ and $-5<\beta<0$ gives

$$
K(2)=16h^2+(8h+6)\beta>96/25>0,
$$

and

$$
K'(y)=4h^2y^3-\beta(3\beta-4h-3)
 >8192/25-155>0\quad(y\ge2).
$$

Thus $q''<0$ in every $B$ row.

For $H$, the identity $h+\alpha+\beta=1$ gives

$$
q''=-2h^2-\frac{2\alpha(h+\beta)}{x^3}
 +\frac{2\beta(\alpha-7h)}{(x+1)^3}
 -\frac{12\beta^2}{(x+1)^4}.
\tag{18.8}
$$

For $h_-$, the only positive displayed term is bounded above by $2(7/100)7$, whereas $2h^2>2(995/1000)^2$; the other terms are negative. For $h_+$, $\alpha<0$, $\beta>0$ and $\alpha-7h<0$. Moreover

$$
\alpha^2-h(1-\alpha)=\frac{2185-8918h}{7225}<0.
\tag{18.9}
$$

Since $x\ge\sqrt{(1-\alpha)/h}$, (18.9) gives $(-\alpha)(1-\alpha)/x^3<h^2$. Consequently the only positive term, the second in (18.8), is smaller than $2h^2$, and $q''<0$. The $V$ formula is a concave quadratic. ∎

**引理 18.3（All discriminant crossings and puncture orders）。** The endpoint roots and orders specified in Definition 17.1 hold. The sign of the source discriminant is exactly the one used in Theorem 17.2.

Proof. In $V(h_-)$, $A(h_-,-r)$ and $B(h_-,-r)$, one has $0<t<1$ on the positive-entry interval. Therefore $q\le t^2/4<1/4$, so there is no crossing. In $V(h_+)$, $q=(hx-1)(h+1-hx)$, and solving $q=1/4$ gives (17.4) with $L<d_1<d_2<U$. Its discriminant is negative between these roots and nonnegative on the two outer intervals.

Consider the six punctured rows. The identities in Sections 15–16 give at $x=r$ exactly the same $(R_c,t_c)$; in particular $L<r<U$ and $0<q(r)<1/4$. Also

$$
1<t(3/2)<5/3.
\tag{18.10}
$$

For $A$ and $B$, substitute their residues and use (18.1)–(18.2). For $H$, the value is exactly $(57h+202)/255$, which satisfies the two strict bounds by (18.1). At $x=3/2$,

$$
q(3/2)-\frac14
 =\frac{(t(3/2)-1)(5-3t(3/2))}{4}>0.
\tag{18.11}
$$

Strict concavity, $q(L)=q(U)=0$, and (18.11) prove exactly two crossings of $1/4$, both simple, one on each side of $3/2$. Since $r<3/2$ and $q(r)<1/4$, the first crossing lies strictly after $r$. This proves the full order (17.5), not just a root count. Indeed a strictly concave function has a convex strict superlevel interval; three level crossings would contradict strict concavity, and the two interior-to-endpoint sign changes ensure the claimed two. The same argument makes the derivatives nonzero at those crossings. On $x>0$, the sign of each $E_A,E_B,E_H$ is exactly the sign of $1-4q$, since their cleared denominators are positive.

For $B(h_+,-r)$, $\beta>0$, so $b'=h+\beta/(x+1)^2>0$ and $c'=-h-2\beta/(x+1)^2<0$. Thus $b-c$ increases from negative to positive between $L$ and $U$, giving the unique $\xi$ in (17.6). At $\xi$, $q=t^2/4>h_+^2/4>1/4$. Concavity and zero endpoint values give exactly two simple crossings, ordered $L<d_1<\xi<d_2<U$.

Finally (18.6) proves one and only one simple crossing in $A(h_+,-r)$; $q\le1/4$ there precisely for $x\in[d,U)$. These arguments locate every crossing inside the full positive-entry domain and exclude every additional such crossing. The endpoint $x=r$ is removed exactly in the six stated rows by the original equations, not by a discriminant convention. Together with Lemma 18.1 this proves all the signature intervals in Theorem 17.2. ∎

## 19. Diagonal joins and actual connected components

**定理 19.1（Topology of the reconstructed fibers）。** Over each regular signature interval in Theorem 17.2 the actual source and entire gain/drift fiber is the union of the two graphs

$$
x\longmapsto\left(P_\pm(x),g_x,\delta_x\right),\qquad
 a_\pm(x)=\frac{1\pm\sqrt{1-4q(x)}}2,
\tag{19.1}
$$

with $g_x,\delta_x$ given by (13.7), (13.11). An interval with no $q=1/4$ point has exactly two connected components. An interval with an included discriminant endpoint has exactly one. Thus the totals are exactly $26$ intervals and $35$ actual connected components as in Theorem 17.2.

Proof. The two affine charts cover every regular point and agree on their overlap by uniqueness of $Q$. They therefore define a continuous gain/drift map throughout the interval, including a point where one chart coefficient vanishes. The source graph has the continuous inverse $x=(1+b)/(b+c)$, so its topology is precisely that of the two displayed sheets. Where $q<1/4$, one sheet has $a<1/2$ and the other $a>1/2$; if there is no discriminant-zero point, these two relatively open-and-closed parts cannot join. Each is homeomorphic to the interval and is connected. At an included endpoint with $q=1/4$, the two graphs meet at the same $a=1/2$, same $b,c$ and same unique $Q$, giving a connected union.

No two different maximal signature intervals can join: their continuous signature projections are separated by an interval with $q>1/4$, an excluded critical signature, or an excluded source-positivity endpoint. Every nonzero finite $L$ or $U$ in the table has $b=0$ or $c=0$ and is excluded by strict positivity. The auxiliary $L=0$ in $A(h_+,-r)$ is an infinite-source limit with $q\to\infty$, outside its legal interval. At a critical puncture no compatible gain exists for that parent. Thus neither a source boundary nor gain freedom supplies an unlisted join.

For each punctured row, $(L,r)$ gives two components, while $(r,d_1]$ and $[d_2,U)$ each give one, hence four. The unpunctured rows give respectively $2,2,2,1,2,2$ components in the order of the table after omitting its punctured rows. Consequently the interval total and component total are

$$
\begin{aligned}
&1+2+1+1+2\cdot3+1+2+2\cdot3+2\cdot3=26,\\
&2+2+2+1+2\cdot4+2+2+2\cdot4+2\cdot4=35.
\end{aligned}
\tag{19.2}
$$

These are topological conclusions from root order, signs and sheet joins; algebraic irreducibility is not used to infer connectedness. At a compatible critical parent there are instead the two disjoint affine fibers of Theorem 16.1, one over each fixed source. ∎

## 20. Whole-carrier use, mathematical sources and the remaining incidence

**命题 20.1（Conditional transfer to the original whole kernel）。** Consider the unchanged complete legal $256$-source tuple, all $254$ nonempty proper prefixes, its original $1538\times1024$ matrix $B$, and its entire $V=\ker B$. Suppose the two $J^7$ sources have unit signature and the common history satisfies

$$
\operatorname{rank}H=\operatorname{rank}(F_{\rm hist},\Delta)=2,
\qquad E=eF_{\rm hist}+f\Delta,
\qquad75e+16f=52,\qquad e>-4.
\tag{20.1}
$$

Suppose also that all eight original leaf-separation guards below $JJJM$ hold. Then the public [history-fiber Theorem 37.1, under Definition 36.1](FIB_ORIGINAL_ROOT_J_SIGNATURE_COUPLING_AND_HISTORY_FIBER_DECODER.md#37-十六槽在原整个核上的一致历史分解), with its paired-kernel suppliers in Sections 35–36, applies on this same entire $V$. It gives $Q_q\in\operatorname{span}\{X,D\}$ for all sixteen slots, where $X=F_{\rm hist}-75\Delta/16$ and $D=\Delta$, as well as factorization of every shared response through this history. Consequently each fifth-M slot is exactly covered by the source tests and reconstruction in Sections 13–19, using its common $(u,v,w,z)$.

Proof. The hypotheses are exactly the directed rank-two and eight-guard hypotheses of the cited theorem, with the original unit-source premise retained. That theorem eliminates hidden directions on $\ker H$ for both fifth-action children; no chosen two-plane or restricted subkernel is substituted for $V$. Its common fourth and fifth-M forms give (13.3) on $V$, and its entire interpolation is (13.7). Apply Theorem 13.2. At a critical slot, membership of $Q$ in the two-dimensional span is an additional conclusion of this whole-kernel theorem: the affine critical fiber of prefix-only equations has dimension $\dim V$, and becomes dimension two only under this supplier. ∎

**定义 20.2（Unchanged simultaneous and original-root boundary）。** The auxiliary classification supplies neither an original same-history simultaneous sixteen-source certificate nor a uniform original full-$G$ or complete-four-coordinate-$D$ obstruction. Even at the ten nonvertical moving parents, the eight fifth-M slots must choose from their one common certified fiber, while the eight fifth-J slots share exactly the same first-three-J and fourth response; their common fifth-J response remains free. All actual clock-six and clock-seven equations from [history-fiber Definition 38.1](FIB_ORIGINAL_ROOT_J_SIGNATURE_COUPLING_AND_HISTORY_FIBER_DECODER.md#38-同一历史的十六正来源精确关联式), both actions, early stopping and the original guards must still hold simultaneously. The finite regular pools at other parents, the residual candidates of (16.5), and compatible critical gain fibers likewise retain their coupled incidence obligations. No equality from different terminal source pairs is transferred to one pair.

A finite continuation problem is to impose that same Definition 38.1 on all ten nonvertical parent tuples using the exact intervals, both diagonal sheets, the reconstructed entire maps and one free fifth-J form. An emptiness proof would have to exhibit an applicable original guard or a contradiction of those simultaneous actual equations for every such assignment; a survivor would have to give all sixteen fixed sources and shared forms. Neither a separate leaf fit nor the present component count does so. The generic finite-pool and critical-parent complements remain separate obligations of the original goal.

Even a local sixteen-slot survivor must match the earlier $JJJJ$ sibling with its already determined fourth response, and then extend to the full fixed $256$-source, $254$-prefix contract. Original full existence requires every original $G$ and applicable full four-coordinate $D$ nonzero on the same whole $V$, or one simultaneous full coefficient vector satisfying all those guards. No selected plane, independently assigned history or unrestricted lifted matrix replaces this requirement. The global eight-versus-nine alternatives, earlier siblings, full-tree existence and a nine-read upper bound are not settled here.

The rational diagonal-swap benchmark at $e=68/75$, its eight-slot fifth-J extension and its failed reuse boundary remain the [history-fiber Theorems 28.2–29.2 and Section 30](FIB_ORIGINAL_ROOT_J_SIGNATURE_COUPLING_AND_HISTORY_FIBER_DECODER.md#28-有理对角交换的-jjjmjjj-实际响应核). The published $e=0$ exclusion is used only with its existing hypotheses. The two other supplier half-lines at $e=-4/5$ and $e=-16/5$ retain their own ranges; the directed family here meets them only at its actual intersections. The two vertical parents are included as existing benchmarks, without a new claim of their previously supplied obstructions. All signed nonzero gains of degree at most three, sampled and repeated roots, one arbitrary constant drift, original clocks, billed atomic and initial readings, both actions and early stops remain in the model.

**定义 20.3（Mathematical source correspondence）。** The original source and response model is this volume's Definition 1.1; the complete-kernel guard interface is Definitions 2.1–2.2 and [IV, Definitions 13.1–13.2 and Theorem 13.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md#13-原根完整目标的联合源秩投影). The first-three interpolation, directed history coordinates, actual trace table and whole-carrier factorization are the [history-fiber Sections 35–39](FIB_ORIGINAL_ROOT_J_SIGNATURE_COUPLING_AND_HISTORY_FIBER_DECODER.md#35-不等正来源的尖锐配对七响应核界). Four-point interpolation, rational-root divisibility, polynomial resultants and elementary concavity are standard mathematical tools. Their use here yields the explicit original-model factor strata, exact interval endpoints and actual component inventory, rather than a new general elimination principle.

[Li--Lee--Bresler, Definition 2.7 and Theorem 2.8, version 1](https://arxiv.org/html/1501.06120v1), characterize constrained nonzero-factor identifiability up to a specified transformation group, separating first-factor orbit identification from conditional second-factor identification. This parallels first locating actual sources and then using the unique regular gain chart, but the general result does not impose the present positive rank-one domain, affine drift or adaptive-prefix incidence. [Choudhary--Mitra, Proposition 1 and Remark 5, version 2](https://arxiv.org/html/1402.2637v2), retain the realizable product-difference set in the lifted-kernel criterion; here (13.5), (13.9) and the critical tests enforce that distinction explicitly. Neither cited result supplies the twelve parent tuples, their $26$ intervals or $35$ components. The new content is this model-specific classification relative to the stated suppliers; no global priority or exhaustive-literature assertion is made. These are ordinary mathematical proofs.

## 追加锚（本行以下为增补区）

## 21. 十个非竖直父历史的原守卫排除

**定义 21.1（十个供应父历史）。** Retain the directed rank-two history of
Definition 36.1, the original whole space \(V=\ker B\), and the coordinates
\(X,\Delta,A,p\) of (36.4).  The following notation names exactly the ten
supplied nonvertical parent histories.  Put

$$
Z(h)=100h^2-421h+320,\qquad
h_\pm=\frac{421\pm\sqrt{49241}}{200},\qquad
\bar h=\frac{421}{100}-h,\qquad
\rho=\sqrt{\frac{24}{17}},\qquad k\in\{\rho,-\rho\},
$$

and, for a real \(s\),

$$
\alpha(s,k)=k\left(\frac87-s\right)-\frac17,\qquad
\beta(s,k)=1-s+k\left(\frac{25}{24}-s\right).
$$

For every \(h=h_\pm\), set \(e=(8h-14)/13\), \(d=(5e-2)/10\), and
\(\ell=25e-24\).  The four \(R\)-rows are indexed by \((h,k)\) and have

$$
\begin{aligned}
 a_R&=\alpha(h,k),&\gamma_R&=\beta(0,-k),&b'_R&=\beta(\bar h,-k),\\
 u_R&=\frac{\ell a_R/5-e}{24},&
 v_R&=-\frac{25a_R+13}{6},&
 w_R&=e+\frac{\ell a_R(\gamma_R-1)}5,&
 z_R&=\frac{100b'_R-11}{7}.
\end{aligned}
$$

Their positive source chart is

$$
t=h+\frac{a_R}{x},\qquad R=xt,\qquad
Q=\frac{u_RX+v_R\Delta/16-R(dX+11\Delta/16)}{(8-7h)(x-k)}.
\tag{21.1}
$$

The four \(N\)-rows, again indexed by \((h,k)\), have

$$
\begin{aligned}
 b_N&=\beta(h,k),&\gamma_N&=\alpha(0,-k),&a'_N&=\alpha(\bar h,-k),\\
 u_N&=\frac{\ell\gamma_N/5-e}{24},&
 v_N&=-\frac{25a'_N+13}{6},&
 w_N&=e+\frac{\ell\gamma_N(h+b_N-1)}5,&
 z_N&=\frac{100b_N-11}{7},
\end{aligned}
$$

with chart

$$
t=h+\frac{b_N}{x+1},\qquad R=xt,\qquad
Q=\frac{w_NX+z_N\Delta/16-(R+t)\{eX+(13/4-5/(2t))\Delta\}}
{(25-24h)(x-k)}.
\tag{21.2}
$$

The two \(H\)-rows have

$$
a_H=\frac{25-24h}{17},\qquad b_H=\frac{7h-8}{17},\qquad
(u_H,v_H,w_H,z_H)=\left(0,\frac{100h-141}{17},0,\frac{100h-141}{17}\right),
$$

and chart

$$
t=h+\frac{a_H}{x}+\frac{b_H}{x+1},\qquad R=xt,\qquad
Q=\frac{(x+1)\{u_HX+v_H\Delta/16-R(dX+11\Delta/16)\}}
{(8-7h)(x^2-\rho^2)}.
\tag{21.3}
$$

For each chart, \(x\) ranges over its actual legal positive-entry intervals.
The source is reconstructed by

$$
b=R-1,\qquad c=t-R+1,\qquad
q=bc,\qquad a=a_\pm=\frac{1\pm\sqrt{1-4q}}2,
\tag{21.4}
$$

where \(b,c>0\), \(0<a<1\), and \(q\le1/4\).  Thus both diagonal sheets and
their included \(q=1/4\) joins are part of every row.  The letter \(Q\) is the
whole linear form \(g(0)+A\) on \(V\), and the gain and drift are the complete
forms in (35.2), including all four coefficients and the constant drift.

**引理 21.2（十个图表上的第六步 \(M\) 单射）。** For one of the ten rows,
let \(g_Q\) be its complete gain form and define the actual sixth-\(M\) response
offset

$$
F_6(x)=(2R(x)+t(x))g_Q(6)-Q(x)
       =F_{6,X}(x)X+F_{6,\Delta}(x)\Delta.
\tag{21.5}
$$

The map \(x\mapsto(F_{6,X}(x),F_{6,\Delta}(x))\) is injective on every legal
positive source interval, including both sheets and every discriminant join.
The complete seventh-\(J\) gain form

$$
G_7(x)=g_Q(7)
 =[1-105(1-1/t)]Q+(e+16/5)X
   +\left(\frac34+\frac{35}{2}(1-1/t)\right)\Delta
\tag{21.6}
$$

is nonzero as a form on \(V\) at every such legal \(x\).  Neither assertion
divides by a carrier value or by an individual gain sample.

**证明.** For an \(R\)-row put \(j=0\), and for an \(N\)-row put \(j=1\),
\(\zeta=x+j\), \(K=k+j\).  Each coefficient of (21.5) has the form

$$
F_{6,l}(x)=\frac{N_l(\zeta)}{\zeta(\zeta-K)},\qquad
N_l(\zeta)=\alpha_l\zeta^3+\beta_l\zeta^2+\gamma_l\zeta+\delta_l,
\quad l\in\{X,\Delta\}.
$$

For a putative collision at two distinct non-poles \(\zeta_0,\zeta_1\), set
\(\sigma=\zeta_0+\zeta_1\), \(\pi=\zeta_0\zeta_1\).  Cross multiplication and
division by \(\zeta_0-\zeta_1\) gives, for each \(l\),

$$
\alpha_l\pi(\pi-K\sigma)
 -(K\beta_l+\gamma_l)\pi-\delta_l(\sigma-K)=0.
\tag{21.7}
$$

Exact reduction in the field generated by \(h\) and \(k\) shows that the two
equations have at most one unordered off-diagonal candidate.  The following
strict rational enclosures, in units of \(10^{-3}\), are the resulting
\((\sigma,\pi)\) candidates; each listed sign or inequality excludes it from
the legal positive domain:

$$
\begin{array}{c|c|c|c}
\text{row}&1000\sigma&1000\pi&\text{exclusion}\\ \hline
R(h_-,-\rho)&(-11864,-11863)&(-400,-399)&\pi<0\\
R(h_-,+\rho)&(2368,2369)&(40,41)&\pi-\sigma/2+1/4<0\\
R(h_+,-\rho)&(-5358,-5357)&(901,902)&\sigma<0\\
R(h_+,+\rho)&(690,691)&(-1013,-1012)&\pi<0\\
N(h_-,-\rho)&(-14117,-14116)&(13288,13289)&\sigma<0\\
N(h_-,+\rho)&(1241,1242)&(-2445,-2444)&\pi<0\\
N(h_+,-\rho)&(-3529,-3528)&(2139,2140)&\sigma<0\\
N(h_+,+\rho)&(2867,2868)&(1218,1219)&\pi-\sigma+1<0
\end{array}
\tag{21.8}
$$

In the two rows with a shifted inequality, source positivity itself gives
\(x>1/2\) in the \(R(h_-,+\rho)\) chart and \(x>1\) in the
\(N(h_+,+\rho)\) chart, so the displayed products would have to be positive.
All denominator cases and positive chart poles are checked in the same exact
reduction; the only possible positive off-curve basepoint has the critical
signature \(C=B=0\), and its mandatory absolute equation would require
\(v=11(8\rho-1)/7\), which none of the ten rows satisfies.

For an \(H\)-row, clear the positive chart denominator
\(D(x)=x(x+1)(x^2-\rho^2)\).  The two secant equations for a collision have
a monic resultant in \(\pi\) of the exact form

$$
R_h(\pi)=\pi^4(\pi^2-\rho^2)(\pi+\rho^2)T_h(\pi).
\tag{21.9}
$$

At \(\pi=\rho\) the common \(\sigma\)-factor is \(\sigma+1+\rho\), and
\(\pi=0,-\rho,-\rho^2\) cannot come from two positive parameters.  Writing
\(T_h=\pi^5+c_4\pi^4+c_3\pi^3+c_2\pi^2+c_1\pi+c_0\), exact rational
interval arithmetic gives

$$
\begin{array}{c|ccccc|c}
 &c_4&c_3&c_2&c_1&c_0&\text{legal }\pi\\ \hline
h_-&(-6,-5)&(-19,-18)&(-12,-11)&(2,3)&(-1,0)&9/10<\pi<4\\
h_+&(9,10)&(22,23)&(13,14)&(-11,-10)&(-9,-8)&\pi>1
\end{array}
$$

The first row makes \(T_{h_-}<0\) on its legal range and the second makes
\(T_{h_+}>0\) there, so no remaining resultant branch is realizable.  This
proves the \(H\) injectivity, including the chart endpoints.

Finally, reduce the two coefficient numerators of (21.6) to monic polynomials
in \(x\).  Their exact gcd is \(1\) in
\(\mathbb Q(\sqrt{49241},\sqrt{102})\); the signs of their nonzero resultants
in the row order \(R(h_-,-\rho),R(h_-,+\rho),R(h_+,-\rho),R(h_+,+\rho),
N(h_-,-\rho),N(h_-,+\rho),N(h_+,-\rho),N(h_+,+\rho),H(h_-),H(h_+)\) are

$$
-,-,+,-,-,-,+,-,+,+.
\tag{21.10}
$$

Hence both coefficients of \(G_7(x)\) never vanish together.  These finite
field reductions and rational sign bounds are the supplied seat certificates;
they are used only for the ten displayed rows and do not assert a classification
of any other parent history. ∎

**定理 21.3（十个非竖直父历史的同一终端原守卫失败）。** Consider a
complete legal \(256\)-source tuple, its original \(1538\times1024\) matrix
\(B\), and the original \(V=\ker B\), with one of the ten parent histories of
Definition 21.1.  If the separation hypotheses required by Theorem 37.1 fail,
that theorem already supplies an equal-source terminal pair with
\(D_w|_V=0\) in all four coordinates.  In the other branch, Theorem 37.1
factors all sixteen gains and all shared responses through the same independent
forms \(X,\Delta\) on this entire \(V\).  In that factorized branch, the actual
terminal pair at

$$
w_*=JJJMMMJ
$$

has equal sixth-\(M\) response only when its two source-chart parameters agree;
then its seventh-\(J\) response forces the two diagonal parameters to agree.
Consequently its two fixed sources, complete gains and constant drifts agree,
and

$$
D_{JJJMMMJ}|_V=0,\qquad
\operatorname{rank}[B;D_{JJJMMMJ}]=\operatorname{rank}B.
\tag{21.11}
$$

Thus no one of these ten parent histories can satisfy all original separation
guards, for any common fifth-\(J\) response form.

**证明.** Assume first the factorized branch.  Let \(x_0,x_1\) be the chart
parameters of the two fixed slots at \(w_*\).  The actual sixth-\(M\) trace is

$$
\tau_6=2R+t,
$$

which is independent of the diagonal source coordinate \(a\).  The common
sixth response supplied by the original \(B\) therefore gives
\(F_6(x_0)=F_6(x_1)\) as an equality of the two coefficient forms in
\(X,\Delta\).  Lemma 21.2 gives \(x_0=x_1\), including all regular intervals,
both sheets, and included discriminant joins.  Equations (21.1)--(21.3) then
give the same \(t,R,Q\), so (35.2) gives exactly the same entire cubic-or-lower
gain and \(\delta=A-Q\), as forms on \(V\).

The actual seventh-\(J\) traces are

$$
\tau_7(a_i)=1+2a_i+2t\qquad(i=0,1).
$$

Subtracting the two seventh responses of this same terminal pair, with no
equation borrowed from another pair, yields

$$
2(a_0-a_1)G_7(x_0)=0\quad\text{in }V^*.
\tag{21.12}
$$

By Lemma 21.2, \(G_7(x_0)\) is a nonzero form, hence \(a_0=a_1\).  The source
matrices are therefore identical, including the \(q=1/4\) join case.  Subtract
the six shared ancestor equations of this same pair.  The complete gain
difference, including its constant coefficient and normalized drift difference,
lies in the injective fixed-source kernel of Lemma 36.2; it is zero on every
vector of the original \(V\).  This proves (21.11), so the applicable original
guard fails.

The first branch was already the failed-guard alternative in Theorem 37.1.
No fifth-\(J\) form was fixed or eliminated, and no equality from a different
terminal source pair was transferred to \(w_*\). ∎

**定义 21.4（范围与未决边界）。** The conclusion retains strict source
positivity, both diagonal sheets, all discriminant joins, singular \(Q\)-chart
points and degree-drop strata.  Positive chart poles and off-curve critical
basepoints are tested by the original absolute equations rather than silently
cancelled.  Gains remain signed nonzero polynomials of degree at most three,
with sampled or repeated roots allowed; the constant drift, actual clocks
\(0,\ldots,7\), billed initial and atomic readings, both actions, early stopping,
and the original full \(V=\ker B\) are unchanged.  No gain value, carrier
coordinate, or fifth-\(J\) response is divided out.

This section settles exactly the ten supplied \(R/N/H\) parent histories.  The
complementary finite-pool and compatible critical parents remain open, as does
the earlier \(JJJJ\) sibling.  The full \(256\)-source problem, the full-\(G\)
and full-four-coordinate-\(D\) obligations, and the global eight-versus-nine
alternative remain open.  No global completion, nine-read upper bound, or
external novelty claim follows from this ten-parent obstruction.

The five executable seat certificates are fallible mathematical input for the
finite reductions in Lemma 21.2.  Their scope is exactly the ten rows above;
they do not replace the original \(B\)-equations, the full-\(V\) factorization,
or the guard interface of Definitions 2.1--2.2 and Theorem 37.1.

## 22. 临界 \(C=B_5=0\) 图的四槽原守卫障碍

本节处理 Definition 38.1 中一个更窄的来源图。它不把“兼容临界父历史”
误当成所有后代都必须临界；后者允许 regular source，仍属于未决问题。

**定义 22.1（四个临界后代）。** Fix the original legal \(256\)-source
tuple, its full \(1538\times1024\) matrix \(B\), and the same original

$$
V=\ker B.
$$

Assume the directed rank-two factorization of Theorem 37.1, so the two
independent forms \(X,\Delta\) are forms on this entire \(V\).  Require the
four slots below the literal prefix \(JJJMMJ\), namely the two slots at

$$
w_1=JJJMMJJ,
\qquad
w_2=JJJMMJM,
$$

to use the critical signature \(C=B_5=0\).  Theorem 16.1 gives the unique
positive signature

$$
h_c=\frac{25-2\sqrt{102}}{217},\qquad
t_c=\frac1{1-h_c}=\frac{96-\sqrt{102}}{84},\qquad
R_c=\frac1{1-8h_c}=\frac{16\sqrt{102}-17}{119}.
$$

Put \(U_c=R_c+t_c\),

$$
b_c=R_c-1,\qquad c_c=t_c-R_c+1,\qquad
a_\pm=\frac{1\pm\sqrt{1-4b_cc_c}}2.
$$

The strict positivity and rank-one trace-one conditions give

$$
0<b_cc_c<\frac14,
$$

so \(a_+\ne a_-\).  For a critical slot \(q\), write its entire gain form as
\(Q_q\).  Equations (38.2)--(38.6) give, on the same \(V\),

$$
g_q(6)=\alpha _6Q_q+L_6,
\qquad
g_q(7)=\alpha _7Q_q+L_7,
$$

where

$$
\begin{aligned}
\alpha _6&=1-56h_c,&
L_6&=\frac{5e+4}{4}X+\left(\frac34+8h_c\right)\Delta,\\
\alpha _7&=1-105h_c,&
L_7&=\left(e+\frac{16}{5}\right)X
      +\left(\frac34+\frac{35}{2}h_c\right)\Delta.
\end{aligned}
$$

The absolute response at clock \(i\) is \(A+\tau_i g_q(i)-Q_q\), with the
same constant drift form \(A-Q_q\) as in Definition 38.1.

**定理 22.2（critical chart forces an original guard failure）。** Under
Definition 22.1, at least one of the two terminal pairs (w_1,w_2) has
identical fixed sources.  For that same literal pair,

$$
D_{w_j}|_V=0
$$

in all four coordinates, and therefore

$$
\operatorname{rank}[B;D_{w_j}]=\operatorname{rank}B.
$$

Consequently no guarded simultaneous sixteen-slot assignment can lie entirely
in this critical \(C=B_5=0\) chart, regardless of the free common fifth-\(J\)
response form.

**证明。** Suppose both terminal pairs are separated.  Since the critical
source set has only \(a_+,a_-\), each pair uses both values.  The \(JJJMMJJ\)
trace is \(U_c\) for either value of \(a\).  Equality of its two actual seventh
\(J\) responses gives

$$
\bigl(U_c\alpha _7-1\bigr)(Q_{w_1,0}-Q_{w_1,1})=0.
$$

Now \(U_c(1-25h_c)=1\), hence

$$
U_c\alpha _7-1=-80U_ch_c\ne0,
$$

so the two whole forms \(Q_{w_1,0},Q_{w_1,1}\) coincide.  Their sixth traces
are \(1+t_c+a_+\) and \(1+t_c+a_-\); subtracting the two sixth responses of
this same pair gives \(g_{w_1}(6)=0\).  Its common sixth response is therefore
\(A-Q_*\), for their common form \(Q_*\).

The two \(JJJMMJM\) slots share the literal sixth prefix \(JJJMMJ\), so their
sixth response is also \(A-Q_*\).  For either critical source, with

$$
\tau _6(a)=1+t_c+a>0,
$$

the equality to this response is

$$
\bigl(\tau _6(a)\alpha _6-1\bigr)(Q_q-Q_*)=0.
$$

Because \(h_c>1/56\), \(\alpha _6<0\), and the coefficient is strictly
negative.  Thus both \(JJJMMJM\) forms also equal \(Q_*\).  If this second
pair is separated, its seventh-\(M\) traces \(2R_c+t_c-a_+\) and
\(2R_c+t_c-a_-\) differ, so its own seventh-response equality forces
\(g_{w_2}(7)=0\).

The two zero forms cannot coexist.  Direct expansion gives

$$
\alpha _6g_{w_2}(7)-\alpha _7g_{w_2}(6)
=\frac{44-5e+(1505e-1484)h_c}{20}X
 +\frac{5h_c(37-112h_c)}4\,\Delta.
$$

The coefficient of \(\Delta\) is strictly positive because
\(0<h_c<1/25\).  Since \(X,\Delta\) are independent on the original \(V\),
the right side is not the zero form, contradicting the two zero equations.
Therefore at least one of \(w_1,w_2\) has identical sources.  Lemma 36.2
then applies to that same fixed pair and yields \(D_{w_j}|_V=0\) in all four
coordinates, proving the rank statement.  No equality from a different
terminal pair, gain sample, carrier coordinate, or selected subspace was used.
∎

**定义 22.3（本节边界）。** The theorem is an ordinary exact algebraic
obstruction, not a Lean verification or a literature novelty claim.  It keeps
signed nonzero gains of degree at most three, degree drops and repeated roots,
constant drift, absolute clocks \(0,\ldots,7\), billed initial and atomic
readings, both actions, early stopping, strict source positivity, both
diagonal sheets, the original \(V=\ker B\), and the full four-coordinate
same-source guard.  It does not exclude a compatible critical parent whose
descendant slots mix critical and regular sources; that mixed incidence still
requires the complete Definition 38.1 equations and all original guards.
The earlier \(JJJJ\) sibling, the remaining finite-pool parents, the complete
fixed-\(256\)-source/full-\(G\)/full-\(D\) problem, and the global
eight-versus-nine and nine-read questions remain open.
