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
