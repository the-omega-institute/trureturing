# 全偶数阶的原标签标记圆锥测试

## 68. 原域测试空间与等权商

**定义 68.1（固定原域模型）。** 设 $F$ 是特征零域，$D/F$ 是可分扩张，
$[D:F]=2m$，其中 $m\ge2$。取正规闭包 $L/F$，并固定原嵌入集合
$\Sigma=\operatorname{Hom}_F(D,L)$。分裂同构
$$
D\otimes_F L\simeq L^\Sigma
$$
只用于证明；$\Sigma$ 的每个元素始终是原标签，不对其另取置换商。
Galois 按 $\tau:\sigma\mapsto\tau\sigma$ 作用于这些标签，并不逐个固定它们。对
$r\in D$，写 $r_\sigma=\sigma(r)$。沿用
[《Catalan 系数空间》](AURIC_R5_026_CATALAN_SUPPORT_CERTIFICATES.md) §§51–54
的内在空间 $H_D$：它由窗口行列式生成，且在分裂坐标中
$$
H_D\otimes_F L
=\left\{Q\in L[x_\sigma:\sigma\in\Sigma]:
\begin{array}{l}
Q\text{ 齐次且 }\deg_{x_\sigma}Q\le1,\\
\deg Q=m,\quad \sum_{\sigma\in\Sigma}\partial_{x_\sigma}Q=0
\end{array}\right\}.
\tag{68.1}
$$
若 $M$ 是 $\Sigma$ 上的有向完美匹配，置
$$
\Delta_M(p)=\prod_{(\sigma,\tau)\in M}[p_\sigma,p_\tau],
\qquad [u,v]=U_uV_v-U_vV_u.
\tag{68.2}
$$
反向一条边只改变符号。所有 $\Delta_M$ 张成 $H_D\otimes_F L$；这正是
原标签版本的匹配生成描述。

用已有的多项式实现 $H_D\subset\operatorname{Sym}^m_F(D^\vee)$ 定义乘法映射及其像：
$$
\mu_D:\operatorname{Sym}_F(H_D)\longrightarrow\operatorname{Sym}_F(D^\vee),
\qquad A_D=\operatorname{im}\mu_D.
$$
在像上重新分次，令 $H_D$ 的次数为 $1$，即
$$
(A_D)_n=\operatorname{im}\!\left(
\operatorname{Sym}^n_F(H_D)\longrightarrow\operatorname{Sym}^{mn}_F(D^\vee)
\right).
$$
其齐次关系理想与射影簇为
$$
\begin{aligned}
J_D&=\ker\mu_D
=\bigoplus_{n\ge0}\ker\!\left(
\operatorname{Sym}^n_F(H_D)\longrightarrow\operatorname{Sym}^{mn}_F(D^\vee)
\right),\\
A_D&\simeq\operatorname{Sym}_F(H_D)/J_D,\qquad
X_D=\operatorname{Proj}A_D\subset\mathbb P(H_D^\vee).
\end{aligned}
\tag{68.3}
$$
因此关系指生成多项式之间的恒等式。在 $L$ 上，对 $P\in(A_D)_n\otimes_F L$
按每个原标签齐次化：
$$
\widehat P((U_\sigma,V_\sigma)_\sigma)
=\left(\prod_{\sigma\in\Sigma}V_\sigma^n\right)
P((U_\sigma/V_\sigma)_\sigma).
$$
每个变量在 $P$ 中的次数至多 $n$，故这是多重次数 $(n,\ldots,n)$ 的多项式。
此操作保持乘法，且以 $V_\sigma=1$ 为逆；一次匹配恰变为 (68.2) 的括号乘积。
Kempe 生成定理因而将此分次像识别为
$$
A_D\otimes_F L\simeq
\bigoplus_{n\ge0}L[U_\sigma,V_\sigma:\sigma\in\Sigma]_{(n,\ldots,n)}^{\operatorname{SL}_2}.
$$
这是等权 $\operatorname{PGL}_2$ 商的环：$2m$ 为偶数，使中央 $-I$ 在等权线性化上
作用平凡；用 $\operatorname{GL}_2$ 表示时采用行列式的 $-mn$ 次扭转。
对 $r\in D$，令 $\operatorname{ev}_r(Q)=Q((r_\sigma)_\sigma)$；当该泛函非零时，
记
$$
e(r)=[\operatorname{ev}_r|_{H_D}]\in\mathbb P(H_D^\vee)(F).
\tag{68.4}
$$

**定理 68.2（全偶数阶的原标签商与实际像闭包）。** 代数 $A_D$ 是等权线性化的
$(\mathbb P^1)^{2m}//\operatorname{PGL}_2$ 的原标签 $F$-形式的齐次坐标环。因此
$$
\dim X_D=2m-3,
\tag{68.5}
$$
且 $X_D$ 的几何点是带原标签的等权商点。实际像 $e(D\setminus F)$ 在 $X_D$ 中
Zariski 稠密，因而
$$
X_D=\overline{e(D\setminus F)}.
\tag{68.6}
$$

**证明。** 在 $L$ 上，(68.1) 的匹配单项式是等权商的一次坐标。Kempe 的生成定理
（HMSV，§2.3 的 Theorem 2.1；匹配方向约定见其 §1.2 与 §2）说明这些一次坐标生成
等权不变量环；定义 68.1 的齐次化识别也保持全部关系。Galois 同时作用于系数，并把
标签 $\sigma$ 及有向边 $(\sigma,\sigma')$ 送到 $\tau\sigma$ 及
$(\tau\sigma,\tau\sigma')$，故生成环带着这个原标签半线性作用下降为 $A_D$。
等权商的稳定开集有维数 $2m-3$，故 (68.5) 成立；这也可
由三维的 $\operatorname{PGL}_2$ 轨道维数从 $2m$ 个射影点的维数中扣除得到。

基变换到 $L$ 后，$D\otimes_F L=L^\Sigma$。因此 $r$ 的分裂坐标遍历一个
$(2m)$-维仿射 $F$-空间的稠密集合；特征零使 $F$-有理点在该仿射空间中稠密。
商映射的像仍稠密，而删去 $D$ 中的标量只删去一个真线性子空间。故 (68.6) 成立。
$\square$

**引理 68.3（原标签匹配补全）。** 把 $2m$ 个标签分成 $k$ 个等大小块，每块大小
$d=2m/k$。若 $k\ge2$，则任取来自不同块的两个标签，都能补成一个不含同块边的
有向完美匹配。若取自四个不同块的四个标签，且 $k\ge4$，余下标签也能补成这样的
匹配；$m=2$ 时余下集合为空，空匹配就是补全。

**证明。** 完全多部图有完美匹配当且仅当最大部大小不超过顶点总数的一半。删去两个
不同块的标签后，最大部大小至多 $m-1$，总数为 $2m-2$；删去四个不同块的标签后，
总数为 $2m-4$，且 $d\le m-2$（$m=2$ 时总数为零）。Hall 判据给出所述匹配；任意
定向只改变一个非零符号。$\square$

## 69. 评价、原域轨道与稳定性

**定理 69.1（范数协变式）。** 对
$g=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\operatorname{GL}_2(F)$，
$\det g\ne0$，以及 $r\in D$，若 $cr+d\ne0$，则对所有 $Q\in H_D$ 有
$$
N_{D/F}(cr+d)\,Q\!\left(\frac{ar+b}{cr+d}\right)
   =\det(g)^m Q(r).
\tag{69.1}
$$

**证明。** 在原坐标中令 $A=M_{cr+d}$。乘法交换性给出
$$
A M_{(ar+b)/(cr+d)}=aM_r+bI,
\qquad \det A=N_{D/F}(cr+d).
$$
对窗口帧 $B$，有
$$
A[\,B,M_{g(r)}B\,]
=[\,B,M_rB\,]
\begin{pmatrix}dI_m&bI_m\\cI_m&aI_m\end{pmatrix}.
$$
右侧分块矩阵的行列式为 $(ad-bc)^m$，故行列式生成元满足 (69.1)。再用
定义中的 $F$-线性张成关系，结论对全部 $H_D$ 成立。$\square$

**定理 69.2（非零评价与实际轨道）。** 对 $r\in D$，
$$
\operatorname{ev}_r|_{H_D}=0\quad\Longleftrightarrow\quad r\in F.
\tag{69.2}
$$
若 $r,s\in D\setminus F$，则
$$
e(r)=e(s)\quad\Longleftrightarrow\quad
s=\frac{ar+b}{cr+d}
\quad\text{对某个 }g\in\operatorname{PGL}_2(F).
\tag{69.3}
$$
若 $k=[F(r):F]\ge3$，满足 (69.3) 的 $g$ 唯一；当 $k=2$ 时不作唯一性断言。

**证明。** 设 $k=[F(r):F]$，则 $r_\sigma$ 分成 $k$ 个等值块，每块大小
$d=2m/k$。若 $r\in F$，所有匹配因子均为零。若 $r\notin F$，则 $k\ge2$，
由引理 68.3 取一个避开同块边的匹配，得到非零的 $\Delta_M(r)$，证明 (69.2)。

若 $s=g(r)$，(69.1) 给出相同比例的全部匹配评价，故 $e(s)=e(r)$。反之，
匹配取值的零模式恢复原标签的等值分块：对任意 $\sigma,\tau$，有
$$
r_\sigma=r_\tau
\Longleftrightarrow
\text{每个含边 }(\sigma,\tau)\text{ 的匹配在 }r\text{ 上为零}.
\tag{69.4}
$$
正向显然；反向由引理 68.3 补成非零匹配。于是 $r,s$ 有相同的带标签分块。

当 $k=2$ 时，两块分别给出同一个二次子域的两个嵌入；两个生成元在该二次域中
由一个 $F$-仿射分式线性变换相连，故存在 $g\in\operatorname{PGL}_2(F)$，但两点
不能唯一决定 $g$。当 $k\ge3$ 时，先取三个不同块的代表；唯一的射影变换把它们
逐一送到 $s$ 的对应代表。若还有第四块，取四个不同块的标签。引理 68.3 提供
同一个剩余匹配，故两种交叉比
$$
\frac{[p_a,p_b][p_c,p_e]}{[p_a,p_c][p_b,p_e]}
\tag{69.5}
$$
由两条匹配评价之比读出；$m=2$ 时剩余匹配是空匹配，(69.5) 仍成立。固定前三点后，
交叉比唯一确定第四点，于是该射影变换送对全部块，再由分块送对全部原标签。
Galois 共轭与它在同一组至少三个不同点上作用相同，故它的系数比属于 $F$；于是
$g\in\operatorname{PGL}_2(F)$。$\square$

**定理 69.3（实际点的稳定分层）。** 等权商中，某点严格半稳定当且仅当某个位置
恰有 $m$ 个标签；稳定当且仅当每个位置至多 $m-1$ 个标签。因而对实际 $r$：
$$
k=2\Longleftrightarrow e(r)\text{ 严格半稳定},\qquad
k\ge3\Longleftrightarrow e(r)\text{ 稳定}.
\tag{69.6}
$$

**证明。** 这是等权 $\operatorname{PGL}_2$ 线性化的 Hilbert–Mumford 判据；同一判据
见 HMSV §2 及 Dolgachev–Ortland 的经典不变量论。实际配置的最大重复数是 $d=2m/k$。
当 $k=2$ 时 $d=m$，当 $k\ge3$ 时 $d<m$。$\square$

## 70. 稳定标记圆锥、边界与精确实际像

**定理 70.1（稳定点的唯一标记圆锥）。** 对每个稳定有理点 $y\in X_D^{\mathrm{st}}(F)$，
存在一个光滑射影 $F$-圆锥曲线 $Q_y$ 与标记态射
$$
\iota_y:\operatorname{Spec}D\longrightarrow Q_y,
\tag{70.1}
$$
使其几何标记的等权商点为 $y$。带原 $\operatorname{Spec}D$ 标记的同构意义下，
$(Q_y,\iota_y)$ 唯一。标记态射唯一分解为
$$
\operatorname{Spec}D\longrightarrow\operatorname{Spec}K
\hookrightarrow Q_y,
\qquad K\subset D,\quad [K:F]=k\ge3,
\tag{70.2}
$$
其中每个几何标记值重复 $[D:K]=2m/k$ 次；只有 $K=D$ 时标记才是闭嵌入。

**证明。** 先在 $\overline F$ 上取 $y$ 的稳定代表 $p=(p_\sigma)_\sigma$，再取包含
$L$ 及全部代表坐标的有限 Galois 扩张 $E/F$，记 $G_E=\operatorname{Gal}(E/F)$。
对 $\tau\in G_E$，原标签的作用是
$(\tau\star p)_\sigma=\tau(p_{\tau^{-1}\sigma})$。因 $y$ 是 $F$-有理点，
$p$ 与 $\tau\star p$ 属于同一稳定商纤维。稳定商是几何商，故此纤维是一个
$\operatorname{PGL}_2(\overline F)$ 轨道。稳定性又保证至少三个不同标记值，
所以存在唯一的标记比较变换；三个 $E$-点确定它，故它属于
$\operatorname{PGL}_2(E)$。写成 $g_\tau$，有
$$
g_\tau(\tau p_\sigma)=p_{\tau\sigma}.
\tag{70.3}
$$
对 $\tau,\upsilon\in G_E$，变换 $g_\tau\tau(g_\upsilon)$ 把
$\tau\upsilon(p_\sigma)$ 送到 $p_{\tau\upsilon\sigma}$，故三点唯一性给出
$g_{\tau\upsilon}=g_\tau\,\tau(g_\upsilon)$；这是带标记 Weil 下降
的余循环条件（Sijsling–Voight, Theorem 2.1.1 及其平凡标记自同构推论）。下面给出
三维的显式下降。

令 $V$ 为对称 $2\times2$ 矩阵的三维 $E$-空间，并定义
$$
\rho([A])(S)=\frac{ASA^{\mathsf t}}{\det A},
\qquad \det(\rho([A])S)=\det S.
\tag{70.4}
$$
令半线性作用 $T_\tau(S)=\rho(g_\tau)(\tau S)$，由 (70.3) 它满足群作用律。固定空间
$W=V^{G_E}$ 是三维 $F$-空间，且 $W\otimes_F E\simeq V$。这可由
迹平均和不同域自同构的线性独立性直接证明。于是
$$
Q_y=\{[S]\in\mathbb P(W):\det S=0\}
\tag{70.5}
$$
是光滑 $F$-圆锥曲线；秩一矩阵的 Veronese 参数化把其基变换到 $E$ 后识别为
$\mathbb P^1_E$。式 (70.3) 使 $\operatorname{Spec}(D\otimes_F E)$ 上的原标签等变，
故它们下降为 (70.1)。至此才由此标记得到 $Q_y(D)\ne\varnothing$；从该 $D$-点作
直线投影，知 $(Q_y)_D\simeq\mathbb P^1_D$，再沿原嵌入 $D\hookrightarrow L$ 扩域，
得到 $(Q_y)_L\simeq\mathbb P^1_L$。因而最终确可在 $L$ 上分裂，但初始代表的选择
不预设此结论。

稳定性给出至少三个不同几何标记值。若两个带标记圆锥给出同一 $y$，分裂后由前三个
标记确定唯一射影同构；其所有 Galois 共轭相同，故同构下降到 $F$，且因三点而唯一。
标记像是一个闭点 $P$，其剩余域 $K=\kappa(P)$ 嵌入 $D$；等值块大小说明
$[D:K]=2m/k$，并由稳定性得 $k\ge3$。$\square$

**定理 70.2（稳定部分的精确提升判据）。** 对稳定 $y\in X_D^{\mathrm{st}}(F)$，
$$
y=e(r)\text{ 对某个 }r\in D\setminus F
\Longleftrightarrow Q_y\simeq_F\mathbb P^1_F
\Longleftrightarrow Q_y(F)\ne\varnothing.
\tag{70.6}
$$
若 $k=[K:F]$ 为奇数，则 $Q_y$ 必分裂。

**证明。** 若 $y=e(r)$，则 $[r:1]$ 给出标记的 $F$-参数化，唯一性迫使
$Q_y\simeq_F\mathbb P^1$。反之，若 $Q_y(F)\ne\varnothing$，从该点作直线投影得
$Q_y\simeq_F\mathbb P^1$。标记闭点次数 $k\ge3$，故它不是无穷远的 $F$-点，写成
$[r:1]$，其中 $r\in D\setminus F$，于是 $y=e(r)$。

最后写 $k=2u+1$。令 $H$ 为一个 $F$-直线截面，$\deg H=2$，令 $P$ 为标记像闭点。
除子 $E=P-uH$ 定义在 $F$ 上且 $\deg E=1$。圆锥曲线属为零，Riemann–Roch 给出
$$
h^0(E)-h^0(K_{Q_y}-E)=2,
$$
而 $\deg(K_{Q_y}-E)=-3$，所以 $h^0(E)>0$。一个非零 $F$-截面给出次数为一的
有效 $F$-除子，即 $F$-有理点。$\square$

**定义 70.3（严格半稳定边界）。** 令 $B_D\subset X_D$ 为严格半稳定点的边界。
几何上它由无序的原标签分割
$$
\{A,A^c\},\qquad |A|=|A^c|=m,
\tag{70.7}
$$
给出：$A$ 中标签取 $0$，$A^c$ 中标签取 $\infty$。这里的边界点是无序分割的
商点；不把全部边界点称为节点。

**定理 70.4（边界的原域算术）。** 有自然双射
$$
B_D(F)\;\longleftrightarrow\;
\{K:F\subset K\subset D, [K:F]=2\}.
\tag{70.8}
$$
每个 $B_D(F)$ 点都属于实际像 $e(D\setminus F)$。

**证明。** 令 $G=\operatorname{Gal}(L/F)$，取原嵌入 $\sigma_0:D\hookrightarrow L$，
以此把 $D$ 视为 $L$ 的子域，并令 $H=\operatorname{Stab}_G(\sigma_0)$，故 $L^H=D$。
若无序分割在 $G$ 下不变，传递性使两块上的作用给出满射 $G\twoheadrightarrow S_2$，
记其核为 $N$。含 $\sigma_0$ 的块必须被 $H$ 保持；只有两块，所以 $H$ 也保持另一块。
因此正确的包含及其固定域映射是
$$
H\subset N,\qquad K=L^N\hookrightarrow L^H=D,\qquad [K:F]=2.
$$
反之，原二次子域 $K\subset D$ 的限制映射
$$
\Sigma\longrightarrow\operatorname{Hom}_F(K,L),\qquad
\sigma\longmapsto\sigma|_K
$$
把 $\Sigma$ 分成两个大小为 $m$ 的块，给出不变无序分割。这两种构造互逆：
在 $\Sigma\simeq G/H$ 中，含 $\sigma_0$ 的块正是 $N/H$，故由 $K$ 的限制映射恢复。
任取 $r\in K\setminus F$，其原标签正好落在这两个块上，所以该边界点等于 $e(r)$。
$\square$

边界上没有稳定点所用的三点唯一性。例如取 $D/\mathbb Q$ 含有
$\mathbb Q(i)$，并令
$$
Q_0:x^2+y^2+z^2=0,\qquad [i:1:0]\in Q_0(\mathbb Q(i)).
\tag{70.9}
$$
这个二次闭点给出一个实际边界标签，且同一边界点也由分裂直线上的实际元素
$r=i$ 给出；但 $Q_0(\mathbb Q)=\varnothing$。因此“任意边界圆锥分裂当且仅当
实际提升”是错误的；边界点没有唯一的标记圆锥。

**推论 70.5（完整实际像公式）。** 记 $I_D=e(D\setminus F)$，则
$$
I_D
=B_D(F)\;\sqcup\;
\{y\in X_D^{\mathrm{st}}(F):Q_y(F)\ne\varnothing\}.
\tag{70.10}
$$
这里 $B_D(F)$ 与稳定部分不交；稳定部分中的圆锥是定理 70.1 的唯一对象。

## 71. 每个 $m\ge2$ 的非提升族与白话桥接

**定理 71.1（全偶数阶的显式严格非提升族）。** 对每个 $m\ge2$，令
$$
t=2^{1/m}>0,\qquad K=\mathbb Q(t),\qquad D=K(i),\qquad
Q_0:x^2+y^2+z^2=0,
\tag{71.1}
$$
并取
$$
q=[i(1+t^2):1-t^2:2t]\in Q_0(D).
\tag{71.2}
$$
则 $[D:\mathbb Q]=2m$，$q$ 的剩余域为 $D$，其 $2m$ 个原标签两两不同；它们给出
一个稳定点 $y\in X_D^{\mathrm{st}}(\mathbb Q)$，但
$$
y\notin e(D\setminus\mathbb Q).
\tag{71.3}
$$

**证明。** $X^m-2$ 在 $2$ 处 Eisenstein，故 $[K:\mathbb Q]=m$；$K\subset\mathbb R$，
所以 $i\notin K$ 且 $[D:\mathbb Q]=2m$。代入 (71.2) 得
$$
-(1+t^2)^2+(1-t^2)^2+4t^2=0.
$$
在 $z\ne0$ 的图中置
$$
A=\frac{x}{z}=\frac{i(t+t^{-1})}{2},\qquad
B=\frac{y}{z}=\frac{t^{-1}-t}{2}.
\tag{71.4}
$$
若 $a^m=b^m=2$ 且 $B(a)=B(b)$，则
$$
(b-a)\left(1+\frac1{ab}\right)=0.
$$
若 $ab=-1$，则 $4=(ab)^m=(-1)^m$，矛盾；故 $B$ 在所有共轭上取不同值，
从而 $\mathbb Q(B)=K$。再由 (71.4) 恢复 $i$，所以 $\mathbb Q(A,B)=D$，证明剩余域
与标签互异性。因重复数为一，定理 69.3 给出稳定性。

在 $D/\mathbb Q$ 的正规闭包 $L$ 中，用参数化
$$
\phi_i(z)=[i(1+z^2):1-z^2:2z],\qquad
\phi_i(-1/a)=[-i(1+a^2):1-a^2:2a]
$$
识别 $(Q_0)_L\simeq\mathbb P^1_L$。原标签的分裂参数因而为
$$
z_\sigma=
\begin{cases}
\sigma(t),&\sigma(i)=i,\\
-\sigma(t)^{-1},&\sigma(i)=-i.
\end{cases}
\tag{71.5}
$$
令 $h(z)=-1/z$。对 $\tau\in\operatorname{Gal}(L/\mathbb Q)$，精确的标签协变关系是
$$
\tau(z_\sigma)=
\begin{cases}
z_{\tau\sigma},&\tau(i)=i,\\
h(z_{\tau\sigma}),&\tau(i)=-i.
\end{cases}
$$
也就是说，$(\tau\star z)_\sigma=\tau(z_{\tau^{-1}\sigma})$ 分别等于 $z_\sigma$ 或
$h(z_\sigma)$；这不声称各个共轭值被逐点固定。每个 $K$ 的嵌入分别延拓为
$i\mapsto i$ 与 $i\mapsto-i$ 的两个 $D$-嵌入，故全部 $m$ 个负号都参与乘积：
$$
\prod_{\sigma\in\Sigma}z_\sigma=(-1)^m.
\tag{71.6}
$$
这里的 $z$ 只是分裂元组，不假定它来自某个 $r\in D$。直接用齐次匹配恒等式：
对 $A_h=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$，有 $\det A_h=1$ 且
$A_h(z_\sigma,1)^{\mathsf t}=(-1,z_\sigma)^{\mathsf t}
=z_\sigma(h(z_\sigma),1)^{\mathsf t}$。因每个标签在匹配中恰出现一次，
$$
\left(\prod_{\sigma\in\Sigma}z_\sigma\right)\Delta_M(hz)
=\det(A_h)^m\Delta_M(z)=\Delta_M(z).
$$
由匹配张成及 (71.6)，对全部 $P\in H_D\otimes_{\mathbb Q}L$ 有
$P(hz)=(-1)^mP(z)$。令 $w=\operatorname{ev}_z|_{H_D\otimes_{\mathbb Q}L}$；
对偶空间上的原标签半线性作用为
$$
(\tau w)(P)=\tau\!\left(w(\tau^{-1}P)\right)
=\operatorname{ev}_{\tau\star z}(P),\qquad
\tau w=
\begin{cases}
w,&\tau(i)=i,\\
(-1)^m w,&\tau(i)=-i.
\end{cases}
$$
因此
$$
w_{\mathbb Q}=\begin{cases}w,&m\text{ 偶},\\ iw,&m\text{ 奇},\end{cases}
\tag{71.7}
$$
是非零的 $\mathbb Q$-泛函：当 $m$ 为奇数且 $\tau(i)=-i$ 时，
$\tau(iw)=(-i)(-w)=iw$；其余情形直接不变。统一写成 $i^m w$ 只相差非零有理倍数。
其射影线就是 $y$，对应的标记圆锥是 $(Q_0,q)$。若 $y=e(r)$，稳定点的带标签三点
唯一性会把 $Q_0$ 与 $\mathbb P^1_{\mathbb Q}$ 唯一地同构，因而迫使
$Q_0(\mathbb Q)\ne\varnothing$。但三个有理平方和为零只能全为零，故
$Q_0(\mathbb Q)=\varnothing$，矛盾。$\square$

当 $m=1$ 时只有两个标签，点处于严格半稳定边界；两点不能固定射影坐标，且二次域
中的任意非标量元素都实现同一个实际轨道。因此该族的“稳定且不提升”结论必须从
$m\ge2$ 开始。

**命题 71.2（从二点匹配到标记圆锥的完整白话表述）。** 原元素 $r\in D$ 给出
$2m$ 个带固定标签的共轭点。匹配把这些标签两两相连；匹配为零的模式准确记录
哪些原标签重合，而剩下的共同匹配之比给出交叉比。两个不同位置只确定一个二次
分块，不能唯一确定坐标；三个不同位置确定唯一射影坐标变换；更多位置由交叉比
逐一确定。于是稳定有理点的全部标签关系下降为一个三维对称矩阵空间中的二次型
$\det S$，其零轨迹就是唯一的标记圆锥 $Q_y$。圆锥有 $F$-点时可在 $F$ 上选取
坐标，标记便还原成一个实际的 $r\in D$；无 $F$-点时，匹配关系仍可给出原域有理
测试，却没有实际元素能够承载这把坐标尺。重复标签只表示标记态射经过某个
$K\subset D$；奇数次闭点由次数一除子迫使圆锥分裂，二次边界则必须单独按
(70.8) 处理。

**证明。** 引理 68.3 与定理 69.2 的式 (69.4)–(69.5) 分别给出重合关系、共同剩余
匹配及交叉比，连同三点唯一性证明坐标变换的断言；二次情形只恢复分块。
定理 70.1 的式 (70.3)–(70.5) 将原标签半线性作用下降到三维空间与其行列式圆锥，
并由式 (70.2) 说明重复标签恰对应实际子域。定理 70.2 把圆锥上的 $F$-坐标精确
还原成 $r\in D$，同时证明奇数次闭点的断言；定理 70.4 与推论 70.5 分开处理二次
边界并给出完整实际像。定理 71.1 则证明无 $F$-点的稳定障碍在每个所述次数确实发生。
这些步骤共同证明命题，未添加可独立选择的标签或坐标。$\square$

上述分类只处理原标签测试像、稳定性、边界和实际提升。系数线的识别、窗口的恢复、
以及最优的认证证书发现仍是独立问题；它们不由 (70.10) 自动推出。

**文献。** Kempe 生成与有向匹配的现代可读出处是 HMSV，
[Theorem 2.1, §2.3](https://math.stanford.edu/~vakil/files/hmsv2-121109.pdf)，
并参见同文 §1.2、§2；等权稳定性与不变量商的经典出处为
[Dolgachev–Ortland, Astérisque 165 (1988)](https://www.numdam.org/item/AST_1988__165__1_0.pdf)。
带标记 Weil 下降可参见 Sijsling–Voight，
[Theorem 2.1.1](https://arxiv.org/pdf/1504.02814v3)。

## 追加锚（本行以下为增补区）
