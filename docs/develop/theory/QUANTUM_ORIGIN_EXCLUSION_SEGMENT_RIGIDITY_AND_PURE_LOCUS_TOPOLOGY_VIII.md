# QUANTUM ORIGIN: EXCLUSION SEGMENT RIGIDITY AND PURE LOCUS TOPOLOGY VIII

未另注卷名的103—106章及103.x—106.x条目均指[有限纯点与面障碍第七卷][Q107VII]；
107章及107.x条目属于本卷，式号以VIII107为前缀。
[全有限层级VII][Q107Hierarchy]的102、103章属于另一理论卷，其编号须带该卷名引用。

## 107. 全部完整排除球为线段时的原域三角形刚性

### 107.1 原全效应域与全线段条件

**定义 107.1（完整排除线段的全称量词）。** 采用第七卷103.1、104.1及105.1的同一个
非零有限维实空间 $V$、闭尖生成凸锥 $C$、在 $C\setminus\{0\}$ 上严格正的
原泛函 $u$、整个紧基 $K=C\cap\{u=1\}$、全部原纯点 $P=\operatorname{ext}K$，
以及整个原效应区间 $\mathcal E=[0,u]_{C^*}$。这里
$C^*=\{f\in V^*:f(c)\ge0\ (c\in C)\}$，$B^d$ 指整个闭欧氏单位球。特别地，

$$
\begin{gathered}
F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in F_p}f(x),\\
p\perp x\ \Longleftrightarrow\
\exists f\in F_p:\ f(x)=0,\qquad
D_p=\{x\in K:T_p(x)=0\}.
\end{gathered}
\tag{VIII107.1}
$$

这里 $p\in P$，但 $x$ 遍历全部原 $K$，包括全部混态；
$F_p$ 的最小化遍历全部原确认效应。$H(p,q)$ 仍是包含 $p,q$ 的整个原最小面。
保留弱入口

$$
\begin{aligned}
\mathsf W&=\mathrm{EB}_{\ge1}+\mathrm{Pair}_{\perp},\\
\mathrm{EB}_{\ge1}&:\quad
 \forall p\in P\ \exists d_p\in\mathbb N,\quad d_p\ge1:
 D_p\simeq_{\rm aff}B^{d_p},\\
\mathrm{Pair}_{\perp}&:\quad
 p,q\in P,\ p\perp q\ \Longrightarrow\ H(p,q)\ne K.
\end{aligned}
\tag{VIII107.2}
$$

在此域内定义附加条件

$$
\mathrm{Seg}_{\rm all}:\quad
\forall p\in P,\quad D_p\text{ 本身为非退化闭线段}.
\tag{VIII107.3}
$$

它要求每一个完整 $D_p$ 的仿射维数为一；只选出其中一条直径、只检查纯目标
$P\cap D_p$、或只检查部分效应，均不是此条件。不预设 $P$ 有限、可数或闭，
也不输入全Pair、$S$、$\mathrm G$、$\mathrm{PL}_3$、Jordan或ROG表示、对称群、
实际菜单、事件或时钟。

### 107.2 全线段刚性及整个原锥的识别

**定理 107.2（无纯点基数前件的经典三角形）。** 在定义107.1的原域中，
$\mathsf W+\mathrm{Seg}_{\rm all}$ 当且仅当存在三个不同原纯点 $p_1,p_2,p_3$，
使

$$
\begin{gathered}
P=\{p_1,p_2,p_3\},\qquad
K=\operatorname{conv}\{p_1,p_2,p_3\},\\
\Phi:\mathbb R^3\overset{\sim}{\longrightarrow}V,\qquad
\Phi(t)=\sum_{i=1}^3t_i p_i,\qquad
\Phi(\mathbb R_+^3)=C,\qquad u(\Phi(t))=\sum_i t_i.
\end{gathered}
\tag{VIII107.4}
$$

三点仿射独立，且全部原效应准确为

$$
\mathcal E=\{f_b:b\in[0,1]^3\},\qquad
f_b(\Phi(t))=\sum_i b_i t_i\quad(t\in\mathbb R^3).
\tag{VIII107.5}
$$

证明。先直接使用第七卷103.2、104.2—104.4及104.6的弱入口后果：
每个 $D_p$ 是非点暴露极大真面；全部非空原真面只有纯单点和整个 $D_p$；
不同非点真面至多交于一个原纯点；$p\mapsto D_p$ 双射；$P$ 紧。
任意原正交纯对有唯一第三纯点，三点两两原正交，且有同一个原空间上的效应

$$
a_1,a_2,a_3\in\mathcal E,\qquad
a_i(p_j)=\delta_{ij},\qquad a_1+a_2+a_3=u.
\tag{VIII107.6}
$$

每个原纯点都进入这样的三元组。这些结论在原 $\mathsf W$ 内成立，
不调用103.3—103.8中以前件全Pair或完整 $S$ 承担的重构。

取任意 $p\in P$，写整个 $D_p=[q,r]$，$q\ne r$。
因为 $D_p$ 是原面，其端点 $q,r$ 是原纯点，且
$P\cap D_p=\{q,r\}$。104.2使这两个对径端点原正交，
所以 $(p,q,r)$ 是(VIII107.6)的三元组。$D_q$ 包含两个不同纯点 $p,r$，
而一条线段恰有两个极点，故

$$
D_p=[q,r],\qquad D_q=[p,r],\qquad D_r=[p,q].
\tag{VIII107.7}
$$

因此每个纯点恰有两个原正交纯邻点，恰属于一个无序正交三元组。
对任何这样的三元组，(VIII107.6)的三张线性效应证明三点线性独立，
因而仿射独立。置 $m=\operatorname{affdim}K$，有 $m\ge2$。
此处既没有对三元组的总数计数，也没有选定它们随纯点连续变化的标号。

现在给全部有序三元组以原有限维拓扑：

$$
\mathcal T=\{(p_1,p_2,p_3)\in P^3:
                 p_i\perp p_j\ (i\ne j)\}.
\tag{VIII107.8}
$$

$\mathcal T$ 非空且紧。确实，103.2给整个 $\mathcal E$ 紧，
而原正交关系是紧集

$$
\{(p,q,f)\in P^2\times\mathcal E:f(p)=1,\ f(q)=0\}
\tag{VIII107.9}
$$

在 $P^2$ 上的投影，故闭；104.6已给 $P$ 紧。
于是(VIII107.8)是紧Hausdorff空间 $P^3$ 的闭子集。
原 $p\not\perp p$ 保证它的每个三元组都有三个不同成员，包括全部极限三元组。
不对 $\mathcal T$ 假设连通性、局部连通性或流形结构。

令 $\Delta=\{\lambda\in\mathbb R_+^3:\sum_i\lambda_i=1\}$，
$\partial\Delta=\{\lambda\in\Delta:\lambda_1\lambda_2\lambda_3=0\}$。
这是闭三角形的整个边界，同胚于圆周。定义紧Hausdorff空间
$Y=\mathcal T\times\partial\Delta$ 及连续映射

$$
b:Y\longrightarrow\partial K,\qquad
b((p_1,p_2,p_3),\lambda)=\sum_i\lambda_i p_i,
\tag{VIII107.10}
$$

其中 $\partial K$ 始终指在 $\operatorname{aff}K$ 内的相对边界。
因为每条对边都是(VIII107.7)的一张完整排除真面，像确在 $\partial K$ 内。
反向，对任意非纯 $x\in\partial K$，取经过它的支撑真面；
真面穷尽使它恰为某张 $D_p$，其两端及 $p$ 给 $x$ 的边上表示。
若 $x$ 纯，取含它的唯一无序三元组即得顶点表示。因此 $b$ 满射。

还须确定全部纤维，而非只确定一般边内点的表示。
若 $x$ 纯，任何(VIII107.10)表示都只有一个正系数，
其对应顶点必为 $x$；其无序三元组由 $x$ 唯一确定。
若 $x$ 非纯，表示恰有两个正系数，故 $x$ 位于某张排除线段的相对内部。
两张不同非点真面不能共有这个非纯点，所以该完整线段唯一。
其两个端点唯一，$p\mapsto D_p$ 的单射又使第三顶点唯一。
最后，固定三元组的一个次序后，仿射独立使重心坐标唯一。
所以 $b$ 的每个纤维恰由一个表示的六种同时重标号组成；
这对纯顶点和所有边内点一并成立。

具体地，置换群 $S_3$ 在 $Y$ 上作用为

$$
\sigma\cdot((p_i)_i,(\lambda_i)_i)
 =((p_{\sigma^{-1}(i)})_i,(\lambda_{\sigma^{-1}(i)})_i).
\tag{VIII107.11}
$$

此作用连续且自由，因为三元组的成员彼此不同。
上段的准确纤维结论使 $b$ 诱导连续双射
$\bar b:Y/S_3\to\partial K$。商空间紧、$\partial K$ Hausdorff，
故 $\bar b$ 是同胚。
这里 $S_3$ 只重标号辅助表示，不是原 $K$ 的仿射对称或实际可逆过程假设。

商映射 $q:Y\to Y/S_3$ 是真正的六层覆盖。为核对这一点，
固定 $y\in Y$；对每个 $\sigma\ne1$，由自由性和Hausdorff性，
取 $y,\sigma y$ 的互不相交开邻域 $U_\sigma,V_\sigma$。
有限交

$$
N=\bigcap_{\sigma\ne1}
       (U_\sigma\cap\sigma^{-1}V_\sigma)
\tag{VIII107.12}
$$

是 $y$ 的开邻域，且 $N\cap\sigma N=\varnothing$ 对全部 $\sigma\ne1$ 成立。
所以六个 $\sigma N$ 两两不交；
$q^{-1}(q(N))=\bigcup_{\sigma\in S_3}\sigma N$ 开，
而每个限制 $q|_{\sigma N}$ 都同胚到开集 $q(N)$。
最后一个断言也直接由商拓扑得到：任一开 $O\subseteq\sigma N$
的饱和集 $\bigcup_\tau\tau O$ 开，所以限制既连续又开且双射。
这正是Hatcher《Algebraic Topology》[Proposition 1.40(a)][Q107H]的条件 $(*)$；
该条不要求 $Y$ 道路连通或局部道路连通。
通过同胚 $\bar b$，(VIII107.10)也成为六层覆盖。

这个覆盖排除全部 $m\ge3$。取 $z\in\operatorname{ri}K$，
在 $L=\operatorname{aff}K-z$ 上任选欧氏范数。
从 $z$ 沿每条射线与 $K$ 的交是闭有界区间，起点附近有内球，
故每条射线恰有一个边界端点。于是径向映射

$$
\partial K\longrightarrow S^{m-1},\qquad
x\longmapsto\frac{x-z}{\|x-z\|}
\tag{VIII107.13}
$$

连续且双射；紧性使其为同胚。
若 $m\ge3$，Hatcher [Proposition 1.14][Q107H]给
$\pi_1(\partial K)=\pi_1(S^{m-1})=0$。
另一方面，固定 $t_0\in\mathcal T$ 和 $\lambda_0\in\partial\Delta$，
映射 $j(\lambda)=(t_0,\lambda)$ 有第二因子投影作左逆。
在这些基点上，$j_*$ 因而单射，而
Hatcher [Theorem 1.7][Q107H]给 $\pi_1(\partial\Delta,\lambda_0)\simeq\mathbb Z$。
覆盖映射又由Hatcher [Proposition 1.31][Q107H]诱导单射，遂得到

$$
\mathbb Z\simeq\pi_1(\partial\Delta,\lambda_0)
\ \lhook\joinrel\xrightarrow{\ j_*\ }\
\pi_1(Y,(t_0,\lambda_0))
\ \lhook\joinrel\xrightarrow{\ b_*\ }\
\pi_1(\partial K,b(t_0,\lambda_0))=0,
\tag{VIII107.14}
$$

矛盾。Proposition 1.31在选定基点使用，不要求整个覆盖空间连通。
这里也不使用需要额外连通前件的Proposition 1.40(b)、(c)。
因此 $m=2$。

由于原 $K$ 张成 $V$ 且位于 $u=1$，有 $\dim V=m+1=3$。
任选一组 $(p_1,p_2,p_3)\in\mathcal T$ 及(VIII107.6)的效应。
三点现在构成 $V$ 的线性基，三把效应是其对偶基。
对每个原 $x\in K$，因此

$$
x=\sum_i a_i(x)p_i,\qquad a_i(x)\ge0,\qquad\sum_i a_i(x)=1.
\tag{VIII107.15}
$$

故整个 $K$ 包含于这一个三角形，反向包含由原凸性成立。
三角形的全部极点正是三个顶点，从而 $P$ 恰有三个成员。
非零原锥向量均为原归一态的正倍，得到(VIII107.4)的同锥同单位识别。
线性效应在三个生成射线上的值完全决定它；
proper的充要条件恰为这三个值都在 $[0,1]$，得到(VIII107.5)。

反向，在同锥同单位的上述三角形中，全部效应由(VIII107.5)给出。
若 $f_b(p_i)=1$，则 $b_i=1$，故在任意原混态
$x=\sum_jt_jp_j$ 上 $f_b(x)\ge t_i$，且取 $b_j=\delta_{ij}$ 达到。
所以 $T_{p_i}(x)=t_i$，整个 $D_{p_i}$ 恰为相对的完整边；
不同纯点都原正交，最小面都是这三条真边。因此
$\mathrm{EB}_{\ge1}$、$\mathrm{Pair}_{\perp}$ 和 $\mathrm{Seg}_{\rm all}$ 全部成立。
这完成原域中的双向证明。
上述无基数前件的边界覆盖构造及其与原排除面的组合为 `repo-derived` 数学综合；
覆盖与基本群的成熟中间结果仅按[Hatcher所引条目][Q107H]的准确前件使用，
不据此作全球新颖性断言。证毕。

### 107.3 弱入口的纯点基数与反例所需的球维数

**推论 107.3（恰三点或连续统）。** 仅在原 $\mathsf W$ 下，

$$
|P|\in\{3,2^{\aleph_0}\}.
\tag{VIII107.16}
$$

其中 $|P|=3$ 当且仅当全部完整 $D_p$ 都为线段。
若一个 $\mathsf W$ 模型失败全Pair或覆盖律，则必存在原纯 $p$，
使其完整 $D_p$ 的仿射维数至少为二，并且 $|P|=2^{\aleph_0}$。

证明。全部 $d_p=1$ 时，107.2给经典三角形和恰三个纯点。
否则存在 $d_p\ge2$；因为 $D_p$ 是原面，
其全部极点也是原纯点，而仿射球的全部极点组成一个
$S^{d_p-1}$，基数为 $2^{\aleph_0}$。
因此 $|P|\ge2^{\aleph_0}$；原有限维实空间又给反向基数界。
这也排除厚球分支的三点情形，证明充要性。
三角形满足全Pair，且104.7的全部覆盖等价可在其前件已成立后使用。
所以失败全Pair或覆盖律的模型不在全线段分支，只能落在上述连续统分支。
本论证不从纯点紧性推断有限或可数，也不要求不同 $d_p$ 相同。证毕。

### 107.4 整个纯点轨迹不是圆周

**推论 107.4（只排除全体同胚于圆周）。** 在原 $\mathsf W$ 下，
整个 $P$ 不同胚于 $S^1$；此结论不排除 $P$ 的子集或连通分量为圆周。

证明。全线段情形的 $P$ 只有三个点，不能为圆周。
否则由107.3的证明取 $d_p\ge2$，球的极点球面中含一个嵌入圆周
$J\subseteq P\cap D_p$。由于 $p\notin D_p$，$J$ 是 $P$ 的真子集。
若存在同胚 $h:P\to S^1$，则 $h(J)$ 是圆周的一个真紧连通子集，
且它本身同胚于圆周。去掉 $S^1\setminus h(J)$ 中一点，
将 $h(J)$ 视为 $\mathbb R$ 中的紧连通集，便是一个非退化闭区间。
区间去掉一个内点会断开，而圆周去掉任一点仍连通，矛盾。
这是对整个 $P$ 的拓扑限制，没有把包含的圆周排除掉。证毕。

### 107.5 与覆盖问题及原三读数长度的准确连接

**命题 107.5（全线段分支内的全局后果与域外义务）。** 在
$\mathsf W+\mathrm{Seg}_{\rm all}$ 中，取107.2的三顶点及其对偶效应 $a_i$，
则105.1的共同中心和原最大三读数平方为

$$
\begin{gathered}
c_{p_i}=\frac{p_j+p_k}{2}\quad(\{i,j,k\}=\{1,2,3\}),\qquad
U=p_1+p_2+p_3,\qquad w=U/3,\\
p_i+2c_{p_i}=U,\qquad
Q_3(v)=\sum_{i=1}^3 a_i(v)^2\quad(v\in V).
\end{gathered}
\tag{VIII107.17}
$$

因此该分支供应 $\mathrm G$、全 $V$ 的 $\mathrm{PL}_3$、完整 $S$、全Pair和覆盖律。
这结算第七卷开放问题104.8的全线段子类，并在105.15及106.16的同域替换中
供应该载体的几何项；在不加
$\mathrm{Seg}_{\rm all}$ 的原 $\mathsf W$ 域内，
$\mathsf W\Rightarrow\mathrm G$、
$\mathsf W+\mathrm G\Rightarrow\mathrm{PL}_3$、
$\mathsf W\Rightarrow\mathrm{PL}_3$ 仍未由此证明。
存在维数至少二的完整排除球时的一般重构也未由此完成。

证明。完整排除集是三条边，球心公式和共同 $U$ 直接成立。
任一原joint三框架的纯点是全部三个顶点的某个排列；
其三张效应由三个顶点上的Kronecker读数唯一确定为同序的 $a_i$。
所以在整个原 $V$ 上，105.1的最大值始终是同一个平方和，
包括所有有符号向量和全部实尺度；它满足平行四边形律。
由107.2反向证明的 $T_{p_i}=a_i$，这些效应是原全锥序least，
且 $a_i(p_j)=a_j(p_i)$，完整 $S$ 成立。
每对不同顶点的最小面为真边，故全Pair已成立；
此后第七卷104.7及105.8的覆盖、长度与Jordan等价才可直接消费。
第七卷106.10—106.11还直接给出该分支的PAIRJET2、JET2、H2、CUB3和J1；
这是既有等价链的应用，没有在拓扑证明之前预付任何一个二阶切形条件。
没有用这些较强结论反向填补107.2的拓扑证明。

104.9已处理的有限纯点三角形结论在这里直接保留；
107.2额外排除的是不加基数限制的全线段模型，
107.3把潜在覆盖反例限制到至少一张厚球和连续统纯点。
这两项仍允许混合球维数，不把“至少一张厚球”加强成“全部球厚”，
也不把必要条件当成反例存在证明。
105.2—105.5已经在整个 $\mathsf W$ 中成立的唯一整球零尺、
全域least、共同正线性延拓和数学projectivity保持其原域，
并不是本全线段条件才取得的结论。

本命题的对象仍是单个原 $(V,C,u)$ 及其全部数学效应。
第七卷105.15、105.17及106.16、106.18的同一来源、指定复合、实际菜单、CP与仪器、
记录和合法未来、原钟及单位等合同，继续保留各自量词。
107.2不供应指定复合层级或实际事件，也不由辅助圆周、
置换或静态坐标制造物理时间。
[全有限层级VII][Q107Hierarchy]的102.11使用其全有限强分块域、原 $S_3$
及B1—B3；该层级卷103.9的另一条路线使用同一层级域、原 $S_2+\mathsf F$
及该层级卷103.1三项具名低二份供应。本分支只供应同一单载体的 $S_1$，
不自动供应全部指定复合、这些较高份比较或共同基三腿资源。
已有单系统、原生过程及全有限层级结果按各自原前提使用，
不能将本分支的三结果结构升格为三副本比较或实际事件饱和。证毕。

[Q107VII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md
[Q107Hierarchy]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md
[Q107H]: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf "Allen Hatcher, Algebraic Topology, Theorem 1.7, Propositions 1.14, 1.31 and 1.40(a); the disjoint-translate condition (*) for covering space actions."

## 追加锚（本行以下为增补区）

## 108. 原排除球的切方向互斥、三框架维数律与五维分解

### 108.1 同一原域中的球与剩余线性空间

**定义 108.1（原域、球范数与投影记号）。** 始终采用VIII107.1的同一个
有限维实 $V$、闭尖生成锥 $C$、严格正原单位 $u$、整个
$K=C\cap\{u=1\}$、全部 $P=\operatorname{ext}K$ 和全部
$\mathcal E=[0,u]_{C^*}$，并假设VIII107.2的
$\mathsf W=\mathrm{EB}_{\ge1}+\mathrm{Pair}_{\perp}$。
记 $n=\dim V$、$d_p=\operatorname{affdim}D_p\ge1$、
$c_p$ 为完整原排除球 $D_p$ 的球心，并置

$$
L_p=\operatorname{lin}(D_p-c_p),\qquad
D_p=c_p+\{z\in L_p:\|z\|_p\le1\}.
\tag{VIII108.1}
$$

这里 $\|\cdot\|_p$ 是该仿射球自身给出的欧氏范数，内积记
$\langle\cdot,\cdot\rangle_p$；没有把不同球的内积预先拼成全空间内积。
直接复用VII104.2—104.7及VII105.2—105.5：唯一原尺 $a_p$ 是全锥序least，
$D_p=\{x\in K:a_p(x)=0\}$，且 $a_p$ 唯一确认 $p$。
每个正交纯对有唯一第三纯点，三张原尺共同相加为 $u$；
在每张已有球上，原纯尺的限制是全部球直径效应。
特别地，若 $q,r$ 是 $D_p$ 的一对对径，则 $(p,q,r)$ 是原joint框架，
而 $p,r$ 也是 $D_q$ 的对径。

使用VII105.4—105.5的共同正线性延拓及正投影

$$
\begin{gathered}
Z_p=\{f\in C^*:f(p)=0\},\qquad
\operatorname{res}_p:Z_p\overset{\sim}{\longrightarrow}
                         \operatorname{Aff}(D_p)_+,\\
\Lambda_p:\operatorname{Aff}(D_p)\longrightarrow V^*,\qquad
\Pi_p^*=\Lambda_p\operatorname{res}_p,\qquad
R_p(v)=a_p(v)p,\\
M_p=\operatorname{span}(\{p\}\cup D_p),\qquad
Q_p=R_p+\Pi_p,\qquad N_p=\ker Q_p.
\end{gathered}
\tag{VIII108.2}
$$

星号表示线性对偶，$\operatorname{res}_p$ 在复合式中取其整个线性限制映射。
$\Lambda_p$ 是上述正锥双射之逆的唯一线性延伸；不能用彼此无关的逐效应延拓替代它。
本节尚不假设共同中心 $\mathrm G$、全Pair或全纯数值互易。

**定理 108.2（原球投影和共同零方向）。** 仅在 $\mathsf W$ 下，

$$
\begin{gathered}
R_p\Pi_p=\Pi_pR_p=0,\qquad Q_p^2=Q_p,\qquad
\operatorname{im}Q_p=M_p,\qquad V=M_p\oplus N_p,\\
\dim M_p=d_p+2,\qquad k_p:=\dim N_p=n-d_p-2\ge0,\\
N_p=\{z\in V:a_p(z)=0,\quad
             a_s(z)=0\text{ 对全部 }s\in P\cap D_p\}.
\end{gathered}
\tag{VIII108.3}
$$

证明。VII105.5给 $\Pi_pp=0$ 及 $\Pi_p^*a_p=0$，所以两个交叉复合为零。
$R_p,\Pi_p$ 各自幂等，故 $Q_p$ 幂等。
原 $C$ 生成 $V$，正像 $\Pi_p(C)=\operatorname{cone}D_p$，
因而 $\operatorname{im}\Pi_p=\operatorname{span}D_p$。
$R_p$ 的像为 $\mathbb Rp$，它与前一像零交，因为 $a_p(p)=1$ 而
$a_p|_{\operatorname{span}D_p}=0$。这给像、直和及维数公式；
$\dim\operatorname{span}D_p=d_p+1$ 使用的是整个 $D_p$ 位于 $u=1$。

对每个 $s\in P\cap D_p$，零对称使 $a_s(p)=0$，故 $a_s\in Z_p$。
限制双射于是给 $\Pi_p^*a_s=a_s$。
这些限制恰为全部球直径效应，线性张成 $\operatorname{Aff}(D_p)$：
相反方向的两个直径效应之和是常数一，差则给全部线性方向。
所以 $a_s$ 张成 $\operatorname{im}\Pi_p^*$。
因此 $\Pi_pz=0$ 当且仅当所有这样的 $a_s(z)=0$。
再用两个投影像的直和，$Q_pz=0$ 当且仅当
$R_pz=0$ 且 $\Pi_pz=0$，即得最后一式。证毕。

### 108.2 一个原纯点处的不同球切空间

**定义 108.3（邻球在原纯点处的切空间）。** 对 $q\in P\cap D_p$，令
$r=2c_p-q$。在 $D_q$ 中，$p,r$ 是对径。定义

$$
T(q\mid p)=\{z\in L_q:a_p(z)=0\}.
\tag{VIII108.4}
$$

这不是最低读数函数 $T_p$ 的另一种记法。
由球上的直径读数，若 $e=p-c_q$，则 $\|e\|_q=1$ 且

$$
a_p(c_q+y)=\frac{1+\langle e,y\rangle_q}{2},\qquad
T(q\mid p)=\{z\in L_q:\langle e,z\rangle_q=0\}.
\tag{VIII108.5}
$$

所以它是球面 $P\cap D_q$ 在 $p$ 处的普通线性切空间，维数为 $d_q-1$。
当 $d_q=1$ 时取零空间；没有对整个 $P$ 另加光滑流形假设。

**定理 108.4（切方向落入同一剩余空间）。** 仅在 $\mathsf W$ 下，

$$
T(q\mid p)\subseteq N_p,\qquad d_q-1\le n-d_p-2
\quad(q\in P\cap D_p).
\tag{VIII108.6}
$$

证明。零向量无须处理。对非零 $z\in T(q\mid p)$ 置
$h=\|z\|_q^{-1}>0$。球内正交性使

$$
\gamma_q(t)=c_q+\cos t\,(p-c_q)+h\sin t\,z
 =\frac{1+\cos t}{2}p+\frac{1-\cos t}{2}r+h\sin t\,z
\tag{VIII108.7}
$$

对全部实 $t$ 都是原纯点，且 $\gamma_q(0)=p$。
任取 $s\in P\cap D_p$，有 $a_s(p)=0$，而原效应正性给
$a_s(\gamma_q(t))\ge0$。这是在 $t=0$ 达到最小值的可微实函数，
正负参数的导数均须一致为零。因此 $h a_s(z)=0$。
又有 $a_p(z)=0$，定理108.2的共同零方向刻画给 $z\in N_p$。
取维数即得不等式。光滑性只用于一张已给球内的这条圆，
没有输入实际运动或全纯点集的可微性。证毕。

**引理 108.5（圆弧原尺的全空间恒等式）。** 保持108.4证明中的
$q,r,z,h$。存在同一原 $V$ 上的有符号线性效应 $b_q$，使对全部实 $t$

$$
\begin{gathered}
a_{\gamma_q(t)}
 =\frac{1+\cos t}{2}a_p+\frac{1-\cos t}{2}a_r+\sin t\,b_q,\\
b_q(p)=b_q(r)=0,\qquad b_q(z)=\frac1{2h},\qquad b_q|_{M_p}=0.
\end{gathered}
\tag{VIII108.8}
$$

恒等式在整个 $V$ 上成立；不只是在 $D_q$ 上的限制等式。

证明。在 $D_q$ 上取仿射函数

$$
B_q(c_q+y)=\tfrac12\langle hz,y\rangle_q,
\qquad b_q=\Lambda_qB_q.
\tag{VIII108.9}
$$

球内直径公式给(VIII108.8)第一行的限制等式。
$\gamma_q(t),p,r$ 均为 $D_q$ 中的原纯点，故相应的三张非负原尺都在
$Z_q$ 中。限制双射使它们各自等于同一 $\Lambda_q$ 对其限制的延拓；
应用该映射的线性性就得到整个 $V$ 上的等式。
$b_q$ 在 $p,r$ 取零，并在 $z$ 上取
$h\|z\|_q^2/2=1/(2h)$，这些值均可在 $\operatorname{span}D_q$ 中直接计算。

对任意 $x\in D_p$，$a_p(x)=0$，原正性给

$$
0\le a_{\gamma_q(t)}(x)
 =\frac{1-\cos t}{2}a_r(x)+\sin t\,b_q(x).
\tag{VIII108.10}
$$

令 $t$ 从正、负两侧趋零，一阶项必须为零，故 $b_q(x)=0$。
结合 $b_q(p)=0$，得到 $b_q|_{M_p}=0$。
没有声称不同球得到的 $b_q$ 在整个 $N_p$ 上相等。证毕。

**定理 108.6（不同邻点的切空间零交）。** 仅在 $\mathsf W$ 下，

$$
q,q'\in P\cap D_p,\quad q\ne q'
\quad\Longrightarrow\quad
T(q\mid p)\cap T(q'\mid p)=\{0\}.
\tag{VIII108.11}
$$

证明。反设有共同非零 $z$，记
$r=2c_p-q$、$r'=2c_p-q'$，则 $r\ne r'$。
分别在 $D_q,D_{q'}$ 中使用引理108.5，保留两个正尺度
$h=\|z\|_q^{-1}$、$h'=\|z\|_{q'}^{-1}$ 及两张原线性效应
$b_q,b_{q'}$。它们各自在 $M_p$ 上为零，而
$b_q(z)=1/(2h)$、$b_{q'}(z)=1/(2h')$。
定理108.4还给 $z\in N_p$，所以 $a_r(z)=a_{r'}(z)=a_p(z)=0$。

球圆的半角参数给下列全部原纯点及其原尺：对任意 $t,s\in\mathbb R$，

$$
\begin{gathered}
x_q(t)=\frac{t^2p+r+2htz}{1+t^2},\qquad
y_{q'}(s)=\frac{p+s^2r'+2h'sz}{1+s^2},\\
a_{x_q(t)}=\frac{t^2a_p+a_r+2t b_q}{1+t^2}.
\end{gathered}
\tag{VIII108.12}
$$

例如第一条圆式使用 $\cos\theta=(t^2-1)/(1+t^2)$、
$\sin\theta=2t/(1+t^2)$；第二条使用
$\cos\theta=(1-s^2)/(1+s^2)$、$\sin\theta=2s/(1+s^2)$。
故这不是把任意线性扰动冒作原纯态。
将同一个原 $a_{x_q(t)}$ 作用在同一个原 $y_{q'}(s)$ 上，得到

$$
0\le a_{x_q(t)}(y_{q'}(s))
 =\frac{t^2+c s^2+2(h'/h)ts}{(1+t^2)(1+s^2)},
\qquad c=a_r(r')\in[0,1).
\tag{VIII108.13}
$$

这里 $a_r(p)=0$，$b_q(p)=b_q(r')=0$，且
$2h'b_q(z)=h'/h$，所以分子中没有被略去的线性项。
严格上界 $c<1$ 只用 $a_r$ 唯一确认 $r$ 及 $r'\ne r$。
令 $s=1,t=-h'/h$，原正性迫使 $(h'/h)^2\le c$。
交换两球，同理有

$$
(h/h')^2\le c',\qquad c'=a_{r'}(r)\in[0,1).
\tag{VIII108.14}
$$

两式相乘给 $1\le cc'<1$，矛盾。
没有令 $c=c'$，没有将两球的范数或剩余空间上的线性效应认作同一张，
也不需要 $\mathrm G$ 或全纯读数互易。证毕。

### 108.3 三元维数约束与一维剩余空间

**推论 108.7（原joint框架的球维数律）。** 对任一原joint框架 $(p,q,r)$，
仅 $\mathsf W$ 已给

$$
T(q\mid p)\oplus T(r\mid p)\subseteq N_p,\qquad
d_p+d_q+d_r\le n.
\tag{VIII108.15}
$$

等号成立当且仅当这两个切空间的线性直和等于 $N_p$。
若所有 $d_p$ 都等于同一 $d$，则 $n\ge3d$；
特别地，全部完整 $D_p$ 为三球时必有 $n\ge9$。

证明。$q,r$ 是 $D_p$ 中两个不同邻点；108.4和108.6给所述直和。
因此

$$
(d_q-1)+(d_r-1)\le n-d_p-2.
\tag{VIII108.16}
$$

移项即得三元不等式；有限维空间中等维包含恰为相等，给等号刻画。
常维结论逐框架应用即可。这里仅相加了两个已证零交子空间的维数。
任意多个两两零交子空间不一定构成总体直和，不能把全部邻点的切维数相加。
即使(VIII108.15)取等，两个切空间的线性和填满 $N_p$，也不同于每个非零
剩余向量都属于某一个 $T(s\mid p)$。$n\ge9$ 是必要界，
不是九维载体必为复三能级的充分条件。证毕。

**推论 108.8（余维一时至多一个邻盘）。** 仅在 $\mathsf W$ 下，若
$\operatorname{codim}_VM_p=k_p=1$，则

$$
d_q\le2\quad(q\in P\cap D_p),\qquad
\#\{q\in P\cap D_p:d_q=2\}\le1.
\tag{VIII108.17}
$$

证明。108.4给 $d_q-1\le1$。
若两个不同邻点都有 $d_q=2$，各自的一维非零切空间必须都等于一维 $N_p$，
违反108.6。其余邻点的完整排除球均为线段，而非只含一条所选直径。证毕。

### 108.4 共同中心下允许厚球的框架平面

**定义 108.9（共同中心、框架平面与球方向空间）。** 从此节到108.11，
另假设VII105.9的共同中心条件 $\mathrm G$，即存在同一个 $U$ 使
$p+2c_p=U$ 对全部 $p\in P$ 成立。置

$$
\begin{gathered}
w=U/3\in\operatorname{ri}K,\qquad H=\ker u,\qquad
\ell_p=\mathbb R(p-w),\\
\mathfrak T=\{\{p,q,r\}:(p,q,r)\text{ 为原joint框架}\},\\
L_T=\operatorname{aff}T,\qquad E_T=L_T-w\quad(T\in\mathfrak T),\qquad
X_p=M_p\cap H.
\end{gathered}
\tag{VIII108.18}
$$

每个框架三点之和为 $U$，故 $E_T$ 是二维线性空间。
三张joint效应还给准确截面

$$
K\cap L_T=\operatorname{conv}T.
\tag{VIII108.19}
$$

确实，三点由Kronecker读数线性独立；在 $L_T$ 中的仿射系数就是这些原效应读数，
所以属于 $K$ 的点的三个系数非负。反向包含由凸性成立。
不同框架若共享两个纯点，VII104.3的唯一第三点使其相同。

**定理 108.10（框架平面相交律和两种覆盖）。** 在 $\mathsf W+\mathrm G$ 下，
不同 $T,S\in\mathfrak T$ 满足

$$
E_T\cap E_S=
\begin{cases}
\ell_p,&T\cap S=\{p\},\\
\{0\},&T\cap S=\varnothing.
\end{cases}
\tag{VIII108.20}
$$

并且

$$
H=\bigcup_{T\in\mathfrak T}E_T,\qquad
X_p=\ell_p\oplus L_p
   =\bigcup_{T\in\mathfrak T:\ p\in T}E_T,
\qquad \dim X_p=d_p+1.
\tag{VIII108.21}
$$

证明。由(VIII108.19)，若两个框架平面相等，其截面三角形相等，
三个极点也相等，故框架相同。因此不同框架的二维空间不可能相等，
非零交只能是一条直线。
设此直线为 $\mathbb Rv$。过 $w$ 的整条直线与 $K$ 的交是非退化闭弦，
同时也是两个截面三角形在这条线上的整弦。
两个端点不可能都是第一三角形的顶点：否则 $w$ 位于一条边上，
与 $w$ 在该三角形内部矛盾。因此可取一个端点 $x$，它在第一三角形一条边的内部，
写该边为 $[q,r]$、第三顶点为 $p$。
$x$ 是非纯点，且 $q,r$ 为 $D_p$ 的对径。

在第二三角形中，$x$ 也不是顶点，故位于其某边 $[q',r']$ 的内部。
$D_p$ 是原面，$x\in D_p$ 迫使 $q',r'\in D_p$。
二者原正交，所以由球直径公式必为 $D_p$ 的对径；
其原最小面就是 $D_p$，点球双射及唯一第三点使第二三角形的第三顶点也为 $p$。
若 $x\ne c_p$，球中经过该非中心点的直径唯一，
故 $\{q,r\}=\{q',r'\}$，两框架相同，矛盾。
所以 $x=c_p$，而

$$
c_p-w=-\tfrac12(p-w)\ne0.
\tag{VIII108.22}
$$

公共直线遂为 $\ell_p$，两框架共享 $p$。
反向，若两框架共享 $p$，两空间显然都含 $\ell_p$；
不同二维空间的交至多一维，所以交恰为它。
这证明相交律，也保留了同一厚球的两条不同直径在中心相交的情形。
不能将该情形误作“两张不同排除球交于非纯点”。

对任意 $v\in H$，$w$ 的内点性使充分小的 $\varepsilon>0$ 满足
$w+\varepsilon v\in K$。VII105.10的同框架谱分解使该态属于某个
$\operatorname{conv}T\subset L_T$，于是 $v\in E_T$，给第一个覆盖。

最后 $w\in M_p$、$M_p=\operatorname{span}\{p,c_p\}+L_p$，且
$c_p=(3w-p)/2$，所以 $X_p=\ell_p+L_p$。
$a_p(p-w)=2/3$ 而 $a_p|_{L_p}=0$，故此和为直和。
含 $p$ 的框架来自 $D_p$ 的全部对径 $q,r$，相应的平面是
$\ell_p\oplus\mathbb R(q-c_p)$。
这些直径方向遍历 $L_p$ 的全部一维方向，遂覆盖整个 $X_p$，
并给其维数。这里是多个平面的并，不称这些平面彼此零交。证毕。

**定理 108.11（共同中心排除余维一）。** 在 $\mathsf W+\mathrm G$ 且
$n\ge5$ 时，不存在满足

$$
d_p=n-3\qquad\bigl(\operatorname{codim}_VM_p=1\bigr)
\tag{VIII108.23}
$$

的原纯点 $p$。

证明。反设存在。此时 $X_p$ 是 $H$ 的超平面。
由108.8，所有 $q\in P\cap D_p$ 均有 $d_q\le2$，
而其中至多一个点 $q_*$ 有 $d_{q_*}=2$。
任取框架 $T$；二维 $E_T$ 必与超平面 $X_p$ 非零相交。
取非零交向量，利用108.10的 $X_p$ 覆盖，找到含 $p$ 的框架 $S$，
使该向量也属于 $E_S$。

若 $T=S$，则 $p\in T$。否则相交律使 $T,S$ 共享某个纯点 $s$。
若 $s=p$，仍有 $p\in T$；若 $s\ne p$，因 $s\in S$，必有 $s\in D_p$。
当 $d_s=1$ 时，整个 $D_s$ 的两个端点固定唯一无序框架，
所以 $T=S$，与此分支矛盾。因此后一情形只能是 $s=q_*$。
故每个框架都包含 $p$ 或这个唯一可能的 $q_*$。

若无 $q_*$，(VIII108.21)使 $H=X_p$，矛盾。
若有，则同一覆盖给

$$
H=X_p\cup X_{q_*},\qquad
\dim X_p=n-2<n-1,\qquad \dim X_{q_*}=3<n-1.
\tag{VIII108.24}
$$

实线性空间不能被两个真线性子空间覆盖：若一者包含另一者，其并仍真；
否则取各自在另一者之外的向量，二者之和属于二者之外。
这与(VIII108.24)矛盾。证毕。

### 108.5 满球张成、低维原锥与同单位尺度

**定理 108.12（满 $M_p$ 迫使原锥旗标分解）。** 仅在 $\mathsf W$ 下，
若某个 $M_p=V$，则

$$
C=\mathbb R_+p\oplus\operatorname{cone}D_p,\qquad
K=\operatorname{conv}(\{p\}\cup D_p),\qquad d_p=n-2.
\tag{VIII108.25}
$$

在同一原单位下，这是 $\mathbb R\oplus\operatorname{spin}_{d_p}$ 的正锥和规范迹，
具体尺度如下。取线性等距 $A:\mathbb R^{d_p}\to L_p$，
使 $A(B^{d_p})=D_p-c_p$。写标准spin坐标为 $(a,x)$，其正锥
$a\ge\|x\|$、规范迹为 $2a$。则

$$
\begin{gathered}
\Phi:\mathbb R\oplus\operatorname{spin}_{d_p}
       \overset{\sim}{\longrightarrow}V,\qquad
\Phi(\alpha,a,x)=\alpha p+2a c_p+2Ax,\\
\Phi(\mathbb R_+\oplus(\operatorname{spin}_{d_p})_+)=C,
\qquad u\Phi(\alpha,a,x)=\alpha+2a.
\end{gathered}
\tag{VIII108.26}
$$

证明。满像投影 $Q_p$ 等于恒等算子。
$R_p,\Pi_p$ 都正，故每个原 $v\in C$ 都有
$v=R_pv+\Pi_pv$，两项分别落在 $\mathbb R_+p$ 与
$\operatorname{cone}D_p$。反向包含由原锥对加法封闭成立；
两线性像零交，得到原锥直和，不只是抽象面格分裂。
原单位归一给所述整个 $K$。

每个原向量唯一写成

$$
v=\alpha p+\beta c_p+z,\qquad z\in L_p,\qquad
u(v)=\alpha+\beta,
\qquad v\in C\ \Longleftrightarrow\
\alpha\ge0,\quad\beta\ge\|z\|_p.
\tag{VIII108.27}
$$

由(VIII108.1)，球锥恰由 $\beta\ge\|z\|_p$ 给出，
包括 $\beta=0$ 时必有 $z=0$。
代入 $\beta=2a,z=2Ax$ 就得到(VIII108.26)。
这里使用VII103.7的成熟spin记号及规范迹，
不是把未缩放Lorentz坐标 $\beta$ 的原质量误认成 $2\beta$。
标准乘法 $(a,x)\circ(b,y)=(ab+x\cdot y,ay+bx)$ 只用于标识所得代数，
原锥分解本身已由正投影证明。证毕。

**推论 108.13（三、四维只需W，五维使用G）。** 在同一原全态、全效应域内，
$\mathsf W$ 迫使 $n\ge3$，且有下列同锥同单位结论：

$$
\begin{array}{c|c|c}
\text{原条件}&\dim V&\text{全部原模型的表示}\\ \hline
\mathsf W&3&\mathbb R_+^3,\quad u=\text{三坐标之和}\\
\mathsf W&4&\mathbb R\oplus\operatorname{spin}_2,\quad
                         u=\alpha+2a\\
\mathsf W+\mathrm G&5&\mathbb R\oplus\operatorname{spin}_3,\quad
                         u=\alpha+2a
\end{array}
\tag{VIII108.28}
$$

表中spin行均指相应正锥；反向这些同单位模型满足所列条件。

证明。joint三点的三张Kronecker效应使三点线性独立，所以 $n\ge3$。
若 $n=3$，108.2给 $d_p\le1$，故全部 $d_p=1$；
直接使用VIII107.2的无G全线段刚性，得到经典三角形，不重证该结果。
若 $n=4$ 且全部 $d_p=1$，同一定理会给 $n=3$，矛盾。
所以存在 $d_p\ge2$，而108.2给 $d_p\le2$；
于是 $M_p=V$，应用108.12得到第二行。这里不需要G。

若 $n=5$ 并有G，同样不能全部 $d_p=1$，故存在 $d_p\ge2$。
108.2给 $d_p\le3$，108.11又排除 $d_p=2=n-3$，
于是 $d_p=3$ 且 $M_p=V$。108.12得到第三行。
这一步确实使用了G；没有把五维结论降为仅W的结论。

为核对反向及全部原效应，统一在
$J=\mathbb R\oplus\operatorname{spin}_d$、$u(\alpha,a,x)=\alpha+2a$ 中写

$$
f(\alpha,a,x)=b\alpha+2c a+2y\cdot x,\qquad
f\in[0,u]\ \Longleftrightarrow\
0\le b\le1,\quad \|y\|\le\min(c,1-c).
\tag{VIII108.29}
$$

正性及补效应正性分别给 $c\ge\|y\|$ 和 $1-c\ge\|y\|$，
所以这确是整个效应区间。原纯点恰为旗标
$f_0=(1,0,0)$ 和球点 $s_e=(0,1/2,e/2)$、$\|e\|=1$。
相应的least确认效应为
$a_{f_0}(\alpha,a,x)=\alpha$、
$a_{s_e}(\alpha,a,x)=a+e\cdot x$，
正性给其准确零面

$$
D_{f_0}=\{(0,1/2,x):\|x\|\le1/2\},\qquad
D_{s_e}=[f_0,s_{-e}].
\tag{VIII108.30}
$$

这些全部效应和排除集也正是VII103.7的直和模型字典。
任意两球纯点同处真面 $D_{f_0}$；旗标与任一球纯点同处真边
$D_{s_{-e}}$，故全Pair成立，特别有 $\mathrm{Pair}_{\perp}$。
全部排除集为非退化球，且
$f_0+2c_{f_0}=s_e+2c_{s_e}=(1,1,0)$，故G也成立。
$d=1$ 给三角形，$d=2,3$ 给其余两行。
仅在这一原锥构造之后，才可用VII104.7、VII105.8和VII106.10的既有等价链，
取得这些模型的完整 $S$、PL3、PAIRJET2和JET2；
没有以这些较强条件反向填补维数论证。证毕。

**推论 108.14（不可分解原模型的维数下界）。** 若
$\mathsf W+\mathrm G$ 的原锥 $C$ 不可分解为两个非零锥的线性直和，则

$$
n\ge6,\qquad 1\le d_p\le n-4\quad(p\in P),\qquad
\exists p\in P:\ d_p\ge2.
\tag{VIII108.31}
$$

证明。108.13穷尽的 $n\le5$ 模型均可分解，故 $n\ge6$。
108.2总给 $d_p\le n-2$；等于 $n-2$ 时108.12给非平凡原锥直和，
而等于 $n-3$ 已被108.11排除。因此 $d_p\le n-4$。
若全部 $d_p=1$，VIII107.2会给三角形和 $n=3$，再次矛盾。
这里没有先分类任意可分解W模型，也没有证明不可分解模型的球维数恒定。证毕。

### 108.6 量子对应、剩余拼合与几何解释

**命题 108.15（必要维数和完整量子入口的区别）。** 原域综合108.2、
108.4—108.8、108.10—108.14为 `repo-derived` 推导；
所用共同延拓和全线段刚性分别直接复用VII105.4—105.5和VIII107.2。
本章的三元维数律与成熟秩三Jordan模型相容，但不替代完整重构前件：
同一原域的完整单载体入口仍是VII106.10的
$\mathsf W+\mathrm{PAIRJET2}$；再要求全部完整排除球为 $B^3$，
才由VII106.17得到同单位复三能级、全部密度态、全部效应及Born配对。

证明。必要维数由108.7给出。作为等号的成熟模型对照，
VII103.7按其所引Alfsen—Shultz秩二字典和有限Jordan分类，
给 $H_3(\mathbb F)$、$\mathbb F=\mathbb R,\mathbb C,\mathbb H,\mathbb O$ 的
$m=\dim_{\mathbb R}\mathbb F\in\{1,2,4,8\}$，其中

$$
d_p=m+1,\qquad n=3+3m=3d_p.
\tag{VIII108.32}
$$

这是既有模型对108.7的等号核对，不是从等号反推该分类。
一般域中，常维 $d=3$ 只由本章取得 $n\ge9$；
本章既未证明 $n=9$ 自动实现该模型，也未从维数推出全纯互易或二阶拼合。
原纯尺之间的局部约束是在同一个原锥上的正性后果，
不能与成熟模型内部已有的Peirce分解互换使用。

完整重构的陈述直接复用VII106.10、VII106.17：
PAIRJET2供应尚缺的共同二阶形，继而取得全Pair、覆盖律、完整 $S$、
同锥同单位EJA表示；全部 $B^3$ 才选择复型。
低维表的 $\mathbb R\oplus\operatorname{spin}_3$ 仅是一个经典旗标加一个三球，
它的其他纯点背后是线段，不能冒充“全部排除球为三球”的复三能级。

VII106.16、VII106.18的原装饰元组和全有限复合合同继续按原量词使用：
全有限层级仍需其全有限强分块域及原 $S_2+\mathsf F$ 与具名低二份供应，
或者其另一路线的原三份比较前件。
同事件CP、仪器、实际菜单和钟单位仍各需原共同来源、实际过程及动态合同。
数学投影、静态圆弧和球切向量没有提供这些操作，切向量也不是实际速度或时间。
上述综合不主张全球原创或用维数必要性完成量子公理重构。证毕。

**开放问题 108.16（从切方向互斥到完整二阶拼合）。** 在同一原域中定义

$$
\mathrm{TCov}(p):\quad
N_p=\bigcup_{q\in P\cap D_p}T(q\mid p).
\tag{VIII108.33}
$$

108.6只说明其中不同子空间零交，故若非零向量属于右侧，其邻点标签唯一；
尚未证明一般W或 $\mathsf W+\mathrm G$ 供应该覆盖。
也没有由本章证明不同 $d_q$ 恒定、这些子空间组成具有局部平凡化的球丛、
或它们的内积与效应延拓跨球一致。
108.7等号时取得的是两个切空间的线性直和覆盖，
不能省去(VIII108.33)中“属于一张切空间”的量词。

此外，尚缺的完整重构桥仍是VII106.15中的

$$
\mathsf W+\mathrm G\ \Longrightarrow\ \mathrm{JET2}.
\tag{VIII108.34}
$$

G只由VII106.11给原谱迹 $\tau$ 的一阶线性，
没有由本章得到 $\sigma_2$ 在不同方向上的共同二次性。
即使另证TCov，也仍须证明它如何推出完整纯读数互易、覆盖律或该二阶恒等式，
不能把一个尚无该桥的几何覆盖当成替代公理已完整。
这里的未决表示尚未证明或反驳，不宣称形式不可判定性。
特别地，五维结论在去掉G后的范围、六维及以上的一般重构，均未由本章结算。

**命题 108.17（从一根切箭头到三张球的完整直观解释）。** 本章结果可按以下
同一原几何解释；其中“读数”始终指原数学效应在原态上的值。

证明与解释。固定一个原纯态 $p$。与它正交的全部态已经组成一个完整球 $D_p$。
先把 $p$ 和这个球张成的方向收在 $M_p$ 中，其余线性方向就是 $N_p$。
这不是另加一个隐藏系统，而是由原尺和共同正投影切出的原空间直和。
球中每个纯邻点 $q$ 又有自己的排除球 $D_q$，且 $p$ 位于这个球的边界。
沿 $D_q$ 的球面从 $p$ 向两边作极小偏移，所有在 $p$ 读零的非负原尺，
一阶都不能向任一侧下降；它们的一阶变化只能为零。
因此这个球在 $p$ 处的切箭头只能伸入同一个 $N_p$。

更强的是，不同邻点不能借用同一根非零切箭头。
若它们共用一根，分别沿两张球取真正的纯态圆弧，
共同线性延拓会把圆弧上的纯尺也锁定到原全空间。
让第一张球的尺去读第二张球的态，非负性要求一个球半径比的平方
不超过某个严格小于一的确认读数；交换两球，又要求倒数平方也严格小于一。
两者相乘不可能成立。这是两张原球通过同一全态、全效应域发生的约束，
不是从外部指定球间夹角或全局内积。

一组三元joint框架正好给两个这样的邻点。
它们的两份切方向不能重叠，所以连同 $D_p$ 及旗标 $p$ 已占的方向，
必须满足 $d_p+d_q+d_r\le n$。这把二元切关系提升为三元维数限制，
但并不允许把无限多张两两零交的切空间全部累加。
若 $N_p$ 只剩一维，所有邻球最多是圆盘，且至多一个邻球真是圆盘。

G再把所有三元框架的重心放在同一点。
此时它们的二维方向平面覆盖整个 $\ker u$，两平面只能零交，
或沿共享纯点的方向线相交；厚球的不同直径在球心相交正是后一情形。
若 $M_p$ 只差一维填满原空间，这个平面覆盖就被迫挤进至多两个真子空间，
所以在 $n\ge5$ 时不可能。
五维因此只剩一张三球连一个经典旗标的分支；四维的对应圆盘分支甚至不用G。
真正不可分解的候选必须从六维起，并满足每张球 $d_p\le n-4$。

剩下的差别是“不能重叠”和“足以拼成同一量子几何”之间的差别。
本章给出前者和相应的低维排除，没有证明每根剩余箭头都被某张邻球接住，
更没有证明各球的二阶读数自动合为同一个二次形。
因此更简洁且完整的量子替代条件仍须补上108.16的具体桥梁；
原来的 $\mathsf W+\mathrm{PAIRJET2}$ 完整入口继续保留。证毕。

## 追加锚（本行以下为增补区）

## 109. 三元二面可辨、共同切度量与原星锥的自对偶重构

### 109.1 只用原态与原效应的附加关系

**定义 109.1（原域与三元二面可辨）。** 沿用VIII107.1、VIII108.1的同一个非零有限维实空间
$V$、闭尖生成锥 $C$、严格正原单位 $u$、整个紧基 $K=C\cap\{u=1\}$、
全部原纯点 $P=\operatorname{ext}K$ 及全部原效应 $\mathcal E=[0,u]_{C^*}$。
对 $p\in P$，仍取全部确认效应上的最小值

$$
\begin{gathered}
F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in F_p}f(x),\qquad D_p=\{x\in K:T_p(x)=0\},\\
p\perp q\ \Longleftrightarrow\ T_p(q)=0,\qquad
\mathsf W=\mathrm{EB}_{\ge1}+\mathrm{Pair}_{\perp},\\
\mathrm{EB}_{\ge1}:\quad D_p\simeq_{\rm aff}B^{d_p},\quad d_p\ge1\quad(p\in P),\\
\mathrm{Pair}_{\perp}:\quad p,q\in P,\ p\perp q\ \Longrightarrow\ H(p,q)\ne K.
\end{gathered}
\tag{VIII109.1}
$$

$H(p,q)$ 是整个原最小面。以下假设 $\mathsf W$，直接复用VII104.2—104.7、
VII105.2—105.5：$P$ 紧，每个原纯点有唯一整球零尺 $a_p$，
它是 $F_p$ 的全锥序least，$T_p=a_p$ 于整个 $K$。
原joint框架指三个两两原正交的纯点 $F=(p,q,r)$；它们恰有
$a_p+a_q+a_r=u$，各自在另外两点读零，在自身读一。
每个纯点进入某个框架，框架任意两点是第三点完整排除球的对径。
这些是W的后果，不是额外输入的全纯互易或全局内积。

新增关系称为**三元二面可辨**，记 $\mathrm{TFD}_3$：

$$
\begin{aligned}
&\text{对每个原joint }F=(p,q,r)\text{ 及任意不同 }x,y\in K,\\
&\qquad\exists i\in\{p,q,r\}\ \exists f\in\mathcal E:\quad
f(i)=0,\qquad f(x)\ne f(y).
\end{aligned}
\tag{VIII109.2}
$$

这里联合使用三张完整的原零效应面；不是只使用 $a_p,a_q,a_r$ 三个标量。
公理陈述只使用原态—原效应二元评价及其零关系，没有另给操作、导数、
内积、反射正性或滤子保纯性。框架可由原二元正交关系识别，
不以实际装置菜单中的可实施性定义它。

保留VIII108.1—108.3的原生对象，写球内积为 $g_p$：

$$
\begin{gathered}
D_p=c_p+\{y\in L_p:g_p(y,y)\le1\},\qquad n=\dim V,\\
Z_p=\{f\in C^*:f(p)=0\},\qquad
\Pi_p^*=\Lambda_p\operatorname{res}_p,\qquad R_p(v)=a_p(v)p,\\
Q_p=R_p+\Pi_p,\qquad M_p=\mathbb Rp+\operatorname{span}D_p,
\qquad N_p=\ker Q_p,\\
V=M_p\oplus N_p,\qquad \dim M_p=d_p+2,\qquad
T(q\mid p)=\{z\in L_q:a_p(z)=0\}\subseteq N_p.
\end{gathered}
\tag{VIII109.3}
$$

其中 $q\in P\cap D_p$，$\Lambda_p$ 是VII105.4的同一张共同正线性延拓。
不同球的 $g_p$ 起初互不认同。定义全框架算子条件

$$
\mathrm{TRI2}:\quad
I=\Pi_p+\Pi_q+\Pi_r-R_p-R_q-R_r
\quad\text{对每个原joint }F=(p,q,r).
\tag{VIII109.4}
$$

$\mathrm{A3}$ 在本章只作为 $\mathrm{TFD}_3$ 或其待证等价式TRI2的简称，
不再表示另一条假设。

### 109.2 原部分Peirce代数、联合盲核与维数

**定理 109.2（W内的三阶剩余）。** 对任一原joint框架 $F=(p,q,r)$，令

$$
\begin{gathered}
E_{pq}=\Pi_r-R_p-R_q,\quad
E_{pr}=\Pi_q-R_p-R_r,\quad
E_{qr}=\Pi_p-R_q-R_r,\\
\mathcal I_F=I-\Pi_p-\Pi_q-\Pi_r+R_p+R_q+R_r,
\qquad Z_F=\operatorname{im}\mathcal I_F.
\end{gathered}
\tag{VIII109.5}
$$

三个 $R_i$、三个 $E_{ij}$ 和 $\mathcal I_F$ 是两两乘积为零的代数投影，和为 $I$。
这里不主张 $E_{ij}$ 或 $\mathcal I_F$ 保正。准确地有

$$
\begin{gathered}
\Pi_p\Pi_q=\Pi_q\Pi_p=R_r,\qquad
\operatorname{im}E_{pr}=T(q\mid p),\qquad \dim\operatorname{im}E_{pr}=d_q-1,\\
Z_F=\ker\Pi_p\cap\ker\Pi_q\cap\ker\Pi_r\subseteq\ker u,\\
V=\mathbb Rp\oplus\mathbb Rq\oplus\mathbb Rr
 \oplus\operatorname{im}E_{pq}\oplus\operatorname{im}E_{pr}
 \oplus\operatorname{im}E_{qr}\oplus Z_F,\\
\dim Z_F=n-d_p-d_q-d_r.
\end{gathered}
\tag{VIII109.6}
$$

证明。$R_iR_j=\delta_{ij}R_i$。若 $i\ne j$，$\Pi_i$ 固定 $j$，
且 $\Pi_i^*a_j=a_j$，因为 $a_j\in Z_i$；若 $i=j$，两种复合均为零。
所以 $\Pi_iR_j=R_j\Pi_i=R_j$ 或零，分别对应 $i\ne j$ 或 $i=j$。

对 $v\in C$，正像 $\Pi_p\Pi_qv$ 在 $\operatorname{cone}D_p$ 中，且
$a_q(\Pi_p\Pi_qv)=a_q(\Pi_qv)=0$。
两张排除面锥的交恰为共同第三点 $r$ 的射线，故这个正像在 $\mathbb R_+r$ 中。
又由VII105.5的归一式及 $a_p\Pi_q=a_p$，

$$
u\Pi_p\Pi_q=(u-a_p)\Pi_q=u-a_q-a_p=a_r.
\tag{VIII109.7}
$$

因此 $\Pi_p\Pi_qv=a_r(v)r$；$C$ 生成 $V$，得到全空间上的乘法式。
交换两指标给另一复合。代入(VIII109.5)，逐项相乘即得所列七个投影
各自幂等、两两相消和总和恒等。

在 $\operatorname{span}D_q$ 中，$p,r$ 是对径，故有代数直和
$\mathbb Rp\oplus\mathbb Rr\oplus T(q\mid p)$。
$E_{pr}$ 杀掉前两项，在第三项上恒等；其像确为第三项：
它的像在 $\operatorname{span}D_q$，且 $uE_{pr}=a_pE_{pr}=0$。
这也证明其维数为 $d_q-1$，包含零维情形。
循环指标给其余两项。

每个 $\Pi_i\mathcal I_F=0$；反过来，若三个 $\Pi_i$ 均杀掉 $z$，
由 $a_p\Pi_q=a_p$ 等式得到三个 $a_i(z)=0$，所以 $R_i z=0$，
并有 $\mathcal I_Fz=z$。这证明共同核公式。
$u=a_p+a_q+a_r$ 使此核位于 $\ker u$。
直和的维数为 $3+(d_p-1)+(d_q-1)+(d_r-1)+\dim Z_F$，即得末式。
这是原滤子的代数推导，没有先用Jordan Peirce分解。证毕。

**定理 109.3（联合全态可辨的等价表述及真实反事实）。** 在W下，
对固定原joint框架 $F$，下列条件等价：该框架满足(VIII109.4)；
$Z_F=0$；联合映射 $v\mapsto(\Pi_pv,\Pi_qv,\Pi_rv)$ 在 $V$ 上注入；
同一联合映射在整个 $K$ 上注入；(VIII109.2)对该框架成立；
$d_p+d_q+d_r=n$。因此 $\mathrm{TFD}_3\Longleftrightarrow\mathrm{TRI2}$，
也等价于每个框架的球维数和恰为 $n$。

证明。投影 $\mathcal I_F$ 为零当且仅当其像为零；109.2的共同核和维数式
立即给全空间注入与维数的等价。
又有

$$
\operatorname{im}\Pi_i^*=\operatorname{span}Z_i,
\qquad
\operatorname{span}(Z_p\cup Z_q\cup Z_r)=V^*
\ \Longleftrightarrow\ Z_F=0.
\tag{VIII109.8}
$$

第一式由 $\Lambda_i$ 的正锥像为 $Z_i$，且非负仿射函数生成全部仿射函数得到。
非零 $f\in Z_i$ 可用 $\max_Kf>0$ 缩放成 $\mathcal E$ 中仍在 $i$ 读零的效应，
所以(VIII109.8)所用的零效应面没有超出原效应范围。
这给全空间注入与(VIII109.2)的正向联系。

反向和归一态注入必须处理有符号核。若 $0\ne z\in Z_F$，109.2给 $u(z)=0$。
闭尖生成锥在有限维有内点；用严格正 $u$ 归一一个内点，得到
$x\in\operatorname{ri}K$，且 $\operatorname{aff}K=\{u=1\}$。
取足够小的 $\epsilon>0$，则

$$
x_+=x+\epsilon z\in K,\qquad x_-=x-\epsilon z\in K,\qquad
x_+\ne x_-,\qquad \Pi_i x_+=\Pi_i x_-\quad(i=p,q,r).
\tag{VIII109.9}
$$

每个原 $f\in\mathcal E$ 且 $f(i)=0$ 都属于 $Z_i$，因而在这两态上读数相同。
这同时否定该框架的(VIII109.2)和归一态联合注入。
然而原全效应仍能分离这两态：选 $\ell\in V^*$ 使 $\ell(z)\ne0$，
$K$ 紧使 $M=\max_K|\ell|<\infty$，且 $M>0$。
取 $0<\delta\le1/(2M)$，则
$f=u/2+\delta\ell\in[0,u]$，而 $f(x_+)\ne f(x_-)$。
所以反事实是同一模型中的两个真实原态；盲的是三张完整二元读回的联合，
不是所有原效应，也不是将非正向量 $z$ 冒作态。证毕。

(VIII109.5)的包含—排除算子属于成熟的无三阶干涉／二缝重构恒等式：
[Ududec—Barnum—Emerson, arXiv:0909.4787v1][Q109UBE] Proposition 1及Appendix
在其standing condition下证明对应的投影和线性张成等价。
该standing condition要求每个暴露面有唯一中性互补滤子及唯一补滤子；
本章不将它当作未核对的W前件，而在109.2—109.3中直接证明这里所需的原代数和全态等价。
单凭这个成熟恒等式不推出Jordan重构。

### 109.3 原跨球正性给切效应收缩

**引理 109.4（共同延拓的跨球收缩）。** 固定 $p$，对 $q\in P\cap D_p$ 记
$r=2c_p-q$，简写 $T_q=T(q\mid p)$，并以 $g_q$ 同时表示球内积及其在 $T_q$ 上的限制。
对 $v\in T_q$ 定义同一原空间上的线性泛函

$$
J_q(v)=\Lambda_q h_v,\qquad
h_v(c_q+y)=g_q(v,y)\quad(y\in L_q).
\tag{VIII109.10}
$$

则 $J_q(v)|_{M_p}=0$，$J_q(v)(w)=g_q(v,w)$ 对 $w\in T_q$ 成立。
对任意 $q'\in P\cap D_p$、$r'=2c_p-q'$、$w\in T_{q'}$，有

$$
\begin{gathered}
c(q,q')=a_r(r')=a_q(q')
 =\frac{1+g_p(q-c_p,q'-c_p)}2,\\
|J_q(v)(w)|^2\le c(q,q')\,g_q(v,v)g_{q'}(w,w).
\end{gathered}
\tag{VIII109.11}
$$

证明。$\Lambda_q$ 在 $D_q$ 上限制为恒等，故在其方向空间给所写的 $g_q$。
VIII108.5的圆弧效应恒等式给 $J_q(v)|_{M_p}=0$：
对非零 $v$，该条的 $b_q$ 正是 $J_q(v)/(2\|v\|_q)$；零向量直接成立。
球 $D_p$ 内的直径读数给 $c$ 的三个表达式，
特别地只在这同一张球上使用了数值互易。

先取 $g_q(v,v)=g_{q'}(w,w)=1$。对所有实 $t,s$，下列点均是各自原球面上的原纯态：

$$
\begin{gathered}
X(t)=\frac{t^2p+r+2tv}{1+t^2},\qquad
Y(s)=\frac{p+s^2r'+2sw}{1+s^2},\\
a_{X(t)}=\frac{t^2a_p+a_r+tJ_q(v)}{1+t^2},\\
0\le a_{X(t)}(Y(s))
=\frac{t^2+c(q,q')s^2+2tsJ_q(v)(w)}{(1+t^2)(1+s^2)}.
\end{gathered}
\tag{VIII109.12}
$$

效应式是在整个 $V$ 上的等式，来自同一 $\Lambda_q$ 的线性性。
分子计算使用 $T_q,T_{q'}\subseteq N_p$，以及 $J_q(v)$ 在 $M_p$ 上为零，
所以没有遗漏其他线性或二次交叉项。令 $s=1$ 并最小化 $t$，
得到 $|J_q(v)(w)|^2\le c(q,q')$。齐次缩放给一般向量；
任一向量为零时也成立。此结论加强了VIII108.6只对共同切向量的比较，
没有预设全纯互易、不同球的共同内积或任何切投影自伴随性。证毕。

### 109.4 饱和对径的双向迹拼合

**定理 109.5（一个剩余空间上的唯一共同内积与等倾）。** 假设TRI2。
固定 $p$。每对对径 $q,r\in P\cap D_p$ 都有
$N_p=T_q\oplus T_r$。按这个代数直和定义内积

$$
G_{q,r}(v_q+v_r,w_q+w_r)=g_q(v_q,w_q)+g_r(v_r,w_r).
\tag{VIII109.13}
$$

它与对径对无关，记为 $G$。各 $T_q$ 的原内积是 $G$ 的限制；
沿 $T_r$ 到 $T_q$ 的代数投影 $P_q$ 成为真正的 $G$ 正交投影，且

$$
\begin{gathered}
P_q+P_r=I_{N_p},\qquad
J_q(v)(z)=G(v,z)\quad(v\in T_q,\ z\in N_p),\\
P_{q'}P_qP_{q'}=c(q,q')P_{q'},\qquad
P_qP_{q'}P_q=c(q,q')P_q.
\end{gathered}
\tag{VIII109.14}
$$

允许某个切空间为零；本定理不以非零秩为前提。

证明。109.2及TRI2给 $N_p=T_q\oplus T_r$。
其代数投影准确是 $P_q=E_{pr}|_{N_p}$，不是预先选的正交投影。
在109.4中取 $q'=r$，则 $c(q,r)=0$，故 $J_q(v)|_{T_r}=0$。
在 $T_q$ 上它是 $g_q(v,\cdot)$，因此对所有 $z\in N_p$ 已有

$$
J_q(v)(z)=g_q(v,P_qz).
\tag{VIII109.15}
$$

现在比较另一对径对 $q',r'$。对 $w\in T_{q'}$，在(VIII109.11)中
对 $g_q$ 单位向量 $v$ 取上确界，并使用(VIII109.15)，得到

$$
\begin{aligned}
 g_q(P_qw,P_qw)&\le c(q,q')g_{q'}(w,w),\\
 g_r(P_rw,P_rw)&\le(1-c(q,q'))g_{q'}(w,w),\\
 G_{q,r}(w,w)&\le g_{q'}(w,w).
\end{aligned}
\tag{VIII109.16}
$$

若 $T_q=0$，第一式的左侧为零，仍成立；另一零块同理。
第二式的系数来自 $c(r,q')=1-c(q,q')$，两式针对同一个 $w$。
对 $w\in T_{r'}$ 同样成立，只交换 $c$ 与 $1-c$。

置 $G'=G_{q',r'}$、$k=\dim N_p$。选一组 $G'$ 正交归一基，
分别由 $T_{q'}$、$T_{r'}$ 的正交归一基拼成。
只在这两块上使用(VIII109.16)并相加，准确给出

$$
\operatorname{tr}(G'^{-1}G_{q,r})\le k.
\tag{VIII109.17}
$$

这里没有把块上二次型界擅自提升为整个空间的Loewner界。
交换两对径对，得到 $\operatorname{tr}(G_{q,r}^{-1}G')\le k$。
若 $k=0$，结论平凡。否则相对正定算子的正特征值记为 $\lambda_1,\ldots,\lambda_k$；
两条迹界给

$$
\sum_j\lambda_j\le k,\quad \sum_j\lambda_j^{-1}\le k,
\quad 0\le\sum_j(\lambda_j+\lambda_j^{-1}-2)\le0.
\tag{VIII109.18}
$$

每一项都非负，故全部 $\lambda_j=1$。
相对算子与实对称正定矩阵相似，因而可对角化；全部特征值为一迫它是恒等，
即 $G_{q,r}=G'$。

共同 $G$ 本来就按每一对的直和定义，所以 $P_q$ 真正自伴随，
且(VIII109.15)成为(VIII109.14)的 $J_q$ 式。
对 $w\in T_{q'}$，(VIII109.16)前两式的左侧和现为 $G(w,w)=g_{q'}(w,w)$，
右侧和也相等；两个非负亏量只能分别为零。
于是 $G(P_qw,P_qw)=c(q,q')G(w,w)$。
在 $T_{q'}$ 上极化，并用各投影自伴随，得
$P_{q'}P_qP_{q'}=c(q,q')P_{q'}$。
交换标签给另一式。此证明不要求交叉配对非退化、相应矩阵为方阵，
也不在迹比较前假设两个 $G$ 相同。证毕。

### 109.5 退化分支与只沿邻球循环的等秩

**定理 109.6（无需全纯连通前件的局部等秩）。** 假设W和TRI2。
若某个 $M_q=V$，原锥已是VIII108.12的同单位
$\mathbb R\oplus\operatorname{spin}_{d_q}$。
若全部 $d_q=1$，原锥已是VIII107.2的经典三角形。
在排除这两个分支后，可选一个厚点 $p$，并存在整数 $m\ge1$，使

$$
\begin{gathered}
d_p=d_q=d_r=m+1\quad
(q\in P\cap D_p,\ r=2c_p-q),\\
\dim T(q\mid p)=m,\qquad \dim N_p=2m,\qquad n=3(m+1).
\end{gathered}
\tag{VIII109.19}
$$

此处不先声称全部 $P$ 连通、同维或已是流形。

证明。前两分支直接引用上述既有定理；它们不要求G。
其余分支中每个 $N_q$ 非零，且至少一个 $d_p\ge2$。
固定这样的 $p$，109.5已给共同 $G$ 和等倾式。

先排零秩邻点。若 $T_q=0$，其对径 $r$ 满足 $P_r=I_{N_p}$。
因 $d_p\ge2$，球面 $P\cap D_p\simeq S^{d_p-1}$ 中可选
$s\ne q,r$，所以 $0<c(r,s)<1$。
等倾式给 $P_s=c(r,s)I_{N_p}$。
$N_p\ne0$，这与 $P_s^2=P_s$ 矛盾。因此每个 $T_q$ 均有正秩。

当 $c(q,s)>0$ 时，$P_qP_sP_q=c(q,s)P_q$ 使
$P_s:T_q\to T_s$ 注入：若 $P_sv=0$，则 $c(q,s)v=0$。
交换两点也注入，故维数相同。非对径不同点的 $c$ 在 $(0,1)$ 中；
对径点可用第三点连接。因此全部邻点的切秩同为某个 $m\ge1$，
而任一对径的饱和直和给 $\dim N_p=2m$。
此处只在同一底球面内用第三点连接对径标签；$d_p\ge2$ 的底球面连通，
所用第三点总可选，没有使用整个 $P$ 的连通性。

现在取其中任意 $q$ 及其对径 $r$。
已有 $d_q=d_r=m+1\ge2$，且全局排除了 $M_q=V$，故可在 $q$ 处重复刚才的论证。
它的排除球邻点包含 $p,r$；这些邻点的切秩相同，迫
$d_p-1=d_r-1=m$。
最后 $n=d_p+2+\dim N_p=(m+1)+2+2m=3(m+1)$。
整个循环只经过 $p$ 的邻球和一个邻点，没有隐藏的全局连通或流形假设。证毕。

### 109.6 等倾反射的线性与全部剩余切向量的覆盖

**定理 109.7（真实球丛与切覆盖）。** 在109.6的其余分支，固定所得厚点 $p$，
将 $L_p$ 用 $g_p$ 识别为 $\mathbb R^{m+1}$。
对 $x\in S^m$ 置

$$
r(x)=c_p+x,\qquad q(x)=c_p-x,\qquad
P_x=P_{q(x)},\qquad A_x=2P_x-I_{N_p}.
\tag{VIII109.20}
$$

$P_x$ 投影到 $T(q(x)\mid p)$，即含直径 $p,r(x)$ 的原球在 $p$ 处的切空间。
则 $A_x$ 对称，并且

$$
\begin{gathered}
A_xA_y+A_yA_x=2(x\cdot y)I,
\qquad A_x=\sum_{i=1}^{m+1}x_iA_{e_i},\\
\mathscr E=\{(x,z)\in S^m\times N_p:P_xz=z\}
\text{ 是光滑秩 }m\text{ 实向量子丛},\\
N_p\setminus\{0\}=\coprod_{x\in S^m}
 \bigl(\operatorname{im}P_x\setminus\{0\}\bigr).
\end{gathered}
\tag{VIII109.21}
$$

每个非零 $z$ 因而有唯一标签 $x(z)$，并满足

$$
\|P_yz\|_G^2=\frac{1+y\cdot x(z)}2\|z\|_G^2
\quad(y\in S^m).
\tag{VIII109.22}
$$

证明。109.5的等倾系数在此重标号下仍为 $(1+x\cdot y)/2$，
且 $P_{-x}=I-P_x$。相对于 $\operatorname{im}P_x\oplus\ker P_x$，
令 $t=x\cdot y$。等倾式分别给 $A_y$ 的两个对角块为 $tI,-tI$，
而 $A_x=\operatorname{diag}(I,-I)$。
直接块乘得到反对易式，不需要预先对 $x\mapsto P_x$ 作连续性假设。

令 $H_x=\sum_i x_iA_{e_i}$。正交基上的反对易式给 $H_x^2=I$，
而全部 $x,e_i$ 的反对易式给 $A_xH_x+H_xA_x=2I$。
所以对称算子 $D=A_x-H_x$ 满足 $D^2=0$。
对所有 $z$ 有 $\|Dz\|_G^2=G(z,D^2z)=0$，故 $D=0$。
因此 $A_x$ 是一个线性算子值映射的球面限制，$P_x=(I+A_x)/2$ 光滑。
这里的Clifford关系用于线性化，没有调用Clifford模分类、Hurwitz或Adams定理。

还须证明子丛的局部平凡化。固定 $x_*$，选 $N_p$ 中 $m$ 个固定向量 $v_j$，
使 $P_{x_*}v_j$ 线性独立。某个坐标 $m\times m$ minor非零；
连续性使它在邻域 $U$ 内仍非零。
于是 $P_xv_1,\ldots,P_xv_m$ 是 $\operatorname{im}P_x$ 的光滑局部标架。
映射 $(x,t)\mapsto(x,\sum_jt_jP_xv_j)$ 给 $U\times\mathbb R^m$ 的平凡化；
逆系数由同一个可逆minor求出，故光滑。
再对该标架作 $G$ 的Gram—Schmidt，得到光滑正交归一标架。
因此单位球丛

$$
\mathscr U=\{(x,z):x\in S^m,\ P_xz=z,\ \|z\|_G=1\}
\tag{VIII109.23}
$$

局部为 $U\times S^{m-1}$，是无边界的 $(2m-1)$ 维流形。
$m=1$ 时纤维为零维流形 $S^0$，同一结论仍成立。
$\mathscr U$ 是紧空间 $S^m\times S(N_p)$ 的闭子集，故紧且Hausdorff。

评价映射 $e:\mathscr U\to S(N_p)$、$(x,z)\mapsto z$ 连续。
若 $e(x,z)=e(y,w)$，则 $z=w\ne0$；VIII108.6的切空间零交迫 $x=y$，
所以它注入。紧域到Hausdorff空间的连续单射是嵌入。
目标 $S(N_p)\simeq S^{2m-1}$ 是连通的同维流形，因为 $m\ge1$。
现在准确应用[Hatcher][Q109H] Theorem 2B.3及Corollary 2B.4（印刷p172）：
紧 $n$ 维流形嵌入连通 $n$ 维流形，像既开又闭，因而满射。
该推论不要求域先连通；这里的维数来自已经构造的局部平凡化，不是形式减维。
于是每个单位剩余向量被某张切空间接住；齐次缩放和零交给(VIII109.21)。
最后用 $P_{x(z)}z=z$ 及
$P_{x(z)}P_yP_{x(z)}=((1+y\cdot x(z))/2)P_{x(z)}$，
在 $z$ 上取 $G$ 二次型，即得(VIII109.22)。证毕。

### 109.7 一颗原纯星上的全空间原尺

**定理 109.8（原纯星及其准确Riesz尺度）。** 保持109.7的厚点 $p$，
在原直和 $V=\mathbb Rp\oplus\mathbb Rc_p\oplus L_p\oplus N_p$ 上定义
正定对称双线性型

$$
\begin{aligned}
B(\alpha p+\beta c_p+y+z,\alpha'p+\beta'c_p+y'+z')
 =\alpha\alpha'+\frac{\beta\beta'}2+
 \frac{g_p(y,y')}2+\frac{G(z,z')}2.
\end{aligned}
\tag{VIII109.24}
$$

定义固定 $p$ 的原纯星和它的凸锥包

$$
\mathcal S_p=\bigcup_{q\in P\cap D_p}(P\cap D_q),\qquad
C_{\star}=\operatorname{cone}(\mathcal S_p),
\tag{VIII109.25}
$$

其中 $\operatorname{cone}$ 指有限非负线性组合。$\mathcal S_p$ 紧，包含 $p$ 和
$P\cap D_p$；它的全部点恰有下列球内参数化：

$$
\begin{gathered}
s=A p+B_0r(x)+z_s,\qquad x\in S^m,\quad A,B_0\ge0,\quad A+B_0=1,\\
z_s\in\operatorname{im}P_x,\qquad \|z_s\|_G^2=4AB_0.
\end{gathered}
\tag{VIII109.26}
$$

对每个这样的原纯点，其原least尺在整个 $V$ 上满足

$$
a_s=B(s,\cdot).
\tag{VIII109.27}
$$

证明。原正交关系在紧 $P^2$ 中闭：将其原效应见证放在紧 $\mathcal E$ 中取极限即可。
因此 $\{(q,s)\in(P\cap D_p)\times P:q\perp s\}$ 紧，
其第二因子投影正是 $\mathcal S_p$。
每个邻点 $q$ 都有 $p\in D_q$；对任意 $r\in P\cap D_p$，其对径 $q$ 满足
$r\in D_q$，故所述包含关系成立。

球 $D_{q(x)}$ 的中心为 $(p+r(x))/2$，其单位直径方向为
$(p-r(x))/2$，切方向空间是 $\operatorname{im}P_x$。
该球自己的内积在切空间上已由109.5认同为 $G$。
把球面点分成直径和切方向，得到 $A+B_0=1$、
$(A-B_0)^2+\|z_s\|_G^2=1$；这正是(VIII109.26)，且该式的每组参数都给球面原纯点。
它不是另加的星点或新的纯态定义。

对任意 $v=\alpha p+\beta c_p+y+z$，原尺在 $M_p$ 上的直径公式及
VIII108.2的共同零方向给

$$
a_p(v)=\alpha,\qquad
 a_{r(x)}(v)=\frac{\beta+x\cdot y}{2},\qquad
 a_p|_{N_p}=a_{r(x)}|_{N_p}=0.
\tag{VIII109.28}
$$

特别地 $B(p,\cdot)=a_p$、$B(r(x),\cdot)=a_{r(x)}$ 在全 $V$ 上成立。
若 $z_s\ne0$，对球 $D_{q(x)}$ 使用同一 $\Lambda_{q(x)}$：
球面直径效应的限制等式经其线性性延拓为

$$
a_s=Aa_p+B_0a_{r(x)}+\tfrac12J_{q(x)}(z_s)
\quad\text{于整个 }V.
\tag{VIII109.29}
$$

109.4给 $J_{q(x)}(z_s)|_{M_p}=0$；109.5在
$N_p=T(q(x)\mid p)\oplus T(r(x)\mid p)$ 上准确给
$J_{q(x)}(z_s)(z)=G(z_s,z)$。
所以(VIII109.29)正是由(VIII109.24)计算的 $B(s,\cdot)$。
这同时核对了 $M_p$ 与整个 $N_p$，没有只在一张球上核对后宣称全空间相等。
若 $z_s=0$，(VIII109.26)迫 $AB_0=0$，故 $s=p$ 或 $r(x)$，
已由(VIII109.28)处理。系数确为 $B|_{N_p}=G/2$，与原圆弧尺中的 $J/2$ 一致。
此步仍未使用全纯互易。证毕。

### 109.8 星锥的直接自对偶与原锥夹逼

**定理 109.9（不经Jordan分类的原星锥自对偶）。** 在109.8的条件及尺度下，

$$
C_{\star}^{*B}:=\{v\in V:B(v,s)\ge0\ (s\in\mathcal S_p)\}
 =C_{\star}=C.
\tag{VIII109.30}
$$

因此 $K=\operatorname{conv}\mathcal S_p$，全部原纯点准确为 $P=\mathcal S_p$，
且(VIII109.27)对全部原纯点成立。

证明。$\mathcal S_p\subseteq P\subseteq C$ 给 $C_{\star}\subseteq C$。
109.8已在全原空间证明 $B(s,\cdot)=a_s\in C^*$，所以

$$
C_{\star}\subseteq C\subseteq C_{\star}^{*B}.
\tag{VIII109.31}
$$

因为 $D_p=\operatorname{conv}(P\cap D_p)$ 且这些原纯点已在星中，
有 $\operatorname{cone}D_p\subseteq C_{\star}$。
只须从星自身的参数证明反向包含。写任意待判向量为
$v=\alpha p+\beta c_p+y+z$，$y\in L_p,z\in N_p$。
由于正倍缩放不影响星锥，(VIII109.26)中的 $A,B_0$ 可取任意非负值，
相应 $\|z_s\|_G=2\sqrt{AB_0}$；两者全零时只给零向量。
对固定 $x,A,B_0$，在整个切球面上最小化横向方向，得到准确读数

$$
\min_{z_s}B(Ap+B_0r(x)+z_s,v)
 =A\alpha+B_0\frac{\beta+x\cdot y}{2}
       -\sqrt{AB_0}\,\|P_xz\|_G.
\tag{VIII109.32}
$$

横向项原本为 $G(z_s,z)/2$，这解释最后一项没有额外的二或二分之一。
$P_xz=0$ 时任意允许方向都取同一横向值零。
令 $a=\sqrt A,b_0=\sqrt{B_0}$，这是
$\alpha a^2+h_xb_0^2-\|P_xz\|_G ab_0$，其中 $h_x=(\beta+x\cdot y)/2$。
在 $a,b_0\ge0$ 上非负的充要条件是两端系数非负且判别式不正：
必要性可先取一个变量为零，再最小化另一变量；充分性由配方或
$\alpha a^2+h_xb_0^2\ge2\sqrt{\alpha h_x}ab_0$ 得到。
因此星对偶的准确条件为

$$
\alpha\ge0,\quad h_x\ge0,\quad
\alpha\frac{\beta+x\cdot y}{2}
 \ge\frac{\|P_xz\|_G^2}{4}\quad(x\in S^m).
\tag{VIII109.33}
$$

先处理 $\alpha=0$。末式迫所有 $P_xz=0$；109.7的切覆盖使 $z=0$。
余下 $h_x\ge0$ 对全部 $x$ 等价于 $\beta\ge\|y\|_p$。
故 $v=\beta c_p+y\in\operatorname{cone}D_p\subseteq C_{\star}$。
这也包括 $\beta=0$ 时必有 $y=0$ 的锥顶。

再处理 $\alpha>0,z=0$。条件仍恰为 $\beta\ge\|y\|_p$，
故 $v=\alpha p+(\beta c_p+y)\in C_{\star}$。

最后取 $\alpha>0,z\ne0$，令 $x_0=x(z)$，并置

$$
b=\frac{\|z\|_G^2}{4\alpha}>0.
\tag{VIII109.34}
$$

由(VIII109.22)，(VIII109.33)的末式准确化为

$$
\begin{aligned}
\alpha(\beta+x\cdot y)
 &\ge \frac{1+x\cdot x_0}{4}\|z\|_G^2
       =\alpha b(1+x\cdot x_0)\quad(x\in S^m),\\
\beta-b&\ge\|y-bx_0\|_p.
\end{aligned}
\tag{VIII109.35}
$$

第一行由原式乘二而得，且与第二行等价；它也已保证 $h_x\ge0$。
于是有同一原向量的实际正分解

$$
\begin{gathered}
v=v_0+v_1,\qquad
v_0=\alpha p+b r(x_0)+z,\qquad
v_1=(\beta-b)c_p+(y-bx_0),\\
\frac{v_0}{\alpha+b}\in\mathcal S_p,\qquad
v_1\in\operatorname{cone}D_p.
\end{gathered}
\tag{VIII109.36}
$$

第一项确为星纯射线：$P_{x_0}z=z$，
$\|z\|_G^2=4\alpha b$，除以原质量 $\alpha+b>0$ 后正好满足(VIII109.26)。
第二项由(VIII109.35)的球锥条件得到。
若残量系数为零，范数界也迫其方向为零，所以没有遗漏该极点情形。
以上覆盖全部对偶向量，故 $C_{\star}^{*B}\subseteq C_{\star}$。
结合(VIII109.31)，三个锥相等。

为核对紧星和全部原pure的最后一步，有限维Carathéodory定理使
$K_{\star}=\operatorname{conv}\mathcal S_p$ 紧，且其中每点原质量为一。
其锥闭：若 $t_jk_j$ 收敛，原质量给 $t_j=u(t_jk_j)$ 收敛；
取 $k_j$ 的紧子列，极限仍在该锥中，包括 $t_j\to0$ 的情形。
锥相等与原质量一给 $K=K_{\star}$。
若原极点 $s\in P$ 写成有限个星点的凸组合，极端性迫每个正权重星点都等于 $s$，
故 $s\in\mathcal S_p$。反向包含已在星的定义中成立。
这没有先用Jordan、滤子保纯、全Pair或全纯数值互易。证毕。

### 109.9 完整条件重构与真实Peirce反向

**定理 109.10（三元二面可辨的同锥同单位重构）。** 在定义109.1的原有限维
全态、全效应域中，下列条件等价：

$$
\boxed{\begin{aligned}
&\mathsf W+\mathrm{TFD}_3;\\
&\mathsf W+\mathrm{TRI2};\\
&\exists\text{有限维秩三EJA }J,\quad
 \Phi:J\overset{\sim}{\longrightarrow}V,\quad
 \Phi(J_+)=C,\quad u\Phi=\operatorname{tr}_J.
\end{aligned}}
\tag{VIII109.37}
$$

这里 $\operatorname{tr}_J$ 是每个本原幂等元取一的规范迹。
在固定W域中，TFD3和TRI2还分别等价于VII106.10的
PAIRJET2、JET2、H2、CUB3、PL3、完整 $S$、全Pair和原面格覆盖律。
共同中心G、滤子保纯和全部原纯点的数值互易是所得后果。

证明。109.3给前两项的等价。
从W与TRI2出发，109.6先处理某个 $M_q=V$ 及全部 $d_q=1$ 的分支；
它们已有同锥同单位秩三EJA表示，不必强行进入非零球丛论证。
在其余分支，109.5—109.9给原全空间上的正定 $B$，并对全部原纯点给

$$
a_s(t)=B(s,t)=B(t,s)=a_t(s)\quad(s,t\in P),\qquad
 a_s\le f\quad(f\in F_s)
\text{ 于整个 }C^*\text{ 序}.
\tag{VIII109.38}
$$

第二部分正是W内VII105.3的全域least，没有把它省略为唯一确认或球上最小。
所以同一个原 $V,C,u,K,P,[0,u]$ 满足完整 $S$。
现在直接消费[完整S桥][Q109S]的
“Reciprocal least confirmation and the spectrality bridge”及
“Least confirmation forces face-filter purity”，并按VII103.4、VII105.8的原域接口使用：
原全proper least与全纯数值互易供应正对偶剥离、忠实自对偶配对、
有符号框架谱性、正面投影、projectivity及面滤波保纯，
最后才使用[Barnum—Müller—Ududec][Q109BMU] Theorem 16。
该定理的三个输入是projectivity、transition reciprocity及filter purity，
这里由完整S桥分别供应；不把第三项藏在无三阶干涉的字眼中。
W已有原面高三，故所得EJA秩为三；同一原单位由该桥的归一接口对应规范迹。
这给(VIII109.37)的正向。

反向从同单位秩三EJA出发，VII103.6—103.7已逐项给全部原效应、
原least、完整排除球及全Pair，因此W成立。
还须核对本章的原 $\Pi_p$ 确为成熟Peirce压缩。
在 $J$ 中对本原幂等元 $e_i$，记 $L_a(b)=a\circ b$，
二次表示为 $U_a=2L_a^2-L_{a^2}$。
设单位为 $e$，则

$$
R_i(v)=\operatorname{tr}_J(e_i\circ v)e_i,
\qquad \Pi_i=U_{e-e_i}.
\tag{VIII109.39}
$$

第二式的认同可由原延拓唯一性直接核对。
$U_{e-e_i}$ 是成熟的正Peirce压缩，杀掉 $e_i$，固定其互补面的整个锥。
对任意正泛函 $f$，$f\circ U_{e-e_i}$ 正、在 $e_i$ 读零，且在 $D_{e_i}$ 上限制为 $f$；
VII105.4的限制双射迫它等于 $\Lambda_i\operatorname{res}_if$。
正对偶锥生成全部对偶空间，故认同对所有泛函成立，得到原算子等式，
而不是仅找到了同像的另一个投影。

取任一完整Jordan框架 $(e_1,e_2,e_3)$，成熟Peirce公式为

$$
\begin{gathered}
J=\bigoplus_{i=1}^3\mathbb Re_i\ \oplus J_{12}\oplus J_{13}\oplus J_{23},\\
\Pi_1=R_2+R_3+P_{23},\quad
\Pi_2=R_1+R_3+P_{13},\quad
\Pi_3=R_1+R_2+P_{12},\\
I=R_1+R_2+R_3+P_{12}+P_{13}+P_{23}.
\end{gathered}
\tag{VIII109.40}
$$

$P_{ij}$ 是相应Peirce块的投影，允许该块为零。
例如 $e-e_1$ 的乘法在互补代数、$J_{12}\oplus J_{13}$、$\mathbb Re_1$
上的特征值分别为 $1,1/2,0$，故 $U_{e-e_1}=2L^2-L$ 分别取 $1,0,0$，
准确得到第二行。三式相加再减三个 $R_i$ 即为TRI2。
这些公式适用于所有有限EJA，包括Albert和直和分支，不用结合矩阵公式替代八元分支。
原joint在同单位字典下正是这些完整本原框架，故量词是全部原joint。
最后在同一W域直接复用VII106.10的既有等价链，取得所列全部比较条件和G。
正向推导在取得完整S之前没有使用这条链，故没有循环。证毕。

本定理在109.4—109.9增加的是从原三元滤子关系到共同切度量、全切覆盖、
全空间原尺和原星锥夹逼的纸面充分推导。
其最终Jordan桥是上述既有桥与成熟Theorem 16的应用。
特别地，BMU Proposition 29的“无三阶干涉当且仅当滤子保纯”以其Postulates 1和2为前提，
其中已含强对称；本证明没有把该命题搬到裸W域，也没有借它预付保纯或互易。

### 109.10 全三球的最小维数与复三能级

**推论 109.11（全三球下一个框架足够，单张三球仍不够）。** 在W下再假设

$$
\forall s\in P,\qquad D_s\simeq_{\rm aff}B^3.
\tag{VIII109.41}
$$

则 $n\ge9$，并且以下条件等价：任意指定的一个原joint框架满足TRI2；
至少一个原joint框架满足TRI2；全部原joint框架满足TRI2；$n=9$；
存在同原锥同原单位的 $H_3(\mathbb C)$ 表示。
因此在全部完整排除球为三球的W模型类中，最小实维数九恰好选择复三能级。

证明。VIII108.7在W中已给 $n\ge9$，仍是原域必要界。
109.3对每个框架给 $\dim Z_F=n-(3+3+3)=n-9$。
所以一个框架恒等当且仅当 $n=9$，而此时每个框架都恒等；原joint非空。
109.10随后给同单位秩三EJA。
依VII103.7、VII106.17已注明来源的成熟有限EJA分类，秩三非简单分支为
$\mathbb R^3$ 或 $\mathbb R\oplus\operatorname{spin}_d$，都有排除线段；
简单分支及全部排除球维数为

$$
\begin{array}{c|c|c}
J&n&d_s\ (s\in P)\\ \hline
H_3(\mathbb R)&6&2\\
H_3(\mathbb C)&9&3\\
H_3(\mathbb H)&15&5\\
H_3(\mathbb O)&27&9
\end{array}
\tag{VIII109.42}
$$

全部三球只保留复型；反向该复型的成熟Peirce公式给TRI2及 $n=9$。
分类在109.10的完整重构之后才使用，不是从Clifford关系先猜允许维数。

若只要求存在一张三球，结论不成立。
VIII108.12—108.13的同单位 $\mathbb R\oplus\operatorname{spin}_3$ 满足W、G和TRI2，
实维数五；旗标的整个排除集是三球，球纯点的整个排除集却是线段。
它不是复三能级。这准确保留了(VIII109.41)的全部量词。
VIII108.7的必要界没有被改判；新增的是加上全三球后九维的充分性。证毕。

### 109.11 旧静态量子公理和其余原合同

**命题 109.12（原全态、全效应与Born的逐项回接）。** 在W、TFD3及全部三球下，
有同一个实线性双射 $\Phi:H_3(\mathbb C)\to V$，使

$$
\begin{gathered}
\Phi(\operatorname{Herm}_+(\mathbb C^3))=C,\qquad
u(\Phi X)=\operatorname{tr}X,\\
K=\{\Phi\rho:\rho\succeq0,\ \operatorname{tr}\rho=1\},\qquad
P=\{\Phi(vv^*):v\in\mathbb C^3,\ v^*v=1\},\\
\mathcal E=\{f_E:f_E(\Phi X)=\operatorname{tr}(EX),\quad0\preceq E\preceq I_3\},\\
a_{\Phi(vv^*)}(\Phi\rho)=\operatorname{tr}(vv^*\rho),\qquad
T_{\Phi(vv^*)}(\Phi(ww^*))=|v^*w|^2.
\end{gathered}
\tag{VIII109.43}
$$

全部有限数学测量恰对应 $E_j\succeq0,\sum_jE_j=I_3$；原纯点几何为
$\mathbb{CP}^2$，原共同中心为 $\Phi(I_3)/3$。
这些结论不缩小原态或原效应集，也不更换原单位。

证明。109.10—109.11供应VII106.17的全部静态前件。
同锥同单位双射将整个对偶锥拉回PSD迹对偶，补效应正性将其区间准确截为
$0\preceq E\preceq I_3$。least确认在该字典中是秩一投影自身，
所以原全部混态的确认概率为迹配对，纯—纯时等于模方。
效应和为原 $u$ 正好对应矩阵和为 $I_3$。
以上是既有完整字典的同域应用，不是另输入Born概率。
数学测量是否为实际可调用菜单仍按原过程合同决定。证毕。

**命题 109.13（全有限层级、CP、实际事件与钟的条件接口）。** 对VII106.16的同一
原装饰元组，在其允许选择的秩三载体上，可将几何项
$\mathsf W_X+\mathrm{PAIRJET2}_X$ 等价替换为
$\mathsf W_X+\mathrm{TFD}_{3,X}$；其全部非几何消费者和未选载体逐字保留。
对[全有限复C星层级VII][Q109Hierarchy]，准确接口为：

| 原目标 | 仍保留的条件及本章供应 |
| --- | --- |
| 单载体原 $S_1$ 与秩三 | 本章109.10供应；全部三球再供应复三能级 |
| 该卷102章的全层级路线 | 保留102.1的全有限强分块域、原 $S_3$ 及B1—B3；本章不供应三份比较 |
| 该卷103章的较低比较路线 | 保留同一层级域、$S_2+\mathsf F$ 和103.1三项具名低二份PAPER供应 |
| 该卷104章的单最大叉口路线 | 保留104.1的同一原域、$S_2$、三项具名低二份PAPER供应及非经典支路的 $\mathsf F_{\max}$；全经典支路不要求资源 |
| 数学全旁观正性与CP/Kraus | 在上述全层级结论之后，使用该卷103.10、102.13及104章相应接口 |
| 实际事件、仪器、条件更新和Lüders | 继续保留原共同来源、可实施菜单、分支预算、合法未来及事件饱和选择 |
| 物理时间、Hamiltonian、单位及 $\hbar$ | 继续保留原钟、动态族、单位和过程合同；静态几何不制造这些数据 |

证明。109.10与VII106.10同在原W域，故替换逐载体成立；
VII106.16中原准备、测试、过程、参考、读回、共同来源、记录、权限、控制、
ready/flags、失败/拒绝/停止/销毁/返回、实际混合、合法未来、旧支撑和中间切口
仍按其原定义与原量词保留。
包括其原像紧与全部中点实现、非负质量与零和不等质量、完整相关联合域、
同一 $L,p,\omega$、全实关系、两尺度等式、同事件提升、相容核和每个资格态的条件，
均没有因几何替换而删除；VII106.16引用的原生及细化消费者也不换对象。

为明确最新层级入口，104.1的三项具名供应分别是：
在原 $q=1,2$ 上从least／谱性／面投影与保纯取得Jordan的桥；
唯一实际自复合 $(W_1,W_1,W_2)$ 的直和扇区限制、秩与实维乘法的复型选择；
原实际两因子产品正规形。
$S_1$ 可由该层级的 $S_2$ 下降，本章不能反向把 $S_1$ 升成 $S_2$。
全有限域还要求全部 $W_N=V^{\otimes_{\mathbb R}N}$、每个实际分块的min/max双界、
同一原产品配对、严格张量单位、全部原极点、全效应、原正置换和规范重括号。
这些联合条件不由一个秩三状态体自动供应。

在该卷104.2的共同局部迹坐标下，$\mathsf F_{\max}$ 要求某个最大块
$r$、$n_r=L\ge2$ 的同一含相位正交基满足

$$
g_r=\sum_{a=1}^{L}|a\rangle_r|a\rangle_r|a\rangle_r,
\qquad\Delta_r=|g_r\rangle\langle g_r|\in C_3,
\qquad u_3(\Delta_r)=L.
\tag{VIII109.44}
$$

其余三份扇区取零，$\Delta_r/L$ 才是原归一源；不预付三份纯性、整锥PSD或实际制备。
该卷104.10在上述完整供应下证明
$S_2+\mathsf F_{\max}\Longleftrightarrow S_2+\mathsf F$
等价于全部有限原锥在同一保迹局部坐标的张量幂下为标准复矩阵块PSD。
因此本章单体结论能接入该条件链，却没有消除 $S_2$ 或叉口资源。

全层级取得后，原数学全旁观正性才按既有自身Choi桥对应通常CP，
矩形跨扇区Kraus与逐输入TP/TNI预算按该卷102.13、103.10读取。
把所有数学CP-TNI分支纳入实际事件，需要其102.14的额外饱和选择；
仪器和Lüders按102.15、103.12以及VII106.16的同来源合同消费。
恒等时间族和非平凡Hamiltonian时间族可以保持同一静态态—效应数据，
所以本章静态恒等式不选择实际钟或 $\hbar$。
若单体为复三能级，其二、三份秩为九、二十七，不能对这些高阶载体同时要求秩三W。
这保留完整量子起源目标的复合与动态部分，而没有将单体重构冒作其完成。证毕。

### 109.12 未证自动性、成熟归属与完整白话

**约定 109.14（准确条件边界与来源）。** 109.2—109.10中从原W滤子到跨球切收缩、
双向迹拼合、局部等秩、真实球丛覆盖、全空间星尺及原星锥夹逼的组合推导按
`repo-derived` 归属。无三阶干涉的包含—排除式及二缝线性重构已有
[UBE Proposition 1及Appendix][Q109UBE]的明确先例；
不变域的使用严格限于[Hatcher Theorem 2B.3、Corollary 2B.4][Q109H]；
原least、共同延拓、正投影和切空间零交分别复用VII105.2—105.5、VIII108.4—108.7。
最终完整S到EJA的接口与成熟分类、Born字典分别沿[原Library桥][Q109S]、
VII103.4—103.7及VII106.17使用；本章不重证这些成熟结论。
BMU Theorem 16与Proposition 29的前提区别按109.10保留。
这些是纸面条件推导，不宣称内核验证、全球原创、文献穷尽或独立最少公理数。

以下自动性仍未由本章证明或反驳：

$$
\mathsf W\ \Longrightarrow\ \mathrm{TRI2},\qquad
\mathsf W+\mathrm G\ \Longrightarrow\ \mathrm{TRI2}.
\tag{VIII109.45}
$$

所以VIII108.16的一般W或W加G的覆盖与二阶拼合问题仍保留；
本章只在追加TRI2后证明它们成立。
这里的“未证”表示尚无所需推导或同域反例，不声称形式不可判定性或逻辑独立性。
109.3说明任何失败框架如何在同一模型中产生两真实原态的联合盲区，
但没有因此构造出满足W而失败TRI2的模型。
同样，109.11的复型选择以全部原排除球为三球为条件，不能用存在一张三球替换。

**命题 109.15（三张完整二元窗口如何锁定同一几何）。** 本章的数学内容可完整解释如下。

证明与解释。首先仍只有原来的全部态和全部零一效应。
每个纯态背后，所有能被确认它的某张尺完全排除的原态，已经按W组成一个完整实心球。
W还把正交的两个纯点补成一个原三元框架，并为每张球确定共同的正线性读回。
新的关系只说：固定任意这样一个框架，收齐所有至少在三个框架点之一读零的原效应，
它们合起来必须区分任意两个原态。每一张窗口内允许完整的二元信息；
不是只留下三个接受概率，也不是声称每个窗口单独足以看清整个状态。

109.2—109.3说明这条话准确禁止一个三阶共同盲核。
若它非零，原状态体的内部允许沿它正反微移成两个真实态；
三张完整读回看到的结果一模一样，原全效应却仍能把它们分开。
禁止这种盲核，等价于把整个原向量精确重构为三张二元读回之和，
再扣掉重复计入的三个单点读回。它同时把VIII108的维数不等式压成等号。

接着固定一个纯点。背后球的每个纯邻点，又有一张经过这个固定点的原球。
沿每张球面伸出的切箭头原来各有自己的长度，不同标签不能共用非零箭头。
三元恒等式先保证任一对径标签的两组箭头恰好线性填满剩余空间。
用一张球的原非负尺去读另一张球的真实圆弧，得到跨球收缩。
若按两种对径拆法分别量长，在对方每个块上的总平方长度都只能缩小；
把各块相加得到互为倒数的两条迹界。
两条界一起迫所有相对伸缩因子等于一，所以长度真正拼成同一个内积。
此时各组箭头才成为同一内积下的正交投影，并具有准确的等倾夹角。

这一约束也排除了厚球旁边的零秩切空间。
沿一张底球，再在一个邻点处循环，已经足以迫出所需的局部同秩，
不用先宣布整个纯态集连通或光滑。
等倾投影的反射满足反对易式；对称性使其随底球坐标线性变化。
这才产生真实的光滑向量子丛。它的单位球丛紧、与全部单位剩余箭头同维，
而不同标签零交使评价注入。不变域于是保证每根剩余箭头恰被一张球接住。
这里用拓扑取得覆盖，不用预先列出Hopf或Clifford模的全部类型。

然后只看固定点周围这一颗原纯星。
原圆弧效应的共同延拓把每颗星点的原尺在整个空间上锁成同一对称配对，
包括剩余方向上的二分之一尺度。
若某个原向量对所有星点都非负，109.9的二次式判据把它分成两件：
一条真实的星纯射线和背后实心球锥中的正残量。
零质量边界和零横向分量分别处理，不靠极限猜测。
因此星生成的锥恰为自己的对偶；原锥既包含它，又因原正效应而被其对偶包含，
两边夹逼迫原锥与星锥相等。星紧且本来全是原pure，原状态体的全部极点于是也都在星上。
到这一步才取得全部原纯点的数值互易；原全域least早已由W给出，
两者共同满足既有完整S桥，再到同原锥同原单位的秩三Jordan几何。

若每一张完整排除球都是三球，原维数至少九；
维数恰九正好使三张读回没有剩余盲核，因而足以给复三能级的全部密度态、全部效应与Born概率。
若只看到一张三球，经典旗标加spin三球已经是另一种模型，不能选出复三能级。
最后，单体几何不等于实际过程：复合仍需同一全有限模型的联合条件，
CP的数学识别仍需该层级，实际事件、条件更新和物理钟仍需原供应。
因而新关系给出一条完整的单载体条件重构，
一般W是否自动满足它以及完整动态的起源仍是明确保留的原目标。证毕。

[Q109UBE]: https://arxiv.org/pdf/0909.4787v1 "Cozmin Ududec, Howard Barnum and Joseph Emerson, Three slit experiments and the structure of quantum theory, Proposition 1 and Appendix; standing condition of unique neutral complemented filters."
[Q109H]: https://pi.math.cornell.edu/~hatcher/AT/ATch2.pdf "Allen Hatcher, Algebraic Topology, Theorem 2B.3 and Corollary 2B.4, printed p172."
[Q109S]: ../../../Library/QuantumStates/mullerududec2012selfduality.md#reciprocal-least-confirmation-and-the-spectrality-bridge
[Q109BMU]: https://arxiv.org/html/1403.4147v4 "Howard Barnum, Markus P. Müller and Cozmin Ududec, Higher-order interference and single-system postulates characterizing quantum theory, Theorem 16 and Proposition 29."
[Q109Hierarchy]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md

## 追加锚（本行以下为增补区）

## 110. 原弱球关系的混合边界收缩、纯点ENR与框架和路径

### 110.1 原域、相对边界与球心集合

**定义 110.1（只使用原W的拓扑对象）。** 采用107.1及VII105.1的同一个
非零有限维实空间 $V$、闭尖生成凸锥 $C$、在 $C\setminus\{0\}$ 上严格正的
原泛函 $u$、整个原基 $K=C\cap\{u=1\}$、全部原纯点
$P=\operatorname{ext}K$，以及全部原效应 $\mathcal E=[0,u]_{C^*}$。明确地，

$$
\begin{gathered}
F_p=\{f\in\mathcal E:f(p)=1\},\qquad
T_p(x)=\min_{f\in F_p}f(x),\qquad
D_p=\{x\in K:T_p(x)=0\},\\
p\perp q\ \Longleftrightarrow\
\exists f\in\mathcal E:\ f(p)=1,\ f(q)=0,\\
\mathsf W=\mathrm{EB}_{\ge1}+\mathrm{Pair}_{\perp},\qquad
\mathrm{EB}_{\ge1}:\ D_p\simeq_{\rm aff}B^{d_p},\ d_p\ge1\ (p\in P),\\
\mathrm{Pair}_{\perp}:\quad
p,q\in P,\ p\perp q\ \Longrightarrow\ H(p,q)\ne K.
\end{gathered}
\tag{VIII110.1}
$$

$x$ 在最低读数与零集定义中遍历整个原 $K$，包括全部混态；
$H(p,q)$ 是原最小面，$B^{d_p}$ 是整个闭欧氏球。
假设始终只有 $\mathsf W$，不要求球维数相同或全部至少为二。
记

$$
\begin{gathered}
N=\dim V,\qquad S=\partial K,\qquad M=S\setminus P,\\
U(p)=p+2c_p,\qquad B=\{c_p:p\in P\},\qquad c(p)=c_p,
\end{gathered}
\tag{VIII110.2}
$$

其中 $\partial K$ 指 $\operatorname{aff}K$ 内的相对边界，$c_p$ 是完整 $D_p$ 的球心。
此处 $B$ 是球心集合，不是单个标准球；$U$ 是向量值函数，不是原泛函 $u$。
不输入G、全纯互易、共同内积、对称群、纯点光滑性或纯点基数条件。

直接复用VII103.2、104.2—104.7及105.9：全部非空原真面只有纯单点与
非点暴露极大真面 $D_p$；不同的这些球若相交，交点只能是一个原纯点；
$p\mapsto D_p$ 双射；$P$ 紧；每个纯点进入原joint三框架；
$U$ 连续，且在原正交纯对上取相同值。若 $(p,q,r)$ 是这样的框架，则

$$
p+q+r=U(p)=U(q)=U(r),\qquad H(q,r)=D_p.
\tag{VIII110.3}
$$

三张原效应的Kronecker读数使框架三点线性独立，故 $N\ge3$。
$C$ 生成 $V$ 给 $\operatorname{affdim}K=N-1$，所以 $S$ 的球面维数是 $N-2$。
VII105.2—105.5的least与数学projectivity、107的全线段刚性及108的切空间结果
保留其各自陈述；下述收缩不以G或108中的附加覆盖条件为前件。

### 110.2 混合边界的唯一球标签与强形变收缩

**定理 110.2（整个混合边界收缩到全部排除球心）。** 在原 $\mathsf W$ 下，
每个 $x\in M$ 恰属于一个完整排除球的相对内部。以此定义 $\sigma(x)\in P$，则

$$
\begin{gathered}
M=\coprod_{p\in P}\operatorname{ri}D_p,\qquad
\sigma:M\longrightarrow P\text{ 连续},\qquad
c:P\overset{\sim}{\longrightarrow}B\text{ 为同胚},\\
\sigma c=\operatorname{id}_P,\qquad
H:M\times[0,1]\longrightarrow M,\qquad
H(x,t)=(1-t)x+t c_{\sigma(x)}.
\end{gathered}
\tag{VIII110.4}
$$

这里 $\coprod$ 只表示集合的不交分解，不宣称其拓扑是离散指标的不交和。
$H$ 是 $M$ 到 $B$ 的强形变收缩；特别地 $M\simeq P$。

证明。每个边界点都有一个经过它的支撑真面。
若 $x$ 非纯，该面不能是纯单点，真面穷尽使它等于某张 $D_p$。
闭欧氏球相对边界上的全部点都是这个球的极点，且面中极点仍为整个 $K$ 的极点，
所以非纯 $x\in D_p$ 必在 $\operatorname{ri}D_p$。
反向，$d_p\ge1$ 使每个球内点都位于球中两个不同点的开线段上，故不纯。
不同 $D_p$ 不能共有非纯点，点球双射遂给唯一标签与所述分解。
特别地每个 $c_p\in M$，$B\subset M$ 且 $M$ 非空。

标签连续性须在原域证明。整个 $\mathcal E$ 紧，$P,K$ 也紧。
评价映射连续，故

$$
\begin{aligned}
\widetilde Z&=\{(p,x,f)\in P\times K\times\mathcal E:
                         f(p)=1,\ f(x)=0\},\\
Z&=\{(p,x)\in P\times K:x\in D_p\}
\end{aligned}
\tag{VIII110.5}
$$

分别是紧集与其紧投影。第二个等式确实成立，因为原 $F_p$ 紧，
最低读数为零时有一张原效应达到零。因此 $Z$ 是闭关联集，
这里没有把纯目标零关系或所选效应菜单当作整个关联集。

若 $x_j\to x$ 于 $M$，任何子列的标签 $\sigma(x_j)$ 均有收敛子子列，设极限为 $p$。
闭关联给 $x\in D_p$，非纯点的唯一标签迫 $p=\sigma(x)$。
$P$ 紧且可度量，故整列标签收敛到 $\sigma(x)$，即 $\sigma$ 连续。
由VII105.9，$c_p=(U(p)-p)/2$ 连续。
若 $c_p=c_q$，这个共同混合点属于两球，唯一性迫 $D_p=D_q$，继而 $p=q$。
所以连续 $c$ 是紧空间 $P$ 到Hausdorff空间 $B$ 的双射，必为同胚，
且 $\sigma(c_p)=p$。

$P$ 在 $S$ 中闭，所以 $M$ 在 $S$ 中开。
公式中的两端都在同一球的相对内部，整条连接线段也在该相对内部。
因此 $H$ 的每个值都在 $M$；由 $c\sigma$ 连续，$H$ 作为到 $V$ 的映射连续，
于是作为到子空间 $M$ 的映射也连续。此外

$$
H(x,0)=x,\qquad H(x,1)=c_{\sigma(x)},\qquad
H(c_p,t)=c_p.
\tag{VIII110.6}
$$

这正是强形变收缩；再用 $B\cong P$ 即得同伦等价。
证明没有选取随 $p$ 连续变化的球图，也没有要求不同 $d_p$ 相同。证毕。

### 110.3 全部原纯点的局部可缩性、ENR与有限道路分支

**定理 110.3（原P的邻域正则性）。** 在原 $\mathsf W$ 下，$P$ 是紧Euclidean
neighborhood retract（ENR），且在如下明确意义下局部可缩：对每个 $p\in P$
及其任意开邻域 $O\subseteq P$，存在开邻域 $A$，$p\in A\subseteq O$，
使包含映射 $A\hookrightarrow O$ 零伦。$P$ 局部道路连通，
只有有限多个道路连通分支，它们也恰是连通分支。
$P$ 可嵌入为某个有限单纯复形的收缩核，故其整数奇异同调群有限生成并在高维为零。

证明。取任意 $z\in\operatorname{ri}K$，在 $\ker u$ 上任选辅助欧氏范数。
每条从 $z$ 出发的射线与 $K$ 相交于一个非退化有界闭区间，恰有一个边界端点。
因此

$$
S\longrightarrow S^{N-2},\qquad
x\longmapsto\frac{x-z}{\|x-z\|}
\tag{VIII110.7}
$$

连续且双射，紧性使它为同胚。故开子空间 $M$ 是拓扑 $(N-2)$ 维流形，
无需假设凸边界光滑。110.2给连续收缩 $r=c\sigma:M\to B$。

固定 $y\in B$ 和其在 $B$ 中的开邻域 $O_B$。
在开集 $r^{-1}(O_B)$ 内取以 $y$ 为中心的流形坐标球 $W$。
坐标线性收缩给 $h:W\times[0,1]\to W$，起于恒等、终于 $y$ 并固定 $y$。
令 $A_B=W\cap B$，则 $A_B\subseteq O_B$，而

$$
(a,t)\longmapsto r(h(a,t)),\qquad a\in A_B,
\tag{VIII110.8}
$$

在 $O_B$ 内把包含 $A_B\hookrightarrow O_B$ 收缩到 $y$。
经同胚 $c$ 运输，给出陈述中的 $A\hookrightarrow O$ 零伦。
这恰是Hatcher《Algebraic Topology》[Theorem A.7，印刷p.525][Q110H]
使用的弱局部可缩定义；不声称 $A$ 在其自身内可缩。

对 $P$ 的任意开子集 $O$ 及 $p\in O$，上述同伦使 $A$ 的每一点都能在 $O$ 内
沿道路连到 $p$。因此 $O$ 中 $p$ 所属的道路分支含 $p$ 的一个开邻域。
对该分支的每一点如此做，说明 $O$ 的每个道路分支均开；
这些开道路分支构成道路连通邻域基，故 $P$ 局部道路连通。
特别地 $P$ 自身的道路分支均开，且构成紧 $P$ 的一个开覆盖，故只有有限多个。
其补集也是开集，故各分支闭；一个连通子集不能横跨这些开闭分支，
所以道路分支与连通分支相同。

$P\subset V\cong\mathbb R^N$ 紧，且已证明A.7的全部局部假设。
该定理遂给 $P$ 在这个欧氏嵌入中的一个开邻域到 $P$ 的收缩。
Hatcher [Corollary A.8，印刷p.527][Q110H]又给有限单纯复形 $L$
及嵌入 $j:P\hookrightarrow L$、收缩 $\rho:L\to P$，满足 $\rho j=\operatorname{id}_P$。
于是每个 $H_i(P;\mathbb Z)$ 是 $H_i(L;\mathbb Z)$ 的直和因子，
故有限生成；$i>\dim L$ 时为零。
这些成熟拓扑工具是在已构造的原W收缩内应用，不另作纯点正则性假设。证毕。

### 110.4 原纯点的Alexander同调自对偶与Euler限制

**定理 110.4（精确维数移位与偶N约束）。** 在原 $\mathsf W$ 下，对
$0\le i\le N-3$ 有整数奇异群同构

$$
\widetilde H_i(P;\mathbb Z)
 \cong\widetilde H^{\,N-i-3}(P;\mathbb Z),
\qquad
H_i(P;\mathbb Z)=0\quad(i\ge N-2).
\tag{VIII110.9}
$$

波浪号分别表示约化同调与约化上同调，右侧不是同次数的同调群。
普通Euler特征在此定义为有限和

$$
\chi(P)=\sum_{i\ge0}(-1)^i
             \dim_{\mathbb Q}H_i(P;\mathbb Q).
\tag{VIII110.10}
$$

当原向量空间维数 $N$ 为偶数时，必有 $\chi(P)=1$。

证明。$P$ 非空，110.2给 $c_p\in S\setminus P$，所以它是 $S$ 的真子集。
110.3已给 $P$ 紧且局部可缩，以及 $S\cong S^{N-2}$。
令 $n=N-2\ge1$。Hatcher [Corollary 3.45，印刷pp.255—256][Q110H]
对紧、局部可缩、非空的真子集 $P\subset S^n$ 给出

$$
\widetilde H_i(S\setminus P;\mathbb Z)
 \cong\widetilde H^{\,n-i-1}(P;\mathbb Z).
\tag{VIII110.11}
$$

110.2的同伦等价将左侧换成 $\widetilde H_i(P;\mathbb Z)$，
而 $n-i-1=N-i-3$，即得所述范围的自对偶。
这里两侧约化的零次群也包括在内，不能将右端零次群改为普通上同调。

再从非空 $S\setminus P$ 取一点 $a$。
去点球面 $S\setminus\{a\}\cong\mathbb R^{N-2}$ 使 $P$ 成为其中的紧局部可缩子空间。
Hatcher [Corollary 3.46，印刷p.256][Q110H]因此直接给
$H_i(P;\mathbb Z)=0$ 对所有 $i\ge N-2$ 成立。
这使用的是此实际嵌入和已得局部可缩性，而非预设 $P$ 的流形维数。

由110.3的有限生成性，令
$b_i=\dim_{\mathbb Q}\widetilde H_i(P;\mathbb Q)$。
整数通用系数定理及(VIII110.9)给

$$
b_i=b_{N-3-i}\quad(0\le i\le N-3),\qquad
\chi(P)-1=\sum_{i=0}^{N-3}(-1)^i b_i.
\tag{VIII110.12}
$$

当 $N$ 偶时，$N-3$ 奇，互补指标的符号相反且没有固定指标，
所以有限和逐对消去，得到 $\chi(P)=1$。
此计算允许 $P$ 不连通，也没有忽略整数群的挠部分来声称更强的整数同调对称。
若 $N$ 奇，该配对不强迫同样的Euler数值。证毕。

### 110.5 框架和下降到整个边界及其像的正则性

**定理 110.5（连续边界下降与内部重心紧集）。** 在原 $\mathsf W$ 下，存在唯一
连续映射 $b:S\to V$，使对每个原纯 $p$ 都有

$$
\begin{gathered}
b(x)=U(p)\quad(x\in D_p),\qquad b|_P=U,\qquad b(S)=U(P).
\end{gathered}
\tag{VIII110.13}
$$

$U(P)$ 紧、道路连通且局部连通，且

$$
U(P)/3\subset\operatorname{ri}K,
\qquad
\inf_{p\in P}\operatorname{dist}(U(p)/3,\partial K)>0
\tag{VIII110.14}
$$

对任一固定的辅助范数成立。这里的重心随 $p$ 变化，不预设G。

证明。使用(VIII110.5)的紧关联集 $Z$，令
$\pi:Z\to S$ 为第二坐标投影。
所有 $D_p$ 都是真面，故像在 $S$ 中。
非纯边界点由真面穷尽属于某个 $D_p$；纯点 $x$ 进入一组三框架，
从而也属于框架另一点的完整排除球。因此 $\pi$ 满射。

连续映射 $Z\to V$，$(p,x)\mapsto U(p)$，在 $\pi$ 的每个纤维上常值。
对混合 $x$，球标签唯一；对纯 $x\in D_p$，原正交边常值性给 $U(p)=U(x)$。
紧到Hausdorff的连续满射是商映射，故存在唯一连续下降 $b$。
它在每个 $D_p$ 上的值、在纯点上的限制及整个像均如陈述。
这些球覆盖 $S$，也给唯一性。

$N\ge3$ 使 $S\cong S^{N-2}$ 道路连通，故 $U(P)=b(S)$ 道路连通；
它又是紧 $P$ 的连续像，所以紧。
局部连通性还须使用110.3。置 $Y=U(P)$，连续满射 $U:P\to Y$ 是商映射。
对任意开 $O\subseteq Y$，$U^{-1}(O)$ 是局部连通空间的开子空间，
其每个连通分支均在 $P$ 中开。每个这样的分支的连续像连通，
故落在 $O$ 的某一个连通分支内。
因此 $O$ 的任意连通分支 $Q$ 的原像 $U^{-1}(Q)$ 是这些开分支的并，
在 $P$ 中开；商性质给 $Q$ 在 $Y$ 中开。
所以每个开集的连通分支均开，即 $Y$ 局部连通。

对任意 $p$，选原框架 $(p,q,r)$，于是 $w_p=U(p)/3=(p+q+r)/3\in K$。
若 $w_p$ 在边界，它所在的支撑真面 $F$ 由正的三个重心系数必同时包含 $p,q,r$。
故 $D_p=H(q,r)\subseteq F$。$D_p$ 的极大真面性迫 $F=D_p$，
与 $p\notin D_p$ 矛盾。所以每个 $w_p\in\operatorname{ri}K$。
连续像 $U(P)/3$ 紧，且与闭集 $\partial K$ 不交，给严格正的统一距离。
所有重心均为原 $K$ 中的态；没有从它们的内点性推出它们彼此相等。证毕。

### 110.6 G失败必在一条真实连续纯路径上发生

**推论 110.6（非恒定框架和的纯路径及不交球族）。** 在原 $\mathsf W$ 下，
若G失败，则存在连续 $\gamma:[0,1]\to P$，满足
$U(\gamma(0))\ne U(\gamma(1))$。
沿这条路径可选出连续统多个原纯源 $p_s$，使其 $U(p_s)$ 两两不同、
完整 $D_{p_s}$ 两两不交。
更一般地，任意 $U(p)\ne U(q)$ 的原纯对均不共处任何真面，且

$$
(1-t)p+tq\in\operatorname{ri}K\quad(0<t<1).
\tag{VIII110.15}
$$

证明。110.3给有限多个道路分支 $P_1,\ldots,P_k$。
若 $U$ 在每个分支上都常值，$U(P)$ 就是有限集；
110.5的道路连通性迫它是单点，从而G成立。
所以G失败时，至少一个 $P_i$ 上有两点的框架和不同。
道路分支定义给连接这两点的所述 $\gamma$。

选线性泛函 $\ell\in V^*$ 分离这两个框架和。
连续函数 $g(t)=\ell(U(\gamma(t)))$ 的像含一个非退化闭区间 $I$。
对每个 $s\in I$ 可具体取

$$
t_s=\min\{t\in[0,1]:g(t)=s\},\qquad p_s=\gamma(t_s).
\tag{VIII110.16}
$$

非空紧原像保证该最小值存在，且 $\ell(U(p_s))=s$，所以不同参数给不同框架和。
这里不声称 $s\mapsto t_s$ 或 $s\mapsto p_s$ 连续，
也不要求 $\gamma$ 单射、光滑或可求长。

若 $U(p)\ne U(q)$ 而 $D_p\cap D_q$ 含混合点，110.2的唯一标签给 $p=q$，矛盾。
若交中有纯点 $a$，则 $a\perp p,q$，边常值性给 $U(p)=U(a)=U(q)$，仍矛盾。
因而这些框架和不同的完整球两两不交。
若 $p,q$ 共处一个真面，它不可能是单点，只能是某个 $D_a$，
又会给 $U(p)=U(a)=U(q)$，矛盾。
最后，若一条严格弦点 $(1-t)p+tq$ 在边界，经过它的支撑真面由两个正系数
必同时包含 $p,q$，与前一结论矛盾，故得到(VIII110.15)。
这给任何潜在G反例的必要结构，没有构造这样的反例。证毕。

### 110.7 谱迹、成熟重构与独立原合同的边界

**开放问题 110.7（尚缺的路径常值与二阶拼合）。** VII106.11在同一原W域给

$$
\mathrm G\ \Longleftrightarrow\ \tau\text{ 线性}
\ \Longleftrightarrow\ \mathrm{J1}.
\tag{VIII110.17}
$$

因此110.6把可能的G失败定位到一个道路分支中的真正连续纯路径，
但110.2—110.6没有证明 $U$ 沿这样的路径常值，也没有证明
$\tau(f+g)=\tau(f)+\tau(g)$ 对全部 $f,g\in V^*$ 成立。
原 $\mathsf W\Rightarrow\mathrm G$ 仍未在这里证明或反驳。
即使另得G，VII106.15的 $\mathsf W+\mathrm G\Rightarrow\mathrm{JET2}$
仍要求跨方向的共同二次形；本章未由ENR、同调对偶或局部连通性取得它。
也未推出TCov、常球维数、局部平凡球丛、全局兼容内积或完整PL3。

110.2—110.6是原W几何与标准拓扑的 `repo-derived` 连接；
Hatcher的邻域收缩与Alexander对偶只在各证明所列参数和假设内使用。
其他成熟重构结果保持其全部条件：
Alfsen—Shultz [*State spaces of Jordan algebras*, Corollary 7.5及Theorem 7.2的(i)、(iii)][Q110AS]
要求Hilbert ball property与每个norm-exposed face的projectivity。
VII105.5已经供应原数学projectivity，但Hilbert ball property量化任意二纯点的面；
本章的整个排除球与ENR结论不替代这一量词，不能据此直接调用该分类。
Müller—Ududec [Theorem 1][Q110MU]的bit symmetry、
Barnum—Hilgert [Theorem 1.1][Q110BH]的spectrality与strong symmetry，
以及Niestegge [Theorem 3][Q110N]中包括对称transition probability的全部前件，
均没有因原纯点成为ENR而自动成立。这些成熟结论不是本章新增的重构定理。

107的无G全线段三角形与108的切方向互斥、维数和低维分类直接保留；
本章不重证这些结论，也不从其必要条件倒推一般厚球分类。
[全有限层级VII][Q107Hierarchy]102.1、103.1及104.11—104.13的原强分块域、
具名低二份供应与rank-two $\mathsf{Fusion}_L$ 合同独立保留：
二维角寄存器成果不因这里的单载体收缩而供应 $L>2$ 的原融合态。
指定复合、同事件CP、实际仪器与记录、共同来源、历史和原物理钟／单位仍按各自原合同使用。
已经从明确动态或时钟前提得到的条件定理继续按那些前提成立；
这里的辅助道路参数既不提供物理速度，也不识别某个原物理时间作用。
[OTF-001][Q110OTF]的G/M/S/R/C/J/I明确模型按自身条件评价，
不把无前提宇宙唯一性添作其数学结论的前件。

### 110.8 从边界球心到纯路径的完整几何解释

**命题 110.8（原W正则性与剩余差别的白话表述）。** 只用(VIII110.1)的原全态、
全效应弱球关系，可以把全部混合边界连续收缩到与全部纯点一一同胚的球心集合；
由此得到的是原纯点本身的邻域正则性及拓扑限制，而非附加正则性公理。

证明与解释。原状态体的每个真正边界面，要么只有一个纯点，要么是某个纯点背后的
完整排除球。一个非纯边界点只能在其中一张球的内部；若两张球都收留它，
就违反既有真面相交规律。于是每个这样的点都有唯一的球标签。
全效应紧性保证点接近时标签也接近；球心又由连续框架和决定。
把每个混合边界点沿本球内的直线推向球心，就得到同时连续的收缩，
无需先把所有球做成等维球丛。不同纯点的球心不同，所以全部球心保留了全部纯点的拓扑。

整个凸边界本来同胚于一个球面，去掉闭纯点集后仍是一个开流形。
球心集合是它的收缩核，因此在一个指定小区域附近，
还可找到更小的区域，让它在前一个区域内连续缩成一点。
这正好足以让原纯点成为欧氏邻域收缩核，并排除无限多个互相分离的道路分支。
它并不说纯点都是孤立点，也不说每个小邻域本身就是球。

混合边界与纯点具有同一同伦类型；另一方面，它们又互为同一球面中的补集。
Alexander对偶把这两种关系合起来，迫使纯点的约化同调与互补次数的约化上同调相等。
当原向量维数为偶数时，相配的约化Betti数在Euler交错和中符号相反，
所以普通Euler特征只能为一。这里允许整数挠群，也允许纯点不连通。

每个原三框架还有一个三点和。沿一张完整排除球，这个和不能改变，
所以它可以连续下降到整个凸边界；其全部取值因而形成一个道路连通的紧集，
三分之一的每个取值都严格落在原状态体内部。
若不同框架的和真不一样，有限多个纯道路分支中至少一个必须承载这种变化。
因此不能把潜在失败只藏在彼此不通的纯点块之间：必有一条实际连续的纯路径见证它，
并能沿路径选出连续统多个框架和不同、背后完整球互不相交的纯点。
这些点的严格连接弦均穿过整体内部。

最后仍缺的是排除这种路径上的框架和变化。
连续、局部可缩、有限道路分支和同调自对偶都没有在这里证明该变化为零；
它们也没有把二阶读数拼成同一个二次形，更没有创造指定复合、事件或物理时钟。
这正是110.2—110.7的完整结论及其范围。证毕。

[Q110H]: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf "Allen Hatcher, Algebraic Topology: Theorem A.7, Corollary A.8, pp.525–527; Corollaries 3.45–3.46, pp.255–256."
[Q110AS]: https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6236-11511_2006_Article_BF02392307.pdf "E. M. Alfsen and F. W. Shultz, State spaces of Jordan algebras, Acta Mathematica 140, 155–190: Theorem 7.2 and Corollary 7.5."
[Q110MU]: https://arxiv.org/pdf/1110.3516v2 "Markus P. Müller and Cozmin Ududec, Structure of reversible computation determines the self-duality of quantum theory, Theorem 1."
[Q110BH]: https://arxiv.org/pdf/1904.03753v1 "Howard Barnum and Joachim Hilgert, Strongly symmetric spectral convex bodies are Jordan algebra state spaces, Theorem 1.1."
[Q110N]: https://arxiv.org/pdf/2312.13213v2 "Gerd Niestegge, Theorems 2–3: finite capacity and the stated order-unit hypotheses; Theorem 3 additionally requires symmetric transition probability."
[Q110OTF]: OTF_001_ORTHOGONAL_TIME_FIELD_THEORY.md "OTF-001, sections 2 and 14–15."

## 追加锚（本行以下为增补区）

## 111. 一组三元二面可辨、双侧正性等号与原纯确认尺的盲核自检测

### 111.1 同一原域中只存在一组的附加关系

**定义 111.1（存在式三元二面可辨）。** 始终采用109.1的同一个非零有限维实
$V$、闭尖生成锥 $C$、严格正原单位 $u$、整个原紧基
$K=C\cap\{u=1\}$、全部原纯点 $P=\operatorname{ext}K$ 和全部原效应
$\mathcal E=[0,u]_{C^*}$，并假设
$\mathsf W=\mathrm{EB}_{\ge1}+\mathrm{Pair}_{\perp}$。
原确认仍为对整个 $F_p=\{f\in\mathcal E:f(p)=1\}$ 取最小值，
原完整排除集仍为整个 $D_p=\{x\in K:T_p(x)=0\}$。
直接复用W已给的全锥序least尺 $a_p$、完整排除球
$D_p=c_p+\{v\in L_p:g_p(v,v)\le1\}$、共同正线性延拓 $\Lambda_p$、
原正投影 $\Pi_p$ 及原joint三框架。
框架 $F=(p_1,p_2,p_3)$ 指三个两两原正交的原纯点；W已给
$a_{p_1}+a_{p_2}+a_{p_3}=u$，每个原纯点均可进入这种框架。

本章的附加关系只要求**存在一组**这样的框架：

$$
\begin{aligned}
\mathrm{TFD}_{3,\exists}:\quad
&\exists\text{原joint }F=(p_1,p_2,p_3)\quad
 \forall x,y\in K,\ x\ne y,\\
&\qquad\exists i\in\{1,2,3\}\ \exists f\in\mathcal E:\quad
 f(p_i)=0,\qquad f(x)\ne f(y).
\end{aligned}
\tag{VIII111.1}
$$

这是一条原态—原效应二元评价的零关系与分离关系，
只把三张完整零效应面联合起来使用。
它不要求任一张球独自区分全态，也不只读取三个标量 $a_{p_i}(x)$。
它不以全框架可辨、共同中心G、全Pair、全纯数值互易、滤子保纯、
全局内积、切丛覆盖或二阶光滑度为输入。
109章的全框架条件 $\mathrm{TFD}_3$ 保持原义；本章将它作为待推出的后果。

**定理 111.2（存在式关系的原算子、维数与三球张成表述）。** 固定任意原joint
$F=(p_1,p_2,p_3)$。对互异 $i,j,k\in\{1,2,3\}$ 置

$$
\begin{gathered}
R_i(v)=a_{p_i}(v)p_i,\qquad
E_{ij}=\Pi_{p_k}-R_i-R_j,\qquad V_{ij}=\operatorname{im}E_{ij},\\
\mathcal I_F=I-\Pi_{p_1}-\Pi_{p_2}-\Pi_{p_3}+R_1+R_2+R_3,\qquad
\pi_F=I-\mathcal I_F,\qquad V_F=\operatorname{im}\pi_F,\qquad
Z_F=\operatorname{im}\mathcal I_F.
\end{gathered}
\tag{VIII111.2}
$$

该框架满足(VIII111.1)中 $\exists F$ 之后的分离条件，当且仅当下列任一条件成立：

$$
\begin{gathered}
\mathcal I_F=0;\qquad Z_F=0;\qquad V_F=V;\qquad
n=d_{p_1}+d_{p_2}+d_{p_3};\\
\operatorname{span}(D_{p_1}\cup D_{p_2}\cup D_{p_3})=V;\qquad
v\longmapsto(\Pi_{p_1}v,\Pi_{p_2}v,\Pi_{p_3}v)
\text{ 在 }V\text{ 上注入};\\
x\longmapsto(\Pi_{p_1}x,\Pi_{p_2}x,\Pi_{p_3}x)
\text{ 在整个 }K\text{ 上注入}.
\end{gathered}
\tag{VIII111.3}
$$

因此 $\mathrm{TFD}_{3,\exists}$ 等价于这些条件对至少一个原joint成立。
这里的 $\operatorname{span}$ 是三张完整原仿射球作为 $V$ 的子集所生成的线性空间。

证明。直接消费109.2—109.3的七投影代数、共同核、维数及全态分离等价。
它们在裸W域对任意固定框架成立，无须输入G。
为核对这里增加的张成写法，由109.2有

$$
\begin{gathered}
V_F=\bigoplus_{i=1}^3\mathbb Rp_i\ \oplus\!\bigoplus_{i<j}V_{ij},
\qquad V=V_F\oplus Z_F,\\
V_F=\operatorname{span}(D_{p_1}\cup D_{p_2}\cup D_{p_3}).
\end{gathered}
\tag{VIII111.4}
$$

后一等式的正向包含由六个块逐项给出：$p_i\in D_{p_j}$ 对 $i\ne j$，
而 $V_{ij}\subseteq\operatorname{span}D_{p_k}$。
反向包含用 $\mathcal I_F\Pi_{p_i}=0$ 及
$\operatorname{im}\Pi_{p_i}=\operatorname{span}D_{p_i}$。
其余等价与非零有符号核产生两个真实归一态的处理，均正是109.3，
不再重证。证毕。

### 111.2 任意固定框架上由两侧正性给出的同尺度范数界

**定理 111.3（原可见六块的两侧球界）。** 只假设W，固定任意原joint $F$，
尚不假设 $\mathcal I_F=0$。在(VIII111.4)的代数直和上定义正定对称型 $h_F$：
六个块彼此正交，三个 $p_i$ 为正交单位向量，且

$$
\begin{gathered}
h_F|_{V_{ij}}=\tfrac12 g_{p_k}|_{V_{ij}},\qquad
U_F=p_1+p_2+p_3,\qquad
h_F(U_F,v)=u(v)\quad(v\in V_F),\qquad
\|U_F\|_{h_F}^2=u(U_F)=3.
\end{gathered}
\tag{VIII111.5}
$$

对每个原 $f\in V^*$，记 $Y_f\in V_F$ 为其限制 $f|_{V_F}$ 的Riesz向量，
即 $h_F(Y_f,v)=f(v)$ 对全部 $v\in V_F$ 成立。
则对全部非负质量原向量和全部原正效应尺度，有

$$
\boxed{\quad
\|\pi_F v\|_{h_F}\le u(v)\quad(v\in C),\qquad
\|Y_f\|_{h_F}\le f(U_F)\quad(f\in C^*).
\quad}
\tag{VIII111.6}
$$

特别地 $\|\pi_F x\|_{h_F}\le1$ 对整个原 $K$ 成立。
$Y_f$ 是原正泛函的限制所对应的向量；此处不把它当作原正态，
也不主张 $\pi_F$、$E_{ij}$ 或 $\mathcal I_F$ 保正。

证明。对互异 $i,j,k$，W已给 $p_i,p_j$ 是 $D_{p_k}$ 的对径。
因此

$$
\begin{gathered}
c_{p_k}=\frac{p_i+p_j}{2},\qquad
 e_{ij}=\frac{p_i-p_j}{2},\qquad g_{p_k}(e_{ij},e_{ij})=1,\\
L_{p_k}=\mathbb Re_{ij}\oplus V_{ij},\qquad
 g_{p_k}(e_{ij},V_{ij})=0.
\end{gathered}
\tag{VIII111.7}
$$

这正是109.2的切块及VIII108.5的球内直径公式：
在 $L_{p_k}$ 上 $a_{p_i}(z)=g_{p_k}(e_{ij},z)/2$，而 $V_{ij}$ 是其核。
三个 $V_{ij}$ 允许为零空间。$u$ 在各 $V_{ij}$ 上为零，在每个 $p_i$ 上取一，
故按块定义确实给正定 $h_F$，并给(VIII111.5)，没有先对整个 $V$ 指定内积。

先证明状态侧。取任意 $v\in C$，写
$t_i=a_{p_i}(v)\ge0$、$m=u(v)=\sum_i t_i$、$z_{ij}=E_{ij}v$。
原 $\Pi_{p_k}$ 保正，且正像恰为 $\operatorname{cone}D_{p_k}$，所以

$$
\begin{aligned}
\Pi_{p_k}v
 &=t_i p_i+t_j p_j+z_{ij}\\
 &=(t_i+t_j)c_{p_k}+(t_i-t_j)e_{ij}+z_{ij}
 \in\operatorname{cone}D_{p_k}.
\end{aligned}
\tag{VIII111.8}
$$

球锥的准确条件及(VIII111.7)给

$$
(t_i-t_j)^2+g_{p_k}(z_{ij},z_{ij})\le(t_i+t_j)^2,
\qquad
\|z_{ij}\|_{h_F}^2\le2t_it_j.
\tag{VIII111.9}
$$

若 $t_i+t_j=0$，两个质量均零，球锥只能给零向量，故 $z_{ij}=0$；
(VIII111.9)仍成立。若一项质量为零，也由该式迫切块为零。
把三个不同球锥所得的界放回同一个原向量的六块，得到

$$
\|\pi_Fv\|_{h_F}^2
 =\sum_i t_i^2+\sum_{i<j}\|z_{ij}\|_{h_F}^2
 \le\sum_i t_i^2+2\sum_{i<j}t_it_j=m^2.
\tag{VIII111.10}
$$

这包括任意非负 $m$；$m=0$ 时原严格正单位使 $v=0$。
没有对 $\pi_Fv$ 的原锥正性作任何使用。

再证明效应侧，独立于状态侧的投影解释。
取任意 $f\in C^*$，令 $s_i=f(p_i)\ge0$。Riesz向量的分块准确为

$$
Y_f=\sum_i s_i p_i+\sum_{i<j}y_{ij},\qquad
 y_{ij}\in V_{ij},\qquad
 f(z)=\frac12g_{p_k}(y_{ij},z)\quad(z\in V_{ij}).
\tag{VIII111.11}
$$

在整个原球 $D_{p_k}$ 上，任意点可写为
$c_{p_k}+\tau e_{ij}+z$，其中 $z\in V_{ij}$、
$\tau^2+g_{p_k}(z,z)\le1$。
原正泛函在该整球上的值和最小值分别为

$$
\begin{aligned}
f(c_{p_k}+\tau e_{ij}+z)
 &=\frac{s_i+s_j}{2}+\frac{s_i-s_j}{2}\tau
       +\frac12g_{p_k}(y_{ij},z),\\
\min_{D_{p_k}}f
 &=\frac{s_i+s_j}{2}
   -\sqrt{\left(\frac{s_i-s_j}{2}\right)^2
                     +\frac14 g_{p_k}(y_{ij},y_{ij})}\ \ge0.
\end{aligned}
\tag{VIII111.12}
$$

这是同一球的欧氏对偶范数公式；零系数时最小值在整球或相应直径上达到。
特别地 $g(y_{ij},y_{ij})/4=\|y_{ij}\|_{h_F}^2/2$，
不是 $\|y_{ij}\|_{h_F}^2$。因此准确得到

$$
\left(\frac{s_i+s_j}{2}\right)^2
 \ge\left(\frac{s_i-s_j}{2}\right)^2+\frac{\|y_{ij}\|_{h_F}^2}{2},
\qquad
\|y_{ij}\|_{h_F}^2\le2s_is_j.
\tag{VIII111.13}
$$

当 $s_i+s_j=0$ 或某个端点读数为零，所写切块同样被迫为零；
零维切块时也适用。正性只给 $s_i\ge0$，不要求 $f\le u$，
所以任意正倍尺度都保留。相加即得

$$
\|Y_f\|_{h_F}^2
 =\sum_i s_i^2+\sum_{i<j}\|y_{ij}\|_{h_F}^2
 \le\left(\sum_i s_i\right)^2=f(U_F)^2.
\tag{VIII111.14}
$$

$f(U_F)\ge0$，取非负平方根得到效应侧结论。
若 $f(U_F)=0$，则所有这些系数均零，$Y_f=0$；
当 $V_F\ne V$ 时，这一步不声称原 $f$ 必为零。
两侧推导均在W中完成，未使用G、全纯互易或状态谱性。证毕。

### 111.3 一处没有盲核就迫出全原空间的共同配对

**定理 111.4（单框架的双侧取等与共同重心）。** 在W下，若某个原joint
$F_0$ 满足 $\mathcal I_{F_0}=0$，则 $V_{F_0}=V$。
置 $B=h_{F_0}$、$U=U_{F_0}$。对每个原纯点 $x$ 有

$$
\|x\|_B=1,\qquad Y_{a_x}=x,\qquad
 a_x=B(x,\cdot)\quad\text{于整个原 }V.
\tag{VIII111.15}
$$

对任意原joint $F=(x,y,z)$，都有 $x+y+z=U$；
因而对全部原纯点 $p$ 都有 $p+2c_p=U$，即G成立。
而且 $U\in\operatorname{int}C$、$U/3\in\operatorname{ri}K$，
$B$ 是全部原纯尺共同决定的唯一配对，满足
$B(U,\cdot)=u$ 和全部原纯点的数值互易。

证明。这里只对 $F_0$ 假设无盲核。111.3在全 $V$ 上给
$\|x\|_B\le1$、$\|Y_{a_x}\|_B\le a_x(U)$。
原 $a_x(x)=1$，所以Cauchy—Schwarz给每个原纯点

$$
1=a_x(x)=B(Y_{a_x},x)
 \le\|Y_{a_x}\|_B\|x\|_B\le a_x(U).
\tag{VIII111.16}
$$

任取 $x$，用W将其补成一个原joint $(x,y,z)$。
对这三个点分别使用(VIII111.16)，每项下界为一，而

$$
a_x(U)+a_y(U)+a_z(U)=u(U)=3.
\tag{VIII111.17}
$$

故三项都恰为一。由于每个原纯点均可这样完成框架，
$a_x(U)=1$ 对全部 $x\in P$ 成立。
于是(VIII111.16)整串取等：两个范数均不超过一，内积却为一，
迫两个范数各等于一且Cauchy—Schwarz取正号等式。
亦可直接算 $\|Y_{a_x}-x\|_B^2=1+1-2=0$。
因此 $Y_{a_x}=x$，并在整个 $V$ 上得到(VIII111.15)；
并非只在某张排除球或某个可见子空间上认同原尺。

现在才可对任意另一个原joint $(x,y,z)$ 相加原尺：

$$
B(x+y+z,\cdot)=a_x+a_y+a_z=u=B(U,\cdot).
\tag{VIII111.18}
$$

$B$ 正定使 $x+y+z=U$。对任意 $p$，取其完整 $D_p$ 的任一直径端点
$q,r$，原joint性质给 $p+q+r=U$，而 $q+r=2c_p$。
这得到G，没有在取等之前使用框架和相同或全纯互易。
对任意 $p,q\in P$，此时才有
$a_p(q)=B(p,q)=B(q,p)=a_q(p)$。
纯点线性张成 $V$，所以将每个 $p$ 配到原 $a_p$ 的双线性型唯一；
若以另一个无盲核框架构造 $h$，也必得到同一个 $B$。

最后，110.5已在裸W下给出每个原框架和的三分之一属于 $\operatorname{ri}K$，
对 $F_0$ 直接复用便得 $U/3\in\operatorname{ri}K$ 与 $U\in\operatorname{int}C$，不需调用Jordan分类。证毕。

### 111.4 与旧二元候选及同锥同单位Jordan结构的准确等价

**定理 111.5（存在一框架等于全部框架）。** 在同一原有限维全态、全效应W域中，
以下条件等价：

$$
\boxed{\begin{aligned}
\mathrm{TFD}_{3,\exists}
&\Longleftrightarrow\exists F:\mathcal I_F=0
\Longleftrightarrow\forall F:\mathcal I_F=0\\
&\Longleftrightarrow\mathrm{TFD}_3
\Longleftrightarrow\mathrm{TRI2}
\Longleftrightarrow S\\
&\Longleftrightarrow\mathrm{PAIRJET2}
\Longleftrightarrow\mathrm{JET2}
\Longleftrightarrow\mathrm{H2}
\Longleftrightarrow\mathrm{CUB3}
\Longleftrightarrow\mathrm{PL}_3\\
&\Longleftrightarrow\mathrm{Pair}
\Longleftrightarrow\mathcal L(K)\text{ 满足原面格覆盖律}\\
&\Longleftrightarrow\exists\text{有限维秩三EJA }J,\quad
\Phi:J\overset{\sim}{\longrightarrow}V,\quad
\Phi(J_+)=C,\quad u\Phi=\operatorname{tr}_J.
\end{aligned}}
\tag{VIII111.19}
$$

两个 $F$ 量词均遍历全部原joint三框架。
$S$ 指整个 $C^*$ 序中的proper least与全部原纯点的数值互易；
$\mathrm{H2}$ 指VII106的效应空间 $A=V^*$ 上原 $Q(f)$ 是正定二次型，
不与状态空间的 $Q_3(v)$ 或本章 $\pi_F$ 混名。
其余比较条件逐字采用VII106.5、106.10的定义。
G是这些等价条件的后果；本定理没有把G单独列成一个等价条件。

证明。111.2先给存在式的算子表述，111.4给全纯互易。
W早已给每个原 $a_p$ 对整个 $F_p$ 的全锥序least，故此时原域满足完整 $S$。
对任意有限原纯准备 $\sum_\ell t_\ell q_\ell$，包括零权和重复标签，
$T_p=a_p$ 与刚取得的互易也直接给

$$
T_p\!\left(\sum_\ell t_\ell q_\ell\right)
 =\sum_\ell t_\ell a_p(q_\ell)
 =\sum_\ell t_\ell T_{q_\ell}(p),\qquad
 t_\ell\ge0,\quad\sum_\ell t_\ell=1.
\tag{VIII111.20}
$$

现在直接消费VII106.10及109.10已明确接口的[完整S桥][Q109S]：
原全proper least与全纯互易先供应正对偶剥离、忠实自对偶配对、
有符号框架谱性、正面投影、projectivity和滤子保纯，
再应用[Barnum—Müller—Ududec Theorem 16][Q109BMU]取得有限EJA。
W已有原面高三，同域归一接口给秩三及 $u\Phi=\operatorname{tr}_J$。
这一整桥按既有证明复用；没有用正投影存在单独顶替滤子保纯。
所得迹配对与 $B$ 都把每个原纯点配到同一个 $a_p$，
所以它们相同；此后才使用Jordan谱与成熟Peirce几何。

EJA反向完全复用109.10的原延拓唯一性与真实Peirce核对：
在每个完整本原框架中，原 $\Pi_{p_i}$ 确为 $U_{e-e_i}$，
原 $R_i$ 确为本原射线投影，而(VIII109.40)使 $\mathcal I_F=0$。
这对全部原joint成立，包括零Peirce块、直和及Albert分支。
全框架条件当然推出存在框架条件，因为W已有非空框架集。
109.3给TFD3、TRI2，VII106.10给全部旧比较条件，闭成所列等价。
并可在所得Peirce分解中读出每个 $h_F$ 都是共同 $B$ 的限制。
正向没有先使用109章切丛或星锥的全局拼接，也没有预付全纯互易、谱性或保纯。证毕。

### 111.5 仅在W加G中定义有符号剩余的原纯自检测

**定理 111.6（三项非负亏损及统一上界）。** 现在只假设W与G，
即存在同一原 $U$ 使 $p+2c_p=U$ 对全部原纯点成立。
本节及111.7—111.8不假设任何框架满足 $\mathcal I_F=0$。
固定任意原joint $F$，此时 $U_F=U$；仍只在 $V_F$ 上使用111.3的 $h_F$。
对每个原纯点 $x$ 定义

$$
X_F(x)=\pi_Fx,\qquad Y_F(x)=Y_{a_x},\qquad
\delta_F(x)=a_x(\mathcal I_Fx).
\tag{VIII111.21}
$$

简记 $X=X_F(x)$、$Y=Y_F(x)$、$\|\cdot\|=\|\cdot\|_{h_F}$，则

$$
\begin{gathered}
\|X\|\le1,\qquad\|Y\|\le1,\qquad
 h_F(U,X)=h_F(U,Y)=1,\\
\delta_F(x)=1-h_F(Y,X)\\
\hphantom{\delta_F(x)}
 =\frac12\left[(1-\|X\|^2)+(1-\|Y\|^2)+\|X-Y\|^2\right],\\
1-\|X\|^2\ge0,\qquad1-\|Y\|^2\ge0,\qquad\|X-Y\|^2\ge0,\\
0\le\delta_F(x)\le\frac43.
\end{gathered}
\tag{VIII111.22}
$$

三个亏损依次量原态可见向量的长度缺口、原确认尺可见Riesz向量的长度缺口、
以及两者的错位。$\mathcal I_Fx$ 是有符号剩余，不是另一张原归一态；
$\delta_F(x)$ 是该剩余经原proper尺读出的差值，不是单独正态上的probability。

证明。W与G给 $a_x(U)=a_x(x+2c_x)=1$，而
$u\mathcal I_F=0$、$u(x)=1$，故 $u(X)=1$。
111.3的两个界分别给 $\|X\|,\|Y\|\le1$；
$h_F(U,\cdot)=u$ 在 $V_F$ 上及Riesz定义给两个配对均为一。
原 $a_x(x)=1$，且 $a_x(\pi_Fx)=h_F(Y,X)$，所以展开平方即得三项恒等式。
此处没有把 $a_x$ 在 $Z_F$ 上的值写成一个未定义的全空间 $h_F$ 配对。

令 $a=\sqrt{2/3}$，中心化得

$$
\widehat X=X-U/3,\qquad\widehat Y=Y-U/3,\qquad
h_F(U,\widehat X)=h_F(U,\widehat Y)=0,\qquad
\|\widehat X\|,\|\widehat Y\|\le a.
\tag{VIII111.23}
$$

因为 $\|U/3\|^2=1/3$，有
$h_F(Y,X)=1/3+h_F(\widehat Y,\widehat X)\ge1/3-2/3=-1/3$，
从而 $\delta_F(x)\le4/3$。
下界由三个亏损非负给出。证明仅用W、G和固定框架的两侧正性，
没有输入全纯非零读数互易。证毕。

### 111.6 非零共同盲核必被某个原纯点自己的确认尺读出

**定理 111.7（原纯自检测的二分之一下界）。** 在W与G下，固定任意原joint $F$。
若 $Z_F\ne0$，则存在原纯点 $x\in P$，使

$$
\delta_F(x)=a_x(\mathcal I_Fx)\ge\frac12.
\tag{VIII111.24}
$$

所用尺必须是这个 $x$ 自己的原least确认尺 $a_x$；
本结论不只给一张事后任选的有符号泛函。
它是条件性的统一下界，不宣称该常数锐，也不宣称存在满足W与G而 $Z_F\ne0$ 的模型。

证明。选 $0\ne z\in Z_F$。
此时已经假设G，故可以准确复用VII105.10在W加G域中的有符号三谱存在，
而不要求全纯互易或Jordan。
得到某个原joint $H=(x_1,x_2,x_3)$ 和实系数

$$
z=\sum_{i=1}^3\lambda_i x_i,\qquad
\sum_i\lambda_i=u(z)=0,\qquad(\lambda_i)_i\ne0.
\tag{VIII111.25}
$$

$H$ 可与固定观测框架 $F$ 不同，全部对象仍属于同一个原模型。
记 $X_i=\pi_Fx_i$、$Y_i=Y_{a_{x_i}}$。
由G的框架和、Riesz线性性及109.2的共同核，分别有

$$
\sum_iX_i=\pi_FU=U,\qquad
\sum_iY_i=Y_{\sum_i a_{x_i}}=Y_u=U,\qquad
\sum_i\lambda_iX_i=\pi_Fz=0.
\tag{VIII111.26}
$$

第一式只用 $U$ 是固定 $F$ 的三个点之和，故 $\pi_FU=U$；
第二式用原joint尺和为 $u$；没有将 $x\mapsto a_x$ 预设成全空间线性映射。
令 $v_i=X_i-U/3$。
则 $\sum_i v_i=0$，且由 $\sum_i\lambda_i=0$ 有 $\sum_i\lambda_i v_i=0$。
系数列 $(1,1,1)$ 与非零零和列 $(\lambda_1,\lambda_2,\lambda_3)$ 线性独立，
故从 $\mathbb R^3$ 向 $V_F$、$e_i\mapsto v_i$ 的线性映射有至少二维核，
其像维数至多一。这严格给出三个可见中心向量共线，包含全部为零的情形。

若全部 $v_i=0$，则 $h_F(Y_i,X_i)=h_F(Y_i,U/3)=1/3$，
所以三个 $\delta_F(x_i)$ 都为 $2/3$，已得结论。
否则在这条直线上取 $h_F$ 单位向量 $e$；它与 $U$ 正交。
定义实数列

$$
v_i=\alpha_i e,\qquad
\beta_i=h_F(e,Y_i-U/3),\qquad
\sum_i\alpha_i=\sum_i\beta_i=0,\qquad
|\alpha_i|,|\beta_i|\le a=\sqrt{2/3}.
\tag{VIII111.27}
$$

$\beta_i$ 的界是正交投影收缩，由111.6的中心范数界给出，
不要求 $Y_i-U/3$ 也在同一条直线上。
两列来自同一个谱框架与同一个固定 $F$，不能各自更换实现。
由此准确计算

$$
\delta_F(x_i)=\frac23-\alpha_i\beta_i.
\tag{VIII111.28}
$$

只需证明三个乘积中至少一个不超过 $a^2/4=1/6$。
若某个乘积非正，已成立。
否则各项 $\alpha_i,\beta_i$ 都非零且逐项同号。
零和三元列必有两项同号；同时给两列换整体符号后，
可重标号使 $\alpha_1,\alpha_2,\beta_1,\beta_2>0$。
于是

$$
\begin{gathered}
\alpha_1+\alpha_2=-\alpha_3\le a,\qquad
\beta_1+\beta_2=-\beta_3\le a,\\
\sqrt{\alpha_1\beta_1}+\sqrt{\alpha_2\beta_2}
\le\sqrt{(\alpha_1+\alpha_2)(\beta_1+\beta_2)}\le a.
\end{gathered}
\tag{VIII111.29}
$$

两乘积不可能都大于 $a^2/4$，否则左边严格大于 $a$。
故某个 $i$ 有 $\alpha_i\beta_i\le1/6$，代入(VIII111.28)得
$\delta_F(x_i)\ge2/3-1/6=1/2$。
以上包括零系数、中心像为零和零切块；没有用滤子保纯或Peirce分类。证毕。

### 111.7 统一自检测阈值与两张真实原态的反事实

**推论 111.8（严格小于二分之一的准确含义）。** 在W与G中，对固定原joint $F$，

$$
\boxed{\quad
\mathcal I_F=0
\ \Longleftrightarrow\ \forall x\in P:\delta_F(x)=0
\ \Longleftrightarrow\ \sup_{x\in P}\delta_F(x)<\frac12.
\quad}
\tag{VIII111.30}
$$

这些条件也等价于该 $F$ 的三元二面可辨；由111.5还等价于全部原joint可辨。
若它们失败，则可取一个原纯点 $x$、$z=\mathcal I_Fx$、$w=U/3$ 和足够小
$\epsilon>0$，使同一原模型中的两个不同真实归一态满足

$$
\begin{gathered}
w_+=w+\epsilon z\in K,\qquad w_-=w-\epsilon z\in K,\qquad w_+\ne w_-,\\
\Pi_{p_i}w_+=\Pi_{p_i}w_-\quad(i=1,2,3),\\
a_x(w_\pm)=\frac13\pm\epsilon\delta_F(x)\in[0,1],\qquad
 a_x(w_+)-a_x(w_-)=2\epsilon\delta_F(x)\ge\epsilon>0.
\end{gathered}
\tag{VIII111.31}
$$

因而共同盲核非零，当且仅当存在这里这种以原纯点自身确认尺分开的反事实。
阈值判据要求上确界严格小于 $1/2$；只知道小于等于 $1/2$ 不足以由本界结算。

证明。$\mathcal I_F=0$ 当然使全部亏损为零，故上确界为零。
若 $\mathcal I_F\ne0$，111.7给一个原纯点使 $\delta_F(x)\ge1/2$，
同时否定其余两项，得到(VIII111.30)。上确界存在，因为 $P$ 非空且111.6给有界区间。
取111.7所给的 $x$，则 $a_x(z)\ge1/2$，故 $z\ne0$。
109.2给 $u(z)=0$ 及三张 $\Pi_{p_i}z=0$；
VII105.9在W加G下已给 $w\in\operatorname{ri}K$，
所以足够小的正反微移都仍在整个原 $K$ 中。
$\operatorname{aff}K=\{u=1\}$ 保证归一没有改变。
原 $a_x(U)=1$ 给(VIII111.31)的两个实际概率与其差，
而109.3还保证每张在某 $p_i$ 读零的原效应在 $w_+,w_-$ 上读数相同。
反向，若三张 $\Pi$ 同读却有 $a_x$ 分开，两态之差便是非零共同核向量，
109.2使 $\mathcal I_F\ne0$。
这把109.3的一般分离泛函加强为指定形式的原proper确认尺，
没有把有符号 $z$ 自己当作概率态。证毕。

### 111.8 全部三球、复三能级和旧全态全效应Born字典

**推论 111.9（存在一组可辨后的复型选择）。** 在W与 $\mathrm{TFD}_{3,\exists}$ 下，
若仍保留全部原纯点上的条件

$$
\forall p\in P,\qquad D_p\simeq_{\rm aff}B^3,
\tag{VIII111.32}
$$

则有同原锥同原单位的 $H_3(\mathbb C)$ 表示，$\dim_{\mathbb R}V=9$ 是后果。
同一个实线性双射 $\Phi:H_3(\mathbb C)\to V$ 给整个静态字典

$$
\begin{gathered}
\Phi(\operatorname{Herm}_+(\mathbb C^3))=C,\qquad
u(\Phi A)=\operatorname{tr}A,\qquad U=\Phi(I_3),\\
K=\{\Phi\rho:\rho\succeq0,\ \operatorname{tr}\rho=1\},\qquad
P=\{\Phi(vv^*):v^*v=1\},\\
\mathcal E=\{f_E:f_E(\Phi A)=\operatorname{tr}(EA),\quad0\preceq E\preceq I_3\},\\
a_{\Phi(vv^*)}(\Phi\rho)=\operatorname{tr}(vv^*\rho),\qquad
T_{\Phi(vv^*)}(\Phi(qq^*))=|v^*q|^2\quad(q^*q=1),\\
B(\Phi A,\Phi A')=\operatorname{tr}(AA'),\qquad
\sum_j f_{E_j}=u\ \Longleftrightarrow\ \sum_jE_j=I_3.
\end{gathered}
\tag{VIII111.33}
$$

全部有限数学测量还要求各 $E_j\succeq0$；原纯几何为 $\mathbb{CP}^2$。
这里没有先另给九维，也没有删掉原混态或原效应。
只要求存在一张完整 $B^3$ 不能代替(VIII111.32)。

证明。111.5先给全部框架TRI2，随后直接复用109.11—109.12的成熟EJA分类与完整字典。
它们在同一个 $V,C,u,K,P,\mathcal E$ 上给复型、九维及Born迹配对。
共同 $B$ 与矩阵迹配对的认同由111.5中原纯尺的唯一配对给出。
109.11已给精确反例：同单位 $\mathbb R\oplus\operatorname{spin}_3$ 满足W、G和TRI2，
所以也满足本章存在式关系，却只有旗标的整个排除面为三球；
其球纯点的整个排除面为线段，实维数为五，非复三能级。
因此不能把全称三球量词缩成一张窗口。
这些数学测量是否属于实际可调用菜单仍按原过程合同决定。证毕。

### 111.9 全有限层级和原过程消费者的原量词接口

**命题 111.10（单体替换与其余合同的完整保留）。** 固定VII106.16的同一个
原装饰元组 $\mathcal O$、共同来源域、非空 $\mathcal J\subseteq\{A,D,E\}$
以及共同域 $\mathcal D_{3,\mathcal J}$。
只在它允许选择的每个秩三载体 $X\in\mathcal J$ 上，将几何项
$\mathsf W_X+\mathrm{PAIRJET2}_X$ 替换成
$\mathsf W_X+\mathrm{TFD}_{3,\exists,X}$，便得到与原包等价的条件包。
$\mathcal N(\mathcal O)$ 和每个未选载体的完整 $S_X$ 仍逐字取原定义的全部量词。
在[全有限复C星层级VII][Q109Hierarchy]的最新104章接口中，本章仅供应相应单载体的
完整 $S_1$；全有限结论仍要求该卷定义102.1、假设104.1的原域及三项具名低二份供应，
普遍比较为整个 $S_2$，非经典支路另有 $\mathsf F_{\max}$。

证明。几何替换直接消费111.5与VII106.16，所有非几何消费者保持原式。
明确地，原概率像自身紧及全部原中点实现、原测试的整个效应表及闭性、
零／单位／中点／补／有界倍增、重复标签和每种同中点实现、
全部非负质量缩放及零／次归一／不等质量、各过程与参考自己的全部相关联合输入域均保留。
同一个原 $L,p,\omega,K,M$、两次同一读回 $p$、两实张成、全实 $Z$、完整(83.8)、
原单位／迹／伴随／内积／二次表示、VI(89.13)全部两尺度等式、C2、整个 $G=1_E$
均按原合同；这里 $G=1_E$ 是原包中的符号，不是本章共同中心条件G。
精确PRE之后仍对同一原资格态使用整个H13输出，保留活跃块严格负方向、
共享总迹一、非活跃零质量、空活跃集及原资格参数。
共同来源仍包括设备／事件／来源绑定、全部菜单与分支、参考／副本／相关联合、
记录／权限／控制／原钟／单位、ready／flags、失败／拒绝／停止／销毁／返回、
实际混合、全部合法未来、旧support与每个中间切口。
VI89.9—89.10的原生／细化消费者、全部原字和terminal futures、联合有符号关系、
细标签粗归组、记录后条件未来、source-adoption与资源合同也逐字保持。
不以球窗口替代完整相关输入，不逐块换态，也不从输出反选资格。

为完整指定最新全有限层级的量词，仍取所有有限 $N\ge1$ 的
$W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正
$u_N=u^{\otimes N}$、全部原极点 $P_N$ 及整个 $[0,u_N]_{C_N^*}$；
对每个实际分块 $a+b=N$ 均保留

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}
 \subseteq C_a\otimes_{\max}C_b,\qquad
(f\otimes g)(x\otimes y)=f(x)g(y),\qquad
u_{a+b}=u_a\otimes u_b.
\tag{VIII111.34}
$$

全部原因子置换及其逆正，重括号为同一原实张量空间的规范识别；
不连续位置分块仍由这些指定置换运输。
$S_2$ 逐字量化每个 $p\in P_2$、每个有限纯准备 $q_\ell\in P_2$、
所有 $t_\ell\ge0$、$\sum_\ell t_\ell=1$，包括纠缠纯态、零权和重复标签，要求

$$
T_p^{(2)}\!\left(\sum_\ell t_\ell q_\ell\right)
 =\sum_\ell t_\ell T_{q_\ell}^{(2)}(p),\qquad
T_p^{(2)}(x)=\inf_{\substack{f\in[0,u_2]\\f(p)=1}}f(x).
\tag{VIII111.35}
$$

该层级104.1的具名低二份PAPER供应仍为：在原 $q=1,2$ 上由least／谱性／
正面投影及保纯性到Jordan的桥；在唯一实际自复合 $(W_1,W_1,W_2)$ 上的
直和扇区限制、秩与实维乘法的复型选择；原实际两因子产品正规形。
每项完整输入和来源均按该层级103.1、104.1，不以本章单体推导替代。
在所得同一保迹局部坐标 $A=\bigoplus_iM_{n_i}(\mathbb C)$ 中，
$L=\max_i n_i\ge2$ 时，$\mathsf F_{\max}$ 联合要求存在一张这种坐标、
某个 $n_r=L$ 的实际块及其同一包含相位的正交归一基，使

$$
g_r=\sum_{a=1}^L|a\rangle_r|a\rangle_r|a\rangle_r,\qquad
\Delta_r=|g_r\rangle\langle g_r|\in C_3,\qquad
u_3(\Delta_r)=L.
\tag{VIII111.36}
$$

其余全部三份扇区取零，原归一源为 $\Delta_r/L$；不预设三份纯性或实际制备。
$L=1$ 的全经典支路不要求资源。
在这些完整原前件下，直接消费该层级104.10：
$S_2+\mathsf F_{\max}\Longleftrightarrow S_2+\mathsf F$，且等价于存在同一保迹局部坐标
$\theta$，使对所有有限 $N\ge1$ 均有

$$
\theta^{\otimes N}(C_N)=
\bigoplus_{(i_1,\ldots,i_N)}
\operatorname{Herm}_+\!\left(\bigotimes_{j=1}^N\mathbb C^{n_{i_j}}\right).
\tag{VIII111.37}
$$

单体 $S_1$ 不能反向供应 $S_2$；也不从一组三窗口制造叉口资源。

取得上述全层级后，数学全旁观正性仍指对每个 $b\ge0$，
$(\mathrm{id}_{W_b}\otimes F)(C_{b+m})\subseteq C_{b+n}$，
量化输入与所有旁观腿间的任意纠缠。
其与通常CP的认同、矩形跨扇区Kraus及逐输入TP/TNI预算，
沿该层级102.13、103.10的自身Choi桥使用。
同事件CP仍消费原完整提升、实际探针及相容核；已有充分递归参考者直接复用。
所有数学CP-TNI分支成为实际事件，仍需该层级102.14的额外饱和选择。
实际仪器保持同族预算、接线、记录、粗粒化及共同输入校准，
条件态只在正质量分支归一；Lüders仍需同一分支的锐效应、接受态中性和输出校准，
按该层级102.15、103.12及VII106.16的同来源合同读取。
物理时间仍要求原钟、连续齐次可逆群及实际动态来源，单位和 $\hbar$ 仍由原过程合同给定。
静态几何可以同时容纳恒等时间族和非平凡Hamiltonian时间族，故不选择这些数据。
复三能级的二、三份秩分别为九、二十七，不能要求它们也满足秩三W。
因此本章完成的是单载体条件替换；全有限联合结构与实际动力学的原目标继续保留。证毕。

### 111.10 新推导的归属与仍未证明的自动性

**约定 111.11（纸面条件结论的来源和边界）。** 111.3—111.4的原六块双侧正性、
单框架取等迫共同Riesz配对，以及111.6—111.8的原自检测亏损、共线三谱和统一阈值，
按 `repo-derived` 归属；111.2消费109.2—109.3，111.5、111.9—111.10为已有桥的同域接合。
范数对偶、Cauchy—Schwarz及有限维Riesz只作为其中成熟的中间工具；
框架和的内点性直接复用110.5，不另计本章新内容。
三缝包含—排除与二面线性张成的先例是[UBE Proposition 1及Appendix][Q109UBE]；
其standing condition要求每个暴露面有唯一滤子及唯一补滤子，
本章没有把该条件未经核对地移植成裸W的已知性质。
本章原代数仍只从109.2—109.3取用。

完整S到EJA的承重桥仍是[原Library的完整S接口][Q109S]及其中
“Least confirmation forces face-filter purity”；最终分类复用
[BMU Theorem 16][Q109BMU]，明确保留projectivity、转移互易及滤子保纯三个输入。
BMU Proposition 29把无三阶干涉与滤子保纯联系起来时另有其Postulates 1、2，
不能脱离这些输入直接用于裸W。
真实Peirce反向及包括Albert、直和的成熟有限EJA分类按109.10—109.11复用，
Born字典按109.12复用，最新全有限层级按其104.1、104.10的完整原条件复用。
这些推导不主张全球原创、文献穷尽、独立最少公理或内核验证。

本章没有证明或反驳以下自动性：

$$
\mathsf W\ \Longrightarrow\ \mathrm{TFD}_{3,\exists},\qquad
\mathsf W+\mathrm G\ \Longrightarrow\ \mathrm{TFD}_{3,\exists}.
\tag{VIII111.38}
$$

由111.5，它们准确对应109.14保留的两个TRI2自动性问题。
“尚未证明”只指没有所需推导或同域反例，不声称形式不可判定或逻辑独立。
111.7不能证明非Jordan的W加G模型存在；$1/2$ 的锐性也未确定。
(VIII111.30)给的是等价附加判据，没有从W加G本身导出其严格上界。
109章既有全框架等价与星锥充分推导保持成立，
本章增加的是更弱量词输入及较短的正性取等路线。

### 111.11 三角窗口与自己的确认尺：完整白话

**命题 111.12（一组三窗口拼全与未拼全时的自检测）。** 上述条件结论可按原对象和原量词
解释为下面的几何图景。

证明与解释。先想象一个装着全部原状态的凸体；每把原尺都在零到一之间读数，
所有允许的原尺都在场，不挑走混态或不方便的效应。
每个纯点背后，有一块能被确认它的某把尺完全排除的区域。
W说这整块区域本身是一颗完整实心球，且原正交的两个纯点生成真面。
原来的结果已经从这里得到每张球的一致线性读回、每个纯点自己的最低确认尺，
以及能共同区分的三点框架。它还没有宣布所有球共享一个中心或一个全局长度。

现在只挑一组三点，把三个背后窗口全部打开。
新条件说，收齐在这组三点至少一个点上读零的全部原尺，联合起来能区分任意两个原态。
只要存在这样一组三角窗口即可；不用预先对每组三角形重复下令。
但每个窗口里的信息是整张球和整张零效应面，绝非只记三个接受概率，
也不是一张三维球独自看清整个模型。
109.2—109.3已经说明，窗口拼全等价于共同盲区为零，
也等价于三张完整原球的线性张成填满整个原空间。

把这一组三角形想成三根互相垂直、长度为一的刻度棒。
三条边旁各有一团切方向，仍使用那张原球自己的长度，统一除以二来量平方。
这些六块先只在窗口实际看到的空间中正交摆放；
若还存在盲区，就先让它留在这个空间之外，不给它偷配一把全局尺。

正性给两道面对面的栏杆。
从状态一边看，每个二元读回都必须落在它原来的球锥里：
两个端点质量越小，中间切方向越不能长，端点为零时相应切方向必须消失。
三个这样的限制加起来，使任何质量一状态的可见向量长度不超过一。
从效应一边看，一把原正尺在整个实心球上都不能读负；
它的切向斜率也被两个端点读数夹住。
用同一半尺度换成Riesz向量后，长度不超过这把尺在三角形三顶点上的读数之和。
两道栏杆分别来自状态和效应的原正性，没有把正尺假装成已经存在的正态。

如果这组三窗口已经拼全，可见空间就是全部原空间。
任一纯态用自己的确认尺读自己，必须恰好读一。
两道长度界和内积不等式于是迫它在这组三角形顶点和上的读数至少为一。
把这个纯态补成另外一组三点框架，三个自己的确认尺加起来仍是原单位尺；
因此这三个下界的总和又只能是三，每一个都必须恰好是一。
栏杆的所有松动同时消失：纯态向量与自己的确认尺向量重合，长度都恰好为一。
这一认同在整个原空间成立，所以全部原纯点之间的比较才自动互易。
任何三点框架的和都被同一个单位尺确定，所有三角重心于是自动重合。
到这里再沿完整least桥取得同锥、同单位的秩三Jordan几何；
谱性、面滤波保纯和成熟Peirce公式在这之后接入。

若只知道共同重心而还没有拼全，也能准确量出缺口。
一个纯态的可见向量与它自己确认尺的可见向量都在单位球里，
它们各自没有用满的平方长度，以及彼此没有对齐的平方距离，
合成同一个非负剩余读数。
这读数来自有符号盲区，所以不能把它当作另一张正态的概率；
它的纸面范围是零到三分之四。

若共同盲区非零，用原共同中心下已有的三谱把其中一根非零箭头拆成同一组三个纯点。
这三个纯点在窗口里的中心箭头只能落在一条直线上：
它们既要加成零，又被同一条非零零和谱关系约束。
另一边三把确认尺的中心投影同样零和，且每根都受统一长度界。
两个有界零和三元列不能让三个逐项乘积都过大，
因此至少一个纯点自己的剩余读数达到二分之一。
这不是随便另找一把能分离的尺，而是这个纯点本来就有的那把确认尺。

沿该纯点自己的盲区箭头，从原共同内点正反挪动一小步，便得到两张真实归一态。
三张完整窗口对它们全部同读，这把原确认尺却读出不同的两个实际概率。
反过来，若对某个框架所有原纯点的剩余读数上确界严格小于二分之一，
上述非零盲区就不可能存在，这个框架已经拼全，全部框架也随之拼全。
本章没有证明W或W加共同中心会自动满足这个严格阈值，也没有造出它们失败的原模型。

最后，若每个纯点背后的完整排除球都是三球，成熟分类才把所得秩三几何选成复三能级，
九维、全部密度态、全部零一矩阵效应与Born概率一起成为后果。
只出现一张三球，经典旗标加一个spin三球仍是另一种可能，不能选复型。
更大复合载体、纠缠旁观者、实际事件、条件更新、仪器、钟和 $\hbar$ 各有自己的原联合合同。
本章的一组三角窗口不替它们付款，也不把高阶载体压回秩三。
因此所得是一条完整的单体条件重构与一条有幅度的盲核判据，
全有限层级和实际动力学仍按原条件继续研究。证毕。

## 追加锚（本行以下为增补区）
