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
