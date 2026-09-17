# 阶二 Fano 局部系统的迹重构与辛实现

## 1. 公开问题、对象及范围

Krämer、Litt、Maculan 的 *E6-local systems from cubic threefolds*
[KLM26, §1.1] 已经解决其大阶 E6 存在问题。本文的目标是作者在同节明确留下的阶二情形：
对三次三维簇族的 Fano 曲面族及非平凡二阶秩一局部系统 L，确定

\[
\mathbb V=R^2\pi_*L,\qquad \operatorname{rank}\mathbb V=27
\]

的连通代数 monodromy。作者预期自然八维辛表示的非平凡二阶外幂。
精确区分覆盖群与忠实像：Sp8 的中心 ±1 在二阶外幂上作用平凡；27 维中的忠实像为 PSp8，类型 C4。
本文没有证明这一几何预期，也没有证明一个任意 27 维自对偶系统具有该类型。
若 L 的延拓还含基上的有限阶秩一扭曲，比较完整表示前需通过有限 étale 基变换除去；这一步不能从表示同构的表述中隐去。

这一文档处理 Fano 双覆盖、Prym 几何和 27 维表示的比较，属于新的具体代数几何问题。
既有 `SURFACE_CONGRUENCE_OBSERVERS.md` 的曲面映射类群同余问题保持原范围。
既有一般观察者理论的以下真实对象是本研究的参照，而不是被重新命名的证明：

- 有限 Hankel 分解及可达空间模全未来不可见方向的维数公式；
- 序列的实际线性实现；
- automath 的 `subsec__pom-pw-tannaka-krein-reconstruction.tex` 所提出的群重构问题；
- newmath 的 `TannakaKreinUp`、`MonodromyUp` 记录接口。它们不提供本问题所需的上同调比较。

## 2. 已有文献提供什么

[Ebe24, §3, (3.2)] 的 cycle weight 是

\[
w(T_1,\ldots,T_k)=\operatorname{tr}((T_1-1)\cdots(T_k-1)).
\]

其 Proposition 3.4 已用环路反转条件判别不变辛形式，Proposition 4.1 讨论通过不变商后环路权重的保持。
本文不把环路权重、一般不变形式判别或迹重构主题声称为新发明。
下面给出的是可直接求值的有理星形坐标、实际矩阵恢复、全部不变交替形式的显式求解，以及非退化性判据。
它们对本问题提供一个有限可反驳的表示检验步骤；目前不构成阶二几何问题的新闭合。

[Don92, Theorem 5.3, printed p.47] 将一般 A∈A4 的 genus-five Prym 纤维识别为相应 Fano 曲面的双覆盖；Prym 纤维上的 λ 对应换层。
紧接的 Remark 5.4 指出 χ 在一个显式大开集上的同构结果。
该识别为八维 H1(A) 提供具体的几何候选来源，仍须另外构造与上述 V 的上同调比较。

## 3. 从真实矩阵计算二阶及三阶观察

设 K 为任意域，I 为有限指标集，a∈I。给定零对角矩阵 H，并令

\[
N_i=e_iH_{i,*},\qquad T_i=1+N_i.
\]

这些是实际的 I×I 矩阵。直接相乘得到

\[
N_i^2=0,\quad T_i^{-1}=1-N_i,
\]
\[
\operatorname{tr}(N_iN_j)=H_{ij}H_{ji},\qquad
\operatorname{tr}(N_iN_jN_k)=H_{ij}H_{jk}H_{ki}.
\]

N_i 的秩至多为一；非零性需要另行满足。在下文的非退化八维实例中它们确为非零。
一般系数空间允许有 radical，不能由指标个数直接认定实际非退化状态维数。

假设双向星形条件

\[
H_{aj}\ne0,\qquad H_{ja}\ne0\quad(j\ne a).
\]

定义真实观察

\[
p_j=\operatorname{tr}(N_aN_j),\qquad
 t_{ij}=\operatorname{tr}(N_aN_iN_j).
\]

非锚点的 p_j 均非零。定义 d_a=1、d_j=H_aj，并令 D=diag(d)。
从观察构造矩阵 R：

\[
R_{aa}=0,\quad R_{aj}=1,\quad R_{ia}=p_i,
\qquad R_{ij}=t_{ij}/p_j\quad(i,j\ne a).
\]

### 定理 3.1. 同时有理恢复

\[
R=DHD^{-1},\qquad DN_i(H)D^{-1}=N_i(R).
\]

D 可逆，且同一个 D 对所有指标都适用。因此，对任意有限有序词 w，

\[
D\Bigl(\prod_{i\text{ in }w}T_i(H)\Bigr)D^{-1}
=\prod_{i\text{ in }w}T_i(R).
\]

**证明。** 锚点行及锚点列由定义直接计算。对两个非锚点，

\[
\frac{t_{ij}}{p_j}
=\frac{H_{ai}H_{ij}H_{ja}}{H_{aj}H_{ja}}
=\frac{d_iH_{ij}}{d_j}.
\]

两个被约去的分母均由星形条件保证非零。对角共轭保持第 i 行的支持，故同时恢复 N_i。
对角 gauge 保持加法、乘法和单位元，有限词等式由长度归纳得到。证毕。

该结论在选择了基的 rank-one 标架上适用。应用于几何生成元时，必须先证明其像方向能提供所用坐标基，或明确处理冗余标架的商空间。

## 4. 从观察构造并求尽不变交替形式

现在直接以 p,t 为输入，仅要求 p_i≠0 对所有 i≠a 成立。令

\[
\mu_a=1,\qquad \mu_i=-p_i^{-1},\qquad J=\operatorname{diag}(\mu)R.
\]

于是

\[
J_{aa}=0,\quad J_{aj}=1,\quad J_{ja}=-1,\qquad
J_{ij}=-\frac{t_{ij}}{p_ip_j}\quad(i,j\ne a).
\]

p_a 及带锚点的 t 坐标不参与构造。实际三阶观察在这些重复指标处为零；不能把未使用的任意输入坐标说成已被读回。

### 定理 4.1. 可执行的辛形式构造

若 t_ii=0 且 t_ij=-t_ji，则 J 交替，并且

\[
T_i(R)^tJT_i(R)=J\quad\text{对所有 }i.
\]

构造出的非锚点二阶、三阶迹恰为 p_j、t_ij。

**证明。** J 的交替性由上述条目表达式推出。对 N_i=e_iR_i 有

\[
(N_i^tJ)_{rc}=R_{ir}J_{ic},\quad
(JN_i)_{rc}=J_{ri}R_{ic},\quad
(N_i^tJN_i)_{rc}=R_{ir}J_{ii}R_{ic}.
\]

将 J_ic=μ_iR_ic 代入，前两个条目由交替性相消，第三项为零。
展开 (1+N_i)^tJ(1+N_i) 即得保持性。
读回使用 R_aj=1、R_ja=p_j 和非零分母 p_j。证毕。

这里没有除以 2，定理包括特征二，但几何应用位于特征零。

### 定理 4.2. 不变形式的完整显式解

设 b≠a。任取交替矩阵 B，如果所有 T_i(R) 保持 B，则

\[
B=B_{ab}J.
\]

此结论本身不要求 t 交替，不要求 R 非退化，也不假设不可约性。

**证明。** 展开保持性，利用 B_ii=0，得到对所有 i,r,c：

\[
R_{ir}B_{ic}+B_{ri}R_{ic}=0. \tag{4.1}
\]

先取 i=a,r=b,c=j≠a。锚点行均为 1，故 B_aj=B_ab。
记这个公共值为 q。再取 i≠a,r=a,c=j，由 (4.1) 得

\[
p_iB_{ij}+qR_{ij}=0,
\]

故 B_ij=qμ_iR_ij。锚点行由前一步给出，全部条目均等于 qJ。证毕。

### 定理 4.3. 无隐藏秩条件

\[
\det J=\Bigl(\prod_i\mu_i\Bigr)\det R,
\qquad \det J\ne0\ \Longleftrightarrow\ \det R\ne0.
\]

**证明。** 对 J=diag(μ)R 使用行列式乘法，每个 μ_i 均非零。证毕。

作为这些结果的普通数学推论，在至少两个指标、p_i≠0、t_ii=0 的条件下，R 的生成元存在非退化不变交替形式，当且仅当非锚点 t 交替且 det R≠0。
必要性由定理 4.2 写 B=qJ；B 非退化迫使 q≠0，交替性与非退化性便传回 J。

## 5. 该观察集保留了哪些信息

两个零对角标架若具有相同的锚点二阶及三阶迹，其 R 完全相同，由定理 3.1 获得显式同时相似。
相似的是带标签的操作族；不允许任意改换标签来弱化结论。

当 p,t 属于 K 的子域 L 时，R 与 J 的每个条目均在 L 中。
所以在这一星形坐标下，标架及不变形式同时下降到观察域，无须选择平方根。
这是构造公式的直接推论；它不把任意特征零表示的迹域与定义域一概混同。

还须区分一次有限证书与 invariant trace field：后者对所有有限指标子群取交。
本文的有限标架结论不计算该无限交，也不证明 [KLM26] 的大阶圆分域结论。

## 6. 二阶资料不足：一个非退化反例

### 命题 6.1. 二阶迹不能决定同时相似类

在 Q 上令

\[
H=\begin{pmatrix}
0&1&1&1\\-1&0&1&1\\-1&-1&0&1\\-1&-1&-1&0
\end{pmatrix},\qquad
H'=\begin{pmatrix}
0&1&1&1\\-1&0&-1&1\\-1&1&0&1\\-1&-1&-1&0
\end{pmatrix}.
\]

两者交替且行列式均为 1。由实际矩阵 N_i=e_iH_i 形成的所有二阶迹相同：对不同 i,j 均为 -1，对角为零。
然而

\[
\operatorname{tr}(N_0N_1N_2)=-1,\qquad
\operatorname{tr}(N'_0N'_1N'_2)=1.
\]

因迹在同时相似下保持，这两组带标签的操作不同时相似。
所以二阶迹即使在非退化交替标架上也不能决定带标签操作族的同时相似类。

## 7. 从矩阵恢复继续推导：28 个有理观察与二阶歧义

对 m 个指标，零对角星形正规形的独立坐标是 m-1 个 p 及 (m-1)(m-2) 个非对角 t。
加上交替性后只需

\[
(m-1)+\binom{m-1}{2}=\frac{m(m-1)}2
\]

个坐标。m=8 时为 7 个锚点二阶迹与 21 个有方向的锚点三角迹，共 28 个。
任取这些坐标且 p 非零，都能由第 4 节构造交替系统；再施加 det R≠0 是一个开条件。
这个开集非空：八阶矩阵 H_ij=1 (i<j)、H_ji=-1、H_ii=0 的行列式为 1。

在特征零的泛型有理重构范畴，这 28 个参数代数独立。
若少于 28 个有理标量观察仍允许一个泛型有理逆，则它们生成的域必须包含超越次数 28 的 k(p,t)，而一个由 q 个元素生成的域的超越次数至多 q，矛盾。
此最小性只针对该带标签、非退化星形坐标图及有理观察，不是任意算法、任意离散编码的下界。

二阶迹的损失还可更精确地描述。对特征零代数闭包上所有上三角条目代数独立的交替 H，固定全部 H_ij^2 后共有 2^{m(m-1)/2} 个边符号选择。
带标签的同时相似必须保持每个像方向 Ke_i，故共轭矩阵为对角矩阵。
两个全非零交替标架之间的这种共轭要求 d_i^2=d_j^2，所以恰是顶点符号切换，整体符号不起作用，作用自由且大小为 2^{m-1}。
因此泛型二阶观察的相似类纤维大小为

\[
2^{(m-1)(m-2)/2}.
\]

m=8 时为 2^{21}。这些是泛型矩阵上的结论，不声称第 6 节的单个数值实例实现全部分支。
每个分支的行列式作为独立变量多项式非零，故泛型非退化条件不会删除这些分支。

## 8. 接到真正的 27 维读数：一个精确恒等式

设 V 是特征零 n 维辛空间，n 为偶数，X,Y,Z∈sp(V)。令

\[
L_X=X\otimes1+1\otimes X,
\qquad W=\Lambda^2_0V.
\]

对本节的公式，L_X 表示其在二阶外幂及 primitive 部分的诱导作用。
普通张量迹计算给出

\[
\operatorname{tr}_W(L_XL_Y)=(n-2)\operatorname{tr}_V(XY),
\]
\[
\operatorname{tr}_W(L_XL_YL_Z)=(n-2)\operatorname{tr}_V(XYZ).
\]

**证明。** 在 V⊗V 上用反对称投影 P=(1-τ)/2 计算迹。
利用 tr(A⊗B)=tr(A)tr(B) 和 tr(τ(A⊗B))=tr(AB)。
辛李代数元素迹为零，于是两因子公式为 (n-2)tr(XY)，三因子的一般迹零公式为

\[
(n-3)\operatorname{tr}(XYZ)-\operatorname{tr}(XZY).
\]

由辛伴随 X*=-X 及迹的循环性有 tr(XZY)=-tr(XYZ)。
此外，二阶外幂中的不变直线被所有 L_X 杀掉，因此这些非空乘积的迹与 primitive 部分相同。证毕。

若 N_i 是 rank-one 辛幂零元，则 Λ²N_i=0，从而

\[
\Delta_i:=\Lambda^2(1+N_i)-1=L_{N_i}.
\]

对 n=8 及 27 维 W，令实际观察为

\[
P_j=\operatorname{tr}_{27}(\Delta_a\Delta_j),\quad
Q_{ij}=\operatorname{tr}_{27}(\Delta_a\Delta_i\Delta_j).
\]

若这些 Δ 确实来自所述八维标架，则第 3 节的输入为 p_j=P_j/6、t_ij=Q_ij/6，因而

\[
R_{ia}=P_i/6,\qquad R_{ij}=Q_{ij}/P_j\quad(i,j\ne a).
\]

必须保留“确实来自该外幂表示”这一义务。一个任意 27 维矩阵族即使通过这些标量检查，也未必具有八维 lift。
任何完整比较都应定义真实二阶外幂、primitive 核及实际算子后证明上述恒等式，不能把迹比例作为输入字段。

## 9. 以开放问题为目标的具体几何下一步

[Don92, Theorem 5.3 and Remark 5.4] 给出一个可用的共同开集：在加入适当 level 及必要的有限基变换后，将 Fano 双覆盖族与 A4 上的 Prym 纤维几何比较。
由通用四维主极化阿贝尔簇取得候选八维局部系统 U=R1a_*Q。
真正需完成的是一个非零、随基点平坦变化的映射

\[
\Psi:\Lambda^2_0U\longrightarrow (R^2\widetilde\pi_*\mathbb Q)^-.
\]

右侧是换层反不变部分，等同于目标二阶扭曲上同调。
在相应共同开集上，若候选 U 保持通用 A4 的稠密辛 monodromy，则 Λ²_0U 不可约。
因此一个非零平坦 Ψ 加上两侧秩均为 27，就足以推出同构。
这些基变换、稠密性与不可约性的假设要逐一核对，不能仅凭相同维数结束证明。

一个具体待计算的候选来源是 Prym 纤维参数化的 Abel-Prym 曲线。
在能选择通用曲线及其嵌入的共同开集/基变换上，其关联循环 Z⊂A×F-tilde 是三维的，故余维为 3。
对应作用是 Z_*:H4(A)→H2(F-tilde)。先与主极化 θ 相乘，再取反不变部分，得到候选

\[
\Psi(\alpha)=\frac{1-\tau^*}{2}\,Z_*(\theta\cup\alpha),
\qquad \alpha\in H^2(A)_0.
\]

此处记录的是明确候选，尚未证明该循环在所需基变换下的完整下降，也未证明 Ψ 非零。
下一项决定性计算是这个实际循环在 primitive 27 维分量上的投影，或计算 Ψ*Ψ 的标量。
若该标量为零，必须更换循环；不得把维数匹配当作替代证据。

矩阵路线提供并行可反驳检查：取得真实几何 Δ_i 后，先核验其局部幂零类型及星形条件，再使用第 8 节构造候选八维矩阵与第 4 节的 J。
随后必须在真实 27 维空间求解外幂候选与 Δ_i 之间的共同 intertwiner，并证明其可逆。
最后用真实生成元的李代数闭包或几何 moduli monodromy 证明稠密性。
仅有 det J≠0、二三阶迹匹配或一个八维模型都不足以结束这条路线。

## 参考文献

[KLM26] Thomas Krämer, Daniel Litt, Marco Maculan. *E6-local systems from cubic threefolds*. arXiv:2604.20970v1, 22 April 2026. §1.1 的阶二预期；本文不重复申报其已完成的大阶 E6 存在结果。
https://arxiv.org/abs/2604.20970

[Ebe24] Sean Eberhard. *Diameter of classical groups generated by transvections*. arXiv:2308.07086v3, 3 May 2024. §3, especially (3.2), Propositions 3.3 and 3.4; §4, Proposition 4.1. 这些是迹及不变形式的已有方法。
https://arxiv.org/abs/2308.07086

[Don92] Ron Donagi. *The fibers of the Prym map*. arXiv:alg-geom/9206008v2, 23 June 1992. Theorem 5.3 and Remark 5.4, printed p.47. 本文只将其用作具体双覆盖/Prym 几何输入，不将它说成已经给出目标上同调比较。
https://arxiv.org/abs/alg-geom/9206008
## 11. 几何范围修正：Prym 比较只直接覆盖偶二阶分量

本节修正第 2、9 节中未写出的必要范围。[Don92, §5.1, Theorems 5.2–5.3] 使用

\[
RC=RC^+\sqcup RC^-,\qquad \chi:A_4\dashrightarrow RC^+.
\]

χ 的目标是带偶二阶点的分量。[LNR22, §6, p.15] 明确将 RC+ 写成满足偶性条件的 (V,δ)，其中 δ 不在中间 Jacobian 的规范 theta 除子上。因此，第 9 节通过 A4 构造八维候选 U 及 Prym 关联循环的路线，目前只适用于相应 RC+ 共同开集。RC− 不能由这项识别自动纳入。

这不构成对 [KLM26] 阶二预期的反证。它修正的是本研究所用文献的适用范围。还不能把 Prym 纤维上的 λ 未经证明地解释为阿贝尔簇 A 上的取负映射；仅凭二阶外幂在取负下不变，不能推断第 9 节候选 Ψ 的反不变投影为零。

## 12. 连通配对图强制生成整个辛李代数

设 K 是特征不为 2 的域，H 是 n×n 交替矩阵，N_i=e_iH_i。定义实际配对图 Γ：不同 i,j 之间有边当且仅当 H_ij≠0。令

\[
C_{ij}=(E_{ij}+E_{ji})H=e_iH_j+e_jH_i.
\]

这里 C_ii=2N_i。直接相乘得到两个恒等式：

\[
[N_i,N_j]=H_{ij}C_{ij},\tag{12.1}
\]
\[
[C_{ij},N_k]=H_{jk}C_{ik}+H_{ik}C_{jk}.\tag{12.2}
\]

### 定理 12.1. 连通生成

若 det H≠0 且 Γ 连通，则

\[
\operatorname{Lie}_K\langle N_i\rangle
=\mathfrak{sp}(H)
:=\{X:X^tH=-HX\}.
\]

**证明。** 每个 N_i 都属于右侧，故生成代数包含于右侧。
对 Γ 的一条边，式 (12.1) 及非零 H_ij 给出 C_ij。若从 i 到 j 的 C_ij 已经生成，且 j,k 是一条边，则 C_jk 已生成，并由

\[
C_{ik}=H_{jk}^{-1}\bigl([C_{ij},N_k]-H_{ik}C_{jk}\bigr)\tag{12.3}
\]

继续生成 C_ik。按路径长度归纳，得到全部 C_ij。
任取 X∈sp(H)，令 S=XH^{-1}。从 H^t=-H 及 X^tH=-HX 推出 S^t=S，故

\[
X=SH=\frac12\sum_{i,j}S_{ij}C_{ij}.
\]

因此 X 也在生成代数中。证毕。

路径传播本身不需要 det H≠0；非退化性只用于证明全部 skew-adjoint 矩阵均有上述对称因子。

### 推论 12.2. 观察所重构的矩阵也具有完整生成性

继续第 4 节的 R,J。若 p 的非锚点坐标非零、t 交替且 det R≠0，则

\[
\operatorname{Lie}_K\langle N_i(R)\rangle=\mathfrak{sp}(J).
\]

**证明。** J=diag(μ)R 的各 μ_i 非零，N_i(J)=μ_iN_i(R)，故两个实际生成元集合的 Lie 闭包相同。J 的锚点行均为 1，其配对图连通。定理 4.3 给出 det J≠0，应用定理 12.1。证毕。

此处不声称两组离散群生成元的抽象群相同。

文献边界：[Yel21, Proposition 3.1 and Remark 3.4] 已在 l-adic transvection 生成中使用连通配对图及图直径。因此连通性方法本身不登记为新发现；下面进一步求出每一级的精确线性空间及匹配下界。

## 13. 更强的精确结果：Lie 生成层等于图距离带

定义实际的线性生成过程

\[
L_0=\operatorname{span}_K\{N_i\},\qquad
L_{k+1}=L_k+\operatorname{span}_K\{[X,N_i]:X\in L_k\}.
\]

L_k 使用至多 k+1 次原始生成元。独立地，令 B_k 为所有由至多 k 条 Γ 边连接的 C_ij 所张成的空间；长度零路径允许 i=j。

### 定理 13.1. 全层相等

对任意交替 H、任意 k≥0，不要求非退化或连通，均有

\[
L_k=B_k.\tag{13.1}
\]

**证明。** k=0 时用 C_ii=2N_i。
若 L_k=B_k，由 (12.2)，[C_ij,N_v] 的每个非零项，都将一条已有路径延长一条实际非零边；另一项使用反向路径。因此 L_(k+1)⊆B_(k+1)。
反向取一条至多 k+1 边的路径。若已有至多 k 边，则由归纳假设获得对应 cross。否则去掉最后的边 u,j，从 L_k 中的 C_iu 出发，用式 (12.3) 生成 C_ij。所减去的 C_uj 已在 L_1⊆L_(k+1)，所有除数均为真实路径上的非零配对。于是 B_(k+1)⊆L_(k+1)。证毕。

两边是独立定义的：左边从矩阵、线性张成和交换子递推；右边从实际非零配对的有限路径定义，不把结论放入左边的定义。

### 定理 13.2. 最早出现时刻的匹配下界

进一步假设 det H≠0。若 X∈L_k，而 r,c 之间没有长度至多 k 的路径，则

\[
(XH^{-1})_{rc}=0.\tag{13.2}
\]

对不同 i,j，特别有

\[
C_{ij}\in L_k\quad\Longleftrightarrow\quad d_\Gamma(i,j)\le k.\tag{13.3}
\]

不连通时距离记为无穷。

**证明。** 每个 C_ijH^{-1}=E_ij+E_ji。由 (13.1)，L_k 中任意线性组合的系数矩阵在距离大于 k 的条目均为零。但 C_ijH^{-1} 的 (i,j) 条目为 1，所以该方向不可能更早出现。反向由路径构造给出。证毕。

### 推论 13.3. 精确维数曲线与最短充分长度

取指标集上的任意全序。如果 det H≠0，则

\[
\dim L_k=n+\#\{i<j:d_\Gamma(i,j)\le k\}.\tag{13.4}
\]

因此，当 Γ 连通且 n≥2 时，达到完整 sp(H) 所需的最小生成元出现次数为

\[
1+\operatorname{diam}(\Gamma).\tag{13.5}
\]

**证明。** 右乘 H^{-1} 将 B_k 的生成族变成对角矩阵单位与距离带内的对称矩阵单位，它们线性独立。计数给出 (13.4)，最远点对给出 (13.5) 的必要性与充分性。证毕。

任意 Lie 括号排布的有界长度张成与上述右延长过程相同：Jacobi 恒等式逐步将右侧复合括号展开为对单个生成元的右延长，并保持生成元出现次数。

上界中的图直径已有 [Yel21, Remark 3.4] 的相关先例；这里得到的对象是完整的线性层、逐条目的零约束及下界。没有找到同一精确陈述的直接来源，但检索不构成全球新颖性认证，也不把它计为一个已解决的公开猜想。

## 14. 星形情况下的三次显式证书及锐性

若 H_ai,H_aj 非零，则式 (12.1)–(12.2) 给出

\[
C_{ij}=-\frac{[N_i,[N_a,N_j]]}{H_{ai}H_{aj}}
+\frac{H_{ij}}{H_{ai}^{2}}[N_a,N_i].\tag{14.1}
\]

该恒等式允许 i=j，也允许叶子之间 H_ij=0；只除以锚点边。

若 H 非退化，下列 n(n+1)/2 个矩阵形成 sp(H) 的一组基：所有 N_i，全部 n−1 个 [N_a,N_i]，以及每个非锚点无序对 i<j 对应的 [N_i,[N_a,N_j]]。

**证明。** N_i 对应对角对称矩阵单位，锚点交换子给出 C_ai。每个双交换子由 (14.1) 给出一个非零倍的独有 C_ij，加上已列出的 C_ai 方向。这是相对于完整对称矩阵单位基的可逆三角变换。证毕。

### 命题 14.1. 两个八维层维数曲线

一个八维锐性实例是：H_0j=1 (1≤j≤7)，H_12=H_34=H_56=1，其他上三角条目为零，下三角由交替性决定。其 det H=1，配对图有 10 条边且直径为 2。故各层维数为

\[
\dim L_0=8,\quad \dim L_1=18,\quad \dim L_2=36.
\]

长度二不够，长度三恰好足够。
对八顶点带权路径 H_(i,i+1)=i+1，维数曲线则为

\[
8,15,21,26,30,33,35,36.
\]

**证明。** 第一矩阵直接展开行列式得 1；其图有 10 条边且直径为 2，代入 (13.4) 得 8、18、36。带权路径中距离至多 k 的无序点对数依次增加 7、6、5、4、3、2、1，再代入 (13.4) 得所列曲线。这里的长度是 Lie 词中的生成元出现次数，不是群的 Cayley 图直径，也不是数值积分的物理时间。证毕。

## 15. 特征零下的完整 Zariski 稠密性推论

在复数域上，取 det H≠0 且配对图连通的交替 H。则

\[
\overline{\langle1+N_i\rangle}^{\mathrm{Zar}}=\mathrm{Sp}(H).\tag{15.1}
\]

**证明。** N_i^2=0，且 1+N_i 保持 H，所以左侧 G 包含于右侧。对每个 i，整数幂为 (1+N_i)^m=1+mN_i。整数在复仿射直线上 Zariski 稠密，因此 G 包含整个一参数子群 1+tN_i，故 Lie(G) 包含每个 N_i。定理 12.1 迫使 Lie(G)=sp(H)。Sp(H) 连通，特征零代数群光滑，故 G 的单位连通分量与 Sp(H) 同维，从而等于 Sp(H)。证毕。

这是经典 nilpotent-exponential 论证；[DdG19, Proposition 3.1] 对两个幂零生成元写出同样机制，任意有限族的证明完全相同。有限正特征不适用上述整数点论证，不能从完整 Lie 生成性直接推出离散有限群的 Zariski 稠密性。

对第 4 节已重构且非退化的 R，推论 12.2 以同样论证给出 Sp(J)。如果真实几何表示已经被证明是该八维表示的 primitive 外幂，才可进一步推出其 27 维连通像为 PSp8。目前这一几何比较仍是额外义务。

## 16. 实际构造 27 维 primitive 空间的独立精确实例

对第 14 节稀疏八维 H，定义收缩映射

\[
c_H:\Lambda^2K^8\to K,\qquad c_H(e_i\wedge e_j)=H_{ij},
\]

并求出 W=ker(c_H) 的一个显式 27 维基。若收缩行的非零枢轴为 p，则其余每个基向量 q 取

\[
b_q=e_q-\frac{(c_H)_q}{(c_H)_p}e_p.
\]

基矩阵记为 B，并令 Δ_i 为 Λ²(1+N_i)−1 在该基上的矩阵，则

\[
B\Delta_i=(\Lambda^2(1+N_i)-1)B,
\quad \Delta_i^2=0,
\quad\operatorname{rank}\Delta_i=6.
\]

### 命题 16.1. 稀疏八维实例的 primitive 数据

上述 W 的维数为 27，每个 Δ_i 的平方为零且秩为 6；二阶及三阶迹相对于自然八维表示均带因子 6。由 8+7+21 个长度至多三的 Lie 词构成的系数矩阵秩为 36。

**证明。** 收缩行非零，故其核的维数为 28−1=27，所列 b_q 由一次消元给出一组基。N_i 是非零 rank-one 辛幂零元，外幂展开中二次项为零，所以 Δ_i 是其导出作用；在辛基中只有 f_1 映到 e_1，primitive 二阶外幂上恰有六个独立像 e_1∧z，因此 Δ_i²=0 且 rank Δ_i=6。迹因子由第 8 节的张量迹恒等式给出。第 14 节图的直径为 2，定理 13.1 与命题 14.1 给出第三层的 36 个独立方向。证毕。

这些矩阵是代数构造的实例，不是从 Fano 几何中导出的 monodromy 矩阵。

## 17. 精确滤过约束下的研究前沿

在八维 transvection 标架上，配对图给出生成整个辛李代数的充分条件以及生成所需的精确层数。几何层仍须完成以下实际比较：

1. RC+ 共同开集上的候选 U 是否给出一个非零平坦映射 Ψ:Λ²₀U→(R²覆盖族)_minus。第 9 节的关联循环还没有非零性证明。
2. 若走矩阵路线，要从实际几何退化构造 Δ_i，证明它们与候选 Λ²₀(1+N_i) 存在同一个可逆 intertwiner。二三阶迹一致本身不够。
3. RC− 需要独立几何来源或专门比较，不能复制 RC+ 的 Prym 身份。

若第 1 项或第 2 项完成并覆盖所需生成元，连通图定理即可供给相应的辛密度结论。当前精确 Lie 滤过结果没有单独约束尚未输入的几何表示，因此不把阶二 Fano 预期标为已解决。

## 18. 补充参考文献

[Yel21] Jeffrey Yelton. *Boundedness results for 2-adic Galois images associated to hyperelliptic Jacobians*. arXiv:1703.10917v5. Mathematische Nachrichten 294 (2021), 1629–1643. Proposition 3.1 and Remark 3.4. 图连通性及直径生成界是已有方法。
https://arxiv.org/abs/1703.10917

[DdG19] A. S. Detinko and W. A. de Graaf. *2-Generation of simple Lie algebras and free dense subgroups of algebraic groups*. arXiv:1905.01853v2. Proposition 3.1. 幂零 Lie 生成到指数子群 Zariski 稠密性的经典证明。
https://arxiv.org/abs/1905.01853

[LNR22] Martí Lahoz, Juan Carlos Naranjo, Andrés Rojas. *Geometry of Prym semicanonical pencils and an application to cubic threefolds*. arXiv:2106.08683v2. §6, printed p.15, RC+ 的偶二阶点条件。
https://arxiv.org/abs/2106.08683

## 19. 从真实 primitive 作用反推出自然算子

以下结果不把自然算子 rank one 当作输入，而从实际 primitive 外幂作用的平方为零推出它。几何八维 lift 的存在仍未被假定为已证。

设 K 是域，I 是有限指标集，n=|I|，记

\[
F_{kl}=E_{kl}-E_{lk},\qquad
\mathcal A_X(B)=XB+BX^t.
\]

当特征不为 2 时，交替系数矩阵 B 严格实现二阶外幂：向量 \(\sum_{i<j}B_{ij}e_i\wedge e_j\) 的导出作用就是 \(\mathcal A_X\)。该定义从实际矩阵乘法出发，没有输入一个宣称来自外幂的任意作用表。

### 定理 19.1. 一次收缩和二次收缩

对任意 X，不要求辛或幂零，均有

\[
\sum_j\mathcal A_X(F_{kj})_{ij}
=(n-2)X_{ik}+\delta_{ik}\operatorname{tr}X,\tag{19.1}
\]
\[
\sum_j\mathcal A_X^2(F_{kj})_{ij}
=(n-4)(X^2)_{ik}+2\operatorname{tr}(X)X_{ik}
+\delta_{ik}\operatorname{tr}(X^2).\tag{19.2}
\]

**证明。** 展开矩阵单位得

\[
\mathcal A_X(F_{kl})_{ij}
=X_{ik}\delta_{jl}-X_{il}\delta_{jk}
+\delta_{ik}X_{jl}-\delta_{il}X_{jk}.
\]

再由实际复合算出

\[
\mathcal A_X^2(B)=X^2B+2XBX^t+B(X^2)^t.
\]

其中 \((XF_{kl}X^t)_{ij}=X_{ik}X_{jl}-X_{il}X_{jk}\)。取 l=j 后对 j 求和，分别使用 \(\sum_jX_{ij}X_{jk}=(X^2)_{ik}\) 和对角求迹，即得两式。证毕。

### 定理 19.2. 二次外幂幂零强制自然 rank-one 因子

假设标量 2、n−2、n−4 在 K 中非零，tr X=0，且对所有 k,l 都有 \(\mathcal A_X^2(F_{kl})=0\)。则

\[
X^2=0,\qquad
\exists u,v\in K^I:\ X_{ij}=u_iv_j,\quad \sum_jv_ju_j=0.\tag{19.3}
\]

因而非零 X 的秩恰为一。

**证明。** 对 (19.2) 的对角再求和，得到

\[
2(n-2)\operatorname{tr}(X^2)=0.
\]

故 tr(X²)=0。回代所有条目得到 (n−4)X²=0，故 X²=0。此时未收缩的二次公式给出

\[
2(X_{ik}X_{jl}-X_{il}X_{jk})=0,
\]

所以全部二阶子式消失。若 X=0，取 u=v=0。否则选择真实非零枢轴 X_pq，定义

\[
u_i=X_{iq},\qquad v_j=X_{pj}/X_{pq}.
\]

用行 i,p 与列 j,q 的子式即得 X_ij=u_i v_j；同时

\[
\sum_jv_ju_j=(X^2)_{pq}/X_{pq}=0.
\]

证毕。这里没有把 nilpotent、rank one 或某个 Jordan 型写进输入。

n−4 条件是本收缩证明的边界，不声称 n=4 时存在相反实例。

## 20. primitive 子空间到全外幂的投影与读回

令 J 可逆且 J^t=−J，X^tJ=−JX。定义实际子空间和投影

\[
W_J=\{B:B^t=-B,\ \operatorname{tr}(JB)=0\},
\qquad
\pi_J(B)=B-\frac{\operatorname{tr}(JB)}nJ^{-1}.\tag{20.1}
\]

普通辛收缩在这些系数上的表达式与 tr(JB) 相差非零常数 −2，因此核就是 primitive 二阶外幂。假设 n≠0。

### 定理 20.1. 实际投影、实际限制与无损读回

J⁻¹ 交替，\(\mathcal A_X(J^{-1})=0\)，\(\mathcal A_X(W_J)\subset W_J\)，并且对交替 B 有

\[
\pi_J(B)\in W_J,\qquad
\mathcal A_X(\pi_J(B))=\mathcal A_X(B).\tag{20.2}
\]

**证明。** 转置 JJ⁻¹=1 并用 J^t=−J 得 (J⁻¹)^t=−J⁻¹。将 X^tJ=−JX 左右乘逆矩阵得 J⁻¹X^t=−XJ⁻¹，所以不变线被实际作用杀掉。
\(\mathcal A_X(B)\) 的转置由 B 的交替性直接计算；迹循环性给出

\[
\operatorname{tr}(J\mathcal A_X(B))
=\operatorname{tr}(JXB)+\operatorname{tr}(X^tJB)=0.
\]

最后 tr(JJ⁻¹)=n，代入投影定义得到其收缩为零，且删除不变线不改变作用。证毕。

### 定理 20.2. primitive 二次判据

假设 2、n、n−2、n−4 非零。如果上述实际限制 \(P_X=\mathcal A_X|_{W_J}\) 满足 \(P_X^2=0\)，则结论 (19.3) 成立。

**证明。** 从 X^tJ=−JX 和迹循环性推出 tr X=−tr X，故 tr X=0。对每个 F_kl 先使用 (20.2) 投影到 W_J。实际 P_X²=0 与被杀掉的不变线迫使 \(\mathcal A_X^2(F_{kl})=0\)，应用定理 19.2。证毕。

维数 8 下，交替系数空间维数为 28，收缩因 tr(JJ⁻¹)=8 非零而满射，所以 dim W_J=27。

### 定理 20.3. primitive infinitesimal 作用的显式逆

对实际 primitive 输入有

\[
\sum_j\mathcal A_X\bigl(\pi_J(F_{kj})\bigr)_{ij}=(n-2)X_{ik}.
\]

当 n−2≠0，右端可直接相除。特别地 n=8 时

\[
X_{ik}=\frac16\sum_j\mathcal A_X\bigl(\pi_J(F_{kj})\bigr)_{ij}.\tag{20.3}
\]

**证明。** (20.2) 将左边变成 (19.1)，再使用 tr X=0。证毕。

式 (20.3) 是在已经指定自然空间与辛形式后求逆，不能为一个任意 27 维空间凭空选择未知的外幂坐标结构。

## 21. 普通推论：必要性、充分性和局部 Jordan 类型

对特征零八维辛 X，有

\[
P_X^2=0\quad\Longleftrightarrow\quad X^2=0\text{ 且 }\operatorname{rank}X\le1.\tag{21.1}
\]

必要性由定理 20.2。充分性中将 X=u v^t 代入，交替 B 满足 v^tBv=0，所以 XBX^t=0；再用实际二次展开即可。

当 X≠0，可选辛基使其唯一非零基本作用为 f_1↦c e_1 (c≠0)。primitive 空间中的 f_1∧z (z∈span{e_2,...,e_4,f_2,...,f_4}) 分别映到 c e_1∧z，给出六个独立像方向，其余基本项均不增加像。因此

\[
\operatorname{rank}P_X=6,
\qquad\text{Jordan 类型为 }2^6 1^{15}.\tag{21.2}
\]

更一般地，若 X²=0 且 rank X=r 在 n 维辛空间中，写 t=n−2r。自然表示作为 nilpotent Jordan 模由 r 个二维块与 t 个平凡块组成。二阶外幂中，每两个二维块贡献一个三维块与一个平凡块，每个二维块与一个平凡块贡献一个二维块，同一二维块的外幂为平凡块；primitive 部分再删除一个不变平凡块。这给出

\[
\#J_3=\binom r2,\quad \#J_2=rt,
\quad \#J_1=r+\binom r2+\binom t2-1,
\]
\[
\operatorname{rank}P_X=r(n-r-1),
\qquad\operatorname{rank}P_X^2=\binom r2.\tag{21.3}
\]

这个分解可以通过对每个二维 Jordan 块的两个基向量直接求楔积得到。它解释了下面算例中 rank 2、3 的自然平方零算子仍会在 primitive 作用平方中留下秩 1、3，且不会被 (21.1) 错收为 rank one。此处不将经典 Jordan 张量分解单列为新发现。

## 22. 群元素的完整识别必须保留中心符号

以下在复数域上令 \(\rho:\mathrm{Sp}_8\to\mathrm{GL}(W_J)\) 为真实 primitive 二阶外幂表示。

### 定理 22.1. 不预设 unipotent 的群元素识别

若 g∈Sp8，\(\Delta=\rho(g)-1\ne0\)，且 Δ²=0，则存在 ε∈{1,−1} 和非零 rank-one N，使

\[
g=\varepsilon(1+N),\quad N^2=0,
\quad\Delta=\mathcal A_N|_{W_J}.\tag{22.1}
\]

**证明。** 先证明 kerρ={±1}。Sp8 固定由 J⁻¹ 张成的不变线，若它在 primitive 部分恒等，则全二阶外幂恒等。若 Λ²g=1，则 g 保持每个由 u,v 张成的二平面。固定非零 u，并取所有包含 u 的二平面之交，得到 gu∈Ku。故 g 是标量，外幂恒等迫使标量平方为 1。

取 g 的乘法 Jordan 分解 g_sg_u。因为 ρ(g)=1+Δ 幂单，ρ(g_s)=1，故 g_s=ε1。令 X=log(g_u)，则 X∈sp8，表示与 exp/log 相容给出

\[
\mathcal A_X|_{W_J}=\log(1+\Delta)=\Delta.
\]

定理 20.2 推出 X²=0 且 rank X≤1。Δ非零推出 X非零，因此 rank X=1，g_u=exp X=1+X。证毕。

特别地，若 g 本身已知幂单，ε=1。对于任意 primitive 观察，ε 不能恢复：ρ(g)=ρ(−g)。因此从 Δ²=0 直接声称 (g−1)²=0 是错误的；负号提升通常使 g−1 可逆。

这个定理仍要求已知 g 所在的自然辛空间和真实表示 ρ。它移除了自然 rank-one 和自然幂单的先验条件，保留了几何 lift 本身的义务。

## 23. 关联循环路线的对象核对与可用修正

进一步核对 [IW14, §2 and §4] 后，应补充第 9 节中“选择通用嵌入”的具体含义。一般 A∈A4 的 Prym 纤维 S 是曲面；但参数化 theta 中 Prym-embedded curves 的自然空间 F→S 的纤维是曲线 λ(X-tilde)，所以 dim F=3。其 tautological curve family C→F 的总空间维数为 4。该文 Theorem 4.1 研究的是 H5(F)→H3(Theta) 的 Abel-Jacobi 像，不是我们需要的 H2(A)_prim→H2(S)_minus 比较。

因此，原先的三维关联循环 Z⊂A×S 不能直接用这个自然四维全族代替。原文第 9 节已经保留了选择、下降和非零性义务；这里明确一个可用的修正：在这些实际族及适当紧化已经给定时，取 F 上相对 S 的 ample 除子类 η，设 r:C→F、p:F→S、e:C→A，则

\[
Z_\eta=(e,p\circ r)_*\bigl(r^*\eta\cap[C]\bigr)\in CH^3(A\times S)
\]

具有正确余维。可以由它定义

\[
\Psi_\eta(\alpha)=\frac{1-\tau^*}{2}(Z_\eta)_*(\theta\cup\alpha).
\]

这给出了修正后的具体候选，不证明其 primitive 反不变分量非零，也没有证明它在所需 moduli 基变换上的所有延拓与平坦性条件。特别不能由总族维数不同推断所有候选必为零，也不能把另一项 Abel-Jacobi 满射替代本问题的非零性。

## 24. 这些结果对公开问题增加了什么

已完成的表示结论是：给定真实八维辛 lift，27 维 primitive infinitesimal 平方零条件足以构造自然 rank-one nilpotence；对群元素还精确保留 ±1 中心歧义。由此可以把此前输入中的 rank-one 条件改成一个实际 27×27 矩阵平方检查，再连接第 12–15 节的配对图生成论。

未完成的关键仍是几何 lift 或非零平坦比较。没有把任意27维平方零算子都宣布具有辛外幂来源，没有用新矩阵实例宣称解决 [KLM26] 的阶二预期，也没有完成 Ψ_eta 的非零性。RC+ 与 RC− 的范围限制继续有效。

下一项决定性研究对象现在是实际几何的局部 monodromy 及其相容的全局 intertwiner，或修正循环 Z_eta 在 primitive 反不变 Kunneth 分量上的计算。局部 Jordan 类型2^6 1^15本身不识别整个全局 monodromy 群。

## 25. 补充参考文献与精确实例

[OM24] Ron Ofir and Michael Margaliot. *Multiplicative and additive compounds via Kronecker products and Kronecker sums*. arXiv:2401.02100. 本文借鉴其实际 compound/Kronecker 语境，不把外幂矩阵公式的存在宣称为新结果。
https://arxiv.org/abs/2401.02100

[DOG26] Debojyoti Dey, Ron Ofir and Christian Grussler. *Inversion of the Multiplicative Matrix Compound Operator*. arXiv:2605.27682v3, 15 July 2026. 该文研究乘法 compound 的逆问题；本文的 primitive infinitesimal 收缩与平方零识别是另一个明确陈述，不把乘法逆问题误作尚无人研究。
https://arxiv.org/abs/2605.27682

[IW14] Elham Izadi and Jie Wang. *The primitive cohomology of theta divisors*. arXiv:1410.5868v1. §2 的 Prym embeddings，§4 的三维参数空间 F 及 Theorem 4.1。它们只支持第 23 节所注明的具体对象与 Abel-Jacobi 结论。
https://arxiv.org/abs/1410.5868

### 命题 25.1. 八维 primitive 秩表

在八维辛空间中，对平方零且秩分别为 1、2、3 的自然算子，以及对角半单算子

\[
X_{\mathrm{ss}}=\operatorname{diag}(1,2,4,8,-1,-2,-4,-8),
\]

自然表示与 primitive 二阶外幂作用的秩如下：

|自然算子|自然rank|自然平方rank|primitive rank|primitive平方rank|
|---|---:|---:|---:|---:|
|平方零rank1|1|0|6|0|
|平方零rank2|2|0|10|1|
|平方零rank3|3|0|12|3|
|一般辛算子|8|8|24|24|

**证明。** 前三行由 (21.3) 取 n=8、r=1,2,3 直接得到。对 X_ss，二阶外幂的权为两个对角权之和；只有四个 e_i∧f_i 具有零权，删除辛形式张成的不变线后零权空间为三维。因此 primitive 作用及其平方的秩均为 27−3=24。证毕。

### 命题 25.2. 中心符号不可由 primitive 像恢复

若 N 是非零 rank-one 辛幂零元，则 1+N 与 −(1+N) 的 primitive 像相同；共同增量的秩为 6 且平方为零，而 −(1+N)−1 的秩为 8。

**证明。** −1 位于 primitive 二阶外幂表示的核中，所以两个群元素有同一像。式 (21.2) 给出共同增量的秩与平方。最后

\[
-(1+N)-1=-(2+N),\qquad (2+N)^{-1}=\tfrac12-\tfrac14N,
\]

故负号提升减去单位阵可逆。证毕。
