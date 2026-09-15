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

- `D5/S3/Observer/Hankel/HankelRankMinimality.lean` 的有限 Hankel 分解及可达空间模全未来不可见方向的维数公式；
- `D5/S3/Observer/Hankel/SequenceHankelRealization.lean` 的实际线性实现；
- automath 的 `subsec__pom-pw-tannaka-krein-reconstruction.tex` 所提出的群重构问题；
- newmath 的 `TannakaKreinUp`、`MonodromyUp` 记录接口。它们不提供本问题所需的上同调比较。

本文给出两组完整矩阵证明的 Lean 源及配套 Scribe。当前会话未执行 Lean elaboration、kernel 检查或 Scribe 编译；因此它们是待编译验证的形式化源，不能标为 Lean-closed。
第 7 至 10 节是普通数学推导与明确的后续研究义务，尚无对应 Lean 声明。

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

Lean 源：`D5/S3/Observer/Monodromy/TransvectionTraceReconstruction.lean`。
主声明为 `recoveredGram_eq_gauge`、`simultaneous_reconstruction` 和
`reconstruct_transvection_word`；`anchor_diagonal_inverse` 给出实际双边逆。

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

上述源位于 `D5/S3/Observer/Monodromy/TraceSymplecticCertificate.lean`，主声明为
`reconstructed_generators_preserve_form`、`invariant_alternating_form_unique`、
`form_nondegenerate_iff`，另有实际 `reconstructed_readback`。

作为这些结果的普通数学推论，在至少两个指标、p_i≠0、t_ii=0 的条件下，R 的生成元存在非退化不变交替形式，当且仅当非锚点 t 交替且 det R≠0。
必要性由定理 4.2 写 B=qJ；B 非退化迫使 q≠0，交替性与非退化性便传回 J。
这一组合 iff 尚未单独写为 Lean 声明。

## 5. 该观察集保留了哪些信息

两个零对角标架若具有相同的锚点二阶及三阶迹，其 R 完全相同，由定理 3.1 获得显式同时相似。
相似的是带标签的操作族；不允许任意改换标签来弱化结论。

当 p,t 属于 K 的子域 L 时，R 与 J 的每个条目均在 L 中。
所以在这一星形坐标下，标架及不变形式同时下降到观察域，无须选择平方根。
这是构造公式的直接推论；它不把任意特征零表示的迹域与定义域一概混同。

还须区分一次有限证书与 invariant trace field：后者对所有有限指标子群取交。
本文的有限标架结论不计算该无限交，也不证明 [KLM26] 的大阶圆分域结论。

## 6. 二阶资料不足：一个非退化反例

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
这个反例是普通精确计算，尚未单独成为 Lean 声明。

## 7. 从源结果继续推导：28 个有理观察与二阶歧义

本节是推导，尚未形式化为代数簇或超越次数定理。
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

## 8. 接到真正的 27 维读数：一个尚待形式化的精确恒等式

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
完成下一步形式化时，应定义真实二阶外幂、primitive 核及实际算子后证明上述恒等式，不能把迹比例作为输入字段。

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

## 10. 精确算例与证据边界

本次使用 SymPy 的有理数矩阵运算独立检验：

- 维数 2 至 8 的 42 个一般零对角星形矩阵，以及各自长度为 9 的非交换词，全部满足同时共轭公式；
- 维数 2、4、6、8 的交替实例满足每个生成元保持 J，且 det R=det J=1；
- 第 6 节反例的两行列式均为 1、全部二阶迹一致、指定三阶迹分别为 -1 和 1；
- 一个八指标但实际秩为 6 的退化标架被 det J=0 正确拦截；
- 四维实例对所有矩阵条目求解交替不变形式线性方程组，解空间维数为 1；
- 在独立构造的 28 维二阶外幂矩阵上，检查了 rank-one 恒等式及六组三元组的迹比例因子 6。不变直线被杀掉是第 8 节普通证明中的步骤，并未把数值 28 维检验冒称为独立构造了 27 维 primitive 基。

有限算例不是全称证明，也不是 Lean 编译记录。本次两个 Lean 源没有 sorry、admit 或新增公理；这只是源文本检查，不能替代 kernel 检查。

## 参考文献

[KLM26] Thomas Krämer, Daniel Litt, Marco Maculan. *E6-local systems from cubic threefolds*. arXiv:2604.20970v1, 22 April 2026. §1.1 的阶二预期；本文不重复申报其已完成的大阶 E6 存在结果。
https://arxiv.org/abs/2604.20970

[Ebe24] Sean Eberhard. *Diameter of classical groups generated by transvections*. arXiv:2308.07086v3, 3 May 2024. §3, especially (3.2), Propositions 3.3 and 3.4; §4, Proposition 4.1. 这些是迹及不变形式的已有方法。
https://arxiv.org/abs/2308.07086

[Don92] Ron Donagi. *The fibers of the Prym map*. arXiv:alg-geom/9206008v2, 23 June 1992. Theorem 5.3 and Remark 5.4, printed p.47. 本文只将其用作具体双覆盖/Prym 几何输入，不将它说成已经给出目标上同调比较。
https://arxiv.org/abs/alg-geom/9206008


## 附录：独立的有理数算例核验

以下脚本只验证第 10 节的有限算例及反例，不执行 Lean。它从矩阵乘法和楔积定义重新计算；固定随机种子，输出写入当前目录的 `audit_results.json`。

```python
"""Exact arithmetic checks of the proposed statements; this is not a Lean run."""
from __future__ import annotations
import itertools, json, random
from pathlib import Path
import sympy as s

rng = random.Random(260420970)

def inc(H: s.Matrix, i: int) -> s.Matrix:
    out = s.zeros(H.rows)
    out[i, :] = H[i, :]
    return out

def readings(H: s.Matrix, a: int = 0):
    ns = [inc(H, i) for i in range(H.rows)]
    p = [(ns[a]*n).trace() for n in ns]
    t = s.Matrix(H.rows,H.rows,lambda i,j:(ns[a]*ns[i]*ns[j]).trace())
    return ns,p,t

def recover(p,t,a=0):
    n=len(p)
    R=s.Matrix(n,n,lambda i,j: 0 if i==a and j==a else
               1 if i==a else p[i] if j==a else t[i,j]/p[j])
    mu=[s.S.One if i==a else -1/p[i] for i in range(n)]
    return R,s.diag(*mu)*R

count=0
for n in range(2,9):
    for sample in range(6):
        H=s.Matrix(n,n,lambda i,j:0 if i==j else rng.choice([-3,-2,-1,1,2,3]))
        ns,p,t=readings(H)
        R,_=recover(p,t)
        D=s.diag(1,*list(H[0,1:]))
        assert R==D*H*D.inv()
        nrs=[inc(R,i) for i in range(n)]
        for i in range(n):
            assert ns[i]**2==s.zeros(n)
            assert D*ns[i]*D.inv()==nrs[i]
        w=[rng.randrange(n) for _ in range(9)]
        W,WR=s.eye(n),s.eye(n)
        for i in w:
            W=W*(s.eye(n)+ns[i]); WR=WR*(s.eye(n)+nrs[i])
        assert D*W*D.inv()==WR
        count+=1

symplectic=[]
for n in [2,4,6,8]:
    H=s.Matrix(n,n,lambda i,j:0 if i==j else 1 if i<j else -1)
    ns,p,t=readings(H)
    R,J=recover(p,t)
    assert J.T==-J
    assert all((s.eye(n)+inc(R,i)).T*J*(s.eye(n)+inc(R,i))==J for i in range(n))
    assert J.det()!=0
    symplectic.append({'dimension':n,'gram_det':str(R.det()),'form_det':str(J.det())})

H=s.Matrix(4,4,lambda i,j:0 if i==j else 1 if i<j else -1)
Hp=H.copy(); Hp[1,2]=-1; Hp[2,1]=1
ns,p,t=readings(H); nsp,pp,tp=readings(Hp)
assert all((ns[i]*ns[j]).trace()==(nsp[i]*nsp[j]).trace() for i in range(4) for j in range(4))
assert H.det()==Hp.det()==1 and t[1,2]==-1 and tp[1,2]==1

H7=s.Matrix(7,7,lambda i,j:0 if i==j else 1 if i<j else -1)
ix=list(range(7))+[6]
Hs=s.Matrix(8,8,lambda i,j:H7[ix[i],ix[j]])
_,ps,ts=readings(Hs); Rs,Js=recover(ps,ts)
assert Hs.rank()==Rs.rank()==Js.rank()==6 and Js.det()==0

# Solve every matrix entry of T_i^t B T_i=B in the six-dimensional space of
# alternating four-by-four matrices; the nullspace must be exactly one-dimensional.
R,J=recover(p,t)
variables=s.symbols('b0:6'); pairs=list(itertools.combinations(range(4),2))
B=s.zeros(4)
for x,(i,j) in zip(variables,pairs):B[i,j]=x;B[j,i]=-x
constraints=[]
for i in range(4):
    T=s.eye(4)+inc(R,i)
    constraints.extend(list(T.T*B*T-B))
A,_=s.linear_eq_to_matrix(constraints,variables)
assert len(A.nullspace())==1

# Exterior-square differential and full exterior-square representation are
# independently assembled in the standard wedge basis.
def exterior(T):
    pairs=list(itertools.combinations(range(T.rows),2))
    return s.Matrix(len(pairs),len(pairs),lambda r,c:
                    T[pairs[r][0],pairs[c][0]]*T[pairs[r][1],pairs[c][1]]-
                    T[pairs[r][0],pairs[c][1]]*T[pairs[r][1],pairs[c][0]])
def derivative(X):
    n=X.rows; pairs=list(itertools.combinations(range(n),2)); at={p:i for i,p in enumerate(pairs)}
    out=s.zeros(len(pairs))
    def add(r,c,v):
        if r[0]==r[1]:return
        if r[0]>r[1]:r=(r[1],r[0]);v=-v
        out[at[r],c]+=v
    for c,(i,j) in enumerate(pairs):
        for k in range(n):add((k,j),c,X[k,i]);add((i,k),c,X[k,j])
    return out
H8=s.Matrix(8,8,lambda i,j:0 if i==j else 1 if i<j else -1)
ns,p,t=readings(H8)
ls=[derivative(N) for N in ns]
assert all(exterior(s.eye(8)+N)-s.eye(28)==L for N,L in zip(ns,ls))
for i,j,k in [(0,1,2),(0,3,6),(3,7,2),(1,1,4),(2,6,4),(5,4,3)]:
    assert (ls[i]*ls[j]).trace()==6*(ns[i]*ns[j]).trace()
    assert (ls[i]*ls[j]*ls[k]).trace()==6*(ns[i]*ns[j]*ns[k]).trace()

out={'seed':260420970,'random_exact_normal_forms_and_length9_words':count,
     'nondegenerate_symplectic_examples':symplectic,
     'pair_only_counterexample':{'both_gram_determinants':1,'triple_012':[-1,1]},
     'degenerate_eight_dimensional_chart_rank':6,
     'invariant_alternating_form_dimension_in_4d':len(A.nullspace()),
     'exterior_square_differential_dimension':28,'primitive_dimension':27,
     'tested_pair_and_triple_trace_factor_in_dimension8':6,
     'lean_elaboration_performed':False}
Path('audit_results.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
```

## 11. 几何范围修正：Prym 比较只直接覆盖偶二阶分量

本节修正第 2、9 节中未写出的必要范围。[Don92, §5.1, Theorems 5.2–5.3] 使用

\[
RC=RC^+\sqcup RC^-,\qquad \chi:A_4\dashrightarrow RC^+.
\]

χ 的目标是带偶二阶点的分量。[LNR22, §6, p.15] 明确将 RC+ 写成满足偶性条件的 (V,δ)，其中 δ 不在中间 Jacobian 的规范 theta 除子上。因此，第 9 节通过 A4 构造八维候选 U 及 Prym 关联循环的路线，目前只适用于相应 RC+ 共同开集。RC− 不能由这项识别自动纳入。

这不构成对 [KLM26] 阶二预期的反证。它修正的是本研究所用文献的适用范围。还不能把 Prym 纤维上的 λ 未经证明地解释为阿贝尔簇 A 上的取负映射；仅凭二阶外幂在取负下不变，不能推断第 9 节候选 Ψ 的反不变投影为零。

本轮新增两个 Lean 源 `TransvectionLieGeneration.lean`、`TransvectionLieFiltration.lean` 及对应 Scribe，仍未在此环境执行 Lean 或 Scribe 编译。以下声明为普通数学证明与待编译形式化源；有限矩阵核验的状态另列。

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

路径传播本身不需要 det H≠0；非退化性只用于证明全部 skew-adjoint 矩阵均有上述对称因子。Lean 源直接使用 Mathlib 的 `LieSubalgebra.lieSpan` 和 `skewAdjointMatricesLieSubalgebra`，没有预先给定的生成性字段。对应主声明为 `generated_eq_skewAdjoint`。

### 推论 12.2. 观察所重构的矩阵也具有完整生成性

继续第 4 节的 R,J。若 p 的非锚点坐标非零、t 交替且 det R≠0，则

\[
\operatorname{Lie}_K\langle N_i(R)\rangle=\mathfrak{sp}(J).
\]

**证明。** J=diag(μ)R 的各 μ_i 非零，N_i(J)=μ_iN_i(R)，故两个实际生成元集合的 Lie 闭包相同。J 的锚点行均为 1，其配对图连通。定理 4.3 给出 det J≠0，应用定理 12.1。证毕。

对应 Lean 声明为 `generated_row_scale` 和 `recovered_generated_eq_skewAdjoint`。此处不声称两组离散群生成元的抽象群相同。

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

对应完整 Lean 声明为 `TransvectionLieFiltration.layer_eq_band`。两边在源中独立定义：左边从矩阵、线性张成和交换子递推；右边从实际非零配对的有限路径定义，不把结论放入左边的定义。

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

对应 Lean 声明为 `layer_support` 和 `cross_mem_layer_iff`。

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

这两个计数推论尚未单独成为 Lean 声明。任意 Lie 括号排布的有界长度张成与上述右延长过程相同，普通证明由 Jacobi 恒等式逐步将右侧复合括号展开为对单个生成元的右延长，保持生成元出现次数；这个自由 Lie 排布比较也尚未形式化。

上界中的图直径已有 [Yel21, Remark 3.4] 的相关先例；这里得到的对象是完整的线性层、逐条目的零约束及下界。没有找到同一精确陈述的直接来源，但检索不构成全球新颖性认证，也不把它计为一个已解决的公开猜想。

## 14. 星形情况下的三次显式证书及锐性

若 H_ai,H_aj 非零，则式 (12.1)–(12.2) 给出

\[
C_{ij}=-\frac{[N_i,[N_a,N_j]]}{H_{ai}H_{aj}}
+\frac{H_{ij}}{H_{ai}^{2}}[N_a,N_i].\tag{14.1}
\]

该恒等式允许 i=j，也允许叶子之间 H_ij=0；只除以锚点边。对应 Lean 声明 `cross_cubic_certificate` 已给出逐项证明。

若 H 非退化，下列 n(n+1)/2 个矩阵形成 sp(H) 的一组基：所有 N_i，全部 n−1 个 [N_a,N_i]，以及每个非锚点无序对 i<j 对应的 [N_i,[N_a,N_j]]。

**证明。** N_i 对应对角对称矩阵单位，锚点交换子给出 C_ai。每个双交换子由 (14.1) 给出一个非零倍的独有 C_ij，加上已列出的 C_ai 方向。这是相对于完整对称矩阵单位基的可逆三角变换。证毕。基数与独立性推论尚未单独写为 Lean 声明。

一个八维锐性实例是：H_0j=1 (1≤j≤7)，H_12=H_34=H_56=1，其他上三角条目为零，下三角由交替性决定。其 det H=1，配对图有 10 条边且直径为 2。故各层维数为

\[
\dim L_0=8,\quad \dim L_1=18,\quad \dim L_2=36.
\]

长度二不够，长度三恰好足够。
对八顶点带权路径 H_(i,i+1)=i+1，维数曲线则为

\[
8,15,21,26,30,33,35,36.
\]

这些是定理 (13.4) 的具体实例，并已用独立有理数消元逐层核验。这里的长度是 Lie 词中的生成元出现次数，不是群的 Cayley 图直径，也不是数值积分的物理时间。

## 15. 特征零下的完整 Zariski 稠密性推论

以下是普通代数群证明，尚未作为 Lean 代数群声明输出。
在复数域上，取 det H≠0 且配对图连通的交替 H。则

\[
\overline{\langle1+N_i\rangle}^{\mathrm{Zar}}=\mathrm{Sp}(H).\tag{15.1}
\]

**证明。** N_i^2=0，且 1+N_i 保持 H，所以左侧 G 包含于右侧。对每个 i，整数幂为 (1+N_i)^m=1+mN_i。整数在复仿射直线上 Zariski 稠密，因此 G 包含整个一参数子群 1+tN_i，故 Lie(G) 包含每个 N_i。定理 12.1 迫使 Lie(G)=sp(H)。Sp(H) 连通，特征零代数群光滑，故 G 的单位连通分量与 Sp(H) 同维，从而等于 Sp(H)。证毕。

这是经典 nilpotent-exponential 论证；[DdG19, Proposition 3.1] 对两个幂零生成元写出同样机制，任意有限族的证明完全相同。有限正特征不适用上述整数点论证，不能从完整 Lie 生成性直接推出离散有限群的 Zariski 稠密性。

对第 4 节已重构且非退化的 R，推论 12.2 以同样论证给出 Sp(J)。如果真实几何表示已经被证明是该八维表示的 primitive 外幂，才可进一步推出其 27 维连通像为 PSp8。目前这一几何比较仍是额外义务。

## 16. 实际构造 27 维 primitive 空间的独立精确实例

前一轮只构造了 28 维二阶外幂。本轮对第 14 节稀疏八维 H，实际构造收缩映射

\[
c_H:\Lambda^2K^8\to K,\qquad c_H(e_i\wedge e_j)=H_{ij},
\]

并求出 W=ker(c_H) 的一个显式 27 维基。若收缩行的非零枢轴为 p，则其余每个基向量 q 取

\[
b_q=e_q-\frac{(c_H)_q}{(c_H)_p}e_p.
\]

基矩阵记为 B。独立构造真正的 Λ²(1+N_i) 后，在此基上求出 Δ_i 并逐一验证

\[
B\Delta_i=(\Lambda^2(1+N_i)-1)B,
\quad \Delta_i^2=0,
\quad\operatorname{rank}\Delta_i=6.
\]

在这些真实 27×27 矩阵上，全部不同指标的二阶迹及五组三阶迹通过因子 6 检验；由 8+7+21 个短 Lie 词构成的系数矩阵秩恰为 36。

这是一组完整的有理数计算实例，证明本轮表示证书有非空的真实外幂实例。它们是我们构造的矩阵，尚不是从 Fano 几何中导出的 monodromy 矩阵。未将这些算例冒称为全称 Lean 证明或几何猜想的验证。

## 17. 经本轮定理约束后的研究前沿

本轮在已经验证的八维 transvection 标架上，去掉了“生成整个辛李代数”这一额外假设，并计算了生成所需的精确层数。几何层仍须完成以下实际比较：

1. RC+ 共同开集上的候选 U 是否给出一个非零平坦映射 Ψ:Λ²₀U→(R²覆盖族)_minus。第 9 节的关联循环还没有非零性证明。
2. 若走矩阵路线，要从实际几何退化构造 Δ_i，证明它们与候选 Λ²₀(1+N_i) 存在同一个可逆 intertwiner。二三阶迹一致本身不够。
3. RC− 需要独立几何来源或专门比较，不能复制 RC+ 的 Prym 身份。

若第 1 项或第 2 项完成并覆盖所需生成元，本轮的连通图定理即可供给相应的辛密度结论。当前精确 Lie 滤过结果没有单独约束尚未输入的几何表示，因此不把阶二 Fano 预期标为已解决。

## 18. 本轮新增参考文献与核验

[Yel21] Jeffrey Yelton. *Boundedness results for 2-adic Galois images associated to hyperelliptic Jacobians*. arXiv:1703.10917v5. Mathematische Nachrichten 294 (2021), 1629–1643. Proposition 3.1 and Remark 3.4. 图连通性及直径生成界是已有方法。
https://arxiv.org/abs/1703.10917

[DdG19] A. S. Detinko and W. A. de Graaf. *2-Generation of simple Lie algebras and free dense subgroups of algebraic groups*. arXiv:1905.01853v2. Proposition 3.1. 幂零 Lie 生成到指数子群 Zariski 稠密性的经典证明。
https://arxiv.org/abs/1905.01853

[LNR22] Martí Lahoz, Juan Carlos Naranjo, Andrés Rojas. *Geometry of Prym semicanonical pencils and an application to cubic threefolds*. arXiv:2106.08683v2. §6, printed p.15, RC+ 的偶二阶点条件。
https://arxiv.org/abs/2106.08683

本轮读取 dev `e88a14f641522c8f73dab28c1d4da1a37ea5d7b2`，并核对它相对前轮 base 的 23-commit 差异；没有重写已有数学源，也没有修改工程文件。新源未编译，`#print axioms` 未执行，有限测试不能替代它们。

以下两段脚本分别保存为 Python 文件运行，依赖 SymPy。它们从实际矩阵计算，不把本轮数学结论作为测试定义。第一段检验路径证书、三次基和真实 primitive 外幂；第二段独立迭代交换子空间，并与图距离带比较，包括不连通和退化实例。它们均已执行成功。

### audit_lie_generation.py

```python
"""Exact checks. Neither an exhaustive search nor a Lean compilation."""
from __future__ import annotations
from collections import deque
from itertools import combinations
from pathlib import Path
import json
import random
import sympy as s

rng = random.Random(814620260916)

def inc(H, i):
    N = s.zeros(H.rows)
    N[i, :] = H[i, :]
    return N

def cross(H, i, j):
    C = s.zeros(H.rows)
    C[i, :] += H[j, :]
    C[j, :] += H[i, :]
    return C

def bracket(X,Y): return X*Y-Y*X

def rank(mats):
    if not mats: return 0
    return s.Matrix.hstack(*(s.Matrix(list(M)) for M in mats)).rank()

def paths(H, start):
    out = {start: [start]}
    q=deque([start])
    while q:
        i=q.popleft()
        for j in range(H.rows):
            if H[i,j] and j not in out:
                out[j]=out[i]+[j];q.append(j)
    if len(out)!=H.rows: raise ValueError('disconnected pairing graph')
    return out

def verify(H):
    n=H.rows
    assert H.T==-H and H.det()!=0
    N=[inc(H,i) for i in range(n)]
    all_C=[]
    for i in range(n):
        for j,path in paths(H,i).items():
            C=2*N[i]
            for u,v in zip(path,path[1:]):
                edge=bracket(N[u],N[v])/H[u,v]
                C=(bracket(C,N[v])-H[i,v]*edge)/H[u,v]
            assert C==cross(H,i,j)
            all_C.append(C)
    for i in range(n):
        assert N[i]**2==s.zeros(n)
        assert N[i].T*H+H*N[i]==s.zeros(n)
    # Universal symmetric-factor decomposition sampled using independently chosen S.
    U=s.Matrix(n,n,lambda i,j:rng.randint(-4,4));S=U+U.T; X=S*H
    assert X.T*H+H*X==s.zeros(n)
    assert X*H.inv()==S
    reconstructed=s.zeros(n)
    for i in range(n):
        for j in range(n):reconstructed+=s.Rational(1,2)*S[i,j]*cross(H,i,j)
    assert reconstructed==X
    assert rank(all_C)==n*(n+1)//2
    return N

def star(n):
    # Anchor edges plus disjoint pairs among the first n-2 leaves.
    H=s.zeros(n)
    for j in range(1,n): H[0,j]=1;H[j,0]=-1
    for i in range(1,n-1,2):H[i,i+1]=1;H[i+1,i]=-1
    return H

results=[]
for n in (2,4,6,8):
    H=s.zeros(n)
    for i in range(n-1): H[i,i+1]=i+1;H[i+1,i]=-(i+1)
    N=verify(H)
    results.append({'kind':'path','n':n,'det':str(H.det()),'full_lie_dimension':n*(n+1)//2})
    H=star(n);N=verify(H)
    for i in range(1,n):
        for j in range(1,n):
            cubic=-bracket(N[i],bracket(N[0],N[j]))/(H[0,i]*H[0,j])
            cubic+=H[i,j]*bracket(N[0],N[i])/H[0,i]**2
            assert cubic==cross(H,i,j)
    selected=N+[bracket(N[0],N[i]) for i in range(1,n)]
    selected += [bracket(N[i],bracket(N[0],N[j])) for i,j in combinations(range(1,n),2)]
    d2=rank(N+[bracket(N[i],N[j]) for i,j in combinations(range(n),2)])
    d3=rank(selected)
    assert len(selected)==d3==n*(n+1)//2
    if n>=4: assert d2<d3
    results.append({'kind':'sparse-star','n':n,'det':str(H.det()),'length_le_2_dimension':d2,
                    'selected_length_le_3_count':len(selected),'length_le_3_dimension':d3})

# Actual primitive exterior square, constructed as a kernel, with its own basis.
H=star(8);N=[inc(H,i) for i in range(8)]
pairs=list(combinations(range(8),2));at={pair:i for i,pair in enumerate(pairs)}

def wedge(T):
    return s.Matrix(28,28,lambda r,c:T[pairs[r][0],pairs[c][0]]*T[pairs[r][1],pairs[c][1]]-
                                          T[pairs[r][0],pairs[c][1]]*T[pairs[r][1],pairs[c][0]])

def derivative(X):
    M=s.zeros(28)
    def add(i,j,col,x):
        if i==j:return
        if i>j:i,j=j,i;x=-x
        M[at[i,j],col]+=x
    for col,(i,j) in enumerate(pairs):
        for k in range(8):add(k,j,col,X[k,i]);add(i,k,col,X[k,j])
    return M

contraction=s.Matrix([[H[i,j] for i,j in pairs]])
pivot=next(i for i in range(28) if contraction[i])
keep=[i for i in range(28) if i!=pivot]
B=s.zeros(28,27)
for col,q in enumerate(keep):B[q,col]=1;B[pivot,col]=-contraction[q]/contraction[pivot]
assert contraction*B==s.zeros(1,27) and B.rank()==27
L=[]
for Ni in N:
    Li=derivative(Ni)
    assert wedge(s.eye(8)+Ni)==s.eye(28)+Li
    restricted=(Li*B)[keep,:]
    assert B*restricted==Li*B and restricted**2==s.zeros(27)
    assert restricted.rank()==6
    L.append(restricted)
for i,j in combinations(range(8),2):
    assert (L[i]*L[j]).trace()==6*(N[i]*N[j]).trace()
for i,j,k in [(0,1,2),(0,2,3),(3,4,5),(0,0,1),(1,3,6)]:
    assert (L[i]*L[j]*L[k]).trace()==6*(N[i]*N[j]*N[k]).trace()
selected27=L+[bracket(L[0],L[i]) for i in range(1,8)]
selected27 += [bracket(L[i],bracket(L[0],L[j])) for i,j in combinations(range(1,8),2)]
assert rank(selected27)==36
out={'seed':814620260916,'connected_frame_checks':results,
     'primitive_space_dimension':27,'primitive_increment_ranks':[M.rank() for M in L],
     'primitive_lie_certificate_rank':36,'pair_and_triple_factor':6,
     'lean_compiled':False,'geometric_monodromy_matrices_supplied':False}
Path('audit_lie_generation_results.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
```

### audit_filtration.py

```python
"""Independently iterate actual commutator spaces and compare with graph bands."""
from collections import deque
from itertools import combinations
from pathlib import Path
import json
import sympy as s

def inc(H,i):
    M=s.zeros(H.rows);M[i,:]=H[i,:];return M

def cross(H,i,j):
    M=s.zeros(H.rows);M[i,:]+=H[j,:];M[j,:]+=H[i,:];return M

def basis(mats):
    A=s.Matrix.hstack(*(s.Matrix(list(M)) for M in mats))
    return [mats[i] for i in A.rref()[1]]

def distances(H):
    n=H.rows;D={}
    for a in range(n):
        seen={a:0};q=deque([a])
        while q:
            u=q.popleft()
            for v in range(n):
                if H[u,v]!=0 and v not in seen:seen[v]=seen[u]+1;q.append(v)
        for b,d in seen.items():D[a,b]=d
    return D

def check(H,name):
    n=H.rows;N=[inc(H,i) for i in range(n)];D=distances(H)
    B=basis(N);profile=[];inv=H.inv() if H.det()!=0 else None
    for k in range(n):
        target=[cross(H,i,j) for i in range(n) for j in range(i,n) if D.get((i,j),n+1)<=k]
        TB=basis(target)
        assert len(B)==len(TB)==len(basis(B+TB))
        if inv is not None:
            predicted=n+sum(D.get((i,j),n+1)<=k for i,j in combinations(range(n),2))
            assert len(B)==predicted
            for X in B:
                S=X*inv
                assert S==S.T
                assert all(S[i,j]==0 for i in range(n) for j in range(n) if D.get((i,j),n+1)>k)
        profile.append(len(B))
        B=basis(B+[X*Ni-Ni*X for X in B for Ni in N])
    return {'name':name,'n':n,'det':str(H.det()),'ranks_by_generator_length_1_to_n':profile}

out=[]
for n in [4,6,8]:
    H=s.zeros(n)
    for i in range(n-1):H[i,i+1]=i+1;H[i+1,i]=-(i+1)
    out.append(check(H,'weighted_path'))
    H=s.zeros(n)
    for i in range(1,n):H[0,i]=1;H[i,0]=-1
    for i in range(1,n-1,2):H[i,i+1]=1;H[i+1,i]=-1
    out.append(check(H,'sparse_star'))
H=s.zeros(8)
for start in [0,4]:
    for i in range(start,start+3):H[i,i+1]=1;H[i+1,i]=-1
out.append(check(H,'two_disconnected_path_blocks'))
H=s.Matrix(5,5,lambda i,j:0 if i==j else 1 if i<j else -1)
out.append(check(H,'singular_odd_complete_graph'))
result={'exact_filtration_checks':out,'lean_compiled':False,'proof_by_exhaustive_search':False}
Path('audit_filtration_results.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
```
