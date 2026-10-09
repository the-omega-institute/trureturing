# AURIC FIB 金字塔：信息逃逸、素数轨迹与热力学作用

## 状态与范围

本文把仓库中已有的 AURIC FIB 五态概率几何、Information Escape 的分层捕获、黄金热层以及素数/Fibonacci 轴放到同一套接口中。文中有三种状态标签：已有结果，本文件的新推导，以及尚未完成的开放接口。已有结果来自 Foundational Formulas、Boundary Calculus、KernelChain、LayeredCapture、GoldenHeatLayers、PrimeAxisEscape 和相关 Lean 文件。本文件的新推导是在已有静态几何上加入一维质量作用流。把离散 native continuation、素数支撑扩张和真实环境热力学接成同一个状态更新，仍然是开放问题。

“信息逃逸”需要分层理解。对只观察均值坐标的观察者，κ 纤维上的状态全部不可辨识，因而是已经逃逸到 kernel 之外的隐藏信息。对完整五态观察者，这部分信息由条件关联和 KL 储备量表示，并沿质量作用流耗散到最大熵完成。这个过程不是信息凭空离开封闭系统。若要称作向环境逃逸，还需要加入环境、chemostat 或擦除协议，并把环境熵流写进账本。

## 1. 静态金字塔是一个带隐藏纤维的商空间

状态顺序取为

\[
p=(p_0,p_2,p_3,p_5,p_{25}),\qquad p_i\ge 0,\qquad \sum_i p_i=1.
\]

定义均值投影

\[
X=p_2+p_{25},\qquad Y=p_5+p_{25},\qquad Z=p_3,\qquad r=1-Z.
\]

投影像是

\[
P=\{(X,Y,Z): X,Y,Z\ge0,\ X+Z\le1,\ Y+Z\le1\}.
\]

给定 \((X,Y,Z)\) 后，唯一剩余的自由坐标是 \(\kappa=p_{25}\)，并且

\[
p_0=r-X-Y+\kappa,\quad
p_2=X-\kappa,\quad
p_3=Z,\quad
p_5=Y-\kappa,\quad
p_{25}=\kappa.
\]

合法纤维区间为

\[
\kappa_-=\max(0,X+Y-r)\le\kappa\le
\kappa_+=\min(X,Y).
\]

对应的核方向是

\[
\nu=(1,-1,0,-1,1).
\]

因此 \(p+t\nu\) 保持 \((X,Y,Z)\) 不变。观察者只看 \((X,Y,Z)\) 时，整个 κ 线段被压成同一个点。纤维宽度

\[
w_\kappa=\kappa_+-\kappa_-
=\min\{X,Y,r-X,r-Y\}
\]

是静态的不可辨识容量。它在四个侧面上归零。这里归零表示隐藏方向没有可走长度，不表示逃逸更强。

底面关联坐标为

\[
\Delta=p_0p_{25}-p_2p_5=r\kappa-XY.
\]

在 \(r>0\) 时，\(\Delta=0\) 等价于条件 \(z=0\) 后的独立完成。最大熵完成为

\[
\kappa_*=\frac{XY}{r},
\]

其对应分布记为 \(p_*\)。在 \(r=0\) 的顶点单独定义 \(p_*=\delta_3\)，不能把 \(XY/r\) 当作定义。

已有 Foundational Formulas 的身份式给出

\[
D(p\Vert p_*)=H_{\ln}(p_*)-H_{\ln}(p)
=r\,I(x:y\mid z=0)\ge0,
\]

以及

\[
\operatorname{TV}(p,p_*)=\frac{2|\Delta|}{r}
\]

在 \(r>0\) 时成立。仓库的 Shannon 熵定理通常使用 \(H_2\)；本文件热力学公式使用自然对数熵 \(H_{\ln}=-\sum p_i\ln p_i\)。二者关系是 \(H_{\ln}=(\ln2)H_2\)。

状态标签 0、2、3、5、25 是五态字母，不是五个素数。特别是 25 是 \(5^2\)。任何素数动力学都必须另行给出标签到算术坐标的映射和跃迁生成元，不能从标签排列直接推出。

## 2. “一层一层逃逸”的正确类型

Information Escape 的 KernelChain 和 LayeredCapture 已经给出离散层级

\[
K_0\supseteq K_1\supseteq\cdots\supseteq K_m,
\]

其中 \(K_j\) 是第 \(j\) 层仍然无法区分的 pair 集合。第 \(j\) 层首次分离的 pair 构成 capture 增量，所有增量互不相交并与最终 unresolved 集合一起分割初始 pair 集合。相应的 capture count、escape rate 和 survival/hazard 具有望远镜恒等式。

把这个结构和金字塔连接时，建议使用带类型的层状态

\[
\mathcal S_j=(K_j,\ P_j,\ \kappa_j,\ \Delta_j),
\]

而不是把所有量压成一个标量：

- \(K_j\) 记录微观观察 kernel 和剩余信息；
- \(P_j=(X_j,Y_j,Z_j)\) 记录宏观均值位置；
- \(\kappa_j\) 记录同一点上的隐藏 fiber 坐标；
- \(\Delta_j\) 或 \(D_j=r_jI_j\) 记录尚未热化的关联；
- 素数支撑和获取成本另放在 arithmetic/cost 分量。

本文件的质量作用流只改变 \(\kappa\)，因此 \(P_j\) 不动。它描述的是“先被投影隐藏，再在隐藏纤维内耗散”的内部信息逃逸。若要从金字塔底面向顶点真正跨层，需要增加改变 \(X,Y,Z\) 的反应或控制，并为这些方向指定 mobility 和环境账本。现有 κ 流不能单独承担这一步。

## 3. κ 纤维上的质量作用动力学

在本节中，p_i 是归一化概率，p_0p_{25} 与 p_2p_5 是确定性 mean-field 质量作用项。因此这里得到的是确定性 detailed-balanced mass-action ODE，不是有限状态 Markov 链；有限粒子主方程需要另行处理跃迁计数和随机熵产。把五个状态标签看作复合状态，定义一条可逆通道

\[
2+5\rightleftharpoons 0+25.
\]

反应向量仍为 \(\nu=(1,-1,0,-1,1)\)。令

\[
a=p_0p_{25},\qquad b=p_2p_5,
\]

并取对称速率 \(\gamma\ge0\)。反应流写成

\[
J=\gamma(b-a),\qquad \dot p=J\nu.
\]

于是

\[
\dot\kappa=\gamma(b-a)
=-\gamma(r\kappa-XY).
\]

四个线性守恒量为

\[
\ell_0=(1,1,1,1,1),\quad
\ell_X=(0,1,0,0,1),\quad
\ell_Y=(0,0,0,1,1),\quad
\ell_Z=(0,0,1,0,0),
\]

且 \(\ell\cdot\nu=0\)。因此归一化和 \((X,Y,Z)\) 精确保持。

当 \(r>0\) 时，精确解为

\[
\kappa(t)=\kappa_*+(\kappa_0-\kappa_*)e^{-\gamma r t},
\]

并且

\[
\Delta(t)=\Delta_0e^{-\gamma r t}.
\]

因为 \(\kappa(t)\) 是 \(\kappa_0\) 与 \(\kappa_*\) 的凸组合，而 \(\kappa_*\) 位于合法区间，所以轨迹始终留在同一条可行纤维内。于是

\[
\operatorname{TV}(p_t,p_*)=
\operatorname{TV}(p_0,p_*)e^{-\gamma r t}.
\]

这里的逃逸速率是隐藏关联的收缩速率 \(\gamma r\)，不是宏观点 \(P_t\) 的移动速率。靠近顶点时，如果沿可行族 \(X=\alpha r,\ Y=\beta r\) 逼近 \(r\to0\)，则

\[
w_\kappa=r\min\{\alpha,\beta,1-\alpha,1-\beta\}=O(r),
\]

\[
|\Delta|\le r^2/4=O(r^2),
\]

而固定 \(\gamma\) 下的绝对松弛时间

\[
\tau=(\gamma r)^{-1}
\]

发散。也就是说，顶点附近可藏的绝对信息量变少，隐藏方向的可走长度变短，但相对于归一化后的剩余质量，动力学变慢。这是一个明确的 escape bottleneck，而不是“越靠近顶点越快”。

对内部点，熵导数为

\[
\dot H_{\ln}
= \gamma(a-b)\ln\frac{a}{b}
= \gamma(b-a)\ln\frac{b}{a}\ge0.
\]

严格不等式在 \(a\ne b\) 时成立。由已有 KL/条件互信息身份式，

\[
\frac{d}{dt}D(p_t\Vert p_*)
=-\gamma(a-b)\ln\frac{a}{b}\le0.
\]

因此条件互信息和隐藏 KL 储备量单调下降，Shannon 熵单调上升。边界点用连续极限解释；当某个侧面使 fiber 退化为单点时，\(a=b\)，流恒为零。\(r=0\) 的顶点也必须单独处理。

这个结论的语义是：相关结构被转换为可观测 Shannon 熵，而不是在封闭五态系统中自动变成外界热。若需要物理热，必须额外定义浴、reset、measurement 或 chemostat。

## 4. 把“能量最优”写成详细平衡，而不是口号

对正向和反向速率分别取 \(k_f,k_r>0\)：

\[
J=k_f p_2p_5-k_r p_0p_{25},\qquad \dot p=J\nu.
\]

设状态能量为 \(E_i\)，并满足详细平衡比值

\[
\frac{k_f}{k_r}=e^{-\beta\Delta E},\qquad
\Delta E=E_0+E_{25}-E_2-E_5.
\]

定义

\[
F(p)=\sum_iE_ip_i-\beta^{-1}H_{\ln}(p).
\]

则

\[
\dot F
=-\beta^{-1}J
\ln\frac{k_fp_2p_5}{k_rp_0p_{25}}
\le0,
\]

并且反应熵产生为

\[
\sigma
=J\ln\frac{k_fp_2p_5}{k_rp_0p_{25}}\ge0.
\]

这是固定 \((X,Y,Z)\) 化学计量类上的 free-energy Lyapunov 定理。对称情形 \(k_f=k_r=\gamma\) 等价于 \(\Delta E=0\)，所以平衡点正是最大熵完成 \(p_*\)。若 \(\Delta E\ne0\)，平衡 κ 会移动，不能继续使用 \(XY/r\) 作为平衡坐标。

也可以用对数平均 mobility

\[
L(a,b)=\frac{a-b}{\ln a-\ln b}>0
\]

把对称流写成

\[
\dot\kappa=-\gamma L(a,b)\,\partial_\kappa
\bigl[-H_{\ln}(p)\bigr].
\]

这说明它是固定纤维上的 Onsager 梯度流。它严格表达了“热力学耗散最优”的一部分，但没有给出有限时间的唯一动作最优，也没有自动包含外界做功。

## 5. 金字塔层与黄金热层的几何接口

GoldenHeatLayers 已经给出每个黄金层的发散横坐标

\[
\alpha_k=\frac1{o5Beta(k+1)},\qquad
\alpha_0=\frac1{\varphi^2},\qquad
\alpha_k\downarrow0.
\]

为了给金字塔一个单调的层高坐标，可以定义模型接口

\[
r_k=\frac{\alpha_k}{\alpha_0},\qquad
Z_k=1-r_k.
\]

于是 \(r_0=1,\ Z_0=0\)，并且 \(Z_k\uparrow1\)。在这个接口下，第 \(k\) 层的水平截面面积按

\[
\operatorname{Area}(P_{Z_k})=r_k^2
\]

缩放，底面 determinant 的预算满足

\[
|\Delta_k|\le r_k^2/4.
\]

这正好把几何横截面、关联容量和黄金热层的二次缩放放在同一坐标中。但这是定义的 embedding，不是从现有物理模型推出的热力学等式。仓库目前没有把层号 \(k\) 证明为真实时间，也没有把 \(r_k\) 证明为实际温度、能量或动力学松弛参数。

在离散层上，可以把每一层的三个读数并列保存：

\[
(\text{capture mass}_k,\ w_{\kappa,k},\ D_k).
\]

它们分别回答“这一层分离了多少 pair”“还剩多少不可辨识 fiber 容量”“还有多少隐藏关联没有热化”。这三个量不能合成一个无类型的 escape 标量。

## 6. 素数到底是不是轨迹

素数更适合做离散 arithmetic seam 和支撑扩张坐标，而不是直接充当连续 κ 轨迹。

### 6.1 Euclid 外部素数是离散逃逸边

对有限素数支撑 \(S\)，定义

\[
N(S)=\prod_{p\in S}p+1.
\]

已有 PrimeAxisEscape 定理保证存在素数 \(q\mid N(S)\) 且 \(q\notin S\)。因此可以构造图

\[
S\longrightarrow S\cup\{q\},
\qquad
\text{cost}(S\to S\cup\{q\})=\ln q.
\]

这是一条严格的离散支撑逃逸边。PrimeCashflow 还提供了 \(\sum_p|u(p)|\ln p\) 型长度/成本。它和 κ 纤维耗散是两种不同的坐标，前者改变算术支撑，后者保持宏观均值而消除隐藏关联。

### 6.3 有限整数载体产生真正的 prime seam

连续概率流可以精确到达 (kappa_*=XY/r)，但有限计数载体通常只能取整数格点。把底面条件分布单独归一化：底面总量为整数 (R>0)，边际计数为 (A,B)，四格计数为

[
(n_{00},n_{10},n_{01},n_{11})
=(R-A-B+k, A-k, B-k, k),
]

其中 (k) 是整数。连续独立目标是

[
k_*=rac{AB}{R}.
]

若 (R) 不整除 (AB)，则任何整数表都无法满足 (Delta_R=Rk-AB=0)。令

[
d=operatorname{dist}(AB,Rmathbb Z)>0.
]

取合法整数格点中最接近 (k_*) 的 (k_Z)，则条件底面分布 (q_k=n/R) 至少保留

[
operatorname{TV}(q_{k_Z},q_*)=rac{2d}{R^2},
qquad
D_{ln}(q_{k_Z}Vert q_*)gerac{8d^2}{R^4}
]

的残差，第二个不等式使用自然对数版本的 Pinsker 下界。若五态总样本量为 (N)，且 (R=Nr)，则完整五态 law 的这部分 KL 乘以 (r=R/N)，完整 law 的 TV 乘以 (r)。因此这里的归一化必须先声明，不能把条件底面和五态 law 的距离混用。

写 (R=prod_p p^{e_p}) 时，独立目标的最简分母是

[
rac{R}{gcd(R,AB)}.
]

如果 (p) 是 Fibonacci 的 primitive divisor，满足 (pmid R)、(p
mid AB)，那么这个 prime seam 在该层首次出现。取 (R=F_n) 时，若 (z(p)=n)，则 (p) 在第 (n) 层进入目标分母。这给出素数几何的严格版本：连续 κ 流趋向零关联，有限整数载体却在 primitive rank 处出现不可消除的自由能地板。

这里仍需保留两个边界。第一，primitive p 只证明该层的独立目标不可达，不保证最近格点距离或自由能地板随层单调增加。第二，若边际 (A,B) 随层变化，p-adic 余量也会变化，必须把它们写进层间 map 后才能讨论全局单调性。

### 6.2 Fibonacci 的素数周期是 projective seam

令

\[
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
z(p)=\min\{n>0:p\mid F_n\}.
\]

对每个素数 p，Fibonacci 矩阵恒等式给出

\[
M^{z(p)}\equiv aI\pmod p,\qquad a\ne0.
\]

因此 \(z(p)\) 是 \(M\) 在 \(PGL_2(\mathbb F_p)\) 中的阶。完整的 Pisano 周期是

\[
\pi(p)=z(p)\,\operatorname{ord}_{\mathbb F_p^\times}(a),
\]

而不是一般地等于 \(z(p)\)。由 Cassini 恒等式，\(a^2\equiv(-1)^{z(p)}\pmod p\)，所以这个尺度因子是有限的；\(p=2,5\) 也必须保留为单独检查的边界案例。这个桥的几何含义是：投影到 projective phase 后，尺度信息只剩一个有限周期 seam。

因此可以把同一条候选轨迹写成两层：

- 连续层：\(\kappa\) 或 \(\Delta\) 沿纤维耗散；
- 离散层：在 \(z(p)\) 或 \(\pi(p)\) 的 primitive return sector 处记录素数 seam。

除非另行证明素数支撑与 reaction rate 有耦合，否则不能把 \(\sum_{z(p)=n}\ln p\) 当作内生的 \(\gamma_n\)。它只是一个新定义的 arithmetic cost。

## 7. 动作最优、耗散最优和做功最优必须分开

固定端点 \(\kappa(0)=\kappa_0,\ \kappa(T)=\kappa_1\)，取几何二次作用

\[
\mathcal A[\kappa]=\frac12\int_0^T\dot\kappa(t)^2\,dt.
\]

现有 HilbertSubspaceAction 定理给出唯一极小路径，即仿射插值，且

\[
\mathcal A_{\min}=\frac{(\kappa_1-\kappa_0)^2}{2T}.
\]

质量作用指数路径的作用量为，令 \(\lambda=\gamma r\)：

\[
\mathcal A_{\exp}
=\frac{(\kappa_0-\kappa_*)^2\lambda}{4}
\bigl(1-e^{-2\lambda T}\bigr).
\]

与同端点仿射极小值相比，比例为

\[
\frac{\mathcal A_{\exp}}{\mathcal A_{\rm affine}}
=\frac{\lambda T}{2}
\coth\frac{\lambda T}{2}\ge1.
\]

所以质量作用流是详细平衡和熵产生意义下自然的耗散路径，但在这个固定端点、固定时长的纯二次作用量中，通常不是最小动作路径。两种“最优”优化了不同目标。

若要研究真正的跨层几何最优，应给 \(q=(X,Y,Z)\) 增加可控反应，并定义

\[
\mathcal A_q=\frac12\int \dot q^{\mathsf T}\zeta(q)\dot q\,dt
\]

或 Fisher–Rao/摩擦度量。然后才可以讨论 q 方向的 geodesic、有限时间耗散和边界奇异性。现有 κ 流只给出了隐藏纤维方向的一个可解切片。

因此目前最可靠的目标不是单一总能量，而是保持分量类型的 Pareto 向量，例如

\[
(\text{unresolved hazard},\
w_\kappa,\
D(p\Vert p_*),\
\text{prime cashflow},\
\mathcal A_q,\
\text{acquisition cost}).
\]

只有选定温度、浴、时间约束和控制变量后，才可以把其中一部分合成一个具体的优化问题。

## 8. 已证实、本文推导与下一步 formalization

### 已有仓库结果

- AURIC FIB 五态概率律、金字塔像、κ fiber、fiber width 和 determinant \(\Delta\)。
- 最大熵完成、KL/条件互信息身份式和 TV 关系。
- KernelChain、LayeredCapture 的分层捕获、survival/hazard 望远镜。
- GoldenHeatLayers 的 \(\alpha_k\) 单调下降和 \(\alpha_0=1/\varphi^2\)。
- PrimeAxisEscape 的 Euclid 外部素数扩张。
- HilbertSubspaceAction 的固定端点二次作用量极小路径。
- Gibbs/relative-entropy、量子关联和 Jarzynski 相关的独立热力学接口。

### 本文件新增加的数学模型

- 用唯一核方向 \(\nu=(1,-1,0,-1,1)\) 定义 κ 质量作用流。
- 精确解 \(\kappa(t)=\kappa_*+(\kappa_0-\kappa_*)e^{-\gamma rt}\)。
- \(\Delta\)、TV、KL 和条件互信息的单调/指数收缩结论。
- 非对称 \(k_f,k_r\) 下的详细平衡 free-energy 下降和熵产生。
- 黄金层到金字塔高度 \(r_k,Z_k\) 的显式 embedding。
- Euclid 素数轨迹、Fibonacci projective rank 与 κ 耗散之间的类型化接口。

这些是理论层的新推导，尚未作为 Lean 定理提交。文中没有修改 judge、CI 或既有定义，也没有把理论模型标成物理实验定律。

### 建议的下一批 Lean 目标

1. 在五态向量上形式化 \(\nu\) 的四个守恒量和一维 κ lift。
2. 证明 \(\kappa_*\) 位于可行区间，并用凸组合证明正性和不变性。
3. 形式化 \(\Delta(t)\) 与 TV 的指数收缩。
4. 在自然对数版本中证明 \(\dot H_{\ln}\ge0\) 和详细平衡 free-energy 下降。
5. 给 KernelChain/LayeredCapture 加上 \((P_j,\kappa_j,D_j)\) 的 typed product，而不是把离散 escape 和宏观 law 混成一个标量。
6. 证明 Fibonacci 的 projective order 与 full Pisano period 之间的有限尺度因子，并显式处理 \(p=2,5\)。

## 仓库锚点

- docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md
- docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_BOUNDARY_CALCULUS.md
- docs/develop/Blueprint/D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.md
- docs/develop/Blueprint/D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.md
- docs/develop/Blueprint/D5/S3/Midline/HeatLayers/GoldenHeatLayers.md
- docs/develop/Blueprint/D5/S3/Axis/PrimeAxisEscape.md
- docs/develop/Blueprint/D5/S3/Observer/HilbertGeometry/HilbertSubspaceAction.md
- docs/develop/Blueprint/D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.md
- docs/develop/Blueprint/D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.md
- docs/develop/Blueprint/D5/S3/Entropy/Thermodynamics/JarzynskiSecondLaw.md
- 与 AURIC FIB escape audit typed spec 相邻的 PR #14815

本文只建立理论接口和可验证的下一步，不宣称已经完成 AURIC 到 Information Escape 的 Lean bridge，也不宣称素数轨迹是唯一的物理几何轨迹。
