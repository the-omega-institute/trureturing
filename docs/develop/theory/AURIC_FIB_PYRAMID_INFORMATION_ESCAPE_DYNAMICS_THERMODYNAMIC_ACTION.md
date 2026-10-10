# AURIC FIB 金字塔：信息逃逸、素数轨迹与热力学作用

## 模型与适用范围

在 [Foundational Formulas](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md) 的五态概率几何上加入一维质量作用流，并与离散分层捕获、黄金热层以及素数/Fibonacci 轴组成带类型的模型接口。把 [Boundary Calculus](AURIC_FIB_ATOM_PYRAMID_BOUNDARY_CALCULUS.md) 的离散 native continuation、素数支撑扩张和真实环境热力学接成同一个状态更新，仍然是开放问题。

“信息逃逸”需要分层理解。对只观察均值坐标的观察者，κ 纤维上的状态全部不可辨识，因而是已经逃逸到 kernel 之外的隐藏信息。对完整五态观察者，这部分信息由条件关联和 KL 储备量表示，并在固定纤维且 \(\gamma r>0\) 时沿质量作用流耗散到最大熵完成。这个过程不是信息凭空离开封闭系统。若要称作向环境逃逸，还需要加入环境、chemostat 或擦除协议，并把环境熵流写进账本。

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

状态标签 0、2、3、5、25 是五态字母，不是五个素数。按 Foundational Formulas 定义 2.1，native 标签 \([25]=[2+5]\) 表示同窗共同选择，数量为 \(2+5=7\)，不是数值 \(5^2\)。任何素数动力学都必须另行给出标签到算术坐标的映射和跃迁生成元，不能从标签排列直接推出。

## 2. “一层一层逃逸”的正确类型

[KernelChain](../../../Blueprint/D5/S3/ConceptDynamics/InformationEscapeHierarchy/KernelChain.md) 和 [LayeredCapture](../../../Blueprint/D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture.md) 给出离散层级

\[
K_0\supseteq K_1\supseteq\cdots\supseteq K_m,
\]

其中 \(K_j\) 是第 \(j\) 层仍然无法区分的 pair 集合。第 \(j\) 层首次分离的 pair 构成 capture 增量，所有增量互不相交并与最终 unresolved 集合一起分割初始 pair 集合。相应的 capture count、escape rate 和 survival/hazard 具有望远镜恒等式。

把这个结构和金字塔连接时，定义带类型的层状态

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

而在 \(\gamma r>0\) 时，绝对松弛时间为

\[
\tau=(\gamma r)^{-1}
\]

在固定 \(\gamma>0\)、\(r\to0^+\) 时发散。\(\gamma=0\) 时，任意合法初态的流恒为零，\(p_t=p_0\)，没有有限的松弛时间；\(r=0\) 时只有顶点态，也不使用上述倒数。也就是说，在正速率分支上，顶点附近可藏的绝对信息量变少，隐藏方向的可走长度变短，但相对于归一化后的剩余质量，动力学变慢。这是一个明确的 escape bottleneck，而不是“越靠近顶点越快”。

对内部点，熵导数为

\[
\dot H_{\ln}
= \gamma(a-b)\ln\frac{a}{b}
= \gamma(b-a)\ln\frac{b}{a}\ge0.
\]

严格不等式恰在 \(\gamma>0\) 且 \(a\ne b\) 时成立；\(\gamma=0\) 时熵导数为零。由已有 KL/条件互信息身份式，

\[
\frac{d}{dt}D(p_t\Vert p_*)
=-\gamma(a-b)\ln\frac{a}{b}\le0.
\]

因此条件互信息和隐藏 KL 储备量单调下降，Shannon 熵单调上升。上述对数公式先在内部点使用；边界按单边极限解释，理想混合熵的导数可能发散，但 ODE 本身仍可有有限的单边速度。当某个侧面使 fiber 退化为单点时，a=b，流恒为零。r=0 的顶点也必须单独处理。

这个结论的语义是：相关结构被转换为可观测 Shannon 熵，而不是在封闭五态系统中自动变成外界热。若需要物理热，必须额外定义浴、reset、measurement 或 chemostat。

## 4. 把“能量最优”写成详细平衡，而不是口号

对正向和反向速率分别取 \(k_f,k_r>0\)：

\[
J=k_f p_2p_5-k_r p_0p_{25},\qquad \dot p=J\nu.
\]

设状态能量为 \(E_i\)、逆温度 \(\beta>0\)，并满足详细平衡比值

\[
\frac{k_f}{k_r}=e^{-\beta\Delta E},\qquad
\Delta E=E_0+E_{25}-E_2-E_5.
\]

定义

\[
F(p)=\sum_iE_ip_i-\beta^{-1}H_{\ln}(p).
\]

在底部四格均为正的内部，

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

这是固定 \((X,Y,Z)\) 化学计量类上的 free-energy Lyapunov 定理。对称正速率情形 \(k_f=k_r=\gamma>0\) 等价于 \(\Delta E=0\)，所以平衡点正是最大熵完成 \(p_*\)。若 \(\Delta E\ne0\)，平衡 κ 会移动，不能继续使用 \(XY/r\) 作为平衡坐标。

对 \(a,b>0\)，定义对数平均 mobility；非对角时使用商式，沿对角线作连续延拓：

\[
L(a,b)=
\begin{cases}
\dfrac{a-b}{\ln a-\ln b},&a\ne b,\\
a,&a=b,
\end{cases}
\qquad L(a,b)>0.
\]

对角值由 \(\ln\) 的导数或商式极限得到。底部四格均为正时，把对称流写成

\[
\dot\kappa=-\gamma L(a,b)\,\partial_\kappa
\bigl[-H_{\ln}(p)\bigr].
\]

这说明它是固定纤维上的 Onsager 梯度流。\(a=b>0\) 时，熵梯度和流都为零，mobility 仍为 \(a\)。零概率边界不使用对数商或有限熵梯度；若作单边延拓，需同时指定 mobility 与梯度乘积的极限，ODE 的通量仍按原概率多项式定义。它严格表达了“热力学耗散最优”的一部分，但没有给出有限时间的唯一动作最优，也没有自动包含外界做功。

## 5. 金字塔层与黄金热层的几何接口

[GoldenHeatLayers](../../../Blueprint/D5/S3/Midline/HeatLayers/GoldenHeatLayers.md) 给出每个黄金层的发散横坐标

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

这把几何横截面、关联容量和黄金热层的二次缩放放在同一坐标中。该 embedding 是模型定义，不是从物理模型推出的热力学等式；层号 \(k\) 与真实时间、\(r_k\) 与实际温度、能量或动力学松弛参数之间的关系仍须另行给出。

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

[PrimeAxisEscape](../../../Blueprint/D5/S3/Axis/PrimeAxisEscape.md) 保证存在素数 \(q\mid N(S)\) 且 \(q\notin S\)。因此可以构造图

\[
S\longrightarrow S\cup\{q\},
\qquad
\text{cost}(S\to S\cup\{q\})=\ln q.
\]

这是一条严格的离散支撑逃逸边。PrimeCashflow 还提供了 \(\sum_p|u(p)|\ln p\) 型长度/成本。它和 κ 纤维耗散是两种不同的坐标，前者改变算术支撑，后者保持宏观均值而消除隐藏关联。

### 6.3 有限整数载体产生真正的 prime seam

连续概率流可以精确到达 \(\kappa_*=XY/r\)，但有限计数载体通常只能取整数格点。把底面条件分布单独归一化：底面总量为整数 \(R>0\)，边际计数为 \(A,B\)，四格计数为

\[
(n_{00},n_{10},n_{01},n_{11})
=
(R-A-B+k,\ A-k,\ B-k,\ k),
\]

其中 \(k\) 是整数。连续独立目标是

\[
k_*=\frac{AB}{R}.
\]

若 \(R\) 不整除 \(AB\)，则任何整数表都无法满足

\[
\Delta_R=Rk-AB=0.
\]

令

\[
d=\operatorname{dist}(AB,R\mathbb Z)>0.
\]

取合法整数格点中最接近 \(k_*\) 的 \(k_Z\)，则条件底面分布 \(q_k=n/R\) 至少保留

\[
\operatorname{TV}(q_{k_Z},q_*)
=
\frac{2d}{R^2},
\qquad
D_{\ln}(q_{k_Z}\Vert q_*)
\ge
\frac{8d^2}{R^4}
\]

的残差，第二个不等式使用自然对数版本的 Pinsker 下界。若五态总样本量为 \(N\)，且 \(R=Nr\)，则完整五态 law 的这部分 KL 乘以 \(r=R/N\)，完整 law 的 TV 乘以 \(r\)。因此这里的归一化必须先声明，不能把条件底面和五态 law 的距离混用。

写

\[
R=\prod_p p^{e_p}
\]

时，独立目标的最简分母是

\[
\frac{R}{\gcd(R,AB)}.
\]

如果 \(p\) 是 Fibonacci 的 primitive divisor，满足 \(p\mid R\)、\(p\nmid AB\)，那么这个 prime seam 在该层首次出现。取 \(R=F_n\) 时，若 \(z(p)=n\)，则 \(p\) 在第 \(n\) 层进入目标分母。这给出素数几何的严格版本：固定纤维且 \(\gamma r>0\) 时，连续 κ 流趋向零关联，有限整数载体却在 primitive rank 处出现有限分辨率的 lattice 残差。

这里仍需保留两个边界。第一，primitive p 只证明该层的独立目标不可达，不保证最近格点距离或自由能地板随层单调增加。第二，若边际 \(A,B\) 随层变化，p-adic 余量也会变化，必须把它们写进层间 map 后才能讨论全局单调性。

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

在固定纤维 \([\kappa_-,\kappa_+]\) 内，取 \(T>0\) 和合法端点 \(\kappa(0)=\kappa_0,\ \kappa(T)=\kappa_1\)。可容许路径 \(\kappa:[0,T]\to[\kappa_-,\kappa_+]\) 必须绝对连续；用其几乎处处导数定义扩展非负几何二次作用

\[
\mathcal A[\kappa]=\frac12\int_0^T\dot\kappa(t)^2\,dt.
\]

有限作用分支要求 \(\dot\kappa\in L^2([0,T])\)；其余绝对连续路径的作用为 \(+\infty\)。[HilbertSubspaceAction](../../../Blueprint/D5/S3/Observer/HilbertGeometry/HilbertSubspaceAction.md) 定义 1.2、定理 1.6 的绝对连续路径合同，经平移起点和时间缩放，给出这一可容许类中的唯一极小路径，即仿射插值，且

\[
\mathcal A_{\min}=\frac{(\kappa_1-\kappa_0)^2}{2T}.
\]

这里绝对连续性给出 \(\kappa_1-\kappa_0=\int_0^T\dot\kappa\,dt\)，Cauchy–Schwarz 给出上述下界；有限分支取等当且仅当导数几乎处处为 \((\kappa_1-\kappa_0)/T\)，再由绝对连续性恢复逐点仿射路径。仿射路径留在同一纤维区间内；连续但非绝对连续的路径不属于此极小问题。

在 \(r>0\) 的固定纤维上，质量作用指数路径的作用量为，令 \(\lambda=\gamma r\ge0\)：

\[
\mathcal A_{\exp}
=\frac{(\kappa_0-\kappa_*)^2\lambda}{4}
\bigl(1-e^{-2\lambda T}\bigr).
\]

当 \(\lambda>0\) 且 \(\kappa_0\ne\kappa_*\) 时，与同端点 \(\kappa_1=\kappa(T)\) 的仿射极小值相比，比例为

\[
\frac{\mathcal A_{\exp}}{\mathcal A_{\rm affine}}
=\frac{\lambda T}{2}
\coth\frac{\lambda T}{2}\ge1.
\]

若 \(\lambda=0\) 或 \(\kappa_0=\kappa_*\)，质量作用路径为常值，两种作用量均为零，比例不定义；右侧函数在 \(\lambda T\to0^+\) 时的极限为一，不是零速率下的 \(0/0\) 比值。顶点 \(r=0\) 也只有常值路径，无需定义 \(\kappa_*\) 的商式。

所以质量作用流是详细平衡和熵产生意义下自然的耗散路径，但在这个固定端点、固定时长的纯二次作用量中，通常不是最小动作路径。两种“最优”优化了不同目标。

若要研究真正的跨层几何最优，应给 \(q=(X,Y,Z)\) 增加可控反应，并在指定的度量域内，对固定 \(T>0\) 的绝对连续路径 \(q:[0,T]\to P\) 及沿路径可测的半正定 \(\zeta(q)\) 定义

\[
\mathcal A_q=\frac12\int_0^T \dot q^{\mathsf T}\zeta(q)\dot q\,dt
\]

或 Fisher–Rao/摩擦度量。有限作用要求该非负被积函数可积，否则取扩展值 \(+\infty\)；度量奇异边界的可容许提升须另行指定。然后才可以讨论 q 方向的 geodesic、有限时间耗散和边界奇异性。现有 κ 流只给出了隐藏纤维方向的一个可解切片。

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


## 8. 统一锥坐标：把三维底座和隐藏纤维放到同一个状态空间

令 \(r=1-Z\)。在 \(r>0\) 时再归一化底部四态：

\[
\alpha=\frac{X}{r},\qquad
\beta=\frac{Y}{r},\qquad
\eta=\frac{\kappa}{r}.
\]

于是

\[
p=
\bigl(
r(1-\alpha-\beta+\eta),\
r(\alpha-\eta),\
1-r,\
r(\beta-\eta),\
r\eta
\bigr),
\]

并且

\[
\max(0,\alpha+\beta-1)
\le\eta\le
\min(\alpha,\beta).
\]

这说明完整概率空间可以看成底部四态单纯形沿 \(r\in[0,1]\) 的锥化。\(r=0\) 时所有 \((\alpha,\beta,\eta)\) 都塌缩到同一个 apex \(p=\delta_3\)，所以它不是普通的全局积空间，而是边界退化的区间纤维化：

\[
\mathcal E=
\{(r,\alpha,\beta,\eta):0<r\le1,\ \eta\in I(\alpha,\beta)\}
\cup\{\delta_3\}.
\]

三维金字塔是忘掉 \(\eta\) 后的商：

\[
(X,Y,Z)=(r\alpha,r\beta,1-r).
\]

在这个坐标中，

\[
\kappa=r\eta,\qquad
\kappa_*=r\alpha\beta,\qquad
\Delta=r^2(\eta-\alpha\beta),
\]

\[
w_\kappa
=
r\min\{\alpha,\beta,1-\alpha,1-\beta\}.
\]

因此隐藏纤维的绝对长度按 \(r\) 缩放，关联 determinant 按 \(r^2\) 缩放，而条件分布中的关联 \(\eta-\alpha\beta\) 可以保持 \(O(1)\)。

在 \(0<r<1\) 且底部四格 \(q_i>0\) 的内部，概率 Fisher 度量在这个分解下满足

\[
ds_F^2
=
\frac{dr^2}{r(1-r)}
+
r\,ds^2_{F,\Delta^3}(q),
\]

其中 \(q\) 是底部四态条件分布。沿隐藏方向的度量为

\[
g_{\eta\eta}
=
r\left(
\frac1{q_0}+\frac1{q_2}+\frac1{q_5}+\frac1{q_{25}}
\right).
\]

这给出一个很重要的区分：Fisher 几何告诉我们哪些方向在统计上可辨识，Onsager mobility 则决定动力学实际沿哪个方向耗散。二者可以一起使用，但不能直接视为同一个 metric。


## 8.1. Toric fiber：四态列联表与金字塔锥

底部四态可以排列成一个 \(2\times2\) 列联表：

\[
q=(q_{00},q_{10},q_{01},q_{11})
=(p_0,p_2,p_5,p_{25}).
\]

它的边际映射是

\[
(q_{00},q_{10},q_{01},q_{11})
\longmapsto
(R,A,B)
\]

对应矩阵

\[
\begin{pmatrix}
1&1&1&1\\
0&1&0&1\\
0&0&1&1
\end{pmatrix}.
\]

其整数核由 Markov move

\[
m=(1,-1,-1,1)
\]

生成。这正是前面的 \(\nu\) 去掉 apex 坐标后的底部部分。因此 \(\kappa\) 纤维不是任意选出的线段，而是固定边际下的 toric fiber。

条件独立模型由二项式关系

\[
q_{00}q_{11}-q_{10}q_{01}=0
\]

定义。它在概率坐标中就是

\[
\Delta=0.
\]

所以：

- 金字塔投影忘掉的是列联表的 toric fiber；
- \(\kappa\) 质量作用流沿 Markov basis move 运动；
- 最大熵完成是 toric independence variety 与同一边际 fiber 的交点；
- 素数 seam 是有理独立点 \(k_*=AB/R\) 与整数 toric fiber 之间的分母障碍。

宏观三维金字塔可以看成底部 binary marginal square 加上 apex state 的锥化。\(Z\) 是 apex mass，\(r=1-Z\) 是底部质量。这个 toric 解释把概率几何、信息丢失、质量作用和整数素数障碍放在同一张代数图上。

## 8.2. Prime seam 的 p-adic 形式

在有限整数载体中，整数 determinant 是

\[
D_{\mathrm{int}}=Rk-AB,
\]

而金字塔中的概率 determinant 为

\[
\Delta=r^2\frac{D_{\mathrm{int}}}{R^2}.
\]

对素数 \(p\)，若

\[
e=v_p(R)>u=v_p(AB),
\]

则对任意整数 \(k\) 都有

\[
v_p(Rk)\ge e>u.
\]

因此 \(Rk\) 与 \(AB\) 在 p-adic 方向上不可能相消为零，并且

\[
v_p(D_{\mathrm{int}})=u.
\]

这给出一个精确的非闭合判据：

\[
\Omega_p=\max(0,v_p(R)-v_p(AB))
\]

是该 prime chart 上的最小 valuation obstruction。只有在 \(e\le u\) 时，进一步的 residue cancellation 才可能提高 \(v_p(D_{\mathrm{int}})\)。所以 p-adic seam 不是简单的“某个素数出现了”，而是 toric binomial independence 方程在该素数方向上无法闭合。

这可以称为 tropical/p-adic seam。它是算术几何中的离散障碍，不能直接当成连续物理距离，但它给出了素数如何进入可达性判据的精确方式。

## 9. 层间径向捕获与层内关联耗散

要让轨迹真正从金字塔底部走向顶点，定义一个额外的径向捕获生成元。令 \(\mu(t)\ge0\)，底部四态统一向 apex 3 泄漏：

\[
\dot p_i=J\nu_i-\mu p_i
\quad (i\in\{0,2,5,25\}),
\]

\[
\dot p_3=\mu r,
\]

其中

\[
J=\gamma(p_2p_5-p_0p_{25}).
\]

这个生成元保持归一化，并给出

\[
\dot r=-\mu r,
\qquad
\dot X=-\mu X,
\qquad
\dot Y=-\mu Y,
\qquad
\dot Z=\mu r.
\]

所以

\[
\dot\alpha=0,\qquad
\dot\beta=0.
\]

宏观轨迹是一条固定 ray：

\[
X(t)=r(t)\alpha_0,\qquad
Y(t)=r(t)\beta_0,\qquad
Z(t)=1-r(t).
\]

同时，隐藏坐标满足

\[
\dot\eta=-\gamma r(\eta-\alpha_0\beta_0).
\]

因此两个过程在归一化坐标中分离：

\[
r(t)
=
r_0\exp\left(-\int_0^t\mu(s)\,ds\right),
\]

\[
\eta(t)-\alpha_0\beta_0
=
(\eta_0-\alpha_0\beta_0)
\exp\left(-\int_0^t\gamma(s)r(s)\,ds\right).
\]

定义有效热化 exposure

\[
G(t)=\int_0^t\gamma(s)r(s)\,ds.
\]

则有一个非平凡的两时间尺度判据：

\[
G(\infty)=\infty
\quad\Longrightarrow\quad
\eta(t)\to\alpha_0\beta_0,
\]

而

\[
G(\infty)<\infty
\quad\Longrightarrow\quad
\text{归一化条件关联可能残留}.
\]

特别地，当 \(\mu,\gamma\) 为常数且 \(\mu>0\) 时，

\[
r(t)=r_0e^{-\mu t},
\qquad
G(\infty)=\frac{\gamma r_0}{\mu}<\infty.
\]

在此 \(\mu>0\) 分支且 \(r_0>0\) 时，系统渐近趋向 apex；若初始条件关联非零，有限的总 exposure 使归一化关联仍有残留。这是动力学和热力学之间的实际 tradeoff，不是单纯的几何类比。

常数 \(\mu=0\) 时则保留另一分支：

\[
r(t)=r_0,\qquad G(t)=\gamma r_0t,\qquad
G(\infty)=
\begin{cases}
\infty,&\gamma r_0>0,\\
0,&\gamma r_0=0.
\end{cases}
\]

因此零径向速率不产生向 apex 的运动；当 \(\gamma r_0=0\) 时 exposure 恒为零，不使用 \(\gamma r_0/\mu\)。

定义隐藏残差

\[
D_{\mathrm h}(t)=r(t)I(q_t).
\]

在内部点并使用对数平均 mobility \(\Lambda\) 时，有

\[
\dot D_{\mathrm h}
=
-\mu D_{\mathrm h}
-\gamma r^2\Lambda A^2
\le0,
\]

其中

\[
A=\ln\frac{q_0q_{25}}{q_2q_5}.
\]

第一项来自底部质量被径向捕获，第二项来自同一层内部的关联耗散。Shannon 熵本身在径向开放流下不必单调，因此这里应使用 \(D_{\mathrm h}\) 或指定的 excess free energy 作为 Lyapunov 量。

## 10. Fisher 几何中的“最优路径”与动力学路径

平方根嵌入

\[
p\longmapsto 2(\sqrt{p_0},\sqrt{p_2},\sqrt{p_3},\sqrt{p_5},\sqrt{p_{25}})
\]

把 Fisher 度量变成正象限球面上的欧氏度量。固定 §8 的正底面条件律 \(q\)，只沿 \(p=(rq_{00},rq_{10},1-r,rq_{01},rq_{11})\) 的同一径向射线改变 \(0<r<1\) 时，取径向坐标

\[
\theta=2\arcsin\sqrt r,
\]

有

\[
ds_{\mathrm{radial}}^2=d\theta^2.
\]

在这条固定 \(q\) 射线上，取 \(T>0\) 和端点 \(\theta_0,\theta_1\in(0,\pi)\)。可容许径向路径要求其提升 \(\theta:[0,T]\to(0,\pi)\) 绝对连续；径向 Fisher 二次作用为

\[
\mathcal A_{\mathrm{radial}}[\theta]=\frac12\int_0^T\dot\theta^2\,dt,
\qquad
\mathcal A_{\mathrm{radial},\min}=\frac{(\theta_1-\theta_0)^2}{2T}.
\]

有限作用要求 \(\dot\theta\in L^2([0,T])\)，否则在绝对连续类中取 \(+\infty\)。由 §7 的同一积分下界与取等条件，唯一作用极小路径是 \(\theta\) 的仿射插值；它以常速实现径向最短长度 \(|\theta_1-\theta_0|\)，并给出

\[
r(t)=\sin^2\frac{\theta(t)}2.
\]

若端点的底面条件律 \(q\) 改变，则须使用 §8 的完整 Fisher 度量 \(dr^2/[r(1-r)]+r\,ds^2_{F,\Delta^3}(q)\) 并指定该度量的可容许绝对连续路径，不能使用此固定射线极小结论。

它一般不是指数径向捕获

\[
r(t)=r_0e^{-\mu t}.
\]

指数捕获是开放系统的生成元轨迹，质量作用流是 Onsager 自由能梯度流，Fisher geodesic 是统计几何的最短路径。三者回答不同的优化问题，必须分别标记。

## 11. 同一 Fibonacci 层上的双重 prime seam

令 \(R_n=F_n\) 为有限整数载体，底部边际计数取 \(A_n=F_a\)、\(B_n=F_b\)，其中 \(0<a,b<n\)。若素数 \(p\) 是 \(F_n\) 的 primitive divisor，则

\[
p\mid R_n,\qquad
p\nmid A_nB_n.
\]

因此连续独立目标

\[
k_*=\frac{A_nB_n}{R_n}
\]

在整数格上不可达，至少出现一个 lattice seam。另一方面，令

\[
z(p)=\min\{m>0:p\mid F_m\}.
\]

则 \(z(p)=n\)，并且

\[
M^n\equiv a_p I\pmod p.
\]

所以同一层同时出现两种不同的 quotient loss：

1. 概率整数载体忘记连续独立点，产生 finite-resolution lattice seam；
2. \(PGL_2\) 观察者忘记 scalar phase，产生 projective seam。

若 \(p\notin\{2,5\}\) 且 \(n\) 为奇数，则

\[
a_p^2\equiv-1\pmod p,
\]

所以 \(\operatorname{ord}(a_p)=4\)，完整线性周期比 projective rank 多出四倍相位。若 \(n\) 为偶数，则 scalar order 为 1 或 2。

可以把第 \(n\) 层的算术缺陷记为

\[
\mathcal C_n=(Q_n,\sigma_n),
\]

其中

\[
Q_n=\frac{F_n}{\gcd(F_n,F_aF_b)}
\]

是独立目标的最简分母，\(\sigma_n\) 是 Fibonacci 矩阵在 projective closure 后剩余的 scalar phase。这个双缺陷比把素数当成几何坐标更准确，因为它同时记录有限计数可达性和观察商丢失的周期信息。

这里必须保留尺度限制。对于最近整数格点，lattice seam 通常是有限分辨率障碍，随着 \(R\) 增大，KL 残差密度可能趋于零。要得到宏观的非零自由能密度，需要额外的同余约束或使允许纤维距离保持 \(O(R)\)。因此 primitive prime 证明的是 exact independence 不可达，不自动证明物理相变或宏观能垒。

## 11.1. 统一混合生成元与三种逃逸

定义连续状态

\[
m=(r,\alpha,\beta,\eta)
\]

和离散状态

\[
s=(K,\text{prime seam},\text{Fibonacci phase}).
\]

候选混合状态空间为

\[
\mathcal M
=
\{(m,s):
0\le r\le1,\
\eta\in I(\alpha,\beta)\}.
\]

对连续观测量 \(f\)，可以把候选生成元写成

\[
\mathcal Gf
=
u_r\partial_r f
+
u_\alpha H_\alpha f
+
u_\beta H_\beta f
-
\gamma r\Lambda_q A_q\,\partial_\eta f
+
\sum_{s'}\lambda_{s,s'}
\bigl(f(m,s')-f(m,s)\bigr).
\]

这里：

- \(u_r\partial_r\) 是层间径向运动；
- \(H_\alpha,H_\beta\) 是 Fisher 水平提升，负责沿宏观底面移动并避免把坐标搬运误当成隐藏相关；
- \(-\gamma r\Lambda_q A_q\partial_\eta\) 是隐藏纤维上的 Onsager/KL 梯度流；
- 最后一项是 prime seam、Fibonacci phase 或 kernel layer 的离散跳跃。

§§3、9 的径向捕获和纤维耗散是两个特例。把 kernel 跳跃和 prime 跳跃加入同一个 \(\mathcal G\) 仍是候选框架，需要为每个离散跳跃指定高度更新、fiber lift 和成本单位。

在这个统一框架中，必须区分三种逃逸：

1. **quotient escape**：观察投影忘掉 \(\kappa\) 或 Fibonacci scalar phase，状态可以不变，但信息进入 kernel；
2. **dynamical escape**：生成元沿 \((r,\alpha,\beta,\eta)\) 移动，把状态带到另一层或另一条纤维；
3. **arithmetic escape**：宏观目标在连续空间存在，但在整数 toric fiber 上没有合法 lift，或者 projective closure 与 full linear closure 不一致。

素数只有在改变 arithmetic lift、phase closure 或 successor relation 时才是动力学变量。单纯出现在 \(R\) 或 \(F_n\) 的支持中，只是标签。


## 11.2. 素数三胞胎：二点投影相同而三点关联发生逃逸

这里需要先把“素数三胞胎”拆成两个层次。素数轮给出的只是有限模数下的候选位点；要求三个整数都是真素数，则是另一个算术事件。前者可以完全枚举，后者涉及素数三元组问题，不能把候选密度当成实际素数密度，也不能由本节推出存在无穷多个三胞胎。

### 11.2.1. 两个最小三胞胎构型与手性

除去唯一的特殊构型 \(\{3,5,7\}\) 后，直径为 \(6\) 的最小三点候选有两个有序模板：

\[
H_+=\{0,2,6\},\qquad H_-=\{0,4,6\}.
\]

若 \(h_0<h_1<h_2\)，定义有序间隙和三点方向

\[
g_1=h_1-h_0,\qquad g_2=h_2-h_1,\qquad
\chi(H)=\frac{g_2-g_1}{2}.
\]

于是 \(\chi(H_+)=+1\)、\(\chi(H_-)=-1\)。反射 \(h\mapsto h_2-h\) 交换两个模板并翻转 \(\chi\)。两个模板的无序二点距离多重集却完全相同：

\[
\bigl\{|h_i-h_k|:i<k\bigr\}=\{2,4,6\}.
\]

这给出了一个最小的“二点投影相同、三点读出可分离”例子。任何只依赖无序二点距离的观测，都不能区分 \(H_+\) 与 \(H_-\)；要区分它们，必须保留三点的顺序、定向或三阶关联。Foundational Formulas §16.4 给出两个三胞胎轮的 cyclic pair Gram 在每个轮模数上相同，而算术三点关联可以不同。因此把更高阶谱矩等同于三点算术量，需要额外的观测识别证明，不能仅由 pair Gram 推出。

这里还有一个初等的模 \(3\) 约束。若三个大于 \(3\) 的素数形如 \(n,n+2,n+4\)，三个数在模 \(3\) 中必有一个为零，所以唯一可能的是 \(3,5,7\)。对 \(H_+\)，要避开模 \(3\) 的零类必须有 \(n\equiv2\pmod3\)；对 \(H_-\)，必须有 \(n\equiv1\pmod3\)。两者还都要求 \(n\) 为奇数。于是这两个方向是同一局部几何的两个反射取向，而不是两个独立的连续坐标。

### 11.2.2. 素数轮给出离散的逃逸层

令前 \(j\) 个素数的轮模数为

\[
W_j=\prod_{i=1}^{j}p_i.
\]

对于一个有限模板 \(H\)，定义完全可枚举的轮候选集合

\[
C_j(H)=
\left\{a\in\mathbb Z/W_j\mathbb Z:
\gcd\!\left(\prod_{h\in H}(a+h),W_j\right)=1\right\},
\]

以及候选分数

\[
\rho_j(H)=\frac{|C_j(H)|}{W_j}\in[0,1].
\]

有限对数代价仅在 \(\rho_j(H)>0\)，即 \(C_j(H)\ne\varnothing\) 时定义为 \(\varepsilon_j(H)=-\log\rho_j(H)\)。为在后文层状态中保留所有有限模板，另定义扩展排斥坐标

\[
\bar\varepsilon_j(H)=
\begin{cases}
\varepsilon_j(H),&\rho_j(H)>0,\\
+\infty,&\rho_j(H)=0.
\end{cases}
\]

新增一个素数层时，只有在 \(\rho_{j-1}(H)>0\) 且 \(\rho_j(H)>0\) 的分支上才定义有限增量

\[
\Delta\varepsilon_j(H)=\varepsilon_j(H)-\varepsilon_{j-1}(H)
\]

来记录这一层去掉的候选比例。若 \(C_j(H)=\varnothing\)，下一轮的候选经模 \(W_j\) 约化仍须落在 \(C_j(H)\)，所以以后各轮也为空；这是吸收的排斥分支。从正分数进入空轮记录为灭绝事件，不定义有限增量；空轮之后也不作扩展代价相减，尤其不形成 \(+\infty-(+\infty)\)。例如 §11.2.8 的 \(H_C=\{0,2,4\}\) 满足 \(C_1(H_C)=\{1\}\)、\(C_2(H_C)=C_3(H_C)=\varnothing\)，其后两层只有扩展值和灭绝分支，没有有限对数或差分。

对所有有限 \(H\)，Foundational Formulas 命题 15.4 的 CRT 计数仍给

\[
\rho_j(H)=\prod_{q\mid W_j}\left(1-\frac{\nu_H(q)}q\right),
\qquad \nu_H(q)=|H\bmod q|.
\]

仅当每个 \(q\mid W_j\) 都有 \(\nu_H(q)<q\) 时，该乘积为正且

\[
\varepsilon_j(H)=-\sum_{q\mid W_j}\log\left(1-\frac{\nu_H(q)}q\right),
\qquad
\Delta\varepsilon_j(H)=-\log\left(1-\frac{\nu_H(p_j)}{p_j}\right)\quad(j\ge2).
\]

最后的增量式同时要求前一层为正。对非空 \(H\)，这里的局部条件就是 Foundational Formulas **定义 16.1** 的 \(1\le\nu_H(q)<q\)；它不限制一般候选集合的定义。\(H_+,H_-\) 在 \(q=2,3\) 的 \(\nu_H(q)\) 分别为一、二，在 \(q\ge5\) 为三，因而各轮上的有限代价和 CRT 公式均适用。

有限代价及其有限增量是组合意义上的对数代价，可以接到热力学式的作用量账本；它们还不是物理能量。实际三胞胎计数应另记为

\[
T_H(x)=\#\{n\le x:n+h\ \text{对所有 }h\in H\text{ 都为素数}\},
\]

并明确声明 \(T_H\) 与 \(|C_j(H)|\) 是两个不同对象。


由于 \(H_-=6-H_+\)，对任意轮模数 \(W\) 都有一个精确双射

\[
a\longmapsto -a-6\pmod W
\]

把 \(C_W(H_+)\) 送到 \(C_W(H_-)\)：若 \(h'=6-h\)，则
\[
(-a-6)+h'=-(a+h),
\]
所以每一项与 \(W\) 互素的条件完全保持。于是对所有 \(W\)，都有
\[
|C_W(H_+)|=|C_W(H_-)|,\qquad
\rho_W(H_+)=\rho_W(H_-),\qquad
\varepsilon_W(H_+)=\varepsilon_W(H_-).
\]
这是上游单位取负、子类型等价和有限基数供应在轮筛上的应用：只读候选密度的观察者在任何轮层都看不见三胞胎手性；其参数对应与来源见 §11.2.6。要让逃逸发生，读出必须保留 residue 的有序位置、镜像奇量、实际素数标签或三阶联合事件。

在小轮上可以直接看到“密度相同、方向不同”。有限枚举得到

| 轮模数 \(W\) | \(C_j(H_+)\) | \(|C_j(H_+)|/W\) | \(C_j(H_-)\) | \(|C_j(H_-)|/W\) |
|---:|---|---:|---|---:|
| \(2\) | \(\{1\}\) | \(1/2\) | \(\{1\}\) | \(1/2\) |
| \(6\) | \(\{5\}\) | \(1/6\) | \(\{1\}\) | \(1/6\) |
| \(30\) | \(\{11,17\}\) | \(2/30\) | \(\{7,13\}\) | \(2/30\) |
| \(210\) | \(\{11,17,41,101,107,137,167,191\}\) | \(8/210\) | \(\{13,37,67,97,103,163,187,193\}\) | \(8/210\) |
| \(2310\) | \(64\) 个 residue class | \(64/2310\) | \(64\) 个 residue class | \(64/2310\) |

这些是轮候选的精确有限计算，不是实际素数三元组计数。它们说明 \(\rho_j\) 或 \(\varepsilon_j\) 可以完全相同，而 residue 的平移、反射取向仍然不同；若读出只保留候选密度，三胞胎方向已经逃逸，若保留 residue 和顺序，则方向仍可被捕获。

给定一个读出仪器 \(\mathcal O_j\)，可以定义三点逃逸层

\[
K_3(H_+,H_-;\mathcal O)=
\min\left\{j:
\mathcal O_j(H_+)\ne\mathcal O_j(H_-)
\ \text{且二点投影仍相同}\right\}.
\]

若在指定的模数链上始终没有分离，则约定 \(K_3=+\infty\)。这个定义把“逃逸发生在第几层”变成可计算的有限问题：先固定模数链、候选状态和观测商，再寻找第一个能看见三点方向 \(\chi\) 的层。不同读出会给不同的逃逸层，因而“素数分布就是唯一轨迹”不是一个坐标无关的命题。

### 11.2.3. 从三胞胎方向到金字塔的隐藏纤维

在 AURIC 五态律中，底部四格按

\[
q=(p_0,p_2,p_5,p_{25})
\]

排列，宏观投影只保留

\[
X=p_2+p_{25},\qquad
Y=p_5+p_{25},\qquad
r=p_0+p_2+p_5+p_{25},
\]

而 \(\kappa=p_{25}\) 是纤维坐标。若两个三胞胎方向的编码 \(q_+\)、\(q_-\) 给出相同的 \((r,X,Y)\)，则它们的差必为

\[
q_+-q_-=\lambda(1,-1,-1,1),
\]

在完整五态顺序中就是

\[
(p_0,p_2,p_3,p_5,p_{25})_+
-
(p_0,p_2,p_3,p_5,p_{25})_-
=\lambda(1,-1,0,-1,1).
\]

因此三胞胎的方向信息可以全部落在 \(\kappa\) 纤维中：三维金字塔看到同一个点，三点读出却看到不同的 \(\kappa\) 或不同的 \(\chi\)。这正是“每一层逃逸轨迹”的严格版本。轨迹不是简单地在三维底面上画一条折线，而是

\[
\Gamma_j=
\bigl(K_j,r_j,\alpha_j,\beta_j,\eta_j,Q_j,\chi_j,\bar\varepsilon_j\bigr),
\]

其中 \(K_j\) 是当前信息核，\(r_j\) 是金字塔径向层，\(\alpha_j=X_j/r_j,\beta_j=Y_j/r_j\)，\(\eta_j=\kappa_j/r_j\)，\(Q_j\) 是整数 toric denominator seam，\(\chi_j\) 是三点方向，\(\bar\varepsilon_j\) 是含空轮吸收分支的扩展排斥坐标，其有限值为 \(\varepsilon_j\)。新增素数时，\(K_j\)、候选集、\(\chi_j\) 的可见性和 \(Q_j\) 都可能同时改变；这就是离散层间跃迁。

### 11.2.4. 三胞胎的三种“逃逸”

在这个接口中，三胞胎会产生三种不同的逃逸事件。

1. **商空间逃逸。** 二点投影把 \(H_+\) 与 \(H_-\) 送到同一个宏观点，三点读出恢复 \(\chi\)，于是信息从金字塔商空间回到隐藏纤维。

2. **动力学逃逸。** 层间径向捕获改变 \(r_j\)，而层内质量作用流改变 \(\eta_j\)。若径向捕获先于足够的三点暴露发生，系统可以已经接近 apex，但 \(\chi_j\) 或归一化关联仍未热化。

3. **算术逃逸。** 当 \(Q_j>1\) 或 \(v_p(R_j)>v_p(A_jB_j)\) 时，连续独立目标没有整数 lift；当 Fibonacci 层的 projective closure 已经成立而 scalar phase 尚未消失时，三点方向还带着额外的相位 seam。此时“逃逸”不是状态连续移动，而是可达状态集合发生了离散断裂。

这三类事件不能用同一个标量代替。一个候选模板可以在二点商空间中已经合并，却在算术轮中仍有很大的 \(\varepsilon_j\)；也可以已经到达 apex，而 \(G(\infty)\) 有限导致 \(\eta\) 和 \(\chi\) 留存。这正是层间动力学、层内热化和算术可达性需要分开记账的原因。

### 11.2.5. 与量子三体关联的接口

三胞胎方向可以由平移不变三阶观测分离；原点前缀仪器则保留不同的位置数据。经典概率中，固定全部一阶和二阶边缘仍可能有不同的三点联合律；在量子语言中，二体约化态也不能一般决定三体态。可把 \(\chi\) 的连续化代理写成三体累积量，或在量子提升中使用

\[
C_3=\operatorname{Tr}\!\left(\rho\,Z_1Z_2Z_3\right)
\]

这样的三体 Pauli 串。\(C_3\) 与 \(\langle Z_iZ_k\rangle\) 属于不同阶的可观测量；前者可以在二体 Gram 完全相同的情况下分裂两条三胞胎轨道。这个量子表达是接口候选，不是声称素数三胞胎本身已经实现了某个量子态。

相应地，若把三胞胎取向看成镜像奇变量，则它自然进入奇的三阶通道；二阶 pair Gram 是镜像偶的，三阶方向是镜像奇的。这与 Foundational Formulas §16 的“pair Gram 相同而 arithmetic three-point correlation 不同”一致，也解释了为什么只研究二阶谱量不足以决定三胞胎逃逸。

### 11.2.6. 轮筛反射的参数与来源

固定 \(W\in\mathbb N\)、\(W\ne0\)，令 \(a\in\mathbb Z/W\mathbb Z\)。把两个有向轮的可容许条件写为
\[
A_+(a)=\operatorname{IsUnit}(a)\land
\operatorname{IsUnit}(a+2)\land\operatorname{IsUnit}(a+6),
\]
\[
A_-(a)=\operatorname{IsUnit}(a)\land
\operatorname{IsUnit}(a+4)\land\operatorname{IsUnit}(a+6).
\]
这里的 \(\operatorname{IsUnit}\) 是模环中的单位条件；对自然数代表元，
它由 `ZMod.isUnit_iff_coprime` 对应到与 \(W\) 互素的轮筛条件。
仿射反射
\[
\rho_W(a)=-a-6
\]
满足
\[
\rho_W(\rho_W(a))=a,\qquad
\rho_W(a)+4=-(a+2),\qquad
\rho_W(a)+6=-a.
\]
第一式是环恒等式；后两式和 \(\rho_W(a)=-(a+6)\) 将三个单位条件逆序对应。
由单位取负的不变性得到
\[
A_+(a)\Longleftrightarrow A_-(\rho_W(a)).
\]
用同一个反射作逆映射，就得到
\[
\{a\in\mathbb Z/W\mathbb Z:A_+(a)\}\simeq\{b\in\mathbb Z/W\mathbb Z:A_-(b)\},\qquad
|\{a:A_+(a)\}|=|\{b:A_-(b)\}|.
\]
非零模数保证两边有限；这一步不要求平方自由性，也不使用实际素数三胞胎的无穷性。

上述推导明确应用 Mathlib 修订
`db584cd6d46c92f209a44c0f1c829460d327499d` 的既有供应，而非新的独立内容定理。
参数与供应对应如下：

- [ZMod.commRing](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/ZMod/Defs.lean#L175)
  取 \(n=W\)，提供上述反射恒等式所在的交换环；
  [IsUnit.neg](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Algebra/Ring/Units.lean#L98)
  与 [IsUnit.neg_iff](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Algebra/Ring/Units.lean#L102)
  分别应用于 \(a,a+2,a+6\)，提供单位取负的不变性。
- [Function.Involutive.toPerm](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Logic/Equiv/Basic.lean#L774)
  取 \(f=\rho_W\)，再将
  [Equiv.subtypeEquiv](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Logic/Equiv/Basic.lean#L262)
  的谓词取为 \(A_+,A_-\)，由逐点等价得到候选子类型的等价。
- [ZMod.fintype](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/ZMod/Defs.lean#L158)
  取 \(n=W\ne0\)；再使用
  [Finite.of_fintype](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/Fintype/EquivFin.lean#L170)、
  [Subtype.finite](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/Fintype/EquivFin.lean#L195)
  与 [Fintype.ofFinite](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/Fintype/EquivFin.lean#L179)
  取得两个候选子类型的有限结构。
  [Fintype.card_congr](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/Fintype/Card.lean#L67)
  应用于该子类型等价，提供基数相等。
- [ZMod.isUnit_iff_coprime](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/ZMod/Basic.lean#L809)
  取自然数代表元 \(m\) 和模数 \(n=W\)，提供单位条件与轮筛解释之间的对应。

任意模数的参数化及不依赖枚举，本身不提供新的独立数学内容；候选密度、定向读出和实际素数计数仍是不同对象。

\(W=30\) 的原点前缀数值和 \(W=210\) 的三点跨度数值来自 Foundational Formulas
§16；§27 解释含重复素因子模数上的轮商。它们在这里是有限数学见证，不能据此宣称
实际素数三胞胎无穷，也不能将未形式化的读出称作内核已核验结论。

层间接口须保留以下对象与对应条件：

- 有序间隙和归一化手性 \(\chi\)，以及反射翻转 \(\chi\) 的对应；
- 有限轮候选、二点相关、三点相关和固定原点前缀，并明确各自的观察商；
- \(W=6\) 的首次原点前缀分离、\(W=30\) 的后续原点见证，以及
  \(W=210\) 的首次平移不变三点分离，各自与 LayeredCapture 接口的相容性；
- 三点方向坐标进入 AURIC 的 \(\kappa\)-fiber 所需的同源编码假设。

实际 \(T_H(x)\) 仍是独立的算术输入。给有限轮轨迹附加经验素数观测，不会把候选密度
转换为实际 prime-triplet count，也不会把有限样本转换为普遍素数分布定理。

### 11.2.7. 原点前缀与平移不变三点相关的不同捕获层

前面的 \(K_3\) 必须带上观测商。令

\[
a_{H,W}(r)=
\mathbf 1\{\gcd(r+h,W)=1\text{ 对所有 }h\in H\},
\]

并定义平移不变二点和三点读出：

\[
O_2(H,W)=\bigl(C_{H,W}(s)\bigr)_s,
\qquad
O_3(H,W)=\bigl(C^{(3)}_{H,W}(s,t)\bigr)_{s,t}.
\]

另定义固定原点的前缀读出。取 \(b\in\mathbb N\)，在整数位置上周期延拓轮指示函数：

\[
P_{H,W}(b)=\sum_{1\le r\le b}a_{H,W}(r\bmod W),\qquad
O_{\mathrm{origin}}(H,W)=\bigl(P_{H,W}(b)\bigr)_{b\in\mathbb N}.
\]

此定义允许 \(b\ge W\)，完整周期按次数计入。原点前缀是保留位置标签的一阶轮指示读出，
不是平移不变三点相关；\(K_3\) 的下标在此标记三点模板，而不表示前缀仪器的关联阶数。

基线理论卷第十六节和第二十七节已经给出以下严格桥接。反射

\[
a_{H_-,W}(r)=a_{H_+,W}(-r-6)
\]

使两个轮的二点自相关、循环 Gram 和全部二阶谱矩相同。对于平移不变三点读出，存在平移 \(a\) 使

\[
a_{H_-,W}(r)=a_{H_+,W}(r+a)
\]

当且仅当 \(W\) 的所有素因子都属于 \(\{2,3,5\}\)。因此沿前素数轮链

\[
W_1=2,\qquad W_2=6,\qquad W_3=30,\qquad W_4=210,
\]

有

\[
K_3^{\mathrm{TI}}=4.
\]

这里的新增素数是 \(7\)。它第一次破坏两个三胞胎轮之间的循环平移等价。

固定原点的前缀读出首次在第二层分离。第一层 \(W_1=2\) 时，
\[
C_1(H_+)=C_1(H_-)=\{1\},
\]
因为两个模板的所有偏移都为偶数。因此两个周期指示函数逐点相同，所有
\(b\in\mathbb N\) 的前缀均相等；没有更早的正轮层能够分离。
第二层 \(W_2=6\) 时，奇数条件加上模三的条件分别给
\[
C_2(H_+)=\{5\},\qquad C_2(H_-)=\{1\}.
\]
取 \(b=1<6\)，有
\[
P_{H_+,6}(1)=0,\qquad P_{H_-,6}(1)=1.
\]
两份单点集合的平移不变二点相关却同为
\[
C_{H_+,6}(s)=C_{H_-,6}(s)=
\begin{cases}1,&s\equiv0\pmod6,\\0,&s\not\equiv0\pmod6.\end{cases}
\]
第一层的二点相关也由同一单点公式给出，模数换为二。故上述首捕获定义给
\[
K_3^{\mathrm{origin}}=2.
\]

即使只固定 \(b=10\)，在允许重复周期的前缀定义下，\(1\le r\le10\) 内模六的合法正整数分别为
\(\{5\}\) 和 \(\{1,7\}\)，所以
\[
P_{H_+,6}(10)=1,\qquad P_{H_-,6}(10)=2.
\]
第一层在同一前缀的读数均为五，故这一固定前缀仪器的首分离层同样为二。
保留模三十的有效见证：
\[
C_3(H_+)=\{11,17\},\qquad C_3(H_-)=\{7,13\},
\]
\[
P_{H_+,30}(10)=0,\qquad P_{H_-,30}(10)=1.
\]
它是后续层的分离，不能单独证明首次分离发生于第三层。

这与 \(K_3^{\mathrm{TI}}=4\) 使用不同的仪器。第一、二层的两个轮都是循环单点，
第三层的两个集合相差平移 \(-4\pmod{30}\)，所以这三层的任意阶平移不变相关都相同。
第四层的三点相关由 Foundational Formulas §16.5 的同标签见证分离：
\[
C^{(3)}_{H_+,210}(6,30)=1,\qquad
C^{(3)}_{H_-,210}(6,30)=0.
\]
原点前缀保留绝对位置；平移不变三点相关忘掉绝对位置，保留关系结构。
两者的首捕获层分别为二和四，不能互换。

#### 11.2.7.1. 二维观测晶格：素数层与读出阶数

把“第几层”和“看几阶关联”分成两个坐标。令 \(j\) 表示素数轮层，
\(k\in\{1,2,3,\ldots\}\) 表示读出阶数，定义观察等价关系
\[
x\sim_{j,k}y
\quad\Longleftrightarrow\quad
O_{j,k}(x)=O_{j,k}(y).
\]
于是每个状态不再只带一个层号，而带一个二维索引
\[
\Gamma_{j,k}=[x]_{\sim_{j,k}},
\qquad
(j,k)\in\mathbb N\times\mathbb N_{\ge1}.
\]
沿 \(j\) 方向新增素数约束，沿 \(k\) 方向增加联合观测阶数；两种推进
都可能减少 kernel，但减少的对象不同。

对本节的三胞胎模板：

- \(k=2\) 的 pair-correlation 和全部 pair-Gram 谱矩在反射取向之间保持
  相同，因此沿 \(j\) 增长也不会自动恢复三点方向；
- \(k=3\) 的平移不变三点相关在 \(W_1,W_2,W_3\) 相同，首次分离在 \(W_4=210\)；
- 另一个保留原点及位置标签的前缀仪器在 \(W_2=6\) 首次分离，
  \(W_3=30,b=10\) 只是其后续见证，不能归作平移不变三阶读出；
- \(k=1\) 若只取平移不变的候选密度，在所有轮层保持相同，因而只记录 arithmetic cost，
  不记录手性；保留位置标签的一阶前缀则具有前述不同的分离能力。

因此三维金字塔 \((X,Y,Z)\) 与二维观测晶格并不是两个互斥空间。完整层状态
应写成
\[
\Gamma_{j,k}
=
(K_{j,k},X_{j,k},Y_{j,k},Z_{j,k},
\kappa_{j,k},\chi_{j,k},\bar\varepsilon_{j,k}).
\]
其中 \((X_{j,k},Y_{j,k},Z_{j,k})\) 给出金字塔商空间位置，\(\kappa\) 是隐藏 fiber，\(\chi\) 是
三点方向，\(\bar\varepsilon\) 是含空轮吸收分支的扩展排斥坐标。沿 \(j\) 的跳跃是离散算术更新，沿
\(k\) 的跳跃是观测分辨率更新；若再加入质量作用流，才得到每个格点内部的
连续时间轨迹。这样“逃逸轨迹”具有几何、观测和热力学三重索引，而不是把
素数序列直接当成唯一的三维空间曲线。

### 11.2.8. 三胞胎逃逸的 \(\kappa\)-fiber 数值证书

基线理论卷第十五节把局部除数事件直接接到金字塔纤维。对奇素数 \(q\)，在 \(\mathbb F_q\) 上取除数指示源。对 \(H_+\) 与 \(H_-\)，都有

\[
X=Y=Z=\frac1q,
\]

并且端点联合坐标满足

\[
\kappa=
\begin{cases}
1/3,&q=3,\\
0,&q>3.
\end{cases}
\]

更强的隐藏纤维证书来自

\[
H_C=\{0,2,4\}
\]

在 \(q=3\) 时的比较。\(H_A=\{0,2,6\}\) 与 \(H_C\) 具有相同的三均值

\[
(X,Y,Z)=\left(\frac13,\frac13,\frac13\right),
\]

但

\[
(\kappa,p_0)_{H_A}
=
\left(\frac13,\frac13\right),
\qquad
(\kappa,p_0)_{H_C}
=
(0,0).
\]

因此三维金字塔位置不变，联合概率沿 \(\kappa\) 纤维跳变。

同一有限证书还可以由归一化三向量 Gram 读出。令

\[
U_c=
\begin{pmatrix}
1&c&0\\
c&1&0\\
0&0&1
\end{pmatrix},
\qquad
c=\frac{\kappa}{\sqrt{XY}}.
\]

则

\[
\operatorname{Spec}(U_c)=\{1-c,1,1+c\},
\]

并且

\[
D_\Psi(U_c)
=
\frac{2\kappa^2}{XY}.
\]

在 \(q=3\) 的两份来源律上，该谱读出分别为 \(2\) 和 \(0\)。这给出了一个完全有限、可计算的隐藏纤维逃逸证书，不需要使用任何关于素数三胞胎无穷性的猜想。

\(q=3\) 与 \(W_4=210\) 的作用不同。前者是联合概率 fiber seam，后者是三点方向的循环平移 seam。两者可以出现在同一套层状态中，但不能合并成一个标量。

### 11.2.9. 仅提高 pair Gram 谱阶数无法恢复三点方向

[Foundational Formulas §16.6](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md) 给出模 \(7\) 的明确边界。取两个三点禁集 \(D_+=\{0,1,5\}\)、\(D_-=\{0,1,3\}\)，其**合法补集** \(D_+^c,D_-^c\) 的循环 Gram 都是

\[
G=2I_7+2J_7,
\]

因此

\[
\operatorname{Spec}(G)=\{16,2,2,2,2,2,2\},
\]

禁点集本身的循环 Gram 则为 \(2I_7+J_7\)，谱为 \(\{9,2,2,2,2,2,2\}\)。这是因为禁点集的自相关在零位移为三、非零位移为一；补集的对应值为四和二。这里 \(J_7\) 为全一矩阵，常数方向的特征值为七，零和子空间的特征值为零。

对每个相同载体上的两个取向，Gram 逐项相等，因而对所有 \(m\ge1\)：

\[
\operatorname{tr}(G_+^m)
=
\operatorname{tr}(G_-^m).
\]

上述模七矩阵是局部载体。另在 \(W=210\) 的同一轮筛载体上，§11.2.7 的两个 pair Gram 也逐项相等，而带相同位移标签 \((6,30)\) 的三点相关为一和零。因此无需把模七矩阵与模二百一十矩阵认作同一个矩阵，就得到观测层级结论：

\[
\text{所有 pair Gram 谱矩}
\;\not\Rightarrow\;
\text{三点算术方向}.
\]

pair Gram 的矩阵指标与算术三点相关的位置标签是不同的读出；前者的全部谱矩不能反推出三胞胎方向。§11.2.8 的 \(q=3\) 联合概率纤维接缝仍是另一载体上的关系。

### 11.2.10. 数学来源与适用边界

§11.2.6 已给出上游单位取负、反射等价和有限基数供应的完整参数对应。
该应用解释了每个非零模数下两个轮候选集等势，以及为何候选密度不识别方向；
它是既有结果的应用。本文的轮筛读出、首捕获层和 AURIC 隐藏纤维接口尚未取得 Lean 准入或冻结，也未完成内核核验。
理论正文的 \(\chi=(g_2-g_1)/2\) 仍是两个直径六模板的定向坐标，
并非由候选基数自动恢复的量。

原点前缀的首捕获层是 \(K_3^{\mathrm{origin}}=2\)，其较早层不分离和模六见证
由 §11.2.7 的逐项推导给出。\(W=30,b=10\) 的原点见证继续成立，
但不承担首次性。平移不变三点仪器仍有 \(K_3^{\mathrm{TI}}=4\)，
\(W=210,(6,30)\) 的见证以及前三层的平移等价分别给出分离和无更早分离。
这些是有限数学推导；
实际 \(T_H(x)\) 的无穷性和全 RH/Robin 目标仍未由它们解决。

对应来源为：

- Foundational Formulas §15 的同源联合概率与纤维坐标；
- Foundational Formulas §16 的二点障碍、三点恢复及 \(W=30,W=210\) 见证，
  以及 §27 的含重复素因子轮商；
- LayeredCapture 的既有首捕获接口，其向本节仪器的形式化接入仍待完成；
- §11.2.6 所列固定修订的 Mathlib 供应。

## 12. 层间兼容条件与开放桥梁

§§1、3 的投影、重构式、合法纤维区间、核方向和 \(\Delta\) 描述固定均值的状态；凸组合松弛保持同点与非负性，指数质量作用流进一步给出导数和收缩。§9 的径向捕获改变底部质量，保持 \(\alpha,\beta\)，其关联松弛取决于 exposure。这些是不同的状态映射。

候选层间映射须同时携带 LayerChain 的 kernel refinement、capture partition 和 \((r_j,\alpha_j,\beta_j,\eta_j)\)：更新后的坐标须给出合法五态律，且与指定高度更新和观察投影相容。离散 capture 本身不推出物理热层，也不供应这种相容性证明。

§6.3 的整数四格 \(R\mid AB\) 判据、TV 下界与分母障碍，若要接入 Euclid 支撑扩张，仍须给出边际计数和支撑的共同更新。Fibonacci 矩阵幂、projective rank 和 scalar period 的对应则保留自身的有限尺度因子及 \(p=2,5\) 边界。把这些算术关系、底面条件独立与互信息、熵导数及对数平均共同接入分层动力学，仍须满足各自的载体、支撑和极限条件。

## 13. Quantum lift：与四大力学统一框架的接口

### 13.1 量子状态的最小提升

定义一个分层 Hilbert 空间

\[
\mathcal H
=
\mathbb C\lvert 3\rangle
\oplus
(\mathbb C^2\otimes\mathbb C^2).
\]

第一项是 apex sector，第二项是底部两个 binary 变量的量子 sector。取块对角密度矩阵

\[
\rho
=
(1-r)\lvert3\rangle\langle3\rvert
\oplus
r\sigma,
\]

其中 \(\sigma\) 是两个量子比特上的密度矩阵。对 \(\sigma\) 在计算基下测量或退相干，得到

\[
q=(q_{00},q_{10},q_{01},q_{11}).
\]

然后

\[
\alpha=q_{10}+q_{11},\qquad
\beta=q_{01}+q_{11},\qquad
\eta=q_{11}.
\]

于是经典金字塔状态是量子状态经过以下复合读出后的结果：

\[
\rho
\longmapsto
\text{dephase}(\sigma)
\longmapsto
q
\longmapsto
(\alpha,\beta,\eta)
\longmapsto
(X,Y,Z).
\]

这给出了一个严格的解释：

- \(\eta\) 是量子 sector 在选定测量基下的经典 joint-correlation 坐标；
- \(\kappa=r\eta\) 是加上 apex 权重后的完整概率坐标；
- \((X,Y,Z)\) 是进一步忘掉 joint correlation 后的 marginal readout；
- \(\sigma\) 中的 off-diagonal coherence 和 entanglement 是更高层的隐藏信息，不能被 \(\eta\) 代替。

因此，当前金字塔是量子状态空间经过两次 quotient 后得到的 classical observable sector。

### 13.2 四大力学的共同生成元结构

对同一个状态变量 \(x\)，考虑四类候选生成元：

\[
\dot x
=
\underbrace{J(x)\nabla E(x)}_{\text{Hamiltonian / reversible}}
+
\underbrace{M(x)\nabla S(x)}_{\text{thermodynamic / dissipative}}
+
\underbrace{\mathcal L_{\mathrm{readout}}(x)}_{\text{quantum measurement / coarse-graining}}
+
\underbrace{\mathcal L_{\mathrm{field}}(x)}_{\text{electromagnetic or gauge boundary}}.
\]

其中：

- \(J^\mathsf T=-J\) 是辛或 Hamiltonian 结构；
- \(M\succeq0\) 是 Onsager mobility；
- \(\mathcal L_{\mathrm{readout}}\) 的连续量子部分必须是迹湮灭的状态保持生成元；在线性情形，它是算子空间上的生成元，而其演化半群才须完全正、保持迹（CPTP）；CPTP 通道本身用于离散状态更新；
- \(\mathcal L_{\mathrm{field}}\) 负责局部连接、端口和 gauge phase；
- 离散 prime/Fibonacci seam 可作为 \(\mathcal L_{\mathrm{field}}\) 的算术 phase sector，但当前仍是模型接口。

对量子密度态，四项的量子分量都须保持指定载体：导数保持 Hermitian 且迹为零，每项的连续演化保持正性和迹一；线性量子项须生成 CPTP 半群。若限定为 §13.1 的 apex/底面块对角载体，还须保持该块结构。各项之和的流存在并保持同一载体也是此方程的模型条件，不能仅由 \(J^\mathsf T=-J\) 或 \(M\succeq0\) 推出。

在有限维 \(\mathcal H\) 上，给定复线性 CPTP 通道 \(\Phi:\mathcal B(\mathcal H)\to\mathcal B(\mathcal H)\) 和常数 \(\lambda\ge0\)，可把连续读出生成元取为

\[
\mathcal L_{\mathrm{readout}}=\lambda(\Phi-\operatorname{id}),
\qquad
e^{t\mathcal L_{\mathrm{readout}}}
=e^{-\lambda t}\sum_{n=0}^{\infty}\frac{(\lambda t)^n}{n!}\Phi^n
\quad(t\ge0).
\]

右侧在有限维算子范数中收敛，是权重和为一的 CPTP 通道混合，形成 CPTP 半群；若 \(\Phi\) 保持所选块载体，其混合半群也保持该载体。对任意密度态，\(\operatorname{Tr}\mathcal L_{\mathrm{readout}}(\rho)=\lambda(\operatorname{Tr}\Phi(\rho)-\operatorname{Tr}\rho)=0\)。离散读出则写为 \(\rho^+=\Phi(\rho^-)\)，不把 \(\Phi(\rho)\) 直接加到导数中。此构造只给已指定通道的连续/离散接口，不供应整个非线性模型的物理实现；§13.4 的实际酉/pinching 步及其熵公式仍按离散合同使用。

对于量子态，标准可逆部分是

\[
\dot\rho=-i[H,\rho].
\]

耗散部分应写成 Lindblad/GKSL 形式：

\[
\mathcal D(\rho)
=
\sum_\ell
\left(
L_\ell\rho L_\ell^\dagger
-\frac12\{L_\ell^\dagger L_\ell,\rho\}
\right).
\]

因此量子版本的候选方程是

\[
\dot\rho
=
-i[H,\rho]
+
\mathcal D(\rho)
+
\mathcal L_{\mathrm{capture}}(\rho).
\]

### 13.3 当前金字塔对应哪一部分

在底部四格均为正的内部，\(\kappa\) 质量作用流是对角概率 sector 上的确定性 mean-field dissipative closure：

\[
\dot\kappa
=
-\gamma L(a,b)\,\partial_\kappa D.
\]

它不是

\[
\dot\rho=-i[H,\rho]
\]

的直接结果，也不是一个线性 CPTP 通道的完整表达。要把它升级为量子动力学，需要构造一个量子 detailed-balance channel，使其在指定测量基下诱导出相应的 classical transition law，或明确声明它是测量后的 mean-field limit。

对有限维 Hermitian Hamiltonian \(H\)、逆温度 \(\beta_{\rm th}>0\) 和实际匹配的 Gibbs 参考态

\[
\rho_{\beta_{\rm th}}=\frac{e^{-\beta_{\rm th}H}}{\mathcal Z_{\beta_{\rm th}}},\qquad
\mathcal Z_{\beta_{\rm th}}=\operatorname{Tr}e^{-\beta_{\rm th}H},\qquad
F(\rho)=\operatorname{Tr}(H\rho)-\beta_{\rm th}^{-1}S(\rho),
\]

[Gibbs/free-energy 身份式](../../../Blueprint/D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.md) 给出

\[
D(\rho\Vert\rho_{\beta_{\rm th}})
=\beta_{\rm th}\bigl(F(\rho)-F(\rho_{\beta_{\rm th}})\bigr).
\]

这里 \(\beta_{\rm th}\) 与底部边际 \(\beta=Y/r\) 是不同参数。要识别 §9 的 \(D_{\rm h}\)，先固定五个正交扇区投影 \(P_i\)，满足 \(\sum_iP_i=I\)，及读出

\[
\mathcal C(\rho)=(\operatorname{Tr}P_i\rho)_i=p,\qquad
\mathcal P(\rho)=\sum_iP_i\rho P_i.
\]

在 §13.1 的五维载体上，\(P_i\) 是计算基的五个一维投影。对 \(r>0\)，令 \(q\) 为归一化底面条件律，\(\alpha=X/r,\beta=Y/r\)，则 [Foundational Formulas §9.3](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md) 的参考是

\[
q_*=\bigl((1-\alpha)(1-\beta),\alpha(1-\beta),(1-\alpha)\beta,\alpha\beta\bigr),
\]

\[
p_*=(rq_{*,00},rq_{*,10},1-r,rq_{*,01},rq_{*,11}),\qquad
D(p\Vert p_*)=rD(q\Vert q_*)=rI(q)=D_{\rm h}.
\]

要以模型定义的 \(D_{\rm h}\) 作为该粗读出的相对熵，须指定参考态满足 \(\mathcal C(\rho_{\rm ref})=p_*\)。它要求参考的 apex/底面权重同为 \(1-r,r\)，底面参考同为当前边际的乘积律，不能由块对角性决定。

对同一扇区分解下的块对角态

\[
\rho=\bigoplus_i p_i\rho_i,\qquad
\rho_{\rm ref}=\bigoplus_i s_i\tau_i,
\]

在支撑包含 \(\operatorname{supp}\rho\subseteq\operatorname{supp}\rho_{\rm ref}\) 时，按块展开对数得到

\[
D(\rho\Vert\rho_{\rm ref})
=D(p\Vert s)+\sum_{i:p_i>0}p_iD(\rho_i\Vert\tau_i).
\]

因此 \(s=p_*\) 后，完整量子相对熵等于 \(D_{\rm h}\) 还要求每个正权扇区内 \(\rho_i=\tau_i\)；块对角性不会使后一个求和自动为零。五个一维扇区的对角嵌入 \(\rho=\operatorname{diag}(p),\rho_{\rm ref}=\operatorname{diag}(p_*)\) 满足这一条件。若 \(\rho\) 还有跨扇区相干且参考块对角，同一 pinching 分解在支撑包含下还给

\[
D(\rho\Vert\rho_{\rm ref})
=D(\mathcal P\rho\Vert\rho_{\rm ref})+D(\rho\Vert\mathcal P\rho).
\]

这些附加项不能由经典五态读出恢复，也不能将扇区内相关与跨扇区相干混作一个已消失的量。

若进一步要求参考态是 Gibbs 态，必须验证上述扇区权重、条件态与 \(H,\beta_{\rm th},\mathcal Z_{\beta_{\rm th}}\) 的匹配。对五个一维扇区且所有 \(p_{*,i}>0\)，模型上可取 \(E_i=-\beta_{\rm th}^{-1}\ln p_{*,i}+c\)，于是 \(\mathcal Z_{\beta_{\rm th}}=e^{-\beta_{\rm th}c}\)；这只是为指定 \(p_*\) 匹配的参考，不是任意给定物理能量的结论。高维扇区即使能量在扇区内常数，其 Gibbs 权重也为 \(d_i e^{-\beta_{\rm th}E_i}/\mathcal Z_{\beta_{\rm th}}\)，条件态为 \(I_{d_i}/d_i\)，仍须逐项匹配。若 \(p_*\) 有零分量，应在其活动支撑上定义参考，或明确给出极限；有限能量、有限正温的完整五维 Gibbs 态不能有零权重。\(r=0\) 时两份经典律均为 \(\delta_3\)，\(D_{\rm h}=0\)，不定义底面 \(q\)。

**反例命题。** 块对角性和五扇区零能量不足以把完整 Gibbs 相对熵识别为 \(D_{\rm h}\)。

**证明。** 取 \(r=1/2\)、均匀底面 \(q=(1/4,1/4,1/4,1/4)\) 和五个零能量。此时 \(p=p_*=(1/8,1/8,1/2,1/8,1/8)\)，故 \(D_{\rm h}=0\)；零能量 Gibbs 态却为 \(I_5/5\)，对角相对熵展开为

\[
D(\operatorname{diag}(p)\Vert I_5/5)
=\frac12\ln\frac58+\frac12\ln\frac52
=\ln\frac54>0.
\]

∎

一般物理 Gibbs 参考与 \(p_*\) 的匹配，以及非线性流的量子实现，仍是条件接口。

### 13.4 QCA/Dirac 载体的条件接口

QCA/Dirac 模型中的局部有限维 Hilbert 空间、酉局部更新、Lieb–Robinson 型有限传播和 SU(2)/Bloch 内部结构，可作为本框架的 reversible/quantum carrier 候选；若另行指定生成 Hamiltonian 及其连续时间演化，记为：

\[
U_{\mathrm{QCA}}^t
=
e^{-itH_{\mathrm{QCA}}}.
\]

Fibonacci 或黄金 transfer 可以作为离散的 SL\(_2\) sector，量子 phase 则由 Hilbert space 中的 unitary representation 携带。金字塔的 \(\eta\) 流和 radial capture 与该可逆 carrier 的关系是拟议的 coarse-graining/mean-field 接口：只有指定具体 carrier、观测映射，并构造相应通道或推导明确的测量后 mean-field limit，才能将它们识别为该 carrier 的不可逆 effective dynamics。§13.3 所述的精确非线性质量作用流实现仍待完成。

这提出了一个仍需上述桥接的候选分层结构：

\[
\text{QCA/Dirac unitary carrier}
\longrightarrow
\text{measurement and marginal quotient}
\longrightarrow
\text{pyramid }(r,\alpha,\beta,\eta)
\longrightarrow
\text{KL/Onsager dissipation}.
\]

[EntropyProductionCoherenceDeletionIdentity](../../../Blueprint/D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.md) 的熵产身份式要求有限维密度态、实际给定的酉 \(U\)，以及每步关系 \(\rho_{k+1}=\operatorname{pinch}(U\rho_kU^\dagger)\)；它本身不提供上述非线性流的通道或极限推导。Boundary Calculus §§13.4–13.6 的相干递归还要求共同输出载体、跨历史相位和满足 \(\sum_aK_{a|h}^\dagger K_{a|h}=I\) 的算子，并保留以后可能重接的实际环境、控制和记忆。重复使用同一环境与每步使用新环境是不同的更新，不能仅由经典边际或通道名称确定这条桥接。

候选运动学关系

\[
v_{\mathrm{ext}}^2+v_{\mathrm{int}}^2=c^2
\]

可以继续作为 QCA 内部几何的模型级约束，但不能直接把 \(r\) 识别成 proper time，也不能把 Fisher metric 识别成 Minkowski metric。当前 \(r\) 是概率层级或底部质量坐标，proper time 需要额外定义的时钟和因果结构。

### 13.5 电磁/规范接口与限制

若把第四个方向理解为电磁或 gauge structure，最自然的接口是：

- \(H_\alpha,H_\beta\) 提供宏观层运动的水平连接；
- Fibonacci scalar phase 提供离散 holonomy-like phase；
- prime seam 提供离散 arithmetic chart transition；
- boundary/readout map 提供端口和观测接口。

这还没有产生 Maxwell 方程、U(1) curvature 或真实电磁场。要完成电磁连接，需要在层状态上定义 gauge group action、link variable、field strength 和 gauge-invariant cost，并证明其与 kernel refinement 及 radial transport 的兼容性。

上述四类接口的条件分别为：

| 方向 | 模型对象 | 所需桥梁与适用边界 |
|---|---|---|
| 动力学 | QCA/SL\(_2\) reversible transfer、候选 Hamiltonian flow | 与各 seam 的共同状态映射仍待构造 |
| 量子力学 | \(\rho\)、unitary、pinching、CPTP/GKSL | 指定载体、读出和通道；金字塔是 classical readout sector |
| 热力学 | \(D_{\mathrm h}\)、Onsager mobility、free-energy decrease | 内部 κ-flow；Gibbs 识别要求匹配参考；环境热须另供协议 |
| 电磁/规范 | horizontal connection、phase、boundary port | 仍是待构造的 field extension |
