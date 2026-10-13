> **Mathematical scope.** This volume concerns finite five-state probability, observation fibers, graph geometry, and conditional arithmetic, triangle-network, and RH bridges.
> Its mathematical source is commit `a2f195ceb64aaaea7eeb8a6bdea479ca2c3c7430`; individual source attributions and applicability limits accompany the corresponding statements.
> Bridge data and hypotheses do not by themselves establish their existence or identify finite models with physical fields or zeta zeros.
>
> **Navigation.** This volume contains the original title and sections 0–26.
> Sections 27–48 continue in [the first continuation](AURIC_FIB_ATOM_TYPED_BRIDGES_AND_ARITHMETIC_TRIANGLE_RH_PIPELINE_CONTINUATION.md).
> The source heading `后续严格补充` and sections 49–65 continue in [the second continuation](AURIC_FIB_ATOM_TYPED_BRIDGES_AND_ARITHMETIC_TRIANGLE_RH_PIPELINE_CONTINUATION_II.md).
> Sections 12–14 give the five-state and finite-triangle contracts as mathematical definitions and propositions; Proposition 14.6 refutes the unconditional probability implication and states the corrected pushforward conditional.

# Auric FIB ATOM：类型化桥接、算术驱动、三角网络与 RH 管线

## 0. 目的与证据边界

本卷把五个已经分别出现的对象放入同一个类型化管线：

1. 五态 FIB 概率律；
2. 固定一阶读出的 \(\kappa\)-纤维；
3. Fisher 信息几何与读出收缩；
4. Fibonacci 支持图的动态边界与环流；
5. 算术驱动、triangle-local 提升以及 RH-Cayley 单元。

本文只使用显式定义的映射和概率核。没有定义的映射不被视为存在。特别是，素数分类到五态模式的编码、FIB 到三个独立源的提升、FIB 缺陷到 zeta 零点的映射，均在本文中作为尚缺具体构造的桥接条件，而不是已经证明的等价。

基础公式、隐藏关系、局部读出几何和静态 seam 的既有结果分别见：

- AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md
- AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md
- AURIC_FIB_ATOM_LOCAL_SOURCE_SPLITTING_AND_READOUT_GEOMETRY.md
- AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md

---

## 1. 原生五态载体

### 定义 1.1（五态空间）

令

\[
\Sigma=\{0,2,3,5,25\}.
\]

状态函数 \(x,y,z:\Sigma\to\{0,1\}\) 由表确定：

\[
\begin{array}{c|ccccc}
s&0&2&3&5&25\\ \hline
x(s)&0&1&0&0&1\\
y(s)&0&0&0&1&1\\
z(s)&0&0&1&0&0
\end{array}
\]

于是

\[
x^2=x,\quad y^2=y,\quad z^2=z,\quad xz=yz=0,\quad xy=\mathbf 1_{\{25\}}.
\]

这里 \(25\) 是联合状态 \([2,5]\)，其原生加性数量为 \(2+5=7\)。

令

\[
\Delta(\Sigma)=
\left\{
p\in\mathbb R^\Sigma:
p_s\ge0,\ \sum_s p_s=1
\right\}.
\]

定义

\[
X=\mathbb E_p[x],\qquad
Y=\mathbb E_p[y],\qquad
Z=\mathbb E_p[z],\qquad
\kappa=\mathbb E_p[xy]=p_{25},
\]

并令 \(r=1-Z\)。

### 定理 1.2（完整重构）

对任意 \(p\in\Delta(\Sigma)\)，有唯一表达

\[
\begin{aligned}
p_0&=r-X-Y+\kappa,\\
p_2&=X-\kappa,\\
p_3&=Z,\\
p_5&=Y-\kappa,\\
p_{25}&=\kappa.
\end{aligned}
\]

证明：由 \(X=p_2+p_{25}\)、\(Y=p_5+p_{25}\)、\(Z=p_3\)、\(\kappa=p_{25}\) 直接得到前四式，最后用归一化得到 \(p_0\)。证毕。

### 定理 1.3（金字塔像与合法纤维）

可见映射

\[
P(p)=(X,Y,Z)
\]

的像为

\[
\mathcal P=
\{(X,Y,Z):X,Y,Z\ge0,\ X+Z\le1,\ Y+Z\le1\}.
\]

固定 \((X,Y,Z)\) 后，合法概率律构成闭区间

\[
\mathcal F_{X,Y,Z}
=
\{p_\kappa:\kappa_-\le\kappa\le\kappa_+\},
\]

其中

\[
\kappa_-=\max(0,X+Y-r),\qquad
\kappa_+=\min(X,Y).
\]

证明：四个底面质量非负分别给出

\[
\kappa\ge0,\quad
\kappa\le X,\quad
\kappa\le Y,\quad
\kappa\ge X+Y-r.
\]

这些条件合并成上述区间。反向地，区间中每个 \(\kappa\) 代入重构式都给出非负、归一化概率律。证毕。

定义

\[
d=(1,-1,0,-1,1).
\]

则

\[
p_\kappa-p_{\kappa'}=(\kappa-\kappa')d,
\]

且在质量零空间 \(T=\{v:\sum_s v_s=0\}\) 上

\[
\ker(DP)=\mathbb R d.
\]

这证明了三维金字塔丢失的概率方向恰为一维。

---

## 2. 事件代数闭包与隐藏四角差

### 定义 2.1（一阶代数与完整代数）

令

\[
\mathcal A_1=\operatorname{span}\{1,x,y,z\},
\]

\[
\mathcal A_2=\operatorname{span}\{1,x,y,z,xy\}.
\]

由于五个状态的评价向量彼此可区分，有代数同构

\[
\mathbb R[x,y,z]/(x^2-x,\ y^2-y,\ z^2-z,\ xz,\ yz)
\cong\mathbb R^\Sigma.
\]

### 定理 2.2（唯一函数展开）

任意 \(f:\Sigma\to\mathbb R\) 唯一写成

\[
f=f_0+(f_2-f_0)x+(f_5-f_0)y+(f_3-f_0)z+J_fxy,
\]

其中

\[
J_f=f_{25}-f_2-f_5+f_0.
\]

并且

\[
\mathbb E_p[f]
=
f_0+(f_2-f_0)X+(f_5-f_0)Y+(f_3-f_0)Z+J_f\kappa.
\]

证明：在状态 \(0,2,5,3\) 逐个代入确定前四个系数，再在状态 \(25\) 代入确定 \(J_f\)。取期望得到第二式。证毕。

### 推论 2.3（一阶充分性判据）

对于整个金字塔的全部概率律，\(\mathbb E_p[f]\) 由 \((X,Y,Z)\) 唯一决定，当且仅当

\[
J_f=0.
\]

因此 \(\kappa\) 是一阶观察代数 \(\mathcal A_1\) 的乘法闭包缺口。

### 定理 2.4（乘积产生隐藏项）

若

\[
f=f_0+a_xx+a_yy+a_zz,\qquad
g=g_0+b_xx+b_yy+b_zz,
\]

则

\[
J_{fg}=a_xb_y+a_yb_x.
\]

证明：只有 \(a_xx\cdot b_yy\) 与 \(a_yy\cdot b_xx\) 产生 \(xy\)，其余交叉项因 \(xz=yz=0\) 消失。证毕。

---

## 3. 二阶矩桥与 \(\kappa\) 恢复

### 定义 3.1（原生数值读出）

令

\[
W=2x+3z+5y.
\]

其五态值为

\[
(0,2,3,5,7).
\]

### 定理 3.2（线性盲性与二阶恢复）

有

\[
\mathbb E[W]=2X+3Z+5Y,
\]

而

\[
W^2=4x+9z+25y+20xy.
\]

因此

\[
\mathbb E[W^2]=4X+9Z+25Y+20\kappa,
\]

从而

\[
\kappa=
\frac{
\operatorname{Var}(W)
+(2X+3Z+5Y)^2
-4X-9Z-25Y
}{20}.
\]

证明：使用幂等关系 \(x^2=x,y^2=y,z^2=z\) 和排斥关系 \(xz=yz=0\) 展开 \(W^2\)。然后使用 \(\operatorname{Var}(W)=\mathbb E[W^2]-(\mathbb E[W])^2\) 解出 \(\kappa\)。证毕。

---

## 4. 条件独立、熵截面与 Fisher 几何

### 定义 4.1（独立性缺陷）

令

\[
\Delta=r\kappa-XY.
\]

则

\[
p_0p_{25}-p_2p_5=\Delta.
\]

若 \(r>0\)，则

\[
\operatorname{Cov}(x,y\mid z=0)=\frac{\Delta}{r^2}.
\]

因此

\[
\Delta=0
\]

等价于底面条件独立。

### 定理 4.2（最大熵截面）

设

\[
\kappa_*=\frac{XY}{r}.
\]

则 \(\kappa_*\) 是固定 \((X,Y,Z)\) 下唯一最大化 Shannon 熵的点，也是唯一满足 \(\Delta=0\) 的点。

证明：沿纤维定义

\[
\vartheta=\log\frac{p_0p_{25}}{p_2p_5},
\qquad
H=-\sum_s p_s\log p_s.
\]

由于

\[
p_0'=p_{25}'=1,\qquad p_2'=p_5'=-1,
\]

得到

\[
\vartheta'
=
\frac1{p_0}+\frac1{p_2}+\frac1{p_5}+\frac1{p_{25}}>0.
\]

并且

\[
H'=-\vartheta.
\]

所以 \(H\) 严格凹。其唯一临界点满足 \(\vartheta=0\)，即 \(p_0p_{25}=p_2p_5\)。代入重构式后化简为 \(r\kappa=XY\)。证毕。

### 定义 4.3（Fisher 纤维）

在纤维内部定义

\[
\mathcal I(\kappa)
=
\frac1{p_0}
+\frac1{p_2}
+\frac1{p_5}
+\frac1{p_{25}}.
\]

### 定理 4.4（Fisher 线元）

沿 \(\kappa\) 方向，

\[
ds_F^2
=
\sum_s\frac{dp_s^2}{p_s}
=
\mathcal I(\kappa)d\kappa^2.
\]

平方根坐标

\[
a_s=2\sqrt{p_s}
\]

把概率单纯形嵌入半径二的球面，因为

\[
\sum_sa_s^2=4,
\qquad
\sum_sda_s^2=\sum_s\frac{dp_s^2}{p_s}.
\]

证明：直接微分 \(a_s=2\sqrt{p_s}\) 即得。证毕。

---

## 5. 粗粒化读出与信息逃逸

### 定义 5.1（随机读出核）

令 \(W(a\mid s)\) 是有限随机核，满足

\[
W(a\mid s)\ge0,\qquad
\sum_aW(a\mid s)=1.
\]

输出分布为

\[
q_a=\sum_sW(a\mid s)p_s.
\]

沿 \(d\) 的输出导数为

\[
q_a'=\sum_sW(a\mid s)d_s.
\]

### 定理 5.2（Fisher 信息收缩）

定义

\[
\mathcal I_{\mathrm{out}}
=
\sum_{a:q_a>0}\frac{(q_a')^2}{q_a}.
\]

则

\[
\mathcal I_{\mathrm{out}}
\le
\mathcal I.
\]

而且

\[
\mathcal I-\mathcal I_{\mathrm{out}}
=
\mathbb E[\operatorname{Var}(S\mid a)],
\qquad
S(s)=\frac{d_s}{p_s}.
\]

证明：对每个 \(a\) 使用 Cauchy–Schwarz：

\[
\left(\sum_sW(a\mid s)d_s\right)^2
\le
q_a\sum_sW(a\mid s)\frac{d_s^2}{p_s}.
\]

除以 \(q_a\) 并对 \(a\) 求和，利用 \(\sum_aW(a\mid s)=1\)，得到 \(\mathcal I_{\mathrm{out}}\le\mathcal I\)。条件方差分解给出差值公式。证毕。

---

## 6. 状态 seam 与动态环流

### 定义 6.1（五态转移图）

取有向边

\[
e_1:0\to2,\quad
e_2:2\to25,\quad
e_3:25\to5,\quad
e_4:5\to0,\quad
e_5:0\to3.
\]

对边流 \(f=(a,b,c,d,e)\)，定义状态边界

\[
Bf=(-a+d-e,\ a-b,\ e,\ c-d,\ b-c)
\]

以及可见边流读出

\[
Af=(b+e,\ c,\ d+e).
\]

### 定理 6.2（动态短正合列）

令

\[
\mathbf c=(1,1,1,1,0),\qquad
\mathbf d=(1,-1,0,-1,1).
\]

则

\[
\ker B=\mathbb R\mathbf c,
\]

\[
\ker(AB)=\{(a,b,a,b,0):a,b\in\mathbb R\},
\]

并有短正合列

\[
0\longrightarrow\mathbb R\mathbf c
\longrightarrow\ker(AB)
\xrightarrow{B}
\mathbb R\mathbf d
\longrightarrow0.
\]

证明：直接计算 \(Bf\) 和 \(ABf=(a-c,e,b-d)\)。由 \(Bf=0\) 得 \(e=0,a=b=c=d\)，所以 \(\ker B=\mathbb R\mathbf c\)。由 \(ABf=0\) 得 \(c=a,e=0,d=b\)。代入 \(B\) 得 \(B(a,b,a,b,0)=(b-a)\mathbf d\)。证毕。

---

## 7. Fibonacci 支持层级

### 定义 7.1（无相邻支持）

令

\[
\Sigma_n=
\{I\subseteq[n]:i\in I\Rightarrow i+1\notin I\}.
\]

含 \(k\) 个元素的合法支持数为

\[
N_{n,k}=\binom{n-k+1}{k}.
\]

总状态数为

\[
V_n=\sum_kN_{n,k}=F_{n+2}.
\]

### 定理 7.2（静态隐藏维数与动态环流维数）

若 \(A_n\) 记录 \(n\) 个单点边缘，\(T_n\) 是质量零空间，则

\[
h_n=\dim\ker(A_n|_{T_n})=F_{n+2}-n-1.
\]

若 \(\Gamma_n\) 是 Fibonacci cube，\(E_n\) 是其边数，则

\[
c_n=\dim\ker B_n=E_n-V_n+1,
\]

并且

\[
c_n-h_n
=
\sum_{k\ge3}(k-2)N_{n,k}.
\]

因此 \(c_n\ge h_n\)，且 \(n\ge5\) 时严格大于。

证明：\(\Gamma_n\) 连通，因此 \(\operatorname{im}B_n=T_n\)。单点状态与空状态的差向量证明 \(A_n|_{T_n}\) 的秩为 \(n\)，由秩零度定理得到 \(h_n\)。图的循环空间维数为 \(E_n-V_n+1\)，代入支持计数并整理得到差值公式。证毕。

---

## 8. 算术驱动桥

### 定义 8.1（算术编码桥）

令 \(\mathcal C\) 是算术配置集合，例如素数窗口、模类、素数间距类别、Fibonacci 支持或具有指定禁字条件的整数词。

一个算术到 FIB 的桥必须显式给出

\[
\Phi:\mathcal C\to\Delta(\Sigma_n).
\]

如果算术类别还控制转移，则需要给出

\[
T_\chi:\Delta(\Sigma_n)\to\Delta(\Sigma_n),
\qquad \chi\in\mathcal C.
\]

### 定理 8.2（管线中的纤维识别判据）

设 \(R_\chi\) 是由 \(\Phi\)、\(T_\chi\) 和实际读出组成的线性全记录映射。对同一可见纤维中的 \(p_\kappa,p_{\kappa'}\)，有

\[
R_\chi(p_\kappa)-R_\chi(p_{\kappa'})
=
(\kappa-\kappa')R_\chi(d).
\]

若纤维非退化，则完整精确记录能够识别 \(\kappa\)，当且仅当存在 \(\chi\) 使

\[
R_\chi(d)\neq0.
\]

证明：由 \(p_\kappa-p_{\kappa'}=(\kappa-\kappa')d\) 以及 \(R_\chi\) 的线性性直接得到。证毕。

素数分类因此应作为驱动输入 \(\chi\)，而不是直接等同于五个概率模式。要得到算术结论，必须构造 \(\Phi\) 或 \(T_\chi\)，并证明它保持支持、正性和闭环结构。

---

## 9. Triangle-local 桥

### 定义 9.1（三角网络源结构）

三角网络的独立源结构为

\[
\mu_{\alpha\beta\gamma}
=
\mu_\alpha\otimes\mu_\beta\otimes\mu_\gamma.
\]

局部响应为

\[
A(a\mid\beta,\gamma),\quad
B(b\mid\gamma,\alpha),\quad
C(c\mid\alpha,\beta).
\]

输出分布为

\[
P(a,b,c)
=
\int A(a\mid\beta,\gamma)
B(b\mid\gamma,\alpha)
C(c\mid\alpha,\beta)
\,d\mu_\alpha d\mu_\beta d\mu_\gamma.
\]

### 命题 9.2（FIB 是局部边缘层）

若存在有限事件分区，把局部响应推前到五态集合 \(\Sigma\)，则得到 FIB 概率律 \(p\)，并可以定义 \((X,Y,Z,\kappa)\)。这个推前是 triangle-local 模型的必要局部边缘。反向地，任意合法五态 \(p\) 只给出局部有限概率律，并不自动给出三个独立源的分解。

因此，全局三角局部性仍需要独立源提升、inflation 或精确算术证书。

---

## 10. RH-Cayley 桥的类型边界

### 定义 10.1（Cayley 缺陷）

对 zeta 非平凡零点 \(\rho\)，定义

\[
c(\rho)=\frac{\rho-1}{\rho}.
\]

则

\[
|c(\rho)|^2-1
=
\frac{1-2\operatorname{Re}\rho}{|\rho|^2}.
\]

在穷尽零点数据的条件下，RH 等价于所有 Cayley 系数模长为一，也等价于相应对角算子酉。

### 定义 10.2（FIB 到 RH 的必要桥）

若要定义 FIB 到 RH 的桥，至少需要给出：

1. 一个零点数据空间 \(\mathcal Z\)；
2. 一个从 FIB 路径、缺陷或闭环到 \(\mathcal Z\) 的映射；
3. 一个保持缺陷的关系，例如
   \[
   \Delta_{\mathrm{FIB}}
   \longmapsto
   1-2\operatorname{Re}\rho;
   \]
4. 一个证明，说明 FIB 的闭环条件等价于 Cayley 算子的等距或酉条件。

Cayley 单元的数学关系见定义 10.1 和第 17.4.3 节所引来源；上述 FIB 到零点空间的映射仍未给定。因此，$\Delta=0$ 与 RH 的临界线条件仍是结构类比。

---

## 11. 数学对象与依赖条件

下列名称对应本卷的数学对象与命题，按依赖顺序排列：

1. FiveModeLaw：五态概率律；
2. VisibleCoordinates：\(X,Y,Z\)；
3. FiberCoordinate：\(\kappa\)；
4. FiberReconstruction：四个重构公式；
5. FourCornerDefect：\(J_f\)；
6. SecondMomentRecovery：由 \(W,W^2\) 恢复 \(\kappa\)；
7. ConditionalIndependenceDefect：\(\Delta\)；
8. MaximumEntropySection：\(\kappa_*=XY/(1-Z)\)；
9. FisherFiberMetric：\(ds_F^2=\mathcal I\,d\kappa^2\)；
10. ReadoutFisherContraction；
11. StateEdgeShortExactSequence；
12. FibonacciHiddenDimension；
13. ArithmeticEncodingBridge；
14. TriangleLocalPushforward；
15. RHBridgeAxiom。

前十二项属于有限维代数、凸几何、信息几何和图论，适用条件见各对应条目。第十三至十五项是桥接条件；相关结论仍依赖尚未给出的具体构造。


---

## 12. 五态代数与条件桥接

### 定义 12.1（五态实函数与概率条件）

沿用定义 1.1 的有序五态集合 $\Sigma=(0,2,3,5,25)$，令 $\mathcal L=\mathbb R^\Sigma$。五态两两可判别且可穷举；$p\in\mathcal L$ 只表示实函数，概率条件另为

$$
\operatorname{Prob}(p)\ \Longleftrightarrow\
(\forall s\in\Sigma,\ p_s\ge0)\ \land\ \sum_{s\in\Sigma}p_s=1.
$$

令 $x=\mathbf1_{\{2,25\}}$、$y=\mathbf1_{\{5,25\}}$、$z=\mathbf1_{\{3\}}$，并对所有 $p\in\mathcal L$ 定义

$$
V(p)=(X(p),Y(p),Z(p))
=\left(\sum_s p_sx(s),\sum_s p_sy(s),\sum_s p_sz(s)\right),
\qquad \kappa(p)=p_{25},\qquad d=(1,-1,0,-1,1).
$$

### 定义 12.2（重构与可见纤维）

对任意 $X,Y,Z,\kappa\in\mathbb R$，按上述状态顺序定义

$$
R(X,Y,Z,\kappa)=(1-X-Y-Z+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
\qquad
\mathcal F_{X,Y,Z}=\{p\in\mathcal L:\operatorname{Prob}(p),\ V(p)=(X,Y,Z)\}.
$$

### 命题 12.3（合法重构的充分条件）

对任意实数 $X,Y,Z,\kappa$，若 $X,Y,Z\ge0$、$X+Z\le1$、$Y+Z\le1$ 且

$$
\max(0,X+Y-(1-Z))\le\kappa\le\min(X,Y),
$$

则 $\operatorname{Prob}(R(X,Y,Z,\kappa))$ 成立。

证明：上述界逐项保证五个质量非负；五项之和为 $1$，即定理 1.3 的反向构造。证毕。

### 命题 12.4（概率律的纤维等价）

对任意 $X,Y,Z\in\mathbb R$ 及满足 $\operatorname{Prob}(p)$ 的 $p\in\mathcal L$，

$$
p\in\mathcal F_{X,Y,Z}
\ \Longleftrightarrow\
\exists\kappa\in\mathbb R,\ p=R(X,Y,Z,\kappa).
$$

证明：正向取 $\kappa=p_{25}$，用定理 1.2。反向将重构式代入 $V$ 得 $(X,Y,Z)$，再用已假定的 $\operatorname{Prob}(p)$。右侧未另加 $\kappa$ 的区间假设；其合法界已由 $p$ 的非负性推出。证毕。

### 定义 12.5（四角差）

对任意 $f:\Sigma\to\mathbb R$，令 $J_f=f_{25}-f_2-f_5+f_0$。

### 命题 12.6（期望分解）

对每个满足 $\operatorname{Prob}(p)$ 的 $p\in\mathcal L$ 和每个 $f:\Sigma\to\mathbb R$，

$$
\sum_s p_sf_s=f_0+(f_2-f_0)X(p)+(f_5-f_0)Y(p)+(f_3-f_0)Z(p)+J_f\kappa(p).
$$

证明：定理 2.2 的唯一函数展开乘以 $p_s$ 后求和，常数项使用 $\sum_s p_s=1$。证毕。

### 定义 12.7（数值读出）

令 $W:\Sigma\to\mathbb R$ 的五态值为 $(0,2,3,5,7)$，即 $W=2x+3z+5y$；状态 $25$ 的值为 $7$。

### 命题 12.8（二阶矩恢复）

对任意满足 $\operatorname{Prob}(p)$ 的 $p\in\mathcal L$，记 $(X,Y,Z)=V(p)$，则

$$
\kappa(p)=\frac{\sum_s p_sW(s)^2-\left(\sum_s p_sW(s)\right)^2
+(2X+3Z+5Y)^2-4X-9Z-25Y}{20}.
$$

证明：由定理 3.2，$W^2=4x+9z+25y+20xy$、$\sum_s p_sW(s)=2X+3Z+5Y$、$\sum_s p_sW(s)^2=4X+9Z+25Y+20\kappa(p)$。代入即得；分子前两项正是方差。证毕。

### 定义 12.9（行列式缺陷）

对任意 $p\in\mathcal L$，令 $\Delta(p)=(1-Z(p))\kappa(p)-X(p)Y(p)$。

### 命题 12.10（缺陷恒等式）

对任意满足 $\operatorname{Prob}(p)$ 的 $p\in\mathcal L$，有 $p_0p_{25}-p_2p_5=\Delta(p)$。

证明：用定理 1.2 写成 $(1-X-Y-Z+\kappa)\kappa-(X-\kappa)(Y-\kappa)=(1-Z)\kappa-XY$，与定义 4.1 一致。此恒等式不要求 $1-Z>0$；条件独立的解释仍受第 4 节的条件限制。证毕。

### 定义 12.11（算术桥接数据）

对任意输入集合 $C$，一组算术桥接数据由映射 $e:C\to\mathcal L$、条件 $\forall c\in C,\operatorname{Prob}(e(c))$ 及由 $C$ 索引的类型族 $(D_c)_{c\in C}$ 组成。这里的驱动数据是类型族，未指定其元素、数值或与 $e$ 的关系。素数窗口、模类或 Fibonacci 支持只有在给定这样的 $e$ 后才成为概率律的输入。

### 定义 12.12（一般三角桥接数据及其边界）

对任意三个源集合 $\Lambda_\alpha,\Lambda_\beta,\Lambda_\gamma$，记 $\mathsf M(\Lambda)$ 为相应测度空间，$\mathbb B=\{0,1\}$。一般三角桥接数据仅由下列三个对象组成：

$$
\begin{aligned}
S&:\mathsf M(\Lambda_\alpha)\to\mathsf M(\Lambda_\beta)\to\mathsf M(\Lambda_\gamma)
\to\mathsf M(\Lambda_\alpha\times\Lambda_\beta\times\Lambda_\gamma),\\
H&:\Lambda_\beta\times\Lambda_\gamma\to\mathsf M(\mathbb B),\\
L&\subseteq\mathcal L.
\end{aligned}
$$

$L$ 表示关于五态实函数的谓词。这些数据没有附加 $S(\mu_\alpha)(\mu_\beta)(\mu_\gamma)=\mu_\alpha\otimes\mu_\beta\otimes\mu_\gamma$、$H$ 为概率核或 $L$ 与 $S,H$ 相容的条件。测度记号所需的可测结构也须给定，仅三个源集合并未指定它们。因而不能仅据此推出第 9 节的独立源分解或某个律属于 $L$；其有限概率版本见第 14 节。

### 定义 12.13（RH 缺陷传送数据）

对任意输入集合 $C$，此类数据包括一个集合 $\mathcal Z$、映射 $m:C\to\mathcal Z$、函数 $\delta_F:C\to\mathbb R$ 和 $\delta_C:\mathcal Z\to\mathbb R$，以及条件

$$
\forall c\in C,\qquad \delta_F(c)=\delta_C(m(c)).
$$

该条件只规定给定数据的缺陷传送；$\mathcal Z$ 尚未被识别为 zeta 零点空间，$\delta_F,\delta_C$ 也尚未被识别为实际的 FIB、Cayley 缺陷。第 10 节的对应、穷尽性及等距或酉条件仍须另外证明。定义 12.11–12.13 均不断言所需桥接数据存在。

## 13. 数学依赖顺序

### 定义 13.1（基础对象与外部条件的依赖次序）

本卷相关对象和结论采用下列依赖次序；编号指向相应数学条目：

1. 五态集合的枚举、相等判别和有限求和（定义 1.1、12.1）；
2. 实函数空间、概率条件、可见坐标和纤维坐标（定义 12.1）；
3. 合法重构（命题 12.3）；
4. 概率律的纤维等价（命题 12.4）；
5. 四角差与期望分解（定义 12.5、命题 12.6）；
6. 数值读出与二阶恢复（定义 12.7、命题 12.8）；
7. 行列式缺陷及其恒等式（定义 12.9、命题 12.10）；
8. 正内部条件下的 Fisher 线元（定义 4.3、定理 4.4）；
9. 有限状态边图和短正合列（第 6 节）；
10. 算术编码、三角提升及 RH 缺陷传送的额外数据（第 8–10 节、定义 12.11–12.13 及第 14 节）。

前七项的证明见第 1–4 节及上述对应条目；Fisher 与图论各保留自己的假设。外部桥接数据的存在不作为这些五态代数恒等式的前提，也不由这些恒等式推出。

## 14. 有限三角提升的精确条件

### 定义 14.1（有限分布与局部概率核）

对任意有限集合 $E$，令 $\mathcal D(E)=\mathbb R^E$，并定义

$$
\operatorname{Dist}_E(\mu)\ \Longleftrightarrow\
(\forall a\in E,\ \mu(a)\ge0)\ \land\ \sum_{a\in E}\mu(a)=1.
$$

对任意集合 $\Omega$ 和任意有限输出集合 $O$，局部概率核是函数 $K:\Omega\times O\to\mathbb R$，满足 $\forall\omega\in\Omega\ \forall o\in O,\ K(\omega,o)\ge0$ 及 $\forall\omega\in\Omega,\ \sum_{o\in O}K(\omega,o)=1$。这里不要求 $\Omega$ 有限。

### 定义 14.2（有限独立源三角数据）

给定任意有限集合 $\Lambda_\alpha,\Lambda_\beta,\Lambda_\gamma$，一组数据 $T$ 包括 $\mu_\alpha\in\mathcal D(\Lambda_\alpha)$、$\mu_\beta\in\mathcal D(\Lambda_\beta)$、$\mu_\gamma\in\mathcal D(\Lambda_\gamma)$，分别满足 $\operatorname{Dist}_{\Lambda_\alpha}(\mu_\alpha)$、$\operatorname{Dist}_{\Lambda_\beta}(\mu_\beta)$、$\operatorname{Dist}_{\Lambda_\gamma}(\mu_\gamma)$，以及定义 14.1 的三个二值输出概率核

$$
A:\Lambda_\beta\times\Lambda_\gamma\times\mathbb B\to\mathbb R,\qquad
B:\Lambda_\gamma\times\Lambda_\alpha\times\mathbb B\to\mathbb R,\qquad
C:\Lambda_\alpha\times\Lambda_\beta\times\mathbb B\to\mathbb R.
$$

每个观察者仅依赖所列的两个相邻源；三个源的联合质量是 $\mu_\alpha(\alpha)\mu_\beta(\beta)\mu_\gamma(\gamma)$。这里未额外假定源集合非空；若其中一个为空，对应归一化条件不能成立。

### 定义 14.3（三角输出分布）

对每组定义 14.2 的数据 $T$，定义 $P_T:\mathbb B^3\to\mathbb R$ 为

$$
P_T(a,b,c)=\sum_{\alpha\in\Lambda_\alpha}\sum_{\beta\in\Lambda_\beta}\sum_{\gamma\in\Lambda_\gamma}
\mu_\alpha(\alpha)\mu_\beta(\beta)\mu_\gamma(\gamma)
A(\beta,\gamma,a)B(\gamma,\alpha,b)C(\alpha,\beta,c).
$$

### 命题 14.4（输出的非负性与归一化）

对每组定义 14.2 的数据 $T$，有 $\operatorname{Dist}_{\mathbb B^3}(P_T)$。

证明：每个求和项为非负因子的乘积。交换有限求和并依次使用三个核的归一化，得

$$
\sum_{a,b,c\in\mathbb B}P_T(a,b,c)
=\sum_{\alpha,\beta,\gamma}\mu_\alpha(\alpha)\mu_\beta(\beta)\mu_\gamma(\gamma)
=\left(\sum_\alpha\mu_\alpha(\alpha)\right)\left(\sum_\beta\mu_\beta(\beta)\right)\left(\sum_\gamma\mu_\gamma(\gamma)\right)=1.
$$

证毕。

### 定义 14.5（五态事件推前关系）

对任意上述 $T$ 和任意 $q\in\mathcal L$，称 $q$ 是 $T$ 的五态事件推前，当且仅当

$$
\exists f:\mathbb B^3\to\Sigma,\quad
\forall s\in\Sigma,\qquad q_s=\sum_{(a,b,c)\in\mathbb B^3:\ f(a,b,c)=s}P_T(a,b,c).
$$

这里 $f$ 是整个输出三元组上的任意函数，未要求满射，也未加局部依赖限制；局部邻接条件仅施于 $A,B,C$。这是一条关于给定 $T,q$ 的存在条件，不断言任意合法 $q$ 都有这样的表示。

### 命题 14.6（给定事件推前的概率性）

若 $T$ 满足定义 14.2 且 $q$ 满足定义 14.5 的存在条件，则 $\operatorname{Prob}(q)$，从而可取其 $(X,Y,Z,\kappa)$ 坐标。

证明：各纤维的质量非负，且 $f$ 的五个纤维分割 $\mathbb B^3$，故 $\sum_s q_s=\sum_{a,b,c}P_T(a,b,c)=1$。仅有三角数据而未将 $q$ 约束为其推前，不能推出 $q$ 是概率律；省略这一条件的蕴含式不成立，例如三个源均取单点、三个响应均确定输出 $0$ 而令 $q=0$，则 $\sum_s q_s=0$。这与命题 9.2 的单向边缘结论一致，反向独立源提升仍未得到。证毕。

### 定义 14.7（算术编码与可见驱动）

对任意输入集合 $C$，算术编码数据为 $e:C\to\mathcal L$ 与 $v:C\to\mathbb R^3$，满足 $\forall c\in C,\operatorname{Prob}(e(c))$ 及 $\forall c\in C, V(e(c))=v(c)$。这里 $v$ 是可见驱动，区别于定义 12.11 的类型族 $(D_c)$。素数驱动须给定这样的编码，才能以 $c\mapsto e(c)_s$ 指定各模式质量的变化；模式名称的相似性不确定这些函数。其可计算性还需输入表示与有效求值条件，仅上述数据并未给出这些条件。

定义 14.2–14.6 区分独立源乘积、仅相邻两源的局部响应及最终有限事件推前。非二值情形可将各个 $\mathbb B$ 换为相应有限输出集合，并保留每个核的非负性、归一化及同一推前条件；命题 14.4、14.6 的有限求和证明不变。


---

## 15. 稳定静态场到能级的桥接

前十四节只规定了五态概率载体和外部桥接接口。本节给出统一场论所需的最小静态场公理，并把三种不同的谱量严格区分：静态 Hessian 的曲率谱、耗散演化的衰减谱、辛提升后的振动能级。

### 定义 15.1（候选静态场接口，不是原生基础对象）

本定义中的 \(\mathcal C,\mathcal E,K_*,M,J\) 是后续连续场或动力学实现的候选接口，不属于前十四节已经给出的原生对象。只有在第 16 节的桥接公理被明确加入后，才允许把它们解释为物理配置空间、能量泛函、迁移率或辛结构；第 15 节本身不从五态代数推出这些对象。

令 \(\mathcal C\) 为带内积的配置 Hilbert 空间，\(\mathcal E:\mathcal C\to\mathbb R\) 为二阶 Fréchet 可微能量泛函，令 \(\Phi_*\in\mathcal C\) 满足

\[
D\mathcal E(\Phi_*)=0,\qquad
K_*:=D^2\mathcal E(\Phi_*).
\]

先在规范固定后的切空间 \(T_*\subseteq T_{\Phi_*}\mathcal C\) 上工作。称 \(\Phi_*\) 半稳定，若 \(K_*\ge0\)；称其严格稳定，若存在 \(\mu>0\) 使

\[
\langle u,K_*u\rangle\ge\mu\|u\|^2,\qquad u\in T_*.
\]

规范方向应先商掉或固定，否则 \(K_*\) 的零空间可能只是规范冗余。观察核 \(\ker D(P\circ\Pi)_{\Phi_*}\) 与曲率核 \(\ker K_*\) 不是同一个对象：前者表示读出看不见的方向，后者表示能量二阶项不变的方向。

### 定理 15.2（静态 Hessian、梯度流和辛谱）

设 \(K_*=K_*^*>0\)，且 \(M=M^*>0\) 为有界迁移率。

1. 梯度流
   \[
   \dot u=-MK_*u
   \]
   的衰减率由 \(\operatorname{Spec}(MK_*)\) 给出。由于
   \[
   MK_*=M^{1/2}\bigl(M^{1/2}K_*M^{1/2}\bigr)M^{-1/2},
   \]
   它与正自伴算子 \(M^{1/2}K_*M^{1/2}\) 相似，因而谱为正实数。严格稳定时
   \[
   \operatorname{Spec}(MK_*)\subseteq[\mu\,m_M,\infty)
   \]
   若 \(M\ge m_M I\)。

2. 取 \(J^*=-J\) 为可逆辛结构，Hamilton 线性化为
   \[
   \dot u=JK_*u.
   \]
   有
   \[
   JK_*=K_*^{-1/2}
   \bigl(K_*^{1/2}JK_*^{1/2}\bigr)K_*^{1/2},
   \]
   中间算子是斜自伴的，因此 \(JK_*\) 的谱在有限维情形为纯虚数成对 \(\{\pm i\omega_j\}\)。二次能量
   \[
   H_2(u)=\tfrac12\langle u,K_*u\rangle
   \]
   沿该流守恒。

证明：第一项是相似变换。第二项由 \(J^*=-J\) 得 \(K_*^{1/2}JK_*^{1/2}\) 斜自伴；斜自伴矩阵的谱纯虚。能量导数为
\[
\frac{d}{dt}H_2
=\langle K_*u,JK_*u\rangle=0
\]
，因为 \(J\) 斜自伴。证毕。

因此 \(\operatorname{Spec}(K_*)\) 是静态曲率，\(\operatorname{Spec}(MK_*)\) 是耗散时间尺度，\(\omega_j\) 才是辛振动频率。只有在附加正则量子化公理后，\(\hbar\omega_j(n+\tfrac12)\) 才可称为量子能级。

### 定义 15.3（静态场到 FIB 的推前）

设 \((\Omega,\mu)\) 为有限或概率测度空间，场 \(\Phi\) 诱导密度 \(\rho_\Phi\)，并给出五个可测分区 \(e_s:\Omega\to[0,1]\)，满足 \(\sum_s e_s=1\)。定义

\[
\Pi(\Phi)_s=\int_\Omega e_s\,\rho_\Phi\,d\mu.
\]

当 \(\rho_\Phi\ge0\) 且归一化时，\(\Pi(\Phi)\in\Delta(\Sigma)\)。再定义

\[
P_{\mathrm{vis}}(\Phi)
=\bigl(\mathbb E_{\Pi(\Phi)}x,\mathbb E_{\Pi(\Phi)}y,
\mathbb E_{\Pi(\Phi)}z\bigr).
\]

若存在 \(v_\kappa\in T_*\) 使

\[
D\Pi_{\Phi_*}(v_\kappa)=d,\qquad
D(P_{\mathrm{vis}})_{\Phi_*}(v_\kappa)=0,
\]

则称 \(v_\kappa\) 为 FIB 隐藏法向。它是场的隐藏读出方向；只有当 \(K_*v_\kappa=0\) 时才同时是静态零模。若 \(K_*v_\kappa=\eta_\kappa v_\kappa\) 且 \(\eta_\kappa>0\)，则 \(\eta_\kappa\) 是该方向的静态曲率，而不是自动的动力学能级。

### 定理 15.4（FIB 纤维的自由能谱）

固定 \((X,Y,Z)\)，令 \(r=1-Z\)，并假设纤维内部 \(p_s>0\)。给定状态能量 \(E_s\)，定义

\[
F_\beta(p)=\sum_sE_sp_s-\beta^{-1}
\Bigl(-\sum_sp_s\log p_s\Bigr).
\]

沿 \(p_\kappa\) 有

\[
\frac{dF_\beta}{d\kappa}
=\Delta E+\beta^{-1}\vartheta,\qquad
\Delta E=E_0+E_{25}-E_2-E_5,
\]

\[
\vartheta=\log\frac{p_0p_{25}}{p_2p_5},\qquad
\frac{d^2F_\beta}{d\kappa^2}
=\beta^{-1}\mathcal I(\kappa)>0,
\]

其中
\[
\mathcal I(\kappa)
=p_0^{-1}+p_2^{-1}+p_5^{-1}+p_{25}^{-1}.
\]

所以自由能在每条合法纤维上严格凸，唯一平衡点满足

\[
\frac{p_0p_{25}}{p_2p_5}=e^{-\beta\Delta E}.
\]

在简并条件 \(\Delta E=0\) 下，平衡点正是最大熵点
\[
\kappa_*=\frac{XY}{r},
\]
并且 \(\Delta=r\kappa-XY=0\)。这里 \(\beta^{-1}\mathcal I_*\) 是 \(\kappa\) 方向的静态自由能曲率。

证明：沿 seam 有 \(p_0'=p_{25}'=1\)、\(p_2'=p_5'=-1\)。对熵逐项微分得到 \(H'=-\vartheta\)，再次微分得到 \(\vartheta'=\mathcal I\)。代入自由能定义即得。证毕。

### 定义 15.5（FIB 耗散谱与 FIB 振动能级）

质量作用动力学取为

\[
\dot\kappa=-\gamma\Delta
=-\gamma r(\kappa-\kappa_*)
\]

在 \(\Delta E=0\) 的平衡附近，其线性衰减率为

\[
\lambda_\kappa=\gamma r.
\]

该量是耗散谱，不是量子能量。若引入隐藏坐标的共轭动量 \(\pi_\kappa\)，定义局部 cotangent Hamiltonian

\[
H_\kappa
=\frac{\pi_\kappa^2}{2m_\kappa}
+\frac12\bigl(\beta^{-1}\mathcal I_*\bigr)
(\kappa-\kappa_*)^2,
\]

则辛线性化频率为

\[
\omega_\kappa
=\sqrt{\frac{\beta^{-1}\mathcal I_*}{m_\kappa}},
\]

形式量子化后才得到

\[
E_n=\hbar\omega_\kappa\left(n+\tfrac12\right).
\]

因此，统一理论中必须同时记录 \(\eta_\kappa\)、\(\lambda_\kappa\)、\(\omega_\kappa\) 三个量，不能用 \(\gamma r\) 直接替代能级。

### 定理 15.6（树场与 FIB 的乘积稳定性）

令 \(\mathcal H_{\mathrm{tree}}=\ell^2(V_{\mathrm{FibTree}})\)，
\[
Lf(p)=\deg(p)f(p)-\sum_{q\sim p}f(q),\qquad
\phi(p)=2^{-|p|},\qquad
H_{\mathrm{tree}}=aL-gM_\phi.
\]

已有 Whole-rho 结果给出
\[
L\phi=\mathbf1_o,\quad \|\phi\|^2=2,\quad Q(\phi)=1,
\quad H_{\mathrm{tree}}\ge
\bigl(a(3-2\sqrt2)-g\bigr)I.
\]

在定义好的乘积空间
\[
\mathcal H_{\mathrm{tot}}
=\mathcal H_{\mathrm{tree}}\otimes\mathcal H_{\mathrm{FIB}}
\]
上，令
\[
H_{\mathrm{tot}}
=H_{\mathrm{tree}}\otimes I+
I\otimes K_{\mathrm{FIB}}+V_{\mathrm{bridge}},
\]
其中 \(V_{\mathrm{bridge}}=V_{\mathrm{bridge}}^*\)。若
\[
H_{\mathrm{tree}}\ge\varepsilon_tI,\qquad
K_{\mathrm{FIB}}\ge\varepsilon_fI,\qquad
\|V_{\mathrm{bridge}}\|<\varepsilon_t+\varepsilon_f,
\]
则
\[
H_{\mathrm{tot}}\ge
(\varepsilon_t+\varepsilon_f-\|V_{\mathrm{bridge}}\|)I>0.
\]

若 \(V_{\mathrm{bridge}}\) 为紧算子，连续谱的阈值保持不变，低于阈值的离散束缚态才可能由桥接产生。该乘积算子不是天然存在的统一场定理，而是需要明确给出张量积状态空间和耦合算子。

### 命题 15.7（块 Hessian 与隐藏能级重整化）

在静态二阶近似中，若树场变量为 \(u\)，FIB 隐藏变量为 \(q\)，总 Hessian 为

\[
K=
\begin{pmatrix}
A&B\\ B^*&C
\end{pmatrix},
\qquad A>0,
\]

则消去 \(u\) 后的有效 FIB 刚度为 Schur 补

\[
K_{\mathrm{eff}}=C-B^*A^{-1}B.
\]

在一维隐藏通道上，
\[
k_{\mathrm{eff}}=c-b^*A^{-1}b.
\]
严格稳定当且仅当 \(A>0\) 且 \(K_{\mathrm{eff}}>0\)。当 \(k_{\mathrm{eff}}=0\) 时出现真正的统一场零模；当 \(k_{\mathrm{eff}}<0\) 时静态背景失稳。由此可把树场与 FIB 的耦合效应精确定义为隐藏曲率的重整化，而不是把两个谱直接相加。

### 定义 15.8（三角网络的静态源场）

令三条源场的 Hilbert 空间为
\(\mathcal H_\alpha,\mathcal H_\beta,\mathcal H_\gamma\)，各自静态 Hamiltonian 为 \(H_\alpha,H_\beta,H_\gamma\)。无源间相互作用时

\[
H_{\mathrm{src}}
=H_\alpha\otimes I\otimes I+
I\otimes H_\beta\otimes I+
I\otimes I\otimes H_\gamma.
\]

若温度参数相同，则 Gibbs 态严格分解为

\[
\rho_{\mathrm{src}}
=\rho_\alpha\otimes\rho_\beta\otimes\rho_\gamma,
\qquad
\rho_i=\frac{e^{-\beta H_i}}{\operatorname{Tr}(e^{-\beta H_i})}.
\]

局部响应核分别只读取相邻两源，并经有限事件分区推前到 \(\Sigma\)。所得 FIB 律是三角静态场的局部边缘。若出现 \(V_{\alpha\beta\gamma}\) 的非局部交叉项，则必须把它列为 triangle-locality defect；不能再自动使用独立源乘积。

### 定义 15.9（RH 零空间的静态算子）

设 \(\mathcal Z\) 为 zeta 非平凡零点的索引集合，\(\rho_v\) 为对应零点。令
\[
\mathcal H_Z=\ell^2(\mathcal Z),\qquad
R e_v=\rho_v e_v,
\]
并定义
\[
H_Z=-i(R-\tfrac12 I),
\]
其自然定义域为
\[
D(H_Z)=
\left\{\psi:
\sum_v|\rho_v-\tfrac12|^2|\psi_v|^2<\infty
\right\}.
\]

则 \(H_Z\) 自伴当且仅当全部 \(\operatorname{Re}\rho_v=\tfrac12\)。在 RH 条件下
\[
\rho_v=\tfrac12+i\gamma_v,\qquad
H_Ze_v=\gamma_v e_v.
\]
Cayley 算子
\[
C_Z=(R-I)R^{-1}
=(iH_Z-\tfrac12I)(iH_Z+\tfrac12I)^{-1}
\]
酉当且仅当 \(H_Z\) 自伴，等价于 RH（假设零点数据穷尽且按重数索引）。

### 定理 15.10（统一场到 RH 的必要桥）

若希望把统一场的静态能级识别为 RH 零点虚部，至少需要构造下列之一：

1. 保持内积的酉映射
   \[
   U:\mathcal H_{\mathrm{field}}\to\mathcal H_Z,\qquad
   UH_{\mathrm{field}}U^{-1}=H_Z;
   \]
2. 或者构造正则化特征行列式
   \[
   \xi(\tfrac12+iE)
   =C(E)\det_{\mathrm{reg}}(E-H_{\mathrm{field}})
   \]
   并证明零点重数与谱重数一致。

在没有 \(U\)、行列式恒等式或同等强度的谱对应定理前，FIB 的 \(\Delta=0\)、树场的束缚态和 RH 临界线只是具有共同形式的约束，不能互相推出。

### 15.11 统一场解释的依赖条件

本卷的统一场解释依次依赖下列对象与条件：

1. 配置空间 $\mathcal C$、规范群和规范固定切空间；
2. $\mathcal E$ 及其二阶 Hessian $K_*$，以及静态背景的存在性与稳定性；
3. 五个事件分区 $e_s$，以及 $\Pi$ 保持概率的条件；
4. $v_\kappa$，以及 $D(P\circ\Pi)$ 的读出核与 $K_*$ 的曲率核的区分；
5. 耗散迁移率 $M$、辛结构 $J$、FIB 质量 $m_\kappa$ 所需的公理；
6. 树场与 FIB 的乘积空间、桥接算子以及 Schur 补；
7. 三角网络中的独立源乘积和局部推前关系；
8. 统一场到 RH 零空间的 $U$ 或正则化行列式所需的对应关系。

第 1 至 5 项的对象与条件可在有限维近似中表述，相关存在性和稳定性仍须各自的假设与证明；第 6 至 8 项依赖额外的外部桥接。尚缺这些条件时，相应的算术、三角或 RH 结论仍未成立。

---

## 16. 数学来源分层与保守静态场定义

本节规定所有对象的来源层级。目的不是增加一个未经检验的物理本体，而是保证每个后续命题都能追溯到已有有限数学对象，或明确标注所需的新公理。

### 定义 16.1（三层来源系统）

把本卷对象分为三层。

**Primitive 层。** 原生给定的有限对象为
\[
\Sigma=\{0,2,3,5,25\},\qquad
\mathcal A_0=\mathbb R^\Sigma,\qquad
\Delta_0=\Delta(\Sigma),
\]
五态函数 \(x,y,z\)，可见投影
\[
P_0:\Delta_0\to\mathbb R^3,\qquad
P_0(p)=(X,Y,Z),
\]
seam 向量
\[
d=(1,-1,0,-1,1),
\]
以及每个有限 Fibonacci 支持图的顶点集 \(V_j\)、边集 \(E_j\)、质量边界映射 \(B_j:\mathbb R^{E_j}\to\mathbb R^{V_j}\) 和边读出映射 \(A_j:\mathbb R^{E_j}\to\mathbb R^{m_j}\)。在 \(j=0\) 的五态图上，已有 \(Bf\) 和 \(Af\) 正是这些映射的实例。

**Derived 层。** 只使用 Primitive 层的有限代数、线性代数、凸性和图论定义出的对象，包括
\[
p_\kappa,\quad
\mathcal F_{X,Y,Z},\quad
\Delta=r\kappa-XY,\quad
\ker DP_0=\mathbb Rd,
\]
Shannon 熵、负熵势
\[
\mathcal V_{\mathrm{ent}}(p)=-H(p)=\sum_s p_s\log p_s,
\]
以及内部单纯形上的 Fisher 二次型
\[
g_{F,p}(u,v)=\sum_s\frac{u_sv_s}{p_s},
\qquad
T_p\Delta_0=\{u:\sum_su_s=0\}.
\]
图论方面，\(Z_j=\ker B_j\) 是循环载体，\(L_j=B_jB_j^*\) 给出由 incidence 映射导出的非负图二次型
\[
Q_j(v)=\langle v,L_jv\rangle=\|B_j^*v\|^2.
\]
这些定义不含时间、质量、能量级或量子化假设。

**Bridge 层。** 下列对象不由上述有限结构自动产生，必须由明确桥接公理或构造加入：
\[
(M,g),\ E,\ \nabla^A,\ \Phi,\ \rho_\Phi,\ \mathcal E[\Phi],
\quad E_s,\quad M_{\mathrm{mob}},\quad J,\quad m_\kappa,
\]
树场与 FIB 的耦合 \(V_{\mathrm{bridge}}\)，三角网络的独立源提升，以及到 zeta 零点空间的酉映射或正则化行列式。特别地，\(\gamma r\) 只有在声明一个耗散迁移率后才是时间衰减率；\(\hbar\omega\) 只有在声明 cotangent 提升和量子化规则后才是能级。

### 定义 16.2（双层有限载体：图场与局部 FIB 概率场）

令 \(V_j\) 为第 \(j\) 层的有限图节点集，令
\[
\Phi_j=\mathbb R^{V_j}
\]
为图场空间。每个图节点承载一个五态 FIB 概率律，因此定义
\[
\Pi_j=\bigl(\Delta(\Sigma)\bigr)^{V_j},
\qquad
T\Pi_j=\bigl(T\Delta(\Sigma)\bigr)^{V_j}.
\]
这里的 \(\Pi_j\) 要求每个节点逐点满足
\[
p_{j,v,s}\ge0,\qquad
\sum_{s\in\Sigma}p_{j,v,s}=1
\quad (v\in V_j),
\]
而不是只要求所有节点和状态的总和为一。

在一个局部可见读出模型中，定义
\[
P_j^{\mathrm{loc}}:\Pi_j\to(\mathbb R^3)^{V_j},
\qquad
(P_j^{\mathrm{loc}}p)_v=P_0(p_v).
\]
若需要全局读出，必须另给显式线性映射
\[
G_j:(\mathbb R^3)^{V_j}\to\mathbb R^{m_j},
\qquad
P_j=G_j\circ P_j^{\mathrm{loc}}.
\]
相应的可见读出核为
\[
N_j=\ker\bigl(DP_j|_{T\Pi_j}\bigr).
\]
在纯局部读出情形，
\[
N_j=\bigl(\ker DP_0\bigr)^{V_j}
=(\mathbb Rd)^{V_j}.
\]
若一个层级只保留单个局部 FIB 单元，取 \(V_0=\{*\}\)，则
\[
\Phi_0=\mathbb R,\qquad
\Pi_0=(\Delta(\Sigma))^{\{*\}}\cong\Delta(\Sigma),
\qquad
N_0\cong\mathbb Rd.
\]
这就是“五态局部载体退化为 \(\Delta(\Sigma)\)”的精确定义。若把五态状态转移图本身作为图空间，则其顶点集是 \(\Sigma\)，属于另一个 graph/edge sector，不能与上述单局部单元的 \(V_0=\{*\}\) 记号混用。

令已有图边空间为 \(\mathbb R^{E_j}\)，边界映射为
\[
B_j:\mathbb R^{E_j}\to\mathbb R^{V_j},
\]
并定义循环核
\[
Z_j=\ker B_j.
\]
\(Z_j\) 只属于图边流或 graph field sector，不是局部 FIB 概率的隐藏坐标。由此得到双层有限载体
\[
C_j=\Phi_j\times\Pi_j\times N_j\times Z_j.
\]
若研究概率场而不记录独立图场，可取投影载体
\[
C_j^{\mathrm{prob}}=\Pi_j\times N_j.
\]

全局单纯形
\[
\widetilde\Delta_j
=\left\{q\in\mathbb R^{V_j\times\Sigma}:
q_{v,s}\ge0,\ \sum_{v,s}q_{v,s}=1\right\}
\]
是另一种模型。它只规定跨节点总质量为一，不能与逐节点归一化的 \(\Pi_j=(\Delta(\Sigma))^{V_j}\) 同时使用，除非另加明确的归一化或条件概率解释。

为了构造投影系统，给出节点压缩 \(\pi_{j+1,j}:V_{j+1}\to V_j\)，其图场推前
\[
\pi^\Phi_{\#}:\Phi_{j+1}\to\Phi_j
\]
必须是显式线性映射。对概率场，给定权重
\[
a_{w|v}\ge0,\qquad
\sum_{w:\pi_{j+1,j}(w)=v}a_{w|v}=1,
\]
定义
\[
(\pi^\Pi_{\#}p)_v
=\sum_{w:\pi_{j+1,j}(w)=v}a_{w|v}p_w.
\]
这是五态概率律的凸组合，因而逐节点保持 \(\Delta(\Sigma)\)，其导数也把 \(T\Pi_{j+1}\) 映到 \(T\Pi_j\)。

若存在读出压缩
\[
\rho_{j+1,j}:\mathbb R^{m_{j+1}}\to\mathbb R^{m_j}
\]
满足
\[
\rho_{j+1,j}P_{j+1}
=P_j\pi^\Pi_{\#},
\]
则 \(D\pi^\Pi_{\#}\) 把 \(N_{j+1}\) 映到 \(N_j\)。再给出边推前
\[
r_{j+1,j}:\mathbb R^{E_{j+1}}\to\mathbb R^{E_j}
\]
并要求
\[
B_jr_{j+1,j}
=\pi^\Phi_{\#}B_{j+1},
\]
即可保证 \(r_{j+1,j}(Z_{j+1})\subseteq Z_j\)。于是
\[
q_{j+1,j}(\phi,p,v,z)
=\bigl(
\pi^\Phi_{\#}\phi,\,
\pi^\Pi_{\#}p,\,
D\pi^\Pi_{\#}v,\,
r_{j+1,j}z
\bigr):C_{j+1}\to C_j
\]
是类型正确的有限投影。

### 定义 16.3（保守静态场）

给定上面的有限投影系统，定义抽象静态场为逆极限
\[
\mathfrak F
=\varprojlim_j(C_j,q_{j+1,j})
=\left\{(c_j)_j:
c_j\in C_j,\ q_{j+1,j}(c_{j+1})=c_j\right\}.
\]
其元素只是所有有限层记录的相容族，不携带先验时间参数、惯性参数或连续空间。逆极限非空性不是集合论自动事实，必须由压缩映射的相容性与有限层一致性另行证明。

定义第 \(j\) 层概率场的 canonical 负熵为
\[
\mathcal V_{\mathrm{ent},j}(p)
=\sum_{v\in V_j}\sum_{s\in\Sigma}
p_{v,s}\log p_{v,s},
\qquad p\in\Pi_j^\circ.
\]
称 \(c=(c_j)_j\) 为熵稳定静态场，若每个 \(p_j\) 位于
\(\Pi_j^\circ=(\Delta(\Sigma)^\circ)^{V_j}\)，并且对所有
\(u\in T_{p_j}\Pi_j\)
\[
D^2\mathcal V_{\mathrm{ent},j}(p_j)[u,u]
=\sum_{v\in V_j}\sum_{s\in\Sigma}
\frac{u_{v,s}^2}{p_{j,v,s}}\ge0.
\]
若存在 \(\mu_j>0\) 使左端至少为
\(\mu_j\|u\|^2\)，称其在第 \(j\) 层严格熵稳定。这里的稳定性是由逐节点概率单纯形的负熵凸性导出的数学性质，不等于尚未定义的物理能量稳定性。若同时要求 graph sector 稳定，则另以
\[
Q_j(\phi)=\|B_j^*\phi\|^2\ge0
\]
作为图场的 canonical 非负二次型；这仍不引入物理惯性或时间演化。

### 定理 16.4（熵势的 canonical Hessian）

在每个内部局部概率场 \(\Pi_j^\circ\) 上，负熵的 Hessian 满足
\[
D^2\mathcal V_{\mathrm{ent},j}(p)[u,u]
=\sum_{v\in V_j}\sum_{s\in\Sigma}
\frac{u_{v,s}^2}{p_{v,s}}
=:g_{F,j,p}(u,u)>0
\]
对任意非零 \(u\in T_p\Pi_j\)。因此 Fisher 纤维度量不是额外物理能量，而是负熵势的 canonical 二阶型。若在每个节点取 seam 方向
\[
u_{v,\cdot}=a_vd,
\]
则
\[
g_{F,j,p}(u,u)
=\sum_{v\in V_j}a_v^2
\left(
p_{v,0}^{-1}+p_{v,2}^{-1}
+p_{v,5}^{-1}+p_{v,25}^{-1}
\right).
\]
当 \(V_j=\{*\}\) 且 \(a_*=1\) 时，这正是五态纤维的
\[
\mathcal I(\kappa)
=p_0^{-1}+p_2^{-1}+p_5^{-1}+p_{25}^{-1}.
\]

证明：逐项微分 \(p_{v,s}\log p_{v,s}\) 两次得到 \(1/p_{v,s}\)，再限制到逐节点质量零切空间即可。正性来自所有 \(p_{v,s}>0\)。代入 \(u_{v,\cdot}=a_vd\) 并使用 \(d_s^2=1\) 得到 seam 公式。证毕。

### 定理 16.5（保守扩展定理）

令 \(\mathsf L_0\) 是由 Primitive 层和上述 Derived 定义组成的形式理论。令 \(\mathsf H\) 是一组明确写出的 Bridge 假设，例如连续场实现、迁移率正性、辛结构、树场耦合界或 RH 谱对应。若
\[
\mathsf L_0+\mathsf H\vdash T,
\]
则对于每个 \(\mathsf L_0\) 模型 \(M\) 和每个把 \(M\) 扩张为满足 \(\mathsf H\) 的模型 \(M^+\)，都有
\[
M^+\models T.
\]
若 \(T\) 只含 \(\mathsf L_0\) 语言且不使用 \(\mathsf H\)，则它对所有 \(\mathsf L_0\) 模型成立；Bridge 层不能把一个未证明的 Primitive 命题变成定理。若不存在满足 \(\mathsf H\) 的模型扩张，条件结论只是空真，因此 Bridge 的一致性与扩张存在性本身也属于待证明义务。反之，若 \(T\) 含 \(E_s,J,M_{\mathrm{mob}},V_{\mathrm{bridge}}\) 或 RH 映射，则必须在定理陈述中逐项列出相应 \(\mathsf H\)。

证明：第一句是形式证明在模型解释下的保真性。第二句是定义扩张的保守性：Derived 符号可逐项展开回 \(\mathsf L_0\)，而未列入 \(\mathsf H\) 的 Bridge 符号不存在解释义务。故任何遗漏的物理或 RH 假设都不能由语法推导出来。证毕。

### 16.6 有限数学与外部桥接的依赖分层

本卷的对象与条件分为以下两层。

**L0，原生有限数学：**

1. Mode、$\mathcal A_0=\mathbb R^\Sigma$、概率单纯形和有限求和；
2. visible、$\kappa$、seam，以及重构式、合法纤维和 $\ker DP_0=\mathbb Rd$；
3. Shannon 熵、负熵 Hessian 和 Fisher 线元，以及定理 16.4；
4. 有限图的边空间、$B_j,A_j$、循环核和 $L_j=B_jB_j^*$；
5. 有限载体 $C_j$、兼容压缩 $q_{j+1,j}$ 和逆极限 $\mathfrak F$。

**L1+，外部桥接义务：**

1. 连续黎曼场实现 \((M,g,E,\nabla^A,\Phi,\rho_\Phi,\Pi)\)；
2. 物理静态能量、状态能量 \(E_s\)、迁移率 \(M_{\mathrm{mob}}\)、辛结构 \(J\) 和质量 \(m_\kappa\)；
3. Whole-rho 树场与 FIB 的乘积空间及 \(V_{\mathrm{bridge}}\)；
4. 三角网络独立源提升和局部推前；
5. 从统一场谱到 RH 零空间的酉映射 \(U\) 或正则化行列式；
6. 量子化规则与能级解释。

在 L1+ 中任何一项尚未构造时，只能把相应结论写成条件命题，不能把它当作 L0 的推论。这个分层也规定了本卷“统一场”的严格含义：基础是相容有限静态记录的逆极限，连续物理场和 RH 谱识别是待证明的扩展。

---

## 17. 外部数学锚点与桥接账本

本节只引入可以明确写出假设、结论和输入输出类型的外部数学结果。引用外部研究的作用是限定可采用的桥接形式，不是把外部模型自动等同于 Auric FIB。每个结果都分为四项记录：假设、结论、可用接口和不能推出的内容。

### 17.1 图 Dirichlet 形式、Mosco 收敛与几何极限

#### 17.1.1 Mosco 型桥接的标准记账

令每一层图场空间经过线性嵌入进入共同 Hilbert 空间 \(\mathcal H\)，记嵌入后的能量为

\[
\mathcal Q_j:\mathcal H\to(-\infty,+\infty].
\]

称 \(\mathcal Q_j\) Mosco 收敛到 \(\mathcal Q\)，如果满足：

1. 弱下极限条件。若 \(u_j\rightharpoonup u\) 弱收敛，则
   \[
   \mathcal Q(u)\leq \liminf_{j\to\infty}\mathcal Q_j(u_j).
   \]

2. 强恢复条件。对每个 \(u\in\mathcal H\)，存在 \(u_j\to u\) 强收敛，使
   \[
   \limsup_{j\to\infty}\mathcal Q_j(u_j)\leq \mathcal Q(u).
   \]

闭、非负二次型还必须满足 Markov 收缩性质，才能称为 Dirichlet 形式：对 \(C(t)=\min(1,\max(0,t))\)，要求
\[
\mathcal Q(C\circ u)\leq\mathcal Q(u).
\]
因此该桥需要同时验证极限定义域在 \(\mathcal H=L^2(X,\mu)\) 中稠密，以及 Markov 性在选定嵌入和收敛下传递。Mosco 的两条条件本身不要求等度量紧性；紧性用于从序列抽取极限或进一步证明离散谱收敛。有限层逆极限本身不提供这些分析条件。

#### 17.1.2 Gigli–Mondino–Savaré

Gigli、Mondino 和 Savaré 的论文 [Convergence of pointed non-compact metric measure spaces and stability of Ricci curvature bounds and heat flows](https://arxiv.org/abs/1311.4907) 在 pointed metric-measure 收敛框架中证明了 RCD 类型曲率条件、热流和 Cheeger 能量的稳定性。对于满足适当紧性、有界性或正的 RCD 曲率下界的空间，Cheeger energies 以适配的 \(\Gamma\)-Mosco 方式收敛，相关 Laplacian 谱也具有稳定性。

相应的数学依赖关系是：

\[
\mathrm{GraphEnergySequence}
\longrightarrow
\mathrm{CommonL2Embedding}
\longrightarrow
\mathrm{MoscoLimit}
\longrightarrow
\mathrm{DirichletForm}.
\]

它允许把

\[
Q_j(\phi)=\langle\phi,L_j\phi\rangle
\]

提升为极限 Dirichlet 形式。它没有直接证明极限是光滑黎曼流形，最自然的极限对象可能只是 metric-measure space 或 RCD space。

#### 17.1.3 Ambrosio–Honda

Ambrosio 和 Honda 的 [New stability results for sequences of metric measure spaces with uniform Ricci bounds from below](https://arxiv.org/abs/1605.07908) 采用 extrinsic common-host 方法处理 measured-Gromov–Hausdorff 收敛。在统一 Ricci 下界等条件下，他们证明 Cheeger energies 的 Mosco 收敛，并建立 Sobolev、Hessian、\(W^{2,2}\) 和 Bakry–Émery/Ricci 条件的稳定性。

有限层 Fibonacci 图的场若要具有所述几何极限，桥接条件必须显式包含：

\[
\iota_j:\Phi_j\hookrightarrow \mathcal H,
\]

\[
\text{uniform coercivity},
\qquad
\text{equicoercivity},
\qquad
\text{compactness},
\qquad
\text{Mosco liminf/recovery}.
\]

逆极限的相容性只负责记录层间投影，不能替代 common-host 分析。

#### 17.1.4 Korevaar–Schoen 能量

Alonso Ruiz 和 Baudoin 的 [Dirichlet forms on metric measure spaces as Mosco limits of Korevaar–Schoen energies](https://arxiv.org/abs/2301.08273) 给出 Korevaar–Schoen 型非局部能量的 Mosco 极限充分条件，并使用 Rellich–Kondrachov 型紧性。该结果适用于 Cheeger spaces，也包括部分 fractal-like metric-measure spaces。

相应的非局部图能量为

\[
\mathcal Q_{j,\varepsilon}(u)
=
\frac{1}{\varepsilon^{m+2}}
\sum_{v,w}
\eta\!\left(\frac{d_j(v,w)}{\varepsilon}\right)
|u_v-u_w|^2\mu_j(v)\mu_j(w),
\]

其 Mosco 收敛是额外的待证条件；极限不预设为流形。若最终需要黎曼流形，仍要增加一个独立的光滑化或流形识别定理。

#### 17.1.5 随机几何图谱收敛

García Trillos、Gerlach、Hein 和 Slepčev 的 [Error estimates for spectral convergence of the graph Laplacian on random geometric graphs towards the Laplace–Beltrami operator](https://arxiv.org/abs/1801.10108) 假设样本独立同分布于 \(M\subset\mathbb R^d\) 的 \(m\) 维光滑子流形，邻域带宽趋于零并满足样本规模和带宽的尺度关系。在这些条件下，图 Laplacian 的特征值和特征函数以显式速率逼近加权 Laplace–Beltrami 算子。

接口必须写成条件形式：

\[
\mathrm{SampledManifold}(M,g,\mu)
+
\mathrm{BandwidthScaling}(n,h)
\Longrightarrow
\mathrm{GraphSpectrum}\to\mathrm{LB\ Spectrum}.
\]

因此 Whole-rho 图若要获得 Riemannian 解释，必须先提供节点采样、距离、权重和尺度参数。仅有一个抽象图和一个 Poisson 型函数 \(\phi(p)=2^{-|p|}\) 不足以得到 Laplace–Beltrami 算子。

#### 17.1.6 最新的 Ricci-limit 与不同维度结果

Inagaki 的 [Spectral convergence of graph Laplacians with Ricci curvature bounds and in non-collapsed Ricci limit spaces](https://arxiv.org/abs/2506.07427) 在闭 \(m\) 维流形上假设

\[
\operatorname{Ric}_g\ge -(m-1)K,
\]

正的体积下界和有界直径，并对 \(\varepsilon\)-邻域图给出特征值与特征函数的高概率误差界。该框架还推广到 non-collapsed Ricci-limit spaces，因此极限允许出现非光滑点。

Bungert 和 Slepčev 的 [Convergence of graph Dirichlet energies and graph Laplacians on intersecting manifolds of varying dimensions](https://arxiv.org/abs/2509.24458) 研究不同内维流形相交的情形。其结论显示，非归一化图能量可能只看见最高维 sector，归一化能量才得到适应多个维度的 tensorized Dirichlet energy。

金字塔层级的极限因此依赖以下归一化条件：

\[
\mathrm{LayerNormalization}
\]

必须成为类型参数或定理假设。否则不同层的维数变化可能导致低维隐藏 sector 在极限中被系统性丢弃。

#### 17.1.7 图离散化的几何假设

Bhattacharya 和 Maity 的 [Graph discretization of Laplacian on Riemannian manifolds with bounds on Ricci curvature](https://arxiv.org/abs/2501.18323) 在紧致无边界流形上使用 Ricci 下界、injectivity radius 下界、直径上界和小球体积条件，证明图方法对 Laplace–Beltrami 特征值的逼近。

因此应将

\[
\mathrm{DirichletToGeometry}
\]

拆成两个不同输出：

1. 弱输出：
   \[
   \mathrm{DirichletForm}
   \longrightarrow
   \mathrm{MetricMeasure/RCD\ Limit}.
   \]

2. 强输出：
   \[
   \mathrm{DirichletForm}
   +
   \mathrm{RicciBound}
   +
   \mathrm{InjectivityRadius}
   +
   \mathrm{Regularity}
   \longrightarrow
   \mathrm{SmoothRiemannianRealization}.
   \]

第二个输出不能从第一个输出自动得到。

### 17.2 Fisher 几何、熵 Hessian 与有限状态梯度流

#### 17.2.1 Fisher Hessian 的原生层

在内部概率单纯形

\[
\Delta(\Sigma)^\circ
=
\{p_s>0:\sum_sp_s=1\}
\]

上，负 Shannon 熵

\[
\mathcal V(p)=\sum_sp_s\log p_s
\]

的 Hessian 是

\[
D^2\mathcal V(p)[u,u]
=
\sum_s\frac{u_s^2}{p_s}.
\]

这是 FIB 文档中 \(\mathcal I(\kappa)\) 的数学来源。它不需要状态能量、温度或物理时间。

需要分开记录三种结构：

\[
D^2\mathcal V
\quad\text{是静态 Fisher 曲率},
\]

\[
\mathsf M D^2\mathcal V
\quad\text{是声明 mobility 后的耗散生成元},
\]

\[
J D^2\mathcal V
\quad\text{是声明辛结构后的线性 Hamiltonian 生成元}.
\]

#### 17.2.2 Maas 的有限 Markov 链梯度流

Maas 的 [Gradient flows of the entropy for finite Markov chains](https://arxiv.org/abs/1102.5238) 假设有限状态空间上的 Markov kernel 不可约且可逆。论文构造离散 Benamou–Brenier 型度量，使连续时间 Markov 链的概率律成为相对于平稳分布的相对熵梯度流。

若采用这条路线，必须提供随机核
\[
K_{st}\ge0,\qquad \sum_tK_{st}=1,\qquad
\pi_sK_{st}=\pi_tK_{ts},
\]
其连续时间生成元可取 \(Q=K-I\)。一般生成元满足的是 \(Q_{st}\ge0\)（\(s\ne t\)）和 \(\sum_tQ_{st}=0\)，不能与随机核的归一化混写。

FIB 的四角质量作用流在完整单纯形上是非线性的，需要单独验证 Onsager 因子分解，不能直接套用有限线性 Markov 链定理。设
\[
a=p_2p_5,\quad b=p_0p_{25},\quad
\Lambda(a,b)=
\begin{cases}
\dfrac{b-a}{\log b-\log a},&a\ne b,\\
a,&a=b,
\end{cases}
\]
并给定 \(\gamma>0\)，则
\[
\mathsf M_p=\gamma\Lambda(a,b)\,dd^{\mathsf T}
\]
是从余切空间到切空间的半正定 Onsager 算子。因为
\[
d^{\mathsf T}D\mathcal V(p)=\log(b/a),
\]
所以
\[
-\mathsf M_pD\mathcal V(p)=\gamma(a-b)d.
\]
这条有限代数恒等式证明所声明的 FIB 质量作用流确实是负熵的退化梯度流。其退化方向对应被保持的可见约束；参数 \(\gamma\) 仍是新增动力学数据。

#### 17.2.3 Erbar–Maas 的离散 Ricci 曲率

Erbar 和 Maas 的 [Ricci curvature of finite Markov chains via convexity of the entropy](https://arxiv.org/abs/1111.2687) 用 entropy 在离散 Wasserstein 型度量下的 geodesic convexity 定义有限 Markov 链的 Ricci 曲率，并证明离散 Bakry–Émery、Otto–Villani 类结果和 tensorisation。

对每个 FIB 节点，可定义一个有限状态 Markov kernel；但只有在给出可逆性、平稳分布和离散 transport metric 后，才可以使用离散 Ricci 语言。Fisher 曲率和 Erbar–Maas Ricci 曲率属于不同层次的对象，不能直接写成同一个符号。

#### 17.2.4 图上的信息 Hessian

Li 和 Lu 的 [Mean field information Hessian matrices on graphs](https://arxiv.org/abs/2203.06307) 在有限图概率单纯形上，对熵、线性能量和相互作用能量推导 mean-field information Hessian，并以最小特征值定义图上的离散曲率下界。

相应的有限层对象为：

\[
\Pi_j=(\Delta(\Sigma))^{V_j},
\]

\[
\mathcal V_j(p)
=
\sum_{v,s}p_{v,s}\log p_{v,s}
+
\mathcal U_j(p),
\]

\[
K_j=D^2\mathcal V_j.
\]

其中 \(\mathcal U_j\) 若包含边相互作用，必须显式给出。\(K_j\) 的最小特征值可以作为有限层静态稳定证书。它只有在另加物理单位和动力学结构后才可被解释为物理能量或时间尺度。

#### 17.2.5 Fisher 与 Wasserstein 的区分

Amari、Karakida 和 Oizumi 的 [Information Geometry Connecting Wasserstein Distance and Kullback–Leibler Divergence via the Entropy-Relaxed Transportation Problem](https://arxiv.org/abs/1709.10219) 在离散概率单纯形上区分 Fisher 几何、Wasserstein transport 和 KL divergence，并通过 entropy-relaxed transport 建立它们之间的关系。

这里须区分两种度量：

\[
g_F
\neq
g_{\mathrm{transport}}
\]

在没有 comparison theorem 时不能把两者识别。FIB 的 \(\mathcal I(\kappa)\) 是概率单纯形上的 Fisher 线元；图边界 \(B_j\) 产生的是流和 transport 结构。若要把两者组合为统一度量，需要证明一个明确的 comparison map 或 block metric。

### 17.3 Triangle-local 与 inflation 约束

#### 17.3.1 经典 triangle-local 的精确定义

官方 [Fast Inflation repository](https://github.com/vgitton/fast-inflation) 将 classical triangle-local 分布定义为

\[
p(a,b,c)
=
\int
d\alpha\,d\beta\,d\gamma\,
p_A(a\mid\beta,\gamma)
p_B(b\mid\gamma,\alpha)
p_C(c\mid\alpha,\beta),
\]

其中三个源变量独立。该集合非凸，因此单一 Bell 不等式框架不够。

FIB 推前最多提供

\[
Q_*p(a,b,c)\in\Delta(\Sigma),
\]

它是 triangle-local 模型的局部边缘。反向的 lift 需要单独证明。

#### 17.3.2 Inflation 的有限证书

Wolfe、Spekkens 和 Fritz 的 [The Inflation Technique for Causal Inference with Latent Variables](https://arxiv.org/abs/1609.00672) 通过复制潜变量因果结构，要求 inflated distribution 的某些 marginal 和 symmetry 满足线性约束。若目标分布无法扩张到某一级 inflation，则可以证明其与指定因果结构不相容。

Navascués 和 Wolfe 的 [The Inflation Technique Completely Solves the Causal Compatibility Problem](https://arxiv.org/abs/1707.06476) 证明 inflation 层级 asymptotically tight。通过第 \(n\) 阶检验的分布距离 causal-compatible set 为

\[
O(n^{-1/2})
\]

量级，且某些因果结构在低阶就已经精确。

这要求我们把

\[
\mathrm{TriangleLift}(p)
\]

从一个存在性占位符细分为：

\[
\mathrm{InflationFeasible}(p,N,q),
\]

其中：

- \(N\) 是有限 inflation 图；
- \(q\) 是 inflated output law；
- \(q\) 满足非负性和归一化；
- \(q\) 满足所有 marginal constraints；
- \(q\) 满足所有 source-induced symmetry constraints。

有限 infeasibility 是严格的非局部证书。有限 feasibility 只说明通过了该级松弛，不能推出真正 triangle-local。

#### 17.3.3 EJM 的最新精确结果

Gitton 和 Renner 的 [The Elegant Joint Measurement is Non-Classical in the Triangle Network](https://arxiv.org/abs/2510.15143) 给出了 EJM 分布在 triangle network 中 classical-incompatible 的首个证明。该工作结合 inflation、对称约化、Frank–Wolfe 和 exact arithmetic。配套 [Fast Inflation code](https://github.com/vgitton/fast-inflation) 明确区分：

- exact rational separating hyperplane certificate，可证明非局部；
- floating-point feasible inflation law，只能作为数值候选，不能证明兼容性；
- inflation size 增大时外逼近收紧，但变量规模大约按 \(n_o^N\) 增长。

指定 inflation 的约束可写为
\[
A_Nq=b_N(p),\qquad q\ge0,
\]
其中归一化已经包含在矩阵方程中。\(b_N(p)\) 可以包含独立可观测副本对应的乘积项，因而不必对 \(p\) 线性。一个精确 Farkas 证书是有理向量 \(y\)，满足
\[
A_N^{\mathsf T}y\ge0,\qquad
y^{\mathsf T}b_N(p)<0.
\]
若可行 \(q\) 存在，则
\[
0\le(A_N^{\mathsf T}y)^{\mathsf T}q
=y^{\mathsf T}A_Nq
=y^{\mathsf T}b_N(p)<0,
\]
矛盾。这样每个向量和矩阵都有固定维度，无须将原分布 \(p\) 和 inflated law \(q\) 当成同一空间中的对象。

#### 17.3.4 Fully quantum inflation

Smith、Wolfe 和 Spekkens 的 [Fully quantum inflation: quantum marginal problem constraints in the service of causal inference](https://arxiv.org/abs/2501.12320)，已在 2026 年发表于 [PRX Quantum](https://journals.aps.org/prxquantum/abstract/10.1103/244y-nh5n)。该方法把 inflation 推广到 quantum marginal problem，并对纯三量子比特态给出 triangle compatibility 的完整分类。

量子 triangle 的载体在 classical probability carrier 之外还需要满足下列条件的密度矩阵：

\[
\rho\succeq0,
\qquad
\operatorname{Tr}\rho=1,
\]

并把 marginal consistency 写成 partial trace 方程。五态 FIB 概率律不能自动承载 density operator、正半定性和量子边缘约束。

### 17.4 RH 与自伴谱桥

#### 17.4.1 Hilbert–Pólya 只是谱目标

Berry 和 Keating 的 [The Riemann zeros and eigenvalue asymptotics](https://epubs.siam.org/doi/10.1137/S0036144598347497) 提出零点虚部的计数函数与某个未知 Hermitian operator 的半经典能级计数具有相似性。这是谱启发和渐近证据，论文没有构造满足零点完整谱的自伴算子。

Connes 的 [Trace formula in noncommutative geometry and the zeros of the Riemann zeta function](https://arxiv.org/abs/math/9811068) 给出临界零点的谱解释和显式公式的 trace-formula 解释。任何统一场与 RH 谱的对应至少依赖一个 trace identity 或等价的正规化行列式关系。

#### 17.4.2 已有算子构造的边界

Bender、Brody 和 Müller 的 [Hamiltonian for the zeros of the Riemann zeta function](https://arxiv.org/abs/1608.03679) 构造了形式 Hamiltonian，并通过边界条件使其特征值对应 zeta 零点。作者明确指出该算子并非通常意义下的 Hermitian，若能严格证明其自伴性，才会得到 RH。

Li 的 [On the spectrum of a differential operator on a Hilbert–Pólya space](https://arxiv.org/abs/2404.11902) 在特定测试函数商空间上构造微分算子，并陈述零点与特征值之间的等价。该结果把“谱实现”与“自伴性”分开，不能单独推出 RH。

因此须区分下列数学条件：

\[
\mathrm{ZeroSpectrumRealization}
\]

和

\[
\mathrm{SelfAdjointness}.
\]

前者只说明零点被表示为谱，后者才控制谱是否位于实轴。

#### 17.4.3 Cayley 变换

对稠密定义、闭的算子 \(H\)，在适当 resolvent/domain 条件下定义 Cayley 变换

\[
U=(H-iI)(H+iI)^{-1}.
\]

标准 Cayley 定理给出：

\[
H=H^*
\iff
U\text{ unitary}.
\]

谱通过 Möbius 变换对应。可参考 [Encyclopedia of Mathematics: Cayley transform](https://encyclopediaofmath.org/index.php?title=Cayley_transform) 和仓库中的 [ZeroHilbertCayleyUnitarity.lean](https://github.com/the-omega-institute/trureturing/blob/dev/D5/S3/Midline/Cayley/ZeroHilbertCayleyUnitarity.lean)。

该定理的适用条件与对象必须包含：

- Hilbert space；
- operator domain；
- closedness；
- resolvent existence；
- exact Cayley map；
- unitary proof。

仅在有限对角矩阵上验证模长为一，不足以处理无界算子或零点重数。

## 18. Typed bridge ledger

下面的五个桥接类型是本卷后续扩展的统一记账格式。每个类型都规定输入、额外假设、输出和失败边界。

### 18.1 GraphToDirichletLimit

输入：
\[
(V_j,E_j,\mu_j,B_j,Q_j)_{j\ge0}.
\]
必需假设：

1. 每个 \(Q_j\) 是有限图上的非负二次型，并满足 Markov 收缩性质；
2. 存在共同 Hilbert 宿主空间 \(\mathcal H=L^2(X,\mu)\) 及明确的比较映射；有限维像外可将能量延拓为 \(+\infty\)；
3. 对候选极限 \(\mathcal Q\) 证明 Mosco liminf；
4. 对每个 \(u\in D(\mathcal Q)\) 给出强恢复序列；
5. 证明 \(\mathcal Q\) 闭、定义域稠密，并证明比较映射允许将 Markov 收缩性质传递到极限；
6. 若需从给定能量序列抽取收敛子列，另给相应的紧性条件；若声称离散特征值收敛，另给统一紧嵌入或 compact spectral convergence 条件。单个极限算子具有 compact resolvent 不能代替整列的紧性证明。

输出：
\[
\mathrm{DirichletFormLimit}(\mathcal Q,\mathcal H),
\]
并可进一步输出热半群或 resolvent 收敛。连续坐标、黎曼流形、物理时间和量子 Hamiltonian 均不包含在此输出中。

### 18.2 DirichletToGeometry

输入：

\[
(\mathcal X,d,\mu,\mathcal Q).
\]

弱输出需要证明 \(\mathcal X\) 是合适的 metric-measure space，并满足 RCD 或同类综合曲率条件。强输出若要成为光滑黎曼流形，还需增加：

\[
\text{finite-dimensional regularity},
\quad
\text{non-collapsing},
\quad
\text{injectivity/coordinate regularity},
\quad
\text{smooth convergence or reconstruction theorem}.
\]

输出可以是：

\[
\mathrm{RCDLimitSpace}
\]

或在更强假设下：

\[
\mathrm{SmoothRiemannianManifold}(M,g).
\]

不能推出：

\[
\mathrm{DirichletForm}
\not\Rightarrow
\mathrm{SmoothRiemannianManifold}
\]

除非额外 regularity 定理已经证明。

### 18.3 FIBEntropyFlow

输入是一个内部概率单纯形、可见约束、负熵 \(\mathcal V\) 和显式向量场 \(F\)。桥接结构必须给出余切到切空间的 Onsager 算子
\[
\mathsf M_p:T_p^*\Delta\to T_p\Delta
\]
并验证：

1. \(\mathsf M_p\) 对称半正定；
2. \(F(p)=-\mathsf M_pD\mathcal V(p)\)；
3. \(F\) 保持归一化和所声明的可见约束；
4. 向量场正向保持概率单纯形；存在唯一性和边界延拓按所使用的 ODE 定理单独证明；
5. 若引用 Maas 的线性 Markov 链定理，则另给 generator \(Q\)、正平稳分布 \(\pi\)、不可约性、detailed balance \(\pi_sQ_{st}=\pi_tQ_{ts}\) 及相应 transport metric。

输出是耗散恒等式
\[
\frac{d}{dt}\mathcal V(p(t))
=-D\mathcal V(p(t))[\mathsf M_{p(t)}D\mathcal V(p(t))]\le0.
\]
这里 \(D\mathcal V\) 是余切向量；没有在 Onsager 算子外再偷偷使用一套 Fisher gradient。

对 FIB 四角反应，17.2.2 中的显式算子满足这些有限代数条件，给出
\[
\dot p=\gamma(p_2p_5-p_0p_{25})d,\qquad
\dot\kappa=-\gamma\Delta.
\]
固定可见量时，\(r=1-Z>0\)，于是
\[
\kappa(t)=\kappa_*+e^{-\gamma rt}(\kappa(0)-\kappa_*).
\]
因为 \(\kappa_*\) 和初值都在合法闭纤维区间内，解是二者的凸组合，故对 \(t\ge0\) 保持合法性。这一证明不需要给五态完整空间伪造不可约线性 Markov generator。

不能由此决定 \(\gamma\) 的数值、物理质量、Hamiltonian 频率、量子能级或真实时空。

### 18.4 TriangleInflationCertificate

输入：
\[
p\in\Delta(\mathcal A\times\mathcal B\times\mathcal C),
\]
有限 inflation 图 \(N\) 和精确约束矩阵。首先证明 soundness：
\[
p\text{ triangle-local}
\Longrightarrow
\exists q\ge0,\ A_Nq=b_N(p).
\]
归一化、复制源对称性、可注入边缘和独立副本乘积边缘均编码在 \(A_N,b_N\) 中。

非相容性证书的字段为：
\[
(p,N,A_N,b_N,y).
\]
必需证明：
\[
A_N^{\mathsf T}y\ge0,\qquad
y^{\mathsf T}b_N(p)<0.
\]
矩阵、目标特征和证书向量使用精确有理数，或使用已经证明的区间误差界。然后 Farkas 矛盾直接给出：
\[
p\text{ is not triangle-local}.
\]
该证书不包含一个可行 \(q\)，因为其结论恰是可行 \(q\) 不存在。若另行找到可行 \(q\)，只能输出该级 inflation 必要条件；真正 compatibility 需要全层级完备性定理或显式独立源局部模型。

### 18.5 SpectralBridgeRH

输入：

\[
\mathcal H_{\mathrm{field}},
\quad
H_{\mathrm{field}},
\quad
D(H_{\mathrm{field}}),
\quad
\mathcal Z.
\]

必需假设：

1. \(H_{\mathrm{field}}\) 在显式 domain 上自伴；
2. 存在零点索引和重数保持的谱映射；
3. 零点没有被遗漏，也没有引入额外谱；
4. 存在 secular determinant、trace formula 或等价的完整谱身份；
5. 若使用 Cayley 形式，还需证明 resolvent/domain 条件；
6. 若使用正则化行列式，还需给出正则化方案、收敛域和 continuation。

输出：

\[
H_{\mathrm{field}}=H_{\mathrm{field}}^*,
\quad
\forall\rho\in\mathcal Z,\ 
-i(\rho-\tfrac12)\in\operatorname{Spec}(H_{\mathrm{field}})
\quad\Longrightarrow\quad
\mathrm{RH}.
\]

这里必须使用完整复零点的对应。对每个非平凡零点 \(\rho\)，例如构造非零
\[
\psi_\rho\in D(H_{\mathrm{field}}),\qquad
H_{\mathrm{field}}\psi_\rho=-i(\rho-\tfrac12)\psi_\rho
\]
即可证明所需谱包含。自伴性给出 \(-i(\rho-\tfrac12)\in\mathbb R\)，故 \(\operatorname{Re}\rho=\tfrac12\)。覆盖全部非平凡零点的谱包含已经足以推出 RH；重数匹配和全谱等价是更强的识别目标。

仅证明
\[
\operatorname{Spec}(H_{\mathrm{field}})\cong\{\operatorname{Im}\rho\}
\]
不能推出 RH，因为每个复数的虚部本来就是实数。若使用行列式版本，必须证明整个复变量恒等式
\[
\xi(\tfrac12+iz)=C(z)D_H(z),\qquad z\in\mathbb C,
\]
其中 \(C\) 无零，且 \(D_H\) 的全部零点来自自伴算子 \(H\) 的实谱。只在已知临界线零点上匹配数据不足以证明全局恒等式。

不能推出：

- 仅有数值零点拟合；
- 仅有形式 Hamiltonian；
- 仅有非自伴谱实现；
- 仅有 Cayley 系数有限截面酉性。

## 19. 最低一致性检查

把外部研究接入本卷后，每个新增命题必须通过以下检查：

1. **类型检查。** 输入对象的载体是否正确，例如逐节点 \((\Delta(\Sigma))^{V_j}\) 与全局单纯形不能混写。
2. **来源检查。** 每个符号是否属于 Primitive、Derived 或 Bridge 层。
3. **假设检查。** 外部定理的紧性、可逆性、曲率、边界或域条件是否逐项出现。
4. **输出检查。** 结论是 Dirichlet form、RCD space、梯度流、有限证书还是自伴算子，不能混用。
5. **反向性检查。** 一个推前存在性结果不能被反向使用为 lift 存在性。
6. **有限与无限检查。** 有限图谱结论不能未经 compact-resolvent 或本质谱分析推广到无限树。
7. **数值与精确检查。** 浮点可行性不能替代有理证书、形式证明或算子恒等式。
8. **物理语义检查。** 任何能量、质量、时间和量子化术语都必须绑定到新增的数学结构。

这些外部结果给出了从 Auric FIB 有限结构到 Dirichlet 极限、信息梯度流、triangle inflation 和 RH 自伴谱所需的额外假设；缺少相应假设时，统一场结论仍未得到。


---

## 20. 有限层相容载体、Fisher 曲率与 Dirichlet 极限

本节给出一个只使用有限维凸性、概率核、加权 Hilbert 空间和二次型的桥接定理。它把“逆极限中的静态记录”“FIB 隐藏曲率”和“图 Dirichlet 形式”放在同一个可检查的账本中。任何连续流形、物理能量、时间参数或量子化均不属于本节的原生输入。

### 20.1 有限层数据

对每个 \(j\in\mathbb N\)，给定有限顶点集 \(V_j\)、有限边集 \(E_j\)、顶点概率测度 \(\mu_j\) 和正边测度 \(\nu_j\)。定义

\[
\Pi_j^\delta
=
\left\{
p=(p_v)_{v\in V_j}:
p_v\in\Delta(\Sigma),\ 
p_{v,s}\ge\delta
\right\},
\qquad
0<\delta\le\frac15.
\]

这里 \(\delta\) 只用于保证 Fisher 曲率有限。若允许概率落在边界，应把 Fisher 泛函取为扩展值 \(+\infty\)，并另行证明下半连续性。

令

\[
\mathcal H_j=\mathbb R^{V_j},
\qquad
\mathcal E_j=\mathbb R^{E_j},
\]

并使用加权内积

\[
\langle f,g\rangle_{\mu_j}
=
\sum_{v\in V_j}\mu_j(v)f_vg_v,
\qquad
\langle \eta,\zeta\rangle_{\nu_j}
=
\sum_{e\in E_j}\nu_j(e)\eta_e\zeta_e.
\]

令 \(B_j:\mathcal E_j\to\mathcal H_j\) 为已有的边界算子，令

\[
G_j=B_j^*:\mathcal H_j\to\mathcal E_j.
\]

定义图 Dirichlet 二次型

\[
\mathcal Q_j(f)
=
\|G_jf\|_{\nu_j}^{\,2}
=
\langle f,B_jB_j^*f\rangle_{\mu_j}.
\]

这一步只使用有限图的边界矩阵和加权线性代数。

对每个 \(j\)，令 \(\mathsf C_j^R\) 是当前理论中有限载体的一个非空紧凸截面。例如可以取

\[
\mathsf C_j^R
=
\mathsf P_j^\delta
\times
\mathsf D_j^R
\times
\mathsf N_j^R
\times
\mathsf Z_j^R,
\]

其中 \(\mathsf P_j^\delta\subseteq\Pi_j^\delta\)，其余三个因子是现有图场、隐藏切向量和边流空间中的闭有界凸集。有限维性保证这些截面紧。这里 \(R\) 是数学截断参数，不被解释成物理半径或能量。

### 定义 20.1（相容有限层系统）

一个相容有限层系统包括连续仿射满射

\[
\rho_j:\mathsf C_{j+1}^R\longrightarrow\mathsf C_j^R.
\]

其概率分量记为

\[
q_j:\Pi_{j+1}^\delta\longrightarrow\Pi_j^\delta.
\]

若存在顶点映射 \(\pi_j:V_{j+1}\to V_j\) 和条件权重 \(a_j(w\mid v)\)，满足

\[
a_j(w\mid v)\ge0,
\qquad
\sum_{\pi_j(w)=v}a_j(w\mid v)=1,
\]

\[
\mu_{j+1}(w)
=
\mu_j(\pi_j(w))a_j(w\mid\pi_j(w)),
\]

则概率推前写成

\[
(q_jp)_v
=
\sum_{\pi_j(w)=v}
a_j(w\mid v)p_w.
\]

这保证每个粗层节点仍然携带一个单独归一化的五态概率律。它没有把 \((\Delta(\Sigma))^{V_j}\) 偷换成一个全局单纯形。

### 定理 20.2（紧相容载体的逆极限非空性）

设 \(\{\mathsf C_j^R,\rho_j\}_{j\ge0}\) 是相容有限层系统，且每个 \(\rho_j\) 连续、仿射、满射。则

\[
\mathsf C_\infty^R
=
\varprojlim_j(\mathsf C_j^R,\rho_j)
=
\left\{
(c_j)_j:
\rho_j(c_{j+1})=c_j
\right\}
\]

是非空紧凸集。

#### 证明

令

\[
\mathsf K=\prod_{j\ge0}\mathsf C_j^R.
\]

由于每个 \(\mathsf C_j^R\) 是紧空间，\(\mathsf K\) 是紧空间。对每个 \(m\) 定义

\[
F_m
=
\left\{
(c_j)_j\in\mathsf K:
\rho_j(c_{j+1})=c_j,\ 0\le j<m
\right\}.
\]

每个 \(F_m\) 是闭集。它非空的原因是从任意 \(c_m\in\mathsf C_m^R\) 开始，利用 \(\rho_{m-1},\ldots,\rho_0\) 的满射性逐层选取 \(c_{m-1},\ldots,c_0\)，再任意补充尚未约束的更高层坐标。更直接地，对任意有限指标集，只涉及有限条相容方程，而满射性保证这些方程有解。因此 \(\{F_m\}\) 具有有限交性质。由紧性，

\[
\bigcap_{m\ge0}F_m\neq\varnothing.
\]

该交集正是 \(\mathsf C_\infty^R\)。仿射映射的相容方程定义了凸集，所以逆极限也是凸的。证毕。

这个结论只保证截断载体的非空性。若要去掉 \(R\) 或 \(\delta\)，必须再证明截面族在相应极限中的紧性或下半连续性。

### 定义 20.3（层级 Fisher 曲率）

对 \(p\in\Pi_j^\delta\) 和质量守恒切向量 \(u=(u_{v,s})\)，定义

\[
\mathcal I_j(p;u)
=
\sum_{v\in V_j}\mu_j(v)
\sum_{s\in\Sigma}
\frac{u_{v,s}^{\,2}}{p_{v,s}}.
\]

当 \(u_{v,\cdot}=d\) 时，这就是每个局部 FIB seam 的加权总 Fisher 曲率。

### 定理 20.4（相容粗粒化下的 Fisher 单调性）

设 \(q_j\) 由定义 20.1 的条件权重给出，令

\[
p_j=q_jp_{j+1},
\qquad
u_j=Dq_j\,u_{j+1}.
\]

则

\[
\boxed{
\mathcal I_j(p_j;u_j)
\le
\mathcal I_{j+1}(p_{j+1};u_{j+1}).
}
\]

如果 \((p_j,u_j)_j\) 是相容族，则

\[
\mathcal I_0\le\mathcal I_1\le\mathcal I_2\le\cdots.
\]

#### 证明

固定 \(v\in V_j\) 和 \(s\in\Sigma\)。记

\[
p_{j,v,s}
=
\sum_{\pi_j(w)=v}a_j(w\mid v)p_{j+1,w,s},
\]

\[
u_{j,v,s}
=
\sum_{\pi_j(w)=v}a_j(w\mid v)u_{j+1,w,s}.
\]

加权 Cauchy–Schwarz 不等式给出

\[
\frac{u_{j,v,s}^{\,2}}{p_{j,v,s}}
\le
\sum_{\pi_j(w)=v}
a_j(w\mid v)
\frac{u_{j+1,w,s}^{\,2}}{p_{j+1,w,s}}.
\]

乘以 \(\mu_j(v)\)，对 \(v,s\) 求和，并使用

\[
\mu_j(v)a_j(w\mid v)=\mu_{j+1}(w),
\]

得到

\[
\mathcal I_j(p_j;u_j)
\le
\mathcal I_{j+1}(p_{j+1};u_{j+1}).
\]

证毕。

特别地，如果每层的隐藏方向由

\[
u_{j,v,\cdot}=d
\]

给出，并且 \(q_jd=d\)，则 FIB seam 曲率沿细化方向单调不减。等号当且仅当每个状态 \(s\) 的 score

\[
\frac{u_{j+1,w,s}}{p_{j+1,w,s}}
\]

在每个聚合纤维 \(\pi_j^{-1}(v)\) 上几乎处处为常数。这是 Cauchy–Schwarz 等号条件的直接展开。

### 定义 20.5（梯度交换的图压缩）

令

\[
R_j:\mathcal H_{j+1}\longrightarrow\mathcal H_j
\]

是顶点场的层间压缩，令

\[
S_j:\mathcal E_{j+1}\longrightarrow\mathcal E_j
\]

是边梯度的层间压缩。称 \((R_j,S_j)\) 为 Dirichlet 相容，如果

\[
G_jR_j=S_jG_{j+1},
\qquad
\|S_j\|_{\nu_{j+1}\to\nu_j}\le1.
\]

这一定义直接记录了图梯度在层间投影下如何交换。仅有边界散度交换

\[
B_jS_j=R_jB_{j+1}
\]

还不足以推出 Dirichlet 能量单调性，因为二次型使用的是 \(B_j^*=G_j\)。

### 定理 20.6（Dirichlet 能量的粗粒化收缩）

若 \((R_j,S_j)\) Dirichlet 相容，则对所有 \(f\in\mathcal H_{j+1}\)，

\[
\boxed{
\mathcal Q_j(R_jf)
\le
\mathcal Q_{j+1}(f).
}
\]

#### 证明

由梯度交换条件，

\[
\mathcal Q_j(R_jf)
=
\|G_jR_jf\|_{\nu_j}^{\,2}
=
\|S_jG_{j+1}f\|_{\nu_j}^{\,2}.
\]

由于 \(\|S_j\|\le1\)，

\[
\|S_jG_{j+1}f\|_{\nu_j}^{\,2}
\le
\|G_{j+1}f\|_{\nu_{j+1}}^{\,2}
=
\mathcal Q_{j+1}(f).
\]

证毕。

因此，对任意相容场族 \(f_j=R_jf_{j+1}\)，有

\[
\mathcal Q_0(f_0)
\le
\mathcal Q_1(f_1)
\le
\mathcal Q_2(f_2)
\le\cdots.
\]

这是一个纯图论和 Hilbert 空间结论。它说明图层越细，能够承载的 Dirichlet 能量不减。它没有指定能量的物理单位。

### 推论 20.7（谱隙在显式可见子空间上传递）

设 \(U_{j+1}\subseteq\mathcal H_{j+1}\) 是一个子空间，\(R_jU_{j+1}\) 位于粗层的零均值子空间，并且存在 \(c_j>0\) 使

\[
\|R_jf\|_{\mu_j}
\ge
c_j\|f\|_{\mu_{j+1}},
\qquad
f\in U_{j+1}.
\]

如果粗层满足

\[
\mathcal Q_j(g)
\ge
\lambda_j\|g\|_{\mu_j}^{\,2},
\qquad
g\in R_jU_{j+1},
\]

则细层满足

\[
\mathcal Q_{j+1}(f)
\ge
c_j^2\lambda_j\|f\|_{\mu_{j+1}}^{\,2},
\qquad
f\in U_{j+1}.
\]

#### 证明

由定理 20.6 和粗层 Poincaré 不等式，

\[
\mathcal Q_{j+1}(f)
\ge
\mathcal Q_j(R_jf)
\ge
\lambda_j\|R_jf\|_{\mu_j}^{\,2}
\ge
c_j^2\lambda_j\|f\|_{\mu_{j+1}}^{\,2}.
\]

证毕。

该推论只对 \(R_j\) 不丢失的指定子空间成立。对被粗粒化消除的高频方向，不能从粗层谱隙反推细层谱隙。

### 20.2 逆极限与 Mosco 极限的最小桥

令 \(\mathcal H\) 是一个共同 Hilbert 宿主空间，并给出等距嵌入

\[
\iota_j:\mathcal H_j\hookrightarrow\mathcal H.
\]

将有限层二次型延拓为 \(\mathcal H\) 上的扩展泛函

\[
\overline{\mathcal Q}_j(u)
=
\begin{cases}
\mathcal Q_j(f),&u=\iota_jf,\\
+\infty,&u\notin\iota_j\mathcal H_j.
\end{cases}
\]

图二次型的 Dirichlet 极限依赖以下三条条件：

\[
\tag{M1}
u_j\rightharpoonup u
\Longrightarrow
\mathcal Q(u)
\le
\liminf_{j\to\infty}\overline{\mathcal Q}_j(u_j),
\]

\[
\tag{M2}
\forall u\in D(\mathcal Q),\ \exists u_j\to u\text{ 强收敛},
\qquad
\limsup_{j\to\infty}\overline{\mathcal Q}_j(u_j)
\le
\mathcal Q(u),
\]

\[
\tag{M3}
\text{有限能量子水平集具有共同宿主空间中的相对紧性}.
\]

(M1) 是 Mosco 下极限，(M2) 是恢复序列，(M3) 是从有限层抽取极限场时所需的紧性。若只要定义闭极限二次型，(M1) 和 (M2) 是核心条件。若还要得到相容静态场、最小值收敛或特征函数收敛，必须增加 (M3) 或等价的 compactness 条件。

### 定理 20.8（相容恢复序列的能量识别）

假设 \(\overline{\mathcal Q}_j\) 满足 (M1) 和 (M2)。若相容场族 \(f_j\) 满足

\[
\iota_jf_j\longrightarrow f
\quad\text{强收敛},
\]

并且它本身是一个恢复序列，即

\[
\limsup_j\overline{\mathcal Q}_j(\iota_jf_j)
\le
\mathcal Q(f),
\]

则

\[
\lim_j\mathcal Q_j(f_j)
=
\mathcal Q(f).
\]

#### 证明

由强收敛推出弱收敛，再由 (M1) 得到

\[
\mathcal Q(f)
\le
\liminf_j\mathcal Q_j(f_j).
\]

由恢复条件得到

\[
\limsup_j\mathcal Q_j(f_j)
\le
\mathcal Q(f).
\]

两式合并即得极限存在且等于 \(\mathcal Q(f)\)。证毕。

这个定理明确指出：逆极限相容性本身不等于 Dirichlet 能量收敛。还必须证明相容族在共同宿主空间中是恢复序列。

### 定理 20.9（严格凸静态截面的极限稳定性）

在定理 20.8 的假设下，令 \(\ell_j\in\mathcal H_j^*\) 是连续线性泛函，并假设其经 \(\iota_j\) 传到共同宿主空间后收敛为 \(\ell\)。定义

\[
\mathcal F_j(f)
=
\frac12\mathcal Q_j(f)-\ell_j(f),
\qquad
\mathcal F(f)
=
\frac12\mathcal Q(f)-\ell(f).
\]

若：

1. \(\mathcal F_j\) 的有限能量子水平集在 \(\mathcal H\) 中相对紧；
2. \(\mathcal Q\) 在其定义域上严格凸；
3. 每个 \(\mathcal F_j\) 有最小元 \(f_j\)；

则 \(f_j\) 的任意弱聚点都是 \(\mathcal F\) 的唯一最小元。若 (M3) 给出强预紧性，则

\[
\iota_jf_j\longrightarrow f_*
\]

强收敛，并且

\[
\mathcal F_j(f_j)\longrightarrow\mathcal F(f_*).
\]

#### 证明

取任意弱聚点 \(f\)。由子水平紧性和 (M1)，对最小元序列有

\[
\mathcal Q(f)
\le
\liminf_j\mathcal Q_j(f_j).
\]

线性项在弱收敛下连续，因此

\[
\mathcal F(f)
\le
\liminf_j\mathcal F_j(f_j).
\]

对任意 \(g\in D(\mathcal Q)\)，由 (M2) 取恢复序列 \(g_j\)。最小性给出

\[
\mathcal F_j(f_j)
\le
\mathcal F_j(g_j).
\]

取上极限得到

\[
\limsup_j\mathcal F_j(f_j)
\le
\mathcal F(g).
\]

合并后得到

\[
\mathcal F(f)\le\mathcal F(g)
\]

对所有 \(g\in D(\mathcal Q)\) 成立。因此 \(f\) 是极小元。严格凸性保证极小元唯一，记为 \(f_*\)。所有聚点相同，结合 (M3) 即得强收敛。能量收敛由定理 20.8 和最小性得到。证毕。

### 20.3 这组定理在现有架构中的准确含义

上述结果允许我们严格声明：

\[
\boxed{
\begin{aligned}
&\text{有限五态概率载体的相容逆极限可非空；}\\
&\text{Fisher seam 曲率在粗粒化下满足数据处理单调性；}\\
&\text{图 Dirichlet 二次型在梯度交换且边压缩为收缩时单调下降；}\\
&\text{相容逆极限只有在共同宿主空间的 Mosco/恢复条件下才产生 Dirichlet 极限；}\\
&\text{严格凸有限层静态最小元在 equicoercive 条件下收敛到唯一极限最小元。}
\end{aligned}
}
\]

这些结论仍然没有引入：

\[
\text{物理质量},
\quad
\text{时间},
\quad
\text{Hamiltonian},
\quad
\text{量子态},
\quad
\text{光滑黎曼流形},
\quad
\text{RH 自伴算子}.
\]

若要继续向黎曼几何推进，必须在定理 20.8 之后额外证明极限二次型来自某个度量测度空间。若要继续向光滑流形推进，还要补充维数、非塌缩、Ricci 下界、注入半径和光滑重构条件。若要继续向物理解释推进，则必须另建桥接结构，不能由本节反向补定义。



### 定理 20.10（Fisher–Dirichlet 的纯数学联合稳定量）

在定理 20.4 和定理 20.6 的假设下，取任意 \(\tau\ge0\)，定义

\[
\mathcal S_j^{(\tau)}(f,p;u)
=
\mathcal Q_j(f)
+
\tau\,\mathcal I_j(p;u).
\]

若

\[
f_j=R_jf_{j+1},
\qquad
p_j=q_jp_{j+1},
\qquad
u_j=Dq_j\,u_{j+1},
\]

则

\[
\boxed{
\mathcal S_j^{(\tau)}(f_j,p_j;u_j)
\le
\mathcal S_{j+1}^{(\tau)}(f_{j+1},p_{j+1};u_{j+1}).
}
\]

#### 证明

由定理 20.4，

\[
\mathcal I_j(p_j;u_j)
\le
\mathcal I_{j+1}(p_{j+1};u_{j+1}),
\]

由定理 20.6，

\[
\mathcal Q_j(f_j)
\le
\mathcal Q_{j+1}(f_{j+1}).
\]

将第二个不等式乘以 \(1\)，将第一个不等式乘以 \(\tau\ge0\)，相加即得结论。证毕。

因此，一个纯数学的联合稳定量可以定义为

\[
\mathcal S_\infty^{(\tau)}
=
\sup_j
\mathcal S_j^{(\tau)}
\in[0,+\infty].
\]

若该上确界有限，则沿任意相容族有极限

\[
\lim_{j\to\infty}
\mathcal S_j^{(\tau)}
=
\mathcal S_\infty^{(\tau)}.
\]

这里 \(\tau\) 只是两个二次型之间的数学权重。只有在额外指定单位和动力学结构后，才可赋予它物理解释。

### 推论 20.11（联合有限层稳定证书）

假设存在 \(\lambda_j^{\mathrm{graph}},\lambda_j^{\mathrm{FIB}}\ge0\)，使得在指定子空间上

\[
\mathcal Q_j(f)
\ge
\lambda_j^{\mathrm{graph}}\|f\|_{\mu_j}^{\,2},
\]

\[
\mathcal I_j(p;u)
\ge
\lambda_j^{\mathrm{FIB}}\|u\|_{\mu_j,\mathrm{E}}^{\,2},
\]

其中 \(\|\cdot\|_{\mu_j,\mathrm E}\) 是节点和状态上的普通加权 Euclidean 范数。则

\[
\mathcal S_j^{(\tau)}(f,p;u)
\ge
\min\left\{
\lambda_j^{\mathrm{graph}},
\tau\lambda_j^{\mathrm{FIB}}
\right\}
\left(
\|f\|_{\mu_j}^{\,2}
+
\|u\|_{\mu_j,\mathrm E}^{\,2}
\right)
\]

对 \(\tau>0\) 成立。

#### 证明

分别使用两个下界：

\[
\mathcal S_j^{(\tau)}
\ge
\lambda_j^{\mathrm{graph}}\|f\|^2
+
\tau\lambda_j^{\mathrm{FIB}}\|u\|^2.
\]

右侧至少为最小系数乘以两个范数平方之和。证毕。

该推论给出一个不依赖物理解释的稳定性判据。若图 sector 和 FIB sector 的有限层下界在相容细化中保持正，则其直和载体具有统一的正稳定下界。若某个 sector 的下界趋于零，必须记录为该 sector 的数学软化或退化，不能用另一个 sector 的正下界掩盖它。



---

## 21. Fibonacci 支持层的具体相容投影

本节把第 20 节的抽象相容系统具体化到已有的 Fibonacci 独立支持层。这里的状态是支持集合，五态 FIB 是 \(n=3\) 的局部实例：

\[
\Sigma_3
=
\{\varnothing,\{1\},\{2\},\{3\},\{1,3\}\}
\longleftrightarrow
\{0,2,3,5,25\}.
\]

### 定义 21.1（删除投影）

令

\[
\Sigma_n
=
\{I\subseteq[n]:
i\in I\Longrightarrow i+1\notin I\}.
\]

定义

\[
\delta_n:\Sigma_{n+1}\longrightarrow\Sigma_n,
\qquad
\delta_n(I)=I\cap[n].
\]

对概率律定义线性推前

\[
D_n:\Delta(\Sigma_{n+1})\longrightarrow\Delta(\Sigma_n),
\]

\[
(D_np)(J)
=
\sum_{\substack{I\in\Sigma_{n+1}\\\delta_n(I)=J}}p(I).
\]

对有符号质量和切向量使用同一个线性映射 \(D_n\)。

### 定理 21.2（Fibonacci 删除投影的观察交换与隐藏核满射）

令

\[
T_n
=
\left\{
v\in\mathbb R^{\Sigma_n}:
\sum_{I\in\Sigma_n}v_I=0
\right\},
\]

\[
(A_nv)_i
=
\sum_{I\ni i}v_I,
\qquad
i\in[n].
\]

令 \(\operatorname{pr}_n:\mathbb R^{n+1}\to\mathbb R^n\) 删除最后一个坐标。则：

1. \(\delta_n\) 和 \(D_n\) 都是满射；
2. 对所有 \(v\in\mathbb R^{\Sigma_{n+1}}\)，
   \[
   A_nD_nv
   =
   \operatorname{pr}_n A_{n+1}v;
   \]
3. \(D_n(T_{n+1})\subseteq T_n\)，并且限制映射
   \[
   D_n:
   \ker(A_{n+1}|_{T_{n+1}})
   \longrightarrow
   \ker(A_n|_{T_n})
   \]
   是满射；
4. 其核维数为
   \[
   \dim\ker\left(
   D_n:
   \ker(A_{n+1}|_{T_{n+1}})
   \to
   \ker(A_n|_{T_n})
   \right)
   =
   F_{n+1}-1.
   \]

#### 证明

对任意 \(J\in\Sigma_n\)，集合 \(J\) 本身看作 \([n+1]\) 的子集，满足

\[
\delta_n(J)=J.
\]

所以 \(\delta_n\) 满射，\(D_n\) 将对应的 Dirac 质量推到 \(J\)，因而也是概率单纯形的满射。

对 \(i\le n\)，有

\[
\begin{aligned}
(A_nD_nv)_i
&=
\sum_{\substack{J\in\Sigma_n\\i\in J}}
\sum_{\delta_n(I)=J}v_I\\
&=
\sum_{\substack{I\in\Sigma_{n+1}\\i\in I}}v_I\\
&=
(A_{n+1}v)_i.
\end{aligned}
\]

这正是

\[
A_nD_n=\operatorname{pr}_nA_{n+1}.
\]

由于 \(D_n\) 的各列和为一，质量零空间被保持。若

\[
w\in\ker(A_n|_{T_n}),
\]

定义 \(\widetilde w\in\mathbb R^{\Sigma_{n+1}}\) 为

\[
\widetilde w_J=w_J
\quad(J\in\Sigma_n),
\qquad
\widetilde w_I=0
\quad(I\ni n+1).
\]

则

\[
D_n\widetilde w=w,
\qquad
\sum_I\widetilde w_I=0.
\]

由观察交换式，

\[
A_{n+1}\widetilde w
=
\bigl(A_nw,0\bigr)
=
0.
\]

故限制映射满射。使用已有公式

\[
h_n
=
\dim\ker(A_n|_{T_n})
=
F_{n+2}-n-1,
\]

有

\[
\begin{aligned}
\dim\ker D_n
&=
h_{n+1}-h_n\\
&=
(F_{n+3}-(n+1)-1)-(F_{n+2}-n-1)\\
&=
F_{n+1}-1.
\end{aligned}
\]

证毕。

这个结果把“新一层的隐藏信息”精确化为：

\[
\boxed{
\text{每增加一个 Fibonacci 支持位，删除投影不可见的新方向数为 }F_{n+1}-1.
}
\]

它是状态空间线性代数结论，不涉及信息论或物理解释。

### 定义 21.3（Fibonacci 层 Fisher 曲率）

在内部单纯形

\[
\Delta(\Sigma_n)^\circ
=
\{p_I>0:\sum_Ip_I=1\}
\]

上，对 \(u\in T_p\Delta(\Sigma_n)\) 定义

\[
\mathcal I_n(p;u)
=
\sum_{I\in\Sigma_n}\frac{u_I^2}{p_I}.
\]

### 定理 21.4（Fibonacci 删除投影的 Fisher 数据处理）

对任意

\[
p\in\Delta(\Sigma_{n+1})^\circ,
\qquad
u\in T_p\Delta(\Sigma_{n+1}),
\]

有

\[
\boxed{
\mathcal I_n(D_np;D_nu)
\le
\mathcal I_{n+1}(p;u).
}
\]

等号当且仅当对每个 \(J\in\Sigma_n\)，以及所有满足 \(\delta_n(I)=J\) 且 \(p_I>0\) 的 \(I\)，比值

\[
\frac{u_I}{p_I}
\]

相同。

#### 证明

对每个 \(J\in\Sigma_n\)，记

\[
P_J=(D_np)(J)
=
\sum_{\delta_n(I)=J}p_I,
\qquad
U_J=(D_nu)(J)
=
\sum_{\delta_n(I)=J}u_I.
\]

由加权 Cauchy–Schwarz，

\[
\frac{U_J^2}{P_J}
\le
\sum_{\delta_n(I)=J}\frac{u_I^2}{p_I}.
\]

对 \(J\) 求和得到不等式。Cauchy–Schwarz 的等号条件正是 \(u_I/p_I\) 在每个纤维上为常数。证毕。

### 推论 21.5（Fibonacci 隐藏层的曲率和维数分离）

令

\[
K_n=\ker(A_n|_{T_n}).
\]

则

\[
D_nK_{n+1}=K_n,
\qquad
\dim K_{n+1}-\dim K_n=F_{n+1}-1.
\]

对每个 \(u_{n+1}\in K_{n+1}\) 定义 \(u_n=D_nu_{n+1}\)，则

\[
\mathcal I_n(p_n;u_n)
\le
\mathcal I_{n+1}(p_{n+1};u_{n+1}).
\]

若 \(u_{n+1}\in\ker D_n\)，则该新方向在第 \(n\) 层的观察和 Fisher 变化都为零：

\[
A_nD_nu_{n+1}=0,
\qquad
D_nu_{n+1}=0.
\]

因此每个新增维度 \(F_{n+1}-1\) 都是删除投影不可见的方向。它们是否在更细层有有限或发散 Fisher 曲率，取决于该方向对应的概率质量，不能由维数公式单独决定。

### 21.1 与图 Dirichlet 形式的接口

Fibonacci cube \(\Gamma_n\) 的顶点为 \(\Sigma_n\)。删除映射 \(\delta_n\) 是图的顶点映射，但它把多条细边压到同一个粗边或粗顶点。为了得到第 20 节的 Dirichlet 收缩定理，不能只使用顶点映射。必须显式构造边梯度压缩

\[
S_n:\mathcal E_{n+1}\to\mathcal E_n
\]

和加权顶点压缩

\[
R_n:\mathcal H_{n+1}\to\mathcal H_n
\]

使

\[
G_nR_n=S_nG_{n+1},
\qquad
\|S_n\|\le1.
\]

一旦这两个条件成立，定理 20.6 给出

\[
\mathcal Q_n(R_nf)
\le
\mathcal Q_{n+1}(f).
\]

因此 Fibonacci 删除投影目前已经完全解决概率观察和隐藏核层面的相容性，Dirichlet 层面还需要逐边定义 \(S_n\)。不能把 \(D_n\) 自动当作图 Dirichlet 商映射。

---

## 22. 边界到 seam 商、最小提升与循环可观测性

本节把第 6 节的五边短正合列和第 7 节的 Fibonacci 维数公式提升为一个一般有限图命题。对象仍然是有限维实向量空间、概率质量零空间、图边界和线性读出。没有引入时间、物理能量或 Hamiltonian。

### 定义 22.1（边界、可见读出与 seam 空间）

令 \(\Gamma=(V,E)\) 是有限连通图。取一个参考定向，并令

\[
B:\mathbb R^E\longrightarrow H:=\mathbb R^V
\]

为有向边界算子，约定每条边列为终点单位向量减起点单位向量。令

\[
T=\left\{v\in H:\sum_{x\in V}v_x=0\right\}.
\]

令

\[
A:H\longrightarrow Y
\]

为任意有限维线性可见读出，并定义

\[
K=\ker B,\qquad
S=\ker(A|_T),\qquad
C=\ker(AB).
\]

其中 \(K\) 是纯循环空间，\(S\) 是状态边界在可见读出下的隐藏 seam 空间，\(C\) 是产生零一步可见边界的边链空间。

### 定理 22.2（边界到 seam 的商同构）

由于 \(\Gamma\) 连通，有

\[
\operatorname{im}B=T.
\]

边界算子在 \(C\) 上下降为一个规范同构

\[
\overline B:
C/K
\longrightarrow
S,
\qquad
[f]\longmapsto Bf.
\]

因此存在短正合列

\[
\boxed{
0\longrightarrow K
\longrightarrow C
\xrightarrow{\ B\ }
S
\longrightarrow0
}
\]

以及自然维数公式

\[
\dim C=\dim K+\dim S.
\]

对于 Fibonacci cube \(\Gamma_n\)，这给出

\[
\dim C_n=c_n+h_n,
\qquad
\dim(C_n/K_n)=h_n.
\]

#### 证明

有限连通图的 incidence 边界满足

\[
\operatorname{im}B=T.
\]

这是因为每条边界都具有总质量零，而从一个固定根到任意顶点的路径边界给出 \(\mathbf e_v-\mathbf e_{\mathrm{root}}\)，这些差向量生成 \(T\)。

若 \(f\in C\)，则 \(ABf=0\)，且 \(Bf\in\operatorname{im}B=T\)，故

\[
Bf\in\ker(A|_T)=S.
\]

于是 \(B\) 从 \(C\) 映射到 \(S\)。若 \(f'=f+k\)，其中 \(k\in K\)，则 \(Bf'=Bf\)，所以该映射对商类 \([f]\) 良定义。

给定 \(s\in S\)，由 \(\operatorname{im}B=T\) 可取 \(f\in\mathbb R^E\) 使 \(Bf=s\)。于是 \(ABf=As=0\)，所以 \(f\in C\)，说明 \(\overline B\) 满射。

若 \(\overline B([f])=0\)，则 \(Bf=0\)，故 \(f\in K\)，即 \([f]=0\)。因此 \(\overline B\) 单射。短正合列及维数公式随即成立。证毕。

### 推论 22.3（同一 seam 的全部边提升）

给定 \(s\in S\)，所有满足

\[
Bf=s
\]

的边链恰为一个仿射空间

\[
B^{-1}(s)=f_0+K,
\]

其中 \(f_0\) 是任意一个满足 \(Bf_0=s\) 的提升。因此：

\[
\boxed{
\text{同一个静态 seam 的边界表示，恰好相差一个纯循环。}
}
\]

这一区分了两个隐藏来源：

\[
\text{静态 seam}
\quad\leftrightarrow\quad
C/K,
\]

\[
\text{动态循环}
\quad\leftrightarrow\quad
K.
\]

在一般图上，\(C\) 同时包含两者；只有取商以后才得到与状态 seam 一一对应的边界类。

### 定理 22.4（加权最小边界提升与诱导 seam 度量）

令 \(W\in\mathbb R^{E\times E}\) 对称正定，并在边链上定义

\[
\langle f,g\rangle_{W^{-1}}
=
f^{\mathsf T}W^{-1}g.
\]

记

\[
L_W=BWB^{\mathsf T}.
\]

对每个 \(s\in S\)，定义

\[
\mathsf L_W(s)
=
WB^{\mathsf T}L_W^\dagger s,
\]

其中 \(L_W^\dagger\) 是 Moore–Penrose 伪逆。则：

1. \(B\mathsf L_W(s)=s\)；
2. \(\mathsf L_W(s)\) 是约束 \(Bf=s\) 下唯一最小化
   \[
   \|f\|_{W^{-1}}^2=f^{\mathsf T}W^{-1}f
   \]
   的边链；
3. \(\mathsf L_W(s)\) 与 \(K\) 在 \(\langle\cdot,\cdot\rangle_{W^{-1}}\) 下正交；
4. 任意边界提升唯一写成
   \[
   f=\mathsf L_W(s)+k,\qquad k\in K;
   \]
5. \(S\) 上的二次型
   \[
   g_W(s,t)
   =
   \left\langle
   \mathsf L_W(s),\mathsf L_W(t)
   \right\rangle_{W^{-1}}
   =
   s^{\mathsf T}L_W^\dagger t
   \]
   是正定的。

#### 证明

对于连通图，\(\ker B^{\mathsf T}\) 是常数向量空间，故

\[
\ker L_W=\ker B^{\mathsf T},
\qquad
\operatorname{im}L_W=\operatorname{im}B=T.
\]

由于 \(s\in S\subseteq T\)，有

\[
L_WL_W^\dagger s=s,
\]

从而

\[
B\mathsf L_W(s)
=
BWB^{\mathsf T}L_W^\dagger s
=
s.
\]

若 \(k\in K\)，则

\[
\left\langle
\mathsf L_W(s),k
\right\rangle_{W^{-1}}
=
s^{\mathsf T}(L_W^\dagger)^{\mathsf T}B k
=
0.
\]

每个满足 \(Bf=s\) 的 \(f\) 与 \(\mathsf L_W(s)\) 之差属于 \(K\)，故正交分解给出唯一最小范数提升。

最后，

\[
\begin{aligned}
\left\langle
\mathsf L_W(s),\mathsf L_W(t)
\right\rangle_{W^{-1}}
&=
s^{\mathsf T}L_W^\dagger
BWB^{\mathsf T}
L_W^\dagger t\\
&=
s^{\mathsf T}L_W^\dagger t,
\end{aligned}
\]

因为 \(s,t\in\operatorname{im}L_W\)。若 \(s\neq0\)，则 \(\mathsf L_W(s)\neq0\)，故

\[
g_W(s,s)=\|\mathsf L_W(s)\|_{W^{-1}}^2>0.
\]

证毕。

### 推论 22.5（循环规范的精确含义）

\(\mathsf L_W\) 是商空间 \(C/K\cong S\) 的唯一 \(W^{-1}\)-正交代表。因而：

\[
\boxed{
\text{最小提升规范只消除循环自由度，}
\quad
\text{它不消除 seam 自由度。}
}
\]

如果在同一 \(s\) 上选取另一条边链 \(f=\mathsf L_W(s)+k\)，则

\[
\|f\|_{W^{-1}}^2
=
g_W(s,s)+\|k\|_{W^{-1}}^2.
\]

这给出一个完全有限维的“边界成本分解”：第一项是 seam 的规范代表成本，第二项是额外循环活动成本。

### 定理 22.6（边读出何时只依赖 seam）

令

\[
R:C\longrightarrow Z
\]

是任意线性边读出。则以下两项等价：

1. 存在唯一线性映射
   \[
   \overline R:S\longrightarrow Z
   \]
   使
   \[
   R=\overline R\circ B;
   \]
2. \(R\) 湮灭所有循环：
   \[
   R|_K=0.
   \]

在此情况下，

\[
\overline R(s)=R(\mathsf L_W(s))
\]

与权重 \(W\) 无关。若 \(R|_K\neq0\)，则 \(R\) 可以区分同一 seam \(s\) 的不同边界提升。

#### 证明

若 \(R=\overline R\circ B\)，则对 \(k\in K\)

\[
R(k)=\overline R(Bk)=0.
\]

反过来，若 \(R|_K=0\)，对 \(s\in S\) 选取任意 \(f\in C\) 满足 \(Bf=s\)，定义

\[
\overline R(s)=R(f).
\]

若 \(f'\) 是另一个提升，则 \(f'-f\in K\)，所以

\[
R(f')-R(f)=R(f'-f)=0.
\]

故 \(\overline R\) 良定义、线性且满足 \(R=\overline R\circ B\)。唯一性由 \(B(C)=S\) 得到。特别地，最小提升可用于计算该映射，但结果不依赖所选 \(W\)。若 \(R|_K\neq0\)，取 \(k\in K\) 使 \(R(k)\neq0\)，则 \(f\) 与 \(f+k\) 具有相同 seam 而读出不同。证毕。

### 定义 22.7（边链未来观测核与折扣 Gramian）

给定任意有限维边更新

\[
U:\mathbb R^E\longrightarrow\mathbb R^E,
\]

令一步状态可见读出为

\[
O=AB.
\]

定义未来观测核

\[
\mathcal N_\infty^E
=
\bigcap_{m\ge0}\ker(OU^m).
\]

若 \(Y\) 带有 Euclidean 内积，并且 \(0<\beta<1\)，定义折扣 Gramian

\[
\mathcal G_\beta
=
\sum_{m=0}^{\infty}
\beta^m
(U^{\mathsf T})^mO^{\mathsf T}OU^m.
\]

有限维中该级数在 \(\|U\|\sqrt\beta<1\) 时按算子范数收敛；若 \(\beta\|U\|^2\ge1\)，可改用有限窗口 Gramian

\[
\mathcal G_{\beta,N}
=
\sum_{m=0}^{N}
\beta^m
(U^{\mathsf T})^mO^{\mathsf T}OU^m.
\]

### 定理 22.8（循环到 seam 的观测转化）

令 \(K=\ker B\)。

1. 若
   \[
   U(K)\subseteq K,
   \]
   则
   \[
   K\subseteq\mathcal N_\infty^E.
   \]
   所有纯循环在任意未来窗口都保持不可见。

2. 若存在
   \[
   k\in K,\quad m\ge0
   \]
   使
   \[
   ABU^m k\neq0,
   \]
   则 \(k\notin\mathcal N_\infty^E\)，即该循环在第 \(m\) 个未来窗口被转化为可见边界。

3. 对任意 \(f\in\mathbb R^E\)，在 Gramian 收敛条件下有
   \[
   f^{\mathsf T}\mathcal G_\beta f
   =
   \sum_{m\ge0}
   \beta^m
   \|ABU^m f\|^2.
   \]
   特别地，
   \[
   f\in\ker\mathcal G_\beta
   \iff
   f\in\mathcal N_\infty^E.
   \]

#### 证明

若 \(U(K)\subseteq K\)，则 \(U^m k\in K=\ker B\) 对所有 \(m\) 成立，因此

\[
ABU^m k=0.
\]

故 \(k\in\mathcal N_\infty^E\)。

第二项是定义的直接展开。

对于第三项，逐项计算：

\[
\begin{aligned}
f^{\mathsf T}\mathcal G_\beta f
&=
\sum_{m\ge0}
\beta^m
f^{\mathsf T}(U^{\mathsf T})^mO^{\mathsf T}OU^m f\\
&=
\sum_{m\ge0}
\beta^m
\|OU^m f\|^2.
\end{aligned}
\]

每项非负，因此总和为零当且仅当每一项都为零，即

\[
OU^m f=0
\]

对所有 \(m\) 成立。证毕。

### 推论 22.9（Fibonacci 图上的三种维数）

对 Fibonacci cube \(\Gamma_n\)，令

\[
K_n=\ker B_n,\qquad
S_n=\ker(A_n|_{T_n}),\qquad
C_n=\ker(A_nB_n).
\]

则：

\[
\dim K_n=c_n
=
\sum_{k\ge2}(k-1)N_{n,k},
\]

\[
\dim S_n=h_n
=
\sum_{k\ge2}N_{n,k},
\]

\[
\dim C_n=c_n+h_n
=
\sum_{k\ge2}kN_{n,k}.
\]

因此：

\[
\boxed{
\begin{aligned}
\text{纯循环维数} &=\sum_{k\ge2}(k-1)N_{n,k},\\
\text{静态 seam 维数} &=\sum_{k\ge2}N_{n,k},\\
\text{零一步可见边链维数} &=\sum_{k\ge2}kN_{n,k}.
\end{aligned}
}
\]

当 \(n\ge5\) 时，

\[
\dim K_n-\dim S_n
=
\sum_{k\ge3}(k-2)N_{n,k}>0.
\]

所以从 \(n=5\) 开始，动态循环自由度严格多于静态 seam 自由度。即使静态观察核维数固定，边链仍然有额外循环活动无法由边界读出恢复。

#### 证明

前两项是既有 Fibonacci 计数公式。由定理 22.2，

\[
\dim C_n=\dim K_n+\dim S_n.
\]

将两项有限和相加，得到

\[
\dim C_n
=
\sum_{k\ge2}
\bigl((k-1)+1\bigr)N_{n,k}
=
\sum_{k\ge2}kN_{n,k}.
\]

差值式和严格不等式由 \(N_{n,3}>0\) 在 \(n\ge5\) 时成立得到。证毕。

### 22.10 结论边界

定理 22.2 和定理 22.4 是有限维线性代数结论。定理 22.6 是商空间的因子化判据。定理 22.8 只使用给定的线性边更新 \(U\) 和读出 \(AB\)。这些结果没有定义：

\[
\text{物理时间},\quad
\text{能量},\quad
\text{概率转移率},\quad
\text{连续流形},\quad
\text{量子 Hamiltonian}.
\]

若要令 \(U\) 来自 Markov 流或边界输运，还要另给非负性、归一化、可达性和非爆炸条件。若要把 \(g_W\) 解释成物理能量，必须另给单位、动力学和作用量。若要从 \(\mathcal G_\beta\) 推出有限记忆或无限未来完备性，还需给出实际记录空间和相容的历史核。



---

### 定理 22.11（隐藏 seam 与循环空间的生成函数和增长分离）

令

\[
P_n(u)=\sum_{k\ge0}N_{n,k}u^k,
\qquad
N_{n,k}=\binom{n-k+1}{k}.
\]

则二元生成函数为

\[
\sum_{n\ge0}P_n(u)z^n
=
\frac{1+uz}{1-z-uz^2}.
\]

令

\[
H(z)=\sum_{n\ge0}h_nz^n,
\qquad
C(z)=\sum_{n\ge0}c_nz^n.
\]

则

\[
\boxed{
H(z)=\frac{z^3}{(1-z)^2(1-z-z^2)},
\qquad
C(z)=\frac{z^3}{(1-z)(1-z-z^2)^2}.
}
\]

因此

\[
\boxed{
\sum_{n\ge0}(c_n-h_n)z^n
=
\frac{z^5}{(1-z)^2(1-z-z^2)^2}.
}
\]

若 \(\varphi=(1+\sqrt5)/2\)，则

\[
h_n\sim
\frac{\varphi^3}{\varphi^2+1}\,\varphi^n,
\]

\[
c_n\sim
\frac{\varphi^3}{(\varphi^2+1)^2}\,(n+1)\varphi^n,
\]

从而

\[
\boxed{
\frac{c_n}{h_n}
\sim
\frac{n}{\varphi^2+1}.
}
\]

#### 证明

每个合法支持的最大位置是否被占据给出 Fibonacci 递推

\[
P_n(u)=P_{n-1}(u)+uP_{n-2}(u)
\qquad(n\ge2),
\]

初值为

\[
P_0(u)=1,\qquad P_1(u)=1+u.
\]

对递推求生成函数得到

\[
\sum_{n\ge0}P_n(u)z^n
=
\frac{1+uz}{1-z-uz^2}.
\]

取 \(u=1\) 得

\[
V(z):=\sum_{n\ge0}V_nz^n
=
\frac{1+z}{1-z-z^2}.
\]

对 \(u\) 求导后在 \(u=1\) 处取值，得到

\[
E(z):=\sum_{n\ge0}E_nz^n
=
\left.
\frac{\partial}{\partial u}
\frac{1+uz}{1-z-uz^2}
\right|_{u=1}
=
\frac{z}{(1-z-z^2)^2}.
\]

由

\[
h_n=V_n-n-1,
\qquad
c_n=E_n-V_n+1,
\]

以及

\[
\sum_{n\ge0}(n+1)z^n=\frac1{(1-z)^2},
\qquad
\sum_{n\ge0}z^n=\frac1{1-z},
\]

直接化简得到

\[
H(z)
=
\frac{1+z}{1-z-z^2}
-\frac1{(1-z)^2}
=
\frac{z^3}{(1-z)^2(1-z-z^2)},
\]

以及

\[
C(z)
=
\frac{z}{(1-z-z^2)^2}
-\frac{1+z}{1-z-z^2}
+\frac1{1-z}
=
\frac{z^3}{(1-z)(1-z-z^2)^2}.
\]

两者相减给出

\[
C(z)-H(z)
=
\frac{z^5}{(1-z)^2(1-z-z^2)^2}.
\]

为得到渐近式，分解

\[
1-z-z^2
=
(1-\varphi z)(1+\varphi^{-1}z).
\]

对于 \(H\)，在 \(z=\varphi^{-1}\) 处是单极点，且其主部系数为

\[
\frac{(\varphi^{-1})^3}
{(1-\varphi^{-1})^2(1+\varphi^{-2})}
=
\frac{\varphi^3}{\varphi^2+1}.
\]

因此

\[
h_n\sim
\frac{\varphi^3}{\varphi^2+1}\varphi^n.
\]

对于 \(C\)，在同一点是二阶极点，二阶主部系数为

\[
\frac{(\varphi^{-1})^3}
{(1-\varphi^{-1})(1+\varphi^{-2})^2}
=
\frac{\varphi^3}{(\varphi^2+1)^2}.
\]

二阶极点的系数为该主部系数乘以 \(n+1\)，故

\[
c_n\sim
\frac{\varphi^3}{(\varphi^2+1)^2}(n+1)\varphi^n.
\]

两式相除即得

\[
\frac{c_n}{h_n}
\sim
\frac{n}{\varphi^2+1}.
\]

证毕。

### 推论 22.12（细化层的循环过剩）

令

\[
\rho=\frac1{\varphi^2+1}.
\]

则

\[
c_n=\rho n\,h_n+O(h_n),
\]

并且

\[
c_n-h_n
=
\rho n\,h_n+O(h_n).
\]

因此存在 \(n_0\)，使得对所有 \(n\ge n_0\)，

\[
c_n>h_n,
\]

且

\[
\frac{c_n-h_n}{c_n}\longrightarrow1.
\]

这意味着在 Fibonacci 细化中，大部分零一步可见边链自由度来自循环的非唯一性，而不是来自新的静态 seam 方向。

#### 证明

由定理 22.11 的渐近式，

\[
c_n=\rho(n+1)h_n(1+o(1)).
\]

于是

\[
c_n=\rho n\,h_n+O(h_n).
\]

因为 \(h_n\) 的增长量级为 \(\varphi^n\)，而 \(c_n/h_n\) 线性发散，所以 \(c_n>h_n\) 对充分大的 \(n\) 成立。再由

\[
\frac{c_n-h_n}{c_n}=1-\frac{h_n}{c_n}
\]

及 \(h_n/c_n\to0\)，得到极限为一。证毕。

该推论只涉及 Fibonacci cube 的有限计数和图循环空间。它不表示循环自由度都是概率上可执行的正流；参考定向下的非负可执行性还需另行检查。




### 推论 22.13（五态边界的 signed lift 与非负流分离）

在第 6 节的五态图上，取

\[
d=(1,-1,0,-1,1),\qquad
c=(1,1,1,1,0),
\]

并使用边空间的标准 Euclidean 内积。则

\[
f_{\mathrm{sgn}}
=
\left(-\frac12,\frac12,-\frac12,\frac12,0\right)
\]

满足

\[
Bf_{\mathrm{sgn}}=d,\qquad
f_{\mathrm{sgn}}\perp c,\qquad
\|f_{\mathrm{sgn}}\|^2=1.
\]

它是同一 seam \(d\) 的唯一最小 signed lift。所有 signed lifts 都是

\[
f_{\mathrm{sgn}}+\gamma c.
\]

若额外要求参考定向下的边流逐项非负，则必须有 \(\gamma\ge\frac12\)，最小非负 lift 为

\[
f_{\mathrm{nonneg}}
=
(0,1,0,1,0),
\qquad
\|f_{\mathrm{nonneg}}\|^2=2.
\]

#### 证明

直接代入第 6 节的边界公式：

\[
B(a,b,c,d,e)=(-a+d-e,\ a-b,\ e,\ c-d,\ b-c)
\]

得到

\[
Bf_{\mathrm{sgn}}=(1,-1,0,-1,1)=d.
\]

又因为

\[
f_{\mathrm{sgn}}\cdot c=0,
\]

且 \(\ker B=\mathbb Rc\)，故正交补中的该提升是唯一最小范数提升。所有其他提升与它之差属于 \(\ker B\)，所以恰为 \(f_{\mathrm{sgn}}+\gamma c\)。

其五个分量逐项非负当且仅当

\[
-\frac12+\gamma\ge0,
\]

其余不等式更弱，故 \(\gamma\ge\frac12\)。在边界值 \(\gamma=\frac12\) 处得到 \(f_{\mathrm{nonneg}}\)，范数平方为 \(2\)。证毕。

这个计算把两个不同的问题分开：

\[
\text{商空间的 canonical signed representative}
\neq
\text{参考定向下的非负可执行流的最小代表}.
\]

后者还需要非负性、容量和守恒等额外条件，不能由线性 seam 商同构自动推出。

## 23. 仿射 FIB 纤维的逆极限刚性

第 20 节给出了紧凸相容载体的逆极限非空性。非空性不等于唯一性。本节给出一条只使用闭区间和一维仿射映射的充分条件。它可以用于判断多层可见数据是否把隐藏 \(\kappa\) 轨道唯一固定。

### 定义 23.1（固定可见数据的纤维系统）

设每一层的可见数据 \(b_j=(X_j,Y_j,Z_j)\) 合法，并令对应 FIB 纤维为

\[
F_j
=
\mathcal F_{b_j}
=
[\ell_j,u_j],
\]

其中

\[
\ell_j=\max(0,X_j+Y_j-(1-Z_j)),
\qquad
u_j=\min(X_j,Y_j).
\]

设层间可见数据满足一个已给定的相容关系。若隐藏坐标的层间映射已被显式构造为

\[
f_j:F_{j+1}\longrightarrow F_j,
\qquad
f_j(t)=a_jt+b_j,
\]

则称 \((F_j,f_j)_{j\ge0}\) 为固定可见数据上的仿射 FIB 纤维系统。

这里 \(a_j,b_j\) 是桥接映射的数学系数。它们不能从“存在一个统一场”这句话自动得到，必须从具体的层间概率推前计算出来。

### 定理 23.2（仿射纤维逆极限至多唯一）

设 \((F_j,f_j)_{j\ge0}\) 是仿射 FIB 纤维系统。假设对某个固定 \(j\)，有

\[
\operatorname{diam}(F_n)
\prod_{k=j}^{n-1}|a_k|
\longrightarrow0
\qquad(n\to\infty).
\]

则任意两个逆极限元素

\[
(\kappa_m)_{m\ge0},
\qquad
(\kappa'_m)_{m\ge0}
\]

满足

\[
\kappa_j=\kappa'_j.
\]

若该条件对所有 \(j\) 成立，则

\[
\varprojlim_j(F_j,f_j)
\]

至多含有一个元素。

#### 证明

由逆极限相容性，

\[
\kappa_j=f_j(\kappa_{j+1}),
\qquad
\kappa'_j=f_j(\kappa'_{j+1}).
\]

仿射性给出

\[
\kappa_j-\kappa'_j
=
a_j(\kappa_{j+1}-\kappa'_{j+1}).
\]

迭代 \(n-j\) 次得到

\[
\kappa_j-\kappa'_j
=
\left(\prod_{k=j}^{n-1}a_k\right)
(\kappa_n-\kappa'_n).
\]

由于两点都属于 \(F_n\)，

\[
|\kappa_n-\kappa'_n|
\le
\operatorname{diam}(F_n).
\]

所以

\[
|\kappa_j-\kappa'_j|
\le
\operatorname{diam}(F_n)
\prod_{k=j}^{n-1}|a_k|.
\]

令 \(n\to\infty\)，由假设得到

\[
|\kappa_j-\kappa'_j|=0.
\]

这证明第 \(j\) 个坐标唯一。若条件对所有 \(j\) 成立，则两个逆极限元素的每个坐标都相同，故逆极限至多含有一个元素。证毕。

### 推论 23.3（统一收缩常数）

若存在 \(0\le q<1\) 使

\[
|a_j|\le q
\]

对所有 \(j\) 成立，并且

\[
\sup_n\operatorname{diam}(F_n)<\infty,
\]

则仿射 FIB 纤维逆极限至多含有一个元素。

#### 证明

有

\[
\operatorname{diam}(F_n)
\prod_{k=j}^{n-1}|a_k|
\le
\left(\sup_m\operatorname{diam}(F_m)\right)q^{n-j}
\longrightarrow0.
\]

应用定理 23.2。证毕。

### 推论 23.4（存在性加刚性）

如果每个 \(f_j:F_{j+1}\to F_j\) 连续满射，并且定理 23.2 的条件对所有 \(j\) 成立，则逆极限恰含一个元素。

#### 证明

闭区间 \(F_j\) 是非空紧凸集，\(f_j\) 连续仿射满射。定理 20.2 应用于该一维系统，给出逆极限非空。定理 23.2 给出至多唯一。两者合并即得恰含一个元素。证毕。

### 推论 23.5（静态隐藏坐标的可识别性条件）

设 \((p_j)_j\) 和 \((p'_j)_j\) 是两个相容的 FIB 概率场族，且它们在每层具有相同的可见数据 \(b_j\)。若各层隐藏坐标满足

\[
\kappa_j=p_{j,25},
\qquad
\kappa'_j=p'_{j,25},
\]

并且层间 \(\kappa\) 映射满足定理 23.2 的收缩条件，则

\[
\kappa_j=\kappa'_j
\]

对每个 \(j\) 成立。由 FIB 的单层重构定理，

\[
p_j=p'_j
\]

对每层成立。因此在该条件下，相容静态场在 FIB 概率 sector 上唯一。

#### 证明

定理 23.2 给出所有隐藏坐标相同。固定 \(b_j\) 后，FIB 重构公式

\[
p_{j,0}=(1-Z_j)-X_j-Y_j+\kappa_j,
\]

\[
p_{j,2}=X_j-\kappa_j,
\qquad
p_{j,3}=Z_j,
\qquad
p_{j,5}=Y_j-\kappa_j,
\qquad
p_{j,25}=\kappa_j
\]

逐项给出 \(p_j=p'_j\)。证毕。

该推论的适用边界是明确的：它要求已经构造出仿射隐藏坐标 bonding。仅知道每层都有同一个 FIB 公式，不能推出不同层之间存在这样的 \(f_j\)。

### 23.1 与 Fisher 曲率的关系

如果每个 \(f_j\) 来自一个概率推前 \(q_j\)，并且 \(u_j=Dq_ju_{j+1}\)，则定理 20.4 仍给出

\[
\mathcal I_j(p_j;u_j)
\le
\mathcal I_{j+1}(p_{j+1};u_{j+1}).
\]

因此，仿射收缩提供的是隐藏坐标的逆极限刚性，Fisher 数据处理提供的是微分扰动的曲率单调性。两者结论不同：

\[
\text{坐标唯一性}
\neq
\text{Fisher 曲率有限性}.
\]

若要同时获得二者，必须分别验证仿射 bonding 条件和概率推前的 Fisher 条件。




---

## 24. 场、能量、轨迹与可见流形的最小数学闭包

前文已经定义了局部五态概率律、Fisher 线元、图 Dirichlet 能量、边界 seam 和逆极限纤维。本节把“场产生能量、能量形成分布、分布产生轨迹、轨迹形成可见流形”改写成有限维数学对象。这里的“产生”表示由给定场状态通过明确的函数或动力学生成元导出，不表示额外的物理本体假设。

### 定义 24.1（有限图上的静态概率场）

令 \(G=(V,E)\) 是有限连通图。对每个节点 \(v\in V\)，给定一个局部概率纤维

\[
F_v\subseteq\Delta(\Sigma),
\]

并令

\[
\mathcal C_G=\prod_{v\in V}F_v
\]

为有限图上的场配置空间。一个场配置记为

\[
\Phi=(p_v)_{v\in V}\in\mathcal C_G.
\]

若所有 \(p_v\) 的坐标都严格为正，则 \(\mathcal C_G^\circ\) 是一个有限维光滑流形的相对内部；其切空间由每个节点的质量零向量组成。

### 定义 24.2（场势与边耦合）

对每个节点给定局部势函数

\[
U_v:F_v\longrightarrow\mathbb R,
\]

对每条有向边 \(e=(u,v)\) 给定线性边读出

\[
L_e:\mathbb R^\Sigma\longrightarrow\mathbb R^{m_e},
\qquad
R_e:\mathbb R^\Sigma\longrightarrow\mathbb R^{m_e},
\]

以及正半定权矩阵 \(M_e\succeq0\)。定义场能量

\[
\mathcal E(\Phi)
=
\sum_{v\in V}U_v(p_v)
+
\frac12
\sum_{e=(u,v)\in E}
\left\|
L_ep_u-R_ep_v
\right\|_{M_e}^{2},
\]

其中

\[
\|q\|_{M_e}^{2}=q^{\mathsf T}M_eq.
\]

第一项是节点势，第二项是相邻局部场之间的兼容成本。若 \(L_e=R_e=I\)，第二项就是普通图上的加权 Dirichlet 耦合。

### 定理 24.3（场能量的非负分解）

若每个 \(U_v\) 有下界，并且 \(M_e\succeq0\)，则

\[
\mathcal E(\Phi)
\]

由节点势和边界失配的非负二次项组成。若两个场配置 \(\Phi,\Psi\) 在所有节点上具有相同的局部势值，且

\[
L_ep_u-R_ep_v
=
L_e q_u-R_e q_v
\]

对相应的边读出成立，则它们具有相同的边耦合能量。

#### 证明

对每条边，

\[
\left\|
L_ep_u-R_ep_v
\right\|_{M_e}^{2}
\ge0
\]

来自 \(M_e\succeq0\)。逐项求和即可得到分解。第二个结论来自边差向量相同导致二次型相同。证毕。

### 定义 24.4（场导出的能量分布）

若 \(\mathcal E_v(\Phi)\ge0\) 是节点 \(v\) 的局部能量贡献，并且

\[
\mathcal E_{\mathrm{tot}}(\Phi)
=
\sum_{v\in V}\mathcal E_v(\Phi)>0,
\]

则定义能量分布

\[
\pi_\Phi(v)
=
\frac{\mathcal E_v(\Phi)}
{\mathcal E_{\mathrm{tot}}(\Phi)}.
\]

因此能量分布不是与场并列的原始变量，而是场配置和势函数的推前。若势函数为五态函数 \(\varepsilon:\Sigma\to\mathbb R\)，则单节点平均能量为

\[
\overline{\varepsilon}(p)
=
\sum_{s\in\Sigma}p_s\varepsilon(s).
\]

对原生数值读出

\[
\varepsilon(0)=0,\quad
\varepsilon(2)=2,\quad
\varepsilon(3)=3,\quad
\varepsilon(5)=5,\quad
\varepsilon(25)=7,
\]

有

\[
\overline{\varepsilon}(p)=2X+3Z+5Y,
\]

而二阶能量为

\[
\sum_s p_s\varepsilon(s)^2
=
4X+9Z+25Y+20\kappa.
\]

因此一次能量均值只看到三维可见投影，二阶能量已经看到隐藏 seam \(\kappa\)。这给出“场产生能量分布”的严格版本：隐藏联合关系在低阶观测中可以退化，在更高阶能量矩中恢复。

### 定义 24.5（场产生的轨迹）

令 \(\mathsf M_\Phi\) 是切空间上的正半定 mobility 算子。若 \(\mathcal E\) 在 \(\mathcal C_G^\circ\) 上可微，则定义耗散轨迹

\[
\dot\Phi_t
=
-\mathsf M_{\Phi_t}\nabla\mathcal E(\Phi_t).
\]

若给定切空间上的反对称算子 \(\mathsf J_\Phi^*=-\mathsf J_\Phi\)，则定义保守轨迹

\[
\dot\Phi_t
=
\mathsf J_{\Phi_t}\nabla\mathcal E(\Phi_t).
\]

这两种生成元应当分开记账：\(\mathsf M_\Phi\) 负责沿势下降的耗散，\(\mathsf J_\Phi\) 负责不改变一阶能量的相位运动。

### 定理 24.6（梯度轨迹的能量耗散）

在耗散轨迹存在且保持在 \(\mathcal C_G^\circ\) 内的时间区间上，有

\[
\frac{d}{dt}\mathcal E(\Phi_t)
=
-\left\langle
\nabla\mathcal E(\Phi_t),
\mathsf M_{\Phi_t}\nabla\mathcal E(\Phi_t)
\right\rangle
\le0.
\]

在保守轨迹上，有

\[
\frac{d}{dt}\mathcal E(\Phi_t)=0.
\]

#### 证明

由链式法则，

\[
\frac{d}{dt}\mathcal E(\Phi_t)
=
\left\langle
\nabla\mathcal E(\Phi_t),\dot\Phi_t
\right\rangle.
\]

代入耗散生成元得到第一式，正半定性给出不等式。代入保守生成元得到

\[
\langle\nabla\mathcal E,\mathsf J_\Phi\nabla\mathcal E\rangle=0
\]

因为 \(\mathsf J_\Phi\) 反对称。证毕。

### 定义 24.7（场配置的可见流形）

令

\[
\mathsf P:\mathcal C_G\longrightarrow\mathbb R^{3|V|}
\]

把每个局部概率律送到其 \((X,Y,Z)\) 坐标。定义可见场空间

\[
\mathcal M_{\mathrm{vis}}
=
\mathsf P(\mathcal C_G).
\]

若在某个场配置的邻域内 \(\mathsf P\) 的秩恒为 \(3|V|\)，则该邻域的可见像可使用 \(3|V|\) 个局部坐标描述。其完整场配置仍然包含 \(\mathsf P\) 的纤维方向。

这给出“三维是视角”的严格数学表述：

\[
\text{三维可见空间}
=
\text{完整场配置空间经过观察映射后的像}.
\]

它不推出完整场本身只有三维，也不自动给出物理时空、Lorentz 结构或引力方程。

---

## 25. \(1\to2\to3\to5\) 的精确组合解释

“一个、镜像成二、二生三、三开始出现无限可能、$2+3=5$”在此对应三个分别陈述的命题：反向读取产生镜像，局部合法支持数满足 Fibonacci 递推，三坐标投影的五态载体具有二维不可见部分。

### 定义 25.1（无相邻支持场）

令

\[
\mathcal W_n
=
\left\{
w=(w_1,\ldots,w_n)\in\{0,1\}^n:
w_iw_{i+1}=0
\right\}.
\]

其中 \(w_i=1\) 表示第 \(i\) 个原子模式被激活。定义反向读取

\[
\mathsf r_n(w_1,\ldots,w_n)
=
(w_n,\ldots,w_1).
\]

由于无相邻条件在反向下保持，\(\mathsf r_n\) 是 \(\mathcal W_n\) 上的 involution：

\[
\mathsf r_n^2=\mathrm{id}.
\]

这就是局部场的离散镜像。它只反转读取方向，不改变合法性。

### 定理 25.2（\(2,3,5\) 的支持计数）

有

\[
|\mathcal W_1|=2,\qquad
|\mathcal W_2|=3,\qquad
|\mathcal W_3|=5.
\]

更一般地，

\[
|\mathcal W_n|
=
|\mathcal W_{n-1}|
+
|\mathcal W_{n-2}|.
\]

若以 \(F_0=0,F_1=1\) 记 Fibonacci 数，则

\[
|\mathcal W_n|=F_{n+2}.
\]

#### 证明

按最后一位分类。若 \(w_n=0\)，前 \(n-1\) 位任意属于 \(\mathcal W_{n-1}\)。若 \(w_n=1\)，则 \(w_{n-1}=0\)，去掉最后两位后得到 \(\mathcal W_{n-2}\)。两个集合不相交且覆盖全部 \(\mathcal W_n\)，所以

\[
|\mathcal W_n|
=
|\mathcal W_{n-1}|+|\mathcal W_{n-2}|.
\]

初值为

\[
\mathcal W_1=\{0,1\},
\]

以及

\[
\mathcal W_2=\{00,01,10\}.
\]

因此 \(|\mathcal W_1|=2\)、\(|\mathcal W_2|=3\)、\(|\mathcal W_3|=5\)。Fibonacci 表达式由同一递推和初值得到。证毕。

长度二时，

\[
\mathcal W_2=\{00,01,10\}
\]

的镜像轨道为

\[
\{00\},\qquad \{01,10\}.
\]

这里一个非平凡镜像轨道确实由两个方向组成，第三个状态是镜像固定点。长度三时，

\[
\mathcal W_3
=
\{000,001,010,100,101\},
\]

并且

\[
\mathsf r_3(001)=100.
\]

这说明“镜像二元关系”和“新增固定点”同时存在。下一层继续按最后一位分裂，就产生更多合法轨迹。

### 定义 25.3（五态载体的三位窗口编码）

对长度三的支持词定义

\[
\ell(000)=0,\qquad
\ell(100)=2,\qquad
\ell(010)=3,\qquad
\ell(001)=5,\qquad
\ell(101)=25.
\]

于是

\[
\ell(\mathcal W_3)=\{0,2,3,5,25\}=\Sigma.
\]

其中 \(25\) 表示第一个和第三个位置同时激活的联合状态。它的原生加性读出为

\[
2+5=7,
\]

这正是前文数值函数 \(W\) 在状态 \(25\) 上的取值。标签 \(25\) 是联合状态名称，数值读出 \(7\) 是另一种明确的函数，两者不能混用。

反向读取在五态上诱导

\[
0\leftrightarrow0,\qquad
2\leftrightarrow5,\qquad
3\leftrightarrow3,\qquad
25\leftrightarrow25.
\]

这是 FIB 五态载体内部的一个自然离散镜像。它与 zeta 功能方程的镜像属于不同层次：前者是局部支持读取的 involution，后者是完成 \(L\)-函数零点的复反射。若要将二者识别，仍需显式的 RH bridge。

### 定理 25.4（\(2+3=5\) 的可见/不可见维数分解）

令

\[
E=\mathbb R^\Sigma
\]

为五态权重空间，定义未归一化可见映射

\[
P:E\longrightarrow\mathbb R^3,
\qquad
P(p)=(X,Y,Z).
\]

则

\[
\operatorname{rank}P=3,
\]

并且

\[
\ker P
=
\operatorname{span}\{e_0,d\},
\]

其中 \(e_0\) 是零态坐标向量，且

\[
d=(1,-1,0,-1,1).
\]

因此

\[
\dim E
=
\dim\ker P+\dim\operatorname{im}P
=
2+3=5.
\]

在概率归一化切空间

\[
T_0=\left\{v\in E:\sum_{s\in\Sigma}v_s=0\right\}
\]

上，

\[
\ker(P|_{T_0})=\mathbb R d.
\]

#### 证明

若 \(P(p)=0\)，则

\[
p_2+p_{25}=0,\qquad
p_5+p_{25}=0,\qquad
p_3=0.
\]

于是

\[
p=(p_0,p_2,0,p_2,-p_2)
=
(p_0+p_2)e_0-p_2d.
\]

所以

\[
\ker P=\operatorname{span}\{e_0,d\}.
\]

由 \(X,Y,Z\) 三个坐标在 \(e_2,e_5,e_3\) 方向上独立，\(\operatorname{rank}P=3\)。秩零度定理给出

\[
5=2+3.
\]

由于

\[
\sum_s d_s=0,\qquad \sum_s(e_0)_s=1,
\]

有

\[
\ker P\cap T_0=\mathbb R d.
\]

证毕。

这个定理给出“二维加三维等于五态”的精确版本：

- 三维是可见坐标 \((X,Y,Z)\)；
- 二维是未归一化观察中不可见的两个方向；
- 其中一个是总质量/归一化方向；
- 另一个是归一化后真正留下的隐藏联合 seam \(d\)。

所以在合法概率场上，真正的隐藏自由度仍是一维 \(\kappa\)，而不是二维。二维加三维是五态线性载体的分解，归一化后变成三维可见加一维隐藏。

### 推论 25.5（三维可见状态产生无限轨迹空间）

定义无限合法支持空间

\[
\mathcal W_\infty
=
\left\{
w\in\{0,1\}^{\mathbb N}:w_iw_{i+1}=0
\right\},
\]

以及左移

\[
\sigma(w_1,w_2,w_3,\ldots)
=
(w_2,w_3,\ldots).
\]

对每个 \(w\in\mathcal W_\infty\)，其长度三局部窗口给出一条五态轨迹

\[
s_k(w)
=
\ell(w_{k+1},w_{k+2},w_{k+3}).
\]

因此

\[
w\longmapsto
(s_0(w),s_1(w),s_2(w),\ldots)
\]

把无限支持场送到五态轨迹空间。若局部能量为 \(\varepsilon:\Sigma\to\mathbb R\)，则定义经验能量分布

\[
\mu_N^w
=
\frac1N\sum_{k=0}^{N-1}
\delta_{s_k(w)}
\]

和经验能量

\[
\mathcal E_N(w)
=
\frac1N\sum_{k=0}^{N-1}
\varepsilon(s_k(w)).
\]

因此“从三开始出现无限可能”的严格含义是：三位局部窗口已经可以作为无限无相邻支持场的 cylinder state，左移作用产生无限长轨迹；有限五态概率律是这些轨迹的局部经验分布或概率推前。

这里的轨迹空间是符号动力系统，不是预先假定的物理时间。若要解释为连续时间动力学，还需要另给流、速率或连续插值。

---

## 26. 场、轨迹与 RH 能级的候选连接

前文的五态场和 Fibonacci 支持已经给出局部转移结构。若把一个局部能量势 \(\varphi\) 放到无限支持场上，可以定义加权转移算子

\[
(\mathcal L_s f)(w)
=
e^{-s\varphi(w)}
f(\sigma w).
\]

对有限窗口，这相当于一个加权邻接矩阵；其特征值控制允许轨迹的增长率、压力和能量分布。无权 Fibonacci 转移的邻接矩阵为

\[
A_{\mathrm{Fib}}
=
\begin{pmatrix}
1&1\\
1&0
\end{pmatrix},
\]

其特征值为

\[
\varphi,\qquad -\varphi^{-1}.
\]

这解释了黄金比例首先出现在支持计数和局部传输谱中。它提供的是 field-side transfer spectrum。

若要把这个结构提升为 Hilbert–Pólya 型算子，必须增加一个算术边界结构。所需的算术边界数据与条件是：

1. 每个素数或 sector 的局部传输块 \(G_{p,\pi}\)；
2. 由 Fibonacci/FIB 支持给出的隐藏 fiber 和 holonomy；
3. Gamma 因子对应的 archimedean boundary；
4. sector 对偶 \(\pi\leftrightarrow\widetilde\pi\) 对应的反射；
5. 一个正定兼容度量 \(G\)；
6. 一个正则化行列式或迹公式，满足
   \[
   \det_{\mathrm{reg}}(z-H)
   =
   C\,\Xi(z)
   \]
   或其一般 \(L\)-函数版本。

在这条链中，FIB 三维几何提供局部传输和隐藏状态；Fisher/Dirichlet 能量提供候选正定度量；Cayley/Krein 提供零点反射与负模态判据；Weil 显式公式负责把素数源和零点谱连起来。

当前可证明的结构只支持以下条件式命题：

\[
\begin{aligned}
&\text{若存在一个由算术局部块和边界条件构造的闭合自伴 }H,\\
&\text{且其谱行列式等于完成的 }\Xi\text{ 或 }\Lambda,\\
&\text{则所有非平凡零点都在临界线上。}
\end{aligned}
\]

FIB 到 \(H\) 的构造、FIB 缺陷到 Cayley 缺陷的守恒、以及谱行列式识别，仍然是桥接接口，不能由局部 Fibonacci 递推自动推出。

---

## 追加锚（本行以下为增补区）
