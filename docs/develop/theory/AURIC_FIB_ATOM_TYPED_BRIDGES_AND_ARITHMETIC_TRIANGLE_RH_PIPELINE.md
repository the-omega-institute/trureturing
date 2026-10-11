# Auric FIB ATOM：类型化桥接、算术驱动、三角网络与 RH 管线

## 0. 目的与证据边界

本卷把五个已经分别出现的对象放入同一个类型化管线：

1. 五态 FIB 概率律；
2. 固定一阶读出的 \(\kappa\)-纤维；
3. Fisher 信息几何与读出收缩；
4. Fibonacci 支持图的动态边界与环流；
5. 算术驱动、triangle-local 提升以及 RH-Cayley 单元。

本文只使用显式定义的映射和概率核。没有定义的映射不被视为存在。特别是，素数分类到五态模式的编码、FIB 到三个独立源的提升、FIB 缺陷到 zeta 零点的映射，均在本文中作为待实现桥接接口，而不是已经证明的等价。

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

当前仓库已经形式化了 Cayley 单元本身，但没有定义上述 FIB 到零点空间的映射。因此，\(\Delta=0\) 与 RH 的临界线条件目前仍是结构类比。

---

## 11. 形式化目标

下一步可直接形式化的对象按依赖顺序排列如下：

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

前十二项是有限维代数、凸几何、信息几何和图论命题。第十三至十五项是桥接接口，需要新的具体构造才能升级为定理。


---

## 12. Lean 形状的形式化契约

本节给出直接进入 Lean 文件时应采用的类型边界。以下代码是接口草图，不宣称已经编译。每个定理的数学内容已经在前文证明或由前文的有限维计算给出。

~~~lean
namespace AuricFIB

inductive Mode
| zero | two | three | five | twentyFive
deriving DecidableEq, Fintype

abbrev Law := Mode → ℝ

def IsProbability (p : Law) : Prop :=
  (∀ s, 0 ≤ p s) ∧ (∑ s, p s = 1)

def x : Mode → ℝ
  | .two | .twentyFive => 1
  | _ => 0

def y : Mode → ℝ
  | .five | .twentyFive => 1
  | _ => 0

def z : Mode → ℝ
  | .three => 1
  | _ => 0

def visible (p : Law) : ℝ × ℝ × ℝ :=
  (∑ s, p s * x s, ∑ s, p s * y s, ∑ s, p s * z s)

def kappa (p : Law) : ℝ :=
  p .twentyFive

def seam : Law :=
  fun s =>
    match s with
    | .zero => 1
    | .two => -1
    | .three => 0
    | .five => -1
    | .twentyFive => 1

def reconstruct (X Y Z κ : ℝ) : Law :=
  fun s =>
    match s with
    | .zero => 1 - X - Y - Z + κ
    | .two => X - κ
    | .three => Z
    | .five => Y - κ
    | .twentyFive => κ

def Fiber (X Y Z : ℝ) : Set Law :=
  {p | IsProbability p ∧ visible p = (X, Y, Z)}

theorem reconstruct_visible
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hXZ : X + Z ≤ 1) (hYZ : Y + Z ≤ 1)
    (hκ : max 0 (X + Y - (1 - Z)) ≤ κ)
    (hκ' : κ ≤ min X Y) :
    IsProbability (reconstruct X Y Z κ) := by
  sorry

theorem fiber_parametric
    (p : Law) (hp : IsProbability p) :
    p ∈ Fiber X Y Z ↔
      ∃ κ, p = reconstruct X Y Z κ := by
  sorry

def fourCorner (f : Mode → ℝ) : ℝ :=
  f .twentyFive - f .two - f .five + f .zero

theorem expectation_decomposition
    (p : Law) (hp : IsProbability p) (f : Mode → ℝ) :
    (∑ s, p s * f s)
      =
      f .zero
      + (f .two - f .zero) * (visible p).1
      + (f .five - f .zero) * (visible p).2.1
      + (f .three - f .zero) * (visible p).2.2
      + fourCorner f * kappa p := by
  sorry

def numeric (s : Mode) : ℝ :=
  match s with
  | .zero => 0
  | .two => 2
  | .three => 3
  | .five => 5
  | .twentyFive => 7

theorem second_moment_recovers_kappa
    (p : Law) (hp : IsProbability p) :
    kappa p =
      ((∑ s, p s * (numeric s)^2)
       - (∑ s, p s * numeric s)^2
       + (2 * (visible p).1 + 3 * (visible p).2.2
          + 5 * (visible p).2.1)^2
       - 4 * (visible p).1
       - 9 * (visible p).2.2
       - 25 * (visible p).2.1) / 20 := by
  sorry

def delta (p : Law) : ℝ :=
  (1 - (visible p).2.2) * kappa p
    - (visible p).1 * (visible p).2.1

theorem determinant_defect
    (p : Law) (hp : IsProbability p) :
    p .zero * p .twentyFive - p .two * p .five = delta p := by
  sorry

structure ArithmeticBridge (C : Type) where
  encode : C → Law
  preserves_probability : ∀ c, IsProbability (encode c)
  driver : C → Type

structure TriangleLift (Λα Λβ Λγ : Type) where
  source_product :
    Measure Λα → Measure Λβ → Measure Λγ → Measure (Λα × Λβ × Λγ)
  response :
    Λβ × Λγ → Measure Bool
  local_pushforward :
    Law → Prop

structure RHBridge (C : Type) where
  zeroSpace : Type
  mapToZero : C → zeroSpace
  fibDefect : C → ℝ
  cayleyDefect : zeroSpace → ℝ
  defect_transport :
    ∀ c, fibDefect c = cayleyDefect (mapToZero c)

end AuricFIB
~~~

其中 ArithmeticBridge、TriangleLift 和 RHBridge 的目的不同：

- ArithmeticBridge 负责把素数窗口、模类或 Fibonacci 支持编码成合法概率律；
- TriangleLift 负责证明该律来自三个独立源和两边响应；
- RHBridge 才有资格讨论 FIB 缺陷是否能被传送为 Cayley 缺陷。

如果没有 encode、local_pushforward 或 defect_transport 的具体构造，后续结论只能停留在接口层。

## 13. 形式化依赖顺序

建议按以下顺序实现：

1. 枚举 Mode，证明 Fintype 和有限求和化简；
2. 定义 Law、IsProbability、visible 和 kappa；
3. 证明 reconstruct_visible；
4. 证明 fiber_parametric；
5. 定义 fourCorner，证明 expectation_decomposition；
6. 定义 numeric，证明 second_moment_recovers_kappa；
7. 定义 delta，证明 determinant_defect；
8. 在正内部条件下定义 Fisher 线元；
9. 单独定义有限状态边图和短正合列；
10. 再定义算术编码、三角提升和 RH 缺陷传送。

这样可以把有限五态代数与尚未完成的外部桥接分开，避免 bridge-only 定义污染基础定理。


## 14. 有限三角提升的精确契约

上一节的 TriangleLift 是桥接占位。对当前五态理论，较小且可形式化的版本应先固定为有限源空间。

~~~lean
abbrev FiniteDist (α : Type) [Fintype α] := α → ℝ

def IsFiniteDist (μ : FiniteDist α) : Prop :=
  (∀ a, 0 ≤ μ a) ∧ (∑ a, μ a = 1)

structure LocalKernel (Ω Out : Type) [Fintype Out] where
  prob : Ω → Out → ℝ
  nonnegative : ∀ ω o, 0 ≤ prob ω o
  normalized : ∀ ω, ∑ o, prob ω o = 1

structure TriangleLiftFinite
    (Λα Λβ Λγ : Type)
    [Fintype Λα] [Fintype Λβ] [Fintype Λγ] where
  μα : FiniteDist Λα
  μβ : FiniteDist Λβ
  μγ : FiniteDist Λγ
  μα_prob : IsFiniteDist μα
  μβ_prob : IsFiniteDist μβ
  μγ_prob : IsFiniteDist μγ
  A : LocalKernel (Λβ × Λγ) Bool
  B : LocalKernel (Λγ × Λα) Bool
  C : LocalKernel (Λα × Λβ) Bool

def triangleObserved
    (T : TriangleLiftFinite Λα Λβ Λγ) :
    Bool × Bool × Bool → ℝ
  | (a, b, c) =>
    ∑ α, ∑ β, ∑ γ,
      T.μα α * T.μβ β * T.μγ γ
        * T.A.prob (β, γ) a
        * T.B.prob (γ, α) b
        * T.C.prob (α, β) c

theorem triangleObserved_probability
    (T : TriangleLiftFinite Λα Λβ Λγ)
    : IsFiniteDist (triangleObserved T) := by
  sorry

def LocalPushforward
    (T : TriangleLiftFinite Λα Λβ Λγ)
    (q : Law) : Prop :=
  ∃ f : Bool × Bool × Bool → Mode,
    q = fun s =>
      ∑ abc, if f abc = s then triangleObserved T abc else 0

structure ArithmeticEncoding (C : Type) where
  encode : C → Law
  valid : ∀ c, IsProbability (encode c)
  visible_driver : C → ℝ × ℝ × ℝ
  visible_correct :
    ∀ c, visible (encode c) = visible_driver c
~~~

这个有限版本把三件事分开：

1. \(\mu_\alpha\mu_\beta\mu_\gamma\) 的独立源乘积；
2. 每个观察者只读取相邻的两个源；
3. FIB 五态律是最终输出的有限事件推前。

因此可以单独证明：

\[
\text{TriangleLiftFinite}
\Longrightarrow
\text{IsProbability}(q),
\]

再研究 \(q\) 的 \((X,Y,Z,\kappa)\) 坐标。若要研究非二值输出，只需把 Bool 替换为有限输出类型。

对素数驱动，直接使用上面的 ArithmeticEncoding。这样可以把“算术输入改变哪一个 FIB 模式质量”作为一个可计算函数，而不是用模式名称相似性代替编码定义。


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

### 15.11 形式化义务清单

为把本卷升级为可检查的统一场理论，需依次补齐：

1. 选择配置空间 \(\mathcal C\)、规范群和规范固定切空间；
2. 给出 \(\mathcal E\) 及其二阶 Hessian \(K_*\)，证明静态背景存在与稳定性；
3. 构造五个事件分区 \(e_s\)，证明 \(\Pi\) 保持概率；
4. 构造 \(v_\kappa\)，并区分 \(D(P\circ\Pi)\) 的读出核和 \(K_*\) 的曲率核；
5. 为耗散迁移率 \(M\)、辛结构 \(J\)、FIB 质量 \(m_\kappa\) 给出公理；
6. 明确定义树场与 FIB 的乘积空间、桥接算子以及 Schur 补；
7. 在三角网络中证明独立源乘积和局部推前；
8. 最后给出统一场到 RH 零空间的 \(U\) 或正则化行列式证明。

目前 1 至 5 可在有限维近似中直接形式化，6 至 8 是真正的外部桥接目标。上述边界保证任何尚未实现的算术、三角或 RH 结论都不会被误写成已有定理。

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

### 16.6 形式化顺序与桥接义务

建议把 Lean 形式化分成两层。

**L0，原生有限数学：**

1. 定义 Mode、\(\mathcal A_0=\mathbb R^\Sigma\)、概率单纯形和有限求和；
2. 定义 visible、\(\kappa\)、seam，证明重构式、合法纤维和 \(\ker DP_0=\mathbb Rd\)；
3. 定义 Shannon 熵、负熵 Hessian 和 Fisher 线元，证明定理 16.4；
4. 定义有限图的边空间、\(B_j,A_j\)、循环核和 \(L_j=B_jB_j^*\)；
5. 定义有限载体 \(C_j\)、兼容压缩 \(q_{j+1,j}\) 和逆极限 \(\mathfrak F\)。

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

可接入 trureturing 的接口是：

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

对本项目的精确启发是：若要把有限层 Fibonacci 图的场推进到几何极限，必须在桥接对象中显式加入：

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

因此，trureturing 可以先定义非局部图能量

\[
\mathcal Q_{j,\varepsilon}(u)
=
\frac{1}{\varepsilon^{m+2}}
\sum_{v,w}
\eta\!\left(\frac{d_j(v,w)}{\varepsilon}\right)
|u_v-u_w|^2\mu_j(v)\mu_j(w),
\]

然后把 Mosco 收敛作为显式证明目标。该路线不预设极限必须是流形。若最终需要黎曼流形，仍要增加一个独立的光滑化或流形识别定理。

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

这直接对应金字塔层级的一个形式化义务：

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

这为本项目提供一个类型正确的有限层对象：

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

对 trureturing 的直接约束是：

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

这为本项目的 Lean 接口提供了一个清晰对象。将指定 inflation 的约束编码为
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

若要接入量子 triangle，trureturing 必须把 classical probability carrier 扩展为：

\[
\rho\succeq0,
\qquad
\operatorname{Tr}\rho=1,
\]

并把 marginal consistency 写成 partial trace 方程。五态 FIB 概率律不能自动承载 density operator、正半定性和量子边缘约束。

### 17.4 RH 与自伴谱桥

#### 17.4.1 Hilbert–Pólya 只是谱目标

Berry 和 Keating 的 [The Riemann zeros and eigenvalue asymptotics](https://epubs.siam.org/doi/10.1137/S0036144598347497) 提出零点虚部的计数函数与某个未知 Hermitian operator 的半经典能级计数具有相似性。这是谱启发和渐近证据，论文没有构造满足零点完整谱的自伴算子。

Connes 的 [Trace formula in noncommutative geometry and the zeros of the Riemann zeta function](https://arxiv.org/abs/math/9811068) 给出临界零点的谱解释和显式公式的 trace-formula 解释。对本项目而言，任何声称统一场产生 RH 谱的构造至少要记录一个 trace identity 或等价的正规化行列式关系。

#### 17.4.2 已有算子构造的边界

Bender、Brody 和 Müller 的 [Hamiltonian for the zeros of the Riemann zeta function](https://arxiv.org/abs/1608.03679) 构造了形式 Hamiltonian，并通过边界条件使其特征值对应 zeta 零点。作者明确指出该算子并非通常意义下的 Hermitian，若能严格证明其自伴性，才会得到 RH。

Li 的 [On the spectrum of a differential operator on a Hilbert–Pólya space](https://arxiv.org/abs/2404.11902) 在特定测试函数商空间上构造微分算子，并陈述零点与特征值之间的等价。该结果把“谱实现”与“自伴性”分开，不能单独推出 RH。

因此本项目必须分开记录：

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

该定理的可形式化接口必须包含：

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

本账本将外部研究转化为可追踪的形式化义务。它不增加未证明的统一场结论，而是规定从 Auric FIB 有限结构走向 Dirichlet 极限、信息梯度流、triangle inflation 和 RH 自伴谱时，每一步必须补充什么。


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

以下三条是把图二次型推进到 Dirichlet 极限所需的最小形式化账本：

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

用户提出的“一个、镜像成二、二生三、三开始出现无限可能、\(2+3=5\)”可以分解成三个可以分别形式化的命题：反向读取产生镜像，局部合法支持数满足 Fibonacci 递推，三坐标投影的五态载体具有二维不可见部分。

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

若要把这个结构提升为 Hilbert–Pólya 型算子，必须增加一个算术边界结构。一个可形式化的目标是寻找：

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

## 27. 本节的形式化边界

本节新增的可直接形式化内容为：

1. 有限图概率场 \(\mathcal C_G\)；
2. 节点势与边耦合能量；
3. 场能量的非负分解；
4. 概率场到能量分布的推前；
5. 梯度轨迹的能量耗散；
6. 五态载体的精确维数分解
   \[
   5=2+3;
   \]
7. 无相邻支持的反射 involution；
8. \(|\mathcal W_1|=2\)、\(|\mathcal W_2|=3\)、\(|\mathcal W_3|=5\)；
9. Fibonacci 支持递推；
10. 三位窗口到五态载体的编码；
11. 无限支持场到五态轨迹的局部推前；
12. 局部势产生经验能量分布的定义。

以下对象仍然是显式桥接目标：

1. 素数分类到支持场 \(\mathcal W_\infty\) 的具体编码；
2. 素数权重到局部势 \(\varphi\) 的唯一构造；
3. FIB transfer operator 到 completed \(L\)-function 的谱行列式；
4. 局部反向读取到 \(s\mapsto1-\overline{s}\) 的复反射；
5. Fisher/Dirichlet 正定度量到 Hilbert–Pólya 自伴算子的构造；
6. 无限轨迹空间的连续流形结构；
7. 物理能量、时间、引力或量子 Hamiltonian 的解释。

因此，本节的核心结论是：

\[
\boxed{
\begin{aligned}
&\text{场配置决定局部势和耦合，}\\
&\text{势决定能量分布，}\\
&\text{场上的 shift 或梯度生成元决定轨迹，}\\
&\text{观察映射决定可见流形，}\\
&\text{镜像与 Fibonacci 递推决定局部状态的闭包方式。}
\end{aligned}
}
\]

对当前 Auric FIB ATOM 载体，最严格的数字结构是

\[
\boxed{
\dim(\text{unobserved linear sector})
+
\dim(\text{visible quotient})
=
2+3=5,
}
\]

以及

\[
\boxed{
|\mathcal W_1|=2,\qquad
|\mathcal W_2|=3,\qquad
|\mathcal W_3|=5,
\qquad
|\mathcal W_n|=F_{n+2}.
}
\]

“镜像、三维视角、联合隐藏关系、无限轨迹和 Fibonacci”因此可以放进同一个有限到无限的组合场框架。把它们继续连接到 RH，需要完成算术编码、正定谱度量和完成 \(L\)-函数的 trace/determinant bridge。


---

## 28. 有限量子载体与 CPTP 组合子

本节把量子网络限定为有限维线性代数。所有量子对象均可编码为有限复矩阵，因此这一层原则上可以进入 Lean、Isabelle 或其他证明助手。这里不把“量子”解释为额外物理本体，只使用正半定性、迹、张量积和线性映射。

### 定义 28.1（有限量子状态）

令 \(H\) 为有限维复 Hilbert 空间，令 \(\mathsf L(H)\) 为其线性算子空间，令

\[
\mathsf D(H)
=
\{\rho\in\mathsf L(H):
\rho=\rho^\ast,\ \rho\succeq0,\ \operatorname{tr}\rho=1\}.
\]

若 \(\rho\in\mathsf D(H)\)，称 \(\rho\) 为量子状态。若 \(\sigma\succeq0\) 且 \(\operatorname{tr}\sigma=1\)，则 \(\sigma\) 也是量子状态。纯状态是秩一投影 \( |\psi\rangle\langle\psi| \)。

### 定义 28.2（量子信道）

有限维量子信道是线性映射

\[
\mathcal E:\mathsf L(H_A)\longrightarrow\mathsf L(H_B)
\]

满足：

1. 完全正性：对每个有限维 \(K\)，
   \[
   \mathcal E\otimes\operatorname{id}_K
   \]
   把正半定算子送到正半定算子；

2. 保迹性：
   \[
   \operatorname{tr}\mathcal E(X)=\operatorname{tr}X.
   \]

记所有这样的映射为 \(\operatorname{CPTP}(H_A,H_B)\)。

### 命题 28.3（Kraus 表示与 Choi 判据）

有限维线性映射 \(\mathcal E\) 是 CPTP，当且仅当存在有限个算子 \(K_i:H_A\to H_B\)，使

\[
\mathcal E(X)=\sum_iK_iXK_i^\ast,
\qquad
\sum_iK_i^\ast K_i=I_{H_A}.
\]

等价地，其 Choi 矩阵

\[
J(\mathcal E)
=
\sum_{i,j}|i\rangle\langle j|
\otimes
\mathcal E(|i\rangle\langle j|)
\]

满足

\[
J(\mathcal E)\succeq0,
\qquad
\operatorname{tr}_{H_B}J(\mathcal E)=I_{H_A}.
\]

#### 证明

Kraus 表示给出完全正性，因为

\[
(\mathcal E\otimes\operatorname{id}_K)(X)
=
\sum_i(K_i\otimes I_K)X(K_i^\ast\otimes I_K)
\]

保持正半定性。且

\[
\operatorname{tr}\mathcal E(X)
=
\operatorname{tr}
\left(
\sum_iK_i^\ast K_iX
\right)
=
\operatorname{tr}X.
\]

反向方向是有限维 Choi 定理。完全正性等价于 \(J(\mathcal E)\succeq0\)，保迹性等价于部分迹条件。证毕。

### 定理 28.4（CPTP 组合子结构）

有限维 Hilbert 空间和 CPTP 映射构成一个带张量积的对称幺半范畴：

\[
\mathbf{QFin}.
\]

具体地：

\[
\operatorname{id}_H\in\operatorname{CPTP}(H,H),
\]

若 \(\mathcal E\in\operatorname{CPTP}(H_A,H_B)\) 且

\[
\mathcal F\in\operatorname{CPTP}(H_B,H_C),
\]

则

\[
\mathcal F\circ\mathcal E
\in\operatorname{CPTP}(H_A,H_C).
\]

若 \(\mathcal E_1,\mathcal E_2\) 是 CPTP，则

\[
\mathcal E_1\otimes\mathcal E_2
\]

也是 CPTP。

#### 证明

恒等映射显然完全正且保迹。复合的完全正性由

\[
(\mathcal F\circ\mathcal E)\otimes\operatorname{id}
=
(\mathcal F\otimes\operatorname{id})
\circ
(\mathcal E\otimes\operatorname{id})
\]

得到，保迹性由迹的逐次保持得到。张量积的 Kraus 算子为

\[
K_i\otimes L_j,
\]

并且

\[
\sum_{i,j}
(K_i\otimes L_j)^\ast(K_i\otimes L_j)
=
\left(\sum_iK_i^\ast K_i\right)
\otimes
\left(\sum_jL_j^\ast L_j\right)
=
I\otimes I.
\]

结合有限维张量积的结合律、单位对象 \(\mathbb C\) 和交换对称子，得到对称幺半范畴结构。证毕。

### 定义 28.5（伴随映射）

相对于 Hilbert--Schmidt 内积

\[
\langle X,Y\rangle_{\mathrm{HS}}
=
\operatorname{tr}(X^\ast Y),
\]

定义 \(\mathcal E^\ast\) 为满足

\[
\operatorname{tr}(Y^\ast\mathcal E(X))
=
\operatorname{tr}((\mathcal E^\ast(Y))^\ast X)
\]

的唯一线性映射。若 \(\mathcal E\) 保迹，则

\[
\mathcal E^\ast(I)=I.
\]

因此 CPTP 映射的伴随是首一完全正映射。量子网络中的“局部观察”应使用 \(\mathcal E^\ast\) 作用在观察量上，而不是把观察量和状态混为同一类型。

### 定义 28.6（POVM 输出映射）

有限输出集 \(A\) 上的 POVM 是一族正半定算子

\[
(M_a)_{a\in A},
\qquad
M_a\succeq0,
\qquad
\sum_{a\in A}M_a=I_H.
\]

它定义概率映射

\[
\operatorname{out}_M:\mathsf D(H)\to\Delta(A),
\qquad
\operatorname{out}_M(\rho)(a)
=
\operatorname{tr}(M_a\rho).
\]

非负性来自 \(M_a,\rho\succeq0\)，归一化来自 \(\sum_aM_a=I_H\)。

---

## 29. FIB 五态概率律作为量子系统的可验证经典扇区

### 定义 29.1（对角嵌入）

令

\[
H_\Sigma=\mathbb C^\Sigma
\]

具有标准基 \((|s\rangle)_{s\in\Sigma}\)。定义

\[
\iota_\Sigma:\Delta(\Sigma)\to\mathsf D(H_\Sigma),
\qquad
\iota_\Sigma(p)
=
\sum_{s\in\Sigma}p_s|s\rangle\langle s|.
\]

该映射把 FIB 概率律嵌入量子状态空间的对角子集。

定义退相干映射

\[
\mathsf{Dec}_\Sigma(X)
=
\sum_{s\in\Sigma}
\langle s|X|s\rangle
|s\rangle\langle s|.
\]

它是 CPTP，并满足

\[
\mathsf{Dec}_\Sigma\circ\iota_\Sigma
=
\iota_\Sigma.
\]

### 定义 29.2（随机核的量子提升）

令 \(W(a\mid s)\) 是从 \(\Sigma\) 到有限集合 \(A\) 的随机核。定义

\[
\mathcal E_W(X)
=
\sum_{a\in A}\sum_{s\in\Sigma}
W(a\mid s)
\langle s|X|s\rangle
|a\rangle\langle a|.
\]

其 Kraus 算子为

\[
K_{a,s}
=
\sqrt{W(a\mid s)}\,|a\rangle\langle s|.
\]

### 定理 29.3（FIB 粗粒化的 CPTP 实现）

\(\mathcal E_W\) 是 CPTP，且对所有 \(p\in\Delta(\Sigma)\) 有

\[
\mathcal E_W(\iota_\Sigma(p))
=
\iota_A(Wp),
\]

其中

\[
(Wp)_a
=
\sum_{s\in\Sigma}W(a\mid s)p_s.
\]

#### 证明

由随机核归一化，

\[
\sum_{a,s}K_{a,s}^\ast K_{a,s}
=
\sum_s
\left(\sum_aW(a\mid s)\right)
|s\rangle\langle s|
=
I_{H_\Sigma}.
\]

所以 \(\mathcal E_W\) 是 CPTP。对角状态代入定义：

\[
\begin{aligned}
\mathcal E_W(\iota_\Sigma(p))
&=
\sum_{a,s}
W(a\mid s)p_s|a\rangle\langle a|\\
&=
\sum_a(Wp)_a|a\rangle\langle a|\\
&=
\iota_A(Wp).
\end{aligned}
\]

证毕。

### 推论 29.4（FIB seam 的量子表示）

令

\[
D=\operatorname{diag}(d_s)_{s\in\Sigma},
\qquad
d=(1,-1,0,-1,1).
\]

则

\[
D=D^\ast,
\qquad
\operatorname{tr}D=0.
\]

若 \(p_\kappa-p_{\kappa'}=(\kappa-\kappa')d\)，则

\[
\iota_\Sigma(p_\kappa)
-
\iota_\Sigma(p_{\kappa'})
=
(\kappa-\kappa')D.
\]

所以 \(\kappa\) 隐藏方向在量子载体中成为一个对角、迹为零的 Hermitian 扰动。它仍然是有限线性代数对象，并不需要把 \(\kappa\) 解释为物理叠加振幅。

### 命题 29.5（经典随机读出的 Fisher 收缩可由 CPTP 读出实现）

令 \(p_\theta\) 是 FIB 概率族，令 \(W\) 为随机核。对角提升满足

\[
\mathcal E_W(\iota_\Sigma(p_\theta))
=
\iota_A(Wp_\theta).
\]

因此输出 Fisher 信息正是前文定理 5.2 的 \(\mathcal I_{\mathrm{out}}\)，并满足

\[
\mathcal I_{\mathrm{out}}\le\mathcal I_{\mathrm{in}}.
\]

证明只使用定理 29.3 和定理 5.2。这里的结论是测量后经典 Fisher 信息的收缩，不等同于尚未定义的量子 Fisher 信息。

---

## 30. 有限 triangle quantum network

### 定义 30.1（三角量子源）

取三个有限维边 Hilbert 空间

\[
H_{AB},\qquad H_{BC},\qquad H_{CA},
\]

以及三个边源状态

\[
\omega_{AB}\in\mathsf D(H_{AB}^{A}\otimes H_{AB}^{B}),
\]

\[
\omega_{BC}\in\mathsf D(H_{BC}^{B}\otimes H_{BC}^{C}),
\]

\[
\omega_{CA}\in\mathsf D(H_{CA}^{C}\otimes H_{CA}^{A}).
\]

三角网络的独立源状态定义为

\[
\Omega
=
\omega_{AB}\otimes\omega_{BC}\otimes\omega_{CA}.
\]

这里“独立”只表示张量积结构。若边源本身是纠缠态，\(\Omega\) 仍是量子网络状态，但它不必具有经典隐变量分解。

### 定义 30.2（局部节点信道）

设

\[
\mathcal A:
\mathsf L(H_{CA}^{A}\otimes H_{AB}^{A})
\to
\mathsf L(K_A),
\]

\[
\mathcal B:
\mathsf L(H_{AB}^{B}\otimes H_{BC}^{B})
\to
\mathsf L(K_B),
\]

\[
\mathcal C:
\mathsf L(H_{BC}^{C}\otimes H_{CA}^{C})
\to
\mathsf L(K_C)
\]

均为 CPTP。网络输出状态为

\[
\rho_{ABC}
=
(\mathcal A\otimes\mathcal B\otimes\mathcal C)(\Omega),
\]

其中输入张量因子按各节点收到的两条边重新排列。

给定 POVM

\[
(M_a^A)_a,\qquad
(M_b^B)_b,\qquad
(M_c^C)_c,
\]

定义输出分布

\[
P(a,b,c)
=
\operatorname{tr}
\left[
(M_a^A\otimes M_b^B\otimes M_c^C)\rho_{ABC}
\right].
\]

### 定理 30.3（有限量子三角分布的归一化）

上式定义合法概率分布：

\[
P(a,b,c)\ge0,
\qquad
\sum_{a,b,c}P(a,b,c)=1.
\]

#### 证明

所有 POVM 元素和输出状态均正半定，所以每个概率非负。对所有输出求和：

\[
\sum_{a,b,c}P(a,b,c)
=
\operatorname{tr}
\left[
(I_{K_A}\otimes I_{K_B}\otimes I_{K_C})\rho_{ABC}
\right]
=
\operatorname{tr}\rho_{ABC}
=
1.
\]

证毕。

### 定理 30.4（经典 triangle-local 是量子网络的对角子类）

假设每个边源都是共享经典寄存器的对角状态，例如

\[
\omega_{AB}
=
\sum_{\alpha}\mu_{AB}(\alpha)
|\alpha\rangle\langle\alpha|_A
\otimes
|\alpha\rangle\langle\alpha|_B,
\]

其余两条边类似。假设节点信道在这些对角输入上先进行经典读取，再输出对角状态。则存在随机核

\[
A(a\mid\beta,\gamma),\quad
B(b\mid\gamma,\alpha),\quad
C(c\mid\alpha,\beta)
\]

使

\[
P(a,b,c)
=
\sum_{\alpha,\beta,\gamma}
\mu_{AB}(\alpha)
\mu_{BC}(\beta)
\mu_{CA}(\gamma)
A(a\mid\gamma,\alpha)
B(b\mid\alpha,\beta)
C(c\mid\beta,\gamma).
\]

#### 证明

把三个对角源状态代入张量积，得到

\[
\Omega
=
\sum_{\alpha,\beta,\gamma}
\mu_{AB}(\alpha)\mu_{BC}(\beta)\mu_{CA}(\gamma)
|\alpha,\beta,\gamma\rangle\langle\alpha,\beta,\gamma|.
\]

对角节点信道在每个输入三元组上给出一个合法输出分布。节点独立作用使输出条件概率分解为三个局部核的乘积。对 \(\alpha,\beta,\gamma\) 求和即可得到公式。证毕。

该定理只证明经典 triangle-local 分布嵌入量子网络的一个对角子类。一般纠缠源的量子三角分布不能由这一定理自动降为经典 triangle-local 分布。

---

## 31. 量子信道的 Dirichlet 单调性

前文的图 Dirichlet 形式使用向量差。量子网络中对应的有限维对象是状态之间的 trace-norm 差。

### 定义 31.1（量子图场）

令 \(G=(V,E,w)\) 为有限无向图，\(w_e\ge0\)。在每个节点 \(v\) 放置

\[
\rho_v\in\mathsf D(H).
\]

定义量子图场的 trace-norm Dirichlet 能量：

\[
\mathcal Q_G^{(1)}(\rho)
=
\sum_{e=(u,v)\in E}
w_e\|\rho_u-\rho_v\|_1^2.
\]

这是一个非负函数。它只测量节点状态之间的可区分性，不假设连续空间或物理距离。

### 定理 31.2（CPTP 分量作用的 Dirichlet 收缩）

设 \(\mathcal E:\mathsf L(H)\to\mathsf L(K)\) 为 CPTP。定义

\[
(\mathcal E_\ast\rho)_v=\mathcal E(\rho_v).
\]

则

\[
\boxed{
\mathcal Q_G^{(1)}(\mathcal E_\ast\rho)
\le
\mathcal Q_G^{(1)}(\rho).
}
\]

#### 证明

对 Hermitian \(X\)，trace norm 的对偶表达为

\[
\|X\|_1
=
\sup_{\|A\|_\infty\le1}
\operatorname{tr}(AX).
\]

由于 \(\mathcal E^\ast\) 是首一正映射，Kadison 不等式给出

\[
\|\mathcal E^\ast(A)\|_\infty
\le
\|A\|_\infty.
\]

因此

\[
\begin{aligned}
\|\mathcal E(X)\|_1
&=
\sup_{\|A\|_\infty\le1}
\operatorname{tr}(A\mathcal E(X))\\
&=
\sup_{\|A\|_\infty\le1}
\operatorname{tr}(\mathcal E^\ast(A)X)\\
&\le
\|X\|_1.
\end{aligned}
\]

每个 \(\rho_u-\rho_v\) 都是 Hermitian，故

\[
\|\mathcal E(\rho_u)-\mathcal E(\rho_v)\|_1
\le
\|\rho_u-\rho_v\|_1.
\]

平方并乘以 \(w_e\)，对所有边求和即得结论。证毕。

### 推论 31.3（与 FIB Dirichlet 形式的相容）

若所有 \(\rho_v\) 都是对角 FIB 状态

\[
\rho_v=\iota_\Sigma(p_v),
\]

则

\[
\|\rho_u-\rho_v\|_1
=
\|p_u-p_v\|_1.
\]

若 \(\mathcal E=\mathcal E_W\) 来自随机核 \(W\)，则

\[
\mathcal Q_G^{(1)}(Wp)
\le
\mathcal Q_G^{(1)}(p).
\]

因此，FIB 概率场的粗粒化是量子 CPTP Dirichlet 收缩定理在对角扇区的限制。

### 定义 31.4（相对熵与量子信息收缩接口）

对 \(\rho,\sigma\in\mathsf D(H)\)，在

\[
\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma
\]

时定义

\[
D(\rho\|\sigma)
=
\operatorname{tr}
\bigl[
\rho(\log\rho-\log\sigma)
\bigr],
\]

否则定义 \(D(\rho\|\sigma)=+\infty\)。

### 定理 31.5（CPTP 相对熵数据处理）

对任意 CPTP 映射 \(\mathcal E\)，有

\[
\boxed{
D(\mathcal E(\rho)\|\mathcal E(\sigma))
\le
D(\rho\|\sigma).
}
\]

这是有限维量子相对熵的数据处理定理。其形式化证明可以沿以下闭合路径展开：先用 Stinespring 表示将 \(\mathcal E\) 写成等距嵌入后偏迹，再证明偏迹下相对熵单调，最后使用等距共轭下相对熵不变。当前文件把它登记为外部有限维定理输入。若将其纳入 Lean，必须分别形式化矩阵对数、支撑条件、偏迹和 Klein 不等式。

该定理的语义边界是明确的：它证明量子信道不能增加相对熵区分度，不直接给出引力、时空或物理热力学定律。

---

## 32. 量子网络的逆极限静态场

### 定义 32.1（量子层载体）

对每个层级 \(j\)，取有限维 Hilbert 空间 \(H_j\)，并取非空紧凸子集

\[
K_j\subseteq\mathsf D(H_j).
\]

令

\[
q_{j+1,j}:K_{j+1}\to K_j
\]

是由 CPTP 映射限制得到的连续仿射映射。

### 定理 32.2（量子 CPTP 逆极限的非空性）

若每个

\[
q_{j+1,j}:K_{j+1}\to K_j
\]

都是满射，则

\[
\mathfrak Q
=
\varprojlim_j(K_j,q_{j+1,j})
\]

是非空紧凸集。

#### 证明

有限维状态空间中的闭有界集合是紧的，连续仿射像保持紧性和凸性。所有 \(K_j\) 的乘积

\[
\prod_jK_j
\]

由 Tychonoff 定理紧。相容条件

\[
q_{j+1,j}(\rho_{j+1})=\rho_j
\]

是闭条件，因此逆极限是紧闭子集。对任意有限层截断，由逐次满射可构造相容有限链。于是这些有限约束集合具有有限交性质。紧性给出全体约束的交非空。坐标逐点凸组合保持相容性，因此逆极限凸。证毕。

这个定理把原来的静态场逆极限扩展到量子载体。它只说明存在一族层间相容的密度矩阵。它不说明存在连续时空，也不说明逆极限具有光滑结构。

### 推论 32.3（量子层与 FIB 层的并行载体）

若

\[
C_j^Q
=
\Phi_j
\times
\Pi_j
\times
N_j
\times
Z_j
\times
K_j
\]

且每一层的 bonding map 在各分量上连续仿射并满射，则

\[
\varprojlim_jC_j^Q
\]

非空紧凸。前四个分量来自 Auric FIB 图场，\(K_j\) 是量子状态分量。这个乘积构造是一个类型化统一载体，不等同于物理统一场方程。

---

## 33. 连接、holonomy 与引力候选几何

若希望把“引力”放入数学骨架，最小的无物理定义是把网络边解释为状态空间之间的可组合传输，并测量闭环传输偏离恒等的程度。

### 定义 33.1（量子连接）

令 \(G=(V,E)\) 为有限有向图。为每条边 \(e:u\to v\) 指定一个 CPTP 映射

\[
\mathcal E_e:\mathsf L(H_u)\to\mathsf L(H_v).
\]

若路径

\[
\gamma=e_n\cdots e_1
\]

首尾 Hilbert 空间相同，则定义路径传输

\[
\mathcal E_\gamma
=
\mathcal E_{e_n}\circ\cdots\circ\mathcal E_{e_1}.
\]

### 定义 33.2（holonomy 与曲率缺陷）

对首尾同为 \(H\) 的闭环 \(\gamma\)，定义

\[
\mathcal H_\gamma=\mathcal E_\gamma,
\qquad
\Omega_\gamma=\mathcal H_\gamma-\operatorname{id}_{\mathsf L(H)}.
\]

称

\[
\Omega_\gamma=0
\]

为该闭环的平坦条件。对 Hermitian 输入使用诱导范数

\[
\|T\|_{1\to1,\mathrm{Herm}}
=
\sup_{X=X^\ast,\ X\ne0}
\frac{\|T(X)\|_1}{\|X\|_1}.
\]

定义曲率缺陷大小为

\[
\|\Omega_\gamma\|_{1\to1,\mathrm{Herm}}.
\]

这是网络传输的代数不一致量。它是候选几何量，不能直接宣称为 Einstein 曲率。

### 定理 33.3（holonomy 缺陷的望远镜界）

若每条 \(\mathcal E_{e_k}\) 都是 CPTP，则

\[
\|\mathcal E_{e_k}\|_{1\to1,\mathrm{Herm}}\le1.
\]

于是

\[
\boxed{
\|\Omega_\gamma\|_{1\to1,\mathrm{Herm}}
\le
\sum_{k=1}^n
\|\mathcal E_{e_k}-\operatorname{id}\|_{1\to1,\mathrm{Herm}}.
}
\]

#### 证明

令

\[
E_k=\mathcal E_{e_k}.
\]

代数恒等式给出

\[
E_n\cdots E_1-I
=
\sum_{k=1}^{n}
E_n\cdots E_{k+1}
(E_k-I)
E_{k-1}\cdots E_1.
\]

CPTP 映射在 Hermitian trace norm 下是收缩，因此每个前后乘积的诱导范数不超过一。对上式取范数并使用三角不等式，得到

\[
\|E_n\cdots E_1-I\|
\le
\sum_{k=1}^n\|E_k-I\|.
\]

证毕。

该定理给出三角网络闭环的严格误差预算。如果每条边都接近恒等传输，则整个闭环的非平坦缺陷至多线性累积。

### 定义 33.4（图电阻度量）

给有限连通无向图 \(G=(V,E,w)\) 赋予正边权 \(w_e>0\)。令 \(B\) 为任意定向边界矩阵，\(W=\operatorname{diag}(w_e)\)，定义

\[
L_w=BWB^{\mathsf T}.
\]

对 \(u,v\in V\)，定义有效电阻

\[
R_w(u,v)
=
(e_u-e_v)^{\mathsf T}
L_w^\dagger
(e_u-e_v),
\]

其中 \(L_w^\dagger\) 是 Moore--Penrose 伪逆。

### 定理 33.5（有效电阻是度量）

\(R_w\) 满足：

\[
R_w(u,v)\ge0,
\qquad
R_w(u,v)=R_w(v,u),
\qquad
R_w(u,v)=0\Longleftrightarrow u=v,
\]

并且

\[
\sqrt{R_w(u,v)}
\]

满足三角不等式。因此 \(R_w\) 是有效电阻平方，\(\sqrt{R_w}\) 是由 Dirichlet 形式诱导的度量。

#### 证明

令

\[
T=L_w^{\dagger/2}.
\]

则

\[
R_w(u,v)
=
\|T(e_u-e_v)\|_2^2.
\]

对称性和非负性直接成立。图连通性说明 \(L_w\) 的核恰为常数向量，因此 \(T(e_u-e_v)=0\) 当且仅当 \(e_u=e_v\)，即 \(u=v\)。最后，\(\sqrt{R_w(u,v)}\) 是 Euclidean 空间中向量 \(T(e_u-e_v)\) 的距离，故满足三角不等式。证毕。

### 推论 33.6（边收缩与几何收缩）

若 \(w'_e\ge w_e\) 对所有边成立，则

\[
R_{w'}(u,v)\le R_w(u,v).
\]

#### 证明

有效电阻具有 Thomson 变分表达：

\[
R_w(u,v)
=
\min_{Bf=e_u-e_v}
\sum_{e\in E}\frac{f_e^2}{w_e}.
\]

增大 \(w_e\) 会逐项减小每个可行流的成本，故最小值不增。证毕。

如果给出一个具体的信道到边权函数

\[
\eta:\operatorname{CPTP}\to(0,\infty),
\qquad
w_e=\eta(\mathcal E_e),
\]

则 \(R_w\) 成为量子连接的候选可见几何。当前理论没有唯一指定 \(\eta\)，所以“信道产生引力度量”仍是桥接接口，而不是已证明的物理结论。

---

## 34. Hamiltonian、静态场与量子能级接口

### 定义 34.1（有限 Hamiltonian 通道）

令 \(H=H^\ast\) 是有限维 Hermitian 矩阵，定义

\[
\mathcal U_t(X)
=
e^{-itH}Xe^{itH}.
\]

则 \(\mathcal U_t\) 是 CPTP，且

\[
\mathcal U_{t+s}
=
\mathcal U_t\circ\mathcal U_s.
\]

### 定理 34.2（静态状态与能量守恒）

若 \(\rho_\ast\in\mathsf D(H)\) 满足

\[
[H,\rho_\ast]=0,
\]

则

\[
\mathcal U_t(\rho_\ast)=\rho_\ast
\]

对所有 \(t\) 成立。并且任意 \(\rho\in\mathsf D(H)\) 的能量期望

\[
E_H(\rho)=\operatorname{tr}(H\rho)
\]

满足

\[
E_H(\mathcal U_t(\rho))=E_H(\rho).
\]

#### 证明

交换关系给出

\[
e^{-itH}\rho_\ast e^{itH}=\rho_\ast.
\]

能量守恒由循环迹：

\[
\begin{aligned}
E_H(\mathcal U_t(\rho))
&=
\operatorname{tr}
\left(
He^{-itH}\rho e^{itH}
\right)\\
&=
\operatorname{tr}
\left(
e^{itH}He^{-itH}\rho
\right)\\
&=
\operatorname{tr}(H\rho).
\end{aligned}
\]

证毕。

### 定义 34.3（能级）

\(H\) 的谱

\[
\operatorname{Spec}(H)
=
\{E_1,\ldots,E_d\}
\]

定义为该有限量子模型的能级集合，按代数重数计数。

如果 \(H\) 由图 Dirichlet 矩阵、量子连接的对称化生成元或某个 FIB 扩张构造，那么这些 \(E_i\) 是该构造的谱值。将它们解释为物理能量，或者进一步解释为 RH 零点虚部，均需要额外的谱识别定理。

当前可严格写出的条件式桥接是：

\[
\begin{aligned}
&\text{若存在自伴 }H\text{，使其正则化谱行列式等于完成的 }\Xi\text{ 函数，}\\
&\text{则 }\Xi\text{ 的非平凡零点由 }H\text{ 的实谱参数化。}
\end{aligned}
\]

FIB、triangle network 和量子连接目前只提供构造候选 \(H\) 所需的有限输入类型，不自动给出该行列式恒等式。

---

## 35. 量子、FIB 与引力桥的保守账本

### Primitive

以下对象属于原始有限数学：

\[
\Sigma,\quad
\Delta(\Sigma),\quad
H,\quad
\mathsf D(H),\quad
\operatorname{CPTP},\quad
\otimes,\quad
\operatorname{tr},\quad
\text{POVM},\quad
G=(V,E,w),\quad
B,\quad
L_w.
\]

### Derived

以下结论由原始对象直接推出：

1. CPTP 映射的复合和张量积闭包；
2. FIB 概率律的对角量子嵌入；
3. 随机核的 measure--dephase--prepare CPTP 提升；
4. 有限 triangle quantum network 输出分布的归一化；
5. 经典 triangle-local 分布作为对角量子网络子类；
6. CPTP 对 trace-norm Dirichlet 能量的收缩；
7. 量子层载体在满射 bonding 下的逆极限非空性；
8. holonomy 缺陷的望远镜界；
9. 有效电阻的度量结构；
10. 有限 Hamiltonian 通道的静态性和能量守恒。

### Bridge

以下对象目前仍需要具体构造：

1. 从 FIB seam \(d\) 到非对角量子相干算子的自然提升；
2. 从有限 quantum triangle network 到完整 triangle-local inflation 证书的映射；
3. 从 CPTP 连接到唯一边权 \(\eta(\mathcal E_e)\)；
4. 从有效电阻或 holonomy 缺陷到 Einstein 曲率、引力势或时空度量；
5. 从 FIB/图 Dirichlet 生成元到自伴 Hamiltonian；
6. 从该 Hamiltonian 的正则化谱行列式到完成的 \(\Xi\) 函数；
7. 从量子能级到 RH 零点的重数保持和谱完备性。

因此当前“量子引力”在 Auric FIB 管线中的严格含义只能是：

\[
\boxed{
\begin{aligned}
&\text{量子层：有限维 CPTP 组合子和密度矩阵；}\\
&\text{网络层：独立源张量积与局部节点信道；}\\
&\text{场层：相容量子状态的逆极限；}\\
&\text{几何层：Dirichlet 形式、holonomy 缺陷和有效电阻；}\\
&\text{能级层：有限自伴算子的谱；}\\
&\text{物理解释：必须由独立桥接定理承担。}
\end{aligned}
}
\]

这套骨架把“引力”和“量子”都降为可检查的数学接口。它不从物理直觉反向定义数学对象，而是先在有限矩阵、凸集、图边界和谱理论中建立可形式化的闭环。



---

## 36. 外部量子网络锚点与证据边界

本节只登记外部结果在管线中的位置，不把外部论文的结论转写成 Auric FIB 的内部定理。

### 锚点 36.1（量子 inflation）

Smith、Wolfe 和 Spekkens 的 *Fully quantum inflation: quantum marginal problem constraints in the service of causal inference*（arXiv:2501.12320）把 inflation 方法推广到量子边缘问题，用量子边缘约束检验给定多方量子态是否兼容指定的量子因果结构，并专门讨论了 triangle scenario。

它支持本卷的类型分离：

\[
\text{经典 triangle-local 分布}
\subsetneq
\text{量子 triangle-network 输出}.
\]

它也给出下一步的形式化方向：在定义 30.1--30.2 的有限源状态和局部 CPTP 映射后，构造复制网络的量子边缘约束。当前文件尚未完成该 inflation 证书，因此不能从有限 CPTP 定义直接推出量子三角兼容性判定。

### 锚点 36.2（三角网络量子非局域性的实验语义）

Wang 等人的 *Experimental genuine quantum nonlocality in the triangle network*（arXiv:2401.15428）报告了三角网络结构中的量子相关实验，并针对 elegant distribution 给出量子非局域性的实验证据。

该结果只能作为以下桥接的实验语义背景：

\[
\text{有限量子源}
\longrightarrow
\text{局部节点测量}
\longrightarrow
\text{三角输出分布}.
\]

它不改变本卷的数学边界：实验相关性不提供 FIB 五态编码，也不证明任意 FIB 概率律具有三个独立量子源分解。

### 锚点 36.3（对本卷的最小影响）

外部量子网络结果对当前理论只增加两个可检验目标：

1. 给定有限 \(\omega_{AB},\omega_{BC},\omega_{CA}\) 和局部 CPTP 映射，生成完整输出态的量子 inflation 复制约束；
2. 给定 FIB 对角输出，判定它是否存在一个满足源独立性、维数上界和局部响应结构的量子 triangle lift。

在这两个目标完成以前，本文使用的关系仍然是：

\[
\text{FIB 对角量子嵌入}
\subseteq
\text{有限量子网络载体},
\]

而不是

\[
\text{任意 FIB 律}
=
\text{量子 triangle-network 律}.
\]



### 锚点 36.4（自旋网络中的纠缠与曲率）

*Curvature from multipartite entanglement in quantum gravity states*（Physical Review D 108, 046010, 2023）研究以图、自旋网络和非平凡 \(SU(2)\) holonomy 表示的量子几何，并分析多体纠缠与有界区域内禀曲率之间的关系。

它与本卷的关系是结构性的：

\[
\text{图连接}
+
\text{边 holonomy}
+
\text{量子态纠缠}
\longrightarrow
\text{曲率候选量}.
\]

本卷目前只使用一般有限 CPTP holonomy 缺陷

\[
\Omega_\gamma=\mathcal E_\gamma-\operatorname{id}
\]

和有效电阻度量。自旋网络论文并不证明这两个量等于其几何曲率；因此它只能支持后续构造的方向，不能升级当前的定理。

### 锚点 36.5（可叠加网络拓扑）

Arrighi、Durbec 和 Wilson 的 *Quantum networks theory*（Quantum 8, 1508, 2024）研究网络连接本身处于量子叠加的过程模型，包括连接、分裂和重连的相干演化。

这提示一个严格的后续扩展：把当前固定图 \(G=(V,E)\) 替换为有限图标签空间

\[
\mathcal G=\{G_1,\ldots,G_m\},
\]

并在

\[
\mathbb C^{\mathcal G}\otimes H_{\mathrm{field}}
\]

上定义 CPTP 映射。当前 PR 只处理固定图和固定层间 bonding，因此不包含量子叠加拓扑。该扩展必须先定义图标签的状态空间、重连信道和逆极限相容性，不能从现有 holonomy 定义直接推导。



## 36. 有限图上的离散曲率证书

本节把“引力”先改写成有限 Dirichlet 载体上的曲率稳定性证书。曲率在这里是由有限矩阵和有限求和定义的函数不等式。它不被解释为 Einstein 曲率，也不自动产生连续时空。

### 定义 36.1（有限可逆图与 Markov 生成元）

令 \(V\) 是有限集合，令 \(\mu_x>0\) 且 \(\sum_{x\in V}\mu_x=1\)。令 \(c_{xy}=c_{yx}\ge0\)，\(c_{xx}=0\)，并假设由 \(c_{xy}>0\) 生成的无向图连通。定义

\[
(Lf)(x)
=
\frac1{\mu_x}
\sum_{y\in V}c_{xy}\bigl(f(y)-f(x)\bigr).
\]

在

\[
\langle f,g\rangle_\mu
=
\sum_{x\in V}\mu_x f(x)g(x)
\]

上，\(L\) 是自伴且非正。记 \(A=-L\)。定义 Dirichlet 双线性型

\[
\mathcal E(f,g)
=
-\langle f,Lg\rangle_\mu
=
\frac12\sum_{x,y\in V}
c_{xy}\bigl(f(x)-f(y)\bigr)\bigl(g(x)-g(y)\bigr).
\]

于是 \(\mathcal E(f)=\mathcal E(f,f)\ge0\)，且连通性给出

\[
\ker A=\operatorname{span}\{\mathbf 1\}.
\]

### 定义 36.2（有限 carré du champ 与二阶型）

对实函数 \(f,g:V\to\mathbb R\)，定义

\[
\Gamma(f,g)
=
\frac12\left(
L(fg)-fLg-gLf
\right),
\qquad
\Gamma(f)=\Gamma(f,f).
\]

直接展开得到

\[
\Gamma(f,g)(x)
=
\frac1{2\mu_x}
\sum_yc_{xy}
\bigl(f(y)-f(x)\bigr)
\bigl(g(y)-g(x)\bigr),
\]

因此

\[
\sum_x\mu_x\Gamma(f)(x)=\mathcal E(f).
\]

定义二阶型

\[
\Gamma_2(f)
=
\frac12L\Gamma(f)-\Gamma(f,Lf).
\]

这里 \(\Gamma_2\) 是有限函数 \(V\to\mathbb R\)。所有量都是有限和与有限矩阵乘法，不需要先给出连续流形。

### 定义 36.3（有限 \(CD_G(K,\infty)\) 证书）

给定 \(K\in\mathbb R\)，称有限图满足 \(CD_G(K,\infty)\)，如果对任意 \(f:V\to\mathbb R\) 和任意 \(x\in V\)，有

\[
\Gamma_2(f)(x)\ge K\Gamma(f)(x).
\]

这一定义是一个可检查的有限二次型不等式。对于固定 \(G,\mu,c\)，最大的允许 \(K\) 是一个有限图证书，可通过有限维半正定条件或广义 Rayleigh 商验证。

### 定理 36.4（离散曲率控制谱隙与 Dirichlet 衰减）

设有限图满足 \(CD_G(K,\infty)\)，且 \(K>0\)。则：

1. 对任意 \(f\)，
   \[
   \sum_x\mu_x\Gamma_2(f)(x)
   =
   \|Lf\|_\mu^2,
   \qquad
   \|Lf\|_\mu^2\ge K\mathcal E(f).
   \]

2. 令 \(\lambda_1>0\) 为 \(A=-L\) 在常数正交子空间上的最小特征值，则
   \[
   \lambda_1\ge K.
   \]

3. 令 \(P_t=e^{tL}\)。则
   \[
   \mathcal E(P_tf)
   \le
   e^{-2Kt}\mathcal E(f).
   \]

#### 证明

由于 \(\sum_x\mu_xLh(x)=0\)，且

\[
\sum_x\mu_x\Gamma(f,Lf)(x)
=
-\langle f,L^2f\rangle_\mu,
\]

有

\[
\begin{aligned}
\sum_x\mu_x\Gamma_2(f)(x)
&=
\frac12\sum_x\mu_xL\Gamma(f)(x)
-
\sum_x\mu_x\Gamma(f,Lf)(x)\\
&=
\langle f,L^2f\rangle_\mu\\
&=
\|Lf\|_\mu^2.
\end{aligned}
\]

积分 \(CD_G(K,\infty)\) 即得第一项的不等式。

若 \(Af=\lambda f\)，且 \(f\perp_\mu\mathbf1\)，则 \(Lf=-\lambda f\)，从而

\[
\|Lf\|_\mu^2
=
\lambda^2\|f\|_\mu^2,
\qquad
\mathcal E(f)
=
\lambda\|f\|_\mu^2.
\]

因此 \(\lambda^2\ge K\lambda\)。对 \(\lambda>0\) 消去一个 \(\lambda\)，得到 \(\lambda\ge K\)。这证明第二项。

令 \(f_t=P_tf\)。由自伴性，

\[
\frac d{dt}\mathcal E(f_t)
=
2\langle Lf_t,-Lf_t\rangle_\mu
=
-2\|Lf_t\|_\mu^2
\le
-2K\mathcal E(f_t).
\]

Gronwall 不等式给出第三项。证毕。

这个定理把“场的稳定性”变成了明确的谱估计：\(K\) 是有限图热流的能量衰减率下界。它没有把 \(K\) 解释成物理引力常数。

### 定理 36.5（曲率证书对有效电阻的控制）

沿用定义 36.1，令

\[
b_{uv}(x)
=
\frac{\mathbf1_{\{x=u\}}}{\mu_u}
-
\frac{\mathbf1_{\{x=v\}}}{\mu_v}.
\]

则 \(b_{uv}\perp_\mu\mathbf1\)，并满足

\[
\langle b_{uv},f\rangle_\mu=f(u)-f(v).
\]

定义加权有效电阻

\[
R_\mu(u,v)
=
\langle b_{uv},A^\dagger b_{uv}\rangle_\mu,
\]

其中 \(A^\dagger\) 是 Moore–Penrose 伪逆。若 \(CD_G(K,\infty)\) 且 \(K>0\)，则

\[
\boxed{
R_\mu(u,v)
\le
\frac{\mu_u^{-1}+\mu_v^{-1}}{K}.
}
\]

#### 证明

定理 36.4 给出 \(A\ge K I\) 在常数正交子空间上的谱序。故

\[
A^\dagger\le K^{-1}I
\]

在该子空间上成立。于是

\[
R_\mu(u,v)
\le
K^{-1}\|b_{uv}\|_\mu^2
=
K^{-1}\left(\frac1{\mu_u}+\frac1{\mu_v}\right).
\]

证毕。

如果令 \(\phi_{uv}=A^\dagger b_{uv}\)，则 \(A\phi_{uv}=b_{uv}\) 且

\[
R_\mu(u,v)
=
\mathcal E(\phi_{uv}).
\]

因此曲率下界控制有限场对点源差分的静态响应幅度。这个响应是离散 Poisson 方程的解。把它称作“引力势”需要额外的物理桥接，数学定理本身只给出有效电阻和 Dirichlet 能量界。

### 定义 36.6（层级曲率数据）

对第 \(j\) 层的 \((V_j,\mu_j,c_j)\)，定义

\[
K_j^{\mathrm{BE}}
=
\sup\{K:\ CD_{G_j}(K,\infty)\text{ 成立}\}.
\]

这给出一个完全由有限层矩阵确定的曲率序列

\[
(K_0^{\mathrm{BE}},K_1^{\mathrm{BE}},\ldots).
\]

若层间 bonding 还满足额外的 \(\Gamma\)-交换和 \(\Gamma_2\)-单调条件，才可以比较 \(K_j^{\mathrm{BE}}\) 与 \(K_{j+1}^{\mathrm{BE}}\)。Dirichlet 能量收缩本身并不自动推出曲率下界单调性。

## 37. 有限量子网络的 detailed-balance Dirichlet 曲率

本节使用有限维矩阵定义量子层。为了避免把经典 \(CD_G\) 不加证明地推广到非交换代数，量子曲率先定义为 detailed-balance 生成元上的二次型谱证书。

### 定义 37.1（有限 detailed-balance 量子半群）

令 \(H\) 是有限维复 Hilbert 空间，令 \(\sigma\in\mathsf D(H)\) 严格正定。对 \(A,B\in\mathsf L(H)\)，定义 GNS 内积

\[
\langle A,B\rangle_\sigma
=
\operatorname{tr}
\left(
\sigma^{1/2}A^\ast\sigma^{1/2}B
\right).
\]

令 \(\mathcal L:\mathsf L(H)\to\mathsf L(H)\) 是有限维 CPTP 半群 \(T_t=e^{t\mathcal L}\) 的生成元，满足

\[
\mathcal L^\ast(\sigma)=0
\]

以及 GNS detailed balance

\[
\langle A,\mathcal L B\rangle_\sigma
=
\langle\mathcal L A,B\rangle_\sigma.
\]

定义量子 Dirichlet 型

\[
\mathcal E_\sigma(A)
=
\langle A,-\mathcal L A\rangle_\sigma.
\]

在 \(A\) 为常数方向之外，\(\mathcal E_\sigma(A)\ge0\)。

### 定义 37.2（量子二阶型曲率证书）

给定 \(K\in\mathbb R\)，称 \((\mathcal L,\sigma)\) 满足 \(QCD(K)\)，如果对所有满足

\[
\langle I,A\rangle_\sigma=0
\]

的 \(A\) 都有

\[
\langle\mathcal L A,\mathcal L A\rangle_\sigma
\ge
K\mathcal E_\sigma(A).
\]

左侧是生成元的二阶 Hilbert 型，右侧是一阶 Dirichlet 型。这个定义是有限矩阵不等式。它不宣称已经得到一般意义的非交换 Bakry–Émery \(\Gamma_2\)。

### 定理 37.3（量子曲率控制谱隙和衰减）

若 \(QCD(K)\) 且 \(K>0\)，则：

1. \(-\mathcal L\) 在 \(I^\perp\) 上的每个非零特征值 \(\lambda\) 满足 \(\lambda\ge K\)；
2. 对所有 \(A\)，
   \[
   \mathcal E_\sigma(T_tA)
   \le
   e^{-2Kt}\mathcal E_\sigma(A);
   \]
3. 记
   \[
   A_0=A-\langle I,A\rangle_\sigma I,
   \]
   则
   \[
   \|T_tA_0\|_\sigma
   \le
   e^{-Kt}\|A_0\|_\sigma.
   \]

#### 证明

由于 detailed balance，\(-\mathcal L\) 是有限维 GNS Hilbert 空间上的自伴非负算子。若 \(-\mathcal L A=\lambda A\)，且 \(A\perp_\sigma I\)，则

\[
\|\mathcal L A\|_\sigma^2
=
\lambda^2\|A\|_\sigma^2,
\qquad
\mathcal E_\sigma(A)
=
\lambda\|A\|_\sigma^2.
\]

\(QCD(K)\) 给出 \(\lambda^2\ge K\lambda\)，所以 \(\lambda\ge K\)。这证明第一项。

令 \(A_t=T_tA\)。由自伴性，

\[
\frac d{dt}\mathcal E_\sigma(A_t)
=
2\langle\mathcal L A_t,-\mathcal L A_t\rangle_\sigma
=
-2\|\mathcal L A_t\|_\sigma^2
\le
-2K\mathcal E_\sigma(A_t).
\]

Gronwall 不等式给出第二项。

第一项的谱结论还给出 \(-\mathcal L\ge K I\) 在 \(I^\perp\) 上。于是

\[
\frac d{dt}\|T_tA_0\|_\sigma^2
=
-2\mathcal E_\sigma(T_tA_0)
\le
-2K\|T_tA_0\|_\sigma^2.
\]

再次应用 Gronwall 得到第三项。证毕。

### 定理 37.4（独立量子边的张量化）

对有限边指标集 \(E\)，令

\[
H=\bigotimes_{e\in E}H_e,
\qquad
\sigma=\bigotimes_{e\in E}\sigma_e.
\]

每个边生成元 \(\mathcal L_e\) 在 \((H_e,\sigma_e)\) 上满足 \(QCD(K_e)\)。将其提升为

\[
\widehat{\mathcal L}_e
=
I_{\bar e}\otimes\mathcal L_e,
\qquad
\mathcal L_{\mathrm{net}}
=
\sum_{e\in E}\widehat{\mathcal L}_e.
\]

则 \(\mathcal L_{\mathrm{net}}\) 满足

\[
QCD\left(\min_{e\in E}K_e\right).
\]

#### 证明

不同边作用在不同张量因子上，因此 \(\widehat{\mathcal L}_e\) 两两交换，并且在乘积 GNS 内积下自伴。有限维谱定理给出共同特征基。共同特征向量的 \(-\mathcal L_{\mathrm{net}}\) 特征值为

\[
\lambda_{\mathrm{net}}
=
\sum_{e\in E}\lambda_e,
\]

其中每个 \(\lambda_e\) 非负。若共同特征向量不在常数方向，则至少一个 \(\lambda_e>0\)，故

\[
\lambda_{\mathrm{net}}
\ge
\min_{e\in E}K_e.
\]

对共同特征基逐项应用

\[
\lambda_{\mathrm{net}}^2
\ge
\left(\min_eK_e\right)\lambda_{\mathrm{net}}
\]

并线性延拓，得到 \(QCD(\min_eK_e)\)。证毕。

这个张量化结果与 triangle quantum network 的源积结构相容。它只处理独立边生成元的乘积模型。一般节点 CPTP 信道会引入非交换耦合，除非额外证明 detailed balance、共同不变状态和相应二阶型不等式，否则不能使用该定理。

## 38. 离散曲率、量子网络与“引力”之间的桥接账本

当前可严格登记的对象是：

\[
\begin{array}{c|c}
\text{数学层} & \text{可验证对象}\\
\hline
\text{静态场} & (\Phi_j,\Pi_j,N_j,Z_j)\\
\text{经典几何} & \mathcal E_j,\Gamma_j,\Gamma_{2,j},K_j^{\mathrm{BE}}\\
\text{有效距离} & R_{\mu_j}(u,v),\sqrt{R_{\mu_j}(u,v)}\\
\text{量子网络} & (H_j,\sigma_j,\mathcal L_j,T_{j,t})\\
\text{量子几何} & \mathcal E_{\sigma_j},QCD(K_j^Q)\\
\text{逆极限} & \varprojlim_j C_j,\quad \varprojlim_jK_j
\end{array}
\]

由这些定义已经证明：

\[
\begin{aligned}
CD_G(K,\infty)
&\Longrightarrow
\lambda_1(A)\ge K
\Longrightarrow
\mathcal E(P_tf)\le e^{-2Kt}\mathcal E(f),\\
CD_G(K,\infty)
&\Longrightarrow
R_\mu(u,v)\le
(\mu_u^{-1}+\mu_v^{-1})/K,\\
QCD(K)
&\Longrightarrow
\operatorname{Spec}(-\mathcal L|_{I^\perp})\subseteq[K,\infty),\\
QCD(K)
&\Longrightarrow
\mathcal E_\sigma(T_tA)\le e^{-2Kt}\mathcal E_\sigma(A).
\end{aligned}
\]

“场产生引力”的纯数学版本只能先写成：

\[
\text{静态 Dirichlet 场}
\longrightarrow
\text{有限曲率证书}
\longrightarrow
\text{谱隙与响应界}
\longrightarrow
\text{有效网络几何}.
\]

要把这条链升级为物理引力，还需独立证明至少一个具体桥接：

1. 从 \(K_j^{\mathrm{BE}}\) 或 \(K_j^Q\) 到某个度量测度极限的 Ricci 型下界；
2. 从该度量测度极限到光滑黎曼结构的维数、非塌缩、正则性和坐标重构；
3. 从静态 Poisson 响应到一个具有明确单位和变分原理的物理势；
4. 从曲率证书到 Einstein 型场方程，或证明该方程是某个有限能量泛函的 Euler–Lagrange 方程；
5. 从量子网络生成元到同一极限几何中的量子 Hamiltonian 或谱三元组；
6. 从此自伴谱数据到 RH 的完整零点空间和谱行列式恒等式。

因此，当前理论只支持以下条件式陈述：

\[
\boxed{
\begin{aligned}
&\text{若有限层曲率证书在 bonding 下具有统一下界，}\\
&\text{且 Dirichlet 形式满足共同宿主空间中的 Mosco 条件，}\\
&\text{则可以尝试构造带稳定谱隙和有限响应界的度量测度极限。}
\end{aligned}
}
\]

这仍是数学极限问题，不是已经证明的引力理论。尤其不能从 \(CD_G\)、\(QCD\)、有效电阻或 holonomy 单独推出 Ricci 张量、Einstein 张量、时空因果结构或物理能量。

### 外部数学锚点

离散熵曲率与 Markov 链的研究已经给出另一条成熟的几何路线：有限 Markov 链可用熵沿离散运输度量的凸性定义 Ricci 型下界，并证明曲率界的张量化。该路线可作为本节 \(CD_G\) 证书之后的后续桥接，但不能把两种曲率定义视为同一对象。参考 Erbar--Maas, *Ricci curvature of finite Markov chains via convexity of the entropy*, arXiv:1111.2687。genui{"citation":{"ref":"turn22academia0"}}

因此，当前文件同时保留两条可检验路线：

\[
\begin{aligned}
&\text{有限 }CD_G\text{ 二次型}
\longrightarrow
\text{谱隙、热流衰减、有效电阻界};\\
&\text{离散熵凸性曲率}
\longrightarrow
\text{运输度量、熵梯度流、可能的 metric-measure 极限}.
\end{aligned}
\]

两条路线的共同输入是有限 Markov/Dirichlet 数据。它们的极限识别、相互等价及其与物理引力的关系，都必须另行证明。
