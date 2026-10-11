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
    (T : TriangleLiftFinite Λα Λβ Λγ)
    (a b c : Bool) : ℝ :=
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

对素数驱动，同样优先使用有限版本：

~~~lean
structure ArithmeticEncoding (C : Type) where
  encode : C → Law
  valid : ∀ c, IsProbability (encode c)
  visible_driver : C → ℝ × ℝ × ℝ
  visible_correct :
    ∀ c, visible (encode c) = visible_driver c
~~~

这样可以把“算术输入改变哪一个 FIB 模式质量”作为一个可计算函数，而不是用模式名称相似性代替编码定义。

