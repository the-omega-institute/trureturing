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
