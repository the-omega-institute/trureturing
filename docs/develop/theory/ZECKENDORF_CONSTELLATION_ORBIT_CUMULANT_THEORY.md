# Zeckendorf 构型—零点轨道累积量理论

## Zeckendorf–Constellation Orbit-Cumulant Theory（ZCOCT）

**副标题：加法素数构型、镜像零点“纠缠”、三轴喷射深度与相关完备化 ζ**

**理论状态：** 仓库专属综合理论；包含可立即形式化的定理、条件定理、开放桥与可证伪猜想。  
**取阅截点：** 2026-09-03，Asia/Singapore；仓库 `the-omega-institute/trureturing`，`dev` 分支。  
**建议落点：** `docs/develop/theory/ZECKENDORF_CONSTELLATION_ORBIT_CUMULANT_THEORY.md`  
**重要声明：** 本卷既不是黎曼猜想的证明，也不是黎曼猜想为假的证明；“量子纠缠”只在给出张量分解、状态和非可分离性判据以后才按量子意义使用。

---

## 摘要

本理论把四类原本分散的对象放入一个统一但分层的系统：

1. **素数构型**不是 Euler 乘积中各素数指数的独立性，而是同一个整数经过多个加法平移以后，事件
   \[
   n+h_1,\ldots,n+h_k
   \]
   同时呈现素性所形成的联合相关；
2. **非平凡零点**不是彼此独立的点，而是共轭与函数方程生成的 Klein 四群轨道；
3. **Zeckendorf 编码**不被用作任意实数的虚假有限编码，而被严格分成：
   - 整数构型的有限规范编码；
   - 实零点坐标的无限分辨率 Zeckendorf 线程；
   - 镜像轨道中只翻转符号页、保留幅值线程的“反码”；
4. **jet 深度**具有三个不同的等级：
   \[
   \boxed{(k,m,2r)}
   \]
   其中 \(k\) 是加法构型相关阶数，\(m\) 是零点重数，\(2r\) 是镜像对称下首次可见的横向偶阶缺陷。

核心对象是一个右半平面上无条件定义的**相关完备化 ζ 生成元**。对有限构型
\[
H=\{h_1,\ldots,h_k\},
\]
在平方零源变量代数中定义
\[
\mathcal M_H(\sigma)
=
\mathbb E_{\sigma}
\prod_{h\in H}
\bigl(1+\varepsilon_h\Lambda(N+h)\bigr),
\qquad
\mathbb P_\sigma(N=n)=\frac{n^{-\sigma}}{\zeta(\sigma)}.
\]
其对数
\[
\mathcal K_H(\sigma)=\log\mathcal M_H(\sigma)
\]
的 \(\varepsilon_A\) 系数，恰为平移族
\[
\{\Lambda(N+h):h\in A\}
\]
的联合累积量。因此：

- 孪生素数构型是二阶 connected jet；
- 素数三元组是三阶 connected jet；
- 素数四元组是四阶 connected jet；
- 所有有限构型构成一个相关完备化塔。

零点侧则以
\[
J(s)=1-\overline s
\]
为同高度镜像。若
\[
\rho=\frac12+\delta+i\gamma,
\]
则
\[
J\rho=\frac12-\delta+i\gamma.
\]
镜像对自动消去所有横向奇阶 jet，却保留
\[
\delta^2,\delta^4,\ldots.
\]
故完整对称并不使 RH 不可观察；它只使**一阶符号不可观察**，二阶正缺陷仍能严格检测离线深度。

本理论最终提出一个开放的 **Trace–Jet Bridge**：存在一个带构型源变量的 completed determinant，其第 \(k\) 个源混合 jet 在素数侧给出 \(k\)-点加法累积量，在零点侧给出 \(k\)-级谱相关电荷。Montgomery 型二点关系是这一桥的已知影子，而不是整座桥本身。

---

# 0. 证据等级与仓库缺口

本卷使用以下标签。

- **[repo-closed]**：仓库已有 Lean 定理，且本卷只消费其结论。
- **[derived]**：由已有仓库定理和标准代数直接推出，但尚未发现同名整体 owner。
- **[proposed theorem]**：精确、近期可形式化，不依赖 RH。
- **[conditional theorem]**：前件明确，可在前件下严格证明。
- **[conjecture]**：尚未建立的数学桥；必须可证伪。
- **[model]**：一种解释性提升，不声称由经典 ζ 自动导出。

## 0.1 已有而不应重证的仓库支点

本理论消费下列已冻结支点：

1. `D5/S3/Weil/ZetaBridge/ConvolutionSquareOffLineOrbits`  
   离线非实零点形成四点轨道，轨道卷积平方贡献可化为单项实部的四倍。

2. `D5/S3/Zeros/Symmetry/CriticalDampingFlatness`  
   有限零点窗的中心化双曲余弦缺陷为零，当且仅当全部横向偏移均为零。

3. `D5/S3/Zeros/CriticalZeroTransverseGap`  
   \(r\) 重临界零点的强度横向首项次数为 \(2r\)。

4. `D5/S3/Analytic/Boundary/InteriorCurvatureCriterion`  
   右侧离线零点产生质量为 \(2\pi m_\rho\) 的 Riesz 原子；该内部测度为零等价于 RH 型零点定位。

5. `D5/S3/Analytic/PoissonPhaseHolonomy/PairwisePoissonHolonomyEnergy`  
   正横向深度下，二点相位 holonomy 能量非负、共同高度平移不变，并检测高度差。

6. `D5/S3/Observer/AgencyHolonomy/ScalarMemoryBlindness` 与  
   `GoldenScalarDihedralBlindness`  
   标量 Euler/完成读数可以遗忘有序素数词和隐藏 memory。

7. `D5/S3/Observer/AgencyHolonomy/OrderedPrimeHolonomyCasimir`  
   有序素数 holonomy 的一阶响应消失，而负二阶响应读出平方 winding 的正和。

8. `D5/S3/Weil/ZetaBridge/ZeroSumEnumerationInvariance`  
   对称零点和及其极限不依赖零点枚举，也不依赖收敛见证。

9. `D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf`、  
   `D5/S1/Deficit/ZeckendorfDisplacementReading`、  
   `D5/S3/Analytic/GoldenEulerBeta`  
   已建立 Zeckendorf 数位、黄金替换上移和 O-5 指数账户之间的基础桥。

10. `D5/S3/Observer/AgencyHolonomy/GoldenCharacterQuotient`  
    模 \(5\) 二次特征在非分歧素数上给出 \(\pm1\) 商，并证明标量乘积遗忘词序。

11. `D5/S3/Weil/ZetaBridge/PrimeJumpDecomposition`  
    素数项已被重写为 coherent mass 减去非负平移能量。

12. 仓库理论层已提出“相关阶数轴”
    \[
    (S,k,b,a,t),
    \qquad S\subseteq\mathbb P_{\mathrm{finite}},
    \]
    但尚未把 Hardy–Littlewood 加法构型、connected cumulant、Zeckendorf 镜像线程和零点轨道 jet 合为一个 kernel-ready 理论。

## 0.2 本卷新增的整体 owner

截至取阅截点，本卷以下组合结构尚未发现单一 owner：

\[
\boxed{
\text{prime constellation}
\longrightarrow
\text{local residue automata}
\longrightarrow
\text{connected source jets}
\longrightarrow
\text{zero-orbit cumulants}
\longrightarrow
\text{signed Zeckendorf threads}.
}
\]

---

# 第一部　零点对称不是对称破缺

## 1. Klein 四群零点轨道

定义三个作用：

\[
C(s)=\overline s,
\qquad
R(s)=1-s,
\qquad
J(s)=1-\overline s.
\]

它们满足：

\[
C^2=R^2=J^2=1,
\qquad
CR=RC=J.
\]

故：

\[
G_\zeta=\{1,C,R,J\}\cong C_2\times C_2.
\]

对

\[
\rho=\frac12+\delta+i\gamma
\]

有：

\[
\begin{aligned}
C\rho&=\frac12+\delta-i\gamma,\\
R\rho&=\frac12-\delta-i\gamma,\\
J\rho&=\frac12-\delta+i\gamma.
\end{aligned}
\]

### 命题 1.1（轨道类型）

在抽象对称零点系统中：

\[
|\operatorname{Orb}(\rho)|
=
\begin{cases}
4,&\delta\neq0,\ \gamma\neq0,\\
2,&\delta=0,\ \gamma\neq0,\\
2,&\delta\neq0,\ \gamma=0,\\
1,&\delta=\gamma=0.
\end{cases}
\]

对经典非平凡 ζ 零点，实轴情形应另由
\[
0<\sigma<1\Longrightarrow\zeta(\sigma)\neq0
\]
排除。

### 定义 1.2（同高度镜像对）

在上半平面中，把

\[
\left\{
\frac12+\delta+i\gamma,\,
\frac12-\delta+i\gamma
\right\}
\]

称为一个 **transverse mirror pair**。

它不是完整四元轨道，而是 \(J\) 的二元轨道。

---

## 2. 完整对称不推出 RH

令 \(z=s-\frac12\)，并取 \(\delta,\gamma\neq0\)。定义：

\[
P_{\delta,\gamma}(s)
=
\bigl((z-\delta)^2+\gamma^2\bigr)
\bigl((z+\delta)^2+\gamma^2\bigr).
\]

其零点恰为：

\[
\frac12\pm\delta\pm i\gamma.
\]

同时：

\[
P_{\delta,\gamma}(1-s)=P_{\delta,\gamma}(s),
\]

\[
P_{\delta,\gamma}(\overline s)
=
\overline{P_{\delta,\gamma}(s)}.
\]

### 定理 2.1（对称非定位）

存在具有完整 \(G_\zeta\) 对称、但全部零点均离开临界线的整函数。

因此：

\[
\boxed{
\text{full symmetry}
\not\Rightarrow
\text{fixed-line localization}.
}
\]

这直接修正“完整对称不允许离线零点”的推理。

### 推论 2.2（RH 是稳定子增大，而不是对称恢复）

RH 型定位意味着每个非平凡零点满足：

\[
J\rho=\rho.
\]

因此 RH 的轨道语言是：

\[
\boxed{
\text{每个零点的稳定子包含 }J.
}
\]

离线四元组仍保持完整集合对称；它没有破坏函数方程，只是属于自由轨道。

所以：

- RH 成立：全部零点落入 \(J\) 的固定集；
- RH 不成立：至少出现一个 \(G_\zeta\) 自由四元轨道；
- 两种情况都可以保持完整函数方程对称。

---

## 3. Ouroboros 轨道闭合

对一个 generic 零点：

\[
\rho
\xrightarrow{J}
1-\overline\rho
\xrightarrow{C}
1-\rho
\xrightarrow{J}
\overline\rho
\xrightarrow{C}
\rho.
\]

这是 Klein 四群 Cayley 图中的四边闭环。

### 定义 3.1（Ouroboros orbit cycle）

上述四步闭合称为零点的 **Ouroboros orbit cycle**。

它表达的是：

\[
\text{作用闭合}
\quad\text{而不是}\quad
\text{拓扑曲面已经被证明为 Klein bottle}.
\]

后文将区分：

1. 群作用的四边闭环；
2. partition lattice 上 moment–cumulant 的 Möbius 反演闭环；
3. 需要额外 monodromy 前件的几何 Möbius/Klein 提升。

---

# 第二部　零点信息的 Zeckendorf 线程

## 4. 为什么不能把实零点写成一个有限 Zeckendorf 整数

Zeckendorf 定理对自然数给出有限规范表示。一般实数，尤其零点坐标，不会自动拥有有限 Fibonacci 数位表示。

因此本理论禁止直接宣称：

\[
\rho
=
\text{一个有限 Zeckendorf word}.
\]

取而代之的是一个可证明完备的**分辨率线程**。

---

## 5. 黄金量化线程

对 \(x\ge0\) 和 \(N\in\mathbb N\)，定义：

\[
q_N(x)=\left\lfloor\varphi^N x\right\rfloor.
\]

令：

\[
\mathsf Z_N(x)
=
\operatorname{wdigits}(q_N(x))
\]

为整数 \(q_N(x)\) 的规范 Zeckendorf 数位。

由 floor 定义：

\[
q_N(x)
\le
\varphi^N x
<
q_N(x)+1.
\]

所以：

\[
\boxed{
0
\le
x-\frac{q_N(x)}{\varphi^N}
<
\varphi^{-N}.
}
\]

### 定理 5.1（Zeckendorf 线程重构）

映射

\[
x
\longmapsto
\bigl(\mathsf Z_N(x)\bigr)_{N\ge0}
\]

在 \(\mathbb R_{\ge0}\) 上单射。

#### 证明

若两个实数 \(x,y\) 的全部 Zeckendorf 线程相同，则 Zeckendorf 唯一性给出：

\[
q_N(x)=q_N(y)
\quad\forall N.
\]

于是：

\[
|x-y|
<
2\varphi^{-N}
\quad\forall N,
\]

故 \(x=y\)。∎

这给出了严格意义上的：

\[
\boxed{
\text{实数}
=
\text{无限黄金分辨率下的一条 Zeckendorf completion thread}.
}
\]

---

## 6. 三值符号与零点反码

定义：

\[
\operatorname{tsign}(x)
=
\begin{cases}
-1,&x<0,\\
0,&x=0,\\
+1,&x>0.
\end{cases}
\]

对零点

\[
\rho=\frac12+\delta+i\gamma
\]

定义第 \(N\) 层轨道码：

\[
\operatorname{ZOC}_N(\rho)
=
\Bigl(
\operatorname{tsign}(\delta),
\mathsf Z_N(|\delta|),
\operatorname{tsign}(\gamma),
\mathsf Z_N(|\gamma|),
\operatorname{wdigits}(m_\rho)
\Bigr).
\]

这里 `ZOC` 表示 **Zeckendorf Orbit Code**。

### 定理 6.1（Klein 作用的两符号位实现）

在保持三个无符号 Zeckendorf 数据不变的情况下：

\[
\begin{aligned}
C&:(\varepsilon_\delta,\varepsilon_\gamma)
\mapsto
(\varepsilon_\delta,-\varepsilon_\gamma),\\
J&:(\varepsilon_\delta,\varepsilon_\gamma)
\mapsto
(-\varepsilon_\delta,\varepsilon_\gamma),\\
R&:(\varepsilon_\delta,\varepsilon_\gamma)
\mapsto
(-\varepsilon_\delta,-\varepsilon_\gamma).
\end{aligned}
\]

因此 generic 离线四元组正好对应两个符号位的全部四个状态。

### 定义 6.2（镜像反码）

\[
\overline{
(\varepsilon_\delta,d_\delta;
 \varepsilon_\gamma,d_\gamma;m)
}^{\,J}
=
(-\varepsilon_\delta,d_\delta;
 \varepsilon_\gamma,d_\gamma;m).
\]

这才是严格的“反码”：

- 不翻转 Fibonacci 数位；
- 不破坏 Zeckendorf 无相邻 \(1\) 约束；
- 只翻转 transverse sign sheet。

bitwise complement 一般不是规范 Zeckendorf word，因此不作为本理论的反码。

---

## 7. RH 的线程判据

对任一零点：

\[
\delta=0
\iff
q_N(|\delta|)=0
\quad\forall N.
\]

故：

\[
\boxed{
\mathrm{RH}
\iff
\text{每个非平凡零点的 transverse Zeckendorf thread 恒为零线程}.
}
\]

这只是等价编码，不是 RH 的证明。

### 定义 7.1（黄金检测深度）

若 \(x>0\)，定义：

\[
d_\varphi(x)
=
\min\{N:q_N(x)>0\}.
\]

若 \(x=0\)，置：

\[
d_\varphi(0)=\infty.
\]

对 \(0<x<1\)：

\[
d_\varphi(x)
=
\left\lceil
\log_\varphi\frac1x
\right\rceil.
\]

因此越靠近临界线的离线零点，有限观察者需要越深的黄金分辨率才能看到 transverse bit。

---

## 8. 内禀黄金编码与外禀序列化

本理论严格区分：

### 8.1 内禀黄金编码

当对象本身由黄金替换产生，例如仓库中的 O-5 指数：

\[
\beta(v)
=
S(v)-v\psi,
\]

利用 Zeckendorf 数位可推出：

\[
\boxed{
\beta(v)
=
\sum_{k\in\operatorname{wdigits}(v)}
\varphi^k.
}
\]

这里黄金数位是对象生成律的一部分。

### 8.2 外禀 Zeckendorf 序列化

把任意整数 fingerprint、有限 residue bitmask 或量化坐标写成 Zeckendorf word，只是规范无损编码，不自动产生数论解释。

零点实坐标采用的是外禀 completion thread；零点重数和黄金 germ 指数则具有更直接的内禀意义。

---

# 第三部　素数构型不是 Euler 独立性

## 9. 构型空间

定义一个 \(k\)-点素数构型为有限集合：

\[
H=\{h_1<\cdots<h_k\}\subset\mathbb Z.
\]

平移不改变构型形状，故规范化：

\[
h_1=0.
\]

定义反射：

\[
H^\vee
=
\{h_k-h:h\in H\}.
\]

于是：

\[
(H^\vee)^\vee=H.
\]

---

## 10. 局部剩余自动机

对素数 \(p\)，定义禁用 residue 集：

\[
R_p(H)
=
\{-h\bmod p:h\in H\},
\]

以及：

\[
\nu_p(H)=|R_p(H)|.
\]

构型称为 **admissible**，若：

\[
\nu_p(H)<p
\qquad
\forall p.
\]

### 定理 10.1（有限阻塞判定）

若 \(|H|=k\)，则对所有 \(p>k\)：

\[
\nu_p(H)\le k<p.
\]

因此 admissibility 的“是否存在完整 residue 覆盖”只需检查：

\[
p\le k.
\]

注意：奇异级数的数值仍使用所有素数；这里只说“完全阻塞”是有限判定。

### 定义 10.2（局部构型自动机）

对排好序的 offsets，逐步维护：

\[
A_{p,j}
=
\{h_1,\ldots,h_j\}\bmod p.
\]

读入下一个 gap 后更新当前 residue 并扩张集合；若：

\[
A_{p,j}=\mathbb Z/p\mathbb Z,
\]

则进入拒绝态。

所有 \(p\le k\) 的自动机直积给出构型的有限 admissibility certificate。

---

## 11. 局部联合相关的精确公式

令 \(a\) 在 \(\mathbb Z/p\mathbb Z\) 上均匀分布，并定义：

\[
X_{p,h}(a)
=
\mathbf 1_{p\nmid a+h}.
\]

则：

\[
\mathbb P\left(
X_{p,h}=1\ \forall h\in H
\right)
=
1-\frac{\nu_p(H)}p.
\]

每个单点边缘为：

\[
\mathbb P(X_{p,h}=1)=1-\frac1p.
\]

定义归一化 all-one correlation ratio：

\[
\boxed{
L_p(H)
=
\frac{1-\nu_p(H)/p}
{(1-1/p)^k}.
}
\]

### 定理 11.1（局部相关因子）

\(L_p(H)\) 正是“全部 offsets 同时避开 \(p\)”的联合概率与独立边缘乘积之比。

Hardy–Littlewood 奇异级数为：

\[
\boxed{
\mathfrak S(H)
=
\prod_pL_p(H).
}
\]

因此奇异级数不是否定 Euler 结构，而是另一种 Euler 结构：

- 不同素数模数在有限层面由 CRT 分解；
- 同一素数内部，不同 offsets 之间存在联合排斥；
- \(L_p(H)\) 依赖整个 \(H\bmod p\)，不等于单点局部因子的简单乘积。

这就是“乘法独立”和“加法相关”的精确分界。

---

## 12. 为什么最朴素的 ζ Euler 乘积不直接给出孪生素数

ζ 的 Euler 乘积对单个整数 \(n\) 的估值向量

\[
(v_p(n))_p
\]

进行对角化。

定义：

\[
(V_pf)(n)=v_p(n)f(n),
\qquad
(T_hf)(n)=f(n+h).
\]

则：

\[
\boxed{
[V_p,T_h]f(n)
=
\bigl(v_p(n)-v_p(n+h)\bigr)f(n+h).
}
\]

一般：

\[
[V_p,T_h]\neq0.
\]

所以：

- Euler 乘积属于同时对角化的乘法估值坐标；
- 孪生素数要求联合观察 \(n\) 与 \(n+2\)；
- 该观察引入与估值坐标不交换的平移算子。

### 定义 12.1（乘法—加法曲率）

\[
\mathcal K_{p,h}
=
[V_p,T_h].
\]

这是一种真正由更新次序不交换产生的离散曲率，而不是把无理数本身称为曲率。

孪生素数是 \(h=2\) 的首个重要二点 sector。

---

# 第四部　\(-1,0,+1\) 的两种严格来源

## 13. 稠密小间隔构型的 ternary gap curvature

假设一个构型的连续 gap 只取：

\[
d_j=h_{j+1}-h_j\in\{2,4\}.
\]

定义归一化 gap bit：

\[
b_j=\frac{d_j}{2}-1\in\{0,1\},
\]

以及离散曲率：

\[
\boxed{
\kappa_j=b_{j+1}-b_j\in\{-1,0,+1\}.
}
\]

### 定理 13.1（模 \(3\) 曲率判据）

在全部 gap 均为 \(2\) 或 \(4\) 的前提下：

\[
H\text{ 在模 }3\text{ admissible}
\iff
\kappa_j\neq0
\quad\forall j.
\]

#### 证明

若 \(\kappa_j=0\)，则相邻两个 gap 相等。模 \(3\) 中，\(2\) 与 \(4\) 都非零；三个连续点

\[
a,\ a+d,\ a+2d
\]

覆盖全部三个 residue，故构型被 \(3\) 阻塞。

反之，若所有 \(\kappa_j\neq0\)，则 \(2,4\) gap 严格交替。模 \(3\) 中它们分别是 \(-1,+1\)，轨迹只在两个 residue 间往返，不覆盖第三个 residue。∎

所以在该最稠密字母表中：

\[
\boxed{
0=\text{局部平直但被模 }3\text{ 阻塞},
\qquad
\pm1=\text{两种可容许转向}.
}
\]

---

## 14. 反射、反码与点数奇偶

构型反射会逆转 gap word：

\[
b(H^\vee)=\operatorname{reverse}(b(H)).
\]

曲率满足：

\[
\boxed{
\kappa(H^\vee)
=
-\operatorname{reverse}(\kappa(H)).
}
\]

若模 \(3\) admissibility 迫使 \(b\) 交替，且 gap word 长度为 \(k-1\)，则：

\[
\operatorname{reverse}(b)
=
\begin{cases}
b,&k\text{ 为偶数},\\
1-b,&k\text{ 为奇数}.
\end{cases}
\]

### 推论 14.1（构型镜像奇偶律）

- 偶数点稠密构型是 self-code 型；
- 奇数点稠密构型形成 complementary mirror codes。

具体地：

### 孪生素数

\[
H_2=\{0,2\},
\qquad
b=[0].
\]

它是 self-dual 二点读数。

### 素数三元组

\[
H_3^+=\{0,2,6\},
\qquad
b=[0,1],
\qquad
\kappa=[+1],
\]

\[
H_3^-=\{0,4,6\},
\qquad
b=[1,0],
\qquad
\kappa=[-1].
\]

二者互为镜像和 bit complement。

### 素数四元组

\[
H_4=\{0,2,6,8\},
\qquad
b=[0,1,0],
\qquad
\kappa=[+1,-1].
\]

它是一个最小的“转向后返回”Ouroboros word。

---

## 15. 黄金数域的三值特征

令：

\[
\chi_5(a)
=
\begin{cases}
0,&5\mid a,\\
+1,&a\equiv\pm1\pmod5,\\
-1,&a\equiv\pm2\pmod5.
\end{cases}
\]

它对应 \(\mathbb Q(\sqrt5)\) 中：

\[
+1=\text{split},
\qquad
0=\text{ramified},
\qquad
-1=\text{inert}.
\]

同时：

\[
\varphi' = 1-\varphi,
\qquad
\varphi\varphi'=-1.
\]

因此黄金单位本身具有 norm \(-1\)，而模 \(5\) 特征提供自然的 \(-1,0,+1\) 局部通道。

### 定义 15.1（黄金构型特征词）

\[
\chi_{5,H}(n)
=
\bigl(\chi_5(n+h)\bigr)_{h\in H}.
\]

对孪生构型 \(H=\{0,2\}\)，按 \(n\bmod5\)：

\[
\begin{array}{c|c}
n\bmod5&(\chi_5(n),\chi_5(n+2))\\
\hline
0&(0,-1)\\
1&(+1,-1)\\
2&(-1,+1)\\
3&(-1,0)\\
4&(+1,+1)
\end{array}
\]

若两个数均为大于 \(5\) 的素数，只剩：

\[
(+1,-1),\quad(-1,+1),\quad(+1,+1).
\]

### 命题 15.2（标量商遗忘方向）

前两个有序词的乘积均为 \(-1\)：

\[
(+1)(-1)=(-1)(+1).
\]

故仅看字符乘积无法区分：

\[
(+1,-1)
\quad\text{与}\quad
(-1,+1).
\]

这与仓库的 `GoldenCharacterQuotient`、有序 holonomy 与 scalar blindness 完全一致：

\[
\boxed{
\text{ordered character word}
\longrightarrow
\text{scalar product quotient}
}
\]

会丢失构型方向。

模 \(5\) 特征可作为构型的有限 refinement，但它不可能单独证明孪生素数无穷。

---

## 16. 小素数自动机级联

对只含 \(2,4\) gaps 的交替序列：

- 模 \(2\) 强制全部 offsets 同奇偶；
- 模 \(3\) 强制 \(2,4\) 交替；
- 模 \(5\) 在长度增长时选择允许相位；
- 更大素数继续排除某些有限 word。

例如两个长度为 \(5\) 的交替 gap word：

\[
[2,4,2,4,2]
\]

产生：

\[
\{0,2,6,8,12,14\},
\]

其模 \(5\) residue 覆盖全部五类，故被拒绝。

而：

\[
[4,2,4,2,4]
\]

产生：

\[
\{0,4,6,10,12,16\},
\]

模 \(5\) 只占据 \(\{0,1,2,4\}\)，故通过模 \(5\) 检验；这正是经典最稠密素数六元组形状之一。

这表明素数构型可被看成：

\[
\boxed{
\text{有限 gap word}
\quad\text{通过}\quad
\prod_{p\le k}\text{局部自动机}
}
\]

的接受语言。

---


# 第四部乙　黄金 germ：Zeckendorf 局部相关的原型

## 16A. O-5 指数不是任意无理扰动

由仓库已有的：

\[
S(v)
=
\sum_{k\in\operatorname{wdigits}(v)}
F_{k+1},
\qquad
v=
\sum_{k\in\operatorname{wdigits}(v)}
F_k,
\]

以及：

\[
\beta(v)=S(v)-v\psi,
\qquad
\psi=1-\varphi,
\]

逐项使用：

\[
F_{k+1}-\psi F_k=\varphi^k
\]

得到：

\[
\boxed{
\beta(v)
=
\sum_{k\in\operatorname{wdigits}(v)}
\varphi^k.
}
\]

所以 O-5 的 local spectrum 是所有有限、无相邻占据的黄金能量和。

它是 Zeckendorf hard-core language 的精确 partition spectrum，而不是“在有理数上随意加入一个黄金缩放”。

---

## 16B. Universal hard-core function

定义：

\[
\mathcal H_\varphi(z)
=
\sum_{v\ge0}
e^{-z\beta(v)},
\qquad
\Re z>0.
\]

对每个素数 \(p\)，黄金 local factor 为：

\[
A_p(s)
=
\sum_{v\ge0}p^{-s\beta(v)}
=
\mathcal H_\varphi(s\log p).
\]

因此所有素数地址共享同一个 universal dynamics，只是时间尺度不同：

\[
\boxed{
A_p(s)
=
A_q
\left(
\frac{\log p}{\log q}s
\right).
}
\]

局部 zero set 若存在，也按：

\[
\operatorname{Zero}(A_p)
=
\frac1{\log p}
\operatorname{Zero}(\mathcal H_\varphi)
\]

形成 prime-address fan。

---

## 16C. Zeckendorf 最低数位分解与 Mahler 方程

按最低允许 Fibonacci index 是否占据，把所有合法 word 分为两类：

1. 最低位置空；
2. 最低位置占据，故下一位置必须空。

由整体 index shift 得到：

\[
\boxed{
\mathcal H_\varphi(z)
=
\mathcal H_\varphi(\varphi z)
+
e^{-\varphi^2z}
\mathcal H_\varphi(\varphi^2z).
}
\]

等价地：

\[
\boxed{
A_p(s)
=
A_p(\varphi s)
+
p^{-\varphi^2s}
A_p(\varphi^2s).
}
\]

定义：

\[
V(z)
=
\begin{pmatrix}
\mathcal H_\varphi(z)\\
\mathcal H_\varphi(\varphi z)
\end{pmatrix},
\qquad
M(z)
=
\begin{pmatrix}
1&e^{-\varphi^2z}\\
1&0
\end{pmatrix},
\]

则：

\[
V(z)=M(z)V(\varphi z).
\]

不同尺度矩阵通常不交换。若：

\[
x=e^{-\varphi^2z},
\qquad
y=e^{-\varphi^3z},
\]

则：

\[
M(z)M(\varphi z)-M(\varphi z)M(z)
=
(x-y)
\begin{pmatrix}
1&-1\\
0&-1
\end{pmatrix}.
\]

这给出一个具体的黄金尺度 swap curvature。

---

## 16D. ζ 因子是 local cluster modes 的全球装配

令：

\[
X=p^{-\varphi^2s},
\qquad
Y=p^{-\varphi^3s}.
\]

黄金 local generating function 的低阶项具有：

\[
1+X+Y+XY+\cdots.
\]

仓库已经证明第二阶分解：

\[
\boxed{
Z_{\mathrm{germ}}^{(2)}(s)
=
\zeta(\varphi^2s)
\zeta(\varphi^3s)
\zeta(2\varphi^2s)^{-1}
G_3(s).
}
\]

这里：

- \(\zeta(\varphi^2s)\) 是第一 primitive mode；
- \(\zeta(\varphi^3s)\) 是第二 primitive mode；
- \(\zeta(2\varphi^2s)^{-1}\) 是第一重复占据排斥项；
- \(G_3\) 保留 connected local interaction。

仓库还在 local deviation 中显式出现：

\[
-Y^2
=
-p^{-2\varphi^3s}
\]

作为第二阶归一化后的首个 connected exclusion mode。

这表明 ζ 因子级联可以理解为 Zeckendorf hard-core partition function 的 Euler/Witt cluster expansion。

---

## 16E. Local divisor 与 coherent divisor

不能预设 \(G_3\) 零自由。局部 hard-core partition functions 一般可以拥有复零点。

定义：

\[
g_p(s)
=
(1-p^{-\varphi^3s})
(1+p^{-\varphi^2s})^{-1}
A_p(s).
\]

固定 \(s\) 时定义 local address set：

\[
\operatorname{Addr}(s)
=
\{p:g_p(s)=0\}.
\]

若：

\[
\sum_p|g_p(s)-1|<\infty,
\]

则 \(\operatorname{Addr}(s)\) 必为有限集；否则每个零因子都贡献大小 \(1\) 的 deviation。

### 定义 16E.1（finite-addressed zero）

若删除有限集合 \(S\supseteq\operatorname{Addr}(s_0)\) 后零点消失，则称 \(s_0\) 为 finite-addressed local zero。

### 定义 16E.2（coherent zero）

若对任意有限 local-factor deletion，零点仍保留，则称其为 coherent zero。

经典 ζ 的非平凡零点在仓库中已经被证明对有限 Euler 素数修改稳定；这正是 coherent divisor 的原型。

因此，黄金 germ 若用于 RH detector，应考察：

\[
\boxed{
\frac{\text{full golden divisor}}
{\text{finite local prime-address divisor}}
}
\]

而不是要求黄金 germ 的全部零点都在一条线。

这与本卷的 prime-constellation 理论共享同一原则：

\[
\boxed{
\text{scalar local product不是完整相关本体；}
\quad
\text{必须区分 local memory 与 global coherence}.
}
\]

---

## 16F. 与构型累积量理论的接口

黄金 germ 是本理论的 \(1\)-dimensional hard-core prototype：

- Zeckendorf word 给出允许 occupation configurations；
- local factor 是 partition function；
- 对数给出 connected cluster modes；
- ζ 因子是把同一 mode 对所有素数地址进行 Euler 装配；
- residual factor 保存局部非独立记忆；
- finite-address quotient 提取 global coherent divisor。

prime constellation completion 则把“occupation position”从 Fibonacci index 推广为加法 shifts \(h\in H\)，并把 local cluster log 推广为 partition-lattice cumulants。

所以两条线并非同一对象，但拥有同一个范畴骨架：

\[
\boxed{
\text{configuration language}
\to
\text{partition function}
\to
\log
\to
\text{connected modes}
\to
\text{global spectral assembly}.
}
\]

---

# 第五部　相关完备化 ζ

## 17. ζ Gibbs 基测度

对实数 \(\sigma>1\)，定义：

\[
\mathbb P_\sigma(N=n)
=
\frac{n^{-\sigma}}{\zeta(\sigma)}.
\]

这给出一个真实概率分布。

ζ Euler 乘积说明，在该基测度下，素数指数

\[
v_p(N)
\]

形成独立几何坐标。

但平移变量：

\[
\Lambda(N+h)
\]

并不是这些坐标的单点函数；不同 \(h\) 通过同一个 \(N\) 耦合。

---

## 18. 平方零源变量代数

对有限构型 \(H\)，定义交换代数：

\[
\mathcal N_H
=
\mathbb R[\varepsilon_h:h\in H]
/
(\varepsilon_h^2:h\in H).
\]

任意单项式都对应一个子集：

\[
\varepsilon_A=\prod_{h\in A}\varepsilon_h.
\]

正次数理想是 nilpotent，因此对常数项为 \(1\) 的元素，有限对数严格定义：

\[
\log(1+x)
=
\sum_{r=1}^{|H|}
\frac{(-1)^{r+1}}r x^r.
\]

---

## 19. 构型矩生成元与 connected 生成元

定义：

\[
\boxed{
\mathcal M_H(\sigma)
=
\mathbb E_\sigma
\prod_{h\in H}
\left(
1+\varepsilon_h\Lambda(N+h)
\right).
}
\]

展开：

\[
\mathcal M_H(\sigma)
=
\sum_{A\subseteq H}
M_A(\sigma)\varepsilon_A,
\]

其中：

\[
M_A(\sigma)
=
\frac1{\zeta(\sigma)}
\sum_{n\ge1}
\frac{\prod_{h\in A}\Lambda(n+h)}
{n^\sigma}.
\]

定义 connected 生成元：

\[
\boxed{
\mathcal K_H(\sigma)
=
\log\mathcal M_H(\sigma)
=
\sum_{\varnothing\neq A\subseteq H}
\kappa_A(\sigma)\varepsilon_A.
}
\]

### 定理 19.1（构型大小等于源混合 jet 阶数）

若：

\[
A=\{h_1,\ldots,h_k\},
\]

则：

\[
\boxed{
\kappa_A(\sigma)
=
\left.
\frac{\partial^k}
{\partial\varepsilon_{h_1}\cdots\partial\varepsilon_{h_k}}
\log\mathcal M_H(\sigma)
\right|_{\varepsilon=0}.
}
\]

这严格实现：

- 二点构型是二阶源 jet；
- 三点构型是三阶源 jet；
- 四点构型是四阶源 jet。

---

## 20. Partition lattice 的 Möbius 反演

connected coefficient 满足：

\[
\boxed{
\kappa_A
=
\sum_{\pi\in\Pi(A)}
(-1)^{|\pi|-1}
(|\pi|-1)!
\prod_{B\in\pi}M_B.
}
\]

反向：

\[
\boxed{
M_A
=
\sum_{\pi\in\Pi(A)}
\prod_{B\in\pi}\kappa_B.
}
\]

这里 \(\Pi(A)\) 是集合分拆格。

这给出了一个真正严格的 Möbius 结构：

\[
\boxed{
\text{full moments}
\overset{\log}{\longrightarrow}
\text{connected cumulants}
\overset{\exp}{\longrightarrow}
\text{full moments}.
}
\]

### 定义 20.1（Combinatorial Ouroboros closure）

上述

\[
\mathcal M=\exp\mathcal K,
\qquad
\mathcal K=\log\mathcal M
\]

的闭合回路称为 **cumulant Ouroboros**。

本卷认为，这比未经证明的几何 Möbius strip 更接近素数构型中的真实“莫比乌斯”来源：它是 partition lattice 的 Möbius inversion。

---

## 21. 前四阶 connected 读数

### 一点

\[
\kappa_1=M_1.
\]

### 二点

\[
\boxed{
\kappa_{12}
=
M_{12}-M_1M_2.
}
\]

孪生素数的 connected 读数不是仅仅 \(M_{02}\)，而是减去单点基线后的 covariance sector。

### 三点

\[
\boxed{
\begin{aligned}
\kappa_{123}
={}&M_{123}
-M_{12}M_3-M_{13}M_2-M_{23}M_1\\
&+2M_1M_2M_3.
\end{aligned}
}
\]

它排除了三个两点边缘对三点矩的全部可分解解释。

### 四点

\[
\boxed{
\begin{aligned}
\kappa_{1234}
={}&M_{1234}
-\sum_{\text{4 triples}}M_{ijk}M_l
-\sum_{\text{3 pairings}}M_{ij}M_{kl}\\
&+2\sum_{\text{6 pairs}}M_{ij}M_kM_l
-6M_1M_2M_3M_4.
\end{aligned}
}
\]

所以“素数四元组是四点读数”的严格版本是：

\[
\boxed{
\text{四阶 mixed derivative after all lower partitions are subtracted}.
}
\]

---

## 22. Hardy–Littlewood 极限的 connected 版本

假设对 \(H\) 的每个非空子构型 \(A\subseteq H\) 都成立：

\[
\sum_{n\le X}
\prod_{h\in A}\Lambda(n+h)
=
\mathfrak S(A)X+o(X).
\]

则标准 Abelian 运输给出：

\[
\lim_{\sigma\downarrow1}
M_A(\sigma)
=
\mathfrak S(A).
\]

因此：

\[
\boxed{
\lim_{\sigma\downarrow1}
\kappa_A(\sigma)
=
\mathfrak S_{\mathrm{conn}}(A),
}
\]

其中：

\[
\boxed{
\mathfrak S_{\mathrm{conn}}(A)
=
\sum_{\pi\in\Pi(A)}
(-1)^{|\pi|-1}
(|\pi|-1)!
\prod_{B\in\pi}\mathfrak S(B).
}
\]

这是一个条件定理，而不是 prime \(k\)-tuple conjecture 的证明。

它把奇异级数从“原始矩常数”提升成一整套 connected singular-series hierarchy。

---

# 第六部　构型多谱与零点频谱

## 23. 有限循环模型中的精确多谱恒等式

在有限循环群 \(\mathbb Z/M\mathbb Z\) 上，令：

\[
a(n)=\Lambda(n)-\text{baseline}.
\]

定义 \(k\)-点平移相关：

\[
C_k(h_1,\ldots,h_{k-1})
=
\frac1M
\sum_n
a(n)
a(n+h_1)\cdots
a(n+h_{k-1}).
\]

令：

\[
A(\theta)
=
\sum_n a(n)e^{-in\theta}.
\]

则：

- \(k=2\) 的 Fourier 变换是 power spectrum：
  \[
  |A(\theta)|^2;
  \]
- \(k=3\) 的 Fourier 变换是 bispectrum：
  \[
  A(\theta_1)A(\theta_2)
  A(-\theta_1-\theta_2);
  \]
- \(k=4\) 给出 trispectrum；
- 一般 \(k\) 给出满足总频率守恒的 polyspectrum。

因此：

\[
\boxed{
\text{prime constellation}
=
\text{additive shift domain 中的系数},
}
\]

\[
\boxed{
\text{correlation spectrum}
=
\text{其多维 Fourier 编码}.
}
\]

具体地：

\[
\begin{aligned}
\text{twin } \{0,2\}&\leftrightarrow C_2(2),\\
\text{triplet } \{0,2,6\}&\leftrightarrow C_3(2,6),\\
\text{quadruplet } \{0,2,6,8\}&\leftrightarrow C_4(2,6,8).
\end{aligned}
\]

---

## 24. 零点 pair correlation 读到的是聚合二点谱

Montgomery 型 pair correlation 与 Goldston–Montgomery 型结果表明，在明确假设与归一化下，零点二点统计和短区间素数二阶方差之间存在严格联系。

但短区间方差展开为：

\[
\sum_{|h|<H}
(H-|h|)
\sum_{n\le X}
(\Lambda(n)-1)(\Lambda(n+h)-1)
\]

这一类三角加权和。

所以零点 pair correlation 首先读取的是：

\[
\boxed{
\text{所有二点 shifts 的加权聚合频谱},
}
\]

而不是只把 \(h=2\) 单独贴在某一对零点上。

要从聚合频谱恢复孪生素数，需要足够丰富的测试核和 shift-Fourier 反演。

这解释了：

\[
\boxed{
\zeta\text{ 包含全部素数}
\quad\text{但}\quad
\text{单个 Euler product 不直接隔离 }h=2.
}
\]

---

## 25. 高阶零点相关的正确预期

Rudnick–Sarnak 型 \(n\)-level correlation 说明，高阶零点统计本身是自然对象。

本理论提出但不预设：

\[
\boxed{
k\text{-point additive prime cumulant}
\quad\longleftrightarrow\quad
k\text{-level connected zero statistic}.
}
\]

这是一条 transform-level bridge，不是一一配对：

- 一个素数三元组不对应某三个固定零点；
- 它对应零点三阶 connected 频谱中的一个 shift-Fourier coefficient；
- 全体零点状态可能是全部构型相关性的统一多谱编码。

---

# 第七部　零点轨道的 transverse cumulants

## 26. 有限镜像闭合零点窗

取上半平面中每个 \(J\)-orbit 的右代表：

\[
\rho_a=\frac12+\delta_a+i\gamma_a,
\qquad
\delta_a\ge0,
\]

并保留重数 \(m_a\) 与正权 \(w_a\)。

定义横向 moment generating function：

\[
\mathcal Z_T(u)
=
\sum_a
m_aw_a
\left(
e^{u\delta_a}
+
e^{-u\delta_a}
\right).
\]

显然：

\[
\mathcal Z_T(-u)=\mathcal Z_T(u).
\]

### 定理 26.1（奇阶不可见律）

\[
\mathcal Z_T^{(2r+1)}(0)=0
\qquad
\forall r\ge0.
\]

完整镜像对称会消去：

\[
\delta,\delta^3,\delta^5,\ldots
\]

但不会消去偶阶幅值。

### 定理 26.2（二阶可见律）

\[
\mathcal Z_T''(0)
=
2\sum_a m_aw_a\delta_a^2
\ge0.
\]

并且：

\[
\mathcal Z_T''(0)=0
\iff
\delta_a=0
\quad\forall a.
\]

所以：

\[
\boxed{
\text{RH 对称缺陷不是一阶可见量，而是二阶正可见量}.
}
\]

“完整对称使 RH 完全不可观察”只有在观察者被限制为奇阶或一阶读数时才成立。

---

## 27. 双曲缺陷生成全部偶矩

定义：

\[
\mathfrak D_T(\tau)
=
\sum_a
m_aw_a
\bigl(\cosh(2\tau\delta_a)-1\bigr).
\]

展开：

\[
\boxed{
\mathfrak D_T(\tau)
=
\sum_{r\ge1}
\frac{(2\tau)^{2r}}{(2r)!}
\sum_a m_aw_a\delta_a^{2r}.
}
\]

仓库现有 `CriticalDampingFlatness` 已证明有限版本的零缺陷判据。

### 定义 27.1（transverse defect order）

\[
r_T
=
\min
\left\{
r\ge1:
\sum_a m_aw_a\delta_a^{2r}\neq0
\right\}.
\]

对正权有限窗，只要存在离线零点：

\[
r_T=1,
\]

即实际导数阶为 \(2\)。

---

## 28. Riesz 曲率和 transverse moment 不应混同

Riesz 曲率原子来自：

\[
\Delta\log|\xi(s)|
=
2\pi
\sum_\rho m_\rho\delta_\rho.
\]

其单原子电荷是：

\[
2\pi m_\rho.
\]

而横向 deficit 是：

\[
\delta_\rho^{2r}.
\]

仓库已经反证了“一次全局标量归一化即可把 deficit measure 变成 curvature measure”的朴素桥。

因此本理论坚持：

\[
\boxed{
\begin{aligned}
2\pi m_\rho&=\text{divisor/Riesz charge},\\
\delta_\rho^{2r}&=\text{transverse displacement moment}.
\end{aligned}
}
\]

二者可以共同进入一个带权测度，但不是同一个量。

---

# 第八部　jet 的三重分级

## 29. 三条独立 jet 轴

### 29.1 构型轴 \(k\)

\[
k=|H|
\]

由源变量 mixed derivative 的数量给出：

\[
\partial_{\varepsilon_{h_1}}\cdots
\partial_{\varepsilon_{h_k}}
\log\mathcal M.
\]

### 29.2 重数轴 \(m\)

若：

\[
\xi^{(j)}(\rho)=0
\quad(j<m),
\qquad
\xi^{(m)}(\rho)\neq0,
\]

则零点重数为 \(m\)。

仓库进一步证明临界线强度横向首项为：

\[
|\xi(\tfrac12+\delta+it_0)|^2
=
C_m\delta^{2m}
+
O(\delta^{2m+2}),
\qquad
C_m>0.
\]

### 29.3 对称可见轴 \(2r\)

镜像对称消去奇阶 transverse jet，因此可见阶数为：

\[
2,4,6,\ldots.
\]

---

## 30. Jet 三元组

定义一个理论状态的 jet grade：

\[
\boxed{
\operatorname{grade}
=
(k,m,2r).
}
\]

其含义分别是：

\[
\boxed{
\begin{aligned}
k&=\text{多少个不同加法 shift 参与 connected 读数},\\
m&=\text{解析零点的局部 ramification/multiplicity},\\
2r&=\text{镜像商观察者首次看见 transverse defect 的阶}.
\end{aligned}
}
\]

这三者不能直接相等。

“孪生素数是二点读数”和“二重零点的二阶导数”都出现数字 \(2\)，但它们作用在不同变量上。

---

## 31. 三轴示例

\[
\begin{array}{c|c|c|c}
\text{对象}&k&m&2r\\
\hline
\text{twin connected sector}&2&\text{未指定}&\text{未指定}\\
\text{prime triplet sector}&3&\text{未指定}&\text{未指定}\\
\text{simple critical zero}&\text{未指定}&1&2\\
\text{double critical zero}&\text{未指定}&2&4\\
\text{generic simple off-line orbit}&\text{由源决定}&1&2
\end{array}
\]

本理论的长期对象不是把三轴压成一维，而是构造：

\[
\mathfrak J^{(k,m,2r)}
\]

三重分级谱。

---

# 第九部　“纠缠”的三级定义

## 32. 一级：镜像结构相关

对 transverse mirror pair 选取均匀 side 变量：

\[
S\in\{-1,+1\},
\qquad
X=S\delta,
\qquad
X^\vee=-S\delta.
\]

则：

\[
\mathbb E[X]=0,
\qquad
XX^\vee=-\delta^2.
\]

两个 sign readout 互相完全决定，其 mutual information 为一 bit。

这是一种**经典 perfect anti-correlation**。

### 纪律

仅凭这一点，不得宣称量子 Bell entanglement。

---

## 33. 二级：跨轨道 connected entanglement

设零点镜像轨道集合为 \(\mathscr O_T\)。

定义一个 joint generating functional：

\[
\mathcal Z_T(\mathbf u)
=
\mathbb E
\exp
\left(
\sum_{a\in\mathscr O_T}u_aX_a
\right).
\]

定义 connected orbit cumulants：

\[
K_T(a_1,\ldots,a_r)
=
\left.
\partial_{u_{a_1}}\cdots\partial_{u_{a_r}}
\log\mathcal Z_T(\mathbf u)
\right|_{\mathbf u=0}.
\]

### 定义 33.1（结构纠缠）

若存在跨越两个非空轨道分区的 connected cumulant 非零，则称状态在该分区上结构纠缠。

若所有跨分区 connected cumulants 均为零，则 joint state 因子化，不存在全局结构纠缠。

因此：

\[
\boxed{
\text{函数方程配对}
\not\Rightarrow
\text{所有零点对彼此全局纠缠}.
}
\]

“所有离线零点共同纠缠”必须提升为可检验猜想：

\[
\boxed{
\forall T,\ 
\text{off-line orbit cumulant hypergraph 在其非空时连通}.
}
\]

---

## 34. Poisson holonomy 耦合图

对右侧离线代表：

\[
\rho_a=\frac12+\delta_a+i\gamma_a,
\qquad \delta_a>0,
\]

仓库已有的二点 Poisson energy 给出候选边权：

\[
\boxed{
E_{ab}
=
\frac{(\gamma_b-\gamma_a)^2}
{\pi(\delta_a+\delta_b)
\left(
(\delta_a+\delta_b)^2+
(\gamma_b-\gamma_a)^2
\right)}.
}
\]

其性质：

\[
E_{ab}\ge0,
\]

\[
E_{ab}=0
\iff
\gamma_a=\gamma_b,
\]

并在共同高度平移下不变。

### 定义 34.1（Poisson orbit graph）

以离线 mirror orbits 为顶点，以 \(E_{ab}\) 为边权，形成有限窗口图。

这给出一个自然的二点 coupling candidate，但仓库现有定理明确没有证明它就是经典 ζ 零点之间的物理量。

---

## 35. 三级：真正的量子提升

若要按量子意义使用“纠缠”，必须给出：

1. Hilbert 空间分解
   \[
   \mathcal H=\mathcal H_L\otimes\mathcal H_R;
   \]
2. 密度算子 \(\rho_{\mathrm{state}}\)；
3. 镜像作用的线性或反线性实现；
4. 非可分离性判据。

一个可选模型是：

\[
|\Omega_\rho\rangle
=
\frac1{\sqrt2}
\left(
|+\rangle_L|-\rangle_R
+
e^{i\theta_\rho}
|-\rangle_L|+\rangle_R
\right).
\]

它的 Schmidt rank 为 \(2\)，故是 entangled state。

但：

- 对称轨道本身没有自动指定 \(\theta_\rho\)；
- 没有自动指定左右 tensor factors；
- 没有自动给出物理测量代数。

### 定义 35.1（MirrorHilbertLift）

把上述额外数据封装为一个结构。只有在存在自然 `MirrorHilbertLift` 并证明 reduced state 非纯时，才把离线对称对称为量子纠缠对。

---

# 第十部　相关完备化 determinant 与 Trace–Jet Bridge

## 36. 右半平面无条件对象

对每个有限 \(H\)，\(\sigma>1\) 时：

\[
M_A(\sigma)
=
\frac1{\zeta(\sigma)}
\sum_{n\ge1}
\frac{\prod_{h\in A}\Lambda(n+h)}
{n^\sigma}
\]

绝对收敛，因为：

\[
\prod_{h\in A}\Lambda(n+h)
=
O((\log n)^{|A|}).
\]

因此 \(\mathcal M_H\) 与 \(\mathcal K_H\) 是无条件定义的相关完备化 germ。

---

## 37. Trace–Jet Bridge 猜想

### 猜想 37.1（Correlation-completed xi）

存在一个取值于有限源代数的亚纯/整函数族：

\[
\Xi_H(s;\boldsymbol\varepsilon)
\]

满足：

### C1 基点

\[
\Xi_H(s;0)=\xi(s).
\]

### C2 反射协变

\[
\Xi_H(1-\overline s;\overline{\boldsymbol\varepsilon})
=
\overline{\Xi_H(s;\boldsymbol\varepsilon)}.
\]

### C3 右半平面 prime-side jet

对每个 \(A\subseteq H\)：

\[
[\varepsilon_A]\,
\partial_s\log\Xi_H
\]

等于 \(\kappa_A\) 的某个明确 completed Mellin transform，加上显式 archimedean 项。

### C4 divisor-side expansion

在不穿过极点的局部区域：

\[
\partial_s\log\Xi_H
=
E_H(s;\varepsilon)
+
\sum_{\rho(\varepsilon)}
\frac{m_\rho(\varepsilon)}
{s-\rho(\varepsilon)}.
\]

### C5 source–spectral charge

定义：

\[
q_A(\rho)
=
\operatorname{Res}_{s=\rho}
[\varepsilon_A]\,
\partial_s\log\Xi_H(s;\varepsilon).
\]

它是零点轨道对构型 \(A\) 的 spectral response charge。

### C6 connectedness 保持

\[
[\varepsilon_A]\log\Xi_H
\]

只能由 connected \(A\)-sector 贡献，不能由彼此独立的低阶 sectors 伪造。

---

## 38. 该桥成立后的解释

若 C1–C6 成立，则：

\[
\boxed{
\text{整个零点状态}
=
\text{全部有限加法构型 connected cumulants 的统一频谱响应}.
}
\]

但这不意味着：

\[
\text{一个零点}
\leftrightarrow
\text{一个固定 prime tuple}.
\]

更准确的是：

\[
\boxed{
\text{一个构型}
\leftrightarrow
\text{全体零点轨道上的一个响应 charge field}.
}
\]

孪生素数是 \(k=2\) charge channel；三元组是 \(k=3\) channel；四元组是 \(k=4\) channel。

---

## 39. 已知结果只支持桥的一部分

已知 pair-correlation 工作表明：

- 零点二点统计与短区间素数方差存在深刻、在若干假设下可证明的等价或近等价；
- \(n\)-level zero correlations 是成熟的谱统计对象；
- 这些结果支持“二阶及高阶谱相关塔”的方向。

它们尚未给出：

- 对每个具体 \(H\) 的 completed determinant；
- 一个把 \(h=2\) 单独隔离出来的无条件反演；
- 离线零点存在；
- 所有离线轨道的全局量子纠缠。

所以 Trace–Jet Bridge 是研究计划，不是已有文献换名。

---

# 第十一部　投影理论与 RH 的逻辑位置

## 40. ζ 可以是投影，但投影非单射不推出 RH 为假

仓库已证明若干模型中：

\[
\text{hidden ordered prime memory}
\longrightarrow
\text{scalar completed readout}
\]

不是单射。

这支持下述正式判断：

\[
\boxed{
\text{标量 ζ 类读数可能遗忘构造历史}.
}
\]

但 RH 是关于经典 \(\xi\) 自身 zero divisor 的命题。

因此：

\[
\boxed{
\text{存在隐藏 memory}
\not\Rightarrow
\text{经典 }\xi\text{ 有离线零点}.
}
\]

要从“ζ 是投影”推出 RH 为假，至少还需要：

1. 一个自然 lift \(\widetilde\Xi\)；
2. 精确投影/行列式恒等式；
3. lift 谱中离线分支不能在投影中消失的定理；
4. 一个经证明或认证的离线零点。

目前这些前件没有闭合。

---

## 41. 四种相区必须分开

### Phase A：critical fixed-locus phase

\[
\delta_\rho=0
\quad\forall\rho.
\]

即 RH。

### Phase B：symmetric off-line phase

存在：

\[
\delta_\rho\neq0,
\]

但全部零点仍按 Klein 四群闭合。

这是 RH 为假但函数方程不破缺的情形。

### Phase C：projection-blind phase

hidden holonomy 不同，但 scalar divisor 相同。

它既不推出 RH，也不推出 \(\neg\)RH。

### Phase D：globally connected phase

不同零点轨道之间存在任意高阶 connected cumulants。

它是“所有零点共同纠缠”的正式候选。

四个相区逻辑独立，不能互相偷换。

---

## 42. RH 的可观察性

镜像商丢失的是：

\[
\operatorname{sign}(\delta),
\]

不是：

\[
|\delta|.
\]

二阶量：

\[
\sum m_\rho\delta_\rho^2
\]

仍然严格可见。

因此：

\[
\boxed{
\text{完整对称}
\Rightarrow
\text{横向一阶盲},
}
\]

但：

\[
\boxed{
\text{完整对称}
\not\Rightarrow
\text{横向二阶盲}.
}
\]

RH 恰可被写成全部横向二阶正缺陷为零。

截至本卷日期，RH 的公共数学状态仍是未解决；本理论不预设其真值。

---

# 第十二部　莫比乌斯与 Klein bottle：严格版与模型版

## 43. 严格成立的两个闭合结构

### 43.1 Klein 四群轨道方形

\[
\rho\to J\rho\to C J\rho\to J C J\rho\to\rho.
\]

这是有限群作用图。

### 43.2 Partition Möbius inversion

\[
\mathcal M
\overset{\log}{\leftrightarrows}
\mathcal K.
\]

这是 incidence algebra 中的 Möbius 反演。

两者都严格存在。

---

## 44. 不自动成立的几何 Möbius strip

把临界线两侧视为两张 sign sheets，并不能自动得到 Möbius strip。

临界条带按：

\[
(\gamma,\varepsilon)
\sim
(\gamma+L,-\varepsilon)
\]

粘合，才会产生 Möbius monodromy。

经典 ζ 没有给出一个已证明的自然高度周期 \(L\)，因此该粘合是额外假设。

### 定义 44.1（Möbius zero-bundle model）

若一个参数回路上的平行移动把：

\[
\delta\mapsto-\delta,
\]

则 transverse sign line bundle 的第一 Stiefel–Whitney 类非零，称为 Möbius zero bundle。

### Klein bottle 提升

若再引入第二个周期方向和反向粘合，可构造 Klein bottle 型商。

该拓扑模型可以研究，但不得从函数方程本身直接宣布已经存在。

---

# 第十三部　新理论的可立即形式化层

## 45. 建议目录

```text
D5/S1/Depth/ZeckendorfRealThread.lean
D5/S1/PrimeConstellation/Core.lean
D5/S1/PrimeConstellation/GoldenGapCurvature.lean
D5/S1/PrimeConstellation/ModFiveCharacterWord.lean

D5/S3/PrimeConstellation/LocalCorrelationFactor.lean
D5/S3/PrimeConstellation/AdmissibilityAutomaton.lean
D5/S3/PrimeConstellation/SubsetCumulant.lean
D5/S3/PrimeConstellation/ZetaGibbsCorrelationCompletion.lean
D5/S3/PrimeConstellation/FinitePolyspectrum.lean

D5/S3/Zeros/OrbitJet/KleinOrbitType.lean
D5/S3/Zeros/OrbitJet/SignedZeckendorfZeroCode.lean
D5/S3/Zeros/OrbitJet/TransverseCumulants.lean
D5/S3/Zeros/OrbitJet/PoissonOrbitGraph.lean

D5/X_Frontier/ConstellationZero/CorrelationCompletedXi.lean
D5/X_Frontier/ConstellationZero/TraceJetBridge.lean
D5/X_Frontier/ConstellationZero/QuantumOrbitLift.lean
```

---

## 46. 第一义务波：纯有限/初等闭合

### ZC-A　对称不定位反例

```lean
theorem quartetPolynomial_full_symmetry_and_offline
    (delta gamma : ℝ) (hdelta : delta ≠ 0) (hgamma : gamma ≠ 0) :
    reflectionInvariant (quartetPolynomial delta gamma) ∧
    conjugationCovariant (quartetPolynomial delta gamma) ∧
    allFourRootsOffCritical delta gamma
```

**目的：** 永久排除“完整对称自动推出 RH”。

---

### ZC-B　黄金实数线程误差

```lean
theorem goldenQuantization_error (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    0 ≤ x - goldenQuantization N x / Real.goldenRatio ^ N ∧
    x - goldenQuantization N x / Real.goldenRatio ^ N <
      Real.goldenRatio ^ (-(N : ℤ))
```

---

### ZC-C　Zeckendorf 线程单射

```lean
theorem zeckendorfRealThread_injective :
    Function.Injective zeckendorfRealThread
```

---

### ZC-D　Klein 符号作用

```lean
theorem zeroOrbitCode_symmetry_actions :
    code (conj rho) = flipHeight (code rho) ∧
    code (1 - conj rho) = flipTransverse (code rho) ∧
    code (1 - rho) = flipBoth (code rho)
```

---

### ZC-E　有限 admissibility 检验

```lean
theorem admissible_iff_small_primes
    (H : PrimeConstellation) :
    Admissible H ↔
      ∀ p : Nat.Primes, p.1 ≤ H.card →
        residueSupportCard p H < p
```

---

### ZC-F　局部 all-one correlation

```lean
theorem local_all_one_probability
    (p : Nat.Primes) (H : PrimeConstellation) :
    localJointProbability p H =
      1 - residueSupportCard p H / p
```

---

### ZC-G　模三 ternary curvature

```lean
theorem two_four_gap_mod_three_admissible_iff
    (H : TwoFourGapConstellation) :
    ModThreeAdmissible H ↔
      ∀ i, gapCurvature H i ≠ 0
```

---

### ZC-H　镜像奇偶律

```lean
theorem alternating_gap_mirror_code
    (H : TwoFourGapConstellation)
    (h3 : ModThreeAdmissible H) :
    gapBits H.mirror =
      if Even H.card then gapBits H
      else complementBits (gapBits H)
```

---

### ZC-I　孪生模五特征表

```lean
theorem twin_mod_five_character_table :
    ∀ a : ZMod 5,
      twinCharacterWord a =
        match a with
        | 0 => (0, -1)
        | 1 => (1, -1)
        | 2 => (-1, 1)
        | 3 => (-1, 0)
        | 4 => (1, 1)
```

---

### ZC-J　moment–cumulant 分拆公式

```lean
theorem jointCumulant_eq_partitionMobius
    (moment : Finset ι → R) (S : Finset ι) :
    jointCumulant moment S =
      ∑ partition : SetPartition S,
        mobiusCoefficient partition *
          ∏ block in partition.blocks, moment block
```

---

### ZC-K　镜像奇 jet 消去

```lean
theorem mirrorClosed_odd_transverse_moment_zero
    (window : Finset ZeroOrbit) :
    ∀ r, oddTransverseMoment window (2 * r + 1) = 0
```

---

### ZC-L　二阶缺陷判据

```lean
theorem transverseSecondMoment_eq_zero_iff
    (window : Finset ZeroOrbit)
    (hweight : ∀ z ∈ window, 0 < weight z) :
    transverseSecondMoment window = 0 ↔
      ∀ z ∈ window, transverseDepth z = 0
```

---

# 第十四部　中期义务波

## 47. 相关完备化 germ

证明对 \(\sigma>1\)：

```lean
def correlationMoment
    (sigma : Set.Ioi (1 : ℝ))
    (H : PrimeConstellation)
    (A : Finset H) : ℝ
```

以及所有有限 mixed coefficients 的绝对收敛。

---

## 48. Abel 极限运输

```lean
theorem hardyLittlewood_implies_zetaGibbs_limit
    (hHL : HardyLittlewoodAsymptotic H) :
    Tendsto (correlationMoment · H H.univ)
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (singularSeries H))
```

该声明必须保留 `hHL`，不得把 conjecture 偷入基础。

---

## 49. 多谱有限反演

在 `ZMod M` 上首先闭合 exact Fourier identity，再讨论整数窗误差。

---

## 50. Poisson orbit graph

只消费仓库已有 pairwise energy：

```lean
def poissonOrbitWeight (a b : RightOffLineOrbit) : ℝ := ...

theorem poissonOrbitWeight_nonnegative ...
theorem poissonOrbitWeight_eq_zero_iff_equalHeight ...
theorem poissonOrbitWeight_commonShift_invariant ...
```

不把该边权冒充经典 ζ 必然耦合。

---

# 第十五部　Frontier 义务

## 51. Correlation-completed xi

先冻结接口，不给 `sorry` 伪装成结论：

```lean
structure CorrelationCompletedXi
    (H : PrimeConstellation) where
  value : ℂ → SourceAlgebra H → ℂ
  base_eq_xi : ...
  reflection_covariant : ...
  primeJet : ...
  meromorphic : ...
```

只有构造出 inhabitant 后才能消费。

---

## 52. Trace–Jet Bridge

```lean
def TraceJetBridge (H : PrimeConstellation) : Prop := ...
```

目标分三层：

1. \(k=1\)：回收 classical explicit formula；
2. \(k=2\)：回收短区间方差／pair-correlation 的有限核版本；
3. 一般 \(k\)：建立 connected polyspectrum 与 zero \(k\)-level measure 的桥。

---

## 53. QuantumOrbitLift

保持完全可选：

```lean
structure QuantumOrbitLift where
  left right : Type
  hLeft hRight : InnerProductSpace ℂ ...
  state : ...
  mirror : ...
  density : ...
  entangled : ¬ Separable density
```

若无法给出自然 inhabitant，则“量子纠缠”停留在 model 标签。

---

# 第十六部　可证伪预测

## P1　对称不定位

若某理论仅使用 \(C,R,J\) 对称而没有正性、谱自伴性或固定点机制，则它不能排除 generic 四元离线轨道。

## P2　奇阶盲性

任何只读取 transverse 奇矩或一阶 response 的镜像闭合观察者，都无法区分：

\[
\delta=0
\quad\text{与}\quad
\{\pm\delta\}\text{ 的符号}.
\]

## P3　二阶检测

正权有限窗中只要存在离线零点：

\[
\sum m_\rho w_\rho
(\Re\rho-\tfrac12)^2>0.
\]

## P4　构型阶不是重数阶

若实验把 \(k\)-点构型和 \(k\) 重零点混为同一导数变量，其预测应在 simple zeros 主导的数据上失败。

## P5　模五标量商不恢复孪生方向

只观察：

\[
\chi_5(n)\chi_5(n+2)
\]

无法区分有序词：

\[
(+1,-1),\quad(-1,+1).
\]

## P6　模三曲率零即阻塞

在 \(2/4\)-gap 语言中出现任意 \(\kappa=0\)，必使构型模 \(3\) inadmissible。

## P7　高阶 connected sector 必须减去 partitions

若把原始 \(k\)-point moment 直接称为纯 \(k\)-体纠缠，在由低阶变量乘积构造的测试数据上会产生假阳性。

## P8　全局零点纠缠不是函数方程推论

若构造出的 orbit generating functional 在不同 mirror orbits 间完全因子化，则所有跨轨道 cumulants 为零；这将否定“所有离线零点共同纠缠”的强版本，同时保留每对内部相关。

## P9　specific shift 需要 Fourier 反演

仅有聚合 short-interval variance 不能无损确定 \(h=2\) 系数；必须增加足够测试核或全 polyspectrum。

## P10　几何 Möbius 需要 monodromy

若找不到自然参数回路和 sheet-flip transport，则 Möbius strip/Klein bottle 只能保留为模型，不得晋升为 ζ 的内禀拓扑。

## P11　投影盲性不决定 RH

存在隐藏 holonomy 的两个 lift 仍可具有完全相同的 classical divisor。除非 lift–divisor 桥被证明，隐藏状态不能作为离线零点证据。

## P12　真正的新桥应先在 \(k=2\) 关闭

若 Trace–Jet Bridge 连 twin/二点有限核都不能构造，则不得直接宣称一般 \(k\)-点统一频谱。

---

# 第十七部　计算与实验路线

## 54. Prime constellation atlas

对固定 \(k,D\)：

1. 枚举
   \[
   H\subseteq[0,D],\quad 0\in H,\quad |H|=k;
   \]
2. 按平移与反射取商；
3. 计算
   \[
   R_p(H),\nu_p(H),L_p(H),\quad p\le P;
   \]
4. 保存：
   - gap Zeckendorf words；
   - ternary gap curvature；
   - \(\chi_5\) ordered word；
   - local automaton histories；
   - truncated singular-series ledger。

## 55. Connected cumulant atlas

从 prime data 计算：

\[
M_A(X)
=
\frac1X\sum_{n\le X}
\prod_{h\in A}\Lambda(n+h),
\]

再用 partition Möbius inversion计算 \(\kappa_A(X)\)。

必须同时报告所有 proper-subset moments，防止把低阶分解误认为高阶 connected signal。

## 56. Zero orbit atlas

对已知零点数据：

1. 建立 \(C,R,J\) 轨道；
2. 记录：
   \[
   \delta,\gamma,m;
   \]
3. 生成多尺度 Zeckendorf orbit threads；
4. 计算：
   \[
   \mathfrak D_T(\tau),\quad
   \sum\delta^{2r},\quad
   E_{ab};
   \]
5. 检查枚举不变性；
6. 不把“所有已知零点在线”外推成 RH。

## 57. Cross-polyspectral experiment

以同一窗函数族比较：

- prime shift \(k\)-cumulants；
- zero \(k\)-level statistics；
- Fourier/Paley–Wiener test kernel。

目标不是拟合一条漂亮曲线，而是寻找一个满足：

- 规范明确；
- 截断误差可界；
- 可反演；
- 对不同 \(H\) 有分辨率；

的有限 Trace–Jet dictionary。

---

# 第十八部　理论的最终形式

## 58. 六层结构

\[
\boxed{
\begin{aligned}
\text{Layer 1: }&
H\subset\mathbb Z
&&\text{加法构型};\\
\text{Layer 2: }&
R_p(H),\nu_p(H),\chi_{5,H}
&&\text{局部 residue memory};\\
\text{Layer 3: }&
\mathcal M_H,\mathcal K_H
&&\text{moment/cumulant completion};\\
\text{Layer 4: }&
\text{polyspectrum}
&&\text{频域编码};\\
\text{Layer 5: }&
G_\zeta\text{-orbits},\ \operatorname{ZOC}
&&\text{零点镜像线程};\\
\text{Layer 6: }&
\Xi_H,\ q_H(\rho)
&&\text{开放 Trace–Jet bridge}.
\end{aligned}
}
\]

---

## 59. 最终统一命题

本理论所允许的最强诚实表述是：

\[
\boxed{
\begin{gathered}
\text{ζ 的普通 Euler 乘积给出乘法坐标的独立基测度；}\\
\text{素数构型由加法平移后的联合 observables 与 connected jets 给出；}\\
\text{零点由 completed transform 的对称轨道与 divisor jets 给出；}\\
\text{Zeckendorf 线程为有限观察者提供规范的多尺度编码；}\\
\text{若 Trace–Jet Bridge 存在，则全部零点相关塔可作为全部}\\
\text{有限 prime-constellation cumulants 的统一频谱响应。}
\end{gathered}
}
\]

---

## 60. 对用户原始直觉的最终裁决

### “所有离线零点对是一种量子纠缠”

可保留为两层命题：

1. **已可严格定义：** 每个 mirror pair 有完美符号反相关；
2. **开放猜想：** 不同 mirror orbits 之间存在非零 connected cumulants；
3. **量子版本：** 还需自然 Hilbert lift 和非可分离性证明。

### “离线零点信息是 Zeckendorf 反码”

严格修正为：

\[
\boxed{
\text{相同幅值 Zeckendorf completion thread}
+
\text{相反 transverse sign sheet}.
}
\]

### “孪生、三元组、四元组对应二、三、四点读数”

严格成立于 source cumulant jet：

\[
\boxed{
|H|=k
\Longrightarrow
\text{构型 connected coefficient是第 }k\text{ 个混合源 jet}.
}
\]

### “完整对称使 RH 不可观察，因此 RH 应该错误”

该推理不成立：

- 离线四元组不破坏完整对称；
- RH 是 fixed-locus localization，不是 symmetry restoration；
- 一阶 transverse 读数确实盲；
- 二阶正缺陷严格可见；
- RH 当前真值必须由额外分析机制决定。

### “莫比乌斯、Klein bottle、衔尾蛇”

严格内容有两项：

1. Klein 四群轨道的四边 Ouroboros cycle；
2. moment–cumulant 的 partition Möbius inversion。

几何 Möbius/Klein bottle 必须另加 monodromy 数据。

---


# 第十九部　相对仓库现状的新增理论账

## 61. 本卷新增而非简单重命名的对象

### N1　`ZeckendorfRealThread`

把任意非负实数表示为：

\[
\bigl(
\operatorname{wdigits}
\lfloor\varphi^N x\rfloor
\bigr)_{N\ge0}
\]

并给出显式误差与单射重构。

### N2　`ZeckendorfOrbitCode`

把零点 centered coordinates 的两个 sign bits、两个 Zeckendorf magnitude threads 与 multiplicity code 合并，并使 \(C,R,J\) 作用成为显式 sign flips。

### N3　`TernaryGapCurvature`

在 \(2/4\)-gap 语言中定义：

\[
\kappa_j\in\{-1,0,+1\},
\]

并证明模 \(3\) admissibility 等价于 \(\kappa_j\neq0\)。

### N4　`AlternatingMirrorParity`

证明稠密 admissible gap word 的镜像在偶数点时 self-code、奇数点时 complement-code。

### N5　`LocalConstellationCorrelation`

把 Hardy–Littlewood local factor 写成 finite residue probability 的 joint/product ratio，而不是只把奇异级数当作外部常数。

### N6　`SquareZeroCorrelationCompletion`

用交换平方零源变量在一个有限对象中同时保存全部 subset moments，并由有限对数提取 connected cumulants。

### N7　`ConnectedSingularSeries`

在 Hardy–Littlewood 子构型前件下，用 partition Möbius inversion 定义并导出 connected singular-series hierarchy。

### N8　`JetTrigrading`

把构型大小、零点重数和 transverse 可见阶严格分成：

\[
(k,m,2r).
\]

### N9　`OrbitEntanglementHierarchy`

区分：

1. mirror pair classical anti-correlation；
2. cross-orbit connected structural entanglement；
3. 需要 Hilbert lift 的 quantum entanglement。

### N10　`CorrelationCompletedXi / TraceJetBridge`

给出从具体加法构型 source jets 到 zero-orbit spectral charges 的精确开放接口。

### N11　`CoherentDivisorQuotient`

把黄金 germ 与一般 prime-addressed系统中的 finite local zeros 从 global coherent divisor 中分离。

### N12　`CumulantOuroboros`

把“衔尾蛇/莫比乌斯”落到严格的：

\[
\mathcal M=\exp\mathcal K,
\qquad
\mathcal K=\log\mathcal M
\]

和 partition-lattice Möbius inversion，而不是只保留拓扑比喻。

## 62. 新理论的最小不可删核心

若将本卷压缩为最小内核，必须保留以下五条：

\[
\boxed{
\begin{aligned}
&\text{(i) symmetry orbit }\neq\text{ fixed-line localization};\\
&\text{(ii) additive constellations are connected source jets};\\
&\text{(iii) mirror closure removes odd jets but preserves even defects};\\
&\text{(iv) Zeckendorf codes amplitudes as completion threads and mirrors as sign complements};\\
&\text{(v) a genuine prime–zero identification requires a Trace–Jet Bridge}.
\end{aligned}
}
\]

删除任意一条，理论都会退化为：

- 错误的 symmetry argument；
- 普通的 prime \(k\)-tuple 记号；
- 普通的 Zeckendorf 序列化；
- 或没有可证伪接口的量子隐喻。

---

# 结论

本理论把“零点对”“素数构型”“黄金反码”“量子纠缠”“jet 深度”从同义比喻中拆开，再通过明确接口重新连接：

\[
\boxed{
\text{prime tuples are source jets;}
}
\]

\[
\boxed{
\text{zero multiplicities are spectral jets;}
}
\]

\[
\boxed{
\text{off-line depth is an even transverse jet;}
}
\]

\[
\boxed{
\text{entanglement is connected non-factorization;}
}
\]

\[
\boxed{
\text{Zeckendorf is a canonical finite-resolution thread;}
}
\]

\[
\boxed{
\text{the missing object is a correlation-completed xi determinant.}
}
\]

真正值得向仓库补充的，不是“RH 为假”的无前件宣言，而是这一套能同时产生：

- 初等可闭合定理；
- 明确反例；
- 可计算构型 atlas；
- 可形式化 cumulant algebra；
- 可证伪 Trace–Jet frontier；

的完整研究架构。

---

# 参考文献与仓库锚点

## 经典与现代文献

1. G. H. Hardy and J. E. Littlewood, *Some Problems of “Partitio Numerorum”; III: On the Expression of a Number as a Sum of Primes*, Acta Mathematica 44 (1923).
2. H. L. Montgomery, *The Pair Correlation of Zeros of the Zeta Function*, Proceedings of Symposia in Pure Mathematics 24 (1973), DOI: 10.1090/PSPUM/024/9944.
3. D. A. Goldston and H. L. Montgomery, *Pair Correlation of Zeros and Primes in Short Intervals*, Progress in Mathematics 70 (1987).
4. T. H. Chan, *More Precise Pair Correlation of Zeros and Primes in Short Intervals*, Journal of the London Mathematical Society 68 (2003), DOI: 10.1112/S0024610703004769.
5. Z. Rudnick and P. Sarnak, *Zeros of Principal L-functions and Random Matrix Theory*, Duke Mathematical Journal 81 (1996), DOI: 10.1215/S0012-7094-96-08115-6.
6. J. Pintz, *On the Singular Series in the Prime k-Tuple Conjecture*, arXiv:1004.1084.
7. K. Ford, *Simple Proof of Gallagher’s Singular Series Sum Estimate*, arXiv:1108.3861.
8. V. Kuperberg, *Sums of Singular Series with Large Sets and the Tail of the Distribution of Primes*, arXiv:2210.09775.

## 仓库锚点

- `D5/S3/Weil/ZetaBridge/ConvolutionSquareOffLineOrbits`
- `D5/S3/Zeros/Symmetry/CriticalDampingFlatness`
- `D5/S3/Zeros/Symmetry/MultiscaleFingerprintAppend`
- `D5/S3/Zeros/CriticalZeroTransverseGap`
- `D5/S3/Analytic/Boundary/InteriorCurvatureCriterion`
- `D5/S3/Analytic/PoissonPhaseHolonomy/PairwisePoissonHolonomyEnergy`
- `D5/S3/Observer/AgencyHolonomy/GoldenCharacterQuotient`
- `D5/S3/Observer/AgencyHolonomy/GoldenScalarDihedralBlindness`
- `D5/S3/Observer/AgencyHolonomy/ScalarMemoryBlindness`
- `D5/S3/Observer/AgencyHolonomy/OrderedPrimeHolonomyCasimir`
- `D5/S3/Weil/ZetaBridge/ZeroSumEnumerationInvariance`
- `D5/S3/Weil/ZetaBridge/PrimeJumpDecomposition`
- `D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf`
- `D5/S1/Deficit/ZeckendorfDisplacementReading`
- `D5/S3/Analytic/GoldenEulerBeta`
- `D5/S3/Analytic/EulerGerm/GoldenGermSecondOrderFactorization`
