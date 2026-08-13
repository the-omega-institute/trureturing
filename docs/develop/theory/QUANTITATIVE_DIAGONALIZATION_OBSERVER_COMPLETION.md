# 投影、商余与完成下的定量对角化
## 自然性、循环余量、Fourier 扇区及其素数—Li–Cayley 实现
### Quantitative Diagonalization under Projection, Quotient Remainders, and Completion

**作者：** Auric  
**机构：** The Omega Institute  
**日期：** 2026-08-13

> **文档地位。** 本文是 `docs/develop/theory` 中的论文稿与理论摄入源，不是 Lean 数学真源。文中标明为仓库既有锚点的结果，以其 Lean 声明为准；本文新增定理均给出纸面证明，但在获得 Lean proof term、依赖闭包与冻结收据以前，不得在治理层标记为 `Closed`。
>
> **理论承接。** 本文续接 [GICT](./GICT.md) 的不动点—对角化链与 [OBSERVER-QUANTUM](./OBSERVER-QUANTUM.md) 的有限观察—完成结构。本文不以语义相似代替数学桥，而以交换图、商纤维、覆盖、角色投影和联合极限为承重接口。
>
> **核心非主张。** 本文没有证明 Riemann 假设，没有把光速定义为信息处理率，没有把量子上下文性等同于 Cantor 对角化，也没有把欧几里得素数证明冒充为自应用表对角化。

---

## 摘要

本文建立一套统一但有明确边界的定量对角理论。

第一，对多尺度评价系统定义扭曲对角算子
\[
\Delta_i(E)(a)=\tau_i(E(a,a)),
\]
并比较“先在细尺度对角化再投影”与“先投影再在粗尺度对角化”：
\[
Q_{j,i}\Delta_j
\quad\text{与}\quad
\Delta_iP_{j,i}.
\]
本文证明总缺陷可分解为对角读取失配与扭曲自然性失配，缺陷沿尺度满足复合不等式；严格自然族唯一下降到逆极限，而在有限坐标可提升时，极限算子的存在反过来强制有限层自然性。

第二，本文把“取反是一种商余结构”收紧为有限群作用理论。对自由对合，选定截面以后
\[
x\longleftrightarrow([x],\varepsilon),
\qquad
\sigma([x],\varepsilon)=([x],-\varepsilon).
\]
对自由循环作用则推广为
\[
x\longleftrightarrow([x],r),
\qquad
T([x],r)=([x],r+1),
\quad r\in C_m.
\]
连续全局余坐标存在当且仅当相应有限覆盖平凡；非平凡连通覆盖只能通过局部截面及有限群 cocycle 命名。

第三，对有限置换，幂固定点谱、循环长度谱和对角逃逸谱互相确定。对任意有限自映射，本文证明这些统计只读取周期核，完全看不见流入周期以前的瞬态树。该周期核还产生有限动力学 zeta：
\[
\zeta_\tau(t)
=
\prod_d(1-t^d)^{-c_d}
=
\det(I-tU_\tau)^{-1}.
\]

第四，在复线性与 Hilbert 空间中，有限阶对称通过 Fourier 投影
\[
P_\ell
=
\frac1m\sum_{r=0}^{m-1}\omega^{-\ell r}T^r
\]
规范分解为离散角色扇区。对角扭曲在第 \(\ell\) 扇区中仅乘以角色相位；不变扇区是商影子，全部非平凡扇区共同保存余信息。密度矩阵给出连续的扇区概率，而单次离散结果来自概率读出，不是连通态空间上的非恒定连续确定标签。

第五，欧几里得 \(+1\) 构造被精确识别为 CRT 余空间中的生成平移
\[
\mathbf x\mapsto\mathbf x+\mathbf1.
\]
布尔取反恰是模二加一。有限加法角色将该平移对角化为单位根相位，随后因子分解从逃逸整数中提取账本外素数。

最后，本文把有限角色延拓到 Li–Cayley 几何。写
\[
C(\rho)=e^{\beta+i\theta},
\]
函数方程镜像将 \(\beta\) 与 \(-\beta\) 配对；四元零点轨道贡献为
\[
L_n(\rho)
=
4-4\cosh(n\beta)\cos(n\theta).
\]
因此 Li 探针放大的是镜像商中保留的无向连续深度 \(|\beta|\)，不是临界线左右的布尔标签。任一非零深度都能沿相位复现子序列局部趋于负无穷；从该局部结论到完整 Li 系数为负，仍需证明其余零点或素数端余项不能实现同阶抵消，并需对探针阶数与截断高度给出联合一致控制。

---

# 1. 仓库既有承重锚点

本文复用而不重复以下既有 Lean 结果：

- `D5/S0/Diagonal/EscapeCount.escaped_listing_card`；
- `D5/S0/Diagonal/CaptureCount.capture_inter_card`；
- `D5/S0/Diagonal/CaptureCount.capture_independent`；
- `D5/S0/Diagonal/DistanceProfile.distance_profile_card`；
- `D5/S0/Diagonal/TypicalDensity.typical_density_failure_probability_tendsto_zero`；
- `D5/S0/Diagonal/EquivariantEscape.equivariant_escaped_card`；
- `D5/S3/Observer/MetricGeometry/WindowObserverDistance.window_observer_distance_eq_cycle_distance`；
- `D5/S1/Solenoid/PathOrbitClassification.path_joined_iff_real_flow_orbit`；
- `D5/S3/Analytic/LiCausalTrichotomy`；
- `D5/S3/Weil/ZeroSum`、`SpectralDynamics` 与 `WeilIdentity`。

设有限地址数 \(|A|=n\)、有限值数 \(|Y|=q\)，扭曲 \(\tau:Y\to Y\) 有 \(k\) 个不动点。仓库既有精确计数为
\[
\#\{E:\Delta_\tau(E)\notin\operatorname{range}(E)\}
=(q^n-k)^n.
\]
本文把该公式作为有限层输入，并研究扭曲幂、投影与完成中的结构。

---

# 2. 多尺度对角系统

## 定义 2.1（评价表、读取与扭曲）

给定地址集 \(A\) 与值集 \(Y\)，令
\[
\mathcal T(A,Y)=Y^{A\times A},
\qquad
\mathcal U(A,Y)=Y^A.
\]
定义对角读取
\[
D(E)(a)=E(a,a),
\]
逐点扭曲
\[
\Theta_\tau(u)=\tau\circ u,
\]
以及扭曲对角
\[
\Delta_\tau=\Theta_\tau D,
\qquad
\Delta_\tau(E)(a)=\tau(E(a,a)).
\]

## 定义 2.2（多尺度投影）

令 \(I\) 为预序。每个尺度 \(i\) 有
\[
\mathcal T_i=Y_i^{A_i\times A_i},
\qquad
\mathcal U_i=Y_i^{A_i},
\qquad
\Delta_i=\Theta_iD_i.
\]
对 \(j\succeq i\)，给定
\[
P_{j,i}:\mathcal T_j\to\mathcal T_i,
\qquad
Q_{j,i}:\mathcal U_j\to\mathcal U_i,
\]
并满足恒等与复合律。必须区分 \(P\) 与 \(Q\)：前者投影二维评价表，后者投影一维对角输出。

设 \(\mathcal U_i\) 上有伪度量 \(d_i\)，定义
\[
\varepsilon^\Delta_{j,i}(E)
=
d_i(Q_{j,i}\Delta_jE,\Delta_iP_{j,i}E),
\]
\[
\varepsilon^D_{j,i}(E)
=
d_i(Q_{j,i}D_jE,D_iP_{j,i}E),
\]
\[
\varepsilon^\tau_{j,i}(u)
=
d_i(Q_{j,i}\Theta_ju,\Theta_iQ_{j,i}u).
\]

## 定理 2.3（总缺陷分解）

若 \(d_i\) 满足三角不等式，且 \(\Theta_i\) 为 \(L_i\)-Lipschitz，则
\[
\boxed{
\varepsilon^\Delta_{j,i}(E)
\le
\varepsilon^\tau_{j,i}(D_jE)
+L_i\varepsilon^D_{j,i}(E).}
\]

### 证明

在
\[
Q\Theta_jD_jE
\quad\text{与}\quad
\Theta_iD_iPE
\]
之间插入 \(\Theta_iQD_jE\)。第一段距离正是扭曲自然性缺陷，第二段由 \(\Theta_i\) 的 Lipschitz 性控制为 \(L_i\varepsilon^D\)。 \(\square\)

## 推论 2.4（严格自然性）

若
\[
QD_j=D_iP,
\qquad
Q\Theta_j=\Theta_iQ,
\]
则
\[
\boxed{Q\Delta_j=\Delta_iP.}
\]

## 定理 2.5（尺度复合）

若 \(k\preceq i\preceq j\)，且 \(Q_{i,k}\) 为 \(L^Q_{i,k}\)-Lipschitz，则
\[
\boxed{
\varepsilon^\Delta_{j,k}(E)
\le
L^Q_{i,k}\varepsilon^\Delta_{j,i}(E)
+
\varepsilon^\Delta_{i,k}(P_{j,i}E).}
\]

### 证明

利用投影复合律，在
\[
Q_{i,k}Q_{j,i}\Delta_jE
\]
与
\[
\Delta_kP_{i,k}P_{j,i}E
\]
之间插入 \(Q_{i,k}\Delta_iP_{j,i}E\)，再用三角不等式。 \(\square\)

反复应用即得任意有限尺度链上的加权 telescoping bound。

---

# 3. 限制自然性、商聚合与逆极限

## 定理 3.1（坐标限制严格自然）

设地址嵌入 \(\iota:A_i\hookrightarrow A_j\)、值映射 \(q:Y_j\to Y_i\)，并定义
\[
P(E)(a,b)=q(E(\iota a,\iota b)),
\qquad
Q(u)(a)=q(u(\iota a)).
\]
若
\[
q\tau_j=\tau_iq,
\]
则
\[
\boxed{Q\Delta_j=\Delta_iP.}
\]

### 证明

逐坐标计算：
\[
Q\Delta_j(E)(a)
=q(\tau_j(E(\iota a,\iota a)))
=\tau_i(q(E(\iota a,\iota a)))
=\Delta_iP(E)(a).
\]
\(\square\)

所以“有限”本身不会产生缺陷；缺陷必须来自地址合并、非对角信息注入粗层自坐标，或扭曲与聚合不交换。

## 命题 3.2（最小读取反例）

令细地址为 \(\{0,1\}\)，粗地址为单点，布尔表投影取全表 OR，输出投影取对角 OR。若
\[
E(0,0)=E(1,1)=0,
\quad E(0,1)=1,
\quad E(1,0)=0,
\]
则
\[
Q(DE)=0,
\qquad
D(P(E))=1.
\]
非对角值被聚合进粗层自坐标。

## 命题 3.3（最小扭曲反例）

对 \(u=(0,1)\)，布尔 OR 与 NOT 满足
\[
\operatorname{OR}(\neg u)=1,
\qquad
\neg\operatorname{OR}(u)=0.
\]
因此聚合与扭曲不自然交换。

## 定理 3.4（严格自然族下降到逆极限）

设 \((\mathcal T_i,P_{j,i})\)、\((\mathcal U_i,Q_{j,i})\) 为逆系，且
\[
Q_{j,i}\Delta_j=\Delta_iP_{j,i}
\]
对全部 \(j\succeq i\) 成立。则存在唯一
\[
\boxed{
\Delta_\infty:
\varprojlim_i\mathcal T_i
\to
\varprojlim_i\mathcal U_i}
\]
满足
\[
\pi_i^\mathcal U\Delta_\infty
=
\Delta_i\pi_i^\mathcal T.
\]

### 证明

对相容族 \((E_i)_i\)，定义
\[
\Delta_\infty((E_i)_i)=(\Delta_i(E_i))_i.
\]
有限层自然性保证右侧相容；坐标投影唯一决定逆极限元素。 \(\square\)

## 定理 3.5（满射坐标下的反向判据）

若每个 \(\pi_j^\mathcal T\) 满射，并存在坐标兼容的 \(\Delta_\infty\)，则
\[
\boxed{Q_{j,i}\Delta_j=\Delta_iP_{j,i}.}
\]

### 证明

任取有限表 \(E_j\)，由满射性提升为 \(E_\infty\)，再沿逆极限相容方块逐步计算两条有限路径相等。 \(\square\)

因此非零缺陷是有限层算子不能下降到完成对象的精确证书。

---

# 4. 对合、轨道商与界面

## 定义 4.1（对合轨道商）

设 \(\sigma:X\to X\) 满足 \(\sigma^2=\mathrm{id}\)。定义
\[
x\sim y
\iff y=x\text{ 或 }y=\sigma x,
\]
商映射为
\[
\pi:X\to B=X/\langle\sigma\rangle.
\]

## 命题 4.2（商纤维）

\[
\pi(\sigma x)=\pi(x),
\qquad
\pi^{-1}(\pi x)=\{x,\sigma x\}.
\]
非固定点纤维有两点，固定点纤维坍缩为单点。

## 定理 4.3（极性—截面对应）

若 \(\sigma\) 无固定点，则下列数据一一对应：

1. 极性函数 \(\chi:X\to\{\pm1\}\)，满足 \(\chi(\sigma x)=-\chi(x)\)；
2. 商映射截面 \(s:B\to X\)。

### 证明

极性函数在每个二点轨道中唯一选出 \(+1\) 代表。反之，截面把轨道中的选中代表标为 \(+1\)，另一个标为 \(-1\)。 \(\square\)

## 推论 4.4（商—余正规形）

选定截面后
\[
\boxed{X\cong B\times\{\pm1\},}
\qquad
\boxed{\sigma(b,\varepsilon)=(b,-\varepsilon).}
\]
不同截面之间由唯一 \(B\to\{\pm1\}\) 的规范函数变换。

## 定理 4.5（连通性障碍）

从非空连通空间到离散空间的连续映射必为常值。因此连通空间上不存在非平凡连续全局极性。

### 证明

连续像保持连通，而离散空间的连通子集只能是单点。 \(\square\)

## 定理 4.6（反不变量产生界面极性）

设 \(h:X\to\mathbb R\) 连续且
\[
h(\sigma x)=-h(x).
\]
令
\[
\mathcal I=h^{-1}(0),
\quad
X_\pm=h^{-1}(\mathbb R_{\gtrless0}).
\]
则 \(\mathcal I\) 闭且 \(\sigma\)-不变，\(\sigma(X_+)=X_-\)，固定点均在 \(\mathcal I\) 中；在 \(X\setminus\mathcal I\) 上，\(\operatorname{sgn}h\) 是连续极性。

因此离散极性来自界面切割、局部截面、分支或概率读出，而不是无界面的全局连续标签。

## 定理 4.7（对合对角的商影子）

若 \(\tau:Y\to Y\) 为对合，\(\pi:Y\to Y/\langle\tau\rangle\) 为轨道商，则逐点商映射 \(\Pi_A\) 满足
\[
\boxed{
\Pi_A\Delta_\tau(E)=\Pi_AD(E).}
\]
若选定极性通道 \(\chi(\tau y)=-\chi(y)\)，则
\[
\boxed{
\Chi_A\Delta_\tau(E)=-\Chi_AD(E).}
\]

因此对合型对角化保持商坐标，只翻转纤维余坐标。

## 结论 4.8（自然性不等于忠实性）

只读取轨道商的观察者会得到零扭曲缺陷，因为它已经把 \(y\) 与 \(\tau y\) 识别。零缺陷只证明交换，不证明扭曲信息未被商掉。

---

# 5. 有限循环余量与覆盖

令
\[
C_m=\mathbb Z/m\mathbb Z,
\qquad m\ge2,
\]
且 \(T^m=\mathrm{id}\) 自由作用于 \(X\)。

## 定义 5.1（循环余坐标）

\[
\kappa:X\to C_m,
\qquad
\kappa(T^rx)=\kappa(x)+r.
\]

## 定理 5.2（截面—循环余坐标对应）

轨道商截面与循环余坐标一一对应。选定截面以后
\[
\boxed{
X\cong(X/C_m)\times C_m,
\qquad
T(b,r)=(b,r+1).}
\]

### 证明

给定截面，每个点唯一写成 \(T^rs([x])\)，令余坐标为 \(r\)。给定余坐标，每个轨道唯一的零余量点构成截面。自由性保证唯一。 \(\square\)

布尔 NOT 是 \(m=2\) 的最小循环平移，而一般“换过来”可以有 \(m-1\) 个非零方向。

## 定理 5.3（自由有限作用的覆盖）

若 \(X\) Hausdorff、作用由同胚给出，则
\[
\pi:X\to X/C_m
\]
是 \(m\) 重覆盖。

### 证明

一个有限自由轨道的点两两不同。由 Hausdorff 性选择两两不交邻域，再取其有限交，使全部平移片互不相交并均匀映到同一商邻域。 \(\square\)

## 定理 5.4（连续余坐标的平凡化判据）

下列条件等价：

1. 存在连续全局截面；
2. 存在连续 \(C_m\)-值余坐标；
3. 覆盖同胚于乘积 \((X/C_m)\times C_m\)。

若 \(X\) 非空连通且 \(m>1\)，三者均不成立。

## 定理 5.5（局部过渡 cocycle）

对局部截面 \(s_i:U_i\to X\)，交叠上存在唯一局部常值
\[
g_{ij}:U_i\cap U_j\to C_m
\]
满足
\[
s_j=T^{g_{ij}}s_i,
\]
并有
\[
g_{ik}=g_{jk}+g_{ij}.
\]
存在全局截面当且仅当该 cocycle 为 coboundary：存在 \(h_i\) 使
\[
g_{ij}=h_i-h_j.
\]

## 定理 5.6（多方向确定性逃逸）

对
\[
\Delta_r(E)(a)=T^r(E(a,a)),
\]
若 \(r\neq0\)，则 \(\Delta_r(E)\) 不等于任何一行。若 \(A\neq\varnothing\)，则 \(r\mapsto\Delta_r(E)\) 单射，故有 \(m-1\) 个不同逃逸方向。

### 证明

若 \(\Delta_r(E)=E(a,-)\)，比较第 \(a\) 坐标得 \(T^r(E(a,a))=E(a,a)\)，与自由性矛盾。两个不同余量产生同一对角对象时，同样在任一对角坐标上违反自由性。 \(\square\)

---

# 6. 循环谱与对角逃逸谱

设有限置换 \(\tau:Y\to Y\)，记长度 \(d\) 的循环数为 \(c_d\)，并令
\[
F_r=|\operatorname{Fix}(\tau^r)|.
\]

## 定理 6.1（幂固定点公式）

\[
\boxed{F_r=\sum_{d\mid r}d\,c_d.}
\]

### 证明

长度 \(d\) 的循环在 \(d\mid r\) 时贡献全部 \(d\) 个固定点，否则贡献零。 \(\square\)

## 定理 6.2（Möbius 反演）

\[
\boxed{
c_d
=
\frac1d
\sum_{e\mid d}
\mu(d/e)F_e.}
\]

### 证明

对关系 \(F_r=\sum_{d\mid r}a_d\)、\(a_d=d c_d\) 应用算术 Möbius 反演。 \(\square\)

## 定理 6.3（逃逸谱）

当 \(|A|=n\ge1\)、\(|Y|=q\) 时，以 \(\tau^r\) 扭曲的逃逸表数量为
\[
\boxed{
N_r
=
\left(q^n-\sum_{d\mid r}d\,c_d\right)^n.}
\]
完整 \((N_r)\) 在已知 \(q,n\) 时恢复全部循环类型。

### 证明

将定理 6.1 给出的不动点数代入既有逃逸计数；取唯一非负整数 \(n\) 次根恢复 \(F_r\)，再用定理 6.2。 \(\square\)

地址数 \(n\ge1\) 是必要边界；空地址系统的计数不能承载固定点信息。

## 定理 6.4（Burnside 平均）

有限群 \(G\) 作用于有限 \(Y\) 时，
\[
\boxed{
\frac1{|G|}\sum_{g\in G}|\operatorname{Fix}(g)|=|Y/G|.}
\]

### 证明

双重计数 \(\{(g,y):gy=y\}\)，并按轨道—稳定子公式求每个轨道的贡献。 \(\square\)

由 Jensen 不等式还得平均逃逸下界
\[
\frac1{|G|}\sum_g(q^n-|\operatorname{Fix}(g)|)^n
\ge
(q^n-|Y/G|)^n.
\]

---

# 7. 周期核、瞬态盲区与有限动力学 ζ

现在允许 \(\tau:Y\to Y\) 为任意有限自映射。

## 定理 7.1（稳定像与周期核）

下降链
\[
Y\supseteq\tau(Y)\supseteq\tau^2(Y)\supseteq\cdots
\]
最终稳定。稳定像 \(P_\tau\) 上的限制 \(\tau|_{P_\tau}\) 是置换，而且 \(P_\tau\) 恰由全部周期点组成。

### 证明

有限基数下降序列最终恒定；稳定像上的满射是双射。稳定像中的点位于有限置换循环上。反之，周期点属于每个 \(\tau^k(Y)\)，故属于稳定像。 \(\square\)

## 定理 7.2（固定点谱只读取周期核）

对全部 \(r\ge1\)，
\[
\boxed{
\operatorname{Fix}(\tau^r)
=
\operatorname{Fix}((\tau|_{P_\tau})^r).}
\]

### 证明

\(\tau^r\) 的固定点必为周期点，故在周期核中；反向包含显然。 \(\square\)

因此逃逸谱完全看不见流入周期以前的瞬态树。具有相同周期循环谱但不同瞬态树的有限函数，产生完全相同的全部 \(N_r\)。

## 定义 7.3（有限动力学 zeta）

在形式幂级数中定义
\[
\zeta_\tau(t)
=
\exp\!\left(
\sum_{r\ge1}\frac{F_r}{r}t^r
\right).
\]

## 定理 7.4（循环乘积）

若周期核中长度 \(d\) 的循环数为 \(c_d\)，则
\[
\boxed{
\zeta_\tau(t)
=
\prod_{d\ge1}(1-t^d)^{-c_d}.}
\]

### 证明

代入 \(F_r=\sum_{d\mid r}d c_d\)，交换形式级数求和：
\[
\sum_{r\ge1}\frac{F_r}{r}t^r
=
\sum_d c_d\sum_{m\ge1}\frac{t^{dm}}m
=-\sum_dc_d\log(1-t^d).
\]
指数化即得。 \(\square\)

## 定理 7.5（迹—行列式表示）

令 \(U_\tau\) 为周期核上的置换算子，则
\[
\boxed{F_r=\operatorname{Tr}(U_\tau^r),}
\qquad
\boxed{
\zeta_\tau(t)=\det(I-tU_\tau)^{-1}.}
\]

### 证明

置换矩阵幂的对角元恰对应 \(\tau^r\) 固定点。长度 \(d\) 的循环块满足
\[
\det(I-tU_d)=1-t^d,
\]
按块相乘并使用定理 7.4。 \(\square\)

所以在 \(q,n\ge1\) 已知时，逃逸谱、幂固定点谱、循环谱、有限动力学 zeta 与置换行列式互相确定；它们共同忽略瞬态树。这一盲区是结构性的。

---

# 8. Fourier 角色扇区

设复向量空间 \(V\) 上有线性算子 \(T\)，满足 \(T^m=I\)。令
\[
\omega=e^{2\pi i/m},
\qquad
P_\ell
=
\frac1m\sum_{r=0}^{m-1}\omega^{-\ell r}T^r.
\]

## 引理 8.1（单位根正交）

\[
\sum_{r=0}^{m-1}\omega^{ar}
=
\begin{cases}
m,&m\mid a,\\0,&m\nmid a.
\end{cases}
\]

## 定理 8.2（Fourier 投影代数）

\[
\boxed{TP_\ell=\omega^\ell P_\ell,}
\]
\[
\boxed{P_\ell P_k=\delta_{\ell k}P_\ell,}
\]
\[
\boxed{\sum_{\ell=0}^{m-1}P_\ell=I.}
\]
因此
\[
\boxed{
V=\bigoplus_{\ell=0}^{m-1}\ker(T-\omega^\ell I).}
\]

### 证明

第一式由循环换指标得到。将第一式代入 \(P_\ell P_k\)，单位根正交关系给出正交幂等性。对全部 \(\ell\) 求和时，只有 \(r=0\) 的 Fourier 和非零。特征空间等于投影像由直接代入得到。 \(\square\)

当 \(m=2\) 时
\[
P_+=\frac{I+T}{2},
\qquad
P_- =\frac{I-T}{2},
\]
线性取反保持偶分量、翻转奇分量，而不是给整个向量贴一个唯一正负标签。

## 定理 8.3（对角扭曲的角色律）

对 \(V\)-值评价表与
\[
\Delta_{T^r}(E)(a)=T^rE(a,a),
\]
有
\[
\boxed{
P_\ell\Delta_{T^r}(E)
=
\omega^{\ell r}P_\ell D(E).}
\]

不变扇区 \(P_0\) 完全看不见扭曲；全部扇区因 \(\sum P_\ell=I\) 而忠实重构原对象。

---

# 9. Hilbert 扇区概率与去相干

设 \(T\) 为有限阶酉算子。由 \(T^*=T^{-1}\) 可证 \(P_\ell^*=P_\ell\)，故它们是两两正交投影。

## 定理 9.1（纯态与混态扇区概率）

对单位向量 \(v\)，
\[
p_\ell(v)=\|P_\ell v\|^2
\]
满足
\[
p_\ell(v)\ge0,
\qquad
\sum_\ell p_\ell(v)=1.
\]
对密度算子 \(\rho\)，
\[
p_\ell(\rho)=\operatorname{Tr}(\rho P_\ell)
\]
同样构成概率分布。

### 证明

由正交分解和 Pythagoras 得纯态公式；正投影与迹归一化给出混态公式。 \(\square\)

循环作用只改变扇区相位，因此
\[
p_\ell(T^rv)=p_\ell(v),
\qquad
p_\ell(T^r\rho T^{-r})=p_\ell(\rho).
\]

## 定理 9.2（角色去相干）

定义
\[
\mathcal D_T(\rho)=\sum_\ell P_\ell\rho P_\ell.
\]
则
\[
p_\ell(\mathcal D_T(\rho))=p_\ell(\rho),
\]
且
\[
P_\ell\mathcal D_T(\rho)P_k=0
\quad(\ell\neq k).
\]

去相干保留扇区概率，删除跨扇区相干。连续存在的是概率向量；一次测量才产生离散标签。只有当允许的可观测量与动力学均不耦合不同扇区时，角色标签才具有超选择意义。

---

# 10. CRT 素数账本是循环平移

设 \(S\) 为非空有限素数集合，
\[
M=\prod_{p\in S}p,
\qquad
R_S=\prod_{p\in S}\mathbb Z/p\mathbb Z.
\]

## 定理 10.1（CRT 加法同构）

\[
\Gamma_S:\mathbb Z/M\mathbb Z\to R_S,
\qquad
[x]_M\mapsto([x]_p)_p
\]
为加法群同构，并满足
\[
\boxed{
\Gamma_S([x+1])=\Gamma_S([x])+\mathbf1.}
\]

### 证明

若所有模 \(p\) 坐标相等，则每个 \(p\mid x-y\)，两两互素性给出 \(M\mid x-y\)，故单射；两侧基数均为 \(M\)，故双射。平移公式逐坐标成立。 \(\square\)

## 推论 10.2（生成单循环）

\(\mathbf x\mapsto\mathbf x+\mathbf1\) 在 \(R_S\) 上是长度 \(M\) 的单循环。

布尔 NOT 恰为 \(\mathbb Z/2\mathbb Z\) 中的 \(+1\)，而不是模二乘以 \(-1\)。

## 定理 10.3（欧几里得逃逸）

\[
\Gamma_S([M])=\mathbf0,
\qquad
\Gamma_S([M+1])=\mathbf1.
\]
所以对全部 \(p\in S\)，\(p\nmid M+1\)。若素数 \(q\mid M+1\)，则 \(q\notin S\)。

因此
\[
\boxed{
\text{CRT 生成平移逃逸}
+
\text{因子分解}
=
\text{账本外素数见证}.}
\]

## 定理 10.4（有限加法角色）

对 \(\mathbf k=(k_p)\in R_S\)，定义
\[
\chi_{\mathbf k}(\mathbf x)
=
\prod_{p\in S}
\exp\!\left(\frac{2\pi i k_px_p}{p}\right).
\]
则
\[
\boxed{
\chi_{\mathbf k}(\mathbf x+\mathbf1)
=
\Omega_{\mathbf k}\chi_{\mathbf k}(\mathbf x),}
\]
其中
\[
\Omega_{\mathbf k}
=
\prod_pe^{2\pi i k_p/p}.
\]
完整角色族分离全部余量，平移算子在角色基中严格单位模。

---

# 11. 从有限角色到 Li–Cayley 复化谐波

有限循环角色是圆周角色 \(z\mapsto z^n\) 在单位根上的限制。把
\[
z=e^{\beta+i\theta}\in\mathbb C^*
\]
代入，得到
\[
\boxed{z^n=e^{n\beta}e^{in\theta},}
\qquad
|z^n|=e^{n\beta}.
\]

## 定理 11.1（全谐波酉界面）

下列条件等价：

1. \(\beta=0\)；
2. \(|z|=1\)；
3. 全部正阶 \(z^n\) 单位模；
4. 某个正阶 \(z^n\) 单位模。

所以单位圆是全部谐波同时酉的唯一径向界面。

## 定理 11.2（镜像商）

定义
\[
J(z)=1/\overline z.
\]
在对数极坐标中
\[
J(\beta,\theta)=(-\beta,\theta),
\]
固定点集为单位圆，且
\[
\boxed{
\mathbb C^*/\langle J\rangle
\cong[0,\infty)\times S^1}
\]
由
\[
(|\beta|,e^{i\theta})
\]
参数化。

## 定理 11.3（镜像对称谐波迹）

\[
\boxed{
z^n+\overline z^{\,n}+z^{-n}+\overline z^{-n}
=4\cosh(n\beta)\cos(n\theta).}
\]

该表达式只依赖镜像商坐标 \((|\beta|,e^{i\theta})\)。

---

# 12. Li–Cayley 临界线与四元轨道

定义
\[
C(s)=1-\frac1s.
\]
直接计算得到
\[
\boxed{
|C(s)|^2-1
=
\frac{1-2\Re s}{|s|^2}.}
\]
因此
\[
\boxed{
\Re s=\frac12
\iff
|C(s)|=1.}
\]

函数方程镜像 \(\mathfrak m(s)=1-\overline s\) 满足
\[
C(\mathfrak m(s))=1/\overline{C(s)}.
\]
令
\[
C(s)=e^{\beta_C(s)+i\theta_C(s)}.
\]
则
\[
\beta_C(\mathfrak m(s))=-\beta_C(s).
\]

## 定理 12.1（临界线的全谐波酉性）

下列条件等价：

1. \(\Re s=1/2\)；
2. \(\beta_C(s)=0\)；
3. 对全部 \(n\ge1\)，\(|C(s)^n|=1\)；
4. 对某个 \(n\ge1\)，\(|C(s)^n|=1\)。

Riemann 假设等价于所有非平凡零点的镜像商深度 \(|\beta_C(\rho)|\) 为零；这只是坐标等价，不是证明。

## 定理 12.2（Li 镜像乘积）

定义
\[
A_n(s)=1-C(s)^n.
\]
由于 \(C(1-s)=C(s)^{-1}\)，有
\[
\boxed{
A_n(s)+A_n(1-s)
=A_n(s)A_n(1-s).}
\]
在临界线上 \(1-s=\overline s\)，故
\[
\boxed{
2\Re A_n(s)=|A_n(s)|^2\ge0.}
\]

## 定理 12.3（四元轨道双曲公式）

若
\[
C(\rho)=e^{\beta+i\theta},
\]
则反射—共轭四元轨道的第 \(n\) 阶贡献为
\[
\boxed{
L_n(\rho)
=4-4\cosh(n\beta)\cos(n\theta).}
\]
它在 \(\beta\mapsto-\beta\) 下不变，所以不读取临界线左右极性，只读取无向深度与相位。

临界线上 \(\beta=0\)，
\[
L_n=8\sin^2(n\theta/2)\ge0.
\]

---

# 13. 非零深度的局部放大与精确阶阈值

## 引理 13.1（相位复现）

对任意 \(\theta\in\mathbb R\)，存在严格递增 \(n_k\to\infty\)，使
\[
\cos(n_k\theta)\to1.
\]

### 证明

有理相位取周期倍数；无理相位由 Dirichlet 有理逼近得到模 \(2\pi\) 趋零的整数子序列。 \(\square\)

## 定理 13.2（局部指数暴露）

若 \(|\beta|>0\)，则存在 \(n_k\to\infty\)，使
\[
\boxed{L_{n_k}(\rho)\to-\infty,}
\]
并且
\[
\boxed{
\frac{L_{n_k}(\rho)}{\cosh(n_k|\beta|)}\to-4.}
\]

### 证明

沿相位复现子序列，\(\cos(n_k\theta)\to1\)，而 \(\cosh(n_k|\beta|)\to\infty\)。代入定理 12.3。 \(\square\)

## 定理 13.3（给定放大阈值的最小阶）

设 \(H\ge1\)。达到
\[
\cosh(n|\beta|)\ge H
\]
的最小非负整数为
\[
\boxed{
n_H(\beta)
=
\left\lceil
\frac{\operatorname{arcosh}(H)}{|\beta|}
\right\rceil.}
\]
固定 \(H>1\) 且 \(|\beta|\downarrow0\) 时，
\[
|\beta|n_H(\beta)
\to
\operatorname{arcosh}(H).
\]

### 证明

\(\cosh\) 在非负实轴严格递增，\(\operatorname{arcosh}\) 为其反函数，再使用上取整不等式。 \(\square\)

该阈值只控制径向双曲因子；具体 Li 符号还需要相位对齐与全局余项控制。

---

# 14. 从局部轨道到完整 Li 系数

在反射—共轭对称求和规范下，设
\[
\lambda_n,L_n(\rho),R_n\in\mathbb R,
\qquad
R_n=\lambda_n-L_n(\rho).
\]

## 定理 14.1（全局支配条件）

若沿定理 13.2 的子序列
\[
\frac{|R_{n_k}|}{\cosh(n_k|\beta|)}\to0,
\]
则
\[
\boxed{\lambda_{n_k}<0}
\]
最终成立。

### 证明

局部项除以正的双曲尺度趋于 \(-4\)，余项除以同一尺度趋于零，所以完整系数的归一化极限为 \(-4\)。 \(\square\)

因此若全部 Li 系数非负，而存在离线轨道，则其他轨道或正则化项必须在相位复现阶数上实现同阶指数抵消。

## 定理 14.2（联合一致控制允许增长阶）

令 \(\lambda_{n,T}\) 为有限对称截断。若 \(n(T)\in N_T\) 且
\[
\sup_{n\in N_T}|\lambda_{n,T}-\lambda_n|\to0,
\]
则
\[
\boxed{
|\lambda_{n(T),T}-\lambda_{n(T)}|\to0.}
\]

### 证明

被选误差逐点不超过给定上确界。 \(\square\)

逐个固定 \(n\) 的收敛不足：取
\[
x_n=0,
\qquad
x_{n,T}=\mathbf1_{n>T},
\]
则每个固定阶最终收敛，但 \(n(T)=T+1\) 的误差恒为一。

所以高阶 Li 探针必须伴随 \((n,T)\) 联合余项界。当前仓库中单侧 Laguerre Li 包与偶、光滑、紧支撑 Weil 测试类尚未由内部定理直接识别；测试类桥接与全局余项控制是两个独立承重缺口。

---

# 15. 统一结构与严格边界

本文区分以下四类经常被“取反”一词混合的操作。

## 15.1 对合纤维交换

\[
([x],\varepsilon)
\mapsto
([x],-\varepsilon).
\]
它保持轨道商，翻转二值余坐标。

## 15.2 循环余量平移

\[
([x],r)
\mapsto
([x],r+1),
\qquad r\in C_m.
\]
布尔 NOT 只是 \(m=2\) 的特例。

## 15.3 Fourier 角色相位

\[
P_\ell T^r
=
\omega^{\ell r}P_\ell.
\]
连续线性空间被规范分解为有限角色子空间，而不是每个状态获得唯一离散标签。

## 15.4 复化谐波放大

\[
e^{\beta+i\theta}
\mapsto
e^{n\beta}e^{in\theta}.
\]
镜像配对商掉径向符号，保留 \(|\beta|\)，并产生 \(\cosh(n|\beta|)\) 的无向深度放大。

由此得到统一骨架：
\[
\boxed{
\text{轨道商}
+
\text{有限余坐标}
+
\text{角色分解}
+
\text{完成方向}.}
\]

但必须保持以下边界：

1. 非可逆扭曲不能自动约化为循环余量；
2. 零自然性缺陷不证明观察忠实；
3. Fourier 扇区不自动成为物理超选择扇区；
4. 有限动力学 zeta 不是 Riemann zeta；
5. 欧几里得逃逸先产生账本外余类，素数由因子分解提取；
6. Li 局部轨道可放大不等于完整 Li 系数已为负；
7. RH 的实质缺口仍是全局正性或等价余项控制。

---

# 16. 主要结论

### 结论 A：对角化与投影的失配可分解

\[
\varepsilon^\Delta
\le
\varepsilon^\tau+L\varepsilon^D.
\]

### 结论 B：严格自然性恰允许对角算子下降到完成对象

在有限坐标可提升时，该条件也是必要的。

### 结论 C：取反的最小正规形是商纤维余坐标变换

对合给出 \(\mathbb Z_2\) 翻转，自由循环作用给出 \(C_m\) 平移。

### 结论 D：连续全局离散余坐标的存在等价于有限覆盖平凡

非平凡连通覆盖只能局部命名，并由 cocycle 记录错位。

### 结论 E：定量逃逸谱读取周期结构

\[
N_r=(q^n-F_r)^n,
\qquad
F_r=\sum_{d\mid r}dc_d.
\]
它恢复周期核循环谱，却严格看不见瞬态树。

### 结论 F：周期核产生迹—行列式—zeta 链

\[
F_r=\operatorname{Tr}(U^r),
\qquad
\zeta_\tau(t)=\det(I-tU)^{-1}.
\]

### 结论 G：Fourier 投影是连续线性空间中的规范离散扇区抽取

不变扇区是商影子，全部角色扇区共同保持忠实。

### 结论 H：欧几里得 \(+1\) 与布尔 NOT 属于同一循环平移家族

CRT 将 \(+1\) 变成 \(+\mathbf1\)，有限角色将其变成单位根相位。

### 结论 I：Li 四元探针测量镜像商后的无向深度

\[
L_n=4-4\cosh(n|\beta|)\cos(n\theta).
\]

### 结论 J：局部放大与 RH 之间的缺口是全局余项

离线轨道局部必可暴露；完整结论要求其余零点或素数端不能同阶抵消，并要求探针阶与截断高度的联合控制。

---

# 17. 形式化状态

仓库已经形式化的输入包括：

- 有限逃逸计数、捕获乘积律、距离剖面与浓缩；
- 有限循环窗口观察者距离；
- solenoid 路径轨道分类；
- 临界线 Cayley 单位模；
- 整数 Li symbol 的因果包；
- 零点反射—共轭对称截断；
- 通过登记经典输入得到的 Weil 显式公式。

本文新增并给出纸面证明、但尚未成为 Lean 真源的结果包括：

- 投影缺陷分解、尺度复合与逆极限判据；
- 对合商余、界面与忠实性区分；
- 循环余坐标、覆盖平凡化与局部 cocycle；
- 扭曲循环谱与逃逸谱恢复；
- 周期核可见性、瞬态盲区与有限动力学 zeta；
- Fourier 角色扇区、Hilbert 概率与角色去相干；
- CRT 生成平移与有限角色对角化；
- Li–Cayley 镜像商、精确深度阈值与全局余项条件。

这些结果在 proof term 落地前不得自动投影为 `Closed`。

---

# 参考文献

1. G. Cantor, “Über eine elementare Frage der Mannigfaltigkeitslehre,” *Jahresbericht der Deutschen Mathematiker-Vereinigung* 1 (1891), 75–78.
2. F. W. Lawvere, “Diagonal Arguments and Cartesian Closed Categories,” Lecture Notes in Mathematics 92, Springer, 1969, 134–145.
3. Euclid, *Elements*, Book IX, Proposition 20.
4. X.-J. Li, “The Positivity of a Sequence of Numbers and the Riemann Hypothesis,” *Journal of Number Theory* 65 (1997), 325–333.
5. E. Bombieri and J. C. Lagarias, “Complements to Li’s Criterion for the Riemann Hypothesis,” *Journal of Number Theory* 77 (1999), 274–287.
6. A. Weil, “Sur les ‘formules explicites’ de la théorie des nombres premiers,” *Communications du Séminaire Mathématique de l’Université de Lund*, supplément (1952), 252–265.
7. E. Artin and B. Mazur, “On Periodic Points,” *Annals of Mathematics* 81 (1965), 82–99.
