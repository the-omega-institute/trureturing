# 投影、商余与完成下的定量对角化
## 自然性、群余坐标、周期—瞬态谱及其素数—Li–Cayley 实现
### Quantitative Diagonalization under Projection, Quotient Remainders, and Completion

**作者：** Auric  
**机构：** The Omega Institute  
**日期：** 2026-08-13

> **文档地位。** 本文是 `docs/develop/theory` 中的单一、自包含论文稿与理论摄入源，不是 Lean 数学真源。仓库既有结果以对应 Lean 声明为准；本文新增定理虽给出纸面证明，但在获得 proof term、依赖闭包与冻结收据以前不得标记为 `Closed`。
>
> **单卷约束。** 正文及此前全部证明型附录均已合并在本文件中；后续扩展也只进入本文件。
>
> **非主张。** 本文没有证明 Riemann 假设，没有把光速定义成信息处理率，没有把量子上下文性等同于 Cantor 对角化，也没有把欧几里得素数证明冒充为自应用表对角化。

---

## 摘要

本文建立一套具有明确可见性边界的定量对角理论。对多尺度评价系统定义
\[
\Delta_i(E)(a)=\tau_i(E(a,a))
\]
并比较
\[
Q_{j,i}\Delta_j
\quad\text{与}\quad
\Delta_iP_{j,i}.
\]
总缺陷分解为对角读取失配与扭曲自然性失配；严格自然族唯一下降到逆极限，在坐标可提升时反向亦成立。

“取反”被收紧为商纤维中的群余坐标变换。自由对合给出
\[
x\leftrightarrow([x],\varepsilon),
\qquad
\sigma([x],\varepsilon)=([x],-\varepsilon),
\]
自由有限群作用给出
\[
x\leftrightarrow([x],g),
\qquad
h\cdot([x],g)=([x],hg).
\]
全局连续余坐标存在当且仅当有限覆盖平凡；一般情形只有局部截面、群值 cocycle 与 monodromy。

对有限置换，幂固定点谱、循环谱与对角逃逸谱互相确定。对任意有限自映射，固定点敏感逃逸谱只看见周期核。本文引入线性化
\[
L_\tau e_y=e_{\tau(y)}
\]
并证明
\[
\operatorname{Tr}(L_\tau^r)=|\operatorname{Fix}(\tau^r)|,
\qquad
\operatorname{rank}(L_\tau^k)=|\tau^k(Y)|.
\]
迹谱恢复周期部分，秩谱恢复零特征值上的 Jordan 块；二者共同确定复 Jordan 形，但仍不能恢复完整函数图。本文给出显式反例。

有限群余量通过 Fourier 角色进入连续线性空间；欧几里得 \(+1\) 是 CRT 余空间中的生成平移。进一步复化为 Li–Cayley 谐波后，零点四元轨道贡献为
\[
L_n(\rho)=4-4\cosh(n\beta)\cos(n\theta).
\]
该式读取镜像商中的无向深度 \(|\beta|\)。离线轨道可局部指数暴露，但从局部暴露到完整 Li 系数变负仍需全局余项控制与 \((n,T)\) 联合截断估计。

---

# 1. 仓库既有锚点

本文复用而不重复：

- `D5/S0/Diagonal/EscapeCount.escaped_listing_card`；
- `CaptureCount.capture_inter_card` 与 `capture_independent`；
- `DistanceProfile.distance_profile_card`；
- `TypicalDensity.typical_density_failure_probability_tendsto_zero`；
- `EquivariantEscape.equivariant_escaped_card`；
- `WindowObserverDistance.window_observer_distance_eq_cycle_distance`；
- `PathOrbitClassification.path_joined_iff_real_flow_orbit`；
- `LiCausalTrichotomy`；
- `ZeroSum`、`SpectralDynamics` 与 `WeilIdentity`。

设 \(|A|=n\)、\(|Y|=q\)，扭曲 \(\tau:Y\to Y\) 有 \(k\) 个不动点。仓库既有精确逃逸计数为
\[
\boxed{
\#\{E:\Delta_\tau(E)\notin\operatorname{range}(E)\}
=(q^n-k)^n.}
\]

---

# 2. 多尺度对角系统

给定地址集 \(A\) 与值集 \(Y\)，令
\[
\mathcal T(A,Y)=Y^{A\times A},
\qquad
\mathcal U(A,Y)=Y^A.
\]
定义
\[
D(E)(a)=E(a,a),
\qquad
\Theta_\tau(u)=\tau\circ u,
\qquad
\Delta_\tau=\Theta_\tau D.
\]

每个尺度 \(i\) 有 \((\mathcal T_i,\mathcal U_i,\Delta_i)\)。对 \(j\succeq i\)，给定
\[
P_{j,i}:\mathcal T_j\to\mathcal T_i,
\qquad
Q_{j,i}:\mathcal U_j\to\mathcal U_i.
\]
前者投影二维评价表，后者投影一维对角输出，二者不能混用。设 \(\mathcal U_i\) 上有伪度量 \(d_i\)，定义
\[
\varepsilon^\Delta_{j,i}(E)
=d_i(Q_{j,i}\Delta_jE,\Delta_iP_{j,i}E),
\]
\[
\varepsilon^D_{j,i}(E)
=d_i(Q_{j,i}D_jE,D_iP_{j,i}E),
\]
\[
\varepsilon^\tau_{j,i}(u)
=d_i(Q_{j,i}\Theta_ju,\Theta_iQ_{j,i}u).
\]

## 定理 2.1（缺陷分解）

若 \(\Theta_i\) 为 \(L_i\)-Lipschitz，则
\[
\boxed{
\varepsilon^\Delta_{j,i}(E)
\le
\varepsilon^\tau_{j,i}(D_jE)
+L_i\varepsilon^D_{j,i}(E).}
\]

### 证明

在 \(Q\Theta_jD_jE\) 与 \(\Theta_iD_iPE\) 之间插入 \(\Theta_iQD_jE\)，再用三角不等式与 Lipschitz 界。\(\square\)

故若
\[
QD_j=D_iP,
\qquad
Q\Theta_j=\Theta_iQ,
\]
则
\[
\boxed{Q\Delta_j=\Delta_iP.}
\]

## 定理 2.2（尺度复合）

若 \(k\preceq i\preceq j\)，且 \(Q_{i,k}\) 为 \(L^Q_{i,k}\)-Lipschitz，则
\[
\boxed{
\varepsilon^\Delta_{j,k}(E)
\le
L^Q_{i,k}\varepsilon^\Delta_{j,i}(E)
+
\varepsilon^\Delta_{i,k}(P_{j,i}E).}
\]
证明是在两端之间插入 \(Q_{i,k}\Delta_iP_{j,i}E\)。反复应用得到加权 telescoping bound。

---

# 3. 限制、聚合与完成

## 定理 3.1（坐标限制自然性）

设地址嵌入 \(\iota:A_i\hookrightarrow A_j\)、值映射 \(q:Y_j\to Y_i\)，并定义
\[
P(E)(a,b)=q(E(\iota a,\iota b)),
\qquad
Q(u)(a)=q(u(\iota a)).
\]
若 \(q\tau_j=\tau_iq\)，则
\[
\boxed{Q\Delta_j=\Delta_iP.}
\]
这是逐坐标恒等式。因此“有限”本身不会制造缺陷。

## 两个最小反例

令细地址为 \(\{0,1\}\)，粗地址为单点，布尔聚合取 OR。

若
\[
E(0,0)=E(1,1)=0,\quad E(0,1)=1,\quad E(1,0)=0,
\]
则
\[
Q(DE)=0,\qquad D(P(E))=1.
\]
非对角信息进入了粗层自坐标。

对 \(u=(0,1)\)，
\[
\operatorname{OR}(\neg u)=1,
\qquad
\neg\operatorname{OR}(u)=0.
\]
所以聚合也可能不与扭曲交换。

## 定理 3.2（逆极限下降与反向判据）

设 \((\mathcal T_i,P_{j,i})\)、\((\mathcal U_i,Q_{j,i})\) 为逆系。若
\[
Q_{j,i}\Delta_j=\Delta_iP_{j,i}
\]
对全部 \(j\succeq i\) 成立，则存在唯一
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
=\Delta_i\pi_i^\mathcal T.
\]
定义即为
\[
\Delta_\infty((E_i)_i)=(\Delta_i(E_i))_i.
\]

反之，若每个有限表坐标都可从极限满射提升，且存在上述坐标兼容的 \(\Delta_\infty\)，则有限层严格自然。故在可提升系统中，对角缺陷正是有限算子不能下降到完成对象的障碍。

---

# 4. 对合、界面与盲自然性

设 \(\sigma^2=\mathrm{id}\)，商为
\[
\pi:X\to B=X/\langle\sigma\rangle.
\]
有
\[
\pi(\sigma x)=\pi(x),
\qquad
\pi^{-1}(\pi x)=\{x,\sigma x\}.
\]

若 \(\sigma\) 无固定点，则截面 \(s:B\to X\) 与极性函数
\[
\chi:X\to\{\pm1\},
\qquad
\chi(\sigma x)=-\chi(x)
\]
一一对应。选定截面后
\[
\boxed{
X\cong B\times\{\pm1\},
\qquad
\sigma(b,\varepsilon)=(b,-\varepsilon).}
\]

若 \(X\) 非空连通，则任意连续映射 \(X\to D\) 到离散空间 \(D\) 都是常值。因此非平凡极性不能是连通空间上的全局连续确定坐标。

若连续 \(h:X\to\mathbb R\) 满足
\[
h(\sigma x)=-h(x),
\]
则
\[
\mathcal I=h^{-1}(0)
\]
是固定界面，且在 \(X\setminus\mathcal I\) 上 \(\operatorname{sgn}h\) 给出极性。离散标签来自界面分侧，而不是无界面的连续离散映射。

对逐点轨道商 \(\Pi_A\)，
\[
\boxed{
\Pi_A\Delta_\sigma(E)=\Pi_AD(E).}
\]
对极性通道 \(\Chi_A\)，
\[
\boxed{
\Chi_A\Delta_\sigma(E)=-\Chi_AD(E).}
\]
所以商观察可以有零自然性缺陷，却完全删除扭曲。定义
\[
\operatorname{sep}_\tau(Q)
=
\inf_{y\notin\operatorname{Fix}(\tau)}d(Qy,Q\tau y),
\]
便得到
\[
\boxed{\text{自然性不等于忠实性}.}
\]

---

# 5. 有限群余坐标、cocycle 与 monodromy

令有限群 \(G\) 自由左作用于 \(X\)，商为 \(B=X/G\)。

## 定理 5.1（群商—余正规形）

选定截面 \(s:B\to X\) 后，每个 \(x\) 唯一写成
\[
x=\gamma_s(x)\cdot s(\pi x),
\qquad
\gamma_s(x)\in G.
\]
故
\[
\boxed{X\cong B\times G},
\qquad
\boxed{h\cdot(b,g)=(b,hg).}
\]

若 \(t(b)=g(b)\cdot s(b)\)，则
\[
\boxed{
\gamma_t(x)=\gamma_s(x)g(\pi x)^{-1}.}
\]

若作用由同胚给出且 \(X\) Hausdorff，则 \(X\to B\) 为有限覆盖。连续全局截面、连续 \(G\)-值余坐标与等变平凡化
\[
X\cong B\times G
\]
三者等价。若 \(X\) 连通而 \(|G|>1\)，三者均不存在。

局部截面 \(s_i\) 在交集上满足
\[
s_i=g_{ij}\cdot s_j,
\]
其中
\[
g_{ik}=g_{ij}g_{jk}.
\]
规范变化 \(s_i'=h_i\cdot s_i\) 给出
\[
\boxed{g'_{ij}=h_i g_{ij}h_j^{-1}.}
\]
全局截面存在当且仅当 cocycle 可规范化为单位元。闭路提升若返回到 \(m\cdot x\) 且 \(m\neq e\)，则全局单值化不可能。圆周双覆盖 \(z\mapsto z^2\) 是最小例子。

## 定理 5.2（群值对角逃逸）

固定 \(h\in G\)，定义
\[
\Delta_h(E)(a)=h\cdot E(a,a).
\]
则
\[
\boxed{
\Pi_A\Delta_h(E)=\Pi_AD(E),}
\qquad
\boxed{
\Gamma_A\Delta_h(E)=h\,\Gamma_AD(E).}
\]
若 \(h\neq e\)，自由性使 \(\Delta_h(E)\) 对所有评价表确定性逃逸。

## 定理 5.3（商观察的信息损失）

设 \(Y\) 是有限自由 \(G\)-集，随机变量 \(Z\) 取值于 \(Y\)。令
\[
B=\pi(Z),\qquad \Gamma=\gamma_s(Z).
\]
则
\[
\boxed{
H(Z)=H(B)+H(\Gamma\mid B).}
\]
商观察丢失的不是固定的 \(\log|G|\)，而是条件余信息
\[
\boxed{
H(Z)-H(\pi Z)=H(\Gamma\mid\pi Z).}
\]
仅在各纤维条件均匀时等于 \(\log|G|\)。

对两个分布 \(P,Q\)，经典相对熵链式法则为
\[
\boxed{
D(P\Vert Q)
=
D(P_B\Vert Q_B)
+
\sum_bP_B(b)D(P_{\Gamma\mid b}\Vert Q_{\Gamma\mid b}).}
\]
所以商投影的数据处理损失正是条件余分布的平均散度。

---

# 6. 循环谱、固定点谱与逃逸谱

设有限置换 \(\tau:Y\to Y\)，长度 \(d\) 的循环数为 \(c_d\)，令
\[
F_r=|\operatorname{Fix}(\tau^r)|.
\]
则
\[
\boxed{F_r=\sum_{d\mid r}d\,c_d,}
\]
并由 Möbius 反演
\[
\boxed{
c_d=\frac1d\sum_{e\mid d}\mu(d/e)F_e.}
\]

当 \(|A|=n\ge1\)、\(|Y|=q\) 时，以 \(\tau^r\) 扭曲的逃逸表数为
\[
\boxed{
N_r
=
\left(q^n-\sum_{d\mid r}d\,c_d\right)^n.}
\]
已知 \(q,n\) 后，完整 \((N_r)\) 恢复全部循环类型。

若有限群 \(G\) 作用于 \(Y\)，Burnside 公式给出
\[
\frac1{|G|}\sum_g|\operatorname{Fix}(g)|=|Y/G|.
\]
由凸性，
\[
\boxed{
\frac1{|G|}\sum_g(q^n-|\operatorname{Fix}(g)|)^n
\ge(q^n-|Y/G|)^n.}
\]

---

# 7. 周期核与有限动力学 zeta

允许 \(\tau:Y\to Y\) 为任意有限自映射。像链最终稳定：
\[
Y\supseteq\tau(Y)\supseteq\tau^2(Y)\supseteq\cdots\supseteq P_\tau.
\]
稳定像 \(P_\tau\) 恰由周期点组成，且 \(\tau|_{P_\tau}\) 是置换。对全部 \(r\ge1\)，
\[
\boxed{
\operatorname{Fix}(\tau^r)
=
\operatorname{Fix}((\tau|_{P_\tau})^r).}
\]
所以固定点敏感逃逸谱完全看不见瞬态树。

定义
\[
\zeta_\tau(t)
=
\exp\!\left(\sum_{r\ge1}\frac{F_r}{r}t^r\right).
\]
若周期核循环数为 \(c_d\)，则
\[
\boxed{
\zeta_\tau(t)
=
\prod_{d\ge1}(1-t^d)^{-c_d}.}
\]

---

# 8. 新结果：Fitting 分解与周期—瞬态双谱

令
\[
V=\mathbb C^Y,\qquad L_\tau e_y=e_{\tau(y)}.
\]

## 定理 8.1（迹与秩的组合意义）

对任意 \(r\ge1\)、\(k\ge0\)，
\[
\boxed{
\operatorname{Tr}(L_\tau^r)
=|\operatorname{Fix}(\tau^r)|,}
\qquad
\boxed{
\operatorname{rank}(L_\tau^k)
=|\tau^k(Y)|.}
\]

### 证明

\(L_\tau^re_y=e_{\tau^r(y)}\)，故第 \(y\) 个对角元在且仅在 \(y\) 为固定点时等于一。另一方面，\(\operatorname{im}L_\tau^k\) 由不同像点对应的标准基向量 \(e_{\tau^k(y)}\) 张成。\(\square\)

因此现有逃逸谱本质上是线性化的迹谱，瞬态衰减则出现在秩谱。

## 定理 8.2（Fitting 分解）

取 \(N\) 使 \(\tau^N(Y)=P_\tau\)。则
\[
\boxed{
V=\ker L_\tau^N\oplus\operatorname{im}L_\tau^N.}
\]
第一部分上 \(L_\tau\) 幂零；第二部分等于
\[
\operatorname{span}\{e_p:p\in P_\tau\}
\]
且 \(L_\tau\) 的限制为周期核置换。

### 证明

周期核部分可逆，因此与 \(\ker L_\tau^N\) 的交为零；再用秩—零度定理。\(\square\)

若 \(q=|Y|\)，则
\[
\boxed{
\det(\lambda I-L_\tau)
=
\lambda^{q-|P_\tau|}
\prod_d(\lambda^d-1)^{c_d},}
\]
\[
\boxed{
\det(I-tL_\tau)
=
\prod_d(1-t^d)^{c_d},}
\qquad
\boxed{
\zeta_\tau(t)=\det(I-tL_\tau)^{-1}.}
\]
幂零瞬态块对 \(\det(I-tL_\tau)\) 恒贡献一，这正是 zeta 的瞬态盲区。

## 定理 8.3（秩差恢复零 Jordan 块）

定义
\[
a_k=\operatorname{rank}(L_\tau^k)-|P_\tau|,
\qquad
b_k=a_{k-1}-a_k.
\]
则 \(b_k\) 等于大小至少为 \(k\) 的零 Jordan 块数；大小恰为 \(k\) 的块数为
\[
\boxed{b_k-b_{k+1}.}
\]

### 证明

大小 \(s\) 的幂零 Jordan 块满足
\[
\operatorname{rank}(J_s^{k-1})-\operatorname{rank}(J_s^k)
=\mathbf1_{\{s\ge k\}}.
\]
对全部块求和。\(\square\)

## 定理 8.4（迹谱与秩谱确定线性相似类）

给定 \(|Y|\)，完整数据
\[
(\operatorname{Tr}(L_\tau^r))_{r\ge1}
\quad\text{和}\quad
(\operatorname{rank}(L_\tau^k))_{k\ge0}
\]
唯一确定 \(L_\tau\) 在 \(\mathbb C\) 上的 Jordan 标准形。

### 证明

迹谱通过固定点公式与 Möbius 反演恢复全部周期循环，因此恢复可对角化的非零单位根部分。秩差恢复零特征值上的全部 Jordan 块。\(\square\)

故增强审计
\[
\boxed{
\mathscr A(\tau)
=
\bigl((N_r)_{r\ge1},(|\tau^k(Y)|)_{k\ge0}\bigr)}
\]
在 \(q,n\ge1\) 已知时确定线性化的复相似类。

## 命题 8.5（双谱仍不恢复完整函数图）

取
\[
Y=\{0,a,b,c,d,e,f,g\}.
\]
定义
\[
\tau_A:\quad
0\mapsto0,\ a,b,c\mapsto0,\ d,e,f\mapsto a,\ g\mapsto b,
\]
以及
\[
\tau_B:\quad
0\mapsto0,\ a,b,c\mapsto0,\ d,e\mapsto a,\ f,g\mapsto b.
\]
二者都只有固定点 \(0\)，且
\[
|Y|=8,\qquad|\tau_A(Y)|=|\tau_B(Y)|=3,\qquad
|\tau_A^k(Y)|=|\tau_B^k(Y)|=1\ (k\ge2).
\]
故迹谱与秩谱全部相同。但根的三个深度一子节点所带叶子数多重集分别为
\[
\{3,1,0\}
\quad\text{与}\quad
\{2,2,0\},
\]
故函数图非同构。

所以
\[
\boxed{
\text{迹谱 + 秩谱恢复线性相似类，
但不恢复带基函数图。}}
\]

## 定理 8.6（因子粗粒化不增加瞬态深度）

若满射 \(\phi:Y\twoheadrightarrow Z\) 满足
\[
\phi\tau=\sigma\phi,
\]
则
\[
\boxed{
\phi(\tau^k(Y))=\sigma^k(Z)}
\]
并有
\[
|\sigma^k(Z)|\le|\tau^k(Y)|.
\]
若 \(\tau\) 的像链在第 \(N\) 步稳定，则 \(\sigma\) 的像链不晚于第 \(N\) 步稳定。

这说明零自然性缺陷之外，还需审计观察投影是否压缩了瞬态秩谱。

---

# 9. Fourier 扇区与 Hilbert 概率

设 \(T^m=I\)，\(\omega=e^{2\pi i/m}\)，定义
\[
P_\ell=\frac1m\sum_{r=0}^{m-1}\omega^{-\ell r}T^r.
\]
单位根正交给出
\[
\boxed{
TP_\ell=\omega^\ell P_\ell,\quad
P_\ell P_k=\delta_{\ell k}P_\ell,\quad
\sum_\ell P_\ell=I.}
\]
因此
\[
V=\bigoplus_\ell\ker(T-\omega^\ell I).
\]

对
\[
\Delta_{T^r}(E)(a)=T^rE(a,a),
\]
有
\[
\boxed{
P_\ell\Delta_{T^r}(E)
=\omega^{\ell r}P_\ell D(E).}
\]
不变扇区是商影子；全部扇区共同忠实。

若 \(T\) 酉，则 \(P_\ell\) 为正交投影。对密度算子
\[
p_\ell(\rho)=\operatorname{Tr}(\rho P_\ell)
\]
构成概率分布。角色去相干
\[
\mathcal D_T(\rho)=\sum_\ell P_\ell\rho P_\ell
\]
保持全部 \(p_\ell\)，并删除 \(P_\ell\rho P_k\) 的跨扇区项。Fourier 扇区只有在允许的可观测量与动力学都不耦合它们时，才成为物理超选择扇区。

---

# 10. CRT 素数账本与有限角色

设
\[
M=\prod_{p\in S}p,
\qquad
R_S=\prod_{p\in S}\mathbb Z/p\mathbb Z.
\]
CRT 同构
\[
\Gamma_S:\mathbb Z/M\mathbb Z\to R_S
\]
满足
\[
\boxed{
\Gamma_S([x+1])=\Gamma_S([x])+\mathbf1.}
\]
所以 \(+\mathbf1\) 是长度 \(M\) 的生成循环。布尔 NOT 正是模二加一。

又有
\[
\Gamma_S([M])=\mathbf0,\qquad
\Gamma_S([M+1])=\mathbf1.
\]
因此 \(M+1\) 不被任何 \(p\in S\) 整除；任一素因子 \(q\mid M+1\) 都满足 \(q\notin S\)。严格过程是
\[
\boxed{
\text{CRT 平移逃逸}
+
\text{因子分解}
=
\text{账本外素数见证}.}
\]

有限加法角色
\[
\chi_{\mathbf k}(\mathbf x)
=
\prod_{p\in S}\exp\!\left(\frac{2\pi i k_px_p}{p}\right)
\]
满足
\[
\boxed{
\chi_{\mathbf k}(\mathbf x+\mathbf1)
=\Omega_{\mathbf k}\chi_{\mathbf k}(\mathbf x).}
\]
完整角色族分离全部余量，且平移严格单位模。

---

# 11. 复化谐波与 Li–Cayley 界面

有限角色是圆周角色 \(z\mapsto z^n\) 在单位根上的限制。写
\[
z=e^{\beta+i\theta},
\]
则
\[
z^n=e^{n\beta}e^{in\theta},
\qquad |z^n|=e^{n\beta}.
\]
单位圆是全部正阶谐波同时单位模的唯一径向层。

镜像
\[
J(z)=\frac1{\overline z}
\]
在对数极坐标中为
\[
\boxed{J(\beta,\theta)=(-\beta,\theta).}
\]
其商坐标为
\[
\boxed{(|\beta|,e^{i\theta}).}
\]

定义
\[
C(s)=1-\frac1s.
\]
直接计算得
\[
\boxed{
|C(s)|^2-1=\frac{1-2\Re s}{|s|^2},}
\]
故
\[
\boxed{\Re s=\frac12\iff |C(s)|=1.}
\]
同时
\[
C(1-\overline s)=\overline{C(s)}^{-1}.
\]
令
\[
\beta_C(s)=\log|C(s)|,
\]
则
\[
\boxed{
\beta_C(1-\overline s)=-\beta_C(s),\qquad
\beta_C(s)=0\iff\Re s=\frac12.}
\]
RH 等价于全部非平凡零点的镜像商深度 \(|\beta_C(\rho)|\) 为零；这只是坐标等价。

定义
\[
A_n(s)=1-C(s)^n.
\]
有
\[
\boxed{
A_n(s)+A_n(1-s)=A_n(s)A_n(1-s).}
\]
在临界线上 \(1-s=\overline s\)，所以
\[
\boxed{2\Re A_n(s)=|A_n(s)|^2\ge0.}
\]

---

# 12. Li 四元轨道：局部放大与全局缺口

写
\[
C(\rho)=e^{\beta+i\theta}.
\]
反射—共轭四元轨道的第 \(n\) 阶贡献为
\[
\boxed{
L_n(\rho)
=4-4\cosh(n\beta)\cos(n\theta).}
\]
该式关于 \(\beta\) 为偶函数，所以函数方程配对已经商掉左右极性，只保留无向深度。

若 \(\beta=0\)，则
\[
L_n=8\sin^2\!\left(\frac{n\theta}{2}\right)\ge0.
\]

对任意 \(\theta\)，Dirichlet 逼近给出严格递增 \(n_k\to\infty\) 使
\[
\cos(n_k\theta)\to1.
\]
若 \(|\beta|>0\)，沿该子序列
\[
\boxed{
L_{n_k}\to-\infty,\qquad
\frac{L_{n_k}}{\cosh(n_k|\beta|)}\to-4.}
\]

给定径向阈值 \(H\ge1\)，使 \(\cosh(n|\beta|)\ge H\) 的最小非负整数阶为
\[
\boxed{
n_H(\beta)
=\left\lceil\frac{\operatorname{arcosh}(H)}{|\beta|}\right\rceil.}
\]
并且
\[
\boxed{
\lim_{n\to\infty}\frac1n\log\cosh(n\beta)=|\beta|.}
\]
所以镜像商深度就是径向放大率。

令完整 Li 系数为 \(\lambda_n\)，其余贡献为
\[
R_n=\lambda_n-L_n(\rho).
\]
若沿相位复现子序列
\[
\frac{|R_{n_k}|}{\cosh(n_k|\beta|)}\to0,
\]
则最终
\[
\boxed{\lambda_{n_k}<0.}
\]
因此局部离线轨道变成全局反例所缺的不是新探针，而是证明其余零点、正则化项或素数端不能提供同阶抵消。

此外，固定 \(n\) 的截断收敛不足以支持增长选阶。若
\[
x_n=0,\qquad
x_{n,T}=
\begin{cases}
0,&n\le T,\\
1,&n>T,
\end{cases}
\]
则每个固定 \(n\) 都收敛，但 \(n(T)=T+1\) 时误差恒为一。只有联合界
\[
\sup_{n\in N_T}|x_{n,T}-x_n|\to0
\]
才能保证增长阶 \(n(T)\in N_T\) 的对角 passage。

当前 `LiCausalTrichotomy` 的一侧 Laguerre 包与 `WeilIdentity` 的偶、光滑、紧支撑测试类尚未由内部定理识别；测试类桥接与联合余项控制是两个独立承重问题。

---

# 13. 观察者的四重审计

一个观察投影至少需要四项独立审计：

1. **自然性**
   \[
   \varepsilon^\Delta=d(Q\Delta,\Delta P).
   \]
2. **扭曲忠实性**
   \[
   \operatorname{sep}_\tau(Q).
   \]
3. **全局可命名性**：由覆盖 cocycle 与 monodromy 决定。
4. **瞬态记忆可见性**
   \[
   (|\tau^k(Y)|)_{k\ge0}.
   \]

因此
\[
\boxed{
\text{交换性}
\neq
\text{忠实性}
\neq
\text{全局可命名性}
\neq
\text{瞬态记忆保持}.}
\]

精确因子投影不会增加瞬态深度，但可能删除它；固定点谱和 zeta 则完全看不见瞬态树。

---

# 14. 统一结论与严格边界

本文得到以下统一链：

\[
\boxed{
\text{轨道商}
+
\text{群余坐标}
+
\text{角色分解}
+
\text{周期—瞬态双谱}
+
\text{完成方向}.}
\]

其具体形态为：

- 对合：
  \[
  ([x],\varepsilon)\mapsto([x],-\varepsilon);
  \]
- 群余更新：
  \[
  ([x],g)\mapsto([x],hg);
  \]
- Fourier 角色：
  \[
  P_\ell T^r=\omega^{\ell r}P_\ell;
  \]
- Fitting 分解：
  \[
  V=V_{\mathrm{nil}}\oplus V_{\mathrm{per}};
  \]
- 复化谐波：
  \[
  e^{\beta+i\theta}\mapsto e^{n\beta}e^{in\theta}.
  \]

严格边界如下：

1. 非可逆扭曲不能自动约化为循环余量；
2. 零自然性缺陷不证明观察忠实；
3. 局部余坐标不证明全局命名存在；
4. Fourier 扇区不自动成为物理超选择扇区；
5. 迹谱与秩谱共同恢复线性相似类，但不恢复完整函数图；
6. 有限动力学 zeta 不是 Riemann zeta；
7. 欧几里得逃逸先产生账本外余类，素数由因子分解提取；
8. Li 局部放大不等于完整 Li 系数已为负；
9. RH 的实质缺口仍是全局正性或等价余项控制。

---

# 15. 形式化状态

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
- 有限群余坐标、覆盖、cocycle、monodromy 与条件余信息；
- 循环谱与逃逸谱恢复；
- 周期核盲区与有限动力学 zeta；
- Fitting 分解、迹—秩双谱、Jordan 块恢复与非完整性反例；
- 因子粗粒化下瞬态深度单调性；
- Fourier 角色扇区、Hilbert 概率与去相干；
- CRT 生成平移与有限角色；
- Li–Cayley 镜像商、深度阈值、增长指数与全局余项条件。

这些结果在 proof term 落地前不得投影为 `Closed`。

---

# 参考文献

1. G. Cantor, “Über eine elementare Frage der Mannigfaltigkeitslehre,” *Jahresbericht der Deutschen Mathematiker-Vereinigung* 1 (1891), 75–78.
2. F. W. Lawvere, “Diagonal Arguments and Cartesian Closed Categories,” Lecture Notes in Mathematics 92, Springer, 1969, 134–145.
3. Euclid, *Elements*, Book IX, Proposition 20.
4. X.-J. Li, “The Positivity of a Sequence of Numbers and the Riemann Hypothesis,” *Journal of Number Theory* 65 (1997), 325–333.
5. E. Bombieri and J. C. Lagarias, “Complements to Li’s Criterion for the Riemann Hypothesis,” *Journal of Number Theory* 77 (1999), 274–287.
6. A. Weil, “Sur les ‘formules explicites’ de la théorie des nombres premiers,” *Communications du Séminaire Mathématique de l’Université de Lund*, supplément (1952), 252–265.
7. E. Artin and B. Mazur, “On Periodic Points,” *Annals of Mathematics* 81 (1965), 82–99.
8. N. Jacobson, *Basic Algebra I*, for Fitting decomposition and Jordan theory.

---

# 16. 追加：带对角代数的完全重构与分支敏感完成

本节严格采用追加式更新。前文已经证明，迹谱与秩谱共同确定线性化 \(L_\tau\) 的复 Jordan 形，却不能恢复带基函数图。本节回答三个后续问题：

1. 线性化究竟遗忘了哪一项结构；
2. 加回什么最小观察界面以后，可以完整恢复有限自映射；
3. 完整函数图能否由一族有限深度观察通过 projective completion 重构。

核心答案是：**遗失的不是更多本征值，而是标准基所定义的对角可观测代数及其分支关联。**

## 16.1 对角代数与箭头的非零角块

令
\[
V_Y=\mathbb C^Y.
\]
对函数 \(f:Y\to\mathbb C\)，定义对角乘法算子
\[
M_f e_y=f(y)e_y.
\]
全部此类算子组成交换代数
\[
\mathcal D_Y=\{M_f:f\in\mathbb C^Y\}.
\]
对每个 \(y\in Y\)，令
\[
P_y=M_{\mathbf1_{\{y\}}}.
\]
则 \((P_y)_{y\in Y}\) 是 \(\mathcal D_Y\) 的全部最小非零幂等元，并满足
\[
P_yP_z=\delta_{yz}P_y,
\qquad
\sum_yP_y=I.
\]

沿用
\[
L_\tau e_y=e_{\tau(y)}.
\]

### 定理 16.1（对角角块重构公式）

对任意 \(y,z\in Y\)，
\[
\boxed{
P_zL_\tau P_y\neq0
\iff
z=\tau(y).}
\]
更精确地，若 \(z=\tau(y)\)，则 \(P_zL_\tau P_y\) 将 \(e_y\) 送到 \(e_z\)；否则该角块为零。

### 证明

对任意基向量 \(e_w\)，
\[
P_y e_w=\delta_{yw}e_y.
\]
所以
\[
P_zL_\tau P_y e_w
=
\delta_{yw}P_z e_{\tau(y)}
=
\delta_{yw}\delta_{z,\tau(y)}e_z.
\]
该算子非零当且仅当 \(z=\tau(y)\)。\(\square\)

因此完整函数图的每条箭头都被编码为一个非零角块：
\[
\boxed{
y\longmapsto\tau(y)
\quad\Longleftrightarrow\quad
P_{\tau(y)}L_\tau P_y\neq0.}
\]

### 定理 16.2（对角代数上的协变关系）

定义函数拉回
\[
\alpha_\tau(f)=f\circ\tau.
\]
则
\[
\boxed{
M_fL_\tau
=
L_\tau M_{\alpha_\tau(f)}}
\]
对全部 \(f:Y\to\mathbb C\) 成立。

### 证明

逐基向量计算：
\[
M_fL_\tau e_y
=f(\tau(y))e_{\tau(y)},
\]
而
\[
L_\tau M_{f\circ\tau}e_y
=f(\tau(y))e_{\tau(y)}.
\]
\(\square\)

这说明离散动力学同时具有两种互补表示：

- 状态侧：\(L_\tau\) 把基状态向前送；
- 可观测侧：\(\alpha_\tau\) 把函数向后拉。

## 16.2 带对角界面的线性化是完全不变量

### 定理 16.3（对角界面保持的相似等价于函数共轭）

设
\[
\tau:Y\to Y,
\qquad
\sigma:Z\to Z
\]
为有限自映射。下列条件等价：

1. 存在双射 \(\phi:Y\to Z\)，满足
   \[
   \phi\circ\tau=\sigma\circ\phi;
   \]
2. 存在线性同构 \(U:V_Y\to V_Z\)，满足
   \[
   UL_\tau U^{-1}=L_\sigma,
   \qquad
   U\mathcal D_YU^{-1}=\mathcal D_Z.
   \]

### 证明

若有函数共轭 \(\phi\)，定义置换线性同构
\[
Ue_y=e_{\phi(y)}.
\]
则
\[
UL_\tau e_y=e_{\phi(\tau(y))}
=e_{\sigma(\phi(y))}
=L_\sigma Ue_y.
\]
同时 \(U\) 把对角最小投影 \(P_y\) 送到 \(P_{\phi(y)}\)，故保持对角代数。

反之，设 \(U\) 满足条件 2。共轭映射把 \(\mathcal D_Y\) 的最小非零幂等元双射到 \(\mathcal D_Z\) 的最小非零幂等元，所以存在唯一双射 \(\phi:Y\to Z\)，使
\[
UP_yU^{-1}=P_{\phi(y)}.
\]
由定理 16.1，
\[
z=\tau(y)
\iff
P_zL_\tau P_y\neq0.
\]
对该角块施加 \(U(-)U^{-1}\)，得到
\[
P_{\phi(z)}L_\sigma P_{\phi(y)}\neq0
\iff
\phi(z)=\sigma(\phi(y)).
\]
取 \(z=\tau(y)\)，即得
\[
\phi(\tau(y))=\sigma(\phi(y)).
\]
\(\square\)

### 推论 16.4（前文反例的精确缺失项）

前文两个八点系统的 \(L_{\tau_A}\) 与 \(L_{\tau_B}\) 可以具有相同 Jordan 形，但不存在同时把
\[
(L_{\tau_A},\mathcal D_Y)
\]
送到
\[
(L_{\tau_B},\mathcal D_Y)
\]
的对角代数保持相似。

因此“带基函数图”与“无基线性相似类”之间的差异，精确等于是否保留标准基诱导的极小对角投影及其角块关联。

## 16.3 精确商观察等价于不变可观测子代数

令 \(\phi:Y\twoheadrightarrow Z\) 为满射。定义由该观察产生的子代数
\[
\mathcal A_\phi
=
\{g\circ\phi:g:Z\to\mathbb C\}
\subseteq\mathbb C^Y.
\]
它恰由在每个 \(\phi\)-纤维上常值的可观测量组成。

### 定理 16.5（因子—不变子代数对应）

对有限自映射 \(\tau:Y\to Y\)，下列条件等价：

1. 存在唯一映射 \(\sigma:Z\to Z\)，满足
   \[
   \phi\tau=\sigma\phi;
   \]
2. 可观测子代数在拉回动力学下不变：
   \[
   \alpha_\tau(\mathcal A_\phi)
   \subseteq
   \mathcal A_\phi.
   \]

此时对全部 \(g:Z\to\mathbb C\)，
\[
\boxed{
\alpha_\tau(g\circ\phi)
=(g\circ\sigma)\circ\phi.}
\]

### 证明

若有 \(\phi\tau=\sigma\phi\)，则
\[
\alpha_\tau(g\circ\phi)
=g\circ\phi\circ\tau
=g\circ\sigma\circ\phi
\in\mathcal A_\phi.
\]

反之，假设 \(\mathcal A_\phi\) 不变。若 \(\phi(y)=\phi(y')\)，则对任意 \(g:Z\to\mathbb C\)，函数
\[
(g\circ\phi)\circ\tau
\]
属于 \(\mathcal A_\phi\)，故在 \(y,y'\) 上取值相同：
\[
g(\phi(\tau(y)))=g(\phi(\tau(y'))).
\]
有限集合上的复值函数分离点，所以
\[
\phi(\tau(y))=\phi(\tau(y')).
\]
于是可定义
\[
\sigma(\phi(y))=\phi(\tau(y)).
\]
该定义良好；\(\phi\) 满射给出唯一性。\(\square\)

这条定理把“观察者是否看到一个封闭动力学”改写成纯代数判据：
\[
\boxed{
\text{精确因子观察}
\iff
\text{观察可测代数对 }\alpha_\tau\text{ 不变}.}
\]

## 16.4 瞬态可观测过滤与 Jordan 信息损失

定义
\[
\mathcal A_k
=
\operatorname{im}(\alpha_\tau^k)
\subseteq\mathbb C^Y.
\]

### 定理 16.6（瞬态可观测过滤）

对全部 \(k\ge0\)：

1. \(\mathcal A_k\) 是含常数的交换子代数；
2. \(\mathcal A_{k+1}\subseteq\mathcal A_k\)；
3. \(h\in\mathcal A_k\) 当且仅当
   \[
   \tau^k(y)=\tau^k(y')
   \Longrightarrow
   h(y)=h(y');
   \]
4. 有维数恒等式
   \[
   \boxed{
   \dim\mathcal A_k
   =|\tau^k(Y)|
   =\operatorname{rank}(L_\tau^k).}
   \]

### 证明

\(\alpha_\tau\) 是含幺代数同态，因此其像为子代数；又
\[
\operatorname{im}\alpha^{k+1}
\subseteq
\operatorname{im}\alpha^k.
\]
若 \(h=f\circ\tau^k\)，则它显然在 \(\tau^k\) 的纤维上常值。

反之，若 \(h\) 在每个纤维上常值，可在像集 \(\tau^k(Y)\) 上定义
\[
f(z)=h(y)
\quad\text{其中 }\tau^k(y)=z,
\]
并把 \(f\) 任意延拓到整个 \(Y\)。于是 \(h=f\circ\tau^k\)。所以
\[
\mathcal A_k\cong\mathbb C^{\tau^k(Y)},
\]
维数为像集基数。最后使用定理 8.1。\(\square\)

另有
\[
\ker\alpha_\tau^k
=
\{f:f|_{\tau^k(Y)}=0\},
\qquad
\dim\ker\alpha_\tau^k
=|Y|-|\tau^k(Y)|.
\]

定义第 \(k\) 步可观测自由度损失
\[
\ell_k
=
\dim\mathcal A_{k-1}-\dim\mathcal A_k
=
|\tau^{k-1}(Y)|-|\tau^k(Y)|.
\]

### 定理 16.7（信息损失层与零 Jordan 链）

\[
\boxed{
\ell_k
=
\operatorname{rank}(L_\tau^{k-1})
-
\operatorname{rank}(L_\tau^k)}
\]
等于大小至少为 \(k\) 的零特征值 Jordan 块数。因此大小恰为 \(k\) 的零 Jordan 块数为
\[
\boxed{
\ell_k-\ell_{k+1}.}
\]
并且
\[
\boxed{
\sum_{k\ge1}\ell_k
=|Y|-|P_\tau|.}
\]

### 证明

第一式由定理 16.6 得到；Jordan 块解释由定理 8.3；最后一式由像集基数下降链 telescoping：
\[
\sum_{k=1}^{N}
(|\tau^{k-1}(Y)|-|\tau^k(Y)|)
=|Y|-|\tau^N(Y)|,
\]
取稳定的 \(N\) 即得。\(\square\)

所以零 Jordan 块不再只是线性代数正规形，而有直接的观察者含义：

> 大小至少为 \(k\) 的块数，等于第 \(k\) 次更新时新丢失的独立可观测方向数。

## 16.5 熵与相对熵的逐步遗忘恒等式

令随机变量 \(X_0\) 取值于有限集 \(Y\)，定义确定动力学轨迹
\[
X_k=\tau^k(X_0).
\]

### 定理 16.8（Shannon 遗忘 telescoping）

对每个 \(k\ge1\)，
\[
\boxed{
H(X_{k-1})-H(X_k)
=H(X_{k-1}\mid X_k).}
\]
因此对任意 \(N\)：
\[
\boxed{
H(X_0)-H(X_N)
=
\sum_{k=1}^{N}H(X_{k-1}\mid X_k).}
\]

### 证明

因为 \(X_k\) 是 \(X_{k-1}\) 的确定函数，
\[
H(X_k\mid X_{k-1})=0.
\]
所以
\[
H(X_{k-1},X_k)=H(X_{k-1}).
\]
另一方面，链式法则给出
\[
H(X_{k-1},X_k)
=H(X_k)+H(X_{k-1}\mid X_k).
\]
两式相等即得单步恒等式；求和后中间熵相消。\(\square\)

注意一般只有
\[
H(X_k)\le\log|\tau^k(Y)|,
\]
等号要求 \(X_k\) 在像集上均匀。维数损失 \(\ell_k\) 与实际 Shannon 损失因此是不同层次：前者是可用坐标容量，后者还依赖概率分布。

### 定理 16.9（KL 数据处理损失的纤维分解）

设 \(P_0,Q_0\) 为 \(Y\) 上分布，且 \(Q_0\) 满支撑。令 \(P_k,Q_k\) 为经 \(\tau^k\) 推前后的分布。则
\[
\boxed{
D(P_{k-1}\Vert Q_{k-1})
-
D(P_k\Vert Q_k)
=
\sum_{z}P_k(z)
D(P_{k-1\mid z}\Vert Q_{k-1\mid z}),}
\]
其中条件分布限制在纤维
\[
\tau^{-1}(z).
\]

### 证明

把 \(X_k=\tau(X_{k-1})\) 与 \(Y_k=\tau(Y_{k-1})\) 分别置于联合分布
\[
(x,\tau(x)).
\]
确定嵌入不改变相对熵。对两个联合分布应用有限 KL 链式法则，边缘项是 \(D(P_k\Vert Q_k)\)，条件项正是各纤维内的平均散度。\(\square\)

因此一次确定性更新造成的 KL 收缩，不是抽象损失；它恰等于被合并到同一后继状态的条件分布差异。

---

# 17. 分支敏感的完整函数图不变量

前文的迹—秩双谱只记录周期长度与瞬态链的线性块大小，却不记录不同前像分支如何附着。现在构造一个精确恢复完整有限函数图的组合不变量。

令
\[
P=P_\tau
\]
为周期点集。对任意 \(y\in Y\)，定义非周期子节点集合
\[
\operatorname{Ch}_\tau(y)
=
\{x\in Y\setminus P:\tau(x)=y\}.
\]
排除周期点的目的，是在周期根处删除来自前一个周期点的循环边，只保留真正附着的瞬态入树。

关系
\[
x\prec y
\iff
x\in\operatorname{Ch}_\tau(y)
\]
是良基的：若存在由非周期点组成的闭链，这些点便是周期点，矛盾。

## 定义 17.1（递归分支码）

令分支码取值于遗传有限多重集。沿良基关系递归定义
\[
\boxed{
\mathcal C_\tau(y)
=
\multiset{\mathcal C_\tau(x):x\in\operatorname{Ch}_\tau(y)}.}
\]
叶节点的码为空多重集；父节点的码是全部子树码的无序多重集。

### 定理 17.2（根树分类）

两个以 \(y,z\) 为根、边方向朝向根的有限瞬态入树同构，当且仅当
\[
\boxed{
\mathcal C_\tau(y)=\mathcal C_\sigma(z).}
\]

### 证明

按树高归纳。高度零时两者都无子节点，码均为空多重集，结论显然。

设结论对高度小于 \(h\) 的树成立。若两棵高度至多 \(h\) 的根树同构，同构把根的子节点双射到根的子节点，并保持各子树同构；由归纳假设，子树码逐一相等，所以根码的多重集相等。

反之，若根码多重集相等，可按每一种子树码匹配相同重数的子节点。归纳假设为每对匹配子节点给出根树同构。将这些互不相交的同构连同根映射合并，得到整棵根树同构。\(\square\)

## 定义 17.3（装饰循环 necklace）

设一个连通分量的唯一周期为
\[
p_0\mapsto p_1\mapsto\cdots
\mapsto p_{d-1}\mapsto p_0.
\]
定义其装饰循环词
\[
(\mathcal C_\tau(p_0),\ldots,
\mathcal C_\tau(p_{d-1})),
\]
并只保留其循环旋转等价类：
\[
\boxed{
\mathcal N_\tau(C)
=
[\mathcal C_\tau(p_0),\ldots,
\mathcal C_\tau(p_{d-1})]_{\mathrm{cyc}}.}
\]
整个系统的不变量 \(\mathfrak N(\tau)\) 是全部连通分量 necklace 的多重集。

### 定理 17.4（装饰 necklace 完全分类有限自映射）

对有限自映射
\[
\tau:Y\to Y,
\qquad
\sigma:Z\to Z,
\]
下列条件等价：

1. 存在双射 \(\phi:Y\to Z\)，满足
   \[
   \phi\tau=\sigma\phi;
   \]
2. 装饰循环多重集相等：
   \[
   \boxed{
   \mathfrak N(\tau)=\mathfrak N(\sigma).}
   \]

### 证明

函数共轭把每个连通分量送到连通分量，把唯一有向周期送到同长度有向周期；在选定周期起点后，共轭只能产生循环旋转。它还把每个周期点附着的瞬态入树送到同构入树。由定理 17.2，necklace 装饰保持，因此 1 推出 2。

反之，若 necklace 多重集相等，可逐分量配对。对一对相同 necklace，选择一个实现相等的循环旋转，把对应周期点逐一匹配。每对周期点的分支码相同，定理 17.2 给出附着入树的根保持同构。周期与各附着树两两只在根处相交，所以这些映射合并成整个分量的函数图同构。再对全部分量取并，得到全局共轭。\(\square\)

这一定理精确补足前文的非完整性：

- 迹谱只保留 necklace 的长度；
- 秩谱只保留全部入树的某些总体链长信息；
- 装饰 necklace 保留每棵树的完整分支类型及其沿周期的排列。

## 17.1 有限深度观察与 projective completion

定义深度 \(h\) 的截断分支码：
\[
\mathcal C_\tau^{(0)}(y)=\bullet,
\]
\[
\boxed{
\mathcal C_\tau^{(h+1)}(y)
=
\multiset{
\mathcal C_\tau^{(h)}(x):
 x\in\operatorname{Ch}_\tau(y)}.}
\]
令 \(\mathfrak N_h(\tau)\) 为用 \(\mathcal C^{(h)}\) 装饰周期所得的 necklace 多重集。

### 定理 17.5（深度截断分类）

\(\mathcal C^{(h)}(y)\) 完全分类以 \(y\) 为根、只保留前 \(h\) 层的瞬态入树。并且存在自然截断映射
\[
\partial_h:
\mathcal C^{(h+1)}\to\mathcal C^{(h)}
\]
使
\[
\partial_h(\mathfrak N_{h+1}(\tau))
=
\mathfrak N_h(\tau).
\]

### 证明

第一项对 \(h\) 归纳，证明与定理 17.2 相同，只把完整子树换成深度截断子树。第二项通过把每个子码递归截断一层定义；多重集与循环旋转均保持该操作。\(\square\)

### 定理 17.6（有限系统的分支完成定理）

若 \(|Y|=q\)，则
\[
\boxed{
\mathfrak N_q(\tau)
}
已经确定完整函数图。更一般地，族
\[
(\mathfrak N_h(\tau))_{h\ge0}
\]
的 projective limit 与完整装饰 necklace \(\mathfrak N(\tau)\) 等价。

### 证明

任意瞬态反向链中的非周期点互不相同，所以其长度不超过
\[
|Y|-|P_\tau|\le q-1.
\]
截断码从深度超过最大树高以后稳定；由于 \(\mathcal C^{(0)}\) 使用根标记，深度 \(q\) 必已越过全部瞬态树。于是 \(\mathfrak N_q\) 等于完整装饰数据，定理 17.4 给出分类。

兼容族的极限逐根恢复稳定的完整分支码，再恢复每个装饰 necklace；反向由完整码的所有有限截断显然得到。\(\square\)

因此“完成”在这里获得一个完全有限可检验的含义：

\[
\boxed{
\text{完整函数图}
=
\varprojlim_h
\text{深度 }h\text{ 的有限分支观察}.}
\]

## 17.2 前文反例的最小分支分辨深度

对两个非共轭系统，若它们的周期长度相同，定义
\[
\delta_{\mathrm{br}}(\tau,\sigma)
=
\min\{h:\mathfrak N_h(\tau)
eq
\mathfrak N_h(\sigma)\}.
\]
定理 17.6 保证有限非共轭系统的该最小值存在。

对命题 8.5 的两个八点系统：

- 深度零只看见一个固定点循环；
- 深度一只看见根有三个瞬态子节点；
- 深度二读取三个子节点各自拥有的叶子数。

两者在深度二分别出现
\[
\{3,1,0\}
\quad\text{与}\quad
\{2,2,0\},
\]
所以
\[
\boxed{
\delta_{\mathrm{br}}(\tau_A,\tau_B)=2.}
\]

这给出比“Jordan 形相同但函数图不同”更细的结论：它们需要一个能向后读取两层前像分支的观察者才会被区分。

---

# 18. 观察者的五重审计与新闭合结论

前文四重审计仍不足以判断完整函数图是否被保存。必须加入第五项：

5. **分支关联可见性**：观察者是否保留
   \[
   (\mathfrak N_h(\tau))_{h\ge0}
   \]
   或至少保留达到系统最大瞬态高度所需的有限深度。

因此更新后的严格区分为
\[
\boxed{
\text{交换性}
\neq
\text{扭曲忠实性}
\neq
\text{全局可命名性}
\neq
\text{瞬态容量保持}
\neq
\text{分支关联保持}.}
\]

迹—秩双谱可以完全通过前四项中的周期与容量审计，却仍在第五项失败。带对角代数的线性化或完整装饰 necklace 则通过第五项并恢复整个有限函数图。

## 18.1 两种完全重构的等价视图

本节得到了两个形式不同但信息等价的完整描述：

### 算子—界面描述

\[
\boxed{(\mathcal D_Y,L_\tau)}
\]
通过最小投影角块恢复每条箭头。

### 组合—完成描述

\[
\boxed{\mathfrak N(\tau)}
\]
通过周期 necklace 与递归前像树恢复每个连通分量。

二者都比 Jordan 形更强，原因相同：它们保留了基状态之间“谁指向谁”的关联，而不是只保留无基线性相似信息。

## 18.2 与对角化主线的关系

对角化读取的是
\[
E(a,a),
\]
因此天然依赖被命名的地址对角。若随后把所有最小地址投影商掉，仅保留一个无基谱对象，则对角逃逸仍可能在总计数中存在，但其具体分支来源已经无法定位。

于是得到一个新的结构结论：
\[
\boxed{
\text{定量对角统计给出全局逃逸量；
对角代数与分支完成给出逃逸发生在哪些地址关系上。}}
\]

前者是容量层，后者是关联层。完整观察者必须同时拥有二者。

## 18.3 严格边界

1. 本节只分类有限确定性自映射；随机核、量子通道与连续流需要相应的可观测代数和路径/分支对象。
2. \((\mathcal D_Y,L_\tau)\) 的完全性依赖保留整个对角代数；只保留其维数或某个低维子代数仍会丢失图信息。
3. 有限深度分支观察在达到稳定深度以前不是完整不变量；“所有已检查深度相同”不能替代统一稳定上界。
4. 这些重构定理不改变 Li–Cayley/RH 部分的全局余项缺口，也不把有限动力学 zeta 与 Riemann zeta 等同。

## 18.4 追加部分的形式化状态

定理 16.1—16.9、17.2—17.6 及第 18 节结论均给出完整纸面证明，但尚未成为 Lean 真源。适合的形式化顺序为：

1. 有限对角代数与角块重构；
2. 因子—不变子代数对应；
3. \(\operatorname{im}\alpha_\tau^k\) 的维数公式；
4. 递归多重集树码；
5. 装饰循环 necklace 分类；
6. 深度截断逆系与稳定界。

在 proof term 与冻结收据出现以前，本追加部分不得标记为 `Closed`。

---

# 19. 追加：最小确定性观察者完成、Nerode 细化与 Koopman 闭包

前文从两个方向恢复了有限确定性动力学：一方面，带对角代数的线性化 \((\mathcal D_Y,L_\tau)\) 保留每条有向边；另一方面，深度递增的分支码在 projective limit 中恢复完整函数图。本节研究一个更接近有限观察者的问题：给定一个可能过粗的读出
\[
q:Y\to O,
\]
观察者只看到
\[
q(y),\ q(\tau y),\ q(\tau^2y),\ldots,
\]
那么需要保留多少有限历史，才能得到一个封闭、确定、自然且最小的有效状态空间？

本节证明：对有限系统，全部无限未来读出所定义的完成必在有限步稳定；稳定商是包含于 \(\ker q\) 的最大 \(\tau\)-同余，也是使扭曲对角自然下降的最小确定性观察者完成。其对偶对象是由初始读出代数在 Koopman 拉回下生成的最小不变交换代数。

设 \(Y\) 为非空有限集合，\(\tau:Y\to Y\)，并将 \(O\) 替换为实际像 \(q(Y)\)，故可假设 \(q:Y\twoheadrightarrow O\)。

## 19.1 有限未来词与分辨关系

对 \(m\ge0\)，定义长度 \(m+1\) 的未来读出词
\[
W_m(y)
=
\bigl(q(y),q(\tau y),\ldots,q(\tau^m y)\bigr)
\in O^{m+1}.
\]
定义等价关系
\[
y\equiv_m y'
\iff
W_m(y)=W_m(y').
\]
记商类数为
\[
c_m=|Y/{\equiv_m}|=|W_m(Y)|.
\]

### 定理 19.1（有限观察细化与稳定界）

关系族 \((\equiv_m)_{m\ge0}\) 满足：

1. \(\equiv_{m+1}\subseteq\equiv_m\)；
2. \(c_{m+1}\ge c_m\)；
3. 存在最小整数 \(m_*\ge0\)，使
   \[
   \equiv_{m_*}=\equiv_{m_*+1};
   \]
4. 该稳定指标满足
   \[
   \boxed{
   m_*
   \le
   c_{m_*}-c_0
   \le
   |Y|-|O|.}
   \]

### 证明

若两个点的长度 \(m+2\) 读出词相同，则其前 \(m+1\) 项相同，所以第一项成立。关系细化只能增加商类数，得到第二项。

商类数是介于 \(|O|=c_0\) 与 \(|Y|\) 之间的非降整数序列，故最终稳定。取第一个满足相邻两项相等的指标为 \(m_*\)。在此之前每一步都严格增加至少一个商类，因此
\[
c_{m_*}\ge c_0+m_*.
\]
整理即得所述界。\(\square\)

### 定理 19.2（一次稳定即永久稳定）

若
\[
\equiv_m=\equiv_{m+1},
\]
则 \(\equiv_m\) 对 \(\tau\) 稳定：
\[
y\equiv_m y'
\Longrightarrow
\tau(y)\equiv_m\tau(y').
\]
并且
\[
\boxed{
\equiv_{m+r}=\equiv_m
\quad\text{对全部 }r\ge0.}
\]

### 证明

设 \(y\equiv_m y'\)。由于 \(\equiv_m=\equiv_{m+1}\)，还有
\[
q(\tau^{m+1}y)=q(\tau^{m+1}y').
\]
而原来的 \(m\)-等价已经给出
\[
q(\tau^ky)=q(\tau^ky')
\quad(0\le k\le m).
\]
因此
\[
q(\tau^k(\tau y))
=
q(\tau^k(\tau y'))
\quad(0\le k\le m),
\]
即 \(\tau y\equiv_m\tau y'\)。反复应用该稳定性，所有后续读出也相同，故不会再发生进一步细化。\(\square\)

## 19.2 最大不可分同余与 greatest-fixed-point 公式

定义无限未来不可分关系
\[
y\equiv_\infty y'
\iff
q(\tau^ky)=q(\tau^ky')
\quad\text{对全部 }k\ge0.
\]

在 \(Y\times Y\) 的关系格上定义单调算子
\[
\Phi(R)
=
\ker q
\cap
(\tau\times\tau)^{-1}(R).
\]
这里
\[
(y,y')\in(\tau\times\tau)^{-1}(R)
\iff
(\tau y,\tau y')\in R.
\]

### 定理 19.3（有限 Kleene 下降与最大同余）

有递推式
\[
\boxed{
\equiv_{m+1}=\Phi(\equiv_m),
\qquad
\equiv_0=\ker q.}
\]
并且
\[
\boxed{
\equiv_\infty
=
\bigcap_{m\ge0}\equiv_m
=
\equiv_{m_*}.}
\]
关系 \(\equiv_\infty\) 是包含于 \(\ker q\) 的最大 \(\tau\)-同余，即：

1. \(\equiv_\infty\subseteq\ker q\)；
2. \(y\equiv_\infty y'\Rightarrow\tau y\equiv_\infty\tau y'\)；
3. 若等价关系 \(R\subseteq\ker q\) 且
   \[
   yRy'\Longrightarrow\tau y\,R\,\tau y',
   \]
   则
   \[
   R\subseteq\equiv_\infty.
   \]

等价地，
\[
\boxed{
\equiv_\infty=\nu R.\,\Phi(R),}
\]
即它是 \(\Phi\) 的最大不动点。

### 证明

\(y\equiv_{m+1}y'\) 当且仅当当前读出相同，并且从下一状态开始的前 \(m+1\) 个读出相同；这正是
\[
(y,y')\in\ker q
\quad\text{且}\quad
(\tau y,\tau y')\in\equiv_m.
\]
故递推式成立。

无限未来相同显然等价于属于全部有限关系。由定理 19.2，有限关系在 \(m_*\) 后稳定，所以交等于 \(\equiv_{m_*}\)。前两项由定义直接得到。

若 \(R\) 是包含于 \(\ker q\) 的 \(\tau\)-同余，则 \(yRy'\) 蕴含
\[
\tau^ky\,R\,\tau^ky'
\]
对全部 \(k\) 成立；又 \(R\subseteq\ker q\)，所以全部未来读出相同。故 \(R\subseteq\equiv_\infty\)。这同时证明 greatest-fixed-point 表述。\(\square\)

该定理把“从无限未来完成观察者”化为一个有限稳定的不动点计算：在有限系统中，无穷交并不要求无限存储，而在最多 \(|Y|-|O|\) 次严格细化后闭合。

## 19.3 最小确定性观察者完成

定义完成状态空间
\[
Z_q=Y/{\equiv_\infty},
\qquad
\pi_q:Y\twoheadrightarrow Z_q.
\]
由定理 19.3，\(\tau\) 在商上良定义：
\[
\overline\tau([y])=[\tau(y)].
\]
当前读出也下降为
\[
\overline q([y])=q(y).
\]
于是
\[
\boxed{
\pi_q\tau=\overline\tau\pi_q,
\qquad
q=\overline q\pi_q.}
\]

### 定理 19.4（最小确定性完成的泛性质）

设另一个有限确定性实现由满射
\[
r:Y\twoheadrightarrow W
\]
给出，并存在
\[
\sigma:W\to W,
\qquad
o:W\to O
\]
使
\[
r\tau=\sigma r,
\qquad
q=or.
\]
则存在唯一满射
\[
h:W\twoheadrightarrow Z_q
\]
满足
\[
\boxed{
\pi_q=hr,
\qquad
h\sigma=\overline\tau h,
\qquad
\overline qh=o.}
\]

因此 \(Z_q\) 在所有精确、确定且保留原读出的完成中状态数最小：
\[
\boxed{|Z_q|\le|W|.}
\]

### 证明

若 \(r(y)=r(y')\)，则由动力学交换性
\[
r(\tau^ky)=r(\tau^ky')
\]
对全部 \(k\) 成立；再由 \(q=or\)，全部未来读出相同。因此
\[
\ker r\subseteq\equiv_\infty=\ker\pi_q.
\]
故 \(\pi_q\) 在每个 \(r\)-纤维上常值，唯一因子化为 \(h\circ r\)。\(r\) 与 \(\pi_q\) 均满射，故 \(h\) 满射。其余两个交换式在 \(r(Y)=W\) 上逐点验证即可。\(\square\)

这里的方向值得强调：任意更精细的隐藏状态实现 \(W\) 都满射到 \(Z_q\)。所以 \(Z_q\) 不是恢复原始微观状态 \(Y\) 的最大模型，而是保留全部未来可预测读出所需的**最小充分状态**。

## 19.4 无限 itinerary 的 projective completion

定义无限读出轨迹
\[
\mathcal I_q(y)
=
\bigl(q(\tau^ky)\bigr)_{k\ge0}
\in O^{\mathbb N}.
\]
令左移算子为
\[
S((o_0,o_1,o_2,\ldots))
=(o_1,o_2,o_3,\ldots).
\]
则
\[
\boxed{
\mathcal I_q\tau=S\mathcal I_q.}
\]

令
\[
X_m=W_m(Y)
\subseteq O^{m+1}
\]
并以删除最后一项的映射
\[
\partial_m:X_{m+1}\to X_m
\]
组成逆系。

### 定理 19.5（itinerary 完成定理）

有自然动力同构
\[
\boxed{
Z_q
\cong
\mathcal I_q(Y)
\cong
\varprojlim_m X_m.}
\]
并且在稳定深度 \(m_*\) 上，坐标投影已经是双射：
\[
\boxed{
\mathcal I_q(Y)
\xrightarrow{\ \cong\ }
X_{m_*}.}
\]
因此有限系统的无限未来完成在有限层即终止。

### 证明

\(\mathcal I_q\) 的核正是 \(\equiv_\infty\)，所以它诱导 \(Z_q\) 到其像的双射，并与 \(\overline\tau\) 和移位相容。

任意实际无限轨迹显然给出兼容的有限前缀族。反之，设 \((x_m)_m\) 是兼容前缀族。令
\[
F_m=\{y\in Y:W_m(y)=x_m\}.
\]
每个 \(F_m\) 非空，且兼容性给出下降链
\[
F_0\supseteq F_1\supseteq F_2\supseteq\cdots.
\]
有限集合中的非空下降链交非空；取 \(y\) 属于其交，则全部前缀均来自 \(\mathcal I_q(y)\)。故逆极限恰为实际轨迹像。

在 \(m_*\) 处，\(W_{m_*}\) 的核已经等于 \(\equiv_\infty\)，故其像与 \(Z_q\) 双射。\(\square\)

定义未来分辨时间
\[
d_q(y,y')
=
\min\{k\ge0:q(\tau^ky)\neq q(\tau^ky')\}
\]
用于非等价点对。则
\[
\boxed{
m_*
=
\max_{y\not\equiv_\infty y'}d_q(y,y')}
\]
（若没有可分辨点对，约定右侧为零）。所以 \(m_*\) 是所有未来可分辨状态对中的最晚首次分离时刻。

## 19.5 对角自然性的最小修复

取任意地址集 \(A\)。对 \(Y\)-值评价表与输出逐点定义
\[
P_q(E)(a,b)=\pi_q(E(a,b)),
\qquad
Q_q(u)(a)=\pi_q(u(a)).
\]

### 定理 19.6（完成商上的对角自然性）

对所有评价表 \(E:A\times A\to Y\)，
\[
\boxed{
Q_q\Delta_\tau(E)
=
\Delta_{\overline\tau}P_q(E).}
\]

### 证明

逐坐标有
\[
\begin{aligned}
Q_q\Delta_\tau(E)(a)
&=\pi_q(\tau(E(a,a)))\\
&=\overline\tau(\pi_q(E(a,a)))\\
&=\Delta_{\overline\tau}P_q(E)(a).
\end{aligned}
\]
\(\square\)

### 定理 19.7（最小自然化）

设满射 \(r:Y\twoheadrightarrow W\) 保留原读出，即 \(q=or\)。若存在 \(\sigma:W\to W\)，使对任意非空地址集和任意评价表都有
\[
Q_r\Delta_\tau
=
\Delta_\sigma P_r,
\]
则 \(r\tau=\sigma r\)，并存在唯一满射 \(h:W\twoheadrightarrow Z_q\) 使 \(\pi_q=hr\)。

### 证明

取单点地址集 \(A=\{*\}\)，并令 \(E(*,*)=y\)。自然性立即给出
\[
r(\tau(y))=\sigma(r(y))
\]
对全部 \(y\) 成立。随后应用定理 19.4。\(\square\)

所以 \(Z_q\) 不仅是最小预测状态，也是使原扭曲对角通过该观察界面严格自然下降的最小状态完成。

## 19.6 Koopman 可观测代数的最小闭包

令
\[
\mathcal B_0
=
q^*(\mathbb C^O)
=
\{f\circ q:f:O\to\mathbb C\}
\subseteq\mathbb C^Y
\]
为当前读出可测代数。令 Koopman 拉回为
\[
K_\tau f=f\circ\tau.
\]
定义
\[
\mathcal B_m
=
\operatorname{alg}^*
\bigl(
\mathcal B_0,
K_\tau\mathcal B_0,
\ldots,
K_\tau^m\mathcal B_0
\bigr),
\]
其中 \(\operatorname{alg}^*\) 表示生成的含幺、共轭封闭交换代数。

### 定理 19.8（有限词代数定理）

\(\mathcal B_m\) 恰由在 \(W_m\)-纤维上常值的复函数组成。因此
\[
\boxed{
\mathcal B_m
\cong
\mathbb C^{X_m},
\qquad
\dim\mathcal B_m=c_m.}
\]

### 证明

每个生成元只依赖某个坐标 \(q(\tau^ky)\)，所以 \(\mathcal B_m\) 中的函数都在相同未来词的纤维上常值。

反之，对任意实际词
\[
w=(w_0,\ldots,w_m)\in X_m,
\]
其纤维指示函数可写为
\[
\mathbf1_{W_m^{-1}(w)}(y)
=
\prod_{k=0}^{m}
\mathbf1_{\{w_k\}}(q(\tau^ky)).
\]
右侧属于 \(\mathcal B_m\)。这些互不相交的纤维指示函数张成全部纤维常值函数。\(\square\)

### 定理 19.9（最小 Koopman 不变闭包）

链
\[
\mathcal B_0
\subseteq
\mathcal B_1
\subseteq\cdots
\]
在 \(m_*\) 处稳定，并且
\[
\boxed{
K_\tau(\mathcal B_{m_*})
\subseteq
\mathcal B_{m_*}.}
\]
此外
\[
\boxed{
\mathcal B_{m_*}
=
\bigcap
\{\mathcal C:\mathcal B_0\subseteq\mathcal C,
\ K_\tau\mathcal C\subseteq\mathcal C,
\ \mathcal C\text{ 为含幺 }*\text{-子代数}\}.}
\]
并有自然同构
\[
\boxed{
\mathcal B_{m_*}
\cong
\mathbb C^{Z_q}.}
\]

### 证明

由定理 19.8，代数维数为 \(c_m\)，所以与关系稳定同步稳定。又
\[
K_\tau(\mathcal B_m)
\subseteq
\mathcal B_{m+1};
\]
在 \(m_*\) 处两代数相等，故得到不变性。

任何包含 \(\mathcal B_0\) 且对 \(K_\tau\) 不变的子代数都包含全部 \(K_\tau^k\mathcal B_0\)，从而包含每个 \(\mathcal B_m\)，特别包含稳定代数。最后，\(W_{m_*}\) 与 \(Z_q\) 具有相同纤维，故其函数代数同构。\(\square\)

因此状态侧与可观测侧给出同一个完成：
\[
\boxed{
Z_q
\quad\longleftrightarrow\quad
\mathbb C^{Z_q}=\mathcal B_{m_*}.}
\]
前者是最小充分状态空间，后者是原始读出代数的最小 Koopman 不变闭包。

## 19.7 完成深度、熵成本与最小记忆

令 \(Y_0\) 是在 \(Y\) 上取值的随机变量，定义
\[
O_k=q(\tau^kY_0),
\qquad
\mathbf O_m=(O_0,\ldots,O_m).
\]

### 定理 19.10（完成信息的链式分解）

对全部 \(m\ge0\)，
\[
\boxed{
H(\mathbf O_m)
=
H(O_0)
+
\sum_{k=1}^{m}
H(O_k\mid O_0,\ldots,O_{k-1}).}
\]
在稳定深度，\(\mathbf O_{m_*}\) 与完成状态 \(\pi_q(Y_0)\) 双射对应，所以
\[
\boxed{
H(\pi_q(Y_0)\mid O_0)
=
\sum_{k=1}^{m_*}
H(O_k\mid O_0,\ldots,O_{k-1}).}
\]

### 证明

第一式是 Shannon 链式法则。由于 \(W_{m_*}\) 与 \(\pi_q\) 具有相同纤维，它们的随机变量通过像集上的双射互相确定，故熵相同。又 \(O_0\) 是 \(\mathbf O_{m_*}\) 的函数，因此
\[
H(\mathbf O_{m_*})-H(O_0)
=H(\mathbf O_{m_*}\mid O_0)
=H(\pi_q(Y_0)\mid O_0).
\]
代入链式法则。\(\square\)

若 \(Y_0\) 满支撑，则还有一个纯信息论的稳定判据。

### 定理 19.11（条件熵零判据）

假设 \(Y_0\) 在每个 \(y\in Y\) 上概率为正。则
\[
\boxed{
m_*
=
\min\{m\ge0:
H(O_{m+1}\mid O_0,\ldots,O_m)=0\}.}
\]

### 证明

若关系在 \(m\) 处稳定，则下一读出是当前词 \(W_m\) 的确定函数，所以条件熵为零。

反之，条件熵为零意味着在每个具有正概率的词纤维上，下一读出几乎处处唯一。满支撑使每个实际状态均具有正概率，因此同一 \(W_m\)-纤维中的任意两个状态都有相同下一读出，即 \(\equiv_m=\equiv_{m+1}\)。取最小指标即得。\(\square\)

### 推论 19.12（最小完成的概率成本）

对任意其他精确确定性完成 \(r:Y\to W\)，以同一随机初态推前，有
\[
\boxed{
H(r(Y_0)\mid O_0)
\ge
H(\pi_q(Y_0)\mid O_0).}
\]

### 证明

定理 19.4 给出 \(\pi_q(Y_0)=h(r(Y_0))\)。在给定 \(O_0\) 后应用确定性数据处理或条件熵单调性。\(\square\)

因此
\[
\boxed{
C_{\mathrm{det}}(q,\tau;Y_0)
:=H(\pi_q(Y_0)\mid q(Y_0))}
\]
是给定分布下，把当前读出补成精确确定性状态所需的最小平均附加信息。最坏情形的附加存储可由
\[
\boxed{
\left\lceil
\log_2
\max_{o\in O}
|\overline q^{-1}(o)|
\right\rceil}
\]
比特实现；它依赖观察映射与动力学，不是普适常数，也不等同于光速。

## 19.8 无记忆随机闭包的严格边界

有人可能试图不扩充状态，只在粗读出集合 \(O\) 上引入随机 Markov 核
\[
K(o,o')
\]
来模拟隐藏确定动力学。若要求该核对所有初始分布都有效，则随机化并不能绕过同余障碍。

### 定理 19.13（分布无关 Markov 闭包判据）

下列条件等价：

1. 存在 Markov 核 \(K\) 于 \(O\)，使对每个 \(Y\) 上初始分布 \(\mu\)，
   \[
   q_*(\tau_*\mu)
   =K_*(q_*\mu);
   \]
2. \(q\) 本身已经是确定性因子，即存在 \(\sigma:O\to O\) 满足
   \[
   q\tau=\sigma q;
   \]
3. \(m_*=0\)。

此时唯一可取的有效核在每个可达读出上是确定性的：
\[
K(o,-)=\delta_{\sigma(o)}.
\]

### 证明

若 2 成立，取确定性核即可，故 2 推出 1。若 1 成立，取点质量 \(\mu=\delta_y\)，得到
\[
K(q(y),-)=\delta_{q(\tau y)}.
\]
若 \(q(y)=q(y')\)，同一个核行必须同时等于
\[
\delta_{q(\tau y)}
\quad\text{和}\quad
\delta_{q(\tau y')},
\]
故两个下一读出相同。于是 \(q\tau\) 在 \(q\)-纤维上常值，定义 \(\sigma(q(y))=q(\tau y)\) 即得 2。条件 2 正是 \(\ker q\) 已经为 \(\tau\)-同余，也就是第一次细化不再改变关系，故与 3 等价。\(\square\)

所以当 \(m_*>0\) 时，一个只看当前粗读出的、分布无关且无记忆的随机模型不可能精确复现全部初始条件。此时只能：

- 使用依赖特定分布或时间的条件核；
- 接受近似误差；
- 或把状态扩充到最小完成 \(Z_q\)。

---

# 20. 追加：观察者的六重审计与有限完成原则

前文的五重审计还没有单独检查“当前观察状态是否足以封闭未来预测”。本节加入第六项：

6. **预测闭合性**：当前观察是否本身构成一个分布无关的确定或 Markov 状态；若否，最小完成深度 \(m_*\)、完成状态 \(Z_q\) 与完成信息成本是多少。

于是有限确定性观察者至少需要区分：
\[
\boxed{
\begin{aligned}
&\text{对角自然性},\\
&\text{扭曲忠实性},\\
&\text{全局单值命名},\\
&\text{瞬态容量可见性},\\
&\text{分支关联可见性},\\
&\text{预测闭合性}.
\end{aligned}}
\]

六者仍然互不等同。特别地：

- 一个观察可以与对角算子自然交换，却把扭曲商掉；
- 一个观察可以保留周期与瞬态容量，却丢失分支关联；
- 一个观察可以在每一时刻给出合法读数，却不构成无记忆状态；
- 无限未来 itinerary 可以区分完成状态，但在有限系统中该完成必于有限深度 \(m_*\) 稳定；
- 完成状态只恢复所有未来读出可区分的信息，不保证恢复微观状态 \(Y\)。

本节得到状态侧、代数侧、信息侧和对角侧的四重等价接口：
\[
\boxed{
\begin{aligned}
Z_q
&=Y/{\equiv_\infty}\\
&\cong\mathcal I_q(Y)\\
&\cong\varprojlim_m W_m(Y),
\end{aligned}}
\]
\[
\boxed{
\mathbb C^{Z_q}
=\text{包含 }q^*\mathbb C^O
\text{ 的最小 Koopman 不变 }*\text{-代数},}
\]
以及
\[
\boxed{
Q_q\Delta_\tau
=\Delta_{\overline\tau}P_q.}
\]

因此，对有限观察者而言，“完成”并非必须预设一个实际可访问的无限对象。它可以严格定义为有限读出关系的最大稳定不动点；所谓无限未来只提供该不动点的外在表示，而有限性保证它最终由一个有限词长度完全决定。

## 20.1 严格边界

1. 本节使用的是未来读出等价，它是数学预测分类，不表示物理观察者可以从现在直接读取未来。
2. 有限步稳定依赖 \(Y\) 有限；无限状态、连续系统或无限精度读出不保证存在有限 \(m_*\)。
3. \(Z_q\) 是相对于指定 \(q\) 的最小预测完成，不是观察者无关的绝对本体空间。
4. 条件熵成本依赖初始分布；最坏状态数与平均信息成本不能混为一谈。
5. 分布特定的随机粗粒化可能暂时闭合，但定理 19.13 排除的是对全部初始分布统一有效的无记忆核。
6. 本节没有推出量子测量的唯一模型、光速信息率、Riemann 假设或任何 Weil 正性。

## 20.2 形式化状态

定理 19.1—19.13 及第 20 节结论均给出完整纸面证明，尚未成为 Lean 真源。推荐形式化顺序为：

1. 有限未来词关系及其稳定界；
2. greatest-fixed-point 与最大同余定理；
3. 最小完成商的泛性质；
4. 有限词逆系与 itinerary 极限；
5. Koopman 生成代数及维数公式；
6. 完成条件熵恒等式；
7. 分布无关 Markov 闭包判据；
8. 对角自然性的最小修复。

在 proof term、依赖闭包与冻结收据出现以前，本追加部分不得标记为 `Closed`。

## 20.3 append-only 排版勘误说明

为严格保留提交 `1f8b203d4a4edef41d1d702ff94a0cc25ef38aca` 以前的正文原字节，第 17.2 节历史文本中的关系符被保留为断行形式。其数学意图应读作
\[
\boxed{
\delta_{\mathrm{br}}(\tau,\sigma)
=
\min\{h:\mathfrak N_h(\tau)\neq
\mathfrak N_h(\sigma)\}.}
\]
本说明只在文件末尾追加，不回写或覆盖旧段落。

---

# 21. 追加：有限精度自回归模型的闭环动力学、预测稳定与退化边界

本节把第 19 节的有限观察完成应用于没有持续外界输入的自回归语言模型。核心结论需要先作一项严格修正：

\[
\boxed{
\text{参数个数有限}
\not\Longrightarrow
\text{推理过程自动成为有限状态系统}.}
\]

参数只是在推理期间固定转移律的一部分；真正决定有限性的，是**所有具有后续因果作用的运行时状态**是否取值于有限集合。反之，在数字硬件的有限精度、有限上下文、有限缓存、有限外部记忆与确定解码假设下，闭环推理确实可以表示成一个极其巨大但有限的自治系统。此时第 19 节的完成定理适用，但“一次稳定即永久稳定”描述的是**未来输出等价关系不再细化**，不是模型状态停止、输出变成常数、概率收敛或语义质量必然下降。

本节进一步证明：有限闭环确定系统必然最终进入周期核，且相对于完整初态没有新的 Shannon 熵注入；然而有限性本身并不蕴含质量退化。严格的永久退化判据取决于可达周期核上的质量函数，而不是仅取决于状态集合有限。对自回归模型而言，更直接的结构性风险来自非单射更新：上下文截断、隐藏状态覆盖以及离散解码可以把不同历史合并为同一后继状态；一旦完整因果状态真正合并，确定系统便永远不能自行重新区分这些历史。

## 21.1 参数空间、因果状态与输出档案的区分

固定模型参数记为

\[
\theta\in\Theta.
\]

在一次不更新权重的推理过程中，\(\theta\) 选择一个转移律，而通常不随时间变化。令运行时具有后续因果作用的分量包括：

\[
C=\text{有效上下文状态},
\]

\[
K=\text{KV 缓存或其他隐藏缓存状态},
\]

\[
R=\text{解码器或伪随机数发生器状态},
\]

\[
M=\text{可被模型重新读取的外部记忆状态},
\]

\[
S=\text{位置、调度器及其他控制状态}.
\]

定义完整因果状态空间

\[
\boxed{
Y=C\times K\times R\times M\times S.}
\]

输出字母表或读出集合记为 \(O\)。若在固定 \(\theta\) 下，每一步完全由当前因果状态决定，则存在

\[
F_\theta:Y\to Y,
\qquad
q_\theta:Y\to O.
\]

从初态 \(y_0\) 出发的输出为

\[
o_t=q_\theta(F_\theta^t(y_0)).
\]

这里必须区分不断增长的输出档案与因果状态。完整 transcript

\[
(o_0,o_1,\ldots,o_t)
\]

可以持续增长；但若模型只能重新读取其最后 \(L\) 个 token，较早档案不再属于后续转移所依赖的因果状态。相反，若模型能够无界地读取全部历史，或者拥有无界增长且可重新访问的记忆，则即使词表有限，因果状态空间也一般不再有限。

### 定理 21.1（有限精度运行时归约）

假设：

1. \(C,K,R,M,S,O\) 均为有限集合；
2. 参数 \(\theta\) 在推理过程中固定；
3. 更新与读出在给定完整状态后是确定的；
4. 没有时钟、网络、检索器、传感器、人工消息或新随机比特等未计入 \(Y\) 的输入。

则该推理过程是有限确定性观察系统

\[
\boxed{
(Y,F_\theta,q_\theta).}
\]

特别地，

\[
|Y|
=
|C|\,|K|\,|R|\,|M|\,|S|
<\infty.
\]

若模型有 \(N\) 个参数槽，每个参数用至多 \(b\) 比特表示，则全部可能参数配置的数量满足

\[
|\Theta|\le 2^{bN}.
\]

但对一个固定模型，动态状态数仍是 \(|Y|\)，而不是 \(2^{bN}|Y|\)。只有在在线学习、持续微调或权重自修改时，\(\theta_t\) 才必须连同优化器状态一起并入动态状态；此时扩展状态数才包含参数配置因子。

### 证明

有限集合的有限直积仍有限。固定 \(\theta\) 后，数字实现的下一步计算给出从完整运行时配置到下一配置的单值映射 \(F_\theta\)，输出端给出 \(q_\theta\)。其余结论由有限精度参数编码的计数直接得到。 \(\square\)

因此，“大语言模型的模型参数可以构成有限系统”更准确的表述是：

\[
\boxed{
\text{有限精度参数}
+
\text{有限因果运行时状态}
+
\text{闭合确定更新}
\Longrightarrow
\text{有限自治系统}.}
\]

仅有“参数数量有限”并不足够。数学上，有限个精确实参数仍可取连续无穷多值；工程上，固定参数又主要属于转移律，而非每一步变化的状态。

## 21.2 有限上下文贪心解码的正规形

令有限词表为 \(\Sigma\)，固定有效上下文长度为 \(L\ge1\)。在最小化模型中，把上下文状态写成

\[
c=(x_1,\ldots,x_L)\in\Sigma^L.
\]

固定模型与确定解码共同诱导下一 token 函数

\[
g_\theta:\Sigma^L\to\Sigma.
\]

闭环更新为

\[
\boxed{
F_\theta(x_1,\ldots,x_L)
=
(x_2,\ldots,x_L,g_\theta(x_1,\ldots,x_L)).}
\]

若读出取本步生成 token，则

\[
q_\theta(c)=g_\theta(c).
\]

在上下文尚未填满时，可取

\[
Y_{\le L}
=
\bigsqcup_{\ell=0}^{L}\Sigma^\ell,
\]

故

\[
|Y_{\le L}|
=
\sum_{\ell=0}^{L}|\Sigma|^\ell.
\]

填满以后，动力学限制在 \(\Sigma^L\)，状态数为

\[
\boxed{|Y|=|\Sigma|^L.}
\]

真实实现还需要把有限精度 KV cache、位置编码状态、采样器状态及可读记忆乘入该状态空间；上述正规形只描述“下一步完全由最后 \(L\) 个 token 决定”的最小情形。

### 定理 21.2（闭环有限生成的最终周期性）

设 \(Y\) 有限，\(F:Y\to Y\)。对任意初态 \(y_0\)，存在整数

\[
\mu\ge0,
\qquad
\lambda\ge1,
\qquad
\mu+\lambda\le |Y|,
\]

使

\[
\boxed{
F^{t+\lambda}(y_0)=F^t(y_0)
\quad
\text{对全部 }t\ge\mu.}
\]

从而任意确定读出 \(q:Y\to O\) 的输出序列也最终周期：

\[
\boxed{
q(F^{t+\lambda}(y_0))
=
q(F^t(y_0))
\quad
(t\ge\mu).}
\]

### 证明

序列

\[
y_0,F(y_0),\ldots,F^{|Y|}(y_0)
\]

含有 \(|Y|+1\) 个元素，故至少两个相等。取第一次重复

\[
F^\mu(y_0)=F^{\mu+\lambda}(y_0).
\]

对两边继续应用 \(F\)，便得到全部 \(t\ge\mu\) 的周期关系。第一次重复以前的状态及一个周期内的状态互异，因此 \(\mu+\lambda\le|Y|\)。对等式施加 \(q\) 即得输出周期性。 \(\square\)

该定理只保证在无限时间极限中进入某个周期。它没有给出周期很短，也没有给出周期上的文本质量很低。对于实际尺寸的数字模型，\(|Y|\) 可以大到使鸽巢上界没有任何工程尺度上的直接解释。

## 21.3 “一次稳定即永久稳定”的准确含义

沿用第 19 节的定义。对 \(m\ge0\)，令

\[
y\equiv_m y'
\iff
q(F^ky)=q(F^ky')
\quad
(0\le k\le m).
\]

也就是说，\(\equiv_m\) 把在未来前 \(m+1\) 个读出上完全相同的状态放入同一等价类。随着 \(m\) 增大，观察者允许检查更长未来，因此关系只能细化：

\[
\equiv_0
\supseteq
\equiv_1
\supseteq
\equiv_2
\supseteq\cdots.
\]

### 定理 21.3（预测分区的一步稳定）

若某个 \(m\) 满足

\[
\boxed{
\equiv_m=\equiv_{m+1},}
\]

则：

\[
y\equiv_m y'
\Longrightarrow
F(y)\equiv_m F(y'),
\]

并且

\[
\boxed{
\equiv_{m+r}=\equiv_m
\quad
\text{对全部 }r\ge0.}
\]

### 证明

设 \(y\equiv_m y'\)。相邻两层相等意味着它们不仅在时刻 \(0,\ldots,m\) 的读出相同，而且时刻 \(m+1\) 的读出也相同。因此

\[
q(F^{k+1}y)=q(F^{k+1}y')
\quad
(0\le k\le m),
\]

即

\[
F(y)\equiv_m F(y').
\]

所以 \(\equiv_m\) 已经成为 \(F\)-同余。反复应用该同余，任意更晚的读出都不能再把当前等价类拆开，于是全部后续关系相等。 \(\square\)

这就是“一次稳定即永久稳定”。它说的是：

> 若把所有状态按长度 \(m+1\) 的未来输出词分类，与按长度 \(m+2\) 分类得到完全相同的全局分区，那么再观察任意长未来也不会产生新的状态类别。

它**不**表示下列任一命题：

\[
F^m(y)=F^{m+1}(y);
\]

\[
q(F^m(y))=q(F^{m+1}(y));
\]

\[
F^m(Y)=F^{m+1}(Y);
\]

\[
\text{模型输出从此成为常数};
\]

\[
\text{模型概率分布已经收敛};
\]

\[
\text{模型语义质量已经停止变化}.
\]

它还是一个关于**全部状态对**的全局陈述，而不是仅观察一条生成轨迹若干步后“暂时没有发现差异”。

### 推论 21.4（稳定深度的 LLM 解释）

若 \(O=q(Y)\)，最小稳定深度 \(m_*\) 满足

\[
\boxed{
m_*
\le
|Y/{\equiv_\infty}|-|O|
\le
|Y|-|O|.}
\]

对 token 读出，\(|O|\) 至多为词表大小；\(|Y|\) 则是完整因果运行时状态数。在最小 \(L\)-token 模型中，

\[
m_*
\le
|\Sigma|^L-|\Sigma|.
\]

该界限制的是“需要多少个未来读出坐标才能完成预测状态分类”，不是：

- 生成多少 token 后模型开始退化；
- 参数数量与词表大小的差；
- 到达周期所需的时间；
- 语义记忆的有效长度。

## 21.4 三种“稳定”必须分开

有限闭环系统中至少存在三种不同现象。

第一种是**预测分区稳定**：

\[
\equiv_m=\equiv_{m+1}.
\]

它意味着长度 \(m+1\) 的未来读出已经包含全部可预测区分。

第二种是**像链稳定**。定义

\[
Y_t=F^t(Y).
\]

由于 \(F(Y)\subseteq Y\)，有下降链

\[
Y_0\supseteq Y_1\supseteq Y_2\supseteq\cdots.
\]

若

\[
Y_N=Y_{N+1},
\]

则

\[
Y_{N+r}=Y_N
\quad
(r\ge0).
\]

稳定像等于周期点集合

\[
P_F=\{y:\exists n\ge1,\ F^n(y)=y\}.
\]

第三种是**单轨道复现**：

\[
F^{\mu+\lambda}(y_0)=F^\mu(y_0).
\]

它说明一条给定轨迹进入长度 \(\lambda\) 的周期。

三者的指标 \(m_*,N,\mu,\lambda\) 一般没有相等关系。尤其：

- \(m_*=0\) 时，隐藏状态仍可沿很长周期运动；
- 像链已经稳定时，状态仍可在周期核上不断变化；
- 一条轨迹进入周期，不表示其他初态已经进入同一周期；
- 预测分区稳定不表示输出固定，只表示更长未来不再提供新的**状态分类能力**。

## 21.5 真正不可逆的是状态合并

预测等价允许两个不同状态永远产生相同输出，但完整状态仍可能不同。更强的现象是状态本身合并。

### 定理 21.5（确定系统的合并不可逆性）

若存在 \(t\ge0\) 使

\[
F^t(y)=F^t(y'),
\]

则对全部 \(r\ge0\)，

\[
\boxed{
F^{t+r}(y)=F^{t+r}(y'),}
\]

并且全部后续输出相同：

\[
q(F^{t+r}(y))
=
q(F^{t+r}(y')).
\]

### 证明

对等式反复施加单值映射 \(F\)，再施加 \(q\)。 \(\square\)

因此，闭合确定系统不能从完全相同的因果状态中“重新想起”已经被删除的差异。恢复只能来自：

- 差异其实仍保存在尚未纳入观察的隐藏状态中；
- 外界重新输入该信息；
- 新随机输入选择了不同分支；
- 状态更新规则或参数发生改变。

这比预测分区稳定更接近上下文遗忘的结构本质。只要两段旧历史被上下文截断、缓存覆盖或摘要映射压成同一个完整因果状态，它们在没有外界输入时便永久失去可区分性。

## 21.6 状态容量与预测容量的下降链

定义状态像容量

\[
r_t=|Y_t|=|F^t(Y)|.
\]

再把无限未来等价关系限制到 \(Y_t\)，定义可达预测状态数

\[
p_t
=
\left|
Y_t/{\equiv_\infty}
\right|.
\]

### 定理 21.6（双容量单调性）

对全部 \(t\ge0\)，

\[
\boxed{
r_{t+1}\le r_t,
\qquad
p_{t+1}\le p_t.}
\]

两条整数序列最终稳定，且

\[
\boxed{
\lim_{t\to\infty}r_t=|P_F|,}
\]

\[
\boxed{
\lim_{t\to\infty}p_t
=
\left|
P_F/{\equiv_\infty}
\right|.}
\]

若定义线性化

\[
L_F e_y=e_{F(y)},
\]

则

\[
\boxed{
r_t=\operatorname{rank}(L_F^t).}
\]

### 证明

由 \(Y_{t+1}\subseteq Y_t\) 得第一项。把固定等价关系限制到更小子集，只能删除非空等价类，不能产生新类，故第二项成立。有限非增整数列最终稳定。有限函数图中稳定像恰为全部周期点，得到两个极限公式。秩公式与定理 8.1 相同。 \(\square\)

定义单步损失：

\[
\ell_t^{\mathrm{state}}
=
r_{t-1}-r_t,
\]

\[
\ell_t^{\mathrm{pred}}
=
p_{t-1}-p_t.
\]

则

\[
\sum_{t\ge1}\ell_t^{\mathrm{state}}
=
|Y|-|P_F|,
\]

\[
\sum_{t\ge1}\ell_t^{\mathrm{pred}}
=
|Y/{\equiv_\infty}|
-
|P_F/{\equiv_\infty}|.
\]

前者计算有多少状态容量落在瞬态树上；后者计算有多少不同的完整预测未来最终不再可达。

这给出“退化”的一个严格但价值中性的含义：

\[
\boxed{
\text{闭环非单射动力学可以收缩可达状态与未来轨迹的容量}.}
\]

然而容量下降不自动等于文本质量下降。系统可能删除大量冗余状态而保留高质量周期，也可能保持全部状态容量却沿一个低质量长周期运行。

## 21.7 有限闭环系统的熵预算

令随机初态为 \(X_0\)，并定义

\[
X_{t+1}=F(X_t),
\qquad
O_t=q(X_t).
\]

### 定理 21.7（状态熵的逐步收缩）

对全部 \(t\ge0\)，

\[
\boxed{
H(X_t)-H(X_{t+1})
=
H(X_t\mid X_{t+1})
\ge0.}
\]

等号成立当且仅当在 \(X_t\) 的概率支撑上，\(X_t\) 可以由 \(X_{t+1}\) 唯一恢复。

### 证明

由于 \(X_{t+1}\) 是 \(X_t\) 的确定函数，

\[
H(X_{t+1}\mid X_t)=0.
\]

对联合变量 \((X_t,X_{t+1})\) 使用两种链式分解即得。 \(\square\)

### 定理 21.8（无外部熵注入与零输出熵率）

对任意 \(T\ge0\)，输出块

\[
\mathbf O_T=(O_0,\ldots,O_T)
\]

是 \(X_0\) 的确定函数，因此

\[
\boxed{
H(\mathbf O_T\mid X_0)=0,}
\]

\[
\boxed{
H(\mathbf O_T)\le H(X_0)\le\log|Y|.}
\]

所以

\[
\boxed{
\lim_{T\to\infty}
\frac{H(O_0,\ldots,O_T)}{T+1}
=0.}
\]

若把模型参数视为随机选择的配置 \(\Theta\)，则相应的条件形式是

\[
H(\mathbf O_T\mid \Theta,X_0)=0,
\]

\[
H(\mathbf O_T)
\le
H(\Theta,X_0).
\]

### 证明

整个输出块由复合映射

\[
X_0
\longmapsto
(q(X_0),q(FX_0),\ldots,q(F^TX_0))
\]

确定，故条件熵为零，并由确定性数据处理得到熵上界。分母趋于无穷而分子被常数 \(H(X_0)\) 控制，故熵率为零。 \(\square\)

这里的“没有新信息”必须作相对化理解：它指相对于已经知道完整参数、完整初态与完整确定规则的观察者，没有新的 Shannon 随机性被注入。一个外部人不知道权重中编码的结构，仍可能从长期展开中看到大量主观新颖内容；有限闭环定理并不把复杂展开等同于平庸重复。它只证明这种展开的总分支信息最终受初始有限状态预算控制。

## 21.8 有限性不是质量退化的充分原因

为了精确定义质量，令

\[
v:Y\to\mathbb R
\]

为状态质量函数。它可以读取下一输出的任务得分、事实一致性、非重复性或其他预先声明的有限状态评价。若质量依赖一个有限窗口，也可把评价器窗口并入状态。

给定允许的初态集合 \(A\subseteq Y\)，定义从 \(A\) 可达的周期核：

\[
P_F(A)
=
P_F
\cap
\bigcup_{t\ge0}F^t(A).
\]

### 定理 21.9（永久退化的周期核判据）

给定阈值 \(\alpha\)，下列条件等价：

1. 存在 \(N\ge0\)，使对全部 \(a\in A\) 与全部 \(t\ge N\)，
   \[
   v(F^t(a))\le\alpha;
   \]
2. 每个从 \(A\) 可达的周期状态都满足
   \[
   \boxed{
   v(p)\le\alpha
   \quad
   (p\in P_F(A)).}
   \]

### 证明

若 1 成立，任一可达周期状态会在某条轨迹上无限次出现，故其质量必须不超过 \(\alpha\)。

反之，每条有限状态轨迹最终进入一个可达周期。进入周期以前的瞬态长度对有限集合 \(A\) 有统一上界；进入周期以后全部状态都属于 \(P_F(A)\)，因而质量不超过 \(\alpha\)。 \(\square\)

因此，有限性给出的是：

\[
\boxed{
\text{长期行为完全由可达周期核决定}.}
\]

而“长期必然低质量”还需要额外条件：

\[
\boxed{
\text{全部可达周期核均为低质量}.}
\]

有限状态本身不提供这个条件。

### 定理 21.10（长期平均质量的循环公式）

若从 \(a\in A\) 出发最终进入周期

\[
C_a=(p_0,\ldots,p_{\lambda-1}),
\]

则

\[
\boxed{
\lim_{T\to\infty}
\frac1T
\sum_{t=0}^{T-1}v(F^t(a))
=
\frac1\lambda
\sum_{j=0}^{\lambda-1}v(p_j).}
\]

### 证明

有限瞬态前缀对 Cesàro 平均的贡献趋于零；其余项由周期块重复组成。 \(\square\)

所以长期平均退化也不是由 \(|Y|<\infty\) 单独决定，而是由各可达循环上的平均质量决定。

## 21.9 自回归上下文中的一阶合并判据

回到 \(L\)-token 正规形。把上下文写成

\[
c=(a,s),
\qquad
a\in\Sigma,
\qquad
s\in\Sigma^{L-1}.
\]

则

\[
F_\theta(a,s)
=
(s,g_\theta(a,s)).
\]

### 定理 21.11（同后缀上下文的合并判据）

对两个上下文

\[
c=(a,s),
\qquad
c'=(a',s'),
\]

有

\[
\boxed{
F_\theta(c)=F_\theta(c')
\iff
s=s'
\ \text{且}\
g_\theta(a,s)=g_\theta(a',s').}
\]

特别地，若两个上下文只在即将被丢弃的最旧 token 上不同，并生成相同下一 token，则它们一步后成为完全相同的因果状态，之后永远不可区分。

### 证明

比较两个后继的前 \(L-1\) 个坐标与最后一个坐标即可。 \(\square\)

这条定理把闭环语言模型的容量收缩定位到一个具体机制：

\[
\boxed{
\text{丢弃旧坐标}
+
\text{相同离散下一 token}
\Longrightarrow
\text{状态合并}.}
\]

若实际 KV cache 完全由保留的 token 窗口与固定位置规则重算，该结论直接适用。若系统另有持久隐藏记忆、全局位置、检索缓存或工具状态，则这些分量必须一并比较；只看 token 后缀相同不足以证明完整状态已经合并。

还有一个更早的压缩发生在上下文投影本身。令

\[
\rho_L:\Sigma^*\to\Sigma^{\le L}
\]

只保留末尾 \(L\) 个 token。若两段完整历史 \(h,h'\) 满足

\[
\rho_L(h)=\rho_L(h')
\]

且没有其他状态保存其差异，则它们在进入模型前已经被识别为同一因果状态。此后模型不能从闭环内部恢复被截断的事实来源、早期约束或身份信息。

## 21.10 确定解码、概率读出与分支压缩

设模型对每个状态给出有限精度概率向量

\[
\pi_\theta(y)\in\mathcal P(\Sigma).
\]

贪心解码使用

\[
g_\theta(y)
=
\operatorname*{arg\,max}_{x\in\Sigma}
\pi_\theta(y)(x),
\]

连同一个固定 tie-breaking 规则。映射

\[
\pi_\theta(y)\longmapsto g_\theta(y)
\]

通常是多对一的：不同概率向量可以选择同一 token。若更新只保留被选 token，而不保留足以区分原概率向量的其他状态，则离散选择可能增加后继碰撞。

这并不证明贪心解码必然产生低质量文本。严格结论只是：

\[
\boxed{
\text{把较细的概率状态投影为单一 token，
不会增加可区分状态，且可能删除分支}.}
\]

低温采样、top-\(k\)、top-\(p\) 或其他解码规则应分别建模为状态到输出或状态—随机输入到输出的映射；仅凭“随机”二字不能推断容量是否恢复。

## 21.11 新随机输入会改变定理的类型

若每一步接收新随机变量 \(U_t\)，更新写成

\[
X_{t+1}=G(X_t,U_t).
\]

此时仅以 \(X_t\) 为状态，系统不是闭合确定映射。有限状态 Markov 链可以进入 recurrent class，但带有持续新随机输入的样本路径一般不需要最终周期。

存在两种不同情况。

### 有限状态伪随机发生器

若随机源实际由有限内部状态 \(R_t\) 确定：

\[
R_{t+1}=J(R_t),
\]

\[
X_{t+1}=G(X_t,R_t),
\]

则扩展状态

\[
\widetilde Y=Y\times R
\]

仍有限，扩展更新仍确定。于是最终周期定理重新成立，但周期上界乘入 \(|R|\)。

### 真正持续的外部随机输入

若 \(U_0,U_1,\ldots\) 是未预先包含在有限初态中的新随机比特，则它们构成外界信息流。第 21.8 节的零熵率结论不再适用；输出可以持续获得正的条件熵。此时应使用 Markov recurrent class、概率双模拟或随机动力学，而不能把确定性“状态重复即未来完全相同”原封不动地套用到样本路径。

所以：

\[
\boxed{
\text{采样是否打破有限闭环，
取决于随机性是新外部输入，
还是有限内部 PRNG 状态的展开}.}
\]

## 21.12 两个二元窗口反例

以下两个四状态系统说明“有限”“预测稳定”“状态容量下降”和“输出重复”不能混为一谈。

### 例 21.12A（立即进入常量输出的压缩系统）

令

\[
\Sigma=\{0,1\},
\qquad
L=2,
\]

并取

\[
g(a,b)=b.
\]

则

\[
F(a,b)=(b,b).
\]

函数图为

\[
00\mapsto00,
\qquad
01\mapsto11,
\qquad
10\mapsto00,
\qquad
11\mapsto11.
\]

像链为

\[
|\Sigma^2|=4
\longrightarrow
2
\longrightarrow
2.
\]

每条输出在至多一步后成为全 \(0\) 或全 \(1\)。然而若读出为

\[
q(a,b)=g(a,b)=b,
\]

则当前输出已经完全决定全部未来输出，因此

\[
\boxed{m_*=0.}
\]

这证明：

\[
\boxed{
\text{预测分区立即稳定}
\not\Longrightarrow
\text{系统没有发生容量压缩}.}
\]

它也说明 \(m_*\) 小不代表模型质量高；这里只表示观察者不需要更长未来就能知道所属的常量输出类。

### 例 21.12B（无容量压缩的四循环）

仍令 \(\Sigma=\{0,1\}\)、\(L=2\)，定义

\[
g(00)=1,
\qquad
g(01)=1,
\qquad
g(11)=0,
\qquad
g(10)=0.
\]

则

\[
00\mapsto01\mapsto11\mapsto10\mapsto00.
\]

这里 \(F\) 是四状态置换，所以

\[
|F^t(Y)|=4
\quad
\text{对全部 }t\ge0.
\]

没有任何状态容量损失。输出按

\[
1,1,0,0,1,1,0,0,\ldots
\]

循环；未来一个额外坐标足以区分四个状态，所以

\[
m_*=1.
\]

该例证明：

\[
\boxed{
\text{有限状态}
\not\Longrightarrow
\text{非单射压缩或固定点塌缩}.}
\]

更一般地，有限系统可以是状态空间上的一个长置换循环。有限性保证周期存在，却不保证周期短、重复模式简单或质量低。

## 21.13 LLM 退化的四个互异层次

为了避免把不同现象统称为“退化”，本节区分：

### 状态容量退化

\[
|F^t(Y)|
\]

显著下降。它测量多少完整因果状态仍可达。

### 预测容量退化

\[
\left|
F^t(Y)/{\equiv_\infty}
\right|
\]

显著下降。它测量多少不同的完整未来输出轨迹仍可达。

### 循环或重复退化

可达周期长度很短，或周期输出具有高重复性。这需要审计周期谱，而不能仅由状态数有限推出。

### 语义或任务质量退化

可达周期核上的质量函数 \(v\) 较低，或循环平均质量较低。其精确判据由定理 21.9 与 21.10 给出。

四者可以相关，但逻辑上互不等价。一个系统可以：

- 状态容量下降而质量保持；
- 状态容量不降却在低质量长循环上运行；
- 输出高度重复但任务评价仍正确；
- 预测类别很少但每个类别都高质量；
- 在巨大周期上长期表现丰富，却最终仍受有限状态约束。

因此，对“有限状态是否是大语言模型退化的原因”的严格回答是：

\[
\boxed{
\text{有限闭环是最终复现与有限信息预算的结构边界，
但不是质量退化的充分原因}.}
\]

更接近因果机制的是：

\[
\boxed{
\text{有限闭环}
+
\text{非单射历史压缩}
+
\text{自反馈进入短或低质量吸引循环}
+
\text{缺少新的外界校正信息}.}
\]

这里每一项都必须单独测量；不能从第一项直接推出其余三项。

## 21.14 与“模型参数构成有限系统”的最终关系

设参数共 \(bN\) 比特，运行时因果状态共至多 \(m\) 比特。若参数固定，则一个具体模型至多有

\[
2^m
\]

个运行状态。若把所有可能模型配置与运行状态共同视为一个扩展系统，则上界为

\[
2^{bN+m}.
\]

但第 19 节中的

\[
m_*\le |Y|-|O|
\]

应使用当前固定模型的完整动态状态集合 \(Y\)，而不是把参数个数 \(N\) 直接代入。即使形式上取

\[
|Y|\le2^m,
\]

所得上界也通常极松：

\[
m_*
\le
2^m-|O|.
\]

它没有解释为什么某次实际生成会在几百或几千 token 内出现重复。要解释有限时间尺度，必须研究具体函数图的：

\[
\boxed{
\text{瞬态高度、像秩下降、状态碰撞、周期长度及周期质量}.}
\]

换言之，参数规模主要决定转移函数的描述容量；运行状态结构决定闭环轨迹；吸引子几何决定长期行为；观察映射决定哪些差异对用户可见。

## 21.15 新的自治生成审计

在前文六重观察者审计之外，对闭环生成器应增加自治长期审计。至少记录：

\[
\boxed{
\begin{aligned}
&\text{状态像曲线 }(|F^t(Y)|)_{t\ge0},\\
&\text{预测类曲线 }
\left(
|F^t(Y)/{\equiv_\infty}|
\right)_{t\ge0},\\
&\text{可达周期长度谱},\\
&\text{周期输出的重复统计},\\
&\text{周期核上的最小与平均质量},\\
&\text{状态合并首次发生的深度},\\
&\text{外部信息与新随机熵的注入率}.
\end{aligned}}
\]

这些量回答不同问题：

- 像曲线检测非单射容量压缩；
- 预测类曲线检测不同未来的消失；
- 周期谱检测最终重复结构；
- 周期质量判断重复是否构成真正质量退化；
- 合并深度定位上下文遗忘何时变得不可逆；
- 外部信息率区分闭合展开与持续开放系统。

只有联合这些审计，才能把“模型变得重复”“模型忘记早期约束”“模型失去事实锚定”“模型语义质量下降”拆成可检验的数学命题。

## 21.16 严格边界

1. 本节不主张所有现实部署的语言模型都是有限自治系统。网络检索、工具调用、用户消息、系统时钟、无界外部存储和新随机输入都会改变闭合假设。
2. 固定参数数量有限不等于状态空间有限；精确实数、无界上下文和无界可读内存均可破坏有限性。
3. 本节的最终周期结论针对有限确定性扩展状态。带持续新随机输入的有限 Markov 系统应使用概率长期理论。
4. 输出 transcript 可以无界增长；有限性只针对会反向影响未来计算的因果状态。
5. 零输出熵率是相对于完整初态分布的 Shannon 结论，不等同于人类观察到的语义新颖度、压缩难度或价值。
6. \(m_*\) 是预测分区完成深度，不是退化时间、上下文长度或周期进入时间。
7. 状态容量、预测容量、周期长度与任务质量互不等价；任何“有限所以必然变差”的推断都缺少周期核质量前提。
8. 本节没有给出特定商业模型的实测退化结论，也没有把合成数据训练中的权重分布变化与固定权重推理混为同一系统。
9. 本节没有改变本文关于 Li–Cayley、Weil 正性或 Riemann 假设的既有边界。

## 21.17 形式化状态

定理 21.1—21.11 及例 21.12A—B 均给出纸面定义与证明，尚未成为 Lean 真源。建议的形式化顺序为：

1. 有限直积运行时归约；
2. 有限窗口 shift-register 更新；
3. 有限自映射的最终周期界；
4. 未来词关系的一步稳定；
5. 状态合并不可逆性；
6. 状态像与预测类双容量单调性；
7. 确定推前的 Shannon 熵收缩；
8. 输出块熵有界与零熵率；
9. 可达周期核上的阈值质量判据；
10. 循环平均质量公式；
11. 同后缀上下文的一步合并判据；
12. 两个二元窗口反例的有限枚举验证。

在获得 proof term、依赖闭包与冻结收据以前，本节不得标记为 `Closed`。

---

# 22. 追加：观察精化的函子性、同余内核与多观察者融合

第 19 节已经对单一读出
\[
q:Y\to O
\]
构造了最小预测完成
\[
Z_q=Y/{\equiv_\infty^q}.
\]
本节研究不同观察界面之间的关系。核心问题不再是“一个观察是否闭合”，而是：

1. 当一个读出比另一个更细时，它们的完成是否存在规范映射；
2. 先完成再粗化，是否等价于直接完成粗读出；
3. 多个观察者联合时，完成状态是简单直积，还是只占据直积中的兼容子集；
4. 状态数、完成深度与信息成本在观察精化下分别怎样变化。

这些问题给出一个比单点最小化更稳定的结构：预测完成不是孤立商，而组成一个由观察精化驱动的规范商塔。

固定非空有限集合 \(Y\) 与自映射
\[
\tau:Y\to Y.
\]
对任意读出 \(q:Y\to O\)，把 \(O\) 替换为实际像 \(q(Y)\)，并定义
\[
y\,R_q\,y'
\iff
q(\tau^k y)=q(\tau^k y')
\quad\text{对全部 }k\ge0.
\]
于是
\[
R_q=\equiv_\infty^q,
\qquad
Z_q=Y/R_q,
\qquad
\pi_q:Y\twoheadrightarrow Z_q.
\]
商动力学与商读出记为
\[
\overline\tau_q([y]_q)=[\tau y]_q,
\qquad
\overline q([y]_q)=q(y).
\]

## 22.1 观察精化与规范商映射

### 定义 22.1（观察精化）

设
\[
q:Y\to O,
\qquad
r:Y\to P.
\]
称 \(q\) **精化** \(r\)，记为
\[
q\succeq_{\mathrm{obs}} r,
\]
若存在映射
\[
h:O\to P
\]
使
\[
\boxed{r=h\circ q.}
\]
这表示 \(r\) 可以从 \(q\) 的当前读数确定地计算出来；\(q\) 至少保留 \(r\) 的全部当前信息。

### 定理 22.2（预测关系随观察精化单调）

若
\[
r=h\circ q,
\]
则
\[
\boxed{R_q\subseteq R_r.}
\]
因此存在唯一满射
\[
\boxed{
\kappa_{q,r}:Z_q\twoheadrightarrow Z_r
}
\]
满足
\[
\boxed{
\pi_r=\kappa_{q,r}\pi_q.
}
\]
并且该映射同时保持动力学与读出：
\[
\boxed{
\kappa_{q,r}\overline\tau_q
=
\overline\tau_r\kappa_{q,r},
}
\]
\[
\boxed{
\overline r\,\kappa_{q,r}
=
h\,\overline q.
}
\]

### 证明

若 \(yR_qy'\)，则对每个 \(k\ge0\)，
\[
q(\tau^k y)=q(\tau^k y').
\]
施加 \(h\) 得
\[
r(\tau^k y)
=
h(q(\tau^k y))
=
h(q(\tau^k y'))
=
r(\tau^k y'),
\]
故 \(yR_ry'\)。于是 \(\pi_r\) 在每个 \(\pi_q\)-纤维上常值，唯一因子化为
\[
\pi_r=\kappa_{q,r}\pi_q.
\]
由于 \(\pi_r\) 满射，\(\kappa_{q,r}\) 亦满射。

对任意 \(y\in Y\)，
\[
\begin{aligned}
\kappa_{q,r}\overline\tau_q(\pi_q y)
&=
\kappa_{q,r}(\pi_q(\tau y))\\
&=
\pi_r(\tau y)\\
&=
\overline\tau_r(\pi_r y)\\
&=
\overline\tau_r\kappa_{q,r}(\pi_q y).
\end{aligned}
\]
\(\pi_q\) 满射，所以动力学交换式成立。读出交换式同理：
\[
\overline r\kappa_{q,r}\pi_q
=
\overline r\pi_r
=
r
=
hq
=
h\overline q\pi_q.
\]
\(\square\)

### 推论 22.3（规范映射的恒等与复合）

有
\[
\boxed{\kappa_{q,q}=\mathrm{id}_{Z_q}.}
\]
若
\[
q\succeq_{\mathrm{obs}}r
\succeq_{\mathrm{obs}}s,
\]
则
\[
\boxed{
\kappa_{q,s}
=
\kappa_{r,s}\circ\kappa_{q,r}.
}
\]

### 证明

两式都由
\[
\pi_r=\kappa_{q,r}\pi_q
\]
的唯一因子化直接得到。对于复合，
\[
(\kappa_{r,s}\kappa_{q,r})\pi_q
=
\kappa_{r,s}\pi_r
=
\pi_s,
\]
故唯一性迫使它等于 \(\kappa_{q,s}\)。\(\square\)

所以预测完成不是任意选择的最小模型。观察精化一旦给定，完成之间的映射便由原始状态投影唯一决定：
\[
\boxed{
q\longmapsto Z_q,
\qquad
(q\succeq_{\mathrm{obs}}r)
\longmapsto
(Z_q\twoheadrightarrow Z_r).
}
\]
更细观察产生更细预测状态；从细状态到粗状态的方向是规范满射，而不是非规范嵌入。

### 推论 22.4（完成状态数的单调性）

若
\[
q\succeq_{\mathrm{obs}}r,
\]
则
\[
\boxed{|Z_q|\ge |Z_r|.}
\]

这是一条状态数单调律，但它不蕴含完成深度 \(m_*\) 的单调性；第 22.8 节将给出严格反例。

## 22.2 完成的幂等性与级联定理

完成状态 \(Z_q\) 已经把所有无限未来可区分状态分开。该陈述需要与“当前读出已经构成一步封闭状态”严格区分。

### 定理 22.5（预测完成的幂等性）

在系统
\[
(Z_q,\overline\tau_q,\overline q)
\]
上重新定义无限未来等价：
\[
z\widehat R_q z'
\iff
\overline q(\overline\tau_q^k z)
=
\overline q(\overline\tau_q^k z')
\quad\text{对全部 }k\ge0.
\]
则
\[
\boxed{
\widehat R_q=\Delta_{Z_q},
}
\]
其中 \(\Delta_{Z_q}\) 是相等关系。因此再次取预测完成不会产生新的状态识别：
\[
\boxed{
Z_{\overline q}\cong Z_q.
}
\]

### 证明

取
\[
z=\pi_q(y),
\qquad
z'=\pi_q(y').
\]
若 \(z\widehat R_qz'\)，则对全部 \(k\ge0\)，
\[
q(\tau^k y)
=
\overline q(\overline\tau_q^k z)
=
\overline q(\overline\tau_q^k z')
=
q(\tau^k y').
\]
故 \(yR_qy'\)，于是
\[
z=\pi_q(y)=\pi_q(y')=z'.
\]
反向显然。\(\square\)

这里不能推出
\[
m_*(\overline q,\overline\tau_q)=0.
\]
幂等性只说**无限未来等价已等于状态相等**；若 \(\overline q\) 当前仍把多个预测状态映到同一输出，观察者仍可能需要若干未来坐标才能从读出词识别具体的 \(z\in Z_q\)。

### 定理 22.6（先细完成再粗完成的级联定理）

设
\[
r=hq.
\]
在 \(Z_q\) 上定义粗读出
\[
r_q=h\overline q:Z_q\to P.
\]
令 \(\widehat R_{r|q}\) 是系统
\[
(Z_q,\overline\tau_q,r_q)
\]
的无限未来等价关系。则
\[
\boxed{
\pi_q(y)\,\widehat R_{r|q}\,\pi_q(y')
\iff
yR_ry'.
}
\]
因此
\[
\boxed{
Z_q/\widehat R_{r|q}
\cong
Z_r,
}
\]
并且该同构把二次完成投影识别为
\[
\kappa_{q,r}:Z_q\twoheadrightarrow Z_r.
\]

### 证明

逐定义计算：
\[
\begin{aligned}
\pi_q(y)\,\widehat R_{r|q}\,\pi_q(y')
&\iff
r_q(\overline\tau_q^k\pi_q y)
=
r_q(\overline\tau_q^k\pi_q y')
\quad(\forall k)\\
&\iff
h\overline q(\pi_q\tau^k y)
=
h\overline q(\pi_q\tau^k y')
\quad(\forall k)\\
&\iff
r(\tau^k y)=r(\tau^k y')
\quad(\forall k)\\
&\iff
yR_ry'.
\end{aligned}
\]
于是二次商的纤维恰是 \(R_r\)-类，故与 \(Y/R_r\) 规范同构。\(\square\)

因此
\[
\boxed{
\operatorname{Comp}(r)
\cong
\operatorname{Comp}
\bigl(
h\overline q:
\operatorname{Comp}(q)\to P
\bigr).
}
\]
这给出完成与观察级联之间的精确相容性：先保留细观察的全部预测信息，再按 \(h\) 粗化并重新最小化，不会比从原系统直接构造粗完成多出或少掉状态。

## 22.3 最大同余内核是关系格上的内算子

第 19 节只对
\[
R=\ker q
\]
定义了 greatest-fixed-point。现在把它提升到任意等价关系。

对 \(Y\) 上等价关系 \(R\)，定义
\[
\boxed{
\mathsf C_\tau(R)
=
\bigcap_{k\ge0}
(\tau^k\times\tau^k)^{-1}(R).
}
\]
即
\[
y\,\mathsf C_\tau(R)\,y'
\iff
\tau^k y\,R\,\tau^k y'
\quad\text{对全部 }k\ge0.
\]

### 定理 22.7（同余内核定理）

\(\mathsf C_\tau\) 满足：

1. \(\mathsf C_\tau(R)\) 是等价关系；
2. 它是 \(\tau\)-同余：
   \[
   y\,\mathsf C_\tau(R)\,y'
   \Longrightarrow
   \tau y\,\mathsf C_\tau(R)\,\tau y';
   \]
3. 它收缩原关系：
   \[
   \boxed{\mathsf C_\tau(R)\subseteq R;}
   \]
4. 它对包含关系单调：
   \[
   R\subseteq S
   \Longrightarrow
   \mathsf C_\tau(R)\subseteq\mathsf C_\tau(S);
   \]
5. 它幂等：
   \[
   \boxed{
   \mathsf C_\tau(\mathsf C_\tau(R))
   =
   \mathsf C_\tau(R);
   }
   \]
6. 它是包含于 \(R\) 的最大 \(\tau\)-同余。

等价地，若 \(\operatorname{Cong}_\tau(Y)\) 表示全部 \(\tau\)-同余，则对每个
\[
S\in\operatorname{Cong}_\tau(Y)
\]
有
\[
\boxed{
S\subseteq R
\iff
S\subseteq\mathsf C_\tau(R).
}
\]

### 证明

每个
\[
(\tau^k\times\tau^k)^{-1}(R)
\]
都是等价关系，任意交仍是等价关系，得到第一项。

若 \(y\mathsf C_\tau(R)y'\)，则对全部 \(k\ge0\)，
\[
\tau^{k+1}y\,R\,\tau^{k+1}y',
\]
故
\[
\tau y\,\mathsf C_\tau(R)\,\tau y'.
\]
第三项取 \(k=0\) 即得。第四项由逆像与交对包含关系的单调性得到。

由于 \(\mathsf C_\tau(R)\) 本身已经是 \(\tau\)-同余，对任意 \(k\)，
\[
y\,\mathsf C_\tau(R)\,y'
\Longrightarrow
\tau^k y\,\mathsf C_\tau(R)\,\tau^k y',
\]
故
\[
\mathsf C_\tau(R)
\subseteq
\mathsf C_\tau(\mathsf C_\tau(R)).
\]
反向包含由第三项应用于关系 \(\mathsf C_\tau(R)\) 得到，故幂等。

若 \(S\subseteq R\) 且 \(S\) 是 \(\tau\)-同余，则
\[
ySy'
\Longrightarrow
\tau^k y\,S\,\tau^k y'
\Longrightarrow
\tau^k y\,R\,\tau^k y'
\]
对全部 \(k\) 成立，所以
\[
S\subseteq\mathsf C_\tau(R).
\]
结合 \(\mathsf C_\tau(R)\subseteq R\)，得到最大性与最后的等价式。\(\square\)

因此 \(\mathsf C_\tau\) 是等价关系格上的一个**内算子**：

\[
\boxed{
\text{单调}
+
\text{收缩}
+
\text{幂等}.
}
\]

它的固定点恰为 \(\tau\)-同余。第 19 节的预测关系只是特殊情形
\[
\boxed{
R_q=\mathsf C_\tau(\ker q).
}
\]

### 定理 22.8（有限下降与一般稳定界）

令
\[
R_0=R,
\qquad
R_{m+1}
=
R\cap(\tau\times\tau)^{-1}(R_m).
\]
则
\[
R_m
=
\bigcap_{k=0}^{m}
(\tau^k\times\tau^k)^{-1}(R),
\]
且最终稳定到
\[
\mathsf C_\tau(R).
\]
若 \(R\) 有 \(c_0\) 个等价类，则最小稳定指标 \(m_R\) 满足
\[
\boxed{
m_R
\le
|Y/\mathsf C_\tau(R)|-c_0
\le
|Y|-c_0.
}
\]

### 证明

递推展开给出有限交公式。关系链逐步细化，商类数是从 \(c_0\) 开始、至多为 \(|Y|\) 的非降整数列。每次严格变化至少增加一个类，所以在至多
\[
|Y/\mathsf C_\tau(R)|-c_0
\]
次严格变化后稳定。一次稳定后，递推算子已到不动点，故永久稳定；极限由定理 22.7 的最大性等于 \(\mathsf C_\tau(R)\)。\(\square\)

## 22.4 与 Koopman 不变闭包的有限对偶

对等价关系 \(R\)，定义纤维常值代数
\[
\mathcal A_R
=
\{f:Y\to\mathbb C:
yRy'\Longrightarrow f(y)=f(y')\}.
\]
令 Koopman 拉回为
\[
K_\tau f=f\circ\tau.
\]
定义包含 \(\mathcal A_R\) 的最小 \(K_\tau\)-不变含幺交换
\(*\)-代数：
\[
\boxed{
\mathsf K_\tau(\mathcal A_R)
=
\operatorname{alg}^*
\left(
\bigcup_{k\ge0}K_\tau^k\mathcal A_R
\right).
}
\]

### 定理 22.9（同余内核—Koopman 闭包对偶）

有
\[
\boxed{
\mathsf K_\tau(\mathcal A_R)
=
\mathcal A_{\mathsf C_\tau(R)}.
}
\]

### 证明

若
\[
y\,\mathsf C_\tau(R)\,y',
\]
则对全部 \(k\ge0\)，
\[
\tau^k y\,R\,\tau^k y'.
\]
所以对任意 \(f\in\mathcal A_R\)，
\[
K_\tau^k f(y)
=
f(\tau^k y)
=
f(\tau^k y')
=
K_\tau^k f(y').
\]
因此全部生成元以及由它们生成的代数都在
\(\mathsf C_\tau(R)\)-类上常值：
\[
\mathsf K_\tau(\mathcal A_R)
\subseteq
\mathcal A_{\mathsf C_\tau(R)}.
\]

反之，令 \(C\) 遍历 \(R\)-等价类。其指示函数
\[
\mathbf 1_C
\]
属于 \(\mathcal A_R\)，而
\[
K_\tau^k\mathbf 1_C
=
\mathbf 1_{(\tau^k)^{-1}(C)}.
\]
有限多个这类指示函数的乘积给出所有有限联合分区原子的指示函数。稳定以后，这些原子正是
\[
\bigcap_{k\ge0}(\tau^k)^{-1}(C_k)
\]
的非空集合，也就是 \(\mathsf C_\tau(R)\)-类。故每个
\(\mathsf C_\tau(R)\)-类的指示函数都属于生成代数，它们张成
\(\mathcal A_{\mathsf C_\tau(R)}\)。得到反向包含。\(\square\)

关系侧与代数侧的方向相反：

\[
\boxed{
\mathsf C_\tau(R)\subseteq R
\quad\Longleftrightarrow\quad
\mathcal A_R
\subseteq
\mathcal A_{\mathsf C_\tau(R)}.
}
\]

关系被细化，是为了恢复未来可区分性；可观测代数被扩张，是为了加入全部未来拉回坐标。二者不是两套完成，而是同一有限分区对偶的两种表示。

取
\[
R=\ker q
\]
便恢复第 19 节：
\[
\boxed{
\mathbb C^{Z_q}
\cong
\mathsf K_\tau(q^*\mathbb C^O).
}
\]

## 22.5 有限词商塔中的分级动力学

令
\[
R_m=\equiv_m^q,
\qquad
Z_m=Y/R_m.
\]
因为
\[
R_{m+1}\subseteq R_m,
\]
存在规范满射
\[
p_{m+1,m}:Z_{m+1}\twoheadrightarrow Z_m.
\]

在未稳定以前，\(\tau\) 一般不能定义为 \(Z_m\) 上的自映射；但它始终定义一个跨层映射。

### 定理 22.10（分级移位）

映射
\[
\boxed{
s_m:Z_{m+1}\to Z_m,
\qquad
s_m([y]_{m+1})=[\tau y]_m
}
\]
良定义。并且
\[
p_{m+1,m}([y]_{m+1})=[y]_m
\]
与 \(s_m\) 共同编码“删除当前读出坐标”的有限词移位。

当
\[
R_{m_*}=R_{m_*+1}
\]
时，\(p_{m_*+1,m_*}\) 是双射，因而 \(s_{m_*}\) 经该双射识别为
\[
Z_{m_*}=Z_q
\]
上的闭合动力学 \(\overline\tau_q\)。

### 证明

若
\[
yR_{m+1}y',
\]
则
\[
q(\tau^{k+1}y)=q(\tau^{k+1}y')
\quad(0\le k\le m),
\]
故
\[
\tau y\,R_m\,\tau y'.
\]
所以 \(s_m\) 良定义。稳定时两个关系相等，规范满射成为双射；此时同一公式正是商动力学。\(\square\)

因此有限深度观察不是“近似的闭合状态”那么简单。更精确的结构是：

\[
\boxed{
Z_{m+1}
\overset{s_m}{\longrightarrow}
Z_m.
}
\]

只有在稳定层，跨层移位才闭合为同层自映射。这个分级接口将在第 24 节给出定量误差解释。

## 22.6 多观察者融合与兼容子积

设 \(I\) 为非空有限指标集，对每个 \(i\in I\) 有读出
\[
q_i:Y\to O_i.
\]
定义联合读出
\[
q_I:Y\to\prod_{i\in I}O_i,
\qquad
q_I(y)=(q_i(y))_{i\in I}.
\]

### 定理 22.11（联合预测关系是交）

有
\[
\boxed{
R_{q_I}
=
\bigcap_{i\in I}R_{q_i}.
}
\]

### 证明

\[
\begin{aligned}
yR_{q_I}y'
&\iff
q_I(\tau^k y)=q_I(\tau^k y')
\quad(\forall k)\\
&\iff
q_i(\tau^k y)=q_i(\tau^k y')
\quad(\forall i,\forall k)\\
&\iff
yR_{q_i}y'
\quad(\forall i).
\end{aligned}
\]
\(\square\)

于是存在规范映射
\[
\boxed{
J_I:Z_{q_I}\longrightarrow\prod_{i\in I}Z_{q_i},
\qquad
J_I([y]_{q_I})=([y]_{q_i})_{i\in I}.
}
\]

### 定理 22.12（融合完成嵌入与兼容像）

\(J_I\) 是单射，并与各分量动力学交换。其像恰为兼容子集
\[
\boxed{
\operatorname{Comp}_I
=
\left\{
(z_i)_{i\in I}:
\exists y\in Y,\quad
\pi_{q_i}(y)=z_i\ \forall i
\right\}.
}
\]
因此
\[
\boxed{
Z_{q_I}
\cong
\operatorname{Comp}_I
\subseteq
\prod_{i\in I}Z_{q_i}.
}
\]

### 证明

若
\[
J_I([y])=J_I([y']),
\]
则
\[
yR_{q_i}y'
\quad\text{对全部 }i.
\]
由定理 22.11，
\[
yR_{q_I}y',
\]
故 \([y]=[y']\)，所以 \(J_I\) 单射。像的描述由定义直接得到。动力学交换式逐分量使用
\[
\pi_{q_i}\tau
=
\overline\tau_{q_i}\pi_{q_i}.
\]
\(\square\)

对于两个观察者，记
\[
c_1=|Z_{q_1}|,
\qquad
c_2=|Z_{q_2}|,
\qquad
c_{12}=|Z_{(q_1,q_2)}|.
\]

### 推论 22.13（融合状态数界）

有
\[
\boxed{
\max(c_1,c_2)
\le
c_{12}
\le
\min(|Y|,c_1c_2).
}
\]

### 证明

联合读出精化每个分量读出，所以由定理 22.2 存在
\[
Z_{12}\twoheadrightarrow Z_i,
\]
得到下界。上界分别来自
\[
Z_{12}=Y/R_{12}
\]
是 \(Y\) 的商，以及定理 22.12 的直积嵌入。\(\square\)

### 定理 22.14（直积充满判据）

对两个观察者，下列条件等价：

1. \(J_{\{1,2\}}\) 满射；
2. 每对预测类
   \[
   C_1\in Z_{q_1},
   \qquad
   C_2\in Z_{q_2}
   \]
   都有非空交：
   \[
   C_1\cap C_2\ne\varnothing;
   \]
3. 有
   \[
   \boxed{c_{12}=c_1c_2.}
   \]

### 证明

\(J\) 的像由定理 22.12 恰是存在共同实现状态的类对，所以 1 与 2 等价。\(J\) 已知单射，因此其像等于有限直积当且仅当两者基数相等，得到 1 与 3 等价。\(\square\)

一般而言，
\[
Z_{12}
\ne
Z_1\times Z_2.
\]
两个观察者各自合法的预测状态组合，未必都能由同一个微观状态同时实现。直积中的缺失点不是信息损坏，而是**兼容性约束**。

定义组合兼容亏损
\[
\boxed{
\chi_{\mathrm{comp}}(q_1,q_2)
=
\log
\frac{c_1c_2}{c_{12}}
\ge0.
}
\]
则
\[
\chi_{\mathrm{comp}}=0
\]
当且仅当全部预测状态对均可共同实现。

这个量只测量支持集未充满直积的组合亏损。它不是给定概率分布下的互信息，也不是 partial information decomposition 意义下的“冗余”或“协同”。

### 定理 22.15（独立直积系统的完全分解）

设
\[
Y=Y_1\times Y_2,
\qquad
\tau(y_1,y_2)=(\tau_1y_1,\tau_2y_2),
\]
并令
\[
q_1'(y_1,y_2)=q_1(y_1),
\qquad
q_2'(y_1,y_2)=q_2(y_2).
\]
则
\[
\boxed{
Z_{(q_1',q_2')}
\cong
Z_{q_1}\times Z_{q_2}
}
\]
且动力学为分量商动力学的直积。

### 证明

联合未来读出相同，当且仅当第一分量的全部未来 \(q_1\)-读出相同且第二分量的全部未来 \(q_2\)-读出相同。因此联合等价类恰为
\[
[y_1]_{q_1}\times[y_2]_{q_2}.
\]
每个类对都由任意代表元对实现，所以定理 22.14 的充满条件成立。\(\square\)

## 22.7 融合的 Shannon 恒等式

令随机初态 \(Y_0\) 取值于 \(Y\)，定义
\[
Z_i=\pi_{q_i}(Y_0),
\qquad
Z_{12}=\pi_{(q_1,q_2)}(Y_0).
\]
定理 22.12 给出
\[
J(Z_{12})=(Z_1,Z_2),
\]
且 \(J\) 在 \(Z_{12}\) 上单射。

### 定理 22.16（融合状态熵等于联合预测熵）

有
\[
\boxed{
H(Z_{12})
=
H(Z_1,Z_2).
}
\]
因此
\[
\boxed{
H(Z_{12})
=
H(Z_1)+H(Z_2\mid Z_1)
}
\]
以及
\[
\boxed{
H(Z_{12})
=
H(Z_2)+H(Z_1\mid Z_2).
}
\]

### 证明

有限随机变量在双射重命名下熵不变。\(J\) 把 \(Z_{12}\) 双射到随机向量 \((Z_1,Z_2)\) 的实际支持，故第一式成立；其余为 Shannon 链式法则。\(\square\)

这给出两种不同的融合增益：

\[
\boxed{
G^{\mathrm{card}}_{2\mid1}
=
\log\frac{c_{12}}{c_1}
}
\]
是最坏情形的状态数增益，而
\[
\boxed{
G^{\mathrm{Sh}}_{2\mid1}
=
H(Z_2\mid Z_1)
}
\]
是给定初始分布下的平均增益。二者不能互换；前者只依赖支持与动力学，后者还依赖概率质量。

## 22.8 完成深度在观察精化下不单调

完成状态数随观察精化单调增加，但达到完成所需的未来词深度不满足同样的单调律。

令
\[
Y_n=\{0,1,\ldots,n-1\},
\qquad
n\ge3,
\]
并定义向根收缩的链动力学
\[
\tau(0)=0,
\qquad
\tau(i)=i-1
\quad(i\ge1).
\]
考虑三个读出：

\[
r(i)=0
\quad\text{（常值读出）},
\]
\[
q(i)=
\begin{cases}
1,&i=0,\\
0,&i>0,
\end{cases}
\quad\text{（根脉冲读出）},
\]
\[
e(i)=i
\quad\text{（恒等读出）}.
\]
显然
\[
e\succeq_{\mathrm{obs}}q
\succeq_{\mathrm{obs}}r.
\]

### 定理 22.17（精化深度的双向反例与稳定界锐性）

上述系统满足
\[
\boxed{
m_*(r)=0,
\qquad
m_*(q)=n-2,
\qquad
m_*(e)=0.
}
\]
并且
\[
\boxed{
|Z_r|=1,
\qquad
|Z_q|=|Z_e|=n.
}
\]

因此：

1. 从 \(r\) 精化到 \(q\) 时，完成深度从 \(0\) 增加到 \(n-2\)；
2. 从 \(q\) 再精化到 \(e\) 时，完成深度从 \(n-2\) 降回 \(0\)；
3. 第 19 节的界
   \[
   m_*\le|Y|-|O|
   \]
   对 \(q\) 取等号：
   \[
   \boxed{
   m_*(q)=n-2=|Y_n|-|q(Y_n)|.
   }
   \]

### 证明

常值读出的所有有限词都相同，故 \(m_*(r)=0\)。

恒等读出在当前时刻已经分离全部状态，所以 \(m_*(e)=0\)。

对根脉冲读出，从状态 \(i\) 出发的无限输出为
\[
\underbrace{0,\ldots,0}_{i\text{ 项}},
1,1,1,\ldots.
\]
故不同 \(i\) 给出不同无限轨迹，\(Z_q\) 有 \(n\) 个状态。状态 \(n-2\) 与 \(n-1\) 在时刻
\[
0,\ldots,n-3
\]
输出相同，并在时刻 \(n-2\) 首次不同，所以
\[
m_*(q)\ge n-2.
\]
任意两个状态 \(i<j\) 至迟在时刻 \(i\le n-2\) 首次不同，故
\[
m_*(q)\le n-2.
\]
于是等号成立。\(\square\)

所以必须严格区分：

\[
\boxed{
\text{完成状态数随观察精化单调，}
}
\]
但
\[
\boxed{
\text{完成深度不随观察精化单调。}
}
\]

更细的当前读出可能立刻分离状态，从而缩短所需未来；也可能只暴露一条需要很久才显现的延迟差异，从而增加完成深度。


---

# 23. 追加：预测最小化算法、最短分辨证书与锐性样例

第 19 节给出 \(Z_q\) 的存在性与泛性质，第 22 节给出它在观察精化下的规范结构。本节把这些对象改写成两个有限算法，并给出可由独立检查器验证的局部证书。

固定
\[
|Y|=n,
\qquad
\tau:Y\to Y,
\qquad
q:Y\to O,
\]
并假设 \(O=q(Y)\)。

两个算法回答不同问题：

1. **分区细化算法**直接计算最小完成商 \(Z_q\)；
2. **状态对反向算法**同时计算每一对状态的最早分辨时间。

前者空间线性、适合构造商；后者空间二次、但提供逐对见证与精确 \(m_*\)。

## 23.1 规范分区细化

令
\[
c_0:Y\to C_0
\]
是 \(q\) 的规范类标签，即
\[
c_0(y)=c_0(y')
\iff
q(y)=q(y').
\]
递归定义签名
\[
\boxed{
\operatorname{sig}_{m+1}(y)
=
\bigl(q(y),c_m(\tau y)\bigr),
}
\]
再把相同签名规范重标为
\[
c_{m+1}:Y\to C_{m+1}.
\]

这里“规范重标”只要求
\[
c_{m+1}(y)=c_{m+1}(y')
\iff
\operatorname{sig}_{m+1}(y)
=
\operatorname{sig}_{m+1}(y').
\]
具体整数编号不承载数学意义。

### 定理 23.1（签名标签等于有限未来词分区）

对全部 \(m\ge0\)，
\[
\boxed{
c_m(y)=c_m(y')
\iff
y\equiv_m^q y'.
}
\]
因此算法第一次出现
\[
c_{m+1}\sim c_m
\]
的同一分区时，该 \(m\) 正是稳定深度 \(m_*\)，最终标签集合自然同构于 \(Z_q\)。

### 证明

对 \(m\) 归纳。

当 \(m=0\) 时，
\[
c_0(y)=c_0(y')
\iff
q(y)=q(y'),
\]
正是 \(y\equiv_0^q y'\)。

假设结论对 \(m\) 成立。则
\[
\begin{aligned}
c_{m+1}(y)=c_{m+1}(y')
&\iff
q(y)=q(y')
\ \text{且}\
c_m(\tau y)=c_m(\tau y')\\
&\iff
q(y)=q(y')
\ \text{且}\
q(\tau^{k+1}y)=q(\tau^{k+1}y')
\quad(0\le k\le m)\\
&\iff
q(\tau^k y)=q(\tau^k y')
\quad(0\le k\le m+1)\\
&\iff
y\equiv_{m+1}^q y'.
\end{aligned}
\]
归纳完成。\(\square\)

### 算法 23.A（未来词分区细化）

输入：

- 状态列表 \(Y\)；
- 后继表 \(\tau(y)\)；
- 当前读出 \(q(y)\)。

过程：

1. 按 \(q(y)\) 对状态分组，得到 \(c_0\)；
2. 在第 \(m\) 轮为每个状态计算
   \[
   (q(y),c_m(\tau y));
   \]
3. 对签名排序或哈希，生成 \(c_{m+1}\)；
4. 若新旧分区相同则停止，否则继续。

输出：

- 完成类映射
  \[
  c_*:Y\twoheadrightarrow Z_q;
  \]
- 商转移
  \[
  \overline\tau(c_*(y))=c_*(\tau y);
  \]
- 稳定深度 \(m_*\)。

### 定理 23.2（朴素算法复杂度）

若每轮通过排序 \(n\) 个常数长度签名完成规范重标，则：

\[
\boxed{
\text{轮数}
\le
n-|O|,
}
\]
\[
\boxed{
\text{时间}
=
O\bigl(n(n-|O|+1)\log n\bigr),
}
\]
\[
\boxed{
\text{额外空间}
=
O(n).
}
\]

使用期望常数时间哈希时，期望时间可写为
\[
O\bigl(n(n-|O|+1)\bigr).
\]

### 证明

初始分区有 \(|O|\) 类。每一轮若未停止，分区严格细化，所以类数至少增加一。类数至多为 \(n\)，故严格轮数至多
\[
n-|O|.
\]
每轮计算 \(n\) 个签名并排序，成本 \(O(n\log n)\)；只需保存当前、下一轮标签与签名数组，空间 \(O(n)\)。\(\square\)

该界的轮数部分是锐的：第 22.8 节的根脉冲链恰需要
\[
n-2=n-|O|
\]
轮严格细化。

## 23.2 状态对图与最早分辨时间

定义状态对空间
\[
\mathcal P=Y\times Y
\]
以及确定后继
\[
\boxed{
T(y,y')=(\tau y,\tau y').
}
\]
定义当前失配集合
\[
\boxed{
D_0
=
\{(y,y'):q(y)\ne q(y')\}.
}
\]

对状态对定义扩展自然数值
\[
d_q(y,y')
\in
\mathbb N\cup\{\infty\}
\]
如下：
\[
d_q(y,y')
=
\min\{k\ge0:T^k(y,y')\in D_0\},
\]
若该集合为空则令
\[
d_q(y,y')=\infty.
\]

### 定理 23.3（状态对距离的精确语义）

对任意 \(y,y'\in Y\)：

1. 有
   \[
   \boxed{
   d_q(y,y')<\infty
   }
   \]
   当且仅当两个状态在某个未来时刻可由 \(q\) 分辨；
2. 若有限，则
   \[
   \boxed{
   d_q(y,y')
   =
   \min\{k:q(\tau^k y)\ne q(\tau^k y')\};
   }
   \]
3. 有
   \[
   \boxed{
   d_q(y,y')=\infty
   \iff
   yR_qy';
   }
   \]
4. 若存在至少一对可分辨状态，则
   \[
   \boxed{
   m_*
   =
   \max\{d_q(y,y'):d_q(y,y')<\infty\}.
   }
   \]
   若没有可分辨状态，约定 \(m_*=0\)。

### 证明

由
\[
T^k(y,y')=(\tau^k y,\tau^k y')
\]
直接得到前两项。第三项是
\[
q(\tau^k y)=q(\tau^k y')
\quad(\forall k)
\]
的改写。第四项沿用第 19.5 节的“最晚首次分离时刻”刻画。\(\square\)

## 23.3 反向广度优先搜索

图 \(\mathcal P\) 中每个顶点有唯一正向后继 \(T\)，但可以有多个反向前驱。把全部边反向，从 \(D_0\) 同时开始广度优先搜索。

### 算法 23.B（状态对反向分辨）

1. 建立每个状态的前像表
   \[
   \operatorname{Pred}(z)=\{y:\tau y=z\};
   \]
2. 对每个对 \((z,z')\)，其反向前驱为
   \[
   \operatorname{Pred}(z)\times\operatorname{Pred}(z');
   \]
3. 把 \(D_0\) 中全部状态对以距离 \(0\) 入队；
4. 每当首次访问一个反向前驱，赋距离为当前距离加一；
5. 搜索结束后未访问的状态对标记为 \(\infty\)。

### 定理 23.4（反向 BFS 的正确性与复杂度）

算法 23.B 输出精确的 \(d_q\)。使用显式状态对边表时：

\[
\boxed{
\text{时间}=O(n^2),
\qquad
\text{空间}=O(n^2).
}
\]

### 证明

一个状态对到 \(D_0\) 的长度 \(k\) 正向路径，等价于从 \(D_0\) 到该状态对的长度 \(k\) 反向路径。多源 BFS 对无权图计算最短路径，所以得到最小分辨时刻。

状态对顶点数为 \(n^2\)。每个有序状态对在正向图中只有一条边，故总边数为 \(n^2\)；反向存储不改变总边数。BFS 对每个顶点和边处理常数次。\(\square\)

两个算法的成本结构不同：

- 分区细化只需 \(O(n)\) 空间，并直接产生最小商；
- 状态对算法需 \(O(n^2)\) 空间，但给出每一对状态的最短见证深度。

## 23.4 局部 Bellman 递推证书

扩展自然数上的 \(d_q\) 满足完全局部的递推：

\[
\boxed{
d_q(y,y')
=
\begin{cases}
0,
&
q(y)\ne q(y'),
\\[4pt]
1+d_q(\tau y,\tau y'),
&
q(y)=q(y'),
\ d_q(\tau y,\tau y')<\infty,
\\[4pt]
\infty,
&
q(y)=q(y'),
\ d_q(\tau y,\tau y')=\infty.
\end{cases}
}
\]

### 定理 23.5（局部递推唯一确定最短分辨证书）

设
\[
\delta:Y\times Y\to\mathbb N\cup\{\infty\}
\]
满足上述三分递推，则
\[
\boxed{\delta=d_q.}
\]

### 证明

若从 \((y,y')\) 的正向轨道在第 \(k\) 步首次进入 \(D_0\)，沿递推反向展开恰得到
\[
\delta(y,y')=k.
\]

若正向轨道从不进入 \(D_0\)，由于 \(Y\times Y\) 有限，该轨道最终进入一个全部当前读出相同的循环。若循环上某点被赋有限自然数，沿循环递推一周会得到
\[
a=a+\ell
\]
其中 \(\ell\ge1\)，矛盾。因此循环及其全部前驱只能取 \(\infty\)。这正是 \(d_q\) 的定义。\(\square\)

所以一个独立验证器不必重新运行整个最小化过程。候选证书可以包含：

1. 类标签
   \[
   c:Y\to C;
   \]
2. 状态对距离表
   \[
   \delta:Y\times Y\to\mathbb N\cup\{\infty\}.
   \]

验证器检查：

\[
\boxed{
c(y)=c(y')
\iff
\delta(y,y')=\infty,
}
\]
以及定理 23.5 的局部递推。

### 推论 23.6（线性局部条件给出全局最小性）

若上述检查全部通过，则：

1. \(c\) 的纤维恰为 \(R_q\)-类；
2. 商转移
   \[
   \overline\tau(c(y))=c(\tau y)
   \]
   良定义；
3. \(C\cong Z_q\)；
4. 且
   \[
   \max\{\delta(y,y')<\infty\}=m_*;
   \]
5. 由第 19.4 节的泛性质，该商在全部精确确定性读出保持实现中状态数最小。

验证工作量为
\[
\boxed{O(n^2).}
\]

该证书把“最小”从一个需要信任构造程序的全局结论，转化为可由另一实现逐格核验的局部不动点条件。

## 23.5 最短分辨词的显式见证

对每个有限距离状态对，还可保存见证时刻
\[
k=d_q(y,y')
\]
以及输出失配：
\[
q(\tau^k y)\ne q(\tau^k y').
\]
若希望避免重新计算 \(\tau^k\)，可为每个有限非零距离对保存下一对指针
\[
(y,y')
\mapsto
(\tau y,\tau y')
\]
并检查距离严格减一。沿指针至多 \(k\) 步便到达 \(D_0\)。

于是证书同时提供：

- **不可分证书**：\(\infty\)-状态对集合对 \(T\) 闭合且当前输出一致；
- **可分证书**：有限距离沿 \(T\) 每步减一，最终到达当前失配。

这正对应 greatest-fixed-point 与 least-reachability 两个互补视图：

\[
\boxed{
R_q
=
\nu R.\,
\bigl(\ker q\cap T^{-1}R\bigr),
}
\]
\[
\boxed{
(Y\times Y)\setminus R_q
=
\mu D.\,
\bigl(D_0\cup T^{-1}D\bigr).
}
\]

前者从“永不被分辨”向下闭合，后者从“最终会失配”向上可达；在有限状态对图中二者互为补集。

## 23.6 根脉冲链给出轮数与见证深度的同时锐性

沿用第 22.8 节：
\[
Y_n=\{0,\ldots,n-1\},
\qquad
\tau(i)=\max(i-1,0),
\]
\[
q(0)=1,
\qquad
q(i)=0\ (i>0).
\]

### 定理 23.7（锐性证书）

对 \(0\le i<j\le n-1\)，
\[
\boxed{
d_q(i,j)=i.
}
\]
特别地，
\[
\boxed{
d_q(n-2,n-1)=n-2,
}
\]
故：

1. 分区细化需要恰好 \(n-2\) 轮严格增加；
2. 状态对 BFS 的最大有限距离恰为 \(n-2\)；
3. 一般界
   \[
   m_*\le n-|O|
   \]
   不能统一改进。

### 证明

状态 \(i\) 在时刻 \(0,\ldots,i-1\) 输出 \(0\)，在时刻 \(i\) 首次输出 \(1\)。若 \(i<j\)，状态 \(j\) 在时刻 \(i\) 仍输出 \(0\)，故首次失配时刻恰为 \(i\)。取 \(i=n-2\)、\(j=n-1\) 即得最大值。\(\square\)

## 23.7 算法边界

1. 上述算法针对有限确定性单后继系统；随机核需要概率等价或统计距离，不能把状态对后继写成单值 \(T\)。
2. \(O(n^2)\) 状态对证书适合审计，不表示它总是构造商的最佳算法。
3. 标签整数本身不是规范数学对象；规范对象是标签诱导的分区。
4. 哈希复杂度是期望界；需要完全确定的最坏界时应使用排序或经证明的字典结构。
5. 验证最小商不等于验证论文全部解释性结论；检查器只裁决有限转移、读出、等价类与见证距离。
6. 在 Lean 中应优先形式化数学正确性，再把具体数组实现的复杂度证明作为独立层。


---

# 24. 追加：折扣预测伪度量、有限深度误差与近似对角自然性

精确关系 \(R_q\) 只回答“是否永远不可分”。为了量化两个状态要经过多久才显出差异，并把未稳定的有限词商解释为有误差的预测接口，本节引入折扣未来伪度量。

设输出空间 \(O\) 带有有界伪度量
\[
d_O:O\times O\to\mathbb R_{\ge0},
\]
且
\[
d_O(o,o')\le D
\]
对全部 \(o,o'\) 成立。固定折扣
\[
0<\gamma<1.
\]

定义
\[
\boxed{
d_\gamma(y,y')
=
\sup_{k\ge0}
\gamma^k
d_O\bigl(q(\tau^k y),q(\tau^k y')\bigr).
}
\]

较早出现的差异权重更大；很晚才显现的差异按 \(\gamma^k\) 衰减。

## 24.1 折扣预测伪度量与 Bellman 方程

### 定理 24.1（\(d_\gamma\) 是有界伪度量）

\(d_\gamma\) 满足：

\[
\boxed{
0\le d_\gamma(y,y')\le D,
}
\]
\[
d_\gamma(y,y)=0,
\]
\[
d_\gamma(y,y')=d_\gamma(y',y),
\]
\[
\boxed{
d_\gamma(y,z)
\le
d_\gamma(y,y')+d_\gamma(y',z).
}
\]

### 证明

非负、有界、对称与对角为零逐项继承自 \(d_O\)。

对任意 \(k\)，三角不等式给出
\[
\gamma^k d_O(q\tau^k y,q\tau^k z)
\le
\gamma^k d_O(q\tau^k y,q\tau^k y')
+
\gamma^k d_O(q\tau^k y',q\tau^k z).
\]
对 \(k\) 取上确界，并使用
\[
\sup_k(a_k+b_k)
\le
\sup_k a_k+\sup_k b_k
\]
即得。\(\square\)

### 定理 24.2（Bellman 最大方程）

有
\[
\boxed{
d_\gamma(y,y')
=
\max\left\{
d_O(qy,qy'),
\gamma d_\gamma(\tau y,\tau y')
\right\}.
}
\]

### 证明

定义中的 \(k=0\) 项为
\[
d_O(qy,qy').
\]
其余 \(k\ge1\) 项令 \(j=k-1\)，得到
\[
\sup_{k\ge1}
\gamma^k d_O(q\tau^k y,q\tau^k y')
=
\gamma
\sup_{j\ge0}
\gamma^j
d_O(q\tau^j(\tau y),q\tau^j(\tau y'))
=
\gamma d_\gamma(\tau y,\tau y').
\]
全部项的上确界是两部分的最大值。\(\square\)

这是一条定量化的一步稳定方程。精确同余只记录零集；Bellman 方程同时记录首次差异的尺度。

在全部有界函数
\[
p:Y\times Y\to\mathbb R
\]
上定义算子
\[
\boxed{
(\mathcal Tp)(y,y')
=
\max\left\{
d_O(qy,qy'),
\gamma p(\tau y,\tau y')
\right\}.
}
\]

### 定理 24.3（Bellman 算子的压缩性与唯一不动点）

在一致范数
\[
\|p\|_\infty
=
\max_{y,y'}|p(y,y')|
\]
下，
\[
\boxed{
\|\mathcal Tp-\mathcal Tp'\|_\infty
\le
\gamma\|p-p'\|_\infty.
}
\]
因此 \(\mathcal T\) 有唯一有界不动点，且该不动点正是 \(d_\gamma\)。

### 证明

对固定 \(a\)，实函数
\[
x\mapsto\max\{a,x\}
\]
是 \(1\)-Lipschitz。因此
\[
\begin{aligned}
|(\mathcal Tp)(y,y')-(\mathcal Tp')(y,y')|
&\le
\gamma
|p(\tau y,\tau y')-p'(\tau y,\tau y')|\\
&\le
\gamma\|p-p'\|_\infty.
\end{aligned}
\]
取最大值得压缩界。有限维一致范数空间完备，Banach 不动点定理给出唯一不动点；定理 24.2 已证明 \(d_\gamma\) 是不动点。\(\square\)

## 24.2 有限值迭代与统一误差界

令
\[
p_0=0,
\qquad
p_{m+1}=\mathcal Tp_m.
\]

### 定理 24.4（有限未来截断公式）

对全部 \(m\ge0\)，
\[
\boxed{
p_{m+1}(y,y')
=
\max_{0\le k\le m}
\gamma^k
d_O(q\tau^k y,q\tau^k y').
}
\]
并且
\[
\boxed{
0
\le
d_\gamma(y,y')-p_{m+1}(y,y')
\le
\gamma^{m+1}D.
}
\]

### 证明

第一式对 \(m\) 归纳，使用 Bellman 递推。截断遗漏的全部项满足
\[
\gamma^k d_O(\cdots)
\le
\gamma^kD
\le
\gamma^{m+1}D
\quad(k\ge m+1),
\]
所以完整上确界至多比截断最大值多
\(\gamma^{m+1}D\)。\(\square\)

因此无需等到精确稳定，长度 \(m+1\) 的有限未来已经以统一误差
\[
\boxed{\gamma^{m+1}D}
\]
逼近全部折扣未来几何。

### 推论 24.5（有限词纤维的预测直径）

若
\[
y\equiv_m^q y',
\]
即前 \(m+1\) 个读出完全相同，则
\[
\boxed{
d_\gamma(y,y')
\le
\gamma^{m+1}D.
}
\]

### 证明

前 \(m+1\) 项全部为零，所以定理 24.4 的截断值为零。\(\square\)

这给出第 22.5 节分级商
\[
Z_m=Y/{\equiv_m}
\]
的严格近似含义：每个 \(Z_m\)-纤维的折扣未来直径至多为
\[
\gamma^{m+1}D.
\]
但在 \(m<m_*\) 时，\(Z_m\) 一般仍没有同层闭合转移；小预测直径不自动产生精确同余。

## 24.3 离散输出时的首差异超度量

现在令 \(d_O\) 为离散度量：
\[
d_O(o,o')
=
\begin{cases}
0,&o=o',\\
1,&o\ne o'.
\end{cases}
\]

### 定理 24.6（首差异公式）

若 \(yR_qy'\)，则
\[
d_\gamma(y,y')=0.
\]
若二者可分辨，且
\[
d_q(y,y')
=
\min\{k:q\tau^k y\ne q\tau^k y'\},
\]
则
\[
\boxed{
d_\gamma(y,y')
=
\gamma^{d_q(y,y')}.
}
\]

### 证明

若永不失配，定义中的每项均为零。

若首次失配时刻为 \(d\)，则时刻 \(d\) 的项等于
\[
\gamma^d.
\]
更早项为零，更晚非零项至多为
\[
\gamma^k\le\gamma^{d+1}<\gamma^d.
\]
所以上确界恰为 \(\gamma^d\)。\(\square\)

### 定理 24.7（预测伪超度量）

离散输出下，
\[
\boxed{
d_\gamma(y,z)
\le
\max\{d_\gamma(y,y'),d_\gamma(y',z)\}.
}
\]
所以 \(d_\gamma\) 是伪超度量。

### 证明

对每个 \(k\)，离散度量满足超三角不等式：
\[
d_O(q\tau^k y,q\tau^k z)
\le
\max\{
d_O(q\tau^k y,q\tau^k y'),
d_O(q\tau^k y',q\tau^k z)
\}.
\]
乘以 \(\gamma^k\)、取上确界，并使用有限最大与上确界交换，得到结论。\(\square\)

### 定理 24.8（有限词关系是超度量阈值）

对全部 \(m\ge0\)，
\[
\boxed{
y\equiv_m^q y'
\iff
d_\gamma(y,y')
\le
\gamma^{m+1}.
}
\]

### 证明

若前 \(m+1\) 个读出相同，则首次差异时刻若存在，必满足
\[
d_q(y,y')\ge m+1.
\]
由定理 24.6，
\[
d_\gamma=\gamma^{d_q}\le\gamma^{m+1}.
\]

反之，若在某个 \(k\le m\) 已经失配，则
\[
d_\gamma
\ge
\gamma^k
\ge
\gamma^m
>
\gamma^{m+1},
\]
矛盾。\(\square\)

因此未来词分区恰是超度量球分区，而不是任意聚类：

\[
\boxed{
\equiv_m^q
=
\{d_\gamma\le\gamma^{m+1}\}.
}
\]

若存在可分辨状态对，则
\[
\boxed{
\min\{d_\gamma(y,y')>0\}
=
\gamma^{m_*}.
}
\]
因为最小正距离对应最晚首次分离时刻。

稳定时
\[
\equiv_{m_*}=R_q,
\]
故
\[
\boxed{
R_q
=
\{d_\gamma\le\gamma^{m_*+1}\}.
}
\]
有限系统在稳定层以下形成一个正的谱隙：
\[
0
<
\gamma^{m_*}
\]
把真正不同的预测状态与零距离类分开。

## 24.4 阈值等价不等于同层动力学闭合

伪超度量球关系具有传递性，但它一般不是 \(\tau\)-同余。

由 Bellman 方程，
\[
\gamma d_\gamma(\tau y,\tau y')
\le
d_\gamma(y,y'),
\]
所以
\[
\boxed{
d_\gamma(\tau y,\tau y')
\le
\gamma^{-1}d_\gamma(y,y').
}
\]
距离在前进一步后最多放大 \(\gamma^{-1}\)。

对应到有限词关系：
\[
\boxed{
y\equiv_{m+1}y'
\Longrightarrow
\tau y\equiv_m\tau y'.
}
\]
但一般不能把右侧提升为
\[
\tau y\equiv_{m+1}\tau y'.
\]

所以必须区分：

\[
\boxed{
\text{阈值类是等价类}
}
\]
与
\[
\boxed{
\text{阈值类对动力学前向闭合}.
}
\]

只有当
\[
\equiv_m=\equiv_{m+1}
\]
时，同一阈值层才成为真正的动力学同余。第 22.5 节的跨层映射
\[
Z_{m+1}\to Z_m
\]
正是该尺度放大律的离散形式。

## 24.5 多观察者折扣距离按最大值融合

对两个读出
\[
q_i:Y\to O_i
\]
分别取有界伪度量 \(d_i\)，并在直积输出上取最大伪度量
\[
d_{12}\bigl((o_1,o_2),(o_1',o_2')\bigr)
=
\max\{d_1(o_1,o_1'),d_2(o_2,o_2')\}.
\]
相应折扣距离记为
\[
d_\gamma^{(1)},
\quad
d_\gamma^{(2)},
\quad
d_\gamma^{(12)}.
\]

### 定理 24.9（传感器融合的最大距离公式）

有
\[
\boxed{
d_\gamma^{(12)}(y,y')
=
\max\{
d_\gamma^{(1)}(y,y'),
d_\gamma^{(2)}(y,y')
\}.
}
\]

### 证明

逐定义：
\[
\begin{aligned}
d_\gamma^{(12)}(y,y')
&=
\sup_k
\gamma^k
\max\{
d_1(q_1\tau^k y,q_1\tau^k y'),
d_2(q_2\tau^k y,q_2\tau^k y')
\}\\
&=
\max\left\{
\sup_k\gamma^k d_1(q_1\tau^k y,q_1\tau^k y'),
\sup_k\gamma^k d_2(q_2\tau^k y,q_2\tau^k y')
\right\}.
\end{aligned}
\]
\(\square\)

零核随之满足
\[
\ker d_\gamma^{(12)}
=
\ker d_\gamma^{(1)}
\cap
\ker d_\gamma^{(2)},
\]
这正是定理 22.11 的定量提升。

## 24.6 近似半共轭与轨道误差传播

精确完成要求
\[
\pi\tau=\sigma\pi.
\]
现在允许该方程具有统一误差。

设 \((Z,d_Z)\) 为度量空间，
\[
\pi:Y\to Z,
\qquad
\sigma:Z\to Z.
\]
定义转移缺陷
\[
\boxed{
\delta(\pi;\tau,\sigma)
=
\max_{y\in Y}
d_Z\bigl(\pi(\tau y),\sigma(\pi y)\bigr).
}
\]
假设 \(\sigma\) 是 \(L\)-Lipschitz：
\[
d_Z(\sigma z,\sigma z')
\le
L\,d_Z(z,z').
\]

### 定理 24.10（近似半共轭的有限时域误差）

对全部 \(k\ge0\) 与 \(y\in Y\)，
\[
\boxed{
d_Z\bigl(\pi(\tau^k y),\sigma^k(\pi y)\bigr)
\le
\delta
\sum_{j=0}^{k-1}L^j.
}
\]
其中 \(k=0\) 时空和为 \(0\)。

特别地：

- 若 \(0\le L<1\)，则
  \[
  \boxed{
  d_Z(\pi\tau^k y,\sigma^k\pi y)
  \le
  \frac{\delta}{1-L};
  }
  \]
- 若 \(L=1\)，则
  \[
  \boxed{
  d_Z(\pi\tau^k y,\sigma^k\pi y)
  \le
  k\delta.
  }
  \]

### 证明

令
\[
e_k(y)
=
d_Z(\pi\tau^k y,\sigma^k\pi y).
\]
有 \(e_0=0\)，且
\[
\begin{aligned}
e_{k+1}(y)
&=
d_Z(\pi\tau(\tau^k y),\sigma(\sigma^k\pi y))\\
&\le
d_Z(\pi\tau(\tau^k y),\sigma\pi(\tau^k y))
+
d_Z(\sigma\pi(\tau^k y),\sigma(\sigma^k\pi y))\\
&\le
\delta+Le_k(y).
\end{aligned}
\]
递归展开即得几何和。\(\square\)

再设输出空间 \((O,d_O)\)，原读出
\[
q:Y\to O,
\]
抽象读出
\[
o:Z\to O.
\]
定义当前读出误差
\[
\boxed{
\eta
=
\max_{y\in Y}
d_O(q(y),o(\pi y)).
}
\]
假设 \(o\) 是 \(M\)-Lipschitz。

### 推论 24.11（输出轨迹误差）

对全部 \(k\ge0\)，
\[
\boxed{
d_O\bigl(q(\tau^k y),o(\sigma^k\pi y)\bigr)
\le
\eta
+
M\delta\sum_{j=0}^{k-1}L^j.
}
\]

### 证明

在两端之间插入
\[
o(\pi\tau^k y)
\]
并使用当前读出误差与 \(o\) 的 Lipschitz 界。\(\square\)

这条公式严格区分两个误差源：

\[
\boxed{
\text{当前读出逼近误差 }\eta
}
\]
与
\[
\boxed{
\text{动力学交换缺陷 }\delta.
}
\]

即使 \(\eta=0\)，非零 \(\delta\) 仍可随时间积累；即使 \(\delta=0\)，抽象读出也可能有固定偏差 \(\eta\)。

## 24.7 近似对角自然性的精确缺陷

取任意非空地址集 \(A\)。对评价表
\[
E:A\times A\to Y
\]
定义逐点投影
\[
P_\pi(E)(a,b)=\pi(E(a,b)),
\]
对输出
\[
u:A\to Y
\]
定义
\[
Q_\pi(u)(a)=\pi(u(a)).
\]

令
\[
\Delta_\tau(E)(a)=\tau(E(a,a)),
\]
\[
\Delta_\sigma(F)(a)=\sigma(F(a,a)).
\]

### 定理 24.12（对角自然性缺陷等于半共轭缺陷）

对每个 \(E\) 与 \(a\in A\)，
\[
\boxed{
d_Z\left(
Q_\pi\Delta_\tau(E)(a),
\Delta_\sigma P_\pi(E)(a)
\right)
\le
\delta.
}
\]
并且
\[
\boxed{
\sup_E\sup_{a\in A}
d_Z\left(
Q_\pi\Delta_\tau(E)(a),
\Delta_\sigma P_\pi(E)(a)
\right)
=
\delta.
}
\]

### 证明

逐坐标有
\[
\begin{aligned}
d_Z(
Q_\pi\Delta_\tau(E)(a),
\Delta_\sigma P_\pi(E)(a))
&=
d_Z(
\pi\tau(E(a,a)),
\sigma\pi(E(a,a)))\\
&\le\delta.
\end{aligned}
\]
由于 \(Y\) 有限，存在 \(y_*\) 取得最大缺陷。取一个评价表使某个对角元等于 \(y_*\)，即可达到 \(\delta\)。\(\square\)

所以精确自然性不是独立于半共轭的额外条件：

\[
\boxed{
\delta=0
\iff
Q_\pi\Delta_\tau
=
\Delta_\sigma P_\pi.
}
\]

而在近似层，
\[
\delta
\]
正是全部地址表上的最坏对角自然性误差。

## 24.8 近似翻译的复合误差

设
\[
(Y,\tau)
\overset{\pi}{\longrightarrow}
(Z,\sigma)
\overset{\rho}{\longrightarrow}
(W,\omega).
\]
记两步缺陷为
\[
\delta_1
=
\max_y d_Z(\pi\tau y,\sigma\pi y),
\]
\[
\delta_2
=
\max_z d_W(\rho\sigma z,\omega\rho z).
\]
假设
\[
\rho:(Z,d_Z)\to(W,d_W)
\]
是 \(K\)-Lipschitz。

### 定理 24.13（近似半共轭复合）

复合映射
\[
\rho\pi:Y\to W
\]
满足
\[
\boxed{
\delta(\rho\pi;\tau,\omega)
\le
K\delta_1+\delta_2.
}
\]

### 证明

对任意 \(y\)，
\[
\begin{aligned}
d_W(\rho\pi\tau y,\omega\rho\pi y)
&\le
d_W(\rho\pi\tau y,\rho\sigma\pi y)
+
d_W(\rho\sigma\pi y,\omega\rho\pi y)\\
&\le
K\,d_Z(\pi\tau y,\sigma\pi y)+\delta_2\\
&\le
K\delta_1+\delta_2.
\end{aligned}
\]
取最大值。\(\square\)

若 \(\rho\) 是等距嵌入，则 \(K=1\)，误差按
\[
\boxed{\delta_1+\delta_2}
\]
相加。这与仓库既有近似命名翻译“语义误差相加、资源模数复合”的结构一致，但这里的对象是动力学半共轭与对角自然性，不应把两个定理视为同一个已形式化声明。

## 24.9 定量近似的严格边界

1. 小的 \(\delta\) 只给出有限时域或在 \(L<1\) 时的统一轨道控制；若 \(L\ge1\)，误差可以线性或指数增长。
2. 小的纤维直径不保证商转移良定义。精确同余要求零缺陷，而不是“足够小”这一非结构条件。
3. 对一般伪度量输出，\(d_\gamma=0\) 只表示全部未来输出落在 \(d_O\) 的零距离类中；只有当 \(d_O\) 分离点时才等价于 \(R_q\)。
4. 离散输出时阈值关系是超度量等价；一般度量下，任意阈值关系
   \[
   d_\gamma\le\varepsilon
   \]
   未必传递。
5. 覆盖数、聚类数或低维嵌入本身不证明近似动力学自然；必须直接审计 \(\delta\)。
6. 本节没有把行为伪度量等同于量子态距离，也没有从折扣参数 \(\gamma\) 推出物理时间常数。


---

# 25. 追加：带输入系统的行为完成、干预自然性与反馈闭包

第 21 节指出：持续外界输入会破坏有限自治系统的最终周期结论。但“轨迹不再自治”不等于“最小预测状态无法定义”。本节把第 19 节从单一自映射推广到有限输入族，得到一个对全部干预词统一有效的最小行为完成。

固定非空有限集合：

\[
Y=\text{状态空间},
\qquad
U=\text{输入字母表},
\qquad
O=\text{读出集合}.
\]

对每个输入 \(u\in U\)，给定转移
\[
F_u:Y\to Y,
\]
并给定 Moore 型当前读出
\[
q:Y\to O.
\]
以下把 \(O\) 替换为实际像 \(q(Y)\)，所以
\[
|O|=|q(Y)|.
\]

对有限输入词
\[
w=u_1u_2\cdots u_k\in U^*
\]
定义
\[
F_\varepsilon=\mathrm{id}_Y,
\]
\[
F_w
=
F_{u_k}\circ\cdots\circ F_{u_1}.
\]
即输入按从左到右的时间顺序施加。

## 25.1 有限输入词等价

对 \(m\ge0\)，定义
\[
y\equiv_m^U y'
\]
当且仅当对全部长度至多为 \(m\) 的输入词，
\[
\boxed{
q(F_wy)=q(F_wy')
\quad
(|w|\le m).
}
\]
定义完全行为等价
\[
\boxed{
y\equiv_\infty^U y'
\iff
q(F_wy)=q(F_wy')
\quad
\text{对全部 }w\in U^*.
}
\]

令
\[
R_m^U=\equiv_m^U,
\qquad
R_\infty^U=\equiv_\infty^U.
\]

### 定理 25.1（受控行为关系递推）

有
\[
\boxed{
R_0^U=\ker q,
}
\]
\[
\boxed{
R_{m+1}^U
=
\ker q
\cap
\bigcap_{u\in U}
(F_u\times F_u)^{-1}(R_m^U).
}
\]

### 证明

长度至多 \(m+1\) 的词分为：

- 空词 \(\varepsilon\)，要求当前读出相同；
- 以某个 \(u\in U\) 开头的非空词 \(uw\)，其中 \(|w|\le m\)。

对第二类，
\[
q(F_{uw}y)=q(F_w(F_uy)).
\]
所以全部此类词读出相同，当且仅当
\[
F_uy\,R_m^U\,F_uy'
\quad
\text{对全部 }u\in U.
\]
与当前读出条件合并即得。\(\square\)

在关系格上定义
\[
\boxed{
\Phi_U(R)
=
\ker q
\cap
\bigcap_{u\in U}
(F_u\times F_u)^{-1}(R).
}
\]
则
\[
R_{m+1}^U=\Phi_U(R_m^U).
\]

### 定理 25.2（一次稳定、最大共同同余与有限界）

若
\[
R_m^U=R_{m+1}^U,
\]
则
\[
\boxed{
R_{m+r}^U=R_m^U
\quad
(r\ge0).
}
\]
并且
\[
\boxed{
R_\infty^U
=
\nu R.\,\Phi_U(R),
}
\]
即 \(R_\infty^U\) 是包含于 \(\ker q\)、并对每个 \(F_u\) 前向稳定的最大等价关系。

若
\[
c_m=|Y/R_m^U|,
\]
则最小稳定深度 \(m_*^U\) 满足
\[
\boxed{
m_*^U
\le
|Y/R_\infty^U|-|O|
\le
|Y|-|O|.
}
\]

### 证明

若 \(R_m^U\) 是 \(\Phi_U\) 的不动点，则对每个 \(u\)，
\[
yR_m^Uy'
\Longrightarrow
F_uyR_m^UF_uy'.
\]
对任意输入词反复应用，得到全部更长词也不能细化该关系，所以永久稳定。

若 \(S\subseteq\ker q\) 且对全部 \(F_u\) 稳定，则
\[
ySy'
\Longrightarrow
F_wy\,S\,F_wy'
\]
对全部词 \(w\) 成立，继而全部读出相同，所以
\[
S\subseteq R_\infty^U.
\]
最大性得证。

商类数从 \(|O|\) 开始非降，每次严格细化至少增加一类，且最终类数为
\[
|Y/R_\infty^U|,
\]
故得到稳定界。\(\square\)

自治系统是
\[
|U|=1
\]
的特殊情形。输入族并没有改变有限下降的逻辑，只把一个同余条件替换为“对全部干预共同稳定”。

## 25.2 最小受控行为完成

定义
\[
\boxed{
Z_{q,U}=Y/R_\infty^U,
\qquad
\pi_{q,U}:Y\twoheadrightarrow Z_{q,U}.
}
\]
对每个 \(u\in U\)，定义商转移
\[
\boxed{
\overline F_u([y])=[F_uy].
}
\]
定义商读出
\[
\overline q([y])=q(y).
\]
由共同同余性，这些映射良定义，并满足
\[
\boxed{
\pi_{q,U}F_u
=
\overline F_u\pi_{q,U}
\quad(\forall u\in U),
}
\]
\[
\boxed{
q=\overline q\,\pi_{q,U}.
}
\]

### 定理 25.3（最小 Moore 行为实现的泛性质）

设另一个受控实现由满射
\[
r:Y\twoheadrightarrow W
\]
以及转移
\[
G_u:W\to W
\quad(u\in U)
\]
和读出
\[
o:W\to O
\]
给出，满足
\[
\boxed{
rF_u=G_ur
\quad(\forall u\in U),
}
\]
\[
\boxed{
q=or.
}
\]
则存在唯一满射
\[
\boxed{
h:W\twoheadrightarrow Z_{q,U}
}
\]
使
\[
\boxed{
\pi_{q,U}=hr,
}
\]
\[
\boxed{
hG_u=\overline F_uh
\quad(\forall u\in U),
}
\]
\[
\boxed{
\overline qh=o.
}
\]
特别地，
\[
\boxed{
|Z_{q,U}|\le|W|.
}
\]

### 证明

若 \(r(y)=r(y')\)，则对任意词 \(w\)，由转移交换性反复得到
\[
r(F_wy)=r(F_wy').
\]
再由 \(q=or\)，
\[
q(F_wy)=q(F_wy').
\]
所以
\[
\ker r\subseteq R_\infty^U.
\]
于是 \(\pi_{q,U}\) 在 \(r\)-纤维上常值，唯一因子化为
\[
\pi_{q,U}=hr.
\]
两者满射推出 \(h\) 满射。其余交换式在 \(r(Y)=W\) 上逐点验证。\(\square\)

所以 \(Z_{q,U}\) 是保留**全部可能输入干预下的全部未来读出**所需的最小状态，而不是只对某一条固定输入轨迹最小。

## 25.3 受控分区细化算法

取当前类标签
\[
c_0(y)=q(y)
\]
的规范重标。递归定义
\[
\boxed{
\operatorname{sig}_{m+1}(y)
=
\left(
q(y),
\bigl(c_m(F_uy)\bigr)_{u\in U}
\right).
}
\]
对相同签名重新编号得到 \(c_{m+1}\)。

### 定理 25.4（受控签名算法正确性）

对全部 \(m\ge0\)，
\[
\boxed{
c_m(y)=c_m(y')
\iff
yR_m^Uy'.
}
\]
因此算法在 \(m_*^U\) 轮稳定，并输出 \(Z_{q,U}\)。

### 证明

对 \(m\) 归纳。归纳步中，签名相同当且仅当当前读出相同，并且对每个 \(u\)，后继状态在 \(R_m^U\) 下等价；由定理 25.1 正是 \(R_{m+1}^U\)。\(\square\)

若 \(|U|=a\)，每轮对每个状态读取 \(a\) 个后继类。通过排序规范化，朴素复杂度为
\[
\boxed{
O\bigl(
a\,n(n-|O|+1)\log n
\bigr)
}
\]
时间与
\[
\boxed{O(an)}
\]
签名空间；若输入枚举固定，可把额外工作空间实现为 \(O(n)\) 加流式签名比较。

## 25.4 状态对干预图与最短分辨词

在状态对空间 \(Y\times Y\) 上，对每个输入 \(u\) 建立边
\[
\boxed{
(y,y')
\overset{u}{\longrightarrow}
(F_uy,F_uy').
}
\]
当前失配集仍为
\[
D_0=\{(y,y'):q(y)\ne q(y')\}.
\]

定义
\[
d_U(y,y')
=
\min\{
|w|:
q(F_wy)\ne q(F_wy')
\},
\]
若不存在分辨词则记为 \(\infty\)。

### 定理 25.5（最短干预见证）

有
\[
\boxed{
d_U(y,y')=\infty
\iff
yR_\infty^Uy'.
}
\]
若存在可分辨状态对，则
\[
\boxed{
m_*^U
=
\max\{d_U(y,y')<\infty\}.
}
\]

### 证明

定义直接说明 \(\infty\) 等价于全部输入词读出相同。深度 \(m\) 关系正是“没有长度至多 \(m\) 的分辨词”，所以最晚的最短分辨词长度等于稳定深度。\(\square\)

从 \(D_0\) 在全部带标签边上做反向 BFS，可计算每个状态对到失配集的最短路径，并保存产生该前驱的输入标签。于是每个有限距离对都得到一个显式最短输入词见证。

### 定理 25.6（受控状态对算法复杂度）

显式构造全部状态对—输入边时：

\[
\boxed{
\text{时间}
=
O(|U|\,n^2),
}
\]
\[
\boxed{
\text{空间}
=
O(|U|\,n^2)
}
\]
用于完整反向边表；若按输入与前像表即时枚举，可在具体结构允许时降低常数或存储，但不改变最坏状态对规模。

## 25.5 干预族上的对角自然性

对每个 \(u\in U\)，把 \(F_u\) 看作一个扭曲。对任意地址集 \(A\)，定义
\[
\Delta_{F_u}(E)(a)=F_u(E(a,a)).
\]

### 定理 25.7（全部干预同时自然下降）

对联合完成投影 \(\pi=\pi_{q,U}\)，逐点定义 \(P_\pi,Q_\pi\)。则对全部 \(u\in U\)，
\[
\boxed{
Q_\pi\Delta_{F_u}
=
\Delta_{\overline F_u}P_\pi.
}
\]

### 证明

逐坐标：
\[
\begin{aligned}
Q_\pi\Delta_{F_u}(E)(a)
&=
\pi(F_u(E(a,a)))\\
&=
\overline F_u(\pi(E(a,a)))\\
&=
\Delta_{\overline F_u}P_\pi(E)(a).
\end{aligned}
\]
\(\square\)

### 定理 25.8（干预自然性的最小性反向判据）

设满射
\[
r:Y\twoheadrightarrow W
\]
保留原读出：
\[
q=or.
\]
若对每个 \(u\in U\) 存在
\[
G_u:W\to W
\]
使对任意非空地址集与任意评价表都有
\[
\boxed{
Q_r\Delta_{F_u}
=
\Delta_{G_u}P_r,
}
\]
则
\[
rF_u=G_ur
\quad(\forall u),
\]
并存在唯一满射
\[
W\twoheadrightarrow Z_{q,U}.
\]

### 证明

取单点地址集 \(A=\{*\}\)，令
\[
E(*,*)=y.
\]
对角自然性给出
\[
r(F_uy)=G_u(r(y))
\]
对全部 \(y,u\) 成立。随后应用定理 25.3。\(\square\)

所以受控预测完成同时具有三种等价角色：

\[
\boxed{
\text{全部输入词的最小行为状态},
}
\]
\[
\boxed{
\text{包含于 }\ker q\text{ 的最大共同同余},
}
\]
\[
\boxed{
\text{使全部干预对角同时自然下降的最小商}.
}
\]

## 25.6 反馈策略在完成上的闭合

设策略只依赖完成状态：
\[
\kappa:Z_{q,U}\to U.
\]
定义原系统上的闭环转移
\[
\boxed{
\tau_\kappa(y)
=
F_{\kappa(\pi y)}(y),
}
\]
以及完成上的闭环转移
\[
\boxed{
\overline\tau_\kappa(z)
=
\overline F_{\kappa(z)}(z).
}
\]

### 定理 25.9（预测完成对状态反馈充分）

有
\[
\boxed{
\pi\tau_\kappa
=
\overline\tau_\kappa\pi.
}
\]

### 证明

对任意 \(y\)，
\[
\begin{aligned}
\pi\tau_\kappa(y)
&=
\pi F_{\kappa(\pi y)}(y)\\
&=
\overline F_{\kappa(\pi y)}(\pi y)\\
&=
\overline\tau_\kappa(\pi y).
\end{aligned}
\]
\(\square\)

因此任意只读取最小行为状态的确定反馈策略，都能在完成上无损执行。特别地，任何只依赖当前原读出 \(q(y)\) 的策略也包含在内，因为
\[
q=\overline q\,\pi.
\]

严格边界是：若控制器使用被 \(\pi\) 删除的微观信息，即策略
\[
\kappa_{\mathrm{micro}}:Y\to U
\]
不在 \(\pi\)-纤维上常值，则一般不存在 \(Z_{q,U}\) 上的对应策略。最小行为状态对“所有可观察反馈”充分，不对“使用隐藏状态的特权控制器”充分。

## 25.7 有限状态加外部输入不保证最终周期

有限自治映射最终周期；有限受控系统在任意外部输入流下不必最终周期。

### 例 25.10（输入复制系统）

令
\[
Y=U=O=\{0,1\},
\]
\[
F_u(y)=u,
\qquad
q(y)=y.
\]
对输入流
\[
u_0,u_1,u_2,\ldots
\]
有
\[
y_{t+1}=u_t,
\]
所以
\[
q(y_{t+1})=u_t.
\]

若输入流不是最终周期，例如取
\[
u_t=
\begin{cases}
1,&t\text{ 是 }2\text{ 的幂},\\
0,&\text{否则},
\end{cases}
\]
则输出也不是最终周期，尽管状态空间只有两个元素。

这不与第 21.2 节矛盾，因为这里不存在单一闭合自映射
\[
Y\to Y;
\]
每一步使用的转移由新的外部输入选择。

### 定理 25.11（有限输入生成器恢复自治周期性）

若输入由有限确定性生成器
\[
C\to C,
\qquad
g:C\to U
\]
产生，则扩展状态
\[
\widetilde Y=Y\times C
\]
上的更新
\[
\widetilde\tau(y,c)
=
(F_{g(c)}y,Jc)
\]
是有限自治映射。因此每条扩展轨迹最终周期。

### 证明

\(\widetilde Y\) 有限，\(\widetilde\tau\) 单值。应用定理 21.2。\(\square\)

所以“输入打破周期”必须继续区分：

\[
\boxed{
\text{新外部输入流}
}
\]
与
\[
\boxed{
\text{有限内部控制器状态的展开}.
}
\]

## 25.8 受控完成的严格边界

1. 本节假设 \(U\) 有限，因而签名可有限枚举；无限输入族仍可定义共同同余，但算法需要额外有效性条件。
2. 本节是 Moore 型读出。若输出依赖状态—输入对，应改用 Mealy 型行为等价，不能直接复用当前递推。
3. 随机转移核需要概率双模拟、分布距离或统计实验等价；确定关系交不足以表达概率差异。
4. \(Z_{q,U}\) 对全部输入词最小，不表示它对某个固定策略已经最小；策略固定后还可再次对闭环系统做更粗最小化。
5. 对所有干预自然下降不等于干预在物理上可实施；数学输入字母只编码已声明的转移族。
6. 本节没有把外界输入等同于 Gödel 意义的“系统外真理”，也没有从非周期输入推出无限状态本体。


---

# 26. 追加：普通逆极限只保留周期核——过去完成与分支完成的严格分家

第 3 节把严格自然族下降到逆极限；第 17 节又用有限深度前像树的 projective completion 恢复完整函数图。二者容易被误读为“对同一个动力学不断向过去取逆极限，就能恢复全部瞬态分支”。

本节证明该推断为假。

对有限自映射
\[
\tau:Y\to Y,
\]
普通状态逆极限
\[
\varprojlim(Y,\tau)
\]
只保留周期核；所有有限瞬态入树都被删除。第 17 节之所以能恢复分支，是因为它取极限的对象不是单个前驱状态，而是“全部前驱子树的有限深度编码”。

## 26.1 普通状态逆极限

定义
\[
\boxed{
X_\tau^-
=
\left\{
(x_0,x_1,x_2,\ldots)\in Y^{\mathbb N}:
\tau(x_{k+1})=x_k
\ \forall k\ge0
\right\}.
}
\]
这是常逆系
\[
\cdots
\overset{\tau}{\longrightarrow}
Y
\overset{\tau}{\longrightarrow}
Y
\overset{\tau}{\longrightarrow}
Y
\]
的逆极限。

令周期核为
\[
P_\tau
=
\{y\in Y:\exists n\ge1,\ \tau^ny=y\}.
\]

### 定理 26.1（有限自映射的逆极限—周期核定理）

坐标投影
\[
p_0:X_\tau^-\to Y,
\qquad
p_0((x_k)_k)=x_0
\]
的像恰为 \(P_\tau\)，并且
\[
\boxed{
p_0:X_\tau^-\xrightarrow{\ \cong\ }P_\tau
}
\]
是双射。

因此
\[
\boxed{
|X_\tau^-|=|P_\tau|.
}
\]

### 证明

先取
\[
x=(x_0,x_1,\ldots)\in X_\tau^-.
\]
由于 \(Y\) 有限，序列中存在
\[
0\le i<j
\]
使
\[
x_i=x_j.
\]
兼容性给出
\[
\tau^{j-i}(x_j)=x_i.
\]
结合 \(x_i=x_j\)，得到
\[
\tau^{j-i}(x_i)=x_i,
\]
所以 \(x_i\) 是周期点。又
\[
x_0=\tau^i(x_i),
\]
周期轨道的正向像仍在同一周期上，故 \(x_0\in P_\tau\)。因此
\[
p_0(X_\tau^-)\subseteq P_\tau.
\]

反之，\(\tau\) 在 \(P_\tau\) 上是置换。对任意 \(p\in P_\tau\)，定义
\[
x_k=(\tau|_{P_\tau})^{-k}(p).
\]
则
\[
\tau(x_{k+1})=x_k,
\]
所以 \((x_k)_k\in X_\tau^-\) 且 \(p_0(x)=p\)。得到满射到 \(P_\tau\)。

最后证明唯一性。任意兼容序列的尾部
\[
(x_k,x_{k+1},\ldots)
\]
仍是无限兼容序列；重复上面的有限性论证，得到每个 \(x_k\in P_\tau\)。而 \(\tau|_{P_\tau}\) 是双射，所以
\[
x_{k+1}
=
(\tau|_{P_\tau})^{-1}(x_k)
\]
被 \(x_k\) 唯一决定。于是整个序列由 \(x_0\) 唯一确定。\(\square\)

普通逆极限没有保存“周期点有哪些瞬态前像”。它只沿周期上的唯一可无限延伸前驱继续。

## 26.2 自然扩张仍只是周期置换

在 \(X_\tau^-\) 上定义右移
\[
S^-(x_0,x_1,x_2,\ldots)
=
(x_1,x_2,x_3,\ldots).
\]
在定理 26.1 的同构下，
\[
\boxed{
S^-
\cong
(\tau|_{P_\tau})^{-1}.
}
\]

也可定义自然扩张
\[
\widehat\tau(x_0,x_1,x_2,\ldots)
=
(\tau x_0,x_0,x_1,\ldots),
\]
则
\[
\boxed{
\widehat\tau
\cong
\tau|_{P_\tau}.
}
\]

所以有限系统的普通自然扩张没有把非可逆瞬态动力学变成一个包含全部历史的可逆系统；它先删除全部不能无限向后延伸的瞬态点，再把剩余周期置换可逆化。

## 26.3 瞬态点为何不能拥有无限过去

对任意 \(y\in Y\)，定义前像树层
\[
\operatorname{Pred}_k(y)
=
\{x\in Y:\tau^kx=y\}.
\]
瞬态点可以有许多有限深度前像，但不能位于一条无限相容前驱链上。

### 推论 26.2（无限过去存在当且仅当当前点周期）

下列条件等价：

1. 存在
   \[
   x_1,x_2,\ldots
   \]
   使
   \[
   \tau x_1=y,
   \qquad
   \tau x_{k+1}=x_k;
   \]
2. \(y\in P_\tau\)。

所以
\[
\boxed{
\text{任意长的非空前像层}
}
\]
与
\[
\boxed{
\text{存在一条无限相容前像链}
}
\]
在有限系统中最终等价于周期性，而不等价于“前像分支丰富”。

## 26.4 与第 17 节分支完成的非交换性

第 17 节定义的递归分支码
\[
\mathcal C_\tau^{(h)}(y)
\]
在深度 \(h\) 记录的是**所有非周期前像子节点及其子树多重集**。其 projective limit 恢复完整装饰 necklace：
\[
\varprojlim_h\mathfrak N_h(\tau)
\cong
\mathfrak N(\tau).
\]

普通状态逆极限却只选择一个状态序列：
\[
x_0\leftarrow x_1\leftarrow x_2\leftarrow\cdots.
\]
它没有在每层保留全部前驱集合，更没有保留各分支之间的多重集关联。

因此存在两个不同的“向过去完成”：

### 路径型过去完成

\[
\boxed{
X_\tau^-
=
\varprojlim(Y,\tau)
\cong
P_\tau.
}
\]

它询问：哪些当前点具有一条无限相容过去？

### 分支型过去完成

\[
\boxed{
\varprojlim_h
\{\text{深度 }h\text{ 的完整前像树码}\}
\cong
\mathfrak N(\tau).
}
\]

它询问：所有有限深度过去分支如何兼容组成完整函数图？

### 定理 26.3（取路径极限与保存分支不交换）

若 \(\tau\) 有非空瞬态部分，则普通状态逆极限不能恢复完整函数图。更精确地：

\[
\boxed{
X_\tau^-
\text{ 只由 }
\tau|_{P_\tau}
\text{ 决定};
}
\]
而
\[
\boxed{
\mathfrak N(\tau)
\text{ 还依赖附着于周期核的全部瞬态入树}.
}
\]

所以可以存在两个非共轭有限自映射 \(\tau,\sigma\)，满足

\[
P_\tau\cong P_\sigma
\]
且周期置换相同，从而
\[
X_\tau^-\cong X_\sigma^-,
\]
但
\[
\mathfrak N(\tau)\ne\mathfrak N(\sigma).
\]

### 证明

第一项由定理 26.1。第二项由定理 17.4 的装饰 necklace 完全分类。取任意相同周期而附着不同非同构入树的两个函数图，即得反例。\(\square\)

这给出严格分家：

\[
\boxed{
\text{先把过去压成一条兼容路径再取极限}
\ne
\text{先保存每层全部分支再取极限}.
}
\]

## 26.5 未来预测完成保留瞬态可分辨性

未来完成
\[
Z_q=Y/R_q
\]
与普通过去逆极限有相反的瞬态行为。

未来读出词
\[
q(y),q(\tau y),q(\tau^2y),\ldots
\]
可以在状态进入周期核以前读取其瞬态位置。因此只要 \(q\) 足够细，\(Z_q\) 可以保留全部瞬态状态。

### 定理 26.4（恒等读出的最大未来完成）

取
\[
q=\mathrm{id}_Y.
\]
则
\[
\boxed{
R_q=\Delta_Y,
\qquad
Z_q\cong Y.
}
\]
而普通过去逆极限仍满足
\[
\boxed{
X_\tau^-\cong P_\tau.
}
\]

若 \(\tau\) 非置换，则
\[
|P_\tau|<|Y|,
\]
所以
\[
\boxed{
|X_\tau^-|
<
|Z_{\mathrm{id}}|.
}
\]

### 证明

恒等读出在时刻 \(0\) 已经分离不同状态，所以预测等价就是相等。其余由定理 26.1。\(\square\)

### 例 26.5（根链的最大分离）

令
\[
Y_n=\{0,\ldots,n-1\},
\qquad
\tau(i)=\max(i-1,0).
\]
周期核只有
\[
P_\tau=\{0\},
\]
所以
\[
\boxed{
|X_\tau^-|=1.
}
\]
对恒等读出，
\[
\boxed{
|Z_{\mathrm{id}}|=n.
}
\]
对第 22.8 节的根脉冲读出，同样有
\[
\boxed{
|Z_q|=n.
}
\]

因此一个系统可以在过去路径逆极限中完全塌成单点，却在未来观察完成中保留全部 \(n\) 个状态。

## 26.6 双向轨迹只存在于周期核

定义双向轨迹
\[
(x_t)_{t\in\mathbb Z}
\]
满足
\[
\tau(x_t)=x_{t+1}
\quad
\text{对全部 }t\in\mathbb Z.
\]

### 定理 26.6（有限系统的双向轨迹定理）

任意双向轨迹的全部状态都属于 \(P_\tau\)。反之，每个周期点都位于唯一的双向周期轨迹中。

### 证明

负时间部分给出每个 \(x_t\) 的无限相容过去。由推论 26.2，\(x_t\in P_\tau\)。在周期核上 \(\tau\) 是置换，故正反两个时间方向都唯一。\(\square\)

因此若要为瞬态点赋予“双向历史”，必须添加原系统之外的数据，例如：

- 一个有限起始边界；
- 外部生成的过去输入；
- 分支树而非单路径；
- 或扩展状态，使原瞬态成为更大系统中的周期/可逆部分。

不能仅凭普通逆极限声称有限不可逆系统的全部状态已经获得时间对称历史。

## 26.7 与观察者完成的方向性审计

一个完整观察者理论必须单独记录以下三个对象：

\[
\boxed{
\text{未来 itinerary 完成 }Z_q,
}
\]
\[
\boxed{
\text{单路径过去逆极限 }X_\tau^-,
}
\]
\[
\boxed{
\text{全分支过去完成 }\mathfrak N(\tau).
}
\]

它们分别保存：

- \(Z_q\)：相对于 \(q\) 的全部未来可预测差异；
- \(X_\tau^-\)：可以无限向后延伸的周期轨迹；
- \(\mathfrak N(\tau)\)：周期与全部瞬态入树的完整关联。

三者一般互不等价。特别地：

\[
\boxed{
Z_q
\text{ 相对读出，}
}
\]
\[
\boxed{
X_\tau^-
\text{ 忘掉全部有限瞬态，}
}
\]
\[
\boxed{
\mathfrak N(\tau)
\text{ 是观察者无关的完整有限函数图不变量。}
}
\]

## 26.8 严格边界

1. 定理 26.1 依赖 \(Y\) 有限。无限状态系统可以有非周期点却拥有无限前史。
2. 普通逆极限只保留一条相容路径；它不应被口语化为“全部可能过去的集合”而忽略分支关联。
3. 分支码完成恢复的是有限函数图组合类型，不自动赋予每条分支概率、物理实在性或量子振幅。
4. 未来完成 \(Z_q\) 依赖读出 \(q\)；恒等读出恢复 \(Y\) 不表示任意现实观察者都能读取微观状态。
5. 双向轨迹定理不证明基本物理时间不可逆；它只描述有限确定性自映射的组合结构。
6. 本节没有把 projective limit、自然扩张与量子多世界解释等同。


---

# 27. 追加：预测同余格、十一项观察审计与形式化落点

前述章节已经得到四类完成：

1. 单读出的最小预测完成 \(Z_q\)；
2. 多读出的联合完成 \(Z_{q_I}\)；
3. 带输入系统的最小行为完成 \(Z_{q,U}\)；
4. 保存全部前像分支的组合完成 \(\mathfrak N(\tau)\)。

本节把这些结果收束成一个有限格结构，并明确它们与仓库已有 Lean 声明之间的可复用接口与不可混同边界。

## 27.1 全部预测完成恰由 \(\tau\)-同余分类

令
\[
\operatorname{Cong}_\tau(Y)
\]
为 \(Y\) 上全部 \(\tau\)-同余，按关系包含排序。

任意族 \((R_i)_{i\in I}\) 的交仍是 \(\tau\)-同余，因此给出格的交：
\[
\boxed{
\bigwedge_iR_i
=
\bigcap_iR_i.
}
\]

对两个同余 \(R,S\)，定义它们的并同余
\[
\boxed{
R\vee_\tau S
=
\bigcap\{
T\in\operatorname{Cong}_\tau(Y):
R\cup S\subseteq T
\}.
}
\]
它是同时包含 \(R,S\) 的最小 \(\tau\)-同余。

由于 \(Y\) 有限，
\[
\operatorname{Cong}_\tau(Y)
\]
是有限完备格。

### 定理 27.1（每个同余都是某个已完成读出的预测关系）

对任意
\[
R\in\operatorname{Cong}_\tau(Y),
\]
取商读出
\[
q_R=\pi_R:Y\to Y/R.
\]
则
\[
\boxed{
R_{q_R}=R.
}
\]

### 证明

当前读出相同恰等价于
\[
yRy'.
\]
所以
\[
R_{q_R}\subseteq R.
\]
反之，若 \(yRy'\)，同余性给出
\[
\tau^k y\,R\,\tau^k y'
\]
对全部 \(k\) 成立，故全部未来商读出相同：
\[
yR_{q_R}y'.
\]
得到反向包含。\(\square\)

因此
\[
\boxed{
\text{有限预测完成的等价关系}
=
\operatorname{Cong}_\tau(Y).
}
\]
读出 \(q\) 只是从当前分区
\[
\ker q
\]
出发，通过内算子
\[
\mathsf C_\tau
\]
选出其中最大的同余。

## 27.2 联合观察与共同信息形成商菱形

令
\[
R_1=R_{q_1},
\qquad
R_2=R_{q_2}.
\]

联合观察对应同余交：
\[
\boxed{
R_{\mathrm{fuse}}
=
R_1\cap R_2.
}
\]
它产生最小共同精化，即在所有同时精化二者的完成中保留最少但仍充分的信息：
\[
\boxed{
Z_{\mathrm{fuse}}
=
Y/(R_1\cap R_2).
}
\]

另一方面，定义共同因子同余
\[
\boxed{
R_{\mathrm{common}}
=
R_1\vee_\tau R_2.
}
\]
并令
\[
\boxed{
Z_{\mathrm{common}}
=
Y/(R_1\vee_\tau R_2).
}
\]

于是存在规范满射菱形：
\[
\boxed{
Z_{\mathrm{fuse}}
\twoheadrightarrow
Z_{q_1}
\twoheadrightarrow
Z_{\mathrm{common}},
}
\]
\[
\boxed{
Z_{\mathrm{fuse}}
\twoheadrightarrow
Z_{q_2}
\twoheadrightarrow
Z_{\mathrm{common}}.
}
\]

### 定理 27.2（最小共同精化的泛性质）

若某完成 \(W\) 同时精化 \(Z_{q_1}\) 与 \(Z_{q_2}\)，即存在满射
\[
W\twoheadrightarrow Z_{q_i}
\]
且这些映射与同一个原始投影 \(Y\to W\) 相容，则存在唯一满射
\[
\boxed{
W\twoheadrightarrow Z_{\mathrm{fuse}}.
}
\]

### 证明

设 \(r:Y\twoheadrightarrow W\)。能从 \(W\) 计算两个完成意味着
\[
\ker r\subseteq R_1
\quad\text{且}\quad
\ker r\subseteq R_2.
\]
故
\[
\ker r\subseteq R_1\cap R_2.
\]
于是联合投影
\[
Y\to Y/(R_1\cap R_2)
\]
在 \(r\)-纤维上常值，唯一因子化为 \(W\to Z_{\mathrm{fuse}}\)。\(\square\)

### 定理 27.3（最大共同因子的泛性质）

设
\[
r:Y\twoheadrightarrow W
\]
是一个动力学因子：存在
\[
\theta:W\to W
\]
满足
\[
r\tau=\theta r.
\]
再假设该因子可以分别从两个完成确定地计算，即存在
\[
a_i:Z_{q_i}\to W
\]
满足
\[
r=a_i\pi_{q_i}
\quad(i=1,2).
\]
则存在唯一满射
\[
\boxed{
h:Z_{\mathrm{common}}\twoheadrightarrow W
}
\]
使
\[
r=h\pi_{\mathrm{common}}.
\]

因此 \(Z_{\mathrm{common}}\) 是两个预测完成的**最细共同确定因子**。

### 证明

由
\[
r=a_i\pi_{q_i}
\]
得到
\[
R_i=\ker\pi_{q_i}\subseteq\ker r.
\]
\(\ker r\) 是 \(\tau\)-同余，因为 \(r\) 作为完成因子与动力学交换。因此
\[
R_1\vee_\tau R_2
\subseteq
\ker r.
\]
所以 \(r\) 在 \(\pi_{\mathrm{common}}\)-纤维上常值，唯一因子化。\(\square\)

在基数上有
\[
\boxed{
|Z_{\mathrm{common}}|
\le
\min(|Z_{q_1}|,|Z_{q_2}|)
}
\]
与
\[
\boxed{
|Z_{\mathrm{fuse}}|
\ge
\max(|Z_{q_1}|,|Z_{q_2}|).
}
\]

所以多观察者结构同时含有两个方向：

\[
\boxed{
\text{融合：保留任一观察者能分辨的差异};
}
\]
\[
\boxed{
\text{共同因子：只保留两个观察者都能独立确定的状态}.
}
\]

不能只构造直积联合读出，而忽略共同因子；两者分别是同余格的交与并。

## 27.3 给定分布下的共同状态熵界

令随机初态为 \(Y_0\)，定义
\[
Z_i=\pi_{q_i}(Y_0),
\qquad
C=\pi_{\mathrm{common}}(Y_0).
\]
由于 \(C\) 同时是 \(Z_1\) 与 \(Z_2\) 的确定函数，
\[
H(C\mid Z_1)=H(C\mid Z_2)=0.
\]

### 定理 27.4（共同确定状态受互信息控制）

有
\[
\boxed{
H(C)
\le
I(Z_1;Z_2).
}
\]

### 证明

因为 \(C\) 是 \(Z_1\) 的函数，数据处理给出
\[
I(Z_1;Z_2)
\ge
I(C;Z_2).
\]
又因为 \(C\) 也是 \(Z_2\) 的函数，
\[
H(C\mid Z_2)=0,
\]
所以
\[
I(C;Z_2)
=
H(C)-H(C\mid Z_2)
=
H(C).
\]
合并即得。\(\square\)

该不等式只针对由两个完成共同确定的商变量 \(C\)。它没有声称全部互信息都能由一个确定共同状态提取，也没有把
\[
Z_{\mathrm{common}}
\]
等同于任何特定文献中的概率共同信息定义。

## 27.4 十一项观察者审计

结合第 18、20、21、22、24、25、26 节，一个有限观察接口至少应分别记录以下十一项。

### 1. 对角自然性

是否有
\[
Q\Delta_\tau=\Delta_\sigma P,
\]
或其误差
\[
\delta_\Delta.
\]

### 2. 扭曲忠实性

观察是否仍能分离
\[
y
\quad\text{与}\quad
\tau y,
\]
而不是自然交换但把扭曲商掉。

### 3. 全局单值命名

商纤维的余坐标是否存在全局截面；若只有局部截面，必须记录 cocycle 与 monodromy。

### 4. 瞬态容量可见性

迹、秩、像链与零 Jordan 块保存了多少瞬态容量。

### 5. 分支关联可见性

是否保留
\[
\mathfrak N_h(\tau)
\]
直至足够深度，从而区分相同谱而不同入树附着的函数图。

### 6. 预测闭合性

当前读出是否已经形成确定状态；若否，记录
\[
m_*,
\qquad
Z_q,
\qquad
C_{\mathrm{det}}.
\]

### 7. 观察精化一致性

对
\[
q\succeq_{\mathrm{obs}}r,
\]
是否保存规范满射
\[
Z_q\twoheadrightarrow Z_r
\]
及其复合律，而不是为每个尺度独立选择不可比较的模型。

### 8. 多观察者兼容性

联合完成是否只占据
\[
Z_1\times Z_2
\]
的兼容子集；共同因子
\[
Z_{\mathrm{common}}
\]
是什么；支持亏损与分布互信息必须分栏。

### 9. 定量鲁棒性

记录
\[
d_\gamma,
\qquad
\delta,
\qquad
\eta,
\qquad
L,
\]
并给出有限时域误差，而不是把近似交换口语化为“基本相同”。

### 10. 干预闭合性

状态商是否对全部
\[
F_u
\]
同时为同余；只对无输入轨迹闭合，不等于对所有外部干预闭合。

### 11. 时间方向完整性

必须区分
\[
Z_q,
\qquad
X_\tau^-,
\qquad
\mathfrak N(\tau).
\]
未来预测完成、单路径过去逆极限与全分支过去完成保存不同信息。

这十一项不应自动互推。已有反例至少表明：

- 自然性不推出忠实性；
- 迹—秩容量不推出分支完整性；
- 当前合法读出不推出无记忆闭合；
- 完成状态数的单调性不推出完成深度单调性；
- 联合完成不必充满直积；
- 小有限词直径不推出同层转移良定义；
- 有限状态在外部输入下不推出轨迹最终周期；
- 普通过去逆极限不推出瞬态分支被恢复。

## 27.5 与仓库已有 Lean 锚点的精确接口

本追加部分不是孤立另起一套观察者术语。它与当前仓库至少有以下可复用接口，但每一项都必须避免过度同一化。

### `D5/S3/ObserverMemory/FiniteReadoutKernel.lean`

该模块形式化线性读出
\[
M\to N
\]
按线性核取商后与可达像线性等价：
\[
M/\ker f
\cong
\operatorname{range}(f).
\]

本节的
\[
Y/R_q
\]
复用“按不可见差异取商”的结构模式，但 \(R_q\) 是由全部未来读出生成的集合论同余，不是线性映射的代数核。除非另行给出线性动力学与线性读出，不能把二者直接识别。

### `D5/S3/ObserverMemory/TwoTimeKnowledge.lean`

该模块用
\[
\texttt{Function.FactorsThrough}
\]
表达事件值在观察纤维上常值，并证明观察粗化方向上的知识传递。

定理 22.2、27.3 与该纤维因子化语言直接相容：观察精化对应更小的纤维关系，公共因子对应同时在两个完成纤维上常值的读出。但本追加处理全部未来与动力学同余，超出两时刻定义本身。

### `D5/S0/Naming/TranslationComposition.lean`

该模块证明近似命名翻译复合时：

- 语义误差相加；
- 资源模数复合；
- 等距嵌入复合。

定理 24.13 给出动力学半共轭缺陷
\[
K\delta_1+\delta_2
\]
的对应复合律。两者共享三角不等式与 Lipschitz 传播模式，但对象与结论不同；现有 Lean 定理不能被引用为本节的 proof term。

### `D5/S3/ObserverMemory/FiniteForgettingCertificate.lean`

该模块保存“遗忘已发生”“访问已撤销”等 append-only 审计标记，并证明有限历史不擦除这些账本事实。

预测完成可能把两个未来读出相同的状态合并，而审计账本仍可要求历史标记不被删除。因此：

\[
\boxed{
\text{预测等价}
\ne
\text{审计历史等价}.
}
\]

若账本会被未来转移读取，它必须并入 \(Y\)；若它只供外部审计且不影响动力学，则可作为与预测状态并列的不可擦除证书。

### `D5/S3/ObserverMemory/MultiCopyErasure.lean`

该模块证明有限个独立环境记录通道的重叠因子相乘，并刻画“至少一个零重叠副本导致对应矩阵元擦除”。

第 22.6 节的多观察者融合是经典确定性读出关系的交：
\[
R_{12}=R_1\cap R_2.
\]
它不能替代量子通道乘积、退相干或多副本擦除定理。二者只共享“多个记录共同约束可见性”的高层模式。

### `D5/S3/ObserverMemory/RecordCorrelationMonogamy.lean`

该模块对同一个固定记录指针证明互补系统相关的约束，并明确排除了把不同记录可观测量混为同一命题的错误替换。

本追加的经典联合读出可以无损拼接多个坐标；这不推出量子互补可观测量也能同时形成经典直积完成。任何量子推广都必须重新指定态空间、通道、可观测代数与距离。

## 27.6 推荐形式化分解

本追加部分适合拆成以下互相依赖但可独立冻结的 Lean 模块。路径仅为候选语义地址，实际创建必须先经过仓库 routing/harness，不应手写绕过。

### 第一簇：预测同余内核

候选模块：

- `PredictiveCongruenceCore`
- `FiniteCongruenceStabilization`
- `PredictiveCompletionIdempotent`

核心声明：

\[
\mathsf C_\tau(R)
=
\bigcap_k(\tau^k\times\tau^k)^{-1}(R),
\]
最大同余、单调、收缩、幂等与稳定界。

### 第二簇：观察精化与同余格

候选模块：

- `PredictiveRefinementFactor`
- `JointReadoutCompletion`
- `PredictiveCongruenceLattice`

核心声明：

\[
R_q\subseteq R_r
\Longrightarrow
Z_q\twoheadrightarrow Z_r,
\]
\[
R_{(q_1,q_2)}=R_{q_1}\cap R_{q_2},
\]
以及共同因子
\[
Y/(R_1\vee_\tau R_2).
\]

### 第三簇：可核验最小化

候选模块：

- `FuturePartitionRefinement`
- `PairDistinguishingCertificate`
- `PredictiveDepthSharpness`

先形式化数学递推与证书正确性，再决定是否对数组实现、排序与复杂度作单独程序验证。

### 第四簇：定量预测距离

候选模块：

- `DiscountedPredictivePseudoMetric`
- `DiscretePredictiveUltraMetric`
- `ApproximateObserverSemiconjugacy`

核心声明：

\[
d_\gamma
=
\max\{d_0,\gamma d_\gamma\circ(\tau\times\tau)\},
\]
有限截断误差、离散首差异公式、轨道误差与缺陷复合。

### 第五簇：受控观察完成

候选模块：

- `ControlledPredictiveCongruence`
- `ControlledObserverCompletion`
- `ControlledDistinguishingWord`

核心声明：

\[
R_{m+1}
=
\ker q\cap
\bigcap_u(F_u\times F_u)^{-1}(R_m),
\]
最小 Moore 行为商、干预对角自然性与反馈策略闭合。

### 第六簇：过去极限分家

候选模块：

- `FiniteInverseLimitPeriodicCore`
- `BidirectionalTrajectoryPeriodic`
- `PastBranchCompletionSeparation`

核心声明：

\[
\varprojlim(Y,\tau)\cong P_\tau
\]
以及与装饰 necklace 完成的显式非等价反例。

推荐依赖顺序为：

\[
\boxed{
\text{有限关系与商}
\to
\text{同余内核}
\to
\text{精化/融合}
\to
\text{算法证书}
\to
\text{度量近似}
\to
\text{受控输入}
\to
\text{逆极限分家}.
}
\]

## 27.7 追加部分的形式化状态

定理 22.2—22.17、23.1—23.7、24.1—24.13、25.1—25.9、例 25.10、定理 25.11、定理 26.1—26.4、例 26.5、定理 26.6 及定理 27.1—27.4 均给出纸面定义与证明，但尚未成为 Lean 数学真源。

在获得以下全部工件以前，不得把任何新增结论标记为 `Closed`：

1. Lean 声明与 proof term；
2. 完整 axiom 闭包；
3. 依赖地址与 Blueprint 镜像；
4. harness admission；
5. 冻结收据。

本文对仓库已有 Lean 模块的引用只说明可复用接口或严格边界，不声称这些模块已经证明本追加定理。

## 27.8 最终非主张

1. 本追加不证明 Riemann 假设，不提供 Weil 正性的缺失全局余项估计。
2. 本追加不把有限预测完成等同于意识、自我或物理观察者的唯一模型。
3. 本追加不声称折扣参数 \(\gamma\)、完成深度 \(m_*\) 或状态数对应任何普适物理常数。
4. 本追加不把经典多传感器融合推广为量子可观测量的任意联合可读性。
5. 本追加不证明现实大语言模型在工程时间尺度上必然进入短循环；第 21 节的有限自治结论仍受完整运行时状态与外部输入假设约束。
6. 本追加不声称普通逆极限能够恢复瞬态分支；定理 26.1 恰好证明相反结论。
7. 本追加不冒领自动机最小化、同余格、Koopman 闭包或行为度量的一般思想为本项目独有发明；本文的贡献定位是把它们在本稿既有“对角—观察—完成”主线中给出单一、自洽、可形式化拆分的接口。
8. 任何新增纸面定理若在 Lean 形式化中需要加强前提、削弱结论或拆分命题，应以 kernel-verified 声明为唯一真值，并在文档中 append-only 记录勘误。

---

# 28. 追加：Hilbert 正交商余塔、有限切片完成与持续逃逸

本节把“在一个已知有限维 Hilbert 空间之外取反，再对余部作商余分类，并持续递归”收紧为类型正确的 Hilbert 空间结构。首先必须修正记号：若 \(H_0\) 只是一个抽象有限维 Hilbert 空间，则表达式
\[
\mathscr H_\infty-H_0
\]
没有定义。必须先给出一个等距线性嵌入
\[
\iota:H_0\hookrightarrow\mathscr H,
\]
并令
\[
M=\iota(H_0)
\subseteq\mathscr H.
\]
真正的“取反”不是集合差，而是闭子空间格中的正交补
\[
M^\perp
=
\{x\in\mathscr H:\langle x,m\rangle=0\ \forall m\in M\},
\]
或者等价地，是正交投影的补
\[
P_M\longmapsto I-P_M.
\]

本节证明五组互相衔接的结论。

1. 对闭子空间，商空间 \(\mathscr H/M\) 与正交余空间 \(M^\perp\) 规范等距同构；
2. 直接重复取正交补只形成二周期，不能产生真正的递归深度；
3. 非平凡递归必须在当前余空间中继续选择有限维切片，形成正交分裂的商余塔；
4. 在无限维空间中，每个有限阶段的余空间仍与原空间同型，但全部有限切片的完成可以重构整个空间；
5. 点态强收敛可以与最坏情形误差恒等于一同时成立，因此任何有限观察层都存在一个完全不可见的正交逃逸方向。

这一结构同时澄清“连续如何产生离散”。Hilbert 向量空间本身仍是连续的；离散性来自所选择的投影族、壳层编号与测量结果，而每个离散壳层内部仍携带实或复的连续振幅。

## 28.1 类型正确的取反：投影补、正交补与商余代表

以下标量域固定为
\[
\mathbb K\in\{\mathbb R,\mathbb C\},
\]
\(\mathscr H\) 为 \(\mathbb K\)-Hilbert 空间。

有限维线性子空间自动闭合，所以有限维 \(M\subseteq\mathscr H\) 存在唯一正交投影
\[
P_M:\mathscr H\to M.
\]
每个 \(x\in\mathscr H\) 唯一分解为
\[
\boxed{
x=P_Mx+(I-P_M)x,
}
\]
其中
\[
P_Mx\in M,
\qquad
(I-P_M)x\in M^\perp.
\]
并且
\[
\boxed{
\|x\|^2
=
\|P_Mx\|^2
+
\|(I-P_M)x\|^2.
}
\]

### 定理 28.1（投影补是子空间取反）

对任意闭子空间 \(M\subseteq\mathscr H\)：
\[
\boxed{
P_{M^\perp}=I-P_M,
}
\]
并有
\[
\boxed{
P_M^2=P_M,
\qquad
P_{M^\perp}^2=P_{M^\perp},
}
\[
\boxed{
P_MP_{M^\perp}=P_{M^\perp}P_M=0,
}
\[
\boxed{
P_M+P_{M^\perp}=I.
}

### 证明

对任意 \(x\)，正交分解
\[
x=P_Mx+(x-P_Mx)
\]
的第二项属于 \(M^\perp\)。因此投影到 \(M^\perp\) 的分量恰为
\[
x-P_Mx=(I-P_M)x.
\]
其余恒等式由互补正交投影直接计算。\(\square\)

### 定理 28.2（商—正交余规范等距同构）

令
\[
q_M:\mathscr H\to\mathscr H/M
\]
为 Banach 商映射。定义
\[
U_M:\mathscr H/M\to M^\perp,
\qquad
U_M(q_M(x))=(I-P_M)x.
\]
则 \(U_M\) 是规范线性等距同构：
\[
\boxed{
\mathscr H/M
\cong_{\mathrm{iso}}
M^\perp.
}
\]

### 证明

若
\[
q_M(x)=q_M(x'),
\]
则 \(x-x'\in M\)，故
\[
(I-P_M)(x-x')=0.
\]
所以 \(U_M\) 良定义。

任意 \(r\in M^\perp\) 满足
\[
U_M(q_M(r))=r,
\]
故满射。若 \(U_M(q_M(x))=0\)，则 \(x=P_Mx\in M\)，所以 \(q_M(x)=0\)，故单射。

最后，商范数满足
\[
\|q_M(x)\|
=
\inf_{m\in M}\|x-m\|.
\]
由正交分解，对任意 \(m\in M\)：
\[
\|x-m\|^2
=
\|P_Mx-m\|^2
+
\|(I-P_M)x\|^2
\ge
\|(I-P_M)x\|^2.
\]
取 \(m=P_Mx\) 达到等号，故
\[
\|q_M(x)\|
=
\|(I-P_M)x\|.
\]
所以 \(U_M\) 等距。\(\square\)

因此“商”和“余”在 Hilbert 空间中不是两个互不相干的操作：
\[
\boxed{
\text{按 }M\text{ 取商}
=
\text{为每个商类选取唯一的正交余代表}.
}
\]

## 28.2 相对正交余、orthomodular 分解与非 Boolean 性

如果
\[
M\subseteq N\subseteq\mathscr H
\]
均为闭子空间，定义 \(M\) 在 \(N\) 中的相对正交余：
\[
\boxed{
N\ominus M
:=
N\cap M^\perp.
}
\]
这才是“从 \(N\) 中扣除已知部分 \(M\)”的类型正确版本。

### 定理 28.3（相对商余分解）

若 \(M\subseteq N\) 为闭子空间，则
\[
\boxed{
N=M\oplus(N\ominus M).
}
并且存在规范等距同构
\[
\boxed{
N/M
\cong_{\mathrm{iso}}
N\ominus M.
}

### 证明

把 \(x\in N\) 按 \(M\) 分解：
\[
x=P_Mx+(I-P_M)x.
\]
由于 \(M\subseteq N\)，第一项属于 \(N\)，所以第二项也属于 \(N\)；同时第二项属于 \(M^\perp\)。故
\[
(I-P_M)x\in N\cap M^\perp=N\ominus M.
\]
唯一性来自正交和。商同构是定理 28.2 限制到 \(N\) 的版本。\(\square\)

该式正是闭子空间格的 orthomodular law：
\[
\boxed{
M\subseteq N
\Longrightarrow
N=M\vee(N\wedge M^\perp).
}
\]
其中
\[
M\wedge N=M\cap N,
\qquad
M\vee N=\overline{M+N}.
\]

### 定理 28.4（正交 De Morgan 公式）

对闭子空间 \(M,N\subseteq\mathscr H\)：
\[
\boxed{
(M\vee N)^\perp
=M^\perp\cap N^\perp,
}
\]
\[
\boxed{
(M\cap N)^\perp
=
\overline{M^\perp+N^\perp}.
}

### 证明

一个向量与 \(M+N\) 中全部向量正交，当且仅当它同时与 \(M\) 和 \(N\) 正交；闭包不改变正交补，得到第一式。对第一式应用双重正交补并交换 \(M,N\) 与其正交补，即得第二式。\(\square\)

正交补虽然具有 involution 与 De Morgan 结构，但闭子空间格一般不是 Boolean 代数，因为分配律失败。

### 例 28.5（二维 Hilbert 格的非分配性）

在
\[
\mathscr H=\mathbb C^2
\]
中取
\[
A=\operatorname{span}(e_1),
\]
\[
B=\operatorname{span}(e_1+e_2),
\qquad
C=\operatorname{span}(e_1-e_2).
\]
因为 \(B\vee C=\mathscr H\)，有
\[
A\wedge(B\vee C)=A.
\]
但三条直线互不相同，所以
\[
A\wedge B=A\wedge C=\{0\},
\]
从而
\[
(A\wedge B)\vee(A\wedge C)=\{0\}.
\]
因此
\[
\boxed{
A\wedge(B\vee C)
\ne
(A\wedge B)\vee(A\wedge C).
}

所以 Hilbert 子空间中的“取反—交—并”不能被无条件当作经典集合的 Boolean 运算。它是 orthomodular，而不是分配的。

## 28.3 直接重复取反只产生二周期

定义闭子空间取反算子
\[
\mathcal C(M)=M^\perp.
\]

### 定理 28.6（双重正交补）

对任意线性子空间 \(M\subseteq\mathscr H\)：
\[
\boxed{
M^{\perp\perp}=\overline M.
}
因此若 \(M\) 闭合，特别是若 \(M\) 有限维，则
\[
\boxed{
\mathcal C^2(M)=M.
}

### 证明

显然 \(M\subseteq M^{\perp\perp}\)，而 \(M^{\perp\perp}\) 闭合，所以
\[
\overline M\subseteq M^{\perp\perp}.
\]
若 \(x\notin\overline M\)，按闭子空间 \(\overline M\) 作正交分解：
\[
x=P_{\overline M}x+r,
\qquad
r\in M^\perp,
\qquad
r\ne0.
\]
则
\[
\langle x,r\rangle
=
\|r\|^2\ne0,
\]
故 \(x\notin M^{\perp\perp}\)。所以反向包含成立。\(\square\)

于是直接迭代为
\[
M,
\quad
M^\perp,
\quad
M,
\quad
M^\perp,
\quad\ldots
\]
只是二周期：
\[
\boxed{
\mathcal C^{2k}(M)=M,
\qquad
\mathcal C^{2k+1}(M)=M^\perp.
}

因此真正有内容的递归不能是“对同一个整体不断再取正交补”。必须在当前余空间内部继续选择一个新切片，并把它加入累计已知空间。

## 28.4 无限吸收：有限切片不改变余空间的 Hilbert 同构类型

Hilbert 维数定义为任一正交规范基的基数。设
\[
\dim_{\mathrm H}\mathscr H=\kappa
\]
为无限基数，而
\[
\dim M=n<\infty.
\]

### 定理 28.7（有限抽取后的余空间维数不变）

有
\[
\boxed{
\dim_{\mathrm H}M^\perp=\kappa.
}
因此
\[
\boxed{
M^\perp\cong_{\mathrm{unitary}}\mathscr H,
}
以及
\[
\boxed{
\mathscr H/M
\cong_{\mathrm{unitary}}\mathscr H.
}

### 证明

由
\[
\mathscr H=M\oplus M^\perp
\]
得到 Hilbert 维数的基数和：
\[
\kappa=n+\dim_{\mathrm H}M^\perp.
\]
若右侧余维有限，则右侧总和有限，与 \(\kappa\) 无限矛盾；若余维无限，则有限基数加无限基数等于该无限基数，所以余维必须为 \(\kappa\)。Hilbert 空间由正交规范基基数分类，故得到酉同构。商同构再由定理 28.2。\(\square\)

在可分无限维情形：
\[
\mathscr H\cong\ell^2(\mathbb N),
\]
对任意有限维 \(M\)：
\[
\boxed{
M^\perp\cong\ell^2(\mathbb N).
}

这给出“无限减去有限仍是无限”的严格含义：它是**抽象 Hilbert 同构类型不变**，而不是集合论差、不是规范恒等，也不表示被抽出的有限部分没有留下结构记录。

若递归只保存
\[
[R_n]_{\cong}
\]
这样的抽象同构类，那么所有有限阶段都会坍缩为同一个值
\[
[\mathscr H].
\]
真正的信息存在于嵌入、投影、商映射及每轮抽出的切片中，而不只存在于余空间对象的同构类型中。

## 28.5 无规范逃逸向量：递归必须携带选择结构

裸 Hilbert 空间在酉群下高度齐性。任意两个同维有限子空间都可由某个酉算子互相送达。因此仅凭 \(\mathscr H\) 本身，没有一个被全体酉对称性保留的首选非零有限切片。

### 定理 28.8（不存在酉自然的正交逃逸选择器）

设 \(\mathscr H\) 无限维。不存在映射
\[
\eta:
\{M\subseteq\mathscr H:M\text{ 为有限维闭子空间}\}
\to
\{x\in\mathscr H:\|x\|=1\}
\]
同时满足：

1. 对每个 \(M\)，
   \[
   \eta(M)\in M^\perp;
   \]
2. 对每个酉算子 \(U\)，
   \[
   \boxed{
   \eta(UM)=U\eta(M).
   }
   \]

### 证明

固定有限维 \(M\)，令
\[
e=\eta(M)\in M^\perp.
\]
取一个酉算子 \(V\)，使它在 \(M\) 上恒等，在 \(e\) 张成的一维空间上取负号，并在其余正交补上恒等。则
\[
VM=M,
\qquad
Ve=-e.
\]
酉自然性要求
\[
e=\eta(M)=\eta(VM)=V\eta(M)=-e,
\]
矛盾。\(\square\)

所以从余空间中“抠出下一个对象”需要额外数据，例如：

- 一组已命名正交规范基；
- 自伴算子的谱投影；
- 一个观察者给出的有限秩投影；
- 一组生成向量及正交化规则；
- 局域性、能量、尺度或复杂度排序；
- 任何明确打破全酉对称性的选择接口。

正交补只给出一个逃逸**空间**，一般不给出一个规范逃逸**向量**。

## 28.6 非平凡递归：有限切片—商—余空间塔

设初始已知空间
\[
S_0=M
\]
为有限维闭子空间，并令
\[
R_0=S_0^\perp.
\]
递归地，已知
\[
\mathscr H=S_n\oplus R_n
\]
后，从当前余空间中选择一个有限维闭子空间
\[
E_{n+1}\subseteq R_n.
\]
定义
\[
\boxed{
S_{n+1}=S_n\oplus E_{n+1},
}
\[
\boxed{
R_{n+1}=R_n\cap E_{n+1}^\perp.
}

### 定理 28.9（单步正交商余递推）

对全部 \(n\ge0\)：
\[
\boxed{
R_{n+1}=S_{n+1}^\perp,
}
\[
\boxed{
R_n=E_{n+1}\oplus R_{n+1},
}
\[
\boxed{
\mathscr H=S_{n+1}\oplus R_{n+1}.
}

### 证明

由
\[
S_{n+1}=S_n\oplus E_{n+1}
\]
及正交 De Morgan：
\[
S_{n+1}^\perp
=S_n^\perp\cap E_{n+1}^\perp
=R_n\cap E_{n+1}^\perp
=R_{n+1}.
\]
又因为 \(E_{n+1}\subseteq R_n\)，在 Hilbert 空间 \(R_n\) 中对闭子空间 \(E_{n+1}\) 作正交分解，得到
\[
R_n=E_{n+1}\oplus(R_n\cap E_{n+1}^\perp).
\]
其余结论代入即得。\(\square\)

### 推论 28.10（有限阶段展开）

对每个 \(n\)：
\[
\boxed{
S_n
=
S_0
\oplus
E_1
\oplus\cdots\oplus
E_n,
}
\[
\boxed{
\mathscr H
=
S_0
\oplus
E_1
\oplus\cdots\oplus
E_n
\oplus
R_n.
}

因此递归的正确形态不是
\[
M\mapsto M^\perp\mapsto M\mapsto M^\perp,
\]
而是
\[
\boxed{
R_n
=
E_{n+1}
\oplus
R_{n+1}.
}
每一步从当前余空间抽取一个有限正交壳层，并把未抽取部分传给下一步。

## 28.7 商余短正合列与 associated graded 重构

定义第 \(n\) 层剩余商：
\[
Q_n=\mathscr H/S_n.
\]
由定理 28.2：
\[
Q_n\cong R_n.
\]
因为 \(S_n\subseteq S_{n+1}\)，存在规范商映射
\[
\rho_n:Q_n\twoheadrightarrow Q_{n+1},
\qquad
\rho_n(x+S_n)=x+S_{n+1}.
\]

### 定理 28.11（一步商余短正合列）

存在正交分裂短正合列
\[
\boxed{
0
\longrightarrow
E_{n+1}
\overset{\jmath_n}{\longrightarrow}
Q_n
\overset{\rho_n}{\longrightarrow}
Q_{n+1}
\longrightarrow
0,
}
其中
\[
\jmath_n(e)=e+S_n.
\]
并且
\[
\boxed{
\ker\rho_n
\cong
S_{n+1}/S_n
\cong
E_{n+1}.
}
在 Hilbert 同构下：
\[
\boxed{
Q_n
\cong
E_{n+1}\oplus Q_{n+1}.
}

### 证明

\(\rho_n\) 显然满射。其核由满足
\[
x\in S_{n+1}
\]
的 \(S_n\)-商类构成，所以
\[
\ker\rho_n=S_{n+1}/S_n.
\]
由
\[
S_{n+1}=S_n\oplus E_{n+1}
\]
得到
\[
S_{n+1}/S_n\cong E_{n+1}.
\]
再用
\[
Q_n\cong R_n=E_{n+1}\oplus R_{n+1}\cong E_{n+1}\oplus Q_{n+1}.
\]
\(\square\)

定义过滤的 associated graded Hilbert 空间：
\[
\operatorname{gr}(S_\bullet)
=
S_0
\oplus_2
\bigoplus_{n\ge0}
(S_{n+1}/S_n),
\]
其中 \(\oplus_2\) 表示平方可和 Hilbert 直和。

由于
\[
S_{n+1}/S_n\cong E_{n+1},
\]
它等距同构于
\[
S_0\oplus_2\bigoplus_{n\ge1}E_n.
\]
这说明递归真正累积的是商层
\[
S_{n+1}/S_n,
\]
而不是每次都与 \(\mathscr H\) 同型的抽象余空间。

## 28.8 无限极限：累计已知空间与最终余空间

定义
\[
\boxed{
S_\infty
=
\overline{\bigcup_{n\ge0}S_n}
=
\overline{
S_0\oplus\bigoplus_{n\ge1}E_n
},
}
\[
\boxed{
R_\infty
=
\bigcap_{n\ge0}R_n.
}

### 定理 28.12（极限商余分解）

有
\[
\boxed{
R_\infty=S_\infty^\perp,
}
并且
\[
\boxed{
\mathscr H=S_\infty\oplus R_\infty.
}

### 证明

若 \(x\in\bigcap_nR_n\)，则它与每个 \(S_n\) 正交，故与
\[
\bigcup_nS_n
\]
及其闭包 \(S_\infty\) 正交。因此
\[
R_\infty\subseteq S_\infty^\perp.
\]
反之，若 \(x\perp S_\infty\)，则 \(x\perp S_n\) 对全部 \(n\) 成立，所以
\[
x\in\bigcap_nS_n^\perp=\bigcap_nR_n.
\]
得到等号。最后对闭子空间 \(S_\infty\) 作正交分解。\(\square\)

### 推论 28.13（递归完备性判据）

下列条件等价：
\[
\boxed{
R_\infty=\{0\},
}
\[
\boxed{
S_\infty=\mathscr H,
}
\[
\boxed{
\overline{
S_0\oplus\bigoplus_{n\ge1}E_n
}
=
\mathscr H.
}

若这些条件成立，则
\[
\boxed{
\mathscr H
\cong
S_0
\oplus_2
\bigoplus_{n\ge1}E_n.
}
若不成立，则完整分解为
\[
\boxed{
\mathscr H
\cong
S_0
\oplus_2
\bigoplus_{n\ge1}E_n
\oplus
R_\infty.
}

所以 \(R_\infty\) 是相对于当前选择规则永远没有被命名的终极余扇区。

## 28.9 一维切片与正交规范基

最小递归每次只选择一个单位向量：
\[
e_{n+1}\in R_n,
\qquad
\|e_{n+1}\|=1,
\]
并令
\[
E_{n+1}=\mathbb K e_{n+1}.
\]
由于
\[
e_{n+1}\perp S_n,
\]
序列 \((e_n)\) 两两正交。

若 \(S_0=\{0\}\) 且 \(R_\infty=0\)，则 \((e_n)\) 是 \(\mathscr H\) 的正交规范基；反过来，任意有序正交规范基都给出这样的完备商余塔。

对每个 \(x\in\mathscr H\)：
\[
\boxed{
x
=
P_{S_0}x
+
\sum_{n\ge1}
\langle x,e_n\rangle e_n
+
P_{R_\infty}x,
}
并有
\[
\boxed{
\|x\|^2
=
\|P_{S_0}x\|^2
+
\sum_{n\ge1}
|\langle x,e_n\rangle|^2
+
\|P_{R_\infty}x\|^2.
}

这里的“离散”是坐标标签
\[
n=1,2,3,\ldots,
\]
而系数
\[
\langle x,e_n\rangle\in\mathbb K
\]
仍是连续振幅。因此：
\[
\boxed{
\text{正交递归产生离散坐标骨架，
不是把 Hilbert 向量变成有限离散集合}.
}

## 28.10 可分与不可分：何时可数递归足够

### 定理 28.14（可数有限切片只产生可分部分）

若每个 \(E_n\) 有限维，则
\[
S_\infty
=
\overline{S_0\oplus\bigoplus_{n\ge1}E_n}
\]
是可分 Hilbert 空间。

因此若 \(\mathscr H\) 不可分，则
\[
\boxed{
R_\infty\ne0
}
对任意可数有限切片递归都成立。

### 证明

每个有限维空间有有限正交规范基；全部切片基的可数并是可数集合，其线性包在 \(S_\infty\) 中稠密。故 \(S_\infty\) 可分。若 \(S_\infty=\mathscr H\)，则 \(\mathscr H\) 可分，矛盾。\(\square\)

对不可分 Hilbert 空间，需要超限递归。

### 定理 28.15（正交基诱导的超限商余塔）

设
\[
\dim_{\mathrm H}\mathscr H=\kappa
\]
为无限基数，并选择以初始序数 \(\kappa\) 编号的正交规范基
\[
(e_\alpha)_{\alpha<\kappa}.
\]
对 \(\alpha\le\kappa\) 定义
\[
S_\alpha
=
\overline{\operatorname{span}}
\{e_\beta:\beta<\alpha\},
\]
\[
R_\alpha=S_\alpha^\perp.
\]
则：

1. 后继阶段
   \[
   \boxed{
   R_\alpha
   =
   \mathbb K e_\alpha
   \oplus
   R_{\alpha+1};
   }
   \]
2. 极限序数 \(\lambda\le\kappa\) 满足
   \[
   \boxed{
   S_\lambda
   =
   \overline{\bigcup_{\alpha<\lambda}S_\alpha},
   \qquad
   R_\lambda
   =
   \bigcap_{\alpha<\lambda}R_\alpha;
   }
   \]
3. 对每个 \(\alpha<\kappa\)：
   \[
   \boxed{
   \dim_{\mathrm H}R_\alpha=\kappa,
   }
   \]
   因而
   \[
   R_\alpha\cong\mathscr H;
   \]
4. 最终
   \[
   \boxed{
   R_\kappa=0.
   }
   \]

### 证明

前两项由基向量集合的分割与正交补定义直接得到。对 \(\alpha<\kappa\)，已抽出的基向量数 \(|\alpha|<\kappa\)；剩余指标集合仍有基数 \(\kappa\)，故余空间 Hilbert 维数为 \(\kappa\)。在阶段 \(\kappa\)，全部基向量已被抽取，其闭线性包为 \(\mathscr H\)，故余空间为零。\(\square\)

这给出一个精确的“无限吸收直到完成”现象：
\[
\boxed{
\text{每个真前阶段的余空间仍与整体同型，
只有完成全部基数长度的递归后余空间才归零}.
}

## 28.11 投影强收敛与持续的最坏情形盲区

令
\[
P_n=P_{S_n},
\qquad
P_\infty=P_{S_\infty}.
\]
因为 \(S_n\) 递增，\((P_n)\) 是递增投影族。

### 定理 28.16（递增投影的强极限）

对每个 \(x\in\mathscr H\)：
\[
\boxed{
P_nx\longrightarrow P_\infty x.
}
特别地，若递归完备，即 \(R_\infty=0\)，则
\[
\boxed{
P_n\xrightarrow{\mathrm{SOT}}I.
}

### 证明

若 \(m>n\)，由于
\[
S_n\subseteq S_m,
\]
向量
\[
P_mx-P_nx
\]
属于 \(S_m\cap S_n^\perp\)，并与 \(P_nx\) 正交。因此
\[
\|P_mx-P_nx\|^2
=
\|P_mx\|^2-
\|P_nx\|^2.
\]
序列 \(\|P_nx\|\) 单调有界，故 \((P_nx)\) Cauchy，收敛到某个 \(y\in S_\infty\)。对任意 \(s\in\bigcup_nS_n\)，充分大 \(n\) 时
\[
\langle x-P_nx,s\rangle=0.
\]
取极限得到 \(x-y\perp S_\infty\)，故 \(y=P_\infty x\)。\(\square\)

### 定理 28.17（有限层的范数一逃逸）

若 \(R_n\ne0\)，则
\[
\boxed{
\|I-P_n\|_{\mathrm{op}}=1.
}
更精确地，存在单位向量
\[
e_n^{\mathrm{esc}}\in R_n
\]
满足
\[
\boxed{
P_ne_n^{\mathrm{esc}}=0,
\qquad
\operatorname{dist}(e_n^{\mathrm{esc}},S_n)=1.
}

### 证明

正交投影补 \(I-P_n\) 的算子范数至多为一。取任意单位向量
\[
e_n^{\mathrm{esc}}\in R_n,
\]
则
\[
(I-P_n)e_n^{\mathrm{esc}}=e_n^{\mathrm{esc}},
\]
故算子范数至少为一。距离公式由正交性得到。\(\square\)

如果递归完备且每个 \(S_n\) 都仍是真子空间，则同时成立：
\[
\forall x\in\mathscr H,
\qquad
\|(I-P_n)x\|\to0,
\]
但
\[
\forall n,
\qquad
\sup_{\|x\|=1}
\|(I-P_n)x\|=1.
\]
所以
\[
\boxed{
\sup_{\|x\|=1}
\lim_{n\to\infty}
\|(I-P_n)x\|
=0,
}
而
\[
\boxed{
\lim_{n\to\infty}
\sup_{\|x\|=1}
\|(I-P_n)x\|
=1.
}

这是一条严格的有限—无限交换失败：

> 对每个预先固定的对象，观察可以越来越完整；但在任意有限阶段，总能在当前余空间中选择一个新的单位对象，使该观察完全失明。

因此强收敛不蕴含算子范数收敛。有限观察的逐对象完备性与全单位球上的统一完备性是两个不同命题。

## 28.12 正交逃逸与 Cantor/Lawvere 对角化的区别

给定有限层 \(S_n\)，正交补提供逃逸集合
\[
\boxed{
\mathfrak E(S_n)
=
\{e\in S_n^\perp:\|e\|=1\}.
}
每个 \(e\in\mathfrak E(S_n)\) 都满足
\[
P_ne=0
\]
及单位距离逃逸。

这与经典对角化具有共同的“逃出当前表示”形态，但不是同一定理：

1. Cantor/Lawvere 对角化从一个评价表的自坐标机械地产生一个指定新对象；
2. 正交逃逸只证明余空间中存在大量候选，通常没有规范唯一选择；
3. Cantor 逃逸依赖无不动点扭曲；正交逃逸依赖内积与闭子空间；
4. Cantor 新对象逐行不同；正交逃逸向量与整个已知线性包同时正交；
5. 正交逃逸边际在单位球上恰为一，是一个几何而非 Hamming 差异。

若加入选择规则
\[
\eta_n(S_n)\in\mathfrak E(S_n),
\]
则可递归定义
\[
S_{n+1}
=S_n\oplus\mathbb K\eta_n(S_n).
\]
但定理 28.8 说明该规则不能同时保持全部酉对称性；它必然编码一个观察者、基、算子或命名偏置。

所以更准确的术语是：
\[
\boxed{
\text{正交逃逸递归},
}
而不是把它直接等同于布尔对角化。

## 28.13 有界能量的 projective completion

有限切片还给出一个自然的有限坐标逆系。对 \(m\ge n\)，定义
\[
p_{m,n}:S_m\to S_n,
\qquad
p_{m,n}=P_{S_n}|_{S_m}.
\]
则
\[
p_{n,n}=\mathrm{id},
\qquad
p_{\ell,n}=p_{m,n}p_{\ell,m}.
\]
定义集合逆极限
\[
\varprojlim S_n
=
\left\{
(x_n)_n:
 x_n\in S_n,
\ p_{m,n}(x_m)=x_n
\ (m\ge n)
\right\}.
\]

普通集合逆极限允许坐标能量无限增长，因此一般比 Hilbert 完成更大。定义有界部分
\[
\boxed{
\varprojlim_{\!b}S_n
=
\left\{
(x_n)\in\varprojlim S_n:
\sup_n\|x_n\|<\infty
\right\}.
}
以范数
\[
\|(x_n)\|_b=\sup_n\|x_n\|.
\]

### 定理 28.18（有界逆极限重构累计完成）

映射
\[
J:S_\infty\to\varprojlim_{\!b}S_n,
\qquad
J(x)=(P_nx)_n
\]
是规范线性等距同构：
\[
\boxed{
S_\infty
\cong_{\mathrm{iso}}
\varprojlim_{\!b}S_n.
}
因此
\[
\boxed{
\mathscr H/R_\infty
\cong_{\mathrm{iso}}
\varprojlim_{\!b}S_n.
}

### 证明

相容性来自
\[
P_nP_m=P_n
\quad(m\ge n).
\]
由定理 28.16，若 \(x\in S_\infty\)，则
\[
P_nx\to x,
\]
所以
\[
\sup_n\|P_nx\|=\|x\|.
\]
故 \(J\) 等距，特别地单射。

现在取有界相容族 \((x_n)\)。定义正交增量
\[
d_0=x_0,
\qquad
d_{n+1}=x_{n+1}-x_n.
\]
由相容性
\[
P_nx_{n+1}=x_n,
\]
所以
\[
d_{n+1}\in S_{n+1}\cap S_n^\perp.
\]
不同增量两两正交，并且
\[
x_n=\sum_{j=0}^{n}d_j,
\]
\[
\|x_n\|^2
=
\sum_{j=0}^{n}\|d_j\|^2.
\]
有界性给出
\[
\sum_{j\ge0}\|d_j\|^2<\infty.
\]
故正交级数
\[
x=\sum_{j\ge0}d_j
\]
在 \(\mathscr H\) 中收敛；其部分和属于 \(S_n\)，所以 \(x\in S_\infty\)。并且
\[
P_nx=x_n.
\]
因此 \(J\) 满射。最后由
\[
\mathscr H/R_\infty\cong S_\infty
\]
得到第二式。\(\square\)

### 例 28.19（相容但无限能量的形式坐标）

取
\[
\mathscr H=\ell^2(\mathbb N),
\qquad
S_n=\operatorname{span}(e_1,\ldots,e_n),
\]
并定义
\[
x_n=e_1+\cdots+e_n.
\]
则
\[
P_nx_{n+1}=x_n,
\]
所以 \((x_n)\) 是普通逆极限中的相容族。但
\[
\|x_n\|=\sqrt n\to\infty,
\]
不存在 \(x\in\ell^2\) 满足
\[
P_nx=x_n
\]
对全部 \(n\) 成立。

因此：
\[
\boxed{
\text{有限坐标相容}
\not\Longrightarrow
\text{存在 Hilbert 向量};
}
还必须加入
\[
\boxed{
\text{统一有界能量／平方可和条件}.
}

这与第 26 节“普通状态逆极限只保留周期核”的结论处理不同对象，但共享一个方法论边界：仅写下形式相容条件，不能自动冒充目标范畴中的完备对象；必须检查该范畴额外要求的有界性、正则性或可实现性。

## 28.14 壳层投影、Born 权重与连续—离散接口

定义壳层投影
\[
P_0=P_{S_0},
\qquad
Q_n=P_{E_n}\quad(n\ge1),
\qquad
Q_\infty=P_{R_\infty}.
\]
这些投影两两正交。定理 28.12 与 28.16 给出强算子意义的分解
\[
\boxed{
P_0+
\sum_{n\ge1}Q_n
+Q_\infty
=I.
}

### 定理 28.20（向量壳层能量分解）

对任意 \(\psi\in\mathscr H\)：
\[
\boxed{
\|\psi\|^2
=
\|P_0\psi\|^2
+
\sum_{n\ge1}\|Q_n\psi\|^2
+
\|Q_\infty\psi\|^2.
}
若 \(\|\psi\|=1\)，则
\[
p_0=\|P_0\psi\|^2,
\qquad
p_n=\|Q_n\psi\|^2,
\qquad
p_\infty=\|Q_\infty\psi\|^2
\]
构成离散概率分布：
\[
\boxed{
p_0+
\sum_{n\ge1}p_n+p_\infty=1.
}

### 证明

有限阶段由 Pythagoras 定理：
\[
\|\psi\|^2
=
\|P_{S_n}\psi\|^2
+
\|P_{R_n}\psi\|^2,
\]
并且
\[
\|P_{S_n}\psi\|^2
=
\|P_0\psi\|^2
+
\sum_{j=1}^{n}\|Q_j\psi\|^2.
\]
令 \(n\to\infty\)，使用
\[
P_{S_n}\psi\to P_{S_\infty}\psi,
\qquad
P_{R_n}\psi\to P_{R_\infty}\psi.
\]
\(\square\)

若 \(\rho\) 为密度算子，定义
\[
p_0=\operatorname{Tr}(\rho P_0),
\qquad
p_n=\operatorname{Tr}(\rho Q_n),
\qquad
p_\infty=\operatorname{Tr}(\rho Q_\infty).
\]
由正性与迹的单调收敛：
\[
\boxed{
p_0+
\sum_{n\ge1}p_n+p_\infty=1.
}

因此商余塔诱导一个投影值离散读出：
\[
\text{“初始已知层”},
\quad
1,2,3,\ldots,
\quad
\text{“最终余层”}.
\]
但离散标签来自投影分解；状态向量、每个壳层与壳层内振幅仍是连续的。不能从壳层概率公式推出 Hilbert 空间本体是有限离散集合。

对于单个有限维 \(M\)，二元投影族
\[
(P_M,I-P_M)
\]
给出最小“已知／余部”测量。对单位向量 \(\psi\)：
\[
\boxed{
\Pr(M)=\|P_M\psi\|^2,
\qquad
\Pr(M^\perp)=\|(I-P_M)\psi\|^2.
}
这正是“取反”在投影测量中的精确概率含义，而不是向量本身被布尔取反。

## 28.15 裸商余塔的酉分类

考虑两套有序正交塔：
\[
\mathscr H
=
S_0
\oplus_2
\bigoplus_{n\ge1}E_n
\oplus R_\infty,
\]
\[
\mathscr H'
=
S_0'
\oplus_2
\bigoplus_{n\ge1}E_n'
\oplus R_\infty'.
\]
称它们塔等价，如果存在酉算子
\[
U:\mathscr H\to\mathscr H'
\]
满足
\[
U(S_0)=S_0',
\qquad
U(E_n)=E_n'\ \forall n,
\qquad
U(R_\infty)=R_\infty'.
\]

### 定理 28.21（裸塔的维数分类）

两套塔等价，当且仅当
\[
\boxed{
\dim S_0=\dim S_0',
}
\[
\boxed{
\dim E_n=\dim E_n'
\quad\forall n,
}
\[
\boxed{
\dim R_\infty=\dim R_\infty'.
}

### 证明

酉算子保持各块 Hilbert 维数，故必要性显然。

反之，按维数相等分别选择酉同构
\[
U_0:S_0\to S_0',
\]
\[
U_n:E_n\to E_n',
\]
\[
U_\infty:R_\infty\to R_\infty'.
\]
其 Hilbert 正交直和
\[
U=U_0\oplus\bigoplus_{n\ge1}U_n\oplus U_\infty
\]
是所需酉同构。\(\square\)

所以在没有任何额外算子、局域结构或语义标签时，商余塔只记录：
\[
\boxed{
\text{每一层抽出了多少 Hilbert 维度}.
}
它不自动记录这些维度“代表什么”。

## 28.16 加入动力学后必须保存块耦合

令
\[
T:\mathscr H\to\mathscr H
\]
为有界线性算子。记正交块为
\[
B_0=S_0,
\qquad
B_n=E_n\ (n\ge1),
\qquad
B_\infty=R_\infty,
\]
投影为 \(P_i\)。完整算子由块矩阵
\[
\boxed{
T_{ij}=P_iTP_j
}
决定。

### 定理 28.22（过滤不变性与三角块结构）

下列条件等价：

1. 对全部有限 \(n\)，
   \[
   T(S_n)\subseteq S_n;
   \]
2. 对全部有限块指标 \(j\) 与所有严格更晚的指标 \(i>j\)，
   \[
   \boxed{
   P_iTP_j=0,
   }
   \]
   并且
   \[
   P_{R_\infty}TP_j=0.
   \]

若每个 \(S_n\) 还是 \(T\) 的 reducing subspace，即同时对 \(T\) 与 \(T^*\) 不变，则每个壳层 \(E_n\) 与 \(R_\infty\) 都 reducing，并且
\[
\boxed{
P_iTP_j=0
\quad(i\ne j).
}
即 \(T\) 对商余塔块对角化。

### 证明

若 \(T(S_j)\subseteq S_j\)，则源于 \(B_j\subseteq S_j\) 的向量不能产生任何位于更晚壳层或最终余空间的分量，得到块消失。

反之，若所有晚向块消失，则每个
\[
S_n=B_0\oplus\cdots\oplus B_n
\]
在 \(T\) 下保持。

若 \(S_n\) 同时对 \(T,T^*\) 不变，则 \(S_n^\perp\) 对 \(T\) 不变。壳层
\[
E_n=S_n\cap S_{n-1}^\perp
\]
是两个 reducing subspace 的交，故 reducing。不同 reducing 正交块之间的块矩阵为零。\(\square\)

因此一旦研究量子动力学、谱算子或观察更新，维数序列不再足够。必须保留
\[
\boxed{
P_iTP_j
}
这些跨层耦合。它们描述：

- 已知层是否向余空间泄漏；
- 余空间是否反向影响已知层；
- 壳层之间是否发生跃迁；
- 过滤是否真正形成闭合有效动力学。

这与本文前面对角自然性审计一致：只保存商空间的对象类型，而不保存算子如何穿过投影，无法判断局部—整体动力学是否交换。

## 28.17 Hilbert 商余塔与观察者完成的接口

把有限观察定义为
\[
q_n:\mathscr H\to S_n,
\qquad
q_n=P_n.
\]
其不可见纤维为
\[
q_n^{-1}(s)=s+R_n.
\]
所以
\[
\ker q_n=R_n.
\]
观察者只能区分商
\[
\mathscr H/R_n
\cong S_n.
\]
随着 \(n\) 增加，核递减：
\[
R_0\supseteq R_1\supseteq\cdots,
\]
可见空间递增：
\[
S_0\subseteq S_1\subseteq\cdots.
\]

这与有限集合上的 Nerode 细化具有共同图式：观察核逐步缩小，可区分类逐步增加。但两者仍有重要区别：

1. 有限集合关系格在有限步后必稳定；无限维 Hilbert 投影塔一般只在极限中强收敛；
2. 有限预测完成的商类数是整数并有 \(|Y|-|O|\) 界；Hilbert 维数可以保持无限不变；
3. Hilbert 有限切片的最坏情形盲区恒为一，尽管逐向量误差趋零；
4. Hilbert 完成需要平方可和／有界能量条件；集合关系完成不携带范数；
5. 若有动力学 \(T\)，必须另外检查过滤不变性或近似半共轭。

因此不能把第 19 节的有限稳定定理原样套到无限维 Hilbert 空间。正确替代是：
\[
\boxed{
\text{关系有限步稳定}
\quad\rightsquigarrow\quad
\text{投影强极限与有界能量完成}.
}

## 28.18 最终统一式

本节得到三种“余”的严格统一。

### 代数商余

\[
\boxed{
\mathscr H/S_n
\cong R_n.
}

### 递归商余

\[
\boxed{
R_n
=E_{n+1}\oplus R_{n+1}.
}

### 完成商余

\[
\boxed{
\mathscr H
=
S_0
\oplus_2
\bigoplus_{n\ge1}E_n
\oplus R_\infty.
}

并且有限坐标完成满足
\[
\boxed{
\mathscr H/R_\infty
\cong
\varprojlim_{\!b}S_n.
}

所以“从无限空间中不断扣除有限对象”的准确结构不是把无限数值逐次做减法，而是：
\[
\boxed{
\text{选择有限闭子空间}
\longrightarrow
\text{正交分裂}
\longrightarrow
\text{记录商层}
\longrightarrow
\text{更新余空间}
\longrightarrow
\text{以平方可和条件完成全部有限坐标}.
}

无限维余空间在每个有限阶段可以与整体同型；递归的历史却保存在 associated graded、投影过滤与跨层算子块中。若把这些结构全部忘掉，只保留“余空间仍是无限维”这一同构类，整个递归便会坍缩成一个无信息固定点。

## 28.19 严格边界

1. \(\mathscr H-H_0\) 不是合法的 Hilbert 空间运算；必须先指定嵌入并使用正交补或商。
2. 直接重复正交补只产生闭包后二周期，不会自动生成无限层级。
3. 每一轮新切片都需要额外选择结构；裸 Hilbert 空间没有酉自然的首选逃逸向量。
4. 有限维切片仍是连续向量空间；离散性来自壳层标签或投影测量结果，而不是有限维本身。
5. \(M^\perp\cong\mathscr H\) 是非规范酉同构，不是子空间相等，也不允许删除嵌入账本。
6. 强算子收敛不等于算子范数收敛；有限层对每个固定向量可渐近完备，同时仍有单位范数的最坏盲区。
7. 普通有限坐标逆极限包含无限能量形式点；Hilbert 重构需要有界范数或平方可和条件。
8. 裸塔的维数分类在加入动力学、局域性或可观测代数后不再完整；必须保存块耦合。
9. 二元投影概率是标准 Hilbert 测量结构，不证明所有物理离散性都来自同一个商余塔。
10. 本节不把正交逃逸等同于 Cantor/Lawvere 对角化，也不从 Hilbert 维数吸收推出 Riemann 假设、光速信息率或意识模型。

## 28.20 形式化状态

定理 28.1—28.22 及例 28.5、28.19 均给出纸面定义与证明，尚未成为 Lean 真源。适合拆分的数学内核包括：

- 闭子空间商与正交补的等距同构；
- 相对正交余与 orthomodular 分解；
- 有限维抽取后的 Hilbert 维数吸收；
- 无酉自然逃逸选择器；
- 正交商余塔的有限阶段与极限分解；
- 递增投影的强收敛及范数一逃逸；
- 有界 inverse limit 与平方可和增量重构；
- 壳层投影的向量／密度算子概率分解；
- 裸塔的块维数分类；
- 过滤不变性与算子块三角／块对角判据。

在获得 kernel proof term、依赖闭包与冻结收据以前，本节不得标记为 `Closed`。

---

# 29. 追加：以 Hilbert 正交商余塔分析 Riemann 假设

## 29.0 文档地位与结论边界

本节把第 28 节的 Hilbert 正交商余塔用于 Riemann 假设（RH），目标不是把抽象的“无限维余空间”直接宣称为 RH 的证明，而是回答四个严格问题：

1. RH 能否被写成某个完成商中的**目标余类消失**；
2. 有限高度零点核验为什么不能推出全局 RH；
3. Li–Cayley 指标为何能够放大高处零点极小的离线偏移；
4. Weil 正性若要通过有限压缩传递到无限维极限，究竟还缺少什么算子论条件。

本节得到两个层次不同的接口。

第一种是**零点侧的诊断塔**：它把 RH 精确改写为一个 Cayley 对角算子的酉性，但该算子直接由零点定义，因此本身是结构诊断，不是非循环证明。

第二种是**Nyman–Beurling–Báez-Duarte 逼近塔**：它完全由显式分数部分函数生成，并把 RH 精确改写为一个指定目标向量在最终正交余空间中的质量为零。这是本节最直接、非循环且可计算的 Hilbert 商余接口。

本节没有证明最终余质量为零，没有证明 Weil 二次型全局非负，也没有构造 Hilbert–Pólya 自伴算子。所有新增结论均为纸面推导；在获得 Lean proof term、依赖闭包与冻结收据以前，不得标记为 `Closed`。

---

## 29.1 零点 Cayley 算子：RH 是酉性缺陷消失

设 \(\mathcal Z\) 为 Riemann \(\xi\) 函数的非平凡零点多重集。对每个

\[
\rho=\sigma+i\gamma\in\mathcal Z
\]

定义 Cayley–Li 坐标

\[
\boxed{
c_\rho
=
1-\frac1\rho
=
\frac{\rho-1}{\rho}.
}
\]

取零点 Hilbert 空间

\[
\mathscr H_{\mathcal Z}
=
\ell^2(\mathcal Z),
\]

其规范正交基记为 \((e_\rho)_{\rho\in\mathcal Z}\)。在有限支撑向量上定义对角算子

\[
\boxed{
Ce_\rho=c_\rho e_\rho.
}
\]

由于非平凡零点位于临界带 \(0<\sigma<1\)，并且 \(|\gamma|\to\infty\) 时 \(c_\rho\to1\)，该对角算子可按标准方式闭包为有界算子。

### 定理 29.1（Cayley 酉性缺陷公式）

对每个非平凡零点 \(\rho=\sigma+i\gamma\)，

\[
\boxed{
(C^*C-I)e_\rho
=
\delta_\rho e_\rho,
}
\]

其中

\[
\boxed{
\delta_\rho
=
|c_\rho|^2-1
=
\frac{1-2\sigma}{|\rho|^2}.
}
\]

因此下列命题等价：

\[
\boxed{
\mathrm{RH};
}
\]

\[
\boxed{
|c_\rho|=1
\quad
\text{对全部 }\rho\in\mathcal Z;
}
\]

\[
\boxed{
C^*C=I;
}
\]

\[
\boxed{
C\text{ 为酉算子}.
}
\]

#### 证明

直接计算：

\[
|c_\rho|^2
=
\frac{|\rho-1|^2}{|\rho|^2}.
\]

而

\[
|\rho-1|^2
=
(\sigma-1)^2+\gamma^2,
\qquad
|\rho|^2
=
\sigma^2+\gamma^2.
\]

故

\[
|c_\rho|^2-1
=
\frac{(\sigma-1)^2-\sigma^2}{|\rho|^2}
=
\frac{1-2\sigma}{|\rho|^2}.
\]

于是

\[
|c_\rho|=1
\iff
1-2\sigma=0
\iff
\sigma=\frac12.
\]

对全部零点同时成立，恰为 RH。对角算子在每个基向量上的模均为一，当且仅当其为酉算子。 \(\square\)

这一公式把临界线从“零点位置”转换成了“Cayley 演化是否保持 Hilbert 范数”：

\[
\boxed{
\Re\rho=\frac12
\iff
\|Ce_\rho\|=\|e_\rho\|.
}
\]

这与仓库 `SpectralDynamics` 中“临界线—镜像固定—半密度酉性—共振”的形式化接口一致，但这里的 \(C\) 是直接按零点对角化的诊断算子，并未构造独立于零点的 Hilbert–Pólya 动力学。

### 推论 29.2（对数径向缺陷与镜像反号）

定义

\[
\boxed{
\beta_\rho
=
\log|c_\rho|
=
\frac12
\log
\frac{|\rho-1|^2}{|\rho|^2}.
}
\]

则

\[
\boxed{
\mathrm{RH}
\iff
\beta_\rho=0
\quad
\text{对全部 }\rho.
}
\]

对函数方程镜像

\[
\rho^\sharp=1-\overline\rho
\]

有

\[
\boxed{
|c_{\rho^\sharp}|=|c_\rho|^{-1},
\qquad
\beta_{\rho^\sharp}=-\beta_\rho.
}
\]

#### 证明

由

\[
c_{\rho^\sharp}
=
\frac{-\overline\rho}{1-\overline\rho}
\]

立即得到模长互为倒数。 \(\square\)

所以一个离线四元轨道不是产生两个独立的“径向偏差”，而是产生一对相反的对数深度

\[
+\beta,
\qquad
-\beta.
\]

这正是本文前述 Li–Cayley 四元贡献中 \(\cosh(n\beta)\) 出现的结构根源。

---

## 29.2 零点高度商余塔与有限核验的严格极限

按非降高度枚举零点多重集：

\[
|\Im\rho_1|
\le
|\Im\rho_2|
\le\cdots.
\]

定义

\[
S_N^{\mathcal Z}
=
\operatorname{span}
(e_{\rho_1},\ldots,e_{\rho_N}),
\]

\[
R_N^{\mathcal Z}
=
(S_N^{\mathcal Z})^\perp,
\]

并令 \(P_N^{\mathcal Z}\) 为 \(S_N^{\mathcal Z}\) 上的正交投影。由于 \(C\) 与缺陷算子

\[
D=C^*C-I
\]

均在零点基下对角化，每个 \(S_N^{\mathcal Z}\) 都是 reducing subspace，因而没有跨壳层块：

\[
P_iDP_j=0
\qquad(i\ne j).
\]

有限高度核验“前 \(N\) 个零点在临界线”恰等价于

\[
\boxed{
P_N^{\mathcal Z}DP_N^{\mathcal Z}=0.
}
\]

### 命题 29.3（有限核验不能消除最终余块）

对任意有限 \(N\)，

\[
P_N^{\mathcal Z}DP_N^{\mathcal Z}=0
\]

只说明已枚举壳层上的缺陷为零；它不给出

\[
P_{R_N^{\mathcal Z}}D
P_{R_N^{\mathcal Z}}=0.
\]

因此任何有限数量的临界线零点核验都不能单独推出 RH。

#### 证明

取任意 \(M>N\)，在 \(R_N^{\mathcal Z}\) 内把某个基向量 \(e_{\rho_M}\) 的对角值改为非零，不影响 \(S_N^{\mathcal Z}\) 上的压缩。抽象地说，有限压缩完全遗忘余空间中的对角数据。 \(\square\)

这里第 28 节的“最坏盲区恒为一”得到一个精确实例：

\[
\|I-P_N^{\mathcal Z}\|_{\mathrm{op}}=1
\]

对每个有限 \(N\) 成立。即使

\[
P_N^{\mathcal Z}x\to x
\]

对每个固定 \(x\) 强收敛，也不存在任何有限阶段在整个单位球上消除余空间。

但零点缺陷还有一个更微妙的性质。由

\[
|\delta_\rho|
=
\frac{|1-2\sigma|}{|\rho|^2}
\le
\frac1{|\rho|^2}
\]

可见，高处离线零点在原始 Cayley 酉性中只产生很小的缺陷。若按高度枚举，则 \(D\) 的对角值趋于零，故 \(D\) 是紧对角算子。

因此：

\[
\boxed{
\text{高处离线零点可以具有任意小的单步酉性缺陷，}
}
\]

而

\[
\boxed{
\text{“缺陷很小”与“缺陷严格为零”不是同一命题。}
}
\]

这解释了为什么提高零点核验高度虽然强烈增加证据，却不能通过连续极限自动把 RH 的等式条件证明出来。

---

## 29.3 Li–Cayley 放大：为什么需要 \((n,T)\) 联合控制

写

\[
c_\rho=e^{\beta_\rho+i\theta_\rho}.
\]

对函数方程与共轭生成的完整四元轨道，本文既有约定下的第 \(n\) 个 Li–Cayley 轨道贡献为

\[
\boxed{
L_n(\rho)
=
4-4\cosh(n\beta_\rho)\cos(n\theta_\rho).
}
\]

在临界线上，

\[
\beta_\rho=0,
\]

故单轨道贡献化为

\[
\boxed{
L_n(\rho)
=
4-4\cos(n\theta_\rho)
=
8\sin^2\frac{n\theta_\rho}{2}
\ge0.
}
\]

离线时 \(\beta_\rho\ne0\)，径向因子变为

\[
\cosh(n\beta_\rho),
\]

其大小随 \(n|\beta_\rho|\) 增长。

当 \(|\gamma|\) 很大时，

\[
\beta_\rho
=
\frac12
\log
\left(
1+\frac{1-2\sigma}{\sigma^2+\gamma^2}
\right),
\]

所以在小偏移区间有尺度关系

\[
\boxed{
|\beta_\rho|
\asymp
\frac{|1-2\sigma|}{2\gamma^2}.
}
\]

因此让 \(n|\beta_\rho|\) 达到常数量级所需的 Li 指标大致为

\[
\boxed{
n
\asymp
\frac{2\gamma^2}{|1-2\sigma|}.
}
\]

这不是“第 \(n\) 个 Li 系数必在该位置变负”的断言，因为相位 \(\theta_\rho\)、其他零点轨道与正则化尾项仍会共同作用；它给出的是一个严格的**径向放大尺度**：

\[
\boxed{
\text{零点越高、离线越浅，所需的 Li 频率通常越大。}
}
\]

所以完整证明不能只做以下任一种单参数极限：

\[
T\to\infty
\quad
\text{而固定 }n,
\]

或

\[
n\to\infty
\quad
\text{而固定零点截断 }T.
\]

真正需要控制的是对称正则化后的联合余项

\[
\mathcal R_{n,T}
=
\sum_{|\Im\rho|>T}^{\mathrm{sym}}
\left[
1-
\left(1-\frac1\rho\right)^n
\right],
\]

并在 \(n\) 可随 \(T\) 增长的区域内给出统一估计。至少需要覆盖能够分辨

\[
|\beta_\rho|
\sim T^{-2}
\]

的尺度，因此不能把 \(n\) 与 \(T\) 完全解耦。

这精确说明了本文摘要中“从局部离线轨道暴露到全局 Li 系数负性仍缺 \((n,T)\) 联合截断估计”的含义。仓库 `LiCausalTrichotomy` 已形式化 Li 测试核的整数指标、因果实现与 Cayley monodromy 三分，但它没有证明全部 Li 系数非负；`WeilIdentity` 已形式化显式公式，但没有附加 Weil 正性或 RH 结论。

---

## 29.4 非循环主接口：Nyman–Beurling 目标余质量

定义分数部分函数

\[
\varrho(t)=t-\lfloor t\rfloor.
\]

取

\[
\mathscr H_{\mathrm{NB}}
=
L^2(0,\infty),
\]

目标向量

\[
\boxed{
\chi=\mathbf1_{(0,1)},
\qquad
\|\chi\|_2^2=1,
}
\]

以及显式算术生成元

\[
\boxed{
f_a(x)
=
\varrho\left(\frac1{ax}\right),
\qquad
a\in\mathbb N_{\ge1}.
}
\]

定义嵌套有限维子空间

\[
S_N
=
\operatorname{span}(f_1,\ldots,f_N),
\]

\[
R_N=S_N^\perp,
\]

\[
S_\infty
=
\overline{\bigcup_{N\ge1}S_N},
\]

\[
R_\infty
=
S_\infty^\perp
=
\bigcap_{N\ge1}R_N.
\]

Báez-Duarte 的强 Nyman–Beurling 判据给出

\[
\boxed{
\mathrm{RH}
\iff
\chi\in S_\infty.
}
\]

第 28 节的商—正交余同构立即把它变成一个精确的商余命题。

### 定理 29.4（Nyman–Beurling 目标余类判据）

下列命题等价：

\[
\boxed{
\mathrm{RH};
}
\]

\[
\boxed{
\chi\in S_\infty;
}
\]

\[
\boxed{
[\chi]=0
\quad
\text{于 }
\mathscr H_{\mathrm{NB}}/S_\infty;
}
\]

\[
\boxed{
P_{R_\infty}\chi=0;
}
\]

\[
\boxed{
\operatorname{dist}(\chi,S_N)\longrightarrow0.
}
\]

#### 证明

第一与第二项是强 Nyman–Beurling–Báez-Duarte 判据。第二与第三项由商空间零类定义等价。由第 28 节的规范等距同构

\[
\mathscr H_{\mathrm{NB}}/S_\infty
\cong
R_\infty,
\]

商类 \([\chi]\) 对应唯一正交余代表

\[
P_{R_\infty}\chi.
\]

故第三与第四项等价。最后，对递增闭子空间 \(S_N\)，投影 \(P_{S_N}\) 强收敛到 \(P_{S_\infty}\)，所以

\[
\operatorname{dist}(\chi,S_N)
=
\|(I-P_{S_N})\chi\|
\longrightarrow
\|(I-P_{S_\infty})\chi\|
=
\|P_{R_\infty}\chi\|.
\]

故第四与第五项等价。 \(\square\)

这里必须强调：

\[
\boxed{
\mathrm{RH}
\text{ 不要求 }
R_\infty=\{0\}.
}
\]

它只要求指定目标 \(\chi\) 没有最终余分量：

\[
\boxed{
P_{R_\infty}\chi=0.
}
\]

因此不能把 RH 错写成“全部 Nyman–Beurling 生成元在整个 \(L^2\) 中稠密”。正确命题是目标特定的：

\[
\boxed{
\chi
\text{ 属于生成闭包}.
}
\]

这一区分是商余塔用于 RH 时最重要的类型边界。

---

## 29.5 正交壳层能量：RH 是目标质量被有限算术层完全吸收

令

\[
E_1=S_1,
\]

\[
E_{N+1}
=
S_{N+1}\cap S_N^\perp
\qquad(N\ge1),
\]

并令

\[
Q_N=P_{E_N},
\qquad
Q_\infty=P_{R_\infty}.
\]

则

\[
S_\infty
=
\bigoplus_{N\ge1}^{\ell^2}E_N,
\]

以及

\[
\mathscr H_{\mathrm{NB}}
=
\left(
\bigoplus_{N\ge1}^{\ell^2}E_N
\right)
\oplus
R_\infty.
\]

定义有限阶段剩余误差

\[
\boxed{
d_N
=
\operatorname{dist}(\chi,S_N)
=
\|P_{R_N}\chi\|.
}
\]

### 定理 29.5（壳层递推与最终余质量）

对全部 \(N\ge1\)，

\[
\boxed{
d_N^2
=
d_{N+1}^2
+
\|Q_{N+1}\chi\|^2.
}
\]

并且

\[
\boxed{
d_N^2
=
\sum_{k>N}\|Q_k\chi\|^2
+
\|Q_\infty\chi\|^2.
}
\]

特别地，

\[
\boxed{
1
=
\sum_{k\ge1}\|Q_k\chi\|^2
+
\|Q_\infty\chi\|^2.
}
\]

因此

\[
\boxed{
\mathrm{RH}
\iff
\|Q_\infty\chi\|^2=0
\iff
\sum_{k\ge1}\|Q_k\chi\|^2=1.
}
\]

#### 证明

由相对正交余分解，

\[
R_N
=
E_{N+1}\oplus R_{N+1}.
\]

故

\[
P_{R_N}\chi
=
Q_{N+1}\chi
+
P_{R_{N+1}}\chi
\]

是正交和。Pythagoras 给出第一式。迭代至 \(M>N\)：

\[
d_N^2
=
\sum_{k=N+1}^{M}\|Q_k\chi\|^2
+
d_M^2.
\]

令 \(M\to\infty\)。递减闭子空间投影满足

\[
P_{R_M}\chi\to P_{R_\infty}\chi,
\]

故得到第二式。取初始零空间 \(S_0=\{0\}\)，有 \(d_0^2=\|\chi\|^2=1\)，得到总能量式。最后应用定理 29.4。 \(\square\)

这给出 RH 的概率式读法。对单位目标态 \(\chi\)，壳层权重

\[
p_k=\|Q_k\chi\|^2,
\qquad
p_\infty=\|Q_\infty\chi\|^2
\]

组成概率分布，而

\[
\boxed{
\mathrm{RH}
\iff
p_\infty=0.
}
\]

它不是“所有未知方向消失”，而是：

\[
\boxed{
\text{目标 }\chi\text{ 的全部 Hilbert 质量最终进入有限算术壳层。}
}
\]

---

## 29.6 Gram–Schur 证书：每一轮到底吸收了多少目标质量

令

\[
V_N:\mathbb C^N\to\mathscr H_{\mathrm{NB}},
\qquad
V_Nc=\sum_{a=1}^{N}c_af_a.
\]

定义 Gram 矩阵与目标相关向量

\[
\boxed{
G_N
=
V_N^*V_N
=
\bigl(\langle f_a,f_b\rangle\bigr)_{a,b\le N},
}
\]

\[
\boxed{
b_N
=
V_N^*\chi
=
\bigl(\langle f_a,\chi\rangle\bigr)_{a\le N}.
}
\]

记 \(G_N^\dagger\) 为 Moore–Penrose 逆。

### 定理 29.6（有限阶段最优距离公式）

有

\[
\boxed{
P_{S_N}
=
V_NG_N^\dagger V_N^*,
}
\]

以及

\[
\boxed{
d_N^2
=
1-b_N^*G_N^\dagger b_N.
}
\]

若 \(G_N\) 可逆，则

\[
\boxed{
d_N^2
=
1-b_N^*G_N^{-1}b_N.
}
\]

#### 证明

有限维闭像 \(\operatorname{range}(V_N)=S_N\) 上的正交投影为

\[
V_N(V_N^*V_N)^\dagger V_N^*.
\]

因此

\[
\|P_{S_N}\chi\|^2
=
\langle
V_NG_N^\dagger V_N^*\chi,
\chi
\rangle
=
b_N^*G_N^\dagger b_N.
\]

再由

\[
d_N^2
=
\|\chi\|^2-\|P_{S_N}\chi\|^2
\]

及 \(\|\chi\|^2=1\) 得证。 \(\square\)

目标向量相关项还有显式公式。

### 命题 29.7（目标相关向量的闭式）

对每个整数 \(a\ge1\)，

\[
\boxed{
\langle\chi,f_a\rangle
=
\frac{\log a+1-\gamma_{\mathrm E}}{a},
}
\]

其中 \(\gamma_{\mathrm E}\) 为 Euler 常数。

#### 证明

有

\[
\langle\chi,f_a\rangle
=
\int_0^1
\varrho\left(\frac1{ax}\right)\,dx.
\]

令 \(t=1/(ax)\)，得

\[
\langle\chi,f_a\rangle
=
\frac1a
\int_{1/a}^{\infty}
\frac{\varrho(t)}{t^2}\,dt.
\]

在区间 \([1/a,1]\) 上 \(\varrho(t)=t\)，故该部分为 \(\log a\)。另一方面，

\[
\int_1^\infty\frac{\varrho(t)}{t^2}\,dt
=
\sum_{n\ge1}
\int_n^{n+1}
\frac{t-n}{t^2}\,dt
=
1-\gamma_{\mathrm E}.
\]

合并即得。 \(\square\)

现在定义新生成元相对于既有空间的创新分量：

\[
r_{N+1}
=
(I-P_{S_N})f_{N+1}.
\]

若 \(r_{N+1}\ne0\)，则

\[
E_{N+1}
=
\operatorname{span}(r_{N+1}).
\]

### 定理 29.8（单步 Schur 增益）

若 \(r_{N+1}\ne0\)，则

\[
\boxed{
d_N^2-d_{N+1}^2
=
\frac{
|\langle\chi,r_{N+1}\rangle|^2
}{
\|r_{N+1}\|^2
}.
}
\]

若 \(r_{N+1}=0\)，则 \(d_{N+1}=d_N\)。

#### 证明

当 \(r_{N+1}\ne0\) 时，

\[
e_{N+1}
=
\frac{r_{N+1}}{\|r_{N+1}\|}
\]

是 \(E_{N+1}\) 的单位基，所以

\[
\|Q_{N+1}\chi\|^2
=
|\langle\chi,e_{N+1}\rangle|^2
=
\frac{
|\langle\chi,r_{N+1}\rangle|^2
}{
\|r_{N+1}\|^2
}.
\]

应用定理 29.5。 \(\square\)

因此每个整数 \(N+1\) 对 RH 逼近所提供的真实新信息，不由原函数 \(f_{N+1}\) 的范数决定，而由它在此前全部生成元之外的正交创新

\[
r_{N+1}
\]

以及该创新与目标 \(\chi\) 的耦合决定。

若 \(G_N\) 可逆，还可写成 Gram 行列式证书：

\[
\boxed{
d_N^2
=
\frac{
\det
\begin{pmatrix}
G_N & b_N\\
b_N^* & 1
\end{pmatrix}
}{
\det G_N
}.
}
\]

这把 RH 转化为一列有限维 Gram–Schur 余量的极限消失，但极限消失本身仍需要独立的全局估计。

---

## 29.7 Mellin–Plancherel 图像：余质量就是 \(1-\zeta A_N\) 的加权误差

对适当的 \(f\in L^2(0,\infty)\)，取 Mellin 变换

\[
\mathcal Mf(s)
=
\int_0^\infty f(x)x^{s-1}\,dx.
\]

在临界线

\[
s=\frac12+it
\]

上，Mellin–Plancherel 把 \(L^2(0,\infty)\) 等距映到 \(L^2(\mathbb R,dt/2\pi)\)。

目标向量满足

\[
\boxed{
\mathcal M\chi(s)=\frac1s.
}
\]

而对 \(0<\Re s<1\)，

\[
\int_0^\infty
\varrho(t)t^{-s-1}\,dt
=
-\frac{\zeta(s)}s.
\]

由缩放得到

\[
\boxed{
\mathcal Mf_a(s)
=
-\frac{\zeta(s)}{s\,a^s}.
}
\]

令

\[
A_N(s)
=
\sum_{a=1}^{N}c_aa^{-s}.
\]

则某个有限线性组合的 Mellin 像为

\[
-\frac{\zeta(s)}sA_N(s).
\]

改变系数整体符号后，最优距离可写成

\[
\boxed{
d_N^2
=
\inf_{A_N}
\frac1{2\pi}
\int_{-\infty}^{\infty}
\left|
1-\zeta\left(\frac12+it\right)
A_N\left(\frac12+it\right)
\right|^2
\frac{dt}{\frac14+t^2},
}
\]

其中下确界遍历长度不超过 \(N\) 的 Dirichlet 多项式

\[
A_N(s)=\sum_{a\le N}c_aa^{-s}.
\]

因此 Nyman–Beurling 最终余质量可以写成

\[
\boxed{
\|Q_\infty\chi\|^2
=
\lim_{N\to\infty}
\inf_{A_N}
\frac1{2\pi}
\int_{-\infty}^{\infty}
|1-\zeta(s)A_N(s)|^2
\frac{dt}{|s|^2},
\quad
s=\frac12+it.
}
\]

于是

\[
\boxed{
\mathrm{RH}
\iff
\zeta(s)
\text{ 在该加权临界线空间中拥有 Dirichlet 多项式近逆}.
}
\]

这不是逐点逼近 \(1/\zeta(s)\)。临界线零点处逐点逆不存在，而 \(L^2\) 判据只要求加权均方误差趋零。真正困难的是证明存在一列显式 Dirichlet 多项式，使这一全局均方误差具有趋零上界。

该公式还把 Gram 矩阵写成零点与素数共同作用的相关矩阵：

\[
\boxed{
(G_N)_{ab}
=
\frac1{2\pi}
\int_{-\infty}^{\infty}
\frac{
\left|
\zeta\left(\frac12+it\right)
\right|^2
}{
\frac14+t^2
}
a^{-\frac12-it}
b^{-\frac12+it}
\,dt.
}
\]

所以第 29.6 节的正交创新并非纯粹数值线性代数对象；它编码了临界线上的 \(|\zeta|^2\) 加权频率相关。

---

## 29.8 为什么有限数值逼近仍然不是证明

若某个有限 \(N\) 给出

\[
d_N\ll1,
\]

它只提供上界

\[
\|Q_\infty\chi\|
\le d_N,
\]

不能给出严格等式

\[
\|Q_\infty\chi\|=0.
\]

即使计算得到一条长序列

\[
d_{N_1}>d_{N_2}>\cdots
\]

并呈现明显趋零趋势，仍可能存在一个不可见的正极限

\[
d_\infty
=
\|Q_\infty\chi\|
>0.
\]

另一方面，第 28 节的算子范数障碍

\[
\|I-P_{S_N}\|_{\mathrm{op}}=1
\]

并不直接否定 Nyman–Beurling 路线，因为 RH 只要求逼近一个固定目标 \(\chi\)，不要求 \(P_{S_N}\) 在整个单位球上一致逼近恒等算子。

正确边界是：

\[
\boxed{
\text{全空间一致逼近不可能，}
}
\]

但

\[
\boxed{
\text{单一目标的强逼近仍可能成立。}
}
\]

要把数值证据升级为证明，必须构造一列可验证系数 \(c_{a,N}\)，并给出完全无条件的显式误差界

\[
\boxed{
\left\|
\chi-\sum_{a\le N}c_{a,N}f_a
\right\|_2^2
\le
\varepsilon_N,
\qquad
\varepsilon_N\longrightarrow0.
}
\]

或者在 Mellin 图像中证明

\[
\boxed{
\frac1{2\pi}
\int_{\mathbb R}
|1-\zeta(\tfrac12+it)A_N(\tfrac12+it)|^2
\frac{dt}{\frac14+t^2}
\le
\varepsilon_N
\longrightarrow0.
}
\]

任何真正建立该估计的无条件论证都会通过强 Nyman–Beurling 判据证明 RH；因此不能把目标误差趋零作为未经证明的“正则性假设”重新命名。

---

## 29.9 Weil 正性：有限压缩向无限极限传递所需的 form-core 条件

设 \(\mathcal D\) 为 Weil 测试函数的稠密定义域，\(q_W\) 为对应 Hermitian 二次型。经典 Weil 判据把 RH 与适当测试类上的全局正性联系：

\[
\boxed{
\mathrm{RH}
\iff
q_W(f)\ge0
\quad
\text{对全部允许测试 }f.
}
\]

仓库 `WeilIdentity` 已形式化零点和、素数项、极点项与 Archimedean 项之间的显式公式，但明确没有附加正性或 RH 断言。

若要把第 28 节的正交塔用于 Weil 正性，必须先在**不假设 RH** 的情况下给出一个 Hilbert 空间 \(\mathscr H_W\) 与可闭二次型 \(q_W\)，再选择递增有限维子空间

\[
S_1^W\subseteq S_2^W\subseteq\cdots\subseteq\mathcal D.
\]

只证明每个有限压缩非负：

\[
q_W(f)\ge0
\qquad
(f\in S_N^W)
\]

还不够。需要证明

\[
\bigcup_NS_N^W
\]

在二次型范数中是 form core。

### 定理 29.9（form-core 正性传递）

设 \(q\) 是稠密定义、闭合且下半有界的 Hermitian 二次型。若

\[
\mathcal C=\bigcup_NS_N
\]

是 \(q\) 的 form core，并且

\[
q(f)\ge0
\qquad
(f\in\mathcal C),
\]

则

\[
\boxed{
q(f)\ge0
\qquad
(f\in\operatorname{Dom}q).
}
\]

#### 证明

对任意 \(f\in\operatorname{Dom}q\)，由 form-core 性存在 \(f_n\in\mathcal C\)，使 \(f_n\to f\) 于二次型范数。闭合二次型在该拓扑下连续，故

\[
q(f_n)\to q(f).
\]

每个 \(q(f_n)\ge0\)，于是 \(q(f)\ge0\)。 \(\square\)

这揭示了有限 Weil 矩阵路线的准确缺口：

\[
\boxed{
\text{有限压缩正性}
+
\text{Hilbert 范数稠密}
\quad
\text{仍不足};
}
\]

必须有

\[
\boxed{
\text{二次型范数稠密／form-core 完备性}.
}
\]

此外，若把相关算子按壳层写成

\[
A_{N+1}
=
\begin{pmatrix}
A_N&C_N\\
C_N^*&D_N
\end{pmatrix},
\]

仅有

\[
A_N\ge0,
\qquad
D_N\ge0
\]

不能推出整个块矩阵非负。最简单的反例是

\[
\begin{pmatrix}
1&2\\
2&1
\end{pmatrix},
\]

其两个对角块均正，但存在特征值 \(-1\)。

在 \(A_N\) 可逆的理想情形，正确的新增壳层条件是 Schur 余量

\[
\boxed{
D_N-C_N^*A_N^{-1}C_N\ge0.
}
\]

半正定情形需把逆替换为 Moore–Penrose 逆，并加入相应的像空间兼容条件。

这正是第 28 节“加入动力学后必须保留全部 \(P_iTP_j\) 块”的 RH 版本：只检查每个壳层自身的正性，会遗漏跨壳层耦合制造的负方向。

---

## 29.10 三条路线的逻辑地位

### 零点 Cayley 塔

它给出最直接的等价：

\[
\mathrm{RH}
\iff
C^*C-I=0.
\]

优点是零点离线深度、镜像反号、Li 放大与有限高度盲区全部透明。缺点是 \(C\) 直接由零点构造，因此只是诊断坐标，不是独立证明机制。

### Nyman–Beurling 目标余塔

它给出：

\[
\mathrm{RH}
\iff
P_{R_\infty}\chi=0.
\]

生成元 \(f_a\) 完全显式，有限阶段可由 Gram–Schur 算法计算，逻辑上非循环。真正缺口是无条件证明目标余质量趋零。

### Weil 压缩塔

它试图把 RH 变成一个全局正算子或正二次型命题。该路线最接近谱解释，但必须解决：

\[
\text{无条件 Hilbert 实现},
\]

\[
\text{二次型可闭性},
\]

\[
\text{form-core 完备性},
\]

\[
\text{跨壳层耦合},
\]

\[
\text{最终余块正性}.
\]

不能先用 Weil 正性定义内积，再以所得 Hilbert 范数证明 Weil 正性；那会把 RH 作为正定性的前提隐藏进空间构造中。

---

## 29.11 本框架识别出的真正“证明心脏”

第 28 节本身提供的是完备的记账语言：

\[
S_N,
\qquad
E_{N+1},
\qquad
R_N,
\qquad
R_\infty,
\qquad
P_iTP_j.
\]

它不会凭空生成 RH 所需的解析估计。用于 RH 后，缺失心脏可以被压缩成以下三种等价风格之一。

### 目标余质量消失

证明

\[
\boxed{
\|P_{R_\infty}\chi\|=0
}
\]

于 Nyman–Beurling 塔。

### 显式 Dirichlet 近逆

构造 \(A_N\) 并证明

\[
\boxed{
\int_{\mathbb R}
|1-\zeta(\tfrac12+it)A_N(\tfrac12+it)|^2
\frac{dt}{\frac14+t^2}
\longrightarrow0.
}
\]

### Weil form-core 正性

构造无条件闭合 Weil 型二次型 \(q_W\)，证明一列有限压缩形成 form core，并控制每个 Schur 余量及最终余块，从而得到

\[
\boxed{
q_W\ge0.
}
\]

三者都不是由“无限维余空间与原空间同型”推出。相反，第 28 节告诉我们为什么这种同型没有证明力：若忘记嵌入、壳层、目标向量与算子块，只剩

\[
R_N\cong\mathscr H,
\]

整个递归会坍缩成无信息固定点。

真正可能产生证明进展的对象是：

\[
\boxed{
\text{目标在每个正交创新层上的精确耦合}
}
\]

以及

\[
\boxed{
\text{这些耦合的可求和全局尾界}.
}
\]

---

## 29.12 可形式化拆分

建议把本节拆成以下 Lean 模块，按依赖顺序推进。

1. `CayleyZeroDefect`
   \[
   |(\rho-1)/\rho|^2-1
   =
   (1-2\Re\rho)/|\rho|^2.
   \]

2. `DiagonalUnitaryCriticalLine`
   \[
   C^*C=I
   \iff
   \forall\rho,\ \Re\rho=\frac12.
   \]

3. `NestedProjectionResidual`
   \[
   R_N=E_{N+1}\oplus R_{N+1},
   \qquad
   d_N^2=d_{N+1}^2+\|Q_{N+1}\chi\|^2.
   \]

4. `TargetQuotientVanishing`
   \[
   [\chi]=0\text{ in }\mathscr H/S_\infty
   \iff
   P_{S_\infty^\perp}\chi=0.
   \]

5. `FiniteGramProjection`
   \[
   d_N^2
   =
   \|\chi\|^2-b_N^*G_N^\dagger b_N.
   \]

6. `OneStepGramSchurGain`
   \[
   d_N^2-d_{N+1}^2
   =
   |\langle\chi,r_{N+1}\rangle|^2/\|r_{N+1}\|^2.
   \]

7. `ClosedFormCorePositivity`
   有限 core 上的非负性向闭合二次型定义域传递。

8. `PositiveDiagonalBlocksInsufficient`
   形式化二维块矩阵反例。

Nyman–Beurling–Báez-Duarte 等价本身依赖经典解析数论结果；在仓库完成该桥以前，应作为明确命名、来源可审计的外部定理接口，而不是把它悄然作为无名公理嵌入。

---

## 29.13 最终结论

Hilbert 正交商余塔对 RH 的最强严格结论不是“无限递归迫使零点上临界线”，而是以下目标化等价：

\[
\boxed{
\mathrm{RH}
\iff
[\chi]=0
\text{ 于 }
L^2(0,\infty)/
\overline{\operatorname{span}}
\left\{
\varrho\left(\frac1{ax}\right):a\in\mathbb N
\right\}.
}
\]

通过商—正交余同构，它等价于

\[
\boxed{
\mathrm{RH}
\iff
P_{R_\infty}\chi=0.
}
\]

通过壳层能量分解，它又等价于

\[
\boxed{
\mathrm{RH}
\iff
\sum_{k\ge1}\|Q_k\chi\|^2=1.
}
\]

通过 Mellin–Plancherel，它等价于

\[
\boxed{
\inf_{A_N}
\int_{\mathbb R}
|1-\zeta(\tfrac12+it)A_N(\tfrac12+it)|^2
\frac{dt}{\frac14+t^2}
\longrightarrow0.
}
\]

零点侧则有诊断等价

\[
\boxed{
\mathrm{RH}
\iff
C^*C=I,
\qquad
Ce_\rho=\left(1-\frac1\rho\right)e_\rho.
}
\]

这四个公式共同揭示同一结构：

\[
\boxed{
\text{RH 不是“余空间不存在”，而是“指定的离线／逼近缺陷在完成后没有剩余质量”。}
}
\]

第 28 节已经提供了精确的商余账本；剩余的数学核心是建立一个无条件、可求和、能穿过无限完成的全局尾估计。缺少该估计时，有限零点核验、有限 Gram 矩阵正性、局部 Li 轨道暴露与有限 Weil 压缩都只能构成证据或等价重述，不能单独完成 RH 的证明。

## 29.14 参考接口

- L. Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the Riemann Hypothesis*, 2002.
- X.-J. Li, *The positivity of a sequence of numbers and the Riemann hypothesis*, 1997.
- A. Connes and C. Consani, *Weil positivity and Trace formula, the archimedean place*, 2020.
- M. Suzuki, *Li coefficients as norms of functions in a model space*, 2023.
- M. Suzuki, *Weil's quadratic form via the screw function*, 2026.
- 仓库接口：`D5/S3/Weil/WeilIdentity.lean`、`D5/S3/Weil/SpectralDynamics.lean`、`D5/S3/Analytic/LiCausalTrichotomy.lean`。

## 29.15 严格非主张与形式化状态

1. 本节没有证明 \(P_{R_\infty}\chi=0\)。
2. 本节没有从有限 \(d_N\) 数值趋降推出其极限为零。
3. 本节没有从有限高度零点全部位于临界线推出不存在更高离线零点。
4. 本节没有把由零点定义的 Cayley 对角算子冒充为独立构造的 Hilbert–Pólya 算子。
5. 本节没有证明局部离线四元贡献必在某个预先给定的 \(n\) 上使全局 Li 系数为负。
6. 本节没有证明有限 Weil 压缩自动形成 form core。
7. 本节没有以 Weil 正性先定义 Hilbert 内积再循环证明 Weil 正性。
8. 本节全部新增定理均为纸面结论；未经 kernel verification 不得标记为 `Closed`。
---

# 30. 追加：界面相对性、对角闭合与量子上下文完成

## 30.0 核心命题与严格边界

本节把此前关于

\[
\infty,\qquad
\text{对角化},\qquad
\text{商余},\qquad
\text{Hilbert 投影},\qquad
\text{量子概率}
\]

的讨论收紧为一个共同数学问题：

\[
\boxed{
\text{整体结构如何相对于一个有限界面被识别、遗忘、演化、逃逸与完成？}
}
\]

这里的“相对性”不是主观任意性，而是以下数据的依赖性：

1. 哪个映射被选作观察界面；
2. 哪些对象被该界面识别为同一对象；
3. 哪些差异进入核、纤维或正交余空间；
4. 整体操作能否下降为界面上的有效操作；
5. 不同界面之间能否自然转换；
6. 所有有限界面的相容数据是否来自一个可实现的整体对象；
7. 一个状态在不可见余空间中是否仍保留非零质量。

本节得到的统一解释是：

\[
\boxed{
\begin{aligned}
\text{商}
&=\text{相对于界面保留的同一性},\\
\text{余}
&=\text{相对于界面被删除的差异},\\
\text{对角化}
&=\text{相对描述无法封闭自身的证书},\\
\infty
&=\text{不存在有限终止界面，但相容界面族可以完成},\\
\text{概率}
&=\text{状态对界面事件的标量评价},\\
\text{量子性}
&=\text{局部经典界面不能统一拼成单一全局 Boolean 界面}.
\end{aligned}
}
\]

本节不主张一切物理相对性均等同于商空间，不把量子理论还原为一个裸无限维 Hilbert 空间，也不把上下文性、Bell 非局域性、退相干和测量问题混成同一个定理。新增结果均为纸面推导；未经 Lean proof term、依赖闭包与冻结收据不得标记为 `Closed`。

---

## 30.1 界面系统、相对同一性与观察偏序

### 定义 30.1（观察界面）

设 \(X\) 为整体对象空间。一个观察界面是映射

\[
q_i:X\to X_i.
\]

它在 \(X\) 上诱导等价关系

\[
\boxed{
x\sim_i y
\iff
q_i(x)=q_i(y).
}
\]

若把 \(X_i\) 替换为实际像 \(q_i(X)\)，则有规范双射

\[
\boxed{
X/{\sim_i}\cong X_i.
}
\]

因此 \(X_i\) 不是一个绝对缩小版的 \(X\)，而是由 \(q_i\) 决定的相对身份空间。

### 定义 30.2（观察精化）

若存在映射

\[
p_{j,i}:X_j\to X_i
\]

满足

\[
\boxed{
q_i=p_{j,i}\circ q_j,
}
\]

则称 \(j\) 比 \(i\) 更精细，记为

\[
j\succeq i.
\]

这表示细界面的读出足以确定粗界面的读出。

### 定理 30.3（相对同一性的反变单调性）

若 \(j\succeq i\)，则

\[
\boxed{
{\sim_j}\subseteq{\sim_i}.
}
\]

并存在唯一满射

\[
\boxed{
\bar p_{j,i}:X/{\sim_j}\twoheadrightarrow X/{\sim_i}
}
\]

使自然商图交换。

#### 证明

若 \(x\sim_jy\)，则 \(q_j(x)=q_j(y)\)。施加 \(p_{j,i}\) 得

\[
q_i(x)=p_{j,i}(q_j(x))
      =p_{j,i}(q_j(y))
      =q_i(y),
\]

故 \(x\sim_i y\)。商映射的存在唯一性由商的泛性质得到。 \(\square\)

所以：

\[
\boxed{
\text{观察越细，被称为“同一”的对象越少；}
}
\]

而：

\[
\boxed{
\text{观察越粗，被遗忘到同一纤维中的差异越多。}
}
\]

### 定义 30.4（相对余量）

一般集合界面 \(q_i\) 的余量不是一个规范对象，而是纤维族

\[
\boxed{
\mathcal R_i(x)=q_i^{-1}(q_i(x)).
}
\]

若 \(X\) 为线性空间且 \(q_i\) 线性，则不可见方向由

\[
\boxed{
\ker q_i
}
\]

统一描述。若 \(X=\mathscr H\) 为 Hilbert 空间且 \(q_i=P_i\) 是正交投影到闭子空间 \(S_i\)，则

\[
\boxed{
\ker P_i=S_i^\perp.
}
\]

此时商与余具有规范等距关系：

\[
\boxed{
\mathscr H/S_i^\perp\cong S_i,
\qquad
\mathscr H/S_i\cong S_i^\perp.
}
\]

因此“隐藏”不是向量的绝对属性，而是向量与所选投影之间的关系。

---

## 30.2 绝对整体是相容关系的闭合，而不是超级界面

设观察指标构成有向偏序 \(I\)，并有逆系

\[
(X_i,p_{j,i})_{j\succeq i}.
\]

定义规范观察映射

\[
\boxed{
\Phi:X\to\varprojlim_iX_i,
\qquad
\Phi(x)=(q_i(x))_i.
}
\]

### 定义 30.5（最终不可分关系）

定义

\[
\boxed{
x\sim_\infty y
\iff
q_i(x)=q_i(y)
\quad
\text{对全部 }i.
}
\]

于是

\[
{\sim_\infty}
=
\bigcap_i{\sim_i}.
\]

### 定理 30.6（分离判据）

规范映射 \(\Phi\) 单射，当且仅当

\[
\boxed{
{\sim_\infty}=\Delta_X,
}
\]

其中 \(\Delta_X\) 为对角相等关系。

在线性情形，这等价于

\[
\boxed{
\bigcap_i\ker q_i=\{0\}.
}
\]

#### 证明

\[
\Phi(x)=\Phi(y)
\iff
q_i(x)=q_i(y)\ \forall i
\iff
x\sim_\infty y.
\]

故 \(\Phi\) 单射恰当且仅当最终不可分关系就是相等。线性情形令 \(y=0\) 即得核交判据。 \(\square\)

### 定义 30.7（形式相容与可实现性）

逆极限中的元素是一族形式相容读出

\[
(x_i)_i,
\qquad
p_{j,i}(x_j)=x_i.
\]

若存在 \(x\in X\) 满足

\[
q_i(x)=x_i
\quad
\forall i,
\]

则称该族可实现。

### 定理 30.8（完成判据）

有规范同构

\[
\boxed{
X/{\sim_\infty}
\cong
\operatorname{im}\Phi
\subseteq
\varprojlim_iX_i.
}
\]

并且

\[
\boxed{
X/{\sim_\infty}
\cong
\varprojlim_iX_i
}
\]

当且仅当每个形式相容族均可实现。

#### 证明

\(\ker\Phi={\sim_\infty}\)，故第一同构定理给出第一式。满射性恰等价于所有逆极限点都来自某个整体对象。 \(\square\)

这表明：

\[
\boxed{
\text{绝对整体不是另一个“最大屏幕”，而是全部相对读出之间的可实现相容闭合。}
}
\]

仅有相容性仍可能不够。第 28 节 Hilbert 塔已经给出反例：普通集合逆极限允许能量无界的形式坐标族；真正的 Hilbert 完成还需

\[
\sup_n\|x_n\|<\infty
\]

或等价的平方可和增量条件。因此在不同范畴中，“可实现”分别携带连续性、有界性、可测性、正性或局域性等附加要求。

---

## 30.3 \(\infty\) 的界面定义：无有限终止与可完成性必须分开

设

\[
S_1\subseteq S_2\subseteq\cdots\subseteq\mathscr H
\]

为有限维闭子空间，投影为 \(P_n\)，余空间为

\[
R_n=S_n^\perp.
\]

### 定义 30.9（有限终止）

若存在有限 \(N\) 使

\[
S_N=\mathscr H,
\]

则观察塔有限终止。

### 定义 30.10（逐态完成）

若对每个固定 \(x\in\mathscr H\)，

\[
P_nx\to x,
\]

则称观察塔逐态完成。

### 定义 30.11（一致完成）

若

\[
\|I-P_n\|_{\mathrm{op}}\to0,
\]

则称观察塔一致完成。

### 定理 30.12（无限维中的三者分离）

若 \(\mathscr H\) 无限维，每个 \(S_n\) 有限维，且

\[
\overline{\bigcup_nS_n}=\mathscr H,
\]

则：

1. 观察塔不在任何有限层终止；
2. 观察塔逐态完成；
3. 观察塔不一致完成，且
   \[
   \boxed{
   \|I-P_n\|_{\mathrm{op}}=1
   \quad
   \forall n.
   }
   \]

#### 证明

有限维真子空间不可能等于无限维空间，故第一项成立。递增闭子空间投影强收敛到闭并投影，闭并为全空间，故 \(P_nx\to x\)。对每个 \(n\)，取单位向量 \(r_n\in R_n\)，则

\[
(I-P_n)r_n=r_n,
\]

所以算子范数至少为一；投影补的范数至多为一，故等号成立。 \(\square\)

因此：

\[
\boxed{
\infty
\text{ 可以被刻画为“任何有限界面都留下余量”，}
}
\]

但这不妨碍

\[
\boxed{
\text{所有相容有限界面在逐态意义下完成整体。}
}
\]

“没有有限终止”与“没有完成”是两个不同命题。

---

## 30.4 对角化是相对自描述的闭合缺陷

设 \(A\) 为地址集合，\(Y\) 为值集合，评价器为

\[
e:A\to Y^A.
\]

第 \(a\) 行 \(e(a)\) 是一个 \(A\)-索引对象。设

\[
\tau:Y\to Y
\]

无不动点：

\[
\tau(y)\ne y
\quad
\forall y.
\]

定义对角逃逸对象

\[
\boxed{
d_e(a)=\tau(e(a)(a)).
}
\]

### 定理 30.13（相对对角逃逸）

有

\[
\boxed{
d_e\notin\operatorname{range}(e).
}
\]

#### 证明

若 \(d_e=e(b)\)，则在 \(b\) 坐标

\[
d_e(b)
=
\tau(e(b)(b))
=
\tau(d_e(b)),
\]

与 \(\tau\) 无不动点矛盾。 \(\square\)

这里有一个重要的相对—绝对分层：

\[
\boxed{
d_e\text{ 的具体内容依赖于名单 }e;
}
\]

但

\[
\boxed{
\text{每个同类型名单都存在逃逸对象}
}
\]

是不依赖特定名单的结构定理。

所以对角化不是在一个绝对空间中寻找固定的“外部对象”，而是：

\[
\boxed{
\text{给定一个自描述界面，由该界面自身构造其相对外部。}
}
\]

### 定义 30.14（界面上的对角自然性）

设值界面

\[
q:Y\to Z
\]

及粗层扭曲

\[
\bar\tau:Z\to Z.
\]

若

\[
q\tau=\bar\tau q,
\]

并逐坐标压缩评价表，则对角操作满足

\[
\boxed{
Q\Delta_\tau
=
\Delta_{\bar\tau}P.
}
\]

若不交换，定义缺陷

\[
\boxed{
\varepsilon^\Delta(E)
=
d\bigl(
Q\Delta_\tau E,
\Delta_{\bar\tau}PE
\bigr).
}
\]

这不是“观察改变一切”的模糊命题，而是一个可测的自然性失败。

### 定理 30.15（商可以完全隐藏对角扭曲）

若

\[
q\tau=q,
\]

则

\[
\boxed{
Q\Delta_\tau(E)
=
QD(E)
}
\]

对所有评价表成立。

#### 证明

逐坐标：

\[
q(\tau(E(a,a)))
=
q(E(a,a)).
\]

\(\square\)

所以一个界面可以得到零自然性缺陷，却完全失去扭曲可见性。这再次证明：

\[
\boxed{
\text{操作交换}
\ne
\text{操作被忠实观察}.
}
\]

需要同时审计分离量

\[
\operatorname{sep}_\tau(q)
=
\inf_{y\notin\operatorname{Fix}\tau}
d(qy,q\tau y).
\]

---

## 30.5 相对性不是任意性：自然变换与不变量

考虑两个界面

\[
q_i:X\to X_i,
\qquad
q_j:X\to X_j
\]

以及转换

\[
p_{j,i}:X_j\to X_i.
\]

若整体动力学为

\[
T:X\to X,
\]

有效动力学为

\[
T_i:X_i\to X_i,
\]

则严格协变条件是

\[
\boxed{
q_iT=T_iq_i.
}
\]

若 \(j\succeq i\)，还要求

\[
\boxed{
p_{j,i}T_j=T_ip_{j,i}.
}
\]

这些交换图保证不同观察者不是各自任意发明规律，而是在重叠可见部分上给出一致描述。

若只近似交换，可定义

\[
\boxed{
\delta_i(T)
=
\sup_{x\in K}
d_i(q_iTx,T_iq_ix)
}
\]

于指定有界状态集 \(K\)。对连续的多尺度链，缺陷按 Lipschitz 常数满足 telescoping bound，这正是本文第 2 节一般缺陷复合定理的观察者版本。

因此一个严格相对理论至少必须同时给出：

\[
\boxed{
\text{界面}
+
\text{界面转换}
+
\text{协变规律}
+
\text{转换不变量}
+
\text{非协变缺陷}.
}
\]

缺少界面转换的“每人有自己的真理”不是数学相对性，而只是不可比较的多重命名。

---

## 30.6 概率是状态—effect 配对，不是投影对象本身

令 \(\mathcal A\) 为含幺 \(C^*\)-代数。一个状态是正的归一化线性泛函

\[
\omega:\mathcal A\to\mathbb C,
\qquad
\omega(I)=1.
\]

一个 effect 是满足

\[
0\le E\le I
\]

的元素。定义事件概率

\[
\boxed{
p_\omega(E)=\omega(E).
}
\]

若 \(E=P=P^*=P^2\)，则 \(P\) 是锐利事件。Hilbert 表示中若

\[
\omega(A)=\operatorname{Tr}(\rho A),
\]

则

\[
\boxed{
p_\rho(P)
=
\operatorname{Tr}(\rho P).
}
\]

纯态 \(\rho=|\psi\rangle\langle\psi|\) 时：

\[
\boxed{
p_\psi(P)
=
\|P\psi\|^2.
}
\]

因此：

\[
\boxed{
\text{投影定义问题，状态定义权重，配对产生概率。}
}
\]

### 定理 30.16（正交可加性）

若 \((P_i)\) 为有限或可数正交投影族，且

\[
\sum_iP_i=I
\]

于强算子拓扑，则

\[
\boxed{
\sum_i\omega(P_i)=1.
}
\]

纯态情形为 Parseval 分解：

\[
\boxed{
\sum_i\|P_i\psi\|^2=\|\psi\|^2.
}
\]

#### 证明

有限情形由线性性。可数情形由正态状态对递增投影和的单调连续性；纯态情形等价于正交分量的 Pythagoras/Parseval。 \(\square\)

概率因此是完整状态经离散投影族后留下的标量质量，但不能把

\[
P_i
\]

与

\[
\omega(P_i)
\]

识别为同一个对象。

---

## 30.7 经典概率也是 Hilbert 投影；量子性来自非交换

设经典概率空间

\[
(\Omega,\Sigma,\mu)
\]

并取

\[
\mathscr H=L^2(\Omega,\mu).
\]

对事件 \(A\in\Sigma\)，定义乘法投影

\[
(P_Af)(\omega)=\mathbf1_A(\omega)f(\omega).
\]

则

\[
P_A^2=P_A=P_A^*,
\]

并且

\[
\boxed{
\mu(A)
=
\langle\mathbf1,P_A\mathbf1\rangle.
}
\]

若 \(\mathcal G\subseteq\Sigma\) 为子 \(\sigma\)-代数，则条件期望

\[
\boxed{
\mathbb E[X\mid\mathcal G]
}
\]

是 \(L^2(\mathcal G)\) 上的正交投影。

所以“概率来自 Hilbert 投影”并不区分经典与量子。真正的差异是：

\[
\boxed{
\text{经典事件投影形成交换 Boolean 代数；}
}
\]

而

\[
\boxed{
\text{量子投影总体形成非分配的 orthomodular 格，且一般不交换。}
}
\]

---

## 30.8 两个投影何时属于同一个经典界面

设 \(P,Q\) 为 Hilbert 空间上的正交投影。

### 定理 30.17（共同四扇区分解判据）

下列条件等价：

1. \(PQ=QP\)；
2. 四个算子
   \[
   PQ,\quad
   P(I-Q),\quad
   (I-P)Q,\quad
   (I-P)(I-Q)
   \]
   都是正交投影；
3. \(\mathscr H\) 有正交分解
   \[
   \boxed{
   \mathscr H
   =
   \operatorname{ran}(PQ)
   \oplus
   \operatorname{ran}(P(I-Q))
   \oplus
   \operatorname{ran}((I-P)Q)
   \oplus
   \operatorname{ran}((I-P)(I-Q)).
   }
   \]
4. 存在一个四结果 PVM \((R_{ab})_{a,b\in\{0,1\}}\)，使
   \[
   P=R_{10}+R_{11},
   \qquad
   Q=R_{01}+R_{11}.
   \]

#### 证明

若 \(P,Q\) 交换，则所有多项式组合仍为自伴幂等元，四项两两正交且和为 \(I\)，得到 2、3、4。

若存在第 4 项，则

\[
PQ
=
(R_{10}+R_{11})(R_{01}+R_{11})
=
R_{11}
=
QP.
\]

故 4 推出 1。其余蕴含由对应投影构造直接得到。 \(\square\)

因此：

\[
\boxed{
PQ=QP
}
\]

恰好意味着两个是／否问题可以被嵌入同一个经典四格界面。

若

\[
PQ\ne QP,
\]

则不存在同时保留二者锐利性的共同 Boolean 精化。量子相对性不是普通坐标变换，因为坐标变换不能把非交换关系消除为交换关系。

---

## 30.9 量子上下文是一张局部经典图

### 定义 30.18（测量上下文）

一个量子上下文是 \(\mathcal A\) 中的最大交换含幺 \(C^*\)-子代数

\[
\mathcal C\subseteq\mathcal A.
\]

有限维时，\(\mathcal C\) 由一族最小正交投影

\[
P_1,\ldots,P_m,
\qquad
\sum_iP_i=I
\]

生成。

状态限制

\[
\omega|_{\mathcal C}
\]

对应经典概率分布

\[
\boxed{
p_i=\omega(P_i).
}
\]

所以：

\[
\boxed{
\text{每一个量子上下文本身都是一个经典概率界面。}
}
\]

不同上下文 \(\mathcal C,\mathcal D\) 在交集

\[
\mathcal C\cap\mathcal D
\]

上必须给出相同限制，因为它们来自同一个全局状态 \(\omega\)。

### 定义 30.19（上下文预层）

对每个上下文 \(\mathcal C\)，令

\[
\mathsf{Val}(\mathcal C)
\]

表示其锐利 \(0/1\) 赋值或更一般的概率赋值集合。若

\[
\mathcal D\subseteq\mathcal C,
\]

则有自然限制映射

\[
\operatorname{res}_{\mathcal C,\mathcal D}:
\mathsf{Val}(\mathcal C)\to\mathsf{Val}(\mathcal D).
\]

局部赋值族 \((v_{\mathcal C})\) 若在所有交集上兼容，就形成一个相容局部截面族。

### 定义 30.20（全局经典化）

若存在一个上下文无关赋值 \(v\)，其对每个 \(\mathcal C\) 的限制均等于 \(v_{\mathcal C}\)，则称该局部族可全局经典化。

Kochen–Specker 型障碍说明，在维数至少三的量子投影结构中，满足函数关系的锐利局部赋值一般不存在全局截面。这里的严格结构是：

\[
\boxed{
\text{每张局部图可以经典化，但全部图不能同时拼平。}
}
\]

因此量子性可以表述为一种相对完成失败：

\[
\boxed{
\text{局部 Boolean 商均存在，全球 Boolean 逆极限点不存在。}
}
\]

该陈述引用经典 Kochen–Specker 结果作为外部数学事实；本节没有重新证明其有限构型。

---

## 30.10 “绝对量子态”不是一个隐藏的全局经典答案表

密度算子 \(\rho\) 确实对每个 effect 给出统一数值

\[
E\mapsto\operatorname{Tr}(\rho E).
\]

但这不是给所有投影预先指定 \(0/1\) 结果。它是一个非交换事件代数上的概率状态。

因此必须区分：

\[
\boxed{
\text{全局量子状态}
}
\]

与

\[
\boxed{
\text{全局经典确定赋值}.
}
\]

前者存在；后者一般不存在。

量子态统一的是所有上下文的**概率兼容性**：

\[
\omega|_{\mathcal C\cap\mathcal D}
\]

从两侧一致。

它不统一为所有上下文中的确定结果同时存在。

所以“绝对是全部相对关系的闭合”在量子理论中的正确版本是：

\[
\boxed{
\text{全局量子状态是所有局部经典概率图在重叠处的一致状态，}
}
\]

而不是：

\[
\boxed{
\text{存在一张隐藏的全局经典样本表。}
}
\]

---

## 30.11 纠缠是局部商无法分配的关联余量

设复合系统

\[
\mathscr H_{AB}
=
\mathscr H_A\otimes\mathscr H_B.
\]

全局状态为 \(\rho_{AB}\)。局部观察界面是限制到子代数

\[
\mathcal A_A\otimes I_B.
\]

其代表密度算子为偏迹

\[
\boxed{
\rho_A=\operatorname{Tr}_B\rho_{AB}.
}
\]

两个全局状态若具有相同 \(\rho_A\)，则相对于所有 \(A\)-局部测量不可区分，即落入同一个局部观察纤维。

### 定理 30.21（纯全局态可投影成混合局部态）

取 Bell 态

\[
|\Phi^+\rangle
=
\frac{|00\rangle+|11\rangle}{\sqrt2}.
\]

则

\[
\rho_{AB}
=
|\Phi^+\rangle\langle\Phi^+|
\]

为秩一纯态，但

\[
\boxed{
\rho_A
=
\operatorname{Tr}_B\rho_{AB}
=
\frac12I_A.
}
\]

#### 证明

展开

\[
\rho_{AB}
=
\frac12(
|00\rangle\langle00|
+
|00\rangle\langle11|
+
|11\rangle\langle00|
+
|11\rangle\langle11|
).
\]

对 \(B\) 偏迹时，交叉项含

\[
\langle1|0\rangle
\quad\text{或}\quad
\langle0|1\rangle
\]

而消失，对角项分别留下 \(|0\rangle\langle0|\) 与 \(|1\rangle\langle1|\)。 \(\square\)

所以局部混合不是必然源于一个预先存在的经典混合，而可以来自：

\[
\boxed{
\text{全局纯关联被局部界面遗忘。}
}
\]

纠缠余量并不属于某个单独局部余空间；它存在于张量因子之间的关联结构中。

---

## 30.12 测量必须拆成概率、记录与条件更新

一个量子仪器由完全正映射族

\[
(\mathcal I_i)_i
\]

组成，且总映射保持迹。定义 effect

\[
E_i=\mathcal I_i^*(I).
\]

对状态 \(\rho\)：

\[
\boxed{
p_i
=
\operatorname{Tr}(\mathcal I_i(\rho))
=
\operatorname{Tr}(\rho E_i).
}
\]

若 \(p_i>0\)，结果 \(i\) 后的条件状态为

\[
\boxed{
\rho_i
=
\frac{\mathcal I_i(\rho)}{p_i}.
}
\]

因此一次测量至少包含三个不同对象：

\[
\boxed{
\begin{aligned}
E_i
&=\text{概率事件},\\
i
&=\text{经典记录标签},\\
\mathcal I_i
&=\text{状态更新规则}.
\end{aligned}
}
\]

仅知道 POVM \((E_i)\) 一般不能唯一决定条件状态更新。

理想 Lüders 投影测量是特殊情形：

\[
\mathcal I_i(\rho)=P_i\rho P_i,
\]

于是

\[
p_i=\operatorname{Tr}(\rho P_i),
\qquad
\rho_i=\frac{P_i\rho P_i}{p_i}.
\]

所以“坍缩”不是概率本身，而是给定记录后的条件状态更新。

---

## 30.13 Naimark 与 Stinespring：相对随机性可由更大空间中的锐利结构实现

### Naimark 扩张

对 POVM

\[
E_i\ge0,
\qquad
\sum_iE_i=I_{\mathscr H},
\]

存在更大 Hilbert 空间 \(\mathscr K\)、等距嵌入

\[
V:\mathscr H\to\mathscr K
\]

及正交投影族 \((\Pi_i)\)，使

\[
\boxed{
E_i=V^*\Pi_iV.
}
\]

因此

\[
\boxed{
\operatorname{Tr}(\rho E_i)
=
\operatorname{Tr}(V\rho V^*\Pi_i).
}
\]

### Stinespring 扩张

对完全正映射

\[
\Phi:\mathcal A\to\mathcal B(\mathscr H),
\]

存在表示 \(\pi\) 与算子 \(V\)，使

\[
\boxed{
\Phi(a)=V^*\pi(a)V.
}
\]

量子通道在 Schrödinger 图像中可写成：

\[
\boxed{
\Phi_*(\rho)
=
\operatorname{Tr}_E
\bigl[
U(\rho\otimes\sigma_E)U^*
\bigr].
}
\]

这说明：

\[
\boxed{
\text{局部的广义测量、噪声与非酉性，可以是更大系统的投影、酉演化与遗忘。}
}
\]

但不能由此推出某个唯一隐藏整体。扩张只在适当最小性意义下唯一到酉等价；系统—环境分解、环境初态与具体实现仍是额外结构。

因此：

\[
\boxed{
\text{“可扩张为确定线性结构”}
\ne
\text{“物理世界已被证明具有唯一经典确定本体”.}
}
\]

---

## 30.14 退相干是相对于上下文的正交投影

设 \((P_i)\) 为完整正交投影族。定义 pinching/dephasing 映射

\[
\boxed{
\mathcal D_P(X)
=
\sum_iP_iXP_i.
}
\]

在有限维 Hilbert–Schmidt 空间

\[
\mathsf{HS}(\mathscr H)
\]

上取内积

\[
\langle X,Y\rangle_{\mathrm{HS}}
=
\operatorname{Tr}(X^*Y).
\]

令

\[
\mathcal B_P
=
\{X:P_iXP_j=0\text{ 当 }i\ne j\}
\]

为相对于该上下文的块对角子空间。

### 定理 30.22（去相干映射是 Hilbert–Schmidt 正交投影）

有

\[
\boxed{
\mathcal D_P^2=\mathcal D_P,
}
\]

\[
\boxed{
\mathcal D_P^*=\mathcal D_P
}
\]

于 Hilbert–Schmidt 内积，并且

\[
\boxed{
\operatorname{range}\mathcal D_P=\mathcal B_P.
}
\]

因此

\[
\boxed{
X
=
\mathcal D_PX
+
(I-\mathcal D_P)X
}
\]

是 Hilbert–Schmidt 正交分解，且

\[
\boxed{
\|X\|_{\mathrm{HS}}^2
=
\|\mathcal D_PX\|_{\mathrm{HS}}^2
+
\|X-\mathcal D_PX\|_{\mathrm{HS}}^2.
}
\]

#### 证明

利用 \(P_iP_j=\delta_{ij}P_i\)：

\[
\mathcal D_P^2(X)
=
\sum_{i,j}P_iP_jXP_jP_i
=
\sum_iP_iXP_i.
\]

又

\[
\langle\mathcal D_PX,Y\rangle
=
\sum_i\operatorname{Tr}(X^*P_iYP_i)
=
\langle X,\mathcal D_PY\rangle.
\]

像空间恰是所有交叉块消失的算子。自伴幂等算子即为正交投影，Pythagoras 随之成立。 \(\square\)

所以一个状态可分解为：

\[
\boxed{
\rho
=
\underbrace{\mathcal D_P(\rho)}_{\text{相对于上下文可见的经典块}}
+
\underbrace{\bigl(\rho-\mathcal D_P(\rho)\bigr)}_{\text{跨扇区相干余量}}.
}
\]

“经典性”因此不是状态的绝对属性，而是相对于投影上下文的块对角性：

\[
\boxed{
\rho=\mathcal D_P(\rho).
}
\]

同一个 \(\rho\) 可以对一个上下文完全经典，对另一个上下文保持相干。

---

## 30.15 动力学相对性：概率流由跨界面耦合控制

设封闭系统由自伴 Hamiltonian \(H\) 生成：

\[
U_t=e^{-itH},
\qquad
\rho_t=U_t\rho U_t^*.
\]

对投影 \(P\)，定义事件概率

\[
p_P(t)=\operatorname{Tr}(\rho_tP).
\]

### 定理 30.23（投影概率流公式）

在有限维或满足相应定义域条件时，

\[
\boxed{
\frac{d}{dt}p_P(t)
=
i\operatorname{Tr}(\rho_t[H,P]).
}
\]

因此若

\[
[H,P]=0,
\]

则

\[
\boxed{
p_P(t)=p_P(0)
}
\]

对全部 \(t\) 成立。

#### 证明

\[
\dot\rho_t=-i[H,\rho_t].
\]

故

\[
\begin{aligned}
\dot p_P(t)
&=
-i\operatorname{Tr}([H,\rho_t]P)\\
&=
-i\operatorname{Tr}(H\rho_tP-\rho_tHP)\\
&=
i\operatorname{Tr}(\rho_t(HP-PH))\\
&=
i\operatorname{Tr}(\rho_t[H,P]).
\end{aligned}
\]

\(\square\)

相对于分解

\[
\mathscr H=P\mathscr H\oplus(I-P)\mathscr H,
\]

Hamiltonian 的跨界面耦合是

\[
PH(I-P),
\qquad
(I-P)HP.
\]

若二者为零，则 \(P\) reducing，事件扇区在动力学下闭合；若非零，则概率可以在已知／余空间之间流动。

这与第 28 节块矩阵判据完全一致：

\[
\boxed{
\text{观察界面的时间稳定性由跨块耦合决定，而不是只由各块内部维数决定。}
}
\]

---

## 30.16 状态完成严格弱于空间完成

设投影塔

\[
P_n\uparrow P_\infty
\]

于强算子拓扑，最终余投影为

\[
Q_\infty=I-P_\infty.
\]

### 定义 30.24（空间完成）

\[
\boxed{
Q_\infty=0.
}
\]

### 定义 30.25（状态完成）

对状态 \(\rho\)：

\[
\boxed{
\operatorname{Tr}(\rho Q_\infty)=0.
}
\]

### 定理 30.26（状态完成判据）

对正迹类 \(\rho\)，下列条件等价：

1. \(\operatorname{Tr}(\rho Q_\infty)=0\)；
2. \(Q_\infty\rho^{1/2}=0\)；
3. \(\operatorname{supp}\rho\le P_\infty\)；
4. \(\operatorname{Tr}(\rho P_n)\to1\)。

#### 证明

\[
\operatorname{Tr}(\rho Q_\infty)
=
\operatorname{Tr}(\rho^{1/2}Q_\infty\rho^{1/2})
=
\|Q_\infty\rho^{1/2}\|_{\mathrm{HS}}^2.
\]

故 1 与 2 等价；2 等价于状态支撑位于 \(P_\infty\) 中。又由 \(P_n\uparrow P_\infty\) 及正态迹的单调连续性：

\[
\operatorname{Tr}(\rho P_n)
\to
\operatorname{Tr}(\rho P_\infty)
=
1-\operatorname{Tr}(\rho Q_\infty).
\]

\(\square\)

所以：

\[
\boxed{
Q_\infty=0
\Longrightarrow
\operatorname{Tr}(\rho Q_\infty)=0,
}
\]

但反向一般不成立。

这给出一条统一解释：

- 在 RH 的 Nyman–Beurling 表述中，不要求整个最终余空间消失，只要求目标态 \(\chi\) 的余质量为零；
- 在量子观察中，不要求观察者覆盖全部可能态，只要求当前状态的支撑落在完成可见空间；
- 在有限模型中，不要求全状态空间统一逼近，只要求任务相关状态族的余概率可控。

---

## 30.17 对角化、量子上下文与完成失败不是同一个障碍

三种结构容易被语言混合，但其类型不同。

### Cantor–Lawvere 对角障碍

给定评价映射

\[
e:A\to Y^A,
\]

无不动点扭曲产生

\[
d_e\notin\operatorname{range}e.
\]

它是**自应用表示的满射失败**。

### Hilbert 正交余障碍

给定闭子空间 \(S\subsetneq\mathscr H\)，存在

\[
e\in S^\perp,
\qquad
\|e\|=1.
\]

它是**线性张成的完备失败**，但没有规范唯一逃逸对象。

### 量子上下文障碍

局部交换上下文各自允许经典赋值，但这些赋值不能拼成保持全部函数关系的全局 \(0/1\) 截面。

它是**局部 Boolean 图册的全局拼接失败**。

三者共同具有：

\[
\boxed{
\text{相对于当前描述存在未闭合余量。}
}
\]

但不能相互替代：

\[
\boxed{
\text{自描述满射失败}
\ne
\text{正交张成失败}
\ne
\text{上下文全局截面失败}.
}
\]

只有在给出明确函子、自然变换及双向定理后，才能把一个障碍传递到另一个领域。

---

## 30.18 “绝对是全部相对关系的闭合”的形式版本

设 \(\mathsf I\) 为界面范畴，给出逆系统

\[
F:\mathsf I^{op}\to\mathsf C,
\]

其中 \(F(i)=X_i\) 是第 \(i\) 个相对读出对象。整体候选是锥

\[
(q_i:X\to X_i)_i.
\]

若该锥满足极限泛性质，则

\[
\boxed{
X\cong\varprojlim_{i\in\mathsf I}X_i.
}
\]

这意味着：对任何另一个对象 \(Y\)，只要有一族相容读出

\[
f_i:Y\to X_i,
\qquad
p_{j,i}f_j=f_i,
\]

就存在唯一

\[
f:Y\to X
\]

使

\[
q_if=f_i.
\]

所以“绝对”不是一个内容最多的单一视角，而是：

\[
\boxed{
\text{使全部相对视角相容因子化的普适对象。}
}
\]

但在 Hilbert、拓扑、概率或算子代数范畴中，必须使用相应范畴的极限与可实现性条件；集合极限可能过大或忘记范数、正性和连续性。

量子理论进一步提示，全部交换上下文的简单集合极限未必给出一个全局经典样本空间。正确全局对象是非交换代数 \(\mathcal A\) 及其状态，而不是所有局部 Gelfand 谱的普通拼接。

因此：

\[
\boxed{
\text{绝对不是相对性的反面；绝对是相对转换规律及其闭合对象。}
}
\]

---

## 30.19 相对性六层审计

一个声称“从有限观察重构整体”的理论至少应通过以下六层审计。

### 第一层：身份审计

明确：

\[
x\sim_qy
\iff
q(x)=q(y).
\]

回答哪些差异被界面商掉。

### 第二层：余量审计

明确纤维、核、正交补或条件分布，回答被删除的信息在哪里。

### 第三层：自然性审计

检查

\[
qT=T_q q
\]

或对角版本

\[
Q\Delta=\Delta P.
\]

回答有效规律是否严格下降。

### 第四层：忠实性审计

检查界面是否仍能区分

\[
y
\quad\text{与}\quad
\tau y,
\]

避免“盲自然性”。

### 第五层：完成审计

区分：

\[
\text{分离性},
\quad
\text{形式相容性},
\quad
\text{可实现性},
\quad
\text{有界能量/正则性}.
\]

### 第六层：上下文审计

当存在多个不兼容界面时，检查：

\[
\text{重叠一致性},
\quad
\text{共同精化},
\quad
\text{全局截面},
\quad
\text{非交换障碍}.
\]

只有全部六层同时说明，才可以把“相对观察”提升为严谨的局部—整体理论。

---

## 30.20 与 Riemann 假设接口的再解释

第 29 节得到：

\[
\mathrm{RH}
\iff
P_{R_\infty}\chi=0
\]

于 Nyman–Beurling 商余塔。

本节说明其相对性含义：

- \(S_N\) 是由前 \(N\) 个显式算术生成元形成的有限观察界面；
- \(R_N\) 是相对于该算术界面仍未解释的方向；
- \(d_N=\|P_{R_N}\chi\|\) 是指定目标的相对余量；
- RH 不要求所有可能向量都被该界面塔统一解释；
- RH 只要求 \(\chi\) 相对于完整算术界面族最终可实现，即
  \[
  [\chi]=0
  \quad
  \text{于 }
  \mathscr H/S_\infty.
  \]

因此 RH 的 Hilbert 表述不是“绝对余空间不存在”，而是：

\[
\boxed{
\text{相对于指定算术生成规则，目标向量没有最终不可解释分量。}
}
\]

这与量子状态完成的形式完全平行：

\[
\operatorname{Tr}(\rho Q_\infty)=0.
\]

两者共享“状态/目标相对完成”结构，但一个是解析数论逼近判据，一个是量子状态支撑判据；二者不能仅凭形式相同而互相证明。

---

## 30.21 可形式化拆分

建议新增以下 Lean 纸面目标，按依赖顺序推进。

1. `ObserverInterfaceKernel`
   \[
   q_i=p_{j,i}q_j
   \Rightarrow
   \ker q_j\subseteq\ker q_i.
   \]

2. `ObserverLimitSeparation`
   \[
   \Phi\text{ injective}
   \iff
   \bigcap_i\ker q_i=\{0\}.
   \]

3. `ObserverLimitRealizability`
   \[
   X/{\sim_\infty}\cong\operatorname{im}\Phi.
   \]

4. `DiagonalInterfaceNaturality`
   \[
   q\tau=\bar\tau q
   \Rightarrow
   Q\Delta_\tau=\Delta_{\bar\tau}P.
   \]

5. `DiagonalBlindQuotient`
   \[
   q\tau=q
   \Rightarrow
   Q\Delta_\tau=QD.
   \]

6. `CommutingProjectionJointPVM`
   两投影交换当且仅当存在共同四结果 PVM。

7. `HilbertSchmidtDephasingProjection`
   \[
   \mathcal D_P^2=\mathcal D_P=\mathcal D_P^*.
   \]

8. `ProjectionProbabilityFlow`
   \[
   \frac d{dt}\operatorname{Tr}(\rho_tP)
   =
   i\operatorname{Tr}(\rho_t[H,P]).
   \]

9. `StateRelativeCompletion`
   \[
   \operatorname{Tr}(\rho Q_\infty)=0
   \iff
   \operatorname{supp}\rho\le P_\infty.
   \]

10. `ContextRestrictionCompatibility`
    状态在交换子代数交集上的限制一致。

Kochen–Specker、Gleason、Naimark、Stinespring 与 GNS 等一般结果应作为具名、来源可审计的经典接口接入，不能以无名公理隐藏。

---

## 30.22 最终统一式

本节得到：

\[
\boxed{
\text{相对性}
=
\text{选择界面并声明界面转换}.
}
\]

\[
\boxed{
\text{商}
=
\text{该界面保留的身份空间}.
}
\]

\[
\boxed{
\text{余}
=
\text{该界面删除的纤维、核或正交分量}.
}
\]

\[
\boxed{
\text{对角化}
=
\text{描述界面不能以同类型封闭自身的证书}.
}
\]

\[
\boxed{
\infty
=
\text{任何有限界面都不终止，但全部相容界面可以完成}.
}
\]

\[
\boxed{
\text{概率}
=
\text{状态对 effect 的评价，而非 effect 本身}.
}
\]

\[
\boxed{
\text{量子性}
=
\text{一族局部经典上下文不能被压平为单一全局 Boolean 上下文}.
}
\]

最凝练的结论是：

\[
\boxed{
\text{整体不是某个观察者看到的最大画面；整体是全部相对观察、转换、余量与一致性条件的闭合。}
}
\]

而量子力学在这个框架中的位置是：

\[
\boxed{
\text{每个测量上下文投影出一个经典概率世界；
完整量子世界则保存这些局部经典世界之间不可交换、不可共同锐化的关系。}
}
\]

## 30.23 严格非主张与形式化状态

1. 本节不把哲学上的全部相对性约化为数学商映射。
2. 本节不声称集合逆极限总能恢复拓扑、Hilbert 或算子代数整体。
3. 本节不把概率等同于投影；概率始终依赖状态—effect 配对。
4. 本节不把 Naimark/Stinespring 扩张解释为唯一隐藏经典本体。
5. 本节不把退相干等同于单一结果选择。
6. 本节不把量子上下文性、Bell 非局域性与 Cantor 对角化视为同一定理。
7. 本节不从界面相对性推出 Riemann 假设、光速信息率或意识模型。
8. 本节新增定理均为纸面结论；在获得 kernel verification 以前不得标记为 `Closed`。

---

# 31. 追加：算子 Hilbert 坐标塔、互补对角与三类量子闭合缺陷

## 31.0 研究定位

第 30 节把相对性、商余、概率与量子上下文统一到“观察界面及其完成”之下，但仍留下一个关键歧义：若两个上下文的去相干通道交换，是否说明它们在物理上兼容？答案是否定的。事实上，两组互相无偏基（mutually unbiased bases, MUB）的锐利投影是最大互补的，但对应去相干通道的复合都等于完全退极化通道，因此两种顺序完全相同。

这迫使本文把“上下文差异”拆成三种彼此独立的结构：

1. **锐利不兼容度**：组成上下文的投影是否能够共同对角化；
2. **粗粒化顺序缺陷**：先按哪个上下文丢弃相干是否影响结果；
3. **全局拼接障碍**：全部局部统计是否存在一个统一的非上下文全局模型。

本节首先把有限维量子状态空间嵌入算子 Hilbert 空间，证明一次基测量恰好是到一个 \((d-1)\)-维“经典对角坐标平面”的正交投影；其余 \(d^2-d\) 个实方向是该上下文看不见的相干余量。随后证明，成套 MUB 上下文在算子 Hilbert 空间中形成正交商余塔：每增加一个最大互补坐标系，恰好抽取一个新的 \((d-1)\)-维正交切片；若存在完整的 \(d+1\) 组 MUB，则这些局部经典对角平面正交直和成全部无迹 Hermitian 算子空间，从而完成量子态层析。

在此基础上，本节给出五组新推导：

- 单一锐利上下文的状态自由度可见率为 \(1/(d+1)\)，线性余量率为 \(d/(d+1)\)；
- \(m\) 组 MUB 的状态无关余维率为 \(1-m/(d+1)\)；
- 状态的 Hilbert–Schmidt 余质量按每个新增概率坐标的二次偏差精确递减；
- 对任意 Lipschitz 自指算子或动力学，观察自然性缺陷由尚未捕获的余质量控制；
- 重复“酉演化—投影界面”产生的熵增，逐步恰等于每轮被删除的相对熵相干。

本节不声称这些组成部分各自都是新发现。MUB 层析、算子 Hilbert 几何、条件期望、量子相干和上下文性均有成熟文献。本文的候选贡献是把它们接入同一个“对角—商余—观察完成”演算，并识别出一个此前框架中的错误替代：**去相干通道交换子不能作为锐利上下文不兼容性的统一度量。**

以下固定

\[
\mathscr H=\mathbb C^d,
\qquad
d\ge2.
\]

所有新增结论均为纸面证明，未经 Lean kernel 验证不得标记为 `Closed`。

---

## 31.1 状态不是一个概率向量，而是算子 Hilbert 空间中的点

令

\[
\operatorname{Herm}_d
=
\{X\in M_d(\mathbb C):X=X^*\}
\]

视为实 Hilbert 空间，内积为

\[
\langle X,Y\rangle_{\mathrm{HS}}
=
\operatorname{Tr}(XY).
\]

其无迹子空间为

\[
\operatorname{Herm}_d^0
=
\{X\in\operatorname{Herm}_d:\operatorname{Tr}X=0\}.
\]

维数为

\[
\boxed{
\dim_{\mathbb R}\operatorname{Herm}_d=d^2,
\qquad
\dim_{\mathbb R}\operatorname{Herm}_d^0=d^2-1.
}
\]

任意密度矩阵唯一写成

\[
\boxed{
\rho=\frac{I}{d}+X_\rho,
\qquad
X_\rho\in\operatorname{Herm}_d^0.
}
\]

这里 \(I/d\) 是共同的仿射原点，而 \(X_\rho\) 携带全部可变状态信息。其 Hilbert–Schmidt 长度满足

\[
\boxed{
\|X_\rho\|_2^2
=
\operatorname{Tr}(\rho^2)-\frac1d.
}
\]

所以偏离最大混合态的总二次信息量就是 purity excess。

### 定义 31.1（基上下文的对角平面）

取一组正交规范基

\[
\mathcal B=(|b_1\rangle,\ldots,|b_d\rangle),
\]

并令

\[
P_j^{\mathcal B}=|b_j\rangle\langle b_j|.
\]

定义该上下文的无迹对角平面

\[
\boxed{
\mathcal D_{\mathcal B}^0
=
\left\{
\sum_{j=1}^d x_jP_j^{\mathcal B}:
x_j\in\mathbb R,\ 
\sum_jx_j=0
\right\}.
}
\]

显然

\[
\boxed{
\dim_{\mathbb R}\mathcal D_{\mathcal B}^0=d-1.
}
\]

定义去相干／pinching 映射

\[
\boxed{
\mathbb E_{\mathcal B}(X)
=
\sum_{j=1}^d
P_j^{\mathcal B}XP_j^{\mathcal B}.
}
\]

### 定理 31.2（一次基测量是算子 Hilbert 正交投影）

\(\mathbb E_{\mathcal B}\) 是 \(\operatorname{Herm}_d\) 上到

\[
\mathcal D_{\mathcal B}
=
\mathbb RI\oplus\mathcal D_{\mathcal B}^0
\]

的 Hilbert–Schmidt 正交投影。限制到 \(\operatorname{Herm}_d^0\) 时，它是到 \(\mathcal D_{\mathcal B}^0\) 的正交投影。

#### 证明

由投影正交性，

\[
\mathbb E_{\mathcal B}^2(X)
=
\sum_{j,k}P_jP_kXP_kP_j
=
\sum_jP_jXP_j
=
\mathbb E_{\mathcal B}(X).
\]

又因为

\[
\operatorname{Tr}\!\left(
Y\mathbb E_{\mathcal B}(X)
\right)
=
\sum_j\operatorname{Tr}(YP_jXP_j)
=
\sum_j\operatorname{Tr}(P_jYP_jX)
=
\operatorname{Tr}\!\left(
\mathbb E_{\mathcal B}(Y)X
\right),
\]

故 \(\mathbb E_{\mathcal B}\) 对 Hilbert–Schmidt 内积自伴。幂等且自伴即为正交投影。其像恰为在 \(\mathcal B\) 中对角的 Hermitian 算子。由于保持迹，限制到无迹空间后的像为 \(\mathcal D_{\mathcal B}^0\)。 \(\square\)

设

\[
p_j^{\mathcal B}(\rho)
=
\operatorname{Tr}(\rho P_j^{\mathcal B}).
\]

则

\[
\boxed{
\mathbb E_{\mathcal B}(\rho)
=
\sum_jp_j^{\mathcal B}(\rho)P_j^{\mathcal B}.
}
\]

所以一组测量概率并不是整个状态，而只确定状态在一个 \((d-1)\)-维经典对角平面上的投影。

### 推论 31.3（单上下文的线性可见率与余量率）

在无迹状态方向空间 \(\operatorname{Herm}_d^0\) 中，一组秩一 PVM 最多可见

\[
d-1
\]

个独立实方向，留下

\[
d^2-d
\]

个正交余方向。因此

\[
\boxed{
\text{visible ratio}
=
\frac{d-1}{d^2-1}
=
\frac1{d+1},
}
\]

\[
\boxed{
\text{remainder ratio}
=
\frac{d^2-d}{d^2-1}
=
\frac d{d+1}.
}
\]

这里的比例是线性维数比例，不是任意具体状态的概率质量比例。

这给出一个精确修正：

\[
\boxed{
\text{一个量子概率向量通常只暴露状态线性自由度的 }1/(d+1).
}
\]

其余部分不是“没有定义”，而是相对于该坐标系仍处于非对角余空间。

---

## 31.2 纯态概率映射的纤维就是相对相位余坐标

在纯态层，取射影空间

\[
\mathbb{CP}^{d-1}
\]

并定义基概率映射

\[
q_{\mathcal B}:
\mathbb{CP}^{d-1}
\longrightarrow
\Delta_{d-1},
\]

\[
q_{\mathcal B}([\psi])
=
\left(
|\langle b_1,\psi\rangle|^2,
\ldots,
|\langle b_d,\psi\rangle|^2
\right).
\]

### 定理 31.4（内点概率纤维为 \((d-1)\)-环面）

若

\[
p=(p_1,\ldots,p_d)
\in\operatorname{int}\Delta_{d-1},
\qquad
p_j>0,
\]

则

\[
\boxed{
q_{\mathcal B}^{-1}(p)
\cong
\mathbb T^{d-1}.
}
\]

#### 证明

任意位于该纤维的单位向量可写成

\[
\psi
=
\sum_{j=1}^d
\sqrt{p_j}e^{i\theta_j}|b_j\rangle.
\]

全部 \(\theta_j\in\mathbb R/2\pi\mathbb Z\) 可自由选择，但共同平移

\[
(\theta_1,\ldots,\theta_d)
\mapsto
(\theta_1+\alpha,\ldots,\theta_d+\alpha)
\]

只改变全局相位，在 \(\mathbb{CP}^{d-1}\) 中代表同一点。因此纤维为

\[
\mathbb T^d/\mathbb T
\cong
\mathbb T^{d-1}.
\]

\(\square\)

所以对于纯态：

\[
\boxed{
\text{概率坐标}
=
\text{模长平方},
}
\]

\[
\boxed{
\text{余坐标}
=
\text{相对相位}.
}
\]

维数核对为

\[
2d-2
=
(d-1)+(d-1).
\]

在概率单纯形边界上，零振幅坐标不再携带相位，纤维退化为更低维环面。

这使“概率是投影”获得一个非常具体的商余形式：

\[
\boxed{
\mathbb{CP}^{d-1}
\longrightarrow
\Delta_{d-1}
}
\]

忘掉的不是一个抽象神秘变量，而是相对于该基的相对相位纤维。

---
## 31.3 互相无偏基在算子 Hilbert 空间中给出正交对角平面

取两组正交基

\[
\mathcal B=(|b_j\rangle)_j,
\qquad
\mathcal C=(|c_k\rangle)_k.
\]

定义重叠矩阵

\[
M_{jk}
=
|\langle b_j,c_k\rangle|^2
=
\operatorname{Tr}(P_j^{\mathcal B}P_k^{\mathcal C}).
\]

\(M\) 是双随机矩阵。

两基互相无偏，是指

\[
\boxed{
M_{jk}=\frac1d
\qquad
\forall j,k.
}
\]

### 定理 31.5（MUB 等价于无迹对角平面正交）

下列命题等价：

1. \(\mathcal B,\mathcal C\) 互相无偏；
2. \(\mathcal D_{\mathcal B}^0\perp\mathcal D_{\mathcal C}^0\) 于 Hilbert–Schmidt 内积；
3. 对任意 \(X\in\operatorname{Herm}_d^0\)，

   \[
   \mathbb E_{\mathcal B}\mathbb E_{\mathcal C}(X)=0
   =
   \mathbb E_{\mathcal C}\mathbb E_{\mathcal B}(X);
   \]

4. 对任意 \(X\in\operatorname{Herm}_d\)，

   \[
   \boxed{
   \mathbb E_{\mathcal B}\mathbb E_{\mathcal C}(X)
   =
   \mathbb E_{\mathcal C}\mathbb E_{\mathcal B}(X)
   =
   \frac{\operatorname{Tr}X}{d}I.
   }
   \]

#### 证明

若两基互相无偏，取

\[
A=\sum_ja_jP_j^{\mathcal B},
\qquad
B=\sum_kb_kP_k^{\mathcal C},
\]

且

\[
\sum_ja_j=\sum_kb_k=0.
\]

则

\[
\langle A,B\rangle_{\mathrm{HS}}
=
\sum_{j,k}a_jb_kM_{jk}
=
\frac1d
\left(\sum_ja_j\right)
\left(\sum_kb_k\right)
=
0.
\]

故 1 推出 2。正交投影到两个正交子空间的复合为零，故 2 推出 3。

对任意 \(X\)，写

\[
X=\frac{\operatorname{Tr}X}{d}I+X_0,
\qquad
\operatorname{Tr}X_0=0.
\]

两映射均固定 \(I\)，而在 \(X_0\) 上复合为零，故得到 4。

最后，令 \(X=P_k^{\mathcal C}\)。由 4，

\[
\mathbb E_{\mathcal B}(P_k^{\mathcal C})
=
\sum_jM_{jk}P_j^{\mathcal B}
=
\frac Id,
\]

比较各 \(P_j^{\mathcal B}\) 系数得到 \(M_{jk}=1/d\)，故 4 推出 1。 \(\square\)

### 关键反例 31.6（去相干通道交换不等于锐利兼容）

当 \(\mathcal B,\mathcal C\) 为 MUB 时，

\[
\boxed{
[\mathbb E_{\mathcal B},\mathbb E_{\mathcal C}]=0,
}
\]

因为两种复合都等于完全退极化投影

\[
X\mapsto\frac{\operatorname{Tr}X}{d}I.
\]

然而任意非平凡 \(P_j^{\mathcal B},P_k^{\mathcal C}\) 一般满足

\[
[P_j^{\mathcal B},P_k^{\mathcal C}]\ne0.
\]

所以

\[
\boxed{
\text{粗粒化顺序无差异}
\not\Rightarrow
\text{锐利测量兼容}.
}
\]

事实上，MUB 是最大互补的锐利坐标系，却给出零去相干顺序缺陷。由此，第 30 节所定义的

\[
\mathbb E_i\mathbb E_j-\mathbb E_j\mathbb E_i
\]

只能测量“丢弃信息的顺序是否重要”，不能单独充当上下文不兼容度。

---

## 31.4 锐利不兼容度、坐标冗余与投影交换子的精确公式

定义中心化投影

\[
\widetilde P_j^{\mathcal B}
=
P_j^{\mathcal B}-\frac Id,
\qquad
\widetilde P_k^{\mathcal C}
=
P_k^{\mathcal C}-\frac Id.
\]

则

\[
\left\langle
\widetilde P_j^{\mathcal B},
\widetilde P_k^{\mathcal C}
\right\rangle_{\mathrm{HS}}
=
M_{jk}-\frac1d.
\]

定义对角平面冗余能量

\[
\boxed{
\mathcal R(\mathcal B,\mathcal C)
=
\sum_{j,k}
\left(M_{jk}-\frac1d\right)^2.
}
\]

利用双随机性，

\[
\boxed{
\mathcal R(\mathcal B,\mathcal C)
=
\sum_{j,k}M_{jk}^2-1.
}
\]

由于任意双随机矩阵满足

\[
1\le\sum_{j,k}M_{jk}^2\le d,
\]

故

\[
0\le\mathcal R\le d-1.
\]

- \(\mathcal R=0\) 当且仅当两基互相无偏；
- \(\mathcal R=d-1\) 当且仅当 \(M\) 为置换矩阵，即两基相同到相位与重标记。

定义归一化锐利不兼容度

\[
\boxed{
\mathcal I(\mathcal B,\mathcal C)
=
1-\frac{\mathcal R(\mathcal B,\mathcal C)}{d-1}
=
\frac{
d-\sum_{j,k}M_{jk}^2
}{
d-1
}.
}
\]

于是

\[
\boxed{
0\le\mathcal I\le1,
}
\]

\[
\boxed{
\mathcal I=0
\iff
\text{同一锐利上下文},
}
\]

\[
\boxed{
\mathcal I=1
\iff
\text{MUB 最大互补上下文}.
}
\]

### 定理 31.7（聚合投影交换子公式）

对秩一上下文，

\[
\boxed{
\sum_{j,k}
\left\|
[P_j^{\mathcal B},P_k^{\mathcal C}]
\right\|_2^2
=
2(d-1)\mathcal I(\mathcal B,\mathcal C).
}
\]

#### 证明

对两个秩一投影 \(P,Q\)，若

\[
m=\operatorname{Tr}(PQ),
\]

直接计算得

\[
\|[P,Q]\|_2^2
=
2m(1-m).
\]

因此

\[
\sum_{j,k}\|[P_j,Q_k]\|_2^2
=
2\sum_{j,k}M_{jk}(1-M_{jk}).
\]

又因

\[
\sum_{j,k}M_{jk}=d,
\]

故

\[
2\sum_{j,k}M_{jk}(1-M_{jk})
=
2\left(
d-\sum_{j,k}M_{jk}^2
\right)
=
2(d-1)\mathcal I.
\]

\(\square\)

因此本节得到三种必须分开的量：

\[
\boxed{
\begin{aligned}
\mathcal I(\mathcal B,\mathcal C)
&=\text{锐利投影不兼容度},\\
\mathcal O_{\mathcal B,\mathcal C}(\rho)
&=
\|
\mathbb E_{\mathcal B}\mathbb E_{\mathcal C}(\rho)
-
\mathbb E_{\mathcal C}\mathbb E_{\mathcal B}(\rho)
\|
=\text{粗粒化顺序缺陷},\\
\mathcal G
&=\text{多上下文全局拼接／非上下文模型缺陷}.
\end{aligned}
}
\]

MUB 给出

\[
\mathcal I=1,
\qquad
\mathcal O=0.
\]

相同基给出

\[
\mathcal I=0,
\qquad
\mathcal O=0.
\]

因此 \(\mathcal O\) 甚至不能按 \(\mathcal I\) 单调排序。全局 contextuality 又不能由任意单个成对量完全决定；一般化非上下文性中，测量不兼容既非必要也非充分条件。故“量子上下文缺陷”必须是多分量审计，而不是一个被过度命名的交换子。

---
## 31.5 MUB 对角塔：每个新坐标系抽出一个正交经典切片

设

\[
\mathcal B_1,\ldots,\mathcal B_m
\]

两两互相无偏。定义

\[
\boxed{
S_m
=
\bigoplus_{\ell=1}^{m}
\mathcal D_{\mathcal B_\ell}^0
\subseteq
\operatorname{Herm}_d^0,
}
\]

以及余空间

\[
\boxed{
R_m=S_m^\perp.
}
\]

由定理 31.5，直和为正交直和。因此

\[
\boxed{
\dim S_m=m(d-1),
}
\]

\[
\boxed{
\dim R_m
=
d^2-1-m(d-1)
=
(d-1)(d+1-m).
}
\]

由此定义状态无关的维数逃逸率

\[
\boxed{
r_m^{\mathrm{dim}}
=
\frac{\dim R_m}{d^2-1}
=
1-\frac{m}{d+1}.
}
\]

以及已完成比例

\[
\boxed{
v_m^{\mathrm{dim}}
=
\frac{\dim S_m}{d^2-1}
=
\frac{m}{d+1}.
}
\]

这给出一个有限量子系统中的精确“观察完成速度”：

> 每增加一个最大互补锐利坐标系，恰好增加 \(1/(d+1)\) 的线性状态自由度覆盖。

注意这不是物理时间速度，而是上下文精化深度。

对状态

\[
X_\rho=\rho-\frac Id
\]

定义状态相关余质量

\[
\boxed{
r_m^{(2)}(\rho)
=
\|P_{R_m}X_\rho\|_2^2.
}
\]

### 定理 31.8（概率偏差—余质量 Pythagoras 恒等式）

令

\[
p_{\ell j}
=
\operatorname{Tr}
\left(
\rho P_j^{\mathcal B_\ell}
\right).
\]

则

\[
\boxed{
\operatorname{Tr}(\rho^2)-\frac1d
=
\sum_{\ell=1}^{m}
\sum_{j=1}^{d}
\left(
p_{\ell j}-\frac1d
\right)^2
+
r_m^{(2)}(\rho).
}
\]

#### 证明

\(\mathbb E_{\mathcal B_\ell}X_\rho\) 是 \(X_\rho\) 在第 \(\ell\) 个无迹对角平面上的正交投影，并且

\[
\mathbb E_{\mathcal B_\ell}X_\rho
=
\sum_j
\left(
p_{\ell j}-\frac1d
\right)
P_j^{\mathcal B_\ell}.
\]

因为各对角平面彼此正交，

\[
P_{S_m}X_\rho
=
\sum_{\ell=1}^m
\mathbb E_{\mathcal B_\ell}X_\rho.
\]

又

\[
\left\|
\mathbb E_{\mathcal B_\ell}X_\rho
\right\|_2^2
=
\sum_j
\left(
p_{\ell j}-\frac1d
\right)^2.
\]

最后应用

\[
\|X_\rho\|_2^2
=
\|P_{S_m}X_\rho\|_2^2
+
\|P_{R_m}X_\rho\|_2^2.
\]

\(\square\)

所以每个新坐标系所捕获的并不是“又一份重复概率”，而是一个与此前全部 MUB 对角平面正交的二次状态分量。

### 推论 31.9（单步概率创新）

增加第 \(m+1\) 个 MUB 上下文时，

\[
\boxed{
r_m^{(2)}(\rho)
-
r_{m+1}^{(2)}(\rho)
=
\sum_j
\left(
p_{m+1,j}-\frac1d
\right)^2.
}
\]

这正是第 28 节商余塔递推

\[
R_m
=
\mathcal D_{\mathcal B_{m+1}}^0
\oplus
R_{m+1}
\]

在量子状态层析中的具体实现。

---

## 31.6 完整 MUB 集、最小层析深度与显式状态重构

任意秩一正交基测量只产生 \(d-1\) 个独立概率参数，而一般密度矩阵具有 \(d^2-1\) 个实参数。因此，仅使用非退化正交基测量时，信息完备至少需要

\[
\boxed{
\frac{d^2-1}{d-1}
=
d+1
}
\]

组测量上下文。

### 定理 31.10（完整 MUB 集达到最小基层析深度）

若存在

\[
d+1
\]

组两两 MUB

\[
\mathcal B_1,\ldots,\mathcal B_{d+1},
\]

则

\[
\boxed{
\operatorname{Herm}_d^0
=
\bigoplus_{\ell=1}^{d+1}
\mathcal D_{\mathcal B_\ell}^0.
}
\]

因此

\[
R_{d+1}=\{0\},
\]

而全部基概率唯一确定 \(\rho\)。

#### 证明

各子空间两两正交，每个维数为 \(d-1\)，总维数为

\[
(d+1)(d-1)=d^2-1,
\]

恰等于 \(\operatorname{Herm}_d^0\) 的维数。 \(\square\)

### 推论 31.11（显式 MUB 重构公式）

在完整 MUB 集下，

\[
\boxed{
\rho
=
\frac Id
+
\sum_{\ell=1}^{d+1}
\sum_{j=1}^{d}
\left(
p_{\ell j}-\frac1d
\right)
P_j^{\mathcal B_\ell}.
}
\]

#### 证明

右侧第二项正是 \(X_\rho\) 在所有正交对角平面上的分量之和。 \(\square\)

### 推论 31.12（完整 MUB 的 purity 概率恒等式）

\[
\boxed{
\sum_{\ell=1}^{d+1}
\sum_{j=1}^{d}
\left(
p_{\ell j}-\frac1d
\right)^2
=
\operatorname{Tr}(\rho^2)-\frac1d.
}
\]

等价地，

\[
\boxed{
\sum_{\ell=1}^{d+1}
\sum_{j=1}^{d}
p_{\ell j}^2
=
1+\operatorname{Tr}(\rho^2).
}
\]

所以完整 MUB 概率族不仅重构状态，还把整体 purity 精确分解为各局部经典坐标图的二次偏差总和。

当 \(d\) 为素数幂时已知存在完整 \(d+1\) 组 MUB。对于一般非素数幂维数，特别是 \(d=6\)，完整集存在性截至本文版本仍是开放问题。因此本节不能把 \(d+1\) MUB 塔假定为所有维数中的普适物理结构。在缺乏完整 MUB 时，可以使用一般信息完备 POVM、互补 frame 或非正交上下文，并以 Gram–Schur 创新代替严格正交增量。

---
## 31.7 对角自指与动力学的自然性缺陷由层析余质量控制

MUB 对角塔不仅重构状态，还可以控制任意状态操作在有限观察坐标中的降阶误差。

令

\[
P_m:
\operatorname{Herm}_d^0
\to S_m
\]

为正交投影。

设

\[
F:
\operatorname{Herm}_d^0
\to
\operatorname{Herm}_d^0
\]

为 \(L_F\)-Lipschitz 映射：

\[
\|F(X)-F(Y)\|_2
\le
L_F\|X-Y\|_2.
\]

定义其第 \(m\) 层压缩模型

\[
\boxed{
F_m
=
P_mF|_{S_m}.
}
\]

定义自然性缺陷

\[
\boxed{
\partial_mF(X)
=
\|
P_mF(X)
-
F_m(P_mX)
\|_2.
}
\]

### 定理 31.13（余质量控制自然性缺陷）

\[
\boxed{
\partial_mF(X)
\le
L_F
\|(I-P_m)X\|_2.
}
\]

对密度矩阵 \(X=X_\rho\)，

\[
\boxed{
\partial_mF(X_\rho)
\le
L_F
\sqrt{
r_m^{(2)}(\rho)
}.
}
\]

#### 证明

由 \(F_m(P_mX)=P_mF(P_mX)\)，

\[
\partial_mF(X)
=
\|
P_m(F(X)-F(P_mX))
\|_2.
\]

正交投影为收缩，故

\[
\partial_mF(X)
\le
\|F(X)-F(P_mX)\|_2
\le
L_F\|X-P_mX\|_2.
\]

\(\square\)

这条定理把第 30 节的抽象界

\[
\text{自然性缺陷}
\le
\text{观察余量}
\]

在量子层析塔中完全具体化。若 \(F\) 是自指／对角操作，则它控制“先在完整状态空间自指再观察”与“先投影到有限概率坐标再自指”的误差；若 \(F\) 是动力学，则它控制有限观察层的有效演化误差。

在完整 MUB 集存在时，

\[
P_{d+1}=I,
\]

因此

\[
\boxed{
\partial_{d+1}F=0
}
\]

对任意 \(F\) 成立。这里的零缺陷不是因为操作本身简单，而是因为观察坐标已经信息完备，不再有状态余量。

### 定理 31.14（自然性缺陷的复合 Leibniz 界）

设 \(F,G\) 分别具有局部压缩 \(F_m,G_m\)，并且 \(F_m\) 为 \(L_m(F)\)-Lipschitz。则

\[
\boxed{
\partial_m(F\circ G)(X)
\le
\partial_mF(GX)
+
L_m(F)\partial_mG(X),
}
\]

其中局部复合取 \(F_m\circ G_m\)。

#### 证明

插入中间项 \(F_m(P_mGX)\)：

\[
\begin{aligned}
&
\|P_mFGX-F_mG_mP_mX\|_2
\\
&\le
\|P_mFGX-F_mP_mGX\|_2
+
\|F_mP_mGX-F_mG_mP_mX\|_2
\\
&\le
\partial_mF(GX)
+
L_m(F)\partial_mG(X).
\end{aligned}
\]

\(\square\)

### 推论 31.15（时间迭代误差）

若 \(F_m\) 的 Lipschitz 常数不超过 \(L\)，则

\[
\boxed{
\partial_m(F^n)(X)
\le
\sum_{k=0}^{n-1}
L^{n-1-k}
\partial_mF(F^kX).
}
\]

若沿轨道单步缺陷均不超过 \(\varepsilon_m\)，则

\[
\boxed{
\partial_m(F^n)(X)
\le
\begin{cases}
n\varepsilon_m,&L=1,\\[1mm]
\dfrac{1-L^n}{1-L}\varepsilon_m,&0\le L<1,\\[3mm]
\dfrac{L^n-1}{L-1}\varepsilon_m,&L>1.
\end{cases}
}
\]

这把“时间”与“有限坐标自然性”连接起来：

- 收缩动力学会使有限观察误差饱和；
- 等距动力学最多线性累计局部缺陷；
- 扩张动力学可能指数放大未观察余量。

该结论仍是模型误差传播，不等同于物理光速或普适时间箭头。

---

## 31.8 重复投影界面产生的熵箭头：每一步熵增恰等于被删除相干

令

\[
U:\mathscr H\to\mathscr H
\]

为酉算子，固定上下文 \(\mathcal B\)，并定义离散时间演化

\[
\boxed{
\rho_{n+1}
=
\mathbb E_{\mathcal B}
\left(
U\rho_nU^*
\right).
}
\]

整体酉演化本身保持 von Neumann 熵：

\[
S(U\rho U^*)=S(\rho).
\]

对去相干映射有标准恒等式

\[
\boxed{
D(\sigma\|
\mathbb E_{\mathcal B}\sigma)
=
S(\mathbb E_{\mathcal B}\sigma)-S(\sigma).
}
\]

### 定理 31.16（熵生产—相干删除恒等式）

对每个 \(n\)，

\[
\boxed{
S(\rho_{n+1})-S(\rho_n)
=
D\!\left(
U\rho_nU^*
\big\|
\mathbb E_{\mathcal B}(U\rho_nU^*)
\right)
\ge0.
}
\]

因此

\[
\boxed{
S(\rho_N)-S(\rho_0)
=
\sum_{n=0}^{N-1}
D\!\left(
U\rho_nU^*
\big\|
\mathbb E_{\mathcal B}(U\rho_nU^*)
\right).
}
\]

#### 证明

令

\[
\sigma_n=U\rho_nU^*.
\]

则

\[
\rho_{n+1}
=
\mathbb E_{\mathcal B}\sigma_n.
\]

利用去相干相对熵恒等式和酉熵不变性：

\[
\begin{aligned}
S(\rho_{n+1})-S(\rho_n)
&=
S(\mathbb E_{\mathcal B}\sigma_n)-S(\sigma_n)
\\
&=
D(\sigma_n\|
\mathbb E_{\mathcal B}\sigma_n).
\end{aligned}
\]

求和即得。 \(\square\)

这给出一个严格的时间箭头分解：

\[
\boxed{
\text{熵增}
=
\text{每一步由观察界面删除的相干总量}.
}
\]

若没有 \(\mathbb E_{\mathcal B}\)，则酉动力学熵不变。若 \(U\) 保持对角代数，并且 \(\rho_0\) 已在该代数中，则所有相对熵项均为零，熵不增加。

所以本模型中的不可逆性不来自 Hilbert 空间本身，而来自

\[
\boxed{
\text{可逆整体动力学}
+
\text{重复非单射界面投影}.
}
\]

### 定理 31.17（投影后动力学退化为 unistochastic Markov 链）

从第一步以后，

\[
\rho_n
=
\sum_jp_{n,j}P_j^{\mathcal B}.
\]

定义

\[
\boxed{
T_{kj}
=
|\langle b_k,Ub_j\rangle|^2.
}
\]

则 \(T\) 为双随机矩阵，并且

\[
\boxed{
p_{n+1}=Tp_n.
}
\]

#### 证明

若

\[
\rho_n=\sum_jp_{n,j}P_j,
\]

则

\[
p_{n+1,k}
=
\operatorname{Tr}
\left(
P_kU\rho_nU^*
\right)
=
\sum_j
|\langle b_k,Ub_j\rangle|^2p_{n,j}.
\]

酉矩阵各行各列模平方和为一，故 \(T\) 双随机。 \(\square\)

因此，一旦每一步都将状态投影回同一个经典对角上下文，量子过程在可见层变成一个经典 Markov 链。双随机性给出

\[
p_{n+1}\prec p_n,
\]

故 Shannon 熵满足

\[
\boxed{
H(p_{n+1})\ge H(p_n).
}
\]

若 \(T\) primitive，则

\[
p_n\to
\left(
\frac1d,\ldots,\frac1d
\right)
\]

并且

\[
H(p_n)\to\log d.
\]

这不是量子力学所有时间箭头的唯一解释，而是一个精确模型，展示了概率、熵、投影与时间如何从同一界面递推中出现。

---

## 31.9 不能再使用一个“上下文缺陷”概括所有量子非经典性

本节的 MUB 反例要求对第 30 节作 append-only 收紧。至少存在以下四个不同问题：

### 1. 锐利兼容性

问投影是否共同可测／共同对角化：

\[
[P_j^{\mathcal B},P_k^{\mathcal C}]=0.
\]

对应量：

\[
\mathcal I(\mathcal B,\mathcal C).
\]

### 2. 粗粒化顺序性

问两次信息删除的顺序是否重要：

\[
\mathbb E_{\mathcal B}
\mathbb E_{\mathcal C}
\stackrel{?}{=}
\mathbb E_{\mathcal C}
\mathbb E_{\mathcal B}.
\]

对应状态依赖量：

\[
\mathcal O_{\mathcal B,\mathcal C}(\rho).
\]

### 3. 层析冗余

问两个坐标系抽取的线性状态方向有多少重合：

\[
\mathcal R(\mathcal B,\mathcal C)
=
\sum_{jk}(M_{jk}-1/d)^2.
\]

MUB 使其为零，因此每个上下文带来最大正交创新。

### 4. 全局 contextuality

问一个测量情景的全部局部统计是否存在统一的非上下文全局实现。这是多上下文、多操作等价关系与概率约束的全局问题，不能由任意一对基的交换子或 dephasing 顺序完全决定。

因此建议将量子上下文审计记录为向量

\[
\boxed{
\mathfrak C
=
\left(
\mathcal I,\mathcal O,\mathcal R,\mathcal G
\right),
}
\]

而不是单一标量。

特别地，

\[
\boxed{
\mathcal I=1,\quad
\mathcal O=0,\quad
\mathcal R=0
}
\]

是 MUB 对的规范签名：

- 锐利投影最大不兼容；
- 两次完全去相干顺序却无差别；
- 两个概率坐标平面在线性层析意义下完全无冗余。

这一签名揭示“互补”不是单纯的不交换，而是：

\[
\boxed{
\text{局部经典坐标最大不同，同时携带最大独立信息}.
}
\]

---
## 31.10 熵的三重分家：状态混合、测量不确定性与相干余量

为避免把“熵”当成唯一无序标量，本节区分：

### 状态熵

\[
\boxed{
S(\rho)=-\operatorname{Tr}(\rho\log\rho).
}
\]

它测量状态本身的混合度，基无关。

### 上下文结果熵

\[
\boxed{
H_{\mathcal B}(\rho)
=
-\sum_jp_j^{\mathcal B}\log p_j^{\mathcal B}.
}
\]

它依赖观察坐标系。纯态可以有

\[
S(\rho)=0
\]

但在某个 MUB 上有

\[
H_{\mathcal B}(\rho)=\log d.
\]

### 相对熵相干

\[
\boxed{
C_{\mathcal B}(\rho)
=
D(\rho\|
\mathbb E_{\mathcal B}\rho)
=
S(\mathbb E_{\mathcal B}\rho)-S(\rho).
}
\]

它测量相对于指定对角代数被删除的跨扇区关系。

最大混合态满足

\[
S(I/d)=\log d
\]

但对所有基都有

\[
C_{\mathcal B}(I/d)=0.
\]

所以：

\[
\boxed{
\text{高状态熵不等于高量子相干，}
}
\]

\[
\boxed{
\text{高测量熵也不等于状态本身高度混合.}
}
\]

MUB 塔的二次恒等式使用的是 purity／Hilbert–Schmidt 质量，而不是 Shannon 或 von Neumann 熵。不同熵可以通过不等式关联，但不得直接互换定义。

---

## 31.11 无限维推广的正确边界

有限维完整 MUB 塔提供了一个清洁模型，但不能未经证明直接推广到任意无限维 Hilbert 空间。

无限维中需要分别处理：

1. 是否存在合适的互补基、frame 或 POVM；
2. 对角子空间的闭合性；
3. 测量映射是否有 frame 上下界；
4. 状态是否为迹类，二次量是否有限；
5. 无限概率坐标族是否满足统一能量界；
6. 形式相容坐标是否确实来自一个正常状态；
7. 动力学与各条件期望的定义域是否稳定。

合理推广是：在一个 von Neumann 代数 \(\mathcal A\) 中取一族正常条件期望

\[
\mathbb E_i:\mathcal A\to\mathcal C_i,
\]

令可见算子子空间逐层增长，并在 \(L^2(\mathcal A,\omega)\) 或标准形式 Hilbert 空间中研究其正交余量。完成不能只取普通集合逆极限，还必须加入正常性、能量或平方可和条件。这与第 28 节的 bounded-energy inverse limit 完全一致。

---

## 31.12 与既有文献的边界及候选新贡献

以下事实属于成熟理论，不应重新命名为本项目独有发现：

- 一组基测量只给出状态在该基上的概率；
- \(d+1\) 组完整 MUB 可用于最优量子态层析；
- 素数幂维数存在完整 MUB 集；
- 去相干是到交换子代数的条件期望／投影；
- relative entropy of coherence 等于去相干熵增；
- 重复测量可诱导经典 Markov 动力学；
- contextuality 与 measurement incompatibility 不是同一概念。

本稿的候选新贡献位于它们的组合方式：

1. 把 MUB 对角代数组织成第 28 节意义下的严格正交商余塔；
2. 同时定义状态无关的余维率和状态相关的 Hilbert–Schmidt 余质量；
3. 由余质量给出自指对角操作与动力学降阶误差的统一 Lipschitz 界；
4. 识别并证明“MUB 最大不兼容但去相干交换子为零”的框架反例；
5. 将锐利不兼容、粗粒化顺序、层析冗余与全局 contextuality 拆成四维审计；
6. 把重复投影的熵箭头写成逐步删除相干的精确 telescoping identity；
7. 将坐标精化时间与物理动力时间明确分离，再通过自然性缺陷研究二者耦合。

是否具有发表意义仍取决于进一步文献审计、非平凡推广以及至少一个不能由现有 MUB／资源理论定理直接重写得到的新结果。

---
## 31.13 建议形式化模块

建议按以下顺序进入 Lean：

1. `HermitianTracelessDimension`
   \[
   \dim_{\mathbb R}\operatorname{Herm}_d^0=d^2-1.
   \]

2. `BasisDephasingOrthogonalProjection`
   \[
   \mathbb E_{\mathcal B}^2=\mathbb E_{\mathcal B}
   =
   \mathbb E_{\mathcal B}^*.
   \]

3. `SingleContextVisibleRemainderDimension`
   \[
   \dim\mathcal D_{\mathcal B}^0=d-1,
   \quad
   \dim R_{\mathcal B}=d^2-d.
   \]

4. `PureStateProbabilityFiber`
   内点纤维
   \[
   q_{\mathcal B}^{-1}(p)\cong\mathbb T^{d-1}.
   \]

5. `MUBDiagonalSubspaceOrthogonal`
   \[
   \mathcal B\perp_{\mathrm{MUB}}\mathcal C
   \iff
   \mathcal D_{\mathcal B}^0
   \perp
   \mathcal D_{\mathcal C}^0.
   \]

6. `MUBDephasingComposition`
   \[
   \mathbb E_{\mathcal B}\mathbb E_{\mathcal C}(X)
   =
   \operatorname{Tr}(X)I/d.
   \]

7. `SharpIncompatibilityCommutatorSum`
   \[
   \sum_{jk}\|[P_j,Q_k]\|_2^2
   =
   2(d-1)\mathcal I.
   \]

8. `MUBTowerDimension`
   \[
   \dim R_m=(d-1)(d+1-m).
   \]

9. `MUBProbabilityPythagoras`
   \[
   \operatorname{Tr}\rho^2-\frac1d
   =
   \sum_{\ell,j}(p_{\ell j}-1/d)^2+r_m^{(2)}(\rho).
   \]

10. `CompleteMUBTomography`
    \[
    \rho
    =
    I/d+\sum_{\ell,j}(p_{\ell j}-1/d)P_{\ell j}.
    \]

11. `ResidualControlsNaturality`
    \[
    \partial_mF(X)
    \le
    L_F\|(I-P_m)X\|_2.
    \]

12. `NaturalityDefectComposition`
    \[
    \partial_m(FG)
    \le
    \partial_mF\circ G
    +
    L_m(F)\partial_mG.
    \]

13. `RepeatedDephasingEntropyProduction`
    \[
    S(\rho_{n+1})-S(\rho_n)
    =
    D(U\rho_nU^*\|
    \mathbb E_{\mathcal B}(U\rho_nU^*)).
    \]

14. `RepeatedDephasingUnistochastic`
    \[
    p_{n+1}=Tp_n,
    \qquad
    T_{kj}=|\langle b_k,Ub_j\rangle|^2.
    \]

MUB 完整集的存在应在素数幂维数中通过具名经典接口接入；一般维数中不得无条件实例化。

---

## 31.14 最终统一式

本节得到一个比“概率是投影”更精确的层次：

\[
\boxed{
\text{量子态}
=
\text{最大混合原点}
+
\text{全部算子 Hilbert 方向}.
}
\]

\[
\boxed{
\text{一个测量坐标系}
=
\text{到一个 }(d-1)\text{-维经典对角平面的正交投影}.
}
\]

\[
\boxed{
\text{概率}
=
\text{该对角投影的坐标}.
}
\]

\[
\boxed{
\text{相干}
=
\text{仍留在其正交余空间中的状态分量}.
}
\]

\[
\boxed{
\text{MUB}
=
\text{彼此正交、冗余为零的局部经典坐标平面}.
}
\]

\[
\boxed{
\text{完整 MUB 层析}
=
\text{用 }d+1\text{ 个局部经典对角完成全部量子状态方向}.
}
\]

\[
\boxed{
\text{自然性缺陷}
\le
\text{尚未被坐标塔捕获的余质量}.
}
\]

\[
\boxed{
\text{重复测量熵增}
=
\text{每轮投影删除的相干相对熵之和}.
}
\]

而最重要的修正是：

\[
\boxed{
\text{锐利不兼容}
\neq
\text{去相干顺序缺陷}
\neq
\text{层析冗余}
\neq
\text{全局 contextuality}.
}
\]

因此，量子力学不能只解释为“多个投影不交换”，也不能只解释为“概率来自投影”。更完整的结构是：

\[
\boxed{
\text{量子力学}
=
\text{一族局部经典对角坐标}
+
\text{这些坐标的余相干}
+
\text{它们之间的互补几何}
+
\text{无法由单一全局经典坐标同时实现的拼接结构}.
}
\]

在这个意义上，坐标系、概率、熵、时间、逃逸率、Hilbert 空间与对角化确实属于同一个研究对象的不同投影；但它们只有在各自的类型、缺陷量与完成条件被严格区分以后，才构成可检验的新数学，而不是词语上的统一。

## 31.15 参考接口与严格非主张

参考接口：

- I. D. Ivanović, *Geometrical description of quantal state determination*, 1981.
- W. K. Wootters and B. D. Fields, *Optimal state-determination by mutually unbiased measurements*, 1989.
- R. B. A. Adamson and A. M. Steinberg, *Improving Quantum State Estimation with Mutually Unbiased Bases*, 2010.
- D. McNulty and S. Weigert, *Mutually Unbiased Bases in Composite Dimensions — A Review*, 2026.
- J. H. Selby et al., *Contextuality without Incompatibility*, 2023.

严格非主张：

1. 本节不声称一般维数都存在完整 \(d+1\) 组 MUB。
2. 本节不把层析精化指标 \(m\) 等同于物理时间。
3. 本节不把 Hilbert–Schmidt 余质量等同于 Shannon 熵、von Neumann 熵或任意操作性资源单调量。
4. 本节不把 dephasing 通道交换当作锐利测量兼容性。
5. 本节不把 pairwise measurement incompatibility 等同于 generalized contextuality。
6. 本节不把重复投影模型中的熵增解释为所有封闭量子宇宙的基本时间箭头。
7. 本节不从有限维层析完成推出无限维正常状态空间的自动完成。
8. 本节新增结论均为纸面定理；在 Lean proof term、依赖闭包、admission 与冻结收据齐备前不得标记为 `Closed`。

---

# 32. 追加：观察者闭包、Heisenberg 预测塔与多轴完备性
## Observer Closure, Heisenberg Predictive Towers, and Multi-Axis Completeness

### 32.0 文档地位与承重边界

本节把项目中已经反复出现的观察者视角收束为同一个类型正确的结构：

- `OBSERVER-QUANTUM` 中的有限读出、读出纤维、整体自逼近、可见层与隐藏层；
- `WindowObserverDistance` 中由可访问变化量的单位球恢复观察者几何；
- universal solenoid 中可见圆、隐藏核与路径分支；
- `D5/S0/Diagonal` 中自坐标读取、逃逸数量、距离剖面与浓缩；
- 本文前述有限预测完成、Koopman 闭包、Hilbert 商余塔、量子上下文、MUB 坐标塔与 RH 目标余量；
- 项目接口理论中“可访问性、代价、命名、正锥与外部真源必须分层”的原则。

核心结论是：

\[
\boxed{
\text{观察者不是一个点，也不仅是一个投影；观察者是“商 + 闭包规则”。}
}
\]

商决定当前哪些对象不可区分；闭包规则决定这种不可区分性在时间、记忆、上下文、完成与自指操作下是否保持。

本节主要在有限维量子状态空间和一般有限/线性观察系统中给出纸面定理。它不把所有观察者结构宣称为同一个既有 Lean 定义，也不把经验完备、层析完备、上下文完备与自描述完备混为一谈。新增定理在 Lean proof term、依赖闭包和冻结收据齐备以前不得标记为 `Closed`。

---

## 32.1 项目观察者的统一类型

设整体状态对象为 \(X\)，动力学为

\[
T:X\to X.
\]

一个最小观察界面由读出映射

\[
q_O:X\to Y_O
\]

给出。它诱导当前不可区分关系

\[
x\sim_Oy
\iff
q_O(x)=q_O(y),
\]

以及读出纤维

\[
\mathcal F_O(y)
=
q_O^{-1}(y).
\]

但仅有 \(q_O\) 还不能说明观察者如何处理未来、记忆、自指和 refinement。为此定义如下数据。

### 定义 32.1（结构化观察者）

一个结构化观察者记为

\[
\boxed{
\mathfrak O
=
(X,T,q_O,\mathcal M_O,\mathcal A_O,\Delta_O,\mathcal R_O),
}
\]

其中：

\[
\begin{aligned}
X
&=\text{整体状态或对象空间},\\
T
&=\text{整体动力学},\\
q_O
&=\text{当前有限读出},\\
\mathcal M_O
&=\text{观察者可保存和再次读取的账本／记忆},\\
\mathcal A_O
&=\text{观察者可提出的问题或可访问可观测量},\\
\Delta_O
&=\text{观察者允许的自应用／对角操作},\\
\mathcal R_O
&=\text{观察分辨率、资源或接口 refinement 规则}.
\end{aligned}
\]

该定义不是要把不同领域强制编码成同一数据类型，而是给出必须分别类型化的七个位置。具体实例可以省略不适用的数据，但不得把省略的位置默认为“自动存在”。

### 原理 32.2（商与闭包）

观察者的当前商为

\[
X_O=X/{\sim_O}.
\]

若要让 \(X_O\) 成为一个封闭有效世界，还必须证明至少一个闭包条件，例如：

\[
q_OT=T_Oq_O
\]

的动力学下降，

\[
Q_O\Delta=\Delta_OP_O
\]

的对角自然性，

或局部上下文在交叠处的拼接一致性。

所以：

\[
\boxed{
\text{商只回答“现在看起来是否相同”；闭包回答“这种相同能否持续成立”。}
}
\]

---

## 32.2 从有限读出纤维到算子 Hilbert 余空间

现在取有限维 Hilbert 空间

\[
\mathscr H=\mathbb C^d,
\]

实 Hilbert 空间

\[
V=\operatorname{Herm}_d^0
=
\{X=X^*,\ \operatorname{Tr}X=0\},
\]

以及量子态的中心化坐标

\[
X_\rho=\rho-\frac Id.
\]

设观察者拥有有限 effect 族

\[
E_1,\ldots,E_r,
\qquad
0\le E_a\le I.
\]

当前读出为

\[
q_O(\rho)
=
\bigl(
\operatorname{Tr}(\rho E_a)
\bigr)_{a=1}^r.
\]

定义中心化 effect

\[
\widetilde E_a
=
E_a-\frac{\operatorname{Tr}E_a}{d}I
\in V,
\]

可见子空间

\[
\boxed{
V_0
=
\operatorname{span}_{\mathbb R}
\{\widetilde E_1,\ldots,\widetilde E_r\},
}
\]

以及当前余空间

\[
\boxed{
R_0=V_0^\perp.
}
\]

### 定理 32.3（读出纤维—Hilbert 余空间等价）

对任意两个密度矩阵 \(\rho,\sigma\)，下列命题等价：

\[
q_O(\rho)=q_O(\sigma);
\]

\[
\operatorname{Tr}
\bigl(
(\rho-\sigma)E_a
\bigr)=0
\quad
\forall a;
\]

\[
X_\rho-X_\sigma\in R_0;
\]

\[
P_{V_0}X_\rho=P_{V_0}X_\sigma.
\]

#### 证明

因为 \(\operatorname{Tr}(\rho-\sigma)=0\)，

\[
\operatorname{Tr}
\bigl(
(\rho-\sigma)E_a
\bigr)
=
\operatorname{Tr}
\bigl(
(X_\rho-X_\sigma)\widetilde E_a
\bigr).
\]

所以全部读出相同，当且仅当差向量与 \(V_0\) 的生成元全部正交，即属于 \(V_0^\perp\)。最后一项是正交投影核的标准刻画。 \(\square\)

因此 `OBSERVER-QUANTUM` 中的读出纤维，在有限维量子模型中具有一个规范线性骨架：

\[
\boxed{
\text{读出纤维的切向不可见方向}
=
\text{可访问 effect 张成空间的正交余}.
}
\]

但物理纤维并不是整个仿射余空间，而是它与密度算子正锥的交：

\[
\boxed{
\mathcal F_O(y)
=
\left(
\frac Id+x_y+R_0
\right)
\cap
\{\rho\ge0,\ \operatorname{Tr}\rho=1\}.
}
\]

### 推论 32.4（正锥纤维的凸性）

每个非空读出纤维 \(\mathcal F_O(y)\) 是紧凸集。

#### 证明

密度矩阵集合是有限维紧凸集，读出映射是连续仿射映射；单点原像与其交仍为闭凸集。 \(\square\)

这说明项目“正锥—界面”视角是必要的：线性商给出不可见方向，正锥决定其中哪些点仍是物理状态。

---

## 32.3 Heisenberg 预测塔：时间如何生成缺失坐标

设

\[
\Phi:
\operatorname{Herm}_d
\to
\operatorname{Herm}_d
\]

为保持迹的量子通道，\(\Phi^*\) 为其 Heisenberg 对偶：

\[
\operatorname{Tr}(\Phi(\rho)A)
=
\operatorname{Tr}(\rho\Phi^*(A)).
\]

观察者在时刻 \(k\) 对 effect \(E_a\) 的预测概率为

\[
p_{a,k}(\rho)
=
\operatorname{Tr}
\bigl(
\Phi^k(\rho)E_a
\bigr)
=
\operatorname{Tr}
\bigl(
\rho(\Phi^*)^k(E_a)
\bigr).
\]

定义第 \(m\) 阶 Heisenberg 可见空间

\[
\boxed{
V_m
=
\operatorname{span}_{\mathbb R}
\left\{
\widetilde{(\Phi^*)^k(E_a)}
:
1\le a\le r,\ 0\le k\le m
\right\}
\subseteq V,
}
\]

其中波浪号表示去除标量迹部分。定义预测余空间

\[
\boxed{
R_m=V_m^\perp.
}
\]

显然：

\[
V_0\subseteq V_1\subseteq\cdots,
\qquad
R_0\supseteq R_1\supseteq\cdots.
\]

### 定义 32.5（有限未来不可区分）

写

\[
\rho\equiv_m^O\sigma
\]

若

\[
p_{a,k}(\rho)=p_{a,k}(\sigma)
\]

对全部 \(a\) 和 \(0\le k\le m\) 成立。

### 定理 32.6（量子未来词—正交余等价）

对任意 \(\rho,\sigma\)，

\[
\boxed{
\rho\equiv_m^O\sigma
\iff
X_\rho-X_\sigma\in R_m
\iff
P_{V_m}X_\rho=P_{V_m}X_\sigma.
}
\]

#### 证明

对每个 \(a,k\)，

\[
p_{a,k}(\rho)-p_{a,k}(\sigma)
=
\left\langle
X_\rho-X_\sigma,
\widetilde{(\Phi^*)^k(E_a)}
\right\rangle_{\mathrm{HS}}.
\]

全部有限未来概率相等，当且仅当差向量与 \(V_m\) 的全部生成元正交。 \(\square\)

这就是本文有限确定系统中 Nerode/未来读出完成在量子算子 Hilbert 空间中的精确对应：

\[
\boxed{
\text{经典未来输出词}
\longleftrightarrow
\text{Heisenberg 轨道上的 effect 期望值}.
}
\]

---

## 32.4 “一次稳定即永久稳定”的量子观察者版本

### 定理 32.7（Heisenberg 塔一次稳定即永久稳定）

若某个 \(m\) 满足

\[
V_m=V_{m+1},
\]

则

\[
\boxed{
V_{m+s}=V_m
\quad
\forall s\ge0.
}
\]

等价地，

\[
R_{m+s}=R_m
\quad
\forall s\ge0.
\]

#### 证明

\(V_{m+1}=V_m\) 意味着对每个生成元及其前 \(m\) 次 Heisenberg 像，再施加一次 \(\Phi^*\) 后仍落在 \(V_m\)。因此

\[
\Phi^*(V_m)\subseteq V_m
\]

（标量方向单独保持，不影响无迹部分）。归纳得到全部更高次像仍在 \(V_m\)，所以不再出现新方向。 \(\square\)

### 推论 32.8（有限稳定深度界）

令

\[
m_*
=
\min\{m:V_m=V_{m+1}\}.
\]

则

\[
\boxed{
m_*
\le
\dim V_\infty-\dim V_0
\le
d^2-1-\dim V_0,
}
\]

其中

\[
V_\infty=\bigcup_mV_m=V_{m_*}.
\]

#### 证明

每次未稳定时，有限维子空间维数至少增加一；总维数不超过 \(d^2-1\)。 \(\square\)

这里的“一次稳定”并不表示：

- 量子态停止演化；
- 输出概率成为常数；
- 通道达到固定点；
- 熵不再变化。

它只表示：

\[
\boxed{
\text{更远的时间不再产生新的线性预测坐标。}
}
\]

因此，时间可以持续发生，而观察者的预测坐标系统已经闭合。

---

## 32.5 最小线性预测观察者

定义最终预测不可见空间

\[
R_\infty
=
\bigcap_{m\ge0}R_m
=
V_\infty^\perp.
\]

定义预测商

\[
\boxed{
Z_O^{\mathrm{lin}}
=
V/R_\infty.
}
\]

通过 Hilbert 正交代表，它规范同构于 \(V_\infty\)。于是可取最小预测状态为

\[
\boxed{
z_O(\rho)
=
P_{V_\infty}X_\rho.
}
\]

### 定理 32.9（全部未来统计的充分性）

全部未来概率

\[
\bigl(
p_{a,k}(\rho)
\bigr)_{a,k}
\]

只依赖于 \(z_O(\rho)\)。更具体地，

\[
z_O(\rho)=z_O(\sigma)
\iff
p_{a,k}(\rho)=p_{a,k}(\sigma)
\quad
\forall a,k\ge0.
\]

#### 证明

应用定理 32.6，并令 \(m\ge m_*\)。 \(\square\)

### 定理 32.10（最小性泛性质）

设

\[
L:V\to W
\]

为线性摘要，并假设所有未来概率都能由 \(L(X_\rho)\) 唯一确定。则存在唯一线性映射

\[
h:\operatorname{range}L\to V_\infty
\]

使

\[
\boxed{
P_{V_\infty}=h\circ L.
}
\]

特别地，

\[
\boxed{
\dim\operatorname{range}L
\ge
\dim V_\infty.
}
\]

#### 证明

若 \(Lx=0\)，则 \(x\) 与零向量具有相同摘要，因此全部未来读出线性泛函在 \(x\) 上为零，即 \(x\in R_\infty\)。所以

\[
\ker L\subseteq R_\infty=\ker P_{V_\infty}.
\]

由线性映射的商泛性质，\(P_{V_\infty}\) 唯一地通过 \(L\) 因子化。维数不等式随即成立。 \(\square\)

所以项目中的“最小预测观察者完成”在量子有限维情形不是一条比喻，而是：

\[
\boxed{
\text{初始 effect 空间的最小 Heisenberg 不变线性闭包}.
}
\]

这与经典有限系统中“当前读出代数的最小 Koopman 不变闭包”完全对偶。

---

## 32.6 时间作为坐标生成器

### 定义 32.11（时间层析完备）

若

\[
V_\infty=V=\operatorname{Herm}_d^0,
\]

则称固定观察界面 \((E_a)\) 在动力学 \(\Phi\) 下时间层析完备。

此时：

\[
\boxed{
\text{一个当下不完备的测量，通过其 Heisenberg 时间轨道可以变成完备坐标系。}
}
\]

### 定理 32.12（有限时间层析）

若时间层析完备，则存在

\[
m\le d^2-1-\dim V_0
\]

使前 \(m+1\) 个时间层的概率已经唯一确定任意量子态。

#### 证明

由推论 32.8，\(V_m\) 在有限步达到 \(V\)。定理 32.6 此时给出状态分离。 \(\square\)

### 例 32.13（一个 qubit 的固定二元测量由时间生成完整坐标）

取 qubit Pauli 算子 \(X,Y,Z\)。选择酉算子 \(U\)，使共轭作用循环三个轴：

\[
U^*ZU=X,
\qquad
U^*XU=Y,
\qquad
U^*YU=Z.
\]

例如可取 Bloch 球上绕轴 \((1,1,1)/\sqrt3\) 旋转 \(2\pi/3\) 的酉提升。

当前只测量

\[
E_\pm=\frac{I\pm Z}{2}.
\]

则其中心化 Heisenberg 轨道依次张成

\[
Z,\quad X,\quad Y.
\]

因此

\[
V_0=\operatorname{span}\{Z\},
\]

\[
V_1=\operatorname{span}\{Z,X\},
\]

\[
V_2=\operatorname{span}\{Z,X,Y\}
=
\operatorname{Herm}_2^0.
\]

所以：

\[
\boxed{
\text{同一个二元测量在三个时间切片上的集合统计足以完成 qubit 层析。}
}
\]

这里必须使用独立制备的同一初态或其他不会把测量反作用混入动力学的实验协议。它不是说在一条经历投影坍缩的单样本轨迹上，可以无扰动地同时读出 \(X,Y,Z\)。

这一例子给“时间是观察者对整体的展开”一个严格而有限的版本：

\[
\boxed{
\text{物理动力学在 Heisenberg 图像中旋转问题；观察者沿时间收集这些问题的坐标。}
}
\]

---

## 32.7 预测余质量与未来误差

对状态差

\[
X=X_\rho-X_\sigma
\]

定义第 \(m\) 层预测余质量

\[
\boxed{
r_m^O(X)
=
\|P_{R_m}X\|_2^2.
}
\]

定义创新壳层

\[
\boxed{
E_{m+1}^O
=
V_{m+1}\cap V_m^\perp.
}
\]

则

\[
R_m
=
E_{m+1}^O\oplus R_{m+1}.
\]

### 定理 32.14（时间坐标创新递推）

\[
\boxed{
r_m^O(X)
=
r_{m+1}^O(X)
+
\|P_{E_{m+1}^O}X\|_2^2.
}
\]

#### 证明

由上述正交直和和 Pythagoras。 \(\square\)

所以每多观察一个时间层，真正增加的不是“又一次重复测量”，而是：

\[
\boxed{
(\Phi^*)^{m+1}\mathcal A_O
\text{ 中相对于全部较早时间无法线性解释的创新方向}.
}
\]

### 定理 32.15（未来概率误差的精确余相关）

令

\[
A_{a,k}
=
\widetilde{(\Phi^*)^k(E_a)}.
\]

若观察者用 \(P_{V_m}X_\rho\) 代替完整状态，则对任意未来 \(a,k\)，

\[
\boxed{
\operatorname{Tr}
\bigl(
(\rho-\rho_m)E_{a,k}
\bigr)
=
\left\langle
P_{R_m}X_\rho,
P_{R_m}A_{a,k}
\right\rangle_{\mathrm{HS}},
}
\]

其中 \(\rho_m\) 仅表示具有中心化坐标 \(P_{V_m}X_\rho\) 的线性预测代表；它未必自身是正密度矩阵。

因此：

\[
\boxed{
|\Delta p_{a,k}^{(m)}|
\le
\sqrt{r_m^O(X_\rho)}
\,
\|P_{R_m}A_{a,k}\|_2.
}
\]

#### 证明

\(X_\rho-P_{V_m}X_\rho=P_{R_m}X_\rho\)。再将 \(A_{a,k}\) 分解为 \(V_m\) 与 \(R_m\) 两部分；前者与状态余向量正交。最后应用 Cauchy–Schwarz。 \(\square\)

当 \(k\le m\) 时，

\[
A_{a,k}\in V_m,
\]

故误差严格为零。对于更远未来，误差由“状态余量”和“未来问题尚未进入当前坐标塔的余量”共同决定。

这给出一个双余量原则：

\[
\boxed{
\text{预测失败}
=
\text{隐藏状态方向}
\times
\text{隐藏未来问题方向}.
}
\]

---

## 32.8 观察者几何：可访问变化量决定距离

项目 `WindowObserverDistance` 的核心结构可以抽象如下。设观察者可访问一族实可观测量 \(\mathcal A_O^{\mathrm{sa}}\)，并给定变化半范数

\[
L_O(A)\in[0,\infty].
\]

定义观察者对偶距离

\[
\boxed{
d_O(\rho,\sigma)
=
\sup
\left\{
|\operatorname{Tr}((\rho-\sigma)A)|:
A\in\mathcal A_O^{\mathrm{sa}},
\ L_O(A)\le1
\right\}.
}
\]

有限循环窗口中的仓库定理说明，在其特定一步更新缺陷半范数下，该对偶距离精确恢复循环图距离。该结果提示：

\[
\boxed{
\text{几何不是只由载体集合给定，而由观察者允许哪些函数以及怎样计价其变化共同给定。}
}
\]

### 定理 32.16（观察 refinement 的距离单调性）

若

\[
\mathcal A_m\subseteq\mathcal A_{m+1}
\]

且 \(L_{m+1}\) 在 \(\mathcal A_m\) 上限制为 \(L_m\)，则

\[
\boxed{
d_m(\rho,\sigma)
\le
d_{m+1}(\rho,\sigma).
}
\]

#### 证明

第 \(m\) 层 supremum 的可行集合包含于第 \(m+1\) 层。 \(\square\)

### 推论 32.17（零距离纤维）

若 \(L_m\) 的单位球线性张成 \(\mathcal A_m^{\mathrm{sa}}\)，则

\[
d_m(\rho,\sigma)=0
\]

当且仅当 \(\rho,\sigma\) 在 \(\mathcal A_m\) 上给出相同状态限制。

因此读出纤维也可以被写成观察者伪度量的零距离类：

\[
\boxed{
\mathcal F_O(\rho)
=
\{\sigma:d_O(\rho,\sigma)=0\}.
}
\]

若完成代数能够分离全部状态，则极限伪度量成为真正度量。若仍有隐藏核，则不同整体状态可在观察者几何中距离为零。

---

## 32.9 可见圆、隐藏核与扇区完备性

universal solenoid 的项目结构提供了一个重要反例：观察者即使对某个可见相位坐标完全精确，也可能仍然无法分辨全局路径扇区。

设

\[
\pi:\Sigma_\infty\to\mathbb T
\]

为可见圆投影，隐藏核为

\[
K_\infty=\ker\pi.
\]

一个只通过 \(\pi\) 读取的观察者满足：

\[
q_O(x)=q_O(x+k)
\qquad
(k\in K_\infty).
\]

所以其当前不可见核至少包含整个隐藏纤维。仓库已有路径轨道分类说明，solenoid 中的路径连通关系由实流轨道刻画，隐藏核偏移参与路径分支标签。

由此必须区分：

\[
\boxed{
\begin{aligned}
\text{点分离完备}
&=\text{能否区分不同整体点},\\
\text{动力预测完备}
&=\text{能否区分未来读出不同的状态},\\
\text{扇区完备}
&=\text{能否分辨路径分支／隐藏核标签}.
\end{aligned}
}
\]

它们互不自动推出。

一个观察者可以对可见圆上的位置拥有精确几何，却对隐藏核上的两个点给出零距离；也可以通过逐 prime-adic refinement 最终分离点，但仍需另行证明这些坐标如何恢复路径、流轨道或物理扇区结构。

因此：

\[
\boxed{
\text{逆极限点完成}
\neq
\text{拓扑路径完成}
\neq
\text{动力扇区完成}.
}
\]

---

## 32.10 经验完备不推出自描述完备

假设一个量子观察者满足

\[
V_\infty=V.
\]

它可以从全部未来统计唯一重构当前密度矩阵。这叫经验／层析完备。

现在另给一个同层自模型评价表

\[
E:A\times A\to Y
\]

与无不动点扭曲

\[
\tau:Y\to Y.
\]

对角对象为

\[
\Delta_\tau(E)(a)
=
\tau(E(a,a)).
\]

Cantor–Lawvere 型论证仍可使该对角对象逃出当前行像。层析完备只说明观察者能识别系统状态，不说明它能够在同一类型中列尽所有关于自身的评价函数。

### 命题 32.18（经验完备与反身完备分离）

存在观察者满足：

\[
\boxed{
\text{当前状态完全可重构}
}
\]

但不满足：

\[
\boxed{
\text{所有同类型自评价均可由其内部名单捕获}.
}
\]

#### 证明

取任意有限维且信息完备的量子层析界面，故状态可重构。独立地，若存在一个声称枚举 \(Y^A\) 全部函数的同层评价名单，则对角扭曲构造逃逸函数。两种完备性涉及不同类型，前者不能消除后者的对角障碍。 \(\square\)

所以：

\[
\boxed{
\text{知道自己的完整状态}
\neq
\text{拥有关于自己的一切可能真命题或模型}.
}
\]

这是项目观察者理论与普通量子层析之间最独特的接缝之一。

---

## 32.11 六个既有反例迫使观察者完备性成为向量

以下结构已在本文不同章节出现。

### 反例 A：预测闭合但不忠实

常值读出对未来已经完全闭合，其最小预测状态只有一个点；但它不能区分任何微观状态。

### 反例 B：层析完备但自描述不完备

定理 32.18。

### 反例 C：最大锐利不兼容但粗粒化顺序缺陷为零

MUB 投影最大不兼容，而对应 dephasing 通道满足

\[
\mathbb E_{\mathcal B}\mathbb E_{\mathcal C}
=
\mathbb E_{\mathcal C}\mathbb E_{\mathcal B}.
\]

### 反例 D：目标完成但空间未完成

Nyman–Beurling 塔中 RH 只要求

\[
P_{R_\infty}\chi=0,
\]

不要求

\[
R_\infty=0.
\]

### 反例 E：有限层逐点逼近但非统一完备

递增有限维投影可满足

\[
P_nx\to x
\quad
\forall x,
\]

但每个真有限阶段仍有

\[
\|I-P_n\|=1.
\]

### 反例 F：可见坐标精确但隐藏扇区未分辨

solenoid 可见圆读出不能自动恢复隐藏核分支。

因此不存在一个不加类型说明的标量“观察者完整度”。

### 定义 32.19（观察者多轴审计）

定义观察者闭合向量

\[
\boxed{
\mathbf C(\mathfrak O)
=
(
C_{\mathrm{sep}},
C_{\mathrm{pred}},
C_{\mathrm{dyn}},
C_{\mathrm{tom}},
C_{\mathrm{ctx}},
C_{\mathrm{sec}},
C_{\mathrm{ref}},
C_{\mathrm{lim}}
).
}
\]

各分量分别测量：

\[
\begin{aligned}
C_{\mathrm{sep}}
&=\text{当前状态分离能力},\\
C_{\mathrm{pred}}
&=\text{未来读出的预测闭合},\\
C_{\mathrm{dyn}}
&=\text{整体动力学能否下降到观察商},\\
C_{\mathrm{tom}}
&=\text{指定状态族的层析完备},\\
C_{\mathrm{ctx}}
&=\text{局部经典图能否全局拼接},\\
C_{\mathrm{sec}}
&=\text{路径／隐藏核／超选择扇区分辨},\\
C_{\mathrm{ref}}
&=\text{自应用评价的反身闭合},\\
C_{\mathrm{lim}}
&=\text{全部兼容有限视图是否由整体实现}.
\end{aligned}
\]

接口价格、计算资源和记忆容量另作为代价向量

\[
\mathbf P(\mathfrak O)
\]

记录，不应伪装成数学完备性的一个分量。

---

## 32.12 观察 refinement 的双层自然性缺陷分解

设

\[
V_m\subseteq V_n\subseteq V,
\qquad
m\le n,
\]

正交投影分别为 \(P_m,P_n\)。设

\[
F:V\to V
\]

为 \(L\)-Lipschitz 操作，粗层模型为

\[
F_m=P_mF|_{V_m}.
\]

定义第 \(m\) 层自然性缺陷

\[
\partial_mF(X)
=
\|P_mF(X)-F_m(P_mX)\|.
\]

再定义从细层 \(n\) 向粗层 \(m\) 的内层模型缺陷

\[
\boxed{
\partial_{m\leftarrow n}F(Y)
=
\|P_mF(Y)-F_m(P_mY)\|,
\qquad
Y\in V_n.
}
\]

### 定理 32.20（尾余量—跨层缺陷分解）

\[
\boxed{
\partial_mF(X)
\le
L\|(I-P_n)X\|
+
\partial_{m\leftarrow n}F(P_nX).
}
\]

#### 证明

插入中间项 \(P_mF(P_nX)\)：

\[
\begin{aligned}
\partial_mF(X)
&\le
\|P_m(F(X)-F(P_nX))\|\\
&\quad+
\|P_mF(P_nX)-F_m(P_mX)\|.
\end{aligned}
\]

第一项不超过 \(L\|(I-P_n)X\|\)。又因 \(P_mP_n=P_m\)，第二项正是定义中的跨层缺陷。 \(\square\)

这条式子把观察误差分成两种不同来源：

\[
\boxed{
\text{完整世界到细观察仍未捕获的尾余量}
}
\]

与

\[
\boxed{
\text{细观察已经捕获的信息在粗层有效模型中仍不能自然下降的失配}.
}
\]

仅仅扩大窗口只能自动减小第一项；第二项必须通过模型自然性另行控制。

---

## 32.13 时间、记忆与熵的严格分工

Heisenberg 塔的 refinement 指标 \(m\) 表示未来坐标深度。它与物理时间步 \(k\) 有联系，因为生成元来自 \((\Phi^*)^kE_a\)，但二者仍扮演不同角色：

\[
k=\text{被预测系统的动力时间},
\]

\[
m=\text{观察者已经纳入模型的最大时间深度}.
\]

稳定深度 \(m_*\) 衡量的是最小线性预测记忆，而不是熵增速度。

定义线性预测复杂度

\[
\boxed{
C_{\mathrm{lin}}(\mathfrak O)
=
\dim V_\infty.
}
\]

定义额外闭合成本

\[
\boxed{
C_{\mathrm{add}}(\mathfrak O)
=
\dim V_\infty-\dim V_0.
}
\]

它们是维数资源，而不是 Shannon 或 von Neumann 熵。

只有在给定状态先验、测量记录过程或重复粗粒化动力学以后，才产生概率熵。特别地，对过程

\[
\rho_{n+1}
=
\mathbb E_{\mathcal B}
(U\rho_nU^*)
\]

本文已经证明每轮熵增等于该轮被删除的相对熵相干。该结论来自不可逆 dephasing，而不是来自 Heisenberg 坐标塔本身。

因此：

\[
\boxed{
\text{时间生成新坐标}
\not\Rightarrow
\text{时间必然产生熵}.
}
\]

以及：

\[
\boxed{
\text{预测闭合深度}
\not\Rightarrow
\text{物理退化时间}.
}
\]

---

## 32.14 算术观察者与目标相对完备

有限 prime ledger、有限零点窗口、Li 测试阶数和 Nyman–Beurling 生成空间都可被视为不同的算术观察界面，但它们的“完备”目标不同。

例如 Nyman–Beurling 观察塔只需对目标

\[
\chi=\mathbf1_{(0,1)}
\]

满足

\[
P_{R_\infty}\chi=0
\]

即可等价于 RH；整个 \(L^2\) 余空间可以非零。

这给出：

\[
\boxed{
\text{目标相对完备}
\neq
\text{全空间层析完备}.
}
\]

类似地，有限零点窗口可以对窗口内零点位置完全准确，却对窗口外是否存在离线零点没有统一控制；Li 高阶测试可以放大某一离线轨道，却仍需控制其余全部轨道的全局余项。

所以项目的算术视角再次确认：

\[
\boxed{
\text{观察者必须声明“对什么命题、什么目标、什么范数完备”。}
}
\]

未注明目标的“观察者已经看见整体”不是数学命题。

---

## 32.15 项目独特视角的统一闭合图

本节可以把项目各分支重新排列为同一个闭合图：

\[
\boxed{
\begin{array}{c}
\text{整体状态／对象 }X\\
\downarrow\ q_O\\
\text{有限读出与纤维}\\
\downarrow\ \text{Hilbert／代数表示}\\
\text{可见子空间 }V_0
\oplus
\text{余空间 }R_0\\
\downarrow\ \Phi^*\text{ 或 refinement}\\
\text{预测／坐标闭包 }V_\infty\\
\downarrow\\
\text{最小有效观察状态 }X/R_\infty\\
\downarrow\ \Delta\\
\text{自描述闭合测试与对角逃逸}\\
\downarrow\ \varprojlim\\
\text{全部相对视图的可实现完成}
\end{array}
}
\]

每一条箭头都可能失败，并对应不同缺陷：

\[
\boxed{
\begin{aligned}
\ker q_O
&=\text{当前不可见差异},\\
R_\infty
&=\text{全部未来仍不可见差异},\\
\partial_O T
&=\text{动力学下降缺陷},\\
\partial_O\Delta
&=\text{自指自然性缺陷},\\
\mathcal G_{\mathrm{ctx}}
&=\text{上下文拼接缺陷},\\
K_{\mathrm{sec}}
&=\text{隐藏扇区核},\\
\mathcal C_{\mathrm{real}}
&=\text{兼容但不可实现的极限族}.
\end{aligned}
}
\]

这使“观察者”不再是额外放入系统中的神秘主体，而成为一组可审计的数学接口。

---

## 32.16 最强的新解释：观察者是相对同一性的稳定器

单一读出 \(q_O\) 只定义瞬时同一性：

\[
x\sim_Oy.
\]

预测闭包把它稳定到全部未来：

\[
x\sim_O^\infty y
\iff
q_OT^k(x)=q_OT^k(y)
\quad
\forall k.
\]

上下文闭包要求不同局部读出在交叠处兼容。

极限闭包要求每个相容局部族可由整体实现。

反身闭包则要求观察者关于自身的描述操作也能下降到该商；对角化说明这一步可能必然失败。

因此最凝练的项目式定义是：

\[
\boxed{
\text{观察者}
=
\text{选择相对同一性，并尝试让这种同一性在时间、上下文、完成和自指下稳定。}
}
\]

由此：

\[
\boxed{
\text{相对性}
=
\text{不同观察者选择不同同一性关系};
}
\]

\[
\boxed{
\text{时间}
=
\text{同一性关系在动力学下接受稳定性检验};
}
\]

\[
\boxed{
\text{概率}
=
\text{状态对观察者可访问事件的权重};
}
\]

\[
\boxed{
\text{熵}
=
\text{观察商删除差异后的统计代价};
}
\]

\[
\boxed{
\text{对角化}
=
\text{同一层自描述不能完全稳定的证书};
}
\]

\[
\boxed{
\infty
=
\text{任何有限稳定器都可能留有余核，但相容 refinement 可形成完成}.
}
\]

这比“观察者看到世界的一部分”更强：观察者不是被动截取一幅画面，而是在定义什么可以被当作同一个对象，并承担该定义在未来是否自洽的全部代价。

---

## 32.17 建议形式化模块

建议按以下顺序进入 Lean。

1. `EffectReadoutFiberOrthogonal`
   \[
   q(\rho)=q(\sigma)
   \iff
   X_\rho-X_\sigma\in V_0^\perp.
   \]

2. `HeisenbergObservableTower`
   定义 \(V_m\)、\(R_m\) 及其单调性。

3. `QuantumFutureEquivalence`
   \[
   \rho\equiv_m\sigma
   \iff
   X_\rho-X_\sigma\in R_m.
   \]

4. `HeisenbergTowerStableForever`
   \[
   V_m=V_{m+1}
   \Rightarrow
   \forall s,\ V_{m+s}=V_m.
   \]

5. `FiniteQuantumObserverDepth`
   \[
   m_*\le d^2-1-\dim V_0.
   \]

6. `MinimalLinearPredictiveObserver`
   证明 \(P_{V_\infty}\) 的因子化泛性质。

7. `QubitTemporalTomographyCycle`
   形式化 Pauli 三轴循环例。

8. `PredictiveResidualPythagoras`
   \[
   r_m=r_{m+1}+\|P_{E_{m+1}}X\|^2.
   \]

9. `FutureProbabilityResidualBound`
   \[
   |\Delta p|
   \le
   \|P_{R_m}X\|_2
   \|P_{R_m}A\|_2.
   \]

10. `ObserverDualMetricRefinement`
    证明可观测代数扩张下距离单调。

11. `TailTransferDefect`
    \[
    \partial_mF(X)
    \le
    L\|(I-P_n)X\|
    +
    \partial_{m\leftarrow n}F(P_nX).
    \]

12. `TomographicNotReflexive`
    将信息完备读出与 Lawvere 型对角逃逸作为不同类型的非蕴含命题陈述。

现有 `WindowObserverDistance`、finite predictive completion、MUB tower、solenoid path-orbit classification 与 diagonal escape-count 模块应作为实例或依赖锚点，而不是在新模块中复制证明。

---

## 32.18 严格非主张

1. 本节不声称仓库中所有名为 observer 的结构已经共享同一个 Lean 类型。
2. 本节不把读出纤维的线性余空间与完整物理纤维等同；后者还受正锥约束。
3. 本节不把时间层析中的 refinement 深度等同于物理时间或热力学时间。
4. 本节不声称单次侵入式测量轨迹可以无扰动完成 Heisenberg 层析。
5. 本节不把预测闭合等同于微观状态忠实性。
6. 本节不把层析完备等同于自描述完备。
7. 本节不把点分离、路径分支分离和超选择扇区分离视为同一个条件。
8. 本节不把可见坐标的 Hilbert–Schmidt 余质量直接等同于 Shannon 熵、von Neumann 熵或操作性资源单调量。
9. 本节不把有限观察深度界推广为无限维系统中的统一有限界。
10. 本节新增结论均为纸面定理；在 Lean 内核验证以前不得标记为 `Closed`。

## 32.19 最终结论

项目中“观察者”的全部独特视角可以压缩成三个连续升级的对象：

\[
\boxed{
\text{读出观察者}
=
\text{当前商 }X/\ker q;
}
\]

\[
\boxed{
\text{预测观察者}
=
\text{该商在动力学下的最小不变闭包};
}
\]

\[
\boxed{
\text{反身观察者}
=
\text{预测闭包再接受自指、上下文和极限实现检验}.
}
\]

在有限维量子系统中，预测观察者由 Heisenberg effect 轨道精确给出：

\[
\boxed{
V_\infty
=
\operatorname{span}
\{(\Phi^*)^k\widetilde E_a:a,k\}.
}
\]

它的正交余：

\[
\boxed{
R_\infty=V_\infty^\perp
}
\]

是所有未来测量仍无法看见的差异。

时间可以通过 \(\Phi^*\) 生成新坐标；概率是状态在这些坐标上的评价；预测误差由状态余量与未来问题余量的内积控制；观察者几何由允许的可观测变化量决定；solenoid 隐藏核提醒我们点、路径和扇区完成不同；对角化则说明，即使经验状态已经完全可见，同层自描述仍可能逃逸。

因此本节的中心公式不是一个新的宇宙口号，而是一组可检验对象：

\[
\boxed{
\begin{aligned}
V_m
&=
\operatorname{span}\{(\Phi^*)^k\widetilde E_a:k\le m\},\\
R_m
&=
V_m^\perp,\\
\rho\equiv_m^O\sigma
&\iff
X_\rho-X_\sigma\in R_m,\\
V_m=V_{m+1}
&\Rightarrow
V_{m+s}=V_m,\\
|\Delta p_{a,k}^{(m)}|
&\le
\|P_{R_m}X_\rho\|_2
\|P_{R_m}A_{a,k}\|_2.
\end{aligned}
}
\]

它们给出一个新的统一解释：

\[
\boxed{
\text{观察不是从整体中静态切下一块；观察是沿时间生成坐标、收缩余核，并检验所得相对同一性能否闭合。}
}
\]

---

## 32.20 观察者闭包算子与动力学下降的最小修复

令 \(V\) 为有限维实 Hilbert 空间，\(K:V\to V\) 为 Heisenberg/Koopman 线性算子，\(W\subseteq V\) 为当前可见可观测子空间。定义

\[
\boxed{
\operatorname{Cl}_K(W)
=
\operatorname{span}
\{K^n w:n\ge0,\ w\in W\}.
}
\]

有限维时无需另取闭包；无限维时使用 Hilbert 闭包。

### 定理 32.21（观察者闭包是最小不变闭包）

\(\operatorname{Cl}_K\) 满足：

\[
\boxed{
W\subseteq\operatorname{Cl}_K(W)
}
\]

（扩张性），

\[
\boxed{
W_1\subseteq W_2
\Longrightarrow
\operatorname{Cl}_K(W_1)
\subseteq
\operatorname{Cl}_K(W_2)
}
\]

（单调性），

\[
\boxed{
\operatorname{Cl}_K(
\operatorname{Cl}_K(W)
)
=
\operatorname{Cl}_K(W)
}
\]

（幂等性），并且它是包含 \(W\) 的最小 \(K\)-不变子空间。

#### 证明

前三项由幂次轨道张成定义直接得到。若 \(U\supseteq W\) 且 \(K(U)\subseteq U\)，则归纳有 \(K^nW\subseteq U\)，故 \(\operatorname{Cl}_K(W)\subseteq U\)。 \(\square\)

因此，预测观察者并不是任意增加记忆，而是对当前问题空间施加一个规范闭包算子。

在量子情形取

\[
K(A)=
\widetilde{\Phi^*(A)}.
\]

则

\[
V_\infty=\operatorname{Cl}_K(V_0).
\]

### 定理 32.22（最终余核是动力学同余）

令 Schrödinger 侧线性演化为 \(\Phi\)，并令

\[
R_\infty=V_\infty^\perp.
\]

则

\[
\boxed{
\Phi(R_\infty)\subseteq R_\infty.
}
\]

因此动力学唯一下降到商

\[
V/R_\infty.
\]

#### 证明

若 \(x\in R_\infty\)，对任意 \(A\in V_\infty\)，

\[
\langle\Phi x,A\rangle
=
\langle x,\Phi^*A\rangle.
\]

由于 \(V_\infty\) 对中心化 Heisenberg 演化不变，\(\Phi^*A\) 的无迹部分仍属于 \(V_\infty\)；而 \(x\) 无迹，标量部分不贡献配对。所以右侧为零，故 \(\Phi x\in V_\infty^\perp\)。商映射的良定义性随即成立。 \(\square\)

### 推论 32.23（预测闭包是动力学自然性的最小修复）

当前读出空间 \(V_0\) 未必允许封闭有效动力学；但其观察闭包

\[
V_\infty=\operatorname{Cl}_{\Phi^*}(V_0)
\]

使最终不可见关系成为动力学同余。任何包含 \(V_0\) 且允许全部未来读出封闭演化的可观测子空间，都必须包含 \(V_\infty\)。

所以：

\[
\boxed{
\text{观察者闭包}
=
\text{把瞬时商修复成动力学商所需的最小坐标扩张}.
}
\]

这给项目所有观察者视角一个更统一的内核：

\[
\boxed{
\text{观察者}
=
\text{初始问题空间}
+
\text{使其在目标操作下稳定的最小闭包}.
}
\]

对于时间，目标操作是 \(\Phi^*\)；对于自指，目标操作是 \(\Delta\)；对于上下文，目标操作是限制与拼接；对于完成，目标操作是全部 bonding maps；对于算术账本，目标操作是 prime/zero/test refinement。不同领域共享的是“闭包问题”的形状，而不是同一个未经证明的对象同一性。

---

# 33. 追加：观察者叶层几何、记录作用、混合时间与三重闭包
## Observer Leaf Geometry, Record Action, Hybrid Time, and the Three Closures

### 33.0 研究位置、仓库锚点与严格边界

第 32 节把观察者收紧为“当前商 + 使该商在目标操作下稳定的最小闭包”。本节继续结合项目已经形式化的独特结构：

- `D5/S3/Quantum/ObserverAlgebra.lean` 与 `ObserverCommutator.lean` 中的读出—更新协变和精确交换子公式；
- `D5/S3/Observer/ObserverMetric.lean`、`MetricGeometry/OrbitConnesDistance.lean`、`WindowObserverDistance.lean` 与 `VisiblePhaseInfinity.lean` 中的更新缺陷半范数、有限叶内距离和跨可见相位无穷距离；
- `HiddenFlow/ContinuousRigidity.lean`、`DiscreteRigidity.lean`、`StreamlineExistence.lean` 中的可见连续流、隐藏素数地址与离散跳变阻碍；
- `Conditioning.lean`、`BornReduction.lean`、`MeasurementMarginal.lean` 中的 Born 权重、条件分支、未读测量和环境边缘；
- `ObserverMemory/MultiCopyErasure.lean`、`LedgerEnvironmentBridge.lean`、`JointCoherentReversal.lean` 中的多记录乘法、退相干与联合反演；
- `FiniteReadoutKernel.lean`、`TwoTimeKnowledge.lean`、`FiniteForgettingCertificate.lean` 中的读出商、知识因子化、遗忘和追加式审计；
- `WindowRegister.lean`、`MatrixUnitCertificate.lean`、`WindowAlgebra/WindowGeneration.lean`、`WindowCharacter.lean` 中的 Weyl 对、全矩阵代数生成、标量交换子和无角色定理；
- `WindowRegisterCRT.lean` 与 `PrimePowerTensorTower.lean` 中的 CRT 地址分解和素数幂张量塔；
- `RecordCorrelationMonogamy.lean` 与 `ClassicalAnswerTableExclusion.lean` 中的同一记录指针互补约束及经典答案表双重排除。

这些结果共同指向一个比“观察者是投影”更强的结构：

\[
\boxed{
\text{观察者是一个带有读出、更新、记忆、代价和闭包规则的相对状态机。}
}
\]

本节的候选新贡献不是重新陈述交叉积、Connes 距离、量子测量或 CRT，而是把下列此前分居不同模块的对象放入同一组定理：

\[
\boxed{
\text{读出交换子}
\longleftrightarrow
\text{观察者 Lipschitz 半范数}
\longleftrightarrow
\text{叶层扩展距离};
}
\]

\[
\boxed{
\text{环境记录重叠乘积}
\longleftrightarrow
\text{可加记录作用}
\longleftrightarrow
\text{相干生存率与可逆性门槛};
}
\]

\[
\boxed{
\text{有限读出核}
\longleftrightarrow
\text{知识代数}
\longleftrightarrow
\text{遗忘余量};
}
\]

\[
\boxed{
\text{CRT 素数幂分解}
\longleftrightarrow
\text{局部观察扇区}
\longleftrightarrow
\text{高阶关联余空间}.
}
\]

本节不主张：所有物理时间都是隐藏地址跳数；记录作用就是 von Neumann 熵；无穷观察距离就是物理空间距离；全矩阵代数生成无条件推出自然界量子力学；素数幂张量分解自动解决一般维数 MUB；相干恢复可以在丢弃环境以后无条件完成。新增定理仍为纸面推导，未经 Lean proof term、依赖闭包、admission 和冻结收据不得标记为 `Closed`。

---

## 33.1 读出—更新交换子就是观察者的一阶导数

设地址集合为 \(I\)，寄存器 Hilbert 空间为

\[
\mathscr H_I=\ell^2(I),
\]

可逆更新为置换

\[
\tau:I\to I.
\]

定义更新酉算子和读出乘法算子：

\[
(U_\tau\psi)(i)=\psi(\tau^{-1}i),
\]

\[
(M_f\psi)(i)=f(i)\psi(i).
\]

定义更新差分：

\[
\boxed{
\delta_\tau f
=f\circ\tau^{-1}-f.
}
\]

仓库已经逐坐标证明：

\[
(U_\tau M_f-M_fU_\tau)\psi(i)
=
\delta_\tau f(i)\psi(\tau^{-1}i).
\]

### 定理 33.1（交换子因子化）

有精确算子恒等式：

\[
\boxed{
[U_\tau,M_f]
=M_{\delta_\tau f}U_\tau.
}
\]

若 \(I\) 有限，或 \(f\) 有界，则：

\[
\boxed{
\|[U_\tau,M_f]\|_{\mathrm{op}}
=
\|\delta_\tau f\|_\infty.
}
\]

#### 证明

第一式是仓库交换子公式的算子写法。第二式利用 \(U_\tau\) 酉以及乘法算子范数公式：

\[
\|M_gU_\tau\|
=
\|M_g\|
=
\|g\|_\infty.
\]

\(\square\)

因此项目中的

\[
\operatorname{perturbationSeminorm}(\tau,f)
=
\sup_i|f(\tau^{-1}i)-f(i)|
\]

不是任意选取的扰动量，而是读出与更新交换子的算子范数：

\[
\boxed{
L_\tau(f)
:=
\|[U_\tau,M_f]\|
=
\|\delta_\tau f\|_\infty.
}
\]

它是观察者相对于一步更新的“一阶导数”。

### 推论 33.2（零导数、更新不变量与操作中心）

\[
\boxed{
L_\tau(f)=0
\iff
f\circ\tau=f.
}
\]

所以 \(L_\tau\) 的核不是“无意义函数”，而是更新无法改变的观测量代数：

\[
\boxed{
\ker L_\tau
=
\operatorname{Fix}(\tau^*).
}
\]

在单个非空循环窗口上，仓库已经证明该核只有常数；因此该窗口没有非平凡的零代价横向观测量。

---

## 33.2 一般置换的观察者距离是叶内图距离、叶间无穷距离

定义扩展观察者距离：

\[
\boxed{
 d_\tau(x,y)
=
\sup\left\{
|f(x)-f(y)|:
L_\tau(f)\le1
\right\}.
}
\]

在无限集合上，为避免无关的增长病态，可以把候选限制为有界函数；以下叶间结论仍然成立，因为轨道指示函数有界。

### 定理 33.3（不变量分离导致无穷距离）

若存在

\[
f\in\ker L_\tau
\]

满足

\[
f(x)\ne f(y),
\]

则

\[
\boxed{
 d_\tau(x,y)=+\infty.
}
\]

#### 证明

对任意 \(c>0\)，有

\[
L_\tau(cf)=cL_\tau(f)=0\le1,
\]

而

\[
|cf(x)-cf(y)|
=c|f(x)-f(y)|.
\]

令 \(c\to\infty\)。\(\square\)

因此有限距离至少要求两个状态在全部零缺陷观测量上给出相同值。

### 定义 33.4（更新叶）

置换 \(\tau\) 将 \(I\) 分解为轨道：

\[
I=\bigsqcup_{\lambda\in\Lambda}\mathcal O_\lambda.
\]

称每个 \(\mathcal O_\lambda\) 为一个更新叶。

### 定理 33.5（置换观察者距离完全分类）

设 \(I\) 为离散集合，\(\tau\) 为置换。

1. 若 \(x,y\) 位于不同更新叶，则
   \[
   \boxed{
   d_\tau(x,y)=+\infty.
   }
   \]
2. 若 \(x,y\) 位于同一有限循环叶 \(C_m\)，则
   \[
   \boxed{
   d_\tau(x,y)
   =
   d_{C_m}(x,y),
   }
   \]
   右侧是循环图上的最短路距离。
3. 若 \(x,y\) 位于同一自由整数叶，并对候选观测量要求有界，则
   \[
   \boxed{
   d_\tau(x,y)=|n_x-n_y|,
   }
   \]
   其中 \(n_x,n_y\in\mathbb Z\) 是相对于任一叶原点的整数坐标。

#### 证明

不同叶时，取某一叶的指示函数。它沿 \(\tau\) 不变，且分离 \(x,y\)，应用定理 33.3。

同一有限循环中，\(L_\tau(f)\le1\) 表示每条相邻边上的函数差至多一。沿最短路求和给出

\[
|f(x)-f(y)|
\le d_{C_m}(x,y).
\]

取截断距离函数

\[
f_z=d_{C_m}(x,z)
\]

即可达到上界。自由整数叶使用仓库已经形式化的 clipped distance observable；上界由逐步三角不等式，下界由截断距离函数达到。\(\square\)

因此观察者空间不是普通连通度量空间，而是扩展度量叶层：

\[
\boxed{
\text{叶内距离有限并由更新步数决定；叶间距离由不变量放大为无穷。}
}
\]

这把仓库中两个看似相反的结果统一起来：

- `WindowObserverDistance` 与 `OrbitConnesDistance` 在一个更新叶内恢复有限路径距离；
- `VisiblePhaseInfinity` 在不同可见相位上得到 \(\top\)，因为隐藏平移保持可见相位，故可见相位函数属于 \(\ker L_\tau\)，并能分离两点。

### 推论 33.6（有限距离分量由不变量代数标记）

令状态限制映射为

\[
\operatorname{res}_{\ker L_\tau}:
I\to
\operatorname{Spec}(\ker L_\tau),
\qquad
x\mapsto(f\mapsto f(x)).
\]

则每个有限距离分量都包含在该限制映射的一个纤维中。

所以：

\[
\boxed{
\text{零缺陷观测量不是距离中的“零方向”；它们是扩展几何的扇区标签。}
}
\]

若不先固定这些标签或商掉不变量代数，Connes 型距离可能自然取无穷值。

---

## 33.3 可见圆与隐藏素数地址给出混合时间，而不是单一连续时间

项目中的 universal solenoid 带有投影：

\[
\pi:\Sigma_\infty\to\mathbb T,
\]

隐藏核为：

\[
K_\infty=\ker\pi
\cong
\prod_p\mathbb Z_p.
\]

对一条连续路径 \(x:\mathbb R\to\Sigma_\infty\)，仓库构造规范化数据：

\[
 x(t)=\operatorname{realFlow}(a(t))+k,
\]

其中 \(a:\mathbb R\to\mathbb R\) 连续，而

\[
k\in K_\infty
\]

在整条连续路径上保持常数。

同时，仓库证明任意连续加法实流

\[
\mathbb R\to K_\infty
\]

都是零流；但存在显式非零整数参数跳变

\[
\mathbb Z\to K_\infty,
\]

且该跳变没有连续实参数扩张。

### 定理 33.7（连续段的隐藏地址守恒）

在规范化 streamline 分解中，若 \(x(t)\) 连续，则其隐藏地址

\[
k(x)
\]

在每个连通时间段上恒定。

因此若两个时刻具有不同隐藏地址：

\[
k(t_0)\ne k(t_1),
\]

则不存在一条在同一规范化可见提升下连接二者的连续隐藏流。

### 定义 33.8（混合观察时间）

一个允许隐藏事件的观察历史可写为分段数据：

\[
 x(t)
=
\operatorname{realFlow}(a_j(t))+k_j,
\qquad
 t\in[t_j,t_{j+1}),
\]

以及跳变收据：

\[
\delta_j=k_{j+1}-k_j.
\]

定义累计隐藏账：

\[
\Lambda(t)
=
\sum_{t_j\le t}\delta_j.
\]

于是完整历史参数不是单个实数，而是：

\[
\boxed{
\Theta(t)
=(t,\Lambda(t)).
}
\]

其中：

- \(t\) 排序可见连续演化；
- \(\Lambda(t)\) 记录不能由连续隐藏流吸收的离散地址变化。

这是一种数学上的 hybrid time／event time 模型，不是关于物理时间本体的无条件断言。

### 推论 33.9（隐藏变化必须留下接缝）

若隐藏地址发生非零变化，而整体路径仍被宣称为连续，则至少一项必须改变：

1. 可见提升的规范；
2. 路径所属的 streamline 扇区；
3. 观察接口；
4. 连续性声明；
5. 记录中所采用的隐藏坐标等价。

所以隐藏事件不能在固定全部接口的同时被“平滑掉”。这给追加式账本一个几何理由：

\[
\boxed{
\text{离散事件收据记录的是连续图册之间无法无痕拼接的接缝。}
}
\]

---

## 33.4 概率是记录分支权重；未读测量是条件分支的重组

设 \((P_k)_{k\in K}\) 是有限完备正交投影族：

\[
P_k=P_k^*=P_k^2,
\qquad
P_kP_l=0\ (k\ne l),
\qquad
\sum_kP_k=I.
\]

对状态 \(\rho\)，定义记录权重：

\[
\boxed{
p_k=\operatorname{Tr}(\rho P_k).
}
\]

当 \(p_k>0\) 时，条件状态为：

\[
\boxed{
\rho_k
=
\frac{P_k\rho P_k}{p_k}.
}
\]

未读测量状态为：

\[
\boxed{
\mathcal P(\rho)
=
\sum_kP_k\rho P_k.
}
\]

仓库已经形式化：

\[
\boxed{
\mathcal P(\rho)
=
\sum_kp_k\rho_k,
}
\]

包括零权重分支的严格处理。

### 定理 33.10（记录经典性固定点）

\[
\boxed{
\mathcal P(\rho)=\rho
\iff
P_k\rho P_l=0
\quad(k\ne l).
}
\]

所以相对于该记录接口，“经典态”恰是未读记录投影的固定点。

### 推论 33.11（Born 权重的秩一约化）

若

\[
P_k=|\phi_k\rangle\langle\phi_k|,
\qquad
\rho=|\psi\rangle\langle\psi|,
\]

则：

\[
\boxed{
p_k
=|\langle\phi_k,\psi\rangle|^2.
}
\]

因此 Born 概率在本框架中的类型是：

\[
\boxed{
\text{整体态与记录分支投影的配对权重，而不是投影或商本身。}
}
\]

未读状态则是丢弃分支标签以后保留的条件状态混合。

---

## 33.5 多记录重叠产生一个可加“记录作用”

考虑同一系统地址 \(i,j\) 被有限多个环境记录复制。第 \(r\) 个记录的 Gram 重叠记为：

\[
g_r(i,j)
=
\langle E_j^{(r)},E_i^{(r)}\rangle.
\]

项目已经形式化，多记录通道逐元满足：

\[
\boxed{
\rho_{ij}^{(N)}
=
\Gamma_N(i,j)\rho_{ij}^{(0)},
\qquad
\Gamma_N(i,j)
=
\prod_{r=1}^{N}g_r(i,j).
}
\]

若所有环境记录向量归一化，则 Cauchy–Schwarz 给出：

\[
|g_r(i,j)|\le1.
\]

### 定义 33.12（记录作用／相干债务）

定义扩展非负量：

\[
\boxed{
\mathfrak A_N(i,j)
=
-\log|\Gamma_N(i,j)|
\in[0,+\infty],
}
\]

并约定 \(\Gamma_N=0\) 时：

\[
\mathfrak A_N=+\infty.
\]

若每个重叠非零，则：

\[
\boxed{
\mathfrak A_N(i,j)
=
\sum_{r=1}^{N}
\bigl(-\log|g_r(i,j)|\bigr).
}
\]

### 定理 33.13（记录作用控制相干生存）

\[
\boxed{
|\rho_{ij}^{(N)}|
=
e^{-\mathfrak A_N(i,j)}
|\rho_{ij}^{(0)}|.
}
\]

若记录向量归一化，则 \(\mathfrak A_N\) 随 \(N\) 单调不减。

若存在极限：

\[
\lambda_{ij}
=
\lim_{N\to\infty}
\frac{\mathfrak A_N(i,j)}{N},
\]

则：

\[
\boxed{
\lim_{N\to\infty}
-\frac1N
\log
\frac{|\rho_{ij}^{(N)}|}{|\rho_{ij}^{(0)}|}
=
\lambda_{ij}.
}
\]

因此 \(\lambda_{ij}\) 是该相干坐标的记录擦除率。

### 特例 33.14（同质记录）

若

\[
|g_r(i,j)|=c
\quad(0<c<1)
\]

对全部 \(r\) 成立，则：

\[
\boxed{
|\rho_{ij}^{(N)}|
=c^N|\rho_{ij}^{(0)}|,
\qquad
\mathfrak A_N=N(-\log c).
}
\]

如果某一份记录满足

\[
g_r(i,j)=0,
\]

则：

\[
\boxed{
\rho_{ij}^{(N)}=0
\quad
\text{对所有后续只由同类 reduced record channel 组成的演化成立}.
}
\]

这与仓库 `multi_copy_erasure_quantifier` 完全一致：一个零重叠记录足以在约化系统中擦除该非零输入项。

### 严格解释

\(\mathfrak A_N\) 是记录 Gram 因子的可加对数，不自动等同于 Shannon 熵、von Neumann 熵或热力学作用量。它的价值在于把：

\[
\text{乘法相干衰减}
\]

改写成：

\[
\boxed{
\text{追加式记录债务的加法累计}.
}
\]

这为“账本长度可能成为内部时间”提供一个精确候选，但不把它冒充为唯一物理时间。

---

## 33.6 可逆性门槛：恢复需要全部相关记录，而不只是系统本身

仓库定义对记录振幅取共轭的反向记录。其重叠满足：

\[
g_r^{\mathrm{rev}}(i,j)
=
\overline{g_r(i,j)}.
\]

对原记录通道后再施加所有反向记录，指定矩阵元获得因子：

\[
\prod_r
\overline{g_r(i,j)}g_r(i,j)
=
\prod_r|g_r(i,j)|^2.
\]

### 定理 33.15（相位记录的联合恢复）

若对全部记录：

\[
|g_r(i,j)|=1,
\]

则施加全部反向记录后：

\[
\boxed{
\rho_{ij}^{\mathrm{restored}}
=
\rho_{ij}^{(0)}.
}
\]

若存在某个记录满足：

\[
|g_r(i,j)|<1,
\]

则仅通过该共轭记录通道不能精确恢复，因为残余因子为：

\[
|g_r(i,j)|^2<1.
\]

若有一个非平凡记录副本未被反转，并且其重叠不等于一，则仓库已经形式化该副本阻止精确恢复。

### 推论 33.16（约化不可逆性是访问缺陷）

在整体系统—环境层面，记录相互作用可以来自可逆酉耦合；系统层面的退相干来自：

\[
\boxed{
\text{整体可逆相关生成}
+
\text{环境记录不可访问／被偏迹}.
}
\]

精确恢复要求控制所有携带相关相位的记录自由度。只对系统约化态作用，一般无法反推出已经被环境关联编码的相位。

因此：

\[
\boxed{
\text{“信息消失”应先审计为“信息是否转移到观察者余空间或记录账本”。}
}
\]

但若环境记录已经被真正丢弃，或被新的不可控自由度继续放大，操作性恢复仍可能不可行；全局可逆表示不等于局部工程可逆。

---

## 33.7 记录作用给出一条与熵相容、但不等同的事件时间

在归一化记录假设下：

\[
\mathfrak A_{N+1}(i,j)
\ge
\mathfrak A_N(i,j).
\]

所以对每个相干坐标都可定义单调事件时钟：

\[
\boxed{
\tau_{ij}^{\mathrm{rec}}(N)
=
\mathfrak A_N(i,j).
}
\]

它满足：

1. 没有区分记录时 \(|g_r|=1\)，时钟不走；
2. 部分区分记录时 \(0<|g_r|<1\)，时钟增加有限量；
3. 正交记录时 \(g_r=0\)，时钟跳到 \(+\infty\)，该约化相干被完全擦除。

对于同一投影上下文的 pinching：

\[
S(\mathcal P\rho)-S(\rho)
=
D(\rho\|\mathcal P\rho)
\ge0.
\]

因此每次生成并丢弃可区分记录时，状态熵增可由相对熵相干测量；与此同时，\(\mathfrak A_N\) 测量指定矩阵元的对数生存债务。

二者关系是：

\[
\boxed{
\begin{aligned}
\mathfrak A_N(i,j)
&=\text{坐标级、乘法级记录债务},\\
S(\mathcal P\rho)-S(\rho)
&=\text{全状态、谱级信息删除量}.
\end{aligned}
}
\]

它们可以在具体通道中互相界定，但不能直接互换定义。

### 定义 33.17（双时间观察历史）

结合第 33.3 节，可把观察历史赋予两个独立的时间坐标：

\[
\boxed{
\mathsf T_O
=
\left(
 t_{\mathrm{vis}},
 \mathfrak A_{\mathrm{rec}}
\right).
}
\]

其中：

- \(t_{\mathrm{vis}}\) 是连续可见动力学参数；
- \(\mathfrak A_{\mathrm{rec}}\) 是记录生成造成的不可逆可访问性债务。

一个系统可以在 \(t_{\mathrm{vis}}\) 上持续酉演化而 \(\mathfrak A_{\mathrm{rec}}=0\)；也可以在极短可见时间内通过一次正交记录使某个 \(\mathfrak A_{ij}\) 跳到无穷。因此两种时间不能预先等同。

---

## 33.8 知识是读出因子化；遗忘是知识代数的严格缩小

设世界集合为 \(X\)，读出为：

\[
q:X\to Y.
\]

定义标量知识代数：

\[
\boxed{
\mathcal K(q)
=
\{f:X\to\mathbb C:
\exists g:Y\to\mathbb C,
 f=g\circ q\n\}.
}
\]

这正是所有在读出纤维上常值的事件值函数。

项目 `TwoTimeKnowledge` 中：

\[
\operatorname{Knows}(q,v_e)
\iff
v_e\in\mathcal K(q).
\]

### 定理 33.18（读出粗化导致知识代数反向缩小）

若后期读出 \(q_1\) 比早期读出 \(q_0\) 更粗，即存在：

\[
r:Y_0\to Y_1
\]

满足：

\[
q_1=r\circ q_0,
\]

则：

\[
\boxed{
\mathcal K(q_1)
\subseteq
\mathcal K(q_0).
}
\]

#### 证明

若 \(f=g\circ q_1\)，则：

\[
f=(g\circ r)\circ q_0.
\]

\(\square\)

因此语义遗忘可以写成：

\[
\boxed{
v_e\in
\mathcal K(q_0)
\setminus
\mathcal K(q_1),
}
\]

同时事件 \(e\) 在完整账本中仍然持续存在。

### 推论 33.19（有限知识容量）

若 \(X,Y\) 有限，并把所有复函数作为可观测量，则：

\[
\boxed{
\dim_{\mathbb C}\mathcal K(q)
=|q(X)|.
}
\]

所以粗化 \(q_1=rq_0\) 的线性知识容量损失为：

\[
\boxed{
\Delta\dim\mathcal K
=
|q_0(X)|-|q_1(X)|.
}
\]

该数量计算的是可独立区分的读出类减少量，不等于自然语言中“忘了多少件事”。

### 定义 33.20（定量遗忘余量）

给定世界分布 \(\mu\)，在 \(L^2(X,\mu)\) 中令

\[
\mathbb E_q
\]

为到 \(\mathcal K(q)\) 的条件期望／正交投影。定义：

\[
\boxed{
\varepsilon_q(f)
=
\|f-\mathbb E_qf\|_{L^2(\mu)}.
}
\]

则：

\[
\boxed{
\varepsilon_q(f)=0
\iff
f\in\mathcal K(q).
}
\]

所以事件从“已知”到“未知”可以从布尔命题推广为连续余量增长。

### 账本与认知必须分离

项目的有限遗忘证书明确保留：

\[
\texttt{forgottenLogged}=\texttt{true}
\]

即使当前认知已经从 `remember` 进入 `forgotten`，甚至后来进入 `recall`。

因此：

\[
\boxed{
\text{当前可访问知识}
\neq
\text{历史记录是否存在}.
}
\]

遗忘是当前读出不能再因子化事件值；追加式账本则保存“该因子化曾经成立或曾经失败”的历史收据。召回需要读出重新精化、重新连接账本，或引入外部记录；它不是粗商内部自动产生的信息。

---

## 33.9 坐标变化不是时间路径：`StateNotPath` 的结构解释

设 \(\mathcal D_Z\) 为计算基中的对角状态集合。纯粹的相位阻尼／经典对角通道满足：

\[
\rho\in\mathcal D_Z
\Longrightarrow
\Phi^n(\rho)\in\mathcal D_Z
\quad
\forall n.
\]

仓库已经形式化：对角输入经任意有限次经典对角通道迭代，非对角元始终为零。

但同一密度矩阵在 Hadamard 坐标中可以出现非零非对角元：

\[
H|0\rangle\langle0|H^*
=
\frac12
\begin{pmatrix}
1&1\\
1&1
\end{pmatrix}.
\]

所以：

\[
\boxed{
\text{一个坐标系中的相干出现}
\not\Rightarrow
\text{存在一条同一经典通道中的时间路径生成该相干}.
}
\]

必须区分：

\[
\boxed{
\begin{aligned}
\text{坐标变换}
&:\rho\mapsto U\rho U^*,\\
\text{物理通道迭代}
&:\rho\mapsto\Phi^n(\rho),\\
\text{观察界面变换}
&:\rho\mapsto\mathbb E_{\mathcal C}(\rho).
\end{aligned}
}
\]

这对“经典世界与量子世界只是坐标系不同”的直觉给出严格修正：

- 相干确实依赖所选对角；
- 但非交换操作结构、可实现通道和时间路径不能由普通坐标重命名消除；
- 改变坐标可以改变哪些元被称为“非对角”，却不把一个受限通道的可达集合自动扩大。

---

## 33.10 三重闭包：预测闭包、操作代数闭包与自描述闭包

项目中至少存在三种不能混用的“完整”。

### 第一种：预测闭包

第 32 节定义：

\[
V_{\mathrm{pred}}
=
\overline{\operatorname{span}}
\{(\Phi^*)^nA:
A\in V_0,
 n\ge0\}.
\]

它回答：

> 为预测全部未来读出，当前观察者还需补充哪些线性坐标？

### 第二种：操作代数闭包

给定可读取观测量和可执行更新，定义最小含幺 \(*\)-代数：

\[
\boxed{
\mathcal A_{\mathrm{op}}
=C^*(M_f,U_\tau:
 f\in\mathcal F_O).
}
\]

在非平凡有限循环窗口中，仓库构造 clock、shift 和全部矩阵单位，并证明：

\[
\boxed{
\mathcal A_{\mathrm{op}}
=M_M(\mathbb C).
}
\]

同时：

\[
\boxed{
\mathcal A_{\mathrm{op}}'
=
\mathbb CI.
}
\]

也就是操作表示不可约。

### 第三种：自描述／经典答案闭包

经典全局答案表要求一个保持代数运算的角色：

\[
\chi:
M_M(\mathbb C)	o\mathbb C.
\]

对于 \(M>1\)，仓库证明：

\[
\boxed{
\operatorname{Hom}_{\mathrm{Alg}}
(M_M(\mathbb C),\mathbb C)
=
\varnothing.
}
\]

并进一步以 CHSH 见证排除同一 preparation-independent 局域确定表。

### 定理 33.21（操作完备不推出经典答案完备）

在任意非平凡有限循环窗口：

\[
\boxed{
\mathcal A_{\mathrm{op}}
=M_M(\mathbb C),
\qquad
\mathcal A_{\mathrm{op}}'
=
\mathbb CI,
\qquad
\operatorname{Char}(\mathcal A_{\mathrm{op}})
=
\varnothing.
}
\]

所以观察者可以生成、组合并层析全部矩阵观测量，却仍不能把它们压成一个保持乘法的全局经典数值表。

这不是矛盾：

\[
\boxed{
\text{知道完整量子态}
\neq
\text{为全部不相容问题预存同时确定的答案}.
}
\]

密度矩阵给出正线性状态：

\[
\omega_\rho(A)=\operatorname{Tr}(\rho A),
\]

但一般不满足：

\[
\omega_\rho(AB)
=
\omega_\rho(A)\omega_\rho(B).
\]

因此状态层析完成、操作代数生成完成与经典角色完成是三种不同层级。

### 推论 33.22（三重闭包非蕴含）

\[
\boxed{
\text{预测完备}
\not\Rightarrow
\text{操作代数完备};
}
\]

常值读出可以预测闭合却操作贫乏。

\[
\boxed{
\text{操作代数完备}
\not\Rightarrow
\text{经典答案完备};
}
\]

非平凡窗口全矩阵代数即为反例。

\[
\boxed{
\text{层析完备}
\not\Rightarrow
\text{同层自描述完备};
}
\]

即使状态由全部概率唯一确定，Cantor–Lawvere 型评价空间仍可能被自己的对角对象逃出。

---

## 33.11 CRT 张量分解揭示局部读出的高阶关联余空间

设有限窗口大小分解为互素因子：

\[
M=mn,
\qquad
\gcd(m,n)=1.
\]

仓库已经形式化地址 CRT 和窗口 clock/shift 的 Kronecker 分解，并进一步对全部素数幂因子给出全矩阵代数等价：

\[
\boxed{
M_M(\mathbb C)
\cong
\bigotimes_{p^r\parallel M}
M_{p^r}(\mathbb C).
}
\]

这给出一个规范的观察者地址张量分解。但张量分解不意味着全局状态由各因子的边缘态唯一确定。

### 定理 33.23（二因子算子 Hilbert 扇区分解）

设：

\[
\mathscr H
=
\mathscr H_A\otimes\mathscr H_B,
\qquad
\dim\mathscr H_A=m,
\quad
\dim\mathscr H_B=n.
\]

在 Hilbert–Schmidt 实内积下：

\[
\boxed{
\operatorname{Herm}_0(\mathscr H)
=
\bigl(
\operatorname{Herm}_0(\mathscr H_A)
\otimes \mathbb RI_B
\bigr)
\oplus
\bigl(
\mathbb RI_A
\otimes\operatorname{Herm}_0(\mathscr H_B)
\bigr)
\oplus
\bigl(
\operatorname{Herm}_0(\mathscr H_A)
\otimes
\operatorname{Herm}_0(\mathscr H_B)
\bigr).
}
\]

三项两两正交，维数分别为：

\[
m^2-1,
\qquad
n^2-1,
\qquad
(m^2-1)(n^2-1).
\]

#### 证明

使用：

\[
\operatorname{Herm}(\mathscr H_A)
=
\mathbb RI_A
\oplus
\operatorname{Herm}_0(\mathscr H_A),
\]

\[
\operatorname{Herm}(\mathscr H_B)
=
\mathbb RI_B
\oplus
\operatorname{Herm}_0(\mathscr H_B),
\]

展开实张量积。全标量项 \(\mathbb R(I_A\otimes I_B)\) 是唯一非无迹项；删除它即得。不同扇区至少在一个因子上由标量与无迹正交，故两两正交。维数乘法给出公式。\(\square\)

### 推论 33.24（局部边缘的关联盲区）

只读取两个局部边缘态，最多读取：

\[
(m^2-1)+(n^2-1)
\]

个无迹方向。未读关联余空间维数为：

\[
\boxed{
D_{\mathrm{corr}}
=(m^2-1)(n^2-1).
}
\]

其在全部无迹方向中的比例为：

\[
\boxed{
 r_{\mathrm{corr}}
=
\frac{(m^2-1)(n^2-1)}{m^2n^2-1}.
}
\]

因此即使每个因子局部层析完备，仍可能遗漏全部跨因子关联。

Bell 纯态与相应经典相关混合具有相同局部边缘而不同全局态，正是该关联余空间的显式见证。

### 定理 33.25（多素数因子的关联深度分解）

设：

\[
\mathscr H
=
\bigotimes_{r=1}^{s}\mathscr H_r,
\qquad
\dim\mathscr H_r=d_r.
\]

对每个非空子集 \(S\subseteq\{1,\ldots,s\}\)，定义关联扇区：

\[
\mathcal C_S
=
\left(
\bigotimes_{r\in S}
\operatorname{Herm}_0(\mathscr H_r)
\right)
\otimes
\left(
\bigotimes_{r\notin S}
\mathbb RI_r
\right).
\]

则：

\[
\boxed{
\operatorname{Herm}_0(\mathscr H)
=
\bigoplus_{\varnothing\ne S\subseteq[s]}
\mathcal C_S,
}
\]

且：

\[
\boxed{
\dim\mathcal C_S
=
\prod_{r\in S}(d_r^2-1).
}
\]

定义 \(|S|\) 为关联阶数。只保留至多 \(k\) 体读出的观察者，其未观察余维数为：

\[
\boxed{
D_{>k}
=
\sum_{|S|>k}
\prod_{r\in S}(d_r^2-1).
}
\]

这给 CRT 素数幂地址塔一个新的量子解释：

\[
\boxed{
\text{素数幂因子给出局部地址；子集 }S\text{ 给出跨地址关联深度。}
}
\]

但这些关联扇区既可以承载经典相关，也可以承载量子纠缠；非零高阶扇区本身不是纠缠充分条件。

---

## 33.12 同一记录指针的互补相关约束

项目 `RecordCorrelationMonogamy` 固定同一个记录指针 \(Z_R\)，定义：

\[
C_Z(\rho)
=
\operatorname{Tr}
\bigl(
\rho(Z_S\otimes Z_R)
\bigr),
\]

\[
C_X(\rho)
=
\operatorname{Tr}
\bigl(
\rho(X_S\otimes Z_R)
\bigr).
\]

仓库证明：

\[
\boxed{
C_Z(\rho)=1
\Longrightarrow
C_X(\rho)=0.
}
\]

其含义不是“所有互补相关不能共存”。Bell 态可以同时具有：

\[
\langle Z\otimes Z\rangle=1,
\qquad
\langle X\otimes X\rangle=1.
\]

真正结论是：

\[
\boxed{
\text{同一个固定 }Z\text{ 记录指针若完美复制系统 }Z\text{ 地址，
则该指针不能同时记录系统 }X\text{ 值。}
}
\]

这与第 31 节的 MUB 坐标塔一致：一个经典记录界面选择了某个对角方向；对该记录本身而言，共轭方向进入余空间。

因此“客观记录形成”可以写成：

\[
\boxed{
\text{某一上下文的相关被冗余增强，
同一指针相对于互补上下文的可读相关被压低。}
}
\]

这仍不是完整的量子 Darwinism 定理，因为项目当前没有无条件证明任意多环境碎片上的冗余互信息平台或客观性阈值。

---

## 33.13 观察者完成必须区分目标完成、状态完成、代数完成与统一完成

设递增可见空间：

\[
V_0\subseteq V_1\subseteq\cdots,
\qquad
R_n=V_n^\perp.
\]

### 目标完成

对固定目标 \(x\)：

\[
\boxed{
\|P_{R_n}x\|\to0.
}
\]

RH 的 Nyman–Beurling 形式属于此类，目标为 \(\chi\)。

### 状态族完成

对某个任务相关集合 \(\mathcal S\)：

\[
\boxed{
\sup_{x\in\mathcal S}
\|P_{R_n}x\|	o0.
}
\]

这比单目标强，但仍可弱于全单位球完成。

### 代数完成

可访问操作闭包等于目标算子代数：

\[
\boxed{
\mathcal A_{\mathrm{op}}
=\mathcal A_{\mathrm{target}}.
}
\]

有限窗口 clock/shift 生成全矩阵代数属于此类。

### 统一完成

要求：

\[
\boxed{
\|I-P_{V_n}\|_{\mathrm{op}}	o0.
}
\]

若所有 \(V_n\) 都是真闭子空间，则：

\[
\|I-P_{V_n}\|_{\mathrm{op}}=1,
\]

统一完成失败。

### 定理 33.26（四种完成的严格层级）

一般只有：

\[
\boxed{
\text{统一完成}
\Longrightarrow
\text{状态族完成}
\Longrightarrow
\text{目标完成}.
}
\]

逆向均不成立。

代数完成与前三者没有无条件蕴含关系：一个代数可以由少量生成元生成，但指定状态的有限截断误差仍需独立控制；反之，单个目标可以被很好逼近，而操作代数仍非常小。

因此项目中的所有“完成”必须携带对象类型：

\[
\boxed{
\operatorname{Complete}
(
\text{target/state family/algebra/uniform ball}
).
}
\]

不能只写一个无参数的“观察者已完成”。

---

## 33.14 观察者逃逸率必须是向量而不是单一数字

结合前述各节，至少存在六种不同逃逸量。

### 1. 读出余质量

\[
r_m^{\mathrm{state}}(\rho)
=
\|P_{R_m}X_\rho\|_2^2.
\]

### 2. 未来问题余质量

\[
r_{m,k}^{\mathrm{effect}}(A)
=
\|P_{R_m}(\Phi^*)^kA\|_2^2.
\]

### 3. 记录相干生存率

\[
s_N^{\mathrm{rec}}(i,j)
=
|\Gamma_N(i,j)|
=
e^{-\mathfrak A_N(i,j)}.
\]

### 4. 对角逃逸率

由有限评价表的 escaped listing 数量、概率或距离剖面给出。

### 5. 知识损失率

\[
\Delta\dim\mathcal K

equals
\dim\mathcal K(q_0)-
\dim\mathcal K(q_1),
\]

或事件余量 \(\varepsilon_q(f)\)。

### 6. 关联阶余量

\[
D_{>k}
=
\sum_{|S|>k}
\prod_{r\in S}(d_r^2-1).
\]

因此定义观察者逃逸剖面：

\[
\boxed{
\mathbf R_O
=
\left(
 r^{\mathrm{state}},
 r^{\mathrm{effect}},
 s^{\mathrm{rec}},
 r^{\mathrm{diag}},
 r^{\mathrm{know}},
 r^{\mathrm{corr}}
\right).
}
\]

这些量可以通过特定不等式耦合，但不应在定义层被压成一个“总熵”。

例如第 32 节已经证明未来概率误差由双余量乘积控制：

\[
|\Delta p|
\le
\sqrt{r^{\mathrm{state}}}
\sqrt{r^{\mathrm{effect}}}.
\]

第 33.5 节又给出：

\[
s_N^{\mathrm{rec}}
=e^{-\mathfrak A_N}.
\]

而第 31 节在重复去相干中给出：

\[
\Delta S
=D(\rho\|\mathbb E\rho).
\]

正确研究方向是寻找这些不同分量间的 sharp inequalities，而不是预先宣称它们同一。

---

## 33.15 从项目全部独特视角得到的观察者闭合图

现在可以把项目中观察者的全部主要结构排列成一个闭合图：

\[
\boxed{
\begin{array}{c}
\text{整体状态／路径／账本}\[1mm]
\downarrow\ q_O\\
\text{当前读出商与读出纤维}\[1mm]
\downarrow\ \Phi^*\\
\text{未来问题的 Heisenberg 预测闭包}\[1mm]
\downarrow\ C^*\text{-closure}\\
\text{读出—更新操作代数}\[1mm]
\downarrow\ \text{record dilation}\\
\text{条件分支、环境相关与记录作用}\[1mm]
\downarrow\ \text{discard record}\\
\text{概率、退相干、熵与知识粗化}\[1mm]
\downarrow\ \Delta\\
\text{自描述闭合测试与对角逃逸}\[1mm]
\downarrow\ \varprojlim\\
\text{相对界面族的可实现完成}
\end{array}
}
\]

该图中每一条箭头都需要独立审计：

1. **读出是否忠实：** \(\ker q_O\) 多大；
2. **动力学是否下降：** 当前商是否为同余；
3. **预测是否闭合：** \(V_m\) 是否稳定；
4. **操作是否完备：** 生成代数是否达到目标；
5. **记录是否可访问：** 环境相关是否保留；
6. **概率是否规范：** 状态、effect 与条件分支是否正且归一；
7. **知识是否保持：** 事件值是否继续因子化读出；
8. **自描述是否封闭：** 是否存在对角逃逸；
9. **有限层是否可完成：** 相容族是否满足正性、能量和可实现性；
10. **跨上下文是否可拼接：** 是否存在全局经典答案表。

因此项目中“观察者”的最强定义可以写成：

\[
\boxed{
\text{观察者}
=
\text{一个定义相对同一性的读出商，
以及使这种同一性在时间、操作、记录和自指下尽可能闭合的最小机制。}
}
\]

---

## 33.16 五个候选新定理族

下面五个定理族最能承载本节相对于成熟理论的新增组合，而不是只做解释性重命名。

### A. 观察者扩展距离叶层分类

形式化一般置换的结论：

\[
\boxed{
 d_\tau(x,y)
=
\begin{cases}
\text{轨道图距离},&x,y\text{ 同叶},\\
+\infty,&x,y\text{ 异叶}.
\end{cases}
}
\]

这将当前分散的 finite cycle、integer orbit 与 visible-phase infinity 合并为一个定理。

### B. 记录作用与擦除率

形式化：

\[
\boxed{
\mathfrak A_N
=-\log\left|\prod_{r\le N}g_r\right|
=
\sum_{r\le N}-\log|g_r|,
}
\]

以及相干指数率、零重叠吸收和全记录反演门槛。

### C. 知识代数—遗忘余量

形式化：

\[
\boxed{
q_1=rq_0
\Longrightarrow
\mathcal K(q_1)
\subseteq
\mathcal K(q_0),
}
\]

并把 `Forgot` 识别为一个持久事件值从早期知识代数退出晚期知识代数。

### D. CRT 关联深度塔

在 prime-power tensor factorization 上形式化：

\[
\boxed{
\operatorname{Herm}_0
=
\bigoplus_{\varnothing\ne S}
\mathcal C_S,
}
\]

及：

\[
\boxed{
D_{>k}
=
\sum_{|S|>k}
\prod_{r\in S}(d_r^2-1).
}
\]

这会把“素数地址因子”与“观察者遗漏的关联阶数”连接起来。

### E. 三重闭包分离证书

以有限窗口为单一模型证明：

\[
\boxed{
\text{操作代数完成}
+
\text{标量交换子}
+
\text{无经典角色}.
}
\]

并与第 32 节预测闭包和本文对角逃逸明确分型。

这些定理即使单项有成熟邻近结果，其在项目统一观察者类型中的组合与互相非蕴含，仍可能形成可发表的结构性贡献。

---

## 33.17 建议 Lean 形式化顺序

1. `ObserverCommutatorNorm`
   \[
   \|[U_\tau,M_f]\|
   =
   \|f\circ\tau^{-1}-f\|_\infty.
   \]

2. `ObserverDistanceInfiniteOfInvariantSeparation`
   \[
   f\in\ker L_\tau,
   \ f(x)\ne f(y)
   \Rightarrow
   d_\tau(x,y)=\top.
   \]

3. `PermutationObserverDistanceClassification`
   同轨道为图距离、异轨道为 \(\top\)。

4. `RecordActionAdditive`
   \[
   -\log|\prod g_r|
   =
   \sum -\log|g_r|.
   \]

5. `RecordActionCoherenceSurvival`
   \[
   |\rho_{ij}^{(N)}|
   =
e^{-\mathfrak A_N}|\rho_{ij}^{(0)}|.
   \]

6. `UnimodularRecordReversalIff`
   对共轭反向记录，精确恢复的模长门槛。

7. `KnowledgeAlgebraAntitone`
   \[
   q_1=rq_0
   \Rightarrow
   \mathcal K(q_1)\subseteq\mathcal K(q_0).
   \]

8. `ForgotAsKnowledgeAlgebraExit`
   把 `TwoTimeKnowledge.Forgot` 与事件值的代数成员变化连接。

9. `TensorHermitianCorrelationDecomposition`
   二因子及有限多因子的正交扇区分解。

10. `PrimePowerCorrelationDepth`
    将 `PrimePowerTensorTower` 的因子索引用于关联阶余维数。

11. `OperationalCompleteNoCharacter`
    汇总 `WindowGeneration`、`window_commutant_eq_scalars` 与 `window_algebra_has_no_character`。

12. `CompletionKindNonImplications`
    为目标、状态族、代数和统一完成给出有限显式反例。

所有新声明应引用现有 Lean GID，而不是从理论卷自然语言复制为第二真源。

---

## 33.18 最终结论

项目中的独特观察者视角可以压缩为以下十二句：

\[
\boxed{
\text{读出定义商，核与余空间定义当前不可见差异。}
}
\]

\[
\boxed{
\text{更新交换子是观察者的一阶导数。}
}
\]

\[
\boxed{
\text{交换子半范数生成叶内有限、叶间无穷的扩展几何。}
}
\]

\[
\boxed{
\text{连续可见流保持隐藏素数地址；隐藏变化需要离散接缝。}
}
\]

\[
\boxed{
\text{概率是状态对记录分支的权重。}
}
\]

\[
\boxed{
\text{未读测量是条件分支在忘记标签后的重组。}
}
\]

\[
\boxed{
\text{多记录将相干乘法衰减转化为可加记录作用。}
}
\]

\[
\boxed{
\text{局部不可逆性来自记录不可访问；恢复要求控制全部相关记录。}
}
\]

\[
\boxed{
\text{知识是事件值对当前读出的因子化；遗忘是该因子化失效。}
}
\]

\[
\boxed{
\text{CRT 给出素数幂局部地址，但高阶关联仍居张量余空间。}
}
\]

\[
\boxed{
\text{操作代数可以完整，而全局经典答案表仍不存在。}
}
\]

\[
\boxed{
\text{预测、操作、记录、自描述与无限完成是不同闭包，不能由一个“完整度”代替。}
}
\]

最凝练的统一式是：

\[
\boxed{
\text{观察者不是世界之外的观看点；
它是世界内部形成的读出商、更新代数、记录账本与闭包规则。}
}
\]

时间描述该结构如何更新；概率描述状态在记录分支上的权重；熵描述某类非单射记录接口删除的可区分性；对角化检验观察者能否以同一类型完整描述自身；无穷则标记任何有限闭包仍可能留下的余核。

因此，这一研究方向真正可能给数学与物理带来的新解释，不是宣称所有概念本来相同，而是：

\[
\boxed{
\text{把它们分别识别为同一个观察者闭合问题中的不同对象、不同缺陷和不同极限。}
}
\]

### 33.19 严格非主张

1. 本节没有从 hidden-flow rigidity 推出自然界时间必为离散—连续二元本体。
2. 本节没有把记录作用 \(\mathfrak A_N\) 等同于 thermodynamic action 或任意标准熵。
3. 本节没有证明所有环境记录都归一化；涉及 \(|g_r|\le1\) 的结论明确以归一化为前提。
4. 本节没有声称全局酉可逆性保证局部实验可逆性。
5. 本节没有把高阶关联扇区非零等同于纠缠。
6. 本节没有把相同局部边缘解释为 Bell 非局域性的充分条件。
7. 本节没有把窗口全矩阵代数生成冒充为量子力学无前件的出身证明。
8. 本节没有把无代数角色直接等同于所有版本的 Kochen–Specker 或 Bell 定理。
9. 本节没有把 observer distance 的 \(+\infty\) 解释为物理空间距离无穷大。
10. 本节没有把知识代数的维数等同于语义知识总量。
11. 本节没有把理论卷纸面推导注册为 Lean 已闭合事实。
12. 本节不修改第 28–32 节任何旧文字；所有收紧均以追加形式记账。

---

# 34. 追加：经济观察者、价格商余、无套利闭包与流动性逃逸
## Economic Observers, Price Quotients, Arbitrage-Free Closure, and Liquidity Escape

### 34.0 研究位置、经济学边界与核心命题

第 28–33 节已经把观察者写成：

\[
\boxed{
\text{当前读出商}
+
\text{使该商在动力学、记录、自指与完成下稳定的最小闭包}.
}
\]

经济系统提供一个尤其重要的检验场，因为经济观察界面不是外生、被动且固定的。价格、评级、抵押率、会计值、风险模型和政策指标一旦被公开，参与者会依据这些读出重新行动；行动又改变价格、资产负债表与未来读出。因此经济观察者一般具有双重角色：

\[
\boxed{
\text{价格是世界状态的读出}
}
\]

同时也是

\[
\boxed{
\text{改变交易、融资和生产决策的控制信号}.
}
\]

本节把项目已有的商余、Hilbert 投影、预测闭包、对角逃逸、记录账本、熵和混合时间结构接入经济学，重点研究：

1. 价格为何是相对于计价单位、交易集合和市场深度的坐标，而不是总价值本体；
2. 无套利为何等价于价格对“相同终端收益”这一商关系的良定义下降；
3. 不完备市场为何可写成 marketed payoff 子空间的正交余风险；
4. 市值为何可以在现金总量几乎不变时大幅上升；
5. 固定名义债务为何把连续资产价格变成离散违约界面；
6. 市场流动性、融资流动性和支付网络为何形成反馈闭包；
7. 信息有效市场、政策评价和公开预测为何具有内生观察与自指缺陷；
8. 为什么“市场效率”“市场完整”“流动性充足”“信息充分”不能压成同一个标量。

本节不主张经济系统是量子系统，不把价格等同于概率，不把市场市值等同于可兑现现金，不把熵指标自动解释为福利，不把无套利等同于均衡存在，也不把下述简化流动性反馈模型冒充为现实金融系统的完整结构模型。所有新增结论均为纸面推导；未经 Lean proof term、依赖闭包、admission 与冻结收据不得标记为 `Closed`。

---

## 34.1 价格坐标的射影性：计价单位是截面，不是绝对原点

设有 \(L\) 种商品，价格向量为

\[
p=(p_1,\ldots,p_L)\in\mathbb R_{++}^{L},
\]

主体的名义财富为 \(w>0\)。预算集为

\[
B(p,w)
=
\{x\in\mathbb R_+^L:p\cdot x\le w\}.
\]

### 定理 34.1（计价尺度规范不变性）

对任意 \(\lambda>0\)：

\[
\boxed{
B(\lambda p,\lambda w)=B(p,w).
}
\]

#### 证明

\[
(\lambda p)\cdot x\le\lambda w
\iff
p\cdot x\le w.
\]

\(\square\)

因此，在没有固定名义合同介入时，经济选择首先依赖的不是绝对价格向量 \(p\)，而是正射影类：

\[
\boxed{
[p]
=
\{\lambda p:\lambda>0\}.
}
\]

选择某种商品、货币或价格指数作为 numeraire，相当于在每条射影轨道上选择一个代表元。例如固定

\[
p_1=1
\]

或

\[
p\cdot n=1
\]

都是选择截面，而不是发现一个绝对价格原点。

这与本文有限群余坐标和局部截面的结构相同：

\[
\boxed{
\text{相对价格}
=
\text{射影商坐标};
\qquad
\text{计价单位}
=
\text{该商上的命名截面}.
}
\]

不同货币图表之间的汇率，是不同截面之间的转换函数。若转换函数满足循环一致性，便不存在纯粹由计价循环产生的套利；若转换积偏离一，则出现三角套利。

### 推论 34.2（固定名义债务破坏价格尺度规范）

设固定名义债务为 \(D>0\)，并以第 \(j\) 种商品衡量其实物负担：

\[
d_j(p)=\frac{D}{p_j}.
\]

若只缩放价格而不同比例缩放合同债务：

\[
p\mapsto\lambda p,
\qquad
D\mapsto D,
\]

则

\[
\boxed{
d_j(\lambda p)=\frac1\lambda d_j(p).
}
\]

所以固定名义债务不是射影不变量；它选择并固定了一个结算尺度。

这给出一个重要经济解释：

\[
\boxed{
\text{真实配置可以对统一名义缩放不敏感，
固定名义合同却把该规范自由变成实际资产负债表效应}.
}
\]

通货紧缩使固定债务的实物负担上升，通货膨胀使其下降；这不是因为 Hilbert 空间或市场“创造了价值”，而是名义合同成为一个破坏计价规范的边界条件。

---

## 34.2 收益商与无套利：价格必须下降到终端收益空间

考虑有限状态的一期市场。终端状态集合为

\[
\Omega=\{1,\ldots,n\}.
\]

有 \(m\) 个可交易资产。组合向量为

\[
z\in\mathbb R^m,
\]

终端收益映射为

\[
A:\mathbb R^m\to\mathbb R^n,
\]

其中 \(Az\) 是组合 \(z\) 在各终端状态中的支付。当前资产价格向量为

\[
c\in\mathbb R^m,
\]

组合成本为

\[
c\cdot z.
\]

定义组合等价关系：

\[
z\sim_A z'
\iff
Az=Az'.
\]

即两个组合若在每个终端状态支付完全相同，则属于同一收益商类。

### 定理 34.3（价格下降—同一收益同一价格等价）

下列命题等价：

1. 对所有 \(z,z'\)：
   \[
   Az=Az'
   \Longrightarrow
   c\cdot z=c\cdot z';
   \]
2. 
   \[
   \ker A\subseteq\ker c^\top;
   \]
3. 存在唯一线性泛函
   \[
   \ell:\operatorname{im}A\to\mathbb R
   \]
   满足
   \[
   \boxed{
   c\cdot z=\ell(Az)
   \qquad
   \forall z\in\mathbb R^m.
   }
   \]

#### 证明

\(1\Rightarrow2\)：若 \(Az=0=A0\)，由 1 得 \(c\cdot z=0\)。

\(2\Rightarrow3\)：定义

\[
\ell(Az)=c\cdot z.
\]

若 \(Az=Az'\)，则 \(z-z'\in\ker A\subseteq\ker c^\top\)，故定义与代表元无关。线性显然。唯一性来自 \(\operatorname{im}A\) 中每个元素都有形如 \(Az\) 的表示。

\(3\Rightarrow1\)：若 \(Az=Az'\)，则

\[
c\cdot z=\ell(Az)=\ell(Az')=c\cdot z'.
\]

\(\square\)

所以无摩擦市场中的 law of one price 可以写成：

\[
\boxed{
\text{价格不是定义在组合名字上，
而必须良定义地因子化到终端收益商}.
}
\]

若该条件失败，则存在

\[
h\in\ker A
\]

满足

\[
c\cdot h\ne0.
\]

改变符号后可令

\[
c\cdot h<0,
\qquad
Ah=0.
\]

主体当前收到正现金，未来没有任何净支付义务，构成零收益套利。因此：

\[
\boxed{
\text{价格不能下降到收益商}
\Longrightarrow
\text{存在纯命名差异套利}.
}
\]

这正是本文自然性语言在金融中的精确实例：

\[
\boxed{
q_{\mathrm{payoff}}(z)=Az,
\qquad
\text{价格必须在 }q_{\mathrm{payoff}}\text{ 的纤维上常值}.
}
\]

---

## 34.3 正状态价格与定价余纤维

在标准有限一期无套利假设下，分离定理给出严格正状态价格向量

\[
\pi\in\mathbb R_{++}^{n}
\]

满足

\[
\boxed{
A^\top\pi=c.
}
\]

于是 marketed payoff \(X=Az\) 的价格为

\[
\ell(X)=\pi\cdot X.
\]

若市场不完备，状态价格一般不唯一。任取一个解 \(\pi_0\)，全部线性解构成仿射空间：

\[
\boxed{
\{\pi:A^\top\pi=c\}
=
\pi_0+\ker A^\top.
}
\]

真正允许的无套利状态价格集合是其与正锥的交：

\[
\boxed{
\mathcal P_c
=
(\pi_0+\ker A^\top)
\cap
\mathbb R_{++}^{n}.
}
\]

因此市场价格观察者只读取状态价格向量在

\[
(\ker A^\top)^\perp
=
\operatorname{im}A
\]

上的作用，而把

\[
\ker A^\top
\]

方向商掉。

这产生一个经济商余结构：

\[
\boxed{
\text{已交易资产价格}
=
\text{状态价格泛函在 marketed payoff 子空间上的限制};
}
\]

\[
\boxed{
\text{定价余量}
=
\text{所有不改变已交易资产价格的状态价格方向}.
}
\]

若存在无风险 numeraire，价格为 \(B_0>0\)，终端支付恒为一，则

\[
\sum_i\pi_i=B_0.
\]

归一化得到风险中性概率：

\[
\boxed{
\mathbb Q_i=\frac{\pi_i}{B_0}.
}
\]

但 \(\mathbb Q\) 不是物理频率分布的同义词。它是把正定价泛函相对于 numeraire 归一化后的坐标，编码价格、稀缺性、风险承受与约束。若市场不完备，则风险中性概率本身也形成一个余纤维；选择最小熵测度或其他准则，是在该纤维中再选择一个截面，而不是从价格中发现唯一客观概率。

---

## 34.4 不完备市场是 Hilbert 余风险

在终端状态上固定一个满支撑物理概率 \(\mu\)，取 Hilbert 空间

\[
\mathscr H_\mu=L^2(\Omega,\mu).
\]

令 marketed payoff 子空间为

\[
\mathcal M=\operatorname{im}A\subseteq\mathscr H_\mu.
\]

对任意目标索赔或负债

\[
X\in\mathscr H_\mu,
\]

有唯一正交分解：

\[
\boxed{
X=P_{\mathcal M}X+R_{\mathcal M}X,
\qquad
R_{\mathcal M}X\in\mathcal M^\perp.
}
\]

### 定理 34.4（最小均方套期保值）

对全部 marketed payoff \(Y\in\mathcal M\)：

\[
\boxed{
\|X-Y\|_2^2
=
\|R_{\mathcal M}X\|_2^2
+
\|P_{\mathcal M}X-Y\|_2^2.
}
\]

因此唯一最优均方套期保值收益为

\[
\boxed{
Y^*=P_{\mathcal M}X,
}
\]

最小不可对冲风险为

\[
\boxed{
\inf_{Y\in\mathcal M}\|X-Y\|_2^2
=
\|R_{\mathcal M}X\|_2^2.
}
\]

#### 证明

\[
X-Y
=
R_{\mathcal M}X+
(P_{\mathcal M}X-Y),
\]

两项正交，应用 Pythagoras。 \(\square\)

所以市场不完备不是一句抽象的“资产不够多”，而是：

\[
\boxed{
\text{目标支付中存在 marketed payoff 子空间无法承载的正交余分量}.
}
\]

### 目标完成与全市场完成

全市场完成要求：

\[
\boxed{
\mathcal M=\mathscr H_\mu.
}
\]

但某个机构只需其特定负债 \(X\) 可复制：

\[
\boxed{
R_{\mathcal M}X=0.
}
\]

因此：

\[
\boxed{
\text{目标负债完成}
\not\Rightarrow
\text{全市场完成}.
}
\]

这与第 29 节 RH 的 Nyman–Beurling 目标完成完全同型：最终余空间可以存在，只要指定目标在余空间中的投影为零。

---

## 34.5 金融创新的正交增益与 Gram–Schur 公式

设现有 marketed payoff 空间为 \(\mathcal M_N\)，加入新资产支付 \(Y_{N+1}\)。定义其相对于旧市场的创新：

\[
r_{N+1}
=
(I-P_{\mathcal M_N})Y_{N+1}.
\]

若 \(r_{N+1}=0\)，新资产在收益层完全冗余，不改变可对冲空间。

若 \(r_{N+1}\ne0\)，则

\[
\mathcal M_{N+1}
=
\mathcal M_N
\oplus
\operatorname{span}(r_{N+1}).
\]

### 定理 34.5（新证券对目标负债的单步套保增益）

令

\[
d_N(X)
=
\operatorname{dist}(X,\mathcal M_N).
\]

若 \(r_{N+1}\ne0\)，则

\[
\boxed{
d_N(X)^2-d_{N+1}(X)^2
=
\frac{
|\langle X,r_{N+1}\rangle|^2
}{
\|r_{N+1}\|^2
}.
}
\]

#### 证明

新增正交壳层的单位向量为

\[
e_{N+1}
=
\frac{r_{N+1}}{\|r_{N+1}\|}.
\]

套保误差下降量恰为目标在新壳层上的平方投影：

\[
|\langle X,e_{N+1}\rangle|^2.
\]

\(\square\)

所以金融创新的真实增量不由“新发行一个证券”这一名字决定，而由两个量决定：

\[
\boxed{
\text{它相对于旧市场是否有正交创新};
}
\]

\[
\boxed{
\text{该创新是否与待管理目标风险耦合}.
}
\]

一个支付结构极其新颖的资产，如果与某个机构的负债余量正交，对该机构的目标完成没有直接帮助。反之，一个维数很小的新壳层，只要与目标高度对齐，也可以显著降低套保余量。
---

## 34.6 信息商、Blackwell 精化与理性疏忽

设真实经济状态为有限随机变量

\[
\Theta\in\mathcal X.
\]

观察者获得信号

\[
Y=q(\Theta).
\]

若另一个信号 \(Y_1\) 可由更细信号 \(Y_0\) 经过再映射获得：

\[
Y_1=r(Y_0),
\]

则 \(Y_0\) Blackwell 不弱于 \(Y_1\)。在确定性读出情形：

\[
\mathcal K(Y_1)
\subseteq
\mathcal K(Y_0),
\]

与第 33 节知识代数的反变单调性一致。

### 定理 34.6（有限确定读出的熵商余分解）

\[
\boxed{
H(\Theta)
=
H(Y)
+
H(\Theta\mid Y).
}
\]

其中：

\[
H(Y)
=
\text{观察界面保留的分类不确定性},
\]

\[
H(\Theta\mid Y)
=
\text{读出纤维内部仍未分辨的状态不确定性}.
\]

若 \(Y_1=r(Y_0)\)，则

\[
\boxed{
H(\Theta\mid Y_0)
\le
H(\Theta\mid Y_1).
}
\]

因此观察 refinement 缩小信息余量。

Blackwell 理论进一步说明：对任意给定的决策问题，更细实验的最优期望收益不低于其 garbling。这里的“更有信息”不是信号维数更大，而是所有决策问题上的可用性偏序。

但经济主体通常不能免费选择无限精细观察。理性疏忽模型把观察界面本身写成优化变量：

\[
\boxed{
\max_{K(a\mid\theta)}
\mathbb E[u(a,\Theta)]
-
\lambda I(\Theta;A).
}
\]

所以经济观察者不是被动给定的商，而是：

\[
\boxed{
\text{在决策收益与信息处理成本之间选择的内生商}.
}
\]

高条件熵不必表示主体非理性；它可能是支付信息成本以后仍然最优保留的余量。

---

## 34.7 价格是内生观察者：信息效率的反身闭包

市场价格既聚合信息，又影响信息生产激励。设基本状态为 \(\theta\)，主体可支付成本 \(\kappa>0\) 获得私人信息并交易，价格 \(P\) 由订单流与市场清算产生。

### 命题 34.7（完全揭示与付费信息激励的条件冲突）

假设：

1. 价格中的状态信息只能来自付费信息主体的交易；
2. 完全揭示价格一旦形成，任何主体额外获得该私人信息的边际交易毛收益为零；
3. 信息成本严格为正：
   \[
   \kappa>0.
   \]

则不存在同时满足以下两项的均衡：

\[
\boxed{
\text{存在正的私人信息生产};
}
\]

\[
\boxed{
\text{价格完全揭示该信息}.
}
\]

#### 证明

若价格完全揭示状态，假设 2 给出付费信息的边际毛收益为零；扣除严格正成本后，购买信息严格劣于不购买，故均衡信息生产为零。由假设 1，没有付费信息交易便没有该信息进入价格的来源，与完全揭示矛盾。 \(\square\)

这是 Grossman–Stiglitz 信息效率悖论的最小闭包形式：

\[
\boxed{
\text{价格观察界面的精度}
\longrightarrow
\text{改变信息生产激励}
\longrightarrow
\text{反过来改变价格观察界面的精度}.
}
\]

因此价格映射不是外生的

\[
q:X\to Y,
\]

而是策略固定点的一部分：

\[
\boxed{
q
=
\operatorname{Clearing}
\bigl(
\operatorname{Strategies}(q)
\bigr).
}
\]

市场观察者必须同时闭合状态、策略、信息成本和清算规则。

---

## 34.8 对角化的经济版本：公开预测可能改变其预测对象

设状态空间为 \(X\)，公开预测取值空间为 \(Y\)，并存在无不动点变换

\[
\tau:Y\to Y,
\qquad
\tau(y)\ne y.
\]

一个预测器是

\[
f:X\to Y.
\]

公开预测后，主体依据 \(f\) 行动，真实结果记为

\[
R(f,x)\in Y.
\]

### 定理 34.8（战略响应下的对角预测障碍）

若对每个预测器 \(f\)，都存在某个状态 \(x_f\) 使市场或政策响应能够实现

\[
\boxed{
R(f,x_f)=\tau(f(x_f)),
}
\]

则不存在对所有状态普遍正确的预测器：

\[
\boxed{
\nexists f\;
\forall x,\quad
R(f,x)=f(x).
}
\]

#### 证明

若存在普遍正确的 \(f\)，在 \(x_f\) 上同时有

\[
R(f,x_f)=f(x_f)
\]

和

\[
R(f,x_f)=\tau(f(x_f)),
\]

从而

\[
f(x_f)=\tau(f(x_f)),
\]

与 \(\tau\) 无不动点矛盾。 \(\square\)

该定理不是说所有经济预测都会失败。它说明：

\[
\boxed{
\text{当被预测主体拥有足够的战略响应能力时，
“公开预测”与“被预测过程”不能再按外生数据生成过程处理}.
}
\]

市场可以出现自我实现预测，也可以出现自我否定预测；是否存在稳定固定点取决于响应映射，而不是由对角化自动决定。

### Lucas 型自然性缺陷

设历史读出为

\[
q:X\to Z,
\]

历史上拟合的约化动力学为

\[
\widehat T_\pi:Z\to Z,
\]

政策 \(\pi\) 在完整状态上的真实作用为

\[
T_\pi:X\to X.
\]

定义政策自然性缺陷：

\[
\boxed{
\varepsilon_\pi(x)
=
d_Z
\left(
q(T_\pi x),
\widehat T_\pi(qx)
\right).
}
\]

若政策改变了主体规则、预期或约束，历史上的商关系可能不再是 \(T_\pi\)-同余，因此

\[
\varepsilon_\pi(x)\ne0.
\]

这把 Lucas critique 写成项目语言：

\[
\boxed{
\text{历史约化模型没有自然地下降到新政策下的观察商}.
}
\]

同样，当绩效指标 \(q\) 被直接设为目标后，主体操作会改变 \(q\) 与真实目标之间的关系；这是一类 Goodhart 型界面漂移，而不是单纯测量噪声。

---

## 34.9 市值不是现金：边际价格坐标与总体可兑现值分离

设某公司有 \(N\) 股流通股，当前显示价格为 \(p\)。账面市值为

\[
\boxed{
V_{\mathrm{mark}}=Np.
}
\]

假设一笔规模为 \(\delta\) 的交易使显示价格从 \(p_0\) 变为 \(p_1\)，成交平均价为 \(\bar p\)。该笔交易实际转移现金约为

\[
C_{\mathrm{trade}}=\delta\bar p,
\]

而显示市值变化为

\[
\Delta V_{\mathrm{mark}}
=
N(p_1-p_0).
\]

### 定理 34.9（边际成交的账面放大）

在上述条件下：

\[
\boxed{
\frac{
|\Delta V_{\mathrm{mark}}|
}{
C_{\mathrm{trade}}
}
=
\frac{
N|p_1-p_0|
}{
\delta\bar p
}.
}
\]

只要 \(\delta\ll N\)，市值变化就可以远大于该笔成交现金。

这只是一个会计—坐标恒等式：显示价格用边际成交为全部存量股份重新标价。它不声称任意小交易必然能造成任意价格跳变；价格跳变大小由订单簿、信息和做市深度决定。

因此：

\[
\boxed{
\text{市值变化没有与净现金流入一一对应的守恒律}.
}
\]

全球现金总量近似不变时，股票市值仍可大幅上升，因为发生的是现金相对于股票索取权的交换比率变化，而不是每一美元市值增量都由一美元现金永久“注入”。

---

## 34.10 标记价值与清算现金之间的流动性余量

设持有 \(Q\) 单位资产，当前边际价格为

\[
P(0)=p_0.
\]

若累计卖出 \(x\) 单位后的边际成交价格为非增函数

\[
P(x),
\qquad
0\le x\le Q,
\]

则全部清算可获得现金为

\[
\boxed{
\mathcal L(Q)
=
\int_0^Q P(x)\,dx.
}
\]

当前 mark-to-market 价值为

\[
V_{\mathrm{mark}}(Q)=p_0Q.
\]

### 定理 34.10（流动性余量非负）

若 \(P\) 非增，则

\[
\boxed{
\mathcal L(Q)
\le
p_0Q.
}
\]

定义流动性余量：

\[
\boxed{
R_{\mathrm{liq}}(Q)
=
p_0Q-\mathcal L(Q)
=
\int_0^Q
\bigl(
p_0-P(x)
\bigr)\,dx
\ge0.
}
\]

#### 证明

对所有 \(x\ge0\)：

\[
P(x)\le P(0)=p_0.
\]

积分即得。 \(\square\)

若采用线性价格冲击：

\[
P(x)=p_0-\lambda x,
\]

并假设区间内价格非负，则

\[
\boxed{
\mathcal L(Q)
=
p_0Q-\frac{\lambda Q^2}{2},
}
\]

\[
\boxed{
R_{\mathrm{liq}}(Q)
=
\frac{\lambda Q^2}{2}.
}
\]

所以：

\[
\boxed{
\text{市值是边际价格坐标};
\qquad
\text{清算现金是沿订单簿路径积分};
\qquad
\text{二者之差是市场深度余量}.
}
\]

这解释了为什么压力状态下“账面资产大于债务”与“能够按时获得足够结算现金”是两个不同命题。
---

## 34.11 固定名义债务把连续资产负债表变成离散违约界面

设压力状态下可用结算资源为

\[
L
=
C
+
\sum_j\mathcal L_j(Q_j)
+
F_{\mathrm{committed}}
+
P_{\mathrm{in}},
\]

其中：

- \(C\) 是现有现金；
- \(\mathcal L_j(Q_j)\) 是资产 \(j\) 的压力清算现金；
- \(F_{\mathrm{committed}}\) 是可靠已承诺融资；
- \(P_{\mathrm{in}}\) 是在结算窗口内实际可收到的付款。

短期固定名义义务为

\[
D_{\mathrm{due}}.
\]

定义结算边际：

\[
\boxed{
g_{\mathrm{settle}}
=
L-D_{\mathrm{due}}.
}
\]

违约／支付失败指示为：

\[
\boxed{
\mathbf 1_{\mathrm{fail}}
=
\mathbf 1_{\{g_{\mathrm{settle}}<0\}}.
}
\]

这正是本文“连续—离散界面”的经济实例：

\[
\boxed{
\text{连续资产价格与流动性路径}
\longrightarrow
\text{零结算界面}
\longrightarrow
\text{支付成功／失败的离散分类}.
}
\]

定义压力现金覆盖率：

\[
\boxed{
\operatorname{CCR}
=
\frac{L}{D_{\mathrm{due}}}.
}
\]

则

\[
\operatorname{CCR}<1
\]

是单体支付缺口的直接判据。

但必须区分：

\[
\boxed{
\text{流动性失败}
\ne
\text{经济价值上的资不抵债}.
}
\]

长期资产现值可以高于总负债，但若资产不能在结算时点转换为现金，主体仍可发生支付失败。反之，短期获得外部流动性可以避免支付失败，却不保证长期净值为正。

---

## 34.12 杠杆是价格余量到权益损失的微分放大器

设资产价值为 \(A\)，固定债务为 \(D\)，权益为

\[
E=A-D>0.
\]

定义资产杠杆：

\[
\ell=\frac AE.
\]

在债务短期固定时：

\[
dE=dA.
\]

因此：

\[
\boxed{
\frac{dE}{E}
=
\ell
\frac{dA}{A}.
}
\]

所以杠杆 \(\ell\) 是资产价值相对变化到权益相对变化的局部放大倍数。

若资产价值中还包含流动性余量误差：

\[
A_{\mathrm{exec}}
=
A_{\mathrm{mark}}-R_{\mathrm{liq}},
\]

则执行价值权益为

\[
E_{\mathrm{exec}}
=
E_{\mathrm{mark}}-R_{\mathrm{liq}}.
\]

当

\[
R_{\mathrm{liq}}\ge E_{\mathrm{mark}},
\]

主体即使账面权益非负，也可能在可执行价值下进入零或负权益区间。

因此：

\[
\boxed{
\text{杠杆不会创造原始价格误差，
但会把价格、折价和流动性余量集中放大到剩余权益层}.
}
\]

---

## 34.13 融资流动性—市场流动性反馈的最小稳定性模型

考虑持有 \(Q\) 单位抵押资产的主体。累计强制出售量为 \(x_t\)，价格冲击为：

\[
p_t=p_0-\lambda x_t,
\qquad
\lambda>0.
\]

抵押折算率为

\[
\alpha\in(0,1],
\]

所以可支持债务为

\[
B_t=\alpha Qp_t.
\]

固定债务为 \(D\)。若债务超过抵押能力，下一轮需按基准价格 \(p_0\) 折算出强制出售量：

\[
\boxed{
x_{t+1}
=
\frac{
[D-\alpha Q(p_0-\lambda x_t)]_+
}{p_0}.
}
\]

在短缺严格为正的活动区间，映射为：

\[
x_{t+1}=a+bx_t,
\]

其中

\[
a=\frac{D-\alpha Qp_0}{p_0},
\]

\[
\boxed{
b=\frac{\alpha Q\lambda}{p_0}.
}
\]

### 定理 34.11（流动性反馈的局部收缩门槛）

在保持活动区间且价格非负的局部模型中：

1. 若
   \[
   0\le b<1,
   \]
   则反馈映射是收缩，唯一固定点为
   \[
   \boxed{
   x^*=\frac{a}{1-b},
   }
   \]
   并且迭代局部收敛；
2. 若
   \[
   b>1,
   \]
   则该固定点局部不稳定，小的出售偏差会被反馈放大；
3. \(b=1\) 是线性化的临界门槛。

#### 证明

活动区间内：

\[
x_{t+1}-x^*
=
b(x_t-x^*).
\]

故误差按 \(b^t\) 缩放。 \(\square\)

这里：

\[
\boxed{
b
=
\text{价格冲击}
\times
\text{抵押敏感度}
\times
\text{持仓规模}
\div
\text{结算价格尺度}.
}
\]

它是融资流动性与市场流动性相互强化的环路增益。该模型只是局部门槛演示；现实中还需加入非线性订单簿、内生 haircut、多个资产、战略交易、跳跃违约和网络支付。成熟金融文献已经研究 margin spiral 与 market/funding liquidity 的互相强化；本节新增的是把它接入本文自然性缺陷和迭代放大演算。

---

## 34.14 支付网络：aggregate 商可以隐藏违约拓扑余量

设机构 \(i\) 的总名义义务为

\[
\bar p_i,
\]

相对负债矩阵为

\[
\Pi,
\]

外部压力现金为

\[
e_i\ge0.
\]

标准比例清算映射为：

\[
\boxed{
\Phi(p)
=
\bar p
\wedge
(e+\Pi^\top p),
}
\]

其中 \(\wedge\) 表示逐坐标最小值。

该映射在区间

\[
[0,\bar p]
\]

上单调。有限维完全格上的单调性给出最小和最大清算固定点；在标准正则条件下二者一致，得到唯一清算向量。

定义支付短缺：

\[
\boxed{
S(p)
=
\sum_i(\bar p_i-p_i).
}
\]

### 例 34.12（相同 aggregate 账本，不同网络清算结果）

考虑两家银行与一个社会节点，所有金额均为 \(100\)。

两套系统均具有：

\[
\text{总外部现金}=100,
\]

\[
\text{总银行间名义负债}=100,
\]

\[
\text{总对外名义负债}=100.
\]

#### 系统 A

- 银行 1 外部现金为 \(0\)，欠银行 2：\(100\)；
- 银行 2 外部现金为 \(100\)，欠社会节点：\(100\)。

银行 1 无资源，不能支付内部债务；银行 2 依靠自身外部现金仍可向社会支付 \(100\)。银行间义务短缺为 \(100\)。

#### 系统 B

- 银行 2 外部现金为 \(100\)，欠银行 1：\(100\)；
- 银行 1 外部现金为 \(0\)，欠社会节点：\(100\)。

银行 2 向银行 1 支付 \(100\)，银行 1 再向社会支付 \(100\)，全部义务结清。

所以：

\[
\boxed{
\text{相同的 aggregate 现金、内部债务和外部债务}
\not\Rightarrow
\text{相同的清算结果}.
}
\]

差异位于有向负债网络的关联余量中。

因此只读取总资产、总债务或系统净额的观察者，可能把两个系统放入同一 aggregate 商类；但清算动力学并不能下降到该商，因为网络拓扑没有被保留。

这与第 33 节 CRT 局部边缘不能恢复高阶关联完全同型：

\[
\boxed{
\text{局部或 aggregate 完成}
\not\Rightarrow
\text{关联结构完成}.
}
\]

---

## 34.15 现金总量不涨而股市市值上涨：严格结算

现在可以回答本文经济应用中的核心问题。

设经济中的结算现金存量近似固定，但股票价格普遍上升。并不需要存在与市值增量等额的现金流入，原因有三层。

### 第一层：价格是交换比率，不是库存守恒量

股票价格表示边际单位股票相对于现金的交换率。若主体更愿意持有股票、贴现率下降、风险溢价下降、预期现金流上升或可供出售深度下降，边际交换率可以变化。

### 第二层：市值按边际价格重估全部存量

\[
V_{\mathrm{market}}=Np
\]

使用边际价格为 \(N\) 股重新计价。实际成交只涉及其中很小部分，故

\[
\Delta V_{\mathrm{market}}
\]

可以远大于同期净现金转移。

### 第三层：压力兑现受清算路径约束

若大量持有人同时要求转回结算现金，可获得的不是

\[
Np,
\]

而是：

\[
\mathcal L(N)
=
\int_0^N P(x)\,dx.
\]

所以危机不由“市值超过现金总量”本身触发，而由以下不等式触发：

\[
\boxed{
\text{固定时间窗口内必须支付的现金义务}
>
\text{该窗口内可获得的压力结算现金}.
}
\]

更完整地：

\[
\boxed{
D_{\mathrm{due}}
>
C
+
\sum_j\mathcal L_j(Q_j)
+
F_{\mathrm{reliable}}
+
P_{\mathrm{in}}.
}
\]

若债务和保证金需求也随上涨阶段扩张，则上涨可以同时增加账面财富与结算脆弱性：

\[
\boxed{
\text{mark-to-market 资本扩张}
+
\text{固定名义杠杆扩张}
+
\text{低估流动性余量}
}
\]

在压力状态下可能坍缩为：

\[
\boxed{
\text{强制出售}
\to
\text{价格冲击}
\to
\text{抵押能力下降}
\to
\text{更多强制出售}.
}
\]

因此应监测的不是“全球现金／全球市值”单一比值，而是一个多轴压力账本：

\[
\boxed{
\begin{aligned}
&\text{短期固定现金义务},\\
&\text{压力清算曲线},\\
&\text{haircut 与追加保证金规则},\\
&\text{融资承诺可靠性},\\
&\text{支付网络拓扑},\\
&\text{持仓集中度与共同出售相关性}.
\end{aligned}
}
\]

---

## 34.16 经济时间的分裂：日历、结算、交易、信息与资产负债表时间

经济系统至少包含五种不能预先等同的时间。

### 日历时间

\[
t_{\mathrm{cal}}
\]

记录合同和宏观过程的外部顺序。

### 结算时间

\[
t_{\mathrm{settle}}
\]

由债务到期、保证金调用和支付窗口决定。即使长期价值不变，结算时点错配也可触发失败。

### 交易事件时间

\[
n_{\mathrm{trade}}
\]

按成交或订单簿更新计数。高频市场中，同一日历时间可以包含极不均匀的事件密度。

### 信息时间

可用公共信念更新的累计信息距离表示，例如：

\[
\boxed{
\tau_{\mathrm{info}}(N)
=
\sum_{k=0}^{N-1}
D_{\mathrm{KL}}
(\mu_{k+1}\Vert\mu_k),
}
\]

在每项有限时非负且可加。它测量信念更新路径，不等同于福利或物理作用量。

### 资产负债表时间

反复 haircut 或流动性乘数

\[
g_k\in(0,1]
\]

使可执行价值满足

\[
V_N=V_0\prod_{k=1}^Ng_k.
\]

定义流动性记录作用：

\[
\boxed{
\mathfrak A_N^{\mathrm{liq}}
=
-\log\frac{V_N}{V_0}
=
\sum_{k=1}^N-\log g_k.
}
\]

它与第 33 节环境记录作用具有同一乘法—加法结构，但经济含义不同：这里记录的是连续压力步骤对可兑现价值的累计折损，不是量子相干。

所以：

\[
\boxed{
\text{经济时间不是一个单轴参数，
而是状态变化、结算门槛、交易密度、信息更新和流动性折损的耦合序}.
}
\]

---

## 34.17 经济逃逸率不能压成一个指标

本框架中至少存在以下经济余量。

### 套保余量

\[
\boxed{
r_N^{\mathrm{hedge}}(X)
=
\|P_{\mathcal M_N^\perp}X\|_2^2.
}
\]

### 流动性余量率

\[
\boxed{
r^{\mathrm{liq}}(Q)
=
1-
\frac{\mathcal L(Q)}{p_0Q}.
}
\]

### 信息余量率

在有限离散状态且 \(H(\Theta)>0\) 时：

\[
\boxed{
r^{\mathrm{info}}(Y)
=
\frac{H(\Theta\mid Y)}{H(\Theta)}.
}
\]

### 网络支付余量率

\[
\boxed{
r^{\mathrm{net}}
=
\frac{
\sum_i(\bar p_i-p_i)
}{
\sum_i\bar p_i
}.
}
\]

### 政策自然性缺陷

\[
\boxed{
r^{\mathrm{policy}}_\pi(x)
=
d
\left(
q(T_\pi x),
\widehat T_\pi(qx)
\right).
}
\]

### 战略对角缺陷

\[
\boxed{
r^{\mathrm{diag}}_f(x)
=
d_Y
\left(
R(f,x),f(x)
\right).
}
\]

这些量分别测量：

- 未被交易资产张成的支付风险；
- 不能按边际价格兑现的资产价值；
- 信号纤维中残留的状态不确定性；
- 支付网络未结清的义务；
- 政策变化下约化模型的不自然性；
- 公开预测被战略响应改变的程度。

它们可以相互反馈，但不是同一“经济熵”或“市场逃逸率”。
---

## 34.18 市场完整度必须是向量

定义经济观察者的多轴闭合向量：

\[
\boxed{
\mathbf C_{\mathrm{econ}}
=
(
C_{\mathrm{price}},
C_{\mathrm{hedge}},
C_{\mathrm{info}},
C_{\mathrm{liq}},
C_{\mathrm{settle}},
C_{\mathrm{network}},
C_{\mathrm{policy}},
C_{\mathrm{reflex}}
).
}
\]

其中：

\[
\begin{aligned}
C_{\mathrm{price}}
&=\text{价格是否良定义地下降到收益商},\\
C_{\mathrm{hedge}}
&=\text{目标支付是否进入 marketed payoff 闭包},\\
C_{\mathrm{info}}
&=\text{价格／信号对目标状态的分离能力},\\
C_{\mathrm{liq}}
&=\text{mark value 到 executable cash 的转换能力},\\
C_{\mathrm{settle}}
&=\text{到期窗口内固定现金义务覆盖},\\
C_{\mathrm{network}}
&=\text{aggregate 读出是否保留清算拓扑},\\
C_{\mathrm{policy}}
&=\text{约化关系在政策改变下是否自然},\\
C_{\mathrm{reflex}}
&=\text{读出公开后是否因主体响应而改变自身生成机制}.
\end{aligned}
\]

几个关键非蕴含是：

\[
\boxed{
\text{无套利}
\not\Rightarrow
\text{市场完备};
}
\]

\[
\boxed{
\text{市场完备}
\not\Rightarrow
\text{压力流动性充足};
}
\]

\[
\boxed{
\text{账面偿付能力}
\not\Rightarrow
\text{结算时点流动性};
}
\]

\[
\boxed{
\text{价格高度信息化}
\not\Rightarrow
\text{信息生产激励稳定};
}
\]

\[
\boxed{
\text{aggregate 资产负债表相同}
\not\Rightarrow
\text{支付网络风险相同};
}
\]

\[
\boxed{
\text{历史预测准确}
\not\Rightarrow
\text{政策干预后仍准确}.
}
\]

因此“市场效率”若不声明轴和观察界面，就不是一个类型充分的数学性质。

---

## 34.19 与现有经济学的边界及候选项目贡献

以下结构具有成熟前驱，不能重新命名为项目独有发现：

- Arrow–Debreu 竞争均衡与完全市场；
- Blackwell 实验比较；
- Harrison–Kreps 型无套利与状态价格；
- Grossman–Stiglitz 信息效率悖论；
- Lucas policy critique；
- Sims rational inattention；
- Eisenberg–Noe 支付清算固定点；
- Brunnermeier–Pedersen 市场／融资流动性反馈；
- 最小方差套期保值、Gram 投影和风险中性定价；
- 价格冲击、订单簿深度与 fire-sale 模型。

本节的候选贡献位于这些结果与项目统一观察者语言的组合：

1. 把 law of one price 识别为价格对收益商的严格因子化；
2. 把不完备市场写成目标支付的 Hilbert 余风险，并用正交壳层量化每个新证券的目标增益；
3. 把状态价格非唯一性写成正锥内的定价余纤维，把风险中性概率解释为 numeraire 截面；
4. 把名义债务识别为破坏价格射影规范的结算边界条件；
5. 把市值—现金差异写成边际重估与清算路径积分之间的流动性余量；
6. 把支付网络 topology 识别为 aggregate 商丢失的关联余量；
7. 把 Grossman–Stiglitz、Lucas 和公开预测反馈统一为内生观察界面的闭包／自然性问题；
8. 把金融稳定拆成定价、套保、信息、流动性、结算、网络、政策和反身八轴，而不是单一效率分数。

是否具有发表价值仍取决于进一步文献审计，以及能否在该统一语言中证明超出现有结果简单重述的新界、稳定性定理或可计算证书。

### 参考接口

- K. J. Arrow and G. Debreu, *Existence of an Equilibrium for a Competitive Economy*, 1954.
- D. Blackwell, *Equivalent Comparisons of Experiments*, 1953.
- R. E. Lucas Jr., *Econometric Policy Evaluation: A Critique*, 1976.
- J. M. Harrison and D. M. Kreps, *Martingales and Arbitrage in Multiperiod Securities Markets*, 1979.
- S. J. Grossman and J. E. Stiglitz, *On the Impossibility of Informationally Efficient Markets*, 1980.
- L. Eisenberg and T. H. Noe, *Systemic Risk in Financial Systems*, 2001.
- C. A. Sims, *Implications of Rational Inattention*, 2003.
- M. K. Brunnermeier and L. H. Pedersen, *Market Liquidity and Funding Liquidity*, 2009.

---

## 34.20 建议 Lean 形式化顺序

1. `PriceFactorsThroughPayoffQuotient`
   \[
   \ker A\subseteq\ker c^\top
   \iff
   \exists!\ell,\ c^\top=\ell\circ A.
   \]

2. `ZeroPayoffPriceDifferenceArbitrage`
   收益相同而价格不同给出零终端支付套利。

3. `NumeraireGaugeInvariantBudget`
   \[
   B(\lambda p,\lambda w)=B(p,w).
   \]

4. `NominalDebtBreaksPriceGauge`
   \[
   D/(\lambda p_j)=\lambda^{-1}D/p_j.
   \]

5. `StatePriceAffineFiber`
   \[
   \{\pi:A^\top\pi=c\}
   =
   \pi_0+\ker A^\top.
   \]

6. `TargetHedgeOrthogonalProjection`
   \[
   \inf_{Y\in\mathcal M}\|X-Y\|^2
   =
   \|P_{\mathcal M^\perp}X\|^2.
   \]

7. `SecurityInnovationHedgeGain`
   \[
   d_N^2-d_{N+1}^2
   =
   |\langle X,r_{N+1}\rangle|^2/\|r_{N+1}\|^2.
   \]

8. `DeterministicSignalEntropyRemainder`
   \[
   H(\Theta)=H(q\Theta)+H(\Theta\mid q\Theta).
   \]

9. `SignalGarblingKnowledgeAntitone`
   \[
   q_1=rq_0
   \Rightarrow
   \mathcal K(q_1)\subseteq\mathcal K(q_0).
   \]

10. `StrategicPredictionDiagonalObstruction`
    形式化定理 34.8。

11. `MarginalRepricingAmplification`
    \[
    \Delta V=N\Delta p.
    \]

12. `LiquidationValueBelowMark`
    \[
    \int_0^QP(x)\,dx\le P(0)Q.
    \]

13. `LinearImpactLiquidityRemainder`
    \[
    R_{\mathrm{liq}}(Q)=\lambda Q^2/2.
    \]

14. `LeverageDifferentialAmplification`
    \[
    dE/E=(A/E)\,dA/A.
    \]

15. `LiquidityFeedbackContraction`
    活动区间内 \(b<1\) 的固定点唯一性和收敛。

16. `ClearingMapMonotone`
    \[
    \Phi(p)=\bar p\wedge(e+\Pi^\top p)
    \]
    的单调性。

17. `AggregateBalanceSheetNetworkCounterexample`
    形式化例 34.12。

18. `EconomicCompletenessNonImplications`
    为无套利、完备、流动性、结算和信息效率之间的非蕴含构造有限反例。

这些声明应以标准线性代数、有限概率和序理论对象实现。Harrison–Kreps、Blackwell、Grossman–Stiglitz、Eisenberg–Noe 等外部经典结果若被用作完整桥，应以具名、可审计接口接入，不得隐藏为无名公理。

---

## 34.21 最终统一式

经济学接入本文以后，得到：

\[
\boxed{
\text{价格}
=
\text{经济状态相对于 traded payoff、numeraire 与边际市场深度的读出坐标}.
}
\]

\[
\boxed{
\text{无套利}
=
\text{价格在相同终端收益的商上良定义}.
}
\]

\[
\boxed{
\text{不完备市场}
=
\text{目标支付仍有 marketed payoff 子空间之外的 Hilbert 余量}.
}
\]

\[
\boxed{
\text{风险中性概率}
=
\text{正状态价格泛函在 numeraire 下的归一化坐标}.
}
\]

\[
\boxed{
\text{市值}
=
\text{边际成交价格对全部存量索取权的重估}.
}
\]

\[
\boxed{
\text{可兑现现金}
=
\text{沿流动性曲线执行得到的路径积分}.
}
\]

\[
\boxed{
\text{固定债务}
=
\text{破坏名义尺度规范并产生零结算界面的合同条件}.
}
\]

\[
\boxed{
\text{金融危机}
=
\text{固定结算义务超过压力可兑现现金，
并经杠杆、抵押和支付网络反馈放大}.
}
\]

\[
\boxed{
\text{信息价格}
=
\text{主体选择和市场清算共同生成的内生观察界面}.
}
\]

\[
\boxed{
\text{经济对角化}
=
\text{公开模型、指标或预测进入主体策略以后，
原被预测关系无法保持外生闭合的证书}.
}
\]

最凝练的结论是：

\[
\boxed{
\text{财富、价格、现金、概率与风险不是同一个守恒量；
它们是经济整体经过不同观察界面、结算规则和时间窗口后得到的不同坐标与余量}.
}
\]

因此，现金总量几乎不变而股市市值持续上升本身并不构成矛盾。真正需要审计的是：

\[
\boxed{
\text{边际价格创造了多少账面重估，
其中多少能在压力路径中转换为结算现金，
以及哪些固定债务会在转换完成以前到期}.
}
\]

### 34.22 严格非主张

1. 本节不把竞争均衡存在性约化为无套利。
2. 本节不把风险中性概率解释为真实事件频率。
3. 本节不把最小均方套保等同于所有偏好下的最优风险管理。
4. 本节不声称任何小额成交都能造成任意市值跳变。
5. 本节不把 market capitalization 当作全体持有人可同时兑现的现金。
6. 本节不把单体 \(\operatorname{CCR}<1\) 当作完整系统性危机的充分必要条件。
7. 本节不把线性流动性反馈模型当作现实市场的完整校准模型。
8. 本节不把 aggregate 统计无效解释为 aggregate 数据没有价值。
9. 本节不把信息熵直接等同于福利、价格效率或热力学熵。
10. 本节不声称所有公开预测都会被主体对角反转；定理 34.8 明确依赖战略响应可实现性。
11. 本节不把名义价格尺度规范与一般物理 gauge theory 视为同一定理。
12. 本节不把 Sections 28–33 的量子、数论或 solenoid 对象与经济变量作本体同一。
13. 本节不提供投资、杠杆或交易建议。
14. 本节新增结论均为纸面推导；未经 Lean kernel 验证不得标记为 `Closed`。

---

# 35. 追加：带初始坐标的连续统观察者、叶—横截双结构与黄金悬挂
## Anchored-Continuum Observers, Leaf–Transversal Duality, and Golden Suspensions

### 35.0 文档地位、问题修正与承重边界

前文主要把观察者写成连续统内部的有限读出、商、可观测代数、预测闭包、路径账本与对角审计。本节研究一个更强的可能性：

\[
\boxed{
\text{观察者本身是否可以是一种带初始坐标的连续统？}
}
\]

答案是肯定的，但“既连续又离散”必须严格分型。一个非空空间不可能在同一个拓扑下同时既连通又离散，除非它只有一个点。因此，正确结构不是把两个互斥性质塞进同一个方向，而是把观察者组织成：

\[
\boxed{
\text{叶方向连续}
+
\text{横截方向全不连通}
+
\text{有限读出离散}
+
\text{路径提升与记忆保存初始坐标}.
}
\]

本节把这一结构与仓库已经闭合或部分闭合的以下接口连接：

- universal solenoid 的连通整体、稠密实流、可见圆投影与 profinite 隐藏核；
- streamline decomposition 中“连续实提升 + 常值隐藏偏移”的唯一分解；
- path-orbit classification 中路径分量与实流轨道的一致性；
- throat transition cocycle 中不同局部提升之间的隐藏纤维差满足加法 cocycle；
- Minkowski golden embedding 中物理坐标与共轭内部坐标；
- Fibonacci–golden partition 中整数权重与逆黄金尺度的精确单位分割；
- 前文的有限读出、预测观察者、记忆账本、上下文商余与对角逃逸。

本节不会把观察者连续统等同于意识本体，不会把 Cantor 横截直接等同于量子离散结果，也不会把黄金比例宣称为一切连续—离散系统的唯一来源。新增结果均为纸面定理；在 Lean proof term、依赖闭包、admission 与冻结收据齐备以前不得标记为 `Closed`。

---

## 35.1 同一拓扑下“连通且离散”的不可能性

### 定理 35.1（连通离散空间退化）

设 \(X\) 是非空拓扑空间。若 \(X\) 连通且离散，则 \(X\) 只有一个点。

#### 证明

若 \(x\in X\)，离散性说明 \(\{x\}\) 为开集，其补集 \(X\setminus\{x\}\) 也为开集。若存在 \(y\neq x\)，则

\[
X=\{x\}\sqcup(X\setminus\{x\})
\]

是两个非空开集的分离，与连通性矛盾。故 \(X=\{x\}\)。 \(\square\)

所以“观察者既连续又离散”不能被解释成：

\[
\text{同一个状态空间在同一个拓扑中既非平凡连通又离散}.
\]

必须至少采用以下一种分层机制：

\[
\boxed{
\begin{aligned}
&\text{不同坐标方向：叶连续、横截全不连通};\\
&\text{不同层级：整体连续、有限商离散};\\
&\text{不同对象：状态连续、事件标签离散};\\
&\text{不同时间：流参数连续、返回次数离散};\\
&\text{不同拓扑：同一集合携带不同可访问结构}.
\end{aligned}
}
\]

其中最适合项目现有 solenoid、观察者与黄金模型集工作的，是“叶—横截”与“逆极限—有限商”两种结构。

---

## 35.2 带初始坐标的连续统观察者

### 定义 35.2（点化连续统）

点化连续统是二元组

\[
(X,\xi_0),
\]

其中 \(X\) 是非空紧致连通度量空间，\(\xi_0\in X\) 是指定原点。

若还指定一个局部坐标架、方向架或尺度架 \(\mathfrak f_0\)，则称

\[
(X,\xi_0,\mathfrak f_0)
\]

为带架连续统。

仅有 \(X\) 时，所有点仍可能被自同构群交换；指定 \(\xi_0\) 后，允许的对称群从

\[
\operatorname{Aut}(X)
\]

缩小到稳定子

\[
\operatorname{Aut}(X,\xi_0)
=
\{g\in\operatorname{Aut}(X):g(\xi_0)=\xi_0\}.
\]

再指定 \(\mathfrak f_0\) 后，对称性进一步缩小。

### 定义 35.3（锚定连续统观察者）

一个锚定连续统观察者记为

\[
\boxed{
\mathfrak O
=
(
\mathcal X_O,
\xi_0,
\mathfrak f_0,
\Phi,
\mathcal K_O,
q_O,
\widetilde{\mathcal X}_O,
\mathcal M_O,
\Delta_O
).
}
\]

其中：

\[
\begin{aligned}
\mathcal X_O
&=\text{观察者的连续统载体},\\
\xi_0
&=\text{初始锚点},\\
\mathfrak f_0
&=\text{初始坐标、方向与尺度架},\\
\Phi
&=\text{连续流、半流或动力作用},\\
\mathcal K_O
&=\text{全不连通／profinite 横截地址},\\
q_O
&=\text{有限读出、事件分割或可观测接口},\\
\widetilde{\mathcal X}_O
&=\text{保存路径提升或历史坐标的扩展状态空间},\\
\mathcal M_O
&=\text{事件数、cocycle、holonomy 与追加式记忆},\\
\Delta_O
&=\text{自评价、同址读取与对角操作}.
\end{aligned}
\]

这一定义的核心不是“观察者占据一个连续统大小的物体”，而是：

\[
\boxed{
\text{观察者是连续统被点化、带架、可读出并保存路径以后形成的结构。}
}
\]

初始坐标不是额外写在状态旁边的一串标签。它决定：

- 哪一点被叫作“这里”；
- 哪一方向被叫作“正方向”；
- 哪一尺度被叫作“单位”；
- 哪一提升被叫作“从零开始”；
- 哪些回归状态属于同一当前点但不同历史。

---

## 35.3 初始点的轨道闭包本身就是连续统

设 \(W\) 是紧致度量空间，且

\[
\Phi:\mathbb R\times W\to W
\]

为连续流。固定 \(\xi_0\in W\)，定义轨道

\[
\mathcal O(\xi_0)
=
\{\Phi_t(\xi_0):t\in\mathbb R\}
\]

和轨道闭包

\[
\boxed{
\mathcal X_{\xi_0}
=
\overline{\mathcal O(\xi_0)}.
}
\]

### 定理 35.4（轨道闭包连续统）

\(\mathcal X_{\xi_0}\) 是紧致连通子空间。

#### 证明

映射

\[
\gamma_{\xi_0}:\mathbb R\to W,
\qquad
t\mapsto\Phi_t(\xi_0)
\]

连续。由于 \(\mathbb R\) 连通，其像 \(\mathcal O(\xi_0)\) 连通；连通集的闭包仍连通。又因为 \(W\) 紧致，闭子集 \(\mathcal X_{\xi_0}\) 紧致。 \(\square\)

所以一种最小的观察者连续统可以直接定义为：

\[
\boxed{
\mathfrak O_{\xi_0}
=
\left(
\overline{\Phi_{\mathbb R}(\xi_0)},
\xi_0
\right).
}
\]

若流是最小的，即每条轨道都稠密，则：

\[
\boxed{
\mathcal X_{\xi_0}=W
\qquad
\forall\xi_0\in W.
}
\]

这时观察者与世界可以拥有相同的未点化载体，但二者仍不等同。观察者还包含：

\[
\xi_0,\quad
\mathfrak f_0,\quad
q_O,\quad
\mathcal M_O,\quad
\Delta_O.
\]

因此：

\[
\boxed{
\text{载体相同}
\not\Rightarrow
\text{观察者结构相同}.
}
\]

世界可以是未点化的动力连续统；观察者则是该连续统相对于一个初始点和一套运输规则所形成的相对结构。

---

## 35.4 锚点是对称性约化，不是绝对外部输入

设群 \(G\) 连续作用于 \(X\)。未点化系统只保留轨道结构。指定 \(\xi_0\) 后，变换 \(g\in G\) 若要保持观察者身份，必须满足：

\[
g\xi_0=\xi_0.
\]

所以锚点把允许对称性从 \(G\) 约化为稳定子：

\[
G_{\xi_0}
=
\{g\in G:g\xi_0=\xi_0\}.
\]

### 命题 35.5（锚定等价）

两个锚定动力连续统

\[
(X,\xi_0,\Phi),
\qquad
(Y,\eta_0,\Psi)
\]

等价，当且仅当存在同胚 \(h:X\to Y\)，使：

\[
h(\xi_0)=\eta_0
\]

且：

\[
h(\Phi_t x)=\Psi_t(hx)
\qquad
\forall t,x.
\]

若再有读出和记忆，则还要求：

\[
q_Y\circ h=q_X
\]

以及 cocycle／账本结构在 \(h\) 下对应。

因此观察者身份不是裸点，也不是裸流，而是：

\[
\boxed{
\text{点化动力系统的共轭类}.
}
\]

锚点不必来自连续统之外；它可以是连续统内部一次自定位所选择的基准。但一旦选择，它便产生结构性不对称：

\[
\boxed{
\text{这里}
\neq
\text{任意其他同构位置}.
}
\]

---

## 35.5 叶连续、横截全不连通

观察者连续统的局部模型可以写为：

\[
\boxed{
U\cong B^d\times K,
}
\]

其中 \(B^d\subseteq\mathbb R^d\) 是连续叶坐标，而 \(K\) 是 Cantor 空间、profinite 群或其他全不连通紧空间。

必须区分：

\[
\boxed{
\text{全不连通}
\neq
\text{离散}.
}
\]

Cantor 空间没有孤立点，因此并非离散空间。但它拥有大量 clopen 集，可以通过有限 clopen 分割产生真正离散的有限读出。

若

\[
K\cong\varprojlim_m K_m
\]

是有限离散空间 \(K_m\) 的逆极限，则：

\[
\boxed{
\begin{aligned}
K
&=\text{完整无限地址},\\
K_m
&=\text{第 }m\text{ 层有限离散读出},\\
\ker(K\to K_m)
&=\text{当前分辨率仍未看见的横截余量}.
\end{aligned}
}
\]

于是同一个观察者可以同时具有：

\[
\boxed{
\begin{aligned}
u\in B^d
&:\text{连续位置／相位／尺度},\\
\kappa\in K
&:\text{全不连通路径地址},\\
q_m(\kappa)\in K_m
&:\text{有限离散事件标签}.
\end{aligned}
}
\]

“连续且离散”真正指的是这种不同层级、不同坐标方向和不同分辨率的共存。

---

## 35.6 悬挂观察者：连续时间中的离散返回

令 \(K\) 为紧致空间，\(T:K\to K\) 为同胚，roof 函数

\[
r:K\to\mathbb R_{>0}
\]

连续。定义悬挂空间：

\[
\boxed{
\Sigma_{T,r}
=
(K\times\mathbb R)/{\sim},
}
\]

其中：

\[
(\kappa,s+r(\kappa))
\sim
(T\kappa,s).
\]

连续流定义为：

\[
\Phi_t[\kappa,s]
=
[\kappa,s+t].
\]

从商空间整体看，\(\Phi_t\) 连续；但当 \(s+t\) 穿过 roof 边界时，横截地址发生离散更新：

\[
\kappa\mapsto T\kappa.
\]

定义 Birkhoff roof 和：

\[
S_nr(\kappa)
=
\sum_{j=0}^{n-1}r(T^j\kappa),
\qquad
n\ge1,
\]

并令 \(S_0r=0\)。

### 命题 35.6（连续时间—离散事件分解）

对每个 \([\kappa,s]\) 和足够一般的 \(t\ge0\)，唯一存在整数 \(n\ge0\) 与残余相位 \(s'\) 使：

\[
S_nr(\kappa)
\le
s+t
<
S_{n+1}r(\kappa),
\]

\[
s'
=
s+t-S_nr(\kappa),
\]

以及：

\[
\boxed{
\Phi_t[\kappa,s]
=
[T^n\kappa,s'].
}
\]

所以：

\[
\boxed{
\text{连续时间}
=
\text{累计离散返回时间}
+
\text{当前叶内残余相位}.
}
\]

事件计数 \(n\) 是离散的，残余相位 \(s'\) 是连续的。二者共同构成观察者的时间坐标。

### 定理 35.7（最小 Cantor 悬挂是连通连续统）

若 \(K\) 是紧致度量空间，\(T\) 最小，且 \(r\) 连续严格为正，则 \(\Sigma_{T,r}\) 紧致连通。

#### 证明概要

紧致性来自 \(K\times[0,\max r]\) 的商。选取任意 \(\kappa_0\)，悬挂流轨道在每次返回时经过 \(T^n\kappa_0\)。由于 \(T\) 最小，\(\{T^n\kappa_0\}\) 在 \(K\) 中稠密，故该连续实流轨道在整个悬挂中稠密。轨道是 \(\mathbb R\) 的连续像，因此连通；其闭包即整个悬挂，故悬挂连通。 \(\square\)

这给出一个标准模型：

\[
\boxed{
\text{整体是连通连续统，横截动力却由离散迭代生成。}
}
\]

---

## 35.7 universal solenoid 是项目内已经存在的原型

仓库中的 universal solenoid 可写为兼容圆坐标族：

\[
\Sigma_\infty
=
\left\{
(\theta_m)_{m\in\mathbb N_{>0}}:
n\theta_{mn}=\theta_m
\right\}.
\]

其可见投影为：

\[
\pi:\Sigma_\infty\to\mathbb T,
\qquad
\pi(\theta)=\theta_1.
\]

连续实流为：

\[
\iota:\mathbb R\to\Sigma_\infty,
\qquad
\iota(t)_m=\frac{t}{m}\pmod1.
\]

仓库已经证明：

\[
\boxed{
\pi(\iota(t))=t\pmod1,
}
\]

\[
\boxed{
\overline{\iota(\mathbb R)}=\Sigma_\infty,
}
\]

以及 \(\Sigma_\infty\) 连通。

`ExactSequence` 又证明了相容同余数据嵌入恰好给出隐藏核，并形成：

\[
\boxed{
0
\longrightarrow
K_\infty
\longrightarrow
\Sigma_\infty
\overset{\pi}{\longrightarrow}
\mathbb T
\longrightarrow
0.
}
\]

因此 solenoid 同时具有：

\[
\boxed{
\begin{aligned}
\mathbb T
&=\text{可见连续相位},\\
\iota(\mathbb R)
&=\text{连续叶流},\\
K_\infty
&=\text{profinite 隐藏横截},\\
K_\infty/K^{(m)}
&=\text{有限同余读出}.
\end{aligned}
}
\]

这不是把观察者放进连续统以后再额外附加离散信息，而是：

\[
\boxed{
\text{连续相位与 profinite 地址本来就是同一连通整体的两个结构方向。}
}
\]

---

## 35.8 初始坐标的 solenoid 正规形

仓库 `StreamlineDecomposition` 已证明：固定基准时刻 \(t_0\) 和可见相位的一个实代表 \(r_0\) 后，每条连续路径

\[
\gamma:\mathbb R\to\Sigma_\infty
\]

唯一分解为：

\[
\boxed{
\gamma(t)
=
\iota(\widetilde r(t))+k_0,
}
\]

其中：

\[
\widetilde r(t_0)=r_0,
\]

而：

\[
k_0\in K_\infty
\]

在整条路径上保持常值。

所以 solenoid 观察者的初始坐标不是一个标量，而是：

\[
\boxed{
(r_0,k_0).
}
\]

其中：

\[
r_0
=
\text{连续叶上的归一化提升原点},
\]

\[
k_0
=
\text{隐藏路径扇区／同余地址}.
\]

同一可见相位可以拥有不同 \(k_0\)，同一当前 solenoid 点也可能由不同未归一化实提升表达。初始代表 \(r_0\) 消除整数平移规范，隐藏偏移 \(k_0\) 保存路径扇区。

仓库 `ThroatTransitionCocycle` 还证明：若三个局部提升具有相同可见投影，则它们之间的隐藏差

\[
k_{\alpha\beta},
\quad
k_{\beta\gamma},
\quad
k_{\alpha\gamma}
\]

唯一存在，并满足：

\[
\boxed{
k_{\alpha\gamma}
=
k_{\alpha\beta}
+
k_{\beta\gamma}.
}
\]

所以不同观察坐标图之间的隐藏转换不是任意误差，而是一个严格的加法 cocycle。

---

## 35.9 路径身份不能由当前状态自动恢复

仓库 `RealFlowRecurrence` 已证明：

\[
\boxed{
\iota(n!)\longrightarrow0
\quad
\text{于 }\Sigma_\infty,
}
\]

但：

\[
n!\longrightarrow+\infty
\quad
\text{于 }\mathbb R.
\]

同时 \(\iota\) 为单射但不是拓扑嵌入。

这意味着内部时间可以无限增长，而当前整体状态重新任意接近初始状态。

### 定理 35.8（回归轨道无连续年龄函数）

设 \(X\) 为拓扑空间，\(\Phi_t\) 为连续流，且存在：

\[
t_n\to+\infty,
\qquad
\Phi_{t_n}(x_0)\to x_0.
\]

则不存在连续函数：

\[
a:X\to\mathbb R
\]

满足：

\[
a(\Phi_t(x_0))=t
\qquad
\forall t\ge0.
\]

#### 证明

若存在，则连续性给出：

\[
a(\Phi_{t_n}(x_0))
\to
a(x_0).
\]

但左侧等于 \(t_n\to+\infty\)，矛盾。 \(\square\)

因此：

\[
\boxed{
\text{当前 ambient state}
\not\Rightarrow
\text{连续可恢复的绝对年龄}.
}
\]

若观察者必须区分：

\[
\iota(0)
\]

与某个极晚但已经回到其邻域的：

\[
\iota(n!),
\]

则必须扩展状态：

\[
\boxed{
\widetilde X
=
X\times\mathcal M
}
\]

或使用覆盖、路径群胚、cocycle／账本来保存提升坐标。

---

## 35.10 记忆是 cocycle，不只是存储数组

设流 \(\Phi_t\) 上有加法 cocycle：

\[
c:\mathbb R\times X\to G
\]

满足：

\[
\boxed{
c_{s+t}(x)
=
c_s(\Phi_t x)+c_t(x).
}
\]

观察者的扩展动力学可以写成 skew product：

\[
\boxed{
\widetilde\Phi_t(x,m)
=
(\Phi_t x,m+c_t(x)).
}
\]

若存在连续函数 \(h:X\to G\)，使：

\[
c_t(x)
=
h(\Phi_t x)-h(x),
\]

则 \(c\) 是 coboundary，记忆可以由当前状态势函数 \(h\) 重构。

### 命题 35.9（回归阻碍 coboundary 化）

若存在：

\[
t_n\to\infty,
\qquad
\Phi_{t_n}(x)\to x,
\]

但：

\[
c_{t_n}(x)\not\to0,
\]

则不存在连续 \(h\) 使 \(c_t(x)=h(\Phi_t x)-h(x)\)。

#### 证明

若存在连续 \(h\)，则：

\[
c_{t_n}(x)
=
h(\Phi_{t_n}x)-h(x)
\to0,
\]

矛盾。 \(\square\)

所以：

\[
\boxed{
\text{不可 coboundary 化的 cocycle}
=
\text{不能由当前状态压缩掉的历史余量}.
}
\]

这给“记忆”的一个结构定义：

\[
\boxed{
\text{记忆是初始坐标沿路径运输所累积、且不能降为当前状态函数的 cocycle 类。}
}
\]

---

## 35.11 同一点附近可以有完全不同的历史

设：

\[
\pi:\widetilde X\to X
\]

为路径提升或记忆扩展。两个扩展状态：

\[
\widetilde x,
\widetilde y\in\widetilde X
\]

可能满足：

\[
\pi(\widetilde x)=\pi(\widetilde y),
\]

但：

\[
\widetilde x\neq\widetilde y.
\]

因此：

\[
\boxed{
\text{当前可见状态相同}
\not\Rightarrow
\text{观察者历史状态相同}.
}
\]

更强地，即使：

\[
d_X(\pi\widetilde x,\pi\widetilde y)\ll1,
\]

提升距离、事件计数或账本差仍可以很大。

所以观察者本身若只取为 \(X\)，可能不足以保存其身份；真正的观察者状态应取为某个最小扩展：

\[
\boxed{
\widetilde X_{\mathrm{obs}}
}
\]

使目标历史量、事件量与路径扇区在该扩展上成为良定义坐标。

这与前文“预测闭包是把瞬时商修复成动力学商的最小扩张”完全平行：

\[
\boxed{
\begin{aligned}
\text{预测闭包}
&=\text{补足未来读出所需坐标},\\
\text{提升闭包}
&=\text{补足路径身份所需坐标},\\
\text{记忆闭包}
&=\text{补足不可 coboundary 化历史所需坐标}.
\end{aligned}
}
\]

---

## 35.12 概率不是连续—离散双性的定义

给定观察者连续统 \(X\)、状态测度 \(\mu\) 和有限读出：

\[
q:X\to A,
\]

其中 \(A\) 有限，离散结果概率为：

\[
\boxed{
p(a)=\mu(q^{-1}(a)).
}
\]

所以概率来自三者配对：

\[
\boxed{
\text{连续／拓扑状态空间}
+
\text{状态测度}
+
\text{有限分割}.
}
\]

离散横截或有限事件标签本身并不自动给出概率；还需要状态或不变测度。

同样，离散输出不自动产生正熵。一个离散序列可以：

- 周期且零熵；
- 非周期但零熵；
- 正熵；
- 甚至没有指定概率测度时根本没有 Shannon 熵。

因此：

\[
\boxed{
\text{离散}
\neq
\text{随机}
\neq
\text{正熵}.
}
\]

黄金／Sturmian 系统恰好提供“非周期离散但零熵”的反例。

---

## 35.13 黄金整数：一个代数操作同时扩张与收缩

令：

\[
\varphi=\frac{1+\sqrt5}{2},
\qquad
\varphi'=1-\varphi=-\varphi^{-1}.
\]

黄金整数环：

\[
\mathbb Z[\varphi]
=
\{a+b\varphi:a,b\in\mathbb Z\}
\]

拥有两个实嵌入。Minkowski 嵌入为：

\[
\boxed{
\iota_M(x)
=
(x,x'),
}
\]

其中 \(x'\) 由 \(\varphi\mapsto\varphi'\) 得到。

乘以 \(\varphi\) 在两个坐标中作用为：

\[
\boxed{
(x,x')
\longmapsto
(\varphi x,-\varphi^{-1}x').
}
\]

所以同一个代数单位同时产生：

\[
\boxed{
\text{物理方向的连续扩张}
}
\]

与：

\[
\boxed{
\text{内部方向的翻转收缩}.
}
\]

这不是把一个连续操作与另一个离散操作人为并置，而是一个整数代数自同构在两个实嵌入中的不同几何表现。

仓库 `MinkowskiModelSet` 已把这一结构实现为：

\[
x
\longmapsto
(\operatorname{embedding}(x),
\operatorname{embedding}(\operatorname{conj}x)),
\]

并通过内部窗口选择物理投影上的离散模型集。

---

## 35.14 Fibonacci 替换的连续—离散谱分解

定义 Fibonacci 替换：

\[
\sigma(L)=LS,
\qquad
\sigma(S)=L.
\]

其计数矩阵为：

\[
\boxed{
M_\varphi
=
\begin{pmatrix}
1&1\\
1&0
\end{pmatrix}.
}
\]

特征值为：

\[
\boxed{
\lambda_+=\varphi,
\qquad
\lambda_-=-\varphi^{-1}.
}
\]

若初始计数向量为 \(v_0\)，则：

\[
v_n=M_\varphi^nv_0.
\]

将 \(v_0\) 分解到两个特征方向：

\[
v_0=au_++bu_-,
\]

得到：

\[
\boxed{
v_n
=
a\varphi^nu_+
+
b(-\varphi^{-1})^nu_-.
}
\]

按主尺度归一化：

\[
\boxed{
\varphi^{-n}v_n
=
au_+
+
b(-1)^n\varphi^{-2n}u_-.
}
\]

所以离散整数替换的归一化余量按：

\[
\boxed{
\varphi^{-2n}
}
\]

指数收缩并交替翻转。

这给“黄金比例同时连续又离散”的严格解释：

\[
\boxed{
\text{离散替换矩阵}
\quad\text{拥有}\quad
\text{连续扩张特征方向与共轭收缩特征方向}.
}
\]

黄金比例不是唯一具有这种现象的代数单位，但它是最简单的二次 Pisot 单位模型之一。

---

## 35.15 黄金单位分割是跨尺度的精确守恒式

仓库 `GoldenPartition` 已证明，对每个 \(n\)：

\[
\boxed{
F_{n+1}\varphi^{-n}
+
F_n\varphi^{-(n+1)}
=
1.
}
\]

这可以读成两个相邻离散计数与两个相邻连续尺度的精确配对：

\[
\boxed{
\text{整数权重}
\times
\text{连续逆尺度}
=
\text{单位总量}.
}
\]

它不是渐近式，而是每层严格成立。

因此可以定义两项权重：

\[
p_n^{(L)}
=
F_{n+1}\varphi^{-n},
\]

\[
p_n^{(S)}
=
F_n\varphi^{-(n+1)},
\]

满足：

\[
p_n^{(L)}+p_n^{(S)}=1.
\]

这并不自动把它们解释成物理 Born 概率；它们首先是一个精确正分割。只有在额外给出状态、事件和操作解释后，才可以把该分割当作概率坐标。

---

## 35.16 Fibonacci 悬挂观察者

令 \(K_F\) 为 Fibonacci 双边子移位闭包，\(T\) 为左移。取 roof：

\[
r(\kappa)
=
\begin{cases}
\varphi,&\kappa_0=L,\\
1,&\kappa_0=S.
\end{cases}
\]

对应悬挂：

\[
\Sigma_F
=
(K_F\times\mathbb R)/{\sim}
\]

可以解释为带标记原点的一维 Fibonacci tiling hull。

此时：

\[
\boxed{
\begin{aligned}
\kappa
&=\text{离散双向 tile 地址},\\
s
&=\text{原点在当前 tile 内的连续位置},\\
\xi_0=[\kappa_0,s_0]
&=\text{带初始 tile 与叶内相位的观察者原点}.
\end{aligned}
}
\]

平移流连续移动原点；穿过 tile 边界时，符号地址离散移位。

所以：

\[
\boxed{
\text{观察者当前坐标}
=
\text{连续 tile 内相位}
+
\text{离散／Cantor tile 历史}.
}
\]

Fibonacci inflation 进一步把 tile 长度乘以 \(\varphi\)，同时按 \(\sigma\) 替换 tile 类型，从而把：

\[
\boxed{
\text{连续空间缩放}
}
\]

与：

\[
\boxed{
\text{离散符号替换}
}
\]

锁定在同一个重整化操作中。

---

## 35.17 黄金机械词：连续相位产生非周期离散事件

取无理斜率：

\[
\alpha=\varphi^{-2}.
\]

对初始相位 \(\theta\in\mathbb R\)，定义：

\[
\boxed{
w_n(\theta)
=
\lfloor\theta+(n+1)\alpha\rfloor
-
\lfloor\theta+n\alpha\rfloor.
}
\]

由于 \(0<\alpha<1\)，有：

\[
w_n(\theta)\in\{0,1\}.
\]

### 定理 35.10（有界余量事件计数）

对每个 \(N\ge1\)：

\[
\boxed{
\sum_{n=0}^{N-1}w_n(\theta)
=
\lfloor\theta+N\alpha\rfloor
-
\lfloor\theta\rfloor.
}
\]

从而：

\[
\boxed{
\left|
\sum_{n=0}^{N-1}w_n(\theta)
-
N\alpha
\right|
<1.
}
\]

#### 证明

求和望远镜：

\[
\sum_{n=0}^{N-1}
\left(
\lfloor\theta+(n+1)\alpha\rfloor
-
\lfloor\theta+n\alpha\rfloor
\right)
=
\lfloor\theta+N\alpha\rfloor-\lfloor\theta\rfloor.
\]

再利用任意实数 \(x\) 满足 \(x-1<\lfloor x\rfloor\le x\)。 \(\square\)

因此：

\[
\boxed{
\text{离散事件数}
=
\text{连续黄金斜率}\times N
+
\text{绝对值小于一个事件的余量}.
}
\]

这比“离散频率趋近连续比例”更强：误差不随 \(N\) 增长。

---

## 35.18 有限未来局部稳定，无限未来持续要求坐标 refinement

定义前 \(N\) 个符号所涉及的边界集合：

\[
B_N
=
\{-n\alpha\bmod1:0\le n\le N\}.
\]

### 命题 35.11（有限前缀局部常值）

若：

\[
\theta\notin B_N,
\]

则存在 \(\varepsilon_N(\theta)>0\)，使：

\[
|\theta'-\theta|_{\mathbb T}<\varepsilon_N(\theta)
\]

推出：

\[
\boxed{
w_n(\theta')=w_n(\theta)
\qquad
0\le n<N.
}
\]

#### 证明

每个 \(w_n\) 只在：

\[
\theta=-n\alpha
\quad\text{或}\quad
\theta=-(n+1)\alpha
\pmod1
\]

处改变。有限多个边界之外，到边界集合的距离为正；在该半径内所有相关 floor 分支保持不变。 \(\square\)

但因为 \(\alpha\) 无理，边界轨道：

\[
\{-n\alpha\bmod1:n\ge0\}
\]

在圆上稠密。

### 推论 35.12（无统一无限未来稳定半径）

对任意 \(\theta\) 和任意邻域 \(U\ni\theta\)，存在 \(\theta'\in U\) 与某个 \(n\) 使：

\[
w_n(\theta')\neq w_n(\theta).
\]

所以：

\[
\boxed{
\forall N<\infty,
\text{有限未来拥有局部稳定坐标精度};
}
\]

但：

\[
\boxed{
\text{整个无限未来一般没有正的统一稳定半径}.
}
\]

这不是指数混沌。底层圆旋转满足：

\[
d(R_\alpha^n\theta,R_\alpha^n\theta')
=
d(\theta,\theta')
\]

而不产生指数分离。未来符号分叉来自读出边界的稠密前像。

因此：

\[
\boxed{
\text{预测逃逸可以来自界面边界，而不来自底层动力学的不稳定。}
}
\]

---

## 35.19 黄金系统说明“离散非周期”不等于熵增

Sturmian／Fibonacci 符号系统的长度 \(N\) 因子复杂度为：

\[
\boxed{
p(N)=N+1.
}
\]

因此其拓扑熵为：

\[
h_{\mathrm{top}}
=
\lim_{N\to\infty}\frac1N\log p(N)
=
0.
\]

所以它同时具备：

\[
\boxed{
\text{离散}
+
\text{非周期}
+
\text{无限新前缀}
+
\text{零熵}.
}
\]

这对前文的熵解释是一个重要边界：

\[
\boxed{
\text{离散事件持续出现}
\not\Rightarrow
\text{每单位时间持续产生正熵}.
}
\]

观察者的离散记录可以是高度有序的几何编码，而不是随机噪声。

---

## 35.20 初始坐标是对角化得以类型化的条件之一

一般对角化需要一个评价表：

\[
E:A\times A\to Y.
\]

第一坐标表示描述者地址，第二坐标表示对象地址。对角映射：

\[
\delta_A(a)=(a,a)
\]

要求能够识别“描述者地址”和“被描述对象地址”中的同一个 \(a\)。

在未点化、完全对称的连续统中，没有规范理由选择某一点或某一地址作为“我”。锚点和坐标架提供了这种识别：

\[
\boxed{
\text{初始坐标使自坐标读取成为良定义操作。}
}
\]

但这并不消除对角逃逸。若 \(\tau:Y\to Y\) 无不动点，则：

\[
\Delta_\tau(E)(a)
=
\tau(E(a,a))
\]

仍不能出现在 \(E\) 的任一行中。

所以：

\[
\boxed{
\text{锚点使“自我指涉”可定义；
对角化证明同层自我描述仍不能穷尽。}
}
\]

观察者成为连续统，并不会让 Cantor–Lawvere 型不完备性消失。

---

## 35.21 连续叶上的离散对角读出需要界面

若 \(A\) 连通，\(Y\) 离散，并且：

\[
E:A\times A\to Y
\]

连续，则 \(A\times A\) 连通，故 \(E\) 必为常值。

因此非平凡离散自指表不可能同时是：

\[
\boxed{
\text{连通叶上的全局连续离散值函数}.
}
\]

它必须来自：

- 横截 Cantor 地址；
- clopen 有限分割；
- 阈值／界面；
- 非连续符号编码；
- 概率 effect 后的抽样；
- 或更高层的记录账本。

这与前文“连续空间不能通过非平凡连续确定映射直接产生离散标签”一致。

所以锚定连续统观察者的对角层应写成：

\[
\boxed{
\text{连续载体}
\longrightarrow
\text{横截／界面／记录地址}
\longrightarrow
\text{离散自评价}.
}
\]

---

## 35.22 观察者的五重闭包升级

本节定义：

\[
\boxed{
\mathbf{Cl}(\mathfrak O)
=
(
\mathrm{Cl}_{\mathrm{anchor}},
\mathrm{Cl}_{\mathrm{orbit}},
\mathrm{Cl}_{\mathrm{pred}},
\mathrm{Cl}_{\mathrm{lift}},
\mathrm{Cl}_{\mathrm{record}},
\mathrm{Cl}_{\mathrm{self}}
).
}
\]

其中：

\[
\mathrm{Cl}_{\mathrm{anchor}}
=
\text{初始原点与坐标架是否在转换中保持};
\]

\[
\mathrm{Cl}_{\mathrm{orbit}}
=
\text{初始点的轨道闭包生成多大的连续统};
\]

\[
\mathrm{Cl}_{\mathrm{pred}}
=
\text{为预测全部未来读出需补足哪些坐标};
\]

\[
\mathrm{Cl}_{\mathrm{lift}}
=
\text{为区分回归路径需补足哪些提升变量};
\]

\[
\mathrm{Cl}_{\mathrm{record}}
=
\text{哪些 cocycle／事件历史不能压成当前状态函数};
\]

\[
\mathrm{Cl}_{\mathrm{self}}
=
\text{同层自评价是否存在对角逃逸}.
\]

它们互不自动推出：

\[
\boxed{
\text{轨道稠密}
\not\Rightarrow
\text{读出层析完备};
}
\]

\[
\boxed{
\text{未来读出完备}
\not\Rightarrow
\text{路径提升完备};
}
\]

\[
\boxed{
\text{路径提升完备}
\not\Rightarrow
\text{记录可以删除};
}
\]

\[
\boxed{
\text{完整记录历史}
\not\Rightarrow
\text{同层自描述完备}.
}
\]

因此观察者没有一个单标量的“完整度”。

---

## 35.23 与量子观察者的关系

量子状态空间本身可以是连续凸集，测量结果却是有限离散标签。两者之间由 effect／投影与状态评价连接：

\[
p_i=\operatorname{Tr}(\rho E_i).
\]

这与本节的叶—横截结构有形式相似性：

\[
\text{连续状态}
\to
\text{有限读出}.
\]

但不能直接把量子测量结果识别为某个 Cantor 横截坐标。量子 contextuality、非交换可观测代数和复振幅相干具有额外结构。

本节提供的真正桥是：

\[
\boxed{
\text{观察者可以拥有连续状态载体，
同时通过有限上下文产生离散记录；
离散记录不要求观察者本体是离散对象。}
}
\]

而路径记忆扩展与量子记录账本都可使用 cocycle／skew-product 语言，但二者的物理解释不能混同。

---

## 35.24 与经济观察者的关系

经济状态、价格、库存和资产负债表可以连续变化；成交、结算、违约、margin call 和政策事件则具有离散边界。

numeraire 与初始财富给出经济坐标架，交易历史与合同账本保存路径依赖。两个具有相同当前价格和总量的系统，可能因债务网络或历史合同不同而具有不同未来。

所以经济观察者也可以写成：

\[
\boxed{
\text{连续价格／状态叶}
+
\text{离散合同／结算横截}
+
\text{初始 numeraire 与账本锚点}.
}
\]

但这不是说经济系统就是 solenoid 或 Fibonacci 悬挂。这里的共同点仅是“连续状态 + 离散事件 + 路径账本”的类型结构。

---

## 35.25 可能的新研究中心：锚定完成而非裸观察

成熟理论已经分别研究：

- 点化拓扑空间和点化动力系统；
- Cantor 最小系统及其悬挂；
- weak solenoid 与 matchbox manifold；
- substitution tiling hull；
- Sturmian／Fibonacci 编码；
- cocycle 与 cohomology；
- 覆盖空间、holonomy 和路径群胚；
- 对角化与固定点障碍。

候选的新贡献不应宣称这些单项首次出现，而应集中在以下统一对象：

\[
\boxed{
\text{锚定连续统}
+
\text{有限读出商}
+
\text{预测闭包}
+
\text{路径提升闭包}
+
\text{记录 cocycle}
+
\text{对角自描述审计}.
}
\]

特别值得形式化的定量问题是：

1. **坐标稳定半径**
   \[
   \varepsilon_N(\xi)
   =
   \text{保持前 }N\text{ 个事件不变的最大初始坐标半径};
   \]

2. **首次逃逸深度**
   \[
   \tau(\xi,\xi')
   =
   \min\{n:q(\Phi_n\xi)\neq q(\Phi_n\xi')\};
   \]

3. **提升余量**
   \[
   r_{\mathrm{lift}}
   =
   \text{当前状态无法恢复的 cocycle 类};
   \]

4. **锚定自然性缺陷**
   \[
   \partial_{\xi_0}(F)
   =
   d\bigl(
   F(\xi_0),
   \xi_0'
   \bigr);
   \]

5. **自描述缺陷**
   \[
   \partial^\Delta_O
   =
   Q_O\Delta-\Delta_O P_O.
   \]

这五个量分别测量有限预测、路径记忆、坐标运输与自指闭合，不能被单一熵或单一距离替代。

---

## 35.26 建议 Lean 形式化模块

建议按下列顺序推进。

1. `ConnectedDiscreteSubsingleton`
   \[
   \text{Connected }X\land\text{Discrete }X
   \Rightarrow
   \operatorname{Subsingleton}X.
   \]

2. `OrbitClosureIsContinuum`
   连续实流单轨道闭包的紧致连通性。

3. `MinimalFlowOrbitClosure`
   最小流中任意轨道闭包等于全空间。

4. `PointedConjugacy`
   点化动力系统共轭及其等价关系。

5. `SuspensionReturnDecomposition`
   \[
   \Phi_t[\kappa,s]=[T^n\kappa,s'].
   \]

6. `MinimalCantorSuspensionConnected`
   最小 Cantor 系统悬挂的连通性。

7. `ProfiniteReadoutInverseLimit`
   完整横截与有限离散商的逆极限关系。

8. `RecurrenceNoContinuousAge`
   无界回归排除连续绝对年龄函数。

9. `CocycleRecurrenceNotCoboundary`
   非消失回归 cocycle 排除连续势函数。

10. `GoldenMinkowskiScaling`
    \[
    (x,x')\mapsto(\varphi x,-\varphi^{-1}x').
    \]

11. `FibonacciSubstitutionSpectrum`
    \[
    \operatorname{spec}M_\varphi
    =
    \{\varphi,-\varphi^{-1}\}.
    \]

12. `NormalizedFibonacciResidual`
    \[
    \varphi^{-n}M_\varphi^nv
    =
    au_++b(-1)^n\varphi^{-2n}u_-.
    \]

13. `MechanicalWordTelescoping`
    \[
    \sum_{n<N}w_n
    =
    \lfloor\theta+N\alpha\rfloor-\lfloor\theta\rfloor.
    \]

14. `MechanicalWordDiscrepancy`
    \[
    \left|\sum_{n<N}w_n-N\alpha\right|<1.
    \]

15. `FinitePrefixLocallyConstant`
    远离有限边界集合时，长度 \(N\) 编码局部常值。

16. `AnchoredDiagonalTyping`
    锚点／地址识别如何诱导自坐标评价。

17. `ContinuousDiscreteDiagonalNoGo`
    连通定义域到离散值域的连续评价表只能常值。

其中 Sturmian 因子复杂度、完整 Fibonacci tiling hull 识别与一般 matchbox manifold 理论，应通过具名经典来源或后续独立形式化接入，不得作为无名公理使用。

---

## 35.27 最终统一式

本节把观察者从“连续统内部的一个对象”升级为：

\[
\boxed{
\text{观察者}
=
\text{连续统对自身选择初始原点以后，
沿动力学运输该原点关系并保存不可压缩历史的结构}.
}
\]

其连续性来自：

\[
\boxed{
\text{叶流、相位、尺度与状态的连续运输}.
}
\]

其离散性来自：

\[
\boxed{
\text{横截地址、有限同余、边界穿越、事件编号与账本记录}.
}
\]

其初始坐标来自：

\[
\boxed{
\text{点化}
+
\text{局部坐标架}
+
\text{路径提升归一化}.
}
\]

其记忆来自：

\[
\boxed{
\text{不能被当前状态函数吸收的 cocycle 类}.
}
\]

其黄金性质来自：

\[
\boxed{
\text{同一个整数代数操作在物理嵌入中扩张，
在共轭嵌入中翻转收缩，
并以 Fibonacci 离散替换实现连续尺度自相似}.
}
\]

其自我限制来自：

\[
\boxed{
\text{锚点使自坐标读取可定义，
但对角化仍证明同层自描述不能穷尽}.
}
\]

所以最凝练的结论是：

\[
\boxed{
\text{观察者不是连续统之外观看连续统的点；
观察者可以是连续统被点化、带架、提升并记忆以后形成的自相对结构}.
}
\]

以及：

\[
\boxed{
\text{“连续且离散”不是逻辑矛盾，
而是叶方向、横截方向、有限商和事件账本属于不同类型的陈述}.
}
\]

---

## 35.28 参考接口与严格非主张

参考接口：

- W. H. Gottschalk and G. A. Hedlund, *Topological Dynamics*, 1955.
- M. Barge and B. Diamond, substitution tiling spaces and inverse-limit models.
- L. Sadun, *Topology of Tiling Spaces*, 2008.
- M. Queffélec, *Substitution Dynamical Systems—Spectral Analysis*.
- J. Bellissard, D. Herrmann and M. Zarrouati, hulls of aperiodic solids and transversal structures.
- S. Hurder and collaborators, matchbox manifolds and weak solenoids.
- M. Lothaire, *Algebraic Combinatorics on Words*, Sturmian and mechanical words.
- 仓库接口：
  `D5/S1/Dynamics/UniversalSolenoid.lean`,
  `D5/S1/Solenoid/ExactSequence.lean`,
  `D5/S1/Solenoid/StreamlineDecomposition.lean`,
  `D5/S1/Solenoid/PathOrbitClassification.lean`,
  `D5/S1/Solenoid/RealFlowRecurrence.lean`,
  `D5/S1/Solenoid/ThroatTransitionCocycle.lean`,
  `D5/S1/Scale/MinkowskiModelSet.lean`,
  `D5/S1/Recurrence/GoldenPartition.lean`.

严格非主张：

1. 本节不声称一个非平凡空间可在同一拓扑下同时连通且离散。
2. 本节不把全不连通 Cantor 横截称为离散拓扑空间。
3. 本节不声称所有观察者都必须是 solenoid、悬挂流或 tiling hull。
4. 本节不把路径记忆等同于人类意识或心理记忆的完整理论。
5. 本节不从轨道稠密推出任何单个有限读出已经完备。
6. 本节不把当前状态回归解释成物理时间倒流。
7. 本节不把不可 coboundary 化的 cocycle 自动解释成主观自我。
8. 本节不把黄金比例视为连续—离散双结构的唯一代数来源。
9. 本节不把 Fibonacci 正分割自动解释成 Born 概率。
10. 本节不把 Sturmian 零熵解释成没有信息内容或没有无限新结构。
11. 本节不把有限前缀稳定解释成无限未来存在统一稳定半径。
12. 本节不把符号分叉解释成底层流的指数混沌。
13. 本节不把量子测量结果直接识别为 solenoid 的 profinite 横截。
14. 本节不把经济交易事件直接识别为 Fibonacci substitution。
15. 本节不声称锚点消除了 Cantor–Lawvere 型对角逃逸。
16. 本节新增定理均为纸面推导；未经 Lean kernel 验证不得标记为 `Closed`。


---

# 36. 追加：逆完成观察者本体、概念离散化与 RH 全局 section 障碍
## Inverse-Completion Observer Ontology, Conceptual Discretization, and the RH Global-Section Obstruction

### 36.0 文档地位、问题提升与承重边界

前文已经分别建立：

- 对角读取、扭曲逃逸、投影自然性与完成障碍；
- Hilbert 正交商余塔、目标余量、最小预测闭包与多轴观察者完备性；
- 量子上下文中的局部经典对角、余相干、互补坐标与全局拼接障碍；
- universal solenoid 中的有限圆坐标、隐藏 profinite 核、实流提升与路径账本；
- 经济学中的收益商、定价纤维、流动性余量与内生观察界面；
- 锚定连续统观察者的叶—横截结构、初始坐标、cocycle 记忆与黄金悬挂；
- Riemann 假设的 Cayley 径向缺陷、Li 正性、Nyman–Beurling 目标余量与 Weil 负方向接口。

本节把问题再提升一个层级。这里的“离散”不再只指离散拓扑、整数标签或有限结果，而指任何一次可命名、可区分、可类型化的概念选择：

\[
\boxed{
\text{凡是被选作一个坐标、对象、性质、定理、模型或观察接口的东西，
都已经对更深关系系统实施了一次区分。}
}
\]

因此，“连续统”这个概念本身也不是最终本体；它是某种关系系统在拓扑语言中的一个呈现。数学、量子力学、复平面、零点、概率、熵和观察者，同样可以被视为不同探针范畴中的呈现对象。

本节提出的数学模型是：

\[
\boxed{
\text{本体不是某个最后的巨大对象，
而是全部有限／局部呈现及其转换关系形成的逆完成对象。}
}
\]

更准确地说，本节采用 pro-object、逆系统、广义点、sheaf section、Hilbert 余量和对角自然性作为严格语言。它不声称标准数学已经证明存在一个超越所有表示的唯一“zeta 本体”，也不把哲学本体论冒充为既有定理。新增结果分成三类：

1. pro-category、逆极限、Hilbert 投影和 sheaf section 中的标准结构推论；
2. 将前文章节统一后的新定义与条件定理；
3. 关于 RH 缺陷全局 section 的研究纲领和明确未闭合接口。

本节全部新增内容仍为纸面数学；在 Lean proof term、依赖闭包、admission 与冻结收据齐备以前不得标记为 `Closed`。

---

## 36.1 “概念离散”不是“值域具有离散拓扑”

### 定义 36.1（拓扑离散）

拓扑空间 \(D\) 称为离散的，当且仅当每个单点集合 \(\{d\}\) 都是开集。

### 定义 36.2（呈现离散／概念切割）

设 \(X\) 为某个对象，\(D\) 为一个呈现对象。一个概念、坐标或观察探针是一个态射

\[
q:X\longrightarrow D.
\]

它诱导不可区分关系

\[
x\sim_q y
\iff
q(x)=q(y).
\]

称选择 \(q\) 的行为为一次呈现离散，因为它把所有可能关系中的一类关系单独命名，并把 \(X\) 按 \(q\) 的纤维切分。

这里 \(D\) 可以是：

\[
\{0,1\},
\quad
\mathbb Z,
\quad
\mathbb R,
\quad
\mathbb C,
\quad
\mathscr H,
\quad
\text{某个函数空间},
\]

所以呈现离散并不要求 \(D\) 具有离散拓扑。

### 原理 36.3（类型选择本身是一种离散）

一旦规定：

\[
q:X\to D,
\]

便同时规定了：

- 哪些差异被 \(q\) 保留；
- 哪些差异被 \(q\) 商掉；
- 哪种相等关系被允许；
- 哪些操作可以在 \(D\) 中表达；
- 哪些问题因类型不匹配而不可表达。

因此：

\[
\boxed{
\text{连续性是某个呈现内部的性质；
选择“这一呈现而非其他呈现”则是元层的离散。}
}
\]

本节以后使用“概念是离散的”时，默认指呈现离散，而不是拓扑离散。

---

## 36.2 pro-object：逆完成先于实际极限对象

设 \(\mathcal C\) 为一个范畴，\(I\) 为小的 cofiltered 范畴。

### 定义 36.4（pro-object）

一个 pro-object 是一个函子

\[
\mathbf X:I\longrightarrow\mathcal C.
\]

记其阶段对象为：

\[
X_i=\mathbf X(i).
\]

对箭头 \(j\to i\)，记遗忘或粗化映射为：

\[
p_{ji}:X_j\to X_i.
\]

pro-object 的本质不是预先存在的集合

\[
\varprojlim_iX_i,
\]

而是整个 cofiltered 图：

\[
\boxed{
\mathbf X=(X_i,p_{ji})_{i\in I}.
}
\]

即使 \(\mathcal C\) 中不存在相应极限，\(\mathbf X\) 仍然是良定义的 pro-object。

### 定义 36.5（pro-category 态射）

若：

\[
\mathbf X=(X_i)_{i\in I},
\qquad
\mathbf Y=(Y_j)_{j\in J},
\]

则：

\[
\boxed{
\operatorname{Hom}_{\operatorname{Pro}(\mathcal C)}
(\mathbf X,\mathbf Y)
=
\varprojlim_{j\in J}
\varinjlim_{i\in I}
\operatorname{Hom}_{\mathcal C}(X_i,Y_j).
}
\]

这个公式表明，pro-object 之间的映射并不是简单的逐层映射族；它允许先把源精化到足够细的阶段，再与目标的每个阶段兼容。

### 原理 36.6（逆完成本体）

本节把一个候选“本体”建模为 pro-object：

\[
\boxed{
\mathbf X=(X_i,p_{ji}),
}
\]

其中每个 \(X_i\) 是某个可表达、可计算或可观测层，而 bonding maps 记录：

\[
\text{更精细呈现}
\longrightarrow
\text{更粗呈现}
\]

所遗忘的信息。

这里“本体”不是额外躲在 \(\mathbf X\) 背后的神秘点；它就是全部阶段及其相容关系的 pro-isomorphism 类。

---

## 36.3 普通概念只需一个阶段，观察者锚点却必须贯穿全部阶段

令：

\[
c:\mathcal C\to\operatorname{Pro}(\mathcal C)
\]

为常值嵌入。

### 定理 36.7（概念—锚点非对称性）

对任意 pro-object \(\mathbf X=(X_i)\) 与普通对象 \(D,A\in\mathcal C\)，有：

\[
\boxed{
\operatorname{Hom}_{\operatorname{Pro}(\mathcal C)}
(\mathbf X,cD)
\cong
\varinjlim_i
\operatorname{Hom}_{\mathcal C}(X_i,D).
}
\]

以及：

\[
\boxed{
\operatorname{Hom}_{\operatorname{Pro}(\mathcal C)}
(cA,\mathbf X)
\cong
\varprojlim_i
\operatorname{Hom}_{\mathcal C}(A,X_i).
}
\]

#### 证明

第一式把目标 pro-object 取为只有一个阶段的常值对象 \(cD\)，代入定义 36.5，外层逆极限退化，得到：

\[
\varinjlim_i\operatorname{Hom}(X_i,D).
\]

第二式把源取为常值对象 \(cA\)，内层正向极限退化，得到：

\[
\varprojlim_i\operatorname{Hom}(A,X_i).
\]

\(\square\)

### 推论 36.8（每个普通概念在有限阶段出现）

任意普通读出：

\[
q:\mathbf X\to cD
\]

都由某个阶段的映射代表：

\[
q_i:X_i\to D.
\]

因此：

\[
\boxed{
\text{任何单一普通概念都只需要本体的某个阶段；
它不必、也通常不能同时读取全部阶段。}
}
\]

即使 \(D=\mathbb R\) 或 \(D=\mathbb C\) 是连续空间，作为对 \(\mathbf X\) 的普通概念，\(q\) 仍在某个有限呈现阶段被定义。

### 推论 36.9（观察者锚点是相容锥）

若 \(\mathcal C\) 有终对象 \(1\)，则 \(\mathbf X\) 的广义点为：

\[
\operatorname{Hom}_{\operatorname{Pro}(\mathcal C)}(c1,\mathbf X)
\cong
\varprojlim_i
\operatorname{Hom}_{\mathcal C}(1,X_i).
\]

所以一个观察者锚点不是某个单一 \(X_i\) 中的点，而是相容族：

\[
\boxed{
\mathbf o=(o_i)_{i\in I},
\qquad
p_{ji}(o_j)=o_i.
}
\]

这给出本节最核心的不对称：

\[
\boxed{
\begin{aligned}
\text{概念}
&=\text{从某个阶段出发的单一读出};\\
\text{观察者}
&=\text{贯穿全部阶段的相容广义点}.
\end{aligned}
}
\]

---

## 36.4 观察者是带锚 compatible cone，而不是底层集合中的一个点

### 定义 36.10（逆完成观察者）

一个逆完成观察者记为：

\[
\boxed{
\mathfrak O
=
(\mathbf X,\mathbf o,\mathcal P,\mathcal M,\Delta),
}
\]

其中：

\[
\begin{aligned}
\mathbf X
&=(X_i,p_{ji})
&&\text{为逆完成载体};\\
\mathbf o
&=(o_i)
&&\text{为相容锚点};\\
\mathcal P
&\subseteq\operatorname{Pro}(\mathcal C)/\mathbf X
&&\text{为允许的概念／探针族};\\
\mathcal M
&&&\text{为不能由当前阶段恢复的路径与转换账本};\\
\Delta
&&&\text{为对探针系统自身进行评价的对角操作}.
\end{aligned}
\]

这里 \(\mathbf o\) 满足：

\[
p_{ji}(o_j)=o_i.
\]

它把每一层中的“这里”绑定为同一个跨尺度观察者。

### 定义 36.11（局部观察者）

若不存在全局相容点 \(\mathbf o\)，但在覆盖或子图上存在局部相容锚点，则称其为局部观察者。

局部锚点之间可能由：

- group-valued cocycle；
- hidden-fiber transition；
- holonomy；
- gauge transformation；
- sheaf restriction；

连接。

所以：

\[
\boxed{
\text{观察者可以是全局 section，也可以只有局部 section 和转移 cocycle。}
}
\]

这与第 35 节的 solenoid 提升、隐藏核和 throat transition cocycle 一致，但本节不把所有逆完成观察者都等同于 solenoid。

---

## 36.5 “结构性无穷”是没有终端忠实阶段

### 定义 36.12（最终阶段）

若存在 \(i_\ast\in I\)，使 \(\mathbf X\) 在 pro-category 中等价于常值对象 \(cX_{i_\ast}\)，则称 \(\mathbf X\) 最终稳定或本质常值。

### 定义 36.13（结构性无穷）

若 \(\mathbf X\) 不本质常值，称其具有结构性无穷。

在集合型逆系统中，一个充分的非终止条件是：

\[
\boxed{
\forall i,\quad
\exists(j\to i)
\text{ 使 }p_{ji}\text{ 仍合并至少两个 }X_j\text{ 中的对象}.
}
\]

也就是说，没有任何阶段能够忠实替代以后全部 refinement。

因此：

\[
\boxed{
\infty
\neq
\text{一个无限大的坐标值};
}
\]

更适合本节的定义是：

\[
\boxed{
\infty
=
\text{不存在终端忠实概念层}.
}
\]

这与前文 Hilbert 投影塔中：

\[
\|I-P_n\|_{\mathrm{op}}=1
\]

对每个有限阶段成立、但 \(P_nx\to x\) 对每个固定 \(x\) 成立的现象同型。

---
## 36.6 候选整体到逆极限的实现映射

设 \(\mathcal C\) 中相应极限存在，并设另有一个候选整体对象 \(X\)，带相容投影：

\[
q_i:X\to X_i,
\qquad
p_{ji}q_j=q_i.
\]

这些投影诱导规范映射：

\[
\boxed{
\eta_X:
X\longrightarrow
\varprojlim_iX_i,
\qquad
x\longmapsto(q_i(x))_i.
}
\]

### 定义 36.14（分离缺陷）

集合情形中定义：

\[
K_{\mathrm{sep}}
=
\{(x,y)\in X^2:
q_i(x)=q_i(y)\ \forall i\}.
\]

若 \(X\) 为线性空间且 \(q_i\) 线性，则：

\[
\boxed{
K_{\mathrm{sep}}
=
\bigcap_i\ker q_i.
}
\]

若 \(K_{\mathrm{sep}}\neq0\)，全部已选概念联合起来仍无法区分某些整体差异。

### 定义 36.15（实现缺陷）

定义：

\[
\boxed{
D_{\mathrm{real}}
=
\left(
\varprojlim_iX_i
\right)
\setminus
\eta_X(X).
}
\]

其中的元素是形式上在每个阶段都相容、但不来自任何实际整体对象的坐标族。

### 定理 36.16（逆完成同构判据）

\(\eta_X\) 为同构，当且仅当：

1. 探针族联合分离 \(X\)；
2. 每个相容阶段族都由唯一的 \(x\in X\) 实现。

#### 证明

第一条件等价于 \(\eta_X\) 单射；第二条件等价于 \(\eta_X\) 满射。二者同时成立即为双射；在相应结构范畴中再验证结构保持，即得同构。 \(\square\)

因此最高层的闭合缺陷不是一个单一数值，而是：

\[
\boxed{
\text{候选整体与其全部概念坐标的逆完成不能建立同构}.
}
\]

---

## 36.7 Hilbert 完成说明“形式相容”仍可能缺少能量条件

设：

\[
S_1\subseteq S_2\subseteq\cdots
\]

为递增有限维 Hilbert 子空间，正交投影为：

\[
p_{n+1,n}:S_{n+1}\to S_n.
\]

一个形式相容族满足：

\[
p_{n+1,n}(x_{n+1})=x_n.
\]

普通集合逆极限允许所有这种族，但 Hilbert 向量只对应满足：

\[
\boxed{
\sup_n\|x_n\|<\infty
}
\]

的相容族。

等价地，正交增量：

\[
d_{n+1}=x_{n+1}-x_n
\]

必须满足：

\[
\boxed{
\sum_n\|d_n\|^2<\infty.
}
\]

所以：

\[
\boxed{
\text{坐标相容}
\not\Rightarrow
\text{对象可实现};
}
\]

还需要：

\[
\boxed{
\text{能量、范数、正性、可积性或其他 admissibility 条件}.
}
\]

这为 RH 的逆完成模型提供重要边界：所有有限层零点／Li／Weil 数据形式相容，仍不保证它们来自一个允许的全局算术对象。

---

## 36.8 Yoneda 探针观点：对象由其对全部探针的响应给出

对范畴 \(\mathcal C\)，Yoneda 嵌入把对象 \(X\) 送到：

\[
\boxed{
h_X:
\mathcal C^{\mathrm{op}}\to\mathbf{Set},
\qquad
P\longmapsto\operatorname{Hom}_{\mathcal C}(P,X).
}
\]

如果探针子范畴 \(\mathcal G\subseteq\mathcal C\) 足够稠密／生成，则 \(X\) 可以由限制 nerve：

\[
N_{\mathcal G}(X)
=
\left(
\operatorname{Hom}(G,X)
\right)_{G\in\mathcal G}
\]

重构。

### 原理 36.17（反应本体）

对象不必被理解为“所有坐标背后的一个裸点集”，而可以被理解为：

\[
\boxed{
\text{它对全部允许探针的响应，以及这些响应对探针态射的自然性}.
}
\]

但这需要证明 \(\mathcal G\) 是联合忠实、稠密或保守的；任意选择的一小组探针并不自动恢复对象。

因此“数学概念是本体的投影”要成为定理，必须给出：

\[
\boxed{
\text{探针范畴}
+
\text{转换律}
+
\text{联合忠实性}
+
\text{可实现性}.
}
\]

---

## 36.9 元对角：任何声称枚举全部概念的单一阶段都会逃逸

设某一阶段 \(X_i\) 声称编码全部同类型读出：

\[
e:X_i\to Y^{X_i}.
\]

设：

\[
\tau:Y\to Y
\]

无不动点。定义：

\[
d(x)=\tau(e(x)(x)).
\]

则：

\[
d\notin\operatorname{im}e.
\]

这仍是普通 Cantor–Lawvere 对角化。

### 定理 36.18（无终端自描述坐标）

若某一普通阶段同时声称：

1. 它忠实表示整个 pro-object；
2. 它枚举全部从该阶段到 \(Y\) 的同类型概念；
3. 这些概念包括对该枚举本身的评价；
4. \(Y\) 上存在无不动点扭曲；

则该阶段不可能闭合。

#### 证明

由条件 2–4 构造上述对角函数 \(d\)，它逃出枚举；与条件 1–2 的完备声称矛盾。 \(\square\)

因此：

\[
\boxed{
\text{对角化不是“连续统存在”本身的后果，
而是某一离散呈现声称包含自身全部同类型呈现时的逃逸。}
}
\]

在最高抽象层面，普通闭合障碍与对角障碍都属于“单一呈现不能替代逆完成本体”；但在具体数学层，它们仍由不同定理实现。

---

## 36.10 解析延拓同时具有 Ind 与 Pro 两个方向

设 \(\mathcal U\) 为定义域按包含关系形成的 filtered 系统。对每个定义域 \(U\)，再设 \(R_U\) 为局部精度、jet 阶数、测试函数、谱截断或计算分辨率形成的 cofiltered 系统。

于是一个“持续解析延拓并持续精化”的对象更接近：

\[
\boxed{
\mathfrak F
=
\underset{U\in\mathcal U}{\operatorname{``colim"}}
\;
\underset{r\in R_U}{\operatorname{``lim"}}
F_{U,r}.
}
\]

即：

\[
\mathfrak F
\in
\operatorname{Ind}
\left(
\operatorname{Pro}(\mathcal C)
\right).
\]

其中：

\[
\begin{aligned}
\operatorname{Ind}\text{ 方向}
&=\text{扩张定义域、加入更多局部图};\\
\operatorname{Pro}\text{ 方向}
&=\text{提高每个局部图中的分辨率与相容约束}.
\end{aligned}
\]

标准复分析已经把 \(\zeta\) 从 \(\Re s>1\) 的 Dirichlet 级数延拓为复平面上的亚纯函数。该亚纯函数是一个完整、合法的标准数学对象。

本节额外提出的“zeta 本体”假设是：

\[
\boxed{
\text{复平面亚纯函数仍可能只是一个更大的 Ind–Pro 观察对象的一个表示函子值}.
}
\]

这不是标准 RH 的前提，也不是已证明事实；它是用于组织不同等价判据与观察接口的候选研究结构。

---

## 36.11 zeta 缺陷观察图册

记一个候选 zeta 逆完成对象为：

\[
\mathfrak Z.
\]

定义观察图册索引范畴：

\[
\mathcal J_{\mathrm{RH}}.
\]

其对象可包括：

\[
\boxed{
\begin{aligned}
\mathsf C
&=\text{复平面／亚纯函数图};\\
\mathsf{Div}
&=\text{零点—极点 divisor 图};\\
\mathsf{Cay}
&=\text{Cayley 相位—径向图};\\
\mathsf{Li}
&=\text{Li 系数图};\\
\mathsf{NB}
&=\text{Nyman--Beurling Hilbert 余量图};\\
\mathsf{W}
&=\text{Weil 二次型图};\\
\mathsf P
&=\text{素数显式公式误差图};\\
\mathsf S
&=\text{谱／共振图}.
\end{aligned}
}
\]

对每个图 \(j\)，设观察对象为：

\[
D_j,
\]

临界／闭合子对象为：

\[
C_j\subseteq D_j.
\]

定义点化缺陷对象：

\[
\boxed{
\overline D_j
=
D_j/C_j.
}
\]

这里 \(D_j/C_j\) 可以是：

- 线性商；
- pointed topological quotient；
- 正锥商；
- 二次型负部；
- 条件定义的状态空间；

不能假定所有图都属于同一个简单范畴。

### 定义 36.19（RH 缺陷图册）

RH 缺陷图册是：

\[
\boxed{
\mathfrak D_{\mathrm{RH}}
=
\left(
\mathcal J_{\mathrm{RH}},
\{\overline D_j\},
\{\text{transition/correspondence data}\}
\right).
}
\]

若各图之间存在真正的函数型转换，则可形成逆系统。若只有局部对应、关系或多值变换，则应使用 fibered category、stack 或 correspondence category，而不是强行写成普通集合逆极限。

---

## 36.12 离线零点不是图册中的一个点，而是一个相容 section

### 定义 36.20（离线缺陷 section）

一个离线缺陷 section 是一族：

\[
\boxed{
\delta
=
(\delta_j)_{j\in\mathcal J_{\mathrm{RH}}},
}
\]

其中：

\[
\delta_j\in\overline D_j,
\]

并且在所有已定义的 transition、restriction 或 correspondence 下相容。

复平面图中的坐标满足：

\[
\delta_{\mathsf C}
=
[\rho],
\qquad
\Re\rho\neq\frac12.
\]

Cayley 图中的坐标为：

\[
\delta_{\mathsf{Cay}}
=
(\theta_\rho,\beta_\rho),
\qquad
\beta_\rho\neq0.
\]

但完整离线对象不是 \(\rho\) 或 \(\beta_\rho\) 单独之一，而是：

\[
\boxed{
\text{全部观察图中的相容非零 section}.
}
\]

### 定义 36.21（本体版 RH）

定义：

\[
\boxed{
\mathrm{RH}_{\mathrm{ont}}
\iff
\operatorname{Sect}_{\mathrm{off}}
(\mathfrak D_{\mathrm{RH}})
=
\varnothing.
}
\]

即不存在全局相容的非零离线缺陷 section。

标准 RH 只直接断言复平面图中不存在离线非平凡零点。本体版 RH 若要与标准 RH 等价，必须证明：

1. 任意标准离线零点可唯一提升为全局缺陷 section；
2. 任意全局缺陷 section 在复平面图中产生标准离线零点。

这两个提升／下降定理目前不是既有结果，必须作为研究目标，而不能直接假设。

---

## 36.13 假设标准 RH 为假时，各观察图的必要异常

假设存在：

\[
\rho=\frac12+\delta+i\gamma,
\qquad
\delta\neq0.
\]

则在经典等价判据的适当定义域中，至少出现以下异常读出。

### 复平面图

\[
\boxed{
\Re\rho-\frac12=\delta\neq0.
}
\]

### Cayley 图

定义：

\[
C(\rho)=1-\frac1\rho=e^{\beta_\rho+i\theta_\rho}.
\]

则：

\[
\boxed{
\beta_\rho
=
\log|C(\rho)|
\neq0.
}
\]

函数方程镜像使：

\[
\beta_{1-\overline\rho}
=
-\beta_\rho.
\]

### divisor／局部提升图

若零点重数为 \(m_\rho\)，则：

\[
\boxed{
m_\rho
=
\frac1{2\pi i}
\oint
\frac{\xi'(s)}{\xi(s)}\,ds
\in\mathbb N_{>0}.
}
\]

\(\log\xi\) 的提升在绕行后改变：

\[
L\mapsto L+2\pi i m_\rho.
\]

所以局部观察者同时携带：

\[
\mathbb Z\text{ 绕数}
\quad\text{和}\quad
\mathbb Z_2\text{ 镜像侧别}.
\]

### Li 图

Li 判据要求：

\[
\lambda_n\ge0
\qquad
\forall n\ge1.
\]

若 RH 为假，则存在：

\[
\boxed{
n,\qquad
\lambda_n<0.
}
\]

### Nyman–Beurling 图

设：

\[
\mathcal M_{\mathrm{NB}}
=
\overline{
\operatorname{span}
\left\{
\left\{\frac1{nx}\right\}:n\ge1
\right\}
}
\subseteq L^2(0,\infty),
\]

\[
\chi=\mathbf1_{(0,1)}.
\]

则：

\[
\boxed{
r_{\mathrm{NB}}
=
(I-P_{\mathcal M_{\mathrm{NB}}})\chi
\neq0.
}
\]

### Weil 图

在正确测试函数域和闭合二次型实现中，存在：

\[
\boxed{
f,\qquad
Q_W(f)<0.
}
\]

### 素数图

显式公式中，离线零点产生归一化模式：

\[
\boxed{
e^{(\rho-\frac12)t}
=
e^{\delta t}e^{i\gamma t}.
}
\]

其中 \(\delta>0\) 的成员给出超临界增长指数，镜像成员给出衰减指数。

这些异常具有同一零集合意义，但目前不能无条件把它们视为同一向量的线性坐标。

---

## 36.14 “同一个缺陷”的严格含义分为三层

### 第一层：共同零集合

定义适当非负缺陷量：

\[
d_{\mathsf{Cay}},
\quad
d_{\mathsf{Li}},
\quad
d_{\mathsf{NB}},
\quad
d_{\mathsf W}.
\]

已知判据给出：

\[
\boxed{
d_{\mathsf{Cay}}=0
\iff
d_{\mathsf{Li}}=0
\iff
d_{\mathsf{NB}}=0
\iff
d_{\mathsf W}=0
\iff
\mathrm{RH}.
}
\]

这是当前最稳固的统一：不同观察量识别同一个闭合状态。

### 第二层：共同来源对象

若能构造 \(\mathfrak D_{\mathrm{RH}}\) 和观察函子：

\[
Q_j:
\mathfrak D_{\mathrm{RH}}\to\overline D_j,
\]

使：

\[
Q_j(\delta)=\delta_j,
\]

则不同判据成为同一个缺陷对象的不同表示。

这一步目前是待构造的本体层桥。

### 第三层：定量层析等价

若还能证明 frame 型不等式：

\[
\boxed{
c\|\delta\|^2
\le
\sum_jw_j\|Q_j\delta\|_j^2
\le
C\|\delta\|^2,
}
\]

则观察图册不仅共同识别零点，还能定量重构缺陷大小。

这是比逻辑等价强得多的新研究目标。

---

## 36.15 有限非空逆系统的紧致性障碍

本节现在得到一个对“所有概念都是离散有限投影”非常关键的限制。

### 定理 36.22（有限非空 cofiltered 逆极限非空）

设：

\[
\mathbf S:I\to\mathbf{Set}
\]

为 cofiltered 图，并且每个 \(S_i\) 都是非空有限集合。则：

\[
\boxed{
\varprojlim_iS_i\neq\varnothing.
}
\]

#### 证明概要

考虑所有由非空子集 \(T_i\subseteq S_i\) 构成、且在 transition 下稳定的子系统。由有限性，任意全序下降链的逐坐标交仍非空，故用 Zorn 引理取得极小子系统。极小性迫使其 transition 均满射，并进一步迫使每个 \(T_i\) 为单点。这些单点构成相容 section。 \(\square\)

### 推论 36.23（纯有限离散 refinement 不会自动消灭反例）

设每个阶段都有稳定的离线候选集合：

\[
O_i\subseteq D_i,
\]

满足：

\[
O_i\neq\varnothing,
\]

且 transition 将 \(O_j\) 映入 \(O_i\)。若所有 \(O_i\) 有限且索引图 cofiltered，则：

\[
\boxed{
\varprojlim_iO_i\neq\varnothing.
}
\]

因此：

\[
\boxed{
\text{如果每个有限离散概念层都允许某个离线候选，
且这些候选形成真正的有限 cofiltered 逆系统，
那么逆完成反而保证存在全局离线 section。}
}
\]

这是本节最重要的反直觉结论之一。

仅仅把所有概念视为有限离散投影，不能自动证明 RH；在上述条件下，它甚至支持全局 section 的存在。

---

## 36.16 要排除离线 section，至少必须破坏一种紧致性条件

若目标是证明：

\[
\operatorname{Sect}_{\mathrm{off}}
(\mathfrak D_{\mathrm{RH}})
=
\varnothing,
\]

则至少需要以下一种机制。

### 有限层空缺

存在某个有限阶段：

\[
O_i=\varnothing.
\]

这给出有限、显式、可核验的 RH 证书。

### 非紧致 admissibility

局部候选集合虽然非空，但合法对象还必须满足：

- 一致能量界；
- 平方可和；
- 正性；
- 可积性；
- 增长阶；
- Euler 乘积兼容；
- trace-class／form-domain 条件。

这些条件可能只在无限极限中失败。

### 非 cofiltered 上下文图

若观察图册是覆盖、上下文或多重交叠系统，而不是 cofiltered 逆系统，则局部非空不保证全局 section。

### transition 不保持“离线”子集

某些精化可能把粗层的离线候选拆成临界与非临界分支，或揭示其不能继续提升。

### 高阶 gluing 障碍

局部 section 在两两交叠上相容，但三重交叠或更高 cocycle 不可平凡化。

### derived inverse-limit 障碍

在线性／阿贝尔范畴中，普通 \(\varprojlim\) 不是正合函子；可能出现：

\[
\varprojlim{}^{1}
\]

等高阶余量，记录“每层可解但不能全局同时解”的障碍。

因此：

\[
\boxed{
\text{真正的证明力量不来自“每个概念都是离散的”，
而来自概念之间的相容律、admissibility 与高阶障碍。}
}
\]

---

## 36.17 普通逆极限与 sheaf 全局 section 不是同一个问题

设 \(\mathcal U\) 是一族观察上下文，\(\mathcal E\) 是一个 presheaf。每个上下文 \(U\) 有局部 section：

\[
s_U\in\mathcal E(U).
\]

全局 section 要求存在：

\[
s\in\mathcal E(X)
\]

使所有限制都等于 \(s_U\)。

局部 section 全部存在，并不保证它们能全局拼接。

量子 contextuality 的 sheaf 表述正是：

\[
\boxed{
\text{每个交换测量上下文都有局部经典赋值，
但不存在统一的上下文无关全局 section。}
}
\]

这与定理 36.22 不矛盾，因为测量上下文图不是简单的有限非空 cofiltered 逆系统；其核心是覆盖交叠和兼容关系。

### 原理 36.24（RH 图册不能被预先假定成普通逆系统）

若 Li、Nyman、Weil、复平面和素数图之间没有已经构造的函数型 bonding maps，则不能直接使用：

\[
\varprojlim_jD_j.
\]

更准确的对象可能是：

- presheaf；
- stack；
- fibered category；
- correspondence diagram；
- derived diagram。

只有在明确类型以后，“不存在全局离线 section”才成为可证明命题。

---

## 36.18 闭合缺陷的七轴分类

本节定义：

\[
\boxed{
\mathbf O_{\mathrm{closure}}
=
(
O_{\mathrm{sep}},
O_{\mathrm{real}},
O_{\mathrm{glue}},
O_{\mathrm{adm}},
O_{\mathrm{pos}},
O_{\mathrm{diag}},
O_{\mathrm{der}}
).
}
\]

其中：

\[
O_{\mathrm{sep}}
=
\text{全部探针仍无法分离的对象差异};
\]

\[
O_{\mathrm{real}}
=
\text{形式相容但没有实际实现的坐标族};
\]

\[
O_{\mathrm{glue}}
=
\text{局部 section 无法全局拼接的 cocycle};
\]

\[
O_{\mathrm{adm}}
=
\text{能量、可积性、增长与正锥条件的极限失败};
\]

\[
O_{\mathrm{pos}}
=
\text{正性二次型中的负方向};
\]

\[
O_{\mathrm{diag}}
=
\text{自描述枚举中的对角逃逸};
\]

\[
O_{\mathrm{der}}
=
\text{普通极限未捕获的高阶 }\varprojlim{}^k\text{ 障碍}.
\]

这些缺陷在最高抽象层都属于“单一呈现未能成为完整本体”，但在具体数学中不可互换。

---

## 36.19 Hilbert 图中的唯一最小目标完成

设 \(\mathscr H\) 为 Hilbert 空间，\(M\subseteq\mathscr H\) 为闭子空间，目标为 \(x\in\mathscr H\)。

定义：

\[
r=(I-P_M)x.
\]

于是：

\[
x=P_Mx+r,
\qquad
r\perp M.
\]

### 定理 36.25（唯一最小完成）

唯一最小的包含 \(M\) 和 \(x\) 的闭子空间是：

\[
\boxed{
M_\ast
=
M\oplus\operatorname{span}\{r\}.
}
\]

若 \(r\neq0\)，则：

\[
\dim(M_\ast/M)=1.
\]

#### 证明

任何包含 \(M\) 和 \(x\) 的闭子空间 \(N\) 也包含：

\[
x-P_Mx=r.
\]

故：

\[
M\oplus\operatorname{span}\{r\}
\subseteq N.
\]

另一方面 \(M_\ast\) 显然包含 \(M\) 与 \(x\)。 \(\square\)

### 定理 36.26（最小作用路径）

在所有绝对连续路径：

\[
\gamma:[0,1]\to\mathscr H,
\qquad
\gamma(0)\in M,
\quad
\gamma(1)=x
\]

中，作用量：

\[
\mathcal S[\gamma]
=
\frac12\int_0^1\|\dot\gamma(t)\|^2dt
\]

的唯一最小值为：

\[
\boxed{
\mathcal S_{\min}
=
\frac12\|r\|^2.
}
\]

唯一极小路径为：

\[
\boxed{
\gamma_\ast(t)
=
P_Mx+tr.
}
\]

#### 证明

Cauchy–Schwarz 给出：

\[
\int_0^1\|\dot\gamma(t)\|^2dt
\ge
\left\|
\int_0^1\dot\gamma(t)dt
\right\|^2
=
\|x-\gamma(0)\|^2
\ge
\|r\|^2.
\]

等号要求 \(\dot\gamma\) 恒定且 \(\gamma(0)=P_Mx\)，故得到唯一极小路径。 \(\square\)

---

## 36.20 余量—观察者对偶

Hilbert 空间的 Riesz 表示把向量 \(r\) 与连续线性观察函数：

\[
\ell_r(y)=\langle r,y\rangle
\]

规范识别。

由于 \(r\perp M\)，有：

\[
\ell_r(m)=0
\qquad
\forall m\in M.
\]

但：

\[
\ell_r(x)
=
\|r\|^2.
\]

### 定理 36.27（规范最强分离观察者）

若 \(r\neq0\)，则：

\[
\widehat r=\frac r{\|r\|}
\]

唯一达到：

\[
\boxed{
\sup_{
g\in M^\perp,\ \|g\|\le1
}
|\langle g,x\rangle|
=
\|r\|.
}
\]

因此同一个 \(r\) 同时是：

\[
\boxed{
\begin{aligned}
r
&=\text{目标的闭合缺陷};\\
r
&=\text{唯一最小新坐标};\\
r
&=\text{最小作用方向};\\
\ell_r
&=\text{对原空间失明、对目标最敏感的观察者}.
\end{aligned}
}
\]

这解释了前文“闭合缺陷本身成为观察者”的精确 Hilbert 含义。

在一般 Banach 空间中，Hahn–Banach 可以给出分离泛函，但通常没有 Hilbert 正交代表的规范唯一性。

---

## 36.21 Nyman–Beurling 图中的 rank–action 双量

取：

\[
\mathscr H=L^2(0,\infty),
\quad
M=\mathcal M_{\mathrm{NB}},
\quad
x=\chi.
\]

定义：

\[
r_{\mathrm{RH}}
=
(I-P_M)\chi.
\]

则：

\[
\boxed{
\mathrm{RH}
\iff
r_{\mathrm{RH}}=0.
}
\]

若 RH 为假：

\[
r_{\mathrm{RH}}\neq0,
\]

且对固定目标 \(\chi\) 的唯一最小完成是：

\[
M\oplus\mathbb C r_{\mathrm{RH}}.
\]

定义：

\[
Q_{\mathrm{RH}}
=
\text{投影到 }\mathbb C r_{\mathrm{RH}}.
\]

则得到连续—离散双量：

\[
\boxed{
\left(
\operatorname{rank}Q_{\mathrm{RH}},
\,
\mathcal S_{\mathrm{RH}}
\right)
=
\left(
\operatorname{rank}Q_{\mathrm{RH}},
\,
\frac12\|r_{\mathrm{RH}}\|^2
\right).
}
\]

若 RH 真：

\[
(0,0).
\]

若 RH 假：

\[
(1,a),
\qquad
a>0.
\]

这里 rank 是离散的，作用量是连续的。

必须强调：

\[
\boxed{
\dim(M_\ast/M)=1
}
\]

只表示固定目标 \(\chi\) 需要一个新商方向，不表示离线零点只有一个，也不表示完整 RH 缺陷空间是一维。

---

## 36.22 图册之间的作用量一致性

设每个 Hilbert 型观察图 \(j\) 带有：

\[
(\mathscr H_j,M_j,x_j),
\]

余量为：

\[
r_j=(I-P_{M_j})x_j.
\]

设 transition：

\[
T_{kj}:\mathscr H_k\to\mathscr H_j
\]

满足：

\[
T_{kj}(M_k)\subseteq M_j,
\]

\[
T_{kj}x_k-x_j\in M_j.
\]

于是它在商空间上诱导：

\[
\overline T_{kj}:
\mathscr H_k/M_k
\to
\mathscr H_j/M_j.
\]

### 命题 36.28（商类相容）

有：

\[
\boxed{
\overline T_{kj}[x_k]
=
[x_j].
}
\]

如果 \(\overline T_{kj}\) 为等距同构，则：

\[
\boxed{
\|r_k\|
=
\|r_j\|.
}
\]

因此最小作用量：

\[
\frac12\|r_j\|^2
\]

在图册转换下不变。

这提供一个研究标准：

\[
\boxed{
\text{若 Cayley、Li、Nyman、Weil 图真的表示同一个缺陷，
应寻找它们商缺陷范数之间的等距、frame 或受控失真关系。}
}
\]

仅有共同零集合还不足以给出作用量一致性。

---

## 36.23 保持目标的严格收缩会消灭全局缺陷

### 定理 36.29（商空间收缩刚性）

设 \(M\subseteq\mathscr H\) 闭，\(x\in\mathscr H\)，且有界线性算子：

\[
R:\mathscr H\to\mathscr H
\]

满足：

\[
R(M)\subseteq M,
\]

\[
Rx-x\in M.
\]

令：

\[
\overline R:\mathscr H/M\to\mathscr H/M
\]

为诱导算子。若：

\[
\boxed{
\|\overline R\|<1,
}
\]

则：

\[
\boxed{
x\in M.
}
\]

#### 证明

在商中：

\[
\overline R[x]=[x].
\]

所以：

\[
\|[x]\|
=
\|\overline R[x]\|
\le
\|\overline R\|\|[x]\|.
\]

严格收缩迫使 \(\|[x]\|=0\)。 \(\square\)

### 经济／作用量解释

\([x]\) 是现有结构无法吸收的目标，\(\|[x]\|\) 是最小完成成本。若 \(R\) 保持同一目标商类，却严格降低所有非零余量成本，则非零最低成本不可能存在。

### RH 条件路线

若能在 Nyman–Beurling 商上构造算术算子 \(R\)，满足：

\[
R(\mathcal M_{\mathrm{NB}})
\subseteq
\mathcal M_{\mathrm{NB}},
\]

\[
R\chi-\chi
\in
\mathcal M_{\mathrm{NB}},
\]

\[
\|\overline R\|<1,
\]

则立即得到 RH。

本节没有构造这种算子；该存在性是实质问题。

---

## 36.24 全局 section 的收缩刚性

设 RH 缺陷图册中，每个 chart quotient \(\overline D_j\) 为范数空间，并有相容 section：

\[
\delta=(\delta_j).
\]

设有图册自同态：

\[
R=(R_j)
\]

满足 transition 自然性：

\[
p_{kj}R_k
=
R_jp_{kj}.
\]

若：

\[
R_j\delta_j=\delta_j
\qquad
\forall j,
\]

且存在一个对全局 section 联合忠实的 chart \(j_0\)，满足：

\[
\|R_{j_0}\|\le\kappa<1,
\]

则：

\[
\delta_{j_0}=0.
\]

若 \(j_0\) 的零读出足以推出整个 section 为零，则：

\[
\boxed{
\delta=0.
}
\]

这给出本体版 RH 的一种条件证明模板：

\[
\boxed{
\text{构造保持离线缺陷 section 的自然重整化，
再证明它在忠实图中严格收缩。}
}
\]

---

## 36.25 镜像奇偶刚性

设 defect pro-object 上有对合：

\[
J^2=I.
\]

若同一个全局 section \(\delta\) 因目标自然性满足：

\[
J\delta=\delta,
\]

又因法向／侧别结构满足：

\[
J\delta=-\delta,
\]

则在特征不为 \(2\) 的线性环境中：

\[
\boxed{
\delta=0.
}
\]

这是另一种可能的 RH 刚性模板：

\[
\boxed{
\text{目标要求缺陷为偶，
镜像法向几何要求同一缺陷为奇，
故非零全局 section 不存在。}
}
\]

目前没有证明 Nyman 余量或共同 RH 缺陷 section 同时满足这两个条件；它仍是研究接口。

---

## 36.26 量子力学在该层级中的位置

量子系统的完整对象可由非交换可观测代数 \(\mathcal A\) 与状态 \(\omega\) 表示。每个交换子代数：

\[
C\subseteq\mathcal A
\]

提供一个局部经典图。

状态在该图中的概率读出为：

\[
\omega|_C.
\]

所以：

\[
\boxed{
\text{一个经典概率模型}
=
\text{量子对象在一个交换概念层中的投影}.
}
\]

量子 contextuality 表明，这些局部经典图一般不能拼成一个全局上下文无关经典 section。

在本节语言中：

\[
\boxed{
\text{量子性不是“存在离散结果”本身，
而是局部离散／经典呈现缺少一个统一全局经典完成。}
}
\]

这与 RH 缺陷图册共享“局部呈现—全局 section”骨架，但不是同一个定理：

- 量子 contextuality 的 section 是全局经典赋值；
- RH 的 section 是相容离线缺陷对象。

二者的索引范畴、transition 和 admissibility 完全不同。

---

## 36.27 数学理论本身作为探针子范畴

一个数学理论选择：

- 一套对象类型；
- 一套允许态射；
- 一套等价关系；
- 一套公理；
- 一套证明规则。

因此它可以被视为一个探针子范畴：

\[
\mathcal P\subseteq\mathcal C.
\]

理论对候选本体 \(\mathbf X\) 的读出是：

\[
\boxed{
N_{\mathcal P}(\mathbf X)
=
\left(
\operatorname{Hom}(P,\mathbf X)
\right)_{P\in\mathcal P}.
}
\]

若 \(\mathcal P\) 不联合忠实，则有本体差异永远不被该理论区分。

若 \(\mathcal P\) 不稠密，则形式读出未必能重构对象。

若理论试图在自身内部枚举全部同类型探针，则可能触发元对角逃逸。

所以：

\[
\boxed{
\text{数学不是本体的外部复制品；
数学是一族被类型化的探针及其证明相容性。}
}
\]

这是一种模型化解释，不是否定数学对象在其标准范畴中的客观性。

---

## 36.28 项目现有结构在逆完成语言中的统一

### universal solenoid

有限圆坐标及其 divisibility compatibility 形成具体逆完成；可见相位是一个普通投影，profinite 核是被该投影商掉的横截余量。

### 锚定连续统观察者

第 35 节的初始坐标：

\[
(r_0,k_0)
\]

现在可解释为：

- \(r_0\)：叶方向的局部提升；
- \(k_0\)：贯穿有限同余层的 compatible cone。

### 预测观察者

第 32 节 Heisenberg 可见空间：

\[
V_0\subseteq V_1\subseteq\cdots
\]

是概念空间的 filtered 扩张；其正交余：

\[
R_m=V_m^\perp
\]

是当前 probe family 尚未分离的状态方向。

### 量子 MUB 塔

每个对角代数是一个局部经典呈现；完整层析要求这些呈现联合忠实，但仍不等于存在全局经典赋值。

### 经济观察者

价格、numeraire、收益商、流动性路径和结算账本是不同经济 probe；aggregate 市值坐标不能替代 directed payment network 本体。

### RH 目标余量

Nyman–Beurling 余量是固定目标在一个 Hilbert chart 中的规范法向缺陷，而不是全部 zeta 本体的预先给定完整模型。

因此项目的独特统一可以写成：

\[
\boxed{
\text{局部坐标}
\to
\text{商余}
\to
\text{相容 refinement}
\to
\text{逆完成}
\to
\text{自描述对角审计}.
}
\]

---

## 36.29 假设 RH 为假的全局一致性审计

假设存在标准离线零点。要把它提升为本节的离线观察者 section，至少必须完成以下审计。

### 解析图相容

复平面零点、局部重数、函数方程四元轨道与解析延拓必须相容。

这一层单独不产生矛盾；离线四元因子可以满足实结构和函数方程对称。

### Cayley 图相容

有符号径向深度必须在镜像下反号：

\[
\beta\mapsto-\beta.
\]

### Li 图相容

完整零点集合必须产生至少一个负 Li 系数，而不是只验证某个局部四元贡献。

### Nyman 图相容

全部整数尺度生成闭包必须留下非零目标余量。

### Weil 图相容

必须存在属于正确 form domain 的负方向，并与显式公式的零点数据一致。

### 素数图相容

超临界模式必须在合法的平滑／截断显式公式中出现，而不是只作形式单项分析。

### transition 相容

必须构造上述异常之间的类型正确转换或共同来源对象。

### admissibility 相容

全局 section 必须同时满足：

- 增长阶；
- 正性；
- 共轭；
- Euler 乘积；
- 可积性；
- 正则化；
- 能量或 form-domain 条件。

当前知识只保证这些经典判据在“RH 成立／不成立”的逻辑层面等价；并未给出本节所要求的统一 defect atlas 与所有 transition。

因此：

\[
\boxed{
\text{假设 RH 为假在各单独经典图中是可表达的；
真正尚未检验的是这些图能否组成一个规范的全局离线本体 section。}
}
\]

---

## 36.30 本体 RH 研究计划

### 阶段一：建立 chart 类型

精确定义：

\[
D_{\mathsf C},
D_{\mathsf{Cay}},
D_{\mathsf{Li}},
D_{\mathsf{NB}},
D_{\mathsf W},
D_{\mathsf P},
D_{\mathsf S}.
\]

### 阶段二：定义临界子对象

对每个 chart 定义：

\[
C_j\subseteq D_j
\]

和 pointed quotient：

\[
\overline D_j=D_j/C_j.
\]

### 阶段三：构造 transition

优先构造已有经典桥：

\[
\text{零点}
\leftrightarrow
\text{Li};
\]

\[
\text{零点}
\leftrightarrow
\text{Weil 显式公式};
\]

\[
\text{Mellin}
\leftrightarrow
\text{Nyman--Beurling};
\]

\[
\text{零点}
\leftrightarrow
\text{素数误差}.
\]

需要明确这些桥是函数、关系、变换还是正则化极限。

### 阶段四：证明联合忠实性

证明：

\[
Q_j(\delta)=0
\quad
\forall j
\Longrightarrow
\delta=0.
\]

### 阶段五：识别 obstruction 类型

判断问题究竟属于：

- cofiltered inverse limit；
- sheaf global section；
- stack descent；
- form-core completion；
- derived \(\varprojlim^1\)；
- 非交换谱表示。

### 阶段六：寻找刚性

寻找：

\[
\text{严格收缩},
\quad
\text{奇偶冲突},
\quad
\text{正性冲突},
\quad
\text{有限层空缺},
\quad
\text{高阶 cocycle 非零}.
\]

只有这些附加结构，才能把“离线 section 的本体模型”推进为对 RH 真值的证明。

---

## 36.31 建议 Lean 形式化模块

建议按以下顺序进入 Lean。

1. `ProConceptFactorsThroughStage`

   对常值目标 \(D\)：

   \[
   \operatorname{Hom}_{\operatorname{Pro}(\mathcal C)}(\mathbf X,cD)
   \cong
   \varinjlim_i\operatorname{Hom}(X_i,D).
   \]

2. `ProGeneralizedPointAsCompatibleCone`

   \[
   \operatorname{Hom}(c1,\mathbf X)
   \cong
   \varprojlim_i\operatorname{Hom}(1,X_i).
   \]

3. `InverseCompletionSeparationKernel`

   线性观察塔中：

   \[
   K_{\mathrm{sep}}=\bigcap_i\ker q_i.
   \]

4. `InverseCompletionIsoIff`

   规范映射的单射／满射分解。

5. `BoundedHilbertCompatibleFamily`

   相容有限坐标族来自 Hilbert 向量当且仅当统一有界／平方可和。

6. `NoTerminalSelfEnumeratingProbe`

   普通阶段的 Cantor–Lawvere 对角逃逸。

7. `FiniteNonemptyCofilteredLimit`

   非空有限集合的 cofiltered 极限非空。

8. `OfflineFiniteSystemHasSection`

   稳定非空离线子系统存在全局 section。

9. `UniqueMinimalTargetCompletion`

   \[
   M_\ast=M\oplus\operatorname{span}\{r\}.
   \]

10. `MinimalCompletionAction`

    \[
    \inf_\gamma\frac12\int\|\dot\gamma\|^2
    =
    \frac12\|r\|^2.
    \]

11. `ResidualObserverDuality`

    归一化余量达到最大分离响应。

12. `QuotientContractionRigidity`

    \[
    \overline R[x]=[x],
    \quad
    \|\overline R\|<1
    \Rightarrow
    [x]=0.
    \]

13. `EvenOddDefectRigidity`

    \[
    Jd=d=-Jd
    \Rightarrow
    d=0.
    \]

14. `AtlasJointFaithfulness`

    抽象观察图册的联合零核判据。

15. `GlobalSectionNaturality`

    chart transition 下 compatible section 的定义与基本性质。

pro-category Hom 公式、sheaf global section、derived limit 与 Ind–Pro 对象应尽量复用 Mathlib／具名范畴论接口；若缺失，必须拆分为独立、可审计模块，不得以无名公理植入 RH 章节。

---

## 36.32 候选新贡献与成熟理论边界

以下内容属于成熟数学输入：

- pro-category 与 cofiltered diagram；
- Yoneda 嵌入和 dense probe 思想；
- 逆极限与有限非空紧致性；
- Ind–Pro／Tate objects；
- sheaf global section 与量子 contextuality；
- Hilbert 投影、Riesz 对偶和最小作用路径；
- Li、Nyman–Beurling、Weil 与显式公式判据；
- Connes 的 adèle class 非交换谱解释。

候选的新研究贡献不应宣称上述单项首次出现，而应集中在：

\[
\boxed{
\text{概念阶段因子化}
+
\text{观察者相容锚点}
+
\text{RH 多图缺陷 atlas}
+
\text{有限逆极限紧致性反约束}
+
\text{Hilbert 最小作用／观察者对偶}
+
\text{收缩或奇偶刚性}.
}
\]

尤其重要的新修正是：

\[
\boxed{
\text{“所有概念都是有限离散投影”
并不会自动使离线 section 消失；
在真正的有限非空 cofiltered 系统中，它反而保证 section 存在。}
}
\]

所以本体化不能停留在“概念是离散的”这一口号；必须识别 transition、admissibility 和高阶 obstruction。

---

## 36.33 最终统一式

本节得到：

\[
\boxed{
\text{概念}
=
\text{逆完成对象到普通呈现对象的一个有限阶段探针}.
}
\]

\[
\boxed{
\text{观察者}
=
\text{贯穿全部 refinement 阶段的带锚 compatible cone}.
}
\]

\[
\boxed{
\text{连续统}
=
\text{没有终端忠实呈现的逆完成结构，而不只是一个被命名的拓扑空间}.
}
\]

\[
\boxed{
\text{本体}
=
\text{阶段、遗忘映射、相容性与可实现性，而不是阶段背后的最后一个隐藏点}.
}
\]

\[
\boxed{
\text{闭合缺陷}
=
\text{候选整体与其全部概念坐标不能建立忠实、可实现、自封闭的同构}.
}
\]

\[
\boxed{
\text{对角化}
=
\text{某个普通概念层声称枚举自身全部同类型概念时的逃逸}.
}
\]

\[
\boxed{
\text{量子 contextuality}
=
\text{局部经典概念层缺少全局经典 section}.
}
\]

\[
\boxed{
\text{RH 的本体版本}
=
\text{是否存在贯穿复平面、Li、Nyman、Weil、素数与谱图的非零离线 section}.
}
\]

\[
\boxed{
\text{Nyman 余量}
=
\text{该问题在一个 Hilbert chart 中的规范最小目标缺陷与最强分离观察方向}.
}
\]

\[
\boxed{
\text{真正可能排除离线 section 的不是“离散投影”本身，
而是有限层空缺、非紧致 admissibility、gluing obstruction、正性、收缩或奇偶刚性}.
}
\]

最凝练的结论是：

\[
\boxed{
\text{复平面离线零点若存在，只是全局离线观察者 section 的一个坐标；
但在构造出全部 chart transition 以前，这个“全局 section”仍是研究对象而非既成事实。}
}
\]

以及：

\[
\boxed{
\text{现实／本体不是某个概念投影所指向的最后对象；
它是所有概念仍可持续 refinement、彼此相容，却不能被其中任一概念层替代的完成关系。}
}
\]

---

## 36.34 参考接口与严格非主张

参考接口：

- D. C. Isaksen, *Calculating limits and colimits in pro-categories*, 2001.
- O. Braunling, M. Groechenig and J. Wolfson, *Tate Objects in Exact Categories*, 2014.
- S. Mac Lane, *Categories for the Working Mathematician*, Yoneda and limits.
- The Stacks Project, Lemma 4.21.7 (`086J`), finite nonempty cofiltered limits.
- S. Abramsky and A. Brandenburger, *The Sheaf-Theoretic Structure of Non-Locality and Contextuality*, 2011.
- S. Abramsky, S. Mansfield and R. S. Barbosa, *The Cohomology of Non-Locality and Contextuality*, 2011.
- A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta function*, 1998.
- L. Báez-Duarte, strong Nyman–Beurling criteria.
- X.-J. Li, positivity criterion for RH.
- E. Bombieri and J. Lagarias, Li criteria and explicit formulas.
- 仓库统一论文 Sections 28–35 及其已列 Lean 接口。

严格非主张：

1. 本节不把呈现离散等同于离散拓扑。
2. 本节不声称每个连续对象都必然有 Cantor–Lawvere 对角缺陷。
3. 本节不声称 pro-object 必须在底层范畴中拥有实际逆极限。
4. 本节不声称某个具体 pro-presentation 是本体的唯一呈现。
5. 本节不声称标准复平面上的 \(\zeta\) 不是完整合法的亚纯函数对象。
6. 本节不声称已经构造出统一的 zeta／RH defect pro-object。
7. 本节不声称 Li、Nyman、Weil、Cayley 和素数误差是同一 Hilbert 向量。
8. 本节不声称这些判据之间已有规范等距 transition。
9. 本节不把量子 contextuality 与 RH 离线 section 障碍视为同一定理。
10. 本节不从局部异常读出直接推出一个已构造的全局离线 section。
11. 本节不从每个有限阶段非空推出 RH；定理 36.22 恰好说明有限 cofiltered 非空会支持全局 section。
12. 本节不把 Nyman 单目标完成的一维性解释为离线零点只有一个自由度。
13. 本节不声称存在保持 Nyman 目标商类的严格算术收缩。
14. 本节不声称镜像同时迫使共同 RH 缺陷既偶又奇。
15. 本节不把哲学“本体”一词作为 Lean 中未经定义的数学对象。
16. 本节不以本体化重述替代 RH 的解析证明义务。
17. 本节新增定理与统一结构均为纸面推导；未经 Lean kernel 验证不得标记为 `Closed`。

# 37. 追加：矩阵序观察者、记录正锥面、GNS 自配对与 RH 对角缺陷
## Matrix-Ordered Observers, Record Faces, GNS Self-Pairing, and the RH Diagonal Defect

本节继续第 31–36 节的统一工作，但修正一个过度压缩：

\[
\text{正锥}
\Longrightarrow
\text{正定度量}
\Longrightarrow
\text{酉性}
\Longrightarrow
\text{临界线}
\]

并不是项目当前真正提供的完整结构。仓库已经分别形式化了：

- 正、迹一矩阵对 \(X^\ast X\) 的 GNS 范数平方评价；
- 投影记录的 Born 权重、条件状态与 unread state；
- pinching／phase damping 的幂等性和固定代数；
- 环境记录 Gram 重叠对相干块的逐项选择；
- 记录复制、共同反转和遗漏一个记录副本时的恢复障碍；
- 观察读出与地址更新的交换子；
- 公开上下文估值的唯一下降；
- 有限投影上下文不存在全局经典二值答案表；
- 可分锥与 block-positive 对偶锥；
- 纠缠见证；
- Weil 卷积平方在临界线上的对角非负性；
- 离线四元轨道的交叉配对与能量界；
- prime-axis Hilbert 空间中的纵向酉群、横向收缩半群和 \(\ell^2\) 临界阈值。

这些结构共同说明：项目中的基本对象不是单个锥，而是一套同时携带

\[
\boxed{
\text{矩阵序}
+
\text{状态—问题配对}
+
\text{条件化仪器}
+
\text{环境记录}
+
\text{上下文拼接}
+
\text{预测闭包}
+
\text{GNS 完成}
}
\]

的观察者系统。

本节的中心命题是：

\[
\boxed{
\text{正锥不是本体本身；
它是判断一个形式坐标、商余类或逆完成 section
能否被实现为合法观察状态的门。}
}
\]

进一步地，临界线正性不应仅被理解为“某个算子可酉化”，而应被理解为：

\[
\boxed{
\text{反射后的平方测试仍然在同一观察纤维中自配对，
因而能够成为 GNS 范数平方。}
}
\]

离线零点则把该自配对拆成两个镜像观察纤维之间的交叉相干：

\[
\boxed{
\widehat g(\gamma)\,
\overline{\widehat g(\overline\gamma)}.
}
\]

该交叉项保持 Hermitian 实性，但不再自动具有范数平方的正性。

---

## 37.1 严格范围与真值状态

本节区分三类陈述。

### 第一类：仓库中已有的 Lean 真源

本节直接依赖以下已形式化结构：

1. 正、迹一矩阵的 GNS 范数平方恒等式；
2. record measurement 的权重和、conditional state、unread state 幂等性与固定块刻画；
3. 环境 record channel 的 Gram-overlap 形式与 fixed-block 选择；
4. pinching 的 Hilbert–Schmidt 自伴和幂等性；
5. 记录副本的共同相干反转及 surviving-copy obstruction；
6. 可分锥与 block-positive 锥的 Hilbert–Schmidt 对偶；
7. 公开上下文账本的唯一下降；
8. 有限投影构型对全局经典地址赋值的排除；
9. 卷积平方 Fourier–Laplace 变换在实频率上的模平方；
10. 临界线零点 summand 的逐项非负；
11. 离线四元轨道的实交叉配对；
12. prime-axis zeta Hilbert 空间和临界线多重刻画；
13. 有限观察塔的稳定与创新能递推。

### 第二类：本节给出的纸面定理

本节在有限维矩阵、闭凸锥和二地址离线扇区上证明：

- 正锥零权重的支撑面放大定理；
- 记录等价类的 fixed-algebra／center 分解；
- cone residual–witness 最小作用量定理；
- 离线四元轨道的交换签名分解；
- 离线评价像的维数—负方向判据；
- side-record／mirror-coherence 互补律；
- 正状态 section 与经典 character section 的严格类型分离；
- 矩阵序预测闭包的有限稳定；
- GNS 零范数传播与不定 isotropic 方向的区别；
- 逆完成中的 physical section 过滤。

### 第三类：明确保持开放的 RH 桥

本节不声称已经证明：

1. 素数账本自然产生一个完美的离线侧别记录；
2. 每个假想离线轨道都能被一个 Weil 测试函数独立局域化；
3. 离线评价映射对所有目标插值数据满射；
4. 其他零点、极点和 archimedean 项可以被同时压低；
5. zeta 显式公式泛函的全局正性已经由素数侧无条件证明；
6. 全部 RH 图表已经构成一个矩阵有序 pro-object；
7. 一个离线复平面零点必然提升为本节定义的全部 physical sections；
8. 本节已经证明 Riemann 假设。

所以本节的目标是：

\[
\boxed{
\text{把真正的缺口移动到一个类型正确、可形式化的位置。}
}
\]

---

## 37.2 矩阵序观察者

### 定义 37.1（矩阵序观察者）

有限维矩阵序观察者是数据：

\[
\boxed{
\mathfrak O
=
(
\mathcal A,
\{M_n(\mathcal A)_+\}_{n\ge1},
u,
\omega,
\mathcal S_O,
\mathbb E_O,
\{\mathcal I_r\}_{r\in R},
\alpha,
\mathcal M_O,
\Delta_O
).
}
\]

其中：

\[
\begin{aligned}
\mathcal A
&=\text{整体有限维 }C^\ast\text{-代数};\\
M_n(\mathcal A)_+
&=\text{加入 }n\text{ 维辅助系统后的正锥};\\
u
&=I\text{，即 order unit};\\
\omega
&=\text{正、归一化状态};\\
\mathcal S_O
&\subseteq\mathcal A\text{ 为观察者可访问的 operator system};\\
\mathbb E_O
&:\mathcal A\to\mathcal S_O\text{ 为粗粒化、pinching 或条件期望};\\
\mathcal I_r
&=\text{结果 }r\text{ 的完全正、迹不增 instrument 分支};\\
\alpha
&=\text{整体动力学};\\
\mathcal M_O
&=\text{结果、路径和环境副本的记录账本};\\
\Delta_O
&=\text{观察者对自身观察规则的同址评价}.
\end{aligned}
\]

这里 operator system 要求：

\[
I\in\mathcal S_O,
\qquad
A\in\mathcal S_O
\Longrightarrow
A^\ast\in\mathcal S_O,
\]

并对复线性组合封闭，但不必对乘法封闭。

因此：

\[
\boxed{
\text{观察者首先决定哪些问题能够被提出，
而不必已经拥有这些问题生成的全部操作代数。}
}
\]

### 定义 37.2（观察等价）

对两个状态 \(\rho,\sigma\)，定义：

\[
\boxed{
\rho\sim_O\sigma
\iff
\operatorname{Tr}((\rho-\sigma)E)=0
\quad
\forall E\in\mathcal S_O.
}
\]

令：

\[
N_O
=
\mathcal S_O^\perp
\]

为 Hilbert–Schmidt 正交余空间，则：

\[
\rho\sim_O\sigma
\iff
\rho-\sigma\in N_O.
\]

这只是线性不可区分关系。

### 定义 37.3（物理观察纤维）

对状态 \(\rho\)，定义：

\[
\boxed{
\operatorname{PhysFiber}_O(\rho)
=
(\rho+N_O)
\cap
\{\sigma\ge0,\ \operatorname{Tr}\sigma=1\}.
}
\]

所以：

\[
\boxed{
\text{线性余空间给出不可见方向；
正锥和归一化截面决定这些方向中哪些仍是可实现状态。}
}
\]

### 命题 37.4（有限维物理纤维）

在有限维情形，\(\operatorname{PhysFiber}_O(\rho)\) 是非空、紧、凸集合。

#### 证明

它至少包含 \(\rho\)，故非空。仿射空间 \(\rho+N_O\) 为闭集；PSD 锥为闭凸集；迹一超平面为闭仿射集。三者交仍闭凸。迹一 PSD 集在有限维中有界，故交集紧。 \(\square\)

这说明一个观察坐标通常对应一个完整的凸状态纤维，而不是唯一的“真实点”。

---

## 37.3 正性为什么必须提升为矩阵正性

### 定义 37.5（标量正性）

线性映射：

\[
\Phi:\mathcal A\to\mathcal B
\]

若满足：

\[
A\ge0
\Longrightarrow
\Phi(A)\ge0,
\]

称为正映射。

### 定义 37.6（完全正性）

若：

\[
\operatorname{id}_{M_n}\otimes\Phi
\]

对每个 \(n\ge1\) 都为正映射，则称 \(\Phi\) 完全正。

### 原理 37.7（扩展稳定性）

\[
\boxed{
\text{完全正性}
=
\text{观察规则在加入任意未读辅助系统后仍保持合法。}
}
\]

标量正性只审计当前观察层；完全正性同时审计所有有限矩阵放大：

\[
\boxed{
\mathcal A_+,
\quad
M_2(\mathcal A)_+,
\quad
M_3(\mathcal A)_+,
\quad\ldots
}
\]

因此项目的 inverse-completion 语言在量子层面的正确正性对象不是一只锥，而是矩阵锥塔：

\[
\boxed{
\mathbf C_{\mathcal A}
=
\{M_n(\mathcal A)_+\}_{n\ge1}.
}
\]

### 定义 37.8（矩阵级闭合缺陷）

对候选观察操作 \(\Delta\)，定义第 \(n\) 级正性缺陷：

\[
\boxed{
\partial^{\mathrm{cp}}_{O,n}(\Delta)
=
\sup_{\substack{X\in M_n(\mathcal S_O)_+\\ \|X\|\le1}}
\operatorname{dist}
\left(
(\operatorname{id}_n\otimes\Delta)(X),
M_n(\mathcal S_O)_+
\right).
}
\]

完全正闭合要求：

\[
\partial^{\mathrm{cp}}_{O,n}(\Delta)=0
\qquad
\forall n.
\]

因此：

\[
\boxed{
\partial^{\mathrm{cp}}_{O,1}=0
\not\Rightarrow
\partial^{\mathrm{cp}}_{O,n}=0
\quad
(n>1).
}
\]

这正是“当前投影层看起来可实现”与“所有扩展层都可实现”的差别。

---

## 37.4 状态—问题极性与 GNS 自配对

在完整矩阵代数上，PSD 锥相对于 Hilbert–Schmidt 配对自对偶：

\[
\boxed{
M_d(\mathbb C)_+^\vee
=
M_d(\mathbb C)_+.
}
\]

所以同一个正矩阵可以扮演两种角色：

\[
\begin{aligned}
\rho&=\text{状态};\\
E&=\text{effect}.
\end{aligned}
\]

Born 权重为：

\[
\boxed{
p(E\mid\rho)
=
\operatorname{Tr}(\rho E).
}
\]

但这不表示状态和问题在操作上相同。它只表示它们通过同一个正序和内积相互评价。

### 定理 37.9（矩阵 GNS 自配对）

设：

\[
\rho\ge0,
\qquad
\operatorname{Tr}\rho=1.
\]

则对任意矩阵 \(X\)：

\[
\boxed{
\operatorname{Tr}(\rho X^\ast X)
=
\|X\sqrt\rho\|_{\mathrm{HS}}^2
\ge0.
}
\]

仓库已经给出该恒等式的 Lean 证明。

这说明正状态的根本性质不是“所有坐标为正”，而是：

\[
\boxed{
\text{任何操作与自身的 }X^\ast X\text{ 配对都成为范数平方。}
}
\]

### 定义 37.10（自配对锥）

令 \(\mathcal T\) 为一个 \(\ast\)-空间，定义：

\[
\boxed{
\mathcal T_+
=
\left\{
\sum_{j=1}^m g_j^\ast g_j:
m<\infty
\right\}.
}
\]

线性泛函 \(\Omega\) 为正，当且仅当：

\[
\Omega(g^\ast g)\ge0
\qquad
\forall g.
\]

### 定理 37.11（GNS 零范数传播）

若 \(\Omega\) 为正泛函，且：

\[
\Omega(g^\ast g)=0,
\]

则：

\[
\boxed{
\Omega(h^\ast g)=0
\qquad
\forall h.
}
\]

#### 证明

由正泛函的 Cauchy–Schwarz 不等式：

\[
|\Omega(h^\ast g)|^2
\le
\Omega(g^\ast g)\Omega(h^\ast h)
=0.
\]

故交叉配对为零。 \(\square\)

因此零自范数方向可以一致商掉：

\[
N_\Omega
=
\{g:\Omega(g^\ast g)=0\}.
\]

而在不定 Hermitian 形式中，可能存在：

\[
[g,g]=0,
\qquad
[h,g]\neq0.
\]

所以：

\[
\boxed{
\text{Hilbert 正完成与不定完成的分界，
不是是否出现零向量，而是零自配对是否传播到全部交叉配对。}
}
\]

---

## 37.5 一条标量记录如何被正锥放大成一个支撑面

### 定理 37.12（零权重支撑面定理）

设：

\[
\rho\ge0,
\qquad
P=P^\ast=P^2.
\]

若：

\[
\operatorname{Tr}(\rho P)=0,
\]

则：

\[
\boxed{
P\rho=\rho P=0
}
\]

并且：

\[
\boxed{
\rho=(I-P)\rho(I-P).
}
\]

#### 证明

矩阵：

\[
\sqrt\rho P\sqrt\rho
\]

为 PSD，且其迹为：

\[
\operatorname{Tr}(\sqrt\rho P\sqrt\rho)
=
\operatorname{Tr}(\rho P)
=
0.
\]

PSD 矩阵迹为零只能为零，因此：

\[
\sqrt\rho P\sqrt\rho=0.
\]

于是：

\[
P\sqrt\rho=0,
\]

从而：

\[
P\rho=0,
\qquad
\rho P=0.
\]

最后得到支撑压缩式。 \(\square\)

### 推论 37.13（单位权重支撑面）

若：

\[
\operatorname{Tr}(\rho P)=1,
\qquad
\operatorname{Tr}\rho=1,
\]

则：

\[
\boxed{
\rho=P\rho P.
}
\]

#### 证明

对 \(I-P\) 应用定理 37.12。 \(\square\)

### 定义 37.14（暴露记录面）

定义：

\[
\boxed{
F_P
=
\left\{
\rho\ge0:
\operatorname{Tr}\rho=1,\ 
\rho=P\rho P
\right\}.
}
\]

确定结果 \(P=1\) 将状态空间压入 \(F_P\)。

若系统 Hilbert 维数为 \(d\)，而 \(P\) 的秩为 \(r\)，则全状态空间的实仿射维数为：

\[
d^2-1,
\]

而 \(F_P\) 的实仿射维数为：

\[
r^2-1.
\]

因此一个确定的标量记录最多一次排除：

\[
\boxed{
d^2-r^2
}
\]

个实自由度。

这给出：

\[
\boxed{
\text{正锥观察放大原理：
一个零／一概率记录可以强制整块支撑结构消失。}
}
\]

仓库的 conditioning 证明已经在具体矩阵接口中实现了：

\[
\text{recordWeight}=0
\Longrightarrow
P\rho P=0.
\]

记录相关单调性又进一步从 PSD 对角为零推出整列为零。

---

## 37.6 选择、记录与遗忘是三种不同的正序操作

设：

\[
\{P_r\}_{r\in R}
\]

为有限完备正交投影族：

\[
P_r^\ast=P_r,
\qquad
P_r^2=P_r,
\qquad
P_rP_s=0\ (r\neq s),
\qquad
\sum_rP_r=I.
\]

### 选择性分支

结果 \(r\) 的非归一化分支为：

\[
\mathcal I_r(\rho)=P_r\rho P_r.
\]

其权重为：

\[
p_r=\operatorname{Tr}(\rho P_r).
\]

若 \(p_r>0\)，条件状态为：

\[
\boxed{
\rho_r
=
\frac{P_r\rho P_r}{p_r}.
}
\]

这不是简单的“把向量投影一次”，而是：

\[
\boxed{
\text{从整个状态锥切换到暴露面 }F_{P_r}.
}
\]

### 保存结果

若记录寄存器具有正交标签 \(|r\rangle\)，保存结果后的经典—量子状态为：

\[
\boxed{
\rho_{RQ}
=
\sum_r
|r\rangle\langle r|
\otimes
P_r\rho P_r.
}
\]

这里结果标签 \(r\) 进入中心，而分支内部仍可保有非交换矩阵块。

### 丢弃结果

若只保留被测系统，得到 unread state：

\[
\boxed{
\mathbb E_P(\rho)
=
\sum_rP_r\rho P_r.
}
\]

仓库已经证明：

\[
\mathbb E_P^2=\mathbb E_P,
\]

并且：

\[
\boxed{
\mathbb E_P(\rho)=\rho
\iff
P_r\rho P_s=0
\quad
(r\neq s).
}
\]

所以：

\[
\boxed{
\begin{aligned}
\text{选择结果}
&=\text{暴露面选择};\\
\text{保存结果}
&=\text{中心标签扩张};\\
\text{丢弃结果}
&=\text{跨块相干商}.
\end{aligned}
}
\]

这三步具有不同的类型，不能都被一个“坍缩”词替代。

---

## 37.7 环境记录如何生成经典中心

设系统地址集合为有限集 \(I\)，每个地址 \(i\) 写入一个归一化环境记录向量：

\[
e_i\in\mathscr H_E,
\qquad
\|e_i\|=1.
\]

定义 Gram 重叠：

\[
G_{ij}
=
\langle e_j,e_i\rangle.
\]

约化 record channel 为：

\[
\boxed{
\Phi_G(\rho)_{ij}
=
G_{ij}\rho_{ij}.
}
\]

仓库已经证明其固定点满足：

\[
\Phi_G(\rho)=\rho
\iff
G_{ij}\neq1
\Longrightarrow
\rho_{ij}=0.
\]

### 定义 37.15（记录不可区分类）

定义：

\[
i\sim_Gj
\iff
G_{ij}=1.
\]

由于记录向量归一化，Cauchy–Schwarz 取等条件给出：

\[
G_{ij}=1
\iff
e_i=e_j.
\]

所以 \(\sim_G\) 是等价关系。

记其等价类分解为：

\[
I=\coprod_{\alpha\in\Lambda}I_\alpha.
\]

### 定理 37.16（记录 fixed algebra 分解）

record channel 的固定代数为：

\[
\boxed{
\operatorname{Fix}(\Phi_G)
\cong
\bigoplus_{\alpha\in\Lambda}
M_{|I_\alpha|}(\mathbb C).
}
\]

#### 证明

固定点条件要求：

\[
\rho_{ij}=0
\]

除非 \(G_{ij}=1\)，即 \(i,j\) 属于同一记录等价类。因此固定矩阵恰为按 \(I_\alpha\) 分块的块对角矩阵，每个块内不受限制。 \(\square\)

### 推论 37.17（记录中心）

其中心为：

\[
\boxed{
Z(\operatorname{Fix}(\Phi_G))
\cong
\bigoplus_{\alpha\in\Lambda}
\mathbb C\,I_{I_\alpha}.
}
\]

因此：

\[
\boxed{
\alpha
=
\text{环境能够稳定复制的经典记录标签},
}
\]

而：

\[
\boxed{
M_{|I_\alpha|}(\mathbb C)
=
\text{该标签内部仍未被环境分辨的量子自由度}.
}
\]

这给出三个极端。

### 无记录

若所有 \(e_i\) 相同，则只有一个等价类：

\[
\operatorname{Fix}(\Phi_G)
=
M_{|I|}(\mathbb C).
\]

没有产生新的经典中心。

### 完美地址记录

若所有 \(e_i\) 两两正交，则：

\[
G_{ij}=\delta_{ij},
\]

每个等价类为单点，因此：

\[
\operatorname{Fix}(\Phi_G)
\cong
\mathbb C^{|I|}.
\]

固定代数完全交换。

### 部分记录

若存在非平凡等价类，则：

\[
\operatorname{Fix}(\Phi_G)
=
\text{经典直和标签}
+
\text{标签内部量子矩阵块}.
\]

所以：

\[
\boxed{
\text{经典现实不是完整量子代数；
它是记录选择的不动代数的中心。}
}
\]

仓库在未记录的有限循环窗口中证明，零扰动 operational center 仅由常数函数组成。环境记录产生非平凡分区后，新的中心投影才成为可公开复制的事实。

---

## 37.8 side record 与 mirror coherence 的精确互补

考虑两个地址：

\[
|\mathrm R\rangle,
\qquad
|\mathrm L\rangle.
\]

环境分别写入归一化纯记录：

\[
|e_{\mathrm R}\rangle,
\qquad
|e_{\mathrm L}\rangle.
\]

定义记录重叠：

\[
c
=
\langle e_{\mathrm L},e_{\mathrm R}\rangle.
\]

系统的 off-diagonal 元素变为：

\[
\boxed{
\rho_{\mathrm{RL}}
\longmapsto
c\,\rho_{\mathrm{RL}}.
}
\]

所以相干保留率为：

\[
\boxed{
\mathcal V=|c|.
}
\]

对两个等先验纯记录，定义最优区分度：

\[
\boxed{
\mathcal D
=
\sqrt{1-|c|^2}.
}
\]

于是：

\[
\boxed{
\mathcal D^2+\mathcal V^2=1.
}
\]

### 定理 37.18（记录—相干互补）

在上述二地址纯记录模型中：

\[
\boxed{
\text{记录越能区分左右地址，
系统左右相干保留越少。}
}
\]

极端情况为：

\[
c=0
\Longrightarrow
\mathcal D=1,\ \mathcal V=0,
\]

以及：

\[
|c|=1
\Longrightarrow
\mathcal D=0,\ \mathcal V=1.
\]

因此：

\[
\boxed{
\text{完美记录侧别}
\Longrightarrow
\text{unread 系统中的镜像相干严格消失};
}
\]

\[
\boxed{
\text{完整保留镜像相干}
\Longrightarrow
\text{环境没有获得可区分侧别记录}.
}
\]

这不是哲学互补，而是 Gram overlap 的精确恒等式。

---

## 37.9 记录相关单调性：同一指针不能同时完美记录共轭方向

仓库已经在一个 system–record qubit 模型中证明：

\[
\boxed{
\text{同一记录指针对系统 }Z\text{ 地址具有完美相关}
\Longrightarrow
\text{它与系统 }X\text{ 共轭变量的相关为零}.
}
\]

其证明并不只是使用不确定性口号，而是使用 PSD 刚性：

1. 完美 \(Z\)-相关与总迹一迫使 disagreement 对角权重为零；
2. PSD 对角元为零迫使相应整列和整行消失；
3. \(X\)-型交叉项因此全部为零。

这可以抽象成：

### 原理 37.19（正记录单调性）

设一个记录指针把某个 sharp decomposition：

\[
P_+\oplus P_-
\]

变为确定经典标签。则同一指针无法同时保留跨 \(P_+\) 与 \(P_-\) 扇区的完整相干读出。

所以：

\[
\boxed{
\text{记录生成中心的同时，也删除中心块之间的相干。}
}
\]

---

## 37.10 约化不可逆性是控制域不足，而非整体动力学必然不可逆

设有 \(N\) 个环境记录副本，第 \(r\) 个副本给地址 \(i,j\) 的重叠为：

\[
G^{(r)}_{ij}.
\]

多记录通道的总重叠为：

\[
\Gamma_N(i,j)
=
\prod_{r=1}^N
G^{(r)}_{ij}.
\]

因此：

\[
\boxed{
\rho_{ij}^{(N)}
=
\Gamma_N(i,j)\rho_{ij}^{(0)}.
}
\]

定义记录作用：

\[
\boxed{
\mathfrak A_N(i,j)
=
-\log|\Gamma_N(i,j)|.
}
\]

在所有因子非零时：

\[
\mathfrak A_N(i,j)
=
\sum_{r=1}^N
-\log|G^{(r)}_{ij}|.
\]

于是：

\[
|\rho_{ij}^{(N)}|
=
e^{-\mathfrak A_N(i,j)}
|\rho_{ij}^{(0)}|.
\]

仓库进一步证明：

- 若全部相关副本重叠均为单位模；
- 并且每个副本都被相干反转；

则指定矩阵项可被恢复。

但只要保留一个未反转副本 \(k\)，且：

\[
G^{(k)}_{ij}\neq1,
\]

则对非零输入项：

\[
\rho_{ij}\neq0,
\]

完整恢复被阻断。

因此：

\[
\boxed{
\text{约化不可逆性}
=
\text{恢复信息分布在观察者当前控制域之外的记录副本中。}
}
\]

这给出一个记录型时间箭头：

\[
\boxed{
\text{时间箭头}
=
\text{记录账本扩张速度}
-
\text{观察者可逆控制域扩张速度}.
}
\]

若账本复制快于控制域扩张，则观察者看到单向相干损失，即使整体 joint evolution 仍可逆。

---

## 37.11 状态不是路径：当前密度矩阵不能替代记录历史

仓库已经给出两个相互补充的事实：

1. 经典对角 phase-damping channel 从对角输入出发，任意有限迭代都不能生成 off-diagonal coherence；
2. 一次 Hadamard 坐标变换却能从基态生成精确非零相干。

所以：

\[
\boxed{
\text{相同的当前对角状态描述，
不能告诉我们它来自纯经典迭代还是来自量子路径后再粗粒化。}
}
\]

再结合多记录账本：

\[
\boxed{
\text{当前状态}
\neq
\text{路径提升}
\neq
\text{环境记录副本族}.
}
\]

因此完整观察者状态至少需要：

\[
\boxed{
(\rho_t,\ \widetilde\gamma_t,\ \mathcal M_t),
}
\]

其中：

\[
\begin{aligned}
\rho_t&=\text{当前约化状态};\\
\widetilde\gamma_t&=\text{无法由当前状态恢复的路径提升};\\
\mathcal M_t&=\text{已经写入环境或公共账本的记录}.
\end{aligned}
\]

---

## 37.12 锥残差自动产生最优观察见证

此前 Hilbert 子空间情形中：

\[
r=(I-P_M)x
\]

既是闭合余量，又通过 Riesz 对偶成为分离观察者。

该结构可以推广到闭凸锥。

### 定义 37.20（极锥）

设 \(C\) 为实 Hilbert 空间 \(V\) 中的闭凸锥。定义极锥：

\[
C^\circ
=
\{y\in V:\langle y,c\rangle\le0\ \forall c\in C\}.
\]

对偶锥为：

\[
C^\vee=-C^\circ.
\]

### 定理 37.21（Moreau 分解）

对任意 \(x\in V\)，存在唯一分解：

\[
\boxed{
x=P_Cx+r,
}
\]

满足：

\[
P_Cx\in C,
\qquad
r\in C^\circ,
\qquad
\langle P_Cx,r\rangle=0.
\]

### 定理 37.22（锥残差—观察见证对偶）

令：

\[
w=-r.
\]

则：

\[
w\in C^\vee,
\]

且若 \(x\notin C\)，则：

\[
\boxed{
\langle w,c\rangle\ge0
\quad
\forall c\in C,
}
\]

但：

\[
\boxed{
\langle w,x\rangle
=
-\|r\|^2
<0.
}
\]

#### 证明

由 \(r\in C^\circ\)，有 \(-r\in C^\vee\)。又：

\[
\langle w,x\rangle
=
-\langle r,P_Cx+r\rangle
=
-\|r\|^2.
\]

若 \(x\notin C\)，则 \(r\neq0\)，故严格为负。 \(\square\)

因此同一个对象同时是：

\[
\boxed{
\begin{aligned}
r
&=\text{离可实现锥最近的闭合缺陷};\\
\frac12\|r\|^2
&=\text{最小完成作用量};\\
w=-r
&=\text{规范对偶观察见证}.
\end{aligned}
}
\]

### 推论 37.23（四类既有结构的统一）

该定理统一：

\[
\boxed{
\begin{aligned}
\text{Nyman 余量}
&=\text{闭子空间版本};\\
\text{纠缠见证}
&=\text{可分锥版本};\\
\text{经济影子价格}
&=\text{可复制收益锥版本};\\
\text{Weil 负方向}
&=\text{临界正性锥版本}.
\end{aligned}
}
\]

---

## 37.13 可分锥、PSD 锥与观察者对偶锥

对复合系统 \(A\otimes B\)，项目定义并研究：

\[
C_{\mathrm{sep}}
=
\overline{
\operatorname{cone}
\{
\rho_A\otimes\rho_B:
\rho_A,\rho_B\ge0
\}
},
\]

完整 PSD 锥：

\[
C_{\mathrm{PSD}}
=
M_{d_Ad_B}(\mathbb C)_+,
\]

以及 block-positive 锥：

\[
C_{\mathrm{block+}}
=
\left\{
W:
\langle a\otimes b,W(a\otimes b)\rangle\ge0
\quad
\forall a,b
\right\}.
\]

仓库已经形式化：

\[
\boxed{
C_{\mathrm{sep}}
\subseteq
C_{\mathrm{PSD}}
\subseteq
C_{\mathrm{block+}},
}
\]

并证明：

\[
\boxed{
C_{\mathrm{block+}}
=
C_{\mathrm{sep}}^\vee
}
\]

相对于实 Hilbert–Schmidt 配对。

因此：

\[
\boxed{
\text{“合法状态”与“合法观察见证”的锥，
取决于当前要检验的可实现性类别。}
}
\]

相对于完整量子物理：

\[
C_{\mathrm{state}}=C_{\mathrm{PSD}}
\]

近似自对偶。

相对于局部可分实现：

\[
C_{\mathrm{state}}=C_{\mathrm{sep}},
\qquad
C_{\mathrm{test}}=C_{\mathrm{block+}},
\]

二者并不相同。

所以观察者的类型不是由单一 PSD 锥永久决定，而是由问题：

\[
\boxed{
\text{它试图区分哪一种“可实现世界”？}
}
\]

决定。

---

## 37.14 正概率账本与经典答案表不是同一对象

项目中的公开账本下降定理证明：

若一族局部上下文估值满足：

1. 重叠事件上的 publicness；
2. 每个上下文内部的有限加法律；

则它们唯一下降为 covered events 上的一个全局估值。

形式上，若：

\[
v_C:E_C\to\mathbb R
\]

满足：

\[
v_C(e)=v_D(e)
\qquad
(e\in E_C\cap E_D),
\]

并且对上下文内不交分解：

\[
e=e_1\sqcup e_2
\]

有：

\[
v_C(e)=v_C(e_1)+v_C(e_2),
\]

则存在唯一：

\[
v_{\mathrm{pub}}
\]

使每个 \(v_C\) 都是其限制。

但该定理明确不主张：

- 正性；
- Born 表示；
- 乘法性；
- 二值性；
- 全局 character。

因此：

\[
\boxed{
\text{公共正概率账本}
\neq
\text{全局确定性答案表}.
}
\]

### 定义 37.24（状态 section）

局部上下文状态 section 是一族：

\[
\omega_C:\mathcal C\to\mathbb C
\]

满足：

- 正性；
- 归一化；
- 重叠兼容。

### 定义 37.25（character section）

若还满足：

\[
\chi_C(ab)=\chi_C(a)\chi_C(b),
\]

并在投影上取：

\[
\chi_C(P)\in\{0,1\},
\]

则称为 classical character section。

量子状态可以给出所有上下文上的相容正线性 section，但有限 Kochen–Specker 构型仍排除全局 character section。

所以：

\[
\boxed{
\text{量子整体可以是全局正状态，
却不是一个全局经典地址点。}
}
\]

这对逆完成观察者本体有直接影响：

\[
\boxed{
\text{跨全部投影层存在 global section，
不表示该 section 必须是点状、确定性或乘法 character。}
}
\]

---

## 37.15 Born 规则的结构优势是加法下降，而不是任意非线性评分

对完整有限上下文：

\[
\sum_iE_i=I,
\]

Born 总量为：

\[
\sum_i\operatorname{Tr}(\rho E_i)
=
\operatorname{Tr}\rho.
\]

若：

\[
\operatorname{Tr}\rho=1,
\]

则：

\[
\boxed{
\sum_ip_i=1
}
\]

在每个完整上下文中不变。

项目进一步给出精确有限反例：对同一个正、迹一 qutrit 状态和两个完整上下文，二次振幅／Born 加法总量均为一，但四次和六次非线性“价格”出现严格上下文差异。

所以：

\[
\boxed{
\text{Born 规则的关键不是任意“平方”；
而是它来自状态锥与 effect 锥之间的正线性配对。}
}
\]

线性保证：

- 上下文内可加；
- 粗粒化一致；
- 公共账本可下降；
- 归一化不依赖完整上下文的选择。

而：

\[
p\mapsto p^2,
\qquad
p\mapsto p^3
\]

破坏这种事件加法。

因此：

\[
\boxed{
\text{概率是能够跨上下文下降的正线性价格。}
}
\]

---

## 37.16 观察者的经典世界是中心，不是所有投影值的隐藏列表

记录 fixed algebra：

\[
\operatorname{Fix}(\Phi_G)
\cong
\bigoplus_\alpha M_{d_\alpha}(\mathbb C)
\]

的中心为：

\[
Z_G
\cong
\mathbb C^{|\Lambda|}.
\]

局部经典概率分布生活在 \(Z_G\) 上。

但每个块内部仍有：

\[
M_{d_\alpha}(\mathbb C)
\]

的非交换自由度。

所以：

\[
\boxed{
\text{经典结果}
=
\text{中心标签 }\alpha;
}
\]

\[
\boxed{
\text{量子条件状态}
=
\text{中心标签内部的矩阵块}.
}
\]

这使“现实分支”得到一个不依赖诠释的最小代数定义：

\[
\boxed{
\text{分支}
=
\text{记录 fixed algebra 的极小中心投影}.
}
\]

若中心投影为 \(Z_\alpha\)，则条件块为：

\[
Z_\alpha\rho Z_\alpha.
\]

但这不自动解决“为何主观经验只出现一个结果”；它只定义了记录结构中可公开区分的 classical sectors。

---

## 37.17 预测闭包应从线性子空间升级为最小 operator system

设整体 Schrödinger 通道为：

\[
\Phi,
\]

其 Heisenberg 对偶为：

\[
\Phi^\ast.
\]

观察者初始可访问 operator system 为：

\[
\mathcal S_{O,0}.
\]

定义：

\[
\boxed{
\mathcal S_{O,m}
=
\operatorname{OSys}
\left(
I,\,
(\Phi^\ast)^k(E):
E\in\mathcal S_{O,0},
\ 0\le k\le m
\right).
}
\]

其中 \(\operatorname{OSys}\) 表示包含所列元素的最小 operator system。

极限预测闭包为：

\[
\boxed{
\mathcal S_{O,\infty}
=
\operatorname{OSys}
\left(
(\Phi^\ast)^k\mathcal S_{O,0}:
k\ge0
\right).
}
\]

### 定理 37.26（operator-system 一次稳定即永久稳定）

若有限维中：

\[
\mathcal S_{O,m}
=
\mathcal S_{O,m+1},
\]

则：

\[
\boxed{
\mathcal S_{O,m+r}
=
\mathcal S_{O,m}
\qquad
\forall r\ge0.
}
\]

#### 证明

等式说明：

\[
\Phi^\ast(\mathcal S_{O,m})
\subseteq
\mathcal S_{O,m}.
\]

所以继续应用 \(\Phi^\ast\) 不会产生新方向。取 operator-system 闭包后仍不增加元素。归纳即得。 \(\square\)

有限维性保证该递增塔最终稳定。

### 定义 37.27（完全未来等价）

定义：

\[
\boxed{
\rho\equiv_O^\infty\sigma
}
\]

当且仅当：

\[
\operatorname{Tr}((\rho-\sigma)A)=0
\qquad
\forall A\in\mathcal S_{O,\infty}.
\]

等价地：

\[
\rho-\sigma
\in
\mathcal S_{O,\infty}^\perp.
\]

物理未来纤维为：

\[
\boxed{
\operatorname{PhysFiber}_{O,\infty}(\rho)
=
\left(
\rho+\mathcal S_{O,\infty}^\perp
\right)
\cap
\{\sigma\ge0,\operatorname{Tr}\sigma=1\}.
}
\]

因此：

\[
\boxed{
\text{预测闭包}
=
\text{把瞬时观察商修复为动力学稳定的矩阵有序商。}
}
\]

---

## 37.18 预测余量、锥距离与创新能必须同时存在

设线性可见子空间为：

\[
V_m
=
\operatorname{span}_{\mathbb R}
\left(
\mathcal S_{O,m}^{\mathrm{sa}}\cap\{I\}^\perp
\right).
\]

对无迹状态坐标：

\[
X_\rho=\rho-\frac Id,
\]

定义线性余能：

\[
\boxed{
r_m^{(2)}(\rho)
=
\|P_{V_m^\perp}X_\rho\|_2^2.
}
\]

仓库的创新能递推给出：若：

\[
V_m\subseteq V_{m+1},
\]

则：

\[
\boxed{
r_m^{(2)}(\rho)
=
r_{m+1}^{(2)}(\rho)
+
\|P_{V_{m+1}\cap V_m^\perp}X_\rho\|_2^2.
}
\]

但这只是线性坐标完成。

还应定义正锥可实现距离：

\[
\boxed{
r_m^{(+)}(y)
=
\operatorname{dist}
\left(
y,\,
q_m(\operatorname{StateCone})
\right)^2.
}
\]

两者区别为：

\[
\boxed{
\begin{aligned}
r_m^{(2)}
&=\text{尚未被线性坐标捕获的状态质量};\\
r_m^{(+)}
&=\text{形式坐标距离可实现状态像有多远}.
\end{aligned}
}
\]

因此观察塔可能出现：

1. 线性信息不完备，但所有当前读出可实现；
2. 线性信息完备，但某个形式拼接坐标不满足正性；
3. 两者都完备；
4. 两者都失败。

---

## 37.19 动力学、对角与正序闭合是三种不同缺陷

设：

\[
\mathbb E_O:\mathcal A\to\mathcal S_O
\]

为观察粗粒化。

### 动力学自然性缺陷

\[
\boxed{
\partial_O^{\mathrm{dyn}}
=
\mathbb E_O\Phi
-
\Phi_O\mathbb E_O.
}
\]

它回答：

> 先整体演化再观察，是否等于先观察再按有效动力学演化？

### 对角自然性缺陷

\[
\boxed{
\partial_O^{\mathrm{diag}}
=
\mathbb E_O\Delta
-
\Delta_O\mathbb E_O.
}
\]

它回答：

> 完整系统中的自评价，能否下降到观察商中的自评价？

### 正序缺陷

设 effect interval 为：

\[
[0,I]_{\mathcal S_O}
=
\{E\in\mathcal S_O:0\le E\le I\}.
\]

定义：

\[
\boxed{
\partial_O^{\mathrm{ord}}(\Delta)
=
\sup_{E\in[0,I]_{\mathcal S_O}}
\operatorname{dist}
\left(
\Delta(E),
[0,I]_{\mathcal S_O}
\right).
}
\]

它回答：

> 对角操作是否仍把合法问题送到合法问题？

三者互不等价。

项目已有缺陷分解定理说明，一个 projected update 的总误差可以分为：

\[
\boxed{
\text{更新自然性缺陷}
+
\text{Lipschitz 放大的对角投影缺陷}.
}
\]

结合正序以后，应升级为：

\[
\boxed{
\text{总物理缺陷}
\le
\text{动力自然性}
+
\text{表示对角缺陷}
+
\text{正序可实现缺陷}
+
\text{矩阵级 CP 缺陷}.
}
\]

---

## 37.20 量子逻辑中的取反是 \(I-E\)，不是 \(-E\)

对合法 effect：

\[
0\le E\le I,
\]

其补事件为：

\[
\boxed{
E^\perp=I-E.
}
\]

仍满足：

\[
0\le I-E\le I.
\]

所以量子观察者的“取反”必须保留 order interval。

在单个交换上下文中，\(E\mapsto I-E\) 是 Boolean 补。

但跨多个非交换上下文，通常不存在一个共同 Boolean 代数同时容纳全部 sharp effects。

因此：

\[
\boxed{
\text{正序对角化}
=
\text{沿自评价对角读取 effect，
再在当前 order interval 中取补}.
}
\]

这与底层向量空间的：

\[
x\mapsto-x
\]

不是同一种操作。

### 原理 37.28（类型化对角逃逸）

若一个观察层声称：

1. 枚举自己的全部合法 effects；
2. 允许在同一地址读取该枚举；
3. 对读取值施加 \(E\mapsto I-E\)；
4. 新 effect 仍属于同一枚举；

则会出现 Lawvere 型逃逸。

但逃逸对象必须首先通过：

\[
0\le E\le I
\]

以及全部矩阵级正性审计。

所以：

\[
\boxed{
\text{抽象对角逃逸}
\not\Rightarrow
\text{物理量子 effect 逃逸};
}
\]

还需要证明新对象处于合法 order interval。

---

## 37.21 观察者完整度必须加入正序和矩阵稳定轴

定义：

\[
\boxed{
\mathbf C(\mathfrak O)
=
(
C_{\mathrm{sep}},
C_{\mathrm{pred}},
C_{\mathrm{dyn}},
C_{\mathrm{tom}},
C_{\mathrm{ord}},
C_{\mathrm{cp}},
C_{\mathrm{ctx}},
C_{\mathrm{record}},
C_{\mathrm{lift}},
C_{\mathrm{self}},
C_{\mathrm{lim}}
).
}
\]

各轴含义：

\[
\begin{aligned}
C_{\mathrm{sep}}
&=\text{当前问题能否分离目标状态};\\
C_{\mathrm{pred}}
&=\text{未来问题闭包是否稳定};\\
C_{\mathrm{dyn}}
&=\text{动力学能否下降到观察商};\\
C_{\mathrm{tom}}
&=\text{指定状态族是否可层析};\\
C_{\mathrm{ord}}
&=\text{观察商是否保留正序和归一化};\\
C_{\mathrm{cp}}
&=\text{加入任意辅助系统后是否仍合法};\\
C_{\mathrm{ctx}}
&=\text{局部上下文能否拼成所需类型的全局 section};\\
C_{\mathrm{record}}
&=\text{结果账本是否保存所需经典中心};\\
C_{\mathrm{lift}}
&=\text{路径与环境副本是否可恢复};\\
C_{\mathrm{self}}
&=\text{同层自描述是否闭合};\\
C_{\mathrm{lim}}
&=\text{相容有限视图是否由全局物理对象实现}.
\end{aligned}
\]

重要非蕴含包括：

\[
\boxed{
C_{\mathrm{sep}}=1
\not\Rightarrow
C_{\mathrm{cp}}=1;
}
\]

\[
\boxed{
C_{\mathrm{pred}}=1
\not\Rightarrow
C_{\mathrm{tom}}=1;
}
\]

\[
\boxed{
C_{\mathrm{ord}}=1
\not\Rightarrow
C_{\mathrm{ctx}}=1;
}
\]

\[
\boxed{
C_{\mathrm{tom}}=1
\not\Rightarrow
C_{\mathrm{self}}=1;
}
\]

\[
\boxed{
C_{\mathrm{record}}=1
\not\Rightarrow
C_{\mathrm{lift}}=1.
}
\]

所以“观察者完备”不能由一个布尔量表达。

---

## 37.22 Weil 卷积平方：临界线上的自配对正性

设 Weil 测试函数空间为 \(\mathcal T\)，定义 involution：

\[
g^\ast(x)
=
\overline{g(-x)}.
\]

卷积平方为：

\[
\boxed{
f_g
=
g*g^\ast.
}
\]

项目已经形式化，在实频率 \(\xi\in\mathbb R\) 上：

\[
\boxed{
\widehat{f_g}(\xi)
=
|\widehat g(\xi)|^2
\ge0.
}
\]

设零点参数写成：

\[
\rho
=
\frac12+i\gamma.
\]

若：

\[
\Re\rho=\frac12,
\]

则：

\[
\gamma\in\mathbb R.
\]

该零点对 \(f_g\) 的 summand 为：

\[
m_\rho\widehat{f_g}(\gamma)
=
m_\rho|\widehat g(\gamma)|^2
\ge0.
\]

所以每个临界线零点都逐项提供：

\[
\boxed{
\text{同一频率地址上的 GNS 自配对}.
}
\]

这不是只在总和以后出现的正性，而是每个临界零点 summand 自身就是模平方。

---

## 37.23 离线零点把自配对拆成镜像纤维间的交叉相干

若：

\[
\rho
=
\frac12+\delta+i t,
\qquad
\delta\neq0,
\]

则：

\[
\gamma
=
t-i\delta
\notin\mathbb R.
\]

其复共轭为：

\[
\overline\gamma=t+i\delta.
\]

项目已经形式化复频率因子分解：

\[
\boxed{
\widehat{g*g^\ast}(\gamma)
=
\widehat g(\gamma)\,
\overline{\widehat g(\overline\gamma)}.
}
\]

记：

\[
A_g
=
\widehat g(\gamma),
\qquad
B_g
=
\widehat g(\overline\gamma).
\]

则单个镜像—共轭四元轨道的总贡献为：

\[
\boxed{
Q_\rho(g)
=
4m_\rho
\operatorname{Re}
\left(
A_g\overline{B_g}
\right).
}
\]

函数方程和共轭保证 \(Q_\rho(g)\) 为实数，但不保证其非负。

所以：

\[
\boxed{
\text{函数方程}
=
\text{交叉配对的 Hermitian 实性};
}
\]

而：

\[
\boxed{
\text{临界线}
=
\text{两个镜像评价地址相合，交叉配对退化为自配对}.
}
\]

---

## 37.24 离线轨道的二地址观察者空间

对一个假想离线轨道定义：

\[
\boxed{
\mathscr H_\rho
=
\operatorname{span}
\{
|\mathrm R\rangle,
|\mathrm L\rangle
\}
\cong
\mathbb C^2.
}
\]

其中：

\[
|\mathrm R\rangle
=
\text{右侧评价地址 }\gamma,
\]

\[
|\mathrm L\rangle
=
\text{左侧镜像评价地址 }\overline\gamma.
\]

定义测试函数产生的评价向量：

\[
\boxed{
|v_g\rangle
=
A_g|\mathrm R\rangle
+
B_g|\mathrm L\rangle.
}
\]

定义侧别算子：

\[
Z_\rho
=
\begin{pmatrix}
1&0\\
0&-1
\end{pmatrix},
\]

以及反射交换算子：

\[
J_\rho
=
\begin{pmatrix}
0&1\\
1&0
\end{pmatrix}.
\]

若 Cayley 径向深度为 \(\beta_\rho\)，定义法向算子：

\[
\boxed{
B_\rho
=
\beta_\rho Z_\rho.
}
\]

则：

\[
\boxed{
J_\rho B_\rho J_\rho
=
-B_\rho.
}
\]

四元轨道读出为：

\[
\boxed{
Q_\rho(g)
=
2m_\rho
\langle v_g,J_\rho v_g\rangle.
}
\]

因为：

\[
\langle v_g,J_\rho v_g\rangle
=
2\operatorname{Re}(A_g\overline{B_g}).
\]

所以离线零点对应的最小观察者结构不是一个裸复数，而包含：

\[
\boxed{
(
\beta_\rho,\,
Z_\rho,\,
J_\rho,\,
E_\rho,\,
Q_\rho
),
}
\]

其中：

\[
E_\rho(g)
=
(A_g,B_g).
\]

这里的二地址模型是局部代数结构，不声称真实 zeta 零点是物理 qubit。

---

## 37.25 交换签名分解

定义对称和反对称基：

\[
|+\rangle
=
\frac{
|\mathrm R\rangle+|\mathrm L\rangle
}{\sqrt2},
\]

\[
|-\rangle
=
\frac{
|\mathrm R\rangle-|\mathrm L\rangle
}{\sqrt2}.
\]

则：

\[
J_\rho|+\rangle=|+\rangle,
\qquad
J_\rho|-\rangle=-|-\rangle.
\]

写：

\[
c_+(g)
=
\frac{A_g+B_g}{\sqrt2},
\]

\[
c_-(g)
=
\frac{A_g-B_g}{\sqrt2}.
\]

则：

\[
\boxed{
\langle v_g,J_\rho v_g\rangle
=
|c_+(g)|^2-|c_-(g)|^2.
}
\]

因此：

\[
\boxed{
Q_\rho(g)
=
2m_\rho
\left(
|c_+(g)|^2-|c_-(g)|^2
\right).
}
\]

这表明离线轨道的局部 Hermitian 形式具有签名：

\[
\boxed{
(1,1).
}
\]

### 临界线退化

若 \(\gamma=\overline\gamma\)，则：

\[
A_g=B_g.
\]

所以：

\[
c_-(g)=0.
\]

于是：

\[
Q_\rho(g)
=
4m_\rho|A_g|^2
\ge0.
\]

因此：

\[
\boxed{
\text{临界线并不是把一个负方向“估计掉”；
而是反对称观察方向根本没有被生成。}
}
\]

---

## 37.26 评价像维数—负方向判据

定义离线评价映射：

\[
\boxed{
E_\rho:
\mathcal T\to\mathbb C^2,
\qquad
E_\rho(g)
=
(A_g,B_g).
}
\]

在 \(\mathbb C^2\) 上定义 Hermitian 形式：

\[
q_J(v)
=
v^\ast J_\rho v.
\]

### 定理 37.29（二维像必有负方向）

若：

\[
\dim_{\mathbb C}
\operatorname{im}E_\rho
=
2,
\]

则存在 \(g\in\mathcal T\) 使：

\[
\boxed{
Q_\rho(g)<0.
}
\]

#### 证明

二维像等于整个 \(\mathbb C^2\)。取：

\[
v=|-\rangle.
\]

则：

\[
q_J(v)=-1.
\]

由满射性存在 \(g\) 使 \(E_\rho(g)=v\)，故：

\[
Q_\rho(g)
=
2m_\rho q_J(v)
=
-2m_\rho<0.
\]

\(\square\)

### 推论 37.30（局部非负像的维数限制）

若：

\[
Q_\rho(g)\ge0
\qquad
\forall g\in\mathcal T,
\]

则：

\[
\boxed{
\dim_{\mathbb C}
\operatorname{im}E_\rho
\le1.
}
\]

因为签名 \((1,1)\) 的 Hermitian 空间中，不存在二维非负线性子空间。

这给出一个非常具体的局部刚性：

\[
\boxed{
\text{离线轨道若对全部平方测试保持非负，
则两个镜像评价不能是独立坐标。}
}
\]

---

## 37.27 一维非负关系仍不自动等于临界对角

若：

\[
\operatorname{im}E_\rho
=
\operatorname{span}\{(1,\lambda)\},
\]

则：

\[
Q_\rho(g)
\propto
2\operatorname{Re}\lambda.
\]

所以局部非负只要求：

\[
\operatorname{Re}\lambda\ge0.
\]

它并不自动要求：

\[
\lambda=1.
\]

而临界线真正给出：

\[
A_g=B_g
\qquad
\forall g,
\]

即：

\[
\lambda=1.
\]

因此：

\[
\boxed{
\text{局部正性}
\not\Rightarrow
\text{镜像地址完全合一}.
}
\]

要从一维非负关系推进到真正临界对角，还需要额外结构，例如：

- reflection naturality；
- conjugation covariance；
- normalization；
- 足够丰富的测试函数；
- prime-side transition law；
- 唯一性或极值性。

---

## 37.28 side-flip 不变性与正性的冲突

侧别算子满足：

\[
\boxed{
Z_\rho J_\rho Z_\rho
=
-J_\rho.
}
\]

所以：

\[
q_J(Z_\rho v)
=
-q_J(v).
\]

### 定理 37.31（side-flip 正性刚性）

设线性子空间：

\[
W\subseteq\mathbb C^2
\]

满足：

\[
Z_\rho W\subseteq W,
\]

并且：

\[
q_J(v)\ge0
\qquad
\forall v\in W.
\]

则：

\[
\boxed{
q_J(v)=0
\qquad
\forall v\in W.
}
\]

#### 证明

对任意 \(v\in W\)，有 \(Z_\rho v\in W\)。所以：

\[
q_J(v)\ge0,
\]

且：

\[
-q_J(v)
=
q_J(Z_\rho v)
\ge0.
\]

故 \(q_J(v)=0\)。 \(\square\)

由于签名 \((1,1)\) 的最大 totally isotropic 子空间维数为一，进一步得到：

\[
\boxed{
\dim_{\mathbb C}W\le1.
}
\]

所以若离线评价像同时：

1. 对 side flip 闭合；
2. 对全部测试保持非负；
3. 具有两个独立评价自由度；

则矛盾。

这提供一个条件 RH 路线：

\[
\boxed{
\text{证明 prime-side 测试闭包使离线评价像既 }Z\text{-不变又二维}.
}
\]

当前项目尚未证明这一算术闭包条件。

---

## 37.29 侧别记录与交换读出的观察者互补

在二地址离线模型中：

\[
Z_\rho
=
\text{左右侧别},
\]

而：

\[
J_\rho
=
\text{左右镜像相干交换}.
\]

若环境完美记录 \(Z_\rho\)，则 unread channel 为 \(Z\)-basis pinching：

\[
\mathbb E_Z(\rho)
=
P_{\mathrm R}\rho P_{\mathrm R}
+
P_{\mathrm L}\rho P_{\mathrm L}.
\]

于是：

\[
\boxed{
\operatorname{Tr}
\left(
\mathbb E_Z(\rho)J_\rho
\right)
=
0.
}
\]

因为 \(J_\rho\) 只有 off-diagonal 元素。

### 定理 37.32（完美侧别记录消除镜像交换读出）

对任意二地址状态 \(\rho\)：

\[
\boxed{
\text{若左右侧别被完美记录并丢弃记录值，
则 }J_\rho\text{ 的期望严格为零。}
}
\]

这与项目的 record-correlation monogamy 同型：

\[
\text{perfect }Z\text{-record}
\Longrightarrow
X\text{-correlation}=0.
\]

因此一个离线结构若同时要求：

1. 左右侧别成为公开、完美、可复制的经典标签；
2. Weil 四元 orbit 保留非零 \(J_\rho\)-型交叉读出；

则二者不能由同一个 unread 观察接口同时实现。

必须至少发生以下之一：

\[
\boxed{
\begin{aligned}
&\text{侧别没有被完美记录};\\
&\text{镜像相干只存在于含环境的 joint state};\\
&\text{Weil 读出属于另一个不兼容上下文};\\
&\text{记录值没有被丢弃};\\
&\text{所谓侧别不是一个可公开复制的经典变量}.
\end{aligned}
}
\]

这并不排除离线零点，但它说明：

\[
\boxed{
\text{离线零点的完整观察者本体不能是一个同时携带
经典侧别和未衰减镜像相干的单一经典对象。}
}
\]

它若存在，必须具有量子上下文或 joint-record 结构。

---

## 37.30 离线轨道的 Gram 状态与不定 observable

定义 rank-one Gram 矩阵：

\[
\boxed{
G_g
=
|v_g\rangle\langle v_g|
=
\begin{pmatrix}
|A_g|^2&A_g\overline{B_g}\\
B_g\overline{A_g}&|B_g|^2
\end{pmatrix}.
}
\]

显然：

\[
G_g\ge0.
\]

离线轨道贡献为：

\[
\boxed{
Q_\rho(g)
=
2m_\rho
\operatorname{Tr}(G_gJ_\rho).
}
\]

所以离线问题不是“Gram 状态失去正性”。

真正发生的是：

\[
\boxed{
\text{一个合法 PSD Gram 状态，
被一个具有正负谱的交换 observable 评价。}
}
\]

\(J_\rho\) 的谱为：

\[
\{+1,-1\}.
\]

因此：

\[
\operatorname{Tr}(G_gJ_\rho)
\]

可以为正、零或负。

这与项目中的 block-positive／entanglement-witness 结构有相似之处：

- 状态本身仍可 PSD；
- 检测问题由更大的对偶锥或不定 observable 给出；
- 负值见证目标不属于某个更窄的可实现锥。

但二者不是同一具体锥，不能直接把离线零点称为纠缠态。

---

## 37.31 临界线是评价地址的对角，不只是复平面的竖线

定义双评价映射：

\[
E(s)
=
\left(
\widehat g(\gamma(s)),
\widehat g(\overline{\gamma(s)})
\right).
\]

临界线条件：

\[
\Re s=\frac12
\]

等价于：

\[
\gamma(s)=\overline{\gamma(s)}.
\]

所以：

\[
E(s)
\in
\Delta_{\mathbb C}
=
\{(A,A):A\in\mathbb C\}.
\]

该对角子空间正是 \(J_\rho\) 的正本征空间：

\[
\Delta_{\mathbb C}
=
\operatorname{span}\{|+\rangle\}.
\]

因此：

\[
\boxed{
\text{Riemann 临界线}
=
\text{镜像评价纤维的对角嵌入像}.
}
\]

离线时：

\[
E(s)\notin\Delta_{\mathbb C}
\]

一般成立，并产生反对称分量：

\[
c_-(g)
=
\frac{A_g-B_g}{\sqrt2}.
\]

所以：

\[
\boxed{
\text{离线深度并不只是横坐标偏移；
它使一个自配对评价分裂为两个可独立变化的地址。}
}
\]

这正是本节所说的“对角缺陷”。

---

## 37.32 函数方程给出 Hermitian 配对，RH 要求正 GNS 完成

设显式公式定义 Hermitian 线性泛函：

\[
\Omega_\zeta:\mathcal T\to\mathbb C.
\]

若：

\[
\Omega_\zeta(g^\ast g)\ge0
\qquad
\forall g,
\]

则可以构造 GNS 空间：

\[
\mathscr H_\zeta
=
\overline{
\mathcal T/N_\zeta
},
\]

其中：

\[
N_\zeta
=
\{g:\Omega_\zeta(g^\ast g)=0\}.
\]

内积为：

\[
\boxed{
\langle[g],[h]\rangle_\zeta
=
\Omega_\zeta(h^\ast g).
}
\]

范数平方为：

\[
\boxed{
\|[g]\|_\zeta^2
=
\Omega_\zeta(g^\ast g).
}
\]

函数方程和共轭对称足以保证相关零点总和为 Hermitian／实，但不自动保证：

\[
\Omega_\zeta(g^\ast g)\ge0.
\]

因此：

\[
\boxed{
\text{函数方程}
=
\text{GNS 候选形式的 Hermitian 性};
}
\]

\[
\boxed{
\text{RH-like 正性}
=
\text{该 Hermitian 形式能够完成为真正 Hilbert 内积}.
}
\]

若 RH 为假，Weil 判据意味着存在 \(g\) 使：

\[
\Omega_\zeta(g^\ast g)<0.
\]

此时不能得到正 GNS Hilbert 空间，只能得到不定型或必须改变测试锥。

---

## 37.33 RH 不是“一个正锥存在”，而是平方锥上的全局正状态存在

定义 Weil 平方锥：

\[
\boxed{
C_{\mathrm{Weil}}
=
\left\{
\sum_{j=1}^m
g_j*g_j^\ast:
m<\infty
\right\}.
}
\]

则 RH 的正性型版本应表述为：

\[
\boxed{
\Omega_\zeta(f)\ge0
\qquad
\forall f\in C_{\mathrm{Weil}}.
}
\]

这里：

- \(C_{\mathrm{Weil}}\) 由测试函数卷积和 involution 无条件定义；
- \(\Omega_\zeta\) 由显式公式的 prime、pole、archimedean 与 zero terms 定义；
- 正性不是另行指定，而是要证明的全局性质。

所以：

\[
\boxed{
\mathrm{RH}
=
\text{zeta 显式公式泛函在 Weil 平方锥上是正状态}.
}
\]

这比：

\[
\text{存在某个抽象正锥使某个算子可酉化}
\]

更贴合项目已经形式化的接口。

---

## 37.34 但离线单轨道负性不自动等于全局 Weil 负性

即使定理 37.29 给出某个 \(g\) 使单个离线轨道：

\[
Q_\rho(g)<0,
\]

完整显式公式仍包含：

\[
\Omega_\zeta(g^\ast g)
=
Q_\rho(g)
+
\sum_{\rho'\neq\rho}
Q_{\rho'}(g)
+
P(g)
+
A(g),
\]

其中：

\[
P(g)
=
\text{prime/pole contributions},
\]

\[
A(g)
=
\text{archimedean contribution}.
\]

其他项可能为正并抵消该负方向。

因此，从局部轨道负性到全局 RH 反例需要一个 localization theorem。

### 条件定理 37.35（离线局域化蕴含全局负性）

若对某个离线轨道 \(\rho\)，存在测试函数列 \(g_n\) 满足：

\[
Q_\rho(g_n)\to -c
\qquad
(c>0),
\]

且：

\[
\sum_{\rho'\neq\rho}
Q_{\rho'}(g_n)
+
P(g_n)
+
A(g_n)
\to0,
\]

则：

\[
\Omega_\zeta(g_n^\ast g_n)<0
\]

对充分大 \(n\) 成立。

#### 证明

由总和分解和极限直接得到。 \(\square\)

真正困难的部分是同时完成：

\[
\boxed{
\text{目标离线评价插值}
+
\text{其余无限谱压制}
+
\text{prime/archimedean 控制}.
}
\]

---

## 37.35 离线 observer 的 classicality–coherence 二分

假设一个离线镜像对被表示为两个地址：

\[
\mathrm R,\mathrm L.
\]

则完整观察者有两种极端。

### 经典侧别观察者

它能够完美、公开、可复制地记录：

\[
\varepsilon\in\{\mathrm R,\mathrm L\}.
\]

此时 fixed algebra 在该二地址上为对角代数：

\[
\mathbb C\oplus\mathbb C.
\]

镜像相干 \(J_\rho\) 被 unread channel 删除。

### 相干镜像观察者

它完整保留：

\[
\langle J_\rho\rangle.
\]

此时环境记录必须满足：

\[
|c|=1,
\]

所以不能区分 \(\mathrm R\) 与 \(\mathrm L\)。

因此：

\[
\boxed{
\text{离线侧别作为经典公开事实}
\quad\text{与}\quad
\text{离线镜像相干作为未衰减读出}
}
\]

不能由同一个纯记录接口同时实现。

这提示一种本体修正：

\[
\boxed{
\text{复平面中“左点”和“右点”的离散标签，
可能只是一个上下文中的记录；
四元显式公式中的交叉相干属于另一个上下文。}
}
\]

所以一个假想离线零点的完整本体必须至少是：

\[
\boxed{
\text{非交换上下文 atlas},
}
\]

而不是一个携带全部性质的单一经典点。

---

## 37.36 从“离线点”升级为矩阵序 observer section

第 36 节把离线对象定义为 RH defect atlas 上的相容非零 section。

本节进一步要求每个图表不是普通集合，而是 operator-system／矩阵序图表：

\[
\boxed{
\mathbf D_{\mathrm{RH}}^{\mathrm{ord}}
=
\left(
\mathcal D_i,
\{M_n(\mathcal D_i)_+\}_{n\ge1},
p_{ji}
\right).
}
\]

一个候选离线 observer section 包括：

\[
\boxed{
d=(d_i)_i
}
\]

以及：

\[
\boxed{
\omega_i:
\mathcal D_i\to\mathbb C
}
\]

满足：

1. 坐标相容：

   \[
   p_{ji}(d_j)=d_i;
   \]

2. 状态相容：

   \[
   \omega_i=\omega_j\circ p_{ji};
   \]

3. 每级正性；

4. 全部矩阵级正性；

5. 归一化；

6. instrument 条件化相容；

7. 环境记录 cocycle 相容；

8. 必要的能量、normality 和 form-domain 条件。

因此集合逆极限：

\[
\varprojlim_iD_i
\]

只给出形式 section。

真正物理／算术允许的 section 应写成：

\[
\boxed{
\operatorname{PhysSect}
\left(
\mathbf D_{\mathrm{RH}}^{\mathrm{ord}}
\right).
}
\]

于是 RH 的本体型问题进一步收紧为：

\[
\boxed{
\text{是否存在一个非零、矩阵正、条件化相容、
记录一致且全局可实现的离线 observer section？}
}
\]

---

## 37.37 正锥不会自动消灭离线 section

第 36 节已经证明：非空有限集合的 cofiltered 逆系统通常具有非空逆极限。

同样地，若每个阶段的状态空间：

\[
K_i
\]

是非空紧凸集，且 bonding maps：

\[
p_{ji}:K_j\to K_i
\]

连续满射，则：

\[
\varprojlim_iK_i\neq\varnothing.
\]

因此：

\[
\boxed{
\text{逐层存在正状态}
+
\text{满射相容}
}
\]

通常支持而不是排除全局正 section。

要排除离线 observer，必须在更强位置出现障碍：

\[
\boxed{
\begin{aligned}
&\text{某个矩阵级正锥为空};\\
&\text{transition 不是完全正};\\
&\text{局部状态不满足重叠 publicness};\\
&\text{instrument 条件化不相容};\\
&\text{form-domain 或能量条件不闭合};\\
&\text{正性常数在极限中退化};\\
&\text{出现 contextual gluing obstruction};\\
&\text{出现严格收缩或奇偶刚性}.
\end{aligned}
}
\]

所以本节再次确认：

\[
\boxed{
\text{“正锥存在”本身不具有 RH 证明力。}
}
\]

证明力必须来自正锥、转换、记录、上下文和极限的联合结构。

---

## 37.38 prime-axis Hilbert 空间中的状态—effect 接缝

项目构造 prime-axis 系数：

\[
k_s(a)
=
n(a)^{-s}
\]

并证明：

\[
\boxed{
k_s\in\ell^2
\iff
\Re s>\frac12.
}
\]

同时：

- 虚部方向：

  \[
  s\mapsto s+it
  \]

  产生范数保持酉群；

- 向右的实部方向：

  \[
  s\mapsto s+\delta,
  \qquad
  \delta\ge0
  \]

  产生收缩半群；

- 镜像伙伴为：

  \[
  1-\overline s;
  \]

- 临界线同时满足：

  \[
  s=1-\overline s,
  \]

  half-density unit modulus，

  self-resonance，

  以及 \(\ell^2\) 阈值。

这提示 rigged Hilbert 解释：

\[
\boxed{
\Phi
\subset
\mathscr H
\subset
\Phi^\prime.
}
\]

其中可能有：

\[
\boxed{
\Re s>\frac12
=
\text{normalizable state side},
}
\]

\[
\boxed{
\Re s<\frac12
=
\text{dual/distribution effect side},
}
\]

\[
\boxed{
\Re s=\frac12
=
\text{state 与 effect 的自对偶接缝}.
}
\]

若存在离线对：

\[
\rho=\frac12+\delta+i\gamma,
\qquad
1-\overline\rho
=
\frac12-\delta+i\gamma,
\]

则其中一侧属于 \(\ell^2\) normalizable 域，另一侧不属于同一个 \(\ell^2\) 状态空间。

因此：

\[
\boxed{
\text{离线镜像对把一个自对偶广义模式拆成
normal state side 与 dual effect side。}
}
\]

当前项目尚未完成对应的 nuclear rigging 和 generalized eigenvector 理论，因此该解释保持为研究方向。

---

## 37.39 有限 Gram 塔与全局 GNS 完成

设测试空间递增：

\[
\mathcal T_0
\subseteq
\mathcal T_1
\subseteq
\cdots.
\]

对有限测试族：

\[
g_1,\ldots,g_N\in\mathcal T_m,
\]

定义 Gram 矩阵：

\[
\boxed{
\Gamma_{\Omega,m}
=
\left[
\Omega(g_j^\ast g_i)
\right]_{i,j=1}^N.
}
\]

\(\Omega\) 正当且仅当所有有限 Gram 矩阵均 PSD。

但“每个有限阶段 PSD”要推出全局 GNS 完成，还必须控制：

1. 测试塔是否为 form core；
2. 二次型是否可闭；
3. 极限是否连续；
4. 统一 coercivity 是否存在；
5. null spaces 是否相容；
6. completion 是否保留作用表示。

### 定义 37.36（有限层最小正性常数）

在有限维测试层 \(\mathcal T_m\) 中定义：

\[
\boxed{
\lambda_m
=
\inf_{\substack{g\in\mathcal T_m\\ \|g\|_{\mathrm{ref}}=1}}
\Omega(g^\ast g).
}
\]

即使：

\[
\lambda_m\ge0
\qquad
\forall m,
\]

仍可能有：

\[
\lambda_m\downarrow0.
\]

此时有限阶段均无负方向，但正完成在无限极限中退化到锥边界。

所以需要区分：

\[
\boxed{
\text{逐层正性}
}
\]

与：

\[
\boxed{
\text{统一非退化正性}.
}
\]

若存在 \(c>0\) 使：

\[
\lambda_m\ge c
\qquad
\forall m,
\]

则二次型对参考范数具有统一下界，更有希望完成为稳定 Hilbert 几何。

---

## 37.40 三种可能的 RH 失败机制

在本节框架中，假设 RH 为假，不必简单说“正锥不存在”。

至少有三种不同可能。

### 类型 A：显式负平方

存在 \(g\)：

\[
\Omega_\zeta(g^\ast g)<0.
\]

这是 Weil 正性直接失败。

### 类型 B：非负但退化的极限

所有有限测试层均 PSD，但：

\[
\lambda_m\to0,
\]

并出现不能一致商掉的极限 null direction。

### 类型 C：形式局部正，但 transitions 不物理

每个图表内部存在正状态，但 chart transition：

\[
p_{ji}
\]

不保持矩阵正序、条件化或 form domain，所以没有 global physical section。

因此：

\[
\boxed{
\neg\mathrm{RH}
}
\]

在观察者本体中可能表现为：

\[
\boxed{
\text{负性}
\quad\text{或}\quad
\text{退化}
\quad\text{或}\quad
\text{拼接失败}.
}
\]

标准 Weil 判据若完整适用，最终必须给出类型 A 的测试见证；但在构造候选有限模型时，B 和 C 是最常见的伪闭合来源。

---

## 37.41 一条新的条件证明路线：prime record–coherence rigidity

本节的记录互补和离线二地址模型组合出一个条件路线。

### 假设 1：算术侧别 record

从 prime ledger 无条件构造一个 CP instrument：

\[
\mathcal R_\pm
\]

其经典结果记录离线扇区：

\[
\varepsilon\in\{\mathrm R,\mathrm L\}.
\]

### 假设 2：记录忠实

对任何非零离线深度：

\[
\beta_\rho\neq0,
\]

该 instrument 完美区分左右侧别。

### 假设 3：显式公式自然性

Weil 轨道读出：

\[
Q_\rho(g)
\]

在 record dilation 和 partial trace 下保持自然。

### 假设 4：非零交叉需求

离线轨道存在要求某个允许测试 \(g\) 满足：

\[
\langle v_g,J_\rho v_g\rangle\neq0.
\]

那么：

\[
\boxed{
\text{完美侧别 record}
\Longrightarrow
\text{unread }J_\rho\text{-读出为零},
}
\]

与假设 4 冲突。

故：

\[
\beta_\rho=0.
\]

### 条件定理 37.37（prime record–coherence rigidity）

若上述四个假设可从 zeta 的无条件算术结构建立，则所有非平凡零点位于临界线。

该路线的真正缺口是：

\[
\boxed{
\text{构造一个不以零点位置为输入的 prime-side CP 记录仪器。}
}
\]

---

## 37.42 第二条条件路线：离线评价满秩与全局局域化

### 假设 1：双点评价满秩

对每个离线 \(\gamma\neq\overline\gamma\)，评价映射：

\[
E_\rho(g)
=
\left(
\widehat g(\gamma),
\widehat g(\overline\gamma)
\right)
\]

的像为 \(\mathbb C^2\)。

### 假设 2：谱局域化

存在测试函数序列 \(g_n\)：

- 在目标离线 orbit 上趋于反对称方向；
- 在其余零点 orbit 上评价趋零；
- prime/pole/archimedean 总余量趋零。

则目标 orbit 贡献趋于严格负值，完整 Weil 泛函最终为负。

### 条件定理 37.38（评价—局域化排除）

若双点评价满秩与全局谱局域化对每个离线 orbit 成立，则 Weil 正性排除全部离线零点。

这一路线的关键不是正锥抽象，而是：

\[
\boxed{
\text{Paley–Wiener 型插值}
+
\text{无限零点谱压制}
+
\text{显式公式尾控制}.
}
\]

---

## 37.43 第三条条件路线：矩阵序 defect atlas 的无 character 定理

第 36 节的 RH defect atlas 目前只要求坐标 section 相容。

本节建议区分两种 global section。

### 正状态 section

\[
\omega_i
\]

在每个图表上为正、归一化、完全正相容。

### 纯 character section

\[
\chi_i
\]

还应在对应交换或乘法结构上为极端／乘法评价。

复平面离线零点作为一个离散 point-like object，更接近一个 generalized character，而不是任意混合正状态。

因此可提出：

### 猜想 37.39（off-critical character exclusion）

RH defect atlas 可能允许一个全局正状态 section，但不允许任何满足：

- 非零离线复平面坐标；
- 镜像 transition；
- prime factorization；
- Weil square positivity；
- matrix-order compatibility；

的 pure character section。

若证明该猜想，则离线零点无法作为一个全局点状观察者存在，即使更一般的非经典正 section 仍可存在。

这与量子 contextuality 的经验相似：

\[
\boxed{
\text{全局概率状态可以存在，
而全局确定性 character 不存在。}
}
\]

但本节不声称 RH atlas 已经构造，也不声称该猜想等同于 Kochen–Specker。

---

## 37.44 第四条条件路线：自对偶接缝唯一性

设存在 rigged Hilbert triple：

\[
\Phi
\subset
\mathscr H
\subset
\Phi^\prime,
\]

以及 reflection：

\[
J:s\mapsto1-\overline s.
\]

假设：

1. \(\Re s>1/2\) 的 mode 产生 normalizable state；
2. \(\Re s<1/2\) 的 mirror mode 产生 continuous effect；
3. 零点 mode 必须同时是 state 和 effect 的同一 generalized eigenobject；
4. state–effect handshake 的固定对象仅位于：

   \[
   \Re s=\frac12.
   \]

则所有零点必须在临界线。

该路线将 RH 改写为：

\[
\boxed{
\text{零点 generalized mode 必须位于状态锥与 effect 锥的自对偶接缝。}
}
\]

真正缺口是构造该 rigging，并证明零点的谱身份，而不是仅观察 \(\ell^2\) 阈值。

---

## 37.45 与对角化理论的最终连接

本节出现了三种对角。

### 地址对角

\[
\gamma=\overline\gamma.
\]

它把两个镜像评价地址合一。

### GNS 对角

\[
g^\ast g.
\]

它把一个操作与自身配对，产生范数平方。

### 自描述对角

\[
E(a,a).
\]

它把描述者地址和被描述对象地址设为同一项。

三者不是同一个定理，但在逆完成元层共享结构：

\[
\boxed{
\text{同址配对}
\Longrightarrow
\text{正性、固定点或闭合};
}
\]

\[
\boxed{
\text{地址分裂}
\Longrightarrow
\text{交叉项、余量或逃逸}.
}
\]

在 RH 卷积平方中：

\[
\boxed{
\text{临界线}
=
\text{地址对角}
+
\text{GNS 对角};
}
\]

离线时：

\[
\boxed{
\text{地址分裂}
\Longrightarrow
\text{GNS 自配对被读取为交叉相干}.
}
\]

所以本节给出“闭合缺陷本质上是对角问题”的一个类型正确版本：

\[
\boxed{
\text{闭合失败不是抽象地“离开一条线”，
而是原本应在同一观察地址完成的自配对，
被迫经过两个不同纤维的 transition 才能返回。}
}
\]

---

## 37.46 新的统一作用量

定义四类缺陷作用量。

### 线性余量

\[
\mathcal A_{\mathrm{lin}}
=
\frac12
\|P_{\mathcal S^\perp}X_\rho\|_2^2.
\]

### 锥可实现余量

\[
\mathcal A_{\mathrm{cone}}
=
\frac12
\operatorname{dist}(x,C)^2.
\]

### 记录作用

\[
\mathcal A_{\mathrm{rec}}
=
-\sum_r\log|G^{(r)}_{ij}|.
\]

### GNS 负性作用

\[
\mathcal A_{\mathrm{GNS}}(g)
=
\left(
-\Omega_\zeta(g^\ast g)
\right)_+.
\]

可以组成观察者总缺陷：

\[
\boxed{
\mathcal A_O
=
w_1\mathcal A_{\mathrm{lin}}
+
w_2\mathcal A_{\mathrm{cone}}
+
w_3\mathcal A_{\mathrm{rec}}
+
w_4\mathcal A_{\mathrm{GNS}}
+
w_5\|\partial_O^{\mathrm{dyn}}\|^2
+
w_6\|\partial_O^{\mathrm{diag}}\|^2.
}
\]

这里权重必须由具体问题定义，不能任意宣称自然唯一。

该式的意义是：

\[
\boxed{
\text{观察者闭合不是单一距离，
而是线性捕获、物理可实现、记录可逆、
GNS 正性和自然性缺陷的多目标最小作用问题。}
}
\]

---

## 37.47 与经济观察者的结构同构

第 34 节中：

\[
\text{marketed payoff subspace}
\]

决定可复制收益，

正价格泛函决定无套利，

流动性路径决定账面价值能否兑现，

支付网络决定 aggregate 数据能否实现结算。

本节中：

\[
\text{operator system}
\]

决定可提问题，

正状态决定 Born 价格，

instrument 和 record 决定概率能否成为分支，

矩阵正性决定局部坐标能否由全局状态实现。

对应表为：

\[
\boxed{
\begin{array}{c|c}
\text{经济观察者} & \text{量子矩阵序观察者}\\
\hline
\text{可复制收益空间} & \text{可访问 operator system}\\
\text{状态价格泛函} & \text{正状态}\\
\text{不可套保余量} & \text{观察余空间／相干余量}\\
\text{影子价格} & \text{对偶见证}\\
\text{流动性路径} & \text{instrument／record dilation}\\
\text{支付网络} & \text{环境关联与上下文 atlas}\\
\text{最小市场完成} & \text{最小预测／GNS 完成}
\end{array}
}
\]

所以：

\[
\boxed{
\text{正性在两个领域中都不是“数值非负”而已；
它决定一个局部报价或局部概率是否能下降为全局可实现结构。}
}
\]

---

## 37.48 Lean 形式化建议顺序

本节新增纸面定理可以按以下顺序形式化。

### 第一阶段：有限矩阵正锥面

建议文件：

```text
D5/S3/Observer/PositiveFaces/ZeroWeightSupport.lean
```

形式化：

\[
\operatorname{Tr}(\rho P)=0
\Longrightarrow
P\rho=\rho P=0.
\]

以及：

\[
\operatorname{Tr}(\rho P)=1
\Longrightarrow
\rho=P\rho P.
\]

### 第二阶段：记录 fixed algebra

建议文件：

```text
D5/S3/Observer/EnvironmentRecords/FixedAlgebraCenter.lean
```

形式化 normalized record vectors 的等价类和：

\[
\operatorname{Fix}(\Phi_G)
\cong
\bigoplus_\alpha M_{d_\alpha}(\mathbb C).
\]

### 第三阶段：二地址 record–coherence complementarity

建议文件：

```text
D5/S3/ObserverMemory/RecordCoherenceComplementarity.lean
```

形式化：

\[
\mathcal D^2+|c|^2=1
\]

以及 perfect record 消除交换 observable 期望。

### 第四阶段：锥残差见证

建议文件：

```text
D5/S3/Resource/ConeResidualWitness.lean
```

形式化 Moreau 分解和：

\[
\langle-r,x\rangle=-\|r\|^2.
\]

### 第五阶段：operator-system 预测闭包

建议文件：

```text
D5/S3/Observer/Tomography/OperatorSystemClosure.lean
```

先在有限维矩阵空间用自伴、单位和线性闭包的显式载体实现，不必立即引入完整抽象 operator-system 库。

### 第六阶段：离线交换签名

建议文件：

```text
D5/S3/Weil/ZetaBridge/OffLineSwapSignature.lean
```

形式化：

\[
4m\operatorname{Re}(A\overline B)
=
2m
\left(
\left|\frac{A+B}{\sqrt2}\right|^2
-
\left|\frac{A-B}{\sqrt2}\right|^2
\right).
\]

### 第七阶段：评价像维数判据

建议文件：

```text
D5/S3/Weil/ZetaBridge/OffLineEvaluationRank.lean
```

形式化二维像包含负交换方向。

### 第八阶段：有限 Gram 正性塔

建议文件：

```text
D5/S3/Weil/GNS/FiniteGramPositivity.lean
```

形式化正泛函的 Gram PSD 与零范数传播。

### 第九阶段：全局 localization seam

该阶段需要新的解析输入，不能仅靠有限线性代数完成。应明确记录：

- complex interpolation；
- compact support；
- exponential type；
- infinite zero control；
- prime/archimedean tails；
- form-core closure。

---

## 37.49 可证伪的实验与计算任务

尽管最终目标是解析定理，本节产生若干可计算问题。

### 任务 A：离线双点评价条件数

给定假想：

\[
\gamma=t-i\delta,
\]

对有限测试基 \(g_1,\ldots,g_N\)，计算矩阵：

\[
M_\gamma
=
\begin{pmatrix}
\widehat g_1(\gamma)&\cdots&\widehat g_N(\gamma)\\
\widehat g_1(\overline\gamma)&\cdots&\widehat g_N(\overline\gamma)
\end{pmatrix}.
\]

研究：

\[
\sigma_{\min}(M_\gamma).
\]

若：

\[
\sigma_{\min}>0,
\]

有限测试族已经能生成两个独立评价方向。

### 任务 B：目标负方向与其他 orbit 泄漏

解约束优化：

\[
\min_c
\quad
Q_\rho\left(\sum_jc_jg_j\right)
+
\lambda
\sum_{\rho'\neq\rho}
\left|
E_{\rho'}
\left(\sum_jc_jg_j\right)
\right|^2.
\]

它测量局部负方向能否在有限测试空间中与全局泄漏分离。

### 任务 C：记录互补模拟

构造二地址 record overlap \(c\)，绘制：

\[
\mathcal D=\sqrt{1-|c|^2},
\qquad
\mathcal V=|c|.
\]

并验证 unread \(J\)-期望按 \(c\) 衰减。

### 任务 D：有限 Gram 最小特征值

对递增测试空间计算：

\[
\lambda_{\min}(\Gamma_{\Omega,m}).
\]

区分：

- 稳定正下界；
- 逼近零的退化；
- 出现负特征值。

这些数值任务不能证明 RH，但可以检验本节提出的闭合机制是否具有合理尺度。

---

## 37.50 本节的最终统一

项目中的正锥、量子力学与观察者不应再分别理解为：

\[
\text{正性条件},
\qquad
\text{概率理论},
\qquad
\text{观看主体}.
\]

更准确的统一是：

\[
\boxed{
\text{正锥}
=
\text{形式坐标成为可实现状态／问题的门};
}
\]

\[
\boxed{
\text{量子力学}
=
\text{矩阵正锥塔、非交换上下文、
条件化 instrument 与全局关联余量的网络};
}
\]

\[
\boxed{
\text{观察者}
=
\text{选择 operator system，
通过 instrument 写入记录中心，
沿动力学生成预测闭包，
并用 GNS 自配对审计自身可实现性的结构}.
}
\]

RH 在该框架中的最强表述不是：

\[
\text{所有零点碰巧位于 }\Re s=\frac12.
\]

而是：

\[
\boxed{
\text{zeta 观察者的每个平方测试，
在反射以后仍然保持为同一评价纤维中的对角自配对，
从而允许全局正 GNS 完成。}
}
\]

离线零点则表示：

\[
\boxed{
\text{一个本应产生范数平方的自观察，
被拆成两个镜像纤维之间的符号不定相干。}
}
\]

因此：

\[
\boxed{
\text{临界线}
=
\text{评价地址对角}
+
\text{状态—effect 自对偶接缝}
+
\text{GNS 正完成}.
}
\]

而：

\[
\boxed{
\text{RH 证明的可能核心}
=
\text{证明 prime-side 记录、矩阵序转换和 Weil 平方测试
不允许一个非零的离线交叉相干 observer section}.
}
\]

---

## 37.51 严格非主张

1. 本节不声称任何物理意识实体参与 zeta 零点的形成。
2. 本节不声称 zeta 零点是物理 qubit。
3. 本节不声称任意正锥都能推出临界线。
4. 本节不声称标量正性足以替代完全正性。
5. 本节不声称 operator system 预测闭包已经在 Lean 中实现。
6. 本节不声称环境记录 fixed algebra 的一般有限维直和分解已经形式化。
7. 本节不声称 record–coherence 互补已经从 prime ledger 构造。
8. 本节不声称复平面左右侧别是可公开复制的经典变量。
9. 本节不把离线二地址模型解释为真实量子测量实验。
10. 本节不把 block-positive 纠缠见证与 Weil 负方向视为同一个具体锥。
11. 本节不声称单个离线轨道的局部负方向自动压过全部其他显式公式项。
12. 本节不声称双点评价映射已经被证明满射。
13. 本节不声称存在同时压制无限其他零点的测试函数列。
14. 本节不声称 prime/pole/archimedean 余项已经在该局域化中受控。
15. 本节不声称第 36 节 RH defect atlas 已经升级为实际矩阵有序 pro-object。
16. 本节不声称任意 compatible positive section 都来自真实 zeta 本体。
17. 本节不声称存在 off-critical character exclusion 定理。
18. 本节不声称 prime-axis \(\ell^2\) 阈值已经给出完整 rigged Hilbert triple。
19. 本节不声称逐层 Gram PSD 自动推出全局 GNS 正完成。
20. 本节不声称有限测试层已经形成 Weil 二次型的 form core。
21. 本节不从函数方程的 Hermitian 性直接推出 RH。
22. 本节不以“对角缺陷”这一元解释替代具体解析估计。
23. 本节新增定理均为纸面推导；未经 Lean kernel 验证不得标记为 `Closed`。
24. 本节没有证明 Riemann 假设。


# 38. 追加：界面因果完成、区分生成、熵增量与对角时间化
## Interface–Causal Completion, Distinction Genesis, Entropic Innovation, and Diagonal Temporalization

本节把前文的离散分类—逆完成研究法、矩阵有序观察者、环境记录中心、闭合缺陷、最小作用量与对角逃逸进一步统一为一套“界面因果完成演算”。

这一推进来自一个更基础的问题：

> 若一切可命名概念都是对某个更深关系对象的离散切分，那么“存在”“取反”“因果”“时间”“熵”“连续完成”之间究竟是什么依赖关系？

本节的核心修正是：

\[
\boxed{
\text{原初操作不是孤立的取反，而是带总体的界面切分。}
}
\]

取反只有在总体、类型或 order unit 已经给定以后才可定义。经典事件的补为：

\[
A^\complement=U\setminus A,
\]

量子 effect 的补为：

\[
E^\perp=I-E.
\]

所以“反里有一切”可以获得一个严格而有限定的含义：

\[
\boxed{
E^\perp=I-E
}
\]

确实显式引用总体 \(I\)，但它不是从虚无中创造总体；它把总体作为定义参数带入反面。更强地，若补运算写成：

\[
c_I(E)=I-E,
\]

则：

\[
\boxed{
I=c_I(0).
}
\]

因此补运算本身已经编码了其 ambient total。所谓“反里有一切”是一个依赖与编码命题，而不是“反先于一切”或“反创造一切”的因果命题。

本节建立以下主链：

\[
\boxed{
\text{总体}
\to
\text{界面切分}
\to
\text{离散分类}
\to
\text{信息不等式}
\to
\text{闭合余量}
\to
\text{新坐标}
\to
\text{逆完成}
\to
\text{对角审计}
\to
\text{逃逸、时间化或类型提升}.
}
\]

其中：

- 信息不等式描述界面删除了多少可区分性；
- 等号描述界面是否在指定任务上充分、可恢复或闭合；
- 熵增量描述每次 refinement 新增多少分类；
- 因果增量描述这些新分类中多少真正影响未来；
- 对角化检查当前分类系统能否把自己的分类器也纳入同一层；
- 时间并不由逻辑否定单独产生，而可能是静态闭合失败被序列化后的实现方式；
- 物理时间箭头还需要记录增长与局部不可逆控制，而不仅是一个无固定点迭代。

---

## 38.1 三种“离散”必须分开

本节使用“离散”时，至少区分以下三种含义。

### 38.1.1 拓扑离散

空间 \(X\) 拓扑离散，表示每个单点集合均为开集。

### 38.1.2 分类离散

给定接口：

\[
q:X\to Y,
\]

它诱导等价关系：

\[
x\sim_qx'
\iff
q(x)=q(x').
\]

即使 \(Y=\mathbb R\)、\(\mathbb C\) 或 Hilbert 空间，选择 \(q\) 这一“方面”本身仍然把整体状态切分成可区分类。

### 38.1.3 记录离散

一个连续或量子过程经过 instrument 与稳定账本以后，产生结果标签：

\[
r\in R.
\]

\(R\) 可以有限或可数，而底层状态空间仍然连续。

因此：

\[
\boxed{
\text{概念离散}
\neq
\text{拓扑离散}
\neq
\text{记录离散}.
}
\]

本节主要研究的是分类离散与记录离散如何在无限 refinement 中生成完成对象。

---

## 38.2 界面的最小定义

### 定义 38.1（界面）

一个界面是一个态射：

\[
q:X\to Y,
\]

其中 \(X\) 是候选整体状态空间，\(Y\) 是某个可表达读出空间。

界面定义相对同一性：

\[
x\sim_qx'
\iff
q(x)=q(x').
\]

### 定义 38.2（界面 refinement）

若存在：

\[
p:Y'\to Y
\]

使：

\[
q=p\circ q',
\]

则称 \(q'\) 比 \(q\) 更精细，记为：

\[
q\preceq q'.
\]

这等价于：

\[
\ker q'\subseteq\ker q
\]

在线性情形成立。

所以 refinement 的方向是：

\[
\boxed{
\text{更精细界面}
\longrightarrow
\text{更粗界面}
}
\]

通过遗忘映射下降。

### 定义 38.3（界面闭合）

给定任务族 \(\mathcal T\)，若任何两个在 \(q\) 下不可区分的整体状态，对全部任务均不可区分，则称 \(q\) 对 \(\mathcal T\) 闭合。

例如对未来预测任务：

\[
q(x)=q(x')
\Longrightarrow
q(T^kx)=q(T^kx')
\quad
\forall k\ge0.
\]

---

## 38.3 存在的四层结构

“存在”不能只用一个布尔量覆盖。

### 定义 38.4（类型存在）

\[
x:X
\]

表示 \(x\) 是类型 \(X\) 中的一个项或候选对象。

### 定义 38.5（可区分存在）

相对于探针族 \(\mathcal Q\)，若存在 \(q\in\mathcal Q\) 和某个 \(y\) 使：

\[
q(x)\neq q(y),
\]

则称 \(x\) 具有可区分存在。

### 定义 38.6（因果存在）

若存在干预或未来读出 \(F\)，使 \(x\) 的不同取值导致未来分布改变，则称该区别具有因果存在。

在概率模型中可写为：

\[
P(F\mid do(X=x))
\neq
P(F\mid do(X=x')).
\]

### 定义 38.7（记录存在）

若某个区别被写入稳定记录中心或追加式账本，并能在以后再次读取，则称它具有记录存在。

所以：

\[
\boxed{
\text{类型存在}
\not\Rightarrow
\text{可区分存在}
\not\Rightarrow
\text{因果存在}
\not\Rightarrow
\text{记录存在}.
}
\]

反向蕴含在给定模型中可能成立，但需要额外假设。

---

## 38.4 补运算的类型依赖

### 定义 38.8（order-unit 补）

设 \(V\) 为有序向量空间，\(u\) 为 order unit。对 effect interval：

\[
[0,u]
=
\{e:0\le e\le u\},
\]

定义：

\[
e^\perp=u-e.
\]

### 定理 38.1（补运算编码总体）

令：

\[
c_u(e)=u-e.
\]

则：

\[
c_u(0)=u,
\qquad
c_u(u)=0,
\qquad
c_u(c_u(e))=e.
\]

因此 \(c_u\) 唯一决定 \(u\)，因为：

\[
\boxed{
u=c_u(0).
}
\]

#### 证明

直接计算：

\[
c_u(0)=u-0=u.
\]

其余等式同样直接。故补运算不是独立于总体的原始操作；它把总体 \(u\) 编码在自身对零元的作用中。证毕。

### 推论 38.1（不存在无类型的绝对补）

若没有指定 ambient order unit \(u\)，则表达式：

\[
u-e
\]

没有确定意义。不同的 \(u\) 给出不同补运算。

所以：

\[
\boxed{
\text{任何“非”都相对于一个已指定总体。}
}
\]

---

## 38.5 “先存在才有反”是结构顺序，不必是物理时间

补运算的定义依赖顺序为：

\[
X
\longrightarrow
\operatorname{Sub}(X)
\longrightarrow
\text{complement}.
\]

在集合论中，补是子对象上的操作；在量子理论中，effect 补是 order interval 上的操作。

所以：

\[
\boxed{
\text{ambient type}
\prec
\text{event/effect}
\prec
\text{complement}
}
\]

是定义依赖顺序。

但这不等于物理时间顺序。给定一次界面切分：

\[
u=e+(u-e),
\]

两侧在静态结构中同时被定义。

因此：

\[
\boxed{
\text{“此”与“非此”由同一次切分共同产生。}
}
\]

真正具有物理先后的，是：

\[
\text{状态}
\to
\text{instrument}
\to
\text{结果}
\to
\text{记录}.
\]

---

## 38.6 界面切分而非取反是更原始的对象

### 定义 38.9（二分界面）

二分界面由：

\[
(u,e,e^\perp)
\]

构成，满足：

\[
e+e^\perp=u.
\]

### 原理 38.1（共同生成）

静态界面并不先产生 \(e\) 再产生 \(e^\perp\)，而是通过选择 \(u\) 与 \(e\) 同时生成有序对：

\[
(e,u-e).
\]

所以原初结构是：

\[
\boxed{
\text{总体}
+
\text{边界}
+
\text{边界两侧}.
}
\]

### 反例 38.1（补运算本身不会生成连续完成）

一个有限 Boolean 代数对补封闭后仍然有限。反复执行：

\[
a\mapsto a^\complement
\]

不会自动增加新元素，也不会生成连续统。

所以：

\[
\boxed{
\text{离散到完成对象}
\neq
\text{单纯反复取反}.
}
\]

真正需要的是：

\[
\boxed{
\text{局部补}
+
\text{无限坐标}
+
\text{跨层相容}
+
\text{完成}.
}
\]

---

## 38.7 分类塔与逆完成

设：

\[
q_n:X\to C_n
\]

为逐层精化的分类接口，并存在：

\[
p_{n+1,n}:C_{n+1}\to C_n
\]

满足：

\[
q_n=p_{n+1,n}\circ q_{n+1}.
\]

得到逆系统：

\[
\mathbf C
=
(C_n,p_{n+1,n})_{n\ge0}.
\]

### 定义 38.10（形式完成）

\[
\widehat X_{\mathrm{form}}
=
\varprojlim_n C_n.
\]

一个元素为相容族：

\[
c=(c_n)_{n\ge0},
\qquad
p_{n+1,n}(c_{n+1})=c_n.
\]

### 定义 38.11（结构性无穷）

若不存在 \(N\) 使从 \(N\) 起所有 refinement 都不再增加可区分结构，则称该界面塔结构性无穷。

即：

\[
\forall N,\ \exists n>N
\]

使 \(q_n\) 严格细于 \(q_N\)。

---

## 38.8 二进制分类如何形成 Cantor 完成

取：

\[
C_n=\{0,1\}^n
\]

并令：

\[
p_{n+1,n}
\]

忘掉最后一位，则：

\[
\boxed{
\varprojlim_n\{0,1\}^n
\cong
\{0,1\}^{\mathbb N}.
}
\]

右侧在乘积拓扑下是紧致、完备、无孤立点、全不连通的 Cantor 空间。

这说明：

\[
\boxed{
\text{每一层坐标完全离散，逆完成仍可形成不可数完备对象。}
}
\]

但它不是连通连续统。因此“离散到连续”应在此处理解为：

\[
\boxed{
\text{有限坐标到无限完备状态空间},
}
\]

而不是自动得到连通空间。

---

## 38.9 对角反对象是一个完成 section

设：

\[
x_0,x_1,\ldots
\in
\{0,1\}^{\mathbb N}.
\]

定义：

\[
d(n)=1-x_n(n).
\]

则每个有限前缀：

\[
d_{\le N}
=
(d(0),\ldots,d(N-1))
\in
\{0,1\}^N
\]

与下一层相容，所以：

\[
d\in
\varprojlim_N\{0,1\}^N.
\]

而：

\[
d(n)\neq x_n(n),
\]

故：

\[
d\neq x_n
\quad
\forall n.
\]

### 定理 38.2（局部反转—全局逃逸）

对角构造不是把某个单独离散元素变成连续对象，而是：

1. 对每个已列对象选择一个自地址坐标；
2. 在该坐标执行局部补；
3. 将全部局部补拼成相容无限 section；
4. 得到逃出原枚举的完成对象。

所以：

\[
\boxed{
\text{对角化}
=
\text{局部离散取反}
+
\text{全局逆完成拼接}.
}
\]

---

## 38.10 “反里有一切”的第二个严格含义

对角对象 \(d\) 并未保存每个 \(x_n\) 的全部信息，但它对每个 \(x_n\) 保留一条关系性回应：

\[
d(n)=1-x_n(n).
\]

所以：

\[
\boxed{
\text{对角反对象是整个候选列表的反轮廓。}
}
\]

它“包含一切”的含义是：

\[
\boxed{
\text{它针对每一个已命名对象都保留至少一个逃逸证书。}
}
\]

这不是信息等价：

\[
d
\not\cong
(x_n)_{n\ge0}.
\]

---

## 38.11 sharp complement 与 unsharp complement

量子 effect 补：

\[
E^\perp=I-E
\]

在完整 effect interval 中有固定点：

\[
E=\frac I2.
\]

因此：

\[
E^\perp=E
\]

是可能的。

但对 sharp projection \(P=P^2=P^\ast\)，若：

\[
P=I-P,
\]

则：

\[
P=\frac I2,
\]

这与 \(P^2=P\) 在非零 Hilbert 空间中不相容。

### 定理 38.3（sharpness 与无固定点补）

在非零有限维 Hilbert 空间的投影集合上：

\[
P\mapsto I-P
\]

无固定点；在全部 effects 上则有固定点 \(I/2\)。

所以 Cantor–Lawvere 型对角逃逸若依赖“无固定点扭曲”，必须明确选择：

- sharp truth values；
- 或其他无固定点 codomain 扭曲。

不能把一般 effect complement 自动当成无固定点否定。

---

## 38.12 信息接口与数据处理缺陷

给定统计距离或信息量 \(M\)，若任何界面 \(q\) 满足单调性：

\[
M_X(x,y)
\ge
M_Y(qx,qy),
\]

定义界面信息缺陷：

\[
\boxed{
\delta_M(q;x,y)
=
M_X(x,y)-M_Y(qx,qy)
\ge0.
}
\]

### 定义 38.12（任务闭合）

若对指定 \((x,y)\)：

\[
\delta_M(q;x,y)=0,
\]

则称 \(q\) 对该信息任务闭合。

若对某类对象全部为零，则称其在该类上充分。

### 定理 38.4（组合缺陷链）

若：

\[
X\overset q\longrightarrow Y
\overset r\longrightarrow Z,
\]

且缺陷由严格差值定义，则：

\[
\boxed{
\delta_M(r\circ q;x,y)
=
\delta_M(q;x,y)
+
\delta_M(r;qx,qy).
}
\]

#### 证明

展开：

\[
M_X-M_Z
=
(M_X-M_Y)+(M_Y-M_Z).
\]

证毕。

所以信息损失沿界面串联可加。

---

## 38.13 经典因果闭合缺陷

设 \(P\) 表示完整过去，\(F\) 表示未来，当前界面为过去的确定函数：

\[
C=q(P).
\]

定义：

\[
\boxed{
\kappa(C)
=
I(P;F\mid C)
\ge0.
}
\]

### 定理 38.5（预测闭合判据）

在标准正则概率条件下：

\[
\kappa(C)=0
\]

当且仅当：

\[
P\longrightarrow C\longrightarrow F
\]

构成 Markov 链，即给定 \(C\) 后，完整过去对未来不再提供额外信息。

所以：

\[
\boxed{
\kappa(C)
=
\text{当前界面遗漏的未来相关信息}.
}
\]

---

## 38.14 refinement 精确分解因果余量

设 \(C'\) 比 \(C\) 更精细，并且：

\[
C=f(C').
\]

则：

\[
\boxed{
I(P;F\mid C)
=
I(C';F\mid C)
+
I(P;F\mid C').
}
\]

### 定理 38.6（因果创新恒等式）

定义：

\[
g(C'\mid C)
=
I(C';F\mid C).
\]

则：

\[
\boxed{
\kappa(C)-\kappa(C')
=
g(C'\mid C)
\ge0.
}
\]

所以 refinement 每加入一层坐标，其真正预测价值恰等于因果闭合缺陷的下降量。

### 推论 38.2（单调闭合）

\[
C\preceq C'
\Longrightarrow
\kappa(C')\le\kappa(C).
\]

---

## 38.15 熵创新与因果创新必须区分

若 \(C=f(C')\)，则：

\[
H(C')
=
H(C)
+
H(C'\mid C).
\]

定义分类创新：

\[
\boxed{
h(C'\mid C)
=
H(C'\mid C).
}
\]

同时：

\[
g(C'\mid C)
=
I(C';F\mid C).
\]

由条件互信息不超过条件熵：

\[
\boxed{
0\le g(C'\mid C)\le h(C'\mid C).
}
\]

定义因果效率：

\[
\eta(C'\mid C)
=
\begin{cases}
\dfrac{g(C'\mid C)}{h(C'\mid C)},&h>0,\\[1ex]
0,&h=0.
\end{cases}
\]

于是：

\[
0\le\eta\le1.
\]

其中：

- \(h>0,g=0\)：新增分类纯属与未来无关的 nuisance distinction；
- \(h=g>0\)：新增每一 bit 都与未来相关；
- \(0<g<h\)：新增分类只部分具有因果价值。

---

## 38.16 因果信息的望远镜分解

设：

\[
C_0\preceq C_1\preceq\cdots\preceq C_n
\]

为逐层精化界面，定义：

\[
g_k=I(C_{k+1};F\mid C_k).
\]

反复使用定理 38.6 得：

\[
\boxed{
\kappa(C_0)
=
\sum_{k=0}^{n-1}g_k
+
\kappa(C_n).
}
\]

因此：

\[
\boxed{
\text{初始因果余量}
=
\text{历次被新坐标捕获的因果信息}
+
\text{最终仍未捕获的余量}.
}
\]

这正是界面理论“不等式持续向等式推进”的精确版本。



## 38.17 有限熵预算与真正 refinement 次数

若完整过去 \(P\) 为有限熵随机变量，且：

\[
C_n=q_n(P),
\]

则：

\[
H(C_n)\le H(P).
\]

又因为：

\[
H(C_n)
=
H(C_0)
+
\sum_{k=0}^{n-1}H(C_{k+1}\mid C_k),
\]

所以：

\[
\boxed{
\sum_{k=0}^{\infty}
h_k
\le
H(P)-H(C_0)
\le H(P).
}
\]

### 推论 38.3（大创新次数界）

对任意 \(\varepsilon>0\)，满足：

\[
h_k\ge\varepsilon
\]

的层数至多为：

\[
\boxed{
\frac{H(P)}{\varepsilon}.
}
\]

因此有限熵系统可以无限 refinement，但不能无限多次产生固定大小的独立新信息。

这与有限状态预测塔中的“有限次真正分裂后永久稳定”同属一个信息预算原则。

---

## 38.18 逆完成中的 sigma-代数极限

令：

\[
\mathcal F_n=\sigma(C_n),
\]

则：

\[
\mathcal F_0
\subseteq
\mathcal F_1
\subseteq
\cdots.
\]

定义极限观察代数：

\[
\boxed{
\mathcal F_\infty
=
\sigma\left(
\bigcup_{n\ge0}\mathcal F_n
\right).
}
\]

对任意可积未来变量 \(Y\)，条件期望：

\[
M_n
=
\mathbb E[Y\mid\mathcal F_n]
\]

构成 martingale，并在通常条件下收敛到：

\[
\boxed{
M_\infty
=
\mathbb E[Y\mid\mathcal F_\infty].
}
\]

所以离散分类塔的连续完成可以被具体实现为：

\[
\boxed{
\text{全部有限读出的生成 sigma-代数}.
}
\]

这不是把某一层变成连续对象，而是把所有有限界面共同闭包。

---

## 38.19 因果连续完成

### 定义 38.13（因果完成）

若：

\[
\lim_{n\to\infty}
I(P;F\mid C_n)
=
0,
\]

则称界面塔 \((C_n)\) 对未来 \(F\) 因果完成。

这意味着：

\[
\mathcal F_\infty
\]

保存了全部与 \(F\) 有关的过去信息，但不要求恢复完整 \(P\)。

### 定义 38.14（本体完成）

若：

\[
\sigma(P)
\subseteq
\mathcal F_\infty
\quad
\text{模零集},
\]

则称该塔恢复完整过去。

所以：

\[
\boxed{
\text{本体完成}
\Longrightarrow
\text{因果完成},
}
\]

但反向不成立。

一个最小充分统计量可以完全预测未来，却仍商掉与未来无关的过去细节。

---

## 38.20 可预测存在与因果存在

若两个状态 \(x,y\) 对当前所有读出相同：

\[
q_n(x)=q_n(y),
\]

但未来分布不同，则其差异属于：

\[
\boxed{
\text{当前不可见、未来有效的因果余量}.
}
\]

若在全部 refinement 后仍无法区分，但未来也完全相同，则该差异对指定预测任务没有因果存在。

因此：

\[
\boxed{
\text{存在相对于任务族而分层。}
}
\]

项目中的观察者商不应要求恢复所有世界细节，而应明确：

- 状态分离任务；
- 未来预测任务；
- 控制任务；
- 记录审计任务；
- 自描述任务。

每种任务有自己的闭合缺陷。

---

## 38.21 量子数据处理缺陷

对量子通道：

\[
\Phi:\rho\mapsto\Phi(\rho),
\]

定义相对熵缺陷：

\[
\boxed{
\delta_\Phi(\rho,\sigma)
=
D(\rho\Vert\sigma)
-
D(\Phi\rho\Vert\Phi\sigma)
\ge0.
}
\]

它测量通道删除了多少状态可区分性。

### 定理 38.7（量子组合缺陷链）

对通道：

\[
\Phi:\mathcal A\to\mathcal B,
\qquad
\Psi:\mathcal B\to\mathcal C,
\]

有：

\[
\boxed{
\delta_{\Psi\circ\Phi}(\rho,\sigma)
=
\delta_\Phi(\rho,\sigma)
+
\delta_\Psi(\Phi\rho,\Phi\sigma).
}
\]

所以量子界面的可区分性损失也沿粗粒化链逐层累积。

### 原理 38.2（等号即恢复）

在适当支撑与有限性条件下：

\[
\delta_\Phi(\rho,\sigma)=0
\]

对应存在恢复映射，使 \(\rho,\sigma\) 可由粗化后状态重建。

所以界面理论的基本形态是：

\[
\boxed{
\text{数据处理不等式}
\to
\text{缺陷}
\to
\text{等号条件}
\to
\text{恢复闭合}.
}
\]

---

## 38.22 量子因果缺陷与条件互信息

对三方状态 \(\rho_{ABC}\)，量子条件互信息：

\[
\boxed{
I(A:C\mid B)
=
S(AB)+S(BC)-S(B)-S(ABC)
\ge0.
}
\]

它可以被解释为：

\[
\boxed{
\text{给定界面 }B
\text{ 后，过去／输入 }A
\text{ 对未来／输出 }C
\text{ 仍保留的关联余量}.
}
\]

当：

\[
I(A:C\mid B)=0,
\]

状态具有量子 Markov 结构，并允许相应恢复。

所以经典因果闭合：

\[
I(P;F\mid C)=0
\]

与量子因果闭合：

\[
I(A:C\mid B)=0
\]

共享同一个“界面充分性”骨架。

---

## 38.23 正锥对零概率的放大

对密度状态 \(\rho\ge0\) 与投影 \(P\)，若：

\[
\operatorname{Tr}(\rho P)=0,
\]

则：

\[
P\rho=\rho P=0.
\]

因此一个标量零概率通过正锥刚性放大为整个支撑块消失。

这说明：

\[
\boxed{
\text{信息界面的零权重}
+
\text{正性}
\Longrightarrow
\text{几何支撑约束}.
}
\]

所以信息论中的“零 bit”在矩阵正序中可以对应高维自由度的整体排除。

---

## 38.24 选择、记录与反事实

给定二结果 instrument：

\[
\mathcal I_0,\mathcal I_1,
\]

effect 为：

\[
E_r=\mathcal I_r^\ast(I),
\qquad
E_0+E_1=I.
\]

测量以前：

\[
E_0,E_1
\]

共同定义两个可能分支。

测量以后，若结果 \(r=0\) 被记录，则：

\[
\text{actual}=0,
\qquad
\text{counterfactual}=1
\]

只相对于该已形成历史成立。

因此：

\[
\boxed{
\text{逻辑补在分支以前已定义；}
}
\]

\[
\boxed{
\text{反事实身份在实际记录以后才相对于历史确定。}
}
\]

所以“反”的逻辑依赖与“反事实”的因果依赖不能混同。

---

## 38.25 记录中心与事实存在

环境记录通道选择固定代数：

\[
\operatorname{Fix}(\mathcal R),
\]

其中心：

\[
Z(\operatorname{Fix}(\mathcal R))
\]

承载可公开复制的经典标签。

### 定义 38.15（事实存在）

若事件 \(e\) 的记录投影进入稳定中心，并可被多个后续接口一致读取，则称 \(e\) 成为当前观察者网络中的事实。

因此：

\[
\boxed{
\text{事实}
=
\text{进入稳定公共中心的区别}.
}
\]

这比“某个量子 effect 在代数中存在”更强，也比“某个结果概率非零”更强。

---

## 38.26 记录时间与动力时间

必须区分：

### 动力时间

\[
\rho_t=\alpha_t(\rho_0).
\]

整体动力学可以可逆且保持熵。

### refinement 时间

\[
\mathcal S_0
\subseteq
\mathcal S_1
\subseteq
\cdots
\]

表示观察者问题空间扩张。

### 记录时间

\[
\mathcal Z_0
\subseteq
\mathcal Z_1
\subseteq
\cdots
\]

表示稳定经典账本增长。

三者不自动相同：

\[
\boxed{
t_{\mathrm{dyn}}
\neq
n_{\mathrm{ref}}
\neq
r_{\mathrm{record}}.
}
\]

只有给出耦合律后，才能把它们解释成同一物理时钟的不同坐标。

---

## 38.27 记录箭头的最小定义

### 定义 38.16（记录箭头）

若记录代数满足：

\[
\mathcal Z_t\subseteq\mathcal Z_{t+1}
\]

且不存在观察者允许的逆操作从当前控制域完整删除或恢复全部记录差异，则称该观察者具有记录时间箭头。

### 定义 38.17（记录创新）

若 \(R_{t+1}\) 是新增记录标签，定义：

\[
h_t^{\mathrm{rec}}
=
H(R_{t+1}\mid\mathcal Z_t).
\]

若：

\[
h_t^{\mathrm{rec}}>0,
\]

则新时刻增加了当前账本不能预测的新事实。

所以时间箭头可以被测量为：

\[
\boxed{
\text{稳定记录创新的累积}.
}
\]

---

## 38.28 complement 本身不产生熵箭头

补运算：

\[
e\mapsto u-e
\]

是 involution：

\[
(e^\perp)^\perp=e.
\]

因此它可逆，不会仅凭自身产生不可逆熵增。

同样，Boolean flip：

\[
0\leftrightarrow1
\]

是双射。

所以：

\[
\boxed{
\text{取反}
\not\Rightarrow
\text{时间箭头}.
}
\]

时间箭头需要：

- 非单射粗粒化；
- 环境记录扩散；
- 局部不可逆控制；
- 或追加式账本。

---

## 38.29 无固定点如何被时间化

设 \(X\) 为有限非空集合，\(T:X\to X\) 无固定点。

### 定理 38.8（有限无固定点动力学）

对任意 \(x\in X\)，轨道：

\[
x,T(x),T^2(x),\ldots
\]

最终进入长度至少为 \(2\) 的周期。

#### 证明

有限性保证存在 \(i<j\) 使：

\[
T^i(x)=T^j(x).
\]

所以轨道从 \(T^i(x)\) 起周期。若周期长度为 \(1\)，则存在固定点，与假设矛盾。证毕。

### 推论 38.4（Boolean 反转）

对：

\[
T(x)=1-x
\]

于 \(\{0,1\}\)，每条轨道均为二周期：

\[
0\to1\to0\to\cdots.
\]

所以一个无法静态固定的自反馈规则可以通过序列化为轨道而继续实现。

---

## 38.30 静态闭合失败的四种命运

一个无固定点或闭合失败结构并不只能产生时间。

它至少有四种处理方式：

### 1. 逃逸

加入一个不在当前分类中的新对象。

### 2. 时间化

把不能同时满足的条件展开为迭代轨道。

### 3. 类型提升

把问题移动到更高元层或更丰富 codomain。

### 4. 部分化

承认某些自应用没有定义值。

所以：

\[
\boxed{
\text{对角缺陷}
\not\Rightarrow
\text{物理时间必然产生}.
}
\]

更准确的是：

\[
\boxed{
\text{时间化是闭合缺陷的一种动态实现。}
}
\]

---

## 38.31 时间作为非同时可满足条件的序列化

若系统要求：

\[
x=F(x)
\]

但无解，可以考虑：

\[
x_{t+1}=F(x_t).
\]

此时：

\[
\boxed{
\text{一个不能在单一状态中同时闭合的关系，
被排列成前后状态之间的转换。}
}
\]

这可称为：

### 原理 38.3（时间化原理）

静态一致性失败若被稳定更新规则吸收，则该失败可以表现为动态轨道。

但它成为物理时间还要求：

- 更新具有因果可实现性；
- 状态可被连续或离散时钟参数化；
- 记录或可观测量能够区分轨道阶段；
- 不是纯粹重标记。

---

## 38.32 区分生成的因果链

界面理论中的最小因果链为：

\[
\boxed{
\text{未记录状态}
\to
\text{交互界面}
\to
\text{结果分支}
\to
\text{稳定记录}
\to
\text{新因果条件}.
}
\]

稳定记录一旦形成，后续决策可以条件于该记录：

\[
P(A_{t+1}\mid R_t).
\]

所以记录不仅描述过去，也改变未来可用策略。

因此：

\[
\boxed{
\text{事实形成}
=
\text{一个区别进入以后因果模型的条件变量集合}.
}
\]

---

## 38.33 因果闭合与控制闭合不同

预测闭合要求：

\[
I(P;F\mid C)=0.
\]

控制闭合还要求：对所有允许动作 \(a\)，界面 \(C\) 足以确定最优行为或未来转移。

可以定义：

\[
\kappa_{\mathrm{ctrl}}(C)
=
\sup_a
I(P;F_a\mid C).
\]

或用最优价值差：

\[
\Delta V(C)
=
V^\ast(P)-V^\ast(C).
\]

因此：

\[
\boxed{
\text{预测充分}
\not\Rightarrow
\text{控制充分}
}
\]

在动作会改变未来分布的情况下成立。

开放问题研究必须明确研究的是哪一种闭合。

---

## 38.34 界面作用量

给定 refinement 塔 \((C_n)\)，定义：

\[
h_n=H(C_{n+1}\mid C_n),
\]

\[
g_n=I(C_{n+1};F\mid C_n),
\]

\[
\kappa_n=I(P;F\mid C_n).
\]

可以定义界面作用量：

\[
\boxed{
\mathcal A_{\mathrm{int}}
=
\sum_{n\ge0}
\left(
\alpha_n h_n
-
\beta_n g_n
+
\gamma_n\kappa_n
\right),
}
\]

其中权重非负。

它惩罚：

- 过多分类成本；
- 剩余因果余量；

并奖励：

- 每层捕获的未来相关信息。

这是一种 information-bottleneck 型研究目标，但不应自动等同于物理作用量。

---

## 38.35 最小充分界面

### 定义 38.18（预测充分）

\[
I(P;F\mid C)=0.
\]

### 定义 38.19（最小预测充分）

若 \(C\) 预测充分，并且任何严格粗化 \(C'\prec C\) 都不再预测充分，则称 \(C\) 最小预测充分。

在适当模型中，它对应 causal state 或最小充分统计量。

所以：

\[
\boxed{
\text{观察者不是越精细越好；}
}
\]

\[
\boxed{
\text{理想观察者是在闭合任务所需信息上最小。}
}
\]

这与前文唯一最小 Hilbert 完成、经济最小套保方向共享同一个“无冗余完成”原则。

---

## 38.36 缺陷—见证—新坐标循环

设第 \(n\) 层界面有缺陷：

\[
\delta_n>0.
\]

若能构造见证 \(w_n\)，使：

\[
w_n(x)\neq w_n(y)
\]

恰好区分当前商掉但任务相关的状态，则定义：

\[
\boxed{
q_{n+1}(x)
=
(q_n(x),w_n(x)).
}
\]

理想情况下：

\[
\delta_{n+1}<\delta_n.
\]

于是形成研究循环：

\[
\boxed{
\text{界面}
\to
\text{不等式}
\to
\text{缺陷}
\to
\text{见证}
\to
\text{新坐标}
\to
\text{更细界面}.
}
\]

这就是开放问题可持续研究的基本发动机。

---

## 38.37 一般缺陷见证的类型

不同结构中，见证分别为：

\[
\begin{aligned}
\text{Hilbert 子空间}
&:\quad
r=(I-P_M)x;\\
\text{闭凸锥}
&:\quad
w\in C^\vee
\text{ 分离 }x\notin C;\\
\text{概率因果}
&:\quad
w=\text{仍影响未来的隐藏统计量};\\
\text{量子通道}
&:\quad
w=\text{恢复失败方向};\\
\text{上下文拼接}
&:\quad
w=\text{非平凡 cocycle 或无全局 section 证书};\\
\text{对角化}
&:\quad
w=\text{逃出当前枚举的 anti-section}.
\end{aligned}
\]

所以“余量成为观察者”不是只发生在 Hilbert 空间，而是一个更一般的对偶机制。

---

## 38.38 形式完成、可容许完成与真实完成

对分类塔：

\[
(C_n,p_{n+1,n}),
\]

定义：

\[
\widehat X_{\mathrm{form}}
=
\varprojlim_n C_n.
\]

再加入统一条件：

\[
\sup_n E_n(c_n)<\infty,
\]

正性、可积性、局部性、复杂度或 form-core 条件，得到：

\[
\widehat X_{\mathrm{adm}}
\subseteq
\widehat X_{\mathrm{form}}.
\]

若有真实对象映射：

\[
\eta:X\to\widehat X_{\mathrm{adm}},
\]

则：

\[
\widehat X_{\mathrm{real}}
=
\eta(X).
\]

所以：

\[
\boxed{
\widehat X_{\mathrm{real}}
\subseteq
\widehat X_{\mathrm{adm}}
\subseteq
\widehat X_{\mathrm{form}}.
}
\]

形式相容绝不自动等于真实存在。

---

## 38.39 “存在从哪里来”的三种形式模型

内部补运算不能生成自己的 ambient type。若继续追问总体来源，至少有三种数学建模方式。

### 38.39.1 基础给定

某个 \(X_0\)、order unit 或初始状态作为原始数据。

### 38.39.2 无终端逆塔

不存在最终总体，只有：

\[
\cdots
\to X_2
\to X_1
\to X_0.
\]

每一层总体仍是更高层的投影。

### 38.39.3 自生成固定点

寻找：

\[
X\simeq F(X).
\]

但固定点的存在、唯一性与稳定性均是额外定理，不能由“自指”自动保证。

因此：

\[
\boxed{
\text{界面理论解释相对对象如何产生，}
}
\]

但不会仅凭取反回答绝对本体为何存在。

---

## 38.40 范畴式存在与补的依赖

在范畴语言中：

- 对象 \(X\) 的存在不同于 \(X\) 中全局点的存在；
- 全局点是态射：

\[
1\to X;
\]

- 子对象是单态射：

\[
A\hookrightarrow X;
\]

- 补是对 \(\operatorname{Sub}(X)\) 的额外结构。

所以：

\[
\boxed{
X
\to
\operatorname{Sub}(X)
\to
\text{complement}
}
\]

是类型依赖。

补不能从无对象状态产生 \(X\)，也不能自动产生一个全局点 \(1\to X\)。

---

## 38.41 分类格不一定具有补

事件代数可能具有补，但“分类本身”的偏序通常只是 partition lattice。

给定两个分类 \(q_1,q_2\)，可以研究：

- 公共粗化；
- 共同 refinement；
- join 与 meet。

但一般不存在一个规范“分类补” \(q^\perp\)，使其与 \(q\) 恢复完整对象。

因此：

\[
\boxed{
\text{事件取反}
\neq
\text{坐标系取反}
\neq
\text{分类补}.
}
\]

把“对当前分类未看见的一切”当成一个单一补对象，通常需要额外 Hilbert 正交、核空间或 Boolean 结构。

---

## 38.42 连续完成是关系闭包，不是最大点

若每个概念层仍可 refinement，则“本体”不应再次被简化成隐藏在背后的最大单点。

更稳定的表述是：

\[
\boxed{
\text{本体}
=
\text{全部界面之间的 refinement、相容与实现关系}.
}
\]

普通逆极限只是该关系图在某个范畴中的一种 realization。

这避免把“连续统”再次绝对化为最终概念。



## 38.43 开放问题的界面化重写

一个开放问题不再首先写成：

\[
\mathsf P\ ?
\]

而应拆成以下数据：

\[
\boxed{
\mathfrak P
=
\left(
I,
\{C_i\},
\{p_{ji}\},
\{A_i\},
\{E_i\},
\{\delta_i\},
\eta
\right).
}
\]

其中：

\[
\begin{aligned}
I
&=\text{refinement 索引};\\
C_i
&=\text{第 }i\text{ 层分类};\\
p_{ji}
&=\text{遗忘／粗化映射};\\
A_i
&=\text{可容许子对象、正锥或约束集};\\
E_i
&=\text{能量、复杂度或作用量};\\
\delta_i
&=\text{闭合缺陷};\\
\eta
&=\text{真实对象到分类塔的 realization map}.
\end{aligned}
\]

开放问题被转换为：

- 是否存在 admissible section；
- 是否存在坏 section；
- section 是否唯一；
- 作用量是否有统一界；
- 缺陷是否只能为零；
- 局部分类是否能持续提升；
- 形式 section 是否真实可实现。

---

## 38.44 七种开放问题缺陷

定义：

\[
\boxed{
\mathbf D
=
(
D_{\mathrm{stage}},
D_{\mathrm{lift}},
D_{\mathrm{glue}},
D_{\mathrm{adm}},
D_{\mathrm{compact}},
D_{\mathrm{derived}},
D_{\mathrm{diag}}
).
}
\]

### 阶段缺陷

某个有限层已经为空。

### 提升缺陷

当前合法分类没有下一层 lift。

### 拼接缺陷

局部 section 存在，但不能形成全局 section。

### 可容许性缺陷

形式相容，但违反正性、能量、可积性、局部性或复杂度条件。

### 紧致性缺陷

有限层解存在，但质量逃向高频、无穷远或锥边界，不能取真实极限。

### 导出缺陷

普通逆极限遗漏 \(\lim^1\)、上同调或更高一致性障碍。

### 对角缺陷

某一层声称列尽包括自身分类器在内的全部同类型对象，而产生逃逸 anti-section。

---

## 38.45 “坏对象”是否能持续提升

设：

\[
B_n\subseteq C_n
\]

表示第 \(n\) 层的坏分类。

定义坏对象提升纤维：

\[
L_{n+1}(b_n)
=
p_{n+1,n}^{-1}(b_n)
\cap B_{n+1}.
\]

若：

\[
L_{n+1}(b_n)=\varnothing,
\]

则该坏模式在第 \(n+1\) 层死亡。

若每个坏模式都能继续提升，且系统满足适当紧致／满射条件，则可能形成全局坏 section。

所以证明“坏对象不存在”的真正目标是找出：

\[
\boxed{
\text{坏分类第一次无法继续提升的接口。}
}
\]

---

## 38.46 纯离散非空 refinement 不会自动消灭坏 section

若每层 \(B_n\) 都是非空有限集合，且构成真正的 cofiltered 逆系统，则普通逆极限通常非空。

因此：

\[
\boxed{
\text{离散性本身不排除坏本体；}
}
\]

甚至可能通过紧致性保证一个相容坏 section。

所以证明力量必须来自：

- 过渡映射不满射；
- 可容许性约束；
- 统一正性；
- 紧致性失败；
- gluing obstruction；
- 收缩；
- 奇偶；
- 对角刚性。

---

## 38.47 缺陷收缩刚性

设缺陷完成空间为 \(D\)，并有算子：

\[
R:D\to D.
\]

若候选缺陷 \(d\) 满足：

\[
Rd=d
\]

且：

\[
\|Rv\|\le\kappa\|v\|,
\qquad
\kappa<1,
\]

则：

\[
\|d\|
=
\|Rd\|
\le
\kappa\|d\|,
\]

所以：

\[
\boxed{
d=0.
}
\]

这是一切“同一目标可以以严格更低成本重复完成”论证的抽象核心。

---

## 38.48 奇偶冲突刚性

设对合：

\[
J^2=I.
\]

若同一个规范缺陷被整体对称性要求：

\[
Jd=d,
\]

但被法向、侧别或对角结构要求：

\[
Jd=-d,
\]

则：

\[
d=-d
\]

从而：

\[
\boxed{
d=0.
}
\]

这给出另一类开放问题终结机制。

---

## 38.49 最小作用量与闭合等式

设闭合缺陷 \(\delta\ge0\)，定义作用量：

\[
\mathcal A=\Phi(\delta)
\]

其中 \(\Phi\) 严格增且：

\[
\Phi(0)=0.
\]

则：

\[
\mathcal A=0
\iff
\delta=0.
\]

在线性 Hilbert 情形：

\[
\mathcal A(x;M)
=
\frac12\operatorname{dist}(x,M)^2.
\]

在因果界面中可取：

\[
\mathcal A_{\mathrm{causal}}(C)
=
I(P;F\mid C).
\]

在量子通道中可取：

\[
\mathcal A_{\mathrm{info}}(\Phi)
=
D(\rho\Vert\sigma)
-
D(\Phi\rho\Vert\Phi\sigma).
\]

所以“最小作用量”在本节不是一个统一物理常数，而是：

\[
\boxed{
\text{闭合不等式距离等号有多远的任务相关代价。}
}
\]

---

## 38.50 不等式—等式研究模板

对一个开放问题，应系统寻找：

\[
L(x)\ge R(x).
\]

然后定义：

\[
\delta(x)=L(x)-R(x).
\]

研究四个问题：

1. \(\delta=0\) 是否等价于目标闭合？
2. \(\delta>0\) 是否产生规范见证？
3. 见证是否能作为下一层坐标？
4. 是否存在保持目标而严格缩小 \(\delta\) 的变换？

若四步均成立，则开放问题可被转成缺陷刚性问题。

---

## 38.51 界面研究算法

### 步骤 1：确定任务

明确要保存的是：

- 状态身份；
- 未来预测；
- 控制价值；
- 正性；
- 记录；
- 全局拼接；
- 自描述。

### 步骤 2：选择最小分类

构造第 \(n\) 层接口：

\[
q_n:X\to C_n.
\]

### 步骤 3：证明粗化自然性

构造：

\[
p_{n+1,n}
\]

并证明：

\[
q_n=p_{n+1,n}\circ q_{n+1}.
\]

### 步骤 4：选择单调量

例如：

- 熵；
- 相对熵；
- 能量；
- 谱隙；
- 复杂度；
- 余空间范数；
- 锥距离。

### 步骤 5：定义闭合缺陷

\[
\delta_n\ge0.
\]

### 步骤 6：提取见证

从 \(\delta_n>0\) 构造新坐标或分离方向。

### 步骤 7：建立 admissibility

证明形式 section 满足统一界时才能成为真实对象。

### 步骤 8：进行对角审计

检查分类器是否试图在同一层列尽自身。

### 步骤 9：寻找刚性

寻找收缩、奇偶、正性、中心记录或 gluing obstruction。

---

## 38.52 量子力学中的依赖链

项目中的量子界面可以写成：

\[
\boxed{
\ast\text{-代数}
\to
\text{矩阵正锥塔}
\to
\text{状态—effect 配对}
\to
\text{operator system}
\to
\text{CP instrument}
\to
\text{记录中心}
\to
\text{预测闭包}
\to
\text{GNS 完成}
\to
\text{对角审计}.
}
\]

这里：

- 正锥决定可实现性；
- instrument 决定分支与状态更新；
- 记录中心决定经典事实；
- Heisenberg 塔决定未来充分性；
- GNS 把正自配对完成为 Hilbert 范数；
- contextuality 与 diagonalization 审计不同类型的全局闭合。

---

## 38.53 量子测量的因果创新

设结果记录为 \(R\)，未来读出为 \(F\)，测量前可访问状态摘要为 \(C\)。

新增记录的因果价值可写成：

\[
\boxed{
g_{\mathrm{meas}}
=
I(R;F\mid C).
}
\]

记录熵为：

\[
h_{\mathrm{meas}}
=
H(R\mid C).
\]

因此：

\[
0\le g_{\mathrm{meas}}\le h_{\mathrm{meas}}.
\]

若：

\[
g_{\mathrm{meas}}=0,
\]

则结果虽然随机，但对指定未来任务没有新增预测价值。

若：

\[
g_{\mathrm{meas}}=h_{\mathrm{meas}},
\]

则结果中的全部不确定性都与未来相关。

---

## 38.54 环境记录与时间箭头的定量差

设第 \(t\) 步环境复制产生记录 \(R_t\)，观察者可逆控制域为 \(\mathcal C_t\)。

定义累计记录量：

\[
K_T
=
H(R_1,\ldots,R_T).
\]

定义可逆控制容量：

\[
B_T
=
\log\dim\mathcal C_T
\]

或选定其他资源度量。

可定义记录压力：

\[
\boxed{
\Pi_T=K_T-B_T.
}
\]

若：

\[
\Pi_T\to+\infty,
\]

则观察者恢复全部记录所需资源持续超出其控制域。

这不是普适物理熵定律，而是一个观察者相对的恢复资源指标。

---

## 38.55 经典事实是中心化后的因果坐标

环境记录选择固定代数：

\[
\mathcal A_{\mathrm{fix}}.
\]

其中心投影：

\[
z_\alpha\in Z(\mathcal A_{\mathrm{fix}})
\]

给出可公开复制的分支标签。

未来操作若条件于 \(z_\alpha\)，则：

\[
z_\alpha
\]

从记录标签升级为因果坐标。

所以经典化的完整链是：

\[
\boxed{
\text{量子区别}
\to
\text{环境复制}
\to
\text{固定代数}
\to
\text{中心标签}
\to
\text{未来条件变量}.
}
\]

---

## 38.56 RH 的界面—因果重写

对 RH 研究，不应只列出零点坐标，而应构造多轴界面塔：

\[
C_n^{\mathrm{RH}}
=
\left(
\text{零点窗口},
\text{Li 阶数},
\text{Weil 测试空间},
\text{Nyman 生成元},
\text{prime 范围},
\text{spectral refinement}
\right)_n.
\]

一个假想离线本体是相容缺陷 section：

\[
d=(d_n).
\]

真正要审计：

1. 复平面离线坐标能否提升到所有 chart；
2. chart transitions 是否自然；
3. Weil 平方测试是否保持正 GNS；
4. prime-side 记录是否允许镜像交叉相干；
5. 非零 section 是否违反统一 admissibility；
6. 是否存在收缩或奇偶刚性迫使 \(d=0\)。

所以：

\[
\boxed{
\text{RH 本体问题}
=
\text{非零离线 section 是否能通过全部界面闭合审计}.
}
\]

---

## 38.57 RH 中的不等式—等式主线

Weil 正性型结构给出：

\[
Q(g)\ge0.
\]

临界线上的自配对呈现：

\[
|\widehat g(\gamma)|^2\ge0.
\]

离线镜像则产生：

\[
\widehat g(\gamma)
\overline{\widehat g(\overline\gamma)}.
\]

所以研究目标可表述为：

\[
\boxed{
\text{何时 Hermitian 交叉配对必须退化为同址正自配对？}
}
\]

这正是：

\[
\boxed{
\text{不定实值}
\longrightarrow
\text{非负值}
\longrightarrow
\text{范数平方}
}
\]

的等式化过程。

---

## 38.58 Navier–Stokes 的界面重写

令：

\[
C_N^{\mathrm{NS}}
=
\text{Fourier 模式 }|k|\le N
\text{ 的 Galerkin 分类}.
\]

遗忘映射删除高频模式。

形式 section 对应所有有限截断相容。

可容许性要求统一能量或临界范数界：

\[
\sup_N E_N(u_N)<\infty.
\]

闭合缺陷是高频余能：

\[
\delta_N
=
\sum_{|k|>N}
w(k)|\widehat u(k)|^2.
\]

真正问题不是每个有限层是否有解，而是：

\[
\boxed{
\text{高频因果／能量余量能否在极限中保持受控并趋零。}
}
\]

---

## 38.59 \(P\) versus \(NP\) 的界面重写

令 \(C_n\) 表示输入长度不超过 \(n\) 的求解行为。

每个固定 \(n\) 存在有限查表解并无意义。

真实 section 还要满足统一生成规则与复杂度：

\[
\operatorname{cost}(C_n)\le n^k
\]

对固定 \(k\) 成立。

所以缺陷是：

\[
\boxed{
D_{\mathrm{uniform}}
+
D_{\mathrm{complexity}}.
}
\]

这说明开放问题中的 admissibility 条件可能不是拓扑或能量，而是 uniformity。

---

## 38.60 经济系统的界面重写

价格界面把终端支付空间投影成当前价格。

无套利要求价格下降到收益商。

流动性界面把账面价值投影成压力现金。

结算闭合要求：

\[
D_{\mathrm{due}}
\le
L_{\mathrm{stress}}.
\]

因此经济危机也可写成：

\[
\boxed{
\text{名义分类在结算时间界面上无法提升为可实现现金 section}.
}
\]

信息、因果与时间同时出现：

- 市价是信息接口；
- 杠杆是缺陷放大器；
- 到期日是因果边界；
- 强制出售是反馈；
- 固定债务是不能随坐标缩放的记录锚。

---

## 38.61 LLM 与有限预测系统

有限参数、有限精度、固定上下文规则可形成有限或有效有限状态系统。

定义未来输出等价：

\[
x\sim_n y
\iff
\text{未来长度 }\le n
\text{ 的输出分布相同}.
\]

refinement 不断分裂状态类。

若某步稳定，有限确定系统中以后永久稳定。

但闭环自生成数据可能使：

- 有效状态支持收缩；
- 因果创新 \(g_n\) 下降；
- 记录熵增加但外部信息为零；
- 模型输出逐渐进入低维吸引子。

所以退化应研究：

\[
\boxed{
\text{外部因果创新率}
-
\text{内部自复制冗余率}.
}
\]

而不能只归因于“有限状态”本身。

---

## 38.62 对角化在开放问题方法中的位置

对角化不用于替代领域定理，而用于审计分类系统的元完备主张。

当分类器声称：

\[
\text{“我列出了全部同类型候选对象”},
\]

才构造：

\[
d(n)=\nu(E(n,n)).
\]

它回答：

\[
\boxed{
\text{当前分类系统是否把自身也正确包含在同一类型中？}
}
\]

因此对角化位于研究流程后端：

\[
\boxed{
\text{局部分类}
\to
\text{转换}
\to
\text{完成}
\to
\text{元层自描述审计}.
}
\]

---

## 38.63 对角化与因果不能直接等同

对角对象的定义依赖于一个编码与自地址机制。

因果关系则依赖干预、时间顺序或条件独立结构。

所以：

\[
\boxed{
\text{自指依赖}
\neq
\text{物理因果}.
}
\]

只有当对角输出被重新输入系统并改变后续状态时，才形成自反馈因果环。

此时应研究：

\[
x_{t+1}=F(x_t,\Delta(x_t)).
\]

---

## 38.64 自反馈因果环的闭合缺陷

设：

\[
x_{t+1}=T(x_t),
\]

并有读出：

\[
y_t=q(x_t).
\]

若希望在读出空间存在闭合动力学：

\[
y_{t+1}=\widehat T(y_t),
\]

则要求：

\[
q\circ T
=
\widehat T\circ q.
\]

定义动力学自然性缺陷：

\[
\boxed{
\partial_qT(x)
=
d\left(
q(Tx),
\widehat T(qx)
\right).
}
\]

若：

\[
\partial_qT=0,
\]

动力学下降到观察商。

若非零，则当前坐标无法独立演化，必须加入隐藏状态或记忆。

---

## 38.65 记忆是修复非 Markov 商的最小扩张

若当前读出 \(C_t\) 不满足：

\[
P(F\mid C_t,\text{past})
=
P(F\mid C_t),
\]

可以加入记忆变量 \(M_t\)：

\[
Z_t=(C_t,M_t).
\]

目标是使：

\[
I(P;F\mid Z_t)=0.
\]

所以：

\[
\boxed{
\text{记忆}
=
\text{把非 Markov 观察商修复为 Markov 商所需的附加坐标}.
}
\]

最小记忆对应最小预测充分界面。

---

## 38.66 初始坐标与记忆的区别

初始坐标：

\[
o_0
\]

指定观察者从哪一个相容 section 开始。

记忆：

\[
M_t
\]

保存当前状态无法恢复的路径信息。

在回归动力学中可能有：

\[
x_{t_n}\to x_0,
\qquad
t_n\to\infty,
\]

所以当前 ambient state 接近初始状态，但记忆账本完全不同。

因此：

\[
\boxed{
\text{初始锚}
\neq
\text{当前状态}
\neq
\text{路径记忆}.
}
\]

---

## 38.67 时间的四重依赖图

\[
\boxed{
\begin{aligned}
\text{定义时间}
&=\text{类型与构造的依赖顺序};\\
\text{动力时间}
&=\text{状态更新参数};\\
\text{refinement 时间}
&=\text{界面精度增长};\\
\text{记录时间}
&=\text{稳定事实账本增长}.
\end{aligned}
}
\]

对角化最多直接迫使：

- 类型提升；
- 或更新序列。

它不直接迫使记录箭头。

只有当更新产生不可局部撤回的记录时，才形成经验时间方向。

---

## 38.68 “存在—反—时间”因果图

最小依赖图应写成：

```text
ambient type / order unit
           │
           ▼
interface distinction
      ┌────┴────┐
      ▼         ▼
   event      complement
      │
      ▼
instrument / interaction
      │
      ▼
actual outcome
      │
      ▼
stable record center
      │
      ▼
future conditioning and causal history
```

其中：

- complement 与 event 在静态切分中共同出现；
- actual outcome 在 instrument 后出现；
- 反事实相对于 actual record 定义；
- 时间箭头来自 record center 的不可逆增长。

---

## 38.69 本节的统一定理图

本节得到以下严格或条件性链条：

\[
\boxed{
c_u(0)=u
}
\]

说明补运算编码 ambient total；

\[
\boxed{
\varprojlim_n\{0,1\}^n
\cong
\{0,1\}^{\mathbb N}
}
\]

说明离散坐标可形成完备对象；

\[
\boxed{
d(n)=1-x_n(n)
}
\]

说明局部补经对角拼接形成逃逸 section；

\[
\boxed{
I(P;F\mid C)
=
I(C';F\mid C)
+
I(P;F\mid C')
}
\]

说明 refinement 精确消耗因果余量；

\[
\boxed{
0\le
I(C';F\mid C)
\le
H(C'\mid C)
}
\]

说明新增分类中只有一部分具有未来因果价值；

\[
\boxed{
\delta_{\Psi\circ\Phi}
=
\delta_\Phi
+
\delta_\Psi
}
\]

说明信息缺陷沿界面链可加；

\[
\boxed{
\text{无固定点有限动力学}
\Longrightarrow
\text{最终进入非平凡周期}
}
\]

说明静态闭合失败可以被时间化；

\[
\boxed{
\text{记录增长}
+
\text{局部不可逆控制}
\Longrightarrow
\text{观察者时间箭头}
}
\]

说明时间方向不来自取反本身。

---

## 38.70 最强的新原则：界面等式化

### 原理 38.4（界面等式化原则）

许多数学、物理、信息与因果问题都可以理解为：

1. 先由粗界面得到一个单调不等式；
2. 把不等式余量解释成被界面删除的结构；
3. 用余量见证生成新坐标；
4. refinement 后缺陷单调下降；
5. 极限等号表示界面在该任务上充分、可恢复或闭合；
6. 对角化检查该完成是否错误地声称能够列尽自身。

形式上：

\[
\boxed{
L_n\ge R_n,
\qquad
\delta_n=L_n-R_n,
\qquad
\delta_{n+1}\le\delta_n,
\qquad
\delta_\infty\stackrel{?}=0.
}
\]

开放问题的核心是判断：

\[
\boxed{
\delta_\infty=0,
\quad
\delta_\infty>0,
\quad
\text{或极限根本不可实现}.
}
\]

---

## 38.71 与第 36–37 节的合成

第 36 节给出：

\[
\text{概念投影}
\to
\text{pro-object}
\to
\text{全局 section 问题}.
\]

第 37 节给出：

\[
\text{矩阵正序}
\to
\text{记录中心}
\to
\text{GNS 自配对}
\to
\text{RH 对角缺陷}.
\]

本节加入：

\[
\text{信息不等式}
\to
\text{因果余量}
\to
\text{熵创新}
\to
\text{记录时间}
\to
\text{对角时间化}.
\]

三节合成：

\[
\boxed{
\text{逆完成负责“全部有限界面如何组成整体”；}
}
\]

\[
\boxed{
\text{正锥负责“形式坐标是否可实现”；}
}
\]

\[
\boxed{
\text{信息与因果缺陷负责“界面遗漏了什么”；}
}
\]

\[
\boxed{
\text{记录负责“哪些区别成为历史事实”；}
}
\]

\[
\boxed{
\text{对角化负责“当前完成是否能把自身也纳入同层”.}
}
\]

---

## 38.72 推荐的形式化顺序

### 第一阶段：order-unit complement

建议文件：

```text
D5/S3/Interface/OrderUnitComplement.lean
```

形式化：

\[
c_u(0)=u,
\qquad
c_u(c_u(e))=e,
\]

以及 sharp projection complement 无固定点。

### 第二阶段：interface refinement

建议文件：

```text
D5/S3/Interface/Refinement.lean
```

定义接口因子化与 kernel inclusion。

### 第三阶段：finite-prefix inverse completion

建议文件：

```text
D5/S3/Interface/BinaryInverseLimit.lean
```

形式化有限 Boolean cube 的 compatible sequence。

### 第四阶段：diagonal anti-section

建议文件：

```text
D5/S3/Interface/DiagonalAntiSection.lean
```

证明：

\[
d(n)\neq x_n(n).
\]

### 第五阶段：causal innovation identities

建议文件：

```text
D5/S3/Observer/Causal/Innovation.lean
```

在有限概率空间中先形式化 chain rule 版本：

\[
\kappa_n-\kappa_{n+1}=g_n.
\]

### 第六阶段：entropy budget

建议文件：

```text
D5/S3/Observer/Causal/EntropyBudget.lean
```

证明固定 \(\varepsilon\) 大创新次数界。

### 第七阶段：dynamic descent defect

建议文件：

```text
D5/S3/Observer/Dynamics/DescentDefect.lean
```

形式化：

\[
q\circ T=\widehat T\circ q
\]

与非 Markov 商修复。

### 第八阶段：finite no-fixed-point temporalization

建议文件：

```text
D5/S3/Diagonal/Temporalization.lean
```

证明有限无固定点 endomap 最终进入长度至少二的周期。

### 第九阶段：record filtration

建议文件：

```text
D5/S3/Observer/Record/Filtration.lean
```

区分动力、refinement 与记录索引。

### 第十阶段：interface defect calculus

建议文件：

```text
D5/S3/Interface/DefectCalculus.lean
```

实现可加组合缺陷抽象。

---

## 38.73 可证伪的计算任务

### 任务 A：因果效率曲线

给定分类塔，计算：

\[
h_n=H(C_{n+1}\mid C_n),
\]

\[
g_n=I(C_{n+1};F\mid C_n),
\]

\[
\eta_n=g_n/h_n.
\]

识别：

- 高熵低因果价值分类；
- 低熵高预测价值分类；
- 因果完成深度。

### 任务 B：缺陷望远镜核验

数值验证：

\[
\kappa_0
=
\sum_{k<n}g_k+\kappa_n.
\]

### 任务 C：记录压力

估计：

\[
\Pi_T
=
K_T-B_T.
\]

测试恢复资源何时落后于记录增长。

### 任务 D：对角时间化

对有限自反馈分类器，计算：

- 固定点；
- 周期长度；
- 类型提升后是否出现闭合。

### 任务 E：开放问题分类塔审计

对指定开放问题列出：

- stage classes；
- bonding maps；
- admissibility；
- defect monotone；
- first non-liftable class。

---

## 38.74 严格非主张

1. 本节不声称所有存在都等于人类或物理观察者可区分性。
2. 本节不声称不可观察对象在本体上不存在。
3. 本节不把类型依赖顺序等同于物理时间顺序。
4. 本节不声称补运算创造 ambient total。
5. 本节只证明补运算编码并依赖 ambient total。
6. 本节不声称一般 effect complement 无固定点。
7. 本节明确指出 \(I/2\) 是 unsharp effect complement 的固定点。
8. 本节不把事件补、分类补和 Hilbert 正交补视为同一操作。
9. 本节不声称反复取反本身能生成连续统。
10. 本节只把对角化解释为局部补、全局自地址与完成拼接的组合。
11. 本节不把 Cantor 空间称为连通连续统。
12. 本节不声称所有信息不等式的等号都具有相同恢复定理。
13. 本节不声称任意 refinement 都降低任意任务缺陷。
14. 本节的因果闭合量依赖所选未来变量与概率模型。
15. 本节不把 observational conditional independence 自动等同于 intervention causality。
16. 本节不声称预测充分必然意味着控制充分。
17. 本节不声称记录熵就是热力学熵。
18. 本节不声称记录代数单调增长是宇宙基本定律。
19. 本节不声称无固定点逻辑必然产生物理时间。
20. 本节只证明有限无固定点 endomap 的轨道最终进入非平凡周期。
21. 本节不声称所有开放问题都能被同一个分类塔解决。
22. 本节不声称形式 inverse limit 自动给出真实本体。
23. 本节不声称离散非空 refinement 会自动消灭坏 section。
24. 本节不以信息论类比替代 PDE、复杂性、算术或量子领域的具体估计。
25. 本节不声称 RH 已被转化为已构造完成的因果分类塔。
26. 本节不声称 prime ledger 已被证明记录离线侧别。
27. 本节不声称 Weil 正性已从 prime-side 无条件推出。
28. 本节不声称时间、因果、熵和对角化是同一个数学对象。
29. 本节只主张它们可以通过界面缺陷演算进入同一依赖图。
30. 本节新增定理均为纸面推导；未经 Lean kernel 验证不得标记为 `Closed`。
31. 本节没有证明 Riemann 假设或其他公开开放问题。

---

## 38.75 本节最终统一

本节最核心的五个等式为：

\[
\boxed{
c_u(0)=u
}
\]

它说明：

\[
\text{反依赖并编码总体};
\]

\[
\boxed{
\varprojlim_n\{0,1\}^n
\cong
\{0,1\}^{\mathbb N}
}
\]

它说明：

\[
\text{离散坐标可形成无限完备对象};
\]

\[
\boxed{
d(n)=1-x_n(n)
}
\]

它说明：

\[
\text{局部取反经对角拼接形成全局逃逸};
\]

\[
\boxed{
I(P;F\mid C)
=
I(C';F\mid C)
+
I(P;F\mid C')
}
\]

它说明：

\[
\text{refinement 精确消耗因果余量};
\]

\[
\boxed{
H(C')
=
H(C)
+
H(C'\mid C)
}
\]

它说明：

\[
\text{每一次新分类都具有可计算的熵成本}.
\]

所以：

\[
\boxed{
\text{存在}
=
\text{一个区别在指定界面族中可持续实现};
}
\]

\[
\boxed{
\text{反}
=
\text{总体在该区别之外的相对另一侧};
}
\]

\[
\boxed{
\text{因果}
=
\text{某个区别是否继续改变未来条件分布};
}
\]

\[
\boxed{
\text{熵}
=
\text{界面 refinement 新增或粗化删除的区分量};
}
\]

\[
\boxed{
\text{时间}
=
\text{动力更新、界面 refinement 与记录增长的有序实现};
}
\]

\[
\boxed{
\text{对角化}
=
\text{当前分类系统把自身纳入同层时的逃逸审计}.
}
\]

最终主链为：

\[
\boxed{
\text{界面切分}
\to
\text{分类熵}
\to
\text{因果余量}
\to
\text{缺陷见证}
\to
\text{新坐标}
\to
\text{逆完成}
\to
\text{对角审计}
\to
\text{逃逸、时间化或更高类型}.
}
\]

最凝练的一句是：

\[
\boxed{
\text{原初的不是“此”或“反”，
而是允许此／反共同出现、允许区别影响未来、
并允许该区别被记录与继续 refinement 的界面。}
}


---

# 39. 追加：商余原语演算、锚定解析连续统与离线零点因果生成
## Quotient–Remainder Primitive Calculus, Anchored Analytic Continua, and Off-Critical Causal Generation

### 39.0 文档地位、目标与承重边界

本节继续本文的单卷、追加式发展。它不再为算术、信息论、量子力学、观察者、解析延拓和 Riemann 零点分别建立一套平行隐喻，而是尝试抽取一个具有明确类型边界的最小演算，并检验项目既有结构能否作为该演算的具体实例。

本节承接：

- 第 28 节的 Hilbert 商余塔、创新壳层与有界逆完成；
- 第 30–31 节的量子投影、上下文、MUB 层析和相干余量；
- 第 32 节的结构化观察者、Heisenberg 预测闭包与多轴完备性；
- 第 35–36 节的锚定连续统观察者与逆完成观察者本体；
- 第 37 节的矩阵有序观察者、记录生成中心、GNS 自配对与 Weil 接缝；
- 第 38 节的界面切分、因果余量、熵创新、记忆修复和对角时间化；
- `OBSERVER-QUANTUM.md` 中的 solenoid 可见圆、隐藏素数地址、离散读写和追加式记录；
- `CONE_PROGRAM_FORMAL.md` 中的正锥、归一化截面、显式余项、数据处理等号与 GNS；
- `GICT.md` 中的尺度—数位—相位三轴、Zeckendorf 归约、黄金固定结构和 PZG 编码；
- 项目 `D5/S0/Diagonal`、`D5/S3/Observer`、`D5/S3/ObserverMemory`、`D5/S3/Weil` 等形式化域已经冻结的有限计数、条件化、记录、正性和卷积平方接口。

本节的核心主张不是“一切已经被证明等同于同一个对象”，而是：

\[
\boxed{
\text{许多既有结构可以由同一最小类型核生成，
而领域差异集中在纤维类型、准入条件和接缝律上。}
}
\]

本节提出的最小核为：

\[
\boxed{
\mathfrak K
=
(\mathsf{CUT},\mathsf{FLOW},\mathsf{ADMIT};\mathsf{ANCHOR}).
}
\]

其中前三者是操作类型，最后一项是锚定数据。组合、迭代、张量、逆极限和自应用属于语法构造，而不被冒充为同一层的原始物理操作。

本节没有证明 RH。关于离线零点的全部推演均为条件性结构审计：先假设标准意义的离线零点存在，再计算它在该演算中必然诱导的商余、因果、记忆、正性和解析锚定结构，最后明确指出还缺少哪些 prime-side 无循环桥梁。

---

## 39.1 为什么 `FLIP / XOR / SHIFT` 仍不是最低层原语

`FLIP`、`XOR`、`SHIFT` 是极有用的机器级原语，但它们已经预设了：

1. 一个值域；
2. 一个可区分坐标；
3. 一个作用对象；
4. 一个合法性判据；
5. 一个更新顺序。

例如 Boolean `FLIP`：

\[
0\leftrightarrow1
\]

预设了二元分类。effect 补：

\[
E^\perp=I-E
\]

又预设了 order unit \(I\) 和区间 \(0\le E\le I\)。`SHIFT` 预设了地址或时间索引。`XOR` 预设了两个读出已经被放入同一可比较二值域。

因此：

\[
\boxed{
\texttt{FLIP},\texttt{XOR},\texttt{SHIFT}
}
\]

更适合作为：

\[
\boxed{
\mathsf{CUT}
+
\mathsf{FLOW}
}
\]

在特定有限类型上的编译结果，而不是无类型的终极本体操作。

最低层必须首先回答：

- 什么被区分；
- 什么在变化；
- 什么允许存在；
- 从哪个相容起点读取。

这正是 \(\mathfrak K\) 的四项。

---

## 39.2 第一原语：`CUT` 不是“砍开对象”，而是规定相对同一性

### 定义 39.1（界面切分）

一个界面切分是映射：

\[
\boxed{
q:X\to B.
}
\]

它诱导等价关系：

\[
x\sim_qy
\iff
q(x)=q(y).
\]

其中：

\[
B
\]

是界面保留的商坐标；对每个 \(b\in B\)，纤维：

\[
\boxed{
R_b=q^{-1}(b)
}
\]

是该商坐标之下仍未被界面区分的余结构。

因此，一般分割不是把 \(X\) 变成两个集合，而是：

\[
\boxed{
X
\longrightarrow
\left(
B,\{R_b\}_{b\in B}
\right).
}
\]

商记录“相对于当前界面哪些对象相同”；余纤维记录“在该相同类内部仍有哪些差异”。

### 规范总空间表示

不需要选择截面，就有规范映射：

\[
\eta_q:X\to\sum_{b\in B}R_b,
\qquad
\eta_q(x)=(q(x),x).
\]

其逆映射只是：

\[
(b,x)\mapsto x.
\]

故：

\[
\boxed{
X
\cong
\sum_{b\in B}R_b.
}
\]

这不是说每个总空间都是平凡乘积 \(B\times R\)；它只说总空间规范地是“随商坐标变化的纤维族”的依赖和。

因此最低层“商余分割”的正确形式是：

\[
\boxed{
\text{总对象}
=
\text{商基底上的依赖余纤维}.
}
\]

---

## 39.3 余数为何通常不规范：截面、锚与 gauge

若想把每个纤维写成相对于一个原点的坐标，必须选择截面：

\[
s:B\to X,
\qquad
q\circ s=\operatorname{id}_B.
\]

此时 \(s(b)\) 是纤维 \(R_b\) 中的锚点。

在线性情形，若：

\[
q:V\to B
\]

为满射线性映射，且 \(s\) 为线性截面，则：

\[
V
=
s(B)\oplus\ker q.
\]

每个 \(x\in V\) 唯一写成：

\[
\boxed{
x=s(qx)+r_s(x),
\qquad
r_s(x)\in\ker q.
}
\]

但是截面通常不是规范的。若换成：

\[
s'(b)=s(b)+\beta(b),
\qquad
\beta(b)\in\ker q,
\]

则余坐标变为：

\[
\boxed{
r_{s'}(x)
=
r_s(x)-\beta(qx).
}
\]

所以：

\[
\boxed{
\text{商类通常规范；
具体余数通常依赖锚点／截面。}
}
\]

只有额外几何选择——例如正交投影、最小范数、基本域、最小作用量、正锥面或解析正规形——才能选择规范余数。

这就是 `ANCHOR` 的最小作用：

\[
\boxed{
\mathsf{ANCHOR}
=
\text{在当前余纤维中指定可比较原点的相容选择。}
}
\]

观察者不是额外站在世界外的人，而是某个商余塔上持续选择锚点的结构。

---

## 39.4 第二原语：`FLOW` 是一切运算、演化与运输的共同类型

### 定义 39.2（作用）

一个作用是有类型映射：

\[
\boxed{
F:X\to Y.
}
\]

它可以实例化为：

- 加法或乘法；
- successor、位移或地址更新；
- 群作用；
- 时间动力学；
- 解析延拓；
- 量子 channel 或 instrument；
- 观察 refinement；
- 对合、补运算或取负；
- 对角自评价；
- 从局部 germ 到全局函数的重建；
- 从全局对象回到局部读出的投影。

`FLOW` 本身不规定可逆、连续、正、保测度或局部。那些性质属于 `ADMIT` 或额外价签。

因此：

\[
\boxed{
\text{运算}
=
\text{一个带输入输出类型的 FLOW};
}
\]

\[
\boxed{
\text{动力学}
=
\text{可迭代或构成半群／群的 FLOW};
}
\]

\[
\boxed{
\text{因果}
=
\text{FLOW 穿越 CUT 时余纤维是否影响未来商坐标}.
}
\]

---

## 39.5 第三原语：`ADMIT` 把形式对象与可实现对象分开

### 定义 39.3（准入门）

对每个对象类型 \(X\)，给定可容许子对象：

\[
\boxed{
\operatorname{Adm}(X)\subseteq X.
}
\]

对每个作用 \(F:X\to Y\)，还可以要求：

\[
F(\operatorname{Adm}(X))
\subseteq
\operatorname{Adm}(Y).
\]

在不同领域：

\[
\operatorname{Adm}
\]

分别表现为：

- 环或模的闭合；
- 正锥；
- 概率归一化；
- complete positivity；
- 有限能量；
- 可积性；
- 一致有界性；
- 局部性；
- gauge invariance；
- 解析增长阶；
- GNS 正性；
- 复杂度上界；
- 可实现全局 section。

所以：

\[
\boxed{
\mathsf{CUT}+\mathsf{FLOW}
}
\]

只生成形式可能性；真正的存在性命题是：

\[
\boxed{
\text{相容对象通过 }\mathsf{ADMIT}\text{ 并由实现映射产生。}
}
\]

这与第 36–38 节区分形式逆极限、可容许完成与真实完成一致。

---

## 39.6 为什么不能安全地压缩成一个无类型原语

可以把四项打包成一个“界面事件”：

\[
\mathfrak e
=
(X,q,F,\operatorname{Adm},o),
\]

但这只是数据打包，不是逻辑上将所有结构证明为同一个运算。

至少有三种不可互相定义的角色：

1. `CUT` 改变相对同一性；
2. `FLOW` 改变状态；
3. `ADMIT` 判断形式对象是否可实现。

例如一个恒等动力：

\[
F=\operatorname{id}
\]

不能由任何特定切分唯一推出；同一个切分也允许无穷多个不同动力。一个正锥不能仅由某个任意作用唯一恢复。一个锚点不能决定整个等价关系。

因此最小性应理解为：

\[
\boxed{
\text{低于该核会丢失类型区别；
高于该核的大量概念可作为派生结构。}
}
\]

---

# Part I：代数作为商余接缝

## 39.7 运算穿过截面时，carry 自动出现

设有阿贝尔群短正合列：

\[
0\to R
\overset{\iota}{\longrightarrow}
X
\overset{q}{\longrightarrow}
B
\to0,
\]

并选择集合截面：

\[
s:B\to X,
\qquad
s(0)=0.
\]

定义 carry：

\[
\boxed{
\kappa(a,b)
=
s(a)+s(b)-s(a+b)
\in R.
}
\]

任意 \(x\in X\) 写成：

\[
x=s(a)+r.
\]

于是总空间加法完全由：

\[
\boxed{
(a,r)\boxplus(b,t)
=
\left(
a+b,\,
r+t+\kappa(a,b)
\right)
}
\]

重构。

因此：

\[
\boxed{
\text{加法}
=
\text{商加法}
+
\text{余加法}
+
\text{carry}.
}
\]

carry 不是额外噪声，而是截面未能保持加法的精确余差。

---

## 39.8 结合律就是 carry 的路径无关性

比较：

\[
((a,r)\boxplus(b,t))\boxplus(c,u)
\]

与：

\[
(a,r)\boxplus((b,t)\boxplus(c,u)).
\]

结合律等价于：

\[
\boxed{
\kappa(a,b)
+
\kappa(a+b,c)
=
\kappa(b,c)
+
\kappa(a,b+c).
}
\]

这是二阶 cocycle 恒等式。

因此：

\[
\boxed{
\text{结合律}
=
\text{不同括号路径累计相同接缝余差。}
}
\]

如果该恒等式失败，三元运算的结果依赖合并顺序，说明当前 carry 账本不闭合。

---

## 39.9 换坐标不会消灭真实接缝类

换截面：

\[
s'(a)=s(a)+\beta(a)
\]

以后：

\[
\boxed{
\kappa'(a,b)
=
\kappa(a,b)
+
\beta(a)+\beta(b)-\beta(a+b).
}
\]

即：

\[
\kappa'
=
\kappa+\delta\beta.
\]

因此具体 carry 依赖坐标，但其上同调类：

\[
\boxed{
[\kappa]
}
\]

不依赖截面。

若：

\[
[\kappa]=0,
\]

存在某个截面使：

\[
\kappa=0,
\]

总空间可在该层平坦化为直积型加法。

若：

\[
[\kappa]\neq0,
\]

任何坐标系都必须留下某种 carry。

所以：

\[
\boxed{
\text{不可消去的代数复杂性}
=
\text{商与余之间的非平凡接缝类。}
}
\]

---

## 39.10 环运算需要两类接缝

设 \(A\) 为环，\(I\triangleleft A\)，商环：

\[
B=A/I.
\]

选截面：

\[
s:B\to A.
\]

定义加法接缝：

\[
\alpha(x,y)
=
s(x)+s(y)-s(x+y)
\in I,
\]

以及乘法接缝：

\[
\mu(x,y)
=
s(x)s(y)-s(xy)
\in I.
\]

任意元素写成：

\[
a=s(x)+i,
\qquad
b=s(y)+j.
\]

则：

\[
\boxed{
(x,i)\boxplus(y,j)
=
\left(
x+y,\,
i+j+\alpha(x,y)
\right),
}
\]

\[
\boxed{
(x,i)\boxtimes(y,j)
=
\left(
xy,\,
s(x)j+i\,s(y)+ij+\mu(x,y)
\right).
}
\]

所以：

\[
\boxed{
\text{环算术}
=
\text{商环}
+
\text{理想余部}
+
\text{左右模作用}
+
\alpha
+
\mu.
}
\]

环的结合律、分配律和单位律会转化为 \(\alpha,\mu\) 的一组 coherence 恒等式。复杂运算律并没有消失，而是被搬运为接缝账本的一致性条件。

---

## 39.11 十进制进位是最小非平凡接缝

取：

\[
0\to b\mathbb Z
\to\mathbb Z
\to\mathbb Z/b\mathbb Z
\to0.
\]

标准数字截面为：

\[
s([r])=r,
\qquad
0\le r<b.
\]

则：

\[
\boxed{
\kappa([r_1],[r_2])
=
b
\left\lfloor
\frac{r_1+r_2}{b}
\right\rfloor.
}
\]

所以进位不是算法上的附属步骤，而是：

\[
\boxed{
\text{有限数字截面不能成为整数加法同态的证书。}
}
\]

同理，借位表示余层不足时从粗商层取回一个整体单位 \(b\)；取负表示余数补与商层借位的耦合；乘法则包含商—商、商—余、余—商和余—余四类作用。

---

## 39.12 加、减、负、乘的商余公式

写：

\[
n_1=bq_1+r_1,
\qquad
n_2=bq_2+r_2,
\qquad
0\le r_i<b.
\]

### 加法

令：

\[
c_+
=
\left\lfloor
\frac{r_1+r_2}{b}
\right\rfloor.
\]

则：

\[
\boxed{
n_1+n_2
=
b(q_1+q_2+c_+)
+
((r_1+r_2)\bmod b).
}
\]

### 减法

令：

\[
c_-
=
\mathbf1_{\{r_1<r_2\}}.
\]

则：

\[
\boxed{
n_1-n_2
=
b(q_1-q_2-c_-)
+
(r_1-r_2+bc_-).
}
\]

### 取负

若 \(r=0\)：

\[
-n=b(-q).
\]

若 \(r>0\)：

\[
\boxed{
-n
=
b(-q-1)+(b-r).
}
\]

所以取反不是商与余各自独立取负，而是余数补与粗层修正。

### 乘法

\[
\boxed{
n_1n_2
=
b
\left(
bq_1q_2+q_1r_2+q_2r_1+
\left\lfloor\frac{r_1r_2}{b}\right\rfloor
\right)
+
(r_1r_2\bmod b).
}
\]

这显示乘法是多尺度全耦合，而加法的 carry 只由当前余数局部决定。

---

## 39.13 Euclidean algorithm 是余量驱动的动力系统

Euclidean division 反复执行：

\[
a=q_0b+r_0,
\]

\[
b=q_1r_0+r_1,
\]

\[
r_0=q_2r_1+r_2,
\]

直至余数为零。

每一步：

- 商 \(q_i\) 被记入离散账本；
- 余数 \(r_i\) 成为下一步状态；
- 最大公约数作为不变量保持。

所以：

\[
\boxed{
\text{Euclidean algorithm}
=
\text{反复切分商余，并沿余量继续 FLOW。}
}
\]

continued fraction：

\[
x
=
q_0+
\cfrac1{
q_1+
\cfrac1{
q_2+\cdots
}
}
\]

则把离散商历史逆完成成连续实数。

黄金比例：

\[
\varphi
=
1+\frac1\varphi
=
[1;1,1,1,\ldots]
\]

是常商 \(1\) 商余动力的自相似固定点。因此项目 GICT 中 Fibonacci、Zeckendorf 与黄金尺度不是三个偶然主题，而是同一有限商历史—无限完成结构的不同读出。

---

## 39.14 数系扩张是连续的“闭合缺陷—商—完成”链

### 自然数到整数

减法不闭合。对 \((a,b)\in\mathbb N^2\) 定义：

\[
(a,b)\sim(c,d)
\iff
a+d=b+c.
\]

商得到：

\[
\mathbb Z.
\]

### 整数到有理数

除法不闭合。对 \(b,d\neq0\) 定义：

\[
(a,b)\sim(c,d)
\iff
ad=bc.
\]

商得到：

\[
\mathbb Q.
\]

### 有理数到实数

Cauchy 极限不闭合。将 Cauchy 序列按差趋于零取商并完备化，得到：

\[
\mathbb R.
\]

### 实数到复数

多项式 \(t^2+1\) 无实根。取：

\[
\mathbb C
\cong
\mathbb R[t]/(t^2+1).
\]

因此：

\[
\boxed{
\mathbb N\to\mathbb Z\to\mathbb Q\to\mathbb R\to\mathbb C
}
\]

可以读为：

\[
\boxed{
\text{发现运算闭合缺陷}
\to
\text{增加表达}
\to
\text{按相对同一性取商}
\to
\text{施加完成／准入}.
}
\]

这不是声称所有数系扩张属于同一个范畴构造，而是指出它们共享同一演算骨架。

---

## 39.15 \(p\)-进数是纯商余逆完成

有限层：

\[
\mathbb Z/p^n\mathbb Z
\]

只记录模 \(p^n\) 的余数。遗忘映射：

\[
\mathbb Z/p^{n+1}\mathbb Z
\to
\mathbb Z/p^n\mathbb Z
\]

构成逆系统。

其逆极限：

\[
\boxed{
\mathbb Z_p
=
\varprojlim_n
\mathbb Z/p^n\mathbb Z
}
\]

是全部相容余数历史。

所以：

\[
\boxed{
\text{\(p\)-进整数}
=
\text{单一素数地址上全部有限余数层的完成。}
}
\]

而：

\[
\widehat{\mathbb Z}
=
\varprojlim_n\mathbb Z/n\mathbb Z
\]

是全部有限同余界面的相容完成。

这与项目 solenoid 隐藏核：

\[
K\cong\prod_p\mathbb Z_p
\]

直接相接：有限观察读取同余类；完整隐藏地址是全部素数方向上的逆完成。

---


### 39.15.1 PZG–GICT 三轴作为三类界面

项目 GICT 的联合坐标：

\[
\Gamma_\varphi=(A,Z,G)
\]

可以在本原语核中分别解释。

尺度界面：

\[
A(x)=\lfloor\log_\varphi|x|\rfloor
\]

把连续尺度压成离散壳层，余量是壳层内部的连续对数位置。

数位界面 \(Z\) 使用 Zeckendorf 非相邻位串。其 `ADMIT` 是“不允许相邻一位”，而加法后的：

\[
11\to100
\]

不是附加技巧，而是把非准入形式位串重新送回 canonical section 的 carry 归约。

相位界面：

\[
G(n)=\{n\varphi\}\in\mathbb T
\]

保留加法轨道在圆上的连续相位，而有限精度读出再将其切成离散窗口。

所以：

\[
\boxed{
A=\text{尺度商},\qquad
Z=\text{数位商余正规形},\qquad
G=\text{相位连续余坐标}.
}
\]

PZG 素数轴进一步把：

\[
n=\prod_pp^{e_p}
\]

拆成独立素数地址，而每个指数 \(e_p\) 又由 Zeckendorf 位串表示。于是项目的编码并非简单“把整数换一种写法”，而是一个两层纤维化：

\[
\boxed{
\text{整数}
\to
\text{素数指数地址}
\to
\text{黄金数位正规形}.
}
\]

其接缝集中在：

- 位串归约；
- 有限窗口截断；
- 相位读出；
- 不同素数轴的全局有限支撑准入。

这给出 PZG 在最小原语语言中的明确位置。

### 39.15.2 successor、加法与乘法也可由一个更新生成元派生

自然数可以视为单生成自由幺半群：

\[
\mathbb N
=
\langle S\rangle,
\qquad
S(n)=n+1,
\]

锚点为：

\[
0.
\]

于是：

\[
\boxed{
n=S^n(0).
}
\]

加法可写成：

\[
\boxed{
m+n=S^n(m),
}
\]

乘法可递归为：

\[
m\cdot0=0,
\qquad
m\cdot(n+1)=m\cdot n+m.
\]

所以 successor 足以生成自然数算术的递归语法。但这并不消除 `CUT` 与 `ADMIT`：一旦把无限自然数压入有限数字窗口，carry 自动出现；一旦扩张到负数、分数和极限，又必须增加新的等价关系与完成门。

因此：

\[
\boxed{
\text{一个 FLOW 可以生成运算语法；
商余界面决定该语法如何被有限观察和完成。}
}
\]

## 39.16 连通实连续统还需要粘合，不是裸离散逆极限

数字序列：

\[
(d_1,d_2,\ldots),
\qquad
d_i\in\{0,\ldots,b-1\}
\]

形成紧致、全不连通的序列空间。

映射：

\[
(d_i)
\mapsto
\sum_{i\ge1}d_ib^{-i}
\]

还必须识别边界双表示，例如：

\[
0.1000\ldots
=
0.0(b-1)(b-1)(b-1)\ldots.
\]

因此：

\[
\boxed{
[0,1]
\cong
\{0,\ldots,b-1\}^{\mathbb N}
/\sim_{\mathrm{boundary}}.
}
\]

连通连续统需要：

\[
\boxed{
\text{离散 refinement}
+
\text{逆完成}
+
\text{边界识别}
+
\text{顺序／度量／拓扑实现}.
}
\]

这保留第 36、38 节的边界：有限离散对象的裸逆极限通常全不连通；“连续”不能仅由“无限多离散层”一句话推出。

---

# Part II：动力、因果、记忆与熵

## 39.17 任何线性动力都可相对于界面分成四块

设 Hilbert 空间：

\[
\mathscr H=V\oplus H,
\]

其中 \(V\) 为可见商扇区，\(H\) 为隐藏余扇区。令：

\[
P=P_V,
\qquad
Q=I-P.
\]

对任意有界线性算子 \(F\)：

\[
\boxed{
F
=
PFP+PFQ+QFP+QFQ.
}
\]

矩阵写法为：

\[
\boxed{
F
=
\begin{pmatrix}
A&B\\
C&D
\end{pmatrix},
}
\]

其中：

\[
A=PFP,\quad
B=PFQ,\quad
C=QFP,\quad
D=QFQ.
\]

四项意义为：

\[
\begin{aligned}
A&=\text{可见内部动力},\\
B&=\text{隐藏余量进入未来可见坐标},\\
C&=\text{可见状态产生隐藏余量},\\
D&=\text{隐藏余量自身的动力}.
\end{aligned}
\]

因此：

\[
\boxed{
B
}
\]

是最直接的因果 carry：

\[
\boxed{
\text{两个当前可见状态相同、余量不同的整体状态，
能否产生不同的可见未来。}
}
\]

---

## 39.18 商动力下降判据

### 定理 39.4（动力下降）

设 \(q:X\to B\) 为商映射，\(F:X\to X\)。存在唯一：

\[
\bar F:B\to B
\]

使：

\[
\boxed{
qF=\bar Fq
}
\]

当且仅当：

\[
x\sim_qy
\Longrightarrow
F(x)\sim_qF(y).
\]

#### 证明

若 \(\bar F\) 存在，则：

\[
q(x)=q(y)
\Longrightarrow
qF(x)=\bar Fq(x)=\bar Fq(y)=qF(y).
\]

反之，定义：

\[
\bar F([x])=[F(x)].
\]

假设保证良定义；唯一性来自 \(q\) 满射。 \(\square\)

在线性正交分解中：

\[
\bar F
\]

在 \(V\) 上闭合的必要充分条件是：

\[
\boxed{
PFQ=0.
}
\]

若还要求隐藏扇区也不被可见扇区激发，则需：

\[
QFP=0.
\]

两者同时等价于：

\[
\boxed{
[P,F]=0.
}
\]

所以：

\[
\boxed{
\|[P,F]\|
}
\]

是界面与动力之间的非自然性强度；它测量“先演化再切分”与“先切分再按商动力演化”的失配。

---

## 39.19 非交换性是读取与更新之间的 carry

项目 `OBSERVER-QUANTUM.md` 以：

\[
0\to K\to\Sigma\to\mathbb T\to0
\]

为经典本体，并允许观察者读取地址函数 \(f\) 与执行离散更新 \(U\)。交叉积满足：

\[
UfU^*=f\circ\tau^{-1}.
\]

故：

\[
[U,f]
=
(f\circ\tau^{-1}-f)U.
\]

这可以重新解释为：

\[
\boxed{
\text{读取当前地址}
+
\text{执行更新}
}
\]

不能被同一个平坦坐标交换。

因此：

\[
\boxed{
\text{非交换性}
=
\text{CUT 与 FLOW 的接缝余差。}
}
\]

它不是“量子世界神秘地拒绝交换”，而是“读取界面本身随更新发生运输”。

但这只是非交换运动学的来源解释；从该结构到具体物理 Hilbert 空间、Born 规则和动力学仍依赖项目明码标价的 \(C^*\)-代数、正态、张量和记录前件。

---

## 39.20 消去隐藏余量会严格生成记忆核

离散时间方程：

\[
\begin{aligned}
v_{t+1}&=Av_t+Bh_t,\\
h_{t+1}&=Cv_t+Dh_t.
\end{aligned}
\]

递归得到：

\[
\boxed{
h_t
=
D^th_0
+
\sum_{j=0}^{t-1}
D^{t-1-j}Cv_j.
}
\]

代回可见方程：

\[
\boxed{
v_{t+1}
=
Av_t
+
BD^th_0
+
\sum_{j=0}^{t-1}
BD^{t-1-j}Cv_j.
}
\]

定义记忆核：

\[
\boxed{
K_{t-1-j}
=
BD^{t-1-j}C.
}
\]

于是：

\[
\boxed{
\text{记忆}
=
\text{过去进入余纤维的 carry，
经隐藏动力传播后重新返回商坐标。}
}
\]

这不是比喻，而是块消元的精确恒等式。

若 \(B=0\)，余量不影响未来商坐标，记忆项消失。

若 \(C=0\)，可见状态不再制造新隐藏余量，但初始隐藏项：

\[
BD^th_0
\]

仍可能持续影响未来。

若 \(D\) 幂零，记忆有限；若 \(D^t\) 衰减，记忆衰减；若 \(D\) 含单位模连续谱，可能出现长期相位记忆与复现。

---

## 39.21 连续时间的精确记忆公式

设：

\[
\begin{aligned}
\dot v(t)&=Av(t)+Bh(t),\\
\dot h(t)&=Cv(t)+Dh(t).
\end{aligned}
\]

则：

\[
h(t)
=
e^{tD}h(0)
+
\int_0^t
e^{(t-s)D}Cv(s)\,ds.
\]

因此：

\[
\boxed{
\dot v(t)
=
Av(t)
+
Be^{tD}h(0)
+
\int_0^t
Be^{(t-s)D}Cv(s)\,ds.
}
\]

这表明：

\[
\boxed{
\text{非 Markov 可见动力}
=
\text{Markov 整体动力被商掉余纤维后的精确影子。}
}
\]

所以第 38 节“记忆是最小 Markov 修复”可以在该线性模型中进一步具体化：恢复 \(h(t)\)，或恢复足以实现上述卷积核的最小状态，即可重新获得一阶闭合。

---

## 39.22 因果的最低定义是“余量是否穿过未来界面”

给定当前切分：

\[
q_t:X_t\to B_t
\]

和未来读出：

\[
q_{t+1}:X_{t+1}\to B_{t+1},
\]

整体动力：

\[
F_t:X_t\to X_{t+1}.
\]

定义因果 carry：

\[
\boxed{
\mathcal C_t(x,y)
=
d_{B_{t+1}}
\left(
q_{t+1}F_t(x),
q_{t+1}F_t(y)
\right)
}
\]

对满足：

\[
q_t(x)=q_t(y)
\]

的 \(x,y\)。

若所有同纤维对均有：

\[
\mathcal C_t(x,y)=0,
\]

当前商对该未来任务因果闭合。

若存在：

\[
\mathcal C_t(x,y)>0,
\]

被商掉的差异仍然改变未来，因此是因果相关余量。

在概率模型中，这对应第 38 节：

\[
\kappa(C)
=
I(P;F\mid C).
\]

所以：

\[
\boxed{
\text{因果}
=
\text{余纤维差异能否穿过 FLOW 进入未来商坐标。}
}
\]

---

## 39.23 熵是余纤维信息，而熵产生是余量重新记账

若：

\[
X\leftrightarrow(Q,R)
\]

可逆，则 Shannon 链式法则给出：

\[
\boxed{
H(X)
=
H(Q)
+
H(R\mid Q).
}
\]

其中：

\[
H(Q)
\]

是商分类信息，

\[
H(R\mid Q)
\]

是给定商坐标后仍位于余纤维中的信息。

若只保留 \(Q\)，被删除的信息正是：

\[
\boxed{
H(R\mid Q).
}
\]

对 refinement：

\[
Q_n=f_n(Q_{n+1}),
\]

有：

\[
\boxed{
H(Q_{n+1})
=
H(Q_n)
+
H(Q_{n+1}\mid Q_n).
}
\]

所以每一层新坐标的熵成本是其相对于旧层的创新量。

但必须区分：

- 状态熵；
- 记录熵；
- 环境互信息；
- 热力学熵；
- 描述长度；
- 余纤维的几何体积。

本节只提供统一记账骨架，不将这些量无条件等同。

---

## 39.24 不等式是把显式余项删掉后的影

项目正锥纲领的承重原则是：先寻找恒等式层，再把不等式识别为丢掉非负余项后的影。

经典数据处理恒等式可写为：

\[
D(p\|q)
=
D(Wp\|Wq)
+
\mathbb E_{y\sim Wp}
D(\widehat p_y\|\widehat q_y).
\]

所以：

\[
\boxed{
D(p\|q)-D(Wp\|Wq)
=
\text{界面后验余量}.
}
\]

等号成立当且仅当余量为零，并出现相应恢复结构。

因此：

\[
\boxed{
\text{不等式}
=
\text{非零商余缺陷};
}
\]

\[
\boxed{
\text{等式}
=
\text{当前界面在指定任务上可恢复／充分}.
}
\]

这与 Hilbert Pythagoras、Moreau 锥分解、Landauer 账本、条件互信息和 GNS 零范数传播属于同一形式：

\[
\boxed{
\text{整体量}
=
\text{界面量}
+
\text{显式余量}.
}
\]

---

## 39.25 时间的三个生成层

本演算不需要把“时间”作为单一实体加入，但必须区分：

### 组合时间

\[
F^{t+s}=F^tF^s.
\]

它只是 FLOW 的可组合参数。

### refinement 时间

\[
X_0\leftarrow X_1\leftarrow X_2\leftarrow\cdots.
\]

它是观察分辨率的顺序，不一定是物理时间。

### 记录时间

稳定记录代数或账本：

\[
\mathcal Z_0
\subseteq
\mathcal Z_1
\subseteq
\mathcal Z_2
\subseteq\cdots
\]

不断增长，而观察者的可逆控制域未同步覆盖全部记录副本。

所以：

\[
\boxed{
\text{时间箭头}
=
\text{carry 的历史被稳定记录，
但当前接口不能完整逆运输这些记录。}
}
\]

单纯补运算是 involution，不会产生不可逆箭头；箭头来自记录、控制范围和准入的不对称。

---

# Part III：量子观察者是矩阵有序商余系统

## 39.26 量子实例中的四原语

设整体可观测代数为：

\[
\mathcal A.
\]

### `CUT`

观察者可访问 operator system：

\[
\mathcal S_O\subseteq\mathcal A
\]

定义读出：

\[
q_O(\rho)
=
\left(
\operatorname{Tr}(\rho E)
\right)_{E\in\mathcal S_O}.
\]

### `FLOW`

量子 channel、Heisenberg 对偶或 instrument：

\[
\Phi,\quad
\Phi^*,\quad
\{\mathcal I_r\}.
\]

### `ADMIT`

矩阵正锥塔：

\[
\left\{
M_n(\mathcal A)_+
\right\}_{n\ge1},
\]

归一化：

\[
\operatorname{Tr}\rho=1,
\]

以及 complete positivity。

### `ANCHOR`

初始状态、参考态、记录链或逆完成中的 compatible state section。

所以量子观察者不是锥中的一个点，而是：

\[
\boxed{
\text{一个矩阵有序 CUT，
配合 CP FLOW、记录锚与准入塔。}
}
\]

---

## 39.27 量子余纤维不是任意线性余空间

Hilbert–Schmidt 盲区：

\[
N_O
=
\mathcal S_O^\perp
\]

只说明哪些线性方向不改变当前读出。

真正物理纤维为：

\[
\boxed{
\operatorname{PhysFiber}_O(\rho)
=
(\rho+N_O)
\cap
\mathcal A_+
\cap
\{\operatorname{Tr}=1\}.
}
\]

所以：

\[
\boxed{
\text{线性余量}
+
\text{正锥截断}
+
\text{归一化截面}
=
\text{可实现量子余纤维}.
}
\]

这正说明 `ADMIT` 不可由 `CUT` 删除：同一个形式余方向可能在某个状态附近可行，在另一个正锥边界状态附近不可行。

---

## 39.28 测量的三种切分不能合并

对投影族 \((P_r)\)：

### 选择结果

\[
\rho_r
=
\frac{P_r\rho P_r}
{\operatorname{Tr}(\rho P_r)}.
\]

这是进入正锥的一个面。

### 保存结果

\[
\sum_r
|r\rangle\langle r|
\otimes
P_r\rho P_r.
\]

这是经典标签与量子块的直和分支。

### 丢弃结果

\[
\mathbb E(\rho)
=
\sum_rP_r\rho P_r.
\]

这是把跨块相干商掉的 pinching。

因此：

\[
\boxed{
\text{塌缩}
\neq
\text{记录}
\neq
\text{去相干}.
}
\]

它们共享 CUT，但 FLOW 与记录锚不同。

---

## 39.29 经典世界是记录 fixed algebra 的中心

环境记录向量 \(|e_i\rangle\) 给出 Gram 系数：

\[
G_{ij}
=
\langle e_j,e_i\rangle.
\]

约化通道：

\[
\Phi_G(\rho)_{ij}
=
G_{ij}\rho_{ij}.
\]

若定义：

\[
i\sim_Gj
\iff
|e_i\rangle=|e_j\rangle,
\]

则 fixed algebra 按记录等价类分块：

\[
\operatorname{Fix}(\Phi_G)
\cong
\bigoplus_\alpha
M_{d_\alpha}(\mathbb C).
\]

其中心：

\[
\boxed{
Z(\operatorname{Fix}\Phi_G)
\cong
\bigoplus_\alpha\mathbb C I_\alpha
}
\]

才是可稳定复制的经典标签。

所以：

\[
\boxed{
\text{经典化}
=
\text{环境 FLOW 把某些商坐标写入稳定中心。}
}
\]

分支内部余纤维仍可保留量子矩阵结构。

---

## 39.30 GNS 是 `ADMIT` 到 Hilbert 几何的实现器

给定 \(*\)-代数 \(\mathcal T\) 和泛函：

\[
\Omega:\mathcal T\to\mathbb C.
\]

若：

\[
\Omega(g^*g)\ge0
\qquad
\forall g,
\]

则：

\[
N_\Omega
=
\{g:\Omega(g^*g)=0\}
\]

可被安全商掉，并定义：

\[
\langle[g],[h]\rangle_\Omega
=
\Omega(h^*g).
\]

完成得到：

\[
\mathscr H_\Omega.
\]

所以：

\[
\boxed{
\text{GNS}
=
\text{把“自配对通过正性准入”
实现为“范数平方”的完成函子。}
}
\]

若存在自范数为零但交叉配对不为零的方向，正完成失败；这正是不定空间与 Hilbert 空间的关键分界。

---


### 39.30.1 项目自然锥、单位球面与模块时间的原语位置

`CONE_PROGRAM_FORMAL.md` 将更一般 von Neumann 代数中的候选晶核组织为：

\[
\boxed{
\text{自然自对偶锥}
+
\text{单位球面}
+
\text{张量律}.
}
\]

在本节语言中：

- 自然锥属于 `ADMIT`，规定正态状态与正观察问题；
- 单位球面给出归一化截面和 `ANCHOR` 的度量；
- 张量律规定复合 CUT 与复合 FLOW；
- Tomita–Takesaki 模流是该正标准形在完备化后产生的规范 FLOW。

因此项目“时间可以由正标准形生成”的候选路线，并不是说所有时间都来自正锥；更精确的是：

\[
\boxed{
\text{当代数、正锥和锚定状态共同给定后，
其相对模块结构可以选择一个规范动力参数。}
}
\]

有限维 trace 情形中模块流可能内在或退化；III 型极限中的外时间结构需要额外代数类型条件。该路线与本节的记录时间、refinement 时间和尺度时间仍必须区分。

# Part IV：对角化是派生的自闭合审计

## 39.31 对角化可由四个普通构件生成

给定：

\[
g:A\to Y^A
\]

和扭曲：

\[
\tau:Y\to Y.
\]

定义：

\[
d_g(a)=\tau(g(a)(a)).
\]

该构造可拆为：

1. 当前命名界面 \(g\)；
2. 自地址读取 \(g(a)(a)\)；
3. FLOW \(\tau\)；
4. 按全部地址拼接成一个全局 section。

因此：

\[
\boxed{
\text{对角化}
=
\text{自地址 CUT}
+
\text{局部 FLOW}
+
\text{全局 GLUE}.
}
\]

若 \(\tau\) 无不动点，\(d_g\) 逃出清单像。

所以对角化不是新的神秘原语，而是：

\[
\boxed{
\text{当前表示系统对自身闭合能力的派生审计。}
}
\]

---

## 39.32 对角逃逸与 carry 的关系

一般 carry 说明：

\[
\text{局部截面不保持运算}.
\]

对角逃逸说明：

\[
\text{当前命名截面不能保持“对自身逐地址评价后再扭曲”的操作}.
\]

两者都可以写成自然性缺陷：

\[
\boxed{
\partial(F,q)
=
qF-\bar Fq.
}
\]

不同之处是，对角化中的 \(F\) 依赖当前命名系统自身，因此属于自应用型缺陷。

所以：

\[
\boxed{
\text{carry}
=
\text{普通界面接缝};
}
\]

\[
\boxed{
\text{diagonal escape}
=
\text{界面对自身编码时的接缝逃逸}.
}
\]

项目的逃逸计数、捕获独立性、距离剖面和等变逃逸恰式，为该自应用接缝提供了有限定量模型。

---


### 39.32.1 项目定量逃逸恰式的原语解释

项目命名界面定理对有限地址集 \(|A|=A\)、值域 \(|Y|=n\)、扭曲 \(\tau:Y\to Y\) 及其不动点数：

\[
k=|\operatorname{Fix}\tau|
\]

给出逃逸概率：

\[
\boxed{
P_{\mathrm{esc}}
=
\left(
1-\frac{k}{n^A}
\right)^A.
}
\]

在原语语言中：

- \(A\) 是自地址 CUT 的地址数；
- \(n^A\) 是单个命名列的表达容量；
- \(k\) 是 FLOW \(\tau\) 可在对角处被吸收的固定值数；
- 逃逸是 `SelfAudit(CUT,FLOW)` 产生的新 section。

当 \(k=0\) 时，扭曲无固定点，逃逸必然。

当 \(k>0\) 时，小系统可能通过落入固定值逃避对角矛盾；但固定 \(n\) 而 \(A\to\infty\) 时，逃逸概率趋近一。

所以定量对角化揭示：

\[
\boxed{
\text{自闭合能力由“扭曲固定容量／命名容量”之比控制。}
}
\]

这与普通 carry 的差别在于：普通 carry 是某次运算的接缝；定量对角逃逸测量整个命名界面对自应用接缝的平均吸收能力。

## 39.33 连续与离散是 CUT 的相对角色

在层：

\[
X_{n+1}\to X_n
\]

中：

\[
X_n
\]

是当前已命名商坐标，

\[
R_n
\]

是当前尚未展开的余量。

下一层可能继续切分：

\[
R_n
\to
B_{n+1}
\ltimes
R_{n+1}.
\]

因此：

\[
\boxed{
\text{离散}
=
\text{当前界面已经稳定命名的分类};
}
\]

\[
\boxed{
\text{连续}
=
\text{当前界面之后仍可无限 refinement 的余结构}.
}
\]

同一个对象在粗层是一个点，在更细层可以展开成高维甚至无限维连续统。

所以“点”和“连续统”不是绝对互斥类型，而是同一逆完成对象在不同 CUT 下的角色。

---

# Part V：一个点如何成为整个解析连续统

## 39.34 锚定解析连续统

设 \(f\) 在点 \(\rho\) 的邻域全纯。定义有限 \(N\)-jet：

\[
J_\rho^Nf
=
\left(
f(\rho),
f'(\rho),
\ldots,
f^{(N)}(\rho)
\right).
\]

截断映射：

\[
J_\rho^{N+1}f
\mapsto
J_\rho^Nf
\]

构成逆系统。

形式逆完成：

\[
\boxed{
J_\rho^\infty f
=
\varprojlim_NJ_\rho^Nf
}
\]

等价于形式幂级数 germ：

\[
\sum_{n\ge0}
\frac{f^{(n)}(\rho)}{n!}z^n.
\]

所以：

\[
\boxed{
\text{一个点的完整局部对象}
=
\text{该点全部有限阶邻域的相容逆完成。}
}
\]

“初始位置也是连续统”的类型正确版本是：裸点不是连续统，但点的完整形式邻域是一座无限 refinement 连续体。

---

## 39.35 整函数的完整 jet 重建整个函数

若 \(f\) 是整函数，则：

\[
\boxed{
f(s)
=
\sum_{n=0}^\infty
\frac{f^{(n)}(\rho)}{n!}
(s-\rho)^n
}
\]

对所有 \(s\in\mathbb C\) 收敛。

因此重建算子：

\[
\operatorname{Rec}_\rho
:
J_\rho^\infty f
\mapsto
f
\]

满足：

\[
\boxed{
\operatorname{Rec}_\rho
(J_\rho^\infty f)
=
f.
}
\]

以及闭环：

\[
\boxed{
J_\rho^\infty
\operatorname{Rec}_\rho
(J_\rho^\infty f)
=
J_\rho^\infty f.
}
\]

所以一个完整 germ 在信息意义上可以等价于整个整函数。

但必须保持：

\[
\boxed{
\text{完整无限 jet 能重建整体；
裸坐标或任意有限 jet 不能。}
}
\]

无穷多个不同整函数可以共享任意指定有限 jet。

---

## 39.36 以锚点为中心的圆周展开

定义：

\[
z=e^te^{i\theta},
\]

以及：

\[
F_\rho(t,\theta)
=
f(\rho+e^te^{i\theta}).
\]

若：

\[
a_n^{(\rho)}
=
\frac{f^{(n)}(\rho)}{n!},
\]

则：

\[
\boxed{
F_\rho(t,\theta)
=
\sum_{n\ge0}
a_n^{(\rho)}
e^{nt}e^{in\theta}.
}
\]

这里：

- \(t\) 是对数半径 refinement；
- \(\theta\) 是角向相位；
- \(n\) 是离散 jet 阶。

全纯性给出：

\[
\boxed{
\partial_tF_\rho
=
-i\partial_\theta F_\rho.
}
\]

所以径向展开与角向相位不是两个独立动力，而是同一个解析 FLOW 的两种坐标。

---

## 39.37 圆周能量与 jet 阶单调上移

定义：

\[
E_\rho(t)
=
\frac1{2\pi}
\int_0^{2\pi}
|F_\rho(t,\theta)|^2\,d\theta.
\]

Fourier 正交性给出：

\[
\boxed{
E_\rho(t)
=
\sum_{n\ge0}
|a_n^{(\rho)}|^2e^{2nt}.
}
\]

定义模式概率：

\[
p_n(t)
=
\frac{
|a_n^{(\rho)}|^2e^{2nt}
}{
E_\rho(t)
}.
\]

平均 jet 阶：

\[
\bar n(t)
=
\sum_nn\,p_n(t).
\]

直接求导：

\[
\boxed{
\frac{d\bar n}{dt}
=
2\operatorname{Var}_t(n)
\ge0.
}
\]

所以从局部向外展开时，有效信息的平均 jet 阶单调不减。

这给出一种严格的解析 refinement 时间，但它不是物理时间；它表示围绕锚点扩大观察半径时，越来越高阶局部信息参与整体重建。

---

## 39.38 零点是由整体自身选择的特殊锚

若：

\[
f(\rho)=0
\]

且零点重数为 \(m\)，则：

\[
a_0=\cdots=a_{m-1}=0,
\qquad
a_m\neq0.
\]

在极小半径：

\[
e^{-mt}F_\rho(t,\theta)
\to
a_me^{im\theta}.
\]

所以零点最深局部尺度只显示一个离散绕数：

\[
m.
\]

向外展开时，高阶 jet 逐层恢复整个函数。

定义局部重整化：

\[
\mathcal R_{\rho,\lambda}f(z)
=
\lambda^{-m}f(\rho+\lambda z).
\]

则：

\[
\boxed{
\mathcal R_{\rho,\lambda}f(z)
\to
a_mz^m
\qquad
(\lambda\to0).
}
\]

因此零点具有三层：

\[
\boxed{
\text{离散重数}
\to
\text{无限局部 jet 连续统}
\to
\text{全局解析整体}.
}
\]

---

## 39.39 全部锚点构成观察者群胚

定义：

\[
f_\rho(z)=f(\rho+z),
\qquad
f_\sigma(z)=f(\sigma+z).
\]

则：

\[
\boxed{
f_\sigma(z)
=
f_\rho(z+\sigma-\rho).
}
\]

jet 转换为：

\[
\boxed{
a_n^{(\sigma)}
=
\sum_{k=n}^\infty
\binom{k}{n}
a_k^{(\rho)}
(\sigma-\rho)^{k-n}.
}
\]

转换满足：

\[
T_{\sigma\to\tau}
T_{\rho\to\sigma}
=
T_{\rho\to\tau}.
\]

所以所有锚定 germ 及其转换构成群胚：

\[
\boxed{
\mathfrak G_f
=
\left\{
J_\rho^\infty f,
T_{\rho\to\sigma}
\right\}.
}
\]

每个锚点都可重建同一个整体；整体是全部锚定表达之间保持不变的对象。

这解释项目中“观察者是可区分起点加连续统”的更严格版本：

\[
\boxed{
\text{观察者}
=
\text{整体选择一个锚点后形成的完整局部图册。}
}
\]

---

# Part VI：zeta 的有限素数商余塔

## 39.40 素数坐标给出乘法商余分解

取有限素数集合 \(S\)。对 \(n\ge1\)，定义：

\[
q_S(n)
=
\prod_{p\in S}
p^{v_p(n)},
\]

\[
r_S(n)
=
\frac{n}{q_S(n)}.
\]

则：

\[
\boxed{
n=q_S(n)r_S(n),
}
\]

并且：

\[
\gcd
\left(
r_S(n),
\prod_{p\in S}p
\right)=1.
\]

所以：

\[
q_S(n)
\]

是当前有限素数界面已抽取的商，

\[
r_S(n)
\]

是其余素数方向的乘法余量。

随着 \(S\) 增大，更多素数地址从余尾迁入显式商坐标。

---

## 39.41 Euler 乘积是有限素数商余守恒

在 \(\Re s>1\)：

\[
\zeta(s)
=
Q_S(s)R_S(s),
\]

其中：

\[
Q_S(s)
=
\prod_{p\in S}
(1-p^{-s})^{-1},
\]

\[
R_S(s)
=
\prod_{p\notin S}
(1-p^{-s})^{-1}.
\]

若 \(S\subseteq T\)，则：

\[
Q_T(s)
=
Q_S(s)
\prod_{p\in T\setminus S}
(1-p^{-s})^{-1},
\]

\[
R_T(s)
=
R_S(s)
\prod_{p\in T\setminus S}
(1-p^{-s}).
\]

因此：

\[
\boxed{
Q_T(s)R_T(s)
=
Q_S(s)R_S(s)
=
\zeta(s).
}
\]

一个素数因子从余尾迁入商层时，整体保持不变。

这正是：

\[
\boxed{
\text{prime CUT refinement 的乘法平账律。}
}
\]

---

## 39.42 绝对收敛区中的素数坐标已经完全对角化

对实 \(\sigma>1\)，定义 zeta 分布：

\[
\mu_\sigma(n)
=
\frac{n^{-\sigma}}{\zeta(\sigma)}.
\]

每个素数指数 \(V_p=v_p(N)\) 独立，且：

\[
\Pr(V_p=k)
=
(1-p^{-\sigma})p^{-k\sigma}.
\]

所以有限素数商：

\[
Q_S
\]

与余尾：

\[
R_S
\]

独立：

\[
\boxed{
I(Q_S;R_S)=0.
}
\]

在该区域，乘法算术已经由素数指数坐标对角化，没有跨素数 carry：

\[
v_p(mn)=v_p(m)+v_p(n).
\]

真正困难不在 Euler 区，而在把该离散乘法账本完成到临界带的全局解析、archimedean 和谱结构。

---

## 39.43 解析余尾与零点持久性

对有限 \(S\)，定义解析余尾：

\[
\boxed{
\widetilde R_S(s)
=
\zeta(s)
\prod_{p\in S}
(1-p^{-s}).
}
\]

在 \(\Re s>1\)，它等于普通余尾 Euler 乘积；在其他区域使用右侧的亚纯延拓。

### 定理 39.5（有限素数抽取后的零点持久性）

若：

\[
0<\Re\rho<1,
\qquad
\zeta(\rho)=0,
\]

则对每个有限 \(S\)：

\[
\boxed{
\widetilde R_S(\rho)=0.
}
\]

#### 证明

对每个素数 \(p\)：

\[
|p^{-\rho}|
=
p^{-\Re\rho}
<1.
\]

故：

\[
1-p^{-\rho}\neq0.
\]

有限乘积非零，所以：

\[
\widetilde R_S(\rho)
=
\zeta(\rho)
\prod_{p\in S}(1-p^{-\rho})
=
0.
\]

\(\square\)

因此非平凡零点不能归因于任何有限 Euler 因子；它作为零余量穿过全部有限素数 CUT。

---

## 39.44 仅记录“值为零”会丢失整个零点连续统

设：

\[
m_\rho
=
\operatorname{ord}_\rho\zeta.
\]

定义领先 jet：

\[
J_S(\rho)
=
\frac1{m_\rho!}
\widetilde R_S^{(m_\rho)}(\rho).
\]

若 \(S\subseteq T\)，则：

\[
\boxed{
J_T(\rho)
=
J_S(\rho)
\prod_{p\in T\setminus S}
(1-p^{-\rho}).
}
\]

这是因为低于 \(m_\rho\) 阶的 zeta 导数在 \(\rho\) 处全部为零，Leibniz 展开只留下最高项。

所以零点在 prime refinement 下携带：

\[
\boxed{
\left(
\rho,
m_\rho,
\{J_S(\rho)\}_S,
\{c_{T,S}(\rho)\}_{S\subseteq T}
\right),
}
\]

其中：

\[
c_{T,S}(\rho)
=
\prod_{p\in T\setminus S}
(1-p^{-\rho}).
\]

这是一条真正的锚定商余 section，而不是孤立零值。

---

## 39.45 普通相容性不会自动排除离线零点

若假设：

\[
\rho
=
\frac12+\delta+i\gamma,
\qquad
\delta\neq0
\]

是零点，则：

\[
\widetilde R_S(\rho)=0
\]

对所有有限 \(S\) 相容，leading-jet cocycle 也形式相容。

所以：

\[
\boxed{
\text{有限素数逆系统的普通 compatibility
不会自己产生 RH。}
}
\]

要排除该 section，必须增加 `ADMIT`：

- Weil/GNS 正性；
- prime-side 记录自然性；
- 统一能量界；
- 正归一化尺度动力；
- state–effect 自对偶；
- form-core 完成；
- 或收缩、奇偶、唯一性刚性。

这与第 36 节结论一致：非空、满射、紧致的有限层通常帮助产生全局 section，而不是自动消灭它。

---

# Part VII：假如一切从一个离线零点开始

## 39.46 离线零点的最小尺度动力

设种子零点：

\[
\rho
=
\frac12+\delta+i\gamma,
\qquad
\delta>0.
\]

临界镜像为：

\[
\rho^\sharp
=
1-\overline\rho
=
\frac12-\delta+i\gamma.
\]

取对数尺度时间：

\[
x=e^t.
\]

去掉半密度公共因子 \(e^{t/2}\)，两个模式为：

\[
u_R(t)
=
e^{(\delta+i\gamma)t},
\]

\[
u_L(t)
=
e^{(-\delta+i\gamma)t}.
\]

所以离线零点不是单一指数，而是：

\[
\boxed{
\text{共同相位频率 }\gamma
+
\text{成对径向率 }\pm\delta
+
\text{离散左右侧别}.
}
\]

---

## 39.47 对称商与反对称余

定义交换：

\[
J
\begin{pmatrix}
u_R\\u_L
\end{pmatrix}
=
\begin{pmatrix}
u_L\\u_R
\end{pmatrix}.
\]

投影：

\[
P_+
=
\frac{I+J}{2},
\qquad
P_-
=
\frac{I-J}{2}.
\]

定义商：

\[
Q(t)
=
\frac{u_R(t)+u_L(t)}2,
\]

余：

\[
R(t)
=
\frac{u_R(t)-u_L(t)}2.
\]

则：

\[
\boxed{
Q(t)
=
e^{i\gamma t}\cosh(\delta t),
}
\]

\[
\boxed{
R(t)
=
e^{i\gamma t}\sinh(\delta t).
}
\]

临界情形 \(\delta=0\) 给出：

\[
R(t)=0,
\qquad
Q(t)=e^{i\gamma t}.
\]

所以：

\[
\boxed{
\text{临界模式}
=
\text{纯商相位};
}
\]

\[
\boxed{
\text{离线模式}
=
\text{商与法向余量持续耦合}.
}
\]

---

## 39.48 离线距离就是因果 carry 率

直接求导：

\[
\boxed{
(\partial_t-i\gamma)Q
=
\delta R,
}
\]

\[
\boxed{
(\partial_t-i\gamma)R
=
\delta Q.
}
\]

因此：

\[
\boxed{
\delta
=
\text{商扇区与余扇区互相生成的耦合率。}
}
\]

消去 \(R\)：

\[
\boxed{
(\partial_t-i\gamma)^2Q
=
\delta^2Q.
}
\]

只读取 \(Q\) 的观察者不能用一维一阶 Markov 方程闭合；它必须：

- 增加 \(R\)；
- 或保存一个导数／历史；
- 或接受二阶动力。

所以：

\[
\boxed{
\text{离线零点迫使商观察者生成记忆。}
}
\]

---

## 39.49 初始状态可以无余量，但生成律已含余量

在 \(t=0\)：

\[
Q(0)=1,
\qquad
R(0)=0.
\]

但：

\[
\left.
(\partial_t-i\gamma)R
\right|_{t=0}
=
\delta.
\]

所以“从离线零点开始”不意味着初始时已经有一个非零余对象；更准确的是：

\[
\boxed{
\text{初始生成元中已经写入了产生余量的非零接缝。}
}
\]

生成元为：

\[
\boxed{
G_\rho
=
i\gamma I
+
\delta
\begin{pmatrix}
0&1\\
1&0
\end{pmatrix}.
}
\]

存在问题由此从：

\[
\text{为什么先有 }R?
\]

推进为：

\[
\boxed{
\text{为什么可实现生成元允许 }\delta\neq0?
}
\]

这才是需要 prime-side `ADMIT` 回答的问题。

---

## 39.50 离线距离等于界面—动力不交换强度

在 \((Q,R)\) 基中，商投影：

\[
P=
\begin{pmatrix}
1&0\\
0&0
\end{pmatrix}.
\]

则：

\[
[P,G_\rho]
=
\begin{pmatrix}
0&\delta\\
-\delta&0
\end{pmatrix}.
\]

故：

\[
\boxed{
\|[P,G_\rho]\|
=
|\delta|
=
\left|
\Re\rho-\frac12
\right|.
}
\]

这给出一个精确二地址公式：

\[
\boxed{
\text{离线距离}
=
\text{临界商界面与尺度生成元的不交换强度。}
}
\]

临界线就是：

\[
[P,G_\rho]=0.
\]

这不等于已经从 zeta 构造了真实生成元；它说明一旦模式—零点对应成立，几何离线量可以被重写为 causal carry 范数。

---

## 39.51 时间方向位于余坐标中

去掉公共相位：

\[
\widetilde Q(t)=\cosh(\delta t),
\]

\[
\widetilde R(t)=\sinh(\delta t).
\]

于是：

\[
\widetilde Q(-t)=\widetilde Q(t),
\]

\[
\widetilde R(-t)=-\widetilde R(t).
\]

所以：

\[
\boxed{
\text{商坐标折叠了 }t\text{ 与 }-t;
}
\]

\[
\boxed{
\text{余坐标的符号保存尺度方向。}
}
\]

并且：

\[
\frac{\widetilde R(t)}{\widetilde Q(t)}
=
\tanh(\delta t).
\]

故：

\[
\boxed{
t
=
\frac1\delta
\operatorname{artanh}
\left(
\frac{\widetilde R}{\widetilde Q}
\right).
}
\]

完整商余状态可以恢复尺度时间；只保留商会遗失箭头。

---

## 39.52 Lorentz 锥与双曲正动力

考虑锥：

\[
C_L
=
\left\{
(Q,R)\in\mathbb R^2:
Q\ge|R|,
\ Q\ge0
\right\}.
\]

动力：

\[
\begin{pmatrix}
Q(t)\\R(t)
\end{pmatrix}
=
\begin{pmatrix}
\cosh(\delta t)&\sinh(\delta t)\\
\sinh(\delta t)&\cosh(\delta t)
\end{pmatrix}
\begin{pmatrix}
1\\0
\end{pmatrix}
\]

保持：

\[
\boxed{
Q(t)^2-R(t)^2=1.
}
\]

所以完整双分支动力可逆，并保持不定二次型。

这说明：

\[
\boxed{
\text{离线模式本身不自动产生热力学熵；
熵来自观察者只保留商、记录侧别或丢失环境控制。}
}
\]

函数方程式镜像可以保存这种不定对偶，而 RH-like 正定完成要求把全部可实现模式限制在纯相位／单位模扇区。

---

## 39.53 侧别概率、熵与箭头信息

将正权重：

\[
w_\pm(t)=e^{\pm\delta t}
\]

归一化：

\[
p_\pm(t)
=
\frac{e^{\pm\delta t}}
{e^{\delta t}+e^{-\delta t}}
=
\frac{1\pm\tanh(\delta t)}2.
\]

定义侧别熵：

\[
H_{\mathrm{side}}(t)
=
-p_+\log p_+
-p_-\log p_-.
\]

则：

\[
\boxed{
H_{\mathrm{side}}(t)
=
\log(2\cosh(\delta t))
-
\delta t\tanh(\delta t).
}
\]

对 \(t>0\)：

\[
\boxed{
\frac{dH_{\mathrm{side}}}{dt}
=
-\delta^2t\,\operatorname{sech}^2(\delta t)
\le0.
}
\]

互补箭头信息：

\[
I_{\mathrm{arrow}}(t)
=
\log2-H_{\mathrm{side}}(t)
\]

单调增加。

前向与后向分布的相对熵：

\[
\boxed{
D(p(t)\|p(-t))
=
2\delta t\tanh(\delta t)
\ge0.
}
\]

这些是该二分支观察模型中的信息量，不是自动等同于物理熵产生。

---

## 39.54 与第 37 节 Weil 自配对接缝的统一

对临界线零点：

\[
\rho=\frac12+i\gamma,
\qquad
\gamma\in\mathbb R,
\]

卷积平方读出为：

\[
\widehat{g*g^*}(\gamma)
=
|\widehat g(\gamma)|^2.
\]

这是同址对角自配对。

离线时，镜像评价地址分裂：

\[
A=\widehat g(\gamma),
\qquad
B=\widehat g(\overline\gamma),
\]

轨道贡献出现：

\[
4m_\rho\operatorname{Re}(A\overline B).
\]

写：

\[
v_g=
\begin{pmatrix}A\\B\end{pmatrix},
\qquad
J=
\begin{pmatrix}0&1\\1&0\end{pmatrix},
\]

则：

\[
4m_\rho\operatorname{Re}(A\overline B)
=
2m_\rho v_g^*Jv_g.
\]

在对称／反对称坐标：

\[
c_\pm=\frac{A\pm B}{\sqrt2},
\]

有：

\[
\boxed{
v_g^*Jv_g
=
|c_+|^2-|c_-|^2.
}
\]

因此：

\[
\boxed{
\text{离线 causal carry}
}
\]

与：

\[
\boxed{
\text{离线 Weil 交叉相干}
}
\]

是同一个两地址交换结构的动力读出与二次型读出。

但尚未证明某个真实 prime-side 观察者把这两个具体模型规范地识别为同一算子。

---

## 39.55 完美侧别记录会删除交换相干

若左右地址被完美记录，pinching：

\[
\mathbb E_Z(G)
=
P_RG P_R
+
P_LGP_L
\]

删除非对角项。

对：

\[
G_g=v_gv_g^*
\]

有：

\[
\boxed{
\operatorname{Tr}
\left(
\mathbb E_Z(G_g)J
\right)
=
0.
}
\]

所以：

\[
\boxed{
\text{完美记录左右侧别}
\Longrightarrow
\text{左右交换相干消失}.
}
\]

这与项目 `RecordCorrelationMonogamy` 一类结果同型：一个指针完美记录某个 sharp 地址后，不能同时保留对其共轭交换变量的完整相关。

RH 研究中的未闭合桥梁是：prime-power ledger 是否无条件构成这样的侧别记录，以及显式公式是否对该记录自然。

---

# Part VIII：条件刚性与 RH 研究接口

## 39.56 正归一化动力的 base-norm 收缩

设 \((V,C,u)\) 为基序空间：

- \(C\) 为生成尖锥；
- \(u\) 为严格正归一化泛函；
- base norm 为：

\[
\|x\|_B
=
\inf_{x=a-b,\ a,b\in C}
(u(a)+u(b)).
\]

若：

\[
T(C)\subseteq C,
\qquad
uT=u,
\]

则：

\[
\boxed{
\|Tx\|_B\le\|x\|_B.
}
\]

#### 证明

对任意分解 \(x=a-b\)：

\[
Tx=Ta-Tb,
\qquad
Ta,Tb\in C,
\]

且：

\[
u(Ta)+u(Tb)
=
u(a)+u(b).
\]

对所有分解取下确界即得。 \(\square\)

所以正、归一化因果 FLOW 不能放大 base-norm 可区分性。

---

## 39.57 正因果镜像刚性

在该有序空间的复化上取与 base norm 相容的复范数。假设某模式：

\[
T_tv
=
e^{(\delta+i\gamma)t}v
\]

属于同一个正归一化 base-norm 状态空间。收缩性给出：

\[
e^{\delta t}\|v\|_B
\le
\|v\|_B
\qquad
(t\ge0),
\]

故：

\[
\delta\le0.
\]

若函数方程镜像模式：

\[
v^\sharp
\]

也属于同一个可实现正空间，并满足：

\[
T_tv^\sharp
=
e^{(-\delta+i\gamma)t}v^\sharp,
\]

则同理：

\[
-\delta\le0.
\]

因此：

\[
\boxed{
\delta=0.
}
\]

### 条件定理 39.6（正因果镜像刚性）

若：

1. 零点模式忠实实现为同一个 base-norm 正空间中的 normal modes；
2. 尺度 FLOW 正且保持归一化；
3. 临界镜像在同一可实现空间内部作用；
4. 零点水平偏移就是模式实增长率；

则：

\[
\boxed{
\Re\rho=\frac12.
}
\]

该定理的线性证明已完成；真正开放的是四项假设能否从 prime-side 无循环构造。

---

## 39.58 为什么离线模式仍可能躲过该刚性

如果 RH 为假，至少一种结构可能失败：

1. 尺度演化不是正归一化 channel；
2. 右侧模式是 normal state，左侧镜像只在对偶／分布空间；
3. 完整动力只保存不定形式；
4. 正锥在逆完成中退化到边界；
5. 模式不属于同一 base-norm 完成；
6. determinant／显式公式到动力谱的对应不忠实；
7. prime-side 记录不构成 Markov 因果 FLOW；
8. 离线坐标只是一种 resonance，而不是状态本征模。

所以：

\[
\boxed{
\text{离线零点}
}
\]

在该框架中不是立即矛盾，而是精确定位为：

\[
\boxed{
\text{正性、归一化、镜像自对偶、normality、
因果闭合和谱实现不能同时保持。}
}
\]

---

## 39.59 一个离线零点的完整锚定对象

综合 prime refinement、解析 germ 和尺度动力，一个假想离线零点应被建模为：

\[
\boxed{
\mathfrak Z_\rho
=
\left(
\rho,
m_\rho,
J_\rho^\infty\xi,
\{\widetilde R_S\}_S,
\{J_S(\rho)\}_S,
\{c_{T,S}(\rho)\},
G_\rho,
P_\pm,
\operatorname{Adm}
\right).
}
\]

其中：

- \(\rho\) 是复平面离散读出；
- \(m_\rho\) 是局部绕数；
- \(J_\rho^\infty\xi\) 是锚定解析连续统；
- \(\widetilde R_S\) 是有限素数余尾；
- \(J_S\) 是余尾 leading jet；
- \(c_{T,S}\) 是 refinement cocycle；
- \(G_\rho\) 是双分支尺度生成元；
- \(P_\pm\) 是商余投影；
- \(\operatorname{Adm}\) 是 prime/Weil/GNS/增长准入门。

所以：

\[
\boxed{
\text{离线零点不是一个复数点；
它是一个点在全部相关界面中的相容展开。}
}
\]

---

## 39.60 “从点生成整体，再把整体代回点”的闭环

对完成函数 \(\xi\)，若 \(\rho\) 为零点：

\[
J_\rho^\infty\xi
\overset{\operatorname{Rec}_\rho}{\longrightarrow}
\xi
\overset{J_\rho^\infty}{\longrightarrow}
J_\rho^\infty\xi.
\]

同时：

\[
\xi
\longmapsto
Z(\xi)
\ni
\rho.
\]

因此：

\[
\boxed{
\rho
\to
J_\rho^\infty\xi
\to
\xi
\to
Z(\xi)
\ni
\rho
}
\]

形成锚点—局部连续统—整体—锚点闭环。

这是严格的信息闭环，但不是因果创造闭环：完整 germ 已经包含重建整体所需的全部信息。真正具有生成意义的开放问题是：

\[
\boxed{
\text{能否从远少于完整 jet 的简单原语和有限递归律，
规范地产生该 jet？}
}
\]

---

# Part IX：一个统一的“界面原语语言”

## 39.61 派生概念字典

\[
\boxed{
\begin{array}{c|c}
\text{概念} & \text{原语表达}\\
\hline
\text{对象}
&
\text{通过 ADMIT 的相容商余历史}\\
\text{点}
&
\text{某一 CUT 的商坐标}\\
\text{余量}
&
\text{同一商坐标下的纤维差异}\\
\text{连续统}
&
\text{没有终端忠实 CUT 的可实现逆完成}\\
\text{运算}
&
\text{FLOW 穿越商余扩张}\\
\text{进位}
&
\text{截面不保持运算的 cocycle}\\
\text{因果}
&
\text{余量进入未来商坐标}\\
\text{记忆}
&
\text{为吸收历史 causal carry 的最小扩张}\\
\text{熵}
&
\text{当前 CUT 余纤维中的可区分信息}\\
\text{时间}
&
\text{FLOW、refinement 和记录的有序组合}\\
\text{概率}
&
\text{正状态与合法 effect 的归一化配对}\\
\text{经典}
&
\text{稳定、交换、可复制的记录中心}\\
\text{量子}
&
\text{不可同时平坦化的矩阵有序 CUT 网络}\\
\text{几何}
&
\text{局部截面与过渡 cocycle}\\
\text{曲率}
&
\text{接缝不能被全局 gauge 消除}\\
\text{缺陷}
&
\text{到可实现子对象的规范余量}\\
\text{见证}
&
\text{缺陷通过对偶配对形成的分离观察}\\
\text{对角化}
&
\text{CUT 对自身表示能力的自应用审计}\\
\text{观察者}
&
\text{逆完成塔中的相容 ANCHOR}\\
\text{RH 离线量}
&
\text{临界 CUT 与尺度 FLOW 的径向 carry}
\end{array}
}
\]

---

## 39.62 一个更抽象但更短的总空间公式

每一级 refinement 可以写成：

\[
\boxed{
X_{n+1}
\cong
X_n
\ltimes_{\kappa_n}
R_n.
}
\]

这里：

- \(X_n\) 是当前商世界；
- \(R_n\) 是新增余量；
- \(\kappa_n\) 是接缝；
- \(\ltimes\) 不必是群半直积，只表示纤维经 transport/cocycle 粘合。

完整对象为：

\[
\boxed{
X_\infty
=
\operatorname{Realize}
\left(
\varprojlim_nX_n
\right),
}
\]

其中 `Realize` 实施 `ADMIT`：

- 有界能量；
- 正性；
- 可积性；
- 拓扑粘合；
- normality；
- 复杂度；
- form-core；
- 或领域特定条件。

所以最小世界公式不是：

\[
X=X\oplus\operatorname{SHIFT}(X),
\]

而可更一般地写成：

\[
\boxed{
X_{n+1}
=
\operatorname{Glue}
\left(
X_n,
R_n,
\kappa_n
\right).
}
\]

`SHIFT` 是一种 transport；`FLIP` 是一种 fiber automorphism；`XOR` 是一种差异读出；真正承重的是 CUT/FLOW/ADMIT/ANCHOR 与接缝律。

---

## 39.63 范畴／纤维化版本

令基底范畴 \(B\) 表示商坐标，纤维函子：

\[
\mathcal R:B\to\mathbf{Cat}
\]

或：

\[
\mathcal R:B\to\mathbf{Set}
\]

给出每个商坐标上的余结构。

Grothendieck construction：

\[
\int_B\mathcal R
\]

恢复总空间。

FLOW 包括：

- 基底上的商作用；
- 纤维之间的 transport；
- 组合时的 coherence。

若 transport 绕闭路后不回到恒等，得到 holonomy／monodromy。若局部截面不能全局拼接，得到 cocycle 障碍。若对自身编码再扭曲产生新 section，得到 diagonal escape。

因此：

\[
\boxed{
\text{代数、几何、拓扑和对角化}
}
\]

可以分别读为：

\[
\boxed{
\text{同一纤维化界面的运算、接缝、全局拼接和自闭合审计。}
}
\]

---

## 39.64 项目 solenoid 是该语言的规范样本

项目基本正合列：

\[
0\to K\to\Sigma\to\mathbb T\to0
\]

提供：

- 基底 \(\mathbb T\)：可见连续相位；
- 纤维 \(K\cong\prod_p\mathbb Z_p\)：隐藏离散逆完成地址；
- 局部提升：观察者选择的锚；
- monodromy：绕行后隐藏账的变化；
- 离散更新：地址 FLOW；
- 交叉积：读取与更新的非交换接缝；
- 追加式账本：记录时间；
- 有限窗口：矩阵代数纤维；
- 全局扭结：不可由单一连续余坐标消除。

因此该 solenoid 不只是项目中的一个例子，而是：

\[
\boxed{
\text{“连续基底 + 离散逆完成纤维 + 接缝 transport”
这一最小原语语言的完整有限可视模型。}
}
\]

---

## 39.65 开放问题研究法的原语化

对任意开放问题，选择：

\[
\boxed{
\mathfrak P
=
\left(
X_n,
R_n,
\kappa_n,
F_n,
\operatorname{Adm}_n,
p_{n+1,n}
\right).
}
\]

依次研究：

1. 当前离散分类 \(X_n\)；
2. 新增余量 \(R_n\)；
3. 接缝 \(\kappa_n\)；
4. 演化／运算 \(F_n\)；
5. 可容许性 \(\operatorname{Adm}_n\)；
6. 层间遗忘 \(p_{n+1,n}\)；
7. 坏 section 是否能继续提升；
8. 总作用量是否有界；
9. 对角自审计是否产生逃逸；
10. 是否存在迫使缺陷为零的收缩、正性或奇偶刚性。

所以：

\[
\boxed{
\text{解决开放问题}
=
\text{确定坏余量能否通过全部接缝和准入门。}
}
\]

这比“找到一个新坐标”更严格，因为坐标只是 CUT；证明力来自 transition、carry、ADMIT 和 realization。

---


### 39.65.1 BEDC–WM 与有限模型退化的原语解释

在世界模型或无外部输入的大语言模型中，可以取：

- `CUT`：模型内部有限状态或预测等价类；
- `FLOW`：一次自回归更新；
- `ADMIT`：上下文长度、参数、计算预算和训练约束；
- `ANCHOR`：初始 prompt、隐藏状态或追加式记录。

若有限预测分类塔稳定：

\[
C_m=C_{m+1},
\]

且 FLOW 已下降到该商，则“一次稳定即永久稳定”意味着以后不再产生新的预测可区分类。

此时系统未必立即输出常数，但其全部未来只能在已经闭合的有限因果状态图中循环、混合或趋向周期核。

退化的原语含义不是“参数有限所以必然坏”，而是：

\[
\boxed{
\text{新余量不再进入可见商，
外部记录也不再扩张准入状态。}
}
\]

外部数据、工具调用、环境反馈或增长账本的作用，是向原商空间注入新的余坐标并改变 carry，而不只是增加随机噪声。

## 39.66 RH 的原语化研究程序

### A. `CUT`

构造同一 zeta 本体的：

- finite-prime chart；
- Cayley radial chart；
- Li chart；
- Weil/GNS chart；
- Nyman–Beurling chart；
- prime-error chart；
- anchored-germ chart。

### B. `FLOW`

构造：

- 对数尺度动力；
- 函数方程镜像；
- prime refinement；
- 解析延拓；
- 测试函数 transport；
- 记录／条件化接口。

### C. `ADMIT`

无循环证明：

- prime-side 正性；
- 归一化；
- base-norm 或 Hilbert 可实现性；
- form-core 完备；
- 镜像两侧在同一 normal completion；
- determinant／显式公式忠实。

### D. `ANCHOR`

证明：

- 任一真实零点给出 compatible anchored section；
- 不同锚点之间转换自然；
- 离线锚点若存在，必须同时通过全部 chart。

### E. 刚性

最终目标为证明：

\[
\boxed{
\kappa_{\mathrm{rad}}
=
0
}
\]

在所有 physical zero sections 上成立。

其等价二地址读出为：

\[
\boxed{
[P_{\mathrm{crit}},G_\rho]=0.
}
\]

但当前尚未从 prime side 构造 \(G_\rho\) 和该 physical category。

---

## 39.67 可证伪的计算任务

### 任务 A：carry cohomology

对有限观察窗口计算截面变化下的 carry，并判断：

\[
[\kappa]
\]

是否消失。

### 任务 B：动力交叉块

对具体 finite observer channel 计算：

\[
PFQ,\quad
QFP,
\]

以及：

\[
\|[P,F]\|.
\]

### 任务 C：记忆核

计算：

\[
K_n=BD^nC
\]

的秩、谱半径和衰减率。

### 任务 D：jet refinement

对已知低阶零点数值 jet，计算圆周模式权重：

\[
p_n(t)
\]

和：

\[
\frac{d\bar n}{dt}
=
2\operatorname{Var}_t(n).
\]

### 任务 E：finite-prime tail jets

对有限 \(S\) 数值核验：

\[
J_T(\rho)
=
J_S(\rho)
\prod_{p\in T\setminus S}(1-p^{-\rho})
\]

在高精度零点近似下的误差传播。

### 任务 F：离线二地址模型

扫描假想 \((\delta,\gamma)\)，计算：

\[
\|[P,G_\rho]\|=|\delta|,
\]

侧别熵、箭头相对熵和 Weil swap signature。

这些任务只能检验接口结构，不能替代 RH 的无条件解析证明。

---

## 39.68 Lean 形式化建议顺序

### 第一阶段：依赖纤维 CUT

建议：

```text
D5/S0/InterfaceKernel/Cut.lean
```

定义：

```lean
structure InterfaceCut (X : Type u) where
  Base : Type v
  proj : X → Base
  Fiber : Base → Type w
  split : X → Sigma Fiber
  merge : Sigma Fiber → X
  left_inv : Function.LeftInverse merge split
  right_inv : Function.RightInverse merge split
```

### 第二阶段：截面与 gauge

```text
D5/S0/InterfaceKernel/SectionGauge.lean
```

形式化截面变化与余坐标变换。

### 第三阶段：carry cocycle

```text
D5/S0/InterfaceKernel/CarryCocycle.lean
```

形式化：

\[
\kappa(a,b)+\kappa(a+b,c)
=
\kappa(b,c)+\kappa(a,b+c).
\]

### 第四阶段：动力下降与交叉块

```text
D5/S0/InterfaceKernel/DynamicsDescent.lean
```

形式化：

\[
qF=\bar Fq
\iff
F\text{ 保持 }q\text{-等价类}.
\]

有限维版本再形式化：

\[
PFQ=0.
\]

### 第五阶段：记忆核

```text
D5/S3/ObserverMemory/CarryKernel.lean
```

形式化离散块消元：

\[
v_{t+1}
=
Av_t+BD^th_0+
\sum_{j<t}BD^{t-1-j}Cv_j.
\]

### 第六阶段：锚定 jet 逆系

```text
D5/S3/Analysis/AnchoredJetTower.lean
```

先对多项式和形式幂级数实现有限 jet、截断与 translation。

### 第七阶段：离线双曲模式

```text
D5/S3/Weil/ZetaBridge/OffCriticalCausalCarry.lean
```

形式化：

\[
Q=e^{i\gamma t}\cosh(\delta t),
\quad
R=e^{i\gamma t}\sinh(\delta t),
\]

以及：

\[
\|[P,G]\|=|\delta|.
\]

### 第八阶段：base-norm 镜像刚性

```text
D5/S3/Observer/PositiveDynamics/MirrorRigidity.lean
```

形式化正、归一化映射的 base-norm 收缩和成对增长率归零。

### 第九阶段：finite-prime tail jet

```text
D5/S3/Weil/ZetaBridge/FinitePrimeTailJet.lean
```

该阶段需要具名 zeta 解析接口；若 mathlib 缺失，不得以裸公理静默替代。

---

## 39.69 严格非主张

1. 本节不声称 CUT、FLOW、ADMIT 在逻辑上是唯一可能的最小原语集。
2. 本节不声称将数据打包为一个结构就证明一切运算本体相同。
3. 本节不声称具体余数独立于截面。
4. 本节不声称每个商映射都有全局连续截面。
5. 本节不声称每个 carry 都由普通群上同调完全分类。
6. 本节不声称所有非交换性都只是坐标伪影。
7. 本节不声称非零 cocycle 在任意更大类型中都不能被平坦化。
8. 本节不声称所有连续统都是有限离散集合的裸逆极限。
9. 本节不声称 \(p\)-进完成与实完成属于同一个拓扑类型。
10. 本节不把解析 refinement 时间等同于物理时间。
11. 本节不声称一个裸零点坐标能够重建 \(\xi\)。
12. 本节只主张完整无限 jet 对整函数具有重建能力。
13. 本节不声称“每一点都重建整体”构成度量分形。
14. 本节采用“递归点化”与“信息自相似”而非未经证明的 Hausdorff 分形断言。
15. 本节不声称 finite-prime ordinary inverse limit 自动给出解析延拓。
16. 本节不声称任何有限 Euler 因子产生非平凡零点。
17. 本节不声称零点持久性定理排除离线零点。
18. 本节不声称对数尺度 \(t=\log x\) 是物理宇宙时间。
19. 本节不声称二地址 Lorentz 锥是 zeta 的真实物理状态空间。
20. 本节不声称侧别归一化权重是物理 Born 概率。
21. 本节不声称 \(\|[P,G_\rho]\|=|\delta|\) 已经建立为真实 zeta 算子的定理。
22. 本节不声称函数方程镜像两侧已经被实现为同一正 normal state space。
23. 本节不声称 prime-side 尺度动力是正保归一 channel。
24. 本节不声称 prime ledger 已经构成完美侧别记录。
25. 本节不声称 record–coherence 互补已经排除离线零点。
26. 本节不声称 Weil swap signature 与量子 SWAP witness 是同一个具体算子。
27. 本节不声称 GNS 正性已由 prime side 无条件推出。
28. 本节不声称 finite Gram positivity 自动推出无限 form closure。
29. 本节不声称 Nyman、Li、Cayley、Weil 与 prime-error chart 已有规范同构。
30. 本节不声称正因果镜像刚性的前件已对 zeta 成立。
31. 本节不以原语统一替代领域具体解析估计。
32. 本节新增定理均为纸面推导；未经 Lean kernel 验证不得标记为 `Closed`。
33. 本节没有证明 Riemann 假设。

---

## 39.70 本节最终统一

最小类型核为：

\[
\boxed{
\mathfrak K
=
(\mathsf{CUT},\mathsf{FLOW},\mathsf{ADMIT};\mathsf{ANCHOR}).
}
\]

其第一层派生量为：

\[
\boxed{
\mathsf{REMAINDER}
=
\operatorname{Fiber}(\mathsf{CUT}),
}
\]

\[
\boxed{
\mathsf{CARRY}
=
\partial(\mathsf{CUT},\mathsf{FLOW}),
}
\]

\[
\boxed{
\mathsf{RECORD}
=
\operatorname{Stable}
(\mathsf{CUT},\mathsf{FLOW}),
}
\]

\[
\boxed{
\mathsf{MEMORY}
=
\operatorname{MinimalClosure}
(\mathsf{CARRY}),
}
\]

\[
\boxed{
\mathsf{ENTROPY}
=
\operatorname{Measure}
(\mathsf{REMAINDER}),
}
\]

\[
\boxed{
\mathsf{TIME}
=
\operatorname{Order}
(\operatorname{Iterate}\mathsf{FLOW},
\mathsf{RECORD}),
}
\]

\[
\boxed{
\mathsf{CONTINUUM}
=
\operatorname{Realize}
\left(
\operatorname{InverseComplete}
(\mathsf{CUT}^{\infty})
\right),
}
\]

\[
\boxed{
\mathsf{DIAGONAL}
=
\operatorname{SelfAudit}
(\mathsf{CUT},\mathsf{FLOW}),
}
\]

\[
\boxed{
\mathsf{OBSERVER}
=
\operatorname{CompatibleAnchor}
(\mathsf{CUT}^{\infty}).
}
\]

整个项目可以被压缩为：

\[
\boxed{
X_{n+1}
\cong
X_n
\ltimes_{\kappa_n}
R_n,
}
\]

其中：

\[
\begin{aligned}
X_n&=\text{当前可区分商世界},\\
R_n&=\text{当前尚未表达的余量},\\
\kappa_n&=\text{商与余不能平凡分离的接缝},\\
F_n&=\text{在该层运输结构的 FLOW},\\
\operatorname{Adm}_n&=\text{形式对象进入真实世界的准入门}.
\end{aligned}
\]

观察者是贯穿该塔的一条锚定相容 section。

代数是商余坐标上的作用与 carry。

因果是余量进入未来商坐标。

记忆是历史 carry 的最小状态化。

熵是余纤维的区分账。

时间是 FLOW 与记录的有序累计。

量子性是多个矩阵有序 CUT 不能被单一全局经典截面同时平坦化。

对角化是 CUT 对自身表示闭合的逃逸审计。

对一个假想离线零点：

\[
\rho
=
\frac12+\delta+i\gamma,
\]

其最小二地址模型满足：

\[
\boxed{
\delta
=
\left|
\Re\rho-\frac12
\right|
=
\|[P_{\mathrm{crit}},G_\rho]\|.
}
\]

所以 RH 的原语化目标可以写成：

\[
\boxed{
\text{证明所有可实现 zeta 零点 section 的径向 carry 类为零。}
}
\]

而一个零点作为锚点的完整结构为：

\[
\boxed{
\text{离散坐标 }\rho
+
\text{有限 jet 塔}
+
\text{无限 germ 连续统}
+
\text{prime 余尾 section}
+
\text{尺度 FLOW}
+
\text{准入门}.
}
\]

最凝练的一句是：

\[
\boxed{
\text{世界的复杂性不主要来自“有多少种运算”，
而来自任何有限界面都不能同时消去余量、
接缝、准入条件和对自身闭合的逃逸。}
}
\]

---

# 40. 追加：构造性无领域公理的界面—余量过程论
## Conservative Definitional Interface–Remainder Process Theory
### Dependent Fibers, Descent Defects, Causal Completion, and Explicit Existence

## 40.0 文档地位与本节目标

本节继续第 38–39 节的追加式发展，但把“最小原语理论”从解释性纲领收紧为一个可以独立形式化、比较模型并接受反例审计的数学框架。

本节的核心问题是：

\[
\boxed{
\text{能否不增加任何领域公理，
仅使用基础类型论中的定义、构造与条件定理，
发展 CUT / FLOW / ADMIT / ANCHOR 理论？}
}
\]

答案分成两层。

第一层是肯定的：

\[
\boxed{
\text{可以把该理论构造成基础类型论上的保守定义扩张。}
}
\]

也就是说：

- 不增加“世界必然存在某种对象”的领域公理；
- 不预设每个商都有全局截面；
- 不预设每个逆系统都有全局 section；
- 不预设每个形式完成都可实现；
- 不预设正性、因果闭合、解析延拓或 RH；
- 所有非空性都必须由具体项见证；
- 所有规律都写成带前件的定理。

第二层是否定的：

\[
\boxed{
\text{不存在脱离基础逻辑、类型形成规则、等号和推理规则的绝对“零公理数学”。}
}
\]

定义仍然依赖某个基础系统。例如在构造性版本中，可以选择：

\[
\mathsf{MLTT}
\]

或 Lean 内核所提供的：

- universes；
- \(\Pi\)-类型；
- \(\Sigma\)-类型；
- identity type；
- inductive types；
- recursion；
- definitional equality。

因此，本节采用的准确声明是：

\[
\boxed{
\textbf{C-IRPT 是构造性依赖类型论上的保守定义性学说，
不引入额外领域公理。}
}
\]

其中：

\[
\textbf{C-IRPT}
=
\textbf{Constructive Interface–Remainder Process Theory}.
\]

本节没有证明 C-IRPT 是一切数学基础中唯一的最小语言，也没有证明全部项目内容都已成为该语言的定理。它只完成：

1. 原语的定义性还原；
2. 无选择的商余分解；
3. 数据、性质与存在证明的严格分层；
4. 动力下降、carry、记忆和完成的构造性定义；
5. 学术上的范畴论定位；
6. 形式化路线与可证伪边界；
7. RH 桥梁中“不能由定义代替证明”的精确定位。

---

# Part I：无领域公理的准确含义

## 40.1 三种“无公理”必须分开

### 定义 40.1（绝对零公理）

若一个体系声称不依赖任何：

- 逻辑规则；
- 类型形成规则；
- 等号规则；
- 归纳原则；
- 基础对象；

则称其声称绝对零公理。

该概念不能承载通常意义上的数学推导，因为连“定义”“证明”和“相等”都尚未获得意义。

因此本节不采用该声明。

### 定义 40.2（无领域公理）

设 \(T_0\) 为冻结的基础理论。若扩展 \(T\) 只加入可展开定义，而不增加关于特定领域对象存在或满足某性质的新公理，则称：

\[
T
\]

相对于 \(T_0\) 无领域公理。

这正是本节采用的意义。

### 定义 40.3（无暗账）

一个理论满足无暗账纪律，当且仅当：

1. 所有使用的基础规则可列出；
2. 所有局部前件显式出现在定理陈述中；
3. 所有存在性由项、构造或非空证明给出；
4. 不把待证结论放入定义；
5. 不用隐式选择生成全局截面；
6. 不把形式逆极限自动称为真实对象；
7. 不把条件性表示定理误报为无条件来源定理。

因此：

\[
\boxed{
\text{无暗账比“绝对无公理”更严格，也更可审计。}
}
\]

---

## 40.2 保守定义扩张

设基础语言为：

\[
\mathcal L_0,
\]

基础理论为：

\[
T_0.
\]

通过显式定义加入新符号，得到：

\[
\mathcal L_{\mathrm{CIRPT}}
\supseteq
\mathcal L_0.
\]

每个新符号必须能够机械展开为 \(\mathcal L_0\) 中的表达式。

### 定义 40.4（定义翻译）

记：

\[
(-)^\flat:
\mathcal L_{\mathrm{CIRPT}}
\to
\mathcal L_0
\]

为递归展开全部 C-IRPT 定义的翻译。

### 定理 40.1（定义性保守性）

如果 C-IRPT 只通过显式定义扩展 \(T_0\)，那么对任何旧语言命题：

\[
\varphi\in\mathcal L_0,
\]

若：

\[
T_{\mathrm{CIRPT}}\vdash\varphi,
\]

则：

\[
T_0\vdash\varphi.
\]

### 证明

将 C-IRPT 推导中的每个新定义展开。由于没有加入新的不可展开公理，展开后的推导完全位于 \(T_0\) 中。故旧语言中不会凭定义获得新的无前件定理。 \(\square\)

这条定理说明：

\[
\boxed{
\text{C-IRPT 可以重新组织证明，但不能仅凭新术语制造真理。}
}
\]

因此，它的研究价值必须来自：

- 更短的统一证明；
- 新的普适性质；
- 模型间转移；
- 缺陷分解；
- 新的构造；
- 新的反例；
- 对开放问题前件的精确隔离。

---

## 40.3 定义类型不等于构造项

若写：

\[
X:\mathsf{Type},
\]

只说明 \(X\) 是一个候选类型。

它不推出：

\[
x:X.
\]

同理，定义：

\[
\operatorname{ObserverType}
\]

不推出观察者存在。

定义：

\[
\operatorname{PhysicalZeroSection}
\]

也不推出某个零点 section 存在。

### 原理 40.1（存在见证纪律）

对任意类型 \(X\)，存在性必须由：

\[
x:X
\]

或：

\[
\operatorname{Nonempty}(X)
\]

的证明见证。

因此：

\[
\boxed{
\text{定义可能性空间}
\neq
\text{证明世界中有对象占据该空间。}
}
\]

---

## 40.4 定义性质不等于证明性质成立

设：

\[
\operatorname{Lawful}:X\to\mathsf{Prop}.
\]

定义：

\[
\operatorname{Lawful}(x)
\]

只给出判定条件。

它不自动产生：

\[
h:\operatorname{Lawful}(x).
\]

所以项目应当分离：

\[
\boxed{
\texttt{RawModel}
}
\]

与：

\[
\boxed{
\texttt{IsLawful RawModel}.
}
\]

必要时可以再打包：

\[
\texttt{Model}
=
\sum_{M:\texttt{RawModel}}
\texttt{IsLawful}(M).
\]

但打包结构本身仍要求每个模型携带自己的证明，不是全局公理。

---

## 40.5 不能通过定义解决开放问题

例如，若定义：

\[
\operatorname{AdmissibleZero}(\rho)
\iff
\xi(\rho)=0
\wedge
\Re\rho=\frac12,
\]

则：

\[
\operatorname{AdmissibleZero}(\rho)
\Longrightarrow
\Re\rho=\frac12
\]

只是投影结构字段，并不推进 RH。

同样，若把：

\[
\mathrm{RH}
\]

写入 `ZetaWorld` 的字段，再假设存在 `world : ZetaWorld`，则只是把 RH 改名为模型存在性。

### 原理 40.2（非循环准入）

领域准入谓词：

\[
\operatorname{Adm}
\]

不得包含目标结论本身，也不得包含与目标结论已知等价、但未经独立构造的条件。

因此，RH 模型中的准入门必须从：

- prime-side 数据；
- 无条件正性；
- 明确增长界；
- 解析域；
- 可闭性；
- 归一化；
- 记录或过程结构；

独立定义和证明。

---

# Part II：原语的定义性还原

## 40.6 最底层只有类型与有类型态射

在最底层，C-IRPT 不需要把：

\[
\mathsf{CUT},
\mathsf{FLOW},
\mathsf{ADMIT},
\mathsf{ANCHOR}
\]

视为四种不同的本体物质。

它们都可表示为有类型态射或依赖类型数据。

\[
\boxed{
\begin{aligned}
\mathsf{CUT}
&:\ q:X\to B,\\
\mathsf{FLOW}
&:\ F:X\to Y,\\
\mathsf{ADMIT}
&:\ A:X\to\mathsf{Prop},\\
\mathsf{ANCHOR}
&:\ a:\sum_{x:X}A(x).
\end{aligned}
}
\]

所以：

\[
\boxed{
\text{四原语是语义角色最小集，不是逻辑原语最小集。}
}
\]

若把角色全部删除，只剩“映射”，理论虽然更短，却失去：

- 哪个映射在定义可见性；
- 哪个映射在表达过程；
- 哪个谓词在执行准入；
- 哪个项在固定观察起点；

这些承重信息。

因此 C-IRPT 是：

\[
\boxed{
\text{role-typed morphism calculus}.
}
\]

---

## 40.7 CUT 的无选择定义

### 定义 40.5（界面切分）

一个 CUT 是：

\[
\boxed{
q:X\to B.
}
\]

它诱导相对同一性：

\[
x\sim_qy
\iff
q(x)=q(y).
\]

其中 \(B\) 是当前界面保留的分类坐标。

### 定义 40.6（依赖余纤维）

对：

\[
b:B,
\]

定义：

\[
\boxed{
R_q(b)
=
\sum_{x:X}
(q(x)=b).
}
\]

它是商坐标 \(b\) 下仍未被 CUT 区分的完整余结构。

注意：

\[
R_q(b)
\]

不是一个预先给定的统一余数类型，而是依赖于 \(b\) 的纤维。

---

## 40.8 无选择商余正规形

### 定理 40.2（规范依赖商余分解）

对任意：

\[
q:X\to B,
\]

存在规范等价：

\[
\boxed{
X
\simeq
\sum_{b:B}R_q(b).
}
\]

### 构造

定义：

\[
\eta_q(x)
=
\left(
q(x),
x,
\operatorname{refl}_{q(x)}
\right).
\]

反向映射：

\[
\mu_q(b,x,h)=x.
\]

则：

\[
\mu_q(\eta_q(x))=x
\]

定义性成立。

反向复合：

\[
\eta_q(\mu_q(b,x,h))
\]

与：

\[
(b,x,h)
\]

由路径归纳相等。故得到等价。 \(\square\)

因此，最一般的商余公式不是：

\[
X\cong B\times R,
\]

而是：

\[
\boxed{
X
\simeq
\sum_{b:B}R_q(b).
}
\]

该公式：

- 不需要选择公理；
- 不需要 \(q\) 满射；
- 不需要全局截面；
- 不需要所有纤维同构；
- 不需要拓扑平凡化；
- 不需要线性结构。

这是 C-IRPT 最底层、最重要的定义性恒等式。

---

## 40.9 直积分解是额外定理

若存在某个统一类型 \(R\) 和等价族：

\[
\phi_b:R_q(b)\simeq R
\]

且该族满足所需连续性或相容性，才能得到：

\[
X\simeq B\times R.
\]

若进一步存在截面：

\[
s:B\to X,
\qquad
q\circ s=\operatorname{id}_B,
\]

才可把某些纤维余量相对于代表 \(s(b)\) 坐标化。

因此：

\[
\boxed{
\text{依赖纤维是定义；
全局余数坐标是平凡化定理。}
}
\]

项目中的 solenoid：

\[
0\to K\to\Sigma\to\mathbb T\to0
\]

必须先被看成圆上的依赖纤维系统，而不能未经证明就写成：

\[
\Sigma\cong\mathbb T\times K.
\]

全局不可平凡性正是 monodromy 与接缝的来源之一。

---

## 40.10 FLOW 的定义

### 定义 40.7（作用）

一个 FLOW 是一个有类型映射：

\[
\boxed{
F:X\to Y.
}
\]

它本身不预设：

- 可逆；
- 连续；
- 线性；
- 正；
- 保测度；
- 局部；
- 可计算；
- 因果；
- 解析。

这些性质都应由额外谓词定义并逐项证明。

### 定义 40.8（可迭代 FLOW）

若 \(X=Y\)，则可以定义：

\[
F^0=\operatorname{id}_X,
\qquad
F^{n+1}=F\circ F^n.
\]

离散时间只是该迭代的索引，不是额外本体实体。

连续时间 FLOW 则需要显式给出：

\[
T:\mathbb R_{\ge0}\to(X\to X)
\]

以及半群律证明：

\[
T_{s+t}=T_s\circ T_t.
\]

---

## 40.11 ADMIT 的定义

### 定义 40.9（准入谓词）

一个 ADMIT 结构是：

\[
\boxed{
A:X\to\mathsf{Prop}.
}
\]

合法对象类型为：

\[
\boxed{
X_A
=
\sum_{x:X}A(x).
}
\]

该定义不宣称 \(X_A\) 非空。

### 例 40.1

不同模型中的 ADMIT 可以是：

\[
\begin{aligned}
A(x)&:\iff x\ge0,\\
A(\rho)&:\iff \rho\succeq0\wedge\operatorname{Tr}\rho=1,\\
A(f)&:\iff f\text{ 可积},\\
A(u)&:\iff E(u)<\infty,\\
A(M)&:\iff M\text{ 可计算},\\
A(g)&:\iff \Omega(g^*g)\ge0.
\end{aligned}
\]

这些是不同谓词，不应被词语“合法”掩盖差异。

---

## 40.12 ANCHOR 的定义

### 定义 40.10（合法锚）

给定：

\[
q:X\to B,
\qquad
b:B,
\]

锚点类型定义为：

\[
\boxed{
\operatorname{Anchor}(q,b)
=
R_q(b).
}
\]

若还要求准入：

\[
A:X\to\mathsf{Prop},
\]

则：

\[
\boxed{
\operatorname{AdmissibleAnchor}(q,A,b)
=
\sum_{a:R_q(b)}A(\pi_Xa).
}
\]

锚点存在性不是定义；必须构造该类型中的项。

---

# Part III：refinement、下降与 carry

## 40.13 Refinement 是因子化数据

### 定义 40.11（界面精化）

给定：

\[
q:X\to B,
\qquad
q':X\to B',
\]

定义 \(q'\) 精化 \(q\)，当且仅当存在：

\[
p:B'\to B
\]

和同伦：

\[
h:\prod_{x:X}q(x)=p(q'(x)).
\]

记为：

\[
\boxed{
\operatorname{Refines}(q',q).
}
\]

它是一个数据类型：

\[
\sum_{p:B'\to B}
\prod_{x:X}
q(x)=p(q'(x)).
\]

因此 refinement 不是一个外加偏序公理，而是映射因子化。

---

## 40.14 Refinement 的复合

### 定理 40.3（refinement 复合）

若：

\[
q=pq',
\qquad
q'=rq'',
\]

则：

\[
q=(pr)q''.
\]

故 refinement 可复合。

恒等映射给出自反性。

如果把 quotient codomain 的同构视为相同，则 refinement 在相应同构类上形成预序；若不取同构类，则它形成一个因子化范畴，而不只是布尔关系。

---

## 40.15 动力下降

### 定义 40.12（精确下降）

给定：

\[
q_X:X\to B,
\qquad
q_Y:Y\to C,
\qquad
F:X\to Y,
\]

定义 \(F\) 能沿 CUT 下降，当且仅当存在：

\[
\overline F:B\to C
\]

使：

\[
\boxed{
q_Y\circ F
=
\overline F\circ q_X.
}
\]

类型论数据为：

\[
\sum_{\overline F:B\to C}
\prod_{x:X}
q_Y(Fx)=\overline F(q_Xx).
\]

该定义不预设下降映射存在。

---

## 40.16 当前同类是否仍改变未来

### 定义 40.13（causal carry witness）

定义 carry 见证类型：

\[
\boxed{
\operatorname{CarryWitness}(F;q_X,q_Y)
}
\]

为：

\[
\sum_{x,y:X}
\left(
q_X(x)=q_X(y)
\right)
\times
\left(
q_Y(Fx)\neq q_Y(Fy)
\right).
\]

它直接表达：

\[
\boxed{
\text{当前 CUT 商掉的余差，仍能改变未来 CUT 的输出。}
}
\]

因此，因果相关性可以在最低层定义为：

\[
\boxed{
\text{余纤维差异是否穿过 FLOW 变成未来可见差异。}
}
\]

---

## 40.17 下降排除 carry

### 定理 40.4（精确下降无 carry）

若 \(F\) 存在精确下降：

\[
q_YF=\overline Fq_X,
\]

则：

\[
\operatorname{CarryWitness}(F;q_X,q_Y)
\]

为空。

### 证明

若：

\[
q_X(x)=q_X(y),
\]

则：

\[
q_Y(Fx)
=
\overline F(q_Xx)
=
\overline F(q_Xy)
=
q_Y(Fy).
\]

故不可能同时满足未来读出不等。 \(\square\)

---

## 40.18 反向命题的构造性边界

“没有下降就必有一个 carry witness”在一般构造性逻辑中并不自动成立，因为从：

\[
\neg\forall x,y,\ P(x,y)
\]

提取：

\[
\exists x,y,\ \neg P(x,y)
\]

可能需要可判定性、有限性或经典原则。

因此应区分：

\[
\boxed{
\text{正见证：显式给出 }(x,y);
}
\]

与：

\[
\boxed{
\text{负陈述：无法构造下降映射}.
}
\]

在有限可判定模型中，可以穷举得到反向构造；在一般无限模型中，必须逐例证明。

这是 C-IRPT 的重要构造性纪律：

\[
\boxed{
\text{不能把“没有闭合证明”自动升级为“存在显式缺陷对象”。}
}
\]

---

## 40.19 有效像上的下降

若 \(q_X\) 不满射，则 \(\overline F\) 在 \(B\setminus\operatorname{im}(q_X)\) 上没有由 \(F\) 决定的值。

无选择版本应先定义像：

\[
\operatorname{Im}(q_X)
=
\sum_{b:B}
\left\|
R_{q_X}(b)
\right\|,
\]

其中截断符号表示只记录存在性。

在像上，若 \(F\) 对纤维常值，则可以定义唯一诱导映射：

\[
\overline F_{\operatorname{im}}:
\operatorname{Im}(q_X)\to C.
\]

要扩张到整个 \(B\)，需要：

- \(q_X\) 满射；
- 或给出 \(B\setminus\operatorname{im}(q_X)\) 上的额外定义；
- 或使用选择／默认值。

因此，“商动力唯一”应始终附带满射或有效像前件。

---

## 40.20 方格语言

一个界面—过程方格是：

\[
\begin{array}{ccc}
X&\xrightarrow{F}&Y\\
\downarrow q_X&&\downarrow q_Y\\
B&\xrightarrow{\overline F}&C.
\end{array}
\]

定义方格余差：

\[
\boxed{
\epsilon_\square(x)
=
q_Y(Fx)-\overline F(q_Xx)
}
\]

只在具有加法或差值结构的模型中成立。

更一般地，可以定义成一条路径、距离或关系见证：

\[
q_Y(Fx)
\rightsquigarrow
\overline F(q_Xx).
\]

精确方格即该见证为恒等路径。

---

## 40.21 加性模型中的组合恒等式

设：

\[
F:X\to Y,
\qquad
G:Y\to Z,
\]

并给出候选商 FLOW：

\[
\overline F:B\to C,
\qquad
\overline G:C\to D.
\]

定义：

\[
\epsilon_F
=
q_YF-\overline Fq_X,
\]

\[
\epsilon_G
=
q_ZG-\overline Gq_Y.
\]

则：

\[
\boxed{
\epsilon_{GF}
=
\epsilon_G\circ F
+
\overline G\circ\epsilon_F.
}
\]

### 证明

\[
\begin{aligned}
q_ZGF-\overline G\overline Fq_X
&=
(q_ZG-\overline Gq_Y)F
+\overline G(q_YF-\overline Fq_X).
\end{aligned}
\]

即得。 \(\square\)

所以 carry 不是无结构误差；它服从链式运输律。

---

# Part IV：截面、carry cocycle 与 gauge

## 40.22 局部余坐标需要截面

在加性扩张中，设：

\[
0\to R\overset{i}\to X\overset{q}\to B\to0.
\]

若给出集合截面：

\[
s:B\to X,
\qquad
qs=\operatorname{id}_B,
\]

则每个 \(x\) 可相对于该截面写成：

\[
x=s(qx)+i(r_s(x)).
\]

但 \(s\) 是附加数据，不是 CUT 的定义性组成。

---

## 40.23 加法 carry

### 定义 40.14（截面 carry）

定义：

\[
\boxed{
\kappa_s(a,b)
=
s(a)+s(b)-s(a+b).
}
\]

由于：

\[
q(\kappa_s(a,b))=0,
\]

它落在余核 \(R\) 中。

商余坐标上的加法为：

\[
\boxed{
(a,r)\boxplus_s(b,t)
=
\left(
a+b,\,
r+t+\kappa_s(a,b)
\right).
}
\]

---

## 40.24 结合律产生 cocycle 恒等式

### 定理 40.5（carry cocycle）

加法结合律蕴含：

\[
\boxed{
\kappa_s(a,b)
+
\kappa_s(a+b,c)
=
\kappa_s(b,c)
+
\kappa_s(a,b+c).
}
\]

### 证明

分别展开：

\[
s(a)+s(b)+s(c)-s(a+b+c)
\]

的两种括号方式。 \(\square\)

因此：

\[
\boxed{
\text{结合律是 carry 的路径无关性。}
}
\]

---

## 40.25 截面变化是 gauge 变化

若：

\[
s'(a)=s(a)+\beta(a),
\]

则：

\[
\boxed{
\kappa_{s'}(a,b)
=
\kappa_s(a,b)
+
\beta(a)+\beta(b)-\beta(a+b).
}
\]

即：

\[
\kappa_{s'}=\kappa_s+\delta\beta.
\]

所以：

- 具体 carry 数值依赖坐标截面；
- 接缝的上同调类在适当模型中保持不变；
- \([\kappa]=0\) 表示存在一种截面把 carry 平坦化。

但本节不声称每种非线性、非群或高范畴 carry 都由普通群上同调完全分类。

---

## 40.26 无截面时的正确对象

当不存在全局截面时，不应伪造一个全局余数函数。

正确数据是：

- 局部截面 \(s_i\)；
- 交叠上的 transition \(g_{ij}\)；
- 三重交叠上的 coherence；
- 路径绕行后的 monodromy；
- 可能的高阶 cocycle。

所以：

\[
\boxed{
\text{全局余量不是一个数，而可能是一套局部纤维与接缝图册。}
}
\]

这正是项目 solenoid、量子上下文和锚定观察者结构共享的骨架。

---

# Part V：因果完成与记忆的纯定义构造

## 40.27 预测等价

设：

- \(P\) 是过去类型；
- \(F\) 是未来观察类型；
- \(K:P\to\mathcal D(F)\) 给出每个过去的未来条件律。

定义：

\[
p\sim_Kp'
\iff
K(p)=K(p').
\]

### 定义 40.15（因果状态 CUT）

定义：

\[
\boxed{
q_K:P\to\operatorname{Im}(K),
\qquad
q_K(p)=K(p).
}
\]

它直接把所有未来预测相同的过去归为一类。

这不需要假设某个抽象“最小充分统计量”存在；它由 \(K\) 的像显式构造。

---

## 40.28 规范因果完成

给定任意当前 CUT：

\[
q:P\to C,
\]

定义增强 CUT：

\[
\boxed{
q^\sharp(p)
=
\left(
q(p),K(p)
\right).
}
\]

则：

\[
K
\]

显然下降到 \(q^\sharp\)：

\[
\overline K(c,\mu)=\mu.
\]

所以 \(q^\sharp\) 是一个显式的预测闭合扩张。

它未必最小，因为可能存在冗余的 \(q(p)\) 坐标。

将其再商掉未来律相同的部分，得到 \(q_K\)，才是规范预测商。

---

## 40.29 最小性

### 定理 40.6（因果状态因子化）

若某个 CUT：

\[
r:P\to R
\]

预测充分，即存在：

\[
\overline K:R\to\mathcal D(F)
\]

满足：

\[
K=\overline K\circ r,
\]

则 \(q_K\) 通过 \(r\) 因子化：

\[
\boxed{
q_K
=
\operatorname{Im}(\overline K)\circ r.
}
\]

因此，任何预测充分接口至少要区分所有不同未来律。

在适当像／商同构意义下，\(q_K\) 是最粗预测充分 CUT。

这是一条构造性普适性质，而不是外加“最小因果状态公理”。

---

## 40.30 记忆是状态化的 carry

在块动力模型：

\[
\begin{aligned}
v_{t+1}&=Av_t+Bh_t,\\
h_{t+1}&=Cv_t+Dh_t,
\end{aligned}
\]

消去 \(h_t\) 得：

\[
v_{t+1}
=
Av_t
+
BD^th_0
+
\sum_{j=0}^{t-1}BD^{t-1-j}Cv_j.
\]

定义记忆核：

\[
K_{t-1-j}=BD^{t-1-j}C.
\]

所以：

\[
\boxed{
\text{记忆不是新增公理；
它是隐藏余纤维被消去后，carry 在商动力中的精确残影。}
}
\]

若重新把足够的隐藏状态加入可见状态，非 Markov 商动力可恢复为一阶闭合 FLOW。

---

## 40.31 记忆最小化问题

定义一类候选扩张：

\[
m:P\to M
\]

使：

\[
(C,m)
\]

预测充分。

最小记忆问题是寻找在某种复杂度、维数或 refinement 序下最小的 \(M\)。

C-IRPT 不假设该最小对象总存在；它把存在性转化为：

- 像构造；
- 商构造；
- 紧致性；
- 有限状态最小化；
- 或伴随函子存在性；

的具体定理。

---

# Part VI：观察者与完成

## 40.32 观察者塔

设指标范畴为 \(I\)，每层有：

\[
X_i,
\]

层间映射：

\[
p_{ji}:X_j\to X_i.
\]

### 定义 40.16（相容观察者）

观察者类型定义为：

\[
\boxed{
\operatorname{Obs}(\mathbf X)
=
\sum_{x:\prod_iX_i}
\prod_{j\succeq i}
p_{ji}(x_j)=x_i.
}
\]

它就是逆极限 cone 的项类型。

该定义不保证非空。

---

## 40.33 ADMIT 后的物理观察者

若每层有：

\[
A_i:X_i\to\mathsf{Prop},
\]

定义：

\[
\boxed{
\operatorname{PhysObs}(\mathbf X,\mathbf A)
=
\sum_{x:\operatorname{Obs}(\mathbf X)}
\prod_iA_i(x_i).
}
\]

还可以加入统一界：

\[
\sup_iE_i(x_i)<\infty,
\]

或矩阵级正性、normality、可积性等条件。

因此：

\[
\boxed{
\text{形式相容}
\neq
\text{物理可实现}.
}
\]

---

## 40.34 形式完成与实现完成

### 定义 40.17（形式完成）

\[
\widehat X_{\mathrm{form}}
=
\varprojlim_iX_i.
\]

### 定义 40.18（实现谓词）

定义：

\[
\operatorname{Realizable}:
\widehat X_{\mathrm{form}}
\to\mathsf{Prop}.
\]

### 定义 40.19（实现完成）

\[
\boxed{
\widehat X_{\mathrm{real}}
=
\sum_{x:\widehat X_{\mathrm{form}}}
\operatorname{Realizable}(x).
}
\]

定义本身不保证：

\[
\widehat X_{\mathrm{real}}\neq\varnothing.
\]

---

## 40.35 完成中的三类缺陷

给定有限层缺陷：

\[
\delta_i,
\]

必须区分：

\[
\boxed{
\begin{aligned}
\delta_{\mathrm{stage}}
&=\text{有限层本身的余差},\\
\delta_{\mathrm{limit}}
&=\text{相容极限中的闭合失败},\\
\delta_{\mathrm{real}}
&=\text{形式 section 无法实现的缺陷}.
\end{aligned}
}
\]

理想的完成保持定理应具有形式：

\[
\boxed{
\delta_\infty
\preceq
\liminf_i\delta_i
+
\delta_{\mathrm{real}}.
}
\]

这不是定义，而是未来需要在每种模型中证明的主定理。

---

## 40.36 一个定义不能替代紧致性

以下命题都不是“完成”的定义性后果：

\[
\varprojlim_iX_i\neq\varnothing;
\]

\[
\varprojlim_iX_i\text{ 紧致};
\]

\[
\varprojlim_iX_i\text{ 连通};
\]

\[
\text{正锥在极限中保持严格非退化};
\]

\[
\text{形式幂级数可解析实现};
\]

\[
\text{有限正 Gram 塔产生可闭 GNS 形式}.
\]

它们必须依赖各领域的：

- 紧致性；
- 完备性；
- 一致界；
- Montel 型定理；
- 能量估计；
- form closability；
- Mittag–Leffler 条件；
- 或其他实现定理。

---

# Part VII：对角化作为可选扩张

## 40.37 对角化不属于最小静态核心

CUT、FLOW、ADMIT、ANCHOR 本身不自动提供：

- self-application；
- evaluation；
- 指数对象；
- 无固定点 twist；
- 命名清单。

因此对角化是 C-IRPT 的扩展模块：

\[
\boxed{
\mathrm{C\text{-}IRPT}_\Delta.
}
\]

---

## 40.38 对角数据

给定：

\[
g:A\to(A\to Y),
\]

评价：

\[
\operatorname{ev}(f,a)=f(a),
\]

和 twist：

\[
\tau:Y\to Y,
\]

定义：

\[
\boxed{
d_g(a)=\tau(g(a)(a)).
}
\]

如果：

\[
\forall y,\quad\tau(y)\neq y,
\]

则：

\[
d_g\notin\operatorname{range}(g).
\]

该结论是条件定理，不是对角化定义的一部分。

---

## 40.39 构造性逃逸证明

假设存在：

\[
a_0:A
\]

使：

\[
g(a_0)=d_g.
\]

在 \(a_0\) 处评价：

\[
g(a_0)(a_0)
=
d_g(a_0)
=
\tau(g(a_0)(a_0)),
\]

与 \(\tau\) 无固定点矛盾。

故不存在这样的 \(a_0\)。 \(\square\)

该证明不需要排中律。

---

## 40.40 对角缺陷与普通 carry 的区别

普通 carry 问：

\[
\text{FLOW 能否下降到当前 CUT？}
\]

对角缺陷问：

\[
\text{当前 CUT 是否声称能够表示包含自身评价规则的全部对象？}
\]

所以：

\[
\boxed{
\text{对角化是自表示闭合审计，不是所有余差的同义词。}
}
\]

---

# Part VIII：范畴论学术定位

## 40.41 C-IRPT 的基础对象不是集合，而是方格

C-IRPT 的基本情形是：

\[
\begin{array}{ccc}
X&\xrightarrow{F}&Y\\
\downarrow q_X&&\downarrow q_Y\\
B&\xrightarrow{\overline F}&C.
\end{array}
\]

其中：

- 水平箭头是 FLOW；
- 垂直箭头是 CUT；
- 方格记录下降、缺陷或 transport；
- ADMIT 是附着于对象和箭头的 doctrine；
- ANCHOR 是点、截面或 cone。

因此其最自然数学容器不是普通一范畴，而是：

\[
\boxed{
\text{双范畴／equipment／double category}.
}
\]

---

## 40.42 缺陷富集

选择一个有序值幺半对象：

\[
\mathcal V
\]

表示缺陷值，例如：

\[
[0,\infty],
\]

正锥，

半序集合，

或见证类型。

对每个方格赋：

\[
\delta(\square)\in\mathcal V.
\]

要求：

\[
\delta(\square)=0
\iff
\square\text{ 精确交换},
\]

并满足水平、垂直组合律或次可加界。

因此，定量版本可学术化为：

\[
\boxed{
\textbf{defect-enriched double category of interfaces and processes}.
}
\]

---

## 40.43 ADMIT 是 doctrine

ADMIT 不应只是一个全局布尔函数，而应随模型变化形成：

- 子对象纤维；
- 谓词纤维；
- 正锥纤维；
- effect module；
- 可计算对象类；
- 能量有限对象类。

它需要沿 FLOW 有：

- 正向保持；
- 逆像；
- 推前；
- 张量稳定；
- 极限稳定。

因此范畴论上更接近：

\[
\boxed{
\text{indexed doctrine／fibration of admissible predicates}.
}
\]

---

## 40.44 ANCHOR 是点与 section

在集合模型中：

\[
a:1\to X
\]

是点。

在纤维模型中：

\[
a:B\to X
\]

可能是 section。

在逆系统中，ANCHOR 是 compatible cone。

在量子 GNS 模型中，它可以是：

- 状态；
- 循环向量；
- 正泛函；
- 记录链。

所以 ANCHOR 是一个角色族，而不是单一代数类型。

---

## 40.45 学术名称

本节建议正式名称：

\[
\boxed{
\textbf{Constructive Interface–Remainder Process Theory}
}
\]

缩写：

\[
\boxed{
\textbf{C-IRPT}.
}
\]

学术副标题可为：

> **A conservative definitional doctrine for dependent fibers, descent defects, causal completion, and observer sections.**

数学主归属：

\[
\boxed{
\text{Applied Category Theory}
+
\text{Categorical Systems Theory}
+
\text{Constructive Type Theory}.
}
\]

次级关联包括：

- fibrations and indexed categories；
- double categories；
- process theories；
- coalgebra；
- abstract interpretation；
- Markov categories；
- operator systems；
- noncommutative probability；
- sheaf contextuality；
- formal completions；
- cohomological extension theory。

---

# Part IX：与相邻理论的严格区分

## 40.46 与普通范畴论的区别

普通范畴论已经提供对象、态射、组合和普适性质。

C-IRPT 的新增重点不在“重新发明态射”，而在同时指定：

1. 哪些态射承担 CUT 角色；
2. 哪些态射承担 FLOW 角色；
3. CUT 与 FLOW 方格的下降缺陷；
4. 余纤维与 carry；
5. 准入 doctrine；
6. 锚定与观察者 section；
7. refinement 与 realization；
8. 自应用审计扩展。

因此它是一个特定的结构包，而不是替代范畴论。

---

## 40.47 与抽象解释的关系

抽象解释研究：

\[
\text{concrete state}
\to
\text{abstract state}
\]

以及抽象转换的可靠性。

C-IRPT 的 CUT 与之相近，但额外强调：

- 被商掉的依赖余纤维；
- carry 的因果回流；
- 记录与观察者；
- 多层逆完成；
- ADMIT 与物理实现；
- 对角自审计。

所以抽象解释是 C-IRPT 的一个重要模型，而不是全部理论。

---

## 40.48 与煤代数的关系

煤代数研究：

\[
X\to F(X)
\]

的行为与最终语义。

C-IRPT 中 FLOW 可以是煤代数结构，预测等价可以由行为映射定义。

但 C-IRPT 额外保留：

- 不同 CUT；
- 余纤维；
- 下降缺陷；
- 准入；
- 锚定；
- 多模型 completion。

---

## 40.49 与 Markov category 的关系

概率 FLOW 可以位于 Markov category 中。

CUT 可以实现为 statistic 或 channel。

预测充分、恢复与数据处理等号可在该模型中表达。

但 C-IRPT 不把所有 FLOW 预设为随机过程；确定性、线性、解析、程序与量子 FLOW 都属于不同模型。

---

## 40.50 与 sheaf／topos 的关系

当局部 CUT 形成覆盖并需要拼接时：

- section 表示局部选择；
- cocycle 表示接缝；
- 全局 section 不存在表示 contextuality 或拓扑障碍。

C-IRPT 可以使用 sheaf 作为局部—全局模型，但不把所有余量都等同于上同调类。

---

# Part X：项目各理论在 C-IRPT 中的重排

## 40.51 算术

### CUT

\[
q_b(n)=n\bmod b.
\]

### REMAINDER

给定余类下的整数纤维。

### FLOW

加法、乘法、取负、除法算法。

### CARRY

标准数字截面不保持加法或乘法的 cocycle。

### ADMIT

整数范围、规范余数区间、终止性、唯一表示。

所以：

\[
\boxed{
\text{算术}
=
\text{商余纤维上的 FLOW 与 carry}.
}
\]

---

## 40.52 GICT 与 PZG

项目的 A/Z/G 三轴可读为不同 CUT：

\[
\begin{aligned}
A&=\text{尺度商},\\
Z&=\text{数字展开商},\\
G&=\text{相位商}.
\end{aligned}
\]

PZG 素数指数坐标提供离散乘法纤维。

Zeckendorf 归约中的进位提供 carry。

黄金比例相关固定点提供特定 FLOW 下的自相似锚。

但这些是 C-IRPT 的算术模型，不应被定义成 C-IRPT 的唯一基础模型。

---

## 40.53 Solenoid

正合列：

\[
0\to K\to\Sigma\to\mathbb T\to0
\]

给出：

- 可见连续基底 \(\mathbb T\)；
- 隐藏 profinite 纤维 \(K\)；
- 局部 ANCHOR；
- 绕行 transport；
- monodromy carry；
- 交叉积 FLOW；
- 记录账本。

它是“连续基底 + 离散逆完成纤维 + 非平凡接缝”的规范样本。

---

## 40.54 量子观察者

### CUT

operator system 或测量上下文：

\[
q_O(\rho)
=
\left(
\operatorname{Tr}(\rho E)
\right)_{E\in\mathcal S_O}.
\]

### FLOW

CP channel、instrument、unitary 或 modular flow。

### ADMIT

矩阵正锥塔：

\[
\{M_n(\mathcal A)_+\}_{n\ge1}
\]

以及归一化、normality 和张量相容。

### ANCHOR

状态、GNS 循环向量或记录链。

### CARRY

被当前 operator system 商掉的相干或关联仍进入未来读出。

因此：

\[
\boxed{
\text{量子性}
=
\text{多个矩阵有序 CUT 网络不能由单一全局经典截面同时平坦化}.
}
\]

---

## 40.55 正锥纲领

GNS 恒等式：

\[
\operatorname{Tr}(\rho x^*x)
=
\|x\sqrt\rho\|_{\mathrm{HS}}^2
\]

说明 ADMIT 的一个核心形式是：

\[
\boxed{
\text{自配对能够实现为范数平方。}
}
\]

数据处理不等式可写成：

\[
\text{原区分量}
=
\text{CUT 后区分量}
+
\text{非负余量}.
\]

所以：

\[
\boxed{
\text{不等式是隐藏余量后的影；
等式是余量归零和恢复闭合。}
}
\]

---

## 40.56 BEDC 与世界模型

在无外部输入的有限模型中：

- CUT 是有限预测状态分类；
- FLOW 是自回归更新；
- ADMIT 是参数、上下文和计算预算；
- ANCHOR 是初始 prompt／隐藏状态／记录；
- carry 是当前预测类遗漏、但仍影响未来的隐藏差异。

“一次稳定即永久稳定”对应：

\[
\text{预测 CUT 达到 FLOW 不变闭包}.
\]

外部工具或数据不是简单噪声，而是：

\[
\boxed{
\text{向旧商世界注入新的余坐标并改变 carry 结构。}
}
\]

---

# Part XI：RH 中定义与证明的边界

## 40.57 RH 的 C-IRPT 数据

可以定义一个候选结构：

\[
\mathfrak Z
=
\left(
\mathsf{CUT}_{\mathrm{prime}},
\mathsf{CUT}_{\mathrm{Weil}},
\mathsf{CUT}_{\mathrm{Li}},
\mathsf{CUT}_{\mathrm{NB}},
\mathsf{FLOW}_{\log},
\mathsf{Mirror},
\mathsf{ADMIT},
\mathsf{ANCHOR}
\right).
\]

但这只是签名。

必须另外构造和证明：

- prime-side FLOW；
- 零点谱实现；
- 正性；
- 归一化；
- 镜像内部性；
- normal completion；
- 显式公式忠实性；
- 极限保持。

---

## 40.58 离线二地址模型是定义性实例

对假想：

\[
\rho=\frac12+\delta+i\gamma,
\]

可定义：

\[
G_\rho
=
i\gamma I
+
\delta
\begin{pmatrix}
0&1\\
1&0
\end{pmatrix}.
\]

并定义临界商投影 \(P_{\mathrm{crit}}\)。

直接计算：

\[
\boxed{
\|[P_{\mathrm{crit}},G_\rho]\|
=
|\delta|.
}
\]

这是一条二维模型定理。

它不证明真实 zeta 存在该 \(G_\rho\) 表示。

---

## 40.59 定义性 RH 伪证明禁令

禁止以下步骤：

1. 定义 \(G_\rho\) 时直接输入零点实部；
2. 定义 ADMIT 时要求 \(\delta=0\)；
3. 声称所有物理模式必须 ADMIT；
4. 得出 RH。

该推理把结论写入准入谓词。

正确路线必须是：

\[
\boxed{
\text{prime data}
\to
\text{无循环构造 }G
\to
\text{证明正保归一}
\to
\text{证明零点忠实谱实现}
\to
\text{镜像刚性}
\to
\delta=0.
}
\]

---

## 40.60 条件正因果镜像刚性

如果已构造同一个 base-norm 正空间，并证明：

\[
T_tv_\rho
=
e^{(\delta+i\gamma)t}v_\rho,
\]

则正、保归一 FLOW 的收缩给出：

\[
\delta\le0.
\]

若镜像模式也在同一空间：

\[
T_tv_\rho^\sharp
=
e^{(-\delta+i\gamma)t}v_\rho^\sharp,
\]

则：

\[
-\delta\le0.
\]

故：

\[
\boxed{
\delta=0.
}
\]

这条线性刚性是条件定理。

未完成工作全部位于前件的 prime-side 构造，而不是二维不等式本身。

---

# Part XII：严格构造性 Lean 核心

## 40.61 最小定义

```lean
universe u v w

structure Cut (X : Type u) where
  Base : Type v
  proj : X → Base

def Fiber {X : Type u} (q : Cut X) (b : q.Base) : Type u :=
  {x : X // q.proj x = b}

def Flow (X : Type u) (Y : Type v) : Type (max u v) :=
  X → Y

def Admit (X : Type u) : Type u :=
  X → Prop

def Real {X : Type u} (A : Admit X) : Type u :=
  {x : X // A x}

def Anchor {X : Type u} (q : Cut X) (b : q.Base) : Type u :=
  Fiber q b
```

这些定义不需要领域公理。

---

## 40.62 Refinement 与下降

```lean
def Refines {X : Type u} (q q' : Cut X) : Type _ :=
  Σ p : q'.Base → q.Base,
    ∀ x, q.proj x = p (q'.proj x)

def Descends
    {X : Type u} {Y : Type v}
    (qX : Cut X) (qY : Cut Y)
    (F : X → Y) : Type _ :=
  Σ fbar : qX.Base → qY.Base,
    ∀ x, qY.proj (F x) = fbar (qX.proj x)

def CarryWitness
    {X : Type u} {Y : Type v}
    (qX : Cut X) (qY : Cut Y)
    (F : X → Y) : Type _ :=
  Σ x y : X,
    qX.proj x = qX.proj y ∧
    qY.proj (F x) ≠ qY.proj (F y)
```

注意 `Descends` 使用 `Type` 而不是只用 `Prop`，因此下降映射和交换证明均被保留为数据。

---

## 40.63 规范依赖分解

可定义：

```lean
def split {X : Type u} (q : Cut X) :
    X → Σ b : q.Base, Fiber q b :=
  fun x => ⟨q.proj x, ⟨x, rfl⟩⟩

def merge {X : Type u} (q : Cut X) :
    (Σ b : q.Base, Fiber q b) → X :=
  fun z => z.2.1
```

并证明二者互逆。

该模块应成为：

```text
D5/S0/InterfaceKernel/DependentFiber.lean
```

的首个核心定理。

---

## 40.64 RawModel 与 IsLawful

```lean
structure RawIRPT where
  Obj    : Type u
  cut    : Cut Obj
  step   : Obj → Obj
  admit  : Obj → Prop

def IsLawful (M : RawIRPT) : Prop :=
  (∀ x, M.admit x → M.admit (M.step x)) ∧
  Descends M.cut M.cut M.step
```

不应直接写：

```lean
axiom everyRawIRPT_isLawful : ∀ M, IsLawful M
```

正确方式是对具体模型证明：

```lean
theorem concrete_isLawful :
  IsLawful concrete := by
  ...
```

---

## 40.65 不使用选择生成全局截面

禁止从：

\[
\forall b,\ \exists x,\ q(x)=b
\]

未经审计地得到一个全局函数：

\[
s:B\to X.
\]

严格构造版本要求：

\[
\forall b,\ \sum_{x:X}q(x)=b,
\]

即每个 \(b\) 都携带具体见证。

如果只有命题截断的存在性，构造全局 section 可能需要 choice。

因此核心库默认保留依赖纤维，不提供通用 `chooseSection`。

---

## 40.66 Quotient 的纪律

若使用 Lean quotient，必须区分：

- 商类型的形成；
- 商映射；
- 商递归；
- 商代表选择。

`Quot.sound` 允许从关系证明商相等。

它不提供每个商类的代表选择。

因此：

\[
\boxed{
\text{形成商不等于选择规范余数。}
}
\]

---

## 40.67 经典便利层与构造核心层

建议库分为：

```text
InterfaceKernel/Constructive/
InterfaceKernel/Classical/
```

构造核心层禁止：

- `Classical.choice`；
- 无声明排中律；
- 非构造性有限见证提取；
- 隐式全局截面。

经典便利层可以在明确 import 后提供：

- 选择截面；
- 基选择；
- Hahn–Banach 分离；
- 紧致性等价；
- 传统谱理论工具。

所有下游定理必须标出使用了哪一层。

---

## 40.68 基础信任账

“无领域公理”审计应报告：

1. Lean kernel；
2. quotient soundness；
3. proof irrelevance／propext 是否出现；
4. Classical.choice 是否出现；
5. 外部分析定理的公理闭包；
6. 是否有 `sorry`；
7. 是否有项目自定义 `axiom`。

因此：

\[
\boxed{
\texttt{\#print axioms}
}
\]

不是装饰，而是 C-IRPT 无暗账纪律的一部分。

---

# Part XIII：正式理论的主定理计划

## 40.69 自由语法模型

第一项承重工作是定义 C-IRPT 的自由语法：

- 对象类型；
- CUT 生成元；
- FLOW 生成元；
- 方格；
- ADMIT 谓词；
- ANCHOR 项；
- 组合；
- 等式与重写。

然后证明其初始性：

\[
\boxed{
\operatorname{Hom}
(
\mathsf{FreeCIRPT}(\Sigma),
M
)
\simeq
\operatorname{Interpretation}(\Sigma,M).
}
\]

这会证明 C-IRPT 不是一组比喻，而是一门有明确模型语义的形式演算。

---

## 40.70 健全性

对每个模型 \(M\)，定义解释：

\[
\llbracket-\rrbracket_M.
\]

证明所有推导规则在模型中保持：

- 类型正确；
- 方格组合；
- defect 零值；
- ADMIT；
- anchor 相容性。

---

## 40.71 相对完备性

在可控片段中，研究：

\[
\text{所有模型中成立}
\Longrightarrow
\text{自由语法中可推导}.
\]

完整高阶版本可能过强，但有限代数片段、线性片段和有限状态片段可以分别建立完备性结果。

---

## 40.72 因果完成反射

目标是证明因果闭合对象形成反射子范畴：

\[
\mathbf{CausalClosed}
\hookrightarrow
\mathbf{InterfaceFlow}.
\]

存在：

\[
\boxed{
\mathsf{CausalComplete}
\dashv
\mathsf{Forget}.
}
\]

在预测核已给出的模型中，因果状态像构造是该伴随的候选。

---

## 40.73 缺陷表示定理

抽象 defect 不应只有名字。

目标是在不同模型中证明：

\[
\partial=0
\]

分别等价于：

\[
\begin{aligned}
&\text{kernel-pair preservation},\\
&\text{无 causal carry witness},\\
&PFQ=0,\\
&\text{数据处理等号／恢复},\\
&\text{transition cocycle 平凡},\\
&\text{余尾消失},\\
&\text{全局 section 可拼接}.
\end{aligned}
\]

数值缺陷不必相同，但零缺陷的语义应由模型函子保持。

---

## 40.74 可容许完成保持

目标是在明确条件下证明：

\[
\delta_i\to0
\]

何时推出：

\[
\delta_\infty=0.
\]

同时构造反例说明以下失败机制：

- 质量逃向无穷；
- 正锥退化；
- normality 丢失；
- 形式 germ 不收敛；
- 极限与商不交换；
- section 只局部存在；
- derived obstruction 非零。

---

## 40.75 原语独立性

要证明语义角色最小性，应构造模型分离：

1. 同一 FLOW，不同 CUT，产生不同 carry；
2. 同一 CUT，不同 FLOW，产生不同因果；
3. 同一 CUT/FLOW，不同 ADMIT，产生不同真实对象；
4. 同一结构，一个有 compatible ANCHOR，一个无；
5. 同一有限塔，不同 realization doctrine，产生不同连续对象。

若删除某一角色会使这些模型不可区分，则说明该角色不是冗余语义。

---

## 40.76 模型转移定理

必须选择至少三个真正异质的模型建立非平凡转移：

1. 有限集合／自动机；
2. 有限维线性或概率系统；
3. operator-system／量子系统。

证明同一抽象定理在三个模型中分别给出具体、已有意义的结果。

这会把“统一语言”升级为“统一证明运输”。

---

# Part XIV：可发表性与学术结构

## 40.77 第一篇核心论文的合理范围

建议首篇独立论文只处理：

> **Constructive Interface–Remainder Process Theory: Dependent Fibers, Descent Defects, and Causal Completion**

核心结果控制在：

1. 无选择依赖商余分解；
2. role-typed CUT/FLOW/ADMIT/ANCHOR；
3. 精确下降与 carry witness；
4. 方格组合与缺陷链式律；
5. 因果状态的规范像构造；
6. 观察者 cone 与形式／实现完成；
7. 三个模型实例；
8. Lean 构造核心。

不应在第一篇把 RH、量子引力、经济和全部哲学主张都作为主定理。

---

## 40.78 第二篇：定量缺陷双范畴

第二篇可以研究：

- \(\mathcal V\)-值 defect；
- 水平／垂直组合；
- tensor；
- recovery；
- completion；
- 反射子范畴；
- stability constants。

标题可为：

> **Defect-Enriched Double Categories of Observation and Dynamics**

---

## 40.79 第三篇：矩阵有序观察者

第三篇处理：

- operator systems；
- matrix cone towers；
- completely positive FLOW；
- instruments；
- record-generated centers；
- GNS；
- contextuality；
- observer completion。

---

## 40.80 RH 论文必须独立

只有在 prime-side 六座桥中至少关闭一座具有新数学内容的桥后，才适合形成 RH 专文。

在此之前，RH 应保持为：

\[
\boxed{
\text{C-IRPT 的高风险条件性应用与研究程序。}
}
\]

而不是理论合法性的主要宣传依据。

---

# Part XV：严格非主张

## 40.81 本节不声称

1. 不声称数学可以脱离任何基础逻辑而绝对无公理。
2. 不声称定义能够生成未构造的存在。
3. 不声称定义 `Observer` 就证明观察者非空。
4. 不声称定义 `Realizable` 就证明形式完成可实现。
5. 不声称每个 CUT 都满射。
6. 不声称每个 CUT 都有全局截面。
7. 不声称每个依赖纤维系统都是直积。
8. 不声称所有 carry 都有数值。
9. 不声称所有非下降都可构造显式 witness。
10. 不声称所有 carry 都由普通群上同调分类。
11. 不声称所有 refinement 构成反对称偏序而非因子化范畴。
12. 不声称所有因果完成都有最小有限状态。
13. 不声称所有逆系统都有非空极限。
14. 不声称所有形式 section 都满足 ADMIT。
15. 不声称所有有限层正性自动通过极限。
16. 不声称所有解析形式 germ 都能全局实现。
17. 不声称 CUT/FLOW/ADMIT/ANCHOR 是唯一可能的语义角色集。
18. 不声称四角色已经被证明绝对最小。
19. 不声称 C-IRPT 替代普通范畴论。
20. 不声称 C-IRPT 替代领域具体估计。
21. 不声称量子理论只是一种坐标伪影。
22. 不声称非交换性总能被更大空间平坦化。
23. 不声称时间只由 carry 产生。
24. 不声称熵只有一种余纤维解释。
25. 不声称对角化是全部闭合缺陷的同义词。
26. 不声称离线二维模型是真实 zeta 算子模型。
27. 不声称 prime-side 正 FLOW 已经构造。
28. 不声称函数方程镜像已在同一正 normal completion 中实现。
29. 不声称条件正因果镜像刚性的前件已对 zeta 关闭。
30. 不声称本节证明 RH。
31. 不声称本节新增定理已经 Lean-closed。
32. 不声称无 `Classical.choice` 就自动没有任何其他基础依赖。
33. 不声称保守定义扩张本身产生新领域结论。
34. 不声称术语统一等于对象同构。
35. 不声称项目全部历史文档必须被立即重写为 C-IRPT。

---

# Part XVI：本节最终统一

## 40.82 最底层公式

对任意 CUT：

\[
q:X\to B,
\]

都有规范依赖分解：

\[
\boxed{
X
\simeq
\sum_{b:B}
\sum_{x:X}
(q(x)=b).
}
\]

这是无选择、无全局截面、无领域公理的商余正规形。

---

## 40.83 最小语义核

\[
\boxed{
\mathfrak K_{\mathrm{CIRPT}}
=
(
\mathsf{CUT},
\mathsf{FLOW},
\mathsf{ADMIT};
\mathsf{ANCHOR}
).
}
\]

其中：

\[
\begin{aligned}
\mathsf{CUT}
&=\text{规定当前相对同一性},\\
\mathsf{FLOW}
&=\text{运输对象和差异},\\
\mathsf{ADMIT}
&=\text{形式对象进入可实现世界的谓词},\\
\mathsf{ANCHOR}
&=\text{合法纤维中的具体项}.
\end{aligned}
\]

---

## 40.84 第一层派生概念

\[
\boxed{
\mathsf{REMAINDER}
=
\operatorname{Fiber}(\mathsf{CUT}),
}
\]

\[
\boxed{
\mathsf{CARRY}
=
\operatorname{FailureOfDescent}
(\mathsf{CUT},\mathsf{FLOW}),
}
\]

\[
\boxed{
\mathsf{MEMORY}
=
\operatorname{StateRealization}
(\text{historical carry}),
}
\]

\[
\boxed{
\mathsf{OBSERVER}
=
\operatorname{CompatibleAdmissibleAnchor}
(\mathsf{CUT}^{\infty}),
}
\]

\[
\boxed{
\mathsf{CONTINUUM}
=
\operatorname{Realizable}
\left(
\operatorname{InverseComplete}
(\mathsf{CUT}^{\infty})
\right).
}
\]

---

## 40.85 理论的准确学术声明

\[
\boxed{
\textbf{C-IRPT 是构造性依赖类型论上的保守定义性过程学说。}
}
\]

它研究：

\[
\boxed{
\text{界面怎样制造相对同一性，
余纤维怎样保存被商掉的差异，
FLOW 怎样把余差重新带回未来，
ADMIT 怎样区分形式结构与可实现结构，
ANCHOR 怎样把整体固定为一个观察起点，
完成怎样把有限分类历史变为全局对象。}
}
\]

---

## 40.86 “无公理”的最终准确表达

正确宣言不是：

\[
\text{“该理论不依赖任何公理。”}
\]

而是：

\[
\boxed{
\text{“该理论不以新增领域公理填补结构缺口；
缺口要么保持为显式空类型，
要么由构造项、见证、实现定理或带前件证明关闭。”}
}
\]

因此：

\[
\boxed{
T_{\mathrm{CIRPT}}
=
T_{\mathrm{base}}
+
\text{可展开定义}
+
\text{显式构造}
+
\text{条件定理}.
}
\]

---

## 40.87 最终一句

\[
\boxed{
\text{定义能够告诉我们什么结构算作世界；
只有构造和证明才能告诉我们这样的世界是否存在。}
}

---

# 41. 追加：构造性界面—余量过程论的完整形式化演算
## A Complete Formal Calculus of Constructive Interface–Remainder Processes
### Dependent Fibers, Descent, Carry, Causal Completion, Information, Geometry, Quantum Order, and the Zeta Interface

## 41.0 文档地位、目标与真值边界

本节在第 38–40 节基础上，给出一套可直接拆分为 Lean 声明的完整纸面演算。目标不是再增加一组解释性口号，而是把下列主链统一为一个具有明确类型、依赖、存在见证与普适性质的定义体系：

\[
\boxed{
\mathsf{CUT}
\longrightarrow
\mathsf{FIBER}
\longrightarrow
\mathsf{FLOW}
\longrightarrow
\mathsf{CARRY}
\longrightarrow
\mathsf{MEMORY}
\longrightarrow
\mathsf{RECORD}
\longrightarrow
\mathsf{REFINEMENT}
\longrightarrow
\mathsf{COMPLETION}
\longrightarrow
\mathsf{DIAGONAL}.
}
\]

本节采用以下准确地位：

\[
\boxed{
T_{\mathrm{CIRPT}}
=
T_{\mathrm{base}}
+
\text{可展开定义}
+
\text{显式构造}
+
\text{带前件定理}.
}
\]

其中 \(T_{\mathrm{base}}\) 是冻结的构造性依赖类型论基础。本文不新增关于算术、概率、物理、量子或 zeta 的领域存在公理。

本节不主张：

1. 脱离任何基础逻辑的绝对零公理数学；
2. 任意 CUT 都有全局截面；
3. 任意形式逆极限都非空；
4. 任意形式 germ 都能解析实现；
5. 任意 carry 都由普通群上同调完整分类；
6. 任意宏观规律都能从本节定义自动推出；
7. 任意量子结构都已还原为经典商余；
8. 任意 zeta 零点都已被构造成正动力学谱；
9. 本节已经证明 Riemann 假设；
10. 本节纸面定理已经获得 Lean proof term。

本节的核心纪律是：

\[
\boxed{
\text{不以公理填补结构缺口；
缺口要么保持为空类型，
要么由项、见证、构造或条件定理关闭。}
}
\]

---

# Part I：基础语言与语义角色

## 41.1 冻结基础

设基础系统至少具有：

\[
\mathsf{Type}_u,\qquad
\Pi,\qquad
\Sigma,\qquad
\mathsf{Id},\qquad
\mathbf 0,\qquad
\mathbf 1,\qquad
\mathbb N,
\]

以及：

- 恒等映射；
- 映射复合；
- 依赖函数消去；
- 依赖和消去；
- identity elimination；
- 自然数递归；
- definitional equality。

不默认：

- 排中律；
- 全局选择；
- proof irrelevance 以外的额外等同原则；
- 任意类型可判等；
- 任意商的有效性；
- 任意截面的存在；
- 任意完成的可实现性。

因此：

\[
\boxed{
X:\mathsf{Type}
\not\Rightarrow
\exists x:X.
}
\]

定义一个对象类型，只给出“什么算作该对象”，不自动给出对象本身。

---

## 41.2 四种最小语义角色

真正底层只有有类型态射。为保留语义，定义四种角色：

\[
\boxed{
\mathfrak K
=
(
\mathsf{CUT},
\mathsf{FLOW},
\mathsf{ADMIT},
\mathsf{ANCHOR}
).
}
\]

### 定义 41.1（CUT）

对 \(X:\mathsf{Type}_u\)，一个 CUT 是：

\[
\boxed{
q:X\to B
}
\]

连同可见坐标类型 \(B:\mathsf{Type}_v\)。

### 定义 41.2（FLOW）

一个 FLOW 是任意有类型映射：

\[
\boxed{
F:X\to Y.
}
\]

### 定义 41.3（ADMIT）

一个 ADMIT 是谓词：

\[
\boxed{
A:X\to\mathsf{Prop}.
}
\]

其合法子类型为：

\[
\boxed{
\operatorname{Real}(X,A)
=
\sum_{x:X}A(x).
}
\]

### 定义 41.4（ANCHOR）

一个 anchor 是：

\[
\boxed{
a:\operatorname{Real}(X,A).
}
\]

所以：

\[
a=(x,h),
\qquad
h:A(x).
\]

四者不是四种本体物质，而是同一种态射语言的四种角色：

\[
\boxed{
\begin{aligned}
\mathsf{CUT}&=\text{规定当前可见性},\\
\mathsf{FLOW}&=\text{规定过程与运输},\\
\mathsf{ADMIT}&=\text{规定可实现性},\\
\mathsf{ANCHOR}&=\text{给出一个实际见证}.
\end{aligned}
}
\]

---

## 41.3 原始数据与规律必须分离

定义原始模型：

\[
\boxed{
\mathsf{RawModel}
=
(X,\mathcal Q,\mathcal F,\mathcal A).
}
\]

其中：

- \(X\) 是对象类型；
- \(\mathcal Q\) 是 CUT 集合或类型；
- \(\mathcal F\) 是 FLOW 集合或类型；
- \(\mathcal A\) 是 ADMIT doctrine。

再单独定义：

\[
\boxed{
\mathsf{IsLawful}(M):\mathsf{Prop}.
}
\]

例如 `IsLawful` 可以要求：

- 恒等 FLOW 合法；
- 合法 FLOW 对复合封闭；
- CUT refinement 可复合；
- ADMIT 对指定 FLOW 稳定；
- defect 对复合满足链式界。

打包模型可定义为：

\[
\boxed{
\mathsf{Model}
=
\sum_{M:\mathsf{RawModel}}
\mathsf{IsLawful}(M).
}
\]

这里证明字段不是全局公理；每个模型必须携带自己的证明。

---

## 41.4 模型间翻译

设 \(\mathfrak M,\mathfrak N\) 为两个模型。一个结构保持翻译至少包含：

\[
H_X:X_{\mathfrak M}\to X_{\mathfrak N},
\]

以及 CUT、FLOW、ADMIT 与 anchor 的兼容数据。

理想情形要求：

\[
\boxed{
H(q_{\mathfrak M})
=
q_{\mathfrak N}H,
}
\]

\[
\boxed{
H(F_{\mathfrak M}x)
=
F_{\mathfrak N}(Hx),
}
\]

并且：

\[
A_{\mathfrak M}(x)
\Longrightarrow
A_{\mathfrak N}(Hx).
\]

若模型带定量缺陷 \(\delta\)，则要求存在单调映射 \(\varphi\) 使：

\[
\boxed{
\delta_{\mathfrak N}(H\square)
\preceq
\varphi(\delta_{\mathfrak M}(\square)).
}
\]

只有这种保持结构的翻译，才能把“不同领域使用同一原语”提升为真正的数学统一。

---

# Part II：CUT、依赖纤维与商余正规形

## 41.5 依赖余纤维

给定：

\[
q:X\to B.
\]

### 定义 41.5（余纤维）

对 \(b:B\)，定义：

\[
\boxed{
R_q(b)
=
\sum_{x:X}(q(x)=b).
}
\]

余量不是预先固定的单一类型，而是依赖于商坐标的纤维。

---

## 41.6 规范商—纤维分解

### 定理 41.1（无选择商余正规形）

对任意 \(q:X\to B\)，存在规范等价：

\[
\boxed{
X
\simeq
\sum_{b:B}R_q(b).
}
\]

### 构造

定义：

\[
\eta_q(x)
=
\bigl(
q(x),
x,
\operatorname{refl}_{q(x)}
\bigr).
\]

定义：

\[
\mu_q(b,x,p)=x.
\]

则：

\[
\mu_q\eta_q(x)=x
\]

定义性成立。

对反方向，取：

\[
z=(b,x,p).
\]

需证明：

\[
\eta_q(\mu_q(z))=z.
\]

对：

\[
p:q(x)=b
\]

使用 identity elimination。归约到：

\[
b=q(x),
\qquad
p=\operatorname{refl},
\]

两边定义性相等。证毕。

---

### 推论 41.1（整体的依赖商余形式）

\[
\boxed{
\text{整体}
=
\text{商坐标}
+
\text{依赖于该商坐标的余纤维位置}.
}
\]

该等价不需要：

- 商对象；
- 满射；
- 截面；
- 选择公理；
- 线性结构；
- 度量。

---

## 41.7 平凡直积是额外定理

一般不能无条件写成：

\[
X\simeq B\times R.
\]

### 定义 41.6（全局平凡化）

一个全局平凡化是某个 \(R\) 与等价族：

\[
\theta_b:R_q(b)\simeq R
\qquad
(b:B),
\]

从而得到：

\[
\sum_{b:B}R_q(b)
\simeq
B\times R.
\]

所以：

\[
\boxed{
X\simeq B\times R
}
\]

意味着所有纤维被一致识别为同一个余类型。

在纤维丛、covering、solenoid、量子上下文和非平凡扩张中，这通常是需要证明、且可能失败的全局性质。

---

## 41.8 观察等价与隐藏差异

### 定义 41.7（界面等价）

\[
\boxed{
x\sim_q y
\iff
q(x)=q(y).
}
\]

### 定义 41.8（可见差异）

\[
\boxed{
\operatorname{Visible}_q(x,y)
\iff
q(x)\neq q(y).
}
\]

### 定义 41.9（隐藏余差）

\[
\boxed{
\operatorname{Hidden}_q(x,y)
\iff
x\neq y
\wedge
q(x)=q(y).
}
\]

必须严格区分：

\[
x=y
\]

与：

\[
x\sim_qy.
\]

前者是对象等同，后者只是相对于当前 CUT 不可区分。

---

# Part III：Refinement 与分类塔

## 41.9 Refinement

给定：

\[
q:X\to B,
\qquad
q':X\to B'.
\]

### 定义 41.10（表示性 refinement）

称 \(q'\) 比 \(q\) 更细，记：

\[
q'\succeq q,
\]

若存在：

\[
p:B'\to B
\]

使：

\[
\boxed{
q=p\circ q'.
}
\]

完整数据为：

\[
\boxed{
\operatorname{Refines}(q',q)
=
\sum_{p:B'\to B}
\prod_{x:X}
q(x)=p(q'(x)).
}
\]

\(p\) 是遗忘或粗化 FLOW。

---

## 41.10 Refinement 的预序结构

### 定理 41.2（自反性）

\[
q\succeq q.
\]

### 证明

取：

\[
p=\operatorname{id}_B.
\]

---

### 定理 41.3（传递性）

若：

\[
q''\succeq q',
\qquad
q'\succeq q,
\]

则：

\[
q''\succeq q.
\]

### 证明

若：

\[
q'=r q'',
\qquad
q=p q',
\]

则：

\[
q=(p r)q''.
\]

证毕。

---

### 定理 41.4（核关系包含）

若：

\[
q'\succeq q,
\]

则：

\[
q'(x)=q'(y)
\Longrightarrow
q(x)=q(y).
\]

### 证明

由 \(q=pq'\)：

\[
q(x)
=
p(q'(x))
=
p(q'(y))
=
q(y).
\]

证毕。

---

## 41.11 核包含的反向需要可实现代表

反方向不能在一般构造性类型论中自动成立。

### 定义 41.11（分裂 CUT）

\(q':X\to B'\) 是分裂的，若存在：

\[
s:B'\to X
\]

满足：

\[
q's=\operatorname{id}_{B'}.
\]

### 定理 41.5（核包含加截面推出 factorization）

若：

\[
q'(x)=q'(y)
\Longrightarrow
q(x)=q(y),
\]

且 \(q'\) 有截面 \(s\)，则存在唯一：

\[
p:B'\to B
\]

满足：

\[
q=pq'.
\]

### 证明

定义：

\[
p(b')=q(s(b')).
\]

对任意 \(x:X\)：

\[
q'(s(q'(x)))=q'(x).
\]

由核包含：

\[
q(s(q'(x)))=q(x).
\]

所以：

\[
p(q'(x))=q(x).
\]

唯一性由：

\[
p'(b')
=
p'(q'(s(b')))
=
q(s(b'))
=
p(b')
\]

得到。证毕。

---

该定理准确显示：

\[
\boxed{
\text{核包含}
+
\text{显式代表构造}
=
\text{refinement factorization}.
}
\]

不能把代表选择隐藏在“显然取一个代表”中。

---

# Part IV：FLOW、下降与 carry

## 41.12 严格下降

给定：

\[
q_X:X\to B,
\qquad
q_Y:Y\to C,
\qquad
F:X\to Y.
\]

### 定义 41.12（严格下降）

称 \(F\) 能下降到商坐标，若存在：

\[
\bar F:B\to C
\]

满足：

\[
\boxed{
q_YF=\bar Fq_X.
}
\]

类型化写作：

\[
\boxed{
\operatorname{Descends}(F;q_X,q_Y)
=
\sum_{\bar F:B\to C}
\prod_{x:X}
q_Y(Fx)=\bar F(q_Xx).
}
\]

---

## 41.13 零 carry 与 carry 见证

### 定义 41.13（零 carry）

\[
\boxed{
\operatorname{NoCarry}(F;q_X,q_Y)
}
\]

定义为：

\[
\forall x,y:X,\quad
q_X(x)=q_X(y)
\Longrightarrow
q_Y(Fx)=q_Y(Fy).
\]

### 定义 41.14（carry 见证）

\[
\boxed{
\operatorname{CarryWitness}(F;q_X,q_Y)
}
\]

定义为：

\[
\sum_{x,y:X}
\bigl(q_X(x)=q_X(y)\bigr)
\times
\bigl(q_Y(Fx)\neq q_Y(Fy)\bigr).
\]

含义是：

\[
\boxed{
\text{当前界面商掉的差异，
在 FLOW 后重新成为未来可见差异。}
}
\]

---

## 41.14 下降与 carry 的关系

### 定理 41.6（下降推出零 carry）

若 \(F\) 下降，则：

\[
\operatorname{NoCarry}(F;q_X,q_Y).
\]

### 证明

若：

\[
q_YF=\bar Fq_X
\]

且：

\[
q_X(x)=q_X(y),
\]

则：

\[
q_Y(Fx)
=
\bar F(q_Xx)
=
\bar F(q_Xy)
=
q_Y(Fy).
\]

证毕。

---

### 定理 41.7（分裂 CUT 上零 carry 推出下降）

若 \(q_X\) 有截面 \(s\)，且 \(F\) 零 carry，则 \(F\) 唯一下降。

### 证明

定义：

\[
\bar F(b)=q_Y(F(s(b))).
\]

因：

\[
q_X(s(q_Xx))=q_Xx,
\]

零 carry 给出：

\[
q_Y(Fx)
=
q_Y(F(s(q_Xx)))
=
\bar F(q_Xx).
\]

故下降成立。

若 \(\bar F'\) 也下降，则：

\[
\bar F'(b)
=
\bar F'(q_X(s(b)))
=
q_Y(F(s(b)))
=
\bar F(b).
\]

证毕。

---

所以在有效商、split epi 或显式商模型中：

\[
\boxed{
F\text{ 可下降}
\iff
\text{当前余纤维对未来无 carry}.
}
\]

这给出统一规律定义：

\[
\boxed{
\text{规律}
=
\text{相对于指定 CUT 能够下降的 FLOW}.
}
\]

---

## 41.15 精确下降的复合

设：

\[
X\xrightarrow{F}Y\xrightarrow{G}Z
\]

以及：

\[
q_X:X\to B_X,\quad
q_Y:Y\to B_Y,\quad
q_Z:Z\to B_Z.
\]

若：

\[
q_YF=\bar Fq_X,
\]

\[
q_ZG=\bar Gq_Y,
\]

则：

\[
\boxed{
q_ZGF
=
(\bar G\bar F)q_X.
}
\]

因此：

\[
\boxed{
\text{零 carry FLOW 对组合封闭}.
}
\]

这使宏观规律可以组成新的宏观规律。

---

## 41.16 近似下降与缺陷预算

若 \(C\) 带伪度量 \(d_C\)，给定候选 \(\bar F:B\to C\)，定义点缺陷：

\[
\boxed{
\varepsilon_F(x)
=
d_C
\bigl(
q_Y(Fx),
\bar F(q_Xx)
\bigr).
}
\]

全局缺陷：

\[
\boxed{
\|\varepsilon_F\|_\infty
=
\sup_x\varepsilon_F(x).
}
\]

### 定理 41.8（近似下降链式界）

设：

\[
F:X\to Y,\qquad
G:Y\to Z,
\]

分别由 \(\bar F,\bar G\) 近似下降，误差不超过：

\[
\varepsilon_F,\qquad
\varepsilon_G.
\]

若 \(\bar G\) 为 \(L\)-Lipschitz，则：

\[
\boxed{
\varepsilon_{GF}
\le
\varepsilon_G+L\varepsilon_F.
}
\]

### 证明

插入中间项：

\[
\bar G(q_Y(Fx)).
\]

由三角不等式：

\[
\begin{aligned}
&
d
\bigl(
q_Z(GFx),
\bar G\bar F(q_Xx)
\bigr)
\\
&\le
d
\bigl(
q_Z(GFx),
\bar G(q_YFx)
\bigr)
+
d
\bigl(
\bar G(q_YFx),
\bar G\bar F(q_Xx)
\bigr)
\\
&\le
\varepsilon_G+L\varepsilon_F.
\end{aligned}
\]

证毕。

---

因此有效理论不是任意近似，而是具有可组合缺陷预算的下降。

---

# Part V：ADMIT、合法纤维与锚点

## 41.17 合法 FLOW

设：

\[
A_X:X\to\mathsf{Prop},
\qquad
A_Y:Y\to\mathsf{Prop}.
\]

### 定义 41.15（合法 FLOW）

\(F:X\to Y\) 合法，若：

\[
\boxed{
\forall x:X,\quad
A_X(x)\Longrightarrow A_Y(Fx).
}
\]

合法 FLOW 对复合封闭：

若 \(F\) 与 \(G\) 合法，则 \(GF\) 合法。

---

## 41.18 物理／可实现余纤维

### 定义 41.16（合法纤维）

\[
\boxed{
R_q^A(b)
=
\sum_{x:X}
A(x)
\times
(q(x)=b).
}
\]

形式纤维：

\[
R_q(b)
\]

只表示语法相容。

合法纤维：

\[
R_q^A(b)
\]

还要求通过 ADMIT 门。

所以：

\[
\boxed{
\text{形式可能}
\neq
\text{可实现存在}.
}
\]

---

## 41.19 锚点

### 定义 41.17（带读出锚点）

对 \(b:B\)，定义：

\[
\boxed{
\operatorname{Anchor}(q,A,b)
=
R_q^A(b).
}
\]

若：

\[
a=(x,h_A,h_q),
\]

则 \(a\) 同时包含：

- 整体对象 \(x\)；
- 合法性证明 \(h_A\)；
- 可见坐标证明 \(h_q:q(x)=b\)。

锚点不是随意选择的坐标，而是某个可见商坐标的合法整体提升。

---

## 41.20 锚点运输

若 \(F:X\to Y\) 合法且严格下降：

\[
q_YF=\bar Fq_X,
\]

则定义：

\[
\boxed{
F_\ast:
\operatorname{Anchor}(q_X,A_X,b)
\to
\operatorname{Anchor}
(q_Y,A_Y,\bar F(b)).
}
\]

给定：

\[
(x,h_A,h_q),
\]

输出：

\[
(Fx,\ h_F(h_A),\ h_{\mathrm{desc}}\cdot h_q).
\]

因此合法锚点能够沿精确方格运输。

---

# Part VI：逆塔、观察者与实现

## 41.21 逆系统

设有类型族：

\[
X_n
\qquad
(n:\mathbb N)
\]

及遗忘映射：

\[
p_n:X_{n+1}\to X_n.
\]

### 定义 41.18（形式逆极限）

\[
\boxed{
\varprojlim_nX_n
=
\sum_{x:\prod_nX_n}
\prod_n
\bigl(
p_n(x_{n+1})=x_n
\bigr).
}
\]

该类型可定义，但可能为空。

---

## 41.22 观察者

### 定义 41.19（形式观察者）

形式观察者就是：

\[
\boxed{
\operatorname{Obs}(\mathbf X)
=
\varprojlim_nX_n.
}
\]

### 定义 41.20（合法观察者）

若每层有 ADMIT：

\[
A_n:X_n\to\mathsf{Prop},
\]

则：

\[
\boxed{
\operatorname{PhysObs}(\mathbf X)
=
\sum_{x:\operatorname{Obs}(\mathbf X)}
\prod_n A_n(x_n).
}
\]

若还有能量或复杂度：

\[
E_n:X_n\to\mathbb R_{\ge0},
\]

可进一步要求：

\[
\sup_nE_n(x_n)<\infty.
\]

因此：

\[
\boxed{
\text{观察者}
=
\text{贯穿全部 refinement 层的合法相容锚点历史}.
}
\]

---

## 41.23 真实对象的塔表示

设整体类型 \(X\)，以及相容 CUT：

\[
q_n:X\to B_n
\]

满足：

\[
p_nq_{n+1}=q_n.
\]

### 定义 41.21（实现映射）

\[
\boxed{
\eta:X\to\varprojlim_nB_n
}
\]

由：

\[
\eta(x)_n=q_n(x)
\]

定义。

---

## 41.24 分离与实现完备

### 定义 41.22（分离性）

\[
\boxed{
\operatorname{Separated}(\eta)
\iff
\forall x,y,\quad
\eta(x)=\eta(y)\Longrightarrow x=y.
}
\]

### 定义 41.23（实现完备性）

\[
\boxed{
\operatorname{Complete}(\eta)
\iff
\forall s:\varprojlim_nB_n,\quad
\sum_{x:X}\eta(x)=s.
}
\]

若二者同时成立，则：

\[
\boxed{
X\simeq\varprojlim_nB_n.
}
\]

该等价是实现定理，不是逆极限定义本身。

---

## 41.25 形式、合法与真实完成

必须区分：

\[
\boxed{
\widehat X^{\mathrm{real}}
\subseteq
\widehat X^{\mathrm{adm}}
\subseteq
\widehat X^{\mathrm{form}}.
}
\]

其中：

\[
\widehat X^{\mathrm{form}}
=
\varprojlim B_n.
\]

\[
\widehat X^{\mathrm{adm}}
=
\left\{
s\in\widehat X^{\mathrm{form}}:
\text{满足统一 ADMIT 条件}
\right\}.
\]

\[
\widehat X^{\mathrm{real}}
=
\operatorname{im}(\eta).
\]

所以开放问题经常不是“形式 section 是否存在”，而是：

\[
\boxed{
\text{形式 section 是否合法，
合法 section 是否真实可实现。}
}
\]

---

## 41.26 严格创新与结构无穷

对 refinement 塔：

\[
q_n:X\to B_n,
\qquad
q_n=p_nq_{n+1},
\]

定义第 \(n\) 层严格创新：

\[
\boxed{
\operatorname{Strict}_n
}
\]

当且仅当存在 \(x,y\) 使：

\[
q_n(x)=q_n(y),
\qquad
q_{n+1}(x)\neq q_{n+1}(y).
\]

若对每个 \(n\) 均有严格创新，则没有有限层成为终端忠实界面。

定义结构无穷：

\[
\boxed{
\infty_{\mathrm{ref}}
=
\text{不存在终端忠实有限 CUT}.
}
\]

这不自动推出拓扑连通、紧致或实连续统；这些仍需独立实现结构。

---

# Part VII：因果完成与最小预测状态

## 41.27 未来轨迹 CUT

给定：

\[
F:X\to X,
\qquad
q:X\to B.
\]

### 定义 41.24（未来轨迹）

\[
\boxed{
\operatorname{Tr}_{q,F}:X\to B^{\mathbb N}
}
\]

由：

\[
\operatorname{Tr}_{q,F}(x)(n)
=
q(F^n x)
\]

定义。

定义 shift：

\[
\operatorname{shift}(u)(n)=u(n+1).
\]

---

## 41.28 轨迹闭合定理

### 定理 41.9（未来轨迹严格下降）

\[
\boxed{
\operatorname{Tr}_{q,F}(Fx)
=
\operatorname{shift}
\bigl(
\operatorname{Tr}_{q,F}(x)
\bigr).
}
\]

### 证明

逐坐标：

\[
\begin{aligned}
\operatorname{Tr}_{q,F}(Fx)(n)
&=
q(F^n(Fx))
\\
&=
q(F^{n+1}x)
\\
&=
\operatorname{Tr}_{q,F}(x)(n+1).
\end{aligned}
\]

证毕。

---

### 定理 41.10（恢复当前读出）

设：

\[
\operatorname{head}(u)=u(0).
\]

则：

\[
\boxed{
q
=
\operatorname{head}
\circ
\operatorname{Tr}_{q,F}.
}
\]

---

## 41.29 未来轨迹的普适性质

设另一状态表示：

\[
r:X\to C
\]

及：

\[
G:C\to C,
\qquad
h:C\to B
\]

满足：

\[
rF=Gr,
\]

\[
q=hr.
\]

### 定理 41.11（预测完成普适性）

存在：

\[
\Phi:C\to B^{\mathbb N}
\]

使：

\[
\boxed{
\operatorname{Tr}_{q,F}
=
\Phi r.
}
\]

### 构造

定义：

\[
\Phi(c)(n)=h(G^nc).
\]

由：

\[
rF^n=G^nr
\]

得到：

\[
\begin{aligned}
\Phi(r(x))(n)
&=
h(G^n(r(x)))
\\
&=
h(r(F^nx))
\\
&=
q(F^nx).
\end{aligned}
\]

证毕。

---

该普适性意味着：

\[
\boxed{
\text{未来轨迹 CUT 是所有精确预测状态表示的规范最粗对象}.
}
\]

任何能恢复当前读出并使 FLOW 闭合的状态表示，都必须 refinement 到完整未来轨迹。

---

## 41.30 最小因果等价

### 定义 41.25（未来等价）

\[
\boxed{
x\sim_\infty y
\iff
\forall n,\quad
q(F^nx)=q(F^ny).
}
\]

即：

\[
x\sim_\infty y
\iff
\operatorname{Tr}_{q,F}(x)
=
\operatorname{Tr}_{q,F}(y).
\]

在有效商范畴中，其商：

\[
X/{\sim_\infty}
\]

就是最小因果状态空间。

这同时统一：

- Myhill–Nerode 等价；
- 控制论不可观测商；
- computational mechanics causal states；
- 项目中的 Heisenberg 预测闭包；
- 有限状态未来区分稳定。

---

## 41.31 记忆是最小闭合 refinement

当前 CUT \(q\) 若不能使 \(F\) 下降，则需要 refinement：

\[
q^\sharp:X\to B^\sharp
\]

满足：

\[
q=hq^\sharp
\]

且 \(F\) 在 \(q^\sharp\) 上下降。

最规范选择是：

\[
q^\sharp=\operatorname{Tr}_{q,F}.
\]

因此：

\[
\boxed{
\text{记忆}
=
\text{使当前观察商成为闭合预测状态所需的最小 refinement}.
}
\]

未来轨迹可以分成：

\[
\operatorname{Tr}_{q,F}(x)
=
\bigl(
q(x),M_{q,F}(x)
\bigr),
\]

其中：

\[
M_{q,F}(x)(n)=q(F^{n+1}x).
\]

这里“未来轨迹”是对当前完整状态的分类，并非系统在物理上已经读取未来。

---

## 41.32 有限历史塔

定义：

\[
\boxed{
H_n(x)
=
\bigl(
q(x),q(Fx),\ldots,q(F^nx)
\bigr).
}
\]

定义：

\[
x\sim_n y
\iff
H_n(x)=H_n(y).
\]

显然：

\[
\sim_{n+1}\subseteq\sim_n.
\]

---

## 41.33 一次稳定即永久稳定

### 定理 41.12

若：

\[
\sim_n=\sim_{n+1},
\]

则对所有 \(r\ge0\)：

\[
\boxed{
\sim_n=\sim_{n+r}.
}
\]

### 证明

证明：

\[
\sim_{n+1}=\sim_{n+2}.
\]

取：

\[
x\sim_{n+1}y.
\]

则：

\[
x\sim_ny.
\]

同时：

\[
Fx\sim_nFy,
\]

因为 \(Fx,Fy\) 的前 \(n+1\) 个观测等于 \(x,y\) 的第 \(1\) 至 \(n+1\) 个观测。

由假设：

\[
Fx\sim_{n+1}Fy.
\]

故：

\[
q(F^{n+2}x)=q(F^{n+2}y).
\]

结合已有前缀得到：

\[
x\sim_{n+2}y.
\]

反向包含由 refinement 自动成立。归纳完成。证毕。

---

### 推论 41.2（有限分裂预算）

若 \(X\) 有限，且 \(\sim_0\) 有 \(k_0\) 个等价类，则严格分裂最多发生：

\[
\boxed{
|X|-k_0
}
\]

次。

因为每次严格 refinement 至少增加一个等价类，而类数最多为 \(|X|\)。

---

# Part VIII：概率、信息、熵与因果创新

## 41.34 有限概率模型

设 \(X\) 有限，概率分布：

\[
\mu:X\to[0,1],
\qquad
\sum_x\mu(x)=1.
\]

给定 CUT：

\[
q:X\to B.
\]

推前概率：

\[
\mu_B(b)
=
\sum_{q(x)=b}\mu(x).
\]

若 \(\mu_B(b)>0\)，定义条件分布：

\[
\mu(x\mid b)
=
\frac{\mu(x)}{\mu_B(b)}.
\]

---

## 41.35 商余熵分解

### 定理 41.13

\[
\boxed{
H_\mu(X)
=
H_{\mu_B}(B)
+
\sum_b
\mu_B(b)\,
H_\mu(X\mid q=b).
}
\]

亦即：

\[
\boxed{
H(X)
=
H(q(X))
+
H(X\mid q(X)).
}
\]

### 证明

对 \(b=q(x)\)：

\[
\mu(x)=\mu_B(b)\mu(x\mid b).
\]

因此：

\[
\log\mu(x)
=
\log\mu_B(b)
+
\log\mu(x\mid b).
\]

代入：

\[
-\sum_x\mu(x)\log\mu(x)
\]

并按纤维重排即得。证毕。

---

所以：

\[
\boxed{
H(q(X))
=
\text{商分类信息},
}
\]

\[
\boxed{
H(X\mid q(X))
=
\text{给定商后仍留在余纤维中的信息}.
}
\]

熵必须始终说明相对于哪个 CUT。

---

## 41.36 Refinement 的信息创新

若：

\[
q=pq',
\]

则：

\[
\boxed{
H(q'(X))
=
H(q(X))
+
H(q'(X)\mid q(X)).
}
\]

定义创新：

\[
\boxed{
h(q'\mid q)
=
H(q'(X)\mid q(X))
\ge0.
}
\]

若该值为零，则新层在概率一意义下没有增加分类信息。

---

## 41.37 因果余量

设：

- \(P\) 是完整过去；
- \(Y\) 是指定未来；
- \(C\) 是当前 CUT；
- \(C'\) 是 refinement；
- \(C'\) 是 \(P\) 的函数；
- \(C\) 是 \(C'\) 的函数。

定义：

\[
\boxed{
\kappa(C)
=
I(P;Y\mid C).
}
\]

它测量给定当前界面后，过去仍然保留多少额外未来信息。

---

## 41.38 因果 refinement 望远镜恒等式

### 定理 41.14

\[
\boxed{
I(P;Y\mid C)
=
I(C';Y\mid C)
+
I(P;Y\mid C').
}
\]

### 证明

因 \(C'\) 是 \(P\) 的函数：

\[
I(P;Y\mid C)
=
I(P,C';Y\mid C).
\]

由链式法则：

\[
I(P,C';Y\mid C)
=
I(C';Y\mid C)
+
I(P;Y\mid C,C').
\]

因 \(C\) 是 \(C'\) 的函数：

\[
I(P;Y\mid C,C')
=
I(P;Y\mid C').
\]

证毕。

---

因此：

\[
\boxed{
\kappa(C)-\kappa(C')
=
I(C';Y\mid C)
\ge0.
}
\]

refinement 消耗的不是抽象“未知”，而是可定量的未来相关余量。

---

## 41.39 因果效率

定义总创新：

\[
h=H(C'\mid C),
\]

因果创新：

\[
g=I(C';Y\mid C).
\]

由：

\[
H(C'\mid C)
=
I(C';Y\mid C)
+
H(C'\mid C,Y),
\]

得到：

\[
0\le g\le h.
\]

当 \(h>0\) 时定义：

\[
\boxed{
\eta_{\mathrm{causal}}
=
\frac{g}{h}.
}
\]

解释：

\[
\eta_{\mathrm{causal}}=0
\]

表示 refinement 只增加描述复杂度；

\[
\eta_{\mathrm{causal}}=1
\]

表示全部新增区分都与未来有关。

---

## 41.40 记录塔与记录熵

有限历史满足：

\[
H_{n+1}
=
(H_n,qF^{n+1}).
\]

因此：

\[
\boxed{
H(H_{n+1})
=
H(H_n)
+
H(qF^{n+1}\mid H_n).
}
\]

记录账本熵单调：

\[
H(H_{n+1})\ge H(H_n).
\]

但该量是记录序列携带的信息，不自动等于热力学熵。

时间箭头还需：

- 实际记录稳定写入；
- 记录副本超出当前逆控制域；
- 微观恢复 FLOW 不可由当前观察者实现。

---

# Part IX：代数扩张、carry cocycle 与 gauge

## 41.41 加法扩张

设交换群短正合数据：

\[
0\to R
\xrightarrow{i}
X
\xrightarrow{q}
B
\to0.
\]

选集合截面：

\[
s:B\to X,
\qquad
qs=\operatorname{id}_B.
\]

### 定义 41.26（加法 carry）

\[
\boxed{
\kappa(a,b)
=
s(a)+s(b)-s(a+b).
}
\]

因：

\[
q(\kappa(a,b))=0,
\]

故 \(\kappa(a,b)\) 可视为 \(R\) 中元素。

---

## 41.42 Cocycle 恒等式

### 定理 41.15

\[
\boxed{
\kappa(a,b)+\kappa(a+b,c)
=
\kappa(b,c)+\kappa(a,b+c).
}
\]

### 证明

两边均等于：

\[
s(a)+s(b)+s(c)-s(a+b+c).
\]

证毕。

---

所以：

\[
\boxed{
\text{结合律}
=
\text{不同括号路径累计相同 carry 的路径无关性}.
}
\]

商余坐标中的加法为：

\[
\boxed{
(a,r)\boxplus(b,t)
=
\bigl(
a+b,\,
r+t+\kappa(a,b)
\bigr).
}
\]

---

## 41.43 截面变化与 gauge

若：

\[
s'(a)=s(a)+i(\beta(a)),
\]

则：

\[
\boxed{
\kappa'(a,b)
=
\kappa(a,b)
+
\beta(a)+\beta(b)-\beta(a+b).
}
\]

即：

\[
\kappa'=\kappa+\delta\beta.
\]

因此：

\[
\boxed{
\text{具体 carry 依赖坐标截面；
carry 的上同调类不依赖截面}.
}
\]

---

## 41.44 分裂判据

### 定理 41.16

存在群同态截面：

\[
s':B\to X
\]

当且仅当存在 \(\beta:B\to R\) 使：

\[
\kappa+\delta\beta=0.
\]

所以：

\[
\boxed{
[\kappa]=0
\iff
\text{扩张可全局平凡分裂}.
}
\]

非零接缝类表示任何坐标系中都无法同时消去商余耦合。

---

## 41.45 位值算术

取：

\[
X=\mathbb Z,\qquad
B=\mathbb Z/b\mathbb Z,\qquad
R=b\mathbb Z.
\]

标准截面：

\[
s([r])=r,
\qquad
0\le r<b.
\]

则：

\[
\boxed{
\kappa([r_1],[r_2])
=
b
\left\lfloor
\frac{r_1+r_2}{b}
\right\rfloor.
}
\]

这就是进位。

所以：

\[
\boxed{
\text{进位}
=
\text{有限数字截面不能保持整数加法的精确缺陷}.
}
\]

减法借位、取负时的余数补和乘法交叉项均是同一接缝的派生表现。

---

## 41.46 乘法的商余耦合

设：

\[
n_i=bq_i+r_i.
\]

则：

\[
n_1n_2
=
b^2q_1q_2
+
bq_1r_2
+
bq_2r_1
+
r_1r_2.
\]

令：

\[
c_\times
=
\left\lfloor
\frac{r_1r_2}{b}
\right\rfloor,
\qquad
r_\times
=
r_1r_2\bmod b.
\]

得到：

\[
\boxed{
q_\times
=
bq_1q_2
+
q_1r_2
+
q_2r_1
+
c_\times,
}
\]

\[
\boxed{
r_\times
=
r_1r_2\bmod b.
}
\]

所以乘法包含：

- 商—商作用；
- 商—余作用；
- 余—商作用；
- 余—余作用；
- 余层乘积向商层的 carry。

---

## 41.47 导数是一阶余量上的乘法提升

考虑双数：

\[
A[\varepsilon]/(\varepsilon^2).
\]

给定线性 \(D:A\to A\)，定义：

\[
\Phi_D(a)=a+\varepsilon D(a).
\]

### 定理 41.17

\(\Phi_D\) 保持乘法，当且仅当：

\[
\boxed{
D(ab)=aD(b)+D(a)b.
}
\]

### 证明

\[
\begin{aligned}
\Phi_D(a)\Phi_D(b)
&=
(a+\varepsilon D(a))
(b+\varepsilon D(b))
\\
&=
ab+\varepsilon(aD(b)+D(a)b),
\end{aligned}
\]

因为 \(\varepsilon^2=0\)。

与：

\[
\Phi_D(ab)=ab+\varepsilon D(ab)
\]

比较即得。证毕。

---

因此：

\[
\boxed{
\text{Leibniz 规则}
=
\text{乘法 FLOW 在第一阶余纤维上的合法提升条件}.
}
\]

---

# Part X：线性动力学、因果 carry 与记忆核

## 41.48 块分解

设：

\[
X=V\oplus H.
\]

\(V\) 是可见商坐标，\(H\) 是隐藏余量。

令：

\[
P:X\to V,
\qquad
Q=I-P.
\]

任意线性 FLOW：

\[
F:X\to X
\]

写成：

\[
\boxed{
F
=
\begin{pmatrix}
A&B\\
C&D
\end{pmatrix}.
}
\]

于是：

\[
\begin{aligned}
v_{t+1}&=Av_t+Bh_t,\\
h_{t+1}&=Cv_t+Dh_t.
\end{aligned}
\]

---

## 41.49 可见动力闭合判据

### 定理 41.18

存在：

\[
\bar F:V\to V
\]

满足：

\[
PF=\bar FP
\]

当且仅当：

\[
\boxed{
PFQ=0.
}
\]

### 证明

若下降成立，则：

\[
PFQ=\bar FPQ=0.
\]

反之，若 \(PFQ=0\)，则：

\[
PF
=
PF(P+Q)
=
PFP.
\]

定义：

\[
\bar F=PFP|_V.
\]

便有：

\[
PF=\bar FP.
\]

证毕。

---

所以：

\[
\boxed{
B=PFQ
}
\]

是隐藏余量进入未来可见坐标的 causal carry。

---

## 41.50 双向不变与交换子

\[
[P,F]
=
PF-FP
=
\begin{pmatrix}
0&B\\
-C&0
\end{pmatrix}.
\]

因此：

\[
[P,F]=0
\]

当且仅当：

\[
PFQ=0,
\qquad
QFP=0.
\]

也就是可见与隐藏两个扇区都在 FLOW 下不相互泄漏。

所以：

\[
\boxed{
\|[P,F]\|
}
\]

可以作为 CUT 与 FLOW 的不自然性强度。

---

## 41.51 隐藏消元与离散记忆核

由：

\[
h_{t+1}=Cv_t+Dh_t
\]

递推：

\[
\boxed{
h_t
=
D^th_0
+
\sum_{j=0}^{t-1}
D^{t-1-j}Cv_j.
}
\]

代回：

\[
\boxed{
v_{t+1}
=
Av_t
+
BD^th_0
+
\sum_{j=0}^{t-1}
BD^{t-1-j}Cv_j.
}
\]

定义记忆核：

\[
\boxed{
K_{t-1-j}
=
BD^{t-1-j}C.
}
\]

所以：

\[
\boxed{
\text{记忆}
=
\text{过去进入隐藏余纤维的 carry，
经隐藏 FLOW 传播后重新进入可见商坐标}.
}
\]

若 \(D^N=0\)，记忆有限。

若：

\[
\|D^n\|\to0,
\]

记忆衰减。

若 \(D\) 有单位模谱或连续谱，则可产生长期记忆和复现。

---

## 41.52 连续时间版本

设：

\[
\frac{d}{dt}
\begin{pmatrix}
v\\h
\end{pmatrix}
=
\begin{pmatrix}
A&B\\
C&D
\end{pmatrix}
\begin{pmatrix}
v\\h
\end{pmatrix}.
\]

Duhamel 公式给出：

\[
\boxed{
h(t)
=
e^{tD}h(0)
+
\int_0^t
e^{(t-s)D}Cv(s)\,ds.
}
\]

代入可见方程：

\[
\boxed{
\dot v(t)
=
Av(t)
+
Be^{tD}h(0)
+
\int_0^t
Be^{(t-s)D}Cv(s)\,ds.
}
\]

因此连续记忆核为：

\[
\boxed{
K(t-s)=Be^{(t-s)D}C.
}
\]

Mori–Zwanzig 型结构在这里表现为一般 CUT–FLOW 块消元的具体实例。

---

# Part XI：局部几何、拓扑余量与形式邻域

## 41.53 纤维丛的局部商余

设：

\[
\pi:E\to B.
\]

局部平凡化：

\[
\varphi_i:
\pi^{-1}(U_i)
\simeq
U_i\times F.
\]

在交叠处：

\[
\varphi_i\varphi_j^{-1}
(b,f)
=
(b,g_{ij}(b)f).
\]

过渡函数满足：

\[
\boxed{
g_{ij}g_{jk}=g_{ik}.
}
\]

这就是局部商余坐标的 cocycle 一致性。

---

## 41.54 Gauge 变化

更换局部截面：

\[
h_i:U_i\to G
\]

使：

\[
\boxed{
g'_{ij}
=
h_i g_{ij}h_j^{-1}.
}
\]

因此具体过渡函数依赖坐标选择，但其同调类和丛的同构类型不依赖坐标。

所以：

\[
\boxed{
\text{几何}
=
\text{局部可平凡商余结构}
+
\text{全局不可消去的接缝类}.
}
\]

---

## 41.55 Connection 与 curvature

connection 指定相邻纤维间的 anchor 运输。

若局部 connection form 为 \(A\)，曲率为：

\[
\boxed{
F_A=dA+A\wedge A.
}
\]

它测量无穷小闭环运输的非平凡 carry。

平坦：

\[
F_A=0
\]

只保证局部路径无穷小缺陷为零；全局仍可能存在 holonomy。

---

## 41.56 Homology

链复形：

\[
\cdots
\to C_{n+1}
\xrightarrow{\partial_{n+1}}
C_n
\xrightarrow{\partial_n}
C_{n-1}
\to\cdots
\]

满足：

\[
\partial_n\partial_{n+1}=0.
\]

定义：

\[
Z_n=\ker\partial_n,
\qquad
B_n=\operatorname{im}\partial_{n+1}.
\]

则：

\[
\boxed{
H_n=Z_n/B_n.
}
\]

解释：

- \(Z_n\)：已经闭合的 cycle；
- \(B_n\)：可由更高维对象填充的部分；
- \(H_n\)：商掉全部可填充部分后仍存活的闭合余量。

所以：

\[
\boxed{
\text{拓扑洞}
=
\text{经过全部局部填充 FLOW 后仍不可消除的余量}.
}
\]

---

## 41.57 Jet 与形式完成

设 \(\mathcal O_x\) 是点 \(x\) 附近的局部函数环，\(\mathfrak m_x\) 是在 \(x\) 消失的函数理想。

第 \(n\) 阶 jet：

\[
\boxed{
J_x^n
=
\mathcal O_x/\mathfrak m_x^{n+1}.
}
\]

形式邻域：

\[
\boxed{
\widehat{\mathcal O}_x
=
\varprojlim_n
\mathcal O_x/\mathfrak m_x^{n+1}.
}
\]

所以：

\[
\boxed{
\text{一个点的形式连续统}
=
\text{全部有限阶邻域的相容逆完成}.
}
\]

但形式幂级数是否收敛、是否来自真实解析函数，仍需独立 realization theorem。

---

# Part XII：有限维量子实例

## 41.58 矩阵有序 ADMIT

设有限维 Hilbert 空间 \(\mathscr H\)。

对象空间：

\[
X=\operatorname{Herm}(\mathscr H).
\]

状态 ADMIT：

\[
\boxed{
\rho\ge0,
\qquad
\operatorname{Tr}\rho=1.
}
\]

量子过程合法性不只要求标量正性，而要求 completely positive：

\[
\operatorname{id}_n\otimes\Phi
\]

对所有 \(n\) 保持矩阵正锥。

因此量子 ADMIT 是矩阵锥塔：

\[
\boxed{
\{M_n(\mathcal A)_+\}_{n\ge1}.
}
\]

---

## 41.59 Operator-system CUT

设：

\[
\mathcal S\subseteq\operatorname{Herm}(\mathscr H)
\]

为含单位元的实自伴线性空间。

定义：

\[
\boxed{
q_{\mathcal S}(\rho)(E)
=
\operatorname{Tr}(\rho E)
\qquad
(E\in\mathcal S).
}
\]

两个状态相对于观察者等价，当且仅当：

\[
\operatorname{Tr}((\rho-\sigma)E)=0
\quad
\forall E\in\mathcal S.
\]

---

## 41.60 量子物理纤维

\[
\boxed{
\operatorname{PhysFiber}_{\mathcal S}(\rho)
=
\left\{
\sigma\ge0:
\operatorname{Tr}\sigma=1,\
q_{\mathcal S}(\sigma)=q_{\mathcal S}(\rho)
\right\}.
}
\]

Hilbert–Schmidt 正交余空间描述线性不可见方向；PSD 锥与迹一截面决定其中哪些方向仍可实现。

---

## 41.61 Heisenberg 预测闭包

令 \(\Phi\) 为 CPTP 通道，\(\Phi^\ast\) 为 unital CP Heisenberg 对偶。

定义：

\[
\boxed{
\mathcal S_n
=
\operatorname{OSys}
\left\{
(\Phi^\ast)^kE:
E\in\mathcal S_0,\
0\le k\le n
\right\}.
}
\]

极限：

\[
\boxed{
\mathcal S_\infty
=
\operatorname{OSys}
\left\{
(\Phi^\ast)^kE:
E\in\mathcal S_0,\
k\ge0
\right\}.
}
\]

---

## 41.62 未来统计等价

### 定理 41.19

对状态 \(\rho,\sigma\)，以下等价：

\[
q_{\mathcal S_0}(\Phi^k\rho)
=
q_{\mathcal S_0}(\Phi^k\sigma)
\quad
\forall k\ge0,
\]

与：

\[
\boxed{
\operatorname{Tr}
\bigl(
(\rho-\sigma)A
\bigr)
=
0
\quad
\forall A\in\mathcal S_\infty.
}
\]

### 证明

由：

\[
\operatorname{Tr}
\bigl(
\Phi^k(\rho-\sigma)E
\bigr)
=
\operatorname{Tr}
\bigl(
(\rho-\sigma)(\Phi^\ast)^kE
\bigr).
\]

对全部生成元成立，当且仅当对其 operator-system 闭包成立。证毕。

---

## 41.63 一次稳定永久稳定

### 定理 41.20

若：

\[
\mathcal S_n=\mathcal S_{n+1},
\]

则：

\[
\boxed{
\mathcal S_{n+r}=\mathcal S_n
\quad
\forall r\ge0.
}
\]

### 证明

\(\mathcal S_n=\mathcal S_{n+1}\) 意味：

\[
\Phi^\ast(\mathcal S_n)\subseteq\mathcal S_n.
\]

以后全部迭代都留在 \(\mathcal S_n\) 中。证毕。

---

## 41.64 Pinching 是记录 CUT 的商投影

给定正交投影族：

\[
\sum_iP_i=I.
\]

定义：

\[
\boxed{
\mathbb E(\rho)
=
\sum_iP_i\rho P_i.
}
\]

则：

\[
\rho
=
\mathbb E(\rho)
+
\bigl(\rho-\mathbb E(\rho)\bigr).
\]

第一项是当前记录 CUT 可见的块对角部分；

第二项是跨分支相干余量。

### 定理 41.21（幂等性）

\[
\boxed{
\mathbb E^2=\mathbb E.
}
\]

### 证明

\[
\begin{aligned}
\mathbb E^2(\rho)
&=
\sum_{i,j}
P_iP_j\rho P_jP_i
\\
&=
\sum_iP_i\rho P_i.
\end{aligned}
\]

证毕。

---

## 41.65 Instrument、结果与条件状态

一个 instrument 是 CP、迹不增映射族：

\[
\{\mathcal I_r\}_r
\]

且：

\[
\sum_r\mathcal I_r
\]

保迹。

概率：

\[
p_r=\operatorname{Tr}\mathcal I_r(\rho).
\]

条件状态：

\[
\boxed{
\rho_r
=
\frac{\mathcal I_r(\rho)}{p_r}
}
\]

当 \(p_r>0\)。

effect：

\[
E_r=\mathcal I_r^\ast(I).
\]

同一个 effect 可由不同 instrument 实现，所以：

\[
\boxed{
\text{相同读出概率}
\not\Rightarrow
\text{相同状态 FLOW}.
}
\]

---

## 41.66 环境记录与经典中心

若地址 \(i\) 写入记录向量 \(|e_i\rangle\)，约化通道为：

\[
\Phi_G(\rho)_{ij}
=
G_{ij}\rho_{ij},
\qquad
G_{ij}=\langle e_j,e_i\rangle.
\]

定义：

\[
i\sim_Gj
\iff
|e_i\rangle=|e_j\rangle.
\]

若等价类为 \(I_\alpha\)，固定代数具有结构：

\[
\boxed{
\operatorname{Fix}(\Phi_G)
\cong
\bigoplus_\alpha
M_{|I_\alpha|}(\mathbb C).
}
\]

其中心：

\[
\boxed{
Z(\operatorname{Fix}(\Phi_G))
\cong
\bigoplus_\alpha
\mathbb C I_\alpha.
}
\]

因此经典事实不是整个量子代数，而是稳定记录所生成的可复制中心。

---

## 41.67 GNS 正完成

设 \(\mathcal A\) 为 \(*\)-代数，\(\omega:\mathcal A\to\mathbb C\) 为正泛函：

\[
\omega(a^\ast a)\ge0.
\]

定义零空间：

\[
N_\omega
=
\{a:\omega(a^\ast a)=0\}.
\]

Cauchy–Schwarz 给出：

\[
\omega(a^\ast a)=0
\Longrightarrow
\omega(b^\ast a)=0
\quad
\forall b.
\]

所以可商掉 \(N_\omega\)，并定义：

\[
\langle[a],[b]\rangle
=
\omega(b^\ast a).
\]

完成后得到 Hilbert 空间。

因此：

\[
\boxed{
\text{GNS}
=
\text{把“所有自配对非负”实现为范数平方的完成器}.
}
\]

---

# Part XIII：对角化扩张

## 41.68 自地址读取

设：

\[
g:A\to(A\to Y)
\]

是清单，\(\tau:Y\to Y\) 是扭曲。

定义：

\[
\boxed{
d_g(a)
=
\tau(g(a)(a)).
}
\]

---

## 41.69 对角逃逸

### 定理 41.22

若：

\[
\forall y:Y,\quad
\tau(y)\neq y,
\]

则：

\[
\boxed{
d_g\notin\operatorname{range}(g).
}
\]

### 证明

假设：

\[
g(a_0)=d_g.
\]

在 \(a_0\) 处：

\[
d_g(a_0)
=
g(a_0)(a_0).
\]

但定义给出：

\[
d_g(a_0)
=
\tau(g(a_0)(a_0))
=
\tau(d_g(a_0)),
\]

与无固定点矛盾。证毕。

---

因此：

\[
\boxed{
\text{对角化}
=
\text{表示 CUT 对自身完备声明的逃逸审计}.
}
\]

它需要：

- 自编码；
- 自地址读取；
- 扭曲；
- 全局拼接。

普通局部取反本身不产生对角逃逸。

---

## 41.70 扭曲依赖类型

在 sharp projection 中：

\[
P^\perp=I-P
\]

没有固定点：

\[
P=I-P
\]

无解。

但在全部 effects 中：

\[
E=\frac I2
\]

是补运算固定点。

所以：

\[
\boxed{
\text{对角逃逸取决于扭曲所在类型的固定点结构}.
}
\]

不能把“取反”作为无类型原语使用。

---

# Part XIV：zeta 锚点、离线 carry 与条件刚性

## 41.71 锚定解析连续统

令完成函数 \(\xi\) 为整函数，\(\rho\in\mathbb C\)。

有限 jet：

\[
J_\rho^N\xi
=
\left(
\xi(\rho),
\xi'(\rho),
\ldots,
\xi^{(N)}(\rho)
\right).
\]

无限 jet：

\[
\boxed{
J_\rho^\infty\xi
=
\varprojlim_NJ_\rho^N\xi.
}
\]

若该形式 jet 是真实 \(\xi\) 的 jet，则 Taylor realization：

\[
\boxed{
\operatorname{Rec}_\rho
(J_\rho^\infty\xi)
=
\xi.
}
\]

所以：

\[
\boxed{
\text{裸零点坐标}
\neq
\text{完整锚定连续统};
}
\]

\[
\boxed{
\text{完整零点观察者}
=
\rho
+
J_\rho^\infty\xi
+
\text{全局实现条件}.
}
\]

---

## 41.72 有限素数商与解析余尾

对有限素数集 \(S\)，定义：

\[
Q_S(s)
=
\prod_{p\in S}(1-p^{-s})^{-1},
\]

\[
\widetilde R_S(s)
=
\zeta(s)
\prod_{p\in S}(1-p^{-s}).
\]

在绝对收敛区：

\[
\zeta(s)=Q_S(s)\widetilde R_S(s).
\]

若 \(\rho\) 是非平凡零点，则：

\[
1-p^{-\rho}\neq0
\]

对每个素数成立，所以：

\[
\boxed{
\widetilde R_S(\rho)=0
\quad
\forall S\Subset\mathbb P.
}
\]

因此零点是任意有限素数商抽取后仍存活的解析余尾 section。

但普通逆系统相容性本身不会排除离线零点；还需要 ADMIT 和正性门。

---

## 41.73 离线二地址动力

设：

\[
\rho
=
\frac12+\delta+i\gamma.
\]

镜像模式：

\[
e^{(\delta+i\gamma)t},
\qquad
e^{(-\delta+i\gamma)t}.
\]

在对称／反对称基中，生成元：

\[
\boxed{
G_\rho
=
i\gamma I
+
\delta
\begin{pmatrix}
0&1\\
1&0
\end{pmatrix}.
}
\]

取临界商投影：

\[
P_{\mathrm{crit}}
=
\begin{pmatrix}
1&0\\
0&0
\end{pmatrix}.
\]

则：

\[
[P_{\mathrm{crit}},G_\rho]
=
\delta
\begin{pmatrix}
0&1\\
-1&0
\end{pmatrix}.
\]

所以：

\[
\boxed{
\|[P_{\mathrm{crit}},G_\rho]\|
=
|\delta|
=
\left|
\Re\rho-\frac12
\right|.
}
\]

在该模型中：

\[
\boxed{
\text{离线距离}
=
\text{临界 CUT 与尺度 FLOW 的径向 causal carry}.
}
\]

这是一条模型内恒等式，不是 prime-side 来源定理。

---

## 41.74 正因果镜像刚性

设有序向量空间：

\[
(V,C,u),
\]

其中 \(C\) 为生成正锥，\(u\) 为严格正归一化泛函。

base norm：

\[
\|x\|_B
=
\inf_{x=a-b,\ a,b\in C}
\bigl(u(a)+u(b)\bigr).
\]

设 \(T_t\) 正且保归一：

\[
T_tC\subseteq C,
\qquad
uT_t=u.
\]

### 定理 41.23（base norm 收缩）

\[
\boxed{
\|T_tx\|_B\le\|x\|_B.
}
\]

### 证明

若：

\[
x=a-b,\qquad a,b\in C,
\]

则：

\[
T_tx=T_ta-T_tb,
\]

且 \(T_ta,T_tb\in C\)。于是：

\[
\|T_tx\|_B
\le
u(T_ta)+u(T_tb)
=
u(a)+u(b).
\]

对全部分解取下确界。证毕。

---

### 条件定理 41.24（镜像刚性）

若某模式属于同一正完成，且：

\[
T_tv_\rho
=
e^{(\delta+i\gamma)t}v_\rho,
\]

则收缩性给出：

\[
\delta\le0.
\]

若镜像模式也属于同一正完成，且：

\[
T_tv_\rho^\sharp
=
e^{(-\delta+i\gamma)t}v_\rho^\sharp,
\]

则：

\[
-\delta\le0.
\]

所以：

\[
\boxed{
\delta=0.
}
\]

即：

\[
\boxed{
\Re\rho=\frac12.
}
\]

---

## 41.75 RH 表示桥账本

上述条件定理要应用于真实 zeta，至少需要证明：

1. **prime-side 生成桥**
   从 prime-power 数据规范构造 \(T_t\)，而不是从零点反向编码。

2. **谱实现桥**
   每个零点忠实对应 \(T_t\) 的 normal mode、共振或明确广义谱对象。

3. **正归一桥**
   \(T_t\) 在某个非循环构造的正锥上正且保归一。

4. **镜像内部性桥**
   \(\rho\) 与 \(1-\overline\rho\) 属于同一个正完成，而不是状态与分布对偶两侧。

5. **显式公式忠实桥**
   prime-side determinant、trace 或二次型保留零点位置、重数和镜像，无额外核。

6. **极限可容许桥**
   有限素数层的正性、normality、谱与收缩在无限完成中不退化。

因此，本节只得到：

\[
\boxed{
\text{忠实同空间正谱实现}
\Longrightarrow
\mathrm{RH}.
}
\]

它没有无条件构造该实现。

---

# Part XV：Lean 形式化骨架

## 41.76 最小定义层

```lean
universe u v w

structure Cut (X : Type u) where
  Base : Type v
  proj : X → Base

def Fiber {X : Type u} (q : Cut X) (b : q.Base) : Type u :=
  { x : X // q.proj x = b }

def Flow (X : Type u) (Y : Type v) :=
  X → Y

def Admit (X : Type u) :=
  X → Prop

def Real {X : Type u} (A : Admit X) :=
  { x : X // A x }

def Refines {X : Type u} (fine coarse : Cut X) : Type _ :=
  Σ forget : fine.Base → coarse.Base,
    ∀ x, coarse.proj x = forget (fine.proj x)

def Descends
    {X : Type u} {Y : Type v}
    (qX : Cut X) (qY : Cut Y)
    (F : X → Y) : Type _ :=
  Σ Fbar : qX.Base → qY.Base,
    ∀ x, qY.proj (F x) = Fbar (qX.proj x)

def NoCarry
    {X : Type u} {Y : Type v}
    (qX : Cut X) (qY : Cut Y)
    (F : X → Y) : Prop :=
  ∀ x y,
    qX.proj x = qX.proj y →
    qY.proj (F x) = qY.proj (F y)

def CarryWitness
    {X : Type u} {Y : Type v}
    (qX : Cut X) (qY : Cut Y)
    (F : X → Y) : Type _ :=
  Σ x y : X,
    qX.proj x = qX.proj y ∧
    qY.proj (F x) ≠ qY.proj (F y)

def FutureTrace
    {X : Type u}
    (q : Cut X)
    (F : X → X) :
    X → ℕ → q.Base :=
  fun x n => q.proj ((F^[n]) x)
```

---

## 41.77 首批承重定理依赖顺序

建议形式化顺序：

```text
fiber_sigma_equiv
refines_refl
refines_trans
refines_kernel_inclusion
split_kernel_inclusion_factor
descends_noCarry
split_noCarry_descends
descends_comp
approx_descends_comp
futureTrace_step
futureTrace_head
futureTrace_universal
history_relation_mono
history_stable_forever
finite_history_split_bound
carry_cocycle
section_change_coboundary
linear_visible_descent_iff
hidden_elimination_memory_kernel
pinching_idempotent
operator_system_stable_forever
diagonal_escape
baseNorm_contract
mirror_rigidity_conditional
```

---

## 41.78 模块分层

```text
CIRPT/Core/Role.lean
CIRPT/Core/Cut.lean
CIRPT/Core/Fiber.lean
CIRPT/Core/Refinement.lean
CIRPT/Core/Descent.lean
CIRPT/Core/Admit.lean
CIRPT/Core/Anchor.lean
CIRPT/Core/InverseTower.lean
CIRPT/Causal/FutureTrace.lean
CIRPT/Causal/FiniteHistory.lean
CIRPT/Causal/MemoryKernel.lean
CIRPT/Information/FiniteEntropy.lean
CIRPT/Information/CausalInnovation.lean
CIRPT/Algebra/CarryCocycle.lean
CIRPT/Linear/BlockDescent.lean
CIRPT/Geometry/TransitionCocycle.lean
CIRPT/Quantum/OperatorCut.lean
CIRPT/Quantum/Pinching.lean
CIRPT/Quantum/GNS.lean
CIRPT/Diagonal/Escape.lean
CIRPT/Zeta/ConditionalMirrorRigidity.lean
```

其中 `Zeta` 模块只能依赖已经证明的条件接口，不得引入隐藏 RH 公理。

---

## 41.79 无暗账审计

每个新增声明应回答：

1. 使用了哪些基础类型规则？
2. 是否使用 `Classical.choice`？
3. 是否假设了全局截面？
4. 是否证明非空？
5. 是否把目标结论写进 ADMIT？
6. 形式完成与真实实现是否分离？
7. 数值缺陷是否有明确定义域？
8. 模型间翻译是否保持零缺陷？
9. 高层 zeta 结论的表示桥是否显式列出？
10. `#print axioms` 是否只包含冻结信任集？

---

# Part XVI：统一概念字典

## 41.80 概念编译表

\[
\boxed{
\begin{aligned}
\text{存在}
&=
\text{ADMIT 子类型中的 anchor},\\
\text{对象}
&=
\text{在指定 FLOW 与 refinement 下稳定的商余历史},\\
\text{相等}
&=
\text{本体等同或指定 CUT 下的界面等同},\\
\text{差异}
&=
\text{非零余纤维坐标},\\
\text{运算}
&=
\text{FLOW},\\
\text{规律}
&=
\text{能够下降的 FLOW},\\
\text{因果}
&=
\text{余量穿过 FLOW 改变未来商坐标},\\
\text{记忆}
&=
\text{修复非闭合商动力的最小 refinement},\\
\text{信息}
&=
\text{CUT 消除的余纤维不确定性},\\
\text{熵}
&=
\text{给定商以后仍留在合法纤维中的区分量},\\
\text{时间}
&=
\text{FLOW 的组合参数},\\
\text{时间箭头}
&=
\text{记录 refinement 超出当前逆控制域},\\
\text{连续统}
&=
\text{无限 CUT 塔的合法实现},\\
\text{几何}
&=
\text{局部商余平凡化及其不可消除接缝},\\
\text{曲率}
&=
\text{闭环运输的局部 carry},\\
\text{经典性}
&=
\text{稳定、交换、可复制的记录中心},\\
\text{量子性}
&=
\text{多个矩阵有序 CUT 无法共同 sharp 平坦化},\\
\text{观察者}
&=
\text{refinement 塔上的合法相容 anchor},\\
\text{对角化}
&=
\text{表示系统对自身闭合声明的逃逸审计}.
\end{aligned}
}
\]

---

# Part XVII：最终总结构

## 41.81 依赖商余塔

最一般形式：

\[
\boxed{
X_{n+1}
\simeq
\sum_{x_n:X_n}
R_n(x_n).
}
\]

在局部可平凡模型中可写成：

\[
\boxed{
X_{n+1}
\cong
X_n\ltimes_{\kappa_n}R_n.
}
\]

其中：

\[
\begin{aligned}
X_n
&=\text{当前可区分商世界},\\
R_n
&=\text{当前尚未表达的余量},\\
\kappa_n
&=\text{商与余不能平凡分离的接缝},\\
F_n
&=\text{运输该层结构的 FLOW},\\
A_n
&=\text{形式对象进入真实世界的 ADMIT}.
\end{aligned}
\]

---

## 41.82 统一主问题

所有领域问题都可以被整理为：

\[
\boxed{
\text{某个余量能否穿过全部 FLOW、refinement 与 ADMIT，
最终成为真实完成中的非零 section？}
}
\]

存在问题：

\[
\operatorname{PhysSect}\neq\varnothing.
\]

唯一性问题：

\[
|\operatorname{PhysSect}|=1.
\]

刚性问题：

\[
\operatorname{PhysDefectSect}=\{0\}.
\]

正则性问题：

\[
\sup_nE_n(x_n)<\infty.
\]

对角问题：

\[
\text{系统能否表示包含自身分类器在内的全部对象？}
\]

---

## 41.83 最终结论

本节得到的不是“所有领域只剩四个单词”，而是一套可以被模型、定理和反例共同审计的过程数学：

\[
\boxed{
\text{一个概念的结构，
不只由它当前显示什么决定，
还由它商掉了什么、
余量能否影响未来、
局部接缝能否被消去、
全部有限层能否实现为同一个整体、
以及该整体能否承受对自身表示能力的审计决定。}
}
\]

其最短形式为：

\[
\boxed{
\text{CUT}
+
\text{FLOW}
+
\text{ADMIT}
+
\text{ANCHOR}
}
\]

及其派生：

\[
\boxed{
\begin{aligned}
\mathsf{REMAINDER}
&=\operatorname{Fiber}(\mathsf{CUT}),\\
\mathsf{CARRY}
&=\operatorname{Defect}(\mathsf{CUT},\mathsf{FLOW}),\\
\mathsf{MEMORY}
&=\operatorname{CausalComplete}(\mathsf{CARRY}),\\
\mathsf{RECORD}
&=\operatorname{StableReadout}(\mathsf{FLOW}),\\
\mathsf{CONTINUUM}
&=\operatorname{Realize}
\bigl(
\operatorname{InverseComplete}(\mathsf{CUT}^{\infty})
\bigr),\\
\mathsf{OBSERVER}
&=\operatorname{CompatibleAnchor}(\mathsf{CUT}^{\infty}),\\
\mathsf{DIAGONAL}
&=\operatorname{SelfAudit}(\mathsf{CUT},\mathsf{FLOW}).
\end{aligned}
}
\]

最终一句：

\[
\boxed{
\text{定义告诉我们什么结构算作一个可能世界；
只有构造、准入证明和实现定理，
才能告诉我们这样的世界是否真实存在。}
}
\]

---

# 42. 追加：观察者—余量对偶的视界读法
## Horizon Readings of the Remainder–Observer Duality
### Anchored Origin, Infinite Ledger Distance, Alphabet Capacity, and the Typing of Other Minds

## 42.0 文档地位、案由与真值边界

**案由。** 本节把一条观察者直觉类型化：

> "黑洞的结构似乎中心就是一个观察者；我作为观察者的直觉是，我位于信息球的中心。"

本节不裁决这条直觉对物理黑洞是否为真。它只做一件事：把直觉拆成若干个在本文既有定义下**可判**的陈述，逐条给出其真值、前提与出处；凡本文定理不支持、只是解释性的提法，明标**"解释性提法（非主张）"**；剩下的本体断言按量子卷 `OBSERVER-QUANTUM.md` §12.2 的先例处理——**挂墙：不批准不嘲笑，不入定理栏**。

**版本。** v1.1（2026-08-26）。v1.0 经一席异模型盲评判 reject（13 条：3 blocking / 9 material / 1 minor），本版逐条采纳；处置明细见对应 PR 正文。

**文档地位。** 纸面；追加式；不改动第 0–41 节任何一行。新增命题在 proof term、依赖闭包与冻结收据齐备前不得标记为 `Closed`。

### 42.0.1 本节统一采用的距离模型

为避免把 §32.8 的**状态**距离 \(d_O(\rho,\sigma)\) 与 §33.2 的**点**距离混用，本节自始至终只用下列点模型：

- 载体 \(X\)（集合，可带动力学 \(T:X\to X\)），锚点 \(o\in X\)（§35.4）；
- 可访问读出族 \(\mathcal A_O\subseteq\mathbb R^X\)，其元皆有界；
- 变化半范数 \(L_O:\mathcal A_O\to[0,\infty]\)；
- 观察者距离
\[
\boxed{
d_O(x,y)
=
\sup\{\,|f(x)-f(y)|:\ f\in\mathcal A_O,\ L_O(f)\le1\,\}
\ \in[0,+\infty].
}
\]

与 §32.8 的关系：取 \(\rho=\delta_x,\sigma=\delta_y\)（求值态）即得该处公式的特例；§32.8 的定理 32.16（refinement 单调）与推论 32.17（零距离纤维）在此模型下逐字成立。**置换模型**指下列特例：\(X=I\)，更新为置换 \(\tau\)，\(\mathcal A_O\) = 边可容许函数（`edgeAdmissible`：有界且 \(|f(\tau i)-f(i)|\le1\)），\(L_O(f)=\sup_i|f(\tau i)-f(i)|\)；此时 \(d_O\) 即仓库 `observerDistance`。**凡本节使用"记账步数""路径"语言，只限置换模型。**

**依赖。** §32.8（定理 32.16、推论 32.17）；§33.2–33.3（定理 33.3）；§35.4（命题 35.5）；§36.4（定义 36.10–36.11）；§36.8（原理 36.17）；§36.20（定理 36.27，仅作动机）；§32.10、§33.10；§24.5；量子卷 §12.1、§12.2、§15.1；`INTERFACE_PHILOSOPHY.md` 附录 E 的物理对表口径。

**仓库锚点（Lean，本节证明中实际使用）。**

- `D5/S3/ContinuousObservables/ObserverDistanceClassification.lean`：`edgeAdmissible`、`observerDistance`、`permutation_observer_distance_classification`——本节只用其**第一子句**（叶不变量分离 ⟹ `observerDistance = ⊤`）；第二、三子句关于独立变量 `a b : ZMod M`、`m n : ℤ`，**不是**关于同一 `x y : I` 的陈述，本节不把它们当作一般同轨道对的结论使用；
- `D5/S3/Observer/MetricGeometry/WindowObserverDistance.lean`：`window_observer_distance_eq_cycle_distance`（循环窗精确值，仅作实例）；
- `D5/S3/Observer/MetricGeometry/OrbitConnesDistance.lean`：`orbitConnesDistance m n = |n−m|`（整数轨道精确值，仅作实例）。

**非主张（先列后论）。** 本节不主张物理黑洞的任何性质；不推导 Bekenstein 界、面积律或 Hawking 温度；不主张时空是某界面的解压；不主张他心问题被解决；不主张 \(d_O=\infty\) 的类恰由核分离刻画（只证充分）；不主张对 Riemann 假设有任何推进。

---

## 42.1 锚定原点：观察者距离以自身为零点

### 定义 42.1（锚定径向函数）

\[
\boxed{
r_O^{\,o}(x)=d_O(o,x).
}
\]

它是到锚点的距离函数，**不是**度量本身；\(d_O\) 一般只是扩展伪度量。

### 命题 42.2（按定义为原点；稳定子不变性）

（i）\(r_O^{\,o}(o)=0\)。

（ii）设群 \(G\) 作用于 \(X\)，且作用与读出族对偶相容：对 \(g\in G\)、\(f\in\mathcal A_O\)，\(g\cdot f:=f\circ g^{-1}\in\mathcal A_O\) 且 \(L_O(g\cdot f)=L_O(f)\)。则 \(d_O(gx,gy)=d_O(x,y)\)，从而对稳定子 \(G_o=\{g:go=o\}\) 的任意 \(g\)：
\[
r_O^{\,o}(gx)=r_O^{\,o}(x).
\]

#### 证明

（i）\(|f(o)-f(o)|=0\)。（ii）\(|f(gx)-f(gy)|=|(g^{-1}\!\cdot f)(x)-(g^{-1}\!\cdot f)(y)|\)，而 \(f\mapsto g^{-1}\!\cdot f\) 是单位球 \(\{L_O\le1\}\) 到自身的双射，故两端 supremum 相等；再取 \(y=o\)、\(g\in G_o\)。\(\square\)

**读法。** "我位于中心"在本节定义下只证到**"按定义为原点"**：每个点到自身距离为零，锚点之所以特殊，只因它被选为 \(r^{\,o}\) 的基点（§35.4 的对称性约化）。这是一条关于**坐标选择**的陈述，对载体无所断言，也不蕴含任何"中心"的度量性质（如最小离心率）。

---

## 42.2 视界：无穷观察者距离

### 定义 42.3（观察者视界与可见球）

\[
\boxed{
\mathcal H_O(o)=\{x:\ d_O(o,x)=+\infty\},
\qquad
\mathcal B_O(o)=\{x:\ d_O(o,x)<+\infty\}.
}
\]

注意 \(d_O(o,x)=0\) 的点属于 \(\mathcal B_O(o)\)：零距离是"不可分辨"，不是"视界之外"。

### 命题 42.4（核分离是视界的充分探测器）

若存在有界 \(f\in\mathcal A_O\)、\(L_O(f)=0\)（即 \(f\in\ker L_O\)），且 \(f(o)\neq f(x)\)，则 \(x\in\mathcal H_O(o)\)。

#### 证明

对任意 \(c>0\)，\(L_O(cf)=0\le1\)，故 \(d_O(o,x)\ge c|f(o)-f(x)|\to\infty\)。这就是定理 33.3。置换模型下其机器证明为 `permutation_observer_distance_classification` 第一子句。\(\square\)

**边界。** 本命题只给**充分**条件。在一般（无限维、半范数）读出族上，\(d_O=\infty\) 不必由某个单独的核元分离产生；"视界恰由 \(\ker L_O\) 决定"**未证**，本节不作此断言。

### 推论 42.5（视界不由载体拓扑给出）

\(\mathcal H_O(o)\) 由 \((\mathcal A_O,L_O)\) 决定，与载体上任何预先给定的拓扑或度量无关；同一载体上两个观察者的视界一般不同。置换模型下，有限距离 = 沿 \(\tau\) 的记账步数上界（命题 42.10 证明中的望远镜和），无穷距离对应量子卷 Connes 度量的"流线型 / 中心型无穷远"；**此路径语言不外推到一般模型**。

### 命题 42.6（视界随 refinement 不减）

设 \(\mathcal A_m\subseteq\mathcal A_{m+1}\) 定义于同一载体，\(L_{m+1}|_{\mathcal A_m}=L_m\)。则
\[
\boxed{
\mathcal H_m(o)\subseteq\mathcal H_{m+1}(o).
}
\]

#### 证明

定理 32.16 在点模型下给出 \(d_m\le d_{m+1}\)（第 \(m\) 层可行集包含于第 \(m+1\) 层）；在 \([0,\infty]\) 中 \(d_m(o,x)=\infty\) 推出 \(d_{m+1}(o,x)=\infty\)。\(\square\)

**读法。** 精化观察者不会把视界内的点拉回可见球；它只会暴露更多"不可达"。这是本节第一条可证伪的结构预测（§42.10）。

---

## 42.3 字母表容量：一次读出的记录上界

### 命题 42.7（字母表容量界）

设 \(\operatorname{Im}q_O\) 有限，\(P\) 为 \(X\) 上任一概率分布，\(H\) 为离散 Shannon 熵。则
\[
\boxed{
H\bigl(q_O(P)\bigr)\le\log\bigl|\operatorname{Im}q_O\bigr|,
}
\]
右侧与读出纤维 \(q_O^{-1}(y)\) 的大小无关。

#### 证明

离散熵不超过支撑集对数。\(\square\)

**边界。** 这是一条通用的字母表容量界。它**不含**任何面积、维数或体积标度，因此**不是**面积律；它与 Bekenstein–Hawking 面积熵之间只有"容量由界面而非内部决定"这一个保留项，`INTERFACE_PHILOSOPHY.md` 附录 E 已将该保留项标为**结构同构，非学说互证**，本节不加码。像无限时本命题不适用。

---

## 42.4 对偶的两个读数

设 \(O\) 与 \(O'\) 是同一载体 \(X\) 上的两个观察者（各有 \((\mathcal A,L)\) 与读出 \(q\)）。称状态对 \((x,y)\) 为 \(O'\) 的**内部差异**，若 \(q_{O'}(x)\neq q_{O'}(y)\)。

### 命题 42.8（同一对状态的三值双读数）

对任意 \((x,y)\)，\(d_O(x,y)\in[0,+\infty]\) 恰落入下列三格之一，各格有类型化含义：
\[
\boxed{
\begin{aligned}
d_O=0
&:\ \text{不可分辨（若 }\{L_O\le1\}\text{ 线性张成 }\mathcal A_O\text{，则由推论 32.17 等价于 }x,y\text{ 同一读出纤维）};\\
0<d_O<\infty
&:\ \text{有限可达};\\
d_O=+\infty
&:\ \text{视界（核分离为其充分探测器，命题 42.4）}.
\end{aligned}
}
\]
对 \(d_{O'}\) 同理；故每对 \((x,y)\) 携带一个二元组 \((d_O,d_{O'})\)。

#### 证明

\([0,+\infty]\) 的三分是穷尽且互斥的；各格标签由所引结果给出。\(\square\)

### 定义 42.9（外隐、有限可达；外侧与内侧读数）

对 \(O'\) 的内部差异 \((x,y)\)：

- 若 \(d_O(x,y)\in\{0,+\infty\}\)，称该差异对 \(O\) **外隐**（externally hidden：或被商掉，或不可达；**不**称"视界之外"，因零距离点属于 \(\mathcal B_O\)）；
- 若 \(0<d_O(x,y)<\infty\)，称它对 \(O\) **有限可达**。

**外侧读数**指 \(O\) 对 \(O'\) 内部差异的 \(d_O\) 取值；**内侧读数**指 \(O'\) 自身的 \(d_{O'}\) 取值（以 \(O'\) 的锚点为原点，命题 42.2）。**"\(O'\) 的全部内部差异对 \(O\) 外隐"是关于观察者对 \((O,O')\) 的一个假设，不是定理**；命题 42.8 明确允许有限可达格非空。

### 命题 42.10（置换模型下的非对称格）

取 \(X=I\)，\(O,O'\) 皆为置换模型，更新分别为 \(\tau,\tau'\)。设 \(\ell:I\to\Lambda\) 为 \(\tau\)-不变标记（\(\ell\circ\tau=\ell\)），且存在 \(x,y\in I\) 满足
\[
\ell(x)\neq\ell(y)
\qquad\text{且}\qquad
x=\tau'^{\,n}y\ \ (\text{某 }n\in\mathbb Z).
\]
则
\[
\boxed{
d_O(x,y)=+\infty,
\qquad
d_{O'}(x,y)\le|n|<+\infty.
}
\]

#### 证明

前者：\(f=\mathbf 1_{\{\ell=\ell(x)\}}\) 有界、\(\tau\)-不变（故 \(L_O(f)=0\)）、分离 \(x,y\)，由命题 42.4；这正是 `permutation_observer_distance_classification` 第一子句。后者：对任一 \(\tau'\)-边可容许 \(f\)，沿轨道望远镜
\[
|f(x)-f(y)|
\le
\sum_{k=0}^{|n|-1}\bigl|f(\tau'^{\,k+1}y)-f(\tau'^{\,k}y)\bigr|
\le|n|,
\]
对 \(f\) 取 supremum。\(\square\)

**辨析。** （a）前提是 \(x,y\) 在**不同 \(O\)-叶、同一 \(O'\)-轨道**；"两个观察者的叶划分不同"**不够**（反例：\(O\) 单一传递叶、\(O'\) 单点叶，划分不同但 \(O\) 无核分离对，该格为空）。（b）"同一 \(O'\)-叶"也不够：叶可粗于轨道，同叶异轨道之间未必有有限记账路径。（c）本命题只给上界 \(|n|\)；`window_observer_distance_eq_cycle_distance` 与 `orbitConnesDistance` 是循环窗、整数轨道两种轨道结构上的**精确值**实例，本节不把它们当作一般同轨道对的陈述。

### 42.4.1 解释性提法（非主张）

定理 36.27 把一个 Hilbert 余量 \(r\) 与"对原空间失明、对目标最敏感"的泛函 \(\ell_r\) 规范识别。**受此启发**，本节提出下述读法：

> 每个观察者被另一个观察者看，外观是一个界面像加一片外隐区；每个观察者看自己，内观是一个以自身为原点的可见球。原直觉"黑洞中心是一个观察者"据此改写为："一个观察者，被别的观察者看时，长成一片外隐区。"

**这不是定理 36.27 的推论**：36.27 中没有第二个观察者、锚点、扩展距离，也未证 \(\ell_r\in\ker L_O\)。本节能证明的只有命题 42.8 的三值分类与命题 42.10 的置换模型实例；上述读法是对它们的解释性组织，记为**非主张**。要把它升为定理，须构造 \(O,O'\) 及各自的 \((\mathcal A,L)\)，并证明所需的零/无穷距离——这是 §42.9 的一项 `open`。

---

## 42.5 方向差：一条类比，不是定理

量子卷 §15.1 证明：固定有限系统的全部读账史总税不超过自由预算 \(F(\rho_0)\)；产出无界则**对象或环境**必须无穷。

**类比（非主张）。** 若把"可见球"类比为有限预算一侧、"余量"类比为无穷所在一侧，则该图像与"视界内藏无穷"的黑洞图像**方向相反**。本节**不**把它写成命题：§15.1 既未提及 \(\mathcal B_O\) 或 \(R_\infty\)，也未给出正的逐条记录成本（总税有界不蕴含记录条数有界），且明确允许无穷落在环境侧。方向差只作记录，不裁。

---

## 42.6 三条不批准

1. **观察者不是一个点。** 定义 36.10：观察者是逆完成塔上的带锚相容锥 \((\mathbf X,\mathbf o,\mathcal P,\mathcal M,\Delta)\)，每一层有一个"这里"且层层相容；定义 36.11：无全局相容点时只有局部 section 与转移 cocycle。"中心"是跨尺度的一致性要求，不是载体中的某个位置。
2. **"我在中心"是自描述通道的输出，而自描述闭包不自动成立。** 该陈述是 \(\Delta_O\) 对自身的一次应用。§32.10 证明存在层析完备而自描述不完备的观察者；§33.10 证明操作完备**不蕴含**经典答案完备，并说明逃逸"仍可能"。故本条只断言：自描述闭包**不由**经验/操作完备自动得出；不断言它"必然失败"。命题 42.2 为真但不承重。
3. **没有唯一的"信息球"。** 每个观察者的球是自己的商；跨观察者距离可为 \(+\infty\)（命题 42.10）；§24.5 多观察者距离按最大值融合而非按并集消解；量子卷 §12.1 的 Hasse 反例说明拼尽全部局部视角整体仍可失明，且盲量自成对象（Brauer 群）。"从中心看全"没有定理支持。

---

## 42.7 他心问题的类型化（不是解决）

哲学上的他心问题（problem of other minds）问：一个观察者如何知道另一个观察者"有内心"。本节不给答案；它把问题拆成一个可判部分和一个挂墙部分。

### 定义 42.11（自描述读出）

设 \(O'\) 指定其可访问读出族中的一个子族 \(\mathcal S_{O'}\subseteq\mathcal A_{O'}\) 为**关于 \(O'\) 自身**的读出（本节不需要其内部结构）。称 \((x,y)\) 为 \(O'\) 的**自描述差异**，若存在 \(s\in\mathcal S_{O'}\) 使 \(s(x)\neq s(y)\)。自描述差异是 \(O'\) 的内部差异的子集（取 \(q_{O'}\) 包含 \(\mathcal S_{O'}\) 的联合读出）。

### 命题 42.12（他心的三值分类；"他心即外隐"是条件句）

对 \(O'\) 的每个自描述差异 \((x,y)\)，\(d_O(x,y)\) 恰落入命题 42.8 三格之一：
\[
\boxed{
d_O=0\ (\text{不可分辨})
\quad\big|\quad
0<d_O<\infty\ (\text{有限可达})
\quad\big|\quad
d_O=+\infty\ (\text{视界}).
}
\]
**条件句**：若 \(O'\) 的全部自描述差异对 \(O\) 外隐（定义 42.9），则 \(O\) 不能由任何有限记账（置换模型意义）区分 \(O'\) 的任一自描述差异。有限可达格非空时，该部分对 \(O\) 可分辨，代价为相应的距离。

#### 证明

三格划分是命题 42.8 的直接特例。条件句：\(d_O=0\) 时任何 \(L_O\le1\) 的读出都不区分二者；\(d_O=\infty\) 时不存在有限上界，置换模型下即无有限步路径（命题 42.10 证明中的望远镜和反向给出：有限步路径 ⟹ 有限距离）。\(\square\)

**本命题不断言**自描述差异对 \(O\) 必然外隐：那是关于具体观察者对的假设，须逐对核验；本文没有定理迫使自描述差异不可有限可达。反例（评审席给出）：同一循环观察者同时作 \(O\) 与 \(O'\)，相邻点距离为 \(1\)，而定义 32.1 不禁止此类点进入 \(\mathcal S_{O'}\)。

### 评注 42.13（可知的部分及其边界；非定理）

\(O\) 无条件可见的是 \(O'\) 上的界面像 \(q_O|_{X'}\)（\(X'\subseteq X\) 为 \(O'\) 的状态支撑）与 \(O'\) 对 \(O\) 的探针族的响应（原理 36.17）。要由响应**重构**代表 \(O'\) 的对象（至同构），须令探针子范畴的限制 nerve **稠密 / 完全忠实**，并保留响应对探针态射的自然性数据；**联合忠实只检测态射相等，不足以重构对象**。且稠密性**不得假定**：量子卷 §12.1 的 Hasse 反例给出局部视角穷尽而整体失明的定理级先例。本评注不含证明，不作定理引用。

**判词。** 他心问题在本节被改判为两句：

\[
\boxed{
\text{（可判）他者每个自描述差异落在哪一格——不可分辨 / 有限可达 / 视界——由 }d_O\text{ 判；}
}
\]
\[
\boxed{
\text{（挂墙）外隐区内是否"有"体验——本体断言，依 §12.2 先例不批准不嘲笑，不入定理栏。}
}
\]

**对称说明。** 三格划分对 \((O,O')\) 与 \((O',O)\) 同时成立，但**哪一格非空可以不对称**。自描述闭包不自动成立（§42.6 第 2 条）意味着"自心"也不是免费的；本节不把这句话写成定理。

**诚实边界。** 以上不是"解决"：它把问题从"知识论遗憾"改写为"距离三格的归类问题"，并给出可知部分的条件（稠密 nerve）。任何声称本节"证明了他者有（或没有）内心"的读法都是对挂墙条目的误读。

---

## 42.8 与物理黑洞的对表（类比；逐行写明保留结构）

附录 E 的口径许可**审慎比较**，不许可新的同构断言。下表每行只标"类比"，并写明该类比**保留**的唯一结构；未写明的一律不保留。

| 物理侧 | 本节对象 | 保留的结构 | 地位 |
|---|---|---|---|
| 事件视界（因果边界）〔典：Hawking–Ellis 1973〕 | \(\mathcal H_O(o)\)（定义 42.3） | 仅"外部不可达"一项；**不**保留因果 / 光锥结构 | 类比 |
| 面积熵〔典：Bekenstein 1973；Hawking 1975〕 | 字母表容量界（命题 42.7） | 仅"容量由界面而非内部决定"；**无**面积标度 | 类比（附录 E 已登记） |
| 无毛定理〔典：Israel 1967；Carter 1971；Hawking 1972；前提：稳态、真空或 Einstein–Maxwell〕 | 外侧只见界面像；内部差异外隐（定义 42.9，含 \(0\) 与 \(\infty\) 两格） | 仅"外部可见参数远少于内部自由度" | 类比 |
| 全息原理〔典：'t Hooft 1993；Susskind 1995〕 | 反应本体（原理 36.17） | 仅"对象由其对外响应给出"；**无**边界 / 维数约化 | 类比（弱） |
| 奇点 / 中心 | 无对应——观察者不是点（§42.6 第 1 条） | — | 不对表 |
| 谱距离〔典：Connes 1994〕 | 观察者距离（§42.0.1；Lean `OrbitConnesDistance`） | 定义形式 | 文献锚 |
| 关系性量子力学〔典：Rovelli 1996〕 | 状态相对观察者 | 仅"相对性" | 相近，未检索 |

**文献地位。** 表中成分各有出处（离线记忆，未核对）；其**组合方式**本节**未做文献检索**，状态记 `open`（检索待做），**不**标 `suspected-novel`——该状态按本仓惯例保留给已完成并留痕的检索。

---

## 42.9 可形式化拆分

1. **视界集合（置换模型）。** 定义 `horizonSet tau o = {x | observerDistance tau o x = ⊤}`；叶分离 ⟹ 成员资格由 `permutation_observer_distance_classification` 第一子句包装即得。
2. **命题 42.6。** 有限读出族上 supremum 的单调性，初等。
3. **命题 42.10 的望远镜上界。** 新引理：`edgeAdmissible tau' f → |f (tau'^n y) − f y| ≤ |n|`，进而 `observerDistance tau' (tau'^n y) y ≤ n`。这是**新证明**，不是对既有子句的搬运。
4. **命题 42.12。** 第 1 项与第 3 项的直接合取。
5. **42.4.1 的桥定理（`open`）。** 构造 \(O,O'\) 使解释性提法成为命题。

以上任一项在 proof term、依赖闭包与冻结收据出现前不得标记为 `Closed`。

---

## 42.10 可证伪的结构预测与严格非主张

**可证伪预测（在本节模型内）。**

1. 视界随 refinement 不减（命题 42.6）：若存在满足其前件的 refinement 使某 \(x\) 从 \(\mathcal H_m(o)\) 退回 \(\mathcal B_{m+1}(o)\)，本节被推翻。
2. 置换模型下，若存在 \(x,y\) 落在不同 \(O\)-叶、同一 \(O'\)-轨道，则 \((d_O,d_{O'})(x,y)=(\infty,\text{有限})\)（命题 42.10）；找到满足前件却使 \(d_{O'}=\infty\) 或 \(d_O<\infty\) 的实例即推翻。（**注意**：仅"叶划分不同"不构成前件。）
3. 命题 42.12 的三格划分对任意有序对成立；反例形是找到一个自描述差异，其 \(d_O\notin[0,+\infty]\)——按定义不可能，故该项实际是类型检查，不承担经验内容。

**严格非主张。**

1. 不主张物理黑洞具有本节任何性质；
2. 不推导 Bekenstein 界、面积律、Hawking 温度或信息悖论的任何结论；
3. 不主张时空是某界面的解压；
4. 不主张他心问题被解决，也不主张他者有或没有体验；
5. 不主张"我位于中心"对载体有任何断言（命题 42.2 只关于坐标选择）；
6. 不主张 \(d_O=\infty\) 的类恰由核分离刻画（只证充分）；
7. 不主张 §42.4.1 的读法为定理，不主张 §42.5 的方向差为命题；
8. 不主张对 Riemann 假设有任何推进。

---

## 42.11 形式化状态

本节各条的地位分三档，不得混报：

- **既有结果的直接改写**：命题 42.4（= 定理 33.3）、命题 42.6（由定理 32.16）、命题 42.7（离散熵上界）、命题 42.8（三分穷尽）；
- **新的小引理（纸面证明）**：命题 42.2（对偶相容作用下的不变性）、命题 42.10（望远镜上界）、命题 42.12（条件句）；
- **解释性提法 / 类比 / 评注（非主张）**：§42.4.1 的对偶读法、§42.5 的方向差、评注 42.13、表 42.8 全部行。

无新公理，无新领域存在假设。所有命题在获得 proof term 与冻结收据前不得投影为 `Closed`。

**本节最终一句。**

\[
\boxed{
\text{"中心"只是被选定的原点；"视界"是无穷观察者距离的类；二者的对偶读法是提法，不是定理。}
}
\]
\[
\boxed{
\text{他心问题由此成为距离三格的归类问题——其本体部分挂墙。}
}
\]

---

# 43. 追加：分辨率的提升律——读数精化、动作扩展与预算
## Resolution Ascent: Readout Refinement, Action Extension, and Budget
### What an Observer Can and Cannot Do to See Finer

## 43.0 文档地位、案由与真值边界

**案由。** §42 把"视界"定义为无穷观察者距离的类，并证明它随读数精化不减（命题 42.6）。本节回答由此引出的操作问题：**一个观察者要提高自己的分辨率，能做什么、不能做什么、代价多少、何时该停。** 本节把散在第 19、27、32、33、38 节、闭合谱卷与完成反射卷中的既有结果按这个问题重新组织，只新增一条定理（定理 43.2，置换模型下视界的轨道刻画）与若干决策规则；决策规则明标"规则（非定理）"。

**版本。** v1.1（2026-08-27）。v1.0 经一席异模型盲评判 reject（4 blocking / 6 material），本版逐条采纳；处置明细见对应 PR 正文。

**文档地位。** 纸面；追加式；不改动第 0–42 节任何一行；沿用 §42.0.1 的点距离模型与置换模型。新增命题在 proof term、依赖闭包与冻结收据齐备前不得标记为 `Closed`。

**依赖。** §19.2（定理 19.2）；§27.2；§32.10、§33.10；§33.6；§33.13（定理 33.26）；§37.11；§38.15、§38.17、§38.35、§38.36；§42.2（定义 42.3、命题 42.4、42.6）、§42.4（命题 42.10）；`OBSERVER_CLOSURE_SPECTRUM.md` §2–§5；`FORMAL_OBSERVER_COMPLETION_REFLECTION.md` §15–§16（折扣 Gramian、定义 16.1）；量子卷 `OBSERVER-QUANTUM.md` §12.1、§14.1（定理 1、定理 2、定理 4）、§15.1。

**仓库锚点（Lean）。** 同 §42.0：`ObserverDistanceClassification.lean`（`edgeAdmissible`、`observerDistance`、`permutation_observer_distance_classification` 第一子句）。

**两个必须分开的谓词（贯穿本节）。** 在置换模型中，对锚点 \(o\) 与点 \(x\)：

- **动作可达**：\(x\in\operatorname{Orb}_\tau(o)\)（存在有限步 \(\tau^{\pm1}\) 路径）；
- **读数可分辨**：\(d_\tau(o,x)>0\)（存在可容许读出区分二者）。

二者独立：\(d=0\) 的点动作可达而不可分辨；不同轨道的点不可达却可分辨（正是被一个不变量分开）。本节任何"看得见 / 够得着"的口语都须落到这两个谓词之一。

**非主张。** 本节不主张任何一般（非置换）模型下视界由动作决定；不主张"读数精化不改变视界"（它可以扩大视界，命题 42.6）；不主张"无 carry 处新增坐标必然无用"；不主张升层是提升自身分辨率的唯一途径；不主张任何心理学或教育学结论；不主张对 Riemann 假设有任何推进。

---

## 43.1 分辨率只相对目标有定义

### 命题 43.1（三种 Hilbert 逼近意义下的分辨率；定理 33.26 的相关部分）

设可见空间递增 \(V_0\subseteq V_1\subseteq\cdots\)，\(R_n=V_n^\perp\)。本节关心的三种"分辨率提升"是：

1. **目标分辨**：对固定目标 \(x\)，\(\|P_{R_n}x\|\to0\)；
2. **状态族分辨**：对任务相关集合 \(\mathcal S\)，\(\sup_{x\in\mathcal S}\|P_{R_n}x\|\to0\)；
3. **统一分辨**：\(\|I-P_{V_n}\|_{\mathrm{op}}\to0\)。

一般有 \(3\Rightarrow2\)，且当 \(x\in\mathcal S\) 时 \(2\Rightarrow1\)；**若每个 \(V_n\) 为真闭子空间**，则 \(\|I-P_{V_n}\|_{\mathrm{op}}=1\)，第 3 种失败。定理 33.26 还含第四种（代数完成），与前三者无无条件蕴含，本节不用。

#### 证明

即定理 33.26 所列前三项及其前提。\(\square\)

**读法。** 在"可见空间永远是真子空间"的前提下，"把分辨率提到底"不可实现；合法的问题是"对**这个**目标（或这一族状态），余量是否趋零"。不声明目标的分辨率提升没有定义。

---

## 43.2 读数精化不越轨道上界；动作变更移动上界

### 定理 43.2（置换模型下全读出族的视界 = 轨道补集）

取置换模型：\(X=I\)，更新 \(\tau\in\operatorname{Sym}(I)\)，读出族为**全部** \(\tau\)-边可容许函数，距离 \(d_\tau\) 即 `observerDistance`。记 \(\operatorname{Orb}_\tau(x)=\{\tau^{\,n}x:n\in\mathbb Z\}\)。则对一切 \(x,y\in I\)（\(I\) 可无限）：

\[
\boxed{
d_\tau(x,y)=+\infty
\iff
\operatorname{Orb}_\tau(x)\neq\operatorname{Orb}_\tau(y),
}
\]

且当 \(y=\tau^{\,n}x\)（\(n\in\mathbb Z\)）时 \(d_\tau(x,y)\le|n|\)。特别地
\[
\boxed{
\mathcal H_\tau(o)=I\setminus\operatorname{Orb}_\tau(o),
\qquad
\mathcal B_\tau(o)=\operatorname{Orb}_\tau(o).
}
\]

#### 证明

（⇐）令 \(f=\mathbf 1_{\operatorname{Orb}_\tau(x)}\)。它取值于 \(\{0,1\}\) 故有界；\(\tau\)-不变，故 \(|f(\tau i)-f(i)|=0\le1\)，边可容许且 \(L_\tau(f)=0\)；\(f(x)=1\neq0=f(y)\)。由命题 42.4（= `permutation_observer_distance_classification` 第一子句）得 \(d_\tau(x,y)=\top\)。以上不依赖 \(I\) 有限。

（⇒，逆否）设 \(y=\tau^{\,n}x\)。**若 \(n\ge0\)**：对任一边可容许 \(f\)，
\[
|f(y)-f(x)|
\le\sum_{k=0}^{n-1}\bigl|f(\tau^{\,k+1}x)-f(\tau^{\,k}x)\bigr|
\le n .
\]
**若 \(n<0\)**：令 \(m=-n>0\)，则 \(x=\tau^{\,m}y\)，对调端点后用 \(n\ge0\) 的情形得 \(|f(x)-f(y)|\le m=|n|\)。对 \(f\) 取 supremum 即 \(d_\tau(x,y)\le|n|<\infty\)。\(\square\)

**勘注（对已合入的 §42.10 证明）。** §42.10 证明中的和式按 \(k=0,\dots,|n|-1\) 沿 \(\tau'^{\,k}y\) 正向求和，对 \(n<0\) 未连接所述端点；正确处理如上（\(n<0\) 时对调端点）。§42.10 的结论不变。按追加式纪律，此处记勘注，不回改 §42。

### 推论 43.3（读数精化的上界与动作变更的效果）

在置换模型中，对固定 \(\tau\)：

（a）**读数精化不越轨道上界，也不缩小既有视界。** 对任意读出子族 \(\mathcal A\subseteq\{\tau\text{-边可容许}\}\)（同一 \(L_\tau\)），\(\mathcal H_{\mathcal A}(o)\subseteq I\setminus\operatorname{Orb}_\tau(o)\)；随 \(\mathcal A\) 增大，\(\mathcal H_{\mathcal A}(o)\) 单调不减（命题 42.6），并在全族处达到上界 \(I\setminus\operatorname{Orb}_\tau(o)\)。**读数精化可以扩大视界**（例：常值子族 \(\mathcal H=\varnothing\)；加入一个轨道指示函数后其余轨道全部变为无穷远），但**永远不能把不同轨道的点拉回有限距离**。

（b）**动作变更移动上界。** 将更新换为 \(\tau'\)，全族视界变为 \(I\setminus\operatorname{Orb}_{\tau'}(o)\)；若 \(\operatorname{Orb}_{\tau'}(o)\supsetneq\operatorname{Orb}_\tau(o)\)，则 \(\operatorname{Orb}_{\tau'}(o)\setminus\operatorname{Orb}_\tau(o)\) 中的点由不可达变为动作可达（在 \(\tau'\) 的全族下距离有限）。

#### 证明

（a）子族的可行集包含于全族的可行集，故 \(d_{\mathcal A}\le d_\tau\)，视界包含于全族视界；单调性即命题 42.6；上界由定理 43.2；两个例子直接验算。（b）定理 43.2 对 \(\tau'\) 重述。\(\square\)

**读法。** "看得更细"与"能做更多"是两种类型不同的提升：读数精化在轨道上界**之内**改变视界（可以扩大，不能越界，不能缩小既有部分）；只有动作变更能移动上界本身。**本推论把 §42.10 末尾聊天中标记的 open（"上界如何随动作变"）在置换模型内闭合；一般模型仍 `open`**（命题 42.4 只给充分条件）。

---

## 43.3 预算：只有一部分区分值钱

### 命题 43.4（预算与效率，汇编）

对 refinement 塔 \(C_0\prec C_1\prec\cdots\)（\(C_n=q_n(P)\)，\(F\) 为未来）：

1. \(h_n=H(C_{n+1}\mid C_n)\)，\(g_n=I(C_{n+1};F\mid C_n)\)，\(0\le g_n\le h_n\)；效率 \(\eta_n=g_n/h_n\)（\(h_n>0\)），**\(h_n=0\) 时定义 \(\eta_n=0\)**（§38.15）；
2. \(\sum_n h_n\le H(P)\)，故 \(h_n\ge\varepsilon\) 的层数至多 \(H(P)/\varepsilon\)（§38.17）；
3. 从当前观察商到完整预测商所需的记忆预算等于二者的对数分辨率差（闭合谱卷 §4）。

#### 证明

三条分别为所引节的结论。\(\square\)

### 规则 43.5（投资顺序；非定理）

新增坐标的价值凭证是**测得的** \(g>0\)。一对状态的 carry（\(q(x)=q(y)\) 而 \(q(Fx)\neq q(Fy)\)）是 \(g>0\) 的**启发式见证**：它在分布对该对赋正概率且贡献不被其他对抵消时才蕴含 \(g>0\)，本节不把它写成蕴含。规则：**先为有 \(g>0\) 凭证（或至少有 carry 见证）的缺陷加坐标（§38.36 循环），无凭证处不先投预算。** 未观察到 carry 不证明 \(g=0\)。这是在有限预算（命题 43.4 之 2）下的决策规则，不是定理。

---

## 43.4 免税轴与互补预算

### 命题 43.6（汇编，按量子卷原意）

在量子卷的读账框架下：

1. **捏合恒等式**（§14.1 定理 1）：\(S(\mathcal P\rho)=S(\rho)+D(\rho\|\mathcal P\rho)\)；税为零 ⟺ **态与分类框架对易**；
2. **免税走廊**（§14.1 定理 4 及其判据）：冻结框架下的酉演化，与**更新**对易的轴逐步税为零；
3. **互补预算**（§14.1 定理 2）：\(D_Z+D_X\ge\ln n-S\)，两个共轭轴的税**不能同时为零**（在其前提下）。

#### 证明

见所引定理。\(\square\)

**读法与规则 43.7（非定理）。** 第 3 条不证明"提升一个方向必然降低另一个方向"，只证明两条税不能同时归零。据此立规则：**先沿免税轴（第 2 条）投资，再决定为哪一条失配轴付税。** "分辨率是向量"是这条规则的口语形，不是定理。

---

## 43.5 停止判据

### 命题 43.8（汇编）

1. 有限系统的未来核塔 \(K_n\)（固定 \(q,F\)）在有限深度稳定，严格精化次数至多 \(|X|-|\operatorname{Im}q|\)（闭合谱卷 §3）；
2. 一次稳定即永久稳定：\(K_{n+1}=K_n\Rightarrow K_{n+s}=K_n\)（定理 19.2）。

#### 证明

见所引结果。\(\square\)

### 规则 43.9（停止；非定理）

对**固定的** \(q\) 与 \(F\)，核塔一步不动即停止**前瞻精化**——继续加深前瞻不再产生新区分。本规则**不**断言此后任何新加坐标（例如换一个 \(q\) 或扩展 \(F\)）都有 \(g=0\)。

---

## 43.6 投向何处：条件数、原料与联合观察

### 命题 43.10（汇编，按原文范围）

1. **条件数与脆弱方向**：折扣 Gramian \(W_\beta\) 的 \(\kappa_\beta=\lambda_{\max}/\lambda^+_{\min}\)（反射卷定义 16.1）是各向异性的标量度量；**脆弱方向**是 \(W_\beta\) 小正特征值的特征子空间，\(\kappa_\beta\) 本身不指出方向；
2. **原料同存（条件形）**：§33.6 证明在其模数条件下恢复须控制全部相关记录，并记有失败情形；§37.11 说明当前状态未必决定历史；
3. **联合观察**：两个观察者联合读出的核为各自核之交（§27.2 商菱形）；
4. **联合的上限**：拼尽全部局部视角，整体仍可失明，盲量自成对象（量子卷 §12.1 Hasse 反例）。

#### 证明

见所引结果。\(\square\)

### 规则 43.11（投资方向；非定理，含启发式）

预算投向 \(W_\beta\) 小正特征值的特征子空间；写入时同存原料（§33.6 所需的记录）；**联合另一观察者通常是廉价的分辨率提升**——"廉价"是启发式（§27.2 不含成本模型），且联合不保证闭合（命题 43.10 之 4）。

---

## 43.7 层限：对自身的分辨率不由同层精化自动得到

§32.10 证明存在层析完备而自描述不完备的观察者；§33.10 证明操作完备不蕴含经典答案完备。故对自身的分辨率**不由**同层读数精化自动得到。**升层（§45）是一条途径，本节不主张它是唯一途径。**

---

## 43.8 提升律汇总、形式化拆分与状态

**提升律（按执行顺序；定理与规则分标）。**

1. 声明目标（命题 43.1，汇编）；
2. 为有 \(g>0\) 凭证或 carry 见证的缺陷加坐标（§38.36；规则 43.5）；
3. 先沿免税轴（命题 43.6 之 2；规则 43.7）；
4. 固定 \(q,F\) 下核塔一步不动即停前瞻精化（命题 43.8；规则 43.9）；
5. 预算投脆弱特征子空间，原料同存，联合异观察者（命题 43.10；规则 43.11）；
6. 读数精化只在轨道上界内改变视界；要移动上界，改更新（定理 43.2、推论 43.3——**仅置换模型**）；
7. 对自身的分辨率不由同层精化自动得到；升层为一途（§43.7；§45）。

**可形式化拆分。**

1. 定理 43.2：新引理 `observerDistance_top_iff_orbit_ne`（⇐ 由第一子句包装；⇒ 由望远镜引理，含 \(n<0\) 的端点对调）；
2. 推论 43.3(a)：子族 supremum 单调 + 两个显式例子；
3. 命题 43.1、43.4、43.6、43.8、43.10 均为既有结果的引用，无新证明义务。

**形式化状态。** 定理 43.2、推论 43.3 为本节新纸面证明；其余命题为汇编；规则 43.5、43.7、43.9、43.11 为决策规则（非定理）。均不得投影为 `Closed`。

---

# 44. 追加：对照评注——实践论与动作—上界律
## A Comparative Note: "On Practice" and the Action–Ceiling Law

## 44.0 文档地位

本节为**对照评注**，全部内容为非主张：它把 §43 的动作—上界律与一个成熟哲学论题逐句对表，目的是给 §43 一个成熟锚，不是用哲学证明数学，也不是用数学裁决哲学。

**对表对象。** 毛泽东《实践论》（1937）："实践、认识、再实践、再认识"；知识来自直接经验与间接经验，真理性由实践检验。相邻锚：实用主义（Peirce 1878 "How to Make Our Ideas Clear"；Dewey）、生成认知（Varela–Thompson–Rosch 1991）。**以上出处为离线记忆，未核对，状态 `ASSUMED-UNVERIFIED`。**

## 44.1 三句对表

| 实践论 | §43 对应 | 对应强度 |
|---|---|---|
| 知识从实践中产生 | 推论 43.3(b)：动作可达的上界由更新决定；不换动作，上界不动（读数精化只在上界内工作） | 置换模型内为定理；一般模型 `open` |
| 也可从他人的间接经验获得 | 命题 43.10 之 3：联合观察 = 核之交 | 定理，但附两条限制（44.2） |
| 归根结底要靠个人实践确认 | 命题 43.8：稳定性只在**自己的**更新下有定义（闭合谱卷 §5：自治须对全部行动词成立） | 定理 |

## 44.2 两条实践论未明说的限制

1. **借得到读数，借不到动作。** 他人给出的区分只是一条读数；它是否成为本观察者的稳定坐标，取决于它在本观察者的更新下是否稳定（命题 43.8）。
2. **联合不保证闭合。** 命题 43.10 之 4（Hasse 反例）。

## 44.3 一处比实践论更窄的断言（按 §43.0 的两个谓词）

实践论隐含"一切知识最终可由实践检验"。§43 只支持其条件形，且须把"检验"落到谓词上：

- **由实践检验** = 由本观察者的动作到达并观察其后果，即**动作可达**（\(x\in\operatorname{Orb}_\tau(o)\)）；
- 不在轨道内的点，本观察者可以**读数可分辨**地知道"它不同"（正因一个不变量把它分开），却**不能以动作触及**它；对它的命题在当前动作下不可由实践检验，诚实标记为 `open`，而非"尚待实践"。

故"实践是检验真理的唯一标准"在本卷读作："**在动作轨道内**，实践是唯一判官；轨道外，先换动作（推论 43.3(b)）。"**不**读作"可见球内即可检验"——零距离点在球内却不可分辨。

## 44.4 非主张

本节不主张《实践论》或任何哲学文本被"证明"或"反驳"；不主张 §43 的结论超出其模型前提；对表强度以 44.1 表中所标为准。

---

# 45. 追加：升层的操作定义与可判判据
## Ascending a Level: Operational Definition and Decidable Criteria

## 45.0 文档地位与案由

**案由。** §43.7 说对自身的分辨率不由同层精化自动得到，升层是一条途径。内化塔（PZG 17.4；CLAUDE.md 第 17、21 条）给出升层的结构：每层判前层，塔无封顶。本节给出**一个观察者升层的操作定义**（含"回合"结构，以区分回合内的反馈与回合间的更新变更），据此对几类常见"自省"做法分类，并给出可判判据。本节只新增两条结构命题（45.2、45.3）；对做法的分类为评注。

**非主张。** 本节不主张升层是唯一途径；不主张任何冥想、心理或教育实践的经验效果；不主张升层可达全知（塔无顶）；不主张本库判例具有统计意义。

## 45.1 定义

### 定义 45.1（带记录的一层观察者与第二层观察者）

**一层观察者（带记录）。** \(O_1\) 的增广状态为 \((x,\lambda)\in X\times\Lambda_1\)，其中 \(\Lambda_1\) 为 append-only 记录（量子卷 §15.1 双列分家：记录列单调不减）；一步演化为
\[
(x,\lambda)\longmapsto\bigl(\widetilde T_1(x,z),\ \lambda\cdot q_1(x)\bigr),
\]
其中 \(\lambda\cdot q_1(x)\) 表示追加本步读数，\(\widetilde T_1:X\times Y_2\to X\) 是**受控更新**，其第二变元 \(z\in Y_2\) 为可能来自第二层的输入。

**第二层观察者。** \(O_2\) 由读出 \(q_2:\Lambda_1\to Y_2\) 给出：它读的是 \(O_1\) 的记录，不是 \(X\)。

**回合与脱钩。** 把演化分成回合 \(e=1,2,\dots\)，每回合内 \(\widetilde T_1\) 固定。称 \(O_2\) 在回合 \(e\) 内**脱钩**，若
\[
\boxed{
\widetilde T_1(x,z)=\widetilde T_1(x,z')\qquad\forall x,\ z,z'\in Y_2,
}
\]
即回合内 \(O_1\) 的更新不依赖 \(q_2\) 的输出。**回合间**允许把 \(\widetilde T_1\) 换成 \(\widetilde T_1'\)（这正是推论 43.3(b) 的"动作变更"），其选择可以依赖 \(q_2\) 在上一回合的读数。称 \(O_2\) 为 \(O_1\) 的**第二层观察者**，若它在每个回合内脱钩。

### 定义 45.2（同层）

称一对 \((O_1,O_2)\) 在回合 \(e\) **同层**，若把 \(X\times\Lambda_1\) 视为单一状态空间、以 \((q_1\circ\pi_X,\ q_2\circ\pi_\Lambda)\) 为联合读出、以定义 45.1 的一步演化为更新后，\(q_2\) 对该联合商的评价是该单一系统的同层自应用（§32.1 的 \(\Delta\)）。

### 命题 45.3（回合内耦合即同层）

若在回合 \(e\) 内脱钩条件不成立（\(\widetilde T_1\) 依赖 \(z\)），则 \((O_1,O_2)\) 在该回合同层；从而 §32.10、§33.10 关于同层自描述的**非蕴含**结论原样适用：该联合系统的自描述闭合**不自动成立**。

#### 证明

依赖 \(z=q_2(\lambda)\) 的更新是 \(X\times\Lambda_1\) 上的一个自映射 \(\bigl(x,\lambda\bigr)\mapsto\bigl(\widetilde T_1(x,q_2(\lambda)),\lambda\cdot q_1(x)\bigr)\)；联合读出下的商是该增广空间上的商，\(q_2\) 的评价是其自应用，符合定义 45.2。§32.10/§33.10 的结论对任意观察者成立，特别对此增广系统成立。\(\square\)

**辨析。** 本命题不断言同层自描述"不可能"，只断言其闭合不自动成立；升层的价值在于让 \(q_2\) 的对象（记录）与其评价所处的系统（\(O_1\) 的回合内演化）分离。

### 命题 45.4（对象取记录与取状态的分辨差，条件形）

设两段历史 \(\gamma,\gamma'\) 具有相同终点 \(x\in X\)、不同记录像 \(\lambda\neq\lambda'\in\Lambda_1\)。则：

1. 任何只读 \(X\) 的读出 \(s:X\to Y\) 不能区分 \(\gamma,\gamma'\)（\(s(x)=s(x)\)）；
2. 读记录的 \(q_2\) 能区分它们**当且仅当** \(q_2(\lambda)\neq q_2(\lambda')\)。

#### 证明

两条皆为定义验算。\(\square\)

**辨析。** 本命题不断言"当前状态永远不含历史"（终点映射可以是单射），也不断言"读记录必能恢复历史"（须 \(q_2\) 分离相应记录像）；它只给出§37.11 与 §33.6 在本设定下的精确条件形。

## 45.2 常见做法的分类（评注）

| 做法 | 本卷对应 | 是否升层（按定义 45.1） |
|---|---|---|
| 专注（收窄到任务所需） | 最小充分界面（§38.35）；层内闭合 | 否（层内分辨率） |
| 放空（放掉无关区分） | 降低 nuisance 的 \(h\)（§38.15），释放预算 | 否（升层的前置） |
| 观而不随（回合内读念头而不据此行动） | 回合内脱钩；但对象为当前状态而非记录（命题 45.4 之 1 的限制） | 候选；对象易失 |
| 写记录并隔期重读 | 对象 = 记录（\(q_2:\Lambda_1\to Y_2\)）；隔期 = 新回合，回合内脱钩、回合间可换 \(\widetilde T_1\) | 是 |
| 由异更新读者读记录 | 对象 = 记录；读者的更新与 \(O_1\) 回合内天然脱钩；CLAUDE.md 第 13/14 条 | 是 |

**本库判例（单例，非统计；来源为 PR #3366 正文的作者自报）。** 同一份 §42 v1.0 文本，作者自报自查得 2 处缺陷，异模型盲评席得 13 处（3 blocking / 9 material / 1 minor），13 处经作者逐条核实全部成立并采纳。这是定义 45.1 的一次实例：席位读的是已落盘的文本（记录），其更新与作者回合内脱钩；作者据其读数在下一回合更换了写作更新（v1.1）。"自查 2"一项在库内无独立证据，只有该 PR 正文的自报。

## 45.3 批评作为读数：核，而非信

他人的批评是第二层观察者的一条读数："你把 \(A,B\) 商掉了。"其正确处置是**核实**：\(A,B\) 在本观察者的更新下是否确不同（命题 43.8）。核实则加坐标；不实则记录分歧。**不核而在回合内全收**，即让 \(\widetilde T_1\) 依赖 \(z\)，由命题 45.3 退回同层。"满"在本卷有精确含义：断言自身商已统一完成——在命题 43.1 的前提下恒假。"谦"的收据不是态度，是记录中新增了一个具体区分。

## 45.4 判据（可判）

一个做法是否实现了升层，检查四项：

1. 是否产出记录（他人或隔期的自己可读的对象，命题 45.4 之 2 的前提）；
2. 读数是否在**回合内**回流到 \(\widetilde T_1\)（是 ⟹ 命题 45.3，同层）；回合间据此更换更新不在此禁，那是推论 43.3(b)；
3. 是否解释掉一个 \(O_1\) 原先解释不了的 carry（能指出具体的 \(A,B\)）；
4. "平静"不作证据——它是预算清理（§45.2 第 2 行）的副产品，与升层无关。

## 45.5 边界

第二层同样不能自动闭合自身（§32.10/§33.10 对 \(O_2\) 原样成立）；塔无封顶（CLAUDE.md 第 21 条：顶上标 open）。升层给出的是**上一层**，不是全知；也不是唯一途径（§43.7）。

## 45.6 形式化拆分与状态

- 定义 45.1–45.2、命题 45.3–45.4：可写成有限集合上的结构引理（增广状态、受控更新的变元无关性、记录像的分离），初等；
- §45.2 表、§45.3、§45.4：评注与规则，非定理。

均不得投影为 `Closed`。

**本节最终一句。**

\[
\boxed{
\text{升层 = 读自己的记录，且回合内读到的东西不回流进自己的更新；回合间据此换更新，就是动作变更。}
}
\]
