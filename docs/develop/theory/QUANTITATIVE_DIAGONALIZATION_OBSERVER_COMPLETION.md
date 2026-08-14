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
