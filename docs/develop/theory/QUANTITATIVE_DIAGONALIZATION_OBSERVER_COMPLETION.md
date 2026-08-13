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
