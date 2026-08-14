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
