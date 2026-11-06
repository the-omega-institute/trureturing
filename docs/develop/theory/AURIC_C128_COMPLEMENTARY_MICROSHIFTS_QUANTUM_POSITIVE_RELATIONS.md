# 对向微移，合计不降

> 参考输入：AI 撰写的工作稿，由用户提供于本会话（2026-11-04，Asia/Singapore）。Lean 是仓库的数学真源；本文仅为参考文稿，未作形式化认证。

AURIC 量子关系研究

从局部实序到完全正过程

C128

两份相同的历史，一份加一点，另一份减同样多；

留下的合计余量，必须真实且不负。

$$
\boxed{Q(a+tz)+Q(a-tz)-2Q(a)\in\mathbb R_{\ge0}.}
$$

只固定一个中心，对每个已声明相干方向，在任意小的非零尺度上要求这一条关系。

在复半双线性接口中，它推出 Hermitian 正关系；在单事件的一条来源行上，它恰好选择完全正过程。无需先给正单位，也无需先给保伴随性。完整概率的一份一，由原记录归一化随后供应。

固定源码：`1764a0c7f33b`
提交时点：2026-11-04 16:03:22，Asia/Singapore
对应 2026-11-04 08:03:22 UTC

自包含工作稿：定义、定理、证明、几何与有限证据

## 摘要与回溯位置

C127 从一个正单位不可双零分解，选择 Hermitian 正关系及完整量子仪器。C128 退到单位之前：比较 $\Gamma$ 只预设复半双线性，$Q(h)=\Gamma(h,h)$ 甚至可先为复数。唯一候选要求一个中心的对向微移增量，在每个方向任意小的非零尺度上落入实非负射线。精确恒等式

$$
\Delta_a(tz):=Q(a+tz)+Q(a-tz)-2Q(a)=2|t|^2Q(z)
$$

使局部条件直接给全域非负实自比较；复极化再恢复 Hermitian 性。零差商因此具有内积。该核心不需要正单位、总归一化、有限维、辅助范数或连续性。

对仅给复线性的候选单事件 $\Phi:M_d(\mathbb C)\to M_m(\mathbb C)$，一条来源行的历史关系表就是尚未假定 Hermitian 的 Choi 表。候选等价于该表正半定，因而推出保伴随与完全正性。原完整记录的 $\sum_j\Phi_j(I)=I$ 只在仪器层给正效果、不增迹与总保迹，不再用来先选正方向。

这不是将 C127 的已知中点恒等式重新命名为新发现。本轮证明它在更少背景前件上独自完成选择；代价是采用实序读数，不能只看实部、零集合或绝对值。复相干二次结构与完整方向量词仍有内容，零过程和放大 CP 过程也会通过核心。

最早的几何是一条没有负曲率的抛物线；两实方向提升成平面、抛物柱或椭圆抛物面。完整复二元关系属于正矩阵锥；非零总量可内生归一为 Bloch 球，零总量保留为锥顶。有限维中令 $G=H+iK$，同一个局部缺陷恰为 $2R^2\max\{(-\lambda_{\min}H)_+,\|K\|\}$，并给到无约束正锥距离的紧 $\sqrt2$ 控制。

本轮核读新的 C117 有符号稳定性与共同正性障碍，以及规范滤片正细化的 Lean 证明体和一般粗过程反例。它们要求保留同一原记录图，不能用逐标签近似替代共同正性；也不能由数学表示自动供应实际门、参考或更新。本稿给出有限量子规则的条件性闭合，不宣称已完成复数、场内容或物理时钟的起源。

| 项目 | C127 | C128 |
|---|---|---|
| 唯一新增约束 | 一个单位不可双零分解 | 一个中心的互补微移实非负 |
| 保伴随/Hermitian | 前件 | 由局部实序恢复 |
| 正历史单位 | CP 选择前件 | 不需要 |
| 完整归一化 | 先供应正单位 | 后组装完整仪器 |
| 检验方向 | 完整单位背景中的相干方向 | 每个单事件一来源行的完整方向 |
| 精确见证 | 双零可能需要大系数 | 失败在任意小尺度出现 |
| 有限误差 | 负谱 | 非实部分与负谱的同一缺陷 |

## 目录

- [1. 新源码中的正性边界](#section-1)
- [2. 唯一候选：互补微移不降读数](#section-2)
- [3. 单事件的局部条件选择完全正过程](#section-3)
- [4. 局部曲率的三维几何与有限证据](#section-4)
- [5. 从局部条件闭合有限量子理论](#section-5)
- [6. 观察者内生与本轮仍有的前件](#section-6)
- [7. 本轮唯一候选与完整白话](#section-7)
- [参考文献](#references)

<a id="section-1"></a>

## 1. 新源码中的正性边界

<a id="sec-c128-sources"></a>

本轮固定 `1764a0c7f33be6acf6dcaf4ad4007da021469ae9`，提交时点为 2026-11-04 16:03:22（Asia/Singapore）。相对前轮 `7c2b901642e2`，完整 Git 子树比较登记了理论目录 16 个变更、量子源码目录 35 个变更。本稿精读的是下面列明的新增段、五份正细化 Lean 文件及相关直接定义，不把变更登记当作全仓数学认证。

仓库 C123 文件中现有的“C127：Z/II/S”是另一个命名序列，不是本对话 C127 的“单位不可双零分解”。下文按文件与节号定位，避免同号混同。

### 1.1 最新 C117：小残差先给有符号仿射族

HEAD 的 PR #26420 只追加 C117 第 21–24 节，未新增 Lean 定理。它保留原全未来方向充分性、连续性、实三维比较、实际控制旋转稠密于 $SO(W)$、原请求图及全部标签。原黄金四时关系在全部实际前后文的绝对残差至多 $\varepsilon$ 时，同一个线性投影

$$
PF_i(n)=\alpha_i+\langle\beta_i,n\rangle
$$

准确保留原图的线性记录恒等式，并满足

$$
\sup_i\|F_i-PF_i\|_\infty\le5\varepsilon.
$$

投影结果可能带负值。令 $d_{\mathcal D}$ 为原概率族到同图共同正仿射族的距离，$\tau_{\mathcal D}$ 为投影族到同一合法集合的距离，新证明给

$$
|d_{\mathcal D}(F)-\tau_{\mathcal D}(PF)|\le5\varepsilon,
 \qquad \tau_{\mathcal D}=\sup_T\tau_T,
$$

其中 $T$ 遍历所有有限原图子系统，而非一个已测有限片段 [1](#ref-repo-c128-c117)。

同一可数请求图的反例将联合细标签分成 $N$ 份，得到 $\varepsilon_N\to0$，但保留共同边缘记录后，对 $N\ge7$ 仍有

$$
d_{\mathcal D}(F^{(N)})=\frac{1-1/\sqrt2}{2}>0.
$$

每个请求的标签数有限，整个图没有统一标签数上界。该辅助图未与原生 $1024$ 标签接口识别；不能称其已否证原生来源。对本轮的约束是：逐标签近似、数学正锥修复与保持同一原图的完整修复须分开。这里的终端仿射化也没有自动提供本稿所继承的复半双线性历史。

### 1.2 正细化何时强制 CP，何时不强制

新增五份 Lean 文件从正映射的支持论证出发。在已给复有限矩阵直和、复线性正细支的前提下，若细支之和在每个原块 $b$ 上，对全部复输入恰是规范单算符滤片
$X_b\mapsto\sqrt {E_b}\,X_b\sqrt {E_b}$，那么细支 $a$ 在该块上只能为该滤片的非负标量倍 $c_{ab}$；系数可依块而异，奇异与零支均包含。由此每支在全部有限矩阵放大下保持正性 [2](#ref-repo-c128-refinement)。

一般 CP 粗过程没有这种结论。新反证文件取二维映射

$$
S_1(X)=\tfrac12X^T,\qquad
 S_2(X)=\tfrac12\bigl(\operatorname{Tr}(X)I-X^T\bigr).
$$

二者都正，迹均为原迹的一半；$S_2(X)=UXU^*/2$，其中
$U=\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$，而

$$
(S_1+S_2)(X)=\tfrac12\operatorname{Tr}(X)I
$$

是完全正且保迹的去极化过程。但是 $S_1$ 不完全正 [3](#ref-repo-c128-refutation)。
这五份文件都有实际证明体；本轮核读源码，未运行新的 Lean 构建，也未认证全部上游文件。

本稿的局部候选对这个坏细支有直接见证。对 $S_1$ 的历史形式，取

$$
z=\frac{E_{11}\otimes e_2-E_{12}\otimes e_1}{\sqrt2}.
$$

直接代入得 $Q_{S_1}(z)=-1/2$，所以任意中心 $a$ 与任意非零实 $t$ 都满足

$$
\Delta_a(tz)=-t^2<0.
$$

因此无需先指定规范粗滤片，也无需寻找双零，本轮在单事件的一条来源行内就发现违例。

### 1.3 平方读数不能替代另名的有向关系

仓库 C123 文件第 35–40 节把原有向关系的零正配对接回指定内导子空间，同时给出完整背景反族：所有 $D_a^2$ 都保持不变，但不同标签的有序混合交换子仍有可见的中心残差 [4](#ref-repo-c128-directed)。
其极化只能从算符平方恢复两种顺序的和，不能恢复它们的差。
本稿使用的是复*半双线性标量形式*的极化，不能据此宣称已经识别一个另行指定的 $D$、方向乘法或原更新。两者的逻辑对象不同。

**白话。**最新源码把问题收得很具体：每个小读数都接近某个线性表，还不保证这些表能共同成为正关系；粗过程合法，也不保证每个细支合法。本轮因此直接检查原细过程自己的相干方向。两份历史向相反方向挪一点，线性变化抵消，只让那个方向自己的弯曲留下来。

<a id="section-2"></a>

## 2. 唯一候选：互补微移不降读数

<a id="sec-c128-local"></a>

本轮把正单位与保伴随性从选择正关系的前件中撤去。继承的结构仍是复相干历史及半双线性比较；新增要求改为一个中心附近的二元实序约束。这里的比较表尚未认证为合法读数，故先允许其自比较为复数。

### 定义 2.1（形式比较与互补微移）

设 $V$ 为复向量空间，$\Gamma:V\times V\to\mathbb C$ 为半双线性形式，首槽共轭，不预设 Hermitian 性。置 $Q(v)=\Gamma(v,v)$，固定任意中心 $a\in V$，定义

$$
\Delta_a(z):=Q(a+z)+Q(a-z)-2Q(a).
$$

两段历史 $a+z,a-z$ 的和保持为 $2a$；$\Delta_a(z)$ 是它们相对均分的合计自比较增量。

### 定义 2.2（C128：方向局部实序）

在上述同一历史域内，对每个方向 $z$ 及每个 $\varepsilon>0$，存在一个实系数 $t$，使

<a id="eq-c128-single-axiom"></a>

$$
\boxed{0<|t|<\varepsilon,\qquad
 \Delta_a(tz)\in\mathbb R_{\ge0}.}
\tag{1}
$$

这里的 $\mathbb R_{\ge0}$ 是 $\mathbb C$ 中的实非负射线；不能将条件改写为仅实部非负。无需各方向共享一个可用半径，也不预设 $V$ 的范数或拓扑。

### 定理 2.3（一个中心的局部判据）

<a id="thm-c128-local"></a>

以下条件等价：

1. 固定中心 $a$ 满足 C128；

2. 对每个 $z$，存在任意一个非零实系数 $t$ 使 $\Delta_a(tz)\in\mathbb R_{\ge0}$；

3. $Q(z)\in\mathbb R_{\ge0}$ 对全部 $z$ 成立，且 $\Gamma$ 为 Hermitian 正半定形式；

4. 所有中心、所有位移均满足该实序约束。

结论不要求正单位、非零读数、有限维或连续性。

**证明。**
对任意复系数 $t$，半双线性展开给

$$
\begin{aligned}
Q(a+tz)&=Q(a)+t\Gamma(a,z)+\bar t\Gamma(z,a)+|t|^2Q(z),\\
 Q(a-tz)&=Q(a)-t\Gamma(a,z)-\bar t\Gamma(z,a)+|t|^2Q(z).
\end{aligned}
$$

因此，在尚未假设实性或正性时已有

<a id="eq-c128-second-difference"></a>

$$
\boxed{\Delta_a(tz)=2|t|^2Q(z).}
\tag{2}
$$

只要 $t\ne0$，将实序条件除以正实数 $2|t|^2$，就得到 $Q(z)\in\mathbb R_{\ge0}$。
一般半双线性形式的极化恒等式为

$$
\Gamma(x,y)=\frac14\bigl[Q(x+y)-Q(x-y)
 -iQ(x+iy)+iQ(x-iy)\bigr].
$$

各自比较为实，便给 $\Gamma(y,x)=\overline{\Gamma(x,y)}$；结合 $Q\ge0$ 得 Hermitian 正半定性。反向由式 [(2)](#eq-c128-second-difference) 立即成立，并适用于所有中心和所有位移。

因此，“任意小”不需要另加极限交换。精确二次结构使每个方向上任意一次非零检查就决定该方向的符号；若允许所有见证取 $t=0$，条件便完全空洞。
二元性作用于两段完整复合历史，方向 $z$ 仍可承载很多原始系数。形式微移的存在也不自动供应实际相干制备或任意小的装置控制。

### 推论 2.4（零差商与前轮单位判据）

<a id="cor-c128-quotient"></a>

候选成立后，$\mathcal N=\{h:Q(h)=0\}=\operatorname{rad}\Gamma$ 是线性空间，
$h\sim k\iff h-k\in\mathcal N$ 可在全部比较中替换。
商空间的内积 $\langle[h],[k]\rangle=\Gamma(h,k)$ 良定义，其完成为 Hilbert 空间。
若后续给出 $Q(e)=1$ 的单位，则它不能拆成两个零历史，即恢复本对话 C127。

**证明。**
若 $Q(h)=0$，对任意 $k,t$ 的正性给
$2\Re(t\Gamma(h,k))+|t|^2Q(k)\ge0$。选适当相位及任意小的 $t$，得 $\Gamma(h,k)=0$。
故零集合为根空间，商内积不依赖代表且正定。两个根空间元素的和仍在根空间，不能等于自比较为一的 $e$。

若 $Q$ 非零，可以从任意正读数历史 $h$ 取得形式单位 $h/\sqrt{Q(h)}$；这不等于已经取得完整仪器的单位保持条件。零形式也满足本轮候选，因而单位或非平凡性没有被偷偷加入核心。

本轮减少了保伴随与正单位这些背景前件，并将全域双零搜索改为方向局部约束。代价也应明说：C127 利用零集合和一个正单位，C128 使用读数的实序。实性是同一射线条件的一部分，不能宣称它无条件消失；相干半双线性仍是从局部外推全域的依据。

**白话。**不用先拿到一份全局单位。先留住当前中心，让两段历史一边挪一点、另一边反向挪同样多。相干关系是二次的，中心和混合项会消掉，只剩这个方向自己的余量乘上位移的平方。要求余量仍沿同一实读出轴且不为负，就能同时排除偏离实轴的比较和向下的弯曲；可靠的零差与内积随后才出现。

<a id="section-3"></a>

## 3. 单事件的局部条件选择完全正过程

<a id="sec-c128-process"></a>

### 定义 3.1（复线性候选事件）

取 $d,m\ge1$ 及复线性映射 $\Phi:M_d(\mathbb C)\to M_m(\mathbb C)$，不预设保伴随、正性、完全正性或单位效果不等式。在
$\mathfrak H_\Phi=M_d\otimes\mathbb C^m$ 上定义

$$
\Gamma_\Phi\left(\sum_r a_r\otimes u_r,\sum_s b_s\otimes v_s\right)
 =\sum_{r,s}\langle u_r,\Phi(a_r^*b_s)v_s\rangle.
$$

复线性保证这个形式在张量空间上良定义。令
$C_\Phi=[\Phi(E_{rs})]_{r,s=1}^d$，此时 Choi 表尚不必为 Hermitian。

### 定理 3.2（一个来源行上的局部 CP 判据）

<a id="thm-c128-process"></a>

固定任意来源行 $p$ 及任意中心 $a\in\mathfrak H_\Phi$，令

$$
\mathfrak H_p=
 \left\{\sum_{r=1}^dE_{pr}\otimes u_r:u_r\in\mathbb C^m\right\}.
$$

以下条件等价：

1. 只对方向 $z\in\mathfrak H_p$，中心 $a$ 满足 C128；

2. $C_\Phi=C_\Phi^*\succeq0$；

3. $\Phi$ 完全正。

成立后，$\Phi$ 自动保伴随。该判据不要求补事件、总归一化、正单位或遍历全部来源行。

**证明。**
矩阵单位满足 $E_{pr}^*E_{qs}=\delta_{pq}E_{rs}$。故对
$z=\sum_rE_{pr}\otimes u_r$，

<a id="eq-c128-row-form"></a>

$$
Q_\Phi(z)=\sum_{r,s}\langle u_r,\Phi(E_{rs})u_s\rangle
 =u^*C_\Phi u,
 \qquad G_\Phi=I_d\otimes C_\Phi.
\tag{3}
$$

由式 [(2)](#eq-c128-second-difference)，(1) 恰好给
$u^*C_\Phi u\in\mathbb R_{\ge0}$ 对所有 $u\in\mathbb C^{dm}$ 成立。
极化给 $C_\Phi=C_\Phi^*$，自比较给正半定性，即 (2)。其分块伴随关系
$\Phi(E_{rs})^*=\Phi(E_{sr})$ 再由复线性扩展为保伴随性。

若 (2) 成立，整个历史关系矩阵 $G_\Phi\succeq0$。任取
$X=[X_{rs}]=T^*T\in M_n(M_d)$ 为正，并取任意 $u_r\in\mathbb C^m$，则

$$
\sum_{r,s}\langle u_r,\Phi(X_{rs})u_s\rangle
 =\sum_\ell Q_\Phi\left(\sum_rT_{\ell r}\otimes u_r\right)
 \in\mathbb R_{\ge0}.
$$

因此 $(\operatorname{id}_n\otimes\Phi)(X)$ 为正；$n$ 任意，得到完全正性。
反之，若 $\Phi$ 完全正，将它逐块作用于正矩阵 $[a_r^*a_s]$，再以向量族评价，便得 $Q_\Phi\ge0$。由增量恒等式，任意中心和方向均满足 (1)。

固定一来源行没有省去完整的输入系数：$u_r$ 仍遍历全部列方向与 $m$ 维输入空间。它不是单输入测量，也不把形式上存在的历史组合自动升级为实际可调用门。

### 3.1 完整仪器的归一化放到下一层

对一族已通过上述判据的原事件 $\Phi_j:M_{d_j}\to M_m$，若实际完整记录另给

<a id="eq-c128-record-normalization"></a>

$$
\sum_j\Phi_j(I_{d_j})=I_m,
\tag{4}
$$

则由 CP 得 $E_j=\Phi_j(I_{d_j})\succeq0$，再由
$I_m-E_j=\sum_{k\ne j}E_k\succeq0$ 得效果上界。
因此各态方向支迹不增，全部原支合计保迹。此时才形成完整量子仪器。

零映射与 $\Phi=c\,\operatorname{id}$（$c>1$）都满足核心候选：前者不提供非零单位，后者不保持单位且在正输入上放大迹。这证明归一化、非平凡性和合法概率支不是局部判据单独供应的结论。

### 3.2 删除前件会漏过哪些关系

**只检查实部。**

标量映射 $\Phi(\lambda)=(1+i)\lambda$ 给
$Q(z)=(1+i)|z|^2$。其全部 $\Re\Delta_a(tz)\ge0$，但 $\Phi(1)=1+i$ 不自伴，也不正。实序射线中的实性不能删去；只比绝对值同样不能替代它。

**只检查实系数方向。**

取 $C=\left(\begin{smallmatrix}1&1\\-1&1\end{smallmatrix}\right)$。
实向量的读数为 $\|x\|^2$，但 $z=(1,i)/\sqrt2$ 的读数为 $1+i$。
这个表可定义一个复线性 $M_2\to\mathbb C$ 事件，却未被实方向检查认证为保伴随。

**把二元历史偷换成两个坐标。**

取 $G=(8/5)I_3-(3/5)\mathbf1\mathbf1^*$，其中 $\mathbf1=(1,1,1)^T$。每个两坐标主块的特征值为 $2/5,8/5$，均为正；但
$G\mathbf1=-\mathbf1/5$。它可以作为一个 $M_3\to\mathbb C$ 事件的 Choi 表，说明全部两坐标检查仍会漏过完整三方向负组合。候选作用的是两个复合历史，方向本身不能限为两个基坐标。

**撤去精确二次结构。**

$Q(x)=x^2-x^4$ 在中心零附近满足每方向的局部条件，却在 $|x|>1$ 时为负，故局部不再决定全域。
由三角不等式与实平方的凸性，$Q(x)=\|x\|_4^2$ 满足全域中点凸性，却仍不来自内积：在二维中

$$
Q(e_1+e_2)+Q(e_1-e_2)=2\sqrt2
 \ne4=2Q(e_1)+2Q(e_2).
$$

所以本轮撤掉的是保伴随与单位前件，未从无结构的凸性中推出复线性或全部量子规则。

**白话。**不必先把每个事件塞进一份已归一的完整仪器。先在事件自身的历史里检查：中心不变的微小分岔，余量能不能始终沿同一实读出轴且不下降。通过这个条件，事件才获得保伴随与完全正的资格。然后把真实的成功、失败记录放回完整测试，归一化才进一步给出合法概率支。

<a id="section-4"></a>

## 4. 局部曲率的三维几何与有限证据

<a id="sec-c128-geometry"></a>

### 4.1 最小图形：平分点只能上弯或平坦

固定中心 $a$，互补微移差额为

$$
\Delta_a(tz)=Q(a+tz)+Q(a-tz)-2Q(a)=2t^2Q(z),\qquad t\in\mathbb R.
$$

沿任一方向，它是一条过原点的二次曲线。候选要求整条局部差额落在非负实轴：向下弯或出现非零虚部都会失败。中心无需归一化；核心判据也没有引入系数范数。

<a id="fig-c128-curvature"></a>

```latex
\begin{tikzpicture}[font=\small,>=Latex]
 \begin{scope}[x=1.1cm,y=0.74cm]
  \node at (0,1.66) {上弯：通过};
  \draw[black!48,->] (-1.30,0)--(1.45,0) node[right] {$t$};
  \draw[black!48,->] (0,-1.15)--(0,1.28) node[left] {$\Delta$};
  \draw[teal!75!black,very thick,domain=-1.12:1.12,samples=60]
    plot (\x,{0.8*\x*\x});
  \fill[teal!75!black] (0,0) circle (1.6pt);
 \end{scope}
 \begin{scope}[xshift=4.25cm,x=1.1cm,y=0.74cm]
  \node at (0,1.66) {平坦：通过};
  \draw[black!48,->] (-1.30,0)--(1.45,0) node[right] {$t$};
  \draw[black!48,->] (0,-1.15)--(0,1.28) node[left] {$\Delta$};
  \draw[teal!75!black,very thick] (-1.12,0)--(1.12,0);
  \fill[teal!75!black] (0,0) circle (1.6pt);
 \end{scope}
 \begin{scope}[xshift=8.50cm,x=1.1cm,y=0.74cm]
  \node at (0,1.66) {下弯：否决};
  \draw[black!48,->] (-1.30,0)--(1.45,0) node[right] {$t$};
  \draw[black!48,->] (0,-1.15)--(0,1.28) node[left] {$\Delta$};
  \draw[red!75!black,very thick,domain=-1.12:1.12,samples=60]
    plot (\x,{-0.8*\x*\x});
  \fill[red!75!black] (0,0) circle (1.6pt);
 \end{scope}
\end{tikzpicture}
```

**图 1。**这里只画实差额；非零虚部也由同一个候选排除。$t$ 是历史的形式系数，不是物理时间。平坦方向必须允许，否则会排除具有非平凡零差的合法过程。

### 命题 4.1（两个实方向的三维提升）

<a id="prop-c128-real-slices"></a>

候选成立后，取两段历史 $u,v$，令

$$
s(x,y):=\tfrac12\Delta_a(xu+yv)
 =\begin{pmatrix}x&y\end{pmatrix}
 \underbrace{\begin{pmatrix}Q(u)&\Re\Gamma(u,v)\\
 \Re\Gamma(u,v)&Q(v)\end{pmatrix}}_{M_{u,v}\succeq0}
 \begin{pmatrix}x\\y\end{pmatrix},\qquad x,y\in\mathbb R.
$$

经实坐标正交旋转，曲面为 $s=\kappa_1X^2+\kappa_2Y^2$，$\kappa_1,\kappa_2\ge0$。
两者均零、一正一零、两者均正，分别给平面、抛物柱和向上开的椭圆抛物面。

**证明。**
展开 $Q(xu+yv)$ 得所示矩阵；全域正性使其为实正半定矩阵。实对称谱分解给两个非负二次系数；相应 Hessian 特征值为 $2\kappa_1,2\kappa_2$。

<a id="fig-c128-three-dimensional"></a>

```latex
\begin{tikzpicture}[font=\small,>=Latex]
 \path[use as bounding box] (-1.65,-0.80) rectangle (10.85,2.90);
 \node at (0,2.72) {平面};
 \node at (0,2.40) {$s=0$};
 \node at (4.60,2.72) {抛物柱};
 \node at (4.60,2.40) {$s=X^2$};
 \node at (9.20,2.72) {抛物面};
 \node at (9.20,2.40) {$s=X^2+Y^2$};

 \def\cgeomaxes{%
  \draw[black!45,->] (-1.30,0,0)--(1.36,0,0)
   node[anchor=north west,black!70,fill=white,inner sep=1pt] {$X$};
  \draw[black!45,->] (0,-1.30,0)--(0,1.36,0)
   node[anchor=south west,black!70,fill=white,inner sep=1pt] {$Y$};
  \draw[black!45,->] (0,0,0)--(0,0,3.18)
   node[anchor=west,black!70,fill=white,inner sep=2pt] {$s$};
 }

 \begin{scope}[x={(0.72cm,-0.30cm)},y={(0.72cm,0.30cm)},z={(0cm,0.65cm)}]
  \fill[teal!7] (-1,-1,0)--(1,-1,0)--(1,1,0)--(-1,1,0)--cycle;
  \foreach \q in {-1,-0.5,0,0.5,1}{
   \draw[teal!55!black,line width=0.35pt] (-1,\q,0)--(1,\q,0);
   \draw[teal!55!black,line width=0.35pt] (\q,-1,0)--(\q,1,0);
  }
  \draw[teal!80!black,line width=0.75pt]
   (-1,-1,0)--(1,-1,0)--(1,1,0)--(-1,1,0)--cycle;
  \cgeomaxes
 \end{scope}

 \begin{scope}[xshift=4.60cm,x={(0.72cm,-0.30cm)},y={(0.72cm,0.30cm)},z={(0cm,0.65cm)}]
  \draw[black!15,dashed] (-1,-1,0)--(1,-1,0)--(1,1,0)--(-1,1,0)--cycle;
  \foreach \q in {-1,-0.5,0,0.5,1}{
   \draw[teal!65!black,line width=0.4pt,domain=-1:1,samples=41,variable=\t]
    plot ({\t},{\q},{\t*\t});
   \draw[teal!55!black,line width=0.35pt]
    (\q,-1,{\q*\q})--(\q,1,{\q*\q});
  }
  \foreach \q in {-1,1}{
   \draw[teal!80!black,line width=0.75pt,domain=-1:1,samples=41,variable=\t]
    plot ({\t},{\q},{\t*\t});
   \draw[teal!80!black,line width=0.75pt] (\q,-1,1)--(\q,1,1);
  }
  \cgeomaxes
 \end{scope}

 \begin{scope}[xshift=9.20cm,x={(0.72cm,-0.30cm)},y={(0.72cm,0.30cm)},z={(0cm,0.65cm)}]
  \draw[black!15,dashed] (-1,-1,0)--(1,-1,0)--(1,1,0)--(-1,1,0)--cycle;
  \foreach \q in {-1,-0.5,0,0.5,1}{
   \draw[teal!65!black,line width=0.4pt,domain=-1:1,samples=41,variable=\t]
    plot ({\t},{\q},{\t*\t+\q*\q});
   \draw[teal!55!black,line width=0.35pt,domain=-1:1,samples=41,variable=\t]
    plot ({\q},{\t},{\q*\q+\t*\t});
  }
  \foreach \q in {-1,1}{
   \draw[teal!80!black,line width=0.75pt,domain=-1:1,samples=41,variable=\t]
    plot ({\t},{\q},{\t*\t+1});
   \draw[teal!80!black,line width=0.75pt,domain=-1:1,samples=41,variable=\t]
    plot ({\q},{\t},{1+\t*\t});
  }
  \cgeomaxes
 \end{scope}
\end{tikzpicture}
```

**图 2。**两个实系数与一个实读数构成三维图。三种标准形对应实二次型的秩 $0,1,2$；画的是关系读数，不是物理时空。

这里的曲率属于读数函数，不是时空曲率；实切片的秩也不是复 Hilbert 维数。例如 $v=iu$ 时，两段历史复线性相关，却给 $s=Q(u)(x^2+y^2)$。零曲率方向恰是当前比较的根空间方向；将它们取商后得到正定内积。

联系最初的 $a^2+xab+b^2$ 图景：$xab$ 对每个变量分别线性，对二元组则是双线性的。若把二次式设为一，$x=0$ 才是圆；$x=2$ 给 $(a+b)^2=1$，是两条平行直线。对应读数曲面从圆碗退化为一条槽，准确表达了一个相干方向成为零差，而非读出条件已变成普通直线性。

### 4.2 相位完整性与更大的正关系锥

写 $\alpha=Q(u)$、$\beta=Q(v)$、$c=\Gamma(u,v)$。相对相位 $\theta$ 的实切片为

$$
Q(xu+e^{i\theta}yv)
 =\alpha x^2+2xy\Re(e^{i\theta}c)+\beta y^2.
$$

它对全部 $x,y,\theta$ 非负，当且仅当

<a id="eq-c128-phase-gram"></a>

$$
B_{u,v}:=\begin{pmatrix}\alpha&c\\\bar c&\beta\end{pmatrix}\succeq0
 \quad\Longleftrightarrow\quad
 \alpha,\beta\ge0,\qquad \alpha\beta\ge|c|^2.
\tag{5}
$$

证明只需取 $\sup_\theta|\Re(e^{i\theta}c)|=|c|$，再用二阶实关系表的正性判据。

只测 $\theta=0,\pi/2$ 不够。取 $\alpha=\beta=1,c=1+i$，这两张实关系表的非对角项分别为 $1,-1$，均正半定；但 $\det B=-1$。在 $\theta=-\pi/4$、$x=1,y=-1$ 时，读数为 $2-2\sqrt2<0$。两种相位可以重建 $c$，不能把这两个平面的正性冒充全部相位正性。数学上选出最坏相位，也不供应实际相位控制门。

式 [(5)](#eq-c128-phase-gram) 给二阶正矩阵锥。令

$$
(T,X,Y,Z)=(\alpha+\beta,\,2\Re c,\,-2\Im c,\,\alpha-\beta),
$$

就有 $T\ge\sqrt{X^2+Y^2+Z^2}$。非零关系表自身给 $\tau=\alpha+\beta>0$，于是

$$
\frac{B_{u,v}}\tau=\frac{I+r\cdot\sigma}{2},\qquad
 r=\frac{(2\Re c,-2\Im c,\alpha-\beta)}\tau,\quad \|r\|\le1.
$$

允许的二阶正关系表按自身迹归一后，形成包含两极的完整 Bloch 球；$\tau=0$ 时整个表为零，是锥顶点，不能归一。锥的行列式零表示秩一边界，并非历史自比较零。固定商空间的维数可以限制可取得子集；实际原门能取得哪些点还须另外认证。

**白话。**先只看一次小改写的两侧：读数只能向上弯，或者保持平坦。放入第二个实方向，就出现一只碗、一条槽或一张平面。复相位改变两方向怎样交叉，所有这些切片必须相容，才合成完整的正关系锥；不需要预先挑一份单位把它撑起来。

### 4.3 一个缺陷同时测量非实读数与负曲率

为量化误差，本小节才固定非零有限系数空间的欧氏范数 $\|\cdot\|_0$。允许尚未通过候选的复矩阵

$$
Q(z)=z^*Gz,\qquad G=H+iK,\qquad
 H=\frac{G+G^*}{2},\quad K=\frac{G-G^*}{2i}.
$$

记 $b=(-\lambda_{\min}H)_+$、$k=\|K\|_{\rm op}$，并在复平面上定义

$$
\operatorname{dist}_\infty(w,\mathbb R_{\ge0})
 :=\inf_{r\ge0}\max\{|\Re w-r|,|\Im w|\}
 =\max\{(-\Re w)_+,|\Im w|\}.
$$

### 定理 4.2（局部差额的统一精确缺陷）

<a id="thm-c128-defect"></a>

对 $R>0$，令

$$
\varepsilon_R:=\sup_{\|z\|_0\le R}
 \operatorname{dist}_\infty(\Delta_a(z),\mathbb R_{\ge0}).
$$

则它与中心 $a$ 无关，并满足

<a id="eq-c128-unified-defect"></a>

$$
\boxed{\varepsilon_R=2R^2\max\{b,k\}.}
\tag{6}
$$

**证明。**
由 $\Delta_a(z)=2z^*Gz$，负实部和虚部模的上确界分别为 $2R^2b$ 与 $2R^2k$；它们分别由最负方向和虚 Hermitian 部分的最大绝对谱方向取得。上确界与两量的最大值交换，即得结论。

### 定理 4.3（到正矩阵锥的紧距离界）

<a id="thm-c128-psd-distance"></a>

令 $d=\inf_{P\succeq0}\|G-P\|_{\rm op}$，则

<a id="eq-c128-psd-distance"></a>

$$
\max\{b,k\}\le d\le\sqrt{b^2+k^2}
 \le\sqrt2\,\max\{b,k\}.
\tag{7}
$$

上下端点常数均为紧的。

**证明。**
对任意 $P\succeq0$，$G-P$ 的虚 Hermitian 部分仍为 $K$，故其范数至少为 $k$。若 $b>0$，以 $H$ 的最负单位特征向量评价 $\Re(G-P)=H-P$，又得范数至少为 $b$。
令 $r=\sqrt{b^2+k^2}$，取

$$
R_0=\sqrt{r^2I-K^2}\succeq bI,
 \qquad P=H+R_0\succeq0.
$$

由于 $R_0$ 与 $K$ 交换，
$(G-P)^*(G-P)=K^2+R_0^2=r^2I$，故距离至多 $r$。
负实标量或纯虚标量给下界等号；标量 $G=-b+ik$ 给 $d=\sqrt{b^2+k^2}$。再取 $b=k=1$，即知最后的 $\sqrt2$ 常数不能缩小。

这些界仅针对声明系数矩阵到无约束 PSD 锥的距离。按原记录的 Choi 块修复时，构造可以保留这些块，却不自动保留总归一化、原装置实现或同一接线图。因此它不是已完成的仪器修复，也不是未经转换的通道距离界。

### 4.4 有限否定证书与微移的噪声代价

若同一实际过程、同一历史配对和同一个置信事件给出 $\Re\Delta_a(tz)$ 的上界严格小于零，或者给出不含零的 $\Im\Delta_a(tz)$ 区间，就得到候选的有限反例。相关形式历史必须有已标定的实际实现，三项读数也须恢复到同一原尺度，不能各自条件化后相减。

一个方向没有越界，并不控制整个上确界 $\varepsilon_R$。只有确有全域上界 $\varepsilon_R\le\eta$ 时，才有

$$
b,k\le\frac{\eta}{2R^2},\qquad
 d\le\frac{\eta}{\sqrt2\,R^2}.
$$

任意负曲率在任意小的非零尺度都会违反精确候选，但其信号同样按 $t^2$ 缩小。若差额绝对误差为 $\eta$，恢复 $Q(z)=\Delta_a(tz)/(2t^2)$ 后的误差为 $\eta/(2t^2)$。所以去掉大半径的精确双零见证，不等于实际有限噪声下的检测成本处处降低。

**白话。**小范围足以决定这类二次关系的方向，却不保证小信号容易测。两边相反的变化抵消以后，剩下的是平方量；改写缩小十倍，信号就缩小一百倍。真正的有限证据要同时说明读数误差和覆盖范围，不能把一次没看到问题说成所有方向都已通过。

<a id="section-5"></a>

## 5. 从局部条件闭合有限量子理论

<a id="sec-c128-quantum"></a>

主定理已从任意复线性候选中选择 CP。下面逐项恢复通常量子规则；Choi、Kraus、Stinespring 和全效果概率表示有成熟来源，不被改称为本轮首次发现 [7](#ref-watrous2018)、[6](#ref-choi1975)、[5](#ref-stinespring1955)、[8](#ref-busch2003)。矩阵对象的复线性与伴随已经给定，实际完整记录、概率评价、独立联合及时间各有自己的输入。

### 5.1 从正历史到过程表示，单位随后出现

### 定理 5.1（正历史的表示与完整记录）

对通过 C128 的 $\Phi:M_d\to M_m$，零差商 $\mathcal H_\Phi=\mathfrak H_\Phi/\mathcal N_\Phi$ 有正定内积，并有保单位 $*$-表示 $\pi$ 和线性 $V$，满足

$$
\Phi(x)=V^*\pi(x)V.
$$

有限维中存在 $d\times m$ 矩阵 $K_\alpha$，使

$$
\Phi(x)=\sum_\alpha K_\alpha^*xK_\alpha.
$$

若原记录族 $\Phi_j:M_{d_j}\to M_m$ 各自通过候选，再有原完整性 $\sum_j\Phi_j(I)=I$，则

<a id="eq-c128-instrument"></a>

$$
\mathcal T_j(\rho)=\sum_\alpha K_{j\alpha}\rho K_{j\alpha}^*,
 \qquad \sum_{j,\alpha}K_{j\alpha}^*K_{j\alpha}=I_m
\tag{8}
$$

给完整 CP 仪器，各支不增迹，总输出 $\bigoplus_j\mathcal T_j(\rho)$ 保迹。

**证明。**
零集合为根空间，商内积由 $\Gamma$ 良定义。左作用 $L_x(a\otimes u)=xa\otimes u$ 满足
$\Gamma(L_xh,k)=\Gamma(h,L_{x^*}k)$，所以保零差，并在商上给 $\pi(x)[h]=[L_xh]$。
对 $b=(\|x\|^2I-x^*x)^{1/2}$，
$\|x\|^2Q(h)-Q(L_xh)=Q(L_bh)\ge0$，故表示有界。
令 $Vu=[I\otimes u]$，直接评价得到压缩式。

将 $C_\Phi\succeq0$ 分解为 $\sum_\alpha w_\alpha w_\alpha^*$，写
$w_\alpha=\sum_i e_i\otimes K_\alpha^*e_i$。比较第 $(i,k)$ 块得
$\Phi(E_{ik})=\sum_\alpha K_\alpha^*E_{ik}K_\alpha$，复线性给全部输入上的 Kraus 式。零表用空和。
对原记录分别如此分解，完整性给式 [(8)](#eq-c128-instrument) 的第二式。
$E_j=\sum_\alpha K_{j\alpha}^*K_{j\alpha}\ge0$ 且
$I-E_j=\sum_{k\ne j}E_k\ge0$。迹配对给态方向式、各支迹界及总保迹。

完整记录还给一个数学等距

$$
Wu=\bigoplus_j\sum_\alpha K_{j\alpha}u\otimes e_\alpha,
 \qquad W^*W=I.
$$

完整输出只评价原记录的块对角代数；数学扩张中的跨 $j$ 非对角项及环境指标 $\alpha$ 不自动成为原可访问记录。
对同一个归一 $u$，原完整历史 $e=(I_{d_j}\otimes u)_j$ 现在才满足 $Q(e)=1$。于是 C127 的单位不可双零分解作为后果恢复；不再拿它来先证明正性。

### 5.2 密度态、Born、可观测量与不确定关系

### 定义 5.2（完整效果评价）

在一个有限矩阵部门，对全部 $0\le E\le I$ 给同一数值 $p(E)\in[0,1]$，满足 $p(I)=1$，且当 $E+F\le I$ 时
$p(E+F)=p(E)+p(F)$。同一效果在不同完整测试中的赋值相同。

### 定理 5.3（概率与纯态）

每个完整效果评价唯一表示为

<a id="eq-c128-born"></a>

$$
p(E)=\operatorname{Tr}(\rho E),\qquad \rho\ge0,\quad\operatorname{Tr}\rho=1.
\tag{9}
$$

密度态的极点恰为秩一态。归一 $\psi,\varphi$ 对应的纯态与单位秩一投影给
$p(\lvert \varphi\rangle \langle \varphi\rvert )=|\langle\varphi,\psi\rangle|^2$；同一纯态的向量代表恰相差一个整体相位。

**证明。**
有限可加性给有理齐次性，非负性给单调性，以有理数夹逼得实齐次性。
对 $A\ge0$，置 $f(A)=s\,p(A/s)$，其中 $s>0$ 且 $s\ge\|A\|$；齐次性使定义与 $s$ 无关且在正锥可加。
若 $A-B=A'-B'$，则 $A+B'=A'+B$，故 $f(A)-f(B)$ 唯一延伸为 Hermitian 空间上的实线性泛函。有限迹配对给唯一 Hermitian $\rho$；正性及单位评价分别给 $\rho\ge0$、迹一。
秩至少二时可反向微移两个正谱权，产生非平凡凸分解；秩一态的正分解只能支持其同一射线。最后对秩一矩阵直接相乘取迹；相同的一维投影具有相同像空间，归一代表因此仅差相位。

这里采用全效果的 Gleason–Busch 形式，包括二维 [8](#ref-busch2003)。完整效果评价尚未由局部候选独自推出，全部数学效果也不自动实际可访问。
有限锐测量由 $\sum_kP_k=I$ 的正交投影及实结果 $a_k$ 给自伴算符 $A=\sum_ka_kP_k$；反向由有限谱分解得到。其期望值为 $\sum_ka_kp(P_k)=\operatorname{Tr}(\rho A)$。

同一正关系还给通常不确定界。对自伴 $A,B$，置
$A_0=A-\operatorname{Tr}(\rho A)I$、$B_0=B-\operatorname{Tr}(\rho B)I$，在算符历史上用
$\Gamma_\rho(X,Y)=\operatorname{Tr}(\rho X^*Y)$。其二元 Gram 表正半定，故

$$
\operatorname{Var}_\rho(A)\operatorname{Var}_\rho(B)
 \ge |\operatorname{Tr}(\rho A_0B_0)|^2
 \ge\tfrac14|\operatorname{Tr}(\rho[A,B])|^2.
$$

第一步是行列式非负，第二步只保留该复数的虚部。这是给定复矩阵与态评价后的推论，没有由抛物图另行选出具体位置、动量或其交换常数。

### 5.3 读后态、Lüders 与独立复合

式 [(8)](#eq-c128-instrument) 给原支概率
$p_j=\operatorname{Tr}(\rho E_j)=\operatorname{Tr}\mathcal T_j(\rho)$。
只有 $p_j>0$ 时定义 $\rho_j=\mathcal T_j(\rho)/p_j$；零支不产生条件态。
若同空间 CP 支的效果为投影 $P$，当 $P=0$ 时所有 Kraus 项均为零。若 $P\ne0$，再要求保持 $\operatorname{Ran} P$ 内每条纯射线，则每个 Kraus 算符先由效果满足 $K_\alpha(I-P)=0$，再由基向量及两两和的射线保持得到 $K_\alpha=c_\alpha P$。
效果给 $\sum_\alpha|c_\alpha|^2=1$，于是该支为 $\rho\mapsto P\rho P$。仅有结果可重复性不排除结果子空间内的旋转。

若 $M_d,M_m$ 保单位保星地嵌入一份联合代数，两像交换并共同生成，则
$a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 是满的保单位 $*$-同态。
定义域 $M_d\otimes M_m\cong M_{dm}$ 简单：任一非零双边理想经矩阵单位左右相乘包含全部矩阵单位。其核不是全体，故为零，得到张量联合。
这是独立复合接口的结论，不由单事件候选供应新的实际联合对象。

CP 串接与并接的 Kraus 族分别是 $L_\beta K_\alpha$ 和 $K_\alpha\otimes L_\beta$。
完整局部保迹过程满足

$$
\operatorname{Tr}_A[(\mathcal T_A\otimes\operatorname{id})(\rho_{AB})]=\operatorname{Tr}_A\rho_{AB},
$$

因为对另一侧任意效果，伴随作用给 $\mathcal T_A^*(I)\otimes E=I\otimes E$。条件在一个结果上的边缘可以改变，所选结果的信息由原记录承载。

### 5.4 完整可逆、时间与保留接口

### 命题 5.4（同维可逆过程）

同维 CPTP 映射若有 CPTP 左逆，便是酉共轭。

**证明。**
设两者 Kraus 族为 $K_i,L_j$。恒等通道的 Choi 表秩一，所以 $L_jK_i=c_{ji}I$。
对非零 $K_{i_0}$，$\sum_jL_j^*L_j=I$ 保证某个 $L_{j_0}K_{i_0}\ne0$；同维使这两个矩阵可逆。从 $L_{j_0}K_i=c_{j_0i}I$ 得所有 $K_i$ 共线，合并为一个 $K$。保迹给 $K^*K=I$，方阵给酉性。

若另给连续一参数 CPTP 群，有限维中取单位附近的小矩阵对数，群律及连续性给 $\mathcal T_t=e^{t\mathcal L}$。
上述酉性使 $\mathcal L$ 为保星导子。
令 $A=\sum_k\mathcal L(E_{k1})E_{1k}$，导子律给 $[A,E_{ij}]=\mathcal L(E_{ij})$；保星性使 $A+A^*$ 为中心元，故可将 $A$ 换为反自伴部分。于是存在自伴 $H$，满足

$$
\mathcal T_t(\rho)=e^{-itH/\hbar}\rho e^{itH/\hbar},
 \qquad i\hbar\dot\rho=[H,\rho].
$$

选择纯态的相位代表后有 $i\hbar\dot\psi=H\psi$。
一般可微酉传播子也给 $H(t)=i\hbar\,\partial_tU(t,s)U(t,s)^*$；传播律使其不依赖起始时刻 $s$。具体时钟、$H$ 与 $\hbar$ 标定并非本轮候选选出。

| 通常规则 | 推导及尚保留的前件 |
|---|---|
| Hilbert 与叠加 | 局部实序恢复正形式，零差取商；复相干线性继承。 |
| 完全正过程 | 仅复线性单事件，一来源行的完整方向微移条件。 |
| 完整仪器 | 各支 CP 加原完整归一化；实际标签与合法接续仍须供应。 |
| Born 与纯态 | 全效果归一可加评价；正锥极点、迹配对与相位等价。 |
| 可观测量与不确定界 | 有限谱分解；态评价的二元 Gram 正性。 |
| 投影与张量 | 逐射线保持；独立交换且共同生成的联合接口。 |
| 酉与时间 | 同维 CPTP 逆；连续群或可微传播，另有物理时钟。 |

**白话。**先让每段局部变化自己的余量真实且不负，就能把零差合并，得到内积和完全正过程。原记录随后合成一份一，才成为完整仪器；一致的效果评价给概率，完整可逆给酉作用，时钟再把这些作用写成时间方程。每一层都保留自己的来源，当前撤掉的是先验保伴随和先验正单位。

<a id="section-6"></a>

## 6. 观察者内生与本轮仍有的前件

<a id="sec-c128-observers"></a>

### 6.1 中心无关，不等于观察域已经对应

$\Delta_a(z)=2Q(z)$ 表明，在同一已声明比较域内，起点 $a$ 不影响合法方向或 CP 类。不同观察者可以从不同历史出发；只要他们已经认证了同一个关系域，就不需要额外挑一个优先观察者或宇宙外的单位参照。
两侧尚未建立对应时，这个恒等式不会自动告诉任何人全部交集。共同子结构的内部证据可以认证一部分重叠；完整交集还需要完整对应或成员判定，逻辑上不必要求一方包含另一方全部结构。

### 命题 6.1（相容窗口的正关系拼接）

若历史窗口通过指定的单射复线性嵌入形成有向系统，各半双线性比较在嵌入下相容，每个窗口在某个中心满足 C128，则代数直接极限有正半定 Hermitian 比较，各零差商等距嵌入同一个 Hilbert 完成空间。各窗口不必先共享正单位。

**证明。**
有限多个历史进入共同更大窗口；在该窗口评价 $\Gamma$，相容性保证与窗口选择无关。主定理使各自比较为实且非负，全局零空间与每个窗口的交就是其原零空间，因此商映射等距。对代数并集商取完成即得结论。

有向嵌入与交叉比较是前件。孤立边缘数据不唯一决定它们；共享完成空间也不自动选择唯一整体态 $\omega$、证明其为纯态或证明实际门序列沿时间收敛。那些结论需要相容准备、足够分离的评价及具体收敛估计。例如反复应用合法酉门 $X=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$，会使 $\lvert 0\rangle ,\lvert 1\rangle $ 交替；每一步通过候选，序列却不收敛。

### 6.2 两份历史不是免费复制的物理态

$a+tz$ 与 $a-tz$ 首先是原相干域内的形式历史。该二元检验没有供应未知态克隆器，也不保证相应两种准备或相位控制实际可调用。原理能否作用于自然界，需要把这些关系接到同一原装置的可实现读数，并保留原尺度、失败及记录身份。

固定归一 $\lvert o\rangle $，自指起点可用数学重置通道 $\rho\mapsto\operatorname{Tr}(\rho)\lvert o\rangle \langle o\rvert $ 表示局部回到固定态；其等距扩张 $\psi\mapsto\lvert o\rangle \otimes\psi$ 将输入留在环境因子。同维封闭酉门不能将不同正交输入消成同一射线。内容与地址的对应还需编码语义，候选未将其从重置式推出。

### 6.3 定义相容性不等于没有前提

本轮只在同一个 $\Omega$ 内部谈已有历史、相干组合和读数差；中心也来自内部。因而候选可以锁定成这些定义之间的兼容条件。
但实序、复标量、半双线性、全部声明方向及原矩阵对象仍为数学输入。实双线性形式的反对称部分在 $Q(x)$ 中不可见；所以本轮从自比较恢复整个 Hermitian 形式的步骤，不能无条件搬到实域，也不能恢复另名的有向关系。

正单位与总归一化没有被宣布不存在。它们只不再是*选择 CP*的前件；完整概率层仍需原完整记录来供应。候选本身允许零过程和放大 CP 过程，因此不推出单位、非平凡性、概率或迹不增。
本轮也未从无结构逻辑唯一选择复量子体系，未选择时空、量子场、标准模型粒子谱或物理作用量。数学证明与实际原生实现的供应须逐项对应，不能以“全都在 $\Omega$ 中”代替对应证明。

**白话。**起点可以留在观察者自己身上。只要比较域相同，无论从哪里做相同的对向微移，留下的都是那份变化自身的关系；这个结论不要求先拿到全局的一。但不知道的交叉关系仍然未知，数学上写得出的历史也未必已有装置可执行。内生的意思，是每一步都给出整体内部的来源和约束，不是把没有证明的桥直接当作已经存在。

<a id="section-7"></a>

## 7. 本轮唯一候选与完整白话

<a id="sec-c128-final"></a>

在一个已给复半双线性历史域中，固定任意中心 $a$。本轮唯一新增条件为：对每个已声明方向 $z$ 及每个 $\varepsilon>0$，存在实 $t$，使

$$
0<|t|<\varepsilon,
 \qquad Q(a+tz)+Q(a-tz)-2Q(a)\in\mathbb R_{\ge0}.
$$

其完整数学闭环是

$$
\text{一中心的方向局部实序}
 \Longleftrightarrow\text{Hermitian 正关系}
 \Longleftrightarrow\text{相应单事件完全正}.
$$

最后一个等价使用明确给出的矩阵历史接口，不适用于任意未定义的过程。
实序比较承载了实性与非负性；减少独立前件，不等于不再使用这些信息。有限噪声下的成本也没有因此普遍下降。
本稿给出纸笔证明与删除反例，未将 C128 进行 Lean 形式化或物理实验，不主张文献首创、全球最小公理或已经确认的新自然定律。

### 本轮完整白话

**白话。**观察者不用先知道整个世界有多大，也不用先拿到一份全局单位。先留住当前这段历史，把它朝一个方向挪一点，同时把另一份朝反方向挪同样多；两份的平均内容没有变，线性变化也正好抵消。现在只要求：留下的合计余量是真实而且非负的。因为相干关系是二次的，这份小余量正好是那个方向自身的比较量乘上位移的平方。哪个方向藏着负弯曲，任意小的分岔都会向下；比较若有不相容的虚部，余量就会偏离实读出轴。排掉这些失败，关系便成为正的 Hermitian 关系；平的方向是真正零差，把它合并后就有内积，过程也必须与全部相干方向一起保持正性。两段历史自己的非零总量随后可以作归一化，画出三维球；完整成功、失败记录再供应概率的一份一。不同观察者可以从不同地方做这个检验，但只有有来源的共同关系才能拼接。所有历史、参照和记录仍在整体内部，本轮只把要求再缩小一步：中心不变的两份微移，留下的余量必须真实且不负。

<a id="references"></a>

## 参考文献

<a id="ref-repo-c128-c117"></a>

### [1]

The Omega Institute, *AURIC Common Source Self Reference and Observer Sequences C117*，第 17–24 节。
[固定快照全文](https://github.com/the-omega-institute/trureturing/blob/1764a0c7f33be6acf6dcaf4ad4007da021469ae9/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md)；
[PR #26420 合入](https://github.com/the-omega-institute/trureturing/commit/1764a0c7f33be6acf6dcaf4ad4007da021469ae9)，2026-11-04 08:03:22 UTC。
相对前轮新增第 17–24 节共 738 行，HEAD 本身追加第 21–24 节共 415 行。本文核读其普通数学证明与明确前件，不将这些文稿结论称为新构建的 Lean 定理。

<a id="ref-repo-c128-refinement"></a>

### [2]

The Omega Institute，规范正细化的五文件链中的四个正向文件：
[PositiveRefinementRigidity](https://github.com/the-omega-institute/trureturing/blob/1764a0c7f33be6acf6dcaf4ad4007da021469ae9/D5/S3/Quantum/Reduction/PositiveRefinementRigidity.lean)；
[PositiveRefinementCorner](https://github.com/the-omega-institute/trureturing/blob/1764a0c7f33be6acf6dcaf4ad4007da021469ae9/D5/S3/Quantum/Reduction/PositiveRefinementCorner.lean)；
[SingularPositiveRefinement](https://github.com/the-omega-institute/trureturing/blob/1764a0c7f33be6acf6dcaf4ad4007da021469ae9/D5/S3/Quantum/Reduction/SingularPositiveRefinement.lean)；
[CanonicalPositiveRefinement](https://github.com/the-omega-institute/trureturing/blob/1764a0c7f33be6acf6dcaf4ad4007da021469ae9/D5/S3/Quantum/Reduction/CanonicalPositiveRefinement.lean)。
核读全部证明体，含零与奇异支持、原块标量及全部有限放大。前件明确包含细支普通正性和逐块规范单滤片粗和；未对所有上游依赖重审或运行 Lean。

<a id="ref-repo-c128-refutation"></a>

### [3]

The Omega Institute, *PositiveCoarseRefinementRefutation*。
[固定快照的完整反证文件](https://github.com/the-omega-institute/trureturing/blob/1764a0c7f33be6acf6dcaf4ad4007da021469ae9/D5/S3/Quantum/Reduction/PositiveCoarseRefinementRefutation.lean)。
两支效果均为 $I/2$，每支正，粗和 CP；转置半支仍非 CP。本文以原公式重算局部负曲率，未由源码中的 `#print axioms` 命令推断本轮有实际编译输出。

<a id="ref-repo-c128-directed"></a>

### [4]

The Omega Institute, *AURIC Native Reciprocal Comparison and Finite Endpoint Quantum C123*，新增第 21–40 节中的第 35–40 节。
[固定全文](https://github.com/the-omega-institute/trureturing/blob/1764a0c7f33be6acf6dcaf4ad4007da021469ae9/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)。
仓内“C127：Z/II/S”与本对话 C127 名称不同。本文使用完整有向关系反族及其平方/交换子区别；未把零正配对定理的全背景义务删掉，也未认证完整旧卷。

<a id="ref-stinespring1955"></a>

### [5]

W. F. Stinespring, ``Positive functions on $C^*$-algebras'',
*Proceedings of the American Mathematical Society* **6**(2), 211–216 (1955).
[doi:10.1090/S0002-9939-1955-0069403-4](https://doi.org/10.1090/S0002-9939-1955-0069403-4)。
本稿对有限历史商与表示给直接证明；数学环境表示与实际原记录供应分别说明。

<a id="ref-choi1975"></a>

### [6]

M.-D. Choi, “Completely positive linear maps on complex matrices”,
*Linear Algebra and its Applications* **10**(3), 285–290 (1975).
[doi:10.1016/0024-3795(75)90075-0](https://doi.org/10.1016/0024-3795(75)90075-0)。
有限 Choi 判据的原始出处；本稿由来源行及正块矩阵分解直接证明所需过程等价。

<a id="ref-watrous2018"></a>

### [7]

J. Watrous, *The Theory of Quantum Information*, Cambridge University Press (2018).
[作者公开电子版第 2 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，Theorem 2.22。
有限 Choi、Kraus、Stinespring 表示及通常量子过程接口。

<a id="ref-busch2003"></a>

### [8]

P. Busch, “Quantum states and generalized observables: a simple proof of Gleason's theorem”,
*Physical Review Letters* **91**, 120403 (2003).
[arXiv:quant-ph/9909073v3](https://arxiv.org/pdf/quant-ph/9909073)。
完整效果可加概率的 Born 表示，包括二维；概率评价条件仍为明确输入。
