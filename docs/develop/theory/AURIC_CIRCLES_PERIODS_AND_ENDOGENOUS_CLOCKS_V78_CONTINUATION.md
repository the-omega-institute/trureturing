# 圆、周期与内生时钟

从二元相位的拼接，到整体量子关系的返回

AURIC v78 后续研究：定义、定理与证明

研究续稿

2026 年 11 月 2 日

## 摘要

圆给出闭合的相位；周期来自同一内部演化把所保留的关系同时带回原位。本稿把这句话分解成可证明的相容关系：投影速度在相同读出的来源上常值，给自治圆流；饱和二元相位的路径乘积相容，给整体正态及可积频率差；全部可见频率同时闭合，给观察者的周期群。

在项目原生双壁控制中，固定权重 $p\in(0,1)$ 后，底部二态球的命令参数周期为 $4\pi$，而包含内部相干参考的当前射线，恰在 $p=a/q$ 为最简有理数时具有最小周期 $4\pi q$。无理权重没有有限精确返回，却有可证明的近回返。该结果把前轮历史圆、椭圆投影及水平相位，与本轮的周期分类直接连接。

所有定理均列出前件。这里的内生化，是把时钟、参考、记录、组合及读出放进同一声明的整体 $\Omega$，再证明它们之间哪些约束可以互相推出；定义本身不会消除尚未推出的选择条件。本文给解析证明及逐段白话图景，未进行数值枚举，也未把新增结果宣称为已形式化的量子唯一起源定理。

## 目录

- [1. 接续位置：本轮在 v78 上增加什么](#section-1)
- [2. 圆何时必然给出周期：把自治写成二元相容](#section-2)
- [3. 圆之间也有关系：两条路径的相位必须拼得起来](#section-3)
- [4. 从相位圆的组合律，积分出频率差与生成元](#section-4)
- [5. 精确周期的二元残差：所有相关圆同时闭合](#section-5)
- [6. 把周期锁成定义：观察者的周期群与完整续接商](#section-6)
- [7. 哪些相位真的被看见：可见频率的严格判据](#section-7)
- [8. 项目原生计算：同一条圆怎样产生倍周期或无理近返](#section-8)
- [9. 一般有限谱的近回返：没有精确周期仍能共同回近](#section-9)
- [10. 内生时钟与历史：表盘可以重复，账本继续增长](#section-10)
- [11. 从公理到定义约束：本轮可以压缩到什么程度](#section-11)
- [12. 完整白话图景：把本轮结果连成一幅画](#section-12)

<a id="section-1"></a>

## 1. 接续位置：本轮在 v78 上增加什么

### 1.1 已核对的版本与已有基础

本轮固定读取的公开提交为

`3ca0ba6c579f2685c52d95a4a6b8a07d037382c9`。

该快照已包含 V73、V74 及 V78 正文。V78 开头将其定位为 AI continuation 原稿的 Markdown 转换，并未宣称为 Lean 数学真值。本文沿用这个研究稿定位[1](#ref-repo-v78)。

| 已有来源 | 已有结果 | 本轮接续点 |
| --- | --- | --- |
| V73 §3 | 三态 Gram 行列式、闭路相位与全图拼接 | 将饱和相位特例压成两个路径值的三维残差，再积分频率差 |
| V74 §3、V78 §12 | 平移不变正核重建自治酉群；完整保核历史重建酉表示 | 将有限相位表示、实际可见频率与周期群连起来 |
| Phase §§8--9 | 当前射线的环面坐标、原生双壁水平相位与接续 | 直接求固定纤维的最小精确周期及近回返残差 |
| OMEGA §§20--21 | 固定等待的无理谱比障碍；独立单项控制的周期 | 用公共频率群统一说明局部闭合与整体不同步 |
| History §§144、148；Clock §3 | 周期读出与追加档案并存；离散周期的未来行为商 | 连续闭周期群及完整实参数续接商 |

因此，“圆与历史螺旋”“几何闭环不等于完整相位返回”都是项目已有基础。本轮新增的是这些结构之间的组合推论，尤其是原生固定纤维的有理／无理周期分类；不将标准谱论或量子回归认领为一般数学上的首创。

### 1.2 三个需要分开的对象

全文用 $\Omega$ 表示整体内部结构，用 $\Omega_0$ 表示一个表示中的单位根向量。一个演化参数 $t$ 是内部接续的标签；只有指定实际时钟标定后，才将其数值解释为秒。$\hbar$ 用于把相位变化率 $\nu$ 转换为物理能量 $E=\hbar\nu$。

必须分别说明：哪些对象作为状态被保留；哪些读口可用；哪些续接合法。当前射线、指定相位提升、相干参考和完整追加档案，保留的信息不同，所以它们的周期可以不同。这些都可属于同一 $\Omega$，并不需要一个外部观察者。

**白话图景。**把整体想成一座内部相连的钟表：有表盘，有带动表盘的齿轮，有比较两只表针的参考，也有记录圈数的账本。表针绕回来了，能否说“整个状态重复”，取决于所说的状态是否还包括齿轮相位和账本。

<a id="section-2"></a>

## 2. 圆何时必然给出周期：把自治写成二元相容

### 2.1 相同圆读出，必须承接相同继续速度

<a id="statement-2-1"></a>

#### 定义 2.1（内部投影与速度下降）

设完整内部状态空间为光滑流形 $M$，实际向量场为 $X$，圆读口为光滑满射下沉 $\pi:M\to S^1$。称该读口承接自治运动，是指存在圆上的光滑向量场 $Y$，使

$$
D\pi_xX(x)=Y(\pi(x)).
$$

<a id="statement-2-2"></a>

#### 定理 2.2（自治的纤维相容判据）

上述 $Y$ 存在，当且仅当

$$
\boxed{\pi(x)=\pi(x')\ \Longrightarrow\
D\pi_xX(x)=D\pi_{x'}X(x').}
\tag{2.1}
$$

**证明。**

必要性由右侧共同等于 $Y(\pi(x))$ 得到。反向，按共同值定义 $Y(\pi(x))$，条件保证与代表元无关。满射下沉有局部光滑截面；沿截面表示这个共同值，得到 $Y$ 光滑。

□

撤去此条件，失败落在两个来源 $x,x'$：圆读出相同，接下来却有不同的投影速度。这正是“当前概念遗漏了会影响后续的历史”。两速度属于同一个切空间，设为 $a,b$，以其内部度量及 $s=\left\lVert a\right\rVert ^2+\left\lVert b\right\rVert ^2>0$ 定义

$$
X_{ab}=\frac{2\langle a,b\rangle }{s},\qquad Y_{ab}=0,\qquad
Z_{ab}=\frac{\left\lVert a\right\rVert ^2-\left\lVert b\right\rVert ^2}{s}.
$$

则 $X_{ab}^2+Y_{ab}^2+Z_{ab}^2\le1$，且

$$
\left\lVert a-b\right\rVert ^2=s(1-X_{ab}).
\tag{2.2}
$$

若 $s=0$，两速度都为零，无需归一化。这个三维读出是局部关系诊断，并未把整个状态空间压成三维。

**白话图景。**若两段历史都显示表针停在十二点，但一段历史使它接着慢走，另一段使它接着快走，那么“十二点”还不是完整的运动状态。把决定速度的内部关系补进去，继续走法才能成为当前状态的单值函数。

### 2.2 非零自治圆流的严格周期

<a id="statement-2-3"></a>

#### 定理 2.3（内生均匀相位）

设圆上的自治运动写成

$$
\dot\theta=v(\theta),\qquad v\in C^1,\qquad
v(\theta+2\pi)=v(\theta)>0.
$$

则所有轨道的最小正周期相同：

$$
\boxed{T=\int_0^{2\pi}\frac{d\theta}{v(\theta)}.}
\tag{2.3}
$$

在角度的实提升上定义

$$
\tau(\theta)=\int_{\theta_*}^{\theta}\frac{du}{v(u)},\qquad
\varphi(\theta)=\frac{2\pi}{T}\tau(\theta)\pmod{2\pi}.
$$

则 $\varphi$ 是圆的保向微分同胚，且

$$
\boxed{\dot\varphi=\frac{2\pi}{T}.}
\tag{2.4}
$$

**证明。**

紧致性使 $v$ 有严格正下界，故 $0<T<\infty$。沿解有
$d\tau/dt=\dot\theta/v(\theta)=1$，且
$\tau(\theta+2\pi)=\tau(\theta)+T$。因此经过 $T$，实提升恰增加 $2\pi$；更短正时间不能完成整圈。$\varphi$ 的导数处处为正，且绕数为一，故给圆的微分同胚及所述均匀速度。

□

任意处处非零的连续圆向量场都有固定方向，必要时换定向即可用此定理。时间形式 $\alpha=d\theta/v(\theta)$ 由 $\alpha(X)=1$ 决定；积分 $\oint\alpha=T$ 不依赖角坐标。整体缩放 $X\mapsto aX$，$a>0$，使周期变为 $T/a$。所以圆的形状不单独确定绝对时间尺度。

$\tau$ 定义在实提升上，不能当成圆上单值的实函数；圆上的单值对象是 $\tau\bmod T$。保留绕数需要额外的内部记录。

**白话图景。**同一个圆点每次都规定同一种走法，沿途也没有停住，一圈就必然能走完，而且每圈花同样时间。把路上快慢重新标成均匀进度，就得到内部相位钟；它的刻度来自已有的变化率。

### 2.3 反推：删掉哪条关系，周期就在哪一步失效

取时间尺度 $\tau_0>0$。路径

$$
z(t)=e^{i(t/\tau_0)^2},\qquad t>0
$$

反复绕同一个圆，但没有固定 $T>0$ 使 $z(t+T)=z(t)$ 对所有 $t>0$ 成立。否则
$(2tT+T^2)/\tau_0^2$ 连续地落在 $2\pi\mathbb Z$，必须为常数，与其非零导数矛盾。这里同一圆点的后续速度不同。

另一方面，自治方程

$$
\dot\theta=\frac{1-\cos\theta}{\tau_0},\qquad
\theta(0)=\pi
$$

有解 $\theta(t)=\pi+2\arctan(t/\tau_0)$。它渐近趋向 $2\pi$，永远不在有限时间到达。这里速度存在零点。

**白话图景。**第一种失败像越转越快的表针：位置重复，走法没有重复。第二种失败像最后一段越走越慢：圆已经画好，却永远走不完。自治相容与不停顿，分别排除这两种具体失败。

<a id="section-3"></a>

## 3. 圆之间也有关系：两条路径的相位必须拼得起来

### 3.1 从合法二元圆到整体正态

<a id="statement-3-1"></a>

#### 定义 3.1（饱和二元相位表）

固定有限个权重 $p_j>0$，$\sum_jp_j=1$。设

$$
\zeta_{jj}=1,\quad \zeta_{kj}=\overline{\zeta_{jk}},
\quad |\zeta_{jk}|=1,\qquad
\Gamma_{jk}=\sqrt{p_jp_k}\,\zeta_{jk}.
\tag{3.1}
$$

每个二元主块都是半正定秩一矩阵。“饱和”指相干幅值已经达到 $\sqrt{p_jp_k}$。

<a id="statement-3-2"></a>

#### 定理 3.2（二元路径相容与整体正性的等价）

对不同指标 $i,j,k$，

$$
\boxed{
\det\Gamma_{\{i,j,k\}}
=-p_ip_jp_k\,
|\zeta_{ij}\zeta_{jk}-\zeta_{ik}|^2.}
\tag{3.2}
$$

在定义的饱和类中，

$$
\boxed{
\Gamma\succeq0
\iff
\zeta_{ij}\zeta_{jk}=\zeta_{ik}
\quad\text{对所有三角成立}.}
\tag{3.3}
$$

满足条件时 $\Gamma$ 必为秩一态。

**证明。**

提出三个权重后，三阶行列式为
$p_ip_jp_k[1-3+2\operatorname{Re} (\zeta_{ij}\zeta_{jk}\overline{\zeta_{ik}})]$。
两条路径值模长都为一，故此式等于 (3.2)。整体正性要求每个主子式非负，因而残差必须为零。

反向，取锚点 $1$，令 $x_j=\zeta_{j1}$。相容条件给
$\zeta_{jk}=x_j\overline{x_k}$。于是以
$v_j=\sqrt{p_j}x_j$ 定义向量，便有 $\Gamma=vv^\dagger$，且
$\left\lVert v\right\rVert =1$。一、二个指标的退化情形同样由此锚点分解成立。

□

式 (3.2) 是 V73 §3 的 Gram／闭路相位结构在饱和情形下的特例[3](#ref-repo-v73)。一般非饱和矩阵不能据此声称“三阶检查足够保证任意整体正性”。

### 3.2 被比较的两个元，是同源同靶的两条路径

令

$$
a=\zeta_{ij}\zeta_{jk},\qquad b=\zeta_{ik}.
$$

$a$ 是经过中间节点的路径值，$b$ 是直达路径值；它们都是内部关系的复合。归一三维坐标为

$$
(X,Y,Z)=
(\operatorname{Re}(\overline a b),
 \operatorname{Im}(\overline a b),0)\in S^2.
$$

于是

$$
\boxed{|a-b|^2=2(1-X),\qquad
\det\Gamma_{\{i,j,k\}}=-2p_ip_jp_k(1-X).}
\tag{3.4}
$$

这正按“找出两个元，再看所属更大结构”的方法工作：二元比较针对两条路径，中间节点仍保留在路径的定义里；更大结构是全体相位表的正性及组合相容。

**白话图景。**每两根箭头之间都可以画一只相位圆，但这些圆不能各转各的。先从甲比较到乙，再从乙比较到丙，得到的相位，必须等于直接比较甲和丙。所检查的是两条到达同一终点的关系路径；三维球上的偏差，精确记录这两条路径有没有对上。

### 3.3 撤去路径相容：每对都合法，整体出现负见证

取三个等权重 $p_j=1/3$，并指定

$$
\zeta_{12}(t)=\zeta_{23}(t)=e^{-i\omega_0t},\qquad
\zeta_{13}(t)=e^{-3i\omega_0t},\quad\omega_0>0.
$$

在 $t=\pi/\omega_0$，得到候选

$$
\Gamma=\frac13
\begin{pmatrix}1&-1&-1\\-1&1&-1\\-1&-1&1\end{pmatrix}.
\tag{3.5}
$$

每个二元主块半正定，按其迹归一后是合法纯态；但
$v=(1,1,1)/\sqrt3$ 满足 $\Gamma v=-v/3$。在其正交补上，
$\Gamma$ 为 $2I/3$，所以整体不是正态。

若强把它作为态使用，二元报告 $\{P_v,I-P_v\}$ 就给
$(-1/3,4/3)$，相应 Bloch 纵坐标为 $-5/3$，落在关系球外。
这表示候选表不相容，并非物理测量产生了负概率。

**白话图景。**三只局部圆都没有画坏，坏在它们对同一整体给出了互相矛盾的相位。把冲突送到一个“是／否”读口，便出现负权重。正性在这里不是孤立口号：它禁止同一关系走两条路却得到互不相容的答案。

<a id="section-4"></a>

## 4. 从相位圆的组合律，积分出频率差与生成元

<a id="statement-4-1"></a>

#### 定义 4.1（自治相位关系）

对每一对指标，要求 $\zeta_{jk}:\mathbb R \to U(1)$ 连续，且

$$
\zeta_{jk}(t+s)=\zeta_{jk}(t)\zeta_{jk}(s).
\tag{4.1}
$$

它表示同一种内部相位续接分两段完成，与合成一段完成相容。

<a id="statement-4-2"></a>

#### 定理 4.2（相位组合与频率可积性）

连续条件 (4.1) 给实常数 $\omega_{jk}$，使
$\zeta_{jk}(t)=e^{-i\omega_{jk}t}$。全时刻三角相容等价于

$$
\omega_{ij}+\omega_{jk}=\omega_{ik}.
\tag{4.2}
$$

这又等价于存在实数 $\nu_j$，使

$$
\boxed{\omega_{jk}=\nu_j-\nu_k.}
\tag{4.3}
$$

因此整个相位表有实现

$$
\boxed{
\psi(t)=\sum_j\sqrt{p_j}\,e^{-i\nu_jt}|j\rangle,\qquad
H=\hbar\operatorname{diag} (\nu_j),\qquad
i\hbar\dot\psi=H\psi.}
\tag{4.4}
$$

**证明。**

连续同态在零点附近可选连续辐角 $a(t)$，且 $a(0)=0$。缩小邻域后，组合律使
$a(t+s)-a(t)-a(s)$ 是连续的 $2\pi$ 整数倍，零点处为零，故局部为零。
局部连续可加函数由有理逼近为线性函数；再用
$\zeta(t)=\zeta(t/n)^n$ 扩展到全部实数，得到指数形式。

三角条件变成
$e^{-i(\omega_{ij}+\omega_{jk}-\omega_{ik})t}=1$ 对所有实 $t$ 成立，故括号内为零。取 $\nu_j=\omega_{j1}$，由 (4.2) 得 (4.3)；反向相减即可。构造 (4.4)，其外积恰为 $\Gamma(t)$，逐项求导得到方程。

□

所有 $\nu_j$ 共同加上常数，不改变任何差，所以仅由关系相位确定的
$H$ 只确定到 $H+cI$。指定相干参考后，可以把原本共同的相位变成相对相位；这个参考也必须属于 $\Omega$。

此处前件是固定权重、有限正交模式及连续自治相位组。它重建的是一个可交换的一参数演化类；任意时变、非交换门序列还需要 V78 的完整核与共同标架条件。V74 §3 已从平移不变正核给出更一般的有限维自治重建[2](#ref-repo-v74)、[1](#ref-repo-v78)。

**白话图景。**先给每一对关系一只连续转动的相位圆，再要求相位能沿路径拼接，就发现各对转速不能任意指定：它们必须来自每个分量自身转速之差。把这些分量放在同一正交坐标里，薛定谔形式随之出现。生成元记录的，就是这些彼此相容的内部转速。

<a id="section-5"></a>

## 5. 精确周期的二元残差：所有相关圆同时闭合

### 5.1 固定有限谱与同根历史核

设实际自治演化为 $U_t=e^{-iHt/\hbar}$，$H$ 有限维自伴。以下将 $H$
限制到根 $\Omega_0$ 的活动谱子空间，保留不同活动谱值：

$$
H=\sum_jE_jP_j,\quad
p_j=\left\lVert P_j\Omega_0\right\rVert ^2>0,\quad
\phi_j=\frac{P_j\Omega_0}{\sqrt{p_j}},\quad
\nu_j=E_j/\hbar.
$$

于是

$$
\psi(t)=\sum_{j=1}^r\sqrt{p_j}e^{-i\nu_jt}\phi_j,\qquad
K(T)=\langle \Omega_0,U_T\Omega_0\rangle =\sum_jp_je^{-i\nu_jT}.
\tag{5.1}
$$

谱简并已吸收入 $P_j$；$r$ 计活动的不同谱值。

<a id="statement-5-1"></a>

#### 定理 5.1（射线返回、向量返回及无相消残差）

对 $T>0$，

$$
\boxed{
[U_T\Omega_0]=[\Omega_0]
\iff(\nu_j-\nu_k)T\in2\pi\mathbb Z \quad\forall j,k,}
\tag{5.2}
$$

$$
\boxed{
U_T\Omega_0=\Omega_0
\iff\nu_jT\in2\pi\mathbb Z \quad\forall j.}
\tag{5.3}
$$

两者分别等价于下列非负残差为零：

<a id="eq-return-residual"></a>

$$
\mathcal R(T):=1-|K(T)|^2
=4\sum_{j<k}p_jp_k
\sin^2\frac{(\nu_j-\nu_k)T}{2},\tag{5.4}
$$

<a id="eq-vector-residual"></a>

$$
\left\lVert U_T\Omega_0-\Omega_0\right\rVert ^2
=4\sum_jp_j\sin^2\frac{\nu_jT}{2}.
\tag{5.5}
$$

**证明。**

比较正交分量：射线返回要求所有 $e^{-i\nu_jT}$ 等于同一个相位；向量返回要求它们全等于一。展开
$|K|^2=\sum_jp_j^2+2\sum_{j<k}p_jp_k\cos((\nu_j-\nu_k)T)$，
再用 $\sum_jp_j=1$，得到第一残差；直接展开向量差得到第二残差。所有活动权重严格正，故任一未闭合谱对都会产生严格正项。由群律，初态返回也保证整个轨迹在相同 $T$ 下返回。

□

只比较两个内部历史 $a=\Omega_0$、$b=U_T\Omega_0$，可取三维坐标

$$
(X,Y,Z)=(\operatorname{Re}K(T),\operatorname{Im}K(T),0).
$$

此时

$$
1-X^2-Y^2=\mathcal R(T),\qquad
\left\lVert b-a\right\rVert ^2=2(1-X).
\tag{5.6}
$$

射线返回意味着到达边界圆；指定向量返回还要求到达 $(1,0,0)$。这里边界上的不同相位只有在已保留相干比较接口时才可进一步区分，数学坐标不自动授权一个实际门。

**白话图景。**每一个相位差像一对齿轮的相对刻度。完整射线返回，要求所有相关刻度同时对齐；任何一对没对齐，返回残差就严格大于零。把初始历史和返回候选作为两个元比较，整个问题又落回一个三维关系球。

### 5.2 每个圆合法，但没有公共整圈

进一步把第 $j,k$ 个活动谱分量单独归一，其三维二态坐标为

$$
\boxed{
(X_{jk},Y_{jk},Z_{jk})
=\left(
A_{jk}\cos(\omega_{jk}t),
A_{jk}\sin(\omega_{jk}t),
\frac{p_j-p_k}{p_j+p_k}
\right),\quad
A_{jk}=\frac{2\sqrt{p_jp_k}}{p_j+p_k}.}
\tag{5.7}
$$

这里 $\omega_{jk}=\nu_j-\nu_k$。有
$A_{jk}^2+Z_{jk}^2=1$，因此这是球上固定高度的圆：
两权重相等时为大圆，不等时为小圆；频率为零时退化为静止点。
这个公式说明每对关系的三维表示，不限制整体只能有两个谱分量。

若所有活动谱差生成的整数加法群是 $\omega_*\mathbb Z$，其中 $\omega_*>0$，最小射线周期为 $2\pi/\omega_*$。若只有一个活动谱值，射线静止，全部实数都是周期，没有最小正周期。

取

$$
H=\hbar\omega_0\operatorname{diag} (0,1,\sqrt2),\qquad
\Omega_0=(1,1,1)/\sqrt3.
\tag{5.8}
$$

它由同一个 $H$ 生成，所以全部三角关系相容，各二元相位都沿圆运动。
若 $T>0$ 为射线周期，则
$\omega_0T=2\pi m$、$\sqrt2\,\omega_0T=2\pi n$。
$m\ne0$，从而 $\sqrt2=n/m$，矛盾。

这与第 3 节负矩阵反例不同：第 3 节根本不能拼成正态；此例是合法整体，但频率不公度。因此**相位可积性与周期公度性是两条不同约束**。

项目 OMEGA §20 已有原生实例：固定等待生成元的谱为
$0,\pm\omega_+,\pm\omega_-$，且
$\omega_\pm^2=(5\pm\sqrt{17})/2$，频率比无理。§21 另行提供的单项控制却可各有 $2\pi$ 周期[5](#ref-repo-omega)。单项旋转周期不强制固定总生成元具有公共周期。

**白话图景。**能拼成同一整体，只说明各只圆的相位没有矛盾。要让整个装置重复，还要这些圆能在同一时刻对齐。如果两只圆的转速比是不公度的，每只都能单独转完一圈，整体却没有一次有限的完全同步。

<a id="section-6"></a>

## 6. 把周期锁成定义：观察者的周期群与完整续接商

### 6.1 三个可能的精确周期结构

<a id="statement-6-1"></a>

#### 定义 6.1（读出周期群）

给定连续读出族 $f_m:\mathbb R \to\mathbb R$ 或 $\mathbb C$，定义

$$
P_{\mathcal M}=
\{T\in\mathbb R :\ f_m(t+T)=f_m(t)\quad
\forall t\in\mathbb R ,\ \forall m\in\mathcal M\}.
\tag{6.1}
$$

<a id="statement-6-2"></a>

#### 定理 6.2（闭周期群分类）

$P_{\mathcal M}$ 是闭加法子群，故恰为以下三类之一：

$$
\boxed{\mathbb R ,\qquad T_0\mathbb Z \ (T_0>0),\qquad \{0\}.}
\tag{6.2}
$$

它们分别对应所有读出静止、有最小正周期、没有非零精确周期。

**证明。**

零平移保持读出，两个保持平移可相加，也可取逆，所以是子群。
对每个 $m,t$，等式 $f_m(t+T)=f_m(t)$ 的解集闭；对这些闭集取交，仍闭。

若子群含任意小的正数，则任意实数都可被这些正数的整数倍逼近，闭性迫使子群为 $\mathbb R$。否则其正元有严格正下确界 $T_0$；用逼近下确界的序列与闭性得 $T_0$ 在群内。任意正元除以 $T_0$ 的余数也在群内，且小于 $T_0$，故余数为零。若没有正元，子群只能为 $\{0\}$。

□

<a id="statement-6-3"></a>

#### 定义 6.3（完整实参数续接不可区分）

定义

$$
s\sim_{\mathcal M}t
\iff f_m(s+u)=f_m(t+u)
\quad\forall u\in\mathbb R ,\ \forall m.
\tag{6.3}
$$

<a id="statement-6-4"></a>

#### 推论 6.4（周期由完整行为商内生）

$$
\boxed{
s\sim_{\mathcal M}t
\iff t-s\in P_{\mathcal M}.}
\tag{6.4}
$$

因此参数平移群的商 $\mathbb R /P_{\mathcal M}$ 分别为点、圆、直线。

**证明。**

令 $v=s+u$；当 $u$ 取遍实数时，$v$ 也取遍实数，定义恰变成差值 $t-s$ 是共同周期。

□

此处明确要求全部实参数续接。只要求 $u\ge0$，对一般连续信号并不推出 (6.4)：一个在 $t\ge0$ 恒零、在负时间非恒定的信号，可以把所有非负时刻判为未来等价，却没有全局周期。带原生守卫的部分控制，应以自身的合法续接定义行为商，不能免费换成全实流。

商为直线也不表示观测轨道的闭包是一条嵌入直线；无周期轨道仍可在更大的环面中回近。此处是参数平移的商分类。

**白话图景。**不要先把“一个周期”额外塞进理论。先问两个内部时刻：从它们接上任意相同后续，所有保留的读出是否始终一样？如果一样，就把它们视作同一个可预测状态。所有这样相同的时间差，自然形成周期群；圆就是具有离散重复间隔时得到的行为商。

### 6.2 观察者加入内部参考，周期可以改变

<a id="statement-6-5"></a>

#### 命题 6.5（读出细化的周期包含）

若 $\mathcal M\subseteq\mathcal N$，则

$$
\boxed{P_{\mathcal N}\subseteq P_{\mathcal M}.}
\tag{6.5}
$$

若两者都有最小正周期，便有
$T_{\mathcal N}=kT_{\mathcal M}$，$k$ 为正整数。

**证明。**

同时保持更多读出的平移，必然保持原有读出。若两群分别为
$T_{\mathcal N}\mathbb Z$ 与 $T_{\mathcal M}\mathbb Z$，其包含关系使
$T_{\mathcal N}\in T_{\mathcal M}\mathbb Z$。

□

细化也可能使离散周期群缩成 $\{0\}$。因此，加入相干参考后出现倍周期或失去精确周期，正是同一整体中增加了必须一同返回的关系。
项目已有离散版本：Periodic Clock Rigidity 对实际对齐的周期核心，证明完整未来行为由时钟种子模最小周期的同余类决定[7](#ref-repo-clock)。这里给出连续全实续接的群形式。

**白话图景。**只看一根表针，可能一圈就重复；再看旁边的相位参考，可能需要两圈或更多圈；连不断追加的账本也看，就可能再也不完全重复。观察者本身仍在整体里，变化的是它保留了多少内部关系。

<a id="section-7"></a>

## 7. 哪些相位真的被看见：可见频率的严格判据

### 7.1 先合并相同频率，再判断周期

对有限效果菜单 $\mathcal M$，令 $0\preceq E\preceq I$，

$$
f_E(t)=\langle \Omega_0,U_t^\dagger E U_t\Omega_0\rangle .
$$

用第 5 节的活动谱分解，定义

$$
c_{E,\omega}=
\sum_{\nu_j-\nu_k=\omega}
\sqrt{p_jp_k}\,\langle \phi_j,E\phi_k\rangle ,\qquad
f_E(t)=\sum_\omega c_{E,\omega}e^{i\omega t}.
\tag{7.1}
$$

同一频率的多个项必须先求和，因为它们可以相消。令
$\mathcal F_{\mathcal M}=\{\omega\ne0:\exists E,\ c_{E,\omega}\ne0\}$。

<a id="statement-7-1"></a>

#### 定理 7.1（可见频率决定菜单周期）

$$
\boxed{
T\in P_{\mathcal M}
\iff \omega T\in2\pi\mathbb Z \quad
\forall\omega\in\mathcal F_{\mathcal M}.}
\tag{7.2}
$$

等价地，若
$\Lambda_{\mathcal M}=\operatorname{span} _{\mathbb Z }\mathcal F_{\mathcal M}$，则

$$
P_{\mathcal M}=\{T:T\Lambda_{\mathcal M}\subseteq2\pi\mathbb Z \}.
\tag{7.3}
$$

**证明。**

差值为
$\sum_\omega c_{E,\omega}(e^{i\omega T}-1)e^{i\omega t}$。
不同实频率的有限指数族线性独立：在零点取到频率数减一阶导数，得到不同频率构成的可逆 Vandermonde 系统。故差值恒零，当且仅当每个非零系数对应的相位因子等于一。整数加法封闭给 (7.3)。

□

若没有可见非零频率，全部读出静止；若
$\Lambda_{\mathcal M}=\omega_*\mathbb Z$，最小周期为 $2\pi/\omega_*$；
若群非循环，就没有非零周期，因为存在 $T\ne0$ 会强制
$\Lambda_{\mathcal M}\subseteq(2\pi/T)\mathbb Z$，而该循环群的子群仍循环。

<a id="statement-7-2"></a>

#### 命题 7.2（无相消的菜单平移缺陷）

定义

$$
\mathcal D_{\mathcal M}(T)=
\lim_{L\to\infty}\frac1{2L}\int_{-L}^{L}
\sum_{E\in\mathcal M}|f_E(t+T)-f_E(t)|^2\,dt .
$$

则

$$
\boxed{
\mathcal D_{\mathcal M}(T)
=4\sum_{E,\omega}|c_{E,\omega}|^2
\sin^2\frac{\omega T}{2}.}
\tag{7.4}
$$

它为零，当且仅当 $T$ 是整个菜单的周期。

**证明。**

展开有限平方和。不同频率交叉项的平均积分趋于零；同频项保留，且
$|e^{i\omega T}-1|^2=4\sin^2(\omega T/2)$。

□

这里的时间平均是解析判据，并未授权观察者免费执行无限时间测量。
只比较一次 $f_E(T)=f_E(0)$ 也不够；例如
$(1-\sin\omega t)/2$ 在 $\pi/\omega$ 返回初值，却不是以该数为周期的函数。

**白话图景。**读口像一组只听得见某些节拍的内部探头。探头听不到的相位差，不影响它报告的周期；同一节拍的几条贡献也可能恰好抵消。先把真正听得见的节拍找齐，再要求它们同时合拍，才能定义这个观察者的周期。

### 7.2 一个完全合法的“读出早返，射线未返”例子

取

$$
H=\hbar\omega_0\operatorname{diag} (0,1,2),\quad
\Omega_0=(1,1,1)/\sqrt3,\quad
E=\frac I2+\frac18
\begin{pmatrix}0&1&1\\1&0&-1\\1&-1&0\end{pmatrix}.
$$

对任意 $z$，扰动二次型绝对值至多为
$\frac14(|z_1z_2|+|z_1z_3|+|z_2z_3|)\le\left\lVert z\right\rVert ^2/4$，
故 $I/4\preceq E\preceq3I/4$，确为合法效果。
相邻两对的 $\omega_0$ 项相消，得到

$$
f_E(t)=\frac12+\frac1{12}\cos(2\omega_0t).
\tag{7.5}
$$

读出最小周期为 $\pi/\omega_0$，完整射线最小周期却为
$2\pi/\omega_0$。在前者时刻，初末重叠平方为 $1/9$。

若根投影 $P_{\Omega_0}$ 已由实际接口取得，则其读出
$|K(t)|^2$ 的同频系数为
$\sum_{\nu_j-\nu_k=\omega}p_jp_k>0$，不会相消。
因此这个特殊同根效果的函数周期，恰等于射线轨迹的周期。
把它解释为概率仍使用 v78 的同根标定，不在此重新假定一个免费可实现的投影。

**白话图景。**有的读口会把两股相反贡献抵消，所以它提早报告“又一样了”。但与同一根态作完整重叠比较时，各个活动谱对都贡献非负权重，没对齐的相位差无法被别的相位差遮掉。

<a id="section-8"></a>

## 8. 项目原生计算：同一条圆怎样产生倍周期或无理近返

### 8.1 保留全部原生合法域的固定纤维

沿用 Phase §9.3、§9.7 的双壁相位坐标[4](#ref-repo-phase)。固定

$$
0<Z<1,\quad r=1-Z,\quad
0<\lambda<r/2,\quad p=\frac{2\lambda}{r}\in(0,1).
\tag{8.1}
$$

取前轮指定的正交归一内部模式

$$
a=\frac{|0\rangle+|13\rangle}{\sqrt2},\qquad
b=\frac{|1\rangle+|3\rangle}{\sqrt2},\qquad m=|2\rangle,
$$

固定初始模式相位吸收到对应基向量中。这是原五模式的编码子空间；
$m$ 为内部固定相干参考分支。写

$$
z=e^{-i\beta}
\bigl(\sqrt p\,a+\sqrt{1-p}\,e^{i\alpha}b\bigr),
\qquad
\Psi=\sqrt r\,z+\sqrt Z\,m.
\tag{8.2}
$$

本节取实际纯相位路径：原生高度位移 $a_{\rm ctl}(t)\equiv0$，
并以相位控制位移 $B=b_{\rm ctl}(t)$ 参数化，因而 $A=K=0$。
仅给端点摘要 $A=K=0$ 不足以限定中途高度；这里固定的是整条路径。
项目精确公式给

$$
\boxed{
\alpha(B)=\alpha_0+B/2,\qquad
\beta(B)=\beta_0+(1-p)B/2.}
\tag{8.3}
$$

固定 $\lambda$ 留在上述严格内部区间，整条纯相位纤维保留其原生 full-support 守卫；本节不靠坐标变换越过控制边界。

<a id="statement-8-1"></a>

#### 定理 8.1（固定纤维的精确周期分类）

在命令参数 $B$ 中：

1. 底部二态球上 $[z(B)]$ 的最小正周期为 $4\pi$。

2. 完整当前射线 $[\Psi(B)]$ 返回，当且仅当

   $$
   B=4\pi n,\qquad np\in\mathbb Z .
   \tag{8.4}
   $$

3. 若 $p=a/q$ 为最简分数，$q>0$，最小完整周期为 $4\pi q$；若 $p$ 无理，则没有非零精确完整周期。

**证明。**

$a,b$ 两系数始终非零，所以底部射线恰在相对相位
$\Delta\alpha=B/2$ 为 $2\pi$ 整数倍时返回。其最小正值为 $4\pi$。

在 $B=4\pi n$ 时，
$z(B)=e^{-i2\pi n(1-p)}z(0)=e^{i2\pi np}z(0)$。
若 $\Psi(B)=e^{i\chi}\Psi(0)$，比较非零 $m$ 分支得
$e^{i\chi}=1$，再比较活动分支得 $e^{i2\pi np}=1$。
反向也立即成立。对固定纤维，(8.3) 是加法流，因此此返回条件保持所有起点参数，给整个轨迹的周期。最小整数 $n>0$ 的算术分类便得到第 3 项。

□

不存在一个非零 $B$ 对开放区间内所有 $p$ 都给相同的完整恒等：
底部要求 $B=4\pi n$，完整参考又要求 $np$ 对所有 $p$ 都为整数，连续性迫使 $n=0$。此结论与 Phase 式 (9.13) 的既有全输入陈述一致。

这里的 $4\pi$ 与 $4\pi q$ 是命令参数周期；将它们换成实验时间需要原生时钟标定。固定 $p$ 的线性相位公式，也没有给出一个对任意未知 $p$ 都相同的全空间酉门。

**白话图景。**底部球面上一圈已经绕完，活动分支却相对于同一整体里的参考分支多转了 $2\pi p$。如果 $p=1/3$，三圈后这个额外相位才整齐归零；如果 $p$ 无理，没有有限圈数能完全归零。圆确实给了第一层周期，更完整的周期由圆与内部参考之间的关系决定。

### 8.2 原生返回残差与可读相位差

在第 $n$ 个底部整圈后，

$$
\langle \Psi(0),\Psi(4\pi n)\rangle 
=Z+r e^{i2\pi np}.
$$

所以

$$
\boxed{
\mathcal R_n
=1-|\langle \Psi(0),\Psi(4\pi n)\rangle |^2
=4rZ\sin^2(\pi np).}
\tag{8.5}
$$

原生内部 $02$ 相位读口为

$$
y_{02}(\lambda,\beta)=2\sqrt{\lambda Z}
\bigl(\cos(\delta_{02}^0+\beta),\sin(\delta_{02}^0+\beta)\bigr),
$$

其中 $\delta_{02}^0$ 是固定初始相位差，见 Phase 式 (10.25)。
因此

$$
\boxed{\left\lVert \Delta y_{02}\right\rVert 
=4\sqrt{Z\lambda}\,|\sin(\pi np)|.}
\tag{8.6}
$$

后式来自该读口的相位向量半径 $2\sqrt{Z\lambda}$ 与圆上弦长公式。
这将当前射线的返回缺陷，与已声明的内部参考读出连接起来。

若 $p$ 无理，对任意整数 $Q\ge2$，将
$0,p,\ldots,Qp\bmod1$ 放进 $Q$ 个等长区间，得到
$1\le n\le Q$，使到最近整数的距离 $\|np\|_{\mathbb R /\mathbb Z }\le1/Q$。
因此纯态半迹距离满足

$$
D(P_{\Psi(4\pi n)},P_{\Psi(0)})
=2\sqrt{rZ}\,|\sin(\pi np)|
\le\frac{2\pi\sqrt{rZ}}{Q}.
\tag{8.7}
$$

**白话图景。**参考分支不仅能告诉我们“还没完全回来”，也能读出差了多少。无理相位永远没有有限的精确整圈，但总能找到某个圈数，使剩下的错位任意小。精确周期与近回返因此有各自明确的残差。

这个有理／无理分类是精确数学性质。对任意有限圈数上界 $N$，

$$
\max_{1\le n\le N}
|e^{i2\pi np}-e^{i2\pi np'}|
\le2\pi N|p-p'|.
$$

有理数与无理数都稠密，所以在有限参数精度、有限圈数内，
两种周期类型可以任意接近。有限精度判断应报告实际残差与圈数，
不能仅由这种有限资料断言权重具有哪种精确算术类型。

**白话图景。**说一个装置理论上“三圈完全回到原位”，与说实测“三圈后偏差小于某个刻度”，是两个层次。内部观察者用有限精度读表时，保留误差和已经走过的圈数，就能诚实表达它实际知道了什么。

### 8.3 接回历史圆、椭圆与水平几何相位

在二态球面上令纬度参数

$$
c=2p-1\in(-1,1).
$$

对应圆可写成
$r(\theta)=(\sqrt{1-c^2}\cos\theta, \sqrt{1-c^2}\sin\theta,c)$。选截面

$$
\psi_c(\theta)=
\begin{pmatrix}\sqrt{(1+c)/2}\\e^{i\theta}\sqrt{(1-c)/2}\end{pmatrix}.
$$

因为
$\langle \psi_c,\partial_\theta\psi_c\rangle =i(1-c)/2$，水平提升为

$$
z_h(\theta)=e^{-i(1-c)\theta/2}\psi_c(\theta),
\qquad \langle z_h,dz_h\rangle =0.
$$

一圈留下

$$
\boxed{\zeta=e^{-i\pi(1-c)}
=e^{i2\pi p}.}
\tag{8.8}
$$

式 (8.3) 正满足 $d\beta=(1-p)d\alpha$，所以本节原生流确为这个水平提升。

前轮历史圆的有向测地曲率 $k$ 与选定历史平面上的椭圆偏心率 $e$ 满足

$$
c=\frac{k}{\sqrt{1+k^2}},\qquad e=|c|.
\tag{8.9}
$$

因而在这套既定投影与水平控制下，椭圆参数与参考相位的精确回返算术相联。
这里的椭圆是圆的指定平面投影，不能把任意球面曲线称为平面椭圆。
$c$ 与 $-c$ 给相同无向偏心率，单圈相位互为逆元，最小回返圈数相同；方向信息仍需保留。

**白话图景。**上一轮那条历史圆，投到选定平面后可以看成椭圆；它在球面上包住的有向面积，又决定水平搬运一圈留下的相位。于是形状、方向、参考错位与倍周期，变成同一组内部关系的不同读法。

### 8.4 同一球面圆，实际总相位仍须按实际门计算

以上有理性判据使用已经证明的水平控制。若实际采用常定

$$
H=\frac{\hbar\Delta}{2}\,n\cdot\sigma,\qquad \Delta>0,\quad n\in S^2,
$$

且 $n\cdot r=c$，底部圆周期为 $T=2\pi/\Delta$，但
$U(T)=-I$。该圈动力学相位为 $-\pi c$，几何相位为
$-\pi(1-c)$，总相位为 $-\pi$。
若另保留固定相干参考分支，总相位两圈返回，与 $c$ 的有理性无关。

几何闭环的相位理论已有原始文献[8](#ref-aa1987)。这里给出的水平公式已直接验证；引用的历史背景不替代原生控制的证明。

**白话图景。**同一条球面圆可以用不同的门来走。圆的面积确定几何部分，实际门还可能贡献动力学相位。旁观参考看到的是二者之和；所以必须先证明实际走法是水平的，才可以直接用圆的面积判断完整回返。

<a id="section-9"></a>

## 9. 一般有限谱的近回返：没有精确周期仍能共同回近

<a id="statement-9-1"></a>

#### 定理 9.1（指定时间网格上的近回返）

在第 5 节的固定有限谱前件下，任给时间间隔 $\tau>0$ 与整数
$Q\ge2$，存在整数
$1\le n\le Q^{r-1}$，令 $T=n\tau$，使

$$
\min_\chi\left\lVert U_T\Omega_0-e^{i\chi}\Omega_0\right\rVert 
\le\frac{2\pi}{Q},\qquad
\mathcal R(T)\le\frac{4\pi^2}{Q^2}.
\tag{9.1}
$$

**证明。**

若 $r=1$，射线恒定，结论直接成立。若 $r\ge2$，置
$\alpha_j=\tau(\nu_j-\nu_1)/(2\pi)$，$j=2,\ldots,r$。
将 $[0,1)^{r-1}$ 分成 $Q^{r-1}$ 个边长为 $1/Q$ 的方格。
在 $0,\alpha,\ldots,Q^{r-1}\alpha\bmod1$ 中，两点同格；指标相减给所需 $n$，每个相对相位到整圈的误差小于 $2\pi/Q$。

由正交分量，

$$
\left\lVert e^{i\nu_1T}U_T\Omega_0-\Omega_0\right\rVert ^2
=\sum_{j=2}^rp_j|e^{-i(\nu_j-\nu_1)T}-1|^2
\le\frac{4\pi^2}{Q^2}.
$$

最优相位只会缩短距离，且
$1-|K|^2\le2(1-|K|)=\min_\chi\left\lVert U_T\Omega_0-e^{i\chi}\Omega_0\right\rVert ^2$，
得到结论。

□

时间间隔 $\tau$ 可选得比任何指定等待时间大，故此定理给任意晚的近回返。
若要求确实曾离开初态，取一对不同活动频率，并令
$t_{\rm exit}=\pi/|\nu_j-\nu_k|$。由式 [(5.4)](#eq-return-residual)，
$\mathcal R(t_{\rm exit})\ge4p_jp_k>0$。再选 $\tau>t_{\rm exit}$ 与更小返回容差，即得到在一次明确离开之后的近回返。

连续时间还能减少一个逼近维数：取
$\tau_{\rm gap}=2\pi/|\nu_2-\nu_1|$，第一相对相位自动整圈，只需逼近剩余 $r-2$ 项，得到 $T\le\tau_{\rm gap}Q^{r-2}$ 的同类界；$r=2$ 时直接精确返回。
这些是标准 Dirichlet／抽屉原理机制。量子回归已有 Bocchieri--Loinger 的原始工作；Gupta--Short 的近期论文还研究统一回归、明确离开条件及更精细时间界[9](#ref-bl1957)、[10](#ref-gs2026)。本文不声称该界最优或给出了首次回返时间。

<a id="statement-9-2"></a>

#### 推论 9.2（同一误差控制所有时刻的效果读出）

对任意效果 $0\preceq E\preceq I$，

$$
|f_E(t+T)-f_E(t)|
\le\sqrt{\mathcal R(T)}
\le2\pi/Q\qquad(\forall t).
\tag{9.2}
$$

**证明。**

由共同酉运输，初末两纯态的半迹距离与 $t$ 无关，等于
$\sqrt{1-|K(T)|^2}$。两投影不同时，在其张成的至多二维空间中，
投影之差的两个非零特征值为此数及其负数；两投影相同时结论直接成立。
任意效果的期望差不超过正部的迹，故得不等式。

□

**白话图景。**有限多个圆未必会精确同步，但相位都被限制在有限个圆周里。把这些圆周刻度分得足够细，足够多次演化后必有两次落进同一小格；两次之差就是一次共同近返。它保证“能回来得任意近”，没有把近似重复冒充完全相同。

<a id="section-10"></a>

## 10. 内生时钟与历史：表盘可以重复，账本继续增长

### 10.1 静态整体中已经包含全部带索引读口

固定内部结构 $(\mathcal H,U,\Omega_0)$，令
$\omega(A)=\langle \Omega_0,A\Omega_0\rangle$。将历史索引放到读口
$A_t=U_t^\dagger AU_t$ 中，就有

$$
\boxed{
\omega(A_t)=\langle U_t\Omega_0,A\,U_t\Omega_0\rangle .}
\tag{10.1}
$$

这是同一结构的两种表示：固定读口看演化向量，或固定根看带历史索引的读口。连续接续关系与时间尺度仍须由该结构提供，不能由记号转换凭空获得。

若一只内部相位钟满足 $\varphi=2\pi t/T\bmod2\pi$，它只给出 $t\bmod T$。
要区分第几圈，须保留额外内部计数。整体 $\Omega$ 可以同时包含钟面和计数器；局部周期不要求完整记录也周期。

<a id="statement-10-1"></a>

#### 命题 10.1（完整追加档案排除非空历史循环；项目已有）

若完整事件档案为有身份的有限序列 $H_n=(e_1,\ldots,e_n)$，
档案表示单射，且每步追加一个事件，则对任意正整数 $q$，

$$
H_{n+q}\ne H_n.
\tag{10.2}
$$

**证明。**

档案长度分别为 $n+q$ 与 $n$，不同；由表示单射，其完整内部状态不同。

□

History Records §144 已证明该单调档案结论；§148 已给出局部三周期，
并把它和增长的档案写成离散螺旋[6](#ref-repo-history)：

$$
\Gamma_n=(\cos(2\pi n/3),\sin(2\pi n/3),n).
$$

该部分是本轮必须保留的既有基础，不重复计为新发现。

单射编码本身只说明档案不同，有限维空间也能容纳无限多个不同的非正交态。
如果这些档案还须由声明的合法读出零误差完美区分，则其纯记录态必须正交，
因而无限追加会超出固定有限维容量。这里使用的是额外的完美可读要求。
有限维近回返与持续增加但可能不可完美区分的历史标签不冲突；
无限容量的完美档案则不满足有限维回返定理的前件。

**白话图景。**一个人可以看到钟表再次指向十二点，同时记得“已经多过了一天”。钟表与记忆都在同一整体里，重复的是钟面的读出，增长的是历史记录。圆解释节拍，保存圈数的内部关系解释为什么经历并没有被抹掉。

### 10.2 把量子门序列的递增与连续圆流接起来

对一参数门流，任意划分
$t_0<\cdots<t_N$ 给
$U_{t_N-t_0}=U_{\Delta t_N}\cdots U_{\Delta t_1}$。
进一步细分某段，由群律得到同一合成门。因而在已声明自治光滑前件下，
连续轨迹与逐段门序列相容。

但一般递增门历史 $G_N\cdots G_1$ 不必来自同一个一参数群。
若门顺序影响结果，或生成元随保留历史变化，就需把相关历史加入状态，
重新检查定理 [2.2](#statement-2-2) 的下降条件。
项目 V78 所强调的完整跨历史核与标架，正用于控制这类一般情形[1](#ref-repo-v78)。

**白话图景。**连续运动可以看成把同一内部演化切得越来越细：每小段都是一个增量门，细分不会改变整段结果。若下一步门取决于先前路径，就把这段依赖保留在状态里；不能只留一个球面点，却要求它独自承接所有历史。

<a id="section-11"></a>

## 11. 从公理到定义约束：本轮可以压缩到什么程度

### 11.1 反推表：每条前件对应哪两个元

| 撤去的条件 | 受影响的两个内部元 | 具体后果及所属结构 |
| --- | --- | --- |
| 投影速度在纤维上相同 | 同读出来源 $x,x'$ 的两投影速度 | 当前圆点不足以决定后续；属于状态摘要的可下降性 |
| 圆流处处非零 | 当前位置与有限一圈的目标接续 | 可能渐近停住，无法有限完成一圈；属于自治流的遍历单圈 |
| 相位路径相容 | 复合值 $\zeta_{ij}\zeta_{jk}$ 与直达值 $\zeta_{ik}$ | 饱和候选出现负三阶主子式；属于整体正核拼接 |
| 连续相位组合律 | 分段过程与合并过程的相位 | 没有固定频率表示的保证；属于接续表示 |
| 可见频率公度 | 初始历史与平移历史的全部读出 | 合法整体可无精确周期；属于周期稳定子 |
| 相干参考回返 | 活动分支与保留参考的相位 | 底部闭环不足以给完整当前态周期；属于扩展读出 |
| 记录回返 | 当前档案与追加后的档案 | 钟面周期不能使完整历史重复；属于身份保持 |

并非表中每项都是“所有量子系统必须满足的公理”。例如频率公度是
*精确周期模型*的定义条件，不是量子理论普遍要求。将它强加于所有量子模型，
反而会错误排除第 5 节的合法无理频率例。

### 11.2 一个更短的关系骨架

接续 v78，可以把本轮用到的骨架写成三个相容式。设内部历史为 $h$，
共同接续为 $T_a$，全部读出为 $q$：

$$
\boxed{
\begin{aligned}
&\text{整体可拼：}\quad
\sum_{i,j}\overline{c_i}c_jK(h_i,h_j)\ge0,\quad K(h,h)=1;\\
&\text{续接可拼：}\quad
K(T_ah,T_ak)=K(h,k),\quad T_{a+b}=T_aT_b;\\
&\text{概念可答：}\quad
c(h)=c(k)\ \Longrightarrow\ q(h)=q(k)
\quad\text{对声明的所有后续测试}.
\end{aligned}}
\tag{11.1}
$$

第一式给同一整体的正核；第二式声明合法的保关系接续，必要的可逆性与光滑性仍须给出；第三式要求一个概念保留足以回答其目标的问题。

在各自完整前件下，V78 的最小表示定理与 V74 的自治重建已把这些关系连接到
Hilbert 表示、酉门及自伴生成元；有限秩、合法可逆续接与所需锚点光滑性等
仍按各定理保留[1](#ref-repo-v78)、[2](#ref-repo-v74)。
本轮增加的结果是：在第 3 节的固定正权、全边单位模的饱和相位类中，
整体可拼压成两路径残差；
周期概念则压成

$$
\boxed{
T\in P_{\mathcal M}
\iff
q(T_T h)=q(h)\quad
\text{对所有声明读出与全部平移历史}.}
\tag{11.2}
$$

这使“周期”成为定义之间的约束，而非额外指定的一串周期常数。

如果 $K$ 已定义成实际幅度的 Gram 核，正性由平方范数自动成立；
如果从抽象二元数据开始重建幅度，所有有限表的正性仍是待验证条件。
把同一条件从公理栏移到定义栏，不等于证明任意关系宇宙都必须满足它。

**白话图景。**可以把规则压短，但压短要有内容：所有局部答案确实能拼成同一个整体；一段过程分开做与合起来做，确实保留同一关系；一个概念合并的两段历史，确实能回答相同的后续问题。周期、生成元和可读相位，就是在这张相容图上推出来的对象。

### 11.3 量子起源还剩哪一个精确问题

单凭“有圆、可组合、内部有钟”不能唯一选出量子理论。
反例是经典确定性圆钟：
$\theta(t)=\theta_0+\omega t\bmod2\pi$，
其全部状态、速度、读出和记录都可以定义在内部，并满足第 2 节的周期定理。
它并不因此拥有量子叠加、非交换效果或 Born 概率。

所以本轮证明的起源链是有前件的：保留第 3 节的有限固定正权、全边单位模
饱和条件，再加第 4 节的连续相位同态，才能使用下面的相位积分路线；
一般正核并不强制三角相位为零，也不自动产生自治常生成元。

$$
\text{共同正关系表示}
\ \Longrightarrow\
\text{相位路径可积}
\ \Longrightarrow\
\text{有限自治生成元}
\ \Longrightarrow\
\text{周期群与近回返}.
\tag{11.3}
$$

若要进一步证明“只有量子结构可行”，下一项真正的目标是：
从更弱且可独立说明的内部操作关系，排除不具所需正核／复相位／效果结构的其他模型。
其中 Born 解释仍接续 v78 的同根校准与效果相容，不能由周期性单独替代。

**白话图景。**这轮已经说明：一旦整体能够用共同的相位关系描述，圆为什么会带来节拍，多个节拍为什么可能不同步，参考为什么会读出倍周期，历史为什么仍能增长。更深的量子起源问题，是证明为什么内部可组合的关系必须具有这种量子结构；这个问题现在有了明确接口，不再藏在“都在整体里”一句话后面。

<a id="section-12"></a>

## 12. 完整白话图景：把本轮结果连成一幅画

整体 $\Omega$ 里有许多内部状态，它们之间不是孤立的点，而是能比较、能接续的关系。
挑出两个分量，它们的相对相位像一只圆上的指针。历史决定这根指针接下来怎样走；
如果同一个保留状态每次都有同样走法，而且沿途不停住，就会得到一圈一圈的周期。

但整体里不止一只圆。甲到乙、乙到丙与甲到丙的相位必须能对上；
否则每只局部圆看起来合法，拼成整体却会给同一个问题互相冲突的答案。
这些相位路径一旦相容，各对转速就能统一写成内部分量转速之差，
于是得到同一生成元和相应的量子演化。

各只圆有共同整圈时，完整当前态周期返回；没有共同整圈时，
它仍可能任意接近返回。球面上的历史圆还有内部相干参考：
底部指针一圈回来了，参考相位可能只转了一个分数圈。
在项目原生控制里，这个分数就是支路权重 $p$；有理数给倍周期，
无理数给无精确周期的近回返。

圆的平面读出可以是椭圆，它所保留的几何信息与水平搬运的相位相连；
实际门的总相位则必须连同动力学部分一起核对。
观察者只看哪些关系，就由哪些关系共同决定它的周期。
再把圈数写入内部账本，表盘依然重复，完整历史却继续增长。
时钟、参考、观察者、记录，以及它们必须满足的相容关系，都在同一个 $\Omega$ 中。

## 资料与可复核位置

<a id="ref-repo-v78"></a>

**[1]**
[AURIC V78：Gate Manifolds, Integrable Relations, Tangent Kernels and Recursive Error](https://github.com/the-omega-institute/trureturing/blob/3ca0ba6c579f2685c52d95a4a6b8a07d037382c9/docs/develop/theory/AURIC_GATE_MANIFOLDS_INTEGRABLE_RELATIONS_TANGENT_KERNELS_AND_RECURSIVE_ERROR_V78.md)，
特别是 §12。固定提交如第 1 节。本文使用公开正文，不声称新增结果已完成 Lean 验证。

<a id="ref-repo-v74"></a>

**[2]**
[AURIC V74：Smooth Quantum Histories, Cotangent Dynamics and Endogenous Motion](https://github.com/the-omega-institute/trureturing/blob/3ca0ba6c579f2685c52d95a4a6b8a07d037382c9/docs/develop/theory/AURIC_SMOOTH_QUANTUM_HISTORIES_COTANGENT_DYNAMICS_AND_ENDOGENOUS_MOTION_V74.md)，
§3，定理 3.2：平移不变正核的自治酉重建。

<a id="ref-repo-v73"></a>

**[3]**
[AURIC V73：Prefix States, Minimal Closed Relational Body and Unitary Reconstruction](https://github.com/the-omega-institute/trureturing/blob/3ca0ba6c579f2685c52d95a4a6b8a07d037382c9/docs/develop/theory/AURIC_PREFIX_STATES_MINIMAL_CLOSED_RELATIONAL_BODY_AND_UNITARY_RECONSTRUCTION_V73.md)，
§3，定理 3.2、命题 3.3：三角 Gram 及闭路相位拼接。

<a id="ref-repo-phase"></a>

**[4]**
[AURIC：Probability, Phase Transport and Holonomy](https://github.com/the-omega-institute/trureturing/blob/3ca0ba6c579f2685c52d95a4a6b8a07d037382c9/docs/develop/theory/AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md)，
§§3、8--9，尤其式 (9.11)、(9.13)、(9.29)。

<a id="ref-repo-omega"></a>

**[5]**
[AURIC OMEGA：Static Compatibility Fiber Theory](https://github.com/the-omega-institute/trureturing/blob/3ca0ba6c579f2685c52d95a4a6b8a07d037382c9/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，
§20 命题 44、§21 假设 45.1。固定总等待与独立控制具有不同权限和周期结构。

<a id="ref-repo-history"></a>

**[6]**
[AURIC：History Records and Time Arrow](https://github.com/the-omega-institute/trureturing/blob/3ca0ba6c579f2685c52d95a4a6b8a07d037382c9/docs/develop/theory/AURIC_FIB_HISTORY_RECORDS_TIME_ARROW.md)，
§144 定理 144.5；§148 定理 148.3、命题 148.4。局部周期与单射追加档案并存。

<a id="ref-repo-clock"></a>

**[7]**
[Recursive Relational Observation：Periodic Clock Rigidity](https://github.com/the-omega-institute/trureturing/blob/3ca0ba6c579f2685c52d95a4a6b8a07d037382c9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PERIODIC_CLOCK_RIGIDITY.md)，
§3 定理 3.1、推论 3.2。其前件包含同一个实际对齐的周期核心。

<a id="ref-aa1987"></a>

**[8]**
Y. Aharonov and J. Anandan,
*Phase change during a cyclic quantum evolution*,
Physical Review Letters 58, 1593--1596 (1987).
[DOI: 10.1103/PhysRevLett.58.1593](https://doi.org/10.1103/PhysRevLett.58.1593)。
本次核对原出版社页面与摘要；本文水平相位公式给出独立直接证明。

<a id="ref-bl1957"></a>

**[9]**
P. Bocchieri and A. Loinger,
*Quantum Recurrence Theorem*,
Physical Review 107, 337--338 (1957).
[DOI: 10.1103/PhysRev.107.337](https://doi.org/10.1103/PhysRev.107.337)。
本次核对原出版社摘要及元数据，不声称阅读全文。

<a id="ref-gs2026"></a>

**[10]**
C. Gupta and A. J. Short,
*Recurrence Time for Finite Quantum Systems*,
Physical Review Letters 137, 140201 (2026)，2026 年 9 月 30 日。
[原出版社开放 PDF](https://journals.aps.org/prl/pdf/10.1103/392k-bgpt)。
本次核读回归定义与 Dirichlet 证明相关段落；本文仅使用自足的初等近回返论证，不复述其精细界。

## 源稿前言与排版元数据

```tex
% !TEX program = xelatex
% Compile twice with XeLaTeX. Fallback font: fonts/NotoSerifCJKsc-Regular.otf.
\documentclass[11pt,a4paper]{article}
\usepackage[margin=24mm,headheight=16pt]{geometry}
\IfFileExists{ctex.sty}{\usepackage[UTF8,fontset=auto]{ctex}}{
  \usepackage{fontspec}
  \IfFontExistsTF{Noto Serif CJK SC}{\setmainfont{Noto Serif CJK SC}[AutoFakeBold=1.7]}{\setmainfont{NotoSerifCJKsc-Regular.otf}[Path=fonts/,AutoFakeBold=1.7,AutoFakeSlant=.15]}
  \XeTeXlinebreaklocale "zh"
  \XeTeXlinebreakskip=0pt plus 1pt
}
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage{xcolor,booktabs,array,tabularx,longtable}
\usepackage{fancyhdr,enumitem,hyperref,needspace}
\definecolor{ink}{HTML}{17384A}
\definecolor{accent}{HTML}{007D86}
\hypersetup{colorlinks=true,linkcolor=ink,urlcolor=accent,citecolor=ink,pdftitle={AURIC v78 后续研究：圆、周期与内生时钟}}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small AURIC / v78 后续研究}
\fancyhead[R]{\small 圆、周期与内生时钟}
\fancyfoot[C]{\thepage}
\setlength{\parindent}{1.8em}
\setlength{\parskip}{4pt}
\setlength{\emergencystretch}{3em}
\setlist{nosep,leftmargin=2em}
\renewcommand{\baselinestretch}{1.10}
\renewcommand{\contentsname}{目录}
\renewcommand{\abstractname}{摘要}
\renewcommand{\refname}{资料与可复核位置}
\renewcommand{\proofname}{证明}
\theoremstyle{definition}
\newtheorem{definition}{定义}[section]
\newtheorem{theorem}[definition]{定理}
\newtheorem{proposition}[definition]{命题}
\newtheorem{corollary}[definition]{推论}
\newtheorem{remark}[definition]{说明}
\newcommand{\ip}[2]{\langle #1,#2\rangle}
\newcommand{\norm}[1]{\left\lVert #1\right\rVert}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\Z}{\mathbb Z}
\newcommand{\Q}{\mathbb Q}
\newcommand{\tr}{\operatorname{Tr}}
\newcommand{\Span}{\operatorname{span}}
\newcommand{\diag}{\operatorname{diag}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\plain}[1]{\par\noindent\textbf{白话图景。}#1\par}
\newcommand{\repo}[2]{\href{https://github.com/the-omega-institute/trureturing/blob/3ca0ba6c579f2685c52d95a4a6b8a07d037382c9/#1}{#2}}
\title{\color{ink}\bfseries 圆、周期与内生时钟\protect\\[5pt]\large 从二元相位的拼接，到整体量子关系的返回\protect\\[5pt]AURIC v78 后续研究：定义、定理与证明}
\author{研究续稿}
\date{2026 年 11 月 2 日}
```

```tex
\begin{document}
\maketitle
\setcounter{tocdepth}{1}
{\small\setlength{\parskip}{0pt}\tableofcontents}
\newpage
\begin{center}\small
\end{center}
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.17\textwidth}XX@{}}
\toprule
\midrule
\bottomrule
\end{tabularx}
\end{center}
\Needspace{12\baselineskip}
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.21\textwidth}XX@{}}
\toprule
\midrule
\bottomrule
\end{tabularx}
\end{center}
\clearpage
\begin{thebibliography}{99}
\end{thebibliography}
\end{document}
```
