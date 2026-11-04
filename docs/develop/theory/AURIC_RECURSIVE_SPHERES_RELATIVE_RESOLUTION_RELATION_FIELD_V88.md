# 递归球面与相对分辨率关系场

从轨迹的轨迹，到内部锚与可见关系的双向相容

**AURIC v88：一个完整量子公理候选及其理论接续**

项目连续研究稿

2026 年 11 月 2 日

## 摘要

本轮承接 v87，研究“关系的变化仍是关系，归一以后又落到同一球面”的递归图景。首先证明：一条光滑正则球面曲线的归一切向可以无限向前递归，每个有限层仍为同一单位球面上的正则曲线；相邻三层的二元夹角和带向三元比较，恢复相对速度与测地曲率。进一步给出曲率递推、圆的层间四循环、局部逆向重建及闭合前驱存在的完整判据。无限微分层级不自动意味着无限独立分辨率，完整相位与时钟尺度也不能由归一轨迹代替。

本轮只新增一个候选 $C_{88}$：相对于一个忠实内部比较态，同一个粗化代表须同时保持它与任意可见关系的左右两种有序复比较。先以左比较定义唯一 GNS 投影，再把右序延续相容作为唯一新增约束。由此解析推出保持伴随、双模性质、正性、完全正性，以及保态条件期望的唯一形式。它存在当且仅当可见代数被锚的模流保持；有限分块中，锚必须是块乘积态。这是标准 Takesaki 判据的有限自足证明和项目接口，不宣称模理论本身为新发现。

删除右序条件会把一个正效果映成负算子。如果同一个固定分辨率要求适配每个忠实内部锚，则只能为全代数或标量代数；量子比特中，相容条件简化为锚方向与保留轴共线。因此非平凡的相对层级由“锚、分辨率、比较协议”共同确定。将这些相容切口接成塔，得到完全正的粗化表示、误差勾股分解和条件方差递归；允许切口随内部条件变化，得到可见子空间的连接与曲率。最后接回共同复正核、Born 读数、酉演化、张量组合和记录通道，明确统一关系场已经闭合的数学部分与尚未选择的现实动力学。

全部数学论证采用解析证明；没有运行数学程序、数值实验、符号计算或候选枚举。

## 目录

- [1. 版本位置：把“关系的关系”接到可执行分辨率](#section-1)
- [2. 同一球面模板上的轨迹、切向与再变化](#section-2)
- [3. 无限前向递归与相邻三层的内生读数](#section-3)
- [4. 逆向重建：局部可以继续，全球必须配平](#section-4)
- [5. 同球表示需要保留的尺度、补态与完整相位](#section-5)
- [6. 内部分辨率：先定义左比较，再增加一个约束](#section-6)
- [7. 主等价定理：从有序比较推出完全正性](#section-7)
- [8. 锚与切口如何配套：有限分块及模流](#section-8)
- [9. 可观测量与状态的不同映射，以及删条件反例](#section-9)
- [10. 全锚要求的分类，以及二元三维图景](#section-10)
- [11. 候选的准确范围：完整比较代表，不是所有信息处理的禁令](#section-11)
- [12. 内容即地址：相对分辨率中的精确定义](#section-12)
- [13. 递归分辨率塔：细节、误差与条件方差](#section-13)
- [14. 每个二元关系怎样再进入有限三维球面](#section-14)
- [15. 没有最高与最底层：有限界限与一个双向开放模型](#section-15)
- [16. 统一关系场的一个明确载体：随内部条件变化的分辨率](#section-16)
- [17. 现有量子规则怎样接回这条关系链](#section-17)
- [18. 反着推：每个条件究竟排除了什么](#section-18)
- [19. 统一关系场的已闭合部分与继续延伸的边界](#section-19)
- [来源与版本关系](#references)

<a id="section-1"></a>

## 1. 版本位置：把“关系的关系”接到可执行分辨率

本轮为 v88，接续已完成的 v87“相对锚、交换原子与关系场”。此前共同复正核、效果强度标定、独立组合、完整相干执行、内部能量闭合和共同场相容继续作为已声明的前件。本轮不把这些已讨论的结构重新当成未回答的问题，也不声称从一句“内容即地址”无前提地推出全部量子力学。

项目核读限于固定提交

`c63ab162315fddd0801cbe9f47dbf3eda6e13360`

下本地已有的 16 份理论 Markdown 的有关章节。本轮公开当前 HEAD 读取没有成功，故不认证该固定基线之后的仓库更新。版本递增指本对话的连续研究稿。

Atlas III 已给普通保迹条件期望、可见与隐藏投影、连续正规化子生成元分类；$\Omega$ 静态纤维稿已有相容局部态到 GNS 的拼接；观察闭包稿已有固定有限载体的分辨率终止界；V78、V79 已强调二元关系球必须保留强度尺度和同一历史身份 [1](#ref-atlas)–[4](#ref-v79)。本轮的增量是：**把比较标定从均匀迹换成实际内部锚以后，什么可见切口仍能同时保持两种次序的完整比较？**

为使“一切概念都是关系”成为能核对的理论语法，本文采用三个定义层次。一是内容及其准备、变换与记录之间的关系；二是对这些关系再作比较、组合和读出；三是指定哪些比较在当前分辨率内可用。锚也是内部关系数据，切口也由内部协议指定，二者相容与否可由内部二元比较检验。它们都不需要一个站在 $\Omega$ 之外的观察者。

但是，*同一种关系表示模板*与*同一个物理状态空间*须保留类型区分。曲线、算符、效果、细节残差、参照协议可以互相编码和比较；要将某个编码当成可制备量子态，还要证明正性、归一、相位和组合条件。下面先给球面递归的正面定理，再以一个新增约束锁定它的操作分辨率接口。

**白话图景。**你画的是一幅可以不断换起点的图：当前轨迹是内容，轨迹的变化又成为新的内容。我们先证明这幅图能怎样一直画下去，再问每次收起细节时，留下的地址能否继续与其他可见内容正确相接。这一次的新公理只管这个接续问题；它会实际排除产生负读数的压缩方式。

<a id="section-2"></a>

## 2. 同一球面模板上的轨迹、切向与再变化

先把用户的图景落实到一个可完整证明的情形：在同一内部参照协议下，将一个二态有效片的轨迹展开到固定初始载体，得到单位 Bloch 球上的曲线。本节参数 $t$ 是已经选定的有向内部参数，并不由几何自动确定为某种物理时钟。球面切向像属于经典微分几何的研究对象 [7](#ref-sahiner)；以下结论逐项证明，不把既有切向像理论当作本项目的数学首创。

### 定义 2.1（球面切向层）

设 $I\subset\mathbb R$ 为区间，$n_0:I\to S^2\subset\mathbb R^3$ 为 $C^\infty$ 曲线，且 $v_0(t)=|\dot n_0(t)|>0$。递归定义

$$
 v_k=|\dot n_k|,\qquad n_{k+1}=\frac{\dot n_k}{v_k}.
$$

在已定义的层上，记

$$
 N_k=n_k\times n_{k+1},\qquad
 \kappa_k=\frac{\dot n_{k+1}\cdot N_k}{v_k}.
$$

$\kappa_k$ 是单位球面上的带向测地曲率。在移动锚中，可以把点导数统一替换为同一 $SO(3)$ 参照连接的协变导数 $D_t$；该连接保持内积与叉乘，v87 的内部展开把沿同一路径的计算化为上述形式。球面半径取 $1$，相应 Fubini–Study 速度为 $v_k/2$。

### 定理 2.2（二元比较配平与球面 Darboux 关系）

对任意光滑正则球面曲线，记 $n=n_k$、$T=n_{k+1}$、$N=n\times T$、$v=v_k$、$\kappa=\kappa_k$。则

$$
\boxed{
\dot n=vT,\qquad
\dot T=v(-n+\kappa N),\qquad
\dot N=-v\kappa T.}
$$

**证明。**由 $n\cdot n=1$ 得 $n\cdot T=0$。对这个二元正交关系求导，

$$
0=\frac d{dt}(n\cdot T)=\dot n\cdot T+n\cdot\dot T=v+n\cdot\dot T,
$$

所以 $\dot T$ 沿 $n$ 的分量为 $-v$。由 $T\cdot T=1$，它没有沿 $T$ 的分量；在正交定向框架 $(n,T,N)$ 中剩余分量唯一写成 $v\kappa N$。最后

$$
\dot N=\dot n\times T+n\times\dot T=vn\times(\kappa N)=-v\kappa T.
$$

这里的 $+v$ 与 $-v$ 是同一个二元比较的两端变化，恰好配平。三个框架向量共同满足 $\dot e=\omega_{\rm D}\times e$，其中 $\omega_{\rm D}=v(N+\kappa n)$。这是移动框架的运动学角速度；仅凭一条轨迹，尚不能把它认作唯一的实际 Hamiltonian。

**白话图景。**原来的点向前走，切箭头就必须朝原点方向转回一点，才能继续与球面相切。这份必需的回转配平了原点的前进；剩下朝侧面的转动，才是轨迹在球面内的弯曲。曲率因此可以从点与切箭头怎样共同变化中读出，不必先贴上一个外来的形状标签。

<a id="section-3"></a>

## 3. 无限前向递归与相邻三层的内生读数

### 定理 3.1（正则切向递归与精确曲率递推）

在定义的 $C^\infty$ 与 $v_0>0$ 条件下，每个有限层都光滑且正则。令 $q_k=\sqrt{1+\kappa_k^2}$，则

$$
\boxed{
 v_{k+1}=v_kq_k\ge v_k>0,\qquad
 \kappa_{k+1}=\frac{\dot\kappa_k}{v_k(1+\kappa_k^2)^{3/2}}.}
$$

相邻框架满足

$$
 n_{k+2}=\frac{-n_k+\kappa_kN_k}{q_k},\qquad
 N_{k+1}=\frac{\kappa_kn_k+N_k}{q_k}.
$$

**证明。**若第 $k$ 层已光滑且正则，由 Darboux 关系

$$
|\dot n_{k+1}|^2=v_k^2(1+\kappa_k^2)>0,
$$

故下一层速度非零，归一操作保持光滑，归纳即知所有有限层存在，并得到第一条速度式与框架递推。为核对曲率，暂记本层为 $(n,T,N,v,\kappa)$，令 $q=\sqrt{1+\kappa^2}$、$T_1=(-n+\kappa N)/q$、$N_1=(\kappa n+N)/q$。逐项代入 Darboux 关系，

$$
\dot T_1=-vqT+\frac{\dot\kappa}{q^2}N_1.
$$

下一层 Darboux 形式为 $\dot T_1=v_1(-T+\kappa_1N_1)$，比较系数即得 $v_1=vq$ 与 $\kappa_1=\dot\kappa/(vq^3)$。

若 $ds_k=v_kdt$，还可写成

$$
\boxed{ds_{k+1}=\sqrt{1+\kappa_k^2}\,ds_k,\qquad
\kappa_{k+1}ds_{k+1}=d(\arctan\kappa_k).}
$$

所以，下一层的带向曲率记录本层弯曲角怎样继续变化。无限前向结论使用 $C^\infty$；若只供应有限阶光滑性，只能在相应可微阶数内递归。

**白话图景。**只要最初的轨迹不停顿，球面就保证下一层切箭头也不会突然停止变化。每层都可以继续画在同一张球面模板上。前一层怎样弯，决定后一层走得多快；前一层的弯曲怎样改变，决定后一层又怎样弯。

### 命题 3.2（相邻三层恢复相对速率与带向曲率）

对每个已定义层，$n_k\cdot n_{k+2}<0$，并有

$$
\boxed{
 \frac{v_{k+1}}{v_k}=-\frac1{n_k\cdot n_{k+2}},\qquad
 \kappa_k=-\frac{(n_k\times n_{k+1})\cdot n_{k+2}}{n_k\cdot n_{k+2}}.}
$$

**证明。**对 $n_k\cdot n_{k+1}=0$ 求导，得 $v_k+v_{k+1}(n_k\cdot n_{k+2})=0$。又由框架递推，$n_k\cdot n_{k+2}=-1/q_k$ 且 $(n_k\times n_{k+1})\cdot n_{k+2}=\kappa_k/q_k$。

### 推论 3.3（有序复三重比较保留带向曲率）

将方向表示为 qubit 纯投影 $P_j=(I+n_j\cdot\sigma)/2$，记

$$
B_k=\operatorname{tr}(P_kP_{k+1}P_{k+2}),\quad d_k=n_k\cdot n_{k+2},\quad
\tau_k=(n_k\times n_{k+1})\cdot n_{k+2}.
$$

相邻内积为零时，Pauli 乘法给出

$$
B_k=\frac{1+d_k+i\tau_k}{4},\qquad
\kappa_k=-\frac{4\operatorname{Im}B_k}{4\operatorname{Re}B_k-1}.
$$

分母为 $d_k<0$，包括 $B_k=0$ 也无奇点。这里使用 v87 已保留的有序复相干读数，不把三重投影恒等式宣称为新的量子假设。仅保留无向实内积一般只能恢复 $|\kappa_k|$；有序复比较还保留带向信息。整体钟速 $v_0$ 仍须由所选参数提供。

### 命题 3.4（圆的层间四循环与归一化的信息损失）

若 $\kappa_0$ 为常数，则从第一切向层开始 $\kappa_k=0$（$k\ge1$），$n_{k+2}=-n_k$（$k\ge1$），$n_{k+4}=n_k$（$k\ge1$）。而不同原轨迹可以具有完全相同的第一切向层及全部更高层。

**证明。**常数曲率使递推中的 $\kappa_1=0$，随后全部为零，代入框架递推即得四循环。取正则纬圈

$$
 n_h(t)=\bigl(\sqrt{1-h^2}\cos t,\sqrt{1-h^2}\sin t,h\bigr),\qquad -1<h<1,
$$

它们的单位切向都等于 $(-\sin t,\cos t,0)$，故全部更高层也相同。四循环是层指标的循环，不是物理时间回返；任意正但非恒定的钟速下层间关系仍成立，不能据此推出固定时间周期。归一化会丢掉原始速度和纬度信息。

**白话图景。**切箭头可以一直追下去，但追出来的可能只是几个方向反复出现。无限层不必带来无限的新内容。不同纬度的圆还可以给出同一条切箭头轨迹，所以仅凭上层不能自动恢复被归一化省去的原始关系。

<a id="section-4"></a>

## 4. 逆向重建：局部可以继续，全球必须配平

### 定理 4.1（全部局部正则前驱）

给定光滑正则球面曲线 $m$，记其速度、切向、法向与带向测地曲率为 $v_m,T_m,N_m,\kappa_m$。若

$$
\dot\beta=v_m\kappa_m,qquad -\frac\pi2<\beta<\frac\pi2,
$$

则

$$
\boxed{n=-\cos\beta\,T_m+\sin\beta\,N_m}
$$

是正则球面曲线，且其正向单位切向恰为 $m$。更精确地，

$$
\dot n=v_m\cos\beta\,m,\qquad v_n=v_m\cos\beta,\qquad \kappa_n=\tan\beta.
$$

反过来，每个正向单位切向为 $m$ 的局部正则前驱都由此给出，自由度为积分常数 $\beta(t_0)$。

**证明。**式中的两个向量正交且单位，故 $|n|=1$、$n\cdot m=0$。用目标层的 Darboux 关系

$$
\dot T_m=v_m(-m+\kappa_mN_m),\qquad \dot N_m=-v_m\kappa_mT_m
$$

逐项求导，$\dot\beta=v_m\kappa_m$ 恰好消去 $T_m$ 和 $N_m$ 的多余项，得到 $\dot n=v_m\cos\beta,m$。又有 $N_n=n\times m=\sin\beta T_m+\cos\beta N_m$，所以

$$
\dot m=v_mT_m=v_m\cos\beta(-n+\tan\beta N_n).
$$

反向若 $m$ 是 $n$ 的正向单位切向，取 $\beta=\arctan\kappa_n$，由 $\kappa_nds_n=d(\arctan\kappa_n)$ 得 $\dot\beta=v_m\kappa_m$；反解框架递推即回到上式，故没有遗漏其他局部正则前驱。

对任意 $\beta(t_0)\in(-\pi/2,\pi/2)$，在足够小的区间上总能维持严格区间条件。若要求整个给定区间，则必须存在常数 $\beta_0$ 使

$$
-\frac\pi2<\beta_0+\int_{t_0}^t v_m(u)\kappa_m(u)\,du<\frac\pi2
$$

全程成立；这既必要又充分。

**白话图景。**倒着找上一层，要决定当前切箭头原来沿着哪条轨迹走。局部可以选择一个起始倾角，然后按已有弯曲连续接起来。但倾角不能一路越过正则区间，否则上一层会停住或改变方向；全球重建因此有实际约束。

### 定理 4.2（闭合正则前驱的充要条件）

设目标曲线 $m$ 为光滑正则的 $L$-周期曲线，允许自交。令

$$
A(t)=\int_0^t v_m(u)\kappa_m(u)\,du,\qquad 0\le t\le L.
$$

它存在同参数周期的光滑正则前驱，当且仅当

$$
\boxed{A(L)=0,\qquad \max_{[0,L]}A-\min_{[0,L]}A<\pi.}
$$

**证明。**若前驱闭合正则，其曲率为周期函数，故 $\beta=\arctan\kappa_n$ 周期，给出 $A(L)=0$。它在紧区间上的值严格落在 $(-\pi/2,\pi/2)$，因此振幅小于 $\pi$。反之，振幅条件保证区间

$$
\left(-\frac\pi2-\min A,\ \frac\pi2-\max A\right)
$$

非空。任取其中的 $\beta_0$，则 $\beta=\beta_0+A$ 全程满足严格区间条件；$A(L)=0$ 使 $\beta$ 周期，而 $m,T_m,N_m$ 均为光滑周期函数，由逆式构造的 $n$ 因而光滑周期且速度处处为正。

特别地，必要条件是 $\oint_m\kappa_m\,ds_m=0$。非赤道纬圈 $n_h$（$h\ne0$）满足

$$
 v_m=\sqrt{1-h^2},\qquad \kappa_m=\frac h{\sqrt{1-h^2}},\qquad
 \oint\kappa_m\,ds_m=2\pi h\ne0,
$$

因此没有光滑正则的闭合前驱。若要求整个 $t\in\mathbb R$ 上的正则前驱，也会因 $\beta(t)=\beta_0+ht$ 终将离开允许区间而失败。若内部参照闭路还带有非平凡 holonomy，必须保留相应的扭转边界条件，不能直接替换成这里的周期假设。

**白话图景。**向上追变化，可以没有最高有限层；向下重建却要检查一圈走完后的总转向。若这份转向无法配平，就接不成一条不停顿的闭合下层轨迹。

<a id="section-5"></a>

## 5. 同球表示需要保留的尺度、补态与完整相位

首先区分三种曲率：$\kappa_k$ 是一维轨迹的测地曲率，球面的 Riemann 曲率描述其度量，连接曲率 $F_{\mu\nu}$ 比较两个独立方向的延续次序。它们可以通过具体几何结构相接，不能仅因同名而直接等同。一条曲线的任意高阶导数，也不会自动供应第二个独立比较方向。

由 Darboux 关系，

$$
\dot T=v(-n+\kappa N),\qquad \nabla^{S^2}_tT=v\kappa N.
$$

大圆的 $\kappa=0$：前者仍非零，后者为零。若最初就出现停顿，也不能任意补上方向；例如 $n(t)=(\cos t^2,\sin t^2,0)$ 的单位切向在 $t=0$ 左右趋向相反向量，不存在连续的双侧归一切向延拓。

### 命题 5.1（Bloch 切箭头不是 Hilbert 正交补态）

把 $n$ 与单位切向 $T$ 分别解释成 qubit 纯态投影 $P_n=(I+n\cdot\sigma)/2$、$P_T=(I+T\cdot\sigma)/2$，则

$$
\operatorname{tr}(P_nP_T)=\frac{1+n\cdot T}{2}=\frac12.
$$

因此它们不是 Hilbert 正交态。非零水平 ket 切向归一后 $\xi/\|\xi\|\in\psi^\perp$ 在 qubit 中对应的 Bloch 点反而是 $-n$。

**证明。**第一式由 Pauli 乘法与 $n\cdot T=0$ 得到。在二复维空间，$\psi^\perp$ 为唯一正交纯态射线，其投影是 $I-P_n=(I-n\cdot\sigma)/2$，故对应 $-n$。更直接地取 $\psi=(1,0)$、水平切向 $\xi=(0,a)$，则

$$
\dot P=\ket\xi\bra\psi+\ket\psi\bra\xi,qquad
\dot n=(2\operatorname{Re}a,2\operatorname{Im}a,0).
$$

归一 ket 的射线却始终为 $\ket1$；切箭头方向记录在相对相位中。

### 命题 5.2（无限轨迹层不能单独恢复完整 Hamiltonian）

给定任意光滑 Bloch 路 $n(t)$，对任意实函数 $\lambda(t),c(t)$ 定义

$$
\boxed{H_{\lambda,c}(t)=\frac\hbar2
\bigl[n\times\dot n+\lambda(t)n\bigr]\cdot\sigma+c(t)I.}
$$

它们都产生同一给定初始射线的 Bloch 轨迹。因此全部递归切向与曲率也相同，但完整态相位和对其他输入的作用不由该轨迹确定。

**证明。**$H=(\hbar/2)\omega\cdot\sigma+cI$ 的 Bloch 方程为 $\dot n=\omega\times n$，而

$$
[n\times\dot n+\lambda n]\times n=\dot n.
$$

若 $\psi_0$ 是 $H_{0,0}$ 的完整态，则另一 Hamiltonian 的对应解为

$$
\psi_{\lambda,c}(t)=\exp\left[-i\int_{t_0}^t\left(\frac{\lambda(u)}2+\frac{c(u)}\hbar\right)du\right]\psi_0(t).
$$

非零 $\lambda$ 项一般还改变其他输入射线的演化。因而本节不能替代 v86 的全部输入共同场条件，也不能替代 v87 的完整相干比较。单个球面点有两个实自由度；连同单位切向的定向框架已有三个。一般 $d$ 维纯态空间 $\mathbb CP^{d-1}$ 有 $2d-2$ 个实维度，$d>2$ 时维数已经不同。

**白话图景。**把切箭头画成球面上的一个新点是可以的，但这个新点不是原态的正交补态。箭头朝哪边，还依赖补态相对于原态的相位。若只保留各自的射线，原本不同的箭头方向就会被压成同一个补态。

本节是轨迹的微分层级。后续候选所讨论的操作分辨率，则要求对可见代数的压缩保持有序复比较、正性与组合一致性。归一切向依赖历史导数，既不是仅由当前态确定的普遍映射，也不自动是一条可执行量子通道。

<a id="section-6"></a>

## 6. 内部分辨率：先定义左比较，再增加一个约束

本节继承已经建立的有限复矩阵关系、效果与组合接口。新的问题是：同一份内容换到较粗的分辨率后，哪些有序比较仍能完整接续？我们不重新假定一个量子态空间，也不把普通条件期望或塔律再次列成新公理。

### 定义 6.1（忠实内部校准与可见代数）

固定 $M=M_d(\mathbb C)$，取

$$
\rho>0,\qquad \operatorname{tr}\rho=1,\qquad
\phi_\rho(x)=\operatorname{tr}(\rho x).
$$

这里的 $\rho$ 是当前比较接口的**忠实内部校准**，不是关于全局 $\Omega$ 必须处于混合态的断言。取共享单位元的 $*$-子代数 $A\subset M$，将 $A$ 称为当前分辨率的可见关系。它对加法、乘法及取伴随封闭，因而同一分辨率内可以继续组合关系。

忠实性使

$$
\langle x,y\rangle_\rho:=\phi_\rho(x^\dagger y)
$$

成为整个矩阵空间上的内积，而非带零方向的半内积。这可以由一组张成当前载体的内部纯态，以严格正权重混合得到；它是一种校准选择，不指定整体唯一或最终物理态。

### 定义 6.2（左比较代表）

记 $E_{\rho,A}:M\to A$ 为上述内积下到 $A$ 的正交投影。它由

$$
\phi_\rho\!\left(a^\dagger E_{\rho,A}(x)\right)
=\phi_\rho(a^\dagger x)\qquad(a\in A,x\in M)
$$

唯一确定。固定 $(\rho,A)$ 时简写为 $E$。有限维正交投影保证该代表总存在。若两个代表之差 $z\in A$ 与所有 $a\in A$ 的左比较都为零，取 $a=z$ 即有 $\operatorname{tr}(\rho z^\dagger z)=0$，从而 $z=0$；唯一性也迫使逐个代表的选择线性。

### 定义 6.3（本轮唯一新候选 $C_{88}$：右序延续相容）

已由左比较定义的同一个 $E$，还应满足

$$
\boxed{\phi_\rho(E(x)a)=\phi_\rho(xa)\qquad(a\in A,x\in M).}
$$

这是一条作用于两个关系元的约束：待压缩内容 $x$ 与仍可见关系 $a$。由于 $A$ 对取伴随封闭，左比较也可写成 $\phi_\rho(aE(x))=\phi_\rho(ax)$。比较值一般是复数，包含有序相关的实部与虚部；不能只用两个单次概率或只保留实部替代。对 Hermitian 的 $a,x$，两种次序的和与差分别记录对称相关与交换子相关。

**白话图景。**一层分辨率把细节收起来以后，可见关系既要接得上原内容的左边，也要接得上右边。只保持一个次序，压缩后得到的东西可能已经不能作为合法读口。两个次序都能接续，才允许把这次压缩当作同一套关系中的完整代表。

<a id="section-7"></a>

## 7. 主等价定理：从有序比较推出完全正性

### 定理 7.1（$C_{88}$ 的五种等价形式）

对固定忠实校准 $\rho$、可见代数 $A$ 及左比较投影 $E$，下列条件等价：

1. $E$ 满足右序延续相容。
2. $E$ 保持伴随：$E(x^\dagger)=E(x)^\dagger$。
3. $E$ 是保持 $\phi_\rho$ 的条件期望：保持单位元、完全正、幂等，像恰为 $A$，且 $E(axb)=aE(x)b$ 对 $a,b\in A$ 成立。
4. $A$ 对锚的模流稳定：$\rho^{it}A\rho^{-it}=A$ 对所有 $t\in\mathbb R$ 成立。
5. 在有限子代数标准分块

   $$
   \mathcal H=\bigoplus_\alpha(\mathbb C^{n_\alpha}\otimes\mathbb C^{m_\alpha}),\qquad
   A=\bigoplus_\alpha(M_{n_\alpha}\otimes I_{m_\alpha}),
   $$

   下，

   $$
   \boxed{\rho=\bigoplus_\alpha p_\alpha\,\sigma_\alpha\otimes\tau_\alpha,}
   $$

   其中 $p_\alpha>0$、$\sum p_\alpha=1$，$\sigma_\alpha,\tau_\alpha$ 为忠实归一密度矩阵。

这是保态条件期望的有限矩阵版本；标准来源是 Takesaki 定理及其有限维表述 [8](#ref-takesaki)–[9](#ref-bardet)。本轮候选的作用，是以唯一新增的二元右序比较条件选出相容的 $(\rho,A)$，而不是声称条件期望定理本身首次出现。

### 引理 7.2（左比较已经给出的性质）

无须 $C_{88}$，左比较投影已经满足

$$
E|_A=\operatorname{id}_A,\qquad E^2=E,\qquad E(I)=I,
\qquad \phi_\rho\circ E=\phi_\rho,
$$

以及左模性质 $E(bx)=bE(x)$（$b\in A$）。

**证明。**前四项来自投影、$I\in A$ 及以 $a=I$ 进行左比较。对 $a,b\in A$，

$$
\langle a,E(bx)\rangle_\rho
=\langle b^\dagger a,x\rangle_\rho
=\langle b^\dagger a,E(x)\rangle_\rho
=\langle a,bE(x)\rangle_\rho,
$$

唯一性给出左模性质。

### 定理 7.3（主定理前三项的解析证明）

右序相容推出保持伴随。将左比较用于 $x^\dagger$ 并取复共轭，得

$$
\phi_\rho(E(x^\dagger)^\dagger a)=\phi_\rho(xa).
$$

若右比较也成立，令 $z=E(x)-E(x^\dagger)^\dagger\in A$，便有 $\phi_\rho(za)=0$ 对全部 $a$ 成立，取 $a=z^\dagger$ 并用忠实性得 $z=0$。反过来，保持伴随时上式的取共轭直接给出右比较。

保持伴随与左模性结合给出右模性：

$$
E(xb)=E((b^\dagger x^\dagger)^\dagger)=E(b^\dagger x^\dagger)^\dagger=E(x)b.
$$

**正性。**若 $x\ge0$，则 $y=E(x)$ 为 Hermitian。若 $y$ 有负谱，取其负谱投影 $p\in A$，则 $pyp\le0$ 且非零，忠实性给 $\phi_\rho(pyp)<0$。另一方面双模性和保校准性给

$$
\phi_\rho(pyp)=\phi_\rho(E(pxp))=\phi_\rho(pxp)\ge0,
$$

矛盾，故 $E(x)\ge0$。

**完全正性。**对任意 $k$，定义 $E^{(k)}=\operatorname{id}_{M_k}\otimes E$。放大后的映射保持伴随、单位元、放大态

$$
\Phi_k(X)=\frac1k\sum_{j=1}^k\phi_\rho(X_{jj}),
$$

以及 $M_k(A)$-双模性。若 $X\ge0$ 而 $Y=E^{(k)}(X)$ 有负谱，负谱投影 $Q\in M_k(A)$ 给出 $\Phi_k(QYQ)<0$，但

$$
\Phi_k(QYQ)=\Phi_k(E^{(k)}(QXQ))=\Phi_k(QXQ)\ge0,
$$

矛盾。因此所有矩阵放大都正，$E$ 完全正。反向由第三项的双模性与保校准性立即得右序比较。

**白话图景。**一个方向的比较先把代表定下来；另一个方向再检查它能否作为同一个内容使用。这次检查锁住了取伴随和两侧组合，于是负读数没有藏身之处。把接口放大到任意有限辅助系统后，同一论证仍然成立，完全正性因此出现。

<a id="section-8"></a>

## 8. 锚与切口如何配套：有限分块及模流

采用既有有限子代数分块，写成定理 7.1 的直和形式，并记 $P_\alpha$ 为各中心块投影。

### 命题 8.1（所有相容压缩的显式形式）

条件 3 成立当且仅当校准满足

$$
\rho=\bigoplus_\alpha p_\alpha\sigma_\alpha\otimes\tau_\alpha;
$$

此时唯一映射为

$$
\boxed{
E(x)=\bigoplus_\alpha
\left[(\operatorname{id}\otimes\phi_{\tau_\alpha})(P_\alpha xP_\alpha)\right]\otimes I_{m_\alpha},
\qquad \phi_{\tau_\alpha}(b)=\operatorname{tr}(\tau_\alpha b).}
$$

**证明。**双模性给出 $E(P_\alpha xP_\beta)=0$（$\alpha\ne\beta$）。在一个固定块内取矩阵单位 $e_{ij}$。像落在 $M_n\otimes I_m$，且

$$
E(e_{11}\otimes b)=f(b)e_{11}\otimes I.
$$

两侧矩阵单位作用得到 $E(e_{ij}\otimes b)=f(b)e_{ij}\otimes I$。正性及保单位元给 $f(b)\ge0$（$b\ge0$）与 $f(I)=1$，故 $f(b)=\operatorname{tr}(\tau b)$。保校准性对跨块矩阵成立迫使 $P_\alpha\rho P_\beta=0$。令 $\rho_\alpha=P_\alpha\rho P_\alpha$、$r_\alpha=\operatorname{tr}_{m_\alpha}\rho_\alpha$，则对本块任意 $x$，

$$
\operatorname{tr}(\rho_\alpha x)
=\operatorname{tr}\bigl((r_\alpha\otimes\tau_\alpha)x\bigr),
$$

从而 $\rho_\alpha=r_\alpha\otimes\tau_\alpha$。归一化 $r_\alpha$ 得到块乘积形式。反向将此形式代入显式公式，左右两种次序都化为同一块迹配对，故满足 $C_{88}$。

### 命题 8.2（模流稳定的有限证明）

块乘积形式与

$$
\rho^{it}A\rho^{-it}=A\qquad(t\in\mathbb R)
$$

等价。

**证明。**块乘积形式给出

$$
\rho^{it}=\bigoplus_\alpha p_\alpha^{it}\sigma_\alpha^{it}\otimes\tau_\alpha^{it},
$$

从而 $a_\alpha\otimes I$ 被送到 $(\sigma_\alpha^{it}a_\alpha\sigma_\alpha^{-it})\otimes I$。反过来，模流在 $A$ 上是连续自同构群，只能置换有限个极小中心投影；连续性迫使逐个固定。固定一块，令 $L=\log\rho_\alpha$，在 $t=0$ 求导得 $[L,a\otimes I]\in M_n\otimes I$。以隐藏空间 Hermitian 基 $B_0=I,B_1,\ldots,B_{m^2-1}$ 展开 $L=\sum A_\mu\otimes B_\mu$。线性独立性要求 $[A_\mu,a]=0$ 对 $\mu>0$ 及全部 $a\in M_n$ 成立，这些 $A_\mu$ 因而为标量；于是 $L=L_{\rm vis}\otimes I+I\otimes L_{\rm hid}$，指数化并归一化即得块乘积。

模流参数在这里无量纲，$-\log\rho$ 是由校准定义的比较生成元；本定理没有证明它等于物理能量，也没有证明模流就是已经标定的物理时钟。

**白话图景。**切口不是任意画的。当前锚若正在用某些跨块相干或可见与隐藏之间的关系，就不能把它们收起来以后还宣称全部有序比较原样留下。合法切口要求锚与分块配套；在每个块内，可见部分和隐藏部分按乘积接合。模流稳定是同一件事的动态写法，不另增加一套运动公理。

<a id="section-9"></a>

## 9. 可观测量与状态的不同映射，以及删条件反例

### 命题 9.1（状态对偶与显式 Kraus 表示）

显式压缩的状态对偶 $E_*$ 由

$$
\boxed{E_*(s)=\bigoplus_\alpha
\left[\operatorname{tr}_{m_\alpha}(P_\alpha sP_\alpha)\right]\otimes\tau_\alpha}
$$

定义，满足 $\operatorname{tr}(E_*(s)x)=\operatorname{tr}(sE(x))$。它完全正、迹保持、幂等且 $E_*(\rho)=\rho$。

在每块写 $\tau_\alpha=\sum_\ell t_{\alpha\ell}|\ell\rangle\langle\ell|$，定义

$$
K_{\alpha\ell q}=\sqrt{t_{\alpha\ell}}
(I_{n_\alpha}\otimes|\ell\rangle\langle q|)_\alpha.
$$

则

$$
E_*(s)=\sum_{\alpha,\ell,q}K_{\alpha\ell q}sK_{\alpha\ell q}^\dagger,
\quad E(x)=\sum_{\alpha,\ell,q}K_{\alpha\ell q}^\dagger xK_{\alpha\ell q},
\quad \sum K_{\alpha\ell q}^\dagger K_{\alpha\ell q}=I.
$$

因此 $E$ 是可观测量图像中的保单位元完全正映射，通常不保持普通矩阵迹；$E_*$ 是其状态对偶，保持迹。二者不能混写，也不能把任意 $E(s)$ 直接视为归一密度矩阵。由公式，$E$ 自身保持普通迹当且仅当 $\tau_\alpha=I_{m_\alpha}/m_\alpha$，这才回到 Hilbert–Schmidt 自伴迹条件期望 $E_A$。对固定旧映射，

$$
\phi_\rho\circ E_A=\phi_\rho
\Longleftrightarrow E_A(\rho)=\rho
\Longleftrightarrow \rho\in A.
$$

因此允许映射随锚改变，与坚持同一个普通迹映射，是两个不同要求。

### 命题 9.2（删除右序相容会产生负效果）

左比较投影可以保持单位元、保持校准、幂等，却不保持正性。

**证明。**取 $A\subset M_2$ 为对角代数，并取忠实校准

$$
\rho=\begin{pmatrix}1/2&1/4\\1/4&1/2\end{pmatrix}.
$$

直接解左比较得

$$
E(x)=\operatorname{diag}\left(x_{11}+\frac{x_{12}}2,\ x_{22}+\frac{x_{21}}2\right).
$$

合法的秩一效果

$$
 x=\frac1{10}\begin{pmatrix}1&-3\\-3&9\end{pmatrix}
$$

被送到

$$
\boxed{E(x)=\operatorname{diag}(-1/20,3/4).}
$$

若把这个输出当作效果，沿第一基态读取就出现负值。此外 $E(\sigma_y)=\operatorname{diag}(-i/2,i/2)$，连 Hermitian 性也不保。取 $P_0=|0\rangle\langle0|$，右序比较失败：

$$
\phi_\rho(E(\sigma_y)P_0)=-i/4,qquad
\phi_\rho(\sigma_yP_0)=+i/4.
$$

这说明右序条件确实排除了一个正输入被写成带负分量输出的压缩。

**白话图景。**左边的复读数单独看似乎足够，但它没有锁住取伴随和右侧组合。删掉右序条件，正的输入可以被写成带负分量的输出；相容的双向比较正是把这种压缩排除的最小检验。

<a id="section-10"></a>

## 10. 全锚要求的分类，以及二元三维图景

### 定理 10.1（固定代数、允许映射随锚改变）

固定共享单位元的 $A\subset M_d$。若对每个忠实校准 $\rho$ 都要求存在满足 $C_{88}$ 的 $E_{\rho,A}$，则恰有

$$
\boxed{A=\mathbb CI\quad\text{或}\quad A=M_d.}
$$

**证明。**若 $A$ 有至少两个中心块，从 $I/d$ 出发加上足够小的跨块 Hermitian 扰动，得到的忠实 $\rho$ 不按中心块对角，违反块乘积形式。因此 $A$ 只能是单块 $M_n\otimes I_m$。若 $n,m\ge2$，取非零无迹 Hermitian $B\in M_n,C\in M_m$，令

$$
\rho=\frac{I+\varepsilon B\otimes C}{nm},qquad
0<|\varepsilon|<\frac1{\|B\|_{\rm op}\|C\|_{\rm op}}.
$$

它忠实，两个边缘都是最大混合，但本身不是乘积，仍违反块形式。因此 $n=1$ 或 $m=1$。反过来标量代数用 $E(x)=\phi_\rho(x)I$，全代数用恒等映射。

### 定理 10.2（连压缩映射也固定的全锚要求）

若同一个固定 $E$ 对每个忠实 $\rho$ 都保持 $\phi_\rho$，则 $E=\operatorname{id}$，其像为 $M_d$。

**证明。**对任意 $x$ 有 $\operatorname{tr}[\rho(E(x)-x)]=0$。先取 $\rho=I/d$，再取 $I/d$ 加上足够小的任意无迹 Hermitian 扰动，便知 $E(x)-x$ 与所有 Hermitian 矩阵的迹配对为零；这些矩阵复线性张成 $M_d$，故 $E(x)=x$。

### 命题 10.3（qubit 的二元三维相容条件）

对 $M_2$，任一非平凡真子代数可写成

$$
A_{\mathbf n}=\operatorname{span}_{\mathbb C}\{I,\mathbf n\cdot\boldsymbol\sigma\},\qquad |\mathbf n|=1.
$$

对忠实校准 $\rho_{\mathbf r}=(I+\mathbf r\cdot\boldsymbol\sigma)/2$、$|\mathbf r|<1$，

$$
\boxed{(\rho_{\mathbf r},A_{\mathbf n})\text{ 满足 }C_{88}
\Longleftrightarrow \mathbf r\times\mathbf n=0.}
$$

**证明。**模流稳定等价于 $[\rho_{\mathbf r},\mathbf n\cdot\boldsymbol\sigma]=0$，而 Pauli 乘法给

$$
[\rho_{\mathbf r},\mathbf n\cdot\boldsymbol\sigma]
=i(\mathbf r\times\mathbf n)\cdot\boldsymbol\sigma.
$$

相容时的映射是

$$
E_{\mathbf n}(x)=P_+xP_++P_-xP_-
=\frac12\left[x+(\mathbf n\cdot\boldsymbol\sigma)x(\mathbf n\cdot\boldsymbol\sigma)\right].
$$

它保留轴向分量；要原样保持校准，校准向量就必须位于该轴。两个不共线的非零锚已经足以排除同一个非平凡轴；中心锚 $\mathbf r=0$ 与所有轴相容。

### 命题 10.4（锚与代数联动的协变性）

对任意酉 $U$，

$$
E_{U\rho U^\dagger,\,UAU^\dagger}(UxU^\dagger)
=UE_{\rho,A}(x)U^\dagger.
$$

**证明。**将 $UaU^\dagger$ 作为新测试元，利用迹的循环性验证右端保持新校准下的左比较；唯一性给出公式。若原来满足右比较，变换后也满足。因此 $C_{88}$ 相容性随这对内部数据一起变换。

**白话图景。**“锚可以相对改变”不要求所有锚无损使用同一个固定切口。在三维球图里，一个切口保留一条轴；两个不共线的锚已经会对这个固定选择提出冲突。把锚和切口一起旋转，关系仍然完整。若坚持切口完全不动而又要照顾每个锚，就只能保留全部关系，或者退到只剩一个标量的可见层。

<a id="section-11"></a>

## 11. 候选的准确范围：完整比较代表，不是所有信息处理的禁令

$C_{88}$ 规定的是一种较强而明确的接口：对每个完整关系 $x$，寻找同一可见代数内的代表 $E(x)$，并保持它与全部可见关系的两种次序的复比较。某个 $(\rho,A)$ 不满足条件，结论只是这个完整、精确的代表要求不能实现。

对任意联合态，取部分迹仍然是合法的状态操作；把态限制到子代数上的可见读数，也总有定义。这些操作可以丢失相关，不要求把所有完整关系都替换成保持左右有序比较的代表，更不要求其对偶在原载体上固定原来的全部相关态。所以本定理不会禁止对关联态取部分迹、进行测量或使用有损分辨率。本轮也没有从校准相容性推出具体装置的能耗、时长或误差容限。

忠实性同样有明确作用。若 $\rho$ 有零特征值，

$$
\phi_\rho(x^\dagger x)=0\Longleftrightarrow x\sqrt\rho=0
$$

允许非零 $x$，唯一代表的证明随即失效。纯锚只测试一个支撑方向；这时必须另行指定支持空间、不可见零方向及组合接口，不能把本节的唯一性与分类直接套用到任意纯锚。用忠实校准进行证明，不改变项目中纯态本身的定义。

普通归一迹 $\rho=I/d$ 是有用特例：它是完整矩阵代数中对所有内部酉变换不变的唯一归一校准。此时模流恒等，每个共享单位元的 $*$-子代数都相容，恢复项目既有的迹条件期望。这个中性数学校准不宣称物理整体处于最大混合态。改用一般忠实校准时，新增限制才显现：切口必须对该校准的模流稳定。

因此 $C_{88}$ 的推进可以精确定位为

$$
\text{右序比较相容}
\Longrightarrow
\text{合法的完整压缩}
\Longleftrightarrow
\text{锚与可见代数配套}.
$$

**白话图景。**整体内部可以有很多种看法，也可以有许多层分辨率。每次收起细节，都要先说清楚想保住哪些比较。若要求所有有序比较完整接续，锚和切口就必须相容；若接受丢失一部分关系，通常的信息处理仍然允许。

<a id="section-12"></a>

## 12. 内容即地址：相对分辨率中的精确定义

现在以满足 $C_{88}$ 的一对 $(\rho,\mathcal A)$ 为一个合法的精确比较切口。这里的“精确”指所声明的有序比较被严格保留，不指任何内部观察者同时知道全部内容。

### 定义 12.1（当前切口的内容地址）

对 $x,y\in M_d$，定义

$$
 x\sim_{\rho,\mathcal A}y
 \quad\Longleftrightarrow\quad
 \phi_\rho\bigl(a^\dagger(x-y)\bigr)=0
 \quad\text{对全部 }a\in\mathcal A.
$$

相应等价类的规范代表为 $E_{\rho,\mathcal A}(x)$。

### 命题 12.2（地址与可见内容一致）

有

$$
 x\sim_{\rho,\mathcal A}y
 \quad\Longleftrightarrow\quad E(x)=E(y).
$$

若 $C_{88}$ 成立，这也等价于全部反序比较 $\phi_\rho((x-y)a)=0$ 同时成立。

**证明。**由正交投影定义，左比较只依赖 $E(x-y)$。若全部为零，取 $a=E(x-y)$ 并用忠实内积得 $E(x-y)=0$；反向显然。右序条件把读数传递到同一代表；若所有右序比较为零，取 $a=E(x-y)^\dagger$，得到 $\phi_\rho(E(x-y)E(x-y)^\dagger)=0$，故代表仍为零。

这是当前切口的地址同一，不是把暂时看不见的历史永久删除。若之后允许的门能将隐藏差别带回可见读口，未来可区分的两份内容仍应保留不同的完整历史地址。只有可见比较对所声明的全部后续操作封闭时，当前等价类才同时承担那个操作范围内的完整身份。

**白话图景。**“内容就是地址”可以落实为：在当前分辨率里，凡是每种可见比较都分不出差别的内容，使用同一个代表。以后增加读口，原来相同的地址可以被细分；如果未来还能找回某段历史，就不能现在把那段历史当作从未存在。

<a id="section-13"></a>

## 13. 递归分辨率塔：细节、误差与条件方差

### 定义 13.1（共同锚下的相容分辨率塔）

固定一个忠实 $\rho$，取共享单位元的嵌套代数

$$
\mathcal A_m\subseteq\mathcal A_{m+1}\subseteq\cdots\subseteq\mathcal A_n,
$$

每一对 $(\rho,\mathcal A_j)$ 均满足 $C_{88}$。记对应映射为 $E_j$。层指标指可保留的比较集合，不自动是物理时间、能量或微分次数。

### 定理 13.2（塔律与误差分解）

若 $i\le j$，则

$$
E_iE_j=E_jE_i=E_i.
$$

令 $d_jx=(E_{j+1}-E_j)x$，则不同层的 $d_jx$ 在同一 GNS 内积中正交，且

$$
\boxed{\|x-E_mx\|_\rho^2
=\sum_{j=m}^{n-1}\|d_jx\|_\rho^2+\|x-E_nx\|_\rho^2.}
$$

**证明。**嵌套子空间的正交投影满足 $E_jE_i=E_i$；取共同内积下的伴随得到 $E_iE_j=E_i$。因此 $E_{j+1}-E_j$ 是到 $\mathcal A_{j+1}\cap\mathcal A_j^{\perp_\rho}$ 的正交投影。不同层细节相互正交，最终残差正交于 $\mathcal A_n$，展开后取平方范数即得。

塔律本身是旧有正交投影恒等式，即使某些左比较投影不为正，它仍可成立。$C_{88}$ 的实质是保证每层还具有完全正的操作解释。各层使用同一个 $\rho$；若任意更换锚而不声明相容转换，不能直接套用共同正交分解。

### 命题 13.3（不确定性与分辨率残差的精确关系）

对 Hermitian $x$，定义 $\operatorname{Var}_\rho(x)=\phi_\rho(x^2)-\phi_\rho(x)^2$。则

$$
\boxed{\operatorname{Var}_\rho(x)=\operatorname{Var}_\rho(E_mx)+\|x-E_mx\|_\rho^2.}
$$

更一般地，算符条件方差

$$
V_i(x)=E_i(x^\dagger x)-E_i(x)^\dagger E_i(x)\ge0
$$

满足

$$
V_i(x)=E_i(V_j(x))+V_i(E_jx),\qquad i\le j.
$$

**证明。**保态性给 $\phi_\rho(E_mx)=\phi_\rho(x)$，正交性给

$$
\|x\|_\rho^2=\|E_mx\|_\rho^2+\|x-E_mx\|_\rho^2,
$$

相减即得第一式。完全正保单位元映射的 Schwarz 不等式给 $V_i(x)\ge0$。将右端展开并用塔律与保持伴随，即得第二式。

例如取 $\mathcal A=M_2$、$\rho=I/2$、$x=\sigma_z$，分辨率残差为零但 $\operatorname{Var}_\rho(\sigma_z)=1$。分辨率误差与量子不确定性有联系，也各有位置。

**白话图景。**每提高一层分辨率，就把原来混在残差里的某些关系单独读出来。各层补出的细节有精确账：已经读出的加上尚未读出的，等于原来的总误差。但即使一层已经保留全部算符，量子读数仍可以有分散。

<a id="section-14"></a>

## 14. 每个二元关系怎样再进入有限三维球面

对任意两份比较内容 $x,y\in M_d$，记

$$
 a=\|x\|_\rho^2,\qquad b=\|y\|_\rho^2,qquad c=\langle x,y\rangle_\rho.
$$

对应 Gram 块

$$
G(x,y)=\begin{pmatrix}a&c\\\bar c&b\end{pmatrix}\ge0,
\qquad \Delta=ab-|c|^2\ge0.
$$

这些内容可以是可观测关系、切向、粗化代表或细节残差，$x,y$ 无须都是正算符。因此这首先是比较向量的球面表示。

### 命题 14.1（关系球与尺度账本）

若 $a,b>0$，则

$$
\boxed{q_\rho(x,y)=\frac1{\sqrt{ab}}
\bigl(\operatorname{Re}c,\operatorname{Im}c,\sqrt{ab-|c|^2}\bigr)\in S^2_+.}
$$

只要同时保留 $a,b$、共同历史身份与相位比较协议，就能由这个球点恢复整个二元 Gram 块，因为 $c=\sqrt{ab}(q_1+iq_2)$。等价的标准坐标是

$$
\frac G{a+b}=\frac12(I+r\cdot\sigma),\qquad
r=\frac{(2\operatorname{Re}c,-2\operatorname{Im}c,a-b)}{a+b},\quad |r|\le1,
$$

并且 $1-|r|^2=4\Delta/(a+b)^2$。若 $a=0$ 或 $b=0$，忠实性意味着相应向量为零，不能给零向量强行规定一个归一方向；若两者很小，归一图像可能相同而实际强度不同。

### 命题 14.2（同一球面模板不等于把整个理论压成一个量子比特）

不存在将 $\mathbb C^3$ 全部纯态送入一个 qubit 纯态球面、并保留所有两态跃迁概率的映射。

**证明。**取 $\mathbb C^3$ 中三个两两正交纯态。它们的像须是 $\mathbb C^2$ 中三个两两正交的非零向量，与二维性矛盾；等价地，Bloch 球上概率为零要求两点互为对跖，不可能有三个不同点两两互为对跖。

因此可以对所有层复用同一种 $S^2$ 关系模板；不同模板之间的上下文、尺度、相位和公共内容仍须相容拼接。单独一个无标签球点不能代替整个网络。

**白话图景。**可以一直用同一种球来画关系：横向两项画相干比较，第三项画尚未对齐的剩余。下一层的两份关系仍然可以这样画，但球旁边要记住“这是谁与谁的比较”以及“它有多大”。

<a id="section-15"></a>

## 15. 没有最高与最底层：有限界限与一个双向开放模型

### 命题 15.1（固定有限载体的严格分辨率界）

在固定 $M_d$ 内，共享单位元的严格嵌套子代数链，从标量代数起至多有 $d^2-1$ 次严格增长。

**证明。**每次严格包含都使复线性维数至少增加一，而 $M_d$ 的复维数为 $d^2$，初始维数至少为一。

这与球面切向无限递归不冲突：微分层可循环，操作分辨率的严格增长则要求新增可区别方向。

### 定义 15.2（双向开放的局部关系模型）

以整数 $j\in\mathbb Z$ 标记内部端口，每个端口具有矩阵代数 $M_2$。取固定忠实单端口态 $\tau$，在每个有限端口集合 $F$ 上使用

$$
\mathcal M_F=\bigotimes_{j\in F}M_2,
\qquad \phi_F=\bigotimes_{j\in F}\phi_\tau.
$$

不同有限集合通过补单位元嵌入，状态限制相容。记所有有限支撑算符组成的代数为 $\mathcal M_{\rm loc}$，$\mathcal A_n$ 为其中仅支撑在 $j\le n$ 端口上的子代数。

### 定理 15.3（每个有限操作有定义的无首尾分辨率族）

对有限支撑纯张量，定义

$$
E_n\!\left(\bigotimes_{j\in F}x_j\right)
=\left(\prod_{j\in F,\,j>n}\phi_\tau(x_j)\right)
\bigotimes_{j\in F,\,j\le n}x_j,
$$

并在线性组合上延拓；被删除端口理解为补回单位元。则 $E_n$ 良定义、保单位元、完全正、保 $\phi$，满足双序比较和

$$
E_mE_n=E_{\min(m,n)},qquad
\mathcal A_n\subsetneq\mathcal A_{n+1}\quad(n\in\mathbb Z).
$$

**证明。**任何有限支撑输入、比较算符和辅助矩阵只涉及某个有限 $F$。在 $\mathcal M_F$ 中，校准态严格正且跨保留与删除部分因子化，映射恰为前述块公式，具有全部性质。扩大 $F$ 只增加单位因子，$\phi_\tau(I)=1$ 保证定义不变。按两次保留范围的交集直接得塔律。第 $n+1$ 个端口上的非标量算符属于 $\mathcal A_{n+1}$ 而不属于 $\mathcal A_n$，故包含严格。

这是一个没有首个或最后一个有限指标切口的关系模型，且相同 $\tau$ 使整数平移保持规则。每个实际比较仍只使用有限多个端口。模型采用开放端口族与相容产品校准作为明确数据，不是由一个有限球面自动推出它们；共同单位元、总局部代数和标量代数仍然存在。

**白话图景。**有限的一张图，能增加的独立分辨率有限；如果整体允许继续纳入新的内部端口，就能让每个切口前后都还有切口。这给“没有指定的最高层和最低层”一个具体模型，同时保留每次操作的有限性。

<a id="section-16"></a>

## 16. 统一关系场的一个明确载体：随内部条件变化的分辨率

前面给出沿层指标的嵌套关系。现在允许锚与可见代数随内部条件 $z$ 改变。$z$ 可表示内部控制、记录或参照选择；本文不预先把它认作四维时空坐标。

### 定义 16.1（相容分辨率场）

在光滑参数域 $\mathcal B$ 上，给定光滑族

$$
 z\longmapsto(\rho_z,\mathcal A_z),\qquad \rho_z>0,
$$

每一对满足 $C_{88}$，且可见子空间具有固定维数、局部固定代数块型。另外给定实际内部比较的延续规则，以比较不同 $z$ 上的关系。每点相容与跨点怎样延续是两个接口；前者由 $C_{88}$ 分类，后者沿用 v87 的内部参照连接。

令 $\mathcal K=M_d$ 带普通 Hilbert–Schmidt 内积，定义

$$
J_z(x)=x\sqrt{\rho_z},\qquad
\mathcal V_z=J_z(\mathcal A_z),\qquad
\Pi_z=J_zE_zJ_z^{-1}.
$$

因为

$$
\operatorname{tr}[(x\sqrt{\rho_z})^\dagger y\sqrt{\rho_z}]
=\operatorname{tr}(\rho_zx^\dagger y),
$$

$J_z$ 把该点 GNS 比较等距地放入共同 $\mathcal K$，$\Pi_z$ 正是到 $\mathcal V_z$ 的正交投影。固定秩与光滑性保证 $\mathcal V_z$ 构成可见关系向量丛；若秩或块型跳变，须分段讨论。

### 定理 16.2（补向比较给分辨率场曲率）

在已展开的平坦共同参照中，以 $d$ 为延续，定义 $\nabla s=\Pi,ds$，其中 $s=\Pi s$。则

$$
\boxed{F_\Pi=\Pi(d\Pi\wedge d\Pi)\Pi.}
$$

一般地，若环境比较空间带度量相容连接 $D=d+B$，在算符场上定义 $D\Pi=d\Pi+[B,\Pi]$，并记 $F_B=dB+B\wedge B$，则

$$
\boxed{F_\nabla=\Pi F_B\Pi+\Pi(D\Pi\wedge D\Pi)\Pi,\qquad \nabla=\Pi D.}
$$

**证明。**由 $\Pi^2=\Pi$ 求协变导数得 $\Pi(D\Pi)\Pi=0$。对可见截面 $s=\Pi s$，

$$
\begin{aligned}
\nabla^2s
&=\Pi D(\Pi Ds)\\
&=\Pi(D\Pi)\wedge Ds+\Pi D^2s\\
&=\Pi(D\Pi)\wedge(D\Pi)s+\Pi F_B\Pi s.
\end{aligned}
$$

取 $B=0$ 得第一式。这里连接描述邻近比较如何接合，补空间来回的剩余给出诱导曲率。

把 $x,\rho_z,\mathcal A_z$ 同时按 $U_z$ 共轭变换时，$J_z$ 诱导 $\mathcal K$ 上的酉变换 $G_z(X)=U_zXU_z^\dagger$，必须同时变换

$$
\Pi'=G\Pi G^{-1},\qquad D'=GDG^{-1},\qquad F_{\nabla'}=GF_\nabla G^{-1}.
$$

不能在时变或空变换框以后把随之产生的参照连接任意重置为零，再宣称轨迹或曲率改变了。

### 例 16.3（不同分辨率次序的完整二元三维例子）

在 $\rho=I/2$ 的 qubit 上，任意轴 $n\in S^2$ 的代数 $\mathcal A_n=\operatorname{Span}_\mathbb C\{I,n\cdot\sigma\}$ 都满足 $C_{88}$，其粗化为

$$
E_n(v\cdot\sigma)=(n\cdot v)n\cdot\sigma.
$$

于是

$$
(E_nE_m-E_mE_n)(v\cdot\sigma)
=(n\cdot m)[(m\cdot v)n-(n\cdot v)m]\cdot\sigma.
$$

取 $n=e_z$、$m=(e_x+e_z)/\sqrt2$、$v=e_z$，得到 $-\tfrac12\sigma_x\ne0$。所以即使每次粗化都合法、都保持同一个锚，两种非嵌套分辨率的使用次序仍可能有差别。两映射各自完全正，但它们的差不是正通道，也不应直接称为酉闭环输运；沿嵌套塔则由塔律可知次序差为零。

### 例 16.4（曲率的层次）

$\kappa_k$ 衡量一条曲线在球面内相对大圆的弯曲；单位球面自身的 Riemann 曲率描述环境几何；$F_\nabla$ 描述两条独立延续方向的次序差。三者都能以内部比较定义，却不是同一个量。单个参数曲线上的二形式拉回为零，追踪多少次沿线导数都不能单凭这一条轨迹唯一恢复横向的全部场曲率。

锚的模流 $\sigma_t^\rho(x)=\rho^{it}x\rho^{-it}$ 保持每个相容切口，并满足

$$
E_{\rho,\mathcal A}\sigma_t^\rho=\sigma_t^\rho E_{\rho,\mathcal A}.
$$

因为模流保持 $\phi_\rho$，它在 GNS 内积下为酉变换且保持 $\mathcal A$；唯一性或块公式给出交换关系。将它认作实际时钟或能量产生的运动，需要另外说明校准与物理过程的对应。

**白话图景。**每个位置先规定“此刻哪些关系可见”，再规定怎样把前一位置的可见内容接到下一位置。可见方向在整体比较空间里转动时，暂时走入补空间、随后返回的部分会留下次序差，这个剩余就是诱导曲率。锚和切口一起换表示，曲率也一起改写，实际比较保持一致。

<a id="section-17"></a>

## 17. 现有量子规则怎样接回这条关系链

本节收束继承关系，不重开 v84–v87 已经明确的相干执行、内部能量、共同场与伙伴反作用接口。共同复正核、概率标定、实际组合及记录资源仍各有自己的合同。$C_{88}$ 的新增作用，是检验按内生参照定义的精确分辨率是否仍为合法量子接口；它不单独替代下表的全部前件。

| 现有规则 | 已声明的内部关系前件 | 数学结论 |
|---|---|---|
| 复 Hilbert 态空间 | 共同复核、全部有限 Gram 正性、声明张成 | 零范数商及完备化；有限秩切口给有限维载体 |
| Born 效果读数 | 全效果区间上的正、归一、可加读数；既有强度标定 | $p(E)=\operatorname{tr}(\rho E)$，纯准备为向量态 |
| 酉与 Schrödinger 演化 | 全复核保持、可逆且覆盖同一载体；光滑内部钟与相位提升 | 共同酉 $U(t)$，$H=i\hbar\dot U U^\dagger$ |
| 张量积与纠缠 | 独立准备的积核、产品参照张成声明复合载体 | 复合载体与张量积酉同构；一般态可纠缠 |
| 仪器与通道 | 完整记录等距、实际记录初态与完整结果集 | Kraus 分支；忽略记录给完全正保迹通道 |
| 不确定性 | 同一准备上两个偏差向量的共同 Gram 正性 | Robertson–Schrödinger 方差约束 |

### 定理 17.1（共同正关系核给出态载体）

设准备标签上的复核 $k(x,y)$ 的每个有限 Gram 矩阵正半定。以标签为生成元的形式线性空间，按

$$
\left\langle\sum_i c_i[x_i],\sum_jd_j[y_j]\right\rangle
=\sum_{ij}\overline{c_i}d_jk(x_i,y_j)
$$

定义半内积。商掉零范数子空间并完备化，得到由同一核生成的 Hilbert 载体。若核的有限 Gram 秩有共同有限上界，则该载体有限维。

**证明。**任一形式向量只含有限标签，所以 Gram 正性保证范数平方非负。对 $u+zv$ 的范数平方应用正性得到 Cauchy–Schwarz；零范数向量与全部向量正交，构成线性子空间，半内积遂下降为商空间的正定内积。任何另一组具有相同 Gram 的生成向量都给出良定等距；在声明闭张成上它是满射。有限秩上界限制独立向量组的长度。

### 定理 17.2（全效果上的正可加读数给出 Born 迹形式）

在有限维载体上，设 $f$ 定义于全部效果 $0\le E\le I$，满足 $f(E)\ge0$、$f(I)=1$，且 $E+F\le I$ 时 $f(E+F)=f(E)+f(F)$。则存在唯一密度矩阵 $\rho$，使

$$
 f(E)=\operatorname{tr}(\rho E).
$$

**证明。**可加性给 $f(0)=0$，正性给单调性。整数细分给有理齐次性，以有理数从两侧逼近并用单调性得到实齐次性。对正算子 $A$，取正整数 $n\ge\|A\|$，定义 $F(A)=nf(A/n)$；比较共同细分知与 $n$ 无关。用共同 $n$ 得 $F(A+B)=F(A)+F(B)$，于是实线性延拓到 Hermitian 空间。有限维迹配对给唯一 Hermitian $\rho$；对秩一正算子测试得 $\rho\ge0$，而 $F(I)=1$ 给 $\operatorname{tr}\rho=1$。

既有强度标定将纯准备 $\psi$ 对应于 $\rho=|\psi\rangle\langle\psi|$，从而 $p(E)=\langle\psi,E\psi\rangle$；概率语义不是由本轮球面递归单独推出的。

### 定理 17.3（完整关系保持给出酉演化）

设同一完整操作将生成态族 $\psi_x$ 送到 $\phi_x$，保持全部复内积，且两族均张成同一有限载体。则存在唯一酉 $U$ 满足 $U\psi_x=\phi_x$。若相干提升 $U(t)$ 对内部钟为 $C^1$，则

$$
H(t)=i\hbar\dot U(t)U(t)^\dagger=H(t)^\dagger,qquad
 i\hbar\dot\psi(t)=H(t)\psi(t).
$$

**证明。**令 $U(\sum c_x\psi_x)=\sum c_x\phi_x$。相同 Gram 保证每个零线性关系仍映成零，故映射良定义且保持内积；输出张成使其满射，输入张成给唯一性。微分 $UU^\dagger=I$ 得 $\dot UU^\dagger$ 反自伴，故 $H$ 自伴，作用于初态即得运动方程。

只保射线转移概率没有固定共同相干相位；实际相位提升与时间标尺仍由继承接口给出。产品关系及声明张成给出张量积与纠缠的复合载体；记录等距 $V\psi=\sum_eM_e\psi\otimes|e\rangle$ 给 $\sum_eM_e^\dagger M_e=I$，取分支或偏迹得到仪器和完全正保迹通道。最后，$u=(A-\langle A\rangle)\sqrt\rho$、$v=(B-\langle B\rangle)\sqrt\rho$ 的二阶 Gram 行列式非负，给

$$
\operatorname{Var}_\rho(A)\operatorname{Var}_\rho(B)
\ge\left|\operatorname{tr}(\rho\,\delta A\,\delta B)\right|^2,
$$

拆开实部与虚部即得 Robertson–Schrödinger 约束。

**白话图景。**量子的规则可以接成一条完整的关系链：先有共同可比较的内容，才有态空间；共同变化保住全部关系，才有酉运动；内部结果怎样分份，给出概率和记录。本轮继续约束的是怎样看粗、怎样看细，以及这种分辨率能否与实际参照相容。

<a id="section-18"></a>

## 18. 反着推：每个条件究竟排除了什么

在忠实密度 $\rho>0$ 与含单位子代数 $\mathcal A\subseteq M_d(\mathbb C)$ 上，$C_{88}$ 要求同一个左比较代表也保留右序比较。前文已由这一条件推出保持伴随、双模性、正性及完全正性，并将相容性等价刻画为

$$
\sigma_t^\rho(\mathcal A)=\mathcal A,qquad
\sigma_t^\rho(X)=\rho^{it}X\rho^{-it}.
$$

模稳定在此是同一候选的结构判据，不是另外加入的独立运动公理。同一表示变换须同时送出 $\rho\mapsto g\rho g^\dagger$ 与 $\mathcal A\mapsto g\mathcal Ag^\dagger$。

| 删去的条件 | 受影响的两个关系元 | 具体后果 |
|---|---|---|
| 全部有限 Gram 正性 | 两两关系与共同三态实现 | 二阶块都合法，整体仍可能有负范数方向 |
| 共同读数可加性 | 两个可合并效果 $E,F$ | 各自非负归一，不保证合并权重一致 |
| 跨输入复核保持 | 两个准备 $x,y$ 的相干比较 | 各态长度可以不变，却不存在共同线性门 |
| $\rho$ 与分辨率的模相容 | 当前参照与保留代数 | 最小二乘投影可能不保持正性，不能作合法量子分辨率 |
| 完整结果与实际后继 | 当前结果与后续读口 | 同一效果可以对应不同后态；丢弃失败分支会改题 |
| 产品关系及声明张成 | 两个独立准备接口 | 不能仅凭“有两个部分”指定整个复合载体为张量积 |

第一行有极小见证：三阶矩阵对角为 $1$、非对角为 $-3/4$，每个二阶主块正定，却在 $(1,1,1)$ 上有负二次型。第二行可取 $f(E)=[\operatorname{tr}(\rho E)]^2$，它非负且 $f(I)=1$ 但一般不满足可加性。第五行的 $M=I$ 与 $M=X$ 都有同一效果 $I$，实际后继却可被未来读口区分。

这些反例指出的是模型接口差别。缺少某项条件不等于所有剩余过程都逻辑矛盾；它意味着不能再使用依赖该条件的那条推出。尤其不能把一个可见空间的数学投影自动当作实际重置，也不能把隐藏残差 $I-E$ 当作正量子操作。

**白话图景。**反推时要盯住真正冲突的两边：两次结果能不能合并，两条历史能不能继续比较，参照改变后原来的粗细划分还能不能使用。每个条件都应消除一个具体缺口；这样公理才能落到定义之间可以核对的关系上。

<a id="section-19"></a>

## 19. 统一关系场的已闭合部分与继续延伸的边界

本轮可以把状态、轨迹、读口和分辨率统一为内部比较接口，并在可容许接口之间继续比较。“同球”表示同一种二元归一几何可以反复使用；每次的尺度、所保留方向及跨层映射仍属于完整内容。父子核相加和带尺度球点的加权合成由既有结果保证，不能把重复使用三维读口理解为任意高维整体都无损缩成一个三维状态。

若另有明确的内部参数域、局部载体与相容输运，可以组成 Hermitian 丛和连接 $D=d+\Gamma$，并定义

$$
F_\Gamma=d\Gamma+\Gamma\wedge\Gamma.
$$

这承接 v87：连接描述怎样把邻近比较接起来，曲率记录不同接续次序留下的差。它本身尚不选择参数域就是物理时空，也不唯一选择 Lorentz 度量、物质表示、耦合常数或场方程。从该框架进一步选择现实四种相互作用，仍需要对应的内部结构和动力学证据。

不指定唯一最高观察层，可以由可继续扩展的接口族表达。但在固定 $d$ 维载体中，实际后续观察空间至多有 $d^2$ 个独立复方向，严格扩张必停止。扩大到无限相容局部代数族时，已有共同态延拓与 GNS 构造可用，条件是逐层状态限制相容；这不供应固定有限记忆里的无限档案，也不单独证明存在无穷多个严格不同的分辨率。

**本轮候选的完整白话。**在这套关系理论里，整体中的一份内容可以充当参照，其他内容通过与它和彼此的比较显现。一条轨迹的单位切箭头又画出一条轨迹，切箭头的变化还可以继续如此；相邻几层怎样相接，已经包含弯曲、朝向和相对快慢。这些层都能使用同一种球面画法，完整内容还包括尺度、相位、历史与拼接。

选一层分辨率，就是决定现在保留哪些比较。如果一份粗化内容要真正代表原内容，那么任何保留下来的关系，无论从左边还是从右边与它接续，都应给出原来的完整复读数。这项双向要求迫使粗化具有合法的量子形式，也迫使参照与切口配套。换了参照，可以一起换切口；不能把一个切口冻结，再要求它无损适配所有参照。逐层保留的细节与剩余误差有精确账目；沿不同方向改变可见关系，接续次序的剩余又形成曲率。于是轨迹、轨迹的变化、分辨率、参照和曲率都进入同一个关系体系，同时保留它们各自在定义和计算中的职责。

这里“公理内生”的含义是：约束只比较内部内容、内部协议及其接续，失败也有内部读数见证。把它写入一种关系结构的定义以后，其后果由定理推出。这种定义不凭改名就证明自然界必然选择它；与实际量子理论及现实场论的对应，仍由明写的继承条件和物理证据承担。

**白话图景。**可以完整地说：整体里的内容彼此比较，比较沿历史变化，变化本身又成为下一次比较的内容。层级记录的是这次分辨出了什么，粗看和细看通过实际参照接在一起。每一层都能复用关系的语言，但不能丢掉尺度、历史和共有内容。这样得到的是一套能计算、能检查、能继续扩展的关系量子理论；它向现实场论前进的每一步，都要继续把新的结构锁进这些内部关系。

<a id="references"></a>

## 来源与版本关系

<a id="ref-atlas"></a>

1. trureturing，[*Quantum Origin: Endogenous Cut Atlas and Discrete Reconstruction Boundaries III*](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_III.md)，固定提交 `c63ab162315f`，尤其 §§1、4、11、16、34–35。普通保迹期望、有限分块、GNS、连续正规化子及可见／隐藏预算为既有结果。
<a id="ref-static"></a>

2. trureturing，[*Omega Static Compatibility Fiber Theory*](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，同一固定提交，§12 的相容局部态、闭包与 GNS 构造。
<a id="ref-foundations"></a>

3. trureturing，[*Contextual Spacetime Quantum: Foundations and Records*](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/ContextualSpacetimeQuantum/001_016_FOUNDATIONS_AND_RECORDS.md)，同一固定提交，§4 的有限后续观察闭包和维数终止界。
<a id="ref-v78"></a>

4. trureturing，[*Endogenous Closure, Finite Root Certificates and Outcome Kernel Recursion, V78 Continuation*](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ENDOGENOUS_CLOSURE_FINITE_ROOT_CERTIFICATES_AND_OUTCOME_KERNEL_RECURSION_V78_CONTINUATION.md)，同一固定提交，尤其 §9 的结果核递归、粗化与记录接口；另参见 [*Unified Relational Axioms, V78 Synthesis*](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ENDOGENOUS_RELATIONAL_QUANTUM_THEORY_UNIFIED_RELATIONAL_AXIOMS_V78_SYNTHESIS.md)，§17.2 的历史初始切向、恒曲率圆族及椭圆读出边界。
<a id="ref-v79"></a>

5. trureturing，[*Binary Reversal Compatibility, Finite Phase Certificates and Quantum Readout Reconstruction, V79*](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_BINARY_REVERSAL_COMPATIBILITY_FINITE_PHASE_CERTIFICATES_AND_QUANTUM_READOUT_RECONSTRUCTION_V79.md)，同一固定提交，尤其 §7 的二元关系球、尺度与父子合成。
<a id="ref-n2"></a>

6. trureturing，[*Shared History Sufficiency, Minimal Internal Completion and Dimension Budget, N2 V78*](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_SHARED_HISTORY_SUFFICIENCY_MINIMAL_INTERNAL_COMPLETION_AND_DIMENSION_BUDGET_N2_V78_CONTINUATION.md)，同一固定提交，§7 的有效维数、遗漏尺度和归一化边界。
<a id="ref-sahiner"></a>

7. B. Sahiner，*Direction curves of tangent indicatrix of a curve*，https://arxiv.org/abs/1808.02245 (2018)，§2 的切向像与 Frenet 背景。本文球面递归及逆向条件均在正文解析展开。
<a id="ref-takesaki"></a>

8. M. Takesaki，*Conditional expectations in von Neumann algebras*，Journal of Functional Analysis **9**(3), 306–321 (1972)，https://doi.org/10.1016/0022-1236(72)90004-3。保态条件期望与模不变性的原始来源；本文另给有限矩阵的完整证明。
<a id="ref-bardet"></a>

9. I. Bardet, A. Capel, C. Rouzé，*Approximate Tensorization of the Relative Entropy for Noncommuting Conditional Expectations*，https://arxiv.org/abs/2001.07981，§2.3。该文同时使用 KMS 内积；本文定义采用 $\operatorname{tr}(\rho x^\dagger y)$ 的 GNS 内积，两者不在定义层面混同。
<a id="ref-previous"></a>

10. 本对话连续研究稿 v84–v87，尤其 v86 的跨输入共同场相容，以及 v87 的相对锚、完整伙伴反作用、整体圆／局部椭圆和补向诱导曲率。这些是本轮连续性前件，不宣称已经合入上述固定仓库提交。

## 20. 原左 GNS 代表的近似右序比较与合法替代分辨率

**定义 20.1（比较域、普通迹与完全有界误差）。** 固定 $d\ge1$、$M=M_d(\mathbb C)$、忠实密度 $\rho>0$、$\operatorname{Tr}\rho=1$，以及共享单位元的 $*$-子代数 $A\subseteq M$。本节的 $\operatorname{Tr}$ 是普通矩阵迹。$E=E_{\rho,A}:M\to A$ 始终是定义 6.2 的实际左 GNS 正交投影：

$$
\operatorname{Tr}(\rho a^\dagger E(x))
=\operatorname{Tr}(\rho a^\dagger x)
\qquad(a\in A,\ x\in M).
$$

不对 $E$ 加正性前件。给定的右序比较缺陷是完整复收缩球上的标量：

$$
\epsilon=\sup_{\substack{x\in M,\ \|x\|_{\rm op}\le1\\
a\in A,\ \|a\|_{\rm op}\le1}}
\left|\operatorname{Tr}\bigl(\rho(E(x)a-xa)\bigr)\right|.
\tag{20.1}
$$

记 $P=P_A:M\to A$ 为普通迹保持的条件期望，$h=P(\rho)$、$\lambda=\lambda_{\min}(h)>0$。沿用[读出闭合稿定义 351.1](ContextualSpacetimeQuantum/351_354_READOUT_CLOSURE_AND_REALIZATION.md) 的既有数学背景：$P$ 是 $U(A')$ 上的酉共轭平均，$Q=P_{A'}$ 是 $U(A)$ 上的酉共轭平均，二者交换。特别地，$P,Q$ 都 UCP、保持普通迹并在 Hilbert–Schmidt 内积下自伴。紧酉平均的存在不作为新增命题。

对任意复线性 $T:M\to M$，约定

$$
T^{(k)}=\operatorname{id}_{M_k}\otimes T,\qquad
\|T\|_{\rm cb}=\sup_{k\ge1}
\sup_{0\ne X\in M_k\otimes M}
\frac{\|T^{(k)}(X)\|_{\rm op}}{\|X\|_{\rm op}}.
\tag{20.2}
$$

值域为 $A$ 的映射经自然包含视为 $M$ 值映射。$\|s\|_1=\operatorname{Tr}|s|$，不含因子 $1/2$；$T_*$ 表示普通迹对偶 $\operatorname{Tr}(T_*(s)x)=\operatorname{Tr}(sT(x))$。式 (20.1) 不含任何辅助矩阵输入。

**命题 20.2（保持可见校准的条件化修复）。** 在定义 20.1 下，令

$$
K=h^{-1/2}\rho h^{-1/2},\qquad
q=Q(K),\qquad
\sigma=h^{1/2}q h^{1/2},\qquad
F(x)=P(q^{1/2}xq^{1/2}).
\tag{20.3}
$$

则 $\sigma>0$、$\operatorname{Tr}\sigma=1$，并且

$$
P(\sigma)=h,\qquad \sigma|_A=\rho|_A.
\tag{20.4}
$$

$F$ 是 Heisenberg 图像中到恰好 $A$ 的 UCP、$A$-双模、幂等映射；它也是 $\sigma$ 的实际左 GNS 投影，且

$$
F_*(\rho)=\sigma=F_*(\sigma).
\tag{20.5}
$$

令 $\Delta=\rho-\sigma$，则有充分界

$$
\boxed{
\|\Delta\|_1\le\epsilon,\qquad
\|E-F\|_{\rm cb}
\le\frac{\|\Delta\|_{\rm op}}{\lambda}
\le\frac{\|\Delta\|_1}{\lambda}
\le\frac{\epsilon}{\lambda_{\min}(P_A(\rho))}.
\ }
\tag{20.6}
$$

该定量原 GNS 推论为 repo-derived 解析推导；不主张常数最优或世界范围的新颖性。所复用的精确 GNS／模不变性判据见定理 7.1、[Carlen–Vershynina, *Recovery map stability for the Data Processing Inequality*, §§1.4、4](https://arxiv.org/html/1710.02409v3)，以及 [Bardet–Capel–Rouzé, *Approximate tensorization of the relative entropy for noncommuting conditional expectations*, §2.3](https://arxiv.org/html/2001.07981)。这些精确判据、既有紧酉平均与已假定 UCP 的稳定性结论不是式 (20.6) 的定量原 GNS 推论本身；这里的文献归属限于这些具体来源与命题范围。

证明。先由左比较和 $P$ 的迹自伴性，对所有 $a\in A$ 得

$$
\operatorname{Tr}(a^\dagger E(x)h)
=\operatorname{Tr}(a^\dagger x\rho)
=\operatorname{Tr}(a^\dagger P(x\rho)).
$$

两侧被配对的矩阵均在 $A$ 中，故

$$
E(x)=P(x\rho)h^{-1}.
\tag{20.7}
$$

这只是实际正交投影的公式，不涉及其正性。将其代入右序比较，并使用 $P$ 的双模性，得到

$$
\begin{aligned}
\operatorname{Tr}\bigl(\rho(E(x)a-xa)\bigr)
&=\operatorname{Tr}\bigl((\rho h^{-1}ah-a\rho)x\bigr),\\
\epsilon
&=\sup_{a\in A,\ \|a\|_{\rm op}\le1}
\|\rho h^{-1}ah-a\rho\|_1.
\end{aligned}
\tag{20.8}
$$

第二式使用完整复收缩球的算符范数／迹范数对偶；只给有限测量菜单时不能直接使用这一步。

对 $b\in A$、$y\in M$，有 $Q(by)=Q(yb)$：与任意 $z\in A'$ 作迹配对，利用 $zb=bz$ 和迹循环性即可。于是

$$
Q(\rho h^{-1})=Q(h^{-1/2}\rho h^{-1/2})=q.
\tag{20.9}
$$

$K>0$，且若 $m=\lambda_{\min}(\rho)>0$，则 $K\ge(m/\|h\|_{\rm op})I$。$Q$ 正且保单位元，故 $q\ge(m/\|h\|_{\rm op})I>0$。$q\in A'$ 与 $h$ 交换，所以 $\sigma=qh>0$。又由两平均交换，

$$
P(K)=h^{-1/2}P(\rho)h^{-1/2}=I,\qquad
P(q)=QP(K)=I,\qquad
P(\sigma)=h.
$$

由此 $\operatorname{Tr}\sigma=\operatorname{Tr}h=1$，且式 (20.4) 对所有复 $a\in A$ 成立。

现在只把式 (20.8) 用于 $a=u\in U(A)$。左乘 $u^\dagger$ 不改变迹范数，得到

$$
\|u^\dagger\rho h^{-1}u h-\rho\|_1\le\epsilon.
$$

对 $U(A)$ 的归一 Haar 测度积分；由式 (20.9) 与迹范数的凸性，

$$
\|\sigma-\rho\|_1
=\left\|\int_{U(A)}
(u^\dagger\rho h^{-1}u h-\rho)\,du\right\|_1
\le\epsilon.
\tag{20.10}
$$

因此态误差界没有除以最小谱值。

$q$ 与 $A$ 交换，且 $P$ 是迹正交投影。与任意 $a\in A$ 作迹配对可将 $q^{1/2}$ 从左侧移到右侧，故

$$
F(x)=P(xq)=P(x\sigma)h^{-1}.
\tag{20.11}
$$

式 (20.3) 是 CP 夹乘与 UCP 映射 $P$ 的组合，且 $F(I)=P(q)=I$。$q$ 与 $A$ 交换、$P$ 双模，给出 $F(axb)=aF(x)b$。于是 $F(a)=a$、像恰为 $A$、$F^2=F$。式 (20.7) 换成校准 $\sigma$ 后，因 $P(\sigma)=h$，其右端正是式 (20.11)，证明 $F=E_{\sigma,A}$。普通迹对偶为

$$
F_*(s)=q^{1/2}P(s)q^{1/2}.
\tag{20.12}
$$

将 $s=\rho,\sigma$ 代入即得式 (20.5)。$F_*$ 是 CPTP；$F$ 本身一般不保持普通迹。

最后，由式 (20.7)、(20.11)，对每个有限 $k$、每个复矩阵 $X\in M_k\otimes M$，

$$
\begin{aligned}
(E-F)^{(k)}(X)
&=P^{(k)}\bigl(X(I_k\otimes\Delta)\bigr)
(I_k\otimes h^{-1}),\\
\|(E-F)^{(k)}(X)\|_{\rm op}
&\le\|X\|_{\rm op}\|\Delta\|_{\rm op}/\lambda .
\end{aligned}
\tag{20.13}
$$

这里用的是已知 $P$ 的完全收缩性以及普通右乘的算符范数界，没有对 $E$ 使用 Schwarz 不等式、正性或完全正性。对所有有限 $k$ 取上确界并结合式 (20.10)，得到式 (20.6)。这也说明结论中的辅助一致控制来自显式矩阵公式，而非把输入假设换成放大缺陷。

**推论 20.3（同一代表、原校准保态与谱条件的分界）。** 在命题 20.2 的对象上，复用精确 $C_{88}$／Takesaki 判据，有

$$
\begin{aligned}
\epsilon=0
&\ \Longleftrightarrow\ E\text{ 正}\\
&\ \Longleftrightarrow\ E\text{ 为 UCP}\\
&\ \Longleftrightarrow\
\rho^{it}A\rho^{-it}=A\quad(t\in\mathbb R)\\
&\ \Longleftrightarrow\
\text{存在到恰好 }A\text{ 的保持原 }\rho\text{ 的条件期望}\\
&\ \Longleftrightarrow\ \sigma=\rho .
\end{aligned}
\tag{20.14}
$$

其中条件期望采用保单位元、完全正、幂等、$A$-双模的含义。对 $\epsilon>0$，式 (20.6) 供应保持 $\sigma$ 的替代 $F$，不供应原 $E$ 的正性，且 $F_*(\rho)\ne\rho$。若给定目标 $\eta_0\ge0$ 并要求完全有界误差不超过 $\eta_0$，一个充分条件是 $\epsilon\le\eta_0\lambda$。

证明。$\epsilon=0$ 就是原 $C_{88}$。正复线性映射保持伴随，结合定理 7.1 给前三个等价。若 $R$ 是保持 $\rho$ 的条件期望，则

$$
\operatorname{Tr}(\rho a^\dagger R(x))
=\operatorname{Tr}(\rho R(a^\dagger x))
=\operatorname{Tr}(\rho a^\dagger x),
$$

所以 $R=E$，而定理 7.1 给存在性的精确模判据。$\epsilon=0$ 时式 (20.6) 给 $\sigma=\rho$；反之若 $\sigma=\rho$，式 (20.7)、(20.11) 给 $E=F$ 为 UCP，故 $\epsilon=0$。

必须分别保留三个误差对象：式 (20.10) 是这一对校准态的迹范数误差；式 (20.13) 是原代表与替代映射的算符误差，且对所有有限辅助矩阵一致；它们都不是原 $\rho$ 的精确保态回缩。$\operatorname{Tr}h=1$ 意味着 $\lambda\le1/d$，而 $h\ge\lambda_{\min}(\rho)I$。因此对每个固定 $(d,\rho,A)$ 的结论不等于跨维数的一致小误差定理；即使已知 $h\ge\kappa I/d$、$0<\kappa\le1$，由式 (20.6) 取得的充分界仍是 $d\epsilon/\kappa$。以下二维族表明，仅有忠实性而没有统一谱下界时，连固定维数也不存在非零缺陷阈值保证原 $E$ 正或保证其接近正映射。

原校准保态但不固定整个 $A$ 的广义 CP 粗化是另一种性质，见 Carlen–Vershynina §1.4 及 Bardet–Capel–Rouzé §§2.4.1、A.1；后者的固定点条件期望还可有严格较小的像。它们不能替代式 (20.14) 中“到恰好 $A$ 的原校准保态回缩”，这里不另提出定量 Petz 结论。

## 21. 忠实量子比特上的小缺陷与无界映射距离

**命题 21.1（原比较缺陷不能无条件控制合法映射距离）。** 固定 $A\subset M_2$ 为对角代数。对 $0<t<1/2$，取

$$
\rho_t=
\begin{pmatrix}t^2&t/2\\ t/2&1-t^2\end{pmatrix},\qquad
h_t=P_A(\rho_t)=\operatorname{diag}(t^2,1-t^2).
\tag{21.1}
$$

这些校准均忠实，实际左 GNS 投影及原始缺陷恰为

$$
\begin{aligned}
E_t(x)&=\operatorname{diag}\left(
x_{11}+\frac{x_{12}}{2t},\
x_{22}+\frac{t\,x_{21}}{2(1-t^2)}\right),\\
\epsilon_t&=2t,\qquad
\lambda_{\min}(h_t)=t^2 .
\end{aligned}
\tag{21.2}
$$

设 $\mathcal P$ 是所有正复线性映射 $M_2\to M_2$，不要求保单位元；$\mathcal U$ 是其中所有 UCP 映射。若 $\|T\|_{{\rm op}\to{\rm op}}=\sup_{\|x\|_{\rm op}\le1}\|T(x)\|_{\rm op}$，则

$$
\boxed{
\begin{aligned}
\inf_{T\in\mathcal P}\|E_t-T\|_{{\rm op}\to{\rm op}}
&=\inf_{T\in\mathcal U}\|E_t-T\|_{{\rm op}\to{\rm op}}
=\frac1{2t}=\frac1{\epsilon_t},\\
\inf_{T\in\mathcal P}\|E_t-T\|_{\rm cb}
&=\inf_{T\in\mathcal U}\|E_t-T\|_{\rm cb}
=\frac1{2t}.
\end{aligned}}
\tag{21.3}
$$

故 $\epsilon_t\downarrow0$ 而距每个正映射或 UCP 映射的最佳距离均无界。非正性及坏角机制复用命题 9.2；这里的 repo-derived 定量增量是同一忠实二维族上原 $\epsilon_t$ 的精确计算及式 (21.3) 的距离结论。

证明。$\operatorname{Tr}\rho_t=1$ 且 $\det\rho_t=t^2(3/4-t^2)>0$，故忠实。式 (20.7) 给出 $E_t$。对 $a=\operatorname{diag}(a_1,a_2)$，$a$ 与 $h_t$ 交换，因此式 (20.8) 中的矩阵为

$$
\rho_t a-a\rho_t
=\frac t2
\begin{pmatrix}0&a_2-a_1\\a_1-a_2&0\end{pmatrix}.
$$

其两个奇异值均为 $t|a_2-a_1|/2$，迹范数为 $t|a_2-a_1|$。完整复收缩球上 $|a_2-a_1|\le2$，并在 $a=\operatorname{diag}(1,-1)$ 取等，故原定义的 $\epsilon_t=2t$。等价地，该 $a$ 配合 $x=-i\sigma_y$ 已达到相同绝对比较值。

对每个正复线性 $T$，$T(\sigma_y)$ Hermitian，其首个对角元为实数，而

$$
\sigma_y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\qquad
E_t(\sigma_y)=
\operatorname{diag}\left(-\frac{i}{2t},\frac{it}{2(1-t^2)}\right).
$$

由于 $\|\sigma_y\|_{\rm op}=1$，其首个对角元的虚部给出

$$
\|E_t-T\|_{{\rm op}\to{\rm op}}
\ge\|(E_t-T)(\sigma_y)\|_{\rm op}
\ge\frac1{2t}.
\tag{21.4}
$$

这不依赖 $T$ 的值域是否为 $A$，也不依赖 $T$ 是否保单位元。另一方面，式 (20.3) 的构造在此处取 $q_t=I$、$\sigma_t=h_t$、$F_t=P_A$，于是

$$
(E_t-F_t)(x)
=\operatorname{diag}\left(\frac{x_{12}}{2t},
\frac{t\,x_{21}}{2(1-t^2)}\right).
$$

在每个有限放大上，输入块 $X_{12},X_{21}$ 的算符范数都不超过 $\|X\|_{\rm op}$，而输出是这两个块乘以所示标量后的直和。因 $t<1/2$，有 $t/[2(1-t^2)]<1/(2t)$，从而

$$
\|E_t-F_t\|_{\rm cb}\le1/(2t).
$$

取 $x=e_{12}$ 达到等号。$F_t$ 为 UCP，结合式 (21.4) 与 $\|\cdot\|_{{\rm op}\to{\rm op}}\le\|\cdot\|_{\rm cb}$，证明式 (21.3)。同时

$$
\|\rho_t-\sigma_t\|_1=t=\epsilon_t/2,\qquad
\|\rho_t-\sigma_t\|_{\rm op}=t/2.
$$

态校准误差确实趋于零，但谱除数 $t^2$ 使映射距离发散。此族的两层估计与式 (20.6) 相容；它不把充分上界认作所有对象上的最优常数。

## 22. 唯一整体中的域限定与二元关系应用

**定义 22.1（内部历史、替代准备、观察及控制域）。** 固定唯一全局态 $\Omega$ 与全局载体 $\mathcal H_\Omega$。在当前有限切口声明嵌入 $\iota:M_d\to B(\mathcal H_\Omega)$、替代准备标签域 $\mathcal D_{\rm prep}$、观察设置域 $\mathcal D_{\rm obs}$、内部参照与记忆读出域 $\mathcal D_{\rm ref}$、允许延续控制域 $\mathcal D_{\rm ctrl}$，以及联合合法标签集

$$
\mathcal J\subseteq
\mathcal D_{\rm prep}\times\mathcal D_{\rm obs}
\times\mathcal D_{\rm ref}\times\mathcal D_{\rm ctrl}.
$$

对每个 $\alpha\in\mathcal J$，指定由内部量子门序列组成的整体历史 $U_\alpha$ 与切口读数

$$
\operatorname{Tr}(s_\alpha x)
=\langle\Omega,U_\alpha^\dagger\iota(x)U_\alpha\Omega\rangle
\qquad(x\in M).
\tag{22.1}
$$

$\Omega$ 归一，$\iota$ 为保单位元的 $*$-嵌入，因此 $s_\alpha$ 是密度矩阵。设置、参照及记忆也属于历史标签及相应切口，不作为整体之外的独立装置。$\mathcal J$ 不假设为直积；共同起源不供应独立性、全部准备或全部控制。切口所保留的记忆和结果属于 $s_\alpha$ 的同一联合对象；未纳入 $M$ 的历史数据不能据此声称已保留或可返回。原生效果菜单是另行指定的 $\mathcal O_\alpha\subseteq[0,I]_M$，其内部记录与延续仍按 $\mathcal J$ 的合法关系决定。

命题 20.2 的 $\rho$ 是此内部接口所声明的忠实比较校准；若以内部备选读数的加权校准表示，需给定 $s_{\alpha_j}$ 与正权重 $w_j$，满足 $\sum_jw_j=1$、$\rho=\sum_jw_js_{\alpha_j}>0$。不假定全部数学密度矩阵都出现在该准备域。$\sigma$ 定义为同一 $M$ 上用于比较的归一正泛函，不断言存在新的可执行准备标签使 $s_\alpha=\sigma$；式 (20.3) 不改变全局 $\Omega$，也不把 Haar 平均当作可用门菜单。式 (20.1) 是比有限原生测量菜单更强的完整复比较球假设，是否由某个原生接口供应须另证。

**推论 22.2（可见二元几何与有域的操作误差）。** 在定义 22.1 的内部解释下应用命题 20.2，设 $\eta=\epsilon/\lambda$。则对所有 $a,b\in A$，

$$
\operatorname{Tr}(\rho a^\dagger b)
=\operatorname{Tr}(\sigma a^\dagger b).
\tag{22.2}
$$

故按 §14 对这些可见二元关系形成的 Gram 数据、保留强度的归一关系几何相同。$F$ 在整个数学态域 $\{s\ge0:\operatorname{Tr}s=1\}$ 上有 CPTP 对偶，在整个数学效果域 $[0,I]_M$ 上是合法 Heisenberg 分辨率。实际准备与控制只按各自已声明的域解释；实现 $F$ 的内部历史若未供应，就仍是缺失的实现桥梁。

对任意有限 $k$、每个 $X\in M_k\otimes M$，以及在同一 $M$ 上的 UCP 前后处理 $B,C:M\to M$，

$$
\|(C\circ E\circ B-C\circ F\circ B)^{(k)}(X)\|_{\rm op}
\le\eta\|X\|_{\rm op}.
\tag{22.3}
$$

普通迹对偶还给所有复矩阵 $S\in M_k\otimes M$ 的线性误差界

$$
\|(\operatorname{id}_{M_k}\otimes(E_*-F_*))(S)\|_1
\le\eta\|S\|_1.
\tag{22.4}
$$

该式不把 $E_*(S)$ 宣称为正态；$\|\rho-\sigma\|_1\le\epsilon$ 只对应指定校准态对，而式 (22.4) 对应两映射之差。两种误差不可互换。

证明。$a^\dagger b\in A$，故式 (22.2) 由式 (20.4) 得到，既有二元归一化只调用相同 Gram 数据。$F$ 的 UCP 性及 $F_*$ 的 CPTP 性保证所述数学态与效果域。式 (22.3) 由式 (20.13) 和 $B,C$ 的完全收缩性得到；这里只比较同一切口上有型的前后组合，不将另一个准备、另一份历史或不相容条件事件混入该组合。只有某个控制历史已在同一切口、所需输入域上实现相应 UCP 映射时，才能把式 (22.3) 解释为该控制的误差；整体酉序列本身不保证在关联的约化输入上存在统一 UCP 映射。式 (22.4) 对每个 $k$ 使用普通迹下的算符范数／迹范数对偶即得。

[第 v89 卷 §§8、10](AURIC_SQUARE_CLOSURE_RECURSIVE_STABILITY_RELATIONAL_QUANTUM_FIELD_V89.md) 的有限词及保忠实态不动代数结论可在其各自前件下作用于显式 UCP 映射 $F$、校准 $\sigma$；它们不能先作用于未知正性的 $E$ 再反推其 CP。[第 v90 卷 §§5、14–15、19](AURIC_BINARY_INTERNAL_MIDPOINT_SQUARE_RECOVERY_SHARED_QUANTUM_STRUCTURE_V90.md) 的中点平方／Petz 论证同样使用已供应的 CPTP 过程，不替代命题 20.2 的原 GNS 推论。

式 (20.2)、(20.13) 的任意有限辅助矩阵是完全有界范数的数学量词，不赋予可访问辅助系统、独立准备、初始环境、控制精度、额外记忆、门编译深度或原生记录器。Finite3 在这里仍是二元关系几何，不是全局维数三的假设。本推论也没有从一个切口的替代分辨率推出 V81 的全程返回／原生记录构造；该目标所需的历史、全部保留记录及控制实现不能由终端校准相近或式 (22.3) 的前后处理界替代。式 (20.6) 因而是声明前件下的解析关系，不承担经验性的量子起源或宇宙本体判定。

## 追加锚（本行以下为增补区）

## 23. 固定原生历史、已得事件与同一个校准

**定义 23.1（十六位菜单上的资源与切口）。** 本节至 §27 只使用 [Setting-Source 定义 8.1–8.3、式 (8.5)、(8.7a)](AURIC_SINGLE_PURE_WHOLE_SETTING_SOURCE_RELATIONS_V78_CONTINUATION.md) 的原生载体、根和记录语义。位置是 $-1,0,\ldots,14$，

$$
\mathcal H_{\mathcal N}=(\mathbb C^2)^{\otimes16},\qquad
\mathcal L=\operatorname{span}\{|b\rangle:b_jb_{j+1}=0\},\qquad
\dim\mathcal L=2584.
$$

唯一根为

$$
\Omega_0=|1,0,0,0,1,0,0,0,1,0\rangle_{-1,\ldots,8}
                 \otimes|000\rangle_{9,10,11}
                 \otimes|000\rangle_{12,13,14}.
\tag{23.1}
$$

记 $\varphi=(1+\sqrt5)/2$、$\zeta=e^{3\pi i/5}$、$\beta=\varphi^{-1/2}$、$t=\beta^2=\varphi^{-1}$。实际门始终是 [V15 §3](AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md) 的完整矩阵

$$
\begin{aligned}
Q_j&=t(I-n_j)+t^2n_j+\beta^3X_j,\\
\mathcal P_j&=n_{j-1}n_{j+1}+(I-n_{j-1})(I-n_{j+1})Q_j,\\
K_j&=\zeta[I+(\zeta-1)\mathcal P_j],\qquad 0\le j\le13.
\end{aligned}
\tag{23.2}
$$

源空间仍是 Setting-Source 式 (8.3) 的 $\mathcal S$：$b_{-1}b_0=10$、$b_6b_7b_8=010$、$(b_1,\ldots,b_5)$ 无相邻 $11$，维数为十三；其原编码 $J|q_Aq_B\rangle=|1,0,q_A,0,1,0,q_B,0,1,0\rangle$ 仅指定四维逻辑子空间。实际运行不重选式 (23.1) 的根。

源准备的地址字只取 $0,\ldots,6$；完整原生菜单另允许 $0,\ldots,13$ 上的门、计算基正交投影及按已得结果选择地址的有限确定表。门保持 $\mathcal L$，但矩阵和以下张量切口都在完整 $\mathcal H_{\mathcal N}$ 上解释。没有任意旋转、自由输入态、自由测量基、外来随机权重、复位或额外相干受控门。

一个具体协议给定有限根树 $\mathcal T$。门节点是一个实际正向 $K_j$；测量节点 $v$ 是计算基对角零一投影的完整分解 $\{\Pi_{v,o}:o\in O_v\}$，包括所有结果，且 $\sum_o\Pi_{v,o}=I$；后续节点可依赖已得报告。失败、拒绝、提前停止和正常停止都有明确终叶，零质量标签也不删除。未调用门的调度槽为恒等。若字表写了逆调用，先按 $K_j^{-1}=K_j^9$ 展开：正向调用成本为一，逆调用成本为九。对展开后的整棵树声明实际资源

$$
L=\max_{h\ \mathrm{terminal}}\#\{h\text{ 上的正向 }K\text{ 调用}\},\qquad
m=\max_h\#\{h\text{ 上的测量节点}\},\qquad
b=\max\bigl(\{1\}\cup\{|O_v|:v\text{ 为测量节点}\}\bigr).
\tag{23.3}
$$

另声明全部有限节点及停止标签、反馈地址表、控制器与实际档案的有限状态集 $\mathcal C$。$L$ 计完整协议全部分支，不能只计成功分支；截在一个已声明切口的前缀也可以独立作为这样的有限树。$m,b,|\mathcal C|$ 是适用域的一部分；以下界不另乘叶数，并不把这些资源当作不存在。档案只记录菜单定义的调用、报告和停止，不添加隐藏的计算基微轨迹。

固定一个实际共同切口 $t_*$，每条完整历史恰穿过它一次；必要时用恒等槽对齐提前停止叶，所得前缀叶仍为完整分解。$\mathcal H_R=H_I$ 由预先指定的原生位置子集 $I$ 构成，$\mathcal H_Z=H_{I^c}$，设

$$
q=|I|,\qquad d=2^q,\qquad e=2^{16-q},\qquad
\mathcal H_{\mathcal N}\cong\mathcal H_R\otimes\mathcal H_Z.
\tag{23.4}
$$

因此 $de=65536$；控制器及报告的其他实际记录仍保留在各自已声明因子或经典记录代数中。$\mathcal L$ 在此只是一个受约束子空间，不被假定为 $\mathcal H_R\otimes\mathcal H_Z$ 内的张量子空间。若把额外控制寄存器纳入待校准因子，须另给其维数及矩阵来源，不能直接沿用这里的 $d,e$。

**定义 23.2（完整事件律与忠实校准域）。** 对切口处完整已得历史 $h$，令 $M_h$ 是沿该分支按实际顺序相乘的门与投影，$v_h=M_h\Omega_0$，$c_h(i,z)=\langle i,z|v_h\rangle$。分支不归一化。若切口后还有延续，$N_{\ell|h}$ 是原表指定的完整后继分支乘积；完整 Born 律为

$$
\Pr(h,\ell,y)=|\langle y|N_{\ell|h}M_h\Omega_0\rangle|^2,
\qquad
\sum_{h,\ell,y}\Pr(h,\ell,y)=1.
\tag{23.5}
$$

$y$ 是完整终端计算基结果，所有失败、停止及实际报告都包含在 $(h,\ell,y)$ 的样本空间中。没有后继时取 $N=I$。由已得报告决定的事件 $\mathcal E$ 必须在 $t_*$ 已经可判；不能把未来才测得的标签事后当作同一切口的已得事件。其未归一原生约化、质量及条件校准分别为

$$
\begin{aligned}
\Xi_{\mathcal E}&=\sum_{h\in\mathcal E}\operatorname{Tr}_Z(v_hv_h^\dagger),
& (\Xi_{\mathcal E})_{ij}&=\sum_{h\in\mathcal E,z}c_h(i,z)\overline{c_h(j,z)},\\
p_{\mathcal E}&=\operatorname{Tr}\Xi_{\mathcal E}
             =\sum_{h\in\mathcal E}\|v_h\|^2,
& \rho&=\Xi_{\mathcal E}/p_{\mathcal E}\quad(p_{\mathcal E}>0).
\end{aligned}
\tag{23.6}
$$

对历史求和是保留完整经典记录律后选择原生因子的数学约化，不是相干叠加不同报告，也不是物理擦除或复制档案；已由原生单元 $X,Y$ 承载的报告不再增加一份返回量子副本。特别采用原设置读出时，$X=b_{10},Y=b_{13}$ 的非选择语义仍是 $\sum_{xy}P_{xy}DP_{xy}$，不是一个新增全局酉门。

这里应用命题 20.2 的精确域是

$$
\mathfrak F=\{(\mathcal T,t_*,I,\mathcal E):\ p_{\mathcal E}>0,
                         \ \operatorname{rank}\Xi_{\mathcal E}=d\}.
\tag{23.7}
$$

命题 20.2 的原校准在此量化域内明确就是式 (23.6) 的同一个 $\rho$。给定 $A\subseteq M_d$ 后仍取原 $E_{\rho,A}$；不把另一个固定而无关的校准替换成原生边际。存在正质量事件并不保证式 (23.7)。若一个事件只含 $n_{\mathcal E}$ 个非零分支，则 $\operatorname{rank}\Xi_{\mathcal E}\le\min(d,e n_{\mathcal E})$；纯根本身不保证任何指定切口忠实。该秩上界由每个 $d\times e$ 系数矩阵的秩及有限求和直接得到，不是忠实切口的存在性定理。

## 24. 完整投影树上的黄金资源谱下界

**定理 24.1（固定根的已得事件与二次域行列式）。** 在定义 23.1–23.2 下，置

$$
\kappa=1+2\varphi^3,\qquad \Xi=\Xi_{\mathcal E},\quad p=p_{\mathcal E}.
$$

若 $p>0$，则

$$
 p\ge\kappa^{-2L}.
\tag{24.1}
$$

若另有 $\operatorname{rank}\Xi=d$，则

$$
\det\Xi\ge\kappa^{-2Ld},\qquad
\lambda_{\min}(\Xi)\ge\kappa^{-2Ld},\qquad
\lambda_{\min}(\rho)\ge\frac{\kappa^{-2Ld}}p.
\tag{24.2}
$$

这些界使用实际最大正向调用数 $L$、指定的 $d,e$、完整测量树和无分母原始概率。它们也蕴含较粗的 $\kappa^{-14Ld}$ 行列式界；不主张常数最优、与资源无关的谱隙，或所有量子态都属于此族。

证明。数域和整性先固定为

$$
F_0=\mathbb Q(\zeta),\quad R_0=\mathbb Z[\zeta],\quad
\mathbb K=F_0(\beta),\quad \mathcal R=\mathbb Z[\zeta,\beta],\quad
k=\mathbb Q(\sqrt5).
\tag{24.3}
$$

$\zeta$ 为本原十次单位根，$t=-(\zeta+\zeta^{-1})$，$t^2+t=1$，$\beta^4+\beta^2-1=0$。因此 $\mathcal R$ 中各数均为代数整数；式 (23.2) 没有有理分母。有限投影、矩阵乘法、记录求和和原生偏迹只作有限加乘，故 $c_h(i,z),\Xi_{ij},p,\det\Xi$ 都是 $\mathbb K$ 中代数整数。这里不要求 $\mathcal R$ 等于全整数环。条件化 $\rho=\Xi/p$ 才引入除法，$\rho$ 的各项不被断言仍为代数整数。

复共轭在 $\mathbb K$ 上记为 $c$，由 $c(\zeta)=\zeta^{-1},c(\beta)=\beta$ 给出。$[F_0:\mathbb Q]=4$。按 V15 引理 9.4 的论证，若实数 $\beta$ 属于 $F_0$，它必属于 $F_0\cap\mathbb R=k$；但 $N_{k/\mathbb Q}(t)=-1$ 不可能等于 $N_{k/\mathbb Q}(\beta)^2$，所以 $\beta\notin F_0$，$[\mathbb K:\mathbb Q]=8$。全部八个嵌入正是

$$
\begin{array}{c|c|c}
a&\sigma(\zeta)&\sigma(\beta)\\ \hline
1,9&\zeta^a&+\beta\ \text{或}\ -\beta\\
3,7&\zeta^a&+i\sqrt\varphi\ \text{或}\ -i\sqrt\varphi
\end{array}
\tag{24.4}
$$

每个 $a$ 有两个独立平方根选择。前一行 $\sigma(t)=t$，后一行 $\sigma(t)=-\varphi$。对任一这样的 $\sigma$，$\sigma\circ c$ 也是八个嵌入之一，但一般
$\sigma(c(x))\ne\overline{\sigma(x)}$：例如后一行取 $x=\beta$。以下估计始终分别使用 $\sigma$ 与 $\sigma\circ c$。

先复用 V15 命题 8.3 证明中逐门的实际矩阵估计。活跃块 $Q=uu^{\mathsf T}$、$u=(\beta,\beta^2)^{\mathsf T}$，满足

$$
\|\sigma(Q)\|_{\rm op}\le |\sigma(\beta)|^2+|\sigma(\beta)|^4
          \le\varphi+\varphi^2=\varphi^3.
$$

完整 $\mathcal P_j$ 的其他控制块为零或单位，$|\sigma(\zeta)|=1$，所以

$$
\|\sigma(K_j)\|_{\rm op}\le1+2\varphi^3=\kappa.
\tag{24.5}
$$

张量单位、地址重排和所有完整计算投影不改变该估计。这里仅复用逐门界；V15 命题 8.3 的酉字事件结论不被直接套给自适应树。

对树中节点 $v$，令 $\ell_v$ 是从该节点开始到任一终叶的最大剩余正向调用数。对任意复向量 $w$，从节点 $v$ 继续所得所有终叶的嵌入分支向量平方范数之和至多为 $\kappa^{2\ell_v}\|w\|^2$。这是有限树上的逆向归纳：终叶为等号；门节点利用式 (24.5) 并消耗一个调用；测量节点各子树的 $\ell$ 至多为 $\ell_v$，而投影仍是原来的正交零一矩阵，因此

$$
\sum_{o\in O_v}\|\Pi_{v,o}w\|^2=\|w\|^2.
$$

此等式覆盖完整结果分解，允许各结果后采用不同门字和不同停止深度。于是对全部叶和任意事件子集都有

$$
\sum_{h\in\mathcal E}\|\sigma(v_h)\|^2
\le\sum_{h\ \mathrm{all}}\|\sigma(v_h)\|^2
\le\kappa^{2L}.
\tag{24.6}
$$

同一归纳也适用于停在 $t_*$ 的完整前缀树。它不逐叶分别放大再求和，因而没有 $b^m$、叶数或报告数惩罚；完整性、有限深度、投影的有理零一性和没有中途条件归一化都是此步的前件。

将各 $c_h(i,z)$ 按 $(h,z)$ 合并成一个 $d\times(e|\mathcal E|)$ 系数矩阵 $V$。逐项施加嵌入，精确等式为

$$
\sigma(\Xi)=\sigma(V)\big((\sigma\circ c)(V)\big)^{\mathsf T}.
\tag{24.7}
$$

这不是 $\sigma(V)\sigma(V)^\dagger$。由式 (24.6)，两个矩阵的 Frobenius 范数分别至多 $\kappa^L$；Cauchy–Schwarz 和算符范数的次乘性给

$$
|\sigma(p)|\le\kappa^{2L},\qquad
\|\sigma(\Xi)\|_{\rm op}\le\kappa^{2L},\qquad
|\sigma(\det\Xi)|\le\kappa^{2Ld}.
\tag{24.8}
$$

第一式直接对 $p=\sum_{h,i,z}c_h(i,z)c(c_h(i,z))$ 配对；第三式用 $d$ 个奇异值的乘积。不假设非物理嵌入后的 $\Xi$ 正或 Hermitian。至此，若只使用八次数域的整数范数，已可得 $p\ge\kappa^{-14L}$、$\det\Xi\ge\kappa^{-14Ld}$。更强指数来自实际奇偶分级，不能从“八次”本身取得。

令 $\tau$ 是 $\mathbb K/F_0$ 的非平凡自同构，$\tau(\beta)=-\beta$、$\tau(\zeta)=\zeta$。它与这里明确给出的物理共轭 $c$ 交换。由 V15 引理 9.1，每条含计算投影的分支仍有

$$
c_h(i,z)\in
\begin{cases}
R_0,&\pi(i)+\pi(z)=\pi(\Omega_0)\pmod2,\\
\beta R_0,&\pi(i)+\pi(z)\ne\pi(\Omega_0)\pmod2,
\end{cases}
$$

其中 $\pi$ 为实际计算基词的 Hamming 奇偶。乘积中的共同输入和共同补词 $z$ 的奇偶各出现两次，因而

$$
\tau(\Xi)=J_R\Xi J_R,
\qquad J_R=\operatorname{diag}_{i}((-1)^{\pi(i)}),
\qquad \tau(p)=p,\quad\tau(\det\Xi)=\det\Xi.
\tag{24.9}
$$

有限事件求和、反馈和停止均不改变这个逐项等式。$\mathbb K^\tau=F_0$，而物理 $\Xi$ 为正半定，所以 $p$ 和 $D=\det\Xi$ 是实数；再取 $F_0$ 内物理复共轭的不动域，得到

$$
p,D\in\mathcal O_k,\qquad k=\mathbb Q(\sqrt5).
\tag{24.10}
$$

这里只对特定的 $\tau,c$ 使用已验证的交换关系；未将任意嵌入与物理共轭交换。$k$ 的另一个实嵌入 $\nu$ 由 $t\mapsto-\varphi$ 给出，可用式 (24.4) 后一行任意嵌入延拓。$p\ne0$ 时，其二次域范数为非零整数；$D>0$ 时同样如此。标准整数范数事实见 [Milne, *Algebraic Number Theory*, v3.08, Proposition 2.19、Corollaries 2.20–2.21](https://www.jmilne.org/math/CourseNotes/ANT.pdf)。于是式 (24.8) 给

$$
1\le|p\nu(p)|\le p\kappa^{2L},\qquad
1\le|D\nu(D)|\le D\kappa^{2Ld},
\tag{24.11}
$$

分别证明式 (24.1) 及行列式界。物理 $\operatorname{Tr}\Xi=p\le1$，所以 $\Xi$ 的每个特征值至多为一。满秩时其最小特征值不小于全部特征值的乘积 $D$；最后除以同一个 $p$，即得式 (24.2)。没有对 $\rho$ 的分母另作一次整数范数估计。证毕。

## 25. 资源界进入原左 GNS 修复的同校准应用

**命题 25.1（原生事件供给命题 20.2 的谱条件）。** 固定 $(\mathcal T,t_*,I,\mathcal E)\in\mathfrak F$，令 $\rho=\Xi/p$，并给定含同一单位的 $*$-子代数 $A\subseteq M_d$。$E=E_{\rho,A}$ 必须仍是定义 6.2 的实际左 GNS 投影，不加正性或 CP 前件。$P_A$ 为定义 20.1 的普通迹条件期望，置

$$
h=P_A(\rho),\quad \lambda=\lambda_{\min}(h),\quad
\mu=\lambda_{\min}(P_A(\Xi))=p\lambda,\quad
\Lambda_{L,d}=\kappa^{-2Ld}.
\tag{25.1}
$$

缺陷完整保留原式 (20.1) 的全部复输入量词：

$$
\begin{aligned}
\epsilon&=\sup_{\substack{x\in M_d,\ \|x\|_{\rm op}\le1\\
a\in A,\ \|a\|_{\rm op}\le1}}
 |\operatorname{Tr}(\rho(E(x)a-xa))|,\\
\delta_{\rm raw}&=\sup_{\substack{x\in M_d,\ \|x\|_{\rm op}\le1\\
a\in A,\ \|a\|_{\rm op}\le1}}
 |\operatorname{Tr}(\Xi(E(x)a-xa))|=p\epsilon.
\end{aligned}
\tag{25.2}
$$

原命题 20.2 所定义的同一 $\sigma,F$ 满足

$$
\begin{aligned}
\mu&\ge\Lambda_{L,d},&
\lambda&\ge\Lambda_{L,d}/p,\\
\|E-F\|_{\rm cb}
&\le\frac\epsilon\lambda
 =\frac{p\epsilon}{\mu}
 =\frac{\delta_{\rm raw}}\mu
 \le\kappa^{2Ld}\delta_{\rm raw},\\
\|\rho-\sigma\|_1&\le\epsilon=\delta_{\rm raw}/p,&
p\|\rho-\sigma\|_1&\le\delta_{\rm raw}.
\end{aligned}
\tag{25.3}
$$

例如原始量纲的充分条件 $\delta_{\rm raw}\le\eta_0\Lambda_{L,d}$ 保证 $\|E-F\|_{\rm cb}\le\eta_0$。若只有 $\delta_{\rm raw}$ 而不知实际 $p$，式 (24.1) 另给态界 $\|\rho-\sigma\|_1\le\kappa^{2L}\delta_{\rm raw}$；这一态界不再作为映射界的额外乘子。

证明。由定理 24.1，$\Xi\ge\Lambda_{L,d}I$。$P_A$ 正且保单位元，故 $P_A(\Xi)\ge\Lambda_{L,d}I$；线性和 $p>0$ 给 $\mu=p\lambda$。在同一 $\rho,A,E$ 上直接应用命题 20.2 得余式。以 $\Xi$ 定义左内积只将原内积整体乘以 $p$，不会改变正交投影 $E$，所以式 (25.2) 没有暗换代表。归一化因子在 $\epsilon=\delta_{\rm raw}/p$ 和 $\lambda=\mu/p$ 中精确抵消；若在此之外再乘一个独立的 $p^{-1}$，便不是式 (25.3) 的推导。证毕。

由同一命题 20.2 及推论 22.2，$P_A(\sigma)=P_A(\rho)$，$F$ 是到恰好 $A$ 的 UCP 回缩并有 CPTP 对偶；原 $E$ 在 $\epsilon>0$ 时仍未被证明为正。对所有 $a,b\in A$，$\operatorname{Tr}(\rho a^\dagger b)=\operatorname{Tr}(\sigma a^\dagger b)$，所以原保强度的二元 Gram／Finite3 几何不变。式 (25.3) 仅给这些既有结论补上实际原生族的谱参数，不重证量子表示或重建原则，也不把有限门菜单升级为完整复比较球的认证菜单。

**命题 25.2（已有原接口的更便宜谱供应）。** Setting-Source 式 (9.7)–(9.9) 的设置报告边际为 $\operatorname{diag}(r,s)$，其中 $r=\varphi^{-2}$、$s=\varphi^{-1}$，故单个原设置接口的谱底直接为 $r$，两个设置合起来为 $r^2$。原式 (9.5) 所选近 Bell 字若满足其 $\varepsilon_*=10^{-3}$ 向量比较界，则共同切口处的原生 $b_1$ 边际满足

$$
\lambda_{\min}(\rho_{b_1})>\tfrac12-\varepsilon_*=0.499.
\tag{25.4}
$$

证明。设置谱从原来的两个质量直接读取，不需要字长。近 Bell 比较目标 $e=J(|00\rangle+|11\rangle)/\sqrt2$ 在 $b_1$ 的边际是 $I_2/2$；允许整体相位的纯向量距离小于 $\varepsilon_*$，故纯态半迹距离及约化半迹距离均小于 $\varepsilon_*$。二维迹零 Hermitian 差的算符范数等于其半迹范数，因此最小特征值严格大于 $1/2-\varepsilon_*$。设置提取不操作源，故此界也适用于 $t_*$；正质量设置事件不改变该源边际。证毕。

这两个原接口有现成比较，使用其直接界即可。原来选定的 $w,u_x,v_y$ 只有有限存在性，原文没有给出已计算字长；不能给它们杜撰数值资源。在实际字一旦给定时，原共同切口前缀的 $L=|w|+2$，整段协议的最大调用数为 $|w|+2+\max_x|u_x|+\max_y|v_y|$，两个二值设置测量后再作一次完整计算基终端测量；若某字含逆字母，长度先按九次代换。定理 24.1 与命题 25.1 的用途是没有上述参考态比较的其他实际有限历史、事件及忠实切口，而非把这些较便宜的既有估计重新计为成果。

## 26. 受限源字和原报告单元中的显式忠实实例

**命题 26.1（三个源调用、两个原设置调用与实际校准）。** 从式 (23.1) 的同一个根出发，选择备选源字按时间依次调用 $K_3,K_2,K_1$，即

$$
\psi_{\rm alt}=K_1K_2K_3J|00\rangle.
\tag{26.1}
$$

再依原表调用 $K_{10},K_{13}$，依次计算投影读取 $X=b_{10},Y=b_{13}$，在局部结果路由前的原共同切口 $t_*$ 取已得事件 $\mathcal E_{00}=\{X=0,Y=0\}$。令待校准的原生因子恰为 $R=H_{\{1\}}$，于是 $d=2$，原生补因子 $Z=H_{\{-1,0,\ldots,14\}\setminus\{1\}}$ 的维数为 $e=32768$。该事件的同一校准为

$$
\begin{gathered}
p=r^2=\varphi^{-4},\qquad \Xi=p\chi,\qquad \rho=\chi,\\
\chi=
\begin{pmatrix}
s&r\beta\zeta^{-4}\\
r\beta\zeta^4&r
\end{pmatrix},\qquad
\det\chi=r^2=\varphi^{-4}>0,
\qquad r=t^2,\quad s=t.
\end{gathered}
\tag{26.2}
$$

若 $A$ 为该原生位的计算基对角代数，则原始可见校准和精确系数为

$$
h=P_A(\chi)=\operatorname{diag}(s,r),\qquad
\lambda=r,\qquad \mu=pr=r^3,\qquad
\epsilon=4r\beta,\qquad \delta_{\rm raw}=4r^3\beta.
\tag{26.3}
$$

这些是同一 $\rho$ 上命题 25.1 的实例，未把可任意准备的数学态当作输入。

证明。活跃黄金块记作

$$
K_Q=\begin{pmatrix}a&b\\b&c\end{pmatrix},\qquad
 a=\zeta[1+(\zeta-1)t]=-t,\quad
 b=\zeta(\zeta-1)\beta^3=-\beta\zeta^4,\quad
 c=\zeta[1+(\zeta-1)t^2]=-t\zeta^3.
\tag{26.4}
$$

由 $\zeta^4-\zeta^3+\zeta^2-\zeta+1=0$ 可得 $t\zeta(\zeta-1)=-\zeta^4$，再用 $\zeta^5=-1$ 分别化简对角项和 $\beta^3=\beta t$ 的非对角项，即得这些等式；特别 $|a|^2=|c|^2=r$、$|b|^2=s$、$r+s=1$。根上 $(b_1,b_2,b_3)=(0,0,1)$，其两外邻 $b_0=b_4=0$；其他源位不变。第一次 $K_3$ 给 $b|000\rangle+c|001\rangle$；第二次 $K_2$ 只在 $b_3=0$ 的分支活跃，在 $b_3=1$ 时是标量 $\zeta$，所以给

$$
ab|000\rangle+b^2|010\rangle+\zeta c|001\rangle.
$$

第三次 $K_1$ 在 $b_2=0$ 时活跃，在 $b_2=1$ 时是 $\zeta$，故得到精确的五项向量

$$
\begin{aligned}
\psi_{123}={}&a^2b|000\rangle+ab^2|100\rangle
       +\zeta ac|001\rangle+\zeta bc|101\rangle
       +\zeta b^2|010\rangle\\
={}&(a|0\rangle+b|1\rangle)_{b_1}
       \otimes(ab|00\rangle+\zeta c|01\rangle)_{b_2b_3}
       +|0\rangle_{b_1}\otimes\zeta b^2|10\rangle_{b_2b_3}.
\end{aligned}
\tag{26.5}
$$

全部五个基词合法且系数非零。右边两个补向量正交，平方范数分别为

$$
|ab|^2+|c|^2=rs+r=s,\qquad |b|^4=s^2=r.
$$

第一因子的 $f=a|0\rangle+b|1\rangle$ 已归一。因此实际偏迹为

$$
\chi=s|f\rangle\langle f|+r|0\rangle\langle0|.
\tag{26.6}
$$

这两个权重由同一原生向量中的正交补项算出，不是外加校准混合。其对角元为 $sr+r=s$、$s^2=r$，非对角元为 $sa\overline b=r\beta\zeta^{-4}$。又 $sr-r^2\beta^2=t^3-t^5=t^4=r^2$，证明式 (26.2) 的满秩。实际特征值为

$$
\lambda_\pm(\chi)=\frac{1\pm\sqrt{1-4r^2}}2>0.
\tag{26.7}
$$

原来四个设置邻位 $b_9,b_{11},b_{12},b_{14}$ 始终为零，所以两个设置调用都作用于原来的 $000$ 块，输出同一个 $f$。两个计算投影报告的完整分支原生密度正是

$$
D_{xy}=p_xp_y\,|xy\rangle\langle xy|_{XY}
       \otimes|\psi_{\rm alt}\rangle\langle\psi_{\rm alt}|
       \otimes|0000\rangle\langle0000|_{9,11,12,14},
\qquad p_0=r,\quad p_1=s.
\tag{26.8}
$$

非设置控制在此切口为原规定的固定 $c_*$。这是 Setting-Source 式 (9.8)–(9.10) 在允许备选字上的直接基向量对应，未加 ready 条件。将 $x=y=0$ 的已得分支约化到 $b_1$ 就是 $\Xi=r^2\chi$；除以实际质量 $r^2$ 才得到 $\rho=\chi$。因此 $\det\Xi=r^6=\varphi^{-12}$，不是 $\det\chi$。

为明确完整终端律，可取原控制表中的 $u_0=u_1=v_0=v_1$ 全为空字，随后作一次全部十六位的计算基终端投影。此时

$$
\Pr(x,y,z,h)=p_xp_y\,
 |\langle z|(|xy\rangle\otimes\psi_{\rm alt}\otimes|0000\rangle)|^2
 \mathbf1_{\{h=h_{xy}(z)\}}.
\tag{26.9}
$$

因子按原式 (8.7) 排列，$h$ 保留五次实际调用、两次设置报告、终端词及停止。每条路径恰有五次正向门调用，没有逆门；到 $t_*$ 有两次二值投影和四个设置历史，之后是一次 $2^{16}$ 结果的完整计算投影。等价地，终端可逐位读，最大十八次二值投影。最大调用数 $L=5$ 在每个设置分支相同；非设置控制表可取阶段 $0,\ldots,8$：阶段 $0,\ldots,4$ 依次执行这五个门，阶段 $5,6$ 依次读 $X,Y$，阶段 $7$ 是 $t_*$ 并执行终端投影，阶段 $8$ 为正常停止；再保留三个零质量失败、拒绝、提前停止吸收标签，共十二个控制标签。固定程序只有一个已选值，前缀调用档案由阶段唯一决定，报告仍留在原 $X,Y$ 单元；没有结果依赖地址或额外读表副本。正常终止质量为一，失败、拒绝及提前停止质量为零而标签保留。终端标签域有 $4\cdot2^{16}$ 个 $(x,y,z)$ 位置；式 (26.5) 的五个非零源词与四个设置值给出二十个正质量位置，其余原生离码及非法标签仍有定义并赋零质量。事件 $\mathcal E_{00}$ 在终端测量前已经获得，不依赖这些未来结果。

最后计算实际 GNS 对应。记 $\gamma=r\beta\zeta^{-4}$。由原式 (20.7)，

$$
E(x)=\operatorname{diag}\left(x_{00}+x_{01}\overline\gamma/s,
                              x_{11}+x_{10}\gamma/r\right).
\tag{26.10}
$$

对角 $A$ 下，$a=\operatorname{diag}(a_0,a_1)$ 与 $h$ 交换，原式 (20.8) 中的矩阵为

$$
\chi a-a\chi=(a_1-a_0)
\begin{pmatrix}0&\gamma\\-\overline\gamma&0\end{pmatrix}.
$$

其两个奇异值均为 $|\gamma||a_1-a_0|$，故普通迹范数为 $2|\gamma||a_1-a_0|$。完整复收缩球上 $|a_1-a_0|\le2$，并在 $a=\operatorname{diag}(1,-1)$ 取等，因此 $\epsilon=4|\gamma|=4r\beta$，由式 (25.2) 得 $\delta_{\rm raw}=p\epsilon=4r^3\beta$。也可直接取

$$
u=\gamma/|\gamma|,\qquad
x=\begin{pmatrix}0&u\\-\overline u&0\end{pmatrix},\qquad
a=\operatorname{diag}(1,-1).
$$

此时 $x^\dagger x=I$、$\|a\|_{\rm op}=1$，且式 (20.8) 给出 $\operatorname{Tr}(\chi(E(x)a-xa))=\operatorname{Tr}((\chi a-a\chi)x)=4|\gamma|$。这是原数学比较域中达到缺陷的收缩对，不增加任何原生取得或控制权限。原命题 20.2 的 $q=I$，故 $\sigma=h$、$F=P_A$；态的迹范数误差 $\|\chi-h\|_1=2|\gamma|=\epsilon/2$ 与上述完整复比较缺陷不同。每个有限放大上的两个非对角块压缩给

$$
\|E-F\|_{\rm cb}=|\gamma|/r=\beta,
\qquad
\frac\epsilon\lambda=\frac{\delta_{\rm raw}}\mu=4\beta.
\tag{26.11}
$$

上界取两个输入块的范数，较大系数为 $|\gamma|/r$；取相应矩阵单位达到它。式 (26.11) 的充分界不被冒称最优。由于 $\gamma\ne0$，原 $E$ 也不保持所有 Hermitian 输入的伴随，不能当作正映射。这里并未要求缺陷很小；它提供确切、非零缺陷、实际忠实校准的源对应。证毕。

**命题 26.2（同报告律中的忠实切口与正质量失秩）。** 在式 (26.8) 的同一个 $t_*$，另预先声明原生因子 $R'=H_{\{1,10,13\}}$，则 $d'=8$、$e'=8192$。全事件的约化是

$$
\rho'=\chi\otimes D_X\otimes D_Y>0,
\qquad D_X=D_Y=\operatorname{diag}(r,s),\qquad
\lambda_{\min}(\rho')=\lambda_-(\chi)r^2.
\tag{26.12}
$$

但在不改变 $R'$ 的条件下，已得事件 $X=0$ 的质量是 $r>0$，未归一约化及秩为

$$
\Xi'_{X=0}=r\,\chi\otimes|0\rangle\langle0|_X\otimes D_Y,
\qquad\operatorname{rank}\Xi'_{X=0}=4<8.
\tag{26.13}
$$

事件 $X=Y=0$ 的质量为 $r^2>0$，秩更降至二。证明直接将式 (26.8) 对指定因子求和或选块。故全事件在 $R'$ 上属于 $\mathfrak F$，正质量的指定报告事件在同一 $R'$ 上却不属于。命题 26.1 使用完整原生位 $b_1$ 的二维张量因子，式 (26.13) 使用八维张量因子；二者是明确不同的因子选择，不是对奇异八维校准作支撑压缩。数学偏迹没有物理删除报告，也没有复制设置记录。证毕。

源字 $K_1K_2K_3$ 是原 $0,\ldots,6$ 准备域内的一个明确备选字，不替换原式 (9.5) 选定的近 Bell 字。其 $b_1$ 边际式 (26.7) 及 $h$ 与近 Bell 的式 (25.4) 是不同对象；不把该备选字称为原非经典相关协议。它只见证源族、事件和谱应用确实有共同实例，不单独计为新的重建结论。

## 27. 供应关系与未覆盖的域

定理 24.1 和命题 25.1 的 `repo-derived` 增量是：对同一固定十六位根、实际黄金矩阵、完整有限投影反馈树及已得事件，用完整树的嵌入能量估计和实际奇偶分级，将未归一原生约化的行列式降到二次整数域，供给原命题 20.2 的同校准谱参数。标准整数范数和矩阵范数不等式为成熟供应，不主张世界范围新颖性。

| 来源 | 在此使用的准确范围 |
| --- | --- |
| [V15 §§3、8.1–8.3、9.1、引理 9.4](AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md) | 完整实际门、有限记录菜单、无分母整性、所有嵌入的逐门范数、分支奇偶分级及八次域。完整自适应树的式 (24.6) 和约化行列式的二次域应用不由其酉字界直接代入取得。 |
| [Setting-Source 定义 8.1–8.3、式 (8.5)、(8.7a)、(9.8)–(9.12)](AURIC_SINGLE_PURE_WHOLE_SETTING_SOURCE_RELATIONS_V78_CONTINUATION.md) | 唯一根、受限源字、原报告单元、非选择投影语义、共同切口及完整返回律。其设置谱与近 Bell 比较已经足够的接口按命题 25.2 直接消费。 |
| [Milne, *Algebraic Number Theory*, v3.08, Proposition 2.19、Corollaries 2.20–2.21](https://www.jmilne.org/math/CourseNotes/ANT.pdf) | `literature-attested`：有限数域范数为嵌入乘积，整元的范数为整数，非零整元范数非零。它不提供本原生树的共轭大小、奇偶约化或忠实切口。 |
| [Remscrim, *The Power of a Single Qubit: Two-way Quantum Finite Automata and the Word Problem*, arXiv:2003.09879v2, Lemma 3.6](https://arxiv.org/abs/2003.09879v2) | `literature-attested` 的相邻方法是有限代数酉生成元的指数型字分离及整数范数论证；其迹与中心分离结论不是自适应投影树或切口谱定理，不借用其提取指数。 |
| 本卷定义 6.1、20.1、命题 20.2、§§21–22 | 原完整复缺陷、未知正性的实际左 GNS $E$、有条件数的 $\sigma,F$ 及可见 Gram／Finite3 结论全部复用。这里没有缩小输入比较球或修改修复目标。 |
| [V38 §§5、10](AURIC_COMPLETE_QUANTUM_PROCESSES_INTERNAL_MEMORY_AND_RANK_BOUNDARY_STABILITY_V38.md)；[Native Terminal Certification §§18–23](RECURSIVE_RELATIONAL_OBSERVATION_FIBONACCI_NATIVE_TERMINAL_CERTIFICATION.md) | 已有条件质量、秩边界稳定、实际纯源面上的终端区分范数及字典条件数。它们不供应本 $\rho=\Xi/p$ 的黄金资源谱底，也不被重复计作此应用。 |
| [V94 定理 4.2、17.1、20.1](AURIC_BINARY_REFERENCE_ENDOGENOUS_SUFFICIENT_REDUCTION_AND_QUANTUM_VISIBLE_ALGEBRA_V94.md) | 条件可见代数／CP 分类、内部记录等距及逐分支自治插入；不从其抽象等距取得原生黄金门编译、同一 $\rho$ 的制备或此资源界。 |

式 (24.2) 不覆盖自由选定的任意校准权重、任意输入态、任意代数基或任意测量菜单；尤其不能只因某校准忠实就断言它有此 $L$。其他切口必须重新声明原生位置、补因子及满秩条件。奇异事件、支撑压缩、无限重试、非完整结果树、未计价的相干控制、外来分母和随机币都没有进入此结论。对固定 $d$，$L$ 增大时此谱底可以趋零，故不与 §21 的坏条件数现象冲突，也不是资源无关的下界。

在原共同切口，完整返回源 $Q$ 包括全部非设置原生位、固定非设置控制和档案；Setting-Source 式 (9.9) 的条件 $Q$ 态是纯态，秩为一。此处较小原生因子的忠实性不使整个 $Q$ 忠实。原生报告边际的数学选择也不实现任何档案复制、擦除或共同全历史取得。完整复比较访问、$F$ 或 $\sigma$ 的原生实现、V81 的原共同分支／全程返回取得仍需各自的实际历史与返回合同；终端诊断投影、抽象范数或一般复制障碍不能替代它们。唯一 $\Omega$ 的内部读出解释保持定义 22.1 的合法联合域；共同起源不增添独立性和自由访问。Finite3 仍为保尺度的二元 Gram 几何，不限制整体 Hilbert 维数为三。本节组是上述模型中的解析条件推导，不推出经验性的量子起源或整体本体真实性。

## 追加锚（本行以下为增补区）

## 28. 实际忠实校准的 Petz 回推与完整原生编译障碍

**定义 28.1（固定反向、合法输入及保留记录的目标）。** 保留定义 23.1–23.2 的唯一根 $\Omega_0$、全部地址 $0,\ldots,13$、完整有限投影反馈树及原控制和档案。取原生因子 $R=H_{\{1\}}$、原生补因子 $Z=H_{\{1\}^c}$，并记 $P_j=|j\rangle\langle j|_R$。实际计算投影读取 $b_1$ 的非选择边际是

$$
\Delta(X)=P_0XP_0+P_1XP_1.
\tag{28.1}
$$

该读取的原结果 $j$ 始终保留，故完整装置不是只含 $\Delta$ 的无记录通道。参照固定为命题 26.1 的实际 $\chi$：它已经是按时间调用 $K_3,K_2,K_1$ 后的无条件 $b_1$ 边际；原设置调用和读取不改变它。这里不把 $\chi$ 宣告为可独立输入的免费态。沿用 $s=t=\varphi^{-1}$、$r=t^2$、$\gamma=r\beta\zeta^{-4}$，于是

$$
\chi=\begin{pmatrix}s&\gamma\\\overline\gamma&r\end{pmatrix},
\quad \det\chi=r^2>0,\quad h=\Delta(\chi)=\operatorname{diag}(s,r).
\tag{28.2}
$$

固定的数学反向是 [C123《内部参照等价与模核》式 (5)、命题 4.2](AURIC_INTERNAL_REFERENCE_EQUIVALENCE_AND_MODULAR_CORE_C123.md) 在 $\mathcal N=\Delta,\sigma=\chi$ 上的同一个 Petz 映射

$$
\mathcal R_\chi(Y)=\chi^{1/2}\Delta(h^{-1/2}Yh^{-1/2})\chi^{1/2},
\qquad Q_j=\frac{\chi^{1/2}P_j\chi^{1/2}}{\chi_{jj}},
\qquad \mathcal R_\chi(Y)=\sum_jY_{jj}Q_j.
\tag{28.3}
$$

$h$ 在整个 $R$ 上可逆。$\mathcal R_\chi(h)=\chi$ 是该既有公式的参考恢复性质；$\gamma\ne0$ 时，C123 命题 4.2 又说明不能改用对角参照而仍声称反向不变。

输入承诺覆盖从同一根取得的每个原合法有限前缀 $\mathcal P$，其分支在共同切口对齐；提前停止、失败和零质量分支仍按定义 23.1 保留。记原程序身份为 $\pi(\mathcal P)$，完整已得档案为 $a$，未归一原生分支密度为 $D_a^{\mathcal P}$。已吸收的停止分支保持其原密度、原档案和原质量，不增加读取、报告或后继调用。对仍可合法执行上述读取的分支，数学目标逐分支规定：读取后原标签 $(\pi(\mathcal P),a,j)$ 不变，量子输出为

$$
\Theta_{a,j}^{\mathcal P}
=(\mathcal R_\chi\otimes\operatorname{id}_Z)
 \bigl[(P_j\otimes I_Z)D_a^{\mathcal P}(P_j\otimes I_Z)\bigr].
\tag{28.4}
$$

这是理想局部反向及身份扩张的定义，不是新增原生能力。其完整目标读出由这些未归一块、每个原 $(\pi,a,j)$、全部十六位终端计算基词 $z$ 和原停止标签给出；质量为 $\langle z|\Theta_{a,j}^{\mathcal P}|z\rangle$，所有零位置也保留。已吸收分支另以原完整停止记录及原计算读出律保留，不给它们添加 $j$ 项；活跃分支中的理想映射也不创造一次新的原调用。实现可增加自己的程序身份和有限延续档案 $k$，但必须全部保留；式 (28.4) 要求对每个原 $(\pi,a,j,z)$ 的质量分别相等，比较时只对新增 $k$ 求和，不合并或重标原档案。新增失败、拒绝及提前停止位置的理想质量为零。对新增档案的数学求和不是物理擦除，也没有假设原菜单能在停止后继续调用。

较弱的边际编译目标只要求固定 $\mathcal R_\chi$ 在每个上述实际读取输出上的 $R$ 边际正确，不要求式 (28.4) 的补因子和原记录身份扩张。两项目标都包括空源程序：不作源调用时，同一 $\Omega_0$ 的 $b_1$ 为 $P_0$，读取后仍是 $P_0$，$j=0$ 的质量为一。编译器可使用全部原菜单、实际反馈和任意有限资源；即使允许依已知原程序选择不同的有限原生延续，也不能删掉这个输入。承诺量词没有把输入局限为 $h$ 或只局限为产生 $\chi$ 的历史。

**命题 28.2（全输入编译分离及同参考历史的保留读数分离）。** 在定义 28.1 下，不存在一个精确有限完整原生编译器满足较弱的边际目标，因而也不存在满足式 (28.4) 的编译器。此外，仅对命题 26.1 的同一实际参考源历史要求式 (28.4)，已经不能精确编译；后一结论不使用空源输入。

证明。令 $d_0=1+2r$。式 (28.2) 的具体平方根为

$$
\chi^{1/2}=\frac{\chi+rI}{\sqrt{1+2r}}
=\frac1{\sqrt{d_0}}
 \begin{pmatrix}1&\gamma\\\overline\gamma&2r\end{pmatrix}.
\tag{28.5}
$$

直接平方即可核对：$|\gamma|^2=r^2s$、$r+s=1$，两个对角项分别给 $s,r$，非对角项给 $\gamma$；$\chi+rI>0$ 固定正平方根。由式 (28.3)，空源输入的终端事件 $\mathcal E_\varepsilon=\{z_1=1\}$ 的理想原始质量为

$$
q=\operatorname{Tr}(P_1Q_0)
 =\frac{|\gamma|^2}{s(1+2r)}
 =\frac{r^2}{1+2r}
 =\frac{13-5\sqrt5}{22}
 =\frac{4-5t}{11},
\qquad N_{k/\mathbb Q}(q)=\frac1{11},
\quad k=\mathbb Q(\sqrt5).
\tag{28.6}
$$

这个输入来自原根，不来自新制备、复位、复制或参考附接。任何候选实现与这一输入前缀合起来，仍是定义 23.1 的完整有限原生树。事件 $\mathcal E_\varepsilon$ 对全部新增档案及其他终端位求和；没有按成功条件归一化。由 [V15 定义 8.1、定理 8.2](AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md) 和本卷式 (24.10)，其实际质量 $p_\varepsilon\in\mathcal O_k$。整元的二次域范数为整数，而式 (28.6) 的范数不是整数，故 $p_\varepsilon\ne q$。这已排除全输入边际编译目标，且量词包含所有菜单地址、所有有限反馈和全部失败、停止分支，并非只排除酉字或某个编码子菜单。

再固定实际前缀 $\mathcal P_\chi$：按时间调用 $K_3,K_2,K_1,K_{10},K_{13}$，依次读取原 $X=b_{10},Y=b_{13}$，取命题 26.1 的 $t_*$，随后只增加上述原生 $b_1$ 计算读取。源结果路由字仍取空字。原程序及其每个设置档案 $a_{xy}$、原记录单元 $X,Y$、新增已得读数 $j$ 全部保留。切口分支 $D_{xy}$ 恰为式 (26.8)，并满足

$$
\sum_{x,y}\operatorname{Tr}_Z D_{xy}=\chi,
\qquad
\operatorname{Tr}_Z[(P_0\otimes I)D_{xy}(P_0\otimes I)]
=p_xp_y sP_0.
\tag{28.7}
$$

式 (28.4) 的目标对每个 $(x,y,j)$ 分别定义，绝非只给粗化后的同一参考态。考虑保留原程序身份的终端事件

$$
\mathcal E_\chi=\{\pi=\pi(\mathcal P_\chi),\ j=0,\ z_1=1\},
\qquad
w=\Pr_{\rm ideal}(\mathcal E_\chi)
 =\sum_{x,y}p_xp_y s\operatorname{Tr}(P_1Q_0)
 =sq=\frac{9\sqrt5-19}{22}
 =\frac{-5+9t}{11}.
\tag{28.8}
$$

这里对 $x,y$、其他终端位及新增档案求和，只是在完整原记录空间内选择一个事件；所有原 $a_{xy}$ 仍各自存在。$w>0$，而

$$
N_{k/\mathbb Q}(w)=-\frac1{11}.
\tag{28.9}
$$

任何完整有限原生候选的同名事件质量仍在 $\mathcal O_k$，所以不等于 $w$。这证明了同一实际参考历史上的加强目标也失败。该目标的 $R$ 无条件边际确为 $\mathcal R_\chi\Delta(\chi)=\chi$；分离来自要求保留 $j$ 及其联合读出关系，不能用该边际相等消去。

此处被反驳的是缩小到 $b_1$ 的 Petz 映射及式 (28.4) 明确规定的记录／补因子扩张，不是完整记录装置或全局原生通道的 Petz 反向。后者须把实际输出、所有记录和全局参照重新代入其自身公式；本源的全局纯态参照也不是忠实的全矩阵参照。式 (28.4) 作为完整 Hilbert 空间上的理想目标甚至未承诺保持 $\mathcal L$，这种数学身份扩张不能反过来授予原生局部控制。若只承诺某个过程将单一 $h$ 的无条件 $R$ 边际返回 $\chi$，而不承诺该固定反向的全输入作用或式 (28.4) 的同记录作用，两种分离均不构成对此较弱承诺的否定。证毕。

**推论 28.3（整棵协议的原始事件误差与正向调用资源）。** 对上面两个输入分别取任意完整有限原生实现，令 $L_\varepsilon,L_\chi$ 为从原根到终端的整棵树最大正向 $K$ 调用数，逆调用先按 $K_j^{-1}=K_j^9$ 展开。令 $p_\varepsilon,p_\chi$ 为其对应原始事件质量，$\kappa=1+2\varphi^3$，则

$$
\begin{aligned}
|p_\varepsilon-q|
 &\ge\frac1{11\left(\kappa^{2L_\varepsilon}
                    +(13+5\sqrt5)/22\right)},\\
|p_\chi-w|
 &\ge\frac1{11\left(\kappa^{2L_\chi}
                    +(19+9\sqrt5)/22\right)}.
\end{aligned}
\tag{28.10}
$$

$\mathcal P_\chi$ 在每个原设置和读数分支前有五次正向调用，因此若后继整树最大展开调用数为 $\ell_\chi$，则 $L_\chi=5+\ell_\chi$；空源前缀没有门调用，$L_\varepsilon=\ell_\varepsilon$。这里的最大值包括零质量、失败、拒绝、提前停止和正常停止路径，不能换成成功路径的调用数。测量数 $m$、分支数界 $b$、全部控制和档案状态集仍须各自有限，并按定义 23.1 声明。

证明。复用式 (24.6)、(24.8)、(24.10) 对完整终端事件的结论，对任一个实际质量 $p$ 都有

$$
p\in\mathcal O_k,\qquad |\nu(p)|\le\kappa^{2L},
\qquad \nu(t)=-\varphi.
\tag{28.11}
$$

分别取 $a=q,w$ 和 $u=11a$。式 (28.6)、(28.8) 给 $u\in\mathcal O_k$、$N(u)=11,-11$。由于 $p\ne a$，

$$
\begin{aligned}
0\ne N(11p-u)
 &=121N(p)-11\operatorname{Tr}_{k/\mathbb Q}(p\nu(u))+N(u)
 \in11\mathbb Z,\\
11&\le121|p-a|\,|\nu(p)-\nu(a)|
 \le121|p-a|\bigl(\kappa^{2L}+|\nu(a)|\bigr).
\end{aligned}
\tag{28.12}
$$

再用 $\nu(q)=(13+5\sqrt5)/22$、$\nu(w)=-(19+9\sqrt5)/22$，即得式 (28.10)。这一整树估计不按叶逐一放大，因而没有额外叶数因子。若比较完整保留记录的实际终端律与任一满足目标原记录边际的终端律，其总变差距离至少为对应单事件差；新增档案的任何保留扩展都不能改变这个必要下界。没有把这些实际输入与实际读口的误差自动提升为任意输入／参考上的 diamond 范数，也没有由下界推出原菜单存在某个逼近序列或精度上界。证毕。

上述应用的 `repo-derived` 内容是固定原根、实际 $\chi$、合法空源输入、同参考历史及完整记录目标之间的对应和两个资源下界。整性与完整树共轭界直接消费 V15 和本卷定理 24.1；Petz 公式与参照分类直接消费 C123 式 (5)、命题 4.2。Petz 充分性本身为既有理论，原始来源见 [Petz, *Sufficient subalgebras and the relative entropy of states of a von Neumann algebra*, CMP 105, 123–131, DOI:10.1007/BF01212345](https://doi.org/10.1007/BF01212345)，不在此重建或主张文献优先权。[C122 §5](AURIC_INTERNAL_BINARY_RECIPROCITY_AND_EXPLICIT_RECONNECTION_C122.md) 的执行路线另需同一完整实现及其逆、初始化与支持投影、最大混合辅助态、参照滤片以及放大所需的相干控制；黄金门自己的九次逆调用不供应这些额外资源。[C118-IBRC §十二](AURIC_C118_IBRC_INTERNAL_BINARY_RELATION_CLOSURE.md) 和 [C133 命题 5.2、5.5、§6.1](AURIC_C133_THREE_READ_CLOSURE_VISIBLE_COMPLEX_GEOMETRY.md) 的结构／可见表示边界均保留，它们没有给这个固定菜单新增控制。这里已采用原 Born 记录律，结论只约束该律下的有限原生编译；不把它循环称为 Born 起源，不解决全局物理实现、完整记录仪器的反向、$\xi=5/2$ 的全域最小值或整个极小点集。

## 追加锚（本行以下为增补区）
