# 黄金回返与二元量子关系

> 参考输入：AI 撰写的工作稿，由用户提供于本会话（2026-11-04，Asia/Singapore）。Lean 是仓库的数学真源；本文仅为参考文稿，未作形式化认证。

Zeckendorf 的进位如何进入相位校准

AURIC C132

定义、等价定理、反例、有限维量子理论的条件重构

项目固定版本：`d9880e9f2c32`；提交时间：2026 年 11 月 4 日 19:01:29（新加坡）

**本轮结论。**
Zeckendorf 三值差额确实能进入上一轮的相位问题，但作用在两个不同层次：
它的*整数性*使圆周上的合成没有进位歧义；黄金共轭根的交替收缩则让同一转角沿斐波那契步数从两侧返回。
这给出一个与现有黄金编码共用相位参照的完整候选。
三值差额本身既不是正核，也没有推出 Born 律。

令 $F_0=0,F_1=1$，$\phi=(1+\sqrt5)/2$，$z=e^{2\pi i/\phi}$，
$\mathcal S=\mathbb N[z]$。原始历史标签集 $X$ 任意，原始复值二元表 $K$ 任意。
对有限配方定义同一合计

$$
B(f,g)=\sum_{h,k}\overline{f(h)}K(h,k)g(k),
 \qquad Q(f)=B(f,f).
$$

本轮只提出下列一个候选：

$$
\boxed{\quad
 \operatorname{Re}B(f,z^{F_j}f)\le \operatorname{Re}B(f,f),
 \qquad f\in\mathcal S^{(X)},\quad j\ge2.
 \quad}\tag{C132}
$$

**一句白话：**同一份历史向前走斐波那契步，回来和自己对照，读数不能比原来对齐时更大。

本稿证明：在上述明确的合计语义下，C132 当且仅当 $K$ 为 Hermitian 正半定核。
因此它恢复 C131 的三相位校准，也恢复 C130 的二元平均预算。
本轮统一的是*回返参照与二元比较的写法*：黄金编码给出同一个转角及其正次数回返。
C131 的直角方向本来也由一个 $i$ 生成，因此这里不声称独立生成元从三个减到一个。
整条回返序列及稠密配方的连续延拓仍需保留；这不是把无限条件变成一次实验，也不是比正核更弱的新物理定律。

**内生性的准确位置。**
$\beta$、进位、回返与相位合成之间的恒等式可以从项目内的定义和证明推出。
原始读数为何遵守 C132、上述相位操作能否由原过程实际执行、效果与复合接口是否齐全，仍是需要来源证明的关系。
把这些关系写在一行，不能使未证前提自动消失。

**阅读路线。**
先核对项目与算术，再证明候选和必要边界；
随后区分算术圆周、三元关系与 Bloch 几何，
最后给出 Hilbert、完全正过程、Born、更新、张量与酉动力学的精确条件链。
这是一份数学研究工作稿；不声称发现了新的实验规律，也不声称本轮重新运行了项目 Lean 验证。

## 目录

- [1. 最新源码与本轮接口](#section-1)
- [2. Zeckendorf 读数中的整数补偿](#section-2)
- [3. 唯一候选：同源回转不能提高自己的实读数](#section-3)
- [4. 从回返校准重建比较空间与旧候选](#section-4)
- [5. 支持圆、三片窗口与三元关系](#section-5)
- [6. 从黄金回返约束恢复有限量子规则](#section-6)
- [7. 把约束放回历史、观察者与原过程](#section-7)
- [8. 本轮完成的回溯与完整白话](#section-8)
- [参考文献](#references)

<a id="section-1"></a>

## 1. 最新源码与本轮接口

<a id="sec-c132-source"></a>

### 1.1 固定快照及新增范围

本轮一次性核对默认分支 `dev`，固定提交为
`d9880e9f2c329bb3db982f33791419d5d90126b9`。
提交时点是 2026-11-04 11:01:29 UTC，即新加坡时间 19:01:29。
相对 C131 的 `2c54932b6f9a`，完整可达新增提交为 26 个，
其中第一父链为四次合并；关闭重命名推断后的实际树差分为 150 条路径，
含 32 新增、118 修改。计数采用固定两端的完整比较与父链核对，
没有把浅缓存的局部日志当作完整祖先集合 [1](#ref-repo-c132-pin)。

本轮有关量子理论的文字更新恰有两处：C117 追加第 25–29 节，
以及新增四路径续卷 IV。
`D5/S3/Quantum`、`D5/S3/ConceptDynamics` 与
`D5/S1/Deficit`、`D5/S1/Digit` 子树均与 C131 相同。
因此，下面使用的 $\beta$、三值亏损和带符号进位定理是既有结果，
本轮确有新的条件性正性研究，但没有相应新增的量子 Lean 子树证明。

### 1.2 新进展真正完成了什么

C117 定义 25.1、定理 25.2 的进展是*整个既定记录图的兼容正性修复*：
若同一来源的全部原始响应，都由固定有限种子经实际合法正字作用作精确非负展开，
则可构造同一兼容常数族 $c$，把有符号仿射近似 $f$ 修为
$G=(f+\theta c)/(1+\theta)$。
在原归一化及全部已给仿射记录关系下，此修复同时恢复正性，
并有趋零误差界。有限正生成与系统依赖的正下界 $\kappa$ 是明确前件，
尚未证明原生全部未来满足它们 [6](#ref-repo-c117)。

其后的反例与有限证书进一步锁定这个缺口：
第 26 节用实际后缀 $3$ 说明仅凭裸终端的 1024 个标签不能保证生成完整未来；
第 27 节构造每个请求至多三标签的固定辅助图，使逐标签残差趋零，
共同修复距离却保持 $(1-1/\sqrt2)/2$；该辅助图没有被认定为实际原生菜单。
第 28 节在*实际共同父请求及记录边确已供应*时给出四个实际前缀的有限证书。
第 29 节继续保留未知原生响应、比较 Born 族与辅助响应的区别。
这些结果没有将“有日志”直接升级为全未来正性或 Born 规则 [6](#ref-repo-c117)。

续卷 IV 定理 49.1 在原来的密度矩阵、反馈及归一效果域中，
定位选定几何比较族的唯一退化点，并在消去稳定方向后证明指定坐标的四次项为正；
其结论是声明的相位反馈部分中的局部分类及右侧竞争分支。
它不声称全域最优或整个 $U(4)$ 的局部分类，也不提供本轮单相位的原生实现 [7](#ref-repo-fourpath)。

### 1.3 黄金算术已供应什么，尚未供应什么

源码的索引是 $W_i=F_{i+2}$，故

$$
n=\sum_i\varepsilon_iF_{i+2},\qquad
 \beta(n)=\sum_i\varepsilon_i\phi^{i+2},\qquad
 \delta(a,b)=\beta(a)+\beta(b)-\beta(a+b)\in\{-1,0,1\}.
$$

这里 $\varepsilon_i$ 是有限、无相邻占据的规范数字。
源码已证明 $\delta$ 等于最低两种进位的净带符号次数；
这是净边界量，不是总执行步数，更不是非负日志长度 [2](#ref-repo-beta)、[4](#ref-repo-carry)。
它还已有 Beatty 闭式、实数模一的黄金相位分区，以及一般加性截面的
余循环与余边界消去判据 [3](#ref-repo-beatty)、[5](#ref-repo-cocycle)。
三种进位值本身没有给出 $1,i,-i$ 三个量子相位或正核。

本轮改用 $z=e^{2\pi i/\phi}$ 及其 Fibonacci 回返，是新的*形式候选接口*。
不能从黄金系数相同推断原始响应保持相同关系：C117 定义 17.3 已明确区分
方向矩阵的黄金四时恒等式与未知响应在全部上下文保持该恒等式的额外条件。
原门的 $K_j^{10}=I$ 只供应各自的有限正字逆作用；
它不意味着所有门字均有限阶，也没有供应本轮精确的 $z$ 相位操作 [6](#ref-repo-c117)。
形式有限配方及它们的极限用于后文数学证明；
是否存在同一原生控制、比较与记录接口实现这些配方，仍须另外核实。

本轮下载的 37 份源文件均与固定 Git 树的 blob 摘要吻合。
其中 35 份相关 Lean 与 Blueprint 原文全文核读；C117 新增五节全文核读，
并复核其部分旧前件；续卷 IV 核读定理陈述、设定及依赖边界，
未逐式重审中间全部代数。没有运行新的 Lean 构建，亦不作全仓库认证。

<a id="section-2"></a>

## 2. Zeckendorf 读数中的整数补偿

<a id="sec-c132-zeckendorf"></a>

项目已有规范位串、黄金双面读数、Beatty 闭式及进位账的明确对应 [2](#ref-repo-beta)、[3](#ref-repo-beatty)、[4](#ref-repo-carry)。这里固定索引并给出自足推导；它将说明本轮相位控制来自哪条算术关系。

### 2.1 两种实嵌入与严格窗口

取 $F_0=0,F_1=1$，$F_{j+2}=F_{j+1}+F_j$，并令
$\phi=(1+\sqrt5)/2$、$\alpha=1/\phi$、$\psi=-\alpha=1-\phi$。
自然数含 $0$。规范展开 $n=\sum_{j\ge2}d_jF_j$ 的位 $d_j\in\{0,1\}$ 有限支撑且不相邻；零用空展开。定义

<a id="eq-c132-beta-definitions"></a>

$$
\beta(n)=\sum_jd_j\phi^j,\qquad
 e(n)=\sum_jd_j\psi^j,\qquad
 \kappa(n)=\sum_jd_jF_{j-1}\in\mathbb Z.
\tag{1}
$$

$e$ 是黄金数域的代数共轭读数，仍是实数；它不是复数虚部。

### 命题 2.1（严格窗口及闭式）

对每个 $n\ge0$ 有

<a id="eq-c132-window-beatty"></a>

$$
\begin{aligned}
 &\alpha-1<e(n)<\alpha,\qquad
 \kappa(n)=\lfloor(n+1)\alpha\rfloor,\\
 &\beta(n)=n\phi+\kappa(n)=\sqrt5\,n+e(n),\qquad
 e(n)=\alpha-\{(n+1)\alpha\}.
 \end{aligned}
\tag{2}
$$

这里 $\{x\}=x-\lfloor x\rfloor$。

**证明。**
相同递推及初值给 $\phi^j=F_j\phi+F_{j-1}$，共轭后也成立，故 $\beta=n\phi+\kappa$、$e=-n\alpha+\kappa$。
由于位串有限，分别用全部偶位与全部奇位的无限尾和严格控制，得

$$
-\frac{\alpha^3}{1-\alpha^2}<e(n)<\frac{\alpha^2}{1-\alpha^2}.
$$

由 $\alpha+\alpha^2=1$，两端为 $\alpha-1$ 与 $\alpha$。于是整数 $\kappa$ 严格位于 $(n+1)\alpha-1$ 与 $(n+1)\alpha$ 之间；后者无理，唯一这样的整数是其下取整。其余等式随即成立。

仓库的上移读数为 $n+\kappa(n)=\lfloor(n+1)\phi\rfloor-1$，故这里的闭式与原位移读数一致 [3](#ref-repo-beatty)。
两面可同时放入平面格

<a id="eq-c132-golden-lattice"></a>

$$
\mathcal L=\{(m+n\phi,m+n\psi):m,n\in\mathbb Z\}\subset\mathbb R^2.
\tag{3}
$$

其基向量 $(1,1),(\phi,\psi)$ 的行列式绝对值为 $\sqrt5$。用宽度为 $1$ 的半开窗 $\widetilde I=(\alpha-1,\alpha]$ 筛选第二坐标，每个整数 $n$ 恰留下一个 $m$；对 $n\ge0$，留下的点就是 $(\beta(n),e(n))$，且位于窗口内部。这是明确的切窗投影结构。

### 2.2 三值是越过哪条窗界

### 命题 2.2（精确进位区间）

令 $\tau(n)=\{(n+1)\alpha\}=\alpha-e(n)$，并定义

<a id="eq-c132-carry-defect"></a>

$$
\begin{aligned}
 \delta(a,b)&=\beta(a)+\beta(b)-\beta(a+b)\\
 &=\kappa(a)+\kappa(b)-\kappa(a+b)
 =e(a)+e(b)-e(a+b).
 \end{aligned}
\tag{4}
$$

若 $s=\tau(a)+\tau(b)$，则

<a id="eq-c132-carry-bands"></a>

$$
\delta(a,b)=-\lfloor s-\alpha\rfloor
 =\begin{cases}
 1,&s<\alpha,\\
 0,&\alpha\le s<1+\alpha,\\
 -1,&s\ge1+\alpha.
 \end{cases}
\tag{5}
$$

**证明。**
对 $(a+1)\alpha+(b+1)\alpha-\alpha=(a+b+1)\alpha$ 分离整数部与小数部，直接得到下取整公式。因 $0\le s<2$，只有所列三种整数。自然数轨道不落在两条分界线上：若 $s=\alpha$ 或 $1+\alpha$，则 $(a+b+1)\alpha$ 为整数，与无理性矛盾。

三种值都出现：$\delta(1,1)=1$、$\delta(1,2)=0$、$\delta(2,2)=-1$。
等价地，先相加的共轭坐标超过 $\alpha$ 就减 $1$，落到 $\alpha-1$ 以下就加 $1$，使结果回到同一窗口。两面同时减去同一个整数 $\delta$，而差解码 $(\beta-e)/\sqrt5$ 不变。
项目的进位桥把该整数识别为底部带符号进位账；保留全部黄金幂的高位重写同时保持两面 [4](#ref-repo-carry)。这里的补偿是原定义间的约束，不是另加一条概率规则。

### 2.3 三路拼接与可消去范围

### 命题 2.3（离散计步上的余边界）

有 $\delta(0,a)=0$、$\delta(a,b)=\delta(b,a)$，且

<a id="eq-c132-cocycle"></a>

$$
\delta(a,b)+\delta(a+b,c)
 =\delta(b,c)+\delta(a,b+c).
\tag{6}
$$

**证明。**
两边展开后均为 $\kappa(a)+\kappa(b)+\kappa(c)-\kappa(a+b+c)$。这正是项目的一般截面进位余循环结构 [5](#ref-repo-cocycle)。

把 $\kappa$ 的下取整公式仅在代数上延至 $\mathbb Z$，仍以其余边界定义 $\delta$，再令

$$
(a,r)\star(b,s)=(a+b,r+s+\delta(a,b)).
$$

变换 $(a,r)\mapsto(a,r+\kappa(a))$ 将此运算化为逐分量相加。因此本离散整数标签上的中心扩张分裂：$\delta$ 是 $\kappa$ 的余边界，而重括号的两条路没有额外残差。对任意实 $\vartheta$，作为加法乘子的 $e^{i\vartheta\delta(a,b)}$ 也可用 $e^{i\vartheta\kappa(a)}$ 的重相位消去。

这个结论有明确范围。消去进位改用线性截面 $n\phi$，通常会离开规范窗口；它没有抹去窗口内的进位账。整个圆 $\mathbb R/\mathbb Z$ 也不存在连续的全局实数截面：若存在，则 $s([t])-t\in\mathbb Z$ 在 $0\le t\le1$ 上连续而恒定，但首尾因 $[0]=[1]$ 又相差 $1$，矛盾。因此不能把离散余边界的可消去性扩大成一切圆绕数或量子环相位都为零。

### 2.4 从整数补偿得到一个相位生成元

### 命题 2.4（最小的进位识别）

设 $A=\mathbb Z[\phi]$ 为加法群，$T:A\to G$ 为到阿贝尔群的加法同态。则 $T\circ\beta$ 在自然数加法下保持相加，当且仅当 $T(1)=0$。这种读出都唯一经过商 $A/\mathbb Z$。

**证明。**
若复合读出可加，由 $\delta(1,1)=1$ 得 $T(1)=0$；反向因为每个缺损都是整数，$T(\delta)=0$ 即给可加性。此时 $\bar T([a])=T(a)$ 与整数代表无关，给唯一分解。

因此整数子群是所有进位盲加法读出必须识别的最小子群。但 $A/\mathbb Z\cong\mathbb Z$ 只是代数结论；已有实嵌入把它送到 $\mathbb R/\mathbb Z$ 的稠密子群 $n\phi\bmod1$，取拓扑闭包才得到整圆。再选复圆表示 $t+\mathbb Z\mapsto e^{2\pi it}$，令

<a id="eq-c132-phase-character"></a>

$$
\chi(n)=e^{2\pi i\beta(n)},\qquad
 z=e^{2\pi i\alpha}=\chi(1),\qquad
 \chi(a+b)=\chi(a)\chi(b),\quad \chi(n)=z^n.
\tag{7}
$$

乘法性只需 $\delta\in\mathbb Z$：整数补偿在单位周期内抵消。闭式也给 $\beta(n)=n\alpha+(n+\kappa(n))$，直接证明同一公式。取单一占据位 $F_k$、$k\ge2$ 时，$\beta(F_k)=\phi^k$；后文的 Fibonacci 回返探针由这些单位置读数产生。

这一步明确使用复圆表示，并未从全实黄金数域推出复数。黄金范数为 $(m+n\phi)(m+n\psi)=m^2+mn-n^2$，是不定二次型；乘 $\phi$ 的两个实特征值为 $\phi,\psi$，不能成为某个正定度量下的正交四分之一转。

还须区分控制与待检关系：$\delta$ 本身不是正核，因为 $\delta(2,2)=-1$。若仅用 $K_\chi(a,b)=\overline{\chi(a)}\chi(b)$ 作比较核，确实得到秩一正核，但其任意三元环积均为 $1$。C132 以 $\chi$ 生成探针，并不要求任意历史的原始核等于这个秩一核。

**白话。**一串整数先有唯一的非相邻位表示。同一串位从黄金比的两面看，一面展开，另一面始终留在一条宽度为一的窄窗里。两份内容相加时，越出哪边就补回一个整数；两面补的是同一笔，差解码仍然一致。要让这种补偿不妨碍相加，就必须识别整数这一个方向。选好圆的表示后，由同一相位生成元不断向前取幂；量子正关系还要由下一步的自比较条件来选择。

<a id="section-3"></a>

## 3. 唯一候选：同源回转不能提高自己的实读数

<a id="c132-golden-return-core"></a>

本节只提出一条候选。它把 C131 的三个指定相位，改为一个相位生成元及其 Fibonacci 回返。这把指定的直角参照换成与项目黄金编码共用的回返参照。检验族成为无限族，不能据此声称检验总量更少。C131 的三个方向本来也由单一 $i$ 生成，且 $\mathbb N[i]=\mathbb Z[i]$；本轮不主张独立生成元数目减少。

### 定义 3.1（原始核、正整数配方与回返）

<a id="c132-definition-data"></a>

取任意集合 $X$ 和任意复值函数 $K:X\times X\to\mathbb C$，不先要求对称或正性。令

$$
\phi=\frac{1+\sqrt5}{2},\quad z=e^{2\pi i/\phi},\quad
 \mathcal S=\mathbb N[z]
 =\left\{\sum_{j=0}^{m}n_jz^j:n_j\in\mathbb N\right\},\qquad
 \mathcal R=\mathcal S^{(X)}.
$$

这里 $\mathbb N$ 包含零，括号表示有限支持。对配方定义有限和

$$
B(f,g)=\sum_{h,k}\overline{f(h)}K(h,k)g(k),\qquad Q(f)=B(f,f).
$$

Fibonacci 数满足 $F_0=0,F_1=1,F_{k+1}=F_k+F_{k-1}$。本轮唯一候选为

<a id="c132-axiom"></a>

$$
\boxed{\quad
 \Re B\bigl(f,z^{F_k}f\bigr)\le\Re B(f,f)
 \quad(f\in\mathcal R,\ k\ge2).
 \quad}
\tag{8}
$$

右侧与左侧共享同一份配方，第二个对象仅沿一个生成元回转。配方不再显式调用负系数或精确的 $\pm i$；复数乘法、共轭、有限聚合和实部读取仍是输入。$\mathcal S$ 的自然数系数只是形式重复，未假定能复制未知量子态。

### 引理 3.2（Fibonacci 回返恰从两侧逼近原方向）

<a id="c132-lemma-return"></a>

对 $k\ge2$，有

<a id="c132-return-identity"></a>

$$
\frac{F_k}{\phi}-F_{k-1}=(-1)^{k+1}\phi^{-k},\qquad
 z^{F_k}=e^{i\theta_k},\quad
 \theta_k=2\pi(-1)^{k+1}\phi^{-k}.
\tag{9}
$$

因此 $0<|\theta_k|<\pi$；奇数项为正，偶数项为负，均趋于零。

**证明。**
令 $E_k=F_k/\phi-F_{k-1}$。由 $\phi^2=\phi+1$ 得
$E_2=-\phi^{-2}$，递推式给 $E_{k+1}=-E_k/\phi$，所以第一式归纳成立。指数中的整数 $F_{k-1}$ 消去，得到第二式。又 $\phi^2>2$，故所述角度均在 $(-\pi,\pi)$ 内。

### 引理 3.3（一个复读数的两侧校准）

<a id="c132-lemma-scalar"></a>

对任意 $q\in\mathbb C$，全部不等式
$\Re(e^{i\theta_k}q)\le\Re q$ 等价于 $q\in\mathbb R_{\ge0}$。

**证明。**
写 $q=a+ib$，预算差为

<a id="c132-scalar-gap"></a>

$$
\Re q-\Re(e^{i\theta_k}q)
 =a(1-\cos\theta_k)+b\sin\theta_k.
\tag{10}
$$

在奇数子列，除以正的 $\sin\theta_k$ 得
$b\ge-a\tan(\theta_k/2)$，令 $k\to\infty$ 得 $b\ge0$。
在偶数子列，同理得 $b\le a\tan(|\theta_k|/2)$，故 $b\le0$。
于是 $b=0$；再取任一项，由 $1-\cos\theta_k>0$ 得 $a\ge0$。
反向直接使用 $\cos\theta_k\le1$。

这里没有先把读数规定成实数，也没有先给出非负范数。虚部不能留下，是因为一个非零侧向分量必在一侧微小回返中提高实读数；实部不能为负，是因为转开后反而会升高它。

### 引理 3.4（没有负系数原语的配方仍然稠密）

<a id="c132-lemma-density"></a>

$\{z^n:n\ge0\}$ 在单位圆稠密，$\mathcal S$ 在 $\mathbb C$ 稠密；因而对每一有限标签集，$\mathcal S^d$ 在 $\mathbb C^d$ 稠密。

**证明。**
$1/\phi$ 无理。鸽巢原理给出任意小的非零有向圆周位移
$q/\phi-\ell$，其中 $q>0,\ell\in\mathbb Z$。该位移的非负整数倍在绕满一圈之前，形成最大空隙不超过其绝对值的圆周网；这些点仍是 $z$ 的非负整数次幂，故轨道稠密。

$\overline{\mathcal S}$ 是加法封闭集且包含整个单位圆。任意模不超过 $2$ 的复数都可写成两个单位复数之和；再作有限次相加可得任意复数。因此 $\overline{\mathcal S}=\mathbb C$，有限直积的结论随之成立。

### 定理 3.5（C132 与全有限 Hermitian 正性完全等价）

<a id="c132-thm-equivalence"></a>

对于原始复核 $K$，条件 [(8)](#c132-axiom) 等价于：每一有限标签表
$G=(K(h_j,h_\ell))_{j,\ell=1}^d$ 都是 Hermitian 半正定矩阵。

**证明。**
由有限和定义，$B(f,z^{F_k}f)=z^{F_k}Q(f)$。引理 [3.3](#c132-lemma-scalar) 因此先给出 $Q(f)\in\mathbb R_{\ge0}$，对所有 $f\in\mathcal R$ 成立。
固定有限表 $G$。多项式 $c\mapsto c^*Gc$ 连续，且 $\mathbb R_{\ge0}$ 闭；引理 [3.4](#c132-lemma-density) 将结论延拓到所有 $c\in\mathbb C^d$。

实对角由 $c=e_j$ 得到。比较 $e_j+e_\ell$ 与 $e_j+i e_\ell$ 的二次读数，分别得到
$\Im(G_{j\ell}+G_{\ell j})=0$ 与
$\Re(G_{j\ell}-G_{\ell j})=0$，所以
$G_{\ell j}=\overline{G_{j\ell}}$。这才恢复 Hermitian 性；其二次型已非负，故 $G\ge0$。

反向，所有有限表正便使 $Q(f)\ge0$ 为实数，因而
$\Re B(f,z^{F_k}f)=Q(f)\cos\theta_k\le Q(f)$。

### 推论 3.6（严格失败总有有限见证）

<a id="c132-cor-finite-witness"></a>

若 $K$ 不满足全有限 Hermitian 正性，则存在一份有限的 $\mathcal S$ 配方与一个有限 $k\ge2$，使 [(8)](#c132-axiom) 严格反向。

**证明。**
先取有限表和复系数 $c$，使 $q=c^*Gc\notin\mathbb R_{\ge0}$。这样的 $c$ 必存在，否则前一定理中的逐项论证已经给出 Hermitian 正性。若 $\Im q\ne0$，取相反侧且足够小的回返角，式 [(10)](#c132-scalar-gap) 为负；若 $q<0$，任一回返角都使它为负。固定这个 $k$ 后，严格负值在系数的小邻域内保持。以 $\mathcal S^d$ 中的配方逼近 $c$ 即得见证。

这只是有限见证的存在定理，未给未知核的统一搜索步数。每个见证虽只含有限次加法和有限门幂，全部可能的 $k$ 仍无上界；当 $X$ 不可数时也不称全局检验族可数。

### 3.1 删去哪些承重部分会失败

**只取一侧。**只保留奇数 $k$，单标签核 $K=1+i$ 通过所有配方的检验；只保留偶数 $k$，$K=1-i$ 通过。因为对单标签 $Q(f)=|f|^2K$，相应的式 [(10)](#c132-scalar-gap) 两项均非负。两者都不是 Hermitian 核。

**只取有限个回返。**对非空有限菜单 $J\subset\{2,3,\dots\}$，令

$$
\tau_J=\min_{k\in J}\left|\tan\frac{\theta_k}{2}\right|>0.
$$

任取 $0<|b|<\tau_J$，单标签 $K=1+ib$ 对全部配方、全部 $k\in J$ 都通过，因为
$1-\cos\theta_k\ge |b\sin\theta_k|$。虚部仍然存在。该例明确区分了有限见证与有限菜单足够这两个命题。

**换成有限阶相位。**若生成元为 $m$ 阶本原单位根，$m\ge3$，则
$K=1+ib$、$0<|b|<\tan(\pi/m)$ 甚至通过全部整数次幂的比较，从而通过 Fibonacci 子族。对非零正弦，主值角的绝对值至少 $2\pi/m$，所以
$(1-\cos t)/|\sin t|\ge\tan(\pi/m)$；正弦为零的项也不造成失败。$m=2$ 只限制实部非负，$m=1$ 毫无限制。回返的精度与两侧性不可用有限相位周期代替。

**只检原子。**矩阵
$G=\left(\begin{smallmatrix}1&2\\2&1\end{smallmatrix}\right)$ 的两个原子自读都合格。但在配方 $(1,z^j)$ 上，$Q=2+4\Re z^j$；稠密性允许它为负。合格的单标签不能代替全部有限聚合。

### 3.2 精确推论与近似读数的区别

定理 [3.5](#c132-thm-equivalence) 已使 $Q(f)$ 为非负实数，故本轮候选还推出

<a id="c132-cor-full-orbit"></a>

$$
\Re B(f,z^n f)\le\Re Q(f)\qquad(n\ge0).
\tag{11}
$$

这是同一候选的全轨道推论。反向包含 Fibonacci 项，故精确情形等价。
但放宽读数后，两种族不能按相同误差互换。以下容差针对固定有限表中的单位系数配方；写成任意配方的形式时，容差为 $\varepsilon\|f\|_2^2$。若允许任意整数倍却给与尺度无关的绝对容差，缩放本身会将误差压到零，属于另一种要求。全轨道的标量容差恰为

$$
|q|-\Re q\le\varepsilon,\qquad
 q=a+ib\Longrightarrow
 a\ge-\varepsilon/2,\quad b^2\le2\varepsilon a+\varepsilon^2.
$$

这是单位圆稠密性给出的全轨道界，不是稀疏 Fibonacci 检验的误差界。

具体取 $q=i$。在全部 Fibonacci 项上，违规量为 $-\sin\theta_k<\sqrt3/2$：奇数项为负；偶数 $k\ge4$ 有 $|\theta_k|<\pi/3$，而 $k=2$ 可用补角化为小于 $\pi/3$ 的角。因此容差 $\sqrt3/2$ 使这些检验全部通过；全轨道违规量的上确界却为 $1$。误差分析必须重新使用实际采样角度，不能转抄 C131 的三向线性稳定界。

**白话。**只保留一个会不断转动的方向标。把同一份配方送去转动，在 Fibonacci 步数时，它会忽而从这一侧、忽而从另一侧，非常接近原方向。要求这些小回转都不能比原来的自身比较读得更高。若读数还藏着侧向成分，总有一侧会把它抬高；若它本身为负，稍微转开也会抬高。两种情况都被排除，留下的才是实在而非负的自比较。这与项目的黄金编码共用一个参照，但仍保留复数关系，并用无穷精细的回返承担校准；它不证明独立控制数目比上一轮更少。

<a id="section-4"></a>

## 4. 从回返校准重建比较空间与旧候选

<a id="c132-hilbert-reconstruction"></a>

全有限正核的 Hilbert 表示是经典结果 [8](#ref-aronszajn1950)。本节直接构造它，区分数学表示与物理可实现操作。

### 定理 4.1（固定核的零差商与最小表示）

<a id="c132-thm-hilbert"></a>

若 C132 成立，令 $\mathcal F=\mathbb C^{(X)}$，沿用有限和 $B$，并令
$\mathcal N=\{f:Q(f)=0\}$。则 $\mathcal N$ 是线性根空间，商空间具有内积。其完成 $\mathcal H$ 满足

$$
\iota(h)=[\delta_h],\qquad
 K(h,k)=\langle\iota(h),\iota(k)\rangle,\qquad
 \overline{\operatorname{span}\{\iota(h):h\in X\}}=\mathcal H.
$$

同一核的此种最小表示唯一到保持标签的酉等价。零核对应零空间，$\iota$ 不必单射。

**证明。**
有限和给出半双线性，定理 [3.5](#c132-thm-equivalence) 给出 Hermitian 正性。若 $Q(f)=0$，则对任意 $g,t$，
$Q(f+tg)=2\Re(tB(f,g))+|t|^2Q(g)\ge0$。
若 $B(f,g)\ne0$，选使交叉项为负的相位及足够小的 $|t|$ 即得矛盾。因此 $B(f,g)=0$，零集合正是线性根空间，商内积良定义。

完成给出所述表示。在两个最小表示间，将同系数的有限标签组合对应起来。两边范数均由同一张核表计算，故映射良定义且等距；由稠密性唯一延伸为满的酉映射。

对 $Q(g)>0$，将 $t=-\overline{B(f,g)}/Q(g)$ 代入 $Q(f+tg)\ge0$，得到 Cauchy–Schwarz 不等式；$Q(g)=0$ 已由根空间论证处理。于是

$$
|B(f,g)|^2\le Q(f)Q(g),\qquad
 d(f,g)=\sqrt{Q(f-g)}
$$

是形式配方上的伪距离，在零差商上满足三角不等式。它保留向量尺度；$f$ 与 $e^{it}f$ 可能代表同一物理射线，但该距离通常非零。

### 4.1 极化、三向校准与独立二元预算

一般互读可由四项自读恢复，第一槽取共轭的约定给出

<a id="c132-polarization"></a>

$$
B(f,g)=\frac14\bigl[
 Q(f+g)-Q(f-g)-iQ(f+ig)+iQ(f-ig)\bigr].
\tag{12}
$$

展开前两个自读，其差为 $2(B(f,g)+B(g,f))$；后两个之差为
$2i(B(f,g)-B(g,f))$，故公式成立。

对任意 Gaussian 整数配方，C131 的三读现在自动成为
$\Re Q(f)=Q(f)\ge0$、$\Re(iQ(f))=\Re(-iQ(f))=0$。
反向，三读合格先使这些配方的 $Q$ 实且非负；清分母得到有理复系数，再逐有限表用连续性扩到 $\mathbb C$，恢复正核与 C132。因此三向校准被恢复为同一类核的另一种测试，不是在黄金算术中额外发现了三个独立物理方向。

C130 的全部独立二元预算也成为

<a id="c132-recovers-c130"></a>

$$
\Re Q(f)+\Re Q(g)-2\Re B(f,g)=Q(f-g)\ge0.
\tag{13}
$$

反向若只给 C130 的整数配方约束，取 $g=0$ 得 $a=\Re Q(f)\ge0$；再取配方对 $(nf,(n+i)f)$，预算差为 $a+2nb$，其中 $b=\Im Q(f)$。全部 $n\in\mathbb Z$ 使 $b=0$，再次由清分母与连续性回到正核。不同候选的等价依赖其各自完整量词，不能只截取几个原子读数。

### 4.2 奇异旧表、新余量与相反微移

### 命题 4.2（恢复 C129 的块式接续）

<a id="c132-prop-schur"></a>

在旧有限表 $G$ 后追加一个标签。正性等价于

<a id="c132-schur"></a>

$$
G\ge0,\quad b\in\operatorname{Ran} G,\quad q-b^*G^+b\in\mathbb R_{\ge0},
 \qquad
 \begin{pmatrix}G&b\\b^*&q\end{pmatrix}
 =\begin{pmatrix}G&Gc\\c^*G&c^*Gc+|r|^2\end{pmatrix}
\tag{14}
$$

中某组 $c,r$ 的存在；$G^+$ 是 Moore–Penrose 伪逆。

**证明。**
若 $u\in\operatorname{ker} G$，它在整个正表中的零自读迫使 $u^*b=0$，故 $b\in\operatorname{Ran} G$。此时取 $c=G^+b$，在组合 $(-c,1)$ 上求值，得到
$s=q-b^*G^+b\ge0$。取 $|r|^2=s$ 即得块式。

反向该块式在任意 $(v,t)$ 上的二次型为
$(v+ct)^*G(v+ct)+|r|^2|t|^2\ge0$。
从空表递归接续，便恢复全部有限正性，因此也恢复 C132。

若 $G=0$，像空间条件先强制 $b=0$。只看 $q-b^*G^+b$ 会漏检，例如
$\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$ 的形式余量为 $1$，矩阵却非正。回返校准把零边界一并保留，并没有用伪逆约定替代它。

在构造空间中还直接得到 C128：

<a id="c132-recovers-c128"></a>

$$
Q(a+tv)+Q(a-tv)-2Q(a)=2|t|^2Q(v)\ge0.
\tag{15}
$$

因此原来的局部微移余量、递归追加余量、二元互读预算与三向自校准，均可在本轮所选的同一正核中重新计算。

以上零差始终是*当前固定核中的向量零差*。换一个读口、更新核，或给程序换输入，未必保留它。形式线性包络也未自动成为可制备态集合；复内积表示还没有自行提供概率归一、复合系统、可实施过程或动力学。尤其 $z^nf$ 与 $f$ 的孤立射线相同，读出交叉实部需要共同相位参考或受控相对相位，不能解释成测到了全局相位。

**白话。**原方向校准后，所有配方的比较可以放进同一个正空间。把在这张固定关系表中处处读不出差别的组合合并，就得到内积空间；增加一个对象时，它自然分成旧空间里的影子和新余量。这说明前几轮的几种写法可以互相还原。黄金回返提供了一种与已有黄金编码共用参照的校准方式，概率、实验控制和物理时间仍须由各自的关系接口接进来。

<a id="section-5"></a>

## 5. 支持圆、三片窗口与三元关系

<a id="sec-c132-geometry"></a>

### 5.1 同一读数为何必须位于圆的最右端

对固定配方写 $Q(f)=p+iy$。Fibonacci 回返相位为 $z^{F_k}=e^{it_k}$，其中 $t_k=-2\pi\psi^k$ 从两侧趋近 $0$。唯一候选要求

<a id="eq-c132-support-reading"></a>

$$
\Re(e^{it_k}Q(f))\le p,
 \qquad
 p(1-\cos t_k)+y\sin t_k\ge0.
\tag{16}
$$

几何上，$e^{it}Q(f)$ 沿以原点为圆心的圆移动。若当前点不在实轴，某一侧的足够小转动必提高实读，黄金回返会访问该侧；负实端点也会被非零小转动提高。因此合法非零读数只能是圆的最右端，竖线 $\Re w=p$ 在那里相切。零读数对应退化为一点的圆。这是前文正核等价定理的支持几何，不是另一条条件。

<a id="fig-c132-carry-and-return"></a>

```latex
\begin{tikzpicture}[font=\small,>=Latex]
 \path[use as bounding box] (-0.25,-0.30) rectangle (12.00,4.35);
 \pgfmathsetmacro{\goldalpha}{(sqrt(5)-1)/2}
 \node at (2.10,4.08) {进位 $\delta$ 的三个区域};
 \begin{scope}[xshift=0.75cm,yshift=0.85cm,x=2.55cm,y=2.55cm]
  \fill[teal!13] (0,0)--(\goldalpha,0)--(0,\goldalpha)--cycle;
  \fill[blue!5] (\goldalpha,0)--(1,0)--(1,\goldalpha)--(\goldalpha,1)--(0,1)--(0,\goldalpha)--cycle;
  \fill[orange!17] (1,1)--(1,\goldalpha)--(\goldalpha,1)--cycle;
  \draw[black!50] (0,0) rectangle (1,1);
  \draw[black!60,dashed] (\goldalpha,0)--(0,\goldalpha);
  \draw[black!60,dashed] (1,\goldalpha)--(\goldalpha,1);
  \draw[black!45,->] (-0.04,0)--(1.15,0) node[below right] {$\tau(a)$};
  \draw[black!45,->] (0,-0.04)--(0,1.15);
  \node[left] at (-0.05,1.08) {$\tau(b)$};
  \node[below left] at (0,0) {$0$};
  \node[below] at (\goldalpha,0) {$\alpha$};
  \node[below] at (1,0) {$1$};
  \node[left] at (0,\goldalpha) {$\alpha$};
  \node[left] at (0,1) {$1$};
  \node[teal!70!black] at (0.20,0.20) {$+1$};
  \node at (0.50,0.50) {$0$};
  \node[orange!80!black] at (0.88,0.88) {$-1$};
 \end{scope}
 \node[font=\footnotesize] at (2.10,0.18)
  {分界：$\tau(a)+\tau(b)=\alpha,\ 1+\alpha$};

 \node at (8.55,4.08) {黄金回返从两侧接近自身};
 \begin{scope}[xshift=8.35cm,yshift=2.03cm,x=1.20cm,y=1.20cm]
  \draw[black!35,->] (-1.30,0)--(1.47,0) node[below right] {$\Re$};
  \draw[black!35,->] (0,-1.25)--(0,1.22) node[above right] {$\Im$};
  \draw[teal!65!black,thick] (0,0) circle[radius=1.20cm];
  \draw[black!55,dashed] (1,-1.20)--(1,1.35);
  \node[right,font=\footnotesize] at (1.06,1.01) {$\Re w=1$};
  \foreach \kk/\sgn/\col in {2/-1/orange,3/1/blue,4/-1/orange,5/1/blue,6/-1/orange,7/1/blue,8/-1/orange}{
   \pgfmathsetmacro{\returnangle}{360*\sgn*\goldalpha^\kk}
   \fill[\col!75!black] ({cos(\returnangle)},{sin(\returnangle)}) circle (1.7pt);
  }
  \node[below left,font=\footnotesize,orange!75!black] at (-0.76,-0.69) {$\chi(F_2)$};
  \node[above left,font=\footnotesize,blue!75!black] at (0.08,1.02) {$\chi(F_3)$};
  \node[below right,font=\footnotesize,orange!75!black] at (0.64,-0.83) {$\chi(F_4)$};
  \node[font=\footnotesize,blue!75!black] at (0.43,0.36) {$\chi(F_5)$};
  \fill (1,0) circle (1.8pt);
  \node[below right] at (1.03,0.02) {$1$};
 \end{scope}
 \node[font=\footnotesize] at (8.55,0.18)
  {$t_k=-2\pi\psi^k\longrightarrow0^{\pm}$};
\end{tikzpicture}
```

**图 1。**左图是式~[(5)](#eq-c132-carry-bands) 的精确分区，实际整数轨道避开虚线边界。右图按精确角度绘出 $k=2,\ldots,8$ 的回返点：奇位蓝、偶位橙；以合法自读 $Q=1$ 归一，支持线在自身处相切。图中圆是一个复读数的相位轨道。

### 5.2 算术提升：三个实坐标组成三片窗口

把二元加法提升为 $(u,v,w)=(e(a),e(b),e(a+b))$。由整数补偿式，三点数据位于

<a id="eq-c132-arithmetic-three-planes"></a>

$$
w=u+v-j,\qquad j\in\{-1,0,1\},\qquad
 (u,v,w)\in\widetilde I^{\,3}.
\tag{17}
$$

这是在一个单位宽立方窗内截出的三张平行平面片。越界只改变所选片；在图左的 $\tau=\alpha-e$ 坐标中，同一关系为
$\tau(a+b)=\tau(a)+\tau(b)-\alpha+\delta(a,b)$。

把窗口端点按整数平移识别，令 $\mathbb T=\mathbb R/\mathbb Z$，三片拼成

$$
\mathcal C=\{(u,v,w)\in\mathbb T^3:w=u+v\}
 =\{(u,v,u+v):u,v\in\mathbb T\}\cong\mathbb T^2.
$$

前两个坐标给逆映射，所以这是圆加法的二维环面图。算术轨道在该图中稠密，但其闭合并不使离散窗口的整数截面变成连续全局截面。

### 5.3 关系的关系：三元 Gram 表限制环相位

正核恢复后，任选三条历史的代表 $u_1,u_2,u_3$，令 $q_j=\|u_j\|^2$、$K_{ij}=\langle u_i,u_j\rangle $。它们的 Gram 实现至多需要三个复维度；这与上一节的三个实坐标是两种不同提升。

### 命题 5.1（三元兼容约束）

三元比较表 $G=[K_{ij}]\succeq0$ 满足

<a id="eq-c132-three-gram"></a>

$$
\begin{aligned}
 \det G={}&q_1q_2q_3+2\Re(K_{12}K_{23}K_{31})\\
 &-q_1|K_{23}|^2-q_2|K_{31}|^2-q_3|K_{12}|^2\ge0.
 \end{aligned}
\tag{18}
$$

环积 $\mathcal B=K_{12}K_{23}K_{31}$ 在三条历史分别重相位时不变。若 $\mathcal B\ne0$，其相位受到式~[(18)](#eq-c132-three-gram) 的约束，并不必为零。

**证明。**
Hermitian 行列式展开即得公式，非负性来自正核。重相位 $u_j\mapsto e^{i\theta_j}u_j$ 使每条边乘 $e^{i(\theta_j-\theta_i)}$，沿三元环相乘时三个因子抵消。环积为零时不定义其相位。

例如在 $\mathbb C^2$ 中取

$$
u_1=\lvert 0\rangle ,\qquad
 u_2=\frac{\lvert 0\rangle +\lvert 1\rangle }{\sqrt2},\qquad
 u_3=\frac{\lvert 0\rangle +i\lvert 1\rangle }{\sqrt2}.
$$

各 $q_j=1$，三条边的模平方均为 $1/2$，而
$\mathcal B=(1+i)/4$，其相位为 $\pi/4$。式~[(18)](#eq-c132-three-gram) 取等，Gram 秩为 $2$。它满足同一 C132 候选，却已有非零环相位。整数历史上 $\delta$ 为余边界，不能用来消除此类正核关系中的环相位。

### 5.4 二元正关系的三维球截面

对两条历史的比较表，写 $p=\|u\|^2$、$q=\|v\|^2$、$\langle u,v\rangle =x+iy$，并令 $T=(p+q)/2$、$D=(p-q)/2$。二阶正性精确等价于

<a id="eq-c132-lorentz-cone"></a>

$$
G=\begin{pmatrix}T+D&x+iy\\x-iy&T-D\end{pmatrix}\succeq0
 \quad\Longleftrightarrow\quad
 T\ge\sqrt{D^2+x^2+y^2}.
\tag{19}
$$

其证明可直接用本征值 $T\pm\sqrt{D^2+x^2+y^2}$。这是二阶正表的 Lorentz 锥表示 [12](#ref-arrighi2002)。若 $T>0$，除以迹 $2T$，得到球坐标
$\mathbf r=(x/T,-y/T,D/T)$、$\|\mathbf r\|\le1$。球面为秩一，内部为秩二；$T=0$ 则整表为零，是不能归一的原锥顶。

对单位二分量向量 $(\xi,\eta)$，秩一投影的三个坐标为

$$
\mathbf r=\bigl(2\Re(\bar\xi\eta),\,2\Im(\bar\xi\eta),\,
 |\xi|^2-|\eta|^2\bigr),\qquad \|\mathbf r\|=1.
$$

它们固定两模及 $\bar\xi\eta$：一个非零分量的相位定下后，另一个也确定；两极只剩单个分量的相位。取 $\xi=\cos(\theta/2)$、$\eta=e^{i\gamma}\sin(\theta/2)$ 可遍历整个单位球面，故映射满射。
公共相位圆恰是纤维；紧空间到 Hausdorff 球面的连续双射给 $S^3/U(1)\cong S^2$ 的 Hopf 结构 [11](#ref-mosseri2001)。允许正凸混合时得到整只 Bloch 球；实际态与效果仍由原读出接口解释。
这里描述的是全部二阶正表的几何，不表示任取两条实际历史就已供应整只球中的可制备态。

算术的三片窗口记录整数加法如何跨界，环面记录圆加法；正核的三元表记录边与边之间的相位兼容，球面则记录二分量纯态的射线。它们在本轮通过同一相位探针联系，但没有被证明是同一个几何对象，更没有由这些坐标推出物理时空。

**白话。**黄金算术给一只会自己回来的相位钟：一直向前取幂，却交替从两边接近起点。若自比较还歪向圆的一侧，总有一次很小的回返会把实读提高；自身始终最高，才把读数锁到正实方向。再把三条历史放在一起，三条边就不能随意拼，相位绕一圈留下的量也要共同满足正表。那种环相位可以非零，不能因为整数进位能重新记账，就把它一并抹掉。

<a id="section-6"></a>

## 6. 从黄金回返约束恢复有限量子规则

<a id="sec-c132-quantum"></a>

黄金回返约束先恢复正核与比较空间。要接回原过程，须使用它实际对应的乘法、复线性、记录与联合接口；自由表的任意正完成不能替代这些关系。这里选择全复矩阵代数，是另一个明确的结构前件，不由 C132 单独产生。以下给一套有限复矩阵理论的条件性闭合，标准表示与概率定理有成熟来源 [9](#ref-watrous2018)、[10](#ref-busch2003)。

### 6.1 一张有限来源表选择完全正过程

### 定义 6.1（事件的原始核）

取 $d,m\ge1$。对仅给复线性的 $\Phi:M_d(\mathbb C)\to M_m(\mathbb C)$，以 $(a,u)\in M_d\times\mathbb C^m$ 为原始历史标签，定义

$$
K_\Phi((a,u),(b,v))=\langle u,\Phi(a^*b)v\rangle.
$$

不预设 $\Phi$ 保伴随、正、完全正或归一化。

### 定理 6.2（有限来源表的黄金回返约束与 CP）

<a id="thm-c132-cp"></a>

固定一来源行 $1\le p\le d$。以下等价：

1. 核 $K_\Phi$ 满足 C132；

2. 对有限列表 $((E_{pi},e_\mu))_{i,\mu}$，其每个 $\mathbb N[z]$ 有限配方均通过全部 $F_k$ 回返比较（$k\ge2$）；

3. $\Phi$ 完全正。

成立后 $\Phi$ 自动保伴随，且存在 $d\times m$ 矩阵 $A_\alpha$，使

$$
\Phi(x)=\sum_\alpha A_\alpha^*xA_\alpha.
$$

**证明。**
该列表的比较表第 $((i,\mu),(j,\nu))$ 项为
$\langle e_\mu,\Phi(E_{ij})e_\nu\rangle$，即 Choi 表 $C_\Phi=[\Phi(E_{ij})]$。
由黄金回返约束与正核的等价，(2) 恰要求 $C_\Phi\succeq0$。
将其分解为 $\sum_\alpha w_\alpha w_\alpha^*$，写
$w_\alpha=\sum_i e_i\otimes A_\alpha^*e_i$，比较各块即得 Kraus 式；它的每一级矩阵放大都将正矩阵送到正矩阵，所以给 (3)。
CP 反向作用于任意正块表 $[a_i^*a_j]$，再用向量族评价，得到

$$
\sum_{ij}\bar z_i K_\Phi((a_i,u_i),(a_j,u_j))z_j\ge0.
$$

于是全核正，本轮正核等价定理给 (1)；(1) 显然给 (2)。

在核商空间上令 $\pi(x)[a,u]=[xa,u]$。它保零差，因为
$\langle\pi(x)h,k\rangle=\langle h,\pi(x^*)k\rangle$。
取 $b=(\|x\|^2I-x^*x)^{1/2}$，有
$\|x\|^2Q(h)-Q(\pi(x)h)=Q(\pi(b)h)\ge0$，故有界。
核公式也保证 $Vu=[I,u]$ 对 $u$ 线性，直接得到

$$
\Phi(x)=V^*\pi(x)V.
$$

这里 $V$ 不必等距；单位效果未归一时不能补出等距结论。零映射使用零比较空间及空 Kraus 和，也满足本轮候选。

### 6.2 完整记录、Born 与读后态

### 命题 6.3（原记录的归一化）

若有限原事件族 $\{\Phi_j:M_{d_j}\to M_m\}_{j\in J}$ 各满足候选，并另有完整记录约束 $\sum_j\Phi_j(I)=I$，则态方向过程

$$
\mathcal T_j(\rho)=\sum_\alpha A_{j\alpha}\rho A_{j\alpha}^*,
 \qquad \sum_{j,\alpha}A_{j\alpha}^*A_{j\alpha}=I
$$

构成完整 CP 仪器。各支迹不增；带标签的总输出位于 $\bigoplus_{j\in J}M_{d_j}$，并且保迹。

**证明。**
令 $E_j=\Phi_j(I)=\sum_\alpha A_{j\alpha}^*A_{j\alpha}\ge0$，则
$I-E_j=\sum_{k\ne j}E_k\ge0$。迹循环给 $\operatorname{Tr}\mathcal T_j(\rho)=\operatorname{Tr}(\rho E_j)$，即得支迹界与总保迹。

概率本身需要一致的效果评价。对全部 $0\le E\le I$ 给 $p(E)\ge0$，满足 $p(I)=1$，且 $E+F\le I$ 时 $p(E+F)=p(E)+p(F)$；同一效果在不同完整测试中赋同值。

### 定理 6.4（效果评价与纯态）

该评价唯一为 $p(E)=\operatorname{Tr}(\rho E)$，其中 $\rho\ge0,\operatorname{Tr}\rho=1$。
密度态的极点恰是秩一态；对归一纯态与秩一投影有 $p=|\langle\phi,\psi\rangle|^2$。

**证明。**
可加性给有理齐次性，非负性给单调性，有理夹逼给实齐次性。对 $B\ge0$，以 $s>0,s\ge\|B\|$ 定义 $f(B)=s\,p(B/s)$，它与 $s$ 无关且在正锥可加。由正负分解延伸为 Hermitian 空间上的实线性泛函；有限迹配对给唯一 Hermitian $\rho$，正性与归一分别给 $\rho\ge0$ 和迹一。
秩至少二时可反向微调两个正谱权，得非平凡凸分解；秩一态的正分解只能支持同一射线，故它是极点。对两个秩一矩阵直接相乘取迹，即得 Born 平方律。相同纯态的归一向量只差整体相位。

该全效果版本包括二维 [10](#ref-busch2003)。候选未自动供应全部物理效果。
原支有 $p_j=\operatorname{Tr}(\rho E_j)$；仅当 $p_j>0$ 时定义 $\rho_j=\mathcal T_j(\rho)/p_j$。
若同空间支效果为投影 $P$，且保持 $\operatorname{Ran} P$ 内每条纯射线，则得到 Lüders 更新：$P=0$ 时所有 Kraus 项为零；$P\ne0$ 时效果先给 $A_\alpha(I-P)=0$，射线保持使每个 $A_\alpha v$ 与 $v$ 共线。对基向量及两两和应用，得 $A_\alpha=c_\alpha P$。效果给 $\sum|c_\alpha|^2=1$，故 $\mathcal T(\rho)=P\rho P$。仅有结果可重复性不排除结果子空间内的旋转。

### 6.3 可观测量、不确定界与独立复合

有限锐测量由正交投影 $\sum_iP_i=I$ 和实结果 $a_i$ 给自伴算符 $A=\sum_i a_iP_i$，反向由有限谱分解得到。其期望为 $\operatorname{Tr}(\rho A)$。
对自伴 $A,B$ 中心化为 $A_0,B_0$，在算符历史上用
$\Gamma_\rho(X,Y)=\operatorname{Tr}(\rho X^*Y)$。二元 Gram 行列式非负给

$$
\operatorname{Var}_\rho(A)\operatorname{Var}_\rho(B)
 \ge |\operatorname{Tr}(\rho A_0B_0)|^2
 \ge\tfrac14|\operatorname{Tr}(\rho[A,B])|^2.
$$

第二步保留复数的虚部。具体位置、动量及交换常数并非黄金回返约束选出；无限维无界算符还需定义域等独立条件。

若 $M_d,M_m$ 保单位保星地嵌入同一非零联合代数，两像交换并共同生成，则
$a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 是满的保单位星同态。定义域 $M_d\otimes M_m\cong M_{dm}$ 简单：非零理想经矩阵单位左右相乘即含全部矩阵单位。故核为零，给张量联合。
CP 串接与并接的 Kraus 族分别为 $B_\beta A_\alpha$ 与 $A_\alpha\otimes B_\beta$。完整局部保迹过程不改变另一侧边缘，因为其伴随把 $I\otimes E$ 送回 $I\otimes E$。条件于特定结果时，边缘可变，所选标签的信息不能丢去。

### 6.4 可逆、时间及物理接口

### 命题 6.5（同维可逆过程与时间群）

同维 CPTP 过程若有 CPTP 左逆，则为酉共轭。若再给连续一参数 CPTP 群，则存在自伴 $H$，使

$$
\mathcal T_t(\rho)=e^{-itH/\hbar}\rho e^{itH/\hbar},
 \qquad i\hbar\dot\rho=[H,\rho].
$$

**证明。**
两过程的 Kraus 族记为 $A_i,B_j$。恒等通道 Choi 秩一给 $B_jA_i=c_{ji}I$。
对一个非零 $A_i$，逆过程保迹保证至少一个乘积非零；同维使相应 $B_j$ 可逆，从而所有 $A_i$ 共线。合并成一个 $A$ 后，保迹给 $A^*A=I$，方阵即酉。
有限维连续群写为 $e^{t\mathcal L}$；酉共轭性使生成元为保星导子。取 $D=\sum_k\mathcal L(E_{k1})E_{1k}$，导子律给 $[D,E_{ij}]=\mathcal L(E_{ij})$；保星性使 $D+D^*$ 为中心。换成反自伴部分并写成 $-iH/\hbar$，得到公式。

选定纯态相位代表后有 $i\hbar\dot\psi=H\psi$。具体钟、生成元与 $\hbar$ 标定并非原始核给出的事实。内积、正过程、完整概率、独立联合与时间的来源必须逐层对应。

| 通常规则 | 本轮推导与保留条件 |
|---|---|
| Hilbert 与叠加 | 正核的自由复包络及零差商；实际叠加仍须原控制接口。 |
| CP 与过程表示 | 指定复线性矩阵事件的来源核；有限 Choi 表上的全部黄金配方与回返比较。 |
| 概率与仪器 | 全效果一致可加评价；原完整记录归一化。 |
| 测量更新 | 已给 CP 仪器；逐射线保持时才选出 Lüders。 |
| 复合与局部性 | 交换且共同生成的独立子代数；完整局部保迹。 |
| 酉与时间 | 同维 CPTP 左逆；连续群和另行标定的物理时钟。 |

**白话。**同源历史的每个斐波那契回返实读都不超过自读，先选择正比较表；接上原过程的乘法与复线性，就选择完全正过程。完整记录给归一化，一致的效果赋值给 Born 规则，独立联合和可逆时间再给张量与酉演化。每一步都来自具体内部关系；公式更短，并没有免除这些关系实际存在的要求。

<a id="section-7"></a>

## 7. 把约束放回历史、观察者与原过程

<a id="sec-c132-internal"></a>

### 7.1 哪些关系已经内生，哪一条仍待供应

本轮可以严格区分三层。第一层是 Zeckendorf 定义自身的算术定理：
自然值沿进位保持，$\delta=\partial\beta=\partial\kappa$，
$\chi(a+b)=\chi(a)\chi(b)$，以及斐波那契回返公式。
这些不是额外的量子公理。第二层是本稿明确选择的读数语义：
复值二元表、同一个共轭线性合计、有限形式叠加、实数次序。
第三层是 C132 要求这个读数与回返操作相容。

第二、三层不能由第一层自动推出。保持全部黄金算术，另取单标签
$K(h,h)=1+i$，仍得到一个完全一致的算术对象，却违反 C132。
因此，若把 $\Omega$ 定义为满足全部已指定关系的整体，
当然可以把 C132 也列为关系；但这只是定义了一类允许模型，
不是从旧定义证明实际读数一定属于这一类。
真正的进一步内生化，是从已有控制、相干比较和记录恒等式证明 C132，
或找出这些原关系不能满足 C132 的有限反证。

项目最新 C117 正生成路线保留了同样的区分：实际控制的矩阵关系，
不能自动替未知响应函数承担全上下文的等式；完整原记录和合法后缀不能删去。
它的原子控制满足 $K_j^{10}=I$，而本稿 $z$ 是无限阶相位。
本稿没有证明原七地址语法实际供应这个相位参照或其相干合计接口
 [6](#ref-repo-c117)。
数学闭包中的极限同样不能自行变成可调用的门。

### 7.2 有限的零差证书

### 定理 7.1（关系成为不随正延拓改变的定义约束）

在 C132 所确定的正核上，任意有限复配方
$r=\sum_jc_j\delta_{h_j}$ 满足

$$
Q(r)=0
 \quad\Longleftrightarrow\quad
 \sum_jc_j\iota(h_j)=0
 \quad\Longleftrightarrow\quad
 \sum_jc_jK(k,h_j)=0\quad\hbox{对全部 }k\in X.
$$

若一个更大的正核保留旧表的所有条目，则该零差对全部新标签也为零。

**证明。**
第一等价是零差商的定义。正核的 Cauchy–Schwarz 给
$|B(k,r)|^2\le Q(k)Q(r)$，故零量使所有二元对照消失。
反向把所有 $B(h_j,r)=0$ 按 $\overline{c_j}$ 合计便有 $Q(r)=0$。
正延拓保留 $Q(r)$，再用同一不等式即得新标签结论。

所以，若历史 $h_3$ 被定义为 $\alpha h_1+\beta h_2$，
其兼容关系可写成
$Q(\delta_{h_3}-\alpha\delta_{h_1}-\beta\delta_{h_2})=0$。
这把一条已供应的定义关系锁进所有未来正延拓；
它没有制造原来不存在的历史组合操作。
若只有 $Q(r)\le\varepsilon$，则
$|B(k,r)|\le\sqrt{Q(k)\varepsilon}$，
需要控制测试历史的尺度，才能得到统一误差界。

还必须区分*旧读口看不出差别*与*同一完整表中的零差*。
令 $v_a=e_1,v_b=e_1+e_2$。先投影到 $e_1$，再开放全空间，得到

$$
G_{\rm old}=\begin{pmatrix}1&1\\1&1\end{pmatrix},
 \qquad
 G_{\rm new}=\begin{pmatrix}1&1\\1&2\end{pmatrix}.
$$

两表都满足候选，但前者把 $b-a$ 看成零，后者不把它看成零。
原因是旧的 $bb$ 条目变了；它不满足定理中的保旧表延拓前件。

类似地，固定来源上的输出等价不自动成为门的等价。
在 $|0\rangle$ 上 $I$ 与 $Z$ 输出相同；把来源换为 $H|0\rangle=|+\rangle$ 后，
$I$ 与 $Z$ 分别输出 $|+\rangle$ 与 $|-\rangle$。
“内容等于地址”的程序编码，需要保留在哪个来源、哪些后续上下文中成立的合同。

### 7.3 不调用全知观察者的兼容拼接

### 定理 7.2（已给有限窗口的有向拼接）

设 $I$ 为非空有向偏序集，$X_\alpha\subseteq X_\beta$ 当 $\alpha\le\beta$，
每个 $K_\alpha$ 满足 C132，并且较大窗口在较小窗口上的限制等于原表。
则 $X=\bigcup_\alpha X_\alpha$ 上存在唯一保留全部这些条目的核 $K$；
它满足 C132，且其最小 Hilbert 表示是各局部表示的等距有向极限再完备化。

**证明。**
任意有限标签族同处一个上界窗口；不同窗口中的条目在共同上界相同，
故 $K$ 定义良好且唯一。任意有限配方及其回返比较也同处一个窗口，
因而候选在并集成立。保旧表使局部零差与内积保持，给等距嵌入；
它们的并集在全局最小表示中稠密，完成构造。

这一定理的输入是实际取得的兼容关系，不要求某个观察者已经知道整个并集。
如果两个观察者各自只知 $K(a,a)=K(b,b)=1$，
则

$$
G_c=\begin{pmatrix}1&c\\\overline c&1\end{pmatrix},
 \qquad |c|\le1,
$$

全部符合自己的记录。$c=0$ 时两条重建射线正交，$c=1$ 时重合。
因此现有局部表不能确定交叉关系。新的共同读数可以缩小可能集合；
这一反例不证明“永远无法知道”，也不证明必须包含另一观察者的全部结构。
这里讨论的是重建空间的交集，不是两个标签集合的字面集合交集。

仅有两两窗口的一致性也不足以保证有向共同窗口。
例如 $2I_3-J_3$ 的每个二阶主块都是正半定，
但全一向量的自读为 $-3$，整表无法进入候选。
三元检验揭示这个反例，却不能代替任意更大有限表的检验。
更一般地，给定 $r\ge1$，取 $(r+1)$ 阶表 $G=(2r+1)I_{r+1}-2J_{r+1}$。
每个 $m\le r$ 阶主块的最小特征值至少为 $2r+1-2m\ge1$，
整表在全一方向的特征值却是 $-1$。所以固定大小的提升只能展示某一层关系，不能替代任意有限相容性。

### 命题 7.3（观察者的逼近对象）

在已固定的共同表示中，若观察者可见的闭子空间
$H_1\subseteq H_2\subseteq\cdots$ 的正交投影为 $P_n$，则对任意 $v$

$$
\|v-P_nv\|^2-\|v-P_{n+1}v\|^2
 =\|(P_{n+1}-P_n)v\|^2\ge0.
$$

并有 $P_nv\to P_\infty v$，
其中 $P_\infty$ 投影到 $\overline{\bigcup_nH_n}$。

**证明。**
嵌套性给正交分解
$v-P_nv=(v-P_{n+1}v)+(P_{n+1}-P_n)v$，得到恒等式。
同理，$\|P_nv\|^2$ 递增且有界，使 $P_nv$ 为 Cauchy；
极限在闭并集内，误差与其稠密子集正交，故为正交投影。

这是“可读关系逐步逼近”的严格版本。若要逼近整个目标，还需
$v\in\overline{\bigcup_nH_n}$。任意门序列不会自动满足这个条件。
$\Omega_{\rm rel}=(X,K,\hbox{已供应的关系})$ 是一个关系结构；
它不自动是一条归一量子态，也不由 C132 唯一选出。

### 7.4 向前的日志与左右的回返

把 $a,b$ 的两份规范数字相加，并沿完整合法路径归一到 $a+b$ 的规范数字。
在这样的路径上设正边界事件数为 $N_+$，负边界事件数为 $N_-$，
其余进位事件数为 $N_0$，则

$$
\delta=N_+-N_-,
 \qquad L=N_++N_-+N_0\ge|\delta|.
$$

负的净差额完全可以出现在增长的事件记录中。
$\delta$ 是端点决定的有符号净值，$L$ 是具体路径的事件数；
两者不是同一个“量”。实际归一化终止量又是源码另给的字典序指标
 [4](#ref-repo-carry)。

C132 的回返同样只取正步数 $F_j$，所以没有倒放控制字。
然而相位误差
$2\pi(-1)^{j-1}\phi^{-j}$ 交替变号。
向前积累的步骤与左右交替的比较方向因此可共存。
这解释了用户所说的画面，并没有推出绝对的空间手性或物理时间箭头。
共轭整个正核仍为正核；换向整个相位约定不改变等价定理。

若“日志只增”指保留每次事件的前缀档案，它是可明确给出的记录协议。
它不是所有封闭系统每个局部寄存器熵都递增的定理。
例如同一 CNOT 先把计算基值写到辅助位，再执行一次就能把辅助位复原；
整体演化可逆，局部记录会被清除。要把旧记录永久可访问，必须说明存在哪个寄存器和哪个读口。
项目 C117 也明确区分保留程序索引与实际可查询档案  [6](#ref-repo-c117)。

同理，不存在把所有不同输入送到同一输出的酉门：
$Uu=Uv$ 会由 $U$ 的单射性推出 $u=v$。
允许环境承接区别时，对 $\|r\|=1$ 可以有 $u\mapsto r\otimes u$ 这样的等距重置结构；
信息去向仍须计入完整系统，不能凭自指命名省去。

**白话。**进位表告诉我们哪些变化只是换了写法，哪些净差额必须记账；
回返表告诉我们同一份历史怎样从两侧重新对齐。
观察者每次只用已经拿到的比较和记录，把能对上的部分接起来。
不知道交叉读数，就保留未知；取得共同读数后再缩小可能。
新增视野可以揭开以前看不见的区别，因此“当时读不出”不能直接写成“永远相同”。

<a id="section-8"></a>

## 8. 本轮完成的回溯与完整白话

### 8.1 候选、完成范围与剩余关系

本轮唯一候选是

$$
\operatorname{Re}B(f,z^{F_j}f)\le\operatorname{Re}B(f,f),
 \qquad f\in\mathbb N[z]^{(X)},\ j\ge2,\quad
 z=e^{2\pi i/\phi}.
$$

它把显式直角校准接到项目既有的黄金算术与两侧回返；进位守恒没有被另加为公理。
但 C131 的三个方向本来也由单一 $i$ 生成，且 $\mathbb N[i]=\mathbb Z[i]$。
所以本轮完成的是统一关系的等价重写，没有证明独立前提或实验资源严格减少。
只有原过程已经供应黄金相位时，才无需另给精确直角参照；当前尚未证明这项供应。

C132 已恢复正核、零差商、Hilbert 表示与二元、三元几何。
全复矩阵接口、完整记录、效果可加评价、独立复合和连续可逆时间等原关系接齐时，
第六节给出 CP、Born、更新、张量和酉演化的条件性闭合。
零核、一维核与只开放交换可观测量的子理论仍与数学核心相容；
场的局域性、规范群、粒子谱与常数尚未从这里导出。

下一步的证明对象已经明确：在同一指定来源中实现 $B$、黄金相位及合法有限配方，
保持原记录、失败质量和所有合法上下文。
把这个关系实际证明出来，才是继续减少外部输入；数学闭包本身不供应操作。

### 8.2 一段完整白话

把向前计步的自然数写成不相邻的斐波那契筹码。两个步数相加重新进位时，
真正的步数没有变，但黄金读法会在最下面两层留下正一、零或负一的净差额。
这个差额是记账：把整圈忽略后，先合起来再走，和分开走完再接起来，落在圆上的同一点。
于是只需留一格黄金转角，不必另备左转、右转两个直角。
同一份历史一直向前走，到斐波那契步数时会从左边、右边轮流靠回原来的自己；
每次回来对照，实读数都不能比原来对齐时更大。
如果自读数带着一点偏斜，总有一侧的足够近回返会把读数推高；
如果留下的是负量，转开也会比原来更高。两种情况都排除，剩下的就是这份历史真实而非负的量。
把所有有限拼法都这样校准，互相读数便组成同一张正比较表，
看不出任何区别的组合合成一个点，能分出的方向形成空间。
再按完整记录归一、把同一条纯态的公共相位合掉，两维复比较空间才显出量子球面。
观察者沿着自己已经取得的记录继续拼接这个结构；步数可以只向前增长，
比较仍会从两侧回返。黄金进位供应了这套回返的精确账本，
而真实读数为什么遵守它，还必须在整体内部找到相应的控制与记录关系来证明。

<a id="references"></a>

## 参考文献

<a id="ref-repo-c132-pin"></a>

### [1]

The Omega Institute, *trureturing*, immutable commit
[d9880e9f2c329bb3db982f33791419d5d90126b9](https://github.com/the-omega-institute/trureturing/commit/d9880e9f2c329bb3db982f33791419d5d90126b9)。
2026-11-04 11:01:29 UTC，19:01:29 Asia/Singapore。
[相对 C131 的固定两端比较](https://github.com/the-omega-institute/trureturing/compare/2c54932b6f9a7eb9a838e5be71e91d97e10027be...d9880e9f2c329bb3db982f33791419d5d90126b9)：26 个可达新增提交、四个第一父链合并；
关闭重命名推断后 150 条路径，32 新增、118 修改。

<a id="ref-repo-beta"></a>

### [2]

The Omega Institute,
[*WDigits.lean*](https://github.com/the-omega-institute/trureturing/blob/d9880e9f2c329bb3db982f33791419d5d90126b9/D5/S0/Conventions/WDigits.lean)，`wValue`、`wdigits`；
[*DeficitInteger.lean*](https://github.com/the-omega-institute/trureturing/blob/d9880e9f2c329bb3db982f33791419d5d90126b9/D5/S1/Deficit/DeficitInteger.lean)，
`betaDigits`、`betaReal`、`deficit_integer`；
[*DeficitThreeValued.lean*](https://github.com/the-omega-institute/trureturing/blob/d9880e9f2c329bb3db982f33791419d5d90126b9/D5/S1/Deficit/DeficitThreeValued.lean)，
`deficit_three_valued`。
原文全文核读，未重跑 Lean；索引为 $F_{i+2}$、$\phi^{i+2}$。

<a id="ref-repo-beatty"></a>

### [3]

The Omega Institute,
[*ZeckendorfDisplacementReading.lean*](https://github.com/the-omega-institute/trureturing/blob/d9880e9f2c329bb3db982f33791419d5d90126b9/D5/S1/Deficit/ZeckendorfDisplacementReading.lean)，
`displacement_decode_eq_beatty_floor`；
[*BetaBeattyClosedForms.lean*](https://github.com/the-omega-institute/trureturing/blob/d9880e9f2c329bb3db982f33791419d5d90126b9/D5/S1/Deficit/Beatty/BetaBeattyClosedForms.lean)，两个面读数的位移闭式；
[*GoldenPhaseDeficit.lean*](https://github.com/the-omega-institute/trureturing/blob/d9880e9f2c329bb3db982f33791419d5d90126b9/D5/S1/Deficit/GoldenPhaseDeficit.lean)，
`golden_phase_deficit`。
三份原文全文核读。其 phase 是实数模一的小数部分。

<a id="ref-repo-carry"></a>

### [4]

The Omega Institute,
[*Carry.lean*](https://github.com/the-omega-institute/trureturing/blob/d9880e9f2c329bb3db982f33791419d5d90126b9/D5/S1/Digit/Carry.lean)，四个原始进位规则；
[*Normalize.lean*](https://github.com/the-omega-institute/trureturing/blob/d9880e9f2c329bb3db982f33791419d5d90126b9/D5/S1/Digit/Normalize.lean)，严格下降量与规范化；
[*ChargedCarryPath.lean*](https://github.com/the-omega-institute/trureturing/blob/d9880e9f2c329bb3db982f33791419d5d90126b9/D5/S1/Deficit/ChargedCarryPath.lean)，
`betaDigits_sub_chargedReduces`、`charged_normal_form_unique`、
`carrySignedCount_phase_classifier`。
原文全文核读。路径无关的是净电荷及规范终点，不是路径长度。

<a id="ref-repo-cocycle"></a>

### [5]

The Omega Institute,
[*AdditiveCarryCocycle.lean*](https://github.com/the-omega-institute/trureturing/blob/d9880e9f2c329bb3db982f33791419d5d90126b9/D5/S1/Deficit/Cocycles/AdditiveCarryCocycle.lean)，
`sectionCarry`、`section_carry_cocycle`；
[*ExtensionSectionCoboundary.lean*](https://github.com/the-omega-institute/trureturing/blob/d9880e9f2c329bb3db982f33791419d5d90126b9/D5/S1/Deficit/Cocycles/ExtensionSectionCoboundary.lean)，
`extension_section_iff_coboundary`。
原文全文核读。前件包含加性商及实际右逆截面；消去判据要求核值余边界，
不能把任意环境空间中的形式抵消当作核值分裂。

<a id="ref-repo-c117"></a>

### [6]

The Omega Institute,
[*AURIC Common Source, Self-Reference and Observer Sequences C117*](https://github.com/the-omega-institute/trureturing/blob/d9880e9f2c329bb3db982f33791419d5d90126b9/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md)。
新增第 25–29 节全文核读：定义 25.1、定理 25.2；命题 26.2、27.2；
引理 28.1、命题 28.2 与定义 29.1。
另核读定义 17.1–17.3 及定理 17.4 陈述开头、定义 21.1 及定理 21.2 开头。
有限正生成、全未来方向充分性、原生身份和记录边均保留原前件；
未宣称新增理论文字已有对应 Lean 验证。

<a id="ref-repo-fourpath"></a>

### [7]

The Omega Institute,
[*Quantum Reality: Four-Path Full-Record Recovery Bound, Continuation IV*](https://github.com/the-omega-institute/trureturing/blob/d9880e9f2c329bb3db982f33791419d5d90126b9/docs/develop/theory/QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND_CONTINUATION_IV.md)。
第 49.1 节设定及定理 49.1、第 49.10 节依赖与边界。
核读这两处，未逐式重审其间全部代数，也未运行 Lean。
结论限定于文中选定几何族与相位反馈部分，未作全域最优断言。

<a id="ref-aronszajn1950"></a>

### [8]

N. Aronszajn, *Theory of reproducing kernels*,
*Transactions of the American Mathematical Society* **68**(3), 337–404 (1950).
[原始论文扫描件](https://pages.stat.wisc.edu/~wahba/stat860public/pdf2/aronszajn.pdf)；
[doi:10.1090/S0002-9947-1950-0051437-7](https://doi.org/10.1090/S0002-9947-1950-0051437-7)。
正核与 Hilbert 表示的经典来源；本稿给出所用构造的自包含证明。

<a id="ref-watrous2018"></a>

### [9]

J. Watrous, *The Theory of Quantum Information*, Cambridge University Press (2018).
[作者公开第 2 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，Theorem 2.22。
有限 Choi、Kraus、Stinespring 表示；完整正性与复合接口需另行供应。

<a id="ref-busch2003"></a>

### [10]

P. Busch, *Quantum states and generalized observables: a simple proof of Gleason's theorem*,
*Physical Review Letters* **91**, 120403 (2003).
[arXiv:quant-ph/9909073v3](https://arxiv.org/pdf/quant-ph/9909073)。
全效果一致可加评价的密度算符表示，包括二维；前件包含完整效果域、正性、可加性及归一化。

<a id="ref-mosseri2001"></a>

### [11]

R. Mosseri and R. Dandoloff,
*Geometry of entangled states, Bloch spheres and Hopf fibrations* (2001).
[arXiv:quant-ph/0108137v1](https://arxiv.org/pdf/quant-ph/0108137)，第 2 节。
公共相位圆纤维与单量子比特球面；须区分 Hilbert 空间与单位态球 $S^3$。

<a id="ref-arrighi2002"></a>

### [12]

P. Arrighi and C. Patricot,
*A note on the correspondence between qubit quantum operations and special relativity*,
预印本 2002，修订版 2003。
[arXiv:quant-ph/0212135v3](https://arxiv.org/pdf/quant-ph/0212135)，第 I 节、Lemma 1。
二阶 Hermitian 正锥与四维 Lorentz 锥的坐标对应；不据此推出物理时空。
