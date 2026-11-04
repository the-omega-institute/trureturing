# 平方闭合、递归稳定与关系量子场

从二元平方缺额到全部关系词闭合，以及场论极限的边界

**AURIC v89：一个完整候选及前沿研究接续**

项目连续研究稿

2026 年 11 月 3 日（新加坡）

## 摘要

本轮将“平方律使关系递归可以闭合”精确化，区分三种二次量：Born 分支强度、操作平方缺额与单次二元结果方差。正交细化相容固定平方权重是项目既有结果；本轮不把它重新宣布为新发现，也不把归一化图像稳定等同于完整内容无损。

唯一新候选 $C_{89}$ 是：对一个已继承的保单位元完全正内部转换 $\Phi$，若两个自伴读出 $A,B$ 被声明为闭合代表，则它们必须满足 $\Phi(A^2)=\Phi(A)^2$、$\Phi(B^2)=\Phi(B)^2$。借有限 Kraus 表示，平方缺额精确分解为补向比较的 Gram 核。这两个等式与全部非交换关系词的相容完全等价；因此无穷多个高阶闭合条件可由一个有限二元证书取代。这是标准乘法域理论在项目接口上的应用，不作数学优先权声明。

在忠实内部校准下，二元总缺额为零即为闭合证书，输入不确定性 Gram 恰等于输出 Gram 加遗漏 Gram。闭合时方差可以严格为正；归一球点不变时，遗漏尺度也可以持续非零。给出长度 $\ell$ 的关系词误差不超过 $\binom\ell2\delta$ 的解析界，并说明生成元病态或校准趋于不忠实时，不能把有限词近似升级成全通道近似。

进一步由保忠实态过程的不动关系构造稳定代数，其 Cesàro 平均给出 v88 的相容条件期望。在明写的对称性前提下，谱隙控制达到指定误差所需的比较深度；平方归一独自不能供应这份速率，更不能保证连续场正则性或杨–米尔斯质量隙。本轮核查了近期 OpenAI、Google DeepMind 及相关工作组原始资料，将有外力 Navier–Stokes 爆破、四维场存在性主张、特殊胶子振幅和数值构造工作分别定位。最后给出质量隙与中心化二元欧氏相关一致指数衰减的条件性等价，接回既有量子公理链。

全部数学论证为解析证明；没有运行数学程序、CAS、数值实验或候选枚举。

## 目录

- [1. 本轮接续：平方、稳定与递归停止分别指什么](#section-1)
- [2. 既有平方律：细分到哪一层，总分账都相同](#section-2)
- [3. 前沿研究提供的检验：平方闭合究竟保证到哪一步](#section-3)
- [4. 平方怎样成为闭合条件：本轮唯一候选](#section-4)
- [5. 有限补空间证明：两个平方锁住全部有序关系](#section-5)
- [6. 一个忠实标定与二元三维证书：形状之外还要保留尺度](#section-6)
- [7. 闭合仍可随机、仍可运动，并能保留不相容关系](#section-7)
- [8. 有限误差怎样传到高阶关系：一个二次词长界](#section-8)
- [9. 反向审计：删掉什么会失去什么](#section-9)
- [10. 平方闭合怎样接到稳定递归：由不动关系生成粗化](#section-10)
- [11. 递归深度由什么控制：平方结构与谱隙的分工](#section-11)
- [12. 平方归一为什么不能独自完成连续场极限](#section-12)
- [13. 从内部正核到场：反射比较与物理谱的接口](#section-13)
- [14. 质量间隙的二元关系形式：一致指数衰减](#section-14)
- [15. 把本轮候选放进一门完整的关系量子理论](#section-15)
- [16. 闭合保持了什么，后续操作又要求什么](#section-16)
- [17. 完整白话图景与统一关系场的范围](#section-17)
- [来源、版本与核读范围](#references)

<a id="section-1"></a>

## 1. 本轮接续：平方、稳定与递归停止分别指什么

本轮版本为 v89，承接 v88 的相对锚、双向有序比较与保态条件期望。文献核查截止 2026 年 11 月 3 日（新加坡）。仓库当前 HEAD 的一次有界公开读取失败，本轮仓库判断仍限定于已核验固定提交

`c63ab162315fddd0801cbe9f47dbf3eda6e13360`

中本地已有的 16 份理论 Markdown 及本对话连续稿，不认证该基线之后的仓库更新。

项目 V67 已由正交细化相容证明平方权重；V79 已由二元反向相容和相位锚得到复效果；基础稿已证明有限未来观察闭包、Schur 记录通道的不动代数；Atlas III 已给可见预测自治与 Heisenberg 闭合的等价；v88 已给条件方差塔与“残差为零而方差非零”的例子 [1](#ref-v67)–[6](#ref-v88)。本轮推进一般完全正转换上的**有限平方证书**，将已有机制连接到全部非交换关系词和精确停止条件。

| 三种二次量 | 公式 | 它回答的问题 |
|---|---|---|
| Born 强度 | $p_e=\|M_e\psi\|^2$ | 同一事件怎样在正交分支间分账 |
| 操作平方缺额 | $\Delta_\Phi(A)=\Phi(A^2)-\Phi(A)^2$ | 先组合再转换，与先转换再组合，是否遗漏关系 |
| 二元结果方差 | $p(1-p)$ | 已给定概率的单次二元结果还有多大分散 |

三者共享正二次比较结构，但相互之间没有无条件同一。本轮的“停止”特指：在声明生成元及后续关系范围内，不再需要增加隐藏补项来修复代表之间的组合。它允许继续计算、继续发生酉运动，也允许每次读出仍然是概率性的。若问某个递归算法实际何时停机，还须证明执行过程达到停止证书；若问所有尺度的场是否正则，还须相应的导数和极限估计。

**白话图景。**平方律可以让账目闭合，但先要说清楚是哪本账。分支分账不因细分而改变，是一件事；两份内容继续组合时不再出现遗漏，是另一件事。这两件事都成立以后，一次测量仍然可以有不确定结果。本轮将“可以停止补关系”写成一个有限、可检验的条件。

<a id="section-2"></a>

## 2. 既有平方律：细分到哪一层，总分账都相同

### 命题 2.1（正交细化固定平方权重，继承 V67）

在已经重构的 Hilbert 范数上，设分支权重非负、只依赖该分支范数，且不依赖无关坐标或正交记录的命名。令 $w(t)$ 表示范数为 $\sqrt t$ 的分支权重。若

$$
w(1)=1,\qquad w(s+t)=w(s)+w(t)\quad(s,t\ge0, s+t\le1),
$$

则 $w(t)=t$，故 $p_e=\|M_e\psi\|^2$。

**证明。**加性给 $w(0)=0$，等分给 $w(1/n)=1/n$，继而 $w(m/n)=m/n$。非负性给单调性；以有理数从上下夹逼任意 $t$，得 $w(t)=t$。

这是 V67 定理 9.5 的既有推导 [1](#ref-v67)。它保留全实细化、同一事件、共同范数和实际记录容量等前件；仅在固定有限菜单上核验，不能无条件使用有理逼近推得整个实区间。

### 推论 2.2（有限结果树的平方分账闭合）

若每个内部节点的后继构成等距记录分解，则对任意完备有限叶截口 $\mathcal L$，

$$
\sum_{w\in\mathcal L}\|\psi_w\|^2=\|\psi_{\rm root}\|^2.
$$

**证明。**每个节点都有 $\sum_j\|\psi_{wj}\|^2=\|\psi_w\|^2$。由最深节点向根逐次替换，所有内部项相消。

这接续项目已有结果核递归 [2](#ref-v78)，证明任意有限细分的分账相容，并不证明过程一定在有限层成为叶节点。唯一恒等后继的无限链已经归一却从不终止。

幂律试探也显示平方指数的作用。若把幅度 $a$ 细分成两份 $a/\sqrt2$，幂权重的未归一总量为

$$
2\left|\frac a{\sqrt2}\right|^p=2^{1-p/2}|a|^p.
$$

要在未改变粗事件的正交细分后保持同一分账，必须取 $p=2$。这个计算使用既有 Hilbert 等距细分，没有从无前提中推导范数结构或复数域。

### 命题 2.3（归一、连续和二次齐次仍不足以决定 Born 效果）

对 $z=(z_1,z_2)\ne0$，令 $s=|z_1|^2+|z_2|^2$，定义

$$
w_0(z)=\frac{(|z_1|^2-|z_2|^2)^2}{s},\qquad w_1(z)=s-w_0(z),
$$

在零点取零。它们非负、连续、二次齐次、共同相位不变，且总量为 $s$，但不存在固定效果 $E$ 使 $w_0(z)=\langle z,Ez\rangle$。

**证明。**在两个正交基态上概率都是一，因此若效果存在，$I-E\ge0$ 在两个基向量上均有零期望。正算子的平方根随即消去这两个基向量，故 $E=I$；但在 $(1,1)/\sqrt2$ 上所给概率为零，矛盾。其余性质由 $0\le w_0\le s$ 直接得到。

这个反例已在 V79 §9.1 出现 [3](#ref-v79)，指出实际缺口是同一事件在相干重编码下的相容。因此本轮继承已有 Born 结构，继续研究平方比较何时能给关系递归的闭合证书。

**白话图景。**同一份内容分成两份、再分成四份，平方分账让粗事件的总量不变。这样可以在任何已完成的有限截口停下来计算总账。但一个过程还可以继续生出下一层；要说它的代表已不需要再补新关系，还要检查本轮接下来定义的平方缺额。

<a id="section-3"></a>

## 3. 前沿研究提供的检验：平方闭合究竟保证到哪一步

本节检索截止 **2026 年 11 月 3 日，新加坡时间**。我们核读公开原稿中的定义、定理陈述与论证范围，并区分公告、公开证明、形式化材料和数值证据。以下研究用于检验本项目的推理边界；它们没有替本项目证明新的量子公理。

| 工作与日期 | 公开证据层级 | 必须保留的适用范围 |
|---|---|---|
| OpenAI Navier–Stokes，2026-09-08 | 公开证明稿与 Lean 材料 | 光滑外力下的有限时间爆破；对应 Clay 的 C/D 选项 [10](#ref-nspaper)–[12](#ref-clayns) |
| OpenAI QCD／Yang–Mills，2026-10-26 | 存在性公告与工作组声明 | 证明材料尚未公开；禁闭和质量隙仍为开放挑战 [13](#ref-openai1026)–[14](#ref-ymcommittee) |
| 单负螺旋度胶子树振幅，原稿 2026-02-12 | 特殊区域内的解析递归证明 | Klein 签名、半共线支撑及分布型振幅 [16](#ref-gluon) |
| DeepMind 不稳定奇异性，原稿 2025-09-17 | PINN 数值候选与稳定性分析 | 特定流体模型；不是无边界 NS 的完整证明 [17](#ref-deepmindfluids) |
| AlphaEvolve 数学构造，首稿 2025-11-03 | 构造搜索、见证与界的改进 | 一侧界改进不等于精确最优值 [18](#ref-alphaevolve) |

### 光滑外力 NS：有限平方总量仍可伴随局部爆破

OpenAI 原稿定理 1.1 声称，对每个正粘性 $\nu>0$，可以构造三维不可压缩 Navier–Stokes 流，从 $u(\cdot,0)=0$ 出发，外力满足

$$
f\in C_c^\infty(\mathbb R^3\times(0,\infty);\mathbb R^3),
$$

速度在 $t<1$ 光滑，并有

$$
\sup_{0\le t<1}\|u(t)\|_{L^2}<\infty,\qquad
\limsup_{t\uparrow1}\|u(t)\|_{L^\infty}=\infty.
$$

这是有光滑外力的定理陈述；Clay 的 C/D 选项允许这种外力，不能改写成无外力 NS 的结论。Clay 在 2026 年 9 月 11 日回应了公告并保留后续评估程序，未宣布完成授奖。本稿也不把读取定理陈述等同于独立复核全部证明 [10](#ref-nspaper)–[12](#ref-clayns)。

**白话图景。**平方积分把各处贡献加成一个总量。变化可以越来越集中，总量仍有限，局部却越来越大。本稿据此区分二次读出保持可控与所有递归变化都保持光滑；后者还要另外控制尺度与导数。

### QCD／Yang–Mills：存在、连续极限与质量隙须分别证明

OpenAI 的 2026 年 10 月 26 日公告称，其结果涉及四维相互作用规范场与费米子理论的存在性，包括 QCD；纯 Yang–Mills 存在性是其中一部分 [13](#ref-openai1026)。KITP 工作组声明说明材料基于格点与重整化群方法，涉及连续极限；工作组将先核对定义、问题陈述和 Lean 形式化与非形式证明的对应，再释放评估及材料，并明确保留禁闭和质量隙为开放挑战。我们没有读取尚未公开的 1147 页证明 [14](#ref-ymcommittee)。

Clay 原题要求对任意紧致单规范群在 $\mathbb R^4$ 构造非平凡量子 Yang–Mills 理论并证明严格正质量隙，还须满足足够强的量子场公理性质。存在性主张不能自动扩展成整个质量隙问题已经解决 [15](#ref-clayym)。

**白话图景。**在有限层写出一个正比较量，是开始；让所有尺度的比较相容地接成连续场，是下一项工作；再证明真空之上确实留有一段能量空隙，又是另一项工作。

### 胶子振幅、DeepMind 候选与 AlphaEvolve

核读的胶子论文为 2026 年 3 月 9 日的 v2。其半共线条件是 $\langle ij\rangle=0$ 对全部外腿成立；在 $(2,2)$ Klein 签名中仍可有 $[ij]\ne0$，普通 Minkowski 实动量没有相同自由。完整振幅含限制支撑的 delta 分布；在特殊单入多出区域给出剥离振幅闭式，用 Berends–Giele 递归证明并检查软极限。这不是一般运动学结论，也不能将分布型振幅逐点平方当作普通概率 [16](#ref-gluon)。

DeepMind 的不稳定奇异性工作使用 PINN、Gauss–Newton 和多阶段训练，研究 CCF、IPM、Boussinesq 等模型；证据包括高精度自相似候选、验证网格上的 PDE 残差和线性化不稳定模态。某些 CCF 候选残差约为 $10^{-13}$；Boussinesq 的第四不稳定候选明确未获可靠验证。这些结果供应后续严格计算机辅助证明的候选，不等于完成无边界 NS 证明 [17](#ref-deepmindfluids)。

AlphaEvolve 的公开 v3 报告 67 个数学问题中的构造搜索。相关的非负函数自卷积不等式将相应最佳常数的已知上界从 $1.50992$ 改进到 $1.5032$，这是特定一侧界改进，未确定精确最优常数 [18](#ref-alphaevolve)。对经典卷积

$$
(f*g)(t)=\int f(x)g(t-x)\,dx
$$

同一输入进入两个位置给出

$$
(\alpha f)*(\alpha f)=\alpha^2(f*f).
$$

二元自组合产生二次齐次性可以解释平方自然出现，却尚未在经典关系模型与量子读出之间完成选择。ETH 的名词也须区分：同期公告中的 ETH 是指数时间假设，不是本征态热化假设，不等于证明 $\mathrm P=\mathrm{NP}$ 或 Born 规则 [13](#ref-openai1026)；固定宽度精确计数的形式化范围另见 [19](#ref-ethscope)。

**白话图景。**这些前沿工作的共同启发，是把直觉变成能够反查的定义和条件。平方、正性、递归闭合、连续场存在以及质量隙，各自回答不同的问题。接下来的新候选只承担它确实能够证明的那一步。

<a id="section-4"></a>

## 4. 平方怎样成为闭合条件：本轮唯一候选

本轮继承共同复关系、Born 读出及完整组合所要求的完全正接口。因此不再把平方概率律当作尚未证明的新命题。这里推进的是另一个问题：一对关系经过当前内部转换后，什么时候不必再为它们组成的更高关系逐项补充隐藏修正？

### 定义 4.1（当前比较转换与生成关系）

固定保单位元完全正映射

$$
\Phi:M_d(\mathbb C)\longrightarrow M_k(\mathbb C),\qquad \Phi(I_d)=I_k,
$$

以及两个 Hermitian 读出 $A,B\in M_d$。记 $\mathfrak A=C^*(I,A,B)$ 为它们生成的有限 $*$-代数。称这对读出在当前转换下**代数闭合**，是指对每个非交换多项式 $p$，

$$
\boxed{\Phi(p(A,B))=p(\Phi(A),\Phi(B)).}
$$

多项式保留乘法次序，例如 $AB$ 与 $BA$ 不是同一个符号。这个定义看似要求无穷多个核验；本节把它锁定为两个平方等式。$\Phi$ 是可观测关系端的映射，其普通迹对偶 $\Phi_*$ 完全正且迹保持；这里没有把 $\Phi$ 本身额外假定为迹保持、幂等或时间演化。

### 定义 4.2（有序平方缺额）

对任意关系元 $x,y\in M_d$，定义

$$
\Gamma_\Phi(x,y)=\Phi(x^\dagger y)-\Phi(x)^\dagger\Phi(y),
\qquad \Delta_\Phi(x)=\Gamma_\Phi(x,x).
$$

### 定义 4.3（$C_{89}$：二元平方闭合候选）

对声明已经闭合的 Hermitian 关系对 $(A,B)$，采用唯一的有限条件

$$
\boxed{\Delta_\Phi(A)=0,\qquad \Delta_\Phi(B)=0.}
$$

即先组成平方再转换，与先转换再组成平方给出同一个关系。

下文证明：在已经继承的完全正接口内，这个有限条件与全部非交换多项式的闭合等价。这里使用标准乘法域理论 [20](#ref-choi)–[21](#ref-mdqec)；本轮的贡献是它在项目递归问题中的位置和可核验含义，不将已有数学定理宣称为新发现。

**白话图景。**把两份基本读出继续相乘、换次序，再组成更高关系，表面上可以一直追下去。平方闭合提供了一个有限检查：如果两端的平方都没有遗漏，它们全部生成关系的代表就会自动相容。停止的是为了修补代表而不断加条件的递归，不是命令所有运动和计算停止。

<a id="section-5"></a>

## 5. 有限补空间证明：两个平方锁住全部有序关系

使用已继承的有限 Kraus 表示，写成

$$
\Phi(x)=\sum_rK_r^\dagger xK_r,qquad \sum_rK_r^\dagger K_r=I_k.
$$

定义从 $\mathbb C^k$ 到 $\mathbb C^d\otimes\mathbb C^s$ 的等距映射

$$
V\psi=\sum_rK_r\psi\otimes|r\rangle,qquad
\pi(x)=x\otimes I_s,qquad P=VV^\dagger,qquad Q=I-P.
$$

于是 $V^\dagger V=I_k$、$\Phi(x)=V^\dagger\pi(x)V$。这是有限 Stinespring 表示的直接构造，不需要增加新的物理环境公理。

### 引理 5.1（平方缺额就是补向 Gram 核）

令 $D(x)=Q\pi(x)V$。则

$$
\boxed{\Gamma_\Phi(x,y)=D(x)^\dagger D(y).}
$$

因此 $\Delta_\Phi(x)\ge0$，任意有限算符块矩阵 $[\Gamma_\Phi(x_i,x_j)]_{ij}$ 都为正，并且

$$
\|\Gamma_\Phi(x,y)\|_{\rm op}
\le\sqrt{\|\Delta_\Phi(x)\|_{\rm op}\,\|\Delta_\Phi(y)\|_{\rm op}}.
$$

**证明。**在 $\Phi(x^\dagger y)$ 与 $\Phi(x)^\dagger\Phi(y)$ 中插入有限表示，得到

$$
\Gamma_\Phi(x,y)=V^\dagger\pi(x)^\dagger(I-VV^\dagger)\pi(y)V=D(x)^\dagger D(y).
$$

块矩阵的任意二次型为 $\|\sum_iD(x_i)\xi_i\|^2\ge0$；最后一式由算符范数次乘性及 $\|D(x)\|^2=\|D(x)^\dagger D(x)\|$ 得到。

### 定义 5.2（乘法域）

记

$$
\operatorname{MD}(\Phi)=\{c\in M_d:\Phi(cx)=\Phi(c)\Phi(x),\ \Phi(xc)=\Phi(x)\Phi(c)\ \text{对全部 }x\in M_d\}.
$$

它要求与任意关系从左右两侧组合时都能延续。

### 定理 5.3（二元平方闭合的完整等价）

对上述 Hermitian 的 $A,B$，下列条件等价：

1. $C_{89}$ 成立。
2. $D(A)=D(B)=0$。
3. $[P,\pi(A)]=[P,\pi(B)]=0$。
4. $A,B\in\operatorname{MD}(\Phi)$。
5. $\mathfrak A\subseteq\operatorname{MD}(\Phi)$。
6. $\Phi|_{\mathfrak A}$ 是保单位元的 $*$-同态。
7. 全部非交换多项式满足 $\Phi(p(A,B))=p(\Phi(A),\Phi(B))$。

**证明。**平方缺额分解立即给出前两项等价。因为 $A=A^\dagger$，$D(A)=0$ 给出 $Q\pi(A)P=D(A)V^\dagger=0$；取伴随还得到 $P\pi(A)Q=0$，所以 $[P,\pi(A)]=0$，$B$ 同理，反向显然。

若 $P$ 与两个生成元的表示对易，它就与所有 $\pi(c)$、$c\in\mathfrak A$ 对易。于是对任意 $x\in M_d$，

$$
\begin{aligned}
\Phi(cx)-\Phi(c)\Phi(x)&=V^\dagger\pi(c)Q\pi(x)V=0,\\
\Phi(xc)-\Phi(x)\Phi(c)&=V^\dagger\pi(x)Q\pi(c)V=0.
\end{aligned}
$$

这给出第五项及第六项；逐次相乘和线性组合给出所有多项式等式。反过来只取多项式 $p(X,Y)=X^2,Y^2$ 即回到第一项。第四项由第五项推出，也通过取 $x=A,B$ 推出第一项。

对一般非 Hermitian 元 $x$，需要同时要求

$$
\Delta_\Phi(x)=0,\qquad\Delta_\Phi(x^\dagger)=0,
$$

分别消去 $Q\pi(x)P$ 和 $P\pi(x)Q$，从而等价于 $x\in\operatorname{MD}(\Phi)$；选取 Hermitian 生成元正是将两个方向合并为最简平方条件。

### 命题 5.4（闭合与忠实保存的区别）

在 $C_{89}$ 成立时，主定理给出 $*$-同态，但一般不保证单射。若另有输出校准 $\eta$，使 $\rho=\Phi_*(\eta)$ 在 $\mathfrak A$ 上忠实，则限制同态单射。若 $\mathfrak A=M_d$，它自动单射；再有 $k=d$ 时，$\Phi$ 为酉共轭。

**证明。**若 $c\in\mathfrak A$ 且 $\Phi(c)=0$，同态性给出

$$
\phi_\rho(c^\dagger c)=\phi_\eta(\Phi(c)^\dagger\Phi(c))=0,
$$

忠实性迫使 $c=0$。完整矩阵代数只有零理想和全代数，保单位元排除后者；同维时单射同态满射。取标准矩阵单位 $e_{ij}$，其像给出一组秩一矩阵单位，选像 $\Phi(e_{11})$ 的单位向量 $v_1$，令 $v_i=\Phi(e_{i1})v_1$，即可得到 $\Phi(e_{ij})=|v_i\rangle\langle v_j|$，故 $\Phi(x)=UxU^\dagger$。

**白话图景。**平方缺额等于补空间里剩余分量的长度平方。两份 Hermitian 读出没有补向剩余，就意味着它们从左右两侧都不会把关系漏出去，所有后续乘积因此自动闭合。闭合还不一定是忠实保存：一个同态可能把整块内容送到零；要说完整内容没有丢失，还必须保证当前比较能看见那一块。

<a id="section-6"></a>

## 6. 一个忠实标定与二元三维证书：形状之外还要保留尺度

取输出空间上的忠实校准 $\eta>0$、$\operatorname{tr}\eta=1$，并定义输入校准 $\rho=\Phi_*(\eta)$。它自动归一，但不必忠实。对 $A_1=A,A_2=B$，令

$$
\delta A_i=A_i-\phi_\rho(A_i)I,\qquad \phi_\rho(x)=\operatorname{tr}(\rho x).
$$

保单位元保证 $\phi_\eta(\Phi(\delta A_i))=0$。

### 定理 6.1（二元不确定性的完整平方预算）

定义

$$
\begin{aligned}
(G_{\rm in})_{ij}&=\phi_\rho(\delta A_i^\dagger\delta A_j),\\
(G_{\rm out})_{ij}&=\phi_\eta(\Phi(\delta A_i)^\dagger\Phi(\delta A_j)),\\
L_{ij}&=\phi_\eta(\Gamma_\Phi(A_i,A_j)).
\end{aligned}
$$

则

$$
\boxed{G_{\rm in}=G_{\rm out}+L,\qquad L\ge0.}
$$

写成 $L=\begin{pmatrix}a&c\\\bar c&b\end{pmatrix}$，有

$$
\boxed{a+b=0\quad\Longleftrightarrow\quad C_{89}\text{ 成立}.}
$$

**证明。**由输入输出校准的对偶关系，将 $G_{\rm in}$ 写成 $\phi_\eta(\Phi(\delta A_i^\dagger\delta A_j))$，逐项相减即得预算。由引理 5.1，

$$
L_{ij}=\langle D(A_i)\sqrt\eta,D(A_j)\sqrt\eta\rangle_{\rm HS},
$$

所以 $L$ 正。其对角元分别为 $\|D(A)\sqrt\eta\|_{\rm HS}^2$ 与 $\|D(B)\sqrt\eta\|_{\rm HS}^2$。$\eta>0$ 使 $\sqrt\eta$ 可逆，故它们之和为零恰好意味着 $D(A)=D(B)=0$。

这个标量证书是精确理论等式，不意味着有限次带误差实验能认证实数严格为零。它同时显示：只要 $C_{89}$ 成立，输入输出完整二元不确定性 Gram 矩阵就相等；这并没有要求矩阵本身为零。

### 命题 6.2（有限三维表示及零尺度边界）

若 $s=a+b>0$，则

$$
\frac Ls=\frac12(I+\mathbf r\cdot\boldsymbol\sigma),\quad
\mathbf r=\frac{(2\operatorname{Re}c,-2\operatorname{Im}c,a-b)}{a+b},\quad |\mathbf r|\le1.
$$

若 $a,b>0$，也可使用上半球坐标

$$
\mathbf q=\frac{(\operatorname{Re}c,\operatorname{Im}c,\sqrt{ab-|c|^2})}{\sqrt{ab}}\in S^2_+.
$$

恢复整个二元缺额块，Bloch 球坐标须配合总尺度 $s$；上半球坐标则须配合 $a,b$，或等价地配合 $s$ 与 $a/b$。闭合对应 $s=0$，此时归一化缺额球没有定义。

**证明。**$L\ge0$ 给出 $a,b\ge0$ 及 $ab-|c|^2\ge0$。直接计算

$$
1-|\mathbf r|^2=\frac{4(ab-|c|^2)}{(a+b)^2},\qquad |\mathbf q|^2=1.
$$

由 $s,\mathbf r$ 或 $a,b,\mathbf q$ 都能恢复 $a,b,c$；若 $a+b=0$，正性迫使整个 $L=0$，不能再除以尺度来指定特权方向。

### 命题 6.3（归一化不变并不意味着平方闭合）

取 qubit 去极化映射

$$
\Phi_\lambda(x)=\lambda x+(1-\lambda)\frac{\operatorname{tr}x}{2}I,qquad 0<\lambda<1,
$$

以及 $\rho=\eta=I/2$、$A=\sigma_x,B=\sigma_z$。则

$$
G_{\rm in}=I_2,\qquad G_{\rm out}=\lambda^2I_2,\qquad L=(1-\lambda^2)I_2.
$$

因此两个 Gram 矩阵归一化后都等于 $I_2/2$，但平方总缺额 $s=2(1-\lambda^2)>0$。

**证明。**该映射是恒等映射与完全去极化映射的凸组合，故为 UCP。两个 Pauli 元的校准均值为零，平方为 $I$，交叉乘积无迹；转换后各自变成 $\lambda$ 倍。

**白话图景。**稳定的归一图形还不够。一张图可以不断缩小，归一以后却始终长得一样。平方账要连大小一起保留，才能分清关系已经接好，还是把持续损失藏进归一化。真正闭合时，缺额的总尺度为零；原本的概率分散则可以完整留下。

<a id="section-7"></a>

## 7. 闭合仍可随机、仍可运动，并能保留不相容关系

### 命题 7.1（v88 的精确接回）

令 $E=E_{\rho,\mathcal A}$ 为 v88 已建立的忠实保态条件期望。则对任意 $x$，

$$
\Delta_E(x)=E\!\left((x-E(x))^\dagger(x-E(x))\right),\qquad
\phi_\rho(\Delta_E(x))=\|x-E(x)\|_\rho^2.
$$

从而 $\Delta_E(x)=0\Longleftrightarrow x=E(x)\Longleftrightarrow x\in\mathcal A$。

**证明。**展开右侧，利用 $\mathcal A$-双模性及 $E^2=E$，交叉项合并为 $-E(x)^\dagger E(x)$；保态性给第二式，忠实性将零范数变成 $x=E(x)$。

这解释了为何本轮不能只重复 v88 方差分解：对已经指定的条件期望，平方零缺额只是代数成员资格。本轮的新用途是允许一般非幂等的 $\Phi$，由两个平方等式直接确定整个可延续的生成代数。

### 命题 7.2（已经闭合的随机二元读出）

取

$$
P_+=\frac{I+\sigma_z}{2},\qquad P_-=I-P_+,qquad E_z(x)=P_+xP_++P_-xP_-.
$$

并以 $\rho=\eta=I/2$ 校准。二元读出 $(P_+,P_-)$ 满足 $C_{89}$，但

$$
p(+)=\frac12,\qquad \operatorname{Var}_\rho(P_+)=\frac14.
$$

**证明。**$E_z(P_\pm)=P_\pm$ 且 $P_\pm^2=P_\pm$，故平方缺额为零；另一方面 $\operatorname{tr}(\rho P_+)=1/2$，方差为 $1/2-(1/2)^2=1/4$。

### 命题 7.3（量子闭合不等于经典共同赋值）

若 qubit 上的 $\sigma_x,\sigma_z$ 同时满足 $C_{89}$，则 $\Phi$ 在整个 $M_2$ 上为保单位元 $*$-同态；同维输出时为酉共轭。这套完整关系不能以同样方式闭合到一个交换代数中。

**证明。**$I,\sigma_x,\sigma_z,\sigma_x\sigma_z$ 张成 $M_2$，主定理适用。若像落在交换代数，记 $X=\Phi(\sigma_x),Z=\Phi(\sigma_z)$，同态性给 $X^2=Z^2=I$、$XZ=-ZX$，交换性给 $XZ=ZX$，于是 $XZ=0$，与 $X,Z$ 可逆矛盾。

这排除的是完整有序关系的经典共同表示，并不禁止普通测量。量子到经典的状态通道，其 Heisenberg 对偶方向是从经典可观测量到量子可观测量；不能把上述代数表示问题与该通道方向混写。

平方闭合也不要求关系停止运动。例如 $U_\theta=e^{-i\theta\sigma_z/2}$、$\Phi_\theta(x)=U_\theta^\dagger xU_\theta$ 对全部关系平方闭合，但

$$
\Phi_\theta(\sigma_x)=\cos\theta\,\sigma_x-\sin\theta\,\sigma_y
$$

通常不是 $\sigma_x$，也不是幂等转换。“没有平方缺口”与“已经是固定点”是两个不同命题。

本节只证明当前 $\Phi$ 内的代数延续，不供应所有多项式对应的原生装置，也不保证任意后续内部操作都保持闭合关系；若要将当前内容地址用于全部未来菜单，仍需继承项目的操作闭包与历史身份条件。

**白话图景。**一个二元读出可以已经稳定闭合，结果却仍是一半对一半。两个不相容的读出也能一起完整保存在量子结构里，只是不能把它们全部关系压成共同的经典数值。同样，关系可以一边完整地绕转，一边始终没有平方缺额。闭合、确定、静止和可执行，是需要分别说清楚的四件事。

<a id="section-8"></a>

## 8. 有限误差怎样传到高阶关系：一个二次词长界

在应用中，比严格等于零更常见的是一个小而可界定的平方缺额。下面只推导有限关系词误差，不从有限误差跳到所有无限迭代的精确终止。

### 定理 8.1（有限词的成对缺额界）

令 $A_1,\ldots,A_\ell$ 为 Hermitian 字母，记

$$
M_j=\|A_j\|_{\rm op},\qquad \epsilon_j=\|D(A_j)\|_{\rm op}=\sqrt{\|\Delta_\Phi(A_j)\|_{\rm op}}.
$$

则

$$
\boxed{\left\|\Phi(A_1\cdots A_\ell)-\Phi(A_1)\cdots\Phi(A_\ell)\right\|_{\rm op}
\le\sum_{1\le i<j\le\ell}\epsilon_i\epsilon_j\prod_{k\ne i,j}M_k.}
$$

特别地，若所有字母从两个 Hermitian 收缩 $A,B$ 中选取，且 $\|\Delta_\Phi(A)\|_{\rm op},\|\Delta_\Phi(B)\|_{\rm op}\le\delta$，则每个长度为 $\ell$ 的词满足

$$
\boxed{\left\|\Phi(w)-w(\Phi(A),\Phi(B))\right\|_{\rm op}\le\binom\ell2\delta.}
$$

**证明。**UCP 映射在算符范数下收缩；有限表示中 $\|V\|=1$、$\|\pi(x)\|=\|x\|$ 也直接给出这一点。定义交织残差

$$
R(w)=\pi(A_1\cdots A_\ell)V-V\Phi(A_1)\cdots\Phi(A_\ell).
$$

由 $\pi(A_j)V-V\Phi(A_j)=D(A_j)$ 逐项相消，得到

$$
R(w)=\sum_{j=1}^{\ell}\pi(A_1\cdots A_{j-1})D(A_j)\Phi(A_{j+1})\cdots\Phi(A_\ell),
$$

从而

$$
\|D(w)\|_{\rm op}\le\sum_{j=1}^{\ell}\epsilon_j\prod_{k\ne j}M_k.
$$

令 $w'=A_2\cdots A_\ell$。首字母 Hermitian，故

$$
\Phi(A_1w')-\Phi(A_1)\Phi(w')=D(A_1)^\dagger D(w').
$$

将整体乘积误差写成这一项加上 $\Phi(A_1)[\Phi(w')-\Phi(A_2)\cdots\Phi(A_\ell)]$。第一项给出所有含指标 $1$ 的成对项，第二项通过归纳给出其余成对项，并补上因子 $M_1$。长度一时误差为零，归纳证明通式。令每个 $M_j\le1$、$\epsilon_j\le\sqrt\delta$ 即得二项式界。

### 推论 8.2（忠实标量证书给出有限词误差）

若输出校准满足 $\eta\ge\mu I$、$\mu>0$，且二元总缺额为 $s=a+b$，则对两个 Hermitian 收缩生成的长度 $\ell$ 词有

$$
\left\|\Phi(w)-w(\Phi(A),\Phi(B))\right\|_{\rm op}
\le\binom\ell2\frac{s}{\mu}.
$$

**证明。**对正算子 $T$，$\operatorname{tr}(\eta T)\ge\mu\operatorname{tr}T\ge\mu\|T\|_{\rm op}$。因此两个算符缺额的范数分别不超过 $a/\mu,b/\mu$，均不超过 $s/\mu$，应用定理 8.1。

### 命题 8.3（近似生成元闭合不自动控制整个通道）

存在始终生成 $M_2$ 的两收缩，其平方缺额趋于零，但对应通道始终远离酉共轭。

**证明。**固定 $\Phi=E_z$，取

$$
A=\sigma_z,\qquad B_\varepsilon=\frac{\sigma_z+\varepsilon\sigma_x}{\sqrt{1+\varepsilon^2}},\qquad \varepsilon>0.
$$

二者为 Hermitian 收缩，且

$$
\Delta_\Phi(A)=0,\qquad
\Delta_\Phi(B_\varepsilon)=\frac{\varepsilon^2}{1+\varepsilon^2}I\longrightarrow0.
$$

每个 $\varepsilon>0$ 时这对生成 $M_2$，因为

$$
\sigma_x=\frac{\sqrt{1+\varepsilon^2}B_\varepsilon-A}{\varepsilon}.
$$

然而 $\Phi(\sigma_x)=0$，任意酉共轭都将 $\sigma_x$ 送到范数为一的算符，所以两映射的算符诱导范数距离至少为一。恢复遗漏方向的系数随 $1/\varepsilon$ 发散，正是缺少统一控制的原因。

因此有限词长与有界系数下的近似结论可靠；若要扩展成整个代数的统一近似，必须另外控制生成关系的条件数或分离尺度。二项式界是明确的通用上界，不宣称对每个通道和每个词都最优。

**白话图景。**平方缺额很小，可以保证有限层关系的误差受到控制；层数增加时，成对误差会累积。但如果两个基本读出几乎指向同一个方向，要恢复另一方向就得把很小差别放大。所以“两个检查都很接近”不能无条件升级成“整个量子世界都接近无损”。

<a id="section-9"></a>

## 9. 反向审计：删掉什么会失去什么

### 命题 9.1（普通正性不能固定有序乘法）

转置 $T(x)=x^{\mathsf T}$ 正且保单位元，保持每个 Hermitian 元的平方，但一般不保持乘法次序。

**证明。**转置保持正矩阵，且 $T(A^2)=T(A)^2$，但 $T(AB)=T(B)T(A)$。例如 $A=\sigma_x,B=\sigma_z$ 都在转置下不变，其乘积却是反对称矩阵，所以 $T(AB)=-AB\ne T(A)T(B)$。

这证明普通正性不足以替代继承的完整量子组合接口。从纯代数角度，保单位元 Schwarz 映射已足以得到相应乘法域结论，因此这里不声称 CP 是逻辑上最弱的假设；采用 CP 是因为项目已要求与任意有限辅助系统相容。

### 命题 9.2（非 Hermitian 元不能只查一个平方）

取 $\Phi(x)=\langle0|x|0\rangle$ 及 $x=|0\rangle\langle1|$。则

$$
\Phi(x^\dagger x)=0=|\Phi(x)|^2,\qquad \Phi(xx^\dagger)=1.
$$

所以单侧平方相容不能替代 $\Delta_\Phi(x)=\Delta_\Phi(x^\dagger)=0$。

**证明。**$x^\dagger x=|1\rangle\langle1|$、$xx^\dagger=|0\rangle\langle0|$，直接代入。

只查两个关系的交叉项也不够。对 $E_z,A=\sigma_x,B=\sigma_z$，有 $\Gamma_{E_z}(A,B)=0$，但 $\Delta_{E_z}(A)=I$；一项交叉比较没有变化，不能代替两端各自的平方账。

### 命题 9.3（不忠实校准会隐藏非零缺额）

定义 UCP 映射

$$
\Phi:M_2\to M_3,\qquad \Phi(x)=x\oplus\frac{\operatorname{tr}x}{2},\qquad
\eta=\operatorname{diag}(1/2,1/2,0).
$$

对 $A=\sigma_x,B=\sigma_z$，两个算符平方缺额都为 $\operatorname{diag}(0,0,1)$，但它们在 $\eta$ 下的标量读数均为零。

**证明。**恒等表示与归一迹态都完全正，直和仍完全正且保单位元。每个 Pauli 元的平方为 $I$，其归一迹为零，代入即得缺额；$\eta$ 在第三个方向权重为零，因而看不见它。

同态闭合也不能自动替代忠实性。例如对 $M_3$ 的分块代数 $\mathfrak A=M_2\oplus\mathbb C$，取 UCP 读出 $\Phi(x)=\langle2|x|2\rangle$。其限制是保单位元同态，却将整个 $M_2$ 块送到零；在该块内取两个 Pauli 生成元并在第三维补零，即可构成平方闭合而内容被删去的关系对。这说明命题 5.4 的额外忠实条件有实际作用。

最后，$C_{89}$ 是对一个已经声明的内部接口与关系对进行闭合分类。它没有要求所有关系对都必须对每种信息处理零缺额；若作这种全域要求，主定理会迫使整个映射成为同态，从而排除通常的有损处理。它也没有推出所有未来菜单都保留当前生成代数，更没有从代数递归闭合推出无条件时间收敛或有限步停机。

**白话图景。**反着看，平方为什么重要就更清楚：只保普通正性，会允许把乘法方向整个翻过来；只看一侧或一个交叉项，会漏掉另一端；校准看不见某个方向，缺额就能藏在那里。把这些接口说清楚后，平方闭合才是一张有限而完整的证书。

<a id="section-10"></a>

## 10. 平方闭合怎样接到稳定递归：由不动关系生成粗化

前文解决的是一次转换下的代数闭合。要问反复转换会留下什么，还须声明同一空间上的动力学及其内部校准。本节是带明确前件的推论，不另立第二个新公理。

### 定理 10.1（保忠实态的稳定关系代数）

设 $\Phi:M_d\to M_d$ 为 UCP 映射，存在忠实态 $\rho>0$，满足 $\phi_\rho\circ\Phi=\phi_\rho$。则 $\mathcal F=\operatorname{Fix}\Phi$ 是一个含单位 $*$-子代数，且其中每一对 Hermitian 元均满足 $C_{89}$。此外 Cesàro 平均

$$
E_N=\frac1N\sum_{j=0}^{N-1}\Phi^j\longrightarrow E
$$

在有限维映射范数下收敛，极限 $E$ 是保 $\rho$ 的 UCP 条件期望，值域正是 $\mathcal F$。

**证明。**用 $\|x\|_\rho^2=\phi_\rho(x^\dagger x)$。平方不等式与保态性给

$$
\|\Phi(x)\|_\rho^2\le\phi_\rho(\Phi(x^\dagger x))=\|x\|_\rho^2.
$$

若 $\Phi(x)=x$，则 $\phi_\rho(\Delta_\Phi(x))=0$；缺额正且 $\rho$ 忠实，故 $\Delta_\Phi(x)=0$。对 $x^\dagger$ 同理，故 $x$ 在乘法域中；两个不动元的乘积、伴随、线性组合和单位元仍不动，所以 $\mathcal F$ 是子代数。

每个 $\Phi^n$ 在 GNS 范数下收缩，故其幂一致有界。有限维谱位于闭单位圆内，单位圆上没有非平凡 Jordan 块，否则幂会多项式增长。对 $|\lambda|<1$ 的 Jordan 块，幂平均趋于零；对 $|\lambda|=1,\lambda\ne1$ 的特征方向，几何和平均也趋于零；只有 $\lambda=1$ 部分留下。因此 $E_N$ 收敛到投影 $E$，值域为 $\mathcal F$。有限维正锥闭合，极限仍 UCP、保单位元且保 $\rho$。

对 $c,d\in\mathcal F$，乘法域给 $\Phi(cxd)=c\Phi(x)d$，迭代后同样成立。取平均和极限得 $E(cxd)=cE(x)d$，于是 $E$ 是所述保态条件期望。

对任意 $c\in\mathcal F$，双模性与保态性还给出

$$
\phi_\rho(cE(x))=\phi_\rho(cx),\qquad
\phi_\rho(E(x)c)=\phi_\rho(xc),
$$

左式给出 v88 的 GNS 正交比较，右式正是反向有序相容。这提供了从具体递归过程得到 C88 条件期望的机制，并包含 Schur 记录通道不动代数作为特例 [4](#ref-foundations)、[6](#ref-v88)。

### 命题 10.2（稳定关系等价于与全部记录分量相容）

若 $\Phi(x)=\sum_rK_r^\dagger xK_r$，则

$$
\mathcal F=\{K_r,K_r^\dagger:\text{全部 }r\}'.
$$

**证明。**若 $x$ 不动，零缺额与有限表示给 $\pi(x)V=V\Phi(x)=Vx$，比较各记录分量得 $xK_r=K_rx$；对 $x^\dagger$ 同理并取伴随。反之与全部 $K_r$ 对易则 $\Phi(x)=\sum_rK_r^\dagger K_rx=x$。

### 命题 10.3（平方闭合不保证逐步收敛）

即使每一步都对所有关系平方闭合，$\Phi^n(x)$ 也可以永远振荡。

**证明。**取 $\Phi(x)=\sigma_zx\sigma_z$、$\rho=I/2$。这是保忠实态的酉共轭，对每个 $x$ 两侧平方缺额都为零，但 $\Phi^n(\sigma_x)=(-1)^n\sigma_x$ 不收敛；其平均 $E_N(\sigma_x)$ 趋于零。

平均选择稳定关系，不意味着未平均的真实轨迹已经停下。没有保忠实态时，不动空间在原有乘法下也不能直接套用本定理。

**白话图景。**一个内部过程反复作用，始终不被它改变的内容会组成一套稳定关系。平方缺额让我们证明，这些稳定内容之间继续相乘也仍然稳定。把整个过程的长程平均取出来，就得到 v88 的相容粗化。但平均稳定和每一步停稳不是同一件事：量子关系可以一直来回转，平均却已经确定。

<a id="section-11"></a>

## 11. 递归深度由什么控制：平方结构与谱隙的分工

在保忠实态前提之外，暂且再研究一个条件模型：$\Phi$ 对 GNS 内积自伴，

$$
\langle x,\Phi(y)\rangle_\rho=\langle\Phi(x),y\rangle_\rho.
$$

这是明确的数学假设，不称为从 $C_{89}$ 已经推出。因为 $\Phi$ 自伴且收缩，它的 GNS 谱属于 $[-1,1]$。令 $L=I-\Phi\ge0$，正性是在 GNS Hilbert 空间上的自伴超算子意义下，并非声称 $L$ 把每个正矩阵送到正矩阵。定义

$$
T_t=e^{-tL}=e^{-t}\sum_{n=0}^{\infty}\frac{t^n}{n!}\Phi^n,qquad t\ge0.
$$

系数非负且总和为一，故 $T_t$ 是 UCP、保 $\rho$ 的半群。$t$ 表示无量纲的平均比较次数，尚未识别为物理时间或能量；误差界适用于这个随机化平均通道，不保证每条原生执行路径在至多 $t$ 步达到同样误差。

### 定理 11.1（有谱隙时的有限精度稳定）

若 $\mathcal F^\perp$ 非零，记 $\gamma>0$ 为 $L$ 在该空间上的最小特征值，则对全部 $x$ 和 $t\ge0$，

$$
\boxed{\|T_t(x)-E(x)\|_\rho\le e^{-\gamma t}\|x-E(x)\|_\rho.}
$$

因此给定误差 $\varepsilon>0$，若初始残差大于 $\varepsilon$，只需

$$
t\ge\frac1\gamma\log\frac{\|x-E(x)\|_\rho}{\varepsilon}.
$$

若初始残差不超过 $\varepsilon$，取 $t=0$ 即可。

**证明。**有限维自伴谱分解把 $L$ 对角化。零特征空间正是 $\operatorname{Fix}\Phi$，其正交投影为 $E$；其余特征方向在 $T_t$ 下乘以 $e^{-t\lambda}$，且 $\lambda\ge\gamma$。各方向平方长度相加得范数界，解指数不等式即得精度界。

若 $\mathcal F=M_d$，则 $L=0$、$E=\operatorname{id}$，已经精确稳定，无需正谱隙。即使 $\gamma>0$，非零特征方向在任何有限 $t$ 仍非零，所以本定理保证有限精度，不保证有限步精确消灭全部残差。

### 命题 11.2（平方律不给出统一稳定速率）

在同一 qubit 载体、同一 Born 读出和同一忠实校准上，存在一族满足上述条件的过程，其正谱隙趋于零。

**证明。**取去极化映射

$$
\Phi_\lambda(x)=\lambda x+(1-\lambda)\frac{\operatorname{tr}(x)}2I,qquad0<\lambda<1.
$$

它对 $\rho=I/2$ 保态且 GNS 自伴。单位方向特征值为一，全部无迹方向特征值为 $\lambda$，故 $\gamma_\lambda=1-\lambda\downarrow0$ 当 $\lambda\uparrow1$。共同复核、Born 规则及维数均未改变。

**白话图景。**平方结构告诉我们误差怎样记账，谱隙告诉我们剩余区别消退得多快。如果每层都有一个越来越慢的方向，即使每层最后都能稳定，也可能没有一个对全部层同时有效的停止深度。

<a id="section-12"></a>

## 12. 平方归一为什么不能独自完成连续场极限

近期有外力 Navier–Stokes 结果的直接启发，是区分总体二次控制与局部正则性。下面给一个完全解析、与具体流体方程无关的反例。

### 命题 12.1（固定平方总量可以集中成奇异读出）

取 $f\in C_c^\infty(\mathbb R^3)$、$\|f\|_2=1$，令

$$
f_\varepsilon(x)=\varepsilon^{-3/2}f(x/\varepsilon),\qquad\varepsilon>0.
$$

则

$$
\|f_\varepsilon\|_2=1,\qquad
\|f_\varepsilon\|_\infty=\varepsilon^{-3/2}\|f\|_\infty,\qquad
\|\nabla f_\varepsilon\|_2=\varepsilon^{-1}\|\nabla f\|_2.
$$

当 $\varepsilon\downarrow0$ 时，$f_\varepsilon$ 在 $L^2$ 中弱收敛于零，但概率测度 $|f_\varepsilon|^2dx$ 弱收敛于原点单位点质量 $\delta_0$。

**证明。**代换 $x=\varepsilon y$ 得 $L^2$ 等式；上确界由幅度缩放，求导多出 $\varepsilon^{-1}$。取 $R$ 使 $\operatorname{supp}f\subseteq B_R$，对任意 $g\in L^2$，Cauchy–Schwarz 给

$$
|\langle g,f_\varepsilon\rangle|\le\|g1_{B_{\varepsilon R}}\|_2\|f_\varepsilon\|_2\longrightarrow0.
$$

对任意有界连续函数 $h$，

$$
\int h(x)|f_\varepsilon(x)|^2dx=\int h(\varepsilon y)|f(y)|^2dy\longrightarrow h(0)
$$

由控制收敛得到点质量极限。

所以“先取幅度弱极限再平方”与“先平方再取读出极限”一般不交换。这没有构造 Navier–Stokes 解，也没有声称证明量子场的紫外发散；它只严格证明平方归一不是导数界、强紧性或二次读出极限交换的替代品。若希望内生分辨率无限提升后仍保留同一物理读出，就必须控制集中，以及实际所用算符、相关函数和状态的收敛方式。

**白话图景。**一份总量为一的内容，可以越挤越窄、越挤越高。每层平方总账都正确，最后却集中成一个点。因此把无穷层放到一起时，要问的不只是每层有没有归一，还要问内容是否躲进越来越小的尺度，以及取极限后读数是否仍然相容。

<a id="section-13"></a>

## 13. 从内部正核到场：反射比较与物理谱的接口

本项目已经用正关系核构造 Hilbert 载体。在欧氏量子场语言中，一个相近但前件更具体的入口是：对正欧氏时间支持的试验观察量 $F,G$，考虑

$$
K(F,G)=S((\Theta F)G),
$$

其中 $S$ 是候选欧氏相关泛函，$\Theta$ 含时间反射与复共轭。若全部有限组合满足反射正性 $K\ge0$，同样可以把零范数方向商掉并完备化，得到 Hilbert 空间。这一步就是共同正核的商空间证明。

从这里继续得到可控的时间平移、正 Hamiltonian、局部性、相对论协变性以及非平凡连续与无限体积极限，还需要相应的欧氏公理和解析估计。Clay 原题明确采用足够强的场论公理性质，不能只交付一个任意正核 [15](#ref-clayym)。本稿不将一般有限 Gram 正性改名为已经完成的 Osterwalder–Schrader 重构。

这里也必须区分普通向量和分布。连续场通常不是可在每一点随意相乘的有界矩阵；本轮有限定理适用于有限切口及已声明的有界读出。将它用于场，需要先规定局部有界观察量，或适当平滑、正则化及共同定义域。诸如 $\varphi(x)^2$ 的复合场与 delta 分布的平方，不能仅凭形式上的平方写法直接使用。胶子结果也须在分布配对和波包框架中构成振幅后，再讨论物理概率 [16](#ref-gluon)。

**白话图景。**有限比较表能造出态空间，场论还要让不同时间、不同位置、不同尺度的比较表接得起来。反射正性提供一种特别适合接时间方向的正核；把每层表拼成真正的连续场，还得证明拼接和极限可靠。

<a id="section-14"></a>

## 14. 质量间隙的二元关系形式：一致指数衰减

为把“有质量隙”落实到二元关系，先假定已经有 Hilbert 空间 $\mathcal H$、自伴物理 Hamiltonian $H\ge0$，以及唯一归一真空 $\Omega_{\rm vac}$，满足

$$
\ker H=\mathbb C\Omega_{\rm vac},\qquad P_0=|\Omega_{\rm vac}\rangle\langle\Omega_{\rm vac}|.
$$

这里真空向量与项目中表示整体和相对锚的 $\Omega$ 分开。采用 $\hbar=c=1$，$\tau$ 为欧氏时间。对有界观察量 $A$，定义中心化向量

$$
u_A=(A-\langle\Omega_{\rm vac},A\Omega_{\rm vac}\rangle I)\Omega_{\rm vac}\in\Omega_{\rm vac}^\perp,
$$

及二元相关核

$$
K_\tau(A,B)=\langle\nu_A,e^{-\tau H}\nu_B\rangle,\qquad\tau\ge0.
$$

它是向量 $e^{-\tau H/2}\nu_A$ 的 Gram 核，仍使用正二次关系语言。

### 定理 14.1（谱隙与中心化二元比较的一致衰减）

给定 $\Delta>0$，下列三项等价：

1. $H$ 在 $\Omega_{\rm vac}^\perp$ 上的谱包含于 $[\Delta,\infty)$。
2. 对全部 $u,v\in\Omega_{\rm vac}^\perp$ 及 $\tau\ge0$，
   $$|\langle u,e^{-\tau H}v\rangle|\le e^{-\Delta\tau}\|u\|\|v\|.$$
3. 对一个在 $\Omega_{\rm vac}^\perp$ 中稠密的线性子空间 $\mathcal D$，全部 $u\in\mathcal D$、$\tau\ge0$ 都满足
   $$\langle u,e^{-\tau H}u\rangle\le e^{-\Delta\tau}\|u\|^2.$$

**证明。**第一项经谱定理给 $\|e^{-\tau H}|_{\Omega_{\rm vac}^\perp}\|\le e^{-\Delta\tau}$，Cauchy–Schwarz 给第二项，第二项给第三项。固定 $\tau$ 时算子有界，第三项由稠密性延续到全部正交补。若第一项不成立，则某个 $0<\delta<\Delta$ 的谱投影 $1_{(0,\delta)}(H)$ 非零，取其中单位向量 $u$；谱定理给 $\langle u,e^{-\tau H}u\rangle\ge e^{-\delta\tau}>e^{-\Delta\tau}$，矛盾。

若实际局部观察代数作用于真空的向量张成稠密空间，则中心化观察量的线性组合可作为 $\mathcal D$。只检查一小组基向量而不检查它们的组合，不能替代定理中的全部量词。在给定正质量隙时，归一向量相关绝对值不超过 $\varepsilon$ 的充分条件为 $\tau\ge\Delta^{-1}\log(1/\varepsilon)$；这是有限精度结论，不保证有限时间严格归零。

该定理证明欧氏时间方向的统一衰减。要进一步得到空间聚类与完整相对论场的质量解释，还要使用局部性、协变性等结构。物理 $H$ 的质量隙 $\Delta$ 与前节比较超算子 $L$ 的间隙 $\gamma$ 不是同一个量；除非模型另外给出具体对应，不能互换名称或单位。

**白话图景。**质量隙可以改写成一句关于关系的话：去掉真空共同背景后，所有归一比较都以一个共同的最慢速度衰减，不能总有更慢激发从下一层冒出来。因此它能放回“关系与关系怎样变化”的语言中；但具体场仍须证明共同正速度存在。

### 命题 14.2（全部量子平方规则成立，仍可没有质量隙）

存在具有唯一真空的正 Hamiltonian，满足通常 Hilbert 与 Born 结构，却没有任何 $\Delta>0$ 使上述统一界成立。

**证明。**在正交归一基 $e_0,e_1,\ldots$ 上定义有界自伴算符

$$
He_0=0,\qquad He_n=\frac1n e_n\quad(n\ge1).
$$

其零特征空间只有 $\mathbb Ce_0$，但非零能量趋于零。取 $A_n=|e_n\rangle\langle e_0|+|e_0\rangle\langle e_n|$，则 $\|A_n\|=1$、$\nu_{A_n}=e_n$，且

$$
K_\tau(A_n,A_n)=e^{-\tau/n},\qquad\sup_{n\ge1}K_\tau(A_n,A_n)=1\quad(\tau<\infty).
$$

对每个固定 $n$ 相关随 $\tau\to\infty$ 消失；对全部 $n$ 没有一致衰减。这个反例精准删除从平方相容到统一场间隙的未经证明步骤，不是 Yang–Mills 模型或其反例。

### 通向 Yang–Mills 的明确剩余命题

假定格点场近似给出自伴 $H_{a,V}\ge0$，且 $\ker H_{a,V}=\mathbb C\Omega_{a,V}$，正转移算子 $T_{a,V}=e^{-aH_{a,V}}$ 唯一真空特征值归一为一。令

$$
\lambda_{\rm exc}(a,V)=\|T_{a,V}|_{\Omega_{a,V}^\perp}\|,qquad
\Delta_{a,V}=-\frac1a\log\lambda_{\rm exc}(a,V).
$$

把有限层正隙送入连续、无限体积场，一条明确充分路线是在所选极限族内建立

$$
\Delta_{a,V}\ge\Delta_0>0
$$

的统一下界，并证明其由非平凡极限理论继承。每层正性和平方归一至多约束谱不越过一，不会自动将激发谱一致推离一；本轮没有把统一下界宣布为第二个新公理或已证结论。弱极限中低能方向还可能沿变化索引逃逸，因此统一下界是有力保证而非所有收敛方案的必要公理 [14](#ref-ymcommittee)。

**白话图景。**有限层每张比较表都合法，并不保证把网格缩到零、把空间放到无穷后仍留有同一段能量空隙。下一道真正的证明任务，是不让越来越细、越来越大的关系系统不断产生越来越慢的方向。它已经能写成明确的二元相关不等式，这让问题可检验，也让尚未完成的部分准确显露。

<a id="section-15"></a>

## 15. 把本轮候选放进一门完整的关系量子理论

现在可以把已有量子重构与本轮新增约束写成同一个有限模型。下述定义整理各版已经声明的结构；其中只有 $C_{89}$ 是本轮新增的相容条件。它检验一次给定操作是否完整保留指定二元比较所生成的关系，不要求一切测量、噪声或粗化都成为无损操作 [1](#ref-v67)、[3](#ref-v79)、[5](#ref-atlas)、[6](#ref-v88)。

### 定义 15.1（有限相容平方闭合关系模型）

在一个有限切口上，模型包括以下继承数据：共同复正核及其有限秩载体；同一事件的正二次权重与完整菜单；声明的准备、相干操作、复合接口和记录仪器。这些数据分别满足既有合同，实际可调用的子菜单与参数范围另外明确标记。

对给定的含单位完全正映射 $\Phi:M_d(\mathbb C)\to M_k(\mathbb C)$，定义

$$
\mathfrak D_{89}(\Phi)=\{(A,B)\in\operatorname{Herm}(d)^2:\Phi(A^2)=\Phi(A)^2,\ \Phi(B^2)=\Phi(B)^2\}.
$$

模型把且仅把属于此集的二元比较标为在该操作下相容平方闭合。这就是前文唯一候选 $C_{89}$ 的模型接口；$\Phi$ 是否保持某个忠实态不是定义的额外前提。若用目标载体上的忠实内部参照 $\eta>0$ 认证，则同一个非负标量证书

$$
s_\eta(A,B)=\operatorname{tr}\!\left(\eta[\Delta_\Phi(A)+\Delta_\Phi(B)]\right)=0
$$

与成员资格等价。

| 量子结构 | 已声明的关系前件 | 推出的表示或规则 |
|---|---|---|
| 复 Hilbert 载体 | 共同复核、全部有限 Gram 正性、声明张成 | 零范数商；有限秩给有限维态空间 |
| Born 读数 | V67 的细化标定，或 V79 的二元反向相容及共同相位锚；实际概率合同 | $w_e(x)=\langle x,E_ex\rangle$，$\sum_eE_e=I$；归一后给概率 |
| 酉与运动方程 | 全复核保持、可逆且输出张成；光滑内部时钟与相位提升 | 共同酉 $U(t)$，$H=i\hbar\dot U U^\dagger$，Schrödinger 方程 |
| 复合与纠缠 | 独立准备的积核，产品准备张成声明的复合载体 | 张量积表示；一般复合态不必为乘积态 |
| 仪器与通道 | 完整记录等距、实际准备记录及完整结果集 | Kraus 分支；忽略记录给完全正保迹通道 |
| 不确定性 | 同一准备上两个偏差关系的 Gram 正性 | 方差、对称协方差和交换子均值的约束 |
| 本轮关系闭合 | 给定含单位完全正 $\Phi$，二元组满足 $C_{89}$ | 对 $C^*(I,A,B)$ 的全部关系词保持乘法与伴随；忠实性另有精确条件 |

### 命题 15.2（继承重构的有限证明链）

上表各项均在所列前件内成立。$C_{89}$ 新增最后一行的有限认证接口，不独立承担此前各行的前件。

**证明。**共同核 $K$ 在形式组合上定义

$$
\left\langle\sum_i c_i[x_i],\sum_jd_j[y_j]\right\rangle
=\sum_{ij}\overline c_i d_jK(x_i,y_j).
$$

Gram 正性与 Cauchy–Schwarz 使零范数方向正交于全部方向，商空间有正定内积；有限秩给有限维载体。保持全部核的标签变换保持每个零线性关系，所以良定义为线性等距；输出张成使其为酉。微分 $UU^\dagger=I$ 即得 $H=i\hbar\dot U U^\dagger=H^\dagger$ 和 Schrödinger 方程。

读出复用 V67、V79 已证的标定和二次表示。对 $x\ne0$，

$$
p_e(x)=\frac{\langle x,E_ex\rangle}{\langle x,x\rangle},\qquad
\rho=\sum_jq_j|\psi_j\rangle\langle\psi_j|\Longrightarrow p_e(\rho)=\operatorname{tr}(\rho E_e).
$$

这里 $q_j\ge0$、$\sum_jq_j=1$，使用实际经典混合的可加读数合同；同一 $\rho$ 的不同准备分解给同一式，但全部密度矩阵的数学表示不等于全部准备或效果都可执行。

产品核使 $[x,y]\mapsto[x]\otimes[y]$ 保持全部 Gram；两侧声明张成时为酉同构。完整记录等距写成 $V\psi=\sum_eM_e\psi\otimes|e\rangle$，给 $\sum_eM_e^\dagger M_e=I$，偏迹给

$$
\Lambda(\rho)=\sum_eM_e\rho M_e^\dagger.
$$

若结果 $e$ 已实际记录且 $p_e=\operatorname{tr}(M_e\rho M_e^\dagger)>0$，条件态为

$$
\rho_e=\frac{M_e\rho M_e^\dagger}{p_e}.
$$

粗结果若包含多个未区分记录分量，分子须对相应 Kraus 分量求和；理想投影仪器取 $M_e=P_e$ 得 Lüders 更新。仅知道效果 $E_e=M_e^\dagger M_e$ 的概率，还不能唯一决定实际仪器及更新。

最后取 Hilbert–Schmidt 向量 $u=\delta A\sqrt\rho$、$v=\delta B\sqrt\rho$，二阶 Gram 正性给

$$
\operatorname{Var}_\rho(A)\operatorname{Var}_\rho(B)\ge\left|\operatorname{tr}(\rho\,\delta A\,\delta B)\right|^2.
$$

右端实部是对称协方差，虚部是交换子均值除以 $2i$。这些证明与 $C_{89}$ 的乘法域证明接合，形成完整依赖链。

**白话图景。**共同内容之间有一致的比较表，态空间就是把这张表实现出来。保住全部比较的共同变化给出量子门；结果怎样分份给出概率；把结果存进内部记录给出测量。本轮再加一个具体判断：两项比较经过一次操作后，它们的平方差额是否都为零？若是，这两项接成再长的关系词，也不需要另补一套组合规则。

<a id="section-16"></a>

## 16. 闭合保持了什么，后续操作又要求什么

令 $\mathcal A=C^*(I,A,B)$，并记前文所得 $\pi=\Phi|_{\mathcal A}$。$C_{89}$ 给出

$$
\pi(XY)=\pi(X)\pi(Y),\qquad \pi(X^\dagger)=\pi(X)^\dagger,qquad X,Y\in\mathcal A.
$$

这保持关系的组合结构，但尚不保证不同内容都能在目标接口区分。

### 命题 16.1（忠实保留的准确条件）

设 $\eta$ 是目标载体上的态，令 $\rho=\Phi_*(\eta)$，即 $\operatorname{tr}(\rho X)=\operatorname{tr}(\eta\Phi(X))$。若 $\rho$ 在 $\mathcal A$ 上忠实，则 $\pi$ 单射。若 $\eta>0$，反向也成立。因此使用忠实 $\eta$ 时，单射性恰好等价于拉回态在被保留代数上的忠实性。

**证明。**若 $\pi(X)=0$，则

$$
\operatorname{tr}(\rho X^\dagger X)=\operatorname{tr}(\eta\pi(X)^\dagger\pi(X))=0,
$$

输入忠实性给 $X=0$。反过来，若 $0\ne X\in\mathcal A$，单射性给 $\pi(X)^\dagger\pi(X)\ne0$，目标忠实性使其期望为正。

这里的拉回态可能不忠实；不能因为认证参照 $\eta$ 忠实就省略条件。在 v88 的保忠实态条件期望 $E$ 特例中，$C_{89}$ 等价于两生成元已在可见代数内；一般动力学中，保同一忠实态是前文不动关系与平均粗化定理的条件，不应倒写成本轮基本候选的前提 [6](#ref-v88)。

**代数关系词与实际未来菜单须分别声明。**$\mathcal A$ 包含的乘积、线性组合及谱投影，是可核对的数学关系；它们成为实际准备、读出或控制，需要相应原生供应。若实际读出只张成一个含单位实空间 $\mathcal W$，所有未来词可见性的判据沿用 Heisenberg 线性闭包。只有已声明整个 $\mathcal A$ 效果接口时，才能直接使用 $F(\mathcal A)\subseteq\mathcal A$ 的全态自治判据；保留结果的仪器则必须逐分支满足 $F_e(\mathcal A)\subseteq\mathcal A$，包括失败分支 [4](#ref-foundations)、[5](#ref-atlas)。

因而，某一 $\Phi$ 上的 $C_{89}$ 不能认证其他未声明操作，也不自动给出多步经典 Markov 律。同一初态和同一步概率可以对应不同未测量历史；实际测得路径还依赖中间仪器、保留标签及控制记忆条件 [6](#ref-record)。

**白话图景。**一本关系账内部可以已经完全对得上，但不表示每页都已做成仪器按钮。同样，两个内容经过操作后遵守同一套乘法，也可能被一起压成同一个内容；忠实条件正是检查有没有把非零区别整个漏掉。真正停止搜索，还要确认以后允许问的问题都在这本账能接续回答的范围内。

<a id="section-17"></a>

## 17. 完整白话图景与统一关系场的范围

这一轮得到的是一个有限、可组合的关系量子模型及其闭合认证。状态、效果、操作、记录和分辨率可以都由整体内部的数据与接口描述；不同对象仍保留自己的类型、尺度和实际操作条件。平方读出把相干幅度变成归一概率；操作平方缺陷判定关系组合有没有被额外扰动；二元结果的 $p(1-p)$ 描述给定准备上的结果不确定性。三者彼此接合，但不是同一个平方。

若另有内部参数域、局部载体和相容输运，这套结构可接到连接及曲率语言。本轮没有由 $C_{89}$ 选择唯一时空、规范群、作用量或耦合常数，没有推出四种基本相互作用，也没有建立四维连续 Yang–Mills 理论及其正质量隙。这些结论需要各自明确的动力学与解析前提，不能由有限关系词闭合替代。

**白话图景。**完整地画出来：整体中的一段内容通过内部操作成为另一段内容；两段内容相互比较，比较又可以成为下一次操作的对象。相干相加留下方向和相位，平方读出把它们变成一组总量为一的结果概率。当指定两项比较的操作平方差额都消失，它们连成的整套关系就已相容，不必为每一个更长的词重新开一个缺口。但这张稳定关系表仍可以给出一半对一半的结果；稳定的是规则，不是每次结果都提前确定。如果以后换了读口、加入新的伙伴或扩大实际菜单，就按同样的内部比较继续检查。这使“关系的关系”成为一门可以接续推导的理论，而不是把尚未给出的现实动力学藏进一个名字。

<a id="references"></a>

## 来源、版本与核读范围

<a id="ref-v67"></a>

1. trureturing 项目，V67：历史脚本、内容寻址与同一整体中的量子纠缠。固定提交原文，核读 §9.3、定理 9.5 的全实细化与平方权重证明。
<a id="ref-v78"></a>

2. trureturing 项目，V78 continuation：内生闭合、有限根证书与结果核递归。固定提交原文，沿用有限结果树、实际记录和闭合范围的既有区分。
<a id="ref-v79"></a>

3. trureturing 项目，V79：二元反向相容、有限相位证书与量子读出重构。固定提交原文，核读 §§2–5 与 §9.1。
<a id="ref-foundations"></a>

4. trureturing 项目，*ContextualSpacetimeQuantum: Foundations and Records*。固定提交原文，核读 §4 的有限未来观察闭包、§8.4 的 Schur 不动代数、§§11.2–11.3 的精确稳定条件。
<a id="ref-atlas"></a>

5. trureturing 项目，*Quantum Origin: Endogenous Cut Atlas and Discrete Reconstruction Boundaries III*。固定提交原文，核读 §§12–13 的 Heisenberg 自治与逐仪器分支闭合。
<a id="ref-record"></a>

6. trureturing 项目，*Recursive Relational Observation: Minimal Record Dilations*。固定提交原文，核读 §5：一步概率、实际中间记录与多步路径律不能混同。
<a id="ref-v88"></a>

7. 本对话研究稿，*AURIC v88: Recursive Spheres and Relative Resolution Fields*，2026。沿用双向有序相容、保忠实态条件期望、条件方差及分辨率塔；本轮不是它们的重新发现。
<a id="ref-choi"></a>

8. M.-D. Choi， “A Schwarz inequality for positive linear maps on $C^*$-algebras,” *Illinois Journal of Mathematics* 18(4), 565–574 (1974)，https://doi.org/10.1215/ijm/1256051007。为平方等式与乘法相容的经典来源。
<a id="ref-mdqec"></a>

9. M.-D. Choi, N. Johnston and D. W. Kribs， “The Multiplicative Domain in Quantum Error Correction,” *Journal of Physics A* 42, 245303 (2009)，https://arxiv.org/html/0811.0947v1，https://doi.org/10.1088/1751-8113/42/24/245303。正文给出完整有限证明。
<a id="ref-nsannouncement"></a>

10. OpenAI， “A solution to the Navier–Stokes Millennium Prize Problem,” 2026-09-08，https://openai.com/index/navier-stokes-solution/。公告层级与实际定理范围分开核查。
<a id="ref-nspaper"></a>

11. OpenAI，*Finite Time Blowup for Navier–Stokes*，2026，公开稿 166 页，https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf。核读摘要、定理 1.1、引言及相关物理说明；没有独立复核全部证明或运行 Lean。
<a id="ref-clayns"></a>

12. Clay Mathematics Institute， “Navier–Stokes Announcement,” 2026-09-11，https://www.claymath.org/news/navier-stokes-announcement/。
<a id="ref-openai1026"></a>

13. OpenAI， “Working with academic communities to build scientific understanding,” 2026-10-26，https://openai.com/index/building-scientific-understanding-with-academic-communities/。核读 QCD／Yang–Mills 存在性与 ETH 两节，不据此假定未公开证明已被本稿验证。
<a id="ref-ymcommittee"></a>

14. M. R. Douglas, D. J. Gross, A. Jaffe, I. R. Klebanov and N. Nekrasov，*Proof by OpenAI of the Existence of Quantum Yang–Mills Theory*，October 2026，https://www.kitp.ucsb.edu/sites/default/files/YM_working_group.pdf。核读存在性材料发布与审核安排、证明尚待公开，以及质量隙与禁闭仍开放的边界。
<a id="ref-clayym"></a>

15. A. Jaffe and E. Witten，*Quantum Yang–Mills Theory*，Clay Millennium problem description，https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf。核读场公理、反射正性、存在性及正质量隙要求。
<a id="ref-gluon"></a>

16. *Single-minus gluon tree amplitudes are nonzero*，arXiv:2602.12176，首稿 2026-02-12，核读 v2（2026-03-09），https://arxiv.org/html/2602.12176v2。核读 Klein 半共线范围、分布支撑、特殊区域闭式与递归证明。
<a id="ref-deepmindfluids"></a>

17. *Discovery of Unstable Singularities*，arXiv:2509.14185，2025-09-17，https://arxiv.org/html/2509.14185v1。核读 PINN／Gauss–Newton 方法、CCF／IPM／Boussinesq 结果和残差验证范围。
<a id="ref-alphaevolve"></a>

18. *Mathematical exploration and discovery at scale*，arXiv:2511.02864，公开 v3，https://arxiv.org/html/2511.02864v3。核读 67 问题框架及 §6.2 的自卷积上界见证；本文数字限定于所核版本。
<a id="ref-ethscope"></a>

19. OpenAI Math repository，Lean statement document `lean/docs/378.md`，2026，https://github.com/openai/math/blob/main/lean/docs/378.md。用于核对固定宽度精确计数的次指数范围，不宣称由此得到 $\mathrm P=\mathrm{NP}$。

**版本与操作记录。**v89 是对话研究稿的递增版本。仓库引用固定在正文给出的提交，近期研究使用截至 2026 年 11 月 3 日已取得的公开原始资料；尚未公开的证明不在本轮核读范围。数学部分均为书面解析证明与反例，未运行数学代码、CAS、数值实验、候选枚举或测试。文件编译及版面检查仅用于生成与核验本文。
