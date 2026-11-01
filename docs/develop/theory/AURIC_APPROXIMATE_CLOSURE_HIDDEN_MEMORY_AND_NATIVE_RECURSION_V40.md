# AURIC：近似闭合与隐藏记忆

# 原生递归的定量边界

**定义、定理与纸面证明　v40.0**

2026 年 10 月 31 日　Asia/Singapore

<!-- editorial-start:metadata -->
> **转写元数据与归属（编者说明）**  
> PDF 标题：AURIC：近似闭合、隐藏记忆与原生递归。  
> PDF 作者：AURIC research continuation。  
> PDF 主题：Approximate closure, exact memory kernels and native finite-cycle witnesses。  
> 原编译提示：XeLaTeX，编译两次；`AURICFontPath` 可指向 Noto CJK OTF 目录。  
> 原页眉：AURIC：近似闭合、隐藏记忆与原生递归；v40 / 2026-10-31。原页脚为页码。  
> 源稿 SHA-256：<code>3f46603e<wbr>4b150e33<wbr>c8c96dff<wbr>cf299e98<wbr>b8dc4ec8<wbr>93e47b13<wbr>8f1a8d03<wbr>cc180cb8</code>。  
> 下文保留作者原稿的全部陈述与纸面证明，节内各类陈述的共享编号显式展开；无编号展示式不另编号。原文的“本轮”、文件与下载数量、来源读取、复用、未运行 Lean 或数学程序、未修改或提交仓库等均是原作者撰稿时的历史自述，不是本次转写工作的现况报告，也不构成内核认证。正文的数学、原生准备权限与统计取得前提仍分别承担其各自范围。
<!-- editorial-end:metadata -->

## 摘要

承接 v39 的精确未来闭合，本稿分析暂时省略的关系怎样返回。
首先区分已知聚合质量轨迹的酉编码、同一系统酉的全输入实现、以及带内部记录的共同通道；
给三模式质量转移的二 Kraus 实现及精确历史保留成本。
对任意有限维酉共轭的可见压缩，推导完整隐藏记忆核；
对长度 $L$ 的近似闭合字，得到已有隐藏误差的一阶累计与可见初值返回的二阶交叉累计，
两种阶均由解析旋转例达到。
利用固定黄金菜单的射影密度，证明任何非平凡真子空间都有正的共同泄漏间隙；
再利用每个原始门的十次复原，得到十步即可见证无记忆压缩误差的正下界。
通过原生纯态轨道稠密和读数 Gram 矩阵，把存在性结论转成实际有限准备字的上确界见证，
但不提供免费字搜索或统计取得。
另给有限周期局部通道的近似可逆性界，以及黄金十设置的精确加权条件数。
所有对象均是同一静态整体内部角色；只作纸面数学与源码读取，不运行数学程序或 Lean。

<a id="section-1"></a>

## 1　本轮来源、前提与真正的增量

本轮固定提交为

<code>30933a24<wbr>a13489f1<wbr>27757b99<wbr>e12796ff<wbr>09ebeafb</code>，

 提交标记时间为 2026-10-31 06:16:06（新加坡）。
比较基线是 v39 的

<code>18ab1784<wbr>72d8c29e<wbr>b90d5e5f<wbr>4e6c8b4c<wbr>89038e84</code>。

完整 theory 与 D5 子树分别有 1086、11661 个文件，未截断；
差异为五个理论文件和一个新增 D5 文件。
续卷 II、原黄金门、V37、Datko 模块均未变化。来源身份核对不等于证明核验。[[1](#bib-head)]

<!-- editorial-start:historical -->
> **历史归属（编者说明）** 此处的两完整子树、文件差异和未变化判断均归属于作者所列固定提交与比较基线；并非对当前工作树的计数或变更判断。
<!-- editorial-end:historical -->

本轮直接相关的新来源有三项。

1. 新三项非负预算稿 §4 给固定实际整数的余量
   $E_h\le2^{-h}E_0$，并以模式 $(2,5,3)$ 的三振幅和随 $h$ 指定的旋转实现。
   它保留聚合质量；逐素数逐层历史另需记录。
   该文是作者稿导入及编辑补充，连续旋转不是新增原生控制。
   本稿不消费其中另标为未定位的匹配终点前提，也不借其三模式编码证明 RH。[[2](#bib-budgets)]
2. FIB 关系 VIII 新 §10 对 $d\ge6$、$\varepsilon>0$，在完整正秩域的
   逐种子路径可靠性、奇异动作、单条不可复位轨迹及种子盲公共因果误差下，
   证明指定一参数秩二族上的私有随机认证操作最坏值为 $1/2$。
   将量词改为每个种子抵抗全部误差，最坏值为零（另须事件可测）。
   这些来源与读口权限不移入本稿量子菜单。[[3](#bib-ranknoise)]
3. 最小预测核桥新 §27 给十四事件安装的严格界
   $C=N-4<N-3\le Q_1\le Q_0\le N$，
   其中 $Q_1$ 限于累计新增集、当前读数和最后事件的因子。
   它说明一种具体短历史摘要未必最优；没有宣称任意有限记忆层级都已分类。[[4](#bib-mpc)]

本文量子结论继续明确消费复 Hilbert 载体、实际原生菜单、所声明输入域，
以及使用线性效果或通道时的 Born/CP 校准。
内部参考、程序、记录及其取得成本保留在同一 $(\mathcal A,\omega)$ 中。
Hilbert–Schmidt 投影只作关系坐标压缩，未被当作免费物理测量、复位或 CP 通道。
v38 已证明：固定有限维联合酉、同一初始内部记录，不能对所有系统输入和全部幂次数
同时精确实现严格收缩半群；
本轮的新消费者是*精确记忆核、有限误差预算、固定原生间隙与十步见证*。

<a id="section-2"></a>

## 2　聚合余量的酉编码与共同过程

在原五模式 $(N,2,3,5,25)$ 中，只考虑明确选定的
$\mathcal H_3=\operatorname{span}\{\lvert2\rangle,\lvert5\rangle,\lvert3\rangle\}$。
按 $(2,5,3)$ 顺序写占据概率 $(X,Y,Z)$；模式 $N,25$ 的质量为零。
这是来源三项预算所用子空间；若允许模式 $25$，原读数会有额外共同贡献，
下面的占据概率更新不能原样扩大。[[2](#bib-budgets), [8](#bib-v37)]
源实际余量的逐步比率为 $\beta_h=E_{h+1}/E_h\in(0,1/2]$；
以下固定 $\beta$ 用来研究同一个共同过程，并未断言源余量有恒定比率。

<a id="definition-2.1"></a>

#### 定义 2.1（聚合纯态族与目标）

固定 $0<a\le1$、$0<\beta<1$，置

$$
v_y=\sqrt{a-y}\lvert2\rangle+\sqrt y\lvert5\rangle+\sqrt{1-a}\lvert3\rangle,
\qquad 0\le y\le a.
$$

目标占据概率转移为

$$
(a-y,y,1-a)\longmapsto(a-\beta y,\beta y,1-a).
$$

<a id="thm:commonunitary"></a>

#### 定理 2.2（逐态旋转存在；共同系统酉不可能）

对每个固定 $y$，存在 $\mathcal H_3$ 上的酉将 $v_y$ 送到 $v_{\beta y}$。
但不存在同一个酉 $U$，对全部 $y\in[0,a]$ 满足
$Uv_y=e^{i\theta_y}v_{\beta y}$。

<a id="proof-1"></a>

**证明。** 
两单位向量分别补全正交基即给逐态酉。
若有共同酉，$v_0$ 的射线必须固定，因而内积模保持。
然而对 $y>0$，

$$
|\langle v_0,v_y\rangle|
=\sqrt a\sqrt{a-y}+1-a
<\sqrt a\sqrt{a-\beta y}+1-a
=|\langle v_0,v_{\beta y}\rangle|.
$$

与酉保内积矛盾，任意整体相位也不能修复。
 ∎

源稿固定整数后指定的 $R(\theta_{h+1}-\theta_h)$ 仍完全合法；
本定理只排除把其量词改成同一个系统酉处理全部未知余量。
归一化保持单位长度，没有自动保持不同输入间的关系。
若仅要求上述占据概率转移，但要求对 $\mathcal H_3$ 的全部密度矩阵成立，
同一个系统酉也不可能：$I_3/3$ 在任何酉下不变，
目标占据概率却为 $((2-\beta)/3,\beta/3,1/3)$。

<a id="thm:population"></a>

#### 定理 2.3（共同占据概率转移的内部记录实现）

定义

$$
A_0=\operatorname{diag}(1,\sqrt\beta,1),\qquad
A_1=\sqrt{1-\beta}\lvert2\rangle\langle5\rvert,
\qquad
\Phi_\beta(\rho)=A_0\rho A_0^*+A_1\rho A_1^*.
$$

则 $\Phi_\beta$ 是 CPTP，且对 $\mathcal H_3$ 上每个密度矩阵精确满足

$$
\boxed{(X,Y,Z)\mapsto(X+(1-\beta)Y,\beta Y,Z).}
$$

其相干内部等距为

$$
V_\beta\psi=A_0\psi\otimes\lvert0\rangle+A_1\psi\otimes\lvert1\rangle.
$$

该等距可在声明的更大同一内部载体上补成酉。
若输入为 $v_y$ 且 $y>0$，系统输出秩为二，并有

$$
\operatorname{Tr}\!\left[\Phi_\beta(|v_y\rangle\langle v_y|)^2\right]
=1-2(1-\beta)y\bigl((1-a)+\beta y\bigr)<1.
$$

<a id="proof-2"></a>

**证明。** 
$A_0^*A_0+A_1^*A_1=I$，直接给保迹、完全正及 $V_\beta^*V_\beta=I$。
对角项逐项给占据概率公式。
两个未归一输出向量为

$$
u_0=\sqrt{a-y}\lvert2\rangle+\sqrt{\beta y}\lvert5\rangle+\sqrt{1-a}\lvert3\rangle,
\quad u_1=\sqrt{(1-\beta)y}\lvert2\rangle.
$$

当 $y>0$ 时二者非零且线性独立；
使用 $\operatorname{Tr}(\sum_i|u_i\rangle\langle u_i|)^2=\sum_{i,j}|\langle u_i,u_j\rangle|^2$
得到纯度式。酉补全是有限维正交基补全，不供应原生编译或准备权限。
 ∎

共同通道和相干记录的标准表示可参见 Watrous；这里的具体消费者已逐式证明。[[10](#bib-watrous5)]
三模式中 $\operatorname{span}\{\lvert2\rangle,\lvert3\rangle\}$ 被逐点保持，
因此全部态对的迹距离收缩系数为一。
余量占据概率的 $Y_n=\beta^nY_0$ 不等于整个状态空间严格收缩。
只限制到 $(2,5)$ 二模式时，Bloch 差更新为
$\operatorname{diag}(\sqrt\beta,\sqrt\beta,\beta)$，系数才为 $\sqrt\beta<1$。

<a id="proposition-2.4"></a>

#### 命题 2.4（最终通道与完整首次转移档案）

令整数 $n\ge1$。若每轮实际供应按所列等距使用、处于 $\lvert0\rangle$ 的新纯 ready 记录，
$n$ 轮后的余量占据概率为 $\beta^nY_0$。
只实现最终通道 $\Phi_\beta^n$，两个 Kraus 算子

$$
\operatorname{diag}(1,\beta^{n/2},1),\qquad
\sqrt{1-\beta^n}\lvert2\rangle\langle5\rvert
$$

已足够；其最小纯 ready 扩张记录维数为二。
若要求记录寄存器本身无误区分并保留“尚未转移”及首次转移于 $1,\ldots,n$ 的全部历史，
该记录维数至少 $n+1$。

<a id="proof-3"></a>

**证明。** 
占据概率与相干项递推直接给所列两算子；它们线性独立，所以 Choi 秩为二。
对初态 $\lvert5\rangle$，上述 $n+1$ 条历史的概率分别是

$$
\beta^n,\qquad (1-\beta)\beta^{j-1}\quad(1\le j\le n),
$$

全部严格正。寄存器本身完美区别它们要求 $n+1$ 个非零正交支持，故给下界。
该下界不适用于仅生成最终粗粒化结果，或仅用 POVM 给出同数目的标签。
 ∎

相反，若反复使用同一个未复位的二记录酉扩张，
在 $\operatorname{span}\{\lvert5,0\rangle,\lvert2,1\rangle\}$ 上取角 $\theta$ 的旋转且
$\cos\theta=\sqrt\beta$，则从 $\lvert5,0\rangle$ 出发的余量是
$\cos^2(n\theta)$，会相干返回，不是 $\beta^n$。
这只是已声明的数学扩张例，不增加任意角度的原生调用。

<a id="section-3"></a>

## 3　省略的关系返回为精确记忆核

<a id="definition-3.1"></a>

#### 定义 3.1（可见压缩与分块）

令 $\mathcal W$ 是有限维实内积空间；量子消费者取
$\mathcal W=\operatorname{Herm}_0(\mathcal H_D)$、内积 $\operatorname{Tr}(XY)$。
取正交投影 $P$，$V=\operatorname{ran}P$，$Q=I-P$。
对正交变换 $\mathcal U$（量子消费者为 $X\mapsto KXK^*$）定义

$$
A=P\mathcal U P|_V,\quad B=P\mathcal U Q,\quad
C=Q\mathcal U P,\quad D_0=Q\mathcal U Q|_{Q\mathcal W}.
$$

对 $x_n=\mathcal U^nx_0$，记 $v_n=Px_n$、$z_n=Qx_n$。

<a id="thm:kernel"></a>

#### 定理 3.2（完整离散记忆方程）

每个 $n\ge0$ 都有

$$
\boxed{
v_{n+1}=Av_n+BD_0^nz_0+
\sum_{k=0}^{n-1}BD_0^kC\,v_{n-1-k}.
}
$$

空和为零。$BD_0^kC$ 是从可见关系离开、在隐藏部分停留、再返回的精确系数。

<a id="proof-4"></a>

**证明。** 
分块给 $v_{n+1}=Av_n+Bz_n$、$z_{n+1}=Cv_n+D_0z_n$。
对第二式归纳，

$$
z_n=D_0^nz_0+\sum_{j=0}^{n-1}D_0^{n-1-j}Cv_j.
$$

代入第一式并换指标即得。没有平均、独立噪声、复位或近似。
 ∎

<a id="thm:kernelzero"></a>

#### 定理 3.3（有限记忆核的零性与自治）

设 $h=\dim Q\mathcal W>0$。下列条件等价：

1. $P\mathcal U^nP|_V=A^n$ 对全部 $n\ge0$ 成立；
2. $BD_0^kC=0$ 对全部 $k\ge0$ 成立；
3. $BD_0^kC=0$ 对 $0\le k\le h-1$ 成立；
4. $P\mathcal U^nP|_V=A^n$ 对 $0\le n\le h+1$ 成立；
5. $C=0$，即 $V$ 对 $\mathcal U$ 不变。

此时 $B=0$ 且 $A$ 为 $V$ 上的正交变换。

<a id="proof-5"></a>

**证明。** 
先令 $z_0=0$。记忆方程从 $n=1$ 给第一个返回核 $BC$；
逐阶消去已为零的核，得到第 1、2 项以及第 3、4 项的等价。
Cayley–Hamilton 将 $D_0^h$ 写成较低幂的线性组合，故第 3 项推出第 2 项。

若全部核为零，令
$\mathcal R=\operatorname{span}\{D_0^kCV:k\ge0\}$。
它对 $D_0$ 不变且 $B\mathcal R=0$，所以 $\mathcal U$ 把
$0\oplus\mathcal R$ 等距映入自身。有限维性使其满射。
又 $V\perp\mathcal R$，正交性给 $\mathcal U V\perp\mathcal U\mathcal R=\mathcal R$。
但 $CV\subseteq\mathcal R$，所以 $C=0$。
反向显然；有限维等距 $A$ 满射，故 $V^\perp$ 也不变，得到 $B=0$。
 ∎

若 $h=0$，结论退化为整个空间上的正交演化。
有限维前件不可删：实 $\ell^2(\mathbb Z)$ 上双边移位 $\mathcal Ue_k=e_{k+1}$，
取 $V=\operatorname{span}\{e_0\}$，则 $A=0$、$C\ne0$，
却有 $P\mathcal U^nP=0=A^n$ 对全部 $n\ge1$ 成立。
它仅讨论正向重复这一无限载体菜单，不是原有限黄金载体的新权限。

<a id="section-4"></a>

## 4　近似闭合的误差：能量损失与返回偏差

<a id="definition-4.1"></a>

#### 定义 4.1（逐门泄漏）

对一列正交变换 $\mathcal U_1,\ldots,\mathcal U_L$，
令 $A_j=P\mathcal U_jP|_V$，并记

$$
\ell_j=\|Q\mathcal U_jP\|_{\mathrm{op}},\qquad
s_L=\sum_{j=1}^L\ell_j,\qquad
t_L=\sum_{1\le i<j\le L}\ell_i\ell_j.
$$

所有范数都来自同一个实内积；量子情形是作用于 HS 空间的诱导范数。

<a id="lem:leak"></a>

#### 引理 4.2（单步精确度量缺陷）

每个 $j$ 都有

$$
\|P\mathcal U_jQ\|_{\mathrm{op}}=\ell_j,\qquad
A_j^*A_j=I_V-C_j^*C_j,
\quad C_j=Q\mathcal U_jP.
$$

因而

$$
\|A_jv\|^2=\|v\|^2-\|C_jv\|^2,
\qquad
\|A_L\cdots A_1v\|^2
\ge\prod_j(1-\ell_j^2)\|v\|^2.
$$

压缩链自身的平方范数损失至多 $(\sum_j\ell_j^2)\|v\|^2$。

<a id="proof-6"></a>

**证明。** 
正交分块给 $A_j^*A_j+C_j^*C_j=I_V$ 及
$A_jA_j^*+B_jB_j^*=I_V$。
方阵 $A_j^*A_j$ 与 $A_jA_j^*$ 的特征值相同，故两缺陷的最大特征值相同。
逐步使用最小奇异值下界，并用
$1-\prod_j(1-\ell_j^2)\le\sum_j\ell_j^2$，即得各式。
 ∎

<a id="thm:finiteerror"></a>

#### 定理 4.3（有限字的两种累计预算）

真实演化只在末端投影，预测则在每一步压缩。两者满足

$$
\boxed{
\|P\mathcal U_L\cdots\mathcal U_1x-A_L\cdots A_1Px\|
\le \min(1,s_L)\|Qx\|+\min(2,t_L)\|Px\|.
}
$$

特别地，$\ell_j\le\ell$ 时，已有隐藏初值给 $L\ell$ 阶；
纯可见初值的首次返回给 $L(L-1)\ell^2/2$ 阶。

<a id="proof-7"></a>

**证明。** 
先取 $x\in V$。每步全向量范数等于 $\|x\|$，
隐藏递推及 $\|D_j\|\le1$ 给
$\|z_{j-1}\|\le\sum_{i<j}\ell_i\|x\|$。
可见误差满足
$e_j=A_je_{j-1}+B_jz_{j-1}$，故累计至多 $t_L\|x\|$。
真实投影与压缩乘积各为收缩，另有 $2\|x\|$ 的上界。

再取 $x\in Q\mathcal W$。可见递推从零开始，每步新增量至多
$\ell_j\|x\|$，总计 $s_L\|x\|$；全投影另给 $\|x\|$。
按 $x=Px+Qx$ 分解并用三角不等式，即得结论。
 ∎

<a id="prop:rotation"></a>

#### 命题 4.4（返回偏差的阶与常数锐利）

在一般数学 qubit 菜单中，令 $K=R_y(\theta)=e^{-i\theta\sigma_y/2}$，
取无迹可见空间 $V=\operatorname{span}\{Z\}$。
则 $\ell=|\sin\theta|$，真实可见系数为 $\cos(L\theta)$，
无记忆系数为 $(\cos\theta)^L$。
固定 $L\ge2$，$\theta\to0$ 时

$$
\frac{|\cos(L\theta)-(\cos\theta)^L|}{\ell^2}
\longrightarrow\frac{L(L-1)}2.
$$

隐藏 $X$ 初值的可见系数则为 $\pm\sin(L\theta)$，其绝对值除以 $\ell$ 趋于 $L$。

<a id="proof-8"></a>

**证明。** 
Bloch 共轭在 $X,Z$ 平面是角 $\theta$ 的旋转。
用 $\cos\theta=1-\theta^2/2+O(\theta^4)$ 与
$\sin\theta=\theta+O(\theta^3)$ 的解析展开即得。
这些是纸面极限，没有执行数值计算。
 ∎

更强地，令 $\theta=\pi/(2N)$、$L=N$，则真实系数为零，
但 Bernoulli 不等式给

$$
(\cos\theta)^N\ge1-\frac{\pi^2}{8N}\longrightarrow1.
$$

与此同时 $N\ell^2\to0$。
所以压缩链自身很小的累计能量损失，不能代替它与真实演化之间的误差预算。
这个反例改变了菜单参数；下一节专门证明固定黄金菜单有不同的正间隙。
它还给出一个可求和但不可忽略的记忆核：
在 $0<\theta<\pi/2$ 时，

$$
BD_0^kC=-\sin^2\theta\,(\cos\theta)^k,
\qquad
\sum_{k\ge0}|BD_0^kC|
=\frac{\sin^2\theta}{1-\cos\theta}=1+\cos\theta.
$$

各项随 $k$ 衰减，且首项随 $\theta$ 趋零；全部记忆影响的绝对和却不趋零。
所以“级数收敛”仍需配合其总量、反馈及一致性量词。

<a id="section-5"></a>

## 5　固定黄金菜单的正间隙与十步返回证书

本节使用一个*固定*的完整原生菜单。
续卷 II §77 已将原十三维扇区及七个地址的射影闭包识别为 $PU(13)$；
扩大扇区另有其全部十一地址与 $PU(89)$ 的供应。
闭包只作数学证明，不把极限酉或随机平均加入可执行菜单。[[5](#bib-continuation)]

<a id="definition-5.1"></a>

#### 定义 5.1（固定菜单的对称算符间隙）

令 $D\ge2$、$\mathcal W=\operatorname{Herm}_0(\mathbb C^D)$、$d=D^2-1$，
固定酉 $K_1,\ldots,K_m$ 生成的射影群稠密于 $PU(D)$。
记实正交作用 $R_j(X)=K_jXK_j^*$。
在 $\mathcal W$ 的实对称算符空间上定义

$$
\mathcal T(Z)=\frac1{2m}\sum_{j=1}^m
\bigl(R_jZR_j^*+R_j^*ZR_j\bigr),
$$

并在无迹对称算符子空间 $\operatorname{Sym}_0(\mathcal W)$ 上置

$$
\gamma=\lambda_{\min}\bigl((I-\mathcal T)|_{\operatorname{Sym}_0(\mathcal W)}\bigr).
$$

这里 $Z$ 是作用于整个误差空间的二阶算符；不是一个新的物理密度矩阵。

<a id="lem:gap"></a>

#### 引理 5.2（正间隙存在）

$\gamma>0$。它由固定完整菜单决定；本文不给数值下界或求值程序。

<a id="proof-9"></a>

**证明。** 
先证明 $\mathcal W$ 的共同不变实子空间只有零及自身。
稠密性与有限维闭性把原生不变性延伸为全部酉共轭不变性。
非零无迹 Hermitian 矩阵可酉对角化，且有两个不同特征值。
交换这两个坐标并相减，得到非零倍的 $E_{aa}-E_{bb}$。
再用置换及二坐标的实、复旋转共轭，得到所有对角差、
$E_{ab}+E_{ba}$、$i(E_{ab}-E_{ba})$，实张成整个 $\mathcal W$。

$\mathcal T$ 自伴，且

$$
\langle Z,(I-\mathcal T)Z\rangle_{
\mathrm F}
=\frac1{2m}\sum_j\|Z-R_jZR_j^*\|_{\mathrm F}^2\ge0.
$$

若等于零，$Z$ 与每个 $R_j$ 对易；$Z$ 的每个实特征空间均共同不变，
刚证的不可约性迫使 $Z$ 为标量。其算符迹为零，故 $Z=0$。
有限维单位球紧性使最小 Rayleigh 商严格为正。
 ∎

<a id="thm:nativegap"></a>

#### 定理 5.3（任何真可见子空间的共同泄漏下界）

令 $P$ 是 $\mathcal W$ 上秩 $0<r<d$ 的正交投影、$Q=I-P$。
则

$$
\boxed{
\frac1m\sum_j\|QR_jP\|_{\mathrm F}^2
\ge\gamma\frac{r(d-r)}d.
}
$$

从而

$$
\boxed{
\max_j\|QR_jP\|_{\mathrm{op}}^2
\ge c_r:=\gamma\frac{\max(r,d-r)}d
\ge\frac\gamma2>0.
}
$$

<a id="proof-10"></a>

**证明。** 
取 $Z=P-(r/d)I_{\mathcal W}$，有
$\|Z\|_{\mathrm F}^2=r(d-r)/d$。
每个 $R_j$ 的正交分块给

$$
\|P-R_jPR_j^*\|_{\mathrm F}^2
=2\|QR_jP\|_{\mathrm F}^2.
$$

代入引理 [5.2](#lem:gap) 的 Dirichlet 恒等式即得第一界。
又 $\operatorname{rank}(QR_jP)\le\min(r,d-r)$，
其 Frobenius 范数平方不超过该秩乘最大奇异值平方，故得第二界。
 ∎

因此，固定完整黄金菜单上，任意非平凡真线性摘要都不能将所有门的泄漏任意压小。
若加入单位效果，$r$ 是其无迹部分的维数；只有常数读数与完整 Hermitian 空间是两个端点。
固定 qubit 代码上的三轴完备性保留其原代码与菜单范围，
不被本定理改写成完整 $13$ 维或 $89$ 维菜单的闭合性。
$\gamma$ 的定义及正性也没有自动给一个可供实验使用的数值容限。

<a id="thm:cycle"></a>

#### 定理 5.4（有限周期的定量返回）

设 $\mathcal U^q=I$、整数 $q\ge1$，$A=P\mathcal UP|_V$，
$\ell=\|Q\mathcal UP\|_{\mathrm{op}}$，并记

$$
\epsilon_{\rm cyc}=\|P\mathcal U^qP|_V-A^q\|_{\mathrm{op}}
=\|I_V-A^q\|_{\mathrm{op}}.
$$

则

$$
\boxed{
1-\sqrt{1-\ell^2}
\le\epsilon_{\rm cyc}
\le\min\!\left(2,\frac{q(q-1)}2\ell^2\right).
}
$$

特别地，$\epsilon_{\rm cyc}\ge\ell^2/2$。
若 $\epsilon_{\rm cyc}\le\epsilon<1$，则

$$
\ell^2\le2\epsilon-\epsilon^2.
$$

精确 $q$ 步无记忆预测迫使 $\ell=0$。

<a id="proof-11"></a>

**证明。** 
引理 [4.2](#lem:leak) 给最小奇异值
$s_{\min}(A)=\sqrt{1-\ell^2}$。
取其单位右奇异向量 $v$，因 $A$ 收缩，
$\|A^qv\|\le\|Av\|=\sqrt{1-\ell^2}$。
三角不等式给下界；$1-\sqrt{1-t}\ge t/2$ 给简化式。
上界是定理 [4.3](#thm:finiteerror) 对同一个门及可见初值的应用。
由 $\sqrt{1-\ell^2}\ge1-\epsilon$ 即得反向预算。
 ∎

项目完整原始矩阵为

$$
K=\zeta(I-\mathcal P)+\zeta^2\mathcal P,
\qquad \mathcal P^2=\mathcal P=\mathcal P^*,\quad
\zeta=e^{3\pi i/5}.
$$

所以在*全部八维三量子位空间*有 $K^{10}=I$，
再张量未操作位置或限制到已证不变扇区仍成立。
左右位为 $01,10$ 的块是 $\zeta I$，不是恒等；$11$ 块为 $\zeta^2I$。
这些相位均计入十次复原。[[6](#bib-fixedgate), [7](#bib-v15)]

<a id="cor:ten"></a>

#### 推论 5.5（固定原生菜单的十步见证）

在定理 [5.3](#thm:nativegap) 的原生菜单上，每个原始门满足 $K_j^{10}=I$。
对任意 $0<r<d$ 的可见子空间，存在一个地址 $j$，使

$$
\boxed{
\|PR_j^{10}P|_V-(PR_jP|_V)^{10}\|_{\mathrm{op}}
\ge b_r:=1-\sqrt{1-c_r}
\ge\frac{c_r}{2}\ge\frac\gamma4.
}
$$

<a id="proof-12"></a>

**证明。** 
定理 [5.3](#thm:nativegap) 给一个 $\ell_j^2\ge c_r$ 的地址；
对其十次重复应用定理 [5.4](#thm:cycle)。
由实际 $\ell_j\le1$ 可知这里 $c_r\le1$，根式定义良好。
 ∎

推论只重复*同一个原始地址*。不同地址的任意组合字没有被宣称十阶。
它说明，即使只看固定十步，真子空间的逐步压缩也不能与真实精确酉递归完全一致。

对一个周期为 $q$ 的单门，有一个直接修复：扩充为

$$
\widetilde V=\operatorname{span}\{R^kV:0\le k<q\},
\qquad \dim\widetilde V\le q\dim V.
$$

周期性使 $R\widetilde V=\widetilde V$，故在该扩充上恢复精确一阶等距递归。
它增加实际需保留的关系；多个非交换地址的共同闭合仍用 v39 的完整效果递推。

<a id="section-5-1"></a>

### 5.1　从算子间隙到原生唯一种子的实际字见证

<a id="thm:actualwitness"></a>

#### 定理 5.6（纯态轨道与实际读数的见证）

假设原生唯一种子 $v_*$ 的有限正字纯态轨道在 $\mathbb P(\mathcal H_D)$ 稠密，
并已供应线性校准读出。记全部有限正准备字为 $\mathsf W$。
令 $E_1,\ldots,E_r$ 是当前实际效果，其中心化
$B_\ell=E_\ell-(\operatorname{Tr} E_\ell/D)I$ 构成 $V$ 的一组基。
置 $\mathsf G_{\ell k}=\operatorname{Tr}(B_\ell B_k)$、$\alpha=\lambda_{\min}\mathsf G>0$。
对推论 [5.5](#cor:ten) 的地址 $j$，令
$\rho_p=K_p|v_*\rangle\langle v_*|K_p^*$，
十步真实读数与无记忆预测的差为

$$
\Delta f_\ell(p)=
\operatorname{Tr}\!\left[B_\ell(I_V-A_j^{10})P(\rho_p-I/D)\right].
$$

则

$$
\boxed{
\sup_{p\in\mathsf W}\max_{1\le\ell\le r}
|\Delta f_\ell(p)|
\ge b_r\sqrt{\frac{\alpha}{rD}}.
}
$$

因此至少有一个实际有限准备字和一个当前读口，超过右端的任意严格较小常数。

<a id="proof-13"></a>

**证明。** 
记 $L=I_V-A_j^{10}$，$c=\|L\|_{\mathrm{op}}\ge b_r$。
取单位左奇异向量 $u\in V$，使 $L^*u=cv$、$\|v\|_{\mathrm{HS}}=1$。
这里 $v$ 是无迹 Hermitian 矩阵，故

$$
\sup_{\rho\text{ pure}}
\|LP(\rho-I/D)\|_{\mathrm{HS}}
\ge\sup_{\rho\text{ pure}}|\operatorname{Tr}(\rho L^*u)|
=c\|v\|_{\mathrm{op}}\ge\frac c{\sqrt D}.
$$

十次实际酉把整个 $\rho$ 送回自身，所以即使 $Q(\rho-I/D)\ne0$，
真实可见量与压缩预测的差仍恰为 $LP(\rho-I/D)$。
对任何 $z\in V$，读数帧满足
$\sum_\ell|\operatorname{Tr}(B_\ell z)|^2\ge\alpha\|z\|_{\mathrm{HS}}^2$。
再用最大分量至少为欧氏范数的 $1/\sqrt r$，给纯态上确界。
有限原生纯态轨道稠密、所列函数连续，使同一个上确界在实际字上保持。
 ∎

在 $D=13$、三个独立无迹读数时，$d=168$、$r=3$，
$c_r=55\gamma/56$，读数因子为 $\sqrt{\alpha/39}$。
这些是符号证书；未求值的 $\gamma,\alpha$ 不能写成已取得的统计阈值。
此定理没有免费制备混态、寻找见证字或取得全部均值；
它只把数学见证的量词忠实地下降为已供稠密轨道上的有限字存在性。

<a id="section-6"></a>

## 6　内部量子通道的有限周期刚性

本节使用另行声明的系统–记录张量接口，不能把上一节任意 HS 投影直接当作偏迹。
令 $\dim\mathcal H_S=s\ge2$，记录态 $\tau_M$ 固定，整体酉 $U$ 在同一个内部载体上满足
$U^q=I$，其中整数 $q\ge1$。定义实际无复位重复过程

$$
\Lambda_n(\rho)=\operatorname{Tr}_M\bigl[U^n(\rho\otimes\tau_M)U^{*n}\bigr].
$$

只给一次输入初始化，没有在各步重新装入 $\tau_M$。

<a id="thm:channelcycle"></a>

#### 定理 6.1（一个完整周期已经排除非酉自治通道）

若某个同维系统 CPTP 映射 $\Phi$ 满足 $\Phi^q=\Lambda_q$，则 $\Phi$ 为酉通道。
特别地，若 $\Lambda_n=\Phi^n$ 对 $0\le n\le q$ 成立，结论也成立。

<a id="proof-14"></a>

**证明。** 
整体周期给 $\Lambda_q=\operatorname{id}$，所以 $\Psi=\Phi^{q-1}$ 是 $\Phi$ 的 CPTP 左逆。
写两者 Kraus 算子为 $A_i,B_j$；组合的 Kraus 算子是 $B_jA_i$。
恒等通道的任何 Kraus 算子都为标量乘 $I$：对每个纯输入，输出秩一迫使每项向量
与输入平行，再对基向量和两基叠加使用线性性即可。
于是 $B_jA_i=c_{ji}I$。
至少一个 $c_{j_0i_0}\ne0$，同维性使 $A_{i_0},B_{j_0}$ 可逆。
对全部 $i$，$B_{j_0}A_i$ 仍为标量 $I$，故所有 $A_i$ 比例于同一个矩阵。
通道遂只有一个有效 Kraus 算子 $W$；保迹给 $W^*W=I$，同维给 $W$ 酉。
 ∎

这将 v38 的无限轮严格收缩障碍强化为指定周期的有限步刚性，
但只适用于确实满足该全局周期与同一初始化的接口。

<a id="thm:approxchannel"></a>

#### 定理 6.2（近似周期与每对状态的保距下界）

使用完整 diamond 范数（未乘 $1/2$）。若

$$
\|\Phi^q-\operatorname{id}\|_\diamond\le\epsilon<1,
$$

则对每个内部参考 $R$ 与每个 Hermitian $\Delta$，

$$
\boxed{
\|(\Phi\otimes\operatorname{id}_R)(\Delta)\|_1
\ge(1-\epsilon)\|\Delta\|_1.
}
$$

若系统态对另满足统一收缩
$\|\Phi(\rho)-\Phi(\sigma)\|_1\le q_0\|\rho-\sigma\|_1$，则

$$
\boxed{q_0\ge(1-\epsilon)^{1/q}.}
$$

<a id="proof-15"></a>

**证明。** 
Hermitian 输入的迹范数在 CPTP 映射下不增，故

$$
\|(\Phi\otimes\operatorname{id})(\Delta)\|_1
\ge\|(\Phi^q\otimes\operatorname{id})(\Delta)\|_1
\ge(1-\epsilon)\|\Delta\|_1.
$$

后一个不等式来自 diamond 预算和三角不等式。
再对任意不同系统态迭代 $q$ 次收缩，得 $q_0^q\ge1-\epsilon$。
 ∎

diamond 范数保留任意内部参考的测试；$q_0$ 则只量化系统态对。
若让任意独立参考本身携带区别，所有联合态对的严格收缩本来就不可能。
相应范数及通道区分接口见 Watrous。[[11](#bib-watrous20)]

若实际各次门仍为同一完整载体上的酉，且相对理想周期门的算子误差至多 $\tau$，
则伸缩求和给 $\|\widetilde U_q\cdots\widetilde U_1-I\|_{\mathrm{op}}\le q\tau$。
偏迹通道相对恒等的 diamond 误差至多 $2q\tau$。
若无记忆模型对实际第 $q$ 步过程满足同一个完整范数预算
$\|\Phi^q-\widetilde\Lambda_q\|_\diamond\le\delta$，
可在定理 [6.2](#thm:approxchannel) 中使用
$\epsilon=\delta+2q\tau$（当它小于一时）。
这保留近似原生门的实际误差，未把理想十阶当成实验恒等式。

<a id="section-7"></a>

## 7　带噪声的有限证据与量词

<a id="definition-7.1"></a>

#### 定义 7.1（有限终端均值报告的比较模型）

这一节另设数学信息模型，不授予原生自由角度。
未知 $\theta\in[0,\theta_*]$，其中 $0<\theta_*<\pi$；
系统初态为 $\rho_0=(I+Z)/2$，候选门为 $R_y(\theta)$。
协议可请求有限整数长度 $n$ 的终端 $Z+$ 均值报告

$$
y(n)=p_\theta(n)+\eta,\qquad
p_\theta(n)=\frac{1+\cos(n\theta)}2,\quad |\eta|\le\epsilon,
$$

其中 $\epsilon>0$，误差可相关。
协议可依据已报告值选择下一个长度或停止。
报告接口的取得及成本为这里的明示前件，不从单个不可复制量子态自动获得。

<a id="thm:noisyclosure"></a>

#### 定理 7.2（无分离承诺时有限报告不能可靠认证精确闭合）

设一个确定协议对全部上述来源和误差可靠。
它不能在 $\theta=0$ 的全一报告路径上有限宣布
$\operatorname{span}\{I,Z\}$ 对候选门精确闭合。

<a id="proof-16"></a>

**证明。** 
若它有限停止，令 $H=\max(\{0\}\cup\{\text{已请求长度}\})$。
若 $H=0$，任意充分小非零角度给相同报告。
否则选固定的 $0<\theta\le\theta_*$，使 $H^2\theta^2/4\le\epsilon$。
对所有已请求 $n$，

$$
0\le1-p_\theta(n)
=\frac{1-\cos(n\theta)}2\le\frac{n^2\theta^2}4\le\epsilon.
$$

因此同一全一记录在该固定非零来源上也合法，
确定协议逐前缀采取相同动作并作出同一断言。
但 $0<\theta<\pi$ 时 $K^*ZK$ 有非零 $X$ 分量，空间不闭合，矛盾。
误差规则可以预先定义为把每个真均值向一移动至多 $\epsilon$，
所以不是运行中更换来源，也不需要读取未来动作。
 ∎

该定理没有把参数菜单代换成固定黄金菜单；后一菜单已有定理 [5.3](#thm:nativegap)
的结构间隙，且精确矩阵可作代数分析。
它说明从有限带噪均值推断零残差时，应先声明来源族与分离承诺。
若只知 $|\widehat\ell-\ell|\le\eta$，验得 $\widehat\ell=0$ 也只能给
$\ell\le\eta$；由此能可靠使用的是定理 [4.3](#thm:finiteerror) 的有限视界预算。

新 FIB VIII 的定理在它自己的动作与来源域中给出更细的随机量词对照。
记固定来源 $s$、私有种子 $\omega$、公共因果误差规则 $\mathcal E$ 的成功事件为
$Z_\Pi(s,\mathcal E)$。
在其完整可靠性合同下，来源证明

$$
\sup_\Pi\inf_s\inf_{\mathcal E}
\Pr_\omega Z_\Pi(s,\mathcal E)=\frac12,
$$

而另有可测性时，

$$
\sup_\Pi\inf_s
\Pr_\omega\{\text{该固定种子对全部允许误差均成功}\}=0.
$$

第一式的同一个误差规则必须跨种子保持公共因果性。
不能对每个种子分别选择不相容的误差，再把各自障碍当成同一随机协议的上界。
本稿不把这两个数值移植到量子闭合认证；它们只作为严格量词范例。[[3](#bib-ranknoise)]

<a id="section-8"></a>

## 8　黄金十设置：完整循环的精确条件数

这一节延续 v39 的未知记录质量问题，是与隐藏记忆不同的误差层面。
假设同一实际相干输入 $X=(z_0\ z_1)$ 已覆盖全部
$S_k=B^k$、$0\le k\le9$ 的完整二分支统计合同：
两质量非负归一、无遗漏失败、细后继是指定投影归一态、
条件终端使用同一个校准读口、质量先于后续选择固定。
门 $B^k$ 来自 $k$ 次原地址 $K_9$；取得全部十组统计及其精度另计。
原生矩阵周期不自动使未知规则识别不同字面历史。[[5](#bib-continuation), [9](#bib-v39)]

<a id="definition-8.1"></a>

#### 定义 8.1（输入关系与加权隔离能量）

令

$$
G=X^*X=\frac{I+g\cdot\sigma}{2}\succ0,\quad \operatorname{Tr} G=1,
\quad \kappa=\lambda_{\min}(G)\in(0,1/2].
$$

$$
d_G=\det G=\kappa(1-\kappa),\qquad a=2\sqrt{d_G}.
$$

定义 $P_k=S_k^{\mathsf T}|0\rangle\langle0|\overline{S_k}=(I+n_k\cdot\sigma)/2$，
$s_k=g\cdot n_k$、$q_k=1-s_k^2$、$t_{k0}=(1+s_k)/2$、$t_{k1}=(1-s_k)/2$。
实际偏差为 $\delta_k=m_{k0}-t_{k0}$，并有

$$
A_k=XX^*+\delta_kH_k,\qquad
Q_X^*H_kQ_X=h_k\cdot\sigma,\qquad Q_X=XG^{-1/2}.
$$

这里 $H_k$ 是两个指定归一后继的差。
置

$$
\boxed{E_q^2=\sum_{k=1}^9q_k\|A_k-A_0\|_{\mathrm{op}}^2.}
$$

$q_k$ 是输入几何权重，不是未知实际质量被先验设为 Born。

输入几何恒等式为

$$
h_k=\frac{aC_gn_k}{q_k},\qquad
C_g=P_{g^\perp}+aP_{\parallel g},\quad C_g^2=I-gg^{\mathsf T}.
$$

在 $g=0$ 时取 $C_g=I$。
它由 $H_k=X(P_k/t_{k0}-(I-P_k)/t_{k1})X^*$ 得到：
将 $g$ 在证明中取为第三坐标，乘开 $\sqrt G$ 两侧，
横向系数为 $a$、纵向系数为 $a^2$，再除以 $q_k$。
该数学换基不供应新控制。

<a id="thm:tenframe"></a>

#### 定理 8.2（十循环的精确框架矩）

令 $x=\varphi^{-1}$、$y=\sqrt x$，黄金块的旋转轴为
$q_R=(2xy,0,x^3)$。
置 $c=n_0\cdot q_R=x^3$、$s=\sqrt{1-c^2}$，则 $s^2=4x^3$，并有

$$
\sum_{k=0}^9n_kn_k^{\mathsf T}
=5s^2P_{q_R^\perp}+10c^2P_{\parallel q_R}.
$$

令

$$
M_{10}=\sum_{k=1}^9(n_0\times n_k)(n_0\times n_k)^{\mathsf T}.
$$

它在 $n_0^\perp$ 上的两个特征值精确为

$$
\boxed{\mu=60x^9,\qquad \nu=20x^3,\qquad 0<\mu<\nu.}
$$

<a id="proof-17"></a>

**证明。** 
取 $e_1,e_2$ 为 $q_R^\perp$ 上的正交基，使
$n_k=cq_R+s(\cos k\theta\,e_1+\sin k\theta\,e_2)$，
$\theta=\pm3\pi/5$。
$B$ 对称，所以转置轴约定仍是这个轨道。
十次单位根等比和给
$\sum e^{ik\theta}=\sum e^{2ik\theta}=0$；
于是平方正弦、平方余弦各和为五，交叉项为零，得到二阶矩。
令 $L(v)=n_0\times v$，则 $M_{10}=L(\sum n_kn_k^{\mathsf T})L^*$。
在

$$
e_{\rm slow}=\frac{n_0\times q_R}{s},\qquad
e_{\rm fast}=\frac{q_R-cn_0}{s}
$$

两个正交方向上的系数分别为 $15c^2s^2$、$5s^2$。
代入黄金恒等式即得。$x<2/3$ 给 $3x^6<1$，故次序如上。
 ∎

<a id="thm:tencondition"></a>

#### 定理 8.3（加权能量配方与全输入最优常数）

令

$$
r_k=\frac{n_0\cdot n_k-s_0s_k}{q_0}.
$$

有精确分解

$$
\boxed{
E_q^2
=a^2\sum_{k=1}^9(\delta_k-r_k\delta_0)^2
+\frac{a^2\delta_0^2}{q_0^2}
\left(a^2\operatorname{Tr} M_{10}+g^{\mathsf T}M_{10}g\right).
}
$$

固定 $d_G$ 时，基准偏差对该加权能量的全输入最佳局部线性界为

$$
\boxed{
|\delta_0|
\le
\frac{E_q}{2\sqrt{d_G(60x^9+80d_Gx^3)}}.
}
$$

其 $\kappa^{-1/2}$ 退化阶不可再改进。

<a id="proof-18"></a>

**证明。** 
对每条边，把 $\delta_kh_k-\delta_0h_0$ 沿 $h_k$ 与其正交方向配方。
输入恒等式给

$$
q_k|h_k|^2=a^2,\qquad
\frac{h_0\cdot h_k}{|h_k|^2}=r_k,
$$

以及

$$
q_k|h_0|^2\sin^2\vartheta_{0k}
=\frac{a^2}{q_0^2}
\left(a^2|n_0\times n_k|^2+
[g\cdot(n_0\times n_k)]^2\right).
$$

求和即得分解。固定 $g$ 时，最优常数为

$$
C(g)=\frac{q_0}{a\sqrt{a^2\operatorname{Tr} M_{10}+g^{\mathsf T}M_{10}g}},
$$

并由 $\delta_k=r_k\delta_0$ 取等；满秩保证足够小的偏差仍为合法概率。

令 $t=|P_{n_0^\perp}g|^2\in[0,1-a^2]$，则 $q_0=a^2+t$，并且

$$
C(g)^2\le\frac{(a^2+t)^2}
{a^2[a^2(\mu+\nu)+\mu t]}.
$$

右边随 $t$ 严格增加：去掉正分母后，导数符号由
$(a^2+t)[a^2(\mu+2\nu)+\mu t]>0$ 决定。
取 $t=1-a^2$，并令 $g$ 沿 $e_{\rm slow}$，得到

$$
\sup C(g)=\frac1{a\sqrt{\mu+a^2\nu}},
$$

代入 $a^2=4d_G$ 即为所列常数。

为在合法概率中统一取等，取
$g=\sqrt{1-4d_G}\,e_{\rm slow}$，
$\delta_k=(n_0\cdot n_k)\delta_0$。
对应输入可取 $X=Q_X\sqrt G$，其中 $Q_X$ 为任意固定系统二维等距。
此时 $q_0=1$、$|s_k|\le s<1$，
所以固定 $0<|\delta_0|\le(1-s)/4$ 即使所有质量严格合法。
并且精确有

$$
E_q=2|\delta_0|\sqrt{d_G(60x^9+80d_Gx^3)}.
$$

固定非零偏差而 $d_G\to0$ 即证明退化阶不可改善。
 ∎

此处“最优”只针对明确的未归一加权和 $E_q^2$、固定基准及上述统计合同。
九条比较边比 v39 的两条边要求更多统计；不能在不计报告成本和误差分配时
将不同和式的常数直接比较为免费精度提升。
同一十循环的原始三维轴框架也不是各向同性：
任意非负权重之和为一时，轴向二阶矩恒为 $c^2\ne1/3$。
因此不能把循环次数增加直接解释为任意三维紧帧。

<a id="section-9"></a>

## 9　对 AURIC 递归语义的可复合结论

本轮明确区分三个层次。
第一，归一化的聚合质量可以沿指定路径由酉实现，但共同未知输入之间的内积也必须保持。
第二，真正共同的局部通道可使余量占据概率减少，其完整信息通过内部记录保存。
第三，把可见坐标自身作为逐步状态，必须保留隐藏关系的返回核，或证明相应空间闭合。

| 目标 | 本轮精确结论 | 承重前件 |
| --- | --- | --- |
| 已知三预算轨迹 | 可按指定角度逐步酉编码 | 实际余量、连续旋转数学模型 |
| 共同未知占据概率更新 | 二 Kraus 通道及内部等距 | 三模式范围、CP/读口、ready 接口 |
| 完整首次转移历史 | $n+1$ 个正交记录槽 | 寄存器本身独立无误保留历史 |
| 无记忆线性递归 | 有限维中等价于零泄漏 | 全可见初值与完整未来量词 |
| 近似闭合有限字 | $s_L$ 隐藏项与 $t_L$ 返回项 | 固定度量、完整误差预算 |
| 固定原生真摘要 | 正间隙及十步返回见证 | 全菜单密度、精确单门十周期 |
| 有限统计认证 | 需来源分离及正确量词 | 明确噪声、报告与随机种子接口 |
| 十记录设置反推 | 精确条件数，阶仍 $\kappa^{-1/2}$ | 十设置实际合同与加权能量定义 |

误差仍是态或读数的差，通常不是迹为一的状态。
可用正定 Gram 度量表示它的方向与长度，但归一化方向时必须另存幅度。
当前压缩看来收缩，可能只是关系流入未保留部分；
完整记忆方程和原生十步见证将这种可能性变成可证明的量。
若未来还允许查询全部原始程序档案，固定载体的效果空间须另行扩张；
续卷 II §83 的档案查询已经给出无界未来秩，不能用本稿有限量子终端摘要替代。[[5](#bib-continuation)]

<a id="bibliography"></a>

## 固定来源与证明范围

<a id="bib-head"></a>

**[1]** 
The Omega Institute.
[固定提交 30933a24a13489](https://github.com/the-omega-institute/trureturing/commit/30933a24a13489f127757b99e12796ff09ebeafb)。
本轮两完整子树、八项下载与九项复用供应均核 Git blob 身份；
未执行 Lean、数学程序、枚举或门字搜索，未修改或提交仓库。

<a id="bib-budgets"></a>

**[2]** 
[Robin 裕量的三项非负预算、递归酉实现与 Mellin 判据](https://github.com/the-omega-institute/trureturing/blob/30933a24a13489f127757b99e12796ff09ebeafb/docs/develop/theory/AURIC_ROBIN_PRIME_OSCILLATION_THREE_POSITIVE_BUDGETS_RECURSIVE_UNITARIES_AND_MELLIN_CRITERION.md)。
本稿直接读取编者说明及 §4 全部证明；来源审查全文读取。
只消费固定实际整数余量、$(2,5,3)$ 聚合编码及其范数速率。
不消费未定位的匹配终点，也不把作者稿导入视作独立形式认证。

<a id="bib-ranknoise"></a>

**[3]** 
[FIB 自校准关系数学 VIII](https://github.com/the-omega-institute/trureturing/blob/30933a24a13489f127757b99e12796ff09ebeafb/docs/develop/theory/FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VIII.md)，新 §10。
完整读取定义 10.1、引理 10.2、定理 10.3 及证明。
固定源域、动作、共享报告、公共因果误差及路径可靠性均保留；
量子模型的有限报告障碍由本文另证，不作未建立的归约。

<a id="bib-mpc"></a>

**[4]** 
[联合核与最小预测核桥](https://github.com/the-omega-institute/trureturing/blob/30933a24a13489f127757b99e12796ff09ebeafb/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_KERNEL_MINIMAL_PREDICTIVE_CORE_BRIDGE.md)，新 §27。
来源审查完整读取；本稿复核其定义、严格界与范围。
十四事件安装及全部响应收费合同不移入量子菜单。

<a id="bib-continuation"></a>

**[5]** 
[AURIC 量子原则与相干重建续卷 II](https://github.com/the-omega-institute/trureturing/blob/30933a24a13489f127757b99e12796ff09ebeafb/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md)。
当前文件未变；消费 §77 的全十三维七地址射影密度、§83 的档案边界、
扩大扇区供应，以及 §105、§111 的精确记录地址作用。
其复结构、准备、校准和统计前件仍独立保留。

<a id="bib-fixedgate"></a>

**[6]** 
[固定黄金门与编织相容性](https://github.com/the-omega-institute/trureturing/blob/30933a24a13489f127757b99e12796ff09ebeafb/docs/develop/theory/AURIC_FIXED_GOLDEN_GATE_AND_BRAID_COMPATIBILITY_ZH.md)，§4 定理 4.1。
复核整个八维块的投影、相位、十阶周期与正向九次逆。

<a id="bib-v15"></a>

**[7]** 
[黄金门、NAND 通用性与算术边界 v15](https://github.com/the-omega-institute/trureturing/blob/30933a24a13489f127757b99e12796ff09ebeafb/docs/develop/theory/AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md)，§3。
完整固定矩阵的原规范；任意组合字不被宣称十阶。

<a id="bib-v37"></a>

**[8]** 
[二元关系、酉表示与黄金门通用性 v37](https://github.com/the-omega-institute/trureturing/blob/30933a24a13489f127757b99e12796ff09ebeafb/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)。
沿用五模式次序及占据读数；当前文稿为旧作者稿导入，非新核验。

<a id="bib-v39"></a>

**[9]** 
前轮作者稿，*AURIC：原生三设置的锐利稳定性、未来闭合与递归误差能量*，
v39，2026-10-31。
本轮复用其完整记录合同、输入几何与 Gram 度量；
十设置的全部统计量词、最优常数和取等族在本稿重新列明。

<!-- editorial-start:v39 -->
> **版本关系（编者说明）** 此处保留作者的“前轮作者稿”称谓。v39 的[仓内版本](https://github.com/the-omega-institute/trureturing/blob/52fdc99080bdca5a4686482df82bad5a6f39f7c7/docs/develop/theory/AURIC_SHARP_NATIVE_THREE_SETTING_STABILITY_FUTURE_CLOSURE_AND_RECURSIVE_ERROR_ENERGY_V39.md)已由 [PR #24482](https://github.com/the-omega-institute/trureturing/pull/24482) 合入；公开发表不等于其纸面证明获得内核认证。十设置的统计合同仍须另供。
<!-- editorial-end:v39 -->

<a id="bib-watrous5"></a>

**[10]** 
John Watrous.
[Theory of Quantum Information, Lecture 5: Characterizations of channels](https://cs.uwaterloo.ca/~watrous/TQI-notes/TQI-notes.05.pdf)，2011。
Kraus、Choi 与内部等距表示为标准数学背景；本稿给所用具体过程的自足证明。

<a id="bib-watrous20"></a>

**[11]** 
John Watrous.
[Theory of Quantum Information, Lecture 20: Channel distinguishability](https://cs.uwaterloo.ca/~watrous/TQI-notes/TQI-notes.20.pdf)，2011。
完整有界迹范数与内部参考接口；本文周期误差界直接由范数定义及收缩性证明。

<!-- source-document-end -->
