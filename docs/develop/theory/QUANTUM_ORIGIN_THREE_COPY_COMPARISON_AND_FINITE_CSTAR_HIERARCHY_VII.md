# 三份原准备比较与全有限复 C* 张量层级 VII

## 102. 三份比较在强分块层级中的全有限闭合

### 102.1 原层级与唯一比较输入

**定义 102.1（全有限强分块层级）。** 取非零有限维实向量空间 $V$，令
$W_N=V^{\otimes_{\mathbb R}N}$，$N\ge1$。给定每个 $W_N$ 上的闭、尖、生成凸锥
$C_N$，以及 $u\in V^*$，使 $u_N=u^{\otimes N}$ 在 $C_N\setminus\{0\}$ 上严格为正。
写

$$
K_N=\{x\in C_N:u_N(x)=1\},\qquad
P_N=\operatorname{ext}K_N,\qquad
\mathcal E_N=[0,u_N]_{C_N^*}.
\tag{102.1}
$$

这里 $P_N$ 是整个原基的全部极点，$\mathcal E_N$ 是整个原 proper 效应区间。
对每个实际分块 $a+b=N$，在指定的同一实张量坐标中要求

$$
C_a\otimes_{\min}C_b\ \subseteq\ C_{a+b}\
 \subseteq\ C_a\otimes_{\max}C_b.
\tag{102.2}
$$

左锥是正简单张量生成的闭凸锥；右锥由所有 $f\otimes g$，
$f\in C_a^*,g\in C_b^*$，的非负半空间相交定义。
每个因子置换 $\tau_\pi$ 保持 $C_N$；它的逆是另一原置换，因而也是正的。
任意不连续位置的分块，先用这些指定置换运输，再使用(102.2)。
重括号是同一实张量空间的规范识别，不另换联合锥。
原状态乘积、原效应乘积及其校准始终是

$$
(f\otimes g)(x\otimes y)=f(x)g(y),\qquad
u_{a+b}=u_a\otimes u_b.
\tag{102.3}
$$

特别地，乘积效应分离整个 $W_{a+b}$。这些全有限条件是本章的模型域；
只指定一对与一个三份对象，不构成此模型域。
为标记空旁观系统，约定 $W_0=\mathbb R$、$C_0=\mathbb R_+$、$u_0=\mathrm{id}$；
它只是标量约定。

**定义 102.2（原穷尽比较、$S_N$ 与三份电路入口）。** 对 $p\in P_N$、$x\in C_N$，定义

$$
T_p^{(N)}(x)=\inf\{f(x):f\in\mathcal E_N,\ f(p)=1\}.
\tag{102.4}
$$

确认集合含 $u_N$，读数有界，故下确界有定义。
$S_N$ 表示对每个 $p\in P_N$、每个有限纯准备 $q_\ell\in P_N$ 及
$a_\ell\ge0$、$\sum_\ell a_\ell=1$，有

$$
T_p^{(N)}\!\left(\sum_\ell a_\ell q_\ell\right)
 =\sum_\ell a_\ell T_{q_\ell}^{(N)}(p).
\tag{102.5}
$$

本章只要求 $S_3$。它量化全部原三份纯态和全部有限准备，包含纠缠纯态；
“三份”不是三个选定探针。

另一个入口 $\mathsf{CB}_3$ 如下。对每个 $p\in P_3$，每个有限不同标签集
$F\subset P_3$，以及每个非零实系数族 $(c_q)_{q\in F}$，若
$\sum_{q\in F}c_q q=0$ 的实际支撑在非零有符号关系中极小，则要求

$$
\sum_{q\in F}c_q T_q^{(3)}(p)=0.
\tag{102.6}
$$

极小性指：同一有限标签上的任意非零关系，其支撑若包含于当前支撑，
便与当前支撑相等。允许有限环境标签中有零系数。
反向读数 $q\mapsto T_q^{(3)}(p)$ 的方向是定义的一部分。
对关系应用 $u_3$ 自动给 $\sum_qc_q=0$。

**命题 102.3（一个纯旁观者下的精确限制）。** 在定义102.1下，不用任何 $S_N$，
存在 $r\in P_1$；对每个 $a\ge1$，$j_r(x)=x\otimes r$ 把 $P_a$ 送入 $P_{a+1}$，且

$$
T_{j_r(p)}^{(a+1)}(j_r(x))=T_p^{(a)}(x)
\qquad(p\in P_a,\ x\in C_a).
\tag{102.7}
$$

因此 $S_{a+1}\Rightarrow S_a$，特别是
$S_3\Leftrightarrow(S_1\land S_2\land S_3)$。
在此同一载体上，$\mathsf{CB}_3\Leftrightarrow S_3$，其中纯端点互反是结论。

**证明。** 有限维闭尖锥的严格正单位给出非空紧基；非零生成性排除空基，
紧凸几何给 $P_1\ne\varnothing$。固定其中一个 $r$。
对实际复合 $(W_a,W_1,W_{a+1})$，(102.2)—(102.3)满足
[Barnum–Hilgert 笔记的纯边缘／纯乘积引理](../../../Library/QuantumStates/barnumhilgert2019spectral.md#a-pure-marginal-fixes-every-conditional-state)
的全部输入：正态乘积、正效应乘积、原单位、精确配对与局部层析。
该引理不消费 $S$；直接使用其纯乘积结论，得 $j_r(p)\in P_{a+1}$。

若 $F\in\mathcal E_{a+1}$ 确认 $p\otimes r$，令 $f(x)=F(x\otimes r)$。
由最小界和 $u_1(r)=1$，对每个 $x\in C_a$ 有
$0\le f(x)\le u_a(x)$，且 $f(p)=1$。故所有这类 $F$ 的读数至少是右侧(102.7)。
反之，任意确认 $p$ 的 $f\in\mathcal E_a$ 都提升为 $f\otimes u_1$。
最大界分别作用于 $f,u_1$ 与 $u_a-f,u_1$，说明提升及其单位补均正，
所以提升是原 proper 效应；其确认和在 $x\otimes r$ 上的读数完全相同。
两族下确界相等。将(102.5)限制到 $j_r(p),j_r(q_\ell)$ 即得下降；先取 $a=2$，再取 $a=1$。

最后直接应用既有
[`full_mixture_iff_circuit_balance`](../../../D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.lean)
的电路平衡等价，其陈述也列于
[对应的数学陈述](../../../Blueprint/D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.md)。
参数逐项取 $A=W_3$、$C=C_3$、单位 $u_3$、全部基 $K_3$、全部极点 $P_3$、
整个 proper 区间 $\mathcal E_3$，以及原下确界(102.4)。
任取 $W_3$ 上的有限维范数；闭性、严格正性和正锥实张成恰是定义102.1的条件。
该陈述中的 `circuit`、`balanced`、`fullMixture` 分别就是上述极小支撑关系、
(102.6)和(102.5)，包含零权与重复准备标签。
它给出 $\mathsf{CB}_3\Leftrightarrow S_3$ 及 reciprocal least confirmation；
不另作互反假设，也不重证此等价。∎

### 102.2 低三份供应与共同坐标

**约定 102.4（B1—B3 的条件性供应接口）。** 以下使用已有纸面桥和它们引用的成熟定理，
保持各自全部输入。供应对应为：

| 供应 | 本层级中的精确输入 | 所用输出与边界 |
| --- | --- | --- |
| B1：$S$ 到 Jordan | 对 $q=1,2,3$ 分别取 $(W_q,C_q,u_q,K_q,P_q,\mathcal E_q)$；命题102.3给 $S_q$，效应不受限 | reciprocal least 尺、自对偶正定配对、共同框架谱分解、正面投影及其保纯性，随后有限维 EJA，包括直和 |
| B2：实际复合与自复合复块 | 实际 $(W_1,W_1,W_2)$；再取 $(W_2,W_1,W_3)$ 及 $(W_1,W_2,W_3)$；各自 B1，正态／效应双乘积、单位、配对和局部层析 | 原扇区的整锥直和、框架秩乘法与实维乘法；一个实际自复合选出任意大小的复矩阵块，三份块的大小是 $n_i n_j n_k$ |
| B3：共同方向 | 两个三份括号使用同一个原 $W_2$；重括号是 $W_3$ 上恒等映射；原 $\tau_{12}$ 在全部 $C_3$ 上正；全部 B2 及实际产品校准 | 存在一套固定坐标，使原一、二、三份的产品同时为标准产品；结论此处只到三份 |

B1 使用
[least confirmation、谱与面保纯的完整桥](../../../Library/QuantumStates/mullerududec2012selfduality.md#reciprocal-least-confirmation-and-the-spectrality-bridge)，
特别是其中 “Least confirmation forces face-filter purity” 的结论，及其所调用的
Barnum–Müller–Ududec，[arXiv:1403.4147v4](https://arxiv.org/abs/1403.4147v4)，定理16。
该归约的 projectivity、对称转移与 filter purity 均保留；不把 bit symmetry、
强对称、纯传递或保纯性另塞为输入。

B2 使用
[实际产品框架与比较因子化](../../../Library/QuantumStates/barnumhilgert2019spectral.md#local-comparison-and-composite-frames)、
[无连通输入的扇区复合](../../../Library/QuantumStates/barnumhilgert2019spectral.md#sector-composites-without-a-connectedness-input)
和[一个自复合的复型选择](../../../Library/QuantumStates/barnumhilgert2019spectral.md#complex-sectors-from-a-single-self-composite)。
正效应产品来自最大界，正态产品来自最小界；张成与分离来自原实张量空间和原配对。
三份中 $(W_2,W_1)$ 的每个简单扇区复合有秩 $n_i n_j n_k$、实维其平方，
故供应中的同一分类包含其标量、秩二与更高秩边界。
不要求比较图连通，也不要求某块非经典。

B3 使用
[实际矩阵产品的条件正规形](../../../Library/QuantumStates/barnumhilgert2019spectral.md#actual-two-factor-products-after-complex-type-selection)
及[一个旁观交换与正重括号定理](../../../Library/QuantumStates/barnumhilgert2019spectral.md#one-spectator-swap-and-positive-reassociation)。
前者内部使用 Xu–Zheng–Fošner 的秩一 Hermitian 产品保持定理，
DOI [10.1017/S1446788714000603](https://doi.org/10.1017/S1446788714000603)；
后者处理所有活跃位置的共同转置方向，包含重复扇区与标量旁观者。
这里 $E_L=E_R=W_3$，两个产品分别是 $(x\otimes y)\otimes z$ 与
$x\otimes(y\otimes z)$，所以其指定重括号在整锥上为恒等正同构。
一个指定旁观交换由定义102.1提供，作用于全部纠缠态和全部扇区。
这些已有低阶桥作为供应结果使用，不在此重复证明。

具体地，供应给出非空有限集 $I$、整数 $n_i\ge1$，以及保单位的整锥同构

$$
\theta:V\longrightarrow A_{\rm h},\qquad
A=\bigoplus_{i\in I}M_{n_i}(\mathbb C),\qquad
u\theta^{-1}(x)=\sum_i\operatorname{Tr}x_i,
\tag{102.8}
$$

和二、三份整锥同构 $\theta_2,\theta_3$，满足

$$
\begin{aligned}
\theta_2(x\otimes y)&=\theta(x)\otimes\theta(y),\\
\theta_3(x\otimes y\otimes z)&=\theta(x)\otimes\theta(y)\otimes\theta(z).
\end{aligned}
\tag{102.9}
$$

纯产品实张成各个原张量空间，所以(102.9)在整个空间上强制
$\theta_q=\theta^{\otimes q}$，$q=2,3$，而非仅在正乘积上巧合。
精确配对同时决定对偶效应坐标。
以下固定这一个 $\theta$，不按份数或按输入重新选方向。

**定义 102.5（高阶向量坐标与原旁观正性）。** 对全部 $N$ 仅作实线性识别

$$
\theta^{\otimes N}:W_N\longrightarrow
\bigoplus_{s\in I^N}\operatorname{Herm}(\mathcal H_s),\qquad
\mathcal H_s=\bigotimes_{t=1}^N\mathbb C^{n_{s_t}},\quad
D_s=\prod_t n_{s_t}.
\tag{102.10}
$$

把运输后的原锥仍记为 $C_N$；原 $u_N$ 此时是各块迹之和，
原配对在向量空间上是实迹配对。记标准块 PSD 锥为
$\mathsf D_N=\bigoplus_{s\in I^N}\operatorname{Herm}_+(\mathcal H_s)$。
B1—B3 已给 $C_q=\mathsf D_q$，$q\le3$。
对 $N\ge4$，(102.10)暂不对原锥作任何 PSD 判断。
同一个 $\theta$ 使原置换仍是普通因子置换，全部(102.2)—(102.3)保持。

一个实线性 $F:W_m\to W_n$ 称为原旁观正的，若

$$
(\mathrm{id}_{W_r}\otimes F)(C_{r+m})\subseteq C_{r+n}
\quad\text{对每个整数 }r\ge0.
\tag{102.11}
$$

这只测试本层级自己的旁观系统。$F$ 在整个 Hermitian 空间的作用确定其唯一
复线性保 Hermitian 扩张，矩阵单位公式均使用此扩张。
若 $u_nF=u_m$，称其保质量；若它和逆均原旁观正并保质量，称其为原数学保质量自同构。
这些是正锥的数学映射定义，不指定物理事件菜单。

### 102.3 任意原纠缠输入的切片与自身 Choi 判据

**引理 102.6（整锥切片）。** 对任意 $a,b\ge0$、$z\in C_{a+b}$、$f\in C_a^*$，有

$$
(f\otimes\mathrm{id}_{W_b})z\in C_b.
\tag{102.12}
$$

同一结论适用于置换后的任意分块以及重复切片；$z$ 不必是可分态。

**证明。** 对每个 $g\in C_b^*$，最大界给
$g((f\otimes\mathrm{id})z)=(f\otimes g)(z)\ge0$。
有限维闭凸锥双极定理给出(102.12)。原置换正且可逆，允许先把所切块移到前面。
每次切片所得向量仍在剩余原锥，故可迭代。标量情形是正数乘法。∎

**引理 102.7（原自身拷贝的 Bell 蛇式与 Choi 当且仅当）。** 固定每个局部块的正交基，令

$$
\begin{aligned}
|I_i\rangle&=\sum_{a=1}^{n_i}|a\rangle\otimes|a\rangle,\qquad
\Omega_i=|I_i\rangle\langle I_i|,\\
\Omega&=\bigoplus_i\Omega_i\quad
 \text{位于二份的 }(i,i)\text{ 块，其余块为零},\\
\beta(z)&=\operatorname{Tr}(\Omega z),\qquad
R=\sum_i n_i,\qquad L=\max_i n_i.
\end{aligned}
\tag{102.13}
$$

则 $\Omega\in C_2$，$u_2(\Omega)=R$，$\beta\in C_2^*$，
$\Omega/R\in K_2$，且 $\beta/L\in\mathcal E_2$。
不缩放的杯与帽满足精确恒等蛇式，归一杯与 proper 帽的蛇式为
$\mathrm{id}_V/(RL)$。

将 $m$ 对杯按原置换排成“全部参考腿、全部输入腿”，记所得为 $\Omega_m\in C_{2m}$；
其参考扇区 $s$ 只与相同输入扇区 $s$ 配对，块为
$|I_{D_s}\rangle\langle I_{D_s}|$。令 $\beta_m$ 表示逐对 $\beta$ 收缩。
对每个 $F:W_m\to W_n$，按“参考 $m$ 腿、输出 $n$ 腿”的次序定义

$$
J(F)=(\mathrm{id}_{W_m}\otimes F)\Omega_m.
\tag{102.14}
$$

有精确原锥判据

$$
F\text{ 原旁观正}\quad\Longleftrightarrow\quad J(F)\in C_{m+n}.
\tag{102.15}
$$

**证明。** 二份整锥已经标准。$\Omega$ 各非零块的唯一非零本征值为 $n_i$，
故 $0\le\Omega\le L\mathbf1$，迹为 $R$，给出所有正性与预算断言。
除全部 $n_i=1$ 的情形外，$\beta$ 本身不满足单位上界。
在一块中对 Hermitian $x,y$ 有

$$
\beta_i(x\otimes y)=\operatorname{Tr}(x^{\mathsf T}y),\qquad
\Omega_i=\sum_{a,b}E_{ab}^{(i)}\otimes E_{ab}^{(i)}.
\tag{102.16}
$$

矩阵单位展开在复线性扩张中书写，和式属于原实 Hermitian 张量空间。
把 $x$ 与一个杯的参考腿用帽收缩，剩余腿为
$\sum_{a,b}x_{ab}E_{ab}=x$；不同扇区间无项。
这证明无转置余项的蛇式。缩放杯、帽分别乘 $1/R,1/L$，给 $1/(RL)$。

最小界及原置换给 $\Omega_m\in C_{2m}$。
对任意原 $C_{2m+b}$ 输入，逐对使用引理102.6给出的帽收缩均落入相应原剩余锥，
所以 $\beta_m$ 是原正泛函且可在任意原旁观输入上切片。
归一化版本 $\Omega_m/R^m$ 和逐对 $\beta/L$ 产生蛇式
$\mathrm{id}_{W_m}/(RL)^m$；后者逐次为 proper 切片，故总预算也受单位控制。
确切地，对剩余 $b$ 腿和任意 $z\in C_{2+b}$，最大界给

$$
0\le u_b\bigl[((\beta/L)\otimes\mathrm{id})z\bigr]
 =((\beta/L)\otimes u_b)(z)\le u_{2+b}(z),
\tag{102.16a}
$$

因为 $(u_2-\beta/L)\otimes u_b$ 对整个原联合锥正。
迭代此预算即可，包括各次剩余输入有纠缠的情形。
这些断言只用二份帽的正性和原最大界，不用 $C_{2m}$ 的 PSD 性。

若 $F$ 原旁观正，在(102.11)取 $r=m$，将其作用于原 $\Omega_m$，即得正向。
反向设 $J(F)\in C_{m+n}$。任取 $r\ge0$ 和
$z\in C_{r+m}$，标记 $z$ 的腿为 $(R_0,X)$，$J(F)$ 的腿为 $(X',Y)$。
最小界把 $z\otimes J(F)$ 放入原 $C_{r+2m+n}$。
在 $X,X'$ 的对应腿上逐对用 $\beta$ 收缩，保留 $(R_0,Y)$。
引理102.6说明输出在原 $C_{r+n}$，包括 $z$ 在 $R_0,X$ 间任意纠缠的情形。
蛇式和实张量张成在整个向量空间给出

$$
\operatorname{cap}_{X,X'}\bigl[z_{R_0X}\otimes J(F)_{X'Y}\bigr]
 =(\mathrm{id}_{W_r}\otimes F)(z).
\tag{102.17}
$$

例如输入扇区 $s$、输出扇区 $t$ 的展开为
$J(F)_{s,t}=\sum_{a,b}E_{ab}^{(s)}\otimes F_{t,s}(E_{ab}^{(s)})$；
收缩恰把输入系数 $x_{ab}$ 送入该和式。
一般带旁观者的恒等式由简单张量张成得到，而其正性已对原整个 $z$ 证明。
若改用归一资源和 proper 帽，只得到此映射的正倍数
$1/(RL)^m$；正锥允许恢复数学正性，却不允许据此把资源协议宣布为确定性事件。

同一系数公式还说明 $J$ 是所有实线性映射与 $W_{m+n}$ 间的向量空间双射：
在每对扇区上它保留每个矩阵单位的全部输出。
这是自身 $m$ 份参考的判据，不预设任意矩阵辅助物，也未给高阶锥加自对偶假设。∎

### 102.4 原中心投影与整锥直和

**引理 102.8（中心投影、局域酉及其所有旁观扩张）。** 令 $\Pi_i:W_1\to W_1$
保留局部块 $i$ 并把其他块置零。每个 $\Pi_i$ 原旁观正；对
$s=(s_1,\ldots,s_N)$，投影

$$
P_s=\Pi_{s_1}\otimes\cdots\otimes\Pi_{s_N}
\tag{102.18}
$$

在 $C_N$ 上正，且

$$
C_N=\bigoplus_{s\in I^N}\bigl(C_N\cap\operatorname{Herm}(\mathcal H_s)\bigr).
\tag{102.19}
$$

对任意局部块酉族 $(U_i)_{i\in I}$，映射
$x_i\mapsto U_i x_iU_i^*$ 和它的逆均原旁观正、保质量，因而在每个原 $C_N$ 上有正逆提升。

**证明。** $J(\Pi_i)=\Omega_i\in C_2$，故引理102.7给全部原旁观正性。
原旁观正映射的正和、复合仍原旁观正；张量积也如此，因为可先提升一个映射，
再经原置换提升另一个，复合即为张量映射。
因此每个 $P_s$ 对任意原旁观系统正。
向量空间上 $\sum_sP_s=\mathrm{id}$、$P_sP_t=\delta_{st}P_s$。
若 $x\in C_N$，每个 $P_sx\in C_N$，且 $x=\sum_sP_sx$。
各分量质量非负且和为 $u_N(x)$，所以每个投影亦不增质量。
反过来各交锥元素之和仍属 $C_N$；各子空间直和且 $P_s$ 的像正是相应子空间，
故得到真正的整锥直和(102.19)。没有从中心边缘的正性直接推断整锥分裂。

局域酉映射的 Choi 元素在 $(i,i)$ 块是
$(I_i\otimes U_i)\Omega_i(I_i\otimes U_i)^*$，其余块为零，
所以属于已知 $C_2$。逆映射把 $U_i$ 换成 $U_i^*$，具有相同正性。
迹保持是整空间恒等式，提升后的 $u_N$ 也保持。
允许只选一个块的酉、其他块取恒等；这一结论是原锥上的数学对称。∎

### 102.5 两个原三份资源给出二体耦合的 Choi 元素

**引理 102.9（角控制交换与正补扩张）。** 取任意 $i,j\in I$，满足
$d=n_i\ge2$、$e=n_j\ge2$。可取一个 $k\in I$、$b=n_k\ge2$，允许 $k=i$。
在块 $i$ 选秩一投影 $P$；在块 $j$ 选一个交换两条基向量、固定其余基向量的酉 $X$。
则

$$
U=(I_d-P)\otimes I_e+P\otimes X
\tag{102.20}
$$

在角 $(i,j)$ 上的酉共轭，延拓为其他角上的零映射，所得
$F_{ij,U}:W_2\to W_2$ 原旁观正。
更具体地，其 Choi 元素 $J(F_{ij,U})\in C_4$ 可以由两个属于原 $C_3$ 的秩一资源，
在原 $C_6$ 中相乘并收缩两条 $k$ 腿得到。
把资源各自归一，并使用 proper 帽 $\beta_k/b$ 时，输出恰是

$$
\frac{J(F_{ij,U})}{2deb},\qquad
u_4\!\left(\frac{J(F_{ij,U})}{2deb}\right)=\frac1{2b}.
\tag{102.21}
$$

令 $P_{ij}=\Pi_i\otimes\Pi_j$。整个二份空间上的映射

$$
G_{ij,U}=F_{ij,U}+\sum_{(h,l)\ne(i,j)}\Pi_h\otimes\Pi_l
\tag{102.22}
$$

是原数学保质量自同构，且 $G_{ij,U}^{-1}=G_{ij,U}$。
它及其所有原旁观提升在选定角上作用为(102.20)，在其余角上为恒等。

**证明。** 记 $A_0=I_d-P,A_1=P,B_0=I_e,B_1=X$，在块 $k$ 选两条基向量
$|0\rangle_k,|1\rangle_k$。对一个方阵 $A$，使用“参考、输出”的向量化

$$
|A\rangle\!\rangle=\sum_a|a\rangle_{\rm ref}\otimes A|a\rangle_{\rm out}.
\tag{102.23}
$$

构造两个三腿向量

$$
\begin{aligned}
|\alpha\rangle_{i_{\rm r},i_{\rm o},k_1}
 &=\sum_{t=0}^1|A_t\rangle\!\rangle\otimes|t\rangle_{k_1},\\
|\gamma\rangle_{k_2,j_{\rm r},j_{\rm o}}
 &=\sum_{t=0}^1|t\rangle_{k_2}\otimes|B_t\rangle\!\rangle.
\end{aligned}
\tag{102.24}
$$

$C_3=\mathsf D_3$，故 $\alpha\alpha^*$ 与 $\gamma\gamma^*$，分别放在
$(i,i,k)$ 与 $(k,j,j)$ 块，确属原 $C_3$。
这是同一局部类型的不同腿；$k=i$ 时也不合并腿或改变张量次数。
由最小界，两资源乘积属于原 $C_6$。
把两条 $k$ 腿置于一起，使用只在 $(k,k)$ 块非零的帽
$\beta_k(z)=\operatorname{Tr}(\Omega_k z)$。
它对原 $C_2$ 正，所以引理102.6把剩余四腿送入原 $C_4$。
在向量上，$\langle I_k|$ 收缩给

$$
\sum_{t=0}^1|A_t\rangle\!\rangle\otimes|B_t\rangle\!\rangle.
\tag{102.25}
$$

将剩余腿从 $(i_{\rm r},i_{\rm o},j_{\rm r},j_{\rm o})$ 排成
$(i_{\rm r},j_{\rm r},i_{\rm o},j_{\rm o})$，(102.25)恰为 $|U\rangle\!\rangle$。
因此密度矩阵收缩恰给 $|U\rangle\!\rangle\langle\!\langle U|$，
位于参考角 $(i,j)$ 和输出角 $(i,j)$；其余参考／输出角为零。
这正是定义(102.14)的 $J(F_{ij,U})$。这里所用的 $C_4$ 正性是原切片的结论，
不是四份 PSD 假设。
用 Bell 资源传递门的张量收缩形式是成熟构造，参见 Gottesman–Chuang，
[*Demonstrating the viability of universal quantum computation using teleportation and single-qubit operations*](https://arxiv.org/abs/quant-ph/9908010)。
本处所需的附加推导是该指定收缩在尚未确定的原 $C_6,C_4$ 中保持正性，
以及下面的整空间正补与预算；不将资源接线本身另认作新的门传递原理。

由桥基的正交性和 $A_0,A_1$ 的互补性，

$$
\|\alpha\|^2=\operatorname{Tr}(A_0^*A_0+A_1^*A_1)=d,\qquad
\|\gamma\|^2=\operatorname{Tr}(B_0^*B_0+B_1^*B_1)=2e.
\tag{102.26}
$$

又 $X=X^*=X^{-1}$，故 $U=U^*=U^{-1}$，
$\||U\rangle\!\rangle\|^2=\operatorname{Tr}(U^*U)=de$。
$\beta_k/b$ 在整个原二份效应区间内，因为
$0\le\Omega_k/b\le\mathbf1$。
归一资源各带因子 $1/d,1/(2e)$，proper 帽带 $1/b$，给出(102.21)。
质量 $1/(2b)$ 是这两个指定资源在该帽下的输出质量。
对任意待处理输入执行某个门时，尚须连接输入并满足相应事件预算；
(102.21)不是该门无条件成功的概率或确定性实现。
在数学正锥中除以正系数只恢复 $J(F_{ij,U})$ 的正性，不放大实际事件。

引理102.7在 $m=n=2$ 给 $F_{ij,U}$ 的全部原旁观正性。
引理102.8使(102.22)中的每一补项原旁观正；这里使用正投影之和，
没有从一个正映射任意减去另一个。
记此和为 $Q=\mathrm{id}-P_{ij}$，则向量空间恒等式为

$$
F_{ij,U}^2=P_{ij},\quad Q^2=Q,\quad
F_{ij,U}Q=QF_{ij,U}=0,\quad G_{ij,U}^2=\mathrm{id}.
\tag{102.27}
$$

对任意二份向量 $x$，选定块的迹由酉共轭保持，其余块的迹由 $Q$ 保持，
所以 $u_2G_{ij,U}=u_2$。
$G_{ij,U}$ 自身就是其正逆；张量旁观提升同样自逆并保持 $u_N$。
因此它在每个原联合锥上都是数学自同构。∎

### 102.6 异维、多块与精确有限字

**引理 102.10（每个原扇区上的精确酉覆盖）。** 对固定 $N$，令 $\Gamma_N$ 为
引理102.8的局域块酉与引理102.9的二体 $G_{ij,U}$ 的全部原提升所生成的有限字群。
允许用原置换把二体映射置于任意两条不同腿。
每个群元素在每个扇区上都是酉共轭，并是整个 $C_N$ 的保质量正自同构。
对每个固定 $s\in I^N$ 和每个 $U_s\in U(D_s)$，存在一个此类有限字，
其在 $\operatorname{Herm}(\mathcal H_s)$ 上的限制恰为 $\operatorname{Ad}_{U_s}$。
有限字可在其他扇区上产生相伴的作用；不要求独立指定整个酉元组。

**证明。** 每个生成元及其逆均已在所有原旁观系统上取得正性，且保持每个标签扇区。
在(102.10)的纯向量坐标中，它们可表示为各扇区酉的一个元组。
取这些元组的有限字群；其伴随作用给 $\Gamma_N$。
因子置换用于把一个已有正提升置于指定腿，所得置换共轭后的生成元仍保持原标签位置。

固定 $s$，只须证明有限字元组在该分量的投影覆盖所需酉共轭。
令活跃腿为 $n_{s_t}\ge2$ 的腿，其数目为 $q$。
若 $q=0$，$D_s=1$，任何酉共轭都是恒等，空字足够。
若 $q=1$，唯一活跃腿的任意局域酉已覆盖 $U(D_s)$ 的伴随作用。
标量腿的相位在共轭上无作用，任意所需总体相位也可由一个局域相位提供。

对活跃腿列表的长度归纳，只在已加入的腿上构造字，其余腿均作旁观者。
对 $q\ge2$，假定前 $q-1$ 条活跃腿的联合 Hilbert 维数是
$D=\prod_{a<q}n_{s_{t_a}}$，最后一条的维数是 $e=n_{s_{t_q}}$。
归纳假设给该固定前缀扇区上的每个 $U(D)$；其每个有限字都由同一批低体生成元组成，
这些生成元已有任意原旁观提升，故整字可在最后一腿上提升为恒等。
最后一腿提供全部 $U(e)$。这在固定目标扇区中给出全部
$U(D)\otimes U(e)$，并未假定高阶 PSD 或一个新的整体控制菜单。

选前缀中的一条活跃腿，维数为 $d\ge2$，其余前缀维数乘积为 $h$，故 $D=dh$。
将引理102.9的门放在该腿与最后一腿。以“整个前缀、最后一腿”分块，
它限制为

$$
V=(I_D-Q)\otimes I_e+Q\otimes X,\qquad
Q=P\otimes I_h,\quad \operatorname{rank}Q=h,
\tag{102.28}
$$

其中 $0<h<D$。取单位向量 $a_1\in\operatorname{im}Q$、
$a_0\in\ker Q$，以及被 $X$ 交换的 $|0\rangle,|1\rangle$，则

$$
V\left(\frac{a_0+a_1}{\sqrt2}\otimes|0\rangle\right)
 =\frac{a_0\otimes|0\rangle+a_1\otimes|1\rangle}{\sqrt2}.
\tag{102.29}
$$

右侧的两侧 Schmidt 秩为二，故此 $V$ 是 imprimitive。
现在只调用 Harrow，
[*Exact universality from any entangling gate without inverses*](https://arxiv.org/abs/0806.0631v1)，
推论2：全部 $U(d_A)\otimes U(d_B)$ 加一个 imprimitive 双体酉，
以精确有限乘积给出 $U(d_A d_B)$。
该推论的两个维数无需相等；这里精确代入 $d_A=D,d_B=e$。
它的局域前提由归纳有限字与最后一腿局域酉支付，imprimitive 前提由(102.29)支付。
得到任意目标 $U(De)$ 的有限字；将每个前缀局域因子换成已取得的原有限字，
所得仍是有限字，所有映射均在同一个原 $N$ 份载体上。
Harrow 的结果承担这里的精确生成步骤；不用稠密性冒充精确性，
也不另作逆函数定理证明。

归纳覆盖所有活跃腿，标量腿保持恒等。
若只跟踪伴随作用，任意无关总体相位直接消去；若跟踪酉代表，局域相位可精确补齐。
构造对每个固定扇区成立，而没有声称
$\Gamma_N\to\prod_sU(D_s)$ 满射。
其他扇区上的相伴作用仍为酉共轭并保持原锥，足够供后面的单扇区态与效应使用。∎

### 102.7 全部原态与全部原效应的双向夹逼

**定理 102.11（三份比较强制全有限原锥）。** 在定义102.1的同一全有限强分块层级上，
使用约定102.4列明的 B1—B3 供应结果，则以下三种条件等价：

1. 原三份比较满足 $S_3$，或等价地满足 $\mathsf{CB}_3$。
2. 原比较同时满足 $S_1,S_2,S_3$。
3. 存在非空有限 $I$、整数 $n_i\ge1$ 和一个固定实线性 $\theta$，使对全部有限 $N$，

$$
\begin{aligned}
\theta^{\otimes N}(C_N)
 &=\bigoplus_{s\in I^N}\operatorname{Herm}_+(\mathcal H_s),\\
u_N(x)&=\sum_{s\in I^N}\operatorname{Tr}\bigl(\theta^{\otimes N}x\bigr)_s.
\end{aligned}
\tag{102.30}
$$

原状态产品、原效应产品、原配对、原全部置换和原重括号在这一套坐标中是标准有限
$A=\bigoplus_iM_{n_i}(\mathbb C)$ 的张量幂数据。
此结论允许经典块、多个不等大小的块和只有一个高维简单块。

**证明。** 命题102.3给 $1\Leftrightarrow2$，并给可替换的三份电路入口。
由条件2应用 B1—B3，固定(102.8)—(102.10)的同一个 $\theta$。
以下证明对每个 $N$ 都有 $C_N=\mathsf D_N$。

先证 $\mathsf D_N\subseteq C_N$。任取扇区 $s$，在每条腿的块 $s_t$ 选一个单位向量
$v_t$，令

$$
p_s=\bigotimes_{t=1}^N|v_t\rangle\langle v_t|.
\tag{102.31}
$$

每个局部因子是原 $C_1$ 中的纯态，重复最小界给 $p_s\in C_N$，
且它仅支撑在扇区 $s$。
对 $\mathcal H_s$ 中任意单位向量 $\psi$，选一个 $U_s$ 将 $\bigotimes_tv_t$ 送到 $\psi$。
引理102.10给整个原锥的数学自同构 $g$，其在该扇区上限制为 $\operatorname{Ad}_{U_s}$。
所以 $g(p_s)=|\psi\rangle\langle\psi|\in C_N$，其他扇区仍为零。
有限维谱分解把任意单扇区 PSD 写成这些秩一态的非负有限和。
对全部有限扇区求和，得第一包含。$D_s=1$ 时这只是正射线，使用空字即可。

再证 $C_N\subseteq\mathsf D_N$。取任意原 $x\in C_N$。
引理102.8已证明 $x_s=P_sx\in C_N$ 及整锥直和。
用与(102.31)相同的局域秩一投影作为迹效应，得到乘积泛函

$$
e_s(y)=\operatorname{Tr}(p_s y_s).
\tag{102.32}
$$

这是原 proper 效应：每个局部投影属于原 $\mathcal E_1$，
最大界使它们的乘积正。
若 $f\in\mathcal E_a$、$g\in\mathcal E_b$，则

$$
u_{a+b}-f\otimes g
 =(u_a-f)\otimes u_b+f\otimes(u_b-g)\in C_{a+b}^*.
\tag{102.33}
$$

因此乘积也满足单位上界，归纳给(102.32)的 proper 性。
对任意单位 $\psi\in\mathcal H_s$，取前段的同一个类型的有限字 $g$。
其实际数学逆在整个原 $C_N$ 上正且保质量，故
$e_s\circ g^{-1}\in\mathcal E_N$。
在原正向量 $x_s$ 上读它，得到

$$
0\le(e_s\circ g^{-1})(x_s)
 =\operatorname{Tr}\bigl(U_s p_s U_s^*x_s\bigr)
 =\langle\psi|x_s|\psi\rangle.
\tag{102.34}
$$

所有单位向量二次型非负，故 $x_s\succeq0$。
所有扇区皆如此，给出反向包含。
这里原效应沿一个已取得正逆的映射运输；未用高阶自对偶或预设高阶纯传递。
前段得到的酉覆盖只须在一个所测扇区上正确，其他扇区上的相伴作用不影响该读数。

由此对全部 $N$ 有(102.30)。同一 $\theta^{\otimes N}$ 与简单张量张成保持乘积，
原配对决定全部对偶识别；原单位及置换已在定义102.5中固定，所以整套数据同时标准。

反过来，在标准有限 $A$ 的张量幂中，闭尖生成与严格正迹成立。
对每个实际分块，PSD 的正乘积仍 PSD；对任意两块正迹效应 $F,G$，
$F\otimes G\succeq0$，故其对所有联合 PSD 的读数非负。
因此两个界成立，全部因子置换是酉运输，单位与配对为原标准形式。
对原纯秩一投影 $p$，确认它的 proper 矩阵效应 $E$ 满足 $E\ge p$，
而 $p$ 自身是 proper；所以 $T_p(x)=\operatorname{Tr}(px)$。
有限准备线性及迹配对对称性给全部 $S_N$，特别是条件1。
该 least 断言的块内论证也在推论102.12中展开。
拉回任意固定 $\theta$ 保持所有这些关系，完成等价。∎

### 102.8 Born 配对、高阶比较与原纯态几何

**推论 102.12（全效应、全部高阶 $S$ 与射影分层）。** 在定理102.11的任一等价条件下，
对全部 $N$，原归一态、全部 proper 效应及有限测量分别为

$$
\begin{aligned}
K_N&=\{(\rho_s):\rho_s\succeq0,\ \sum_s\operatorname{Tr}\rho_s=1\},\\
\mathcal E_N&=\{(E_s):0\preceq E_s\preceq I_{D_s}\},\\
(E_a)_a\text{ 为测量}&\quad\Longleftrightarrow\quad
 E_{a,s}\succeq0,\quad\sum_aE_{a,s}=I_{D_s}\quad(\text{每个 }s).
\end{aligned}
\tag{102.35}
$$

相应概率为原 Born 配对

$$
\Pr(a\mid\rho)=\sum_s\operatorname{Tr}(E_{a,s}\rho_s).
\tag{102.36}
$$

原纯态与比较为

$$
P_N=\coprod_{s\in I^N}\mathbb{CP}^{D_s-1},\qquad
T_p^{(N)}(x)=\operatorname{Tr}(p x_s)
\quad\bigl(p\text{ 在 }s\text{ 块}\bigr).
\tag{102.37}
$$

因此所有高阶 $S_N$ 都成立。不同扇区纯态比较为零；同扇区的单位向量代表满足
$T_{|\psi\rangle\langle\psi|}(|\varphi\rangle\langle\varphi|)
=|\langle\psi,\varphi\rangle|^2$。

**证明。** 定理102.11给整个原正锥等于标准直和 PSD，非退化迹配对把整个原对偶锥
识别为同一个 PSD 直和。上下单位界逐块就是(102.35)。
测量是正效应的有限单位分解，故概率和为一，且(102.36)就是原配对。

单扇区单位秩一投影是归一基极点。若一个态在两个扇区具有正质量，
按扇区质量分解即不是极点；若只在一个扇区而矩阵秩大于一，谱分解也不是极点。
反之，秩一 PSD 的任何正分解都支撑在同一射线上，归一化使分解平凡。
得到(102.37)的纯态描述。

取块 $s$ 的 $p=|\psi\rangle\langle\psi|$。若 $0\le E\le\mathbf1$ 且
$\operatorname{Tr}(E_s p)=1$，则
$\langle\psi|(I-E_s)|\psi\rangle=0$。
正矩阵平方根给 $(I-E_s)\psi=0$，所以 $E_s\psi=\psi$；
Hermitian 性消去 $\mathbb C\psi$ 与其正交补之间的交叉项。
$E_s-p$ 在正交补上等于 $E_s$，故为正；其他块的 $E_t$ 也正。
因此整个 $E\ge p$，而 $p$ 本身确认 $p$ 并 proper，说明 $p$ 是 least 确认效应。
这给任意原正 $x$ 的下确界式。线性与 $\operatorname{Tr}(pq)=\operatorname{Tr}(qp)$
直接给全部(102.5)。

归一混态可写成扇区质量 $w_s=\operatorname{Tr}\rho_s$ 与块内态：
$w_s>0$ 时 $\rho_s=w_s\widehat\rho_s$，$\operatorname{Tr}\widehat\rho_s=1$；
$w_s=0$ 时 $\rho_s=0$，无需指定条件块态。
这给经典概率单纯形上的量子块分层；$D_s=1$ 的射影空间是一个点。
在 $D_s=2$ 的简单块才出现 Bloch 三球，其他维数的射影几何仍保留。
全部结论来自同一原基与原效应区间，没有替换成选定的正子模型。∎

### 102.9 原旁观正映射、跨扇区 CP 与逐输入预算

**命题 102.13（自身 Choi 的完整矩形分量描述）。** 在定理102.11的层级中，取任意有限
$m,n\ge1$，写输入扇区 $s\in I^m$、输出扇区 $t\in I^n$。
对实线性 $F:W_m\to W_n$，以下条件等价：
原旁观正性(102.11)；$J(F)\in C_{m+n}$；每个矩形分量
$F_{t,s}:M_{D_s}(\mathbb C)\to M_{D_t}(\mathbb C)$ 的复线性扩张完全正。
它们也等价于有限 Kraus 表达

$$
(Fx)_t=\sum_{s,\alpha}K_{t,s,\alpha}x_sK_{t,s,\alpha}^*,\qquad
K_{t,s,\alpha}:\mathcal H_s\to\mathcal H_t.
\tag{102.38}
$$

允许 $D_s\ne D_t$、$s\ne t$；零分量取空 Kraus 族。
在这些等价条件下，$F$ 的原保质量／不增质量条件分别恰是

$$
B_s:=\sum_{t,\alpha}K_{t,s,\alpha}^*K_{t,s,\alpha}
 =I_{D_s}\quad\text{／}\quad B_s\preceq I_{D_s}
\quad\text{对每个输入 }s.
\tag{102.39}
$$

**证明。** 原 Choi 当且仅当已在未假设高阶 PSD 时由引理102.7证明。
现在定理102.11允许将其整个原 Choi 锥识别为标准 $\mathsf D_{m+n}$。
其 $(s,t)$ 块是

$$
J(F)_{s,t}=\sum_{a,b=1}^{D_s}E_{ab}^{(s)}\otimes F_{t,s}(E_{ab}^{(s)}).
\tag{102.40}
$$

未触动的参考标签 $s$ 保留了输入扇区；不同输入分量没有在输出中被平均。
所以全 Choi 正性逐块测试每个(102.40)，包括改变扇区的分量。
在每一块应用 Watrous，*The Theory of Quantum Information*，定理2.22、2.26，
其精确来源及矩形、零分量和逐输入预算的应用见
[既有完整通道与有限扇区笔记](../../../Library/Quantum/watrous2018theory.md#one-actual-self-reference-for-finite-sector-operations)。
该成熟 Choi／Kraus 定理给每个非零矩形分量的完全正性及(102.38)；
零分量直接为零映射。这里不重新证明这一表示定理。

对任意 $x\in C_m$，迹循环性给

$$
u_n(Fx)=\sum_s\operatorname{Tr}(B_s x_s).
\tag{102.41}
$$

逐个输入扇区测试任意秩一正 $x_s$，说明与 $u_m(x)$ 比较的必要充分条件正是
(102.39)；空 Kraus 和为零，零映射也在不增质量类中。
这是逐输入块预算，不能只比较整个 Choi 元素的总迹。
同一预算在自身 Choi 坐标中为

$$
\sum_t\operatorname{Tr}_{\mathcal H_t}J(F)_{s,t}=B_s^{\mathsf T}.
\tag{102.41a}
$$

所以原旁观正映射锥经 $J$ 恰为整个原 $C_{m+n}$，CP-TNI 与 TP 分别是其
逐参考块边缘不超过 $I_{D_s}$ 与等于 $I_{D_s}$ 的切片。
若用 $J(F)/R^m$，参考边缘相应不超过或等于
$\sigma_m=\bigoplus_s I_{D_s}/R^m$；$\operatorname{Tr}\sigma_m=1$，
因为 $\sum_sD_s=R^m$。
这是相关态锥的完整边缘条件，不由总归一质量替代。

这些等价也推出任意矩阵参考维数上的常规 CP 正性，因为每个已取得的 Kraus 项
与参考恒等张量后仍保持 PSD。该结论在原锥已经确定之后得到，
没有把任意矩阵参考当作初始可用系统。
原参考只用了输入自身的 $m$ 份拷贝。∎

**定义 102.14（额外的事件饱和选择）。** 在上述固定层级上，数学分支指原旁观正且
不增质量的实线性映射；数学仪器是有限族 $(F_a)_a$，其中每项为数学分支，
且 $\sum_aF_a$ 保质量。
若进一步选择一个实际 typed 事件菜单，使它包含全部此类分支及所有此类有限仪器，
并按映射复合与标签求和解释顺序复合和粗粒化，称该选择事件饱和。
事件饱和是相对于已确定几何的额外菜单条件。
仅有态锥、全 proper 效应与比较等式不指定该菜单，也不指定给定效应的唯一更新。

**命题 102.15（饱和选择中的完整仪器与补分支）。** 在定义102.14的额外选择下，
全部数学分支恰是(102.38)—(102.39)的 CP-TNI 映射；有限族 $(F_a)_a$ 为仪器当且仅当
它们有上述矩形 Kraus 族且

$$
\sum_{a,t,\alpha}K_{a,t,s,\alpha}^*K_{a,t,s,\alpha}=I_{D_s}
\quad\text{对每个输入 }s.
\tag{102.42}
$$

任意一个数学分支可补成一个二结果数学仪器，输出可落入与输入不同的扇区。
对归一输入 $\rho$，分支质量 $p_a=u_n(F_a\rho)$ 为概率；
只有 $p_a>0$ 时，$F_a\rho/p_a$ 才定义条件态。

**证明。** 前两项由命题102.13逐输入块应用于 $F_a$ 和其和。
为显式给补，令 $B_s$ 为分支的(102.39)，$D_s'=I_{D_s}-B_s\succeq0$。
任选一个实际输出扇区 $t_0\in I^n$、其单位向量 $v$，及每个输入块的正交基 $(e_{s,b})_b$。
定义矩形 Kraus 算子

$$
L_{s,b}=|v\rangle\langle e_{s,b}|\sqrt{D_s'}:
\mathcal H_s\longrightarrow\mathcal H_{t_0}.
\tag{102.43}
$$

它们满足 $\sum_bL_{s,b}^*L_{s,b}=D_s'$。
把所有这些分量送到 $t_0$ 得一个 CP 补分支 $H$，
$F+H$ 的每个输入预算正好为单位，故 $(F,H)$ 是数学仪器。
若 $D_s'=0$，相应算子均为零；零分支与零概率结果可原样保留。
输出质量和为一且各项非负；质量为零的正输出向量因严格正单位而为零，
但零向量除以零仍没有定义。

Kraus 复合、标签求和分别保持(102.38)和相应总预算，给出所选菜单中的复合和粗粒化。
这里将数学分支纳入实际事件，使用的是定义102.14的附加饱和选择。
特别地，引理102.9以正倍数恢复的自同构，无需由该资源的某一次后选择确定性实现。
数学正逆、保质量预算、实际事件存在是三个分别陈述的条件。∎

### 102.10 经典、超选择、非 qubit 与比较顺序的边界

**命题 102.16（主定理的不同块型模型）。** 定理102.11的等价条件分别具有如下模型：
任意有限经典代数 $\mathbb C^r$，$r\ge1$；多块非经典代数
$M_2(\mathbb C)\oplus\mathbb C$；单块 $M_3(\mathbb C)$。
因而这些条件不推出非经典块存在、只有一个简单块，或整个局部系统是 qubit。

**证明。** 各取其标准全有限复 C* 张量幂、整 PSD 态锥、迹单位和全效应。
定理102.11的标准层级反向证明已逐项给出全部分块界、置换、原配对及所有 $S_N$。
对 $\mathbb C^r$，每个 $n_i=1$，$K_N$ 是 $r^N$ 点概率单纯形；
所有纯态比较为 Kronecker delta，没有活跃腿，耦合构造完全无需使用。
$r=1$ 的单点情形也满足全部条件。
对 $M_2\oplus\mathbb C$，$K_1$ 的纯态集是 $\mathbb{CP}^1$ 与一个点的不交并，
块间比较恒为零；原整锥有两个非零中心扇区，不能是单个简单块。
对 $M_3$，局部实维为九，纯态集是 $\mathbb{CP}^2$，
与 qubit 的实维四及 $\mathbb{CP}^1$ 不同。
它可有二维子空间，但该子空间不是所给整个局部系统，也未被假定为一个张量因子。∎

**命题 102.17（裸互反与时间先后不能替代准备一致性）。** 一个有限全效应基上的纯端点
数表互反，不必满足准备比较一致性。反之，满足定理102.11的比较互反，
也不使不同测量的时间次序可交换。

**证明。** 第一项取方形基 $K=[0,1]^2$ 的齐次化闭尖锥，单位是齐次坐标，
效应为 $K$ 上全部值在 $[0,1]$ 内的仿射函数。
记四顶点为 $a=(0,0),b=(1,0),c=(0,1),d=(1,1)$。
任意两个不同顶点总有一条坐标不同，选该坐标或其补作效应，就能确认第一点且拒绝第二点。
故 $T_p(q)=\delta_{pq}$，纯端点表完全互反。
然而同一个中点有两种原准备

$$
\frac{a+d}{2}=\frac{b+c}{2},\qquad
\frac{T_a(a)+T_d(a)}2=\frac12,\qquad
\frac{T_b(a)+T_c(a)}2=0.
\tag{102.44}
$$

因此完整准备等式不成立。此例是
[least confirmation 笔记中的方形障碍](../../../Library/QuantumStates/mullerududec2012selfduality.md#an-intrinsic-binary-comparison-and-its-consistency-condition)
在本比较记号下的应用；它不声称方形可满足本章 $S_3$。

第二项在标准 $M_2$ 模型中取
$P=|0\rangle\langle0|$、$Q=|+\rangle\langle+|$、初态 $\rho=P$。
比较值 $T_P(Q)=T_Q(P)=1/2$。
若额外选择相应 Lüders 仪器，先问 $P$ 再问 $Q$ 两次均“是”的概率为

$$
\operatorname{Tr}(QP\rho P)=\frac12,
\qquad
\operatorname{Tr}(PQ\rho Q)=\frac14
\tag{102.45}
$$

是相反先后下的概率。两个分支各为 CP-TNI，连同各自投影补构成仪器，
符合定义102.14的一种饱和选择。
所以交换一次比较的两端点、交换原副本标签与交换有更新的时间顺序，是不同关系。∎

**命题 102.18（条件对应与量词边界）。** 在定义102.1的共同模型域及约定102.4的供应结果下，
三份原比较一致性与全部有限复 C* 张量幂几何等价。
这一对应中，凸混合与全效应是输入；复标量矩阵块及全部高阶 PSD 是结论；
Born 配对是原配对在共同坐标中的表达；数学 CP 分支的事件饱和是附加选择。
这些关系不强制任何给定连续时间生成元或其数值单位。

**证明。** 第一个等价是定理102.11，全部效应、几何及高阶比较由推论102.12给出。
引理102.7以自身原参考检测旁观正性，命题102.13才在已确定几何中把它等价为通常 CP；
定义102.14与命题102.15明确分离预算和事件选择。
本章的 Bell 收缩是线性代数与正锥运算；其中 $\Omega/R$、$\beta/L$ 及
(102.21)的质量因子均保留，因此没有把后选择质量当作免费确定性资源。

对时间结论，可在同一标准层级和同一静态比较数据上，分别指定恒等时间族，
或任取 Hermitian $H_s$ 的族
$\rho_s\mapsto e^{-itH_s}\rho_s e^{itH_s}$。
这些族都保持同一态锥、单位、效应与比较；不同 $H_s$ 给不同时间作用。
任意重标 $t\mapsto ct$ 也保持全部静态输入。
所以静态定理不选择物理钟、数值 $\hbar$、某个 Hamiltonian 或硬件实现。
全部量词只遍历给定的每个有限张量次数，不引入无限维极限、指定误差复杂度或独立物理系统类型。
S3 的较短写法由命题102.3与既有电路等价支付；
这个等价不构成对所有站立条件之逻辑独立性或前提最少性的证明。∎

## 追加锚（本行以下为增补区）
