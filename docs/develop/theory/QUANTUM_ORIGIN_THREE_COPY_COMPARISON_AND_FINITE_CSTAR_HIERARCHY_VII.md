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

## 103. 二份比较与一个共同基相干叉口

### 103.1 低二份接口与资源的量词

**假设 103.1（仅在低二份调用的条件供应）。** 模型始终是定义102.1的原全有限强分块层级，
包括每个实际分块的两个界、全部原置换、固定配对、全部原极点和完整 proper 效应。
本章考察的比较条件仅为(102.5)在 $N=2$ 的 $S_2$，量化全部原二份纯极点及全部有限准备。
以下具名纸面接口作为条件供应使用：

| 接口 | 完整代入 | 使用的输出 |
| --- | --- | --- |
| 低二份 $S$ 到 Jordan | 分别代入 $(W_q,C_q,u_q,K_q,P_q,\mathcal E_q)$，$q=1,2$；$S_1$ 由命题102.3的纯旁观下降取得 | least proper 确认、互反、自对偶正定配对、同框架谱分解、正面投影及其保纯性、保迹 EJA 表示，允许直和 |
| 一个实际自复合 | 只代入 $(W_1,W_1,W_2)$；两因子与复合的上述 Jordan 输出，正双线性态／效应产品、单位与精确配对、乘积效应分离 | 原局部简单块为复矩阵块；原二份扇区的整锥直和、秩与实维乘法，含标量块 |
| 实际两因子产品正规形 | 对每个原扇区 $(i,j)$ 代入已选复型及维数 $n_i,n_j,n_i n_j$；原态与效应产品的正性、全域配对及效应单位 | 固定输出酉与固定输入转置的正规形；标量因子用其单因子边界 |

第一接口指
[reciprocal least confirmation and the spectrality bridge](../../../Library/QuantumStates/mullerududec2012selfduality.md#reciprocal-least-confirmation-and-the-spectrality-bridge)
及其中
[least confirmation forces face-filter purity](../../../Library/QuantumStates/mullerududec2012selfduality.md#least-confirmation-forces-face-filter-purity)。
这里 $S_q$ 的单项准备先给互反，再把任意准备的等式转为 $T_p$ 的仿射性；
完整效应区间使其线性延拓成为一个 proper 确认效应，并低于每个确认效应，故是 least。
反之，least 性与互反给原准备等式。因此代入的是该接口的全部 $S$，不是一张互反数表。
该接口所经的正双极、谱、projectivity 与 filter purity 桥均保留；
Barnum–Müller–Ududec 定理16是其中被调用的成熟分类结果，并不单独断言 $S_2$ 的整条路线。

第二接口指
[sector composites without a connectedness input](../../../Library/QuantumStates/barnumhilgert2019spectral.md#sector-composites-without-a-connectedness-input)
和
[complex sectors from a single self-composite](../../../Library/QuantumStates/barnumhilgert2019spectral.md#complex-sectors-from-a-single-self-composite)。
最小界供应正态产品，最大界供应正效应产品；原实张量空间和配对供应张成、分离与局部层析。
各原中心扇区的限制继承这些输入与完整效应。简单自复合的秩平方、实维平方才供复型选择；
不假设比较图连通、非经典块存在或预选 qubit。
第三接口是
[actual two-factor products after complex-type selection](../../../Library/QuantumStates/barnumhilgert2019spectral.md#actual-two-factor-products-after-complex-type-selection)，
其中 Xu–Zheng–Fošner 的产品秩一保持分类承担正规形步骤，
DOI [10.1017/S1446788714000603](https://doi.org/10.1017/S1446788714000603)。
这些供应是具名条件纸面桥，不将其全链归给任一成熟论文。

具体地，固定一个保迹局部 Jordan 坐标

$$
\theta:V\longrightarrow A_{\rm h},\qquad
A=\bigoplus_{i\in I}M_{n_i}(\mathbb C),\quad
\theta(C_1)=A_+,\quad u\theta^{-1}=\sum_i\operatorname{Tr},
\qquad n_i\ge1.
\tag{103.1}
$$

以后用 $\theta^{\otimes N}$ 只识别原实向量空间，把运输后的原锥仍记 $C_N$。
记 $\mathsf D_N$ 为(102.10)中的标准块 PSD 锥。
低二份供应在这一固定原产品坐标中的结论是

$$
C_2=\bigoplus_{i,j\in I}\Gamma_1^{\epsilon_{ij}}
       \operatorname{Herm}_+(\mathbb C^{n_i}\otimes\mathbb C^{n_j}),
\qquad \epsilon_{ij}\in\mathbb Z/2,
\tag{103.2}
$$

其中 $\Gamma_1$ 只转置第一条腿，绝不表示原锥上的已知正映射。
为核对这一输出，设实际产品在某个二份 Jordan 表示下为
$\Phi_{ij}=\operatorname{Ad}_{U_{ij}}(T_i^r\otimes T_j^s)$。
原固定产品坐标中的锥是 $\Phi_{ij}^{-1}(\mathrm{PSD})$。
因为 $\operatorname{Ad}_{U_{ij}^{-1}}$ 把整个 PSD 锥送回它自身，输出酉在这个整锥拉回中消失；
再利用全部转置保持 PSD，得到 $\epsilon_{ij}=r+s$ 的(103.2)。
这不是把 $U_{ij}$ 宣布为高阶原对称。
若任一因子为标量，该部分转置锥就是 PSD，不可观测的掩码一律取零。
同一个坐标的原对偶为实迹配对；$\Gamma_1$ 是正交自逆线性映射且固定单位，故
$C_2^*$ 也由(103.2)的相同直和锥表示，proper 上界仍是原单位。
这里没有调用三份 Jordan 分类、B3 或普遍 $S_3$。

**定义 103.2（共同基三腿资源 $\mathsf F$）。** 在(103.1)的某一个局部 Jordan 迹坐标中，
每块选一个正交归一向量基 $(|a\rangle_i)_{a=1}^{n_i}$，包括其相位，三条腿使用同一个基。
令

$$
g_i=\sum_{a=1}^{n_i}|a\rangle_i|a\rangle_i|a\rangle_i,
\qquad \Delta_i=|g_i\rangle\langle g_i|,
\qquad \Delta=\bigoplus_i\Delta_i,
\qquad R=\sum_i n_i.
\tag{103.3}
$$

$\Delta_i$ 支撑于原向量扇区 $(i,i,i)$，其他扇区为零。
$\mathsf F$ 是存在上述共同坐标与共同基，使 $\Delta\in C_3$ 的条件。
此时 $u_3(\Delta)=R$，所以 $\Delta/R\in K_3$。
这个条件只指定一个锥元素，不指定物理制备事件；
$\Delta_i$ 的矩阵秩一暂不意味着它是原 $K_3$ 的纯极点。

**命题 103.3（$\mathsf F$ 的被动坐标不变性）。** 定义103.2的存在性不依赖局部 Jordan
迹表示中的酉、转置及等型块重标记。无需假定这些局部改变在原 $C_3$ 上是主动对称。

**证明。** 两个此类表示的转移，逐块为 $x\mapsto U_i xU_i^*$ 或
$x\mapsto U_i x^{\mathsf T}U_i^*$，再作保大小的块重标记。
这是有限复矩阵 Jordan 自同构的标准形式。
前一种把三个位置的基同时变为 $(U_i|a\rangle_i)_a$；后一种变为
$(U_i\overline{|a\rangle_i})_a$。
三腿同时转置是该扇区的全部转置，把 $|g_i\rangle\langle g_i|$ 变为
$|\overline{g_i}\rangle\langle\overline{g_i}|$，所以两种情况下同一原向量的坐标仍恰为(103.3)。
原锥也随坐标被动运输，成员关系保持。逆坐标改变给反向结论。
相位是向量基的一部分：只给一族秩一投影未必确定 $g_i$，本定义对此没有取商。
因此可以把见证基选为计算基；这一步只改表示，不调用三份局域酉正性。
局域酉移过部分转置时只把该酉换为复共轭酉，而其对整个 PSD 锥的作用仍满射；
故相应二份被动运输仍具有(103.2)的掩码形状。∎

### 103.2 未对齐二份锥中的杯、帽与自身判据

**引理 103.4（由 $\Delta$ 支付的 Bell 配对）。** 在假设103.1和 $\mathsf F$ 下，
即使(103.2)的非对角掩码尚未确定，仍有
$\epsilon_{ii}=0$ 对全部 $n_i\ge2$ 成立。
在见证基中定义 $\Omega_i,\Omega,\beta,R,L$ 如(102.13)，其中 $L=\max_i n_i$。
则

$$
\Omega\in C_2,\quad \Omega/R\in K_2,\quad
\beta\in C_2^*,\quad \beta/L\in\mathcal E_2.
\tag{103.4}
$$

用此杯定义(102.14)的 $J(F)$，对任意 $m,n\ge1$、任意实线性 $F:W_m\to W_n$ 有

$$
J(F)\in C_{m+n}
\quad\Longleftrightarrow\quad
(\mathrm{id}_{W_r}\otimes F)(C_{r+m})\subseteq C_{r+n}
\quad\text{对全部 }r\ge0.
\tag{103.5}
$$

这里旁观锥是所有原 $C_r$，输入包括其与被作用腿之间的全部原纠缠。
归一杯与 proper 帽的 $m$ 对蛇式系数仍为 $(RL)^{-m}$。

**证明。** 先用引理102.6；它只消费原最大界与闭锥双极性。
令 $\eta_i=\sum_a|a\rangle_i$，令 $f_i(x)=\langle\eta_i|x_i|\eta_i\rangle$，
在其他局部块取零。$f_i\in C_1^*$，故直接切原 $\Delta$ 的第三腿给

$$
(\mathrm{id}\otimes\mathrm{id}\otimes f_i)(\Delta)=\Omega_i\in C_2.
\tag{103.6}
$$

不需要先取得三份中心投影。若 $n_i\ge2$ 而 $\epsilon_{ii}=1$，
(103.2)将要求 $\Gamma_1\Omega_i\succeq0$。
它却是交换算子，在任意两条不同基向量的反对称向量上有本征值 $-1$，矛盾。
标量块自动标准。因此二份所有对角块的原锥均为 PSD。
对这些块 $0\le\Omega_i\le n_i I$，其余块的帽为零。
利用(103.2)的整锥直和，$\beta$ 及 $u_2-\beta/L$ 对每一块均正，得到(103.4)。
各 $\Omega_i$ 求和给原杯；其迹为 $R$。
若要求切片预算，则 $f_i/n_i$ 是 proper，且从 $\Delta/R$ 切得
$\Omega_i/(Rn_i)$，质量为 $1/R$。
对 $f=\sum_i f_i$，$f/L$ proper，切得 $\Omega/(RL)$，质量为 $1/L$。
由正倍数恢复杯的锥成员关系不把这些系数变成确定性制备概率。

现在(102.16)的矩阵单位恒等式和蛇式逐块适用，它们只要求已取得的对角杯帽。
最小界和原置换把 $m$ 个杯放入原 $C_{2m}$，没有假定这个高阶锥标准。
帽的每次切片由引理102.6作用于当时的整个原剩余输入。
若用 $\beta/L$，对 $z\in C_{b+2}$ 有

$$
0\le (u_b\otimes\beta/L)(z)\le u_{b+2}(z),
\tag{103.7}
$$

因为 $u_b\otimes(u_2-\beta/L)$ 由最大界为正。迭代给全部预算。

正向(103.5)直接把原旁观正映射作用于 $\Omega_m$。
反向令 $z\in C_{r+m}$ 任意；最小界把 $z\otimes J(F)$ 放入
原 $C_{r+2m+n}$，逐对收缩输入和参考腿，再用原置换保留旁观腿与输出腿。
上述整锥切片使所得落入 $C_{r+n}$。
在参考／输出扇区 $(s,t)$，Choi 展开为
$\sum_{a,b}E_{ab}^{(s)}\otimes F_{t,s}(E_{ab}^{(s)})$；
蛇式把 $z$ 的输入系数原样交给 $F$，所以输出恰是
$(\mathrm{id}_{W_r}\otimes F)z$，没有转置余项。
恒等式在简单张量上核对，再由实张量张成推广；正性已对整个原 $z$ 证明。
这正是(102.17)的证明，所用输入已由(103.4)供应，非对角 $C_2$ 是否标准不参与。
归一杯帽只把该输出乘以 $(RL)^{-m}>0$，不改变数学正性。
同一系数展开还给 $J$ 的向量空间双射。全程未引入任意矩阵辅助物。∎

### 103.3 可见掩码的复合约束

**定理 103.5（秩二实角强制共同方向）。** 在引理103.4的坐标中，令
$I_{\rm a}=\{i:n_i\ge2\}$。
存在 $a_i\in\mathbb Z/2$，使全部可见掩码满足

$$
\epsilon_{ij}=a_i+a_j\qquad(i,j\in I_{\rm a}).
\tag{103.8}
$$

同时对每条腿都改用同一个局部坐标 $x_i\mapsto x_i^{T^{a_i}}$，
便有 $C_1=\mathsf D_1$、$C_2=\mathsf D_2$，而同一个 $\Delta$ 仍属于原 $C_3$。
标量块、零个或一个非经典块均包含在结论中。

**证明。** 对任意矩形 $K:\mathbb C^{n_i}\to\mathbb C^{n_j}$，
令 $F_{ji}^K$ 在输入块 $i$、输出块 $j$ 上为

$$
F_{ji}^K(x)=Kx^{T^{\epsilon_{ij}}}K^*,
\tag{103.9}
$$

其余输入／输出分量为零。在“参考、输出”次序中，

$$
J(F_{ji}^K)_{i,j}=\Gamma_1^{\epsilon_{ij}}
 |K\rangle\!\rangle\langle\!\langle K|\in C_2.
\tag{103.10}
$$

引理103.4于是使每个(103.9)原旁观正；这里没有先宣称跨块普通合同正。
原置换交换两个因子，把 $\Gamma_1^{\epsilon_{ij}}\mathrm{PSD}$ 送为
$\Gamma_2^{\epsilon_{ij}}\mathrm{PSD}=\Gamma_1^{\epsilon_{ij}}\mathrm{PSD}$。
在两个活跃因子上，标准与部分转置锥不同：嵌入二维 Bell 投影后部分转置在反对称方向为负。
因此 $\epsilon_{ij}=\epsilon_{ji}$；对角零掩码已由引理103.4取得。

对每个活跃块，在见证基的前两条向量上取实等距嵌入
$E_i:\mathbb C^2\to\mathbb C^{n_i}$，令 $L_{ji}=E_jE_i^*$。
复合 $F_{kj}^{L_{kj}}F_{ji}^{L_{ji}}$ 原旁观正。
因为所有 $E_i$ 在这些坐标中为实矩阵，$E_j^*E_j=I_2$，其非零分量恰是

$$
x\longmapsto E_kE_i^*x^{T^{\epsilon_{ij}+\epsilon_{jk}}}E_iE_k^*.
\tag{103.11}
$$

它的 Choi 元素必须在原 $(i,k)$ 扇区锥内。
令 $\omega_{ik}$ 是向量 $\sum_{a=0}^1 E_i|a\rangle\otimes E_k|a\rangle$ 的 dyad。
对这个 Choi 元素施加 $\Gamma_1^{\epsilon_{ik}}$，得到
$\Gamma_1^{\epsilon_{ij}+\epsilon_{jk}+\epsilon_{ik}}\omega_{ik}$。
若指数为一，其在该二维角的归一反对称向量上读数为 $-1$，不可能 PSD。
所以对全部活跃 $i,j,k$，包括重复标签，

$$
\epsilon_{ik}=\epsilon_{ij}+\epsilon_{jk}.
\tag{103.12}
$$

若 $I_{\rm a}$ 非空，选 $h\in I_{\rm a}$，置 $a_i=\epsilon_{hi}$；
(103.12)给(103.8)，且 $a_h=0$。若只有一个活跃块，这就是其已知的对角零掩码。
若无活跃块，所有二份锥本来就是标量正射线直和，取全部 $a_i=0$。
对所有标量标签也取 $a_i=0$；与标量配对的转置在整个锥上不可见，不施加虚假的边约束。

共同坐标改变后，活跃 $(i,j)$ 上的锥成为
$\Gamma_1^{\epsilon_{ij}+a_i+a_j}\mathrm{PSD}=\mathrm{PSD}$；
有标量因子的块仍标准。这是同一个局部图在全部腿上的使用，未按有序对另选坐标。
在 $(i,i,i)$ 上，三次 $T_i^{a_i}$ 为全部转置；见证基中 $\Delta_i$ 为实矩阵，故保持 $\Delta_i$。
所以原 $\Delta$ 的坐标不变，$\mathsf F$ 在对齐后仍由同一元素见证。
该证明只在尚未标准的 $C_2$ 中使用已取得的自身 Choi 判据和映射复合，
没有从预设三份 PSD 反推二份方向。∎

### 103.4 矩形一体映射与两个指定三腿资源

**引理 103.6（对齐后的一体合同与中心分解）。** 使用定理103.5的同一个局部坐标。
对任意块 $i,j$、任意矩形 $K:\mathbb C^{n_i}\to\mathbb C^{n_j}$，
仅有分量 $x_i\mapsto Kx_iK^*$ 的一体映射原旁观正。
若 $K^*K\preceq I_{n_i}$，它在全部原旁观扩张中不增质量。
局域块酉共轭及其逆在全部原旁观者上正且保质量。
每个 $\Pi_i$ 及每个原多腿中心投影 $P_s$ 都正，且有(102.19)的原整锥直和。

**证明。** 一体矩形合同的 Choi 元素仅在 $(i,j)$ 块非零，为
$|K\rangle\!\rangle\langle\!\langle K|$。
现在 $C_2=\mathsf D_2$，故引理103.4给全部原旁观正性，包括任意原纠缠输入。
正和、复合及张量积保持此性质；张量积可先提升第一映射，再用原置换提升第二映射。
当 $K^*K\preceq I$，$u_1-u_1F$ 是原一体正泛函。
把它与旁观单位相乘，原最大界给全部扩张的不增质量预算。
局域块酉是相应合同的直和，其逆以 $U_i^*$ 替换 $U_i$，迹恒等式给保质量。
取 $K=I_i$、仅保留一个输入／输出块即得 $\Pi_i$。
于是 $P_s$ 正；$\sum_sP_s=\mathrm{id}$ 是整空间恒等式，
每个原正向量都是其正扇区分量之和，反向由锥的加法封闭性成立。
这也重得引理102.8的证明所需全部输入；它无需 $C_3=\mathsf D_3$。
对称与合同是数学原锥映射，预算条件本身不把它们纳入任何物理事件菜单。∎

**命题 103.7（$\Delta$ 供应(102.24)的两个原资源）。** 在定理103.5之后，
取任意活跃 $i,j$，令 $d=n_i\ge2$、$e=n_j\ge2$。
任取 $k$ 满足 $b=n_k\ge2$，可一直取 $k=i$。
对(102.20)的任意秩一 $P$ 和任意基交换 $X$，
(102.24)定义的 $\alpha\alpha^*$ 与 $\gamma\gamma^*$ 分别属于原 $C_3$ 的
$(i,i,k)$ 与 $(k,j,j)$ 扇区。它们的迹分别为 $d,2e$。
这些成员关系可由原 $\Delta$ 经已经取得原旁观正性的一体矩形合同得到。

**证明。** 保持见证基为各源块的计算基。选正交归一 $(f_a)_{a=1}^d$，
使 $P=|f_1\rangle\langle f_1|$。在桥块 $k$ 选两条基向量 $|0\rangle,|1\rangle$。
定义三个从源块 $i$ 出发的矩形算子

$$
K_{\rm r}|a\rangle=|\overline{f_a}\rangle,\qquad
K_{\rm o}|a\rangle=|f_a\rangle,\qquad
K_{\alpha}|a\rangle=
\begin{cases}|1\rangle_k&a=1,\\|0\rangle_k&a\ge2.\end{cases}
\tag{103.13}
$$

前两个输出在块 $i$，第三个输出在块 $k$；对应一体映射在其他源块为零。
由 $|I_d\rangle=\sum_a|\overline{f_a}\rangle|f_a\rangle$，有

$$
(K_{\rm r}\otimes K_{\rm o}\otimes K_{\alpha})g_i
 =|I_d-P\rangle\!\rangle|0\rangle_k
    +|P\rangle\!\rangle|1\rangle_k=\alpha.
\tag{103.14}
$$

此张量映射作用于全 $\Delta$ 时自动消去其他源扇区。
每条一体合同的原旁观正性由引理103.6先取得，所以输出 $\alpha\alpha^*\in C_3$。
这里没有使用原三份锥的一般 PSD 正性。

对 $X$ 选正交归一特征基 $(h_a)_{a=1}^e$，本征值为 $\lambda_a\in\{1,-1\}$。
因为 $X$ 只交换两条基向量，$+1$ 的重数为 $e-1$，$-1$ 的重数为一。
从源块 $j$ 定义

$$
K_{\gamma}|a\rangle=|0\rangle_k+\lambda_a|1\rangle_k,\qquad
H_{\rm r}|a\rangle=|\overline{h_a}\rangle,\qquad
H_{\rm o}|a\rangle=|h_a\rangle.
\tag{103.15}
$$

输出标签分别为 $k,j,j$。矩阵单位向量化给

$$
(K_{\gamma}\otimes H_{\rm r}\otimes H_{\rm o})g_j
 =|0\rangle_k|I_e\rangle\!\rangle
   +|1\rangle_k|X\rangle\!\rangle=\gamma.
\tag{103.16}
$$

同理 $\gamma\gamma^*\in C_3$。不同位置始终是不同张量腿，即使 $i=j=k$ 也不合并。
正交桥基和投影互补性给
$\|\alpha\|^2=\operatorname{Tr}(I_d-P)+\operatorname{Tr}P=d$，
$\|\gamma\|^2=\operatorname{Tr}I_e+\operatorname{Tr}(X^*X)=2e$。

为单独核对预算，置

$$
c_\alpha=\max\{1,d-1\},\qquad c_\gamma=2(e-1).
\tag{103.17}
$$

这里 $c_\alpha,c_\gamma$ 是算子范数的平方：
$K_\alpha K_\alpha^*=(d-1)|0\rangle\langle0|+|1\rangle\langle1|$，
$K_\gamma K_\gamma^*$ 在 $|0\rangle\pm|1\rangle$ 的归一方向上的本征值为
$2(e-1),2$。其余四个算子是酉。
因此把 $K_\alpha,K_\gamma$ 分别除以 $\sqrt{c_\alpha},\sqrt{c_\gamma}$ 后，
全部一体合同均满足 $K^*K\preceq I$，故有原全旁观不增质量预算。
从两个独立的全局输入 $\Delta/R$，分别得到

$$
\frac{\alpha\alpha^*}{Rc_\alpha},\quad
\frac{\gamma\gamma^*}{Rc_\gamma},\qquad
\text{质量分别为 }\frac{d}{Rc_\alpha},\quad\frac{2e}{Rc_\gamma}.
\tag{103.18}
$$

若先写条件源 $\Delta_i/d$ 与 $\Delta_j/e$，相应输出质量为
$1/c_\alpha$ 与 $2/c_\gamma$；从全局源选择这些扇区还分别带权 $d/R,e/R$。
这些条件质量不能替代(103.18)的全局质量。
正锥缩放给归一资源 $\alpha\alpha^*/d$、$\gamma\gamma^*/(2e)$ 属于原 $K_3$；
它不声明物理菜单已经提供上述筛选或条件制备。

现在可复用引理102.9中从资源成员关系之后开始的收缩。
两资源的原乘积在 $C_6$，两条桥腿上 $\beta_k/b$ 是 proper 帽。
收缩与置换给

$$
\operatorname{cap}_{\beta_k/b}
 \left[\frac{\alpha\alpha^*}{d}\otimes
             \frac{\gamma\gamma^*}{2e}\right]
 =\frac{J(F_{ij,U})}{2deb},\qquad
u_4\left(\frac{J(F_{ij,U})}{2deb}\right)=\frac1{2b}.
\tag{103.19}
$$

这逐项等于(102.21)，因为未缩放的桥收缩把向量送到
$|A_0\rangle\!\rangle\otimes|B_0\rangle\!\rangle+
 |A_1\rangle\!\rangle\otimes|B_1\rangle\!\rangle$，重排后为 $|U\rangle\!\rangle$，
其范数平方为 $de$。
若保持(103.18)的全局、不增质量输出而不归一，则相应结果为

$$
\frac{J(F_{ij,U})}{R^2c_\alpha c_\gamma b},\qquad
\text{质量 }\frac{de}{R^2c_\alpha c_\gamma b}
 =\frac{d}{Rc_\alpha}\frac{2e}{Rc_\gamma}\frac1{2b}.
\tag{103.20}
$$

这还支付了源扇区权重。连接一个待处理门输入所需的额外杯帽预算另计；
(103.19)和(103.20)都只是指定资源收缩的质量。
原引理102.9中唯一从 $C_3=\mathsf D_3$ 引入这两个资源的步骤，
在这里已由(103.13)—(103.16)替代。∎

### 103.5 只消费二份标准与指定资源的尾部

**定理 103.8（削弱输入的全有限尾部接口）。** 保持定义102.1的原全有限层级。
假定一个固定局部迹坐标给 $C_1=\mathsf D_1$、$C_2=\mathsf D_2$。
对每个有序活跃块对 $(i,j)$，包括 $i=j$，假定存在一个实际块 $k$、$n_k\ge2$，
以及一个秩一 $P$ 和一个基交换 $X$，使(102.24)的两个指定 dyad 属于原 $C_3$。
不假定整个 $C_3$ 标准，不要求任何 $S_N$，也不假定 $\mathsf F$。
则在这同一个坐标中，全部原有限锥均满足 $C_N=\mathsf D_N$。

**证明。** 引理102.7的杯帽和自身 Choi 证明只需 $C_2$ 标准及原分块界，
故在此全部适用。引理102.8的中心投影、整锥直和与局域酉提升同样只需这个 Choi 判据。
也可逐项使用引理103.6的证明；二者均不消费三份 PSD。

对一个活跃 $(i,j)$，将假设的两个资源在 $C_6$ 中相乘，
按引理102.9的(102.25)收缩桥腿，得到原 $C_4$ 中的 $J(F_{ij,U})$。
这一段只消费原最小界、已正的二份 Bell 帽和原整锥切片，归一预算就是(103.19)。
Choi 反向给角酉映射 $F_{ij,U}$ 的全部原旁观正性。
对其他角作正补

$$
G_{ij,U}=F_{ij,U}+Q_{ij},\qquad
Q_{ij}=\sum_{(h,l)\ne(i,j)}\Pi_h\otimes\Pi_l.
\tag{103.21}
$$

每个补项已经正，没有从任意正映射减去另一正映射。
在整个向量空间上 $F_{ij,U}^2=\Pi_i\otimes\Pi_j$、$Q_{ij}^2=Q_{ij}$，
两个交叉复合为零，故 $G_{ij,U}^2=\mathrm{id}$。
选定角上酉保持迹，其余角恒等，故它及其逆在全部原旁观者上正且保质量。
标量角留在 $Q_{ij}$ 中，也有正预算。
这正是引理102.9的正补结论；它已不需要原三份锥的其他成员。

接着复用引理102.10的精确有限字证明。为明确其较弱输入，固定
$s\in I^N$，只要求有限字在这一个扇区上实现任意 $U(D_s)$ 的伴随作用。
无活跃腿时用空字；一条活跃腿时用已取得的局域酉。
若前缀活跃腿已能精确覆盖 $U(D)$，加入维数 $e\ge2$ 的一条腿。
前缀中的任一活跃腿和新腿给(103.21)的一个门，其在目标扇区上为

$$
(I_D-Q)\otimes I_e+Q\otimes X,
\qquad Q=P\otimes I_h,\quad 0<\operatorname{rank}Q=h<D.
\tag{103.22}
$$

在 $\ker Q$ 与 $\operatorname{im}Q$ 各选一条单位向量，
取其等幅叠加再乘被 $X$ 交换的一条基向量，输出的两侧 Schmidt 秩为二。
所以该门是 imprimitive。
前缀的精确有限字和最后一腿局域酉提供全部 $U(D)\otimes U(e)$。
Harrow，[arXiv:0806.0631v1](https://arxiv.org/abs/0806.0631v1)，推论2，
于是给任意目标 $U(De)$ 的精确有限字；该成熟结果允许 $D\ne e$。
把前缀因子逐个替换为已取得的字仍为有限字，且每个字都有全部原旁观提升。
这里复用的是引理102.10的归纳，不以稠密性替代精确生成。
它不要求同时独立指定全部扇区上的酉元组。
只有一个活跃局部标签时，不同腿仍可重复该标签，所需 $(i,i)$ 资源已在假设中；
没有预选 qubit、第三种非经典物种或额外系统。

最后复用定理102.11证明中的两个包含，而不调用其带 $S_3$/B3 输入的整条定理。
固定一个扇区 $s$，原局部秩一态的乘积 $p_s$ 由最小界在 $C_N$。
精确有限字的原正自同构把它送为该扇区任意 $|\psi\rangle\langle\psi|$，
谱分解及有限扇区求和给 $\mathsf D_N\subseteq C_N$。
反向对 $x\in C_N$，中心投影给 $x_s=P_sx\in C_N$。
局部秩一迹效应的乘积 $e_s(y)=\operatorname{Tr}(p_sy_s)$ 是原 proper 效应：
最大界给正性，逐次使用

$$
u_{a+b}-f\otimes g=(u_a-f)\otimes u_b+f\otimes(u_b-g)\in C_{a+b}^*
\tag{103.23}
$$

给单位上界。沿已经取得正逆且保质量的有限字运输 $e_s$，仍是原 proper 效应。
对每个单位 $\psi\in\mathcal H_s$，选择在该扇区把 $p_s$ 送到
$|\psi\rangle\langle\psi|$ 的字，得到 $\langle\psi|x_s|\psi\rangle\ge0$。
所以每个 $x_s$ PSD，得 $C_N\subseteq\mathsf D_N$。
标量扇区中同一论证只是非负射线及其单位效应；所有补效应均在(103.23)中支付。
其他扇区上的相伴酉作用不影响这一个扇区的态与效应读数。
证明只使用原层级、标准二份锥及两资源，故得到所述削弱接口。∎

### 103.6 完整条件等价与量子公理的对应

**定理 103.9（二份比较加共同叉口的条件等价包）。** 在定义102.1的同一原模型域上，
以假设103.1的具名低二份纸面桥为条件供应，以下条件等价：

1. 全部原二份准备满足 $S_2$，且共同基三腿条件 $\mathsf F$ 成立。
2. $S_1,S_2$ 均成立，且 $\mathsf F$ 成立。
3. 在原一份、二份载体上，每个原纯极点都有 least proper 确认效应，
   纯端点确认互反，且 $\mathsf F$ 成立。
4. 存在一个固定保迹局部坐标 $\vartheta:V\to A_{\rm h}$，
   $A=\bigoplus_iM_{n_i}(\mathbb C)$、$n_i\ge1$，使对每个有限 $N\ge1$，

$$
\vartheta^{\otimes N}(C_N)=\mathsf D_N,\qquad
u_N(x)=\sum_{s\in I^N}\operatorname{Tr}(\vartheta^{\otimes N}x)_s.
\tag{103.24}
$$

在条件4中，全部原产品、配对、置换和重括号同时是标准有限复 C* 张量幂数据。
标量块、多超选择块、不等大小块和重复标签全部保留。

**证明。** 命题102.3在 $a=1$ 给 $S_2\Rightarrow S_1$，所以1与2等价。
假设103.1中已核对的仿射延拓与 least 确认等价，逐个 $q=1,2$ 使2与3等价。
从1使用的供应只到 $(W_1,W_1,W_2)$，得到(103.1)—(103.2)。
命题103.3允许采用资源见证的共同基。
引理103.4先给原杯帽和全部自身旁观 Choi 判据；
定理103.5再统一可见掩码，保留同一 $\Delta$。
引理103.6此后才给普通矩形一体合同的全部原旁观正性。
命题103.7用这些已经支付的映射供应每个活跃对的两个指定资源，取 $k=i$ 即可。
定理103.8的削弱接口推出(103.24)，包括尚未标准的原高阶锥。
这条依赖链没有将 B3、三份 Jordan 性或 $S_3$ 用作中间前提。

反向，在条件4的同一坐标中，任取每块一个正交归一基，(103.3)是标准三份 PSD，
故属于原 $C_3$，给 $\mathsf F$。
标准有限块中，任意纯投影 $p$ 的 least proper 确认效应就是 $p$：
若 $0\le E\le I$ 且 $\operatorname{Tr}(Ep)=1$，则 $E$ 在 $p$ 的像上恒等，
交叉项为零，故 $E\ge p$。不同块取零即可。
因此 $T_p(x)=\operatorname{Tr}(px)$，迹对称与有限准备线性给全部 $S_N$，特别是 $S_2$。
这些是推论102.12中的标准锥计算，不反向使用其 $S_3$ 入口。
共同的局部张量坐标保持原简单张量产品及其张成，原配对决定全部效应坐标，
单位、置换及重括号亦同步保持，完成等价。∎

**推论 103.10（Born、全效应与自身 CP 对应）。** 在定理103.9的等价条件下，
原态、全部 proper 效应、纯极点和全部高阶比较恰为(102.35)—(102.37)，
原概率为 $\sum_s\operatorname{Tr}(E_s\rho_s)$。
对任意有限原 $m$ 份到 $n$ 份映射，原全旁观正性恰为所有矩形跨扇区分量的通常 CP 性，
恰为(102.38)的有限 Kraus 表达；保质量和不增质量分别由(102.39)逐输入扇区预算刻画。

**证明。** 定理103.9已在一个共同坐标中给全部原锥标准。
推论102.12从这一锥等式之后开始的证明，只使用 PSD 的迹对偶、谱分解与 proper 上界，
所以逐项给态、全效应、纯极点及 least/Born 公式；零质量块无需条件态，标量块是一个纯点。
引理103.4已经给原自身 Choi 当且仅当；现在(103.24)才允许把其目标整锥读为 PSD。
因此可直接复用命题102.13的矩形分量证明与其中
[Watrous 定理2.22、2.26的实际参考接口](../../../Library/Quantum/watrous2018theory.md#one-actual-self-reference-for-finite-sector-operations)。
零分量取空 Kraus 族，输入输出维数不必相等；迹循环及逐输入纯态测试给(102.39)。
先前只使用原自身旁观者；任意矩阵辅助物上的 CP 性是此时 Kraus 表达的推论。
成熟表示定理不另作新的表示定理，也不把总 Choi 迹当作逐输入预算。∎

### 103.7 共同基叉口的几何与操作边界

**推论 103.11（原锥上的相干叉口与 Schur 合拢）。** 在定理103.9的条件下，
共同见证基给出两个原全旁观正映射

$$
\begin{aligned}
v_i|a\rangle&=|aa\rangle,\\
(Dx)_{i,i}&=v_i x_i v_i^*,\qquad (Dx)_{i,j}=0\ (i\ne j),\\
(Mz)_i&=v_i^*z_{i,i}v_i.
\end{aligned}
\tag{103.25}
$$

$D:W_1\to W_2$ 保质量，$M:W_2\to W_1$ 不增质量。
它们在实迹配对下满足 $M=D^*$，但二者的原旁观正性各自有资源证明，
并不由未知高阶锥上的取伴随推断。
单位是 $J=\bigoplus_iJ_i$，其中 $J_i=|\eta_i\rangle\langle\eta_i|$ 为全一矩阵，
而不是 $\bigoplus_i I_{n_i}$。

**证明。** 以下正性在定理103.5之后、使用定理103.8之前就已取得。
在“输入参考、输出”次序，矩阵单位展开给

$$
J(D)=\bigoplus_i\sum_{a,b}E_{ab}^{(i)}\otimes E_{ab}^{(i)}\otimes E_{ab}^{(i)}=\Delta.
\tag{103.26}
$$

对 $M$，输入块 $(i,j)$ 不匹配时输出为零；匹配时
$v_i^*(E_{ab}\otimes E_{cd})v_i=\delta_{ac}\delta_{bd}E_{ab}$，所以
其“两个参考腿、一个输出腿”的 Choi 元素也是(103.26)。
这使用的是由原杯乘积构成的 $\Omega_2\in C_4$，并未假定 $C_4$ 标准。
由原 $\Delta\in C_3$ 和引理103.4，分别得到 $D$ 与 $M$ 的全部原旁观正性。
这是两个独立 Choi 代入；$M=D^*$ 只是另由迹恒等式核对的线性代数关系。

因为 $v_i^*v_i=I_i$，$u_2D=u_1$。
令 $Q$ 在匹配二份扇区上为 $v_iv_i^*=\sum_a|aa\rangle\langle aa|$，
其他扇区为零。此时 $0\le Q\le I$ 是原二份 proper 效应，且
$u_1M(z)=\operatorname{Tr}(Qz)\le u_2(z)$。
与旁观单位的最大界把预算提升到所有原纠缠旁观者。
单独的 $M$ 为零的非匹配块也保留其正补预算。

逐块矩阵元给
$M(x\otimes y)_i=x_i\odot y_i$，这里 $\odot$ 是逐项 Schur 乘积，
并且 $MD=\mathrm{id}$。
在每个块的向量基上，$v_i$ 是相干复制基向量的映射，
$v_i^*|ab\rangle=\delta_{ab}|a\rangle$，单位向量为 $\eta_i=\sum_a|a\rangle$。
这些是 Coecke–Pavlovic–Vicary，
[*A new description of orthogonal bases*, arXiv:0810.0812v1](https://arxiv.org/abs/0810.0812v1)，
定理5.1及第6节的成熟正交基／special commutative dagger-Frobenius 对应中的基公式，
DOI [10.1017/S0960129512000047](https://doi.org/10.1017/S0960129512000047)。
在此只把这些已知恒等式嵌入原锥推导，不另立 Frobenius 分类。

具体地，在每个 $|a\rangle$ 上两种迭代 $v_i$ 都给 $|aaa\rangle$，且 $v_i^*v_i=I$。
在 $|ab\rangle$ 上，下面三个算子的作用均为 $\delta_{ab}|aa\rangle$：

$$
v_iv_i^*=(v_i^*\otimes I)(I\otimes v_i)
         =(I\otimes v_i^*)(v_i\otimes I)
\tag{103.27}
$$

故相应合同映射满足交换、结合、special 与 Frobenius 恒等式。
不匹配块上的所有这些复合均为零；匹配块逐块成立，因而可在整个原直和中组合。
令 $q:\mathbb R\to W_1$ 为 $q(1)=J$，则
$M(q\otimes\mathrm{id})=M(\mathrm{id}\otimes q)=\mathrm{id}$，
因为 $J_i\odot x_i=x_i$。
若把单位错取为 $I_i$，Schur 乘积只保留对角元，不能给此恒等式。
相应相干余单位是 $q^*(x)=\sum_i\langle\eta_i|x_i|\eta_i\rangle$，
满足 $(q^*\otimes\mathrm{id})D=(\mathrm{id}\otimes q^*)D=\mathrm{id}$。
$u_1(J)=R$、$J_i\le n_iI_i$，所以 $J/R$ 归一、$q^*/L$ proper；
使用这些归一预算时，单位式分别带 $1/R$，余单位式带 $1/L$，不能删除系数。

对任意 $|\psi\rangle=\sum_a c_a|a\rangle$，
$v_i|\psi\rangle=\sum_a c_a|aa\rangle$。
这是相关的相干振幅，不是 $|\psi\rangle\otimes|\psi\rangle$；
其 dyad 保留 $c_a\overline{c_b}|aa\rangle\langle bb|$ 的非对角项，
因此也不是先去相干再广播的经典通道。
新的原锥内容在于 $\mathsf F$ 使这两条叉口在全部原旁观者上正，
以及它供应了命题103.7的两个资源；上述基恒等式本身是成熟数学。∎

**命题 103.12（静态公理包的范围）。** 定理103.9的等价包确定全部有限原态锥、全效应、
Born 配对和数学 CP 预算，却不指定物理事件饱和、物理钟、Hamiltonian 或数值 $\hbar$。
它不使有更新的测量时间次序可交换，也不推出非经典块存在或超选择块消失。

**证明。** 推论103.10给出这些静态对应。只有额外选择定义102.14的事件饱和菜单后，
才可把全部数学 CP-TNI 分支和(102.42)的有限仪器称为可用事件；
此时命题102.15的补分支证明适用，零质量结果仍不定义条件态。
引理103.6的数学合同、推论103.11的保质量／不增质量，以及资源的正倍数恢复，
均未作这一菜单选择，尤其不能从数学自同构推出某个后选择协议确定性成功。
命题102.17的两个不交换 Lüders 次序就在同一标准层级中，故不改变本公理包。
命题102.18中恒等时间族与任意块 Hamiltonian 时间族保持相同静态数据，
重标时间也保持它们，故静态输入不固定钟、生成元或 $\hbar$。
任意有限经典 $\mathbb C^r$、$M_2\oplus\mathbb C$ 与 $M_3$ 的标准层级都满足
$S_2$ 和 $\mathsf F$，直接保留纯经典、多块与非 qubit 边界。

本等价使用了定义102.1的全部有限层级条件，以及明确的低二份条件纸面桥。
它没有断言 $S_2$ 单独足够，也没有给这些站立输入的逻辑独立性、资源最小性或假设数最少性证明。
承重增量是原锥中的方向复合、单一资源到两个指定资源的供应和削弱尾部接口的组合，
属于本仓推导；不把既有引理102.9至命题102.13中的尾部或成熟 Frobenius、精确生成、Choi/Kraus
结果另认作新的文献定理。这是有限层级的条件数学结论，不含无限维极限或物理实现结论。∎

## 追加锚（本行以下为增补区）

## 104. 一个最大扇区的完整相干叉口

### 104.1 条件供应与单扇区资源

**假设 104.1（原层级与低二份 PAPER 供应）。** 始终保留定义102.1的同一原全有限强分块模型：
全部原极点、完整 proper 效应、每个实际分块的 min/max 双界、固定实张量配对、
严格张量单位和全部原正置换。唯一普遍比较输入为定义102.2的 $S_2$。
条件供应逐项取假设103.1的三个具名 PAPER 接口：
在 $q=1,2$ 使用 least confirmation／谱性／正面投影及保纯性到 Jordan 的桥，
其中 $S_1$ 由命题102.3下降；在唯一实际自复合 $(W_1,W_1,W_2)$
使用直和扇区限制、秩与实维乘法的复型选择；最后使用实际两因子产品正规形。
这些接口的完整输入与原文来源均按假设103.1，不调用三份 Jordan 分类或 B3。

因此可选(103.1)的保迹局部 Jordan 坐标，令
$A=\bigoplus_iM_{n_i}(\mathbb C)$、$L=\max_i n_i$、$R=\sum_i n_i$。
在同一个局部坐标的所有张量幂中，低二份输出恰为(103.2)的整锥掩码式，
其原对偶也为该掩码锥，单位为逐块恒等矩阵。
这里的矩阵只表示原向量空间；对 $N\ge3$ 尚无 PSD 结论。
“原旁观正”仍指对每个 $b\ge0$，
$(\mathrm{id}_{W_b}\otimes F)(C_{b+m})\subseteq C_{b+n}$，
包括输入与全部原旁观腿之间的任意纠缠。

**定义 104.2（单最大扇区叉口 $\mathsf F_{\max}$）。** 若 $L\ge2$，
要求联合存在假设104.1的一张局部 Jordan 迹坐标、一个满足 $n_r=L$ 的实际块 $r$，
以及该块的一个包含相位的正交归一向量基 $(|a\rangle_r)_{a=1}^L$，使

$$
g_r=\sum_{a=1}^L|a\rangle_r|a\rangle_r|a\rangle_r,\qquad
\Delta_r=|g_r\rangle\langle g_r|\in C_3.
\tag{104.1}
$$

三条腿使用同一个向量基；$\Delta_r$ 在 $(r,r,r)$ 之外的所有原向量扇区取零。
这是一个原锥成员条件，归一源为 $\Delta_r/L\in K_3$。
它不预设中心投影正，也不预设任何制备事件或原三份纯性。
对 $L=1$ 不要求资源。为分离最大维的用途，另记 $\mathsf F_{r,q}$ 为同样的联合存在条件，
但只用块 $r$ 内前 $q$ 条共同基向量，$2\le q\le n_r$：
其向量和与 dyad 分别为 $g_{r,q}$、$\Delta_{r,q}$，归一源为 $\Delta_{r,q}/q$。
$\mathsf F_{\max}$ 就是某个最大块上的 $\mathsf F_{r,L}$。

**命题 104.3（被动协变与全经典支路）。** 上述资源的联合存在性在保迹局部
Jordan 坐标改变下保持；不需把坐标改变视为原高阶主动对称。
若 $L=1$，全部原有限锥已经是标准经典正交体。

**证明。** 逐块坐标转移为酉共轭或酉共轭后转置，再作等维标签置换，
其标准形式与命题103.3相同。三腿共同酉运输共同向量基；
三腿共同转置将 dyad 送为共轭向量的 dyad，仍使用同一个共轭基。
对不足满维的基先补为正交归一基。原锥随表示被动运输，
资源的原成员关系和支撑秩 $q$ 不变，最大块也仍为最大块。
可据此把资源见证基写成计算基，而不使用未知的三份局域酉正性。
两份整锥仍具有(103.2)的形状。
若 $L=1$，$C_1$ 是有限正交体；正交体与正交体的最小、最大张量锥相同。
沿 $a=N,b=1$ 的实际分块归纳使用双界，便得每个 $C_N$ 的标准正交体。∎

### 104.2 源帽、真实零扩张与非源对角激活

**引理 104.4（单源已支付的整锥帽）。** 在假设104.1和任一 $\mathsf F_{r,q}$ 下，
源对角掩码 $\epsilon_{rr}=0$，整个满维源杯
$\Omega_r=|\sum_{a=1}^{n_r}aa\rangle\langle\sum_{a=1}^{n_r}aa|$ 属于原 $C_2$。
令 $\beta_r(z)=\operatorname{Tr}(\Omega_r z_{rr})$，
在其他二份块取零，则 $\beta_r\in C_2^*$ 且 $\beta_r/n_r\in\mathcal E_2$。
帽对整个原锥 proper，包括未对齐的所有非源块。

**证明。** 取局部正泛函
$f(x)=\langle\eta|x_r|\eta\rangle$，$\eta=\sum_{a=1}^q|a\rangle_r$，
其他块取零。引理102.6是原最大界与闭锥双极性的整锥切片结论，
不消费任何高阶 PSD。切 $\Delta_{r,q}$ 的第三腿得到原 $C_2$ 中的秩 $q$ 杯
$\Omega_{r,q}=|\sum_{a=1}^qaa\rangle\langle\sum_{a=1}^qaa|$。
若 $\epsilon_{rr}=1$，(103.2)要求它的第一腿部分转置为 PSD；
但在前两条基向量的反对称单位向量上，其读数为 $-1$。
故 $\epsilon_{rr}=0$。于是低二份整块分类已给整个 $(r,r)$ 块为 PSD，
从而满维 $\Omega_r\in C_2$。这一步是整块锥的准入，不是从秩 $q$ 资源物理制备满秩杯。
在该块 $0\preceq\Omega_r\preceq n_r I$；其他块的帽为零，其补为单位。
(103.2)的整锥直和与迹自对偶性给所述原正性及 proper 上界。

预算也可直接区分：$f/q$ proper，从 $\Delta_{r,q}/q$ 切得
$\Omega_{r,q}/q^2$，质量 $1/q$。
满维杯的标准归一态是 $\Omega_r/n_r$，
不把前一个切片结果改称后一个确定性输出。∎

**引理 104.5（受限原 Choi 当且仅当与真正零扩张）。** 记
$B_r=\operatorname{Herm}(\mathbb C^{n_r})$，
$\iota_{r,m}:B_r^{\otimes_{\mathbb R}m}\to W_m$
为原向量扇区 $r^m$ 的嵌入，$\pi_{r,m}$ 为相应向量分量提取。
这里先不假定 $\iota_{r,m}\pi_{r,m}$ 原正。
任取实线性 $F:B_r^{\otimes m}\to W_n$，$m,n\ge1$，定义其真实零扩张

$$
F^0=F\pi_{r,m},\qquad
J_{r,m}(F)=
 (\mathrm{id}_{W_m}\otimes F^0)\Omega_r^{[m]}.
\tag{104.2}
$$

$\Omega_r^{[m]}$ 是 $m$ 个实际源杯经原置换排列的“参考、输入”杯，
属于原 $C_{2m}$。则

$$
J_{r,m}(F)\in C_{m+n}
\quad\Longleftrightarrow\quad
(\mathrm{id}_{W_b}\otimes F^0)C_{b+m}\subseteq C_{b+n}
\quad\text{对每个 }b\ge0.
\tag{104.3}
$$

此处 $F^0$ 在其他整个输入扇区为零；结论是在整个原联合锥上成立，
不是只测试支撑在 $r^m$ 的输入。

**证明。** 正向使用原旁观 $b=m$，将 $F^0$ 作用于已在 $C_{2m}$ 的源杯。
反向任取 $z\in C_{b+m}$。
实际最小界把 $z\otimes J_{r,m}(F)$ 放入 $C_{b+2m+n}$，
原置换使 $z$ 的每条输入腿与相应参考腿相邻。
逐对用引理104.4的整锥正帽切片；引理102.6在每一步作用于当时的整个剩余原输入，
因此输出在 $C_{b+n}$，无需投影原 $z$ 或假定其扇区分量正。

核对输出只需线性恒等式：在源矩阵单位上
$\Omega_r=\sum_{a,c}E_{ac}\otimes E_{ac}$，
$\beta_r(x\otimes y)=\operatorname{Tr}(x_r^{\mathsf T}y_r)$。
故每一条帽交还输入的 $r$ 分量，其他块贡献零。
在简单实张量上收缩结果为 $(\mathrm{id}_{W_b}\otimes F\pi_{r,m})z$，
实张量张成给整个空间的等式。
矩阵单位记号使用唯一复线性扩张，所得恒等式仍是原实 Hermitian 空间恒等式。
这支付了零扩张本身，未用尚未取得正性的中心投影。
若用归一杯 $\Omega_r/n_r$ 和 proper 帽 $\beta_r/n_r$，
输出系数为 $n_r^{-2m}$。
每次质量不增由
$(u_2-\beta_r/n_r)\otimes u_{\rm rest}$ 的原正性保证。
没有引入外来矩阵旁观系统，也没有从一个映射正性推断其伴随正性。∎

**引理 104.6（非源扇区对角激活与全局原 Choi）。** 在上述条件下，
全部非经典块的对角掩码为零，即使源维数并不最大。
因此所有完整 $\Omega_i$ 都属于原 $C_2$，并有
$\Omega=\sum_i\Omega_i\in C_2$、$\Omega/R\in K_2$、
$\beta=\sum_i\beta_i\in C_2^*$、$\beta/L\in\mathcal E_2$。
对所有有限 $m,n\ge1$，用这个原全杯定义的 $J$ 满足(103.5)的全局原旁观 Choi 当且仅当。

**证明。** 任取 $n_i\ge2$。在源块和目标块各取前两条实计算基，
记嵌入为 $E_r:\mathbb C^2\to\mathbb C^{n_r}$、
$E_i:\mathbb C^2\to\mathbb C^{n_i}$，置 $K_i=E_iE_r^*$。
定义从输入 $r$ 到输出 $i$ 的映射，其余输入块真实取零：

$$
H_i^0(x)_i=K_i x_r^{T^{\epsilon_{ri}}}K_i^*,\qquad
J_{r,1}(H_i)=
 \Gamma_1^{\epsilon_{ri}}|K_i\rangle\!\rangle
                       \langle\!\langle K_i|\in C_2.
\tag{104.4}
$$

最后的成员关系只用尚未对齐的 $(r,i)$ 掩码块。
引理104.5给 $H_i^0$ 对全部原旁观者正。
先作用于 $\Omega_r$ 的一条腿，再作用另一条腿，原置换许可这两个提升，
所以 $(H_i^0\otimes H_i^0)\Omega_r\in C_2$。
两个 $K_i$ 都实；两个输入转置一起是 $\Omega_r$ 的全部转置并保持它。
因此输出恰为 $\Omega_{i,2}$。
若 $\epsilon_{ii}=1$，同一个反对称读数 $-1$ 与(103.2)矛盾，
故非源对角也标准。标量块的杯本来就是正乘积态。
现在才由各整个对角块的 PSD 分类准入完整 $\Omega_i$。

求和给原全杯；在每个对角块
$0\preceq\Omega_i\preceq n_i I\preceq LI$，其他块为零，
故全帽与其单位补在整个掩码锥的对偶中正。
这些恰是引理103.4在(103.6)之后所需的全部输入。
具体地，最小界供应杯的张量幂，整锥切片供应帽的逐次收缩，
(102.16)的蛇式给任意原纠缠输入上的(102.17)，从而给(103.5)及 $J$ 的实向量空间双射。
归一杯帽的系数为 $(RL)^{-m}$。
这里复用的是该蛇式证明；没有把引理103.4的全框架 $\mathsf F$ 当前提。∎

### 104.3 共同方向与最大维的唯一用途

**定理 104.7（任意秩二以上源统一方向）。** 任一 $\mathsf F_{r,q}$，$q\ge2$，
足以在同一局部被动坐标中给 $C_1=\mathsf D_1$、$C_2=\mathsf D_2$，
且保持原种子 $\Delta_{r,q}$。
该坐标中全部一体矩形合同的真实零扩张在每个原旁观者上正；
局域中心投影及所有多腿中心投影正，原整锥逐扇区直和。
矩形合同若 $K^*K\preceq I$，全部原旁观提升都不增质量。

**证明。** 全局 Choi 已由引理104.6支付。
定理103.5的证明从(103.9)开始只消费掩码式、对角零掩码、原正置换与该 Choi 当且仅当，
不再消费全框架资源。为明确其复合约束，令
$F_{ji}^K(x)_j=Kx_i^{T^{\epsilon_{ij}}}K^*$，其他分量为零；
其 Choi 为(103.10)，所以它原旁观正。
原交换在两个非经典因子上强制 $\epsilon_{ij}=\epsilon_{ji}$，
因为二维 Bell dyad 区分标准锥和部分转置锥。
取每个活跃块上的实二维嵌入 $E_i$，用 $K=E_jE_i^*$，
则 $F_{kj}F_{ji}$ 的 Choi 在 $(i,k)$ 块有转置指数
$\epsilon_{ij}+\epsilon_{jk}$。
该元素必须属于原 $(i,k)$ 掩码锥，二维反对称方向于是强制

$$
\epsilon_{ik}=\epsilon_{ij}+\epsilon_{jk},\qquad
a_i=\epsilon_{ri},\qquad \epsilon_{ij}=a_i+a_j.
\tag{104.5}
$$

这些公式允许重复标签；$a_r=\epsilon_{rr}=0$。
对标量块取 $a_i=0$，其不可观测转置不施加额外约束。
共同被动坐标 $x_i\mapsto x_i^{T^{a_i}}$ 对齐全部二份块。
源块不转置，故种子仍为同一个原元素；即使使用共同全转置，它也是实 dyad。
只有一个非经典块时已由对角激活完成，无额外三标签要求。

此后普通矩形合同的 Choi 只在 $(i,j)$ 块为 PSD dyad，
由引理104.6得全部原旁观正性。
这正支付引理103.6的证明所需输入；其单位预算证明只用
$u_1-u_1F\in C_1^*$ 与实际最大界，故仍完整适用。
取 $K=I_i$ 得局域 $\Pi_i$ 正，提升后相乘得 $P_s$ 正，
$\sum_sP_s=\mathrm{id}$ 才给原整锥直和。
上述中心正性是在所需杯帽和 Choi 之后取得，未用于非源对角激活。∎

**命题 104.8（完整源的截取、归一预算与全框架供应）。** 现在只假设一个完整源
$\mathsf F_{r,n_r}$。对每个 $n_i\le n_r$，在已对齐坐标中选目标块共同计算基，
定义 $T_i:\mathbb C^{n_r}\to\mathbb C^{n_i}$ 为
$T_i|a\rangle_r=|a\rangle_i$（$a\le n_i$），其余基向量送零。
对应一体合同只接受输入块 $r$。它的三腿提升满足

$$
(\operatorname{Ad}_{T_i})^{\otimes3}(\Delta_r/n_r)
 =\Delta_i/n_r,\qquad
u_3(\Delta_i/n_r)=n_i/n_r,\qquad
\text{条件态 } \Delta_i/n_i.
\tag{104.6}
$$

在最大源情形 $n_r=L$，这对每个实际块成立，
$\Delta=\sum_i\Delta_i\in C_3$，从而支付定义103.2的全框架资源。
此处是本章首次使用源维数最大。

**证明。** $T_i^*T_i$ 是源前 $n_i$ 条基向量的投影，
故定理104.7给三条合同的原旁观正性及质量不增。
对源向量的作用是逐项精确截取，输出为
$\sum_{a=1}^{n_i}|aaa\rangle_i$，其 dyad 迹为 $n_i$，给(104.6)。
不同腿即使标签相同仍是不同张量位置。标量目标也只是该公式的 $n_i=1$ 情形。

各输出在原正锥，有限求和给 $\Delta$。
其静态归一态可写成
$\Delta/R=\sum_i(n_i/R)(\Delta_i/n_i)$，是合法凸混合。
这不是说上述全部截取是同一个仪器：
对同一归一源，各分支质量之和为 $R/L$，
若还有其他块则 $R/L>1$；其和在该输入上已不满足仪器预算。
锥内求和、各自条件归一与共同仪器是不同陈述。
若源不最大，此证明只支付 $n_i\le n_r$ 的完整目标叉口；
较大块的对角杯与共同方向仍已由定理104.7支付，
但(104.6)不提供其完整叉口。∎

### 104.4 指定资源与第103章尾部的逐项接合

**命题 104.9（单最大源的两资源权重）。** 在 $\mathsf F_{\max}$ 下，
对定理103.8的每个有序活跃对 $(i,j)$，包括 $i=j$，
取 $d=n_i$、$e=n_j$，桥块可固定为 $k=r$、$b=L$。
命题103.7的任意秩一 $P$、任意基交换 $X$ 所定义的
$\alpha\alpha^*$、$\gamma\gamma^*$ 属于相应原 $C_3$。
令 $c_\alpha=\max\{1,d-1\}$、$c_\gamma=2(e-1)$。
从两份各自归一的同一类型源 $\Delta_r/L$ 经不增质量合同，
可以分别得到

$$
\frac{\alpha\alpha^*}{Lc_\alpha},\qquad
\frac{\gamma\gamma^*}{Lc_\gamma},\qquad
\text{质量 } \frac{d}{Lc_\alpha},\quad
                 \frac{2e}{Lc_\gamma}.
\tag{104.7}
$$

两者用 proper 桥帽 $\beta_k/b$ 收缩，输出及质量精确为

$$
\frac{J(F_{ij,U})}{bL^2c_\alpha c_\gamma},\qquad
\frac{de}{bL^2c_\alpha c_\gamma}.
\tag{104.8}
$$

**证明。** 定理104.7已经支付命题103.7的所有一体矩形合同及任意原旁观提升；
命题104.8支付其源 $\Delta_i,\Delta_j$。
因而可直接使用(103.13)—(103.16)的向量恒等式，
不复证两个资源的标准线性代数构造。
具体输入对应为：参考／输出基 $f_a$ 实现 $P$，
$h_a$ 是 $X$ 的 $\pm1$ 特征基，桥取 $r$ 内两条共同基；
三腿输出分别为 $(i,i,k)$、$(k,j,j)$。
这些恒等式消费完整的 $d$、$e$ 项源叉口，未把它们替换成二维截角。
(103.17)的算子范数平方仍是 $c_\alpha,c_\gamma$。

先对原单源使用 $T_i^{\otimes3}$ 或 $T_j^{\otimes3}$，
再用(103.13)、(103.15)中经范数缩放的三个算子。
每步已原旁观正且不增质量；等价地，可把每条链复合为一个从 $r$ 出发的矩形收缩。
从(104.6)的非条件输出 $\Delta_i/L,\Delta_j/L$ 出发，
得到的正是(104.7)，保留选择质量 $d/L,e/L$。
若改写为条件源 $\Delta_i/d,\Delta_j/e$，
则输出质量 $1/c_\alpha,2/c_\gamma$ 必须再乘这些选择质量。

引理102.9在(102.24)—(102.25)中的未缩放收缩恒等式为
$\operatorname{cap}_{\beta_k}(\alpha\alpha^*\otimes\gamma\gamma^*)=J(F_{ij,U})$，
且 $\operatorname{Tr}J(F_{ij,U})=de$。
最小界、原置换和引理102.6保证整个收缩在原 $C_4$ 中，给(104.8)。
如果另用已归一资源 $\alpha\alpha^*/d,\gamma\gamma^*/(2e)$，
则输出为(103.19)的 $J(F_{ij,U})/(2deb)$，质量 $1/(2b)$；
从(104.7)改成这些条件资源所需的两项归一权重必须相应保留。
如果改用静态全框架态 $\Delta/R$，则(103.18)、(103.20)使用的分母为
$Rc_\alpha,Rc_\gamma,bR^2c_\alpha c_\gamma$；
它们属于另一归一输入，不能替换(104.7)—(104.8)的 $L$。
所有正倍数只恢复锥成员关系，不声明一次后选择确定性实现了门。∎

**定理 104.10（单最大叉口的全有限条件等价）。** 在定义102.1的原模型域与
假设104.1具名低二份 PAPER 供应下，以下条件等价：

1. $S_2$ 成立，且在非经典支路有 $\mathsf F_{\max}$；
2. $S_2$ 成立，且在非经典支路有定义103.2的全框架资源 $\mathsf F$；
3. 存在同一保迹局部坐标 $\theta$，对所有有限 $N\ge1$ 有

$$
\theta^{\otimes N}(C_N)=
 \bigoplus_{s=(i_1,\ldots,i_N)\in I^N}
 \operatorname{Herm}_+
   \left(\bigotimes_{\ell=1}^N\mathbb C^{n_{i_\ell}}\right)
 =\mathsf D_N.
\tag{104.9}
$$

全经典支路中条件1、2均不要求资源。
式(104.9)保持全部原配对、单位及原因子置换。

**证明。** 条件1先由假设104.1取得局部复型和低二份掩码式；
命题104.3允许采用资源共同计算基。
引理104.4—104.6先支付源整锥帽、真实零扩张、所有非源对角杯和全局原 Choi；
定理104.7对齐坐标并支付矩形合同与中心分解。
命题104.8给 $\Delta\in C_3$，故1推出2。

为明确通向全部高阶原锥的输入，直接接合定理103.8，而不把三份 PSD 偷渡为前提：

| 定理103.8的输入或证明接口 | 本章已支付的对应 |
| --- | --- |
| 同一原全有限模型及所有实际分块双界 | 假设104.1完整保留定义102.1 |
| 同一坐标中 $C_1=\mathsf D_1,C_2=\mathsf D_2$ | 低二份供应与定理104.7 |
| 原自身全杯、proper 帽、任意原旁观 Choi | 引理104.6，不需三份整锥标准 |
| 所有中心投影、正补项及局域酉与正逆 | 定理104.7及引理103.6的预算证明 |
| 每个有序活跃对，包括重复标签，所需的两个原三份 dyad | 命题104.9，桥块始终可取 $r$ |
| 两资源原乘积、桥腿收缩、角门的全旁观正性 | 原最小界、整锥帽、引理102.6；权重为(104.8)，Choi 反向由引理104.6 |

从这些输入开始，定理103.8的证明已给正补角门、
每个固定扇区上任意酉的精确有限字，
以及乘积秩一态和全部 proper 效应的双向夹逼。
其使用的精确生成是该定理所引 Harrow 推论2，允许异维；
不改成稠密近似，不要求独立控制整个扇区酉元组。
因此直接得到(104.9)，未重复该成熟尾部。
零个活跃块由命题104.3处理；一个活跃块仍有不同张量腿上的 $(i,i)$ 对，
所以命题104.9正好支付尾部的这一重复标签输入。

条件2推出3也可逐项使用命题103.7与定理103.8；
条件3反向时任取最大块的共同正交归一基，$\Delta_r$ 是原三份 PSD，
故给 $\mathsf F_{\max}$；全框架 $\Delta$ 也为 PSD。
对原任意有限份纯态 $p$，在其扇区中完整 proper 确认效应 $E$ 满足
$E\succeq p$，而 $p$ 本身是 proper 确认效应，
故 $T_p^{(N)}(x)=\operatorname{Tr}(px)$。
这是定理103.9反向及推论102.12的同一标准锥计算，
给全部 $S_N$，特别是 $S_2$。
简单张量张成、原严格张量单位及配对保证坐标运输同时保持产品和置换。
于是三个条件等价。
本结论比较的是假设资源的支撑范围，不证明独立公理数量、逻辑严格弱化、
源维最大条件的必要性或资源最小性。∎

### 104.5 二维种子的原正 retract 与全对偶

**命题 104.11（任意原旁观者中的完整 qubit 角）。** 只假设 $\mathsf F_{r,2}$，
允许 $n_r<L$。采用定理104.7对齐后的坐标，令
$E:\mathbb C^2\to\mathbb C^{n_r}$ 为种子共同实基的等距嵌入，
$P=EE^*$。对每个 $N\ge1$，记
$H_N^{(2)}=\operatorname{Herm}((\mathbb C^2)^{\otimes N})$，定义

$$
j_N=\operatorname{Ad}_E^{\otimes N},\quad
q_N=\operatorname{Ad}_{E^*}^{\otimes N}\pi_{r,N},\quad
p_N=j_Nq_N,\quad
B_N=q_N(C_N).
\tag{104.10}
$$

$\pi_{r,N}$ 只表示向量分量；$p_N$ 是原一体真实零扩张
$x\mapsto Px_rP$ 的张量提升。
则 $q_Nj_N=\mathrm{id}$，$p_N(C_N)\subseteq C_N$，且

$$
B_N=j_N^{-1}(C_N),\qquad
j_N(B_N)=C_N\cap\operatorname{im}j_N=p_N(C_N),\qquad
B_N=\operatorname{Herm}_+((\mathbb C^2)^{\otimes N}).
\tag{104.11}
$$

这些锥继承定义102.1的全部分块 min/max 双界、原置换、迹单位和完整对偶；
特别地，对每个 $N$，

$$
j_N^*(C_N^*)=B_N^*,\qquad
q_N^*(B_N^*)\subseteq C_N^*,\qquad
j_N^*(\mathcal E_N)=[0,\operatorname{Tr}]_{B_N^*}.
\tag{104.12}
$$

在 $N$ 条这类角腿之间的任意通常 CP 映射，其真正角零扩张对所有原纠缠旁观者正。

**证明。** 定理104.7的一体矩形合同先给原全旁观正性，
故 $p_N$ 是原正幂等，且不增质量；这里不从 $j_N$ 或其伴随的正性作推断。
$q_Nj_N=\mathrm{id}$ 是线性恒等式。
对 $x\in C_N$，$j_Nq_Nx=p_Nx\in C_N$；
反之 $j_Ny\in C_N$ 蕴含 $y=q_Nj_Ny\in B_N$。
这证明(104.11)的前两个等式，
并把 $B_N$ 识别为闭锥与一个子空间的交，因此是闭的。
尖性由 $j_N$ 单射及原尖性给出；
它包含所有 qubit 正乘积，故生成 $H_N^{(2)}$。
$\operatorname{Tr}y=u_N(j_Ny)$，在 $B_N\setminus\{0\}$ 上严格正。

若 $f\in B_N^*$，则 $f\circ q_N\in C_N^*$，
因为 $q_N(C_N)=B_N$；其沿 $j_N$ 的限制恰为 $f$。
任意原正泛函沿 $j_N$ 限制也正，给(104.12)的前两项。
更精确地，令 $v_N=u_N\circ p_N=\operatorname{Tr}\circ q_N$，
原旁观不增质量给 $0\le v_N\le u_N$。
若 $0\le f\le\operatorname{Tr}$，其延拓满足
$0\le f\circ q_N\le v_N\le u_N$，
所以是原 proper 效应，且精确限制为 $f$。
反向原 proper 效应的限制介于零与 $u_Nj_N=\operatorname{Tr}$ 之间，
给(104.12)最后一项。
因此所继承的是全效应与全对偶，不是选定菜单的限制。

为验证每个实际分块，$x\in B_a,y\in B_b$ 的嵌入乘积属于原 $C_{a+b}$，
再提取回去给最小界；闭包也保持。
若 $z\in B_{a+b}$，则 $j_{a+b}z\in C_{a+b}$；
任意 $f\in B_a^*,g\in B_b^*$ 各延拓成
$fq_a,gq_b$，原最大界给
$(f\otimes g)(z)=((fq_a)\otimes(gq_b))(j_{a+b}z)\ge0$。
所以最大界使用了整个新对偶，而非仅产品态上的检查。
同一个 $E$ 使原置换、重括号和迹单位精确继承。
$B_1$、$B_2$ 已分别是标准 qubit 一、二份 PSD；
种子 $\Delta_{r,2}$ 在此 retract 中恰为完整二维叉口。
对这一原正 retract，复用命题103.7与命题104.9中从已正矩形合同开始的两资源构造：
唯一块维数二，完整二维种子支付定理103.8所需的两个指定资源，
该尾部的其余全部输入已在本段逐项证明，故直接应用定理103.8。
因此得(104.11)最后的全有限等式，不需对 retract 重新调用低二份 PAPER 分类。

最后任取 qubit 寄存器 CP 映射 $\Phi:H_m^{(2)}\to H_n^{(2)}$。
定义全原向量空间上的真正角零扩张
$\Phi^0=j_n\Phi q_m$；它压缩掉同一原块内角与角外的交叉矩阵元，
也消去其他输入扇区。
其原 Choi 元素为
$(j_m\otimes j_n)J_2(\Phi)$。
种子基的 $E$ 为实嵌入，故参考腿没有额外共轭；
一般基可相应把参考嵌入写为 $\overline E$。
$J_2(\Phi)\succeq0$ 属于已证明的 $B_{m+n}$，
(104.11)使其嵌入属于原 $C_{m+n}$，
全局原 Choi 因而给 $\Phi^0$ 的全部原旁观正性。
这是对未知全高阶锥中角零扩张的证明，不是把 qubit 内正性直接外推。
通常 CP 的 Choi 定理在这里仅用于已标准的 qubit 寄存器。
其他实际块内任意二维角可用已支付的一体矩形合同及其反向压缩运输同一结论。∎

### 104.6 有限二维成果与具名融合接口

**定义 104.12（寄存器到最大原块的 $\mathsf{Fusion}_L$）。** 在
$\mathsf F_{r,2}$ 的上述已标准 qubit retract 中，任取最大块 $s$，
$n_s=L\ge2$，置 $m=\lceil\log_2L\rceil$，
在块 $s$ 选正交归一基 $|a\rangle_s$，$0\le a<L$。
令 $|x\rangle_Q$ 表示 $m$ 个实际种子角腿中的计算基，
其中 $x=\operatorname{bin}_m(a)$。定义

$$
\eta_L=\sum_{a=0}^{L-1}|\operatorname{bin}_m(a)\rangle_Q\otimes|a\rangle_s,
\qquad
\mathsf{Fusion}_L:\quad |\eta_L\rangle\langle\eta_L|\in C_{m+1}.
\tag{104.13}
$$

它支撑于原输入参考的种子角和一个原输出块，
不是另加一个抽象矩阵辅助系统。
该条件只在本节作为具名充分接口；不包含在二维种子的定义中。

**命题 104.13（融合接口的准确充分性与边界）。** 二维种子已经支付定理104.7及
命题104.11的全部结论；若再有 $\mathsf{Fusion}_L$，则支付 $\mathsf F_{\max}$，
因而得到定理104.10的全原层级。
当 $L=2$，融合接口已由标准原 $C_2$ 支付，二维种子本身足够。
当 $L>2$，这里不证明也不否定二维种子单独推出 $\mathsf{Fusion}_L$
或直接推出全原层级。

**证明。** 定义寄存器矩阵
$K:(\mathbb C^2)^{\otimes m}\to\mathbb C^L$，
在 $a<L$ 的计算字上送为 $|a\rangle_s$，其他字送零，
并定义真正原角零扩张 $G^0=j_s\operatorname{Ad}_K q_m$，
其中 $j_s$ 是输出块的向量嵌入。
对全原杯直接展开，$J(G^0)=|\eta_L\rangle\langle\eta_L|$。
因此引理104.6给精确接口

$$
\mathsf{Fusion}_L
\quad\Longleftrightarrow\quad
G^0\text{ 在每个原旁观者上正}.
\tag{104.14}
$$

这是从多条实际腿相干汇入一个较大原块的混合 Choi 准入。
命题104.11末段只处理已标准 qubit 寄存器之间的 CP 映射，
其输出仍是角寄存器；不能把该结论直接替换为(104.14)。

预算也已明确：$K^*K$ 是长度 $L$ 的计算码投影。
在已标准 $B_m$ 中它是 proper 效应；
命题104.11的全效应延拓说明
$u_1G^0=(\operatorname{Tr}\operatorname{Ad}_K)q_m\le u_m$。
若(104.13)成立，$G^0$ 原旁观正，再将此正差与旁观单位相乘，
得到所有原旁观扩张上的质量不增。
最小界取 $m$ 份归一种子 $\Delta_{r,2}/2$，
原置换重排成三组各含 $m$ 条腿的寄存器，态为向量

$$
h_m=\sum_{x\in\{0,1\}^m}|x\rangle_Q|x\rangle_Q|x\rangle_Q
\quad\text{的 dyad 除以 }2^m.
\tag{104.15}
$$

在三组寄存器上分别作用已支付的 $G^0$，
输出恰为 $\Delta_s/2^m$，质量 $L/2^m$；
条件态为 $\Delta_s/L$，所以完整最大叉口属于原 $C_3$。
当 $L=2$，$m=1$，(104.13)就是两个实际二维块之间的 Bell dyad，
已在标准 $C_2$ 中，且上述质量为一；
也可先用定理104.7的一体合同把种子搬到任意最大块。

一般完整源维 $d=n_r$ 不最大时，命题104.8已支付所有 $n_i\le d$ 的叉口。
这些块的原中心限制形成正 retract，沿命题104.11同一全对偶延拓论证继承所有分块界；
故它们组成的每个有限扇区锥也由定理103.8标准化。
这是一条准确局部结论，不对更大原块作补完。
特别是二维种子确定所有有限二维角寄存器，
以及全部至多二维块所组成的完整子层级（若该标签集非空）；
$L>2$ 的其余原块仍缺(104.13)或足以替代它的原相干接口。
未支付某接口不构成原命题反例，也不证明它不能由现有条件推出；
这里没有采用任何张量网络构造类的普遍障碍或逻辑独立性主张。∎

### 104.7 叉口几何、量子对应与静态边界

**推论 104.14（单源叉口／合拢及标准读取）。** 在 $\mathsf F_{\max}$ 的条件下，
最大源的相干分支算子与合拢算子可写为

$$
D_r|a\rangle=|aa\rangle,\qquad
M_r=D_r^*,\qquad
D_rxD_r^*=\sum_{a,c}x_{ac}|aa\rangle\langle cc|,\qquad
M_r(x\otimes y)M_r^*=x\circ y.
\tag{104.16}
$$

它们在其他源扇区及相应角外取零。
这两个映射各自对每个原旁观者正；其原 Choi 元素均为同一个
$\Delta_r$ 的腿排列。
叉口保质量于所选输入块，合拢不增质量。
对其他块的相同结论由命题104.8支付的 $\Delta_i$ 分别取得。
全部有限原态、全效应、Born 配对与数学旁观正映射，
在(104.9)之后恰为推论103.10的标准复 C* 描述。

**证明。** 两个 Choi 代入分别把 $\Delta_r$ 看成“一条参考、两条输出”
和“两条参考、一条输出”，原正置换及引理104.6分别给正性。
$M_r=D_r^*$ 是另由迹配对验证的线性代数关系，
没有从叉口正性推断合拢正性。
$D_r^*D_r=I_r$，而 $M_r^*M_r$ 是两输入腿中
$\operatorname{span}\{|aa\rangle\}$ 的投影；
它是标准原二份块中的 proper 效应。
因此两项预算由原最大界提升到所有原旁观者。
式(104.16)逐矩阵元成立，保留 $a\ne c$ 的相干项；
它不复制任意输入态为 $x\otimes x$。
这是推论103.11的共同基 Frobenius／Schur 几何，
现在资源的初始支撑只有 $(r,r,r)$，其向其他块的权重恰为(104.6)。

定理104.10已给全部原锥等式后，推论103.10的前提全部满足：
迹对偶识别完整 proper 效应为 $0\preceq E_s\preceq I_s$，
归一态满足 $\rho_s\succeq0$、$\sum_s\operatorname{Tr}\rho_s=1$，
Born 读数为 $\sum_s\operatorname{Tr}(E_s\rho_s)$。
全部原纯极点是单扇区秩一投影，全部高阶 $S_N$ 由同一 least 确认计算取得。
原全旁观正映射此后才读成跨扇区矩形 Kraus 族；
其不增质量预算逐输入扇区为
$\sum_{t,\alpha}K_{t,s,\alpha}^*K_{t,s,\alpha}\preceq I_s$。
这些复用的是命题102.13及推论103.10的成熟 Choi／Kraus 读取，
不是在未知高阶原锥中预设通常 CP。∎

**命题 104.15（比较含义与结论范围）。** 单最大叉口条件所确定的是
定理104.10的静态有限锥包；它不确定物理事件菜单、时间演化、物理钟或 $\hbar$。
$S_2$ 的端点互反与准备混合平均不表示时间测量次序可交换。

**证明。** 这里保留原全效应，所以归一态与数学效应的概率读取已由推论104.14确定；
把所有数学 CP-TNI 分支或仪器纳入可用事件仍须定义102.14的额外饱和选择。
命题104.8的多个独立截取甚至不自动满足一个共同仪器的预算。
命题102.17在相同标准层级内给不交换的 Lüders 时间顺序，
命题103.12保留恒等与非平凡 Hamiltonian 时间族共享同一静态数据的边界。
故本章没有新增这些动力学或事件结论，也未涉及无限维。

白话地说，先只在一个最大的非经典扇区放入一只完整的相干三岔：
切去一腿获得源杯，用整锥上的帽把它接到真正的原输入上，
再将这种能力传到其他扇区，统一二份方向。
此后才能把最大的三岔截成每个较小块的三岔，再接上第103章已经证明的有限尾部。
每条截取分支保留自己的质量，几条路线能分别走通不等于能免费合成一次仪器。
若起点只有二维三岔，全部二维角寄存器已经能闭合；
尚未支付的是把多条二维腿相干汇成一条更大原腿的融合接口，
而不是某个被构造法失败证明为不可能的物理过程。

本章单源受限零扩张、非源对角激活与输入压缩的推导属于 repo-derived PAPER 内容，
不主张全球原创或 Lean 核验。
具名低二份桥仍以假设103.1的 PAPER 身份为条件；
其中引用的 Jordan、产品保持分类均按原接口归属。
Choi／Kraus、共同基 Frobenius／Schur 恒等式及精确酉生成是既有结果，
分别沿引理102.7、命题102.13、定理103.8和推论103.11使用。
资源支撑从全框架改为单最大块，不等于已证明独立公理更少；
二维种子的较大块融合边界按命题104.13保留。∎

## 追加锚（本行以下为增补区）

## 105. 实际混合角的互反端点与全有限通道夹逼

### 105.1 原模型、码角与坐标

**假设 105.1（全有限原层级、低二份供应与二维种子）。** 取定义102.1的整个模型域：
非零有限维实空间 $V$，每个整数 $N\ge1$ 的原空间
$W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成凸锥 $C_N$，以及在非零正向量上严格为正的
原张量单位 $u_N=u^{\otimes N}$。归一基、纯极点和 proper 效应始终分别是整个
$K_N$、$P_N=\operatorname{ext}K_N$ 和 $\mathcal E_N=[0,u_N]_{C_N^*}$。
每个实际分块 $a+b=N$ 都满足(102.2)的 min/max 双界；
所有原位置置换及其逆均正，重括号为同一实张量空间的规范识别，
产品配对和单位为(102.3)，不改用另一个联合实现。

普遍比较条件只取整个 $S_2$：对每个原 $p\in P_2$、每个有限原纯准备族
$q_\ell\in P_2$ 和全部 $a_\ell\ge0$、$\sum_\ell a_\ell=1$，要求

$$
T_p^{(2)}\!\left(\sum_\ell a_\ell q_\ell\right)
 =\sum_\ell a_\ell T_{q_\ell}^{(2)}(p).
\tag{105.1}
$$

这里包括原纠缠二份纯态、零权和重复标签；$T$ 仍由整个原 proper 区间的
(102.4)定义。三项条件 PAPER 供应均按假设103.1、104.1的完整输入使用：
在原 $q=1,2$ 的整个基和全效应上，由 least confirmation、互反、谱性、
正面投影及其保纯性到保迹 Jordan 表示，其中 $S_1$ 由纯旁观下降取得；
在实际 $(W_1,W_1,W_2)$ 上，由正态／效应产品、原单位与配对及局部层析，
使用原中心扇区限制、框架秩乘法和实维乘法的自复合复型选择；
在所选复型的每个实际二因子扇区上，使用产品正规形的固定输出酉和固定输入转置分类，
保留标量因子边界。各桥的来源和全部中间条件仍是103.1所列的具名接口，
不将整条桥归给其中任一成熟分类定理。

设 $L=3$，故保留全部 $n_i\in\{1,2,3\}$ 的实际块，包括所有标量块与二维块。
联合给定一个实际 $\mathsf F_{r,2}$ 种子，向量基含相位。
在定理104.7对齐后的同一个局部坐标中，
$A=\bigoplus_iM_{n_i}(\mathbb C)$，$C_1=\mathsf D_1$、$C_2=\mathsf D_2$，
原单位为各块迹之和。对高阶空间只采用同一坐标的张量幂，不假定 $N\ge3$ 的原锥为 PSD。
定理104.7的一体矩形合同、全部原旁观提升和质量预算，
命题104.11的全有限种子 qubit 寄存器、全对偶及寄存器之间 CP 映射的真正零扩张，
以及引理104.6的原杯、帽与全局自身 Choi 判据，均按原陈述复用。
本章不假定任意实际 qutrit 与 qubit 寄存器之间的通常 CP 映射已原旁观正，
也不使用 $S_3$。

**定义 105.2（实际 $3\times3$ 混合角）。** 固定一个实际最大块 $s$，
$H_s=\mathbb C^3$，并在其选定基中写 $e_0,e_1,e_2$。
令 $Q=\mathbb C^2\otimes\mathbb C^2$ 是两条实际种子角腿组成的寄存器。
取实等距嵌入

$$
c:\mathbb C^3\longrightarrow Q,\qquad
ce_0=|00\rangle,\quad ce_1=|01\rangle,\quad ce_2=|10\rangle,
\qquad c^*|11\rangle=0.
\tag{105.2}
$$

码投影为 $cc^*$；它不是 $Q$ 的恒等，余字 $11$ 被压缩为零。
令 $j_2$ 为(104.10)在这两条原种子腿上的嵌入，$\iota_s$ 为最后一条原腿的块嵌入，定义

$$
\begin{aligned}
i_s&=(j_2\operatorname{Ad}_c)\otimes\iota_s:
 \operatorname{Herm}(\mathbb C^3\otimes\mathbb C^3)\longrightarrow W_3,\\
q_s&=i_s^*,\qquad \mathsf p_s=i_sq_s,\qquad
D_s=i_s^{-1}(C_3).
\end{aligned}
\tag{105.3}
$$

伴随用实迹内积，故 $i_s$ 等距、$q_si_s=\mathrm{id}$，
$\mathsf p_s$ 为该实子空间的正交投影。$D_s$ 表示实际原锥的角交，不是另选的诊断锥。
本章在此角内记

$$
\begin{aligned}
\eta&=\sum_{a=0}^2e_a\otimes e_a,& R&=|\eta\rangle\langle\eta|,& P&=R/3,\\
\tau_F&=\frac{1-F}{8}(I-P)+FP\quad(F\in\mathbb R),&
W_\lambda&=I-\lambda R,&
t_s&=\max_{x\in D_s,\ \operatorname{Tr}x=1}\operatorname{Tr}(Px).
\end{aligned}
\tag{105.4}
$$

$I$ 是这个九维 Hilbert 角的恒等，不是整个 $W_3$ 的单位矩阵；
$R$ 是角内 dyad，原全杯总质量仍为 $\sum_i n_i$。
$i_s(R)$ 的向量代表恰为
$|00\rangle|0\rangle_s+|01\rangle|1\rangle_s+|10\rangle|2\rangle_s$，
所以 $R\in D_s$ 正是定义104.12的 $\mathsf{Fusion}_3$。
定义中的 $F$ 允许为负，此时 $\tau_F$ 不在通常 PSD 锥。
记 $\mathsf T$ 为这两个固定计算因子的同时全转置，$\mathsf T_N$ 为全部 $N$ 条原腿的转置；
它们不是部分转置，也不先假定它们在原锥上正。

### 105.2 实际对偶中的各向同性分离

**命题 105.3（实际角的全对偶与合法分离正规形）。** 在假设105.1下，
$D_s$ 闭、尖、生成，迹严格正，且

$$
\begin{aligned}
i_s(D_s)&=\mathsf p_s(C_3)=C_3\cap\operatorname{im}i_s,\\
q_s(C_3)&=D_s,\qquad i_s^*(C_3^*)=D_s^*,\\
i_s(D_s^*)&=C_3^*\cap\operatorname{im}i_s,\qquad D_s^*=\mathsf T(D_s).
\end{aligned}
\tag{105.5}
$$

所有 Schmidt 秩至多二的 dyad，针对同一个“码参考 $\mathbb C^3$｜实际块 $H_s$”切口，
都属于 $D_s$ 和 $D_s^*$。
若 $R\notin D_s$，则从实际整个原对偶中的分离泛函出发，
可以得到 $W_\lambda\in D_s^*$ 及其正原零扩张，其中
$1/3<\lambda\le1/2$。所用平均在 $D_s$ 和其整个对偶上正。

**证明。** 码投影共轭是 $Q$ 上的寄存器 CP 映射，
其真正零扩张由命题104.11在所有原纠缠旁观者上正；
最后一条腿的中心投影由定理104.7具有同样正性。
两者交换，其乘积正是实自伴幂等 $\mathsf p_s$。
码投影满足 $cc^*\preceq I_Q$，所以其 proper 效应预算也由104.11延拓；
与末腿中心投影合成后，对 $z\in C_3$ 有
$0\le u_3(\mathsf p_sz)\le u_3(z)$。
因此角交、正像和(105.5)前两行的原锥等式成立。
闭性由交子空间给出，尖性由 $i_s$ 单射给出；
码与实际块之间的所有正乘积 dyad 均为原正，且实张成整个角 Hermitian 空间，故生成。
$u_3i_s=\operatorname{Tr}$ 使迹在角内非零正向量上严格正。

若 $f\in D_s^*$，则 $fq_s$ 对全部 $C_3$ 正，且沿 $i_s$ 的限制为 $f$。
反向限制任何原正泛函也正。以迹内积表示时，$fq_s$ 的向量就是 $i_s(f)$，
因为 $q_s=i_s^*$；这给正零扩张等式及全对偶等式。
此处没有把选定效应菜单当成整个对偶。

全转置极性可直接从已取得的原杯帽推出。对任意整数 $N\ge1$，
将 $N$ 个原杯按“全部参考、全部输入”重排为 $\Omega_N\in C_{2N}$。
对 $f\in C_N^*$ 在一组 $N$ 腿上切片，矩阵单位式(102.16)给
$\mathsf T_Nf\in C_N$。另一方面，对 $x,y\in C_N$，
其原乘积在 $C_{2N}$，$N$ 对原正帽的收缩给
$\operatorname{Tr}((\mathsf T_Nx)y)\ge0$，所以 $\mathsf T_Nx\in C_N^*$。
结合 $\mathsf T_N^2=\mathrm{id}$ 得

$$
C_N^*=\mathsf T_N(C_N)\qquad(N\ge1).
\tag{105.6}
$$

这里使用全有限分块与重排来供应 $C_{2N}$ 中的杯乘积和输入乘积，
不从低阶对象外推高阶自对偶。
实码投影及实际中心投影与全转置交换，故(105.5)的角交与零扩张等式
将(105.6)限制为 $D_s^*=\mathsf T(D_s)$。
这不蕴含 $D_s=\mathsf T(D_s)$，也不假定 $D_s=\mathrm{PSD}$。

对任意 $U\in U(3)$，在寄存器 $Q$ 上把 $cUc^*$ 扩为
$cUc^*+(I_Q-cc^*)$，即码上的 $U$ 加余字上的恒等。
它及其逆的真正寄存器零扩张由104.11给出。
在实际块 $s$ 上的 $\overline U$ 共轭及其逆由104.7给出。
于是 $U\otimes\overline U$ 共轭在实际混合角上是锥自同构，其迹伴随也保持整个 $D_s^*$。
标准 Haar 平均因此在两个闭凸锥上均正，且

$$
\mathcal A(x)=\int_{U(3)}\operatorname{Ad}_{U\otimes\overline U}(x)\,dU
 =\frac{\operatorname{Tr}x-\operatorname{Tr}(Px)}8(I-P)
    +\operatorname{Tr}(Px)P.
\tag{105.7}
$$

这里复用 Terhal–Horodecki，
[*A Schmidt number for density matrices*, quant-ph/9911117v4](https://arxiv.org/abs/quant-ph/9911117v4)，
式(6)、(9)的各向同性平均及其固定空间 $\operatorname{span}_{\mathbb R}\{I,P\}$；
线性公式作用于全部 Hermitian 矩阵，不限于 PSD。
平均是有限维闭凸锥内的数学投影，不断言一个连续物理随机化事件存在。

为支付整个秩二族，写任意 Schmidt 秩至多二向量为
$\varphi=u_0\otimes v_0+u_1\otimes v_1$，允许某项为零。
从两个实际种子角之间的未归一 Bell dyad 开始，
在第一条腿使用寄存器 Kraus 算子 $A:\mathbb C^2\to Q$，$A|j\rangle=cu_j$；
在第二条腿使用一体矩形算子，令其种子二维基的像为 $v_j\in H_s$，角外送零。
第一映射由104.11、第二映射由104.7具有全部原旁观正性。
输出恰为 $i_s(|\varphi\rangle\langle\varphi|)$。
对共轭向量作同样构造，再用 $D_s^*=\mathsf T(D_s)$，得该 dyad 也在对偶。
这是单个实际输出腿的完整秩二族，尚未涉及多条实际 qutrit 的全局二维子空间。

若 $R$ 不在闭凸锥 $D_s$，有限维锥分离给 $h\in D_s^*$、$\operatorname{Tr}(hR)<0$。
原 $C_3$ 中的任意分离泛函也可先经 $\mathsf p_s$ 压缩，
保留对 $i_s(R)$ 的负读数和原正性，再用(105.5)限制。
平均固定 $R$，所以 $\mathcal A(h)=aI+bR$ 仍分离 $R$。
在正乘积向量 $|01\rangle$ 上读数为 $a$，故 $a\ge0$；
若 $a=0$，负 $R$ 读数迫使 $b<0$，却在正乘积 $|00\rangle$ 上为负。
因此 $a>0$，可除以 $a$ 写为 $W_\lambda$。
由 $\operatorname{Tr}(PW_\lambda)=1-3\lambda<0$ 得 $\lambda>1/3$。
在归一秩二 Bell 向量 $(|00\rangle+|11\rangle)/\sqrt2$ 上的读数为
$1-2\lambda$，故 $\lambda\le1/2$。
该归一族与其通常 Schmidt 数阈值是上述 Terhal–Horodecki 引理1、2及定理2的标准背景；
在这里将它用于实际全对偶的根据是前面的原映射构造。
最后由(105.5)把 $W_\lambda$ 正零扩张到原 $C_3^*$。
全程没有借用另一个有限诊断锥的对偶。∎

### 105.3 实际极值、互反系数与 proper 预算

**定理 105.4（实际角的精确互反端点）。** 在假设105.1及定义105.2下，
最大值 $t=t_s$ 确实取得。令

$$
\frac23\le t\le1,\qquad
\ell=\frac{t-1}{9t-1},\qquad \lambda_* =\frac1{3t}.
\tag{105.8}
$$

则整个归一实际角的 $P$ 坐标恰遍历 $[\ell,t]$，两个端点均取得，且

$$
\begin{aligned}
D_s\cap\operatorname{span}_{\mathbb R}\{I,P\}
 &=\operatorname{cone}\{\tau_\ell,\tau_t\},\\
\lambda\ge0:\quad W_\lambda\in D_s
 &\ \Longleftrightarrow\ W_\lambda\in D_s^*
 \ \Longleftrightarrow\ \lambda\le\lambda_*,\\
\mathsf{Fusion}_3&\ \Longleftrightarrow\ t=1
 \ \Longleftrightarrow\ \lambda_*=1/3.
\end{aligned}
\tag{105.9}
$$

若融合不成立，则 $-1/15\le\ell<0$、$1/3<\lambda_*\le1/2$，
命题105.3中各向同性分离系数的准确范围是 $1/3<\lambda\le\lambda_*$。
所有实际大小三的输出块具有同一个 $t$；码基和输出基的酉改变也保持此参数。

**证明。** 有限维闭尖锥上的严格正迹给紧的迹一基。
该基非空，因为它包含归一正乘积态，所以 $t$ 有限并取得。
归一秩二 Bell dyad 在 $D_s$ 中，$P$ 读数为 $2/3$，故 $t\ge2/3$。
平均一个最大元，由(105.7)得 $\tau_t\in D_s$。
正乘积 dyad $|01\rangle\langle01|\in D_s^*$ 在其上读数为 $(1-t)/8$，
故 $t\le1$。这个上界不假定整个实际角是 PSD。

对整个迹一实际角任意 $x$，记 $F=\operatorname{Tr}(Px)$。
对 $\lambda\ge0$ 有

$$
\operatorname{Tr}(W_\lambda x)=1-3\lambda F,\qquad
W_\lambda\in D_s^*\ \Longleftrightarrow\ 1-3\lambda t\ge0.
\tag{105.10}
$$

严格正迹允许把每个非零正向量缩为迹一，所以这真是整个对偶的判据。
特别地，它遍历可能不是通常 PSD 的全部原角状态。
$W_\lambda$ 固定于全转置，(105.5)于是使其原、对偶成员条件相同，给(105.9)第二行。
因此 $W_{\lambda_*}$ 同时为原角和对偶角的正元素。
其迹为 $9-3\lambda_*>0$，归一后的 $P$ 读数为

$$
\frac{1-3\lambda_*}{9-3\lambda_*}
 =\frac{t-1}{9t-1}=\ell,\qquad
\frac{W_{\lambda_*}}{9-3\lambda_*}=\tau_\ell.
\tag{105.11}
$$

另一方面，$\tau_t$ 也是实矩阵，因此由全转置极性属于 $D_s^*$。
对任意上述 $x$，其非负读数给

$$
0\le\operatorname{Tr}(\tau_t x)
 =tF+\frac{1-t}{8}(1-F)
 =\frac{(9t-1)F+1-t}{8}.
\tag{105.12}
$$

$9t-1>0$，所以 $F\ge\ell$；(105.11)给等号，最大端点由 $\tau_t$ 给出。
两端点的所有凸组合恰为 $\tau_F$，$F\in[\ell,t]$，所以所有这些坐标确实取得。
固定空间内每个正迹向量唯一写成正倍数的某个 $\tau_F$；
严格正迹排除非零迹零正向量，得(105.9)第一行的整锥等式。

若 $t=1$，则 $\tau_t=P\in D_s$，故 $R\in D_s$。
反向若 $R\in D_s$，其归一化 $P$ 的坐标为一，结合上界得到 $t=1$。
这就是所给实际最大块上的融合条件，而不是另一个抽象参考的条件。
命题104.13此时给 $\mathsf F_{\max}$，定理104.10再给全部有限原锥的标准 PSD 层级；
这一步不使用 $S_3$。将 $t\in[2/3,1)$ 代入(105.8)给所述分离范围与负端点范围。

两个大小三的实际块之间的等距矩形一体映射和反向映射，
由104.7在全部原旁观者上正。
把输出基逐个对应，它们在两个实际混合角之间互逆、保迹并保持 $P$ 坐标，
所以 $t_s$ 与块标签无关。
码上的酉由 $U\oplus1$ 寄存器酉实现，输出基的酉由一体映射实现；
它们把相应基下的 $P$ 连同整个实际角一同运输，故保持极值。

同一端点计算的参数形式如下：令 $d,k$ 为正整数，$d\ge2$、$1\le k\le d$。
对 $\operatorname{Herm}(\mathbb C^d\otimes\mathbb C^d)$ 中任一闭尖生成锥 $D$，
若迹严格正、$D^*=\mathsf T(D)$、$U\otimes\overline U$ 共轭保持 $D$，
且全部 Schmidt 秩至多 $k$ 的 dyad 在 $D$ 中，取
$P_d=|I_d\rangle\langle I_d|/d$，并在迹一基上最大化 $P_d$ 得 $t$。
共轭向量与全转置极性先给全部这些 dyad 的对偶成员关系。
向量 $v_k=k^{-1/2}\sum_{j=0}^{k-1}e_j\otimes e_j$ 定义良好、范数一、
Schmidt 秩恰为 $k$，且 $\operatorname{Tr}(P_d|v_k\rangle\langle v_k|)=k/d$。
正交乘积向量给 $t\le1$。
把上述证明的 $3,8,9$ 分别换为 $d,d^2-1,d^2$，即得

$$
\frac{k}{d}\le t\le1,\qquad
\ell_d=\frac{t-1}{d^2t-1},\qquad
\lambda_{*,d}=\frac1{dt}\in\left[\frac1d,\frac1k\right].
\tag{105.13}
$$

固定空间的迹一向量为
$(1-F)(I-P_d)/(d^2-1)+FP_d$，其角锥端点为 $\ell_d,t$，
而 $I-\lambda|I_d\rangle\langle I_d|$ 的原／对偶非负系数阈值为 $\lambda_{*,d}$。
这里 $d^2t-1\ge dk-1>0$；秩参数 $k$ 的整数条件不可删除。
本章实际参数对应恰为 $d=3,k=2$。
标准平均和 Schmidt 秩估计沿命题105.3所引文献复用；
(105.8)—(105.12)是在实际原角及其整个对偶上的应用关系。∎

**命题 105.5（条件性的实际非 PSD 态与精确分离效应）。** 若 $t<1$，令

$$
\rho_- =\frac{i_s(W_{\lambda_*})}{9-3\lambda_*},\qquad
M=1-\frac\ell t
 =\frac{9t^2-2t+1}{t(9t-1)},\qquad
E(z)=\frac{\operatorname{Tr}(i_s(W_{\lambda_*})z)}{M}.
\tag{105.14}
$$

则 $\rho_-\in K_3$ 是一个在通常矩阵坐标中非 PSD 的实际原态，
$E\in\mathcal E_3$ 是整个原三份锥上的 proper 效应，且

$$
E(i_s(P))=\frac{1-3\lambda_*}{M}<0.
\tag{105.15}
$$

此负读数的输入是该条件下被排除的融合候选，不是一个实际态。

**证明。** 定理105.4和(105.5)把 $i_s(W_{\lambda_*})$ 同时放入
原 $C_3$ 与原 $C_3^*$。它在 $\eta$ 方向的本征值为 $1-3\lambda_*<0$，
在其余八个角方向的本征值为一，角外为零。
迹为正，故(105.14)的归一化确属原 $K_3$，同时不是通常 PSD。
这不是构造一个满足假设105.1而 $t<1$ 的层级；它是该条件在实际角内强制的态。

对整个归一角，(105.10)与 $F\in[\ell,t]$ 给

$$
0\le\operatorname{Tr}(W_{\lambda_*}x)\le1-3\lambda_*\ell=M,
\tag{105.16}
$$

下界在 $\tau_t$ 取得，上界在 $\tau_\ell$ 取得。
对任意原 $z\in K_3$，令 $a=u_3(\mathsf p_sz)\in[0,1]$。
若 $a=0$，严格正单位给 $\mathsf p_sz=0$；若 $a>0$，则
$q_sz/a\in D_s$ 且迹一。因为 $i_s(W_{\lambda_*})$ 位于投影像内，
(105.16)给

$$
0\le\operatorname{Tr}(i_s(W_{\lambda_*})z)\le aM\le M.
\tag{105.17}
$$

任意非零原正向量可按质量归一，故(105.17)在全原锥上证明 $0\le E\le u_3$。
角内 $\tau_\ell$ 的原嵌入使上界取得，因此这里的归一预算恰为实际最大读数。
代入 $P$ 得(105.15)。没有把未缩放的 $I-R/2$ 诊断效应当成原 proper 效应，
也没有确定实际参数 $t$ 的数值。∎

### 105.4 双向实际通道与每个有限张量次数

**命题 105.6（互反噪声参数的原全旁观通道夹逼）。** 令

$$
p=\frac{9t-1}{8},\qquad r=-\frac1{9t-1},\qquad
\mathcal D_a(X)=aX+(1-a)\operatorname{Tr}(X)I_3/3.
\tag{105.18}
$$

则 $5/8\le p\le1$、$-1/5\le r\le-1/8$、$pr=-1/8$。
对每个 $a\in\{p,r\}$，$\mathcal D_a$ 都有从实际码到实际块 $s$，
以及从实际块 $s$ 到实际码的真正零扩张；两者对每个原纠缠旁观者正且不增质量，
在所接受的码或块上保迹。
令 $C_{s^n}$ 是 $C_n$ 在全部标签为 $s$ 的实际扇区中的角锥，
用该扇区的矩阵坐标表示。对每个整数 $n\ge1$，有

$$
\mathcal D_a^{\otimes n}\bigl(\operatorname{Herm}_+( (\mathbb C^3)^{\otimes n})\bigr)
 \ \subseteq\ C_{s^n}
 \ \subseteq\
 (\mathcal D_a^{\otimes n})^{-1}
 \bigl(\operatorname{Herm}_+((\mathbb C^3)^{\otimes n})\bigr).
\tag{105.19}
$$

**证明。** 采用原杯的“参考、输出”Choi 约定，在 $3\times3$ 码坐标中，
矩阵单位计算给

$$
\begin{aligned}
J(\mathcal D_a)&=aR+\frac{1-a}{3}I,\\
J(\mathcal D_p)&=3\tau_t,\qquad
J(\mathcal D_r)=\frac{W_{\lambda_*}}{3-\lambda_*}.
\end{aligned}
\tag{105.20}
$$

两者已由定理105.4属于实际 $D_s$，并非以通常 Choi 正性替代原 Choi 成员关系。
更明确地，令 $q_2$ 为(104.10)的原两种子角压缩，$\pi_s=\iota_s^*$ 为块提取，定义

$$
\begin{aligned}
A_a^0:W_2\to W_1,&\qquad
 A_a^0(z)=\iota_s\mathcal D_a(c^*q_2(z)c),\\
B_a^0:W_1\to W_2,&\qquad
 B_a^0(y)=j_2\bigl(c\mathcal D_a(\pi_s y)c^*\bigr).
\end{aligned}
\tag{105.21}
$$

$A_a^0$ 消去余字 $11$、码与余字的交叉元及其他输入扇区；
$B_a^0$ 消去其他实际输入块，输出只在码内。
直接对完整原杯展开，得 $J(A_a^0)=i_s(J(\mathcal D_a))\in C_3$。
对反向映射，$\mathcal D_a$ 为实且迹自伴，
其普通 $3\times3$ Choi 矩阵(105.20)在交换参考与输出后不变。
所以 $J(B_a^0)$ 正是同一个三原腿元素的置换，次序为“一条实际块参考、两条码输出”。
原置换正，故 $J(B_a^0)\in C_3$。
引理104.6的全局原 Choi 当且仅当分别给两条映射在全部原旁观系统上的正性，
包括任意纠缠输入。这里没有先假定通常 qutrit–寄存器 CP 许可，
也没有仅从其中一个方向正而推断另一个方向正。

$\operatorname{Tr}\mathcal D_a(X)=\operatorname{Tr}X$。
因此 $u_1A_a^0$ 恰为两种子腿上的码接受效应，
$u_2B_a^0$ 恰为实际 $s$ 块的接受效应。
前者由104.11的全 proper 延拓、后者由104.7的中心预算给
$0\le u_1A_a^0\le u_2$、$0\le u_2B_a^0\le u_1$。
把各正差与任意旁观单位相乘，原最大界将不增质量提升到所有原纠缠旁观者。
这给完整输入预算，而不是只比较 Choi 元素的总迹。
这些断言是数学映射及其预算，不增加物理事件菜单或饱和选择。

任取 $(\mathbb C^3)^{\otimes n}$ 上的通常 PSD 矩阵。
用 $c^{\otimes n}$ 把它放进实际 $2n$ 条种子角寄存器的码子空间，
104.11的整个寄存器锥已为 PSD，所以该嵌入是原正。
逐个作用 $n$ 条 $A_a^0$，每次把全部其余腿作为原旁观者；
用原置换重排，即得到第一包含。
反向从实际 $C_{s^n}$ 的任意元素出发，逐个作用 $B_a^0$，
得到原 $2n$ 条种子角寄存器中的正元素。
由104.11它必为通常 PSD，坐标恰为
$c^{\otimes n}\mathcal D_a^{\otimes n}(x)(c^*)^{\otimes n}$，
等距压回给(105.19)第二包含。
两参数都非零，$\mathcal D_a$ 在标量方向为恒等、在无迹方向乘以 $a$，
所以可逆；式中右侧仍是集合的逆像，并未授予逆映射原正性。
所有 $n$ 的包含是未知原锥必须满足的关系，不定义这些锥，也不构造负例层级。

直接复合给 $\mathcal D_b\mathcal D_a=\mathcal D_{ab}$，因而

$$
\mathcal D_r\mathcal D_p=\mathcal D_p\mathcal D_r=\mathcal D_{-1/8},
\qquad J(\mathcal D_{-1/8})=\frac{3I-R}{8}.
\tag{105.22}
$$

这正位于通常 qutrit CP 的边界：在 $\eta$ 方向本征值为零，正交方向为 $3/8$。
因此两条原接口的这一直接复合与已知的一体／寄存器 CP 操作相容，
并不把 $t$ 的端点提高到一。
若 $t<1$，则 $0<p<1$。对任意码内单位向量 $v$，

$$
\mathcal D_p^{-1}(|v\rangle\langle v|)
 =p^{-1}|v\rangle\langle v|+(1-p^{-1})I_3/3
\tag{105.23}
$$

在两个正交方向上的本征值为 $(1-p^{-1})/3<0$。
故把它作为码内寄存器逆操作时，它甚至不保持通常秩一 PSD；
正向原接口不授权用这个逆取消噪声。
两参数的数值范围与(105.22)来自(105.8)、(105.18)的直接代入。
这里保留的是实际原 Choi 所给的双向接口及全有限夹逼，
通常矩形 Choi/Kraus 表示的来源仍沿命题102.13所引 Watrous 定理2.22、2.26复用。∎

### 105.5 局部压缩、集体二维支撑与不变截面

**命题 105.7（逐输出压缩检验的准确范围）。** 对每个
$1/3<\lambda\le1/2$，通常约化映射
$\mathcal L_\lambda(X)=\operatorname{Tr}(X)I_3-\lambda X$
不是通常 CP，却是通常完全余正，其所有张量幂保持通常 PSD。
对任意等距 $E:\mathbb C^2\to\mathbb C^3$，$W_\lambda$ 压缩实际输出到此二维平面后为 PSD；
逐个压缩每条输出后的任意有限张量积，接续寄存器 CP 映射及 PSD 寄存器效应，读数仍非负。
这个检验族不包含所有“参考｜多条实际 qutrit”全局 Schmidt 秩二向量的检验。

**证明。** $J(\mathcal L_\lambda)=W_\lambda$，它在 $\eta$ 方向的本征值
$1-3\lambda<0$，所以不是通常 CP。仅作普通矩阵计算，在一个因子上部分转置得

$$
W_\lambda^{\Gamma_2}=I-\lambda S,
\tag{105.24}
$$

$S$ 是交换算子，本征值为 $+1,-1$；当 $0\le\lambda\le1$ 时右侧为 PSD。
因此 $\mathcal L_\lambda=\Psi_\lambda\circ T$，其中 $\Psi_\lambda$ 通常 CP，
$T$ 是普通矩阵转置。
每个张量幂为 $\Psi_\lambda^{\otimes n}\circ T_{\rm all}$：
先作整个输入的同时转置，再作 CP 张量幂，两步都保持通常 PSD，故得普通张量稳定正性。
这复用 Terhal–Horodecki，
[quant-ph/9911117v4](https://arxiv.org/abs/quant-ph/9911117v4)，引理2的约化族，
以及 Müller-Hermes–Reeb–Wolf，
[*Positivity of Linear Maps under Tensor Powers*, arXiv:1502.05630v2](https://arxiv.org/abs/1502.05630v2)，
Example I.1 中完全正／完全余正的平凡张量稳定类。
(105.24)没有宣称部分转置是一个合法原操作，
也没有把普通张量幂正性等同于(102.11)对全部原旁观者的正性。

在较小的压缩空间 $\mathbb C^3\otimes\mathbb C^2$ 中，写
$\eta_E=(I_3\otimes E^*)\eta$，则

$$
(I_3\otimes E^*)W_\lambda(I_3\otimes E)
 =I_3\otimes I_2-\lambda|\eta_E\rangle\langle\eta_E|,
\qquad \|\eta_E\|^2=2.
\tag{105.25}
$$

所以它当且仅当 $\lambda\le1/2$ 时为 PSD。
若重新嵌回原输出空间，其向量为 $(I_3\otimes EE^*)\eta$，
不可把不同空间中的 $\eta_E$ 直接当作此嵌入向量。
任意单站秩至多二的 Kraus 算子都通过这样一个二维平面压缩分解；
对秩一或零算子可补成二维平面。
对每个有限次数，将(105.25)逐站张量后仍为 PSD。
随后通常寄存器 CP 处理保持 PSD，PSD 寄存器效应给非负迹配对。
相应寄存器处理的原正性可由104.11取得；
这只证明先逐站压缩的这个检验族不排除上述 $\lambda$。

为区分全局二维支撑，在两个实际 qutrit 上取

$$
b_0=\frac{|00\rangle+|11\rangle+|22\rangle}{\sqrt3},\qquad
b_1=\frac{|01\rangle+|12\rangle+|20\rangle}{\sqrt3}.
\tag{105.26}
$$

两向量正交、范数一，各自每个局部约化矩阵均为 $I_3/3$。
故它们的二维联合支撑在每个实际站上都有完整三维局部支撑，
不可能包含在任意 $E_1(\mathbb C^2)\otimes E_2(\mathbb C^2)$ 中。
若 $a_0,a_1$ 是正交参考向量，则

$$
\psi=\frac{a_0\otimes b_0+a_1\otimes b_1}{\sqrt2}
\tag{105.27}
$$

在“参考｜两个实际 qutrit”切口上 Schmidt 秩恰为二，
却不能通过对每个实际输出先固定二维支撑来涵盖。
通常集体 Kraus 算子
$H=|0\rangle\langle b_0|+|1\rangle\langle b_1|$
可读出此联合支撑，但其从两条实际 qutrit 到一条种子角腿的真正原零扩张，
仍须证明其混合原 Choi 元素属于原 $C_3$。
通常 CP 性和已知两实际输入腿的 PSD 性没有支付这一全原旁观条件。
命题105.3所给秩二族的实际输出只有一条腿，不提供这个集体许可。

上述区分不排除其他已合法网络、辅助实际系统的复用或其他原分块约束产生更强结论。
Müller-Hermes–Reeb–Wolf 附录A给通常各向同性／Werner 平均，
引理9对某些 block-positive 矩阵施加指定符号条件后才得到正平均；
该引理不把任意原混合锥或这里的 $W_\lambda$ 自动变成 Werner 态模型。
这里的约化映射属于该论文明确的平凡完全余正类，
故不能用关于非平凡张量稳定正映射的结论代替剩余融合桥。
这些计算没有建立 $\mathsf{Fusion}_3$ 与 Werner 不可蒸馏性、NPPT 问题或全局秩二检验的等价。∎

**命题 105.8（不变二维截面的连续端点族）。** 对每个数值
$t\in[2/3,1]$，取 $\ell=(t-1)/(9t-1)$，则

$$
\mathcal K_t=\operatorname{cone}\{\tau_\ell,\tau_t\}
 \ \subset\operatorname{span}_{\mathbb R}\{I,P\}
\tag{105.28}
$$

在该二维实迹内积空间中闭、尖、生成、迹严格正且自对偶，
并包含所有归一 Schmidt 秩至多二 PSD dyad 的各向同性平均。
这些不变截面条件因而允许连续的数值 $t$，不单独强制 $t=1$。

**证明。** 两生成元的迹均为一，且

$$
\operatorname{Tr}(\tau_f\tau_g)
 =fg+\frac{(1-f)(1-g)}8,
\qquad \operatorname{Tr}(\tau_\ell\tau_t)=0.
\tag{105.29}
$$

两生成元的迹内积范数平方 $\operatorname{Tr}(\tau_\ell^2),\operatorname{Tr}(\tau_t^2)$
严格正，且 $\ell<t$，故它们是二维空间中两条正交的非零射线。
它们生成的正象限与其迹对偶相等；任意非零非负线性组合的迹为正。
这也给闭性、尖性和生成性。
对归一 Schmidt 秩至多二 PSD dyad，普通 $P$ 重叠在 $[0,2/3]$ 中，
上界是命题105.3所引 Terhal–Horodecki 引理1的情形 $k=2,N=3$，下界为 PSD 读数。
$\ell\le0$、$t\ge2/3$，故其平均 $\tau_F$ 都在 $\mathcal K_t$ 中。

这只是固定空间内的二维例族，不是完整 $D_s$、实际混合角反例或全有限原层级。
不变空间外的一体滤波、所有原分块和整个对偶的相容性仍须分别满足。
它也不提供一个预设 proper PSD 三份局部锥的全有限扩张。
本章的端点、proper 预算与(105.19)是标准分离、平均、Choi 和迹计算在实际原模型中的推导应用，
不把这些成熟结果另认作新的分类或表示定理。

在假设105.1的原条件下，剩余融合命题准确等价于证明实际参数 $t=1$，
即排除所有 $\lambda>1/3$ 的实际 $W_\lambda\in D_s^*$；
另一方向须构造并核对一个具有 $t<1$ 的完整原全有限层级，
保留原 $S_2$、三项供应、种子、全部原纯态与全对偶，二维截面本身不构成此构造。
若一条有限原网络能从实际 $\tau_t$、$W_{1/(3t)}$、已合法寄存器操作、
一体 qutrit 映射、杯帽与原分块，在每个 $t<1$ 时产生实际 $\tau_f$、$f>t$，
或产生已标准种子寄存器中的非 PSD 正元素，就分别与最大值定义或104.11矛盾，迫使 $t=1$。
其中每条集体实际 qutrit–寄存器操作都须先支付自己的原 Choi 成员关系；
(105.22)、(105.23)及逐输出压缩族尚未给出这样的网络。

全部结论只涉及原有限锥、数学映射与所写预算。
物理事件饱和、实际来源及其仪器、时间作用、物理钟校准和数值 $\hbar$，
仍按命题104.15保留各自条件，不从上述平均、同一矩阵表示或保迹关系取得。∎

## 追加锚（本行以下为增补区）
