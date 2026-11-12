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
反过来各交锥元素之和仍属 $C_N$；各子空间直和且 $P_s$ 的像正是相应子空间，
故得到真正的整锥直和(102.19)。没有从中心边缘的正性直接推断整锥分裂。

局域酉映射的 Choi 元素在 $(i,i)$ 块是
$(I_i\otimes U_i)\Omega_i(I_i\otimes U_i)^*$，其余块为零，
所以属于已知 $C_2$。逆映射把 $U_i$ 换成 $U_i^*$，具有相同正性。
迹保持是整空间恒等式，提升后的 $u_N$ 也保持。
允许只选一个块的酉、其他块取恒等；这一结论是原锥上的数学对称。∎

## 追加锚（本行以下为增补区）
