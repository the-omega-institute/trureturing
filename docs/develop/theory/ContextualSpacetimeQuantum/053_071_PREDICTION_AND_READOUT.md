# 情境时空算术的量子扩展：预测、记录与稳定读出

[总目](../CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) · [前卷](033_051_CLASSICAL_AND_QUANTUM_STORAGE.md) · [续卷](072_098_HISTORY_AND_CAPACITY.md)


<a id="entry-141"></a>

## 追加锚（新终端）
<a id="section-53"></a>

## 53. 第 51 节候选条件的适用域更正

**命题 53.1（退相干因子分解的假设）。** 第 51.1 节的乘积式

$$
\Gamma_{ab}(t)=\prod_k\gamma_{ab}^{(k)}(t)
$$

需要至少假设初态在所选环境分解下为

$$
\rho_{SE}(0)=\rho_S(0)\otimes\bigotimes_k\tau_k
$$

并且条件环境演化在每个标签 $a$ 下因子化为 $U_a(t)=\bigotimes_kU_{a,k}(t)$。在这些假设下，环境重叠给出

$$
\Gamma_{ab}(t)=\prod_k\operatorname{tr}\!\left(U_{a,k}(t)\tau_kU_{b,k}(t)^\dagger\right).
$$

若系统自身 Hamiltonian 混合不同的 $\Pi_a$ 子空间，则 $\rho_{ab}(t)=\rho_{ab}(0)\Gamma_{ab}(t)$ 一般只是相互作用表象或附加条件下的表达，不能直接当作完整动力学的恒等式。

证明。因子化初态与条件演化使环境条件态分别为 $\bigotimes_kU_{a,k}\tau_kU_{a,k}^\dagger$。两个条件态的重叠是各片段重叠的乘积，得到第一式。若系统自身演化不保持指针分解，它会在不同 $a$ 之间产生额外转移项，故单一乘法因子不能代表完整演化。证毕。

**命题 53.2（互信息条件的可读性边界）。** 第 51.2 节的条件

$$
I(A:F)\ge(1-\delta)H(A)
$$

只说明经典标签 $A$ 与片段 $F$ 的互信息接近标签熵。要把它解释为某个实际测量能够以小猜测误差读出 $A$，还须指定测量类并加入相应的可访问信息或猜测概率界；互信息条件单独不提供该测量界。

证明。互信息是对允许测量前的量子—经典相关量的函数，而可读性还包含从 $F$ 到标签估计器的优化。二者只有在给定编码、测量类及相应信息—误差不等式后才能连接。因此本命题把第 51.2 节的第二项保留为冗余相关性指标，不把它冒充为单次读出定理。证毕。

**推论 53.3（第 51 节结论的正确状态）。** 第 51 节的三项只能作为指定模型、形成后时间窗和误差阈值下的候选筛选条件。要在具体开放系统中把它们升级为充分判据，还须同时验证完整生成元对指针代数的时间窗内近似不变性，并给出该近似与目标读出误差之间的定量界。

因此，“需要多少约束”仍由 $\varepsilon,\delta,T,R_\ast$、环境分解、可执行测量类和生成元参数共同决定；本批不赋予它一个普适整数。

证明。命题 53.1 限定退相干分解的动力学假设，命题 53.2 限定冗余互信息的操作解释，完整生成元检验补足系统自身 Hamiltonian 条件未覆盖的开放动力学。三项边界合并后，所得只是可检验的模型内筛选标准。证毕。



<a id="entry-143"></a>

## 追加锚（新终端）
<a id="section-52"></a>

## 52. 末端读取与无中间干预的累计预测界

**定义 52.1（真实演化的末端读取与逐步记录模型）。** 设 $\mathcal H$ 为有限维 Hilbert 空间，$\Phi:\mathcal L(\mathcal H)\to\mathcal L(\mathcal H)$ 为 CPTP 映射，$\mathcal E$ 为同一算符空间上的幂等 CPTP 映射，$\mathcal E^2=\mathcal E$。记全部密度算符为 $\mathsf D(\mathcal H)$，记录态集为

$$
\mathcal R=\mathcal E\bigl(\mathsf D(\mathcal H)\bigr),
\qquad
T=\mathcal E\Phi\mathcal E,
\qquad
K=T|_{\mathcal R}.
$$

幂等性使 $\mathcal E(\sigma)=\sigma$ 对每个 $\sigma\in\mathcal R$ 成立，故 $K(\sigma)=\mathcal E\Phi(\sigma)$，且 $K$ 将记录态集映入自身。

对任意共同初态 $\rho$，在不插入中间记录通道的演化中，真实状态与其第 $n$ 步末端读数分别为

$$
\sigma_n=\Phi^n(\rho),
\qquad
r_n=\mathcal E\Phi^n(\rho).
$$

仅用初始记录建立的闭合预测则是

$$
s_0=\mathcal E(\rho),
\qquad
s_{n+1}=K(s_n),
\qquad
s_n=T^n\mathcal E(\rho).
$$

这里同时写出各个 $r_n$ 是计算不同演化时刻的粗观察量，不要求在同一次实际运行中每一步都施加 $\mathcal E$。若在每一步 $\Phi$ 后实际施加记录通道，则相应状态为 $(\mathcal E\Phi)^n(\rho)$；它与 $\mathcal E\Phi^n(\rho)$ 是两种不同的通道复合。

**定理 52.2（末端记录的累计闭合误差）。** 在定义 52.1 的模型中，令

$$
D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1,
$$

$$
\delta
=\max_{\omega\in\mathsf D(\mathcal H)}
D\bigl(\mathcal E\Phi(\omega),\mathcal E\Phi\mathcal E(\omega)\bigr).
$$

该最大值存在，且 $0\le\delta\le1$。对每个密度算符 $\rho$ 与整数 $n\ge0$，有

$$
\boxed{
D\bigl(\mathcal E\Phi^n(\rho),T^n\mathcal E(\rho)\bigr)
\le n\delta.
}
$$

特别地，若 $\mathcal E\Phi=\mathcal E\Phi\mathcal E$，则末端记录由初始记录严格决定：

$$
\mathcal E\Phi^n(\rho)=K^n\mathcal E(\rho)
\qquad(n\ge0).
$$

若另有 $0\le\kappa\le1$，使记录更新满足

$$
D(K\sigma,K\tau)\le\kappa D(\sigma,\tau)
\qquad(\sigma,\tau\in\mathcal R),
$$

则有更强的界

$$
D\bigl(\mathcal E\Phi^n(\rho),T^n\mathcal E(\rho)\bigr)
\le\delta\sum_{j=0}^{n-1}\kappa^j.
$$

当 $n=0$ 时空和为零；当 $\kappa<1$ 时，右端可写成 $\delta(1-\kappa^n)/(1-\kappa)$。上述结论不要求 $\Phi$ 保持 $\mathcal R$，也不要求 $\Phi\mathcal E=\mathcal E\Phi$。

证明。有限维密度算符集合紧，两个通道及迹范数连续，所以定义中的上确界达到。两候选均为密度算符，其迹距离属于 $[0,1]$。

采用定义 52.1 的 $\sigma_n,r_n,s_n$，并令 $e_n=D(r_n,s_n)$。初始时 $r_0=s_0=\mathcal E(\rho)$，故 $e_0=0$。幂等性给出

$$
T(r_n)
=\mathcal E\Phi\mathcal E\bigl(\mathcal E(\sigma_n)\bigr)
=\mathcal E\Phi\mathcal E(\sigma_n).
$$

又有 $r_{n+1}=\mathcal E\Phi(\sigma_n)$，其中 $\sigma_n$ 仍为密度算符，故一步缺陷的定义逐步适用：

$$
D\bigl(r_{n+1},T(r_n)\bigr)\le\delta.
$$

$r_n$ 与 $s_n$ 都位于 $\mathcal R$，而 $s_{n+1}=T(s_n)$。三角不等式和记录更新的收缩性给出

$$
\begin{aligned}
e_{n+1}
&\le D\bigl(r_{n+1},T(r_n)\bigr)
+D\bigl(T(r_n),T(s_n)\bigr)\\
&\le\delta+\kappa e_n.
\end{aligned}
$$

对这个标量递推归纳，由 $e_0=0$ 得

$$
e_n\le\delta\sum_{j=0}^{n-1}\kappa^j.
$$

$T$ 是 CPTP 映射，其限制 $K$ 总可取收缩上界 $\kappa=1$，于是得到 $n\delta$。严格闭合使 $\delta=0$，故全部 $e_n=0$。证明中的 $T(r_n)$ 只是把真实第 $n$ 步读数输入预测规则作比较，没有对真实状态 $\sigma_n$ 施加中间干预。

与此区别，令 $A=\mathcal E\Phi$。对第 50.4 条比较的逐步记录通道，$A$ 与 $T$ 在 $\mathcal R$ 上相同，且 $A(\rho),T(\rho)$ 都在 $\mathcal R$。因此对每个 $n\ge1$，

$$
A^n(\rho)=K^{n-1}A(\rho),
\qquad
T^n(\rho)=K^{n-1}T(\rho),
$$

从而

$$
D\bigl(A^n(\rho),T^n(\rho)\bigr)
\le\kappa^{n-1}\delta\le\delta.
$$

这里 $n=1$ 时空次迭代的系数为一。这一更强界适用于逐步记录的两种初始处理；它不把 $A^n$ 改写成 $\mathcal E\Phi^n$。证毕。

**命题 52.3（中间去相干会改变后续记录）。** 对一个量子比特，取计算基去相干通道

$$
\mathcal E_Z(X)=P_0XP_0+P_1XP_1,
\qquad P_j=|j\rangle\langle j|,
$$

以及 Hadamard 幺正通道

$$
\Phi(X)=H X H,\qquad
H=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}.
$$

对初态 $\rho=P_0$ 和两步演化，

$$
\mathcal E_Z\Phi^2(P_0)=P_0,
\qquad
(\mathcal E_Z\Phi)^2(P_0)=\frac I2.
$$

因此末端读取与逐步记录的通道一般不同。在这个模型中，定义 52.2 的一步缺陷为 $\delta=1/2$，而末端记录与闭合预测的两步误差恰为 $1/2$。

证明。$H^2=I$，所以第一式成立。另一方面，$\Phi(P_0)=|+\rangle\langle+|$，去相干后为 $I/2$；后者在 $\Phi$ 和 $\mathcal E_Z$ 下都不变，得到第二式。

为计算一步缺陷，把任意态写成 Bloch 形式

$$
\omega=\frac12(I+xX+yY+zZ),
\qquad x^2+y^2+z^2\le1.
$$

Hadamard 共轭将 $X$ 与 $Z$ 互换。于是

$$
\mathcal E_Z\Phi(\omega)=\frac12(I+xZ),
\qquad
\mathcal E_Z\Phi\mathcal E_Z(\omega)=\frac I2.
$$

两者迹距离为 $|x|/2$，其最大值 $1/2$ 由 $|+\rangle$ 达到。记录更新 $K$ 把所有计算基对角态映为 $I/2$，所以 $T^2\mathcal E_Z(P_0)=I/2$。末端误差为 $D(P_0,I/2)=1/2$；它符合定理 52.2，却不等同于逐步通道之间的误差。证毕。

**定理 52.4（时变记录与逐步收缩系数）。** 设 $\mathcal H_0,\ldots,\mathcal H_n$ 均为有限维空间。对每个 $k=0,\ldots,n-1$，令

$$
\Phi_k:\mathcal L(\mathcal H_k)\to\mathcal L(\mathcal H_{k+1})
$$

为 CPTP 映射，并对每个 $k=0,\ldots,n$ 取幂等 CPTP 记录通道 $\mathcal E_k$。定义记录态集

$$
\mathcal R_k=\mathcal E_k\bigl(\mathsf D(\mathcal H_k)\bigr),
$$

一步记录更新

$$
K_k:\mathcal R_k\to\mathcal R_{k+1},
\qquad
K_k(\sigma)=\mathcal E_{k+1}\Phi_k(\sigma),
$$

以及一步缺陷

$$
\delta_k
=\max_{\omega\in\mathsf D(\mathcal H_k)}
D\bigl(\mathcal E_{k+1}\Phi_k(\omega),
\mathcal E_{k+1}\Phi_k\mathcal E_k(\omega)\bigr).
$$

取任意满足

$$
D(K_k\sigma,K_k\tau)\le\kappa_k D(\sigma,\tau)
\qquad(\sigma,\tau\in\mathcal R_k)
$$

的 $\kappa_k\in[0,1]$。令 $\sigma_0=\rho$、$\sigma_{k+1}=\Phi_k(\sigma_k)$，真实末端读数为 $r_k=\mathcal E_k(\sigma_k)$；闭合预测从 $s_0=\mathcal E_0(\rho)$ 出发，按 $s_{k+1}=K_k(s_k)$ 更新。则

$$
\boxed{
D(r_n,s_n)
\le\sum_{j=0}^{n-1}\delta_j
\prod_{k=j+1}^{n-1}\kappa_k.
}
$$

空积取一，$n=0$ 时空和取零。每个记录更新都可以选择 $\kappa_k=1$，从而始终有 $D(r_n,s_n)\le\sum_{j=0}^{n-1}\delta_j$。

证明。$K_k$ 是 CPTP 映射 $\mathcal E_{k+1}\Phi_k$ 在记录态集上的限制，所以记录态集保持及收缩上界成立。真实状态 $\sigma_k$ 仍归一化；由 $r_k=\mathcal E_k(\sigma_k)$，可直接得到

$$
D\bigl(r_{k+1},K_k(r_k)\bigr)
=D\bigl(\mathcal E_{k+1}\Phi_k(\sigma_k),
\mathcal E_{k+1}\Phi_k\mathcal E_k(\sigma_k)\bigr)
\le\delta_k.
$$

令 $e_k=D(r_k,s_k)$，三角不等式给出

$$
e_{k+1}\le\delta_k+\kappa_k e_k,
\qquad e_0=0.
$$

归纳展开：$e_1\le\delta_0$；若第 $m$ 步已满足乘积和，则

$$
\begin{aligned}
e_{m+1}
&\le\delta_m+\kappa_m
\sum_{j=0}^{m-1}\delta_j\prod_{k=j+1}^{m-1}\kappa_k\\
&=\sum_{j=0}^{m}\delta_j\prod_{k=j+1}^{m}\kappa_k.
\end{aligned}
$$

这正是陈述的第 $m+1$ 步形式。整个比较针对未经中间记录干预的真实通道序列 $\Phi_{n-1}\cdots\Phi_0$；变化的是各时刻的观察映射与预测规则，未把观察计算替换成物理测量。证毕。

**推论 52.5（经典记录的原始预测式）。** 若记录通道为有限正交指针基中的完全去相干，

$$
\mathcal E(\rho)=\sum_i\operatorname{tr}(P_i\rho)P_i,
\qquad P_i=|i\rangle\langle i|,
$$

令 $\pi(\rho)_i=\operatorname{tr}(P_i\rho)$，$\iota(p)=\sum_i p_iP_i$，以及列随机矩阵

$$
K_{ij}=\operatorname{tr}\bigl(P_i\Phi(P_j)\bigr).
$$

则

$$
D\bigl(\mathcal E\Phi^n(\rho),\iota(K^n\pi(\rho))\bigr)
\le n\delta.
$$

等价地，真实末端读数分布与仅从初始读数预测出的 $K^n\pi(\rho)$ 之间，总变差距离不超过 $n\delta$。

证明。每个 $K_{ij}\ge0$，且迹保持给出 $\sum_iK_{ij}=1$。直接代入得 $T\iota(p)=\iota(Kp)$，而 $\mathcal E(\rho)=\iota\pi(\rho)$，故 $T^n\mathcal E(\rho)=\iota(K^n\pi(\rho))$。两个对角密度算符的迹距离恰为其权重向量的总变差距离，应用定理 52.2 即得。证毕。

所用迹范数收缩见 Watrous，*The Theory of Quantum Information*，[Corollary 3.40，式 (3.241)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)。本章在有限维 CPTP 模型中用这一标准工具证明末端观察的递推界；一步缺陷的最大值遍历所声明系统的全部密度算符。若要对额外惰性参考上的任意纠缠输入给出统一保证，需要把缺陷改为扩展通道上的最大迹距离，或使用相应 diamond 范数界，不能由未扩展的 $\delta$ 自动推出。界中的 $n\delta$ 可以大于一，此时只有平凡的迹距离上界一更强。量子通道收缩和预测误差界均不指定某一次观测的唯一结果，也不要求把证明中的各次粗观察实现为实际中间测量。



<a id="entry-145"></a>

## 追加锚（新终端）

<a id="section-54"></a>

## 54. 有限实验族的预测等价与最小充分记录

前面的闭合条件研究的是一个已经选定的记录通道能否独立推进。这里把问题换成静态的有限任务：在只允许一组有限实验、且每个实验最多运行有限步时，哪些历史必须被区分，哪些历史可以合法地合并？这个问题不要求给不相容测量预先填写一张共同答案表；每个实验协议都有自己的结果分布。

**定义 54.1（有限实验族）。** 设 $X$ 是非空有限的候选历史集合，且 $m\ge1$。固定一个有限实验族

$$
\mathfrak T_H=\{\tau_1,\ldots,\tau_m\},
$$

其中每个协议 $\tau_i$ 的运行长度不超过 $H$，可以包含基于先前结果选择后续操作的有限自适应分支，终端结果集合 $Y_i$ 有限。对 $x\in X$，记该协议的结果分布为

$$
p_i(\,\cdot\mid x)=p_{\tau_i}(\,\cdot\mid x)\in\Delta(Y_i).
$$

记录值只需取在 $r(X)$ 中；对每个 $u\in r(X)$，相应的预测器取值于 $\Delta(Y_i)$。

在量子模型中，$x$ 可以代表一个候选密度算符或带有历史标签的状态，$p_{\tau_i}(y\mid x)$ 由该协议的通道复合与末端 POVM 按 Born 规则给出。实验族中的每个 $\tau_i$ 是一个固定的可执行协议（必要时含有限分支）；不同 $\tau_i$ 之间不要求、也不默认存在联合结果分布。

**定义 54.2（$H$ 步预测等价）。** 定义

$$
x\mathrel{\sim_H}x'
\quad\Longleftrightarrow\quad
p_i(\,\cdot\mid x)=p_i(\,\cdot\mid x')
\quad\text{对所有 }i=1,\ldots,m.
$$

把

$$
S_H(x)=\bigl(p_1(\,\cdot\mid x),\ldots,p_m(\,\cdot\mid x)\bigr)
$$

称为预测响应签名，并令 $Q_H=X/{\sim_H}$。因为 $X$ 有限，$\sim_H$ 是有限个等价类。

**定理 54.3（有限实验族的最小充分记录）。** 令 $r:X\to R$ 是一个记录。以下两件事等价：

1. 对每个实验 $\tau_i$，存在只依赖记录值的分布 $\widehat p_i(\,\cdot\mid r)$，使

   $$
   p_i(\,\cdot\mid x)=\widehat p_i(\,\cdot\mid r(x))
   \qquad(x\in X).
   $$

2. $r$ 的每个纤维都包含在一个 $\sim_H$ 等价类中，即

   $$
   r(x)=r(x')\Longrightarrow x\sim_H x'.
   $$

因此 $S_H$（等价地，商映射 $q_H:X\to Q_H$）是这组实验的最小充分记录：任意充分记录都能区分 $\sim_H$ 的不同类，而 $q_H$ 本身保留恰好足以重建全部 $p_i$ 的信息。达到 $|Q_H|$ 个有效记录值的充分记录，其每个非空纤维恰为一个 $\sim_H$ 类，因而在把记录值作双射重标记的意义下唯一；允许多余记录值时，充分记录可以严格细化这些类。并且

$$
|Q_H|=\bigl|\{S_H(x):x\in X\}\bigr|.
$$

证明。若第 1 条成立且 $r(x)=r(x')$，则对每个 $i$ 都有

$$
p_i(\,\cdot\mid x)=\widehat p_i(\,\cdot\mid r(x))
=\widehat p_i(\,\cdot\mid r(x'))=p_i(\,\cdot\mid x'),
$$

故 $x\sim_Hx'$。反过来，若第 2 条成立，对每个非空记录纤维的记录值 $u$ 选一个代表元 $x_u$，定义

$$
\widehat p_i(\,\cdot\mid u):=p_i(\,\cdot\mid x_u).
$$

第 2 条保证同一纤维中的任意 $x$ 与 $x_u$ 预测等价，所以该定义与代表元选择无关，并满足第 1 条。取 $r=q_H$ 即得到充分记录。若另有充分记录 $r$，已证其纤维不能跨越 $\sim_H$ 类，因此它至少有 $|Q_H|$ 个有效值；$q_H$ 达到该下界。若有效值数也等于 $|Q_H|$，每个类只能对应一个纤维，纤维对应遂给出记录值与 $Q_H$ 之间的双射。证毕。

这个定理给出一个可直接检查的“对象”判据：在指定实验族和 $H$ 步上限后，对象不是当前数值相同的所有历史，而是响应签名相同的历史类。改变实验族会改变等价关系；增加实验只能细化记录，不能把两个已经可区分的响应重新合并。

**推论 54.4（有限协议组合的因子化）。** 若先以固定概率 $\lambda_i\ge0$ 选择协议 $\tau_i$，满足 $\sum_i\lambda_i=1$，并对其终端结果施加随机核 $K_i:Y_i\to\Delta(Y)$，其中 $Y$ 是共同有限结果集，则组合实验的结果分布为

$$
p(y\mid x)=\sum_{i=1}^{m}\lambda_i
\sum_{z\in Y_i}K_i(y\mid z)p_i(z\mid x).
$$

它只依赖于 $S_H(x)$，因而也只依赖于 $q_H(x)$。这给出有限实验族对随机菜单和经典读出的封闭性；它没有把不同不相容协议的结果拼成一个联合样本。

证明。右端只含各个 $p_i(\cdot\mid x)$，而这些分布由 $S_H(x)$ 确定。证毕。

**推论 54.5（实验族扩张的单调性与有限稳定化）。** 若

$$
\mathfrak T_H\subseteq\mathfrak T_{H+1}
$$

（例如加入长度为 $H+1$ 的协议），则

$$
x\sim_{H+1}x'\Longrightarrow x\sim_Hx',
\qquad
|Q_H|\le |Q_{H+1}|.
$$

对有限 $X$，每次严格细化至少使等价类数增加一；所以这条链至多发生 $|X|-1$ 次严格细化。达到某个 $H_0$ 后若 $Q_{H_0}=Q_{H_0+1}$，这只说明在所声明的有限扩张中没有新区别；它不推出未列入实验族的协议也无法区分这些类。

证明。第一式是实验条件包含关系的直接应用；第二式由商集细化得到。严格细化会把至少一个类拆成两个，故有限性给出次数上界。证毕。

**定义 54.6（有限实验族的预测伪距离）。** 在不要求 $X$ 有限时，令

$$
d_H(x,x')
=\max_{1\le i\le m}
\operatorname{TV}\!\left(p_i(\,\cdot\mid x),p_i(\,\cdot\mid x')\right),
$$

其中

$$
\operatorname{TV}(p,q)=\frac12\sum_{y}|p(y)-q(y)|.
$$

在任意 $X$ 上仍用“所有 $p_i(\cdot\mid x)$ 相等”定义 $\sim_H$；当 $X$ 有限时，这与定义 54.2 完全一致。

则 $d_H$ 是伪度量：它非负、对称，满足三角不等式，但不同状态可能有 $d_H=0$。零距离关系正好是 $\sim_H$；并令 $Q_H:=X/{\sim_H}$，于是 $Q_H$ 是把有限任务下不可区分状态取商得到的预测空间。

对每个 $i$ 再施加一个随机后处理 $K_i$ 时，数据处理不等式给出

$$
\operatorname{TV}(K_ip_i^x,K_ip_i^{x'})
\le \operatorname{TV}(p_i^x,p_i^{x'}),
$$

故后处理后的预测伪距离不超过 $d_H$。三角不等式则逐个 $i$ 应用总变差距离的三角不等式，再取最大值。这些收缩性只涉及已列出的协议结果，不涉及不相容测量的联合赋值。

具体地，对任意 $x,y,z$ 有

$$
\begin{aligned}
d_H(x,z)
&=\max_i\operatorname{TV}(p_i^x,p_i^z)\\
&\le\max_i\bigl[\operatorname{TV}(p_i^x,p_i^y)+\operatorname{TV}(p_i^y,p_i^z)\bigr]\\
&\le d_H(x,y)+d_H(y,z),
\end{aligned}
$$

其中 $p_i^x$ 简写为 $p_i(\cdot\mid x)$。这同时说明 $d_H$ 的三角不等式不依赖于任何跨协议联合赋值。

**命题 54.7（近似充分记录的纤维判据）。** 若记录 $r:X\to R$ 满足每个纤维的 $d_H$ 直径不超过 $\varepsilon$，选定每个非空纤维的代表元 $x_u$ 并令

$$
\widehat p_i(\,\cdot\mid u)=p_i(\,\cdot\mid x_u),
$$

则对所有 $x$ 和 $i$，都有

$$
\operatorname{TV}\!\left(p_i(\,\cdot\mid x),
\widehat p_i(\,\cdot\mid r(x))\right)\le\varepsilon.
$$

反过来，若某个预测器对每个 $x$ 的误差均不超过 $\alpha$，即

$$
\operatorname{TV}\!\left(p_i(\,\cdot\mid x),
\widehat p_i(\,\cdot\mid r(x))\right)\le\alpha
$$

对所有 $i,x$ 成立，则每个记录纤维的 $d_H$ 直径不超过 $2\alpha$。

证明。第一部分把 $x$ 与同一纤维代表元的总变差距离直接代入 $d_H$ 的定义。第二部分对同一纤维中的 $x,x'$ 使用三角不等式：

$$
\operatorname{TV}(p_i^x,p_i^{x'})
\le\operatorname{TV}(p_i^x,\widehat p_i^{r(x)})
+\operatorname{TV}(\widehat p_i^{r(x')},p_i^{x'})
\le2\alpha,
$$

其中 $r(x)=r(x')$。对 $i$ 取最大值得证。证毕。

该命题是静态的有限任务压缩条件，和第 50、52 节的动态闭合误差不同：这里不假定存在一步记录通道，也不把误差按时间步累积；它只回答“在预先列出的实验族上，一个记录纤维内最多允许多大预测差异”。如果实验族以包含原实验族的方式扩张，$d_H$ 只能增大，原来的 $\varepsilon$-充分性可能失效。

**例 54.8（增加一个实验会拆分对象）。** 取四个候选历史 $X=\{a,b,c,d\}$。第一实验 $\tau_1$ 和第二实验 $\tau_2$ 都是二结果协议，令结果 $1$ 的概率表为

$$
\begin{array}{c|cccc}
 &a&b&c&d\\ \hline
\tau_1&0&0&1&1\\
\tau_2&0&1&0&1
\end{array}
$$

只允许 $\tau_1$ 时，最小充分记录有两个类：$\{a,b\}$ 与 $\{c,d\}$。加入 $\tau_2$ 后，四个响应签名分别为 $(0,0),(0,1),(1,0),(1,1)$，所以 $Q_H$ 变成四个单点类。一个具体实现是在 $\mathbb C^4$ 的基 $|00\rangle,|01\rangle,|10\rangle,|11\rangle$ 上分别读取第一和第二个经典比特；两行在这个实现中相容。该表的作用是展示商结构，而不是声称任意量子实验都能同时实现不相容读数。

**量子相容性边界。** 在量子应用中，$\mathfrak T_H$ 应理解为一组具体协议，每个协议内部的测量顺序和控制已经固定。定义 $S_H$ 只收集各协议的边缘结果分布，不产生跨不相容协议的联合概率。因而“$x\sim_Hx'$”的含义是：在这组可执行协议上统计不可区分；它不等价于存在一张同时写好所有测量答案的经典表。若实验族包含连续控制参数，有限的 $H$ 步上限本身仍不使 $\mathfrak T_H$ 有限；此时应改用上确界型伪距离，或先给控制菜单和精度预算，再使用本节的有限版本。

**本节边界。** 定理 54.3 处理有限候选历史和有限实验族，证明的是响应分布的因子化与最小性；命题 54.7 给出有限任务下的近似压缩误差。它们不声称记录一定能由一个物理仪器无损实现，也不替代第 50、52 节关于实际通道闭合和时间累计误差的检验。若要把 $Q_H$ 实现为物理记录，还需另外给出仪器、扰动和后续实验的动力学模型，并检查它是否保持所需的响应精度。

本节是 repo-derived/open 的理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

<a id="entry-147"></a>

## 追加锚（新终端）

<a id="section-55"></a>

## 55. 有限记录的 Gram 谱、相位回流与复用协议

前面已经分别给出了预测等价、去相干固定点以及末端预测误差。本节把“记录怎样参与后续演化”压缩成一个有限维可计算对象：条件记录向量的 Gram 矩阵。它同时给出相干模式的衰减因子和相位因子，但不能单独决定记录是否真的被读取，也不能把带记忆的复用协议当成每步独立的无记忆通道。

本节所有结论都是有限维模型中的 `repo-derived/open` 推导；没有新增 Lean 声明、形式覆盖或冻结状态。

<a id="entry-149"></a>

### 定义 55.1（条件记录与 Gram 记录通道）

设构型标签集 $I$ 有限，系统空间为

$$
\mathcal H_S=\operatorname{span}\{|i\rangle:i\in I\},
$$

记录空间为 $\mathcal H_R$。固定记录初态 $|m_\ast\rangle$，并假设内部耦合在这些输入上满足

$$
|i\rangle|m_\ast\rangle\longmapsto |i\rangle|r_i\rangle,
\qquad \langle r_i|r_i\rangle=1.
$$

定义 Gram 矩阵

$$
R_{ij}:=\langle r_j|r_i\rangle.
$$

对系统算符定义记录后的局部通道

$$
\mathcal C_R(\rho)=R\circ\rho,
\qquad
(R\circ\rho)_{ij}=R_{ij}\rho_{ij}.
$$

这里的 $\circ$ 是逐项乘积。因为 $R$ 是单位对角的半正定矩阵，Schur 乘积定理给出 $\mathcal C_R$ 完全正且保持迹；它正是上述联合幺正演化后对记录空间取偏迹得到的通道。

<a id="entry-150"></a>

### 命题 55.2（Gram 谱就是相干模式的响应谱）

令 $E_{ij}=|i\rangle\langle j|$。则

$$
\mathcal C_R(E_{ij})=R_{ij}E_{ij}.
$$

因此在矩阵单位基下，记录通道的特征值（按代数重数计）就是 $\{R_{ij}:i,j\in I\}$。对 $R_{ij}\neq0$，给定记录间隔 $\tau>0$ 可写成

$$
R_{ij}=e^{-\Gamma_{ij}\tau+i\omega_{ij}\tau},
$$

其中

$$
\Gamma_{ij}=-\frac{\log|R_{ij}|}{\tau},
\qquad
\omega_{ij}=\frac{\arg R_{ij}}{\tau}\pmod{\frac{2\pi}{\tau}}.
$$

故模长描述该相干模式的单次衰减，辐角描述相对相位旋转。这个“谱”属于记录耦合与选定标签的组合，不是孤立构型预先携带的普适频率。

证明。第一式由逐项乘积直接得到；矩阵单位构成全体矩阵空间的基，故特征值列表如上。指数参数化只是对非零复数的模长和辐角作定义。证毕。

<a id="entry-151"></a>

### 推论 55.3（趋于经典与仅有经典固定点是两件事）

设 $|I|\ge2$，并令

$$
q:=\max_{i\neq j}|R_{ij}|.
$$

则对任意 $N\ge1$，

$$
(\mathcal C_R^N\rho)_{ij}=R_{ij}^{N}\rho_{ij}.
$$

若 $q<1$，则所有非对角元趋于零，且 $\mathcal C_R^N(\rho)$ 收敛到 $\rho$ 的指针基对角部分。若存在 $i\neq j$ 使 $|R_{ij}|=1$，则该模式不会衰减；它可以周期旋转，也可以保持不变。一般地，固定点空间由满足 $R_{ij}=1$ 的矩阵单位张成；条件 $|R_{ij}|=1$ 本身只说明记录向量同射线，不能说明它们携带可区分记录。对纯记录态，二者的迹距离为 $\sqrt{1-|R_{ij}|^2}$。

若所有 $i\ne j$ 都满足 $R_{ij}=1$ 或 $|R_{ij}|<1$，则逐项极限存在，并等于保留 $R_{ij}=1$ 的矩阵单位的投影；若存在 $|R_{ij}|=1$ 且 $R_{ij}\ne1$，则通常只有 Cesàro 平均才会消除该周期相位，而单次迭代不收敛。

特别地，取

$$
|r_0\rangle=|0\rangle,
\qquad |r_1\rangle=-|0\rangle,
$$

则

$$
R=\begin{pmatrix}1&-1\\-1&1\end{pmatrix},
\qquad
\mathcal C_R(\rho)=Z\rho Z.
$$

其固定点满足 $\rho_{01}=0$，因而固定点全是对角的；但是

$$
\mathcal C_R^2=\operatorname{id}.
$$

所以“固定点代数是经典的”不推出“动力学趋向经典”。趋近经典需要严格的谱隙条件 $q<1$，而不是仅仅要求 $R_{ij}\neq1$。

证明。逐次应用第一式即可。$q<1$ 时有限维任意矩阵范数中的非对角部分都趋于零；反例直接代入 Schur 乘积公式。证毕。

<a id="entry-152"></a>

### 定义 55.4（独立新记录与相干复用）

设每次记录都使用一个与系统和旧记录无关的空白单元，则 $N$ 次局部通道为 $\mathcal C_R^N$，其模式 $E_{ij}$ 的可见度为

$$
V_N^{\mathrm{fresh}}(i,j)=|R_{ij}|^N.
$$

若同一个记录单元保留相干并再次参与联合演化，则不能直接把每次作用替换成 $\mathcal C_R$；需要从联合幺正演化重新计算当前记录向量的 Gram 矩阵。

<a id="entry-153"></a>

### 命题 55.5（同一记录复用的有限模型）

令

$$
A=\sum_{i\in I}a_i|i\rangle\langle i|,
\qquad
U_\theta=e^{-i\theta A\otimes Y},
$$

记录比特从 $|0\rangle$ 开始。连续作用 $m$ 次而不测量、不重置该比特后，系统边缘通道仍为 Schur 通道，并且

$$
R^{(m)}_{ij}
=\langle0|e^{im\theta a_jY}e^{-im\theta a_iY}|0\rangle
=\cos\!\bigl(m\theta(a_i-a_j)\bigr).
$$

因此

$$
V_m^{\mathrm{reuse}}(i,j)
=\left|\cos\!\bigl(m\theta(a_i-a_j)\bigr)\right|,
$$

而一般不满足

$$
\mathcal C_{R^{(m+n)}}
=\mathcal C_{R^{(m)}}\mathcal C_{R^{(n)}}.
$$

例如 $a_0=0,a_1=1,\theta=\pi/4$ 时，

$$
V_2^{\mathrm{fresh}}=\frac12,
\quad V_2^{\mathrm{reuse}}=0,
\qquad
V_4^{\mathrm{fresh}}=\frac14,
\quad V_4^{\mathrm{reuse}}=1.
$$

同样四次作用可以给出衰减到四分之一的独立记录，也可以给出完整回归的相干复用。差异来自旧记录仍在联合系统中携带相位，而不是来自“作用次数”这个整数本身。

证明。由于 $A$ 在构型基底对角化，$U_\theta^m$ 对 $|i\rangle$ 条件地作用为 $e^{-im\theta a_iY}$。对记录比特取内积得到 $R^{(m)}_{ij}$；$e^{-isY}=\cos s\,I-i\sin s\,Y$ 且 $\langle0|Y|0\rangle=0$，故得到余弦式。数值等式由 $\cos(\pi/2)=0$、$\cos(\pi)=-1$ 以及独立通道的幂次直接得出。证毕。

<a id="entry-154"></a>

### 记忆回流的有限表达

为了把“旧历史重新回来”与上述复用例子分开，考虑任意有限维线性演化的可见—隐藏分块：

$$
x_{n+1}=Ax_n+By_n,
\qquad
y_{n+1}=Cx_n+Dy_n.
$$

这里 $x_n$ 是当前记录保留的坐标，$y_n$ 是被省略但仍在整体中演化的坐标；不假定 $y_n$ 自身是量子态。

<a id="entry-155"></a>

### 命题 55.6（隐藏块诱导的历史回流核）

对 $n\ge0$，消去 $y_n$ 得

$$
x_{n+1}
=Ax_n+BD^ny_0
+\sum_{k=0}^{n-1}BD^{n-1-k}Cx_k.
$$

其中 $BD^ny_0$ 是初始隐藏差异的后效，$BD^{n-1-k}C$ 是从时刻 $k$ 的可见变化进入隐藏块、再返回当前读数的回流核。

若在某个次乘范数下 $\|D^r\|\le\eta_r$，则相距 $r$ 步以上的回流项范数至多按

$$
\|B\|\,\eta_r\,\|C\|\,\|x_k\|
$$

控制。只有在给定预测窗口和误差容限下这些尾项足够小，才可以把 $x_n$ 近似当作无记忆状态。该条件是对隐藏动力学的谱或范数假设，不由“当前读数已经稳定”自动推出。

证明。由第二式递归展开

$$
y_n=D^ny_0+\sum_{k=0}^{n-1}D^{n-1-k}Cx_k,
$$

代回第一式即得。尾项界由次乘范数和三角不等式给出。证毕。

<a id="entry-156"></a>

### Zeckendorf 约束窗口中的记录混叠

取长度 $L$ 的合法字串集合

$$
\mathcal W_L=\{w\in\{0,1\}^L:w_jw_{j+1}=0\},
$$

并令 $a(w)$ 是其 Zeckendorf 权重读数。以三位窗口为例，合法构型为

$$
000,001,010,100,101,
$$

对应 $a(w)=0,1,2,3,4$。在该有限集合上使用命题 55.5 的记录耦合，得到

$$
R_{wv}=\cos\!\bigl(\theta(a(w)-a(v))\bigr).
$$

于是

$$
R_{wv}=0
\iff
\theta(a(w)-a(v))\in\frac\pi2+\pi\mathbb Z,
$$

表示两条条件记录正交；而

$$
|R_{wv}|=1
\iff
\theta(a(w)-a(v))\in\pi\mathbb Z,
$$

表示它们至多相差一个相位符号，局部记录不能稳定地区分二者。故 Zeckendorf 刻度差大并不自动意味着可读信息增加；还必须检查实际耦合角度造成的 Gram 谱是否混叠。

这个构造只规定了合法构型和一个明确记录模型。它没有把 Fibonacci 权重解释为物理能量，也没有声称仓库现有 `WindowRegister` 已经实现该受约束量子空间。

<a id="entry-157"></a>

### 与前面章节的边界

命题 55.2–55.3 研究一次固定记录通道的谱和渐近行为；它们不替代第 50 节的粗变量闭合条件。命题 55.5 比较两种联合协议，说明第 52 节的逐步无记忆界不能直接套用于相干复用；命题 55.6 给出有限线性模型中的回流核，但不自动保证某个开放量子系统的生成元具有该分块形式。第 54 节的预测等价仍然按预先声明的实验族定义对象；本节只说明同一记录值在不同记录协议下可能拥有不同 Gram 谱和历史后效。项目已有的跨记录类指数衰减结果要求相应重叠统一小于一；本节的周期反例属于同一记录射线只差相位的情形，因此不满足那个收缩假设。

因此，“保留多少历史”在这个有限模型中至少由三项共同决定：记录 Gram 谱中模长小于一的谱隙、相位复用产生的回流、以及任务允许的预测窗口。不存在脱离协议、读出和误差容限的普适整数答案。

<a id="entry-158"></a>

## 追加锚（新终端）

<a id="section-56"></a>

## 56. 任务依赖的记忆视界与有效阶数

第 54 节把对象定义为指定实验族上的预测响应类，第 55 节说明记录复用会把旧关联重新带回可见演化。本节把“还要保留多少历史”写成一个可计算的任务量。关键区别是：记忆视界由输入—隐藏—输出的通道共同决定，而不是由隐藏空间的维数或某个全局谱单独决定。

<a id="entry-160"></a>

### 定义 56.1（有限线性记忆实现与任务核）

考虑有限维线性实现

$$
x_{n+1}=Ax_n+By_n,
\qquad
y_{n+1}=Cx_n+Dy_n,
$$

其中 $x_n$ 是当前记录保留的坐标，$y_n$ 是未写入记录但仍在整体中演化的坐标。给定线性任务读出 $G$，实际比较的量为 $z_n=Gx_n$。取次乘范数，并令

$$
K_r:=GBD^{r-1}C\quad(r\ge1),
\qquad
b_n:=GBD^ny_0.
$$

由第 55.6 节的消元式，输出满足

$$
z_{n+1}
=GAx_n+b_n+
\sum_{r=1}^{n}K_r x_{n-r}.
$$

$K_r$ 是相隔 $r$ 步的任务记忆核；它只记录能够从可见端口进入隐藏块、再由读出端口返回的部分。隐藏方向若被 $G B$ 消掉，即使在整体中长时间存在，也不属于这个任务的可见记忆。

<a id="entry-161"></a>

### 定义 56.2（$\varepsilon$-记忆视界）

固定任务时间窗 $T$、可见轨道界 $\|x_k\|\le X$ 和初始隐藏界 $\|y_0\|\le Y$。整数 $h$ 满足 $0\le h<T$ 时，称其为 $(T,\varepsilon)$-记忆视界，如果对每个 $n$ 满足 $h\le n<T$，都有

$$
\|b_n\|
+X\sum_{r=h+1}^{n}\|K_r\|
\le\varepsilon.
$$

最小这样的 $h$ 记为 $h_{\varepsilon,T}$；若没有这样的整数，则记为 $\infty$。它给出一个直接的任务判据：把 $n-h$ 步以前的可见历史以及尚未释放的初始隐藏差异删去时，下一次任务读出的误差至多为 $\varepsilon$。这里的误差是任务读出所选的范数；若 $G$ 最后产生概率分布，则可再用相应的数据处理收缩把它换成总变差界。

这个定义不同于第 52 节的逐步闭合误差。第 52 节把每一步粗粒化误差沿无记忆迭代累积；这里直接计算被隐藏动力学传播后的尾核，允许同一记录被相干复用，也允许不同延迟的记忆项发生抵消。它因此是“任务需要保留多长历史”的视界，而不是每步误差的重新命名。

<a id="entry-162"></a>

### 命题 56.3（几何隐藏衰减给出可计算视界）

设存在 $M\ge1$ 和 $0\le\alpha<1$，使得

$$
\|D^r\|\le M\alpha^r\qquad(r\ge0).
$$

令 $g=\|G\|$、$b=\|B\|$、$c=\|C\|$。则任意 $h$ 都满足

$$
\|b_n\|+X\sum_{r=h+1}^{n}\|K_r\|
\le
gbM\alpha^h\left(Y+\frac{cX}{1-\alpha}\right)
\qquad(n\ge h).
$$

因此，只要 $0<\varepsilon<gbM(Y+cX/(1-\alpha))$，取

$$
h\ge
\left\lceil
\frac{\log\!\left(\varepsilon/[gbM(Y+cX/(1-\alpha))]\right)}{\log\alpha}
\right\rceil
$$

就得到一个 $(T,\varepsilon)$-记忆视界；当右端常数为零时，视界为 $0$。若 $\alpha=0$，则 $D^r=0$（$r\ge1$），记忆核在有限步内严格截断。

证明。由次乘性，$\|b_n\|\le gbM\alpha^nY\le gbM\alpha^hY$。并且

$$
\|K_r\|\le gbcM\alpha^{r-1},
$$

所以

$$
X\sum_{r=h+1}^{n}\|K_r\|
\le gbcMX\sum_{r=h+1}^{\infty}\alpha^{r-1}
=\frac{gbcM X\alpha^h}{1-\alpha}.
$$

两式相加即得。对 $0<\alpha<1$ 取对数并注意 $\log\alpha<0$，得到给出的整数条件。证毕。

<a id="entry-163"></a>

### 推论 56.4（有效阶数与精确有限记忆）

在上述条件下，$h_{\varepsilon,T}$ 随 $\varepsilon$ 只按对数增长：其上界为

$$
O\!\left(\frac{\log(1/\varepsilon)}{-\log\alpha}\right).
$$

当存在 $q$ 使

$$
GBD^rC=0\quad(r>q),
\qquad
GBD^ny_0=0\quad(n>q)\quad\text{（对当前给定的初始隐藏态 $y_0$）},
$$

则 $q$ 是该任务的记忆阶数上界；若第 $q$ 延迟项实际非零，它就是精确阶数。所有超过 $q$ 的历史对任务输出都没有作用。特别地，$D^q=0$ 是一个与任务无关的充分条件，但不是必要条件，因为端口 $GB$ 或 $C$ 可能消灭长寿命隐藏方向。

在有限任务窗 $T$ 内，只有 $r<T$ 的核会出现；因此即使 $h_{\varepsilon,\infty}=\infty$，有限实验族仍可能有有限的 $h_{\varepsilon,T}$。这与第 54 节的有限实验族一致：有限视界上的对象只需对声明过的实验和长度负责。

<a id="entry-164"></a>

### 反例 56.5（没有谱隙就没有普适有限视界）

若 $D$ 在某个可见端口方向上是单位模旋转，例如 $D=-I$ 且 $GB\ne0$、$C\ne0$，则

$$
K_r=GB(-I)^{r-1}C
$$

的范数不衰减。对适当的有界轨道，任意固定 $h$ 的尾和都不能由几何级数压到任意小；于是 $h_{\varepsilon,\infty}=\infty$（除非端口耦合恰好相消）。这正是第 55 节相干复用的周期回流在记忆核语言中的表现：同一记录被再次访问时，单次 Gram 因子 $|R_{ij}|<1$ 的“新记录”结论不能直接套用。

反过来，$D$ 的谱半径小于一也不足以给出一个仅由谱半径决定的短视界。非正规矩阵

$$
D=\begin{pmatrix}\alpha&L\\0&\alpha\end{pmatrix},
\qquad 0<\alpha<1,
$$

有

$$
D^r=\begin{pmatrix}\alpha^r&rL\alpha^{r-1}\\0&\alpha^r\end{pmatrix}.
$$

当 $L$ 很大时，短期回流可先放大再衰减。故需要的是可验证的范数包络（或带条件数的 Jordan 估计），不能只报告渐近谱半径。

<a id="entry-165"></a>

### 命题 56.6（任务端口决定记忆，而非隐藏维数）

设隐藏空间分解为 $Y=Y_{\mathrm{seen}}\oplus Y_{\mathrm{dark}}$，且 $C$ 的像和 $GB$ 的行空间都落在 $Y_{\mathrm{seen}}$ 的相应端口闭包中。若 $D$ 在 $Y_{\mathrm{dark}}$ 上任意（甚至是幺正），则所有 $K_r=GBD^{r-1}C$ 对 $Y_{\mathrm{dark}}$ 的分量均为零；该暗子空间不增加 $h_{\varepsilon,T}$。

相反，隐藏空间可以只有一个维度而取 $D=\alpha$、$\alpha$ 任意接近一，从而使

$$
K_r=GB\,\alpha^{r-1}C
$$

保持很长的有效尾。于是“保留多少历史”既不由隐藏自由度数量决定，也不由当前记录值的数量决定，而由任务允许的输入端口、输出端口、误差和时间窗共同决定。

证明。若 $C$ 不把可见扰动送入 $Y_{\mathrm{dark}}$，且 $GB$ 不从该子空间读出，则每个乘积 $GBD^{r-1}C$ 在该分量上为零。后一断言直接取一维 $D=\alpha$ 代入定义。证毕。

<a id="entry-166"></a>

### 与第 54、55 节的连接和边界

第 54 节的 $H$ 步预测等价检验“在已列实验族上能否区分历史”；本节的 $h_{\varepsilon,T}$ 检验“删去多早以前的历史后，指定读出在 $T$ 步内还差多少”。增加实验协议可能使静态商细化，即使原来的记忆视界不变；改变端口或记录复用协议也可能使同一静态商获得不同的回流核。

第 55 节的 Gram 谱给出一次记录对相干模式的模长和相位。只有在每次记录使用独立空白单元并满足相应因子化假设时，$|R_{ij}|^N$ 才能直接作为衰减律；相干复用必须通过联合实现的 $D$ 和端口核重新计算。因而 Gram 谱的谱隙、隐藏块的范数衰减与任务端口的可见性是三个相关但不等同的量。

本节也不声称任何开放量子系统都具有给定的 $(A,B,C,D)$ 分块，或把一般非马尔可夫过程自动压成有限阶经典递推。量子应用必须先给出联合通道、记录初始化和任务 POVM，再证明这些线性界适用于所选算子空间。若环境有初始相关、控制依赖历史或任务读出本身变化，应把相应记录并入状态；否则有限视界结论没有适用依据。

因此，“稳定经典现实”在这个模型中的可计算版本是：对给定实验族、端口和误差容限，存在有限 $h_{\varepsilon,T}$，使更早历史通过回流核对后续记录的影响低于 $\varepsilon$。它是任务依赖的有效阶数，而不是脱离观测协议的宇宙常数。

本节为 `repo-derived/open` 理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

<a id="entry-167"></a>

## 追加锚（新终端）

<a id="section-57"></a>

## 57. 无限未来统计、预测商与最小动力学修复

第 54 节把对象定义在有限实验族上，第 55–56 节把记录复用和隐藏回流写成有限记忆模型。若允许继续进行同一类后续操作，还需要回答一个更强的问题：**当前记录是否足以决定所有有限次未来读数？** 这一节用 Heisenberg 迭代生成的可观测空间回答它。

本节使用仓库中已冻结的 `AllFutureStatisticsSufficiency`、`FutureStatisticsEquivalence`、`MinimalPredictiveSummary`、`OperationalReadoutQuotientRepresentation` 与 `PredictionClosureDynamicalRepair` 结果。这里的“所有未来”指给定有限初始 effect 家族、给定离散 Heisenberg 演化下的所有有限迭代；它不表示任意连续控制或任意物理实验都已包含。

<a id="entry-169"></a>

### 定义 57.1（未来可见空间与预测投影）

令 $\mathcal V_0$ 是当前选定的有限 effect 家族在 traceless-Hermitian 载体中的实线性 span，令 $H$ 是 Heisenberg 迭代的实线性作用。定义

$$
\mathcal V_{\infty}
=
\operatorname{span}_{\mathbb R}
\{H^n E_i:n\in\mathbb N,\ i\in I\}.
$$

记 $P_{\infty}$ 为到 $\mathcal V_{\infty}$ 的正交投影。它只保留会在某个有限未来时刻进入所选 effect 读数的方向。

<a id="entry-170"></a>

### 定理 57.2（全部未来统计的充要预测表示）

对两个 traceless-Hermitian 状态坐标 $\rho,\sigma$，有

$$
P_{\infty}\rho=P_{\infty}\sigma
\iff
\forall n\in\mathbb N,\ \forall i\in I,
\quad
\langle\rho,H^nE_i\rangle
=
\langle\sigma,H^nE_i\rangle.
$$

证明思路是把投影差为零转化为 $\rho-\sigma\in\mathcal V_{\infty}^{\perp}$，再用 span induction 将生成元上的内积相等推广到整个空间；反向则把每个 $H^nE_i$ 看作生成元。形式化定理为 `all_future_statistics_sufficiency`。

这一定义比单次读数严格：两个状态可以有相同当前概率，却在某个未来 Heisenberg 迭代的 effect 上分开。相反，若投影相同，则在这套实验协议允许的任意有限延迟下都不能分开。

<a id="entry-171"></a>

### 定理 57.3（Schrödinger 读数与无限 Heisenberg span）

设 $\Phi$ 是有限维量子通道，$H$ 是其 Heisenberg 对偶，$\mathcal A_0$ 是当前 operator system。令

$$
\mathcal V_{\infty}
=\operatorname{span}_{\mathbb R}
\{H^k A:A\in\mathcal A_0,\ k\in\mathbb N\}.
$$

则两个密度态的所有未来 operator-system readout 相等，当且仅当

$$
\rho-\sigma\in\mathcal V_{\infty}^{\perp_{\operatorname{tr}}},
$$

即

$$
\left[\forall k,\quad
R_{\mathcal A_0}(\Phi^k\rho)
=
R_{\mathcal A_0}(\Phi^k\sigma)\right]
\iff
\left[\forall A\in\mathcal V_{\infty},\quad
\operatorname{Tr}\bigl((\rho-\sigma)A\bigr)=0\right].
$$

形式化定理为 `future_statistics_iff_annihilates_infinite_system`。它把“历史被丢掉”精确改写为：历史差异是否落入全部未来读数的正交核。这个核依赖初始 effect 家族和 channel 对偶，不能被称为绝对不可观测部分。

<a id="entry-172"></a>

### 定理 57.4（预测充分 summary 的唯一因子化和维数下界）

令 $S$ 是当前状态的线性 summary，并假设

$$
S(x)=S(y)
\Longrightarrow
\langle x,H^nE_i\rangle
=
\langle y,H^nE_i\rangle
$$

对所有 $n,i$ 成立。则存在唯一线性映射 $L$，使

$$
P_{\infty}=L\circ S_{\rm range},
$$

并且

$$
\operatorname{finrank}(\mathcal V_{\infty})
\le
\operatorname{finrank}(\operatorname{range}S).
$$

形式化定理为 `minimal_predictive_summary`。因此“保留多少历史”在该线性模型中有一条必要条件：summary 的可达维数不能小于未来预测空间的维数。summary 可以包含额外不可见坐标，但这些坐标对当前声明的未来任务不是必要的。

<a id="entry-173"></a>

### 定理 57.5（操作读数商的规范代表）

定义

$$
\rho\sim_{\mathcal A_0}\sigma
\iff
R_{\mathcal A_0}(\rho)=R_{\mathcal A_0}(\sigma).
$$

则商空间 $\mathrm{States}/\!\sim_{\mathcal A_0}$ 规范等价于实际 readout 的 range。该等价把每个状态类送到它的 readout，并保持二元密度混合：

$$
R(t\rho+(1-t)\sigma)
=tR(\rho)+(1-t)R(\sigma),
\qquad 0\le t\le1.
$$

这是 `operational_readout_quotient_representation` 的内容。故当前尺度上的“对象”可以取为操作商中的一个类；它不是脱离指定 readout 的本体标签。

<a id="entry-174"></a>

### 定理 57.6（最小动力学修复）

仅有当前 visible space $\mathcal V$ 时，$\mathcal V^{\perp}$ 未必对后续演化保持不变；于是两个当前不可区分状态的差异可能在未来重新出现。令

$$
\overline{\mathcal V}
=\operatorname{span}\{(H^*)^n v:v\in\mathcal V,\ n\in\mathbb N\},
\qquad
\mathcal R=\overline{\mathcal V}^{\perp}.
$$

则 $\overline{\mathcal V}$ 是包含 $\mathcal V$ 且对 observable evolution 不变的最小扩张，$\mathcal R$ 对 adjoint evolution 不变，并且存在商上的线性演化 $\overline H$ 满足

$$
\overline H\circ\pi
=
\pi\circ H^*.
$$

形式化定理为 `prediction_closure_minimal_dynamical_repair`。这给第 50 节的经典闭合判据一个线性算子版本：若当前记录没有形成演化同余，就把可见空间闭包到最小不变空间，再在残差商上定义演化。

<a id="entry-175"></a>

### Zeckendorf 前缀作为一个有误差界的预测摘要

Zeckendorf 卷定理 459.2 给出一个可直接接入本节的有限精度例子。设 $q_L(n)$ 读取自然数 $n$ 的低 $L$ 位合法 Zeckendorf 字串，设 $\alpha$ 为该卷相位定义中的黄金共轭数。若

$$
q_L(n)=q_L(m),
$$

则

$$
\left\|\alpha(n-m)\right\|\le\alpha^L,
$$

其中左侧是到最近整数的圆周距离。于是可以定义一个明确的相位记录模型

$$
|\psi_n\rangle
=\frac{|0\rangle+e^{2\pi i\alpha n}|1\rangle}{\sqrt2}.
$$

两条同前缀历史对应的纯态迹距离满足

$$
D\bigl(|\psi_n\rangle\langle\psi_n|,
|\psi_m\rangle\langle\psi_m|\bigr)
=\left|\sin\bigl(\pi\alpha(n-m)\bigr)\right|
\le\min\{1,\pi\alpha^L\}.
$$

因此，对这个特定的相位读出和任意后续 POVM，低 $L$ 位可以作为误差为 $\pi\alpha^L$ 的近似预测摘要；要让单次读出误差不超过 $\varepsilon$，一个充分条件是

$$
L\ge
\left\lceil\frac{\log(\pi/\varepsilon)}{-\log\alpha}\right\rceil.
$$

这只是一个指定记录模型中的任务界。Zeckendorf 卷定理 469.5 同时指出，同前缀相位的 Wasserstein 或 Lipschitz 误差界不自动给出总变差收敛；某些端点读出仍可把两个同前缀历史完全分开。故“前缀足够”必须连同读出类别和误差度量一起声明，不能从相位逼近直接推出完整历史已经被压缩。

<a id="entry-176"></a>

### 与第 54–56 节的边界

第 54 节的有限实验族只要求在已声明的协议上响应相同；本节的 $\mathcal V_{\infty}$ 把协议固定后允许任意有限迭代，因此条件更强。第 56 节的 $h_{\varepsilon,T}$ 是给定时间窗与误差的近似记忆视界；本节给出的是精确的线性预测商，未引入范数误差或有限时间截断。实际应用中可以先取后续章节的有限稳定深度，再用第 56 节的尾核界控制截断误差。

这些定理不声称任意开放量子系统都有给定的有限维 Heisenberg 对偶，也不声称所有连续控制已被枚举；它们只在文件中明确的有限维、线性、指定 effect/channel 假设下成立。本节新增理论叙述应标记为 `repo-derived/open`；不新增 Lean 声明，也不把解释层的“客体”表述升级为普适物理定律。

<a id="entry-177"></a>

## 追加锚（新终端）
<a id="section-58"></a>

## 58. Zeckendorf 黄金读数的误差预算与预测响应接口

第 54--56 节已经把对象、响应和记忆视界分开：第 54 节按指定实验族取预测等价类，第 55 节区分独立新记录与相干复用，第 56 节用输入端口、隐藏演化和输出端口定义记忆尾项。本节补上 Zeckendorf 刻度与这三个量之间的一个有限、可检验接口。

关键限制先写明。Zeckendorf 规范化给出离散整数的唯一表示；黄金读数给出一个实数嵌入。它的误差界只适用于已经规范的有限 Zeckendorf 行。对含有重复槽位的原始行，不能把同一个界直接套到未规范的字面系数上。规范化也不自动保留历史：不同原始表可能有同一个规范整数，而第 54 节的后续实验仍能将它们分开。

<a id="entry-179"></a>

### 定义 58.1（规范黄金读数与刻度残差）

令

$$
\phi=\frac{1+\sqrt5}{2},\qquad
G_j=F_{j+2},
$$

并令 $s(n)$ 是低位到高位的规范 Zeckendorf 行。置

$$
\Lambda_Z(s(n))
=
\sum_{j\ge0}\phi^{j+2}s(n)_j,
\qquad
\gamma_Z(n)
=
\frac{\Lambda_Z(s(n))}{\sqrt5},
$$

其中和因 $s(n)$ 有限支撑而有限；这正是 Z 卷定义 19 的黄金值 $\beta$ 在单行规范数字上的限制。定义刻度残差

$$
\eta_Z(n)=\gamma_Z(n)-n.
$$

这里的 $\gamma_Z$ 是一个读数坐标，不是新的整数运算，也不是物理能量或 Hamiltonian 的定义。

<a id="entry-180"></a>

### 命题 58.2（黄金读数的统一误差界）

对所有 $n\in\mathbb N$，

$$
\left|\eta_Z(n)\right|<\frac1{\sqrt5}.
$$

因而在任意有限窗口 $0\le n<G_L$ 上，误差上界相同；窗口长度只限制可出现的规范构型数，不会把这个读数误差自动改成零。

证明。Binet 恒等式在本索引约定下为

$$
\phi^{j+2}
=
\sqrt5\,G_j+(-\phi^{-1})^{j+2}.
$$

将 $s(n)$ 代入并除以 $\sqrt5$，得到

$$
\eta_Z(n)
=
\frac1{\sqrt5}
\sum_{j\ge0}s(n)_j(-\phi^{-1})^{j+2}.
$$

规范行只有有限个非零位，所以

$$
\left|\sum_{j\ge0}s(n)_j(-\phi^{-1})^{j+2}\right|
<
\sum_{j\ge0}\phi^{-(j+2)}
=1.
$$

最后一个严格不等式来自有限支撑；故得到所列界。这个证明只使用规范行和有限支撑，未把原始重复槽位当作规范数字。证毕。

<a id="entry-181"></a>

### 定义 58.3（任务响应的刻度 Lipschitz 条件）

固定有限历史集合 $R$、规范化后的整数读数

$$
N:R\longrightarrow\mathbb N
$$

以及有限实验族 $\mathfrak T=\{\tau_i:1\le i\le m\}$。对每个实验，设输出分布为 $p_i(\,\cdot\mid r)$。若存在定义在包含所有 $N(r)$ 与 $\gamma_Z(N(r))$ 的实区间上的映射

$$
\kappa_i:\mathbb R\longrightarrow\Delta(Y_i)
$$

满足

$$
p_i(\,\cdot\mid r)=\kappa_i(N(r))
$$

以及某个 $L_i<\infty$ 使

$$
\operatorname{TV}\!\left(\kappa_i(x),\kappa_i(y)\right)
\le L_i|x-y|,
$$

则称该实验在这组历史上满足 $L_i$-刻度 Lipschitz 条件。它要求响应确实经由 $N$ 因子化；若不同原始历史具有同一个 $N$ 却有不同后续响应，该条件不成立。

用黄金坐标构造预测器

$$
\widehat p_i(\,\cdot\mid r)
=
\kappa_i\!\left(\gamma_Z(N(r))\right).
$$

<a id="entry-182"></a>

### 定理 58.4（刻度误差到有限预测误差的传输）

在定义 58.3 的条件下，对所有 $r\in R$ 和 $i$，

$$
\operatorname{TV}\!\left(
p_i(\,\cdot\mid r),
\widehat p_i(\,\cdot\mid r)
\right)
<
\frac{L_i}{\sqrt5}.
$$

令 $L_{\mathfrak T}=\max_iL_i$，则全部实验输出的最坏总变差误差满足

$$
\max_{r\in R,\,i\le m}
\operatorname{TV}\left(
p_i(\,\cdot\mid r),\widehat p_i(\,\cdot\mid r)
\right)
<
\frac{L_{\mathfrak T}}{\sqrt5}.
$$

证明。对每个 $i,r$ 使用 Lipschitz 条件和命题 58.2：

$$
\operatorname{TV}\!\left(
\kappa_i(N(r)),
\kappa_i(\gamma_Z(N(r)))
\right)
\le
L_i\left|N(r)-\gamma_Z(N(r))\right|
<
\frac{L_i}{\sqrt5}.
$$

对 $i$ 取最大值即得。证毕。

这个定理只控制“同一个规范整数的实数刻度近似”。它不控制规范化纤维内部的历史差异，也不证明 $\gamma_Z$ 是一个足够状态。

<a id="entry-183"></a>

### 定义 58.5（规范化纤维缺陷）

不假设响应经由 $N$ 因子化。对每个实验定义规范化纤维缺陷

$$
\varepsilon_{\mathrm{fib},i}
=
\sup_{\substack{r,r'\in R\\N(r)=N(r')}}
\operatorname{TV}\!\left(
p_i(\,\cdot\mid r),
p_i(\,\cdot\mid r')
\right),
$$

并令

$$
\varepsilon_{\mathrm{fib}}
=
\max_i\varepsilon_{\mathrm{fib},i}.
$$

它是第 54 节预测伪距离在规范化纤维上的直径；当纤维中没有两个不同元素时，其上确界取 $0$。$\varepsilon_{\mathrm{fib}}=0$ 才表示在所列实验族上，规范化整数已经足以代表历史。

对每个 $i$，从每个非空纤维选一个代表 $r_u$，置

$$
\bar\kappa_i(u)=p_i(\,\cdot\mid r_u).
$$

若 $\bar\kappa_i$ 在同一实区间上有 $L_i$-刻度 Lipschitz 延拓，定义代表黄金预测器

$$
\widehat p_i(\,\cdot\mid r)
=
\bar\kappa_i\!\left(\gamma_Z(N(r))\right).
$$

<a id="entry-184"></a>

### 定理 58.6（历史纤维、黄金刻度与任务误差的三项分解）

在上述有限条件下，对所有 $r$ 和 $i$，

$$
\operatorname{TV}\!\left(
p_i(\,\cdot\mid r),
\widehat p_i(\,\cdot\mid r)
\right)
<
\varepsilon_{\mathrm{fib},i}
+
\frac{L_i}{\sqrt5}.
$$

因此全部实验输出的最坏总变差误差满足

$$
\max_{r\in R,\,i\le m}
\operatorname{TV}\left(
p_i(\,\cdot\mid r),\widehat p_i(\,\cdot\mid r)
\right)
<
\varepsilon_{\mathrm{fib}}
+
\frac{L_{\mathfrak T}}{\sqrt5}.
$$

证明。令 $u=N(r)$，取该纤维代表 $r_u$。三角不等式给出

$$
\operatorname{TV}\!\left(
p_i(\,\cdot\mid r),
\bar\kappa_i(u)
\right)
\le
\varepsilon_{\mathrm{fib},i}.
$$

另一方面，命题 58.2 和 $\bar\kappa_i$ 的 Lipschitz 条件给出

$$
\operatorname{TV}\!\left(
\bar\kappa_i(u),
\bar\kappa_i(\gamma_Z(u))
\right)
<
\frac{L_i}{\sqrt5}.
$$

两式相加即得；再对 $i$ 和 $r$ 取最大值。证毕。

该分解把两个常被混淆的损失分开：

$$
\underbrace{\varepsilon_{\mathrm{fib}}}_{\text{规范化抹去的历史仍可被实验看见}}
\quad+\quad
\underbrace{\frac{L_{\mathfrak T}}{\sqrt5}}_{\text{黄金实数刻度的近似误差}}.
$$

第一项即使整数读数完全精确也可能存在；第二项即使历史恰好经由整数闭合也仍可能存在。更换实验族会改变第一项和各 $L_i$，所以没有脱离任务的单一“黄金现实精度”。

<a id="entry-185"></a>

### 命题 58.7（与记忆视界的合并预算）

设第 56 节的 $(T,h)$ 截断在同一任务输出度量下有尾误差 $\tau_{h,T}$；也就是说，把 $n-h$ 步以前的历史和初始隐藏差异删除后，对所有 $n<T$ 的输出改变至多为 $\tau_{h,T}$。若定理 58.6 的黄金代表预测器再用于该截断模型，则总误差满足

$$
\varepsilon_{\mathrm{total}}(h,T)
<
\varepsilon_{\mathrm{fib},T}
+
\frac{L_T}{\sqrt5}
+
\tau_{h,T},
$$

其中 $\varepsilon_{\mathrm{fib},T}$ 和 $L_T$ 分别取长度不超过 $T$ 的全部实验与读出中的最大值。

若第 56 节的线性输出先经过一个以 $c_{\mathrm{out}}$ 为收缩常数的概率读出，则应取

$$
\tau_{h,T}
=
c_{\mathrm{out}}
\max_{n<T}
\left(
\|b_n\|+
X\sum_{r=h+1}^{n}\|K_r\|
\right).
$$

证明。先以真实历史与其规范化纤维代表比较，误差至多 $\varepsilon_{\mathrm{fib},T}$；再以代表的精确整数坐标与黄金坐标比较，误差至多 $L_T/\sqrt5$；最后以完整隐藏演化与 $h$-截断演化比较，误差至多 $\tau_{h,T}$。三次使用总变差的三角不等式即可。若线性尾项先在另一范数中给出，应用读出收缩性得到所列 $c_{\mathrm{out}}$ 因子。证毕。

这条合并预算的解释是：

$$
\text{总任务误差}
\le
\text{规范化纤维缺陷}
+
\text{黄金刻度误差}
+
\text{记忆尾项}.
$$

若给定目标 $\varepsilon$，只有在

$$
\varepsilon_{\mathrm{fib},T}
+
\frac{L_T}{\sqrt5}
+
\tau_{h,T}
\le\varepsilon
$$

时，才可把当前 Zeckendorf 读数、$h$-步历史截断和指定实验族一起当作一个满足该预算的有效对象。此判据仍是充分的预算检验，不是必要条件，也不是无条件的物理定律。

<a id="entry-186"></a>

### 推论 58.8（响应分离的安全裕量）

设有限标签集 $U$ 的代表响应满足

$$
\Delta_T
=
\min_{\substack{u\ne v\\u,v\in U}}
\max_{i\le m}
\operatorname{TV}\!\left(
\bar\kappa_i(u),\bar\kappa_i(v)
\right)>0.
$$

若

$$
2\left(
\frac{L_T}{\sqrt5}
+
\tau_{h,T}
\right)
+
2\varepsilon_{\mathrm{fib},T}
<
\Delta_T,
$$

则任意两个不同代表在实际完整任务响应中的分离仍为正；黄金刻度与记忆截断不会在该预算内把它们保证可分的响应合并成同一个预测分布。

证明。对每个代表的近似误差用定理 58.6 和命题 58.7 控制，再对两个代表应用总变差三角不等式的反向形式：

$$
\operatorname{TV}(p_u,p_v)
\ge
\operatorname{TV}(\bar\kappa(u),\bar\kappa(v))
-
\operatorname{TV}(p_u,\bar p_u)
-
\operatorname{TV}(p_v,\bar p_v).
$$

由假设右端为正。证毕。

这里“分离仍为正”只表示在所选实验族和预算下不会被这个近似模型保证为同一分布；它不保证一次有限样本实验必然正确判别，也不产生不相容量子测量的全局答案表。

<a id="entry-187"></a>

### 命题 58.9（规范化电荷的相位商）

沿用 Z 卷定理 21。若一条有限实际进位路径把原始行 $r$ 送到 $r'$，记其总电荷为 $z$，则

$$
\beta(r)-\beta(r')=z\in\mathbb Z.
$$

因此相位读出

$$
\chi(r)=\exp\!\left(2\pi i\,\beta(r)\right)
$$

满足

$$
\chi(r)=\chi(r').
$$

更一般地，若记录使用相位尺度 $\vartheta$，置 $\chi_{\vartheta}(r)=e^{i\vartheta\beta(r)}$，则

$$
\frac{\chi_{\vartheta}(r)}{\chi_{\vartheta}(r')}
=e^{i\vartheta z}.
$$

当 $\vartheta/(2\pi)\in\mathbb Z$ 时，所有规范化电荷都被该相位商抹去；当 $\vartheta/(2\pi)=a/b$ 为既约有理数时，只能看到 $z$ 模 $b$ 的信息；当 $\vartheta/(2\pi)$ 无理时，$e^{i\vartheta z}=1$ 当且仅当 $z=0$，所以不同整数电荷不会因这个相位因子相等。

证明。第一式是 Z 卷定理 21 的黄金值差公式。将其代入指数函数即得三种情形；有理情形使用 $e^{i2\pi az/b}=1$ 当且仅当 $b\mid z$，无理情形则由 $\vartheta z\in2\pi\mathbb Z$ 推出 $z=0$。证毕。

这说明“规范化前后相位相同”不是无条件事实，而是读出尺度的选择。相位只记录 $\beta$ 的某个商；若选取把整数电荷识别为零的尺度，规范化历史在该读数中严格不可见，但连续黄金值或另一相位尺度仍可能看见它。这个相位商应作为第 55 节 Gram 相位的一个明确输入参数，而不能从 Zeckendorf 唯一性自动推出。

<a id="entry-188"></a>

### 与现有章节的关系和边界

第 54 节的 $d_H$ 衡量指定实验族上的预测差异；本节给出一个由 Zeckendorf 规范行到该伪距离的充分上界。第 55 节的 Gram 特征值决定记录相干的衰减与相位回流；本节的 $\eta_Z$ 是数值坐标读数误差，两者不属于同一谱，也不能用黄金误差替代 Gram 谱隙。第 56 节的 $K_r$ 和 $\tau_{h,T}$ 衡量隐藏历史回流；本节只把其尾项与规范化纤维缺陷、刻度误差用三角不等式合并，未重新假设隐藏动力学是无记忆的。

若原始表尚未规范，必须先使用 $\nu$ 或明确给出其输入行的系数界；否则 $\Lambda_Z$ 的有限误差界不适用。若环境有初始关联、实验控制依赖完整历史、或代表响应不存在 Lipschitz 延拓，则定理 58.6--58.7 的相应项只能标为未验证，不能把 $1/\sqrt5$ 冒称为总误差。若 $\varepsilon_{\mathrm{fib},T}>0$，增加数值刻度精度也不能消除被规范化抹去的历史；应扩展记录或缩小实验族。

因此，Zeckendorf 在这条主线中的作用可以精确表述为：

$$
\boxed{
\text{规范行提供离散状态，}
\quad
\gamma_Z\text{ 提供有界误差的实数坐标，}
\quad
\varepsilon_{\mathrm{fib}}\text{ 测量规范化的历史损失，}
\quad
\tau_{h,T}\text{ 测量有限记忆截断的损失。}
}
$$

稳定的经典对象只有在这三项共同落入任务误差预算时才获得操作性支持。它不要求保留全部历史，也不允许仅凭一个漂亮的黄金刻度宣称历史已经消失。

本节为 repo-derived/open 理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

<a id="entry-189"></a>

## 追加锚（新终端）

<a id="section-59"></a>

## 59. 局部读出不能凭空恢复关联方向

第 54 节把有限实验族上的响应相同定义成一个预测商，第 57 节把所有有限 Heisenberg 迭代生成的统计放进无限 operator system，第 58 节再把观察深度和有限顺序词联系起来。本节补上一条不同的边界：

> **如果读出端口只接触局部扇区，且 Heisenberg 动力学保持该局部扇区不变，那么增加局部读出次数不会凭空产生关联扇区的信息。**

这不是“局部观察永远不能做 tomography”的普遍断言，而是一个带有明确扇区保持假设的条件定理。对应的现有 Lean 模块是 D5/S3/Quantum/PredictionDepth/LocalDynamicsNoTomography.lean，其冻结声明为 local_dynamics_no_tomography。本节所有解释仍标记为 repo-derived/open；没有新增 Lean 声明、形式覆盖或冻结状态。

<a id="entry-191"></a>

### 59.1 双系统的三种方向

令两个有限维系统的局部维数分别为 $$m$$ 和 $$n$$。在双系统 traceless-Hermitian 算子空间中，仓库模块 BipartiteSectorDecomposition.lean 定义了：

$$
\mathcal L_A
=
\operatorname{traceZeroHermitian}(m)
\otimes
\operatorname{scalarHermitian}(n),
$$

$$
\mathcal L_B
=
\operatorname{scalarHermitian}(m)
\otimes
\operatorname{traceZeroHermitian}(n),
$$

以及真正同时依赖两边的关联扇区：

$$
\mathcal C
=
\operatorname{traceZeroHermitian}(m)
\otimes
\operatorname{traceZeroHermitian}(n).
$$

在 Hilbert--Schmidt 实内积下，模块中的 bipartite_sector_decomposition 给出这些扇区的正交分解。相应维数为：

$$
\dim\mathcal L_A=m^2-1,
\qquad
\dim\mathcal L_B=n^2-1,
$$

$$
\dim\mathcal C=(m^2-1)(n^2-1).
$$

因此无关联局部方向的维数与真正关联方向的维数是两笔不同的账。把局部边缘读数做得更精细，只是在前两笔账内增加可见方向；它不会自动把第三笔账转移到前两笔账。

记局部可见扇区为：

$$
\mathcal V_{\mathrm{loc}}
=
\mathcal L_A+\mathcal L_B.
$$

由正交分解：

$$
\mathcal V_{\mathrm{loc}}\perp\mathcal C,
\qquad
\mathcal V_{\mathrm{loc}}\cap\mathcal C=\{0\}.
$$

这里的“方向”是算子空间中的方向，不是物理空间中的额外坐标轴。

<a id="entry-192"></a>

### 59.2 扇区保持给出严格的无生成结论

设 $$H$$ 是作用在上述算子空间上的 Heisenberg 线性演化，并假设：

$$
H(\mathcal V_{\mathrm{loc}})
\subseteq
\mathcal V_{\mathrm{loc}}.
$$

那么对任意自然数 $$t$$：

$$
H^t(\mathcal V_{\mathrm{loc}})
\subseteq
\mathcal V_{\mathrm{loc}}.
$$

再因为局部扇区与关联扇区正交，有：

$$
H^t(\mathcal V_{\mathrm{loc}})\cap\mathcal C
=
\{0\}.
$$

这正是 local_dynamics_no_tomography 的两部分结论。证明只使用两步：先对 $$t$$ 做迭代归纳，得到局部扇区保持；再用正交性说明其与 $$\mathcal C$$ 的交只能是零。它没有使用“观察者在系统外部”或“意识选择结果”的假设。

若状态差方向 $$D$$ 属于关联扇区，局部初始 effect $$x$$ 属于 $$\mathcal V_{\mathrm{loc}}$$，则所有局部未来读出都满足：

$$
\left\langle D,H^t x\right\rangle=0
\qquad
\text{对所有 }t\in\mathbb N.
$$

所以同一关联方向即使在整体状态中真实存在，也不会因为重复施加同一类局部 Heisenberg 读出而进入该读数。这里的“不能恢复”是相对于指定的局部 effect 族和指定的动力学而言的。

<a id="entry-193"></a>

### 59.3 一个两比特反例：局部边缘相同，关联读数相反

取两个 qubit，令 $$Z$$ 为 Pauli 矩阵。对 $$0\le\varepsilon\le1$$ 定义：

$$
\rho_{\pm}
=
\frac14
\left(
I\otimes I
\pm
\varepsilon\,Z\otimes Z
\right).
$$

这两个矩阵都是合法密度态。对任意 traceless 的局部 effect $$A\otimes I$$ 或 $$I\otimes B$$，有：

$$
\operatorname{Tr}\!\left(\rho_+(A\otimes I)\right)
=
\operatorname{Tr}\!\left(\rho_-(A\otimes I)\right),
$$

$$
\operatorname{Tr}\!\left(\rho_+(I\otimes B)\right)
=
\operatorname{Tr}\!\left(\rho_-(I\otimes B)\right).
$$

但关联 effect $$Z\otimes Z$$ 给出：

$$
\operatorname{Tr}\!\left(\rho_+(Z\otimes Z)\right)=\varepsilon,
\qquad
\operatorname{Tr}\!\left(\rho_-(Z\otimes Z)\right)=-\varepsilon.
$$

因此，局部边缘读数不能区分 $$\rho_+$$ 与 $$\rho_-$$，而联合读数可以区分。这个例子是有限矩阵计算，不是对仓库中新建定理的声明；它具体展示了 $$\mathcal C$$ 中的方向如何落在局部签名的核内。

仓库的 IncompleteObserverPhysicalCounterexample.lean 给出更一般的物理版本。冻结声明 incomplete_observer_physical_counterexample 表明：只要 identity 加上已选 centered effects 的可见空间存在非零正交残差，就能构造两个不同的 density states，它们对全部已选 effect 的读数相同。因而“当前签名相同”不能推出“整体状态相同”。

<a id="entry-194"></a>

### 59.4 目标在可见扇区内，才有签名充分性

对给定 centered effects，令可见空间为：

$$
\mathcal V
=
\operatorname{span}
\left(
\{I\}\cup\{E_i\}
\right).
$$

仓库的 TargetPredictionSufficiency.lean 中，冻结声明 target_prediction_sufficiency 将两件事放在同一命题中：

$$
A\in\mathcal V
\Longrightarrow
\text{所有 }E_i\text{ 的共同读数决定 }A\text{ 的期望值};
$$

而：

$$
A\notin\mathcal V
\Longrightarrow
\text{存在读数完全相同、但 }A\text{ 期望不同的两个物理态}.
$$

因此，局部读出是否足够，不能只问“测了多少次”，还要问目标 effect 是否落在局部可见空间及其动力学闭包中。若目标关联 effect 位于 $$\mathcal C$$，而 $$H$$ 满足局部扇区保持条件，那么所有迭代后的局部读出仍在 $$\mathcal V_{\mathrm{loc}}$$ 内，目标仍然位于该读出族的不可见残差。

这也说明第 57 节的最小预测摘要必须带有任务索引。对局部任务，$$\rho_+$$ 与 $$\rho_-$$ 可以属于同一预测类；加入联合目标后，它们被拆分为不同类。对象的等价性随允许的 effect 和动力学改变，而不是由一个脱离任务的标签决定。

<a id="entry-195"></a>

### 59.5 何时可以恢复关联方向？

要使关联方向进入可见响应，至少需要改变下列一项：

1. 增加一个具有关联分量的 effect，例如 $$Z\otimes Z$$；
2. 让 Heisenberg 演化违反局部扇区保持条件，使某个局部 effect 的迭代获得 $$\mathcal C$$ 分量；
3. 引入与两边共同耦合的 ancilla、联合记录或其他可执行的非局部协议。

第二种情形可写成：

$$
H(\mathcal V_{\mathrm{loc}})
\not\subseteq
\mathcal V_{\mathrm{loc}},
$$

但这只说明“有可能进入新的方向”，不自动保证已经完成 tomography。还必须计算由允许迭代生成的 visible span，并检查目标 effect 是否真的落入其中。第 57 节引用的 PredictionClosureDynamicalRepair.lean 提供了相应的最小动力学闭包框架：把初始 visible space 扩张到对演化不变的 observer closure，再在其正交残差上定义商。该框架使用有限维线性空间与伴随不变性；它不自动推广到任意开放量子系统。

<a id="entry-196"></a>

### 59.6 对“保留多少历史”的含义

局部记录保留的是边缘方向；关联扇区中的差异属于当前任务的历史残差。若动力学把局部空间封闭，那么这部分残差不会通过未来局部读出回流：

$$
\mathcal R_{\mathrm{corr}}
\subseteq
\mathcal V_{\mathrm{loc}}^{\perp},
\qquad
\left\langle
\mathcal R_{\mathrm{corr}},
H^t\mathcal V_{\mathrm{loc}}
\right\rangle=0.
$$

在这种条件下，继续增加同类局部记录不会减少关联残差；需要的是扩大端口或改变动力学。反之，若存在从关联扇区到局部扇区的耦合，则历史是否必须保留取决于该耦合在指定时间窗内产生的响应大小，不能仅由隐藏空间的维数决定。

这把“稳定经典现实”的一个边界写成了可检验条件：

$$
\boxed{
\text{局部读出足够}
\iff
\text{目标与允许未来统计都落在局部可见动力学闭包内};
}
$$

$$
\boxed{
\text{局部读出不足}
\iff
\text{存在非零关联残差在全部允许局部统计中保持不可见}.
}
$$

第二个判据是相对于指定读出族的判据，不是关于所有可能实验的本体论结论。加入联合测量、改变交互作用或扩大记录端口后，等价类和所需历史预算都可能改变。

本节是 repo-derived/open 的理论追加；引用的 Lean 模块已有冻结状态，但本节没有新增 Lean 声明、形式覆盖或冻结状态。

<a id="entry-197"></a>

## 追加锚（新终端）

<a id="section-60"></a>

## 60. 记录作用量、相干衰减与不可逆恢复下界

> **状态：repo-derived/open。** 本节整理并连接已有 Lean 结果，没有新增声明、证明覆盖或冻结状态。引用的冻结模块包括 D5/S3/Quantum/Decoherence/RecordActionCoherenceSurvival.lean、D5/S3/Quantum/PureState/RecordCoherenceComplementarity.lean、D5/S3/Quantum/Decoherence/FiniteShiftedRecordChannel.lean 与 D5/S3/Quantum/Decoherence/FiniteRecordRecoveryError.lean。这里的“作用量”是有限记录模型中的数学量，不是一个已从项目推出的普适物理作用量。

第 55 节已经给出单步记录的 Gram 系数。本节把它累积为记录作用量，再连接到有限移位记录模型中的恢复误差下界：

$$
\text{条件记录重叠}
\longrightarrow
\text{累计相干}
\longrightarrow
\text{记录作用量}
\longrightarrow
\text{恢复误差下界}.
$$

“不可逆”首先是操作意义上的：指定记录被丢弃以后，任何只作用于剩余系统的恢复通道，都不能把最坏情形误差压到下界以下。这不等于说包括环境在内的联合幺正演化不可逆。

<a id="entry-199"></a>

### 60.1 记录重叠的乘积与作用量

设有限标签集为 $$
I
$$，第 $$
r
$$ 次记录给标签 $$
i
$$ 留下归一化环境向量 $$
e_{r,i}
$$。定义单步 Gram 系数

$$
g_r(i,j)=\langle e_{r,j},e_{r,i}\rangle .
$$

归一化与 Cauchy--Schwarz 不等式给出

$$
|g_r(i,j)|\le 1.
$$

若某个相干矩阵元在每一步都乘上这个系数，则 $$
N
$$ 次记录后的累计系数为

$$
C_N(i,j)=\prod_{r<N}g_r(i,j),
$$

从而

$$
|C_N(i,j)|=\prod_{r<N}|g_r(i,j)|.
$$

在非负扩展实数中定义记录作用量

$$
\mathsf A_N(i,j)=-\log |C_N(i,j)|.
$$

当某个因子为零时，右侧按扩展值解释为无穷；这正是一次完全正交记录把该相干坐标压到零的情形。冻结定理 RecordActionCoherenceSurvival.record_action_controls_coherence_survival 给出：

$$
\mathsf A_{N+1}(i,j)\ge \mathsf A_N(i,j),
$$

以及精确的相干存活关系

$$
|\rho_N(i,j)|
=
\exp\!\bigl(-\mathsf A_N(i,j)\bigr)
|\rho_0(i,j)|.
$$

若记录作用量的平均率存在，即

$$
\lim_{N\to\infty}\frac{\mathsf A_N(i,j)}{N}=\lambda,
$$

并且初始相干非零，则相对相干的负对数率也是 $$
\lambda
$$：

$$
\lim_{N\to\infty}
\frac{-\log\!\left(|\rho_N(i,j)|/|\rho_0(i,j)|\right)}{N}
=
\lambda.
$$

若每一步满足统一严格收缩界

$$
|g_r(i,j)|\le q<1,
$$

则

$$
|C_N(i,j)|\le q^N,
\qquad
\mathsf A_N(i,j)\ge -N\log q.
$$

这给出一个可计算的记录预算。相反，若某些步满足 $$
|g_r(i,j)|=1
$$，则该方向可能只发生相位旋转而没有模长衰减，甚至周期性返回。因此，固定点呈经典形式不能单独推出所有初态都会趋向经典；还必须检查非对角 Gram 系数的模长。

把单步系数写成

$$
g_r(i,j)=|g_r(i,j)|\exp\!\bigl(\mathrm i\varphi_r(i,j)\bigr),
$$

则

$$
C_N(i,j)
=
\exp\!\left(
-\mathsf A_N(i,j)
+
\mathrm i\sum_{r<N}\varphi_r(i,j)
\right).
$$

作用量只记账模长衰减；累计相位是另一项动力学数据。不能把作用量、Zeckendorf 坐标误差或 Fibonacci 权重直接解释为物理能量或 Hamiltonian 频率。

<a id="entry-200"></a>

### 60.2 记录重叠同时限制可区分性与可见相干

对两个归一化纯记录 $$
e_L,e_R
$$，令

$$
c=\langle e_L,e_R\rangle,
\qquad
\mathsf V=|c|,
\qquad
\mathsf D=\sqrt{1-|c|^2}.
$$

冻结定理 PureState.RecordCoherenceComplementarity.pure_record_distinguishability_coherence_complementarity 证明

$$
\mathsf D^2+\mathsf V^2=1.
$$

于是正交记录满足

$$
c=0
\quad\Longrightarrow\quad
\mathsf D=1,\quad \mathsf V=0,
$$

而同一量子态射线上的记录满足

$$
|c|=1
\quad\Longrightarrow\quad
\mathsf D=0,\quad \mathsf V=1.
$$

这项等式只适用于声明中的归一化纯记录，不能无条件推广到混合记录或任意开放系统。对有限记录链，可把每一步的可见度相乘：

$$
\mathsf V_N(i,j)=|C_N(i,j)|=\exp\!\bigl(-\mathsf A_N(i,j)\bigr).
$$

因此，标签差异本身不决定可区分性。两个 Zeckendorf 合法构型即使数值不同，也可能留下同一条记录射线；反过来，是否正交取决于实际记录向量，而不取决于标签名称。

<a id="entry-201"></a>

### 60.3 有限移位记录通道

FiniteShiftedRecordChannel.lean 给出一个具体有限实现。令

$$
c:\mathbb Z\to\mathbb C
$$

在区间 $$
0,\ldots,N
$$ 外为零，并满足

$$
\sum_{n=0}^{N}|c(n)|^2=1.
$$

给每个系统标签 $$
i
$$ 一个整数位置 $$
q_i
$$。平移后的系数产生有限环境记录，其自相关函数为

$$
\gamma(\ell)
=
\sum_{n=0}^{N}c(n+\ell)\,\overline{c(n)}.
$$

相应通道在矩阵元上的作用为

$$
\Lambda(A)_{kl}
=
\gamma(q_k-q_l)A_{kl}.
$$

所以对角元不变，非对角元按标签位移的自相关系数缩放。该模块证明此构造来自有限维等距嵌入并实现量子通道；它没有额外证明空间局域性、指定 Hamiltonian 的守恒律、零操作成本或任意设备上的普适性。

若

$$
|\gamma(q_i-q_j)|<1,
$$

该相干方向经过一次记录即收缩；若模长等于一，则它可能只获得相位。相同的 Zeckendorf 数值差在不同记录波形下也可以对应不同的自相关值，因此离散刻度不决定记录强度。

<a id="entry-202"></a>

### 60.4 恢复误差的不可绕过下界

考虑任意候选恢复通道 $$
R
$$。冻结定理 FiniteRecordRecoveryError.finite_record_recovery_error_lower_bound 假设有限支持、系数归一化，以及选定的非零位移

$$
q_i-q_j\ne0.
$$

对所有密度态取最坏情形迹距离误差，得到

$$
\boxed{
\sup_{\rho}
D\!\left(R\circ\Lambda(\rho),\rho\right)
\ge
\frac{1-|\gamma(q_i-q_j)|}{2}.
}
$$

定理源码把左侧表示为误差集合的上确界，并使用迹距离的收缩性证明该不等式。

见证态是 $$
i,j
$$ 两个标签上的对称与反对称叠加：

$$
|+\rangle=\frac{|i\rangle+|j\rangle}{\sqrt2},
\qquad
|-\rangle=\frac{|i\rangle-|j\rangle}{\sqrt2}.
$$

记录前两态的距离为

$$
D(|+\rangle\langle+|,\ |-\rangle\langle-|)=1,
$$

记录后距离变为

$$
D\!\left(
\Lambda(|+\rangle\langle+|),
\Lambda(|-\rangle\langle-|)\right)
=
|\gamma(q_i-q_j)|.
$$

任何量子通道都不会增加迹距离；将收缩性与三角不等式用于恢复后的两态，就得到上述下界。记录已经降低的这部分区分度，不能由只访问记录后系统的统一恢复无条件补回。

特别地，

$$
\gamma(q_i-q_j)=0
\quad\Longrightarrow\quad
\sup_{\rho}D(R\circ\Lambda(\rho),\rho)\ge\frac12.
$$

而

$$
|\gamma(q_i-q_j)|\approx1
$$

只表示这个下界接近零，并不保证存在零误差恢复。若恢复端还可以访问未丢弃的环境记录，问题已经变成联合系统上的恢复任务，不能继续套用只在系统端恢复的同一结论。

<a id="entry-203"></a>

### 60.5 作用量、恢复下界与 Zeckendorf 接口

设有限合法 Zeckendorf 构型集合为

$$
\mathcal W_L
=
\left\{
w\in\{0,1\}^{L}:w_rw_{r+1}=0
\right\},
$$

并给每个构型一个整数标签 $$
q(w)
$$。为每个构型选择条件记录 $$
e_{r,w}
$$，便得到

$$
g_r(w,v)=\langle e_{r,v},e_{r,w}\rangle,
\qquad
C_N(w,v)=\prod_{r<N}g_r(w,v).
$$

这一步只把合法构型接入记录模型；它没有指定记录向量的制备，也没有把 Fibonacci 权重自动变成能量。若采用移位记录接口，还必须给出整数标签 $$
q(w)
$$、有限波形 $$
c
$$ 及其支持条件，才能使用 $$
\gamma(q(w)-q(v))
$$ 的恢复定理。

在该接口上，可以分别记录两种损失：

$$
\mathsf A_N(w,v)=-\log|C_N(w,v)|,
$$

以及有限移位模型中的恢复下界

$$
\varepsilon_{\mathrm{rec}}^{\mathrm{lb}}(w,v)
=
\frac{1-|\gamma(q(w)-q(v))|}{2}.
$$

前者是多步相干存活的对数记账，后者是特定一次通道的恢复障碍。两者不是同一个量，不能相加，也不能互相替代。

若每一步都有

$$
|g_r(w,v)|\le q<1,
$$

则

$$
\mathsf A_N(w,v)\ge-N\log q
$$

给出长期收缩的充分条件；若存在单位模重叠，则该方向可能持续回流。因此，判断一个记录是否足以支持稳定的经典预测，必须同时指定：

$$
\text{记录波形}
\;+\;
\text{可访问的环境范围}
\;+\;
\text{允许的恢复操作}
\;+\;
\text{预测时间窗}.
$$

仅知道 Zeckendorf 标签数量或记录次数，不足以确定这些量。

<a id="entry-204"></a>

### 60.6 与前面章节的衔接和边界

第 55 节的 Gram 谱给出单步模长收缩与相位信息；本节把模长收缩累积为作用量，并用有限移位实例给出恢复下界。第 56 节的记忆视界描述隐藏变量怎样回流到读出；本节的乘积公式只适用于记录向量和相干坐标已按给定协议组成的有限链，不能替代有记忆联合演化。第 57 节的无限未来预测商决定全部指定未来统计下的不可区分类；本节只针对特定记录通道给出相干与恢复量，不等同于无限实验族的操作商。

适用边界可写成：

$$
\begin{aligned}
&\text{记录作用量：归一化记录与有限步乘积；非零初始相干用于速率商；}\\
&\text{互补关系：归一化纯记录，不自动推广到混合记录；}\\
&\text{恢复下界：有限移位记录、有限支持、非零标签位移；}\\
&\text{物理解释：不推出 Hamiltonian、空间局域性或普适恢复定理。}
\end{aligned}
$$

因此，本节支持的研究命题是：

$$
\boxed{
\text{记录作用量量化相干被削弱的累计程度，}
\quad
\text{记录自相关给出有限模型中不可逆恢复的下界。}
}
$$

它把“保留多少历史才能得到稳定现实”改写成可检验的问题：在给定 Zeckendorf 合法构型、记录协议和预测视界下，哪些相干方向的作用量已经足够大，哪些方向仍可由可访问关联恢复，以及恢复误差是否超过任务容限。

本节为 repo-derived/open 理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

<a id="entry-205"></a>

## 追加锚（新终端）

<a id="section-61"></a>

## 61. 观察精炼、商空间度量与容量守恒

第 57 节把对象定义为全部指定未来统计下的预测等价类，第 59 节说明局部端口若不接触关联扇区，就不能凭空恢复关联信息，第 60 节则给出记录作用量和恢复误差的下界。本节把“增加约束或增加读出究竟保留了什么”写成一个有限维账本：观察精炼增加可见方向，同时减少不可见残差；在固定载体上，两者的总维数保持不变。

本节使用以下冻结 Lean 结果：`ObserverRefinementVisibleResidualEquivalence.lean` 中的 `observer_refinement_visible_residual_equivalence`，`OperationalObservationKernel.lean` 中的 `operational_observation_kernel_and_metric`，以及 `ObserverCapacityConservation.lean` 中的 `observer_capacity_conservation`。正文仍是 `repo-derived/open` 解释，不新增 Lean 声明，也不把有限维结论提升为任意物理系统的普遍定律。

<a id="entry-207"></a>

### 61.1 可见空间与残差空间

令系统维数为

$$
d\in\mathbb N,
$$

并在实 Hermitian 算子空间中给定一族 effect。对一个 effect 集合

$$
E\subseteq\operatorname{Herm}(d),
$$

定义包含单位方向的可见空间

$$
\mathcal V(E)
=
\operatorname{span}_{\mathbb R}
\bigl(\{I_d\}\cup E\bigr),
$$

以及其 Hilbert--Schmidt 正交残差

$$
\mathcal R(E)=\mathcal V(E)^{\perp}.
$$

单位方向单独列出，是因为密度态的归一化已经固定了迹；真正增加区分能力的是去掉单位方向以后新增的可见维数。这里的残差是相对于这组 effect 的算子空间残差，不是一个额外物理介质，也不是尚未证明存在的隐藏变量。

若两个密度态在所有选定 effect 上读数相同，它们的状态差落在相应残差中。反过来，残差方向在这些线性读数中不可见；是否能在未来出现，还要再结合第 57 节的动力学闭包条件。

<a id="entry-208"></a>

### 定理 61.1（观察精炼的三重等价）

设 `one` 和 `two` 是两组有限维 Hermitian effect，`two` 至少包含 `one` 所提供的可见信息。仓库中的 `observer_refinement_visible_residual_equivalence` 给出以下等价关系：

$$
\begin{aligned}
&\text{精细签名相同}\Rightarrow\text{粗签名相同}\\
&\qquad\Longleftrightarrow\qquad
\mathcal R_{\mathrm{two}}
\subseteq
\mathcal R_{\mathrm{one}}\\
&\qquad\Longleftrightarrow\qquad
\mathcal V_{\mathrm{one}}
\subseteq
\mathcal V_{\mathrm{two}}.
\end{aligned}
$$

第一行的量词是对所有密度态对：如果两态的精细签名相等，则它们的粗签名也相等。第二行是残差包含关系；第三行是可见空间包含关系。形式化定理在有限维 Hermitian 载体上同时保留了这三个方向，因而不能把“更细”只理解成标签数量增加。

这条等价解释了为什么残差方向是反变的：读出越丰富，可见空间越大，残差越小。若只改变标签名称而没有改变 effect span，三种关系都不变，也就没有获得新的预测能力。

<a id="entry-209"></a>

### 定理 61.2（观察半范数的核与商空间度量）

给定有限 effect 索引集、严格正的权重和 centered effects，定义一个加权观察半范数。冻结结果 `operational_observation_kernel_and_metric` 的第一部分把它的核识别为 effect span 的正交补：

$$
\operatorname{ker}\|D\|_{\mathrm{obs}}
=
\operatorname{span}_{\mathbb R}
\{E_i\}^{\perp}.
$$

因此，对密度态差

$$
D=\rho-\sigma,
$$

半范数为零，恰好表示当前 effect 家族无法区分这两个状态。它在状态空间上只给出伪距离；把零距离状态取商以后，诱导的 `operationalQuotientDistance` 满足非负性、对称性和三角不等式，并且

$$
\bar d([\rho],[\sigma])=0
\iff
[\rho]=[\sigma].
$$

这使“对象是一个读数等价类”获得了一个内部几何：距离不是预先附加的物理空间距离，而是由允许的 effect、权重和读出范数共同定义的操作距离。

冻结结果还给出分离条件：若原状态空间上的伪距离已经是严格距离，则这组 effect 对密度态是 informationally complete。反之，存在非零残差就意味着至少有两个不同状态落入同一个操作类。这里的 `informationally complete` 只针对指定的密度态与 effect 集合，不能推出对任意序列仪器或任意开放系统都完备。

<a id="entry-210"></a>

### 定理 61.3（可见容量与残差容量守恒）

对任意 effect 集合 $E$，令

$$
C(E)
=
\dim_{\mathbb R}\mathcal V(E)-1,
\qquad
Q(E)
=
\dim_{\mathbb R}\mathcal R(E).
$$

`observer_capacity_conservation` 证明，在固定的实 Hermitian 载体上：

$$
\boxed{
C(E)+Q(E)=d^2-1.
}
$$

其中 $d^2$ 是完整 Hermitian 载体的实维数，减去一维单位方向后得到 traceless 方向总数。若粗 effect 集合包含于细 effect 集合，则

$$
C(E_{\mathrm{coarse}})
\le
C(E_{\mathrm{fine}}),
$$

并且

$$
Q(E_{\mathrm{fine}})
\le
Q(E_{\mathrm{coarse}}).
$$

所以每增加一个真正独立的可见方向，残差容量至少相应减少；如果新增 effect 落在原有 span 中，两个容量都不改变。这个守恒式给出的是维数账本，不是信息熵守恒，也不是说每个新增 effect 都携带一个独立可读取的经典 bit。

<a id="entry-211"></a>

### 61.4 接到 Zeckendorf 合法构型

令

$$
\mathcal W_L
=
\{w\in\{0,1\}^L:w_rw_{r+1}=0\},
$$

并把合法构型映到第 58 节的黄金坐标或某个指定的 effect 家族。若窗口扩大、记录端口增加，得到的不是自动的“更多历史”，而是一组新的 effect。应分别计算

$$
\mathcal V_L=\operatorname{span}_{\mathbb R}\bigl(\{I\}\cup E_L\bigr),
\qquad
\mathcal R_L=\mathcal V_L^{\perp},
$$

再比较

$$
C_L=\dim_{\mathbb R}\mathcal V_L-1,
\qquad
Q_L=\dim_{\mathbb R}\mathcal R_L.
$$

Zeckendorf 约束只规定合法构型集合及其离散坐标；它不自动规定 effect 的线性独立性，也不自动把窗口长度 $L$ 转成可见容量 $C_L$。若新增构型只改变编号、不改变读出 span，容量不变；若新增构型引入了新的可区分 effect，容量才增加。相应的相干与历史影响仍须用第 55、56 和 60 节的 Gram、回流和作用量计算。

<a id="entry-212"></a>

### 61.5 观察距离的任务依赖

设实验族改变了 effect 集合或权重，则半范数、商空间和容量账本都会改变。于是两个状态可能满足

$$
\bar d_{\mathfrak T_1}([\rho],[\sigma])=0,
$$

而在更细任务上满足

$$
\bar d_{\mathfrak T_2}([\rho],[\sigma])>0.
$$

这不是逻辑矛盾，而是两个观察商不同。第 54 节的有限响应商、第 57 节的无限未来商和本节的线性 effect 商，只有在明确给出 effect、channel 与时间范围后才能比较。把它们不加条件地合并成一个“最终对象空间”，会丢掉它们各自的操作边界。

因此，“用多少约束保留历史”可以拆成三个可测量问题：

$$
\begin{aligned}
&\text{当前读出保留了多少可见维数？}\\
&\text{剩余残差在指定未来动力学下是否闭合？}\\
&\text{记录作用量和任务误差是否允许忽略该残差？}
\end{aligned}
$$

第一问由 $C(E)$ 和 $Q(E)$ 结算，第二问由第 57 节的 observer closure 与第 59 节的扇区保持条件结算，第三问由第 56、58、60 节的误差预算结算。三者共同决定当前尺度上是否可以把某个操作等价类当作稳定对象。

本节为 `repo-derived/open` 理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

<a id="entry-213"></a>

## 追加锚（新终端）

<a id="section-62"></a>

## 62. 有限观察深度、稳定塔与顺序词完备性

第 61 节给出了静态观察精炼的容量守恒，但“增加一次后续操作”还需要一个时间方向的版本。本节把初始 effect 在 Heisenberg 作用下的前 $n$ 次迭代组成观察塔，证明可见空间随深度单调增加、残差反向减少，并在有限维条件下得到稳定深度。随后把同一思想推广到 sequential instrument words。

使用的冻结模块是 `FiniteTimeObserverMonotonicity.lean` 的 `finite_time_observer_monotonicity`、`CenteredEffectStabilityDepthBound.lean` 的 `centered_effect_stability_depth_bound`、`FiniteSequentialCompletenessDepth.lean` 的 `finite_sequential_completeness_depth`，以及 `UnifiedSequentialKernel.lean` 的 `unified_sequential_kernel`。本节仍为 `repo-derived/open` 理论解释，没有新增 Lean 声明。

<a id="entry-215"></a>

### 定义 62.1（有限 Heisenberg 观察塔）

令 $H$ 是 Hermitian 载体上的 Heisenberg 线性作用，初始 effect 家族为

$$
E_0=\{E_i: i\in I\}.
$$

定义 horizon 为 $n$ 的可见空间

$$
\mathcal V_n
=
\operatorname{span}_{\mathbb R}
\left(
\{I\}\cup
\{H^tE_i:t<n,\ i\in I\}
\right),
$$

以及有限深度残差

$$
\mathcal R_n=\mathcal V_n^{\perp}.
$$

这里的 $n$ 是允许的后续迭代次数，不是物理时间单位；是否存在连续时间生成元需要另外的动力学假设。

<a id="entry-216"></a>

### 定理 62.2（观察深度的单调性）

冻结结果 `finite_time_observer_monotonicity` 证明对每个 $n$：

$$
\mathcal V_n\subseteq\mathcal V_{n+1},
$$

并且正交残差满足反向包含

$$
\mathcal R_{n+1}subseteq\mathcal R_n.
$$

证明只使用 $t<n$ 蕴含 $t<n+1$，以及正交补对包含关系的反变性。它给出一个可计算的观察偏序：增加允许的后续操作不会让已经可见的线性方向消失，但会缩小当前任务仍无法区分的残差。

对两个状态坐标差 $D$，若

$$
D\in\mathcal R_n,
$$

则所有深度小于 $n$ 的 effect 读数都相同。若在某个更大深度首次有

$$
D\notin\mathcal R_{n+1},
$$

这说明新加入的一步确实把该历史差异带入了可见响应。这个结论是线性读数的结论，不等于一次有限样本实验必然识别出该差异。

<a id="entry-217"></a>

### 定理 62.3（有限维稳定深度）

在 trace-zero Hermitian 载体上，令 `towerSpace` 表示由初始 centered effects 和前面各层的 Heisenberg 像递归生成的空间，令 `predictiveSpace` 是所有有限迭代的 span。冻结结果 `centered_effect_stability_depth_bound` 定义最小一步稳定深度

$$
\operatorname{sd}(H,E)
=\min\{m:\mathcal T_m=\mathcal T_{m+1}\}.
$$

它给出

$$
\operatorname{sd}(H,E)
\le
\dim(\mathcal V_{\infty})-\dim(\mathcal T_0),
$$

以及

$$
\dim(\mathcal V_{\infty})-\dim(\mathcal T_0)
\le
 d^2-1-\dim(\mathcal T_0).
$$

更强的是，一旦某一步满足

$$
\mathcal T_m=\mathcal T_{m+1},
$$

以后所有层都保持相同；并且

$$
\mathcal V_{\infty}
=\bigcup_{n\ge0}\mathcal T_n
=\mathcal T_{\operatorname{sd}(H,E)}.
$$

因此，在固定有限维载体与固定线性 Heisenberg 作用下，“所有有限未来 effect”虽然以无限并集定义，却有一个有限深度的线性证书。这个证书的上界来自 traceless-Hermitian 载体维数，而不是来自 Zeckendorf 窗口长度本身。

<a id="entry-218"></a>

### 62.4 顺序词不是单时刻标签的重复

令 `Alphabet` 是允许的仪器字母，令

$$
\mathsf E_w
$$

表示由字 $w$ 经过指定 instrument-dual 顺序折叠得到的 sequential word effect。对一个允许词集合

$$
\mathcal A\subseteq\operatorname{List}(\mathrm{Alphabet}),
$$

定义顺序可见空间

$$
\mathcal V_{\mathcal A}
=\operatorname{span}_{\mathbb R}
\{\mathsf E_w:w\in\mathcal A\}.
$$

顺序词记录了操作次序；它不应被替换成只保存每个单步标签的无序集合。不同词可能拥有相同的最终经典标签，却对应不同的 effect 和不同的后续响应。

<a id="entry-219"></a>

### 定理 62.5（统一顺序核）

冻结结果 `unified_sequential_kernel` 给出：对任意状态表示 $s$、$s'$，所有允许顺序词的统计相等，当且仅当状态差落在顺序可见空间的正交残差中：

$$
\begin{aligned}
&\forall w\in\mathcal A,
\quad
\langle s,\mathsf E_w\rangle
=
\langle s',\mathsf E_w\rangle\\
&\qquad\Longleftrightarrow\\
&s-s'\in\mathcal V_{\mathcal A}^{\perp}.
\end{aligned}
$$

因此，历史压缩的安全条件不是“最终标签相同”，而是所有允许顺序词对这两个历史给出相同统计。若再加入一个新词，空间变为

$$
\mathcal V_{\mathcal A\cup\{w_0\}},
$$

残差只会缩小或保持不变；新词是否真正增加信息，要看 $\mathsf E_{w_0}$ 是否已经落在旧 span 中。

<a id="entry-220"></a>

### 定理 62.6（顺序词的有限完备深度）

若所有有限 sequential word effects 在完整实 Hermitian 载体中张成单位空间，即

$$
\operatorname{span}_{\mathbb R}
\{\mathsf E_w:w\text{ 为任意有限词}\}
=\operatorname{Herm}(d),
$$

则 `finite_sequential_completeness_depth` 保证存在某个

$$
N\le d^2-1
$$

使长度不超过 $N$ 的 sequential words 已经张成完整 Hermitian 可见空间：

$$
\operatorname{span}_{\mathbb R}
\{\mathsf E_w:\lvert w\rvert\le N\}
=\operatorname{Herm}(d).
$$

这里的完备性是假设了所有有限词的总 span 已经完整；定理只把这个无界假设压缩成一个有限深度证书，不声称任意给定仪器族自动满足它。它也不说单个时间片的 POVM 必然 informationally complete。

<a id="entry-221"></a>

### 62.7 接到 Zeckendorf 窗口和记忆视界

对合法 Zeckendorf 构型集合

$$
\mathcal W_L
=\{w\in\{0,1\}^L:w_rw_{r+1}=0\},
$$

可以把窗口内每个构型映射成初始 effect，或映射成允许的 sequential word。此时有三种彼此不同的深度参数：

$$
\begin{aligned}
&L: \text{合法离散构型窗口长度},\\
&N: \text{观察词的最大操作长度},\\
&h: \text{第 56 节隐藏历史的截断深度}.
\end{aligned}
$$

$L$ 增大可能增加构型数，但不保证 $\mathcal V_L$ 增维；$N$ 增大只在新增 effect 不在旧 span 时增加可见方向；$h$ 增大控制的是隐藏回流尾，而不是线性 effect span 的稳定深度。将三者混成一个“观察深度”会把离散编码、操作次序和环境记忆混为一谈。

因此，在任务误差 $\varepsilon$ 下，一个可检查的停止判据可以写成：先找到 $N$ 使线性观察塔稳定，再估计第 56 节的记忆尾和第 58、60 节的刻度与记录误差，要求合并预算不超过 $\varepsilon$。只有在这个复合条件下，才可以把有限深度摘要作为当前任务的有效对象。

本节为 `repo-derived/open` 理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

<a id="entry-222"></a>

## 追加锚（新终端）

<a id="section-63"></a>

## 63. 约化不可见、整体可逆与恢复误差下界

第 60 节已经把记录作用量与恢复下界分开。本节进一步区分两种常被混称为“不可逆”的现象：一是只访问约化态时无法从同一个输入恢复不同的联合记录；二是包括记录自由度在内的整体演化是否真的不可逆。仓库中的可逆复制模型给出一个明确反例：前者可以成立，而后者仍然完全可逆。

本节引用 `ReducedRecordAccessDefect.lean` 的 `reduced_irreversibility_is_access_defect`、`CanonicalRecordAccessRecovery.lean` 的 canonical-record 包装，以及 `FiniteRecordRecoveryError.lean` 的 `finite_record_recovery_error_lower_bound`。这些结果都是有限矩阵和有限通道命题，正文继续标记为 `repo-derived/open`。

<a id="entry-224"></a>

### 63.1 受控复制的联合演化

令系统是一个 qubit，环境记录也是一个两态自由度。对系统矩阵 $\rho$，先把环境置于空白态，记为

$$
B(\rho).
$$

受控复制幺正 $U_{\mathrm{copy}}$ 把系统地址写入记录，得到

$$
U_{\mathrm{copy}}B(\rho)U_{\mathrm{copy}}^{\dagger}
=
J(\rho),
$$

其中 $J(\rho)$ 是带有 copied-address record 的联合态。`ReducedRecordAccessDefect` 明确构造了这个 permutation unitary，并证明其满足

$$
U_{\mathrm{copy}}^{\dagger}U_{\mathrm{copy}}=I.
$$

因此，联合系统的演化有显式逆

$$
U_{\mathrm{copy}}^{\dagger}J(\rho)=B(\rho).
$$

这一步只使用整体记录仍然可访问的假设；它没有说任何局部观察者都能访问环境。

<a id="entry-225"></a>

### 定理 63.1（约化访问缺陷）

设两个系统态 $\rho,\sigma$ 满足相同的对角元

$$
\forall i,\qquad \rho_{ii}=\sigma_{ii},
$$

但存在非对角位置 $i\ne j$ 使

$$
\rho_{ij}\ne\sigma_{ij}.
$$

冻结定理 `reduced_irreversibility_is_access_defect` 给出以下同时成立的事实：

$$
\operatorname{Tr}_{E}J(\rho)
=
\operatorname{Tr}_{E}J(\sigma),
$$

但

$$
J(\rho)\ne J(\sigma),
$$

并且不存在只依赖约化态的函数 $F$，同时满足

$$
F(\operatorname{Tr}_{E}J(\rho))=J(\rho),
\qquad
F(\operatorname{Tr}_{E}J(\sigma))=J(\sigma).
$$

另一方面，访问完整记录并施加逆耦合时，分别有

$$
U_{\mathrm{copy}}^{\dagger}J(\rho)=B(\rho),
\qquad
U_{\mathrm{copy}}^{\dagger}J(\sigma)=B(\sigma).
$$

所以这里真正失败的是访问范围：相同的约化输入被要求映到两个不同联合输出，任何约化态函数都无法完成；整体联合演化仍保留了区分，并且有明确的逆。

<a id="entry-226"></a>

### 63.2 与经典记录的关系

对角元相同的条件意味着，受控复制后对环境做偏迹会抹掉该模型中的非对角相干。若把环境记录也纳入整体，非对角差异并没有从联合态中消失；它只是被转移到系统—记录关联中。因而必须区分：

$$
\begin{aligned}
&\text{局部约化不可见},\\
&\text{联合态仍然不同},\\
&\text{访问联合记录后可逆恢复}.
\end{aligned}
$$

`CanonicalRecordAccessRecovery` 把同一个结论接到项目的 canonical `copiedAddressRecord`，说明这不是两个定义方向造成的记号差异。它仍然是特定 qubit 复制模型的结果，不是任意偏迹通道都可逆的断言。

这个例子也修正了“去相干就是历史删除”的说法。若记录被丢弃，历史对该局部读出不可见；若记录保留并可控，历史差异仍可能恢复。是否称为“消失”，必须先指定访问的代数和允许的恢复操作。

<a id="entry-227"></a>

### 63.3 有限移位记录的通道系数

令有限记录振幅为

$$
c:\mathbb Z\longrightarrow\mathbb C,
$$

其支撑位于有限区间并满足归一化

$$
\sum_{k\in\mathbb Z}|c(k)|^2=1.
$$

定义记录自相关

$$
\gamma(\ell)
=
\sum_{k\in\mathbb Z}c(k+\ell)\,\overline{c(k)}.
$$

给每个系统标签 $i$ 一个整数位置 $q(i)$，则 `FiniteShiftedRecordChannel` 产生的 Heisenberg 作用按逐项乘法写成

$$
\Lambda(A)_{ij}
=
\gamma\bigl(q(i)-q(j)\bigr)A_{ij}.
$$

因此，对角元保持不变，非对角元由记录自相关调节。这里的 $\gamma$ 是有限移位模型的输入，不是任意记录通道都必须具有的普适函数。

`finite_record_pair_witnesses` 构造两个只在 $i,j$ 位置有相反相干符号的纯态，使其初始迹距离为

$$
D(\rho,\sigma)=1,
$$

而经过 $\Lambda$ 后的距离恰为

$$
D(\Lambda\rho,\Lambda\sigma)
=|\gamma(q(i)-q(j))|.
$$

这个见证把 Gram 或自相关系数直接连接到一个可测的最坏方向：不是所有初态都按同一个相干速率衰减，至少有一对相位方向实现该系数。

<a id="entry-228"></a>

### 定理 63.2（有限记录恢复的误差下界）

对任意候选量子通道 $R$ 作为恢复操作，冻结定理 `finite_record_recovery_error_lower_bound` 给出

$$
\sup_{\tau}
D\bigl(R\Lambda(\tau),\tau\bigr)
\ge
\frac{1-|\gamma(q(i)-q(j))|}{2},
$$

其中 $q(i)-q(j)\ne0$，上确界遍历该有限标签空间的密度态。若记录完全区分这两个位置，使

$$
\gamma(q(i)-q(j))=0,
$$

则这个模型中的任何恢复都存在至少 $1/2$ 的最坏迹距离误差；若

$$
|\gamma(q(i)-q(j))|=1,
$$

该下界变为零，但这只表示该见证方向没有给出正的恢复障碍，不表示任意通道都可被完美恢复。

这个下界和第 60 节的记录作用量承担不同工作：作用量描述相干模长的累计损失；这里的下界描述在指定有限通道族中，丢弃记录后恢复误差至少有多大。二者不能互相替代。

<a id="entry-229"></a>

### 63.4 接到 Zeckendorf 历史与访问预算

若把合法 Zeckendorf 构型 $w$ 映到整数位置 $q(w)$，则记录自相关只看位置差

$$
q(w)-q(v),
$$

而不自动保留完整的规范化来源。两个不同历史可以有相同位置差，因而拥有相同的该通道系数；这并不说明它们在第 54 节的全部实验族上等价。要把它们合并，仍须检查所有允许读出和后续操作。

恢复能力可以用三项预算描述：

$$
\begin{aligned}
&\text{局部可访问记录的范围},\\
&\text{记录自相关的模长 }|\gamma(\ell)|,\\
&\text{允许恢复通道的类别}.
\end{aligned}
$$

扩大访问范围可能把约化不可见变成联合可见；改变记录分布会改变 $\gamma$ 和第 60 节的作用量；限制恢复通道则会提高可达到的最坏误差。单独知道 Zeckendorf 标签的数量或记录次数，不能决定这三项。

因此，对“多少约束足以形成稳定经典现实”的一个更精确表述是：在指定访问代数和恢复通道类下，约化不可见的历史残差是否已经低于任务误差；若未低于，则需要保留记录关联或扩大可访问端口，而不是仅仅增加数值刻度精度。

本节为 `repo-derived/open` 理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

<a id="entry-230"></a>

## 追加锚（新终端）

<a id="section-64"></a>

## 64. 记录类、指数去相干与经典块的形成

第 63 节说明偏迹后的不可见可以来自访问缺陷，而不是整体信息消灭。本节处理另一种更强的情形：当不同记录类的 Gram 重叠统一严格小于一时，重复记录会使跨类相干按明确速率收缩；同一记录类内部的矩阵元则被保留下来，极限是块对角的记录类结构。

引用的冻结模块是 `RepeatedRecordExponentialDecay.lean` 的 `repeated_record_exponential_decay`，以及 `CoherenceDecay.lean` 的 `equal_superposition_coherence_tendsto_zero`。本节只解释这些有限矩阵结论，不新增 Lean 声明，也不把指数收缩推广到未满足 Gram 假设的任意开放系统。

<a id="entry-232"></a>

### 64.1 记录 Gram 系数与重复通道

设有限系统标签为 $i\in\operatorname{Fin}(d)$，每个标签对应一个归一化环境记录向量

$$
r_i=\bigl(r_{i,a}\bigr)_{a\in\operatorname{Fin}(e)},
$$

满足

$$
\sum_a|r_{i,a}|^2=1.
$$

定义记录 Gram 系数

$$
G_{ij}=\langle r_j,r_i\rangle.
$$

一次记录通道逐项作用于系统矩阵：

$$
\mathcal C(\rho)_{ij}=G_{ij}\rho_{ij}.
$$

重复 $N$ 次后，冻结定理给出精确式

$$
\bigl(\mathcal C^N(\rho)\bigr)_{ij}
=G_{ij}^{,N}\rho_{ij}.
$$

当 $i=j$ 时，归一化保证

$$
G_{ii}=1.
$$

因此对角概率不受这一记录通道改变；变化集中在非对角关系方向。

<a id="entry-233"></a>

### 定理 64.1（跨记录类的指数收缩）

假设存在

$$
q\in[0,1)
$$

使得只要 $r_i\ne r_j$，就有

$$
|G_{ij}|\le q.
$$

对每个记录值 $\lambda$ 定义记录类投影 $P_\lambda$，并令 pinching 映射为

$$
\Pi(\rho)
=\sum_{\lambda}P_\lambda\rho P_\lambda.
$$

`repeated_record_exponential_decay` 同时证明三件事：

$$
\bigl(\mathcal C^N(\rho)\bigr)_{ij}
=G_{ij}^{,N}\rho_{ij},
$$

$$
\Pi(\rho)_{ij}
=
\begin{cases}
\rho_{ij},&r_i=r_j,\\
0,&r_i\ne r_j,
\end{cases}
$$

以及 Frobenius 范数界

$$
\left\|
\mathcal C^N(\rho)-\Pi(\rho)
\right\|_F
\le
q^N
\left\|
\rho-\Pi(\rho)
\right\|_F.
$$

所以极限保留的是每个记录类内部的矩阵块，而跨类相干以 $q^N$ 收缩。若记录向量两两正交，则 $q=0$，一次作用就完成跨类 pinching；若只知道 $|G_{ij}|<1$ 但没有统一有限维上界，仍需另行建立统一 $q$ 才能使用上述范数界。

<a id="entry-234"></a>

### 64.2 “经典化”是块结构，不一定是完全对角化

若每个标签都有不同记录向量，记录类都是单点，$Pi(\rho)$ 是对角矩阵，此时

$$
\mathcal C^N(\rho)\longrightarrow\operatorname{diag}(\rho).
$$

但若存在 $i\ne j$ 满足

$$
r_i=r_j,
$$

则 $i,j$ 位于同一记录类，$\Pi(\rho)_{ij}=\rho_{ij}$。这些类内相干不会由该通道衰减。于是“固定点是经典的”只有在记录类全为单点时才意味着对角经典代数；一般极限是记录类块代数。

这与第 55 节的相位反例相容：若条件记录只相差一个相位，物理记录射线可能相同，跨类收缩条件并不成立；不能用固定点的形式描述替代 Gram 模长的严格假设。

`CoherenceDecay` 的 qubit 特例给出同一逻辑的极限版本：若相位阻尼系数 $c$ 满足

$$
0\le c<1,
$$

则等权叠加态的非对角矩阵元满足

$$
\bigl(\mathcal C^N(\rho)\bigr)_{01}
=\frac12c^N
\longrightarrow0.
$$

这里的严格不等式 $c<1$ 是收敛所需的条件；若 $|c|=1$，只能得到相位旋转或周期行为，不能推出衰减。

<a id="entry-235"></a>

### 64.3 与 Zeckendorf 合法构型的接口

在合法窗口

$$
\mathcal W_L
=\{w\in\{0,1\}^L:w_rw_{r+1}=0\}
$$

上，可以选择一个记录映射

$$
r:\mathcal W_L\longrightarrow\mathcal R.
$$

映射的纤维

$$
[w]_r=\{v\in\mathcal W_L:r(v)=r(w)\}
$$

决定极限块的边界。Zeckendorf 数值、激发数和局部模式都可以作为 $r$ 的候选，但它们的 Gram 重叠并不由编码本身决定。

若 $r$ 把所有合法构型分开，并且记录向量满足统一 $q<1$，则

$$
\|\mathcal C^N(\rho)-\operatorname{diag}(\rho)\|_F
\le
q^N\|\rho-\operatorname{diag}(\rho)\|_F.
$$

若 $r$ 只记录 Zeckendorf 数值的某个粗粒化，例如多个来源历史共享同一数值，则极限保留这些历史对应的块内相干；要进一步把块内结构当作经典噪声，必须增加记录 effect 或引入另一个会区分块内方向的动力学。

这给出一个比“编码有唯一表示”更严格的判据：唯一表示只说明离散标签层的规范性；经典化速度还需要记录 Gram 模长的统一谱隙

$$
1-q>0.
$$

<a id="entry-236"></a>

### 64.4 作用量、误差与停止条件

指数界可转写为达到目标 Frobenius 误差 $\varepsilon$ 的充分步数：若初始跨类残差满足

$$
\|\rho-\Pi(\rho)\|_F\le M,
$$

则只要

$$
q^N M\le\varepsilon,
$$

就有

$$
\|\mathcal C^N(\rho)-\Pi(\rho)\|_F\le\varepsilon.
$$

当 $0<q<1$ 且 $M>0$ 时，一个充分的整数条件是

$$
N\ge
\left\lceil
\frac{\log(M/\varepsilon)}{-\log q}
\right\rceil.
$$

这个 $N$ 只控制跨记录类的 Frobenius 范数尾项；它不自动控制第 56 节隐藏回流、第 58 节 Zeckendorf 刻度误差、第 61 节观察残差或第 63 节访问受限的恢复误差。完整任务预算仍需把这些项按各自适用的距离和通道假设合并。

因此，本节得到的“稳定经典现实”是一个带条件的操作性结论：在记录类固定、Gram 跨类重叠统一小于一、重复通道确实按同一有限模型作用的范围内，跨类相干以指数速度进入块对角结构；块内是否继续保留历史，则由更细的记录和后续动力学决定。

本节为 `repo-derived/open` 理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

<a id="entry-237"></a>

## 追加锚（新终端）

<a id="section-65"></a>

## 65. 多上下文读出的独立预算下界

第 61 节给出了单一观察族的可见容量守恒，第 62 节给出了顺序观测的有限稳定深度。本节问一个不同的问题：如果把读出分成多个上下文，每个上下文内部有一组归一化 outcome，那么为了让联合读出区分所有密度态，最少需要保留多少独立 outcome？

冻结模块 `D5/S3/Quantum/PredictionDepth/MultiContextBudgetLowerBound.lean` 中的 `multi_context_budget_lower_bound` 给出一个一般下界。它只使用有限维 traceless-Hermitian 载体和 informational completeness 假设；本节的 Zeckendorf 解释是接口层推导，不是该 Lean 定理的额外前提。

<a id="entry-239"></a>

### 65.1 上下文、归一化与独立 outcome

令系统 Hilbert 空间维数为

$$
d\in\mathbb N,
$$

每个上下文属于有限集合

$$
X\in\mathcal X.
$$

上下文 $x$ 有 $m_x+1$ 个 outcome effect，记为

$$
E_{x,0},E_{x,1},\ldots,E_{x,m_x}.
$$

归一化条件是 centered effect 的和为零：

$$
\sum_{j=0}^{m_x}E_{x,j}=0.
$$

因此最后一个 outcome 由前 $m_x$ 个决定：

$$
E_{x,m_x}
=-\sum_{j=0}^{m_x-1}E_{x,j}.
$$

真正计入预算的是每个上下文的独立数量 $m_x$，而不是把归一化约束后的全部 outcome 数量重复相加。

<a id="entry-240"></a>

### 定理 65.1（多上下文 informational completeness 下界）

若联合读出对密度态是单射，即

$$
\rho\ne\sigma
\Longrightarrow
\exists x,j,
\quad
\operatorname{Tr}(\rho E_{x,j})
e
\operatorname{Tr}(\sigma E_{x,j}),
$$

则冻结定理 `multi_context_budget_lower_bound` 证明

$$
\boxed{
 d^2-1
\le
\sum_{x\in\mathcal X}m_x.
}
$$

证明的线性核心是：所有上下文 outcome 的 span 必须覆盖完整的 traceless-Hermitian 载体，其实维数为

$$
\dim_{\mathbb R}\operatorname{Herm}_0(d)=d^2-1.
$$

每个上下文删去一个由归一化关系决定的 outcome 后，剩余独立 outcome 总数为

$$
\sum_xm_x.
$$

一个有限 spanning family 的基数不可能小于载体维数，于是得到下界。该结论不要求上下文彼此正交，也不要求它们来自同一个物理装置；只要求联合读出确实 informationally complete。

<a id="entry-241"></a>

### 65.2 对 qubit 与受约束构型的含义

当 $d=2$ 时，

$$
d^2-1=3.
$$

因此，任何 informationally complete 的多上下文 qubit 读出至少需要三项独立的 traceless 方向。把它们写成三个 Pauli 方向只是一个常见实现；下界本身不依赖具体坐标选择。

对 Zeckendorf 合法窗口

$$
\mathcal W_L
=\{w\in\{0,1\}^L:w_rw_{r+1}=0\},
$$

可以把构型集合分成上下文

$$
\mathcal W_L=\bigsqcup_{x\in\mathcal X}\mathcal W_{L,x},
$$

并为每个上下文指定一组 effect。合法构型数量

$$
|\mathcal W_L|=F_{L+2}
$$

本身不是 informational completeness 的预算；它只告诉我们有多少离散基底候选。要判断这些候选是否真的提供独立读出，必须计算对应 effect 的 span，并检查是否覆盖任务所需的 traceless 方向。

因此，增加 Zeckendorf 窗口长度可能增加标签，却不一定满足

$$
\sum_xm_x\ge d^2-1.
$$

反过来，较短窗口若配备线性独立的多个上下文，也可能达到指定有限维载体的完备性。编码容量和观测容量是两笔不同的账。

<a id="entry-242"></a>

### 65.3 与观察精炼和顺序深度的关系

第 61 节中的容量守恒对单个 effect span 给出

$$
C+Q=d^2-1.
$$

本节给出的多上下文下界则说明，若目标是把残差降到零，跨上下文累积的独立方向至少要填满同一个 $d^2-1$ 维 traceless 载体。第 62 节的顺序词可以提供这些方向，但每一个顺序词是否增加新维数仍要由 effect span 检验；重复一个已在 span 内的词不会增加预算。

若只要求某个目标 observable $A$ 的预测，而不是完整 informational completeness，则不必支付整个 $d^2-1$ 的预算。只要

$$
A\in\mathcal V_{\mathrm{task}},
$$

目标就由任务可见空间决定；这正是第 59 节 `TargetPredictionSufficiency` 的边界。因而本下界是完整 tomography 的必要条件，不是所有预测任务的普遍最小成本。

<a id="entry-243"></a>

### 65.4 上下文预算与历史保留

把“历史保留多少”改写成上下文预算时，需要区分三层：

$$
\begin{aligned}
&\text{离散层：保留哪些 Zeckendorf 合法构型；}\\
&\text{上下文层：允许哪些读出方式和操作顺序；}\\
&\text{线性层：这些读出在 traceless 载体中提供多少独立方向。}
\end{aligned}
$$

若联合读出不是 informationally complete，剩余方向仍可能在第 57 节的未来动力学或第 63 节的完整记录访问中重新出现；不能仅因当前上下文预算不足就宣称这些方向不存在。若联合读出达到完整性，则在该有限维、指定 effect 模型内，当前密度态被唯一确定，但这仍不等于所有环境历史或所有不相容未来实验都已被编码。

所以一个可检验的预算流程是：先列出上下文及其 outcome 归一化关系，再计算独立 outcome 总数和 effect span，最后根据任务是完整 tomography 还是目标预测选择下界。Zeckendorf 只提供合法构型组织，不替代这三步线性核验。

本节为 `repo-derived/open` 理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

<a id="entry-244"></a>

## 追加锚（新终端）

<a id="section-66"></a>

## 66. 信息完备读出的有限证书

第 65 节给出了多上下文完整读出的独立预算下界，但下界本身没有说明一个已经完备的无限或任意索引 effect 家族能否压缩成有限清单。本节使用 `FiniteInformationalEffectCertificate.lean` 的 `finite_informational_effect_certificate`，把这个压缩问题写成有限证书。

本节仍限定在有限维 Hermitian 算子和密度态读出；“有限证书”表示存在一个有限子族，不表示任意实验都能自动找到该子族，也不把证书搜索过程当作物理动力学。正文为 `repo-derived/open`，没有新增 Lean 声明。

<a id="entry-246"></a>

### 定理 66.1（信息完备家族的有限子证书）

令系统维数为

$$
d\in\mathbb N,
$$

并给定任意索引集上的 effect 家族

$$
\{F_i:i\in I\},
$$

其中每个 $F_i$ 是合法 effect。假设原始读出对密度态单射：

$$
\Bigl[
\forall i,
\quad
\operatorname{Tr}(\rho F_i)
=\operatorname{Tr}(\sigma F_i)
\Bigr]
\Longrightarrow
\rho=\sigma.
$$

冻结定理 `finite_informational_effect_certificate` 保证存在有限子集

$$
S\subseteq I
$$

满足

$$
|S|\le d^2-1,
$$

并且 centered effect 张成完整 trace-zero Hermitian 载体：

$$
\operatorname{span}_{\mathbb R}
\left\{
F_i-\frac{\operatorname{Tr}(F_i)}{d}I_d:i\in S
\right\}
=\operatorname{Herm}_0(d).
$$

同一个子族的原始概率读出仍然单射：

$$
\Bigl[
\forall i\in S,
\quad
\operatorname{Tr}(\rho F_i)
=\operatorname{Tr}(\sigma F_i)
\Bigr]
\Longrightarrow
\rho=\sigma.
$$

<a id="entry-247"></a>

### 66.2 为什么 centered 化不丢失密度态信息

对两个密度态，迹差为零：

$$
\operatorname{Tr}(\rho-\sigma)=0.
$$

因此对任意 effect $F$，有

$$
\operatorname{Tr}\left((\rho-\sigma)
\left(F-\frac{\operatorname{Tr}(F)}{d}I_d\right)\right)
=
\operatorname{Tr}\bigl((\rho-\sigma)F\bigr).
$$

单位方向在状态差上没有贡献，centered effect 保留了区分密度态所需的全部线性信息。定理先把原始完备性转成 centered span 的完整性，再从有限维 span 中抽取至多 $d^2-1$ 个生成元；最后用上式把 centered 读数的单射性转回原始 effect 的单射性。

这说明“保留全部历史”并不等于“保留全部原始记录条目”。若任务只是区分有限维密度态，可以删除所有落在已有 centered span 中的冗余 effect，而不改变该任务的预测能力。

<a id="entry-248"></a>

### 66.3 与第 65 节预算下界的夹逼

第 65 节说明，任意完整的独立 outcome 家族必须满足

$$
\text{独立 outcome 总数}\ge d^2-1.
$$

本节说明，若已经存在一个信息完备 effect 家族，则总能找到一个规模不超过同一数量的有限子证书：

$$
\boxed{
\text{完整读出的最小规模}
\le d^2-1
\le\text{任意完整读出的独立预算}.
}
$$

当某个选出的子族恰好有 $d^2-1$ 个线性独立 centered effect 时，它同时达到维数下界。若原始 effect 含有额外归一化关系或重复方向，实际可用条目数可能更多，但多出的条目不增加 centered span。

这里的“最小规模”应理解为存在性夹逼：定理保证一个不超过 $d^2-1$ 的证书，但没有声称任意给定索引排序的前 $d^2-1$ 项就构成证书，也没有提供一个通用实验搜索算法。

<a id="entry-249"></a>

### 66.4 Zeckendorf 构型中的压缩准则

对合法窗口

$$
\mathcal W_L
=\{w\in\{0,1\}^L:w_rw_{r+1}=0\},
$$

若每个构型或历史来源产生一个 effect $F_w$，可以先计算 centered 家族

$$
\widetilde F_w
=F_w-\frac{\operatorname{Tr}(F_w)}{d}I_d.
$$

只有当某个新构型的 $\widetilde F_w$ 不在已有 span 中时，它才增加信息完备性证书的线性容量。Zeckendorf 的唯一规范表示保证离散标签没有字面重复，但不保证对应 effect 在线性上独立；相反，不同历史也可能产生相同 centered effect，从而在该任务中可被压缩为同一个读出方向。

因此，对 Zeckendorf 编码的一个可执行压缩检查是：

$$
\widetilde F_{w_1},\ldots,\widetilde F_{w_k}
$$

逐步加入时，记录每次 span 的维数增量，直到达到任务所需维数。完整 tomography 的终点是

$$
\dim\operatorname{span}\{\widetilde F_w\}=d^2-1;
$$

目标预测的终点则只需包含目标 observable 所在的子空间。这个判据比按构型数或 Fibonacci 维数直接估计信息量更严格。

<a id="entry-250"></a>

### 66.5 与历史保留问题的边界

有限证书只保证当前指定密度态读出的完备性。它不保证：

$$
\begin{aligned}
&\text{环境记录已经被保留；}\\
&\text{所有未来 Heisenberg 迭代都在该子族 span 内；}\\
&\text{不相容测量可以同时赋予一份经典答案表；}\\
&\text{第 63 节中约化不可见的联合相干已经可恢复。}
\end{aligned}
$$

若后续动力学把目标带入新的 effect 方向，需要回到第 57、62 节扩张预测空间；若记录通道保留了同一块内相干，需要回到第 63、64 节分析访问范围和 Gram 收缩。有限证书因此是任务索引的：它压缩一个已声明读出任务的冗余，而不是宣布所有历史都已被安全删除。

本节为 `repo-derived/open` 理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

<a id="entry-251"></a>

## 追加锚（新终端）


<a id="section-67"></a>

## 67. 有限读出的条件数、稳定重建与噪声预算

第 66 节的有限证书回答哪些读出足以唯一确定指定有限维密度态读出任务中的每个状态。本节再问：读数有误差、耦合的标定也有误差时，这种唯一性是否仍能支持稳定预测？本节把帧下界、最小二乘误差与标定扰动接到同一预算中。新增连接为 `repo-derived/open` 理论推导，不增加 Lean 声明或冻结状态。

<a id="entry-253"></a>

### 67.1 读出方向的数目与最弱可见方向

取 $d>1$，令实内积空间

$$
\mathsf H_0=\operatorname{Herm}_0(d)
$$

由无迹 Hermitian 矩阵组成，使用 Hilbert–Schmidt 内积与范数。给定有限指标集 $I$、权重 $w_i\ge0$ 和 Hermitian 读出方向 $E_i$，定义

$$
A:\mathsf H_0\longrightarrow\mathbb R^I,
\qquad
A(D)_i=\sqrt{w_i}\,\langle D,E_i\rangle_{\mathrm{HS}}.
$$

这里的 $E_i$ 首先是线性读出方向。只有另行满足 $0\le E_i\le I$、适当归一化以及物理测量实现条件时，才能赋予其概率 effect 的解释。若 $D=\rho-\rho_\ast$，$A(D)$ 表示扣除已知参考读数后的加权差值，而非未经中心化的一份概率分布。

令 $G=A^\ast A$，并记

$$
\alpha=\lambda_{\min}(G),
\qquad
\beta=\lambda_{\max}(G).
$$

源码 `D5/S3/Observer/Linear/RobustFrameBounds.lean` 的 `robust_observer_frame_bounds` 给出这一载体上的谱帧界及单射性条件：

$$
\alpha\|D\|_{\mathrm{HS}}^2
\le\|A(D)\|_2^2
\le\beta\|D\|_{\mathrm{HS}}^2,
\qquad
A\text{ 单射}\iff\alpha>0.
$$

在 $\alpha>0$ 的范围，奇异值条件数为

$$
\kappa(A)=\sqrt{\frac{\beta}{\alpha}}.
$$

源码排除 $d=1$，因为这时无迹载体为零维，其构造没有最小特征值。源码使用 Lean 的总定义除法；$\alpha=0$ 时写出的形式商不能解释为通常数值分析中有限的可逆条件数。本节所有可逆条件数与除以 $\sqrt\alpha$ 的公式都明确要求 $\alpha>0$。

同一个有限维读出一旦单射就有正的 $\alpha$；但对一族不同读出而言，单射性不提供共同的正下界。稳定预算需要的是

$$
\alpha\ge\alpha_0>0,
$$

并且需要说明使用的坐标尺度、权重和噪声范数。

<a id="entry-254"></a>

### 67.2 完备读出可以任意病态

**命题 67.1（线性完备不提供统一抗噪裕量）。** 在二维实内积载体上，取 $\varepsilon>0$ 和

$$
A_\varepsilon=
\begin{pmatrix}
1&0\\
1&\varepsilon
\end{pmatrix}.
$$

每个 $A_\varepsilon$ 都单射，但其 Gram 特征值为

$$
\lambda_\pm(\varepsilon)
=\frac{2+\varepsilon^2\pm\sqrt{4+\varepsilon^4}}{2},
$$

且 $\lambda_-(\varepsilon)\to0$、$\kappa(A_\varepsilon)\to\infty$ 当 $\varepsilon\to0^+$。不存在对这整个族统一有效的正下帧界。

证明。行列式为 $\varepsilon$，故单射；直接计算

$$
A_\varepsilon^\ast A_\varepsilon
=\begin{pmatrix}2&\varepsilon\\\varepsilon&\varepsilon^2\end{pmatrix},
$$

其特征多项式为 $\lambda^2-(2+\varepsilon^2)\lambda+\varepsilon^2$，得到所列特征值。为避免把两个接近数相减，用等价形式

$$
\lambda_-(\varepsilon)
=\frac{2\varepsilon^2}
{2+\varepsilon^2+\sqrt{4+\varepsilon^4}}.
$$

于是 $\lambda_-/\varepsilon^2\to1/2$、$\lambda_+\to2$，推出结论。更直接地，对真实向量零施加观测噪声 $(0,\nu)$，精确求解得到重建向量 $(0,\nu/\varepsilon)$；其误差为 $|\nu|/\varepsilon$。证毕。

这是一般线性读出的反例，也可以作用在 qubit 无迹空间中任意指定的二维子空间上；它本身不是一个完整 qubit POVM。两项读出接近同一方向，虽然仍线性独立，却不能稳定地区分垂直于该方向的差异。

条件数和绝对灵敏度还必须分别记账。若 $s>0$，把 $A$ 换成 $sA$，则

$$
\alpha\longmapsto s^2\alpha,
\qquad
\beta\longmapsto s^2\beta,
\qquad
\kappa(sA)=\kappa(A).
$$

同一绝对读数噪声下，重建放大因子却变成 $1/(s\sqrt\alpha)$。若只是改写单位，噪声也须同步乘以 $s$，物理预算不因此改善；若真的改变耦合，则必须重新标定噪声，不能仅凭形式缩放声称获取了更多信息。

<a id="entry-255"></a>

### 67.3 最小二乘中的噪声如何进入重建

**命题 67.2（有参考读数的重建预算）。** 设 $A$ 满足下帧界 $\alpha>0$，数据模型为

$$
b=A(D)+\xi,
$$

且重建 $\widehat D$ 满足正规方程

$$
A^\ast(A\widehat D-b)=0.
$$

则

$$
\boxed{
\|\widehat D-D\|_{\mathrm{HS}}
\le\frac{\|\xi\|_2}{\sqrt\alpha}.
}
$$

证明。令 $e=\widehat D-D$。正规方程给出 $A^\ast(Ae-\xi)=0$，从而

$$
\|Ae\|_2^2=\langle Ae,\xi\rangle
\le\|Ae\|_2\|\xi\|_2.
$$

若 $Ae=0$，下帧界推出 $e=0$；否则约去 $\|Ae\|_2$。两种情形均有 $\sqrt\alpha\|e\|_{\mathrm{HS}}\le\|\xi\|_2$。这一推导的抽象有限维内积空间版本由 `D5/S3/Observer/Linear/LeastSquaresReconstructionNoiseBound.lean` 的 `least_squares_reconstruction_noise_bound` 承担。证毕。

这个命题不自行给出 $\xi$ 的统计分布或有限采样置信度。若采样、刻度近似和其他建模误差已在同一个加权数据范数中分别有界，才能用三角不等式合并。第 58 节的黄金刻度误差只有经过该节要求的响应正则性或另行证明的范数转换，才能作为这里的输入噪声界。

<a id="entry-256"></a>

### 67.4 耦合标定误差与噪声共用一个预算

**定理 67.3（扰动读出的稳定裕量）。** 设 $A$ 满足帧界 $0<\alpha\le\beta$，实际用于重建的标定映射为

$$
\widehat A=A+\Delta,
\qquad
\|\Delta\|_{\mathrm{op}}\le\eta<\sqrt\alpha.
$$

则对全部 $D\in\mathsf H_0$，

$$
(\sqrt\alpha-\eta)\|D\|_{\mathrm{HS}}
\le\|\widehat A D\|_2
\le(\sqrt\beta+\eta)\|D\|_{\mathrm{HS}}.
$$

所以 $\widehat A$ 单射，且

$$
\kappa(\widehat A)
\le\frac{\sqrt\beta+\eta}{\sqrt\alpha-\eta}.
$$

若真实数据仍为 $b=AD+\xi$，而 $\widehat D$ 满足

$$
\widehat A^\ast(\widehat A\widehat D-b)=0,
$$

则

$$
\boxed{
\|\widehat D-D\|_{\mathrm{HS}}
\le
\frac{\|\xi\|_2+\eta\|D\|_{\mathrm{HS}}}
{\sqrt\alpha-\eta}.
}
$$

证明。上下界分别来自反三角不等式和三角不等式：$\|AD\|-\|\Delta D\|\le\|\widehat AD\|\le\|AD\|+\|\Delta D\|$。正的下界保证单射，极端奇异值之比给出条件数估计。再把数据改写为

$$
b=\widehat A D+(\xi-\Delta D).
$$

以 $\widehat A$ 的下帧界 $(\sqrt\alpha-\eta)^2$ 应用命题 67.2，并用 $\|\xi-\Delta D\|_2\le\|\xi\|_2+\eta\|D\|_{\mathrm{HS}}$，即得结论。证毕。

这里 $A$ 是数据真实遵循的读出，$\widehat A$ 是重建采用的标定模型；两者的角色不能在误差公式中静默互换。严格条件 $\eta<\sqrt\alpha$ 也有内容：在最弱奇异方向上，大小恰为 $\sqrt\alpha$ 的扰动就能把该方向完全消掉。

若真实状态为密度矩阵，选择参考 $\rho_\ast=I/d$，则

$$
D=\rho-I/d,
\qquad
\|D\|_{\mathrm{HS}}^2
=\operatorname{Tr}(\rho^2)-\frac1d
\le1-\frac1d.
$$

在参考读数的误差也已计入 $\xi$ 的条件下，$\|\xi\|_2\le\nu$ 给出统一预算

$$
\boxed{
\|\widehat D-D\|_{\mathrm{HS}}
\le
\frac{\nu+\eta\sqrt{1-1/d}}{\sqrt\alpha-\eta}.
}
$$

这是有限维、指定读出、确定性范数误差下的结论；$\nu$ 和 $\eta$ 必须由实际采样与标定程序提供。

<a id="entry-257"></a>

### 67.5 从线性重建到合法状态与可见预测

无约束最小二乘只保证 $\rho_{\mathrm{raw}}=I/d+\widehat D$ 是迹为一的 Hermitian 矩阵，不保证正半定。可在 Hilbert–Schmidt 距离下把它投影到密度矩阵的闭凸集，得到 $\widehat\rho$。这一步与求解正规方程是两个不同操作。

**命题 67.4（凸投影与后续概率的误差）。** 设 $\rho$ 是真实密度矩阵，$\widehat\rho$ 是上述 Hilbert–Schmidt 最近点投影。若 $\|\rho_{\mathrm{raw}}-\rho\|_{\mathrm{HS}}\le r$，则

$$
\|\widehat\rho-\rho\|_{\mathrm{HS}}\le r.
$$

若此后施加同一个量子通道 $\Phi$ 和同一个有限 POVM，输出分布分别为 $p,\widehat p$，则

$$
\boxed{
\operatorname{TV}(p,\widehat p)
\le\frac12\|\Phi(\widehat\rho)-\Phi(\rho)\|_1
\le\frac12\|\widehat\rho-\rho\|_1
\le\frac{\sqrt d}{2}\,r.
}
$$

证明。记 $u=\rho_{\mathrm{raw}}$、$v=\widehat\rho$。闭凸集的最近点条件给出 $\langle u-v,\rho-v\rangle_{\mathrm{HS}}\le0$。展开 $\|u-\rho\|_{\mathrm{HS}}^2$，得到它不小于 $\|v-\rho\|_{\mathrm{HS}}^2$。后续测量和通道的迹距离收缩分别给出前两条不等式；最后一条是对至多 $d$ 个奇异值应用 Cauchy–Schwarz。证毕。

投影后的 $\widehat\rho-I/d$ 不必满足原正规方程；误差不增来自凸几何。上述后续通道必须是作用于该状态的同一个已指定通道。若真正后续还依赖未纳入状态的旧环境记录，就不能直接套用；应先扩大联合状态，或另计历史回流误差。

<a id="entry-258"></a>

### 67.6 这给历史保留问题增加了哪一个约束

Zeckendorf 合法窗口确定候选构型载体，实际耦合与读出标定确定 $E_i$；权重还包含统计加权等分析选择。两者共同确定最弱可见方向及 $\alpha$。对基底作纯标签重排会给出等距的坐标变换，奇异值不变；把 Fibonacci 数值直接改当物理耦合强度，则是在改变 $A$，必须重新计算谱界。

有限证书解决的是“保留的读出是否足够”；$\alpha$ 解决的是“这些读出是否足够敏感”；$\eta$ 和 $\nu$ 解决的是“标定及采样是否准确到可以使用这种敏感度”。在完整状态重建的任务中，给定重建误差容限 $r_\ast$，一个充分条件为

$$
\eta<\sqrt\alpha,
\qquad
\nu+\eta\sqrt{1-1/d}
\le r_\ast(\sqrt\alpha-\eta).
$$

稳定预测还需后续演化对所选状态描述闭合，或者另有已校准的回流误差界。若只预测少数目标读数，则不必要求完整状态重建，所需的稳定常数应只针对那些目标；完整 tomography 的最弱方向不能自动成为所有任务的成本下界。

本节的谱帧界与最小二乘基础按上述两份项目源码定位；扰动、凸投影及任务解释属于本节的有限维连接推导。所用线性代数、最小二乘和迹距离收缩为标准数学结构，`repo-derived` 表示本卷中的组合与适用域，不声称发明这些结构。本节没有从编码推导物理耦合、采样置信度、唯一测量结果或宇宙的经典性，也没有新增 Lean 形式化或覆盖。

<a id="entry-259"></a>

## 追加锚（新终端）

<a id="section-68"></a>

## 68. 适用域校准与读出约束

第 61–66 节的有限维结论可以继续使用，但需要把矩阵记号、读出类型和任务范围校准到源码实际证明的假设。本节只修正适用域，不新增 Lean 声明；正文状态为 `repo-derived/open`。

<a id="entry-261"></a>

### 68.1 受控复制的恢复必须是左右共轭

第 63.1 节原先写成

$$
U_{\mathrm{copy}}^{\dagger}J(\rho)=B(\rho).
$$

这条写法应撤回。源码 `D5/S3/Quantum/Decoherence/ReducedRecordAccessDefect.lean` 的 `unitaryEvolution` 是左右乘法；定理 `reduced_irreversibility_is_access_defect` 的恢复分支实际断言

$$
\operatorname{unitaryEvolution}
\bigl(U_{\mathrm{copy}}^{\dagger},J(\rho)\bigr)
=B(\rho),
$$

亦即

$$
\boxed{
U_{\mathrm{copy}}^{\dagger}J(\rho)U_{\mathrm{copy}}=B(\rho)
}.
$$

对 $\sigma$ 同样有

$$
U_{\mathrm{copy}}^{\dagger}J(\sigma)U_{\mathrm{copy}}=B(\sigma).
$$

保留的结论是：包括记录自由度的受控复制仍由显式幺正控制，访问联合记录并施加逆耦合可以恢复；只访问偏迹后的系统矩阵，则不能由同一个函数恢复两个不同联合矩阵。这里的左右共轭是矩阵演化的必要部分，不能删去。

<a id="entry-262"></a>

### 68.2 正权重改变的是度量尺度，不自动改变观察商

第 61.5 节原先说“改变 effect 集合或权重，则半范数、商空间和容量账本都会改变”。其中关于权重的部分需要撤回并加条件。

在固定 centered effect 家族、且所有权重仍满足

$$
\forall i,\qquad w_i>0,
$$

时，`D5/S3/Quantum/Measurement/OperationalObservationKernel.lean` 中的 私有引理 `operational_seminorm_kernel` 表明

$$
\ker\|D\|_{\mathrm{obs}}
=
\operatorname{span}_{\mathbb R}\{E_i\}^{\perp}
$$

与正权重的具体数值无关。加权读出只是对每个坐标乘以非零因子 $\sqrt{w_i}$；因此状态的零距离关系、`OperationalStateQuotient` 的商以及由 effect span 定义的

$$
C(E)=\dim\operatorname{span}(\{I\}\cup E)-1,
\qquad
Q(E)=\dim\operatorname{span}(\{I\}\cup E)^{\perp}
$$

保持不变。`ObserverCapacityConservation.lean` 的 `observer_capacity_conservation` 没有权重参数，正是这一点的源码边界。

应保留的校准说法是：改变严格正权重通常改变半范数和距离的数值尺度；改变 effect 集合可能改变 kernel、商和容量。若允许某些权重降为零，kernel 与商应对有效家族

$$
E_{\mathrm{eff}}=\{E_i:w_i>0\}
$$

重新计算；此时由有效家族定义的容量才可能改变，而把全部未加权 effect 仍计入 $C(E),Q(E)$ 的名义账本则不会自动改变。若权重不再严格为正，`operational_observation_kernel_and_metric` 的正权重假设不再适用。

<a id="entry-263"></a>

### 68.3 多上下文预算使用的是 centered 方向

第 65.1 节中单射条件的显示式有一个排版错误：理论正文中的孤立字符 `e` 应改为数学关系符号 $\ne$。

$$
\rho\ne\sigma
\Longrightarrow
\exists x,j,
\quad
\operatorname{Tr}(\rho E_{x,j})
\ne
\operatorname{Tr}(\sigma E_{x,j}).
$$

此外，第 65 节不能把源码中的 `effect` 自动称为物理 POVM outcome。`multi_context_budget_lower_bound` 的参数类型是

$$
\operatorname{effect}(x,j):\operatorname{traceZeroHermitian}(d),
$$

并且只假设

$$
\sum_j\operatorname{effect}(x,j)=0.
$$

这表达的是 centered effect 方向的线性归一化关系；源码没有为这些项加入正半定性、$0\le E\le I$ 或原始 POVM 的

$$
\sum_jE_{x,j}=I
$$

条件。因此需撤回“这些项本身就是概率 outcome”的表述。

若从合法 POVM $(E_{x,j})_j$ 出发，应先定义

$$
\widetilde E_{x,j}
=E_{x,j}-\frac{\operatorname{Tr}(E_{x,j})}{d}I_d.
$$

原 POVM 的归一化会给出

$$
\sum_j\widetilde E_{x,j}=0,
$$

而状态差上的读数满足

$$
\operatorname{Tr}\bigl((\rho-\sigma)\widetilde E_{x,j}\bigr)
=
\operatorname{Tr}\bigl((\rho-\sigma)E_{x,j}\bigr).
$$

所以第 65.1 节的下界应保留为 centered 线性读出预算：

$$
d^2-1\le\sum_xm_x,
$$

其中 $m_x$ 是每个上下文删去一个由零和关系决定的项后，剩余 centered 方向的项数。源码虽把参数命名为 `independentCount`，却未假设这些剩余方向线性独立；它们的 span 维数只保证不超过 $m_x$。要把它解释为物理概率测量，还必须另外提供原始 POVM 的正性和单位和条件。

<a id="entry-264"></a>

### 68.4 第 63 节的裸矩阵定理与密度态见证分开

`reduced_irreversibility_is_access_defect` 及其 canonical bridge 的输入是

$$
\rho,\sigma:\operatorname{QubitMatrix},
$$

源码假设只有对角元相等和某个非对角元不同；没有在该定理的参数中要求 Hermitian、正半定或迹为 $1$。因此第 63.1 节把任意参数直接称为“两个密度态”的说法应撤回，改为“两个 qubit 矩阵的线性见证”。

文件末尾的具体例子取 $\rho=|+\rangle\langle+|$、$\sigma=|-\rangle\langle-|$。从这两个归一化向量的外积可直接检验正性和迹为一；该 Lean `example` 的结论本身只记录对角相等及非对角不同。因此可以在上述合法性检验后保留如下物理实例：在这个例子中，偏迹相同、联合矩阵不同，并且联合逆耦合可恢复。一般的密度态版本需要显式加入

$$
\rho\succeq0,\quad \sigma\succeq0,
\qquad
\operatorname{Tr}\rho=\operatorname{Tr}\sigma=1,
$$

或直接引用该具体见证。

同样，第 63.3 节的恢复误差下界不是任意记录通道的定理。`FiniteRecordRecoveryError.lean` 的 `finite_record_recovery_error_lower_bound` 固定了有限支撑振幅 $c:\mathbb Z\to\mathbb C$、归一化、整数标签 $q$、非零位移 $q(i)-q(j)$，并对由 `FiniteShiftedRecordChannel` 构造的具体通道 $\Lambda$ 以及任意恢复通道 $R$ 给出

$$
\sup_{\tau}D\bigl(R\Lambda(\tau),\tau\bigr)
\ge
\frac{1-|\gamma(q(i)-q(j))|}{2}.
$$

因此应保留“该有限移位记录模型中的恢复下界”，撤回任何对任意记录通道、任意环境或普适物理恢复的外推。

<a id="entry-265"></a>

### 68.5 稳定深度的维数必须区分 identity 与 centered predictive space

第 62.3 节前面定义的 $\mathcal V_n$ 包含单位方向 $I$，而源码 `CenteredEffectStabilityDepthBound.lean` 的 `towerSpace` 与 `predictiveSpace` 都位于 trace-zero Hermitian 载体。源码定理 `centered_effect_stability_depth_bound` 的精确上界是

$$
\operatorname{sd}(H,E)
\le
\dim\mathcal P_{\infty}-\dim\mathcal T_0,
$$

其中

$$
\mathcal P_{\infty}=\operatorname{predictiveSpace}(H,E),
\qquad
\mathcal T_0=\operatorname{towerSpace}(H,E,0).
$$

它还给出

$$
\dim\mathcal P_{\infty}-\dim\mathcal T_0
\le
d^2-1-\dim\mathcal T_0.
$$

因此原先写成 $\dim(\mathcal V_{\infty})-\dim(\mathcal T_0)$ 的公式应撤回，除非明确重新定义 $\mathcal V_{\infty}$ 为 centered predictive space。若保留第 62.1 节含单位的全 Hermitian 观察塔，在另行假定单位方向被单列且动力学保持相应 trace-zero 子空间时，可写

$$
\mathcal V_{\infty}=\mathbb RI\oplus\mathcal P_{\infty};
$$

此时单位方向不计入 trace-zero 稳定深度。保留的结论是：固定有限维载体和固定线性 Heisenberg 作用下，某一步 tower 稳定后以后永久稳定，并存在有限深度证书。

<a id="entry-266"></a>

### 68.6 有限 effect 证书分离全部密度态

第 66.5 节把有限证书说成“当前指定密度态读出的完备性”，范围过窄。`FiniteInformationalEffectCertificate.lean` 的 `finite_informational_effect_certificate` 假设的是整个映射

$$
\rho\longmapsto
\bigl(\operatorname{Tr}(\rho F_i)\bigr)_{i\in I}
$$

在全部 $\operatorname{DensityState}(\operatorname{Fin}d)$ 上 injective。它抽取有限 $S\subseteq I$，满足

$$
|S|\le d^2-1
$$

以及

$$
\operatorname{span}_{\mathbb R}
\left\{
F_i-\frac{\operatorname{Tr}(F_i)}{d}I_d:i\in S
\right\}
=\operatorname{Herm}_0(d),
$$

并且同一子族仍分离全部密度态：

$$
\left[
\forall i\in S,
\quad
\operatorname{Tr}(\rho F_i)=\operatorname{Tr}(\sigma F_i)
\right]
\Longrightarrow
\rho=\sigma.
$$

所以应把旧说法改为“指定有限维密度态读出任务的全体状态完备性”。它仍然是任务索引的：不保证环境记录已保留，不保证未来 Heisenberg 方向仍在该子族 span 内，也不保证约化不可见的联合相干可以恢复。

<a id="entry-267"></a>

### 68.7 校准后的使用规则

六项边界合并后，当前可安全使用的推理链是

$$
\begin{aligned}
&\text{centered effect span}
\longrightarrow
\text{当前读出商与残差},\\
&\text{trace-zero predictive tower}
\longrightarrow
\text{有限观察深度},\\
&\text{具体记录通道}
\longrightarrow
\text{具体相干衰减与恢复下界},\\
&\text{联合幺正}
\longrightarrow
\text{左右共轭的整体恢复}.
\end{aligned}
$$

因此，Zeckendorf 合法构型仍可作为离散索引和约束窗口；它不自动提供 POVM 正性、Hamiltonian、记录通道、全体未来完备性或环境恢复。所谓“保留多少历史”必须同时标明：使用的是哪一类 effect、是否已经 centered、动力学位于哪个 trace-zero 载体、记录通道的具体假设是什么，以及完备性是针对全部有限维密度态还是仅针对一个目标预测任务。

<a id="entry-268"></a>

## 追加锚（新终端）

<a id="section-69"></a>

## 69. 面向未来任务的稳定记录与最小噪声放大

第 67 节对全部状态方向给出重建预算。但“足以预测后续相互作用”并不总是完整 tomography：有些状态差异与指定后续实验无关。对这些任务，要求全部方向都有统一正下帧界，会把无需恢复的隐藏信息也计入成本。本节把精确可见性收紧为带噪声的任务判据；新增连接为 `repo-derived/open`，不新增 Lean 声明或冻结状态。

<a id="entry-270"></a>

### 69.1 当前读出与未来任务必须分别指定

令 $X,Y,Z$ 为有限维实 Hilbert 空间，当前读出为 $A:X\to Y$，未来任务为 $F:X\to Z$。它们都是线性映射。量子应用可取 $X=\operatorname{Herm}_0(d)$；任务的每个坐标是扣除已知参考后的未来期望值。若未来由已指定的通道 $\Phi$ 和读出方向 $E_j$ 构成，则

$$
F(D)_j=\operatorname{Tr}(E_j\Phi(D))
=\operatorname{Tr}(\Phi^\ast(E_j)D).
$$

因此，“未来”通过实际操作的 Heisenberg 拉回进入 $F$。如果选择多个互不相容的实验，$F(D)$ 记录的是这些不同实验各自的统计响应，不是给单次系统同时指定所有实验的预存答案。

`D5/S3/Observer/VisibleDescent/TargetObservabilityFourWayEquivalence.lean` 的 `target_observability_four_way_equivalence` 给出标量目标的纤维常值、核包含与 adjoint 像等价；`D5/S3/Quantum/PredictionDepth/TargetPredictionSufficiency.lean` 的 `target_prediction_sufficiency` 给出密度态上的可见 span 条件及其失败见证。这些判据解决精确可见性，尚需为数据误差指定数值代价。

<a id="entry-271"></a>

### 69.2 任务稳定常数与一个可检验的算子不等式

**定理 69.1（任务读出的有限噪声放大判据）。** 对上述有限维线性映射，以下条件等价：

$$
\ker A\subseteq\ker F;
$$

$$
\exists L_0:\operatorname{ran}A\to Z\text{ 线性},
\qquad F=L_0A;
$$

$$
\exists c\ge0,\quad
\forall x\in X,\qquad\|Fx\|\le c\|Ax\|.
$$

第二式将 $A$ 的值视为 $\operatorname{ran}A$ 的元素，且 $L_0$ 唯一。把满足第三式的最小常数记为 $c_{\mathrm{task}}$，则

$$
\boxed{
 c_{\mathrm{task}}=\|L_0\|
 =\|FA^+\|_{\mathrm{op}}.
}
$$

这里 $A^+$ 是 Moore–Penrose 逆。$A=0,F=0$ 时约定 $c_{\mathrm{task}}=0$。核包含不成立时，记任务代价为 $+\infty$，不把零分母按总定义除法解释为零代价。对给定 $c\ge0$，上述范数不等式又等价于

$$
\boxed{
F^\ast F\preceq c^2A^\ast A,
}
$$

其中 $\preceq$ 表示自伴算子的二次型偏序。

证明。若核包含成立，定义 $L_0(Ax)=Fx$。相同读出的两个原像之差属于 $\ker A$，因此定义与代表无关；线性和唯一性随之成立。有限维使 $L_0$ 有有限算子范数，从而得到范数界。反之，把 $x\in\ker A$ 代入范数界立即得到 $Fx=0$。

由 Penrose 恒等式 $AA^+A=A$，有 $A(A^+Ax-x)=0$，核包含推出

$$
F=FA^+A.
$$

令 $P=AA^+$。Penrose 恒等式还给出 $P^2=P=P^\ast$、$\operatorname{ran}P=\operatorname{ran}A$，因此 $P$ 是到读出像空间的正交投影；由 $A^+AA^+=A^+$ 得 $A^+P=A^+$。于是

$$
FA^+=L_0P.
$$

$P$ 不扩张范数，且在像空间上为恒等，故 $\|FA^+\|=\|L_0\|$。所有可用 $c$ 的最小值正是该范数。最后，平方范数界等价于对全部 $x$ 有

$$
\langle x,(c^2A^\ast A-F^\ast F)x\rangle\ge0,
$$

即所列半正定条件。证毕。

`D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse.lean` 的 `isMoorePenroseInverse_moorePenroseInverse` 及 `comp_moorePenroseInverse_comp` 提供所用的有限维 Penrose 基础。这里的任务因子化、最小算子范数及半正定判据是本节组合推导，不称为该模块已有的同名结果。

<a id="entry-272"></a>

### 69.3 这个常数直接控制预测误差

**定理 69.2（任务预测与最坏有界噪声）。** 假设定理 69.1 的核包含成立，数据为 $b=Ax+\xi$，且 $\|\xi\|\le\nu$，$\nu\ge0$。定义预测

$$
\widehat f=FA^+b.
$$

则

$$
\boxed{
\|\widehat f-Fx\|\le c_{\mathrm{task}}\nu.
}
$$

对任意预测函数 $\Psi:Y\to Z$，定义确定性风险

$$
R_\nu(\Psi)
=\sup_{x\in X,\,\|\xi\|\le\nu}
\|\Psi(Ax+\xi)-Fx\|.
$$

在允许全部 $x\in X$ 和全部该范数球内噪声的线性问题中，

$$
\inf_{\Psi:Y\to Z}R_\nu(\Psi)=c_{\mathrm{task}}\nu.
$$

证明。因子化给出 $FA^+b-Fx=FA^+\xi$，得到上界。若 $c_{\mathrm{task}}\nu=0$，上界已经为零。否则，有限维单位球的紧性使像空间中存在单位向量 $y$，满足 $\|L_0y\|=c_{\mathrm{task}}$。取 $x_\ast$ 使 $Ax_\ast=\nu y$。输入 $x_\ast$ 配噪声 $-\nu y$，与输入 $-x_\ast$ 配噪声 $\nu y$，都产生 $b=0$。两者目标为 $\pm Fx_\ast$，相距 $2c_{\mathrm{task}}\nu$。任意同一预测值至少对其中一者误差不小于其半距。证毕。

这一最小最坏结论针对整个线性载体，不自动是受限密度态集合上的全局下界。若采用 $\rho_\pm=I/d\pm x_\ast$ 的物理见证，必须另外满足 $x_\ast$ Hermitian、无迹及

$$
\|x_\ast\|_{\mathrm{op}}\le1/d.
$$

即使这两个状态合法，所用噪声 $\pm\nu y$ 还必须符合允许的数据域与采样模型；若读数被解释为概率，须检验相应概率约束。因此不能仅凭状态合法就声称达到了物理实验的最小最坏下界。上界则对允许状态的任何子集继续成立。无论是否达到线性最坏下界，$c_{\mathrm{task}}$ 都是一个可计算的充分误差系数。

标量目标 $Fx=\langle f,x\rangle$ 还有直接的源码支点：`D5/S3/Observer/Conditioning/TargetVisibilityConditionCost.lean` 的 `target_visibility_condition_cost` 给出 $A^\ast a=f$ 的最小范数读出系数证书，并证明其二次条件成本。对这个 $a$，

$$
|\langle a,b\rangle-\langle f,x\rangle|
\le\|a\|\,\|\xi\|.
$$

系数范数描述绝对误差放大；称它为通常的无量纲“条件数”还需要另行指定输入输出归一化。

<a id="entry-273"></a>

### 69.4 丢掉某个方向是否可接受，取决于未来操作

**命题 69.3（同一记录对不同目标有不同成本）。** 取 $0<\varepsilon\le1$，在三维实坐标上定义

$$
A_\varepsilon(x,y,z)=(x,\varepsilon y,\varepsilon z).
$$

对目标 $F_x(x,y,z)=x$ 和 $F_y(x,y,z)=y$，分别有

$$
c_x=1,
\qquad
c_y=1/\varepsilon.
$$

当 $\varepsilon=0$ 时，$F_x$ 仍可精确预测，而 $F_y$ 的核包含条件失败。

证明。$A_\varepsilon$ 可逆时，两个目标的系数行分别为 $(1,0,0)$ 和 $(0,1/\varepsilon,0)$，其 Euclidean 范数就是定理 69.1 的代价。$\varepsilon=0$ 时 $(0,1,0)\in\ker A_0$，却不在 $\ker F_y$ 中；$F_x$ 则直接是当前第一项读数。证毕。

这个例子可以实现为三个不同 qubit 测量上下文。设 $(x,y,z)$ 为 Bloch 坐标，分别使用

$$
E_{k,\pm}=\frac{I\pm s_k\sigma_k}{2},
\qquad
(s_x,s_y,s_z)=(1,\varepsilon,\varepsilon).
$$

它们均满足正性与单位和条件；每个上下文的两个概率之差为 $s_k$ 乘以相应 Bloch 分量。按这三个差值组织数据，就得到 $A_\varepsilon$。这里使用 Euclidean Bloch 范数，与第 67 节的无迹 Hilbert–Schmidt 范数相差固定因子 $\sqrt2$；跨节转换时必须同步校准。三个上下文是在分别制备的同态样本上统计，不表示同时测得单个 qubit 的三个确定值。

若未来只再读 $X$，第一项已经够用。若允许一个满足 $U^\ast XU=Y$ 的校准幺正操作，随后同样读取 $X$，则未来目标变成当前的 $Y$ 分量；例如可取 $U=e^{i\pi Z/4}$。原来没有进入第一项记录的相位方向，现在进入可见预测。因此，扩大允许操作族会改变所需记录及其稳定成本。

<a id="entry-274"></a>

### 69.5 近似任务与历史尾项应在相同输出尺度上记账

精确核包含有时过强。对已指定的任务 $F$，可以选择当前读出可实现的近似任务 $F_0=L_0A$；令 $P$ 为到 $\operatorname{ran}A$ 的正交投影，取 $L=L_0P$。

**命题 69.4（近似闭合与数据噪声的任务预算）。** 若

$$
\|F-F_0\|_{\mathrm{op}}\le\delta,
\qquad
\|x\|\le M,
\qquad
b=Ax+\xi,\quad\|\xi\|\le\nu,
$$

则预测 $Lb$ 满足

$$
\boxed{
\|Lb-Fx\|\le\delta M+\|L\|\nu.
}
$$

若实际后续读数 $f_{\mathrm{actual}}$ 还满足 $\|f_{\mathrm{actual}}-Fx\|\le\mu$，则总误差不超过

$$
\delta M+\|L\|\nu+\mu.
$$

证明。恒等式 $LA=F_0$ 给出 $Lb-Fx=(F_0-F)x+L\xi$；分别应用算子范数界和三角不等式，再加上实际输出的偏差即可。证毕。

$\delta M$ 是任务不完全落在当前可见空间内的代价，$\|L\|\nu$ 是把读数噪声转换为预测误差的代价，$\mu$ 则容纳已单独证明的历史尾项或动力学失配。第 56、58 节的记忆尾界或刻度界，只有在转换成这里同一个任务输出范数后才能代入 $\mu$ 或 $\nu$。本式没有证明这些误差天然小，也没有赋予三个符号相互独立的概率意义。

<a id="entry-275"></a>

### 69.6 可预测对象的候选记录应怎样比较

给定未来任务 $F$、误差容限 $\epsilon_\ast$ 和候选记录 $A_J$，可以先用

$$
\ker A_J\subseteq\ker F
$$

筛出精确足够的记录，再用

$$
F^\ast F\preceq c_J^2A_J^\ast A_J,
\qquad
c_J\nu_J\le\epsilon_\ast
$$

检验其数值稳定性。若只要求近似足够，则使用命题 69.4 的三项预算。$\nu_J$ 必须随记录方案一同标定；单纯增加权重或重复同一项，并不在固定资源下自动减少误差。

因此，记录数、采样量、可访问环境范围、预测时间和误差容限共同约束可选方案。Zeckendorf 标签可以索引 $J$，但标签数量或整数差不能替代 $A_J$ 的线性作用与噪声标定。

相对于这组任务，能够被删除的是那些不影响目标，或只在容许预算内影响目标的关系；需要保留的是会进入未来响应、且必须被稳定读取的方向。这是“保留哪些历史”的有限维任务版本。它仍需物理记录稳定性、实际环境访问条件与后续闭合共同支持，不能单凭线性预测界宣称选出了唯一经典结果。

本节的精确可见性、最小范数标量证书及 Penrose 基础分别由所引项目模块定位；多输出任务范数、最坏有界噪声、物理上下文实例与近似任务预算为本节的连接推导。它们使用标准有限维线性代数和估计论结构，不主张文献新颖性；本节未新增 Lean 形式覆盖。

<a id="entry-276"></a>

## 追加锚（新终端）

<a id="section-70"></a>

## 70. 有限视界内的稳定记录、闭合缺陷与记忆容量

第 69 节把“当前记录能否预测指定目标”写成了任务级核包含和噪声常数。本节再加入记录通道的动力学条件：记录是否在每一步被重新建立，隐藏关联是否会回流，以及完全区分历史需要多大的内部记忆。新增组合为 `repo-derived/open` 理论；所引 Lean 模块是现有冻结结果，本节没有新增 Lean 声明。

<a id="entry-278"></a>

### 70.1 固定点、吸引子与记录闭合是三件事

设 $\mathcal E$ 是一个有限维量子记录通道，$\Phi$ 是下一步系统演化。若记录是完整正交 pinching，则已有 `FiniteRecordPinchingIdempotence.finite_record_pinching_idempotent` 给出

$$
\mathcal E^2=\mathcal E.
$$

因此 $\operatorname{im}\mathcal E$ 是重复记录后不再改变的子空间。这个事实只说明记录结构是幂等的，不说明任意态会趋近它。

在条件记录向量 $|r_i\rangle$ 的模型中，`EnvironmentMarginalChannel.environment_marginal_channel` 给出

$$
\mathcal E(\rho)_{ij}=R_{ij}\rho_{ij},
\qquad
R_{ij}=\langle r_j,r_i\rangle.
$$

`SingletonRecordClassicality.singleton_record_classicality` 在 $i\ne j$ 时只要求 $R_{ij}\ne1$，即可推出固定点中的相应非对角项为零。若进一步存在统一的

$$
|R_{ij}|\le q<1
$$

跨记录类界，`RepeatedRecordExponentialDecay.repeated_record_exponential_decay` 才给出到记录类 pinching 的收缩，例如

$$
\|\mathcal E^N(\rho)-\mathcal P(\rho)\|_F
\le
q^N\|\rho-\mathcal P(\rho)\|_F.
$$

所以应区分：

$$
\text{幂等固定结构}
\quad\ne\quad
\text{对它的吸引性}
\quad\ne\quad
\text{与下一步动力学的预测闭合}.
$$

当 $|R_{ij}|=1$ 而 $R_{ij}\ne1$ 时，非对角项可以只发生相位旋转；固定点可能是经典的，单次迭代却不收敛。这个边界不能用“已经发生记录”替代。

<a id="entry-279"></a>

### 70.2 逐步记录时的精确闭合缺陷

假设每一步都执行同一个记录通道。定义两个从当前完整状态到下一次记录的通道：

$$
A=\mathcal E\Phi,
\qquad
B=\mathcal E\Phi\mathcal E.
$$

$A$ 先让完整状态演化再记录；$B$ 先丢弃当前记录看不见的部分，再演化和记录。若存在记录层通道 $\overline\Phi:\operatorname{im}\mathcal E\to\operatorname{im}\mathcal E$ 使

$$
A=\overline\Phi\mathcal E,
$$

则当前记录是这一步的封闭状态描述。由于 $\mathcal E^2=\mathcal E$，这等价于

$$
\boxed{
\mathcal E\Phi=\mathcal E\Phi\mathcal E.
}
$$

如果只要求有限精度，定义

$$
\delta
=
\sup_{\rho\in\mathsf D}
D\!\left(\mathcal E\Phi(\rho),
\mathcal E\Phi\mathcal E(\rho)\right),
$$

其中 $\mathsf D$ 是指定密度态集合，$D$ 是迹距离。这里的 $\delta$ 衡量当前删去的部分在下一次记录中重新显现的最大幅度。

**命题 70.1（逐步记录的有限视界误差）。** 令 $A=\mathcal E\Phi$、$B=\mathcal E\Phi\mathcal E$，两者均为量子通道，并假设每一步都在记录之后继续演化。若

$$
\sup_{\rho\in\mathsf D}D(A\rho,B\rho)\le\delta,
$$

则对任意初态 $\rho$ 和整数 $n\ge1$，

$$
D(A^n\rho,B^n\rho)\le n\delta.
$$

证明。通道的迹距离收缩性给出

$$
D(A\sigma,A\tau)\le D(\sigma,\tau),
\qquad
D(B\sigma,B\tau)\le D(\sigma,\tau).
$$

插入望远镜分解

$$
A^n-B^n
=
\sum_{k=0}^{n-1}A^{n-1-k}(A-B)B^k
$$

的逐步态版本。第 $k$ 项的距离贡献不超过 $\delta$，已有贡献不会被后续通道放大，故归纳得到

$$
e_{n+1}\le e_n+\delta,
\qquad e_0=0.
$$

因此 $e_n\le n\delta$。证毕。

当要求视界 $n$ 内的记录分布误差不超过 $\varepsilon$ 时，一个充分条件是

$$
\boxed{n\delta\le\varepsilon.}
$$

这个命题只适用于“每一步重新建立记录”的无记忆协议。若同一个记录单元被相干复用，旧关联会留在联合系统中，过程不再由固定的 $B$ 描述；第 55 节的相位回流模型已经给出相同单步作用可以周期性恢复相干的反例。此时必须把记录单元并入状态，或建立带记忆的多时误差界。

<a id="entry-280"></a>

### 70.3 完全区分历史的容量下界

设记忆系统维数为 $d_M$，用一个 POVM $(E_j)_j$ 读取它。若有 $N$ 个历史被编码为密度矩阵 $\rho_1,\ldots,\rho_N$，并且满足

$$
\operatorname{Tr}(E_j\rho_i)=\mathbf 1_{i=j},
$$

则 `FiniteMemoryHistoryCapacity.finite_memory_history_capacity` 给出

$$
\boxed{N\le d_M.}
$$

证明的线性核心是：每个 $\rho_i$ 的支撑落在 $E_i$ 的值域，每个不同历史的支撑彼此正交；$d_M$ 维空间至多容纳 $d_M$ 个非零两两正交向量。

若记忆由 $b$ 个量子比特构成，$d_M=2^b$，则完全区分 $N$ 个历史要求

$$
\boxed{b\ge\lceil\log_2N\rceil.}
$$

对长度 $L$、禁止相邻 $1$ 的 Zeckendorf 合法窗口，候选构型数为

$$
|\mathcal W_L|=F_{L+2}.
$$

若每个合法构型都必须在一次读取中被完全区分，记忆维数至少为 $F_{L+2}$。若实验族只区分这些构型的 $N$ 个未来响应类，则容量下界只对 $N$ 生效，而不是对全部 $F_{L+2}$ 个标签生效。

这是编码容量和预测容量的区别：增加 Zeckendorf 合法字串会增加候选标签，但只有当它们落入不同的任务响应类时，才增加必须保留的记录数。近似区分时，$N\le d_M$ 不再是充分描述；需要改用记录态的迹距离、Gram 重叠或本节的闭合缺陷 $\delta$。

<a id="entry-281"></a>

### 70.4 投影动力学何时可以写成经典转移

`ProjectedUnistochasticDynamics.projected_dynamics_is_unistochastic` 对每一步执行构型投影的协议给出

$$
K_{ij}=|U_{ij}|^2,
$$

以及

$$
\mathbf p_{n+1}=K\mathbf p_n.
$$

$K$ 是双随机矩阵。这个结论的前提是每一步确实插入了投影；未测量的连续幺正演化不自动服从同一个 $K$。源码中的 `initialWeights` 也没有自动假设非负和归一，所以只有另外加入概率向量条件时，$\mathbf p_n$ 才能直接称为概率分布。

因此，经典转移矩阵不是从“有一个量子基底”自动得到的，而是从

$$
\text{指定投影协议}
+
\text{幺正演化}
+
\text{概率初始条件}
$$

共同得到的。更换为相干复用协议，或者把投影记录留在可访问环境中，都会改变有效过程。

<a id="entry-282"></a>

### 70.5 稳定经典对象的有限视界定义

给定实验族 $\mathfrak T$、视界 $H$ 和容许误差 $\varepsilon$，对两个历史 $h,h'$ 定义

$$
 h\sim_{\mathfrak T,H,\varepsilon}h'
$$

当且仅当任意 $T\in\mathfrak T$、任意长度不超过 $H$ 的记录序列，其输出概率分布的总变差距离不超过 $\varepsilon$。

这个关系把三种条件放在同一个对象定义中：

$$
\begin{aligned}
&\text{当前读出足以区分哪些历史；}\\
&\text{记录通道是否在视界内近似闭合；}\\
&\text{隐藏历史是否通过回流在视界内重新可见。}
\end{aligned}
$$

若固定记录通道满足 $|R_{ij}|\le q<1$，则第 70.1 节提供指数项 $q^H$；若逐步闭合缺陷为 $\delta$，则第 70.2 节提供 $H\delta$；若读数存在任务噪声，则第 69 节提供 $c_{\mathrm{task}}\nu$。在这些项都被转换到同一个输出距离后，可以使用

$$
\boxed{
\text{总预测误差}
\le
\text{记录收缩尾项}
+
\text{闭合缺陷项}
+
\text{读出噪声项}
+
\text{其余已标定的历史回流项}.
}
$$

因此当前尺度上的“经典对象”是一个有限预测等价类，而不是脱离实验协议的绝对实体。更换允许的实验族、视界、记录访问范围或误差容限，可能细化或合并这些类。

本节组合了现有记录通道、pinching 幂等性、有限记忆容量与投影动力学的边界；`StaticLossVersusReturnFlow` 仍只提供一般实线性回流反例，不能被当作量子通道定理。Zeckendorf 在这里提供合法构型的离散索引，尚未由本仓量子模块自动生成 Fibonacci 约束 Hilbert 空间或其 Hamiltonian。不从这些有限模型推出唯一测量结果、宇宙经典性或物理耦合常数。

<a id="section-71"></a>

## 71. 幂等记录的有限视界强化与近似记忆容量

第 70 节给出的逐步误差界

$$
D(A^n\rho,B^n\rho)\le n\delta
$$

适用于一般的逐步通道比较，但在本卷当前采用的 pinching 协议中，还可以利用记录映射的幂等性得到更强的结论。令

重复施加记录映射本身满足 $\mathcal E^n=\mathcal E$（$n\ge1$），所以它在一次作用后就到达自己的固定像空间。这里需要区分的是：幂等性不保证一个另行指定的未记录演化 $\Phi$ 会把完整状态吸引到这个像空间，也不保证记录对 $\Phi$ 之后的预测闭合。

$$
A=\mathcal E\Phi,
\qquad
B=\mathcal E\Phi\mathcal E,
\qquad
\mathcal E^2=\mathcal E.
$$

由于 $\mathcal E$ 是记录后的 pinching，$A\rho$ 和 $B\rho$ 都属于 $\operatorname{im}\mathcal E$。若 $\sigma\in\operatorname{im}\mathcal E$，则 $\mathcal E\sigma=\sigma$，从而

$$
A\sigma
=\mathcal E\Phi\sigma
=\mathcal E\Phi\mathcal E\sigma
=B\sigma.
$$

也就是说，$A$ 与 $B$ 在第一次记录之后限制为同一个像空间内的通道。设

$$
\delta
=
\sup_{\rho\in\mathsf D}
D(A\rho,B\rho),
$$

其中现在明确取 $\mathsf D$ 为全部有限维密度态，且假设 $\mathcal E$ 与 $\Phi$ 都是保持密度态域的 CPTP 通道，$\mathcal E$ 还满足幂等性。若只在一个真子集上取上确界，则还必须另加条件 $B^k(\rho)\in\mathsf D$，才能把同一上界用于后续轨道。

则对任意 $n\ge1$，迹距离收缩性给出

$$
\boxed{
D(A^n\rho,B^n\rho)
\le
D(A\rho,B\rho)
\le
\delta.
}
$$

证明可以写成一行递归。令 $C$ 为 $A$ 与 $B$ 在 $\operatorname{im}\mathcal E$ 上共同的限制，则

$$
A^n\rho=C^{n-1}A\rho,
\qquad
B^n\rho=C^{n-1}B\rho.
$$

于是

$$
D(A^n\rho,B^n\rho)
=D(C^{n-1}A\rho,C^{n-1}B\rho)
\le D(A\rho,B\rho).
$$

因此，在固定、无记忆、每步都重新 pinching 的协议中，$n\delta$ 是通用的累积上界，而

$$
\boxed{
D(A^n\rho,B^n\rho)\le\delta\quad(n\ge1)
}
$$

是利用幂等记录结构得到的强化。这个强化不适用于相干复用同一个记录单元的协议：那时完整联合态未必在每一步落入同一个无记忆像空间，旧关联可以沿联合动力学返回可见部分。故“误差是否随视界线性累积”本身也是协议相关的性质。

<a id="entry-284"></a>

### 71.1 完全容量与近似容量必须分开

第 70 节的

$$
N\le d_M
$$

有一个不可省略的前提：同一个记忆 POVM 必须**完美区分**所编码的 $N$ 个状态，即存在结果标签 $j$ 满足

$$
\operatorname{Tr}(E_j\rho_i)=\mathbf 1_{i=j}.
$$

这个条件推出不同记忆态支撑两两正交，所以 $N$ 不得超过记忆 Hilbert 空间维数 $d_M$。若记忆由 $b$ 个 qubit 构成，才可进一步得到

$$
b\ge\lceil\log_2N\rceil.
$$

因此，Zeckendorf 合法窗口的数量

$$
|\mathcal W_L|=F_{L+2}
$$

只有在**每一个合法构型都必须由一次读取完全区分**时，才给出

$$
d_M\ge F_{L+2}.
$$

若实验只要求区分 $N$ 个未来响应类，容量下界只在**同一个记忆 POVM 能完美恢复这 $N$ 个类的标签**时作用于这 $N$ 类。仅仅有不同的未来概率律，并不推出一次读取就能完美区分它们。如果若干合法字串在允许实验族中产生相同响应，它们可以共享同一条记录，不需要为每个 Zeckendorf 标签配置独立记忆。

完全区分之外，还有两个不同的近似问题。

第一，可以要求不同记忆态的迹距离至少为某个阈值：

$$
D(\rho_i^M,\rho_j^M)\ge 1-\varepsilon.
$$

这给出有限误差下的可区分性问题，容量不再由一个整数 $N\le d_M$ 单独刻画，而要同时依赖 $d_M$、$\varepsilon$ 和允许的测量族。

第二，可以直接控制记录态的 Gram 矩阵

$$
G_{ij}=\langle r_j|r_i\rangle.
$$

其中 $|G_{ij}|$ 小表示两条记录的相干重叠小，$G_{ij}$ 接近单位模则表示它们即使带有不同相位，也没有形成稳定的可区分记录。对于条件记录通道，非对角系统项按

$$
\rho_{ij}\longmapsto G_{ij}\rho_{ij}
$$

变化。因此，近似记录应同时报告：

$$
\text{状态可区分度 }D(\rho_i^M,\rho_j^M),
\qquad
\text{相干重叠 }|G_{ij}|,
\qquad
\text{视界内闭合缺陷 }\delta.
$$

它们分别回答“能否读出”“相干还剩多少”和“被省略的部分会不会回来”。把这三个量压成单一的历史条数，会丢掉协议与时间尺度的信息。

<a id="entry-285"></a>

### 71.2 对稳定经典对象的修正定义

给定实验族 $\mathfrak T$、预测视界 $H$、误差容限 $\varepsilon$ 和记录访问范围 $\mathfrak R$，可以定义当前对象的有限响应**容差关系**：

$$
h\sim_{\mathfrak T,H,\varepsilon,\mathfrak R}h'
$$

当且仅当对所有 $T\in\mathfrak T$，所有长度不超过 $H$ 的记录序列，以及所有允许的记录访问操作 $R\in\mathfrak R$，两段历史给出的输出分布总变差距离不超过 $\varepsilon$。当 $\varepsilon=0$ 时它才是严格的输出等价关系；当 $\varepsilon>0$ 时一般不传递，不能直接把它称为等价类。若需要有限误差下的类，必须另行指定聚类规则或先取精确等价商再定义近似邻域。

在这个定义下，“需要保留多少历史”不是一个脱离协议的常数，而是以下数据的函数：

$$
\boxed{
\text{所需记忆}
=
\text{响应类数量}
+
\text{记录态的近似区分成本}
+
\text{视界内的回流与闭合误差}.
}
$$

若实验族缩小、访问范围减少或视界变短，原先不同的历史可能落入同一个容差邻域；若允许更强的联合操作或更长的视界，它们又可能被重新区分。这种相对性有明确的操作索引，并不等于任意描述都同样有效。闭合缺陷 $\delta$ 也不是独立的近似判别误差；要谈近似容量，还需指定要判别的标签、允许的 POVM 和错误准则。

因此，本卷目前能够支持的最严格表述是：

$$
\boxed{
\text{稳定的经典现实}
=
\text{在指定实验族、记录访问范围和有限视界内，}
\text{对后续响应近似闭合的有限记录类}.
}
$$

这一定义保留了三条边界。记录通道的固定点可以是经典的，但不保证具有吸引性；完全记忆容量只在完美区分前提下给出维数下界；Zeckendorf 的 Fibonacci 计数只统计候选合法构型，不自动等于必须保留的物理记忆数。第 70 节的收缩尾项、闭合缺陷项和噪声项只有在它们分别比较同一协议中的相应端点、所有需要的前缀以及联合历史寄存器（必要时还包括参考系统）时，才能合成为一个输出误差界；当前写法应读作带这些条件的三角不等式模板，而不是已经证明的多时自适应记录定理。后续若要把这条主线推进为新的 Lean 内容，最小的可复用目标是分别形式化幂等像空间上的一次性误差界，以及带 Gram/迹距离阈值和明确判别任务的近似记忆容量，而不是把它们合并成一个无条件的“经典化定理”。
