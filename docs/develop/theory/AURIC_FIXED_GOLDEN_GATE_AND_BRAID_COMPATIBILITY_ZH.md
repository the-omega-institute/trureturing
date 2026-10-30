<a id="auric-fixed-golden-gate"></a>

# AURIC 固定黄金门与编织相容性

**固定单门、合法 Fibonacci 路径与编码近似普适性 · 2026-10-29**

> 本文是用户提供的“固定黄金门与编织相容性”正式稿的独立纯 Markdown 转换版。数学表达使用标准 Markdown 数学块；本文不依赖 TeX 编译。
>
> 固定项目版本：[`9ccde90c0c0d10b50d8ebcd55a8499b357c787d1`](https://github.com/the-omega-institute/trureturing/commit/9ccde90c0c0d10b50d8ebcd55a8499b357c787d1)，提交时间：2026-10-29 15:54:29（Asia/Singapore）。
>
> 本文把项目已有的路径、投影和可控性接口接成条件定理。Fibonacci 编织的密度与编译性引用外部数学结果；本文不把抽象门的存在写成原生硬件已经提供。

## 摘要与主结论

在项目已经建立的 Fibonacci 合法路径与加权投影上，可以构造一枚固定三比特酉门 $K$。它在 AURIC 五模式空间中有显式矩阵；配合明确的编码初态、边界位和相邻接线，只调用这一枚门，就能任意精度地逼近任意量子电路。

固定门满足

$$
\boxed{K^{10}=I,\qquad K^{-1}=K^9,\qquad K^5=2\mathcal P-I.}
$$

因此，“反”在这个模型里有精确含义：基本门的第五次作用就是一次投影反射。这里的“NAND 式”指固定一种门，通过重复使用和改变接线位置获得计算通用性；量子情形采用编码与任意精度逼近的定义。

本稿的证明链为

$$
\text{合法路径}
\longrightarrow
\text{黄金投影}
\longrightarrow
\text{编织相位比例}
\longrightarrow
\text{固定局部门}
\longrightarrow
\text{编码近似普适性}.
$$

## 1. 项目接口与逻辑范围

本轮固定核对 `dev` 分支提交 [`9ccde90c0c0d10b50d8ebcd55a8499b357c787d1`](https://github.com/the-omega-institute/trureturing/commit/9ccde90c0c0d10b50d8ebcd55a8499b357c787d1)。已有接口包括：

| 项目已有结果 | 本文如何使用 |
| --- | --- |
| 合法词与 Fibonacci 融合路径对应；带权路径投影满足 Temperley--Lieb 关系 | 在路径坐标中定义黄金投影，并逐个对应编织生成元。 |
| 在可独立选择各位置的 $X$ 控制、另供一个固定位置的 $Y$ 控制及任意实角条件下，整个有限合法空间可控 | 说明固定局部门的实现接口，但不把有限实例可控性升级为统一原生成本定理。 |
| 最新续卷区分源树嫁接、独立组合与联合相干拒绝 | 保留结果概率、后态和联合记录之间的区别。 |

对应项目来源为[《融合自旋链与 QCA 切面》 §§12--16](https://github.com/the-omega-institute/trureturing/blob/9ccde90c0c0d10b50d8ebcd55a8499b357c787d1/docs/develop/theory/FUSION_SPIN_CHAIN_QCA_CUT_OBSTRUCTIONS.md)、[《合法门、状态机与 Shor 读出》定理 11.2](https://github.com/the-omega-institute/trureturing/blob/9ccde90c0c0d10b50d8ebcd55a8499b357c787d1/docs/develop/theory/FIB_LEGAL_GATES_STATE_MACHINES_AND_SHOR_READOUT.md)，以及[《相干重构续卷》 §§51--56](https://github.com/the-omega-institute/trureturing/blob/9ccde90c0c0d10b50d8ebcd55a8499b357c787d1/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION.md)。

项目结果提供接口和前提；本稿的固定门、相位方程、边界对应和编码误差链是本文的组织与纸面证明。它们仍然需要明确的复 Hilbert 空间、操作合同、制备、控制和读出。

## 2. 从五模式到黄金投影

### 定义 2.1（合法路径空间）

令

$$
\mathcal B_m=
\left\{
b_1\cdots b_m\in\{0,1\}^m:
b_jb_{j+1}=0
\right\},
\qquad
\mathcal H_m=\mathbb C^{\mathcal B_m}.
$$

这里禁止相邻两个位置同时为 $1$。当 $m=3$ 时，合法词恰有

$$
000,\quad100,\quad010,\quad001,\quad101.
$$

采用项目模式标签，可写为

$$
|\mathrm{null}\rangle,\quad|1\rangle,\quad|2\rangle,\quad|3\rangle,\quad|13\rangle.
$$

合法词数满足

$$
\dim\mathcal H_m=F_{m+2},
$$

因为按首位分类后得到 Fibonacci 递推。

### 定理 2.2（相同扩展规则锁定黄金比例）

考虑标签 $\mathbf1,\tau$ 的邻接矩阵

$$
A=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

若严格正的扩展权重满足

$$
Ad=\delta d,\qquad d_{\mathbf1}=1,
$$

则

$$
\boxed{\delta=\varphi=\frac{1+\sqrt5}{2},\qquad d_\tau=\varphi.}
$$

**证明。** 第一行给出 $d_\tau=\delta$，第二行给出 $1+d_\tau=\delta d_\tau$。所以 $\delta^2-\delta-1=0$；严格正性排除负根，结论成立。∎

正权重此时不是测量概率。它是局部扩展相容性所选出的维数权重。

### 定义 2.3（五模式黄金投影）

在上述五模式顺序中，定义

$$
P_A=
\begin{pmatrix}
\varphi^{-1}&0&\varphi^{-3/2}&0&0\\
0&0&0&0&0\\
\varphi^{-3/2}&0&\varphi^{-2}&0&0\\
0&0&0&0&0\\
0&0&0&0&1
\end{pmatrix}.
$$

等价地，令

$$
|v\rangle=\varphi^{-1/2}|\mathrm{null}\rangle+\varphi^{-1}|2\rangle,
$$

则

$$
P_A=|v\rangle\langle v|+|13\rangle\langle13|.
$$

由于 $\varphi^{-1}+\varphi^{-2}=1$，有 $\langle v|v\rangle=1$，从而

$$
P_A^\dagger=P_A,\qquad P_A^2=P_A.
$$

因此 $\mathrm{null}$ 与 $2$ 参与黄金比例的相干混合，$13$ 是另一个选中的正交通道，而 $1$ 与 $3$ 属于投影的核。物理含义仍取决于如何制备、控制和读出这些模式。

## 3. 相融对复相位的限制

项目已有的加权路径投影满足

$$
P_i^2=P_i=P_i^\dagger,
$$

$$
P_iP_{i+1}P_i=\varphi^{-2}P_i,
\qquad
P_{i+1}P_iP_{i+1}=\varphi^{-2}P_{i+1},
$$

以及远距离对易关系

$$
[P_i,P_j]=0,\qquad |i-j|\ge2.
$$

给每个投影配置两谱值酉门

$$
B_i=s\bigl[I+(z-1)P_i\bigr],qquad |s|=|z|=1,
$$

其中 $s$ 是共同相位，$z$ 是两个投影通道之间的相位比例。

### 定理 3.1（非平凡编织相容性限制相位比例）

假设相邻投影不同并要求

$$
B_iB_{i+1}B_i=B_{i+1}B_iB_{i+1}.
$$

除去 $z=1$ 的标量退化情形，有

$$
\boxed{z=e^{3\pi\mathrm i/5}\quad\text{或}\quad z=e^{-3\pi\mathrm i/5}.}
$$

**证明。** 记 $P=P_i$、$Q=P_{i+1}$、$\lambda=\varphi^{-2}$、$t=z-1$。直接展开两边，利用 $P^2=P$、$Q^2=Q$、$PQP=\lambda P$ 和 $QPQ=\lambda Q$，得到

$$
B_PB_QB_P-B_QB_PB_Q
=s^3t(1+t+\lambda t^2)(P-Q).
$$

因为 $P\ne Q$ 且排除 $t=0$，必须有 $1+t+\lambda t^2=0$。代入 $t=z-1$ 得

$$
z+\varphi^{-2}(z-1)^2=0,
$$

即

$$
z^2+\varphi^{-1}z+1=0.
$$

又因 $2\cos(3\pi/5)=-\varphi^{-1}$，两个根正是 $e^{\pm3\pi\mathrm i/5}$。反向代入同一展开式证明充分性。∎

这使“相融”成为可计算条件：同一局部结构沿两种三步组合得到相同算符，所以相位比例受到代数约束。证明使用了复 Hilbert 空间和指定投影族，没有从裸五点集合推出复数域；编织关系确定的是 $z$，共同相位 $s$ 仍自由。

还可得到定量缺陷。若 $P\ne Q$，则

$$
\|P-Q\|=\sqrt{1-\varphi^{-2}},
$$

故

$$
\boxed{
\mathcal D(z)=
\varphi^{-2}\sqrt{1-\varphi^{-2}}\,|z-1|
\left|z^2+\varphi^{-1}z+1\right|.
}
$$

只要远离标量退化点 $z=1$，小编织缺陷就迫使相位接近上述两个共轭根。这是近似相融的误差尺度，而不是新的物理公理。

## 4. 一枚固定的 AURIC 黄金门

取标准方向

$$
\zeta=e^{3\pi\mathrm i/5},
\qquad
K_A=\zeta\bigl[I+(\zeta-1)P_A\bigr].
$$

为了在任意长度链上统一使用，令三位置为 $L,C,R$，并记

$$
n=|1\rangle\langle1|,
\qquad
g=(I-n_L)(I-n_R).
$$

定义三比特算子

$$
\boxed{
\mathcal P=
n_Ln_R+
g\left[
\varphi^{-1}(I-n_C)
+\varphi^{-2}n_C
+\varphi^{-3/2}X_C
\right].
}
$$

最后定义固定门

$$
\boxed{K=\zeta\bigl[I+(\zeta-1)\mathcal P\bigr].}
$$

所有参数已经固定，运行时只选择把同一枚门作用在哪三个相邻位置。

### 定理 4.1（酉性、十阶周期与反射）

上述 $\mathcal P$ 是完整八维三比特空间上的正交投影；$K$ 是酉门，并满足

$$
K^{10}=I,\qquad K^{-1}=K^9,\qquad K^5=2\mathcal P-I.
$$

此外，它保持任意长度链上的合法词空间。

**证明。** 按左右两位分块：

| 左右位 | 中间位上的 $\mathcal P$ |
| --- | --- |
| $00$ | $\begin{pmatrix}\varphi^{-1}&\varphi^{-3/2}\\ \varphi^{-3/2}&\varphi^{-2}\end{pmatrix}$，一个秩一投影 |
| $11$ | $I$ |
| $01$、$10$ | $0$ |

所以 $\mathcal P^2=\mathcal P=\mathcal P^\dagger$。在 $\ker\mathcal P$ 上，$K$ 的特征值是 $\zeta$；在 $\operatorname{ran}\mathcal P$ 上，特征值是 $\zeta^2$。两者都是十次单位根，故 $K^{10}=I$。又 $\zeta^5=-1$，所以 $K^5$ 在核上为 $-1$、在像上为 $+1$，即 $K^5=2\mathcal P-I$；于是 $K^{-1}=K^9$。

最后，唯一非对角变化是 $000\leftrightarrow010$。它只在中间位两侧均为零时翻转中间位，不会产生相邻 $11$，故保持合法词空间。∎

单独在同一位置重复 $K$ 只有有限周期。通用计算来自不同位置的同型门之间的非交换组合。

## 5. 固定门的编码近似普适性

### 5.1 固定边界与路径对应

给 $m$ 个内部合法位加入三个外部位

$$
b_{-1}=1,\qquad b_0=0,\qquad b_{m+1}=0.
$$

令 $K_j$ 表示将同一枚 $K$ 作用于 $(j-1,j,j+1)$，其中 $j=0,\ldots,m$。外部三个位在这些操作中精确保持不变。

将内部位解释为融合路径标签：

$$
b_j=1\iff x_{j+1}=\mathbf1,
\qquad
b_j=0\iff x_{j+1}=\tau.
$$

固定

$$
x_0=\mathbf1,\qquad x_1=\tau,\qquad x_{m+2}=\tau.
$$

这给出合法词空间与 $m+2$ 个 Fibonacci 任意子、总荷为 $\tau$ 的路径空间之间的酉映射 $W_m$。

### 定理 5.1（逐个生成元的精确对应）

在合法空间上

$$
\boxed{
W_m\widetilde K_jW_m^\dagger
=\zeta\bigl[I+(\zeta-1)P_{j+1}\bigr]
=B_{j+1},
}
$$

其中 $\widetilde K_j$ 是加入并去掉固定外部位之后的内部作用。

**证明。** 对内部位置，按左右位分类，$\mathcal P$ 的四个块恰好对应融合路径的局部真空通道投影。左端需要单独核对：当中心为 $b_0=0$、左侧固定为 $b_{-1}=1$ 时，$g=0$，投影退化为 $\mathcal P=n_1$，恰好判断第一对任意子是否融合为真空，同时不翻转边界位。因此包括最左端在内，所有生成元都有同一固定矩阵实现。∎

两个融合通道上的相位为

$$
R_{\mathbf1}=\zeta^2=e^{-4\pi\mathrm i/5},
\qquad
R_\tau=\zeta=e^{3\pi\mathrm i/5},
$$

与标准 Fibonacci 编织数据一致。

### 5.2 逻辑编码

对 $n$ 个逻辑比特取 $m=4n-1$，规定

$$
b_{4r-3}=q_r,\qquad b_{4r-2}=0,\qquad b_{4r-1}=1,
$$

并在相邻块之间放一个零。例如

$$
J_1|q\rangle=|q01\rangle,
$$

$$
J_2|q_1q_2\rangle=|q_1\,0\,1\,0\,q_2\,0\,1\rangle.
$$

再加入外部边界，得到编码 $\widehat J_n$，共使用 $4n+2$ 个位置。在融合路径语言中，每四个任意子构成一个总荷为真空的逻辑块，末端再接一个 $\tau$ 旁观者。

### 定理 5.2（固定黄金门的近似编码普适性）

在上述编码、初始化和相邻接线条件下，对任意 $n$ 比特酉变换 $U$ 和任意 $\varepsilon>0$，存在仅由 $K$ 的正向调用构成的有限电路 $C_K$，使

$$
\boxed{
\left\|C_K\widehat J_n-e^{\mathrm i\gamma}\widehat J_nU\right\|_{\mathrm{op}}<\varepsilon
}
$$

对某个整体相位 $\gamma$ 成立。

**编码桥假设。** 对每个固定 $n$，路径编码 $\widehat J_n$ 与四任意子总荷为真空的逻辑块编码之间存在与目标 $U$ 无关的有限局部 $F$-变换及末端旁观者固定酉；该固定变换逐个把标准编织生成元 $\sigma_j^{\pm1}$ 对应到路径坐标中的 $B_{j+1}^{\pm1}$，并保持算子范数。

**证明。** 在上述编码桥假设下，Fibonacci 编织理论的外部密度与编译结果给出该四任意子编码上的近似通用性：单比特门与纠缠门可由编织任意精度逼近，最终编码泄漏也可任意压低。可参见 Freedman--Larsen--Wang 的 Fibonacci 编织普适性来源 [arXiv:quant-ph/0001108](https://arxiv.org/abs/quant-ph/0001108)。取实现目标 $U$ 的足够准确编织词。由定理 5.1，每个编织生成元可精确替换为对应位置的 $K$，这是坐标变换，不增加误差。若编织词含逆向生成元，利用 $K^{-1}=K^9$ 替换为九次正向调用。因此整个电路只使用同一枚 $K$，并保持原编织逼近误差界。若原词含 $L$ 个正向或逆向字母，替换后至多调用 $9L$ 次 $K$。∎

编码中的固定 $0,1$ 标记规定输入与最终目标编码；跨块计算期间不能把它们全部冻结。运算可以暂时离开逻辑编码子空间，但始终留在合法路径空间；上面的算子范数界保证最终泄漏概率不超过 $\varepsilon^2$，并且对与外部系统纠缠的输入同样成立。

因此这里的“NAND 式”量子构造包含固定门、固定参数、明确接线、明确编码、普适性证明和误差界。有限门字是可数的，任意酉矩阵形成连续族，所以采用近似普适性；连续操作意义可作为离散门字在误差范数下的闭包出现。

## 6. 黄金递归中的条件返回

### 定理 6.1（相融循环的条件返回）

设相邻投影满足

$$
PQP=\varphi^{-2}P,
$$

初态满足 $\rho=P\rho P$、$\operatorname{Tr}\rho=1$。先测量 $Q$ 并保留成功支，再测量 $P$ 并保留成功支，则未归一输出为

$$
\boxed{PQ\rho QP=\varphi^{-4}\rho.}
$$

因此两次都成功的概率是 $\varphi^{-4}$，成功条件下状态精确返回 $\rho$；重复 $k$ 次完整循环，全部成功概率是 $\varphi^{-4k}$。

**证明。** 由支撑条件

$$
PQ\rho QP=PQP\,\rho\,PQP=\varphi^{-4}\rho.
$$

取迹得到成功概率，再迭代即可。∎

这区分了条件化后的状态稳定与支撑该分支的总概率质量下降。该结论使用 Born 规则与 Lüders 测量，是指定量子框架中的推论。

另一方面，同一黄金权重也定义经典随机过程

$$
T_{ab}=\frac{A_{ab}d_b}{\varphi d_a},
\qquad
\sum_bT_{ab}=1.
$$

因此正性、递归和 Fibonacci 权重不足以单独区分经典与量子；相干复合方式和联合仪器仍必须进入理论。

## 7. 联合记录中的隐藏关系

### 7.1 绝对共轭方向

因为 $\mathcal P$ 是实矩阵，两种共轭选择满足

$$
K_- = \overline{K_+}.
$$

如果初态和计算基读出都是实的，将整个门协议共轭只会把每条分支振幅变成其复共轭，所有概率保持不变；该读出菜单无法选择绝对共轭方向。但两个系统之间的相对方向可以通过联合操作进入相关记录。

### 7.2 八记录实例

从 $|00\rangle$ 出发，施加联合投影测量

$$
P=|++\rangle\langle++|,\qquad Q=I-P,
$$

保留 $P/Q$ 结果，再分别作局部读出。比较两协议：同向时两侧都采用 $|\pm i\rangle$ 基；反向时第二侧采用共轭基并保持结果标签对应固定，其中

$$
|\pm i\rangle=\frac{|0\rangle\pm i|1\rangle}{\sqrt2}.
$$

在 $P$ 支，四个完整记录的概率均为 $1/16$。在 $Q$ 支，概率为

| 两侧结果 | 同向 | 反向 |
| --- | ---: | ---: |
| $++$ | $5/16$ | $1/16$ |
| $+-$ | $1/16$ | $5/16$ |
| $-+$ | $1/16$ | $5/16$ |
| $--$ | $5/16$ | $1/16$ |

完整分布的总变差距离为 $1/2$；只保留任一侧局部结果时差异消失。

**证明要点。** 拒绝支的未归一向量为

$$
|\Xi\rangle=Q|00\rangle=|00\rangle-\frac12|++\rangle.
$$

对 $s,t\in\{+1,-1\}$，

$$
\langle si,ti|\Xi\rangle=\frac{3+st+i(s+t)}8.
$$

模平方给出同向表；第二侧共轭对应 $t\mapsto-t$，得到反向表。∎

拒绝支系数矩阵为

$$
M=\frac14\begin{pmatrix}3&-1\\-1&-1\end{pmatrix},
\qquad \det M=-\frac14,
$$

所以拒绝支是纠缠态。局域操作与经典通信从乘积输入出发不能产生这样的纠缠纯态分支；局域测量可以复制二值效果的概率，却一般不能复制 $\rho\mapsto Q\rho Q$ 的相干输出。

若要以“预测之间相融”解释量子性，至少需要

$$
\boxed{\text{状态之间的相容关系}+\text{操作的相干复合}+\text{记录形成的联合仪器}.}
$$

单一输出概率表不足以确定完整量子行为。

## 8. 静态操作网、切面与内生观察者

### 定义 8.1（静态操作网及合法切面）

把系统表示为有向无环操作网：边承载量子系统或经典记录，顶点承载门、通道或带结果的测量仪器，边界指定制备和最终读出。合法切面是某个向下闭合顶点集的边界，并保留尚未处理的输入、已经产生的输出及必要记录。

### 定理 8.2（固定网络的切面不变性）

记切面之前和之后的组合分别为 $\Phi_{\le c}$ 和 $\Phi_{>c}$。边界事件概率为

$$
\boxed{p=\operatorname{Tr}\left[\Phi_{>c}^{*}(E)\,\Phi_{\le c}(\rho)\right].}
$$

同一网络的任意合法拓扑求值顺序给出相同结果。

**证明。** 通道对偶定义给出

$$
\operatorname{Tr}[E\Phi_{>c}(\sigma)]
=\operatorname{Tr}[\Phi_{>c}^{*}(E)\sigma].
$$

代入 $\sigma=\Phi_{\le c}(\rho)$ 即得切面公式。任意两个拓扑排序可以通过交换相邻不可比顶点互相变换；当这些顶点作用于独立因子且无记录依赖时，交换不改变整体通道。若保留记录，交换条件必须升级为完整接口上的通道交换；系统端对易本身不够。∎

同一条线上若 $AB\ne BA$，交换它们会改变网络。若所有操作都彼此对易，它们生成群的闭包仍对易，不能实现完整量子普适性。相融的有力数学含义是

$$
B_iB_{i+1}B_i=B_{i+1}B_iB_{i+1},
$$

即不同组合路径的一致性，而不是所有操作都交换。

### 定义 8.3（内生观察者的记忆耦合）

给定投影 $P$，加入初态为 $|0\rangle$ 的记忆位并定义

$$
R_P=P\otimes X+(I-P)\otimes I.
$$

读出记忆位得到两支

$$
\rho\mapsto P\rho P,
\qquad
\rho\mapsto(I-P)\rho(I-P).
$$

观察者因此可以放进联合网络内部：得到一个结果对应系统与记忆形成可读出的相关性。若记忆必须完美区分 $M$ 种历史，其维数至少为 $M$；“预测行为成为自身增长”在有限模型中表现为记录容量、相关性和可区分历史的增长。

## 9. 适用范围、实现接口与结论

本轮实质结果是

$$
\boxed{
\text{一个固定黄金投影相位门}
+\text{相邻位置选择}
+\text{明确编码与边界}
\Longrightarrow
\text{近似通用量子计算}.}
$$

它具有可核查矩阵、代数证明、编码、接线规则和误差界。物理实现还有一个具体接口。令

$$
\cos\eta=\varphi^{-1/2},
\qquad
\sin\eta=\varphi^{-1},
$$

并定义

$$
V=e^{-\mathrm i\eta gY_C},
\qquad
D=n_Ln_R+g(I-n_C).
$$

则

$$
\mathcal P=VDV^\dagger,
$$

所以

$$
\boxed{K=\zeta\,V\,e^{\mathrm i(3\pi/5)D}\,V^\dagger.}
$$

这把统一实现要求压缩为固定受条件保护旋转与固定条件相位。项目已有的有限空间可控性保证相应有限实例存在实现；统一的局部实现成本还需要针对原生控制菜单继续证明。

合法词空间与任意子路径空间的对应，不自动带来真实任意子的拓扑保护；Hilbert 空间同构和物理操作的拓扑性质属于不同层次。可参见关于 Rydberg 链与 Fibonacci 路径的研究 [arXiv:1909.09652](https://arxiv.org/abs/1909.09652)。

因此，AURIC 五模式在这次构造中可以作为固定局部量子门的合法作用空间；计算力量来自黄金投影、非交换组合关系和可扩展编码。这个结论是条件完整的数学定理，仍不等于原生硬件已经供应该门、统一控制成本或实际读出服务。

## 参考文献

1. AURIC 项目，[FUSION_SPIN_CHAIN_QCA_CUT_OBSTRUCTIONS.md](https://github.com/the-omega-institute/trureturing/blob/9ccde90c0c0d10b50d8ebcd55a8499b357c787d1/docs/develop/theory/FUSION_SPIN_CHAIN_QCA_CUT_OBSTRUCTIONS.md)，固定提交，§§12--16。
2. AURIC 项目，[FIB_LEGAL_GATES_STATE_MACHINES_AND_SHOR_READOUT.md](https://github.com/the-omega-institute/trureturing/blob/9ccde90c0c0d10b50d8ebcd55a8499b357c787d1/docs/develop/theory/FIB_LEGAL_GATES_STATE_MACHINES_AND_SHOR_READOUT.md)，固定提交，定理 11.2。
3. AURIC 项目，[AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION.md](https://github.com/the-omega-institute/trureturing/blob/9ccde90c0c0d10b50d8ebcd55a8499b357c787d1/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION.md)，固定提交，§§51--56。
4. M. Freedman, M. Larsen, and Z. Wang, “A Modular Functor Which is Universal for Quantum Computation,” [arXiv:quant-ph/0001108](https://arxiv.org/abs/quant-ph/0001108)。本文只使用其 Fibonacci 编织密度/编译性结果。
5. 关于 Rydberg 链与 Fibonacci 路径的操作层区别，[arXiv:1909.09652](https://arxiv.org/abs/1909.09652)。
