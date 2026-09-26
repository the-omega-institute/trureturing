# 波粒整体的关系全息表示

## 0. 模型、关系接口与引用约定

**假设 0.1（有限维量子模型）。** 所有系统空间均为有限维复 Hilbert 空间，状态为正半定、迹为一的算子。通道为完全正保迹线性映射，仪器为和为保迹映射的有限族完全正映射。结果概率取分支输出的迹；仅在该迹为正时定义归一化条件后继。以上是模型规则，不作为从关系概念推出的结论。粒子式事件指指定探测接口产生的离散记录，不作为粒子物理定义的替代。

**定义 0.2（任务边界）。** 沿用[动态充分边界与内部观察者](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md)第 1—3 节的合法域、输出、后继与拼接接口。边界必须保留指定续接任务仍能访问的记忆、控制、参考和记录。模式编号的空间意义、阶段编号的钟标定、各部分的共同来源均作为额外模型数据。下文的有限维空间可以包含环境记忆，不限于单个受测系统。

**假设 0.3（标准表示工具）。** 使用矩阵乘法、谱定理、Cayley–Hamilton 定理及有限维通道的 Kraus 表示。通道与仪器的标准框架见 Watrous, *The Theory of Quantum Information*, [公开书稿](https://cs.uwaterloo.ca/~watrous/TQI/)。历史编码、双路径互补、Choi 表示与首次探测公式作为下述关系接口推导中的既有工具；其具体用途在相应条目内注明，不据此提出原创性主张。

## 1. 单激发、合法切面与关系体

**定义 1.1（单激发关系空间）。** 固定有限模式集 $X=\{1,\ldots,d\}$，$d\ge2$，令

$$
\mathcal H_1=\operatorname{span}_{\mathbb C}\{|x\rangle:x\in X\},
\qquad
|\psi\rangle=\sum_x\psi(x)|x\rangle,
\qquad
\sum_x|\psi(x)|^2=1.
$$

模式基正交归一。多个非零振幅仍表示同一单激发空间中的向量；激发数由所选扇区规定，不由非零坐标的个数规定。

**定义 1.2（相干运输）。** 给定合法切面链 $\Sigma_0\to\cdots\to\Sigma_N$ 及酉映射 $U_n:\mathcal H\to\mathcal H$。置

$$
V_0=I,\qquad V_n=U_{n-1}\cdots U_0,
\qquad \rho_n=V_n\rho_0V_n^\dagger.
$$

阶段 $n$ 仅为标签；若解释为历时，另给钟读数与标签的标定。未来会再次参与耦合的记忆包括在 $\mathcal H$ 内。

**定义 1.3（关系体的全息充分性）。** 对过程配置 $s$、边界摘要 $\eta(s)$ 与指定实验族 $\mathcal T$，称 $\eta$ 全息充分，当

$$
\eta(s)=\eta(t)
\Longrightarrow
\operatorname{Obs}(E[s])=\operatorname{Obs}(E[t])
\quad(E\in\mathcal T).
$$

若任务包含继续执行，观察值还包括合法性、分支概率及后继边界。该定义恢复的是指定任务的作用，不要求恢复内部的唯一搭建方式。

## 2. 相干路径与切面拼接

**命题 2.1（同一运输的展开与拼接）。** 对定义 1.2 的纯初态，置 $A_{b:a}=U_{b-1}\cdots U_a$，$A_{a:a}=I$，则

$$
\psi_N(x_N)=
\sum_{x_0,\ldots,x_{N-1}}
\psi_0(x_0)\prod_{n=0}^{N-1}U_n(x_{n+1},x_n),
$$

$$
A_{N:0}(x_N,x_0)
=\sum_{x_k}A_{N:k}(x_N,x_k)A_{k:0}(x_k,x_0).
$$

证明。逐次展开 $\psi_{n+1}(y)=\sum_xU_n(y,x)\psi_n(x)$ 得到第一式；第二式为 $A_{N:0}=A_{N:k}A_{k:0}$ 的矩阵元。这里的路径是展开指标，公式没有把各指标指定为已发生的经典记录。$\square$

**命题 2.2（路径模平方的不充分性）。** 只知道各项 $|a|^2,|b|^2$ 不能确定 $|a+b|^2$。

证明。恒等式

$$
|a+b|^2=|a|^2+|b|^2+2\operatorname{Re}(\overline a b)
$$

包含相对相位项。取 $(a,b)=(1,1)$ 与 $(1,-1)$，单项模平方相同而总模平方为 $4$ 与 $0$。因此先删去相对相位再拼接不能一般保持原边界响应。$\square$

## 3. 静态历史与钟条件化

**定义 3.1（钟—系统历史表示）。** 令 $\mathcal C_N=\operatorname{span}\{|0\rangle,\ldots,|N\rangle\}$，定义

$$
W\psi=\frac1{\sqrt{N+1}}\sum_{n=0}^N|n\rangle\otimes V_n\psi,
\qquad \Gamma=W\rho_0W^\dagger,
$$

$$
A_n=\langle n+1|\otimes I-\langle n|\otimes U_n,
\qquad K_{\rm hist}=\sum_{n=0}^{N-1}A_n^\dagger A_n.
$$

这是电路历史编码的有限形式；相关标准构造见 Aharonov 等，*Adiabatic Quantum Computation is Equivalent to Standard Quantum Computation*, [arXiv:quant-ph/0405098](https://arxiv.org/abs/quant-ph/0405098)。这里只使用编码与相邻传播约束，不引入该文的计算复杂度结论。

**命题 3.2（历史编码与切面态）。** 有 $W^\dagger W=I$、$K_{\rm hist}W=0$。在 $\Gamma$ 上读钟标签 $n$ 的概率为 $1/(N+1)$，对应系统条件态为 $\rho_n$。

证明。钟标签正交且 $V_n$ 酉，故

$$
W^\dagger W=\frac1{N+1}\sum_nV_n^\dagger V_n=I.
$$

$V_{n+1}=U_nV_n$ 给出 $A_nW=0$。展开

$$
\Gamma=\frac1{N+1}\sum_{n,m}|n\rangle\langle m|
\otimes V_n\rho_0V_m^\dagger
$$

并取第 $n$ 个钟对角块，得到 $\rho_n/(N+1)$，取迹与归一化即得。$\square$

**命题 3.3（钟条件化不产生模式选择）。** 取所有 $U_n=I$ 与 $\psi_0=(|L\rangle+|R\rangle)/\sqrt2$。每个钟条件态仍为 $|\psi_0\rangle\langle\psi_0|$，其 $L,R$ 非对角元为 $1/2$。故只读取钟标签不等于读取局域探测结果。

证明。直接代入命题 3.2。$\square$

## 4. 局域事件与记录后继

**定义 4.1（单 Kraus 局域仪器）。** 给定 $K_x:\mathcal H\to\mathcal H'$，满足 $\sum_xK_x^\dagger K_x=I$，令

$$
E_x=K_x^\dagger K_x,
\qquad J\psi=\sum_xK_x\psi\otimes|r_x\rangle,
$$

其中 $r_x$ 为正交记录标签。事件 $e=(n,a,x)$ 同时指定钟标签、实际仪器设置及局域结果。多 Kraus 结果的不可读内部指标在第 18 节处理。

**命题 4.2（钟—仪器联合分支）。** 有 $J^\dagger J=I$，且命题 3.2 的历史态给出

$$
p(n,x)=\frac1{N+1}\operatorname{Tr}(\rho_nE_x),
\qquad
\rho_{n,x}=\frac{K_x\rho_nK_x^\dagger}{\operatorname{Tr}(\rho_nE_x)}
$$

，第二式仅在分母正时定义。

证明。记录正交性使 $J^\dagger J=\sum_xK_x^\dagger K_x$。钟块 $\rho_n/(N+1)$ 经第 $x$ 分支变为 $K_x\rho_nK_x^\dagger/(N+1)$，取迹并归一化即得。该构造指定一次钟—仪器联合实验，不把历史编码的均匀钟权重解释成真实首次点击时间。$\square$

**命题 4.3（同一点击概率不决定受测对象的后继）。** 在 $\mathcal H_1$ 上，理想模式效果 $E_x=|x\rangle\langle x|$ 给出 $p(x\mid n)=\langle x|\rho_n|x\rangle$。取破坏性分支 $K_x=|\mathrm{vac}\rangle\langle x|$，取得结果后系统为空态；取保留模式的分支 $K_x=|x\rangle\langle x|$，取得结果后系统处于 $|x\rangle$。两者效果相同。

证明。分别计算 $K_x^\dagger K_x$ 和 $K_x\rho K_x^\dagger$。正交记录投影满足互斥且完备的结果合同，但上述合同不单独解释为何经验中呈现一个确定结果。$\square$

## 5. 路线记录、干涉与联合相干

**定义 5.1（双路径记录态）。** 对归一化 $d_L,d_R$，令

$$
|\Psi_\phi\rangle=
\frac{|L\rangle|d_L\rangle+e^{i\phi}|R\rangle|d_R\rangle}{\sqrt2},
\qquad \kappa=\langle d_L|d_R\rangle,
\qquad |\pm\rangle=\frac{|L\rangle\pm|R\rangle}{\sqrt2}.
$$

下述计算采用等振幅、纯记录态的限制。一般双路径互补关系见 Englert, *Fringe Visibility and Which-Way Information: An Inequality*, [DOI:10.1103/PhysRevLett.77.2154](https://doi.org/10.1103/PhysRevLett.77.2154)。

**命题 5.2（边界干涉的记录重叠因子）。** 忽略记录系统时

$$
p_\pm(\phi)=\frac12\bigl(1\pm\operatorname{Re}(e^{i\phi}\kappa)\bigr),
\qquad \mathcal V=|\kappa|.
$$

证明。投影到 $+$ 的记录向量为 $(d_L+e^{i\phi}d_R)/2$，取范数平方得到概率；负号同理。相位变化时的极值为 $(1\pm|\kappa|)/2$，代入可见度定义即得。$\square$

**命题 5.3（纯记录的可分辨性）。** 定义等先验记录的半迹距离

$$
\mathcal D=\frac12\bigl\||d_L\rangle\langle d_L|-|d_R\rangle\langle d_R|\bigr\|_1.
$$

则 $\mathcal D=\sqrt{1-|\kappa|^2}$，故 $\mathcal D^2+\mathcal V^2=1$。

证明。忽略不改变投影的整体相位后，记录态在其至多二维张成空间可写为 $|0\rangle$ 与 $|\kappa||0\rangle+\sqrt{1-|\kappa|^2}|1\rangle$。两投影之差迹为零，非零本征值为 $\pm\sqrt{1-|\kappa|^2}$。取迹范数即得；张成空间一维时差为零。$\square$

**命题 5.4（相干记录读取的条件恢复）。** 若 $d_L,d_R$ 正交，在记录基 $d_\pm=(d_L\pm d_R)/\sqrt2$ 上读取得到各为 $1/2$ 的概率，条件通路态为 $(|L\rangle\pm e^{i\phi}|R\rangle)/\sqrt2$。不按结果分类时，两者平均没有两路干涉。

证明。作用 $\langle d_\pm|$ 得未归一化向量 $(|L\rangle\pm e^{i\phi}|R\rangle)/2$。归一化后，两条件密度矩阵的非对角项在等权平均中抵消。这是量子擦除机制在该接口的计算；参见 Scully–Drühl, [DOI:10.1103/PhysRevA.25.2208](https://doi.org/10.1103/PhysRevA.25.2208)。$\square$

## 6. 落点统计与切面状态恢复

**定义 6.1（占据读数）。** 令 $q_Z(\rho)=(\rho_{xx})_{x\in X}$。此对象是精确概率向量，不是单次样本。

**命题 6.2（固定占据的相位纤维）。** 若概率向量 $p$ 的正支撑大小为 $k\ge1$，满足 $|\psi(x)|^2=p_x$ 的纯态射线构成 $\mathbb T^k/U(1)\cong\mathbb T^{k-1}$。

证明。非零分量为 $\sqrt{p_x}e^{i\theta_x}$，共有 $k$ 个相位；用一个非零分量消去共同相位后余下 $k-1$ 个独立相对相位。零分量不提供相位参数。$\square$

**命题 6.3（配对相干探针的恢复公式）。** 对 $x<y$，令

$$
F^R_{xy}=\frac{(|x\rangle+|y\rangle)(\langle x|+\langle y|)}2,
\qquad
F^I_{xy}=\frac{(|x\rangle-i|y\rangle)(\langle x|+i\langle y|)}2.
$$

取 $r_{xy}=\operatorname{Tr}(\rho F^R_{xy})$、$s_{xy}=\operatorname{Tr}(\rho F^I_{xy})$，则

$$
\operatorname{Re}\rho_{xy}=r_{xy}-\frac{p_x+p_y}{2},
\qquad
\operatorname{Im}\rho_{xy}=s_{xy}-\frac{p_x+p_y}{2}.
$$

证明。展开两个投影的二次型，分别为 $(\rho_{xx}+\rho_{yy})/2+\operatorname{Re}\rho_{xy}$ 与 $(\rho_{xx}+\rho_{yy})/2+\operatorname{Im}\rho_{xy}$。共 $d+2\binom d2=d^2$ 个读数确定所有矩阵元。每个效果可作为二结果测量的一支；它们并未被声明为同一个 POVM 的所有结果。精确读数恢复不等于从同一未知样本无损读出这些概率。$\square$

**命题 6.4（经典占据的恢复障碍）。** 令 $\rho_\pm=|\pm\rangle\langle\pm|$，$\mathcal M_Z(\rho)=\sum_x\rho_{xx}|x\rangle\langle x|$。任何恢复通道 $\mathcal R$ 对 $\rho_+,\rho_-$ 的最坏半迹距离误差至少为 $1/2$。

证明。$\mathcal M_Z(\rho_+)=\mathcal M_Z(\rho_-)$，故两次恢复输出为同一 $\sigma$。两正交输入的半迹距离为一，三角不等式给出

$$
1\le\frac12\|\rho_+-\sigma\|_1+\frac12\|\sigma-\rho_-\|_1.
$$

至少一项不小于 $1/2$。$\square$

## 7. 过程体的输入—输出边界

**定义 7.1（Choi 边界）。** 若被封装过程为通道 $\mathcal E_M:\mathcal L(\mathcal H_A)\to\mathcal L(\mathcal H_B)$，固定输入基并定义非归一化 Choi 算子

$$
J_M=\sum_{i,j}|i\rangle\langle j|\otimes\mathcal E_M(|i\rangle\langle j|).
$$

标准表示参见 Choi, *Completely positive linear maps on complex matrices*, [DOI:10.1016/0024-3795(75)90075-0](https://doi.org/10.1016/0024-3795(75)90075-0)。

**命题 7.2（指定两端口任务的全息充分性）。** 以下等价：$J_M=J_N$；$\mathcal E_M=\mathcal E_N$；对于任意有限参考 $R$、联合输入 $\rho_{RA}$ 和输出效果 $F_{RB}$，两过程的概率相同。恢复公式为

$$
\mathcal E_M(X)=\operatorname{Tr}_A[(X^{\mathsf T}\otimes I)J_M].
$$

证明。$\operatorname{Tr}(X^{\mathsf T}|i\rangle\langle j|)=X_{ij}$，故右侧等于 $\sum_{ij}X_{ij}\mathcal E_M(|i\rangle\langle j|)=\mathcal E_M(X)$。通道相同蕴含所有扩展实验相同。反向取 $d_A^{-1/2}\sum_i|i\rangle_R|i\rangle_A$ 为输入，输出为 $J_M/d_A$。所有效果的迹配对分离 Hermitian 算子，故概率相同推出 Choi 算子相同。$\square$

**命题 7.3（两端口边界不识别内部实现）。** 恒等过程与先作 $V$ 再作 $V^\dagger$ 的过程具有相同两端口通道。若允许中间探针，这一等价可以失效。

证明。整体复合为 $V^\dagger V=I$。取量子比特 $V=X$、输入 $|0\rangle$，在中间读取 $|0\rangle\langle0|$，恒等实现给出概率一，$X$ 实现给出零。相干控制端口也须明确加入任务边界，普通通道数据不确定不同实现间的相对全局相位。$\square$

## 8. 内部观察者与顺序事件

**定义 8.1（带记录的内部策略）。** 当前观察者配置为 $O_h=(C_h,\kappa_h,R_h,P_h)$，设置 $a=\pi(O_h)$。结果分支 $\Phi_{a,y}$ 的概率与正概率后继为

$$
p(y\mid h,a)=\operatorname{Tr}\Phi_{a,y}(\rho_h),
\qquad
\rho_{h(a,y)}=\frac{\Phi_{a,y}(\rho_h)}{p(y\mid h,a)}.
$$

档案追加 $(a,y,\text{来源与钟标定})$。控制、参考和权限的更新属于同一配置转移。策略只能读取当前声明可访问的记录；零概率历史不要求定义条件状态。

**命题 8.2（顺序概率的双表示）。** 对符合策略的有限词 $w=(a_1,y_1)\cdots(a_n,y_n)$，记沿该词选择的分支为 $\Phi_i$，则

$$
p(w)=\operatorname{Tr}[\Phi_n\circ\cdots\circ\Phi_1(\rho_0)]
=\operatorname{Tr}(\rho_0F_w),
\qquad
F_w=\Phi_1^*\circ\cdots\circ\Phi_n^*(I).
$$

证明。正概率前缀的条件概率相乘时，归一化因子逐项抵消。若某前缀概率为零，其未归一化正算子迹为零，故该算子为零，后续分支也为零。最后反复使用迹对偶恒等式 $\operatorname{Tr}[F\Phi(X)]=\operatorname{Tr}[\Phi^*(F)X]$。这个论证只要求沿已指定词的实际分支，不把不同历史下的设置当作同一固定操作。$\square$

## 9. 关系整体的接口组合

**定义 9.1（波体—事件联合切面）。** 关系整体由相干运输、内部钟、局域仪器和记录后继共同给出。波性指振幅及关联的相干组合关系；事件指指定钟条件、仪器设置和结果的联合分支。完整事件边界保留所声明未来任务所需的后继。

**命题 9.2（分层充分性与其失效）。** 定义 9.1 的组合满足：历史编码恢复阶段态；阶段态和指定仪器确定事件律及条件后继；Choi 边界恢复指定两端口过程；但钟标签、占据统计和单次点击各自均不一般恢复完整相干过程。

证明。前三项分别用命题 3.2、4.2、7.2。后三项分别由命题 3.3、6.2—6.4、4.3 和 7.3 的成对实现否定相应充分性。所有比较保持同一声明任务；扩大允许探针后重新判定边界。$\square$

## 10. 局部边缘与完整记忆

**命题 10.1（同边缘、异未来的共同过程）。** 存在同一系统—环境操作，使两种来源具有相同的系统与环境边缘，却在同一后续操作下产生正交的系统输出。

证明。取量子比特 $S,E$，$\rho_\pm=|\pm\rangle\langle\pm|$、$\omega_E=I/2$，并令

$$
U=I_S\otimes|0\rangle\langle0|_E+Z_S\otimes|1\rangle\langle1|_E.
$$

输入 $\rho_\pm\otimes\omega_E$ 后的中间态为

$$
\chi_\pm=\tfrac12\rho_\pm\otimes|0\rangle\langle0|
+\tfrac12\rho_\mp\otimes|1\rangle\langle1|.
$$

两边缘均为 $I/2$；但 $U^2=I$，再作用同一 $U$ 后恢复 $\rho_\pm\otimes I/2$。检验 $\rho_+$ 分别给出概率一与零。区别由联合关联携带。带记忆过程的操作性框架参见 Pollock 等，*Non-Markovian quantum processes: complete framework and efficient characterisation*, [arXiv:1512.00589](https://arxiv.org/abs/1512.00589)。本命题只使用给出的两比特构造。$\square$

## 11. 首次探测协议

**定义 11.1（固定单 Kraus 未点击接口）。** 令 $\dim\mathcal H=d\ge1$，固定

$$
Q^\dagger Q+\sum_xL_x^\dagger L_x=I.
$$

每轮未点击则继续，首次点击则记录轮数、端口并停止。定义

$$
K_{n,x}=L_xQ^{n-1},\qquad E_{n,x}=K_{n,x}^\dagger K_{n,x},
\qquad S_N=(Q^\dagger)^NQ^N,
\qquad S_0=I.
$$

$Q$ 包含传播和未点击更新，轮次不自动等于秒。首次探测的重复测量框架参见 Friedman–Kessler–Barkai, *Quantum walks: The first detected passage time problem*, [DOI:10.1103/PhysRevE.95.032141](https://doi.org/10.1103/PhysRevE.95.032141)；这里以下述逐项计算固定实际使用的合同。

**命题 11.2（有限事件概率分解）。** 对每个 $N\ge1$，

$$
\sum_{n=1}^N\sum_xE_{n,x}+S_N=I.
$$

因而 $p(n,x)=\operatorname{Tr}(\rho E_{n,x})$ 与 $s_N=\operatorname{Tr}(\rho S_N)$ 满足总和为一。

证明。$\sum_xE_{n,x}=S_{n-1}-S_n$，对 $n$ 求和后取迹。$\square$

**命题 11.3（未点击的条件后继）。** 若 $s_N>0$，未点击后状态为 $Q^N\rho(Q^\dagger)^N/s_N$。

证明。连续应用未点击分支并归一化。该状态一般不等于删除探测器后的自由演化状态，因 $Q$ 已含实际探测操作。$\square$

## 12. 首次事件的静态表示

**定义 12.1（带停止标签的关系编码）。** 对固定 $N$，取正交标签 $|\varnothing_N\rangle$ 和 $|n,x\rangle$，令

$$
\mathcal W_N\psi=|\varnothing_N\rangle\otimes Q^N\psi
+\sum_{n=1}^N\sum_x|n,x\rangle\otimes L_xQ^{n-1}\psi.
$$

**命题 12.2（事件时间的等距编码）。** $\mathcal W_N^\dagger\mathcal W_N=I$；读取标签得到命题 11.2 的概率及相应分支后继。

证明。标签正交使伴随乘积为 $S_N+\sum_{n,x}E_{n,x}=I$。第 $(n,x)$ 块为 $K_{n,x}\rho K_{n,x}^\dagger$，未点击块为 $Q^N\rho(Q^\dagger)^N$。编码中的时间权重由仪器决定，不是命题 3.2 的均匀历史权重；记录空间随 $N$ 增长，不由有限维系统自动提供无限个正交原始时间标签。$\square$

## 13. 单 Kraus 暗空间与等待界

**定义 13.1（协议暗空间）。** 令

$$
\mathcal D=\bigcap_{n\ge0,x}\ker(L_xQ^n),
\qquad G_d=I-(Q^\dagger)^dQ^d.
$$

**命题 13.2（暗空间的有限代数判定）。** $\mathcal D=\ker G_d$。

证明。由命题 11.2，$\langle\psi,G_d\psi\rangle=\sum_{n=0}^{d-1}\sum_x\|L_xQ^n\psi\|^2$。其为零等价于这些项全零。Cayley–Hamilton 定理使所有更高 $Q$ 次幂由前 $d$ 个生成，故全部后续点击振幅为零。此为已知模型的代数判定，不是从 $d$ 次未点击样本推断永久暗。$\square$

**命题 13.3（单 Kraus 生存极限）。** 设 $P_{\mathcal D}$ 为正交投影，则

$$
S_N\longrightarrow P_{\mathcal D},
\qquad p(\text{永不点击})=\operatorname{Tr}(\rho P_{\mathcal D}).
$$

证明。$Q\mathcal D\subseteq\mathcal D$，且对 $u\in\mathcal D$ 有 $Q^\dagger Qu=u$，故 $Q|_{\mathcal D}$ 为有限维酉映射。若 $y\perp\mathcal D$、$x=Qu\in\mathcal D$，则 $\langle x,Qy\rangle=\langle u,y\rangle=0$；所以 $\mathcal D^\perp$ 也不变。若该补空间非零，$G_d$ 在其上正定，最小本征值 $g>0$，从而 $\|Q^d|_{\mathcal D^\perp}\|^2=1-g<1$。补空间分量逐块趋零，暗分量保持范数，得算子极限。全暗情形直接成立。$\square$

**命题 13.4（暗权重之外的尾界）。** 在命题 13.3 的非零补空间情形，

$$
0\le s_{md}-\operatorname{Tr}(\rho P_{\mathcal D})
\le(1-g)^m\operatorname{Tr}(\rho P_{\mathcal D^\perp}).
$$

若初态支撑于 $\mathcal D^\perp$，首次点击轮数 $\mathsf N$ 满足 $\mathbb E\mathsf N\le d/g$。

证明。第一式由分块收缩得到。对取值于正整数的等待时间，$\mathbb E\mathsf N=\sum_{N\ge0}s_N$，按长度 $d$ 分块，以 $d\sum_{m\ge0}(1-g)^m=d/g$ 控制。$\square$

**命题 13.5（相干相消导致协议暗方向）。** 令 $B=(L+R)/\sqrt2$、$D=(L-R)/\sqrt2$，取 $Q=|D\rangle\langle D|$、单点击算子 $L_{\rm c}=|B\rangle\langle B|$。输入 $|L\rangle$ 或 $|R\rangle$ 的首轮点击概率均为 $1/2$，输入 $B$ 则立即点击，输入 $D$ 则永不点击。

证明。两个投影正交且和为 $I$；计算其对四个向量的作用即可。$\square$

## 14. 事件统计的观察商

**定义 14.1（事件效果空间）。** 在实空间 $\operatorname{Herm}(\mathcal H)$ 上使用迹内积，令

$$
\mathcal V_N=\operatorname{span}_{\mathbb R}\bigl(\{I\}\cup\{E_{n,x}:1\le n\le N\}\bigr),
\qquad \mathcal V_\infty=\bigcup_{N\ge1}\mathcal V_N.
$$

**命题 14.2（事件律的精确残余）。** 两初态具有相同的全部首次点击分布和永不点击概率，当且仅当 $\rho-\sigma\in\mathcal V_\infty^\perp$。

证明。各有限事件概率差为 $\operatorname{Tr}[(\rho-\sigma)E_{n,x}]$；恒等元的配对因两态迹相同而为零。永不点击概率为一减去全部有限事件概率之和。$\square$

**命题 14.3（已知固定模型的有限效果闭包）。** 存在 $1\le N_*\le d^2$，使所有 $N\ge N_*$ 满足 $\mathcal V_N=\mathcal V_\infty$。

证明。置 $\mathcal A(F)=Q^\dagger FQ$。有 $\mathcal A(E_{n,x})=E_{n+1,x}$ 与 $\mathcal A(I)=I-\sum_xE_{1,x}$。若某 $N\ge1$ 有 $\mathcal V_{N+1}=\mathcal V_N$，则 $\mathcal A(\mathcal V_N)\subseteq\mathcal V_N$，以后稳定。空间总维度为 $d^2$，而 $\dim\mathcal V_1\ge1$，不可能发生 $d^2$ 次连续严格增长。此为精确模型的有限闭包，不是未知装置的有限样本识别。$\square$

**命题 14.4（所有态的可识别性判据）。** 完整事件律唯一确定任意密度矩阵，当且仅当 $\mathcal V_\infty=\operatorname{Herm}(\mathcal H)$。

证明。充分性由命题 14.2。若空间真小，取非零 $\Delta\in\mathcal V_\infty^\perp$；因 $I\in\mathcal V_\infty$，$\operatorname{Tr}\Delta=0$。充分小的 $a>0$ 使 $I/d\pm a\Delta$ 为不同密度矩阵，而事件律相同。$\square$

**命题 14.5（必然探测而无态区分）。** 取 $0<\gamma<1$、$Q=\sqrt{1-\gamma}I$、$L=\sqrt\gamma I$。每态的首次点击律均为 $\gamma(1-\gamma)^{n-1}$，最终点击概率为一，而 $\mathcal V_\infty=\mathbb RI$。

证明。$E_n=\gamma(1-\gamma)^{n-1}I$。所有统计独立于输入，但点击后的量子态仍是输入态。继续测量后继扩大了原来的纯事件记录任务。$\square$

## 15. 经典合并与相干读取

**命题 15.1（经典标签合并）。** 对正交记录下的分支 $K_j$，将已读标签仅保留为“$j\in A$”时，条件分支为 $\Phi_A(\rho)=\sum_{j\in A}K_j\rho K_j^\dagger$，效果为 $\sum_{j\in A}K_j^\dagger K_j$。

证明。对已区分的记录求部分迹会消去不同标签的交叉项，故不能一般替换成 $(\sum_jK_j)\rho(\sum_jK_j)^\dagger$。$\square$

**命题 15.2（相干记录检验与不可访问副本）。** 若实际可相干访问记录，检验归一化 $\chi=\sum_jc_j|j\rangle$ 得到分支算子 $K_\chi=\sum_j\overline{c_j}K_j$。若联合编码还含归一化环境记录 $e_j$，忽略环境后的分支改为

$$
\Phi_\chi(\rho)=\sum_{j,k}\overline{c_j}c_k
\langle e_k|e_j\rangle K_j\rho K_k^\dagger.
$$

证明。对 $\sum_j|j\rangle\otimes K_j\psi\otimes e_j$ 作用 $\langle\chi|$，再对环境求迹。环境副本正交时交叉项消失。这个操作要求对实际记录及相应相位参考的访问，单纯忘记标签不满足该前提。$\square$

## 16. 表示细分与实际探测细分

**定义 16.1（二态投影监测）。** 固定 $\omega\ne0$，$U_\delta=e^{-i\omega\delta X}$、$P_j=|j\rangle\langle j|$，$Q_\delta=P_0U_\delta$、$L_\delta=P_1U_\delta$，初态为 $|0\rangle$。每轮历时 $\delta>0$。此为理想 Zeno 模型；标准机制见 Misra–Sudarshan, [DOI:10.1063/1.523304](https://doi.org/10.1063/1.523304)。

**命题 16.2（首次点击与固定历时极限）。** 有

$$
p_\delta(n)=\sin^2(\omega\delta)\cos^{2(n-1)}(\omega\delta),
\qquad s_\delta(N)=\cos^{2N}(\omega\delta).
$$

固定 $T>0$ 时，$s_{T/N}(N)\to1$。

证明。$Q_\delta|0\rangle=\cos(\omega\delta)|0\rangle$，点击振幅为 $-i\sin(\omega\delta)\cos^{n-1}(\omega\delta)|1\rangle$。又

$$
1\ge\bigl[1-\sin^2(\omega T/N)\bigr]^N
\ge1-N\sin^2(\omega T/N)
\ge1-\omega^2T^2/N.
$$

夹逼得到极限。$\square$

**命题 16.3（两个细分协议不等价）。** 中间不测量而只在 $T$ 探测，点击概率为 $\sin^2(\omega T)$；每隔 $T/N$ 实际探测，则截至 $T$ 的首次点击概率为 $1-\cos^{2N}(\omega T/N)\to0$。

证明。前者由 $U_{T/N}^N=U_T$；后者由命题 16.2。前者只有表示细分，后者增加了分支更新。$\square$

**命题 16.4（最终发生与平均历时）。** 若 $0<|\omega|\delta<\pi/2$，则最终点击概率为一，且

$$
\mathbb E\mathsf N=\frac1{\sin^2(\omega\delta)},
\qquad
\mathbb E\mathsf T=\frac\delta{\sin^2(\omega\delta)}
\sim\frac1{\omega^2\delta}\quad(\delta\downarrow0).
$$

证明。对几何分布求和并用 $\sin u\sim u$。极限描述协议的等待时间，不推出物理钟的单位长度改变。$\square$

## 17. 首次事件关系体

**定义 17.1（固定协议的关系数据）。** 令

$$
\mathfrak Q=(\mathcal H,\rho_0,Q,\{L_x\},\text{记录接口},\text{允许控制},\text{钟标定}).
$$

固定这些数据后，暗空间 $\mathcal D$ 描述永久无点击的初始方向，$\mathcal V_\infty^\perp$ 描述全部事件统计不能区分的状态差。二者分别位于向量空间与算子空间。

**命题 17.2（两种不可见性不能混同）。** $\mathcal D=\{0\}$ 不蕴含 $\mathcal V_\infty^\perp=\{0\}$；局域结果已经出现也不蕴含中间路线可辨或输入态可恢复。

证明。命题 14.5 在 $d\ge2$ 时满足第一断言的反例条件。后两项由命题 5.2—5.4 的不可分路线记录与命题 6.4 的同统计异态分别得到。$\square$

## 追加锚（本行以下为增补区）

## 18. 不可读分支与非投影生存边界

**定义 18.1（一般未点击仪器）。** 用完全正映射

$$
\mathcal N(X)=\sum_{\alpha}Q_\alpha XQ_\alpha^\dagger,
\qquad
\mathcal C_x(X)=\sum_\beta L_{x\beta}XL_{x\beta}^\dagger
$$

分别表示未点击和可读结果 $x$，并要求

$$
\sum_\alpha Q_\alpha^\dagger Q_\alpha+
\sum_{x,\beta}L_{x\beta}^\dagger L_{x\beta}=I.
$$

实际记录只读出“未点击”或 $x$，不自动包含 $\alpha,\beta$。同一映射的不同 Kraus 表示给出同一统计与后继。设 $\mathcal A=\mathcal N^*$，$B_x=\mathcal C_x^*(I)$，并定义

$$
E_{n,x}=\mathcal A^{n-1}(B_x),
\qquad S_N=\mathcal A^N(I),\qquad S_0=I.
$$

有限维完全正映射的可达性与不变子空间方法参见 Ying、Feng、Yu、Ying, *Reachability Probabilities of Quantum Markov Chains*, [DOI:10.1007/978-3-642-40184-8_24](https://doi.org/10.1007/978-3-642-40184-8_24)。以下把这些算子工具用于本卷的首次事件与后继接口，保留一般仪器和单 Kraus 模型的区别。

**定理 18.2（仪器商下的首次事件与最大固定效果）。** 定义 18.1 的可读首次事件概率为

$$
p(n,x)=\operatorname{Tr}[\mathcal C_x\mathcal N^{n-1}(\rho)]
=\operatorname{Tr}(\rho E_{n,x}).
$$

有限分解仍满足 $\sum_{n=1}^N\sum_xE_{n,x}+S_N=I$。算子列 $S_N$ 单调下降并在范数下收敛到 $F$，其中

$$
0\le F\le I,\qquad \mathcal A(F)=F,
\qquad p(\text{永不点击})=\operatorname{Tr}(\rho F).
$$

$F$ 是所有满足 $0\le H\le I$、$\mathcal A(H)=H$ 的效果中最大的一个；它不依赖 Kraus 表示。

证明。迹对偶给出首式。由 $\sum_xB_x=I-\mathcal A(I)$，

$$
\sum_xE_{n,x}=S_{n-1}-S_n.
$$

$\mathcal A$ 为正映射且 $\mathcal A(I)\le I$，故 $0\le S_{N+1}\le S_N\le I$。有限维中，各向量二次型的单调极限经极化确定唯一 Hermitian 算子 $F$，矩阵元收敛等价于范数收敛。连续性给出 $\mathcal A(F)=F$。未点击事件随 $N$ 递减，其交为永久无点击事件，概率的从上连续性给出迹公式。若 $H$ 为上述固定效果，则 $H=\mathcal A^N(H)\le\mathcal A^N(I)=S_N$，取极限得 $H\le F$。全部公式仅取决于映射，故对 Kraus 表示不变。$\square$

**定理 18.3（永久暗方向与流入暗区的概率不同）。** 对任意 $0<a<1$，存在二维仪器，其永久无点击效果为

$$
F=|0\rangle\langle0|+a|1\rangle\langle1|,
$$

因而 $F^2\ne F$；其确定永不点击的纯态方向却仅为 $\mathbb C|0\rangle$。

证明。取

$$
Q_1=|0\rangle\langle0|,
\quad Q_2=\sqrt a\,|0\rangle\langle1|,
\quad L=\sqrt{1-a}\,|1\rangle\langle1|.
$$

完备性由 $Q_1^\dagger Q_1+Q_2^\dagger Q_2+L^\dagger L=I$ 得到。对任意 $X$，

$$
\mathcal N(X)=(X_{00}+aX_{11})|0\rangle\langle0|.
$$

一次未点击即进入永不点击的 $|0\rangle$，故 $S_N=F$ 对所有 $N\ge1$ 成立。输入 $|1\rangle$ 时，以概率 $1-a$ 首轮点击，以概率 $a$ 进入暗区；初态的暗空间投影权重为零，永不点击概率却为 $a$。归一化向量的 $F$ 期望等于一当且仅当其 $|1\rangle$ 分量为零。$\square$

**定义 18.4（一般仪器的确定暗空间）。** 令 $\mathcal D_0=\mathcal H$，递归定义

$$
\mathcal D_{n+1}=
\left(\bigcap_{x,\beta}\ker L_{x\beta}\right)
\cap\left(\bigcap_\alpha Q_\alpha^{-1}(\mathcal D_n)\right).
$$

它要求当前点击振幅为零，且每个不可读未点击分支仍进入下一层暗方向。

**定理 18.5（一般仪器暗方向的有限闭合）。** 若 $d=\dim\mathcal H$，则

$$
\mathcal D_n=\ker(I-S_n),\qquad
\mathcal D_d=\mathcal D_{d+1}=\cdots
=\ker(I-F)=:\mathcal D.
$$

$\mathcal D$ 是所有点击 Kraus 算子为零且对全部 $Q_\alpha$ 不变的最大子空间。该空间的定义与结论均不依赖所选 Kraus 表示。

证明。$I-S_n$ 是前 $n$ 轮全部可读点击效果之和。将 $\mathcal N^k$ 展开为所有 $Q$ 词的 Kraus 和后，

$$
\langle\psi,(I-S_n)\psi\rangle
=\sum_{k=0}^{n-1}\sum_{x,\beta}\sum_{\alpha_1,\ldots,\alpha_k}
\|L_{x\beta}Q_{\alpha_k}\cdots Q_{\alpha_1}\psi\|^2.
$$

非负和为零等价于这些向量全部为零，正好给出递归式。子空间列递减；若 $\mathcal D_{n+1}=\mathcal D_n$，则该空间已由递归式保持不变，以后恒定。若在前 $d$ 次都严格缩小，则 $\mathcal D_d=\{0\}$，也已稳定。因而至多 $d$ 轮闭合。$I-S_n\uparrow I-F$，其共同核等于 $\ker(I-F)$。任何满足所述不变条件的子空间都包含于全部 $\mathcal D_n$；反向由稳定递归得到。最后 $\ker(I-S_n)$ 与 $\ker(I-F)$ 是映射本身的对象，故 Kraus 表示不改变它们。$\square$

**定理 18.6（没有确定暗方向等价于所有态最终点击）。** 定义 18.1 下，下列条件等价：$\mathcal D=\{0\}$；$F=0$；$I-\mathcal A^d(I)$ 正定；每个初态最终点击概率为一。

证明。有限核判据给出第一与第三项等价；第二与第四项由迹分离得到。$F=0$ 显然推出 $\mathcal D=0$。反之若 $F\ne0$，令 $\lambda=\|F\|>0$，$M$ 为其最大本征空间。对单位 $v\in M$，

$$
\lambda=\sum_\alpha\langle Q_\alpha v,FQ_\alpha v\rangle
\le\lambda\sum_\alpha\|Q_\alpha v\|^2\le\lambda.
$$

等号迫使所有点击振幅为零，并使每个 $Q_\alpha v$ 属于 $M$。所以 $M$ 是非零不变暗子空间，包含于 $\mathcal D$。矛盾。该论证也表明非零 $F$ 必有本征值一，但其其他本征值不必为零；定理 18.3 给出后一情形。$\square$

## 19. 扣除永久尾项的条件等待算子

**定义 19.1（最终点击效果与剩余尾项）。** 对第 18 节的仪器，令

$$
R=I-F,\qquad R_n=S_n-F=\mathcal A^n(R),
\qquad r_\rho=\operatorname{Tr}(\rho R).
$$

$r_\rho$ 是最终点击概率；$\operatorname{Tr}(\rho R_n)$ 是“前 $n$ 轮未点击但以后会点击”的概率。后者为概率事件的差，不要求在第 $n$ 轮已经识别哪些未点击样本将永久无点击。

**定理 19.2（有限维剩余尾项的统一收缩）。** 若 $R\ne0$，存在整数 $M\ge1$ 和 $0<q<1$，使

$$
R_M\le qR,\qquad
0\le R_n\le q^{\lfloor n/M\rfloor}R.
$$

因此范数收敛的算子级数

$$
T=\sum_{n=0}^{\infty}R_n
$$

满足

$$
0\le T\le\frac M{1-q}R,
\qquad T-\mathcal A(T)=R.
$$

证明。$0\le R_n\le R$ 且 $R_n\to0$。正算子被 $R$ 控制时，其核包含 $\ker R$，所以可限制到 $P=\operatorname{supp}R$。在该空间 $R^{-1/2}$ 有界，$R^{-1/2}R_nR^{-1/2}\to0$。选 $M$ 使其范数小于某个 $q<1$，得到第一式。正性与 $R_n=\mathcal A^nR$ 推出 $R_{kM}\le q^kR$；对 $0\le j<M$，再用 $\mathcal A^jR\le R$ 得到第二式。按块求和得 $T$ 的界，逐项移位得方程。若 $R=0$，所有 $R_n$ 与 $T$ 均为零。$\square$

**定理 19.3（条件等待时间与唯一瞬态解）。** 若 $r_\rho>0$，首次点击轮数在最终点击条件下满足

$$
\mathbb P(\mathsf N>n\mid\mathsf N<\infty)
=\frac{\operatorname{Tr}(\rho R_n)}{r_\rho},
\qquad
\mathbb E[\mathsf N\mid\mathsf N<\infty]
=\frac{\operatorname{Tr}(\rho T)}{r_\rho}
\le\frac M{1-q}.
$$

$T$ 是满足 $X-\mathcal A(X)=R$ 且 $0\le X\le cR$ 对某有限 $c$ 成立的唯一算子。此支撑与有界性条件不能直接删去。

证明。第 19.1 条识别分子事件；对条件分布使用尾和公式并交换非负和与迹即得期望。若 $X$ 是所述解，则

$$
X=\sum_{n=0}^{k-1}\mathcal A^nR+\mathcal A^kX,
\qquad 0\le\mathcal A^kX\le cR_k\longrightarrow0,
$$

故 $X=T$。若存在非零固定效果 $F$，$T+bF$ 对 $b>0$ 也满足同一方程，却不满足被 $R$ 控制的条件，因为 $F$ 在 $\mathcal D$ 上为恒等、$R$ 在其上为零。$\square$

**定理 19.4（有限截断的条件尾和误差）。** 对 $k\ge0$，

$$
0\le T-\sum_{n=0}^{kM-1}R_n
\le\frac{Mq^k}{1-q}R.
$$

因此用前 $kM$ 项计算条件期望时，任意 $r_\rho>0$ 的来源都具有误差至多 $Mq^k/(1-q)$。

证明。按 $M$ 项分块，余项被 $M\sum_{j=k}^{\infty}q^jR$ 控制，随后取迹并除以 $r_\rho$。这里的统一界需要已知仪器以及有效的 $F,M,q$；有限次数无点击样本不能代替这份算子不等式。$\square$

## 20. 事件统计成为动态边界的充要条件

**定义 20.1（一般仪器的事件边界坐标）。** 令

$$
\mathcal V=\operatorname{span}_{\mathbb R}\{I,\mathcal A^nB_x:n\ge0,x\},
\qquad
b_\rho(H)=\operatorname{Tr}(\rho H)\quad(H\in\mathcal V).
$$

来源类为全部密度矩阵。$b_\rho$ 是 $\mathcal V$ 上的实线性泛函，其可实现集合为全部状态限制到 $\mathcal V$ 的像。

**定理 20.2（未点击预测的精确闭合）。** 一般仪器的效果空间在至多 $d^2$ 层后稳定。全部首次事件律相同等价于 $b_\rho=b_\sigma$。此外 $\mathcal A(\mathcal V)\subseteq\mathcal V$，若 $p_0=b_\rho(\mathcal A I)>0$，则未点击后

$$
b_{\rho'}(H)=\frac{b_\rho(\mathcal A H)}{p_0},
\qquad \rho'=\mathcal N(\rho)/p_0.
$$

因而事件边界足以递归预测同一停止协议的全部未点击续接。

证明。命题 14.2—14.3 的线性论证只用了 $\mathcal A$ 的线性、$\mathcal A(I)=I-\sum_xB_x$ 和 $E_{n+1,x}=\mathcal A(E_{n,x})$，故逐项适用。剩余公式由迹对偶得到；分母是已知边界坐标，零分支无需定义条件后继。由于协议首次点击即停止，本断言不要求预测点击后的额外实验。$\square$

**定理 20.3（点击后继续观察的精确桥梁）。** 给定任意实线性空间 $\mathcal W\subseteq\operatorname{Herm}(\mathcal H)$ 和一支 $\mathcal C_x$。对所有具有相同 $b_\rho$ 的初态，只要该结果概率为正，其归一化后继在 $\mathcal W$ 上具有相同期望，当且仅当

$$
\mathcal C_x^*(\mathcal W)\subseteq\mathcal V.
$$

证明。$p_x=\operatorname{Tr}(\rho B_x)$ 已由 $b_\rho$ 确定。若所示包含成立，则每个 $H\in\mathcal W$ 的条件期望为 $b_\rho(\mathcal C_x^*H)/p_x$，故充分。反之若某 $H$ 的拉回 $D=\mathcal C_x^*H$ 不在 $\mathcal V$，取其在 $\mathcal V^\perp$ 上的非零正交投影 $\Delta$。则 $\operatorname{Tr}\Delta=0$，$\operatorname{Tr}(\Delta D)=\|\Delta\|_2^2>0$。充分小的 $\varepsilon>0$ 使

$$
\rho_\pm=I/d\pm\varepsilon\Delta
$$

都是满秩状态且具有相同边界。$D\ne0$ 意味着 $\mathcal C_x\ne0$，故正效果 $B_x\ne0$，两态的共同结果概率 $\operatorname{Tr}(B_x)/d>0$。两分支期望之差为 $2\varepsilon\|\Delta\|_2^2/p_x\ne0$，与假设矛盾。若 $B_x=0$，完全正性给出该分支为零，包含关系自动成立。$\square$

**定理 20.4（停止任务充分，继续任务不充分的同一仪器）。** 在命题 14.5 的仪器中，$\mathcal V=\mathbb RI$ 对全部首次点击律充分，但对点击后的模式测试不充分。

证明。取 $d=2$、$H=|0\rangle\langle0|$，有 $\mathcal C^*H=\gamma H\notin\mathbb RI$。初态 $|0\rangle$ 和 $|1\rangle$ 的首次事件律完全相同，点击后分别仍为这两个正交态；随后检验 $H$ 得概率一与零。定理 20.3 正好识别缺失的拉回方向。$\square$

**定义 20.5（续接任务的最小闭合效果空间）。** 给定有限族允许分支 $\{\Phi_j\}$，所有操作对全部状态合法，相关记录与设置均可读。从需保留的效果空间 $\mathcal Z_0\supseteq\mathbb RI$ 出发定义

$$
\mathcal Z_{k+1}=\operatorname{span}_{\mathbb R}
\left(\mathcal Z_k\cup\bigcup_j\Phi_j^*(\mathcal Z_k)\right).
$$

定义中的边界载体是状态限制到效果空间的实际像；不把任意坐标组合都视为可实现状态。线性闭合不要求效果空间对算子乘法闭合，也不在此指定较小 Hilbert 空间上的量子通道实现。

**定理 20.6（有限闭合与内部策略的动态充分性）。** 若 $r=\dim\mathcal Z_0$，则 $\mathcal Z_{d^2-r}$ 已稳定，并等于包含 $\mathcal Z_0$、对全部分支对偶不变的最小实线性空间。其状态限制坐标与实际可读历史一起，确定所有有限合法续接词的概率和条件后继坐标；允许根据已有记录选择操作时同样成立。

证明。一次相等便对所有 $\Phi_j^*$ 闭合，之后不再增长；若前 $d^2-r$ 步都严格增长，空间已满维，因而稳定。归纳表明每个后继候选空间包含 $\mathcal Z_k$，得最小性。对每个分支，概率由 $\Phi_j^*I$ 给出，后继坐标由 $H\mapsto b_\rho(\Phi_j^*H)/b_\rho(\Phi_j^*I)$ 给出。对结果树归纳即可处理依赖历史的选择。若合法性另依赖权限、未包含的记忆或不可读设置，则必须把这些数据加入配置，单独的效果空间不能替代它们。$\square$

## 21. 有限接收器、时间模糊与观察纤维

**定义 21.1（有限时限的实际记录）。** 运行一般仪器至第 $N$ 轮，得到有限 POVM

$$
\mathsf P_N=\{E_{n,x}:1\le n\le N\}\cup\{S_N\}.
$$

最后一个结果仅表示截至 $N$ 未点击。记其效果实张成为 $\mathcal U_N$，则由完备性，$\mathcal U_N=\mathcal V_N$。此装置不区分“以后会点击”和“永不点击”。

**定理 21.2（有限接收器的精确模型可识别性）。** 若全部事件统计在全部密度矩阵上可识别，则存在 $N\le d^2$ 使有限记录 $\mathsf P_N$ 也可识别。反之，任一这样的有限记录可识别都蕴含完整事件律可识别。

证明。定理 20.2 给出 $\mathcal V_{d^2}=\mathcal V$；可识别性由该空间是否为全部 Hermitian 空间判定。有限记录是完整记录的确定性粗粒化，故反向成立。这里要求精确概率和已知固定仪器；结论不把一次长度 $N$ 的运行变为对任意未知态的精确重建。$\square$

**定义 21.3（经典时间读出通道）。** 对有限效果族 $H_j$，令 $T_{zj}\ge0$ 且 $\sum_zT_{zj}=1$。仪器已经产生 $j$ 后，记录接口仅输出 $z$，新效果为

$$
\overline H_z=\sum_jT_{zj}H_j.
$$

这表示既有记录上的随机模糊或重新标记，不改变物理探测间隔和分支后继。

**定理 21.4（时间模糊不损失态区分的充要条件）。** 在全部密度矩阵来源类上，模糊前后记录诱导相同的不可区分关系，当且仅当

$$
\operatorname{span}_{\mathbb R}\{\overline H_z\}
=\operatorname{span}_{\mathbb R}\{H_j\}.
$$

证明。左侧空间包含于右侧。相等时全部效果期望互相线性确定，纤维相同。若严格包含，取属于右侧且正交于左侧的非零 $\Delta$；因为两空间均包含 $I$，它迹为零。$I/d\pm\varepsilon\Delta$ 对充分小的 $\varepsilon$ 为密度矩阵，新读数相同，旧读数至少有一项不同。这证明纤维扩大。上述线性恢复只针对已知效果的精确统计，不保证存在从 $z$ 模拟 $j$ 的状态无关随机逆，也不保证误差或样本成本相等。$\square$

**定理 21.5（有限时限造成的统计距离损失）。** 设 $P_\rho,P_\sigma$ 为完整首次事件分布，结果集含永不点击标签；$P_\rho^{(N)},P_\sigma^{(N)}$ 为只保留 $\mathsf P_N$ 的分布。则

$$
0\le\operatorname{TV}(P_\rho,P_\sigma)
-\operatorname{TV}(P_\rho^{(N)},P_\sigma^{(N)})
\le\min\{\operatorname{Tr}(\rho S_N),\operatorname{Tr}(\sigma S_N)\}.
$$

若两来源均满足 $\operatorname{Tr}(\rho F)=\operatorname{Tr}(\sigma F)=0$，可进一步用定理 19.2 的 $q^{\lfloor N/M\rfloor}$ 控制右侧。

证明。前 $N$ 轮坐标不变。令被合并尾部的两族质量为 $a_j,b_j$，总量为 $a,b$，则距离损失恰为

$$
\frac12\left(\sum_j|a_j-b_j|-|a-b|\right).
$$

三角不等式给非负；$\sum_j|a_j-b_j|\le a+b$ 给上界 $(a+b-|a-b|)/2=\min(a,b)$。当永久无点击权重为零，$s_N=\operatorname{Tr}(\rho R_N)$，可使用剩余尾界。若这些权重不为零，不能把有限时限记录中的 $S_N$ 直接替换成 $R_N$。$\square$

## 22. 从精确恢复到有误差的关系重建

**定义 22.1（有限记录的恢复常数）。** 设 $d\ge2$，固定有限 POVM $\{H_j\}_{j=1}^J$，定义

$$
\mathsf M(\Delta)=(\operatorname{Tr}(\Delta H_j))_{j=1}^J,
\qquad
\alpha=\min_{\substack{\Delta=\Delta^\dagger,\ \operatorname{Tr}\Delta=0\\\|\Delta\|_2=1}}
\|\mathsf M(\Delta)\|_{\ell^2}.
$$

$\|\cdot\|_2$ 为 Hilbert–Schmidt 范数。$\alpha$ 依赖所用记录坐标与噪声范数，单独比较不同粗粒化前后的 $\alpha$ 不构成信息增减的判据。

**定理 22.2（稳定恢复与残余误差下界）。** 以下条件等价：$\alpha>0$；效果张成全部 Hermitian 空间；该 POVM 在全部密度矩阵上可识别。此时

$$
\frac12\|\rho-\sigma\|_1
\le\frac{\sqrt d}{2\alpha}\|\mathsf M(\rho)-\mathsf M(\sigma)\|_{\ell^2}.
$$

若 $\alpha=0$，则存在两不同状态具有完全相同记录，且任何只读取该记录概率向量的恢复法对其中一态的半迹距离误差至少为两态半迹距离的一半。

证明。迹零 Hermitian 单位球紧，故 $\alpha>0$ 等价于 $\mathsf M$ 在该空间的核为零。POVM 完备性使 $I$ 属于效果张成，因而该核为零等价于满张成。对 $\Delta=\rho-\sigma$ 使用 $\|\Delta\|_1\le\sqrt d\|\Delta\|_2$ 与 $\|\mathsf M\Delta\|_{\ell^2}\ge\alpha\|\Delta\|_2$ 得到上界。若核非零，取 $\rho_\pm=I/d\pm a\Delta$，任意相同输入的恢复输出相同，由三角不等式得到下界。$\square$

**定理 22.3（重复准备下的有限样本保证）。** 假定可以独立同分布地准备同一未知 $\rho$，每份样本运行同一有限记录 POVM。令 $m$ 次结果频率为 $\widehat p$，$\widehat\rho$ 为全部密度矩阵中使 $\|\mathsf M(\tau)-\widehat p\|_{\ell^2}$ 最小的一个。若 $\alpha>0$，则对 $0<\delta<1$，以至少 $1-\delta$ 的概率，

$$
\frac12\|\widehat\rho-\rho\|_1
\le\frac{\sqrt{dJ}}{\alpha}
\sqrt{\frac{\log(2J/\delta)}{2m}}.
$$

证明。状态集紧，所以极小值存在。对每个结果的指示变量应用 Hoeffding 不等式，再取 $J$ 项并集界，以概率至少 $1-\delta$ 有每个坐标误差不超过 $\varepsilon=\sqrt{\log(2J/\delta)/(2m)}$。故 $\|\widehat p-\mathsf M\rho\|_{\ell^2}\le\sqrt J\varepsilon$。极小性给出 $\|\mathsf M\widehat\rho-\widehat p\|_{\ell^2}\le\sqrt J\varepsilon$，三角不等式及定理 22.2 得结论。所用集中界参见 Hoeffding, *Probability Inequalities for Sums of Bounded Random Variables*, [DOI:10.1080/01621459.1963.10500830](https://doi.org/10.1080/01621459.1963.10500830)。若 $H_j$ 来自 $N$ 轮时限协议，每份准备至多运行 $N$ 轮；其历时仍需逐轮钟标定。$\square$

**定理 22.4（可识别性不提供统一精度成本）。** 固定任一信息完备 POVM $\{H_j\}$ 和 $0<\gamma<1$，构造一般仪器

$$
\mathcal N(X)=(1-\gamma)X,
\qquad
\mathcal C_j(X)=\gamma\sqrt{H_j}\,X\sqrt{H_j}.
$$

它没有永久暗方向，最终端口分布为 $\operatorname{Tr}(\rho H_j)$；但固定时限 $N$ 内两态记录的总变差恰为

$$
\bigl[1-(1-\gamma)^N\bigr]
\operatorname{TV}\bigl((\operatorname{Tr}\rho H_j)_j,(\operatorname{Tr}\sigma H_j)_j\bigr),
$$

可随 $\gamma\downarrow0$ 趋零，平均首次点击轮数为 $1/\gamma$。

证明。第 $(n,j)$ 效果为 $\gamma(1-\gamma)^{n-1}H_j$，未点击效果为 $(1-\gamma)^NI$。后者对两态相同，前者的绝对差求和分离出几何系数，得到总变差式。所有 $\gamma>0$ 下第一层效果已满张成，生存概率又趋零，但固定时限内的实际信号与等待成本并不统一。$\square$

## 23. 允许控制如何改变共同暗区

**定义 23.1（记录控制的随机协议）。** 给定有限设置集 $A$，每个设置 $a$ 提供完整仪器 $(\mathcal N_a,\{\mathcal C_{a,x}\}_x)$，所有设置每轮均合法。每轮独立选择 $a$，概率 $w_a>0$、$\sum_aw_a=1$，并把设置连同结果记录。忽略设置以计算总生存时，未点击映射为

$$
\overline{\mathcal N}=\sum_aw_a\mathcal N_a.
$$

这要求实际执行随机控制及存储设置，不能解释为把不同实验中分别可实现的最优结果拼成一次联合实现。

**定理 23.2（共同不变暗区与统一探测证书）。** 写 $\mathcal N_a(X)=\sum_\alpha Q_{a\alpha}XQ_{a\alpha}^\dagger$，点击 Kraus 为 $L_{a,x,\beta}$。随机协议的确定暗空间是满足

$$
L_{a,x,\beta}D=0,\qquad Q_{a\alpha}D\subseteq D
\quad\text{对全部 }a,x,\alpha,\beta
$$

的最大子空间，与正权重的具体数值无关。若该空间为零，令

$$
g=\lambda_{\min}\bigl(I-(\overline{\mathcal N}^{,*})^dI\bigr)>0,
$$

则任意初态满足

$$
s_{md}\le(1-g)^m,
\qquad \mathbb E\mathsf N\le d/g.
$$

若共同暗区非零，从其中任何态出发，任意只使用这些设置、根据已读记录选择下一设置的策略均永不点击。

证明。平均未点击映射的 Kraus 为 $\sqrt{w_a}Q_{a\alpha}$，总点击分支的 Kraus 为 $\sqrt{w_a}L_{a,x,\beta}$。因所有权重正，定理 18.5 中的零条件与不变条件恰为上述共同条件。若共同暗区为零，定理 18.6 保证定义 $g$ 的矩阵正定，因此

$$
(\overline{\mathcal N}^{,*})^dI\le(1-g)I.
$$

利用正性逐块迭代并对尾和求和，得到两个界。若初态在共同暗区，每次合法设置都保持该空间且点击概率为零，对策略的结果树归纳即得最后断言。$\square$

**定理 23.3（固定协议的暗方向可以被合法控制解除）。** 在命题 13.5 的二维空间中，取设置 $a$ 的未点击、点击算子为 $(P_D,P_B)$，设置 $b$ 的为 $(P_B,P_D)$。分别固定设置时均存在一维暗区；若独立以概率 $w$、$1-w$ 选择两设置，$0<w<1$，则无共同暗区，并且

$$
\overline{\mathcal A}^{,n}(I)
=w^nP_D+(1-w)^nP_B,
\qquad
\mathbb E\mathsf N
=\frac{\operatorname{Tr}(\rho P_D)}{1-w}
+\frac{\operatorname{Tr}(\rho P_B)}w.
$$

证明。$\overline{\mathcal A}(X)=wP_DXP_D+(1-w)P_BXP_B$。两投影正交，迭代得到幂公式并取几何级数。每个固定设置的暗态都能由另一个设置点击，因此共同暗区为零。该构造改变了探测耦合，未仅对既有事件时间重新命名。$\square$

## 24. 钟重标、操作变化与联合恢复

**定义 24.1（同一事件的钟重标）。** 固定某个已执行协议及其轮次 $n$，令严格递增的确定标定 $t_n=\theta(n)$，事件时间为 $\mathsf T=\theta(\mathsf N)$。永久无点击映为单独的 $\infty$ 标签。若标定依赖另一个随机钟，则须给出该钟与事件的联合律；仅给两者边缘分布不足以定义该事件时间律。

**定理 24.2（重标保持事件信息，重采样改变协议）。** 确定且单射的钟重标保持事件分布的可识别性与永久无点击概率；其时间律是轮次律的推前。对相同传播生成元在新钟上重新等间隔插入探测，一般不保持原事件分布。

证明。单射标签映射在其像上可逆，因而每个轮次事件与其标定事件一一对应，效果空间不变。重采样重新选择传播间隔并在相应位置插入分支映射；命题 16.2—16.3 给出同一总历时下概率不同的明确构造。有限分辨率钟若是非单射或随机模糊，则改用定理 21.4 的空间相等判据。$\square$

**定理 24.3（带首次事件的动态全息充分性）。** 在以下共同条件下：有限维完整记忆、已知仪器、实际可读历史、全部声明设置合法、确定钟标定；令 $\mathcal Z$ 为定理 20.6 的稳定效果空间，边界为

$$
\eta(\rho,h)=\bigl(\rho|_{\mathcal Z},h,\text{当前控制与钟标定}\bigr).
$$

若策略只读此边界，则 $\eta$ 保留所有由声明分支组成的有限实验之合法执行、结果律和后继边界。进一步有以下两个限定结论。

对于反复使用第 18.1 条同一固定仪器、首次点击即停止的协议，可缩到第 20.1 条的 $\mathcal V$。若途中可换设置，这一缩减须另证对全部允许设置的充分性，不能仅凭停止条件推出。

对于该固定仪器的一次指定点击分支，以及紧接其后的 $\mathcal W$ 期望测试，在全部初态来源类上，初始 $\mathcal V$ 坐标足以确定条件测试期望，当且仅当 $\mathcal C_x^*(\mathcal W)\subseteq\mathcal V$。若任务还包含多步续接，采用上述稳定空间 $\mathcal Z$ 是充分构造；对被前序操作限制的可达后继，全状态闭合不在这里被声称为必要条件。

证明。定理 20.6 给出分支更新闭合与按历史选择操作时的归纳。钟标定由定理 24.2 运输标签，不额外取得态信息。停止任务只需同一未点击分支的闭合，由定理 20.2 足够；紧接点击后的指定期望测试之必要性与充分性由定理 20.3 给出；该条的来源类是全部初态，不是把每个后继接口都重新扩大为任意状态。若遗漏未来会再次耦合的环境，命题 10.1 提供相同边界读数而未来不同的反例；若仅保存首次事件律而扩展到点击后的模式检验，定理 20.4 提供反例；若只作经典时间模糊，则能否保留充分性由定理 21.4 判定。$\square$

**定义 24.4（相干体、事件与可恢复边界的分工）。** 在上述模型中，相干体指支持声明续接的联合量子过程；局域事件指仪器与记录接口中的一个结果；事件时间由先前未点击后继及钟标定共同确定。状态恢复要求效果分离，稳定恢复还要求正的恢复常数，动态恢复进一步要求全部必要拉回方向闭合。永久暗空间、非投影永久生存效果与状态差残余分别表示确定不触发、最终无点击概率及统计不能区分的三种关系，不互相替代。


**命题 24.5（换设置的停止协议需要新增效果方向）。** 在量子比特上令设置 $a$ 为

$$
\mathcal N_a(X)=\tfrac12X,\qquad \mathcal C_a(X)=\tfrac12X,
$$

设置 $b$ 为零未点击分支与两个点击分支 $\mathcal C_{b,j}(X)=P_jXP_j$。策略先使用 $a$，未点击时改用 $b$，首次点击即停止。则单独设置 $a$ 的事件空间 $\mathbb RI$ 对这一策略不充分。

证明。初态 $P_0,P_1$ 具有相同的 $\mathbb RI$ 坐标、初始历史与控制。第一轮均以概率 $1/2$ 未点击并保留原状态。第二轮端口 $0$ 的无条件概率分别为 $1/2$ 与零。缺失方向为 $\mathcal N_a^*(P_0)=P_0/2$，它不在 $\mathbb RI$ 中。$\square$

**命题 24.6（已知重置后的任务不要求任意态上的闭合）。** 固定 $0<\gamma<1$，取

$$
\mathcal N(X)=(1-\gamma)X,
\qquad \mathcal C(X)=\gamma\operatorname{Tr}(X)P_0.
$$

首次事件空间为 $\mathbb RI$。点击后若只允许已知 Hadamard 酉 $H$、计算基测量及依赖已读历史的选择，则全部后续概率可由实际历史确定。尽管如此，$\mathcal W=\operatorname{span}_{\mathbb R}\{I,P_0\}$ 并不对 Hadamard 拉回闭合。

证明。该仪器完全正且总迹保持，每次点击后的归一化状态均为 $P_0$，与输入无关。其后从已知 $P_0$ 出发，按记录的酉操作与测量结果递归计算状态，就能得到每步概率；零概率后继不作条件化。另一方面，$H^\dagger P_0H=P_+$ 具有非零非对角元，不属于 $\mathcal W$。初始输入对所有这些未来效果的作用都先经过重置，$\mathcal C^*(F)=\gamma\operatorname{Tr}(P_0F)I$，所以全部复合测试仍由初始事件边界决定。此处的充分性限于重置后的可达配置，不是任意后继态上的闭合。$\square$

## 追加锚（本行以下为增补区）


## 25. 稀有事件条件化与近似动态边界

**定义 25.1（分支预测误差）。** 记 $D(\rho,\sigma)=\|\rho-\sigma\|_1/2$。给定完全正迹不增分支 $\Phi$，令 $B=\Phi^*(I)$、$p=\operatorname{Tr}(\rho B)$、$q=\operatorname{Tr}(\sigma B)$。仅在 $p,q>0$ 时比较条件后继 $\rho_\Phi=\Phi(\rho)/p$ 与 $\sigma_\Phi=\Phi(\sigma)/q$。这里 $\Phi$ 也可为一条已指定有限结果词的分支复合。

**定理 25.2（分支误差的概率加权界）。** 定义 25.1 下，

$$
|p-q|\le D(\rho,\sigma),
\qquad
\max\{p,q\}\,D(\rho_\Phi,\sigma_\Phi)\le D(\rho,\sigma).
$$

因此，若真实分支概率 $p\ge p_*>0$ 且 $D(\rho,\sigma)\le\varepsilon<p_*$，则估计分支也具有正概率，并有

$$
D(\rho_\Phi,\sigma_\Phi)\le\varepsilon/p_*.
$$

证明。$0\le B\le I$，所以迹零 Hermitian 差的正负部分分解给出 $|\operatorname{Tr}[(\rho-\sigma)B]|\le\|\rho-\sigma\|_1/2$。把失败分支压到一个正交标志，得到保迹完全正映射

$$
\widehat\Phi(X)=\Phi(X)\oplus\operatorname{Tr}[(I-B)X].
$$

正保迹映射对 Hermitian 输入收缩迹范数：若 $X=X_+-X_-$ 为 Jordan 分解，三角不等式给出输出范数至多 $\operatorname{Tr}X_++\operatorname{Tr}X_-=\|X\|_1$。故

$$
\|\Phi(\rho)-\Phi(\sigma)\|_1+|p-q|
\le\|\rho-\sigma\|_1.
$$

另一方面，

$$
p(\rho_\Phi-\sigma_\Phi)
=\Phi(\rho)-\Phi(\sigma)+(q-p)\sigma_\Phi,
$$

所以 $p\|\rho_\Phi-\sigma_\Phi\|_1$ 不超过上一式左端；交换两态得到同样的 $q$ 界，因而得到最大值形式。最后 $q\ge p-\varepsilon>0$，再除以 $p_*$。$\square$

**命题 25.3（小初态误差可在稀有分支达到最大条件误差）。** 对每个 $0<\varepsilon<1$，存在两态与同一分支，使 $D(\rho,\sigma)=\varepsilon$，两分支概率均为 $\varepsilon$，而条件后继半迹距离为一。

证明。取正交基 $c,0,1$，令

$$
\rho=(1-\varepsilon)|c\rangle\langle c|+\varepsilon|0\rangle\langle0|,
\quad
\sigma=(1-\varepsilon)|c\rangle\langle c|+\varepsilon|1\rangle\langle1|.
$$

以 $P=|0\rangle\langle0|+|1\rangle\langle1|$ 定义分支 $\Phi(X)=PXP$，补分支为 $|c\rangle\langle c|X|c\rangle\langle c|$。直接计算得到三项读数，且定理 25.2 的加权界取等号。故去掉分支概率因子后不存在趋于零的统一条件误差界。$\square$

**定理 25.4（近似拉回闭合需要概率下界）。** 设 $\mathcal V$ 是包含 $I,B$ 的实效果空间，两态在 $\mathcal V$ 上期望相同，且共同分支概率 $p>0$。对某个后继效果 $0\le H\le I$，若存在 $G\in\mathcal V$ 满足

$$
\|\Phi^*(H)-G\|_\infty\le\eta,
$$

则

$$
\left|\operatorname{Tr}[(\rho_\Phi-\sigma_\Phi)H]\right|
\le\min\{1,2\eta/p\}.
$$

证明。两态的 $G$ 期望相同，分母也相同，故左侧等于

$$
\frac{|\operatorname{Tr}[(\rho-\sigma)(\Phi^*H-G)]|}{p}
\le\frac{\|\rho-\sigma\|_1\,\|\Phi^*H-G\|_\infty}{p}
\le\frac{2\eta}{p}.
$$

效果的两状态期望差还不超过一。$\square$

**命题 25.5（近似闭合缺陷趋零而条件差不消失）。** 在命题 14.5 的量子比特仪器中，取 $\mathcal V=\mathbb RI$、点击分支 $\Phi(X)=\gamma X$、$H=P_0$。其拉回到 $\mathcal V$ 的最小算子范数距离为 $\gamma/2$，但初态 $P_0,P_1$ 的点击后 $H$ 期望差始终为一。

证明。$\Phi^*H=\gamma P_0$，与 $cI$ 的距离为 $\max\{|\gamma-c|,|c|\}$，在 $c=\gamma/2$ 取最小值 $\gamma/2$。两态同边界、共同点击概率为 $\gamma$，点击后保持原态，所以条件差为一，恰等于 $2(\gamma/2)/\gamma$。当 $\gamma\downarrow0$ 时，未归一化误差趋零，条件误差不变。$\square$

**定理 25.6（有限样本恢复到分支预测的充分预算）。** 沿用定理 22.3 的独立准备、已知 POVM 和 $\alpha>0$ 假设。给定 $0<\zeta<1$、$p_*>0$ 与 $0<\delta<1$。若

$$
m\ge\frac{dJ\log(2J/\delta)}{2\alpha^2\zeta^2p_*^2},
$$

则以概率至少 $1-\delta$，对于每个真实概率至少 $p_*$ 的已声明完全正迹不增分支，其估计概率为正，且真实与估计条件后继的半迹距离至多 $\zeta$。

证明。定理 22.3 的同一个高概率事件给出 $D(\widehat\rho,\rho)\le\zeta p_*<p_*$。在这一事件上，定理 25.2 对每个分支同时成立，得到所述结论，无需再对分支数作并集界。预算是所选恢复方法的充分上界，不声称样本复杂度最优。分支可表示有限历史，但未校准仪器、模型误差或缺失环境记忆不由该统计界控制。$\square$

## 追加锚（本行以下为增补区）

## 26. 把最终点击条件写入一套新的仪器

**约定 26.1（来源、支撑与输出类型）。** 沿用第 18—19 节的固定有限维仪器：未点击分支为 $\mathcal N$，点击分支为 $\mathcal C_x$，$\mathcal A=\mathcal N^*$，$B_x=\mathcal C_x^*(I)$。置

$$
F=\lim_{n\to\infty}\mathcal A^n(I),\qquad
R=I-F\ne0,\qquad
\mathcal D=\ker R,\qquad P=P_{\mathcal D^\perp},
\qquad\mathcal H_P=P\mathcal H.
$$

记 $G=R^{1/2}$；$G^{-1}$ 始终指 $\mathcal H_P$ 上的逆，嵌入原空间时在 $\mathcal D$ 上补零。符号 $I_P$ 表示 $\mathcal H_P$ 的恒等。对 $r_\rho=\operatorname{Tr}(\rho R)>0$ 定义

$$
\mathcal S_R(X)=GXG,\qquad
\tau_R(\rho)=\frac{\mathcal S_R(\rho)}{r_\rho}.
$$

新未点击分支的输入、输出都是 $\mathcal H_P$，新点击分支的输入为 $\mathcal H_P$、输出仍为原来的 $\mathcal H$。将不同结果放入正交标志直和，就得到通常意义下具有共同输出空间的仪器。这里保留点击后的量子系统，不只保存点击概率。

**引理 26.2（暗空间使支撑限制与实际分支相容）。** 对任意 Kraus 表示 $\mathcal N(X)=\sum_\alpha Q_\alpha XQ_\alpha^\dagger$、$\mathcal C_x(X)=\sum_\beta L_{x\beta}XL_{x\beta}^\dagger$，有

$$
R=\mathcal A(R)+\sum_xB_x,
\qquad P Q_\alpha(I-P)=0,
\qquad L_{x\beta}(I-P)=0.
$$

若 $H=PHP$，则 $\mathcal A(H)=P\mathcal A(H)P$；对任意终端 Hermitian 测试 $Z$，$\mathcal C_x^*(Z)$ 也支撑在 $\mathcal H_P$。

证明。由 $\mathcal A(F)=F$ 与 $\mathcal A(I)+\sum_xB_x=I$ 得到第一式。定理 18.5 说明每个 $Q_\alpha$ 保持 $\mathcal D$，每个 $L_{x\beta}$ 在 $\mathcal D$ 上为零，得到其余两个式子。由 $PQ_\alpha=PQ_\alpha P$ 与 $H=PHP$，有 $\mathcal A(H)=\sum_\alpha(PQ_\alpha P)^\dagger H(PQ_\alpha P)$，故其两侧均支撑于 $P$；这一步不要求 $H$ 自伴。点击拉回的结论由 $L_{x\beta}=L_{x\beta}P$ 同样得到。$\square$

**定理 26.3（最终点击条件的量子 Doob 表示）。** 对 $X\in\mathcal L(\mathcal H_P)$ 定义

$$
\widetilde{\mathcal N}(X)
=G\mathcal N(G^{-1}XG^{-1})G,
\qquad
\widetilde{\mathcal C}_x(X)
=\mathcal C_x(G^{-1}XG^{-1}).
$$

这些分支完全正，且满足仪器完备性

$$
\widetilde{\mathcal N}^{*}(I_P)
+\sum_x\widetilde{\mathcal C}_x^{*}(I)=I_P.
$$

对原空间全部算子，有

$$
\widetilde{\mathcal N}\mathcal S_R=\mathcal S_R\mathcal N,
\qquad
\widetilde{\mathcal C}_x\mathcal S_R=\mathcal C_x.
$$

因而对每个 $n\ge1$ 和 $r_\rho>0$，

$$
\boxed{
\widetilde{\mathcal C}_x\widetilde{\mathcal N}^{\,n-1}
\bigl(\tau_R(\rho)\bigr)
=\frac{\mathcal C_x\mathcal N^{n-1}(\rho)}{r_\rho}.
}
$$

所以新过程复现原过程在最终点击条件下的首次点击时间、端口及各非零分支的归一化终端量子态。

证明。新 Kraus 算子分别是 $GQ_\alpha G^{-1}$ 和 $L_{x\beta}G^{-1}$，完全正性直接成立。拉回恒等后相加，得到

$$
G^{-1}\left(\mathcal A(R)+\sum_xB_x\right)G^{-1}
=G^{-1}RG^{-1}=I_P.
$$

引理 26.2 给出 $GQ_\alpha P=GQ_\alpha$ 与 $L_{x\beta}P=L_{x\beta}$，故

$$
G\mathcal N(PXP)G=G\mathcal N(X)G,
\qquad \mathcal C_x(PXP)=\mathcal C_x(X).
$$

再用 $G^{-1}G=GG^{-1}=P$，即得两个交织恒等式。逐次代入并除以 $r_\rho$ 得到方框公式。其右端迹是原分支概率除以最终点击概率；终端分支再归一化时该公共因子抵消。$\square$

**定理 26.4（条件尾项变为普通生存效果）。** 新过程从任意 $\mathcal H_P$ 上的初态出发最终点击概率为一，且

$$
\widetilde S_n
=(\widetilde{\mathcal N}^{*})^n(I_P)
=G^{-1}\mathcal A^n(R)G^{-1}\longrightarrow0.
$$

对定理 19.2 的 $M,q,T$，有

$$
\widetilde S_n\le q^{\lfloor n/M\rfloor}I_P,
\qquad
\widetilde T:=\sum_{n\ge0}\widetilde S_n=G^{-1}TG^{-1},
\qquad
\operatorname{Tr}\bigl(\tau_R(\rho)\widetilde T\bigr)
=\frac{\operatorname{Tr}(\rho T)}{r_\rho}.
$$

证明。新未点击拉回为

$$
\widetilde{\mathcal N}^{*}(H)=G^{-1}\mathcal A(GHG)G^{-1}.
$$

从 $GI_PG=R$ 开始迭代；引理 26.2 保证中间算子都在 $P$ 支撑上，故相邻的 $G,G^{-1}$ 可消去，得到生存效果公式。定理 19.2 的剩余尾项趋零且被 $q^{\lfloor n/M\rfloor}R$ 控制，共轭后得到前两项。范数收敛允许逐项共轭求和。$T=PTP$，迹的循环性给出最后一式。$\square$

**说明 26.5（既有工具与本处适用范围）。** 通过正算子平方根改变量子轨迹动力学是既有量子 Doob 变换机制。Carollo、Garrahan、Lesanovsky 与 Pérez-Espigares 的 [arXiv:1711.10951v2](https://arxiv.org/abs/1711.10951v2)，特别是式 (6)—(11)，处理计数偏置的开放系统动力学，包含长时及有限时间构造；Esteve 等的 [arXiv:2508.04622v1](https://arxiv.org/abs/2508.04622v1) 讨论输运优化与受限控制。本节直接证明离散首次吸收条件下、允许 $R$ 奇异时的支撑版本，不将上述文献的条件或结论逐字移植。仪器的数学存在性也不证明当前装置拥有实施这些新分支所需的控制。

## 27. 条件坐标中的动态充分边界

**定义 27.1（按最终点击权重归一的边界）。** 设 $\mathcal W\subseteq\operatorname{Herm}(\mathcal H)$ 为实线性空间，其中每个元素都支撑在 $P$ 上，且 $R\in\mathcal W$。令

$$
\Theta_R(H)=G^{-1}HG^{-1},\qquad
\widetilde{\mathcal W}=\Theta_R(\mathcal W),
\qquad
b_{\mathcal W}(\rho)
=\left(\frac{\operatorname{Tr}(\rho H)}{r_\rho}\right)_{H\in\mathcal W}.
$$

有限基即可给出这份边界的全部坐标。它描述已条件于最终点击的任务；若还要恢复原过程的无条件点击权重，须另保留 $r_\rho$。

**定理 27.2（条件边界的拉回闭合被精确运输）。** 对任意 $H\in\mathcal W$ 及 $r_\rho>0$，

$$
\operatorname{Tr}\bigl[\tau_R(\rho)\Theta_R(H)\bigr]
=\frac{\operatorname{Tr}(\rho H)}{r_\rho},
\qquad
\widetilde{\mathcal N}^{*}\Theta_R(H)=\Theta_R\mathcal A(H).
$$

因此

$$
\mathcal A(\mathcal W)\subseteq\mathcal W
\iff
\widetilde{\mathcal N}^{*}(\widetilde{\mathcal W})
\subseteq\widetilde{\mathcal W}.
$$

指定点击后测试族 $\mathcal Z_x$ 时，还有

$$
\mathcal C_x^*(\mathcal Z_x)\subseteq\mathcal W
\iff
\widetilde{\mathcal C}_x^*(\mathcal Z_x)
\subseteq\widetilde{\mathcal W}.
$$

若这些包含关系成立，且每个 $\mathcal Z_x$ 包含终端恒等，则 $b_{\mathcal W}$ 对新过程的首次点击、未点击条件续接及所指定终端测试动态充分。这里的闭合指全部 $\mathcal H_P$ 状态上的同一线性表示；不据此断言受限可达来源必须具有全空间闭合。

证明。第一式用 $H=PHP$ 与迹循环性。第二式由定理 26.4 的拉回公式和 $G\Theta_R(H)G=H$ 得到。$\Theta_R$ 是 $P$ 支撑 Hermitian 空间到 $\operatorname{Herm}(\mathcal H_P)$ 的线性双射，故推出第一个等价。新点击拉回满足

$$
\widetilde{\mathcal C}_x^*(Z)=\Theta_R\bigl(\mathcal C_x^*(Z)\bigr),
$$

得到第二个等价。$\Theta_R(R)=I_P$，所以新边界含恒等；对结果概率与每个后继坐标反复拉回，得到第 20 节的动态充分性。正概率后继才归一化，零概率路径不要求条件态。该证明同时说明：$\tau_R(\rho)$ 要配合变换后的仪器与测试使用，不能把原系统上任意中间测量的算子保持原样后仍声称相同条件实验。$\square$

**命题 27.3（条件过程仍不能确定原来的点击权重）。** 若 $\mathcal D\ne\{0\}$，取任意暗态 $\omega_D$ 及 $\mathcal H_P$ 上的状态 $\sigma$。对 $0<t\le1$ 令 $\rho_t=(1-t)\omega_D+t\sigma$，则

$$
\tau_R(\rho_t)=\tau_R(\sigma),
\qquad r_{\rho_t}=t\operatorname{Tr}(\sigma R).
$$

全部条件首次事件及终端态相同，而无条件最终点击概率可以不同。

证明。$G\omega_DG=0$，故分子和分母同时乘 $t$。定理 26.3 随即给出条件过程相同；最后的概率公式随 $t$ 严格改变。$\square$

## 28. 条件状态的精确制备成本

**定义 28.1（单份未知输入的成功分支合同）。** 本节来源类是 $\mathcal H_P$ 上的全部密度矩阵。实验者知道 $R$，但不知本次输入 $\rho$；每次只取得一份输入，不允许先取得其经典完整描述或额外副本。允许任意固定完全正迹不增成功操作 $\mathcal E$，要求对全部来源都满足

$$
p_{\mathcal E}(\rho):=\operatorname{Tr}\mathcal E(\rho)>0,
\qquad
\frac{\mathcal E(\rho)}{p_{\mathcal E}(\rho)}=\tau_R(\rho).
$$

辅助系统及未读结果可包含在 CP 操作实现中，成功时交出的量子系统为 $\mathcal H_P$。这是一份统一量子操作的合同，不是每个已知输入可另选制备程序。

**定理 28.2（精确成功操作的刚性）。** 定义 28.1 下，存在与输入无关的常数 $c>0$，使

$$
\boxed{\mathcal E(X)=cGXG.}
$$

反之，该映射满足所需条件态；它迹不增当且仅当 $cR\le I_P$。

证明。写 $\mathcal E(X)=\sum_jK_jXK_j^\dagger$。对每个非零向量 $\psi\in\mathcal H_P$，输出在归一化后为 $G\psi$ 对应的纯态。正半定秩一和的每个向量 $K_j\psi$ 因而都平行于 $G\psi$，包括零向量的情形。于是 $G^{-1}K_j$ 保持每一条向量射线。在线性空间维数至少二时，取基向量及每对基向量之和，得到全部比例系数相同，因此 $G^{-1}K_j=a_jI_P$；一维时这一结论直接成立。令 $c=\sum_j|a_j|^2$，即得方框式；处处正的成功概率迫使 $c>0$。其效果为 $cR$，所以迹不增条件正是 $cR\le I_P$。$\square$

**定理 28.3（最优最坏成功率）。** 令 $r_{\min},r_{\max}>0$ 为 $R|_{\mathcal H_P}$ 的最小、最大本征值。则

$$
\boxed{
p_{\mathrm{opt}}
:=\sup_{\mathcal E}\inf_{\rho\text{ 支撑于 }P}
p_{\mathcal E}(\rho)
=\frac{r_{\min}}{r_{\max}}.
}
$$

上确界由成功 Kraus 算子 $G/\sqrt{r_{\max}}$ 达到，可补失败 Kraus 算子 $\sqrt{I_P-R/r_{\max}}$。确定性精确制备对全部来源成立，当且仅当 $R|_{\mathcal H_P}$ 是正标量乘恒等。

证明。定理 28.2 给出 $c\le1/r_{\max}$，而输入取最小本征态时成功率为 $cr_{\min}$；这既给出上界，又被所述 Kraus 对达到。确定性要求 $cR=I_P$，等价于正标量形式。反向此时 $\tau_R(\rho)=\rho$，恒等通道即可。$\square$

**命题 28.4（条件模拟与原始事件权重的两种合同）。** 原始过滤分支 $\mathcal S_R$ 是合法迹不增操作。对任意原空间初态 $\rho$，先执行该分支，成功后运行第 26 节的新过程，所得有限首次点击分支的未归一化终端态恰为

$$
\widetilde{\mathcal C}_x\widetilde{\mathcal N}^{\,n-1}
\mathcal S_R(\rho)
=\mathcal C_x\mathcal N^{n-1}(\rho).
$$

成功概率为 $r_\rho$；失败可以标记为无事件，其概率为 $1-r_\rho$。若改用最优过滤 $\mathcal S_R/r_{\max}$，每个有限事件权重同时乘 $1/r_{\max}$，条件分布与条件终端态保持相同。

证明。$R\le I$ 保证原过滤合法；与失败标志分支 $X\mapsto\operatorname{Tr}[(I-R)X]$ 合成保迹操作。交织恒等式证明终端公式，最优过滤仅乘常数。该模拟在新协议中可以即时宣告失败；它没有复现原协议中无穷长的未点击记录，也没有识别同一份原始样本在未执行实验中的个体未来。$\square$

## 29. 制备成功率与条件敏感度的精确对应

**定义 29.1（整个来源类上的条件数）。** 假设 $\dim\mathcal H_P\ge2$，记

$$
\kappa_R=\frac{r_{\max}}{r_{\min}},\qquad
L_R=\sup_{\rho\ne\sigma\text{ 支撑于 }P}
\frac{D(\tau_R(\rho),\tau_R(\sigma))}{D(\rho,\sigma)},
\qquad D(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1.
$$

两态可以为混态，且共享同一个已知 $R$。$L_R$ 是归一化状态变换的灵敏度，不是对未知仪器误差的界。

**定理 29.2（条件化的锐迹距离常数）。** 定义 29.1 下，

$$
\boxed{L_R=\kappa_R.}
$$

并且全部来源满足双向界

$$
\kappa_R^{-1}D(\rho,\sigma)
\le D(\tau_R(\rho),\tau_R(\sigma))
\le\kappa_RD(\rho,\sigma).
$$

证明。对迹不增过滤 $\mathcal E(X)=GXG/r_{\max}$，每个来源的成功概率至少为 $r_{\min}/r_{\max}$。由定理 25.2 的概率加权收缩界得到上界。若 $r_{\min}<r_{\max}$，取相应正交本征态 $P_-,P_+$，置 $\rho=P_-$、$\sigma_\varepsilon=(1-\varepsilon)P_-+\varepsilon P_+$，其中 $0<\varepsilon<1$。则

$$
D(\rho,\sigma_\varepsilon)=\varepsilon,
\qquad
\frac{D(\tau_R(\rho),\tau_R(\sigma_\varepsilon))}
{D(\rho,\sigma_\varepsilon)}
=\frac{\kappa_R}{1+(\kappa_R-1)\varepsilon}
\longrightarrow\kappa_R.
$$

故上界最优。若两本征值相等，$\tau_R$ 是恒等映射，来源类中存在不同两态，所以 $L_R=1=\kappa_R$。逆变换为

$$
\tau_R^{-1}(\omega)
=\frac{G^{-1}\omega G^{-1}}{\operatorname{Tr}(\omega R^{-1})}.
$$

它对应正算子 $R^{-1}$ 的归一化过滤，谱比仍是 $\kappa_R$；用合法缩放 $r_{\min}R^{-1}\le I_P$ 重复上界论证，得到下界。$\square$

**推论 29.3（制备成本与误差放大是同一谱比的两面）。** 在第 28 节的全部来源、单输入、统一 CP 操作合同及 $\dim\mathcal H_P\ge2$ 下，

$$
\boxed{
p_{\mathrm{opt}}=\kappa_R^{-1},\qquad
L_R=\kappa_R,\qquad
p_{\mathrm{opt}}L_R=1.
}
$$

证明。定理 28.3 与定理 29.2 使用同一个 $R$、同一个来源类与同一个半迹距离，直接组合即得。$\square$

这给出本批“AHH”的精确内容：最终点击条件造成的最大误差放大，与精确制备该条件态时最优的最坏成功率，由同一组谱端点控制。该关系不把代数改写当作免费实验，也不把一般量子后选择都归入这份特定合同。

**命题 29.4（稀有程度与条件敏感度可以分离）。** 对正数 $a$，只要 $aR\le I$，便有

$$
\tau_{aR}=\tau_R,\qquad
\kappa_{aR}=\kappa_R,
\qquad p_{\mathrm{opt}}(aR)=p_{\mathrm{opt}}(R),
$$

而原始过滤成功概率满足 $\operatorname{Tr}(\rho aR)=a\operatorname{Tr}(\rho R)$。

证明。归一化分子、分母同时乘 $a$；最小和最大正本征值也同时乘 $a$，所以比值不变。最后一式由迹的线性性。此命题首先是效果过滤的结论：把 $R$ 缩放后若仍要求它来自某套首次点击仪器，还须另给该仪器；第 30.3 条提供一族实际实现。$\square$

**命题 29.5（一维来源不能套用乘积恒等式）。** 若 $\dim\mathcal H_P=1$，则该来源类只有一个状态，最优精确制备成功率为一，且任意两来源的输出距离都为零；将最小非负 Lipschitz 常数定义为零时，$L_R=0$。

证明。一维密度矩阵只有 $I_P$，归一化过滤保持它，恒等操作成功率为一。所有距离比较都发生在同一状态之间，常数零满足要求。这也是定义 29.1 排除一维的原因。$\square$

## 30. 接近暗空间时的失稳与一个共同实现

**定理 30.1（扩大来源类会同时失去两个统一保证）。** 假设 $\mathcal D\ne\{0\}$ 且 $\dim\mathcal H_P\ge2$。将来源扩大为原空间全部满足 $r_\rho>0$ 的密度矩阵，则 $\tau_R$ 没有有限的统一迹距离 Lipschitz 常数。任何在这个来源类上精确实现 $\tau_R$、处处具有正成功率的固定 CP 迹不增操作，其成功概率的下确界均为零。

证明。取暗空间单位向量 $d$，以及 $R|_{\mathcal H_P}$ 的两个正交本征向量 $u,v$。对 $0<\varepsilon<1$，令

$$
\rho_\varepsilon=(1-\varepsilon)|d\rangle\langle d|+\varepsilon|u\rangle\langle u|,
\quad
\sigma_\varepsilon=(1-\varepsilon)|d\rangle\langle d|+\varepsilon|v\rangle\langle v|.
$$

输入距离为 $\varepsilon$，输出分别为两个正交本征态，距离为一，故没有有限统一常数。再令 $\mathcal E$ 为所述成功操作。对第一族，正算子

$$
(1-\varepsilon)\mathcal E(|d\rangle\langle d|)
+\varepsilon\mathcal E(|u\rangle\langle u|)
$$

必须支撑于 $\mathbb Cu$，所以 $\mathcal E(|d\rangle\langle d|)$ 支撑于该直线。对第二族同理得到支撑于 $\mathbb Cv$，从而它为零。于是 $p_{\mathcal E}(\rho_\varepsilon)=\varepsilon p_{\mathcal E}(|u\rangle\langle u|)\le\varepsilon$，下确界为零。这里只分别证明无有限常数和无正统一成功率，不将 $0\cdot\infty$ 写成恒等式。$\square$

**命题 30.2（远离零事件权重的来源保留有界控制）。** 对任意来源子集 $\mathfrak S$，若有 $a>0$ 使 $r_\rho\ge a$ 对全部 $\rho\in\mathfrak S$ 成立，则过滤 $\mathcal S_R/r_{\max}$ 在该来源集上的成功率至少为 $a/r_{\max}$，并且

$$
D(\tau_R(\rho),\tau_R(\sigma))
\le\frac{r_{\max}}aD(\rho,\sigma)
\qquad(\rho,\sigma\in\mathfrak S).
$$

证明。该过滤在原空间上仍然合法，因为 $R/r_{\max}\le I$。成功率公式和定理 25.2 给出两式。这是来源约束下的充分界，不声称对每个受限来源类都达到最优。$\square$

**命题 30.3（同一吸收仪器中的条件变换与谱比成本）。** 取正交基 $d,u,v$ 与 $0<r_1\le r_2\le1$，设置一个点击端口和以下 Kraus 算子：

$$
Q_0=|d\rangle\langle d|,
\quad Q_1=\sqrt{1-r_1}|d\rangle\langle u|,
\quad Q_2=\sqrt{1-r_2}|d\rangle\langle v|,
\quad L=\sqrt{r_1}|u\rangle\langle u|+\sqrt{r_2}|v\rangle\langle v|.
$$

则最终点击效果为

$$
R=r_1|u\rangle\langle u|+r_2|v\rangle\langle v|,
$$

条件 Doob 过程在 $\operatorname{span}\{u,v\}$ 上必定第一轮点击，并保持输入的条件态；其过滤的最优最坏成功率为 $r_1/r_2$，锐条件敏感度为 $r_2/r_1$。原过程从 $u$ 或 $v$ 出发仍分别只有 $r_1,r_2$ 的最终点击概率。永久生存效果 $F=I-R$ 非投影，当且仅当 $r_1<1$。

证明。直接相加得到 $\sum_{j=0}^2Q_j^\dagger Q_j+L^\dagger L=I$。任何一次未点击都进入暗态 $d$，故只有第一轮可能点击，$R=L^\dagger L$。在 $P$ 上 $G=L$，新点击 Kraus 算子 $LG^{-1}=I_P$，全部新未点击 Kraus 算子 $GQ_jG^{-1}$ 为零。成本和敏感度由第 28—29 节得到，输入本征态的点击概率由 $R$ 的对角元给出。$F$ 的本征值为 $1,1-r_1,1-r_2$；在给定参数范围内，它们全属于 $\{0,1\}$ 当且仅当 $r_1=r_2=1$，得到非投影判据。若同时把 $r_1,r_2$ 乘任意 $0<a\le1$ 并相应重建上述 Kraus 算子，条件变换和谱比不变，而原来的两点击概率均乘 $a$。$\square$

**说明 30.4（关系解释与证据边界）。** 本批把第 19 节的最终事件效果与等待算子、第 20 节的动态拉回闭合、第 25 节的后选择误差连接到同一支撑变换；第 28—30 节另行写明制备任务及其极端来源。Kraus 操作、后选择和迹范数的基础沿用第 0 节所引 Watrous 教材，Doob 机制的来源见第 26.5 条。这里是有限维模型中的自包含数学推导，不主张文献原创性，也不是 Lean 编译结果。已知变换后的条件分布、能够制备条件初态、能够实施新仪器，以及原实验实际出现点击，是四个不同的要求；各自的概率、权限与来源条件都不能由另外一项代替。

**说明 30.5（后选择距离的相关文献）。** Gavorová 的 *Notes on distinguishability of postselected computations*，[arXiv:2011.08487v2](https://arxiv.org/abs/2011.08487v2)，从归一化 CP 映射的非线性出发研究后选择计算之间的距离，并给出相应转换引理。本批第 29 节固定同一个过滤，比较不同输入状态，另附第 28 节的精确单输入制备合同；这与比较两个后选择过程的距离有不同的量词。第 25 节的加权界在本卷直接证明，不能仅由“量子通道收缩距离”省略归一化分母后推出。

## 追加锚（本行以下为增补区）

## 31. 有限截止条件与逐轮变化的支撑

**定义 31.1（截止前点击效果）。** 固定第 18 节的同一重复仪器，沿用 $\mathcal N,\mathcal C_x,\mathcal A,F,R$，假设 $R\ne0$。令

$$
B=\sum_x\mathcal C_x^*(I),\qquad
H_m=I-\mathcal A^m(I),\qquad H_0=0,
\qquad h_m(\rho)=\operatorname{Tr}(\rho H_m).
$$

$H_m$ 表示前 $m$ 轮之内已经首次点击，$R$ 表示最终点击；两者不是第 19 节的剩余尾项 $R_m=\mathcal A^m(R)$。记 $P_m$ 为 $H_m$ 的支撑投影，$G_m=H_m^{1/2}$；逆算子只在支撑上取逆，其余方向补零。$P_0=G_0=0$。条件来源要求 $h_m(\rho)>0$，并定义

$$
\tau_m(\rho)=\frac{G_m\rho G_m}{h_m(\rho)},
\qquad \mathcal S_m(X)=G_mXG_m.
$$

截止轮数在本协议开始前给定。若在读到中途结果后改变截止规则，必须按新规则重新计算其成功效果；本节不把两套条件事件自动等同。

**引理 31.2（截止递推、有限支撑与尚未收敛的权重）。** 对 $m\ge1$ 有

$$
H_m=B+\mathcal A(H_{m-1}),\qquad
0\le H_m\le H_{m+1}\le R,\qquad
R-H_m=\mathcal A^m(R).
$$

若 $d=\dim\mathcal H$，则 $P_m=P=\operatorname{supp}R$ 对全部 $m\ge d$ 成立。对任意 Kraus 表示，

$$
G_{m-1}Q_\alpha(I-P_m)=0,
\qquad L_{x\beta}(I-P_m)=0.
$$

证明。由 $B=I-\mathcal A(I)$ 得到递推，前 $m$ 轮点击效果的非负和给出单调性。$\mathcal A^m(F)=F$，故 $R-H_m=\mathcal A^m(I)-F=\mathcal A^m(R)$。定理 18.5 给出 $\ker H_m=\mathcal D$ 对 $m\ge d$ 成立，从而支撑相等。若 $u\in\ker H_m$，递推式的二次型为

$$
0=\langle u,H_mu\rangle
=\sum_{x,\beta}\|L_{x\beta}u\|^2
+\sum_\alpha\|G_{m-1}Q_\alpha u\|^2.
$$

每项非负，所以每项为零。支撑的有限稳定只确定哪些方向能在截止前触发事件；它不推出 $H_m=R$，因为剩余尾项仍可非零。$\square$

**定理 31.3（有限截止的量子 Doob 仪器）。** 剩余 $m\ge1$ 轮时，对支撑于 $P_m$ 的输入定义

$$
\mathcal N^{[m]}(X)
=G_{m-1}\mathcal N(G_m^{-1}XG_m^{-1})G_{m-1},
\qquad
\mathcal C_x^{[m]}(X)
=\mathcal C_x(G_m^{-1}XG_m^{-1}).
$$

未点击输出位于 $P_{m-1}\mathcal H$，点击输出位于原空间 $\mathcal H$；用结果标志直和可统一输出类型。这些完全正分支满足

$$
(\mathcal N^{[m]})^*(I_{P_{m-1}})
+\sum_x(\mathcal C_x^{[m]})^*(I)=I_{P_m}.
$$

对原空间全部算子，有

$$
\mathcal N^{[m]}\mathcal S_m=\mathcal S_{m-1}\mathcal N,
\qquad
\mathcal C_x^{[m]}\mathcal S_m=\mathcal C_x.
$$

这里 $I_{P_0}$ 是零空间上的零算子。最后一轮的未点击分支恒为零。

证明。新 Kraus 算子是 $G_{m-1}Q_\alpha G_m^{-1}$ 与 $L_{x\beta}G_m^{-1}$。其效果之和为

$$
G_m^{-1}\bigl(\mathcal A(H_{m-1})+B\bigr)G_m^{-1}
=G_m^{-1}H_mG_m^{-1}=I_{P_m}.
$$

引理 31.2 使 $G_{m-1}Q_\alpha P_m=G_{m-1}Q_\alpha$、$L_{x\beta}P_m=L_{x\beta}$。将 $G_m^{-1}G_m=P_m$ 代入即可逐 Kraus 验证交织式，不要求 $P_m$ 对原未点击算子不变。当 $m=1$，左侧未点击 Kraus 的 $G_0$ 为零。$\square$

**定理 31.4（倒计时过程精确保留截止条件下的终端分支）。** 初始截止为 $m$，未点击时将剩余轮数减一。对 $1\le n\le m$ 及 $h_m(\rho)>0$，有

$$
\boxed{
\mathcal C_x^{[m-n+1]}
\mathcal N^{[m-n+2]}\cdots\mathcal N^{[m]}
\bigl(\tau_m(\rho)\bigr)
=\frac{\mathcal C_x\mathcal N^{n-1}(\rho)}{h_m(\rho)}.
}
$$

$n=1$ 时中间乘积为空。该新过程至迟第 $m$ 轮点击，保留原过程条件于 $\mathsf N\le m$ 的时间、端口及各非零分支的终端态。

证明。对定理 31.3 的未点击交织式逐次代入，使 $\mathcal S_m$ 依次变成 $\mathcal S_{m-1},\ldots,\mathcal S_{m-n+1}$，再使用点击交织式，得到方框公式。所有 $n\le m,x$ 的右端迹之和为 $h_m(\rho)/h_m(\rho)=1$；最后一轮未点击分支也直接为零。归一化某个非零终端分支时，公共分母抵消。这个等价要求同时改变初态与逐轮仪器；它不把原仪器加上一只倒计时钟就自动变成条件仪器。$\square$

**说明 31.5（时空调和变换的既有来源）。** Ticozzi 与 Pavon 的 *On time-reversal and space-time harmonic processes for Markovian quantum channels*，[arXiv:0811.0929v2](https://arxiv.org/abs/0811.0929v2)，第 6 节式 (29) 及其后的乘性变换讨论说明：时空调和正算子可产生新的保恒等量子操作，其伴随为保迹通道；该处乘性构造明确采用各时刻满秩的简化条件。第 26.5 条所引 Carollo 等还给出连续时间的有限时域量子 Doob 构造。本节使用这一成熟机制，并直接证明首次点击问题中随剩余期限变化的支撑、零末端及终端分支恒等式；没有把满秩假设默默用于奇异截止效果。

## 32. 用有限截止逼近最终点击的条件任务

**定义 32.1（保留早期终端态的有限记录输出）。** 固定 $m\ge1$，令

$$
T_{n,x}(\rho)=\mathcal C_x\mathcal N^{n-1}(\rho),\qquad
r=\operatorname{Tr}(\rho R),\qquad h=h_m(\rho)>0,
\qquad t_m(\rho)=\frac{r-h}{r}.
$$

在有限直和空间 $\bigl(\bigoplus_{n\le m,x}\mathcal H\bigr)\oplus\mathbb C$ 上定义

$$
\Omega_{\infty\to m}(\rho)
=\left(\bigoplus_{n\le m,x}\frac{T_{n,x}(\rho)}r\right)\oplus t_m(\rho),
\qquad
\Omega_m(\rho)
=\left(\bigoplus_{n\le m,x}\frac{T_{n,x}(\rho)}h\right)\oplus0.
$$

第一态在最终点击条件下保留所有早期记录及其终端量子态，将更晚的点击压入一个正交标志；第二态条件于截止前点击。晚点击标志是条件输出的数学归类，不是在第 $m$ 轮已经认证某个未点击样本今后必会点击。

**定理 32.2（完整早期记录的截断误差恰为条件尾重）。** 两态均归一化，且

$$
\boxed{
D\bigl(\Omega_{\infty\to m}(\rho),\Omega_m(\rho)\bigr)
=t_m(\rho)
=\frac{\operatorname{Tr}[\rho\mathcal A^m(R)]}{r}.
}
$$

因此对这份共同输出上的每个效果，概率差至多为 $t_m(\rho)$；读取晚点击标志达到该界。

证明。全部早期块的迹之和为 $h$，两个直和的总迹均为一。由于 $h\le r$，每个早期差块 $T_{n,x}(1/r-1/h)$ 都半负定，其迹范数相加为 $1-h/r=t_m$；晚标志差块为正数 $t_m$。直和的迹范数相加，除以二得第一式。引理 31.2 给出第二式。效果概率差的界由迹距离变分公式得到，晚标志的效果给出等号。$\square$

**推论 32.3（任意共同终端读出的统一误差）。** 对每个事件 $(n,x)$ 指定一个保迹完全正终端读出 $\Lambda_{n,x}$，输出到同一个有限维空间 $\mathcal K$。定义

$$
\Xi_\infty(\rho)=\frac1r\sum_{n\ge1,x}\Lambda_{n,x}(T_{n,x}(\rho)),
\qquad
\Xi_m(\rho)=\frac1h\sum_{n\le m,x}\Lambda_{n,x}(T_{n,x}(\rho)).
$$

则级数在迹范数中收敛，并且 $D(\Xi_\infty(\rho),\Xi_m(\rho))\le t_m(\rho)$。

证明。级数每项为正，其迹之和为 $r$，故在有限维中迹范数绝对收敛。若 $t_m>0$，把尾和按其迹归一化为态 $\Xi_{>m}$，得到

$$
\Xi_\infty=(1-t_m)\Xi_m+t_m\Xi_{>m}.
$$

两态距离不超过一，所以结论成立；尾迹为零时两态相同。这允许终端操作读取时间、端口并处理终端系统，前提是两种比较使用同一组 $\Lambda_{n,x}$。$\square$

**定理 32.4（相对尾界消去稀有事件的小分母）。** 取第 19.2 条的 $M\ge1$、$0<q<1$，记 $\varepsilon_m=q^{\lfloor m/M\rfloor}$。若 $m\ge M$，则对每个 $r_\rho>0$ 的原空间来源都有

$$
(1-\varepsilon_m)R\le H_m\le R,
\qquad h_m(\rho)>0,
\qquad t_m(\rho)\le\varepsilon_m.
$$

给定 $0<\eta<1$，选择

$$
m=M\left\lceil\frac{\log(1/\eta)}{\log(1/q)}\right\rceil
$$

足以同时使定理 32.2 和推论 32.3 的误差不超过 $\eta$，不要求各来源的最终点击概率具有共同正下界。

证明。引理 31.2 与 $\mathcal A^m(R)\le\varepsilon_mR$ 给出算子夹逼；与 $\rho$ 取迹，分子和分母具有同一 $r_\rho$ 因子，故相除后只剩 $\varepsilon_m$。所选整数使 $q^{\lfloor m/M\rfloor}\le\eta$。这不违反第 25 节的稀有事件放大：那里比较任意两个邻近输入或近似分支，这里比较同一已知过程、同一初态上的嵌套成功事件，并拥有相对于 $R$ 的统一算子尾界。有限样本或未标定仪器不自动供应 $R,M,q$。$\square$

## 33. 更长截止并不保证更便宜的条件态制备

**定义 33.1（每个截止的同一来源合同）。** 当 $P_m=P$ 且 $\dim P\mathcal H\ge2$ 时，来源固定为该支撑上的全部态。记

$$
\kappa_m=\frac{\lambda_{\max}(H_m|_P)}{\lambda_{\min}(H_m|_P)},
\qquad p_m^{\mathrm{opt}}=\kappa_m^{-1},\qquad L_m=\kappa_m.
$$

这两个操作量由第 28—29 节的证明用于正效果 $H_m$ 得到，分别对应单份未知输入的统一精确 CP 过滤，以及固定过滤的锐迹距离常数。它们与原过程实际在截止前点击的概率 $h_m(\rho)$ 分开记号。

**定理 33.2（截止制备成本的相对收敛界）。** 若 $0<\varepsilon<1$ 且 $(1-\varepsilon)R\le H_m\le R$，则 $P_m=P$，并有

$$
(1-\varepsilon)\kappa_R\le\kappa_m\le\frac{\kappa_R}{1-\varepsilon},
\qquad
\frac{1-\varepsilon}{\kappa_R}\le p_m^{\mathrm{opt}}
\le\frac1{(1-\varepsilon)\kappa_R}.
$$

因此在有限维固定仪器模型中，$L_m\to\kappa_R$ 且 $p_m^{\mathrm{opt}}\to\kappa_R^{-1}$。这些界不声称随 $m$ 单调。

证明。算子夹逼给出相同的核，且最小、最大本征值分别满足

$$
(1-\varepsilon)\lambda_{\min}(R|_P)
\le\lambda_{\min}(H_m|_P)\le\lambda_{\min}(R|_P),
$$

$$
(1-\varepsilon)\lambda_{\max}(R|_P)
\le\lambda_{\max}(H_m|_P)\le\lambda_{\max}(R|_P).
$$

分别用分子下界与分母上界、分子上界与分母下界得到谱比界，再取倒数。令 $\varepsilon=\varepsilon_m\to0$ 并应用定理 32.4，得到极限。$\square$

**命题 33.3（点击机会增加而统一制备成功率严格下降）。** 取正交基 $d,u,v$，记相应秩一投影为 $P_d,P_u,P_v$。定义

$$
Q_0=P_d+\frac1{\sqrt2}P_v,
\qquad Q_1=\sqrt{\frac35}|d\rangle\langle u|,
\qquad Q_2=\sqrt{\frac1{10}}|d\rangle\langle v|,
\qquad L=\sqrt{\frac25}(P_u+P_v).
$$

以 $Q_0,Q_1,Q_2$ 为同一未点击结果的 Kraus 算子，以 $L$ 为唯一点击分支。则

$$
H_m=\frac25P_u+\frac45(1-2^{-m})P_v,
\qquad R=\frac25P_u+\frac45P_v,
\qquad P_m=P=P_u+P_v\quad(m\ge1).
$$

每个原始来源的截止前点击概率随 $m$ 不下降，但在固定的全部支撑态来源类上，

$$
\boxed{
p_m^{\mathrm{opt}}=\frac1{2(1-2^{-m})}\downarrow\frac12,
\qquad L_m=2(1-2^{-m})\uparrow2.
}
$$

尤其 $m=1$ 时条件态可由恒等通道确定性制备，而最终点击条件态的最优最坏制备成功率为二分之一。

证明。各效果相加为 $P_d+(3/5+2/5)P_u+(1/2+1/10+2/5)P_v=I$，所以仪器合法。点击总效果为 $B=(2/5)(P_u+P_v)$。对 $aP_u+bP_v$，未点击拉回为 $(b/2)P_v$，于是截止递推给出 $u$ 坐标恒为 $2/5$，$v$ 坐标为几何和 $(2/5)\sum_{j=0}^{m-1}2^{-j}$。这证明效果公式及其单调性。对全部 $m\ge1$，最小本征值为 $2/5$，最大值为 $(4/5)(1-2^{-m})$，得到方框式。第一截止的效果为 $(2/5)I_P$，归一化过滤是恒等；最终效果的谱比为二，应用第 28.3 条。未读 Kraus 指标不被当作观察者记录，结论对带相干项的输入同样成立。$\square$

这给出本批的“AHH”：增加可取得事件的时间预算，会增加累计点击机会，却可能扩大不同输入的成功权重差异，使统一的条件态制备更困难、对输入误差更敏感。成本由截止效果的谱比决定，不能仅由事件总概率的单调性推断。

## 34. 截止何时只改变权重而不改变条件初态形状

**定理 34.1（同支撑下的截止无畸变判据）。** 固定某个 $m\ge1$，假设 $P_m=P$。下列条件等价：

- 对全部支撑于 $P$ 的状态，$\tau_m(\rho)=\tau_R(\rho)$。
- 存在 $0<c_m\le1$，使 $H_m=c_mR$。
- 对全部 $r_\rho>0$ 的原空间来源，$\mathbb P_\rho(\mathsf N\le m\mid\mathsf N<\infty)$ 为同一个常数 $c_m$。

证明。第二项使归一化分子和分母同时乘 $c_m$，推出第一项。反过来，对每个非零 $\psi\in P\mathcal H$，第一项给出 $G_m\psi$ 与 $G\psi$ 平行。因此 $G^{-1}G_m$ 保持每条射线，按第 28.2 条的线性论证为标量 $aI_P$，即 $G_m=aG$。两算子均正定，故 $a>0$，得到 $H_m=a^2R$；$H_m\le R$ 给出 $c_m=a^2\le1$。第二项与第三项的正向由概率比 $h_m(\rho)/r_\rho$ 得到；若第三项成立，所有支撑态都满足 $\operatorname{Tr}[\rho(H_m-c_mR)]=0$，纯态二次型分离 Hermitian 算子，故第二项成立。两效果在 $P^\perp$ 上都为零，等式因此属于原空间。$\square$

**定理 34.2（全部截止的来源独立性等价于几何等待律）。** 在同一固定重复仪器、$R\ne0$ 及全部 $r_\rho>0$ 来源类下，以下条件等价：

- 最终点击条件下的首次点击轮数分布不依赖初态。
- 存在 $0\le q<1$，使 $\mathcal A(R)=qR$。
- 存在 $0\le q<1$，使对每个 $m\ge1$ 都有 $H_m=(1-q^m)R$，且

$$
\mathbb P_\rho(\mathsf N=n\mid\mathsf N<\infty)
=(1-q)q^{n-1}\qquad(n\ge1).
$$

在这些条件下，每个有限截止都具有 $P_m=P$ 和 $\tau_m=\tau_R$。几何参数 $q$ 控制等待速度；条件态过滤的谱比仍由 $R|_P$ 控制。这里相等的是过滤后的初态；第 31 节的逐轮仪器仍带剩余截止标签，终端统计也不能据此直接等同。

证明。若条件等待分布来源独立，第一轮条件点击概率是常数 $c$，所以对全部支撑态 $\operatorname{Tr}(\rho B)=c\operatorname{Tr}(\rho R)$。$B$ 与 $R$ 都支撑于 $P$，效果分离给出 $B=cR$。$B\ne0$，否则所有有限点击效果 $\mathcal A^{n-1}(B)$ 都为零，与 $R\ne0$ 矛盾；故 $c>0$。又 $B\le R$，所以 $c\le1$。由 $R=B+\mathcal A(R)$ 得到第二项，取 $q=1-c$。第二项给出 $\mathcal A^m(R)=q^mR$，引理 31.2 得到 $H_m$ 公式；相邻截止概率相减得到几何律，显然不依赖初态。$q=0$ 时该律在第一轮集中，按整数幂约定 $q^0=1$。支撑与条件态结论由正比例关系得到。$\square$

**命题 34.3（单个来源的确定等待不能代替全来源判据）。** 存在固定二维仪器，使某个已知初态必在第二轮点击，但 $\mathcal A(R)$ 不是 $R$ 的标量倍数。

证明。取正交基 $u,v$，令 $Q=|u\rangle\langle v|$、$L=|u\rangle\langle u|$。其效果之和为 $P_v+P_u=I$，而 $Q^2=0$，所以 $R=I$。输入 $P_v$ 时第一轮未点击且后继为 $P_u$，第二轮必点击；输入 $P_u$ 则第一轮必点击。$\mathcal A(R)=Q^\dagger Q=P_v$ 不是标量恒等。因此受限到一个初态的等待律，不能支持第 34.2 条的全来源结论。$\square$

**说明 34.4（本批所连接的边界）。** 第 31 节把截止事件作为倒计时仪器的完整条件，包含随阶段变化的支撑和终端后继；第 32 节把条件输出误差交给同一过程的相对尾界；第 33 节区分点击机会与精确条件态制备；第 34 节给出截止不改条件态形状的比例效果判据及其几何等待特例。所用时空调和与量子 Doob 工具见第 31.5 条，谱过滤与迹距离工具见第 28—30 节。这里不主张文献原创性，没有新增 Lean，也未验证未知装置的识别、控制可得性或有限样本对这些精确效果的认证。

## 追加锚（本行以下为增补区）

## 35. 仪器校准误差怎样进入有限事件历史

第 31—34 节固定同一已知仪器，研究截止与最终点击条件之间的关系。本批允许仪器本身发生偏差：第 35 节控制有限历史，第 36—37 节给出无限等待的不连续及其有限查询障碍，第 38 节用共同尾界恢复长期输出的稳定性，第 39 节再区分稳定预测与精确暗空间识别。不改判前文；所有推导仍是有限维标准量子仪器模型中的纯理论文本。

[《递归关系观察：共同相位谱与接收边界》](RECURSIVE_RELATIONAL_OBSERVATION_PHASE_BOUNDARY.md)第 161—162 节已经用通道望远镜展开与统一余项，区分有限窗口连续和长期响应稳定。本批复用这两个方法，目标换为首次点击的完整停止输出，并把误差进一步连接到永久不可见方向的识别。

**定义 35.1（带记录和后继的单轮校准距离）。** 固定共同的系统空间 $\mathcal H$、有限点击集合 $X$、各点击后继空间及钟标签含义。每个模型的 $\mathcal H$ 都包含重复运行所需的全部活动记忆；比较对象是每轮使用同一通道的模型，不是只匹配单轮边缘的未知带记忆装置。仪器的完整输出通道为

$$
\mathfrak I(Y)=\mathcal N(Y)\oplus\bigoplus_{x\in X}\mathcal C_x(Y).
$$

不同直和块表示正交经典记录，块内保留量子后继。对共同输入输出空间上的两通道定义

$$
\delta(\Phi,\Psi)=
\sup_{\mathcal K,\,\rho\in\mathcal S(\mathcal K\otimes\mathcal H)}
D\bigl((\operatorname{id}_{\mathcal K}\otimes\Phi)(\rho),
(\operatorname{id}_{\mathcal K}\otimes\Psi)(\rho)\bigr),
\qquad D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1.
$$

上确界允许任意有限参考空间；对通道差，这就是半 diamond 距离。下文令 $\delta=\delta(\mathfrak I,\mathfrak J)$。距离约束是校准合同的前提，本批不把有限样本自动升级为这个精确上界。

对整数 $m\ge1$，保留首次点击标签及其后继的停止通道为

$$
\Omega_m^{\mathfrak I}(Y)=\mathcal N^m(Y)
\oplus\bigoplus_{n=1}^m\bigoplus_x
\mathcal C_x\mathcal N^{n-1}(Y).
$$

第一块的含义是截至第 $m$ 轮尚未点击；各 $(n,x)$ 块相互正交。完整性恒等式使它为 CPTP 通道。

**定理 35.2（有限停止历史的校准界）。** 两模型使用相同停止协议时，

$$
\boxed{
\delta(\Omega_m^{\mathfrak I},\Omega_m^{\mathfrak J})
\le \min\{1,m\delta\},
\qquad
\|H_m^{\mathfrak I}-H_m^{\mathfrak J}\|_\infty
\le \min\{1,m\delta\}.
}
$$

证明。把 $m$ 轮电路中的仪器逐轮替换。相邻两份混合电路仅有一次调用不同，该次调用之前的联合态相同。已点击块原样传递；未点击块为迹至多一的正算子。将其归一化并使用定义 35.1，该轮产生的半迹距离至多为该块迹乘 $\delta$，因而至多 $\delta$。其后相同的记录控制和停止续接均为 CPTP，不能增加距离。三角不等式给 $m\delta$；两归一化态的距离至多一。论证包含任意外部参考。

在输出上使用共同效果“已点击”，得到每个初态的截止概率差不超过同一界。取全部纯态二次型的绝对值上确界，即得 Hermitian 效果差的算子范数界。$\square$

**推论 35.3（仪器误差与稀有截止条件）。** 对共同初态 $\rho$，记两停止输出为 $\omega_I,\omega_J$，截止点击概率为 $h_I,h_J$。若两概率均正，按“截止前已点击”选择并归一化的完整记录后继满足

$$
\boxed{
\max\{h_I,h_J\}\,
D(\omega_{I\mid\mathrm{click}},\omega_{J\mid\mathrm{click}})
\le\min\{1,m\delta\}.
}
$$

若已知 $h_I\ge h_*>m\delta$，则 $h_J>0$，条件距离至多 $m\delta/h_*$。若初态也不同，右侧可改为 $\min\{1,D(\rho,\sigma)+m\delta\}$，相应正概率条件使用这个总误差。

证明。对两份停止输出应用同一个选择分支，再用第 25.2 条。不同初态时先用同一停止通道的收缩性比较输入，再替换仪器。$\square$

这说明第 32 节“同一过程的相对尾界不需点击概率下界”有明确范围：一般仪器误差进入归一化时，仍可能被稀有条件放大。

## 36. 任意小的单轮误差，可以改变最终是否点击

**命题 36.1（精确暗态与缓慢泄漏的共同实现）。** 在正交基 $b,d$ 上，记 $P_b,P_d$ 为对应投影。对 $0\le\gamma\le1$，取

$$
Q_\gamma=\sqrt{1-\gamma}\,P_d,
\qquad L_b=P_b,
\qquad L_{d,\gamma}=\sqrt\gamma\,P_d.
$$

分别作为一个未点击分支和两个点击分支的 Kraus 算子。即使 $\gamma=0$，仍保留零概率的点击标签 $d$。则

$$
\mathfrak I_\gamma=(1-\gamma)\mathfrak I_0+\gamma\mathfrak I_1,
\qquad \delta(\mathfrak I_\gamma,\mathfrak I_0)=\gamma,
$$

并且对每个 $m\ge1$，

$$
\boxed{
H_{m,\gamma}=P_b+[1-(1-\gamma)^m]P_d,
\qquad
\delta(\Omega_{m,\gamma},\Omega_{m,0})=1-(1-\gamma)^m.
}
$$

而最终点击效果为

$$
\boxed{R_0=P_b,\qquad R_\gamma=I\quad(\gamma>0).}
$$

证明。三个效果相加为 $P_b+(1-\gamma)P_d+\gamma P_d=I$，仪器合法。其三个输出块为 $(1-\gamma)P_dYP_d$、$P_bYP_b$ 和 $\gamma P_dYP_d$，直接给出凸分解。对任意参考联合态，两通道差只在未点击块和点击 $d$ 块中分别出现负、正的 $\gamma$ 倍压缩态，半迹范数为 $\gamma\operatorname{Tr}[(I_{\mathcal K}\otimes P_d)\rho]$。上确界为 $\gamma$，由输入 $P_d$ 达到。

未点击 $m$ 轮的效果为 $(1-\gamma)^mP_d$，所以得到 $H_{m,\gamma}$。两停止输出之差同样只有一份负的生存块和若干正的首次点击 $d$ 块，总正迹为 $[1-(1-\gamma)^m]\operatorname{Tr}[(I_{\mathcal K}\otimes P_d)\rho]$。取上确界得到停止距离。最后令 $m\to\infty$，分别处理 $\gamma=0$ 与 $\gamma>0$。$\square$

**推论 36.2（无限等待与零误差极限不能交换）。** 记暗基态输入的截止点击概率为 $h_m(\gamma)=1-(1-\gamma)^m$。则

$$
\lim_{\gamma\downarrow0}\lim_{m\to\infty}h_m(\gamma)=1,
\qquad
\lim_{m\to\infty}\lim_{\gamma\downarrow0}h_m(\gamma)=0.
$$

每个固定正 $\gamma$ 的平均首次点击轮数为 $1/\gamma$，且 $\|R_\gamma-R_0\|_\infty=1$。

证明。对正 $\gamma$，$d$ 输入的首次点击概率为 $\gamma(1-\gamma)^{n-1}$，给出几何等待与期望；固定 $m$ 时 $h_m(\gamma)\to0$。最终效果差为 $P_d$。$\square$

对任意 $0<\gamma_0\le1$，这一族没有共同趋零的等待尾界：每个有限 $m$ 都有

$$
\sup_{0<\gamma\le\gamma_0}
\|\mathcal A_\gamma^m(R_\gamma)\|_\infty
=\sup_{0<\gamma\le\gamma_0}(1-\gamma)^m=1.
$$

因此，“每台已知有限维装置分别具有收敛尾界”不能代替“对所有校准相容装置具有同一个尾界”。这里的差别已由同一二维模型实现，无需无穷维状态空间。

## 37. 允许自适应量子探针，有限查询仍不能统一认证精确黑暗

**定义 37.1（有限调用的校准实验）。** 在两个已知候选通道 $\mathfrak I_0$ 与 $\mathfrak I_\gamma$ 之间作等先验二元判别，固定 $0<\gamma<1$。实验至多调用候选通道 $m\ge1$ 次，可使用任意有限辅助系统、已知初态、保留的经典记录、量子记忆及结果依赖的已知 CPTP 控制，最后输出一个判别结果。两候选下使用同一策略，每次调用都是对应的同一 CPTP 通道。

这里的接口是带经典结果的通道本身；不提供其环境纯化、不可访问的随机混合标签、通道逆或某个特定酉实现的相干受控调用。提前停止的实验可补齐无关调用并丢弃输出，转成恰好 $m$ 个调用槽。

**定理 37.2（任意自适应策略的精确最优错误率）。** 在定义 37.1 的合同下，最小平均错误率为

$$
\boxed{
P_{\mathrm{err}}^{\mathrm{opt}}(m,\gamma)
=\frac12(1-\gamma)^m.
}
$$

证明。把第 36.1 条的通道凸分解代入实验的每个调用槽。包括测量记录的整个确定性策略对每个槽线性，故最终两假设下的状态满足

$$
\sigma_\gamma=(1-\gamma)^m\sigma_0+
[1-(1-\gamma)^m]\tau
$$

，其中 $\tau$ 为某个密度矩阵：它是至少一个槽使用 $\mathfrak I_1$ 的全部合法混合电路输出的归一化凸组合。因而

$$
D(\sigma_\gamma,\sigma_0)
\le1-(1-\gamma)^m.
$$

等先验 Holevo–Helstrom 判别式给错误率至少 $(1-\gamma)^m/2$。

达到方式是每次准备 $P_d$ 并保留结果；也可在未点击时继续同一 $d$ 态。若有任何点击 $d$，判为正 $\gamma$；若全部未点击，判为零。零模型绝不误判，正模型仅以概率 $(1-\gamma)^m$ 被误判，故等先验错误率恰为方框值。$\square$

**推论 37.3（分辨微弱泄漏的查询量）。** 对目标平均错误率 $0<e<1/2$，必要且充分的调用次数满足

$$
\boxed{
m\ge
\left\lceil
\frac{\log(1/(2e))}{-\log(1-\gamma)}
\right\rceil.
}
$$

证明。将第 37.2 条的不等式 $(1-\gamma)^m/2\le e$ 取对数，注意 $\log(1-\gamma)<0$。$\square$

于是没有一个有限 $m$ 能对所有任意小的正 $\gamma$，把“精确暗态”与“最终必点击”以某个共同小于 $1/2$ 的平均错误率区分。这是给定访问接口下的统计障碍；若模型事先给出已知的正泄漏下界，公式本身就提供有限资源方案。该结论也不把一次“没看见”当作精确暗态证明。

## 38. 共同尾界把有限校准连接到长期输出

**定义 38.1（最终输出与有限删失输出）。** 对每个首次点击标签 $(n,x)$，固定一个将其后继送到共同有限空间 $\mathcal K$ 的 CPTP 读出 $\Lambda_{n,x}$；两模型使用相同的这族读出。沿用 $S_m=\mathcal A^m(I)$、$F=\lim_m S_m$ 和 $R=I-F$，置

$$
\begin{aligned}
\Phi_\infty^{\mathfrak I}(Y)
&=\left[\sum_{n\ge1,x}
\Lambda_{n,x}\mathcal C_x\mathcal N^{n-1}(Y)\right]
\oplus\operatorname{Tr}(FY),\\
\Phi_m^{\mathfrak I}(Y)
&=\left[\sum_{1\le n\le m,x}
\Lambda_{n,x}\mathcal C_x\mathcal N^{n-1}(Y)\right]
\oplus\operatorname{Tr}(S_mY).
\end{aligned}
$$

第一块汇集点击后读出，第二块为正交的一维旗标。无穷式的旗标表示永不点击；有限式中同一输出位置表示截至第 $m$ 轮未解决。有限式不宣称已经认证永不点击。若要保留无限多个原始时间标签，需另换无限记录接口，本定义没有给有限维接收器免费增加这种能力。

**定理 38.2（含任意参考的精确删失误差）。** 两个公式均定义 CPTP 通道，且

$$
\boxed{
\delta(\Phi_\infty^{\mathfrak I},\Phi_m^{\mathfrak I})
=\|\mathcal A^m(R)\|_\infty.
}
$$

证明。点击部分的有限和完全正，在未归一化 Choi 约定下，其 Choi 算子递增且迹等于 $\operatorname{Tr}H_m\le\dim\mathcal H$，所以在有限维空间收敛到正 Choi 算子，给出完全正极限。有限和的效果为 $H_m$，极限效果为 $R$；补上 $S_m$ 或 $F=I-R$ 的旗标后均保迹。

对任意参考联合态 $\rho$，无穷输出减有限输出具有两个正交块：点击块为正的迟到输出 $T_\rho$，旗标块为负的参考算子 $-V_\rho$。后者来自正泛函 $Y\mapsto\operatorname{Tr}[(S_m-F)Y]$，所以 $V_\rho\ge0$。两块的迹均为

$$
t_\rho=\operatorname{Tr}[(I_{\mathrm{ref}}\otimes\mathcal A^m(R))\rho].
$$

因此半迹范数恰为 $t_\rho$。其上确界为正算子 $\mathcal A^m(R)$ 的最大本征值，并由无参考的最大本征态达到。$\square$

**定理 38.3（两个校准相近模型的长期误差）。** 对任意 $m\ge1$，有

$$
\boxed{
\delta(\Phi_\infty^{\mathfrak I},\Phi_\infty^{\mathfrak J})
\le\min\left\{1,
 m\delta+
 \|\mathcal A_I^m(R_I)\|_\infty+
 \|\mathcal A_J^m(R_J)\|_\infty\right\}.
}
$$

最终点击效果差 $\|R_I-R_J\|_\infty$ 也满足同一个上界。

证明。有限删失输出是第 35 节停止输出的共同 CPTP 后处理：对点击标签使用 $\Lambda_{n,x}$，把未点击后继压为旗标。故有限输出距离至多 $m\delta$。在两端分别加入第 38.2 条的删失距离，三角不等式给第一项；两通道距离至多一。最后检验是否处于点击块，取全部输入态，即得效果差界。$\square$

**推论 38.4（共同模型类的连续性模量）。** 若一族校准候选模型具有共同的 $b_m\downarrow0$，满足

$$
\|\mathcal A_{\mathfrak I}^m(R_{\mathfrak I})\|_\infty\le b_m
\quad\text{对全部候选 }\mathfrak I,
$$

则上述两种长期误差均不超过

$$
\omega(\delta)=\min\{1,\inf_{m\ge1}(m\delta+2b_m)\},
\qquad \lim_{\delta\downarrow0}\omega(\delta)=0.
$$

若共同尾界具体为 $b_m=q^{\lfloor m/M\rfloor}$，其中 $M\ge1$ 为整数、$0<q<1$，则对 $0<M\delta<1$，令

$$
k=\left\lceil\frac{\log(1/(M\delta))}{\log(1/q)}\right\rceil,
\qquad m=Mk,
$$

可取显式上界

$$
\boxed{\min\{1,M\delta(k+2)\}.}
$$

证明。先固定一个使 $2b_m$ 任意小的 $m$，再令 $\delta\downarrow0$，得到模量收敛。几何情形中 $q^k\le M\delta$，代入第 38.3 条即可；$\delta=0$ 时由任意 $m$ 的界及 $b_m\to0$ 得零误差。$\square$

共同尾界是一组足够条件，不是所有模型族稳定性的必要条件。它必须覆盖全部仍被校准资料允许的装置；第 19 节对单个固定模型取得的常数，不能未经证明就充当这一族的共同常数。先取有限前缀、再用共同余项控制极限的思路，与相位边界卷第 162 节相同；这里的余项是可明确识别的迟到点击效果。

## 39. 长期概率稳定，仍不等于精确暗空间稳定

**命题 39.1（零等待尾项仍允许暗空间突变）。** 取正交基 $d,u,v$。对 $0\le\varepsilon\le1$，用同一个未点击结果的两个 Kraus 算子及两个点击分支

$$
Q_0=P_d,
\qquad Q_1=\sqrt{1-\varepsilon}|d\rangle\langle u|,
\qquad L_u=\sqrt\varepsilon P_u,
\qquad L_v=P_v.
$$

则全部点击只能发生在第一轮，且

$$
\boxed{
R_\varepsilon=\varepsilon P_u+P_v,
\qquad \mathcal A_\varepsilon^m(R_\varepsilon)=0\quad(m\ge1).
}
$$

相对于零参数，完整单轮距离与最终输出距离均为 $\varepsilon$；最终输出此处使用恒等终端读出。然而

$$
\mathcal D_0=\operatorname{span}\{d,u\},
\qquad \mathcal D_\varepsilon=\operatorname{span}\{d\}\quad(\varepsilon>0),
\qquad
\|P_{\mathcal D_\varepsilon}-P_{\mathcal D_0}\|_\infty=1\quad(\varepsilon>0).
$$

证明。效果之和为 $P_d+(1-\varepsilon)P_u+\varepsilon P_u+P_v=I$。每次未点击后的量子态都支撑于 $d$，此后不会点击。因此 $R_\varepsilon$ 就是首轮点击效果，所有迟到尾项为零。对任意参考输入，两仪器差为未点击块减少 $\varepsilon$ 倍的 $u$ 压缩态经 $|d\rangle\langle u|$ 运输的结果，以及点击 $u$ 块增加同迹的正算子，距离为 $\varepsilon$ 乘输入的 $u$ 权重。上确界由 $P_u$ 达到。最终输出中，这两块分别是未点击旗标和点击态，同样得到距离 $\varepsilon$。核空间由 $R_\varepsilon$ 的对角式直接读出。$\square$

这个例子没有隐藏很长的等待：从 $u$ 输入，微弱点击失败后会永久进入 $d$。其区别是某个方向的最终点击概率从精确零变成任意小的正数。因此，共同等待尾界控制的是长期输出的近似误差，不能独自控制精确核的维数。

**引理 39.2（共同正谱隙控制支撑投影）。** 设 $R,S$ 为同一有限维空间上的正效果，$P=\operatorname{supp}R$、$Q=\operatorname{supp}S$。若已知同一个 $g>0$ 满足

$$
R\ge gP,\qquad S\ge gQ,
$$

则

$$
\boxed{
\|P-Q\|_\infty\le
\min\left\{1,\frac{\|R-S\|_\infty}{g}\right\}.
}
$$

当 $\|R-S\|_\infty<g$ 时，两支撑具有相同维数。允许其中一个效果为零；上述假设在零支撑上按通常方式理解。

证明。记 $a=\|R-S\|_\infty$。对 $z\in\ker R$，有 $Sz=(S-R)z$，所以 $\|Sz\|\le a\|z\|$。$S$ 在 $Q$ 上的本征值至少为 $g$，从而 $\|Sz\|\ge g\|Qz\|$，得到 $\|Q(I-P)\|\le a/g$。交换两个效果得 $\|(I-Q)P\|\le a/g$。投影恒等式

$$
(P-Q)^2=P(I-Q)P+(I-P)Q(I-P)
$$

在 $P\oplus(I-P)$ 上分块，故

$$
\|P-Q\|=\max\{\|(I-Q)P\|,\|Q(I-P)\|\}.
$$

这证明所需界；投影差的范数至多一。若其范数小于一，$Q$ 在 $P$ 的像上没有非零核，$P$ 在 $Q$ 的像上也没有非零核，有限维单射比较给出秩相等。$\square$

**推论 39.3（校准到暗方向的两层充分条件）。** 若两候选仪器同时满足第 38.4 条的共同尾界，且其最终点击效果都具有第 39.2 条的共同正谱隙 $g$，则

$$
\boxed{
\|P_{\mathcal D_I}-P_{\mathcal D_J}\|_\infty
\le\min\{1,\omega(\delta)/g\}.
}
$$

若 $\omega(\delta)<g$，两候选具有相同暗空间维数。

证明。第 38.4 条控制最终点击效果的差，第 39.2 条控制其支撑投影；暗投影为支撑投影的补，范数差相同。$\square$

本批的“AHH”是两个不同的极限门槛：共同迟到尾界保证有限观察一致逼近长期事件，共同正谱隙进一步保证近似效果支持稳定的精确可见／不可见分类。第 36 节的正参数模型具有恒等最终效果，却缺少跨参数的共同等待尾界；第 39.1 条具有零等待尾项，却缺少共同正谱隙。两种关系不能彼此替代。以测量精度定义“近似暗方向”又是另一项任务，不能悄悄替换这里的精确核。

**说明 39.4（文献、接口与结论范围）。** 标准工具与本批的连接范围如下。

- John Watrous，[*The Theory of Quantum Information*，第 3 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf)：第 3.4 定理给出 Holevo–Helstrom 二态判别；第 3.3 节讨论带辅助系统的通道距离与判别。第 35 节和第 37 节使用这些成熟工具，逐轮替换论证也复用仓内相位边界卷第 161.1 条的方法。
- Gus Gutoski、John Watrous，[*Toward a General Theory of Quantum Games*](https://arxiv.org/abs/quant-ph/0611234v2)：给出保留量子记忆的多轮策略及其正算子表示。第 37 节的访问合同属于此类多轮量子交互；精确错误率由本文具体通道凸分解直接证明，不把一般策略表示冒称为该例的现成闭式。
- Ruoyu Yin、Qingyuan Wang、Eli Barkai，[*Instability in the quantum restart problem*](https://arxiv.org/abs/2301.06100v2)：研究重复监测量子游走的重启优化不稳定。其目标是最优重启时间及平均击中时间，不直接提供第 36 节的最终点击效果不连续定理。
- 第 38 节使用有限前缀加共同尾项的稳定性方法；第 39.2 条是自包含的有限维谱投影扰动估计。本批在首次事件接口上连接这些工具及两个显式反例，不主张文献原创性。

所有距离结论均依赖声明的共同记录、量子后继、参考系统和重复调用合同。本批没有取得实验校准置信区间，没有认证某个实际装置的共同尾界或谱隙，也没有新增 Lean、消化覆盖或冻结结果。

## 追加锚（本行以下为增补区）

## 40. 紧致装置族上的长期连续性与共同尾界恰好等价

第 38—39 节给出了共同尾界及正谱隙的充分保证。本批增加装置族的紧性，确定何时这些保证能够反向刻画连续性；随后用同一个三能级仪器，区分长期输出、条件等待和一阶矩的稳定性。全部结论仍限于声明的有限维仪器合同，不改判前文。

**定义 40.1（连续的紧致仪器族）。** 固定非空紧度量空间 $\Theta$、有限维活动空间 $\mathcal H$、有限点击标签集及各后继空间。对每个 $\theta\in\Theta$，给定完整带记录通道 $\mathfrak I_\theta$，且 $\theta\mapsto\mathfrak I_\theta$ 在第 35.1 条的半 diamond 距离下连续。每个模型包含重复运行所需的全部活动记忆，并在全部轮次重复自身同一仪器。

对各参数沿用

$$
\mathcal A_\theta=\mathcal N_\theta^*,\qquad
R_\theta=I-F_\theta,\qquad
H_{m,\theta}=I-\mathcal A_\theta^m(I),\qquad
R_{m,\theta}=R_\theta-H_{m,\theta}=\mathcal A_\theta^m(R_\theta).
$$

固定第 38.1 条的同一族事件依赖 CPTP 读出，送到共同有限空间，并保留与点击输出正交的未解决／永不点击旗标。所得通道记为 $\Phi_{m,\theta}$、$\Phi_{\infty,\theta}$。仪器族的紧性与连续性属于已给定的模型合同，不从有限样本自动推出。

**引理 40.2（单调连续余项的有限覆盖判据）。** 设紧空间 $\Theta$ 上的连续实函数 $f_m\ge0$ 随 $m$ 递减，并逐点趋零。则 $\sup_\theta f_m(\theta)\to0$。

证明。给定 $\eta>0$，开集 $U_m=\{\theta:f_m(\theta)<\eta/2\}$ 递增，并覆盖 $\Theta$。紧性给有限子覆盖，取其最大指标 $M$，便有 $U_M=\Theta$。因此所有 $m\ge M$ 都满足 $\sup_\theta f_m(\theta)\le\eta/2<\eta$。$\square$

这是 Dini 定理所需的单调紧性机制；[《递归关系观察：可执行上下文几何》](RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md)第 45.5 节已在共同来源检验中使用相关有限网方法。这里将其接到迟到点击效果。

**定理 40.3（长期事件的四个等价接口）。** 在定义 40.1 下，以下条件等价：

- $\theta\mapsto R_\theta$ 在算子范数下连续。
- $\displaystyle\lim_{m\to\infty}\sup_{\theta\in\Theta}\|R_{m,\theta}\|_\infty=0$。
- $\theta\mapsto\Phi_{\infty,\theta}$ 在半 diamond 距离下连续。
- $\displaystyle\lim_{m\to\infty}\sup_{\theta\in\Theta}\delta(\Phi_{\infty,\theta},\Phi_{m,\theta})=0$。

证明。每个固定 $m$ 的 $H_{m,\theta}$ 与 $\Phi_{m,\theta}$ 都连续：第 35.2 条控制停止通道，效果选择和共同读出保持连续性。

假设第一项。$f_m(\theta)=\|R_\theta-H_{m,\theta}\|_\infty$ 连续，正算子余项递减且逐点趋零；正算子的算子范数保持此单调性。引理 40.2 推出第二项。反过来，第二项使 $R_\theta$ 为连续函数 $H_{m,\theta}$ 的一致极限，故连续。

第 38.2 条的精确恒等式使第二与第四项等价。第四项使最终通道为连续有限通道的一致极限，推出第三项。最后，对最终通道使用“在点击块”这一共同效果，得到

$$
\|R_\theta-R_\eta\|_\infty
\le\delta(\Phi_{\infty,\theta},\Phi_{\infty,\eta}),
$$

故第三项推出第一项。$\square$

这里的正交旗标承担了反向推论：若把点击与永不点击全都压成同一个固定输出，所得常值通道当然连续，却不再包含最终点击效果。

**命题 40.4（紧性与已知速率是两项不同条件）。** 去掉装置族的紧性，连续的最终点击效果不必具有共同趋零尾界。

证明。取第 36.1 条仪器，限制 $\gamma\in(0,1]$。这是连续但非紧的参数族，$R_\gamma=I$ 恒定；对每个固定 $m$，迟到尾范数的上确界仍为一。$\square$

定理 40.3 的有限覆盖证明也没有输出可计算的截止。若要得到数值期限，仍需有效的参数覆盖、可核对的尾估计或其他定量结构。紧集、连续函数与存在量本身，不是已经取得的实验停止证书。

## 41. 连续事件效果上的暗空间稳定与统一条件等待

**定理 41.1（紧族上的支撑、秩与正谱隙）。** 在定义 40.1 下，额外假设 $R_\theta$ 连续，置 $P_\theta=\operatorname{supp}R_\theta$。以下条件等价：

- $\theta\mapsto P_\theta$ 在算子范数下连续。
- $\theta\mapsto\operatorname{rank}R_\theta$ 局部常值。
- 存在同一个 $g>0$，使全部参数满足 $R_\theta\ge gP_\theta$。

允许零效果；不要求不同连通分支具有相同秩。

证明。若投影连续，对每个 $\theta_0$，存在邻域使 $\|P_\theta-P_{\theta_0}\|<1$。第 39.2 条证明中的投影单射论证给出两秩相等，故秩局部常值。

若秩局部常值，固定 $\theta_0$。秩为零时，在一个邻域内全部效果为零，该邻域可取任意正谱隙常数。秩为 $r>0$ 时，令 $a>0$ 为 $R_{\theta_0}$ 的最小正本征值。取秩恒为 $r$ 且 $\|R_\theta-R_{\theta_0}\|<a/2$ 的邻域。Hermitian 本征值的极小极大原理给每个按序本征值的变化不超过算子范数差；因此该邻域内的 $r$ 个正本征值均至少为 $a/2$。这些邻域覆盖紧空间，选有限子覆盖，再取其正下界的最小值，得到共同 $g>0$。

最后，共同谱隙和第 39.2 条给

$$
\|P_\theta-P_\eta\|_\infty
\le\frac{\|R_\theta-R_\eta\|_\infty}{g},
$$

由效果连续性得到投影连续。$\square$

若 $\Theta$ 连通，局部常秩进一步给全族同秩；在两个离散参数分别取零效果与一个秩一投影，则可有不同秩而仍满足本定理。效果连续性也不可省略：第 36 节的闭参数区间具有共同正谱隙一，但最终效果本身在零参数不连续。

“局部常秩”不能仅以“每个连通分支上常秩”替代。将第 39.1 条仪器限制到紧参数集 $\{0\}\cup\{1/n:n\ge1\}$，每个连通分支都是单点，但零参数的任何邻域仍含两种秩；局部常值在此失败。

**定理 41.2（共同谱隙把绝对尾界升级为条件几何尾界）。** 在定理 41.1 的等价条件成立时，存在同一个整数 $M\ge1$，使对全部参数及 $m\ge0$，

$$
\boxed{
0\le R_{m,\theta}\le2^{-\lfloor m/M\rfloor}R_\theta.
}
$$

从而，对所有 $\operatorname{Tr}(\rho R_\theta)>0$ 的参数—来源对，

$$
\mathbb P_{\theta,\rho}(\mathsf N>m\mid\mathsf N<\infty)
\le2^{-\lfloor m/M\rfloor},
\qquad
\mathbb E_{\theta,\rho}[\mathsf N\mid\mathsf N<\infty]\le2M.
$$

证明。定理 40.3 给共同趋零的绝对尾界，选 $M$ 使 $\|R_{M,\theta}\|\le g/2$ 对全部参数成立。由于 $0\le R_{M,\theta}\le R_\theta$，其支撑包含于 $P_\theta$，故

$$
R_{M,\theta}\le(g/2)P_\theta\le R_\theta/2.
$$

对每个参数重复应用正映射 $\mathcal A_\theta$，得到 $R_{kM,\theta}\le2^{-k}R_\theta$；块内再用 $\mathcal A_\theta^j(R_\theta)\le R_\theta$，推出全部 $m$。与初态取迹并除以正的最终点击概率给条件尾界，按长度 $M$ 分块求尾和得 $2M$。零效果参数没有需定义的正概率条件来源。$\square$

本定理提供充分结构，不把“共同条件等待界”反称为“暗空间秩必稳定”。第 39.1 条的仪器全部点击只在第一轮，条件等待具有共同界一，暗空间维数仍在零参数变化。

## 42. 同一个紧致三能级族：概率连续，稀有条件等待失控

**定义 42.1（弱点击与缓慢退出的共同仪器）。** 在正交基 $d,u,v$ 上，对 $0\le\varepsilon\le1$ 定义

$$
Q_{0,\varepsilon}=P_d+\sqrt{1-\varepsilon}\,P_u,
\qquad
Q_{1,\varepsilon}=\sqrt{\varepsilon(1-\varepsilon)}|d\rangle\langle u|,
\qquad
L_{u,\varepsilon}=\varepsilon P_u,
\qquad L_v=P_v.
$$

前两个 Kraus 算子属于同一个未点击结果，后两个分别产生点击记录 $u,v$。这里点击 $u$ 的效果是 $\varepsilon^2P_u$，振幅与概率不能混用。

**命题 42.2（所有效应来自同一完整仪器）。** 上述仪器合法，且完整带记录通道随 $\varepsilon\in[0,1]$ 连续。它满足

$$
\boxed{
R_\varepsilon=\varepsilon P_u+P_v,
\qquad
H_{m,\varepsilon}=\varepsilon[1-(1-\varepsilon)^m]P_u+P_v,
\qquad
R_{m,\varepsilon}=\varepsilon(1-\varepsilon)^mP_u\quad(m\ge1).
}
$$

证明。四个效果在 $u$ 方向之和为

$$
(1-\varepsilon)+\varepsilon(1-\varepsilon)+\varepsilon^2=1,
$$

在 $d,v$ 方向分别为一，所以完整性成立。Kraus 算子是同一有限维空间上的连续矩阵族，故对应通道连续。总点击效果是 $B_\varepsilon=\varepsilon^2P_u+P_v$，并且对对角效果有

$$
\mathcal A_\varepsilon(aP_u+bP_v)=(1-\varepsilon)aP_u.
$$

于是第一轮的 $v$ 点击效果为 $P_v$，$u$ 的第 $n$ 轮首次点击效果为 $\varepsilon^2(1-\varepsilon)^{n-1}P_u$。有限几何和与其极限给出方框式；$\varepsilon=0$ 时 $u$ 点击始终为零，单独代入得到同一效果公式。$\square$

**定理 42.3（共同绝对尾的精确多项式包络）。** 对每个 $m\ge1$，定义 42.1 的仪器族满足

$$
\boxed{
\sup_{0\le\varepsilon\le1}\|R_{m,\varepsilon}\|_\infty
=\frac{m^m}{(m+1)^{m+1}}
\sim\frac1{\mathrm e\,m}.
}
$$

因此最终输出在这个紧族上连续，有限删失输出一致逼近最终输出；却不存在常数 $C<\infty$、整数 $M\ge1$ 和 $0<q<1$，使全部参数及 $m\ge1$ 同时满足 $\|R_{m,\varepsilon}\|\le Cq^{\lfloor m/M\rfloor}$。

证明。对 $f_m(\varepsilon)=\varepsilon(1-\varepsilon)^m$ 求导，内部导数为

$$
f_m'(\varepsilon)=(1-\varepsilon)^{m-1}[1-(m+1)\varepsilon].
$$

端点值为零，唯一内部最大点为 $\varepsilon=1/(m+1)$，代入即得精确式。其乘以 $m$ 后趋于 $\mathrm e^{-1}$。效果 $R_\varepsilon$ 连续，定理 40.3 给出通道结论。若存在所述共同几何界，取 $m=kM$，则左侧渐近于 $1/(\mathrm e kM)$，右侧为 $Cq^k$；指数衰减不可能支配这一正的多项式尾。$\square$

**定理 42.4（小事件权重与长条件等待能够同时出现）。** 对 $\varepsilon>0$ 和共同初态 $P_u$，有

$$
\mathbb P_\varepsilon(\mathsf N=n)
=\varepsilon^2(1-\varepsilon)^{n-1},
\qquad
\mathbb P_\varepsilon(\mathsf N<\infty)=\varepsilon,
$$

$$
\boxed{
\mathbb P_\varepsilon(\mathsf N>m\mid\mathsf N<\infty)
=(1-\varepsilon)^m,
\qquad
\mathbb E_\varepsilon[\mathsf N\mid\mathsf N<\infty]=\frac1\varepsilon.
}
$$

所以不存在统一趋零的条件等待尾界，即使第 42.3 条的绝对尾项已经一致趋零。

证明。首次点击效果在命题 42.2 的证明中已算出；在 $P_u$ 上取迹，再除以最终点击概率 $\varepsilon$，得到成功参数 $\varepsilon$ 的几何律。对每个固定 $m$，$\sup_{0<\varepsilon\le1}(1-\varepsilon)^m=1$。在 $\varepsilon=0$ 处最终点击概率为零，条件等待没有定义，不能人为补一个值参与连续性断言。$\square$

**命题 42.5（等待算子有统一界，却在端点跳变）。** 第 19 节的等待算子在该族上为

$$
\boxed{
T_\varepsilon=\sum_{m\ge0}R_{m,\varepsilon}
=P_u+P_v\quad(\varepsilon>0),
\qquad T_0=P_v.
}
$$

尤其 $0\le T_\varepsilon\le I$ 对全部参数成立，但 $T_\varepsilon$ 在零参数不连续。

证明。$m=0$ 的项为 $R_\varepsilon=\varepsilon P_u+P_v$。对正 $\varepsilon$，$u$ 方向的全部尾和为 $\varepsilon\sum_{m\ge0}(1-\varepsilon)^m=1$；零参数时该方向每一项都为零。$\square$

对 $P_u$ 来源，有限点击的一阶矩是 $\sum_n n\mathbb P(\mathsf N=n)=1$，而在零参数为零。它等于“点击概率 $\varepsilon$”乘“点击条件下平均轮数 $1/\varepsilon$”。同一个实际模型中，事件质量趋零与等待长度发散相互抵消；概率收敛因此不能单独交换一阶矩的极限。

## 43. 长期时间成本的稳定性由加权尾项刻画

**定义 43.1（只统计有限点击的时间矩）。** 令

$$
E_{n,\theta}=\sum_x E_{n,x,\theta}
=\mathcal A_\theta^{n-1}(B_\theta),
\qquad
M_{m,\theta}=\sum_{n=1}^m nE_{n,\theta}.
$$

本节以探测轮数为时间单位；实际历时的矩还需钟标定及相应加权尾合同。本节将记录函数 $Y$ 定义为：有限轮次点击时取 $Y=\mathsf N$，永不点击时取 $Y=0$。其期望为

$$
\mathbb E_{\theta,\rho}Y
=\operatorname{Tr}(\rho T_\theta),
\qquad
T_\theta=\sum_{n\ge1}nE_{n,\theta}
=\sum_{k\ge0}R_{k,\theta}.
$$

每个单独有限维模型的 $T_\theta$ 有限，由第 19.2 条保证；共同有界性尚未假设。这个量是有限点击子概率律的一阶矩。永不点击分支的零值属于统计约定；有限截止只能读到尚未点击。若把永不点击的等待值定义为 $+\infty$，只要该事件有正概率，相应扩展期望就是无穷，不能与这里的 $T_\theta$ 混用。

置加权迟到效果

$$
Z_{m,\theta}=T_\theta-M_{m,\theta}
=\sum_{n>m}nE_{n,\theta}\ge0.
$$

**引理 43.2（概率尾与时间矩尾的精确连接）。** 对任意单个模型及 $m\ge0$，有

$$
\boxed{
Z_m=mR_m+\mathcal A^m(T),
\qquad
R_m\le\frac{T}{m+1}.
}
$$

证明。对全部正算子和逐项使用 $n=\sum_{k=0}^{n-1}1$，有

$$
\sum_{n\ge1}nE_n
=\sum_{k\ge0}\sum_{n>k}E_n
=\sum_{k\ge0}R_k=T.
$$

第 19 节的有限性保证这些正算子和在范数中收敛。再将 $n>m$ 写成 $n=m+(n-m)$，得到

$$
Z_m=m\sum_{n>m}E_n+\sum_{k\ge m}R_k
=mR_m+\mathcal A^m(T).
$$

最后，由 $T\ge\sum_{n>m}nE_n\ge(m+1)\sum_{n>m}E_n$ 得第二式。$\square$

**定理 43.3（紧族的一阶矩连续性等价于共同加权尾收敛）。** 在定义 40.1 下，不预先假设 $R_\theta$ 连续。以下条件等价：

- $\theta\mapsto T_\theta$ 在算子范数下连续。
- $\displaystyle\lim_{m\to\infty}\sup_{\theta\in\Theta}\|Z_{m,\theta}\|_\infty=0$。
- 全部参数和全部初态的有限点击时间记录满足

$$
\lim_{m\to\infty}
\sup_{\theta,\rho}
\mathbb E_{\theta,\rho}[Y\,\mathbf1_{\{Y>m\}}]=0.
$$

证明。每个 $M_{m,\theta}$ 是有限次仪器复合效果的有限和，所以连续。若 $T_\theta$ 连续，$\|T_\theta-M_{m,\theta}\|$ 是连续、递减且逐点趋零的非负函数；引理 40.2 得第二项。反过来，第二项使 $T_\theta$ 为连续 $M_{m,\theta}$ 的一致极限。

对每个参数和初态，加权尾期望为 $\operatorname{Tr}(\rho Z_{m,\theta})$。正算子对全部初态的迹上确界恰为其范数，因此第二项与第三项完全相同。$\square$

第三项就是这些非负时间记录分布的一致可积尾条件。这里无需假设不同装置的记录已经在同一个物理实验中耦合；每个期望取自各自声明的概率律，统一性是对这些概率律共同取上确界。

**推论 43.4（一阶矩连续比事件概率连续更强）。** 在定义 40.1 下，若 $T_\theta$ 连续，则 $R_\theta$ 及第 40 节的最终输出连续。反向一般不成立；即使全部 $T_\theta$ 共同有界也不成立。

证明。紧性给 $C=\sup_\theta\|T_\theta\|<\infty$。引理 43.2 得共同绝对尾界 $\|R_{m,\theta}\|\le C/(m+1)$，应用定理 40.3。第 42 节同时具有连续 $R_\varepsilon$、$T_\varepsilon\le I$ 与不连续的 $T_\varepsilon$，给出反向反例。$\square$

第 42 节的加权尾项还能直接算出：对 $m\ge1$，

$$
Z_{m,\varepsilon}=(1+m\varepsilon)(1-\varepsilon)^mP_u\quad(\varepsilon>0),
\qquad Z_{m,0}=0,
\qquad \sup_{0\le\varepsilon\le1}\|Z_{m,\varepsilon}\|=1.
$$

第一式由引理 43.2 代入 $T_\varepsilon=P_u+P_v$ 得到。$Z_{m,\varepsilon}\le T_\varepsilon\le I$ 给上界一；固定 $m$ 后令正 $\varepsilon\downarrow0$，达到上确界一。因此每个截止都遗漏了某些相容参数的近乎全部有限点击时间矩。

**定理 43.5（完整仪器校准到时间矩的有限—尾分解）。** 对两模型 $\mathfrak I,\mathfrak J$，令 $\delta=\delta(\mathfrak I,\mathfrak J)$。则对每个 $m\ge1$，

$$
\boxed{
\|T_I-T_J\|_\infty
\le m\min\{1,m\delta\}+\|Z_{m,I}\|_\infty+\|Z_{m,J}\|_\infty.
}
$$

若模型类具有共同的 $\|Z_{m,\theta}\|\le c_m\to0$，便有连续性模量

$$
\|T_I-T_J\|_\infty
\le\inf_{m\ge1}(m^2\delta+2c_m),
$$

右侧随 $\delta\downarrow0$ 趋零。

证明。在第 35 节停止输出上使用同一个记录函数：点击于 $n\le m$ 时取值 $n$，尚未点击时取零。其对应观察算子 $W_m$ 满足 $0\le W_m\le mI$。对任意两归一化输出 $\omega,\sigma$，效果 $W_m/m$ 给

$$
|\operatorname{Tr}[W_m(\omega-\sigma)]|\le mD(\omega,\sigma).
$$

第 35.2 条因而给 $\|M_{m,I}-M_{m,J}\|\le m\min\{1,m\delta\}$。分别加入两侧正尾 $Z_m$，三角不等式得到方框式。共同尾情形先选 $m$ 使 $2c_m$ 足够小，再令 $\delta$ 足够小。$\square$

**推论 43.6（统一条件几何尾也控制时间矩尾）。** 若全部模型共有 $R_{m,\theta}\le q^{\lfloor m/M\rfloor}R_\theta$，其中整数 $M\ge1$、$0<q<1$，置 $C=M/(1-q)$。则

$$
\boxed{
0\le Z_{m,\theta}\le
(m+C)q^{\lfloor m/M\rfloor}R_\theta.
}
$$

在定义 40.1 的紧族上，$T_\theta$ 因而连续。定理 41.2 是 $q=1/2$ 的一个共同实现条件。

证明。按长度 $M$ 分块求和得 $T_\theta\le CR_\theta$。正映射保持此序关系，所以 $\mathcal A_\theta^m(T_\theta)\le C R_{m,\theta}$。代入引理 43.2，并用 $R_\theta\le I$，得到共同趋零加权尾，应用定理 43.3。$\square$

## 44. 稀有而漫长的记录揭示了哪些稳定性层次

本批的“AHH”来自第 42 节同一个装置族和共同初态 $P_u$：点击总概率是 $\varepsilon$，在最终点击条件下，首次点击轮数的均值是 $1/\varepsilon$，有限点击时间矩在每个正参数却恒为一。把参数取到零以后，这个时间矩变成零。小概率没有消除时间成本，而是把它留在越来越稀有、越来越漫长的记录中。

几个任务因而具有不同的边界要求：

- 在连续紧致仪器族上，最终事件效果及带旗标终端通道的连续性，由共同绝对尾项趋零精确刻画。
- 已有连续最终效果时，暗投影连续性由局部常秩精确刻画；紧性把它升级成共同正谱隙。
- 条件等待还涉及对最终点击概率归一化。共同正谱隙配合绝对尾界足以得到共同相对几何尾，但第 42 节说明仅有绝对尾收敛不够。
- 有限点击时间矩的连续性，由共同加权尾项趋零精确刻画；单独的一阶矩共同有界不能代替它。

这四项分别保留概率、方向、条件分布和时间权重。它们不是给同一份读数换四个名称；第 42 节的显式公式使其中的区别可逐项核对。

**说明 44.1（成熟工具与本批连接）。** 引理 40.2 使用标准 Dini 机制。仓内上下文几何卷第 45.5 节已有紧性与单调收敛的相关应用；项目钉版 Mathlib 的 [Dini 源文件](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Topology/UniformSpace/Dini.lean)提供一般的连续单调函数一致收敛定理。本批只将其作为既有数学工具的来源，没有编译本批命题的 Lean 应用。

J. R. Norris 的 [*Probability and Measure*，第 6.2 节](https://www.statslab.cam.ac.uk/~james/Lectures/pm.pdf) 的引理 6.2.2 给出一致可积的尾判据，前文给出 $L^1$ 有界但不一致可积的例子，定理 6.2.3 连接一致可积与 $L^1$ 收敛。第 43 节在首次事件效果上给出完整算子推导；没有把不同参数下的随机变量未经耦合就直接套入同一概率空间上的收敛定理。

相关首次探测文献也区分了总探测概率、长时间尾和时间矩。Felix Thiel、David A. Kessler 的 [*Non-Hermitian and Zeno limit of quantum systems under rapid measurements*](https://arxiv.org/abs/2005.00464v1)比较重复投影监测与非 Hermitian 吸收模型的 Zeno 极限，并研究探测概率和时间矩；Qingyuan Wang、Ruoyu Yin、Eli Barkai 的 [*Temporal Interference from Topological Transitions in Monitored Quantum Dynamics*](https://arxiv.org/abs/2607.27045v1)研究投影监测返回中暗态转变附近的慢衰减与时间干涉。它们采用特定的酉传播与投影监测合同；第 42 节则允许同一未点击结果含多个 Kraus 分支，并把失败质量送入永久暗态。因此本文的显式公式由本例推导承担，不直接借用这些文献中的返回均值量子化或渐近式。

本批把上述成熟工具、有限维谱扰动和本卷第 19、35、38—39 节连接到同一仪器族及校准任务，不主张文献原创性。共同尾速率、正谱隙和有效参数覆盖的存在与实际取得仍有区别；正文没有认证未知实验装置，也没有新增 Lean、消化覆盖或冻结结果。

## 追加锚（本行以下为增补区）

## 45. 来源支撑与正尾项：一个满秩探针能够控制什么

第 40—44 节要求跨装置统一控制所有初态。本批先把允许的初态支撑写进任务，再研究只含酉传播和投影探测的返回过程。一个量子比特就能实现：最终点击概率始终为一，完整等待律在总变差中连续，平均返回轮数却从二跳为一。这个现象与上一批的低点击概率例子不同，不能全部归因于最终事件变得稀有。

**定义 45.1（允许来源的初始支撑）。** 保留第 40.1 条的非空紧参数空间 $\Theta$、连续完整仪器族 $\mathfrak I_\theta$ 及共同有限终端读出。另给非空允许初态集合 $\Gamma\subseteq\mathcal S(\mathcal H)$，置

$$
W=\operatorname{span}\{\operatorname{supp}\rho:\rho\in\Gamma\},
\qquad P_W\text{ 为 }W\text{ 的正交投影},
\qquad r=\dim W\ge1.
$$

这里 $W$ 只限定初始准备，后续演化可以离开 $W$；不在每一轮额外插入 $P_W$ 投影。对通道 $\Phi$，记 $\Phi|_W$ 为先将 $\mathcal L(W)$ 自然嵌入 $\mathcal L(\mathcal H)$、再作用 $\Phi$ 的通道。其半 diamond 距离仍允许初态与任意有限参考系统纠缠。

**引理 45.2（有限来源覆盖产生忠实正测试）。** 可从 $\Gamma$ 中选出 $k\le r$ 个状态及正权重，满足

$$
\bar\rho=\sum_{i=1}^k w_i\rho_i,
\qquad w_i>0,\quad\sum_iw_i=1,
\qquad\operatorname{supp}\bar\rho=W.
$$

令 $\lambda>0$ 为 $\bar\rho|_W$ 的最小本征值。对每个正算子 $A\ge0$，有

$$
\boxed{
\operatorname{Tr}(\bar\rho A)
\le\|P_WAP_W\|_\infty
\le\frac{\operatorname{Tr}(\bar\rho A)}\lambda.
}
$$

证明。从任意允许态的非零支撑开始；若已取支撑的张成还不等于 $W$，就再取一个支撑不包含在当前张成中的允许态。每次维数至少增加一，至多 $r$ 次得到 $W$。任取全正权重；若 $v\in W$ 对 $\bar\rho$ 的二次型为零，则每个非负加项都为零，故 $v$ 与所有已取支撑正交，只能为零。所以 $\bar\rho|_W$ 正定。

记 $A_W=P_WAP_W|_W\ge0$。由 $\operatorname{Tr}\bar\rho=1$ 得左界。又 $\bar\rho|_W\ge\lambda I_W$，故

$$
\operatorname{Tr}(\bar\rho A)
\ge\lambda\operatorname{Tr}(A_W)
\ge\lambda\|A_W\|_\infty,
$$

得到右界。$\square$

$\bar\rho$ 在此也可以只表示 $k$ 个允许来源读数的固定加权和。若要实际随机准备这份混合态，还须允许相应经典随机化；线性推导本身不增加准备权限。

**定理 45.3（忠实标量响应与完整来源支撑上的稳定性）。** 固定引理 45.2 的测试态 $\bar\rho$。下列条件等价：

- 标量 $a(\theta)=\operatorname{Tr}(\bar\rho R_\theta)$ 连续。
- $\theta\mapsto P_WR_\theta P_W$ 在算子范数下连续。
- $\displaystyle\sup_{\theta\in\Theta}\|P_WR_{m,\theta}P_W\|_\infty\longrightarrow0$。
- $\theta\mapsto\Phi_{\infty,\theta}|_W$ 在半 diamond 距离下连续。

此外，对每个参数及截止都有精确式及探针界

$$
\boxed{
\delta(\Phi_{\infty,\theta}|_W,\Phi_{m,\theta}|_W)
=\|P_WR_{m,\theta}P_W\|_\infty
\le\frac{\operatorname{Tr}(\bar\rho R_{m,\theta})}{\lambda}.
}
$$

证明。若第一项成立，标量余项

$$
f_m(\theta)=\operatorname{Tr}(\bar\rho R_\theta)
-\operatorname{Tr}(\bar\rho H_{m,\theta})
=\operatorname{Tr}(\bar\rho R_{m,\theta})
$$

连续、非负、递减且逐点趋零。第 40.2 条给共同趋零，再用引理 45.2 的正算子界得到第三项。第三项使压缩效果为连续有限效果 $P_WH_{m,\theta}P_W$ 的一致极限，推出第二项。第二项当然推出第一项。

第 38.2 条证明可在初态嵌入后直接使用：带参考的删失输出差仍是等迹的正、负正交块，最大迟到概率正是初始空间 $W$ 上压缩效果的最大本征值。这给出方框中的等式，无需 $W$ 对后续动力学不变。第三项于是使最终限制通道为连续有限限制通道的一致极限，推出第四项。第四项经共同点击旗标检验给第二项。最后的上界由引理 45.2 得到。$\square$

因此，若固定有限来源的最终点击响应均随参数连续，它们的支撑覆盖所产生的忠实加权测试也连续，便足以保证整个 $W$ 初态类的长期输出稳定；这包括这些初态所允许的相干叠加及外部参考。这里用的是正尾项的控制，不是由几个概率读数恢复全部矩阵元。

**定理 45.4（同一忠实测试对时间矩的判据）。** 在相同合同下，下列三项等价：

$$
\theta\longmapsto\operatorname{Tr}(\bar\rho T_\theta)\text{ 连续};
\qquad
\theta\longmapsto P_WT_\theta P_W\text{ 连续};
\qquad
\sup_\theta\|P_WZ_{m,\theta}P_W\|\longrightarrow0.
$$

这里 $T,Z_m$ 仍按第 43 节统计有限点击的轮数矩。

证明。首项使 $\operatorname{Tr}(\bar\rho Z_{m,\theta})$ 成为连续、递减、逐点趋零的非负函数，因为每个有限矩 $M_{m,\theta}$ 连续。Dini 机制与引理 45.2 推出第三项；第三项使压缩 $T$ 为连续压缩 $M_m$ 的一致极限，推出第二项；第二项取固定迹即得首项。$\square$

**命题 45.5（忠实稳定性测试不等于效果重建）。** 一个满秩初态的最终点击概率，不能一般确定完整最终点击效果。

证明。在量子比特上取 $R_+=|+\rangle\langle+|$ 与 $R_-=|-\rangle\langle-|$，其中 $|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$。两者可分别由点击 Kraus 算子 $L_\pm=R_\pm$ 和未点击算子 $Q_\pm=I-R_\pm$ 实现；未点击后进入该装置的暗子空间，故最终点击效果就是 $R_\pm$。满秩来源 $\bar\rho=I/2$ 对两者都给概率 $1/2$，但输入 $R_+$ 时两概率分别为一与零。甚至分别测试 $P_0,P_1$ 的全部首次点击概率，也不能区分这两份效果。$\square$

引理 45.2 不能套到一般 Hermitian 差 $R_+-R_-$：其忠实迹为零而算子非零。第 45.3 条是在连续有限前缀和正的单调余项之间搭桥，所得是模型族的稳定性判据；它没有把同一个初态变成信息完备层析，更没有把单次点击变成完整边界恢复。

## 46. 只用酉传播和投影监测，也能出现稳定点击与均值突变

本节使用 Grünbaum、Velázquez、A. H. Werner、R. F. Werner 的离散酉返回理论中已有的二态旋转例子，改写为本卷仪器记号；第 49.1 条给出原始出处及精确对应。新增连接在于来源支撑、统一尾项和固定记录抽样任务，不把返回均值的整数跳变作为本卷的新发现。

**定义 46.1（量子比特的首次返回）。** 取 $\mathcal H=\operatorname{span}\{|0\rangle,|1\rangle\}$，参数 $0\le\gamma\le1$，令

$$
U_\gamma=
\begin{pmatrix}
\sqrt{1-\gamma}&-i\sqrt\gamma\\
-i\sqrt\gamma&\sqrt{1-\gamma}
\end{pmatrix},
\qquad
Q_\gamma=P_1U_\gamma,
\qquad
L_\gamma=P_0U_\gamma.
$$

每轮先执行 $U_\gamma$，再检测是否处于 $|0\rangle$；点击即停止，未点击则继续。共同初态为 $P_0$。这是一轮酉演化后接理想投影的仪器，参数也可写成 $\gamma=\sin^2\theta$、$0\le\theta\le\pi/2$。时间仍按轮数计。

**定理 46.2（同一初态的精确返回律）。** 仪器完整且随参数连续。对正 $\gamma$，从 $P_0$ 出发的首次返回轮数满足

$$
\boxed{
p_\gamma(1)=1-\gamma,
\qquad p_\gamma(n)=\gamma^2(1-\gamma)^{n-2}\quad(n\ge2).
}
$$

在 $\gamma=0$ 处，$p_0(1)=1$，其余概率为零。所有参数均以概率一最终点击，点击后系统态均为 $P_0$。

证明。直接核对 $U_\gamma^\dagger U_\gamma=I$，所以 $Q_\gamma^\dagger Q_\gamma+L_\gamma^\dagger L_\gamma=I$；共同矩阵条目连续给完整通道连续。第一轮点击振幅为 $\sqrt{1-\gamma}|0\rangle$。对 $n\ge2$，有

$$
Q_\gamma^{n-1}|0\rangle
=-i\sqrt\gamma(\sqrt{1-\gamma})^{n-2}|1\rangle,
\qquad
L_\gamma Q_\gamma^{n-1}|0\rangle
=-\gamma(\sqrt{1-\gamma})^{n-2}|0\rangle.
$$

取模平方即得概率。对正 $\gamma$ 求和，后续概率总和为 $\gamma$，与第一轮的 $1-\gamma$ 相加为一。零参数时第一轮已经必点击。所有非零点击分支均沿 $|0\rangle$。当 $\gamma=1$，公式按非负整数幂约定读为第二轮必点击。$\square$

**定理 46.3（完整等待律接近，而平均轮数不接近）。** 将等待律视为 $\{1,2,\ldots\}$ 上的经典概率分布，则

$$
\boxed{
\operatorname{TV}(p_\gamma,p_0)=\gamma.
}
$$

但

$$
\boxed{
\mathbb E_\gamma\mathsf N=2\quad(\gamma>0),
\qquad \mathbb E_0\mathsf N=1.
}
$$

对正 $\gamma$ 还有

$$
\mathbb E_\gamma\mathsf N^2=2+\frac2\gamma,
\qquad
\operatorname{Var}_\gamma(\mathsf N)=\frac2\gamma-2.
$$

证明。第一轮概率比零模型少 $\gamma$，其余轮次的总概率为 $\gamma$，所以总变差为 $\gamma$。记 $q=1-\gamma$，对 $\gamma>0$ 使用

$$
\sum_{j\ge0}q^j=\frac1\gamma,
\quad\sum_{j\ge0}jq^j=\frac q{\gamma^2},
\quad\sum_{j\ge0}j^2q^j=\frac{q(1+q)}{\gamma^3}.
$$

将 $n=j+2$ 代入第二轮以后的概率和，得到

$$
\mathbb E\mathsf N=q+\gamma^2\sum_{j\ge0}(j+2)q^j=2,
\qquad
\mathbb E\mathsf N^2=q+\gamma^2\sum_{j\ge0}(j+2)^2q^j=2+2/\gamma.
$$

减去均值平方得到方差；零参数为常数轮数一。$\square$

**命题 46.4（全来源不连续与指定来源稳定并存）。** 这一仪器族的最终点击效果为

$$
R_\gamma=I\quad(\gamma>0),\qquad R_0=P_0.
$$

所以完整效果在零参数不连续，但允许来源类 $\Gamma=\{P_0\}$ 的最终点击概率恒为一，采用恒等终端读出并合并时间标签时，最终输出也恒为同一个点击态。

证明。对正 $\gamma$，$Q_\gamma$ 的像位于 $|1\rangle$，且 $Q_\gamma|1\rangle=\sqrt{1-\gamma}|1\rangle$，因此对任意输入向量 $Q_\gamma^m\psi\to0$；所有初态最终点击。零参数下 $Q_0=P_1$，初态的 $|1\rangle$ 部分永久不点击，故效果为 $P_0$。指定初态结论由第 46.2 条给出。$\square$

本例的初始允许支撑 $W=\operatorname{span}\{|0\rangle\}$ 不是正参数下的未点击不变空间：第一次未点击后状态为 $P_1$。第 45 节只限制初态，所以仍适用。它保证的是 $W$ 任务的稳定性，不能扩成未被允许来源覆盖的全空间稳定性。

## 47. 稀有的迟到分支可以携带一个完整单位的平均时间

**定理 47.1（完整等待律一致可截断）。** 对第 46 节的共同初态，记 $s_m(\gamma)=\Pr_\gamma(\mathsf N>m)$。对 $m\ge1$，

$$
s_m(\gamma)=\gamma(1-\gamma)^{m-1}.
$$

其中 $s_m(0)=0$，整数零次幂取一。其精确统一尾界为

$$
\boxed{
\sup_{0\le\gamma\le1}s_1(\gamma)=1,
\qquad
\sup_{0\le\gamma\le1}s_m(\gamma)
=\frac{(m-1)^{m-1}}{m^m}\sim\frac1{em}\quad(m\ge2).
}
$$

映射 $\gamma\mapsto p_\gamma$ 在整个 $[0,1]$ 上按总变差连续。

证明。对 $n>m$ 的几何级数求和得到尾公式。若 $m\ge2$，函数 $\gamma(1-\gamma)^{m-1}$ 的内部导数与 $1-m\gamma$ 同号，两端为零，故最大值在 $\gamma=1/m$ 取得。渐近式来自 $(1-1/m)^{m-1}\to e^{-1}$。$m=1$ 时尾概率就是 $\gamma$。

把 $n>m$ 的所有记录替换为共同删失符号 $\partial$，得到有限字母表上的分布 $p_\gamma^{(m)}$；将它与原分布都放在 $\mathbb N_{\ge1}\cup\{\partial\}$ 上。每个有限分布依赖参数连续，且

$$
\operatorname{TV}(p_\gamma,p_\gamma^{(m)})=s_m(\gamma)
$$

一致趋零。三角不等式便给完整等待律的总变差连续性。$\square$

这里只给无穷记录律的数学表示和有限删失近似，不宣称有限装置能够存下无界的原始轮数标签。

**定理 47.2（概率尾收敛，但加权尾不收敛）。** 定义

$$
z_m(\gamma)=\mathbb E_\gamma[\mathsf N\,\mathbf1_{\{\mathsf N>m\}}].
$$

对 $m\ge1$、$\gamma>0$，

$$
\boxed{
z_m(\gamma)=(1+m\gamma)(1-\gamma)^{m-1},
\qquad z_m(0)=0.
}
$$

对 $m\ge2$，其精确上确界为

$$
\boxed{
\sup_{0\le\gamma\le1}z_m(\gamma)
=\left(1+\frac1m\right)
 \left(1-\frac1{m^2}\right)^{m-1}
\longrightarrow1.
}
$$

因此这些等待时间的均值虽共同不超过二，分布族却不一致可积。

证明。对正参数，逐项计数给

$$
\mathbb E[\mathsf N\mathbf1_{\{\mathsf N>m\}}]
= m s_m+\sum_{k=m}^{\infty}s_k
=(1+m\gamma)(1-\gamma)^{m-1}.
$$

零参数下所有等待时间都为一，所以 $m\ge1$ 时尾矩为零。对 $m\ge2$，正参数表达式的导数为

$$
(1-\gamma)^{m-2}(1-m^2\gamma),
$$

最大值在 $\gamma=1/m^2$ 取得。代入即得上确界；第二因子的对数为 $(m-1)\log(1-1/m^2)\to0$，故极限为一。$m=1$ 时，正参数下 $z_1(\gamma)=1+\gamma$，零参数下仍为零，最大值为二。按非负随机变量族的一致可积尾判据，统一加权尾不趋零，正是所需反例。$\square$

**命题 47.3（进入迟到分支的概率与其条件等待相抵）。** 对正 $\gamma$，第一轮未点击的概率为 $\gamma$；条件于该结果，状态变成 $P_1$，剩余轮数 $\mathsf N-1$ 具有参数 $\gamma$ 的几何分布。因此

$$
\boxed{
\mathbb E_\gamma\mathsf N
=1+\Pr_\gamma(\mathsf N>1)
  \mathbb E_\gamma[\mathsf N-1\mid\mathsf N>1]
=1+\gamma\frac1\gamma=2.
}
$$

证明。第一轮未点击后态由 $Q_\gamma|0\rangle=-i\sqrt\gamma|1\rangle$ 给出。从 $P_1$ 出发，每轮点击概率为 $\gamma$，未点击又回到 $P_1$；故剩余轮数的分布为 $\gamma(1-\gamma)^{j-1}$、$j\ge1$，均值为 $1/\gamma$。条件全期望得到方框式。$\square$

在零参数处，这个迟到条件事件概率为零，不能继续定义其归一化后继并把 $0\cdot\infty$ 当计算规则。零模型的均值直接由第一轮必点击给出。这里的单位时间贡献由同一过程的稀有后继承担，未点击分支的条件化是实质步骤。

**推论 47.4（固定截止的实际运行成本不能统一逼近完整均值）。** 截止于第 $m\ge1$ 轮的运行成本为 $\min\{\mathsf N,m\}$，其均值满足

$$
\boxed{
\mathbb E_\gamma\min\{\mathsf N,m\}
=2-(1-\gamma)^{m-1}\quad(0\le\gamma\le1).
}
$$

该函数对参数连续，但对任意固定 $m$，

$$
\sup_{0\le\gamma\le1}
\left(\mathbb E_\gamma\mathsf N
-\mathbb E_\gamma\min\{\mathsf N,m\}\right)=1.
$$

证明。整数等待时间的截断期望是 $\sum_{k=0}^{m-1}s_k$，其中 $s_0=1$。代入第 47.1 条求和；零参数下式值也为一。对正参数，完整均值与截断均值的差为 $(1-\gamma)^{m-1}$，上确界为一；零参数下差为零。$\square$

这个运行成本与第 43 节的 $\mathbb E[\mathsf N\mathbf1_{\{\mathsf N\le m\}}]$ 不同：后者把未结束轨迹记为零，前者把已经执行的 $m$ 轮如实计入。两种都不应与只报告完成样本的条件均值混写。

## 48. 有限条完整返回记录，仍不能统一认证平均返回时间

**定义 48.1（固定来源的独立完成记录）。** 未知参数或者为零，或者为某个指定正数 $\gamma$，两假设先验相等。每次都按第 46 节从 $P_0$ 重新准备，运行到点击，独立重复 $k\ge1$ 次，只读取完整轮数 $(\mathsf N_1,\ldots,\mathsf N_k)$。不增加其他初态、控制或中途量子读出。这是固定协议的数据任务。

所有参数下单条记录都以概率一完成，$k$ 条记录也如此；但正 $0<\gamma<1$ 时完成所需总仪器调用次数没有确定的有限上界。两个端点的总成本则是确定的：零参数为 $k$ 轮，$\gamma=1$ 为 $2k$ 轮。

**定理 48.2（两种返回模型的精确抽样区分界）。** 在定义 48.1 下，

$$
\boxed{
\operatorname{TV}(p_0^{\otimes k},p_\gamma^{\otimes k})
=1-(1-\gamma)^k,
\qquad
P_{\mathrm{err}}^{\mathrm{opt}}=\frac{(1-\gamma)^k}{2}.
}
$$

最优规则是：只要有一条记录超过一轮，就判断正参数；全部为一则判断零参数。

证明。零模型集中在唯一数据词 $(1,\ldots,1)$；正模型赋该词概率 $(1-\gamma)^k$。一个点质量与任意概率律的总变差等于一减该点概率，给出第一式。

在其余数据词上只可能是正模型。在共同数据词上，两假设的未归一化后验权重分别为 $1/2$ 和 $(1-\gamma)^k/2$，选择零模型使错误最小。所得错误正好为后者。随机化不能降低这个逐词最小错误。$\square$

**推论 48.3（均值估计的非统一性）。** 记 $\mu_\eta=\mathbb E_\eta\mathsf N$。对任意可能随机化的估计量 $\widehat\mu$，有

$$
\boxed{
\frac12\Pr_0(|\widehat\mu-1|\ge1/2)
+\frac12\Pr_\gamma(|\widehat\mu-2|\ge1/2)
\ge\frac{(1-\gamma)^k}{2}.
}
$$

因此不存在固定有限 $k$，使这个来源协议上的均值估计对全部 $\eta\in[0,1]$ 都以小于 $1/2$ 的共同失败概率保证误差严格小于 $1/2$。

证明。把估计值与阈值 $3/2$ 比较，得到两假设分类器。若估计误差严格小于 $1/2$，分类必正确；故分类错误率不超过对应估计失败率。第 48.2 条给出下界。若共同失败概率可取 $\alpha<1/2$，令正 $\gamma\downarrow0$，右侧趋于 $1/2$，产生矛盾。$\square$

误差门槛必须保留“严格小于”：若只要求误差至多 $1/2$，常数估计量 $3/2$ 已对全部参数成功。

这不排除对固定已知分离量 $\gamma>0$ 取足够多样本，也不排除增加探测权限。它刻画的是零参数与任意接近零的正参数不能由固定数量的完成记录统一区分。按仪器调用计，$k$ 条记录的平均成本分别为 $k$ 和 $2k$；平均成本有界没有提供确定截止，也没有消除上述推断障碍。第 37 节的任意自适应查询结论属于另一仪器与访问合同，不能移植成此处的无条件下界。

## 49. 从返回量子化到关系边界：本批得到的连接与来源

本批的“AHH”是：造成不稳定平均时间的稀有性，可以藏在迟到的子历史中。第 46 节对共同来源的最终点击概率始终为一，完整等待律按总变差连续；但概率 $\gamma$ 的第一轮未点击分支，携带条件均值 $1/\gamma$ 的剩余等待。它们在每个正参数下贡献整整一个平均轮数，而零参数下这个条件事件已经不存在。

因此“边界保存全部事件概率”和“边界稳定控制无界时间成本”具有不同的精度要求。第 47 节分别算出趋零的概率尾与不趋零的加权尾，第 48 节再把这种区别变成一个固定来源、固定样本数的区分障碍。这些都是同一装置、同一初态、同一记录规则中的关系，没有将不同模型的最优量拼接为一个实现。

第 45 节给出另一条有用的连接：对正的迟到效果，一个在允许初始支撑上忠实的测试态可以控制该支撑上的最坏误差。这个测试能桥接稳定性，却不能重建任意效果；关键是正性与连续有限前缀，不能只凭“满秩”把单个期望值当作全部相干信息。

**说明 49.1（既有量子返回结果及精确模型对应）。** F. A. Grünbaum、L. Velázquez、A. H. Werner、R. F. Werner 的 [*Recurrence for discrete time unitary evolutions*，arXiv:1202.3903v3](https://arxiv.org/abs/1202.3903v3)，发表于 *Communications in Mathematical Physics* 320（2013），研究每次酉演化后投影测试是否返回初始纯态的协议。原文定理 2 在每轮酉演化后投影监测初态、且最终返回概率为一的常返对 $(U,\phi)$ 上表明：平均返回时间有限，当且仅当初态谱测度只含有限个非零权重的不同点质量，并且均值等于这些点的个数。常返前提不能省略；它使这里的平均返回时间与本卷的有限点击时间矩相等。

原文第 4.2 节例 2 已给二态旋转的平均返回时间：非退化旋转时为二，退化时为一；第 5 节讨论均值跳变附近的返回方差。第 46 节与这个例子的对应可直接写出。令

$$
V=\operatorname{diag}(1,-i),
\qquad
O_\theta=
\begin{pmatrix}\cos\theta&-\sin\theta\\
\sin\theta&\cos\theta\end{pmatrix}.
$$

则在 $0\le\theta\le\pi/2$、$\gamma=\sin^2\theta$ 下，

$$
U_\gamma=VO_\theta V^\dagger,
\qquad VP_0V^\dagger=P_0,
\qquad VP_1V^\dagger=P_1.
$$

所以整个准备、酉步骤和两投影都由同一个基变换对应，首次返回记录律相同。本卷的直接级数计算与这一成熟结果一致，不主张首次发现二态均值跳变。

在本例中，循环空间 $\operatorname{span}\{U_\gamma^n|0\rangle:n\ge0\}$ 的维数为：零参数下一，正参数下二。后者因为 $U_\gamma|0\rangle$ 有非零 $|1\rangle$ 分量。因此这里的均值也等于这个维数。一般有限维酉返回中，该维数等于初态所覆盖的不同谱点数；此解释依赖返回初态的投影合同，不自动推广到本卷允许的任意 CP 仪器。

**说明 49.2（工具、证据与适用边界）。** 第 45 节复用第 40 节的 Dini 机制、正算子的忠实迹控制，以及第 38 节含任意参考的删失通道恒等式。第 47 节的一致可积概念采用第 44.1 条所引 Norris 第 6.2 节的尾判据；第 48 节是对两点抽样实验逐词计算的标准检验界。它们在此连接到同一返回仪器，不以改换记号或综合表述声称文献原创性。

本批只给纯理论定义、推导、反例与来源对应。有限来源的支撑覆盖是已给定模型条件，不能从有限次实验无误认证；完成记录数也不等于确定的仪器调用预算。时间均以轮数计，物理秒数需要额外钟标定。本文没有新增 Lean 证明、消化覆盖或冻结结果。

## 追加锚（本行以下为增补区）
