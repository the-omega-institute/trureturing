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

这里 $W$ 只限定初始准备，后续演化可以离开 $W$；不在每一轮额外插入 $P_W$ 投影。对通道 $\Phi$，记 $\Phi|_W$ 为先将 $\mathcal L(W)$ 自然嵌入 $\mathcal L(\mathcal H)$、再作用 $\Phi$ 的通道。其半 diamond 距离仍允许初态与任意有限参考系统纠缠。这是把通道的数学输入域扩到全部支撑于 $W$ 的状态；若某个相干叠加不属于 $\Gamma$，这个定义并不赋予实际制备它的权限。

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

第 38.2 条证明可在初态嵌入后直接使用：带参考的删失输出差仍是等迹的正、负正交块，最大迟到概率正是初始空间 $W$ 上压缩效果的最大本征值。这给出方框中的等式，无需 $W$ 对后续动力学不变。第三项于是使最终限制通道为连续有限限制通道的一致极限，推出第四项。第四项经第 38 节固定的正交点击／永不点击旗标检验给第二项；同一族终端读出保留该旗标，所以效果差受限制通道距离控制。若删去旗标，一个恒定输出通道可以抹掉最终点击效果的区别，这个反向推论便无此依据。最后的上界由引理 45.2 得到。$\square$

因此，若固定有限来源的最终点击响应均随参数连续，它们的支撑覆盖所产生的忠实加权测试也连续，便足以保证整个 $W$ 初态类的长期输出稳定；这包括这些初态所允许的相干叠加及外部参考。这里用的是正尾项的控制，不是由几个概率读数恢复全部矩阵元。常数 $\lambda$ 取决于所选来源和权重；支撑覆盖本身不给跨来源族统一的正下界。

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

在 $\gamma=0$ 处，$p_0(1)=1$，其余概率为零。从共同初态 $P_0$ 出发，所有参数均以概率一最终点击，点击后系统态均为 $P_0$。

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

本例的初始允许支撑 $W=\operatorname{span}\{|0\rangle\}$ 不是正参数下的未点击不变空间：第一次未点击后状态为 $P_1$。第 45 节只限制初态，所以仍适用。它保证的是 $W$ 数学输入域上的稳定性，不能扩成未被允许来源覆盖的全空间稳定性，也不增加实际准备权限。

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

## 50. 随机截止把等待过程变成一份可操作的生成函数

第 45—49 节说明：完整等待律连续，不足以保证无界时间均值连续。本批增加一个实际控制接口——每次未点击后，以固定概率结束本轮实验。它使平均运行成本有限，并把事件时间律变成一族有理响应。以下保持已声明的有限维完整记忆与固定仪器，不改判既有条目。

**定义 50.1（独立几何截止）。** 设每轮原始仪器由未点击 CP 分支 $\mathcal N$ 与点击分支 $\mathcal C_x$ 组成，各分支允许不同的后继空间，并满足 $\operatorname{Tr}\mathcal N(Y)+\sum_x\operatorname{Tr}\mathcal C_x(Y)=\operatorname{Tr}Y$。沿用

$$
\mathcal A=\mathcal N^*,\qquad
B=\sum_x\mathcal C_x^*(I)=I-\mathcal A(I),\qquad
E_n=\mathcal A^{n-1}(B).
$$

本批对各端口选固定的 CPTP 终端读出 $\Lambda_x$，不依赖点击轮数；共同有限输出空间为 $\mathcal K$，并保留与点击输出正交的截止旗标 $|\partial\rangle$。这是第 38 节允许接口的一种特殊情形。

给定 $0<\eta\le1$，置 $q=1-\eta$。每次至少执行一轮原始仪器；点击则结束，未点击后才抛独立硬币，以概率 $\eta$ 截止，以概率 $q$ 继续。等价地，可预先独立抽取

$$
\Pr(\mathsf M=m)=\eta q^{m-1},\qquad m=1,2,\ldots,
$$

运行到首次点击或第 $\mathsf M$ 轮；同轮点击优先于截止。若原始过程永不点击，记原始轮数为 $\mathsf N=\infty$，实际调用次数仍为 $\min\{\mathsf N,\mathsf M\}$。

硬币独立性、其概率标定及重新使用同一仪器，都是操作合同。这里没有在未点击后重新准备初态，因而不是重启协议。每轮相同的硬币规则无需先存储一个无界整数；本批也不要求保留全部原始时间标签。成本只计原仪器调用次数，不含初态制备、硬币生成、终端读出或秒数；期望成本的上界也不等于确定的最大轮数。

**定理 50.2（截止后的完整仪器与终端通道）。** 一轮扩展仪器可写成

$$
\text{继续}:q\mathcal N,\qquad
\text{点击 }x:\Lambda_x\mathcal C_x,\qquad
\text{截止}:Y\longmapsto\eta\operatorname{Tr}[\mathcal N(Y)]|\partial\rangle\langle\partial|.
$$

它是完整 CP 仪器，且以概率一终止。最终通道为

$$
\boxed{
\Psi_\eta(Y)=
\left[\sum_{n\ge1,x}q^{n-1}
 \Lambda_x\mathcal C_x\mathcal N^{n-1}(Y)\right]
\oplus\operatorname{Tr}[(I-G_\eta)Y],
\qquad
G_\eta=\sum_{n\ge1}q^{n-1}E_n.
}
$$

其中 $0\le G_\eta\le I$ 是截止前实际点击的效果。

证明。三类分支均 CP；其迹之和为

$$
q\operatorname{Tr}\mathcal N(Y)
+\sum_x\operatorname{Tr}\mathcal C_x(Y)
+\eta\operatorname{Tr}\mathcal N(Y)=\operatorname{Tr}Y.
$$

连续 $m$ 轮仍未终止的概率为 $q^m\operatorname{Tr}\mathcal N^m(\rho)\le q^m$，故终止概率为一。首次点击在第 $n$ 轮须先经历 $n-1$ 次未点击且硬币均允许继续，因而分支权重为 $q^{n-1}$。这些分支的迹给 $G_\eta$；其余质量进入正交旗标，得到保迹终端通道。$\square$

这里的 $\partial$ 只表示本次被截止，没有认证原始仪器永不点击。它与第 38 节的未解决旗标使用相同输出位置，便于比较；含义仍由实际运行协议决定。

**定理 50.3（点击响应与运行成本的预解式）。** 定义实际调用次数的期望效果 $\mathsf C_\eta$，即

$$
\mathbb E_\rho\min\{\mathsf N,\mathsf M\}
=\operatorname{Tr}(\rho\mathsf C_\eta).
$$

则

$$
\boxed{
G_\eta=(\operatorname{id}-q\mathcal A)^{-1}(B),\qquad
\mathsf C_\eta=(\operatorname{id}-q\mathcal A)^{-1}(I)
=\sum_{m\ge0}q^mS_m,
}
$$

并有

$$
\boxed{
I\le\mathsf C_\eta\le\frac I\eta,\qquad
I=qG_\eta+\eta\mathsf C_\eta.
}
$$

因此只要硬币合同已知，截止前点击概率 $a_\eta=\operatorname{Tr}(\rho G_\eta)$ 就确定平均调用成本

$$
\boxed{c_\eta=\frac{1-q a_\eta}{\eta}.}
$$

证明。$\mathcal A$ 正且次保单位；在 Hermitian 算子的算子范数下是收缩，因为 $-I\le H\le I$ 推出 $-I\le\mathcal A(H)\le I$。故 $q<1$ 时 Neumann 级数收敛，给出两份逆算子表达。

实际调用次数严格超过 $m$ 的概率为 $q^m\operatorname{Tr}(\rho S_m)$。对 $m\ge0$ 求和得到成本式。由 $S_0=I$、$0\le S_m\le I$ 得两侧界。

最后

$$
(\operatorname{id}-q\mathcal A)(I)=\eta I+qB.
$$

作用逆算子即得恒等式，取迹得到标量成本。$\eta=1$ 时 $q=0$，本协议只运行一轮，所有式子仍成立。$\square$

## 51. 永久未点击与有限点击时间矩，是同一成本的两部分

**定理 51.1（截止成本的极点与有限部分）。** 对每一个固定模型，沿用 $F=\lim_mS_m$、$R_m=S_m-F$、$T=\sum_{m\ge0}R_m$。则

$$
\boxed{
\mathsf C_\eta
=\frac F\eta+\sum_{m\ge0}q^mR_m,
\qquad
\lim_{\eta\downarrow0}\eta\mathsf C_\eta=F,
\qquad
\lim_{\eta\downarrow0}
\left(\mathsf C_\eta-\frac F\eta\right)=T.
}
$$

极限均为算子范数极限。第一项 $F/\eta$ 来自原始过程永久未点击的质量；第二项趋向本卷把永不点击记为零的有限点击时间矩。

证明。将 $S_m=F+R_m$ 代入第 50.3 条，常数项求几何级数即得分解。第 19、43 节对每个固定有限模型给出正级数 $T=\sum_mR_m$ 的收敛。有限维下

$$
\sum_m\|R_m\|_\infty
\le\sum_m\operatorname{Tr}R_m=\operatorname{Tr}T<\infty.
$$

对这个可和上界作有限前缀与尾项分解，$q\uparrow1$ 时得到 $\sum_mq^mR_m\to T$。此外该正和不超过 $T$，所以乘以 $\eta$ 后趋零，给第一个极限。$\square$

对固定初态，若 $\operatorname{Tr}(\rho F)>0$，实际截止成本按 $\operatorname{Tr}(\rho F)/\eta$ 发散；若该权重为零，成本趋向有限点击均值。这与把原始无穷等待赋值为无穷的扩展期望相容，也说明不能把有限点击时间矩误当作所有实际轨迹的完整成本。

**定理 51.2（几何截止的精确输出偏差）。** 将第 38 节最终通道 $\Phi_\infty$ 特殊化为同一族 $\Lambda_x$ 读出，采用共同旗标，则

$$
\boxed{
\delta(\Phi_\infty,\Psi_\eta)=\|R-G_\eta\|_\infty,
\qquad
0\le R-G_\eta\le\eta(T-R).
}
$$

这里 $\delta$ 是含任意有限参考系统的半 diamond 距离。

证明。点击块中，无穷输出减去截止输出，恰是把第 $n$ 轮首次点击分支乘以 $1-q^{n-1}\ge0$ 后求和；它是 CP 映射，效果为

$$
R-G_\eta=\sum_{n\ge1}(1-q^{n-1})E_n.
$$

旗标块差为相反号，带参考时仍为等迹的正、负正交块。第 38.2 条的同一证明给出精确半 diamond 范数。由

$$
1-(1-\eta)^{n-1}\le\eta(n-1)
$$

及 $\sum_n(n-1)E_n=T-R$，得到算子序界。$\square$

这条偏差界按同一个模型的 $T-R$ 计量。单个模型的有限性不提供跨模型的统一常数，也不自动说明减去极点以后，有限部分对装置校准连续。

## 52. 截止提高稳定性，同时引入可量化的偏差

**定理 52.1（完整仪器校准对随机截止输出的控制）。** 比较两个具有相同端口、相同终端读出和相同截止概率的原始仪器，记其带记录通道的半 diamond 距离为 $\delta_0$。则

$$
\boxed{
\delta(\Psi_\eta^I,\Psi_\eta^J)
\le\min\{1,\delta_0/\eta\},
}
$$

以及

$$
\boxed{
\|\mathsf C_\eta^I-\mathsf C_\eta^J\|_\infty
\le\frac q\eta\min\{1,\delta_0/\eta\}.
}
$$

证明。以同一独立截止 $\mathsf M$ 对第 38 节有限删失通道混合，得

$$
\Psi_\eta=\sum_{m\ge1}\eta q^{m-1}\Phi_m.
$$

这是归一化几何权重的通道混合，级数在通道范数中收敛。第 35、38 节给 $\delta(\Phi_m^I,\Phi_m^J)\le m\delta_0$；凸性与 $\mathbb E\mathsf M=1/\eta$ 给第一界，再与距离不超过一合并。

共同点击旗标检验给 $\|G_\eta^I-G_\eta^J\|_\infty\le\delta(\Psi_\eta^I,\Psi_\eta^J)$。第 50.3 条的恒等式直接给

$$
\mathsf C_\eta^I-\mathsf C_\eta^J
=-\frac q\eta(G_\eta^I-G_\eta^J),
$$

推出第二界。$\square$

**命题 52.2（两种截止敏感度的阶数均可达到）。** 即使只有一维活动空间，固定 $0<\eta<1$ 时，输出对校准误差的一阶系数 $1/\eta$ 与成本的一阶系数 $q/\eta^2$ 都不能在整个模型类上统一降低。

证明。比较每轮从不点击的仪器与每轮以概率 $0<\varepsilon\le1$ 点击的仪器。其未点击分支分别为恒等与 $(1-\varepsilon)\operatorname{id}$，点击分支分别为零与 $\varepsilon\operatorname{id}$；完整带记录通道距离为 $\varepsilon$。使用共同标量点击输出，则

$$
G_\eta^0=0,\qquad
G_\eta^\varepsilon=\frac{\varepsilon}{\eta+q\varepsilon},
\qquad
\mathsf C_\eta^0=\frac1\eta,\qquad
\mathsf C_\eta^\varepsilon=\frac1{\eta+q\varepsilon}.
$$

所以

$$
\lim_{\varepsilon\downarrow0}
\frac{\delta(\Psi_\eta^0,\Psi_\eta^\varepsilon)}{\varepsilon}
=\frac1\eta,
\qquad
\lim_{\varepsilon\downarrow0}
\frac{|\mathsf C_\eta^0-\mathsf C_\eta^\varepsilon|}{\varepsilon}
=\frac q{\eta^2}.
$$

$\square$

**推论 52.3（已知成本尾预算下的偏差—校准分解）。** 若两个模型另满足

$$
\|T_I-R_I\|_\infty\le K_I,\qquad
\|T_J-R_J\|_\infty\le K_J,
$$

则对每个 $0<\eta\le1$，

$$
\boxed{
\delta(\Phi_\infty^I,\Phi_\infty^J)
\le\min\{1,\delta_0/\eta+\eta(K_I+K_J)\}.
}
$$

证明。在两个最终输出之间分别插入其截止输出，使用第 51.2、52.1 条与三角不等式。$\square$

减小截止概率会降低每个固定模型的截止偏差，同时放大校准误差的系数。这里的 $K_I,K_J$ 必须来自已知模型或独立证书；不能由一批有限截止记录自动获得。公式给出在这份已知预算下选择 $\eta$ 的依据，不提供未知尾项的无条件认证。

## 53. 有限维先验可以把整条事件时间律压进有限个精确截止读数

这一节的读数是精确概率，不是有限实验样本。保持同一固定仪器在全部轮次重复，并把会影响后续的全部活动记忆计入维数上界。

**定理 53.1（截止响应的有理次数界）。** 固定状态 $\rho$，把 $q=1-\eta$ 作为参数，定义

$$
a(q)=\operatorname{Tr}\!\left[\rho(\operatorname{id}-q\mathcal A)^{-1}(B)\right]
=\sum_{n\ge1}q^{n-1}\operatorname{Tr}(\rho E_n),\qquad0\le q<1.
$$

若 $\dim\mathcal H\le d$、$D=d^2$，则存在实多项式 $P,Q$，满足

$$
\boxed{
a(q)=\frac{P(q)}{Q(q)},\qquad
\deg P\le D-1,\quad\deg Q\le D,\quad
Q(q)\ne0\ (0\le q<1),\quad Q(0)=1.
}
$$

零多项式 $P$ 也允许。对每个端口单独的截止点击概率，同样成立。

证明。在 Hermitian 算子的实向量空间上选基，$\mathcal A$ 由一个阶数 $D_0=(\dim\mathcal H)^2\le D$ 的实矩阵 $A$ 表示。取 $Q(q)=\det(I-qA)$。第 50.3 条保证 $0\le q<1$ 时可逆，且 $Q(0)=1$。由伴随矩阵公式，$\operatorname{adj}(I-qA)$ 的各项次数不超过 $D_0-1$；与固定输入 $B$、输出泛函 $X\mapsto\operatorname{Tr}(\rho X)$ 配对，得到次数不超过 $D-1$ 的分子。端口版本只需换成 $B_x=\mathcal C_x^*(I)$。$\square$

这里的 $d^2$ 来自密度算子的线性动力学空间，不是把概率生成函数等同于纯态振幅生成函数。若另有已知且已证明的较小线性实现维数，可对该维数应用同一论证；仅凭某些样本显示低秩还不构成这份先验。

**定理 53.2（有限精确响应对完整事件律的充分性）。** 给定维数上界 $d$。两份符合上述合同的模型，各使用自己固定的初态。若它们在 $2d^2$ 个不同的 $q_i\in[0,1)$ 上具有相同 $a(q_i)$，则它们的全部首次点击轮数概率、永不点击概率和有限点击时间矩都相同。

如果两模型有共同输入空间，且在这些点的整个效果 $G_{1-q_i}$ 相同，则它们对每个共同初态都具有相同的上述时间统计。若每个截止设置还分别给出各端口的精确点击概率，逐端口应用可恢复时间—端口联合分布；只有总点击概率不提供这份端口分解。

证明。写两响应为 $P_1/Q_1$ 与 $P_2/Q_2$。多项式

$$
P_1Q_2-P_2Q_1
$$

次数不超过 $2d^2-1$，却在 $2d^2$ 个不同点为零，故恒为零。因此两有理函数在 $[0,1)$ 上相同。其在零点邻域的幂级数系数唯一，给出每个首次点击概率相同。总有限点击概率及其补数随之相同；逐项加权求和得到有限点击时间矩相同。

效果版本对任意固定初态取迹即可；端口版本对每个 $B_x$ 重复上述推导。$\square$

该结果给出一个充分的读数数量，不主张最少。它唯一确定指定来源的时间律，不唯一确定内部仪器、隐藏记忆或未知初态。相同时间律可以有不同内部实现；若要保留点击后的量子态，则还须保留相应的量子输出接口。

**命题 53.3（没有维数上界时，有限截止读数甚至不能确定均值）。** 任给有限个不同的 $q_1,\ldots,q_r\in[0,1)$，$r\ge1$，存在两个有限支撑、最终必点击的等待律，使全部这些截止点击概率相同，但平均等待不同。它们可由同一维数、同一固定初态的有限 CP 仪器分别实现。

证明。令

$$
h(z)=(z-1)\prod_{i=1}^r(z-q_i)
=\sum_{n=1}^{r+2}\Delta_n z^{n-1}.
$$

则 $\sum_n\Delta_n=h(1)=0$，而

$$
\sum_{n=1}^{r+2}n\Delta_n
=h'(1)+h(1)=\prod_{i=1}^r(1-q_i)>0.
$$

取足够小的 $a>0$，使

$$
p_n^\pm=\frac1{r+2}\pm a\Delta_n>0
\qquad(1\le n\le r+2).
$$

它们都归一化。两概率生成函数之差为 $2ah(z)$，在每个 $q_i$ 为零，而两个均值之差为 $2ah'(1)>0$。

为实现任意一份这样的 $p$，取基 $|0\rangle,\ldots,|r+1\rangle$，共同初态为 $|r+1\rangle$。单个点击标签的 Kraus 算子为

$$
\sqrt{p_1}|0\rangle\langle r+1|,\qquad |0\rangle\langle0|;
$$

单个未点击标签的 Kraus 算子为

$$
\sqrt{p_n}|n-2\rangle\langle r+1|\quad(2\le n\le r+2),
\qquad
|k-1\rangle\langle k|\quad(1\le k\le r).
$$

这些算子的伴随平方之和为 $I$。第一轮点击的概率为 $p_1$；否则以概率 $p_n$ 进入倒计时态 $|n-2\rangle$，再经 $n-2$ 次未点击移位和一次点击，总计第 $n$ 轮首次点击。所有轮次使用同一仪器，且两模型使用相同初态。$\square$

这个实现的活动空间随有限读数数量增长；它没有违反第 53.2 条的已知维数上界。它说明维数证书必须覆盖实际可回流的记忆，不能只数外部可见端口，再把隐藏的倒计时装置排除在模型之外。

## 54. 精确可恢复与稳定可恢复，在同一个量子比特上分开

**定理 54.1（量子比特返回的随机截止响应）。** 对第 46 节的仪器和共同初态 $P_0$，有

$$
\boxed{
a_\eta(\gamma)=1-\frac{\gamma\eta}{\eta+q\gamma},\qquad
c_\eta(\gamma)=1+\frac{q\gamma}{\eta+q\gamma},
\qquad q=1-\eta.
}
$$

其中 $0\le\gamma\le1$、$0<\eta\le1$。特别地，

$$
\boxed{
\sup_{0\le\gamma\le1}(1-a_\eta(\gamma))=\eta,
\qquad
\sup_{0\le\gamma\le1}|\mathbb E_\gamma\mathsf N-c_\eta(\gamma)|=1.
}
$$

证明。将第 46.2 条的等待律代入生成函数：

$$
a_\eta(\gamma)
=1-\gamma+\frac{q\gamma^2}{1-q(1-\gamma)}
=1-\frac{\gamma\eta}{\eta+q\gamma}.
$$

零参数时也直接成立。成本式由第 50.3 条，或对 $q^m s_m$ 求和得到。

函数 $\gamma\eta/(\eta+q\gamma)$ 随 $\gamma$ 单调增加，在 $\gamma=1$ 取得最大值 $\eta$。对正 $\gamma$，原始均值为二，故

$$
2-c_\eta(\gamma)=\frac{\eta}{\eta+q\gamma};
$$

固定 $\eta$ 后令正 $\gamma\downarrow0$，上确界为一。零参数时原始均值和截止成本都为一，差为零。$\square$

这份来源上，截止前点击概率一致趋向一；实际成本却不能一致逼近原始均值。所有原始模型都最终必点击，所以这种非一致性完全不需要永久未点击质量。

**命题 54.2（双参数极限具有连续的过渡层）。** 令 $\eta\downarrow0$，同时 $\gamma/\eta\to u\in[0,\infty]$。则

$$
\boxed{
a_\eta(\gamma)\longrightarrow1,\qquad
c_\eta(\gamma)\longrightarrow1+\frac{u}{1+u},
}
$$

其中 $u=\infty$ 时分式解释为一。

证明。点击概率结论由第 54.1 条的共同上界 $1-a_\eta\le\eta$。另有

$$
c_\eta-1=\frac{q(\gamma/\eta)}{1+q(\gamma/\eta)},
$$

而 $q\to1$，逐种 $u$ 取极限即得。$\square$

因此先让模型退化与先移除截止并不交换；中间的任何有限比值都产生一个介于一与二之间的成本极限。它是探测变化与截止长度的相对尺度，不是物理秒本身出现分数化。

**命题 54.3（有限精确识别不保证均值的稳健恢复）。** 固定任意有限个截止概率 $\eta_i>0$。当 $\gamma\downarrow0$ 时，响应向量

$$
\bigl(a_{\eta_1}(\gamma),\ldots,a_{\eta_r}(\gamma)\bigr)
\longrightarrow(1,\ldots,1),
$$

而原始均值从正参数的二变为零参数的一。因此从这些精确响应向量到原始均值的正确恢复映射，在零模型的响应处不连续。即使在已知的这一参数族内，一个截止概率就已能精确区分零参数与正参数，这种不连续性仍成立。

证明。第 54.1 条给 $0\le1-a_{\eta_i}(\gamma)\le\gamma$，所以向量收敛。对每个固定 $\eta_i>0$，$a_{\eta_i}(0)=1$，而全部正参数都有 $a_{\eta_i}(\gamma)<1$，因此精确区分成立。均值的两个取值使任何正确恢复映射都在极限点不连续。$\square$

第 53.2 条的有限精确充分性与本命题没有矛盾：前者依靠无误的实数概率和已知有限维模型类，后者检验恢复映射对概率误差的稳定性。第 48 节已经给出固定数量完整返回记录的统计下界；本节没有把它擅自升级为任意相干输入、任意自适应控制或任意随机运行预算下的下界。

## 55. 时间边界的充分性还需要给出精度与成本

本批的“AHH”是：一份有限输出接口，可以通过改变一个已标定的截止概率，把整条无穷时间律编码进有理响应；在已知有限记忆上界时，有限个精确响应甚至足以唯一确定整条时间律。但对这些响应施加任意小误差以后，平均时间仍可能无法稳定恢复。信息是否足够、恢复是否连续、实验能否达到所需精度，是三件不同的事。

随机截止还有一个直接物理含义：对每个固定模型，它把实际调用成本分成 $F/\eta$ 与趋向 $T$ 的有限部分。永久未点击权重决定前者，有限点击轨迹决定后者。故同一个操作族既能解释“永远等不到”的成本，也能展示“必然等到但均值不稳定”的限制。

**说明 55.1（标准工具与本批证据范围）。** 本批使用 Neumann 级数、有限矩阵伴随公式、概率生成函数及多项式零点计数。仓内折扣可观测性 Lyapunov 方程与有限序列的 Hankel 实现源码已有相关线性结构；本批将这些工具连接到实际截止仪器、事件记录和运行成本，没有新增或编译这些推导的 Lean 应用。

Mohammed Dahleh、Munther A. Dahleh、George Verghese 的 MIT 讲义 [*Lectures on Dynamic Systems and Control*，第 25.3 节](https://ocw.mit.edu/courses/6-241j-dynamic-systems-and-control-spring-2011/resources/mit6_241js11_chap25/) 给出线性状态空间的有理传递函数 $H(z)=C(zI-A)^{-1}B+D$，式（25.11）—（25.12）连接其系数与 $CA^{n-1}B$。[第 10 章](https://ocw.mit.edu/courses/6-241j-dynamic-systems-and-control-spring-2011/resources/mit6_241js11_chap10/) 式（10.20）—（10.21）给出相应的离散时间变换和预解式展开。

第 53 节的精确对应是：$A$ 表示未点击伴随映射，$B$ 表示点击效果，$C$ 是固定初态的迹泛函，直通项 $D=0$；对 $q>0$，$a(q)=q^{-1}H(q^{-1})$。本文只沿原 CP 仪器到线性表示的方向使用这份对应；任意有理函数的线性实现并不自动具有 CP 性、完整仪器归一化或可实现的量子记忆。最小线性实现维数也不能未经证明就当成最小物理记忆维数。

第 49.1 条所引 Grünbaum 等人的原文以酉返回振幅及其 Schur 函数描述返回过程；这里的 $G_\eta$ 是概率效果的生成函数，作用空间为 Hermitian 算子的线性空间，不能把二者的次数与量子化结论直接互换。第 53 节的有理次数界由本文的伴随矩阵证明承担。

本批未声称取得未知装置的维数证书、截止概率校准、精确实数概率或统一尾预算。几何截止只中止当前实验；若要重启并重新准备初态，需要额外的制备与记忆重置合同。全部结论是纯理论文本，不宣称文献原创性、Lean 核验、消化覆盖或冻结。

## 追加锚（本行以下为增补区）

## 56. 带误差的截止读数可以认证什么

本批承接第 50—55 节的随机截止协议：每次未点击后，以已标定的概率 $\eta=1-q$ 独立结束当前实验；点击与截止同轮时先判点击。始终执行至少一次原仪器调用，并假定每份实验的初态和全部可回流记忆均按同一合同重置。本批不改判既有条目；新增的问题是：读数只有正误差容许时，哪些时间成本仍有有效证书？

**定义 56.1（原始等待、截止响应与均值约定）。** 固定来源和仪器，原始首次点击轮数记为

$$
\mathsf N\in\{1,2,\ldots\}\cup\{\infty\}.
$$

对 $0<q<1$ 定义

$$
f_q(n)=q^{n-1}\quad(n<\infty),\qquad f_q(\infty)=0,
\qquad a(q)=\mathbb E f_q(\mathsf N).
$$

这里 $a(q)$ 正是截止前点击的概率。本批使用扩展均值

$$
\mu=\mathbb E\mathsf N\in[1,\infty],
$$

其中永不点击的正质量使 $\mu=\infty$。这与前文把永不点击分支赋值零的有限点击时间矩 $\operatorname{Tr}(\rho T)$ 有别；只有最终必点击时，两者相同。下面的主要反例均最终必点击，且每个候选模型的均值有限。

**定理 56.2（带噪读数的上下包络证书）。** 预先固定 $r\ge1$ 个 $q_i\in(0,1)$。若同一真实等待律满足

$$
|a(q_i)-b_i|\le\varepsilon_i\quad(1\le i\le r),
\qquad\varepsilon_i\ge0,
$$

取实系数 $c_0,c_1,\ldots,c_r$，置

$$
h(n)=c_0+\sum_{i=1}^r c_i f_{q_i}(n).
$$

对任意非负扩展实值目标 $g$，若 $h(n)\le g(n)$ 对全部有限 $n$ 及 $n=\infty$ 成立，则

$$
\boxed{
\mathbb E g(\mathsf N)
\ge c_0+\sum_i c_i b_i-\sum_i|c_i|\varepsilon_i.
}
$$

若反向的逐点不等式 $h(n)\ge g(n)$ 在同一完整定义域成立，则

$$
\boxed{
\mathbb E g(\mathsf N)
\le c_0+\sum_i c_i b_i+\sum_i|c_i|\varepsilon_i.
}
$$

证明。$h$ 有界可积，且 $\mathbb Eh=c_0+\sum_i c_i a(q_i)$。逐点序关系可取期望，而

$$
\left|\sum_i c_i(a(q_i)-b_i)\right|
\le\sum_i|c_i|\varepsilon_i.
$$

两式合并即得。$\square$

如果上述全部读数区间在一个概率至少 $1-\alpha$ 的共同事件上成立，那么在这个事件上，所有满足逐点条件的证书同时有效。可以读完数据后再选择系数或包络，而无需仅因这种选择重新支付并集界；但所用全部读数必须已包含在共同事件内，选出的包络仍须真正满足全部逐点不等式。这个结论没有证明最优证书存在、强对偶成立，或无穷多个逐点约束可以免费核验。

**命题 56.3（有界读数不能直接上包络无界等待成本）。** 任意上述有限仿射组合 $h$ 都不能满足 $h(n)\ge n$ 对所有正整数成立。

证明。$|f_q(n)|\le1$，故 $|h(n)|\le|c_0|+\sum_i|c_i|$；取比这个常数大的正整数即可。$\square$

这一点只说明该类逐点上包络失败。它本身不排除借助精确维数先验、其他非线性推理或额外尾条件获得均值。第 58 节会给出实际相容模型，证明正误差下更强的上界障碍。

## 57. 一份精确截止读数给出尖锐下界，却通常不给上界

**定理 57.1（单节点读数的精确最小均值）。** 固定 $0<q<1$ 与 $0<a\le1$。选择整数 $k\ge0$ 满足 $q^{k+1}\le a\le q^k$，并置

$$
t=\frac{q^k-a}{q^k(1-q)}\in[0,1].
$$

在全部满足 $a(q)=a$ 的等待律中，有

$$
\boxed{\mu\ge1+k+t.}
$$

由如下两点分布达到等号：

$$
\mathbb P(\mathsf N=k+1)=1-t,\qquad
\mathbb P(\mathsf N=k+2)=t.
$$

当 $a=q^j$、$j\ge1$ 时，$k=j-1,j$ 两种选择给出相同下界 $j+1$ 和集中于 $\mathsf N=j+1$ 的分布；当 $a=1$ 时，只有 $k=0$ 合法，此时 $t=0$。

证明。考虑第 56.2 条中的仿射函数

$$
h(n)=1+k+\frac{q^k-f_q(n)}{q^k(1-q)}.
$$

若 $n<\infty$，记 $m=n-1$。当 $m\ge k$ 时，

$$
\frac{1-q^{m-k}}{1-q}
=\sum_{j=0}^{m-k-1}q^j\le m-k,
$$

其中空和为零。当 $m<k$ 时，同一分式为

$$
-\sum_{j=m-k}^{-1}q^j\le-(k-m)=m-k.
$$

所以总有 $h(n)\le n$；在 $n=\infty$ 处也成立。取期望得到下界。所列两点分布的截止响应为 $(1-t)q^k+tq^{k+1}=a$，均值为 $1+k+t$。它也可用第 53.3 条的倒计时构造实现：把其余有限轮次权重设为零即可。$\square$

**命题 57.2（同一精确响应可以对应任意大的有限均值）。** 若 $0<a<1$，即使限定为有限支撑且最终必点击的等待律，约束 $a(q)=a$ 也不给任何有限均值上界。

证明。取足够大的整数 $M$，使 $q^{M-1}<a$，置

$$
w_M=\frac{1-a}{1-q^{M-1}}\in(0,1),
\qquad
\mathbb P(\mathsf N=1)=1-w_M,\quad
\mathbb P(\mathsf N=M)=w_M.
$$

其截止响应恰为 $a$，但

$$
\mu_M=1+w_M(M-1)\longrightarrow\infty,
$$

因为 $w_M\to1-a>0$。每个分布都可用第 53.3 条的倒计时仪器构造实现；允许零权重不会改变归一化或等待律。此处实现维数随 $M$ 增长。$\square$

精确端点 $a(q)=1$ 则强制 $\mathsf N=1$ 几乎处处，因为 $f_q\le1$，且只在 $n=1$ 取一。端点 $a(q)=0$ 强制永不点击，因为全部有限 $n$ 都有 $f_q(n)>0$。这是精确等式的后果；不能把一个接近一或零的有限精度读数替换成这样的端点等式。

## 58. 二维慢分支已足以摧毁统一均值上界

本节固定完整活动空间为二维，不让隐藏倒计时的维数增长。慢尾来自同一记忆态的重复续接。

**定义 58.1（稀有进入、缓慢退出的完整仪器）。** 取正交基 $|s\rangle,|u\rangle$，共同初态 $P_s=|s\rangle\langle s|$。对 $0\le w<1$、$0<\gamma\le1$，未点击分支 $\mathcal N_{w,\gamma}$ 使用两个 Kraus 算子

$$
\sqrt w\,|u\rangle\langle s|,\qquad
\sqrt{1-\gamma}\,|u\rangle\langle u|;
$$

点击分支 $\mathcal C_{w,\gamma}$ 使用

$$
\sqrt{1-w}\,|s\rangle\langle s|,\qquad
\sqrt\gamma\,|s\rangle\langle u|.
$$

每个分支内部求 Kraus 和，不把两个 Kraus 指标视作可读结果。四个伴随平方之和为 $I$，因此这是合法的双结果仪器。另把同一公式的 $(w,\gamma)=(0,0)$ 纳入模型族，作为基准仪器：从 $P_s$ 第一轮必点击，从 $P_u$ 永不点击。

**定理 58.2（等待律、截止律与完整仪器距离）。** 对正 $\gamma$ 的仪器，任意初态最终都点击。从共同来源 $P_s$ 出发有

$$
\boxed{
p(1)=1-w,\qquad
p(n)=w\gamma(1-\gamma)^{n-2}\ (n\ge2),\qquad
\mu=1+\frac w\gamma.
}
$$

与基准的完整首次点击时间分布之总变差距离为 $w$。令 $q=1-\eta$、$0<\eta\le1$，则

$$
\boxed{
a_\eta=1-\frac{w\eta}{\eta+q\gamma},\qquad
\sup_{0<\eta\le1}|a_\eta-1|=w.
}
$$

若保留正交的点击、未点击记录及其量子输出，完整单轮仪器通道与基准的半 diamond 距离恰为

$$
\boxed{\delta_{\mathrm{inst}}=\max\{w,\gamma\}.}
$$

证明。第一轮未点击的概率为 $w$，条件后继为 $P_u$。从 $P_u$ 开始，每轮以概率 $\gamma$ 点击，否则回到 $P_u$，给出上述几何尾和均值。从任意初态开始，第一次未点击后也为 $P_u$，所以正 $\gamma$ 保证最终点击。概率式在 $\gamma=1$ 时按零次幂为一解释。

基准时间律为集中在一的点质量，因此总变差距离为 $1-p(1)=w$。截止响应由级数直接得到

$$
a_\eta=1-w+\frac{wq\gamma}{1-q(1-\gamma)}
=1-\frac{w\eta}{\eta+q\gamma}.
$$

损失不超过 $w$，在 $\eta=1$ 取得它。

对任意有限参考系统与联合输入态，记输入在 $s,u$ 基上的两个参考对角块为 $\rho_{ss},\rho_{uu}$，均正半定且迹之和为一。两仪器输出之差在未点击记录块为

$$
D\otimes P_u,\qquad D=w\rho_{ss}-\gamma\rho_{uu},
$$

在点击记录块为 $-D\otimes P_s$。记录块正交，故输出差的半迹范数为

$$
\|D\|_1
\le w\operatorname{Tr}\rho_{ss}+\gamma\operatorname{Tr}\rho_{uu}
\le\max\{w,\gamma\}.
$$

通道差的 diamond 范数可用带参考的输入态取上确界；上式给上界。分别输入 $P_s$ 和 $P_u$ 达到 $w$ 与 $\gamma$，故取其较大值即得等号。$\square$

**推论 58.3（任意正校准容许内的均值上确界为无穷）。** 任给 $\varepsilon_{\mathrm{inst}},\varepsilon_{\mathrm{read}}>0$ 和有限 $M$，存在一个正 $w,\gamma$ 的上述二维仪器，满足

$$
\delta_{\mathrm{inst}}<\varepsilon_{\mathrm{inst}},\qquad
\sup_{0<\eta\le1}|a_\eta-1|<\varepsilon_{\mathrm{read}},\qquad
\mu>M.
$$

它的完整等待律与基准的总变差距离也可同时小于 $\varepsilon_{\mathrm{read}}$。

证明。先固定 $0<w<\min\{1,\varepsilon_{\mathrm{inst}},\varepsilon_{\mathrm{read}}\}$，再选择足够小的 $0<\gamma<\min\{1,\varepsilon_{\mathrm{inst}}\}$，使 $1+w/\gamma>M$。应用定理 58.2。$\square$

因此即使已知完整活动维数是二、仪器经过任意精细但仍有正误差的校准、所有截止响应均接近立即点击，仍没有统一有限的原始平均等待上界。这些候选自身没有永不点击质量；缺失的是跨候选的统一尾控制。第 53.2 条关于有限个精确响应的唯一性仍成立：这里没有声称响应精确相同。

**定理 58.4（固定数量完成记录的诚实上置信界必须退化）。** 固定整数 $k\ge1$ 和 $0<\alpha<1$。实验只能取得上述共同来源的 $k$ 份独立完成等待记录，可附加与参数无关的随机化。设同一个可测规则输出 $U\in[1,\infty]$，并对定义 58.1 的全部模型满足

$$
\mathbb P_\theta(U\ge\mu_\theta)\ge1-\alpha.
$$

则在基准模型上必有

$$
\boxed{\mathbb P_0(U=\infty)\ge1-\alpha.}
$$

证明。取 $w_j=1/(j+1)$、$\gamma_j=w_j/(j+1)$，$j\ge1$。对应均值为 $\mu_j=j+2$，单条记录与基准的总变差距离为 $w_j\to0$。独立乘积律的总变差不超过 $kw_j$；共同随机化是相同的随机核，不增加该距离。因此覆盖条件给

$$
\mathbb P_0(U\ge j+2)\ge1-\alpha-kw_j.
$$

事件 $\{U\ge j+2\}$ 随 $j$ 递减，其交集是 $\{U=\infty\}$。概率从上连续，令 $j\to\infty$ 即得。$\square$

结论也适用于这些记录经过与未知参数无关的共同删失或后处理之后的数据，包括固定设置的独立随机截止数据：可对完成记录附加同一截止随机数再生成它们。这里没有授予任意量子输入、相干控制或额外校准实验；因此它不是所有量子查询策略的不可能性定理。固定完成记录数也不是固定原始调用预算，慢模型完成这些记录所需的成本本身可以很大。

## 59. 把有界等待成本变成带噪矩证书

现在不要求重建完整等待律。先指定一个有界任务：前 $m$ 轮累计了多少原始等待成本，即 $\mathbb E\min(\mathsf N,m)$。允许的输入仍是随机截止的点击概率，使用第 56 节同一来源。

**定义 59.1（等待变量的紧区间编码）。** 固定 $q_0\in(0,1)$，置

$$
X=q_0^{\mathsf N-1}\quad(\mathsf N<\infty),\qquad X=0\quad(\mathsf N=\infty).
$$

则对每个整数 $j\ge1$，

$$
\mathbb E X^j=a(q_0^j).
$$

零次矩恒为 $\mathbb E1=1$，包括 $X=0$ 的质量；不能把它误换成 $\lim_{q\uparrow1}a(q)=\mathbb P(\mathsf N<\infty)$。这里的幂基常数项就是常数函数一。

对整数 $m\ge2$，定义 $G_m:[0,1]\to[1,m]$：在节点上取

$$
G_m(q_0^{n-1})=n\quad(1\le n\le m),
$$

在相邻节点之间线性插值，在 $[0,q_0^{m-1}]$ 恒为 $m$。于是

$$
G_m(X)=\min(\mathsf N,m),
\qquad
L_m=\frac1{(1-q_0)q_0^{m-2}}
$$

是 $G_m$ 的 Lipschitz 常数：第 $n$、$n+1$ 个节点的间距为 $(1-q_0)q_0^{n-1}$，最小间距在 $n=m-1$ 取得。$\mathsf N=\infty$ 时，截断成本约定为 $m$。

**定理 59.2（截止矩对截断均值的显式误差证书）。** 固定整数 $k\ge1$，对 $G_m$ 取 Bernstein 多项式

$$
B_kG_m(x)=\sum_{\ell=0}^{k}
G_m(\ell/k)\binom{k}{\ell}x^\ell(1-x)^{k-\ell}
=\sum_{j=0}^k c_jx^j.
$$

若同时知道

$$
|a(q_0^j)-b_j|\le\varepsilon_j\qquad(1\le j\le k),
$$

令

$$
\widehat v_{m,k}=c_0+\sum_{j=1}^k c_jb_j,
\qquad
 e_{m,k}=\frac{L_m}{2\sqrt k}+\sum_{j=1}^k|c_j|\varepsilon_j.
$$

则

$$
\boxed{
\left|\mathbb E\min(\mathsf N,m)-\widehat v_{m,k}\right|
\le e_{m,k}.
}
$$

并有保守系数界

$$
\boxed{\sum_{j=0}^k|c_j|\le m3^k.}
$$

证明。固定 $x\in[0,1]$，令 $Z$ 服从参数 $(k,x)$ 的二项分布。Bernstein 权重给

$$
B_kG_m(x)=\mathbb E G_m(Z/k).
$$

于是

$$
\begin{aligned}
|B_kG_m(x)-G_m(x)|
&\le L_m\mathbb E|Z/k-x|\\
&\le L_m\sqrt{x(1-x)/k}
\le\frac{L_m}{2\sqrt k}.
\end{aligned}
$$

对 $X$ 再取期望，结合定义 59.1，得到

$$
\left|\mathbb E G_m(X)-\left(c_0+\sum_{j=1}^kc_j a(q_0^j)\right)\right|
\le\frac{L_m}{2\sqrt k}.
$$

读数误差再由三角不等式控制，给第一结论。为估计系数绝对值之和，展开每项的 $(1-x)^{k-\ell}$；该项系数绝对值之和至多

$$
m\binom{k}{\ell}2^{k-\ell}.
$$

对 $\ell$ 求和得 $m(1+2)^k=m3^k$。$\square$

这个构造复用《[递归关系观察的恢复几何](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md)》第 11.4 条的 Bernstein 方差方法：那里以谱变量近似未来响应，这里令谱样的标量变量为 $X=q_0^{\mathsf N-1}$，近似指定截断成本。映射保留的是 $[0,1]$ 上正概率权重及幂矩；它没有把原始 CP 动力学的全部算子变成自伴谱模型，也不继承原问题的物理实现结论。

**推论 59.3（每份短期望实验与总体估计成本分开）。** 假定仪器、来源、重置和截止概率均准确固定。对每个节点 $q_0^j$，进行 $\ell\ge1$ 份独立新实验，$b_j$ 是截止前点击频率。固定 $0<\alpha<1$，取

$$
\varepsilon=\sqrt{\frac{\log(2k/\alpha)}{2\ell}}.
$$

以至少 $1-\alpha$ 的概率，第 59.2 条的结论在全部 $\varepsilon_j=\varepsilon$ 下成立。每份实验的期望原始调用数至多 $1/(1-q_0)$，全部 $k\ell$ 份实验的期望调用总数至多

$$
\boxed{\frac{k\ell}{1-q_0}.}
$$

证明。每个实验的点击指示变量取值于 $[0,1]$，均值为 $a(q_0^j)$。Hoeffding 不等式给每个频率的失败概率不超过 $2e^{-2\ell\varepsilon^2}$；对 $k$ 个节点取并集界，得到共同失败概率至多 $\alpha$。各节点之间独立并非这个并集界所必需，但每个节点内的重复实验须满足所用集中界的独立同分布假设。

第 $j$ 个截止参数为 $\eta_j=1-q_0^j\ge1-q_0$，第 50.3 条给单份期望成本不超过 $1/\eta_j$。再用期望的线性性求和。$\square$

这个结果允许每份实验以短的期望调用数结束，但不提供确定的最大时长。它也不等于便宜的均值恢复：系数会放大误差，$L_m$ 随截断高度增长。保守地说，若想让证书误差不超过 $\tau>0$，可以选择

$$
k\ge\max\{1,\lceil(L_m/\tau)^2\rceil\},
\qquad
\ell\ge\max\left\{1,
\left\lceil\frac{2m^2 9^k\log(2k/\alpha)}{\tau^2}\right\rceil\right\}.
$$

近似项与噪声项此时各不超过 $\tau/2$。这仅是有限可行的充分预算，未声称阶数或样本量最优；重置、制备与读数本身的成本也未折算成仪器调用数。

如果实际实验响应与目标 $a(q_0^j)$ 另有已认证的校准偏差 $\zeta_j$，应把误差改为 $\varepsilon_j=\varepsilon+\zeta_j$。增加采样只能减小集中误差，不会自动消除校准偏差。

## 60. 另给尾预算，才能把截断成本接回完整均值

**定理 60.1（独立高阶矩预算给出均值区间）。** 假定同一等待律另满足已知条件

$$
\mathbb E\mathsf N^{1+\beta}\le K<\infty,\qquad\beta>0.
$$

则它没有永不点击质量，$\mu<\infty$，且对每个整数 $m\ge1$，

$$
\boxed{
0\le\mu-\mathbb E\min(\mathsf N,m)\le\frac K{m^\beta}.
}
$$

若已取得第 59.2 条的截断成本估计及误差 $e_{m,k}$，则

$$
\boxed{
\max\{1,\widehat v_{m,k}-e_{m,k}\}
\le\mu\le
\widehat v_{m,k}+e_{m,k}+\frac K{m^\beta}.
}
$$

证明。正的永不点击质量会令高阶矩无穷，与假设矛盾。又 $\mathsf N\le\mathsf N^{1+\beta}$，故均值有限。对有限正整数 $n$，

$$
0\le n-\min(n,m)
\le n\,\mathbf1_{\{n>m\}}
\le\frac{n^{1+\beta}}{m^\beta}.
$$

取期望得到尾界，再与截断成本区间合并。$\square$

这里 $K,\beta$ 必须是模型类预先给出的合同，或由另一份有效证书提供；第 58 节证明，同一批有限精度有界读数不能普遍认证这样一个有限预算。若尾预算本身只有置信度 $1-\alpha_{\mathrm{tail}}$，读数区间的置信度为 $1-\alpha_{\mathrm{data}}$，两者在同一真实模型上的联合结论可用并集界给至少 $1-\alpha_{\mathrm{tail}}-\alpha_{\mathrm{data}}$，不要求二事件独立。若尾预算只是尚未核验的前提，结论仍是条件式。

这与前文的共同加权尾条件相接：高阶矩上界是一个方便且明确的充分条件。更一般地，只要已有可用函数 $r(m)\downarrow0$，并认证

$$
\mathbb E[(\mathsf N-m)_+]\le r(m),
$$

同一均值区间就可把 $K/m^\beta$ 换成 $r(m)$。不需要把高阶矩有限误当成所有均值认证方法的必要条件。

## 61. 可识别的整体与可认证的时间成本之间还隔着尾部

本批的“AHH”是：已知二维活动记忆也不能消除正误差下的均值障碍。极少发生的慢分支，在全部有界读数中只支付它的概率质量；在平均等待中，却支付“质量乘以停留长度”。把质量压小、把停留拉得更长，就能同时保留很好的读数拟合并推高均值。第 58 节用同一个合法仪器族同时实现这些关系。

这里还明确前后两个例子的区别：第 46、54 节的酉返回族，均值只取一或二，非一致可积的是无界等待变量；第 50 节引言中的“无界时间均值”应按“无界时间变量的均值”理解。本批第 58 节允许稀有进入与慢退出分别调节，才得到均值本身在任意正误差邻域内无上界的更强结论。

因此，对时间边界而言，精确识别、稳定估计和有限置信认证需要分别给出条件。第 53 节的有限维有理唯一性处理精确识别；第 58 节排除了无统一尾条件的普适均值上界；第 59—60 节则给出可用的恢复路径：先指定有界成本，再控制近似、读数和尾部三个不同误差源。

$$
\boxed{
\text{完整均值误差预算}
=
\text{有界目标的近似误差}
+
\text{读数误差传播}
+
\text{独立认证的尾成本}.
}
$$

这个式子表达第 60.1 条的上界预算分解，不宣称三项总在真实误差中同时取等号。它也把关系全息的任务含义进一步具体化：边界是否足够，要同时指定观察任务、容许误差和准许的来源类。对有界记录统计足够精细的接口，未必足够认证无界的时间成本。

**说明 61.1（复用、来源与适用范围）。** 第 56 节使用期望的单调性与有限线性组合误差界，属于矩约束的弱包络方法。仓内 `RationalMomentQueryEnvelope` 的 `query_interval_of_envelope` 已有有限有理权重下的逐点包络到均值区间结构；这里允许可数等待标签、永不点击点及带噪读数，其纸面证明由第 56.2 条承担，没有宣称该有限有理声明已覆盖本节或已编译本节的精确应用。

第 59 节的 Bernstein 归一化和方差方法对应上述恢复几何第 11.4 条及其所引钉版 Mathlib [Bernstein 源码](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/Bernstein.lean)。集中界沿用第 22 节的来源：W. Hoeffding，*Probability Inequalities for Sums of Bounded Random Variables*，[DOI:10.1080/01621459.1963.10500830](https://doi.org/10.1080/01621459.1963.10500830)。本批给出新的任务对应和完整推导，不将这些标准工具声明为原创。

第 58.4 条通过小总变差、大发散均值和统一覆盖推出上置信界退化。相关历史文献是 R. R. Bahadur、Leonard J. Savage，*The Nonexistence of Certain Statistical Procedures in Nonparametric Problems*（1956），[DOI:10.1214/aoms/1177728077](https://doi.org/10.1214/aoms/1177728077)。本批核对了该书目元数据，未取得可读原文，因此不把这里的二维仪器实现或单侧上置信界定理归给原文；所声明结论由第 58.4 条的自包含证明承担。

以上均为纯理论文本，未新增 Lean 实现、消化覆盖或冻结结果。仪器维数、完整记忆、来源重置、截止校准和独立尾预算各有明确用途，不能以同一份有限记录同时替代所有这些前提。全文不声称文献原创性。

## 追加锚（本行以下为增补区）

## 62. 尾预算把不可认证的均值变成具有精确指数的稳定任务

第 58 节表明，完整活动记忆只有二维也不足以排除正误差下的无界均值；第 60 节说明，独立尾预算能够补足这项缺口。本批继续区分两种预算：只对实际初始来源成立的平均预算，以及对后继状态也统一成立的续接预算。它们给出的稳定性强度不同。本批保留既有正文和结论，所有新增结果仍是纯理论推导。

**定义 62.1（固定来源的矩预算类）。** 本批固定

$$
0<\beta\le1,\qquad p=1+\beta,\qquad K\ge1,
\qquad r=\frac{\beta}{1+\beta}=1-\frac1p.
$$

等待律 $P$ 属于 $\mathcal P_{p,K}$，是指其首次点击轮数 $\mathsf N\in\{1,2,\ldots\}\cup\{\infty\}$ 满足

$$
\mathbb E_P\mathsf N^p\le K.
$$

所以 $P(\mathsf N=\infty)=0$，且均值 $\mu_P\le K^{1/p}$。这里的预算只约束声明的初始来源，不自动约束换成其他初态或条件于某次未点击以后的状态。

**定理 62.2（均值对完整等待律的 Hölder 模量）。** 若 $P,Q\in\mathcal P_{p,K}$，且

$$
\varepsilon=\operatorname{TV}(P,Q)
=\frac12\sum_{n\ge1}|P(n)-Q(n)|,
$$

则

$$
\boxed{|\mu_P-\mu_Q|\le(K-1)^{1/p}\varepsilon^r.}
$$

证明。取两律共同部分 $c_n=\min\{P(n),Q(n)\}$，并置 $u_n=P(n)-c_n$、$v_n=Q(n)-c_n$。两剩余质量都为 $\varepsilon$。因为 $p>1$，对 $n\ge1$ 有

$$
(n-1)^p\le n^p-1.
$$

例如，函数 $(1+t)^p-t^p$ 在 $t\ge0$ 上不减且在零点取一。因而

$$
\sum_n(n-1)^pu_n\le K-1,
\qquad
\sum_n(n-1)^pv_n\le K-1.
$$

Hölder 不等式给

$$
A:=\sum_n(n-1)u_n\le(K-1)^{1/p}\varepsilon^{1-1/p},
\qquad
B:=\sum_n(n-1)v_n\le(K-1)^{1/p}\varepsilon^{1-1/p}.
$$

共同部分抵消，且 $\sum_nu_n=\sum_nv_n$，所以 $\mu_P-\mu_Q=A-B$。由 $A,B\ge0$ 得 $|A-B|\le\max\{A,B\}$，推出结论。$\varepsilon=0$ 时两律相同；$K=1$ 时两律都集中于一，结论也成立。$\square$

**命题 62.3（二维完整仪器已能达到该指数）。** 固定 $K>1$，令

$$
c_p=\frac{K-1}{2^p}>0.
$$

对任意 $0<w<\min\{1,c_p\}$，取 $\gamma=(w/c_p)^{1/p}$。比较第 58.1 条的两个仪器

$$
\mathfrak I_{0,\gamma},\qquad\mathfrak I_{w,\gamma},
$$

共同初态仍为 $P_s$。两者从任意初态最终都点击，且从 $P_s$ 出发的等待律都属于 $\mathcal P_{p,K}$。两仪器的完整单轮半 diamond 距离及这两份等待律的总变差距离均为 $w$，均值差为

$$
\boxed{
\mu_{w,\gamma}-\mu_{0,\gamma}
=\frac{(K-1)^{1/p}}2w^r.
}
$$

证明。两模型使用同一正 $\gamma<1$，所以最终点击结论由第 58.2 条成立。设 $\mathsf G$ 是成功概率为 $\gamma$、支撑从一开始的几何变量。从 $P_s$ 出发，第一轮未点击后总等待为 $1+\mathsf G$。几何级数及其一、二阶求导给

$$
\mathbb E(1+\mathsf G)^2
=1+\frac1\gamma+\frac2{\gamma^2}
\le\frac4{\gamma^2}.
$$

由于 $1<p\le2$，幂函数的凹性给

$$
\mathbb E(1+\mathsf G)^p
\le\left[\mathbb E(1+\mathsf G)^2\right]^{p/2}
\le\frac{2^p}{\gamma^p}.
$$

因此

$$
\mathbb E_{w,\gamma}\mathsf N^p
=1-w+w\mathbb E(1+\mathsf G)^p
\le1+\frac{2^pw}{\gamma^p}=K.
$$

另一个模型从 $P_s$ 第一轮必点击，其矩为一。相对于它，只有第一轮从 $s$ 出发的点击质量 $w$ 被移入慢尾，所以等待律的总变差为 $w$。

对带参考的任意输入，两单轮输出之差在未点击块为 $w\rho_{ss}\otimes P_u$，在点击块为 $-w\rho_{ss}\otimes P_s$；两块正交，半迹范数为 $w\operatorname{Tr}\rho_{ss}\le w$，由输入 $P_s$ 达到。注意这里固定两模型相同的 $\gamma$，与第 58.2 条比较 $(0,0)$ 的距离公式有别。最后 $w/\gamma=c_p^{1/p}w^r$，即得均值差。$\square$

令 $w\downarrow0$，任何以 $\varepsilon^s$、$s>r$ 为模量且常数只依赖 $p,K$ 的统一均值界都会被这个家族推翻。这里尖锐的是指数，未声称第 62.2 条的常数在二维仪器子类中最优；比较中的两个仪器都随 $w$ 变化。

## 63. 校准误差实际累积的长度，是仍在运行的轮数

第 35.2 条把每个调用槽的活动概率上界取成一，得到 $m\delta$。对固定来源保留这些活动概率，可以得到由真实平均调用数控制的界。

**定理 63.1（按活动质量加权的停止历史界）。** 两完整仪器 $\mathfrak I,\mathfrak J$ 具有共同输入、记录和各分支输出空间，完整单轮半 diamond 距离为 $\delta$。它们使用同一首次点击停止协议和同一初态 $\rho$。记

$$
s_j^I=\operatorname{Tr}\mathcal N_I^j(\rho),\qquad
c_m^I=\sum_{j=0}^{m-1}s_j^I
=\mathbb E_I\min(\mathsf N,m),
$$

并对 $J$ 类似定义。则第 35 节保留完整有限停止记录和量子后继的两个输出满足

$$
\boxed{
D\bigl(\Omega_m^I(\rho),\Omega_m^J(\rho)\bigr)
\le\min\{1,\delta\min(c_m^I,c_m^J)\}.
}
$$

给定初态可带任意有限参考系统；此时左侧在完整联合输出上取距离，右侧的生存概率由共同系统边缘态计算。

证明。取混合过程：前 $j$ 轮使用 $I$，剩余轮次使用 $J$，$0\le j\le m$。相邻两个混合过程只在第 $j+1$ 轮不同，其共同前缀中的未点击块是 $\mathcal N_I^j(\rho)$，迹为 $s_j^I$。归一化该块，应用完整仪器距离定义，再用后续相同停止处理的迹距离收缩性，这一替换的代价至多 $s_j^I\delta$。零迹块的代价为零。

对 $j=0,\ldots,m-1$ 求和得 $\delta c_m^I$。交换 $I,J$ 重做给 $\delta c_m^J$，再与距离不超过一合并。带参考时同一未归一化块的迹仍为 $s_j^I$，其余论证不变。$\square$

**推论 63.2（固定来源的完整时间律与均值校准）。** 若两个来源下的均值 $\mu_I,\mu_J$ 都有限，则全部首次点击轮数律满足

$$
\boxed{
\operatorname{TV}(P_I,P_J)
\le\min\{1,\delta\min(\mu_I,\mu_J)\}.
}
$$

若二者还都属于 $\mathcal P_{p,K}$，则

$$
\boxed{
|\mu_I-\mu_J|
\le(K-1)^{1/p}
\left[\min\{1,K^{1/p}\delta\}\right]^r.
}
$$

证明。丢弃有限停止输出中的量子后继和端口细分，只保留轮数及未解决标签，距离不增加。将大于 $m$ 的轮数统一编码为 $\infty$，所得删失律与原始律的总变差距离为 $s_m$，因有限均值而趋零。因此第 63.1 条在 $m\to\infty$ 时给第一个界。第二个界使用 $\mu_I,\mu_J\le K^{1/p}$ 及第 62.2 条。$\square$

第 62.3 条中的完整仪器距离也等于 $w$，因此这里的 $\delta^r$ 指数在固定来源矩预算类中同样不能统一提高。这个结论对仪器的完整带记录校准成立，不是只比较点击效果或未点击映射的某个矩阵元。

## 64. 保留截断调用轮数，可以取得尖锐的样本指数

这一节使用真实调用计数作为记录。它与第 59 节仅取得截止点击频率的接口不同；因此允许改变估计器及其精度预算。所有样本均来自同一仪器、相同来源与完整记忆重置后的独立准备。

**定理 64.1（截断计数的均值置信区间）。** 设真实等待律属于 $\mathcal P_{p,K}$。取整数 $\ell,m\ge1$，每次运行至首次点击或第 $m$ 轮，记录实际调用数

$$
Y_i=\min(\mathsf N_i,m),\qquad
\widehat\mu_{m,\ell}=\frac1\ell\sum_{i=1}^{\ell}Y_i.
$$

对任意 $t>0$，以至少 $1-2e^{-t}$ 的概率有

$$
\boxed{
|\widehat\mu_{m,\ell}-\mu|
\le\frac K{m^\beta}
+\sqrt{\frac{2Km^{1-\beta}t}{\ell}}
+\frac{2mt}{3\ell}.
}
$$

若 $t=\log(2/\alpha)$、$0<\alpha<1$、整数 $\ell\ge t$，并取

$$
x=\left(\frac{K\ell}{t}\right)^{1/p},\qquad
m=\lceil x\rceil,
$$

则上述半径不超过

$$
\boxed{\frac{13}{3}K^{1/p}\left(\frac t\ell\right)^r.}
$$

所有实验的调用总数确定地不超过 $\ell m$；其期望则不超过 $\ell\mu\le\ell K^{1/p}$。

证明。第 60.1 条给 $0\le\mu-\mathbb EY_i\le K/m^\beta$。逐点有

$$
Y_i^2\le\mathsf N_i^p m^{2-p},
$$

因为 $\mathsf N_i\le m$ 时可把 $\mathsf N_i^{2-p}$ 换成 $m^{2-p}$，反之可把 $m^p$ 换成 $\mathsf N_i^p$。故 $\operatorname{Var}Y_i\le Km^{1-\beta}$。又 $|Y_i-\mathbb EY_i|\le m$。有界变量的 Bernstein 不等式给

$$
\mathbb P\!\left(
\left|\widehat\mu_{m,\ell}-\mathbb EY_i\right|
>\sqrt{\frac{2Km^{1-\beta}t}{\ell}}+\frac{2mt}{3\ell}
\right)\le2e^{-t}.
$$

所用常数也可直接由中心变量 $Z$ 的指数矩界核对：若 $|Z|\le m$、$\mathbb EZ=0$、$\mathbb EZ^2\le v$，则对 $0\le\lambda<3/m$，展开指数级数并用 $j!\ge2\cdot3^{j-2}$（$j\ge2$）得到

$$
\log\mathbb Ee^{\pm\lambda Z}
\le\frac{\lambda^2v}{2(1-\lambda m/3)}.
$$

独立性、Chernoff 界及对两个符号取并集给以上 Bernstein 形式。加上截断偏差即得第一式。

对参数选择，由 $K\ge1$、$\ell\ge t$ 得 $x\ge1$，所以 $x\le m\le2x$。三项分别至多

$$
K^{1/p}(t/\ell)^r,\qquad
2^{1-\beta/2}K^{1/p}(t/\ell)^r,\qquad
\frac43K^{1/p}(t/\ell)^r.
$$

因为 $2^{1-\beta/2}\le2$，三项之和不超过所列常数。调用总数为 $\sum_iY_i$，逐项用 $Y_i\le m$ 及 $Y_i\le\mathsf N_i$ 得两种成本界。$\square$

这里给定的矩预算、调用计数可读性与来源重置都仍是前提。制备、计数器和物理秒数没有折算进调用成本；若需要确定的总运行预算，应使用 $\ell m$，不能把期望上界当作硬截止。

**定理 64.2（固定完成记录数下的指数不能改善）。** 固定 $K>1$，令 $c_p=(K-1)/2^p$。对任何整数

$$
\ell\ge\max\{1,(2c_p)^{-1}\},
$$

以及任何从 $\ell$ 份独立完成等待记录和与参数无关的随机化产生的均值估计器 $\widehat\mu$，存在第 62.3 条类型的二维仪器与共同来源，使其等待律属于 $\mathcal P_{p,K}$，且

$$
\boxed{
\mathbb P\!\left(
|\widehat\mu-\mu|
\ge\frac{(K-1)^{1/p}}4(2\ell)^{-r}
\right)\ge\frac14.
}
$$

证明。置 $w=1/(2\ell)$、$\gamma=(w/c_p)^{1/p}\le1$。在 $w=c_p$ 的端点，第 62.3 条的矩估计和仪器公式仍成立，只需允许 $\gamma=1$。比较 $\mathfrak I_{0,\gamma}$ 与 $\mathfrak I_{w,\gamma}$。两均值相差

$$
\Delta=\frac{(K-1)^{1/p}}2(2\ell)^{-r}.
$$

第一种记录律集中在一，因此两份 $\ell$ 重积律的总变差恰为 $1-(1-w)^\ell\le\ell w=1/2$。共同随机化不增加它。对两个模型作等先验检验，任何规则的平均错误概率至少为 $(1-w)^\ell/2\ge1/4$。

把估计器的输出与两均值的中点比较，可制成一个检验；检验错误必包含在相应的 $|\widehat\mu-\mu|\ge\Delta/2$ 事件内。因此至少一个模型的该事件概率不小于 $1/4$。$\square$

第 64.1 条的截断计数是完成记录的共同后处理，所以该下界也限制这种观测方式。固定 $1<p\le2$、$K>1$ 及失败概率 $0<\alpha<1/4$ 时，上下界给出相同的样本幂指数 $r$；这里未证明置信参数、常数或原始调用预算下的全局最优性，也不覆盖任意初态制备和相干控制查询。

这个下界不需要某个真实模型具有幂律重尾。参与反例的每个正 $\gamma$ 模型都有几何尾；使估计变难的是模型类中没有统一的几何衰减尺度。不能把“每一份模型指数衰减”自动当作“整个类满足同一个轻尾合同”。

## 65. 精确概率能互相换算，不表示有限记录同样充分

**定理 65.1（同一两轮过程的两种记录实验）。** 在第 58.1 条仪器中固定 $\gamma=1$，未知参数为 $0\le w<1$，来源为 $P_s$。所以 $\mathsf N$ 只取一、二，概率分别为 $1-w,w$，均值为 $\mu=1+w$。

加入第 50 节已标定的独立几何截止，$0<\eta\le1$、$q=1-\eta$，点击同轮优先。记 $C$ 为实际调用数，$F$ 为终端点击或截止标签。完整记录的三个可能结果为

$$
\boxed{
\begin{array}{c|c}
(C,F)&\text{概率}\\\hline
(1,\mathrm{click})&1-w\\
(1,\mathrm{abort})&w\eta\\
(2,\mathrm{click})&wq
\end{array}
}
$$

完整记录确定变量

$$
R=\mathbf1_{\{F=\mathrm{abort}\ \text{或}\ C=2\}},
\qquad R\sim\operatorname{Bernoulli}(w).
$$

反过来，由 $R$ 加一枚参数已知、与 $w$ 无关的截止硬币，可以生成上述完整记录律。因此在这个已知两点支撑族中，两种记录可经共同随机核互相模拟。

只保留终端标签时，截止指示变量为

$$
A=\mathbf1_{\{F=\mathrm{abort}\}}
\sim\operatorname{Bernoulli}(w\eta).
$$

证明。第一轮直接点击的概率为 $1-w$。否则已经进入 $u$，若此轮硬币截止则给 $(1,\mathrm{abort})$；若继续，第二轮必点击，给 $(2,\mathrm{click})$。于是完整记录恰好判断是否发生了第一轮未点击。若给定 $R=1$，按概率 $\eta,q$ 生成后两种记录；给定 $R=0$，输出第一种记录。这份模拟核不含未知的 $w$。丢弃 $C$ 就合并两种点击结果，给最后的 Bernoulli 律。$\square$

**推论 65.2（相同均值目标的方差与区分能力）。** 对 $\ell$ 份独立实验，两种无偏估计器

$$
\widehat\mu_{\mathrm{full}}=1+\frac1\ell\sum_iR_i,
\qquad
\widehat\mu_{\mathrm{flag}}=1+\frac1{\eta\ell}\sum_iA_i
$$

分别具有方差

$$
\boxed{
\operatorname{Var}\widehat\mu_{\mathrm{full}}
=\frac{w(1-w)}\ell,
\qquad
\operatorname{Var}\widehat\mu_{\mathrm{flag}}
=\frac{w(1-w\eta)}{\ell\eta}.
}
$$

对假设 $w=0$ 与任意固定 $w>0$ 的等先验最优检验，完整记录和仅终端标签的错误概率分别为

$$
\boxed{
P_{\mathrm{err}}^{\mathrm{full}}
=\frac{(1-w)^\ell}{2},
\qquad
P_{\mathrm{err}}^{\mathrm{flag}}
=\frac{(1-w\eta)^\ell}{2}.
}
$$

证明。方差由独立 Bernoulli 和得到。基准 $w=0$ 的所有完整记录都为 $(1,\mathrm{click})$，另一模型在这同一记录词上的概率为 $(1-w)^\ell$；故积律总变差为 $1-(1-w)^\ell$。只看标签时，基准全为点击，另一模型全点击的概率为 $(1-w\eta)^\ell$。各自代入等先验最小错误率 $(1-\operatorname{TV})/2$。$\square$

固定 $0<w<1$ 并令 $\eta\downarrow0$，两方差之比趋于无穷；固定 $\ell$ 时，终端标签的最优错误率趋于 $1/2$，完整记录的区分能力保持不变。两接口的运行协议及实际调用数完全相同，每份实验都至多两轮；差异在于是否保留 $C$，记录存储的费用并未计入调用成本。

而在精确概率层面，$\mathbb EA=w\eta$ 仍唯一给出 $w$，因而给出均值。这里分开的正是精确识别与统计实验的充分性。上述无偏估计器和互相模拟结论依赖已知的两点支撑；不能不带这份先验就应用于一般未知等待律。若只允许更小的矩预算 $K$，还须限制 $1+w(2^p-1)\le K$；当 $K>1$ 时，总能选取满足它的足够小的正 $w$；$K=1$ 则只允许 $w=0$。

## 66. 对全部后继状态的成本预算给出 Lipschitz 稳定性

只控制初始来源的高阶矩，允许条件后继极慢。本节改用更强的充分条件：对全部初态的剩余平均等待给共同控制。它可以比实际允许来源需要的条件更强，不作为一般必要条件。

**定义 66.1（全状态的等待成本势）。** 对有限维完整仪器的未点击伴随映射 $\mathcal A=\mathcal N^*$，假定

$$
T=\sum_{m\ge0}\mathcal A^m(I)
$$

在算子范数中收敛，记 $M=\|T\|_\infty$。则每个初态都最终点击，且由等待时间的尾和公式，其实际平均轮数为 $\operatorname{Tr}(\rho T)$。所以此处 $T$ 与前文的有限点击时间矩一致，$M$ 是所有初态的最大平均等待；没有把永不点击轨迹赋零后隐去其成本。

**引理 66.2（正预解映射的范数就是最大等待）。** 在定义 66.1 的条件下，作用于 Hermitian 算子空间的映射

$$
\mathcal R=(\operatorname{id}-\mathcal A)^{-1}
=\sum_{m\ge0}\mathcal A^m
$$

存在且正，并且

$$
\boxed{\|\mathcal R\|_{\infty\to\infty}=\|\mathcal R(I)\|_\infty=M.}
$$

这里使用 Hermitian 算子的算子范数，未假设 $\mathcal A$ 对 Hilbert–Schmidt 内积自伴。

证明。任意正映射 $\mathcal B$ 在这个实赋范空间上满足 $\|\mathcal B\|_{\infty\to\infty}=\|\mathcal B(I)\|_\infty$：对 $-I\le H\le I$，正性给 $-\mathcal B(I)\le\mathcal B(H)\le\mathcal B(I)$，而 $H=I$ 达到下界。

因此有限维下

$$
\sum_m\|\mathcal A^m\|_{\infty\to\infty}
=\sum_m\|\mathcal A^m(I)\|_\infty
\le\sum_m\operatorname{Tr}\mathcal A^m(I)
=\operatorname{Tr}T<\infty.
$$

映射级数绝对收敛。与 $\operatorname{id}-\mathcal A$ 相乘，有限和望远镜抵消，余项 $\mathcal A^{m+1}$ 趋零，故它就是逆映射。正映射级数的极限仍正，且 $\mathcal R(I)=T$；再应用首段范数恒等式。$\square$

**定理 66.3（完整仪器校准对全状态成本的乘积界）。** 两仪器具有第 63.1 条的共同接口，完整单轮半 diamond 距离为 $\delta$，并各自满足定义 66.1。则

$$
\boxed{
\|T_I-T_J\|_\infty\le\delta M_I M_J.
}
$$

证明。由 $(\operatorname{id}-\mathcal A_I)T_I=I$ 及对 $J$ 的同一等式，

$$
T_I-T_J
=\mathcal R_I(\mathcal A_I-\mathcal A_J)(T_J).
$$

因为 $I\le T_J\le M_JI$，在完整带记录输出上取效果：未点击块为 $T_J/M_J$，所有点击块为零。它是合法的 $[0,I]$ 效果，所以对每个共同输入态 $\rho$，

$$
\left|\operatorname{Tr}\rho(\mathcal A_I-\mathcal A_J)(T_J)\right|
\le M_J\delta.
$$

对全部输入态取上确界，得到 Hermitian 算子的范数界

$$
\|(\mathcal A_I-\mathcal A_J)(T_J)\|_\infty\le M_J\delta.
$$

再用引理 66.2。这里没有额外的因子二：所用的是完整输出上的一个效果，其概率差受半迹距离控制。该效果只用于证明界，不假设实验者已取得未知的 $T_J$。$\square$

**命题 66.4（乘积形式可取等号）。** 一维仪器每轮以概率 $0<\gamma_i\le1$ 点击，否则继续，其未点击分支为 $(1-\gamma_i)\operatorname{id}$、点击分支为 $\gamma_i\operatorname{id}$。两个这样的模型满足

$$
\delta=|\gamma_I-\gamma_J|,\qquad
M_i=T_i=\frac1{\gamma_i},\qquad
\boxed{|T_I-T_J|=\delta M_I M_J.}
$$

证明。单轮带记录通道是两点概率律，半迹距离就是成功概率之差；等待为几何分布，均值为 $1/\gamma_i$。取两个倒数之差即可。$\square$

**推论 66.5（把矩预算施加到所有初态的代价与收益）。** 若两仪器对每个初态都最终点击，且时间矩效果满足

$$
\mathsf M_{p,i}:=\sum_{n\ge1}n^pE_{n,i}\le KI,
$$

则它们满足定义 66.1，并有

$$
\boxed{M_i\le K^{1/p},\qquad
\|T_I-T_J\|_\infty\le K^{2/p}\delta.}
$$

证明。对每个初态 $\rho$，最终点击假设使 $\operatorname{Tr}(\rho\mathsf M_{p,i})$ 是实际等待的 $p$ 阶矩。Jensen 不等式给 $\operatorname{Tr}(\rho T_i)\le K^{1/p}$。也可先对有限尾和应用标量平均等待上界，再取单调极限；有限维正算子递增且有界，故在范数中收敛。对全部状态取上确界得到 $M_i\le K^{1/p}$，再用定理 66.3。$\square$

“对每个初态最终点击”不能从把永不点击赋零的矩效果上界单独推出：从不点击的仪器具有全部 $E_n=0$，这个矩效果为零，却有无穷实际等待。这里显式保留该条件，防止混用前文的两种时间矩约定。

第 62.3 条的二维族没有违反这个 Lipschitz 界。从 $P_s$ 准备时，进入慢分支的权重足以压低初始矩；但从条件后继 $P_u$ 重新开始，平均等待为 $1/\gamma$，其 $p$ 阶矩至少为 $\gamma^{-p}$。所以这族不满足同一个全状态预算，$M_i$ 随 $\gamma\downarrow0$ 发散。初始来源预算与可续接状态预算因此不能互换。

## 67. 关系边界还要保存任务精度与条件预算

本批的“AHH”有两部分。第一，固定 $1<p\le2$ 和 $K>1$，同一二维活动空间、同一合法仪器族中，只约束指定初态的 $p$ 阶时间矩不超过 $K$，得到的均值稳定性指数是 $(p-1)/p$，而且不能统一提高；把平均成本预算扩展到所有后继初态以后，预解恒等式给出线性的校准界。边界预算的量词范围改变了可证明的稳定性。

第二，精确概率之间存在代数换算，不代表对应的有限记录实验同样有用。第 65 节不改变实际运行，只丢弃调用数，就能令终端标签在小截止概率下几乎失去区分能力。这里不是多保存一个名字，而是保留了一份仍与未知参数相关的真实记录。

由此，时间任务的充分边界可以更明确地记为

$$
\boxed{
\begin{gathered}
\bigl(\text{共同来源与合法续接},\ \text{实际保留的记录},\\
\text{目标成本},\ \text{误差与置信水平},\ \text{预算覆盖的条件状态}\bigr).
\end{gathered}
}
$$

只给“维数有限”“全部精确概率可恢复”或“每个模型都有指数尾”，均不足以替代这些字段。第 62—66 节分别提供反例、有效模量、样本指数和更强条件下的成本界。

**说明 67.1（成熟结果、对应关系与未覆盖范围）。** 第 62.2 条的通用插值步骤对应仓内 `CountableWeightedHolderInterpolation` 的 `countable_weighted_holder_interpolation`：对剩余质量 $u_n$，取 $f_n=(n-1)^pu_n$、$g_n=u_n$、权重 $1/p$ 与 $1-1/p$。两列的非负性和可和性分别由矩预算及有限剩余质量给出。本文另外使用共同部分分解和相等剩余质量消去常数成本；未新增或编译这份精确应用的 Lean 声明。

第 63 节直接保留第 35.2 条逐轮替换证明中的实际活动质量；第 66 节使用正映射级数和预解恒等式。正映射表示它保持正算子锥，不表示其作为 Hilbert–Schmidt 空间上的线性算子是自伴的；因此这里没有把自伴正矩阵的谱下界定理直接套给一般 CP 演化。

Charles M. Grinstead、J. Laurie Snell 的 [*Introduction to Probability*，第 11.2 节](https://math.dartmouth.edu/~prob/prob/prob.pdf) 定理 11.4 给吸收 Markov 链的基本矩阵 $N=(I-Q)^{-1}=\sum_{m\ge0}Q^m$，定理 11.5 给平均吸收时间 $t=Nc$，其中 $c$ 为全一列。在经典对角子类中，$Q$ 对应未点击的函数演化 $\mathcal A$，$c$ 对应 $I$，基本矩阵对应 $\mathcal R$，吸收时间向量对应 $T$。一般 CP 情况以正算子锥替代逐坐标非负性；带记录半 diamond 距离的乘积估计由第 66.3 条证明，不归为书中原定理。

第 64 节所用的截断、Bernstein 集中和 $\ell^{-(p-1)/p}$ 均值估计指数属于成熟稳健统计工具。Sébastien Bubeck、Nicolò Cesa-Bianchi、Gábor Lugosi 的 [*Bandits with heavy tail*，arXiv:1209.1727](https://arxiv.org/abs/1209.1727)，第 2.1 节引理 1，在有限 $1+\varepsilon$ 原始矩条件下用截断经验均值得到相应置信指数。其变量可有正负值，截断阈值随样本指标变化，并使用阈值外置零的估计器；本文针对正整数等待，实际执行固定轮数截止并记录 $\min(\mathsf N,m)$，故估计器、物理取得方式和常数由第 64.1 条单独证明。原文的 bandit 遗憾下界不被当作本文固定记录数下界；第 64.2 条用实际二维仪器给出两点检验论证。

本批没有把固定记录数的指数结论升级为任意量子查询或确定总调用预算下的最优性。也没有从有限数据认证矩预算、完整仪器距离、重置合同或所有后继状态的成本上界。全部结果是指定模型和权限下的纯理论推导，不宣称文献原创性、Lean 核验、消化覆盖或冻结。

## 追加锚（本行以下为增补区）

## 68. 从完整仪器校准到可迁移的等待成本证书

**定义 68.1（共同接口、实际等待与正漂移余量）。** 固定有限维完整活动空间 $\mathcal H$。名义仪器与实际仪器分别为

$$
\widehat\Gamma(\rho)
=|\varnothing\rangle\langle\varnothing|\otimes\widehat{\mathcal N}(\rho)
+\sum_x|x\rangle\langle x|\otimes\widehat\Phi_x(\rho),
\qquad
\Gamma(\rho)
=|\varnothing\rangle\langle\varnothing|\otimes\mathcal N(\rho)
+\sum_x|x\rangle\langle x|\otimes\Phi_x(\rho).
$$

所有分支完全正，两完整映射保迹，输入、输出、记录标签与可再次作用的量子记忆一致。记

$$
\widehat{\mathcal A}=\widehat{\mathcal N}^{*},\qquad
\mathcal A=\mathcal N^{*},\qquad
\delta=\frac12\|\Gamma-\widehat\Gamma\|_\diamond.
$$

每调用一次完整仪器计一单位成本；第一次点击后停止，永不点击的轨迹成本为 $\infty$。实际等待轮数为 $\mathsf N\in\{1,2,\ldots,\infty\}$，部分成本势为

$$
T_m=\sum_{j=0}^{m-1}\mathcal A^j(I),\qquad T_0=0.
$$

给定一个非零正算子 $B$，置

$$
b=\|B\|_\infty,\qquad
\varepsilon=\lambda_{\min}\bigl(B-\widehat{\mathcal A}(B)\bigr),\qquad
c=\varepsilon-\delta b.
$$

本节的证书条件为 $c>0$。它涉及所有输入方向的算子序，不以指定来源上的平均不等式代替。

附引：平均运行时间的算子表示是已有理论。Junyi Liu、Li Zhou、Gilles Barthe、Mingsheng Ying，[*Quantum Weakest Preconditions for Reasoning about Expected Runtimes of Quantum Programs (Extended Version)*，arXiv:1911.12557v3](https://arxiv.org/abs/1911.12557v3)，定义 3.1、定理 1—2 与推论 4.1 分别给成本语义、运行时间可观测量及有限维终止结论。其语法将初始化、酉操作和测量分别计费；本节只数原完整仪器的调用次数，不把两种成本数值直接等同。Christina Gehnen、Dominique Unruh、Joost-Pieter Katoen，[*Quantum Weakest Preconditions Revisited: Pre-expectations for Expected Runtime Analysis*，arXiv:2607.12532v1](https://arxiv.org/abs/2607.12532v1)，第 6 节说明计费规则可由 reward 插入位置指定；其命题 5.11、7.6 给 Park 归纳上界。下面证明中的正性与望远镜估计是这一成熟方法在当前成本约定下的有限维步骤；新增的组合对象是完整仪器校准误差与同一证书余量。

**定理 68.2（校准损耗后的成本与加权尾界）。** 在定义 68.1 的证书条件下，实际成本势 $T=\lim_mT_m$ 在算子范数中存在。所有初态最终点击，而且

$$
\boxed{
I\le T\le\frac Bc,\qquad
\sup_\rho\mathbb E_\rho\mathsf N
=\|T\|_\infty\le\frac bc.
}
$$

进一步，令 $r=1-c/b\in[0,1)$。对任意初态 $\rho$、整数 $m\ge0$，有

$$
\boxed{
\mathbb E_\rho[(\mathsf N-m)_+]
\le\frac{\operatorname{Tr}(\rho B)}c\,r^m.
}
$$

其中 $r^0=1$，包括 $r=0$ 的情形。该结论先建立实际成本有限，无须预先假定实际仪器最终点击。

证明。在完整输出上取效果：未点击块为 $B/b$，所有点击块为零。它介于零与恒等之间。因此对任意输入态，两个完整输出在该效果上的概率差至多为 $\delta$，从而

$$
\|(\mathcal A-\widehat{\mathcal A})(B)\|_\infty\le\delta b,
\qquad
B-\mathcal A(B)\ge cI. \tag{68.1}
$$

正性给 $B\ge cI$，故 $0<c\le b$。将式 (68.1) 依次作用 $\mathcal A^j$ 并相加，得到

$$
cT_m\le B-\mathcal A^m(B)\le B.
$$

有限维递增正算子序列 $T_m$ 有界，故在范数中收敛到 $T\le B/c$。对每个初态，尾和公式与单调收敛给

$$
\mathbb E_\rho\mathsf N
=\sum_{j\ge0}\operatorname{Tr}\bigl(\rho\mathcal A^j(I)\bigr)
=\operatorname{Tr}(\rho T)<\infty.
$$

因此永不点击的概率为零。又因 $B\le bI$，有

$$
\mathcal A(B)\le B-cI\le(1-c/b)B=rB,
\qquad \mathcal A^m(B)\le r^mB.
$$

对收敛级数移项，并使用 $T\le B/c$，

$$
\sum_{j=m}^\infty\mathcal A^j(I)
=\mathcal A^m(T)
\le\frac{\mathcal A^m(B)}c
\le\frac{r^mB}c.
$$

与 $\rho$ 取迹即为加权尾界。全状态最大均值等于正算子 $T$ 的最大本征值。$\square$

**推论 68.3（先认证有限性，再传递成本差）。** 若名义成本势 $\widehat T$ 存在，$\widehat M=\|\widehat T\|_\infty$，且 $\delta\widehat M<1$，则实际仪器满足

$$
\boxed{
\|T\|_\infty\le\frac{\widehat M}{1-\delta\widehat M},\qquad
\|T-\widehat T\|_\infty
\le\frac{\delta\widehat M^2}{1-\delta\widehat M}.
}
$$

证明。取 $B=\widehat T$。由其收敛级数，$\widehat T-\widehat{\mathcal A}(\widehat T)=I$，故 $\varepsilon=1$。定理 68.2 先给实际成本存在与第一式，此后两侧都满足定理 66.3 的假设。将第一式代入其乘积界即得第二式。$\square$

## 69. 有限证书的逼近、最优标量余量与退化边界

**定义 69.1（标量余量证书的校准半径）。** 对固定名义仪器，定义

$$
\mathfrak r_{\mathrm{cert}}
=\sup\left\{
\frac{\lambda_{\min}(B-\widehat{\mathcal A}B)}{\|B\|_\infty}:
B\ge0,\ B\ne0,\ \lambda_{\min}(B-\widehat{\mathcal A}B)>0
\right\},
$$

若集合为空则取零。每个集合元素认证严格小于它的完整仪器校准距离；它是这一类证书的半径，不定义为仪器实际失去终止性的最小距离。

**定理 69.2（同一校准证书族的最优半径与有限逼近）。** 若名义成本势 $\widehat T$ 存在，则

$$
\boxed{\mathfrak r_{\mathrm{cert}}=\frac1{\widehat M}.}
$$

该上确界由 $B=\widehat T$ 达到。无需先精确取得 $\widehat T$，对整数 $m\ge1$ 定义有限算子

$$
B_m=\sum_{j=0}^{m-1}\widehat{\mathcal A}^j(I),\qquad
b_m=\|B_m\|_\infty,\qquad
\varepsilon_m=1-\|\widehat{\mathcal A}^m(I)\|_\infty
$$

也满足

$$
\boxed{
\frac{\varepsilon_m}{b_m}\longrightarrow\frac1{\widehat M}.
}
$$

因而给定任意 $\delta<1/\widehat M$，某个有限 $m$ 的证书已经具有正校准余量 $\varepsilon_m-\delta b_m>0$。

证明。任一正余量 $\varepsilon$ 与正算子 $B$，在定理 68.2 中取 $\delta=0$，得到 $\widehat T\le B/\varepsilon$，所以 $\varepsilon/b\le1/\widehat M$。取 $B=\widehat T$ 达到等号。

对有限和直接计算

$$
B_m-\widehat{\mathcal A}(B_m)
=I-\widehat{\mathcal A}^m(I).
$$

右侧最小本征值就是 $\varepsilon_m$。收敛的正级数给 $B_m\to\widehat T$ 及 $\widehat{\mathcal A}^m(I)\to0$，故 $b_m\to\widehat M$、$\varepsilon_m\to1$。最后由严格距离不等式与实数极限得到有限 $m$。这不声称比值随 $m$ 单调。$\square$

**命题 69.3（统一阈值和两个成本界均可达到）。** 任取 $\widehat M\ge1$，置 $\widehat\gamma=1/\widehat M$。取一维名义仪器每轮以概率 $\widehat\gamma$ 点击，并取实际仪器成功概率 $\gamma=\widehat\gamma-\delta$。对 $0\le\delta<1/\widehat M$，两仪器的完整半 diamond 距离正是 $\delta$，且

$$
M=\frac{\widehat M}{1-\delta\widehat M},\qquad
|T-\widehat T|=\frac{\delta\widehat M^2}{1-\delta\widehat M}.
$$

在端点 $\delta=1/\widehat M$，实际仪器永不点击。因此在只知道 $\widehat M$ 与完整仪器距离的模型类中，严格条件 $\delta\widehat M<1$ 不能统一放宽为包含端点的条件。

证明。一维完整输出是未点击、点击两点概率律，半 diamond 距离等于成功概率之差。正成功概率的等待均值为倒数；代入 $\gamma$ 给两条等式。成功概率为零时，每轮都未点击。$\square$

上述命题的量词是跨仪器类的统一界，不断言每个固定名义仪器在自己的 $1/\widehat M$ 距离处都能产生不终止扰动。

## 70. 真实记录驱动的自适应控制也需要可续接的证书

**定义 70.1（带记录后继的校准证书族）。** 允许每次未终止操作产生有限个实际可读的继续标签 $z$。有限历史 $h$ 包括此前取得的继续标签与实际控制设置；点击标签终止本次协议。每个活动历史的合法控制集合有限且非空，当前控制记为 $a$，继续分支的名义和实际 CP 映射分别为

$$
\widehat{\mathcal N}_{h,a,z},\qquad
\mathcal N_{h,a,z},
$$

作用于同一个有限维完整量子活动空间。继续后的历史记为 $h(a,z)$。每个 $(h,a)$ 的完整仪器还包括点击分支，且两侧完整映射均保迹。实际控制策略只能依赖已有历史；若随机选择控制，选择律是给定历史上的有限概率分布，实际选中的控制进入记录。未被读取的 Kraus 指标不能充当 $z$。

假设存在对全部合法历史给出的正算子 $B_h$ 和常数 $b>0$、$\varepsilon>0$、$\delta\ge0$，使对每个合法 $(h,a)$ 同时成立

$$
0\le B_h\le bI,
\qquad
B_h-\sum_z\widehat{\mathcal N}_{h,a,z}^{*}\bigl(B_{h(a,z)}\bigr)
\ge\varepsilon I,
$$

$$
\frac12\|\Gamma_{h,a}-\widehat\Gamma_{h,a}\|_\diamond\le\delta,
\qquad c:=\varepsilon-\delta b>0.
$$

这里的历史算子族是数学证书；其存在不额外授权对不可读环境或未知输入态的查询。

**定理 70.2（共同后继余量控制全部合法自适应策略）。** 在定义 70.1 下，任意上述控制策略与任意初态 $\rho$ 都满足

$$
\boxed{
\mathbb E_{\rho,\pi}\mathsf N
\le\frac{\operatorname{Tr}(\rho B_{\emptyset})}{c},\qquad
\mathbb E_{\rho,\pi}[(\mathsf N-m)_+]
\le\frac{\operatorname{Tr}(\rho B_{\emptyset})}{c}
\left(1-\frac cb\right)^m.
}
$$

因此该策略最终点击的概率为一，且上界同时覆盖所有合法策略，不要求从头固定同一个控制。这里的共同证书条件不能只由每个固定控制各自的有限成本预算替代；下面附上已有反例在本节接口中的计算。

证明。固定 $(h,a)$，在完整输出的继续标签 $z$ 上置效果 $B_{h(a,z)}/b$，点击块置零。正交经典记录使其为一个合法效果，校准距离遂给

$$
B_h-\sum_z\mathcal N_{h,a,z}^{*}\bigl(B_{h(a,z)}\bigr)\ge cI. \tag{70.1}
$$

若控制随机化，对控制概率加权后该不等式仍成立。对一个固定策略，记经过 $n$ 次调用仍活动的历史 $h$ 的未归一化态为 $\sigma_h$。定义

$$
s_n=\sum_{|h|=n}\operatorname{Tr}\sigma_h
=\mathbb P(\mathsf N>n),\qquad
V_n=\sum_{|h|=n}\operatorname{Tr}(\sigma_h B_h).
$$

由式 (70.1)，

$$
V_n-V_{n+1}\ge cs_n,\qquad
cs_n\le V_n\le bs_n.
$$

第二式左侧使用 $B_h\ge cI$，由式 (70.1) 的继续项正性得到。于是

$$
V_{n+1}\le V_n-cs_n\le(1-c/b)V_n,
\qquad V_0=\operatorname{Tr}(\rho B_{\emptyset}).
$$

对任意有限 $k>m$，望远镜相加给

$$
c\sum_{n=m}^{k-1}s_n\le V_m-V_k\le V_m.
$$

先令 $k\to\infty$，再使用 $V_m\le(1-c/b)^mV_0$，得到两条尾和界。均值有限排除正概率的无限活动轨迹。所有不等式在策略选择之前已经对全部合法 $(h,a)$ 成立，所以量词可以覆盖任意同权限策略。$\square$

附引：证明中的正性、线性期望与漂移求和沿用第 68.1 条引用的运行时间上界方法。本条把同一误差余量作用于实际记录分支上的后继算子，并保留“对全部合法控制同时成立”的量词；单个控制的终止证明不能履行该量词。

附引与反例计算：Shenggang Ying、Mingsheng Ying，[*Reachability Analysis of Quantum Markov Decision Processes*，arXiv:1406.6146v2](https://arxiv.org/abs/1406.6146v2)，定义 2.2 将调度器建立在实际操作与测量记录上；例 2.3 已给出两个分别流向吸收态、交替后却可避开吸收的通道。以下构造将其三维空间中的吸收态改记为终端点击标签、交换两个控制的命名，并以二维空间保留停止前活动状态；对应的是停止前转移和吸收概率，不把不同的点击后量子输出声明为相同通道。该反例属于已有构造在定理 70.2 量词核对中的应用，不另立新增命题。

在 $\mathbb C^2$ 上取：

$$
Q_a=|1\rangle\langle0|,\quad L_a=|0\rangle\langle1|,
\qquad
Q_b=|0\rangle\langle1|,\quad L_b=|1\rangle\langle0|.
$$

每个控制都满足仪器完备关系。若始终使用 $a$ 或始终使用 $b$，任何初态至多两轮点击，两者全状态最大平均等待均为二；但从 $|0\rangle$ 出发，依次使用 $a,b,a,b,\ldots$ 时，永不点击的概率为一。

证明。直接计算 $Q_a^\dagger Q_a+L_a^\dagger L_a=I$，$b$ 同理。又 $Q_a^2=Q_b^2=0$，所以两轮未点击概率为零。两固定仪器的成本势分别为

$$
T_a=I+|0\rangle\langle0|,\qquad
T_b=I+|1\rangle\langle1|,
$$

均具有最大本征值二。而 $Q_a|0\rangle=|1\rangle$、$Q_b|1\rangle=|0\rangle$，每次对应点击振幅均为零。归纳得到全部轮次都未点击。$\square$

对这两个控制，不存在 $B\ge0$ 与 $c>0$ 同时满足

$$
B-Q_a^\dagger BQ_a\ge cI,\qquad
B-Q_b^\dagger BQ_b\ge cI.
$$

也不存在覆盖全部控制历史、具有统一有限上界与正余量的定义 70.1 型证书族，即使两仪器的校准误差为零。

证明。记 $b_j=\langle j|B|j\rangle$。第一条不等式在 $|0\rangle$ 上给 $b_0-b_1\ge c$，第二条在 $|1\rangle$ 上给 $b_1-b_0\ge c$，相加矛盾。若有更一般的历史证书族，定理 70.2 会给交替策略有限均值，与上述交替轨迹矛盾。$\square$

该例中的每次操作都合法，问题不在单次完备性，而在新的控制把后继送回另一控制的活动方向。固定控制预算分别成立，不能作为同一个自适应过程的共同预算。

## 71. 正漂移证书的最优半径仍可小于实际终止半径

**定义 71.1（固定接口中的不终止距离）。** 对名义完整仪器 $\widehat\Gamma$，固定其量子输入、活动输出和经典记录接口，定义

$$
\mathfrak r_{\mathrm{fail}}
=\inf\left\{
\frac12\|\Gamma-\widehat\Gamma\|_\diamond:
\Gamma\text{ 是同接口完整仪器，且存在初态 }
\rho\text{ 满足 }\lim_n\operatorname{Tr}\mathcal N^n(\rho)>0
\right\}.
$$

本节仅比较有限维、每轮重复同一仪器的过程，不把增加隐藏活动维数或历史自适应控制计入同一扰动类。

**定理 71.2（二维仪器的证书半径与失效距离严格分离）。** 对两个记录标签“未点击、点击”，在 $\mathbb C^2$ 上取名义 Kraus 算子

$$
\widehat Q=|0\rangle\langle1|,\qquad
\widehat L=|0\rangle\langle0|.
$$

则

$$
\boxed{
\widehat M=2,\qquad
\mathfrak r_{\mathrm{cert}}=\frac12,
\qquad
\frac45\le\mathfrak r_{\mathrm{fail}}\le1.
}
$$

特别地，任何同接口实际仪器只要与名义仪器的完整半 diamond 距离小于 $4/5$，就对全部初态具有有限平均等待。这里不声称 $4/5$ 就是精确失效距离，也不从这个断言给出整个开球的共同均值常数。

证明。名义未点击映射为 $\widehat{\mathcal N}(\rho)=\rho_{11}|0\rangle\langle0|$，其平方为零，故

$$
\widehat T=I+|1\rangle\langle1|,
\qquad \widehat M=2.
$$

定理 69.2 给证书半径 $1/2$。

现在设实际仪器有一个正概率永不点击的初态 $\rho$。其未点击映射 $\mathcal N$ 是 CP 且迹不增。令

$$
\tau_k=\frac1k\sum_{j=0}^{k-1}\mathcal N^j(\rho).
$$

有限维下，从有界正算子列选取收敛子列。由于生存概率递减到某个 $s_\infty>0$，极限 $\tau$ 的迹为 $s_\infty$。而

$$
\mathcal N(\tau_k)-\tau_k
=\frac{\mathcal N^k(\rho)-\rho}{k}\longrightarrow0,
$$

故归一化 $\sigma=\tau/s_\infty$ 满足 $\mathcal N(\sigma)=\sigma$。完整仪器保迹使点击分支在 $\sigma$ 上为零。

若 $\sigma$ 满秩，实际点击效果 $E\ge0$ 满足 $\operatorname{Tr}(\sigma E)=0$，只能有 $E=0$。此时实际仪器对所有输入都不点击；名义仪器对输入 $|0\rangle\langle0|$ 必点击，所以两完整输出的半迹距离为一，$\delta\ge1$。

若 $\sigma$ 秩一，写 $\sigma=|\psi\rangle\langle\psi|$ 并记

$$
a=|\langle0|\psi\rangle|^2\in[0,1],\qquad P_0=|0\rangle\langle0|.
$$

同一输入 $\sigma$ 在实际仪器上给全部位于未点击块的 $\sigma$，在名义仪器上给未点击块 $(1-a)P_0$ 与点击块 $aP_0$。所以

$$
\delta\ge\frac12\left(\|\sigma-(1-a)P_0\|_1+a\right)
=\frac{a+\sqrt{a^2+4(1-a)^2}}2. \tag{71.1}
$$

末式可由差矩阵的迹 $a$、行列式 $-(1-a)^2$ 求得，包括 $a=1$ 的退化端点。又 $8/5-a>0$ 且

$$
a^2+4(1-a)^2-(8/5-a)^2
=4(a-3/5)^2\ge0.
$$

故式 (71.1) 至少为 $4/5$。秩一、秩二穷尽二维密度矩阵，得到失效距离下界。取实际仪器恒不点击且保持输入态，可给距离至多一的失效例，故上界成立。

最后，若 $\delta<4/5$，则每个初态最终点击。令 $S_n=\mathcal A^n(I)$。它是递减正算子列，所有态的期望趋零，有限维下因而 $\|S_n\|_\infty\to0$。选择有限 $m$ 使 $\|S_m\|_\infty=q<1$。正性给

$$
S_{km}\le q^kI,\qquad
\sum_{n\ge0}S_n\le\frac m{1-q}I.
$$

因此实际成本势存在，每个初态的均值有限。这最后一步是有限维齐次过程的终止—有限均值关系，亦与第 68.1 条所引有限维运行时间文献一致。$\square$

## 72. 成本边界的三个量词与证书失效的含义

**定义 72.1（来源、续接与扰动的成本要求）。** 对同一个事件任务，分别考虑：指定初态的等待成本；全部允许后继初态和控制历史的等待成本；在完整仪器校准邻域内仍成立的成本认证。三者的对象均使用实际无限轨迹成本，不把永久未点击赋零。

**定理 72.2（成本认证的三项不可替代性）。** 下列三个替代规则均不成立：

1. 以指定来源的共同高阶矩预算替代全部后继态的共同平均成本预算。
2. 以每个固定控制各自的有限成本预算替代全部合法自适应续接的共同预算。
3. 以某一完整正漂移证书族已达到最优半径，判定该半径就是装置实际失去终止性的距离。

证明。第一项由第 62.3 条的稀有慢分支族成立：固定 $1<p\le2$ 与 $K>1$，指定来源的 $p$ 阶矩统一不超过 $K$，而后继 $P_u$ 的平均等待 $1/\gamma$ 无界。第二项由定理 70.2 后附的已有反例计算成立：两个固定控制的最大均值均为二，交替控制的实际均值为无穷。第三项由定理 71.2 成立：同一个二维名义仪器的正漂移标量余量半径恰为 $1/2$，实际失效距离至少为 $4/5$。$\square$

上述三个反例把成本边界的关系要求写成了严格不同的量词：从哪个来源出发、容许哪些记录后继、对什么扰动保持认证。定理 68.2 和 70.2 给出能实际履行后两类量词的共同余量条件；定理 71.2 同时表明，这种充分条件的最优性仍不等于物理失效阈值的精确性。

## 追加锚（本行以下为增补区）

## 73. 相干暗态给出一个可精确计算的失效仪器

**定义 73.1（同一二维端口上的两个完整仪器）。** 继续使用第 71 节的共同活动空间 $\mathcal H=\mathbb C^2$、两个正交记录标签“未点击、点击”和相同量子输出空间。名义仪器 $\Gamma_0$ 与相干暗态仪器 $\Gamma_+$ 的 Kraus 算子为

$$
Q_0=|0\rangle\langle1|,\qquad L_0=|0\rangle\langle0|,
\qquad
Q_+=P_+=|+\rangle\langle+|,\qquad L_+=|0\rangle\langle-|,
$$

其中 $|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$。完整通道记为

$$
\Gamma_i(\rho)
=|\varnothing\rangle\langle\varnothing|\otimes Q_i\rho Q_i^\dagger
+|\mathrm{click}\rangle\langle\mathrm{click}|\otimes L_i\rho L_i^\dagger,
\qquad i\in\{0,+\}.
$$

每次未点击后重复同一仪器，第一次点击后停止；永久未点击的实际成本为无穷。两组算子均满足 $Q_i^\dagger Q_i+L_i^\dagger L_i=I$，因此都是完整合法仪器。

**定理 73.2（显式失效仪器的完整半 diamond 距离）。** 记

$$
c_*=\sqrt{\frac{11+5\sqrt5}{32}}.
$$

则

$$
\boxed{
\frac12\|\Gamma_+-\Gamma_0\|_\diamond=c_*.
}
$$

该最大区分距离可由单个纯系统输入达到，针对这两个指定通道不需要外部参考系统。$\Gamma_+$ 从 $P_+$ 出发永不点击，所以第 71.1 条的全量子同接口失效距离满足

$$
\boxed{
\frac45\le\mathfrak r_{\mathrm{fail}}\le c_*<1.
}
$$

右侧是由一个具体失效仪器提供的上界；此处不把 $c_*$ 声明为全体失效仪器的最小距离。

证明。由于通道之差保持 Hermitian 性，其 diamond 范数可以在纯联合输入上取最大，参考维数取输入维数已经足够。这里使用 John Watrous，[*The Theory of Quantum Information*，第 3.3.3 节、定理 3.51、式 (3.291)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf#page=184) 的标准表征；同节定理 3.52 说明其通道区分含义。下面为当前两个完整仪器计算该最大值，而不是由系统输入上的若干检验代替 diamond 范数。

对任意纯联合输入 $|\Psi\rangle_{R\mathcal H}$，写系统边缘态为

$$
\rho=
\begin{pmatrix}
a&u+iv\\
u-iv&1-a
\end{pmatrix},
\qquad
0\le a\le1,\quad u^2+v^2\le a(1-a),
\qquad x=a-u.
$$

每个记录块都是两个未归一化纯态的差。对任意向量 $\xi,\zeta$，由它们张成的至多二维空间中的迹与行列式，

$$
\bigl\||\xi\rangle\langle\xi|-|\zeta\rangle\langle\zeta|\bigr\|_1
=\sqrt{(\|\xi\|^2+\|\zeta\|^2)^2-4|\langle\xi,\zeta\rangle|^2}.
\tag{73.1}
$$

线性相关或零向量情形由同式直接包含。对未点击块，两向量的范数平方为 $1/2+u$、$1-a$，内积模平方为 $\bigl((1-a+u)^2+v^2\bigr)/4$；对点击块，相应三量为 $1/2-u$、$a$、$\bigl((a-u)^2+v^2\bigr)/2$。正交记录块的迹范数相加，故完整输出半迹距离恰为

$$
F(x,v)
=\frac12\left[
\sqrt{\frac54-x-v^2}
+\sqrt{\frac14+x-x^2-2v^2}
\right].
\tag{73.2}
$$

将 $\rho$ 的虚部 $v$ 置零保持正性与迹一，且不改变 $x$，两个根号内的数均不减。因此最大值可在实密度矩阵上取得。

定义实对称算子

$$
H=
\begin{pmatrix}
1&-1/2\\
-1/2&0
\end{pmatrix}.
$$

有 $x=\operatorname{Tr}(\rho H)$，故

$$
x\in J:=
\left[\frac{1-\sqrt2}{2},\frac{1+\sqrt2}{2}\right].
$$

反过来，$J$ 中每个点都由某个实纯态达到：取 $H$ 的实正交本征基，对两个本征向量作具有适当实系数的归一化叠加，其期望遍历整个区间。因此 diamond 最大化归结为单变量函数

$$
f(x)=F(x,0)
=\frac12\left[\sqrt{\frac54-x}+\sqrt{\frac14+x-x^2}\right],
\qquad x\in J.
$$

两项在 $J$ 上均为凹函数，第一项严格凹。其内部导数为

$$
f'(x)
=\frac14\left[
-\frac1{\sqrt{5/4-x}}
+\frac{1-2x}{\sqrt{1/4+x-x^2}}
\right].
$$

取 $x_*=(3-\sqrt5)/4$，它位于 $J$ 内部，直接代入给 $f'(x_*)=0$。所以它是唯一最大点。记 $s=\sqrt5$，则

$$
\frac54-x_*=\frac{2+s}{4},\qquad
\frac14+x_*-x_*^2=\frac{1+s}{8},
$$

$$
\sqrt{\left(\frac54-x_*\right)
\left(\frac14+x_*-x_*^2\right)}
=\frac{3+s}{8}.
$$

于是 $f(x_*)^2=(11+5s)/32$，得到精确距离。由于 $x_*$ 也可由实纯系统态实现，外部参考并非达到这对通道最坏距离的必要资源。这不推广为任意仪器对都无纠缠辅助增益。

最后，$Q_+|+\rangle=|+\rangle$ 且 $L_+|+\rangle=0$，故 $\Gamma_+$ 是一个实际不终止仪器。它给 $\mathfrak r_{\mathrm{fail}}\le c_*$；下界沿用定理 71.2。$\sqrt5<3$ 还给 $c_*^2<26/32<1$。$\square$

## 74. 限制未点击后继的相干权限，会改变失效距离

**定义 74.1（对角不变的未点击扰动类）。** 仍固定定义 73.1 的名义仪器与完整端口。称实际未点击映射 $\mathcal N$ 对角不变，若每个计算基对角密度矩阵经过 $\mathcal N$ 后仍为对角正算子；输出可以未归一化。不要求它抹除任意输入的相干项，也不要求点击分支满足额外对角条件。

令 $\mathfrak r_{\mathrm{diag}}$ 为第 71.1 条失效距离的受限版本：取下确界时只允许未点击映射对角不变的完整仪器，距离仍用完整半 diamond 范数。活动空间和完整量子输出接口均不改变。

**定理 74.2（对角不变类的失效距离严格大于相干例子的距离）。** 有

$$
\boxed{
\mathfrak r_{\mathrm{diag}}=1,
\qquad
\mathfrak r_{\mathrm{fail}}\le c_*<\mathfrak r_{\mathrm{diag}}.
}
$$

因而即使名义过程把两个基输入都送到同一个量子输出，允许扰动生成相干后继仍会严格缩小到永久未点击的距离。

证明。设对角不变的 $\mathcal N$ 从某初态 $\rho$ 出发具有正的永不点击概率。因为 $\rho\le I$，有 $I/2\ge\rho/2$；正性给

$$
\operatorname{Tr}\mathcal N^n(I/2)
\ge\frac12\operatorname{Tr}\mathcal N^n(\rho).
$$

所以从 $I/2$ 出发也有正的永久生存概率，而且每个 $\mathcal N^n(I/2)$ 都对角。应用第 71.2 条证明中的 Cesàro 平均构造，得到一个对角未点击固定态

$$
\sigma=aP_0+(1-a)P_1,\qquad
\mathcal N(\sigma)=\sigma.
$$

若 $0<a<1$，$\sigma$ 满秩。完整保迹性使点击效果在 $\sigma$ 上期望为零，正性迫使整个点击效果为零。输入 $P_0$ 时，实际仪器必未点击，名义仪器必点击，完整输出可完美区分，距离为一。

若 $a=1$，同一个输入 $P_0$ 直接给上述正交记录。若 $a=0$，实际仪器对 $P_1$ 输出未点击块中的 $P_1$，名义仪器对它输出未点击块中的 $P_0$。记录虽相同，量子后继正交，完整输出仍可完美区分。

因此受限类中每个失效仪器与 $\Gamma_0$ 的完整半 diamond 距离都至少为一；通道间该距离至多为一，所以恰为一。未点击恒等映射、零点击分支给一个该类内的失效实例，保证下确界的对象非空。再结合定理 73.2。$\square$

## 75. 同一次校准若丢掉量子后继，失效距离可以变为零

**定义 75.1（只保留单轮结果标签的校准）。** 对共同完整仪器 $\Gamma$，定义结果通道

$$
\mathcal M_\Gamma(\rho)
=\operatorname{Tr}_{\mathcal H}\Gamma(\rho),
\qquad
\delta_{\mathrm{rec}}(\Gamma,\Gamma_0)
=\frac12\|\mathcal M_\Gamma-\mathcal M_{\Gamma_0}\|_\diamond.
$$

它保留单次调用的未点击或点击标签。校准实验仍可使用外部参考；但每次调用后的活动量子输出不属于读出。该伪距离可能把不同完整仪器识别成同一点。

令 $\mathfrak r_{\mathrm{rec}}$ 为对同一名义仪器、同一不终止目标，使用 $\delta_{\mathrm{rec}}$ 取代完整距离得到的下确界。这里的读出不包括重复调用后的全部时间记录；后者是另一类实验。

**定理 75.2（显式仪器同时区分三种校准合同）。** 对定义 73.1 的两个仪器，有

$$
\boxed{
\delta_{\mathrm{rec}}(\Gamma_+,\Gamma_0)=\frac1{\sqrt2}
<
\frac12\|\Gamma_+-\Gamma_0\|_\diamond=c_*.
}
$$

另取

$$
Q_c=P_1,\qquad L_c=P_0
$$

定义完整仪器 $\Gamma_c$。则

$$
\boxed{
\mathcal M_{\Gamma_c}=\mathcal M_{\Gamma_0},\qquad
\frac12\|\Gamma_c-\Gamma_0\|_\diamond=1,\qquad
\mathfrak r_{\mathrm{rec}}=0.
}
$$

这些等式对同一合法二维仪器族成立，不以改变活动维数或把未读 Kraus 指标当作记录实现。

证明。两个二结果测量的未点击效果差为

$$
F=P_+-P_1
=\frac12
\begin{pmatrix}
1&1\\
1&-1
\end{pmatrix},
\qquad
F^2=\frac12I.
$$

对任意联合输入态 $\eta_{R\mathcal H}$，两结果通道的差在两个记录块上分别为 $X_R$ 与 $-X_R$，其中

$$
X_R=\operatorname{Tr}_{\mathcal H}[(I_R\otimes F)\eta].
$$

用 $F=F_+-F_-$ 的正负部分分解，得到

$$
\|X_R\|_1
\le\operatorname{Tr}[(I_R\otimes|F|)\eta]
\le\|F\|_\infty.
$$

完整记录差的半迹范数恰为 $\|X_R\|_1$。取 $F$ 的一个归一化本征态作为系统输入就达到 $\|F\|_\infty=1/\sqrt2$；这也证明参考系统不能提高本例的结果通道距离。定理 73.2 给完整距离，而

$$
c_*^2-\frac12=\frac{5(\sqrt5-1)}{32}>0
$$

给严格不等式。

对 $\Gamma_c$，未点击、点击效果仍为 $P_1,P_0$，与 $\Gamma_0$ 完全相同，故两个结果通道作为线性映射相等，包括任意参考扩展。另一方面，输入 $P_1$ 后，$\Gamma_c$ 永久保持 $P_1$ 且不点击；$\Gamma_0$ 的单轮未点击后继为 $P_0$，下一轮必点击。第一轮的两个量子输出已经正交，所以完整单轮距离为一。由于 $\Gamma_c$ 是结果伪距离为零的实际失效仪器，$\mathfrak r_{\mathrm{rec}}=0$。$\square$

相同效果遗漏后继的现象属于量子仪器与 POVM 的既有区别；它不被当作新的测量原理。这里的计算把它与同一个名义仪器的正失效半径、相干失效上界及对角不变阈值放在同一比较中。

## 76. 有限占据态给出超出原证书半径的显式成本界

**定义 76.1（有限调用的归一化占据态）。** 对任一同接口实际仪器 $\Gamma$，记未点击、点击分支为 $\mathcal N,\mathcal C$。给定初态 $\rho$、整数 $n\ge1$，置

$$
\rho_j=\mathcal N^j(\rho),\qquad
s_j=\operatorname{Tr}\rho_j,\qquad
\mu_n=\sum_{j=0}^{n-1}s_j=\mathbb E_\rho\min(\mathsf N,n),
$$

$$
\sigma_n=\frac1{\mu_n}\sum_{j=0}^{n-1}\rho_j.
$$

由于 $s_0=1$，有 $\mu_n\ge1$，且 $\sigma_n$ 是归一化密度矩阵。它把前 $n$ 轮的活动态按实际活动质量组合；定义不使用无限运行的收敛性。

**定理 76.2（$\delta<4/5$ 校准球中的统一平均等待界）。** 设实际完整仪器满足

$$
\frac12\|\Gamma-\Gamma_0\|_\diamond\le\delta<\frac45,
\qquad \delta\ge0.
$$

则对每个初态 $\rho$，实际等待均值满足

$$
\boxed{
\mathbb E_\rho\mathsf N
\le
\frac{3-\delta}{(1-\delta)(4/5-\delta)}.
}
$$

该上界同时覆盖整个指定校准球与全部初态，不预设其中各实际模型已经终止。因此它在 $1/2\le\delta<4/5$ 的范围仍给有限的显式成本保证，尽管第 69.1 条标量余量证书族无法认证这些距离。

证明。先固定有限 $n$，不假定无限成本势存在。由望远镜恒等式，

$$
\mathcal N(\sigma_n)-\sigma_n
=\frac{\rho_n-\rho}{\mu_n},
\qquad
\operatorname{Tr}\mathcal C(\sigma_n)
=\frac{1-s_n}{\mu_n}.
$$

把 $\sigma_n$ 全放入未点击记录块形成理想联合态，记为 $|\varnothing\rangle\langle\varnothing|\otimes\sigma_n$。记录块正交、点击分支为正以及 $\|\rho_n-\rho\|_1\le s_n+1$ 给

$$
D\!\left(
\Gamma(\sigma_n),
|\varnothing\rangle\langle\varnothing|\otimes\sigma_n
\right)
\le\frac{(1+s_n)+(1-s_n)}{2\mu_n}
=\frac1{\mu_n}.
\tag{76.1}
$$

这里 $D$ 为半迹距离。

设 $\sigma_n$ 的最小本征值为 $t\in[0,1/2]$。选择最大本征值对应的秩一投影 $P$，则 $D(\sigma_n,P)=t$，包括 $t=1/2$ 的退化情况。记实际点击效果为 $E=\mathcal C^*(I)$。名义仪器对 $P_0$ 必点击，完整校准界于是给

$$
\langle0|E|0\rangle\ge1-\delta,\qquad
\operatorname{Tr}E\ge1-\delta.
$$

由 $\sigma_n\ge tI$，

$$
t(1-\delta)
\le\operatorname{Tr}(\sigma_nE)
=\frac{1-s_n}{\mu_n}
\le\frac1{\mu_n},
\qquad
t\le\frac1{(1-\delta)\mu_n}.
\tag{76.2}
$$

另一方面，对任意纯态投影 $P$，第 71.2 条的秩一计算给

$$
D\!\left(
\Gamma_0(P),
|\varnothing\rangle\langle\varnothing|\otimes P
\right)
=\frac{a+\sqrt{a^2+4(1-a)^2}}2
\ge\frac45,
\qquad a=\operatorname{Tr}(P P_0).
\tag{76.3}
$$

这个纯态不等式只涉及名义仪器；它不要求 $P$ 是实际仪器的固定态。沿

$$
\Gamma_0(P),\quad
\Gamma_0(\sigma_n),\quad
\Gamma(\sigma_n),\quad
|\varnothing\rangle\langle\varnothing|\otimes\sigma_n,\quad
|\varnothing\rangle\langle\varnothing|\otimes P
$$

应用三角不等式。名义通道的收缩性、校准界和式 (76.1)—(76.3) 依次给

$$
\frac45
\le 2t+\delta+\frac1{\mu_n}
\le\delta+\frac1{\mu_n}\left(1+\frac2{1-\delta}\right).
$$

因为 $\delta<4/5$，可移项得到

$$
\mu_n
\le\frac{3-\delta}{(1-\delta)(4/5-\delta)}.
$$

最后令 $n\to\infty$，$\min(\mathsf N,n)$ 单调增加到实际扩展等待 $\mathsf N$，单调收敛给结论并排除正概率的无穷等待。$\square$

**推论 76.3（同一校准球中的两类有效成本证书）。** 当 $0\le\delta<1/2$ 时，可同时使用第 68.3 条和定理 76.2，得到

$$
\boxed{
\sup_{\Gamma:\,D_\diamond(\Gamma,\Gamma_0)\le\delta}
\ \sup_\rho\mathbb E_\rho^\Gamma\mathsf N
\le
\min\left\{
\frac2{1-2\delta},
\frac{3-\delta}{(1-\delta)(4/5-\delta)}
\right\}.
}
$$

当 $1/2\le\delta<4/5$ 时，第二项仍独立有效。这里 $D_\diamond$ 表示完整仪器的半 diamond 距离。

证明。名义最大成本为二，所以第 68.3 条给第一项；定理 76.2 给第二项，且两项对相同的每个实际仪器与初态同时成立，因而可取其最小值。$\square$


## 77. 一个固定装置的四个半径不能互换

**定义 77.1（固定名义装置的四种比较）。** 对 $\Gamma_0$，同时保留以下量词与观察范围：

| 量 | 校准所见 | 允许的实际仪器或证书 |
| --- | --- | --- |
| $\mathfrak r_{\mathrm{cert}}$ | 完整记录与量子后继 | 第 69.1 条的正漂移标量余量证书 |
| $\mathfrak r_{\mathrm{fail}}$ | 完整记录与量子后继 | 全部同接口二维齐次 CP 仪器 |
| $\mathfrak r_{\mathrm{diag}}$ | 完整记录与量子后继 | 未点击映射保持计算基对角态的仪器 |
| $\mathfrak r_{\mathrm{rec}}$ | 单轮经典结果标签 | 全部同接口二维齐次 CP 仪器 |

前三行使用相同的完整距离，但第一行只优化第 69.1 条的特定证书族，后两行寻找实际失效过程；第四行更换了校准读出。定理 76.2 给出了越过第一行半径的另一类有效成本论证，故此处不把某个证书族的半径等同于全部可认证范围。

**定理 77.2（同一来源下的严格半径分层）。** 上述四种比较满足

$$
\boxed{
\mathfrak r_{\mathrm{rec}}=0
<
\mathfrak r_{\mathrm{cert}}=\frac12
<
\frac45
\le
\mathfrak r_{\mathrm{fail}}
\le
\sqrt{\frac{11+5\sqrt5}{32}}
<
\mathfrak r_{\mathrm{diag}}=1.
}
$$

证明。证书半径由定理 69.2 与名义最大均值二得到；完整失效下界由定理 71.2 给出；显式相干仪器与其精确距离由定理 73.2 给上界；对角不变阈值和结果伪距离阈值分别由定理 74.2、75.2 给出。各量均针对同一个 $\Gamma_0$，所以这些结论可以共同排列；并未把不同名义装置各自达到的极值拼在一起。$\square$

**定义 77.3（仍待确定的全量子最小距离）。** 定理 77.2 将全量子失效距离限制在闭区间 $[4/5,c_*]$，但未决定它是否等于显式仪器 $\Gamma_+$ 的距离 $c_*$。证明等号仍需要对全部同接口不终止 CP 仪器建立距离至少为 $c_*$ 的下界；推翻等号则需要一个距离严格小于 $c_*$ 的实际不终止仪器。单独优化 $\Gamma_+$ 的输入，或只给出若干候选的距离，均未履行这个全仪器量词。

## 追加锚（本行以下为增补区）

## 78. 饱和一个暗态下界，还必须与相邻相干输入相容

本批接续第 73—77 节，将同一二维、齐次、完整仪器的失效距离下界从 $4/5$ 加强为严格大于 $4/5$，并确定这个改进对等待成本的含义。第 71.2、73.2、76.2 条的既有结论仍成立；本批不改写旧字节，也不把第 73 节的显式候选宣布为全局最优。

始终固定完整活动记忆 $\mathcal H=\mathbb C^2$、两个可读记录“未点击、点击”和同一个量子后继空间。实际仪器写为

$$
\Gamma(\rho)
=|\varnothing\rangle\langle\varnothing|\otimes\mathcal N(\rho)
+|\mathrm c\rangle\langle\mathrm c|\otimes\mathcal C(\rho),
$$

其中两分支完全正，$\mathcal N+\mathcal C$ 保迹；每个装置在所有轮次重复自身同一仪器。名义仪器仍为

$$
Q_0=|0\rangle\langle1|,\qquad
L_0=|0\rangle\langle0|,\qquad
\Gamma_0=(\mathcal N_0,\mathcal C_0).
$$

距离始终是完整记录与量子后继都保留时的

$$
\delta(\Gamma)=\frac12\|\Gamma-\Gamma_0\|_\diamond.
$$

**引理 78.1（纯未点击固定态对相干方向的约束）。** 设 $\mathcal N(P)=P$，其中 $P=|\psi\rangle\langle\psi|$。选单位向量 $\eta\perp\psi$，置 $R=|\eta\rangle\langle\eta|$。则存在 $\lambda\in[0,1]$ 与 $d\in\mathbb C$，使

$$
\boxed{
\mathcal C^*(I)=\lambda R,\qquad
\mathcal N(|\psi\rangle\langle\eta|)
=d|\psi\rangle\langle\eta|,\qquad
|d|^2\le1-\lambda.
} \tag{78.1}
$$

此外，若 $a=|\langle0|\psi\rangle|^2$，则

$$
\boxed{\lambda(1-a)\ge1-\delta(\Gamma).} \tag{78.2}
$$

证明。为两分支分别选有限 Kraus 族 $A_i,B_j$。由于

$$
\sum_i|A_i\psi\rangle\langle A_i\psi|=P,
$$

每个 $A_i\psi$ 都与 $\psi$ 共线。完整保迹及 $\operatorname{Tr}\mathcal N(P)=1$ 又使每个 $B_j\psi=0$。在正交基 $(\psi,\eta)$ 中可写

$$
A_i=
\begin{pmatrix}
 c_i&u_i\\0&v_i
\end{pmatrix},\qquad
\sum_i|c_i|^2=1.
$$

因为点击效果为正且湮灭 $\psi$，它具有形式 $\lambda R$。完整性矩阵等式的非对角项和第二个对角项分别给出

$$
\sum_i\overline{c_i}u_i=0,\qquad
\sum_i(|u_i|^2+|v_i|^2)+\lambda=1.
$$

因此

$$
\begin{aligned}
\mathcal N(|\psi\rangle\langle\eta|)
&=\left(\sum_i c_i\overline{u_i}\right)P
  +\left(\sum_i c_i\overline{v_i}\right)|\psi\rangle\langle\eta|\\
&=d|\psi\rangle\langle\eta|,
\end{aligned}
$$

且 Cauchy–Schwarz 不等式给

$$
|d|^2\le\sum_i|v_i|^2\le1-\lambda.
$$

这一步覆盖任意 Kraus 数，不把不可读 Kraus 指标当成额外记录。

最后，对输入 $P_0=|0\rangle\langle0|$，名义点击概率为一。完整输出距离控制点击事件的概率差，所以实际点击概率至少为 $1-\delta(\Gamma)$；而该概率恰为 $\lambda\operatorname{Tr}(RP_0)=\lambda(1-a)$。得到式 (78.2)。$\square$

**定理 78.2（距离 $4/5$ 的完整仪器不可能永久未点击）。** 任一同接口实际仪器若有正概率永不点击的初态，则

$$
\boxed{\delta(\Gamma)>\frac45.} \tag{78.3}
$$

这里先断言每个失效仪器的严格不等式；把它升级成失效集合的统一严格间隔，还需要第 79 节的紧性。

证明。第 71.2 条已经证明失效必给 $\delta\ge4/5$，并产生一个未点击固定密度矩阵。假设存在失效仪器满足 $\delta=4/5$。固定态不可能满秩，否则同条证明给 $\delta=1$。因此它为纯态 $P=|\psi\rangle\langle\psi|$。

同一输入的下界

$$
f(a)=\frac{a+\sqrt{a^2+4(1-a)^2}}2\ge\frac45
$$

只能在 $a=3/5$ 取等，故 $|\langle0|\psi\rangle|^2=3/5$。式 (78.2) 于是给

$$
\lambda\ge\frac12,\qquad |d|\le\frac1{\sqrt2}. \tag{78.4}
$$

为计算相干方向，可令

$$
\psi=\sqrt{\frac35}|0\rangle+\sqrt{\frac25}|1\rangle,
\qquad
\eta=-\sqrt{\frac25}|0\rangle+\sqrt{\frac35}|1\rangle,
\qquad r=\frac{\sqrt6}{5}.
$$

这个相位选择不限制实际仪器类：对输入和量子输出同步作计算基对角酉变换，$\Gamma_0$ 不变，完整 diamond 距离不变，且任意相位的 $\psi$ 可变为上述形式。

考察未点击输出差

$$
D=P-\frac25P_0.
$$

其本征值为 $4/5,-1/5$，所以其符号算子为

$$
S=\operatorname{sign}D=2D-\frac35I,
\qquad \|S\|_\infty=1.
$$

在完整输出上选同一个 Hermitian 检验

$$
Z=|\varnothing\rangle\langle\varnothing|\otimes S
  -|\mathrm c\rangle\langle\mathrm c|\otimes I,
\qquad \|Z\|_\infty=1,
$$

并将它拉回输入端：

$$
M=\frac12(\Gamma^*-\Gamma_0^*)(Z).
$$

对每个输入密度矩阵 $\rho$，迹范数对偶性与完整校准给 $|\operatorname{Tr}(\rho M)|\le\delta$，故

$$
-\delta I\le M\le\delta I. \tag{78.5}
$$

在固定态 $P$ 上，两个记录块之差为 $D$ 与 $-(3/5)P_0$，所以

$$
\langle\psi|M|\psi\rangle
=\frac12\left(\|D\|_1+\frac35\right)
=\frac45=\delta.
$$

由于 $\delta I-M\ge0$，一个向量上的二次型为零便使该向量落入其核。因此

$$
\langle\eta|M|\psi\rangle=0. \tag{78.6}
$$

另一方面，置 $H=|\psi\rangle\langle\eta|+|\eta\rangle\langle\psi|$。引理 78.1 与 $B_j\psi=0$ 给

$$
\mathcal N(H)=d|\psi\rangle\langle\eta|
+\overline d|\eta\rangle\langle\psi|,
\qquad \mathcal C(H)=0.
$$

名义分支满足

$$
\mathcal N_0(H)=2rP_0,\qquad
\mathcal C_0(H)=-2rP_0.
$$

直接计算 $\langle0|S|0\rangle=-1/5$ 与 $\langle\eta|S|\psi\rangle=4r/5$，得到

$$
\begin{aligned}
2\operatorname{Re}\langle\eta|M|\psi\rangle
&=\operatorname{Tr}(MH)\\
&=\frac12\left(
\frac{8r}{5}\operatorname{Re}d+\frac{2r}{5}-2r
\right)\\
&=\frac{4r}{5}(\operatorname{Re}d-1).
\end{aligned} \tag{78.7}
$$

式 (78.6) 迫使 $\operatorname{Re}d=1$，与式 (78.4) 矛盾。故等号不可能成立。$\square$

这个证明的作用点是同一装置对不同输入的相容性。暗态本身使一个距离检验饱和；全输入校准于是迫使相邻相干方向的交叉项为零，而完全正性与点击概率给出不相容的约束。只优化单个固定态上的读数，遗漏了这一层关系。

## 79. 从每个失效都严格更远，到一个共同的正间隔

**引理 79.1（失效集合紧致，最短失效距离取得）。** 在上述固定有限输入、输出和记录接口内，全部完整仪器组成紧致集 $\mathfrak I$。其中

$$
\mathfrak F=
\{\Gamma\in\mathfrak I:\exists\rho,\
\lim_n\operatorname{Tr}\mathcal N_\Gamma^n(\rho)>0\}
$$

也是非空紧致集。因此存在实际失效仪器 $\Gamma_*$，使

$$
\boxed{
\mathfrak r_{\mathrm{fail}}
=\min_{\Gamma\in\mathfrak F}\delta(\Gamma)
=\delta(\Gamma_*).
} \tag{79.1}
$$

证明。用各记录分支的 Choi 矩阵表示仪器，完全正性给正半定约束，完整保迹给固定的部分迹等式。各 Choi 矩阵的迹非负且其和为输入维数，因而这是有限维实向量空间中的闭有界集，故紧致。此处允许每个分支任意有限 Kraus 表示，不先固定 Kraus 数再取一个可能遗漏边界的参数集。

第 71.2 条的 Cesàro 证明给

$$
\Gamma\in\mathfrak F
\iff\exists\sigma\ge0,\quad
\operatorname{Tr}\sigma=1,\quad
\mathcal N_\Gamma(\sigma)=\sigma. \tag{79.2}
$$

反向显然：从该固定态出发始终未点击。仪器与密度矩阵的乘积空间紧致，式 (79.2) 的等式连续，所以符合条件的联合集合闭且紧致。向仪器坐标的投影仍紧致。恒等未点击、零点击仪器属于其中，故集合非空。有限维中的 diamond 范数连续，最小值因此取得。$\square$

**定理 79.2（完整失效半径严格超过 $4/5$）。** 对第 78 节的同一个名义仪器，

$$
\boxed{
\frac45<\mathfrak r_{\mathrm{fail}}
\le\sqrt{\frac{11+5\sqrt5}{32}}.
} \tag{79.3}
$$

证明。引理 79.1 使最小值由某个失效仪器取得；定理 78.2 排除该仪器的距离为 $4/5$。上界是第 73.2 条显式相干失效仪器的已算距离。$\square$

本条证明了严格间隔存在，没有给出该间隔的显式数值，也没有证明右端就是最小值。不能从“每个成员都严格大于”直接跳到“下确界严格大于”；紧性与取得性正是这里新增且不可省的连接。

## 80. 真正的失效半径，也是统一等待预算失效的位置

**定义 80.1（完整校准球的最坏实际成本）。** 对 $0\le u\le1$，定义

$$
\mathfrak B_u=\{\Gamma\in\mathfrak I:\delta(\Gamma)\le u\},
\qquad
\mathscr K(u)=\sup_{\Gamma\in\mathfrak B_u}\sup_\rho
\mathbb E_\rho^\Gamma\mathsf N.
$$

这里 $\mathsf N$ 是包括首次点击那一轮在内的实际调用数，永久未点击轨迹取 $+\infty$。每个装置重复自己同一仪器，$\sup_\Gamma$ 不允许在一次执行中逐轮更换装置。

**定理 80.2（校准球内共同指数尾与有限成本的精确阈值）。** 对上述二维名义仪器，

$$
\boxed{\mathscr K(u)<\infty\iff u<\mathfrak r_{\mathrm{fail}}.} \tag{80.1}
$$

更具体地，对每个固定 $u<\mathfrak r_{\mathrm{fail}}$，存在共同整数 $m\ge1$，使球内每个仪器、每个初态以及所有 $n\ge0$ 同时满足

$$
\boxed{
\Pr_\rho^\Gamma(\mathsf N>n)
\le2^{-\lfloor n/m\rfloor},
\qquad
\mathbb E_\rho^\Gamma\mathsf N\le2m.
} \tag{80.2}
$$

证明。校准球 $\mathfrak B_u$ 是紧致仪器集中的闭子集。因 $u<\mathfrak r_{\mathrm{fail}}$，其中每个仪器对全部初态最终点击。令

$$
\mathcal A_\Gamma=\mathcal N_\Gamma^*,\qquad
f_n(\Gamma)=\|\mathcal A_\Gamma^n(I)\|_\infty.
$$

每个 $f_n$ 连续，$1=f_0\ge f_1\ge\cdots\ge0$。对固定装置，全状态终止及有限维性给 $f_n\to0$，与第 71.2 条末段相同。

开集 $U_n=\{\Gamma\in\mathfrak B_u:f_n(\Gamma)<1/2\}$ 递增并覆盖整个球。紧性给有限子覆盖，取最大指标 $m\ge1$，便有所有装置同时满足

$$
\mathcal A_\Gamma^m(I)\le\frac12I.
$$

这是第 40.2 条已使用的单调紧性机制在全状态生存效果上的应用。对每个固定装置，正性与齐次重复给

$$
\mathcal A_\Gamma^{km}(I)\le2^{-k}I.
$$

其余时刻由生存效果单调性控制，得到式 (80.2) 的尾界；尾和按每 $m$ 项分组，给 $\mathbb E\mathsf N\le m\sum_{k\ge0}2^{-k}=2m$。这一步没有交换未经控制的上确界与无穷和。

反之，若 $u\ge\mathfrak r_{\mathrm{fail}}$，引理 79.1 的最小失效仪器就在球内。从其未点击固定态出发，$\mathsf N=\infty$ 几乎必然，故 $\mathscr K(u)=\infty$。$\square$

**推论 80.3（旧显式公式的极点并非真实成本极点）。** 存在 $\varepsilon>0$ 与有限 $C$，使

$$
\boxed{\mathscr K(4/5+\varepsilon)\le C<\infty.} \tag{80.3}
$$

特别地，包含端点的整个 $4/5$ 校准球有共同有限预算。

证明。由定理 79.2，可取 $\varepsilon=(\mathfrak r_{\mathrm{fail}}-4/5)/2>0$；再应用定理 80.2。$\square$

第 76.2 条的显式上界

$$
K_u=\frac{3-u}{(1-u)(4/5-u)}
$$

在 $u\uparrow4/5$ 发散，但实际最坏均值在一个更大的闭球上仍共同有界。因此这一发散属于该显式估计的局限。反过来，本条的紧性证明不给出可直接代入的 $\varepsilon,m,C$，不能替代第 76.2 条已经给出的数值预算。

**定理 80.4（接近真实失效边界必有倒数级成本下界）。** 对每个 $0\le u<\mathfrak r_{\mathrm{fail}}$，

$$
\boxed{
\mathscr K(u)\ge
\frac{\mathfrak r_{\mathrm{fail}}}
{\mathfrak r_{\mathrm{fail}}-u}.
} \tag{80.4}
$$

因而 $\mathscr K(u)\to\infty$ 当 $u\uparrow\mathfrak r_{\mathrm{fail}}$。

证明。取引理 79.1 的最小失效仪器 $\Gamma_*$ 及其未点击固定密度矩阵 $\sigma_*$。令

$$
t=\frac{u}{\mathfrak r_{\mathrm{fail}}}\in[0,1),
\qquad
\Gamma_t=t\Gamma_*+(1-t)\Gamma_0.
$$

这是同接口完整仪器，其分支逐一取相同凸组合；每一轮都重复这个固定映射。由范数齐次性，

$$
\frac12\|\Gamma_t-\Gamma_0\|_\diamond
=t\mathfrak r_{\mathrm{fail}}=u.
$$

又 $\mathcal N_t(X)\ge t\mathcal N_*(X)$ 对每个 $X\ge0$ 成立。反复使用正性与 $\mathcal N_*(\sigma_*)=\sigma_*$，得到

$$
\mathcal N_t^n(\sigma_*)\ge t^n\sigma_*.
$$

因此这个合法装置和初态的生存概率至少为 $t^n$，尾和至少为 $\sum_{n\ge0}t^n=1/(1-t)$，即式 (80.4)。$\Gamma_t$ 距离严格小于失效半径，定理 80.2 同时保证其实际均值有限；证明给的是越来越大的有限成本，而没有把失效端点提前代入。$\square$

凸组合在这里必须逐轮按同一无记忆随机机制实现，或直接作为同一个 CP 仪器使用。如果在执行开始时只抽一次装置并一直保留选择，就引入了额外持久记忆，给出不同过程；那种混合不属于本证明。

## 81. 本批所得的关系与未解决边界

**结论 81.1（单态饱和、全接口相容与真实成本边界）。** 同一个二维名义仪器现在具有

$$
\boxed{
\mathfrak r_{\mathrm{rec}}=0
<\mathfrak r_{\mathrm{cert}}=\frac12
<\frac45
<\mathfrak r_{\mathrm{fail}}
\le\sqrt{\frac{11+5\sqrt5}{32}}
<\mathfrak r_{\mathrm{diag}}=1.
}
$$

其中 $\mathfrak r_{\mathrm{cert}}$ 仍只指第 69 节指定的标量余量规则。真实最坏均值在每个严格小于 $\mathfrak r_{\mathrm{fail}}$ 的闭球上共同有限，在接近这一半径时至少按式 (80.4) 发散。

本批的关键连接是：一个固定态上的最优读数还必须来自同一个对全部输入合法的仪器。该相容性排除了旧下界的等号；紧性再把排除单点升级成共同间隔，并把这个间隔传给整个装置族的等待预算。

**来源与适用边界 81.2。** Kraus／Choi 表示、迹范数对偶与有限维范数连续性是标准工具，沿用第 7 节与第 73 节所引 Watrous《The Theory of Quantum Information》。其中定理 2.22、2.26 与推论 2.27 给完全正性、保迹及 Kraus／Choi／Stinespring 表征，[命题 2.28](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf#page=98)明确给有限维通道集的紧性与凸性；单调紧性复用第 40.2 条的 Dini 机制，未点击固定态提取复用第 71.2 条的 Cesàro 构造。本批新增纸面推导是它们在同一完整仪器约束下的结合、$4/5$ 等号的相干相容性排除，以及由最小失效仪器导出的实际成本下界。不主张文献原创性，不将既有工具重复命名为新理论。

这里没有得到全量子失效半径的精确值，也没有给出严格间隔的显式正数、端点共同预算的数值或成本发散的匹配上界。结论限定于固定有限完整记忆和齐次重复，不推广到任意切换控制；第 70 节的共同后继证书仍承担那一类问题。全部新增为理论正文，未新增或编译 Lean，未进入消化、覆盖或冻结链。

## 追加锚（本行以下为增补区）

## 82. 近似暗态可以在同一完整接口内修成精确暗态

本批接续第 78—81 节。先控制一次合法仪器修改所需的完整通道距离，再把它接到有限占据态，得到实际等待成本关于失效距离的定量上界。此前的严格半径分离、共同有限性与倒数下界均保留；这里仍不决定第 73 节显式失效仪器是否全局最优。

本节先允许任意非零有限维活动空间 $\mathcal H$。记录空间为两个正交标签“未点击、点击”，完整输出为 $\mathcal K=\mathbb C^2\otimes\mathcal H$。仪器 $\Gamma=(\mathcal N,\mathcal C)$ 完全正且完整保迹，输出已在记录基中分块。对指定单位向量 $\psi\in\mathcal H$，记

$$
P=|\psi\rangle\langle\psi|,\qquad
y=|\varnothing\rangle\otimes|\psi\rangle,
\qquad
\alpha=\langle y|\Gamma(P)|y\rangle
=\operatorname{Tr}[P\mathcal N(P)],
\qquad
\varepsilon=1-\alpha.
$$

$\varepsilon$ 同时计入点击概率及未点击后离开指定纯态的部分；它一般不等于单独的点击概率。

**定理 82.1（保留完整接口的纯暗态修复）。** 存在同输入、同记录及同量子输出空间的完整仪器 $\widetilde\Gamma=(\widetilde{\mathcal N},\widetilde{\mathcal C})$，满足

$$
\boxed{
\widetilde{\mathcal N}(P)=P,\qquad
\widetilde{\mathcal C}(P)=0,\qquad
\frac12\|\widetilde\Gamma-\Gamma\|_\diamond
\le\sqrt{\varepsilon}.
} \tag{82.1}
$$

这是一个通道存在与距离定理。它不宣称不知道 $\Gamma$ 或 $\psi$ 时，单靠一次读数即可实施修复。

证明。取有限 Stinespring 等距

$$
V:\mathcal H\longrightarrow\mathcal K\otimes\mathcal E,\qquad
\Gamma(X)=\operatorname{Tr}_{\mathcal E}(VXV^\dagger),
\qquad v=V\psi.
$$

标准等距表示见 Watrous《The Theory of Quantum Information》[推论 2.27](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf#page=97)。设

$$
\Pi_y=|y\rangle\langle y|\otimes I_{\mathcal E},
\qquad \|\Pi_yv\|^2=\alpha.
$$

若 $\alpha=1$，输出 $\Gamma(P)$ 已完全支撑于一维空间 $\mathbb Cy$，故等于 $|y\rangle\langle y|$，直接取 $\widetilde\Gamma=\Gamma$。

若 $0<\alpha<1$，令 $w=\Pi_yv/\sqrt\alpha$；若 $\alpha=0$，在 $\mathbb Cy\otimes\mathcal E$ 中任选单位向量 $w$。两种情形均有

$$
w=y\otimes e,\qquad
\langle v,w\rangle=\sqrt\alpha,
\qquad
\theta=\arccos\sqrt\alpha\in(0,\pi/2].
$$

在 $v,w$ 张成的复二维平面中，令

$$
u=\frac{w-\cos\theta\,v}{\sin\theta}.
$$

于是 $v,u$ 正交归一，且 $w=\cos\theta\,v+\sin\theta\,u$。定义酉算子 $U$：

$$
Uv=\cos\theta\,v+\sin\theta\,u,\qquad
Uu=-\sin\theta\,v+\cos\theta\,u,
$$

并在该平面的正交补上取恒等。它满足 $Uv=w$，以及整个联合空间上的算子不等式

$$
\frac{U+U^\dagger}{2}\ge\cos\theta\,I
=\sqrt\alpha\,I. \tag{82.2}
$$

令 $V'=UV$，并先构造通道 $\Xi(X)=\operatorname{Tr}_{\mathcal E}(V'XV'^\dagger)$。它在输入 $P$ 上输出 $|y\rangle\langle y|$，但对其他输入未必已经在记录基中分块。以 $\mathcal P$ 表示实际记录空间上的去相干通道，置

$$
\widetilde\Gamma=\mathcal P\circ\Xi.
$$

这样所得通道重新具有两个 CP 记录分支，且 $P$ 的目标输出不变。因为 $\Gamma$ 原先已经是记录分块通道，$\mathcal P\circ\Gamma=\Gamma$。

下面控制包含任意有限参考系统的完整距离。对任意纯联合输入 $\zeta\in\mathcal R\otimes\mathcal H$，设 $z=(I_{\mathcal R}\otimes V)\zeta$。式 (82.2) 给

$$
\operatorname{Re}\langle z|(I_{\mathcal R}\otimes U)z\rangle
\ge\sqrt\alpha.
$$

两个归一化纯态的半迹距离因而满足

$$
\begin{aligned}
D\!\left(
|z\rangle\langle z|,
(I_{\mathcal R}\otimes U)|z\rangle\langle z|
(I_{\mathcal R}\otimes U^\dagger)
\right)
&=\sqrt{1-\left|\langle z|(I_{\mathcal R}\otimes U)z\rangle\right|^2}\\
&\le\sqrt{1-\alpha}.
\end{aligned}
$$

偏迹及记录去相干都是 CPTP 映射，不增加此距离。混合联合输入由凸性包含；通道差的纯联合输入表征见第 73 节所引 Watrous 定理 3.51。因此得到式 (82.1) 的完整 half-diamond 界。$\square$

证明中的环境是同一次调用的等距表示，并非新增的持久活动记忆。按同一个修复仪器逐轮重复时，从 $P$ 出发每轮仍为 $P$ 且始终未点击；不需要把环境指标变成观察者记录。

**推论 82.2（可校准模型中的纯态返回缺陷下界）。** 回到第 78 节的二维名义仪器 $\Gamma_0$，记其真实失效半径为 $R=\mathfrak r_{\mathrm{fail}}$。若 $\delta(\Gamma)\le u<R$，则对每个纯态 $P$，

$$
\boxed{
1-\operatorname{Tr}[P\mathcal N_\Gamma(P)]
\ge(R-u)^2.
} \tag{82.3}
$$

证明。定理 82.1 给一个同接口失效仪器 $\widetilde\Gamma$，其与 $\Gamma$ 的距离至多为返回缺陷的平方根。由失效半径定义及三角不等式，

$$
R\le\delta(\widetilde\Gamma)
\le u+\sqrt{1-\operatorname{Tr}[P\mathcal N_\Gamma(P)]}.
$$

因为 $R-u>0$，移项并平方即得。$\square$

## 83. 有限占据态把修复距离变成二次成本上界

本节固定第 78 节的完整二维接口、同一个名义仪器 $\Gamma_0$，以及第 80.1 条的 $\mathscr K(u)$。各实际装置在所有未点击轮次重复自身同一仪器；仍把永不点击轨迹的实际调用成本取为无穷。

**定理 83.1（由真实失效间隔控制全校准球成本）。** 设 $R=\mathfrak r_{\mathrm{fail}}$。对每个 $0\le u<R$，令 $\Delta=R-u>0$。则

$$
\boxed{
\frac{R}{R-u}
\le\mathscr K(u)
\le
\frac{1+2(R-u)^2}{(1-u)(R-u)^2}.
} \tag{83.1}
$$

特别地，接近真实失效半径时，已知的成本下界为倒数阶、上界至多为二次倒数阶；本条不认定其中任一指数就是精确发散阶。

证明。左侧是第 80.4 条。对右侧，任取 $\Gamma\in\mathfrak B_u$、初态 $\rho$ 与有限 $n\ge1$。定义

$$
\rho_j=\mathcal N^j(\rho),\qquad
s_j=\operatorname{Tr}\rho_j,\qquad
\mu_n=\sum_{j=0}^{n-1}s_j
=\mathbb E_\rho^\Gamma\min(\mathsf N,n),
\qquad
\sigma_n=\frac1{\mu_n}\sum_{j=0}^{n-1}\rho_j.
$$

无须假定最终点击或完整均值有限，就有 $1\le\mu_n\le n$，且 $\sigma_n$ 是密度矩阵。第 76.1 条的望远镜等式给

$$
\mathcal N(\sigma_n)-\sigma_n
=\frac{\rho_n-\rho}{\mu_n},\qquad
q_n:=\operatorname{Tr}\mathcal C(\sigma_n)
=\frac{1-s_n}{\mu_n}\le\frac1{\mu_n}. \tag{83.2}
$$

置 $E=\mathcal C^*(I)$。名义仪器对 $P_0$ 必点击，所以完整校准保证

$$
\operatorname{Tr}E\ge\langle0|E|0\rangle\ge1-u. \tag{83.3}
$$

在二维空间写

$$
\sigma_n=(1-t)P+tP^\perp,\qquad
0\le t\le\frac12,
$$

其中 $P$ 是最大本征值对应的秩一投影；当 $\sigma_n=I/2$ 时任选一个这样的投影。由 $\sigma_n\ge tI$、式 (83.2)—(83.3)，

$$
t(1-u)\le t\operatorname{Tr}E
\le q_n\le\frac1{\mu_n}. \tag{83.4}
$$

记

$$
\varepsilon=1-\operatorname{Tr}[P\mathcal N(P)],\qquad
\beta=\operatorname{Tr}[P\mathcal N(P^\perp)],
\qquad
e_P=\operatorname{Tr}(EP),\quad
e_\perp=\operatorname{Tr}(EP^\perp).
$$

因为 $0\le P\le I$，未点击分支迹不增且与点击分支完整互补，故

$$
e_P\le\varepsilon,\qquad
\beta\le1-e_\perp
\le u+e_P\le u+\varepsilon. \tag{83.5}
$$

其中中间一步使用 $e_P+e_\perp=\operatorname{Tr}E\ge1-u$。另一方面，在式 (83.2) 的第一个等式上检验 $P$，得到

$$
-(1-t)\varepsilon+t\beta
=\frac{\operatorname{Tr}(P\rho_n)-\operatorname{Tr}(P\rho)}{\mu_n}
\ge-\frac1{\mu_n}.
$$

结合式 (83.5)，即

$$
(1-2t)\varepsilon\le tu+\frac1{\mu_n}. \tag{83.6}
$$

推论 82.2 对这个依赖于 $n,\Gamma,\rho$ 的纯态 $P$ 同样成立，给 $\varepsilon\ge\Delta^2$。由于 $1-2t\ge0$，式 (83.6) 于是推出

$$
\begin{aligned}
\Delta^2
&\le t(u+2\Delta^2)+\frac1{\mu_n}\\
&\le\frac{u+2\Delta^2}{(1-u)\mu_n}
+\frac1{\mu_n}\\
&=\frac{1+2\Delta^2}{(1-u)\mu_n}.
\end{aligned}
$$

这里 $1-u>0$，因为第 79.2 条已给 $u<R\le c_*<1$。得到对全部有限 $\mu_n$ 同时成立的上界。最后用单调收敛得到完整均值上界，再对同一个校准球的装置及来源取上确界。整个证明没有预先调用一个可能发散的无限预解算子。$\square$

**推论 83.2（用已证明的失效下界生成预算）。** 若掌握一个正数 $R_0\le R$，则对 $0\le u<R_0$，

$$
\boxed{
\mathscr K(u)\le
\frac{1+2(R_0-u)^2}{(1-u)(R_0-u)^2}.
} \tag{83.7}
$$

证明。函数 $x\mapsto2+x^{-2}$ 在 $x>0$ 上递减，而 $R-u\ge R_0-u>0$，代入式 (83.1)。$\square$

因此定量使用这个结果需要真实失效半径的下界。不能把第 73 节的候选上界 $c_*$ 当成 $R_0$；那会把成本上界的方向用反。对 $u<4/5$，还可以与第 76.2、76.3 条已有上界取最小值，因为它们同时约束同一批装置与来源。

**推论 83.3（端点成本由严格间隔定量控制）。** 写 $g=R-4/5>0$，则

$$
\boxed{\mathscr K(4/5)\le10+\frac5{g^2}.} \tag{83.8}
$$

证明。在式 (83.1) 取 $u=4/5$、$\Delta=g$。$\square$

这个公式给出了端点预算与严格间隔的明确关系。本式本身未给出 $g$ 的数值下界；第 85 节将补上一个可用的有理下界。

## 84. 修好指定纯态，与找到最近失效仪器，是不同优化

定理 82.1 的平方根来自同一个耦合对全部输入的作用。下面用一族原先都会终止的仪器，检验这个平方根能否统一改成线性，同时说明这不决定第 83 节成本发散的精确指数。

**定义 84.1（指定暗态修复距离与自由失效距离）。** 固定纯态 $P$。在同一完整接口上定义

$$
d_P(\Gamma)=
\inf_{\widetilde\Gamma:\,\widetilde{\mathcal N}(P)=P}
\frac12\|\widetilde\Gamma-\Gamma\|_\diamond,
\qquad
d_{\mathrm{fail}}(\Gamma)=
\inf_{\widetilde\Gamma\in\mathfrak F}
\frac12\|\widetilde\Gamma-\Gamma\|_\diamond.
$$

前者要求把指定 $P$ 变成暗态；后者允许任何来源产生永久未点击。故总有 $d_{\mathrm{fail}}(\Gamma)\le d_P(\Gamma)$。本节的 $\Gamma$ 随参数变化，$d_{\mathrm{fail}}(\Gamma)$ 不等同于固定 $\Gamma_0$ 的半径 $R$。

**定理 84.2（在原先会终止的仪器上，指定修复仍需要平方根尺度）。** 对 $0<\theta<1/2$，置 $\kappa=\theta^4$，

$$
U_\theta=
\begin{pmatrix}
\cos\theta&-\sin\theta\\
\sin\theta&\cos\theta
\end{pmatrix},\qquad
Q_\theta=\sqrt{1-\kappa}\,U_\theta,\qquad
L_\theta=\sqrt\kappa\,I,
$$

并以它们定义两个记录分支的完整仪器 $\Gamma_\theta$。令 $P=P_0$ 以及

$$
\varepsilon_\theta
=1-\operatorname{Tr}[P_0\mathcal N_\theta(P_0)]
=\kappa+(1-\kappa)\sin^2\theta.
$$

则每个初态的首次点击时间都是成功参数为 $\kappa$ 的几何分布，均值为 $1/\kappa$，而

$$
\boxed{
\frac{\sqrt{\kappa^2+4(1-\kappa)\sin^2\theta}+\kappa}{2}
\le d_{P_0}(\Gamma_\theta)
\le\sqrt{\varepsilon_\theta}.
} \tag{84.1}
$$

因此

$$
\boxed{
\lim_{\theta\downarrow0}
\frac{d_{P_0}(\Gamma_\theta)}{\sqrt{\varepsilon_\theta}}=1.
} \tag{84.2}
$$

证明。完整性由 $Q_\theta^\dagger Q_\theta+L_\theta^\dagger L_\theta=I$ 成立。未点击映射每次将迹乘以 $1-\kappa$，所以全部来源具有上述几何等待律。

任一把 $P_0$ 修成纯暗态的完整仪器，在该输入上的输出必为未点击块中的 $P_0$，点击块为零。原仪器对应输出则为未点击块 $(1-\kappa)P_{\theta}$ 与点击块 $\kappa P_0$，其中 $P_{\theta}=U_\theta P_0U_\theta^\dagger$。两完整输出的半迹距离为

$$
\frac12\left(\|P_0-(1-\kappa)P_\theta\|_1+\kappa\right)
=
\frac{\sqrt{\kappa^2+4(1-\kappa)\sin^2\theta}+\kappa}{2}.
$$

这里使用第 73.1 式的两个未归一化纯态之差公式。单个输入上的距离是完整 diamond 距离的下界，得到式 (84.1) 左侧；右侧为定理 82.1。

当 $\theta\downarrow0$，有 $\kappa=\theta^4$、$\sin\theta\sim\theta$。式 (84.1) 两端均与 $\theta$ 渐近等价，且 $\sqrt{\varepsilon_\theta}\sim\theta$，夹逼得到式 (84.2)。$\square$

所以即使限定为原先会终止的仪器，也不存在常数 $C<\infty$ 与指数 $p>1/2$，使所有这类指定修复都满足 $d_P(\Gamma)\le C\varepsilon^p$。特别地，统一线性缺陷界不成立。

**命题 84.3（同一族的自由失效距离却恰为点击率）。** 对上述同一仪器族，

$$
\boxed{
d_{\mathrm{fail}}(\Gamma_\theta)=\kappa=\theta^4,
\qquad
\frac{d_{\mathrm{fail}}(\Gamma_\theta)}
{d_{P_0}(\Gamma_\theta)}
\longrightarrow0.
} \tag{84.3}
$$

证明。将点击分支置零，把未点击分支改为 $\rho\mapsto U_\theta\rho U_\theta^\dagger$，得到一个同接口的恒不点击仪器。对任意带参考的输入，两个记录块的差分别为迹范数 $\kappa$ 的负、正算子，所以完整半 diamond 距离恰为 $\kappa$，给上界。

反向，任一同接口失效仪器都由第 79.1 条的固定态判据给出未点击固定密度矩阵 $\sigma$。它在该输入上的点击概率为零，而 $\Gamma_\theta$ 对任何输入的点击概率均为 $\kappa$。读取点击标签便有概率差 $\kappa$，所以完整距离至少为 $\kappa$。第一式成立，第二式结合定理 84.2 即得。$\square$

因此，指定纯态修复的平方根尺度已经达到最优，也不能据此宣布第 83.1 条的二次成本上界达到最优。两者优化的是不同对象：修好一个预先指定的关系，与寻找所有可能失效关系中最近的一份。

## 85. 一个显式有理间隔使旧端点具有数值预算

第 78 节在单个暗态上饱和检验时排除了距离 $4/5$。现在保留同一个检验的非对角项，并给出有限误差余量，从而把严格间隔变成明确的有理数下界。本节始终使用第 78 节的同一二维完整仪器类。

**引理 85.1（纯暗态失效必须满足的二阶余量）。** 设实际失效仪器的完整距离为 $\delta<1$，取其纯未点击固定态 $P_\psi$，并如第 78 节消去计算基相位。记

$$
a=|\langle0|\psi\rangle|^2,\quad b=1-a,\quad
r=\sqrt{ab},\quad
s=\sqrt{a^2+4b^2},\quad
f(a)=\frac{a+s}{2}.
$$

此时 $0<a<1$、$\delta\ge a$、$\delta\ge f(a)$，并且

$$
\boxed{
\frac{ab}{4s^2}
\left[3a-2+s-2\sqrt{b(\delta-a)}\right]_+^2
\le2\delta\bigl(\delta-f(a)\bigr).
} \tag{85.1}
$$

证明。第 71.2 条的固定态构造及秩分类保证 $\delta<1$ 的失效必有纯固定态。若 $a=0$ 或 $a=1$，同条下界给 $f(a)=1$，故不可能。第 78.1 条给

$$
\mathcal N(|\psi\rangle\langle\eta|)
=d|\psi\rangle\langle\eta|,
\qquad
|d|^2\le\frac{\delta-a}{b},
$$

其中 $\eta=-\sqrt b\,|0\rangle+\sqrt a\,|1\rangle$；右侧非负也给 $\delta\ge a$。

现在置

$$
D=P_\psi-bP_0,\qquad
S=\operatorname{sign}D=\frac{2D-aI}{s},
\qquad
Z=\operatorname{diag}_{\mathrm{record}}(S,-I),
\qquad
M=\frac12(\Gamma^*-\Gamma_0^*)(Z).
$$

仍有 $-\delta I\le M\le\delta I$，且

$$
\langle\psi|M|\psi\rangle=f(a),\qquad
\langle\eta|M|\psi\rangle
=\frac{r}{2s}\bigl(2bd-3a+2-s\bigr). \tag{85.2}
$$

为核对第二式，直接使用

$$
\langle\eta|S|\psi\rangle=\frac{2br}{s},\qquad
\langle0|S|0\rangle=\frac{3a-2}{s},
$$

以及 $\mathcal N_0(|\psi\rangle\langle\eta|)=rP_0$、
$\mathcal C_0(|\psi\rangle\langle\eta|)=-rP_0$ 即得。由 $\operatorname{Re}d\le|d|\le\sqrt{(\delta-a)/b}$，若方括号中的实数为正，则

$$
|\langle\eta|M|\psi\rangle|
\ge\frac r{2s}
\left(3a-2+s-2\sqrt{b(\delta-a)}\right).
$$

若该实数非正，使用零下界。因此左侧平方至少为式 (85.1) 左端。

另一方面，正算子 $\delta I-M$ 的二维主子式非负，所以

$$
\begin{aligned}
|\langle\eta|M|\psi\rangle|^2
&\le(\delta-f(a))
\bigl(\delta-\langle\eta|M|\eta\rangle\bigr)\\
&\le2\delta(\delta-f(a)).
\end{aligned}
$$

两式合并。$\square$

**定理 85.2（实际失效半径的显式严格改进）。** 对同一个名义仪器，

$$
\boxed{
R=\mathfrak r_{\mathrm{fail}}>
\frac{1601}{2000}
=\frac45+\frac1{2000}.
} \tag{85.3}
$$

证明。置 $\delta_0=1601/2000$，假设存在实际失效仪器满足 $\delta\le\delta_0$。其纯固定态参数满足 $f(a)\le\delta_0$，且恒等式

$$
f(a)-\frac45
=\frac{2(a-3/5)^2}{s+8/5-a} \tag{85.4}
$$

成立。先在 $0\le a\le1$ 上使用 $s\le2$，得到分母至多 $18/5$，从而 $|a-3/5|\le3/100$。因此 $57/100\le a\le63/100$。

在这一区间，$s^2=5a^2-8a+4$ 递减，故 $s<26/25$。再次使用式 (85.4)，

$$
\left(a-\frac35\right)^2
<\frac{207}{400000}
<\left(\frac{23}{1000}\right)^2.
$$

于是

$$
\frac{577}{1000}<a<\frac{623}{1000},\qquad
r>\frac{12}{25},\qquad
\frac{97}{100}<s<\frac{103}{100}. \tag{85.5}
$$

后面三个有理估计可分别检验 $a(1-a)$ 与 $5a^2-8a+4$ 的端点值；两者在这个位于 $a>1/2$、$a<4/5$ 的区间上递减。

定义

$$
B_0(a)=3a-2+s-2\sqrt{(1-a)(\delta_0-a)}.
$$

在式 (85.5) 区间内，根号严格为正，且

$$
B_0'(a)
=3+\frac{5a-4}{s}
+\frac{1+\delta_0-2a}{\sqrt{(1-a)(\delta_0-a)}}
>\frac95.
$$

确实，最后一项为正；用式 (85.5) 可得 $(5a-4)/s>-6/5$。故 $B_0$ 递增。在下端点处，

$$
s\!\left(\frac{577}{1000}\right)>\frac{128}{125},
\qquad
\sqrt{\left(1-\frac{577}{1000}\right)
\left(\delta_0-\frac{577}{1000}\right)}
<\frac{77}{250}.
$$

所以

$$
B_0(a)>
-\frac{269}{1000}
+\frac{1024}{1000}
-\frac{616}{1000}
=\frac{139}{1000}.
$$

因为 $\delta\le\delta_0$，以 $\delta$ 代替 $\delta_0$ 只会使这个方括号增大。因此式 (85.2) 的非对角项满足

$$
|\langle\eta|M|\psi\rangle|
>\frac{24}{103}\frac{139}{1000}
>\frac3{100}. \tag{85.6}
$$

但同一正算子主子式又给

$$
|\langle\eta|M|\psi\rangle|^2
\le2\delta_0\left(\delta_0-\frac45\right)
=\frac{1601}{2000000}
<\frac9{10000},
$$

与式 (85.6) 矛盾。因此没有距离至多 $\delta_0$ 的失效仪器。第 79.1 条已经证明最小失效距离取得，故其最小值也严格大于 $\delta_0$，得到结论。$\square$

**推论 85.3（旧端点的明确全状态调用预算）。** 对每个完整距离至多 $4/5$ 的同接口齐次仪器，以及每个初态，

$$
\boxed{
\mathbb E_\rho^\Gamma\mathsf N
\le\mathscr K(4/5)
<20\,000\,010.
} \tag{85.7}
$$

更一般地，对所有 $0\le u<1601/2000$，可以在式 (83.7) 中使用 $R_0=1601/2000$，得到只含已给定数值的统一预算。

证明。由定理 85.2，式 (83.8) 中 $g>1/2000$。于是

$$
\mathscr K(4/5)
\le10+\frac5{g^2}
<10+5\cdot2000^2.
$$

一般结论直接由推论 83.2。$\square$

这个上界非常保守，只保证所声明的实际调用轮数有限，不声称接近最优，也不把调用数换成未经标定的物理秒。在更外侧的端点 $u=1601/2000$，第 80.2 条仍给共同有限成本，但这里使用的数值公式尚未给该新端点的有限数值；不能把它的分母置零后仍当成预算。

## 86. 从接近暗态到等待成本的定量关系

**结论 86.1（修复、间隔与成本的同一推导链）。** 对固定二维名义仪器，第 82—83 节建立

$$
\boxed{
\text{某纯态返回缺陷很小}
\ \Longrightarrow\
\text{附近存在同接口精确暗态仪器}
\ \Longrightarrow\
\text{距失效仍有正间隔时，占据成本不能任意大}.
}
$$

其中第一步允许任意有限活动维数，最后的具体成本常数使用二维占据态的谱分解、名义点击校准与齐次重复。不能删除这些条件再引用式 (83.1)。

**来源与边界 86.2。** Stinespring 等距、纯态迹距离公式、CPTP 收缩性及纯联合输入的 diamond 表征是成熟工具，沿用 Watrous 定理 2.22、推论 2.27 与定理 3.51 的上述定位。本批把一个指定输入的目标输出通过联合空间的平面旋转精确实现，再对所有参考输入统一控制；有限占据态来自第 76 节，真实失效半径与成本下界来自第 79—80 节。新增内容是这些关系之间的纸面构造、定量估计与同族区分例，不主张文献原创性。

当前已经有成本发散的倒数下界和二次倒数上界，尚未证明其精确指数；第 84 节的最优平方根也不补上这一缺口。第 85 节已经给出 $g>1/2000$ 及旧端点的明确有限预算；真实失效半径的精确值与最坏成本的精确发散阶仍未取得。全部新增仍为纯理论 Markdown，未新增或编译 Lean，未进入消化、覆盖或冻结链。

## 追加锚（本行以下为增补区）

## 87. 完整失效半径具有有限代数定义

**定义 87.1（同一二维仪器的实坐标）。** 本节及后续三节继续固定

$$
Q_0=|0\rangle\langle1|,\qquad
L_0=|0\rangle\langle0|,\qquad
\Gamma_0=(\mathcal N_0,\mathcal C_0).
$$

活动记忆为 $\mathcal H=\mathbb C^2$，结果记录为未点击与点击两个正交标签；每个结果都保留同一个二维量子后继。完整仪器写成通道

$$
\Gamma(X)=|\varnothing\rangle\langle\varnothing|\otimes\mathcal N(X)
+|\bullet\rangle\langle\bullet|\otimes\mathcal C(X).
$$

沿用第 79—83 节的

$$
\delta(\Gamma)=\frac12\|\Gamma-\Gamma_0\|_\diamond,
\quad R=\mathfrak r_{\mathrm{fail}},
\quad\mathfrak B_u=\{\Gamma:\delta(\Gamma)\le u\},
\quad\mathscr K(u)=\sup_{\Gamma\in\mathfrak B_u,\rho}
\mathbb E_\rho^\Gamma\mathsf N.
$$

每次执行始终重复自己同一个仪器。$\mathsf N$ 包括首次点击那一轮；永久未点击的成本为无穷。

用两个 $4\times4$ Hermitian Choi 矩阵 $J_{\varnothing},J_\bullet$ 表示仪器，并将矩阵元实部、虚部分别作为实坐标。合法性条件准确为

$$
J_{\varnothing}\succeq0,\qquad J_\bullet\succeq0,
\qquad \operatorname{Tr}_{\rm out}(J_{\varnothing}+J_\bullet)=I_2.
\tag{87.1}
$$

记这些条件为 $\mathsf I(\Gamma)$。它们不固定 Kraus 秩，不删除秩退化装置。这里沿用标准 Choi 完全正性与保迹表征；参见第 73、81 节所引 Watrous 定理 2.22、2.26。

**定理 87.2（全参考校准与永久失效的有理半代数关系）。** 在定义 87.1 的同一接口中，下列两个集合都有有限有理系数实多项式等式、不等式的无量词定义：

$$
\{(\Gamma,u):\mathsf I(\Gamma),\ u\ge0,\ \delta(\Gamma)\le u\},
\qquad \mathfrak F.
\tag{87.2}
$$

其中 $\mathfrak F$ 是存在某初态永久未点击概率为正的仪器集。因此，准确失效半径 $R$ 是实代数数，而且

$$
\frac{1601}{2000}<R\le\sqrt{\frac{11+5\sqrt5}{32}}.
\tag{87.3}
$$

证明。固定大小的 Hermitian 矩阵正半定，当且仅当其所有主子式非负。拆开复坐标后，式（87.1）因而是有限有理多项式条件。

先准确表示完整校准球。取参考空间 $\mathcal R=\mathbb C^2$ 及单位向量 $z\in\mathcal R\otimes\mathcal H$，令

$$
D_\Gamma(z)=
[\operatorname{id}_{\mathcal R}\otimes(\Gamma-\Gamma_0)](|z\rangle\langle z|).
$$

它是 $8\times8$ Hermitian 矩阵，其矩阵元是仪器实坐标与 $z$ 实坐标的有理多项式。对 Hermitian $D$，

$$
\|D\|_1\le2u
\iff
\exists Y\succeq0:\quad Y^2=D^2,\quad\operatorname{Tr}Y\le2u.
\tag{87.4}
$$

原因是 $D^2$ 的正半定平方根唯一，右侧强制 $Y=|D|$。这在零本征值与秩变化处仍成立。

Hermitian 保持映射的 diamond 范数可在与输入同维的参考及纯联合输入上取得；使用 Watrous 定理 3.51、式（3.291）。因此完整距离条件准确等价于有限实量词公式

$$
\mathsf B(\Gamma,u):\quad
\mathsf I(\Gamma),\ u\ge0,\quad
\forall z\ \bigl[
\|z\|^2=1\Longrightarrow
\exists Y\succeq0:
Y^2=D_\Gamma(z)^2,\ \operatorname{Tr}Y\le2u
\bigr].
\tag{87.5}
$$

参考输入的全称量词仍在，点击与未点击的量子后继也都在 $D_\Gamma(z)$ 中；这里没有用单轮标签距离替换完整距离。

其次，由引理 79.1 的固定态判据，永久失效准确等价于

$$
\mathsf F(\Gamma):\quad
\mathsf I(\Gamma),\quad
\exists\sigma\succeq0:
\operatorname{Tr}\sigma=1,\quad\mathcal N_\Gamma(\sigma)=\sigma.
\tag{87.6}
$$

这也是有限有理多项式量词公式；最后的等式对仪器坐标和 $\sigma$ 坐标为双线性。使用实闭域量词消去的标准定理，式（87.5）—（87.6）可消去量词，且保持有理定义域。[^wave_real_closed_elimination]

令 $\mathsf H(u)$ 表示 $u\ge0$ 且存在满足 $\mathsf F(\Gamma)$ 与 $\mathsf B(\Gamma,u)$ 的仪器。引理 79.1 的最小值取得性使 $R$ 成为下列公式唯一选出的实数：

$$
\mathsf H(R)\quad\wedge\quad
\neg\exists v\,[0\le v<R\ \wedge\ \mathsf H(v)].
\tag{87.7}
$$

所以单点 $\{R\}$ 有有理半代数定义。无量词定义只使用有限个非零有理多项式；若 $R$ 不是其中任何一个的根，则全部符号在其一个邻域内不变，无法只选出单点。因此 $R$ 是实代数数。式（87.3）复用定理 85.2 与第 73.2 条。$\square$

本证明复用《动态充分边界与内部观察者》卷第 76 节的有限优化量词化思路，以及《相位边界》卷第 142 节的迹范数图表示；新的对象是保留全部参考与量子后继的永久失效集合。它没有计算 $R$ 的最小多项式，也没有将代数性解释为低成本计算。

## 88. 无限等待的最坏值由同一有限算子方程取得

**定理 88.1（最坏成本的取得、连续性与代数图）。** 对每个 $0\le u<R$，存在同一个实际仪器 $\Gamma_u\in\mathfrak B_u$ 与纯初态 $P_u$，使

$$
\mathscr K(u)=\mathbb E_{P_u}^{\Gamma_u}\mathsf N<\infty.
\tag{88.1}
$$

函数 $\mathscr K:[0,R)\to\mathbb R$ 连续、非减，其图为有理半代数集。每个实代数参数 $u\in[0,R)$ 都给实代数数 $\mathscr K(u)$。

证明。令 $\mathcal A_\Gamma=\mathcal N_\Gamma^*$。对无永久失效的固定仪器，第 66、71 节给出唯一有限成本势

$$
T_\Gamma=\sum_{n\ge0}\mathcal A_\Gamma^n(I),
\qquad T_\Gamma\succeq0,\qquad
T_\Gamma-\mathcal A_\Gamma(T_\Gamma)=I.
\tag{88.2}
$$

反过来，有限 Hermitian 矩阵 $T\succeq0$ 满足最后一个方程时，正性给 $T\succeq I$。令 $M=\|T\|_\infty\ge1$，则

$$
0\preceq\mathcal A_\Gamma(T)=T-I
\preceq(1-M^{-1})T.
$$

反复作用正映射，得到

$$
0\preceq\mathcal A_\Gamma^n(I)
\preceq\mathcal A_\Gamma^n(T)
\preceq(1-M^{-1})^nT\qquad(n\ge1).
\tag{88.3}
$$

若 $M=1$，右侧对 $n\ge1$ 为零。有限和望远镜恒等式

$$
T=\sum_{j=0}^{n-1}\mathcal A_\Gamma^j(I)
+\mathcal A_\Gamma^n(T)
$$

因此收敛到式（88.2），同时保证所有初态终止与均值有限。任意 Hermitian 固定差 $X=\mathcal A_\Gamma(X)$ 满足
$-\|X\|_\infty I\preceq X\preceq\|X\|_\infty I$；迭代并用式（88.3）可知 $X=0$，故该正解唯一。这个双向论证使有限方程承载实际无限尾和，而不只是一个成本上界证书。

对每个固定 $v<R$，定理 80.2 给 $\mathfrak B_v$ 上共同的指数尾。因此式（88.2）的连续有限部分和在整个 $\mathfrak B_v$ 上一致收敛，$\Gamma\mapsto T_\Gamma$ 与

$$
M(\Gamma)=\lambda_{\max}(T_\Gamma)
=\max_\rho\operatorname{Tr}(\rho T_\Gamma)
$$

都连续。紧性使 $M$ 在 $\mathfrak B_u$ 上取得最大值；取最大本征值的一个纯本征态即得式（88.1）。

接着核对参数连续性。非减性来自校准球嵌套。若 $u_j\to u<R$，取 $v<R$ 使充分大的 $j$ 都有 $u_j\le v$。相应最优仪器的收敛子列及 $\delta$ 的连续性给
$\limsup_j\mathscr K(u_j)\le\mathscr K(u)$。若 $u>0$，取 $\Gamma_u$，并令

$$
t_j=\min\{1,u_j/u\},\qquad
\widehat\Gamma_j=t_j\Gamma_u+(1-t_j)\Gamma_0.
$$

逐分支凸混合仍是同接口合法仪器，且
$\delta(\widehat\Gamma_j)=t_j\delta(\Gamma_u)\le u_j$。
又 $\widehat\Gamma_j\to\Gamma_u$，所以
$\liminf_j\mathscr K(u_j)\ge M(\Gamma_u)=\mathscr K(u)$。
$u=0$ 时使用球嵌套即可得到同一下半连续性。故 $\mathscr K$ 连续。

最后写出准确有限图关系。对实数 $m$，记

$$
\mathsf W(\Gamma,T,m):\quad
T=T^\dagger\succeq0,\quad
T-\mathcal A_\Gamma(T)=I,\quad
mI-T\succeq0,\quad\det(mI-T)=0.
\tag{88.4}
$$

正性和行列式条件准确给 $m=\lambda_{\max}(T)$。取迹对偶只使 $\mathcal A_\Gamma(T)$ 的坐标成为仪器坐标与 $T$ 坐标的双线性式；所以 $\mathsf W$ 是有理多项式条件。对 $0\le u<R$，$k=\mathscr K(u)$ 等价于

$$
\begin{aligned}
&\exists\Gamma,T:\quad
\mathsf B(\Gamma,u)\ \wedge\ \mathsf W(\Gamma,T,k),\\
&\forall\Gamma',T',m:\quad
[\mathsf B(\Gamma',u)\ \wedge\ \mathsf W(\Gamma',T',m)]
\Longrightarrow m\le k.
\end{aligned}
\tag{88.5}
$$

存在量词合法使用了已证明的最大值取得性。$R$ 可用式（87.7）消去；对余下有限实量词应用同一量词消去定理，就得到有理半代数图。固定代数 $u$ 时，用其有理最小多项式和隔离区间指定该参数，再沿用定理 87.2 的单点论证，得到 $\mathscr K(u)$ 为实代数数。$\square$

## 89. 真实等待成本具有有理幂发散主项

**定理 89.1（发散阶存在并夹在一与二之间）。** 对定义 87.1 的固定模型，存在实代数数 $c>0$、有理数 $p\in[1,2]$、整数 $m\ge1$，使

$$
\boxed{
\mathscr K(R-h)
=c\,h^{-p}\bigl(1+O(h^{1/m})\bigr)
\qquad(h\downarrow0).
}
\tag{89.1}
$$

因此其首项是单一的正系数有理幂。定理不确定 $p$ 是否为端点值，也不确定 $c$ 的数值。

证明。在一个小正区间上定义

$$
g(h)=\frac1{\mathscr K(R-h)},\qquad g(0)=0.
$$

定理 88.1 的连续性与定理 80.4 的发散给 $g$ 连续、$g(h)>0$，且 $g(h)\to0$。它的图定义在实代数数域
$\mathbb A=\overline{\mathbb Q}\cap\mathbb R$ 上。

取一个正有理 $h_0<R$。闭图

$$
G=\{(h,g(h)):0\le h\le h_0\}
$$

是紧的一维半代数集，因而半解析。在原点删去该点后，充分短的图段连通，并构成穿孔邻域基。这核对了 Bierstone–Milman Lemma 6.3(1) 的条件：存在穿过原点、在零点两侧实解析的弧

$$
t\longmapsto(a(t),b(t)),
$$

其正参数小段覆盖原点附近的正向图段。[^wave_endpoint_arc] 两坐标对小 $t>0$ 都为正且不是零函数，因此

$$
a(t)=A t^m(1+O(t)),\qquad
b(t)=B t^n(1+O(t)),\qquad A,B>0,\quad m,n\ge1.
\tag{89.2}
$$

这里 $a'(t)>0$ 对充分小的 $t>0$ 成立，故它覆盖全部充分小的 $h>0$。由 $h=a(t)$ 得

$$
t=(h/A)^{1/m}(1+O(h^{1/m})),
$$

代入第二坐标，得到

$$
g(h)=B A^{-n/m}h^{n/m}(1+O(h^{1/m})).
$$

取 $p=n/m$ 并求倒数，即得式（89.1），暂时只有 $c=A^{n/m}/B>0$。这一步并未假定解析弧首系数 $A,B$ 是代数数。

为证明 $c$ 的代数性，写 $p=r/s$，其中 $r,s$ 为正整数。正值关系 $z=h^p$ 可由 $z>0$、$z^s=h^r$ 表示，所以

$$
q(h)=h^p\mathscr K(R-h)
$$

的图仍定义在 $\mathbb A$ 上。已证明 $q(h)\to c$，故其图的闭包与直线 $h=0$ 的交集恰为单点 $(0,c)$。闭包可由有限实量词表达，例如每个正半径的开球都与原图相交；量词消去保持定义域。于是 $\{c\}$ 是 $\mathbb A$ 上半代数单点，单点论证给 $c$ 在 $\mathbb A$ 上代数，因而本身属于 $\mathbb A$。

最后使用同一模型中已经证明的两侧成本界：

$$
\frac Rh\le\mathscr K(R-h)
\le\frac{1+2h^2}{(1-R+h)h^2}.
\tag{89.3}
$$

左式来自定理 80.4，右式来自定理 83.1；$R<1$ 保证右式首系数有限。若 $p<1$，则 $h\mathscr K(R-h)\to0$，与左式矛盾；若 $p>2$，则 $h^2\mathscr K(R-h)\to\infty$，与右式矛盾。因此 $1\le p\le2$。$\square$

本证明复用《相位边界》卷第 144 节的解析弧方法，但先由第 88 节证明了当前无限等待最坏值的有限代数图。前一卷的有限终端误差幂律不能直接替代这里的均值与全装置优化证明。

**推论 89.2（倍率尺度律与两个端点系数条件）。** 对每个固定 $\lambda>0$，有

$$
\lim_{h\downarrow0}
\frac{\mathscr K(R-\lambda h)}{\mathscr K(R-h)}
=\lambda^{-p},\qquad
\lim_{h\downarrow0}
\frac{\log\mathscr K(R-h)}{\log(1/h)}=p.
\tag{89.4}
$$

若 $p=1$，则 $c\ge R$；若 $p=2$，则 $c\le(1-R)^{-1}$。

证明。两个极限直接代入式（89.1）；足够小的 $h$ 使 $R-\lambda h\ge0$。两个端点系数条件分别将式（89.3）乘 $h$ 或 $h^2$ 后取极限得到。$\square$

## 90. 代数最坏实现与仍未计算的临界参数

**定理 90.1（同一实际实现可取代数坐标）。** 最短失效距离 $R$ 可由 Choi 矩阵元实部、虚部均为实代数数的仪器 $\Gamma_*$ 取得，并且可以同时选择具有代数矩阵元的未点击固定密度矩阵 $\sigma_*$。对每个实代数 $0\le u<R$，也可同时选择代数坐标的合法仪器 $\Gamma_u$ 与纯初态 $P_u$，使

$$
\delta(\Gamma_*)=R,\quad
\mathcal N_{\Gamma_*}(\sigma_*)=\sigma_*,\qquad
\mathbb E_{P_u}^{\Gamma_u}\mathsf N=\mathscr K(u).
\tag{90.1}
$$

证明。实代数数域 $\mathbb A$ 是实闭域。实闭域量词消去给以下标准传递性质：一个只含 $\mathbb A$ 系数的有限实多项式量词公式，若在 $\mathbb R$ 中有解，则在 $\mathbb A$ 中有解。[^wave_real_closed_elimination]

对最近失效仪器，把式（87.1）、（87.5）、（87.6）的共同变量 $\Gamma,\sigma$ 放在同一个公式中并固定半径 $R\in\mathbb A$。引理 79.1 保证实解存在，传递性质给代数实解。任何这样的解都有 $\delta\le R$ 且失效，最小性强制 $\delta=R$。

对固定代数 $u<R$，定理 88.1 保证 $k=\mathscr K(u)\in\mathbb A$。将式（88.4）的变量 $\Gamma,T,k$ 与 $\mathsf B(\Gamma,u)$ 联合，再加入

$$
P=P^\dagger\succeq0,\qquad
P^2=P,\qquad\operatorname{Tr}P=1,\qquad
TP=kP.
\tag{90.2}
$$

最大本征态保证该共同公式有实解，因此有代数解。式（88.2）与（90.2）使同一个装置和同一个纯态的实际均值等于 $k$，即式（90.1）。$\square$

**命题 90.2（临界结构与数值求解的分界）。** 对上述固定接口，准确失效半径、任意代数子临界校准参数的最坏成本，以及临界发散首系数都是实代数数；临界指数为区间 $[1,2]$ 中的有理数。这些结论同时与第 85 节的显式预算相容：

$$
R>0.8005,\qquad \mathscr K(0.8)<20\,000\,010.
$$

证明。分别应用定理 87.2、88.1、89.1 及第 85 节的预算结论。$\square$

其中尚未计算的量仍是 $R$ 的精确值、$p,c$ 及最优仪器的具体矩阵。量词消去提供有限定义与原则上的精确判定，不提供本节尚未执行的消元结果、可行的运算预算或样本复杂度。幂律刻画的是完整校准球中齐次仪器的最坏实际调用数；它不改变物理钟标定，不扩展到任意切换控制或无限维活动记忆。第 84 节指定暗态修复的最优平方根尺度也没有因此被改判为 $p=2$。

[^wave_real_closed_elimination]: Saugata Basu, “Algorithms in Real Algebraic Geometry: A Survey”，[作者提供的 2014 年版本](https://www.math.purdue.edu/~sbasu/raag_survey2011_final-sep4-2014.pdf)。第 1.1 节（第 2 页）明确以任意实闭域为底域，并列出实数与实代数数域；第 2.1 节 Theorem 2.1（第 5 页）陈述量词消去。系数运算在输入的有序整环内，参见第 1.2 节、Definition 1.1 与 Theorem 2.27。实闭域扩张的传递性质由同一无量词公式在两个域上具有相同多项式符号直接得到。本文将这些成熟工具用于式（87.5）、（87.6）、（88.5）的具体仪器与成本合同，不把量词消去本身列为新结果。

[^wave_endpoint_arc]: Edward Bierstone and Pierre D. Milman, “Semianalytic and subanalytic sets,” *Publications Mathématiques de l’IHÉS* **67** (1988), 5–42，[原文 PDF](https://www.numdam.org/item/PMIHES_1988__67__5_0.pdf)，[doi:10.1007/BF02699126](https://doi.org/10.1007/BF02699126)。Lemma 6.3(1)，印刷第 33 页，给一维半解析集在删点后局部连通条件下的实解析参数弧。第 89 节使用连续正向单值图核对条件，再用两个解析坐标的整数消失阶取得主项与余项；代数首系数由有限图闭包另证，并非该引理直接宣告。

## 追加锚（本行以下为增补区）

## 91. 最近失效装置只有一个临界未点击方向

**定义 91.1（最近失效集合与未点击谱）。** 保留定义 87.1 的名义仪器
$Q_0=|0\rangle\langle1|$、$L_0=|0\rangle\langle0|$，以及完整二维活动记忆、两个结果记录与同一仪器齐次重复的合同。记

$$
\mathfrak F_R=\{\Gamma\in\mathfrak F:\delta(\Gamma)=R\},
\qquad
\mathcal A_\Gamma=\mathcal N_\Gamma^*,
\qquad
r(\Gamma)=\operatorname{spr}(\mathcal N_\Gamma).
\tag{91.1}
$$

这里 $\operatorname{spr}$ 是作用于全部复矩阵空间的谱半径；它也等于伴随映射的谱半径。引理 79.1 保证 $\mathfrak F_R$ 非空紧致，第 85 节给 $0<R<1$。对无永久失效的仪器，记

$$
T_\Gamma=\sum_{n\ge0}\mathcal A_\Gamma^n(I),
\qquad M(\Gamma)=\|T_\Gamma\|_\infty.
$$

**定理 91.2（最近失效的唯一暗态与统一谱分离）。** 每个 $\Gamma_*\in\mathfrak F_R$ 恰有一个未点击固定密度矩阵，且它是纯态 $P=|\psi\rangle\langle\psi|$。取与 $\psi$ 正交的单位向量 $\eta$，可以把任一未点击 Kraus 表示写成

$$
A_j=\begin{pmatrix}c_j&b_j\\0&a_j\end{pmatrix},
\qquad
\sum_j|c_j|^2=1,\qquad
\sum_j\overline{c_j}b_j=0.
\tag{91.2}
$$

令

$$
\beta=\sum_j|b_j|^2,\quad
v=\sum_j|a_j|^2,\quad
d=\sum_j\overline{c_j}a_j,\quad
e=1-\beta-v.
$$

则

$$
e\ge1-R>0,\qquad
\beta+v\le R,\qquad |d|\le\sqrt v\le\sqrt R<1.
\tag{91.3}
$$

未点击映射与其伴随的特征值，计代数重数，均为

$$
\boxed{1,\ d,\ \overline d,\ v.}
\tag{91.4}
$$

特别地，特征值 $1$ 是代数简单的，其余谱统一位于 $|z|\le\sqrt R$ 中。最终未点击效果准确为

$$
F_*:=\lim_{n\to\infty}\mathcal A_{\Gamma_*}^n(I)
=P+q(I-P),\qquad
q=\frac{\beta}{1-v}\le R<1.
\tag{91.5}
$$

伴随映射的全部 Hermitian 固定点恰为实数倍的 $F_*$。在正固定点中，$F_*$ 是唯一算子范数为一的成员，其最大本征空间恰为暗态直线。

证明。记实际点击效果为 $E=\mathcal C_{\Gamma_*}^*(I)$。名义仪器从 $P_0=|0\rangle\langle0|$ 出发必点击，完整距离控制这一结果概率，故

$$
\operatorname{Tr}E\ge\langle0|E|0\rangle\ge1-R>0.
\tag{91.6}
$$

任一未点击固定密度矩阵 $\sigma$ 满足 $\operatorname{Tr}(E\sigma)=0$。正性使其支撑包含于 $\ker E$。二维性与 $E\ne0$ 使该核至多一维，而固定密度矩阵存在，因此它恰是一维且 $\sigma=P$ 唯一。于是 $E=e(I-P)$，其中 $e=\operatorname{Tr}E\ge1-R$。

从 $\sum_jA_jPA_j^\dagger=P$ 可知各 $A_j\psi=c_j\psi$，得到上三角形状及 $\sum_j|c_j|^2=1$。完整性给

$$
\sum_jA_j^\dagger A_j=I-E
=\begin{pmatrix}1&0\\0&1-e\end{pmatrix}.
$$

对比矩阵元便得到式（91.2）及 $\beta+v=1-e$；Cauchy–Schwarz 给 $|d|^2\le v$。

若 $H=\begin{pmatrix}x&z\\\overline z&y\end{pmatrix}$ 为 Hermitian，令 $k=\sum_j\overline{b_j}a_j$，直接计算得

$$
\mathcal A_{\Gamma_*}(H)=
\begin{pmatrix}
x&dz\\
\overline d\,\overline z&\beta x+vy+2\operatorname{Re}(kz)
\end{pmatrix}.
\tag{91.7}
$$

在复化坐标 $(x,z,\overline z,y)$ 下这是三角线性系统，故特征多项式为
$(\lambda-1)(\lambda-d)(\lambda-\overline d)(\lambda-v)$。
伴随关系使 $\mathcal N_{\Gamma_*}$ 具有共轭谱，而上述多重集已在共轭下不变，得到式（91.4）。

固定点方程先给 $z=0$，再给 $y=\beta x/(1-v)$。从 $I$ 开始迭代时，$x_n=1,z_n=0$，且 $y_{n+1}=\beta+vy_n$，因而收敛到式（91.5）。又

$$
1-q=\frac e{1-v}\ge e\ge1-R,
$$

故 $q\le R$，其余固定点及最大本征空间的结论随即成立。$\square$

这里的统一界使用了名义仪器的确定点击输入 $P_0$。不能仅从任意二维名义仪器满足 $R<1$，就省略式（91.6）的实际接口条件。

**命题 91.3（较小失效半径并不单独保证唯一暗态）。** 在相同二维活动空间和两个结果接口上，另取名义仪器

$$
\widetilde\Gamma_0
=((1-\gamma)\operatorname{id},\,\gamma\operatorname{id}),
\qquad 0<\gamma<1.
$$

相对于这个新名义仪器，完整失效半径恰为 $\widetilde R=\gamma<1$，但一个最近失效仪器是
$\widetilde\Gamma_*=(\operatorname{id},0)$，它的每个密度矩阵都是暗态。在其子临界校准球内，

$$
\widetilde{\mathscr K}(u)=\frac1{\gamma-u}
\qquad(0\le u<\gamma),
\tag{91.8}
$$

而且每个初态都能与同一个最优仪器共同取得该值，包括混态。

证明。任一失效仪器有未点击固定密度矩阵 $\sigma$；该来源在失效仪器上的点击概率为零，在 $\widetilde\Gamma_0$ 上为 $\gamma$，故完整距离至少 $\gamma$。两个记录块直接相减给
$\frac12\|\widetilde\Gamma_*-\widetilde\Gamma_0\|_\diamond=\gamma$，因此半径准确。

若完整距离至多 $u<\gamma$，每个输入的点击概率都至少 $\gamma-u$，即实际点击效果满足
$E\succeq(\gamma-u)I$。未点击分支因而使每个正输入的迹至多乘 $1-\gamma+u$；逐轮迭代并求尾和，得到式（91.8）的上界。

取

$$
\widetilde\Gamma_u
=((1-\gamma+u)\operatorname{id},\,(\gamma-u)\operatorname{id}).
$$

它与新名义仪器的完整距离恰为 $u$，每个初态都产生成功参数为 $\gamma-u$ 的几何等待律，达到上界。其成本势为 $I/(\gamma-u)$，归一化后恒为 $I$；极限失效仪器的特征值 $1$ 具有四重代数重数。因此唯一纯暗态、统一分离的其余三个谱值和唯一最坏初态均不能只由 $\widetilde R<1$ 推出。$\square$

## 92. 最坏初态与最近失效装置共同趋向同一暗态

**定理 92.1（最优装置、初态与成本势的共同极限）。** 设 $0\le u_j<R$ 且 $u_j\to R$。对每个 $j$，取一个实际达到最坏成本的仪器与初态：

$$
\Gamma_j\in\mathfrak B_{u_j},\qquad
\operatorname{Tr}(\rho_jT_{\Gamma_j})=\mathscr K(u_j).
\tag{92.1}
$$

这里 $\rho_j$ 可以是混态。若某子列 $\Gamma_j\to\Gamma_*$，则该极限属于 $\mathfrak F_R$，并且沿同一子列

$$
\boxed{
\rho_j\longrightarrow P_*,\qquad
\frac{T_{\Gamma_j}}{\mathscr K(u_j)}\longrightarrow F_*,
}
\tag{92.2}
$$

其中 $P_*$ 是 $\Gamma_*$ 自己的唯一暗态，$F_*$ 是它自己的最终未点击效果。特别地，最坏装置族接近最近失效集合；不要求这个集合只有一个装置。

证明。由最坏值定义及式（92.1），必有
$M(\Gamma_j)=\mathscr K(u_j)$。第 80.4 条给该值趋于无穷。

假设某仪器极限 $\Gamma_*$ 不失效。有限维全状态终止给所有未点击谱严格位于单位圆内，所以 $\operatorname{id}-\mathcal A_{\Gamma_*}$ 可逆。有限矩阵逆在可逆点附近连续，而

$$
T_{\Gamma_j}=(\operatorname{id}-\mathcal A_{\Gamma_j})^{-1}(I),
$$

这将使其范数有界，与最坏成本发散矛盾。因此 $\Gamma_*$ 失效。由 $\delta(\Gamma_j)\le u_j$ 的连续极限，$\delta(\Gamma_*)\le R$；失效半径的最小性迫使等号成立。

置 $H_j=T_{\Gamma_j}/\mathscr K(u_j)$。有

$$
0\preceq H_j\preceq I,\quad
\|H_j\|_\infty=1,\quad
\operatorname{Tr}(\rho_jH_j)=1,
\quad H_j-\mathcal A_{\Gamma_j}(H_j)
=\frac I{\mathscr K(u_j)}\longrightarrow0.
\tag{92.3}
$$

从紧性取任何共同收敛子列 $(H_j,\rho_j)\to(H_*,\rho_*)$。极限满足
$H_*\succeq0$、$\|H_*\|_\infty=1$、$\mathcal A_{\Gamma_*}(H_*)=H_*$，故定理 91.2 强制 $H_*=F_*$。

又 $\operatorname{Tr}(\rho_*F_*)=1$，而 $F_*=P_*+q_*(I-P_*)$ 且 $q_*<1$，所以
$\operatorname{Tr}[\rho_*(I-P_*)]=0$。正性给 $\rho_*=P_*$。所有聚点均为同一对 $(F_*,P_*)$，从而沿原来的仪器收敛子列成立式（92.2）。若最优仪器不接近 $\mathfrak F_R$，再用紧性取一个与该集合距离保持正值的聚点便得到矛盾。$\square$

**推论 92.2（充分接近临界时，给定最优装置的最坏初态唯一）。** 存在 $0\le u_0<R$，使每个 $u_0<u<R$ 的每个最坏成本仪器都有唯一的最大等待初态，且该态为纯态。仪器本身仍可不唯一。

证明。若否，可以取 $u_j\to R$ 和最优仪器，使其成本势最高本征值重数至少为二。二维下，归一化成本势便为 $I$。但定理 92.1 的任一仪器收敛子列迫使其趋于 $F_*$，而定理 91.2 给 $F_*$ 的本征值间隙至少 $1-R>0$，矛盾。最高本征值简单时，唯一最大化密度矩阵是其纯本征态。$\square$

## 93. 发散项之外的全部预解贡献统一有界

**定理 93.1（最近失效附近的统一单极点分解）。** 存在包含紧集 $\mathfrak F_R$ 的仪器邻域 $\mathcal U$，使每个 $\Gamma\in\mathcal U$ 都有一个代数简单的正实特征值 $r(\Gamma)$，它严格大于其余特征值的模。对应于伴随映射的谱投影记为 $\Pi_\Gamma$。对其中所有不失效的仪器，

$$
\boxed{
T_\Gamma
=\frac{\Pi_\Gamma(I)}{1-r(\Gamma)}+B_\Gamma,
\qquad
\sup_{\Gamma\in\mathcal U\setminus\mathfrak F}
\|B_\Gamma\|_\infty<\infty.
}
\tag{93.1}
$$

并且，当不失效的 $\Gamma$ 到 $\mathfrak F_R$ 的距离趋零时，统一有

$$
\boxed{(1-r(\Gamma))M(\Gamma)\longrightarrow1.}
\tag{93.2}
$$

若 $\Gamma\to\Gamma_*\in\mathfrak F_R$，则更强地

$$
(1-r(\Gamma))T_\Gamma\longrightarrow F_*.
\tag{93.3}
$$

证明。先说明所用有限矩阵谱事实的参数范围。取
$\sqrt R<a<b<1$，并取围住 $1$、与闭圆盘 $|z|\le a$ 分离的小圆盘。定理 91.2 使每个边界装置的特征多重集在小圆盘内恰有一个根，其他三个根在 $|z|\le\sqrt R$ 内。多项式根随系数连续，紧性因而给一个共同闭邻域，在其中小圆盘内仍恰有一个简单根，其他根的模至多 $a$，且所取根的模大于 $b$。

这一根连续性可直接由有限根的紧性理解：单首多项式系数有界使全部根有界；若系数列收敛，将每次的全部根共同取子列，则极限乘积恰为极限多项式，保留代数重数。于是上述根数和分离若沿任一逼近边界的序列失效，就与边界多重集矛盾。伴随映射在 Hermitian 实基中的矩阵为实矩阵，小圆盘内的唯一根必须等于其共轭，因此为正实数。

CP 次保单位映射的幂在 Hermitian 算子范数下有界；将一般复矩阵分解为两个 Hermitian 矩阵可得复空间上的幂同样有界，故全部谱模长至多一。所取正实根严格支配其余根，所以就是 $r(\Gamma)$。若仪器不失效，第 71 节的有限收缩块使 $r(\Gamma)<1$。

下面给出投影和有界余项的有限代数表达，避免把谱分离本身当成非正规矩阵的范数界。设 $\chi_\Gamma$ 为四维伴随矩阵的特征多项式，写

$$
\chi_\Gamma(z)=(z-r(\Gamma))q_\Gamma(z),
\qquad
\Pi_\Gamma=\frac{q_\Gamma(\mathcal A_\Gamma)}
{q_\Gamma(r(\Gamma))}.
\tag{93.4}
$$

简单性给分母非零。Cayley–Hamilton 与广义特征空间分解说明：该多项式算子在所取特征直线上为恒等，在其他全部广义特征空间上为零；即使其他谱有 Jordan 块也成立。因此 $\Pi_\Gamma$ 为连续的秩一谱投影，与 $\mathcal A_\Gamma$ 对易。

令

$$
\mathcal D_\Gamma=
(\operatorname{id}-\mathcal A_\Gamma+\Pi_\Gamma)^{-1}
(\operatorname{id}-\Pi_\Gamma).
\tag{93.5}
$$

第一因子中的算子在所取特征直线上为乘 $2-r(\Gamma)$，在其余广义特征空间上为 $\operatorname{id}-\mathcal A_\Gamma$，所以在整个共同闭邻域上可逆。它及其逆连续；闭邻域是紧致仪器集的闭子集，故 $\mathcal D_\Gamma$ 具有共同有限范数界。这一步控制了稳定部分全部 Jordan 与非正规贡献。

对不失效仪器，在两份不变子空间上分别计算可得

$$
(\operatorname{id}-\mathcal A_\Gamma)^{-1}
=\frac{\Pi_\Gamma}{1-r(\Gamma)}+\mathcal D_\Gamma.
$$

作用于 $I$，取 $B_\Gamma=\mathcal D_\Gamma(I)$，即得式（93.1）。

在任一 $\Gamma_*\in\mathfrak F_R$ 上，$\mathcal N_{\Gamma_*}(P_*)=P_*$，而伴随的特征直线由 $F_*$ 张成，且 $\operatorname{Tr}(P_*F_*)=1$。因此

$$
\Pi_{\Gamma_*}(X)=\operatorname{Tr}(P_*X)F_*,
\qquad\Pi_{\Gamma_*}(I)=F_*,
\qquad\|\Pi_{\Gamma_*}(I)\|_\infty=1.
\tag{93.6}
$$

连续性与边界紧性给：到 $\mathfrak F_R$ 的距离趋零时，$r(\Gamma)\to1$ 且 $\|\Pi_\Gamma(I)\|_\infty\to1$，均为统一极限。式（93.1）的有界余项于是给式（93.2）；指定仪器极限时，投影的连续性还给式（93.3）。$\square$

本证明与《相位边界》卷第 162.6 节同样保留了“统一谱分离加紧性控制预解算子”的条件；这里用式（93.4）—（93.5）直接写出固定四维的有限矩阵表达。没有把一般 CP 映射当成自伴算子，也没有将非正交谱投影换成正交投影。

## 94. 最坏等待幂律就是最慢未点击谱隙的闭合幂律

**定义 94.1（同一校准球内的最大生存谱半径）。** 对 $0\le u<R$，令

$$
r_{\max}(u)=\max_{\Gamma\in\mathfrak B_u}r(\Gamma),
\qquad \varepsilon(u)=1-r_{\max}(u).
\tag{94.1}
$$

谱半径的连续性与校准球紧性保证该最大值取得。此处仍在每次执行前选定一个完整仪器，未点击后重复它；$r_{\max}$ 不表示逐轮重新优化或切换装置。

**定理 94.2（成本与最慢谱隙的首项相同）。** 有 $\varepsilon(u)>0$，且

$$
\boxed{\lim_{u\uparrow R}\mathscr K(u)\varepsilon(u)=1.}
\tag{94.2}
$$

因此，若 $p,c$ 为定理 89.1 的实际临界参数，则

$$
\boxed{1-r_{\max}(R-h)\sim c^{-1}h^p.}
\tag{94.3}
$$

证明。有限维下，仪器不失效当且仅当 $r(\Gamma)<1$。一方向由全状态终止的有限收缩块成立；另一方向由矩阵幂的有限 Jordan 展开给 $\mathcal N_\Gamma^n\to0$。失效时已有特征值为一的固定密度矩阵，而次保单位的幂有界保证谱半径不会超过一。

每个子临界球都无失效且紧，连续最大值因而严格小于一，得到 $\varepsilon(u)>0$。取最近失效仪器 $\Gamma_*$ 及其固定态 $P_*$，并沿第 80.4 条令

$$
\Gamma_t=t\Gamma_*+(1-t)\Gamma_0,\qquad t=u/R.
$$

正性给 $\mathcal N_{\Gamma_t}^n(P_*)\succeq t^nP_*$。若其谱半径严格小于 $t$，有限 Jordan 展开将使该矩阵幂为 $o(t^n)$，矛盾。因此

$$
r_{\max}(u)\ge u/R\longrightarrow1.
\tag{94.4}
$$

取谱半径最优仪器 $\Gamma_u^{\rm sp}$。当 $u\uparrow R$ 时，它的任一仪器聚点都有谱半径一，因而失效；距离极限至多为 $R$，故属于 $\mathfrak F_R$。因此全部谱最优仪器也接近该紧集。

另取成本最优仪器 $\Gamma_u^{\rm cost}$。定理 92.1 使它们接近同一个最近失效集合。定理 93.1 对这两类实际仪器分别给

$$
\begin{aligned}
M(\Gamma_u^{\rm sp})[1-r(\Gamma_u^{\rm sp})]&\longrightarrow1,\\
\mathscr K(u)[1-r(\Gamma_u^{\rm cost})]&\longrightarrow1.
\end{aligned}
$$

两类最优装置不必相同，但它们都属于同一个球。由各自极值的方向，

$$
M(\Gamma_u^{\rm sp})\varepsilon(u)
\le\mathscr K(u)\varepsilon(u)
\le\mathscr K(u)[1-r(\Gamma_u^{\rm cost})].
\tag{94.5}
$$

两端都趋于一，得到式（94.2）。再代入定理 89.1 即得式（94.3）。$\square$

这份比较没有把两个最优装置强行认作共同实现，而是对各自装置先证明同一个统一预解估计，再按正确的上下界方向夹逼。它也没有声称有限 $u$ 时严格有 $\mathscr K(u)=1/\varepsilon(u)$。

## 95. 一次相干旋转给二次发散留下准确的待证条件

**定义 95.1（只旋转未点击后继的固定仪器族）。** 取任意 $\Gamma_*\in\mathfrak F_R$，并使用定理 91.2 的基 $(\psi,\eta)$ 与参数 $e,v,d$。对实控制角 $\theta$，定义

$$
U_\theta=
\begin{pmatrix}\cos\theta&-\sin\theta\\
\sin\theta&\cos\theta\end{pmatrix},
\qquad
\mathcal N_\theta=\operatorname{Ad}_{U_\theta}\circ\mathcal N_{\Gamma_*},
\qquad \mathcal C_\theta=\mathcal C_{\Gamma_*}.
\tag{95.1}
$$

$\Gamma_\theta=(\mathcal N_\theta,\mathcal C_\theta)$ 是同接口完整仪器，因为旋转不改变未点击效果。每次执行固定一个 $\theta$ 并齐次重复该仪器；$\theta$ 是控制角，不是事件时间或钟读数。

**定理 95.2（暗态后继旋转的二阶泄漏与等待）。** 对充分小的 $\theta\ne0$，$\Gamma_\theta$ 对所有初态终止，且

$$
\boxed{
1-r(\Gamma_\theta)=a_*\theta^2+O(|\theta|^3),
\qquad
a_*=
\frac{e}{1-v}\frac{1-|d|^2}{|1-d|^2}>0.
}
\tag{95.2}
$$

因此

$$
\boxed{M(\Gamma_\theta)\sim\frac1{a_*\theta^2}.}
\tag{95.3}
$$

证明。点击效果仍是 $E=e(I-P)$。若旋转后的仪器失效，则其固定密度矩阵仍必须支撑在 $\ker E=\mathbb C\psi$，只能为 $P$。但

$$
\mathcal N_\theta(P)=U_\theta P U_\theta^\dagger\ne P
$$

对充分小的非零 $\theta$ 成立。因此它不失效。

简单特征值及其谱投影随这个实解析矩阵族实解析变化：这也可由特征多项式在简单根处的隐函数定理及式（93.4）直接得到。取 trace 归一化的 Hermitian 特征矩阵

$$
\sigma_\theta=
\begin{pmatrix}1-y(\theta)&z(\theta)\\
\overline{z(\theta)}&y(\theta)\end{pmatrix},
\qquad
\mathcal N_\theta(\sigma_\theta)=r(\Gamma_\theta)\sigma_\theta,
\qquad \sigma_0=P.
\tag{95.4}
$$

它可由状态侧谱投影作用于 $P$ 后除以迹获得；该迹在零点为一，故在邻域内非零。下面的展开只需这些解析特征方程，不先假定特征矩阵的正性。

沿用 $k=\sum_j\overline{b_j}a_j$。未旋转的状态映射为

$$
\mathcal N_{\Gamma_*}(\sigma_\theta)=
\begin{pmatrix}
1-y+\beta y&\overline d\,z+\overline k\,y\\
d\overline z+ky&vy
\end{pmatrix}.
\tag{95.5}
$$

取迹先得准确关系

$$
r(\Gamma_\theta)=1-ey(\theta).
\tag{95.6}
$$

令 $y(\theta)=y_1\theta+y_2\theta^2+O(|\theta|^3)$，
$z(\theta)=z_1\theta+O(\theta^2)$。将式（95.5）左右乘旋转矩阵，并与式（95.4）的右侧比较。右下角的一阶项给 $y_1=vy_1$，故 $y_1=0$；右上角的一阶项给

$$
z_1=1+\overline d\,z_1,
\qquad z_1=\frac1{1-\overline d}.
$$

右下角的二阶项于是给

$$
(1-v)y_2
=1+2\operatorname{Re}(\overline d\,z_1)
=\frac{1-|d|^2}{|1-d|^2}.
\tag{95.7}
$$

其中 $\overline k\,y$ 只在该角的三阶及更高项出现。由式（95.6）得式（95.2）；$e>0,v<1,|d|<1$ 保证 $a_*>0$。最后对 $\Gamma_\theta\to\Gamma_*\in\mathfrak F_R$ 应用式（93.2），得到式（95.3）。$\square$

**定理 95.3（完整距离的一阶向内方向足以判定 $p=2$）。** 若存在某个实际最近失效仪器及上述旋转方向，使某个 $b_*>0$ 满足

$$
\delta(\Gamma_\theta)
=R-b_*\theta+o(\theta)
\qquad(\theta\downarrow0),
\tag{95.8}
$$

则定理 89.1 的实际临界指数必为 $p=2$，其首系数满足

$$
\frac{b_*^2}{a_*}\le c\le\frac1{1-R}.
\tag{95.9}
$$

证明。置 $h_\theta=R-\delta(\Gamma_\theta)=b_*\theta+o(\theta)>0$。旋转后的同一个仪器属于半径 $R-h_\theta$ 的实际校准球，所以

$$
\mathscr K(R-h_\theta)\ge M(\Gamma_\theta),
\qquad
\liminf_{\theta\downarrow0}
h_\theta^2\mathscr K(R-h_\theta)
\ge\frac{b_*^2}{a_*}>0.
$$

若定理 89.1 的 $p<2$，左侧将趋于零，矛盾。结合已知 $p\le2$ 得 $p=2$，并得到 $c$ 的下界；上界复用推论 89.2。$\square$

式（95.8）是本节尚未履行的条件。旋转确实使暗态发生二阶泄漏，不保证完整 diamond 距离向名义仪器一阶减小；该距离包含全部参考输入及两个量子后继。第 73 节显式候选的距离只是 $R$ 的上界，不能把该候选代入式（95.8）就冒充对真实最近失效装置的结论。因此本节仍保留 $1\le p\le2$，没有无条件宣告二次指数。

本批使用的 Kraus 表示、有限矩阵特征多项式、广义特征空间、简单根隐函数定理及连续求逆均为成熟工具。量子表示沿用第 81 节的 Watrous 来源；统一预解机制与《相位边界》卷第 162.6 节相接。式（91.2）—（91.7）、（93.4）—（93.6）和（95.4）—（95.7）给出当前完整仪器任务所需的具体矩阵连接。所有结论仍要求同一有限活动记忆与齐次重复；它们不提供任意切换协议的谱判据。

## 追加锚（本行以下为增补区）

## 96. 临界谱投影同时给出生存尾和真实准平稳态

**定义 96.1（同一装置的慢尺度与首次点击律）。** 继续固定定义 87.1 的完整二维仪器、名义装置与齐次重复合同。本批使用第 91—95 节的最近失效集合 $\mathfrak F_R$、未点击伴随 $\mathcal A_\Gamma$、主特征值 $r_\Gamma=r(\Gamma)$ 及其秩一谱投影 $\Pi_\Gamma$。对附近不失效的装置，令

$$
\epsilon_\Gamma=1-r_\Gamma>0,\qquad
s_{\Gamma,\rho}(n)=\Pr_\rho^\Gamma(\mathsf N>n)
=\operatorname{Tr}[\rho\mathcal A_\Gamma^n(I)].
\tag{96.1}
$$

$\mathsf N\in\{1,2,\ldots\}$ 包括首次点击那一轮。$\epsilon_\Gamma$ 是当前实际装置的谱泄漏量，与定义 94.1 对整个校准球优化后的 $\varepsilon(u)$ 分开。以下的分布极限缩放调用次数，不改变内部钟标定。

**定理 96.2（统一幂余项与正谱权重）。** 可以缩小定理 93.1 的共同邻域，使存在与装置、初态和轮数无关的 $C<\infty$、$0<q<1$，且其中 $r_\Gamma>q$，对所有 $n\ge0$ 有

$$
\left\|\mathcal A_\Gamma^n-r_\Gamma^n\Pi_\Gamma\right\|_{\infty\to\infty}
\le Cq^n.
\tag{96.2}
$$

存在连续的密度矩阵 $\sigma_\Gamma$ 和正算子 $G_\Gamma=\Pi_\Gamma(I)$，满足

$$
\begin{aligned}
\mathcal N_\Gamma(\sigma_\Gamma)&=r_\Gamma\sigma_\Gamma,&
\mathcal A_\Gamma(G_\Gamma)&=r_\Gamma G_\Gamma,\\
\operatorname{Tr}(G_\Gamma\sigma_\Gamma)&=1,&
\Pi_\Gamma^*(X)&=\operatorname{Tr}(G_\Gamma X)\sigma_\Gamma.
\end{aligned}
\tag{96.3}
$$

这里 $\Pi_\Gamma^*$ 是迹配对下的状态侧伴随。特别地，令 $a_{\Gamma,\rho}=\operatorname{Tr}(\rho G_\Gamma)\ge0$，则

$$
\begin{aligned}
\bigl|s_{\Gamma,\rho}(n)-a_{\Gamma,\rho}r_\Gamma^n\bigr|&\le Cq^n,\\
\left\|\mathcal N_\Gamma^n(\rho)
-a_{\Gamma,\rho}r_\Gamma^n\sigma_\Gamma\right\|_1&\le Cq^n.
\end{aligned}
\tag{96.4}
$$

若 $\Gamma\to\Gamma_*\in\mathfrak F_R$，则 $G_\Gamma\to F_*$、$\sigma_\Gamma\to P_*$。对不失效的固定 $\Gamma$，从实际初态 $\sigma_\Gamma$ 出发，条件于未点击的后继始终是 $\sigma_\Gamma$，且 $\mathsf N$ 准确服从成功参数 $\epsilon_\Gamma$ 的几何分布。

证明。第 93 节给紧致闭邻域上的连续投影，以及其余特征值的统一模长上界 $b<1$。缩小邻域并取 $b<q<\inf_\Gamma r_\Gamma$。置

$$
\mathcal B_\Gamma=\mathcal A_\Gamma(\operatorname{id}-\Pi_\Gamma).
$$

其谱由三个稳定特征值与零组成，故每个 $\mathcal B_\Gamma/q$ 的谱半径严格小于一。有限 Jordan 展开保证它的幂趋零。对每个装置选一个整数 $m_i\ge1$，使相应幂的范数小于 $1/2$；由连续性，此不等式在该装置的一个邻域内仍成立。紧性允许有限覆盖。取这些 $m_i$ 的共同倍数 $m$，则每个装置至少落入其中一个邻域，从而

$$
\left\|(\mathcal B_\Gamma/q)^m\right\|
\le(1/2)^{m/m_i}\le1/2.
$$

前 $m$ 次幂在紧集上共同有界，按长度 $m$ 分块得到所有幂的统一有界性。利用对易及互补性，准确地有

$$
\mathcal A_\Gamma^n-r_\Gamma^n\Pi_\Gamma
=\mathcal B_\Gamma^n(\operatorname{id}-\Pi_\Gamma)
\qquad(n\ge0).
$$

将 $\operatorname{id}-\Pi_\Gamma$ 的共同范数界吸收进 $C$，得到式（96.2），包括 $n=0$。这一步处理非正规矩阵与稳定 Jordan 块，没有把谱半径本身当成算子范数。

由于 $r_\Gamma>q$，式（96.2）给 $r_\Gamma^{-n}\mathcal A_\Gamma^n\to\Pi_\Gamma$。每一项完全正，有限维完全正锥闭合，因此 $\Pi_\Gamma$ 及其伴随也完全正。置

$$
\sigma_\Gamma=
\frac{\Pi_\Gamma^*(I)}{\operatorname{Tr}[\Pi_\Gamma^*(I)]}.
$$

分母为正：在边界它等于 $\operatorname{Tr}F_*=1+q_*\ge1$，连续性及紧性保证缩小后的邻域内仍不为零。投影秩一使每个 $\Pi_\Gamma^*(X)$ 都是 $\sigma_\Gamma$ 的标量倍；取迹确定该标量恰为 $\operatorname{Tr}(G_\Gamma X)$。投影恒等式再给 $\operatorname{Tr}(G_\Gamma\sigma_\Gamma)=1$，主特征方程给式（96.3）。

对式（96.2）取迹对偶得到状态侧 $1\to1$ 范数界，再作用于密度矩阵并取迹，得到式（96.4）。第 93.6 式给边界投影，因而两份连续极限分别为 $F_*$ 与 $P_*$。最后，$\mathcal N_\Gamma^n(\sigma_\Gamma)=r_\Gamma^n\sigma_\Gamma$ 同时给条件后继不变与几何等待律。$\square$

$G_\Gamma$ 在子临界处只保证为正算子，未断言 $G_\Gamma\preceq I$；相应的 $a_{\Gamma,\rho}$ 也未必小于一。因此式（96.4）是带有统一余项的谱分解，不能在有限参数处直接当成两个概率分布的凸混合。边界极限 $F_*\preceq I$ 才保证下一节混合权重的概率意义。

## 97. 一般初态给零点质量与指数尾的共同极限

**定理 97.1（首次点击的缩放分布及全部固定正阶矩）。** 设不失效的 $\Gamma_j\to\Gamma_*\in\mathfrak F_R$，初态 $\rho_j\to\rho_*$。记

$$
\epsilon_j=1-r(\Gamma_j),\qquad
\alpha=\operatorname{Tr}(\rho_*F_*)\in[0,1],\qquad
X_j=\epsilon_j\mathsf N_j.
$$

其中 $\mathsf N_j$ 是从同一对 $(\Gamma_j,\rho_j)$ 实际产生的首次点击轮数。则

$$
\boxed{
X_j\ \Rightarrow\ (1-\alpha)\delta_0+\alpha\operatorname{Exp}(1).
}
\tag{97.1}
$$

$\Rightarrow$ 表示弱收敛，$\delta_0$ 表示零点单位质量。对每个固定 $t>0$，准确的尾极限是

$$
\lim_j\Pr(X_j>t)=\alpha e^{-t}.
\tag{97.2}
$$

对每个固定实数 $a>0$，还有

$$
\boxed{
\lim_j\epsilon_j^a\mathbb E\mathsf N_j^a
=\alpha\int_0^\infty a t^{a-1}e^{-t}\,dt
=\alpha\,\Gamma_{\rm E}(a+1).
}
\tag{97.3}
$$

$\Gamma_{\rm E}$ 是 Euler Gamma 函数，与仪器符号不同。特别地，整数 $k\ge1$ 的极限为 $\alpha k!$，且

$$
\epsilon_j^2\operatorname{Var}(\mathsf N_j)
\longrightarrow2\alpha-\alpha^2.
\tag{97.4}
$$

证明。令 $a_j=\operatorname{Tr}(\rho_jG_{\Gamma_j})\to\alpha$。因为 $\mathsf N_j$ 取整数值，

$$
\Pr(X_j>t)
=s_{\Gamma_j,\rho_j}\!\left(\left\lfloor t/\epsilon_j\right\rfloor\right).
$$

对固定 $t>0$，$\epsilon_j\to0$，式（96.4）的余项趋零，而

$$
(1-\epsilon_j)^{\lfloor t/\epsilon_j\rfloor}\longrightarrow e^{-t}.
$$

得到式（97.2）。极限分布在每个正点连续，在负点分布函数为零；当 $\alpha<1$ 时零点是允许的跳跃点。因此这些尾极限准确给式（97.1）。当 $\alpha=1$ 时零点也是连续点，原分布在零点的质量始终为零。

矩收敛不能只由弱收敛推出。这里使用同一幂估计提供共同可积包络。$a_j$ 共同有界，取固定 $0<\epsilon_0<1$，使充分大的 $j$ 有 $\epsilon_j\le\epsilon_0$。对全部 $t\ge0$，

$$
\begin{aligned}
(1-\epsilon_j)^{\lfloor t/\epsilon_j\rfloor}&\le e^{\epsilon_0}e^{-t},\\
q^{\lfloor t/\epsilon_j\rfloor}&\le q^{-1}
\exp\!\left(-\frac{|\log q|}{\epsilon_0}t\right).
\end{aligned}
\tag{97.5}
$$

因此 $\Pr(X_j>t)$ 有与 $j$ 无关的指数包络。任意 $a>0$ 都有非负随机变量的尾积分恒等式

$$
\mathbb E X_j^a
=\int_0^\infty a t^{a-1}\Pr(X_j>t)\,dt.
$$

式（97.5）乘 $a t^{a-1}$ 后在零点附近及无穷远均可积。支配收敛给式（97.3）。使用 $a=1,2$ 后相减即得方差公式。$\square$

极限中的 $\alpha$ 正是从 $\rho_*$ 出发在边界装置 $\Gamma_*$ 上永久未点击的概率。子临界装置仍然最终点击；边界会永久保留的那部分质量，在临界逼近时成为越来越长的指数等待。其余质量的等待在 $1/\epsilon_j$ 尺度下压到零点，零点质量并不表示真实装置在第零轮已经点击。

**命题 97.2（缩放、无限等待与总变差的边界）。** 在定理 97.1 的合同中，若 $\alpha<1$，不能把式（97.2）延伸为 $t=0$ 时同一尾公式；若 $\alpha=1$，$X_j$ 的分布与连续 $\operatorname{Exp}(1)$ 的总变差距离对每个 $j$ 都恰为一。与此同时，$\alpha=1$ 时分布函数仍然一致收敛到指数分布函数。

证明。$X_j>0$ 几乎处处，所以 $\Pr(X_j>0)=1$，而候选右侧在零点为 $\alpha$。在 $\alpha=1$ 时，每个 $X_j$ 都支撑于可数格点集 $\{\epsilon_j,2\epsilon_j,\ldots\}$；连续指数律赋该集合零质量，所以按事件概率差的上确界定义，总变差距离为一。

分布函数一致收敛则由弱收敛到连续分布和单调性得到：先截去指数尾，再把剩余紧区间分为足够细的有限网格；网格点上的收敛与相邻点之间的单调夹逼共同控制上确界。$\square$

式（97.3）只断言每个预先固定的阶数，未声称同时控制随 $j$ 增大的矩阶数。若 $\alpha=0$，所有这些缩放矩趋零，也不能反推未缩放均值保持有界。

## 98. 连续未点击记录在短过渡期后选出准平稳后继

**定理 98.1（对数轮数的条件筛选与离散几何近似）。** 沿用定理 97.1，另假定 $\alpha>0$。固定 $L>0$，对充分大的 $j$ 定义

$$
b_j=\left\lceil L\log(1/\epsilon_j)\right\rceil,
\qquad
\widehat\rho_j=
\frac{\mathcal N_{\Gamma_j}^{b_j}(\rho_j)}
{s_{\Gamma_j,\rho_j}(b_j)}.
\tag{98.1}
$$

这些条件态均在正概率事件上定义，并满足

$$
\boxed{
\epsilon_j b_j\to0,\qquad
s_{\Gamma_j,\rho_j}(b_j)\to\alpha,\qquad
\|\widehat\rho_j-\sigma_{\Gamma_j}\|_1
=O\!\left(\epsilon_j^{L|\log q|}\right).
}
\tag{98.2}
$$

从而 $\widehat\rho_j\to P_*$。条件于前 $b_j$ 轮未点击，剩余调用数满足更强的离散分布比较：

$$
\boxed{
\operatorname{TV}\!\left(
\mathcal L(\mathsf N_j-b_j\mid\mathsf N_j>b_j),
\operatorname{Geom}(\epsilon_j)
\right)
=O\!\left(\epsilon_j^{L|\log q|}\right).
}
\tag{98.3}
$$

几何分布在 $1,2,\ldots$ 上取值。其参数始终是当前同一装置的 $\epsilon_j$，没有提前把装置替换成失效端点。

证明。$b_j\to\infty$ 且 $\epsilon_jb_j\to0$，因此 $r_j^{b_j}\to1$。式（96.4）给

$$
\mathcal N_{\Gamma_j}^{b_j}(\rho_j)
=a_jr_j^{b_j}\sigma_{\Gamma_j}+R_j,
\qquad \|R_j\|_1\le Cq^{b_j}
\le C\epsilon_j^{L|\log q|}.
$$

取迹后，分母趋于 $\alpha>0$，故充分大时有统一正下界。归一化相减给

$$
\widehat\rho_j-\sigma_{\Gamma_j}
=\frac{R_j-\operatorname{Tr}(R_j)\sigma_{\Gamma_j}}
{s_{\Gamma_j,\rho_j}(b_j)},
$$

从而得到式（98.2）的迹范数界。再用 $\sigma_{\Gamma_j}\to P_*$。

对每个固定 $j$，装置在所有初态上终止，全部首次点击轮数效果构成总和为 $I$ 的可数 POVM。任意轮数集合 $A$ 对应一个 $0\preceq E_A\preceq I$ 的效果，故两初态产生的完整剩余等待律总变差至多是初态半迹距离：

$$
\operatorname{TV}(\mathcal L_\tau\mathsf N,\mathcal L_\sigma\mathsf N)
\le\frac12\|\tau-\sigma\|_1.
\tag{98.4}
$$

完整活动记忆与齐次重复保证，在前 $b_j$ 轮未点击后，真实剩余协议恰是从 $\widehat\rho_j$ 重新开始同一仪器。用 $\sigma_{\Gamma_j}$ 作比较时，第 96 节给准确几何律。代入式（98.4）即得式（98.3）。$\square$

**推论 98.2（条件点击率与谱泄漏的一阶一致）。** 若定理 98.1 中再取 $L|\log q|>1$，则

$$
\frac{\Pr(\mathsf N_j=b_j+1\mid\mathsf N_j>b_j)}{\epsilon_j}
\longrightarrow1.
\tag{98.5}
$$

证明。式（98.3）控制剩余轮数等于一这一事件的概率差为 $O(\epsilon_j^{L|\log q|})=o(\epsilon_j)$；几何律的该概率恰为 $\epsilon_j$。$\square$

本节的条件筛选依赖 $\alpha>0$，以及实际取得的一串未点击记录。它没有把丢失的记录免费补回，也没有规定初态必须已经是准平稳态。$b_j$ 随临界逼近发散，但相对于主要等待尺度 $1/\epsilon_j$ 为低阶。迹范数收敛到 $P_*$ 的速度还包含 $\sigma_{\Gamma_j}\to P_*$ 的装置收敛速度；式（98.2）只量化向当前准平稳态的靠近。

## 99. 最坏初态的整个等待律由自身均值归一化为指数律

**定理 99.1（任意最优选择的共同极限律）。** 设 $u_j<R$、$u_j\to R$，每次选择任意一对满足式（92.1）的实际最优仪器与初态。令 $K_j=\mathscr K(u_j)$。即使这些装置不收敛到唯一的最近失效仪器，仍有

$$
\boxed{
\frac{\mathsf N_j}{K_j}\Rightarrow\operatorname{Exp}(1),
\qquad
\frac{\mathbb E\mathsf N_j^a}{K_j^a}
\longrightarrow\Gamma_{\rm E}(a+1)
\quad\text{对每个固定 }a>0.
}
\tag{99.1}
$$

特别地，

$$
\frac{\operatorname{Var}(\mathsf N_j)}{K_j^2}\to1,
\qquad
\frac{\sqrt{\operatorname{Var}(\mathsf N_j)}}{\mathbb E\mathsf N_j}\to1.
\tag{99.2}
$$

证明。任取一个子列。仪器空间紧性允许再取 $\Gamma_j\to\Gamma_*$；定理 92.1 迫使 $\Gamma_*\in\mathfrak F_R$ 且 $\rho_j\to P_*$。因此定理 97.1 的权重为 $\alpha=\operatorname{Tr}(P_*F_*)=1$。

同一装置满足 $M(\Gamma_j)=K_j$，而定理 93.1 给 $\epsilon_jK_j\to1$。于是

$$
\frac{\mathsf N_j}{K_j}
=\frac{\epsilon_j\mathsf N_j}{\epsilon_jK_j}.
$$

定理 97.1 的分布及矩结论在这个子列上给出式（99.1）。所有子列都有进一步子列趋于同一分布及同一矩值，所以原列也有这些极限。式（99.2）使用一、二阶矩，且本来就有 $\mathbb E\mathsf N_j=K_j$。$\square$

**推论 99.2（固定分位数具有同一临界幂）。** 对固定 $0<\tau<1$，令 $Q_{\tau,j}$ 为实际最优等待律的最小 $\tau$ 分位轮数，即最小的整数 $n$ 使 $\Pr(\mathsf N_j\le n)\ge\tau$。则

$$
\frac{Q_{\tau,j}}{K_j}\longrightarrow-\log(1-\tau).
\tag{99.3}
$$

若写 $h_j=R-u_j\to0^+$，并使用定理 89.1 的实际参数 $c,p$，则

$$
Q_{\tau,j}\sim[-\log(1-\tau)]c\,h_j^{-p}.
\tag{99.4}
$$

证明。指数分布函数连续且在正半轴严格递增。在其 $\tau$ 分位点左右各取一个固定小间隔，两端分布函数分别严格小于和大于 $\tau$。式（99.1）使实际缩放分位点最终夹在两端之间；间隔趋零得到式（99.3）。再代入 $K_j\sim c h_j^{-p}$。$\square$

这里的分位结论不覆盖随 $j$ 趋于一的置信水平。均值发散也没有使等待集中成一个确定轮数：相对标准差趋于一。不同最优装置可以具有不同的暗态与矩阵结构，但在自身均值尺度上呈现同一个指数等待形状。

## 100. 暗态权重决定长等待的质量，谱泄漏决定它的尺度

**关系结论 100.1（未点击后继、等待质量与等待形状）。** 第 96—99 节给出三个由同一个实际仪器连接的对象：

$$
\boxed{
\alpha=\operatorname{Tr}(\rho_*F_*)
\quad\text{决定慢等待部分的极限质量};\qquad
\epsilon_\Gamma^{-1}
\quad\text{决定慢等待的调用尺度};\qquad
\sigma_\Gamma
\quad\text{决定未点击后的准平稳关系}.
}
$$

本批的“AHH”在于：在第 98 节 $\alpha>0$ 的条件下，一段不断积累的未点击记录，也能把后继态筛选到接近暗态，同时把余下事件时间变成接近几何分布的等待。第 98 节用同一装置、同一条件事件与迹距离收缩把这两件事连接起来。临界最优初态具有全部慢质量，因而得到纯指数缩放律；一般初态还保留压到零点的早期点击质量。它们无需先知道失效半径的精确值或临界幂的精确指数。

**来源与适用边界 100.2。** 有限矩阵谱投影、Jordan 展开、紧性、尾积分和支配收敛是本批使用的成熟工具；量子仪器及迹距离收缩仍沿用前文核对的 Watrous 来源。经典吸收 Markov 链中的准平稳分布研究可见 J. N. Darroch、E. Seneta，[*On Quasi-Stationary Distributions in Absorbing Discrete-Time Finite Markov Chains*](https://doi.org/10.2307/3211876)，1965。该文献是概念背景；本批不把经典非负矩阵的额外假设直接施加到未必不可约的量子映射，而由式（96.2）—（96.4）独立建立所需的正投影与统一幂估计。

本批连接的是前述最近失效结构与真实首次点击律，属于成熟工具下的纸面推导，不主张文献原创性。结论保留完整有限活动记忆、当前指定名义仪器及每次执行中重复同一仪器的条件；不推出任意切换协议的指数律，不把离散律与连续律的弱收敛称作总变差收敛，不由等待形状倒推出 $R=c_*$ 或 $p=2$。未新增或编译 Lean，未进入消化、覆盖或冻结链。

## 追加锚（本行以下为增补区）

## 101. 带参考系统的检验消去失效装置的未知相干项

**定义 101.1（原名义仪器与暗态参数）。** 本批继续使用定义 87.1 的原名义仪器、完整二维活动记忆、两个记录与齐次重复合同，记

$$
\phi=\frac{1+\sqrt5}{2},\qquad
c_*^2=\frac{11+5\sqrt5}{32}=\frac{3+5\phi}{16}.
\tag{101.1}
$$

第 73 节已经给出距离恰为 $c_*$ 的失效仪器 $\Gamma_+$；本批将证明匹配的全局下界，并履行第 95.8 式的一阶向内条件。此前关于精确 $R$、$p$ 未求出的边界由本批新证明补足，原有有条件结论及其既有字节保留。

考虑任一失效仪器。若其未点击固定密度矩阵满秩，则点击效果为零；用名义装置的确定点击输入 $P_0$ 检验，完整距离为一。对其余需考虑的失效装置，取纯固定态 $P_\psi$。同时作输入、输出的计算基对角酉共轭不改变名义仪器或完整距离，可以令

$$
\psi=\sqrt a\,|0\rangle+\sqrt b\,|1\rangle,
\qquad \eta=-\sqrt b\,|0\rangle+\sqrt a\,|1\rangle,
\qquad b=1-a.
\tag{101.2}
$$

将点击量子后继用一个通道重置为 $P_0$，保持未点击分支不变。这个后处理固定名义仪器、保持失效，并且不能增大完整 half-diamond 距离。因此，对重置后的每个装置证明共同下界，便也证明原装置的下界。

由纯固定态与完整性，未点击 Kraus 算子仍有式（91.2）的上三角形状；该形状不要求装置已经最近失效。用该式的 $\beta,v,d,k$，有 $\beta,v\ge0$、$e=1-\beta-v\ge0$，点击映射为

$$
\mathcal C(X)=e\operatorname{Tr}(P_\eta X)P_0.
\tag{101.3}
$$

以下允许 $d,k$ 为复数，未靠实数化删除可能的失效装置。

**定理 101.2（独立于全部未知 Kraus 参数的参考检验下界）。** 设 $0<a<1$，并选择

$$
\frac12\le z<1,\qquad a+2(b-a)z\ge0.
\tag{101.4}
$$

则每个具有该纯暗态参数的完整失效仪器都满足

$$
\boxed{
\delta(\Gamma)\ge L(a,z):=
\frac12\left[
\sqrt{a^2+4abz(1-z)+4b^2z^2}
+\sqrt{a^2+4abz(1-z)}
\right].
}
\tag{101.5}
$$

证明。按定义 101.1 先重置点击后继，记重置后仪器为 $\Gamma'$。取参考量子比特与归一化联合输入

$$
|\Omega_z\rangle
=\sqrt{1-z}\,|0_R0\rangle+\sqrt z\,|1_R\psi\rangle.
\tag{101.6}
$$

其系统边缘为 $(1-z)P_0+zP_\psi$。比较同一暗态的投影仪器

$$
\mathcal N_a^{\rm pr}(X)=P_\psi XP_\psi,\qquad
\mathcal C_a^{\rm pr}(X)=\operatorname{Tr}(P_\eta X)P_0
$$

与名义仪器在这个联合输入上的输出。未点击块之差为

$$
D_N=|u\rangle\langle u|-|q_0\rangle\langle q_0|,
\quad
u=\sqrt{a(1-z)}\,|0_R\psi\rangle+\sqrt z\,|1_R\psi\rangle,
\quad
q_0=\sqrt{bz}\,|1_R0\rangle.
\tag{101.7}
$$

点击块之差为

$$
D_C=w|0_R0\rangle\langle0_R0|-|\ell\rangle\langle\ell|,
\quad w=b(1-z),\quad
\ell=\sqrt{1-z}\,|0_R0\rangle+\sqrt{az}\,|1_R0\rangle.
\tag{101.8}
$$

置

$$
\chi=\sqrt{a^2+4abz(1-z)},\qquad
\nu=\sqrt{\chi^2+4b^2z^2},\qquad T=a+2bz.
\tag{101.9}
$$

两个向量投影之差的非零谱可由迹与行列式直接求出，给

$$
\operatorname{Tr}D_N=a,\quad\|D_N\|_1=\nu,
\qquad
\operatorname{Tr}D_C=-a,\quad\|D_C\|_1=\chi.
$$

因 $0<a<1$、$0<z<1$，两块各有恰好一个负本征值。令 $E_N,E_C$ 分别为其负谱投影，在各自核上取零。由总迹为零，投影仪器的这份联合输出差在该负谱检验上的负权重为

$$
-\operatorname{Tr}(E_ND_N)-\operatorname{Tr}(E_CD_C)
=\frac{\nu+\chi}{2}.
\tag{101.10}
$$

现在保持同一联合输入及同一两个检验，换成任意可行的 $\Gamma'$。定义

$$
w_\psi=-\sqrt w\,|0_R\psi\rangle,
\qquad w_\eta=-\sqrt w\,|0_R\eta\rangle.
$$

每个未点击 Kraus 算子的联合输出向量为 $c_j u+b_jw_\psi+a_jw_\eta$。式（91.2）中的 $\sum_j\overline{c_j}b_j=0$ 消去 $u,w_\psi$ 之间的交叉项。更关键的是

$$
w_\eta\perp u,\qquad w_\eta\perp q_0,
\qquad E_Nw_\eta=0.
\tag{101.11}
$$

于是所有含 $d,k$ 的交叉项，以及 $v|w_\eta\rangle\langle w_\eta|$，都在这个未点击检验下消失。只剩 $\beta$ 项。令

$$
h_N=\langle0_R\psi|E_N|0_R\psi\rangle,
\qquad h_C=\langle0_R0|E_C|0_R0\rangle.
$$

实际点击输出比投影仪器少 $(\beta+v)w|0_R0\rangle\langle0_R0|$。完整输出差仍然迹为零，任一效果的负期望都不超过半迹范数。因此，同一实际装置满足

$$
\delta(\Gamma)\ge\delta(\Gamma')
\ge\frac{\nu+\chi}{2}
+w\{\beta(h_C-h_N)+vh_C\}.
\tag{101.12}
$$

最后核对未知非负参数的系数。点击块在其二维支撑上的负谱投影给

$$
h_C=\frac12\left(1+\frac{a(1-2z)}{\chi}\right).
\tag{101.13}
$$

未点击块的特征值为 $\lambda_\pm=(a\pm\nu)/2$。其负谱投影满足

$$
\langle u|E_N|u\rangle
=\frac{(T-\nu)(\nu-a)}{4\nu}.
$$

对负本征向量应用 $D_N$，再与 $|0_R\psi\rangle$ 配对；因该向量与 $q_0$ 正交，其分量等于 $\sqrt{a(1-z)}$ 乘对应的 $u$ 分量再除以 $\lambda_-$。取模平方得到

$$
h_N=\frac{a(1-z)(T-\nu)}{\nu(\nu-a)}.
\tag{101.14}
$$

这里 $\nu>a>0$，分母严格为正。由 $z\ge1/2$ 和 $\chi\ge a$，式（101.13）给 $h_C\ge1-z$。另一方面，

$$
\begin{aligned}
h_N\le1-z
&\iff aT\le\nu^2,\\
\nu^2-aT&=2bz\{a+2(b-a)z\}\ge0.
\end{aligned}
\tag{101.15}
$$

因此 $h_C-h_N\ge0$ 且 $h_C\ge0$。式（101.12）中的附加项非负，得到式（101.5）。$\square$

这个下界对同一个实际仪器的全部可行 $\beta,v,d,k$ 同时成立。它没有将不同装置各自可达到的读数拼成一个假想装置，也没有假定投影仪器在每个固定 $a$ 下都最优。

## 102. 真实失效半径的精确值

**定理 102.1（完整仪器失效半径恰为显式候选距离）。** 对本卷固定的名义仪器和完整接口，

$$
\boxed{
R=\sqrt{\frac{11+5\sqrt5}{32}}
=\frac{\phi^{5/2}}4.
}
\tag{102.1}
$$

证明。第 73 节已给匹配上界，故只需证明每个失效装置的距离至少为 $c_*$。定义 101.1 已处理满秩固定态的距离一；其余按纯暗态参数 $a$ 分三段。

第一段，$0\le a\le1/4$。第 71.2 条的暗态输入检验给

$$
\delta(\Gamma)\ge
\frac{a+\sqrt{a^2+4(1-a)^2}}2
\ge1-\frac a2\ge\frac78>c_*.
\tag{102.2}
$$

第二段，$1/4\le a\le2/3$。取 $z_0=\phi/2\in(1/2,1)$，则

$$
a+2(b-a)z_0
=\phi+(1-2\phi)a
\ge\frac{2-\phi}{3}>0.
$$

定理 101.2 可用。为了精确比较 $L(a,z_0)$ 与 $c_*$，置

$$
\begin{aligned}
A&=\chi^2=a^2+(\phi-1)ab
=1+(\phi-3)b+(2-\phi)b^2,\\
B&=\nu^2=A+(\phi+1)b^2
=1+(\phi-3)b+3b^2,\\
D&=4c_*^2=\frac{3+5\phi}{4}.
\end{aligned}
$$

利用 $\phi^2=\phi+1$ 逐项展开并收集系数，得到精确因式分解

$$
\boxed{
(D-A-B)^2-4AB
=\left(b-\frac12\right)^2
\left[(2+3\phi)(b^2+b)-\frac{14+25\phi}{4}\right].
}
\tag{102.3}
$$

本段 $1/3\le b\le3/4$，故方括号至多为

$$
\frac{21(2+3\phi)-4(14+25\phi)}{16}
=-\frac{14+37\phi}{16}<0.
$$

因此 $(D-A-B)^2\le4AB$，推出 $D\le A+B+2\sqrt{AB}$。于是

$$
L(a,z_0)=\frac{\sqrt A+\sqrt B}{2}\ge c_*.
\tag{102.4}
$$

除 $a=1/2$ 外上述不等式严格。在 $a=1/2$ 处，$A=\phi/4$、$B=\phi^3/4$，且 $1+\phi=\phi^2$，所以 $L(1/2,z_0)=\phi^{5/2}/4=c_*$。

第三段，$2/3\le a<1$。取 $z=1/2$，式（101.4）的第二个条件变为 $b\ge0$，所以

$$
\begin{aligned}
\delta(\Gamma)
&\ge\frac{\sqrt{1-ab}+\sqrt a}{2}\\
&\ge\frac{\sqrt7+\sqrt6}{6}
>\frac56>c_*.
\end{aligned}
\tag{102.5}
$$

这里使用 $ab\le2/9$。最后一个严格比较可平方核对：$c_*<5/6$ 等价于 $\sqrt5<101/45$，而 $5\cdot45^2<101^2$。端点 $a=1$ 由暗态输入检验给距离一。三段覆盖全部纯暗态，匹配上界使式（102.1）成立。$\square$

**推论 102.2（最近失效装置的未点击分支必须是平衡纯投影）。** 每个最近失效装置的纯暗态满足 $|\langle0|\psi\rangle|^2=1/2$，且其未点击映射准确为

$$
\mathcal N(X)=P_\psi XP_\psi.
\tag{102.6}
$$

将点击后继重置为 $P_0$ 并作计算基相位对齐后，最近失效装置成为第 73 节的 $\Gamma_+$。

证明。重置点击后继不能改变未点击映射；重置后的失效距离至少为 $R$，又不超过原来的 $R$，所以仍然取等号。第 102.2、102.4、102.5 式的严格性迫使 $a=1/2$。

在 $a=1/2,z=z_0$ 时，$\chi>a$ 且 $z_0>1/2$，故式（101.13）严格给 $h_C>1-z_0$。式（101.15）的右侧严格为正，故 $h_N<1-z_0$。又 $w>0$，因此式（101.12）取等号必须有 $\beta=v=0$。由它们分别是 $\sum_j|b_j|^2$、$\sum_j|a_j|^2$，所有 $b_j,a_j$ 都为零。每个未点击 Kraus 算子于是为 $c_jP_\psi$，且 $\sum_j|c_j|^2=1$，给式（102.6）。点击重置后完整性确定另一分支为 $\operatorname{Tr}[(I-P_\psi)X]P_0$。$\square$

这条推论没有声称原来的所有点击量子后继已经唯一确定。重置是实际通道后处理，原接口中可访问的点击后继仍属于完整装置的一部分。

## 103. 显式候选的完整距离确实存在一阶向内方向

**定义 103.1（平衡投影的输出旋转）。** 取

$$
\psi=\frac{|0\rangle+|1\rangle}{\sqrt2},\qquad
\eta=\frac{-|0\rangle+|1\rangle}{\sqrt2},\qquad
\psi_\theta=\cos\theta\,\psi+\sin\theta\,\eta.
$$

定义固定齐次仪器

$$
\widehat Q_\theta=|\psi_\theta\rangle\langle\psi|,
\qquad \widehat L_\theta=|0\rangle\langle\eta|,
\qquad \widehat\Gamma_\theta=(\operatorname{Ad}_{\widehat Q_\theta},\operatorname{Ad}_{\widehat L_\theta}).
\tag{103.1}
$$

这与定义 95.1 在 $\Gamma_+$ 处的输出旋转一致，完整性对每个 $\theta$ 成立。$\theta=0$ 是定理 102.1 已证明的真实最近失效装置；参数向内的方向将是 $\theta<0$。

**定理 103.2（保留全部参考输入的精确距离公式与导数）。** 令

$$
J=\left[\frac{1-\sqrt2}{2},\frac{1+\sqrt2}{2}\right].
$$

对上述仪器，完整距离准确为

$$
\boxed{
\delta(\widehat\Gamma_\theta)
=\max_{x\in J}\frac12\left[
\sqrt{\frac54-x+\sin(2\theta)(1-x)^2}
+\sqrt{\frac14+x-x^2}
\right].
}
\tag{103.2}
$$

特别地，若 $t\downarrow0$，则

$$
\boxed{
\delta(\widehat\Gamma_{-t})
=R-\kappa t+O(t^2),
\qquad
\kappa=\frac{\sqrt\phi}{4}>0.
}
\tag{103.3}
$$

证明。完整通道之差保持 Hermitian；第 87 节使用的纯联合输入表征允许在一个量子比特参考上最大化。取任意纯联合输入，其系统边缘为

$$
\rho=\begin{pmatrix}q_0&u+iv\\u-iv&1-q_0\end{pmatrix},
\qquad \rho\succeq0,\quad\operatorname{Tr}\rho=1,
\qquad x=q_0-u.
$$

每个记录分支在该纯联合输入上各给一个未归一化纯向量。两个向量投影之差满足

$$
\bigl\||f\rangle\langle f|-|g\rangle\langle g|\bigr\|_1
=\sqrt{(\|f\|^2+\|g\|^2)^2-4|\langle f,g\rangle|^2}.
\tag{103.4}
$$

未点击的两个范数平方为 $1/2+u$ 与 $1-q_0$；内积模平方为
$(1-\sin2\theta)[(1-x)^2+v^2]/4$。点击分支的两个范数平方为 $1/2-u$ 与 $q_0$，内积模平方为 $(x^2+v^2)/2$。记录正交，故完整输出的半迹距离准确为

$$
F_\theta(x,v)=\frac12\left[
\sqrt{\frac54-x-v^2+\sin(2\theta)((1-x)^2+v^2)}
+\sqrt{\frac14+x-x^2-2v^2}
\right].
\tag{103.5}
$$

将边缘态的虚部 $v$ 置零保持正性与迹一，不改变 $x$；因 $\sin2\theta-1\le0$，两个根号内的数均不减。因此最大值可在实边缘态上取得。

再令

$$
H=\begin{pmatrix}1&-1/2\\-1/2&0\end{pmatrix}.
$$

有 $x=\operatorname{Tr}(\rho H)$，所以 $x$ 的范围恰为 $H$ 的本征值区间 $J$。每个 $x\in J$ 都由一个实纯系统态达到：在 $H$ 的实本征基上取适当的实单位叠加即可。故对全部联合输入的最大化准确化为式（103.2），而非只取得一个无参考的下界。

在 $\theta=0$ 时，第 73.2 条已给唯一最大坐标

$$
x_* =\frac{3-\sqrt5}{4}=1-\frac\phi2,
$$

位于 $J$ 内部，两个根号都严格为正。该处目标对 $x$ 的二阶导数严格为负：第一项 $\sqrt{5/4-x}$ 严格凹，第二项 $\sqrt{1/4+x-x^2}$ 在内部凹。目标在 $(x_*,0)$ 的邻域内光滑。

由紧区间上的唯一最大值，充分小的 $\theta$ 的全部最大坐标都落在 $x_*$ 的任意预定小邻域内；否则取最大点收敛子列会给 $\theta=0$ 的另一最大点。局部二阶导数保持负值，隐函数定理因而给唯一光滑最大坐标 $x(\theta)$。最大值的一阶导数只剩显含 $\theta$ 的部分，得到

$$
\left.\frac{d}{d\theta}\delta(\widehat\Gamma_\theta)\right|_{\theta=0}
=\frac{(1-x_*)^2}{2\sqrt{5/4-x_*}}
=\frac{\sqrt\phi}{4}.
\tag{103.6}
$$

光滑性给二阶余项；使用 $\delta(\widehat\Gamma_0)=\delta(\Gamma_+)=R$，再将 $\theta=-t$，便得式（103.3）。$\square$

旋转族用 $\widehat\Gamma_\theta$ 标记，名义装置仍由 $Q_0=|0\rangle\langle1|$、$L_0=|0\rangle\langle0|$ 指定。上述距离在任何角度都是相对于该固定名义装置计算。

## 104. 临界等待成本的指数准确为二

**定理 104.1（真实失效边界的二次发散）。** 定理 89.1 中的临界参数满足

$$
\boxed{
p=2,\qquad
\frac{1+\sqrt5}{32}\le c\le\frac1{1-R},
\qquad R=\sqrt{\frac{11+5\sqrt5}{32}}.
}
\tag{104.1}
$$

因而存在正整数 $m$，使真实最坏成本满足

$$
\boxed{
\mathscr K(R-h)
=c\,h^{-2}\bigl(1+O(h^{1/m})\bigr)
\qquad(h\downarrow0).
}
\tag{104.2}
$$

证明。先对式（103.1）的同一个实际仪器计算全部等待。其未点击映射为

$$
\mathcal N_\theta(X)=\operatorname{Tr}(P_\psi X)P_{\psi_\theta}.
$$

唯一可能的非零特征值为
$\operatorname{Tr}(P_\psi P_{\psi_\theta})=\cos^2\theta$。对充分小的非零 $\theta$，该值严格小于一，所以所有初态终止。其伴随生存效果为

$$
\mathcal A_\theta^n(I)
=\cos^{2(n-1)}\theta\,P_\psi
\quad(n\ge1).
$$

求和得到准确成本

$$
T_{\widehat\Gamma_\theta}=I+\frac{P_\psi}{\sin^2\theta},
\qquad
M(\widehat\Gamma_\theta)=1+\frac1{\sin^2\theta}.
\tag{104.3}
$$

由定理 103.2，令 $h_t=R-\delta(\widehat\Gamma_{-t})=\kappa t+O(t^2)>0$。同一个装置属于半径 $R-h_t$ 的校准球，因此

$$
\mathscr K(R-h_t)\ge1+\csc^2t,
\qquad
\liminf_{t\downarrow0}h_t^2\mathscr K(R-h_t)
\ge\kappa^2=\frac{1+\sqrt5}{32}>0.
\tag{104.4}
$$

第 89.1 条已证明实际最坏值具有正首系数和某个 $1\le p\le2$ 的有理幂主项。若 $p<2$，式（104.4）的左侧将为零，矛盾。故 $p=2$，并给首系数下界；第 89.2 条给 $c\le1/(1-R)$。代回既有主项便得式（104.2）。$\square$

这一步履行了第 95.8 式此前留下的条件：旋转从已证明最近的失效装置出发，完整距离一阶向内，谱泄漏二阶开启。它没有要求这条显式旋转族在每个子临界半径上都恰好最优，首系数 $c$ 的精确值仍未确定。

**推论 104.2（最近失效的慢质量及固定分位数）。** 第 97.1 条中，任一最近失效极限都满足 $F_*=P_*$，故其慢等待权重准确为

$$
\alpha=\operatorname{Tr}(\rho_*P_*).
\tag{104.5}
$$

对第 99.2 条的任意实际最优选择与固定 $0<\tau<1$，

$$
Q_{\tau,j}\sim[-\log(1-\tau)]c\,(R-u_j)^{-2}.
\tag{104.6}
$$

证明。推论 102.2 给最近失效的未点击映射 $X\mapsto P_*XP_*$，其伴随从 $I$ 迭代一步后即为 $P_*$，因此 $F_*=P_*$。分位式由第 99.2 条代入 $p=2$。$\square$

## 105. 精确阈值来自共同检验，临界指数来自距离与泄漏的不同阶

**关系结论 105.1（两份精确关系的连接）。** 全局失效半径与局部等待发散由不同的证明义务控制。第 101 节构造的同一参考输入及同一负谱检验，使未知相干项对该检验期望的贡献全部为零；剩余参数贡献具有正确的非负号。第 102 节再用三个覆盖全部暗态参数的区间，证明显式候选确实达到全局最小失效距离。

随后，第 103—104 节在该真正的边界点上连接

$$
R-\delta(\widehat\Gamma_{-t})\sim\kappa t,
\qquad
1-r(\widehat\Gamma_{-t})\sim t^2,
\qquad
M(\widehat\Gamma_{-t})\sim t^{-2}.
$$

本批的“AHH”是：一个保留参考关系的检验，能把原本未知的整个相干参数族压成同一个可证下界；找到真实边界以后，校准距离的一阶改变与生存泄漏的二阶改变，共同决定二次等待发散。这里的“消去”是实际检验对矩阵项正交，不是把这些相干关系从模型中删去。

**来源与未决边界 105.2。** 完整量子通道的后处理收缩、纯参考输入表征和秩二 Hermitian 谱计算沿用第 73、81、87 节核对的 Watrous 来源。第 101.6—101.15 式及第 102.3 式是当前仪器任务的具体纸面检验与代数推导；第 103 节继续对完整参考输入取最大值，第 104 节复用已经建立的临界主项定理。它们不把有限数值优化、离散参数扫描或求解器状态当作全局证明，不主张文献原创性。

精确半径与指数现由本批证明给出；本批尚未确定首系数 $c$ 的精确值，也未给出全部原始点击后继的最近失效分类或每个子临界半径的最优装置。第 102.2 条只分类未点击分支及重置后的完整装置，不能把该后处理的结果当成原接口的全部分类。所有结论继续限于本文固定名义装置、完整二维活动记忆和每轮重复同一实际仪器。全部新增仍为纯理论 Markdown，未新增或编译 Lean，未进入消化、覆盖或冻结链。

## 追加锚（本行以下为增补区）

## 106. 最近失效装置的完整分支映射构成一圈平衡投影

**定理 106.1（保留原始点击后继的最近失效分类）。** 对定义 87.1 的原名义仪器和完整二维接口，最近失效集合准确为

$$
\boxed{
\mathfrak F_R=
\{\Gamma_\vartheta^{\rm eq}:\vartheta\in\mathbb R/(2\pi\mathbb Z)\},
}
\tag{106.1}
$$

其中

$$
\psi_\vartheta=\frac{|0\rangle+e^{i\vartheta}|1\rangle}{\sqrt2},
\quad P_\vartheta=|\psi_\vartheta\rangle\langle\psi_\vartheta|,
$$

$$
\mathcal N_\vartheta^{\rm eq}(X)=P_\vartheta XP_\vartheta,
\qquad
\mathcal C_\vartheta^{\rm eq}(X)
=\operatorname{Tr}[(I-P_\vartheta)X]P_0.
\tag{106.2}
$$

该分类按实际 CP 分支映射成立，不分类实现同一映射的内部 Kraus 表示或环境搭建。它补足第 105.2 条未给出的原始点击后继分类。

证明。推论 102.2 已证明：每个最近失效装置的暗态平衡，且原始未点击分支就是 $X\mapsto P_\psi XP_\psi$。以计算基对角酉变换对齐相位，可令 $\psi=|+\rangle$；该变换保持名义仪器及完整距离，也保持 $P_0$。

完整性使点击效果恰为 $P_\eta=I-P_\psi$。取任一点击 Kraus 表示 $\mathcal C(X)=\sum_j B_jXB_j^\dagger$。因

$$
\sum_j\|B_j\psi\|^2
=\langle\psi|P_\eta|\psi\rangle=0,
$$

每个 $B_j$ 都消去 $\psi$，故 $B_j=|v_j\rangle\langle\eta|$。因此存在迹一正算子 $\tau=\sum_j|v_j\rangle\langle v_j|$，使

$$
\mathcal C(X)=\operatorname{Tr}(P_\eta X)\tau.
\tag{106.3}
$$

现在对这个原始点击输出使用第 101 节的同一个联合输入和负谱检验，取 $a=1/2,z=z_0=\phi/2$。与重置后的 $\Gamma_+$ 相比，未点击块完全相同，点击块只增加

$$
w|0_R\rangle\langle0_R|\otimes(\tau-P_0),
\qquad w=\frac12(1-z_0)>0.
$$

原检验 $E_C$ 支撑在参考系统张量量子输出 $|0\rangle$ 的空间内，且
$h_C=\langle0_R0|E_C|0_R0\rangle>0$。所以同一个负谱检验给

$$
\delta(\Gamma)
\ge R+w h_C\bigl(1-\langle0|\tau|0\rangle\bigr).
\tag{106.4}
$$

最近失效要求左侧恰为 $R$。正性和迹一保证括号非负，因 $w h_C>0$，只能有 $\langle0|\tau|0\rangle=1$，从而 $\tau=P_0$。撤销相位对齐得到式（106.2）。

反过来，每个式（106.2）都是 $\Gamma_+$ 的计算基对角相位共轭，故具有相同的完整距离 $R$，并固定 $P_\vartheta$ 而永久未点击。它们全部属于 $\mathfrak F_R$。不同相位模 $2\pi$ 给不同的 $P_\vartheta$；而未点击效果就是 $P_\vartheta$，所以不同参数确实给不同分支映射。$\square$

**推论 106.2（边界本身的有限事件律只有第一轮点击）。** 从初态 $\rho$ 在 $\Gamma_\vartheta^{\rm eq}$ 上运行，令 $\alpha=\operatorname{Tr}(\rho P_\vartheta)$。则

$$
\Pr(\mathsf N=1)=1-\alpha,\qquad
\Pr(2\le\mathsf N<\infty)=0,\qquad
\Pr(\mathsf N=\infty)=\alpha.
\tag{106.5}
$$

在正概率的点击分支上，量子后继为 $P_0$；在正概率的未点击分支上，后继为 $P_\vartheta$，以后一直未点击。

证明。式（106.2）直接给第一次两分支为 $(1-\alpha)P_0$ 与 $\alpha P_\vartheta$，且 $\mathcal N_\vartheta^{\rm eq}(P_\vartheta)=P_\vartheta$、$\mathcal C_\vartheta^{\rm eq}(P_\vartheta)=0$。$\square$

该边界律与第 97 节的临界逼近不同：每个子临界装置仍最终点击，趋向永久保留的质量在逼近中形成长尾。直接将边界的无穷等待换成一个有限点击轮数，会丢掉这一极限次序。

## 107. 同一子临界校准球内，可以改变点击后继而保持全部等待律

**定义 107.1（未点击动力学相同的后继参数族）。** 固定 $a>0$，取充分小的 $t>0$，令

$$
\psi=|+\rangle,\quad P=|\psi\rangle\langle\psi|,
\quad \eta=\frac{-|0\rangle+|1\rangle}{\sqrt2},
\quad \psi_t=\cos t\,\psi-\sin t\,\eta,
\quad S_t=|\psi_t\rangle\langle\psi_t|,
\quad k_t=at^2<1.
$$

对任意密度矩阵 $\tau$，定义

$$
\boxed{
\begin{aligned}
\mathcal N_t(X)&=(1-k_t)\operatorname{Tr}(PX)S_t,\\
\mathcal C_t^\tau(X)&=
\operatorname{Tr}[(I-P)X]P_0+k_t\operatorname{Tr}(PX)\tau,
\qquad \Gamma_t^\tau=(\mathcal N_t,\mathcal C_t^\tau).
\end{aligned}
}
\tag{107.1}
$$

$\tau$ 是装置参数，每次执行前固定；不是观察者取得的额外结果。实际记录仍只有未点击与点击。点击 CP 映射的两项也未被声明为可读取的两个记录标签。

令

$$
r_t=(1-k_t)\cos^2t,\qquad
\epsilon_t=1-r_t
=k_t+(1-k_t)\sin^2t>0,
\tag{107.2}
$$

并记第 103 节不附加 $k_t$ 分支的向内旋转仪器为 $\widehat\Gamma_{-t}$。取共同校准半径

$$
u_t=\delta(\widehat\Gamma_{-t})+k_t.
\tag{107.3}
$$

这里 $u_t$ 随 $t$ 变化，不是一个固定的子临界常数。

**定理 107.2（共同合法性、完整距离与全部来源的相同等待）。** 对充分小的 $t>0$，定义 107.1 的全部 $\Gamma_t^\tau$ 都是同接口完整仪器，并同时属于 $\mathfrak B_{u_t}$，其中

$$
u_t=R-\kappa t+O(t^2)<R,
\qquad \kappa=\frac{\sqrt\phi}{4}.
\tag{107.4}
$$

它们都对全部初态终止，并且对任意两个后继参数

$$
\boxed{
\frac12\|\Gamma_t^\tau-\Gamma_t^{\tau'}\|_\diamond
=k_tD(\tau,\tau'),
\qquad D(\tau,\tau')=\frac12\|\tau-\tau'\|_1.
}
\tag{107.5}
$$

若 $p=\operatorname{Tr}(\rho P)$，则每个 $\tau$ 给完全相同的首次点击概率：

$$
\begin{aligned}
\Pr_\rho(\mathsf N=1)&=1-(1-k_t)p,\\
\Pr_\rho(\mathsf N=n)&=(1-k_t)p\,\epsilon_t r_t^{n-2}\quad(n\ge2),\\
\mathbb E_\rho\mathsf N&=1+\frac{(1-k_t)p}{\epsilon_t},\qquad
M_t=1+\frac{1-k_t}{\epsilon_t}.
\end{aligned}
\tag{107.6}
$$

从准平稳态 $S_t$ 出发，等待准确服从 $\operatorname{Geom}(\epsilon_t)$。所有这些时间律都不含 $\tau$。

证明。各分支是完全正的测量制备映射，其效果分别为 $(1-k_t)P$ 与 $I-(1-k_t)P$，总和为 $I$，得到完整性。未点击映射为秩一超算子，非零特征值为 $r_t<1$，所以全部初态终止。

与 $\widehat\Gamma_{-t}$ 相比，未点击块减少 $k_t\operatorname{Tr}(PX)S_t$，点击块增加 $k_t\operatorname{Tr}(PX)\tau$。对任意带参考的归一化联合输入 $\omega\succeq0$、$\operatorname{Tr}\omega=1$，定义未归一化参考态

$$
\omega_R^P=(I_R\otimes\langle\psi|)\omega
(I_R\otimes|\psi\rangle)\succeq0,
\qquad\operatorname{Tr}\omega_R^P\le1.
$$

两块之差分别为 $-k_t\omega_R^P\otimes S_t$ 与 $k_t\omega_R^P\otimes\tau$。记录正交使其半迹范数为 $k_t\operatorname{Tr}\omega_R^P\le k_t$，由输入 $P$ 达到。因此

$$
\frac12\|\Gamma_t^\tau-\widehat\Gamma_{-t}\|_\diamond=k_t.
$$

三角不等式给 $\delta(\Gamma_t^\tau)\le u_t$，且这个上界对全部 $\tau$ 同时成立。定理 103.2 给式（107.4）。比较 $\tau,\tau'$ 时未点击块相同，点击块差为 $k_t\omega_R^P\otimes(\tau-\tau')$；取范数并再次用输入 $P$ 达到上界，得到式（107.5）。

直接迭代得

$$
\mathcal N_t^n(\rho)=(1-k_t)p\,r_t^{n-1}S_t
\qquad(n\ge1).
$$

取迹得到生存概率，作相邻差及尾和得到式（107.6）。最大值由 $p=1$ 的初态 $P$ 取得。对 $S_t$，未点击后仍为 $S_t$，且单轮生存概率为 $r_t$，所以等待为准确几何律。$\square$

相同时间律并不只针对一份准备态。首次点击效果由共同未点击映射与共同点击效果确定，所以全部来源乃至保留参考系统而丢弃点击量子后继的时间记录通道都相同。$\tau$ 的区别位于仍可读取的量子后继中。

## 108. 完整等待记录相同，最终量子后继仍保持有限差异

**定义 108.1（终端量子通道与有限停止输出）。** 对定义 107.1 的装置，忽略点击轮数但保留点击后的量子系统，定义

$$
\Xi_t^\tau(X)=\sum_{n\ge1}
\mathcal C_t^\tau\mathcal N_t^{n-1}(X).
\tag{108.1}
$$

所有初态终止且尾部几何衰减，故该有限维输入输出的级数在算子范数中收敛，并定义 CPTP 通道。另用 $\Omega_m^{t,\tau}$ 表示第 35 节的有限停止通道：保留每个首次点击轮数及量子后继，并保留截至 $m$ 轮尚未点击的块。

**定理 108.2（有限停止输出与终端输出的精确距离）。** 对每个密度矩阵 $\rho$，置 $p=\operatorname{Tr}(\rho P)$。有

$$
\boxed{
\Xi_t^\tau(\rho)
=\left(1-\frac{k_t p}{\epsilon_t}\right)P_0
+\frac{k_t p}{\epsilon_t}\tau.
}
\tag{108.2}
$$

并且，对每个 $m\ge1$，包含任意参考输入的完整距离准确为

$$
\boxed{
\begin{aligned}
\frac12\|\Omega_m^{t,\tau}-\Omega_m^{t,\tau'}\|_\diamond
&=\frac{k_t(1-r_t^m)}{\epsilon_t}D(\tau,\tau'),\\
\frac12\|\Xi_t^\tau-\Xi_t^{\tau'}\|_\diamond
&=\frac{k_t}{\epsilon_t}D(\tau,\tau').
\end{aligned}
}
\tag{108.3}
$$

输入 $P$ 同时达到这两条等式。当 $t\downarrow0$ 时，

$$
\frac{k_t}{\epsilon_t}\longrightarrow\frac a{1+a}>0,
\qquad
\frac12\|\Gamma_t^\tau-\Gamma_t^{\tau'}\|_\diamond
\longrightarrow0.
\tag{108.4}
$$

证明。未点击后的 $P$ 占据满足

$$
\operatorname{Tr}[P\mathcal N_t^{n-1}(X)]
=r_t^{n-1}\operatorname{Tr}(PX)
\qquad(n\ge1).
\tag{108.5}
$$

所以每个首次点击分支中，含 $\tau$ 的项准确为
$k_t r_t^{n-1}\operatorname{Tr}(PX)\tau$。当 $X\succeq0$ 时，其余点击项均为 $P_0$ 的非负倍数。几何求和与总迹一给式（108.2）；$k_t\le\epsilon_t$ 保证它是概率凸组合。

对任意带参考输入，两个装置的第 $n$ 个点击块之差准确为

$$
k_t r_t^{n-1}\omega_R^P\otimes(\tau-\tau').
$$

截至 $m$ 轮尚未点击的块完全相同。不同轮数记录正交，因此半迹范数相加为

$$
\frac{k_t(1-r_t^m)}{\epsilon_t}
\operatorname{Tr}(\omega_R^P)D(\tau,\tau').
$$

参考态的迹至多一，输入 $P$ 取得一，得到第一条距离等式。终端通道之差由式（108.2）直接得到相同形式，只将有限几何和换成 $1/\epsilon_t$，给第二条等式。

最后，$k_t=at^2$，而
$\epsilon_t=at^2+(1-at^2)\sin^2t=(1+a)t^2+O(t^4)$，故式（108.4）成立。$\square$

**推论 108.3（只使用全部时间记录也不能普适恢复点击后继）。** 取 $\tau=P_0$、$\tau'=P_1$，并固定共同初态 $P$。两模型的全部首次点击时间律完全相同；任何仅接收这些时间记录、使用同一规则的后处理，输出的平均恢复态只能是同一个 $\sigma_t$。因此

$$
\boxed{
\max\{D(\sigma_t,\Xi_t^{P_0}(P)),
D(\sigma_t,\Xi_t^{P_1}(P))\}
\ge\frac{k_t}{2\epsilon_t}
\longrightarrow\frac a{2(1+a)}.
}
\tag{108.6}
$$

此不可恢复性也适用于已经精确知道全部来源的时间概率，而没有取得区分 $\tau$ 的其他读数的情形。

证明。两个恢复任务提供相同的输入记录分布；相同后处理因而产生相同平均态。定理 108.2 给两个目标态距离 $k_t/\epsilon_t$；迹距离三角不等式迫使至少一个误差不小于其一半。全部来源的时间律仍不含 $\tau$，所以给出更多同类精确概率也不能区分这两个装置。$\square$

这一结论没有否定完整单轮仪器校准。两个仪器的完整单轮距离确实可读且趋零；不一致来自临界附近越来越长的执行，将小的分支后继差异累积成有限的最终区别。

**定理 108.4（相同临界装置和时间律下，终端态可趋向任意预定量子态）。** 在式（107.1）的同一分支构造中，另取 $\widetilde k_t=t^{3/2}$，记得到的装置为 $\widetilde\Gamma_t^\tau$，以及

$$
\widetilde\epsilon_t=\widetilde k_t+(1-\widetilde k_t)\sin^2t,
\qquad
\widetilde u_t=\delta(\widehat\Gamma_{-t})+\widetilde k_t.
$$

对充分小的 $t>0$，所有预先固定的密度矩阵参数 $\tau$ 同时满足

$$
\widetilde\Gamma_t^\tau\in\mathfrak B_{\widetilde u_t},
\qquad \widetilde u_t=R-\kappa t+o(t)<R,
\qquad \widetilde\Gamma_t^\tau\longrightarrow\Gamma_+.
\tag{108.7}
$$

它们对全部初态具有相同的首次点击时间律；但对共同初态 $P$，其终端通道满足

$$
\boxed{
\widetilde\Xi_t^\tau(P)\longrightarrow\tau
\quad\text{且该收敛对全部密度矩阵 }\tau\text{ 一致}.
}
\tag{108.8}
$$

特别地，取 $\tau=P_0,\tau'=P_1$，单轮完整距离为 $t^{3/2}\to0$，终端输出距离却趋于一；只用共同时间记录作恢复的最坏半迹距离误差下界趋于 $1/2$。

证明。式（107.1）的完全正性、完整性及第 107—108 节的有限几何求和，均只要求 $0<k_t<1$ 与 $r_t=(1-k_t)\cos^2t<1$；将 $k_t$ 换成 $\widetilde k_t$ 后同样成立。只有涉及参数阶数的渐近式需要重新计算。

由于 $t^{3/2}=o(t)$，与无附加分支的旋转仪器之完整距离准确为 $\widetilde k_t$，所以定理 103.2 给式（108.7）的共同半径及装置极限。另一方面，$\sin^2t=o(\widetilde k_t)$，故

$$
\widetilde w_t:=\frac{\widetilde k_t}{\widetilde\epsilon_t}
=\left[1+\frac{(1-\widetilde k_t)\sin^2t}{\widetilde k_t}\right]^{-1}
\longrightarrow1.
$$

终端态准确为 $(1-\widetilde w_t)P_0+\widetilde w_t\tau$，所以

$$
D(\widetilde\Xi_t^\tau(P),\tau)
=(1-\widetilde w_t)D(P_0,\tau)
\le1-\widetilde w_t\longrightarrow0,
$$

其界不依赖 $\tau$。两端点的距离及恢复误差结论分别由同一距离公式与三角不等式得到。$\square$

这里没有从相同记录中恢复不同的未知态。不同的 $\tau$ 是事先指定的不同仪器；它们给出相同的时间读数，却把不同的量子状态交给未来。相同的临界装置极限也没有使这些终端通道趋于同一个通道，因为终端化包含越来越长的实际执行。

## 109. 活动质量加权的停止误差界，其系数一不能统一降低

**定理 109.1（同接口量子仪器中停止界的渐近锐常数）。** 固定 $a>0$，使用定义 107.1 的两装置 $\Gamma_t^{P_0},\Gamma_t^{P_1}$ 与共同初态 $P$。记其完整单轮距离为 $d_t=k_t$，共同均值为 $M_t$。则

$$
\boxed{
\frac{D(\Xi_t^{P_0}(P),\Xi_t^{P_1}(P))}{d_tM_t}
=\frac1{1+(1-k_t)\sin^2t}
\longrightarrow1.
}
\tag{109.1}
$$

而且，第 63.1 条保留全部有限停止记录和后继的界中，乘在 $d_t\min(c_m^I,c_m^J)$ 前面的系数一也不能被某个统一的更小正数替代。

证明。由式（107.6）与（108.3），分子为 $k_t/\epsilon_t$，分母为
$k_t[1+(1-k_t)/\epsilon_t]$。相除得到

$$
\frac1{\epsilon_t+1-k_t}
=\frac1{1+(1-k_t)\sin^2t},
$$

从而成立式（109.1）。

对有限截断，两个装置在同一来源上的活动成本均为

$$
c_m=\mathbb E_P\min(\mathsf N,m)
=1+\frac{(1-k_t)(1-r_t^{m-1})}{\epsilon_t}
\qquad(m\ge1).
\tag{109.2}
$$

取 $m_t=\lceil\epsilon_t^{-2}\rceil$，则 $r_t^{m_t}\to0$，同时

$$
\frac{D(\Omega_{m_t}^{t,P_0}(P),\Omega_{m_t}^{t,P_1}(P))}
{d_t c_{m_t}}
=\frac{1-r_t^{m_t}}
{\epsilon_t+(1-k_t)(1-r_t^{m_t-1})}
\longrightarrow1.
\tag{109.3}
$$

这里 $d_t c_{m_t}\to a/(1+a)<1$，所以第 63.1 条与一取最小值的上限没有遮住该比例。任取统一常数 $c_0<1$，充分小的 $t$ 都使式（109.3）的比例大于 $c_0$，由实际有限停止输出直接推翻该替换。$\square$

**推论 109.2（共同半径趋近失效阈值是必要的范围条件）。** 第 108 节的非零极限使用随 $t$ 变化且趋于 $R$ 的共同半径 $u_t$。在任何预先固定的 $u<R$ 内，若两完整仪器的单轮距离趋零，则其在共同来源上的最终记录后继距离也趋零，并有统一上界

$$
D(\text{最终完整输出}_I,\text{最终完整输出}_J)
\le d(I,J)\mathscr K(u).
\tag{109.4}
$$

该上界包含有限参考输入；丢弃事件时间后，对终端量子通道同样成立。

证明。第 80 节使整个固定球上的均值统一不超过有限的 $\mathscr K(u)$。第 63.1 条于是对每个有限 $m$ 给 $d(I,J)\mathscr K(u)$。把各有限停止输出嵌入同一个由未解决标签与全部有限轮数标签组成的可数记录空间。有限前缀与最终完整输出的差只涉及未解决质量和相应未来记录；其半迹范数等于该生存概率。两过程都全状态终止，故这些概率趋零，取极限得式（109.4）。带参考时活动概率由系统边缘决定，具有同一均值上界。最后使用偏迹收缩。$\square$

**推论 109.3（原半径 $4/5$ 的明确预算可降至 4744 以下）。** 在原名义仪器的半径 $u=4/5$ 内，每个完整仪器及每个初态都满足

$$
\boxed{\mathbb E_\rho^\Gamma\mathsf N
\le\mathscr K(4/5)<4744.}
\tag{109.5}
$$

证明。定理 102.1 给精确 $R$。因为

$$
5\cdot25000^2-55889^2=1419679>0,
$$

有 $\sqrt5>55889/25000$，从而

$$
R^2-\left(\frac{333}{400}\right)^2
=\frac{25000\sqrt5-55889}{160000}>0.
$$

因此 $R>333/400$，$g=R-4/5>13/400$。沿用第 83.3 条的同一成本界，

$$
\mathscr K(4/5)
\le10+\frac5{g^2}
<10+\frac{800000}{169}
=\frac{801690}{169}<4744.
$$

证毕。

这是从已经求出的阈值复用原预算公式得到的保证；不是对最优成本的精确计算，也不把调用轮数换成秒数。它加强第 85.3 条的数值上界，不改写或否定该条原有较宽的保证。

## 110. 时间记录与量子后继的差别可以在同一个真实过程内分离

**关系结论 110.1（同一时间律并不确定同一后继关系）。** 第 106 节完成了最近失效装置按完整分支映射的分类。第 107—109 节随后保留同一活动空间、同一未点击映射和同一来源，把点击后的量子状态作为唯一可变参数。由此得到

$$
\boxed{
\text{全部来源的首次点击时间律相同}
\quad\text{而}\quad
\text{点击后的完整量子作用不同}.
}
$$

本批的“AHH”在于：记录告诉我们事件何时发生，还必须保留事件把什么状态交给下一次续接。第 108.4 条甚至允许终端态趋向任意预定密度矩阵，同时保持全部时间律相同和同一个临界装置极限。这里两份单轮完整仪器越来越接近，执行中的时间记录却始终完全相同；不断增长的等待把量子后继中每轮很小的差别累积到有限大小。式（109.3）进一步说明，这份累积准确达到活动质量加权误差界的首项，而非只给一个抽象的不充分性反例。

**来源与边界 110.2。** 本批复用第 101—103 节的同一参考检验、精确失效半径及向内距离导数，并把第 35、63 节的停止通道与活动质量界应用于可逐项求和的同接口仪器族。完全正测量制备映射、迹距离收缩与带参考输入的通道距离仍沿用已核对的 Watrous 来源。第 106.4、107.5、108.3、109.3 式展示本批所需的具体连接，不主张文献原创性。

共同半径 $u_t$ 必须随参数趋近 $R$；固定子临界球内仍有式（109.4）的统一连续性。后继参数族不被宣称为每个球内的精确最坏装置，首系数 $c$ 的精确值与全部子临界最优装置仍未确定。本批未添加可读取的内部 Kraus 标签，也未把单轮仪器的分类当成内部实现的唯一性。所有新增仍为纯理论 Markdown，未新增或编译 Lean，未进入消化、覆盖或冻结链。

## 追加锚（本行以下为增补区）

## 111. 当前准平稳态的本征基给出一般仪器的泄漏正规形

本批继续限定于定义 87.1 的原名义装置、完整二维活动记忆、两种记录和每轮重复同一实际仪器。第 104 节已经确定最坏均值按距离间隙的负二次幂发散，但只给首系数的上下界。以下把该首系数准确求出；第 105.2、110.2 条关于首系数未定的边界由本批补足，原有上下界仍成立。

**定义 111.1（以真实准平稳态选择坐标）。** 对最近失效集合附近的任一不失效仪器 $\Gamma=(\mathcal N,\mathcal C)$，沿用定理 96.2 的实际准平稳态与主特征值：

$$
\mathcal N(\sigma)=(1-\epsilon)\sigma,
\qquad \operatorname{Tr}\sigma=1,\qquad \epsilon>0.
\tag{111.1}
$$

在充分小的共同邻域内，$\sigma$ 的最大本征值简单。令其谱分解为

$$
\sigma=(1-y)P+yP_\eta,
\qquad P=|\psi\rangle\langle\psi|,
\qquad P_\eta=I-P,
\qquad 0\le y<\frac12.
\tag{111.2}
$$

同时作输入输出的计算基对角酉共轭，可以令

$$
\psi=\sqrt a\,|0\rangle+\sqrt b\,|1\rangle,
\qquad \eta=-\sqrt b\,|0\rangle+\sqrt a\,|1\rangle,
\qquad b=1-a.
$$

该变换保持名义仪器和完整距离。趋近最近失效集合时，$a\to1/2$、$y\to0$，相位对齐后的未点击映射趋向 $X\mapsto P_+XP_+$。

取任意有限 Kraus 表示，在这份当前本征基中写成

$$
A_j=\begin{pmatrix}c_j&b_j\\ f_j&a_j\end{pmatrix}.
\tag{111.3}
$$

这里不要求 $f_j=0$。定义与该表示的选择无关的 Gram 量

$$
C=\sum_j|c_j|^2,\quad
\beta=\sum_j|b_j|^2,\quad
F=\sum_j|f_j|^2,\quad
v=\sum_j|a_j|^2,
$$

$$
g=\sum_j\overline{c_j}b_j,\qquad
h=\sum_j\overline{c_j}f_j,\qquad
\ell_\psi=1-C,
\qquad E=I-\sum_jA_j^\dagger A_j=\mathcal C^*(I)\succeq0.
\tag{111.4}
$$

以下 $o(1)$ 指不失效装置趋近整个最近失效紧集的共同极限，不仅指某条预选旋转路径。

**引理 111.2（准平稳方程压低一项潜在的一阶相干）。** 在上述范围内，准确地有

$$
\begin{aligned}
\epsilon&=\operatorname{Tr}(E\sigma),&
y\operatorname{Tr}E&\le\epsilon,\\
\ell_\psi&=\epsilon+\frac{y\beta}{1-y},&
h&=-\frac y{1-y}\sum_j\overline{b_j}a_j,\\
0\le F&\le\ell_\psi,&
|g|&\le\sqrt{(\ell_\psi-F)(1-\beta-v)}+\sqrt{Fv}.
\end{aligned}
\tag{111.5}
$$

因此，趋近最近失效集合时，

$$
\boxed{
\begin{gathered}
y=O(\epsilon),\qquad
\ell_\psi=\epsilon(1+o(1)),\qquad F=O(\epsilon),\\
\beta,v\to0,\qquad
|h|=O(\epsilon)\sqrt{\beta v},\qquad
|g|\le(1+\sqrt v)\sqrt{\ell_\psi}.
\end{gathered}}
\tag{111.6}
$$

证明。对式（111.1）取迹，使用完整性得到第一条恒等式。又有 $\sigma\succeq yI$，故正算子 $E$ 给 $\epsilon\ge y\operatorname{Tr}E$。

取式（111.1）的 $\psi$ 对角元与 $\eta,\psi$ 非对角元，分别得到

$$
(1-\epsilon)(1-y)=(1-y)C+y\beta,
\qquad
0=(1-y)\sum_j\overline{c_j}f_j
+y\sum_j\overline{b_j}a_j.
$$

整理得到 $\ell_\psi$ 与 $h$ 的两条恒等式。完整性还给

$$
E=
\begin{pmatrix}
\ell_\psi-F&-g-\sum_j\overline{f_j}a_j\\
-\overline g-\sum_j\overline{a_j}f_j&1-\beta-v
\end{pmatrix}\succeq0.
$$

其对角元非负，二阶行列式非负，再用 Cauchy–Schwarz，便有

$$
\left|g+\sum_j\overline{f_j}a_j\right|^2
\le(\ell_\psi-F)(1-\beta-v),
\qquad
\left|\sum_j\overline{f_j}a_j\right|\le\sqrt{Fv}.
$$

这证明式（111.5）及 $|g|$ 的后一上界。

定理 96.2 和推论 102.2 给共同边界极限 $\sigma\to P_*$、$\mathcal N\to P_*({\cdot})P_*$。例如

$$
\beta=\langle\psi|\mathcal N(P_\eta)|\psi\rangle,
\quad
v=\langle\eta|\mathcal N(P_\eta)|\eta\rangle,
\quad
C=\langle\psi|\mathcal N(P)|\psi\rangle,
$$

故 $\beta,v\to0$、$C\to1$，同时 $\operatorname{Tr}E\to1$。这些都是映射的矩阵元，不要求固定 Kraus 个数或选取连续的 Kraus 算子。因此 $y\le\epsilon/\operatorname{Tr}E=O(\epsilon)$，再代入已证恒等式得到 $\ell_\psi/\epsilon\to1$、$F=O(\epsilon)$ 及 $h$ 的界。紧性和这些矩阵元的连续性使估计在整个最近失效集合附近一致。$\square$

这个坐标选择有实际作用：单靠完整性只能把某些相干项控制到 $\sqrt\epsilon$ 阶；当前准平稳方程使 $h$ 降至 $O(\epsilon)\sqrt{\beta v}$。它没有宣称每个 $f_j$ 单独消失，也没有把混合准平稳态换成纯态来证明。

## 112. 同一个负谱检验给出距离下降与谱泄漏之间的锐系数

**定义 112.1（在当前主本征态上放置参考检验）。** 在定义 111.1 的相位对齐坐标下，取第 101 节的实际输入 $\Omega_z$，固定

$$
z=z_0=\frac\phi2,\qquad \phi=\frac{1+\sqrt5}{2}.
$$

仍用该节同一投影仪器相对名义仪器的负谱投影 $E_N,E_C$、函数 $L(a,z)$ 及标量 $\chi,\nu,T,h_N,h_C$。写 $E_C=E_C^R\otimes P_0$，置

$$
\alpha_R=\sqrt{a(1-z)}|0_R\rangle+\sqrt z|1_R\rangle,
\qquad \beta_R=-\sqrt{b(1-z)}|0_R\rangle,
$$

$$
v_c=\alpha_R\otimes\psi,\quad
v_b=\beta_R\otimes\psi,\quad
v_f=\alpha_R\otimes\eta,\quad
v_a=\beta_R\otimes\eta,
\qquad
H=E_C^R\otimes I-E_N.
\tag{112.1}
$$

令 $H_{ij}=\langle v_i|H|v_j\rangle$。这些量在 $a=1/2$ 附近连续、有界且为实数，因为全部检验矩阵和向量在上述坐标中为实。

**引理 112.2（剩余一阶方向的系数准确为 $\kappa$）。** 在 $a=1/2$ 的一个共同邻域内，有

$$
H_{ca}=H_{ba}=0,\qquad
H_{bb}=b(1-z)(h_C-h_N)\ge0,\qquad
H_{aa}=b(1-z)h_C>0,
\tag{112.2}
$$

以及

$$
H_{cb}
=-\sqrt{ab}(1-z)
\left[h_C+\frac z\chi+\frac{T-\nu}{2\nu}\right].
\tag{112.3}
$$

特别地，令 $\kappa=\sqrt\phi/4$，则

$$
\boxed{H_{cb}(1/2,z_0)=-\frac{\sqrt\phi}{8}=-\frac\kappa2.}
\tag{112.4}
$$

证明。第 101.11 式给 $E_Nv_a=0$。而 $E_C^R\otimes I$ 的 $\psi,\eta$ 交叉矩阵元为零，故得到两个零系数；两个对角系数由定义直接得到。对充分接近 $1/2$ 的 $a$，第 101.4 式的条件成立，因此第 101.15 式保证 $h_C-h_N\ge0$，且连续性保证 $h_C>0$。

点击块的二维负谱投影满足

$$
\langle0_R|E_C^R|1_R\rangle
=\frac{\sqrt{az(1-z)}}\chi.
$$

于是

$$
\langle v_c|(E_C^R\otimes I)|v_b\rangle
=-\sqrt{ab}(1-z)\left(h_C+\frac z\chi\right).
$$

对未点击检验，$v_c=u$，$v_b=-\sqrt{b(1-z)}|0_R\psi\rangle$。沿用第 101 节负本征值 $\lambda_-=(a-\nu)/2$ 及其投影，可得

$$
\langle u|E_N|v_b\rangle
=-\frac{\sqrt{ab}(1-z)}{\lambda_-}
\langle u|E_N|u\rangle
=\frac{\sqrt{ab}(1-z)(T-\nu)}{2\nu}.
$$

两项相减便是式（112.3）。在平衡点，

$$
\chi=\frac{\sqrt\phi}{2},\qquad
\nu=\frac{\phi^{3/2}}2,\qquad
T=\frac{\phi^2}2,\qquad
h_C=\frac{1-\phi^{-3/2}}2.
$$

代入后得到

$$
H_{cb}
=-\frac{(2-\phi)(3\sqrt\phi-\phi^{-3/2})}{8}
=-\frac{\sqrt\phi}{8},
$$

最后一步使用 $2-\phi=\phi^{-2}$ 与 $\phi^4=3\phi+2$。$\square$

**定理 112.3（一般子临界方向的锐距离—泄漏上界）。** 对任意趋近最近失效集合的不失效仪器，有一致估计

$$
\boxed{
R-\delta(\Gamma)
\le\bigl(\kappa+o(1)\bigr)\sqrt{\epsilon_\Gamma}.
}
\tag{112.5}
$$

这里 $\delta$ 是保留参考输入、记录与量子后继的完整半钻石距离；该上界并不把允许仪器限制到单 Kraus、实数 Kraus、纯准平稳态或预先选定的旋转族。

证明。先将实际点击后继重置为 $P_0$。该后处理固定名义仪器，保持未点击映射、$\sigma$ 与 $\epsilon$，并只能减小 $\delta$。对重置后的装置使用定义 112.1 的同一个参考输入和两个负谱检验。

每个未点击 Kraus 算子的联合输出向量是

$$
c_jv_c+b_jv_b+f_jv_f+a_jv_a.
$$

若其联合未点击输出为 $Y$，则点击参考输出由完整性给成输入参考边缘减去 $\operatorname{Tr}_{\mathcal H}Y$，再张量 $P_0$。所以相对于投影仪器的联合未点击输出 $|v_c\rangle\langle v_c|$，整份负检验值的变化准确为

$$
\operatorname{Tr}\left[H\bigl(Y-|v_c\rangle\langle v_c|\bigr)\right].
$$

由于完整输出差的迹为零，这份负检验值不超过实际半迹范数。展开得到

$$
\begin{aligned}
\delta(\Gamma)\ge L(a,z)
&+(C-1)H_{cc}+\beta H_{bb}+F H_{ff}+vH_{aa}\\
&+2\operatorname{Re}\left[
H_{cb}g+H_{cf}h
+H_{ca}\sum_j\overline{c_j}a_j
+H_{bf}\sum_j\overline{b_j}f_j\right.\\
&\hspace{39mm}\left.
+H_{ba}\sum_j\overline{b_j}a_j
+H_{fa}\sum_j\overline{f_j}a_j
\right].
\end{aligned}
\tag{112.6}
$$

引理 112.2 使 $H_{ca},H_{ba}$ 两项恰为零，且 $\beta,v$ 对角项非负，可以在下界中舍去。其他系数一致有界。再由引理 111.2，

$$
|C-1|+F=O(\epsilon),\qquad
|h|=O(\epsilon)\sqrt{\beta v},
$$

$$
\left|\sum_j\overline{b_j}f_j\right|
\le\sqrt{\beta F}=o(\sqrt\epsilon),
\qquad
\left|\sum_j\overline{f_j}a_j\right|
\le\sqrt{Fv}=o(\sqrt\epsilon).
$$

因此全部可能降低检验值的剩余项中，只有 $H_{cb}g$ 还需保留到 $\sqrt\epsilon$ 阶，得到

$$
\begin{aligned}
\delta(\Gamma)
&\ge L(a,z_0)-2|H_{cb}(a,z_0)||g|-o(\sqrt\epsilon)\\
&\ge L(a,z_0)
-2|H_{cb}(a,z_0)|(1+\sqrt v)\sqrt{\ell_\psi}
-o(\sqrt\epsilon).
\end{aligned}
\tag{112.7}
$$

这里不需要知道 $a-1/2$ 相对 $\epsilon$ 的速度。因为 $a\to1/2$，第 102.4 式在同一个邻域内直接给 $L(a,z_0)\ge R$；引理 112.2 与 $\ell_\psi/\epsilon\to1$ 给

$$
2|H_{cb}(a,z_0)|(1+\sqrt v)\sqrt{\ell_\psi/\epsilon}
\longrightarrow\kappa.
$$

代入式（112.7）即得所需上界。上述估计由相位对齐后的映射矩阵元控制，未依赖 Kraus 表示的秩或选法。若一致性失败，可取一列反例，经最近失效紧集的收敛子列与相同相位对齐后，上述每一项仍给相同极限，矛盾。$\square$

## 113. 最坏等待律的临界首系数准确为黄金比例的十六分之一

**定理 113.1（最坏均值的精确主项）。** 在本批固定模型中，存在正整数 $m$，使

$$
\boxed{
\mathscr K(R-h)
=\frac{1+\sqrt5}{32}\,h^{-2}
\bigl(1+O(h^{1/m})\bigr)
\qquad(h\downarrow0).
}
\tag{113.1}
$$

因此第 104 节未定的首系数准确为

$$
\boxed{c=\kappa^2=\frac\phi{16}=\frac{1+\sqrt5}{32}.}
\tag{113.2}
$$

证明。第 104.1 条已给幂指数二和下界

$$
\liminf_{h\downarrow0}h^2\mathscr K(R-h)\ge\kappa^2.
$$

对每个充分小的 $0<h<R$，选择实际最大化仪器 $\Gamma_h\in\mathfrak B_{R-h}$，使 $M(\Gamma_h)=\mathscr K(R-h)$。第 88—93 节保证最大值取得，且这些最大化仪器趋近最近失效集合。令 $\epsilon_h=1-r(\Gamma_h)$。校准约束与定理 112.3 给

$$
h\le R-\delta(\Gamma_h)
\le(\kappa+o(1))\sqrt{\epsilon_h}.
$$

另一方面，第 93 节与推论 104.2 给一致的同装置关系

$$
\epsilon_h M(\Gamma_h)\longrightarrow1.
$$

于是

$$
h^2\mathscr K(R-h)
=\frac{h^2}{\epsilon_h}
\bigl[\epsilon_h M(\Gamma_h)\bigr]
\le(\kappa+o(1))^2(1+o(1)).
$$

与下界匹配得到式（113.2）。第 104.1 条已有的实代数主项展开再给式（113.1）的分数次余项；这里未声称已经确定最小可能的 $m$ 或次主项系数。$\square$

**推论 113.2（显式向内旋转在首阶达到全局最优）。** 对第 103 节的 $\widehat\Gamma_{-t}$，可以在充分小的 $h>0$ 下选择唯一小正角 $t(h)$，使

$$
\delta(\widehat\Gamma_{-t(h)})=R-h,
\qquad t(h)=\frac h\kappa+O(h^2).
$$

它的实际最大均值满足

$$
\boxed{
\frac{M(\widehat\Gamma_{-t(h)})}{\mathscr K(R-h)}\longrightarrow1.
}
\tag{113.3}
$$

证明。第 103 节给局部光滑距离及非零导数 $-\kappa$，反函数定理给所述 $t(h)$。该族的实际均值准确为 $1+\csc^2t$，所以

$$
M(\widehat\Gamma_{-t(h)})
=\kappa^2h^{-2}(1+O(h)).
$$

与定理 113.1 相除得到结论。$\square$

这里的“首阶最优”只指比例趋于一；它没有证明每个正 $h$ 上该旋转装置恰为全局最优，也没有分类全部达到相同首项的装置。

**推论 113.3（最优实际事件时间的系数也随之确定）。** 对每个充分小的 $0<h<R$ 选择任一最优仪器与其最优初态，令其实际首次点击轮数为 $\mathsf N_h$。则

$$
\boxed{
h^2\mathsf N_h\Rightarrow\kappa^2 Z,
\qquad Z\sim\operatorname{Exp}(1).
}
\tag{113.4}
$$

对每个固定实数 $s>0$，有

$$
h^{2s}\mathbb E\mathsf N_h^s
\longrightarrow\kappa^{2s}\Gamma_{\rm E}(s+1).
\tag{113.5}
$$

对每个固定 $0<\tau<1$，其下分位数满足

$$
q_\tau(h)\sim
\kappa^2[-\log(1-\tau)]\,h^{-2}.
\tag{113.6}
$$

证明。定理 99.1 与推论 99.2 已对任意实际最优选择给出 $\mathsf N_h/\mathscr K(R-h)\Rightarrow\operatorname{Exp}(1)$、全部固定正阶矩及固定分位数收敛。定理 113.1 给缩放因子 $h^2\mathscr K(R-h)\to\kappa^2$，代入这些已证关系便得到三式。$\square$

式（113.4）仍是离散等待的弱极限，不升级成与连续分布的总变差收敛。$h$ 是完整通道距离间隙，$\mathsf N_h$ 是实际调用轮数；本批没有另作物理钟标定。

## 114. 锐系数来自准平稳约束与同一检验的共同作用

**关系结论 114.1（AHH：决定主阶的坐标由当前过程自己选择）。** 失效边界的纯暗态只描述极限；临界附近实际装置可以有混合准平稳态和一般 Kraus 算子。直接把边界上的上三角形状套回这些实际装置，会遗漏 $f_j$。本批保留这些项，再用当前准平稳方程确定主本征基。为与第 113 节的距离间隙 $h$ 分开，将式（111.4）的相干量写成 $h_{\rm coh}=\sum_j\overline{c_j}f_j$，于是得到

$$
\boxed{
\text{当前准平稳方程}
\longrightarrow
h_{\rm coh}=O(\epsilon)\sqrt{\beta v}
\longrightarrow
R-\delta\le(\kappa+o(1))\sqrt\epsilon.
}
$$

同一参考检验使另两项精确消失、两项系数非负；剩下的唯一主阶下降系数与显式旋转族的 $\kappa$ 完全匹配。这使 $\epsilon M\to1$ 转化成全局首系数 $c=\kappa^2$，而不是仅给某个例子的二次等待。

**来源与边界 114.2。** 本批是第 91—104 节基础上的纸面综合推导：使用该卷已经给出的完全正分支表示、后处理收缩、准平稳谱投影、参考负谱检验与实代数主项；新增推导由正文展示的二维正矩阵约束、矩阵元恒等式及一致余项承担。量子通道和半钻石距离的基础仍沿用已列 Watrous 来源，实代数展开仍沿用已列 Basu 与 Bierstone–Milman 来源。不主张文献原创性，不以数值搜索或独立审阅代替数学证明，也不宣称本批已经编译为 Lean。

第 108 节的任意终端态构造仍成立；它没有要求达到第 113 节的最优首系数。本批仍未确定每个子临界半径上的全部最优仪器、最坏均值的完整闭式、次主项和最小分数次指数，也未把齐次二维结论推广到任意时变控制或无限维记忆。

## 追加锚（本行以下为增补区）

## 115. 临界终端通道由快分支与归一化慢点击后继共同确定

第 108 节说明：临界附近，终端态可以趋向任意预定密度矩阵。第 113 节又准确求出最坏均值的首系数。现在把这两种自由放到同一个实际装置上比较：达到最坏等待的首阶，是否还允许终端量子后继任意改变？

以下继续使用原名义装置、完整二维活动记忆、两种实际记录和齐次重复合同。保留全部参考输入；终端通道丢弃首次点击轮数，但保留点击后的量子系统。

**定义 115.1（最坏均值占比与终端距离）。** 对 $0<h<R$ 和任意 $\Gamma\in\mathfrak B_{R-h}$，定义

$$
\Xi_\Gamma=\sum_{n\ge1}\mathcal C_\Gamma\mathcal N_\Gamma^{n-1}
=\mathcal C_\Gamma(\operatorname{id}-\mathcal N_\Gamma)^{-1},
\qquad
\mathcal T_0(X)=\operatorname{Tr}(X)P_0,
$$

$$
\lambda_h(\Gamma)=\frac{M(\Gamma)}{\mathscr K(R-h)}\in(0,1],
\qquad
 d_\Gamma=\frac12\|\Xi_\Gamma-\mathcal T_0\|_\diamond\in[0,1].
\tag{115.1}
$$

该球内所有装置全状态终止，有限维谱半径小于一，所以级数收敛并定义 CPTP 通道。这里 $\lambda_h$ 比较同一装置的最大平均等待与整个球的最坏平均等待；$d_\Gamma$ 比较同一装置的完整终端作用与固定准备 $P_0$ 的通道。

对最近失效集合附近的装置，沿用 $\mathcal N(\sigma)=(1-\epsilon)\sigma$，定义实际慢点击后继

$$
\zeta_\Gamma=\frac{\mathcal C_\Gamma(\sigma_\Gamma)}{\epsilon_\Gamma}.
\tag{115.2}
$$

完整性使分子正半定且迹恰为 $\epsilon_\Gamma$，故 $\zeta_\Gamma$ 是密度矩阵。它使用原始点击分支，不是第 112 节检验中辅助重置后的分支。

**定理 115.2（终端通道的共同极限分解）。** 若不失效的 $\Gamma_j\to\Gamma_*\in\mathfrak F_R$，且沿所取子列有 $\zeta_j\to\zeta_*$，则在完整 diamond 范数中

$$
\boxed{
\Xi_{\Gamma_j}(X)\longrightarrow
\operatorname{Tr}(P_*X)\zeta_*
+\operatorname{Tr}[(I-P_*)X]P_0.
}
\tag{115.3}
$$

其中 $P_*$ 是该边界装置的暗态投影。因而，即使沿原序列 $\zeta_j$ 没有极限，仍有

$$
\boxed{d_{\Gamma_j}-D(\zeta_j,P_0)\longrightarrow0,\qquad
D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1.}
\tag{115.4}
$$

式（115.4）也对趋近整个最近失效集合的序列成立，不要求预选唯一边界相位。

证明。令状态侧谱投影为

$$
\mathcal P_\Gamma(X)=\sigma_\Gamma\operatorname{Tr}(G_\Gamma X),
\qquad
\mathcal B_\Gamma=\mathcal N_\Gamma(\operatorname{id}-\mathcal P_\Gamma),
\qquad
\mathcal R_\Gamma=(\operatorname{id}-\mathcal B_\Gamma)^{-1}
(\operatorname{id}-\mathcal P_\Gamma).
$$

第 93、96 节保证该投影及稳定部分连续，后者的谱与一一致分离。分解主谱空间与其补空间，准确得到

$$
(\operatorname{id}-\mathcal N_\Gamma)^{-1}
=\epsilon_\Gamma^{-1}\mathcal P_\Gamma+\mathcal R_\Gamma,
$$

$$
\Xi_\Gamma(X)
=\zeta_\Gamma\operatorname{Tr}(G_\Gamma X)
+\mathcal C_\Gamma\mathcal R_\Gamma(X).
\tag{115.5}
$$

在边界，定理 106.1 给

$$
\mathcal N_* =\mathcal P_*:X\mapsto P_*XP_*,
\quad G_*=P_*,\quad
\mathcal B_*=0,\quad
\mathcal R_* =\operatorname{id}-\mathcal P_*,
$$

$$
\mathcal C_*\mathcal R_*(X)
=\operatorname{Tr}[(I-P_*)X]P_0.
$$

因此式（115.5）的两项分别收敛，得到式（115.3）。这里先准确分离 $\epsilon^{-1}$ 主项，再对有界稳定部分取极限；没有把一个未控制的点击映射误差除以 $\epsilon$。

输入、输出维数固定，线性映射空间中的范数等价，故矩阵元收敛也是 diamond 范数收敛。极限通道与 $\mathcal T_0$ 之差为

$$
X\longmapsto\operatorname{Tr}(P_*X)(\zeta_*-P_0).
$$

对任意归一化参考联合输入，其输出是一个迹至多一的正参考算子张量 $\zeta_*-P_0$；输入 $P_*$ 达到迹一。因此极限完整半钻石距离恰为 $D(\zeta_*,P_0)$。

密度矩阵和最近失效集合都紧。若式（115.4）不成立，取差值远离零的子列，再取装置与 $\zeta_j$ 的共同收敛子列，刚才的极限计算给矛盾。这也处理不同边界相位。$\square$

## 116. 最坏等待占比限制终端量子后继的偏离

**定理 116.1（等待占比与终端距离的平方关系）。** 对任意 $h_j>0$、$h_j\to0$ 及任意实际 $\Gamma_j\in\mathfrak B_{R-h_j}$，有

$$
\boxed{
\limsup_{j\to\infty}
\left[\lambda_{h_j}(\Gamma_j)+d_{\Gamma_j}^{\,2}\right]
\le1.
}
\tag{116.1}
$$

这比较同一个装置的实际最大均值和最终完整通道，不将不同装置各自达到的值拼成共同结论。

证明。只需考虑 $\lambda_j\to\lambda$ 的任意子列。若 $\lambda=0$，由 $d_j\le1$ 直接成立。设 $\lambda>0$。定理 113.1 给 $\mathscr K(R-h_j)\sim\kappa^2h_j^{-2}$，故 $M(\Gamma_j)\to\infty$。仪器紧性、子临界均值的局部有界性及校准约束迫使每个装置聚点属于 $\mathfrak F_R$。于是可用第 111—112 节的共同估计，以及

$$
\epsilon_jM(\Gamma_j)\longrightarrow1,
\qquad
\frac{h_j^2}{\kappa^2\epsilon_j}\longrightarrow\lambda.
\tag{116.2}
$$

在当前准平稳态本征基中，保留式（112.6）里 $g_j$ 的实部，不先用其模替换。其他可能降低检验值的项仍为 $o(\sqrt{\epsilon_j})$，且 $H_{cb}\to-\kappa/2$。因 $L(a,z_0)\ge R$，有

$$
h_j\le R-\delta(\Gamma_j)
\le(\kappa+o(1))\operatorname{Re}g_j
+o(\sqrt{\epsilon_j}).
$$

$|g_j|/\sqrt{\epsilon_j}$ 有界，结合式（116.2）得到

$$
\liminf_j\frac{\operatorname{Re}g_j}{\sqrt{\epsilon_j}}
\ge\sqrt\lambda.
\tag{116.3}
$$

点击效果 $E_j=\mathcal C_j^*(I)$ 的矩阵元满足

$$
(E_j)_{\psi\eta}=-g_j-\sum_\ell\overline{f_\ell}a_\ell,
\qquad
\left|\sum_\ell\overline{f_\ell}a_\ell\right|
\le\sqrt{F_jv_j}=o(\sqrt{\epsilon_j}),
$$

$$
(E_j)_{\psi\psi}\le\ell_{\psi,j}
=\epsilon_j(1+o(1)),\qquad
(E_j)_{\eta\eta}\longrightarrow1.
\tag{116.4}
$$

现在必须回到原始点击后继。取该点击 CP 映射的任一 Kraus 表示 $B_\ell$，在本装置的辅助空间中置

$$
x_j=\sum_\ell B_\ell\psi_j\otimes|\ell\rangle,
\qquad
z_j=\sum_\ell B_\ell\eta_j\otimes|\ell\rangle,
\qquad A=P_0\otimes I.
$$

这些辅助标签只用于证明，不是新可读记录。由式（116.4），

$$
\langle x_j,z_j\rangle=(E_j)_{\psi\eta},
\qquad \|x_j\|/\sqrt{\epsilon_j}=O(1),
\qquad \|z_j\|\to1.
$$

定理 106.1 对原始点击分支的分类给 $\mathcal C_j(P_{\eta,j})\to P_0$。因此

$$
\|(I-A)z_j\|\to0,\qquad \|Az_j\|\to1.
$$

把内积分成 $A$ 与 $I-A$ 两部分，Cauchy–Schwarz 给

$$
\frac{|(E_j)_{\psi\eta}|}{\sqrt{\epsilon_j}}
\le\frac{\|Ax_j\|}{\sqrt{\epsilon_j}}\|Az_j\|
+\frac{\|x_j\|}{\sqrt{\epsilon_j}}\|(I-A)z_j\|.
\tag{116.5}
$$

第二项趋零，第一项的最后因子趋一；结合式（116.3）—（116.4），得到

$$
\liminf_j
\frac{\langle0|\mathcal C_j(P_j)|0\rangle}{\epsilon_j}
\ge\lambda.
$$

实际准平稳态为 $\sigma_j=(1-y_j)P_j+y_jP_{\eta,j}$，$y_j\to0$。两个点击输出均正，所以

$$
\liminf_j\langle0|\zeta_j|0\rangle
=\liminf_j
\frac{(1-y_j)\langle0|\mathcal C_j(P_j)|0\rangle
+y_j\langle0|\mathcal C_j(P_{\eta,j})|0\rangle}{\epsilon_j}
\ge\lambda.
\tag{116.6}
$$

对任意量子比特密度矩阵 $\zeta=\begin{pmatrix}q&b\\\overline b&1-q\end{pmatrix}$，正性给 $|b|^2\le q(1-q)$，直接求 $\zeta-P_0$ 的两本征值可得

$$
D(\zeta,P_0)^2=(1-q)^2+|b|^2\le1-q.
$$

结合式（116.6）与定理 115.2，得到 $\limsup d_j^2\le1-\lambda$。每一条 $\lambda_j$ 的收敛子列都满足相同结论，故成立式（116.1）。$\square$

**推论 116.2（首阶最坏等待强制终端通道趋向固定后继）。** 若同一序列满足

$$
\frac{M(\Gamma_j)}{\mathscr K(R-h_j)}\longrightarrow1,
$$

则

$$
\boxed{\frac12\|\Xi_{\Gamma_j}-\mathcal T_0\|_\diamond\longrightarrow0.}
\tag{116.7}
$$

尤其，任意精确最坏装置选择都满足此结论。任意初态和参考关联下，丢弃首次点击时间后的输出趋向参考边缘张量 $P_0$。

证明。将 $\lambda_j\to1$ 代入定理 116.1，利用 $d_j^2\ge0$。diamond 范数控制所有参考输入，再用重置通道的定义得到后一句。$\square$

这不与第 108.4 条的任意终端态相冲突：该构造允许很长的等待，却没有要求其均值占整个球的最坏均值趋于一。终端量子作用的自由与等待达到最坏首阶不能分别取得后再直接合并。

## 117. 相干点击构造使平方关系的每个边界点都可实现

**定义 117.1（保持点击相干项的同接口仪器）。** 固定

$$
\psi=|+\rangle,\quad P=P_\psi,\quad
\eta=\frac{-|0\rangle+|1\rangle}{\sqrt2},\quad
\psi_t=\cos t\,\psi-\sin t\,\eta.
$$

对充分小的 $t>0$ 及 $0\le k<1$，取

$$
Q_{t,k}=\sqrt{1-k}\,|\psi_t\rangle\langle\psi|,
\qquad
B_k=|0\rangle\langle\eta|+\sqrt k\,|1\rangle\langle\psi|,
$$

$$
\Gamma_{t,k}^{\rm coh}
=(X\mapsto Q_{t,k}XQ_{t,k}^\dagger,
  X\mapsto B_kXB_k^\dagger).
\tag{117.1}
$$

$Q_{t,k}^\dagger Q_{t,k}=(1-k)P$，而 $B_k^\dagger B_k=I-P+kP$，故这是完整仪器。它仍只有未点击与点击两个可读结果。点击映射包含交叉项，不是第 107 节两个制备项的经典相加。

**引理 117.2（相干点击的完整校准修正只有 $O(k)$）。** 在 $(t,k)\to(0,0)$、$k\ge0$ 时，完整名义距离满足

$$
\boxed{
\delta(\Gamma_{t,k}^{\rm coh})
=\delta(\widehat\Gamma_{-t})+O(k)
=R-\kappa t+O(t^2+k).
}
\tag{117.2}
$$

这里比较的是两份到同一名义仪器的距离之差，不声称这两个实际仪器之间的距离为 $O(k)$。

证明。对任意系统密度矩阵 $\rho$，取其归一化纯化。实际与名义仪器的每个分支都只有一个 Kraus 算子，所以每个联合输出块是两个向量投影之差。其迹范数由式（103.4）准确给出。令

$$
p=\operatorname{Tr}(\rho P),\quad
q=\operatorname{Tr}(\rho P_1),\quad
\alpha_t=\operatorname{Tr}[\rho(|\psi\rangle\langle\psi_t|)Q_0],
\quad
\beta_0=\operatorname{Tr}(\rho B_0^\dagger L_0),
$$

其中 $Q_0=|0\rangle\langle1|$、$L_0=P_0$ 仍是名义装置。关键恒等式是

$$
B_k^\dagger L_0=B_0^\dagger L_0=|\eta\rangle\langle0|.
$$

因此完整输出的半迹距离准确为

$$
\mathcal F(t,k;\rho)=\frac12\left[
\sqrt{((1-k)p+q)^2-4(1-k)|\alpha_t|^2}
+\sqrt{(1-p+kp+1-q)^2-4|\beta_0|^2}
\right].
\tag{117.3}
$$

对全部 $\rho$ 最大化就是完整半钻石距离：任意参考输入可纯化，系统边缘决定上述所有内积，二维参考已足够取得最大值。

在 $t=k=0$ 时，第 103 节已经把全部最大化边缘态描述为 $x=x_*,v=0$，其中 $x=q_0-\operatorname{Re}\rho_{01}$、$q_0=\rho_{00}$。在这整个最大化集合上，两根号内的量分别为

$$
\frac54-x_*>0,\qquad \frac14+x_*-x_*^2>0.
$$

密度矩阵集合紧，函数 $\mathcal F$ 联合连续。因此充分小的 $(t,k)$ 的全部最大化点都落在上述集合的任意预定邻域内；否则取收敛子列会在基点产生新的最大化点。选取其中一个邻域，使两个根号内的量都有共同正下界。

在该邻域中，式（117.3）的两个根号内部对 $k$ 的变化都是一致的 $O(k)$，平方根因远离零而具有共同 Lipschitz 常数。于是

$$
|\mathcal F(t,k;\rho)-\mathcal F(t,0;\rho)|\le Ck
$$

在两种参数的全部最大化点上同时成立。分别代入两边的最大化点，得到两个最大值之差的绝对值至多 $Ck$。$k=0$ 时仪器准确为 $\widehat\Gamma_{-t}$，再用定理 103.2 得式（117.2）。$\square$

**定理 117.3（全部极限边界点由实际仪器达到）。** 对每个 $\lambda\in[0,1]$，存在 $t_j\to0$ 的上述实际仪器和正间隙

$$
h_j=R-\delta(\Gamma_{t_j,k_j}^{\rm coh})\longrightarrow0,
$$

使该仪器属于 $\mathfrak B_{R-h_j}$，并且

$$
\boxed{
\frac{M(\Gamma_{t_j,k_j}^{\rm coh})}{\mathscr K(R-h_j)}
\longrightarrow\lambda,
\qquad
 d_{\Gamma_{t_j,k_j}^{\rm coh}}\longrightarrow\sqrt{1-\lambda}.
}
\tag{117.4}
$$

因而定理 116.1 的整个边界曲线都在同一物理接口与同一校准定义内实现。

证明。先取固定 $a\ge0$，令 $k=at^2$。未点击动力学与第 107 节相同，其准平稳态为 $S_t=P_{\psi_t}$，且

$$
\epsilon_{t,k}=k+(1-k)\sin^2t,
\qquad
M(\Gamma_{t,k}^{\rm coh})=1+\frac{1-k}{\epsilon_{t,k}}.
\tag{117.5}
$$

直接作用点击算子得到

$$
B_k\psi_t=-\sin t\,|0\rangle+\sqrt k\cos t\,|1\rangle,
\qquad
\zeta_{t,k}=
\frac{|B_k\psi_t\rangle\langle B_k\psi_t|}{\epsilon_{t,k}}.
\tag{117.6}
$$

从任意输入第一次点击时输出 $B_kXB_k^\dagger$；若第一次未点击，未归一化后继是 $(1-k)\operatorname{Tr}(PX)S_t$。从 $S_t$ 出发的最终点击后继准确为 $\zeta_{t,k}$，所以

$$
\Xi_{t,k}(X)=B_kXB_k^\dagger
+(1-k)\operatorname{Tr}(PX)\zeta_{t,k}.
\tag{117.7}
$$

令 $t\to0$，有

$$
\epsilon_{t,at^2}\sim(1+a)t^2,
\qquad
\zeta_{t,at^2}\longrightarrow P_{\xi_a},
\qquad
\xi_a=\frac{-|0\rangle+\sqrt a\,|1\rangle}{\sqrt{1+a}}.
$$

引理 117.2 给 $h_t=\kappa t+O(t^2)>0$。由定理 113.1，

$$
\mathscr K(R-h_t)\sim t^{-2},\qquad
\frac{M(\Gamma_{t,at^2}^{\rm coh})}{\mathscr K(R-h_t)}
\longrightarrow\frac1{1+a}.
$$

定理 115.2 或式（117.7）直接给

$$
d_{\Gamma_{t,at^2}^{\rm coh}}
\longrightarrow D(P_{\xi_a},P_0)=\sqrt{\frac a{1+a}}.
$$

每个 $0<\lambda\le1$ 都可取 $a=(1-\lambda)/\lambda$ 达到，包括 $a=0$ 对应的原旋转族。

最后处理 $\lambda=0$：另取 $k=t^{3/2}$。引理 117.2 仍给 $h_t=\kappa t+o(t)>0$，而 $\epsilon_{t,k}\sim t^{3/2}$、$M\sim t^{-3/2}$。所以 $M/\mathscr K(R-h_t)\to0$。式（117.6）给 $\zeta_{t,k}\to P_1$，故 $d\to1$。所有正 $t$ 的装置都终止，结论来自真实子临界序列。$\square$

## 118. 最坏等待与终端自由之间的关系是共同约束

**关系结论 118.1（AHH：长等待的首阶与交给未来的状态不能独立安排）。** 第 108 节的任意终端态自由没有消失；新的约束是，它与最坏均值占比共同满足

$$
\boxed{\lambda+d^2\le1\quad\text{的临界极限关系}.}
$$

若等待达到最坏首阶，$\lambda\to1$ 就迫使完整终端通道趋向准备 $P_0$。若要保持非零终端距离，就必须让最坏均值占比离开一。第 117 节同时给每个边界点的真实实现，不能再统一收紧这条曲线。

这一步依赖原始点击后继的完整分类：只知道未点击映射的边界极限，还不能控制点击 Kraus 向量 $z_j$ 的输出方向。它也依赖准确首系数；只有确定 $c=\kappa^2$，等待占比才能回接到式（116.3）中同一个装置的相干量。

相干点击构造还显示，第 107 节经典制备混合所得的关系不必是最强边界。保留一个点击 Kraus 算子中的交叉项，可以在相同未点击动力学下把终端距离提高到平方根曲线。但校准必须重新证明：式（117.2）来自完整参考输入上的范数分析，不能由“只加了一点点击振幅”直接宣称。

**来源与边界 118.2。** 本批是同一有限矩阵模型内的纸面推导，复用第 93、96、106、111—113 节的谱投影、原始点击分类、统一检验与精确首系数。终端分解由准确 resolvent 恒等式给出；距离上界由正性、Cauchy–Schwarz 和二维迹范数公式给出；锐性由具体 Kraus 算子和全部参考输入的校准推导承担。

量子准平稳概念的相关原始文献还有 A. Dhahri、F. Fagnola、F. Girotti、H. J. Yoo，*Quasi-stationary normal states for quantum Markov semigroups*，[arXiv:2508.06396](https://arxiv.org/abs/2508.06396)。其 Theorem 1 将准平稳态与约化半群的正特征态联系起来；该文研究连续时间量子 Markov 半群，本批研究离散仪器的未点击分支。这里将其作为相关背景，不将其定理直接充作本批平方关系或锐性证明，也不额外引入不可约性或忠实态假设。

全部结论仍限于固定名义装置、二维完整活动记忆与齐次重复；终端通道丢弃时间，未声称完整时间记录也趋向同一个固定输出。平方关系是临界极限，不是未经余项控制的有限 $h$ 不等式。未声称达到边界曲线的内部实现唯一，也未求每个有限半径的全部最优仪器。本批不主张文献原创性，未新增或编译 Lean，未进入消化、覆盖或冻结链。

## 追加锚（本行以下为增补区）

## 119. 固定临界相位下，等待占比与慢点击态的完整可达区域

第 116 节只把慢点击后继压缩成一个标量距离，第 117 节证明了该标量平方边界可以达到。继续保留后继的全部密度矩阵，可以得到更细的结论：**临界等待占比的上限不是由终端态到 $P_0$ 的距离单独决定，而是由终端态在 $P_0$ 上的实际人口决定。**

**定义 119.1（固定相位的临界可达对）。** 固定最近失效相位 $\vartheta$，并记其暗态投影为 $P_\vartheta$。称一对

$$
(\lambda,\zeta),
\qquad 0\le\lambda\le1,
\qquad \zeta\succeq0,
\qquad \operatorname{Tr}\zeta=1,
$$

是**可达的**，若存在 $h_j\downarrow0$ 和完整齐次仪器 $\Gamma_j\in\mathfrak B_{R-h_j}$，满足

$$
\Gamma_j\longrightarrow\Gamma_\vartheta^{\rm eq},
\qquad
\frac{M(\Gamma_j)}{\mathscr K(R-h_j)}\longrightarrow\lambda,
$$

并且其准平稳慢点击态

$$
\zeta_j=\frac{\mathcal C_j(\sigma_j)}{\epsilon_j}
$$
收敛到 $\zeta$。这里的终端通道仍然丢弃首次点击轮数；$\zeta_j$ 保存点击后量子输出。

**定理 119.2（完整可达区域）。** 对固定 $\vartheta$，可达对恰好满足

$$
\boxed{
\mathcal A_\vartheta
=
\left\{
(\lambda,\zeta):
0\le\lambda\le1,\quad
\zeta\succeq0,\quad
\operatorname{Tr}\zeta=1,\quad
\lambda\le\langle0|\zeta|0\rangle
\right\}.
}
\tag{119.1}
$$

若 $(\lambda,\zeta)\in\mathcal A_\vartheta$，则相应终端通道在完整 diamond 范数中趋向

$$
\boxed{
\Lambda_{\vartheta,\zeta}(X)
=
\operatorname{Tr}(P_\vartheta X)\zeta
+
\operatorname{Tr}[(I-P_\vartheta)X]P_0.
}
\tag{119.2}
$$

反之，任何满足定义 119.1 的临界序列都满足 $\lambda\le\langle0|\zeta|0\rangle$。

### 证明：必要性

记 $\lambda_j:=M(\Gamma_j)/\mathscr K(R-h_j)$；按定义 $\lambda_j\to\lambda$。若 $\lambda=0$，所需不等式自动成立。设 $\lambda>0$。

由第 113 节的精确首系数、第 96 节的谱估计以及第 93.2 节的均值渐近式，

$$
\mathscr K(R-h_j)\sim\kappa^2h_j^{-2},
\qquad
\epsilon_jM(\Gamma_j)\longrightarrow1,
\qquad
\kappa=\frac{\sqrt\phi}{4}.
$$

故

$$
\frac{h_j^2}{\kappa^2\epsilon_j}\longrightarrow\lambda.
\tag{119.3}
$$

沿第 111 节，在当前准平稳态的本征基中作相位对齐。相位不预先固定 $g_j$ 的符号；保留第 112.6 式中的相干项并取其绝对值，得到

$$
 h_j\le R-\delta(\Gamma_j)
\le (\kappa+o(1))|g_j|+o(\sqrt{\epsilon_j}).
\tag{119.4}
$$

结合 $|g_j|/\sqrt{\epsilon_j}$ 的统一有界性与式（119.3），得到

$$
\liminf_j
\frac{|g_j|}{\sqrt{\epsilon_j}}
\ge\sqrt\lambda.
\tag{119.5}
$$

令 $P_j:=|\psi_j\rangle\langle\psi_j|$，并令 $E_j=\mathcal C_j^*(I)$。完整性和准平稳方程给出

$$
(E_j)_{\psi_j\eta_j}=-g_j+o(\sqrt{\epsilon_j}),
\qquad
(E_j)_{\psi_j\psi_j}\le\epsilon_j(1+o(1)).
\tag{119.6}
$$

取点击分支的任意 Stinespring 算子 $V_j$，置

$$
 x_j=V_j\psi_j,\qquad z_j=V_j\eta_j,\qquad
 A=P_0\otimes I_{\rm env}.
$$

则

$$
\langle x_j,z_j\rangle=(E_j)_{\psi_j\eta_j},\qquad
\|x_j\|=O(\sqrt{\epsilon_j}).
$$

第 106 节分类的是原始点击映射，因此给出

$$
\mathcal C_j(P_{\eta_j})\longrightarrow P_0.
$$

于是 $\|Az_j\|\to1$ 且 $\|(I-A)z_j\|\to0$。把内积分成 $A$ 和 $I-A$ 两部分，Cauchy–Schwarz 不等式给出

$$
\frac{|(E_j)_{\psi_j\eta_j}|}{\sqrt{\epsilon_j}}
\le
\sqrt{\frac{\langle0|\mathcal C_j(P_j)|0\rangle}{\epsilon_j}}\,\|Az_j\|
+
\frac{\|x_j\|}{\sqrt{\epsilon_j}}\|(I-A)z_j\|.
\tag{119.7}
$$

第二项趋于零，故式（119.5）—（119.7）推出

$$
\liminf_j
\frac{\langle0|\mathcal C_j(P_j)|0\rangle}{\epsilon_j}
\ge\lambda.
\tag{119.8}
$$

准平稳态为 $\sigma_j=(1-y_j)P_j+y_jP_{\eta_j}$，两个点击输出均为正半定，且 $y_j\to0$。因此

$$
\langle0|\zeta_j|0\rangle
=(1-y_j)\frac{\langle0|\mathcal C_j(P_j)|0\rangle}{\epsilon_j}
+
\frac{y_j}{\epsilon_j}\langle0|\mathcal C_j(P_{\eta_j})|0\rangle
\ge
(1-y_j)\frac{\langle0|\mathcal C_j(P_j)|0\rangle}{\epsilon_j}.
$$
由式（119.8）得到

$$
\lambda\le\langle0|\zeta|0\rangle.
$$

再证终端通道的极限。令

$$
\mathcal P_j(X)=\sigma_j\operatorname{Tr}(G_jX),
$$

并令 $\mathcal R_j$ 为第 115 节的有界稳定 resolvent。准确恒等式为

$$
(\operatorname{id}-\mathcal N_j)^{-1}
=\epsilon_j^{-1}\mathcal P_j+\mathcal R_j,
$$

故

$$
\Xi_j(X)=\zeta_j\operatorname{Tr}(G_jX)+\mathcal C_j\mathcal R_j(X).
\tag{119.9}
$$

由第 106 节的原始点击分类以及第 115、96 节的稳定 resolvent 连续性，$G_j\to P_\vartheta$，$\mathcal R_j\to\operatorname{id}-\mathcal P_\vartheta$，并且

$$
\mathcal C_j\mathcal R_j(X)\longrightarrow
\operatorname{Tr}[(I-P_\vartheta)X]P_0.
$$
固定有限维输入输出空间上的线性映射范数等价，所以这是完整 diamond 范数收敛。得到式（119.2）。证毕。

### 证明：充分性

先取 $\vartheta=0$，令

$$
\psi=|+\rangle,\qquad
\eta=\frac{-|0\rangle+|1\rangle}{\sqrt2},\qquad
P=P_\psi,\qquad Q=P_\eta,
$$

$$
\psi_t=\cos t\,\psi-\sin t\,\eta,\qquad S_t=P_{\psi_t}.
$$

设 $0<\lambda<1$ 且 $\zeta_{00}:=\langle0|\zeta|0\rangle\ge\lambda$。取二维环境的纯化 $|w\rangle$，满足

$$
\operatorname{Tr}_{\rm env}|w\rangle\langle w|=\zeta.
$$

令 $y=(\langle0|\otimes I)|w\rangle$，则 $\|y\|^2=\zeta_{00}$。选单位向量 $e_0$ 使

$$
\langle e_0,y\rangle=-\sqrt\lambda.
$$

这是可能的，因为 $\|y\|^2\ge\lambda$；若 $y\ne0$，可在其正交补中取单位向量并令

$$
 e_0=-\sqrt{\frac\lambda{\zeta_{00}}}\frac y{\|y\|}
 +\sqrt{1-\frac\lambda{\zeta_{00}}}\,e_\perp.
$$

令 $s=|0\rangle\otimes e_0$，并置

$$
 u=\frac{w+\sqrt\lambda\,s}{\sqrt{1-\lambda}}.
$$

则 $u$ 为单位向量，且 $u\perp s$，并有

$$
 w=-\sqrt\lambda\,s+\sqrt{1-\lambda}\,u.
\tag{119.10}
$$

定义同一 qubit 活动空间上的未点击算子和点击 Stinespring 算子

$$
 A_{t,k}=\sqrt{1-k}\,|\psi_t\rangle\langle\psi|,
$$

$$
 V_k\eta=s,\qquad V_k\psi=\sqrt{k}\,u,
$$

其中 $k=\frac{1-\lambda}{\lambda}t^2$。取 $t$ 足够小使 $0<k<1$。定义两种实际记录分支

$$
\mathcal N_{t,k}(X)=A_{t,k}XA_{t,k}^\dagger,\qquad
\mathcal C_k(X)=\operatorname{Tr}_{\rm env}(V_kXV_k^\dagger).
\tag{119.11}
$$

由于 $u\perp s$，

$$
A_{t,k}^\dagger A_{t,k}=(1-k)P,\qquad
V_k^\dagger V_k=Q+kP,
$$

两者之和为 $I$。环境指标未成为第三种可读记录；将其分解成 Kraus 算子至多只增加同一个点击记录内部的表示项。

未点击本征分支的谱泄漏为

$$
\epsilon_{t,k}=\sin^2t+k\cos^2t.
$$

本模型的最大均值为

$$
M_{t,k}=1+\frac{1-k}{\epsilon_{t,k}},
\tag{119.12}
$$

并且该最大值由输入 $P$ 达到；从 $P_{\psi_t}$ 出发的均值则为 $1/\epsilon_{t,k}$。

记点击分支在该输入上的未归一化输出向量为

$$
v_{t,k}=-\sin t\,s+\sqrt{k}\cos t\,u.
$$

归一化慢点击后继是活动 qubit 上的密度矩阵

$$
\zeta_{t,k}
=
\frac{\operatorname{Tr}_{\rm env}|v_{t,k}\rangle\langle v_{t,k}|}
{\sin^2t+k\cos^2t}.
\tag{119.13}
$$

由式（119.10）与 $k=((1-\lambda)/\lambda)t^2$，有

$$
\frac{v_{t,k}}{\sqrt{\sin^2t+k\cos^2t}}\longrightarrow w,
\qquad
\zeta_{t,k}\longrightarrow\operatorname{Tr}_{\rm env}|w\rangle\langle w|=\zeta.
$$

另一方面，需要检验实际完整仪器到固定名义仪器的距离，而不能只比较两个实际仪器。由于环境是二维的，可将 $u$ 分解为

$$
u=\alpha|1\rangle\otimes e_0+|r\rangle\otimes e_1,
$$

其中 $e_1\perp e_0$，$|\alpha|^2+\lVert r\rVert^2=1$。令 $k'=k|\alpha|^2$，并定义

$$
B_{0,\alpha}=|0\rangle\langle\eta|+\sqrt{k}\,\alpha|1\rangle\langle\psi|,
\qquad
B_1=\sqrt{k}\,|r\rangle\langle\psi|.
$$

实际点击分支为 $\operatorname{Ad}_{B_{0,\alpha}}+\operatorname{Ad}_{B_1}$。去掉 $e_1$ 分量的比较仪器定义为

$$
\widetilde A=\sqrt{1-k'}\,|\psi_t\rangle\langle\psi|,
\qquad
\widetilde{\mathcal C}=\operatorname{Ad}_{B_{0,\alpha}},
$$

并以 $\widetilde{\mathcal N}=\operatorname{Ad}_{\widetilde A}$ 作为未点击分支。因为

$$
B_{0,\alpha}^\dagger B_{0,\alpha}=Q+k'P,
\qquad
\widetilde A^\dagger\widetilde A=(1-k')P,
$$

它是完整的两记录仪器。对任意参考输入，实际仪器与该比较仪器的两个记录块之差分别是一个正的 $k-k'$ 质量与其相反的未点击质量，故

$$
\frac12\lVert\Gamma_{t,k}-\widetilde\Gamma_{t,k'}\rVert_\diamond
=k-k'=k(1-|\alpha|^2).
\tag{119.14}
$$

对相干比较仪器，点击 Kraus 算子满足

$$
B_{0,\alpha}^\dagger L_0=|\eta\rangle\langle0|,
$$

所以第 117.2 节的全参考输入估计对复数 $\alpha$ 原样适用：其完整距离在 $k'$ 处相对于 $k'=0$ 的变化只有 $O(k')$。具体地，在 $k'=0$ 的全部最大化边缘态上，第 103 节的两个平方根分别严格为正；紧性把所有邻近最大化点限制在一个共同邻域，平方根在那里有统一 Lipschitz 常数。因此

$$
\delta(\Gamma_{t,k})
=R-\kappa t+O(t^2+k).
\tag{119.15}
$$

置

$$
 h_t=R-\delta(\Gamma_{t,k})>0.
$$

则 $h_t\sim\kappa t$，且

$$
\epsilon_{t,k}\sim \frac{t^2}{\lambda},\qquad
M_{t,k}\sim\lambda t^{-2},\qquad
\mathscr K(R-h_t)\sim t^{-2}.
$$
所以等待占比趋向 $\lambda$，而归一化慢点击后继趋向目标 $\zeta$。取一列 $t_j\downarrow0$，必要时再取子列，使正间隙 $h_{t_j}\downarrow0$。

若 $\lambda=1$，条件 $\zeta_{00}\ge1$ 迫使 $\zeta=P_0$；第 103 节的原旋转族给出该端点。

若 $\lambda=0$，对任意目标 $\zeta$ 使用第 108.4 节的经典点击制备族，取 $\widetilde k_t=t^{3/2}$。设所得仪器为 $\widetilde\Gamma_t^\zeta$，无附加点击分支的旋转仪器为 $\widehat\Gamma_{-t}$。第 108.4 节给出

$$
\frac12\lVert\widetilde\Gamma_t^\zeta-\widehat\Gamma_{-t}\rVert_\diamond=\widetilde k_t,
$$

因此到同一名义仪器的距离满足反向三角估计

$$
|\delta(\widetilde\Gamma_t^\zeta)-\delta(\widehat\Gamma_{-t})|
\le\widetilde k_t.
$$

结合第 103 节的 $\delta(\widehat\Gamma_{-t})=R-\kappa t+O(t^2)$，实际间隙仍为 $h_t\sim\kappa t$。此外，第 107 节的几何求和给出慢点击后继

$$
\widetilde\zeta_t
=
\frac{\sin^2t\,P_0+\widetilde k_t\cos^2t\,\zeta}
{\sin^2t+\widetilde k_t\cos^2t}
\longrightarrow\zeta,
$$

并且 $\widetilde\epsilon_t\sim t^{3/2}$、$M_t\sim t^{-3/2}$，而 $\mathscr K(R-h_t)\sim t^{-2}$，所以等待占比趋向零。这一步不把 $\lambda=0$ 的任意目标误塞入上面的纯化构造。

最后，对一般 $\vartheta$，令

$$
U_\vartheta=\operatorname{diag}(1,e^{i\vartheta}),
\qquad
\operatorname{Ad}_{U_\vartheta}(X)=U_\vartheta XU_\vartheta^\dagger.
$$

先以 $U_\vartheta^\dagger\zeta U_\vartheta$ 代替目标运行上述构造，并把两条分支显式共轭为

$$
\mathcal N^{(\vartheta)}(X)=U_\vartheta\mathcal N^{(0)}(U_\vartheta^\dagger XU_\vartheta)U_\vartheta^\dagger,
\qquad
\mathcal C^{(\vartheta)}(X)=U_\vartheta\mathcal C^{(0)}(U_\vartheta^\dagger XU_\vartheta)U_\vartheta^\dagger.
$$

由于 $\operatorname{Ad}_{U_\vartheta}(Q_0)=e^{-i\vartheta}Q_0$ 且 $\operatorname{Ad}_{U_\vartheta}(L_0)=L_0$，固定名义仪器的 CP 映射不变；距离、均值和等待占比保持不变，暗态变为 $P_\vartheta$，目标后继恢复为 $\zeta$。证毕。

## 120. 终端状态的 Bloch 球帽与目标检验上界

**推论 120.1（固定等待占比的状态几何）。** 对固定 $0\le\lambda\le1$，可达慢点击密度矩阵正好是

$$
\boxed{
\{\zeta:\zeta\succeq0,\ \operatorname{Tr}\zeta=1,\ \zeta_{00}\ge\lambda\}.
}
\tag{120.1}
$$

记

$$
\mathcal Z_\lambda:=\{\zeta:\zeta\succeq0,\ \operatorname{Tr}\zeta=1,\ \zeta_{00}\ge\lambda\}.
$$

写 $\zeta=(I+\mathbf r\cdot\boldsymbol\sigma)/2$，其中 $\sigma_z=|0\rangle\langle0|-|1\rangle\langle1|$，则它是 Bloch 球帽

$$
|\mathbf r|\le1,\qquad r_z\ge2\lambda-1.
\tag{120.2}
$$

特别地，

$$
\max_{\zeta\in\mathcal Z_\lambda}|\zeta_{01}|
=
\begin{cases}
\frac12,&0\le\lambda\le\frac12,\\[1mm]
\sqrt{\lambda(1-\lambda)},&\frac12\le\lambda\le1.
\end{cases}
\tag{120.3}
$$

证明。式（120.1）是定理 119.2 的直接投影；Bloch 表示给出式（120.2）。正性给 $|\zeta_{01}|^2\le\zeta_{00}(1-\zeta_{00})$。在 $\zeta_{00}\ge\lambda$ 上最大化右侧，得到式（120.3）；定理 119.2 的构造实现每个最大值。证毕。

**推论 120.2（任意纯目标的最大终端检验概率）。** 令 $|v\rangle$ 为目标纯态，并记

$$
q_v=|\langle0|v\rangle|^2.
$$
在固定等待占比 $\lambda$ 下，从边界暗态的输入 $P_\vartheta$ 出发，终端输出通过检验 $|v\rangle\langle v|$ 的最大临界概率为

$$
\boxed{
\sup_{\zeta\in\mathcal Z_\lambda}
\langle v|\zeta|v\rangle
=
\begin{cases}
1,&q_v\ge\lambda,\\[1mm]
\left(\sqrt{\lambda q_v}
+\sqrt{(1-\lambda)(1-q_v)}\right)^2,&q_v<\lambda.
\end{cases}
}
\tag{120.4}
$$

证明。固定 $q=\zeta_{00}$ 时，正性给

$$
|\zeta_{01}|\le\sqrt{q(1-q)}.
$$
选择相位使非对角项与 $|v\rangle$ 的相位一致，得到

$$
\langle v|\zeta|v\rangle
\le
q q_v+(1-q)(1-q_v)+2\sqrt{q(1-q)q_v(1-q_v)}.
$$
右侧是

$$
\left(\sqrt{q q_v}+\sqrt{(1-q)(1-q_v)}\right)^2.
$$
它在 $q=q_v$ 处取一；若 $q_v\ge\lambda$，该点可行。若 $q_v<\lambda$，令

$$
g(q)=\sqrt{q q_v}+\sqrt{(1-q)(1-q_v)}.
$$

在 $q_v<q<1$ 上

$$
g'(q)=\frac12\left(\sqrt{\frac{q_v}{q}}-\sqrt{\frac{1-q_v}{1-q}}\right)<0,
$$

故在区间 $q\ge\lambda$ 上最大值位于端点 $q=\lambda$；端点 $q=1$ 由连续性处理，给出式（120.4）。达到上界的矩阵是相应相位的纯态投影，定理 119.2 保证其可达。证毕。

## 121. 人口而非距离是临界后继的真实预算

**关系结论 121.1（AHH：等待预算由后继对点击端口的人口承载）。** 第 118 节的平方关系是完整终端距离的投影；第 119 节给出更细的算子事实：在固定最近失效相位与固定等待占比 $\lambda$ 下，终端后继的真正必要且充分条件是

$$
\boxed{\zeta_{00}\ge\lambda.}
$$

因此两个密度矩阵可以到 $P_0$ 的距离相同，却拥有不同的等待预算；距离只记录一个投影，而 $P_0$ 人口保留了相干和混合结构所需的方向信息。比如 $\zeta=I/2$ 的最大等待占比是 $1/2$，虽然它到 $P_0$ 的平方距离只有 $1/4$；状态人口给出的限制严格得多。

该人口规律描述的是临界极限中归一化慢点击后继的预算，也解释了相干点击构造的作用：在极限中，点击分支必须把足够的归一化人口送入 $|0\rangle$ 输出端口，剩余振幅才能以环境内部的相干方式组成任意目标纯化。环境指标不成为额外记录；它只是完整 CP 分支的内部表示。把环境标签公开，会改变观察接口，不能拿来替代本定理的两记录模型。

**来源与边界 121.2。** 本批在第 106—118 节的原始点击分类、精确首系数、准平稳谱投影、Stinespring 向量估计和完整参考输入校准上继续推导。新增区域定理由密度矩阵正性、准确 resolvent 分解和显式 Kraus/Stinespring 构造承担；不依赖数值优化，不主张文献原创性。连续时间 QSS 文献仅作背景，不能替代本离散仪器证明。

本批只描述临界序列的极限可达区域，不给有限 $h$ 的精确状态区域，不分类达到同一极限的内部实现，也不把 terminal channel 丢弃时间后的结论推广为保留完整时间记录的结论。模型仍固定为指定名义仪器、二维活动记忆、两个可读记录和齐次重复；调用轮数仍不是物理秒数。未新增或编译 Lean，未进入消化、覆盖或冻结链。

## 追加锚（本行以下为增补区）

## 122. 把事件时间和量子后继放进同一个标记对象

第 115 节只保留终端量子输出，因而把首次点击轮数求和掉。若把缩放时间

$$
\tau_{j,n}=\epsilon_j n
$$

与第 $n$ 轮点击后的量子输出一起保留，则同一份临界过程产生一个算子值的时间测度，而不是一条单独的时间律。

**定义 122.1（缩放标记测度）。** 沿用第 115 节的指定名义仪器、完整二维活动记忆、两种实际记录和齐次重复合同，取一条趋近同一个最近失效相位的非失效序列，设

$$
\Gamma_j\longrightarrow\Gamma_*\in\mathfrak F_R,
\qquad
\epsilon_j\longrightarrow0,
\qquad
\zeta_j\longrightarrow\zeta,
$$

并写

$$
P_*=P_{\text{暗}},
\qquad
Q_*=I-P_*.
$$

对每个输入算子 $X$，定义正时间标记的算子值测度

$$
\boxed{
\mathbf M_j(X)
=
\sum_{n\ge1}\delta_{\epsilon_j n}\otimes
\mathcal C_j\mathcal N_j^{\,n-1}(X).
}
\tag{122.1}
$$

对有界连续函数 $f:[0,\infty)\to\mathbb C$，定义其测试响应

$$
\boxed{
\mathbf M_j[f](X)
=
\sum_{n\ge1}f(\epsilon_j n)\mathcal C_j\mathcal N_j^{\,n-1}(X).
}
\tag{122.2}
$$

对 Borel 集 $E\subseteq[0,\infty)$，式（122.1）按集合函数理解为

$$
\mathbf M_j(E)
=
\sum_{\epsilon_j n\in E}
\mathcal C_j\mathcal N_j^{\,n-1}.
$$

每个 $\mathbf M_j(E)$ 是完全正、迹不增的映射，并且

$$
\sum_{n=1}^{m}
(\mathcal C_j\mathcal N_j^{\,n-1})^*(I)
=
I-(\mathcal N_j^*)^m(I)
\longrightarrow I.
$$

在有限维映射空间中，这个正项级数还按范数收敛：若记
$K_{j,n}=\mathcal C_j\mathcal N_j^{\,n-1}$，则
$\|K_{j,n}\|_\diamond\le\operatorname{Tr}K_{j,n}^*(I)$，而右侧的级数总和为输入空间维数。因此对不交 Borel 集的可数并，$\mathbf M_j$ 按映射范数可数可加；这使上面的集合函数确实是算子值测度，而不是只对有限集合定义的形式和。

所以 $\mathbf M_j([0,\infty))=\Xi_{\Gamma_j}$ 是迹保持通道；对密度输入，取迹后的标量测度总质量为一。若 $f\ge0$，则 $\mathbf M_j[f]$ 是完全正映射；$0\le f\le1$ 时它还迹不增。一般复值 $f$ 只定义一个线性测试响应，不宣称其正性。这里的 $\epsilon_j$ 是内部谱泄漏标度，不是未经标定的物理秒。

在第 115 节的谱投影记号下，置

$$
r_j=1-\epsilon_j,
\qquad
\mathcal P_j(X)=\sigma_j\operatorname{Tr}(G_jX),
$$

$$
\mathcal B_j=\mathcal N_j(\operatorname{id}-\mathcal P_j).
$$

则

$$
\boxed{
\mathcal N_j^{\,n-1}
=
r_j^{\,n-1}\mathcal P_j
+
\mathcal B_j^{\,n-1}(\operatorname{id}-\mathcal P_j).
}
\tag{122.3}
$$

式（122.3）是线性映射的代数谱分解：它把实际点击映射的传播拆成慢本征项与稳定余项。有限 $j$ 时稳定余项一般不是正映射，也不是可单独读取的仪器分支；两项只有相加后才等于同一个实际事件映射。式（123.2）中的两个正分量是取极限后才出现的标记测度分解。

**引理 122.2（稳定尾的统一几何界）。** 存在 $q\in(0,1)$、$C<\infty$ 和 $j_0$，使得对 $j\ge j_0$ 及所有 $m\ge0$，

$$
\boxed{
\|\mathcal B_j^m\|_\diamond\le Cq^m.
}
\tag{122.4}
$$

### 证明

第 115 节的稳定谱与 $1$ 一致分离，且 $\mathcal B_j$ 在固定二维活动记忆所诱导的有限维算子空间中连续趋向边界稳定块 $\mathcal B_*=0$。取一个严格包住所有充分大的 $j$ 的稳定谱的圆周 $|z|=q<1$。有限维 resolvent 在该紧圆周上统一有界，Cauchy 积分公式给出

$$
\mathcal B_j^m
=
\frac1{2\pi i}\int_{|z|=q}z^m(zI-\mathcal B_j)^{-1}\,dz,
$$

从而得到式（122.4）。证毕。

---

## 123. 时间—后继的算子值弱极限

**定理 123.1（标记弱极限）。** 对每个固定的有界连续函数 $f:[0,\infty)\to\mathbb C$，测试响应作为线性映射在完整 diamond 范数中满足

$$
\boxed{
\mathbf M_j[f](X)\longrightarrow
f(0)\operatorname{Tr}(Q_*X)P_0
+
\left(\int_0^\infty f(t)e^{-t}\,dt\right)
\operatorname{Tr}(P_*X)\zeta.
}
\tag{123.1}
$$

等价地，$\mathbf M_j$ 弱收敛到算子值测度

$$
\boxed{
\mathbf M_\infty(X)
=
\delta_0\,\operatorname{Tr}(Q_*X)P_0
+
e^{-t}\,dt\,\operatorname{Tr}(P_*X)\zeta.
}
\tag{123.2}
$$

### 证明

将式（122.3）代入式（122.2），得到

$$
\mathbf M_j[f](X)
=
a_j(f)\,\zeta_j\operatorname{Tr}(G_jX)
+\mathbf S_j[f](X),
\tag{123.3}
$$

其中

$$
a_j(f)=\epsilon_j\sum_{n\ge1}f(\epsilon_j n)r_j^{\,n-1},
$$

$$
\mathbf S_j[f](X)
=
\sum_{n\ge1}f(\epsilon_j n)
\mathcal C_j\mathcal B_j^{\,n-1}(\operatorname{id}-\mathcal P_j)(X).
$$

先处理慢项。对任意固定 $L>0$，在 $0\le\epsilon_j n\le L$ 上，

$$
(1-\epsilon_j)^{n-1}
\longrightarrow e^{-\epsilon_j n}
$$

一致成立；因此有限区间上的和是黎曼和。尾部由

$$
\epsilon_j\sum_{n>L/\epsilon_j}(1-\epsilon_j)^{n-1}
\le e^{-L/2}
$$

控制，充分大的 $j$ 上该界与 $f$ 无关。先令 $j\to\infty$，再令 $L\to\infty$，得到

$$
a_j(f)\longrightarrow
\int_0^\infty f(t)e^{-t}\,dt.
\tag{123.4}
$$

因为 $G_j\to P_*$、$\zeta_j\to\zeta$，慢项趋向式（123.1）的第二项。

再处理稳定项。由式（122.4），对任意固定 $N$，前 $N$ 项满足

$$
\sum_{n=1}^{N}
\bigl(f(\epsilon_j n)-f(0)\bigr)
\mathcal C_j\mathcal B_j^{\,n-1}(\operatorname{id}-\mathcal P_j)
\longrightarrow0.
$$

其余项的范数不超过

$$
2\|f\|_\infty C'\sum_{n>N}q^{n-1},
$$

其中 $C'$ 吸收 $\mathcal C_j$ 与 $\operatorname{id}-\mathcal P_j$ 的统一有界范数；可先取 $N$ 很大使其任意小。因此，利用

$$
\sum_{m\ge0}\mathcal B_j^m(\operatorname{id}-\mathcal P_j)
=
\mathcal R_j,
$$
有

$$
\mathbf S_j[f]
-
f(0)\mathcal C_j\mathcal R_j
\longrightarrow0.
$$

第 115 节的稳定 resolvent 连续性直接给出

$$
\mathcal C_j\mathcal R_j
\longrightarrow
\mathcal C_*(\operatorname{id}-\mathcal P_*).
$$

第 106 节的边界分支分类于是给

$$
\mathcal C_*(\operatorname{id}-\mathcal P_*)(X)
=
\operatorname{Tr}(Q_*X)P_0.
\tag{123.5}
$$

这得到式（123.1）。所有估计在张量任意参考系统后仍成立；输入维数固定时，有限维完全范数与所用线性映射范数等价，所以收敛是完整 diamond 收敛。证毕。

**推论 123.2（终端化只是取 $f=1$ 的边缘）。** 令 $f\equiv1$，则

$$
\mathbf M_j[1](X)=\Xi_{\Gamma_j}(X)
\longrightarrow
\operatorname{Tr}(Q_*X)P_0+\operatorname{Tr}(P_*X)\zeta,
$$

这正是式（115.3）（定理 115.2）的终端通道极限。若只取标量迹，则首次点击的缩放时间律弱收敛为

$$
\boxed{
\mu_\infty^\rho
=
\operatorname{Tr}(Q_*\rho)\,\delta_0
+
\operatorname{Tr}(P_*\rho)e^{-t}\,dt.
}
\tag{123.6}
$$

因此“时间被丢弃”不是说时间关系不存在，而是把同一标记对象作用于常函数 $1$。

**推论 123.3（远离零的有限时间窗）。** 对 $0<a<b<\infty$，令 $I=[a,b]$。则在完整 diamond 范数中

$$
\boxed{
\sum_{n:\,a\le\epsilon_j n\le b}
\mathcal C_j\mathcal N_j^{\,n-1}(X)
\longrightarrow
(e^{-a}-e^{-b})\operatorname{Tr}(P_*X)\zeta.
}
\tag{123.7}
$$

### 证明

慢项是截断几何和，其系数趋向 $e^{-a}-e^{-b}$。稳定项由式（122.4）不超过 $Cq^{a/\epsilon_j}$，趋向零。边界端点的取整误差至多一个几何项，亦趋向零。证毕。

这里的快分支已经全部压到缩放时间零；任何固定的正时间窗只看见慢分支。

---

## 124. 晚事件条件化会同时筛选输入扇区和量子后继

**定理 124.1（固定正缩放时间的条件后继）。** 取整数 $n_j\ge1$，满足

$$
\epsilon_jn_j\longrightarrow s\in(0,\infty).
$$

若 $X\succeq0$ 且 $p=\operatorname{Tr}(P_*X)>0$，则

$$
\boxed{
\frac{\mathcal C_j\mathcal N_j^{\,n_j-1}(X)}
{\operatorname{Tr}[\mathcal C_j\mathcal N_j^{\,n_j-1}(X)]}
\longrightarrow\zeta.
}
\tag{124.1}
$$

更一般地，对任意有限参考系统 $R$ 和固定的正迹类联合输入 $\omega_{RA}\succeq0$（以下取密度算子），若

$$
\omega_R^*
=
\operatorname{Tr}_A[
(I_R\otimes P_*)\omega_{RA}(I_R\otimes P_*)
],
\qquad
p=\operatorname{Tr}\omega_R^*>0,
$$

则对充分大的 $j$ 条件事件概率为正，且条件后的联合输出在迹范数中满足

$$
\boxed{
\frac{(\operatorname{id}_R\otimes\mathcal C_j\mathcal N_j^{\,n_j-1})(\omega_{RA})}
{\operatorname{Tr}[(\operatorname{id}_R\otimes\mathcal C_j\mathcal N_j^{\,n_j-1})(\omega_{RA})]}
\longrightarrow
\frac{\omega_R^*}{p}\otimes\zeta.
}
\tag{124.2}
$$

### 证明

式（122.3）给慢主项

$$
r_j^{\,n_j-1}\epsilon_j\zeta_j\operatorname{Tr}(G_jX).
$$

因 $\epsilon_jn_j\to s$，有 $r_j^{n_j-1}\to e^{-s}$，而 $\operatorname{Tr}(G_jX)\to p$。稳定项由式（122.4）为 $O(q^{n_j})=o(\epsilon_j)$。所以分子为

$$
\epsilon_je^{-s}p\,\zeta+o(\epsilon_j),
$$

其迹为 $\epsilon_je^{-s}p+o(\epsilon_j)$，得到式（124.1）。

对联合输入，慢项变为

$$
r_j^{n_j-1}\epsilon_j\,
\omega_{R,j}^{G}\otimes\zeta_j,
\qquad
\omega_{R,j}^{G}
=
\operatorname{Tr}_A[
(I_R\otimes G_j^{1/2})\omega_{RA}(I_R\otimes G_j^{1/2})
],
$$

且 $\omega_{R,j}^{G}\to\omega_R^*$。同样的稳定尾估计在参考张量后成立；慢项的迹为 $\epsilon_je^{-s}p+o(\epsilon_j)>0$，归一化并在迹范数中取极限，得到式（124.2）。证毕。

这说明“晚到”不是一次单纯的时间条件化：它把输入筛到边界慢扇区，同时把点击后的量子后继筛到同一个 $\zeta$。若 $\zeta=P_0$，时间仍可揭示输入来自慢扇区的权重；若 $\zeta\ne P_0$，时间条件化和后继输出共同保留这一临界关系。

## 125. AHH：终端边缘、时间标记和后继不是三个对象

**关系结论 125.1（标记对象的边缘一致性）。** 在指定名义仪器、完整二维活动记忆、两种实际记录、齐次重复以及趋近同一个最近失效相位的非失效序列条件下，同一实际仪器序列有三种相互兼容的读法：

$$
\boxed{
\begin{aligned}
\text{时间—后继标记测度}
&\longrightarrow
\text{取迹：缩放首次事件时间律},\\
\text{时间—后继标记测度}
&\xrightarrow{\ f\equiv1\ }
\text{终端量子通道},\\
\text{时间—后继标记测度}
&\xrightarrow{\text{晚事件条件化}}
\text{经慢扇区效果条件化的参考系统与点击后继的联合态}.
\end{aligned}
}
$$

AHH 在于：**终端通道的“量子后继自由”与事件时间的“指数慢尾”并不是两个可以独立拼接的结果；它们是同一算子值测度的两个边缘。** 有限 $j$ 的谱余项不被解释成正的“快事件分支”；只有极限标记测度才分解为时间零的 $P_0$ 原子和携带 $\zeta$ 的指数尾。晚事件条件化还会更新参考系统并选择后继。

这也说明三个恢复任务必须分开：

$$
\boxed{
\begin{array}{c}
\text{只读时间}\\
\text{终端量子输出}\\
\text{联合时间与后继}
\end{array}
\quad
\text{分别读取同一标记对象的不同边缘与条件层。}
}
$$

只读时间可以恢复慢扇区的权重，却不能一般从时间记录恢复 $\zeta$；只读终端输出把快、慢事件的时间位置求和掉。若已知 $P_*$ 且完整识别了极限终端通道，则可以由 $\Lambda(P_*)=\zeta$ 得到后继态，但这仍不恢复事件时间与后继之间的联合标记关系；联合接口同时保留指数时间尺度、时间零原子、参考更新和量子后继。

**来源与边界 125.2。** 本批只使用第 93、106、115 节的有限维谱投影、稳定 resolvent 和原始点击分支分类，在这些已声明接口上新增算子值弱极限与晚事件条件化。弱收敛是针对每个固定有界连续测试函数的完整 diamond 收敛，不是对测试函数取一致上确界。对任意归一化输入，令

$$
D_j=\{\epsilon_j n:n\ge1\},
\qquad
D=\bigcup_jD_j.
$$

则 $0\notin D$、每个有限 $j$ 的离散时间律满足 $\mu_j(D)=1$，而极限测度满足 $\mu_\infty(D)=0$；在 $d_{\rm TV}=\sup_A|\mu(A)-\nu(A)|$ 约定下，$d_{\rm TV}(\mu_j,\mu_\infty)=1$。因此不声称在总变差或支配总变差的测度范数中收敛。时间仍以 $\epsilon_j n$ 的内部标度表示，物理秒需要额外钟标定。

本批不新增 Lean、消化、覆盖或冻结内容；不推广到无限维记忆、时变控制、非齐次仪器或未声明的完整时间记录认证问题，也不主张文献原创性。

## 追加锚（本行以下为增补区）

## 126. 临界标记测度因子化为两个时间扇区

第 123 节的极限公式还可以进一步压缩。它的时间坐标是连续的，但它对输入的作用只通过两个互相正交的边界扇区发生：在时间零出现的快速扇区，以及产生指数尾的慢扇区。

**定义 126.1（两个扇区的时间系数与准备映射）。** 对 Borel 集 $E\subseteq[0,\infty)$，置

$$
\alpha(E)=\mathbf 1_{\{0\in E\}},
\qquad
\beta(E)=\int_Ee^{-t}\,dt.
$$

定义两个固定的完全正映射

$$
\mathsf F(X)=\operatorname{Tr}(Q_*X)P_0,
\qquad
\mathsf S(X)=\operatorname{Tr}(P_*X)\zeta.
$$

这里的 $\mathsf F$ 与 $\mathsf S$ 分别表示快速和慢速边界扇区的点击后继。定义极限标记仪器为

$$
\boxed{
\mathbf M_\infty(E)=\alpha(E)\mathsf F+\beta(E)\mathsf S.
}
\tag{126.1}
$$

这一定义直接给出一个算子值测度。它不是把有限 $j$ 的离散测度在每个 Borel 集上逐点取极限所得的额外断言；第 123 节的弱极限含义是，对每个固定有界连续 $f$，有

$$
\mathbf M_\infty[f](X)
=f(0)\mathsf F(X)
+\left(\int_0^\infty f(t)e^{-t}\,dt\right)\mathsf S(X).
\tag{126.2}
$$

**定理 126.2（标记对象的二元因子化）。** 对任意 Borel 集 $E$，$\mathbf M_\infty(E)$ 完全正且迹不增，并且

$$
\mathbf M_\infty([0,\infty))=\mathsf F+\mathsf S
$$

是迹保持通道。对任意密度矩阵 $\rho$，其标量时间测度为

$$
\boxed{
\mu_\infty^\rho
=q_\rho\,\delta_0+p_\rho e^{-t}\,dt,
\qquad
q_\rho=\operatorname{Tr}(Q_*\rho),
\quad
p_\rho=\operatorname{Tr}(P_*\rho).
}
\tag{126.3}
$$

并且 $q_\rho+p_\rho=1$。因此，极限标记对象可以因子化为

$$
\boxed{
X
\xmapsto{\ \mathsf d\ }
\bigl(\operatorname{Tr}(Q_*X),\operatorname{Tr}(P_*X)\bigr)
\xmapsto{\ \mathsf p_E\ }
\alpha(E)\operatorname{Tr}(Q_*X)P_0
+\beta(E)\operatorname{Tr}(P_*X)\zeta.
}
\tag{126.4}
$$

### 证明

$\mathsf F$ 与 $\mathsf S$ 是正映射的非负标量倍和，因而完全正。对 $X\succeq0$，

$$
\operatorname{Tr}\mathsf F(X)=\operatorname{Tr}(Q_*X),
\qquad
\operatorname{Tr}\mathsf S(X)=\operatorname{Tr}(P_*X).
$$

由于 $0\le\alpha(E)\le1$ 且 $0\le\beta(E)\le1$，两项的迹之和不超过 $\operatorname{Tr}X$，所以 $\mathbf M_\infty(E)$ 迹不增。对全集，$\alpha=1$、$\beta=1$，且 $Q_*+P_*=I$，故总映射保迹。

把这两个迹写成 $q_\rho,p_\rho$ 即得式（126.3）。式（126.4）只是把式（126.1）的两个系数先读出，再执行相应的准备映射。证毕。

**推论 126.3（无限时间坐标的二元状态作用）。** 对任意有界 Borel 测试函数 $f$，形式上定义的极限响应都只依赖于两个数

$$
\alpha_f=f(0),
\qquad
\beta_f=\int_0^\infty f(t)e^{-t}\,dt,
$$

并满足

$$
\mathbf M_\infty[f](X)=\alpha_f\mathsf F(X)+\beta_f\mathsf S(X).
\tag{126.5}
$$

若 $f\ge0$，该响应为完全正；若 $0\le f\le1$，它迹不增。时间函数的其余细节只影响指数尾上的经典加权，不再产生新的输入方向。

这不是说指数等待律退化成单个时间点。对慢扇区，$\beta_f$ 仍然是完整的 Laplace 型时间读数；它说明的是：在输入—输出关系的量子部分，全部时间读数通过 $\mathsf S$ 的同一个量子后继进入。

---

## 127. 参考系统下，任意时间窗都只混合两个条件后继

前一节的二元因子化对没有参考系统的状态已经成立。加入参考系统后，时间窗还会更新参考边缘；这个更新同样只沿快速和慢速两个扇区进行。

**定义 127.1（参考扇区压缩）。** 对有限参考系统 $R$ 和联合正算子 $\omega_{RA}\succeq0$，置

$$
\omega_R^Q
=\operatorname{Tr}_A\bigl[(I_R\otimes Q_*)\omega_{RA}(I_R\otimes Q_*)\bigr],
$$

$$
\omega_R^P
=\operatorname{Tr}_A\bigl[(I_R\otimes P_*)\omega_{RA}(I_R\otimes P_*)\bigr].
$$

记

$$
q=\operatorname{Tr}\omega_R^Q,
\qquad
p=\operatorname{Tr}\omega_R^P.
$$

当 $\omega_{RA}$ 是密度矩阵时，$p+q=1$。

**定理 127.2（时间窗条件化的参考—后继公式）。** 对任意 Borel 集 $E$，有

$$
\boxed{
(\operatorname{id}_R\otimes\mathbf M_\infty(E))(\omega_{RA})
=\alpha(E)\,\omega_R^Q\otimes P_0
+\beta(E)\,\omega_R^P\otimes\zeta.
}
\tag{127.1}
$$

令

$$
Z_E=\alpha(E)q+\beta(E)p.
$$

若 $Z_E>0$，则条件于事件 $E$ 的归一化联合后继为

$$
\boxed{
\omega_{RA\mid E}
=\frac{\alpha(E)\,\omega_R^Q\otimes P_0
+\beta(E)\,\omega_R^P\otimes\zeta}{Z_E}.
}
\tag{127.2}
$$

特别地，若 $E\subseteq(0,\infty)$ 且 $\beta(E)>0$，则

$$
\boxed{
\omega_{RA\mid E}
=\frac{\omega_R^P}{p}\otimes\zeta,
}
\tag{127.3}
$$

只要 $p>0$。正时间窗的形状、长度和位置只改变该事件的发生概率 $\beta(E)p$，不改变其条件量子后继。

### 证明

对任意 $Y_R\otimes X_A$，有

$$
(\operatorname{id}_R\otimes\mathsf F)(Y_R\otimes X_A)
=Y_R\operatorname{Tr}(Q_*X_A)P_0,
$$

$$
(\operatorname{id}_R\otimes\mathsf S)(Y_R\otimes X_A)
=Y_R\operatorname{Tr}(P_*X_A)\zeta.
$$

线性延拓到 $\omega_{RA}$，并用部分迹的 sandwich 恒等式，得到

$$
(\operatorname{id}_R\otimes\mathsf F)(\omega_{RA})=\omega_R^Q\otimes P_0,
$$

$$
(\operatorname{id}_R\otimes\mathsf S)(\omega_{RA})=\omega_R^P\otimes\zeta.
$$

代入式（126.1）即得式（127.1）。取迹得到 $Z_E$；在 $Z_E>0$ 时除以该正数，得到式（127.2）。当 $E$ 不含零时 $\alpha(E)=0$，再用 $\beta(E)>0$ 与 $p>0$ 即得式（127.3）。证毕。

**推论 127.3（正时间条件化的参考信息与系统后继分离）。** 在式（127.3）中，参考系统保留的是慢扇区压缩 $\omega_R^P/p$，受测系统固定为 $\zeta$。因此晚事件条件化可以改变参考系统的状态，却不能把一个新的系统后继从指数时间位置中读出来。

相反，含有时间零的事件窗会混合两个后继。例如对 $E=[0,a]$，$a>0$，有

$$
\omega_{RA\mid[0,a]}
=\frac{\omega_R^Q\otimes P_0+(1-e^{-a})\omega_R^P\otimes\zeta}
{q+(1-e^{-a})p},
\tag{127.4}
$$

只要分母正。早期有限分辨率因此不是简单地把“快事件”读成时间零；它把时间零原子与慢尾在同一事件格中混合。

---

## 128. 全部临界标记记录的观察商只有一个慢扇区人口

因果边界是否保留全部时间—后继标记，取决于它能否区分输入。临界极限给出一个精确的观察等价关系。

**定理 128.1（无参考输入的标记观察等价）。** 对密度矩阵 $\rho,\sigma$，以下条件等价：

$$
\mathbf M_\infty(E)(\rho)=\mathbf M_\infty(E)(\sigma)
\quad\text{对所有 Borel 集 }E;
\tag{128.1}
$$

$$
\operatorname{Tr}(P_*\rho)=\operatorname{Tr}(P_*\sigma).
\tag{128.2}
$$

等价地，全部有界连续时间测试函数及其点击后继输出都相同，当且仅当两输入具有相同的慢扇区人口。

对一般 Hermitian 输入差值 $\Delta$，全部标记响应为零的充要条件是

$$
\boxed{
\operatorname{Tr}(Q_*\Delta)=0,
\qquad
\operatorname{Tr}(P_*\Delta)=0.
}
\tag{128.3}
$$

### 证明

若式（128.2）成立，由迹为一且 $Q_*+P_*=I$，两态的 $Q_*$ 人口也相等；代入式（126.1）即可得到式（128.1）。

反过来，取 $E=(0,\infty)$，有 $\alpha(E)=0$、$\beta(E)=1$，从而

$$
\mathbf M_\infty(E)(\rho)=\operatorname{Tr}(P_*\rho)\zeta.
$$

两边相等给出式（128.2）。对一般 Hermitian 差值，取 $E=\{0\}$ 与 $E=(0,\infty)$，分别得到两个迹条件；反向代入式（126.1）显然成立。证毕。

若只假定所有有界连续测试函数的响应相同，也可取 $f(t)=e^{-t}$；其两个系数为 $f(0)=1$ 与 $\int_0^\infty e^{-2t}dt=1/2$，因而能区分两个不同的慢扇区人口。这说明这里的 Borel 集表述与连续测试函数表述给出同一个观察商。

**例 128.2（相同临界标记、不同相干输入）。** 在二维活动空间中取 $P_*=|p\rangle\langle p|$、$Q_*=|q\rangle\langle q|$。固定 $0<p<1$，定义

$$
|\psi_\phi\rangle
=\sqrt p\,|p\rangle+e^{i\phi}\sqrt{1-p}\,|q\rangle,
\qquad
\rho_\phi=|\psi_\phi\rangle\langle\psi_\phi|.
$$

不同的 $\phi$ 给出不同的纯态；当 $\phi-\phi'\notin2\pi\mathbb Z$ 时，通常 $\rho_\phi\ne\rho_{\phi'}$。但

$$
\mathbf M_\infty(E)(\rho_\phi)
=\mathbf M_\infty(E)(\rho_{\phi'})
$$

对所有 $E$ 成立。临界时间—后继接口完全删去了 $P_*\!-\!Q_*$ 之间的相对相位。

**定理 128.3（带参考输入的观察商）。** 对两个密度矩阵 $\omega_{RA}$ 与 $\widetilde\omega_{RA}$，全部参考—时间—后继标记输出相同，当且仅当

$$
\boxed{
\omega_R^Q=\widetilde\omega_R^Q,
\qquad
\omega_R^P=\widetilde\omega_R^P.
}
\tag{128.4}
$$

因此参考接口可以保留两个扇区的条件参考状态，但仍然不读取系统输入的跨扇区相干块。

### 证明

若两个压缩算子相同，式（127.1）立即给出全部事件集的输出相同。

反之，取 $E=\{0\}$ 得

$$
\omega_R^Q\otimes P_0
=\widetilde\omega_R^Q\otimes P_0,
$$

从而 $\omega_R^Q=\widetilde\omega_R^Q$；取 $E=(0,\infty)$ 得

$$
\omega_R^P\otimes\zeta
=\widetilde\omega_R^P\otimes\zeta,
$$

从而 $\omega_R^P=\widetilde\omega_R^P$。证毕。

**关系解释。** “保留整个临界时间记录”与“恢复整个临界输入”不是同一命题。对无参考输入，连续时间记录的观察商只有一个实数 $p=\operatorname{Tr}(P_*\rho)$；对带参考输入，观察商扩大为两个参考算子 $\omega_R^Q,\omega_R^P$，但跨扇区相干仍在该接口上不可见。

---

## 129. 有限时间分辨率把理想扇区识别变成贝叶斯混合

理想极限的时间零原子与正时间指数尾互相奇异，因此精确记录任意 $t>0$ 会确定事件来自慢扇区。有限时间分辨率会把一段含零的早期窗口与慢尾合并；该合并可以精确计算。

**定理 129.1（早晚窗口的后验与后继）。** 固定 $a>0$，对无参考密度输入 $\rho$ 记

$$
p=\operatorname{Tr}(P_*\rho),
\qquad
q=1-p.
$$

以

$$
E_a=[0,a],
\qquad
L_a=(a,\infty)
$$

作为二元时间读数，则

$$
\boxed{
\Pr(E_a)=1-pe^{-a},
\qquad
\Pr(L_a)=pe^{-a}.
}
\tag{129.1}
$$

在 $\Pr(E_a)>0$ 时，早窗口中来自慢扇区的后验人口为

$$
\boxed{
\Pr(P_*\mid E_a)
=\frac{p(1-e^{-a})}{1-pe^{-a}}.
}
\tag{129.2}
$$

若 $p>0$，晚窗口必来自慢扇区：

$$
\boxed{\Pr(P_*\mid L_a)=1.}
\tag{129.3}
$$

相应的系统条件后继为

$$
\boxed{
\rho_{\mid E_a}
=\frac{qP_0+p(1-e^{-a})\zeta}{1-pe^{-a}},
\qquad
\rho_{\mid L_a}=\zeta.
}
\tag{129.4}
$$

### 证明

由式（126.3），快速扇区在 $E_a$ 上的质量为 $q$，在 $L_a$ 上为零；慢扇区在两窗上的质量分别为 $p(1-e^{-a})$ 与 $pe^{-a}$。相加得到式（129.1），以慢质量除以早窗总质量得到式（129.2），晚窗的快速质量为零故得式（129.3）。将同样的两个质量乘以后继 $P_0,\zeta$，再归一化即得式（129.4）。证毕。

**推论 129.2（分辨率的单调作用）。** 对固定 $p\in(0,1)$，早窗的慢扇区后验

$$
\pi_p(a)=\frac{p(1-e^{-a})}{1-pe^{-a}}
$$

严格随 $a$ 增加而增加，并满足

$$
\lim_{a\downarrow0}\pi_p(a)=0,
\qquad
\lim_{a\to\infty}\pi_p(a)=p.
$$

### 证明

置 $u=e^{-a}$。直接求导得

$$
\frac{d\pi_p}{da}
=\frac{p(1-p)e^{-a}}{(1-pe^{-a})^2}>0.
$$

两个极限由 $e^{-a}\to1$ 与 $e^{-a}\to0$ 得到。证毕。

有限分辨率越早截断，早窗越接近纯时间零的快速记录；把窗口放宽，便逐渐把慢尾早期部分混入同一经典标签。晚窗始终保持慢扇区纯度，却以概率 $pe^{-a}$ 变得稀有。

---

## 130. AHH：连续时间的量子观察商只有一个人口坐标

**关系结论 130.1（时间细节与扇区信息的分离）。** 在第 115 节的指定名义仪器、完整二维活动记忆、两种实际记录、齐次重复及单一最近失效相位的临界序列条件下，极限标记仪器同时具有两种看似不同的结构：

$$
\boxed{
\begin{aligned}
\text{在经典时间侧：}
&\quad \delta_0\ \text{与}\ e^{-t}dt\ \text{保留完整的零点原子和指数形状};\\
\text{在量子输入侧：}
&\quad \rho\mapsto\operatorname{Tr}(P_*\rho)\ \text{是全部无参考标记输出的观察商};\\
\text{在参考侧：}
&\quad \omega_{RA}\mapsto(\omega_R^Q,\omega_R^P)\ \text{是全部参考标记输出的观察商}.
\end{aligned}
}
\tag{130.1}
$$

AHH 在于：**临界极限没有把连续时间坐标变成更多的量子状态坐标。时间仍然可以精确描述“慢事件在指数尾的哪一处发生”，但所有这些正时间位置共享同一个点击后继 $\zeta$，对无参考输入也共享同一个慢人口 $\operatorname{Tr}(P_*\rho)$。因此，时间记录的连续细节属于事件律；量子关系的可辨识信息在该接口上已经压缩为扇区人口。**

这不是说跨扇区相干在整个关系体中不存在。它只是被当前临界标记接口的观察商消去；若允许访问更细的有限 $j$ 过渡结构、其他控制或不同探测接口，原本被合并的关系可能重新可见。因而“观察商只有一个人口坐标”是一个接口相对的充分性结论，不是全体内部状态的本体定义。

第 126—129 节还给出一个更操作性的版本：任何 Borel 时间窗只通过 $(\alpha(E),\beta(E))$ 混合两个条件后继；正时间窗把参考系统筛到慢扇区并固定系统后继，含零窗口则按贝叶斯权重混合 $P_0$ 与 $\zeta$。这把“晚事件会选择什么”与“早期有限分辨率会混合什么”放在同一标记对象中。

**来源与边界 130.2。** 本批只把第 123—125 节的标记弱极限改写为二元扇区因子化，并在有限参考系统、正迹条件输入及固定时间窗上作直接推导。没有把有限 $j$ 的离散测度宣称为逐 Borel 集收敛，没有把临界极限的观察商推广为任意仪器或无限维记忆的充分统计，也没有把时间窗口的贝叶斯后验当作物理钟的动力学定律。本批仍是纯理论 Markdown，不新增 Lean、消化、coverage 或 freeze 内容。

## 追加锚（本行以下为增补区）
