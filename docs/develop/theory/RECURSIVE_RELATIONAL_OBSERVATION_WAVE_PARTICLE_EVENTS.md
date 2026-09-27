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

## 131. 后续控制作用在标记测度上，而不只作用在终端通道上

第 126—130 节的观察商是相对于“读完事件后不再使用精确时间”的接口得到的。若内部观察者把事件时间送入下一次控制，后续关系应作用在整个时间—后继标记对象上。

**定义 131.1（时间依赖的后续族）。** 设输出空间为 $\mathcal H_B$。对每个 $t\ge0$，给定一个从当前点击输出空间到 $\mathcal H_B$ 的完全正迹不增映射 $\Lambda_t$。假定 $t\mapsto\Lambda_t$ 在有限维线性映射空间中可测且有统一范数界。

对极限标记仪器定义时间推送后的续接映射

$$
\boxed{
\mathcal K_{\Lambda_\bullet}(X)
=
\Lambda_0\bigl(\mathbf M_\infty(\{0\})(X)\bigr)
+
\int_{(0,\infty)}
\Lambda_t\bigl(\mathbf M_\infty(dt)(X)\bigr).
}
\tag{131.1}
$$

积分是有限维映射空间中的 Bochner 积分。若每个 $\Lambda_t$ 都保迹，则 $\mathcal K_{\Lambda_\bullet}$ 也保迹。

**定理 131.2（时间敏感续接的二扇区公式）。** 在第 126 节的临界极限下，

$$
\boxed{
\mathcal K_{\Lambda_\bullet}(X)
=
\operatorname{Tr}(Q_*X)\Lambda_0(P_0)
+
\operatorname{Tr}(P_*X)
\int_0^\infty e^{-t}\Lambda_t(\zeta)\,dt.
}
\tag{131.2}
$$

对有限参考系统 $R$ 和联合输入 $\omega_{RA}$，有

$$
\boxed{
(\operatorname{id}_R\otimes\mathcal K_{\Lambda_\bullet})(\omega_{RA})
=
\omega_R^Q\otimes\Lambda_0(P_0)
+
\int_0^\infty e^{-t}\,
\omega_R^P\otimes\Lambda_t(\zeta)\,dt.
}
\tag{131.3}
$$

若每个 $\Lambda_t$ 为通道，式（131.2）和（131.3）的迹分别为输入的总迹。

### 证明

由式（126.1），时间零原子为

$$
\mathbf M_\infty(\{0\})(X)=\operatorname{Tr}(Q_*X)P_0,
$$

正时间部分为

$$
\mathbf M_\infty(dt)(X)
=e^{-t}dt\,\operatorname{Tr}(P_*X)\zeta.
$$

将这两式代入定义 131.1，因 $\Lambda_t$ 对算子线性且积分在有限维中可交换，得到式（131.2）。

对联合输入，定理 127.2 的微分形式给出

$$
(\operatorname{id}_R\otimes\mathbf M_\infty)(\omega_{RA})
=
\omega_R^Q\otimes P_0\,\delta_0
+
\omega_R^P\otimes\zeta\,e^{-t}dt.
$$

逐点作用 $\operatorname{id}_R\otimes\Lambda_t$ 并积分，得到式（131.3）。若 $\Lambda_t$ 保迹，则快速项贡献 $\operatorname{Tr}\omega_R^Q$，慢项贡献 $\operatorname{Tr}\omega_R^P\int_0^\infty e^{-t}dt$，两者相加为总迹。证毕。

**推论 131.3（时间盲续接时终端通道足够）。** 若 $\Lambda_t=\Lambda$ 对所有 $t$ 相同，则

$$
\boxed{
\mathcal K_{\Lambda_\bullet}
=
\Lambda\circ\mathbf M_\infty([0,\infty)).
}
\tag{131.4}
$$

此时取 $f\equiv1$ 的终端通道不会丢失该续接所需的信息。若 $\Lambda_t$ 随 $t$ 变化，式（131.2）一般不能由 $\mathbf M_\infty([0,\infty))$ 单独决定。

这一区分补充了第 125 节：终端化是标记对象的一个边缘；只有当所有后续操作对时间标签相同，它才是相对于后续任务的充分边界。

---

## 132. 时间敏感续接可以把被终端化丢掉的指数形状重新变成量子输出

上一定理给出一般公式。下面的二维例子证明，时间被求和掉以后，确实可能失去后续任务所需的关系，而不是只失去一个叙述标签。

**定理 132.1（旋转族反例）。** 假定慢后继为 $\zeta=P_0$，在输出 qubit 上取

$$
U_t=e^{-itY},
\qquad
\Lambda_t(X)=U_tXU_t^\dagger,
$$

其中 $Y$ 为 Pauli $y$ 矩阵。对慢扇区输入 $P_*$，时间敏感续接的输出为

$$
\bar\rho
=
\int_0^\infty e^{-t}U_tP_0U_t^\dagger\,dt
=
\begin{pmatrix}
3/5&1/5\\
1/5&2/5
\end{pmatrix}.
\tag{132.1}
$$

而先终端化再使用时间盲续接 $\Lambda_0$ 的输出为 $P_0$。两者不同，且

$$
\boxed{
\frac12\|\bar\rho-P_0\|_1=\frac{\sqrt5}{5}>0.
}
\tag{132.2}
$$

### 证明

在计算基中，

$$
U_t|0\rangle
=\cos t\,|0\rangle+\sin t\,|1\rangle,
$$

所以

$$
U_tP_0U_t^\dagger
=
\begin{pmatrix}
\cos^2t&\sin t\cos t\\
\sin t\cos t&\sin^2t
\end{pmatrix}.
$$

使用

$$
\int_0^\infty e^{-t}\,dt=1,
\qquad
\int_0^\infty e^{-t}\cos(2t)\,dt=\frac15,
\qquad
\int_0^\infty e^{-t}\sin(2t)\,dt=\frac25,
$$

得到

$$
\int_0^\infty e^{-t}\cos^2t\,dt=\frac35,
\quad
\int_0^\infty e^{-t}\sin^2t\,dt=\frac25,
\quad
\int_0^\infty e^{-t}\sin t\cos t\,dt=\frac15.
$$

这给出式（132.1）。先取 $f\equiv1$ 得到慢后继 $P_0$，再施加固定 $\Lambda_0$ 仍为 $P_0$，所以两输出不同。

差矩阵为

$$
\bar\rho-P_0
=
\begin{pmatrix}
-2/5&1/5\\
1/5&2/5
\end{pmatrix},
$$

其本征值为 $\pm\sqrt5/5$，故半迹范数为式（132.2）。证毕。

**关系含义。** 这里没有改变第 126 节的终端量子后继：慢事件在事件接口上仍都交付 $P_0$。改变的是观察者是否把事件发生的内部时间用于下一次酉控制。因而

$$
\boxed{
\text{“终端后继相同”}
\not\Rightarrow
\text{“所有时间敏感续接相同”}.
}
$$

这也不是说每个物理观察者都能无误地实现 $\Lambda_t$；它是一个指定的合法续接族下的充分性反例。

---

## 133. 受限的时间控制族只需要有限个指数矩

任意时间敏感续接需要保留完整标记测度，但许多控制族只使用有限个时间函数。此时可以把连续时间压缩为有限个矩，而不损失该控制族的输出。

**定义 133.1（有限时间函数控制族）。** 固定有界可测函数

$$
f_0,\ldots,f_m:[0,\infty)\to\mathbb C
$$

及固定线性映射 $\Lambda^{(0)},\ldots,\Lambda^{(m)}$，考虑满足

$$
\boxed{
\Lambda_t=\sum_{k=0}^{m}f_k(t)\Lambda^{(k)}
}
\tag{133.1}
$$

的时间控制族。只保留那些对每个 $t$ 实际上完全正且迹不增的 $\Lambda_t$；式（133.1）本身只是线性展开，不把各 $\Lambda^{(k)}$ 单独宣称为仪器分支。

这里的固定映射 $\Lambda^{(k)}$ 属于已声明的后续合同；式（133.2）所说的边界摘要只压缩事件对象对该合同的时间依赖，不把执行后续控制所需的映射定义本身从模型中删除。

定义时间系数

$$
c_k=f_k(0),
\qquad
\ell_k=\int_0^\infty f_k(t)e^{-t}\,dt.
$$

**定理 133.2（时间函数的有限矩充分性）。** 对式（133.1）的全部续接，极限标记对象只需保留有限数据

$$
\boxed{
\bigl((c_k)_{k=0}^{m},(\ell_k)_{k=0}^{m},P_0,\zeta,\omega_R^Q,\omega_R^P\bigr).
}
\tag{133.2}
$$

更具体地，

$$
\boxed{
\mathcal K_{\Lambda_\bullet}(X)
=
\operatorname{Tr}(Q_*X)\sum_{k=0}^{m}c_k\Lambda^{(k)}(P_0)
+
\operatorname{Tr}(P_*X)\sum_{k=0}^{m}\ell_k\Lambda^{(k)}(\zeta).
}
\tag{133.3}
$$

参考系统版本为

$$
\boxed{
(\operatorname{id}_R\otimes\mathcal K_{\Lambda_\bullet})(\omega_{RA})
=
\omega_R^Q\otimes\sum_{k=0}^{m}c_k\Lambda^{(k)}(P_0)
+
\omega_R^P\otimes\sum_{k=0}^{m}\ell_k\Lambda^{(k)}(\zeta).
}
\tag{133.4}
$$

### 证明

将式（133.1）代入定理 131.2，并交换有限求和与积分：

$$
\begin{aligned}
\int_0^\infty e^{-t}\Lambda_t(\zeta)\,dt
&=\int_0^\infty e^{-t}\sum_{k=0}^{m}f_k(t)\Lambda^{(k)}(\zeta)\,dt\\
&=\sum_{k=0}^{m}\ell_k\Lambda^{(k)}(\zeta).
\end{aligned}
$$

时间零项同理给出

$$
\Lambda_0(P_0)=\sum_{k=0}^{m}c_k\Lambda^{(k)}(P_0).
$$

代回式（131.2）得到式（133.3）；参考系统版本由式（131.3）同样得到。证毕。

**推论 133.3（矩闭包的层级）。** 若允许的后续族由常函数 $f_0\equiv1$ 生成，则只有总终端通道所需的时间零—指数总质量；若加入 $f_1,\ldots,f_m$，每增加一个独立时间函数，最多增加一个指数矩。有限矩摘要是该控制族的一个充分边界，但不自动是所有时间敏感控制的充分边界。

这把“该不该保留时间”改写成一个明确的续接问题：不是时间坐标有一个绝对的信息量，而是允许的后续族决定需要哪些函数评价。

---

## 134. AHH：全息边界的最小形状由后续合同决定

**关系结论 134.1（续接相对的边界充分性）。** 对第 115 节的指定名义仪器、完整二维活动记忆、两种实际记录、齐次重复及单一最近失效相位的临界序列，存在三层边界：

$$
\boxed{
\begin{array}{c|c}
\text{允许的后续合同}&\text{足够的极限边界}\\
\hline
\text{时间盲的固定后续 }\Lambda&\mathbf M_\infty([0,\infty))\\
\text{有限时间函数张成的族}&((c_k),(\ell_k),P_0,\zeta,\omega_R^Q,\omega_R^P)\\
\text{任意有界可测的时间敏感族}&\text{完整时间—后继标记测度 }\mathbf M_\infty
\end{array}
}
\tag{134.1}
$$

第一行由推论 131.3，第二行由定理 133.2，第三行是定义 131.1 对所有合法时间推送的直接充分性结论。

AHH 在于：**全息边界没有脱离后续任务而预先固定的“最终大小”。终端通道是时间盲续接的充分摘要；一旦观察者可以用事件时间选择后续操作，指数尾的函数矩就成为边界内容；若续接族不受限，完整标记测度本身才是能够继续执行的边界。**

这解释了两个看似相反的事实：

$$
\boxed{
\text{终端化可以对一个任务充分，}
\qquad
\text{同时对更大的合法续接族不充分。}
}
$$

第 132 节的旋转族给出了后者的显式反例；第 133 节说明扩大续接族时，所需边界不是抽象地“更多信息”，而是可计算的指数矩坐标。因而观察者的权限、记录格式和后续控制必须一起写入边界定义，不能只给出一个当前密度矩阵便宣称全息恢复。

**来源与边界 134.2。** 本批只对第 126 节定义的极限标记仪器施加有限维、可测且统一有界的后续 CP 族；旋转例子使用二维输出 qubit 和慢后继 $P_0$。没有把时间敏感续接的结论推广到有限 $j$ 的逐事件误差界、无限维控制或未经声明的物理钟读取。本批仍是纯理论 Markdown，不新增 Lean、消化、coverage 或 freeze 内容。

## 追加锚（本行以下为增补区）

## 135. 两次事件的时间—后继关系按扇区转移核组合

第 134 节把后续控制合同分成时间盲和时间敏感两类。若后续任务还要继续运行同一个临界事件协议，第一次点击后的量子后继会成为第二次事件的输入；因此需要把后继对下一次扇区的作用显式写出。

**定义 135.1（临界扇区与转移矩阵）。** 置

$$
\rho_0=P_0,\qquad \rho_1=\zeta,
$$

$$
E_0=Q_*,\qquad E_1=P_*,
$$

并定义两个时间测度

$$
\nu_0=\delta_0,
\qquad
\nu_1(dt)=e^{-t}\,dt.
$$

这里下标 $0$ 表示时间零的快速扇区，下标 $1$ 表示指数慢扇区。固定一个事件之间使用的时间盲续接通道 $\Lambda$，定义扇区转移矩阵

$$
\boxed{
T_{ba}
=
\operatorname{Tr}\bigl(E_b\Lambda(\rho_a)\bigr),
\qquad a,b\in\{0,1\}.
}
\tag{135.1}
$$

每一列都是概率分布：

$$
\sum_{b=0}^{1}T_{ba}=1.
\tag{135.2}
$$

对初态 $\rho$，记首个事件的扇区人口

$$
w_a=\operatorname{Tr}(E_a\rho).
$$

**定理 135.2（两次事件的联合标记公式）。** 先运行一次极限标记仪器，在第一次事件后施加 $\Lambda$，再运行一次同样的极限标记仪器。记两次相对事件时间为 $t_1,t_2$，第二次事件后的未归一化输出为 $\mathbf M^{(2)}_\Lambda(E_1,E_2)(\rho)$。则对任意 Borel 集 $E_1,E_2$，

$$
\boxed{
\mathbf M^{(2)}_\Lambda(E_1,E_2)(\rho)
=
\sum_{a,b\in\{0,1\}}
w_aT_{ba}\,
\nu_a(E_1)\nu_b(E_2)\,\rho_b.
}
\tag{135.3}
$$

若只保留总历时 $t=t_1+t_2$，则

$$
\boxed{
\mathbf T^{(2)}_\Lambda(dt)(\rho)
=
\sum_{a,b}
w_aT_{ba}\,
(\nu_a*\nu_b)(dt)\,\rho_b.
}
\tag{135.4}
$$

### 证明

第一次事件位于扇区 $a$、时间窗 $E_1$ 时，式（126.1）给出的未归一化输出为

$$
w_a\nu_a(E_1)\rho_a.
$$

施加 $\Lambda$ 后，第二次事件位于扇区 $b$ 的概率为

$$
\operatorname{Tr}(E_b\Lambda(\rho_a))=T_{ba}.
$$

第二次事件的时间窗贡献为 $\nu_b(E_2)$，其后继为 $\rho_b$。对 $a,b$ 求和得到式（135.3）。

总历时映射 $(t_1,t_2)\mapsto t_1+t_2$ 把乘积测度 $\nu_a\otimes\nu_b$ 推送为卷积 $\nu_a*\nu_b$，得到式（135.4）。证毕。

**推论 135.3（零时原子与指数尾的卷积）。** 定义

$$
\gamma_0=\delta_0,
\qquad
\gamma_k(dt)
=
\frac{t^{k-1}e^{-t}}{(k-1)!}\,dt
\quad(k\ge1).
$$

则

$$
\nu_a*\nu_b=\gamma_{a+b}.
\tag{135.5}
$$

所以两次事件的总时间由路径中出现了几次慢扇区决定：两次都快给时间零原子，一次慢给单位指数尾，两次都慢给 Erlang 二阶密度 $te^{-t}dt$。

---

## 136. 多次递归事件形成一个矩阵值更新核

两次事件的公式已经显示，第二次时间不是独立复制第一次时间；它由第一次交付的后继经过 $T$ 转移后再产生。这个结构可以对任意有限事件词迭代。

**定理 136.1（$m$ 次事件的路径展开）。** 在定义 135.1 的同一极限标记仪器与固定续接通道 $\Lambda$ 下，运行 $m\ge1$ 次事件。对扇区路径

$$
\mathbf a=(a_1,\ldots,a_m)\in\{0,1\}^m,
$$

记

$$
|\mathbf a|=\sum_{r=1}^{m}a_r,
\qquad
W(\mathbf a)
=
w_{a_1}\prod_{r=2}^{m}T_{a_r a_{r-1}}.
$$

则总历时和最终后继的联合测度为

$$
\boxed{
\mathbf T^{(m)}_\Lambda(dt)(\rho)
=
\sum_{\mathbf a\in\{0,1\}^m}
W(\mathbf a)\,
\gamma_{|\mathbf a|}(dt)\,
\rho_{a_m}.
}
\tag{136.1}
$$

路径权重满足

$$
\sum_{\mathbf a}W(\mathbf a)=1,
$$

所以式（136.1）在每个密度输入上是总质量为一的状态值测度。

### 证明

$m=1$ 时式（136.1）就是式（126.1）的两扇区分解。假定对 $m$ 次事件成立。再施加一次 $\Lambda$ 和一次标记仪器：每条已有路径 $\mathbf a$ 的最终后继为 $\rho_{a_m}$，下一扇区 $b$ 的权重乘以 $T_{b a_m}$，下一时间测度乘以 $\nu_b$。由

$$
\gamma_{|\mathbf a|}*\nu_b
=
\gamma_{|\mathbf a|+b}
$$

得到长度 $m+1$ 的路径展开。

权重归一化由归纳法及式（135.2）得到：

$$
\sum_{a_1}w_{a_1}=1,
\qquad
\sum_bT_{ba}=1.
$$

证毕。

**推论 136.2（矩阵值核表示）。** 定义从前一扇区 $a$ 到下一扇区 $b$ 的矩阵值测度

$$
\boxed{
K_{ba}(dt)=T_{ba}\nu_b(dt).
}
\tag{136.2}
$$

则 $K$ 是列质量为一的 $2\times2$ 矩阵值概率核；多次事件的扇区—时间传播由 $K$ 的卷积幂给出。路径展开式（136.1）正是该卷积幂的逐项展开。

这说明递归观察的边界对象不再只是一个终端通道，而是一个带量子后继标签的时间更新核。它同时保存“下一扇区的概率”和“该扇区交付的时间测度”。

---

## 137. 相同的首个等待律，不保证相同的递归等待律

单次只读时间会把慢后继 $\zeta$ 求和掉；递归运行时，$\zeta$ 重新进入转移矩阵。因此终端化可以保持第一轮时间律，却改变第二轮以后的时间关系。

**定理 137.1（首轮时间相同而两轮时间不同）。** 取首个输入为边界慢态 $\rho=P_*$，并在事件之间取 $\Lambda=\operatorname{id}$。则首个事件的缩放时间律对所有 $\zeta$ 都是

$$
\mu_1(dt)=e^{-t}\,dt.
\tag{137.1}
$$

若记

$$
r_\zeta=\operatorname{Tr}(P_*\zeta),
$$

则两次事件的总历时密度为

$$
\boxed{
\mu_{2,\zeta}(dt)
=
\bigl((1-r_\zeta)+r_\zeta t\bigr)e^{-t}\,dt.
}
\tag{137.2}
$$

其平均总历时为

$$
\boxed{
\mathbb E_\zeta[T_2]=1+r_\zeta.
}
\tag{137.3}
$$

### 证明

因为首个输入为 $P_*$，首个扇区必为 $a_1=1$，首轮时间为 $\nu_1=e^{-t}dt$。首个事件后交付 $\zeta$；第二次事件进入慢扇区的概率为 $r_\zeta$，进入快扇区的概率为 $1-r_\zeta$。因此式（135.4）给出

$$
\mu_{2,\zeta}
=(1-r_\zeta)(\nu_1*\nu_0)
+r_\zeta(\nu_1*\nu_1)
=(1-r_\zeta)e^{-t}dt+r_\zeta te^{-t}dt.
$$

指数律的均值为 $1$，Erlang 二阶律的均值为 $2$，所以式（137.3）成立。证毕。

**例 137.2（同一名义相位的两种递归后继）。** 在第 106 节的相位边界上，任取 $P_*$。因为

$$
\operatorname{Tr}(P_*P_0)=\frac12,
$$

可以比较两个允许的慢后继目标

$$
\zeta^{(A)}=P_*,
\qquad
\zeta^{(B)}=P_0.
$$

二者都满足 $\operatorname{Tr}(P_*\zeta^{(A)})=1$ 与 $\operatorname{Tr}(P_*\zeta^{(B)})=1/2$。当等待占比取不超过 $1/2$ 的临界区域时，二者都属于第 119 节给出的可达后继区域。它们的首轮时间律都为 $e^{-t}dt$，但两轮总历时分别为

$$
\mu_{2,A}(dt)=te^{-t}dt,
\qquad
\mu_{2,B}(dt)=\frac{1+t}{2}e^{-t}dt,
$$

平均值分别为 $2$ 与 $3/2$。

这里没有矛盾：两种仪器的第一轮时间读数相同，第一轮点击后的量子后继不同；第二轮时间正是该后继差异在同一关系过程中的再次显现。

---

## 138. AHH：递归全息边界必须保留交付后继对未来时间的作用

**关系结论 138.1（递归事件的边界层级）。** 在第 135—137 节的重复临界协议中：

$$
\boxed{
\begin{aligned}
\text{单轮时间盲任务}
&\longleftarrow
\mathbf M_\infty([0,\infty)),\\
\text{单轮时间敏感任务}
&\longleftarrow
\mathbf M_\infty,\\
\text{多轮递归时间任务}
&\longleftarrow
K_{ba}(dt)=T_{ba}\nu_b(dt).
\end{aligned}
}
\tag{138.1}
$$

第一行只需要终端通道；第二行需要保存事件时间与点击后继的标记测度；第三行还需要保存后继经过合法续接后如何转化为下一次事件扇区的矩阵值核。

AHH 在于：**粒子式事件的后继不是一次点击后的附属状态；它是下一次事件时间的生成器。把后继终端化，会把递归关系核压成一次边缘，从而保留第一轮概率却可能改变第二轮及以后事件律。**

式（136.1）显示，递归时间的连续形状由路径中慢扇区的次数生成 Erlang 卷积；矩阵 $T$ 则记录这些慢扇区何时会再次出现。因而真正可持续执行的边界必须同时保留：

$$
\boxed{
\text{当前事件时间}
+
\text{当前点击后继}
+
\text{后继到下一事件的转移作用}.
}
$$

这与第 134 节的续接相对原则一致，但推进了一层：后续合同不只决定要保留多少时间矩，还决定是否需要把边界提升为一个矩阵值更新核。单次终端通道可以是某个任务的充分边界，同时不是递归观察者的充分边界。

**来源与边界 138.2。** 本批采用第 126 节的临界二扇区标记测度，加入固定时间盲续接 $\Lambda$ 并重复同一协议；卷积律和 Erlang 密度是有限维正映射与概率测度卷积的直接推导。没有把该更新核推广为任意时变仪器、任意自适应控制、无限维记忆或物理钟的普遍定律。本批仍是纯理论 Markdown，不新增 Lean、消化、coverage 或 freeze 内容。

## 追加锚（本行以下为增补区）

## 139. 递归时间核的 Laplace—事件数生成函数

第 136 节的卷积核可以同时记录总历时和已经完成的事件数。这样得到的不是一条新的物理钟，而是同一递归关系的一个生成函数表示。

**定义 139.1（扇区时间变换）。** 对 $s\ge0$，置

$$
D(s)=
\begin{pmatrix}
1&0\\
0&(1+s)^{-1}
\end{pmatrix}.
$$

第一行对应 $\nu_0=\delta_0$ 的 Laplace 变换，第二行对应 $\nu_1(dt)=e^{-t}dt$ 的 Laplace 变换。对扇区权重向量 $v=(v_0,v_1)^{\mathsf T}$，定义准备映射

$$
\mathsf R(v)=v_0\rho_0+v_1\rho_1.
$$

**定理 139.2（有限事件数的矩阵生成式）。** 设

$$
\widehat{\mathbf T}^{(m)}_\Lambda(s)(\rho)
=
\int_0^\infty e^{-st}\mathbf T^{(m)}_\Lambda(dt)(\rho).
$$

则对每个 $m\ge1$，

$$
\boxed{
\widehat{\mathbf T}^{(m)}_\Lambda(s)(\rho)
=
\mathsf R\!\left(D(s)\,[T D(s)]^{m-1}w\right).
}
\tag{139.1}
$$

因此，对 $0\le z<1$ 定义事件数生成响应

$$
\mathcal G_\rho(z,s)
=
\sum_{m\ge1}z^{m-1}
\widehat{\mathbf T}^{(m)}_\Lambda(s)(\rho),
$$

有

$$
\boxed{
\mathcal G_\rho(z,s)
=
\mathsf R\!\left(
D(s)\,[I-zT D(s)]^{-1}w
\right).
}
\tag{139.2}
$$

其标量迹版本为

$$
\boxed{
\operatorname{Tr}\mathcal G_\rho(z,s)
=
\mathbf 1^{\mathsf T}
D(s)\,[I-zT D(s)]^{-1}w.
}
\tag{139.3}
$$

### 证明

由式（136.1），每条扇区路径 $\mathbf a$ 的总时间测度为 $\gamma_{|\mathbf a|}$。而

$$
\int_0^\infty e^{-st}\gamma_k(dt)
=(1+s)^{-k}
$$

对 $k=0$ 也成立。于是路径中每出现一次慢扇区，就在其对应位置贡献一个 $(1+s)^{-1}$；把所有路径权重按矩阵乘法排列，正好得到

$$
D(s)[TD(s)]^{m-1}w.
$$

再施加 $\mathsf R$ 得式（139.1）。

当 $0\le z<1$ 时，在扇区权重上的诱导 $1$ 范数中，$T$ 的列和为一且 $D(s)$ 的算子范数不超过一，所以

$$
\|zTD(s)\|\le z<1.
$$

Neumann 级数收敛：

$$
\sum_{m\ge1}z^{m-1}D(s)[TD(s)]^{m-1}
=
D(s)[I-zTD(s)]^{-1}.
$$

这给出式（139.2）；取迹得到式（139.3）。证毕。

**推论 139.3（生成函数的两个边缘）。** 令 $s=0$，则 $D(0)=I$，$z$ 只计数已经完成的事件数；令 $z=0$，则只保留第一事件的时间—后继响应。令 $s>0$，则长时间路径受到 $(1+s)^{-1}$ 的慢扇区折扣。

所以 $T$ 与 $D(s)$ 的非交换乘积保留了两种关系的顺序：

$$
\boxed{
\text{后继转移}
\quad\text{与}\quad
\text{下一事件时间}
}
$$

不能先把所有后继求和，再声称得到同一个递归生成函数。

---

## 140. 长期事件时钟由平稳慢扇区人口决定

单次事件的慢时间是指数律；重复事件后，长期平均每次事件花费多少内部时间，则由扇区转移矩阵的平稳分布决定。

**定理 140.1（递归平均时间率）。** 令 $A_r\in\{0,1\}$ 为第 $r$ 次事件所属的扇区，初始分布为 $w$，转移矩阵为 $T$。条件于 $A_r=0$，第 $r$ 次时间增量 $\tau_r=0$；条件于 $A_r=1$，$\tau_r$ 服单位指数分布。令

$$
S_m=\tau_1+\cdots+\tau_m.
$$

则

$$
\boxed{
\mathbb E[S_m]
=
\sum_{r=1}^{m}
e_1^{\mathsf T}T^{r-1}w,
\qquad
e_1=(0,1)^{\mathsf T}.
}
\tag{140.1}
$$

若 $T$ 在两个扇区上不可约，平稳分布 $\pi$ 满足 $T\pi=\pi$、$\mathbf1^{\mathsf T}\pi=1$，则

$$
\boxed{
\lim_{m\to\infty}\frac{\mathbb E[S_m]}m
=
\pi_1.
}
\tag{140.2}
$$

### 证明

给定扇区路径，快扇区的时间增量期望为零，慢扇区的时间增量期望为单位指数均值一。因此

$$
\mathbb E[\tau_r]=\Pr(A_r=1)=e_1^{\mathsf T}T^{r-1}w.
$$

线性相加得到式（140.1）。

有限不可约马尔可夫链的 Cesàro 平均满足

$$
\frac1m\sum_{r=0}^{m-1}T^rw\longrightarrow\pi.
$$

将其左乘 $e_1^{\mathsf T}$，再用式（140.1），得到式（140.2）。证毕。

**推论 140.2（二状态参数化）。** 若

$$
T=
\begin{pmatrix}
1-a&b\\
a&1-b
\end{pmatrix},
\qquad a,b>0,
$$

则

$$
\pi=
\frac1{a+b}
\begin{pmatrix}
b\\a
\end{pmatrix},
\qquad
\lim_{m\to\infty}\frac{\mathbb E[S_m]}m
=
\frac{a}{a+b}.
\tag{140.3}
$$

这里 $a$ 是从快速扇区转入慢扇区的概率，$b$ 是从慢扇区转入快速扇区的概率。长期内部时间率因此由后继反馈决定，而非由第一轮指数律单独决定。

---

## 141. 同一首轮指数律可以产生不同的长期内部时间率

现在把第 137 节的两种后继比较推进到任意多轮。它们首轮都从 $P_*$ 出发，所以首轮时间相同；但后继对下一扇区的反馈会改变平稳人口。

**定理 141.1（后继目标控制长期时间率）。** 取 $\Lambda=\operatorname{id}$、初态 $\rho=P_*$，并固定第 106 节的相位边界。令

$$
r_\zeta=\operatorname{Tr}(P_*\zeta).
$$

则扇区转移矩阵的慢行概率为

$$
T_{10}=\operatorname{Tr}(P_*P_0)=\frac12,
\qquad
T_{11}=r_\zeta.
\tag{141.1}
$$

若 $0<r_\zeta<1$，长期慢扇区人口为

$$
\boxed{
\pi_1(\zeta)
=
\frac{1/2}{(1/2)+(1-r_\zeta)}
=
\frac1{3-2r_\zeta}.
}
\tag{141.2}
$$

因此

$$
\lim_{m\to\infty}\frac{\mathbb E_\zeta[S_m]}m
=
\frac1{3-2r_\zeta}.
\tag{141.3}
$$

端点按直接递归解释：$r_\zeta=1$ 时慢扇区在首个事件后吸收，长期时间率为一；$r_\zeta=0$ 时长期率为 $1/3$。

### 证明

从快速后继 $P_0$ 出发，下一次进入慢扇区的概率是

$$
T_{10}=\operatorname{Tr}(P_*P_0)=\frac12
$$

因为第 106 节的 $P_*$ 是等振幅相位态。从慢后继 $\zeta$ 出发，慢概率为

$$
T_{11}=\operatorname{Tr}(P_*\zeta)=r_\zeta.
$$

所以矩阵具有式（140.3）的形式，其中

$$
a=\frac12,\qquad b=1-r_\zeta.
$$

代入式（140.3）得到式（141.2）与式（141.3）。当 $r_\zeta=1$ 时，慢态是吸收类；从初态 $P_*$ 首次事件已经进入该类，故平均时间率趋向一。$r_\zeta=0$ 时，代入矩阵幂的直接计算或取 $b=1$ 的极限得到 $1/3$。证毕。

**例 141.2（两种后继的长期差异）。** 取第 137.2 例的两个目标：

$$
\zeta^{(A)}=P_*,
\qquad
\zeta^{(B)}=P_0.
$$

则

$$
r_{\zeta^{(A)}}=1,
\qquad
r_{\zeta^{(B)}}=\frac12.
$$

两者都在等待占比 $\lambda\le1/2$ 的第 119 节可达区域内，但长期平均时间率分别为

$$
\boxed{
\lim_{m\to\infty}\frac{\mathbb E_A[S_m]}m=1,
\qquad
\lim_{m\to\infty}\frac{\mathbb E_B[S_m]}m=\frac12.
}
\tag{141.4}
$$

第一轮事件的时间律在两种情形中都为 $e^{-t}dt$；递归展开后，二者的长期内部时钟已经不同。

---

## 142. AHH：递归极限的全息边界是矩阵值更新核的谱，而非单次通道

**关系结论 142.1（长期递归边界）。** 在第 135—141 节的重复临界协议中，三种任务对应三个不同的边界层级：

$$
\boxed{
\begin{array}{c|c}
\text{任务}&\text{充分边界}\\
\hline
\text{单次时间盲输出}&\mathbf M_\infty([0,\infty))\\
\text{有限次时间—后继记录}&K_{ba}(dt)\\
\text{长期事件数与总时间}&D(s),\ T,\ (\rho_0,\rho_1)\ \text{及其生成 resolvent}
\end{array}
}
\tag{142.1}
$$

AHH 在于：**一旦观察者允许递归续接，单次终端后继不再是最终边界；后继决定下一次慢扇区人口，转移矩阵的谱决定长期内部时间率，而 Laplace—事件数 resolvent 同时保存事件计数和时间尺度。**

所以：

$$
\boxed{
\text{单次指数尾}
\neq
\text{长期递归时钟的完整形状}.
}
$$

前者是一次标记测度的慢边缘；后者是矩阵值更新核反复卷积后的平稳关系。改变 $\zeta$ 即使不改变首轮等待律，也会改变 $T$、平稳人口和长期时间率。

这给“关系全息”一个递归版本：边界不是某个被动保存的终端密度矩阵，而是对指定续接族足以生成未来事件词的更新算子。对有限事件词，保存 $K$ 足够；对长期计数与时间问题，还必须保存 $K$ 的 Laplace 变换及其 resolvent。若把这些对象压成一次终端通道，得到的只是一个较小任务的充分摘要。

**来源与边界 142.2。** 本批只在第 135 节的固定时间盲续接、重复临界二扇区仪器和有限扇区状态下推导生成函数、平稳时间率与显式后继对比。没有把长期平均率解释为物理秒速率，没有推广到时变或自适应转移、无限维记忆或非齐次谱，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 143. 矩阵值时间核的谱生成率

第 139 节的 resolvent 同时含有事件数变量和 Laplace 变量。对固定事件数趋于无穷时，真正控制其指数尺度的是矩阵 $T D(s)$ 的 Perron 根，而不是单独的慢人口。

**定义 143.1（事件数的 Laplace 质量）。** 记

$$
F_m(s;\rho)
=
\operatorname{Tr}\widehat{\mathbf T}^{(m)}_\Lambda(s)(\rho)
=
\mathbf 1^{\mathsf T}D(s)[T D(s)]^{m-1}w,
\qquad s\ge0.
$$

假定 $T$ 是 primitive 的列随机矩阵，即存在某个正整数 $k$ 使 $T^k$ 的每个矩阵元都严格为正。置

$$
A(s)=T D(s),
\qquad
\lambda(s)=\rho(A(s)),
\qquad
\psi(s)=\log\lambda(s),
$$

其中 $\rho(\cdot)$ 表示谱半径。

**定理 143.2（长期 Laplace 生成率）。** 在上述 primitive 假设下，对每个 $s\ge0$，有

$$
\boxed{
\lim_{m\to\infty}\frac1m\log F_m(s;\rho)=\psi(s).
}
\tag{143.1}
$$

只要 $w$ 是非零非负向量，极限与初始输入 $\rho$ 的具体扇区人口无关。更精确地，若 $\ell(s),r(s)$ 分别是满足

$$
\ell(s)^{\mathsf T}r(s)=1
$$

的正左、右 Perron 向量，则

$$
F_m(s;\rho)
=
\lambda(s)^{m-1}
\bigl(\mathbf 1^{\mathsf T}D(s)r(s)\bigr)
\bigl(\ell(s)^{\mathsf T}w\bigr)
+o(\lambda(s)^{m-1}).
\tag{143.2}
$$

### 证明

$D(s)$ 的两个对角元都严格为正，且它不改变 $T$ 的零元图。因此 $A(s)=T D(s)$ 仍为 primitive 非负矩阵。Perron—Frobenius 定理给出简单正特征值 $\lambda(s)>0$，其余特征值的模严格小于 $\lambda(s)$，并给出谱分解

$$
A(s)^{m-1}
=
\lambda(s)^{m-1}r(s)\ell(s)^{\mathsf T}
+o(\lambda(s)^{m-1}).
$$

左乘 $\mathbf1^{\mathsf T}D(s)$、右乘 $w$ 即得式（143.2）。正性使两个前因子都严格为正，取对数并除以 $m$ 得式（143.1）。证毕。

**推论 143.3（均值率只是谱生成率的一阶切线）。** 在 $s=0$，$D(0)=I$、$\lambda(0)=1$。若 $\pi$ 是 $T$ 的平稳分布，则

$$
\boxed{
\psi'(0)=-\pi_1.
}
\tag{143.3}
$$

因此第 140 节的长期平均内部时间率是谱生成率在零点的负一阶导数；它只给出谱函数的局部信息。

### 证明

列随机性给出左 Perron 向量 $\mathbf1$，平稳分布给出右 Perron 向量 $\pi$，并取 $\mathbf1^{\mathsf T}\pi=1$。因为

$$
D'(0)=\begin{pmatrix}0&0\\0&-1\end{pmatrix},
\qquad
A'(0)=T D'(0),
$$

简单特征值微分公式给出

$$
\lambda'(0)
=\mathbf1^{\mathsf T}A'(0)\pi
=-\mathbf1^{\mathsf T}T
\begin{pmatrix}0&0\\0&1\end{pmatrix}\pi
=-\pi_1.
$$

由于 $\lambda(0)=1$，有 $\psi'(0)=\lambda'(0)$。证毕。

---

## 144. 长期时间波动还记得扇区转移的相关性

均值率只记录慢扇区的长期人口；相邻事件是否倾向于连续落在同一扇区，则会进入总时间的二阶波动。

**定理 144.1（平稳时间方差率）。** 令扇区链以平稳分布 $\pi$ 开始，且每个慢扇区独立附加一个单位指数变量 $Y_r$，置

$$
\tau_r=A_rY_r,
\qquad
S_m=\sum_{r=1}^m\tau_r.
$$

若 $T$ primitive，则极限

$$
\sigma^2
=\lim_{m\to\infty}\frac{\operatorname{Var}(S_m)}m
$$

存在，并且

$$
\boxed{
\sigma^2
=
2\pi_1-\pi_1^2
+2\sum_{k\ge1}
\left(\pi_1(T^k)_{11}-\pi_1^2\right).
}
\tag{144.1}
$$

同一个量是第 143 节谱函数的二阶导数：

$$
\boxed{
\psi''(0)=\sigma^2.
}
\tag{144.2}
$$

### 证明

单位指数变量满足 $\mathbb E Y_r=1$、$\mathbb E Y_r^2=2$。故

$$
\operatorname{Var}(\tau_r)
=\mathbb E[A_rY_r^2]-\mathbb E[A_rY_r]^2
=2\pi_1-\pi_1^2.
$$

当 $k\ge1$ 时，独立的 $Y_r$ 给出

$$
\operatorname{Cov}(\tau_r,\tau_{r+k})
=\operatorname{Cov}(A_r,A_{r+k})
=\pi_1(T^k)_{11}-\pi_1^2.
$$

primitive 性使 $T^k$ 指数趋近于 $\pi\mathbf1^{\mathsf T}$，上述协方差级数绝对收敛。将方差展开为方差项与两倍协方差和，除以 $m$ 后得到式（144.1）。

另一方面，$F_m(s;\pi)$ 是 $S_m$ 的 Laplace 变换。有限维 primitive 矩阵的简单 Perron 根在 $s=0$ 附近解析，因此

$$
\frac1m\log F_m(s;\pi)\longrightarrow\psi(s)
$$

可在 $s=0$ 的二阶导数上逐项取极限。Laplace 对数的二阶导数在零点等于方差，故得到式（144.2）。证毕。

**推论 144.2（只知道长期均值仍不足以知道长期形状）。** 两个转移矩阵可以具有相同的平稳慢人口 $\pi_1$，却具有不同的 $\sigma^2$。所以长期平均内部时间率不确定长期时间波动，也不确定不同事件词的尾部聚集程度。

---

## 145. 相同的慢人口可以对应不同的递归时间噪声

给出一个显式二状态族。取 $0<p<1$，$-\min\{p/(1-p),(1-p)/p\}<\lambda<1$，置

$$
T_{p,\lambda}
=
\begin{pmatrix}
1-p(1-\lambda)&(1-p)(1-\lambda)\\
p(1-\lambda)&1-(1-p)(1-\lambda)
\end{pmatrix}.
$$

其列和为一，平稳分布为

$$
\pi=(1-p,p)^{\mathsf T},
$$

而另一个特征值为 $\lambda$。

**定理 145.1（固定均值、可变二阶律）。** 对上述族，长期平均内部时间率恒为 $p$，但平稳时间方差率为

$$
\boxed{
\sigma^2(p,\lambda)
=2p-p^2+2p(1-p)\frac{\lambda}{1-\lambda}.
}
\tag{145.1}
$$

### 证明

二状态链的平稳协方差满足

$$
\operatorname{Cov}(A_0,A_k)=p(1-p)\lambda^k.
$$

将其代入式（144.1），使用几何级数

$$
\sum_{k\ge1}\lambda^k=\frac\lambda{1-\lambda}
$$

即得式（145.1）。平均率由 $\pi_1=p$ 直接给出。证毕。

**例 145.2（同均值的两个谱边界）。** 取 $p=1/2$。当 $\lambda=0$ 时，链的两行相同，连续事件的扇区没有记忆，且

$$
\sigma^2(1/2,0)=\frac34.
$$

当 $\lambda=1/2$ 时，链偏好保持当前扇区，仍有 $\pi_1=1/2$，但

$$
\sigma^2(1/2,1/2)=\frac54.
$$

所以两种递归协议具有相同的长期平均时间率 $1/2$，但每次事件总历时的平方根涨落系数不同。

---

## 146. AHH：长期全息边界要保留谱函数，而不只保留一个人口数

**关系结论 146.1（长期任务的边界层级）。** 对第 135—145 节的同一递归协议，可以按任务区分三个摘要：

$$
\boxed{
\begin{array}{c|c}
\text{任务}&\text{足够边界}\\
\hline
\text{长期平均内部时间率}&\pi_1\\
\text{长期二阶时间波动}&\{\pi_1(T^k)_{11}:k\ge1\}\ \text{或}\ \psi''(0)\\
\text{所有渐近时间累积率}&\psi(s)=\log\rho(TD(s))\ \text{（在声明域内）}
\end{array}
}
\tag{146.1}
$$

第一行说明平稳慢人口对均值任务已经充分；第二行必须加入扇区相关性；第三行则需要整个谱生成函数。把第三行压成 $\pi_1$ 会把同均值、不同相关性的两个协议错误识别为同一长期关系。

AHH 在于：**递归全息边界的最小形状由未来任务的阶数决定；一次平均率只需一个人口坐标，波动任务需要相关谱，所有长期累积任务则需要矩阵值核的 Perron 函数。**

这不是把谱函数解释成一条额外物理钟。$s$ 仍是内部时间 Laplace 参数，$\psi$ 是固定模型和固定续接合同下的渐近生成率。只有在另行给出内部标度到物理钟的校准后，才可以把它与实验时间量比较。

**来源与边界 146.2。** 本批在固定有限二扇区、primitive 齐次转移矩阵、独立单位指数慢增量和固定时间盲续接假设下推导 Perron 生成率、均值导数、方差率及同均值反例。没有把 Perron 函数推广到时变或自适应核、无限维谱、非独立等待增量或物理时间度量；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 147. 事件编号时间与截止时刻计数是两种不同的切片

第 143—146 节沿事件编号 $m$ 研究总历时 $S_m$。实验也可以反过来固定一个内部截止时刻 $t$，询问在这之前已经完成了多少次事件。由于快速扇区的时间增量是零，反演必须保留零时间原子，不能把它当成普通的严格递增更新。

**定义 147.1（截止事件数）。** 在同一扇区链和慢扇区独立单位指数增量下，置

$$
S_m=\sum_{r=1}^{m}A_rY_r,
\qquad
N(t)=\sup\{m\ge0:S_m\le t\}.
$$

这里 $A_r\in\{0,1\}$ 是事件编号为 $r$ 的扇区，$Y_r$ 是单位指数变量；若 $T$ 不可约且 $\pi_1>0$，则 $S_m\to\infty$ 几乎处处，故 $N(t)$ 几乎处处有限。

**定理 147.2（事件数与内部时间的一阶互逆律）。** 若 $T$ 不可约、平稳慢人口 $\pi_1>0$，则

$$
\boxed{
\frac{S_m}{m}\longrightarrow\pi_1
\quad\text{几乎处处},
\qquad
\frac{N(t)}{t}\longrightarrow\frac1{\pi_1}
\quad(t\to\infty)\ \text{几乎处处}.
}
\tag{147.1}
$$

若进一步 $T$ primitive，则还具有均值版本

$$
\boxed{
\lim_{t\to\infty}\frac{\mathbb E[N(t)]}{t}
=\frac1{\pi_1}.
}
\tag{147.2}
$$

### 证明

有限不可约马尔可夫链的遍历定理给出

$$
\frac1m\sum_{r=1}^{m}A_r\longrightarrow\pi_1
\quad\text{几乎处处}.
$$

令

$$
M_m=\sum_{r=1}^{m}A_r(Y_r-1).
$$

在给定扇区历史后，$M_m$ 是平方可积鞅差和，且其条件二次变差为 $O(m)$。鞅强大数定律给出 $M_m/m\to0$，于是 $S_m/m\to\pi_1$。

因为 $S_m$ 非降且 $S_m\to\infty$，对任意满足 $S_m\le t<S_{m+1}$ 的 $m$ 有

$$
\frac{m}{S_{m+1}}
\le
\frac{N(t)}t
\le
\frac{m+1}{S_m}.
$$

代入 $S_m/m\to\pi_1$ 得第二个几乎处处极限。

最后，在 primitive 假设下，取充分小的 $s>0$。第 143 节给出

$$
\lim_{m\to\infty}\frac1m\log\mathbb E[e^{-sS_m}]
=\log\lambda(s),
\qquad
\lambda(s)=\rho(TD(s)),
$$

且 $\log\lambda(s)=-\pi_1s+o(s)$。对任意 $c>1/\pi_1$，可选取 $s$ 使 $e^{sc}\lambda(s)<1$。Chernoff 界于是使 $\Pr(N(t)\ge ct)$ 按 $t$ 指数衰减；结合几乎处处收敛，对 $N(t)/t$ 取得一致可积性，得到式（147.2）。证毕。

**推论 147.3（零时间事件不等于没有事件）。** 当 $\pi_1<1$ 时，平均每单位内部时间完成的事件数为 $1/\pi_1>1$。其中多出的事件来自快扇区的零时间连续串；它们改变截止计数，却不增加 $S_m$。

这只是内部时间标度中的计数律。它没有把 $1/\pi_1$ 解释成物理钟的频率，后者仍需独立标定。

---

## 148. 截止计数由矩阵 renewal resolvent 精确生成

将第 136 节的矩阵值核直接按事件编号卷积，可以得到所有截止事件数的尾概率和均值，而不必逐个枚举事件词。

**定义 148.1（初始事件向量测度）。** 定义列向量值测度

$$
\boldsymbol\nu_w(dt)
=
\begin{pmatrix}
w_0\nu_0(dt)\\
w_1\nu_1(dt)
\end{pmatrix},
$$

以及矩阵值核

$$
K_{ba}(dt)=T_{ba}\nu_b(dt).
$$

对 $m\ge1$，置

$$
\boldsymbol\mu_m(dt)
=
K^{*(m-1)}*\boldsymbol\nu_w(dt).
$$

其 $b$ 分量是第 $m$ 次事件发生在扇区 $b$ 且总历时落在 $dt$ 的概率测度。

**定理 148.2（截止事件到达 renewal resolvent）。** 对 $s>0$，若 $T$ 不可约且 $\pi_1>0$，则

$$
\boxed{
\boldsymbol{\mathcal U}_w(dt)
=
\sum_{m\ge1}\boldsymbol\mu_m(dt)
}
\tag{148.1}
$$

在有界时间区间上具有有限质量，且其 Laplace 变换为

$$
\boxed{
\widehat{\boldsymbol{\mathcal U}}_w(s)
=
[I-D(s)T]^{-1}D(s)w
=
D(s)[I-TD(s)]^{-1}w.
}
\tag{148.2}
$$

此外，对每个 $t\ge0$，

$$
\boxed{
\mathbb E[N(t)]
=
\mathbf1^{\mathsf T}\boldsymbol{\mathcal U}_w([0,t]).
}
\tag{148.3}
$$

### 证明

第 $m$ 次事件的 Laplace 向量为

$$
\widehat{\boldsymbol\mu}_m(s)
=[D(s)T]^{m-1}D(s)w.
$$

当 $s>0$ 时，$D(s)$ 在慢列上严格收缩；不可约性保证该损失可从每个状态到达，所以 $D(s)T$ 的谱半径严格小于一。因而 Neumann 级数收敛，并给出

$$
\sum_{m\ge1}[D(s)T]^{m-1}D(s)w
=[I-D(s)T]^{-1}D(s)w.
$$

恒等式

$$
[I-AB]^{-1}A=A[I-BA]^{-1}
$$

取 $A=D(s)$、$B=T$，得到第二个表示。

对任一样本路径，$S_m$ 非降且趋于无穷，因此

$$
N(t)=\sum_{m\ge1}\mathbf1_{\{S_m\le t\}}
$$

几乎处处成立。取期望并按扇区求和，得到式（148.3）。证毕。

**推论 148.3（零时间原子的作用）。** 虽然 $\nu_0=\delta_0$，式（148.2）仍然在 $s>0$ 有限；有限性来自快扇区连续串的转移矩阵衰减，而不是来自把 $\delta_0$ 删除。把零时间原子直接抹去，会丢失截止时刻前已经完成的快事件数量。

---

## 149. 截止事件数的概率生成函数不是事件总时间的简单边缘

第 139 节的 $z$ 变量给出按事件数加权的总历时测度。固定截止时刻后，$z$ 还可以生成随机变量 $N(t)$ 本身；两者由一次累计和恒等式连接，却不是同一个边缘。

**定理 149.1（截止事件数的概率生成式）。** 对 $0\le z<1$，定义

$$
\boldsymbol{\mathcal U}_{w,z}(dt)
=
\sum_{m\ge1}z^{m-1}\boldsymbol\mu_m(dt).
$$

则

$$
\boxed{
\widehat{\boldsymbol{\mathcal U}}_{w,z}(s)
=
[I-zD(s)T]^{-1}D(s)w
=
D(s)[I-zT D(s)]^{-1}w.
}
\tag{149.1}
$$

并且

$$
\boxed{
\mathbb E[z^{N(t)}]
=
1-(1-z)\,
\mathbf1^{\mathsf T}
\boldsymbol{\mathcal U}_{w,z}([0,t]).
}
\tag{149.2}
$$

### 证明

式（149.1）由定义 148.1 的逐项 Laplace 变换和 Neumann 级数得到。

对每条 $N(t)$ 有限的样本路径，有限几何和恒等式给出

$$
1-z^{N(t)}
=(1-z)\sum_{m=1}^{N(t)}z^{m-1}
=(1-z)\sum_{m\ge1}z^{m-1}\mathbf1_{\{S_m\le t\}}.
$$

取期望，再用 $\boldsymbol\mu_m$ 的定义，得到式（149.2）。证毕。

**推论 149.2（两种 resolvent 的任务区别）。** 在 $s=0$ 的形式代入中，第 139 节的表达式按事件数加权总历时；式（149.2）先对总历时测度作截止累计，再得到截止事件数的概率生成函数。若存在零时间原子，累计与事件数加权不能交换成一个终端通道。

---

## 150. AHH：时间切片有事件编号方向和截止方向

**关系结论 150.1（双向时间边界）。** 在固定二扇区递归协议中：

$$
\boxed{
\begin{array}{c|c}
\text{问题}&\text{充分边界}\\
\hline
\text{给定事件编号的时间—后继词}&K_{ba}(dt)\\
\text{给定截止时刻的事件数}&\boldsymbol\nu_w,\ [I-D(s)T]^{-1}\\
\text{截止事件数的概率生成}&\boldsymbol\nu_w,\ [I-zD(s)T]^{-1}\\
\text{仅求长期一阶计数率}&\pi_1^{-1}
\end{array}
}
\tag{150.1}
$$

事件编号方向从 $m$ 生成 $S_m$；截止方向从 $t$ 反演 $N(t)$。当快扇区有零时间原子时，反演不是把一个标量时间律取逆，而是要保留矩阵转移与零时间串的 renewal resolvent。

AHH 在于：**同一个关系过程具有两种互补的时间切片：按事件编号切片得到时间—后继核，按截止时刻切片得到累计计数 resolvent；只保存其中一个方向，不能普遍恢复另一个方向。**

因此，$K$ 是有限事件词的边界，$[I-D(s)T]^{-1}$ 是截止计数的边界，$\pi_1^{-1}$ 只是它们在长期一阶问题上的压缩。将最后一个标量反过来冒充完整时间关系，会把不同的零时间串和不同的有限截止分布压成同一对象。

**来源与边界 150.2。** 本批在固定有限二扇区、不可约或 primitive 齐次转移矩阵、独立单位指数慢增量和固定时间盲续接假设下推导事件数的逆律、矩阵 renewal resolvent 及截止时刻概率生成函数。没有推广到时变或自适应核、无限维记忆、非独立等待增量或物理钟标定；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 151. 完整截止计数可以反演标量到达测度

第 149 节把截止事件数的概率生成函数写成到达测度的累计。现在反过来问：若对所有截止时刻和所有 $z$ 都知道计数生成函数，究竟能恢复什么？

**定义 151.1（标量到达系数）。** 令

$$
u_{m,w}(dt)
=
\mathbf1^{\mathsf T}\boldsymbol\mu_m(dt)
$$

为第 $m$ 次事件的总历时标量测度，并定义

$$
G_w(z,t)=\mathbb E_w[z^{N(t)}],
\qquad
H_w(z,t)=\frac{1-G_w(z,t)}{1-z}
\quad(0\le z<1).
$$

**定理 151.2（截止计数的系数反演）。** 对每个 $t\ge0$，有

$$
\boxed{
H_w(z,t)
=
\sum_{m\ge1}z^{m-1}u_{m,w}([0,t]).
}
\tag{151.1}
$$

因此，完整函数 $G_w(z,t)$ 唯一确定每个累计到达函数 $u_{m,w}([0,t])$；在其为连续点的 $t$ 上，可写成

$$
\boxed{
u_{m,w}([0,t])
=
\frac1{(m-1)!}
\left.
\frac{\partial^{m-1}}{\partial z^{m-1}}
H_w(z,t)
\right|_{z=0}.
}
\tag{151.2}
$$

若截止记录还保留最终扇区 $b$，把 $G_w$ 换成向量值到达生成函数，则同样的系数反演唯一确定每个 $\boldsymbol\mu_m$ 的两个扇区分量。

### 证明

由式（149.2），对 $z<1$ 有

$$
H_w(z,t)
=
\sum_{m\ge1}z^{m-1}
\Pr_w(S_m\le t)
=
\sum_{m\ge1}z^{m-1}u_{m,w}([0,t]).
$$

系数非负且总和有限，所以这是 $|z|<1$ 内的幂级数；幂级数系数唯一，逐项微分得到式（151.2）。保留最终扇区时，只是把每个标量系数替换成向量系数，论证不变。证毕。

**推论 151.3（可反演不等于可恢复量子后继）。** 标量截止计数完整确定

$$
\mathbf1^{\mathsf T}\boldsymbol\mu_m
$$

及其 Laplace 变换，却没有确定 $\boldsymbol\mu_m$ 的扇区分量，更没有确定每个分量所携带的量子后继状态。

换言之，知道所有截止时间的计数分布，比知道一个截止时刻的计数多得多；但它仍然只是标量时间边界。

---

## 152. 相同的截止计数可以对应不同的量子后继

下面给出一个与第 151 节相反方向的成对实现：所有标量截止计数完全相同，但后继态不同。

**定理 152.1（计数边界的后继不可识别性）。** 取二维相位边界

$$
P_* = |+\rangle\langle+|,
\qquad
|+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},
$$

固定 $\Lambda=\operatorname{id}$、快速后继 $\rho_0=P_0$，并比较

$$
\rho_1^{(A)}=P_0,
\qquad
\rho_1^{(B)}=P_1.
$$

两种模型都有

$$
\operatorname{Tr}(P_*\rho_1^{(A)})
=
\operatorname{Tr}(P_*\rho_1^{(B)})
=\frac12.
$$

因此它们的扇区转移矩阵 $T$ 相同，任意初始扇区人口 $w$ 下的所有标量到达测度 $u_{m,w}$、所有截止计数生成函数 $G_w(z,t)$ 也相同；但是其状态值第 $m$ 次事件输出不同，已经在 $m=1$ 时出现。

### 证明

因为

$$
\operatorname{Tr}(P_*P_0)=\operatorname{Tr}(P_*P_1)=\frac12,
$$

慢后继的下一次扇区人口在两种模型中都为 $(1/2,1/2)$，快速列也相同，所以 $T$ 和所有由 $T,\nu_0,\nu_1,w$ 生成的标量路径权重相同。第 151 节的系数展开于是给出相同的 $u_{m,w}$ 与 $G_w$。

另一方面，第一个事件的慢分支分别交付 $P_0$ 和 $P_1$。对初态 $P_*$，该分支的时间—后继测度分别为

$$
e^{-t}dt\,P_0,
\qquad
e^{-t}dt\,P_1,
$$

二者是不同的状态值测度。证毕。

**这不是“计数数据不够精确”的统计问题。** 即使给出无限精确的所有截止计数分布，缺失的量子后继方向也不会从标量累计中自动出现。它是观察映射的核，而不是有限样本误差。

---

## 153. 带状态标签和多种准备可以反演转移核

上一节的不可识别性来自两个压缩：把最终扇区求和，以及只使用一个初始扇区人口。增加相应的关系接口后，可以得到一个精确的有限维反演定理。

**定义 153.1（状态值截止响应）。** 假定 $\rho_0,\rho_1$ 已知且在线性算子空间上实线性无关。对每个初始扇区人口向量 $w$，定义状态值到达响应

$$
\boldsymbol{\mathfrak U}_{w}(z,dt)
=
\sum_{m\ge1}z^{m-1}
\sum_{b=0}^{1}
\mu_{m,b}(dt)\,\rho_b,
$$

其中 $\mu_{m,b}$ 是 $\boldsymbol\mu_m$ 的第 $b$ 分量。

**定理 153.2（有限扇区核的可识别性）。** 若观察者能够：

1. 对两个线性无关的初始人口向量 $w^{(0)},w^{(1)}$ 分别取得完整状态值响应 $\boldsymbol{\mathfrak U}_{w^{(j)}}(z,dt)$；
2. 在状态空间上作足以区分线性无关 $\rho_0,\rho_1$ 的精确层析；
3. 已知两种扇区时间测度 $\nu_0,\nu_1$；

则可以唯一恢复转移矩阵 $T$。在任意 $s>0$ 上，恢复出的第两次事件向量满足

$$
\widehat{\boldsymbol\mu}_2(s;w)
=
D(s)T D(s)w.
$$

把 $w^{(0)},w^{(1)}$ 作为一组基向量，组成矩阵 $W=[w^{(0)}\ w^{(1)}]$，则

$$
\boxed{
T
=
D(s)^{-1}
\begin{bmatrix}
\widehat{\boldsymbol\mu}_2(s;w^{(0)})
&
\widehat{\boldsymbol\mu}_2(s;w^{(1)})
\end{bmatrix}
W^{-1}
D(s)^{-1}.
}
\tag{153.1}
$$

### 证明

由 $\rho_0,\rho_1$ 的实线性无关性，状态层析把每个状态值系数唯一分解成两个标量分量。因此由定理 151.2 的系数反演，完整状态值截止响应给出每个 $\boldsymbol\mu_m$，尤其给出 $\boldsymbol\mu_2$ 的 Laplace 向量。

矩阵值核定义给出

$$
\widehat K(s)=D(s)T,
\qquad
\widehat{\boldsymbol\nu}_w(s)=D(s)w,
$$

所以

$$
\widehat{\boldsymbol\mu}_2(s;w)
=
\widehat K(s)\widehat{\boldsymbol\nu}_w(s)
=
D(s)T D(s)w.
$$

两种初始向量组成基，右乘 $W^{-1}$ 得到 $D(s)T D(s)$；$D(s)$ 的两个对角元均正，左右乘其逆即得式（153.1）。如果只给一个初始向量，式（153.1）只有一个矩阵作用值，不能一般确定 $T$ 的全部两列。证毕。

**推论 153.3（可辨识条件是合同的一部分）。** 结论依赖状态标签、两种独立准备和已知时间核。去掉其中任一项，恢复任务都会退化为相应的观察商；“边界足够”不能脱离允许的续接与准备族单独谈论。

---

## 154. AHH：全息边界的可恢复性必须连同观察合同声明

**关系结论 154.1（四个边界层级）。** 对第 151—153 节的同一递归协议：

$$
\boxed{
\begin{array}{c|c}
\text{观察任务}&\text{足够边界}\\
\hline
\text{全部截止计数分布}&\{u_{m,w}\}_{m\ge1}\\
\text{带最终扇区标签的截止分布}&\{\boldsymbol\mu_m\}_{m\ge1}\\
\text{带状态值和多种准备的核恢复}&\{\rho_0,\rho_1,\nu_0,\nu_1,T\}\\
\text{一个固定准备下的长期计数率}&\pi_1^{-1}
\end{array}
}
\tag{154.1}
$$

第一行能反演标量到达测度；第二行保留扇区分解；第三行才足以在本有限模型中反演转移核；第四行只是一个长期标量。

AHH 在于：**“全息”不是给某个边界贴上永恒的充分标签，而是一个相对于观察合同、准备族、记录标签和目标任务的可恢复性命题。**

因此，同一个内部递归关系对计数观察者可以有一个小的标量边界，对带后继层析和多种准备的观察者却必须提升为状态值核。两者不是矛盾的全息定义，而是不同续接族下的不同充分性。

**来源与边界 154.2。** 本批在固定二维扇区、已知时间测度、精确状态层析、两种线性无关初始人口和齐次转移矩阵的模型内，推导截止计数的系数反演、计数边界的量子后继不可识别性及转移核恢复公式。没有把精确层析或无限数据解释成现实实验的零成本资源，没有推广到未知时间核、无限维记忆、时变控制或物理钟标定；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 155. 非齐次续接的时间核按因果顺序组合

前面的 $T$ 假定每次事件之间使用同一个续接通道。若观察者在不同轮次使用不同的合法续接，后继转移矩阵也随轮次改变；这时边界对象是有序核列，而不是一个平均矩阵。

**定义 155.1（非齐次扇区核）。** 对第 $r$ 次事件后的续接 $\Lambda^{[r]}$，置

$$
T^{[r]}_{ba}
=
\operatorname{Tr}\bigl(E_b\Lambda^{[r]}(\rho_a)\bigr),
\qquad
K^{[r]}_{ba}(dt)
=
T^{[r]}_{ba}\nu_b(dt).
$$

固定首轮人口 $w$，令初始事件向量测度仍为 $\boldsymbol\nu_w$。对 $m\ge1$，定义

$$
\boldsymbol\mu^{(m)}_{[1:m-1]}(dt)
=
K^{[m-1]}*\cdots*K^{[1]}*\boldsymbol\nu_w(dt),
$$

其中 $m=1$ 时约定空乘积为恒等核。

**定理 155.2（非齐次路径展开）。** 在同一二扇区时间测度 $\nu_0,\nu_1$ 下，令 $D(s)$ 如定义 139.1。则

$$
\boxed{
\widehat{\boldsymbol\mu}^{(m)}_{[1:m-1]}(s)
=
D(s)T^{[m-1]}D(s)T^{[m-2]}
\cdots
D(s)T^{[1]}D(s)w.
}
\tag{155.1}
$$

等价地，对扇区路径 $\mathbf a=(a_1,\ldots,a_m)$，其权重为

$$
w_{a_1}
\prod_{r=1}^{m-1}T^{[r]}_{a_{r+1}a_r},
$$

而总历时测度为 $\gamma_{|\mathbf a|}$，最终后继为 $\rho_{a_m}$。

### 证明

$m=1$ 时，初始事件向量的 Laplace 变换是 $D(s)w$，即式（155.1）的空乘积情形。

若式（155.1）对 $m$ 成立，左侧再卷积第 $m$ 次事件核 $K^{[m]}$，其 Laplace 矩阵为 $D(s)T^{[m]}$，于是得到

$$
D(s)T^{[m]}D(s)T^{[m-1]}
\cdots
D(s)T^{[1]}D(s)w.
$$

路径权重同时多出因子 $T^{[m]}_{a_{m+1}a_m}$，时间测度多出 $\nu_{a_{m+1}}$；由 $\gamma_k*\nu_b=\gamma_{k+b}$，得到长度 $m+1$ 的展开。归纳完成。证毕。

**推论 155.3（非齐次谱不能由单一平稳人口代替）。** 非齐次序列的长期率若存在，要由有序乘积

$$
D(s)T^{[m-1]}\cdots D(s)T^{[1]}D(s)
$$

的增长性质决定。单独记录每个 $T^{[r]}$ 的平稳人口，不能一般恢复这些乘积的谱行为。

---

## 156. 续接顺序本身可以改变有限事件时间律

矩阵乘法的非交换性在这里不是记号问题；它会改变同一组控制的事件时间路径。

**定理 156.1（同一控制集合的顺序反例）。** 在扇区核层面取两个列随机矩阵

$$
T^{\mathrm A}
=
\begin{pmatrix}
1&1\\
0&0
\end{pmatrix},
\qquad
T^{\mathrm B}
=
\begin{pmatrix}
0&0\\
1&1
\end{pmatrix},
$$

并以 $w=e_0=(1,0)^{\mathsf T}$ 开始。对四次事件分别使用续接序列 $\mathrm A,\mathrm B,\mathrm A$ 与 $\mathrm B,\mathrm A,\mathrm B$，得到确定的扇区词

$$
(0,0,1,0),
\qquad
(0,1,0,1).
$$

因此两种顺序的总历时测度分别为

$$
\boxed{
\gamma_1(dt)=e^{-t}dt,
\qquad
\gamma_2(dt)=te^{-t}dt.
}
\tag{156.1}
$$

### 证明

$T^{\mathrm A}$ 把任一输入列重置到快速扇区，$T^{\mathrm B}$ 把任一输入列重置到慢扇区。故从 $e_0$ 出发，顺序 $\mathrm A,\mathrm B,\mathrm A$ 产生

$$
0\overset{\mathrm A}{\longmapsto}0
\overset{\mathrm B}{\longmapsto}1
\overset{\mathrm A}{\longmapsto}0,
$$

四个事件扇区为 $(0,0,1,0)$；顺序 $\mathrm B,\mathrm A,\mathrm B$ 产生 $(0,1,0,1)$。路径中慢扇区次数分别为一与二，代入 $\gamma_{|\mathbf a|}$ 即得式（156.1）。

两种控制序列使用完全相同的两个一步核，只是排列不同；若先把它们替换成一个平均矩阵，就无法同时保留这两个有序乘积及其时间律。证毕。

这个反例只在有限扇区核层面说明因果顺序；它不宣称每个抽象列随机矩阵都来自上一节固定量子接口的同一 CP 实现。若要把控制序列纳入量子模型，必须另外声明能够实现这些核的控制寄存器与续接通道。

---

## 157. 记录依赖控制时，边界是策略树而不是矩阵

非齐次序列还不是最一般的情形。观察者可以根据已经取得的事件记录选择下一次续接；此时下一步核由历史决定。

**定义 157.1（扇区历史策略）。** 令

$$
h_r=(a_1,\ldots,a_r)
$$

表示前 $r$ 次事件的扇区历史。一个策略 $\Pi$ 为每个可达历史 $h_r$ 指定一个列随机矩阵 $T^{\Pi(h_r)}$。定义路径权重

$$
W_\Pi(\mathbf a)
=
w_{a_1}
\prod_{r=1}^{m-1}
T^{\Pi(h_r)}_{a_{r+1}a_r},
\qquad
h_r=(a_1,\ldots,a_r).
$$

**定理 157.2（策略树的路径测度）。** 对固定策略 $\Pi$，第 $m$ 次事件的总历时—后继测度为

$$
\boxed{
\boldsymbol\mu^{(m)}_\Pi(dt)
=
\sum_{\mathbf a\in\{0,1\}^m}
W_\Pi(\mathbf a)\,
\gamma_{|\mathbf a|}(dt)\,
\rho_{a_m}.
}
\tag{157.1}
$$

若策略还依赖于连续时间读数，而不只是扇区历史，则式（157.1）中的固定 $\gamma_{|\mathbf a|}$ 必须替换为沿时间记录逐步积分的路径测度；不能把时间依赖隐藏进一个常数矩阵。

### 证明

给定历史 $h_r$ 后，策略选择的下一核是 $T^{\Pi(h_r)}$。条件概率链法则给出路径概率为 $W_\Pi(\mathbf a)$。每个扇区词仍由相应的 $\nu_{a_r}$ 贡献时间因子，卷积得到 $\gamma_{|\mathbf a|}$；最终状态由最后扇区给出 $\rho_{a_m}$。对所有路径求和即得式（157.1）。若控制依赖连续时间，下一核在同一扇区词内部也随时间改变，因而不能先把时间积分替换为一个固定的卷积因子。证毕。

**推论 157.3（反事实分支属于策略边界）。** 只记录实际实现的历史，足以计算这一次运行的条件概率；若任务允许改变未来控制，则还必须保存每个允许历史上的核 $T^{\Pi(h)}$。未实现的分支不是“没有发生所以无关”，它们是合法续接的反事实边界。

---

## 158. AHH：递归全息边界必须保留因果控制合同

**关系结论 158.1（控制合同的边界层级）。** 对固定扇区时间测度的递归协议：

$$
\boxed{
\begin{array}{c|c}
\text{允许的续接任务}&\text{充分边界}\\
\hline
\text{固定同一续接的递归词}&K\\
\text{预先声明的非齐次控制序列}&(K^{[1]},K^{[2]},\ldots)\\
\text{依赖记录的自适应控制}&\{K_h:h\ \text{为可达历史}\}\\
\text{只回放已实现的一条路径}&\text{该路径的条件记录}
\end{array}
}
\tag{158.1}
$$

第一行由一个矩阵值核足够；第二行需要有序核列；第三行需要策略树；第四行只能回答这一次回放，不能回答改变控制后的合法未来。

AHH 在于：**动态全息边界的“完整”不仅是保存当前量子状态，还要保存允许的因果控制合同；矩阵的乘法顺序和未实现分支共同决定可持续续接的未来。**

因此，把一组控制取平均再迭代，只有在额外证明所有相关核彼此可交换、或任务本身只要求平均一阶读数时才合法。对时间—后继任务，非交换的有序产品和策略树是边界内容，不是实施细节。

**来源与边界 158.2。** 本批在有限二扇区、已知零/指数时间测度、列随机续接核和有限历史策略下推导非齐次卷积、顺序反例与策略树路径测度。没有把抽象核序列自动宣称为固定 CP 仪器的实现，没有推广到无限历史、连续控制、无限维记忆或物理钟标定；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 159. 共同续接下的策略树可以按强 lumpability 压缩

策略树的节点不一定都需要逐个保留。若两个内部扇区对所有允许控制都给出相同的后继块概率、时间标记和声明输出，它们可以被压成同一个商扇区。

**定义 159.1（控制族的强 lumpability）。** 令 $A$ 为有限扇区集，$U$ 为允许的固定控制集，$T^u$ 是控制 $u$ 下的列随机转移矩阵。给定满射

$$
\varphi:A\longrightarrow\overline A,
$$

称 $\varphi$ 对控制族强 lumpable，若对任意 $u\in U$、任意 $a,a'$ 满足 $\varphi(a)=\varphi(a')$，以及任意 $\bar b\in\overline A$，都有

$$
\boxed{
\sum_{\varphi(b)=\bar b}T^u_{ba}
=
\sum_{\varphi(b)=\bar b}T^u_{ba'}.
}
\tag{159.1}
$$

若同一纤维内的时间测度和声明输出也相同，

$$
\nu_a=\nu_{a'},
\qquad
\rho_a=\rho_{a'},
$$

则定义商核

$$
\overline T^u_{\bar b\,\bar a}
=
\sum_{\varphi(b)=\bar b}T^u_{ba},
\qquad
\overline\nu_{\bar a}=\nu_a,
\qquad
\overline\rho_{\bar a}=\rho_a.
$$

**定理 159.2（强 lumpability 保持有限控制词响应）。** 设 $\varphi$ 满足定义 159.1。对任意有限控制词 $u_1,\ldots,u_{m-1}$，若初始人口向量 $w$ 与商初始人口 $\bar w$ 相容，

$$
\bar w_{\bar a}
=
\sum_{\varphi(a)=\bar a}w_a,
$$

则原扇区模型与商模型在所有长度 $m$ 的时间—后继记录上给出相同的商响应。特别地，对任意扇区词 $q_1,\ldots,q_m\in\overline A$，

$$
\boxed{
\sum_{\varphi(a_r)=q_r}
w_{a_1}
\prod_{r=1}^{m-1}
T^{u_r}_{a_{r+1}a_r}
=
\bar w_{q_1}
\prod_{r=1}^{m-1}
\overline T^{u_r}_{q_{r+1}q_r}.
}
\tag{159.2}
$$

### 证明

$m=1$ 时式（159.2）就是初始人口相容性。假设长度 $m$ 成立，在右端再推进一步 $\overline T^{u_m}_{q_{m+1}q_m}$。按商核定义，它等于对所有 $a_m$ 位于 $q_m$ 纤维、$a_{m+1}$ 位于 $q_{m+1}$ 纤维的原始转移求和；强 lumpability 保证这个总和与选取的纤维代表无关。于是归纳得到长度 $m+1$ 的式子。

同一纤维的 $\nu_a$ 相同，所以每个商扇区词携带同一卷积测度；同一纤维的 $\rho_a$ 相同，所以后继输出也相同。对所有商词求和即得商响应与原响应一致。证毕。

**推论 159.3（时间敏感任务通常阻止过度压缩）。** 若两个扇区的时间测度不同，例如 $\nu_0=\delta_0$、$\nu_1=e^{-t}dt$，则它们不能在时间敏感任务中放入同一 lumpability 纤维。能在时间盲任务中使用的商，不自动是时间—后继任务的充分边界。

---

## 160. 延续等价给出相对于任务的最小策略边界

强 lumpability 是一种显式的充分条件；更一般地，可以直接用所有允许未来来定义最小商。

**定义 160.1（延续等价）。** 固定一个允许控制与记录的任务族 $\mathcal C$。对每个可达历史 $h$ 和策略 $\Pi\in\mathcal C$，令

$$
\mathcal O_h(\Pi)
$$

表示从 $h$ 开始执行 $\Pi$ 所得到的全部声明时间、扇区和量子后继记录的联合测度。定义

$$
\boxed{
h\sim_{\mathcal C}h'
\iff
\mathcal O_h(\Pi)=\mathcal O_{h'}(\Pi)
\quad\text{对所有 }\Pi\in\mathcal C.
}
\tag{160.1}
$$

**定理 160.2（延续等价商的最小性）。** 设 $\eta(h)$ 是一个边界摘要，并要求它对任务族 $\mathcal C$ 充分，即

$$
\eta(h)=\eta(h')
\Longrightarrow
\mathcal O_h(\Pi)=\mathcal O_{h'}(\Pi)
\quad\forall\Pi\in\mathcal C.
$$

则

$$
\boxed{
\eta(h)=\eta(h')
\Longrightarrow
h\sim_{\mathcal C}h'.
}
\tag{160.2}
$$

反过来，商映射

$$
q_{\mathcal C}:h\longmapsto[h]_{\sim_{\mathcal C}}
$$

本身对 $\mathcal C$ 充分。若可达历史有限，则任何确定性充分摘要的取值数都不少于等价类数；$q_{\mathcal C}$ 达到这个下界。

### 证明

式（160.2）只是把充分性的量词代入定义 160.1。对商映射，若两个历史属于同一个等价类，则按定义对每个 $\Pi$ 的输出完全相同，所以商摘要充分。

任一确定性充分摘要都必须把同一摘要值内的历史放在同一个 $\sim_{\mathcal C}$ 等价类中，因而其取值类数不少于等价类数。商映射恰好一类对应一个取值，达到下界。证毕。

**这里的“最小”是任务相对的。** 改变允许的控制、记录标签或目标输出，就会改变 $\mathcal C$，从而改变等价类和最小边界；它不是脱离观察合同的内部本体计数。

---

## 161. 只保存已实现路径不能保证反事实干预完整

如果观察者只回放一个实际策略，两个隐藏历史可以完全相同；一旦允许替换下一次控制，它们可能立刻给出不同事件律。

**定理 161.1（干预分离条件）。** 设 $\Pi_0$ 是实际运行的策略，$\iota$ 是允许的下一步干预。若存在两个历史 $h,h'$ 满足

$$
\mathcal O_h(\Pi_0)=\mathcal O_{h'}(\Pi_0),
\qquad
\mathcal O_h(\iota)\ne\mathcal O_{h'}(\iota),
$$

则任何只以 $\Pi_0$ 的已实现记录为边界的摘要，都不是包含 $\iota$ 的任务族的充分边界。

### 证明

只保存 $\Pi_0$ 的实际记录会把 $h,h'$ 置于同一观察纤维。若这个摘要对包含 $\iota$ 的任务族充分，定义 160.1 将迫使

$$
\mathcal O_h(\iota)=\mathcal O_{h'}(\iota),
$$

与假设矛盾。证毕。

**例 161.2（隐藏记忆只在干预下显现）。** 令隐藏记忆 $q\in\{0,1\}$，当前可见扇区均为快速扇区。控制 $\mathrm A$ 对两个记忆都把下一扇区重置为快速：

$$
T_{\mathrm A}^{(0)}=T_{\mathrm A}^{(1)}
=
\begin{pmatrix}1\\0\end{pmatrix}.
$$

控制 $\mathrm B$ 则依赖隐藏记忆：

$$
T_{\mathrm B}^{(0)}
=
\begin{pmatrix}1\\0\end{pmatrix},
\qquad
T_{\mathrm B}^{(1)}
=
\begin{pmatrix}0\\1\end{pmatrix}.
$$

在实际策略 $\Pi_0$ 永远选择 $\mathrm A$ 时，两种历史都给出同样的零时间事件记录。若下一步改用 $\mathrm B$，记忆 $q=0$ 仍给 $\nu_0=\delta_0$，而 $q=1$ 给 $\nu_1=e^{-t}dt$；两个历史因而被时间记录立刻区分。

这个例子不把隐藏记忆解释成额外观察者；它只说明：对允许干预的任务，未实现控制的作用必须属于边界合同。

---

## 162. AHH：最小全息边界是控制族上的延续等价商

**关系结论 162.1（因果边界的最小层级）。** 在前述有限递归模型中：

$$
\boxed{
\begin{array}{c|c}
\text{目标任务}&\text{最小充分边界}\\
\hline
\text{固定控制词的回放}&\text{该词下的状态—时间记录}\\
\text{全部固定控制序列}&\text{对控制族强 lumpable 的商核}\\
\text{所有记录依赖策略}&\text{延续等价类 }[h]_{\sim_{\mathcal C}}\\
\text{允许反事实干预}&\text{包含干预的延续等价商}
\end{array}
}
\tag{162.1}
$$

若强 lumpability 成立，商核提供一个可计算的有限边界；若不存在这样的显式商，延续等价仍给出抽象的最小边界定义。固定一条已实现路径只回答回放问题，不能自动回答干预问题。

AHH 在于：**全息边界的最小对象不是“当前状态”这个固定名词，而是相对于未来控制族的延续等价类；观察合同扩大，等价类细分，边界必然增大。**

这把动态充分性、策略树和反事实完整性放进同一个关系判据：边界保存的不是内部的所有细节，而是所有被允许的未来能够继续区分的差异。任何被压进同一摘要的差异，都必须对整个声明控制族永远不可区分；否则该摘要不是充分边界。

**来源与边界 162.2。** 本批在有限扇区、有限控制族、有限历史和精确时间—后继记录的模型内推导强 lumpability 商、延续等价最小性与干预分离反例。没有把抽象策略树自动宣称为物理装置实现，没有推广到无限历史、连续控制、无限维记忆或物理钟标定；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 163. 有限控制族上的延续等价可以递归计算

第 160 节的延续等价是由所有未来策略定义的抽象商。有限扇区和有限控制族使这个商可以通过逐层区分签名构造，而不必枚举无限长策略。

**定义 163.1（输出签名与划分细化）。** 令 $A$ 为有限扇区集，$U$ 为有限控制集。对 $A$ 的划分 $\mathcal P$，定义状态 $a$ 的签名为

$$
\operatorname{sig}_{\mathcal P}(a)
=
\left(
\nu_a,\rho_a,
\left(
\sum_{b\in B}T^u_{ba}
\right)_{\substack{u\in U\\B\in\mathcal P}}
\right).
$$

令 $\mathcal P_0$ 按 $(\nu_a,\rho_a)$ 相等性分块，并令 $\mathcal P_{n+1}$ 把具有相同 $\operatorname{sig}_{\mathcal P_n}$ 的状态放在同一块。

**定理 163.2（划分细化的有限稳定性）。** 序列

$$
\mathcal P_0\succeq\mathcal P_1\succeq\cdots
$$

在至多 $|A|-1$ 次严格细分后稳定。稳定划分 $\mathcal P_\infty$ 是所有满足输出相同和控制族强 lumpability 的划分中最粗的一个。

### 证明

每次细化只会拆分块，不会合并块；若发生严格细分，块数至少增加一。块数最多为 $|A|$，所以严格细分次数不超过 $|A|-1$。

稳定时，同一块内的状态具有相同的 $\nu,\rho$，并且对上一划分的每个块 $B$ 和每个控制 $u$ 具有相同的总转移概率。由于稳定划分等于上一划分，正满足定义 159.1 的强 lumpability 条件。

反过来，设 $\mathcal Q$ 是任一满足这些条件的划分。归纳证明 $\mathcal Q$ 的每个块都包含在 $\mathcal P_n$ 的某个块中。$n=0$ 时由输出相同成立；若在 $\mathcal Q$ 中两个状态仍同块，则它们对 $\mathcal P_n$ 各块的总转移概率相同，而这正是 $\operatorname{sig}_{\mathcal P_n}$ 的每个坐标，所以它们也留在 $\mathcal P_{n+1}$ 的同一块。稳定后 $\mathcal Q$ 仍细于或等于 $\mathcal P_\infty$，故 $\mathcal P_\infty$ 最粗。证毕。

**推论 163.3（时间任务与时间盲任务有不同稳定商）。** 若细化签名包括 $\nu_a$，得到的是时间敏感商；若先把所有时间测度投影为总质量一，再运行同一细化，得到的可能是更粗的时间盲商。后者不能自动用于恢复时间—后继记录。

---

## 164. 有限 horizon 的近似商有显式误差预算

精确等价过于严格时，可以规定一个有限 horizon 和误差容许量。只要每一步的块转移与时间标记都近似相同，整个有限词的差异由逐步误差累加控制。

**定义 164.1（近似签名缺陷）。** 设 $\mathcal P$ 是一个划分。称同一块中的 $a,a'$ 具有缺陷 $(\epsilon,\delta,\eta)$，若对所有 $u\in U$：

$$
\frac12
\sum_{B\in\mathcal P}
\left|
\sum_{b\in B}T^u_{ba}
-
\sum_{b\in B}T^u_{ba'}
\right|
\le\epsilon,
$$

$$
\|\nu_a-\nu_{a'}\|_{\mathrm{TV}}\le\delta,
\qquad
D(\rho_a,\rho_{a'})\le\eta.
$$

**定理 164.2（有限控制词的近似边界误差）。** 对同一近似块中的两个初始状态 $a,a'$，以及任意长度为 $m-1$ 的固定控制词，若每个可达对应块的逐步缺陷都不超过 $(\epsilon,\delta,\eta)$，则其长度 $m$ 的块—时间记录分布满足

$$
\boxed{
D_{\mathrm{TV}}
\bigl(
\mathsf P_a^{(m)},
\mathsf P_{a'}^{(m)}
\bigr)
\le
(m-1)\epsilon+m\delta.
}
\tag{164.1}
$$

若最后还读取量子后继状态，则联合经典—量子输出的半迹距离满足

$$
\boxed{
D_{\mathrm{cq}}
\le
(m-1)\epsilon+m\delta+\eta.
}
\tag{164.2}
$$

### 证明

对每一轮使用最大耦合：在同一划分块条件下，下一块不同的概率不超过 $\epsilon$；该轮时间标记不同的概率不超过 $\delta$。只要前面所有耦合成功，两个过程继续使用同一控制词和同一块历史。对 $m-1$ 次转移与 $m$ 个时间标记应用并集界，得到式（164.1）。

在经典记录相同的耦合分支上，最终量子态的半迹距离不超过 $\eta$。把失败耦合分支压到正交经典标志，迹距离三角不等式再增加至多 $(m-1)\epsilon+m\delta$，得到式（164.2）。证毕。

**推论 164.3（近似商的有效范围）。** 固定 $\epsilon,\delta>0$ 时，式（164.1）只保证有限 horizon；当 $m$ 无界，线性预算会耗尽。因而“近似全息”必须连同 horizon、误差预算和允许的控制词一起声明。

---

## 165. 稀有条件分支会放大边界压缩误差

有限 horizon 的未条件化误差很小，并不保证一个稀有事件条件化后的后继仍然接近。归一化会除以分支概率。

**定理 165.1（条件化的概率下界）。** 设 $X,Y\succeq0$ 是同一局域分支在两个边界摘要下给出的未归一化输出，令

$$
p=\operatorname{Tr}X,
\qquad
q=\operatorname{Tr}Y,
\qquad
p,q\ge p_*>0,
$$

且 $\|X-Y\|_1\le\varepsilon$。则

$$
\boxed{
|p-q|\le\varepsilon,
\qquad
D\left(\frac Xp,\frac Yq\right)
\le\frac{\varepsilon}{p_*}.
}
\tag{165.1}
$$

### 证明

迹是迹范数的收缩，所以 $|p-q|\le\|X-Y\|_1\le\varepsilon$。又

$$
\left\|\frac Xp-\frac Yq\right\|_1
\le
\frac{\|X-Y\|_1}{p}
+
\left|\frac1p-\frac1q\right|\|Y\|_1
=
\frac{\varepsilon+|p-q|}{p}
\le
\frac{2\varepsilon}{p}.
$$

取半迹范数并用 $p\ge p_*$，得到式（165.1）。证毕。

**例 165.2（误差放大不是形式缺陷）。** 若一条边界压缩把分支的未归一化输出误差压到 $\varepsilon$，但该分支概率只有 $p_*=\varepsilon$，式（165.1）只给出距离不超过一的界。因而稀有晚事件、稀有控制历史和近暗分支都必须单独登记概率下界，不能只报告未归一化核的绝对误差。

---

## 166. AHH：精确商、近似商和条件商是三种不同边界

**关系结论 166.1（边界压缩的三层合同）。** 对有限控制族和时间—后继任务：

$$
\boxed{
\begin{array}{c|c}
\text{边界合同}&\text{必须保存的量}\\
\hline
\text{无限 horizon 精确恢复}&\mathcal P_\infty\ \text{的精确商核}\\
\text{有限 horizon 近似恢复}&(\epsilon,\delta,\eta,m)\ \text{及近似商核}\\
\text{条件后继恢复}&\text{上述数据及分支概率下界 }p_*\\
\end{array}
}
\tag{166.1}
$$

第一行由划分细化得到；第二行的误差随 horizon 累加；第三行还受到条件归一化的 $1/p_*$ 放大。

AHH 在于：**边界压缩的安全性不是一个静态“保真度”数字，而是由未来 horizon、控制族和条件分支概率共同决定的误差合同。**

这把精确全息、近似全息和稀有事件条件化放进一条连续但有方向的关系链：先判断哪些历史在所有允许未来下真正等价，再决定有限资源下允许多大偏差，最后检查任何条件化是否会把偏差放大。把一个小的未归一化误差直接宣传成小的条件后继误差，缺少了不可省略的 $p_*$ 条件。

**来源与边界 166.2。** 本批在有限状态、有限控制族、有限 horizon、可测时间标记和完全正后继输出的模型内推导划分细化、近似耦合误差和条件化放大界。没有把近似商解释为无限 horizon 的精确充分性，没有推广到无限维、无限控制、未知分支概率或物理钟标定；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 167. 带接口标签的时间核可以结合拼接

一个关系体若要被拆成前后两段，前段的输出接口必须保留给后段作为输入。矩阵值时间核正好给出这种带接口的拼接运算。

**定义 167.1（核的接口卷积）。** 令 $K$ 是从接口集 $A$ 到 $B$ 的矩阵值测度，令 $L$ 是从 $B$ 到 $C$ 的矩阵值测度。定义

$$
\boxed{
(L\star K)_{ca}(dt)
=
\sum_{b\in B}
(L_{cb}*K_{ba})(dt).
}
\tag{167.1}
$$

这里 $*$ 是时间测度卷积，乘法顺序表示先经过 $K$、再经过 $L$。

**定理 167.2（接口拼接的结合律）。** 若 $K:A\to B$、$L:B\to C$、$M:C\to D$ 的矩阵值测度均为有限质量，则

$$
\boxed{
M\star(L\star K)
=
(M\star L)\star K.
}
\tag{167.2}
$$

在 Laplace 域中，

$$
\boxed{
\widehat{L\star K}(s)
=
\widehat L(s)\widehat K(s).
}
\tag{167.3}
$$

### 证明

展开左侧的 $(d,a)$ 分量：

$$
\sum_{c\in C}\sum_{b\in B}
M_{dc}*(L_{cb}*K_{ba}).
$$

测度卷积的结合律允许去掉括号；有限求和可以交换顺序，所得表达式正是 $(M\star L)\star K$ 的 $(d,a)$ 分量。Laplace 变换把卷积变成乘法，且矩阵乘法保留接口求和的顺序，得到式（167.3）。证毕。

**推论 167.3（可组合边界的接口条件）。** 若前段和后段的摘要共享同一个接口集 $B$，则可以只保存各自的矩阵值核并通过 $\star$ 生成联合响应。若前段只保存了对 $B$ 的标量边缘，后段一般不能再执行式（167.1）。

---

## 168. 忘掉中间接口会破坏后续拼接

终端化一个阶段可能完全保持该阶段的标量输出，却破坏下一阶段对接口状态的作用。

**定理 168.1（接口遗忘反例）。** 取一个二状态接口 $B=\{0,1\}$，时间测度

$$
\nu_0=\delta_0,
\qquad
\nu_1(dt)=e^{-t}dt.
$$

定义两个前段核，对任意输入列 $a$ 都分别重置到不同接口：

$$
K^{(0)}_{ba}(dt)=
\begin{cases}
\delta_0(dt),&b=0,\\
0,&b=1,
\end{cases}
\qquad
K^{(1)}_{ba}(dt)=
\begin{cases}
0,&b=0,\\
\delta_0(dt),&b=1.
\end{cases}
$$

它们的接口求和边缘相同：

$$
\sum_bK^{(0)}_{ba}
=
\sum_bK^{(1)}_{ba}
=
\delta_0.
$$

令后段核只把接口状态保留，并附加该接口的时间测度：

$$
L_{cb}(dt)=
\begin{cases}
\nu_0(dt),&c=b=0,\\
\nu_1(dt),&c=b=1,\\
0,&c\ne b.
\end{cases}
$$

则

$$
\boxed{
\sum_c(L\star K^{(0)})_{ca}=\delta_0,
\qquad
\sum_c(L\star K^{(1)})_{ca}=\nu_1.
}
\tag{168.1}
$$

### 证明

前段两核都给出同一个时间零原子，故任何只看接口求和的终端任务无法区分它们。拼接后，$K^{(0)}$ 只把质量送到 $b=0$，后段贡献 $\nu_0$；$K^{(1)}$ 只把质量送到 $b=1$，后段贡献 $\nu_1$。分别求和即得式（168.1）。证毕。

这个反例说明：**一个摘要对单段任务充分，不等于它对含后段续接的任务充分。** 中间接口不是实施细节，而是后段能够读取的关系。

---

## 169. 有限续接任务的最小线性接口由响应秩决定

接口大小不能只凭“保留了一个状态”来计数。真正的下界由所有允许后续读数在边界空间上产生多少个独立线性响应决定。

**定义 169.1（续接响应映射）。** 令 $X$ 为有限维实边界空间，给定有限续接任务族

$$
\mathcal F=\{F_1,\ldots,F_J\},
\qquad
F_j:X\to\mathbb R
$$

的线性读数。定义响应映射

$$
\mathcal R_{\mathcal F}:X\to\mathbb R^J,
\qquad
\mathcal R_{\mathcal F}(x)
=
(F_1(x),\ldots,F_J(x)).
$$

**定理 169.2（响应秩的接口维数下界）。** 若线性摘要 $S:X\to Y$ 对 $\mathcal F$ 充分，即对每个 $F_j$ 都存在 $\overline F_j:Y\to\mathbb R$ 使

$$
F_j=\overline F_j\circ S,
$$

则

$$
\boxed{
\dim Y\ge\operatorname{rank}\mathcal R_{\mathcal F}.
}
\tag{169.1}
$$

反过来，取

$$
Y=\operatorname{im}\mathcal R_{\mathcal F},
\qquad
S=\mathcal R_{\mathcal F},
$$

即可达到这个线性维数。

### 证明

充分性意味着 $\mathcal R_{\mathcal F}=\overline{\mathcal R}\circ S$，其中 $\overline{\mathcal R}:Y\to\mathbb R^J$ 由各个 $\overline F_j$ 组成。因此

$$
\operatorname{rank}\mathcal R_{\mathcal F}
\le
\operatorname{rank}S
\le
\dim Y,
$$

得到式（169.1）。

若取 $S=\mathcal R_{\mathcal F}$，每个 $F_j$ 就是 $\operatorname{im}\mathcal R_{\mathcal F}$ 上的第 $j$ 个坐标投影，因而摘要充分；其取值空间维数等于响应映射的秩。证毕。

**推论 169.3（任务扩大时接口成本单调）。** 若 $\mathcal F\subseteq\mathcal F'$，则

$$
\operatorname{rank}\mathcal R_{\mathcal F}
\le
\operatorname{rank}\mathcal R_{\mathcal F'}.
$$

所以允许更多后续控制或读数不会降低精确线性接口的最小维数；它只能保持或增加边界成本。

这里的秩是声明任务族上的线性下界，不自动等同于物理装置的 Hilbert 空间维数。正性、完全正性和可实现性还需要额外检查。

---

## 170. AHH：全息拼接需要接口、结合律和响应秩

**关系结论 170.1（可组合边界的三个条件）。** 对分段递归关系：

$$
\boxed{
\begin{array}{c|c}
\text{问题}&\text{边界要求}\\
\hline
\text{两段关系能否拼接}&\text{共享且未终端化的接口标签}\\
\text{多段拼接是否与分段方式无关}&\text{矩阵值核的结合律}\\
\text{接口需要多大}&\text{允许续接响应映射的秩}\\
\end{array}
}
\tag{170.1}
$$

若只保存每段的终端标量，式（168.1）说明后段作用可能无法恢复；若接口完整保留，式（167.2）保证分段括号不改变联合响应；若任务族扩大，式（169.1）给出不可绕过的线性维数下界。

AHH 在于：**全息边界的“可拼接”不是单段充分性的自动传递，而是一个接口范畴条件；接口标签保证后段可作用，结合律保证整体独立于分段方式，响应秩决定必须保留多少关系自由度。**

这把动态充分边界、策略树和成本问题接到同一条链上：先声明可拼接的续接族，再构造接口核，最后用响应秩检查是否过度压缩。把接口删掉后再试图从终端边缘补回它，已经失去了后段区分关系所需的坐标。

**来源与边界 170.2。** 本批在有限接口集、有限时间测度、有限线性续接任务和矩阵值核卷积模型内推导拼接结合律、接口遗忘反例与响应秩下界。没有把线性维数自动等同于物理 Hilbert 维数，没有推广到无限接口、非线性摘要、未知控制或物理钟标定；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 171. 终端充分性还不等于因果闭合

一个边界摘要可以完整回答当前阶段的终端效果，却没有保存后段接口把未来效果拉回当前边界所需的方向。

**定义 171.1（效果空间的因果闭合）。** 令 $\mathcal X$ 为有限维边界状态空间，$\mathcal X^*$ 为其线性效果空间。给定终端任务族 $\mathcal F_{\mathrm{term}}\subseteq\mathcal X^*$ 和允许接口映射族 $\mathcal C$。称子空间 $V\subseteq\mathcal X^*$ 对该任务族因果闭合，若

$$
\mathcal F_{\mathrm{term}}\subseteq V,
\qquad
\Phi^*(V)\subseteq V
\quad\forall\Phi\in\mathcal C.
$$

这里 $\Phi^*$ 是接口映射对效果的伴随拉回。

**定理 171.2（因果闭合保证任意有限拼接充分）。** 若两份边界状态 $\rho,\sigma$ 对因果闭合空间 $V$ 的所有效果期望相同，即

$$
\operatorname{Tr}[(\rho-\sigma)F]=0
\quad\forall F\in V,
$$

则对任意有限接口词 $\Phi_1,\ldots,\Phi_n\in\mathcal C$ 和任意终端效果 $H\in\mathcal F_{\mathrm{term}}$，都有

$$
\boxed{
\operatorname{Tr}\!\left[
(\rho-\sigma)
(\Phi_1^*\circ\cdots\circ\Phi_n^*)(H)
\right]
=0.
}
\tag{171.1}
$$

### 证明

因果闭合给出

$$
(\Phi_1^*\circ\cdots\circ\Phi_n^*)(H)\in V
$$

的归纳结论：$H\in V$，每次再作用一个 $\Phi_j^*$ 仍留在 $V$。将该效果代入两态在 $V$ 上相同的假设，得到式（171.1）。证毕。

**推论 171.3（边界合同的方向）。** 若任务只要求当前终端效果，$\mathcal F_{\mathrm{term}}$ 可能已足够；若允许继续拼接接口，必须把所有可能的伴随拉回加入边界。后段的作用决定当前边界需要保存哪些坐标。

---

## 172. 失去因果闭合的局部摘要不能拼接

**定理 172.1（终端摘要的组合反例）。** 取线性边界空间

$$
\mathcal X=\mathbb R^2,
\qquad
F_0(x_1,x_2)=x_1,
\qquad
V=\operatorname{span}\{F_0\}.
$$

令接口映射为交换两个坐标：

$$
\Phi(x_1,x_2)=(x_2,x_1).
$$

则 $V$ 对当前终端任务充分，但不对 $\{\Phi\}$ 因果闭合；事实上

$$
\Phi^*F_0(x_1,x_2)=x_2\notin V.
$$

状态

$$
x=(1,0),
\qquad
y=(1,1)
$$

对 $V$ 给出相同读数，却满足

$$
F_0(\Phi x)=0,
\qquad
F_0(\Phi y)=1.
$$

### 证明

$F_0(x)=F_0(y)=1$，所以终端摘要 $V$ 无法区分 $x,y$。但交换映射后第一坐标分别为 $0$ 与 $1$，故后段终端读数不同。由于 $\Phi^*F_0=x_2$ 不在 $V$，这正是定理 171.2 的闭合条件失败。证毕。

这个二维例子只用于说明线性边界的组合逻辑；若要把 $\Phi$ 解释成量子接口，还必须另行检查正性与完全正性。其信息结论不依赖那个物理实现。

---

## 173. 伴随拉回闭包给出最小递归边界

可以从终端效果开始反复加入所有允许接口的拉回，得到所有有限续接任务所需的最小线性空间。

**定义 173.1（因果闭包序列）。** 置

$$
V_0=\operatorname{span}\mathcal F_{\mathrm{term}},
$$

并递归定义

$$
V_{n+1}
=
V_n+
\operatorname{span}
\{\Phi^*(F):
\Phi\in\mathcal C,\ F\in V_n\}.
$$

令

$$
V_\infty=\bigcup_{n\ge0}V_n.
$$

**定理 173.2（有限维因果闭包的稳定性与最小性）。** 若 $\mathcal X$ 有限维，则存在

$$
n_*\le\dim\mathcal X
$$

使

$$
\boxed{
V_{n_*}=V_{n_*+1}=V_\infty.
}
\tag{173.1}
$$

该稳定空间是包含 $\mathcal F_{\mathrm{term}}$ 且对所有 $\Phi^*$ 闭合的最小线性子空间。两态在 $V_\infty$ 上期望相同，当且仅当它们对所有有限接口词后的终端效果都给出相同读数。

### 证明

$V_n$ 是递增子空间链；每次严格增长至少增加一维，而 $\mathcal X^*$ 维数为 $\dim\mathcal X$，所以至多经过 $\dim\mathcal X$ 次严格增长后稳定。稳定意味着对每个 $\Phi$ 都有 $\Phi^*(V_{n_*})\subseteq V_{n_*}$，并且显然包含终端空间。

若 $W$ 是任一包含终端空间且对所有 $\Phi^*$ 闭合的子空间，则归纳有 $V_n\subseteq W$，故 $V_\infty\subseteq W$，证明最小性。

最后，$V_\infty$ 由所有有限次拉回的终端效果张成；两态在其上期望相同，当且仅当对这些生成效果逐一相同。证毕。

**推论 173.3（闭包秩是递归边界成本）。** 令

$$
r_\infty=\dim V_\infty.
$$

则 $r_\infty$ 是所有线性充分边界的下界；取对偶坐标使边界记录 $V_\infty$ 上的期望，即可达到该线性秩。终端任务的秩 $\dim V_0$ 可能严格小于递归任务的秩 $r_\infty$。

---

## 174. AHH：真正的最小边界是因果闭包秩

**关系结论 174.1（终端到递归的边界层级）。** 对有限维边界和允许接口族：

$$
\boxed{
\begin{array}{c|c}
\text{任务}&\text{线性充分边界}\\
\hline
\text{当前终端读数}&V_0=\operatorname{span}\mathcal F_{\mathrm{term}}\\
\text{固定长度不超过 }n\text{ 的拼接}&V_n\\
\text{任意有限续接}&V_\infty\\
\text{不可压缩的递归接口}&r_\infty=\dim V_\infty
\end{array}
}
\tag{174.1}
$$

若 $V_0$ 已对所有接口拉回闭合，则终端边界可以递归复用；若不闭合，继续任务必然扩大边界。$V_\infty$ 达到全效果空间时，当前模型下不存在非平凡的线性观察商。

AHH 在于：**边界的真正成本不是终端输出的维数，而是终端效果在允许接口下反复拉回后生成的因果闭包秩。**

这解释了为什么一个单段全息摘要在递归观察中会失效：它只覆盖 $V_0$，却没有覆盖后段能够访问的 $V_1,V_2,\ldots$。把接口合同写成伴随闭包，才可以逐层判定哪些内部差异仍会在未来重新显现。

**来源与边界 174.2。** 本批在有限维线性边界、有限或任意已声明接口映射族及终端线性效果任务下推导因果闭合、局部组合反例和闭包秩最小性。没有把线性闭包秩自动等同于物理 Hilbert 维数，没有推广到非线性摘要、无限维闭包、未知接口或物理钟标定；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 175. 因果闭包诱导规范的接口商

闭包空间 $V_\infty$ 不只给出一个维数；它还直接定义哪些边界状态在全部允许续接下不可区分。

**定义 175.1（因果评价商）。** 取 $V_\infty$ 的一组基 $F_1,\ldots,F_r$，定义评价映射

$$
\mathsf q_{V_\infty}:\mathcal X\longrightarrow\mathbb R^r,
\qquad
\mathsf q_{V_\infty}(x)
=
\bigl(F_1(x),\ldots,F_r(x)\bigr).
$$

写

$$
x\equiv_{V_\infty}y
\iff
\mathsf q_{V_\infty}(x)=\mathsf q_{V_\infty}(y).
$$

**定理 175.2（规范商的充分性与最小性）。** 对任意两个边界状态 $x,y$，以下条件等价：

$$
\mathsf q_{V_\infty}(x)=\mathsf q_{V_\infty}(y);
$$

$$
F(x)=F(y)
\quad\text{对所有 }F\in V_\infty;
$$

$$
H\bigl(\Phi_n\circ\cdots\circ\Phi_1(x)\bigr)
=
H\bigl(\Phi_n\circ\cdots\circ\Phi_1(y)\bigr)
$$

对所有有限接口词 $\Phi_1,\ldots,\Phi_n$ 和所有终端效果 $H\in\mathcal F_{\mathrm{term}}$ 成立。

此外，任何线性摘要 $S:\mathcal X\to Y$ 若对全部有限续接任务充分，则存在唯一线性映射 $\widetilde q$ 使

$$
\mathsf q_{V_\infty}=\widetilde q\circ S
$$

在 $S(\mathcal X)$ 上成立。因此 $\mathsf q_{V_\infty}$ 是所有线性充分接口的规范商。

### 证明

前两条是有限维线性空间中“对基相等”等价于“对整个张成空间相等”。第三条中的每个复合效果都属于 $V_\infty$，所以第二条推出第三条。

反过来，取空接口词就得到所有 $H\in\mathcal F_{\mathrm{term}}$ 的相等；再对有限接口词逐层取拉回，$V_\infty$ 的定义说明这些复合效果张成整个 $V_\infty$，故第三条推出第二条。

若 $S(x)=S(y)$，充分性迫使 $x,y$ 对 $V_\infty$ 的所有效果相等。因此 $\mathsf q_{V_\infty}$ 在每个 $S$ 的纤维上为常值，有限维线性因子化定理给出 $\widetilde q$；若限制到 $S(\mathcal X)$，因子化唯一。证毕。

**推论 175.3（接口坐标不是内部坐标的任意选择）。** 不同的 $V_\infty$ 基只改变评价商的可逆坐标变换；真正不变量是核

$$
\ker\mathsf q_{V_\infty}=V_\infty^\perp.
$$

这正是所有声明续接都无法区分的方向。

---

## 176. 近似因果闭包的误差按拉回范数传播

精确闭包可以被有限精度摘要替代，但误差会沿未来接口的伴随作用传播。

**定义 176.1（算子意义下的近似闭合）。** 在 $\mathcal X^*$ 上固定范数。称子空间 $V$ 具有误差 $\eta$ 的近似闭合，若对每个 $\Phi\in\mathcal C$ 存在线性映射

$$
P_\Phi:\mathcal X^*\longrightarrow V
$$

使

$$
\|\Phi^*-P_\Phi\|\le\eta.
$$

假定所有接口以及它们的近似代表都满足

$$
\|\Phi^*\|\le M,
\qquad
\|P_\Phi\|\le M.
$$

这一定义把每一步的误差控制提升为算子范数控制，因而不需要对近似代表的范数作未声明的归一化假设。

**定理 176.2（有限拉回的乘积望远镜误差界）。** 对任意范数不超过一的终端效果 $H\in V$ 和任意接口词 $\Phi_1,\ldots,\Phi_n$，令

$$
G_n=P_{\Phi_1}\circ\cdots\circ P_{\Phi_n}(H)\in V.
$$

则

$$
\boxed{
\left\|
(\Phi_1^*\circ\cdots\circ\Phi_n^*)(H)-G_n
\right\|
\le
n\eta M^{n-1}.
}
\tag{176.1}
$$

更一般地，若第 $j$ 个精确拉回和近似代表的范数上界分别为 $a_j,b_j$，则右侧可替换为

$$
\eta\sum_{j=1}^{n}
\left(\prod_{i<j}a_i\right)
\left(\prod_{i>j}b_i\right).
$$

在 $M=1$ 时式（176.1）为 $n\eta$；当 $0\le M<1$ 时，所有 horizon 的上界统一不超过 $\eta/(1-M)^2$；当 $M>1$ 时，该界显示出最坏情形的指数放大因子。

### 证明

记 $A_j=\Phi_j^*$、$B_j=P_{\Phi_j}$。乘积的望远镜恒等式给出

$$
A_1\cdots A_n-B_1\cdots B_n
=
\sum_{j=1}^{n}
A_1\cdots A_{j-1}(A_j-B_j)B_{j+1}\cdots B_n.
$$

作用于 $H$ 后取范数，并使用

$$
\|A_j-B_j\|\le\eta,
\qquad
\|A_i\|,\|B_i\|\le M,
\qquad
\|H\|\le1,
$$

每一项至多为 $\eta M^{n-1}$，求和即得（176.1）。若使用不等的 $a_j,b_j$，同一估计逐项给出所述乘积和。证毕。

**推论 176.3（收缩与放大两种情形）。** 若接口拉回及其近似代表均为严格收缩，近似闭合误差在所有有限 horizon 上有统一上界；若 $M>1$，逐步误差的最坏界可能含有 $M^{n-1}$ 的放大，即使每一步的局部算子缺陷都相同。此处的统一收缩上界来自 $nM^{n-1}\le(1-M)^{-2}$，不是把未经假设的递推误差写成几何级数。

这里的范数界是模型内的效果空间界，不替代对条件化分支概率的 $1/p_*$ 检查；两种放大机制可以同时出现。

---

## 177. 终端化一旦合并因果方向，后处理不能普遍恢复

把内部边界送入一个终端摘要 $\mathcal C$ 后，若它的纤维中仍有未来可区分的状态，则任何只作用于摘要的恢复都无法补回被合并的方向。

**定理 177.1（终端化的不可逆性）。** 设 $\mathcal C:\mathcal X\to\mathcal Y$ 是线性终端化映射。若存在 $x,y\in\mathcal X$ 使

$$
\mathcal C(x)=\mathcal C(y)
$$

但存在允许接口词 $\Phi_1,\ldots,\Phi_n$ 和终端效果 $H$ 满足

$$
H(\Phi_n\circ\cdots\circ\Phi_1(x))
\ne
H(\Phi_n\circ\cdots\circ\Phi_1(y)),
$$

则不存在恢复映射 $\mathcal R:\mathcal Y\to\mathcal X$ 能同时保持这两个状态的全部续接读数。特别地，不存在满足

$$
H\circ\Phi_n\circ\cdots\circ\Phi_1
=
\overline H\circ\mathcal C
$$

对所有声明续接都成立的单一摘要坐标。

### 证明

$\mathcal C(x)=\mathcal C(y)$ 迫使 $\mathcal R\mathcal C(x)=\mathcal R\mathcal C(y)$，所以任何只依赖摘要的后处理对这两个输入给出相同结果，不能同时重现两个不同的续接读数。若存在所述因子化，则右侧在 $x,y$ 上相同，而左侧不同，直接矛盾。证毕。

**例 177.2（交换方向被终端坐标抹掉）。** 取 $\mathcal X=\mathbb R^2$、$\mathcal C(x_1,x_2)=x_1$，接口 $\Phi(x_1,x_2)=(x_2,x_1)$，终端效果 $H(x)=x_1$。则 $x=(1,0)$ 与 $y=(1,1)$ 的终端摘要相同，但续接读数分别为 $0$ 与 $1$。任何对 $x_1$ 的后处理都不能恢复 $x_2$。

---

## 178. AHH：终端摘要、因果闭包和恢复映射构成不可逆阶梯

**关系结论 178.1（边界压缩的不可逆阶梯）。** 在有限维线性模型中：

$$
\boxed{
\begin{array}{c|c}
\text{层级}&\text{可保证的内容}\\
\hline
\text{终端摘要 }V_0&\text{当前终端任务}\\
\text{精确因果闭包 }V_\infty&\text{所有有限声明续接}\\
\text{近似闭包 }(V,\eta,M)&\text{带 horizon 的误差合同}\\
\text{终端化映射 }\mathcal C&\text{若有未来核方向则不可普遍恢复}
\end{array}
}
\tag{178.1}
$$

终端摘要只有在自身因果闭合时才可递归复用；近似闭合必须同时记录拉回范数和 horizon；一旦终端化把 $V_\infty^\perp$ 之外的方向合并，任何摘要后处理都不能保证恢复。

AHH 在于：**全息不是“保存后可以再加工”这么简单；摘要是否保留未来可拉回的效果空间，决定了信息能否继续组合，而终端化合并因果方向会产生严格不可逆的任务损失。**

这把状态压缩、接口拼接和恢复问题放进同一条偏序：$V_0\subseteq V_\infty$ 决定精确递归范围，近似误差决定有限资源范围，$\mathcal C$ 的纤维决定不可恢复方向。任何声称“终端输出足够、未来可以再推回”的说法，都必须先证明相应的伴随闭包或给出恢复所需的额外接口。

**来源与边界 178.2。** 本批在有限维线性效果空间、声明接口映射族和有限续接任务下推导规范评价商、近似闭合误差、终端化不可逆性及边界层级。没有把线性恢复映射自动解释为物理逆过程，没有推广到非线性摘要、无限维闭包、未知接口或物理钟标定；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 179. 允许续接扩张会单调增加边界成本

前面的闭包秩依赖于两个合同：当前要回答哪些终端效果，以及未来允许调用哪些接口。改变任一合同，必须重新计算闭包；不能把旧合同下的充分性外推到新任务。

**定义 179.1（任务对与闭包算子）。** 令

$$
\mathfrak T=(\mathcal F,\mathcal C),
$$

其中 $\mathcal F\subseteq\mathcal X^*$ 是终端效果族、$\mathcal C$ 是允许接口族。定义

$$
\Gamma(\mathfrak T)
=
\operatorname{span}\left\{
(\Phi_1^*\circ\cdots\circ\Phi_n^*)(H):
 n\ge0,
 H\in\mathcal F,
 \Phi_j\in\mathcal C
\right\}.
$$

对任意有限维效果子空间 $V$，记 $\mathsf q_V$ 为按 §175 同样方式由一组基给出的评价坐标；坐标基的改变只产生可逆线性变换。

约定 $n=0$ 时表达式为 $H$。若

$$
\mathfrak T_1\preceq\mathfrak T_2
\iff
\mathcal F_1\subseteq\mathcal F_2
\quad\text{且}\quad
\mathcal C_1\subseteq\mathcal C_2,
$$

就称第二个续接合同扩张了第一个。

**定理 179.2（合同扩张的单调性）。** 若 $\mathfrak T_1\preceq\mathfrak T_2$，则

$$
\boxed{
\Gamma(\mathfrak T_1)
\subseteq
\Gamma(\mathfrak T_2).
}
\tag{179.1}
$$

令 $K_i=\Gamma(\mathfrak T_i)^\perp\subseteq\mathcal X$。则

$$
K_2\subseteq K_1,
$$

并且第一个评价商在第二个评价商上有唯一线性因子化：存在唯一线性映射 $L$ 使

$$
\mathsf q_{\Gamma(\mathfrak T_1)}
=
L\circ\mathsf q_{\Gamma(\mathfrak T_2)}
$$

在第二个评价商的像上成立。因此闭包秩满足

$$
\dim\Gamma(\mathfrak T_1)
\le
\dim\Gamma(\mathfrak T_2).
$$

### 证明

$\Gamma(\mathfrak T_1)$ 的每个生成元仍然是 $\mathfrak T_2$ 的允许终端效果和接口词，所以（179.1）成立。对偶取正交补反向包含给出 $K_2\subseteq K_1$。

取 $\Gamma(\mathfrak T_1)$ 的一组基。若两个状态在 $\mathsf q_{\Gamma(\mathfrak T_2)}$ 下相同，它们对较小闭包的所有效果也相同，因此 $\mathsf q_{\Gamma(\mathfrak T_1)}$ 在第二个评价商的每个纤维上为常值。有限维因子化给出 $L$；在像空间上，因子化唯一。秩不等式是子空间包含的维数不等式。证毕。

**例 179.3（只增加一个后段接口也可能增加一整维）。** 取 $\mathcal X=\mathbb R^2$，终端效果 $F_0(x_1,x_2)=x_1$。令 $\mathfrak T_1$ 只含恒等接口，令 $\mathfrak T_2$ 另外允许交换接口

$$
S(x_1,x_2)=(x_2,x_1).
$$

则

$$
\Gamma(\mathfrak T_1)=\operatorname{span}\{F_0\},
\qquad
\Gamma(\mathfrak T_2)=\operatorname{span}\{F_0,F_0\circ S\}
=\operatorname{span}\{x_1,x_2\}.
$$

所以旧终端摘要的秩为一，而扩张合同要求秩为二。两个状态在旧合同下相同，不代表它们在新合同下仍相同。

这条单调性把“新增观察权限”的代价写成了闭包偏序：权限扩张只能细分原来的等价类，不能由旧摘要自动制造被删去的方向。

---

## 180. 随机调度的闭包不等于逐词闭包

允许接口词逐次选择时，记录接口标签会保留每条路径；若先把接口标签作概率平均，再反复作用，可能发生代数抵消；若联合记录仍可作相干读取，还会出现额外交叉项。两种操作的顺序必须写入边界合同。

**定义 180.1（词闭包与调度闭包）。** 设允许接口为有限族

$$
\mathcal C=\{\Phi_1,\ldots,\Phi_m\},
\qquad
A_i=\Phi_i^*.
$$

终端效果族记为 $\mathcal F$。词闭包为

$$
V_{\mathrm{word}}
=
\operatorname{span}\{A_{i_n}\cdots A_{i_1}H:
 n\ge0,\ H\in\mathcal F\}.
$$

对概率向量 $p=(p_1,\ldots,p_m)$，定义平均拉回

$$
T_p=\sum_{i=1}^mp_iA_i.
$$

给定调度族 $\mathfrak P\subseteq\Delta_m$，定义调度闭包

$$
V_{\mathfrak P}
=
\operatorname{span}\{T_{p_n}\cdots T_{p_1}H:
 n\ge0,\ H\in\mathcal F,\ p_j\in\mathfrak P\}.
$$

**定理 180.2（平均调度的包含关系）。** 总有

$$
\boxed{
V_{\mathfrak P}\subseteq V_{\mathrm{word}}.
}
\tag{180.1}
$$

若 $\mathfrak P$ 包含每个顶点分布 $\delta_i$，则

$$
\boxed{
V_{\mathfrak P}=V_{\mathrm{word}}.
}
\tag{180.2}
$$

### 证明

把每个平均算子展开：

$$
T_{p_n}\cdots T_{p_1}H
=
\sum_{i_1,\ldots,i_n}
(p_1)_{i_1}\cdots(p_n)_{i_n}
A_{i_n}\cdots A_{i_1}H.
$$

右侧属于词闭包，得到（180.1）。若 $\delta_i\in\mathfrak P$，取 $p_j=\delta_{i_j}$ 就直接得到每个逐词生成元，反向包含成立，故得（180.2）。证毕。

**例 180.3（固定平均会抹掉逐词方向）。** 在抽象线性接口模型中取

$$
\mathcal X^*=\mathbb R^2,
\qquad
H=e_1,
\qquad
S=\begin{pmatrix}0&1\\1&0\end{pmatrix},
$$

并令 $A_1=S$、$A_2=-S$。逐词闭包包含 $H$ 与 $SH=e_2$，所以

$$
V_{\mathrm{word}}=\mathbb R^2.
$$

但固定均匀调度 $p=(1/2,1/2)$ 给出

$$
T_p=\tfrac12(S-S)=0,
$$

从而

$$
V_{\{p\}}=\operatorname{span}\{H\}
\subsetneq
V_{\mathrm{word}}.
$$

因此“先平均再递归”与“保留标签后逐词递归”一般不交换。这个反例只使用线性接口；若要把两个接口解释为具体量子仪器，还必须另行验证正性、完全正性及记录合同。

---

## 181. 折扣 resolvent 只提供带权续接合同

当任务只关心按 horizon 衰减的平均响应，可以把无限词压缩为一个 resolvent；这个压缩有严格尾误差，但它不自动等价于保留每个离散 horizon。

**定义 181.1（固定调度的折扣响应）。** 固定一个调度 $p$，写 $T=T_p$。在 $\mathcal X^*$ 上固定次乘法范数，取 $\lambda\ge0$ 满足

$$
\lambda\|T\|<1.
$$

对 $H\in\mathcal X^*$ 定义

$$
\mathsf R_{\lambda,T}(H)
=
\sum_{n=0}^{\infty}\lambda^nT^nH.
$$

**定理 181.2（折扣响应的收敛、方程与尾界）。** 上述级数在范数下绝对收敛，并满足

$$
\boxed{
\mathsf R_{\lambda,T}(H)
=(I-\lambda T)^{-1}H,
}
\tag{181.1}
$$

以及对截断响应

$$
\mathsf R^{(N)}_{\lambda,T}(H)
=\sum_{n=0}^{N}\lambda^nT^nH
$$

的尾误差

$$
\boxed{
\left\|
\mathsf R_{\lambda,T}(H)-\mathsf R^{(N)}_{\lambda,T}(H)
\right\|
\le
\frac{\|H\|(\lambda\|T\|)^{N+1}}
{1-\lambda\|T\|}.
}
\tag{181.2}
$$

### 证明

由次乘法性，级数各项范数至多为

$$
\|H\|(\lambda\|T\|)^n.
$$

几何级数收敛，尾和给出（181.2）。逐项作用 $I-\lambda T$ 后，除首项 $H$ 外相邻项望远镜抵消，得到

$$
(I-\lambda T)\mathsf R_{\lambda,T}(H)=H.
$$

因为 $\lambda\|T\|<1$，Neumann 级数同时给出 $I-\lambda T$ 的逆，故得（181.1）。证毕。

**定理 181.3（一个折扣读数不保持全部 horizon）。** 取 $\mathcal X=\mathbb R^2$，并把 $T$ 视为作用在效果空间 $\mathcal X^*$ 上的交换算子，令终端效果 $H=e_1^*$，并取 $0<\lambda<1$。则

$$
\mathsf R_{\lambda,T}(H)
=\frac{e_1^*+\lambda e_2^*}{1-\lambda^2}.
$$

存在非零状态差

$$
\Delta=-\lambda e_1+e_2
$$

使

$$
\mathsf R_{\lambda,T}(H)(\Delta)=0,
$$

但

$$
H(\Delta)=-\lambda\ne0,
\qquad
(TH)(\Delta)=e_2^*(\Delta)=1.
$$

所以两个边界状态若只保留这一个折扣读数，可以在折扣任务上相同，却在 horizon $0$ 和 $1$ 的离散任务上不同。

### 证明

交换矩阵满足 $T^2=I$，故

$$
\sum_{n\ge0}\lambda^nT^nH
=
\frac{H+\lambda TH}{1-\lambda^2}.
$$

将 $\Delta$ 代入，分子为 $(-\lambda)+\lambda=0$；而两个未加权效果的取值分别为 $-\lambda$ 与 $1$。证毕。

因此 resolvent 的充分性必须连同权重 $\lambda$、调度 $p$ 和目标测试族一起声明。它是带权续接的接口，不是无条件的“全部未来”接口。

---

## 182. AHH：闭包、调度和折扣形成三层边界合同

**关系结论 182.1（从逐词到带权未来的边界阶梯）。** 在有限维线性模型中：

$$
\boxed{
\begin{array}{c|c|c}
\text{边界层}&\text{保留的关系}&\text{可保证的任务}\\
\hline
V_{\mathrm{word}}&\text{每个允许接口词及其终端效果}&\text{全部有限确定性续接}\\
V_{\mathfrak P}&\text{声明调度族的平均拉回}&\text{该调度族的有限随机续接}\\
\mathsf R_{\lambda,T}&\text{按 }\lambda^n\text{ 加权的总响应}&\text{固定调度的折扣任务}\\
\end{array}
}
\tag{182.1}
$$

逐词闭包先保留标签再组合；调度闭包把标签按声明的概率合同组合；折扣 resolvent 进一步把不同 horizon 按权重相加。每一步都是信息商，而且包含关系一般严格。

AHH 在于：**“未来”不是单一对象；它至少要标明接口词是否可区分、调度是否可访问、horizon 是否带权。先平均会丢掉逐词方向，先折扣会把不同时间层合并；这些压缩一旦合并了目标任务可区分的方向，后处理不能普遍恢复。**

这把边界成本写成一条带合同的偏序：扩大接口标签或调度权限只能扩大闭包，加入折扣则改变需要保持的测试族。任何声称“一个平均终端输出包含全部未来”的说法，都必须给出从目标任务族到该摘要的因子化证明；找不到因子化时，二维或符号矩阵反例足以否定普适充分性。

**来源与边界 182.2。** 本批在有限维线性效果空间、有限接口族、概率调度与严格收敛的折扣参数下推导合同扩张单调性、逐词/平均调度闭包差异、resolvent 尾误差及带权边界阶梯。没有把抽象负接口自动解释为物理量子仪器，没有把折扣参数解释为物理钟速率，没有推广到无限维谱或未知接口识别；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 183. 双侧响应的 Hankel 秩是递归边界的下界

前两批主要从效果一侧构造闭包。本节固定一个接口反复调用，并同时保留可进入的初始边界族，研究这份双侧响应本身需要多少状态坐标。

**定义 183.1（固定接口的双侧响应）。** 令 $\mathcal X$ 为有限维状态空间，$T:\mathcal X\to\mathcal X$ 为一个固定接口，$A=T^*$ 为其效果拉回。取有限初始族

$$
\mathcal B=\{b_1,\ldots,b_s\}\subseteq\mathcal X
$$

和有限终端效果族

$$
\mathcal F=\{f_1,\ldots,f_t\}\subseteq\mathcal X^*.
$$

定义响应序列

$$
 h_{ij}(k)=f_i(T^k b_j),
 \qquad k\ge0,
$$

以及有限 Hankel 块

$$
\mathsf H_{N,M}
\bigl[(i,n),(j,m)\bigr]
=
 f_i(T^{n+m}b_j),
\quad
0\le n\le N,\ 0\le m\le M.
$$

令

$$
 r_{\mathrm H}
=
\sup_{N,M}\operatorname{rank}\mathsf H_{N,M}.
$$

因为 $\mathcal X$ 有限维，该上确界是有限整数。

**定理 183.2（Hankel 秩的摘要下界）。** 设 $S:\mathcal X\to Y$ 是线性边界摘要，并假定对每个 $i,n$ 都存在 $\widetilde f_{i,n}\in Y^*$ 使

$$
 f_i\circ T^n=\widetilde f_{i,n}\circ S.
$$

也就是说，摘要对这组初始源和固定接口的所有有限 horizon 终端读数充分。则

$$
\boxed{
 r_{\mathrm H}\le\dim Y.
}
\tag{183.1}
$$

### 证明

对任意 $N,M$，定义行算子和列算子

$$
\mathsf O_N[(i,n),y]=\widetilde f_{i,n}(y),
$$

$$
\mathsf R_M[y,(j,m)]=S(T^m b_j).
$$

由摘要因子化假设，

$$
\mathsf H_{N,M}=\mathsf O_N\mathsf R_M.
$$

所以

$$
\operatorname{rank}\mathsf H_{N,M}
\le\dim Y.
$$

对所有 $N,M$ 取上确界即得（183.1）。证毕。

这个下界同时依赖输入侧和输出侧：只有终端效果的数量并不能代替可达初始方向，只有初始状态的数量也不能代替未来读数。它是指定合同下的线性状态维数下界，不自动等同于物理记忆的 Hilbert 维数。

---

## 184. 可达—可观测商给出固定接口的最小线性实现

Hankel 秩可以进一步写成一个商空间维数，从而把“哪些内部方向真正参与响应”分开。

**定义 184.1（可达空间与不可观测核）。** 令

$$
\mathcal R
=\operatorname{span}\{T^m b_j:m\ge0,\ 1\le j\le s\}
\subseteq\mathcal X,
$$

并定义

$$
\mathcal N
=
\mathcal R
\cap
\bigcap_{i,n}\ker(f_i\circ T^n).
$$

称 $\mathcal R$ 为可达空间，称 $\mathcal N$ 为在该源族和效果族下的可达不可观测方向。

**定理 184.2（最小商实现与 Hankel 等式）。** 有：

$$
T\mathcal R\subseteq\mathcal R,
\qquad
T\mathcal N\subseteq\mathcal N.
$$

因此 $T$ 在商空间

$$
\overline{\mathcal R}=\mathcal R/\mathcal N
$$

上诱导线性映射 $\overline T$。令 $\overline b_j=b_j+\mathcal N$，并令 $\overline f_i$ 为 $f_i$ 在商上的观测泛函。则

$$
 f_i(T^k b_j)
=
\overline f_i(\overline T^k\overline b_j)
$$

对所有 $i,j,k$ 成立，而且

$$
\boxed{
 r_{\mathrm H}
=\dim\overline{\mathcal R}
=\dim\mathcal R-\dim\mathcal N.
}
\tag{184.1}
$$

任何能够产生同一组双侧响应的有限维线性状态实现，其状态维数都不小于 $r_{\mathrm H}$；上述商实现达到该维数。

### 证明

$T\mathcal R\subseteq\mathcal R$ 直接来自生成式。若 $x\in\mathcal N$，则 $Tx\in\mathcal R$，且

$$
(f_i\circ T^n)(Tx)=f_i\circ T^{n+1}(x)=0
$$

对所有 $i,n$ 成立，故 $T\mathcal N\subseteq\mathcal N$，商上的 $\overline T$ 定义良好。由于每个 $f_iT^k$ 在 $\mathcal N$ 上为零，响应在商上保持不变。

令

$$
\mathcal O
=\operatorname{span}\{(f_i\circ T^n)|_{\mathcal R}:i,n\}
\subseteq\mathcal R^*.
$$

Hankel 的所有行生成 $\mathcal O$，所有列生成 $\mathcal R$ 的像；其条目正是自然配对

$$
\mathcal O\times\mathcal R\longrightarrow\mathbb R.
$$

该配对的右核正是 $\mathcal N$，所以其秩为

$$
\dim\mathcal R-\dim\mathcal N.
$$

有限维性保证取足够大的 $N,M$ 已包含 $\mathcal O$ 和 $\mathcal R$ 的基，故有限块秩的上确界就是该配对秩，得到（184.1）。任意另一线性实现的每个有限响应块都可分解为“输出矩阵乘状态矩阵”，因此其状态维数至少为 $r_{\mathrm H}$；这是定理 183.2 所用因子化下界的同一矩阵论证。商实现本身达到等号。证毕。

这里的最小性只针对声明的源族、固定接口和终端效果族。扩大任一族都会改变 $\mathcal R$ 或 $\mathcal N$，从而可能增加最小实现维数。

---

## 185. 最小商把全部响应序列压进一个共同递推

最小实现不仅给出维数，还给出所有 horizon 响应共享的代数递推；这比保存某一个折扣值更强。

**定理 185.1（共同最小多项式递推）。** 令 $\mu_{\overline T}(z)$ 为 $\overline T$ 的最小多项式，次数记为 $\mu$。写

$$
\mu_{\overline T}(z)
=z^\mu+c_{\mu-1}z^{\mu-1}+\cdots+c_0.
$$

则每个响应序列 $h_{ij}(k)=f_i(T^k b_j)$ 都满足

$$
\boxed{
 h_{ij}(k+\mu)
+c_{\mu-1}h_{ij}(k+\mu-1)
+\cdots
+c_0h_{ij}(k)=0
}
\tag{185.1}
$$

对所有 $i,j,k\ge0$ 成立。特别地，Cayley–Hamilton 定理给出一个次数不超过 $r_{\mathrm H}$ 的共同递推。

反过来，若一个非零首一多项式 $q$ 使全部响应序列都满足由 $q$ 给出的同样线性递推，则

$$
q(\overline T)=0,
$$

所以 $\deg q\ge\mu_{\overline T}$。因此共同递推的最小次数正是最小商转移的最小多项式次数。

### 证明

由最小多项式恒等式

$$
\overline T^\mu+c_{\mu-1}\overline T^{\mu-1}+\cdots+c_0I=0
$$

左乘任意 $\overline T^k$，再作用于 $\overline b_j$ 并由 $\overline f_i$ 读取，得到（185.1）。Cayley–Hamilton 给出次数上界。

反过来，设 $q$ 使全部序列满足递推。对任意 $m,j$，把递推式移位 $m$ 步，得到

$$
\overline f_i\,\overline T^n q(\overline T)\overline T^m\overline b_j=0
$$

对所有 $i,n$ 成立。可达向量 $\overline T^m\overline b_j$ 张成整个 $\overline{\mathcal R}$，而商的定义已经删去了所有对全部 $\overline f_i\overline T^n$ 不可观测的方向，所以

$$
q(\overline T)\overline T^m\overline b_j=0
$$

对所有 $m,j$。故 $q(\overline T)=0$，最小多项式的定义给出次数下界。证毕。

这份递推只说明精确代数响应的有限维闭合；从有限带噪读数估计递推系数，还需要额外的谱间隔、样本量和数值稳定性合同。

---

## 186. AHH：全息最小性是双侧响应的商，而非终端输出的数量

**关系结论 186.1（可达—可观测—递推三层边界）。** 对固定接口和指定源、效应族：

$$
\boxed{
\begin{array}{c|c|c}
\text{层级}&\text{保存的关系}&\text{可保证的内容}\\
\hline
\text{终端效果族}&\{f_i\}&\text{当前读数}\\
\text{Hankel 响应}&\{f_iT^{n+m}b_j\}&\text{双侧续接的秩下界}\\
\text{可达—可观测商}&\mathcal R/\mathcal N&\text{固定接口的最小线性实现}\\
\text{最小多项式}&\mu_{\overline T}&\text{全部响应序列的共同递推}
\end{array}
}
\tag{186.1}
$$

AHH 在于：**一个边界是否足够，不只由“有多少终端输出”决定；它由哪些初始方向能够进入、哪些方向能够被未来读出，以及两者在商空间中留下多少共同响应决定。Hankel 秩是这份双侧关系的不可压缩维数，最小多项式则是其 horizon 方向的共同代数记忆。**

因此，保存一个折扣 resolvent、保存一个终端通道或保存一个单次读数，都可能只覆盖双侧响应的投影；只有在目标任务族上给出因子化，才能把它们称为充分边界。这里的最小线性实现也不等同于最小物理 Hilbert 空间：正性、完全正性、仪器归一化和不可访问环境仍需另行纳入合同。

**来源与边界 186.2。** 本批在有限维线性状态空间、固定重复接口、有限初始源族与终端效果族下推导 Hankel 秩下界、可达—可观测商、最小线性实现及共同多项式递推。没有把抽象状态实现自动解释为量子仪器，没有把递推系数的可估计性混同于精确代数存在，没有推广到无限维谱、未知接口识别、带噪统计或物理钟标定；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 187. 双侧 Gramian 把可达与可观测方向压成响应谱

第 184 节给出了精确商的维数。本节在固定有限 horizon 上加入内积，把同一关系分解成“哪些方向能被送入”和“哪些方向能被读出”两侧的 Gramian。

**定义 187.1（有限 horizon 的双侧因子化）。** 在 $\mathcal X$ 上固定 Euclidean 内积，并用 Riesz 表示把每个效果 $f_i$ 写成向量 $\widehat f_i$。对给定 $N,M\ge0$，定义

$$
B_M:\mathbb R^{s(M+1)}\to\mathcal X,
\qquad
B_M e_{j,m}=T^m b_j,
$$

以及

$$
C_N:\mathcal X\to\mathbb R^{t(N+1)},
\qquad
(C_Nx)_{i,n}=f_i(T^n x).
$$

则第 183 节的响应块满足

$$
\mathsf H_{N,M}=C_NB_M.
$$

定义有限可达 Gramian 与有限可观测 Gramian：

$$
W_c^{(M)}=B_MB_M^{\mathsf T}
=\sum_{j=1}^s\sum_{m=0}^{M}
(T^m b_j)(T^m b_j)^{\mathsf T},
$$

$$
W_o^{(N)}=C_N^{\mathsf T}C_N
=\sum_{i=1}^t\sum_{n=0}^{N}
(T^n)^{\mathsf T}
\widehat f_i\widehat f_i^{\mathsf T}T^n.
$$

**定理 187.2（响应谱的 Gramian 表示）。** $\mathsf H_{N,M}$ 的非零奇异值，按重数计，正好等于

$$
W_o^{(N)1/2}W_c^{(M)1/2}
$$

的非零奇异值。因此

$$
\boxed{
\operatorname{rank}\mathsf H_{N,M}
=
\operatorname{rank}\!\left(
W_o^{(N)1/2}W_c^{(M)1/2}
\right).
}
\tag{187.1}
$$

### 证明

取 $B_M$ 的极分解

$$
B_M=W_c^{(M)1/2}V
$$

和 $C_N$ 的极分解

$$
C_N=UW_o^{(N)1/2},
$$

其中 $U,V$ 是相应支撑上的部分等距。于是

$$
\mathsf H_{N,M}
=U\,W_o^{(N)1/2}W_c^{(M)1/2}V.
$$

部分等距在非零支撑上保持奇异值，得到结论。证毕。

这份表示把响应的每个非零方向同时标记为可达和可观测；只有一侧 Gramian 的大特征值不能单独证明对应方向会在另一侧产生可读响应。

---

## 188. Hankel 奇异值给出有限任务的最佳秩预算

精确商回答“需要多少维才能零误差保持全部响应”。若允许一个明确的有限 horizon 误差预算，则响应块的奇异值给出最佳线性秩压缩。

**定义 188.1（响应谱与秩-$r$ 误差）。** 对固定 $N,M$，记

$$
\sigma_1\ge\sigma_2\ge\cdots\ge0
$$

为 $\mathsf H_{N,M}$ 的奇异值。对 $0\le r$ 定义

$$
\varepsilon_{2,r}=\sigma_{r+1},
\qquad
\varepsilon_{\mathrm F,r}
=\left(\sum_{k>r}\sigma_k^2\right)^{1/2},
$$

并约定超出秩的奇异值为零。

**定理 188.2（有限响应的最佳秩-$r$ 近似）。** 在所有秩不超过 $r$ 的矩阵 $K$ 中，截断奇异值分解

$$
\mathsf H_{N,M}=U\Sigma V^{\mathsf T},
\qquad
\mathsf H_{N,M}^{(r)}
=U\Sigma^{(r)}V^{\mathsf T}
$$

满足

$$
\boxed{
\inf_{\operatorname{rank}K\le r}
\|\mathsf H_{N,M}-K\|_2
=\varepsilon_{2,r},
}
\tag{188.1}
$$

以及

$$
\boxed{
\inf_{\operatorname{rank}K\le r}
\|\mathsf H_{N,M}-K\|_{\mathrm F}
=\varepsilon_{\mathrm F,r}.
}
\tag{188.2}
$$

因此任何精确依赖 $r$ 个线性边界坐标的响应因子化，其秩不能超过 $r$；若要求保留该有限块的算子范数误差至多 $\varepsilon$，必要条件是

$$
\sigma_{r+1}\le\varepsilon.
$$

### 证明

奇异值分解给出

$$
\mathsf H_{N,M}-\mathsf H_{N,M}^{(r)}
=\sum_{k>r}\sigma_k u_kv_k^{\mathsf T}.
$$

其算子范数为最大剩余奇异值 $\sigma_{r+1}$，Frobenius 范数平方为剩余奇异值平方和。

对任意秩不超过 $r$ 的 $K$，其列空间维数至多为 $r$。取前 $r+1$ 个左奇异向量张成的子空间，并用极小极大原理，至少有一个单位向量 $v$ 使 $Kv$ 无法同时捕获 $\sigma_{r+1}u_{r+1}$ 的正交分量，故

$$
\|\mathsf H_{N,M}-K\|_2\ge\sigma_{r+1}.
$$

Frobenius 下界由同一正交分解及平方和极小性得到。证毕。

这是一条任务级误差定理：$\mathsf H_{N,M}^{(r)}$ 是最佳响应矩阵，但它不自动携带一个满足移位一致性的时间演化算子。若要把截断矩阵实现成单一递归接口，还要另外证明投影后的转移、源注入和终端读取满足同一动力学合同。

---

## 189. 加权奇异方向是近似全息的合同坐标

不同 horizon、源和终端效果可能有不同的重要性。把它们的权重写进响应矩阵后，近似边界的方向会随任务合同改变。

**定义 189.1（加权响应任务）。** 取正半定权重矩阵

$$
D_o\succeq0,
\qquad
D_c\succeq0,
$$

分别作用在输出索引空间和源索引空间。定义加权响应

$$
\mathsf H^{(D_o,D_c)}
=D_o^{1/2}\mathsf H_{N,M}D_c^{1/2}.
$$

其奇异值记为

$$
\tau_1\ge\tau_2\ge\cdots\ge0.
$$

**定理 189.2（加权合同下的误差证书）。** 对任意秩不超过 $r$ 的加权响应摘要 $K_r$，有

$$
\left\|
\mathsf H^{(D_o,D_c)}-K_r
\right\|_2
\ge\tau_{r+1},
$$

并且截断奇异值分解达到等号。若 $a,b$ 为单位输出/源系数，采用该截断摘要时的加权标量误差满足

$$
\left|
 a^{\mathsf T}
\bigl(\mathsf H^{(D_o,D_c)}-\mathsf H^{(D_o,D_c)}_{(r)}\bigr)b
\right|
\le\tau_{r+1}.
\tag{189.1}
$$

### 证明

对加权矩阵直接应用定理 188.2，得到算子范数的最优性。对单位向量使用 Cauchy–Schwarz：

$$
|a^{\mathsf T}Eb|
\le\|a\|_2\|E\|_2\|b\|_2
\le\tau_{r+1},
$$

其中 $E$ 是截断残差。证毕。

权重为零的方向不会进入这份误差证书；这不是它们在未加权任务中不存在，而是当前合同选择不为它们付出预算。反之，改变 $D_o,D_c$ 可以改变奇异向量和所需秩。近似边界因此是任务相对的，不能把某一组权重下的“低奇异值”冒称为所有未来任务下的可忽略方向。

---

## 190. AHH：精确商、响应谱和物理实现是三种不同层次

**关系结论 190.1（双侧边界的精确—近似阶梯）。** 对固定接口、源族、效果族和有限 horizon：

$$
\boxed{
\begin{array}{c|c|c}
\text{层级}&\text{核心对象}&\text{保证}\\
\hline
\text{精确递归商}&\mathcal R/\mathcal N&\text{全部声明响应无误差}\\
\text{Hankel 秩}&r_{\mathrm H}&\text{任何精确线性实现的维数下界}\\
\text{奇异值尾}&(\sigma_{r+1},\varepsilon_{\mathrm F,r})&\text{有限任务的最佳秩-$r$误差}\\
\text{加权响应}&D_o^{1/2}\mathsf H D_c^{1/2}&\text{按合同分配的误差预算}\\
\text{物理实现}&\text{CP/正性/环境合同}&\text{能否实际执行该摘要}\\
\end{array}
}
\tag{190.1}
$$

AHH 在于：**可达—可观测商告诉我们哪些方向在精确关系中不可删；Hankel 奇异值告诉我们在明确的有限任务和误差预算下哪些响应方向可以近似合并；物理实现合同则决定这份线性压缩能否成为真正的仪器。三者不能用同一个“维数小”读数互相替代。**

因此，近似全息不是把小奇异值直接宣布为不存在，而是先声明 horizon、源/效果权重和允许误差，再由奇异值尾给出可审计的响应损失。若未来任务扩大或权重改变，必须重新计算谱；若要求无限 horizon，还需另行证明谱尾、稳定性和动态移位一致性。

**来源与边界 190.2。** 本批在有限维 Euclidean 线性状态空间、固定重复接口、有限源/效果族和有限 horizon 下推导双侧 Gramian 因子化、Hankel 奇异值的最佳秩误差、加权响应证书及近似边界阶梯。没有把矩阵截断自动解释为递归 CP 仪器，没有把小奇异值解释为物理不存在，没有推广到无限 horizon、带噪估计、未知系统辨识或物理钟标定；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 191. 串联边界的误差按因果增益传播

第 176 节控制单次伴随拉回的误差；多阶段关系还需要说明每一段的误差如何通过后续接口传到最终读数。

**定义 191.1（阶段响应合同）。** 取有限维赋范空间链

$$
\mathcal U_0
\xrightarrow{R_1}
\mathcal U_1
\xrightarrow{R_2}
\cdots
\xrightarrow{R_k}
\mathcal U_k.
$$

精确总响应为

$$
R^{[k]}=R_k\circ\cdots\circ R_1.
$$

对每一阶段给出近似响应 $\widehat R_i:\mathcal U_{i-1}\to\mathcal U_i$，并令

$$
\delta_i=\|R_i-\widehat R_i\|,
\qquad
g_i\ge\|R_i\|,
\qquad
\widehat g_i\ge\|\widehat R_i\|.
$$

**定理 191.2（串联误差的乘积望远镜界）。** 有

$$
\boxed{
\left\|R^{[k]}-\widehat R^{[k]}\right\|
\le
\sum_{i=1}^{k}
\left(\prod_{j=i+1}^{k}g_j\right)
\delta_i
\left(\prod_{j=1}^{i-1}\widehat g_j\right),
}
\tag{191.1}
$$

其中

$$
\widehat R^{[k]}
=\widehat R_k\circ\cdots\circ\widehat R_1.
$$

### 证明

乘积望远镜恒等式为

$$
R_k\cdots R_1-\widehat R_k\cdots\widehat R_1
=
\sum_{i=1}^{k}
R_k\cdots R_{i+1}
(R_i-\widehat R_i)
\widehat R_{i-1}\cdots\widehat R_1.
$$

逐项取算子范数，使用次乘法性以及 $g_j,\widehat g_j$ 的定义，即得（191.1）。证毕。

若全部阶段的两种增益都不超过 $G$，则

$$
\left\|R^{[k]}-\widehat R^{[k]}\right\|
\le
G^{k-1}\sum_{i=1}^{k}\delta_i.
$$

但这只是统一粗界；式（191.1）保留了每个局部误差在因果链中的具体放大位置。前段误差会经过更多后续阶段，后段误差则不会被同样的尾部增益放大。

---

## 192. 局部奇异截断给出可组合的全局误差证书

每一阶段都可以用自己的奇异值尾产生局部摘要，但局部最优只提供一个可组合的上界，不能自动宣称整个串联响应的全局最优。

**定义 192.1（阶段秩合同）。** 对每个阶段取秩不超过 $r_i$ 的截断响应

$$
\widehat R_i=R_i^{(r_i)},
$$

其中 $R_i^{(r_i)}$ 是 $R_i$ 的截断奇异值分解。令

$$
\delta_i
=\sigma_{r_i+1}(R_i),
$$

并约定超出秩的奇异值为零。

**定理 192.2（局部谱尾的串联界）。** 在定义 192.1 的阶段合同下，

$$
\boxed{
\left\|
R_k\cdots R_1-
R_k^{(r_k)}\cdots R_1^{(r_1)}
\right\|
\le
\sum_{i=1}^{k}
\left(\prod_{j=i+1}^{k}\|R_j\|\right)
\sigma_{r_i+1}(R_i)
\left(\prod_{j=1}^{i-1}\|R_j^{(r_j)}\|\right).
}
\tag{192.1}
$$

此外，

$$
\operatorname{rank}
\left(
R_k^{(r_k)}\cdots R_1^{(r_1)}
\right)
\le
\min_i r_i.
$$

### 证明

定理 191.2 直接代入

$$
\delta_i=\|R_i-R_i^{(r_i)}\|
=\sigma_{r_i+1}(R_i),
$$

得到（192.1）。秩不超过每个因子的秩，故不超过它们的最小值。证毕。

式（192.1）给出了一个真实的串联合同：只要测得各阶段的谱尾和增益，就能在同一个整体响应上结算误差。它没有声称“逐段各自最佳”会使最终乘积在全局秩约束下最佳；全局优化还要考虑不同阶段奇异向量之间的方向配合，以及乘积后的移位一致性。

---

## 193. 误差预算可以按因果放大系数分配

式（191.1）把每个阶段的局部误差乘上一个后续放大系数。若局部精度有成本，就可以先在响应合同内计算预算，而不把所有阶段强行要求同一误差。

**定义 193.1（固定增益下的预算问题）。** 令

$$
w_i
=
\left(\prod_{j=i+1}^{k}g_j\right)
\left(\prod_{j=1}^{i-1}\widehat g_j\right)
>0
$$

为第 $i$ 段的因果权重。假定把该段误差压到 $\delta_i>0$ 的成本模型为

$$
C_i(\delta_i)=a_i\delta_i^{-p},
\qquad
a_i>0,\ p>0.
$$

在总误差合同

$$
\sum_{i=1}^{k}w_i\delta_i\le\varepsilon
$$

下，研究总成本 $C(\delta)=\sum_i C_i(\delta_i)$ 的最小值。

**定理 193.2（幂律成本下的最优误差分配）。** 在没有额外上限的内点问题中，令

$$
S
=
\sum_{i=1}^{k}
a_i^{1/(p+1)}
w_i^{p/(p+1)}.
$$

则唯一最优分配为

$$
\boxed{
\delta_i^*
=
\frac{\varepsilon}{S}
\left(\frac{a_i}{w_i}\right)^{1/(p+1)},
}
\tag{193.1}
$$

最小总成本为

$$
\boxed{
C(\delta^*)
=
\frac{S^{p+1}}{\varepsilon^p}.
}
\tag{193.2}
$$

### 证明

成本随每个 $\delta_i$ 严格递减，所以最优点饱和约束。令拉格朗日乘子为 $\lambda>0$：

$$
\mathscr L
=
\sum_i a_i\delta_i^{-p}
+
\lambda
\left(
\sum_iw_i\delta_i-\varepsilon
\right).
$$

一阶条件给出

$$
-p a_i\delta_i^{-p-1}+\lambda w_i=0,
$$

故存在常数 $c>0$ 使

$$
\delta_i=c\left(\frac{a_i}{w_i}\right)^{1/(p+1)}.
$$

代入饱和约束得到 $c=\varepsilon/S$，即（193.1）。再代回成本：

$$
\sum_i a_i
\left[
\frac{\varepsilon}{S}
\left(\frac{a_i}{w_i}\right)^{1/(p+1)}
\right]^{-p}
=
\frac{S^p}{\varepsilon^p}
\sum_i a_i^{1/(p+1)}w_i^{p/(p+1)}
=
\frac{S^{p+1}}{\varepsilon^p}.
$$

严格凸性保证内点解唯一。若另有可达精度上限，需把相应约束加入并按活动集重新结算。证毕。

这说明前段和后段不应默认承担同样的局部精度：因果权重大的阶段更值得分配较小误差，但其具体比例还受该阶段的测量或压缩成本系数 $a_i$ 控制。

---

## 194. AHH：局部最优、全局响应与资源预算必须分层

**关系结论 194.1（串联全息的三层合同）。** 对多阶段边界关系：

$$
\boxed{
\begin{array}{c|c|c}
\text{层级}&\text{核心数据}&\text{可保证的内容}\\
\hline
\text{局部摘要}&(\widehat R_i,\delta_i)&\text{每一段的误差与秩}\\
\text{串联响应}&R_k\cdots R_1&\text{整体误差的因果放大界}\\
\text{预算合同}&(w_i,a_i,p,\varepsilon)&\text{达到总误差的成本分配}\\
\end{array}
}
\tag{194.1}
$$

AHH 在于：**每一段局部都压到最优，不等于整个递归关系全局最优；真正可组合的对象是带增益和误差的阶段合同。只有把局部谱尾沿因果顺序传播，再按总预算分配精度，近似全息才有可审计的整体意义。**

因此，边界压缩有两种容易混淆的失败：一是局部摘要本身的谱尾没有记录，二是谱尾虽已记录，却忽略后续接口对它的放大。前者使局部关系不可复核，后者使局部误差在整体响应中被低估。若链条进一步扩大，式（191.1）和式（193.1）必须随合同一起更新；它们不是一个与未来接口无关的固定常数。

**来源与边界 194.2。** 本批在有限维赋范阶段空间、线性串联响应、局部谱截断和幂律压缩成本模型下推导乘积望远镜误差、谱尾串联界、因果权重预算分配及阶段合同 AHH。没有把局部秩截断自动解释为全局最优递归仪器，没有把成本幂律宣称为现实实验定律，没有推广到非线性组合、未知增益、无限阶段或物理钟标定；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 195. 不确定阶段本身也是边界关系

确定性近似合同给出一个中心响应和一个误差半径；当阶段存在多个合法实现时，真正需要保存的是一族响应及其组合规则，而不是任意挑选一条名义路径。

**定义 195.1（集合值阶段合同）。** 对每个阶段 $i$，令

$$
\mathfrak R_i
\subseteq
\mathcal L(\mathcal U_{i-1},\mathcal U_i)
$$

为非空紧的合法响应集合。定义串联响应集合

$$
\mathfrak R_{[k]}
=
\mathfrak R_k\cdots\mathfrak R_1
=
\{R_k\circ\cdots\circ R_1:R_i\in\mathfrak R_i\}.
$$

若有名义响应 $\widehat R_i$ 和半径 $\delta_i$，满足

$$
\mathfrak R_i
\subseteq
\{R:\|R-\widehat R_i\|\le\delta_i\},
$$

则称 $(\widehat R_i,\delta_i)$ 是该阶段的球形不确定性合同。另记

$$
\gamma_i
\ge
\sup_{R\in\mathfrak R_i}\|R\|,
\qquad
\widehat\gamma_i\ge\|\widehat R_i\|.
$$

**定义 195.2（集合间的响应距离）。** 对两个非空紧响应集合 $\mathfrak A,\mathfrak B$，定义 Hausdorff 距离

$$
d_{\mathrm H}(\mathfrak A,\mathfrak B)
=
\max\left\{
\sup_{A\in\mathfrak A}\inf_{B\in\mathfrak B}\|A-B\|,
\sup_{B\in\mathfrak B}\inf_{A\in\mathfrak A}\|A-B\|
\right\}.
$$

它衡量两份合同在最坏合法实现下能否彼此匹配，不是某一个平均响应的距离。

---

## 196. 集合值串联的 Hausdorff 误差界

**定理 196.1（不确定合同的组合稳定性）。** 设对每个阶段有两个非空紧响应集合 $\mathfrak A_i,\mathfrak B_i$，满足

$$
d_{\mathrm H}(\mathfrak A_i,\mathfrak B_i)\le\delta_i,
$$

并取共同增益界

$$
\gamma_i
\ge
\sup_{R\in\mathfrak A_i\cup\mathfrak B_i}\|R\|.
$$

则

$$
\boxed{
d_{\mathrm H}
\left(
\mathfrak A_k\cdots\mathfrak A_1,
\mathfrak B_k\cdots\mathfrak B_1
\right)
\le
\sum_{i=1}^{k}
\left(\prod_{j\ne i}\gamma_j\right)\delta_i.
}
\tag{196.1}
$$

### 证明

任取

$$
A=A_k\cdots A_1
\in
\mathfrak A_k\cdots\mathfrak A_1.
$$

由 Hausdorff 距离，对每个 $i$ 可选取 $B_i\in\mathfrak B_i$ 使

$$
\|A_i-B_i\|\le\delta_i.
$$

乘积望远镜恒等式给出

$$
A_k\cdots A_1-B_k\cdots B_1
=
\sum_{i=1}^{k}
A_k\cdots A_{i+1}
(A_i-B_i)
B_{i-1}\cdots B_1.
$$

每一项范数至多为

$$
\left(\prod_{j>i}\gamma_j\right)
\delta_i
\left(\prod_{j<i}\gamma_j\right).
$$

这给出从第一集合到第二集合的单向距离界。交换 $\mathfrak A_i$ 与 $\mathfrak B_i$，得到反向同样的界；取二者最大值即得（196.1）。证毕。

当每个 $\mathfrak B_i$ 是名义单点 $\{\widehat R_i\}$ 时，式（196.1）退化为一个集合值的全局误差半径。与单一名义读数相比，集合合同还保留了“哪些实现仍然合法”的外层关系。

---

## 197. 忘掉相关性会制造不可逆的鲁棒过度估计

逐阶段边缘集合不总能决定串联集合；如果多个阶段共享同一个隐藏校准参数，相关性本身就是边界的一部分。

**定理 197.1（相同边缘、不同串联未来）。** 取标量阶段、$0\le\delta<1$，并考虑两个联合合同：

$$
\mathfrak J_{\mathrm{shared}}
=
\{(1+\theta,1-\theta):-\delta\le\theta\le\delta\},
$$

$$
\mathfrak J_{\mathrm{ind}}
=
[1-\delta,1+\delta]
\times
[1-\delta,1+\delta].
$$

两者的每个阶段边缘集合完全相同，但串联响应集合分别为

$$
\boxed{
\mathcal C_{\mathrm{shared}}
=
[1-\delta^2,1],
}
\tag{197.1}
$$

以及

$$
\boxed{
\mathcal C_{\mathrm{ind}}
=
[(1-\delta)^2,(1+\delta)^2].
}
\tag{197.2}
$$

当 $0<\delta<1$ 时，二者严格不同。

### 证明

共享合同的串联响应为

$$
(1+\theta)(1-\theta)=1-\theta^2.
$$

随着 $\theta\in[-\delta,\delta]$ 变化，其值域为 $[1-\delta^2,1]$。独立合同的两个因子可以分别取区间端点，且因子均为正，所以乘积值域为 $[(1-\delta)^2,(1+\delta)^2]$。当 $\delta>0$ 时，后者包含严格大于 $1$ 的值，而前者不含，故严格不同。证毕。

因此任何只保存两个阶段边缘集合、而忘掉它们是否由同一个 $\theta$ 共同实现的摘要，都不能在这两个联合模型上同时恢复正确的串联响应集合。后处理只能重新计算被保存的边缘信息，不能从相同边缘中补回未保存的联合约束。

这不是把“独立实现的最优值”拼成一次实验；它恰好说明联合来源必须先声明：共享校准、独立扰动和可相干控制是三种不同的关系合同。

---

## 198. AHH：鲁棒全息需要保存集合、增益和相关来源

**关系结论 198.1（从名义误差到联合不确定性）。** 对多阶段关系：

$$
\boxed{
\begin{array}{c|c|c}
\text{边界层}&\text{保存的对象}&\text{可保证的内容}\\
\hline
\text{名义阶段}&(\widehat R_i,\delta_i)&\text{相对于中心的局部误差}\\
\text{集合值阶段}&\mathfrak R_i,\gamma_i&\text{每段合法响应与增益}\\
\text{串联集合}&\mathfrak R_{[k]}&\text{全部合法整体未来}\\
\text{联合来源}&\mathfrak J\subseteq\prod_i\mathfrak R_i&\text{阶段之间的相关性约束}\\
\end{array}
}
\tag{198.1}
$$

AHH 在于：**鲁棒边界不只是“中心加半径”；它还要保存每一段的合法响应集合、组合增益以及阶段之间的共同来源。忘掉集合会漏掉最坏方向，忘掉增益会低估传播，忘掉相关性则会把同一个联合过程误写成独立过程。**

式（196.1）给出了在信息已被保守地集合化之后仍可组合的误差合同；定理 197.1 则说明，若联合相关性对目标响应有作用，单纯保存各边缘集合已经不可逆。扩大未来任务、允许新校准或允许跨阶段相干控制时，必须重新声明联合合同，而不能沿用旧的边缘摘要。

**来源与边界 198.2。** 本批在有限维赋范线性阶段、非空紧响应集合、算子范数 Hausdorff 距离和有限串联下推导集合值组合界、共享/独立不确定性的成对反例及鲁棒边界层级。没有把集合值响应自动解释为概率分布，没有把共享标量扰动推广为所有物理相关噪声，没有推广到无限阶段、非紧集合或物理钟标定；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 199. 事件条件化后的集合值边界

第 195—198 节保存了合法响应集合、串联增益和阶段相关性。本节加入一个常被遗漏的操作：**先取得一个指定事件，再把剩余关系条件化**。集合值边界经过归一化时，稀有事件会放大原有的不确定性；因此事件概率区间本身也是边界的一部分。

**定义 199.1（集合值分支合同）。** 令 $\mathfrak R$ 为有限维密度算子空间中的非空紧集，令 $\Phi$ 为完全正迹不增映射。写

$$
B=\Phi^*(I),
\qquad
p_\Phi(\rho)=\operatorname{Tr}(\rho B).
$$

定义分支概率区间

$$
p^-_\Phi(\mathfrak R)=\min_{\rho\in\mathfrak R}p_\Phi(\rho),
\qquad
p^+_\Phi(\mathfrak R)=\max_{\rho\in\mathfrak R}p_\Phi(\rho).
$$

当 $p^-_\Phi(\mathfrak R)>0$ 时，定义条件后继集合

$$
\boxed{
\mathsf C_\Phi(\mathfrak R)
=
\left\{
\frac{\Phi(\rho)}{p_\Phi(\rho)}:
\rho\in\mathfrak R
\right\}.
}
\tag{199.1}
$$

在状态空间上使用半迹距离

$$
D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1,
$$

并用它诱导集合的 Hausdorff 距离 $D_H$。这里的正概率下界是声明合同的一部分；有限次没有观察到事件，不能单独推出这样的下界。

**定理 199.2（集合条件化的概率区间与误差放大）。** 对两个非空紧状态集 $\mathfrak R,\mathfrak S$，令

$$
\varepsilon=D_H(\mathfrak R,\mathfrak S).
$$
则

$$
\boxed{
\left|p^-_\Phi(\mathfrak R)-p^-_\Phi(\mathfrak S)\right|
\le\varepsilon,
\qquad
\left|p^+_\Phi(\mathfrak R)-p^+_\Phi(\mathfrak S)\right|
\le\varepsilon.
}
\tag{199.2}
$$

若存在 $p_*>0$ 使

$$
\inf_{\rho\in\mathfrak R\cup\mathfrak S}p_\Phi(\rho)\ge p_*>
0,
$$
则

$$
\boxed{
D_H\!\left(\mathsf C_\Phi(\mathfrak R),
\mathsf C_\Phi(\mathfrak S)\right)
\le
\frac{\varepsilon}{p_*}.
}
\tag{199.3}
$$

### 证明

由于 $0\le B\le I$，迹距离的对偶表述给出

$$
|p_\Phi(\rho)-p_\Phi(\sigma)|
=|\operatorname{Tr}[(\rho-\sigma)B]|
\le D(\rho,\sigma).
$$

对紧集取最小值与最大值，得到（199.2）。

任取 $\rho\in\mathfrak R$。由 Hausdorff 距离和紧性，存在 $\sigma\in\mathfrak S$ 使 $D(\rho,\sigma)\le\varepsilon$。定理 25.2 应用于同一个分支 $\Phi$，并利用 $p_\Phi(\rho),p_\Phi(\sigma)\ge p_*$，得到

$$
D\!\left(
\frac{\Phi(\rho)}{p_\Phi(\rho)},
\frac{\Phi(\sigma)}{p_\Phi(\sigma)}
\right)
\le\frac{\varepsilon}{p_*}.
$$

交换 $\mathfrak R,\mathfrak S$ 得到反向包含的同一界，故有（199.3）。证毕。

**推论 199.3（正概率下界是条件边界的条件数）。** 在固定 $\varepsilon$ 下，式（199.3）的系数为 $1/p_*$. 因此，未归一化集合响应可以趋于相近，而若允许分支概率趋于零，条件后继集合不具有统一的连续性界。一个只保存未归一化响应误差、却没有保存分支概率下界的边界，不能给出条件后继的鲁棒误差证书。

这一区分把“事件稀有”与“状态本身不稳定”分开：前者来自归一化分母，后者来自原始集合或分支映射的误差。两者在边界合同中必须分别记账。

## 200. 最坏未来集合与概率平均后继

集合值边界描述允许的来源；概率平均后继还需要一个关于来源的先验。两者回答不同问题，不能把平均态自动当作最坏未来的代表。

**定义 200.1（事件后的先验平均）。** 令 $\mu$ 是 $\mathfrak R$ 上的概率测度，且

$$
\bar p=\int_{\mathfrak R}p_\Phi(\rho)\,d\mu(\rho)>0.
$$

定义事件后的先验平均态

$$
\boxed{
\bar\rho_{\Phi,\mu}
=
\frac{\int_{\mathfrak R}\Phi(\rho)\,d\mu(\rho)}{\bar p}.
}
\tag{200.1}
$$

若 $\tau_\rho=\Phi(\rho)/p_\Phi(\rho)$，则令

$$
 d\nu(\rho)=\frac{p_\Phi(\rho)}{\bar p}\,d\mu(\rho),
$$

便有

$$
\bar\rho_{\Phi,\mu}=\int_{\mathfrak R}\tau_\rho\,d\nu(\rho).
$$

这里的 $\nu$ 是取得事件以后对来源的更新权重，不是原来的 $\mu$.

**定理 200.2（平均后继只给出鲁棒区间中的一个凸组合）。** 对任意效果 $0\le H\le I$，有

$$
\boxed{
\min_{\tau\in\mathsf C_\Phi(\mathfrak R)}\operatorname{Tr}(\tau H)
\le
\operatorname{Tr}(\bar\rho_{\Phi,\mu}H)
\le
\max_{\tau\in\mathsf C_\Phi(\mathfrak R)}\operatorname{Tr}(\tau H).
}
\tag{200.2}
$$

左侧等号当且仅当 $\operatorname{Tr}(\tau_\rho H)$ 在 $\nu$-几乎处处取到该最小值；右侧等号具有相应的最大值条件。

### 证明

由定义，$\bar\rho_{\Phi,\mu}$ 是条件后继态的凸组合。对线性泛函 $\tau\mapsto\operatorname{Tr}(\tau H)$ 积分，所得值必位于其值域的闭区间内。若积分等于下端点，则非负函数

$$
\operatorname{Tr}(\tau_\rho H)-min_{\tau\in\mathsf C_\Phi(\mathfrak R)}\operatorname{Tr}(\tau H)
$$

的积分为零，故它在 $\nu$-几乎处处为零；反向同理。证毕。

**命题 200.3（相同平均后继不能决定最坏未来）。** 设事件分支为恒等映射，取

$$
\mathfrak R_A=\left\{\frac I2\right\},
\qquad
\mathfrak R_B=\{|0\rangle\langle0|,|1\rangle\langle1|\},
$$

并在第二个集合上给两个来源相等先验。两者的平均后继都为 $I/2$。但是对效果 $H=|0\rangle\langle0|$，有

$$
\left\{\operatorname{Tr}(\tau H):\tau\in\mathsf C_\Phi(\mathfrak R_A)\right\}
=\left\{\frac12\right\},
$$

而

$$
\left\{\operatorname{Tr}(\tau H):\tau\in\mathsf C_\Phi(\mathfrak R_B)\right\}
=\{0,1\}.
$$

### 证明

恒等分支的条件化不改变状态。集合 $\mathfrak R_B$ 的平均为

$$
\frac12|0\rangle\langle0|+\frac12|1\rangle\langle1|=\frac I2,
$$

但两集合的效果值域按直接取迹分别为单点 $1/2$ 与区间端点 $0,1$. 证毕。

因此，平均后继适用于已经声明先验并只询问期望值的任务；最坏未来则需要保存整个条件后继集合，不能由平均态后处理恢复。

## 201. 条件后的联合来源与矩形化误差

条件化不仅改变状态，还会改变状态与隐藏校准、环境或控制参数之间的联合来源。若把条件后的两个边缘随意相乘，就会引入原联合关系中从未允许的后继。

**定义 201.1（联合条件后继与矩形包络）。** 令 $\Lambda$ 为有限或紧参数空间，$\mathfrak J\subseteq\mathsf D(\mathcal H)\times\Lambda$ 为非空紧联合来源。对每个 $\lambda$ 给定完全正迹不增分支 $\Phi_\lambda$，定义

$$
 p_\lambda(\rho)=\operatorname{Tr}[\Phi_\lambda(\rho)],
$$

并在指定事件的正概率集合上定义

$$
\mathfrak J_\Phi
=
\left\{
\left(
\frac{\Phi_\lambda(\rho)}{p_\lambda(\rho)},\lambda\right):
(\rho,\lambda)\in\mathfrak J, p_\lambda(\rho)>0
\right\}.
$$

记其两个投影为 $\mathfrak R_\Phi$ 和 $\Lambda_\Phi$，矩形包络为

$$
\operatorname{Rect}(\mathfrak J_\Phi)
=\mathfrak R_\Phi\times\Lambda_\Phi.
$$

矩形化保留两个边缘集合，却允许它们任意重新配对。

**定理 201.2（矩形化只给出保守最坏界）。** 对任何实值未来响应 $h$，有

$$
\boxed{
\inf_{\operatorname{Rect}(\mathfrak J_\Phi)}h
\le
\inf_{\mathfrak J_\Phi}h
\le
\sup_{\mathfrak J_\Phi}h
\le
\sup_{\operatorname{Rect}(\mathfrak J_\Phi)}h.
}
\tag{201.1}
$$

若未来目标分别是下界或上界，矩形化只有在对应极值能够由原联合集合中的合法配对达到时才保持该端点；否则它会扩大鲁棒区间。

### 证明

有

$$
\mathfrak J_\Phi\subseteq
\operatorname{Rect}(\mathfrak J_\Phi).
$$

对集合包含关系取下确界与上确界，立即得到（201.1）。端点相等的充要条件就是扩大后的集合没有产生更小的下界或更大的上界。证毕。

**命题 201.3（条件边缘相同而最坏未来不同）。** 取二维系统、参数集 $\Lambda=\{0,1\}$，并令联合条件后继为

$$
\mathfrak J_\Phi
=\left\{
(|0\rangle\langle0|,0),
(|1\rangle\langle1|,1)
\right\}.
$$

定义未来效果 $H_\lambda=|\lambda\rangle\langle\lambda|$，响应为

$$
 h(\tau,\lambda)=\operatorname{Tr}(\tau H_\lambda).
$$

在真实联合集合上 $h=1$ 恒成立；在矩形包络上还包含 $(|0\rangle\langle0|,1)$ 与 $(|1\rangle\langle1|,0)$，故

$$
\inf_{\mathfrak J_\Phi}h=1,
\qquad
\inf_{\operatorname{Rect}(\mathfrak J_\Phi)}h=0.
$$

### 证明

真实联合集合中的参数和状态标签相同，故对应投影的期望均为一。矩形包络允许交叉配对，而交叉配对的投影正交，响应为零。证毕。

这个反例与第 197 节的共享/独立串联反例承担不同任务：那里比较的是阶段算子串联集合；这里比较的是**事件条件化以后，状态与隐藏来源的联合后继**。如果下一步控制读取了参数、环境记录或与之相关的端口，联合来源必须保留。

## 202. 概率加权的鲁棒全息合同

前面三节给出一条组合链：初态集合经事件归一化，条件后继再经未来响应族传播。最后把这条链压成一个可审计的边界对象。

**定义 202.1（概率加权鲁棒边界）。** 对集合值来源 $\mathfrak R$、事件分支 $\Phi$、未来响应族 $\mathfrak P$ 和联合来源 $\mathfrak J$，定义边界合同至少包含

$$
\boxed{
\eta_{\mathrm{rob}}
=
\left(
 p^-_\Phi,p^+_\Phi,
 \mathsf C_\Phi(\mathfrak R),
 \mathfrak J_\Phi,
 \Gamma_{\mathfrak P},
 \text{来源与控制记录}
\right),
}
\tag{202.1}
$$

其中 $\Gamma_{\mathfrak P}$ 是未来映射的统一增益上界。若任务只要求先验平均，则还需声明 $\mu$ 和 $\bar\rho_{\Phi,\mu}$；平均态不能替代式（202.1）中的条件集合或联合来源。

**定理 202.2（条件放大与未来增益的串联界）。** 用半迹距离比较状态，用

$$
\|T\|_{1\to1}=\sup_{\|X\|_1\le1}\|T(X)\|_1
$$

比较线性未来映射。设两个来源边界满足

$$
D_H(\mathfrak R,\mathfrak S)\le\varepsilon,
\qquad
\inf_{\rho\in\mathfrak R\cup\mathfrak S}p_\Phi(\rho)\ge p_*>0.
$$

设未来映射族 $\mathfrak P,\mathfrak Q$ 满足：每个 $T\in\mathfrak P$ 有 $U\in\mathfrak Q$ 使

$$
\frac12\|T-U\|_{1\to1}\le\delta,
$$

反向也成立，并且

$$
\|T\|_{1\to1},\|U\|_{1\to1}\le G.
$$

令

$$
\mathfrak P\circ\mathsf C_\Phi(\mathfrak R)
=\{T(\tau):T\in\mathfrak P,\ \tau\in\mathsf C_\Phi(\mathfrak R)\},
$$

则

$$
\boxed{
D_H\!\left(
\mathfrak P\circ\mathsf C_\Phi(\mathfrak R),
\mathfrak Q\circ\mathsf C_\Phi(\mathfrak S)
\right)
\le
\delta+G\frac{\varepsilon}{p_*}.
}
\tag{202.2}
$$

### 证明

任取 $T\in\mathfrak P$ 和 $\tau=\Phi(\rho)/p_\Phi(\rho)$，由定理 199.2 取 $\sigma\in\mathfrak S$ 使对应条件态 $\upsilon$ 满足

$$
D(\tau,\upsilon)\le\varepsilon/p_*.
$$

再取匹配的 $U\in\mathfrak Q$. 写 $X=\tau-\upsilon$. 由三角不等式与算子范数，

$$
\begin{aligned}
D(T\tau,U\upsilon)
&\le
\frac12\|(T-U)\upsilon\|_1
+\frac12\|T(\tau-\upsilon)\|_1\\
&\le
\delta+G D(\tau,\upsilon)
\le
\delta+G\frac{\varepsilon}{p_*}.
\end{aligned}
$$

反向选择同理，故得到 Hausdorff 界。证毕。

**关系结论 202.3（平均、条件集合、联合来源的分工）。** 对声明的未来任务，边界所能保证的内容分层如下：

$$
\boxed{
\begin{array}{c|c|c}
\text{边界记录}&\text{可回答的任务}&\text{遗漏时的失败}\\
\hline
\bar p,\bar\rho_{\Phi,\mu}&\text{给定先验的平均事件后期望}&\text{不能给出最坏界}\\
 p^- ,p^+ ,\mathsf C_\Phi(\mathfrak R)&\text{单步条件后继的鲁棒区间}&\text{稀有分支误差无界}\\
\mathfrak J_\Phi&\text{带隐藏来源的联合后续控制}&\text{矩形化引入不可能配对}\\
\Gamma_{\mathfrak P}&\text{条件集合向未来传播的误差证书}&\text{低估后续增益}\\
\end{array}
}
\tag{202.3}
$$

**AHH 202.4（概率加权的鲁棒全息）。** 鲁棒全息边界必须同时回答三件事：事件发生的概率范围是多少，发生后允许哪些条件关系，条件关系与隐藏来源之间保留哪些联合约束。若任务还包含未来组合，则要继续保存响应族的增益。一个先验平均态可以是正确的期望摘要，却不能自动成为最坏未来的充分边界；两个条件边缘集合可以分别正确，却可能在联合控制中生成从未存在的后继。

因此，波粒关系中的“事件切片”在不确定来源下不是单个归一化态，而是

$$
\boxed{
\text{事件概率区间}
+
\text{条件后继集合}
+
\text{联合来源}
+
\text{未来增益合同}.
}
$$

**来源与边界 202.5。** 本批在有限维密度算子、紧集合、完全正迹不增分支和有限算子范数未来映射下，推导集合条件化的概率区间稳定性、$1/p_*$ 误差放大、先验平均与最坏未来的严格区别、联合来源矩形化的保守性及条件后继到未来响应的组合界。没有把先验平均解释为无先验的物理事实，没有把矩形包络解释为真实独立实现，没有把正概率下界从有限观测自动推出，也没有推广到无限维、未知仪器、无限历史或物理钟标定；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 203. 集合化与事件条件化的交换律

第 199—202 节把事件条件化作用在一个来源集合上，第 200 节把同一操作作用在一个声明先验上。两者的顺序看起来相似，但对象不同：集合化允许重新选择来源，先验平均则固定了来源权重。本节先给出集合层面的精确交换律，再说明它为什么不等于先验平均的交换律。

**定义 203.1（正分支集合与有限凸包）。** 令 $\mathfrak R$ 为有限维密度算子空间中的非空集，令 $\Phi$ 为完全正迹不增映射。记

$$
\mathfrak R_+=\{\rho\in\mathfrak R:p_\Phi(\rho)>0\},
\qquad
\mathsf C_\Phi(\mathfrak R_+)
=
\left\{\frac{\Phi(\rho)}{p_\Phi(\rho)}:\rho\in\mathfrak R_+\right\}.
$$

在本节，$\operatorname{co}$ 表示有限凸组合；若来源集是紧的，有限维 Carathéodory 定理保证每个凸包点都可由至多 $d^2+1$ 个密度算子表示，其中 $d=\dim\mathcal H$。

**定理 203.2（集合层面的条件化—凸包交换律）。** 若 $\mathfrak R_+$ 非空，则

$$
\boxed{
\mathsf C_\Phi\!\left(\operatorname{co}\mathfrak R\right)_+
=
\operatorname{co}\!\left(\mathsf C_\Phi(\mathfrak R_+)\right),
}
\tag{203.1}
$$

其中左侧的下标 $+$ 表示只保留分支概率为正的凸包点。

### 证明

先取左侧任意点。存在 $\rho_i\in\mathfrak R$ 与 $w_i\ge0$、$\sum_iw_i=1$，使

$$
\rho=\sum_iw_i\rho_i,
\qquad
p_i=p_\Phi(\rho_i),
\qquad
p_\Phi(\rho)=\sum_iw_ip_i>0.
$$

若 $p_i=0$，该项对 $\Phi(\rho)$ 没有贡献，可以删去。对其余项令

$$
\tau_i=\frac{\Phi(\rho_i)}{p_i},
\qquad
\alpha_i=\frac{w_ip_i}{\sum_jw_jp_j}.
$$

则 $\alpha_i\ge0$、$\sum_i\alpha_i=1$，并且

$$
\frac{\Phi(\rho)}{p_\Phi(\rho)}
=\sum_i\alpha_i\tau_i.
$$

故左侧包含于右侧。

反过来，取右侧任意有限凸组合 $\sum_i\alpha_i\tau_i$，其中 $\tau_i=\Phi(\rho_i)/p_i$ 且 $p_i>0$。令

$$
c=\sum_i\frac{\alpha_i}{p_i},
\qquad
w_i=\frac{\alpha_i/p_i}{c}.
$$

则 $w_i\ge0$、$\sum_iw_i=1$，且

$$
\frac{\Phi(\sum_iw_i\rho_i)}
{p_\Phi(\sum_iw_i\rho_i)}
=
\frac{\sum_iw_ip_i\tau_i}{\sum_iw_ip_i}
=\sum_i\alpha_i\tau_i.
$$

故右侧也包含于左侧，证毕。

**推论 203.3（交换律的真正限制）。** 只要允许来源在 $\operatorname{co}\mathfrak R$ 中任意重新选择，集合值的条件后继可以精确写成正分支条件后继的凸包；各来源的分支概率差异只改变实现同一凸组合所需的原始权重。相反，若保留一个固定先验 $\mu$，则事件后的平均态仍是一个由 $p_\Phi(\rho)d\mu(\rho)$ 加权的单点，一般不等于整个凸包。

**命题 203.4（集合交换而先验不交换的二能级例子）。** 取

$$
\mathfrak R=\{P_0,P_1\},
\qquad
P_j=|j\rangle\langle j|,
$$

并令 $K=\operatorname{diag}(1,1/\sqrt2)$、$\Phi(X)=KXK$。则

$$
 p_\Phi(P_0)=1,
 \qquad
 p_\Phi(P_1)=\frac12,
 \qquad
 \mathsf C_\Phi(\operatorname{co}\mathfrak R)
=\operatorname{co}\{P_0,P_1\}.
$$

若先验给 $P_0,P_1$ 各权重 $1/2$，事件后的平均后继却为

$$
\bar\rho_{\Phi,\mu}
=\frac23P_0+\frac13P_1.
$$

### 证明

$K P_jK$ 分别为 $P_0$ 和 $P_1/2$，所以两个条件态仍为 $P_0,P_1$。定理 203.2 给出集合等式。先验平均的未归一化分子为

$$
\frac12P_0+\frac14P_1,
$$

其迹为 $3/4$，归一化得到所示结果。证毕。

这里的 AHH 是：**在集合语义中，条件化会重新参数化凸组合，但不会丢失凸包；在固定先验语义中，条件化会选择一个由事件概率偏置的平均点。把这两个“平均”混为一谈，会同时错估鲁棒范围和事件后的期望。**

## 204. 事件概率与条件未来的极小值不能互相除掉

事件后的未来效果有两个自然数值：无条件地取得事件并继续得到效果的概率，以及已经知道事件发生以后效果的条件概率。它们由同一分支产生，却不是同一个极小化问题。

**定义 204.1（无条件与条件的鲁棒值）。** 固定效果 $0\le H\le I$。对 $\rho$ 定义

$$
 p(\rho)=p_\Phi(\rho),
 \qquad
 h(\rho)=\operatorname{Tr}\!\left(
 \frac{\Phi(\rho)}{p(\rho)}H
 \right)
$$

只在 $p(\rho)>0$ 时定义 $h$，并令

$$
 a(\rho)=\operatorname{Tr}(\Phi(\rho)H)=p(\rho)h(\rho).
$$

对 $\mathfrak R_+$ 定义

$$
V_{\mathrm{cond}}=\inf_{\rho\in\mathfrak R_+}h(\rho),
\qquad
V_{\mathrm{uncond}}=\inf_{\rho\in\mathfrak R_+}a(\rho).
$$

**定理 204.2（极小值的概率夹逼）。** 若

$$
0<p_-\le p(\rho)\le p_+\le1
\qquad(\rho\in\mathfrak R_+),
$$

则

$$
\boxed{
 p_-V_{\mathrm{cond}}
\le V_{\mathrm{uncond}}
\le p_+V_{\mathrm{cond}},
}
\tag{204.1}
$$

并且

$$
\boxed{
\frac{V_{\mathrm{uncond}}}{p_+}
\le V_{\mathrm{cond}}
\le
\frac{V_{\mathrm{uncond}}}{p_-}.
}
\tag{204.2}
$$

一般不存在一个由 $V_{\mathrm{uncond}}$ 和单个平均概率唯一决定的等式。

### 证明

因为 $h(\rho)\ge V_{\mathrm{cond}}$ 且 $p(\rho)\ge p_-$，有

$$
 a(\rho)=p(\rho)h(\rho)\ge p_-V_{\mathrm{cond}}.
$$

取下确界得到第一条左侧界。另一方面，对任意 $\rho$ 有 $a(\rho)\le p_+h(\rho)$，故取一列 $h(\rho_n)\downarrow V_{\mathrm{cond}}$ 得

$$
V_{\mathrm{uncond}}\le p_+V_{\mathrm{cond}}.
$$

两边除以正数 $p_+,p_-$ 即得（204.2）。若两个量之间存在只依赖某个平均概率的普适等式，则同一概率与同一无条件值的不同 $(p,h)$ 配对会违反该等式；命题 204.3 给出具体反例。证毕。

**命题 204.3（同一无条件最坏值的不同条件未来）。** 在二能级系统中令

$$
\Phi(X)=KXK,
\qquad
K=\operatorname{diag}(\sqrt{0.9},\sqrt{0.1}),
$$

取来源 $P_0,P_1$ 与效果

$$
H=\operatorname{diag}(0.5,1).
$$

则

$$
(p(P_0),h(P_0),a(P_0))=(0.9,0.5,0.45),
$$

$$
(p(P_1),h(P_1),a(P_1))=(0.1,1,0.1).
$$

因此

$$
V_{\mathrm{cond}}=0.5,
\qquad
V_{\mathrm{uncond}}=0.1,
$$

而 $V_{\mathrm{uncond}}/p_-=1$、$V_{\mathrm{uncond}}/p_+=1/9$，两个简单除法都不能给出真实条件极小值。

### 证明

$K P_jK$ 的迹分别为 $0.9,0.1$，归一化后仍为 $P_j$。所以效果 $H$ 的条件值是 $0.5,1$，无条件值是 $0.45,0.1$。取两个有限来源的极小值即得。证毕。

这说明“事件发生后最坏会怎样”与“事件发生且随后成功的最坏联合概率”必须分开记录。前者属于条件边界，后者属于事件—未来联合边界；用一项除以另一项会隐式丢掉来源与概率的配对。

## 205. 分支树的联合来源不能由逐分支边缘替代

对一个多结果仪器，单个结果分支的条件集合可以分别正确，但一个策略的总期望仍然由同一个初始来源同时决定所有分支。若只保存每个分支的边缘，就会允许不同分支分别挑选不同来源。

**定义 205.1（事件树联合合同）。** 设有限结果集为 $Y$，仪器分支为 $\{\Phi_y\}_{y\in Y}$，满足 $\sum_y\Phi_y$ 为迹保持通道。对来源集合 $\mathfrak R$ 定义事件树关系集

$$
\boxed{
\mathfrak E(\mathfrak R)
=
\left\{
\left((p_y(\rho),\tau_y(\rho))\right)_{y\in Y}:
\rho\in\mathfrak R,\ p_y(\rho)>0\Rightarrow
\tau_y(\rho)=\frac{\Phi_y(\rho)}{p_y(\rho)}
\right\},
}
\tag{205.1}
$$

其中 $p_y(\rho)=\operatorname{Tr}\Phi_y(\rho)$，零概率分支保留为显式的不可达标签。逐分支边缘只保存

$$
\mathfrak E_y=\operatorname{proj}_y\mathfrak E(\mathfrak R),
$$

而不是完整的 $\mathfrak E(\mathfrak R)$。

给定各分支未来效果 $H_y$，策略的无条件值为

$$
F\left((p_y,\tau_y)_{y\in Y}\right)
=\sum_{y\in Y}p_y\operatorname{Tr}(\tau_yH_y),
$$

零概率分支的项按零计。

**定理 205.2（逐分支边缘只给策略值的保守包络）。** 对事件树联合集与其矩形包络，有

$$
\operatorname{Rect}(\mathfrak E)
=\prod_{y\in Y}\mathfrak E_y,
$$

并且

$$
\boxed{
\inf_{\operatorname{Rect}(\mathfrak E)}F
\le
\inf_{\mathfrak E}F
\le
\sup_{\mathfrak E}F
\le
\sup_{\operatorname{Rect}(\mathfrak E)}F.
}
\tag{205.2}
$$

只有当极值所需的逐分支选择能够由同一个来源同时实现时，矩形包络才保持对应的鲁棒端点。

### 证明

联合集显然包含于各投影的笛卡尔积。对任意实值函数 $F$，集合包含关系直接给出下确界和上确界的四项不等式。端点条件与第 201.2 定理相同。证毕。

**命题 205.3（相同分支边缘、不同总策略值）。** 令 $Y=\{0,1\}$，并抽象地给出两个可能来源的事件树关系

$$
\mathfrak E_{\mathrm{same}}=\{(A,A),(B,B)\},
\qquad
\mathfrak E_{\mathrm{opp}}=\{(A,B),(B,A)\},
$$

其中 $A,B$ 是两个合法的 $(p_y,\tau_y)$ 分支记录，且两集合的每个分支边缘都相同：

$$
\operatorname{proj}_0=\operatorname{proj}_1=\{A,B\}.
$$

取分支收益满足 $f_0(A)=f_1(B)=1$、$f_0(B)=f_1(A)=0$，并令

$$
F((z_0,z_1))=f_0(z_0)+f_1(z_1).
$$

则 $F$ 在 $\mathfrak E_{\mathrm{same}}$ 上恒为 $1$，而在 $\mathfrak E_{\mathrm{opp}}$ 上分别取 $2$ 与 $0$；仅保存两个分支边缘无法恢复总策略值或其鲁棒范围。

### 证明

对 $(A,A)$ 和 $(B,B)$，两项收益分别为 $(1,0)$ 与 $(0,1)$，总和都是 $1$。对 $(A,B)$，两项收益均为 $1$，总和为 $2$；对 $(B,A)$，两项均为零，总和为 $0$。投影集合在两种联合来源中都为 $\{A,B\}$，故边缘摘要完全相同而总值范围不同。证毕。

这个构造不把两个不同来源的最优分支拼成一次真实运行；它正好说明策略值要求一份共同来源的事件树。若任务只询问已经观测到某一个固定 $y$ 后的条件效果，逐分支边缘可能足够；一旦询问所有结果的联合期望或资源分配，必须恢复事件树联合合同。

## 206. AHH：选择感知的全息边界

前面四节把一个新的边界缺口分成三层：集合凸包中的来源重参数化，事件概率与条件效果的配对，以及多结果事件树中的共同来源。最后给出一个对声明任务族充分的选择感知边界。

**定义 206.1（选择感知边界）。** 对固定仪器、允许的未来策略族 $\mathcal F$ 和来源集合 $\mathfrak R$，定义

$$
\boxed{
\eta_{\mathrm{sel}}
=
\left(
\mathfrak E(\mathfrak R),
\text{来源先验（若询问平均值）},
\text{零概率标签},
\text{未来策略合同与增益}
\right).
}
\tag{206.1}
$$

若只询问单一结果的条件后继，可以把 $\mathfrak E(\mathfrak R)$ 投影到该结果并保留其正概率下界；若询问所有结果的联合期望、资源成本或自适应策略，必须保留完整事件树关系。

**定理 206.2（联合事件树是连续策略值的充分边界）。** 设 $\mathfrak E$ 为有限维事件树关系的非空紧集。若两个来源模型具有相同的 $\mathfrak E$，则对每个连续策略泛函 $F$，它们的可达值集合

$$
F(\mathfrak E)=\{F(e):e\in\mathfrak E\}
$$

完全相同。反之，若两个非空紧联合来源集 $\mathfrak E_1\ne\mathfrak E_2$，则存在一个连续实值泛函 $F$，使

$$
F(\mathfrak E_1)\ne F(\mathfrak E_2).
$$

因此，对于允许全部连续策略泛函的任务族，完整事件树关系是必要且充分的联合边界；逐分支边缘只有在任务族对联合来源不敏感时才足够。

### 证明

正向结论是定义直接给出的：同一个集合经同一个 $F$ 的像相同。

反向取 $e_0\in\mathfrak E_1\setminus\mathfrak E_2$。有限维欧氏空间中的紧集 $\mathfrak E_2$ 是闭集，故存在 $r>0$ 使 $e_0$ 的某个邻域不与 $\mathfrak E_2$ 相交。取连续截断函数

$$
F(e)=\max\left\{0,1-\frac{\|e-e_0\|}{r}\right\}.
$$

则 $F(e_0)=1$，而 $F$ 在 $\mathfrak E_2$ 上恒为零。因此两个像集不同。证毕。

**AHH 206.3（选择感知的全息边界）。** 事件记录不是从波体中抽出一个孤立的粒子点，而是对来源关系施加了一次选择。完整的选择感知边界必须保留：

$$
\boxed{
\text{同一来源生成的事件树}
+
\text{每条分支的概率—后继配对}
+
\text{零概率不可达信息}
+
\text{未来策略的增益与许可范围}.
}
$$

集合凸包可以在正分支层面精确重参数化；固定先验会留下事件偏置；无条件最坏值不能除以一个平均概率变成条件最坏值；逐分支边缘不能替代同一来源的联合事件树。这四个区别共同说明：**全息边界保存的不是“事件之后的一张平均照片”，而是允许选择怎样作用于来源、怎样改变后继、怎样在分支之间保持共同来源的关系合同。**

**来源与边界 206.4。** 本批在有限维密度算子、有限仪器结果集、完全正迹不增分支和紧联合来源下，证明集合层面的条件化—凸包交换律，区分无条件与条件鲁棒极小值，给出事件树逐分支边缘的保守包络和连续策略泛函的联合边界判据。没有把集合凸包交换律推广到固定先验平均，没有把抽象事件树任意解释为实际可相干读取的记录，没有把连续策略族等同于所有物理控制，也没有推广到无限维、未知仪器或物理钟标定；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 207. 记录过滤与非预见策略

第 205—206 节保存了同一来源生成的完整事件树。本节把“记录”本身作为时间递增的过滤来处理，并明确策略只能读取当前已经出现的记录。若把最终后继集合当作唯一边界，就会丢掉哪些来源在同一历史中仍然可以共同实现的信息。

**定义 207.1（有限记录过滤）。** 令 $\Omega$ 为有限或紧的完整来源空间，令

$$
r_t:\Omega\longrightarrow\mathcal H_t,
\qquad 0\le t\le N,
$$

为第 $t$ 步的记录映射。称 $(r_t)$ 为过滤，若存在忘却映射

$$
q_t:\mathcal H_{t+1}\longrightarrow\mathcal H_t
$$

使

$$
r_t=q_t\circ r_{t+1}.
$$

历史 $h\in\mathcal H_t$ 的来源纤维为

$$
\Omega_h=\{\omega\in\Omega:r_t(\omega)=h\}.
$$

在历史 $h$ 上的非预见策略是一个只依赖 $h$ 的动作 $a_t(h)$；它不能依赖尚未出现的 $r_{t+1},\ldots,r_N$。

**定义 207.2（历史条件边界）。** 给定初始来源集 $\mathfrak R\subseteq\Omega$，历史 $h$ 的条件边界为

$$
\mathfrak R_h=\mathfrak R\cap\Omega_h.
$$

若 $h'$ 满足 $q_t(h')=h$，则 $\mathfrak R_{h'}\subseteq\mathfrak R_h$。记 $\mathcal A_t(h)$ 为历史 $h$ 上允许的动作集合，记 $G_\pi(\omega)$ 为非预见策略 $\pi$ 在完整来源 $\omega$ 上的总收益。

**定理 207.3（固定动作下记录细化缩小鲁棒区间）。** 设过滤 $(r'_t)$ 比 $(r_t)$ 精细，即存在

$$
c_t:\mathcal H'_t\longrightarrow\mathcal H_t,
\qquad
r_t=c_t\circ r'_t.
$$

对任意粗历史 $h$ 和精历史 $h'$ 满足 $c_t(h')=h$，以及任意固定动作 $a\in\mathcal A_t(h)$，有

$$
\boxed{
\inf_{\omega\in\mathfrak R_{h'}}G_a(\omega)
\ge
\inf_{\omega\in\mathfrak R_h}G_a(\omega),
\qquad
\sup_{\omega\in\mathfrak R_{h'}}G_a(\omega)
\le
\sup_{\omega\in\mathfrak R_h}G_a(\omega).
}
\tag{207.1}
$$

若精记录允许的策略类包含粗记录策略的提升，则最大化的鲁棒值满足

$$
\boxed{
\sup_{\pi'\ {\rm 精细}}\inf_{\omega\in\mathfrak R}G_{\pi'}(\omega)
\ge
\sup_{\pi\ {\rm 粗}}\inf_{\omega\in\mathfrak R}G_{\pi}(\omega).
}
\tag{207.2}
$$

### 证明

由 $\mathfrak R_{h'}\subseteq\mathfrak R_h$，对同一个实值函数取下确界和上确界立即得到（207.1）。

任意粗策略 $\pi$ 都可以定义一个精策略 $\pi'$：在精历史 $h'$ 上执行粗历史 $c_t(h')$ 所规定的动作。因而精策略类包含粗策略类，先对每个粗策略比较其最坏收益，再取上确界，得到（207.2）。证毕。

记录细化有两种同时发生的作用：固定动作时，它删去不再相容的来源；允许自适应动作时，它还扩张了可用策略类。若在边界中只保存“细化后状态更窄”而不保存新增许可动作，便无法结算完整的信息价值。

## 208. 矩形来源下的 Bellman 递归

动态递归需要一个来源合同：在已经知道历史 $h$ 后，下一步的不确定选择是否可以独立地从每个子历史的条件集合中重新选取。这个性质就是本节的矩形性。

**定义 208.1（来源树与矩形性）。** 设每个历史 $h$ 有有限后继集合 $Y(h)$。一条完整来源 $\omega$ 由各历史上的局部参数 $\theta_h$ 和结果 $y_h$ 组成。给定条件局部集合 $\Theta_h\subseteq\Theta(h)$，称来源合同为矩形的，若任何满足

$$
\theta_h\in\Theta_h
$$

并且在每个历史上都遵守允许结果关系的局部选择，都能拼成一条合法完整来源。记 $\mathfrak J^{\square}$ 为所有这些拼接的完整来源集合。

对终端收益 $g$ 定义鲁棒策略值

$$
V(\mathfrak J,\pi)
=
\inf_{\omega\in\mathfrak J}G_\pi(\omega),
\qquad
V^*(\mathfrak J)
=
\sup_{\pi\ {\rm nonanticipative}}V(\mathfrak J,\pi).
$$

**定理 208.2（矩形来源上的 Bellman 等式）。** 在有限深度、有限动作和有限结果的矩形来源合同下，定义终端值 $V_h$ 为终端收益，向后递归

$$
\boxed{
V_h
=
\sup_{a\in\mathcal A(h)}
\inf_{\theta\in\Theta_h}
\left[
r(h,a,\theta)
+
\sum_{y\in Y(h)}
p(y\mid h,a,\theta)V_{hy}
\right].
}
\tag{208.1}
$$

则根历史的递归值等于

$$
\boxed{
V_{\mathrm{root}}=V^*(\mathfrak J^{\square}).
}
\tag{208.2}
$$

### 证明

按剩余深度归纳。终端历史上两边都等于给定终端收益。

设所有深度小于 $k$ 的子历史已经满足结论。固定当前历史 $h$ 和动作 $a$。由于来源矩形，当前局部参数 $\theta$ 的选择与每个后继历史中允许的来源选择可以分别完成，并拼成同一完整来源。因此，在固定 $a$ 下的最坏后继收益等于

$$
\inf_{\theta\in\Theta_h}
\left[
r(h,a,\theta)
+
\sum_y p(y\mid h,a,\theta)
\inf_{\pi_{hy}}\inf_{\omega_{hy}}G_{\pi_{hy}}(\omega_{hy})
\right].
$$

归纳假设把每个子问题的内层最优值替换为 $V_{hy}$。当前动作只影响当前历史及其后继，非预见性允许对不同后继历史分别选择子策略；故再对 $a$ 取上确界，得到（208.1）。在根历史应用同一等式即得（208.2）。证毕。

矩形性不是说物理来源真的独立，而是说当前鲁棒合同允许对每个历史的后继不确定性作这种重新组合。若真实来源非矩形，直接套用（208.1）计算的是一个矩形包络问题。

**推论 208.3（矩形化对最大化鲁棒值是保守的）。** 对任意来源集 $\mathfrak J\subseteq\mathfrak J^{\square}$，

$$
\boxed{
V^*(\mathfrak J^{\square})
\le
V^*(\mathfrak J).
}
\tag{208.3}
$$

### 证明

对每个非预见策略 $\pi$，来源集扩大使下确界不增：

$$
\inf_{\omega\in\mathfrak J^{\square}}G_\pi(\omega)
\le
\inf_{\omega\in\mathfrak J}G_\pi(\omega).
$$

再对同一策略类取上确界即得。证毕。

**命题 208.4（相关来源使 Bellman 值严格过低）。** 根历史先观察 $x\in\{0,1\}$，随后选择动作 $a\in\{0,1\}$，终端隐藏目标为 $z\in\{0,1\}$，收益为

$$
g(a,z)=
\begin{cases}
1,&a=z,\\
0,&a\ne z.
\end{cases}
$$

真实联合来源为

$$
\mathfrak J=\{(x,z)=(0,0),(1,1)\}.
$$

策略 $a(x)=x$ 给出

$$
V^*(\mathfrak J)=1.
$$

若只保存每个 $x$ 下的边缘集合 $\{0,1\}$，其矩形包络为

$$
\mathfrak J^{\square}
=\{0,1\}\times\{0,1\},
$$

则对任意策略都有某个 $z\ne a(x)$，故

$$
V^*(\mathfrak J^{\square})=0.
$$

### 证明

在真实来源中观察到 $x$ 就确定 $z$，策略 $a=x$ 恒得一分。矩形包络允许在观察到同一个 $x$ 后独立选择相反的 $z$，对任意动作都能使收益为零。证毕。

这个例子中的信息来自来源相关性，而不是来自额外的物理点击。把联合来源矩形化会抹掉“观察记录可以推断尚未观察量”的关系，因而 Bellman 递归的保守性可能是严格的。

## 209. 记录的价值与记录成本必须分开

记录细化通常提高可保证的控制值，但保存、传输和读取记录可能有成本。若把成本和信息价值混在一个未声明的平均态中，边界就无法说明增加记录究竟改变了哪一部分关系。

**定义 209.1（过滤上的信息值）。** 对记录过滤 $r$，令 $\Pi(r)$ 为所有只依赖该过滤的非预见策略，令

$$
W(r)=
\sup_{\pi\in\Pi(r)}
\inf_{\omega\in\mathfrak R}G_\pi(\omega)
$$

为最大化者的鲁棒信息值。若记录合同有代价 $C(r)\ge0$，则净值为

$$
W_C(r)=W(r)-C(r).
$$

**定理 209.2（纯信息细化的单调性）。** 若 $r'$ 精细于 $r$，并且记录本身没有改变仪器、来源或收益，即只增加可读取历史，则

$$
\boxed{
W(r')\ge W(r).
}
\tag{209.1}
$$

若存在一个粗策略的提升在某个精历史上能选择更高的最坏收益，则不等式严格。净值则满足

$$
W_C(r')-W_C(r)
=
\bigl(W(r')-W(r)\bigr)
-
\bigl(C(r')-C(r)\bigr),
$$

所以信息细化本身的单调性不能推出带成本净值的单调性。

### 证明

粗策略类嵌入精策略类，定理 207.3 已给出每个粗策略都有精细提升且收益不变。因此精细策略类的上确界至少不小于粗策略类的上确界。严格性由存在一个精策略在某个精历史上分辨来源并提高其最坏收益直接得到。净值等式是定义展开。证毕。

**命题 209.3（一个记录位带来严格鲁棒增益）。** 令隐藏来源 $z\in\{0,1\}$，来源集合为两点。无记录时动作只能固定为 $0$ 或 $1$，收益为 $g(a,z)=1_{a=z}$，故

$$
W(r_{\mathrm{coarse}})=0.
$$

若记录直接给出 $z$，允许策略 $a=z$，则

$$
W(r_{\mathrm{fine}})=1.
$$

若记录成本为 $c$，净值差为 $1-c$；因此只有在声明 $c<1$ 时，细化才提高净值。

### 证明

无记录的任一固定动作都被相反来源击败。精记录下动作与来源相同，收益恒为一。代入净值定义即得。证毕。

记录的作用因此有两个可分的层次：它先细分来源等价类，再扩张允许的非预见策略；记录成本是第三个独立合同，不能从状态集合宽度自动推断。

## 210. AHH：过滤化的全息边界

前面三节把选择感知边界推进到动态层：记录改变来源纤维，矩形性决定 Bellman 递归是否真实，策略价值还要扣除记录成本。现在把这些条件收束为过滤化边界。

**定义 210.1（过滤化全息合同）。** 对有限深度事件树，定义

$$
\boxed{
\eta_{\mathrm{fil}}
=
\left(
\{\mathfrak R_h:h\in\mathcal H_t,\ 0\le t\le N\},
\text{历史忘却映射},
\text{同一来源的子历史耦合},
\text{来源测度或先验（若询问分布）},
\text{非预见动作许可},
\text{记录成本与未来增益}
\right).
}
\tag{210.1}
$$

这里的“同一来源的子历史耦合”指各层纤维如何由同一个完整来源集合生成；只保存每个纤维的独立投影并不包含这项关系。

**定理 210.2（过滤化边界对非预见策略的充分性）。** 若两个关系体具有同构的过滤化全息合同：存在各层历史的双射，保持忘却映射、来源纤维、结果概率、动作许可、收益和成本，则对每个非预见策略都有相同的总收益分布；因此它们的鲁棒值、先验期望值以及带记录成本的净值完全相同。

### 证明

按历史深度归纳。根历史的同构保持初始来源和动作集合。假设某历史 $h$ 的来源、动作和当前收益在同构下对应。每个允许动作产生的后继结果概率与子历史纤维按假设一一对应，且忘却映射保持历史结构；因此在每个后继上递归应用归纳假设，得到同一条件收益分布。将后继按相同概率拼接，再加当前收益和相同成本，得到整条策略的相同分布。对来源取下确界或按先验积分都保持相等。证毕。

**定理 210.3（只保存单层投影不能保证动态充分性）。** 若两个过滤化来源合同在各层的单层投影相同，但其跨历史联合耦合不同，则存在一个有限深度非预见策略，使两者的鲁棒值不同。

### 证明

取命题 208.4 的两个来源合同。根层的观察坐标 $x$ 和隐藏目标坐标 $z$ 在两模型中的投影都为 $\{0,1\}$；但第一模型的联合来源满足 $z=x$，第二模型允许四个矩形配对。非预见策略 $a=x$ 在第一模型的鲁棒值为一，在第二模型为零。故相同单层投影不足以确定动态策略值。证毕。

**AHH 210.4（过滤化全息）。** 全息边界不是“某个时刻的后继集合”，而是一个带时间过滤的来源合同。它必须同时保存：

$$
\boxed{
\text{记录怎样细分来源}
+
\text{同一来源怎样贯穿各历史}
+
\text{策略在哪些历史可改变}
+
\text{记录与控制的成本和增益}.
}
$$

AHH 的核心是：**动态观察的价值不只来自把状态集合变小；它来自在不违反非预见性的前提下，把记录变成合法控制，并保留记录之间由同一来源施加的相关性。Bellman 递归只有在矩形来源合同下才是精确的；在非矩形关系上，它是对扩大来源的保守递归。**

**来源与边界 210.5。** 本批在有限深度、有限历史与动作、紧来源合同和非预见策略下，定义过滤化来源边界，证明记录细化对固定动作和最大化鲁棒值的单调性，证明矩形来源上的 Bellman 等式及矩形化保守性，给出相关来源使递归值严格变化的反例，并把过滤、耦合、策略许可和记录成本合并为动态全息合同。没有把 Bellman 递归推广到非矩形来源而仍宣称精确，没有把记录细化的价值与现实装置成本混同，没有把抽象来源变量自动解释为物理钟或观察者自由选择，也没有推广到无限深度、连续时间或未知仪器；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 211. 风险量词的三层分离

过滤化边界不仅要回答未来收益，还要回答失败概率。对同一个事件树，“每个来源都安全”“每个已到达历史都安全”和“按一个先验平均后安全”是三个不同命题。

**定义 211.1（策略风险）。** 固定非预见策略 $\pi$、完整来源集合 $\mathfrak J$ 和一个安全事件 $S_\pi$。对来源 $\omega$ 写

$$
P_\omega^\pi(S_\pi)
$$

为该来源下安全事件的概率，写

$$
R_\omega^\pi=1-P_\omega^\pi(S_\pi)
$$

为总风险。若 $\mu$ 是来源先验，定义三种风险合同：

$$
R_{\mathrm{worst}}(\pi)
=\sup_{\omega\in\mathfrak J}R_\omega^\pi,
$$

$$
R_{\mathrm{avg}}(\pi,\mu)
=\int_{\mathfrak J}R_\omega^\pi\,d\mu(\omega),
$$

以及在历史 $h$ 上的条件风险

$$
R_{\mathrm{cond}}(h,\pi)
=
\sup_{\omega\in\mathfrak J_h}
P_\omega^\pi(\neg S_\pi\mid h),
$$

其中只对 $P_\omega^\pi(h)>0$ 的来源定义条件概率。

**定理 211.2（风险量词的蕴含方向）。** 对 $0\le\alpha\le1$：

$$
R_{\mathrm{worst}}(\pi)\le\alpha
\Longrightarrow
R_{\mathrm{avg}}(\pi,\mu)\le\alpha
$$

对任意先验 $\mu$ 成立。反之，平均风险合同一般不能推出最坏风险合同。若对某个历史分割 $\{h_i\}$ 存在数列 $\alpha_i$ 使

$$
R_{\mathrm{cond}}(h_i,\pi)\le\alpha_i
\quad\text{对每个可达 }h_i,
$$

则对每个来源 $\omega$ 有

$$
\boxed{
R_\omega^\pi
\le
\sum_i P_\omega^\pi(h_i)\alpha_i
\le
\max_i\alpha_i.
}
\tag{211.1}
$$

### 证明

第一条由积分不超过被积函数的上确界得到。平均风险不能推出最坏风险，只需取一个小先验权重放在高风险来源上即可。

对历史分割使用全概率公式：

$$
R_\omega^\pi
=
\sum_iP_\omega^\pi(h_i)
P_\omega^\pi(\neg S_\pi\mid h_i).
$$

逐项使用条件风险界，得到第一项不等式；概率权重和为一，得到第二项不等式。证毕。

局部条件合同保留了“风险发生在哪个记录历史”的信息；若只保存总平均风险，稀有历史上的高条件风险会被平均权重掩盖。

**命题 211.3（同一平均风险、不同最坏风险）。** 取两个来源 $\omega_0,\omega_1$，安全事件概率分别为

$$
P_{\omega_0}(S)=1,
\qquad
P_{\omega_1}(S)=0.8.
$$

在均匀先验下，

$$
R_{\mathrm{avg}}=0.1,
\qquad
R_{\mathrm{worst}}=0.2.
$$

另一个模型令两个来源的安全概率都为 $0.9$，则同样有

$$
R_{\mathrm{avg}}=0.1,
$$

但

$$
R_{\mathrm{worst}}=0.1.
$$

### 证明

直接代入风险定义。两个模型的平均风险相同，而来源逐点风险集合分别为 $\{0,0.2\}$ 与 $\{0.1,0.1\}$，故最坏风险不同。证毕。

**AHH 前件。** “平均上安全”不是“每个来源安全”的弱措辞，而是不同量词的命题；边界必须记录采用了哪一种量词以及来源先验是否属于合同。

## 212. 首次失败分区下的条件风险组合

把风险按首次失败发生的历史分区，可以得到比单纯并集界更精确的组合证书。

**定义 212.1（首次失败节点）。** 在有限深度事件树中，令 $\mathcal B=\{b_1,\ldots,b_m\}$ 为互不相交的首次失败节点。对来源 $\omega$，记

$$
q_i(\omega)
=
P_\omega^\pi(\text{在 }b_i\text{ 失败}\mid b_i),
\qquad
\beta_i(\omega)=P_\omega^\pi(b_i).
$$

假定所有失败路径恰好先经过某个 $b_i$，并令剩余项 $q_\infty(\omega)$ 表示在时限内未进入任何已列节点而失败的概率。

**定理 212.2（到达权重乘条件风险）。** 对每个来源 $\omega$，

$$
\boxed{
R_\omega^\pi
=
\sum_{i=1}^m\beta_i(\omega)q_i(\omega)
+
q_\infty(\omega).
}
\tag{212.1}
$$

若边界只保存上界

$$
\beta_i(\omega)\le\overline\beta_i,
\qquad
q_i(\omega)\le\overline\alpha_i,
\qquad
q_\infty(\omega)\le\overline\alpha_\infty,
$$

则有鲁棒证书

$$
\boxed{
R_{\mathrm{worst}}(\pi)
\le
\sum_{i=1}^m\overline\beta_i\,\overline\alpha_i
+
\overline\alpha_\infty.
}
\tag{212.2}
$$

若每个首次失败节点都被完全列出，使 $q_\infty=0$，则（212.1）为精确分解；若只知道 $\overline\beta_i\le1$，（212.2）退化为条件风险上界的和。

### 证明

首次失败节点互不相交，且与剩余失败事件构成失败事件的分割。全概率公式给出（212.1）。逐项使用非负量的上界，得到（212.2）。证毕。

**推论 212.3（风险预算的历史分配）。** 若给定总风险预算 $\alpha$，只要选择

$$
\sum_i\overline\beta_i\,\overline\alpha_i
+
\overline\alpha_\infty
\le\alpha,
$$

便得到所有来源同时成立的最坏风险证书。若 $\overline\beta_i$ 很小，则该历史允许的条件风险可以较大；若历史必达，条件风险几乎就是总风险预算。

这不是把稀有历史的失败删掉，而是把它的到达概率显式计入预算。忘掉 $\overline\beta_i$ 会产生过紧的合同，忘掉 $\overline\alpha_i$ 则会产生不安全的合同。

**命题 212.4（同一总风险的不同历史结构）。** 两个来源模型都满足总风险 $0.1$。模型 A 在必达历史上具有条件风险 $0.1$；模型 B 在到达概率 $0.01$ 的历史上具有条件风险 $1$，其余路径无风险。若未来任务要求每个已达历史的条件风险不超过 $0.2$，模型 A 合法而模型 B 不合法，尽管总风险相同。

### 证明

模型 A 的总风险为 $1\cdot0.1=0.1$，且条件风险为 $0.1$。模型 B 的总风险为 $0.01\cdot1=0.01$，若要达到题设的 $0.1$，可再加入一个独立风险 $0.09$ 的安全失败项；总风险仍为 $0.1$，但稀有历史条件风险为一，违反 $0.2$ 的局部合同。证毕。

## 213. 机会约束与最坏约束的边界反例

平均风险证书可以适合一个明确的先验任务，却不能替代逐历史的安全约束；反过来，逐历史证书也可能比总风险任务付出更多预算。

**定义 213.1（先验机会约束）。** 给定先验 $\mu$ 和阈值 $\alpha$，机会约束为

$$
R_{\mathrm{avg}}(\pi,\mu)\le\alpha.
$$

给定来源集合而无先验的最坏约束为

$$
R_{\mathrm{worst}}(\pi)\le\alpha.
$$

给定历史预算向量 $\boldsymbol\alpha=(\alpha_h)$ 的局部约束为

$$
R_{\mathrm{cond}}(h,\pi)\le\alpha_h
\quad\text{对所有可达 }h.
$$

**定理 213.2（约束强度的严格关系）。** 在相同阈值 $\alpha$ 下，最坏约束蕴含机会约束；若把每个历史预算取为 $\alpha_h=\alpha$，局部约束通过定理 211.2 蕴含最坏约束。两个反向蕴含都不成立。

### 证明

前两条分别由定理 211.2 的积分界和历史分割界得到。

机会约束不蕴含最坏约束：取一个先验质量为 $\varepsilon<\alpha$ 的来源，其风险为一，其余来源风险为零，则平均风险为 $\varepsilon$ 而最坏风险为一。

最坏约束不蕴含局部约束：取一个到达概率正好为 $\alpha$ 的历史，其条件风险为一，其余历史无风险，则总风险为 $\alpha$，但该历史的条件风险大于 $\alpha$。证毕。

**命题 213.3（相同平均成功率、不同可行策略集）。** 设一个策略族中只有两个策略 $\pi_A,\pi_B$。在均匀先验下：

$$
(R_{\omega_0}^{\pi_A},R_{\omega_1}^{\pi_A})=(0,0.2),
$$

$$
(R_{\omega_0}^{\pi_B},R_{\omega_1}^{\pi_B})=(0.1,0.1).
$$

两者平均风险均为 $0.1$。若任务合同是平均风险 $\le0.1$，两者均可行；若合同是最坏风险 $\le0.1$，只有 $\pi_B$ 可行；若再要求每个历史条件风险 $\le0.1$，仍需检查历史分解，平均数据本身不能决定可行性。

### 证明

前两项由风险对来源取平均和最大得到。最后一句是因为总风险只给出历史加权和，不能反推出各条件项；命题 212.4 给出相同总风险而局部合同不同的构造。证毕。

这说明“成功率”不是一个无上下文的数字。必须同时说明来源量词、历史条件化方式、先验、时限和风险预算，才能把它作为全息边界上的可组合读数。

## 214. AHH：风险感知的全息证书

**定义 214.1（风险感知边界）。** 对过滤化来源合同和策略 $\pi$，定义

$$
\boxed{
\eta_{\mathrm{risk}}
=
\left(
\{\mathfrak J_h\}_{h},
\{\overline\beta_b\}_{b\in\mathcal B},
\{\overline\alpha_b\}_{b\in\mathcal B},
\overline\alpha_\infty,
\text{来源量词与先验},
\text{策略许可、时限与成本}
\right).
}
\tag{214.1}
$$

其中 $\mathcal B$ 是声明的首次失败节点集合。该边界同时保存到达权重、条件风险、未覆盖尾项和风险量词；删去任一项都可能改变（212.2）的证书。

**定理 214.2（风险证书的边界充分性）。** 若两个关系体具有相同的风险感知边界，并且允许策略、首次失败分区和预算合同对应，则：

1. 每个对应策略具有相同的风险上界证书；
2. 在相同来源量词下，它们的最坏风险可行性结论相同；
3. 在相同先验下，它们的机会约束结论相同。

### 证明

由相同的历史来源纤维、到达上界、条件风险上界和尾项，式（212.2）的右端逐项相同，因此每个策略的证书相同。策略许可与预算对应保证同一个策略集合和同一个阈值问题，故可行性结论相同。若采用机会约束，来源先验和对应的风险分布也相同，积分后的结论相同。证毕。

**定理 214.3（删除量词或联合风险会破坏普适充分性）。** 若边界只保存平均风险而不保存来源量词，命题 211.3 的两个模型在边界上相同却具有不同最坏风险。若只保存每个历史的条件风险边缘而不保存到达权重与首次失败的联合配对，则命题 212.4 的两个模型可以具有相同总风险边缘却具有不同局部安全可行性。

### 证明

第一句直接由命题 211.3。第二句由命题 212.4：相同总风险的边缘读数不确定风险发生在哪个历史及其到达概率，因而不能决定逐历史合同。证毕。

**AHH 214.4（风险感知全息）。** 对动态波粒关系，局域事件之后的边界不能只写“成功概率为多少”。它必须写清：

$$
\boxed{
\text{对谁取量词}
+
\text{在哪个历史条件下}
+
\text{风险如何按到达概率组合}
+
\text{未覆盖尾项与记录成本}.
}
$$

AHH 的关键是：**平均、最坏和条件风险不是同一个读数的三种精度；它们是三种不同的边界任务。只有把概率—历史—失败的联合结构保存下来，安全证书才可以沿观察者的合法后继递归。**

**来源与边界 214.5。** 本批在有限过滤、有限首次失败分区、非预见策略和明确来源量词下，区分最坏、条件与先验平均风险，证明到达权重乘条件风险的组合证书，给出机会约束与最坏约束的严格反例，并构造风险感知全息边界。没有把平均成功率冒称逐来源安全，没有把局部风险预算推广到无限时间、连续事件或独立失败，没有把概率证书解释为现实实验的零成本保证；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 215. 有限样本只给风险区间

第 212 节的风险证书假定到达权重和条件风险已经被知道。实际记录通常只给有限样本，因此边界还必须保存估计误差。这里把统计置信度作为独立于未来物理风险的第二层概率。

**定义 215.1（首次失败参数与经验读数）。** 固定首次失败节点 $b_1,\ldots,b_m$。对每个节点定义真实参数

$$
\beta_i=P^\pi(b_i),
\qquad
\alpha_i=P^\pi(\text{在 }b_i\text{ 失败}\mid b_i),
$$

并令 $\alpha_\infty$ 是未覆盖尾项的失败概率。这里把 $\beta_i,\alpha_i,\alpha_\infty$ 视为来源合同中声明的统一参数；若它们随来源变化，则还需对来源族声明额外的联合估计合同。对每个参数 $\theta_j$（其中 $\theta_j$ 遍历所有 $\beta_i,\alpha_i$ 和 $\alpha_\infty$）使用 $n_j$ 个独立的 $[0,1]$ 有界样本，经验均值记为 $\widehat\theta_j$。若共有 $K$ 个参数，给定 $0<\delta<1$，定义

$$
r_j(\delta)
=
\sqrt{\frac{\log(2K/\delta)}{2n_j}},
$$

以及截断区间

$$
I_j=
\left[
\max\{0,\widehat\theta_j-r_j\},
\min\{1,\widehat\theta_j+r_j\}
\right].
$$

这里的独立样本合同只描述统计读数的取得方式，不声称实际装置可以无成本重复准备。

**定理 215.2（同时置信盒）。** 在定义 215.1 的独立有界样本合同下，

$$
\boxed{
\Pr_{\mathrm{data}}
\left\{
\theta_j\in I_j\text{ 对所有 }j
\right\}
\ge1-\delta.
}
\tag{215.1}
$$

### 证明

对每个 $j$，Hoeffding 不等式给出

$$
\Pr_{\mathrm{data}}
\left\{
|\widehat\theta_j-\theta_j|>r_j
\right\}
\le
2e^{-2n_jr_j^2}
=
\frac{\delta}{K}.
$$

对 $K$ 个坐标使用并集界，所有坐标同时落入未截断区间的概率至少为 $1-\delta$。截断到 $[0,1]$ 不会排除真实参数，故得到（215.1）。证毕。

**定理 215.3（首次失败风险的上置信证书）。** 定义

$$
\overline\beta_i=\sup I_{\beta_i},
\qquad
\overline\alpha_i=\sup I_{\alpha_i},
\qquad
\overline\alpha_\infty=\sup I_{\alpha_\infty}.
$$

则以数据概率至少 $1-\delta$，

$$
\boxed{
R^\pi_{\mathrm{worst}}
\le
\sum_{i=1}^{m}
\overline\beta_i\,\overline\alpha_i
+
\overline\alpha_\infty.
}
\tag{215.2}
$$

### 证明

在定理 215.2 的同时置信事件上，每个真实参数不超过相应上端点。代入定理 212.2 的逐来源风险证书，并使用各项非负，得到（215.2）。证毕。

式（215.2）有两层概率：外层的 $1-\delta$ 是“数据足以支持证书”的置信度，内层的 $R^\pi_{\mathrm{worst}}$ 是未来来源和事件树的物理风险。二者不能写成一个未标注的成功率。

## 216. 区间组合与双重概率的正确次序

经验读数进入风险公式时不能先把区间中心相乘，再把误差留到最后；正确顺序是先形成参数盒，再在盒上取风险泛函的上界。

**定理 216.1（单调风险泛函的最小坐标上界）。** 令

$$
\mathcal B=
\prod_{i=1}^{m}
[\underline\beta_i,\overline\beta_i]
\times
[\underline\alpha_i,\overline\alpha_i]
\times
[\underline\alpha_\infty,\overline\alpha_\infty].
$$

对

$$
F(\beta,\alpha,\alpha_\infty)
=
\sum_i\beta_i\alpha_i+\alpha_\infty
$$

有

$$
\boxed{
\sup_{\mathcal B}F
=
\sum_i\overline\beta_i\,\overline\alpha_i
+
\overline\alpha_\infty.
}
\tag{216.1}
$$

任何只使用坐标区间而声称对整个盒子 sound 的风险上界都不小于右端。

### 证明

在 $[0,1]$ 上，$F$ 对每个坐标单调不减，因此最大值在所有上端点同时取得。若另一个上界小于该端点值，就在盒子中的上端点处失效。证毕。

**推论 216.2（中心乘积不是置信证书）。** 若某个 $\beta_i$ 或 $\alpha_i$ 的区间具有正宽度，则一般有

$$
\widehat\beta_i\widehat\alpha_i
<
\overline\beta_i\,\overline\alpha_i.
$$

因此把经验中心直接代入（212.2）只能给点估计，不能给同时置信的上界。

**定理 216.3（物理风险与数据置信度的双层结论）。** 对任意数据集，令

$$
\widehat R^+_\delta
=
\sum_i\overline\beta_i\,\overline\alpha_i
+\overline\alpha_\infty
$$

则

$$
\boxed{
\Pr_{\mathrm{data}}
\left\{
R^\pi_{\mathrm{worst}}\le\widehat R^+_\delta
\right\}
\ge1-\delta.
}
\tag{216.2}
$$

这不等于对未来事件说“以概率 $1-\delta$ 安全”；未来风险的量词仍由 $R^\pi_{\mathrm{worst}}$ 的定义给出。

若实际数据给出 $\widehat R^+_\delta\le\alpha$，则同一置信事件进一步给出 $R^\pi_{\mathrm{worst}}\le\alpha$。

### 证明

定理 215.3 表明，同时置信事件发生时 $R^\pi_{\mathrm{worst}}\le\widehat R^+_\delta$，其数据概率至少为 $1-\delta$。若观测到的上界不超过 $\alpha$，则在该事件上也有 $R^\pi_{\mathrm{worst}}\le\alpha$。最后一句只是区分数据随机性与未来物理随机性。证毕。

## 217. 相同经验中心不代表相同的全息证书

如果边界只保留经验中心，不保留样本量与置信预算，那么两个统计实验会拥有相同的表面读数，却支持完全不同的风险上界。

**命题 217.1（样本量改变上置信边界）。** 取一个首次失败节点，经验中心为

$$
\widehat\beta=0.1,
\qquad
\widehat\alpha=0.2,
$$

并令 $K=3,\delta=0.05$。若两个坐标都使用 $n=10$ 个样本，则

$$
r(0.05)
=
\sqrt{\frac{\log(120)}{20}}
\approx0.489,
$$

上置信风险乘积约为

$$
(0.1+0.489)(0.2+0.489)\approx0.406.
$$

若使用 $n=10000$ 个样本，则

$$
r(0.05)
=
\sqrt{\frac{\log(120)}{20000}}
\approx0.0155,
$$

上置信风险乘积约为

$$
(0.1+0.0155)(0.2+0.0155)\approx0.0249.
$$

两次的经验中心相同，但可审计的风险证书相差一个数量级。

### 证明

直接代入定义 215.1 的半径公式和定理 216.1 的上端点乘积。证毕。

**命题 217.2（置信预算本身也是边界字段）。** 固定经验中心和样本量，改变 $\delta$ 会改变 $r_j(\delta)$，从而改变上置信风险。若一个边界不保存 $\delta$ 或各坐标的置信分配，就不能恢复其声明的同时置信保证。

### 证明

$r_j(\delta)$ 对 $\delta$ 严格递减。取两个不同的置信预算即可得到不同区间上端点和不同风险证书。证毕。

样本量和置信预算描述的是认识论不确定性；$\beta_i,\alpha_i$ 描述的是关系过程在未来运行中的物理风险。前者变小不会自动使后者变小，只会使我们对后者的证书更紧。

## 218. AHH：统计—物理双层全息

**定义 218.1（统计风险边界）。** 对一个过滤化风险合同，定义

$$
\boxed{
\eta_{\mathrm{stat}}
=
\left(
\widehat\theta_j,n_j,\delta_j,
I_j,
\text{抽样与独立性合同},
\text{来源风险量词},
\text{物理风险阈值}
\right)_{j=1}^{K}.
}
\tag{218.1}
$$

其中 $\sum_j\delta_j\le\delta$，$I_j$ 是由经验读数和置信半径产生的参数区间。若不同坐标共享样本或具有相关性，独立 Hoeffding 盒不能直接使用，必须换成声明过的联合置信集合。

**定理 218.2（统计边界对风险证书的充分性）。** 若两个实验记录具有相同的统计风险边界 $\eta_{\mathrm{stat}}$，且其首次失败分区、策略和风险函数对应，则它们给出的同时置信风险上界、数据置信度和物理阈值可行性结论相同。

### 证明

相同 $\widehat\theta_j,n_j,\delta_j$ 给出相同区间 $I_j$，定理 216.1 给出相同的盒上风险上界。相同抽样合同保证定理 215.2 的置信度适用，相同来源量词和阈值则给出相同可行性判断。证毕。

**定理 218.3（删除统计字段破坏统一紧证书）。** 若边界只保留经验中心而删除样本量或置信预算，则不存在一个只由中心决定、同时对所有允许数据实验保持同样紧的非平凡同时置信风险上界。命题 217.1 和命题 217.2 给出同中心而不同上界的成对实例。

### 证明

若上界只由经验中心决定，则命题 217.1 的两个实验必须得到同一上界；但其置信半径分别约为 $0.489$ 和 $0.0155$，同时 sound 的上界必须容纳前者的更大区间，因此不能对后者给出同样紧的证书。改变 $\delta$ 的同样论证适用于置信预算。证毕。

**AHH 218.4（统计—物理双层全息）。** 事件之后的全息边界不能只保存一个“成功率估计”。它必须同时保存：

$$
\boxed{
\text{经验读数}
+
\text{样本与置信预算}
+
\text{参数的联合区间}
+
\text{来源风险量词与物理阈值}.
}
$$

AHH 的核心是：**物理风险是未来关系的属性，统计置信是我们对该属性的证据强度；把二者压成一个数字，会同时丢掉可组合的风险量词和可审计的证据边界。**

**来源与边界 218.5。** 本批在有限首次失败分区、独立有界样本、有限参数盒和明确来源风险量词下，推导同时置信区间、区间风险上界、数据置信度与物理风险的双层结论，并给出删除样本量或置信预算的反例。没有把独立样本合同推广到相关数据，没有把置信保证解释为未来事件概率，没有推广到无限时间、连续参数或未知统计模型；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 219. 固定样本置信界不能自动穿过停止时间

第 215—218 节给出了固定样本量的统计证书。若观察者根据已读结果决定何时停止采样，停止标签本身也是记录的一部分；固定某个 $n$ 的置信界不能未经修改地对所有可能的停止时刻同时成立。

**定义 219.1（顺序经验均值与时间一致半径）。** 令 $X_1,X_2,\ldots$ 为独立的 $[0,1]$ 有界样本，均值为 $\theta$。定义

$$
\widehat\theta_n=\frac1n\sum_{k=1}^nX_k.
$$

对 $0<\delta<1$，令

$$
\delta_n=\frac{6\delta}{\pi^2n^2},
\qquad
r_n(\delta)
=
\sqrt{\frac{\log\!\left(\pi^2n^2/(3\delta)\right)}{2n}}.
$$

这里使用 $\sum_{n\ge1}n^{-2}=\pi^2/6$，将总置信预算分配到所有可能的样本量。

**定理 219.2（时间一致 Hoeffding 盒）。** 有

$$
\boxed{
\Pr_{\mathrm{data}}
\left\{
|\widehat\theta_n-\theta|
\le r_n(\delta)
\text{ 对所有 }n\ge1
\right\}
\ge1-\delta.
}
\tag{219.1}
$$

### 证明

对每个固定 $n$，Hoeffding 不等式给出

$$
\Pr_{\mathrm{data}}
\left\{
|\widehat\theta_n-\theta|>r_n
\right\}
\le
2e^{-2nr_n^2}
=
\delta_n.
$$

对所有 $n$ 使用可数并集界，并利用

$$
\sum_{n\ge1}\delta_n
=
\frac{6\delta}{\pi^2}
\sum_{n\ge1}\frac1{n^2}
=\delta,
$$

即得（219.1）。证毕。

**推论 219.3（停止时刻安全代入）。** 令 $\tau$ 是由样本过滤生成的任意停止时刻，允许 $\tau=\infty$；在 $\tau<\infty$ 时有

$$
\boxed{
\Pr_{\mathrm{data}}
\left\{
|\widehat\theta_\tau-\theta|
\le r_\tau(\delta)
\right\}
\ge1-\delta.
}
\tag{219.2}
$$

### 证明

时间一致事件在每一个确定 $n$ 上都成立，因此在其上也成立于随机取出的 $\tau$。不需要把 $\tau$ 当作独立于样本的常数。证毕。

## 220. 停止规则可以成为风险证书的一部分

停止不是统计过程之外的管理动作。它决定使用哪一行置信区间，也决定观察者何时允许把一个风险上界写入后续边界。

**定义 220.1（顺序风险上界）。** 对每个 $n$，由时间一致区间构造参数盒 $\mathcal B_n$，并令

$$
\widehat R_n^+
=
\sup_{\vartheta\in\mathcal B_n}
F(\vartheta),
$$

其中 $F$ 是定理 216.1 的风险泛函。定义停止规则

$$
\tau_\alpha
=
\inf\{n\ge1:\widehat R_n^+\le\alpha\},
$$

若从未达到阈值则置 $\tau_\alpha=\infty$。停止规则必须对当前样本过滤可测。

**定理 220.2（顺序风险证书）。** 在定理 219.2 的时间一致事件上，对所有有限 $n$ 同时有

$$
R_{\mathrm{worst}}^\pi
\le
\widehat R_n^+.
$$

因此在事件 $\{\tau_\alpha<\infty\}$ 上，

$$
\boxed{
R_{\mathrm{worst}}^\pi\le\alpha
}
\tag{220.1}
$$

以数据概率至少 $1-\delta$ 成立。

### 证明

时间一致事件给出每个 $n$ 的真实参数盒包含关系。风险泛函在盒上的上确界因此同时支配真实风险。若 $\tau_\alpha<\infty$，取 $n=\tau_\alpha$ 即有 $\widehat R_{\tau_\alpha}^+\le\alpha$，从而得到（220.1）。证毕。

**命题 220.3（停止改变了经验分布）。** 令 $X_1,X_2$ 为独立 Bernoulli$(1/2)$ 样本，停止时刻为

$$
\tau=
\begin{cases}
1,&X_1=1,\\
2,&X_1=0.
\end{cases}
$$

则停止后的经验均值取值 $1,0,1/2$ 的概率分别为 $1/2,1/4,1/4$；固定使用两个样本的均值取值 $1,0,1/2$ 的概率分别为 $1/4,1/4,1/2$。因此把固定 $n=2$ 的分布或置信界直接套到停止样本，会忽略停止记录造成的选择偏差。

### 证明

逐一枚举 $(X_1,X_2)$：若 $X_1=1$，在第一步停止且均值为一；若 $X_1=0$，第二个样本决定均值为零或 $1/2$。固定两样本均值的三种概率由二项式分布直接得到。证毕。

固定样本界并非错误；它回答的是预先声明的一个 $n$。顺序证书回答的是观察者允许在多个 $n$ 中选择一个的任务，后者保存了更多停止关系，也必须付出时间一致置信预算。

## 221. 自适应分支采样的联合置信预算

风险树中不同节点的样本数往往由前面读到的记录决定。只要每个节点的下一次样本在抽取前仍遵守独立性合同，就可以把时间一致界沿节点和样本量同时拼接。

**定义 221.1（节点化顺序采样）。** 令 $J$ 为有限参数坐标集合，例如首次失败节点的 $\beta_i,\alpha_i$ 和尾项。对每个 $j\in J$，潜在样本序列 $X_{j,1},X_{j,2},\ldots$ 独立且均值为 $\theta_j$。采样策略可根据已经取得的全部记录选择下一个坐标，但在取得 $X_{j,n}$ 前不能读取该样本的值。令 $N_j$ 为最终取得的样本数，允许 $N_j$ 是全局记录过滤下的停止时刻。

取

$$
\delta_{j,n}
=
\frac{6\delta}{\pi^2|J|n^2},
\qquad
r_{j,n}
=
\sqrt{
\frac{\log\!\left(\pi^2|J|n^2/(3\delta)\right)}{2n}
}.
$$

**定理 221.2（节点—时间一致联合盒）。** 在定义 221.1 的抽样合同下，以数据概率至少 $1-\delta$，对所有 $j\in J$ 和所有 $n\ge1$ 同时有

$$
\boxed{
|\widehat\theta_{j,n}-\theta_j|
\le r_{j,n}.
}
\tag{221.1}
$$

特别地，在任意自适应终止样本 $(N_j)_{j\in J}$ 上，可以同时使用对应的区间构造风险上界。

### 证明

固定 $j$ 后，定理 219.2 以预算 $\delta/|J|$ 给出对所有 $n$ 的时间一致事件。对有限 $J$ 再取并集，失败概率至多

$$
\sum_{j\in J}\frac{\delta}{|J|}=\delta.
$$

该事件对所有可能的自适应采样路径同时成立，所以在随机样本数 $N_j$ 处仍成立。证毕。

**推论 221.3（自适应风险证书）。** 令 $\mathcal B_{(N_j)}$ 是把定理 221.2 的区间代入参数盒，令

$$
\widehat R^+_{(N_j)}
=
\sup_{\vartheta\in\mathcal B_{(N_j)}}F(\vartheta).
$$

则

$$
\boxed{
\Pr_{\mathrm{data}}
\left\{
R_{\mathrm{worst}}^\pi
\le
\widehat R^+_{(N_j)}
\text{ 对最终自适应样本同时成立}
\right\}
\ge1-\delta.
}
\tag{221.2}
$$

若策略在风险证书首次低于 $\alpha$ 时停止所有节点，则在同一置信事件上所提交的证书满足 $R_{\mathrm{worst}}^\pi\le\alpha$。

### 证明

把定理 221.2 的联合区间代入单调风险泛函的盒上界，应用定理 216.1。停止规则只是在一个已经同时有效的随机场上选择索引，不改变其覆盖事件。证毕。

## 222. AHH：任何时刻的统计全息

**定义 222.1（anytime 风险边界）。** 对节点集合 $J$，定义

$$
\boxed{
\eta_{\mathrm{any}}
=
\left(
\{\widehat\theta_{j,n},r_{j,n}\}_{j,n},
\text{节点采样过滤},
\text{停止规则},
\text{置信预算分配},
\text{风险量词与物理阈值}
\right).
}
\tag{222.1}
$$

边界保存的是整个可停止的置信序列，而不是停止瞬间的一行经验中心。

**定理 222.2（anytime 边界对自适应证书的充分性）。** 若两个实验关系体具有同样的 anytime 风险边界、采样过滤、停止规则、风险泛函和来源量词，则任意允许的自适应采样策略产生相同的置信风险证书与阈值可行性结论。

### 证明

相同的序列区间和置信预算给出定理 221.2 的同一同时覆盖事件；相同停止规则在对应记录上选出相同索引；定理 216.1 对同一风险泛函给出相同上界。来源量词和阈值对应后，可行性结论相同。证毕。

**定理 222.3（删除停止信息破坏统一充分性）。** 若边界只保留停止时的经验中心和样本量，而不保留停止规则或时间一致置信预算，则不存在一个对所有自适应停止策略同时有效且保持同样紧的风险证书。命题 220.3 给出停止改变经验分布的基本反例，定理 219.2 的半径则显示缺失时间预算会漏掉跨时刻的并集项。

### 证明

两个策略可以在同一个停止样本中心和样本量处停止，但一个停止规则只在偏高波动时停止，另一个规则预先固定样本量。它们对数据的选择事件不同，固定时刻的覆盖不能区分二者。若要求同时覆盖所有时刻，必须至少支付定理 219.2 的 $\sum_n\delta_n$ 预算；删除该字段就无法确定应支付的并集项。证毕。

**AHH 222.4（anytime 统计全息）。** 观察者可以在任意已读历史停止，并把风险证书写入下一份关系边界；因此全息接口必须保存：

$$
\boxed{
\text{时间一致区间}
+
\text{自适应采样过滤}
+
\text{停止规则}
+
\text{风险量词与物理阈值}.
}
$$

AHH 的核心是：**停止时刻不是统计过程外的时间标签，而是选择关系的一部分；只有把“在所有可能停止时刻都有效”的置信结构保存下来，事件记录才可以安全地成为下一次合法续接的证书。**

**来源与边界 222.5。** 本批在独立有界顺序样本、可测停止时刻、有限参数坐标和明确风险泛函下，推导时间一致 Hoeffding 盒、停止时风险证书、节点—时间联合置信预算和 anytime 全息边界。没有把固定样本界冒称可选停止界，没有推广到相关样本、无限参数族、连续时间鞅或现实装置零成本采样；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 223. 抽样误差与模型失配误差必须分开

第 215—222 节的置信盒假定样本均值围绕声明参数集中。若仪器、来源或记录接口只是名义模型，真实参数还会与名义参数存在结构偏差；增加样本数只能缩小抽样半径，不能自动消除这项偏差。

**定义 223.1（近似模型合同）。** 对每个待估参数 $j$，令 $\bar\theta_j$ 为名义模型下的参数，令真实关系参数为 $\theta_j$。声明模型失配半径

$$
|\theta_j-\bar\theta_j|\le\kappa_j,
\qquad
\kappa_j\ge0.
$$

从名义模型产生的有界样本给出经验均值 $\widehat\theta_j$。若用顺序或固定样本方法得到抽样半径 $r_j$，则抽样合同只约束

$$
|\widehat\theta_j-\bar\theta_j|\le r_j
$$

的置信事件。

**定理 223.2（失配半径的三角扩张）。** 在上述合同下，以抽样数据概率至少 $1-\delta$，

$$
\boxed{
|\widehat\theta_j-\theta_j|
\le
r_j+\kappa_j
\quad\text{对所有 }j.
}
\tag{223.1}
$$

因此真实参数的可审计区间是

$$
I_j^{\mathrm{true}}
=
\left[
\max\{0,\widehat\theta_j-r_j-\kappa_j\},
\min\{1,\widehat\theta_j+r_j+\kappa_j\}
\right].
$$

### 证明

在抽样置信事件上，三角不等式给出

$$
|\widehat\theta_j-\theta_j|
\le
|\widehat\theta_j-\bar\theta_j|
+
|\bar\theta_j-\theta_j|
\le r_j+\kappa_j.
$$

对所有坐标同时成立的概率沿用原抽样合同，截断到 $[0,1]$ 不排除真实参数。证毕。

**推论 223.3（样本加倍不能支付模型失配）。** 当 $n_j\to\infty$ 使 $r_j\to0$ 时，区间半径仍至少为 $\kappa_j$。若边界只保留 $r_j$ 而删除 $\kappa_j$，它报告的是名义模型内的精度，不是对真实关系参数的覆盖。

抽样不确定性和模型失配都表现为区间宽度，却具有不同的可修复方式：前者可通过更多符合合同的样本缩小，后者需要校准、扩大模型类或改变任务边界。

## 224. 模型失配进入风险组合的可审计界

**定义 224.1（含失配的风险盒）。** 对首次失败参数使用定理 223.2 的上端点，记

$$
u_{\beta_i}
=
\min\{1,\widehat\beta_i+r_{\beta_i}+\kappa_{\beta_i}\},
$$

$$
u_{\alpha_i}
=
\min\{1,\widehat\alpha_i+r_{\alpha_i}+\kappa_{\alpha_i}\},
\qquad
u_{\alpha_\infty}
=
\min\{1,\widehat\alpha_\infty+r_{\alpha_\infty}+\kappa_{\alpha_\infty}\}.
$$

定义含失配上界

$$
\widehat R^+_{\delta,\kappa}
=
\sum_i u_{\beta_i}u_{\alpha_i}
+
u_{\alpha_\infty}.
$$

**定理 224.2（抽样—失配—物理风险三层组合）。** 在定理 223.2 的同时置信事件上，

$$
\boxed{
R^\pi_{\mathrm{worst}}
\le
\widehat R^+_{\delta,\kappa}.
}
\tag{224.1}
$$

若观测数据满足 $\widehat R^+_{\delta,\kappa}\le\alpha$，则以数据概率至少 $1-\delta$ 得到物理最坏风险阈值 $R^\pi_{\mathrm{worst}}\le\alpha$ 的有效证书。

### 证明

定理 223.2 给出真实参数属于含失配风险盒。风险泛函

$$
F(\beta,\alpha,\alpha_\infty)
=
\sum_i\beta_i\alpha_i+\alpha_\infty
$$

在 $[0,1]$ 上逐坐标单调不减，所以定理 216.1 的盒上界正是 $\widehat R^+_{\delta,\kappa}$。阈值结论与定理 216.3 相同。证毕。

**定理 224.3（结构偏差的显式增量）。** 假设所有截断均未触及 $1$。令不含失配的统计上界为

$$
\widehat R^+_{\delta,0}
=
\sum_i v_{\beta_i}v_{\alpha_i}+v_{\alpha_\infty},
$$

其中 $v_{\beta_i}=\widehat\beta_i+r_{\beta_i}$、$v_{\alpha_i}=\widehat\alpha_i+r_{\alpha_i}$。则

$$
\boxed{
\widehat R^+_{\delta,\kappa}
-
\widehat R^+_{\delta,0}
=
\sum_i
\left(
v_{\beta_i}\kappa_{\alpha_i}
+
v_{\alpha_i}\kappa_{\beta_i}
+
\kappa_{\beta_i}\kappa_{\alpha_i}
\right)
+
\kappa_{\alpha_\infty}.
}
\tag{224.2}
$$

### 证明

逐项展开

$$
(v_{\beta_i}+\kappa_{\beta_i})
(v_{\alpha_i}+\kappa_{\alpha_i})
-
v_{\beta_i}v_{\alpha_i}
$$

即可得到括号中的三项，再加上尾项增量。证毕。

结构偏差不是抽样半径的另一个名字。式（224.2）显示它会和统计上端点交叉放大；因此“把样本做得更多”与“把模型校准得更真”在风险预算中是不同的投资方向。

## 225. 相同观测读数、不同模型合同的安全结论

若只保存观测中心和样本量，两个名义模型可以拥有相同的统计读数，却对真实风险给出不同的有效证书。

**命题 225.1（失配半径改变证书）。** 取一个首次失败节点，经验中心与抽样半径为

$$
\widehat\beta=0.1,\quad
\widehat\alpha=0.2,\quad
r_\beta=r_\alpha=0.01.
$$

模型 A 声明

$$
\kappa_\beta=\kappa_\alpha=0,
$$

模型 B 声明

$$
\kappa_\beta=\kappa_\alpha=0.1.
$$

则两者的统计中心完全相同，但风险上端点分别为

$$
(0.11)(0.21)=0.0231
$$

与

$$
(0.21)(0.31)=0.0651.
$$

若物理阈值为 $\alpha=0.04$，模型 A 的证书通过，模型 B 的证书不通过。

### 证明

直接代入定义 224.1。两项的差异完全来自模型失配半径，而非经验中心或抽样半径。证毕。

**命题 225.2（名义覆盖不等于真实覆盖）。** 若真实参数与名义参数的差异可以达到 $\kappa_j$，而边界只使用 $r_j$ 构造区间，则存在真实参数落在报告区间之外，即使名义模型下的抽样置信事件完全成立。

### 证明

取某个坐标使 $|\theta_j-\bar\theta_j|=\kappa_j>0$，并在抽样事件上令 $|\widehat\theta_j-\bar\theta_j|=r_j$ 且方向相同。此时

$$
|\widehat\theta_j-\theta_j|=r_j+\kappa_j>r_j,
$$

故真实参数超出只用 $r_j$ 的区间。证毕。

这两个命题区分了两种“同样数据却不同结论”的来源：统计证书差异来自样本记录，模型证书差异来自关系接口的适用范围。后处理观测中心不能补回没有声明的模型失配。

## 226. AHH：来源可追溯的统计—关系全息

**定义 226.1（provenance 全息边界）。** 对每个风险参数定义

$$
\boxed{
\eta_{\mathrm{prov}}
=
\left(
\widehat\theta_j,
n_j\text{ 或时间一致序列},
\delta_j,
r_j,
\kappa_j,
\text{抽样合同},
\text{模型适用域},
\text{来源风险量词与阈值}
\right)_{j}.
}
\tag{226.1}
$$

其中 $r_j$ 表示抽样误差合同，$\kappa_j$ 表示名义模型到真实关系的结构失配合同；二者都必须有来源和适用范围。

**定理 226.2（provenance 边界对真实风险证书的充分性）。** 若两个关系体具有相同的 provenance 边界、风险泛函、首次失败分区和策略许可，则它们的真实参数区间、含失配风险上界和阈值可行性结论相同。

### 证明

相同的统计字段和抽样合同给出相同 $r_j$ 与置信事件；相同模型适用域给出相同 $\kappa_j$；定理 223.2 和 224.2 随后给出相同真实区间和风险上界。其余风险量词、分区和阈值相同，故可行性结论相同。证毕。

**定理 226.3（删除失配字段破坏真实安全性）。** 若边界只保留经验中心、样本量和统计半径而删除 $\kappa_j$，则不存在一个对所有允许模型适用域都 sound 的统一非平凡真实风险证书。命题 225.1—225.2 给出同一统计读数而不同真实结论的成对实例。

### 证明

同一统计字段可以与 $\kappa=0$ 或 $\kappa>0$ 的模型合同配对。命题 225.2 表明只用统计半径的区间在后者上可以漏掉真实参数；因此任何声称对两类适用域都 sound 的证书必须扩大到包含失配半径，不能只由统计字段决定。证毕。

**AHH 226.4（provenance 全息）。** 事件记录之后的边界不只是“我们测得多准”，还要保存“这个测量对哪个关系模型有效，以及模型离真实来源允许多远”。因此完整安全边界必须同时保留：

$$
\boxed{
\text{抽样置信}
+
\text{模型失配}
+
\text{来源量词}
+
\text{风险组合与适用域}.
}
$$

AHH 的核心是：**统计置信解决的是在一个声明模型内读数有多稳定；provenance 解决的是这个模型是否覆盖了要续接的关系。没有第二层，越来越多的样本只能把错误模型估计得越来越精确。**

**来源与边界 226.5。** 本批在有限参数盒、独立有界样本、显式模型失配半径和首次失败风险泛函下，推导抽样—失配三角扩张、含失配风险证书、结构偏差增量及 provenance 全息边界。没有把模型失配自动视为统计噪声，没有把名义模型覆盖宣称为真实关系覆盖，也没有推广到未知失配、相关样本、无限维模型或物理钟标定；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 227. 模型失配必须沿允许动作索引

第 226 节的失配半径 $\kappa_j$ 仍然可能隐藏一个维度：模型在当前动作上很准，不代表它在未来允许的另一个动作上也很准。自适应策略会把模型带到一条由记录选择的动作路径，因此失配合同必须按动作和历史索引。

**定义 227.1（动作索引的响应合同）。** 令 $\mathcal A$ 为有限动作集。对每个 $a\in\mathcal A$，取真实线性响应 $T_a$ 和名义响应 $\bar T_a$，并定义

$$
\kappa_a=\|T_a-\bar T_a\|,
\qquad
g_a\ge\|T_a\|,
\qquad
\bar g_a\ge\|\bar T_a\|.
$$

策略 $\pi$ 在一条完整记录上产生动作词

$$
w=(a_1,\ldots,a_n).
$$

记

$$
T_w=T_{a_n}\cdots T_{a_1},
\qquad
\bar T_w=\bar T_{a_n}\cdots\bar T_{a_1}.
$$

动作支持 $\mathcal A_\Pi$ 是允许策略族在所有声明历史上可能调用的动作集合。

**定理 227.2（策略路径上的失配望远镜界）。** 对每条动作词 $w$，有

$$
\boxed{
\|T_w-\bar T_w\|
\le
\sum_{i=1}^{n}
\left(\prod_{j=i+1}^{n}g_{a_j}\right)
\kappa_{a_i}
\left(\prod_{j=1}^{i-1}\bar g_{a_j}\right).
}
\tag{227.1}
$$

因此，对整个策略族同时适用的界必须取所有允许动作词的上确界。若所有允许动作满足 $\kappa_a\le\kappa$ 且 $g_a,\bar g_a\le G$，则长度 $n$ 的统一界为

$$
\boxed{
\|T_w-\bar T_w\|
\le nG^{n-1}\kappa.
}
\tag{227.2}
$$

### 证明

乘积望远镜恒等式给出

$$
T_{a_n}\cdots T_{a_1}
-
\bar T_{a_n}\cdots\bar T_{a_1}
=
\sum_{i=1}^{n}
T_{a_n}\cdots T_{a_{i+1}}
(T_{a_i}-\bar T_{a_i})
\bar T_{a_{i-1}}\cdots\bar T_{a_1}.
$$

逐项取范数并使用次乘法性，得到（227.1）。在统一界下，每项不超过 $G^{n-1}\kappa$，共有 $n$ 项，得到（227.2）。证毕。

该界沿实际动作词结算，而不是沿一个事后选出的最优词结算。若未来策略能调用多个动作，单个动作上的校准读数不能替代整个动作支持上的失配剖面。

## 228. 条件归一化会再次放大动作失配

**定义 228.1（分支响应距离）。** 令 $K_{a,y}$ 与 $\bar K_{a,y}$ 是真实和名义的完全正迹不增分支。用迹范数定义动作—结果失配

$$
\frac12\|K_{a,y}-\bar K_{a,y}\|_{1\to1}
\le\kappa_{a,y}.
$$

对输入态 $\rho$，写

$$
p=\operatorname{Tr}K_{a,y}(\rho),
\qquad
\bar p=\operatorname{Tr}\bar K_{a,y}(\rho).
$$

**定理 228.2（动作失配的条件后继界）。** 若真实和名义分支概率都满足

$$
p,\bar p\ge p_*>0,
$$

则

$$
\boxed{
D\!\left(
\frac{K_{a,y}(\rho)}p,
\frac{\bar K_{a,y}(\rho)}{\bar p}
\right)
\le
\frac{2\kappa_{a,y}}{p_*}.
}
\tag{228.1}
$$

### 证明

令 $A=K_{a,y}(\rho)$、$\bar A=\bar K_{a,y}(\rho)$，并令

$$
d=\frac12\|A-\bar A\|_1\le\kappa_{a,y}.
$$

迹差满足

$$
|p-\bar p|\le\|A-\bar A\|_1=2d.
$$

分解归一化差：

$$
\frac A p-\frac{\bar A}{\bar p}
=
\frac{A-\bar A}{p}
+
\bar A\left(\frac1p-\frac1{\bar p}\right).
$$

取半迹范数得到

$$
D\!\left(\frac A p,\frac{\bar A}{\bar p}\right)
\le
\frac d p+
\frac{|p-\bar p|}{2p}
\le
\frac{2d}{p_*}
\le
\frac{2\kappa_{a,y}}{p_*}.
$$

证毕。

**推论 228.3（动作族的条件边界）。** 若允许策略族的每个动作—结果对都满足 $\kappa_{a,y}\le\kappa$，且所有可达分支具有统一概率下界 $p_*$，则任何一次条件后继的名义—真实距离不超过 $2\kappa/p_*$。若动作或历史改变概率下界，必须按历史重新记录 $p_{*,a,y,h}$；一个全局平均概率不能替代它们。

这把两种放大区分开：式（227.1）的因果增益放大作用于未归一化响应，式（228.1）的 $1/p_*$ 放大来自事件条件化。它们可以在同一策略路径上连续出现。

## 229. 单动作校准不能保证自适应策略

**命题 229.1（未校准动作的迁移反例）。** 取一维正响应空间 $\mathbb R_{\ge0}$ 和两个动作 $a,b$。定义

$$
T_a=\bar T_a=0.1I,
\qquad
T_b=0.9I,
\qquad
\bar T_b=0.1I.
$$

在动作 $a$ 上名义模型与真实模型完全一致：

$$
\kappa_a=0.
$$

若未来策略允许调用 $b$，则

$$
\kappa_b=0.8,
$$

长度一的策略响应误差为 $0.8$。因此任何只保存动作 $a$ 的校准证书，都不能给调用 $b$ 的策略提供统一真实误差界。

### 证明

直接计算

$$
\|T_a-\bar T_a\|=0,
\qquad
\|T_b-\bar T_b\|=0.8.
$$

策略选择 $b$ 时，式（227.1）只有一个误差项，等于 $0.8$。证毕。

**命题 229.2（同当前边界、不同未来动作）。** 两个关系体在当前动作 $a$ 上具有相同边界读数和相同零失配证书；它们在未校准动作 $b$ 上分别具有 $T_b=\bar T_b$ 与 $T_b\ne\bar T_b$。若允许策略只使用 $a$，两者不可区分；若扩展允许动作至 $b$，两者的真实风险证书不同。

### 证明

在动作支持 $\{a\}$ 上，所有策略词只含 $a$，响应和证书相同。扩展至 $\{a,b\}$ 后，选择 $b$ 的策略读取两模型之间的非零差异，故由命题 229.1 得到不同证书。证毕。

这不是要求预先校准所有想象中的动作；它要求边界明确写出动作支持。改变允许的未来接口，就是改变了模型失配合同的量词。

## 230. AHH：动作可迁移的 provenance 全息

**定义 230.1（可迁移 provenance 边界）。** 对策略族 $\Pi$，定义

$$
\boxed{
\eta_{\mathrm{tr}}
=
\left(
\mathcal A_\Pi,
\{\kappa_a,g_a,\bar g_a\}_{a\in\mathcal A_\Pi},
\{\kappa_{a,y},p_{*,a,y,h}\}_{a,y,h},
\text{历史动作许可},
\text{模型适用域与风险阈值}
\right).
}
\tag{230.1}
$$

$\mathcal A_\Pi$ 是策略族的真实动作支持；动作—结果概率下界和失配半径按历史记录，而不是按一个未标注平均值保存。

**定理 230.2（动作 provenance 对策略迁移的充分性）。** 若两个关系体具有相同的可迁移 provenance 边界、策略动作支持、风险泛函和时限，则每条允许自适应策略词都有相同的未归一化传输误差证书；在相同分支概率下界上，它们也有相同的条件后继误差证书。

### 证明

对每条允许策略词应用定理 227.2，动作索引的失配和增益字段相同，故望远镜上界相同。对每个可达动作—结果—历史应用定理 228.2，$\kappa_{a,y}$ 与 $p_{*,a,y,h}$ 相同，故归一化上界相同。策略支持和风险泛函相同，证书结论相同。证毕。

**定理 230.3（删除动作支持破坏迁移充分性）。** 若边界只保存当前动作的模型失配，而不保存未来动作支持或动作索引的失配剖面，则不存在一个对所有扩展策略族都 sound 的非平凡迁移证书。命题 229.1—229.2 给出同一当前边界、不同未来动作结论的成对模型。

### 证明

同一当前动作证书可以与任意 $\kappa_b$ 配对，而命题 229.1 表明调用 $b$ 的误差可从零变为 $0.8$。因此只由当前字段产生的统一上界不能同时覆盖所有未来动作支持，除非退化为不使用动作信息的粗界。证毕。

**AHH 230.4（动作可迁移 provenance）。** 关系全息的“适用域”不是静态标签，而是一个带动作、历史和分支概率的索引族。完整边界必须保存：

$$
\boxed{
\text{允许哪些未来动作}
+
\text{每个动作的模型失配与增益}
+
\text{条件分支的概率下界}
+
\text{历史上的策略量词}.
}
$$

AHH 的核心是：**模型在当前切面上的精确，不会自动迁移成模型对未来控制的精确；只有沿允许动作路径保存 provenance，名义边界才可能成为下一次事件的真实证书。**

**来源与边界 230.5。** 本批在有限动作族、有限策略词、有限算子范数和正条件分支概率下，推导动作索引的望远镜失配界、条件归一化的 $2\kappa/p_*$ 放大界、单动作校准迁移反例和可迁移 provenance 边界。没有把当前动作校准推广到未声明动作，没有把条件概率下界替换为平均概率，也没有推广到无限策略、未知控制或物理钟标定；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 231. 策略占用把动作失配变成轨迹误差

上一批按动作索引保存了局部失配。对自适应策略，还需要记录每个动作在历史树上实际被访问的权重；否则同一组局部半径会被错误地解释成同一个未来误差。

**定义 231.1（有限策略树）。** 令 $\mathsf H_t$ 是第 $t$ 轮的有限记录历史，$\pi_t(a\mid h)$ 是共同声明的策略，$P_{t,h,a}$ 与 $\bar P_{t,h,a}$ 是真实和名义模型在 $(t,h,a)$ 后产生下一条记录的概率核。令

$$
\kappa_{t,h,a}
=
D_{\mathrm{TV}}(P_{t,h,a},\bar P_{t,h,a}),
\qquad
D_{\mathrm{TV}}(\mu,\nu)=\frac12\|\mu-\nu\|_1.
$$

策略诱导的单步核为

$$
K_t^\pi(h,\cdot)=\sum_a\pi_t(a\mid h)P_{t,h,a}(\cdot),
\qquad
\bar K_t^\pi(h,\cdot)=\sum_a\pi_t(a\mid h)\bar P_{t,h,a}(\cdot).
$$

设 $\mu_t$ 是真实核 $K_0^\pi,\ldots,K_{t-1}^\pi$ 产生的历史分布。这里假定策略本身的历史读取、随机源和动作许可在真实与名义模型中相同；若策略代码也有失配，它必须另列为一个动作—策略误差项。

**定理 231.2（策略轨迹的占用加权失配界）。** 对长度为 $H$ 的策略轨迹分布 $\mathbb P^\pi$ 与 $\bar{\mathbb P}^\pi$，有

$$
\boxed{
D_{\mathrm{TV}}(\mathbb P^\pi,\bar{\mathbb P}^\pi)
\le
\sum_{t=0}^{H-1}
\int_{\mathsf H_t}
\mu_t(dh)
\sum_a\pi_t(a\mid h)\kappa_{t,h,a}.
}
\tag{231.1}
$$

因此，对任意终端记录函数 $F$ 满足 $0\le F\le1$，有

$$
\boxed{
\left|
\mathbb E_{\mathbb P^\pi}F
-
\mathbb E_{\bar{\mathbb P}^\pi}F
\right|
\le
\sum_{t=0}^{H-1}
\mathbb E_{h\sim\mu_t}
\sum_a\pi_t(a\mid h)\kappa_{t,h,a}.
}
\tag{231.2}
$$

### 证明

把真实与名义轨迹核写成乘积，并作望远镜展开：

$$
\begin{aligned}
&\mu_0K_0^\pi\cdots K_{H-1}^\pi
-
\mu_0\bar K_0^\pi\cdots\bar K_{H-1}^\pi\\
&=
\sum_{t=0}^{H-1}
\mu_0K_0^\pi\cdots K_{t-1}^\pi
(K_t^\pi-\bar K_t^\pi)
\bar K_{t+1}^\pi\cdots\bar K_{H-1}^\pi.
\end{aligned}
$$

概率核在迹范数或全变差距离下是收缩的，所以第 $t$ 项的范数不超过

$$
\int\mu_t(dh)
D_{\mathrm{TV}}(K_t^\pi(h,\cdot),\bar K_t^\pi(h,\cdot)).
$$

全变差的凸性给出

$$
D_{\mathrm{TV}}(K_t^\pi(h,\cdot),\bar K_t^\pi(h,\cdot))
\le
\sum_a\pi_t(a\mid h)\kappa_{t,h,a}.
$$

对 $t$ 求和即得（231.1）。对 $[0,1]$ 值函数，积分差的绝对值不超过全变差距离，得到（231.2）。证毕。

式（231.1）中的权重是由真实前缀产生的策略占用，而不是事后挑选的最坏动作。若目标任务要求所有来源、所有历史同时成立，则可以把积分替换为对应的上确界；那是量词变强后的合同，不是同一个统计读数。

**定理 231.3（带后续增益的策略界）。** 假定在第 $t$ 个节点发生的局部记录扰动，经名义后续续接传到终端时至多放大 $g_{t,h,a}\ge0$。则同一望远镜证明给出

$$
\boxed{
\left|
\mathbb E_{\mathbb P^\pi}F
-
\mathbb E_{\bar{\mathbb P}^\pi}F
\right|
\le
\sum_{t=0}^{H-1}
\mathbb E_{h\sim\mu_t}
\sum_a\pi_t(a\mid h)g_{t,h,a}\kappa_{t,h,a}.
}
\tag{231.3}
$$

这里的“至多放大”具体指：对该节点下一历史上的任意零迹有符号扰动 $\xi$，名义策略的后续作用满足

$$
\left|
\xi\!\left(\mathcal R^{\bar\pi}_{t+1:H}F\right)
\right|
\le
g_{t,h,a}\|\xi\|_{\mathrm{TV}},
$$

其中 $\mathcal R^{\bar\pi}_{t+1:H}F$ 是从下一历史到终端的名义续接值函数。因而 $g_{t,h,a}=1$ 覆盖普通概率核的收缩情形，而大于一的值只表示声明了额外的算子增益合同。

### 证明

在（231.1）的第 $t$ 项中，不把后续核的收缩常数粗略置为一，而使用其对终端泛函的局部算子范数上界 $g_{t,h,a}$。每个节点的差分先乘以局部失配，再乘以后续增益；对历史和动作求和得到（231.3）。当所有后续核都是概率收缩时 $g_{t,h,a}=1$，退化为（231.2）。证毕。

**AHH 231.4（策略占用层）。** 动作失配只有沿策略树的占用测度传播，才成为一个实际的轨迹证书。全局最大失配可以给出安全上界，却丢掉了“哪些历史真的被访问、哪些动作只在反事实分支出现”的关系。

## 232. 校准策略与目标策略之间的覆盖税

局部校准通常由一个参考策略取得，而未来任务由另一个策略执行。两者之间的动作支持关系必须进入边界；仅比较两个策略的平均动作频率无法保证目标策略可被评估。

**定义 232.1（参考策略与覆盖系数）。** 令 $q_t(a\mid h)$ 是校准或数据收集策略，$\pi_t(a\mid h)$ 是目标策略。若

$$
\pi_t(a\mid h)>0\Longrightarrow q_t(a\mid h)>0,
$$

定义密度比与历史覆盖系数

$$
r_t(h,a)=\frac{\pi_t(a\mid h)}{q_t(a\mid h)},
\qquad
C_t(h)=\max_{a:q_t(a\mid h)>0}r_t(h,a).
$$

若存在目标策略使用而参考策略从不使用的动作，约定 $C_t(h)=+\infty$。

**定理 232.2（离策略 provenance 传输界）。** 在定义 232.1 的绝对连续条件下，任意非负节点权重 $g_{t,h,a}$ 满足

$$
\sum_a\pi_t(a\mid h)g_{t,h,a}\kappa_{t,h,a}
\le
C_t(h)
\sum_aq_t(a\mid h)g_{t,h,a}\kappa_{t,h,a}.
$$

从而目标策略的终端误差满足

$$
\boxed{
\left|
\mathbb E_{\mathbb P^\pi}F
-
\mathbb E_{\bar{\mathbb P}^\pi}F
\right|
\le
\sum_{t=0}^{H-1}
\mathbb E_{h\sim\mu_t}
\left[
C_t(h)\sum_aq_t(a\mid h)g_{t,h,a}\kappa_{t,h,a}
\right].
}
\tag{232.1}
$$

### 证明

对每个有 $\pi_t(a\mid h)>0$ 的动作，代入 $\pi_t=r_tq_t$，并使用 $r_t\le C_t(h)$：

$$
\sum_a\pi_tg\kappa
=
\sum_aq_t r_tg\kappa
\le
C_t(h)\sum_aq_tg\kappa.
$$

将此不等式代入定理 231.3 即得（232.1）。证毕。

覆盖系数不是单纯的估计方差常数。它记录了目标策略在校准策略看来有多么反事实；当 $C_t$ 很大时，即使参考数据中的加权误差很小，目标策略的真实证书仍可能很松。

**命题 232.3（无支持则不可迁移）。** 取一个单步历史和动作集 $\{a,b\}$。若 $q(b)=0$、$\pi(b)=1$，构造两个真实模型 $P$ 与 $P'$，使它们在动作 $a$ 上完全相同，而在动作 $b$ 上分别确定地产生记录 $0$ 与记录 $1$。则所有由 $q$ 取得的校准记录完全相同，但目标策略的终端记录分布全变。

### 证明

参考策略从不调用 $b$，所以两模型在所有被观测数据上的联合分布相同。目标策略必调用 $b$，因而一个模型的记录概率为 $P(Y=1)=0$，另一个为 $P'(Y=1)=1$。任何只依赖参考记录的后处理都不能区分这两个模型，故不能给目标策略一个非平凡统一证书。证毕。

**命题 232.4（稀有支持造成覆盖放大）。** 若 $q(b)=\varepsilon>0$、$\pi(b)=1$，则 $C=1/\varepsilon$。一个动作 $b$ 上的参考加权失配 $\varepsilon\kappa_b$，传输到目标策略后变为至多 $\kappa_b$；当 $\varepsilon\downarrow0$ 时，覆盖税发散。

### 证明

直接由 $r(b)=1/\varepsilon$ 和定理 232.2 得到。证毕。

**AHH 232.5（支持与密度比）。** 参考策略的校准边界只有在目标动作支持绝对连续时才可迁移；迁移成本由历史—动作密度比而不是由参考策略的平均误差单独决定。缺少一个动作的支持，是不可识别；支持过稀，是可识别但证书被覆盖税放大。

## 233. provenance 校准预算的最优分配

当动作支持已经确定，下一项问题是有限预算应投向哪些动作。只按动作数量平均分配，会忽略策略占用、后续增益和参考覆盖。

**定义 233.1（连续校准成本模型）。** 对有限活动动作集 $\mathcal A_+$，令 $n_a>0$ 是动作 $a$ 的校准资源，$c_a>0$ 是单份资源成本，$\sigma_a>0$ 是该动作的误差尺度。设策略证书中动作 $a$ 的合并权重为 $w_a>0$，其中可以包含占用、后续增益和覆盖系数。采用理想化半径

$$
\kappa_a(n_a)=\frac{\sigma_a}{\sqrt{n_a}}.
$$

给定总预算 $B>0$，考虑

$$
\min_{n_a>0}
\sum_{a\in\mathcal A_+}
\frac{w_a\sigma_a}{\sqrt{n_a}}
\quad\text{subject to}\quad
\sum_{a\in\mathcal A_+}c_an_a=B.
$$

这里的 $n_a$ 是连续松弛；整数样本、置信预算和模型偏差必须在实际证书中另行声明。

**定理 233.2（按关系权重的最优校准分配）。** 置 $b_a=w_a\sigma_a$，并令

$$
S=\sum_{a\in\mathcal A_+}b_a^{2/3}c_a^{1/3}.
$$

则唯一内点最优解为

$$
\boxed{
 n_a^*
 =
 B\frac{(b_a/c_a)^{2/3}}{S}
}
\tag{233.1}
$$

且最小证书值为

$$
\boxed{
\min
\sum_a\frac{b_a}{\sqrt{n_a}}
=
\frac{S^{3/2}}{\sqrt B}.
}
\tag{233.2}
$$

### 证明

目标函数严格凸，约束集在正象限的闭包上给出唯一内点极小值。拉格朗日函数为

$$
L(n,\lambda)=\sum_ab_an_a^{-1/2}
+\lambda\left(\sum_ac_an_a-B\right).
$$

一阶条件为

$$
-rac12b_an_a^{-3/2}+\lambda c_a=0,
$$

所以 $n_a=(b_a/(2\lambda c_a))^{2/3}$。代入预算约束并用 $S$ 的定义，得到（233.1）。再代入目标函数：

$$
\sum_a\frac{b_a}{\sqrt{n_a^*}}
=
\frac{S^{1/2}}{\sqrt B}
\sum_ab_a^{2/3}c_a^{1/3}
=
\frac{S^{3/2}}{\sqrt B},
$$

得到（233.2）。严格凸性给出唯一性。证毕。

**推论 233.3（低占用动作仍可能优先校准）。** 若某动作的占用较小但后续增益或覆盖系数足够大，使 $w_a\sigma_a/c_a$ 大于另一动作，则（233.1）给它更多校准资源。动作频率本身不是充分的预算指标。

### 证明

由（233.1），资源比由 $(b_a/c_a)^{2/3}$ 决定，而 $b_a$ 包含完整关系权重 $w_a$。证毕。

**命题 233.4（去掉成本字段会改变最优边界）。** 取两个动作具有相同 $w_a\sigma_a$，但成本分别为 $c_1=1$ 和 $c_2=8$。最优资源比为

$$
\frac{n_1^*}{n_2^*}=\left(\frac{8}{1}\right)^{2/3}=4.
$$

若边界忘掉成本，只按误差尺度分配，就会错误地给出 $n_1=n_2$，其证书值严格更大。

### 证明

把数值代入（233.1）得到 $n_1^*/n_2^*=4$。目标函数严格凸，非最优分配的值严格大于最优值。证毕。

**AHH 233.5（预算几何）。** provenance 的校准不是把样本平均撒在动作标签上，而是按“策略占用 × 后续增益 × 覆盖税 × 误差尺度”与单位成本的组合分配。预算字段从边界中删去，最优证书本身就会改变。

## 234. AHH：策略路径上的 provenance 是带成本的测度

前面三层可以合并成一个策略可迁移证书。对固定目标策略、参考策略和有限 horizon，定义

$$
\boxed{
\eta_{\mathrm{pol}}
=
\left(
\mathsf{supp}(\pi),
\mathsf{supp}(q),
\{r_t(h,a)\},
\{\mu_t(h)\},
\{g_{t,h,a}\},
\{\kappa_{t,h,a}\},
\{n_a,c_a\},
H,
\text{策略是否依赖记录}
\right).
}
\tag{234.1}
$$

这里 $\mu_t$ 是共同声明的真实占用；若任务要对来源集合或模型集合作统一保证，就把它替换为对应的占用集合或上确界合同。“策略是否依赖记录”决定了动作量词是在一条词上、全部策略树上，还是在一个反事实策略集合上。

**定理 234.1（策略 provenance 边界的充分性）。** 在有限历史、绝对连续支持、给定增益定义和半径合同有效的条件下，若两个关系体具有相同的 $\eta_{\mathrm{pol}}$，则对每个声明的目标策略和每个 $[0,1]$ 值终端任务，它们产生相同的证书上界（231.3）、相同的离策略传输上界（232.1）和相同的连续校准最优值（233.2）。

### 证明

（231.3）只使用策略历史支持、占用、增益和动作失配；（232.1）在这些量之外只使用参考支持与密度比；（233.2）只使用由前三者形成的权重、动作误差尺度、样本数成本和预算。逐项代入相同的边界字段，三个上界与最优值分别相同。证毕。

**定理 234.2（删去任一关键层会失去普适充分性）。** 对以下任一字段族，若从边界中删去它而不以等价信息替代，就存在两个关系体具有相同剩余字段，却对某个允许未来任务给出不同正确证书：

1. 删去参考支持或密度比：由命题 232.3 的无支持模型对给出；
2. 删去策略占用：取两个策略在同一动作支持上分别集中访问高失配动作和低失配动作，局部动作字段相同而（231.2）的轨迹界不同；
3. 删去后续增益：取相同局部 $\kappa$、不同续接放大 $g$，则（231.3）的终端误差不同；
4. 删去成本与预算：由命题 233.4，最优校准分配和最小证书值不同；
5. 删去记录依赖合同：取两个策略在当前边缘动作频率相同、但在不同历史上选择不同动作的模型，反事实动作树和未来响应不同。

### 证明

前四项分别由命题 232.3、定理 231.2、定理 231.3 和命题 233.4 直接给出。第五项中，若只保留当前动作边缘而不保留历史到动作的映射，可构造一个隐藏记录在历史 $h_0,h_1$ 间交换动作的策略；当前边缘频率保持不变，但将模型的高失配分支放到 $h_0$ 或 $h_1$ 后，策略树上的条件响应不同。因此剩余字段不能唯一决定未来证书。证毕。

**AHH 234.3（策略路径 provenance）。** 关系全息在可迁移任务上不是一张静态动作清单，而是策略路径空间上的带成本测度：

$$
\boxed{
\text{支持}
+
\text{密度比}
+
\text{历史占用}
+
\text{后续增益}
+
\text{动作失配}
+
\text{校准成本与预算}
}
$$

共同决定一份边界能否从校准策略迁移到目标策略。**AHH 的转折是：provenance 不是动作标签的附录，而是动作被访问、被放大、被校准和被付费的联合测度；删除任一层，边界就只对一个较窄的任务合同充分。**

**来源与边界 234.4。** 本批在有限历史树、有限动作、共同策略随机源、有限 horizon、概率核全变差距离、绝对连续参考支持、给定后续增益和连续半径模型 $\kappa_a=\sigma_a/\sqrt{n_a}$ 下，推导占用加权策略望远镜界、离策略覆盖税、支持缺失反例、校准预算的唯一内点解和策略路径 provenance AHH。没有把覆盖税解释成物理时间、没有把连续预算解冒称为整数样本定理、没有把参考策略可迁移性推广到无支持动作或策略代码失配；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 235. 联合来源耦合决定策略尾部风险

**勘误 235.0。** §233 的一阶条件应读为

$$
-\frac12 b_a n_a^{-3/2}+\lambda c_a=0.
$$

本勘误只在追加区给出规范写法，不改写既有卷字节；后续预算推导均采用这一式。

§234 的策略边界按动作和历史保存了局部误差，但概率风险还需要说明这些局部误差是否由同一个隐藏来源共同产生。相同的每动作半径可以对应完全不同的策略尾部风险。

**定义 235.1（联合误差耦合）。** 固定一条长度为 $m$ 的动作路径，令 $\epsilon_i$ 是第 $i$ 步相对于名义响应的标量误差，$|\epsilon_i|\le\kappa_i$，令 $g_i\ge0$ 是从该步到目标任务的后续增益。路径误差记为

$$
\Delta=\sum_{i=1}^{m}g_i\epsilon_i.
$$

给定各 $\epsilon_i$ 的边缘分布后，所有具有这些边缘的联合分布组成耦合集合 $\Gamma$。耦合本身是 provenance 的一部分。

**定理 235.2（确定性界与耦合依赖的分离）。** 对任何 $\gamma\in\Gamma$，都有

$$
\boxed{
|\Delta|
\le
\sum_{i=1}^{m}g_i\kappa_i
\quad\gamma\text{-几乎处处}.
}
\tag{235.1}
$$

但是由边缘分布决定的局部半径不能唯一决定尾部风险

$$
R_\gamma(\tau)
=
\gamma\{|\Delta|>\tau\}.
$$

具体地，取 $m=2$、$g_1=g_2=1$，并令两个边缘都以概率 $1/2$ 取 $\pm\kappa$。若 $\gamma_+$ 满足 $\epsilon_2=\epsilon_1$，而 $\gamma_-$ 满足 $\epsilon_2=-\epsilon_1$，则两种耦合具有完全相同的边缘，却有

$$
\boxed{
R_{\gamma_+}(\kappa)=1,
\qquad
R_{\gamma_-}(\kappa)=0.
}
\tag{235.2}
$$

### 证明

由三角不等式，

$$
|\Delta|
=
\left|\sum_i g_i\epsilon_i\right|
\le
\sum_i g_i|\epsilon_i|
\le
\sum_i g_i\kappa_i,
$$

得到（235.1）。

在 $\gamma_+$ 下，$\Delta=2\kappa$ 或 $-2\kappa$，所以 $|\Delta|>\kappa$ 必然发生。在 $\gamma_-$ 下，$\Delta=0$ 恒成立，所以该事件从不发生。边缘分布在两种情况下都各自以一半概率取正负 $\kappa$。证毕。

**推论 235.3（方差需要联合来源）。** 在二阶矩存在时，

$$
\operatorname{Var}_\gamma(\Delta)
=
\sum_i g_i^2\operatorname{Var}_\gamma(\epsilon_i)
+
2\sum_{i<j}g_ig_j
\operatorname{Cov}_\gamma(\epsilon_i,\epsilon_j).
$$

因此，单动作半径或单动作方差只决定第一项；相关协方差属于联合 provenance。上面的 $\gamma_+$ 与 $\gamma_-$ 分别给出方差 $4\kappa^2$ 与 $0$。

### 证明

将 $\Delta=\sum_i g_i\epsilon_i$ 代入方差的双线性展开即可。两种耦合的均值都为零，且在同向耦合下 $\Delta=\pm2\kappa$，反向耦合下 $\Delta=0$。证毕。

若任务只要求几乎处处的最坏界，式（235.1）足够；若任务要求超越概率、方差、风险预算或可选停止后的尾部证书，必须把 $\Gamma$ 或等价的联合相关合同保存下来。

**AHH 235.4（联合耦合层）。** provenance 不能只列出“每个动作各自有多准”。当未来任务对路径误差施加非线性风险函数时，边缘半径相同的模型仍可能给出完全不同的尾部；共同来源的耦合是边界中的独立关系层。

## 236. 动作支持不等于干预可识别

§232 的覆盖条件处理了目标策略是否访问某个动作，但观测到一个动作，并不自动等于知道把该动作外加到同一个来源上会发生什么。这里需要把观察分布和干预分布区分开。

**定义 236.1（干预 provenance 合同）。** 令 $U$ 是未记录来源，$A$ 是动作，$Y$ 是结果。观察合同给出 $P(Y\mid A=a,H=h)$；干预合同给出

$$
I_a(\,\cdot\mid h)=P(Y\in\cdot\mid \operatorname{do}(A=a),H=h).
$$

干预 provenance 包括动作干预支持、来源到干预结果的稳定性假设，以及把观察核连接到 $I_a$ 的识别条件。动作的观察支持不等于干预支持。

**命题 236.2（同观察分布、不同干预未来）。** 存在两个因果模型具有相同的观察联合分布 $P(A,Y)$，且观察数据中两个动作都出现，但它们的干预分布不同。

### 证明

令隐藏变量 $U$ 以概率一半取 $0,1$，并令观察机制 $A=U$。

模型 $\mathsf M_1$ 取结构方程 $Y=A$；模型 $\mathsf M_2$ 取结构方程 $Y=U$。在观察分布中，两模型都只产生

$$
P(A=0,Y=0)=P(A=1,Y=1)=\frac12.
$$

所以两个动作都具有正观察支持，且所有观察读数完全相同。

但在干预 $\operatorname{do}(A=1)$ 下，模型 $\mathsf M_1$ 给出 $Y=1$ 恒定，而模型 $\mathsf M_2$ 给出 $Y=U$，即 $Y=1$ 的概率为 $1/2$。因此观察边界无法决定干预后继。证毕。

**定理 236.3（随机化与一致性给出的干预识别）。** 假定对每个历史 $h$：

1. 一致性：实际结果满足 $Y=Y(A)$；
2. 条件可交换性：$(Y(0),Y(1))\perp A\mid H=h$；
3. $P(A=a\mid H=h)>0$。

则

$$
\boxed{
P(Y\in B\mid\operatorname{do}(A=a),H=h)
=
P(Y\in B\mid A=a,H=h)
}
\tag{236.1}
$$

对每个可测结果集合 $B$ 成立。

### 证明

由潜在结果定义，

$$
P(Y\in B\mid\operatorname{do}(A=a),H=h)
=
P(Y(a)\in B\mid H=h).
$$

条件可交换性把右侧改写为

$$
P(Y(a)\in B\mid A=a,H=h).
$$

一致性再给出

$$
P(Y(a)\in B\mid A=a,H=h)
=
P(Y\in B\mid A=a,H=h).
$$

正支持保证条件分布有定义。证毕。

**AHH 236.4（干预层）。** 支持和密度比只回答“目标动作在参考记录中出现了多少”；它们不回答“记录中的动作是否是外加干预”。可迁移的全息边界还必须保存随机化、可交换性或其他干预识别合同。缺少这一层，即使每个动作都有正支持，也可能完全不知道未来干预后继。

## 237. 来源转移与动作转移的联合覆盖税

动作策略之外，校准来源本身也可能发生变化。把来源覆盖和动作覆盖分别记账，只有在联合密度确实分解时才可安全相乘。

**定义 237.1（联合来源—动作测度）。** 令 $\mu$ 是校准来源上的历史测度，$\nu$ 是目标来源测度；令 $q(a\mid h)$ 与 $\pi(a\mid h)$ 分别是参考和目标动作核。若绝对连续，定义

$$
r_S(h)=\frac{d\nu}{d\mu}(h),
\qquad
r_A(h,a)=\frac{\pi(a\mid h)}{q(a\mid h)}.
$$

联合校准测度与目标测度的密度比为

$$
r_{S,A}(h,a)=r_S(h)r_A(h,a).
$$

**定理 237.2（联合覆盖传输界）。** 对任意非负误差场 $e(h,a)$，若

$$
C_S=\operatorname*{ess\,sup}_{\mu}r_S,
\qquad
C_A=\operatorname*{ess\,sup}_{\mu q}r_A
$$

有限，则

$$
\boxed{
\mathbb E_{\nu\pi}[e]
\le
C_SC_A\,\mathbb E_{\mu q}[e].
}
\tag{237.1}
$$

更精确地，令

$$
C_{S,A}
=
\operatorname*{ess\,sup}_{\mu q}r_{S,A},
$$

则

$$
\boxed{
\mathbb E_{\nu\pi}[e]
\le
C_{S,A}\,\mathbb E_{\mu q}[e],
\qquad
C_{S,A}\le C_SC_A.
}
\tag{237.2}
$$

### 证明

由 Radon–Nikodym 变换，

$$
\mathbb E_{\nu\pi}[e]
=
\int e(h,a)r_S(h)r_A(h,a)\,\mu(dh)q(da\mid h).
$$

逐点使用 $r_S\le C_S$ 与 $r_A\le C_A$ 得到（237.1）。直接使用联合比值的上确界得到（237.2），并且 $r_{S,A}=r_Sr_A$ 给出 $C_{S,A}\le C_SC_A$。证毕。

分开记录两个上确界是安全的，但可能浪费联合相关性；若来源转移恰好把质量移向动作覆盖较好的区域，联合税可以严格小于乘积。反过来，只记录来源边缘和动作边缘而忘掉历史条件动作核，不能重建 $r_{S,A}$。

**命题 237.3（相同边缘、不同联合未来）。** 取校准测度 $\lambda_0$ 在四个单元 $(h,a)\in\{0,1\}^2$ 上均匀。取两个目标测度：$\lambda_+$ 在对角单元 $(0,0),(1,1)$ 上各放一半质量，$\lambda_-$ 在反对角单元 $(0,1),(1,0)$ 上各放一半质量。两者的来源边缘和动作边缘都均匀，但对误差场 $e(h,a)=1_{\{h=a\}}$ 有

$$
\mathbb E_{\lambda_+}[e]=1,
\qquad
\mathbb E_{\lambda_-}[e]=0.
$$

### 证明

直接按四个单元求和。两个目标测度的每个边缘都给 $P(h=0)=P(h=1)=P(a=0)=P(a=1)=1/2$，但它们对历史—动作的联合耦合相反。证毕。

**AHH 237.4（联合覆盖层）。** 来源覆盖税与动作覆盖税只有在联合历史—动作测度上才有真实含义。边缘支持、平均动作频率和单独的来源比值不能替代联合密度；可以具有相同边缘，却对未来策略风险给出完全不同的答案。

## 238. AHH：干预—联合来源是可迁移全息的最小合同

把 §§235–237 合并，得到比策略路径边界更严格的因果 provenance 对象。

**定义 238.1（干预—联合 provenance 边界）。** 对目标策略族 $\Pi$，定义

$$
\boxed{
\eta_{\mathrm{causal}}
=
\left(
\mathsf{supp}_{\operatorname{do}},
\mathsf{Ign},
\Gamma_{\mathrm{joint}},
\{r_{S,A}\},
\{g_{t,h,a}\},
\{\kappa_{t,h,a}\},
\{n_a,c_a\},
H,
\text{干预是否保持来源}
\right).
}
\tag{238.1}
$$

其中 $\mathsf{Ign}$ 表示可交换性或其他识别合同，$\Gamma_{\mathrm{joint}}$ 表示路径误差的联合耦合，$r_{S,A}$ 是来源—动作联合覆盖比。若任务只需确定性最坏界，可以把 $\Gamma_{\mathrm{joint}}$ 压缩为半径盒；若任务涉及尾部、方差或干预迁移，则必须保留更细的联合结构。

**定理 238.2（干预—联合边界的充分性）。** 在有限历史、有限动作、正干预支持、识别合同有效、联合密度有限和后续增益合同有效的条件下，两个关系体若具有相同的 $\eta_{\mathrm{causal}}$，则对每个声明的目标策略和每个允许的干预风险泛函，给出相同的传输上界、联合路径尾部上界和校准预算最优值。

### 证明

策略路径的局部误差由 $\kappa$ 与 $g$ 传播，来源与动作的测度变化由 $r_{S,A}$ 传播，干预结果由 $\mathsf{Ign}$ 和一致性合同从观察核连接，路径风险由 $\Gamma_{\mathrm{joint}}$ 决定，预算最优值由 $n_a,c_a$ 决定。上述字段逐项覆盖这些计算中出现的全部量；相同字段经过同一风险泛函得到相同上界。证毕。

**定理 238.3（删除层的不可充分性）。** 若不以等价信息替代而删去以下任一层，则存在相同剩余边界、不同未来结论的关系体：

1. 删除 $\mathsf{Ign}$：由命题 236.2，观察数据相同而干预结果不同；
2. 删除 $\Gamma_{\mathrm{joint}}$：由定理 235.2，边缘半径相同而尾部风险不同；
3. 删除 $r_{S,A}$：由命题 237.3，来源与动作边缘相同而联合任务值不同；
4. 删除干预支持：目标动作的干预后继可以在校准中从未被外加，导致非识别；
5. 删除“干预是否保持来源”：同一个动作在校准来源与目标来源中可以有不同潜在结果机制。

### 证明

前两项分别由命题 236.2 与定理 235.2 直接给出。第三项由命题 237.3 给出。第四项复制命题 232.3，但把观察支持替换成干预支持；第五项取两个来源具有相同观察边缘、不同 $P(Y(a)\mid H)$ 的模型对。每一项都保留其余字段而改变被删除层，故剩余边界不能普适决定目标结论。证毕。

**AHH 238.4（因果联合 provenance）。** 可迁移全息有三个不可互相替代的层次：

$$
\boxed{
\text{拓扑层：动作与干预支持}
\quad+\quad
\text{语义层：干预识别与来源不变性}
\quad+\quad
\text{概率层：路径误差的联合耦合与联合覆盖}.
}
$$

策略占用和预算决定资源如何穿过这三层；局部动作精度只是在它们都已声明以后才有可迁移意义。**AHH 的核心是：真正的全息边界不是“所有动作都测过”，而是保存了目标干预在联合来源空间中的可识别路径、耦合关系和代价。**

**来源与边界 238.5。** 本批在有限潜在来源、有限动作与历史、有限 horizon、共同策略合同、全变差/概率测度距离、潜在结果一致性、条件可交换性和有限联合密度下，给出联合误差耦合的尾部反例、观察—干预不可识别定理、随机化识别桥、来源—动作联合覆盖税及因果联合 provenance AHH。没有把观察支持冒称为干预支持，没有把边缘误差冒称为联合尾部证书，没有把乘积覆盖税宣称为总是最优，也没有推广到无限潜变量、未知干预机制或物理钟标定；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 239. 干预怎样切开当前边界的不可识别纤维

前一批说明干预合同是必要的；现在把“需要哪一个干预”本身写成一个可计算的分离问题。

**定义 239.1（当前等价纤维与目标泛函）。** 令 $\mathfrak M$ 是声明的关系模型类，$O:\mathfrak M\to\mathcal Y$ 是当前边界给出的观察映射，$\Phi:\mathfrak M\to\mathbb R$ 是未来任务要恢复的目标。定义

$$
M\sim_O M'
\quad\Longleftrightarrow\quad
O(M)=O(M').
$$

允许干预 $a\in\mathcal A$ 的结果核记为 $P_M^a$。给定干预集合 $I\subseteq\mathcal A$，把联合接口写成

$$
O_I(M)
=
\left(
O(M),\{P_M^a\}_{a\in I}
\right),
\qquad
M\sim_I M'
\Longleftrightarrow
O_I(M)=O_I(M').
$$

**定理 239.2（可识别性的纤维判据）。** 目标 $\Phi$ 能由当前接口 $O_I$ 唯一确定，当且仅当

$$
\boxed{
M\sim_I M'
\Longrightarrow
\Phi(M)=\Phi(M').
}
\tag{239.1}
$$

若加入一个干预 $a$，则

$$
\sim_{I\cup\{a\}}\ \subseteq\ \sim_I.
$$

因此干预只能细分不可识别纤维；它是否真正有用，取决于它是否分离某个具有不同 $\Phi$ 值的模型对。

### 证明

若（239.1）成立，在每个等价类上定义 $\widehat\Phi([M])=\Phi(M)$，则该定义良好，并且 $\Phi=\widehat\Phi\circ[\,\cdot\,]_I$，所以接口足以恢复目标。

反之，若存在 $M\sim_I M'$ 且 $\Phi(M)\ne\Phi(M')$，任何只依赖 $O_I$ 的函数在这两个模型上取值相同，不可能同时等于两个不同的目标值。

加入 $a$ 后相等条件增加了一个坐标，故新等价关系必为旧等价关系的子关系。证毕。

**推论 239.3（干预分离的必要性）。** 若 $M\sim_I M'$ 但 $\Phi(M)\ne\Phi(M')$，则仅对当前边界作任意经典后处理，都不能恢复 $\Phi$。要取得精确目标，必须加入一个能够在该模型对上产生不同结果分布的干预，或加入等价强度的新关系。

### 证明

若所有允许干预在该模型对上也具有相同结果核，则加入它们不会拆开这条纤维，定理 239.2 仍然失败。证毕。

这个判据把“边界是否全息”改写成一个关系问题：不是问边界是否包含隐藏模型的全部细节，而是问它是否已经把当前任务的不同答案分离开。

## 240. 干预的信息价值与协同效应

干预会细分模型纤维，但不同干预的价值可以是非加性的。需要分别定义最坏直径和带先验的平均后验风险。

**定义 240.1（鲁棒目标直径）。** 对非空模型子集 $F\subseteq\mathfrak M$，定义

$$
D_\Phi(F)
=
\sup_{M,M'\in F}
|\Phi(M)-\Phi(M')|.
$$

在当前接口 $I$ 下，模型位于某个纤维 $F_I$。执行干预 $a$ 并观察离散结果 $y$ 后，可能纤维为

$$
F_{I,a,y}
=
\{M\in F_I:P_M^a(y)>0\}.
$$

定义最坏后验直径

$$
\overline D_a(F_I)
=
\sup_{y:F_{I,a,y}\ne\varnothing}
D_\Phi(F_{I,a,y}),
$$

以及鲁棒分离价值

$$
V_\infty(a\mid F_I)
=
D_\Phi(F_I)-\overline D_a(F_I).
$$

**定理 240.2（信息价值的单调性）。** 对任何可行干预 $a$，

$$
\boxed{
0\le V_\infty(a\mid F_I)\le D_\Phi(F_I).
}
\tag{240.1}
$$

若 $V_\infty(a\mid F_I)=D_\Phi(F_I)$，则该干预的每个可能结果都把目标值固定在一个点上。若 $\overline D_a(F_I)>0$，则一次结果不足以在最坏意义下完成目标识别。

### 证明

每个 $F_{I,a,y}$ 都是 $F_I$ 的子集，所以其直径不超过 $D_\Phi(F_I)$。取所有可能 $y$ 的上确界得到 $\overline D_a(F_I)\le D_\Phi(F_I)$，故（240.1）成立。

若价值等于总直径，则 $\overline D_a(F_I)=0$；每个非空后验纤维的目标直径为零，定理 239.2 的纤维判据在一次干预后成立。反之，若某个结果纤维直径为正，则最坏后验仍不能唯一恢复目标。证毕。

**定理 240.3（带先验的方差分解）。** 令 $M$ 按先验 $\lambda$ 取值，$Z=\Phi(M)$，$Y$ 是干预 $a$ 的结果。则

$$
\boxed{
\mathbb E_\lambda[\operatorname{Var}(Z\mid Y)]
=
\operatorname{Var}_\lambda(Z)
-
\operatorname{Var}_\lambda(\mathbb E[Z\mid Y]).
}
\tag{240.2}
$$

所以平均后验方差不会因取得结果而增加；但它与最坏直径价值是两种不同的合同。

### 证明

这是全方差公式

$$
\operatorname{Var}(Z)
=
\mathbb E[\operatorname{Var}(Z\mid Y)]
+
\operatorname{Var}(\mathbb E[Z\mid Y])
$$

的移项。证毕。

**命题 240.4（干预价值可以具有协同效应）。** 令模型由两个隐藏位 $(i,j)\in\{0,1\}^2$ 标记，当前观察为空，目标为 $\Phi(i,j)=i\oplus j$。干预 $a$ 只返回 $i$，干预 $b$ 只返回 $j$。则

$$
V_\infty(a)=V_\infty(b)=0,
\qquad
V_\infty(\{a,b\})=1.
$$

### 证明

执行 $a$ 后，$j$ 仍可取 $0$ 或 $1$，所以异或目标在同一结果纤维中仍取两个值，最坏直径为一。执行 $b$ 同理。

执行二者后，$(i,j)$ 完全确定，异或目标也确定，后验直径为零。初始直径为一，故两步联合价值为一。证毕。

**AHH 240.5（分离价值层）。** 干预的价值不是动作本身的稀有程度或局部误差，而是它对目标等价纤维的切割能力。单步价值可以为零而联合干预具有正价值；因此不能把主动探测预算按独立动作收益简单相加。

## 241. 最小干预集合是一个关系覆盖问题

把不可识别模型对列出来，可以把“需要做哪些干预”写成一个精确的覆盖判据。

**定义 241.1（未分离模型对）。** 在当前接口 $I$ 下，定义

$$
\mathcal P_I
=
\left\{
(M,M')\in\mathfrak M^2:
M\sim_I M',
\ \Phi(M)\ne\Phi(M')
\right\}.
$$

干预 $a$ 覆盖模型对 $(M,M')$，若

$$
P_M^a\ne P_{M'}^a.
$$

对干预集合 $J$，记其覆盖集为

$$
\operatorname{Cov}(J)
=
\{(M,M')\in\mathcal P_I:
\exists a\in J,\ P_M^a\ne P_{M'}^a\}.
$$

**定理 241.2（精确识别的覆盖等价）。** 对有限模型类和有限允许干预族，以下条件等价：

1. $I\cup J$ 能唯一确定 $\Phi$；
2. $\mathcal P_I\subseteq\operatorname{Cov}(J)$；
3. 每一对当前答案不同的模型，都至少被 $J$ 中一个干预分离。

### 证明

若存在 $(M,M')\in\mathcal P_I$ 不在覆盖集内，则它们在 $I$ 和 $J$ 的所有接口读数都相同而目标不同，故不能识别。

反之，若所有 $\mathcal P_I$ 中的模型对都被某个 $a\in J$ 分离，则任何满足 $O_{I\cup J}(M)=O_{I\cup J}(M')$ 的模型对不可能属于 $\mathcal P_I$。于是相等接口必推出相等目标值，应用定理 239.2。证毕。

若每个干预 $a$ 有成本 $c_a>0$，则最小精确干预预算是

$$
\boxed{
\min_{J\subseteq\mathcal A}
\left\{
\sum_{a\in J}c_a:
\mathcal P_I\subseteq\operatorname{Cov}(J)
\right\}.
}
\tag{241.1}
$$

它是关系覆盖，而不是按照动作标签数目平均取样。

**推论 241.3（异或模型的最小预算）。** 在命题 240.4 的四模型中，干预 $a$ 或 $b$ 单独都不能覆盖全部未分离模型对；二者联合才能识别异或目标。若两者成本均为一，则（241.1）的最优值为二。

### 证明

命题 240.4 已证明单独执行任一干预后目标仍有两个可能值，所以至少需要两个干预；执行二者即可确定两个隐藏位，故达到下界。证毕。

**命题 241.4（局部最大分离率不保证最小成本）。** 存在三个干预 $a,b,c$ 和模型对集合，使 $a$ 单独覆盖最多的模型对，但 $b,c$ 的总成本更低且联合覆盖全部模型对。

### 证明

取未分离模型对为 $\{p_1,p_2,p_3,p_4\}$。令 $a$ 覆盖 $\{p_1,p_2,p_3\}$、成本为 $3$；令 $b$ 覆盖 $\{p_1,p_4\}$、成本为 $1$；令 $c$ 覆盖 $\{p_2,p_3\}$、成本为 $1$。$a$ 覆盖数量最多，但 $b,c$ 的联合覆盖为全部四对，成本二小于三。证毕。

**AHH 241.5（主动预算层）。** 可迁移全息的主动扩展不是“把更多动作加入清单”，而是保存当前未分离模型对、每个干预的分离关系和成本。局部观测增益、动作频率与最小识别预算可以给出不同排序；预算必须针对目标纤维的覆盖结构结算。

## 242. AHH：全息边界是可干预的决策几何

把前面的对象合并，得到主动关系边界。

**定义 242.1（主动全息边界）。** 对当前任务定义

$$
\boxed{
\eta_{\mathrm{active}}
=
\left(
\mathfrak M/\!\sim_I,
\Phi,
\mathcal A_{\mathrm{do}},
\{P_M^a\},
\mathcal P_I,
\{c_a\},
\text{停止规则},
\text{来源与干预合同}
\right).
}
\tag{242.1}
$$

其中 $\mathfrak M/\!\sim_I$ 是当前观察边界的等价纤维，$\mathcal P_I$ 是目标不同而当前不可分的模型对，$\{P_M^a\}$ 说明每项干预如何切纤维，成本和停止规则说明主动取得关系的资源合同。

**定理 242.2（主动边界的充分性）。** 在有限模型类、有限干预族和明确结果核的条件下，若两个关系体具有相同的 $\eta_{\mathrm{active}}$，则它们具有相同的：

1. 当前可识别目标泛函集合；
2. 每项干预的最坏后验直径与带先验的后验方差更新；
3. 达到目标识别所需的最小干预成本；
4. 在同一停止规则下的合法主动策略集合。

### 证明

第一项由定理 239.2 的等价纤维判据决定。第二项由定义 240.1、定理 240.2、定理 240.3 及每个结果核决定。第三项由定理 241.2 的覆盖优化决定。第四项由可行干预、成本、结果核和停止规则共同决定；相同字段给出相同的策略树。证毕。

**定理 242.3（删除主动字段的成对反例）。** 若不以等价信息替代而删除以下任一层，则存在相同剩余字段、不同未来主动结论的关系体：

1. 删除 $\mathfrak M/\!\sim_I$：当前观察相同但不同答案的模型对无法列出；
2. 删除 $\{P_M^a\}$：相同动作标签和成本可以对应分离或不分离的干预；
3. 删除 $\mathcal P_I$：无法知道哪些模型对仍需覆盖，命题 241.4 给出成本排序反例；
4. 删除成本：相同分离图会产生不同的最小预算；
5. 删除停止规则：相同识别集合会产生不同的合法主动策略与记录后继。

### 证明

前两项分别由定理 239.2 和命题 236.2 型模型对给出。第三项由定理 241.2 与命题 241.4 给出。第四项取同一覆盖图而交换边成本。第五项取同一干预结果核而使用“达到零直径即停”与“必须达到固定 horizon”两种合同。每项都保留其余字段而改变被删除层，故剩余边界不具普适充分性。证毕。

**AHH 242.4（主动全息）。** 全息边界的最小对象不是已经取得的状态快照，而是一个可干预的决策几何：

$$
\boxed{
\text{当前等价纤维}
+
\text{目标不同的未分离模型对}
+
\text{干预如何切纤维}
+
\text{每项成本与停止规则}.
}
$$

**AHH 的转折是：信息不是静态地“存在于边界里”或“不存在于边界里”；它还由允许的干预把不可识别纤维切开的方式决定。全息充分性因此必须相对于一个主动决策合同，而不是相对于一张固定读数表。**

**来源与边界 242.5。** 本批在有限模型类、有限干预族、明确潜在来源、离散干预结果、固定目标泛函和显式成本/停止合同下，给出纤维识别判据、最坏与先验信息价值、协同干预反例、最小干预集合的关系覆盖等价以及主动全息 AHH。没有把有限模型覆盖问题推广为无限模型的可计算算法，没有把带先验后验方差冒称为最坏风险，没有把局部贪心分离率冒称为全局最小预算，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 243. 实验精化序与边界的单调收缩

主动干预不只有“做或不做”两个选项。一个实验可能保留另一个实验的全部读数，再额外提供可区分的细节；这种关系应当进入全息边界。

**定义 243.1（有限信号实验）。** 在有限模型类 $\mathfrak M$ 上，一个确定性信号实验写为

$$
E=(Y_E,s_E,c_E),
\qquad
s_E:\mathfrak M\to Y_E,
$$

其中 $Y_E$ 是结果集，$c_E>0$ 是成本。给定目标 $\Phi$，结果 $y$ 的模型纤维为

$$
F_{E,y}
=
\{M\in\mathfrak M:s_E(M)=y\},
$$

并定义实验的最坏后验直径

$$
\overline D_\Phi(E)
=
\max_{y:s_E^{-1}(y)\ne\varnothing}
D_\Phi(F_{E,y}).
$$

称 $E'$ **精化** $E$，若存在与模型无关的映射 $r:Y_{E'}\to Y_E$ 使

$$
s_E=r\circ s_{E'}.
$$

于是 $E$ 是把 $E'$ 的结果再次粗粒化得到的实验。

**定理 243.2（精化不增最坏不确定性）。** 若 $E'$ 精化 $E$，则

$$
\boxed{
\overline D_\Phi(E')
\le
\overline D_\Phi(E).
}
\tag{243.1}
$$

若 $E$ 已经精确识别 $\Phi$，则 $E'$ 也精确识别 $\Phi$。

### 证明

对任意 $y'\in Y_{E'}$，有

$$
F_{E',y'}
\subseteq
F_{E,r(y')}.
$$

目标直径对集合包含关系单调不增，所以

$$
D_\Phi(F_{E',y'})
\le
D_\Phi(F_{E,r(y')}).
$$

对 $y'$ 取最大值得到（243.1）。若 $\overline D_\Phi(E)=0$，右侧为零，故精化实验的每个非空纤维也具有零目标直径。证毕。

**定理 243.3（贝叶斯精化的方差单调性）。** 令模型按先验 $\lambda$ 产生精化信号 $Y'$，再经模型无关随机核产生粗化信号 $Y$。于是 $M\to Y'\to Y$ 构成马尔可夫链。对任意平方可积目标 $Z=\Phi(M)$，有

$$
\boxed{
\mathbb E[\operatorname{Var}(Z\mid Y')]
\le
\mathbb E[\operatorname{Var}(Z\mid Y)].
}
\tag{243.2}
$$

### 证明

因为 $Y$ 是 $Y'$ 的随机后处理，有

$$
\operatorname{Var}(Z\mid Y)
=
\mathbb E[\operatorname{Var}(Z\mid Y')\mid Y]
+
\operatorname{Var}(\mathbb E[Z\mid Y']\mid Y).
$$

第二项非负。对 $Y$ 取期望即得（243.2）。证毕。

确定性精化给出最坏直径的单调性，随机精化给出先验平均方差的单调性；两者的量词不同，不能互相替代。

**命题 243.4（成本会打破信息单调的行动排序）。** 若 $E'$ 精化 $E$ 但 $c_{E'}>c_E$，则 $E'$ 虽然一定不差于 $E$，却未必具有更高的单位成本信息价值。取两个实验的后验直径分别为 $1/2$ 和 $0$，成本分别为 $1$ 和 $100$，按每单位成本计算时粗实验更优。

### 证明

信息减少量分别为 $1/2$ 与 $1$，单位成本收益为 $1/2$ 与 $1/100$。精化的无条件优越性不蕴含预算合同下的优先级。证毕。

**AHH 243.5（精化层）。** 可迁移边界不仅要保存某次干预的结果，还要保存实验之间的精化关系。精化决定不确定性怎样单调收缩，成本决定这种收缩在主动任务中是否值得取得。

## 244. 任务相对的最小全息商

上一节给出了实验如何切细纤维；这一节说明“最小边界”必须相对于未来要回答的任务族定义。

**定义 244.1（任务等价）。** 给定目标泛函族 $\mathcal T\subseteq\{\Phi:\mathfrak M\to\mathbb R\}$，定义

$$
M\sim_{\mathcal T}M'
\quad\Longleftrightarrow\quad
\Phi(M)=\Phi(M')
\quad\text{对所有 }\Phi\in\mathcal T.
$$

记商映射为

$$
q_{\mathcal T}:\mathfrak M\to\mathfrak M/\!\sim_{\mathcal T}.
$$

**定理 244.2（任务商的最小充分性）。** 商映射 $q_{\mathcal T}$ 本身足以恢复 $\mathcal T$ 中的每个目标。若另一个摘要 $S:\mathfrak M\to\mathcal Z$ 也足以恢复全部 $\mathcal T$，即

$$
S(M)=S(M')
\Longrightarrow
\Phi(M)=\Phi(M')
\quad\forall\Phi\in\mathcal T,
$$

则存在唯一映射 $f$ 使

$$
\boxed{
q_{\mathcal T}=f\circ S.
}
\tag{244.1}
$$

换言之，任何足以回答 $\mathcal T$ 的摘要都至少区分任务商要求区分的模型类；任务商是最粗的精确全息边界。

### 证明

若 $S(M)=S(M')$，充分性假设给出 $M\sim_{\mathcal T}M'$，所以可定义

$$
f(S(M))=[M]_{\mathcal T}.
$$

若同一 $S$ 值有两个表示 $M,M'$，它们属于同一任务等价类，故 $f$ 良定义。显然 $q_{\mathcal T}=f\circ S$。商类上的每个 $\Phi$ 都是良定义函数，故 $q_{\mathcal T}$ 足以恢复全部目标。唯一性来自 $S(\mathfrak M)$ 上的像。证毕。

**推论 244.3（任务扩展必细化边界）。** 若 $\mathcal T\subseteq\mathcal T'$，则

$$
\sim_{\mathcal T'}\subseteq\sim_{\mathcal T}.
$$

增加未来任务只能细分最小全息商，不能由旧商自动恢复新任务中区分的模型。

### 证明

新等价关系要求对更多泛函取相同值，故包含关系成立。证毕。

这说明“完整内部状态”不是脱离任务的唯一概念。对单一终端概率，商可以很粗；一旦允许干预、尾部风险或资源优化，任务族扩大，所需商也必须细化。

**AHH 244.4（任务商层）。** 全息充分性是一个商结构，而不是一个固定维数。边界保存的是未来任务仍能区分的等价类；换任务合同等价于改变商的粒度。

## 245. 预算约束下的自适应干预递归

单步价值不能处理协同干预。有限模型类中，可以直接写出带成本和停止的 Bellman 递归。

**定义 245.1（最坏目标直径值函数）。** 令 $F\subseteq\mathfrak M$ 是当前非空模型纤维，令 $b\ge0$ 是剩余预算。对干预 $a$，结果信号为 $s_a:\mathfrak M\to Y_a$，成本为 $c_a$，定义

$$
F_{a,y}
=
\{M\in F:s_a(M)=y\}.
$$

令 $V(F,b)$ 表示在预算 $b$ 内允许自适应选择干预并可停止时，终端最坏目标直径的最小值。

**定理 245.2（主动识别的 Bellman 方程）。** 在有限模型类、有限干预族和正成本条件下，

$$
\boxed{
V(F,b)
=
\min\!\left\{
D_\Phi(F),
\ \min_{a:c_a\le b}
\ \max_{y:F_{a,y}\ne\varnothing}
V(F_{a,y},b-c_a)
\right\}.
}
\tag{245.1}
$$

若 $D_\Phi(F)=0$，则 $V(F,b)=0$；若没有剩余预算可执行干预，第一项给出唯一值。

### 证明

对任意合法策略，第一步要么停止，此时最坏直径为 $D_\Phi(F)$；要么选择某个 $a$，付出 $c_a$ 后观察结果 $y$，进入纤维 $F_{a,y}$，剩余策略的最坏值至少为 $V(F_{a,y},b-c_a)$。因此任何策略的值都不小于右侧。

反过来，选择右侧达到最小值的停止动作或干预 $a$；对每个可达 $y$，递归采用达到 $V(F_{a,y},b-c_a)$ 的策略。有限模型类和正成本保证预算或模型纤维在有限步内下降，归纳得到右侧值可达。两边相等。证毕。

**推论 245.3（异或协同的动态值）。** 在命题 240.4 的四模型异或任务中，两个位干预成本均为一，则

$$
V(\mathfrak M,0)=1,
\qquad
V(\mathfrak M,1)=1,
\qquad
V(\mathfrak M,2)=0.
$$

### 证明

预算为零时只能停止，初始目标直径为一。预算为一时执行任一位干预，所得纤维仍包含两个异或值，最坏直径仍为一。预算为二时先取得一个位，再对剩余两模型执行另一个位，终端纤维为单点，值为零。证毕。

所以 §240 中的“单步价值为零”并不意味着干预无用；它可能是一个只有在后续预算存在时才显现的动态价值。

**命题 245.4（停止规则是边界字段）。** 对同一模型类、干预核和预算，规则“达到 $D_\Phi=0$ 即停”与规则“必须执行固定 $H$ 轮”产生不同的合法策略树和记录成本，即使两者最终都能识别目标。

### 证明

在第一条规则下，单点纤维一旦出现就没有合法继续的必要；在第二条规则下，仍必须追加后续记录或执行空操作。记录长度和资源消耗不同，故主动边界不同。证毕。

**AHH 245.5（递归预算层）。** 主动全息不是静态的“最少做哪些实验”，而是一个带预算状态的递归值函数。协同干预、历史纤维和停止规则共同决定下一项合法动作；逐步贪心的局部价值不能替代 Bellman 边界。

## 246. AHH：实验类别与主动全息的统一边界

前面的对象可以组成一个任务相对、可精化、可递归的主动关系接口。

**定义 246.1（实验—任务全息边界）。** 对任务族 $\mathcal T$ 和允许实验类别 $\mathcal E$，定义

$$
\boxed{
\eta_{\mathrm{exp}}
=
\left(
\mathfrak M/\!\sim_{\mathcal T},
\mathcal E,
\preceq_{\mathrm{refine}},
\{s_E,c_E\}_{E\in\mathcal E},
\{F_{E,y}\},
V,
\text{来源与干预合同}
\right).
}
\tag{246.1}
$$

其中 $\preceq_{\mathrm{refine}}$ 是实验精化序，$F_{E,y}$ 是结果纤维，$V$ 是在给定预算和停止规则下的递归主动值。

**定理 246.2（实验—任务边界的充分性）。** 在有限模型类、有限实验类别、明确成本、明确停止规则和明确结果信号的条件下，两个关系体若具有相同的 $\eta_{\mathrm{exp}}$，则具有相同的：

1. 任务族 $\mathcal T$ 的可识别目标；
2. 实验精化造成的最坏直径与贝叶斯方差单调关系；
3. 每个预算状态的最优主动值函数与合法策略树；
4. 达到任务识别所需的最小资源合同。

### 证明

第一项由定理 244.2，第二项由定理 243.2—243.3，第三项由定理 245.2 的递归，第四项由同一递归的零值状态和成本约束决定。相同边界字段逐项给出相同结果。证毕。

**定理 246.3（删除实验类别字段的反例）。** 若不以等价信息替代而删除以下任一字段，则存在相同剩余边界、不同未来主动结论的关系体：

1. 删除任务商：新增任务可能细分原先合并的模型；
2. 删除精化序：无法判断一个结果是否是另一个结果的无损细化；
3. 删除结果纤维：相同成本和标签可以对应完全不同的识别能力；
4. 删除递归值函数：单步收益相同的实验可以有不同的多步协同价值；
5. 删除停止规则：同一目标和实验集会产生不同合法记录长度与成本。

### 证明

第一项由推论 244.3，第二项由定理 243.2，第三项由定理 239.2，第四项由推论 245.3，第五项由命题 245.4 分别给出。证毕。

**AHH 246.4（主动全息）。** 全息边界最终表现为一个带精化序的实验类别作用在任务商上的递归决策几何：

$$
\boxed{
\text{任务商}
+
\text{实验精化}
+
\text{结果纤维}
+
\text{预算递归}
+
\text{停止合同}.
}
$$

**AHH 的核心是：边界的“完整性”不等于保存最多数据，而等于保存所有允许未来实验对任务商的作用，以及这些作用的成本和停止后继。波粒关系中的一次局域事件因此不只是一个结果标签，它也改变了后续可识别纤维和下一次合法测量的决策空间。**

**来源与边界 246.5。** 本批在有限模型类、有限信号实验、确定性精化、有限成本、有限预算和明确任务族下，给出实验精化单调性、任务相对最小商、主动干预 Bellman 方程、异或协同和实验—任务全息 AHH。没有把有限 Bellman 递归推广到无限模型的可计算性，没有把随机实验的最坏直径单调性冒称为无条件结论，没有把后验方差与最坏风险混同，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 247. 接口核的拼接结合律与误差传播

主动实验可以分成多个关系体。若只保存每段的终端边缘，段与段之间的接口关系可能丢失；首先把可拼接对象写成带接口的核。

**定义 247.1（接口标记核）。** 令 $Z$ 是有限接口集合，第一段关系体在模型 $M$ 下产生接口分布 $\lambda_M$，第二段关系体从接口 $z$ 到终端结果的核为 $K_M(\,\cdot\mid z)$。两段的拼接终端分布定义为

$$
(\lambda_M\star K_M)(y)
=
\sum_{z\in Z}\lambda_M(z)K_M(y\mid z).
$$

若第三段核为 $L_M(w\mid y)$，定义三段拼接的顺序为

$$
\lambda_M\star K_M\star L_M.
$$

接口标签属于边界合同；把 $z$ 忘掉后，$\lambda_M$ 与 $K_M$ 的乘积通常不能由两个独立终端边缘恢复。

**定理 247.2（接口拼接结合律）。** 对任意有限接口和概率核，

$$
\boxed{
(\lambda_M\star K_M)\star L_M
=
\lambda_M\star(K_M\star L_M).
}
\tag{247.1}
$$

若真实与名义两段满足

$$
D_{\mathrm{TV}}(\lambda_M,\bar\lambda_M)\le\varepsilon_1,
\qquad
\sup_{z\in Z}
D_{\mathrm{TV}}(K_M(\cdot\mid z),\bar K_M(\cdot\mid z))
\le\varepsilon_2,
$$

则

$$
\boxed{
D_{\mathrm{TV}}(\lambda_M\star K_M,
\bar\lambda_M\star\bar K_M)
\le
\varepsilon_1+\varepsilon_2.
}
\tag{247.2}
$$

更精细地，第二项可以替换为

$$
\sum_z\bar\lambda_M(z)
D_{\mathrm{TV}}(K_M(\cdot\mid z),\bar K_M(\cdot\mid z)).
$$

### 证明

展开左侧：

$$
\sum_y\left(\sum_z\lambda_M(z)K_M(y\mid z)\right)L_M(w\mid y)
=
\sum_{z,y}\lambda_M(z)K_M(y\mid z)L_M(w\mid y),
$$

右侧展开得到同一有限和，故结合律成立。

误差项作望远镜分解：

$$
\lambda K-\bar\lambda\bar K
=
(\lambda-\bar\lambda)K
+
\bar\lambda(K-\bar K).
$$

概率核对全变差距离是收缩的，第一项不超过 $\varepsilon_1$；第二项由凸性不超过接口条件误差的加权和，进而不超过 $\varepsilon_2$。证毕。

**推论 247.3（多段串联）。** 对 $n$ 个带共同接口合同的关系体，若第 $i$ 段的统一接口误差不超过 $\varepsilon_i$，则整体终端误差不超过

$$
D_{\mathrm{TV}}(\Lambda_1\star\cdots\star\Lambda_n,
\bar\Lambda_1\star\cdots\star\bar\Lambda_n)
\le
\sum_{i=1}^{n}\varepsilon_i.
$$

若每段后续作用有增益 $g_i$，则第 $i$ 段误差项按其后续增益乘积传播。

### 证明

对段数作归纳，使用定理 247.2；引入增益时对望远镜的每一项乘以其后段算子范数。证毕。

**AHH 247.4（接口拼接层）。** 局部全息要成为可组合全息，边界必须保存同一接口标签、条件核和误差传播合同。结合律来自接口求和，而不是来自两个终端边缘的偶然相等。

## 248. 终端边缘相同仍可能无法拼接

**命题 248.1（均匀校准下的接口遗忘反例）。** 令 $Z,Y\in\{0,1\}$。两个第二段实现分别为

$$
K_+(y\mid z)=1_{\{y=z\}},
\qquad
K_-(y\mid z)=1_{\{y=1-z\}}.
$$

在均匀校准接口 $\nu(0)=\nu(1)=1/2$ 下，两者的终端边缘都均匀：

$$
\sum_z\nu(z)K_+(y\mid z)
=
\sum_z\nu(z)K_-(y\mid z)
=
\frac12.
$$

但若第一段真实产生

$$
\lambda(0)=0.8,
\qquad
\lambda(1)=0.2,
$$

则拼接后的终端分布分别为

$$
(\lambda\star K_+)(0)=0.8,
\qquad
(\lambda\star K_-)(0)=0.2.
$$

### 证明

均匀校准时，恒等映射和翻转映射都把一半质量送到每个终端。真实接口分布不均匀时，恒等映射保留 $z=0$ 的质量，翻转映射把它送到 $y=1$，故得到 $0.8$ 与 $0.2$。证毕。

**推论 248.2（局部充分性不自动拼接）。** 若第一段边界只保存接口的终端边缘、第二段边界只保存校准接口下的终端边缘，而不保存 $K(\cdot\mid z)$ 或等价的接口条件关系，则不存在对所有真实接口分布都 sound 的非平凡拼接证书。

### 证明

命题 248.1 中两个第二段边界摘要完全相同，但对真实第一段接口产生不同终端响应。任何只使用两个局部摘要的拼接函数都会对它们给出同一答案，因而至少错于一个实现。证毕。

**命题 248.3（接口相关性可以隐藏在联合记录中）。** 若第一段还保留一个与 $Z$ 相关的隐藏记录 $R$，而第二段的核实际为 $K(y\mid z,r)$，则只保存 $P(Z)$ 与 $P(Y)$ 的两个边缘，仍不能决定带后续检验 $F(Y,R)$ 的值。

### 证明

取 $R=Z$ 与 $R=1-Z$ 两种联合实现，使各自 $Z$、$Y$ 边缘相同，但令后续检验为 $F=1_{\{Y=R\}}$。在一实现中检验恒为一，在另一实现中恒为零。边缘后处理无法恢复联合记录。证毕。

**AHH 248.4（接口相关性）。** 可拼接全息边界必须保存接口的条件关系和仍可访问的联合记录。终端边缘相同只证明一个狭窄终端任务相同，不证明任何后续接口任务相同。

## 249. 延续等价给出最小接口商

接口不必保留全部原始标签；真正需要的是未来允许续接仍能区分的接口类。

**定义 249.1（接口延续等价）。** 固定允许的后续合同族 $\mathcal K$。对接口状态 $z,z'\in Z$，定义

$$
z\sim_{\mathcal K}z'
$$

当且仅当对每个后续核 $K\in\mathcal K$、每个允许终端效果 $f$，都有

$$
\sum_yK(y\mid z)f(y)
=
\sum_yK(y\mid z')f(y).
$$

记商映射为 $q_{\mathcal K}:Z\to Z/\!\sim_{\mathcal K}$。

**定理 249.2（接口商的充分性与最小性）。** 若两个接口状态满足 $z\sim_{\mathcal K}z'$，则对所有允许续接，它们可以在边界中合并而不改变任何任务响应。若 $z\not\sim_{\mathcal K}z'$，则存在一个允许续接和终端效果将二者区分；任何对全部 $\mathcal K$ 充分的接口摘要都必须把它们保留在不同类中。

### 证明

等价关系的定义已经给出第一句：所有后续核和效果的响应完全相同，所以替换 $z$ 与 $z'$ 不改变任何拼接响应。

若 $z\not\sim_{\mathcal K}z'$，按否定定义存在 $K\in\mathcal K$ 和 $f$ 使两侧响应不同。该续接就是区分见证。若某摘要把二者合并，则它对该续接只能给出同一响应，故不可能对全部 $\mathcal K$ 充分。证毕。

**推论 249.3（接口压缩的条件）。** 任何把接口分成 $\sim_{\mathcal K}$ 的商类的映射，都能把拼接计算改写为商接口上的加权核；若商类有限，接口记忆和误差证书都可按商类而非原始标签保存。

### 证明

对同一商类的接口，定理 249.2 保证所有允许后续响应相同，所以先对原始接口质量求和再对商类求和，结果不变。证毕。

**AHH 249.4（延续接口层）。** 接口的最小全息对象不是接口标签本身，而是相对于允许后续的延续等价类。扩大后续合同会细分接口商；删除后续合同则可能允许更强压缩。

## 250. AHH：可组合全息是一个接口函子

把局部关系体、接口商和误差债务合并，可得到可拼接边界。

**定义 250.1（可组合全息边界）。** 对允许拼接的关系体族定义

$$
\boxed{
\eta_{\mathrm{comp}}
=
\left(
Z/\!\sim_{\mathcal K},
\{\lambda_M\},
\{K_M(\cdot\mid[z])\},
\mathcal K,
\preceq_{\mathrm{refine}},
\{\varepsilon_i,g_i\},
\text{联合记录与接口所有权},
\text{资源债务}
\right).
}
\tag{250.1}
$$

其中 $Z/\!\sim_{\mathcal K}$ 是延续接口商，$\lambda_M$ 是商接口分布，$K_M(\cdot\mid[z])$ 是在商类上的条件续接核，$\mathcal K$ 是允许后续族。资源债务记录尚未支付的校准、记录或接口访问成本；它不能被终端概率本身代替。

**定理 250.2（可组合边界的充分性）。** 在有限接口、有限关系体、共同接口语义、明确后续族和有限误差增益条件下，若两个系统具有相同的 $\eta_{\mathrm{comp}}$，则它们对每个允许的有限拼接词给出相同的：

1. 终端响应；
2. 接口商上的延续等价；
3. 望远镜误差上界；
4. 资源债务与可行拼接策略。

### 证明

终端响应由接口商上的核迭代和定理 247.2 的结合律决定；延续等价由定理 249.2 决定；误差上界由定理 247.2—247.3 的局部误差和增益决定；可行策略还取决于接口所有权、联合记录和资源债务。边界字段逐项相同，故四类结果相同。证毕。

**定理 250.3（删除接口字段的不可充分性）。** 若不以等价信息替代而删除以下任一字段，则存在相同剩余摘要、不同拼接未来的关系体：

1. 删除条件接口核：由命题 248.1，校准边缘相同而真实接口分布下终端不同；
2. 删除延续接口商：由定理 249.2，某个允许后续会区分被合并的接口；
3. 删除联合记录：由命题 248.3，边缘相同而联合终端效果不同；
4. 删除误差增益：同一局部误差在不同后续长度下有不同整体界；
5. 删除资源债务：同一数学拼接在可访问接口与不可支付接口下具有不同合法性。

### 证明

前两项分别由命题 248.1 与定理 249.2 直接给出。第三项由命题 248.3 给出。第四项取两个续接核一个为恒等、一个为增益 $G>1$，代入式（247.3）。第五项取同一接口核而让接口访问成本超过剩余预算；一个合同可拼接，另一个合同只能停止。证毕。

**AHH 250.4（可组合全息）。** 局部全息的组合律不是“两个摘要都充分，所以直接相乘”，而是一个接口函子：

$$
\boxed{
\text{接口延续商}
+
\text{条件核与联合记录}
+
\text{拼接结合律}
+
\text{误差增益}
+
\text{资源债务}.
}
$$

**AHH 的核心是：终端边界能回答一个局部问题，不代表它能作为另一个关系体的接口。只有当边界保留所有允许后续能看见的接口关系，并把误差与未支付成本沿结合律传递时，局部全息才成为可组合全息。**

**来源与边界 250.5。** 本批在有限接口、有限关系体、有限后续族、概率核全变差距离、明确接口所有权和有限资源债务下，给出接口拼接结合律、条件误差传播、终端边缘反例、延续接口商最小性和可组合全息 AHH。没有把两个局部终端通道的相等推广成任意接口相等，没有把接口商推广到未声明的后续族，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 251. 并行关系体需要联合接口而不只是两个边缘

串联拼接沿一个接口求和；并行组合则同时暴露两个接口。只有在共同来源确实因子化时，两个局部边界才可以独立张量化。

**定义 251.1（并行接口合同）。** 令 $Z_A,Z_B$ 是两个并行关系体的接口，联合接口来源为 $\Gamma_M$，它是 $Z_A\times Z_B$ 上的概率分布。两个局部续接核分别为 $K^A_M(y_A\mid z_A)$ 和 $K^B_M(y_B\mid z_B)$。并行终端分布为

$$
P_M(y_A,y_B)
=
\sum_{z_A,z_B}
\Gamma_M(z_A,z_B)
K^A_M(y_A\mid z_A)
K^B_M(y_B\mid z_B).
$$

若声明了独立来源合同

$$
\Gamma_M(z_A,z_B)
=
\lambda^A_M(z_A)\lambda^B_M(z_B),
$$

则称该并行边界为因子化；否则必须保留联合接口来源，而不能由两个边缘 $\lambda^A_M,\lambda^B_M$ 代替。

**定理 251.2（因子化并行的响应与误差）。** 在因子化合同下，

$$
\boxed{
P_M(y_A,y_B)
=
P^A_M(y_A)P^B_M(y_B),
}
\tag{251.1}
$$

其中 $P^A_M=\lambda^A_M\star K^A_M$，$P^B_M=\lambda^B_M\star K^B_M$。若真实与名义局部终端分布满足

$$
D_{\mathrm{TV}}(P^A_M,\bar P^A_M)\le\varepsilon_A,
\qquad
D_{\mathrm{TV}}(P^B_M,\bar P^B_M)\le\varepsilon_B,
$$

则

$$
\boxed{
D_{\mathrm{TV}}(P^A_M\otimes P^B_M,
\bar P^A_M\otimes\bar P^B_M)
\le
1-(1-\varepsilon_A)(1-\varepsilon_B)
\le
\varepsilon_A+\varepsilon_B.
}
\tag{251.2}
$$

### 证明

在因子化合同下，双重求和拆成两个独立和，得到（251.1）。

分别取实现两个局部全变差距离的最大耦合，使两对局部变量分别以至少 $1-\varepsilon_A$ 与 $1-\varepsilon_B$ 的概率相等。令两对耦合独立，则两个并行输出同时相等的概率至少为 $(1-\varepsilon_A)(1-\varepsilon_B)$。耦合表征给出全变差距离不超过其不同概率，即得第一项；展开乘积得到第二项。证毕。

若来源只具有给定边缘而不具有因子化合同，则（251.1）不成立；这时整体误差要按联合 $\Gamma_M$ 的距离结算。

**推论 251.3（资源共享破坏独立执行）。** 即使两个并行关系体的数学响应因子化，若它们共享一个容量为 $B$ 的资源且各自成本为 $c_A,c_B$，则只有在 $c_A+c_B\le B$ 时二者同时属于同一合法后继。资源预算是并行边界的第三个联合字段。

### 证明

并行执行需要同时满足两项资源义务，成本可加；若总成本超过容量，联合操作不在合法操作集合中。数学张量积本身不能解除资源约束。证毕。

**AHH 251.4（并行联合层）。** 并行全息需要保存两个局部接口的联合来源、是否因子化及共享资源合同。局部响应各自充分，不代表它们可以在同一个未来中独立执行。

## 252. 相同局部边缘的共同来源反例

**命题 252.1（并行相关性不可由边缘恢复）。** 令 $Z_A,Z_B\in\{0,1\}$，两个局部接口边缘都均匀。定义两种联合来源

$$
\Gamma_+(0,0)=\Gamma_+(1,1)=\frac12,
\qquad
\Gamma_-(0,1)=\Gamma_-(1,0)=\frac12.
$$

两种来源的每个局部边缘完全相同。若并行终端任务为

$$
F(z_A,z_B)=1_{\{z_A=z_B\}},
$$

则

$$
\boxed{
\mathbb E_{\Gamma_+}F=1,
\qquad
\mathbb E_{\Gamma_-}F=0.
}
\tag{252.1}
$$

### 证明

在 $\Gamma_+$ 下两个接口总是相等，在 $\Gamma_-$ 下总是不等。边缘求和在两种情况下都给每个接口取 $0,1$ 各一半概率，但联合事件不同。证毕。

**推论 252.2（局部并行证书的失效）。** 任何只保存 $Z_A$ 与 $Z_B$ 的边缘边界、却不保存 $\Gamma$ 的并行证书，都不能同时正确回答所有依赖两个接口联合关系的终端任务。

### 证明

命题 252.1 给出相同边缘字段、不同任务值的成对实现。边缘后处理对两者给出同一答案，故至少错于一个。证毕。

若后续实验只分别读取 $Z_A$ 或 $Z_B$，边缘边界可能足够；一旦允许读取奇偶性、碰撞、联合失败或共享控制，联合来源就成为可见关系。

**AHH 252.3（共同来源层）。** 并行接口的“各自完整”不推出“联合完整”。相关性是并行组合中的独立全息层，不能用两个局部误差半径或两个局部终端概率替代。

## 253. 部分序并发与事件顺序的可交换性

并行关系体还可能在同一段历史中交错执行。此时边界必须说明哪些事件可交换，哪些顺序会改变后续状态。

**定义 253.1（部分序事件合同）。** 令 $P$ 是有限事件集合上的偏序。其线性扩展 $w=(e_1,\ldots,e_n)$ 是满足偏序的合法执行词。每个事件 $e$ 对关系状态施加线性响应算子 $T_e$。给定终端效果 $f$，词 $w$ 的响应为

$$
R_w(x)=f(T_{e_n}\cdots T_{e_1}x).
$$

若两个无序关系事件 $e,f$ 满足

$$
T_eT_f=T_fT_e,
$$

称它们在声明合同下可交换。

**定理 253.2（局部可交换推出线性扩展不变）。** 若 $P$ 中每一对无序事件的响应算子都两两可交换，则任意两个线性扩展 $w,w'$ 对所有初态和终端效果给出相同响应：

$$
\boxed{
R_w=R_{w'}.
}
\tag{253.1}
$$

### 证明

有限偏序的任意两个线性扩展可以通过有限次交换相邻的无序事件互相变换。每次相邻交换把局部因子 $T_eT_f$ 换成 $T_fT_e$，由交换假设响应不变。有限次交换后得到（253.1）。证毕。

**命题 253.3（不交换时顺序必须入边界）。** 若存在无序事件 $e,f$ 使 $T_eT_f\ne T_fT_e$，则存在初态 $x$ 和终端效果 $f_0$ 使两个合法线性扩展 $ef$ 与 $fe$ 的响应不同。因而只保存事件集合而删除其合法顺序关系，不能对所有终端任务保持充分。

### 证明

由算子不等式，存在 $x$ 使 $(T_eT_f-T_fT_e)x\ne0$。有限维对偶分离保证存在线性效果 $f_0$ 使

$$
f_0(T_eT_fx)\ne f_0(T_fT_ex).
$$

两词都是同一偏序下的线性扩展，但给出不同响应。证毕。

**例 253.4（二维非交换响应）。** 取

$$
T_e=
\begin{pmatrix}
1&1\\
0&1
\end{pmatrix},
\qquad
T_f=
\begin{pmatrix}
1&0\\
1&1
\end{pmatrix}.
$$

则

$$
T_eT_f=
\begin{pmatrix}
2&1\\
1&1
\end{pmatrix},
\qquad
T_fT_e=
\begin{pmatrix}
1&1\\
1&2
\end{pmatrix},
$$

两者不同。初态 $x=(1,0)^{\mathsf T}$ 和第一坐标效果即可区分两个顺序。

**AHH 253.5（因果顺序层）。** 并发边界需要保存偏序、可交换关系和仍允许的线性扩展。把“同时发生”压成一个无序集合，只有在所有无序事件对都可交换时才保持相同的未来。

## 254. AHH：组合全息的三种代数模式

串联接口、并行联合来源和部分序并发不能由一个“组合”标签替代；它们要求不同的边界字段。

**定义 254.1（组合代数边界）。** 对允许的组合合同定义

$$
\boxed{
\eta_{\mathrm{alg}}
=
\left(
\text{串联接口商},
\text{并行联合来源},
\text{因子化见证},
\text{部分序与交换关系},
\text{条件核},
\text{误差增益},
\text{共享资源义务},
\text{联合记录}
\right).
}
\tag{254.1}
$$

串联字段支持接口卷积，并行字段支持联合测度，部分序字段支持线性扩展；共享资源和联合记录约束哪些代数组合实际上是合法后继。

**定理 254.2（组合代数边界的充分性）。** 在有限事件、有限接口、有限关系体和明确资源合同下，若两个系统具有相同的 $\eta_{\mathrm{alg}}$，则对每个允许的串联、并行和部分序组合，它们具有相同的：

1. 终端响应；
2. 允许线性扩展集合；
3. 局部误差沿组合的传播上界；
4. 资源可行性和联合记录响应。

### 证明

串联终端响应和误差由定理 247.2—247.3 与接口商决定；并行响应和误差由定理 251.2 及联合来源决定；顺序集合和响应由定理 253.2—253.3 决定；资源和记录字段分别决定组合是否属于合法后继以及联合终端效果。逐项相同的边界给出逐项相同的结果。证毕。

**定理 254.3（删除组合模式的反例）。** 若不以等价信息替代而删除以下任一字段，则存在相同剩余边界、不同组合未来的关系体：

1. 删除串联接口商：由定理 249.2，允许后续可以区分被合并的接口；
2. 删除并行联合来源：由命题 252.1，相同边缘给出不同联合任务；
3. 删除部分序与交换关系：由命题 253.3，相同事件集合给出不同顺序响应；
4. 删除共享资源义务：数学组合相同但一个后继超出容量；
5. 删除联合记录：局部终端相同但联合后续效果不同。

### 证明

前两项由定理 249.2 和命题 252.1 直接给出，第三项由命题 253.3 给出，第四项由推论 251.3 给出，第五项由命题 248.3 给出。每项都保留其余字段而改变被删除层，所以剩余边界不能普适决定组合未来。证毕。

**AHH 254.4（组合全息）。** 可组合全息的最小对象不是局部摘要的并集，而是一个带模式的组合代数：

$$
\boxed{
\text{串联接口}
+
\text{并行联合来源}
+
\text{部分序交换}
+
\text{误差与资源传播}
+
\text{联合记录}.
}
$$

**AHH 的核心是：同一批局部关系体，采用串联、并行或交错组合时可能拥有不同的未来；全息边界必须保存“如何组合”的代数，而不只是保存“各自是什么”的局部数据。**

**来源与边界 254.5。** 本批在有限接口、有限并行来源、有限事件偏序、有限线性扩展、概率核全变差距离、线性响应算子和明确资源合同下，给出并行因子化误差界、共同来源反例、部分序交换定理、非交换顺序反例和组合代数 AHH。没有把局部终端边缘相等推广成联合独立，没有把非交换算子自动解释为具体物理哈密顿量，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 255. 闭环接口的固定点与回路增益

组合代数遇到反馈时，接口会再次返回同一关系体。此时一次终端响应不再足以描述未来；必须保存一轮回路怎样把扰动送回接口。

**定义 255.1（线性反馈合同）。** 令 $\mathcal H$ 是有限维赋范空间，$A:\mathcal H\to\mathcal H$ 是一轮闭环返回算子，$b\in\mathcal H$ 是外部注入。闭环状态满足

$$
x=Ax+b.
$$

若 $\|A\|<1$，称该反馈合同为收缩稳定，并定义回路解析子

$$
R_A=(I-A)^{-1}.
$$

它把接口注入变成固定点响应。

**定理 255.2（收缩闭环的唯一性与截断界）。** 若 $\|A\|=q<1$，则闭环方程有唯一解

$$
\boxed{
x^*=R_Ab
=
\sum_{n=0}^{\infty}A^nb.
}
\tag{255.1}
$$

有限回路展开 $x_N=\sum_{n=0}^{N}A^nb$ 满足

$$
\boxed{
\|x^*-x_N\|
\le
\frac{q^{N+1}}{1-q}\|b\|.
}
\tag{255.2}
$$

### 证明

映射 $F(x)=Ax+b$ 是常数 $q<1$ 的压缩映射，故存在唯一不动点。又有 $\|A^n\|\le q^n$，几何级数在算子范数下收敛，并满足

$$
(I-A)\sum_{n=0}^{\infty}A^n=I.
$$

因此级数等于 $(I-A)^{-1}$。尾项范数满足

$$
\left\|\sum_{n=N+1}^{\infty}A^nb\right\|
\le
\sum_{n=N+1}^{\infty}q^n\|b\|
=
\frac{q^{N+1}}{1-q}\|b\|.
$$

证毕。

**定理 255.3（闭环失配的解析放大）。** 设真实和名义闭环分别为 $(A,b)$ 与 $(\bar A,\bar b)$，且 $\|A\|,\|\bar A\|\le q<1$。令

$$
\delta_A=\|A-\bar A\|,
\qquad
\delta_b=\|b-\bar b\|.
$$

则

$$
\boxed{
\|x^*-\bar x^*\|
\le
\frac{1}{1-q}
\left(
\delta_b+\delta_A\|\bar x^*\|
\right).
}
\tag{255.3}
$$

### 证明

由 $(I-A)x^*=b$ 和 $(I-\bar A)\bar x^*=\bar b$，

$$
x^*-\bar x^*
=
(I-A)^{-1}
\left[
(b-\bar b)+(A-\bar A)\bar x^*
\right].
$$

Neumann 级数给出 $\|(I-A)^{-1}\|\le(1-q)^{-1}$；取范数即得（255.3）。证毕。

闭环误差的放大因子不是一次局部动作的误差，而是稳定余量 $(1-q)^{-1}$。当回路接近临界时，极小的接口失配也可以产生宏观的固定点差异。

**AHH 255.4（回路解析层）。** 闭环全息必须保存回路增益或等价的解析子。固定点是回路无限次返回后的一个结果，不能反向决定回路怎样放大下一次接口扰动。

## 256. 相同固定点不等于相同闭环边界

**命题 256.1（同固定点、不同敏感度）。** 在一维空间中，考虑两个反馈模型

$$
(A_1,b_1)=(0,1),
\qquad
(A_2,b_2)=\left(\frac12,\frac12\right).
$$

二者的固定点都为 $x^*=1$，但对同一外部注入 $\delta$，新的固定点分别为

$$
x_1' =1+\delta,
\qquad
x_2'=1+2\delta.
$$

因此保存当前固定点 $1$ 不能决定未来接口响应。

### 证明

直接代入 $x=Ax+b$ 得到两模型的固定点。将 $b_i$ 替换为 $b_i+\delta$ 后，响应增益分别为 $(1-A_1)^{-1}=1$ 和 $(1-A_2)^{-1}=2$。证毕。

**命题 256.2（临界余量是可见的未来关系）。** 取

$$
A_\varepsilon=1-\varepsilon,
\qquad
b_\varepsilon=\varepsilon,
\qquad
0<\varepsilon<1.
$$

所有模型的固定点都为 $1$，但解析子为 $R_\varepsilon=\varepsilon^{-1}$，截断界和失配界随 $\varepsilon\downarrow0$ 发散。

### 证明

有

$$
R_\varepsilon=(1-A_\varepsilon)^{-1}=\varepsilon^{-1},
\qquad
R_\varepsilon b_\varepsilon=1.
$$

将其代入（255.2）和（255.3）即可。证毕。

**推论 256.3（闭环分支不能由终端读数选择）。** 若反馈方程改为非线性 $x=F(x)+b$，而同一终端读数可以来自多个稳定或不稳定不动点，则必须把分支选择、稳定域或初态合同纳入边界；一个固定点读数不说明下一次闭环更新会落在哪个分支。

### 证明

两个不同不动点具有同一终端投影时，终端读数对分支不可区分；改变初态或注入可以使后续迭代进入不同吸引域。故分支信息不能由单次投影反推。证毕。

**AHH 256.4（稳定性层）。** 反馈全息不仅要记录“现在落在哪个点”，还要记录“离临界有多远、扰动沿回路放大多少、允许哪些分支”。固定点相同的关系体仍可能拥有完全不同的未来风险。

## 257. 延续等价要求解析子而不只是固定点

**定义 257.1（反馈延续响应）。** 给定基准反馈 $(A,b)$ 和允许的外部注入子空间 $U\subseteq\mathcal H$，定义

$$
\mathcal C_{A,b,U}(\delta)
=
x^*(A,b+\delta)-x^*(A,b),
\qquad
\delta\in U.
$$

在收缩反馈下，

$$
\mathcal C_{A,b,U}(\delta)=R_A\delta.
$$

称两个反馈边界对 $U$ 延续等价，若它们对每个 $\delta\in U$ 的延续响应和声明的终端效果都相同。

**定理 257.2（解析子是满注入合同下的最小线性边界）。** 若 $U=\mathcal H$，两个收缩反馈 $(A,b)$ 和 $(\bar A,\bar b)$ 对所有外部注入和所有线性终端效果延续等价，当且仅当

$$
\boxed{
x^*=\bar x^*,
\qquad
R_A=R_{\bar A}.
}
\tag{257.1}
$$

### 证明

若两式成立，对任意 $\delta$，

$$
x^*(A,b+\delta)-x^*
=
R_A\delta
=
R_{\bar A}\delta
=
x^*(\bar A,\bar b+\delta)-\bar x^*,
$$

故所有线性效果相同。

反之，取 $\delta=0$ 得 $x^*=\bar x^*$。延续等价再给出

$$
R_A\delta=R_{\bar A}\delta
\quad\forall\delta\in\mathcal H.
$$

两个线性算子在全部向量上相同，故 $R_A=R_{\bar A}$。证毕。

**推论 257.3（受限注入的接口商）。** 若 $U$ 是真子空间，则只需保存解析子在 $U$ 上的限制 $R_A|_U$；两个回路在 $U$ 上相同而在 $U^\perp$ 上不同，对该受限任务仍然延续等价。

### 证明

定义 257.1 只读取 $\delta\in U$，所以响应完全由 $R_A|_U$ 决定。若限制不同，取其差异向量即可被线性效果分离。证毕。

这给出反馈版的任务相对商：允许的未来注入族越大，必须保存的解析子方向越多；只保留当前固定点相当于把注入族错误地压成空集。

**AHH 257.4（反馈延续层）。** 最小闭环边界是固定点与允许注入方向上的解析子，而不是完整内部轨道。扩大未来控制会细分反馈接口商；删除控制方向则可能允许合法压缩。

## 258. AHH：闭环全息是带稳定余量的解析接口

**定义 258.1（闭环全息边界）。** 对允许的闭环关系体定义

$$
\boxed{
\eta_{\mathrm{fb}}
=
\left(
\text{接口延续商},
A,
R_A=(I-A)^{-1},
b,
x^*,
1-\|A\|,
\text{允许注入方向},
\text{分支与初态合同},
\text{迭代成本与停止规则}
\right).
}
\tag{258.1}
$$

其中稳定余量 $1-\|A\|$ 只在收缩合同下有意义；若反馈不满足收缩，必须改用声明的谱、分支或局部稳定性合同，不能把该数值硬套到非稳定模型。

**定理 258.2（闭环边界的充分性）。** 在有限维收缩反馈、明确注入子空间、明确终端效果和有限迭代合同下，两个关系体若具有相同的 $\eta_{\mathrm{fb}}$，则对每个允许的有限反馈续接给出相同的：

1. 固定点与截断响应；
2. 外部注入的延续响应；
3. 局部失配的闭环放大上界；
4. 稳定性、分支合法性和迭代资源证书。

### 证明

固定点和截断响应由定理 255.2，失配界由定理 255.3，注入响应由定理 257.2，稳定性和资源由稳定余量、分支合同及迭代字段共同决定。相同边界字段逐项给出相同结果。证毕。

**定理 258.3（删除闭环字段的不可充分性）。** 若不以等价信息替代而删除以下任一字段，则存在相同剩余摘要、不同反馈未来的关系体：

1. 删除回路解析子：由命题 256.1，同固定点而注入敏感度不同；
2. 删除稳定余量：由命题 256.2，固定点相同而截断和失配界发散速度不同；
3. 删除允许注入方向：由推论 257.3，受限任务相同但扩展方向不同；
4. 删除分支与初态合同：由推论 256.3，多不动点反馈可进入不同后继；
5. 删除迭代成本和停止规则：同一固定点数学上可达，但一个合同的资源不足以完成闭环。

### 证明

前四项分别由命题 256.1、命题 256.2、推论 257.3 和推论 256.3 给出。第五项取相同回路而改变每轮访问成本或最大迭代数；固定点不变，合法后继集合改变。证毕。

**AHH 258.4（闭环全息）。** 闭环全息的最小对象不是一个已经稳定的终端读数，而是一个带解析子和资源合同的反馈接口：

$$
\boxed{
\text{固定点}
+
\text{回路解析子}
+
\text{稳定余量}
+
\text{允许注入方向}
+
\text{分支与迭代合同}.
}
$$

**AHH 的核心是：反馈把“边界保存什么”变成“边界如何在未来再次作用于自身”。只有保存回路的解析响应、稳定域和可执行成本，局部关系体才有资格被当成一个可闭合、可继续的全息对象。**

**来源与边界 258.5。** 本批在有限维收缩线性反馈、有限注入方向、明确初态与分支合同、有限迭代成本和线性终端效果下，给出固定点解析子、闭环误差放大、同固定点反例、反馈延续等价和闭环全息 AHH。没有把收缩条件推广到非稳定反馈，没有把线性解析子冒称为一般非线性分岔理论，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 259. 观测矩阵与闭环可观测商

闭环解析子描述扰动如何返回接口；还需要知道接口究竟看见了哪些状态方向。在线性模型中，这由观测矩阵给出。

**定义 259.1（有限观测合同）。** 令 $\mathcal H=\mathbb R^d$，系统在固定动作下满足

$$
x_{t+1}=Ax_t,
\qquad
y_t=Cx_t,
$$

其中 $A:\mathcal H\to\mathcal H$、$C:\mathcal H\to\mathbb R^r$。前 $N$ 个输出由观测矩阵

$$
\mathcal O_N
=
\begin{pmatrix}
C\\
CA\\
\vdots\\
CA^{N-1}
\end{pmatrix}
$$

给出：

$$
\begin{pmatrix}
y_0\\y_1\\\vdots\\y_{N-1}
\end{pmatrix}
=
\mathcal O_Nx_0.
$$

定义 $N$ 步不可观测子空间

$$
\mathcal N_N=\ker\mathcal O_N.
$$

**定理 259.2（观测纤维判据）。** 两个初态 $x_0,x_0'$ 产生相同的前 $N$ 步记录，当且仅当

$$
\boxed{
x_0-x_0'\in\mathcal N_N.
}
\tag{259.1}
$$

因此前 $N$ 步记录能够唯一恢复初态，当且仅当

$$
\operatorname{rank}\mathcal O_N=d.
$$

### 证明

输出差为

$$
\begin{pmatrix}
y_0-y_0'\\
\vdots\\
y_{N-1}-y_{N-1}'
\end{pmatrix}
=
\mathcal O_N(x_0-x_0').
$$

它为零当且仅当差向量属于核。核为零等价于矩阵满列秩，正好等价于初态唯一恢复。证毕。

**推论 259.3（观测商）。** 对只允许前 $N$ 步固定动作的任务，状态边界可以压缩为商空间

$$
\mathcal H/\mathcal N_N.
$$

若未来动作会把 $\mathcal N_N$ 的方向映射到可观测方向，则这个商不能直接作为更大动作族的充分边界。

### 证明

定理 259.2 说明同一商类的状态具有相同当前记录。若某未来动作 $A_a$ 使 $CA_a\delta\ne0$，其中 $\delta\in\mathcal N_N$，则两状态在追加一步后产生不同输出，故旧商不再充分。证毕。

**AHH 259.4（观测商层）。** 测量记录保存的是状态的观测商，而不是自动保存完整状态。可观测商相对于动作合同定义；扩大允许控制会把原先隐藏的方向重新变成边界可见关系。

## 260. 输出反馈可以把隐藏方向重新暴露

**定义 260.1（动作索引的观测闭环）。** 对每个允许动作 $a$，令

$$
x_{t+1}=A_ax_t+B_au_t,
\qquad
y_t=C_ax_t,
\qquad
u_t=\pi_t(y_{\le t}).
$$

当前记录只给出输出历史和策略动作，不直接给出 $x_t$。对固定记录，状态差 $\delta$ 若满足所有已执行动作的观测矩阵核条件，则属于当前隐藏纤维。

**命题 260.2（隐藏方向的动作暴露反例）。** 取当前动作的

$$
A_0=I_2,
\qquad
C_0=\begin{pmatrix}1&0\end{pmatrix}.
$$

状态 $x=(0,0)^{\mathsf T}$ 与 $x'=(0,1)^{\mathsf T}$ 在当前动作下产生相同的任意长度输出零。若下一步允许动作 $a$ 具有

$$
A_a=
\begin{pmatrix}
1&1\\
0&1
\end{pmatrix},
\qquad
C_a=\begin{pmatrix}1&0\end{pmatrix},
$$

则下一次输出分别为 $0$ 与 $1$。

### 证明

当前 $A_0=I$ 且 $C_0x=C_0x'=0$，所以两状态记录完全相同。作用 $A_a$ 后，

$$
A_ax=(0,0)^{\mathsf T},
\qquad
A_ax'=(1,1)^{\mathsf T},
$$

再用 $C_a$ 即得不同输出。证毕。

**定理 260.3（输出反馈的延续充分条件）。** 令 $\mathcal N$ 是当前记录的状态差纤维。若对每个允许未来动作词 $w$ 和每个 $\delta\in\mathcal N$，其所有未来输出满足

$$
C_{w,t}A_{w,t-1}\cdots A_{w,0}\delta=0
\quad\text{对所有未来时刻 }t,
$$

则当前输出记录对所有该动作族的未来输出任务充分。若存在一条动作词和一个时刻使该式非零，则当前输出记录不具普适充分性。

### 证明

条件成立时，任意同一当前记录的两状态差在每个允许未来输出上都为零，所以未来输出只依赖当前记录纤维而不依赖纤维内代表元。反之，若某项非零，取该纤维内的两状态和该动作词，便得到不同未来输出，故当前记录不能决定未来任务。证毕。

**AHH 260.4（控制暴露层）。** “当前没有看见某个方向”不是“该方向对所有未来都不可见”。输出反馈边界必须保存隐藏纤维如何在允许动作下传播，以及哪些控制会把它送入观测通道。

## 261. 记录后的状态应是纤维而不是点估计

观测不充分时，观察者真正拥有的是与记录相容的一组状态。把这组状态压成一个点，可能丢掉下一次反馈所需的分支。

**定义 261.1（确定性记录纤维递归）。** 令 $\mathcal B_t\subseteq\mathcal H$ 是第 $t$ 轮记录后当前状态的相容集合。执行动作 $a_t$ 并取得输出 $y_{t+1}$ 后，定义

$$
\boxed{
\mathcal B_{t+1}
=
A_{a_t}\mathcal B_t
\cap
C_{a_t}^{-1}(\{y_{t+1}\}).
}
\tag{261.1}
$$

初始 $\mathcal B_0$ 是来源合同允许的状态集合。

**定理 261.2（纤维递归的精确性）。** 在确定性线性动力学和无噪声记录合同下，$\mathcal B_t$ 恰好等于所有与完整记录 $y_1,\ldots,y_t$ 相容的当前状态；递归（261.1）不遗漏也不引入状态。

### 证明

归纳于 $t$。$t=0$ 时结论由定义成立。假定 $\mathcal B_t$ 等于所有相容当前状态。下一状态必须形如 $A_{a_t}x$，其中 $x\in\mathcal B_t$，并且必须满足观测方程 $C_{a_t}A_{a_t}x=y_{t+1}$；这正是（261.1）的交集。反之，交集中的每个状态由某个相容前态产生，并满足新记录，所以相容性保持。证毕。

**推论 261.3（纤维直径的传播界）。** 对任意范数，

$$
\operatorname{diam}(\mathcal B_{t+1})
\le
\|A_{a_t}\|\operatorname{diam}(\mathcal B_t).
$$

### 证明

交集不会增加直径，而线性映射 $A_{a_t}$ 至多按其算子范数放大直径。证毕。

**命题 261.4（点估计不能替代观测纤维）。** 取 $A_0=I_2$、$C_0=(1,0)$，当前记录为零。点估计可以选择 $(0,0)$，但相容纤维还包含 $(0,1)$；在命题 260.2 的未来动作 $a$ 下，两者产生不同下一输出。因此任何只保存点估计的边界都不能对该动作族给出 sound 的未来证书。

### 证明

两状态当前记录相同，且都属于 $\mathcal B_0$；命题 260.2 已证明未来动作将它们分离。点估计丢掉了纤维内另一状态，故其未来预测至少错于其中一个真实来源。证毕。

**AHH 261.5（纤维状态层）。** 观测后的“状态”在不充分边界中是一个记录纤维及其传播规则。点估计只有在纤维已经是单点，或所有允许续接在纤维上恒等时，才可代替完整边界。

## 262. AHH：观测反馈全息是商、纤维与控制作用的联合

**定义 262.1（观测反馈边界）。** 对允许动作族定义

$$
\boxed{
\eta_{\mathrm{obsfb}}
=
\left(
\text{观测商 } \mathcal H/\mathcal N,
\{\mathcal B_t\},
\{A_a,B_a,C_a\},
\text{隐藏纤维的未来暴露图},
\text{输出记录合同},
\text{控制支持},
\text{反馈稳定与资源合同}
\right).
}
\tag{262.1}
$$

观测商说明当前读数合并了哪些状态，纤维递归说明记录如何更新不确定性，未来暴露图说明允许控制是否能把隐藏方向送入输出，反馈字段说明这些更新是否稳定且可执行。

**定理 262.2（观测反馈边界的充分性）。** 在有限维线性系统、有限动作族、确定性记录或已声明噪声合同、有限反馈 horizon 和明确终端效果下，若两个关系体具有相同的 $\eta_{\mathrm{obsfb}}$，则对每个允许的反馈策略给出相同的：

1. 当前观测等价类；
2. 记录后的相容纤维递归；
3. 未来输出可识别性；
4. 反馈稳定性与资源证书。

### 证明

当前等价类由定理 259.2，纤维递归由定理 261.2，未来输出可识别性由定理 260.3，稳定性和资源由闭环字段与控制支持决定。边界字段逐项相同，故四类结果相同。证毕。

**定理 262.3（删除观测反馈字段的不可充分性）。** 若不以等价信息替代而删除以下任一层，则存在相同剩余摘要、不同反馈未来的关系体：

1. 删除观测商：当前记录无法确定哪些状态已被合并；
2. 删除纤维递归：相同当前读数的点估计会错误预测下一反馈；
3. 删除未来暴露图：命题 260.2 中当前隐藏方向可被下一动作分离；
4. 删除输出记录合同：同一系统矩阵在不同噪声或记录权限下具有不同可识别性；
5. 删除反馈稳定与资源合同：数学上可观测的路径可能无法在声明预算内执行。

### 证明

前两项分别由定理 259.2 与命题 261.4 给出，第三项由命题 260.2，第四项取相同 $A,C$ 而改变记录噪声或读取权限，第五项取相同观测矩阵而令访问成本超过资源预算。每项都保留其余字段而改变被删除层，故剩余边界不能普适决定未来。证毕。

**AHH 262.4（观测反馈全息）。** 反馈中的全息边界不是一张读数表，而是

$$
\boxed{
\text{观测商}
+
\text{记录纤维}
+
\text{隐藏方向的控制暴露}
+
\text{输出记录合同}
+
\text{稳定与资源}.
}
$$

**AHH 的核心是：观测记录只把内部状态压成一个当前纤维；反馈控制会继续作用在这条纤维上，并可能把隐藏方向重新变成可见事件。因而“粒子式记录”之后的下一次事件，取决于纤维怎样被控制传播，而不只取决于当前读数。**

**来源与边界 262.5。** 本批在有限维线性系统、有限动作族、确定性无噪声或已声明记录合同、有限反馈 horizon 和有限资源下，给出观测矩阵核判据、隐藏方向暴露反例、相容纤维递归、点估计失效和观测反馈全息 AHH。没有把线性可观测性推广到未知噪声或一般非线性观测器，没有把点估计解释为无损状态，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 263. 可检测性：不可观测不等于不可稳定

观测反馈边界还有一个重要分层：有些内部方向无法由输出恢复，但它们会自行衰减，因此不必被精确重建；另一些隐藏方向会增长，任何只依赖该输出的反馈都无法从读数中发现它。

**定义 263.1（固定离散 LTI 合同）。** 本节固定有限维状态空间 \(\mathcal H\) 以及不随时间切换的离散系统

$$
x_{t+1}=Ax_t+Bu_t,
\qquad
y_t=Cx_t.
$$

状态空间已经包含该反馈任务所需的记忆；若记忆被遗漏，下面的边界就不是充分边界。定义无限时不可观测子空间

$$
\mathcal N
=\bigcap_{t\ge0}\ker(CA^t).
$$

它对 \(A\) 不变。称 \((A,C)\) **可检测**，若限制算子 \(A|_{\mathcal N}\) 的谱半径满足

$$
\rho(A|_{\mathcal N})<1.
$$

这里不讨论任意切换系统；若动作会切换 \(A\) 或 \(C\)，必须另行定义相应的共同不变子空间和稳定合同。

**定理 263.2（隐藏稳定模式的衰减）。** 若 \((A,C)\) 可检测，则对任意初始隐藏差 \(\delta\in\mathcal N\)，存在常数 \(M>0\) 和 \(0<r<1\)，使

$$
\boxed{
\|A^t\delta\|
\le
Mr^t\|\delta\|
\quad(t\ge0).
}
\tag{263.1}
$$

对同一输入序列，两个初态的输出差始终严格为零：

$$
CA^t\delta=0\quad(t\ge0).
$$

可检测性约束的是隐藏状态差和估计误差的长期尾，而不是把一个本来为零的输出差变成非零小量。

### 证明

\(\mathcal N\) 对 \(A\) 不变，所以 \(A|_{\mathcal N}\) 是有限维线性算子。谱半径小于一时，取任意 \(\rho(A|_{\mathcal N})<r<1\)，有限维谱半径估计或 Jordan 分解给出某个 \(M\) 使

$$
\|(A|_{\mathcal N})^t\|\le Mr^t.
$$

对 \(\delta\in\mathcal N\) 应用该界即得（263.1）；而 \(CA^t\delta=0\) 是 \(\mathcal N\) 的定义。若 \(\mathcal N=\{0\}\)，不等式对唯一的隐藏差平凡成立。证毕。

若 \(\rho(A|_{\mathcal N})\ge1\)，同一输出记录中可以存在不衰减或增长的隐藏未来；这时“只保存观测商”不能成为稳定性边界。若任务只要求有限输出序列，隐藏方向对该固定合同的输出影响仍是严格零；若任务还要求状态代价、估计误差或未来会改变观测接口，则必须保留相应的隐藏谱和切换条件。

**推论 263.3（可检测商的任务条件）。** 在固定 LTI 合同和同一输入序列下，\(\mathcal H/\mathcal N\) 足以表示输出等价类；当隐藏限制满足（263.1）时，还可给出隐藏状态差的显式衰减尾。若任务要求精确重建当前状态，仍需更强的完全可观测条件 \(\mathcal N=\{0\}\)。

### 证明

商空间消除了产生相同全部输出的隐藏差；（263.1）给出未被消除的内部差异的长期界。两种目标的量词不同：输出等价不等于状态相等。证毕。

**AHH 263.4（可检测层）。** 全息边界必须区分“隐藏但稳定”和“隐藏且会放大”。不可观测商可以服务于固定输出任务，但隐藏谱余量仍决定内部稳定、估计误差和接口改变后的风险；不能把严格零输出差冒称为完整状态恢复。

## 264. 观测器—控制器分离与联合稳定性

**定义 264.1（线性输出反馈）。** 在同一个固定 LTI 模型上选取状态反馈增益 \(K\) 和观测器增益 \(L\)：

$$
u_t=K\hat x_t,
$$

$$
\hat x_{t+1}
=A\hat x_t+Bu_t+L(y_t-C\hat x_t).
$$

令估计误差 \(e_t=x_t-\hat x_t\)。

**定理 264.2（名义分离结构）。** 若

$$
\rho(A+BK)<1,
\qquad
\rho(A-LC)<1,
$$

则名义输出反馈闭环渐近稳定。其联合状态满足块上三角递推

$$
\begin{pmatrix}
x_{t+1}\\e_{t+1}
\end{pmatrix}
=
\begin{pmatrix}
A+BK&-BK\\
0&A-LC
\end{pmatrix}
\begin{pmatrix}
x_t\\e_t
\end{pmatrix}.
$$

### 证明

由 \(u_t=K(x_t-e_t)\)，

$$
x_{t+1}
=(A+BK)x_t-BKe_t.
$$

观测器误差满足

$$
\begin{aligned}
e_{t+1}
&=x_{t+1}-\hat x_{t+1}\\
&=(A-LC)e_t.
\end{aligned}
$$

故联合矩阵为所示块上三角矩阵；其特征值是两个对角块特征值的并集。两个谱半径都小于一，所以联合系统渐近稳定。有限维性还给出某个 \(M>0\)、\(r<1\) 使联合范数按 \(Mr^t\) 衰减。证毕。

**推论 264.3（分离不删除 provenance）。** 定理 264.2 只在同一已声明的 \(A,B,C,K,L\)、每一步都取得 \(y_t\) 并执行 \(u_t\) 的精确记录合同下成立。若允许模型失配、动作切换、输出噪声或资源限制，观测器和控制器的误差、稳定余量和共同来源必须重新进入联合边界。

### 证明

块三角分解依赖同一名义矩阵和同一误差更新。改变任一矩阵或记录合同就改变对角块、非对角耦合或更新次数，不能由名义谱半径自动推出新闭环的稳定性。证毕。

**AHH 264.4（分离层）。** 观测器和控制器在名义固定 LTI 模型中可以分开设计，但它们在真实关系中共享记录、模型 provenance 和资源合同。分离是一个有条件的结构定理，不是删除联合边界的许可。

## 265. 可检测性与分离定理的失效边界

**命题 265.1（不可检测隐藏增长模式）。** 取

$$
A=
\begin{pmatrix}
1.1&0\\
0&0.5
\end{pmatrix},
\qquad
C=\begin{pmatrix}0&1\end{pmatrix},
\qquad
B=\begin{pmatrix}0\\1\end{pmatrix}.
$$

第一坐标完全不可观测且不受控制输入影响。两个初态只在第一坐标上不同，会产生相同的全部输出，但差异按 \(1.1^t\) 增长。

### 证明

对任意 \(t\)，

$$
CA^t=\begin{pmatrix}0&0.5^t\end{pmatrix},
$$

所以第一坐标属于 \(\mathcal N\)。控制项 \(Bu_t\) 的第一坐标恒为零；在相同输出反馈下两条轨迹使用相同输入，隐藏差异为 \(1.1^t\delta_1\)，不会被输出或控制消除。证毕。

**命题 265.2（名义分离不能支付模型失配）。** 在一维名义系统中取

$$
A=0.99,\qquad B=C=1,\qquad K=-0.98,\qquad L=0.98.
$$

名义闭环和观测误差因子都为 \(0.01\)：

$$
A+BK=A-LC=0.01.
$$

现在真实植物系数变为 \(A'=2\)，但观测器仍使用名义的 \(A=0.99\)，而 \(B,C,K,L\) 保持不变。真实的 \((x,e)\) 联合矩阵不是两个独立的 \(1.02\) 对角块，而是

$$
J(A')=
\begin{pmatrix}
A'+BK&-BK\\
A'-A&A-LC
\end{pmatrix}
=
\begin{pmatrix}
1.02&0.98\\
1.01&0.01
\end{pmatrix}.
$$

该矩阵有一个大于一的特征值，名义分离证书因模型失配而失效。

### 证明

真实植物满足 \(x_{t+1}=A'x_t+Bu_t\)，观测器递推仍以名义 \(A\) 计算。代入 \(u_t=K(x_t-e_t)\) 得

$$
x_{t+1}=(A'+BK)x_t-BKe_t,
$$

而直接相减得到

$$
e_{t+1}=(A'-A)x_t+(A-LC)e_t.
$$

所以得到 \(J(A')\)。其特征多项式为

$$
p(\lambda)=\lambda^2-1.03\lambda-0.9796.
$$

有 \(p(1)=-1.0096<0\)、\(p(2)=0.9604>0\)，故介于一与二之间存在实特征值，联合系统不渐近稳定。若观测器也同步改用 \(A'=2\)，则这是另一个匹配模型，不能把它与当前失配合同混为一谈。证毕。

**推论 265.3（资源边界的失效）。** 即使 \((A,C)\) 可检测且名义分离成立，若输出记录带宽、观测器更新次数或控制执行次数不足以实现声明的 \(L,K\)，则数学稳定性不等于该资源合同下的合法后继。

### 证明

分离定理的递推假定每一步都取得 \(y_t\) 并执行 \(u_t\)。删除其中任一实际更新会改变误差递推，故原稳定结论不适用；合法后继还取决于停止规则和记录是否被保留。证毕。

**AHH 265.4（鲁棒可检测层）。** 稳定隐藏模式、名义分离、模型失配下的联合稳定和实际可执行性是四个不同字段。把它们合并成一个“系统稳定”标签，会掩盖不可检测增长、下三角失配耦合和记录资源不足。

## 266. AHH：观测器—控制器边界的联合稳定几何

**定义 266.1（可检测反馈全息边界）。** 对一个固定 LTI 反馈合同，定义

$$
\boxed{
\eta_{\mathrm{detect}}
=
\left(
A,B,C,
\mathcal N,\ A|_{\mathcal N},
\mathcal H/\mathcal N,
K,L,
\mathfrak M,\ \mathfrak R,\ \mathfrak U,
\text{记录与停止规则}
\right).
}
\tag{266.1}
$$

其中 \(\mathfrak M\) 是模型失配集合及其“观测器是否同步更新”的实施规则，\(\mathfrak R\) 是输出记录合同，\(\mathfrak U\) 是执行次数、带宽和 horizon 等资源合同。对纯名义合同，\(\mathfrak M=\{A\}\)；对真实失配，若观测器继续使用名义模型，则每个 \(\widetilde A\in\mathfrak M\) 的联合矩阵为

$$
J(\widetilde A)
=
\begin{pmatrix}
\widetilde A+BK&-BK\\
\widetilde A-A&A-LC
\end{pmatrix}.
$$

商与隐藏限制描述固定观测接口下的关系分层；增益、失配集合和记录资源描述实际反馈如何继续。

**定理 266.2（条件性的可检测反馈边界充分性）。** 在固定有限维 LTI 模型、固定输出反馈实现、有限 horizon 和已声明记录/执行合同下，若两个关系体具有相同的 \(\eta_{\mathrm{detect}}\)，则它们对该合同产生相同的输出递推、相同的观测器—控制器联合递推和相同的停止后继。名义稳定性由

$$
\rho(A+BK)<1,
\qquad
\rho(A-LC)<1
$$

给出；若还要求对失配盒作统一稳定承诺，则必须另外满足某个 \(M_* >0\)、\(0<r_*<1\)，使

$$
\|J(\widetilde A)^t\|\le M_*r_*^t
\quad
(\widetilde A\in\mathfrak M,\ t\ge0).
$$

### 证明

相同的 \(A,B,C,K,L\) 和相同记录/执行映射逐步给出相同的名义递推；\(\mathfrak M\) 及其实施规则逐一给出失配分支 \(J(\widetilde A)\)，停止规则给出相同的合法后继。名义谱条件由定理 264.2 给出；失配盒的统一界是额外的联合矩阵条件，不能由两个名义对角块的谱半径单独推出。证毕。

**定理 266.3（约化摘要的明确不可充分性）。** 下面的结论针对列明的约化摘要；它们不声称一个仍完整保留 \(A,B,C\) 的摘要还需要把由其可计算的隐藏谱另存一份。

1. **只保留当前输出算子而删除隐藏谱。** 取
   $$
   A_s=\operatorname{diag}(0.5,0.5),\qquad
   A_u=\operatorname{diag}(1.1,0.5),\qquad
   C=(0,1),\qquad B=(0,1)^{\mathsf T}.
   $$
   两者的所有 \(CA^t\) 都相同，初态只在第一坐标上不同的输出记录也相同；隐藏谱却分别为 \(0.5\) 与 \(1.1\)。
2. **删除增益而保留植物和记录合同。** 在标量 \(A=0.5,B=C=1,L=0.2\) 下，\(K=0\) 与 \(K=2\) 给出控制闭环因子 \(0.5\) 与 \(2.5\)，所以同一观测商可以对应不同的联合稳定性。
3. **删除失配盒。** 命题 265.2 的名义字段完全相同；真实 \(A'=2\) 与真实 \(A'=A\) 对应不同的联合稳定性，单看名义分离证书无法决定后者。
4. **删除共同记录合同。** 同一 \(A,B,C,K,L\) 在“每一步可取得 \(y_t\)”和“只在偶数步可取得 \(y_t\)”两种合同下具有不同误差递推与合法后继。
5. **删除执行资源。** 同一数学稳定系统在一个允许无限 horizon 的合同和一个只允许零次或一次更新的预算合同下，具有不同的可执行后继，即使它们共享所有数学矩阵。

### 证明

第 1 项是显式模型对，说明输出算子本身不含隐藏谱；第 2 项直接代入 \(A+BK\)；第 3 项由命题 265.2 的联合矩阵；第 4、5 项由递推所需的记录与执行次数定义。每项都只声称相应约化摘要不充分，并保留“若完整矩阵仍在摘要中，某些字段可由它推导”的限定。证毕。

**AHH 266.4（可检测反馈全息）。** 观测反馈的完整边界是一个联合稳定几何：

$$
\boxed{
\text{可观测商}
+
\text{隐藏谱余量}
+
\text{观测器—控制器分离结构}
+
\text{失配下的联合矩阵}
+
\text{共同记录与资源}
}.
$$

**AHH 的核心是：一个粒子式记录可以足以稳定地继续，也可以把增长的隐藏模式藏在读数之外；决定二者的不是“有没有点击”，而是隐藏纤维的谱、观测器—控制器联合回路以及它们真实可执行的记录合同。**

**来源与边界 266.5。** 本批在固定有限维离散线性系统、固定反馈实现、确定性或已声明记录合同、可检测隐藏模式、名义分离和有限资源 horizon 下，给出可检测性衰减界、观测器—控制器分离、不可检测增长反例、带下三角耦合的模型失配反例，以及条件性的可检测反馈全息边界。这里使用的是标准线性系统结论与本卷关系边界的组合；没有主张这些组合本身为文献外原创定理，也没有把分离定理推广到未知噪声、约束控制或一般非线性系统。本批没有新增 Lean、消化、coverage 或 freeze 内容，仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 267. 严格耗散证书：可以组合的不是状态照片，而是接口能量账

前面的分离定理保存的是矩阵和误差递推。本节改问一个更适合组合的问题：当两个关系体通过端口连接时，是否可以只交换一份可加的稳定性证书，而不交换全部内部轨迹？

**定义 267.1（严格被动离散模块）。** 对于模块

$$
x_i^+=F_i(x_i,u_i),
\qquad
y_i=G_i(x_i,u_i),
$$

称一个连续存储函数 $V_i$ 和常数 $a_i>0$、$\varepsilon_i>0$ 构成严格被动证书，若对所有合法状态和输入都有

$$
 a_i\|x_i\|^2\le V_i(x_i),
$$

以及

$$
\boxed{
V_i(x_i^+)-V_i(x_i)
\le
u_i^{\mathsf T}y_i-\varepsilon_i\|x_i\|^2.
}
\tag{267.1}
$$

本节只讨论两个端口的维数已经匹配、互连规则固定且每一步都实际执行的有限维系统。

**定理 267.2（反对称互连的存储组合）。** 若两个模块具有（267.1），并按

$$
u_1=y_2,
\qquad
u_2=-y_1
$$

互连，则总存储 $V=V_1+V_2$ 满足

$$
\boxed{
V^+-V
\le
-\varepsilon_1\|x_1\|^2
-\varepsilon_2\|x_2\|^2.
}
\tag{267.2}
$$

特别地，零初始外部注入时，状态平方和有限：

$$
\sum_{t=0}^{\infty}
\left(
\varepsilon_1\|x_{1,t}\|^2
+
\varepsilon_2\|x_{2,t}\|^2
\right)
\le V(x_{1,0},x_{2,0}),
$$

从而 $x_{1,t}\to0$、$x_{2,t}\to0$。

### 证明

将两个不等式相加，交叉项为

$$
u_1^{\mathsf T}y_1+u_2^{\mathsf T}y_2
=
y_2^{\mathsf T}y_1-y_1^{\mathsf T}y_2=0.
$$

于是得到（267.2）。对 $t=0,\ldots,N$ 求和并利用 $V\ge0$，再令 $N\to\infty$，得到平方和界。平方可和的有限维序列范数趋于零，故两条状态轨迹都趋于零。证毕。

**推论 267.3（端口证书的全息意义）。** 对这个固定互连合同，外部续接只需读取端口方向、存储上下界和严格耗散余量，就可以组合出稳定性与能量预算；它不需要读取每个内部时刻的完整状态。若改变互连符号、端口维数或停止规则，原证书不能自动迁移。

### 证明

（267.2）只使用每个模块的存储差分、端口配对和互连规则。改变其中任一项就改变交叉项是否抵消，故原不等式不再是同一合同下的证明。证毕。

**AHH 267.4（耗散组合层）。** 一个可组合的边界不是终端读数的副本，而是一份能在合法互连中相加的存储账。它压缩了内部轨迹，却保留了外部连接仍会消费的能量方向和稳定余量。

## 268. 小增益：有限观测接口上的反馈放大因子

严格被动性不是唯一可组合证书。若每个模块只给出输入到输出的有限增益，也能在环增益低于一时得到统一的外部界；但这份界只覆盖声明的端口响应，不自动覆盖未接出的内部模式。

**定义 268.1（有限 horizon 的零态增益）。** 对模块 $i$ 和 horizon $N$，置

$$
\|z\|_{2,N}^2=\sum_{t=0}^{N}\|z_t\|^2.
$$

称 $\gamma_i\ge0$ 是零初态有限增益，若对所有长度不超过 $N$ 的输入序列都有

$$
\|y_i\|_{2,N}\le\gamma_i\|u_i\|_{2,N}.
$$

这里的初态被固定为零；非零初态必须另列为独立响应项。

**定理 268.2（正反馈小增益界）。** 两个模块按

$$
u_1=d_1+y_2,
\qquad
u_2=d_2+y_1
$$

连接。以下只对该互连存在的合法有限 horizon 轨迹作结论；增益不等式本身不替代因果性和唯一后继的适定性条件。令 $g=\gamma_1\gamma_2<1$。则任意有限 horizon 都有

$$
\boxed{
\|y_1\|_{2,N}
\le
\frac{\gamma_1\|d_1\|_{2,N}+g\|d_2\|_{2,N}}{1-g},
}
\tag{268.1}
$$

以及

$$
\boxed{
\|y_2\|_{2,N}
\le
\frac{g\|d_1\|_{2,N}+\gamma_2\|d_2\|_{2,N}}{1-g}.
}
\tag{268.2}
$$

### 证明

记 $Y_i=\|y_i\|_{2,N}$、$D_i=\|d_i\|_{2,N}$。三角不等式和增益定义给出

$$
Y_1\le\gamma_1(D_1+Y_2),
\qquad
Y_2\le\gamma_2(D_2+Y_1).
$$

代入第二式到第一式，得到

$$
(1-g)Y_1\le\gamma_1D_1+gD_2,
$$

这就是（268.1）。交换指标得到（268.2）。证毕。

**推论 268.3（裕量的放大）。** 小增益界中的 $1-g$ 是外部记录、扰动和初态响应的共同放大分母。仅知道 $g<1$ 而不保存其裕量，不能比较两个接口在有限资源和有限精度下的可续接性。

**命题 268.4（端口增益不含隐藏稳定性）。** 取两个标量模块，均有端口输出恒为零：

$$
\mathsf M_s:\ z_{t+1}=0.5z_t,\ y_t=0,
\qquad
\mathsf M_u:\ z_{t+1}=1.1z_t,\ y_t=0.
$$

两者的零态输入—输出增益都为 $0$，但第一个内部状态衰减，第二个内部状态增长。

### 证明

对任意输入，输出序列恒为零，所以两者的端口增益相同。直接迭代内部状态得到 $z_t=0.5^tz_0$ 与 $z_t=1.1^tz_0$。证毕。

**AHH 268.5（小增益层）。** 小增益边界保存的是外部接口的反馈放大，而不是整个关系体的稳定性。只有把增益裕量与隐藏模式的稳定合同同时保留，端口上的粒子式记录才不会掩盖内部的增长方向。

## 269. 记录误差：边界精度会沿反馈余量被放大

实际记录和执行通常只给出近似的端口值。把记录误差写成反馈中的附加输入，可以把“观测精度”直接接到小增益余量，而不把它误读成新的物理噪声来源。

**定义 269.1（误差化记录合同）。** 在定理 268.2 的互连上加入记录或执行误差 $\nu_1,\nu_2$：

$$
\tilde u_1=d_1+y_2+\nu_1,
\qquad
\tilde u_2=d_2+y_1+\nu_2,
$$

并假定

$$
\|\nu_i\|_{2,N}\le\delta_i.
$$

$\delta_i$ 可以来自量化、丢包后的保守包络或执行器分辨率；它不是由数学增益定义自动决定的参数。

**定理 269.2（记录误差的小增益传播）。** 在 $g=\gamma_1\gamma_2<1$ 时，输出满足

$$
\boxed{
\|y_1\|_{2,N}
\le
\frac{\gamma_1(D_1+\delta_1)+g(D_2+\delta_2)}{1-g},
}
\tag{269.1}
$$

$$
\boxed{
\|y_2\|_{2,N}
\le
\frac{g(D_1+\delta_1)+\gamma_2(D_2+\delta_2)}{1-g},
}
\tag{269.2}
$$

其中 $D_i=\|d_i\|_{2,N}$。

### 证明

将 $d_i+\nu_i$ 视为定理 268.2 的新外部输入。由三角不等式，新的输入范数分别不超过 $D_i+\delta_i$；代入（268.1）和（268.2）即得。证毕。

**例 269.3（同一记录精度在临界反馈中的不同后果）。** 取两个静态标量模块

$$
 y_i=\gamma u_i,
\qquad 0<\gamma<1,
$$

并使用正反馈。令 $g=\gamma^2$，$d_1=d_2=\nu_2=0$，而 $\nu_1=\delta$。则精确解为

$$
\boxed{
 y_1=\frac{\gamma\delta}{1-g},
\qquad
 y_2=\frac{g\delta}{1-g}.
}
\tag{269.3}
$$

所以同一个记录误差 $\delta$ 在 $g=0.2$ 和 $g=0.99$ 时具有完全不同的外部后果；误差本身没有改变，改变的是剩余反馈裕量。

### 证明

由 $y_1=\gamma(y_2+\delta)$、$y_2=\gamma y_1$，消去 $y_2$ 得

$$
(1-\gamma^2)y_1=\gamma\delta.
$$

再代回得到 $y_2=\gamma y_1$，即（269.3）。证毕。

**推论 269.4（记录资源是稳定边界的一部分）。** 若任务要求输出误差不超过 $\tau$，则必须同时声明 $\delta_i$ 与反馈裕量 $1-g$，并验证（269.1）—（269.2）给出的上界不超过 $\tau$。只保存一次点击或一次端口读数而删除其精度合同，不能决定后续是否仍满足任务。

### 证明

（269.1）—（269.2）中的误差项依赖 $\delta_i/(1-g)$。删除任一参数都不能计算该任务不等式。证毕。

**AHH 269.5（精度—裕量层）。** 记录不是静态的“已知/未知”二值；在反馈关系中，有限精度会沿剩余裕量传播。边界必须同时保存记录误差包络、互连方向和增益裕量，才能判断一个局域事件是否仍能安全地成为下一阶段输入。

## 270. AHH：可组合稳定边界的最小职责分层

**定义 270.1（可组合反馈证书边界）。** 对一个固定端口互连合同，定义

$$
\boxed{
\eta_{\mathrm{comp}}
=
\left(
\text{端口与互连方向},
\text{存储函数与严格耗散余量},
\text{有限增益与小增益裕量},
\text{隐藏状态稳定合同},
\text{记录/执行误差包络},
\text{初态响应},
\text{合法分支、资源与停止规则}
\right).
}
\tag{270.1}
$$

各字段并不宣称彼此独立：在一个给定的完整状态空间和模型中，有些字段可以由其他字段推导；定义它们是为了明确外部续接实际需要哪些证明义务。

**定理 270.2（可组合证书的条件充分性）。** 在有限维、固定互连、有限 horizon、每个记录分支都有合法唯一后继且记录合同已声明的条件下：

1. 若两个模块各有定理 267.2 的严格被动证书，并使用反对称互连，则总存储给出状态平方和界；
2. 若两个模块具有定理 268.1 的零态有限增益、$g<1$，且记录误差满足定义 269.1，则（269.1）—（269.2）给出全部有限 horizon 的端口误差界；
3. 若边界还附有每个模块的隐藏状态稳定合同，则端口界与隐藏状态界可以同时作为后续合法性判据。

因此，满足同一个 $\eta_{\mathrm{comp}}$ 的两个实现，对这组已声明的互连、误差和资源任务给出相同的证书结论。

### 证明

第 1 项是定理 267.2，第 2 项是定理 269.2。第 3 项只是把独立声明的隐藏状态界与端口界按同一任务合取；它不从端口增益反推出隐藏稳定。固定互连、记录和停止规则保证这些不等式作用在同一个实际后继上。证毕。

**定理 270.3（约化边界的明确失效）。** 对以下约化摘要，存在具有相同其余摘要而任务结论不同的实现对：

1. 删除互连方向：同一对端口增益在反对称互连下交叉项抵消，在正反馈下出现 $1-g$ 分母；在静态实例 $y_i=u_i$ 中，$g=1$ 的正反馈方程甚至不适定。
2. 删除隐藏稳定合同：命题 268.4 的两个模块端口增益相同，但内部状态分别衰减和增长。
3. 删除小增益裕量：固定记录误差 $\delta$，例 269.3 中 $g=0.2$ 与 $g=0.99$ 的输出放大不同。
4. 删除记录误差包络：同一物理模块和同一 $g<1$，精确记录 $\delta=0$ 与有限精度记录 $\delta>0$ 的任务误差结论不同。
5. 删除初态响应：零态增益相同的模块，可以从不同非零初态产生不同的第一阶段输出。

### 证明

第 1 项由端口交叉项和小增益方程直接给出；第 2 项由命题 268.4；第 3、4 项由（269.3）及（269.1）—（269.2）；第 5 项是零态增益定义对初态的明确排除。每项只针对所列约化摘要作不可充分性断言；若完整动力学仍被保留，某些字段当然可以由它计算出来。证毕。

**AHH 270.4（可组合稳定全息）。** 关系体的可组合全息不是把内部状态压成一个终端数，而是保存一份能被未来互连消费的证书：

$$
\boxed{
\text{可抵消的端口方向}
+
\text{可组合的存储/增益}
+
\text{隐藏状态尾}
+
\text{反馈裕量}
+
\text{记录精度与资源}
}.
$$

**真正的 AHH 时刻是：内部轨迹可以被压缩，证明义务却不能被压缩成一个读数。能够穿过边界继续传播的，不是“系统现在是多少”，而是“下一次合法互连最多会消费多少稳定预算，以及哪些隐藏方向仍可能增长”。**

**来源与边界 270.5。** 本批在有限维离散模块、固定端口互连、有限 horizon、零态有限增益、严格耗散证书和有界记录误差合同下，给出耗散组合、小增益界、记录误差放大和可组合反馈全息。严格被动性、小增益和有限 horizon 的推导是标准系统理论工具在本卷关系边界语境中的组合；没有把端口增益推广成内部稳定性，没有覆盖未知噪声、任意切换、约束控制或一般非线性系统，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 271. 仿射响应证书：串联关系的边界代数

严格耗散证书适合证明能量下降，小增益证书适合证明反馈放大。本节抽取两者共同的一个接口形状：有限 horizon 上，输出误差由一个固定余项和一个输入增益控制。

**定义 271.1（仿射接口合同）。** 在固定的输入、输出范数和 horizon 下，模块 $M$ 具有合同

$$
\mathcal C(M)=(\alpha,\gamma,c),
\qquad
\alpha,\gamma,c\ge0,
$$

若对每个声明的合法输入 $u$，其输出满足

$$
\boxed{
\|y\|\le\alpha+\gamma\|u\|,
}
\tag{271.1}
$$

并消耗资源成本不超过 $c$。余项 $\alpha$ 可以包含初态响应、记录误差或已声明的外部残差；它不被解释成一个额外的内部状态。

**定理 271.2（串联证书律）。** 若 $M_1$、$M_2$ 的合同分别为

$$
(\alpha_1,\gamma_1,c_1),
\qquad
(\alpha_2,\gamma_2,c_2),
$$

且 $M_1$ 的输出作为 $M_2$ 的输入，那么串联模块 $M_2\circ M_1$ 具有合同

$$
\boxed{
\mathcal C(M_2\circ M_1)
=
(\alpha_2+\gamma_2\alpha_1,
\gamma_2\gamma_1,
 c_1+c_2).
}
\tag{271.2}
$$

### 证明

由（271.1），

$$
\|y_1\|\le\alpha_1+\gamma_1\|u\|,
$$

以及

$$
\|y_2\|\le\alpha_2+\gamma_2\|y_1\|.
$$

代入第一式得到

$$
\|y_2\|
\le
\alpha_2+\gamma_2\alpha_1+\gamma_2\gamma_1\|u\|.
$$

独立执行的资源成本相加，得到（271.2）。证毕。

**推论 271.3（证书形成带资源的幺半群）。** 置

$$
(\alpha_2,\gamma_2,c_2)\odot(\alpha_1,\gamma_1,c_1)
=
(\alpha_2+\gamma_2\alpha_1,
\gamma_2\gamma_1,
 c_1+c_2).
$$

则该运算结合，单位元为 $(0,1,0)$。若总预算为 $B$，一条串联链合法的必要资源条件是

$$
\sum_i c_i\le B.
$$

### 证明

对三个合同直接展开余项：

$$
\alpha_3+\gamma_3(\alpha_2+\gamma_2\alpha_1)
=
(\alpha_3+\gamma_3\alpha_2)+\gamma_3\gamma_2\alpha_1.
$$

增益是乘法、成本是加法，所以两种括号给出同一个三元组；单位元的代入也直接成立。预算条件来自成本加法。证毕。

**AHH 271.4（证书代数层）。** 一个边界可以保存“余项、增益、成本”三元组，而不保存每个内部时刻。这个压缩只有在范数、horizon、端口方向和资源计数都属于同一个合同族时才成立；改变其中任一项，就不再是同一个幺半群运算。

## 272. 并联组合：共同输入下不需要假设概率独立

并联关系常被误写成独立来源的乘积。本节只使用确定性的范数合同，说明共同输入下的并联边界如何组合，也说明它不需要虚构统计独立。

**定义 272.1（堆叠输出合同）。** 两个模块使用同一个输入 $u$，输出分别为 $y_1,y_2$。定义堆叠输出

$$
 y_\oplus=(y_1,y_2),
$$

并在输出空间使用平方和范数

$$
\|y_\oplus\|^2=\|y_1\|^2+\|y_2\|^2.
$$

假定模块合同为 $(\alpha_i,\gamma_i,c_i)$，并且两次执行使用同一输入记录和可加资源预算。

**定理 272.2（并联仿射证书）。** 堆叠输出具有合同

$$
\boxed{
\|y_\oplus\|
\le
\sqrt{\alpha_1^2+\alpha_2^2}
+
\sqrt{\gamma_1^2+\gamma_2^2}\,\|u\|,
}
\tag{272.1}
$$

资源成本为 $c_1+c_2$。

### 证明

由两个局部合同，

$$
\|y_\oplus\|
\le
\left((\alpha_1+\gamma_1\|u\|)^2
+(\alpha_2+\gamma_2\|u\|)^2\right)^{1/2}.
$$

把右侧看成二维向量

$$
(\alpha_1,\alpha_2)+\|u\|(\gamma_1,\gamma_2),
$$

应用 Minkowski 不等式得到（272.1）。成本按独立执行合同相加。证毕。

**推论 272.3（共同来源与统计独立的分离）。** 定理 272.2 不需要 $y_1,y_2$ 的概率独立，也不把两个边缘范数的乘积当作联合范数。若任务需要概率或相关函数的联合分布，还必须在边界中另列共同来源和联合记录字段。

### 证明

证明只使用同一输入下的逐轨迹范数不等式，没有使用概率空间上的乘积测度。联合统计任务的目标比堆叠范数更强，故不能由（272.1）自动推出。证毕。

**AHH 272.4（并联层）。** 并联全息保存的是共同输入下的联合误差预算，而不是把两个局部读数宣称为独立来源。边界的平方和组合可以压缩幅度信息；相关性、共同记录和概率任务仍是额外关系。

## 273. 事件调度：记录总数不决定隐藏误差

反馈边界还必须保存记录发生的时间位置。下面用一个带有未建模创新的标量误差递推，精确展示同样数量的记录如何给出不同的安全裕量。

**定义 273.1（重置型事件调度）。** 固定 $a>1$、创新上界 $\omega\ge0$ 和 horizon $T$。给定记录时刻集合

$$
S\subseteq\{0,1,\ldots,T-1\},
$$

定义估计误差递推

$$
 e_{t+1}
=
\begin{cases}
0,&t\in S,\\
 ae_t+w_t,&t\notin S,
\end{cases}
\qquad
|w_t|\le\omega.
$$

记录时刻把误差重置为零；没有记录时，隐藏误差按 $a$ 放大并接受一次创新。令 $h(S)$ 为 $S$ 的最长连续无记录段长度。

**定理 273.2（最大间隔误差界）。** 若 $|e_0|\le E_0$，则对每个 $t\le T$，

$$
\boxed{
|e_t|
\le
 a^{h(S)}E_0
+
\omega\frac{a^{h(S)}-1}{a-1}.
}
\tag{273.1}
$$

若某个无记录段长度为 $\ell$，并且该段开始时误差为零，选择同号极值创新 $w_t=\omega\operatorname{sgn}(e_{t})$（首项取正）可达到

$$
\boxed{
|e|=\omega\frac{a^{\ell}-1}{a-1}
}
\tag{273.2}
$$

因此，给定 $a$、$\omega$ 和容许误差 $\tau$，最大间隔而非记录总数决定最坏情况下的安全条件。

### 证明

在一个长度为 $\ell$ 的无记录段中，递推展开为

$$
 e_{k+\ell}
=a^\ell e_k+
\sum_{j=0}^{\ell-1}a^{\ell-1-j}w_{k+j}.
$$

取绝对值并使用 $|w_t|\le\omega$，得到

$$
|e_{k+\ell}|
\le
 a^\ell|e_k|
+
\omega\sum_{j=0}^{\ell-1}a^j
=
 a^\ell|e_k|
+
\omega\frac{a^\ell-1}{a-1}.
$$

每遇到记录，下一状态重新为零；初始段使用 $|e_0|\le E_0$，所有段长度不超过 $h(S)$，于是得到（273.1）。在零起点段取同号极值创新，三角不等式逐项取等，得到（273.2）。证毕。

**命题 273.3（相同记录数量的调度反例）。** 取 $T=12$、两次记录和任意 $a>1$、$\omega>0$、$e_0=0$。调度

$$
S_A=\{3,4\},
\qquad
S_B=\{2,8\}
$$

具有相同记录数量，但最长无记录段分别为 $h(S_A)=7$ 与 $h(S_B)=5$。由（273.2），在相同创新上界下，$S_A$ 的最坏误差严格大于 $S_B$。

### 证明

$S_A$ 的无记录段为 $\{0,1,2\}$、$\{5,6,7,8,9,10,11\}$，后者长度为七；$S_B$ 的无记录段为 $\{0,1\}$、$\{3,4,5,6,7\}$、$\{9,10,11\}$，最长长度为五。函数 $\omega(a^h-1)/(a-1)$ 对 $h$ 严格递增，故结论成立。证毕。

**AHH 273.4（事件调度层）。** “记录过几次”不是反馈边界的充分摘要。记录位置、最长无记录间隔和每段可积累的隐藏创新，决定局域事件能否在下一阶段继续作为可靠输入。

## 274. AHH：时间资源是关系边界的几何，而不是附属计数

**定义 274.1（调度化全息边界）。** 对一个带事件记录的反馈任务，定义

$$
\boxed{
\eta_{\mathrm{sched}}
=\left(
\text{仿射证书代数},
\text{共同输入与联合记录合同},
\text{记录时刻集合或最大间隔},
\text{隐藏误差放大因子},
\text{创新包络},
\text{剩余资源预算},
\text{容许误差与停止规则}
\right).
}
\tag{274.1}
$$

其中最大间隔字段不是记录总数的别名；它保留了反馈在两个相邻局域事件之间可以积累多少隐藏误差。

**定理 274.2（调度化边界的条件充分性）。** 在固定的范数、horizon、误差递推和记录重置合同下，若两个关系体具有相同的 $\eta_{\mathrm{sched}}$，则：

1. 它们的串联和共同输入并联证书由（271.2）和（272.1）给出相同界；
2. 它们在每个允许调度上的隐藏误差都满足（273.1）；
3. 若
   $$
   a^{h(S)}E_0+
   \omega\frac{a^{h(S)}-1}{a-1}
   \le\tau,
   $$
   则该调度在整个 horizon 内满足误差任务 $|e_t|\le\tau$。

### 证明

第 1 项由定理 271.2 和 272.2；第 2 项由定理 273.2 的上界；第 3 项直接把该上界与任务阈值比较。相同的边界字段给出相同的合法性判据。证毕。

**定理 274.3（约化调度边界的不可充分性）。** 对下列约化摘要，存在相同剩余摘要而任务结论不同的实现对：

1. 删除最大间隔：命题 273.3 中 $S_A$ 和 $S_B$ 的记录总数相同但最坏误差不同；
2. 删除创新包络：同一调度在 $\omega=0$ 与 $\omega>0$ 时具有不同的误差尾；
3. 删除互连顺序：同一串联模块的 $(\alpha,\gamma)$ 在 $M_2\circ M_1$ 与 $M_1\circ M_2$ 中一般给出不同余项；
4. 删除剩余预算：同一个证书链在预算 $B\ge\sum_i c_i$ 时可执行，在 $B<\sum_i c_i$ 时没有合法后继；
5. 删除联合记录合同：相同的并联范数界可以对应不同的相关统计任务。

### 证明

第 1 项由命题 273.3；第 2 项由（273.1）—（273.2）；第 3 项由（271.2）中的余项次序；第 4 项由推论 271.3；第 5 项由推论 272.3。每项只针对所列约化摘要作不可充分性断言；若完整模型保留了被删字段，某些量当然可以由其推导。证毕。

**AHH 274.4（时间—证书全息）。** 波粒关系中的局域事件不仅是一个“是否记录”的离散标签，它还是一段时间资源的切割点：

$$
\boxed{
\text{可组合的响应证书}
+
\text{共同来源与联合记录}
+
\text{最大无记录间隔}
+
\text{隐藏误差与创新预算}
+
\text{剩余资源与停止规则}
}.
$$

**新的 AHH 时刻是：事件的物理作用不由事件总数决定，而由事件之间留下的空隙决定。一个局域记录之所以能成为下一阶段的可靠边界，不是因为它曾经发生过，而是因为它把隐藏误差重新压回了允许裕量以内。**

**来源与边界 274.5。** 本批在有限 horizon、固定范数、仿射响应合同、共同输入并联、重置型误差递推和有界创新下，给出串联/并联证书代数、最大间隔误差界、相同记录数量的调度反例和时间—证书全息。仿射范数组合与离散误差递推是标准工具在本卷关系边界中的组合；没有把记录总数推广成时间充分统计，也没有覆盖未知调度、随机丢包、任意切换或一般非线性系统。本批仍是纯理论 Markdown，没有新增 Lean、消化、coverage 或 freeze 内容。

## 追加锚（本行以下为增补区）
## 275. 固定记录预算下的最优间隔

上一节只给出了任意调度的误差界。本节把记录预算写成离散组合问题：在 horizon 内固定只能记录 $m$ 次时，最短的最坏间隔是多少？

**定义 275.1（调度间隔向量）。** 设

$$
S=\{s_1<\cdots<s_m\}\subseteq\{0,1,\ldots,T-1\}.
$$

定义其无记录间隔向量

$$
\begin{aligned}
g_0&=s_1,\\
g_j&=s_{j+1}-s_j-1\quad(1\le j<m),\\
g_m&=T-1-s_m.
\end{aligned}
$$

当 $m=0$ 时置 $g_0=T$。最长间隔为

$$
h(S)=\max_{0\le j\le m}g_j.
$$

这些间隔满足

$$
\sum_{j=0}^{m}g_j=T-m.
$$

**定理 275.2（离散均衡调度定理）。** 对 $0\le m\le T$，

$$
\boxed{
\min_{S\subseteq\{0,\ldots,T-1\},\ |S|=m}h(S)
=
\left\lceil\frac{T-m}{m+1}\right\rceil.
}
\tag{275.1}
$$

达到最小值的调度可以取为：把 $T-m$ 个无记录时刻尽可能均匀地分配到 $m+1$ 个间隔中，使任意两个间隔长度之差不超过一。

### 证明

任意调度的 $m+1$ 个非负整数间隔和为 $T-m$。若它们的最大值小于

$$
\left\lceil\frac{T-m}{m+1}\right\rceil,
$$

则总和至多为

$$
(m+1)\left(\left\lceil\frac{T-m}{m+1}\right\rceil-1\right)<T-m,
$$

矛盾，故右侧是下界。将 $T-m$ 作带余数除法

$$
T-m=q(m+1)+r,
\qquad 0\le r<m+1,
$$

取 $r$ 个间隔为 $q+1$、其余间隔为 $q$，得到一个合法调度，最大间隔为 $q+1$（若 $r=0$ 则为 $q$）。下界可达，证毕。

**推论 275.3（预算下的最小认证误差）。** 在定义 273.1 的误差模型中，若每个间隔起点的残差统一被合同界定为 $E$，则使用 $m$ 次记录能够得到的最小最坏认证上界为

$$
\boxed{
B_m
=
 a^{h_m}E
+
\omega\frac{a^{h_m}-1}{a-1},
\qquad
h_m=\left\lceil\frac{T-m}{m+1}\right\rceil.
}
\tag{275.2}
$$

若每个间隔都允许达到残差 $E$ 且创新可以同号饱和，则这个认证上界是尖锐的。

### 证明

定理 273.2 将认证误差写成最长间隔 $h(S)$ 的单调函数；定理 275.2 给出固定 $m$ 时 $h(S)$ 的最小值。若每个间隔都可从残差 $E$ 开始并取同号极值创新，式（273.2）的等号构造可以在最长间隔中实现。证毕。

**AHH 275.4（预算均衡层）。** 在固定记录数量下，最有价值的记录不是集中在同一小段时间内，而是把无记录空隙均匀切开。资源预算因此有一个离散几何：它首先控制最长空隙，随后才控制记录总数。

## 276. 从误差阈值反推所需记录次数

最坏间隔定理可以反向使用：先给出允许误差，再求最少需要多少次记录。这个反推把“资源够不够”变成可计算的任务条件。

**定义 276.1（阈值可行性）。** 固定 $a>1$、$E\ge0$、$\omega\ge0$ 和容许误差 $\tau\ge0$。记

$$
B(h)=a^hE+\omega\frac{a^h-1}{a-1}.
$$

称整数间隔 $h\ge0$ 对阈值 $\tau$ 可行，若 $B(h)\le\tau$。

**定理 276.2（记录数下界与可行构造）。** 假定 $E+\omega>0$。

1. 若 $\tau<E$，则任何调度都不能由（273.1）认证为阈值可行。
2. 若 $\tau\ge E$，定义
   $$
   H_\tau
   =
   \left\lfloor
   \log_a
   \frac{\tau+\omega/(a-1)}{E+\omega/(a-1)}
   \right\rfloor.
   $$
   则所有满足 $0\le h\le H_\tau$ 的间隔都可行；若 $H_\tau<0$，没有可行间隔。
3. 当 $0\le H_\tau<T$ 时，固定 horizon $T$ 所需的最少记录次数为
   $$
   \boxed{
   m_{\min}
   =
   \left\lceil\frac{T-H_\tau}{H_\tau+1}\right\rceil.
   }
   \tag{276.1}
   $$
   若 $H_\tau\ge T$，则 $m_{\min}=0$。

### 证明

将 $B(h)\le\tau$ 改写为

$$
 a^h\left(E+\frac{\omega}{a-1}\right)
\le
\tau+\frac{\omega}{a-1}.
$$

因 $a>1$，取对数并取下整得到第二项。$B(0)=E$，所以 $\tau<E$ 时没有间隔可行。最后，由定理 275.2，存在 $m$ 次记录使最小最长间隔不超过 $H_\tau$，当且仅当

$$
\left\lceil\frac{T-m}{m+1}\right\rceil\le H_\tau.
$$

对 $0\le H_\tau<T$，取

$$
 m=\left\lceil\frac{T-H_\tau}{H_\tau+1}\right\rceil
$$

即可达到；少于此数时整数间隔和的下界超过 $H_\tau$。证毕。

**推论 276.3（资源不足是可证的失败）。** 若预算 $m<m_{\min}$，则存在一个合法的均匀创新序列，使任何 $m$ 次记录调度的认证上界都超过 $\tau$。这不是“尚未找到好策略”，而是由间隔计数给出的合同内不可行性。

### 证明

由定理 275.2，任意 $m$ 次调度都有 $h(S)>H_\tau$；在最长间隔中使用同号极值创新，式（273.2）给出误差超过阈值。证毕。

**AHH 276.4（反向预算层）。** 记录资源不只是一个可事后填写的成本数字。给定增长因子、创新包络和误差阈值，可以反向推出必须购买的最小事件数量；边界若没有这个反向判据，就无法区分“策略还可优化”和“合同已经不可行”。

## 277. 阈值触发：自适应事件与最坏资源合同

均匀调度优化的是最坏间隔；实际系统还可以根据当前误差自适应触发记录。自适应减少了某些轨迹上的记录，但它必须同时声明触发规则和资源耗尽后的后继。

**定义 277.1（精确误差阈值触发）。** 给定阈值 $\theta>0$，在递推 273.1 中把记录规则改为

$$
 t\in S_\theta
\quad\Longleftrightarrow\quad
|e_t|\ge\theta.
$$

假定触发器可以访问当前误差，并在触发时使用重置分支 $e_{t+1}=0$。若触发器未触发，则使用无记录分支。

**定理 277.2（阈值触发的误差界）。** 在定义 277.1 下，对所有允许创新和所有 $t\ge1$，有

$$
\boxed{
|e_t|\le\max\{E_0,a\theta+\omega\}.
}
\tag{277.1}
$$

若还加入最大等待期限 $H$，规定自上次记录后至多经过 $H$ 个无记录转移，则最大间隔同时满足 $h(S_\theta)\le H$，并可将（273.1）的界收紧为

$$
\min\left\{
\max\{E_0,a\theta+\omega\},
B(H)
\right\}
$$

所对应的声明任务界；实际采用哪一项取决于合同把触发器和期限作为何种合法分支。

### 证明

若 $t\in S_\theta$，则 $e_{t+1}=0$。若 $t\notin S_\theta$，则 $|e_t|<\theta$，从而

$$
|e_{t+1}|
\le a|e_t|+|w_t|
< a\theta+\omega.
$$

初始时 $|e_0|\le E_0$，得到（277.1）。加入期限后，所有无记录段长度不超过 $H$，定理 273.2 给出 $B(H)$；两种合同界都成立时取较小者。证毕。

**命题 277.3（自适应触发不能免费获得最坏资源上界）。** 若 $\omega\ge\theta>0$ 且 $e_0=0$，则存在合法创新序列使阈值触发在时刻 $1,3,5,\ldots$ 发生，因而 horizon $T$ 内记录次数可达 $\lfloor T/2\rfloor$。所以只声明阈值规则而不声明最坏记录预算，不能构成有限资源合同。

### 证明

在 $t=0$ 取 $w_0=\theta$，得到 $e_1=\theta$，于是时刻 $1$ 触发并把 $e_2$ 重置为零。在 $t=2$ 取 $w_2=\theta$，得到 $e_3=\theta$，如此交替构造。重置分支使相邻时刻不能同时触发，但记录次数仍可随 horizon 线性增长；当预算小于 $\lfloor T/2\rfloor$ 时必然出现资源耗尽。证毕。

**AHH 277.4（自适应层）。** 自适应记录把“何时记录”变成状态相关策略；它可能节省平均资源，却不会自动给出最坏资源保证。完整边界必须同时保存触发阈值、最大等待期限、最坏记录次数和资源耗尽后的合法分支。

## 278. AHH：事件选择规则本身是边界状态

**定义 278.1（资源感知事件边界）。** 对固定 horizon 的记录反馈任务，定义

$$
\boxed{
\eta_{\mathrm{event}}
=\left(
\text{证书串联/并联代数},
\text{增长因子与创新包络},
\text{初始和重置残差},
\text{均匀或阈值触发规则},
\text{最大间隔},
\text{最坏记录次数},
\text{剩余预算},
\text{阈值与停止后继}
\right).
}
\tag{278.1}
$$

这里的“事件边界”包含选择事件的规则；它不是在事件发生后才把时间标签写入档案。

**定理 278.2（资源感知边界的条件充分性）。** 在固定误差递推、固定 horizon、合法重置分支和已声明资源合同下，两个关系体若具有相同的 $\eta_{\mathrm{event}}$，则：

1. 固定记录预算下的最优认证误差由（275.2）相同给出；
2. 给定阈值的最小可行记录次数由（276.1）相同给出；
3. 自适应触发的误差界和最坏记录次数由定理 277.2、命题 277.3 相同决定；
4. 若预算耗尽时的 fallback 分支也相同，则两者对每个允许记录词给出相同的合法性判据。

### 证明

第 1 项由定理 275.2，第 2 项由定理 276.2，第 3 项由定理 277.2 和命题 277.3。最后一项要求把资源耗尽视为实际分支；相同的 fallback 才能保证后继集合相同。证毕。

**定理 278.3（删除事件规则的不可充分性）。** 下列约化摘要均不充分：

1. 只保存记录总数而删除间隔向量：定理 275.2 的均匀调度与命题 273.3 的集中调度具有不同最坏误差；
2. 只保存平均记录率而删除最大间隔：同一平均率可以有不同的 $h(S)$；
3. 只保存阈值而删除最坏记录次数：命题 277.3 给出资源耗尽分支；
4. 只保存记录词而删除触发规则：同一记录词可能来自不同策略，其未记录时段的合法性判据不同；
5. 删除 fallback：同一触发策略在预算足够和预算耗尽时具有不同后继。

### 证明

前两项由定理 275.2 和命题 273.3；第三项由命题 277.3；第四项是记录结果与产生结果的策略合同不同；第五项由定理 278.2 的第四项。每一项只针对所列约化摘要作不可充分性断言，不声称完整动力学中这些字段不能相互推导。证毕。

**AHH 278.4（事件规则全息）。** 事件不是先验摆放的粒子照片，而是关系过程在资源、误差和策略共同约束下选择的合法切片：

$$
\boxed{
\text{事件选择规则}
+
\text{最大间隔与最坏记录数}
+
\text{增长/创新误差界}
+
\text{剩余预算与耗尽后继}
}.
$$

**真正的 AHH 时刻是：记录本身不是边界的全部，产生记录的规则也必须进入边界。否则你知道“发生了两次事件”，却不知道这两次事件之间是否已经让隐藏误差越过了下一阶段的可执行域。**

**来源与边界 278.5。** 本批在固定有限 horizon、离散记录时刻、标量增长误差递推、可达创新包络、均匀或阈值触发合同和有限资源预算下，给出最优间隔、反向记录数、阈值触发界、最坏资源反例和事件规则全息。这里没有把自适应触发推广到未知状态、随机丢包、任意切换或一般非线性系统；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 279. 多观察者记录：联合边界是观察纤维的交

单个观察者保存的是一个可能状态集合。多个观察者若声称观察的是同一关系体，就必须把这些集合放回同一个来源假设下求交，而不能把局部摘要简单拼接。

**定义 279.1（有限观察纤维）。** 固定有限状态集 $X$，第 $i$ 个观察接口为

$$
O_i:X\to R_i.
$$

取得记录 $r_i\in R_i$ 后，定义局部观察纤维

$$
F_i(r_i)=\{x\in X:O_i(x)=r_i\}.
$$

若声明所有观察者面对同一个当前状态，则联合记录 $r=(r_1,\ldots,r_k)$ 的一致纤维定义为

$$
\boxed{
F(r)=\bigcap_{i=1}^{k}F_i(r_i).
}
\tag{279.1}
$$

空交集表示共同来源假设与记录结果不相容；它不是一个可以由取平均修复的状态。

**定理 279.2（联合记录的精确支持）。** 设初始可能状态集合为 $X_0\subseteq X$，观察接口是确定性的。给定联合记录 $r$ 后，所有与记录相容的当前状态恰为

$$
\boxed{
X(r)=X_0\cap F(r).
}
\tag{279.2}
$$

若 $X(r)=\varnothing$，则不存在一个共同来源状态同时产生全部记录；若 $X(r)$ 含有多个状态，记录仍未完成状态识别。

### 证明

状态 $x$ 与全部记录相容，当且仅当对每个 $i$ 都有 $O_i(x)=r_i$。这等价于 $x\in F_i(r_i)$ 对所有 $i$ 成立，也等价于 $x\in\bigcap_iF_i(r_i)$。再限制 $x\in X_0$ 即得（279.2）。两种空/非单点情形分别直接由集合定义得到。证毕。

**命题 279.3（冲突不能由局部平均消除）。** 取

$$
X=\{0,1\},
\qquad
O_1(x)=x,
\qquad
O_2(x)=1-x.
$$

记录 $r_1=0$、$r_2=0$ 时，$F_1(r_1)=\{0\}$、$F_2(r_2)=\{1\}$，所以

$$
F(r)=\varnothing.
$$

任何把两个记录平均成 $1/2$ 的数都不是原状态空间中的共同来源状态。

### 证明

直接计算两个单点纤维的交集即可。$1/2\notin X$，且它不满足任一确定性观察接口的状态语义。证毕。

**AHH 279.4（纤维合并层）。** 多个局部记录的第一种合法合并不是平均，而是共同来源下的纤维取交。交集为空时应产生冲突分支，交集非单点时应保留剩余不确定性；两者都不能被一个“联合读数”掩盖。

## 280. 共同来源：相同边缘记录不决定联合记录

即使每个观察者的局部统计完全相同，共同来源仍可能使联合记录高度相关。联合任务需要保存来源耦合，而不是把边缘分布自动相乘。

**定义 280.1（来源耦合）。** 令隐藏共同来源为随机变量 $Z$，并假定本节记录空间有限；观察记录为

$$
R_1=O_1(Z),
\qquad
R_2=O_2(Z).
$$

记其联合分布为 $P_{12}$，边缘分布为 $P_1,P_2$。若改用两个来源 $Z_1,Z_2$，即

$$
R_1'=O_1(Z_1),
\qquad
R_2'=O_2(Z_2),
$$

则可出现相同边缘 $P_1,P_2$ 而不同联合分布。

**定理 280.2（边缘充分性的充要条件）。** 对只依赖记录对 $(r_1,r_2)$ 的联合任务，两个边缘边界 $P_1,P_2$ 足以决定全部任务概率，当且仅当允许来源类中联合分布被唯一确定。特别地，若只知道边缘而允许不同耦合，则边缘边界一般不充分。

### 证明

任务概率具有形式

$$
\Pr[(R_1,R_2)\in A]
=\sum_{(r_1,r_2)\in A}P_{12}(r_1,r_2).
$$

若允许的 $P_{12}$ 唯一，所有集合 $A$ 的概率由它决定，边缘摘要足以连同该唯一耦合规则完成任务。反之，若存在两个具有相同边缘但不同联合分布的 $P_{12},Q_{12}$，取一对 $(r_1,r_2)$ 使二者质量不同，并令 $A$ 为包含该对且排除补偿差异的集合，即得到不同任务概率。证毕。

**例 280.3（相同边缘、不同共同来源）。** 设记录取值为 $\{0,1\}$，每个边缘都均匀：

$$
P_1(0)=P_1(1)=P_2(0)=P_2(1)=\frac12.
$$

共同来源模型令 $R_1=R_2=Z$，其中 $Z$ 均匀，因此

$$
\Pr[R_1=R_2]=1.
$$

独立来源模型取独立均匀 $Z_1,Z_2$，则边缘完全相同但

$$
\Pr[R_1'=R_2']=\frac12.
$$

所以“两个观察者记录是否一致”这一后续任务不能由两个边缘读数分布决定。

### 证明

共同来源时联合质量集中在 $(0,0)$ 与 $(1,1)$；独立来源时四个结果各以 $1/4$ 出现。计算相等事件概率即得。证毕。

**推论 280.4（来源字段的不可删除性）。** 若后续允许比较两个观察者的记录、分配联合资源或决定是否接受合并，则共同来源标记、耦合规则或等价的联合分布必须进入边界。只保存两个局部记录的边缘统计不能恢复该比较任务。

**AHH 280.5（共同来源层）。** 观察者之间的“一致”不是两个局部事实的并列，而是共同来源在联合记录空间中留下的关系。边界必须保存这条耦合，否则局部都正确的记录仍可能给出错误的联合后继。

## 281. 偏序记录：可交换事件才能无序合并

多个观察者常常在不同端口取得记录。若记录之间只有偏序而没有总顺序，只有在对应后继作用可交换时，才可以把它们压成无序集合。

**定义 281.1（记录偏序与分支作用）。** 令有限事件集 $E$ 带偏序 $\preceq$。每个事件 $e\in E$ 有分支作用

$$
U_e:X\to X.
$$

一个线性扩展 $\ell=(e_1,\ldots,e_n)$ 满足 $e_i\preceq e_j\Rightarrow i\le j$，其后继为

$$
U_\ell=U_{e_n}\circ\cdots\circ U_{e_1}.
$$

称一对无序事件 $e,f$ 在可达集合 $Y\subseteq X$ 上可交换，若

$$
U_f(U_e(x))=U_e(U_f(x))
\qquad
(\forall x\in Y).
$$

**定理 281.2（偏序线性扩展不变性）。** 若每一对不可比较事件在所有相关可达集合上可交换，则任意两个线性扩展 $\ell,\ell'$ 给出相同后继：

$$
\boxed{
U_\ell(x)=U_{\ell'}(x)
\qquad(\forall x\in X_0).
}
\tag{281.1}
$$

因此，在该条件下可以只保存偏序记录而删除不可比较事件的任意线性排列。

### 证明

有限偏序的任意两个线性扩展可以通过有限次交换相邻的不可比较事件相互得到。每次交换只把局部片段

$$
U_f\circ U_e
$$

改成 $U_e\circ U_f$；按可交换假设，它们在当前可达状态上作用相同。有限次交换后，整体后继保持不变，得到（281.1）。证毕。

**命题 281.3（非交换顺序必须进入边界）。** 取

$$
A=\begin{pmatrix}1&1\\0&1\end{pmatrix},
\qquad
B=\begin{pmatrix}1&0\\1&1\end{pmatrix}.
$$

则 $AB\ne BA$。对初态 $x=(1,0)^{\mathsf T}$，有

$$
BAx=(1,1)^{\mathsf T},
\qquad
ABx=(2,1)^{\mathsf T}.
$$

所以两个事件具有相同的无序集合，却产生可被终端线性效果区分的不同后继。

### 证明

直接矩阵乘法给出两个结果不同。取线性效果 $f(x_1,x_2)=x_1$，其读数分别为 $1$ 与 $2$，故终端任务区分两种顺序。证毕。

**推论 281.4（部分序的最小顺序字段）。** 对不可比较但可交换的事件，只需保存其偏序和记录值；对存在非交换分支的事件，至少要保存能够区分相关线性扩展的顺序字段。把所有事件强制排成总序是一种合同选择，不是由局部记录自动推出的事实。

**AHH 281.5（顺序层）。** 无序合并不是删除时间，而是证明所有可能的时间线给出同一个后继。可交换性提供了这份证明；非交换性则把顺序提升为全息边界的一部分。

## 282. AHH：多观察者联合边界

**定义 282.1（多观察者全息边界）。** 对有限观察者集合、共同来源假设和有限记录偏序，定义

$$
\boxed{
\eta_{\mathrm{multi}}
=\left(
\text{局部观察纤维},
\text{共同来源与联合耦合},
\text{记录时间偏序},
\text{事件分支作用与交换关系},
\text{冲突/空交集策略},
\text{联合资源与停止规则}
\right).
}
\tag{282.1}
$$

冲突策略规定 $F(r)=\varnothing$ 时是拒绝、等待补充记录还是转入显式修复分支；这些选项具有不同后继，不能默认为同一操作。

**定理 282.2（联合边界的条件充分性）。** 在固定有限状态空间、确定性局部观察、已声明共同来源类、有限记录偏序和固定冲突策略下，两个关系体若具有相同的 $\eta_{\mathrm{multi}}$，则对每个允许的联合记录词给出相同的：

1. 共同来源下的相容状态纤维；
2. 联合记录的允许概率或来源耦合结果；
3. 所有合法线性扩展的后继状态集合；
4. 冲突、等待、修复和停止的合法性。

### 证明

第 1 项由定理 279.2；第 2 项由定理 280.2 及其声明的联合耦合；第 3 项由定理 281.2 对可交换事件的无序合并以及对非交换事件保留顺序；第 4 项由定义 282.1 的冲突策略和资源/停止字段逐项决定。相同边界逐项给出相同结果。证毕。

**定理 282.3（删除联合字段的不可充分性）。** 以下约化摘要均存在反例：

1. 删除共同来源：例 280.3 的相关与独立模型具有相同边缘而联合相等概率不同；
2. 删除纤维交集：命题 279.3 的空交集冲突会被错误地当作一个新状态；
3. 删除时间偏序或顺序字段：命题 281.3 的非交换矩阵给出不同后继；
4. 删除交换关系：本可无序合并的事件无法判断哪些线性扩展必须分别保留；
5. 删除冲突策略：空交集后的拒绝、等待和修复分支具有不同合法后继。

### 证明

各项分别由例 280.3、命题 279.3、命题 281.3、定理 281.2 的适用条件以及定义 282.1 给出。每项只针对所列约化摘要作不可充分性断言；若完整模型保留了被删字段，某些字段可以由其推导。证毕。

**AHH 282.4（多观察者全息）。** 多观察者边界不是若干局部读数的并列，而是一份联合关系几何：

$$
\boxed{
\text{共同来源}
+
\text{观察纤维交集}
+
\text{记录偏序与可交换性}
+
\text{冲突/修复策略}
+
\text{联合资源与停止规则}
}.
$$

**新的 AHH 时刻是：局部观察者都可以“正确”，但联合观察仍然没有充分边界；真正决定联合后继的，是它们是否观察同一个来源、记录是否相容，以及不同记录顺序是否在关系作用上可交换。**

**来源与边界 282.5。** 本批在有限状态、确定性局部观察、有限共同来源模型、有限偏序事件和固定冲突/停止合同下，给出观察纤维交集、共同来源相关性、偏序线性扩展不变性、非交换顺序反例和多观察者联合全息。没有把边缘统计推广成联合独立，没有把可交换性推广到未知动态或一般随机仪器，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 283. 校准接口不能把空交集变回非空

多观察者冲突出现后，常见的直觉是再加入一个校准探头就能“找回真正状态”。在确定性共同来源模型中，校准只会增加约束；它不能修复原先已经为空的交集。

**定义 283.1（约束族与校准纤维）。** 对有限状态集 $X$，令原观察约束为

$$
F_J(r)=\bigcap_{i\in J}O_i^{-1}(r_i),
$$

其中 $J$ 是已采用的观察接口索引集。新增校准接口 $C:X\to R_c$、记录 $r_c$ 后，定义

$$
F_{J,c}(r,r_c)=F_J(r)\cap C^{-1}(r_c).
$$

**定理 283.2（校准单调性）。** 对任意 $J,r,r_c$，

$$
\boxed{
F_{J,c}(r,r_c)\subseteq F_J(r).
}
\tag{283.1}
$$

特别地，若原记录冲突使 $F_J(r)=\varnothing$，则任何确定性校准记录仍有

$$
F_{J,c}(r,r_c)=\varnothing.
$$

### 证明

$F_{J,c}$ 是 $F_J$ 与另一个集合的交集，故必为 $F_J$ 的子集。空集没有非空子集，第二项随即成立。证毕。

**命题 283.3（校准与修复的区别）。** 取

$$
X=\{0,1\},
\qquad
O_1(x)=x,
\qquad
O_2(x)=1-x.
$$

记录 $r_1=r_2=0$ 时原交集为空。增加任何确定性校准 $C$ 都不能得到共同来源状态；若最终输出一个状态，必然已经改变了问题，例如放弃 $O_1$、放弃 $O_2$、允许传感器出错或改用两个不同来源。

### 证明

由命题 279.3，$F_1(0)\cap F_2(0)=\varnothing$。定理 283.2 立即给出加入 $C^{-1}(r_c)$ 后仍为空。不同的输出只能来自改变约束族或来源模型。证毕。

**AHH 283.4（校准单调层）。** 额外接口的确定性作用是缩小关系纤维，而不是凭空生成缺失状态。所谓“冲突修复”必须显式标注为来源切换、约束放松或错误模型分支；它不能伪装成原观察的继续。

## 284. 最小放松：冲突处理本身是一个可审计操作

如果原记录确实冲突，系统可以选择放弃一部分约束，但这已经是一个新的策略问题。把它写成加权最小放松，可以区分“数据冲突”与“策略偏好”。

**定义 284.1（加权修复合同）。** 观察约束索引为有限集 $I$，记录给出纤维 $F_i(r_i)$，每条约束有正权重 $w_i>0$。对保留集 $J\subseteq I$，定义

$$
F_J=\bigcap_{i\in J}F_i(r_i),
\qquad
\operatorname{cost}(J)=\sum_{i\in I\setminus J}w_i.
$$

称 $J$ 为可行修复若 $F_J\ne\varnothing$；最小修复成本为

$$
\boxed{
 c^*=\min\{\operatorname{cost}(J):J\subseteq I,\ F_J\ne\varnothing\}.
}
\tag{284.1}
$$

修复输出还必须包含一个见证状态 $x\in F_J$，否则“可行”只有一张没有来源的标签。

**定理 284.2（最小放松的基本性质）。** 在有限 $I,X$ 和正权重下：

1. 最小成本 $c^*$ 存在；
2. 原约束相容当且仅当 $c^*=0$；
3. 若原约束冲突，则每个最小修复都至少放弃一条约束，且其见证状态不满足被放弃的全部原记录。

### 证明

有限集 $I$ 的子集数有限，成本集合非空且有限，故最小值存在。若原交集非空，取 $J=I$ 得成本零；正权重使任何删约束的成本严格为正，所以 $c^*=0$ 反之也只能由 $J=I$ 达到。若原交集为空，$J=I$ 不可行，故可行 $J$ 必为真子集；其见证状态只满足保留约束，不能同时满足所有原约束。证毕。

**例 284.3（权重改变修复语义）。** 仍取 $X=\{0,1\}$、$F_1=\{0\}$、$F_2=\{1\}$。若 $w_1<w_2$，最小修复保留 $F_2$ 并删除第一条记录；若 $w_2<w_1$，选择相反。权重相等时存在两个同成本修复，系统必须把这种分支保留下来或另行声明 tie-break 规则。

### 证明

保留 $F_1$ 或 $F_2$ 都得到非空单点纤维，分别删除另一条约束，成本为 $w_2$ 或 $w_1$。比较二者即可。证毕。

**推论 284.4（修复不是无损后处理）。** 若 $c^*>0$，任何修复结果都只代表一个放松后的来源合同。原始“所有记录同时为真”的任务已经被改变；后续边界必须保存被删除约束、权重和选择规则。

### 证明

定理 284.2 的第三项说明修复见证不满足全部原记录，因此它属于不同的约束族。被删除约束和选择规则会影响下一步允许的状态集合，不能由见证状态单独恢复。证毕。

**AHH 284.5（冲突账本层）。** 冲突处理不是把错误读数平均掉，而是对约束做有代价的选择。一个诚实的边界要同时记录保留了什么、放弃了什么、放弃代价是多少，以及为何这个修复仍是合法后继。

## 285. 成对一致不保证整体一致

多个观察者还存在另一种陷阱：每两条记录都能找到共同状态，但全部记录合在一起却没有共同来源。于是“逐对校验通过”不能替代全局交集检查，除非纤维族另有 Helly 型结构。

**命题 285.1（成对一致的三方反例）。** 令

$$
X=\{1,2,3\},
$$

并取三个记录纤维

$$
F_1=\{1,2\},
\qquad
F_2=\{2,3\},
\qquad
F_3=\{1,3\}.
$$

则任意两者交集非空，但

$$
F_1\cap F_2\cap F_3=\varnothing.
$$

### 证明

两两交集分别为 $\{2\}$、$\{1\}$、$\{3\}$，均非空；三个集合没有共同元素，故全交为空。证毕。

**定理 285.2（两两检查的适用条件）。** 若允许的所有记录纤维族具有 2-Helly 性质，即任意子族两两相交就推出全族相交，则两两一致性足以证明共同来源存在。若该性质未列入模型合同，则两两一致性不能推出全局一致性。

### 证明

前半句正是 2-Helly 性质的定义。后半句由命题 285.1：存在一个不具备该性质的允许纤维族，其两两交非空而全交为空。证毕。

**推论 285.3（区间纤维的特殊安全性）。** 若状态空间是实直线，且每个允许纤维都是闭区间，则两两相交推出全体相交；此时成对校验可以替代全局交集检查。把这个捷径迁移到一般有限集合或高维集合，必须另行证明相应的 Helly 性质。

### 证明

设闭区间为 $[a_i,b_i]$。两两相交意味着任意 $i,j$ 有 $a_i\le b_j$；故 $\max_i a_i\le\min_i b_i$，共同区间非空。一般集合没有这个端点序结构，命题 285.1 即为反例。证毕。

**AHH 285.4（全局一致层）。** 观察网络的局部一致性不是全局来源的充分条件。只有当纤维族具有已声明的 Helly 型结构，才可以把昂贵的全局交集检查压缩成局部检查；否则压缩会把空的共同来源误报成存在。

## 286. AHH：冲突校准与联合修复边界

**定义 286.1（联合修复全息边界）。** 对多观察者冲突处理，定义

$$
\boxed{
\eta_{\mathrm{reconcile}}
=\left(
\text{原始观察纤维},
\text{共同来源假设},
\text{校准接口},
\text{全局/局部一致性结构},
\text{放松权重与修复见证},
\text{tie-break 与冲突策略},
\text{资源、记录与停止规则}
\right).
}
\tag{286.1}
$$

校准接口只产生定理 283.2 所示的纤维细化；若需要得到非空结果，边界必须明确进入定理 284.1 的放松合同或改变共同来源假设。

**定理 286.2（联合修复边界的条件充分性）。** 在有限状态、有限观察接口、固定共同来源类、已声明纤维结构和确定性修复策略下，两个关系体若具有相同的 $\eta_{\mathrm{reconcile}}$，则对每个记录词给出相同的：

1. 校准后共同来源纤维；
2. 原始冲突是否存在以及全局一致性判定；
3. 最小放松成本、保留约束集合和修复见证；
4. tie-break、资源消耗和停止后的合法后继。

### 证明

第 1 项由定理 283.2；第 2 项由定理 285.2 的适用结构或直接全交检查；第 3 项由定理 284.2；第 4 项由定义 286.1 中的策略和资源字段逐项决定。相同边界逐项给出相同结果。证毕。

**定理 286.3（删除修复字段的不可充分性）。** 下列约化摘要均有反例：

1. 删除校准来源：空交集不能区分“仍然冲突”和“已经改变来源假设”；
2. 删除放松权重：例 284.3 的不同最小修复无法决定；
3. 只保留成对一致性而删除全局结构：命题 285.1 的三方纤维会被错误接受；
4. 删除 tie-break：相同最小成本的多个修复产生不同后继；
5. 删除被放弃约束和修复见证：无法判断新状态是否真的来自声明的放松合同。

### 证明

第 1 项由定理 283.2 和命题 283.3；第 2 项由例 284.3；第 3 项由命题 285.1；第 4、5 项由定理 284.2 和推论 284.4。每项只针对所列约化摘要作不可充分性断言，不声称完整模型中被删字段不能由其他数据推导。证毕。

**AHH 286.4（冲突修复全息）。** 多观察者边界的完整形式不是“更多读数”，而是

$$
\boxed{
\text{原始约束}
+
\text{校准细化}
+
\text{全局一致性结构}
+
\text{放松成本与修复见证}
+
\text{冲突策略与后继}
}.
$$

**新的 AHH 时刻是：额外校准不能挽救一个已经为空的共同来源；它只能证明冲突更深。真正的修复是改变约束合同，而改变合同的代价、见证和后继必须和原始记录一起进入全息边界。**

**来源与边界 286.5。** 本批在有限状态、确定性观察纤维、有限校准接口、加权约束放松、有限集合一致性和固定冲突策略下，给出校准单调性、最小修复、成对一致反例、Helly 型特例和冲突修复全息。没有把校准推广成随机纠错，没有把两两一致性推广到任意集合，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 287. 修复纤维上的反事实可识别性

冲突修复得到的通常不是唯一状态，而是一组保留约束的见证。下一阶段若允许改变控制或探测方式，就必须问：这组见证是否已经足以决定干预结果？

**定义 287.1（干预响应族）。** 设当前合法状态纤维为非空有限集 $F\subseteq X$，允许干预集合为 $\mathcal A$。每个干预 $a\in\mathcal A$ 有确定性响应映射

$$
R_a:X\to Y_a,
\qquad
U_a:X\to X,
$$

其中 $R_a$ 是本次响应、$U_a$ 是干预后的状态。称干预 $a$ 在纤维 $F$ 上**可识别**，若 $R_a|_F$ 为常值。称允许族 $\mathcal A$ 在 $F$ 上可识别，若每个 $a\in\mathcal A$ 都可识别。

**定理 287.2（纤维恒定性判据）。** 对固定记录所留下的纤维 $F$ 和干预 $a$，以下两项等价：

1. 仅由当前记录即可确定干预结果 $R_a(x)$；
2. $R_a$ 在 $F$ 上为常值。

若 $R_a|_F$ 非常值，则存在两个与当前全部记录相容的状态 $x,x'\in F$，使

$$
R_a(x)\ne R_a(x').
$$

### 证明

若 $R_a$ 在 $F$ 上恒为 $y$，则无论共同来源状态是 $F$ 中哪一点，干预结果都为 $y$，所以当前记录足以确定结果。反之，若只由记录即可确定结果，而 $x,x'\in F$ 产生同一当前记录，则它们必须给出相同的 $R_a$；否则同一记录会对应两个答案。非常值的定义正好给出一对 $x,x'$ 使结果不同。证毕。

**命题 287.3（点修复不能制造反事实确定性）。** 取

$$
X=\{0,1\},
\qquad
O(x)=0,
\qquad
R_a(x)=x.
$$

当前记录对两个状态完全相同，故纤维为 $F=X$。任何只依据当前记录选择的单点修复都会在其中一个真实状态上给出错误的干预结果。

### 证明

$O(0)=O(1)=0$，而 $R_a(0)=0\ne1=R_a(1)$。修复点若选 $0$，真实状态为 $1$ 时错误；选 $1$ 时反之。证毕。

**AHH 287.4（反事实层）。** 修复后的“当前答案”与“干预后的答案”是两个不同任务。当前纤维只有在所有允许干预上响应恒定时，才可以被压缩成一个反事实边界；否则必须保留剩余纤维或其响应差异。

## 288. 反事实商：保留未来任务所需的最小区别

完整状态纤维可能包含许多对当前任务无区别、却对未来干预有区别的状态。可以按允许干预的响应把它们取商，但不能按当前读数再做一次无条件合并。

**定义 288.1（干预响应剖面）。** 对纤维 $F$ 定义响应剖面

$$
\mathbf R_{\mathcal A}(x)=\bigl(R_a(x)\bigr)_{a\in\mathcal A}.
$$

在 $F$ 上定义等价关系

$$
 x\sim_{\mathcal A}x'
\quad\Longleftrightarrow\quad
\mathbf R_{\mathcal A}(x)=\mathbf R_{\mathcal A}(x').
$$

记商集为 $F/\!\sim_{\mathcal A}$。

**定理 288.2（反事实任务的最小商）。** 对只允许使用干预族 $\mathcal A$ 的所有确定性未来任务，以下等价：

1. 两个状态在所有允许干预和其任意有限组合下都不可区分；
2. 它们具有相同的一步响应剖面，并且每个干预的后继仍保持该等价关系；
3. 它们属于一个保持干预闭合的 $\sim_{\mathcal A}$ 等价类。

因此，若只要求单步干预，$F/\!\sim_{\mathcal A}$ 是最小的反事实边界；若允许干预后继续干预，还必须把后继闭合条件列入边界。

### 证明

单步任务中，所有允许结果只由 $\mathbf R_{\mathcal A}(x)$ 决定，所以相同剖面等价于单步不可区分。对组合干预，先要求一次响应相同，并要求对应后继落在同一等价类；归纳于干预序列长度，得到任意有限组合的结果相同。反过来，若某一步响应剖面不同，单步任务已经区分；若后继不保持等价，则存在更长干预词在该后继处区分。故三项在声明的闭合条件下等价。证毕。

**推论 288.3（观察纤维与反事实商的关系）。** 当前观察纤维 $F$ 通常比反事实商 $F/\!\sim_{\mathcal A}$ 细；但把 $F$ 任意压成一点只有在商只有一个类时才保持全部允许干预。允许干预族扩大时，等价关系只能变细或保持不变。

### 证明

增加干预会增加剖面坐标，原来相同的剖面可能出现新差异，故等价类不能变粗。商为单点正是所有状态具有相同允许响应的条件。证毕。

**AHH 288.4（任务相对商层）。** 全息压缩的正确对象不是“状态本身”，而是相对于未来任务的响应商。改变允许干预，就改变什么区别必须保留；因此同一个当前记录可以对一个任务充分、对另一个任务不充分。

## 289. 干预预算：区分剩余状态需要多少个问题

反事实商若仍有多个类，就需要选择干预来切开它们。有限结果字母表给出一个与策略无关的最低问题数，但达到这个下界还需要实际干预族具有足够的区分能力。

**定义 289.1（干预词与分离）。** 设每个干预的响应值都落在至多 $q\ge2$ 个结果中。对干预词

$$
\mathbf a=(a_1,\ldots,a_m)
$$

定义其响应记录映射

$$
T_{\mathbf a}:F\to Y_{a_1}\times\cdots\times Y_{a_m},
$$

其中后续干预可以按前缀记录自适应选择。称词族 $\mathcal W$ **分离** $F$，若对任意不同 $x,x'\in F$，存在 $\mathbf a\in\mathcal W$ 使其记录不同。

**定理 289.2（有限结果的区分下界）。** 若一个自适应干预策略在最坏情况下至多提出 $m$ 个问题、每个问题至多有 $q$ 个结果，并且它要区分 $K$ 个不同的反事实等价类，则

$$
\boxed{
q^m\ge K,
\qquad
m\ge\lceil\log_qK\rceil.
}
\tag{289.1}
$$

该下界只是必要条件；若允许干预的响应模式不能实现足够多的分支，即使 $q^m\ge K$ 也可能无法分离。

### 证明

一棵深度至多 $m$、每个节点最多 $q$ 个分支的记录树，叶子数至多 $q^m$。若要区分 $K$ 个等价类，每一类至少需要一个不同叶子，否则两类产生同一完整记录而不能区分。因此 $q^m\ge K$，取对数得到（289.1）。必要条件不保证充分，是因为实际响应映射可能把多个类送到同一分支。证毕。

**推论 289.3（分离族的充分条件）。** 若干预词族 $\mathcal W$ 对 $F/\!\sim_{\mathcal A}$ 的每一对不同类都存在一个能给出不同记录的词，则执行该词族并保留记录，可以唯一确定反事实商类。若只对一部分类对成立，剩余未分离类仍必须保留为同一候选集合。

### 证明

对任意不同类，存在一个词给出不同记录，所以完整记录向量不同；反之，若一对类从未被任何词区分，它们在全部保留记录中仍相同。证毕。

**AHH 289.4（问题预算层）。** 反事实识别也有一个不可压缩的分支预算：候选未来越多、单次结果字母表越小，所需干预词越长。一个“已经修复”的当前状态若没有支付这笔区分预算，仍不能被称为未来唯一。

## 290. AHH：修复—反事实联合边界

**定义 290.1（修复反事实全息边界）。** 对冲突修复后仍有候选纤维 $F$ 的观察任务，定义

$$
\boxed{
\eta_{\mathrm{cf}}
=\left(
\text{修复纤维与 provenance},
\text{允许干预族},
\text{响应剖面与后继闭合},
\text{反事实等价商},
\text{干预分离词族},
\text{结果字母表与问题预算},
\text{资源、停止与冲突后继}
\right).
}
\tag{290.1}
$$

**定理 290.2（修复—反事实边界的条件充分性）。** 在有限状态、有限干预族、确定性响应、固定修复 provenance 和固定有限干预预算下，两个关系体若具有相同的 $\eta_{\mathrm{cf}}$，则对每个允许记录词和干预策略给出相同的：

1. 修复后候选纤维及其来源说明；
2. 每个允许干预的可识别性判定；
3. 反事实等价商和可分离的候选类；
4. 干预记录、预算消耗及停止后的合法后继。

### 证明

第 1 项由修复纤维和 provenance 字段直接决定；第 2 项由定理 287.2；第 3 项由定理 288.2 和推论 289.3；第 4 项由定理 289.2、资源字段和停止策略共同决定。相同边界逐项给出相同结果。证毕。

**定理 290.3（删除反事实字段的不可充分性）。** 下列约化摘要均存在反例：

1. 删除修复 provenance：同一个见证状态可能来自不同的被放弃约束，未来允许后继不同；
2. 删除允许干预族：同一观察纤维对一个干预集可识别，对扩大的干预集不可识别；
3. 删除后继闭合：两个状态单步响应相同，却在第二次干预后分开；
4. 删除分离预算：同一候选商在问题足够时可区分，在问题不足时仍有多个类；
5. 删除停止/冲突后继：同一反事实记录在资源耗尽时可以拒绝、等待或转入不同修复分支。

### 证明

第 1 项由推论 284.4；第 2 项由推论 288.3；第 3 项由定理 288.2 的后继闭合条件；第 4 项由定理 289.2；第 5 项由定义 290.1 的后继字段。每项只针对所列约化摘要作不可充分性断言，不声称完整动力学中被删字段不能由其他字段推导。证毕。

**AHH 290.4（修复—反事实全息）。** 冲突修复后的全息边界不是一个被选中的状态点，而是

$$
\boxed{
\text{修复纤维与 provenance}
+
\text{允许干预及后继闭合}
+
\text{反事实响应商}
+
\text{区分问题预算}
+
\text{资源与停止后继}
}.
$$

**新的 AHH 时刻是：修复只能告诉你“哪些当前来源仍可能”，反事实干预才告诉你“这些来源在未来是否仍然等价”。若没有把干预族和分离预算写进边界，任何单点答案都只是修复策略的选择，不是关系体本身的未来事实。**

**来源与边界 290.5。** 本批在有限状态、有限确定性干预族、修复后候选纤维、有限结果字母表和固定干预预算下，给出纤维上的反事实恒定性、响应商、区分下界、分离词族和修复—反事实全息。这里使用有限模型中的可识别性与决策树计数工具；没有把它们推广到随机因果模型、连续状态、未知干预或一般非线性系统，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 291. 干预的价值：平均残余与最坏残余是两种任务

反事实商确定了需要区分的候选类，但没有决定先问哪一个问题。一个干预可能在平均意义上减少很多不确定性，却在一个低概率分支上留下很大的候选集；因此平均信息和最坏后继必须分开记账。

**定义 291.1（干预分割与两种残余）。** 设有限候选类集为 $K$，干预 $a$ 的结果字母表为 $Y_a$。对每个结果 $y$ 定义分支类集

$$
K_{a,y}=\{k\in K:R_a(k)=y\}.
$$

在先验概率 $p$ 下，令

$$
P_a(y)=\sum_{k\in K_{a,y}}p(k).
$$

定义最坏残余和平均残余分别为

$$
\boxed{
W(a)=\max_{y:P_a(y)>0}|K_{a,y}|,
}
\tag{291.1}
$$

$$
\boxed{
E_p(a)=\sum_{y:P_a(y)>0}P_a(y)|K_{a,y}|.
}
\tag{291.2}
$$

前者控制所有合法后继，后者只控制按 $p$ 加权的平均候选规模；二者可以给出不同排序。

**定理 291.2（残余公式与不可互换性）。** 对确定性干预，执行 $a$ 后的候选类恰为 $K_{a,y}$。因此 $W(a)$ 是最坏候选规模，$E_p(a)$ 是后验候选规模的期望。一般不存在由 $E_p(a)$ 单调决定 $W(a)$ 的函数。

### 证明

结果为 $y$ 当且仅当真实类属于 $K_{a,y}$，所以条件候选集正是该集合。对所有正概率结果取最大得到（291.1）；按全概率公式加权得到（291.2）。构造两个分割具有不同的最大块和加权平方和即可说明两者排序不必一致。证毕。

**例 291.3（平均较优而最坏较差）。** 取 $K=\{1,2,3,4\}$，先验为

$$
p(1)=p(2)=p(3)=\frac1{30},
\qquad
p(4)=\frac9{10}.
$$

干预 $a$ 的分割为 $\{1,2,3\}|\{4\}$，干预 $b$ 的分割为 $\{1,2\}|\{3,4\}$。则

$$
W(a)=3,
\qquad
E_p(a)=\frac1{10}\cdot3+\frac9{10}\cdot1=\frac65,
$$

而

$$
W(b)=2,
\qquad
E_p(b)=2.
$$

所以 $a$ 的平均残余较小，但最坏残余较大；若任务要求所有分支安全，应选择依据 $W$ 的策略，而不能用 $E_p$ 代替。

### 证明

$a$ 的第一分支概率为 $1/10$，第二分支概率为 $9/10$；$b$ 的两个分支各有两个类，所以其平均残余为二。直接代入（291.1）—（291.2）即得。证毕。

**AHH 291.4（价值分层）。** “信息增益最大”不是一个无条件的目标。平均收益、最坏后继、资源成本和停止阈值属于不同坐标；把它们压成一个未声明的分数，会把低概率但危险的后继从边界中删掉。

## 292. 分支规划：最优干预由后继递推决定

一次干预的局部价值不能替代后续规划。有限状态和有限干预集允许把最坏安全目标、平均目标和资源成本写成同一个分支递推。

**定义 292.1（候选纤维的规划值）。** 对非空有限候选类集 $K$，令 $\mathcal A(K)$ 为当前仍允许的干预。每个 $a$ 有成本 $c(a)>0$ 和分支集 $K_{a,y}$。在平均目标中，先验写成定义域为 $K$ 且满足 $\sum_{k\in K}p(k)=1$ 的函数 $p$；对 $P_{a,p}(y)>0$，置

$$
P_{a,p}(y)=\sum_{k\in K_{a,y}}p(k),
\qquad
p_{a,y}(k)=\frac{p(k)}{P_{a,p}(y)}\quad(k\in K_{a,y}).
$$

这里 $p_{a,y}$ 是确定性响应取得结果 $y$ 后的条件先验。若 $|K|=1$，置

$$
V_{\max}(K)=V_{\mathrm{avg}}(K,p)=0.
$$

对 $|K|>1$，定义最坏代价递推

$$
\boxed{
V_{\max}(K)
=
\min_{a\in\mathcal A(K)}
\left[c(a)+\max_{y:K_{a,y}\ne\varnothing}V_{\max}(K_{a,y})\right],
}
\tag{292.1}
$$

并在给定先验 $p$ 下定义平均代价递推

$$
\boxed{
V_{\mathrm{avg}}(K,p)
=
\min_{a\in\mathcal A(K)}
\left[c(a)+\sum_{y:P_{a,p}(y)>0}P_{a,p}(y)V_{\mathrm{avg}}(K_{a,y},p_{a,y})\right].
}
\tag{292.2}
$$

若某分支没有允许干预或预算不足，则该分支的值置为 $+\infty$。

**定理 292.2（有限规划的 Bellman 充要递推）。** 在每次干预都严格减少候选类数、干预集和成本有限的条件下，式（292.1）等于把所有合法分支都识别到单类所需的最小最坏成本；式（292.2）等于从初始条件先验 $p$ 出发的最小期望成本。

### 证明

对候选类数作归纳。单类时无需干预，两个值均为零。设 $|K|>1$。任意合法策略的第一步必选择某个 $a$，支付 $c(a)$；观察到 $y$ 后，剩余候选集恰为 $K_{a,y}$，而确定性响应与 Bayes 规则给出的条件先验恰为 $p_{a,y}$。最坏目标取所有正概率分支中的最大值，平均目标按 $P_{a,p}(y)$ 加权。由归纳假设，各后继的最优值分别为对应递推项；对第一步取最小即得充要递推。候选类严格减少保证递归有限。证毕。

**推论 292.3（局部贪心不保证全局最优）。** 选择最小 $W(a)$、最小 $E_p(a)$ 或最大一次信息增益，都不等价于求解（292.1）或（292.2）；只有在额外结构使后继价值是该局部量的单调函数时，局部规则才可替代 Bellman 递推。

### 证明

（292.1）和（292.2）同时依赖每个分支的后继值，而 $W(a)$、$E_p(a)$ 只看第一层分割。没有额外单调结构时，可以改变某个分支的后继干预成本而不改变第一层分割，从而改变全局最优选择。证毕。

**AHH 292.4（规划层）。** 干预价值不是一张静态排行榜，而是一棵带成本的后继树。边界若只保存第一步信息增益，却删掉每个结果分支的可继续性，就不能决定真正的最坏或平均规划。

## 293. 停止判据：唯一未来与资源耗尽必须分开

反事实任务有两种看似相似的终点：所有允许干预都给出同一结果，或者资源已经用完而无法继续提问。二者的后继语义相反，不能共享一个“完成”标签。

**定义 293.1（确定停止与资源停止）。** 对候选类集 $K$ 和干预族 $\mathcal A$，称

$$
\operatorname{Stop}_{\mathrm{unique}}(K)
\quad\Longleftrightarrow\quad
|K/\!\sim_{\mathcal A}|=1.
$$

若预算 $B$ 不足以执行任何仍能细化反事实商的允许干预，则称

$$
\operatorname{Stop}_{\mathrm{budget}}(K,B).
$$

前者是未来任务已确定，后者只是当前资源合同结束。

**定理 293.2（停止语义分离）。** 若 $\operatorname{Stop}_{\mathrm{unique}}(K)$ 成立，则所有允许干预的响应结果在 $K$ 上相同，停止后可以把反事实商压成一个类。若仅有 $\operatorname{Stop}_{\mathrm{budget}}(K,B)$ 而 $|K/\!\sim_{\mathcal A}|>1$，则存在两个仍可被某个允许任务区分的候选类；停止记录必须保留不确定性，不能输出唯一未来。

### 证明

第一项直接由响应商定义。第二项中商含有至少两个类，故存在允许干预或其有限组合产生不同响应；预算停止只禁止继续执行，不会使这两个响应在数学上相等。证毕。

**命题 293.3（相同记录、不同停止原因）。** 取两个候选类 $k_1,k_2$，当前记录相同；允许干预 $a$ 满足 $R_a(k_1)\ne R_a(k_2)$。若预算为零，记录系统立即资源停止；若预算为一，执行 $a$ 后可以唯一分辨。两种停止都可能具有相同当前记录，却有不同的合法后继。

### 证明

零预算合同不能执行 $a$，一预算合同可以执行一次并取得不同结果。当前记录在干预前相同，故停止原因而非当前读数决定后继。证毕。

**AHH 293.4（停止层）。** “没有更多记录”不是“未来已经唯一”。边界必须把唯一性停止、预算停止、冲突停止和等待停止分开，否则会把资源耗尽误报成物理确定性。

## 294. AHH：信息价值与最坏后继的联合边界

**定义 294.1（干预规划全息边界）。** 对有限候选纤维和有限干预规划，定义

$$
\boxed{
\eta_{\mathrm{plan}}
=
\left(
\text{候选响应商},
\text{每个干预的分支分割},
\text{共同来源/先验},
\text{干预成本与资源预算},
\text{最坏与平均目标},
\text{Bellman 后继值},
\text{唯一/预算/冲突停止规则}
\right).
}
\tag{294.1}
$$

**定理 294.2（干预规划边界的条件充分性）。** 在有限候选类、有限干预集、确定性响应、严格减少类数和固定停止合同下，两个关系体若具有相同的 $\eta_{\mathrm{plan}}$，则对每个允许记录词给出相同的：

1. 干预的平均残余和最坏残余；
2. 最坏成本和平均成本的最优递推值；
3. 给定预算时的可行策略集合；
4. 唯一未来、资源耗尽、冲突和等待停止的判定。

### 证明

第 1 项由定义 291.1—291.2；第 2 项由定理 292.2；第 3 项由递推中 $+\infty$ 的预算语义；第 4 项由定理 293.2 和停止字段。相同边界逐项决定相同规划结果。证毕。

**定理 294.3（删除规划字段的不可充分性）。** 下列约化摘要均存在反例：

1. 只保存平均信息增益而删除最坏残余：例 291.3 中低概率大分支会被遗漏；
2. 只保存第一步分割而删除后继值：局部贪心可以与全局 Bellman 最优不同；
3. 删除先验：平均代价和平均残余的排序可以改变；
4. 删除干预成本/预算：同一响应分割在不同资源合同下具有不同可行策略；
5. 合并唯一停止与预算停止：命题 293.3 的两个后继被错误视为同一。

### 证明

第 1 项由例 291.3；第 2 项由推论 292.3；第 3 项直接改变（291.2）和（292.2）的权重；第 4 项由（292.1）—（292.2）的成本项；第 5 项由定理 293.2。每项只针对所列约化摘要作不可充分性断言，不声称完整模型中被删字段不能由其他字段推导。证毕。

**AHH 294.4（信息—后继全息）。** 反事实规划的完整边界不是一个“最有信息”的动作，而是

$$
\boxed{
\text{候选响应分割}
+
\text{共同来源与先验}
+
\text{最坏/平均目标}
+
\text{成本与 Bellman 后继}
+
\text{停止语义}
}.
$$

**新的 AHH 时刻是：一条低概率的危险后继可以比许多平均信息增益更重要；真正的全息边界必须同时保存“平均会学到什么”和“最坏会被带到哪里”。**

**来源与边界 294.5。** 本批在有限候选类、有限确定性干预、有限结果字母表、严格减少类数和固定资源/停止合同下，给出平均/最坏残余、Bellman 规划递推、停止语义分离和信息—后继全息。使用的是有限决策树与条件后继的标准推导；没有把平均信息增益推广成普适最优性，没有覆盖连续状态、随机策略或一般非线性系统，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 295. 噪声干预：响应分割变成证据核

上一批的确定性响应把候选类直接切成互不相交的分支。现实的局域记录通常带有噪声：同一个候选类在同一干预下可以给出多个结果，不同候选类也可能给出相同结果。此时，边界不能只保留“哪些类仍有可能”，还必须保留各类对结果的似然权重。

**定义 295.1（有限证据核与历史后验）。** 设 $K$ 是有限候选类集，$\mathcal A$ 是有限干预集。对每个 $a\in\mathcal A$，给定有限结果字母表 $Y_a$ 和证据核

$$
L_a:Y_a\times K\longrightarrow[0,1],
\qquad
\sum_{y\in Y_a}L_a(y\mid k)=1.
$$

先验 $p$ 满足 $p(k)\ge0$ 且 $\sum_{k\in K}p(k)=1$。一条有限记录词写成

$$
 h=((a_1,y_1),\ldots,(a_m,y_m)).
$$

定义其类条件似然、证据和后验为

$$
\Lambda_h(k)=\prod_{i=1}^{m}L_{a_i}(y_i\mid k),
\qquad
Z_h=\sum_{k\in K}p(k)\Lambda_h(k),
$$

$$
\boxed{
 p_h(k)=\frac{p(k)\Lambda_h(k)}{Z_h}
 }
\tag{295.1}
$$

其中只对 $Z_h>0$ 的可实现历史定义后验。给定后验 $p_h$，下一干预 $a$ 的预测结果分布为

$$
\boxed{
 q_{p_h}^{a}(y)=\sum_{k\in K}p_h(k)L_a(y\mid k).
}
\tag{295.2}
$$

若 $q_{p_h}^{a}(y)>0$，取得结果 $y$ 后的后验为

$$
\boxed{
 p_h^{a,y}(k)=
 \frac{p_h(k)L_a(y\mid k)}{q_{p_h}^{a}(y)}.
}
\tag{295.3}
$$

**定理 295.2（后验是带噪声续接的充分边界）。** 固定剩余的允许干预、成本、记录权限和终端损失合同。若两条可实现历史 $h,h'$ 具有相同后验

$$
 p_h=p_{h'},
$$

则对任意同一后续策略，它们的每条后续结果词的条件概率相同；终端决策的最优风险、最优期望成本以及所有合法后继集合也相同。

### 证明

对后续长度作归纳。长度为零时，终端损失只依赖后验和终端决策，结论成立。设下一步选择干预 $a$。由（295.2），两条历史的下一结果分布相同。对每个正概率结果 $y$，由 Bayes 公式（295.3），两条历史的后验后继也相同。归纳假设遂给出每个 $y$ 分支上的相同后续分布、风险和成本；按（295.2）加权即得当前结论。若策略允许根据记录选择下一干预，则两条历史具有相同后验和相同剩余合同，策略所作选择也相同。证毕。

**例 295.3（相同支持不等于相同边界）。** 令 $K=\{0,1\}$。两条历史的后验分别为

$$
 p_h(0)=p_h(1)=\frac12,
\qquad
 p_{h'}(0)=\frac9{10},\quad p_{h'}(1)=\frac1{10}.
$$

二者的支持都是整个 $K$，但在零—一损失下的最优立即决策风险分别为 $1/2$ 和 $1/10$。因此，仅保存“哪些候选仍未被排除”的支持纤维，不能决定后续置信度、停止时刻或平均成本；必须保留后验权重。

### 证明

零—一损失下选择后验最大类，条件错误概率为 $1-\max_kp(k)$。代入两组后验即得。证毕。

**AHH 295.4（从分割到证据）。** 当干预结果不是确定性标签时，关系边界从

$$
\text{候选类的集合分割}
$$

升级为

$$
\boxed{
\text{共同来源与先验}
+
\text{每个干预的证据核}
+
\text{记录词的似然乘积}
+
\text{可继续使用的后验后继}.
}
$$

## 296. 信息退化：可见结果被怎样压缩，同样属于边界

同一个干预结果还可能经过分类器、压缩器或不可逆记录接口。只保存压缩后的结果，会不会损失决策能力，取决于它是否只是一个与候选类无关的随机退化。

**定义 296.1（实验与随机退化）。** 对固定候选集 $K$，一个有限实验 $E$ 具有结果集 $Z$ 和核

$$
E(z\mid k),
\qquad
\sum_zE(z\mid k)=1.
$$

另一个实验 $F$ 具有结果集 $W$。若存在与 $k$ 无关的随机核 $T(w\mid z)$，使

$$
\boxed{
F(w\mid k)=\sum_{z\in Z}T(w\mid z)E(z\mid k),
}
\tag{296.1}
$$

则称 $F$ 是 $E$ 的随机退化，记作 $E\succeq F$。

给定先验 $p$、有限决策集 $D$ 和损失 $\ell:K\times D\to[0,\infty)$，定义实验 $E$ 的 Bayes 风险

$$
\boxed{
\mathcal R_E(p)
=
\sum_{z\in Z}
\min_{d\in D}
\sum_{k\in K}p(k)E(z\mid k)\ell(k,d).
}
\tag{296.2}
$$

**定理 296.2（随机退化不能增加信息）。** 若 $E\succeq F$，则对任意先验 $p$、决策集 $D$ 和损失函数 $\ell$，有

$$
\boxed{
\mathcal R_E(p)\le\mathcal R_F(p).
}
$$

### 证明

对每个 $z$ 和决策 $d$，置

$$
 u_z(d)=\sum_kp(k)E(z\mid k)\ell(k,d).
$$

由（296.1），对每个 $w$ 有

$$
\sum_kp(k)F(w\mid k)\ell(k,d)
=
\sum_zT(w\mid z)u_z(d).
$$

有限决策集上的逐点不等式

$$
\min_d\sum_zT(w\mid z)u_z(d)
\ge
\sum_zT(w\mid z)\min_d u_z(d)
$$

成立。对 $w$ 求和，并使用 $\sum_wT(w\mid z)=1$，得到

$$
\begin{aligned}
\mathcal R_F(p)
&\ge
\sum_w\sum_zT(w\mid z)\min_du_z(d)\\
&=
\sum_z\min_du_z(d)
=\mathcal R_E(p).
\end{aligned}
$$

证毕。

**例 296.3（严格损失）。** 令 $K=\{0,1\}$，先验均匀，零—一损失。实验 $E$ 直接返回候选类 $z=k$，故 $\mathcal R_E(p)=0$。令 $T$ 把两个结果都压成同一个符号 $w_0$，则退化实验 $F$ 与候选类无关，故 $\mathcal R_F(p)=1/2$。压缩记录没有创造新的区分能力。

### 证明

$E$ 的结果已经确定 $k$，最优错误率为零；$F$ 的唯一结果不含关于 $k$ 的信息，任何固定决策在均匀先验下错误率均为 $1/2$。证毕。

**推论 296.4（全息边界必须记录退化关系）。** 若两个关系体具有相同的压缩结果分布，却对应不同的原始实验 $E$ 及退化核 $T$，则仅凭压缩分布不能判断某个未来决策的最小 Bayes 风险。只有把原始证据核、或足以恢复其相对于任务族的退化关系，一并纳入边界，才能应用定理 296.2。

### 证明

例 296.3 中，完全揭示实验和完全压缩实验可以在某些单一固定决策读数上被人为配成相同的边缘分布，但它们对允许决策族的 Bayes 风险不同。故压缩结果分布本身不是任务充分边界；定理 296.2 所需的核关系必须保留。证毕。

## 297. 置信度停止：后验阈值与资源递推

带噪声记录不会像确定性分割那样在一次结果后删除全部不相容类。于是，停止不能只用“候选数是否为一”，而应由任务误差阈值和剩余资源共同决定。

**定义 297.1（后验风险与置信停止）。** 在零—一损失下，定义后验 Bayes 风险

$$
 r(p)=1-\max_{k\in K}p(k).
$$

给定置信阈值 $\varepsilon\in[0,1)$，称历史 $h$ 达到置信停止，若

$$
\operatorname{Stop}_\varepsilon(h)
\quad\Longleftrightarrow\quad
 r(p_h)\le\varepsilon.
$$

停止时取最大后验类作为决策 $\widehat k(h)$。假定策略在有限资源合同下以概率一停止。

**定理 297.2（局部后验阈值给出全局错误界）。** 任意只在满足 $\operatorname{Stop}_\varepsilon$ 的历史停止的策略，其最终决策错误概率满足

$$
\boxed{
\Pr[\widehat k\ne k]\le\varepsilon.
}
$$

### 证明

对每一条停止历史 $h$，最大后验决策的条件错误概率为

$$
\Pr[\widehat k(h)\ne k\mid h]=r(p_h)\le\varepsilon.
$$

将条件概率按所有停止历史分解：

$$
\Pr[\widehat k\ne k]
=
\sum_h\Pr(h)\Pr[\widehat k(h)\ne k\mid h]
\le
\sum_h\Pr(h)\varepsilon
=\varepsilon.
$$

有限停止使该和为有限和；若按可数历史取极限，同一不等式由单调收敛成立。证毕。

**定义 297.3（带预算的置信 Bellman 值）。** 假定每个干预成本 $c(a)$ 是正整数，给定剩余预算 $B\in\mathbb N$。令 $C_\varepsilon(p,B)$ 为达到 $r(p)\le\varepsilon$ 所需的最小期望附加成本。对 $r(p)\le\varepsilon$，置

$$
C_\varepsilon(p,B)=0.
$$

对 $r(p)>\varepsilon$，对每个满足 $c(a)\le B$ 的干预，令

$$
q_p^a(y)=\sum_kp(k)L_a(y\mid k),
\qquad
p^{a,y}(k)=\frac{p(k)L_a(y\mid k)}{q_p^a(y)}
\quad(q_p^a(y)>0).
$$

定义

$$
\boxed{
C_\varepsilon(p,B)
=
\min_{a:c(a)\le B}
\left[
 c(a)+
 \sum_{y:q_p^a(y)>0}
 q_p^a(y)C_\varepsilon(p^{a,y},B-c(a))
\right],
}
\tag{297.1}
$$

若没有可行干预，或某个正概率后继在剩余预算下不能达到阈值，则相应值为 $+\infty$。

**定理 297.4（有限预算的置信 Bellman 充要性）。** 在上述正整数成本、有限干预集和有限结果集条件下，式（297.1）等于达到置信阈值所需的最小期望附加成本；$+\infty$ 恰表示不存在满足阈值的合法策略。

### 证明

对预算 $B$ 作归纳。若当前后验已经满足阈值，立即停止且成本为零。若不满足，任何合法策略必须先选择某个成本不超过 $B$ 的干预 $a$，支付 $c(a)$；取得正概率结果 $y$ 后，Bayes 后验是 $p^{a,y}$，剩余预算是 $B-c(a)$。由归纳假设，该分支的最小期望后继成本为 $C_\varepsilon(p^{a,y},B-c(a))$，对结果概率 $q_p^a(y)$ 加权，再对第一步干预取最小，正好得到（297.1）。若不存在可行第一步，任何策略都不可能达到阈值，值为 $+\infty$。证毕。

**AHH 297.5（停止由风险而非候选数决定）。** 确定性响应的“单类停止”只是置信任务的一个特殊极限。带噪声的关系体必须把后验风险、允许误差、剩余预算和每个结果的后验后继一起保留；否则“暂时没有新候选被排除”会被误报成“没有必要继续测量”。

## 298. AHH：证据核、退化与置信后继的联合边界

**定义 298.1（证据—后继全息边界）。** 对有限候选关系体和有限自适应测量协议，定义

$$
\boxed{
\eta_{\mathrm{evidence}}
=
\left(
\text{候选类与共同先验},
\text{干预证据核},
\text{历史似然与后验更新},
\text{可访问的退化/恢复关系},
\text{损失与置信阈值},
\text{成本、预算与停止后继}
\right).
}
\tag{298.1}
$$

**定理 298.2（证据—后继边界的条件充分性）。** 在有限候选类、有限干预和结果字母表、条件独立的已声明证据核、有限正整数成本及固定决策损失合同下，两个关系体若具有相同的 $\eta_{\mathrm{evidence}}$，则对每条可实现记录词给出相同的：

1. 记录词概率与后验分布；
2. 任意有限续接策略的结果分布和终端 Bayes 风险；
3. 所有随机退化关系下的 Bayes 风险比较；
4. 给定置信阈值和预算的 Bellman 值、可行策略与停止判定。

### 证明

第 1 项由定义 295.1—295.3 的似然乘积和 Bayes 更新。第 2 项由定理 295.2 对每个后续长度归纳。第 3 项由定理 296.2 的核分解和相同损失合同。第 4 项由定理 297.2、297.4 及相同的成本和预算字段。相同边界逐项给出相同的记录—后继树。证毕。

**定理 298.3（删除证据字段的不可充分性）。** 下列约化摘要均存在反例：

1. 只保存后验支持而删除权重：例 295.3 的停止风险不同；
2. 只保存压缩结果分布而删除原始核及退化关系：推论 296.4 的 Bayes 风险比较不可恢复；
3. 删除共同先验：相同似然核可产生不同后验和不同平均规划；
4. 删除损失或置信阈值：同一后验可以对应不同的停止决定；
5. 删除预算和成本：同一后验更新树的可行策略集合不同。

### 证明

第 1 项由例 295.3；第 2 项由推论 296.4；第 3 项直接改变（295.1）和（297.1）的权重；第 4 项由定义 297.1；第 5 项由（297.1）中的资源参数。每项只针对所列约化摘要给出不可充分性反例，不声称被删字段不能由完整模型的其他字段推导。证毕。

**AHH 298.4（证据—后继全息）。** 带噪声的粒子式记录不是一次把候选体切成若干硬块，而是用证据核连续重加权关系体。真正充分的边界必须同时保存

$$
\boxed{
\text{哪些结果可能出现}
+
\text{各结果对共同来源的似然}
+
\text{记录后的后验}
+
\text{可逆或不可逆的记录退化}
+
\text{风险、预算与停止后继}
}.
$$

**新的 AHH 时刻是：噪声并没有把“粒子式事件”变成模糊的失败点击；它把事件的意义从“排除哪些类”改成“怎样重新加权哪些未来仍可继续”。因此，观察者真正携带的不是一串裸结果，而是结果对共同来源及后续任务的可计算作用。**

**来源与边界 298.5。** 本批在有限候选类、有限干预和有限结果字母表、条件独立的已声明证据核、随机退化通道、有限正整数成本与置信停止合同下，给出后验充分性、随机退化的 Bayes 风险单调性、置信度错误界、后验 Bellman 递推和证据—后继全息。没有把条件独立推广到带未记录记忆的过程，没有把 Blackwell 退化结论推广为任意信息指标的全序，也没有把有限预算递推推广到连续时间、未知噪声或一般非线性系统；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 299. 不确定证据：后验必须和未来核共同携带

上一批假定每个干预的证据核已经知道。若仪器校准、环境耦合或共同来源本身只知道属于一个有限模型族，那么一次记录得到的不是单一后验，而是一族与未来响应相连的后验—核对。

**定义 299.1（模型索引的后验—核束）。** 设有限候选类集为 $K$，有限模型族为 $\mathfrak M$。每个模型 $m\in\mathfrak M$ 给出先验 $p_m$ 和证据核

$$
L^m_a(y\mid k),
\qquad
\sum_{y\in Y_a}L^m_a(y\mid k)=1.
$$

对记录词 $h=((a_1,y_1),\ldots,(a_r,y_r))$，定义模型 $m$ 下的证据

$$
Z^m_h
=
\sum_{k\in K}p_m(k)
\prod_{i=1}^{r}L^m_{a_i}(y_i\mid k).
$$

当 $Z^m_h>0$ 时，定义模型条件后验

$$
 p^m_h(k)=
 \frac{p_m(k)\prod_iL^m_{a_i}(y_i\mid k)}{Z^m_h}.
$$

定义历史 $h$ 的模型索引后验—核束

$$
\boxed{
\mathcal B_h
=
\left\{
\left(m,p^m_h,(L^m_a)_{a\in\mathcal A}\right):
 m\in\mathfrak M, Z^m_h>0
\right\}.
}
\tag{299.1}
$$

模型标签 $m$ 表示同一个全局来源假设在后续历史中继续保持；它不能在每个结果分支后被无记录地换成另一个模型。

**定理 299.2（后验—核束的续接充分性）。** 固定剩余干预、资源、记录权限和终端损失合同。若两条历史 $h,h'$ 的模型索引后验—核束相同，即

$$
\mathcal B_h=\mathcal B_{h'},
$$

则它们对任意有限续接策略给出相同的鲁棒结果集合、相同的最坏终端风险和相同的最优资源值。

### 证明

对续接长度作归纳。对束中每个模型 $m$，下一干预 $a$ 在结果 $y$ 上的条件概率为

$$
q^m_h(y\mid a)=\sum_kp^m_h(k)L^m_a(y\mid k).
$$

因此相同的束给出相同的模型逐项预测。对正概率结果，Bayes 更新把 $p^m_h$ 变成

$$
 p^{m,a,y}_h(k)
=
 \frac{p^m_h(k)L^m_a(y\mid k)}{q^m_h(y\mid a)},
$$

未来核仍由同一模型 $m$ 提供，所以更新后的束也相同。归纳假设给出各模型的相同后续分布、风险和资源值；对模型集合取相应的最坏值或最优值，结论仍相同。证毕。

**例 299.3（相同当前后验、不同未来可见性）。** 令 $K=\{0,1\}$，当前记录为空，两个模型都给出均匀后验

$$
 p^{m_+}(0)=p^{m_-}(0)=\frac12.
$$

在下一干预 $a$ 下，模型 $m_+$ 的结果完全揭示候选类：

$$
L^{m_+}_a(y\mid k)=\mathbf 1_{y=k},
$$

而模型 $m_-$ 的结果与候选类无关：

$$
L^{m_-}_a(0\mid k)=L^{m_-}_a(1\mid k)=\frac12.
$$

两模型的当前后验集合都是单点 $\{(1/2,1/2)\}$，但零—一损失下执行 $a$ 后的终端风险分别为 $0$ 与 $1/2$。所以只保存当前后验集合而删除其与未来证据核的配对，不能决定后续任务。

### 证明

在 $m_+$ 中结果 $y$ 直接确定 $k$；在 $m_-$ 中结果独立于 $k$，后验保持均匀。代入 $1-\max_kp(k)$ 即得。证毕。

**AHH 299.4（来源身份进入边界）。** 当证据核未知但属于共同来源模型族时，充分边界不再是一个静态后验集合，而是

$$
\boxed{
\text{模型身份与共同先验}
+
\text{当前后验}
+
\text{该模型对所有未来干预的核}
+
\text{模型在不同历史之间的持续耦合}.
}
$$

## 300. 鲁棒后验：不确定性集合的包含关系与决策单调性

保留模型束后，可以定义对模型不确定性的保守决策。这里的“鲁棒”是相对于声明的模型族取最坏值；它不是从有限数据自动推出的频率保证。

**定义 300.1（束上的鲁棒终端风险）。** 对有限模型束 $\mathcal B$，其中每个元素含后验 $p$，给定有限决策集 $D$ 和损失 $\ell:K\times D\to[0,\infty)$，定义

$$
\boxed{
R_{\mathrm{rob}}(\mathcal B)
=
\min_{d\in D}
\max_{(m,p,L)\in\mathcal B}
\sum_{k\in K}p(k)\ell(k,d).
}
\tag{300.1}
$$

若允许在取得下一个结果后继续决策，则把每个束元素的核 $L$ 与同一模型标签一起带入后继束，并对每个后继使用相同的鲁棒合同。

**定理 300.2（模型束包含的鲁棒单调性）。** 若两个束满足

$$
\mathcal B_1\subseteq\mathcal B_2,
$$

则

$$
\boxed{
R_{\mathrm{rob}}(\mathcal B_1)\le
R_{\mathrm{rob}}(\mathcal B_2).
}
$$

对任意固定有限续接协议，协议的最坏期望终端损失也具有同样的包含单调性。

### 证明

对每个固定决策 $d$，有限集合上的最大值满足

$$
\max_{b\in\mathcal B_1}r_b(d)
\le
\max_{b\in\mathcal B_2}r_b(d),
$$

其中 $r_{(m,p,L)}(d)=\sum_kp(k)\ell(k,d)$。对两边分别取 $d$ 的最小值得到（300.1）的不等式。固定续接协议后，终端损失是每个模型元素的一个非负期望；同样的最大值包含关系逐项成立。证毕。

**推论 300.3（加入模型是保守化，删除模型是承诺）。** 扩大模型族不会改善声明的最坏风险；删除一个仍可能的模型可能严格降低数值，却同时缩小了关系边界允许的未来。

### 证明

第一项由定理 300.2。若被删除模型在某个决策上实现原最大值，则删除后最大值严格下降。此时下降来自改变来源合同，而不是来自同一合同内的免费信息。证毕。

**例 300.4（严格的鲁棒代价差）。** 在 $K=\{0,1\}$、决策集 $D=\{0,1\}$ 和零—一损失下，若束只含均匀后验，则鲁棒风险为 $1/2$。若束加入一个后验 $p(0)=1$ 的模型，则最优固定决策可把该模型的损失降为零，但束中的均匀模型仍使最坏风险保持 $1/2$；若相反只保留确定模型，风险降为零。由此可见，风险数值必须连同模型族边界解释。

### 证明

对均匀后验，任一固定决策错误率为 $1/2$；对确定后验，选择类 $0$ 可得零错误。代入（300.1）即得。证毕。

**AHH 300.5（鲁棒边界不是一个区间）。** 逐坐标给出概率下界和上界，通常不能恢复模型之间的共同约束；可执行的后继由整个束及其模型标签决定。全息边界需要保存“哪些不确定性可以共同实现”，而不能只保存每个参数的独立区间。

## 301. 非矩形来源：逐分支最坏递推会过度悲观

确定性规划和已知噪声 Bellman 递推都隐含一个重要选择：不同结果分支上的不确定性是否可以由同一个共同来源同时实现。若来源集合不是矩形的，逐分支各取最坏模型会制造一个现实中不存在的拼接来源。

**定义 301.1（全局与逐分支鲁棒值）。** 设一次固定协议产生有限结果集 $Y$。每个全局模型 $m\in\mathfrak M$ 给出结果概率 $q_m(y)$ 和非负终端损失 $g_m(y)$。全局共同来源的最坏期望损失为

$$
\boxed{
J_{\mathrm{global}}(\mathfrak M)
=
\max_{m\in\mathfrak M}
\sum_{y\in Y}q_m(y)g_m(y).
}
\tag{301.1}
$$

允许每个结果分支独立选取一个模型 $m_y\in\mathfrak M$ 的逐分支矩形化值为

$$
\boxed{
J_{\mathrm{rect}}(\mathfrak M)
=
\sum_{y\in Y}
\max_{m\in\mathfrak M}q_m(y)g_m(y).
}
\tag{301.2}
$$

（301.2）是把同一模型身份在各分支之间的耦合删去后的上界；它不自动代表任何真实全局来源。

**定理 301.2（矩形化上界与等式条件）。** 对任意有限模型族，

$$
\boxed{
J_{\mathrm{global}}(\mathfrak M)
\le
J_{\mathrm{rect}}(\mathfrak M).
}
$$

若存在某个模型 $m^*$，同时对每个 $y$ 达到（301.2）中的分支最大值，则等号成立。否则不排除严格不等式。

### 证明

对任意固定 $m$ 和每个 $y$，有

$$
q_m(y)g_m(y)
\le
\max_{m'\in\mathfrak M}q_{m'}(y)g_{m'}(y).
$$

对 $y$ 求和，再对 $m$ 取最大得到第一式。若同一 $m^*$ 在所有分支同时达到右侧最大值，逐项不等式均为等式，故总和相等。证毕。

**例 301.3（非矩形耦合造成严格差距）。** 取 $Y=\{0,1\}$，两个全局模型都给出

$$
q_{m_1}(0)=q_{m_1}(1)=q_{m_2}(0)=q_{m_2}(1)=\frac12,
$$

但终端损失为

$$
(g_{m_1}(0),g_{m_1}(1))=(0,1),
\qquad
(g_{m_2}(0),g_{m_2}(1))=(1,0).
$$

于是

$$
J_{\mathrm{global}}(\mathfrak M)=\frac12,
\qquad
J_{\mathrm{rect}}(\mathfrak M)=1.
$$

逐分支最坏递推把 $m_1$ 的零分支和 $m_2$ 的零分支拼在一起，形成了一个不属于原模型族的虚构来源。

### 证明

两模型各自的期望损失都是 $1/2$，所以（301.1）为 $1/2$；对每个分支，$q_m(y)g_m(y)$ 的最大值都是 $1/2$，两项相加得到 $1$。证毕。

**推论 301.4（鲁棒 Bellman 的共同来源条件）。** 把每个结果分支的最坏后继值分别相加，只有在声明的来源族对这些分支具有矩形闭合，或明确接受矩形化上界时，才可解释为同一鲁棒过程的精确值。否则它只是一个保守上界。

### 证明

定理 301.2 给出任意逐分支矩形化的上界；例 301.3 表明该上界可以严格大于共同来源下的真实最坏值。因此，若没有矩形闭合或额外上界合同，不能把（301.2）冒称为原过程的 Bellman 等式。证毕。

## 302. AHH：共同来源、鲁棒后验与矩形化合同

**定义 302.1（鲁棒证据全息边界）。** 对有限不确定关系体和有限自适应测量协议，定义

$$
\boxed{
\eta_{\mathrm{robust}}
=
\left(
\text{全局模型族与共同先验},
\text{模型索引后验—核束},
\text{可共同实现的来源约束},
\text{鲁棒损失与模型包含关系},
\text{矩形化/非矩形化合同},
\text{资源、预算与停止后继}
\right).
}
\tag{302.1}
$$

**定理 302.2（鲁棒证据边界的条件充分性）。** 在有限模型族、有限干预和结果字母表、已声明的模型内条件独立、有限成本与固定鲁棒损失合同下，两个关系体若具有相同的 $\eta_{\mathrm{robust}}$，则对每条可实现记录词给出相同的：

1. 模型逐项后验、可实现后验束和未来证据预测；
2. 固定策略的鲁棒终端风险与模型包含单调性；
3. 共同来源下的全局最坏值，以及接受矩形化后得到的上界；
4. 给定资源与停止规则的鲁棒后继和可行策略集合。

### 证明

第 1 项由定义 299.1 和定理 299.2；第 2 项由定义 300.1、定理 300.2 和推论 300.3；第 3 项由定义 301.1、定理 301.2 及其等式条件；第 4 项由相同的成本、预算、停止和来源耦合字段逐步应用前三项。证毕。

**定理 302.3（删除共同来源字段的不可充分性）。** 下列约化摘要均存在反例：

1. 删除模型与未来核的配对，只保留当前后验：例 299.3 的未来风险不同；
2. 删除模型族的包含结构：推论 300.3 的鲁棒风险单调性无法判定；
3. 把非矩形来源自动矩形化：例 301.3 的最坏值从 $1/2$ 被抬高为 $1$；
4. 删除矩形化合同：同一逐分支上界无法判断是精确值还是保守值；
5. 删除共同来源与停止后继：相同局部记录可以对应不同的可行继续策略。

### 证明

第 1 项由例 299.3；第 2 项由模型集合包含改变后的定理 300.2；第 3 项由例 301.3；第 4 项由推论 301.4；第 5 项由资源和停止合同的定义。每项只对所删字段给出不可充分性反例，不声称完整模型中被删字段不能由其他字段推导。证毕。

**AHH 302.4（共同来源全息）。** 面对未知噪声或校准不确定性，真正的关系边界不是一组独立的参数区间，也不是每个分支各自挑一个最坏模型，而是

$$
\boxed{
\text{同一来源族可以同时实现哪些历史、后验和未来核}
+
\text{鲁棒决策如何对这族来源取最坏}
+
\text{矩形化是否是事实、假设还是仅仅上界}
+
\text{资源与停止后继怎样作用于上述共同约束}
}.
$$

**新的 AHH 时刻是：最坏情况也有“共同来源”这一几何。把每个分支的危险模型分别拼起来，确实得到一个保守安全壳，却可能描述一个从未存在的关系体；因此，鲁棒全息不仅要保存不确定性的大小，还要保存不确定性之间能否共同实现。**

**来源与边界 302.5。** 本批在有限全局模型族、有限候选类、有限干预和结果字母表、模型内条件独立、固定鲁棒损失及资源/停止合同下，给出模型索引后验—核束的充分性、模型族包含的鲁棒单调性、非矩形来源的逐分支上界及严格反例，并定义共同来源—鲁棒—矩形化联合全息边界。没有把模型不确定性自动解释为频率置信区间，没有把非矩形来源的上界冒称 Bellman 等式，也没有覆盖连续模型、未知记忆过程或一般非线性动力学；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 303. 共同模型族上的鲁棒实验支配

第 296 节的 Blackwell 结论比较单一实验核的退化。面对模型族时，还要要求退化映射对所有共同来源模型使用同一个记录通道；否则“信息更少”可能只是换了来源合同。

**定义 303.1（模型族实验与共享退化）。** 固定有限模型束

$$
\mathcal B=\{(m,p_m):m\in\mathfrak M\},
$$

以及有限决策集 $D$ 和损失 $\ell:K\times D\to[0,\infty)$。实验 $E$ 对每个模型 $m$ 给出结果集 $Z$ 和核 $E_m(z\mid k)$。允许随机决策规则 $\delta(d\mid z)$，满足 $\sum_d\delta(d\mid z)=1$。定义其模型风险和鲁棒风险为

$$
L_m(E,\delta)
=
\sum_{z,k,d}p_m(k)E_m(z\mid k)\delta(d\mid z)\ell(k,d),
$$

$$
\boxed{
R_{\mathcal B}^*(E)
=
\min_{\delta}\max_{m\in\mathfrak M}L_m(E,\delta).
}
\tag{303.1}
$$

若实验 $F$ 的结果集为 $W$，存在与模型 $m$ 和候选类 $k$ 都无关的随机核 $T(w\mid z)$，使

$$
F_m(w\mid k)=\sum_{z\in Z}T(w\mid z)E_m(z\mid k)
\qquad\forall m,k,w,
$$

则称 $E$ 对整个模型族共享支配 $F$，记作 $E\succeq_{\mathfrak M}F$。

**定理 303.2（共享 Blackwell 支配的鲁棒单调性）。** 若 $E\succeq_{\mathfrak M}F$，则

$$
\boxed{
R_{\mathcal B}^*(E)\le R_{\mathcal B}^*(F).
}
$$

### 证明

任取 $F$ 上的随机决策规则 $\delta_F$。在取得 $E$ 的结果 $z$ 后，先按 $T(\cdot\mid z)$ 生成一个模拟结果 $w$，再按 $\delta_F(\cdot\mid w)$ 决策。这给出 $E$ 上的规则

$$
\delta_E(d\mid z)=\sum_wT(w\mid z)\delta_F(d\mid w).
$$

对每个模型 $m$，将此式代入 $L_m$，并使用（303.1）中的共享核关系，得到

$$
L_m(E,\delta_E)=L_m(F,\delta_F).
$$

因此 $E$ 至少可以复现 $F$ 的每个模型风险；分别取模型最大值，再对规则取最小值，得到结论。证毕。

**例 303.3（模型依赖的压缩不能冒称共享退化）。** 令两个模型在同一二元结果上使用相反的标签约定：模型 $m_1$ 的 $E$ 直接返回 $z=k$，模型 $m_2$ 的 $E$ 返回 $z=1-k$。若某个压缩器在 $m_1$ 上把 $z$ 保留、在 $m_2$ 上把它翻回候选类，则这个“压缩器”依赖隐藏模型标签，不能作为一个单一的 $T(w\mid z)$。把它写成共享退化会错误地给模型族增加一个不可访问的校准端口。

### 证明

同一个输入结果 $z$ 在两个模型下要求不同的输出变换；不存在同时满足两种变换的模型无关 $T$。因此该操作属于扩大的模型识别或校准合同，而不是原结果接口上的随机后处理。证毕。

**AHH 303.4（支配关系也有来源量词）。** 在不确定关系体上，“实验 $E$ 比实验 $F$ 信息更多”必须带有共同模型族的量词：同一个退化核要对所有允许来源同时成立。若退化映射偷偷读取了模型身份，比较的已经是另一份边界。

## 304. 共享策略与知道来源后的神谕策略

鲁棒规划中的策略必须在不知道真实模型标签时共同适用。若把每个模型的最优策略分别取出再比较，会把不可访问的来源身份当成额外观测。

**定义 304.1（共享值与神谕值）。** 设有限模型族为 $\mathfrak M$，有限共享策略集为 $\Pi$。固定策略 $\pi$ 在模型 $m$ 下的终端期望损失记为 $L_m(\pi)\ge0$。定义

$$
\boxed{
V_{\mathrm{shared}}
=
\min_{\pi\in\Pi}\max_{m\in\mathfrak M}L_m(\pi),
}
\tag{304.1}
$$

以及允许先知道模型标签再选策略的神谕值

$$
\boxed{
V_{\mathrm{oracle}}
=
\max_{m\in\mathfrak M}\min_{\pi\in\Pi}L_m(\pi).
}
\tag{304.2}
$$

**定理 304.2（共享策略的 minimax 间隙）。** 总有

$$
\boxed{
V_{\mathrm{oracle}}\le V_{\mathrm{shared}}.
}
$$

若存在同一策略 $\pi^*$ 同时达到每个模型的单模型最小值，即

$$
L_m(\pi^*)=\min_{\pi\in\Pi}L_m(\pi)
\quad\forall m,
$$

则两值相等。没有这个共同最优策略时，不排除严格间隙。

### 证明

对任意共享策略 $\pi$ 和任意模型 $m$，有

$$
\min_{\pi'\in\Pi}L_m(\pi')\le L_m(\pi).
$$

对 $m$ 取最大，再对 $\pi$ 取最小，得到（304.2）不超过（304.1）。若 $\pi^*$ 同时达到各模型最小值，则

$$
\max_mL_m(\pi^*)
=
\max_m\min_\pi L_m(\pi),
$$

从而两值相等。证毕。

**例 304.3（严格的来源—策略间隙）。** 取两个模型和两个确定策略，损失矩阵为

$$
\begin{array}{c|cc}
 &\pi_0&\pi_1\\
\hline
m_0&0&1\\
m_1&1&0
\end{array}
$$

则每个模型的单模型最小损失都是零，所以 $V_{\mathrm{oracle}}=0$；但任一共享确定策略在某个模型下损失一，故 $V_{\mathrm{shared}}=1$。若另行声明可用一个不可观察模型独立的公平随机种子，混合两策略各半，则共享随机值可降为 $1/2$，但这已经是扩大的策略合同。

### 证明

直接代入（304.1）和（304.2）。随机混合后的两个模型风险都为 $1/2$。证毕。

**推论 304.4（模型标签不是免费后继）。** 把 $V_{\mathrm{oracle}}$ 当成实际鲁棒规划值，等价于在边界中加入“当前真实模型是谁”的记录。若该记录未列入允许接口，就必须使用 $V_{\mathrm{shared}}$ 或声明一个可证明的模型识别步骤。

### 证明

神谕策略按模型标签选择不同动作；共享策略在相同历史上必须使用同一动作。二者的差别正是一个额外模型标签端口。证毕。

## 305. 随机化策略：凸化是资源，而不是默认事实

随机化可以缩小共享 minimax 值，但只有在随机种子、混合时刻和后续是否可访问该种子都被声明时，它才是关系体的一部分。

**定义 305.1（策略风险向量与随机化闭包）。** 对有限确定策略集 $\Pi=\{\pi_1,\ldots,\pi_s\}$，定义模型风险向量

$$
v(\pi_i)=\bigl(L_m(\pi_i)\bigr)_{m\in\mathfrak M}
\in\mathbb R^{|\mathfrak M|}.
$$

随机化策略由概率向量 $\lambda\in\Delta_s$ 给出，先按 $\lambda$ 选取一个确定策略，并将该随机选择独立于隐藏模型。其风险向量为

$$
v(\lambda)=\sum_{i=1}^{s}\lambda_i v(\pi_i).
$$

定义确定值与随机值

$$
V_{\mathrm{det}}=\min_i\max_m v(\pi_i)_m,
\qquad
\boxed{
V_{\mathrm{rand}}=\min_{\lambda\in\Delta_s}\max_m v(\lambda)_m.
}
\tag{305.1}
$$

**定理 305.2（随机化的凸包刻画）。** 有

$$
\boxed{
V_{\mathrm{rand}}\le V_{\mathrm{det}},
\qquad
\{v(\lambda):\lambda\in\Delta_s\}
=\operatorname{conv}\{v(\pi_i):1\le i\le s\}.
}
$$

若确定风险向量的凸包有一点同时严格低于所有确定策略的最坏坐标，则不等式严格。

### 证明

风险对随机策略按全概率公式线性组合，所以第二个等式直接成立。每个顶点策略对应一个退化的 $\lambda$，故最小化范围包含全部确定策略，得到第一式。若凸包中某点的每个坐标都严格低于所有确定策略的相应最坏坐标，则其最大坐标严格小于 $V_{\mathrm{det}}$，从而不等式严格。证毕。

**例 305.3（随机化严格改善）。** 例 304.3 的两个风险向量为 $(0,1)$ 和 $(1,0)$。其凸包包含 $(1/2,1/2)$，所以 $V_{\mathrm{rand}}=1/2<V_{\mathrm{det}}=1$。

### 证明

两向量的凸组合为 $(\lambda,1-\lambda)$；其坐标最大值在 $\lambda=1/2$ 时最小，为 $1/2$。证毕。

**命题 305.4（随机源可见性改变后继）。** 若随机选择的种子在下一阶段可被记录，则后继策略可以条件于该种子；若种子不可见，只能使用混合后的风险向量。两种记录合同具有相同的当前平均风险时，仍可能具有不同的未来最优值。

### 证明

种子可见时，后继可以分别执行 $\pi_i$；不可见时，后继只能按未分裂的混合历史选择。取例 304.3，在第一阶段以公平种子选择 $\pi_0$ 或 $\pi_1$，若种子同时揭示模型标签，后继可把风险降为零；若种子不揭示模型，任一共享后继仍面对两个相反损失方向。故未来值由记录可见性决定。证毕。

**AHH 305.5（随机性进入边界）。** “允许随机策略”不是一个无害的算法实现细节。随机源的独立性、可见性、可复用性和是否计入资源，都会改变合法后继；把凸化收益写进边界，却删除随机源合同，会把一个不可执行的混合策略冒称为当前关系事实。

## 306. AHH：主动鲁棒证据的策略边界

**定义 306.1（主动鲁棒全息边界）。** 对有限模型族、有限实验协议和有限策略资源，定义

$$
\boxed{
\eta_{\mathrm{active\text{-}robust}}
=
\left(
\text{共同模型族与来源耦合},
\text{每模型证据核},
\text{共享/神谕策略量词},
\text{模型无关退化关系},
\text{随机源独立性与可见性},
\text{损失、成本、预算与停止后继}
\right).
}
\tag{306.1}
$$

**定理 306.2（主动鲁棒边界的条件充分性）。** 在有限模型族、有限候选类、有限结果字母表、已声明的模型内条件独立、有限资源和固定损失合同下，两个关系体若具有相同的 $\eta_{\mathrm{active\text{-}robust}$，则对每条可实现记录词给出相同的：

1. 共享实验之间的鲁棒支配关系与最小风险；
2. 共享策略、神谕策略和随机化策略的值及其间隙；
3. 模型无关记录退化下的可模拟后继；
4. 随机源可见性、预算和停止合同所允许的策略集合。

### 证明

第 1 项由定义 303.1、定理 303.2 及共享退化条件；第 2 项由定义 304.1—304.2、定理 304.2 和定理 305.2；第 3 项由模型无关核的模拟构造；第 4 项由命题 305.4 及相同的资源、记录和停止字段。相同边界逐项决定相同的主动鲁棒后继树。证毕。

**定理 306.3（删除策略字段的不可充分性）。** 下列约化摘要均存在反例：

1. 删除模型无关退化条件：例 303.3 把隐藏模型校准误当成可访问压缩；
2. 用神谕值替代共享值：例 304.3 把不可见模型标签当成现有记录；
3. 删除随机源合同：例 305.4 的相同平均风险具有不同后继值；
4. 删除模型耦合：第 301 节的逐分支矩形化上界严格高于共同来源值；
5. 删除预算与停止后继：同一实验风险向量可以有不同的可执行策略树。

### 证明

第 1 项由例 303.3；第 2 项由定理 304.2 和例 304.3；第 3 项由命题 305.4；第 4 项由例 301.3；第 5 项由资源合同改变可行策略集合这一直接构造。每项只对所删字段给出不可充分性反例，不声称完整边界中被删字段不能由其他字段推导。证毕。

**AHH 306.4（主动鲁棒证据全息）。** 对不确定关系体进行主动观察时，真正的边界不是“哪个动作平均最有信息”，而是

$$
\boxed{
\text{哪些来源必须共同解释所有历史}
+
\text{每个实验对这些来源的核}
+
\text{策略是否必须跨来源共享}
+
\text{记录退化是否模型无关}
+
\text{随机性和模型标签是否可见}
+
\text{资源与停止后继的合法域}
}.
$$

**新的 AHH 时刻是：主动测量的“自由选择”本身也是一种关系接口。知道来源标签、偷用模型依赖的压缩器、或无记录地调用随机种子，都会让规划数值变好；但那种变好来自偷偷扩大边界，而不是来自同一个关系体中的信息。**

**来源与边界 306.5。** 本批在有限共同模型族、有限实验核、有限共享策略、模型无关退化、显式随机化合同和有限资源/停止合同下，给出鲁棒 Blackwell 支配、共享—神谕 minimax 间隙、策略风险凸化、随机源可见性后继和主动鲁棒全息边界。没有把神谕策略当作可执行事实，没有把随机化收益推广到无记录随机源，没有把矩形化上界替代共同来源值，也没有覆盖连续模型、未知记忆过程或一般非线性控制；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 307. 静态证据核：何时可以安全合并记录顺序

若每次记录只给同一个固定候选类一个似然因子，而不改变后续证据核，那么记录顺序可能只是表示层细节。但这个结论依赖于静态共同来源合同，不能自动推广到会改变内部状态的干预。

**定义 307.1（静态证据算子）。** 对有限候选类集 $K$ 和证据核 $L_a(y\mid k)$，在非负权重空间 $\mathbb R_{\ge0}^{K}$ 上定义分支算子

$$
\boxed{
(M_{a,y}w)(k)=L_a(y\mid k)w(k).
}
\tag{307.1}
$$

给定初始先验权重 $w_0=p$，记录词 $h=((a_1,y_1),\ldots,(a_r,y_r))$ 的未归一化权重为

$$
w_h=M_{a_r,y_r}\cdots M_{a_1,y_1}w_0.
$$

其证据概率为 $Z_h=\sum_kw_h(k)$；当 $Z_h>0$ 时，后验为 $w_h/Z_h$。若存在模型族，则每个模型 $m$ 各自使用一套静态算子 $M^m_{a,y}$，并保留模型标签的共同来源约束。

**定理 307.2（静态记录的排列不变性）。** 对任意两个记录事件 $(a,y)$ 和 $(b,z)$，有

$$
M_{a,y}M_{b,z}=M_{b,z}M_{a,y}.
$$

因此，只要两条记录词包含相同的带结果事件多重集，且两种排列都满足同一资源合同，它们具有相同的未归一化权重、证据概率和后验。模型族情形下，各模型的后验—核束也相同。

### 证明

对任意 $k\in K$，

$$
(M_{a,y}M_{b,z}w)(k)
=L_a(y\mid k)L_b(z\mid k)w(k)
=(M_{b,z}M_{a,y}w)(k).
$$

所以相邻交换不改变权重；任意排列都可由有限次相邻交换得到，结论随之成立。模型族中逐模型使用同一交换等式，再保留共同模型标签即可。证毕。

**推论 307.3（合并顺序的适用范围）。** 在定理 307.2 的合同内，观察者可以把记录词压缩成带结果事件的多重集，而不会改变当前后验或任何只依赖该后验—核束的未来任务。若动作选择本身依赖先前结果，只有在交换后仍是合法记录、且剩余资源和可用动作相同的排列之间才能使用该压缩。

### 证明

前件由定理 307.2 和第 299 节的后验—核束充分性得到。合法性与资源条件不是似然乘积的一部分，必须另行保持。证毕。

**例 307.4（静态合并的数值核对）。** 取 $K=\{0,1\}$，两次结果均为 $0$，并令

$$
L_a(0\mid0)=\frac34,\quad L_a(0\mid1)=\frac14,
$$

$$
L_b(0\mid0)=\frac23,\quad L_b(0\mid1)=\frac13.
$$

对均匀先验，两种顺序都给出未归一化权重 $(1/4,1/24)$，归一化后后验为 $(6/7,1/7)$。顺序被忘掉没有损失，因为两次算子是同一对角乘法的不同排列。

### 证明

第一分量为 $(1/2)(3/4)(2/3)=1/4$，第二分量为 $(1/2)(1/4)(1/3)=1/24$；乘法交换性给出另一顺序相同。证毕。

**AHH 307.5（可合并性来自算子交换）。** “忘掉时间顺序”不是一个一般的信息擦除许可。它只有在所有被交换的证据分支算子彼此交换、资源合同也不区分排列时，才是同一关系边界的商；否则它会合并本来不同的后继。

## 308. 状态性证据：非交换干预把顺序写进边界

若一次干预改变下一次干预所作用的状态，记录就不再是静态似然因子的乘积。顺序差异此时可以直接改变结果概率和后验，而不仅是改变记账方式。

**定义 308.1（带状态的分支映射）。** 令 $S$ 为有限内部状态集，权重空间为

$$
V=\mathbb R_{\ge0}^{K\times S}.
$$

一个带结果干预由非负线性映射

$$
T_{a,y}:V\to V
$$

给出；对固定 $a$，假定 $\sum_yT_{a,y}$ 保持总质量。记录词 $h=((a_1,y_1),\ldots,(a_r,y_r))$ 的未归一化联合权重为

$$
W_h=T_{a_r,y_r}\cdots T_{a_1,y_1}W_0.
$$

总质量给出记录概率，按总质量归一化并对 $S$ 求和得到候选类后验。

**定理 308.2（分支映射的交换判据）。** 若两个分支映射满足

$$
T_{a,y}T_{b,z}=T_{b,z}T_{a,y},
$$

则在任意初始权重和任意共同后继合同下，交换这两个相邻事件不会改变联合权重、记录概率或后验。若两映射不相等，则存在某个初始权重使交换改变联合权重；改变可以表现为记录概率不同、归一化后验不同，或二者同时不同。

### 证明

交换等式直接给出第一项；其余历史前后再乘同样的线性映射，结论保持。若 $TU\ne UT$，则线性映射差 $TU-UT$ 非零，存在 $W_0$ 使 $(TU-UT)W_0\ne0$。若两结果总质量不同，记录概率已不同；若总质量相同而归一化候选边缘不同，后验已不同。证毕。

**例 308.3（先翻转再读取与先读取再翻转）。** 令 $K=S=\{0,1\}$，初始内部状态等于候选类。干预 $F$ 无可见结果但把状态翻转 $s\mapsto1-s$；干预 $R$ 读取当前状态，结果 $y=s$，并保持状态不变。考虑结果为 $1$ 的读取分支 $R_1$：

- 先执行 $F$ 再取得 $R_1$，结果 $1$ 对应初始候选类 $k=0$；
- 先取得 $R_1$ 再执行 $F$，结果 $1$ 对应初始候选类 $k=1$。

两条记录都含有同一组操作名称 $\{F,R_1\}$，却给出互补的候选后验。把它们压成同一多重集会丢失实际干预顺序。

### 证明

第一种顺序把初始状态 $k$ 变成 $1-k$ 后读取，故 $R_1$ 当且仅当 $k=0$；第二种直接读取，故当且仅当 $k=1$。翻转和读取分支不交换。证毕。

**推论 308.4（状态扩展是顺序丢失的修复）。** 若把所有会被干预改变且会影响未来核的内部状态纳入 $S$，则顺序差异可以由分支映射复现；若把它删去而只保留候选类边缘，通常会把非交换过程错误地变成静态可交换证据。

### 证明

完整联合权重上的分支复合保留状态变化；只取候选类边缘会合并不同的 $S$ 分量。例 308.3 给出该合并导致不同后验的具体反例。证毕。

## 309. 可交换事件的 trace 商与主动规划

在许多协议中，只有部分事件可以交换。与其把全部顺序保留，或把全部顺序删除，可以只对已证明交换的相邻事件取商。

**定义 309.1（独立关系与 trace 等价）。** 令 $E$ 为带结果事件类型集，给定对称且反自反的关系 $I\subseteq E\times E$。若 $(e,f)\in I$，要求其分支映射交换、资源消耗可加且记录权限不区分两种排列。对事件词定义 trace 等价 $\equiv_I$ 为由局部变换

$$
u\,e\,f\,v\longleftrightarrow u\,f\,e\,v
\qquad ((e,f)\in I)
$$

生成的最小等价关系。

**定理 309.2（trace 商的后验充分性）。** 若每个独立事件对的分支映射满足交换条件，且两事件的资源与权限合同满足定义 309.1，则

$$
 h\equiv_I h'
$$

蕴含两条记录词具有相同的记录概率、联合后验、模型索引后验—核束和所有固定剩余合同下的鲁棒后继值。

### 证明

$h\equiv_Ih'$ 由有限次独立相邻交换组成。每次交换由定理 308.2 保持联合权重和记录概率；资源可加性和权限条件保持剩余合同。对每一步应用第 299 节的后验—核束充分性，迭代得到结论。证毕。

**推论 309.3（主动策略可以在 trace 类上规划）。** 若策略的下一步选择只依赖 trace 类、而不依赖被商掉的独立排列，则规划树可以在 trace 类上压缩；若策略依赖某个被商掉的时间戳或资源副作用，必须把该字段加入边界，不能使用该压缩。

### 证明

前件中，等价词给出相同后验和剩余合同，故策略输入相同。后件中，两个排列虽有相同物理证据，却向策略暴露不同的控制字段，商后无法恢复该选择。证毕。

**例 309.4（部分交换的三事件词）。** 设事件 $e_1,e_2$ 的分支映射交换，而 $e_2,e_3$ 不交换。词 $e_1e_2e_3$ 与 $e_2e_1e_3$ 属于同一 trace 类；词 $e_1e_2e_3$ 与 $e_1e_3e_2$ 一般不等价。前一对可共享同一个后验边界，后一对必须保留顺序或加入足以恢复非交换状态的字段。

### 证明

第一对由一次允许的相邻交换得到；第二对需要交换 $e_2,e_3$ 或其他未声明关系，不能由定义 309.1 推出。证毕。

## 310. AHH：顺序—证据—后继联合边界

**定义 310.1（顺序全息边界）。** 对有限候选类、有限内部状态、有限带结果干预和有限主动策略，定义

$$
\boxed{
\eta_{\mathrm{order}}
=
\left(
\text{共同来源与联合状态},
\text{每个分支映射},
\text{可交换事件关系与 trace 商},
\text{资源消耗和权限副作用},
\text{可见记录字段},
\text{鲁棒策略与停止后继}
\right).
}
\tag{310.1}
$$

**定理 310.2（顺序边界的条件充分性）。** 在有限状态、有限事件字母表、非负质量保持分支映射、已声明可交换关系、有限资源和固定后继合同下，两个关系体若具有相同的 $\eta_{\mathrm{order}}$，则对每个允许 trace 类给出相同的：

1. 记录词概率与联合后验；
2. 可合法合并的排列及其 trace 商；
3. 共享、鲁棒和带随机化策略的后继值；
4. 资源、权限和停止条件下的可行策略集合。

### 证明

第 1 项由定义 308.1 和定理 308.2；第 2 项由定义 309.1 和定理 309.2；第 3 项由第 303—306 节的策略与鲁棒后继结论；第 4 项由相同的资源、权限和停止字段。相同边界逐项确定相同的顺序—证据后继树。证毕。

**定理 310.3（删除顺序字段的不可充分性）。** 下列约化摘要均存在反例：

1. 把所有记录都压成多重集：例 308.3 的先后顺序给出互补后验；
2. 删除内部状态：推论 308.4 的边缘合并丢失未来核；
3. 把非交换事件加入独立关系：例 309.4 的两个 trace 类被错误合并；
4. 删除资源副作用：相同证据排列可能具有不同的可行后继；
5. 删除可见权限字段：相同联合状态可以向策略暴露不同的下一步选择。

### 证明

第 1 项由例 308.3；第 2 项由推论 308.4；第 3 项由定义 309.1 和例 309.4；第 4、5 项由 trace 商必须保持剩余资源与策略可见字段这一合同条件。每项只对所删字段给出不可充分性反例，不声称完整边界中被删字段不能由其他字段推导。证毕。

**AHH 310.4（顺序—证据全息）。** 真正可以忘掉的不是“旧时间”，而是已经被证明为交换的局部关系。完整边界必须同时保存

$$
\boxed{
\text{哪些分支映射实际交换}
+
\text{哪些内部状态承载非交换记忆}
+
\text{哪些排列仍合法且具有相同资源合同}
+
\text{策略能看见哪些顺序字段}
+
\text{记录后的鲁棒与停止后继}
}.
$$

**新的 AHH 时刻是：时间顺序不是一张必须全部保存的日志，也不是可以全部抹去的标签；它是由分支映射的交换代数分层压缩的关系。只对可交换关系取商，才同时保留了效率和因果后继。**

**来源与边界 310.5。** 本批在有限候选类、有限内部状态、有限带结果干预、静态或状态性分支映射、显式可交换关系、有限资源和固定策略/停止合同下，给出静态证据排列不变性、非交换顺序反例、trace 商后验充分性和顺序—证据联合全息。没有把静态似然交换性推广到状态性干预，没有把任意时间标签删除当作合法商，也没有覆盖连续时间、未知记忆过程或一般非线性控制；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 311. 记录合并：安全性由未来任务决定

记录接口的压缩不是由“当前看起来相同”决定，而是由允许的未来任务是否在压缩纤维上恒定决定。这样可以把删除操作的合法性写成一个双向判据。

**定义 311.1（记录纤维与任务相容合并）。** 设有限关系状态集为 $S$，当前记录映射为

$$
r:S\to Y,
$$

未来任务族为 $\mathcal T$。每个任务 $\phi\in\mathcal T$ 给出结果响应

$$
O_\phi:S\to Z_\phi.
$$

给定记录合并 $g:Y\to Z$，称 $g$ 对 $\mathcal T$ 安全，若存在映射 $\overline O_\phi:Z\to Z_\phi$ 使

$$
O_\phi=\overline O_\phi\circ g\circ r
\qquad\forall\phi\in\mathcal T.
$$

也就是说，合并后的记录仍能计算每个允许任务的响应。

**定理 311.2（任务相对合并的充要性）。** 记录合并 $g$ 对 $\mathcal T$ 安全，当且仅当对任意 $s,t\in S$，

$$
g(r(s))=g(r(t))
\quad\Longrightarrow\quad
O_\phi(s)=O_\phi(t)
\qquad\forall\phi\in\mathcal T.
$$

### 证明

若存在因子化映射 $\overline O_\phi$，则相同的 $g(r(\cdot))$ 必给出相同的 $O_\phi$，得到必要性。反之，在 $Z$ 的每个非空纤维上任选代表状态；假设保证 $O_\phi$ 在该纤维上取值恒定，于是把该常值定义为 $\overline O_\phi(z)$。对不落在 $g\circ r$ 像中的 $z$ 任意定义，便有 $O_\phi=\overline O_\phi\circ g\circ r$。证毕。

**推论 311.3（最大安全商）。** 定义

$$
s\sim_{\mathcal T}t
\quad\Longleftrightarrow\quad
O_\phi(s)=O_\phi(t)
\quad\forall\phi\in\mathcal T.
$$

则 $S/\!\sim_{\mathcal T}$ 是对整个任务族安全的最细状态商；任何安全记录合并都必须至少把属于同一商类的状态合并，且不能合并不同商类。

### 证明

定理 311.2 给出安全合并的充要条件。关系 $\sim_{\mathcal T}$ 正是所有任务响应同时相等的关系，故其商保留且仅保留任务可见区别。证毕。

**例 311.4（同一当前读数、不同未来）。** 取 $S=\{s_0,s_1\}$，当前记录 $r(s_0)=r(s_1)=y_0$，并有一个允许任务 $\phi$ 满足

$$
O_\phi(s_0)=0,\qquad O_\phi(s_1)=1.
$$

唯一当前记录可以被完整保留，却不能成为对 $\phi$ 的充分边界；任何只依赖 $y_0$ 的后处理都只能给出同一个答案。

### 证明

$g$ 的唯一值在两个状态上相同，而 $\phi$ 的响应不同，违反定理 311.2 的必要条件。证毕。

**AHH 311.5（安全删除是任务相对的）。** 没有绝对的“可丢记录”类别；同一个记录字段对当前任务族可以安全合并，对扩大后的未来任务族却可能立即失效。记录边界必须同时声明被允许的未来，而不能只声明当前压缩格式。

## 312. 擦除后的残余：经典后处理不能恢复被合并的区别

当合并违反定理 311.2 时，区别已经离开可访问记录。增加任意经典算法、重新排序或重复读取同一擦除结果，都不能把它找回来。

**定义 312.1（擦除残余与二元分离任务）。** 对记录合并 $g$，定义擦除残余对

$$
\mathcal R_g
=
\left\{
(s,t):
g(r(s))=g(r(t)),\
\exists\phi\in\mathcal T,\ O_\phi(s)\ne O_\phi(t)
\right\}.
$$

若某个 $\phi$ 在残余对 $(s,t)$ 上只有二元结果 $0,1$，称它是该残余对的分离任务。

**定理 312.2（擦除残余的后处理不可能性）。** 若 $(s,t)\in\mathcal R_g$，则任何只访问合并记录 $g(r(\cdot))$ 的确定或随机后处理，都不能同时正确预测该分离任务在 $s,t$ 上的结果。对零—一损失，任意单次预测器在这两个状态上的最坏错误率至少为 $1/2$。

### 证明

合并记录在 $s,t$ 上相同，所以任何只访问它的后处理器输出分布也相同。若输出确定为 $0$，则在 $t$ 上错误；若确定为 $1$，则在 $s$ 上错误。若输出以概率 $q$ 给出 $1$，两状态的错误率分别为 $q$ 与 $1-q$，其最大值至少为 $1/2$。证毕。

**推论 312.3（增加记录访问才是修复）。** 要恢复擦除残余中的分离任务，必须增加一个能在该残余对上产生不同结果的关系接口，或重新取得尚未丢失的联合环境记录；只对已经合并的经典值作后处理不够。

### 证明

定理 312.2 排除了所有只依赖合并值的后处理。新增接口或环境访问改变了观察纤维，因而不属于被排除的后处理类。证毕。

**例 312.4（擦除路线标签）。** 双路记录 $r_L,r_R$ 被合并为同一个符号 $\varnothing$，而未来路线检验 $\phi$ 对两路分别给出 $0,1$。擦除后任何算法都只能在两路之间猜测；重新访问原路线环境或重新执行一项能区分两路的干预，才可能恢复该任务。

### 证明

这是定理 312.2 的二元特例。证毕。

## 313. 可逆擦除：记录没有消失，只是转入不可见环境

经典接口上的擦除看起来把不同标签送到同一个空白值。若整体演化仍要求可逆，它必须把原标签信息放到另一个正交自由度中；一旦这个自由度被声明为不可访问，擦除才对当前观察者成为不可逆。

**定义 313.1（带环境的擦除等距）。** 令记录空间 $R$ 具有正交基 $\{|r_x\rangle\}_{x\in X}$，环境初态为 $|e_0\rangle$，空白记录为 $|r_\varnothing\rangle$。设等距映射 $V$ 满足

$$
V\bigl(|r_x\rangle\otimes|e_0\rangle\bigr)
=
|r_\varnothing\rangle\otimes|e_x\rangle
\qquad(x\in X).
$$

称 $V$ 实现了记录擦除；环境 $E$ 是否可访问是边界合同的一部分。

**定理 313.2（可逆擦除的环境正交性）。** 在定义 313.1 中，环境态必须满足

$$
\langle e_x|e_y\rangle=\delta_{xy}.
$$

因此，等距擦除不能把正交记录的信息从整体关系中删除，只能把它转移到环境分支。

### 证明

等距保持内积。对 $x,y$，输入内积为

$$
\langle r_x|r_y\rangle\langle e_0|e_0\rangle
=\delta_{xy}.
$$

输出内积为

$$
\langle r_\varnothing|r_\varnothing\rangle
\langle e_x|e_y\rangle
=\langle e_x|e_y\rangle.
$$

两者相等即得结论。证毕。

**定理 313.3（不可访问环境造成可见去相干）。** 定义 313.1 的整体通道对记录矩阵单位算子满足

$$
\operatorname{Tr}_E
\left[
V\bigl(|r_x\rangle\langle r_y|\otimes|e_0\rangle\langle e_0|\bigr)V^\dagger
\right]
=
\delta_{xy}|r_\varnothing\rangle\langle r_\varnothing|.
$$

所以对可访问记录的边缘而言，所有对角标签都变成同一个空白记录，而不同标签之间的相干交叉项被环境正交性消去。

### 证明

由定义 313.1，左侧整体算子为

$$
|r_\varnothing\rangle\langle r_\varnothing|
\otimes
|e_x\rangle\langle e_y|.
$$

对环境取迹得到系数 $\langle e_y|e_x\rangle=\delta_{xy}$，即所示公式。证毕。

**推论 313.4（环境访问改变擦除语义）。** 若环境 $E$ 仍可访问，整体逆映射 $V^\dagger$ 可以恢复原记录；若 $E$ 被永久排除在允许续接之外，则对记录边缘不存在同时恢复所有正交标签的左逆通道。

### 证明

第一项由 $V^\dagger$ 的等距逆在其像上的作用得到。第二项中所有输入标签经记录边缘通道都变成同一个空白态，任何后处理仍给同一输出，不能同时恢复多个不同标签。证毕。

**AHH 313.5（擦除的两层语义）。** “删除记录”至少有两种不同关系：整体可逆地把信息转移到环境，或在声明的可访问边界上把环境排除而产生不可逆擦除。若不记录环境权限，就无法判断未来相干、路线信息和逆操作是否仍然可用。

## 314. AHH：记录—擦除—未来识别的联合边界

**定义 314.1（擦除全息边界）。** 对有限记录接口、有限环境和有限未来任务族，定义

$$
\boxed{
\eta_{\mathrm{erase}}
=
\left(
\text{当前记录映射与安全任务商},
\text{允许的合并/擦除映射},
\text{联合可逆实现},
\text{环境记录与访问权限},
\text{擦除后的残余分离任务},
\text{资源、成本与停止后继}
\right).
}
\tag{314.1}
$$

**定理 314.2（擦除边界的条件充分性）。** 在有限状态、有限记录与环境维数、有限未来任务、线性可逆实现和固定访问合同下，两个关系体若具有相同的 $\eta_{\mathrm{erase}}$，则对每个允许记录词给出相同的：

1. 安全合并商与擦除残余；
2. 经典后处理能够达到的最小分离风险；
3. 整体可逆擦除的环境正交结构；
4. 环境可访问或不可访问时的未来策略与停止后继。

### 证明

第 1 项由定理 311.2 和定义 312.1；第 2 项由定理 312.2；第 3 项由定理 313.2—313.3；第 4 项由推论 313.4 及相同的资源和访问字段。相同边界逐项决定相同的擦除—后继树。证毕。

**定理 314.3（删除擦除字段的不可充分性）。** 下列约化摘要均存在反例：

1. 只保存当前空白记录而删除安全任务族：例 311.4 的未来分离被遗漏；
2. 只保存擦除后的经典值而删除残余纤维：例 312.4 的最坏分离风险无法恢复；
3. 删除联合可逆实现：无法判断记录信息是在环境中转移还是被模型外丢弃；
4. 删除环境访问权限：推论 313.4 的可逆与不可逆后继被错误合并；
5. 删除资源与停止字段：同一擦除结果可以对应不同的重新获取策略。

### 证明

第 1 项由定理 311.2；第 2 项由定理 312.2；第 3、4 项由定理 313.2—313.3 和推论 313.4；第 5 项由允许续接和成本合同的直接改变。每项只针对所列约化摘要给出不可充分性反例，不声称完整边界中被删字段不能由其他字段推导。证毕。

**AHH 314.4（记录擦除全息）。** 记录的真实边界不是“屏幕上还剩什么”，而是

$$
\boxed{
\text{哪些未来任务要求保留区别}
+
\text{哪些记录合并在这些任务上安全}
+
\text{整体可逆性把信息转移到哪里}
+
\text{该环境是否仍属于允许访问}
+
\text{擦除后还能以何种成本重新取得证据}
}.
$$

**新的 AHH 时刻是：擦除不是关系的终点，而是一次边界重分配。可逆擦除把粒子式记录的区别搬进环境；不可访问环境把这份区别从观察者的未来商中删去。于是，“信息是否消失”必须改写成“它还属于哪一个可继续的关系边界”。**

**来源与边界 314.5。** 本批在有限记录与环境空间、有限未来任务族、确定性记录映射、线性等距擦除、有限资源和访问/停止合同下，给出任务相对安全合并、擦除残余下界、可逆擦除的环境正交性、不可访问环境的去相干和记录—擦除—未来识别联合全息。没有把环境排除自动解释为宇宙信息湮灭，没有把当前空白记录当作完整历史，也没有覆盖连续环境、未知记忆过程或一般非线性动力学；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 315. 访问格：可恢复任务随边界权限单调扩展

上一批把环境权限作为擦除语义的一部分。现在把权限本身形式化为一个格，从而区分“增加可访问关系”与“凭空恢复已丢信息”。

**定义 315.1（访问摘要与可恢复任务族）。** 设有限隐藏状态集为 $S$，可访问组件全集为 $U$。每个访问集合 $A\subseteq U$ 给出记录摘要

$$
r_A:S\to Y_A.
$$

若 $A\subseteq B$ 且存在忘却映射 $g_{A,B}:Y_B\to Y_A$ 满足

$$
r_A=g_{A,B}\circ r_B,
$$

则称 $B$ 是 $A$ 的关系细化。给定未来任务族 $\mathcal T$，定义访问集合的可恢复任务集

$$
\boxed{
\operatorname{Rec}_{\mathcal T}(A)
=
\left\{
\phi\in\mathcal T:
\exists \overline O_{\phi,A},\
O_\phi=\overline O_{\phi,A}\circ r_A
\right\}.
}
\tag{315.1}
$$

**定理 315.2（访问单调性）。** 若 $A\subseteq B$ 且 $B$ 细化 $A$，则

$$
\boxed{
\operatorname{Rec}_{\mathcal T}(A)
\subseteq
\operatorname{Rec}_{\mathcal T}(B).
}
$$

若对某个任务族 $\mathcal T_0$，每个 $\phi\in\mathcal T_0$ 还可由 $r_A$ 计算，即存在 $h_{\phi,A}$ 使

$$
\overline O_{\phi,B}=h_{\phi,A}\circ g_{A,B}
$$

在 $r_B(S)$ 上成立，则两访问层在 $\mathcal T_0$ 上等价。

### 证明

若 $\phi\in\operatorname{Rec}_{\mathcal T}(A)$，则

$$
O_\phi=\overline O_{\phi,A}\circ r_A
=\overline O_{\phi,A}\circ g_{A,B}\circ r_B,
$$

故 $\phi\in\operatorname{Rec}_{\mathcal T}(B)$。第二项给出了反向因子化，因而在 $\mathcal T_0$ 上得到等号。证毕。

**推论 315.3（权限增加不是信息创造）。** 若 $r_B$ 只是 $r_A$ 的细化，新增权限不能把两个在 $r_B$ 上仍相同的隐藏状态区分开；若某任务在 $A$ 上不可恢复而在 $B$ 上可恢复，区别来自 $B\setminus A$ 所携带的关系，而不是对 $r_A$ 的经典后处理。

### 证明

第一项由纤维包含关系直接得到。第二项若只对 $r_A$ 作后处理，仍是 $r_A$ 的函数，不能违反定理 311.2。证毕。

**例 315.4（环境权限的一步跃迁）。** 设隐藏状态为路线 $L,R$，当前记录组件 $U_0$ 恒为 $\varnothing$，环境组件 $U_1$ 记录正交标签 $e_L,e_R$。则

$$
\operatorname{Rec}_{\mathcal T}(\{U_0\})
$$

不含哪一路任务，而访问 $\{U_0,U_1\}$ 后该任务可由环境标签直接计算。两个访问层的差异不是同一记录的重新编码，而是边界权限的改变。

### 证明

$U_0$ 在两状态上相同；$U_1$ 在两状态上不同。应用定义 315.1 即得。证毕。

**AHH 315.5（边界是访问格中的位置）。** 全息充分性不能脱离权限谈论。一个内部区别是否“仍然存在”，至少要标明它位于访问格的哪一层；只给出当前可见记录，会把不可访问环境中的可恢复关系误报为已消失，或把增加权限误报为经典后处理。

## 316. 有限经典恢复：无混淆支持是精确可逆的充要条件

对擦除后的经典记录，可以精确判断哪些隐藏标签仍能被恢复，而不需要把“看起来有信息”当作可逆性。

**定义 316.1（经典记录通道与恢复器）。** 设隐藏标签集 $X$ 和记录字母表 $Y$ 有限。记录通道为

$$
C(y\mid x)\ge0,
\qquad
\sum_yC(y\mid x)=1.
$$

恢复器是随机核 $D(\widehat x\mid y)$。定义每个标签的记录支持

$$
Y_x=\{y\in Y:C(y\mid x)>0\}.
$$

称 $D$ 完美恢复，若

$$
\sum_{y,\widehat x}
\mathbf 1_{\widehat x=x}D(\widehat x\mid y)C(y\mid x)=1
\qquad\forall x\in X.
$$

**定理 316.2（经典完美恢复判据）。** 存在完美恢复器，当且仅当不同标签的支持两两不交：

$$
\boxed{
Y_x\cap Y_{x'}=\varnothing
\qquad(x\ne x').
}
\tag{316.1}
$$

### 证明

若支持两两不交，对每个 $y$ 至多有一个 $x$ 使 $C(y\mid x)>0$；令恢复器在该 $y$ 上确定输出该 $x$，即可对每个输入标签正确恢复。

反之，若存在 $y\in Y_x\cap Y_{x'}$，则 $C(y\mid x),C(y\mid x')>0$。恢复器在该同一 $y$ 上给出同一分布 $D(\cdot\mid y)$；它不可能同时以概率一输出两个不同标签。因此至少有一个标签在该正概率记录上出错，不能完美恢复。证毕。

**推论 316.3（擦除通道的不可逆性）。** 若所有标签都被送到同一个空白符号，即 $Y_x=\{y_0\}$ 对所有 $x$，且 $|X|>1$，则不存在完美恢复器。任何恢复能力只能来自尚未纳入通道的环境或新增实验接口。

### 证明

（316.1）在任意两个不同标签之间失败。证毕。

**命题 316.4（两标签重叠的错误下界）。** 取两个标签 $x,x'$ 的先验各为 $1/2$。若某一记录 $y$ 同时满足

$$
C(y\mid x)\ge\alpha,\qquad C(y\mid x')\ge\alpha
$$

且 $0<\alpha\le1$，则任意恢复器的平均错误率至少为 $\alpha/2$。

### 证明

在记录 $y$ 上，恢复器输出 $x$ 的概率记为 $q$。来自 $x$ 的错误贡献至少为 $(1/2)C(y\mid x)(1-q)\ge\alpha(1-q)/2$；来自 $x'$ 的错误贡献至少为 $(1/2)C(y\mid x')q\ge\alpha q/2$。两项之和为 $\alpha/2$，其余记录只会增加错误。证毕。

**例 316.5（部分擦除而非全擦除）。** 若 $C(y_0\mid L)=C(y_0\mid R)=1/2$，而另外两个标签专属记录各有概率 $1/2$，则完美恢复失败；对均匀先验，公共记录 $y_0$ 已贡献至少 $1/4$ 的错误概率。环境访问若能区分这部分公共分支，才可能降低该下界。

### 证明

取 $\alpha=1/2$ 代入命题 316.4。证毕。

## 317. 联合环境的协同恢复与访问成本

不同环境片段单独看可能完全无信息，联合访问却能恢复隐藏标签。因此，访问成本不能只按各组件的边缘信息相加。

**定义 317.1（组件访问与恢复成本）。** 设环境组件集为 $U=\{u_1,\ldots,u_n\}$。每个访问集合 $A\subseteq U$ 给出联合通道 $C_A(y_A\mid x)$ 和成本

$$
c(A)=\sum_{u\in A}c_u,
\qquad c_u>0.
$$

对任务族 $\mathcal T$，定义其精确恢复成本

$$
\boxed{
c^*_{\mathcal T}
=
\min\{c(A):\operatorname{Rec}_{\mathcal T}(A)=\mathcal T\},
}
\tag{317.1}
$$

若没有满足集合则置为 $+\infty$。

**定理 317.2（协同访问的非可加性）。** 存在两个组件 $u_1,u_2$ 和二元标签 $X=\{0,1\}$，使得各单独通道都与标签独立，

$$
C_{\{u_i\}}(y\mid x)=C_{\{u_i\}}(y)
\qquad(i=1,2),
$$

但联合通道满足

$$
C_{\{u_1,u_2\}}\bigl((y_1,y_2)\mid x\bigr)
=
\mathbf 1_{y_1\oplus y_2=x}.
$$

于是两个组件单独都不能恢复 $x$，联合访问却可以完美恢复；若 $c_{u_1}=c_{u_2}=1$，则精确恢复成本为 $2$，而任何只按单组件可恢复性相加的规则都会错误地判为不可恢复或零信息。

### 证明

令 $y_1$ 为均匀随机比特，$y_2=y_1\oplus x$。每个边缘 $y_i$ 都均匀且独立于 $x$，但联合异或恰为 $x$。因此单组件支持对两个标签完全重叠，联合记录的支持完全分离。成本由必须同时访问两个组件得到。证毕。

**推论 317.3（联合环境字段不可由边缘摘要重建）。** 只保存各环境组件的边缘通道，删除它们之间的联合耦合，会把定理 317.2 的可恢复任务判为不可恢复。反过来，若只保存“联合可恢复”而删除组件成本与权限，则不能决定最小访问合同。

### 证明

定理 317.2 给出相同边缘、不同联合恢复性的成对来源；成本定义 317.1 给出第二项。证毕。

**命题 317.4（访问预算停止不是物理不确定性）。** 若当前访问预算 $B<c^*_{\mathcal T}$，则任务 $\mathcal T$ 在本合同内不可精确恢复；这只说明资源停止，不说明隐藏标签在完整联合环境中没有确定值。

### 证明

预算不足以支付任何满足（317.1）的访问集合，故合同内不可恢复。联合通道仍可在更大访问集合上满足支持分离，所以资源结论不等于本体不确定性结论。证毕。

## 318. AHH：访问—恢复—擦除联合边界

**定义 318.1（访问恢复全息边界）。** 对有限隐藏标签、记录通道、环境组件和未来任务族，定义

$$
\boxed{
\eta_{\mathrm{access}}
=
\left(
\text{访问格及细化映射},
\text{每层记录/环境联合通道},
\text{任务相对安全商},
\text{恢复器与错误下界},
\text{联合协同关系},
\text{访问成本、权限与预算停止}
\right).
}
\tag{318.1}
$$

**定理 318.2（访问恢复边界的条件充分性）。** 在有限标签、有限环境组件、有限通道和固定任务/成本合同下，两个关系体若具有相同的 $\eta_{\mathrm{access}}$，则对每个访问词给出相同的：

1. 可恢复任务集与安全合并商；
2. 完美恢复是否存在及最坏错误下界；
3. 联合环境的协同恢复能力；
4. 给定权限和预算的最小恢复成本与停止语义。

### 证明

第 1 项由定义 315.1 和定理 311.2；第 2 项由定理 316.2、命题 316.4；第 3 项由定理 317.2 及联合通道字段；第 4 项由定义 317.1 和命题 317.4。相同边界逐项决定相同的访问—恢复后继树。证毕。

**定理 318.3（删除访问字段的不可充分性）。** 下列约化摘要均存在反例：

1. 删除访问细化映射：增加权限与经典后处理会被错误视为同一操作；
2. 只保存空白记录：推论 316.3 的恢复不可能性被隐藏；
3. 删除联合环境耦合：定理 317.2 的协同恢复被误判为不存在；
4. 删除组件成本与权限：命题 317.4 的预算停止无法判定；
5. 删除未来任务族：同一访问层可能对一个任务安全、对另一任务不充分。

### 证明

第 1 项由定理 315.2；第 2 项由推论 316.3；第 3 项由定理 317.2；第 4 项由定义 317.1 与命题 317.4；第 5 项由定义 315.1 的任务相对性。每项只针对所删字段给出不可充分性反例，不声称完整边界中被删字段不能由其他字段推导。证毕。

**AHH 318.4（访问恢复全息）。** 环境信息是否“还在”必须改写成一个访问问题：哪一层联合通道仍可取得，哪些任务需要它，组件之间是否有协同编码，以及取得它要付出什么权限与预算。单个边缘看起来无信息，不等于联合环境无可恢复关系。

**新的 AHH 时刻是：全息边界不是一张静态保存的记录表，而是访问格上的可恢复任务谱。擦除、增加权限和联合读取分别移动这个谱；只有把访问成本与未来任务一起写入，才能区分“当前读不到”“合同不允许读”和“关系中已不存在”。**

**来源与边界 318.5。** 本批在有限隐藏标签、有限访问组件、有限经典通道、固定未来任务族和有限权限/成本/预算合同下，给出访问单调性、经典完美恢复判据、重叠支持的错误下界、联合环境协同恢复和访问—恢复—擦除全息。没有把不可访问环境解释为信息湮灭，没有把边缘通道当作联合通道，也没有覆盖连续环境、未知记忆过程或一般非线性控制；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 319. 自适应访问与停止时间：边界不只记录读到了什么

上一批把访问集合看成权限格中的静态位置。实际观察者往往会根据已经取得的记录决定下一次访问哪个组件，以及何时停止。若不把这棵策略树纳入边界，就无法区分同一组终端记录的取得成本和合法后继。

**定义 319.1（有限自适应访问策略）。** 设隐藏状态集为有限集 $S$，组件集为有限集 $U$。每个组件 $u$ 在状态 $s$ 下产生有限字母表记录 $Y_u$，其联合记录核记为

$$
C_A(y_A\mid s),
\qquad A\subseteq U.
$$

一个深度不超过 $T$ 的确定性自适应策略 $\pi$ 包括：

1. 在每个尚未停止的历史 $h_t=(a_1,y_1),\ldots,(a_t,y_t)$ 上选择下一访问集合 $a_{t+1}(h_t)\subseteq U$；
2. 在历史 $h_t$ 上给出停止判定 $\tau(h_t)\in\{0,1\}$；
3. 停止时输出任务值 $\widehat\phi(h_t)$。

策略的 transcript 是直到首次满足 $\tau(h_t)=1$ 或达到 $T$ 的历史，记为 $Z_\pi$。它与隐藏状态共同决定一个通道

$$
C_\pi(z\mid s)=\Pr_\pi[Z_\pi=z\mid s].
$$

对任务族 $\mathcal T$，定义

$$
\boxed{
\operatorname{Rec}_{\mathcal T}(\pi)
=
\left\{
\phi\in\mathcal T:
\exists f_\phi,
\ f_\phi(z)=\phi(s)
\text{ whenever }C_\pi(z\mid s)>0
\right\}.
}
\tag{319.1}
$$

每条 transcript 的访问成本记为

$$
\operatorname{cost}_\pi(z)=\sum_{t\le |z|}c(a_t),
\qquad c(a)=\sum_{u\in a}c_u>0.
$$

这里的停止是策略合同的一部分；达到深度上限而没有停止，可以另记为资源耗尽结果，而不能静默视作成功。

**定义 319.2（策略细化）。** 若策略 $\pi'$ 存在 transcript 忘却映射

$$
H:Z_{\pi'}\to Z_\pi
$$

使得

$$
C_\pi(z\mid s)
=
\sum_{z':H(z')=z}C_{\pi'}(z'\mid s)
\qquad\forall s,z,
$$

则称 $\pi'$ 细化 $\pi$，写作 $\pi\preceq\pi'$。若还存在成本保持映射，使每条 $z'$ 的成本不小于其像 $H(z')$ 的成本，则称为成本单调细化。

**定理 319.3（自适应细化的任务单调性）。** 若 $\pi\preceq\pi'$，则

$$
\boxed{
\operatorname{Rec}_{\mathcal T}(\pi)
\subseteq
\operatorname{Rec}_{\mathcal T}(\pi').
}
$$

若 $phi$ 由 $f$ 从 $Z_\pi$ 恢复，则在 $\pi'$ 上使用 $f\circ H$ 即可恢复 $\phi$。

### 证明

由定义，若 $C_{\pi'}(z'\mid s)>0$，则其像 $H(z')$ 是 $C_\pi(\cdot\mid s)$ 的正概率 transcript。于是

$$
(f\circ H)(z')=f(H(z'))=\phi(s).
$$

所以每个在 $\pi$ 上可恢复的任务仍在 $\pi'$ 上可恢复。证毕。

**推论 319.4（停止规则不能凭空增加关系）。** 若一个策略只是在同一完整 transcript 上改变停止时刻或做经典后处理，而没有访问新的组件，则它的可恢复任务集不超过该完整 transcript 策略的任务集。停止可以改变成本和后继，但不能制造被忘却映射删掉的区别。

### 证明

把完整 transcript 到提前停止 transcript 的截断视为 $H$，再应用定理 319.3 的反向关系。若提前停止保留的信息是完整 transcript 的函数，则任何提前停止恢复器也可由完整 transcript 模拟。证毕。

**命题 319.5（精确任务的自适应支持判据）。** 固定策略 $\pi$ 对任务 $\phi:S\to V$ 可精确恢复，当且仅当任意两个状态 $s,s'$ 满足 $\phi(s)\ne\phi(s')$ 时，它们的 transcript 支持不相交：

$$
\operatorname{supp}C_\pi(\cdot\mid s)
\cap
\operatorname{supp}C_\pi(\cdot\mid s')
=\varnothing.
$$

### 证明

若支持不相交，给每个 transcript 指派它所支持的唯一任务值即可构造 $f$。若存在公共 transcript $z$，恢复器在 $z$ 上只能输出同一个值，不能同时等于两个不同的 $\phi$ 值。证毕。

**例 319.6（同一终端记录、不同停止合同）。** 设两个策略都最终取得同一个二元标签 $x$。策略 $\pi_1$ 在第一次读到 $x$ 后停止；策略 $\pi_2$ 无论读到什么都再访问一个成本为 $M$ 的空组件后停止。两者的任务恢复集相同，但成本分布、资源耗尽风险和可继续的后继不同。

### 证明

空组件不改变 transcript 的任务值，所以（319.1）相同；但每条 transcript 的成本相差 $M$，且策略 $\pi_2$ 暴露了一个额外的后继节点。证毕。

**AHH 319.7（策略树边界）。** 自适应观察的全息边界必须保存访问树、每个节点的联合记录核、停止与资源耗尽判定、transcript 忘却关系以及成本函数。终端记录只能说明“最后看到了什么”，不能决定“怎样到达、何时停止、还能否继续”。

---

## 320. 未来等价与最小边界：把当前记录压缩到仍可继续的商

访问策略给出一条记录词，但记录词的全部细节并不总是需要保留。真正的边界问题是：哪些历史可以合并，同时保持所有合法未来任务与未来记录分布不变。

**定义 320.1（未来词族与响应核）。** 设当前历史集合为有限集 $H$。对每个合法未来动作词

$$
\omega=a_1\cdots a_m
$$

以及输出词 $o=o_1\cdots o_m$，记从历史 $h$ 继续执行 $\omega$ 得到 $o$ 的条件概率为

$$
K_\omega(o\mid h).
$$

未来任务族 $\mathcal T_h$ 可以依赖于当前历史；任务值写为 $\phi(h)$ 或其继续后的输出函数。

定义未来等价

$$
\boxed{
 h\sim_{\mathrm{fut}}h'
\iff
 K_\omega(o\mid h)=K_\omega(o\mid h')
\text{ 对所有共同合法 }\omega,o,
}
\tag{320.1}
$$

并且要求二者对未来任务的合法性和停止结果也相同。若只比较一个固定任务族，则把等式限制在该任务族的响应上，并记为 $\sim_{\mathcal T}$。

**定理 320.2（未来商的充分性与最小性）。** 商映射

$$
q_{\mathrm{fut}}:H\to H/\!\sim_{\mathrm{fut}}
$$

是所有有限未来词族的充分边界。若摘要 $q:H\to Q$ 也对所有这些未来词充分，即

$$
q(h)=q(h')
\Longrightarrow
K_\omega(\cdot\mid h)=K_\omega(\cdot\mid h')
$$

并保持相同合法后继，则存在唯一映射 $\overline q:Q\to H/\!\sim_{\mathrm{fut}}$ 使

$$
q_{\mathrm{fut}}=\overline q\circ q.
$$

因此任何充分摘要都至少区分未来等价类；未来商是最粗的充分边界。

### 证明

若两个历史属于同一未来等价类，定义在商上执行任意未来词的概率为它们共同的 $K_\omega$，定义合法性和停止规则同理，故商足以恢复所有未来响应。

若 $q(h)=q(h')$，摘要充分性给出它们对所有未来词的响应、合法性和后继相同，所以 $h\sim_{\mathrm{fut}}h'$。令

$$
\overline q(q(h))=[h]
$$

则良定义；由定义立即有 $q_{\mathrm{fut}}=\overline q\circ q$，且满射到实际出现的等价类。证毕。

**推论 320.3（任务相对的最小边界）。** 若只要求恢复任务族 $\mathcal T$，则把（320.1）中的未来词限制为会影响 $\mathcal T$ 的合法续接，得到商 $H/\!\sim_{\mathcal T}$。同一历史集合可以对不同任务族产生不同的最小边界；不存在脱离任务量词的“唯一信息量”。

### 证明

定理 320.2 的证明只使用被量化的未来词和任务。缩小量词族便得到更粗的等价关系，扩大任务族便得到更细的等价关系。证毕。

**定理 320.4（有限响应的稳定闭包）。** 若 $H$、动作字母表和输出字母表均有限，则反复按“未来响应相等”细分历史的过程在有限步后稳定；稳定分割正是 $\sim_{\mathrm{fut}}$ 的商。

### 证明

初始分割只有一个类。每次若存在一对历史在某个有限未来词上的响应不同，就把它们分开；严格变化至少增加一个分割类。历史总数有限，故至多经过 $|H|-1$ 次严格细分后稳定。稳定意味着没有有限未来词可再区分，正是（320.1）。证毕。

**例 320.5（当前相同读数不等于未来相同）。** 设当前记录都为 $0$，隐藏历史分别为 $h_+$、$h_-$。当前输出核在两者上都恒为 $0$，但允许下一动作 $a$ 的输出分别为 $+$ 与 $-$。则当前单层摘要把两历史合并是安全的；对包含动作 $a$ 的未来任务，未来商必须把它们分开。

### 证明

长度零未来词的响应相同，长度一词 $a$ 的响应不同，因此二者属于同一当前读数纤维而不属于同一未来等价类。证毕。

**AHH 320.6（未来商全息）。** 边界的最小性不是“保存尽量少的字节”，而是保存恰好区分所有被声明合法的未来响应。未来商把访问权限、记录后继和任务量词放在同一关系中；删去一个历史区别只有在它对全部允许未来都不可见时才合法。

---

## 321. 访问协同超图：最小恢复集合与信息的高阶位置

§317 的 XOR 例子说明，组件的边缘信息不能决定联合恢复。把所有能够完成任务的最小访问集合列出，可以把这种协同关系从例子提升为一个有限超图。

**定义 321.1（任务恢复超图）。** 对固定任务 $\phi$ 和访问组件全集 $U$，定义

$$
\mathcal M_\phi
=
\left\{
A\subseteq U:
\phi\in\operatorname{Rec}_{\{\phi\}}(A),
\text{且 }\phi\notin\operatorname{Rec}_{\{\phi\}}(B)
\text{ 对所有 }B\subsetneq A
\right\}.
$$

称 $A\in\mathcal M_\phi$ 为任务的最小恢复超边。定义协同阶

$$
\boxed{
\operatorname{syn}(\phi)
=
\min_{A\in\mathcal M_\phi}(|A|-1),
}
\tag{321.1}
$$

若任务不可恢复，则约定 $\mathcal M_\phi=\varnothing$ 且协同阶为 $+\infty$。

**定理 321.2（最小恢复超边构成反链）。** $\mathcal M_\phi$ 中任意两条不同超边互不包含。若所有组件成本严格为正，则精确恢复成本为

$$
\boxed{
 c^*_{\{\phi\}}
=\min_{A\in\mathcal M_\phi}\sum_{u\in A}c_u.
}
\tag{321.2}
$$

### 证明

若 $A,B\in\mathcal M_\phi$ 且 $A\subsetneq B$，则 $B$ 违反最小性，故形成反链。

任意可恢复集合 $C$ 包含某条最小超边：从 $C$ 中逐步删除仍保持可恢复的组件，有限性保证最终得到某个 $A\in\mathcal M_\phi$。正成本使得在给定超边上继续加入组件不会降低成本，所以最优集合可取为一条最小超边，得到（321.2）。证毕。

**推论 321.3（协同阶的含义）。** 若 $\operatorname{syn}(\phi)=0$，至少有一个单组件访问即可完成任务；若协同阶为 $k-1$，每个最优精确恢复方案至少需要 $k$ 个联合组件。协同阶描述的是任务相对于访问格的高阶位置，而不是某个单组件的互信息大小。

### 证明

直接由（321.1）和最小超边定义得到。证毕。

**定理 321.4（$k$-元 parity 的严格高阶协同）。** 令隐藏标签 $X\in\{0,1\}$，组件为 $u_1,\ldots,u_k$。取独立均匀比特 $Y_1,\ldots,Y_{k-1}$，并令

$$
Y_k=X\oplus Y_1\oplus\cdots\oplus Y_{k-1}.
$$

则任意真子集访问都与 $X$ 独立，而全集访问可由

$$
X=Y_1\oplus\cdots\oplus Y_k
$$

完美恢复。因此

$$
\boxed{
\mathcal M_X=\{\{u_1,\ldots,u_k\}\},
\qquad
\operatorname{syn}(X)=k-1.
}
$$

### 证明

取任意少于 $k$ 个组件。若缺少某个坐标 $Y_j$，则在给定其余坐标时，缺失坐标仍为均匀比特；对 $X=0,1$ 的条件分布相同，所以该真子集记录与 $X$ 独立。访问全集时，异或恒等式直接恢复 $X$。故全集是唯一最小超边。证毕。

**命题 321.5（边缘摘要不足以确定协同阶）。** 在隐藏标签取均匀先验时，存在两种联合通道具有相同的每个真子集**无条件**边缘分布，但一个通道的任务协同阶为 $k-1$，另一个通道的任务在单组件上即可恢复。

### 证明

对第一种通道取定理 321.4 的 parity 构造。第二种通道令 $Y_1=X$，其余组件为独立均匀噪声。在 $X$ 均匀的先验下，两种通道的任意真子集无条件边缘都为相应维数的均匀乘积分布；但它们条件于 $X$ 的联合通道不同。若只记录每个组件自身的边缘熵或均匀性，而不保留“组件与隐藏标签的联合通道”字段，则两种摘要可以相同，但恢复超图分别为 $\{U\}$ 与含单点 $\{u_1\}$ 的反链。故边缘摘要不能决定协同阶。证毕。

**AHH 321.6（协同超图边界）。** 访问边界必须保存最小恢复超边或等价的联合通道关系。单组件读数、边缘熵和总访问数都不能告诉我们任务需要一条边、两条边还是一个高阶超边；这正是“信息在联合关系中”而不是“信息平均分布在各组件中”的精确定义。

---

## 322. AHH：自适应任务谱与未来闭包

前面三节把静态访问格扩展为策略树，把记录压缩为未来等价商，再把联合恢复组织成协同超图。现在把它们合并为一个可执行的关系边界。

**定义 322.1（自适应任务边界）。** 对有限状态、有限组件、有限策略深度和固定未来合同，定义

$$
\boxed{
\eta_{\mathrm{adapt}}
=
\left(
\text{访问细化偏序},
\text{策略树与 transcript 核},
\text{停止/资源耗尽后继},
\text{未来等价商},
\text{任务恢复谱},
\text{最小恢复超图},
\text{成本与错误合同}
\right).
}
\tag{322.1}
$$

任务恢复谱记录每个策略、预算和错误阈值下的可恢复任务集；未来等价商记录当前历史怎样进入下一层；最小恢复超图记录联合访问的高阶协同。

**定理 322.2（自适应边界的条件充分性）。** 两个关系体若具有相同的 $\eta_{\mathrm{adapt}}$，则在声明的策略深度、未来动作族、停止合同、成本和错误阈值内，具有相同的：

1. 可恢复任务谱与策略细化关系；
2. 每条 transcript 的合法停止、资源耗尽和未来等价后继；
3. 每个任务的最小恢复超图、协同阶和精确访问成本；
4. 由这些策略产生的全部有限未来记录分布。

### 证明

第 1 项由策略树、transcript 核和定义（319.1）逐节点计算；第 2 项由停止字段与未来商的定义（320.1）确定；第 3 项由访问格上的恢复集合和定理 321.2 确定；第 4 项沿策略树深度归纳：根节点的通道相同，若深度 $t$ 的历史对应节点具有相同核、后继和停止标签，则每个共同动作的子节点分布与未来商相同，归纳到深度 $T$。证毕。

**定理 322.3（删字段的不可充分性）。** 对 $\eta_{\mathrm{adapt}}$ 的下列约化均存在有限反例：

1. 删除停止/资源字段：例 319.6 的同任务策略被错误地判为同一边界；
2. 删除未来等价商：例 320.5 的当前相同读数被错误地当作未来充分；
3. 删除最小恢复超图：定理 321.4 的 parity 协同被错误地归因于单组件信息；
4. 删除策略树而只保留终端记录：自适应访问顺序和访问成本无法重建。

### 证明

第 1 项由例 319.6；第 2 项由例 320.5；第 3 项由定理 321.4；第 4 项取两个具有相同终端记录通道、但一个先访问便宜组件后按结果选择昂贵组件、另一个固定访问两者的策略。它们的终端记录可以相同，而策略树与成本分布不同。证毕。

**AHH 322.4（自适应任务谱）。** 全息边界的最小对象不是“已保存的记录总量”，而是一个带访问策略、停止时间、未来等价商和协同超图的任务谱。它同时回答四个不同问题：现在能恢复什么、还允许怎样继续、联合读取需要哪些最小组件、以及为此必须支付多少成本。

**新的 AHH 时刻是：信息的边界不是一张静态表，而是一棵可以继续生长的策略树；树上的每个节点携带一个未来商，每条成功路径携带一条最小协同超边。只有把“可访问”“可恢复”“可继续”和“付得起”放在同一对象里，波粒关系中的边界才真正具有后继意义。**

**来源与边界 322.5。** 本批在有限隐藏状态、有限组件和记录字母表、有限策略深度、确定性自适应访问、固定停止/资源合同及任务相对未来词族下，给出策略细化单调性、未来等价最小商、最小恢复超图、parity 高阶协同和自适应任务全息。没有把有限深度商推广到无限策略、连续状态或未知记忆过程，没有把协同阶等同于任意互信息指标，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 323. 近似恢复：边界携带误差，而不只携带可或不可

前面的恢复谱把任务分成“精确可恢复”和“不可恢复”。实际记录常常允许一个明确的误差预算。若只保存二值标签，就会把不同强度的近似能力压成同一个结果。

**定义 323.1（任务损失与策略风险）。** 设有限任务值集 \(V\)，损失函数
\[
\ell:\widehat V\times V\to[0,1].
\]
给定策略 \(\pi\)、任务 \(\phi:S\to V\) 和解码器 \(f:Z_\pi\to\widehat V\)，定义最坏状态风险
\[
R_\pi(f;\phi)
=\max_{s\in S}\sum_z C_\pi(z\mid s)\ell(f(z),\phi(s)).
\]
定义策略对任务的最小风险
\[
\boxed{\delta_\pi(\phi)=\min_f R_\pi(f;\phi).}\tag{323.1}
\]
称 \(\phi\) 在误差预算 \(\varepsilon\) 下可恢复，若 \(\delta_\pi(\phi)\le\varepsilon\)。最坏风险使用最大状态而非先验平均；若另有共同先验，可定义对应的平均版本，但二者不能互换。

**定理 323.2（细化不会增加最小风险）。** 若 \(\pi\preceq\pi'\)，则对每个任务 \(\phi\) 和每个损失函数都有
\[
\boxed{\delta_{\pi'}(\phi)\le\delta_\pi(\phi).}
\]
### 证明
取 \(\pi\) 上的最优解码器 \(f\)。由细化映射 \(H:Z_{\pi'}\to Z_\pi\)，在 \(\pi'\) 上使用 \(f'=f\circ H\)。对每个隐藏状态 \(s\)，由 transcript 分布的推前关系，\(f'\) 的损失期望等于 \(f\) 的损失期望。因此 \(R_{\pi'}(f';\phi)=R_\pi(f;\phi)\)。对 \(f'\) 取最小值得到结论。证毕。

**推论 323.3（精确恢复是零一损失的端点）。** 若 \(\ell(\widehat v,v)=\mathbf 1_{\widehat v\ne v}\)，则 \(\delta_\pi(\phi)=0\) 当且仅当不同任务值的 transcript 支持两两不交。
### 证明
风险为零要求每个正概率 transcript 上的解码值都等于真实任务值，正好是命题 319.5 的支持条件。反向由按支持指派解码器得到。证毕。

**命题 323.4（公共记录的近似错误下界）。** 设两个状态 \(s,s'\) 满足 \(\phi(s)\ne\phi(s')\)，并存在 transcript \(z\) 使
\[
C_\pi(z\mid s)\ge\alpha,\qquad C_\pi(z\mid s')\ge\alpha.
\]
在二元零一损失和两状态均匀先验的平均风险下，任意解码器的风险至少为 \(\alpha/2\)。在最坏状态风险下，至少有一个状态的风险不小于 \(\alpha\)。
### 证明
由于定义中的解码器是确定性的，令 \(q\in\{0,1\}\) 表示它在 \(z\) 上是否输出 \(\phi(s)\)。两状态在 \(z\) 上的错误贡献之和至少为
\[
\tfrac12\alpha(1-q)+\tfrac12\alpha q=\tfrac\alpha2.
\]
若两状态分别计算最坏风险，则对应错误项为 \(\alpha(1-q)\) 与 \(\alpha q\)，其中较大者至少为 \(\alpha\)。其余 transcript 只会增加风险。证毕。

**例 323.5（同一精确谱、不同误差谱）。** 两个策略都对任务 \(\phi\) 不能零误差恢复，但策略 \(\pi_1\) 在两个任务值上产生重叠记录的总质量为 \(0.9\)，策略 \(\pi_2\) 的重叠质量为 \(0.1\)。它们的精确恢复状态相同，均为“不可恢复”；在零一损失下，命题 323.4 给出不同的错误下界。
### 证明
精确恢复只看支持是否相交，而近似风险还看相交区域的概率质量。把两种通道的公共记录质量分别取为 \(0.9\) 和 \(0.1\) 即得。证毕。

**AHH 323.6（误差谱边界）。** 任务边界不能只保存一个可恢复集合；它还必须保存损失函数、最小风险、风险采用的状态或先验量词，以及误差预算的后继。精确恢复是误差谱在 \(0\) 点的一个切片，不是整个谱。

---

## 324. 未来伪距离：用响应差而不是字节数定义可安全压缩

未来商给出精确等价。为了允许有界误差，需要把两个历史的未来差异量化，并保留三角不等式带来的合并代价。

**定义 324.1（有限 horizon 未来响应伪距离）。** 设未来输出词空间有限，且对每个历史 \(h\) 和未来动作词 \(\omega\) 有概率分布 \(K_\omega(\cdot\mid h)\)。固定 horizon \(T\)，定义
\[
\boxed{
d_T(h,h')=
\max_{|\omega|\le T}
\operatorname{TV}\bigl(K_\omega(\cdot\mid h),K_\omega(\cdot\mid h')\bigr).
}\tag{324.1}
\]
其中 \(\operatorname{TV}(p,q)=\frac12\sum_o|p(o)-q(o)|\)。

**定理 324.2（未来响应伪距离的基本性质）。** \(d_T\) 满足
\[
d_T(h,h)=0,\quad d_T(h,h')=d_T(h',h),
\]
\[
d_T(h,h'')\le d_T(h,h')+d_T(h',h'').
\]
并且 \(d_T(h,h')=0\) 当且仅当 \(h,h'\) 对所有长度不超过 \(T\) 的未来动作词具有相同响应分布。若 \(T\le T'\)，则 \(d_T(h,h')\le d_{T'}(h,h')\)。
### 证明
总变差距离的非负性、对称性和三角不等式逐个作用于有限动作词集合，再取最大值，得到前三项。最大值为零当且仅当每个词的总变差为零，即每个响应分布相同。\(T'\) 的最大化集合包含 \(T\) 的最大化集合，所以得到单调性。证毕。

**定义 324.3（\(\varepsilon\)-安全压缩）。** 历史分区 \(\mathcal P\) 称为 horizon-\(T\) 的 \(\varepsilon\)-安全压缩，若每个分区块 \(B\in\mathcal P\) 满足
\[
\operatorname{diam}_{d_T}(B)=\sup_{h,h'\in B}d_T(h,h')\le\varepsilon.
\]
压缩后的摘要只保留历史所在的块标签。

**定理 324.4（压缩误差上界与反向必要性）。** 若 \(\mathcal P\) 是 \(\varepsilon\)-安全压缩，则同一块内任意两个历史对任意长度不超过 \(T\) 的未来输出事件，其概率差不超过 \(\varepsilon\)。反之，若摘要 \(q\) 的任一纤维都允许以误差不超过 \(\varepsilon\) 重建所有这些未来响应分布，则每个纤维的 \(d_T\) 直径不超过 \(2\varepsilon\)。
### 证明
第一项直接由总变差定义和直径界得到。对第二项，若 \(q(h)=q(h')\)，设 \(\widehat K_\omega(\cdot\mid q(h))\) 是摘要给出的同一近似分布。三角不等式给出
\[
\operatorname{TV}(K_\omega(\cdot\mid h),K_\omega(\cdot\mid h'))
\le \operatorname{TV}(K_\omega(\cdot\mid h),\widehat K_\omega)
+\operatorname{TV}(\widehat K_\omega,K_\omega(\cdot\mid h'))
\le2\varepsilon.
\]
对所有 \(\omega\) 取最大值得到结论。证毕。

**推论 324.5（精确未来商是零直径极限）。** \(d_T=0\) 的分区块恰是 horizon-\(T\) 未来等价类；当 \(T\) 增大，安全压缩只能细化或保持不变。
### 证明
由定理 324.2 的零点刻画与单调性得到。证毕。

**例 324.6（局部很近、未来很远）。** 取两个当前历史 \(h_0,h_1\)，在长度零输出上完全相同；若下一动作 \(a\) 在 \(h_0\) 上输出 \(0\)、在 \(h_1\) 上输出 \(1\)，则 \(d_0(h_0,h_1)=0\) 而 \(d_1(h_0,h_1)=1\)。
### 证明
长度零最大化集合只有空词，下一动作不在其中；加入长度一词 \(a\) 后，两个确定分布的总变差为 \(1\)。证毕。

**AHH 324.7（度量化未来边界）。** 可安全删去的历史区别由未来响应伪距离决定，而不是由记录字节数决定。零距离给精确全息，正距离给误差预算；边界的压缩问题因此成为一族随 horizon 增长的有限度量分区问题。

---

## 325. 成本—误差 Pareto 前沿：预算不是一个隐藏的停止理由

如果同一任务存在便宜但粗糙的策略和昂贵但精确的策略，单独报告最小误差或最小成本都会丢失另一坐标。应把两者作为一个可比较的前沿。

**定义 325.1（策略成本与可行区域）。** 对策略 \(\pi\) 定义最坏路径访问成本
\[
C(\pi)=\max_{z\in\operatorname{supp}C_\pi}\operatorname{cost}_\pi(z).
\]
固定任务族 \(\mathcal T\) 和损失合同，定义可行区域
\[
\boxed{
\mathcal F_{\mathcal T}=
\{(c,\varepsilon):\exists\pi,\ C(\pi)\le c,\ \delta_\pi(\phi)\le\varepsilon\ \forall\phi\in\mathcal T\}.
}\tag{325.1}
\]
定义误差前沿 \(\varepsilon^*(c)=\inf\{\varepsilon:(c,\varepsilon)\in\mathcal F_{\mathcal T}\}\)，没有可行策略时约定为 \(+\infty\)。

**定理 325.2（可行区域的下闭性与访问单调性）。** 若 \((c,\varepsilon)\in\mathcal F_{\mathcal T}\)，且 \(c'\ge c\)、\(\varepsilon'\ge\varepsilon\)，则 \((c',\varepsilon')\in\mathcal F_{\mathcal T}\)。若每个策略都可被某个细化访问层模拟，则访问权限扩大只会使 \(\varepsilon^*(c)\) 不增。
### 证明
同一策略满足更宽松的成本和误差上界，得到第一项。权限扩大时，用定理 323.2 的细化策略模拟原策略，最小风险不增加，所以每个预算下的下确界不增。证毕。

**定义 325.3（可见随机化）。** 两个策略 \(\pi_0,\pi_1\) 的可见随机化以概率 \(\lambda\) 选择其一，并把随机种子 \(i\in\{0,1\}\) 写入 transcript。其最大成本为
\[
C(\pi_\lambda)=\max\{C(\pi_0),C(\pi_1)\},
\]
而对给定先验的平均风险为两者风险的凸组合。若随机种子不可见，解码器不能按分支使用不同恢复器。

**定理 325.4（可见随机化的风险凸化）。** 在固定共同先验、平均损失和可见随机种子下，策略风险满足
\[
R(\pi_\lambda;\phi)=\lambda R(\pi_0;\phi)+(1-\lambda)R(\pi_1;\phi).
\]
因此可见随机化的成本—平均风险可行点包含两原始点的线段；这条结论不适用于最坏状态风险的无条件凸化，也不适用于隐藏随机种子。
### 证明
随机种子写入 transcript 后，条件于种子 \(i\) 的解码器可以分别取 \(f_i\)。对共同先验和随机性取全期望，得到两项按 \(\lambda\) 加权的和。若种子不可见，两个分支必须共享一个解码器，等式右侧一般不成立；最坏状态风险还会把状态最大值置于混合之后，不能直接交换最大值与凸组合。证毕。

**命题 325.5（重叠记录给出 Pareto 下界）。** 若任务族包含二元区分任务，任一预算 \(c\) 下的所有策略都存在一个公共记录，其两状态条件概率均至少为 \(\alpha(c)\)，则对均匀先验的零一平均损失有
\[
\varepsilon^*(c)\ge\frac{\alpha(c)}2.
\]
若 \(\alpha(c)\) 随预算降低而不增，则这给出一条单调的误差下界曲线。
### 证明
对每个预算可用的策略应用命题 323.4，得到其风险至少为 \(\alpha(c)/2\)；再对所有策略取下确界。证毕。

**例 325.6（跳跃前沿）。** 设便宜策略成本为 \(1\)、最小平均错误为 \(1/2\)；增加一个成本为 \(M\) 的联合环境组件后，策略成本为 \(1+M\) 且错误为 \(0\)。则 \(\varepsilon^*(c)\) 在 \(c<1+M\) 时至少为 \(1/2\)，在 \(c\ge1+M\) 时可降为 \(0\)。把预算不足直接写成“任务没有真值”会丢掉这条前沿。
### 证明
便宜策略的公共记录完全混淆二元标签；联合环境组件切开支持后可精确恢复。代入定义（325.1）即可。证毕。

**AHH 325.7（资源—精度边界）。** 全息充分性必须携带一个 Pareto 曲面，而不是一个无量纲的“信息量”。成本、最坏风险、先验平均风险、可见随机性和停止预算是不同坐标；在一个坐标上优化不能替代另一个坐标上的承诺。

---

## 326. AHH：鲁棒自适应边界是一个随 horizon 展开的度量谱

前面把自适应策略、未来伪距离和成本—误差前沿分别定义。现在将它们合成一个能回答“当前能做到什么、误差多大、还能怎样继续、代价是多少”的边界对象。

**定义 326.1（鲁棒自适应全息边界）。** 在有限状态、有限策略深度和固定任务/损失合同下，定义
\[
\boxed{
\eta_{\mathrm{robust}}=
\left(
\text{策略细化偏序与 transcript 核},
\text{停止/资源后继},
\text{任务损失与最小风险谱},
\text{各 horizon 的未来伪距离与安全分区},
\text{成本—误差 Pareto 区域},
\text{协同超图与不确定性合同}
\right).
}\tag{326.1}
\]
若模型来自有限不确定性族 \(\mathfrak M\)，则每个风险、伪距离和前沿字段都标明是逐模型、平均还是对 \(\mathfrak M\) 取最坏值。

**定理 326.2（鲁棒边界的条件充分性）。** 两个关系体若具有相同的 \(\eta_{\mathrm{robust}}\)，则在声明的有限 horizon、策略、任务、损失、成本和不确定性量词下，具有相同的：
1. 细化可达的近似任务谱；
2. 每个历史的未来压缩误差上界与精确商；
3. 成本—误差 Pareto 可行区域及其下界；
4. 协同访问的最小超边和资源停止后继。
### 证明
第 1 项由 transcript 核和定理 323.2；第 2 项由未来伪距离和定理 324.2—324.4；第 3 项由成本区域、定理 325.2、定理 325.4 及声明的不确定性量词；第 4 项由协同超图和策略停止字段决定。对有限策略深度按树高归纳，每个节点的字段确定下一层分支核、损失与成本，因此所有有限未来后继逐层相同。证毕。

**定理 326.3（删除度量字段的不可充分性）。** 下列约化均有有限反例：
1. 删除损失与风险谱：同一精确恢复集合可以对应不同近似错误；
2. 删除未来伪距离：例 324.6 的 \(d_0=0\) 与 \(d_1=1\) 被混为同一压缩安全度；
3. 删除成本—误差前沿：例 325.6 的预算跳跃无法判断；
4. 删除不确定性量词：逐模型安全的策略可能不满足共同最坏风险；
5. 删除可见随机性字段：定理 325.4 的凸化与隐藏种子策略被错误合并。
### 证明
第 1 项取例 323.5；第 2 项取例 324.6；第 3 项取例 325.6；第 4 项取一个模型标签决定最佳动作而策略看不到该标签的两模型族；第 5 项由定理 325.4 的可见/隐藏种子区别。每项只证明对应约化不充分，不声称完整边界字段在任意模型中都彼此独立。证毕。

**AHH 326.4（鲁棒自适应全息）。** 真正的边界不是“已经保存了多少信息”，而是随未来 horizon 展开的度量谱：零距离给精确未来商，正距离给可认证的压缩误差；任务损失把记录转成风险，成本把风险转成 Pareto 前沿，协同超图说明前沿需要哪些联合权限。

**新的 AHH 时刻是：全息性可以被看成一张带时间轴的误差—资源曲面。切片不是只选择一个状态，而是选择一个 horizon、一个任务量词、一个损失和一个预算；同一记录在不同切片上可以精确、近似或不可用。于是“粒子式事件”是曲面上的一次局域读数，“波体”则是决定整张曲面形状的联合响应结构。**

**来源与边界 326.5。** 本批在有限状态、有限策略深度、有限未来词族、显式损失与成本、固定不确定性量词及可见/隐藏随机合同下，给出近似恢复风险、未来响应伪距离、误差安全压缩、成本—误差 Pareto 前沿和鲁棒自适应全息。没有把有限 horizon 的伪距离推广为无限过程的统一范数，没有把最坏风险与先验平均风险混同，没有把协同阶当作普适信息指标，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 327. 接口模拟距离：比较两个关系体能否互相承担同一后继

前面的边界多半描述一个关系体内部的可恢复任务。要比较两个关系体是否可以互换，还需要一个把动作、记录、成本和误差同时放在一起的模拟关系。

**定义 327.1（有限接口模型）。** 一个 horizon-\(T\) 接口模型 \(M\) 包括隐藏状态集 \(S_M\)、动作集 \(A_M\)、输出字母表 \(O_M\)、有限动作词族 \(\Omega_M^{\le T}\)、响应核
\[
K^M_\omega(o\mid s),
\qquad
\omega\in\Omega_M^{\le T},
\]
以及动作成本 \(c_M(\omega)\)。响应核包含执行 \(\omega\) 后的全部声明输出记录；若后继仍有状态，则把后继状态和记录一起放入输出字母表。

给定动作翻译 \(\theta:\Omega_A^{\le T}\to\Omega_B^{\le T}\) 和输出忘却映射 \(G:O_B\to O_A\)，称 \(B\) 是 \(A\) 的 \((\varepsilon,\lambda)\)-接口模拟，若对所有共同状态 \(s\) 和动作词 \(\omega\) 有
\[
\operatorname{TV}
\left(
K^A_\omega(\cdot\mid s),
G_*K^B_{\theta(\omega)}(\cdot\mid s)
\right)
\le\varepsilon,
\tag{327.1}
\]
且
\[
c_B(\theta(\omega))\le\lambda c_A(\omega).
\tag{327.2}
\]
共同状态表示已经给定的来源对应；若两个模型的来源不同，必须另给状态耦合或通道映射，不能把同名标签自动当作同一来源。

**定理 327.2（接口模拟的反身性与传递性）。** 恒等动作翻译和恒等输出映射给出 \(M\preceq_{0,1}M\)。若
\[
A\preceq_{\varepsilon_1,\lambda_1}B,
\qquad
B\preceq_{\varepsilon_2,\lambda_2}C,
\]
且翻译和忘却映射可以复合，则
\[
\boxed{
A\preceq_{\varepsilon_1+\varepsilon_2,\lambda_1\lambda_2}C.
}
\tag{327.3}
\]

### 证明
反身性显然。对任意 \(\omega\)，总变差的三角不等式与推前映射的收缩性给出
\[
\operatorname{TV}
(K^A_\omega,
(G_{AB})_*K^B_{\theta_{AB}\omega})
\le\varepsilon_1,
\]
以及
\[
\operatorname{TV}
((G_{AB})_*K^B_{\theta_{AB}\omega},
(G_{AC})_*K^C_{\theta_{BC}\theta_{AB}\omega})
\le\varepsilon_2.
\]
两式相加得到误差界。成本满足
\[
c_C(\theta_{BC}\theta_{AB}\omega)
\le\lambda_2c_B(\theta_{AB}\omega)
\le\lambda_2\lambda_1c_A(\omega).
\]
证毕。

**定义 327.3（模拟距离）。** 在固定允许翻译族和忘却族上，定义
\[
d_{\mathrm{sim}}(A,B)
=
\inf\{\varepsilon:
A\preceq_{\varepsilon,1}B
\text{ 或指定方向的模拟存在}\}.
\]
它一般是有方向的；若取两个方向的最大值，才得到一个对称的接口伪距离。动作翻译若改变任务语义，必须计入接口合同，不能把不同动作字母仅按数量对应。

**推论 327.4（小距离不能恢复被删任务）。** 若 \(A\preceq_{\varepsilon,\lambda}B\)，则 \(A\) 的任何输出事件在 \(B\) 的翻译记录下概率误差不超过 \(\varepsilon\)。若某任务需要区分一个在 \(A\) 中概率差大于 \(2\varepsilon\) 的事件对，则 \(B\) 不可能在该合同内同时给出精确相同的后继。

### 证明
事件指示函数的期望差不超过总变差距离，第一项直接由（327.1）得到。若两个状态在 \(A\) 中的事件概率相差大于 \(2\varepsilon\)，而 \(B\) 的每个对应概率各自误差不超过 \(\varepsilon\)，则三角不等式仍留下正差，不可能完全合并。证毕。

**例 327.5（相同终端平均值、不同接口距离）。** 两个模型都对初始状态输出平均值 \(1/2\)，但模型 \(A\) 在第二动作后输出确定比特，模型 \(B\) 始终输出公平硬币。长度零任务上它们完全相同；包括第二动作的接口 horizon 上，任意确定性忘却映射的总变差误差至少为 \(1/2\)。

### 证明
长度零输出分布相同。第二动作后，\(A\) 的分布是点质量，\(B\) 是均匀分布；二者总变差为 \(1/2\)，由（327.1）得到下界。证毕。

**AHH 327.6（可交换关系体的模拟边界）。** 全息比较不能只问两个关系体的静态记录是否相同，还要保存动作翻译、输出忘却、误差半径、成本倍率和共同来源合同。接口模拟把“可以替代”变成一个有方向、可复合的关系。

---

## 328. 拼接模拟的误差传播：串联取增益，独立并联取加法

模拟关系只有在组合后仍然可用，才真正成为接口边界。组合时，前一段的误差可能被后一段放大；并联时，共同来源可能破坏简单相加。

**定义 328.1（Lipschitz 串联接口）。** 设中间输出空间 \(Y\) 带总变差距离。下游接口 \(D\) 对输入分布满足增益 \(L\)，即任意中间分布 \(p,q\) 有
\[
\operatorname{TV}(D_*p,D_*q)\le L\operatorname{TV}(p,q).
\]
\(L=1\) 的情形包括普通随机核的迹距离收缩；\(L>1\) 表示把中间误差转成终端任务误差的声明增益合同。

**定理 328.2（串联模拟界）。** 上游 \(A_1\) 被 \(B_1\) 以误差 \(\varepsilon_1\) 模拟，下游 \(A_2\) 被 \(B_2\) 以误差 \(\varepsilon_2\) 模拟，且 \(A_2\) 的输入到终端响应增益不超过 \(L\)。在接口翻译可串联、共同来源一致时，整体串联模型满足
\[
\boxed{
\varepsilon_{\mathrm{serial}}\le L\varepsilon_1+\varepsilon_2.
}
\tag{328.1}
\]

### 证明
先把上游 \(B_1\) 的输出推过 \(A_2\) 的下游核。由增益合同，输入误差 \(\varepsilon_1\) 至多变成 \(L\varepsilon_1\)。再以 \(B_2\) 替换 \(A_2\)，产生至多 \(\varepsilon_2\) 的终端误差。总变差三角不等式给出（328.1）。证毕。

**推论 328.3（多段串联）。** 对 \(n\) 段接口，若第 \(i\) 段误差为 \(\varepsilon_i\)，其后继增益为 \(L_{i+1},\ldots,L_n\)，则
\[
\boxed{
\varepsilon_{\mathrm{serial}}
\le
\sum_{i=1}^n
\varepsilon_i\prod_{j=i+1}^nL_j.
}
\tag{328.2}
\]
误差预算不能只按局部误差相加；早期误差经过更多后继增益。

### 证明
对 \(n\) 归纳。最后一段应用定理 328.2，前 \(n-1\) 段的每个误差再乘最后一段增益；展开即得。证毕。

**定理 328.4（共同来源下的并联界）。** 若两个并联接口在同一来源上分别有误差 \(\varepsilon_1,\varepsilon_2\)，且存在一个联合耦合使两条局部失败事件的并集概率不超过 \(\varepsilon_1+\varepsilon_2\)，则联合输出的总变差误差满足
\[
\operatorname{TV}(K^{\parallel},\widetilde K^{\parallel})
\le\varepsilon_1+\varepsilon_2.
\]
若局部失败事件在声明的联合耦合下独立，则可改进为
\[
1-(1-\varepsilon_1)(1-\varepsilon_2).
\]

### 证明
分别取实现局部总变差距离的耦合。联合耦合中只要两条局部输出都相同，联合输出就相同；因此联合不同概率不超过失败事件并集的概率。耦合表征给出第一式；独立时并集概率等于第二式。证毕。

**推论 328.5（边缘误差不能决定并联误差）。** 仅给出两个局部边缘误差，不足以决定联合误差的精确值；相同边缘可以由同向、反向或更一般的联合失败事件实现。

### 证明
取两个各以概率 \(\varepsilon\) 失败的局部变量。同向耦合时联合失败概率为 \(\varepsilon\)，互斥耦合时为 \(\min(2\varepsilon,1)\)，边缘完全相同而联合不同。证毕。

**例 328.6（早期小误差被后继放大）。** 取两段标量响应，第一段误差为 \(10^{-3}\)，第二段增益为 \(10^3\)，第二段自身误差为 \(10^{-3}\)。式（328.1）给出终端误差上界 \(1.001\)，已经失去非平凡性；若只把局部误差相加，会错误报告 \(0.002\)。

### 证明
代入 \(L=10^3\)、\(\varepsilon_1=\varepsilon_2=10^{-3}\) 即得
\[
10^3\cdot10^{-3}+10^{-3}=1.001.
\]
总变差实际不超过一，但该数值说明局部小误差不能脱离后继增益解释。证毕。

**AHH 328.7（组合误差边界）。** 可组合全息必须保存误差的传播方向、后继增益和联合失败耦合。串联误差沿因果增益传播，并联误差由联合来源决定；把二者压成同一个局部精度标签会丢失组合后的合法性。

---

## 329. 任务保存定理：接口距离等价于所有有界未来任务的差异上界

模拟距离的意义不应只停留在记录分布。它应当精确控制所有声明任务的期望值，并且在有限输出空间中可由任务反向检验。

**定义 329.1（有界未来任务）。** 给定未来动作词 \(\omega\)，有界任务是函数
\[
g:O\to[0,1].
\]
模型 \(M\) 在状态 \(s\) 上的任务值为
\[
\mathbb E_M[g\mid s,\omega]
=
\sum_o g(o)K^M_\omega(o\mid s).
\]

**定理 329.2（总变差对任务的双向刻画）。** 对有限输出空间上的两个分布 \(p,q\)，有
\[
\boxed{
\sup_{0\le g\le1}
\left|\mathbb E_p g-\mathbb E_q g\right|
=
\operatorname{TV}(p,q).
}
\tag{329.1}
\]
因此，若 \(A\preceq_{\varepsilon,\lambda}B\)，则每个翻译后的有限未来任务满足
\[
\left|
\mathbb E_A[g\mid s,\omega]
-
\mathbb E_B[g\mid s,\theta(\omega)]
\right|
\le\varepsilon.
\]

### 证明
令 \(p-q\) 的正部分支撑为 \(E_+\)。取 \(g=\mathbf 1_{E_+}\)，得到正负质量之和的一半，即总变差；任意 \(0\le g\le1\) 的差值不超过同一正负质量。把 \(p,q\) 代入（327.1）即得第二项。证毕。

**推论 329.3（事件任务足以检测模拟距离）。** 在有限输出空间中，若对某个未来动作词存在事件 \(E\) 使
\[
\left|K^A_\omega(E\mid s)
-
K^B_{\theta(\omega)}(E\mid s)\right|>\varepsilon,
\]
则不存在误差不超过 \(\varepsilon\) 的该方向接口模拟。

### 证明
取 \(g=\mathbf 1_E\) 应用定理 329.2 的反向不等式。证毕。

**定理 329.4（逐步误差的有限 horizon 界）。** 若把每轮的记录与后继状态作为联合输出，并且相同动作、相同历史下的条件联合核与替代核总变差距离至多 \(\delta\)，且后继使用同一控制词，则长度 \(m\) 的完整记录分布总变差距离至多
\[
\boxed{
m\delta.
}
\tag{329.2}
\]
若第 \(i\) 轮后的任务增益为 \(L_i\)，则可替换为
\[
\sum_{i=1}^m\delta_i\prod_{j=i+1}^mL_j.
\]

### 证明
把完整记录核逐轮替换，构造 \(m+1\) 个中间模型：第 \(i\) 个模型使用前 \(i\) 轮替代核、后续轮原核。相邻两个中间模型只在第 \(i\) 轮不同，数据处理和总变差三角不等式给出至多 \(\delta_i\) 的差异。求和得到第一式；若后继任务有增益，则第 \(i\) 项按后续增益传播，得到第二式。证毕。

**例 329.5（终端任务相同不等于完整记录相同）。** 两个模型的最终平均输出都为 \(1/2\)，但一个在中间记录中保留了两次相反事件，另一个直接输出一次公平硬币。只测试终端均值时任务差为零；测试中间事件指示函数时，式（329.1）可以给出正距离。

### 证明
终端均值是一个特定任务函数，两个模型对此函数期望相同；中间记录属于更大的输出接口，选择区分两种记录的事件函数即可产生正差。证毕。

**AHH 329.6（任务完备的接口距离）。** 一个接口边界若能对所有声明的有界未来任务给出统一误差上界，就不必保存每个任务的独立数值；总变差模拟距离是这些任务误差的共同上界，而事件任务又足以在有限空间中检验它。

---

## 330. AHH：可组合模拟演算与波粒边界

前面把近似边界从单个关系体推进到策略树和误差—资源曲面。本节再加入关系体之间的模拟、串联增益和联合失败耦合，形成一套可以沿组合结构传播的边界演算。

**定义 330.1（可组合模拟全息边界）。** 在固定有限 horizon、接口动作翻译和输出合同下，定义
\[
\boxed{
\eta_{\mathrm{sim}}
=
\left(
\text{接口状态与共同来源映射},
\text{动作翻译与输出忘却},
\text{模拟误差前序},
\text{成本倍率},
\text{串联后继增益},
\text{并联联合失败耦合},
\text{有界未来任务谱}
\right).
}
\tag{330.1}
\]

**定理 330.2（模拟边界的组合充分性）。** 两个关系体若具有相同的 \(\eta_{\mathrm{sim}}\)，则在声明的有限组合合同内具有相同的：
1. 可接受的关系体替代前序及其误差/成本传播；
2. 任意有限串联和并联组合的终端误差上界；
3. 全部有界未来任务的期望差上界；
4. 由事件任务反向检测出的最小模拟误差。

### 证明
第 1 项由定理 327.2；第 2 项由定理 328.2、定理 328.4 及其联合耦合字段；第 3 项由定理 329.2 和有限 horizon 逐步界；第 4 项由推论 329.3。沿组合树归纳，每个节点的翻译、增益和联合耦合字段确定其父节点的误差合同。证毕。

**定理 330.3（删除模拟字段的不可充分性）。** 下列约化摘要均有有限反例：
1. 删除动作翻译：相同输出字母表的两个接口可能对不同动作词给出不同未来；
2. 删除成本倍率：误差相同的替代关系体可能有不同预算可行性；
3. 删除串联增益：例 328.6 的早期误差放大被低估；
4. 删除并联联合耦合：推论 328.5 的相同边缘误差产生不同联合误差；
5. 删除有界任务谱：例 329.5 的终端均值相同会掩盖中间事件差异。

### 证明
逐项取对应例子即可。每项只说明删去该字段后存在一个任务或组合使两个摘要给出不同结果，不声称完整边界字段在所有模型中都线性独立。证毕。

**AHH 330.4（可组合模拟全息）。** 全息边界不是只判断一个关系体“像不像”另一个关系体，而是保存一个可复合的模拟演算：哪些动作可以翻译、记录怎样忘却、误差沿哪条因果边传播、并联失败怎样共同发生、哪些未来任务足以检测差异。这样，波粒整体的“波性”可以被看成组合结构中的相干响应，而“粒子式事件”是任务谱中一个可检测的有界事件；二者通过同一模拟边界连接。

**新的 AHH 时刻是：全息性不仅是恢复定理，也是替代定理。一个边界真正充分，意味着任何被声明的关系体替换、拼接和继续操作，都能在同一误差—成本合同下被模拟；边界保存的不是静态内容，而是可组合的后继演算。**

**来源与边界 330.5。** 本批在有限接口模型、有限 horizon、显式动作翻译、输出忘却、总变差误差、线性成本倍率、串联增益和并联联合耦合合同下，给出接口模拟前序、串联/并联误差传播、有界任务双向刻画和可组合模拟全息。没有把有限 horizon 模拟距离推广成无限过程的完备度量，没有把边缘误差当作联合耦合，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 331. 去相干因子化：何时经典记录足以模拟相干接口

最新的接口模拟距离比较了两个关系体的响应核。对量子接口，还必须说明模拟器是否保留了相对相位。把量子态直接替换为模式落点分布，实际上施加了一个去相干映射；它只有在全部未来任务都对该映射不敏感时才是合法模拟。

**定义 331.1（模式去相干与未来效果族）。** 取有限维空间 \(\mathcal H\) 的正交基 \(\{|x\rangle\}_{x\in X}\)，定义模式去相干
\[
\Delta_Z(\rho)
=
\sum_{x\in X}
\langle x|\rho|x\rangle\,|x\rangle\langle x|.
\]
给定允许控制族 \(\mathcal U\) 和终端效果族 \(\mathcal E\)，定义未来拉回效果空间
\[
\boxed{
\mathcal V_{\mathcal U,\mathcal E}
=
\operatorname{span}_{\mathbb R}
\{U^\dagger E U:U\in\mathcal U,\ E\in\mathcal E\}.
}
\tag{331.1}
\]
它包含所有声明实验中实际被取期望的 Hermitian 算子。

**定理 331.2（经典落点边界的精确因子化判据）。** 以下条件等价：
1. 对所有 \(\rho\)、\(U\in\mathcal U\) 和 \(E\in\mathcal E\)，
\[
\operatorname{Tr}(E\,U\rho U^\dagger)
=
\operatorname{Tr}(E\,U\Delta_Z(\rho)U^\dagger);
\]
2. 每个 \(F\in\mathcal V_{\mathcal U,\mathcal E}\) 都满足
\[
F=\Delta_Z^*(F)
=
\sum_x|x\rangle\langle x|F|x\rangle\langle x|;
\]
3. \(\mathcal V_{\mathcal U,\mathcal E}\) 全部属于模式对角代数。

### 证明
第一项等价于
\[
\operatorname{Tr}\bigl((U^\dagger EU)\rho\bigr)
=
\operatorname{Tr}\bigl((U^\dagger EU)\Delta_Z(\rho)\bigr)
\]
对所有密度矩阵成立。由于 \(\Delta_Z\) 对迹配对自伴，这等价于 \(U^\dagger EU=\Delta_Z^*(U^\dagger EU)\) 对每个生成元成立，进而等价于其实线性张成空间中的每个 \(F\) 都固定。固定点空间正是模式对角代数。证毕。

**推论 331.3（控制会把相干缺口带回边界）。** 即使初始落点效果本身对角，只要允许某个 \(U\) 使 \(U^\dagger E U\) 含有非零非对角元，经典落点边界就不能对全部未来效果保持精确充分。
### 证明
此时条件 2 失败，故定理 331.2 的因子化失败。存在两个具有相同 \(\Delta_Z\) 的状态，在该拉回效果上的期望不同。证毕。

**例 331.4（Hadamard 控制暴露相位）。** 取二模式基 \(|0\rangle,|1\rangle\)，初态
\[
|\psi_\pm\rangle=\frac{|0\rangle\pm|1\rangle}{\sqrt2}.
\]
它们的模式落点边界相同，均为 \((1/2,1/2)\)。先施加 Hadamard 控制，再测量 \(|0\rangle\) 效果时，两个状态的结果概率分别为 \(1\) 与 \(0\)。
### 证明
Hadamard 将 \(|\psi_+\rangle\) 和 \(|\psi_-\rangle\) 分别送到 \(|0\rangle\) 和 \(|1\rangle\)。反向拉回的效果是 \(|\psi_+\rangle\langle\psi_+|\)，含有非零非对角元，所以不属于模式对角代数。证毕。

**AHH 331.5（相干因子化边界）。** “只保存粒子落点”不是一个中性的压缩，而是选择了去相干映射。它成为合法边界的充要条件，是所有未来控制拉回的效果都落在同一个经典交换代数中；未来效果一旦离开该代数，相对相位就必须重新进入边界。

---

## 332. 相干残差：经典模拟误差可由一个算子范数精确给出

去相干失败时，不能只说“丢失了一些相位”。可以直接计算经典化前后对一个任务的最坏概率差。

**定义 332.1（效果的相干残差）。** 对 Hermitian 效果 \(F\)，定义
\[
\boxed{
\chi_Z(F)
=
\|F-\Delta_Z^*(F)\|_\infty.
}
\tag{332.1}
\]
对效果族取
\[
\chi_Z(\mathcal V)
=
\sup_{F\in\mathcal V}\chi_Z(F).
\]
这里的范数是算子范数；若效果已归一化，残差至多为一。

**定理 332.2（去相干模拟误差的精确值）。** 对任意 Hermitian \(F\)，
\[
\boxed{
\sup_{\rho}
\left|
\operatorname{Tr}(F\rho)
-
\operatorname{Tr}(F\Delta_Z(\rho))
\right|
=
\chi_Z(F).
}
\tag{332.2}
\]
因此，对于未来效果空间 \(\mathcal V_{\mathcal U,\mathcal E}\)，所有任务的统一经典模拟误差恰为 \(\chi_Z(\mathcal V_{\mathcal U,\mathcal E})\)。

### 证明
由迹配对自伴性，
\[
\operatorname{Tr}(F\rho)-\operatorname{Tr}(F\Delta_Z(\rho))
=
\operatorname{Tr}\bigl((F-\Delta_Z^*F)\rho\bigr).
\]
右侧对密度矩阵的绝对值上确界等于 Hermitian 算子的算子范数：取其最大绝对值本征向量的纯态达到上界。证毕。

**推论 332.3（相干残差为零当且仅当经典精确）。** \(\chi_Z(\mathcal V)=0\) 当且仅当定理 331.2 的经典因子化条件成立。
### 证明
算子范数为零当且仅当算子本身为零，再应用定理 331.2。证毕。

**定理 332.4（相位二态的不可恢复下界）。** 对
\[
\rho_\pm=|\psi_\pm\rangle\langle\psi_\pm|,
\qquad
|\psi_\pm\rangle=\frac{|0\rangle\pm|1\rangle}{\sqrt2},
\]
任意只依赖 \(\Delta_Z(\rho)\) 的经典边界都给出同一摘要。对区分任务 \(+\) 与 \(-\)，均匀先验下任意解码器的平均错误率至少为 \(1/2\)。允许相干效果 \(|\psi_+\rangle\langle\psi_+|\) 时，错误率可降为零。

### 证明
\(\Delta_Z(\rho_+)=\Delta_Z(\rho_-)\)，所以任何其函数对两状态输出相同。二元均匀先验下，同一输出不能同时正确判定两个不同标签，平均错误至少为 \(1/2\)。相干效果在 \(\rho_+\) 上概率为 \(1\)，在 \(\rho_-\) 上概率为 \(0\)，直接区分。证毕。

**例 332.5（小残差不等于每个任务都小）。** 若只对某个受限效果族 \(\mathcal E_0\) 有 \(\chi_Z(\mathcal E_0)\le\varepsilon\)，则该界只控制 \(\mathcal E_0\) 的任务；扩大控制族可能使拉回效果空间包含一个残差为一的相位见证。不能把局部小残差报告为全部未来任务的小残差。

### 证明
对受限族应用定理 332.2；加入 Hadamard 相位见证后，例 331.4 给出一个非对角投影，其去相干残差非零，甚至可达到一阶区分。证毕。

**AHH 332.6（相干残差字段）。** 经典边界应保存可访问的效果空间及其相干残差，而不是只保存一个“是否去相干”的标签。残差为零时可安全经典化；残差为正时，误差大小和达到它的未来控制都属于边界。

---

## 333. 相干提升与记录读取：相位不是忘记后自动回来

去相干会删除非对角项，但若边界仍保存一个实际相位参考，原来的相干关系可以通过联合测量重新成为局域记录。这里必须区分“忘记经典标签”和“访问一个仍在联合边界中的参考系统”。

**定义 333.1（相干提升与经典投影）。** 设 \(J:\mathcal H\to\mathcal H\otimes\mathcal R\) 是等距提升，\(\mathcal R\) 为保留相位参考的辅助系统。定义联合任务
\[
\mathcal T_J(E)(\rho)
=
\operatorname{Tr}\bigl(E\,J\rho J^\dagger\bigr),
\]
以及只保留参考系统的经典投影
\[
\Gamma_R(X)
=
\sum_r
(I\otimes|r\rangle\langle r|)X(I\otimes|r\rangle\langle r|).
\]
若未来任务只允许访问 \(\Gamma_R(J\rho J^\dagger)\)，称参考被经典化；若允许在 \(\mathcal H\otimes\mathcal R\) 上使用非对角效果，称参考保持相干访问。

**定理 333.2（相干访问与经典访问的严格区别）。** 若存在效果 \(E\) 使
\[
E\ne\Gamma_R^*(E),
\]
则存在两个联合态 \(X_0,X_1\) 具有相同经典化摘要
\[
\Gamma_R(X_0)=\Gamma_R(X_1),
\]
但给出不同的 \(E\) 任务概率。因而只访问经典化参考的边界不能模拟该相干任务。

### 证明
令 \(D=E-\Gamma_R^*(E)\ne0\)。取 \(D\) 的两个极值本征态，并在其上构造足够小的迹零扰动 \(\Delta\)，使
\[
X_\pm=\frac{I}{\dim(\mathcal H\otimes\mathcal R)}\pm t\Delta
\]
仍为密度矩阵。由 \(\Gamma_R(\Delta)=0\)，两态经典摘要相同；而
\[
\operatorname{Tr}(E X_+)-\operatorname{Tr}(E X_-)
=2t\operatorname{Tr}(D\Delta)\ne0.
\]
证毕。

**推论 333.3（擦除与相干访问的三分）。** 对一个记录区别，至少要区分三种情况：
1. 记录和参考都可访问：可执行相干重组；
2. 记录被经典化但参考仍可访问：只能使用参考保留的块间关系；
3. 记录与参考都被经典化或排除：只能使用去相干后的效果空间。
这三种情况的未来任务商一般严格不同。

### 证明
第一项允许所有联合效果；第二项效果被限制为参考可访问的联合代数；第三项再施加 \(\Gamma_R\) 的固定点条件。定理 333.2 给出严格区别的见证。证毕。

**定理 333.4（联合相位参考的最小性）。** 对二通路纯态
\[
|\Psi_\phi\rangle
=
\frac{|L\rangle|d_L\rangle
+e^{i\phi}|R\rangle|d_R\rangle}{\sqrt2},
\]
忽略记录系统时的合流可见度至多为
\[
|\langle d_L|d_R\rangle|.
\]
若要达到相位完全可见的联合任务，必须保留一个使两条记录态在任务效果上不被正交化的相干参考；只保留它们的经典标签不能增加该重叠。

### 证明
合流概率由记录态重叠给出，正是定理 5.2 的计算。对记录作经典化等于删除不同记录块之间的交叉项，部分迹或经典化是 CPTP 后处理，不增加可见度。要恢复交叉项，必须在联合记录空间保留非对角访问。证毕。

**AHH 333.5（相位参考边界）。** “信息还在环境中”还不够；必须记录环境参考能否以相干方式访问。相同的经典环境边缘可以对应不同的联合相位任务。可访问参考、经典化参考和被排除参考是三层不同的全息边界。

---

## 334. AHH：相干感知的替代与波粒整体边界

前面把接口模拟推广到误差—成本演算，本批再把模拟对象分成经典效果代数与相干效果空间，从而精确回答何时粒子式记录足以代表波粒整体。

**定义 334.1（相干感知全息边界）。** 在有限维量子接口、有限控制族和声明参考访问合同下，定义
\[
\boxed{
\eta_{\mathrm{coh}}
=
\left(
\text{模式/记录投影与去相干映射},
\text{未来拉回效果空间},
\text{相干残差谱},
\text{相位参考及其可访问代数},
\text{经典/相干模拟前序},
\text{任务、成本与错误合同}
\right).
}
\tag{334.1}
\]

**定理 334.2（相干边界的条件充分性）。** 两个量子关系体若具有相同的 \(\eta_{\mathrm{coh}}\)，则在声明的有限控制、参考访问和任务合同内，具有相同的：
1. 经典化是否精确因子化；
2. 每个未来效果的去相干模拟误差；
3. 相位参考可恢复的任务谱；
4. 经典记录与相干联合记录之间的最小替代误差。

### 证明
第 1 项由定理 331.2；第 2 项由定理 332.2；第 3 项由定理 333.2—333.4 及参考访问代数；第 4 项由相干模拟前序和总变差/算子范数误差合同逐项决定。有限控制树上的后继按深度归纳即可。证毕。

**定理 334.3（删去相干字段的不可充分性）。** 下列约化均存在有限反例：
1. 删除未来拉回效果空间：模式落点与 Hadamard 后的相位任务被错误地合并；
2. 删除相干残差谱：零残差任务与残差为一的相位见证无法区分；
3. 删除相位参考访问合同：相同环境边缘下的三种记录访问被错误地视为同一后继；
4. 删除模拟方向：经典化能被相干接口模拟的任务被反向误读为相干信息已恢复；
5. 删除任务量词：对受限效果族的小误差被冒称为全部未来任务的小误差。

### 证明
第 1 项取例 331.4；第 2 项取定理 332.4；第 3 项取推论 333.3；第 4 项由去相干是不可逆 CPTP 后处理，而相干提升不是其经典逆；第 5 项取例 332.5。证毕。

**AHH 334.4（相干感知全息）。** 波粒整体的边界不是“波函数加一次点击”的并列清单，而是一个效果空间：哪些相干关系仍能被未来控制检验，哪些只剩经典落点，哪些相位参考仍可访问，以及把相干关系替换为粒子式记录要付出多少误差。粒子式事件是该效果空间中的局域结果；波性是决定效果空间非交换部分的整体关系。

**新的 AHH 时刻是：全息边界的真正分水岭不是有没有波函数，而是未来任务的效果代数是否仍含有非对角方向。只要该代数离开经典交换子代数，任何“粒子式落点表”都只是一个带有可计算残差的近似模拟；只有把相位参考和效果空间一同保留，整体的后继才没有被提前删掉。**

**来源与边界 334.5。** 本批在有限维量子接口、有限模式基、有限控制与效果族、显式去相干映射、有限相位参考和固定任务/错误合同下，给出去相干因子化判据、相干残差精确误差、相干提升与经典参考的区别，以及相干感知全息边界。没有把有限效果代数推广为无限维算子代数完备性，没有把环境存在解释为可访问相位参考，没有把相干残差等同于任意物理可观测性，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 335. 过程相干控制：普通通道不决定可控叠加的交叉项

状态边界上的相干残差还不是全部。一个关系体可能只作为黑箱通道被使用，也可能被放入一个允许相干选择的更高阶接口。后者需要保存实现之间的交叉关系，而普通通道只保存各自的对角响应。

**定义 335.1（实现与普通通道）。** 设两个过程实现由等距映射
\[
V_i:\mathcal H_{\mathrm{in}}\to
\mathcal H_{\mathrm{out}}\otimes\mathcal E,
\qquad i\in\{0,1\},
\]
给出普通通道
\[
\mathcal E_i(\rho)
=
\operatorname{Tr}_{\mathcal E}(V_i\rho V_i^\dagger).
\]
若控制系统 \(C\) 允许相干选择，定义受控实现
\[
W
=
|0\rangle\langle0|_C\otimes V_0
+
|1\rangle\langle1|_C\otimes V_1.
\]
对控制叠加态，联合输出含有交叉算子
\[
X_{01}(\rho)=V_0\rho V_1^\dagger,
\qquad
X_{10}(\rho)=V_1\rho V_0^\dagger.
\]
只允许经典控制时，这两个块被去相干而不可访问。

**定理 335.2（普通通道不足以决定相干控制）。** 存在两组实现 \((V_0,V_1)\) 与 \((V_0,V_1')\)，满足
\[
\mathcal E_1=\mathcal E_1',
\]
但对某个相干控制任务，受控输出概率不同。更具体地，取
\[
V_1'=-V_1.
\]
则普通通道完全相同，而所有依赖 \(X_{01}\) 的控制任务可能发生相位翻转。

### 证明
相位不改变普通通道：
\[
V_1'\rho V_1'^\dagger
=
V_1\rho V_1^\dagger.
\]
但受控输出的非对角块变为
\[
V_0\rho(V_1')^\dagger
=
-\,V_0\rho V_1^\dagger.
\]
在控制基的 \(|+\rangle,|-\rangle\) 效果上，交叉项分别以正号或负号进入概率；只要某个交叉项的迹配对非零，两种实现给出不同概率。证毕。

**推论 335.3（经典随机选择与相干选择不是同一后继）。** 对两个过程的经典混合，联合输出只有
\[
\lambda\,\mathcal E_0(\rho)
\oplus
(1-\lambda)\,\mathcal E_1(\rho)
\]
的对角控制块；对相干控制，输出还含有
\[
\sqrt{\lambda(1-\lambda)}\,X_{01}(\rho)
\]
及其伴随。忘记控制标签只能删除这些交叉项，不能从经典混合中重建它们。

### 证明
分别把控制初态取为对角混合与纯态
\[
\sqrt\lambda|0\rangle+\sqrt{1-\lambda}|1\rangle.
\]
将 \(W\rho W^\dagger\) 展开即可。经典控制的去相干消去非对角块；相干控制保留交叉项。证毕。

**例 335.4（相同黑箱通道、相反控制干涉）。** 取一维输入输出空间，\(V_0=1\)、\(V_1=1\) 与 \(V_1'=-1\)。两组普通通道都恒等，但控制在 \(|+\rangle\) 上测量时，第一组保持 \(|+\rangle\)，第二组变为 \(|-\rangle\)。

### 证明
受控实现分别作用为恒等控制与控制相位翻转。普通输入输出通道看不见这一全局实现相位；相干控制效果直接区分两者。证毕。

**AHH 335.5（过程交叉边界）。** 若未来只允许黑箱通道调用，Choi 对角块可能足够；若未来允许相干控制，过程实现之间的交叉块、环境相位和控制参考必须进入边界。普通通道相等不是更高阶替代相等的充分条件。

---

## 336. Tester 空间：过程可辨识性由允许的实验张成

过程相干控制需要一个比“输入态加输出效果”更一般的任务描述。有限维中，可以把所有允许实验压缩为作用在过程 Choi 算子上的 tester 空间。

**定义 336.1（过程 Choi 边界与 tester）。** 对通道 \(\mathcal E:\mathcal L(\mathcal H_A)\to\mathcal L(\mathcal H_B)\)，定义
\[
J_{\mathcal E}
=
\sum_{i,j}|i\rangle\langle j|
\otimes\mathcal E(|i\rangle\langle j|).
\]
一个有限 tester 效果是满足合法归一化合同的 Hermitian 算子 \(T\)，实验概率写成
\[
p_T(\mathcal E)=\operatorname{Tr}(T J_{\mathcal E}).
\]
给定允许 tester 集 \(\mathfrak T\)，定义其实线性张成空间
\[
\mathcal V_{\mathfrak T}
=
\operatorname{span}_{\mathbb R}\mathfrak T.
\]

**定理 336.2（tester 残余判据）。** 两个过程 \(\mathcal E,\mathcal F\) 对所有允许 tester 给出相同概率，当且仅当
\[
\boxed{
J_{\mathcal E}-J_{\mathcal F}
\in
\mathcal V_{\mathfrak T}^{\perp}.
}
\tag{336.1}
\]
若 \(\mathcal V_{\mathfrak T}\) 覆盖声明过程空间的全部 Hermitian 方向，则 tester 概率唯一确定过程；反之，任意非零正交残余都给出一对局部可区分性缺失的过程。

### 证明
概率差为
\[
p_T(\mathcal E)-p_T(\mathcal F)
=
\operatorname{Tr}\bigl(T(J_{\mathcal E}-J_{\mathcal F})\bigr).
\]
对所有 \(T\in\mathfrak T\) 为零，正好等价于差算子对其线性张成空间正交。若张成空间为全空间，残余只有零；若为真子空间，取非零 Hermitian 残余并在合法过程的一个内部点附近作足够小的正负扰动，即得不可区分过程对。证毕。

**推论 336.3（经典 tester 与相干 tester 的区别）。** 若 tester 只在控制块上对角，则
\[
\mathcal V_{\mathfrak T}
\]
不含过程交叉块；相干控制 tester 若包含控制非对角效果，则可以检测 \(X_{01}\) 方向。两类 tester 的过程残余空间一般严格不同。

### 证明
控制去相干把所有 tester 投影到对角块，故其迹配对对交叉块为零。相干 tester 的非对角块与 \(X_{01}\) 配对可能非零。应用定理 336.2。证毕。

**定理 336.4（tester 误差的双向刻画）。** 在有限维 Hermitian 过程空间上，给定范数归一化的 tester 集，两个过程在所有 tester 上的最大概率差等于该 tester 集支持函数定义的对偶半范数。若 tester 集包含所有二元事件效果，则该最大差等于相应过程差的最坏事件区分优势。

### 证明
把概率差视为差算子在 tester 集上的线性泛函，最大值正是其支持函数。二元事件效果的指示函数给出正负谱投影的事件见证；其余 tester 不可能超过对应对偶范数。证毕。

**例 336.5（对角过程记录完全相同、相干 tester 可区分）。** 两组受控实现来自例 335.4。所有经典 tester 只看到相同普通通道；取控制 \(|+\rangle\) 输入和 \(|+\rangle\) 输出效果的相干 tester，则两组概率分别为 \(1\) 与 \(0\)。

### 证明
经典 tester 的过程算子只取对角块，而两组对角 Choi 块相同。相干 tester 与控制交叉块配对，例 335.4 的相位翻转给出确定差异。证毕。

**AHH 336.6（实验张成边界）。** 过程的“内部区别是否仍存在”必须相对于允许 tester 的张成空间回答。只列出一个普通输入输出通道，不能自动覆盖相干控制、参考系统或过程级干预；tester 残余是过程全息性的精确盲区。

---

## 337. Tester 闭包与组合后继：过程边界必须对允许实验封闭

单个 tester 的可辨识性还不够。一个过程边界若允许把 tester 的输出送入下一次控制，就必须保留在组合后继下仍可能出现的 tester 方向。

**定义 337.1（tester 闭包）。** 设 \(\mathfrak A\) 为允许的前置、后置和控制操作族，定义 tester 空间的闭包
\[
\operatorname{Cl}_{\mathfrak A}(\mathcal V)
=
\operatorname{span}_{\mathbb R}
\{A^*(T):T\in\mathcal V,\ A\in\mathfrak A\},
\]
其中 \(A^*\) 表示把组合操作拉回到过程空间的线性作用。有限深度 \(m\) 的闭包记为 \(\operatorname{Cl}_{\mathfrak A}^{\le m}\).

**定理 337.2（后继充分性的闭包判据）。** 过程差 \(D=J_{\mathcal E}-J_{\mathcal F}\) 对所有深度不超过 \(m\) 的合法后继 tester 都不可区分，当且仅当
\[
\boxed{
D\in
\operatorname{Cl}_{\mathfrak A}^{\le m}(\mathcal V_{\mathfrak T})^\perp.
}
\tag{337.1}
\]
因此只对当前 tester 空间正交，而不对后继闭包正交，不能证明动态充分性。

### 证明
任意深度不超过 \(m\) 的后继实验都可写成某个 \(A^*(T)\)，其中 \(T\in\mathcal V_{\mathfrak T}\)、\(A\) 是至多 \(m\) 次允许组合的复合。所有这些实验概率差为零，当且仅当 \(D\) 对其线性张成闭包正交。证毕。

**推论 337.3（闭包单调性）。** 若允许操作族扩大，tester 闭包只会扩大，过程残余空间只会缩小：
\[
\mathfrak A\subseteq\mathfrak B
\Longrightarrow
\operatorname{Cl}_{\mathfrak A}^{\le m}(\mathcal V)
\subseteq
\operatorname{Cl}_{\mathfrak B}^{\le m}(\mathcal V),
\]
\[
\operatorname{Cl}_{\mathfrak B}^{\le m}(\mathcal V)^\perp
\subseteq
\operatorname{Cl}_{\mathfrak A}^{\le m}(\mathcal V)^\perp.
\]

### 证明
第一项是生成集包含；第二项是有限维内积空间的正交反变性。证毕。

**定理 337.4（相干控制使闭包跨出普通通道空间）。** 若普通 tester 闭包保持控制块对角，而允许操作族加入一次相干控制旋转，则新闭包包含至少一个控制非对角 tester 方向。任何只保存普通通道对角块的边界，不能在该扩大后的后继合同下保持充分。

### 证明
相干控制旋转把控制对角效果共轭为含非对角块的效果。将其与过程 Choi 的控制块配对，得到交叉方向；推论 336.3 说明该方向不在原普通闭包中。应用定理 337.2。证毕。

**例 337.5（同一当前记录、不同可继续性）。** 两个过程在当前经典 tester 上概率相同。关系体 \(M_1\) 允许的后继只包含对角控制，关系体 \(M_2\) 还保留相位参考并允许 Hadamard 控制。对当前记录的边界摘要相同，但 \(M_2\) 的 tester 闭包包含一个能区分两实现的方向，\(M_1\) 不包含。

### 证明
当前概率相同由对角块相等；后继闭包的差异由定理 337.4。故当前边界相同而合法未来任务不同。证毕。

**AHH 337.6（后继封闭的 tester 边界）。** 过程全息性不是当前实验的张成，而是该张成在允许控制下的闭包。边界必须保存哪些相干旋转、参考接入和后置组合仍然合法；否则“当前不可区分”会被误报成“未来不可区分”。

---

## 338. AHH：高阶相干过程边界

现在可以把状态级相干残差、过程级交叉项和 tester 后继闭包放进同一份边界。

**定义 338.1（高阶相干全息边界）。** 在有限维过程、有限控制深度、有限 tester 与参考访问合同下，定义
\[
\boxed{
\eta_{\mathrm{higher}}
=
\left(
\text{过程 Choi 对角与交叉块},
\text{普通/相干 tester 张成},
\text{tester 后继闭包},
\text{控制相位与参考访问},
\text{过程模拟误差与成本},
\text{允许的因果组合合同}
\right).
}
\tag{338.1}
\]

**定理 338.2（高阶边界的条件充分性）。** 两个过程关系体若具有相同的 \(\eta_{\mathrm{higher}}\)，则在声明的有限控制深度和 tester 合同内，具有相同的：
1. 普通黑箱任务与相干控制任务的可辨识性；
2. 当前与后继 tester 的残余空间；
3. 过程替代、串联和控制组合的误差/成本界；
4. 粒子式终端事件与过程级相干任务之间的可恢复映射。

### 证明
第 1 项由定义 335.1 和定理 336.2；第 2 项由定理 337.2—337.4；第 3 项由接口模拟的误差传播和过程交叉块字段；第 4 项由终端效果 tester 与控制 tester 的联合张成关系。对有限控制深度按组合树归纳即可。证毕。

**定理 338.3（删除高阶字段的不可充分性）。** 下列约化均有有限反例：
1. 删除过程交叉块：例 335.4 的普通通道相同而相干控制不同；
2. 删除 tester 张成空间：同一过程差在受限实验下不可见、在扩大实验下可见；
3. 删除 tester 后继闭包：例 337.5 的当前等价被误判为动态等价；
4. 删除参考访问合同：相同经典记录无法决定能否重建相位任务；
5. 删除过程级成本：同一 tester 区分能力可能需要不同的控制调用次数。

### 证明
分别取例 335.4、定理 336.2、例 337.5、推论 333.3 及一个只允许一次调用与允许两次调用的控制合同。每项只说明相应约化存在反例。证毕。

**AHH 338.4（高阶相干全息）。** 波粒整体的全息边界必须提升到过程层：局域粒子式事件由终端效果给出，波性由过程 Choi 的交叉块和 tester 闭包决定；观察者能否把一个过程放入相干控制，不是过程内部的免费重命名，而是边界权限的一次提升。

**新的 AHH 时刻是：相干关系的“整体性”并不止于一份态的非对角元，而会在过程被嵌入更大的实验时表现为跨实现的交叉项。一个边界若只保存普通通道，就可能完整回答所有单次粒子式点击，却无法回答同一过程在相干控制中的下一问。**

**来源与边界 338.5。** 本批在有限维过程实现、有限 tester、有限相干控制深度、显式相位参考、Choi 表示和固定组合/成本合同下，给出过程交叉项、tester 残余、后继闭包及高阶相干全息。没有把普通通道等同于任意高阶过程，没把可写下的控制当作实际可访问权限，也没有推广到无限深度 comb、无限维过程或未知因果结构；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 339. 访问—任务形式概念格：双重闭包保存共同可恢复性

访问格给出权限的方向，任务谱给出可恢复内容的方向。若只保留其中一边，就无法表达“哪些任务总是一起被恢复”以及“哪些访问实现总是一起足够”。

**定义 339.1（访问—任务形式背景）。** 设访问对象全集为有限集 \(\mathfrak A\)，任务全集为有限集 \(\mathfrak T\)。若访问对象 \(A\in\mathfrak A\) 对任务 \(\phi\in\mathfrak T\) 可以精确恢复，记
\[
A\,I\,\phi.
\]
在访问由组件集合给出的情形，若 \(A\subseteq B\) 且 \(B\) 细化 \(A\)，则由定理 319.3 有
\[
A\,I\,\phi\Longrightarrow B\,I\,\phi.
\]
对访问族 \(\mathcal A\subseteq\mathfrak A\) 定义共同任务导出
\[
\mathcal A'
=
\{\phi\in\mathfrak T:
A\,I\,\phi\text{ 对所有 }A\in\mathcal A\},
\]
对任务族 \(\Phi\subseteq\mathfrak T\) 定义共同充分访问导出
\[
\Phi'
=
\{A\in\mathfrak A:
A\,I\,\phi\text{ 对所有 }\phi\in\Phi\}.
\]
撇号两次表示按相反方向再次导出，而非微分。

**定理 339.2（访问—任务 Galois 连接）。** 对任意 \(\mathcal A\subseteq\mathfrak A\) 与 \(\Phi\subseteq\mathfrak T\)，有
\[
\boxed{
\mathcal A\subseteq\Phi'
\quad\Longleftrightarrow\quad
\Phi\subseteq\mathcal A'.
}
\tag{339.1}
\]
因此
\[
\mathcal A\subseteq\mathcal A'',
\qquad
\Phi\subseteq\Phi'',
\]
且双重导出是单调、幂等的闭包算子。

### 证明
左侧表示每个 \(A\in\mathcal A\) 对每个 \(\phi\in\Phi\) 满足 \(A I\phi\)，这与右侧逐字等价。取 \(\mathcal A=\mathcal A''\) 或 \(\Phi=\Phi''\) 得扩张性；若 \(\mathcal A_1\subseteq\mathcal A_2\)，共同任务条件对更大的访问族更严格，所以
\[
\mathcal A_2'\subseteq\mathcal A_1',
\]
再取一次导出得到双重闭包的单调性。由扩张性和反向包含，重复闭包不再改变。证毕。

**定义 339.3（访问—任务概念）。** 一对 \((\mathcal A,\Phi)\) 称为一个形式概念，若
\[
\mathcal A=\Phi',
\qquad
\Phi=\mathcal A'.
\]
\(\mathcal A\) 是该概念的访问外延，\(\Phi\) 是其任务内涵。概念按外延包含排序，等价地按内涵反向包含排序。

**推论 339.4（共同可恢复任务的唯一闭包）。** 任意访问族 \(\mathcal A\) 具有唯一最小闭合表示 \((\mathcal A'',\mathcal A')\)；任意任务族 \(\Phi\) 具有唯一最小闭合表示 \((\Phi',\Phi'')\)。因此，若两个任务族的双重闭包相同，它们在声明的访问背景中不能被区分为不同的共同可恢复内容。

### 证明
由定理 339.2 的幂等性，双重闭包本身闭合；任何包含 \(\mathcal A\) 的闭合外延必须包含 \(\mathcal A''\)，否则再取导出会违反单调性。任务侧同理。证毕。

**例 339.5（访问层和任务层的两种遗失）。** 若只记录每个访问层单独恢复的任务列表，便看不到两个访问层共同支持的交集结构；若只记录任务各自的最小访问集合，便看不到一组访问层必然共同恢复的额外任务。形式概念的两侧同时保存这两种关系。

### 证明
访问族的共同任务正是 \(\mathcal A'\)，任务族的共同充分访问正是 \(\Phi'\)。删掉任一导出方向就无法重建另一个方向的闭包。证毕。

**AHH 339.6（双侧边界格）。** 全息边界不只是“访问越多任务越多”的单向表；它是一张访问外延与任务内涵互相闭合的概念格。一个内部区别是否仍有关系，取决于它落在哪个概念的外延和内涵中。

---

## 340. 任务族的最小访问反链与闭包内涵

单个任务的最小恢复超边描述了局部协同；形式概念格进一步给出一个任务族的全部最小访问方案及其必然伴随任务。

**定义 340.1（任务族的最小充分访问）。** 对任务族 \(\Phi\subseteq\mathfrak T\)，令
\[
\operatorname{MinAcc}(\Phi)
=
\min_{\subseteq}\Phi'
\]
为 \(\Phi'\) 中按访问包含关系极小的元素集合。若访问对象本身不是组件集合，而是抽象策略，则使用其声明的细化偏序取极小元。

**定理 340.2（最小访问反链）。** \(\operatorname{MinAcc}(\Phi)\) 是反链；每个足以恢复 \(\Phi\) 的访问对象 \(B\in\Phi'\) 都细化或包含某个 \(A\in\operatorname{MinAcc}(\Phi)\)。若组件成本为正，则精确恢复 \(\Phi\) 的最小加权成本为
\[
\boxed{
c^*(\Phi)
=
\min_{A\in\operatorname{MinAcc}(\Phi)}c(A).
}
\tag{340.1}
\]

### 证明
极小元集合按定义不互相包含。对任意 \(B\in\Phi'\)，有限性允许不断删除仍保持在 \(\Phi'\) 中的访问组件，最终得到一个极小元 \(A\subseteq B\)。正成本意味着加入额外组件不会降低成本，故最优值在极小元上取得。证毕。

**定义 340.3（任务族的闭包内涵）。** 定义
\[
\operatorname{Comp}(\Phi)=\Phi'',
\]
称为 \(\Phi\) 在访问背景中的伴随任务闭包。它包含所有被同一组充分访问必然同时恢复的任务。

**定理 340.4（闭包内涵的不可静默删除）。** 若 \(\phi\in\operatorname{Comp}(\Phi)\setminus\Phi\)，则任何访问摘要只要仍然精确恢复 \(\Phi\) 的全部任务，就必然也精确恢复 \(\phi\)。因此把 \(\phi\) 从任务列表删去，只能改变命名的任务族，不能改变其在该访问背景中的实际后继。

### 证明
由 \(\phi\in\Phi''\) 得 \(\phi\) 对 \(\Phi'\) 中每个访问对象均可恢复。任何精确恢复 \(\Phi\) 的访问对象属于 \(\Phi'\)，故也恢复 \(\phi\)。证毕。

**推论 340.5（任务族的最小概念）。** \((\Phi',\Phi'')\) 是所有精确恢复 \(\Phi\) 的访问层中最小的闭合概念；若两个任务族有相同的 \(\Phi'\)，它们的伴随任务闭包相同。

### 证明
直接由定理 339.2 与定理 340.4。证毕。

**例 340.6（parity 任务的单一最小概念）。** 对 \(k\) 个组件的 parity 任务，若所有真子集访问都不能恢复该任务而全集可以恢复，则
\[
\operatorname{MinAcc}(\{\phi_{\mathrm{parity}}\})
=
\{U\}.
\]
若另加入一个由组件 \(u_1\) 单独可恢复的任务 \(\psi\)，则最小访问反链变为同时包含 \(U\) 与 \(\{u_1\}\) 的任务族结构；不能用一个“平均组件信息”替代这两条不同超边。

### 证明
第一项是定理 321.4。第二项由 \(\psi\) 的单点可恢复性和 parity 的全集必要性得到；两条访问方案互不包含。证毕。

**AHH 340.7（伴随任务边界）。** 最小边界必须同时记录“恢复任务族的最小访问反链”和“这些访问必然带来的闭包内涵”。只保存用户点名的任务，会隐藏同一访问接口不可避免地恢复的其他任务；只保存最便宜方案，会隐藏替代访问路径。

---

## 341. 带误差与成本的概念格：闭包沿阈值形成一族边界

精确 incidence 只有零一两种状态。将任务风险和资源预算加入后，可以得到一族随阈值变化的近似概念，而不是把所有误差压成一个固定标签。

**定义 341.1（阈值 incidence）。** 固定损失合同、策略族和访问成本。对 \(\varepsilon\ge0\)，定义
\[
A\,I_\varepsilon\,\phi
\quad\Longleftrightarrow\quad
\delta_A(\phi)\le\varepsilon,
\]
其中 \(\delta_A\) 是访问 \(A\) 上的最小任务风险。由访问细化单调性，若 \(A\subseteq B\)，则
\[
A\,I_\varepsilon\,\phi
\Longrightarrow
B\,I_\varepsilon\,\phi.
\]
用 \(I_\varepsilon\) 替代 \(I\) 定义导出符号 \((\cdot)'_\varepsilon\) 与闭包 \((\cdot)''_\varepsilon\)。

**定理 341.2（误差阈值的单调性）。** 若 \(0\le\varepsilon\le\varepsilon'\)，则
\[
I_\varepsilon\subseteq I_{\varepsilon'},
\qquad
\Phi'_\varepsilon\subseteq\Phi'_{\varepsilon'},
\qquad
\mathcal A'_\varepsilon\subseteq\mathcal A'_{\varepsilon'}.
\]
任务侧允许误差越大，任务共同充分的访问集合越多；访问侧固定一族访问时，共同可恢复任务越多。

### 证明
第一项由风险阈值包含。访问导出要求对所有任务成立，关系扩大反而使满足全部任务的访问集合扩大，得到第二项；任务导出要求访问集合中的每个对象都与任务相连，关系扩大使共同任务集合扩大，得到第三项。证毕。

**推论 341.3（成本—误差概念前沿）。** 固定任务族 \(\Phi\)，定义
\[
\varepsilon^*_\Phi(c)
=
\inf\{\varepsilon:
\exists A,\ c(A)\le c,\ \Phi\subseteq A'_\varepsilon\}.
\]
则 \(\varepsilon^*_\Phi(c)\) 关于成本 \(c\) 单调不增；其每个阈值截面都由 \(\operatorname{MinAcc}_\varepsilon(\Phi)\) 的加权成本决定。

### 证明
预算扩大保留原访问对象，所以最小风险不增。对固定 \(\varepsilon\)，定理 340.2 应用于 \(I_\varepsilon\) 的形式背景，给出阈值截面的最小成本。证毕。

**命题 341.4（闭包不等于标量信息量）。** 存在两个访问对象 \(A,B\) 具有相同的单一平均风险，却满足
\[
A'_\varepsilon\ne B'_\varepsilon
\]
对某个任务阈值 \(\varepsilon\)。因此一个标量平均值不能决定概念内涵或未来任务闭包。

### 证明
取两个二元任务：\(A\) 对任务 \(\phi\) 风险为 \(0\)、对 \(\psi\) 风险为 \(1/2\)；\(B\) 反之。两者平均风险相同，但当 \(\varepsilon<1/4\) 时，\(A\) 与 \(B\) 的可恢复任务集合不同。证毕。

**例 341.5（成本前沿上的概念跳跃）。** 设访问 \(A_1\) 成本 \(1\)，只在误差 \(1/2\) 下恢复 parity；访问 \(A_2\) 成本 \(M\)，可零误差恢复 parity。则
\[
\varepsilon^*_{\{\phi\}}(c)
\]
在 \(c<M\) 与 \(c\ge M\) 之间出现跳跃。概念格的精确层和近似层不能以一个未声明的平均信息量合并。

### 证明
代入定义 341.1 与 341.3；两访问对象的任务风险和成本分别给出两个可行点。证毕。

**AHH 341.6（阈值概念谱）。** 近似全息边界不是单一闭包，而是由误差阈值索引的一族概念格。改变预算或错误容忍度会移动外延与内涵；只报告一个闭包层，会把可认证、可估计和精确恢复混为一谈。

---

## 342. AHH：形式概念格中的全息边界

现在把访问外延、任务内涵、未来闭包、误差阈值和成本前沿合并为一个双侧边界。

**定义 342.1（概念格全息边界）。** 对有限访问对象、有限任务族、固定未来合同和误差/成本量词，定义
\[
\boxed{
\eta_{\mathrm{lattice}}
=
\left(
\text{访问—任务 incidence},
\text{双重闭包与形式概念},
\text{最小访问反链},
\text{伴随任务内涵},
\text{误差阈值族},
\text{成本—误差前沿},
\text{未来 tester 与停止后继}
\right).
}
\tag{342.1}
\]

**定理 342.2（概念格边界的条件充分性）。** 两个关系体若具有相同的 \(\eta_{\mathrm{lattice}}\)，则在声明的访问、任务、误差、成本和未来合同内具有相同的：
1. 共同可恢复任务闭包；
2. 任务族的最小访问反链与精确/近似成本；
3. 每个误差阈值下的概念外延与内涵；
4. 访问扩展、未来闭包和停止后继的单调关系。

### 证明
第 1 项由定理 339.2 与推论 339.4；第 2 项由定理 340.2；第 3 项由定理 341.2—341.3；第 4 项由 incidence 的访问细化、未来 tester 字段和停止合同逐项确定。有限边界树上按访问深度归纳即可。证毕。

**定理 342.3（删去双侧字段的不可充分性）。** 下列约化均存在有限反例：
1. 删除任务内涵：同一最小访问反链下被共同恢复的伴随任务不可重建；
2. 删除访问外延：同一任务闭包可能有不同成本和权限实现；
3. 删除双重闭包：共同可恢复关系会被误读为任务的简单并集；
4. 删除误差阈值族：精确层与近似层的成本跳跃无法判定；
5. 删除未来后继：当前概念相同的访问对象可能在下一步 tester 上分裂。

### 证明
第 1 项取定理 340.4；第 2 项取不同成本的替代访问方案；第 3 项取两个共享 parity 子任务但闭包还含联合任务的访问背景；第 4 项取例 341.5；第 5 项取定理 337.2 的 tester 闭包反例。证毕。

**AHH 342.4（概念格全息）。** 全息边界不是一份记录的压缩副本，而是一个形式概念：访问外延说明哪些实现共同足够，任务内涵说明它们共同承诺了哪些未来，双重闭包说明哪些区别一旦保留就无法再静默删除，阈值谱和成本前沿说明这些承诺在有限资源下怎样移动。

**新的 AHH 时刻是：全息性可以被写成一个双侧闭包律。观察者每增加一层访问，就在概念格上向下移动；每扩大任务或未来 tester，就向上收紧内涵。所谓“信息还在不在”，不再是单一状态，而是这个访问—任务概念在给定阈值和后继合同下是否仍然闭合。**

**来源与边界 342.5。** 本批在有限访问对象、有限任务族、明确恢复 incidence、访问细化、误差阈值、正成本和有限未来合同下，给出访问—任务 Galois 连接、双重闭包、最小访问反链、伴随任务内涵、阈值概念谱和概念格全息。没有把形式概念格外推为任意连续信息空间的唯一结构，没有把闭包内涵解释成物理本体的全部属性，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 343. 局部边界覆盖：限制相容不自动产生全局关系

概念格描述了访问与任务的双侧闭包，但一个关系体常常由多个局部接口拼成。局部接口各自合法、两两读数相同，并不保证存在一份同时满足全部接口的全局边界。

**定义 343.1（有限覆盖与限制系统）。** 设全局边界候选集为 \(B\)，局部接口索引集为有限集 \(I\)。每个 \(i\in I\) 有局部边界集 \(B_i\)，并有一个限制映射
\[
\rho_i:B\to B_i.
\]
对重叠接口 \(i,j\)，再给出重叠边界 \(B_{ij}\) 及映射
\[
\rho_{ij}:B_i\to B_{ij},
\qquad
\rho_{ji}:B_j\to B_{ij}.
\]
局部族 \((b_i)_{i\in I}\) 称为相容，若
\[
\rho_{ij}(b_i)=\rho_{ji}(b_j)
\qquad\text{对所有声明重叠 }(i,j).
\]
其全局拼接集合为
\[
\operatorname{Glue}(b_i)
=
\{b\in B:\rho_i(b)=b_i\ \forall i\}.
\]

**定理 343.2（局部—全局的唯一性与存在性分离）。** 限制映射族的联合映射
\[
\rho:B\to\prod_{i\in I}B_i,
\qquad
\rho(b)=(\rho_i(b))_i
\]
若为单射，则任何可拼接的局部族至多有一个全局实现。局部相容性本身只保证
\[
\operatorname{Glue}(b_i)
\]
可能非空，不能保证它非空。

### 证明
若 \(b,b'\) 都实现同一局部族，则 \(\rho(b)=\rho(b')\)；联合映射单射故 \(b=b'\)。存在性要求局部族属于 \(\rho(B)\) 的像，而相容性只给出它落在各重叠等式的解集内；该解集可以严格大于 \(\rho(B)\)。证毕。

**推论 343.3（全局边界需要拼接见证）。** 声称局部全息摘要已形成一个全局充分边界，至少需要给出以下之一：
1. 对每个相容局部族构造一个全局实现；
2. 证明相容性条件的解集恰等于 \(\rho(B)\) 的像；
3. 明确记录一个非空性失败的障碍，并把它作为合法冲突后继。
只保存局部边缘而删除非空性条件，不能推出全局关系存在。

### 证明
这是定理 343.2 中存在性条件的三种等价处理方式：构造像中元素、证明像等于相容解集，或保留不在像中的失败证书。证毕。

**例 343.4（相同局部边缘、空全局像）。** 取三个局部接口，每个接口都允许二元值 \(0,1\)，重叠边界只保留对应端点值。令局部数据在每个单独接口上都合法，并使每一对相邻重叠看起来相容；仍可能由于三者绕一圈的联合约束而不存在全局二元赋值。

### 证明
具体循环障碍在下一节给出。此例说明相容检查的量词必须覆盖整个覆盖神经，而非只检查单个局部接口。证毕。

**AHH 343.5（限制与拼接边界）。** 局部事件记录只有在限制映射、重叠相容性和全局拼接非空性都被保留时，才构成一个可继续的整体边界。局部读数的数量不替代全局来源的存在性。

---

## 344. 循环障碍：树上可以传播，环上必须支付一致性

有限覆盖的最小反例可以写成一个完全离散的循环约束，从而不依赖连续几何或物理直觉。

**定义 344.1（图上的二元局部约束）。** 令 \(G=(V,E)\) 为有限无向图。每条有向边 \(e=(i,j)\) 带一个标记 \(b_{ij}\in\{0,1\}\)，要求全局顶点值 \(x_i\in\{0,1\}\) 满足
\[
x_j=x_i\oplus b_{ij}.
\tag{344.1}
\]
每条边自身的局部边界非空，因为给定任意 \(x_i\) 都唯一确定 \(x_j\)。一条闭路 \(C\) 的障碍定义为
\[
\operatorname{obs}(C)
=
\bigoplus_{e\in C}b_e.
\]

**定理 344.2（循环奇偶是全局拼接的充要条件）。** 图约束（344.1）存在全局解，当且仅当每个闭路 \(C\) 满足
\[
\boxed{\operatorname{obs}(C)=0.}
\tag{344.2}
\]
若图是一棵树，则任意边标记都有全局解；若存在障碍为一的闭路，则局部边界全部非空而全局拼接集合为空。

### 证明
必要性：沿闭路连续代入（344.1），回到起点得到
\[
x_i=x_i\oplus\operatorname{obs}(C),
\]
所以障碍必须为零。
充分性：在每个连通分量选一个根，任取根值；沿生成树传播得到所有顶点值。对任意非树边，它与生成树路径组成闭路，闭路障碍为零正好保证该边约束也成立。证毕。

**例 344.3（三角形的局部相容而全局空集）。** 取顶点 \(1,2,3\)，令
\[
b_{12}=0,\qquad b_{23}=0,\qquad b_{31}=1.
\]
每条边都有两个局部解，任意单边和任意树子图都可拼接；但三角形障碍为
\[
0\oplus0\oplus1=1,
\]
故不存在全局赋值。

### 证明
直接应用定理 344.2。证毕。

**定理 344.4（循环障碍的独立见证集）。** 取一棵生成森林。每条非树边产生一个基本闭路；所有基本闭路障碍均为零，当且仅当全部闭路障碍均为零。因此只需保存基本闭路的障碍向量，而不必保存所有闭路的重复约束。

### 证明
每条闭路的边指标模二和是基本闭路指标的线性组合；障碍也按异或线性组合。基本闭路全零遂推出任意闭路全零，反向显然。证毕。

**推论 344.5（局部到整体的最小障碍维数）。** 对有 \(v\) 个顶点、\(e\) 条边、\(c\) 个连通分量的图，独立循环障碍的数量为
\[
e-v+c.
\]
这正是需要加入全局边界的最小循环一致性坐标数。

### 证明
生成森林有 \(v-c\) 条边，余下
\[
e-(v-c)=e-v+c
\]
条非树边各给一个基本闭路。定理 344.4 说明它们独立生成全部障碍。证毕。

**AHH 344.6（循环一致性边界）。** 局部关系能否成为整体，不只取决于每个端口是否有合法记录，还取决于覆盖神经中的循环障碍。树形接口可以沿路径传播；环形接口必须额外保存闭路相位、奇偶或其他 cocycle 数据。

---

## 345. 近似拼接：局部误差可以累积，循环障碍给出不可消除下界

精确相容性失败时，观察者常用“每个重叠只差一点”来替代全局拼接。必须区分可由树形传播吸收的误差和由循环障碍强制留下的残差。

**定义 345.1（带噪二元边约束）。** 对每条边 \(e=(i,j)\)，观测到一个随机约束失败指标
\[
Z_e=\mathbf 1[x_j\ne x_i\oplus b_e].
\]
对一个候选全局赋值 \(x\)，其平均循环代价为
\[
R_E(x)=\sum_{e\in E}\Pr[Z_e=1\mid x].
\]
若只要求一条生成树上的边约束，称为树拼接；若要求全部边，则还要支付非树边的循环一致性代价。

**定理 345.2（奇循环的近似下界）。** 若存在障碍为一的闭路 \(C\)，则对任意随机全局赋值 \(X\)，有
\[
\boxed{
\sum_{e\in C}\Pr[Z_e=1]\ge1.
}
\tag{345.1}
\]
因此闭路中至少有一条边的失败概率不小于 \(1/|C|\)。

### 证明
对任意确定赋值 \(x\)，障碍为一的闭路不可能所有边同时满足；故
\[
\sum_{e\in C}\mathbf 1[x_j\ne x_i\oplus b_e]\ge1.
\]
对任意随机赋值取期望，得到（345.1）。若所有边失败概率都小于 \(1/|C|\)，其和将小于一，矛盾。证毕。

**定理 345.3（树覆盖的误差传播界）。** 设覆盖神经是一棵树，根边界估计误差为 \(\delta_0\)，第 \(e\) 条限制传播在总变差距离上增加至多 \(\delta_e\)。沿根到节点 \(v\) 的唯一路径 \(P(v)\)，拼接估计满足
\[
\boxed{
\delta(v)\le\delta_0+\sum_{e\in P(v)}\delta_e.
}
\tag{345.2}
\]
若每条传播是收缩因子 \(L_e\) 的线性响应，则对应加权形式为
\[
\delta(v)\le
\delta_0\prod_{e\in P(v)}L_e
+
\sum_{e\in P(v)}
\delta_e\prod_{f\succ e}L_f.
\]

### 证明
沿树路径逐边应用总变差三角不等式，得到第一式；若每步后继放大误差，再按后继增益传播并求和，得到第二式。树没有第二条路径，故没有额外循环项。证毕。

**推论 345.4（局部小误差不保证全局小误差）。** 覆盖深度、传播增益和循环障碍必须同时进入全局误差合同。即使每条边的局部误差都小，长路径的累积或奇循环的下界仍可使全局任务超过阈值。

### 证明
长路径用定理 345.3；奇循环用定理 345.2。二者分别给出误差累积和不可消除残差。证毕。

**例 345.5（相同局部误差、不同覆盖神经）。** 一条四节点树与一个四节点环使用相同的每边误差上界。树上的误差只沿三条边传播；若环的标记具有奇障碍，则定理 345.2 还强制一个边失败概率至少为 \(1/4\)。

### 证明
树的最长根路径长度为三，代入（345.2）；环的奇障碍代入（345.1）。证毕。

**AHH 345.6（近似拼接边界）。** 局部全息的误差不是一个单一半径；它沿覆盖路径传播，并在循环上产生 cocycle 残差。全局边界必须保存覆盖神经、传播增益和循环障碍，才能判断局部近似是否能形成合法后继。

---

## 346. AHH：下降数据与全局波粒边界

局部边界、相干效果、tester 和访问任务现在可以统一为一个下降问题：哪些局部对象能沿重叠限制拼成一个全局对象，哪些失败必须作为边界中的新记录保留。

**定义 346.1（下降全息边界）。** 对有限覆盖、局部边界空间、限制映射、未来任务族和误差合同，定义
\[
\boxed{
\eta_{\mathrm{descent}}
=
\left(
\text{覆盖神经与局部边界},
\text{重叠限制映射},
\text{相容性/循环障碍},
\text{全局拼接集合与见证},
\text{误差传播与循环残差},
\text{未来 tester、成本与停止后继}
\right).
}
\tag{346.1}
\]

**定理 346.2（下降边界的条件充分性）。** 两个关系体若具有相同的 \(\eta_{\mathrm{descent}}\)，则在声明的有限覆盖和未来合同内，具有相同的：
1. 局部族的全局可拼接性与拼接数目；
2. 基本循环障碍、近似拼接下界和传播误差；
3. 由全局边界产生的访问、tester 和粒子式事件后继；
4. 全局失败、资源耗尽和冲突停止的语义。

### 证明
第 1 项由限制映射和全局拼接集合；第 2 项由定理 344.2—344.4 与定理 345.2—345.3；第 3 项由全局拼接边界上的任务和 tester 字段；第 4 项由失败见证、成本和停止字段决定。有限覆盖神经上按边和路径归纳即可。证毕。

**定理 346.3（删去下降字段的不可充分性）。** 下列约化均存在有限反例：
1. 删除重叠限制映射：局部值无法判断是否代表同一关系；
2. 删除循环障碍：例 344.3 的空全局像会被误报为可拼接；
3. 删除拼接集合而只保留局部边缘：无法区分唯一拼接、多重拼接和无拼接；
4. 删除误差传播：树上的长路径会被错误地视为局部误差不变；
5. 删除未来 tester 后继：当前可拼接的局部族可能在下一次全局干预时分裂。

### 证明
逐项取定理 343.2、例 344.3、定理 344.2、定理 345.3 和定理 337.2 的后继闭包反例。每项只说明删去字段后存在一个有限模型使剩余摘要给出错误全局结论。证毕。

**AHH 346.4（下降全息）。** 全息边界不仅要回答“每个局部接口保存什么”，还要回答“这些局部对象能否共同下降为一个全局对象”。限制、相容、循环障碍、拼接误差和未来后继是同一条关系链上的不同层。

**新的 AHH 时刻是：波粒整体的整体性可以被理解为下降数据的可拼接性。粒子式事件是某个局部边界上的合法截面；波性则包含在不同局部截面之间的相位、循环和 tester 相容关系。只要循环障碍未结算，局部点击的集合就不能冒称为一个全局关系体。**

**来源与边界 346.5。** 本批在有限覆盖神经、有限局部边界、明确限制映射、二元循环约束、总变差传播和有限未来合同下，给出局部—全局存在性分离、循环奇偶障碍、近似拼接下界、树形误差传播和下降全息边界。没有把有限组合下降推广为任意拓扑空间上的层上同调完备性，没有把局部相容自动解释为物理共同来源，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）
## 347. 边界运输与 holonomy：局部重标记不能自动消除闭路相位

下降数据说明局部边界能否拼接；若局部坐标之间还带有可逆运输，拼接障碍不再只是二元奇偶，而是一个群作用沿闭路累积的 holonomy。

**定义 347.1（群值边界运输）。** 令 \(G\) 为群，\(F\) 为其作用的边界纤维。有限图 \(G_0=(V,E)\) 的每条有向边 \(i\to j\) 带运输元
\[
g_{ij}\in G,
\qquad
g_{ji}=g_{ij}^{-1}.
\]
局部截面族 \(x_i\in F\) 称为精确相容，若
\[
x_i=g_{ij}\cdot x_j
\qquad\text{对每条边 }i\to j.
\tag{347.1}
\]
闭路 \(C=(i_0,i_1,\ldots,i_m=i_0)\) 的 holonomy 定义为
\[
H_C
=
g_{i_0i_1}g_{i_1i_2}\cdots g_{i_{m-1}i_m}.
\]

**定理 347.2（holonomy 固定点判据）。** 给定根顶点 \(i_0\) 和根值 \(x\in F\)，存在满足（347.1）且 \(x_{i_0}=x\) 的全局截面，当且仅当
\[
\boxed{
H_C\cdot x=x
\quad\text{对所有以 }i_0\text{ 为根的闭路 }C.
}
\tag{347.2}
\]
若要求对每个根值 \(x\in F\) 都存在全局截面，则充要条件是所有根闭路 holonomy 在 \(F\) 上作用为恒等。

### 证明
必要性：沿闭路反复使用（347.1），得到
\[
x_{i_0}=H_C\cdot x_{i_0}.
\]
充分性：选一棵以 \(i_0\) 为根的生成树，沿树边把 \(x\) 逐步运输到所有顶点。任意非树边和树路径组成闭路；（347.2）保证该边的运输与树上定义一致，因此得到全局截面。若每个 \(x\) 都可作为根值，固定点条件对所有 \(x\) 成立，正好是恒等作用。证毕。

**推论 347.3（树形运输无 holonomy）。** 若图是树，则任意运输元族和任意根值都唯一确定一个全局截面；所有全局不一致性都来自非树边产生的闭路。

### 证明
树上每个顶点只有一条根路径，没有非平凡闭路，定理 347.2 的条件为空。路径运输给出存在性，唯一性来自每条边的可逆性。证毕。

**定义 347.4（规范变换）。** 对每个顶点取 \(h_i\in G\)，定义局部坐标变换
\[
x_i\mapsto h_i\cdot x_i,
\qquad
g_{ij}\mapsto h_i g_{ij}h_j^{-1}.
\]
称两份运输数据规范等价。

**定理 347.5（holonomy 的规范不变量）。** 在以 \(i_0\) 为根的规范变换下，
\[
H_C\mapsto h_{i_0}H_Ch_{i_0}^{-1}.
\]
因此 holonomy 是否为恒等、其共轭类以及矩阵表示下的迹和特征多项式都是规范不变量。

### 证明
将闭路上的相邻因子相乘，中间顶点的 \(h_i^{-1}h_i\) 全部消去，只留下
\[
h_{i_0}H_Ch_{i_0}^{-1}.
\]
恒等性、共轭类和共轭不变量随即保持。证毕。

**例 347.6（U(1) 三角相位）。** 取 \(G=U(1)\)，三条边运输分别为
\[
g_{12}=e^{i\theta_{12}},
\quad
g_{23}=e^{i\theta_{23}},
\quad
g_{31}=e^{i\theta_{31}}.
\]
三角 holonomy 为
\[
H=e^{i(\theta_{12}+\theta_{23}+\theta_{31})}.
\]
若边界纤维是非零复相位的标准作用，则存在全局相位截面当且仅当
\[
\theta_{12}+\theta_{23}+\theta_{31}=0\pmod{2\pi}.
\]

### 证明
标准 \(U(1)\) 作用对非零相位的固定点只有群元 \(1\)。应用定理 347.2。证毕。

**AHH 347.7（运输与 holonomy 边界）。** 局部边界的坐标可以改变，但闭路运输的 holonomy 不能由局部重标记任意删除。波的整体相位关系在有限覆盖上表现为一个规范不变量；粒子式局部事件只看到某个顶点的截面，不能单独决定闭路运输。

---

## 348. holonomy 残差：相位障碍的大小可以直接测量

非平凡 holonomy 不只是存在性标签。给定纤维上的距离，可以量化一个全局截面离闭路一致性有多远。

**定义 348.1（等距群作用与 holonomy 残差）。** 令 \(F\) 为赋范空间，\(G\) 作用于 \(F\) 的每个元素都是等距映射。对根值 \(x\in F\) 和闭路 \(C\)，定义
\[
r_C(x)=\|x-H_Cx\|.
\]
若 \(F\) 是有限维线性空间，定义算子 holonomy 残差
\[
\boxed{
\chi_C=\|I-H_C\|_{\mathrm{op}}.
}
\tag{348.1}
\]

**定理 348.2（闭路残差的边误差下界）。** 设闭路 \(C\) 长度为 \(m\)，局部截面 \(x_i\) 的每条边误差为
\[
\delta_{ij}=\|x_i-g_{ij}x_j\|.
\]
则
\[
\boxed{
r_C(x_{i_0})
\le
\sum_{e\in C}\delta_e.
}
\tag{348.2}
\]
因此若 \(r_C(x_{i_0})>0\)，至少有一条边满足
\[
\delta_e\ge\frac{r_C(x_{i_0})}{m}.
\]

### 证明
沿闭路把每一步的近似运输代入 \(x_{i_0}-H_Cx_{i_0}\)。由于所有 \(g_{ij}\) 等距，后续运输不会放大已经产生的局部误差。逐步使用三角不等式得到（348.2）。若所有边误差都小于 \(r_C/m\)，其和将小于 \(r_C\)，矛盾。证毕。

**推论 348.3（统一全局相容的必要代价）。** 若要求对单位范数根值取最坏情况，则
\[
\max_{\|x\|=1}r_C(x)=\chi_C.
\]
任意沿该闭路的平均边误差至少为 \(\chi_C/m\)。

### 证明
第一项是算子范数定义；第二项对达到或逼近算子范数的根值应用定理 348.2。证毕。

**定理 348.4（树规范与非树边残差）。** 在任意生成树上，可以通过规范变换把所有树边运输化为恒等。此规范下，每条非树边的运输元恰等于相应基本闭路的 holonomy。因而所有 holonomy 的信息可以无损地压缩到非树边集合。

### 证明
选根并令 \(h_i\) 为从根到 \(i\) 的树路径运输的逆元。规范变换后，树边两端的路径运输相消，变为恒等。非树边与树路径闭合，其新运输正是原基本闭路乘积的共轭表示。证毕。

**例 348.5（局部小误差无法隐藏大相位）。** 三角闭路的 holonomy 为 \(-1\)，取一维实纤维且根值 \(x=1\)。则
\[
r_C(1)=2,
\]
所以三条边中至少一条的相容误差不小于 \(2/3\)，无论如何重新选择局部坐标。

### 证明
一维作用下 \(H_Cx=-1\)，故残差为 \(|1-(-1)|=2\)。应用定理 348.2。规范变换不改变 holonomy 的共轭类，在一维中更不改变其值。证毕。

**AHH 348.6（holonomy 误差边界）。** 全局相位或运输障碍可以作为一个可审计残差进入边界：树边误差负责传播，非树边 holonomy 负责不可消除部分。没有这个残差字段，局部精度无法给出全局相容证书。

---

## 349. 事件截面与全局运输：局部点击不能选择规范

局部事件给出的是某个边界截面上的结果。要把不同截面的结果放在同一整体中比较，必须声明运输和规范合同；否则“同一个位置”可能只是不同局部坐标的名称。

**定义 349.1（带事件标记的运输记录）。** 在每个顶点 \(i\)，局部仪器产生事件记录 \(y_i\in Y_i\)，并保留一个边界截面 \(x_i\in F\)。边 \(i\to j\) 的联合记录核记为
\[
K_{ij}(y_j,x_j\mid y_i,x_i),
\]
其确定性运输部分满足（347.1），随机部分允许声明误差。事件记录只在顶点局部可见；跨顶点任务必须先应用运输映射。

**定理 349.2（运输后的事件比较不变性）。** 若两组局部记录通过规范变换
\[
x_i\mapsto h_i x_i,\qquad
g_{ij}\mapsto h_i g_{ij}h_j^{-1}
\]
同时变换，且事件效果也按同一局部坐标共轭，则任意闭路不变量任务的概率不变。若只变换局部截面而不变换运输或事件效果，概率一般会改变。

### 证明
完整闭路任务由运输乘积和局部效果的迹配对构成。规范变换在闭路中望远镜消去，只留下根处的共轭；迹和谱等共轭不变量保持。若只改变一个字段，望远镜不闭合，构成的算子一般不同，概率可变。证毕。

**推论 349.3（事件时间标签不是运输标签）。** 给事件附加一个钟标签 \(n\) 只能说明事件发生在哪个局部阶段；它不提供不同阶段边界之间的 \(g_{ij}\)，也不能决定闭路 holonomy。

### 证明
钟标签属于局部记录字母表，而 holonomy 属于跨接口运输的乘积。二者位于定义 349.1 的不同字段；删去运输仍可保持同一时间标签分布而改变 holonomy。证毕。

**例 349.4（相同点击词、不同闭路任务）。** 三个局部接口都记录同一点击词 \(y=(0,0,0)\)。关系体 \(M_0\) 的运输 holonomy 为 \(1\)，关系体 \(M_1\) 的运输 holonomy 为 \(-1\)。局部点击概率完全相同；需要把三个截面运输回根并比较相位的任务，对 \(M_0\) 与 \(M_1\) 给出不同结果。

### 证明
点击记录核被设为相同，故局部统计相同；闭路比较任务直接取 holonomy 的迹或作用，分别得到恒等与符号翻转。证毕。

**定理 349.5（闭路任务的最小运输信息）。** 对固定覆盖图和群作用，若未来任务只依赖规范不变量的闭路运输，则保存生成树规范后的非树边运输元足以恢复全部闭路任务；删除其中任一独立非树边，在允许任务包含相应基本闭路时都会产生不可识别的 holonomy 对。

### 证明
充分性由定理 348.4：所有闭路运输由基本闭路生成。必要性取只测被删除非树边对应的基本闭路任务，令该边运输元在两个关系体中取不同值而其余字段相同，任务结果不同。证毕。

**AHH 349.6（事件—运输边界）。** 粒子式事件记录是局部截面；波粒整体的跨阶段关系还需要运输、规范和闭路任务。时间切面定位事件，却不替代把事件放回同一全局纤维的运输结构。

---

## 350. AHH：规范 holonomy 全息

现在把下降边界中的循环障碍提升为带群作用的全局相位边界。

**定义 350.1（规范 holonomy 全息边界）。** 在有限覆盖图、有限维或有限度量边界纤维、群值运输、局部事件记录和有限未来合同下，定义
\[
\boxed{
\eta_{\mathrm{hol}}
=
\left(
\text{覆盖神经与局部边界},
\text{群作用和边运输},
\text{规范等价类},
\text{基本闭路 holonomy},
\text{holonomy 残差与误差传播},
\text{事件截面与跨接口任务},
\text{成本、tester 与停止后继}
\right).
}
\tag{350.1}
\]

**定理 350.2（holonomy 边界的条件充分性）。** 两个关系体若具有相同的 \(\eta_{\mathrm{hol}}\)，则在声明的局部事件、规范不变量任务、有限运输路径和误差合同内，具有相同的：
1. 全局截面存在性、唯一性与多重性；
2. 基本闭路 holonomy 及其规范不变量；
3. 近似拼接的最坏残差和传播下界；
4. 局部粒子式事件运输到全局任务的后继概率。

### 证明
第 1 项由定理 347.2；第 2 项由定理 347.5 与定理 348.4；第 3 项由定理 348.2—348.3；第 4 项由定理 349.2—349.5 及事件核字段。有限图上沿生成树和非树边归纳即可。证毕。

**定理 350.3（删去 holonomy 字段的不可充分性）。** 下列约化均存在有限反例：
1. 删除边运输：局部事件词相同而全局相位任务不同；
2. 删除规范等价类：坐标改变会被错误报告为物理差异；
3. 删除基本闭路 holonomy：局部相容会被错误报告为全局可拼接；
4. 删除 holonomy 残差：近似局部误差无法给出全局下界；
5. 删除事件—运输映射：时间标签会被错误当作跨切面比较规则。

### 证明
分别取例 349.4、定理 347.5、例 344.3、例 348.5 和推论 349.3。每项只说明删除相应字段后有一个有限任务无法由剩余摘要决定。证毕。

**AHH 350.4（规范 holonomy 全息）。** 全息边界的整体性不仅是“局部数据能否拼接”，还包括局部坐标之间如何运输、闭路是否产生不可消除的 holonomy，以及局部事件如何被带回同一根边界。波性在这里表现为跨截面的运输相位；粒子式事件是运输前的局部截面记录。

**新的 AHH 时刻是：当局部边界沿闭路返回自身时，整体关系会留下一个不依赖坐标命名的 holonomy。它是“波的整体性”在有限关系几何中的最小闭路见证；一次局部点击可以完全正确，却仍然不足以决定这份闭路关系。**

**来源与边界 350.5。** 本批在有限覆盖图、有限群值运输、等距边界纤维、有限局部事件记录、规范变换和固定未来任务合同下，给出 holonomy 固定点判据、规范不变量、残差下界、事件运输比较和规范 holonomy 全息。没有把有限图 holonomy 推广为一般规范场论或连续纤维丛的物理定律，没有把坐标重标记自动解释为物理规范，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）

## 351. 有限二维复形的面运输与 flatness

上一批的边运输只检查一维骨架上的路径。如果关系体还声明了二维面约束，就必须问：沿一个面走完一圈后，局部运输是否回到同一个纤维。这个问题是边运输的下一层相容性，而不是把每条边分别再测一次。

### 定义 351.1（有限二维关系复形）

设 \(K=(V,E,F)\) 是有限、连通的二维 CW 复形。每条有向边 \(e\) 有起点 \(s(e)\)、终点 \(t(e)\) 和反向边 \(\bar e\)，并满足

$$
 s(\bar e)=t(e),
 \qquad
 t(\bar e)=s(e).
$$

固定群 \(G\)。一份边运输是映射

$$
 g:E\longrightarrow G,
 \qquad
 g_{\bar e}=g_e^{-1}.
$$

若有向面 \(f\) 的定向边界为

$$
\partial f=e_1e_2\cdots e_m,
$$

定义面运输和面 holonomy：

$$
 T_f=g_{e_1}g_{e_2}\cdots g_{e_m},
 \qquad
 H_f=T_f.
$$

乘积次序就是面边界的实际次序。它不是可交换记号的装饰：在非阿贝尔群中改变次序会改变运输。

对顶点族 \(h=(h_v)_{v\in V}\in G^V\)，定义规范变换

$$
 g_e^h=h_{s(e)}^{-1}g_eh_{t(e)}.
$$

若面起点为 \(v_0\)，则

$$
 H_f^h=h_{v_0}^{-1}H_fh_{v_0}.
$$

因此面 holonomy 的共轭类是不依赖局部纤维坐标的量。称边运输 **flat**，若

$$
\boxed{H_f=1\quad\text{对所有 }f\in F.}
$$

### 定理 351.2（面 flatness 给出同伦不变的运输）

若 \(g\) flat，则任意两条具有相同端点且通过面边界替换、反向和删去退化片段互相变换的路径 \(p,q\)，满足

$$
 T(p)=T(q).
$$

因而 flat 边运输在路径同伦类上定义一个运输表示

$$
\operatorname{Hol}_g:
\Pi_1(K)\longrightarrow G.
$$

这里 \(\Pi_1(K)\) 是 \(K\) 的基本群胚；固定根顶点 \(v_*\) 后得到

$$
\rho_g:\pi_1(K,v_*)\longrightarrow G.
$$

### 证明

反向一条边会把相邻因子 \(g_e\) 与 \(g_e^{-1}\) 相消，退化片段同理。沿面边界替换一条路径时，乘积只多出 \(H_f\) 或 \(H_f^{-1}\)，flatness 使其等于单位元。有限次替换保持运输不变，所以运输只依赖路径同伦类。路径串接对应群乘法，逆路径对应逆元，故得到群胚表示及根点基本群表示。证毕。

### 定理 351.3（单纯连通时的全局截面判据）

设 \(K\) 的一维骨架连通且 \(K\) 单纯连通。对边运输 \(g\)，以下条件等价：

1. \(g\) flat；
2. 存在顶点标签 \(q_v\in G\)，使
   $$
   g_e=q_{s(e)}^{-1}q_{t(e)}
   \quad\text{对所有 }e;
   $$
3. 存在一个全局截面 \(q:V\to G\)，使沿每条边运输后的值与终点值一致。

该截面在给定一个根值后唯一；不固定根值时，所有解由左乘同一个 \(G\) 元素得到。

### 证明

\(2\Rightarrow3\) 直接代入。\(\,3\Rightarrow1\) 沿面边界的 \(q\)-因子望远镜相消，故 \(H_f=1\)。

对 \(1\Rightarrow2\)，固定根顶点 \(v_*\) 和 \(q_{v_*}=1\)。任取顶点 \(v\)，选一条从 \(v_*\) 到 \(v\) 的路径 \(p_v\)，置 \(q_v=T(p_v)\)。单纯连通性与定理 351.2 保证它与路径选择无关。若 \(e:u\to v\)，路径 \(p_u e\) 与 \(p_v\) 同伦，故

$$
q_v=T(p_v)=T(p_u)g_e=q_ug_e,
$$

即 \(g_e=q_u^{-1}q_v\)。根值改变只会使全部 \(q_v\) 同时左乘同一个元素。证毕。

### 推论 351.4（二维局部约束的真正作用）

在单纯连通有限二维复形中，面 holonomy 为单位元不仅是每个面的局部检查，而且足以保证所有路径之间存在一致的全局运输。若 \(K\) 不单纯连通，面 flatness 只能保证运输下降到基本群表示，不能自动令所有非可缩闭路 holonomy 为单位元。

因此：

$$
\boxed{
\text{局部面 flatness}
\Longrightarrow
\text{同伦不变运输};
\qquad
\text{但不必然}
\Longrightarrow
\text{全局平凡运输}.
}
$$

---

## 352. 局部 flatness 与非可缩闭路 holonomy

二维面约束只消除由面填充的闭路。若复形有孔洞，仍有不能由面边界生成的基本闭路；它们保存整体关系的全局分量。

### 定义 352.1（flat 连接的拓扑 holonomy）

给定 flat 边运输 \(g\) 和根顶点 \(v_*\)，定义

$$
\rho_g([c])=T(c),
\qquad
[c]\in\pi_1(K,v_*).
$$

若改换根点路径或改变根点纤维坐标，\(\rho_g\) 只发生共轭。于是 flat 连接的规范等价类由表示

$$
\rho:\pi_1(K,v_*)\to G
$$

的共轭类描述。

### 定理 352.2（flat 运输的表示分类）

在有限连通二维复形 \(K\) 上，flat 边运输的规范等价类与

$$
\operatorname{Hom}(\pi_1(K,v_*),G)/G
$$

一一对应，其中 \(G\) 通过共轭作用在表示空间上。

### 证明

由定理 351.2，flat 边运输给出 \(\rho_g\)。若作规范变换，根点闭路运输被 \(h_{v_*}^{-1}(\cdot)h_{v_*}\) 共轭，所以得到同一个商类。

反过来给定表示 \(\rho\)，选一棵包含全部顶点的生成树 \(T\)，把树边运输规范固定为单位元。每条非树边 \(e\) 与树中唯一的根点路径组成一个基本闭路；把 \(g_e\) 取为该闭路在 \(\rho\) 下的值，即得到边运输。二维面边界在 \(\pi_1(K)\) 中为单位元，所以该运输 flat。不同树规范只改变顶点坐标，且相同表示共轭类给出规范等价运输。两种构造互为逆。证毕。

### 例 352.3（有限环面复形上的局部平坦与全局相位）

取一个有限 CW 环面模型：一个顶点 \(v\)，两条有向边 \(a,b\)，以及一张面，其边界词为

$$
aba^{-1}b^{-1}.
$$

取 \(G=U(1)\)，并令

$$
 g_a=e^{i\alpha},
 \qquad
 g_b=e^{i\beta}.
$$

由于 \(U(1)\) 阿贝尔，面 holonomy 为

$$
 H_f=g_ag_bg_a^{-1}g_b^{-1}=1
$$

对任意 \(\alpha,\beta\)。因此所有面都 flat，但两条非可缩基本闭路分别有 holonomy

$$
\rho(a)=e^{i\alpha},
 \qquad
\rho(b)=e^{i\beta}.
$$

若 \(\alpha\notin2\pi\mathbb Z\)，沿 \(a\) 绕一周不会回到同一纤维相位。由于 \(U(1)\) 共轭平凡，这个相位不能由根点规范改变。

同样的现象可在有限环带型复形中出现：局部矩形面可以全部 flat，而绕环带核心的单一非可缩闭路仍保留任意 \(G\) 元素。

### 定理 352.4（局部面数据不能决定拓扑 holonomy）

若 \(\pi_1(K)\) 非平凡，则存在两个 flat 边运输 \(g,g'\)，使所有面 holonomy 都相同为单位元，但某条非可缩闭路 \(c\) 满足

$$
T_g(c)\ne T_{g'}(c).
$$

### 证明

取非平凡元素 \([c]\in\pi_1(K,v_*)\)。一个表示取平凡表示 \(\rho([c])=1\)，另一个表示取使 \(\rho'([c])\ne1\) 的表示；在 \(G=U(1)\) 时，可将该生成元送到任意非平凡相位。定理 352.2 将二者实现为 flat 边运输。每个面边界在基本群中为单位元，故两者的面 holonomy 都为单位元，而 \(c\) 的 holonomy 不同。证毕。

### AHH 352.5（局部面与全局孔洞的分层）

二维关系几何至少有两层不同的可见量：

$$
\boxed{
\text{面 holonomy}
\quad\text{检测局部曲率};
}
$$

$$
\boxed{
\text{基本群表示}
\quad\text{检测非可缩闭路的全局运输}.
}
$$

局部 flatness 消除了可由面填充的闭路障碍，却不消除由孔洞产生的拓扑 holonomy。一次局部事件若只读到一张面内截面，就不会自动决定绕整个复形运输一圈后的关系。

---

## 353. 曲率残差、非阿贝尔次序与全局误差下界

精确 flatness 是二值条件；实际边运输还可以带有近似面约束。为了描述这种近似，给 \(G\) 配置一个双不变度量 \(d\)：

$$
 d(ag b,ah b)=d(g,h)
 \quad\text{对所有 }a,b,g,h\in G.
$$

紧李群的算子范数诱导度量、有限群的离散度量都给出本节的例子。双不变性保证误差不会因换局部坐标而改变。

### 定义 353.1（曲率残差与路径运输）

对面 \(f\)，定义曲率残差

$$
\kappa_f=d(H_f,1).
$$

对有向路径 \(p=e_1\cdots e_r\)，定义

$$
T(p)=g_{e_1}\cdots g_{e_r}.
$$

若 \(p,q\) 可串接，则

$$
T(pq)=T(p)T(q).
$$

若交换相邻两段，差异由交换子

$$
[a,b]=aba^{-1}b^{-1}
$$

控制；在非阿贝尔群中，\(ab\) 与 \(ba\) 一般不同。

### 定理 353.2（非阿贝尔路径次序是可观测关系）

若 \(a,b\in G\) 不交换，则存在一项闭路任务能区分按 \(ab\) 次序运输与按 \(ba\) 次序运输。具体地，两条同起同终的路径 \(p_{ab},p_{ba}\) 若运输分别为 \(ab,ba\)，则闭合组合的相对 holonomy 为

$$
T(p_{ab}p_{ba}^{-1})=ab(ba)^{-1}=aba^{-1}b^{-1}=[a,b]\ne1.
$$

### 证明

直接由路径串接和逆路径公式计算。若该交换子非单位元，测量一个区分单位元与 \([a,b]\) 的闭路效果即可区分两种次序。证毕。

### 定理 353.3（面残差对可缩闭路的上界）

设闭路 \(c\) 在二维复形中由有向面 \(f_1,\ldots,f_q\) 填充。则存在面边界的共轭因子 \(u_j\in G\) 和取向符号 \(\epsilon_j\in\{1,-1\}\)，使

$$
T(c)=
\prod_{j=1}^{q}u_jH_{f_j}^{\epsilon_j}u_j^{-1}.
$$

因而

$$
\boxed{
 d(T(c),1)\le\sum_{j=1}^{q}\kappa_{f_j}.
}
$$

特别地，若所有参与面的残差不超过 \(\varepsilon\)，则

$$
 d(T(c),1)\le q\varepsilon.
$$

### 证明

沿一个面逐步消去内部共享边。每次消去把相邻边界词替换为面 holonomy 或其逆，并因基点改变产生共轭。最后得到所示乘积。双不变性给出

$$
 d(u_jH_{f_j}^{\epsilon_j}u_j^{-1},1)=\kappa_{f_j}.
$$

对乘积反复使用三角不等式，得到上界。证毕。

### 推论 353.4（全局闭路给出的曲率下界）

若一个可缩闭路 \(c\) 的填充最少需要 \(q\) 个面，并测得

$$
\delta=d(T(c),1)>0,
$$

则任何使这些面都满足统一残差上界 \(\varepsilon\) 的边运输，都必须满足

$$
\boxed{\varepsilon\ge\delta/q.}
$$

### 证明

定理 353.3 给出 \(\delta\le q\varepsilon\)，移项即得。证毕。

### 定义 353.5（边修正距离）

设 \(\widetilde g\) 是另一份边运输，且对每条边

$$
 d(g_e,\widetilde g_e)\le\eta.
$$

对长度为 \(r\) 的闭路 \(c=e_1\cdots e_r\)，令 \(\widetilde T(c)\) 为 \(\widetilde g\) 的运输。

### 定理 353.6（平坦修正的全局下界）

若 \(\widetilde g\) 在 \(c\) 上的运输为单位元，则

$$
\boxed{
\eta\ge\frac{d(T_g(c),1)}{r}.
}
$$

更一般地，若 \(d(T_g(c),\widetilde T(c))\) 已知，则

$$
 d(T_g(c),\widetilde T(c))\le r\eta.
$$

### 证明

把 \(T_g(c)\) 与 \(\widetilde T(c)\) 的逐边因子依次替换。双不变度量使每次替换至多增加 \(\eta\)，三角不等式给出

$$
 d(T_g(c),\widetilde T(c))\le r\eta.
$$

若 \(\widetilde T(c)=1\)，即得第一式。证毕。

### 说明 353.7（局部误差与拓扑误差的方向）

定理 353.3 处理可由面填充的闭路：面残差可以沿填充传播，并给出闭路误差上界。定理 352.4 的非可缩闭路则不受这些面残差单独控制；即使每个面都精确 flat，拓扑 holonomy 仍可非平凡。

因此必须分开记录：

$$
\boxed{
\text{曲率残差是局部面约束的失败};
\qquad
\text{拓扑 holonomy 是非可缩闭路的剩余自由度}.
}
$$

把二者合并成一个“局部误差”数字，会丢失全局任务所需的方向信息。

### AHH 353.8（曲率的整体见证）

局部边读数可以全部接近相容，然而一条闭路仍能产生一个不可由局部重排消除的残差。非阿贝尔情形还要求保留路径次序，因为同一批边运输以不同顺序组合会产生不同交换子。

波性在此表现为多个面与路径贡献的有序联合；粒子式事件只提供某条局部路径上的一次记录。事件记录若不带面约束、路径次序和闭路检验，不能推出整体运输的误差范围。

---

## 354. 曲率感知全息边界

前面的结果给出一个比单纯边 holonomy 更强的边界对象：它既保存局部面约束，也保存孔洞上的基本群表示、局部事件怎样运输，以及近似关系的误差合同。

### 定义 354.1（曲率感知边界）

固定有限二维复形 \(K\)、群 \(G\)、双不变度量 \(d\)，以及一族声明的局部事件核。定义曲率感知边界为

$$
\boxed{
\eta_{\mathrm{curv}}=
\left(
K,
[g],
\{[H_f]\}_{f\in F},
[\rho_g],
\mathsf E,
\mathsf{Err},
\mathsf{Stop}
\right).
}
$$

各字段含义如下：

1. \([g]\) 是边运输的规范等价类；它保留可用于后续拼接的接口运输，而删除纯坐标命名。
2. \([H_f]\) 是每个面 holonomy 的共轭类；在阿贝尔群中可直接视为元素。
3. \([\rho_g]\) 是基本群表示的共轭类；它保留非可缩闭路的拓扑运输。
4. \(\mathsf E\) 是局部事件核，包括事件发生位置、钟标签、分支概率以及沿边和面的运输规则。
5. \(\mathsf{Err}\) 是面残差、闭路下界、允许的边修正距离和度量合同。
6. \(\mathsf{Stop}\) 是有限路径、预算、记录权限与停止后继；未声明的继续操作不自动纳入边界。

这一定义把“曲率”理解为有限关系复形中面运输相对单位元的残差，不把它直接宣称为连续时空或物理规范场的曲率。

### 定理 354.2（曲率感知边界的条件充分性）

若两个有限关系体具有相同的 \(\eta_{\mathrm{curv}}\)，并且允许的未来任务都属于边界声明的局部事件、有限运输、面约束、基本闭路检验和误差/停止合同，则二者对这些任务给出相同的：

1. 面 flatness 与近似 flatness 判定；
2. 全局截面存在性、根值多重性及其失败原因；
3. 可缩闭路的曲率残差上界与边修正下界；
4. 基本群闭路的 holonomy 共轭类；
5. 局部事件沿合法路径运输后的记录概率和条件后继；
6. 在预算与停止规则内可继续的合法任务树。

### 证明

第 1 项由 \([H_f]\) 和 \(\mathsf{Err}\) 直接决定。第 2 项在单纯连通部分由定理 351.3，在一般情形由定理 352.2 的表示及其不变量决定。第 3 项由定理 353.3 和 353.6，且其数值只使用 \(\mathsf{Err}\) 中声明的度量、面分解与闭路长度。第 4 项由 \([\rho_g]\) 决定。第 5 项由 \(\mathsf E\) 中的事件核、边面运输和记录后继逐步相乘；规范变换只在中间插入相消的局部坐标因子。第 6 项由 \(\mathsf{Stop}\) 对每一步允许的动作、资源和记录后继作有限归纳。故所有声明任务的结果在两关系体之间相同。证毕。

### 定理 354.3（删除字段的不可充分性）

在相同有限模型范围内，以下每种删字段都存在有限反例：

1. 删除面 holonomy：面内局部边数据相同，但一个关系体 flat、另一个不 flat；
2. 删除基本群表示：所有面都 flat，但环面基本闭路 holonomy 不同；
3. 删除路径次序：非阿贝尔交换子使两种合法运输给出不同闭路结果；
4. 删除事件—运输核：局部点击概率相同，但运输到另一接口后的条件记录不同；
5. 删除误差合同：同一局部残差读数对应不同的全局闭路下界或修正预算；
6. 删除停止后继：当前记录相同，但一个边界允许继续、另一个已资源耗尽。

### 证明

第 1 项取一张面并令其边界乘积分别为 \(1\) 与 \(a\ne1\)。第 2 项取例 352.3 中两组 \(U(1)\) 相位。第 3 项取定理 353.2 的非交换 \(a,b\)。第 4 项取同一局部效果核，但令两个接口之间的运输分别为单位元与一个可区分群元。第 5 项取相同面 holonomy 而改变允许边修正半径，定理 353.6 给出不同可行域。第 6 项取同一当前记录并分别附加“可继续”与“停止”后继。每个反例都说明删去字段后，至少一个声明任务不再由剩余摘要决定。证毕。

### 定义 354.4（曲率感知的波粒事件链）

在边界 \(\eta_{\mathrm{curv}}\) 上，一条合法事件链写成

$$
\mathsf C=
\bigl(
\text{面约束},
\text{路径运输},
\text{钟标签},
\text{局部结果},
\text{闭路检验},
\text{记录后继}
\bigr).
$$

它的“粒子式”部分是某个局部结果 \(x\) 在某个接口和钟标签上的离散记录；它的“波性”部分是该结果与其余路径、面 holonomy、基本群表示及后续记录的联合约束。

### AHH 354.5（曲率感知全息）

> 当局部边界被组织成有限二维复形时，全息边界不能只保存边运输或一张局部事件表。它还必须保存面约束的曲率残差、非可缩闭路的基本群表示、非阿贝尔路径次序、事件运输核以及误差和停止合同。

于是主线可写成

$$
\boxed{
\text{局部边运输}
\longrightarrow
\text{面 holonomy 与曲率残差}
\longrightarrow
\text{基本群 holonomy}
\longrightarrow
\text{事件运输与记录后继}.
}
$$

局部 flatness 使关系能够沿同伦路径一致运输；拓扑 holonomy 记录孔洞留下的整体自由度；曲率残差给出近似拼接的全局下界。一次局部点击可以在其接口上完全正确，却仍不足以决定面外闭路、非阿贝尔次序或基本群表示。

**新的 AHH 时刻是：二维面不是把整体性自动封口的“最后一层”；它只把可缩闭路的相容性固定下来。真正的全局边界还要保留孔洞上的 holonomy，以及曲率残差如何沿面拼接传播。**

### 来源与边界 354.6

本批在有限二维 CW 复形、有限群值边运输、双不变误差度量、有限局部事件核和显式停止合同下，给出面 flatness、基本群表示分类、非可阿贝尔路径次序、曲率残差上界、平坦修正下界与曲率感知全息边界。没有把有限二维复形结论推广为一般连续规范场论、量子引力或物理时空曲率定律；没有把 holonomy 的群元自动解释为可直接观测的粒子属性；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）

## 355. 三维胞腔、离散 Bianchi 恒等式与曲率闭合

上一批已经把二维面 holonomy 作为局部曲率记录下来。若有限关系体还有三维胞腔，就必须继续检查：这些面曲率是否能共同成为某个边运输的曲率，而不是只在每一张面上分别看起来合理。

### 定义 355.1（有限胞腔复形的上链）

设 \(K\) 是有限、定向的三维 CW 复形。取一个阿贝尔系数群 \(A\)，用加法记号写其上链群

$$
C^0(K;A)\xrightarrow{d_0}
C^1(K;A)\xrightarrow{d_1}
C^2(K;A)\xrightarrow{d_2}
C^3(K;A).
$$

这些映射是胞腔边界算子的对偶。对 \(k\)-上链 \(u\)，记其在定向 \(k\)-胞腔 \(\sigma\) 上的值为 \(u(\sigma)\)。若 \(g\in C^1(K;A)\) 是边运输的阿贝尔表示，定义面曲率

$$
F=d_1g\in C^2(K;A).
$$

若 \(\sigma\) 是三维胞腔，定义其 Bianchi 残差

$$
B(\sigma)=(d_2F)(\sigma).
$$

在乘法群中，这些加法式分别对应沿面边界的乘积以及沿三胞腔边界的有向乘积；本节使用加法记号以便直接处理误差。

### 定理 355.2（离散 Bianchi 恒等式）

胞腔复形满足

$$
d_2d_1=0.
$$

因此任何由全局边运输 \(g\) 产生的面曲率 \(F=d_1g\) 都满足

$$
\boxed{d_2F=0.}
$$

特别地，对每个三维胞腔 \(\sigma\)，其有向面边界上的曲率总和为零：

$$
\sum_{f\subset\partial\sigma}
\varepsilon_{\sigma f}F(f)=0,
\qquad
\varepsilon_{\sigma f}\in\{-1,0,1\}.
$$

### 证明

胞腔边界满足 \(\partial_1\partial_2=0\)。取对偶便得到 \(d_2d_1=0\)。代入 \(F=d_1g\) 即得 \(d_2F=0\)。按三胞腔的面展开，就是所写的带定向数的有限和。证毕。

### 定理 355.3（离散 Stokes 关系）

对任意三维上链 \(V\in C_3(K;\mathbb Z)\)，任意面曲率上链 \(F\in C^2(K;A)\)，有

$$
\langle F,\partial V\rangle
=
\langle d_2F,V\rangle.
$$

若 \(F=d_1g\)，则

$$
\boxed{\langle F,\partial V\rangle=0.}
$$

### 证明

这是胞腔边界与上链 coboundary 的对偶定义：

$$
\langle d_2F,V\rangle
=\langle F,\partial V\rangle.
$$

当 \(F=d_1g\) 时，定理 355.2 给出 \(d_2F=0\)。证毕。

### 推论 355.4（曲率表面不是任意独立记录的集合）

若一个闭合面 \(S\) 是三维链 \(V\) 的边界，则由同一个全局边运输产生的曲率满足

$$
\langle F,S\rangle=0.
$$

所以，逐面读数全部合法，并不保证它们能组成同一个三维关系体。三维胞腔还要求这些读数在带定向的面组合上闭合。

### 定义 355.5（表面 holonomy 与填充差异）

对定向二维链 \(S=\sum_f n_ff\)，定义阿贝尔表面 holonomy

$$
\mathsf H_F(S)=\langle F,S\rangle.
$$

若 \(S\) 与 \(S'\) 具有相同边界，则

$$
\mathsf H_F(S)-\mathsf H_F(S')
=
\mathsf H_F(S-S').
$$

当 \(S-S'=\partial V\) 且 \(F\) 满足 Bianchi 恒等式时，两种填充给出相同结果；若 \(S-S'\) 是非平凡二循环，则差异由其二维同调类承载。

### AHH 355.6（三维闭合的第一层）

二维面 holonomy 记录局部曲率；三维胞腔的 Bianchi 恒等式记录这些曲率是否能够共同闭合。一个面事件可以在自己的接口上完全正确，却仍然无法与同一三胞腔的其余面读数组成全局关系。

$$
\boxed{
\text{边运输}
\longrightarrow
\text{面曲率}
\longrightarrow
\text{三胞腔 Bianchi 闭合}.
}
$$

这里的闭合是代数相容性，不是额外假定的物理场方程。

---

## 356. 曲率可实现性、\(H^2\) 障碍与 \(H^1\) 残余

Bianchi 闭合是曲率来自边运输的必要条件，但在有孔洞的复形上还不一定充分。曲率必须是一个 coboundary，而不是仅仅一个 cocycle。

### 定义 356.1（闭上链、恰当上链与上同调）

记

$$
Z^k(K;A)=\ker d_k,
\qquad
B^k(K;A)=\operatorname{im}d_{k-1},
\qquad
H^k(K;A)=Z^k(K;A)/B^k(K;A).
$$

面曲率 \(F\) 的 Bianchi 条件是 \(F\in Z^2(K;A)\)。若存在边运输 \(g\) 使 \(F=d_1g\)，则 \(F\in B^2(K;A)\)。

### 定理 356.2（曲率的可实现性判据）

对任意 \(F\in C^2(K;A)\)，以下条件等价：

1. 存在边上链 \(g\in C^1(K;A)\)，使 \(d_1g=F\)；
2. \(F\in B^2(K;A)\)；
3. \(F\in Z^2(K;A)\) 且其上同调类 \([F]\in H^2(K;A)\) 为零。

### 证明

\(1\Leftrightarrow2\) 是 \(B^2=\operatorname{im}d_1\) 的定义。若 \(F\in B^2\)，则 \(d_2F=d_2d_1g=0\)，且 \([F]=0\)，所以 \(2\Rightarrow3\)。若 \(F\in Z^2\) 且 \([F]=0\)，按商群定义 \(F\in B^2\)，于是 \(3\Rightarrow2\)。证毕。

### 定理 356.3（同一曲率下的边运输残余）

若 \(g,g'\in C^1(K;A)\) 满足

$$
d_1g=d_1g',
$$

则

$$
z=g'-g\in Z^1(K;A).
$$

所有具有同一曲率 \(F\) 的边运输组成仿射集

$$
g+Z^1(K;A).
$$

若把顶点势 \(\lambda\in C^0(K;A)\) 视为规范变换

$$
g\longmapsto g+d_0\lambda,
$$

则同一曲率的规范等价类构成 \(H^1(K;A)\) 上的仿射空间。

### 证明

由线性性，

$$
d_1(g'-g)=d_1g'-d_1g=0,
$$

所以 \(z\in Z^1\)。反过来，任意 \(z\in Z^1\) 都使 \(d_1(g+z)=d_1g\)，得到第一项。规范变换只在 \(Z^1\) 中识别 \(B^1=\operatorname{im}d_0\)，故剩余商正是 \(H^1=Z^1/B^1\)。证毕。

### 例 356.4（环面上的两个不同障碍）

在一个有限环面 CW 模型中，若系数为 \(A=\mathbb R/2\pi\mathbb Z\)，则有两条独立的一维非可缩方向。零面曲率 \(F=0\) 可以由许多不同的边运输产生；它们的差异由

$$
H^1(K;A)\cong A\oplus A
$$

记录，正是两条基本闭路的全局相位。

另一方面，在只有一个二维胞腔且没有三维胞腔的模型中，任意面上链都满足 Bianchi 条件，因为 \(C^3=0\)。但边界词 \(aba^{-1}b^{-1}\) 的阿贝尔化为零，所以 \(d_1:C^1\to C^2\) 的像为零；非零面曲率是 \(Z^2\) 中的元素，却不在 \(B^2\) 中。它满足局部 Bianchi，却没有任何全局边运输可实现。

### 定理 356.5（局部闭合不足以保证全局来源）

存在有限二维或三维复形以及面曲率 \(F\)，满足

$$
d_2F=0,
$$

但不存在 \(g\) 使 \(F=d_1g\)。

### 证明

取例 356.4 的环面模型，选择一个非零的 \(F\in C^2\)。由于 \(C^3=0\)，有 \(d_2F=0\)。但 \(B^2=\operatorname{im}d_1=0\)，故 \(F\notin B^2\)，定理 356.2 排除全局边运输。证毕。

### AHH 356.6（曲率与全局来源的分层）

三维 Bianchi 只说明曲率是闭的；\(H^2\) 还决定它是否有一个全局边势。即使曲率来源存在，\(H^1\) 仍保存同一曲率下不可由顶点规范消去的边运输残余。

$$
\boxed{
\text{Bianchi 闭合}
\neq
\text{曲率可实现};
\qquad
\text{曲率可实现}
\neq
\text{边运输唯一}.
}
$$

这把“局部曲率”“全局来源”和“来源的拓扑残余”分成三个不同边界字段。

---

## 357. 近似 Bianchi、曲率修正与三维全局误差下界

实际记录的面曲率可能不满足精确 Bianchi。此时要区分两件事：把数据修正为一个闭上链，和进一步修正为一个恰当上链。前者是三维相容性，后者还要跨过 \(H^2\) 障碍。

### 定义 357.1（测量曲率与 Bianchi 残差）

令 \(A=\mathbb R^m\)，在 \(C^2(K;A)\) 和 \(C^3(K;A)\) 上取逐胞腔的 \(\ell_\infty\) 范数。给定测量面曲率

$$
\widehat F\in C^2(K;A),
$$

定义三胞腔残差

$$
b=d_2\widehat F.
$$

对三胞腔 \(\sigma\)，记其面入射数的绝对和为

$$
q_\sigma=\sum_f|\varepsilon_{\sigma f}|.
$$

### 定理 357.2（Bianchi 残差的最坏面修正下界）

若 \(F\in C^2(K;A)\) 满足 \(d_2F=0\)，并令

$$
\eta=\|\widehat F-F\|_\infty,
$$

则对每个三胞腔 \(\sigma\)，有

$$
\boxed{
\|b(\sigma)\|_\infty\le q_\sigma\eta.
}
$$

因此任何把测量数据修正为 Bianchi 闭合数据的方案都满足

$$
\boxed{
\eta\ge
\max_{\sigma:q_\sigma>0}
\frac{\|b(\sigma)\|_\infty}{q_\sigma}.
}
$$

### 证明

由 \(d_2F=0\)，有

$$
b=d_2(\widehat F-F).
$$

在三胞腔 \(\sigma\) 上展开：

$$
b(\sigma)
=\sum_f\varepsilon_{\sigma f}
(\widehat F-F)(f).
$$

取 \(\ell_\infty\) 范数并使用三角不等式，得到

$$
\|b(\sigma)\|_\infty
\le
\sum_f|\varepsilon_{\sigma f}|\eta
=q_\sigma\eta.
$$

对所有 \(\sigma\) 取最大值即得。证毕。

### 定理 357.3（闭合曲面读数的误差下界）

设 \(S=\partial V\) 是一个三维链的边界。若 \(F\) 满足 \(d_2F=0\)，则

$$
\langle F,S\rangle=0.
$$

对测量数据 \(\widehat F\)，有

$$
\boxed{
\|\langle\widehat F,S\rangle\|_\infty
\le
\|S\|_1\,\|\widehat F-F\|_\infty,
}
$$

其中 \(\|S\|_1=\sum_f|n_f|\)。因此若测得闭合曲面总残差

$$
\Delta_S=\|\langle\widehat F,S\rangle\|_\infty,
$$

则任何 Bianchi 闭合修正都满足

$$
\boxed{
\|\widehat F-F\|_\infty\ge\Delta_S/\|S\|_1.
}
$$

### 证明

由定理 355.3，\(\langle F,S\rangle=0\)。故

$$
\langle\widehat F,S\rangle
=\langle\widehat F-F,S\rangle.
$$

逐面展开并使用三角不等式得到第一式，移项得到第二式。证毕。

### 定理 357.4（可实现修正的二层判据）

设 \(\widehat F\) 已被修正为某个 Bianchi 闭合 \(F\in Z^2(K;\mathbb R^m)\)。则存在边运输 \(g\) 使 \(d_1g=F\)，当且仅当

$$
[F]=0\in H^2(K;\mathbb R^m).
$$

若 \([F]\ne0\)，则修正已经通过了所有三胞腔 Bianchi 检查，却仍不能来自全局边运输。

### 证明

这是定理 356.2 在 \(\mathbb R^m\) 系数下的直接应用。证毕。

### 推论 357.5（有限维噪声下的不可消除残差）

若 \(\widehat F\) 是 Bianchi 闭合但 \([\widehat F]\ne0\)，则不存在零误差的全局边运输解释。由于 \(B^2(K;\mathbb R^m)\) 是有限维线性空间中的闭子空间，

$$
\operatorname{dist}_\infty
(\widehat F,B^2)>0.
$$

这份正距离是曲率数据跨越 \(H^2\) 可实现性障碍所需的最小面修正量。

### 证明

若距离为零，有限维空间中的闭子空间会包含 \(\widehat F\)，与 \([\widehat F]\ne0\) 矛盾。证毕。

### 说明 357.6（误差下界的两种来源）

三胞腔残差

$$
d_2\widehat F
$$

给出局部三维相容性的下界；上同调残余

$$
[\widehat F]\in H^2
$$

给出全局来源的下界。前者可以通过改变面读数使其消失，后者即使在 Bianchi 已满足时也可能继续存在。

### AHH 357.7（三维曲率的可验证性）

曲率的“整体性”不只是一张面表是否平滑，而是至少需要通过两道门：

$$
\boxed{
\text{三胞腔闭合}
\quad\text{和}\quad
\text{全局边势可实现}.
}
$$

局部事件记录可以暴露第一道门的残差；只有访问到足够的二维周期和边运输接口，才能检验第二道门。把两者混成一个噪声数，会错误地把拓扑不可实现性当作普通测量误差。

---

## 358. 三维曲率感知全息与表面事件后继

现在把边运输、面曲率、三胞腔闭合、上同调残余和事件记录放入同一个可继续的边界。

### 定义 358.1（三维曲率全息边界）

固定有限三维 CW 复形 \(K\)、阿贝尔系数群 \(A\)、必要时的非阿贝尔边运输群 \(G\)、事件核和误差/停止合同。定义

$$
\boxed{
\eta_{\mathrm{3curv}}=
\left(
K,
[g],
F,
d_2F,
[F]_{H^2},
H^1,
\mathsf{SurfEvt},
\mathsf{Err}_3,
\mathsf{Stop}
\right).
}
$$

其中：

1. \([g]\) 保存边运输的规范等价类与非阿贝尔闭路 holonomy；
2. \(F\) 保存面曲率及其定向；
3. \(d_2F\) 保存三胞腔 Bianchi 残差；
4. \([F]_{H^2}\) 保存曲率是否有全局边势的可实现性类；
5. \(H^1\) 保存同一曲率下不能由顶点规范消去的边运输残余；
6. \(\mathsf{SurfEvt}\) 保存表面探测、局部事件、路径运输、钟标签及记录后继；
7. \(\mathsf{Err}_3\) 保存三胞腔残差、闭曲面下界、曲率修正半径和 \(H^2\) 距离合同；
8. \(\mathsf{Stop}\) 保存允许的三维继续操作、权限、预算和停止后继。

若边运输群非阿贝尔，则面曲率字段只对指定的阿贝尔系数或中心部分作加法化；不能把非阿贝尔面数据未经额外高阶结构而直接当作普通上链。

### 定理 358.2（三维曲率边界的条件充分性）

若两个关系体具有相同的 \(\eta_{\mathrm{3curv}}\)，且未来任务限于边界声明的有限边运输、面/表面事件、三胞腔闭合、上同调可实现性、误差合同和停止规则，则二者给出相同的：

1. 面曲率与三胞腔 Bianchi 残差；
2. 曲率是否能由全局边运输产生；
3. 同一曲率下的 \(H^1\) 边运输残余；
4. 可缩表面与不同填充之间的 holonomy 关系；
5. 表面事件沿合法路径运输后的记录概率和条件后继；
6. 在误差预算内的最小修正下界与可继续任务树。

### 证明

第 1 项由 \(F\) 和 \(d_2F\) 直接给出。第 2 项由定理 356.2 和字段 \([F]_{H^2}\) 决定。第 3 项由定理 356.3 和 \(H^1\) 决定。第 4 项由定理 355.3、表面链边界和基本闭路字段决定。第 5 项由 \(\mathsf{SurfEvt}\) 中的事件核、边/面运输与记录后继逐步组合；每一步的规范因子在相邻接口相消。第 6 项由定理 357.2—357.5 与 \(\mathsf{Err}_3\) 决定，再对有限停止树作归纳。故所有声明任务的结果相同。证毕。

### 定理 358.3（删去三维字段的有限反例）

以下每项删除都存在有限反例：

1. 删除 \(d_2F\)：每张面局部读数相同，但一个三胞腔闭合、另一个不闭合；
2. 删除 \([F]_{H^2}\)：两份曲率都满足 Bianchi，但只有一份来自全局边运输；
3. 删除 \(H^1\)：曲率相同而基本闭路边 holonomy 不同；
4. 删除表面事件核：面总曲率相同，但局部事件运输到另一接口后的记录不同；
5. 删除三维误差合同：相同面读数却得到不同的修正半径和闭曲面风险；
6. 删除停止后继：当前表面记录相同，但一个关系体允许沿第三维继续，另一个已经停止。

### 证明

第 1 项取一个三胞腔并在一张面上改变曲率而不改变其余面。第 2 项取例 356.4 中 Bianchi 闭合但非零 \(H^2\) 类的面数据。第 3 项取环面上零曲率而具有不同 \(H^1\) 相位的两个边运输。第 4 项固定局部效果概率，改变表面到目标接口的运输核。第 5 项使用定理 357.2 或 357.3 的不同误差合同。第 6 项使用相同当前记录并分别附加可继续与停止后继。每项都给出一个剩余摘要无法决定的声明任务。证毕。

### 定义 358.4（三维表面事件链）

一条合法的表面事件链写成

$$
\mathsf C_3=
\bigl(
\text{边运输},
\text{面曲率},
\text{三胞腔闭合},
\text{表面路径},
\text{钟标签},
\text{局部结果},
\text{后继记录}
\bigr).
$$

其中局部结果仍是离散的粒子式事件；面曲率和三胞腔闭合则决定这个事件能否作为同一整体关系的一部分被运输、比较并继续。

### AHH 358.5（三维曲率全息）

> 当关系体具有三维胞腔时，二维曲率表还不是完整边界。全息边界必须同时保存 Bianchi 闭合、曲率的 \(H^2\) 可实现性、同一曲率下的 \(H^1\) 边运输残余，以及表面事件的运输和停止后继。

主线因此继续为

$$
\boxed{
\text{边运输}
\longrightarrow
\text{面曲率}
\longrightarrow
\text{三胞腔 Bianchi}
\longrightarrow
\text{上同调可实现性}
\longrightarrow
\text{表面事件与记录后继}.
}
$$

**新的 AHH 时刻是：三维闭合不只是给曲率增加一条约束；它把“这份局部曲率是否来自同一个整体”变成一个可检验的上同调问题。Bianchi 消除局部不闭合，\(H^2\) 暴露全局无来源，\(H^1\) 则保存同一来源下仍无法由局部规范消掉的边运输记忆。**

### 来源与边界 358.6

本批在有限定向三维 CW 复形、阿贝尔面曲率上链、有限边运输、有限表面事件核、有限维误差度量和显式停止合同下，给出离散 Bianchi 恒等式、离散 Stokes 关系、曲率可实现性 \(H^2\) 判据、同一曲率的 \(H^1\) 残余、近似闭合下界和三维曲率感知全息。没有把这些有限胞腔结论推广为连续规范场论、量子引力或物理时空曲率定律；没有把上同调类自动解释为可直接观测的粒子属性；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）


## 359. 有限胞腔上链的 Hodge 分解

上一批已经区分了曲率的闭合性、可实现性与 \(H^1\) 残余。为了说明这些残余在有限模型中怎样彼此正交，给上链空间加入一个明确的内积。这个内积是重建与误差预算的结构，不是另加一个物理观察者。

### 定义 359.1（有限上链内积与伴随）

令 \(K\) 是有限定向胞腔复形，系数取 \(\mathbb R\)。在每个有限维上链空间 \(C^k(K;\mathbb R)\) 选择正定内积 \(\langle\cdot,\cdot\rangle_k\)。记

$$
d_k:C^k\longrightarrow C^{k+1}
$$

为 coboundary，并定义其伴随

$$
\delta_{k+1}=d_k^*:C^{k+1}\longrightarrow C^k.
$$

定义第 \(k\) 层的 Hodge Laplacian：

$$
\boxed{
\Delta_k=d_{k-1}\delta_k+\delta_{k+1}d_k.
}
$$

约定没有相应阶数的项为零。定义 harmonic 子空间

$$
\mathcal H^k=\ker\Delta_k.
$$

内积可以来自胞腔权重、探测器精度或资源成本。改变内积会改变最小范数代表和误差大小，但不改变闭合关系 \(d_{k+1}d_k=0\)。

### 定理 359.2（有限 Hodge 正交分解）

对每个 \(k\)，有正交直和

$$
\boxed{
C^k
=
\operatorname{im}d_{k-1}
\ \oplus\
\mathcal H^k
\ \oplus\
\operatorname{im}\delta_{k+1}.
}
$$

并且

$$
\mathcal H^k
=
\ker d_k\cap\ker\delta_k.
$$

### 证明

对任意 \(u\in C^k\)，有

$$
\langle\Delta_ku,u\rangle
=
\langle d_{k-1}\delta_ku,u\rangle
\ +\
\langle\delta_{k+1}d_ku,u\rangle
=
\|\delta_ku\|^2+\|d_ku\|^2.
$$

因此 \(\Delta_ku=0\) 当且仅当 \(d_ku=0\) 且 \(\delta_ku=0\)。

又因为 \(d_kd_{k-1}=0\)，有

$$
\left\langle d_{k-1}a,\delta_{k+1}b\right\rangle
=
\left\langle d_kd_{k-1}a,b\right\rangle
=0.
$$

同理，\(\mathcal H^k\) 与两幅像空间都正交。有限维线性代数给出

$$
(\ker\Delta_k)^\perp=\operatorname{im}\Delta_k
\subseteq
\operatorname{im}d_{k-1}+\operatorname{im}\delta_{k+1}.
$$

反向包含由上式的正交性成立，故三项正交直和张成整个 \(C^k\)。证毕。

### 定理 359.3（harmonic 空间代表上同调）

映射

$$
\mathcal H^k\longrightarrow H^k(K;\mathbb R),
\qquad
h\longmapsto[h],
$$

是线性同构。因此

$$
\boxed{\dim\mathcal H^k=\dim H^k(K;\mathbb R).}
$$

### 证明

先取任意闭上链 \(z\in Z^k=\ker d_k\)。由定理 359.2 写成

$$
z=d_{k-1}a+h+\delta_{k+1}b.
$$

因为 \(d_kz=0\)，有 \(d_k\delta_{k+1}b=0\)。于是

$$
\|\delta_{k+1}b\|^2
=
\langle d_k\delta_{k+1}b,b\rangle
=0,
$$

故 \(\delta_{k+1}b=0\)，从而 \(z=d_{k-1}a+h\)。这说明每个上同调类都有 harmonic 代表。

若 \(h\in\mathcal H^k\) 同时是恰当上链 \(h=d_{k-1}a\)，则

$$
\|h\|^2
=
\langle d_{k-1}a,h\rangle
=
\langle a,\delta_kh\rangle
=0.
$$

所以 \(h=0\)，代表唯一。证毕。

### 推论 359.4（曲率的局部与拓扑正交层）

对一阶边上链 \(g\)，有

$$
g
=
\underbrace{d_0\lambda}_{\text{顶点规范}}
\ +\
\underbrace{h_1}_{\text{harmonic 全局模式}}
\ +\
\underbrace{\delta_2\beta}_{\text{曲率响应模式}}.
$$

其中：

1. \(d_0\lambda\) 不改变面曲率 \(d_1g\)，属于坐标规范；
2. \(h_1\) 满足 \(d_1h_1=0\)，不被局部曲率读数看到，却承载 \(H^1\) 周期；
3. \(\delta_2\beta\) 是与面曲率直接相连的 coexact 部分。

因此，同一个局部曲率读数可以对应不同的全局 harmonic 波形。

### AHH 359.5（Hodge 三分）

有限关系体中的“整体波”可以分成三个可检验层：

$$
\boxed{
\text{exact}
\;|\;
\text{harmonic}
\;|\;
\text{coexact}.
}
$$

exact 是局部命名变化，harmonic 是局部曲率看不见的全局记忆，coexact 是实际被面曲率激活的局部响应。粒子式事件只在声明的效果接口上读取其中的一部分；一次读数不会自动把三层合并成完整状态。

---

## 360. 曲率重建、规范固定与最小范数代表

Hodge 分解不仅分类残余，还给出一个明确的重建程序：先由曲率确定 coexact 部分，再由周期读数确定 harmonic 部分，最后把 exact 部分作为规范选择处理。

### 定义 360.1（曲率解集与三个子空间）

在一阶上链空间中置

$$
\mathcal E^1=\operatorname{im}d_0,
\qquad
\mathcal C^1=\operatorname{im}\delta_2,
\qquad
\mathcal H^1=\ker\Delta_1.
$$

给定可实现曲率 \(F\in B^2(K;\mathbb R)\)，定义解集

$$
\mathcal S_F
=
\{g\in C^1:d_1g=F\}.
$$

### 定理 360.2（曲率确定唯一的 coexact 代表）

对每个可实现 \(F\)，存在唯一 \(g_{\mathrm{coex}}\in\mathcal C^1\)，使

$$
d_1g_{\mathrm{coex}}=F.
$$

所有曲率解都唯一写成

$$
\boxed{
g=g_{\mathrm{coex}}+d_0\lambda+h,
\qquad
\lambda\in C^0,\ h\in\mathcal H^1.
}
$$

### 证明

取一个解 \(g\in\mathcal S_F\)，由定理 359.2 分解为

$$
g=d_0\lambda+h+\delta_2\beta.
$$

因为 \(d_1d_0=0\) 且 \(d_1h=0\)，有

$$
F=d_1\delta_2\beta.
$$

令 \(g_{\mathrm{coex}}=\delta_2\beta\)。若 \(u\in\mathcal C^1\) 也满足 \(d_1u=0\)，写 \(u=\delta_2b\)，则

$$
\|u\|^2
=
\langle\delta_2b,u\rangle
=
\langle b,d_1u\rangle
=0.
$$

故曲率到 coexact 部分的映射是单射，\(g_{\mathrm{coex}}\) 唯一。反向代入给出全部解。证毕。

### 定理 360.3（最小范数规范）

在 \(\mathcal S_F\) 中，唯一满足

$$
g_{\min}\perp\ker d_1
$$

的解是 \(g_{\mathrm{coex}}\)。它满足

$$
\boxed{
\|g_{\min}\|
\le
\|g\|
\quad\text{对所有 }g\in\mathcal S_F.
}
$$

若只允许顶点规范变换 \(g\mapsto g+d_0\lambda\)，则 Coulomb 条件

$$
\delta_1g=0
$$

可以消去 exact 方向，但不会消去 harmonic 方向。

### 证明

由 Hodge 分解，

$$
\ker d_1=\mathcal E^1\oplus\mathcal H^1.
$$

而 \(\mathcal C^1\) 与这两个子空间正交。任意解都为

$$
g=g_{\mathrm{coex}}+v,
\qquad
v\in\ker d_1.
$$

勾股关系给出

$$
\|g\|^2=\|g_{\mathrm{coex}}\|^2+\|v\|^2.
$$

等号只在 \(v=0\) 时成立。Coulomb 条件对 exact 分量的作用来自

$$
\delta_1d_0=\Delta_0,
$$

其核只包含不改变 \(g\) 的常数势；\(\delta_1h=0\) 对 harmonic \(h\) 恒成立，所以它不能被该规范条件消除。证毕。

### 定义 360.4（周期读数）

取线性映射

$$
\Pi:\mathcal H^1\longrightarrow\mathbb R^r
$$

使其在 harmonic 空间上单射。它可以由一组基本闭路积分、周期 holonomy 的局部坐标或其他声明的全局接口构成。

### 定理 360.5（曲率加周期的唯一重建）

若 \(F\) 可实现，且给定周期数据 \(p\in\operatorname{im}\Pi\)，则存在唯一的 harmonic \(h_p\in\mathcal H^1\) 满足

$$
\Pi(h_p)=p.
$$

因此

$$
\boxed{
g_{\mathrm{rec}}=g_{\mathrm{coex}}+h_p
}
$$

是满足 Coulomb 条件和周期合同的唯一规范代表。所有其他满足同一数据的边运输只差一个不改变代表的常数顶点势。

### 证明

\(\Pi\) 在 \(\mathcal H^1\) 上单射，故 \(p\) 至多对应一个 \(h_p\)；由 \(p\in\operatorname{im}\Pi\) 存在性成立。定理 360.2 给出所有解的 exact、harmonic、coexact 分解。Coulomb 条件去除 exact 变化，周期条件固定 harmonic，曲率固定 coexact，故只剩常数势的零作用。证毕。

### AHH 360.6（重建的三步合同）

完整边界的重建不应把所有读数混成一张位置图，而应按三步进行：

$$
\boxed{
\text{曲率读数}
\longrightarrow
\text{coexact 响应};
\qquad
\text{周期读数}
\longrightarrow
\text{harmonic 记忆};
\qquad
\text{规范选择}
\longrightarrow
\text{exact 表示}.
}
$$

这说明“全息恢复”有不同强度：只给 \(F\) 只能恢复 coexact 部分；给 \(F\) 加上足够周期才恢复规范等价类；给出具体规范还需要额外的表示约定。

---

## 361. 局部事件、周期接口与可识别性

上一批的边界语言强调合法后继。本节把它转成一个简单的可识别性判据：哪些事件接口能够切开曲率解集的纤维，哪些接口只看得到 coexact 部分。

### 定义 361.1（曲率与事件观察）

定义局部曲率观察

$$
\mathcal O_{\mathrm{curv}}(g)=d_1g.
$$

给定周期映射 \(\Pi\)，定义增强观察

$$
\mathcal O_{\mathrm{enh}}(g)
=
\bigl(d_1g,\Pi(P_{\mathcal H^1}g)\bigr),
$$

其中 \(P_{\mathcal H^1}\) 是 Hodge 正交投影。

对有限事件族 \(\mathcal T\)，若每个事件 \(t\) 的记录核可以写成

$$
R_t(g)
=
\Phi_t\!\left(
d_1g,\Pi(P_{\mathcal H^1}g)
\right),
$$

则称 \(\mathcal T\) **通过增强边界因子化**。这里 \(\Phi_t\) 可以包含记录概率、后继状态和停止条件；因子化是模型的声明合同。

### 定理 361.2（局部曲率观察的精确纤维）

对任意 \(g,g'\in C^1\)，有

$$
\mathcal O_{\mathrm{curv}}(g)
=
\mathcal O_{\mathrm{curv}}(g')
\quad\Longleftrightarrow\quad
g'-g\in\ker d_1.
$$

由 Hodge 分解，

$$
\ker d_1=\operatorname{im}d_0\oplus\mathcal H^1.
$$

因此局部曲率观察恰好把 exact 规范和 harmonic 全局模式合并在同一观察纤维中。

### 证明

第一等价由

$$
d_1g=d_1g'
\Longleftrightarrow
d_1(g'-g)=0
$$

直接得到。若 \(z\in\ker d_1\)，按定理 359.2 分解为 \(d_0\lambda+h+\delta_2\beta\)。由 \(d_1z=0\) 和定理 360.2 的单射性，\(\delta_2\beta=0\)，故 \(z=d_0\lambda+h\)。反向包含显然。证毕。

### 定理 361.3（周期读数切开全部非规范纤维）

若 \(\Pi\) 在 \(\mathcal H^1\) 上单射，则

$$
\mathcal O_{\mathrm{enh}}(g)
=
\mathcal O_{\mathrm{enh}}(g')
\quad\Longleftrightarrow\quad
g'-g\in\operatorname{im}d_0.
$$

所以增强观察能够唯一确定边运输的规范等价类。

### 证明

若增强观察相同，定理 361.2 给出 \(g'-g=d_0\lambda+h\)，其中 \(h\in\mathcal H^1\)。周期分量相同给出 \(\Pi(h)=0\)，\(\Pi\) 单射故 \(h=0\)。反向若差是 \(d_0\lambda\)，曲率与 harmonic 投影都不变。证毕。

### 推论 361.4（事件的粒子式读数不自动恢复 harmonic 波）

若事件族只通过 \(\mathcal O_{\mathrm{curv}}\) 因子化，则任意两个只相差非零 harmonic 模式的边运输具有相同全部事件统计：

$$
g'=g+h,
\qquad
0\ne h\in\mathcal H^1.
$$

若某事件直接耦合于一个周期接口 \(\Pi\)，则它可以切开这两个状态；这需要额外的访问权限，不能由局部点击记录自动推出。

### 证明

由 \(d_1h=0\)，局部曲率观察相同，因子化合同使所有 \(R_t\) 相同。若事件访问 \(\Pi(h)\ne0\)，则增强观察不同，定理 361.3 给出可区分性。证毕。

### 定理 361.5（任务族的充分边界判据）

固定一个来源类 \(\mathcal S\subseteq C^1\)。若所有声明任务响应 \(R_t\) 都通过 \(\mathcal O_{\mathrm{enh}}\) 因子化，且未来合法性、结果概率和后继边界也只依赖 \(\mathcal O_{\mathrm{enh}}\)，则 \(\mathcal O_{\mathrm{enh}}\) 对任务族 \(\mathcal T\) 是充分边界。

若存在 \(g,g'\in\mathcal S\) 具有相同 \(\mathcal O_{\mathrm{enh}}\) 但某个任务或后继不同，则该观察不是充分边界。

### 证明

第一部分是因子化定义对每一步记录和后继的有限归纳：当前观察相同，下一步合法动作、结果分布和后继观察相同，故有限任务词的联合响应相同。第二部分由一对观察相同而目标不同的来源直接否定充分性。证毕。

### AHH 361.6（局部事件的识别边界）

局部粒子式事件是一个观察接口，而不是完整本体。它可以精确读取某个曲率效果，却可能把

$$
\operatorname{im}d_0\oplus\mathcal H^1
$$

压成同一条观察纤维。只有追加周期接口，才可能把 harmonic 波形从这个纤维中切出。

---

## 362. Hodge 感知全息边界

把前面四层合并，就得到一个同时支持重建、事件识别、误差估计和继续操作的边界。

### 定义 362.1（Hodge 感知边界）

固定有限胞腔复形、上链内积、允许的曲率和事件接口。定义

$$
\boxed{
\eta_{\mathrm{Hodge}}=
\left(
K,
d,
\delta,
\operatorname{spec}\Delta,
F,
\mathcal C^1,
\mathcal H^1,
\Pi,
\mathsf{Event},
\mathsf{Err},
\mathsf{Stop}
\right).
}
$$

其中：

1. \(d,\delta\) 与 \(\operatorname{spec}\Delta\) 保存有限 Hodge 结构和重建条件数；
2. \(F\) 保存当前曲率以及它是否满足 \(H^2\) 可实现性；
3. \(\mathcal C^1\) 保存由曲率激活的 coexact 响应空间；
4. \(\mathcal H^1\) 与 \(\Pi\) 保存局部曲率看不见的 harmonic 周期；
5. \(\mathsf{Event}\) 保存局部点击、周期探针、结果概率和记录后继；
6. \(\mathsf{Err}\) 保存曲率残差、周期估计误差、最小范数代价和停止预算；
7. \(\mathsf{Stop}\) 保存未来允许动作、资源耗尽和停止后继。

### 定理 362.2（Hodge 边界的条件充分性）

若两个有限关系体具有相同的 \(\eta_{\mathrm{Hodge}}\)，且未来任务限于边界声明的有限曲率重建、规范固定、周期观测、局部事件、误差合同和停止规则，则二者给出相同的：

1. Hodge 正交分解与 harmonic 维数；
2. 曲率的 coexact 重建和最小范数代表；
3. 周期数据约束下的规范等价类恢复；
4. 局部事件与周期事件的记录分布和条件后继；
5. 曲率、周期和重建误差的声明下界；
6. 有限预算内的合法任务树。

### 证明

第 1 项由 \(d,\delta,\operatorname{spec}\Delta\) 决定。第 2 项由定理 360.2—360.3；第 3 项由定理 360.5 与 \(\Pi\) 的声明；第 4 项由 \(\mathsf{Event}\) 的因子化核和记录后继递归；第 5 项由 \(\mathsf{Err}\) 与有限维正交投影的范数公式；第 6 项由 \(\mathsf{Stop}\) 作有限深度归纳。所有任务的外部响应因此相同。证毕。

### 定理 362.3（删除 Hodge 字段的有限反例）

以下删字段均有有限反例：

1. 删除 coexact 曲率字段：同一 harmonic 周期但局部面曲率不同；
2. 删除 harmonic 周期字段：环面上的零曲率边运输具有不同基本闭路相位；
3. 删除内积或 Laplacian：同一规范等价类的最小范数代表与误差代价不同；
4. 删除事件核：同一 Hodge 摘要在不同探测接口下给出不同记录后继；
5. 删除停止合同：当前重建相同，但一个接口允许继续、另一个已耗尽预算。

### 证明

第 1 项取两个不同的 coexact 上链；第 2 项取例 356.4 的两个 \(H^1\) 周期；第 3 项改变胞腔权重，最小范数投影随之改变；第 4 项改变事件的周期耦合或局部效果核；第 5 项附加不同资源后继。每项都产生一个剩余摘要无法决定的声明任务。证毕。

### 定义 362.4（Hodge 波粒事件链）

一条合法事件链写成

$$
\mathsf C_{\mathrm H}=
\bigl(
\text{exact 规范},
\text{coexact 曲率响应},
\text{harmonic 周期},
\text{局部或周期探测},
\text{钟标签},
\text{离散结果},
\text{后继边界}
\bigr).
$$

粒子式事件是链中的离散结果；波性则是三个 Hodge 分量之间的相干约束以及它们对未来接口的联合作用。

### AHH 362.5（Hodge 全息）

> 全息边界的最小充分性不是“保存最多的局部读数”，而是把 exact 规范、coexact 曲率和 harmonic 全局记忆分别保存到它们真正影响未来任务的程度。局部点击通常只切到 coexact 响应；周期探针才可能读出 harmonic 波形。

主线可写成

$$
\boxed{
\text{上同调闭合}
\longrightarrow
\text{Hodge 三分}
\longrightarrow
\text{曲率与周期重建}
\longrightarrow
\text{局部/全局事件}
\longrightarrow
\text{记录后继}.
}
$$

**新的 AHH 时刻是：所谓“波的整体形状”在有限关系几何中不是一个额外的神秘实体，而是 coexact 局部响应与 harmonic 全局模式的联合；exact 部分只是表示选择。粒子式事件只在声明的接口上切片，是否看见 harmonic 模式完全取决于周期访问权限。**

### 来源与边界 362.6

本批在有限定向胞腔复形、有限维实上链、正定内积、Hodge 伴随、有限曲率与周期接口、显式事件核和停止合同下，给出有限 Hodge 分解、harmonic 上同调代表、曲率 coexact 重建、最小范数规范、周期增强可识别性与 Hodge 感知全息。没有把有限维 Hodge 结构推广为连续场论、量子引力或物理时空的普适定律；没有把 harmonic 分量自动解释为可直接观测的粒子属性；没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）


## 363. Hodge 模式的有限动力学

上一批的 Hodge 分解是静态的。本节把同一个有限上链空间复化，给出两种明确的模式运输：保持相位的酉运输和耗散高频分量的热运输。它们都是有限矩阵合同，不把某一合同直接宣称为现实世界唯一动力学。

### 定义 363.1（Hodge 动力学）

令

$$
\mathcal C^k=C^k(K;\mathbb R)\otimes_{\mathbb R}\mathbb C
$$

并把 \(\Delta_k\) 延拓为复 Hilbert 空间上的自伴算子。定义

$$
U_t=e^{-it\Delta_k},
\qquad
S_t=e^{-t\Delta_k},
\qquad
t\ge0.
$$

\(U_t\) 是相位保持的 Hodge 运输，\(S_t\) 是正半群式的耗散运输。若

$$
\Delta_k\phi_j=\lambda_j\phi_j,
\qquad
\lambda_j\ge0,
$$

并令 \(P_j\) 为相应谱投影，则

$$
U_t=\sum_j e^{-it\lambda_j}P_j,
\qquad
S_t=\sum_j e^{-t\lambda_j}P_j.
$$

零特征值空间正是复化后的 harmonic 空间。

### 定理 363.2（相位运输、耗散运输与 harmonic 记忆）

对任意 \(u\in\mathcal C^k\)，有

$$
\|U_tu\|=\|u\|,
$$

以及

$$
\|S_tu\|\le\|u\|.
$$

若 \(P_0\) 是 \(\ker\Delta_k\) 上的投影，则

$$
\lim_{t\to\infty}S_tu=P_0u.
$$

并且

$$
\frac{d}{dt}\|S_tu\|^2
=-2\langle S_tu,\Delta_kS_tu\rangle\le0.
$$

### 证明

谱展开给出

$$
\|U_tu\|^2
=\sum_j\|P_ju\|^2
=\|u\|^2,
$$

而

$$
\|S_tu\|^2
=\sum_je^{-2t\lambda_j}\|P_ju\|^2
\le\|u\|^2.
$$

当 \(t\to\infty\) 时，所有 \(\lambda_j>0\) 的因子趋于零，只剩 \(P_0u\)。对半群求导即得最后一式。证毕。

### 定义 363.3（模式探测接口）

给定有限维输出空间 \(Y\) 和线性接口

$$
C:\mathcal C^k\longrightarrow Y,
$$

定义第 \(n\) 个离散时间样本的振幅输出

$$
y_n=C\,U_{n\tau}u
$$

或耗散版本

$$
y_n=C\,S_{n\tau}u,
$$

其中 \(\tau>0\) 是已标定的内部钟步长。之后的离散仪器把 \(y_n\) 转为结果概率与记录后继；本节先研究振幅接口本身的可见性。

称谱子空间 \(P_j\mathcal C^k\) 对接口 \(C\) **暗**，若

$$
CP_j=0.
$$

### 推论 363.4（局部事件可以保留 harmonic 模式，也可以完全错过它）

若 \(C P_0=0\)，则 harmonic 分量不会出现在任何 \(y_n=C U_{n\tau}u\) 中；若 \(C P_0\ne0\)，则 harmonic 分量以不随 \(n\) 变化的振幅进入每一轮输出。

对热运输，非零特征值模式会衰减，而 harmonic 模式仍保持原值。因此“长期没有局部点击”既可能来自暗接口，也可能来自耗散后只剩下接口未访问的 harmonic 记忆。

### 证明

由 \(U_tP_0=P_0\) 和 \(CP_j=0\) 的定义直接得到。热运输的结论由定理 363.2 的谱展开得到。证毕。

### AHH 363.5（动力学中的波体）

有限 Hodge 动力学把波形拆成：

$$
\boxed{
\text{谱相位}
\;+\;
\text{局部接口耦合}
\;+\;
\text{harmonic 长期记忆}.
}
$$

粒子式事件不是某个 \(u\) 在时间轴上被动切开的照片；它是 \(U_{n\tau}u\) 或 \(S_{n\tau}u\) 经过 \(C\) 和仪器后的分支记录。时间标签只有与 \(\tau\)、动力学和接口一起才有关系意义。

---

## 364. 时间采样、谱混叠与有限可识别性

时间切片是否能区分整体模式，取决于采样算子 \(C U_\tau^n\) 的秩。仅增加切片标签而不检查谱相位，不能保证增加信息。

### 定义 364.1（有限采样观察算子）

固定 \(\tau>0\)，令

$$
A_\tau=U_\tau=e^{-i\tau\Delta_k}.
$$

设 \(A_\tau\) 的不同特征值为

$$
\zeta_1,\ldots,\zeta_r,
$$

相应谱投影为 \(Q_1,\ldots,Q_r\)。注意不同的 \(\Delta_k\) 特征值 \(\lambda,\mu\) 可能给出同一个采样特征值：

$$
e^{-i\tau\lambda}=e^{-i\tau\mu}
\quad\Longleftrightarrow\quad
\tau(\lambda-\mu)\in2\pi\mathbb Z.
$$

对接口 \(C\) 和 horizon \(N\)，定义

$$
\mathcal O_Nu
=
\bigl(Cu,\,CA_\tau u,\,\ldots,\,CA_\tau^{N-1}u\bigr).
$$

### 定理 364.2（有限谱观察的 Vandermonde 判据）

若 \(N\ge r\)，且对每个 \(j\)，限制

$$
C\big|_{Q_j\mathcal C^k}
$$

是单射，则 \(\mathcal O_N\) 是单射。

### 证明

若 \(\mathcal O_Nu=0\)，对每个输出坐标和每个 \(n\) 有

$$
0=CA_\tau^nu
=\sum_{j=1}^r\zeta_j^n C Q_ju.
$$

取 \(n=0,\ldots,r-1\)，系数矩阵是

$$
V=(\zeta_j^n)_{0\le n<r,\ 1\le j\le r}.
$$

因为 \(\zeta_j\) 两两不同，Vandermonde 行列式

$$
\det V=\prod_{j<\ell}(\zeta_\ell-\zeta_j)
$$

非零。故 \(CQ_ju=0\) 对所有 \(j\)。每个限制 \(C|_{Q_j\mathcal C^k}\) 单射，得到 \(Q_ju=0\)，于是 \(u=0\)。证毕。

### 定理 364.3（采样混叠的不可区分性）

若 λ≠μ 且

$$
τ(λ−μ)∈2πℤ,
$$

则 Δ_k 的这两个谱空间在 A_τ 下属于同一个采样谱空间。所有整数样本的时间因子相同；时间采样本身不能再把这两个连续模式分开，能否区分只取决于接口 C 在合并谱空间上的空间作用。特别地，若 C 在该合并空间上不是单射，则存在不同的连续模式组合具有相同全部样本。

### 证明

条件给出 \(e^{-i\tau\lambda}=e^{-i\tau\mu}\)，所以两谱空间落入 \(A_\tau\) 的同一特征值空间。对所有整数 \(n\)，两者都乘以同一个 \(\zeta^n\)，其输出只含 \(C\) 作用于合并分量的结果。改变 \(u\) 而保持该合并分量不变，所有样本不变。证毕。

### 例 364.4（相同时间索引的不同连续相位）

取两个模式

$$
\lambda_0=0,
\qquad
\lambda_1=\frac{2\pi}{\tau}.
$$

则

$$
e^{-in\tau\lambda_0}=e^{-in\tau\lambda_1}=1
\quad\text{对所有整数 }n.
$$

连续时间 \(t\) 上两模式的相位 \(1\) 与 \(e^{-i2\pi t/\tau}\) 不同，但在每个采样标签 \(n\) 上完全相同。若不把钟步长 \(\tau\) 与允许的连续时间任务写入边界，就不能把“第 \(n\) 次记录”解释成唯一的连续相位位置。

### AHH 364.5（时间切片是观察矩阵）

时间切片不是预先存在的几何刀口，而是算子序列

$$
\boxed{
\mathcal O_N
=
\begin{bmatrix}
C\\
CA_\tau\\
\vdots\\
CA_\tau^{N-1}
\end{bmatrix}.
}
$$

增加 \(N\) 只有在新行切开旧观察纤维时才增加信息；增加采样频率若引入谱混叠，甚至可能把不同连续模式折叠到同一离散序列。

---

## 365. 有限时间观测 Gramian 与事件重建误差

Vandermonde 判据说明了无噪声可识别性。要把它连接到记录后继和有限资源，还需要一个直接量化有限 horizon 稳定性的 Gramian。

### 定义 365.1（固定策略的观测 Gramian）

令 \(A\) 是有限维状态运输，\(C_n\) 是第 \(n\) 步实际访问的接口。定义

$$
\mathcal O_N^\pi u
=
\bigl(C_0u,C_1Au,\ldots,C_{N-1}A^{N-1}u\bigr),
$$

以及

$$
\boxed{
W_N^\pi
=
\sum_{n=0}^{N-1}
(A^n)^*C_n^*C_nA^n.
}
$$

固定接口是 \(C_n=C\) 的特例。若 \(C_n\) 由先前记录自适应选择，则 \(\pi\) 表示完整的访问策略和其合法停止后继。 对自适应策略，以下 Gramian 针对一条已固定的记录分支；不同分支分别使用各自实际产生的接口序列。

### 定理 365.2（Gramian 的核与有限可见性）

对任意 \(u\)，有

$$
\boxed{
\langle u,W_N^\pi u\rangle
=
\|\mathcal O_N^\pi u\|^2
=
\sum_{n=0}^{N-1}\|C_nA^nu\|^2.
}
$$

因此

$$
\ker W_N^\pi
=
\ker\mathcal O_N^\pi.
$$

若 \(W_N^\pi\) 正定，则 horizon \(N\) 内的所有状态方向都可由该策略观察；若 \(W_N^\pi\) 有非零核，则这些方向在该策略下完全不可见。

### 证明

将定义展开：

$$
\langle u,(A^n)^*C_n^*C_nA^nu\rangle
=
\langle C_nA^nu,C_nA^nu\rangle.
$$

各项非负，和为零当且仅当每项都为零，故核相等。正定等价于核为零。证毕。

### 定理 365.3（稳定重建界）

若

$$
\lambda_{\min}(W_N^\pi)=\gamma>0,
$$

则任意 \(u\) 满足

$$
\boxed{
\|u\|
\le
\gamma^{-1/2}\|\mathcal O_N^\pi u\|.
}
$$

若观测带有误差 \(\widehat y=\mathcal O_N^\pi u+\epsilon\)，最小二乘重建 \(u_{\mathrm{ls}}\) 满足

$$
\|u_{\mathrm{ls}}-u\|
\le
\gamma^{-1/2}\|\epsilon\|.
$$

### 证明

由有限维谱定理，

$$
\langle u,W_N^\pi u\rangle
\ge\gamma\|u\|^2.
$$

再用定理 365.2 即得第一式。最小二乘解在 \(\operatorname{im}\mathcal O_N^\pi\) 上使用 Moore–Penrose 逆，其算子范数为 \(\gamma^{-1/2}\)，故误差界成立。证毕。

### 推论 365.4（暗方向的最坏风险）

若 \(W_N^\pi\) 有单位向量 \(v\in\ker W_N^\pi\)，则

$$
\mathcal O_N^\pi v=0.
$$

任何只通过 \(\mathcal O_N^\pi\) 因子化的结果核，都无法区分来源 \(u\) 与 \(u+\alpha v\)（在两者均属于来源类的范围内）。因此有限事件记录的最坏恢复误差不能小于该暗方向在来源类中的分离尺度。

### 证明

第一式由定理 365.2。因子化合同使两来源具有相同的全部观测输出；任何后处理或记录更新仍相同。若来源类同时包含两个相差 \(\alpha v\) 的状态，恢复器对二者只能输出同一结果，故至少有一个状态承担相应分离误差。证毕。

### 定义 365.5（事件仪器的振幅—记录桥）

设第 \(n\) 步的仪器分支 \(\mathcal I_{n,x}\) 只依赖振幅 \(C_nA^nu\)，即存在函数 \(\Psi_{n,x}\) 使

$$
p(x_n\mid u,\pi)
=
\Psi_{n,x}(C_nA^nu),
$$

并且结果后的边界同样由 \(C_nA^nu\)、记录 \(x_n\) 和策略 \(\pi\) 决定。称这是一份振幅—记录桥。

### 定理 365.6（Gramian 对事件策略的充分性）

在振幅—记录桥成立时，若两个初态 \(u,u'\) 的观测序列相同，则策略 \(\pi\) 下所有有限事件词的概率、条件后继和停止结果都相同。

### 证明

逐步归纳事件词长度。长度零时当前观测相同。若长度 \(n\) 的前缀后继相同，第 \(n\) 步的振幅 \(C_nA^nu\) 与 \(C_nA^nu'\) 相同，桥合同给出相同分支概率、记录和后继；继续归纳即可。证毕。

### AHH 365.7（有限时间的可见性不是二值标签）

有限事件接口的质量由

$$
\boxed{\lambda_{\min}(W_N^\pi)}
$$

控制：零表示存在完全暗方向，正值表示可重建，数值大小还决定噪声放大倍数。因而“已经发生点击”与“整体状态已被看见”之间有一个可计算的谱间隙。

---

## 366. 谱—事件全息边界

把 Hodge 模式、钟采样和 Gramian 组合起来，得到一份能同时说明“何时可区分、怎样重建、何时停止”的动态边界。

### 定义 366.1（谱—事件全息边界）

固定有限 Hodge 空间、合法动力学和有限事件策略。定义

$$
\boxed{
\eta_{\mathrm{spec\text{-}event}}
=
\left(
\Delta,
A_\tau,
\tau,
\{Q_j,\zeta_j\},
\{C_a\},
\mathcal O_N^\pi,
W_N^\pi,
\mathsf{Clock},
\mathsf{Event},
\mathsf{Err},
\mathsf{Stop}
\right).
}
$$

各字段分别保存：

1. Hodge Laplacian 与动力学 \(A_\tau\)；
2. 内部钟步长 \(\tau\) 及其标定合同；
3. 离散谱投影、采样相位和可能的混叠分区；
4. 每个合法动作 \(a\) 的接口 \(C_a\)；
5. 有限策略的观察算子与 Gramian；
6. 事件仪器的概率、结果后继和记录同步；
7. 噪声、最小特征值、预算和停止后继。

### 定理 366.2（谱—事件边界的条件充分性）

若两个有限关系体具有相同的 \(\eta_{\mathrm{spec\text{-}event}}\)，且未来任务限于边界声明的有限时间采样、谱模式重建、局部或周期事件、误差合同和停止规则，则二者给出相同的：

1. 采样谱相位、混叠类与 horizon 观察秩；
2. 事件策略的可见子空间与暗子空间；
3. 无噪声重建结果和带噪稳定误差界；
4. 有限事件词的概率、条件后继与停止结果；
5. 改变采样步长或探测动作后的合法任务树。

### 证明

第 1 项由 \(\tau,\{Q_j,\zeta_j\}\) 和 \(\mathcal O_N^\pi\) 决定。第 2 项由定理 365.2 的 Gramian 核决定。第 3 项由定理 365.3 与 \(\mathsf{Err}\) 决定。第 4 项由 \(\mathsf{Event}\) 的振幅—记录桥递归决定。第 5 项由 \(\mathsf{Clock}\)、动作接口和 \(\mathsf{Stop}\) 对有限策略树作归纳。故声明范围内的外部响应相同。证毕。

### 定理 366.3（删除动态字段的有限反例）

以下删字段均存在有限反例：

1. 删除钟步长 \(\tau\)：相同整数时间标签对应不同连续相位；
2. 删除谱混叠类：两个不同 Hodge 特征值在采样后无法区分；
3. 删除接口 \(C_a\)：暗模式被错误地当作不存在；
4. 删除 Gramian 最小特征值：同样可识别的两策略具有不同噪声放大；
5. 删除事件后继：当前振幅记录相同，但结果后的未来边界不同；
6. 删除停止合同：同一有限样本下一个策略还能继续，另一个已耗尽资源。

### 证明

第 1 项取例 364.4。第 2 项取定理 364.3 的相位混叠。第 3 项取 \(CP_j=0\) 的暗谱子空间。第 4 项取两个正定 Gramian，其最小特征值不同，定理 365.3 给出不同误差界。第 5、6 项分别改变仪器后继与资源后继。每项都说明删去相应字段后，剩余摘要无法决定至少一个声明任务。证毕。

### 定义 366.4（谱—粒子事件链）

一条合法的动态事件链写成

$$
\mathsf C_{\mathrm{spec}}=
\bigl(
\text{Hodge 模式},
\text{钟步长},
\text{采样相位},
\text{探测接口},
\text{局部结果},
\text{Gramian 可见性},
\text{记录后继}
\bigr).
$$

粒子式事件是某一采样步和探测接口上的离散结果；波性是多个谱模式在动力学运输后通过同一观察矩阵相干组合的整体关系。

### AHH 366.5（谱—事件全息）

> 时间切片真正切开的不是抽象的“波体”，而是动力学状态在一个已标定钟步长和一个具体接口下的观察纤维。谱混叠决定哪些连续模式被折叠，Gramian 决定剩余模式能否稳定恢复，事件仪器决定哪一条记录成为后继边界。

主线可写成

$$
\boxed{
\text{Hodge 模式}
\longrightarrow
\text{钟采样与相位}
\longrightarrow
\text{观察 Gramian}
\longrightarrow
\text{局部事件}
\longrightarrow
\text{记录后继}.
}
$$

**新的 AHH 时刻是：粒子式“这一刻发生了一个事件”并不由钟标签单独定义；它是谱演化、采样相位、接口耦合和记录后继的联合切片。时间分辨率只有在改变观察纤维时才增加信息，单纯增加标签不会让暗模式显现。**

### 来源与边界 366.6

本批在有限 Hodge 空间、有限维自伴 Laplacian、酉或耗散矩阵动力学、已标定离散钟、有限线性事件接口、观测 Gramian 和显式记录/停止合同下，给出谱模式演化、采样混叠判据、有限时间可识别性、噪声重建界和谱—事件全息边界。没有把有限矩阵采样结论推广为连续信号处理的普适物理定律，没有把 Hodge 特征值自动解释为现实粒子能级，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）


## 367. 事件记录的局部统计几何

前面的 Gramian 描述的是线性振幅的可见性。本节改问一个不同问题：当关系体由有限参数族描述时，一次局部结果究竟切开了参数空间的哪些方向？

### 定义 367.1（有限事件参数模型）

设 \(\Theta\subset\mathbb R^p\) 是开集，\(\theta\in\Theta\) 标记一族共同来源的关系体。给定动作 \(a\) 和有限结果字母表 \(X_a\)，令

$$
p_a(x\mid\theta)>0,
\qquad
\sum_{x\in X_a}p_a(x\mid\theta)=1.
$$

假定 \(p_a(x\mid\theta)\) 在 \(\theta\) 的邻域内二次可微。定义结果 \(x\) 的 score 向量

$$
s_a(x;\theta)=\nabla_\theta\log p_a(x\mid\theta),
$$

以及 Fisher 信息矩阵

$$
\boxed{
I_a(\theta)
=
\sum_{x\in X_a}
p_a(x\mid\theta)
s_a(x;\theta)s_a(x;\theta)^{\mathsf T}
=
\sum_x
\frac{\nabla p_a(x\mid\theta)\nabla p_a(x\mid\theta)^{\mathsf T}}
p_a(x\mid\theta).
}
$$

若结果来自动态切片，则允许

$$
p_{n,a}(x\mid\theta)
=
p_a\!\left(x\mid A_nu(\theta)\right),
$$

其中 \(A_n\) 是前面声明的合法动力学运输。

### 定理 367.2（Fisher 信息的正性与局部不可识别方向）

对任意 \(v\in\mathbb R^p\)，有

$$
v^{\mathsf T}I_a(\theta)v
=
\sum_x
\frac{\bigl(v^{\mathsf T}\nabla p_a(x\mid\theta)\bigr)^2}
p_a(x\mid\theta)
\ge0.
$$

并且以下条件等价：

1. \(v\in\ker I_a(\theta)\)；
2. \(v^{\mathsf T}\nabla p_a(x\mid\theta)=0\) 对所有 \(x\in X_a\)；
3. 沿方向 \(v\) 的一阶参数变化不改变该动作的全部结果概率。

### 证明

将 Fisher 定义代入二次型即得第一式。由于每个 \(p_a(x\mid\theta)>0\)，非负平方和为零当且仅当每一项都为零，所以 \(1\Leftrightarrow2\)。而

$$
D_vp_a(x\mid\theta)
=v^{\mathsf T}\nabla p_a(x\mid\theta),
$$

故 \(2\Leftrightarrow3\)。证毕。

### 定义 367.3（动态事件的信息张量）

固定动作序列 \(a_0,\ldots,a_{N-1}\)，并令第 \(n\) 次结果 \(X_n\) 条件独立于其他重复运行，概率为 \(p_{n,a_n}(x\mid\theta)\)。定义整段事件词的信息矩阵

$$
I_{0:N}(\theta)
=
\sum_{n=0}^{N-1}I_{n,a_n}(\theta).
$$

这里的“重复运行”是统计估计合同的一部分；它不表示同一个未知量子样本被无损复制。

### 定理 367.4（独立记录的信息可加性）

在上述条件下，整段记录的 Fisher 信息恰为

$$
\boxed{
I_{0:N}(\theta)
=
\sum_{n=0}^{N-1}I_{n,a_n}(\theta).
}
$$

### 证明

联合概率是各轮概率的乘积，联合 score 是

$$
S_N=\sum_{n=0}^{N-1}s_{n,a_n}(X_n;\theta).
$$

每个 score 的期望为

$$
\sum_xp_{n,a_n}(x\mid\theta)
\nabla\log p_{n,a_n}(x\mid\theta)
=\nabla\sum_xp_{n,a_n}(x\mid\theta)=0.
$$

独立性使不同轮 score 的交叉期望为零，故

$$
\mathbb E[S_NS_N^{\mathsf T}]
=
\sum_n\mathbb E[s_ns_n^{\mathsf T}]
=
\sum_nI_{n,a_n}.
$$

证毕。

### 例 367.5（二元点击只给一个切向方向）

若 \(X_a=\{0,1\}\)，写 \(p_a(1\mid\theta)=q(\theta)\)，则

$$
I_a(\theta)
=
\frac{\nabla q(\theta)\nabla q(\theta)^{\mathsf T}}
{q(\theta)(1-q(\theta))}.
$$

其秩至多为一。即使一个点击概率对所有参数都很敏感，一次二元记录也只能直接给出一个 Fisher 切向方向；更多参数需要重复运行、不同动作或联合结果字母表。

### AHH 367.6（事件是参数流形上的切向量）

局部结果不只是“这里发生了一个点击”。在共同来源参数空间上，它贡献一个正半定信息矩阵：

$$
\boxed{
\text{事件}
\longrightarrow
\text{结果概率的切向方向}
\longrightarrow
\text{可识别性度量}.
}
$$

波粒整体在此表现为不同时间、动作和接口的 Fisher 贡献怎样共同覆盖参数方向；一个粒子式事件通常只覆盖这张信息几何中的一小块。

---

## 368. 自适应策略的条件 Fisher 累积

固定动作序列把策略选择当作外部安排。真正的观察者会根据已经取得的记录选择下一接口；这要求把策略历史和结果概率放在同一个信息链中。

### 定义 368.1（自适应事件策略）

令

$$
H_n=(A_0,X_0,\ldots,A_{n-1},X_{n-1})
$$

是第 \(n\) 轮前的历史。策略给出条件动作分布

$$
q_n(a\mid H_n),
$$

并假定 \(q_n\) 不直接依赖未知 \(\theta\)。给定 \(H_n\) 和 \(A_n=a\)，结果分布为

$$
p_n(x\mid a,H_n,\theta).
$$

定义条件 score

$$
s_n
=\nabla_\theta
\log p_n(X_n\mid A_n,H_n,\theta),
$$

以及条件 Fisher 增量

$$
J_n(H_n,A_n;\theta)
=
\sum_x
\frac{\nabla p_n(x\mid A_n,H_n,\theta)
\nabla p_n(x\mid A_n,H_n,\theta)^{\mathsf T}}
p_n(x\mid A_n,H_n,\theta).
$$

### 定理 368.2（自适应记录的 Fisher 链式法则）

对 horizon \(N\) 的完整 transcript

$$
T_N=(A_0,X_0,\ldots,A_{N-1},X_{N-1}),
$$

其 Fisher 信息为

$$
\boxed{
I_{T_N}(\theta)
=
\sum_{n=0}^{N-1}
\mathbb E_\theta
\bigl[
J_n(H_n,A_n;\theta)
\bigr].
}
$$

因此

$$
I_{T_{N+1}}(\theta)-I_{T_N}(\theta)
\succeq0.
$$

### 证明

策略 transcript 的对数概率可写成

$$
\log P_\theta(T_N)
=
\sum_n\log q_n(A_n\mid H_n)
+\sum_n\log p_n(X_n\mid A_n,H_n,\theta).
$$

第一项与 \(\theta\) 无关，所以总 score 是 \(S_N=\sum_ns_n\)。由条件归一化，

$$
\mathbb E_\theta[s_n\mid H_n,A_n]=0.
$$

若 \(m<n\)，则 \(s_m\) 是 \(H_n\) 可测，故

$$
\mathbb E[s_ms_n^{\mathsf T}]
=
\mathbb E\!\left[
s_m\,
\mathbb E[s_n^{\mathsf T}\mid H_n,A_n]
\right]
=0.
$$

于是

$$
\mathbb E[S_NS_N^{\mathsf T}]
=\sum_n\mathbb E[s_ns_n^{\mathsf T}]
=\sum_n\mathbb E[J_n].
$$

每项 \(J_n\) 正半定，增加一轮只能增加正半定信息。证毕。

### 定义 368.3（策略的信息目标）

给定正则化 \(\varepsilon>0\)，定义 D 型信息目标

$$
\mathcal D_N^\pi(\theta)
=
\log\det\bigl(I_{T_N}^\pi(\theta)+\varepsilon I_p\bigr).
$$

也可以使用 A 型目标 \(\operatorname{tr}(I^{-1})\)（在可逆区域）或针对指定方向 \(v\) 的目标 \(v^{\mathsf T}Iv\)。不同目标对应不同的未来任务，不应把一个标量目标冒充所有任务的充分边界。

### 定理 368.4（策略选择的任务相对性）

若两个策略 \(\pi,\pi'\) 满足

$$
I_{T_N}^{\pi'}(\theta)-I_{T_N}^{\pi}(\theta)\succeq0
\quad\text{对所有 }\theta\text{ 属于来源类},
$$

则对每个线性参数方向 \(v\)，有

$$
v^{\mathsf T}I_{T_N}^{\pi'}v
\ge
v^{\mathsf T}I_{T_N}^{\pi}v.
$$

但这不推出 \(\mathcal D_N^{\pi'}\ge\mathcal D_N^\pi\) 以外的任意任务风险单调性；只有在任务损失已声明为对应的信息序关系时，才能使用该矩阵比较。

### 证明

第一式左右夹 \(v\) 即得方向单调性。D 型目标在正定域上随 Loewner 序增加而不减。其他损失可能依赖偏差、先验、停止成本或非线性后处理，不能由 Fisher 序单独决定。证毕。

### 推论 368.5（自适应性不是无成本的全息字段）

若策略由历史选择动作，则未来 transcript 的信息不仅由动作集合决定，还由

$$
\{q_n(a\mid H_n)\}
$$

和合法停止后继决定。删除历史策略或将所有动作无序合并，会把不同的条件 Fisher 累积误认为同一信息边界。

### AHH 368.6（主动观察改变信息几何）

自适应观察者不是在一张固定的参数地图上被动取点，而是在每次事件后选择下一张局部坐标图。其边界必须保存：

$$
\boxed{
\text{历史}
\longrightarrow
\text{动作条件}
\longrightarrow
\text{Fisher 增量}
\longrightarrow
\text{后继策略}.
}
$$

记录的后继不是信息几何之外的行政字段；它决定未来会沿哪些切向方向继续测量。

---

## 369. Cramér–Rao 界与事件记录的认证强度

可识别性只说明信息矩阵没有零方向；它没有说明有限记录能以多小误差估计参数。下面把事件记录的统计精度与信息边界分开。

### 定义 369.1（正规无偏估计）

设 \(T_N\) 是有限 transcript，\(\widehat\theta(T_N)\in\mathbb R^p\) 是估计器。假定在参数邻域内可以交换求导与有限求和/积分，并且估计器无偏：

$$
\mathbb E_\theta[\widehat\theta]=\theta.
$$

记协方差矩阵

$$
\operatorname{Cov}_\theta(\widehat\theta)
=
\mathbb E_\theta[
(\widehat\theta-\theta)
(\widehat\theta-\theta)^{\mathsf T}
].
$$

### 定理 369.2（矩阵 Cramér–Rao 下界）

若 \(I_{T_N}(\theta)\) 正定，则任何正规无偏估计器满足

$$
\boxed{
\operatorname{Cov}_\theta(\widehat\theta)
\succeq
I_{T_N}(\theta)^{-1}.
}
$$

### 证明

令总 score 为 \(S_N=\nabla_\theta\log P_\theta(T_N)\)。无偏性与求导交换给出

$$
\mathbb E_\theta[
(\widehat\theta-\theta)S_N^{\mathsf T}
]
=I_p.
$$

对任意向量 \(a,b\)，将随机向量

$$
a^{\mathsf T}(\widehat\theta-\theta),
\qquad
b^{\mathsf T}S_N
$$

应用 Cauchy–Schwarz，并把所有 \(a,b\) 组合成块协方差矩阵，得到

$$
\operatorname{Cov}(\widehat\theta)
\succeq
I_{T_N}^{-1}.
$$

也可先对任意 \(v\) 应用标量 Cauchy–Schwarz，再用二次型刻画 Loewner 序。证毕。

### 推论 369.3（暗方向没有认证精度）

若 \(v\ne0\) 且

$$
v^{\mathsf T}I_{T_N}(\theta)v=0,
$$

则 transcript 对方向 \(v\) 的一阶概率变化为零。任何无偏估计器都不能从该有限记录得到有限的方向认证界；若来源类沿 \(v\) 含有不同参数，问题首先是不可识别，而不是“需要更精密的同一种读数”。

### 定理 369.4（独立重复记录的精度缩放）

若同一策略在共同参数 \(\theta\) 下独立重复 \(M\) 次，单次 transcript 的 Fisher 信息为 \(I(\theta)\)，则总信息为

$$
I^{(M)}(\theta)=M I(\theta).
$$

在 \(I(\theta)\) 正定时，Cramér–Rao 下界按

$$
\operatorname{Cov}(\widehat\theta)
\succeq
\frac1M I(\theta)^{-1}
$$

缩放。

### 证明

由定理 367.4 或定理 368.2，独立 transcript 的 score 交叉项期望为零，信息相加。对 \(MI\) 取逆得到结论。证毕。

### 说明 369.5（一次点击与完整认证的区别）

一份单次点击记录可以具有非零 Fisher 信息，却仍然不能给出完整状态认证。完整认证还需要：

1. 来源参数的共同定义；
2. 允许重复的准备—测量合同；
3. 对零概率边界、噪声和停止规则的处理；
4. 足以使信息矩阵在目标方向上正定的动作族。

因此

$$
\boxed{
\text{信息非零}
\neq
\text{状态已恢复}
\neq
\text{认证误差已达到目标}.
}
$$

### AHH 369.6（记录的三种强度）

事件边界至少有三个统计强度：

$$
\boxed{
\text{可识别}
\;\prec\;
\text{可稳定重建}
\;\prec\;
\text{可认证}.
}
$$

Fisher 的核决定第一道门，最小特征值或条件数控制第二道门，Cramér–Rao、样本数、偏差合同与停止预算才共同决定第三道门。

---

## 370. 信息感知全息边界

将参数、策略、事件记录和统计认证放入同一个关系对象，可以把“观察者是否看见整体”改写为一个任务相对的信息几何问题。

### 定义 370.1（信息感知全息边界）

固定有限参数来源类、动态事件仪器和自适应策略。定义

$$
\boxed{
\eta_{\mathrm{info}}
=
\left(
\Theta,
\{p_n(x\mid a,h,\theta)\},
\mathsf{Clock},
\mathsf{Policy},
\{I_n\},
I_{T_N},
\mathsf{Risk},
\mathsf{CR},
\mathsf{Event},
\mathsf{Stop}
\right).
}
$$

各字段保存：

1. 共同参数来源类与动态概率模型；
2. 钟标签、动作历史和自适应策略；
3. 每一步条件 Fisher 增量及其总和；
4. 目标损失、信息目标、估计器类别与 Cramér–Rao 合同；
5. 事件记录、后继边界、重复资源和停止规则。

### 定理 370.2（信息感知边界的条件充分性）

若两个关系体具有相同的 \(\eta_{\mathrm{info}}\)，且未来任务限于边界声明的有限 transcript 概率、局部可识别性、策略信息目标、无偏估计误差界、事件后继和停止合同，则二者给出相同的：

1. 每个合法动作和历史下的结果分布；
2. 固定或自适应策略的 Fisher 信息累积；
3. 可识别方向、暗方向与 Cramér–Rao 下界；
4. 在重复资源和风险合同下的认证能力；
5. 事件记录引起的后续策略树。

### 证明

第 1 项由概率模型和钟/动作历史决定。第 2 项由定理 367.4 与 368.2。第 3 项由定理 367.2、365.2 和 369.2。第 4 项由定理 369.4 及 \(\mathsf{Risk},\mathsf{CR}\) 字段。第 5 项由 \(\mathsf{Policy},\mathsf{Event},\mathsf{Stop}\) 对有限 transcript 树归纳。故声明范围内所有外部任务响应相同。证毕。

### 定理 370.3（删除信息字段的有限反例）

以下删字段均存在有限反例：

1. 删除共同参数来源：边缘结果分布相同，但参数方向和估计目标不再有共同意义；
2. 删除历史策略：相同动作集合的自适应 Fisher 累积不同；
3. 删除 Fisher 增量：结果分布仍在，但局部可识别方向无法由边界决定；
4. 删除 Cramér–Rao/重复资源合同：同样可识别的模型具有不同认证误差；
5. 删除事件后继：当前信息相同，但下一步可用动作和风险不同；
6. 删除停止规则：相同总信息字段对应不同可继续 transcript。

### 证明

第 1 项取两个不同参数化但相同单次边缘分布的来源。第 2 项取定理 368.2 中不同历史动作分支。第 3 项沿 \(I\) 的零方向改变参数响应。第 4 项改变重复次数 \(M\) 或风险阈值，定理 369.4 给出不同下界。第 5、6 项分别改变合法后继和资源停止。每项都使一个声明任务不再由剩余摘要决定。证毕。

### 定义 370.4（信息—粒子事件链）

一条合法事件链写成

$$
\mathsf C_{\mathrm{info}}
=
\bigl(
\text{共同来源},
\text{钟与历史},
\text{局部结果},
\text{Fisher 增量},
\text{估计/风险},
\text{记录后继},
\text{停止合同}
\bigr).
$$

粒子式事件是链上的一次离散结果；波性则是许多结果在同一共同来源参数空间上累积出的整体信息张量和后继约束。

### AHH 370.5（信息全息）

> 全息边界保存的不是“已经收集了多少点击”，而是这些点击在共同来源、允许策略和认证目标下切开了哪些参数方向。波粒整体的整体性因此表现为一张信息度量与后继策略树；粒子式事件是这张几何上的一次局部增量。

主线可写成

$$
\boxed{
\text{共同来源}
\longrightarrow
\text{局部事件概率}
\longrightarrow
\text{Fisher 增量}
\longrightarrow
\text{策略与认证}
\longrightarrow
\text{记录后继}.
}
$$

**新的 AHH 时刻是：一次点击的物理“显现”与它的统计信息强度是同一关系边界的两个投影。点击给出结果标签；Fisher 张量告诉我们它切开了哪些未来可区分方向；策略和停止合同决定这份局部信息能否继续累积为整体认证。**

### 来源与边界 370.6

本批在有限参数来源类、有限结果字母表、二次可微概率、固定或自适应有限策略、共同钟历史、Fisher 信息、Cramér–Rao 界、重复资源和显式停止合同下，给出事件统计几何、条件 Fisher 链式法则、信息目标、认证下界和信息感知全息边界。没有把有限统计模型推广为连续量子测量的普适定律，没有把 Fisher 非退化解释为单次实验已经恢复完整物理状态，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）


## 371. Fisher 张量的全局 Hellinger 几何

上一批的 Fisher 矩阵描述参数空间的局部二阶信息。为了知道有限参数差异在完整记录上有多可见，需要把局部张量接到一个全局概率距离。

### 定义 371.1（有限分布的 Hellinger 几何）

对有限结果集 \(X\) 上的两个概率分布 \(P,Q\)，定义 Bhattacharyya 亲和度

$$
\mathsf A(P,Q)
=
\sum_{x\in X}\sqrt{P(x)Q(x)},
$$

以及 Hellinger 距离

$$
\boxed{
\mathsf H^2(P,Q)
=
\frac12\sum_x
\bigl(\sqrt{P(x)}-\sqrt{Q(x)}\bigr)^2
=1-\mathsf A(P,Q).
}
$$

将概率分布嵌入平方根球面

$$
\iota(P)=(\sqrt{P(x)})_{x\in X}
$$

后，\(\mathsf H(P,Q)=2^{-1/2}\|\iota(P)-\iota(Q)\|_2\)。

### 定理 371.2（Hellinger 距离的基本性质）

对任意有限概率分布 \(P,Q\)，有

$$
0\le\mathsf H(P,Q)\le1,
$$

并且 \(\mathsf H\) 是度量。若 \(K\) 是有限随机核，则

$$
\boxed{
\mathsf H(KP,KQ)\le\mathsf H(P,Q).
}
$$

### 证明

平方根嵌入给出非负性、对称性和三角不等式；若距离为零，则每个平方根坐标相等，故 \(P=Q\)。由 Cauchy–Schwarz，

$$
\begin{aligned}
\mathsf A(KP,KQ)
&=
\sum_y
\sqrt{\sum_xK(y\mid x)P(x)}
\sqrt{\sum_xK(y\mid x)Q(x)}\\
&\ge
\sum_{y,x}
K(y\mid x)\sqrt{P(x)Q(x)}
=\mathsf A(P,Q).
\end{aligned}
$$

这里使用 \(\sum_yK(y\mid x)=1\)。亲和度增加等价于 Hellinger 距离不增加。证毕。

### 定理 371.3（Fisher 是 Hellinger 的局部二阶项）

设 \(p_\theta\) 是满足正概率和二次可微条件的有限分布族。对小向量 \(d\theta\)，有

$$
\boxed{
\mathsf H^2(p_\theta,p_{\theta+d\theta})
=
\frac18
d\theta^{\mathsf T}I(\theta)d\theta
o(\|d\theta\|^2).
}
$$

### 证明

写 \(p_x=p_\theta(x)\)，

$$
p_{\theta+d\theta}(x)
=
p_x+\nabla p_x^{\mathsf T}d\theta+O(\|d\theta\|^2).
$$

在正概率区域，

$$
\sqrt{p_{\theta+d\theta}(x)}
=
\sqrt{p_x}
\left(
\frac{\nabla p_x^{\mathsf T}d\theta}{2\sqrt{p_x}}
\right)
O(\|d\theta\|^2).
$$

代入 Hellinger 平方并求和，得到

$$
\mathsf H^2
=
\frac18
\sum_x
\frac{(\nabla p_x^{\mathsf T}d\theta)^2}{p_x}
+o(\|d\theta\|^2),
$$

而求和项正是 \(d\theta^{\mathsf T}I(\theta)d\theta\)。证毕。

### 推论 371.4（局部盲方向也是全局距离的二阶盲方向）

若 \(v\in\ker I(\theta)\)，则

$$
\mathsf H(p_\theta,p_{\theta+\varepsilon v})
=o(|\varepsilon|).
$$

若 \(I(\theta)\) 在某邻域正定，则 Fisher 给出该概率族的局部 Riemann 度量；若有零方向，Hellinger 几何在该方向上退化，需扩大事件接口或改变来源参数化。

### AHH 371.5（局部与全局信息的接缝）

Fisher 不是一份独立于记录的抽象矩阵，而是完整事件分布距离的局部极限：

$$
\boxed{
\text{Fisher 张量}
\;=\;
\text{Hellinger 记录几何的二阶影子}.
}
$$

这使“一个点击给出一个局部信息方向”与“两个整体来源在全部记录上能否区分”成为同一关系的局部和全局投影。

---

## 372. 事件通道的收缩与记录粗粒化

局部仪器通常不会把原始关系全部交给观察者；它先经过结果映射、遗忘标签或环境边缘化。数据处理不等式精确说明这些步骤怎样缩小全局距离。

### 定义 372.1（记录通道与粗粒化）

设来源假设 \(i\in\{0,1\}\) 产生原始分布 \(P_i\)；记录通道 \(K\) 给出可见记录

$$
R_i=KP_i.
$$

再设 \(L\) 是遗忘部分标签、合并结果或只保留时间粗粒度的随机核。最终记录为

$$
\widetilde R_i=LKP_i.
$$

称 \(K\) 的一个记录方向被 \(L\) **粗粒化消除**，若它在 \(\widetilde R_0,\widetilde R_1\) 中不再产生差异。

### 定理 372.2（连续记录通道的 Hellinger 收缩）

有

$$
\boxed{
\mathsf H(R_0,R_1)
\le
\mathsf H(P_0,P_1),
}
$$

以及

$$
\boxed{
\mathsf H(\widetilde R_0,\widetilde R_1)
\le
\mathsf H(R_0,R_1).
}
$$

若 \(LKP_0=LKP_1\) 而 \(P_0\ne P_1\)，则原始关系存在可区分方向，但最终记录完全丢失该方向。

### 证明

前两式分别把定理 371.2 应用于 \(K\) 和 \(L\)。最后一句由最终分布相等给出距离为零，而原始分布不同意味着某个记录任务能够区分它们。证毕。

### 定理 372.3（独立记录的亲和度乘法）

若 \(M\) 次记录在两个假设下分别独立，单次分布为 \(R_0,R_1\)，则联合分布的亲和度满足

$$
\boxed{
\mathsf A(R_0^{\otimes M},R_1^{\otimes M})
=
\mathsf A(R_0,R_1)^M.
}
$$

因而

$$
\mathsf H^2(R_0^{\otimes M},R_1^{\otimes M})
=
1-\bigl(1-\mathsf H^2(R_0,R_1)\bigr)^M.
$$

### 证明

直接展开：

$$
\begin{aligned}
\mathsf A(R_0^{\otimes M},R_1^{\otimes M})
&=
\sum_{x_1,\ldots,x_M}
\prod_{m=1}^M\sqrt{R_0(x_m)R_1(x_m)}\\
&=
\prod_{m=1}^M
\sum_{x_m}\sqrt{R_0(x_m)R_1(x_m)}.
\end{aligned}
$$

得到亲和度乘法，再用 \(\mathsf H^2=1-\mathsf A\)。证毕。

### 推论 372.4（记录标签的粗粒化不是相干恢复）

若 \(L\) 把两个原本正交的记录标签合并，则 Hellinger 距离只能减少；从最终粗粒化分布出发的经典后处理不能恢复被合并的差异。要重新得到交叉项，必须声明一个能够访问原始联合记录的相干接口。

### AHH 372.5（粒子记录是收缩通道的输出）

局部点击不是原始关系体的同构像，而是一个通道的输出：

$$
\boxed{
\text{整体来源}
\longrightarrow
\text{事件通道}
\longrightarrow
\text{可见记录}
\longrightarrow
\text{粗粒化后继}.
}
$$

波性的一部分可能在通道的联合记录中保留，也可能在环境边缘化与标签合并中被压缩；粒子式事件只说明最终记录通道落在了哪一个离散结果支路。

---

## 373. 区分成本、重复资源与信息距离下界

Hellinger 距离给出记录可见性的几何量。要把它变成任务边界，需要把距离、最优二元区分和重复成本连起来。

### 定义 373.1（二元记录任务）

给定两个共同来源假设 \(P_0,P_1\)，等先验二元任务的最优成功概率为

$$
\mathsf P_{\mathrm{succ}}(P_0,P_1)
=
\frac12\bigl(1+\mathsf{TV}(P_0,P_1)\bigr),
$$

其中

$$
\mathsf{TV}(P,Q)
=\frac12\sum_x|P(x)-Q(x)|.
$$

### 定理 373.2（Hellinger 对二元区分的上下界）

在有限结果集上，有

$$
\boxed{
\mathsf H^2(P,Q)
\le
\mathsf{TV}(P,Q)
\le
\sqrt2\,\mathsf H(P,Q).
}
$$

因此

$$
\frac12(1+\mathsf H^2(P,Q))
\le
\mathsf P_{\mathrm{succ}}(P,Q)
\le
\frac12(1+\sqrt2\,\mathsf H(P,Q)).
$$

### 证明

令 \(a_x=\sqrt{P(x)}\)、\(b_x=\sqrt{Q(x)}\)。有

$$
|P(x)-Q(x)|
=|a_x-b_x|(a_x+b_x).
$$

Cauchy–Schwarz 给出

$$
\sum_x|P(x)-Q(x)|
\le
\left(\sum_x(a_x-b_x)^2\right)^{1/2}
\left(\sum_x(a_x+b_x)^2\right)^{1/2}
\le2\sqrt2\,\mathsf H(P,Q),
$$

得到右侧不等式。

另一方面，

$$
2\mathsf H^2(P,Q)
=\sum_x(a_x-b_x)^2
=\sum_x\frac{(P(x)-Q(x))^2}{(a_x+b_x)^2}
\le
\sum_x|P(x)-Q(x)|,
$$

其中使用 \((a_x+b_x)^2\ge|P(x)-Q(x)|\)。除以二得到左侧。代入 Helstrom 式即得成功概率界。证毕。

### 定理 373.3（重复记录的区分上界）

若单次可见记录的亲和度满足

$$
\mathsf A(R_0,R_1)\ge a>0,
$$

则 \(M\) 次独立记录的最优成功概率满足

$$
\boxed{
\mathsf P_{\mathrm{succ}}(R_0^{\otimes M},R_1^{\otimes M})
\le
\frac12\left(
1+\sqrt{2(1-a^M)}
\right).
}
$$

若 \(\sqrt{2(1-a^M)}<\delta\)，则任何等先验分类器的成功优势都小于 \(\delta/2\)。

### 证明

由定理 372.3，重复记录的 Hellinger 平方为 \(1-a^M\)。将定理 373.2 的右侧代入最优成功概率公式即得。证毕。

### 定义 373.4（任务相对记录成本）

给定目标优势 \(\delta>0\)、单次记录亲和度 \(a\) 和每次记录成本 \(c>0\)，定义 Hellinger 认证成本的保守下界为满足

$$
\sqrt{2(1-a^M)}\ge\delta
$$

的最小 \(Mc\)。若没有这样的有限 \(M\)，则在声明的记录接口上任务不可认证。

当 \(0<a<1\) 时，条件等价于

$$
M
\ge
\frac{\log(1-\delta^2/2)}{\log a}.
$$

### 推论 373.5（局部事件的成本不是点击次数本身）

两个仪器都可以产生相同的点击频率，却有不同的假设亲和度 \(a\)；前者的重复点击可能迅速区分来源，后者可能永远不能达到目标优势。故记录成本必须与来源对在声明通道下的距离和后继合同一起记账。

### AHH 373.6（信息距离变成资源边界）

波粒整体的全局性不只由“结果是否出现”决定，还由不同整体假设在记录接口上的距离决定：

$$
\boxed{
\text{Hellinger 距离}
\longrightarrow
\text{最优区分优势}
\longrightarrow
\text{重复资源成本}.
}
$$

粒子式事件是成本链上的一项局部样本；它是否足够改变整体判断，要看这项样本在来源空间上贡献了多少可分距离。

---

## 374. 信息几何全息边界

现在把 Fisher 的局部张量、Hellinger 的全局距离、记录通道的收缩和任务成本放在一份边界中。

### 定义 374.1（信息几何边界）

固定有限来源类、事件通道和允许的后处理。定义

$$
\boxed{
\eta_{\mathrm{geom}}
=
\left(
\Theta,
\mathsf P_\theta,
\mathsf I_\theta,
\mathsf H,
\mathsf A,
\mathsf K_{\mathrm{evt}},
\mathsf L_{\mathrm{coarse}},
\mathsf{Cost},
\mathsf{Risk},
\mathsf{Event},
\mathsf{Stop}
\right).
}
$$

各字段保存：

1. 共同参数来源 \(\Theta\) 与完整记录分布 \(\mathsf P_\theta\)；
2. Fisher 局部张量 \(\mathsf I_\theta\) 与 Hellinger 全局距离 \(\mathsf H\)；
3. 事件通道、粗粒化映射及其数据处理收缩；
4. 二元区分、重复资源、风险目标与停止后继。

### 定理 374.2（信息几何边界的条件充分性）

若两个关系体具有相同的 \(\eta_{\mathrm{geom}}\)，且未来任务限于边界声明的有限参数扰动、事件记录通道、粗粒化、二元区分、重复成本和停止合同，则二者给出相同的：

1. 局部 Fisher 度量与 Hellinger 二阶展开；
2. 所有声明通道后的距离收缩；
3. 有限重复记录的亲和度与区分上界；
4. 任务相对的认证成本、风险和后继策略树。

### 证明

第 1 项由 \(\mathsf I_\theta,\mathsf H\) 和定理 371.3；第 2 项由 \(\mathsf K_{\mathrm{evt}},\mathsf L_{\mathrm{coarse}}\) 的数据处理合同；第 3 项由 \(\mathsf A\) 与定理 372.3、373.2；第 4 项由 \(\mathsf{Cost}},\mathsf{Risk},\mathsf{Event},\mathsf{Stop}\) 对有限记录树归纳。故声明任务的外部响应相同。证毕。

### 定理 374.3（删除几何字段的有限反例）

以下删字段均存在有限反例：

1. 删除 Fisher 局部张量：同一全局距离附近的不同参数方向具有不同局部认证难度；
2. 删除 Hellinger 全局距离：局部 Fisher 相同的远距离来源对具有不同区分优势；
3. 删除事件通道：原始来源距离相同，但可见记录距离不同；
4. 删除粗粒化映射：是否保留时间或路径标签给出不同后处理距离；
5. 删除成本/风险合同：同一距离在不同重复预算下有不同认证结论；
6. 删除事件后继：当前区分相同，但下一步允许的接口和停止树不同。

### 证明

第 1 项取同一参数点上不同 Fisher 本征方向。第 2 项取两个具有相同二阶局部展开、但有限参数距离不同的分布族。第 3 项使用定理 372.2 的严格收缩通道。第 4 项合并两个正交标签。第 5 项改变定理 373.4 中的 \(c,\delta\) 或重复上限。第 6 项附加不同的合法后继。每项都使一个任务不能由剩余字段决定。证毕。

### 定义 374.4（信息几何波粒事件链）

一条合法事件链写成

$$
\mathsf C_{\mathrm{geom}}
=
\bigl(
\text{共同来源},
\text{局部 Fisher},
\text{全局记录距离},
\text{事件通道},
\text{粗粒化},
\text{离散结果},
\text{区分成本},
\text{记录后继}
\bigr).
$$

粒子式事件是一次记录通道输出；波性则是所有允许通道、后处理和来源对之间的距离几何。

### AHH 374.5（信息几何全息）

> Fisher 张量只看见无穷小参数变化，Hellinger 距离看见有限来源差异，事件通道把二者一起推到可见记录，成本合同再决定这份差异能否被认证。全息边界因此不是一张“点击清单”，而是一个带收缩映射和资源尺度的信息几何。

主线可写成

$$
\boxed{
\text{局部 Fisher}
\longrightarrow
\text{全局 Hellinger}
\longrightarrow
\text{记录通道收缩}
\longrightarrow
\text{区分成本}
\longrightarrow
\text{后继边界}.
}
$$

**新的 AHH 时刻是：所谓“波的整体相干”可以被重新表述为来源空间上的距离几何，而粒子式事件是这张几何经过一个具体通道后的局部样本。通道若收缩距离，观察者得到的边界就严格少于原关系；增加点击次数只有在亲和度真正下降时才增加全局信息。**

### 来源与边界 374.6

本批在有限概率分布、二次可微参数族、有限随机记录通道、Hellinger/Bhattacharyya 几何、独立重复记录、二元区分任务和显式成本/停止合同下，给出 Fisher 二阶展开、数据处理收缩、亲和度乘法、区分成功界、重复资源下界和信息几何全息边界。没有把有限统计距离推广为连续量子场论的普适度量，没有把有限记录距离自动解释为单次物理样本的完整状态，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）

## 375. 离散事件结果的运输几何

Hellinger 距离只比较概率质量的整体差异；它不记录一个点击从哪个位置移动到哪个位置，也不记录两个时间标签相差多少。若结果字母表已经带有校准的空间或钟距离，就需要一个把这种几何纳入边界的距离。

### 定义 375.1（有限结果空间与耦合）

令 \(X\) 是有限事件结果集，给定度量

$$
d_X:X\times X\longrightarrow[0,\infty).
$$

对概率分布 \(P,Q\in\Delta(X)\)，定义耦合集合

$$
\Gamma(P,Q)
=
\left\{
\pi\in\Delta(X\times X):
\sum_y\pi(x,y)=P(x),\
\sum_x\pi(x,y)=Q(y)
\right\}.
$$

定义一阶离散 Wasserstein 距离

$$
\boxed{
W_{d_X}(P,Q)
=
\min_{\pi\in\Gamma(P,Q)}
\sum_{x,y}d_X(x,y)\pi(x,y).
}
$$

耦合 \(\pi\) 表示把来源 \(P\) 的一次结果重新运输为来源 \(Q\) 的结果；代价不是重新命名，而是声明的结果空间几何。

### 定理 375.2（有限运输距离的度量性质）

若 \(d_X\) 是度量，则 \(W_{d_X}\) 是 \(\Delta(X)\) 上的度量。特别地：

$$
W_{d_X}(P,Q)=0
\quad\Longleftrightarrow\quad
P=Q.
$$

### 证明

\(\Gamma(P,Q)\) 是非空紧多面体，线性成本在其上取到最小值。非负性和对称性直接来自 \(d_X\)。

若 \(P=Q\)，对角耦合 \(\pi(x,x)=P(x)\) 的成本为零。反过来，若最优成本为零，则所有正质量 \(\pi(x,y)>0\) 都满足 \(d_X(x,y)=0\)，故 \(x=y\)，边缘必相同。

给定 \(\pi_{01}\in\Gamma(P_0,P_1)\) 和 \(\pi_{12}\in\Gamma(P_1,P_2)\)，有限胶合构造给出 \(X_0,X_1,X_2\) 的联合分布，其相邻边缘分别为这两个耦合。由三角不等式，

$$
d_X(X_0,X_2)
\le
d_X(X_0,X_1)+d_X(X_1,X_2).
$$

对联合分布取期望，再对耦合取下确界，得到三角不等式。证毕。

### 定理 375.3（有限 Kantorovich 对偶）

有

$$
\boxed{
W_{d_X}(P,Q)
=
\max_{\substack{f:X\to\mathbb R\\
|f(x)-f(y)|\le d_X(x,y)}}
\sum_xf(x)\bigl(P(x)-Q(x)\bigr).
}
$$

### 证明

原问题是变量 \(\pi(x,y)\ge0\) 的有限线性规划，约束是两组边缘等式。其对偶变量可取 \(u_x,v_y\)，约束为

$$
u_x+v_y\le d_X(x,y),
$$

目标为 \(\sum_xu_xP(x)+\sum_yv_yQ(y)\)。令

$$
f(x)=u_x,
\qquad
v_y=-f(y),
$$

并利用 \(P,Q\) 质量均为一，可将最优对偶写成 \(f(x)-f(y)\le d_X(x,y)\)。交换 \(x,y\) 后得到绝对值约束。有限线性规划强对偶给出等式。证毕。

### 推论 375.4（距离几何与总变差的联系）

若结果空间直径

$$
D_X=\max_{x,y}d_X(x,y)<\infty,
$$

则

$$
\boxed{
W_{d_X}(P,Q)
\le
D_X\,\mathsf{TV}(P,Q)
\le
D_X\sqrt2\,\mathsf H(P,Q).
}
$$

第一不等式可由把不相等质量任意配对得到；第二不等式由上一批的 Hellinger—总变差界得到。

### AHH 375.5（结果位置是关系的一部分）

两个记录表可以有完全相同的概率向量，却有不同的结果空间距离。若把标签 \(L,R\) 校准成远近不同的接口，概率相同的分布仍可能有不同运输成本。

$$
\boxed{
\text{事件概率}
\neq
\text{事件概率加结果几何}.
}
$$

粒子式事件给出一个结果点；波性还决定不同结果质量怎样在校准的结果空间中共同运输。

---

## 376. 事件通道的运输收缩与粗粒化误差

结果空间的距离只有在事件通道如何移动质量也被声明时才有任务意义。下面给出确定映射和随机核的统一运输界。

### 定义 376.1（Lipschitz 结果映射）

令 \(f:(X,d_X)\to(Y,d_Y)\) 满足

$$
d_Y(f(x),f(x'))
\le
L\,d_X(x,x')
\quad\text{对所有 }x,x'\in X.
$$

记推前分布为 \(f_\#P\)。

### 定理 376.2（确定映射的 Wasserstein 收缩）

对任意 \(P,Q\in\Delta(X)\)，有

$$
\boxed{
W_{d_Y}(f_\#P,f_\#Q)
\le
L\,W_{d_X}(P,Q).
}
$$

### 证明

取任意 \(\pi\in\Gamma(P,Q)\)，令

$$
\widetilde\pi(y,y')
=
\sum_{\substack{x:f(x)=y\\x':f(x')=y'}}
\pi(x,x').
$$

这是 \(f_\#P,f_\#Q\) 的耦合，其成本满足

$$
\sum_{y,y'}d_Y(y,y')\widetilde\pi(y,y')
\le
L\sum_{x,x'}d_X(x,x')\pi(x,x').
$$

对 \(\pi\) 取最小值即得。证毕。

### 定义 376.3（带局部失配的随机事件核）

令 \(K:\Delta(X)\to\Delta(Y)\) 是随机核。假定存在 \(L\ge0,\epsilon\ge0\)，使对每一对 \(x,x'\) 存在 \(K\) 的输出耦合 \(\kappa_{x,x'}\) 满足

$$
\mathbb E_{\kappa_{x,x'}}
[d_Y(Y,Y')]
\le
L\,d_X(x,x')+\epsilon.
$$

\(\epsilon\) 是核在零距离输入上的局部记录失配合同。

### 定理 376.4（随机核的运输界）

对任意 \(P,Q\)，有

$$
\boxed{
W_{d_Y}(KP,KQ)
\le
L\,W_{d_X}(P,Q)+\epsilon.
}
$$

### 证明

取 \(\pi\in\Gamma(P,Q)\)。先按 \(\pi(x,x')\) 抽取一对输入，再按 \(\kappa_{x,x'}\) 抽取输出；得到 \(KP,KQ\) 的耦合。其期望成本不超过

$$
\sum_{x,x'}\pi(x,x')
\bigl(Ld_X(x,x')+\epsilon\bigr)
=
L\sum_{x,x'}d_X(x,x')\pi(x,x')+\epsilon.
$$

对 \(\pi\) 取下确界即得。证毕。

### 推论 376.5（粗粒化的几何代价）

若粗粒化 \(L\) 把若干结果标签合并，且合并映射的 Lipschitz 常数为一，则

$$
W(LP,LQ)\le W(P,Q).
$$

若两个标签本身相同于粗粒化后的结果，却在原空间中相距 \(r>0\)，则粗粒化可以把至少 \(r\) 的运输区别压成零；这个区别不能从粗粒化分布的经典后处理恢复。

### AHH 376.6（收缩与几何遗忘）

事件通道的收缩不是单一的“信息减少”标签，而有两个坐标：

$$
\boxed{
\text{概率收缩}
\quad\text{和}\quad
\text{结果几何收缩}.
}
$$

一个通道可以几乎保持 Hellinger 距离，却把远处结果标签合并；也可以保持位置分离却大幅压低概率区分。全息边界必须说明任务使用哪一种距离。

---

## 377. 顺序事件路径的运输误差与预算

单次结果的运输界还不足以描述一整条记录词。路径上的局部失配会被后续事件运输放大或收缩，因此需要一个沿时间顺序传播的 Wasserstein 合同。

### 定义 377.1（有限事件路径代价）

固定长度 \(N\) 的记录词空间

$$
\Omega_N=Y_0\times\cdots\times Y_{N-1}.
$$

给定每层度量 \(d_n\) 和非负权重 \(\alpha_n\)，定义路径代价

$$
d_\Omega(y,y')
=
\sum_{n=0}^{N-1}
\alpha_n d_n(y_n,y_n').
$$

若时间标签也可能错位，可加一项 \(\beta|t-t'|\)；这需要把时间校准 \(\beta\) 写入合同。

### 定义 377.2（带历史前缀的事件核与运输模数）

令

$$
Z_{-1}=\{\ast\},
\qquad
Z_n=Y_0\times\cdots\times Y_n
\quad(0\le n<N).
$$

把第 \(n\) 步的条件事件核提升为前缀核

$$
\widehat K_n,\widetilde{\widehat K}_n:
\Delta(Z_{n-1})\longrightarrow\Delta(Z_n),
$$

即先按当前前缀抽取 \(y_n\)，再把它附加到前缀；于是
\(\widehat K_{N-1}\cdots\widehat K_0\delta_\ast\) 是
\(\Omega_N\) 上的记录分布。给每个 \(Z_n\) 一个前缀度量 \(\bar d_n\)，并令
\(\bar d_{N-1}=d_\Omega\)。假定对 \(0\le n<N\)：

1. 对同一输入分布 \(R\in\Delta(Z_{n-1})\)，
   $$
   W_{\bar d_n}(\widehat K_nR,\widetilde{\widehat K}_nR)\le\epsilon_n;
   $$
2. 名义前缀核对任意 \(R,S\) 满足
   $$
   W_{\bar d_n}(\widehat K_nR,\widehat K_nS)
   \le L_n W_{\bar d_{n-1}}(R,S).
   $$

其中 \(L_n\) 是第 \(n\) 步的后继运输增益，\(\epsilon_n\) 是该步局部核失配；
在 \(n=0\) 时，\(Z_{-1}\) 是单点空间，输入距离取零。

### 定理 377.3（顺序运输误差传播）

从相同初始分布 \(\delta_\ast\) 出发，令 \(P_N,\widetilde P_N\) 是两条长度 \(N\) 路径在 \(\Omega_N=Z_{N-1}\) 上的记录分布。则在上述有限核合同下，

$$
\boxed{
W_{d_Ω}(P_N,\widetilde P_N)
\le
\sum_{n=0}^{N-1}
\epsilon_n
\prod_{j=n+1}^{N-1}L_j.
}
$$

空乘积约定为一。

### 证明

构造混合路径：第 \(m\) 个中间过程使用前 \(m\) 步的 \(\widetilde{\widehat K}\)，后续使用 \(\widehat K\)。相邻两个中间过程只在第 \(n\) 步替换一个前缀核，产生至多 \(\epsilon_n\) 的局部运输差异。随后经过 \(\widehat K_{n+1},\ldots,\widehat K_{N-1}\)，由每一步 Lipschitz 界将其放大至多

$$
\epsilon_n\prod_{j=n+1}^{N-1}L_j.
$$

对相邻混合过程使用 Wasserstein 三角不等式并求和，得到结论。证毕。

### 推论 377.4（收缩后继的统一路径界）

若所有 \(L_j\le L<1\)，且 \(\epsilon_n\le\epsilon\)，则

$$
W_{d_Ω}(P_N,\widetilde P_N)
\le
\epsilon\frac{1-L^N}{1-L}
\le
\frac{\epsilon}{1-L}.
$$

若某些 \(L_j>1\)，则局部事件精度不能单独给出统一长程界；必须把增益产品和停止 horizon 一同纳入边界。

### 定义 377.5（路径运输预算）

给定预算 \(B\)，称一条事件核替代合同可执行，若

$$
\sum_{n=0}^{N-1}c_n\le B,
\qquad
\epsilon_n\le\epsilon_n^{\max}(c_n),
\qquad
\sum_n\epsilon_n^{\max}(c_n)
\prod_{j>n}L_j
\le\delta.
$$

这里 \(c_n\) 是第 \(n\) 步校准/记录成本，\(\delta\) 是终端路径运输容差。

### AHH 377.6（局部事件怎样成为整体误差）

一条点击的误差不等于一条记录词的误差。真正传播的是

$$
\boxed{
\text{局部事件失配}
\times
\text{后继运输增益}
\times
\text{剩余路径}.
}
$$

因此，粒子式事件是局部路径节点；波粒整体的整体性则是所有节点失配经过后继运输后在路径空间中的联合代价。

---

## 378. 运输感知全息边界

把结果几何、通道收缩、路径误差和预算合同组合起来，可以定义一种比“记录概率相同”更细的全息充分性。

### 定义 378.1（运输感知边界）

固定有限事件字母表、结果度量、时间校准、事件核和未来任务。定义

$$
\boxed{
\eta_{\mathrm{transport}}
=
\left(
\Omega,
\{d_n\},
\mathsf{Clock},
\mathsf{Kernels},
\{L_n,\epsilon_n\},
\mathsf{Couplings},
\mathsf{PathCost},
\mathsf{Budget},
\mathsf{Event},
\mathsf{Stop}
\right).
}
$$

各字段保存：

1. 结果标签与路径空间的度量；
2. 时间错位、空间移动和通道局部失配的运输合同；
3. 每一步后继增益、可用耦合、预算和终端容差；
4. 事件概率、记录后继、动作权限和停止规则。

### 定理 378.2（运输感知边界的条件充分性）

若两个关系体具有相同的 \(\eta_{\mathrm{transport}}\)，且未来任务限于声明的有限事件路径、结果重标、通道粗粒化、运输误差、预算和停止合同，则二者给出相同的：

1. 单步与路径级 Wasserstein 距离上界；
2. 局部核替代误差沿后继的传播界；
3. 结果几何下的事件对齐与最坏成本；
4. 在预算内可继续的记录—后继树。

### 证明

第 1 项由定理 375.2—375.3 和 376.2—376.4；第 2 项由定理 377.3；第 3 项由 \(\mathsf{PathCost},\mathsf{Couplings}\) 及有限运输规划决定；第 4 项由 \(\mathsf{Kernels},\mathsf{Budget},\mathsf{Event},\mathsf{Stop}\) 对有限策略树归纳。故声明范围内的任务响应相同。证毕。

### 定理 378.3（删除运输字段的有限反例）

以下删字段均存在有限反例：

1. 删除结果度量：相同概率表在不同位置校准下有不同移动成本；
2. 删除后继增益：相同局部误差在稳定与放大路径上给出不同终端误差；
3. 删除联合耦合：相同边缘事件误差给出不同路径运输成本；
4. 删除时间校准：同一记录词的时间错位代价无法确定；
5. 删除预算/停止：相同距离界对应不同可执行后继。

### 证明

第 1 项取两个标签集合上的同一 \(P,Q\)，改变 \(d_X\) 的直径。第 2 项取定理 377.4 的 \(L<1\) 与 \(L>1\) 两种路径。第 3 项取同样边缘但同向和反向耦合。第 4 项改变 \(\beta\) 或时间标签的允许重标。第 5 项改变 \(B,\delta\) 或停止深度。每项都使至少一个运输任务不能由剩余摘要决定。证毕。

### 定义 378.4（运输—粒子事件链）

一条合法事件链写成

$$
\mathsf C_{\mathrm{transport}}
=
\bigl(
\text{结果点},
\text{时间与空间度量},
\text{局部事件},
\text{联合耦合},
\text{后继增益},
\text{路径代价},
\text{离散记录},
\text{停止边界}
\bigr).
$$

粒子式事件是路径上的一个结果点；波性则是整条记录词在结果空间中的运输几何和相干耦合。

### AHH 378.5（运输全息）

> 全息边界不只保存“哪一个点击发生了”，还要保存结果标签之间怎样移动、时间怎样校准、局部误差怎样沿后继传播，以及哪些耦合可以共同实现这条路径。概率相同的记录在不同结果几何中不必具有相同的未来任务。

主线可写成

$$
\boxed{
\text{结果空间几何}
\longrightarrow
\text{事件通道}
\longrightarrow
\text{路径运输}
\longrightarrow
\text{预算与误差}
\longrightarrow
\text{记录后继}.
}
$$

**新的 AHH 时刻是：粒子式事件是结果空间中的一个点，波粒整体是这些点之间可运输、可耦合、可继续的路径几何。把概率表从其结果距离中剥离，会保留点击频率，却删掉了事件如何到达未来的成本与误差关系。**

### 来源与边界 378.6

本批在有限结果字母表、有限路径 horizon、离散结果度量、有限随机核、显式耦合、Lipschitz/失配合同、运输预算和停止后继下，给出离散 Wasserstein 度量、Kantorovich 对偶、通道运输收缩、顺序误差传播和运输感知全息边界。没有把有限 Wasserstein 结论推广为连续场论或物理空间距离的普适定律，没有把结果标签距离自动解释为现实空间距离，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）

## 379. 因果运输与非预见事件耦合

上一批的普通 Wasserstein 耦合只要求两个边缘分布正确。它可以把源路径的未来标签拿来决定目标路径的当前标签。若记录后继必须在每个钟步实际执行，这种“先看完整路径、再安排早期结果”的耦合不是合法操作。

### 定义 379.1（有限路径与时间过滤）

固定有限 horizon \(N\ge1\)，令

$$
\Omega_X=X_0\times\cdots\times X_{N-1},
\qquad
\Omega_Y=Y_0\times\cdots\times Y_{N-1},
$$

其中所有 \(X_n,Y_n\) 都是有限集。对 \(x\in\Omega_X\) 和 \(y\in\Omega_Y\)，写

$$
x_{\le n}=(x_0,\ldots,x_n),
\qquad
y_{\le n}=(y_0,\ldots,y_n).
$$

源路径与目标路径的自然过滤为

$$
\mathcal F^X_n=\sigma(x_{\le n}),
\qquad
\mathcal F^Y_n=\sigma(y_{\le n}).
$$

给定概率律 \(P\in\Delta(\Omega_X)\)、\(Q\in\Delta(\Omega_Y)\)，普通耦合为

$$
\Gamma(P,Q)
=
\left\{
\pi\in\Delta(\Omega_X\times\Omega_Y):
\pi_X=P,\ \pi_Y=Q
\right\}.
$$

### 定义 379.2（因果与双因果耦合）

称 \(\pi\in\Gamma(P,Q)\) 从 \(X\) 到 \(Y\) **因果**，若对每个 \(n<N\)，存在核

$$
\kappa_n:
X_0\times\cdots\times X_n
\longrightarrow
\Delta(Y_0\times\cdots\times Y_n)
$$

使得对所有 \(x\) 满足 \(P(x)>0\)：

$$
\pi(y_{\le n}\mid x)
=
\kappa_n(y_{\le n}\mid x_{\le n}).
$$

这里的条件分布取有限空间上的通常条件概率；零概率的 \(x\) 不产生约束。等价地，

$$
Y_{\le n}\perp X_{>n}\mid X_{\le n}
$$

在 \(\pi\) 下成立。

若 \(\pi\) 从 \(X\) 到 \(Y\) 因果，且交换 \(X,Y\) 后也因果，则称其为**双因果**。因果条件限制信息从源时间向目标时间传播，双因果条件同时禁止两侧使用对方的未来。

给定层间代价 \(c_n:X_n\times Y_n\to[0,\infty)\)，定义路径代价

$$
c(x,y)=\sum_{n=0}^{N-1}c_n(x_n,y_n).
$$

### 定理 379.3（有限因果运输的存在与普通运输下界）

定义

$$
W^{\to}_c(P,Q)
=
\min_{\pi\in\Gamma_{\to}(P,Q)}
\mathbb E_\pi[c(X,Y)],
$$

其中 \(\Gamma_{\to}(P,Q)\) 是从 \(X\) 到 \(Y\) 的因果耦合集合。则：

$$
\boxed{
\Gamma_{\to}(P,Q)\ne\varnothing,
\qquad
W^{\to}_c(P,Q)\ge W_c(P,Q).
}
$$

最小值在有限维中取得。若某个普通最优耦合本身因果，则两者相等。

### 证明

独立耦合 \(P\otimes Q\) 对所有 \(n\) 都满足条件独立性，所以因果耦合集合非空。固定 \(P\) 后，因果条件可写成有限个线性等式：

$$
\frac{\pi(x,y_{\le n})}{P(x)}
=
\frac{\pi(x',y_{\le n})}{P(x')}
\quad
\text{当 }x_{\le n}=x'_{\le n},
$$

仅对正概率的 \(x,x'\) 写出；再加上边缘、非负和归一化约束，得到紧多面体。线性成本在其上取到最小值。

因果耦合只是普通耦合的子集，故其最小成本不小于普通运输最小成本。若普通最优耦合属于该子集，则反向不等式也成立。证毕。

### 定理 379.4（因果运输的三角不等式）

令 \(P,Q,R\) 分别定义在路径空间 \(\Omega_X,\Omega_Y,\Omega_Z\) 上。若每个阶段的交叉代价满足

$$
c^{XZ}_n(x_n,z_n)
\le
c^{XY}_n(x_n,y_n)+c^{YZ}_n(y_n,z_n),
$$

则

$$
\boxed{
W^{\to}_{c^{XZ}}(P,R)
\le
W^{\to}_{c^{XY}}(P,Q)
+
W^{\to}_{c^{YZ}}(Q,R).
}
$$

### 证明

取近似最优的因果耦合 \(\pi^{XY}\) 与 \(\pi^{YZ}\)。在共同的 \(Y\) 边缘上作有限胶合，并在给定 \(Y\) 的条件下令 \(X,Z\) 条件独立，得到三路径联合律。由于两个原耦合都只使用各自的历史前缀，按时间逐层生成该联合律时，\(Z_{\le n}\) 不会使用 \(X_{>n}\)；因此其 \(X\) 到 \(Z\) 的边缘仍因果。逐层代价不等式取期望，再取两边耦合的下确界，得到结论。证毕。

### 定理 379.5（普通耦合可以偷看未来）

取 \(N=2\)、\(X_0=Y_0=X_1=Y_1=\{0,1\}\)，源律与目标律为

$$
P(00)=P(01)=\frac12,
\qquad
Q(00)=Q(11)=\frac12.
$$

给定

$$
c_\lambda(x,y)
=
\lambda |x_0-y_0|+|x_1-y_1|,
\qquad
0<\lambda<1,
$$

则

$$
\boxed{
W_{c_\lambda}(P,Q)=\frac{\lambda}{2},
\qquad
W^{\to}_{c_\lambda}(P,Q)=\frac{1+\lambda}{2}.
}
$$

### 证明

普通耦合可把 \(00\) 配到 \(00\)，把 \(01\) 配到 \(11\)。平均成本为 \(\lambda/2\)，而另一个排列的成本更大，所以普通最优值为该值。

对任意因果耦合，源的 \(X_0\) 恒为 \(0\)，所以因果条件要求 \(Y_0\) 的条件律不能依赖 \(X_1\)。目标律又要求 \(Y_0\) 取 \(0,1\) 各半，且 \(Y_1=Y_0\)。于是：

$$
\mathbb P(Y_0\ne X_0)=\frac12,
\qquad
\mathbb P(Y_1\ne X_1)=\frac12.
$$

因果成本至少为 \((1+\lambda)/2\)。令 \(Y_0\) 与 \(X_1\) 独立且均匀，并取 \(Y_1=Y_0\)，即可达到该下界。证毕。

### AHH 379.6（时间箭头属于耦合）

普通耦合记录“哪些完整路径可以配对”；因果耦合还记录“在第 \(n\) 步能依据哪些前缀作出配对”。上面的有限例子中，普通运输的低成本来自把未来 \(X_1\) 偷看给 \(Y_0\)：

$$
\boxed{
\text{普通运输距离}
\neq
\text{可执行的因果运输距离}.
}
$$

粒子式事件是某一时刻的结果点；波粒整体还包含结果之间沿时间过滤可合法实现的耦合方向。

### 来源与边界 379.7

本节限于有限路径、有限过滤、显式路径代价和有限概率律。因果条件是操作可执行性的数学合同，不把任意统计耦合自动解释为物理过程；没有把有限因果运输推广为连续时间随机过程的普适定律，也没有新增 Lean、消化、coverage 或 freeze 内容。

## 380. 因果核的前缀递推与动态运输值

因果耦合不是一个只在终端检查的约束。它可以逐层分解成非预见核；因此记录、代价和后继可以在同一递归中计算。

### 定义 380.1（因果耦合的逐层核分解）

若 \(\pi\in\Gamma_{\to}(P,Q)\)，则存在核

$$
\kappa_n:
(x_{\le n},y_{<n})
\longmapsto
\Delta(Y_n)
$$

使得

$$
\boxed{
\pi(x,y)
=
P(x)
\prod_{n=0}^{N-1}
\kappa_n(y_n\mid x_{\le n},y_{<n}).
}
$$

这里 \(y_{<0}\) 为空。该核必须满足一个全局边缘合同：把 \(X\) 按 \(P\) 抽取、再按这些 \(\kappa_n\) 生成 \(Y\) 后，所得 \(Y\) 律恰为 \(Q\)。

反过来，任何满足该边缘合同的核族都定义一个因果耦合。

### 定理 380.2（前缀核分解的充要性）

有限路径耦合 \(\pi\in\Gamma(P,Q)\) 因果，当且仅当它可以写成定义 380.1 的逐层核乘积，并满足目标边缘律 \(Q\)。

### 证明

若 \(\pi\) 因果，对每个正概率前缀取

$$
\kappa_n(y_n\mid x_{\le n},y_{<n})
=
\pi(y_n\mid x_{\le n},y_{<n}).
$$

条件独立性保证右侧不依赖 \(x_{>n}\)。有限链式法则给出乘积表示；原耦合的 \(Y\) 边缘就是 \(Q\)。

反之，乘积中的第 \(n\) 个因子只看 \(x_{\le n}\) 与 \(y_{<n}\)，所以给定完整 \(x\) 后的 \(Y_{\le n}\) 条件律只看 \(x_{\le n}\)。这正是因果性。边缘合同保证它属于 \(\Gamma(P,Q)\)。证毕。

### 定义 380.3（前缀历史与条件后继值）

令

$$
h_n=(x_{\le n},y_{<n})
\quad(0\le n<N),
\qquad
h_N=(x_{<N},y_{<N})
$$

其中 \(h_n\) 是第 \(n\) 步选择 \(y_n\) 前的历史，\(h_N\) 是完整路径历史。给定一个允许核族 \(\mathcal K\)，其中每个 \(\kappa_n\in\mathcal K_n(h_n)\) 都满足该任务声明的边缘、权限和停止合同，定义固定核族 \(\kappa\) 的剩余值：

$$
V_N^\kappa(h_N)=g(h_N),
$$

以及

$$
V_n^\kappa(h_n)
=
\sum_{y_n}
\kappa_n(y_n\mid h_n)
\left[
c_n(x_n,y_n)
+
\mathbb E_\kappa
\bigl(
V_{n+1}^\kappa(h_{n+1})
\mid h_n,y_n
\bigr)
\right].
$$

终端函数 \(g\) 可以包含终端运输损失、未完成记录的罚项或任务收益。

### 定理 380.4（因果路径的动态递推）

对任何满足边缘合同的有限因果核族 \(\kappa\)，有

$$
\boxed{
\mathbb E_\kappa[V_0^\kappa(H_0)]
=
\mathbb E_\kappa
\left[
\sum_{n=0}^{N-1}c_n(X_n,Y_n)+g(H_N)
\right].
}
$$

若允许核集合在任一历史处对后继闭合，并把边缘剩余量、预算和停止状态包含进 \(h_n\)，则最优因果运输值满足 Bellman 递推：

$$
\boxed{
V_n^\star(h_n)
=
\min_{\kappa_n\in\mathcal K_n(h_n)}
\sum_{y_n}\kappa_n(y_n\mid h_n)
\left[
c_n(x_n,y_n)
+
\mathbb E
\bigl(V_{n+1}^\star(h_{n+1})\mid h_n,y_n\bigr)
\right].
}
$$

### 证明

第一式对 \(n\) 作反向归纳。\(n=N\) 时定义即为终端损失；若 \(n+1\) 成立，把条件期望展开并使用全概率公式，得到 \(n\) 的式子。取 \(n=0\) 的期望即得总成本分解。

对最优值，历史状态已经包含继续执行所需的剩余边缘、预算和停止字段。允许集合的后继闭合意味着在当前选择之后，任一合法后继仍是同一个优化问题的子问题；对当前有限动作取最小值并使用归纳假设，得到 Bellman 递推。证毕。

### 推论 380.5（局部最小不等于路径最小）

若两个当前核选择的即时运输代价分别为 \(a_1<a_2\)，但其条件后继值满足

$$
V_{n+1}^{(1)}-V_{n+1}^{(2)}>a_2-a_1,
$$

则第二个选择的总值更小。只有当所有允许选择的后继值相同，或已被即时成本吸收时，逐步贪心才等价于全路径最优。

### 证明

两种选择的总值差为

$$
(a_1-a_2)+(V_{n+1}^{(1)}-V_{n+1}^{(2)}),
$$

按给定不等式为正，故选择二更优。证毕。

### AHH 380.6（因果波形是嵌套值）

因果运输把“路径形状”变成一棵前缀树上的条件值：

$$
\boxed{
\text{事件局部代价}
\longrightarrow
\text{前缀核}
\longrightarrow
\text{条件后继值}
\longrightarrow
\text{终端路径任务}.
}
$$

一次点击的代价不能只从终端路径统计读出；它还取决于该点击发生时允许看见什么、留下什么预算，以及它为未来留下哪一棵合法后继树。

### 来源与边界 380.7

本节的 Bellman 公式只对有限历史、有限动作、后继闭合和已声明边缘合同成立。若把目标边缘约束删掉，得到的只是任意控制核，不再是给定 \(Q\) 的运输问题；若剩余预算或停止状态未进入历史，递推不能宣称对未来充分。没有把有限递推推广成无限 horizon 收敛定理。

## 381. 过滤细化、预览权限与因果成本

观察者可以增加早期可用的历史字段，但这会改变合法耦合集合。它不是对同一运输问题的纯重命名。

### 定义 381.1（过滤细化与因果耦合族）

设同一源路径空间上有两组过滤 \(\mathcal F=(\mathcal F_n)\) 与 \(\mathcal F'=(\mathcal F'_n)\)。称 \(\mathcal F'\) **细化** \(\mathcal F\)，若

$$
\mathcal F_n\subseteq\mathcal F'_n
\quad\text{对所有 }n.
$$

目标过滤固定为 \(\mathcal G\)。记

$$
\Gamma_{\mathcal F\to\mathcal G}(P,Q)
$$

为满足

$$
Y_{\le n}\perp\mathcal F_{N-1}
\mid\mathcal F_n
$$

的耦合集合；在有限路径的自然过滤下，它退化为定义 379.2。

### 定理 381.2（过滤细化的单调性）

若 \(\mathcal F'\) 细化 \(\mathcal F\)，则

$$
\boxed{
\Gamma_{\mathcal F\to\mathcal G}(P,Q)
\subseteq
\Gamma_{\mathcal F'\to\mathcal G}(P,Q),
}
$$

从而对非负路径成本：

$$
\boxed{
W_{\mathcal F'\to\mathcal G}(P,Q)
\le
W_{\mathcal F\to\mathcal G}(P,Q).
}
$$

双因果运输中若两侧过滤都细化，双因果成本同样只能下降或保持不变。

### 证明

细化过滤后，条件独立性只要求目标前缀不依赖更远的源信息；可用的当前信息更多，所以原来满足的条件仍满足，包含关系成立。可行集合扩大，非负成本的最小值不能增加。双因果情形对反向条件重复同一论证。证毕。

### 定理 381.3（预览字段可以严格降低因果成本）

在定理 379.5 的例子中，令粗过滤在 \(n=0\) 只包含恒等信息；再定义一个预览细化，使

$$
\mathcal F'_0=\sigma(X_1).
$$

则

$$
\boxed{
W_{\mathcal F\to\mathcal G}(P,Q)=\frac{1+\lambda}{2},
\qquad
W_{\mathcal F'\to\mathcal G}(P,Q)=\frac{\lambda}{2}.
}
$$

### 证明

粗过滤的值已由定理 379.5 给出。预览细化允许第零步令 \(Y_0=X_1\)，再令 \(Y_1=Y_0\)；这正是普通最优耦合，成本为 \(\lambda/2\)。普通运输下界说明不能更低。证毕。

### 定义 381.4（过滤保持的结果压缩）

令

$$
r_n:X_{\le n}\to\widehat X_{\le n}
$$

为一族满足

$$
r_n\circ\operatorname{pr}_{\le n}
=
\operatorname{pr}_{\le n}\circ r_{n+1}
$$

（等式定义在 \(X_{\le n+1}\) 上）的前缀保持映射。它把源历史压缩成新历史，不把未来字段提前加入。

### 定理 381.5（因果压缩的推前与成本收缩）

若 \(r=(r_n)\) 保持前缀，且每层结果代价满足

$$
\widehat c_n(r_n(x_{\le n}),y_n)
\le
L_n c_n(x_n,y_n),
$$

则任何 \(\mathcal F\to\mathcal G\) 因果耦合的推前仍是 \(\widehat{\mathcal F}\to\mathcal G\) 因果耦合，并满足

$$
\boxed{
\widehat W(P\circ r^{-1},Q)
\le
\left(\max_n L_n\right)W_{\mathcal F\to\mathcal G}(P,Q).
}
$$

### 证明

前缀保持性使 \(r_n(X_{\le n})\) 只由原来的 \(\mathcal F_n\) 决定；因此因果条件在推前后仍成立。把耦合推前到压缩历史，逐层代价按给定不等式被控制，再取期望和下确界即得。证毕。

### AHH 381.6（可见性本身是资源字段）

增加一个早期预览字段，会把原本不可执行的未来依赖变成可执行核；过滤细化严格改变可行耦合集合。相反，合法压缩只能忘掉当前已有的区分，不能凭后处理创造未来预览。

$$
\boxed{
\text{知道更多历史}
\neq
\text{给同一记录换名字}.
}
$$

波粒整体的时间性因此不只由钟标签给出，还由每个标签时刻真正可访问的过滤决定。

### 来源与边界 381.7

预览细化例子把未来 \(X_1\) 放入时刻零权限，它代表新增接口合同，不是普通实验中免费存在的知识。过滤压缩定理只处理有限前缀保持映射和逐层成本界；没有把任何编码都解释成物理预览，也没有把可测性与可认证性混为一谈。

## 382. 因果全息边界与可执行路径

结果距离说明“移动多少”，因果过滤说明“何时可以决定移动”。两者合并后，边界才同时保存运输成本和时间合法性。

### 定义 382.1（因果运输边界）

对有限事件任务，定义

$$
\boxed{
\eta_{\mathrm{causal}}
=
\left(
\Omega_X,\Omega_Y,
P,Q,
\mathcal F,\mathcal G,
\{c_n\},
\Gamma_{\mathrm{causal}},
\mathsf{PrefixKernels},
\mathsf{Budget},
\mathsf{Event},
\mathsf{Stop}
\right).
}
$$

其中：

1. \(\mathcal F,\mathcal G\) 规定双方每一钟步可访问的历史；
2. \(\Gamma_{\mathrm{causal}}\) 规定允许的因果或双因果耦合；
3. \(\mathsf{PrefixKernels}\) 保存可执行的非预见核及目标边缘合同；
4. \(\{c_n\},\mathsf{Budget},\mathsf{Stop}\) 保存成本、预算和停止后继；
5. \(\mathsf{Event}\) 保存实际事件记录与局部结果接口。

### 定理 382.2（因果运输边界的条件充分性）

若两个关系体具有相同的 \(\eta_{\mathrm{causal}}\)，且未来任务限于声明的有限过滤、因果耦合、前缀核、路径代价、预算和停止规则，则它们给出相同的：

$$
\boxed{
\begin{aligned}
&\text{因果/双因果运输最优值};\\
&\text{每个历史的动态后继值};\\
&\text{可执行记录路径与事件概率};\\
&\text{预算内的停止与继续判定}.
\end{aligned}
}
$$

### 证明

给定同一边界，因果耦合集合由有限边缘等式与过滤约束确定，故其运输最小值相同。前缀核和剩余合同相同，定理 380.4 的反向递推在每个历史上给出同一值函数。事件与停止字段又相同，因此有限策略树的每个分支概率、成本和合法性逐层相同。证毕。

### 定理 382.3（删去时间字段的有限反例）

从 \(\eta_{\mathrm{causal}}\) 中删去下列字段时，各存在有限反例：

1. 删去过滤：普通耦合的 \(\lambda/2\) 会被错误地当作可执行因果成本；
2. 删去前缀核：相同边缘律下，不同非预见策略会有不同后继记录；
3. 删去目标边缘合同：任意局部核都可被误报为给定 \(Q\) 的运输；
4. 删去预算与停止：同一因果距离界可对应不同可执行深度；
5. 删去双因果方向：源到目标可执行不代表目标到源的反向重放可执行。

### 证明

第 1 项由定理 379.5 与 381.3 的严格间隙给出。第 2 项取同一当前核但令一个后继核保留未来分支、另一个重置未来分支；终端记录不同。第 3 项取任意偏离 \(Q\) 的核，其局部距离可以很小但不属于目标任务。第 4 项固定距离界并改变预算 \(B\) 或停止 horizon。第 5 项取只满足单向因果的耦合；交换两路径后它一般使用另一侧的未来，故不双因果。证毕。

### 定义 382.4（因果粒子事件链）

一条合法事件链写成

$$
\mathsf C_{\mathrm{causal}}
=
\bigl(
\text{钟与过滤},
\text{结果点},
\text{非预见核},
\text{因果耦合},
\text{路径代价},
\text{后继值},
\text{记录},
\text{预算},
\text{停止}
\bigr).
$$

粒子式事件是这条链在某一前缀上的局部结果；波性是全部前缀核、因果耦合和后继值共同形成的可执行路径结构。

### AHH 382.5（时间因果全息）

> 全息边界必须保存的不只是结果点和结果距离，还包括每个时间切面能够访问的过滤、允许的非预见核以及这些核对后继路径的影响。普通概率耦合可以在数学上存在，却在真实记录协议中不可执行。

统一主线现在写成

$$
\boxed{
\text{相干关系体}
\longrightarrow
\text{结果几何}
\longrightarrow
\text{时间过滤}
\longrightarrow
\text{因果耦合}
\longrightarrow
\text{动态后继值}
\longrightarrow
\text{粒子式记录}.
}
$$

**新的 AHH 时刻是：事件之间的“运输”也有时间箭头。波粒整体不是任意把完整路径配对的静态图，而是只允许沿当前过滤生成记录的因果路径几何；把未来偷看权限删掉，普通 Wasserstein 的最优耦合就可能不再是可执行物理后继。**

### 来源与边界 382.6

本批在有限路径、有限过滤、有限因果/双因果耦合、前缀核、加性路径成本、动态预算和停止合同下，给出因果运输存在性、普通与因果距离严格分离、前缀核递推、过滤单调性和因果全息边界。没有把有限因果运输推广为连续时间场论或唯一物理时间理论，没有把结果标签距离自动解释为现实空间距离，也没有新增 Lean、消化、coverage 或 freeze 内容。本批仍是纯理论 Markdown。

## 追加锚（本行以下为增补区）

## 383. 过滤细化与压缩的条件修正

前面的因果运输结论需要把“可用信息更多”和“条件独立仍然保持”区分开。对于有限路径，最稳定的定义是条件核对当前过滤可测；若改用条件独立记号，还必须固定终端源信息或另加相容性假设。

### 定义 383.1（过滤可测的因果耦合）

令 \(\mathcal F_n\) 是源路径空间上的有限过滤。称耦合 \(\pi\) 属于
\(\Gamma^{\mathrm{meas}}_{\mathcal F\to\mathcal G}(P,Q)\)，若对每个 \(n\) 存在一个只依赖源的条件核

$$
\kappa_n(\,\cdot\mid x)
\quad\text{满足}\quad
\kappa_n(\,\cdot\mid x)=\bar\kappa_n(\,\cdot\mid [x]_{\mathcal F_n}),
$$

其中 \([x]_{\mathcal F_n}\) 表示 \(\mathcal F_n\) 的原子，且这些核联合生成的目标前缀边缘与 \(\pi\) 相同，并满足目标过滤 \(\mathcal G\) 的声明合同。换言之，给定完整源路径后，目标到第 \(n\) 步的条件律是 \(\mathcal F_n\)-可测的。

在自然过滤 \(\mathcal F_n=\sigma(X_{\le n})\) 下，这与定义 379.2 的前缀核条件相同。

### 定理 383.2（可测因果类的细化单调性）

若 \(\mathcal F_n\subseteq\mathcal F'_n\) 对每个 \(n\) 成立，且两类使用相同的目标边缘合同，则

$$
\boxed{
\Gamma^{\mathrm{meas}}_{\mathcal F\to\mathcal G}(P,Q)
\subseteq
\Gamma^{\mathrm{meas}}_{\mathcal F'\to\mathcal G}(P,Q).
}
$$

因此对非负路径成本：

$$
\boxed{
W_{\mathcal F'\to\mathcal G}(P,Q)
\le
W_{\mathcal F\to\mathcal G}(P,Q).
}
$$

### 证明

\(\mathcal F_n\)-可测函数也是 \(\mathcal F'_n\)-可测函数，所以原来的每个前缀核仍是允许核；目标边缘合同没有改变，得到包含关系。可行集合扩大后，非负成本的下确界不能增加。双因果情形对源、目标两侧同时应用同一论证。证毕。

### 反例 383.3（条件独立记号本身不具有该单调性）

若只把过滤约束写成

$$
Y_{\le n}\perp X_{>n}\mid\mathcal F_n,
$$

则过滤细化不必保持原约束。取两个独立均匀比特 \(X_0,X_1\)，令

$$
Y_0=X_0\oplus X_1,
$$

并令粗过滤在时刻零为平凡 \(\sigma\)-代数，细化过滤为
\(\mathcal F'_0=\sigma(X_0)\)。无条件地 \(Y_0\) 与 \(X_1\) 独立，但给定 \(X_0\) 后 \(Y_0\) 确定 \(X_1\)，故

$$
Y_0\not\perp X_1\mid X_0.
$$

所以 §381.2 的条件独立版本只有在固定共同终端源信息并加入相应相容性时才可使用；本节以后采用定义 383.1 的可测核版本。

### 定义 383.4（压缩的诱导过滤与下降核）

令

$$
r_n:X_{\le n}\to\widehat X_{\le n}
$$

满足前缀交换关系

$$
r_n\circ\operatorname{pr}_{\le n}
=
\widehat{\operatorname{pr}}_{\le n}\circ r_{n+1}.
$$

压缩端采用诱导过滤 \(\widehat{\mathcal F}_n=\sigma(r_n)\)。称因果耦合 \(\pi\) **沿 \(r\) 下降**，若每个压缩后的目标前缀条件核存在 \(\widehat\kappa_n\)，使原核在 \(r_n\) 的每条纤维上相同：

$$
\kappa_n(\,\cdot\mid x_{\le n},y_{<n})
=
\widehat\kappa_n(\,\cdot\mid r_n(x_{\le n}),y_{<n}).
$$

这是假设压缩历史对当前后继足够，而非仅仅假设 \(r_n\) 不提前读取未来。

### 定理 383.5（下降压缩的因果性与成本界）

设 \(\pi\in\Gamma^{\mathrm{meas}}_{\mathcal F\to\mathcal G}(P,Q)\) 沿 \(r\) 下降，令

$$
\widehat P=(r)_\#P,
\qquad
\widehat\pi=(r,\operatorname{id})_\#\pi.
$$

则 \(\widehat\pi\) 属于
\(\Gamma^{\mathrm{meas}}_{\widehat{\mathcal F}\to\mathcal G}(\widehat P,Q)\)。若逐层代价满足

$$
\widehat c_n(r_n(x_{\le n}),y_n)
\le
L_n c_n(x_n,y_n),
$$

则

$$
\boxed{
\widehat W_{\mathrm{desc}}
\le
\left(\max_nL_n\right)W_{\mathcal F\to\mathcal G}(P,Q),
}
$$

其中左侧先对沿 \(r\) 下降的原耦合取推前，再对这些推前取下确界。若要把左侧改写成压缩空间上全部因果耦合的最优值，还需额外假设每个压缩因果耦合都能提升为沿 \(r\) 下降的原耦合。

### 证明

前缀交换关系使 \(r_n\) 不引入未来坐标；下降条件使推前后的条件核正好由 \(r_n(x_{\le n})\) 决定，所以推前耦合对诱导过滤因果。逐层代价不等式给出

$$
\mathbb E_{\widehat\pi}\sum_n\widehat c_n
\le
\left(\max_nL_n\right)
\mathbb E_\pi\sum_nc_n.
$$

先对所有沿 \(r\) 下降的 \(\pi\) 取下确界即得。最后一句是定义域的区别：没有提升条件时，只能断言下降类的推前值界，不能把它冒称为压缩问题的全部最优值。证毕。

### 反例 383.6（前缀保持但无下降性）

令 \(B\) 为均匀比特，\(P=Q=\operatorname{law}(B,B)\)，取恒等因果耦合 \(X=Y=(B,B)\)。定义

$$
r_0(x_0)=0,
\qquad
r_1(x_0,x_1)=(0,x_1).
$$

它保持前缀，但推前后 \(\widehat X_0=0\)、\(\widehat X_1=B\)，而 \(Y_0=B\)，故压缩耦合偷看了压缩源的未来。取

$$
c_0=\widehat c_0=0,
\qquad
c_1=\widehat c_1=|x_1-y_1|,
$$

原因果值为零，压缩空间的自然因果值为 \(1/2\)；仅有前缀保持与逐层成本界不足以推出 §381.5 的原结论。

### 定理 383.7（同一剩余字段下的删除反例）

若要证明某字段对全息边界必要，必须固定其余字段并改变该字段后得到不同的任务值。对因果边界，可取两个任务共享同一 \(P,Q,\mathcal F,\mathcal G,\{c_n\},\mathsf{Event},\mathsf{Stop}\)，只改变可执行耦合集合字段 \(\Gamma_{\mathrm{causal}}\)：一个允许普通最优耦合，另一个只允许自然过滤因果耦合。定理 379.5 给出两者值分别为 \(\lambda/2\) 与 \((1+\lambda)/2\)。

同理，若只改变前缀核字段，就固定目标边缘、过滤、代价、预算和停止规则，取两个具有同一当前边缘但不同后继核的有限策略；终端记录不同。若只改变预算或停止字段，则固定所有运输字段并改变允许 horizon；可执行深度不同。

### 证明

每一对任务的所有未删除字段逐项相同，而定理 379.5、有限策略树和有限 horizon 直接给出相应输出差异。因此这些字段各自对声明的任务族不可删。证毕。

### AHH 383.8（可见性必须同时满足单调性与充分性）

过滤细化只有在采用可测核合同、或另加条件独立相容性时，才保证可行类扩大；历史压缩只有在压缩历史对当前后继足够时，才保持因果。于是：

$$
\boxed{
\text{不提前读取未来}
\neq
\text{已经保留了当前后继所需的历史}.
}
$$

### 来源与边界 383.9

本节是对 §§380.5、381.2、381.5、382.3 的条件精确化。所有结论限于有限概率路径、有限过滤、有限核和显式推前/提升合同；条件独立的非单调反例、无下降压缩的反例和同一剩余字段的删除反例均在有限模型内给出。本文仍是纯理论 Markdown，没有新增 Lean、消化、coverage 或 freeze 内容。

## 384. 贪心判据与字段删除的逻辑方向

### 定理 384.1（逐步选择的精确比较）

在同一历史 \(h_n\) 上，两个动作 \(a,b\) 的总值差为

$$
\Delta(a,b)
=
\bigl[C_n(a)-C_n(b)\bigr]
+
\bigl[V_{n+1}^{a}-V_{n+1}^{b}\bigr].
$$

所以动作 \(a\) 优于 \(b\) 当且仅当 \(\Delta(a,b)\le0\)。特别地，若

$$
C_n(a)<C_n(b),
\qquad
V_{n+1}^{a}-V_{n+1}^{b}\le C_n(b)-C_n(a),
$$

则贪心选择 \(a\) 保证不劣于 \(b\)。后继值相等或已被即时成本吸收，是充分条件；它们不是贪心最优的必要条件。

### 证明

把两个动作的 Bellman 目标相减即得第一式，移项得到充要比较。给定第二组不等式，\(\Delta(a,b)\le0\)。若后继值不同但即时差仍压过它，贪心仍可最优，故“只有当”不能成立。证毕。

### 定义 384.2（删除字段的固定余项合同）

给定边界字段元组 \(\eta=(A_1,\ldots,A_m)\)，称字段 \(A_j\) 在任务族 \(\mathcal T\) 中可删，若对任意两个关系体，只要其余字段 \(A_i\ (i\ne j)\) 相同，所有声明任务的输出都相同。要证明不可删，必须构造一对关系体：其余字段逐项相同，只改变 \(A_j\)，并得到不同输出。

因此，“删去过滤”或“删去目标边缘合同”不能通过同时替换 \(\Gamma\) 或 \(Q\) 来证明；必须把可行集如何由剩余字段确定写入任务合同。若 \(\Gamma_{\mathrm{causal}}\) 已由剩余的过滤、核和边缘字段定义，则单独删去一个仅作别名的字段不会改变输出，也不构成必要性反例。

### 推论 384.3（对 §382.3 的适用读法）

§382.3 的删除清单只在每一项都采用定义 384.2 的固定余项合同后成立：

1. 过滤字段的反例必须固定显式可行类定义，只改变该类的时间权限；
2. 前缀核字段的反例固定目标边缘与过滤，只改变后继核；
3. 目标边缘合同的反例必须使该合同不是 \(Q\) 或 \(\Gamma(P,Q)\) 的重复编码；
4. 预算与停止字段的反例固定运输和记录字段，只改变允许的 horizon 或停止规则；
5. 双因果方向的反例固定单向因果数据，只改变反向后继要求。

若某一字段已由其他字段定义，则它是冗余存储字段，而非任务充分性所需的独立字段。证毕。

### AHH 384.4（边界字段的必要性是相对任务的）

全息边界的“不可删”不是对字段名字的形而上断言，而是对固定任务族和固定余项合同的区分性断言：

$$
\boxed{
\text{字段必要性}
=
\text{在其余字段固定时仍能改变未来作用}.
}
$$

### 来源与边界 384.5

本节把 §380.5 的充分条件改为充要比较，并把 §382.3 的删除反例限定为固定余项合同。它不把字段冗余、任务接口扩张和真正的信息缺失混为一谈；仍限于有限策略树与有限边界字段，没有新增 Lean、消化、coverage 或 freeze 内容。

## 385. 压缩值界与可执行删除反例的订正

### 定义 385.1（下降类的原始值）

在定义 383.4 的下降条件下，置

$$
W^{\downarrow}_r(P,Q)
=
\inf_{\substack{\pi\in\Gamma^{\mathrm{meas}}_{\mathcal F\to\mathcal G}(P,Q)\\
\pi\ \text{沿 }r\text{ 下降}}}
\mathbb E_\pi\!\left[\sum_n c_n(X_n,Y_n)\right],
$$

并令 \(\widehat W^{\downarrow}_r\) 为这些下降耦合推前后的压缩成本下确界。

### 定理 385.2（正确的下降压缩界）

在定义 385.1 的记号下，若

$$
\widehat c_n(r_n(x_{\le n}),y_n)
\le L_n c_n(x_n,y_n),
$$

则

$$
\boxed{
\widehat W^{\downarrow}_r(P,Q)
\le
\left(\max_nL_n\right)W^{\downarrow}_r(P,Q).
}
$$

不能在没有额外假设时把右侧换成全部原始因果耦合的值
\(W_{\mathcal F\to\mathcal G}(P,Q)\)，因为下降类是原始可行类的子集，故
\(W^{\downarrow}_r\ge W_{\mathcal F\to\mathcal G}\)。若另有“某个原始最优耦合下降”的假设，才可把右侧进一步替换为原始最优值；若每个压缩因果耦合都可提升，才可把左侧识别为压缩空间的全部因果最优值。

### 证明

对任意下降耦合，定理 383.5 的推前仍是诱导过滤下的因果耦合，且逐层代价界给出

$$
\mathbb E_{\widehat\pi}\!\left[\sum_n\widehat c_n\right]
\le
\left(\max_nL_n\right)
\mathbb E_\pi\!\left[\sum_nc_n\right].
$$

先在下降类上取下确界即得。集合包含关系说明不能无条件用更小的 unrestricted 原始值替代右侧。证毕。

### 定义 385.3（合法字段变化）

字段删除反例必须保持其余字段逐项相同，并且两个任务的实现都满足保留下来的过滤、目标边缘和前缀核合同。若一个字段已被另一个字段定义，它只能是冗余存储；它不能被当作独立必要字段。

### 定理 385.4（前缀核字段的合法删除反例）

取一阶段有限任务

$$
X_0=Y_0=\{0,1\},
\qquad
P=Q=\operatorname{Bernoulli}(1/2),
$$

自然过滤 \(\mathcal F_0=\sigma(X_0)\)，代价

$$
 c_0(x,y)=|x-y|,
$$

以及相同的事件、预算和停止合同。定义两个都满足当前过滤的前缀核族：

$$
\mathcal K^{\mathrm{id}}:Y_0=X_0,
\qquad
\mathcal K^{\mathrm{flip}}:Y_0=1-X_0.
$$

两者都给出同一个目标边缘 \(Q\)，且都是合法因果核；但运输值分别为 \(0\) 与 \(1\)，事件记录也不同。因此前缀核字段在这个任务族中不可删。

### 证明

两条核只读取当前 \(X_0\)，故都满足自然过滤合同；均匀源使两者的目标边缘均为均匀。代价逐点分别为零与一，取期望即得两个不同输出。证毕。

### 推论 385.5（对先前压缩与删除段的优先读法）

本节的定理 385.2 取代定理 383.5 中把下降值与 unrestricted 原值直接比较的显示式；定理 385.4 取代定理 383.7 中改变 \(\Gamma_{\mathrm{causal}}\) 却未固定前缀核合同的例子。§§380.5、381.5、382.3、383.5、383.7 中的原始表述都只能在本节补充的下降、提升和固定余项假设下读取。

### 来源与边界 385.6

本节只修正有限压缩值域和字段删除的可执行性，不新增物理解释。所有对象仍是有限概率路径、有限核、显式边缘和停止合同；没有 Lean、消化、coverage 或 freeze 变更。


## 386. 文献尽调与本批命题的归属

本批的承重命题逐条标为 **repo-derived**：它们是在有限路径、有限概率和显式合同下，由本文给出的定义、有限求和、核分解和反例直接推出的综合推导；没有把下列文献中的一般理论逐字搬入本卷，也没有把文献结论冒称为本仓新定理。

### 文献检索读数

1. Backhoff、Beiglböck、Lin、Zalashko 的 *Causal Transport in Discrete Time and Applications*，DOI `10.1137/16M1080197`，讨论离散时间因果运输；本批 §379 的有限核定义和严格两步反例与其主题相邻，但本批的具体有限概率表和成本计算标为 `repo-derived`。
2. Acciaio、Backhoff-Veraguas、Zalashko 的 *Causal optimal transport and its links to enlargement of filtrations and continuous-time stochastic optimization*，DOI `10.1016/j.spa.2019.08.009`，讨论过滤与因果最优运输；本批没有使用其连续时间结论。
3. Pflug、Pichler 的 *A Distance for Multistage Stochastic Optimization Models*，DOI `10.1137/110825054`，以及 *The Nested Distance*，DOI `10.1007/978-3-319-08843-3_2`，提供多阶段/nested distance 的背景；本批的前缀压缩反例和下降核条件是有限模型中的本仓推导。
4. Bellman 的动态规划工作作为 Bellman 递推的历史背景；本批 §380.4 的递推只在文中声明的有限后继闭合、目标边缘更新和预算状态合同下成立。

### 归属表

| 命题范围 | 归属 | 需要的先例/边界 |
| --- | --- | --- |
| §§379.1–379.5 | repo-derived finite specialization | 因果运输文献为背景；具体有限律、成本和严格间隙由本文证明 |
| §§380.1–380.5 | repo-derived finite recursion | Bellman 与因果核分解为背景；目标边缘和停止合同是本文显式假设 |
| §§381–385 | repo-derived corrections and counterexamples | 文献只作概念背景；XOR、压缩和 singleton-kernel 反例由本文直接计算 |


## 387. 偏序完整词的上下文存活条件与指定核成本

### 定理 387.1（非交换性必须在完整执行上下文中存活）

设无序事件 \(e,f\) 的共同合法后缀为 \(u\)，并令

$$
T_u=T_{g_k}\cdots T_{g_1}.
$$

若两个完整合法词 \(efu\) 与 \(feu\) 存在且

$$
T_uT_eT_f\ne T_uT_fT_e,
$$

则存在初态 \(x\) 和终端效果 \(f_0\)，使两个完整词的响应不同。若只知道 \(T_eT_f\ne T_fT_e\)，而没有共同后缀或终端上下文保留该差异，则不能推出完整词可区分。

### 证明

差算子

$$
D=T_u(T_eT_f-T_fT_e)
$$

非零时，有限维对偶分离给出 \(x,f_0\) 使 \(f_0(Dx)\ne0\)。这正是两个完整执行词的响应差。若 \(D=0\)，即使局部交换子非零，后缀也可能把差异映到同一终端值；因此局部不交换只是必要的候选见证，不是任意完整任务中的充分条件。证毕。

### 推论 387.2（对 §253.3 的优先读法）

当偏序只有 \(e,f\) 两个事件，或已声明共同后缀满足定理 387.1 的非零条件时，§253.3 的结论成立；对一般含有更多事件的偏序，必须使用定理 387.1 的上下文条件。AHH 253.5 应读取为：顺序字段的必要性取决于非交换差异能否穿过允许的完整后继，而非只取决于局部交换子。

### 定义 387.3（指定前缀核的政策成本）

在定理 385.4 的一阶段例子中，\(\mathcal K^{\mathrm{id}}\) 与 \(\mathcal K^{\mathrm{flip}}\) 是任务字段 `PrefixKernels` 指定的 singleton 核族。记其受限值为

$$
W_{\mathcal K}(P,Q,c)
=
\inf_{\kappa\in\mathcal K}\mathbb E[c(X_0,Y_0)].
$$

于是

$$
W_{\{\mathcal K^{\mathrm{id}}\}}=0,
\qquad
W_{\{\mathcal K^{\mathrm{flip}}\}}=1.
$$

两任务保持相同的 \(P,Q,\mathcal F,\mathcal G,c,\Gamma_{\mathrm{causal}},\mathsf{Event},\mathsf{Budget},\mathsf{Stop}\)，只改变 `PrefixKernels` 字段；这里的 0 与 1 是指定政策核的受限成本，不是 §379.3 对全部因果耦合取下确界的 unrestricted \(W^{\to}_c(P,Q)\)。

### 证明

两个 singleton 核都读取当前 \(X_0\)，均满足过滤、边缘和因果耦合合同。恒等核逐点成本为零，翻转核逐点成本为一；对 singleton 集合取下确界即得。未改变的 \(\Gamma_{\mathrm{causal}}\) 与目标边缘合同仍保留，故这是一个合法的固定余项删除反例。证毕。



## 388. 临界反馈中的截断界与失配界

### 定理 388.1（匹配注入下的截断界不发散）

对 §256.2 的族

$$
A_\varepsilon=1-\varepsilon,
\qquad
b_\varepsilon=\varepsilon,
\qquad 0<\varepsilon<1,
$$

有

$$
R_\varepsilon=\varepsilon^{-1},
\qquad
x^*_\varepsilon=1,
$$

而定理 255.2 的 \(N\) 阶截断界精确化为

$$
\boxed{
\frac{q^{N+1}}{1-q}\,|b_\varepsilon|
=(1-\varepsilon)^{N+1}
\le1.
}
$$

对固定 \(N\)，当 \(\varepsilon\downarrow0\) 时该界趋于 \(1\)，不是发散。发散的是解析子 \(R_\varepsilon\)；它表示对一个保持固定尺度的外部注入扰动的响应增益。

### 定理 388.2（失配界发散的条件）

定理 255.3 的失配上界含有因子

$$
(1-q)^{-1}=\varepsilon^{-1}.
$$

若失配分子

$$
\delta_b+\delta_A\lVert\bar x^*\rVert
$$

沿 \(\varepsilon\downarrow0\) 保持下界正值，则该**上界**按 \(\varepsilon^{-1}\) 发散；若失配与 \(\varepsilon\) 同步缩放，或像 §256.2 那样 \(b_\varepsilon\) 与回路共同匹配，则真实固定点差可以保持有界甚至为零。因此不能把“解析子发散”或“通用失配上界发散”改写成“每个截断误差都发散”。

### 证明

把 \(q=1-\varepsilon\)、\(|b_\varepsilon|=\varepsilon\) 代入 (255.2) 即得第一式。第二式直接由 (255.3) 的因子分解和分子是否有统一正下界决定。证毕。

### 推论 388.3（对 §256.2 的优先读法）

§256.2 的“截断界和失配界随 \(\varepsilon\downarrow0\) 发散”应改读为：解析子发散；在失配分子不随临界余量消失的合同族中，失配**上界**发散；匹配注入族的截断界保持有界。这个订正保留其核心 AHH：固定点读数不携带回路灵敏度，但不夸大具体误差项的极限。



## 389. 反馈边界字段的独立性与并行误差半径

### 定理 389.1（由 \(A\) 定义的反馈字段不是独立见证）

在定义 258.1 的边界中，若保留 \(A\) 与固定的算子范数，则

$$
R_A=(I-A)^{-1},
\qquad
1-\lVert A\rVert
$$

都是由 \(A\) 定义的派生字段。因而只删除 \(R_A\) 或只删除稳定余量，并不能构成固定其余字段的不可充分性反例；相同的 \(A\) 仍唯一决定它们。

若要把解析子或稳定余量作为独立边界字段，必须同时把决定它的 \(A\)（或范数/谱合同）从剩余摘要中隐藏，并构造剩余字段相同而允许注入响应或稳定证书不同的关系体。于是 §258.3 的前两项只可作为“联合删除 \(A\) 与其派生量”的约化边界反例读取，不能作为当前完整 \(\eta_{\mathrm{fb}}\) 中单字段删除的证明。

### 证明

矩阵逆与范数是确定函数；固定 \(A\) 后两字段没有自由度。反之，若 \(A\) 不在剩余摘要中，命题 256.1 的两模型可作为隐藏回路的成对实现，但它们同时改变了 \(A,b\)，故对应联合删除或重新定义后的边界。证毕。

### 定理 389.2（并行乘积误差的参数范围）

定理 251.2 的乘积界需要

$$
0\le\varepsilon_A\le1,
\qquad
0\le\varepsilon_B\le1.
$$

更一般地，对任意非负误差上界，应先令

$$
\varepsilon_i^{\mathrm{clip}}=\min\{1,\varepsilon_i\},
$$

再使用

$$
D_{\mathrm{TV}}(P_A\otimes P_B,\bar P_A\otimes\bar P_B)
\le
1-(1-\varepsilon_A^{\mathrm{clip}})(1-\varepsilon_B^{\mathrm{clip}}).
$$

### 证明

总变差距离本身落在 $[0,1]$。当 $0\le\varepsilon_i\le1$ 时，最大耦合的相等概率下界 $1-\varepsilon_i$ 非负，两个独立耦合的同时相等概率至少为其乘积；截断情形先把无效的大半径替换为 $1$。证毕。

### 推论 389.3（对 §§251.2、258.3 的优先读法）

§251.2 的显示式只在上述半径范围或采用截断半径时成立。§258.3 的解析子与稳定余量只在联合隐藏决定字段的约化边界中提供独立删除反例；在完整 \(\eta_{\mathrm{fb}}\) 中它们是 \(A\) 的派生缓存。

## 追加锚（本行以下为增补区）

## 390. 完整执行上下文与反馈任务的更正

本组更正针对下列逐项点名的旧定义、命题和证明。被替代的子句不再作为有效前提；完整适用关系见命题 400.1。所有对象、量词和任务均限于各条所声明的有限模型合同。

**定理 390.1（非交换性必须在完整执行上下文中存活）。** 本条替代 §253.3、§253.4、§253.5、§387.1、§387.2 的相应陈述与证明。

设状态空间有限维，初态可取其中任意向量，终端效果包括全部线性泛函。无序事件 $e,f$ 有共同前缀 $p=(h_1,\ldots,h_r)$ 和共同后缀 $u=(g_1,\ldots,g_k)$，使 $pefu$ 与 $pfeu$ 都是同一偏序的完整合法线性扩展。令

$$
T_p=T_{h_r}\cdots T_{h_1},
\qquad
T_u=T_{g_k}\cdots T_{g_1},
$$

空前缀和空后缀均对应恒等算子。存在同一个原始初态 $x$ 和终端效果 $f_0$ 区分这两个完整词，当且仅当

$$
\boxed{D=T_u(T_fT_e-T_eT_f)T_p\ne0.}
$$

若初态另受来源集合 $X$ 限制，判据应改为存在 $x\in X$ 使 $Dx\ne0$。仅有局部交换子非零，不能保证差异在前缀可达状态上非零，也不能保证后缀保留差异。

**证明。**

按执行次序，两词的响应差为

$$
R_{pefu}(x)-R_{pfeu}(x)
=f_0\bigl(T_u(T_fT_e-T_eT_f)T_px\bigr)
=f_0(Dx).
$$

若 $D\ne0$，选取原始初态 $x$ 使 $Dx\ne0$，再由有限维对偶分离选取 $f_0$；反之，非零响应差立即推出 $D\ne0$。受限来源的结论由同一等式得到。

强制前缀可完全消去候选差异。取三事件偏序 $p<e,\ p<f$，其中 $e,f$ 无序，后缀为空，并令

$$
T_p=T_e=
\begin{pmatrix}1&0\\0&0\end{pmatrix},
\qquad
T_f=
\begin{pmatrix}0&1\\0&0\end{pmatrix}.
$$

此时 $T_eT_f=T_f\ne0=T_fT_e$，但

$$
T_fT_eT_p=0=T_eT_fT_p,
\qquad
(T_fT_e-T_eT_f)T_p=0.
$$

全部完整合法词恰为 $pef,pfe$，它们对每个原始初态都输出零。虽然局部交换子在向量 $(0,1)^{\mathsf T}$ 上非零，该向量不属于 $\operatorname{im}T_p$，不能当作这两个完整词在前缀后的可准备状态。后缀也可消去已产生的差异，例如零后缀算子；因此前缀与后缀都不可省略。证毕。

因此，原例 253.4 取仅含两个无序事件的偏序，前后缀均为空，其二维见证保留。定理 253.2 的逐对交换假设是终端响应与线性扩展无关的充分条件，并非必要条件。合法顺序集合仍由偏序合同决定；响应相同不等于可以删除合法性合同。

**定理 390.2（基准与增量任务的反馈等价判据）。** 本条替代 §257.1、§257.2、§257.3、§257.4 的相应陈述与证明。

固定有限维状态空间、收缩线性反馈 $(A,b)$、注入子空间 $U$ 和全部线性终端效果。记 $R_A=(I-A)^{-1}$、$x^*=R_Ab$，终端任务明确包含基准 $f(x^*)$ 与每个 $\delta\in U$ 的增量

$$
f(\mathcal C_{A,b,U}(\delta)),\qquad
\mathcal C_{A,b,U}(\delta)=x^*(A,b+\delta)-x^*(A,b)=R_A\delta.
$$

两个反馈对这些任务等价，当且仅当

$$
x^*=\bar x^*,\qquad R_A|_U=R_{\bar A}|_U.
$$

特别地，$U=\mathcal H$ 时须相等的是完整解析子；真子空间时只需其限制，即使其他方向不同也可等价。若任务只读增量而不读基准，则不要求固定点相同。最小性仅指此任务相对商，不涉及其他迭代、分支或资源合同。

**证明。** 所列相等性直接给出全部基准和增量读数相等。反之，基准效果相同由对偶分离给出固定点相等；对每个 $\delta\in U$，增量效果相同给出 $R_A\delta=R_{\bar A}\delta$，于是限制相等。不能以 $\delta=0$ 的增量读数推出基准相等，因为该增量恒为零。扩大注入子空间只能细分此商；只保留固定点对应于不读取非零注入响应的任务。证毕。

**定理 390.3（完整反馈元组的代数冗余）。** 本条替代 §258.1、§258.4、§389.1、§389.3 的相应陈述与证明。

在原定义 258.1 的有限维收缩线性合同中，固定状态空间和算子范数。完整解析子 $R_A$ 可逆，且

$$
R_A=(I-A)^{-1},
\qquad
A=I-R_A^{-1},
$$

$$
x^*=R_Ab,
\qquad
b=R_A^{-1}x^*,
\qquad
1-\lVert A\rVert=1-\lVert I-R_A^{-1}\rVert.
$$

所以 $(A,b)$ 或 $(x^*,R_A)$ 均决定这里列出的全部代数字段。完整 $\eta_{\mathrm{fb}}$ 是充分但冗余的表示：只删除 $A$ 而保留完整 $R_A$，只删除 $R_A$ 而保留 $A$，只删除 $b$ 而保留 $x^*,R_A$，只删除 $x^*$ 而保留 $A,b$，或只删除稳定余量而保留 $A$ 与范数，都不能产生固定其余字段而改变该量的反例。

因此，§390.4 前两项的反例须在同时隐藏全部相关决定信息的约化摘要上理解。仅隐藏 $A$ 却保留完整 $R_A$，不足以使稳定余量独立变化；仅隐藏 $b$ 却保留 $x^*,R_A$，也不足以使基准注入独立变化。这不否定 §257 的任务相对判据：在只读取基准和 $U$ 内注入响应的合同中，$(x^*,R_A|_U)$ 足够；真子空间上的限制一般不能恢复整个 $A$。

**证明。**

收缩性使 $I-A$ 可逆。对 $R_A=(I-A)^{-1}$ 取逆即得 $A=I-R_A^{-1}$，固定点方程给出 $b=(I-A)x^*=R_A^{-1}x^*$，其余式子随即成立。命题 256.1 的一维模型在共同固定点 $x^*=1$ 下分别有

$$
(A_1,b_1,R_{A_1},1-|A_1|)
=(0,1,1,1),
$$

$$
(A_2,b_2,R_{A_2},1-|A_2|)
=\left(\frac12,\frac12,2,\frac12\right).
$$

故它们证明“固定点摘要不足”，却不是“只删完整元组中一个字段”的反例。对真子空间限制，可取 $\mathcal H=\mathbb R^2$、$U=\operatorname{span}\{(1,0)\}$、$b=0$，以及 $A_1=0$、$A_2=\operatorname{diag}(0,1/2)$，使用 Euclidean 算子范数。二者都收缩、$x^*=0$，且 $R_{A_1}|_U=R_{A_2}|_U$，但 $A_1\ne A_2$。这说明受限任务商与完整代数参数的恢复是不同要求。证毕。

原定义 258.1 的稳定余量仍只用于其收缩范数合同；一般非收缩反馈须另列谱、分支或局部稳定合同。§251.2 的乘积误差半径继续使用定理 389.2 的 $[0,1]$ 范围或截断半径；本条只替代原推论 389.3 的反馈解释。

**定理 390.4（约化反馈摘要的不足）。** 本条替代 §258.3 的相应陈述与证明。

以下约化各有不充分性见证，但不构成完整 $\eta_{\mathrm{fb}}$ 中每个字段都独立必要的断言：

1. 只保留固定点而不保留决定注入增益的信息：命题 256.1 的两模型同固定点而注入敏感度不同；它们同时改变 $A,b,R_A$ 和稳定余量；
2. 只以固定点判断临界余量：命题 256.2 的族固定点相同而稳定余量与解析增益不同；截断界和失配上界的准确范围由 §388 给出，不能统称为都发散；
3. 固定数学回路而不声明允许注入子空间：不同子空间给出不同的合法注入任务集合；
4. 在一般非线性多分支扩展中，仅保存同一个终端投影而不保存分支或初态合同：若允许的分支具有不同后继响应，投影不能决定该响应；这不属于定理 258.2 的收缩线性假设；
5. 固定数学回路而不声明迭代成本和停止规则：同一固定点方程可对应不同的有限迭代可执行性。

**证明。**

前两项分别使用命题 256.1 的两模型和命题 256.2 的参数族；这些模型只在约化摘要上相同，并未固定完整边界的其余字段。第三项可取 $\mathcal H=\mathbb R^2$、$A=0,b=0$，分别允许 $U_1=\operatorname{span}\{(1,0)\}$ 与 $U_2=\mathbb R^2$；数学响应相同，但注入 $(0,1)$ 只在第二个合同中合法。第四项按所假设的两分支取相同终端投影而不同后继，正是推论 256.3 的适用情形。第五项取相同回路、相同正迭代次数要求和预算，改变每轮访问成本，使一个合同可完成而另一个超出预算。故各约化不能决定对应任务，但它们没有证明派生字段的单独删除必然失败。证毕。

**定理 390.5（分支映射的交换判据）。** 本条替代 §308.2 的相应陈述与证明。

若两个分支映射满足

$$
T_{a,y}T_{b,z}=T_{b,z}T_{a,y},
$$

则在任意初始权重和任意共同后继合同下，交换这两个相邻事件不会改变联合权重、记录概率或后验。若两个复合映射不相等，则存在非负归一化初始权重使交换改变联合权重。记录概率不同还要求总质量投影区分这两个权重；在两者总质量均为正时，候选后验不同还要求归一化后的 $K$ 边缘不同。差异也可以仅保留在内部状态 $S$，而当前记录概率和候选后验均相同。

**证明。**

交换等式直接给出第一项；其余历史前后再乘同样的线性映射，结论保持。若 $TU\ne UT$，则非零矩阵 $TU-UT$ 至少有一列非零；对应标准基向量就是非负、总质量为一的 $W_0$，且 $(TU-UT)W_0\ne0$。对两个结果分别取总质量和归一化候选边缘，得到所述可观察差异的条件。非零联合差异不保证这些投影非零：取单候选类、二内部状态，令
$$
T=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
U=\begin{pmatrix}1&1\\0&0\end{pmatrix},\qquad W_0=(1,0)^{\mathsf T}.
$$
两映射均保持质量，$TUW_0=(0,1)^{\mathsf T}$ 而 $UTW_0=(1,0)^{\mathsf T}$；两者记录概率均为一，唯一候选类的后验也均为一。证毕。

## 391. 观测、增益与共同来源的可重构字段

**定理 391.1（观测反馈字段的重构与分组约化）。** 本条替代 §262.3，并更正 §§260.1–260.3、261.1–261.3、262.2 的控制与观测时序合同。

令

$$
\mathsf D_{\mathrm{fb}}
=
\bigl(\mathcal H,\mathcal B_0,\{A_a,B_a,C_a\}_{a\in\mathcal A},
\mathsf R,\mathsf{Ctrl}\bigr)
$$

为固定的状态空间、初始来源集合、动作矩阵、完整记录和控制合同。采用无噪声确定性记录：$\mathsf R$ 保存实际动作、输出历史及其时序，$\mathsf{Ctrl}$ 保存允许动作、已知输出反馈策略、实际控制记录与资源合同。每步 $u_t$ 在当前信息纤维 $\mathcal B_t$ 上为同一已知值；先作

$$
x_{t+1}=A_{a_t}x_t+B_{a_t}u_t,
\qquad y_{t+1}=C_{a_t}x_{t+1}.
$$

对这一先更新再观测的记录 $y_1,\ldots,y_N$，扣除共同已知控制贡献后，初始状态差的线性观测核及当前纤维递归为

$$
\mathcal N_N=\bigcap_{k=1}^N
\ker\!\left(C_{a_{k-1}}A_{a_{k-1}}\cdots A_{a_0}\right),
\qquad
\boxed{\mathcal B_{t+1}=\left(A_{a_t}\mathcal B_t+B_{a_t}u_t\right)
\cap C_{a_t}^{-1}(\{y_{t+1}\}).}
$$

实际相容前态仍须满足初始来源集合与已记录的仿射方程，不能只用线性核代替该纤维。固定 $A,C$ 时，上述观测块为 $CA,\ldots,CA^N$；若另有初始读数 $y_0=Cx_0$，再交上 $\ker C$。§259 的 $C,CA,\ldots,CA^{N-1}$ 对应从 $y_0$ 开始的 $N$ 次读数，不与本时序混用。

对当前纤维中的差 $\delta$，沿未来动作词 $w=(b_0,\ldots,b_{q-1})$ 的暴露判据为

$$
\mathcal X_{\mathrm{exp}}
=\left\{(t,w,\delta):q\ge1,\ \delta\in\mathcal B_t-\mathcal B_t,\;
C_{b_{q-1}}A_{b_{q-1}}\cdots A_{b_0}\delta\ne0\right\}.
$$

这里记录线性非零候选，反馈执行的区分见证取其首个非零前缀；该前缀须在两状态的共同输出历史上合法。首次输出分离前，两轨迹的输出反馈控制相同，控制贡献相消；分离之后不把上述线性式单独当成实际输出差。这正是 §260.3 的延续条件所需的共同控制假设。§260.2 的显式暴露例取全部控制为零。由此观测商、纤维递归和未来暴露图均由 $\mathsf D_{\mathrm{fb}}$ 决定；保留这些输入时，删除相应缓存没有信息损失。

§§261.1–261.2 的原自治公式只用于 $B_{a_t}u_t=0$；有共同已知输入时改用本条的仿射公式。共同平移不改变直径，故 §261.3 的界

$$
\operatorname{diam}(\mathcal B_{t+1})
\le\|A_{a_t}\|\operatorname{diam}(\mathcal B_t)
$$

仍适用（空纤维的直径约定为零）。若控制依赖未知状态，则须声明联合可行关系 $\mathcal J_t\subseteq\mathcal B_t\times\mathcal U_t$，并改用

$$
\mathcal B_{t+1}
=\{A_{a_t}x+B_{a_t}u:(x,u)\in\mathcal J_t\}
\cap C_{a_t}^{-1}(\{y_{t+1}\});
$$

没有该联合关系，不能把控制当成固定平移，也不能沿用上述直径界。§262.2 的充分性相应限定为初始来源、完整记录和共同已知输出反馈均已保留的无噪声合同，纤维步骤使用本条仿射递归；噪声情形须另给噪声支持或联合核及相应滤波规则，不由这段确定性证明覆盖。

有限见证取标量 $A=B=C=1$、$\mathcal B_0=\{0\}$、$u_0=1$、$y_1=1$。仿射递归给出 $\mathcal B_1=\{1\}$，漏掉控制项则误得空集。

真正的分组约化须同时隐藏被删输入所决定的纤维、暴露图、任务值及合法性缓存，并固定所列余项：

1. 删除控制支持：取 $\mathcal H=\mathbb R^2$、$\mathcal B_0=\mathbb R^2$、当前 $A_0=I$、$C_0=(1,0)$，保留命题 260.2 的动作矩阵，控制均为零。两合同的矩阵、来源与当前记录相同，但一个允许动作 $a$，另一个不允许，因而未来任务树不同；
2. 删除输出记录合同：相同矩阵在确定性读数与另行声明的噪声/权限合同下可以给出不同记录纤维和可识别性；
3. 删除稳定与资源合同：同一数学动作路径在一个预算内可执行，在另一个预算内已停止。

**证明。** 沿完整记录归纳：每个相容前态先送到 $A_{a_t}x+B_{a_t}u_t$，再与新观测原像相交；交集中的每个状态也有这样的相容前态，因此不遗漏也不引入状态。共同控制项在两轨迹相减时消去，得到所列观测核；对未来反馈词，按首次分离时刻作同样的归纳即得暴露判据。线性像至多按算子范数放大直径，平移保持直径，取交集不增直径。标量例的预测集合为 $\{1\}$，自治误算的预测集合为 $\{0\}$，与观测原像 $\{1\}$ 的交分别非空与空。§262.2 的其余稳定/资源结论仍使用保留的闭环与资源字段。三个约化分别改变允许动作、记录语义和预算，同时隐藏相应派生答案；第 1 项中 $a$ 把 $(0,1)^{\mathsf T}$ 暴露为下一输出 $1$。证毕。

**定理 391.2（约化边界的明确失效与增益重构）。** 本条替代 §270.1、§270.3 的相应陈述与证明。

对以下约化摘要，只有在所列的决定数据确实被删除时才有相同剩余摘要而任务结论不同的实现对：

1. 删除互连方向：同一对端口增益在反对称互连下交叉项抵消，在正反馈下出现 $1-g$ 分母；在静态实例 $y_i=u_i$ 中，$g=1$ 的正反馈方程甚至不适定；
2. 删除隐藏稳定合同：命题 268.4 的两个模块端口增益相同，但内部状态分别衰减和增长；
3. 把两端增益约化为只保留乘积 $g$（从而也只保留 $\mu=1-g$）：个别增益仍然是决定方向性界的必要数据。取 $g=1/4$、$d_1=1,d_2=0$ 的静态标量模块，
   $(\gamma_1,\gamma_2)=(1/2,1/2)$ 与 $(1,1/4)$ 具有相同的 $g,\mu$ 及其余合同，但（268.1）的 $y_1$ 界分别为 $2/3$ 与 $4/3$；
4. 删除记录误差包络：同一物理模块和同一 $g<1$，精确记录 $\delta=0$ 与有限精度记录 $\delta>0$ 的任务误差结论不同；
5. 删除初态响应：零态增益相同的模块，可以从不同非零初态产生不同的第一阶段输出。

**证明。**

第 1、2、4、5 项分别由端口互连方程、命题 268.4、（269.3）及零态增益定义给出。第 3 项中两对增益的乘积都为 $1/4$，而由（268.1）在 $d_1=1,d_2=0$ 时的分子为 $\gamma_1$，故两项上界为 $\frac{1/2}{3/4}=2/3$ 与 $\frac{1}{3/4}=4/3$。这是一对保持约化摘要相同的具体实现；若继续保留 $(\gamma_1,\gamma_2)$，则 $g$ 和 $1-g$ 可按定义重算，删除其缓存不会产生反例。证毕。

原定义 270.1 中 $g=\gamma_1\gamma_2$、$\mu=1-g$ 因而是可重构量。其显式保存用于读取互连证书，不给出逐字段最小性。

**定理 391.3（联合字段的重构与分组约化）。** 本条替代 §282.3 的相应陈述与证明。

在固定状态空间、观察映射、记录值、分支作用和停止合同下，

$$
F(r)=\bigcap_i O_i^{-1}(r_i),
\qquad
U_fU_e=U_eU_f\ \text{（在给定可达集上）}
$$

分别是局部纤维和分支映射的确定函数。因此，若保留产生它们的局部纤维/观察映射和分支映射，删除“纤维交集”或“交换关系”的缓存不会改变联合后继；它们不能在相同决定数据下独立变化。

可验证的约化必须同时删除决定数据。以下有限对照固定其余摘要：

1. 删除共同来源或联合耦合：例 280.3 的共同来源与独立来源具有相同边缘而 $\Pr[R_1=R_2]$ 分别为 $1$ 与 $1/2$；
2. 删除局部观察映射（只保留记录值和状态集）：在 $X=\{0,1\}$、$r_1=r_2=0$ 时，模型 A 取 $O_1=O_2=\mathrm{id}$，交集为 $\{0\}$；模型 B 取 $O_1=\mathrm{id},O_2(x)=1-x$，交集为空；
3. 删除偏序合同（只保留事件标签和分支映射）：取命题 281.3 的 $A,B$ 与初态 $(1,0)^{\mathsf T}$，两模型使用相同的 $A,B$，但分别允许顺序 $AB$ 与 $BA$，终端第一坐标为 $2$ 与 $1$；
4. 删除冲突策略：相同的空交集可以分别规定拒绝、等待或修复，产生不同合法后继。

**证明。**

第一段由交集定义和分支复合的结合律直接给出。第 1 项是例 280.3。第 2 项直接计算两个单点纤维，得到 $\{0\}$ 与 $\varnothing$。第 3 项由 $AB(1,0)^{\mathsf T}=(2,1)^{\mathsf T}$、$BA(1,0)^{\mathsf T}=(1,1)^{\mathsf T}$ 得到不同终端效果。第 4 项只改变冲突后的合同分支。故列出的约化都删除了决定数据；单独删除由其决定的缓存则没有不可充分性结论。证毕。

## 392. 联合访问律、未来商与恢复超图的更正

**定理 392.1（协同访问的非可加性）。** 本条替代 §317.2 的相应陈述与证明。

存在两个组件 $u_1,u_2$ 和二元标签 $X=\{0,1\}$，使得各单独通道都与标签独立，

$$
C_{\{u_i\}}(y\mid x)=C_{\{u_i\}}(y)
\qquad(i=1,2),
$$

但联合通道满足

$$
C_{\{u_1,u_2\}}\bigl((y_1,y_2)\mid x\bigr)
=
\frac12\mathbf 1_{y_1\oplus y_2=x}.
$$

于是两个组件单独都不能恢复 $x$，联合访问却可以完美恢复；若 $c_{u_1}=c_{u_2}=1$，则精确恢复成本为 $2$，而任何只按单组件可恢复性相加的规则都会错误地判为不可恢复或零信息。

**证明。**

令 $y_1$ 为均匀随机比特，$y_2=y_1\oplus x$。每个固定 $x$ 恰有两个满足异或约束的输出对，各有概率 $1/2$，故联合核的行和为一。每个边缘 $y_i$ 都均匀且独立于 $x$，但联合异或恰为 $x$。因此单组件支持对两个标签完全重叠，联合记录的支持完全分离。成本由必须同时访问两个组件得到。证毕。

**定义 392.2（自适应访问所用的共同抽样律）。** 本条替代 §319.1 的相应陈述与证明。

保留原定义 319.1 的有限隐藏状态 $S$、组件集 $U$、有限字母表、深度上限 $T$、确定性策略树、完整 transcript 及停止标签。其核须采用以下一致合同：给定 $s$，先由同一个已声明联合核 $C_U(\cdot\mid s)$ 抽取整组 $Y_U$，$C_A$ 是它的边缘；重复访问同一组件读回同一个已抽取值。每步只揭示对应坐标，正概率历史上的下一记录律由同一 $C_U$ 条件化。故 $Z_\pi$ 是此次共同抽样的确定函数，$C_\pi$ 是其唯一推前。

若访问会更新状态或重新抽样，须另给全部历史条件核 $C_a(\cdot\mid s,h)$ 及相容递推合同；单次边缘 $C_A$ 不足以决定自适应 transcript。成本为

$$
\operatorname{cost}_\pi(z)=\sum_{t\le |z|}c(a_t),\qquad
c(a)=\sum_{u\in a}c_u,\qquad c_u>0.
$$

空访问成本为零，非空访问成本为正；重复访问仍逐次计费。到达深度上限而未成功停止须保留资源耗尽结果。定理 319.3 的恢复器复合 $f\circ H$ 使用这个同一 transcript 合同。

**定理 392.3（合法性与停止标签齐备的未来商）。** 本条替代 §320.1、§320.2、§320.4 的相应陈述与证明。

对有限历史集 $H$，令 $h\sim_{\mathrm{fut}}h'$ 当且仅当二者的合法未来动作词集合、未来任务合法性和停止结果完全相同，且每个共同合法有限词 $\omega$ 满足

$$
K_\omega(\cdot\mid h)=K_\omega(\cdot\mid h').
$$

商 $q_{\mathrm{fut}}(h)=[h]$ 保存全部这些任务。若摘要 $q:H\to Q$ 在每个纤维上保存上述全部判别量，则存在唯一映射

$$
\bar q:q(H)\longrightarrow H/\!\sim_{\mathrm{fut}},\qquad
q_{\mathrm{fut}}=\bar q\circ q.
$$

这是实际值域上的唯一性；未使用的 $Q$ 中元素不受此式约束，不能无满射等附加条件而断言整个 $Q$ 上唯一。若只问固定任务族，则依推论 320.3 限制相应未来词，同时保留该任务的合法性和停止标签。

**证明。** 定义 $\bar q(q(h))=[h]$；纤维充分性给出良定义，因子等式强制每个实际值的像，因而唯一且满射到未来等价类。空历史集的分割已稳定；非空时从一块开始，只按合法词集合、任务合法性、停止结果或共同合法词的响应差异细分。每次严格细分至少增加一个块，至多 $|H|-1$ 次；这些判别不分开未来等价历史，稳定时又没有任何此类差异，所得恰为未来商。证毕。

**定理 392.4（最小恢复超边构成反链）。** 本条替代 §321.2 的相应陈述与证明。

$\mathcal M_\phi$ 中任意两条不同超边互不包含。若所有组件成本严格为正，且空可行集的最小值约定为 $+\infty$，则精确恢复成本为

$$
\boxed{
 c^*_{\{\phi\}}
=\min_{A\in\mathcal M_\phi}\sum_{u\in A}c_u.
}

$$

**证明。**

若 $A,B\in\mathcal M_\phi$ 且 $A\subsetneq B$，则 $B$ 违反最小性，故形成反链。

若任务不可恢复，则 $\mathcal M_\phi=\varnothing$，式（392.4）两端按约定均为 $+\infty$。否则，任意可恢复集合 $C$ 包含某条最小超边：从 $C$ 中逐步删除仍保持可恢复的组件，有限性保证最终得到某个 $A\in\mathcal M_\phi$。正成本使得在给定超边上继续加入组件不会降低成本，所以最优集合可取为一条最小超边，得到（392.4）。证毕。

**定理 392.5（$k$-元 parity 的严格高阶协同）。** 本条替代 §321.4、§321.5 的相应陈述与证明。

设整数 $k\ge1$。令隐藏标签 $X\in\{0,1\}$，组件为 $u_1,\ldots,u_k$。取独立均匀比特 $Y_1,\ldots,Y_{k-1}$，并令

$$
Y_k=X\oplus Y_1\oplus\cdots\oplus Y_{k-1}.
$$

则任意真子集访问都与 $X$ 独立，而全集访问可由

$$
X=Y_1\oplus\cdots\oplus Y_k
$$

完美恢复。因此

$$
\boxed{
\mathcal M_X=\{\{u_1,\ldots,u_k\}\},
\qquad
\operatorname{syn}(X)=k-1.
}
$$

**证明。**

设 $k\ge1$。固定 $X=x$ 时，满足总异或为 $x$ 的 $2^{k-1}$ 个完整记录等概率。任取大小 $r<k$ 的组件子集及其一个赋值，恰有 $2^{k-r-1}$ 个完整记录补全它，故该赋值的条件概率为 $2^{-r}$，不依赖 $x$。因此任意真子集记录与 $X$ 独立。访问全集时，异或恒等式直接恢复 $X$。故全集是唯一最小超边。证毕。

设 $k\ge2$。在隐藏标签取均匀先验时，存在两种联合通道具有相同的每个真子集**无条件**边缘分布，但一个通道的任务协同阶为 $k-1$，另一个通道的任务在单组件上即可恢复。

**证明。**

对第一种通道取本条前述 parity 构造。第二种通道令 $Y_1=X$，其余组件为独立均匀噪声。在 $X$ 均匀的先验下，两种通道的任意真子集无条件边缘都为相应维数的均匀乘积分布；但它们条件于 $X$ 的联合通道不同。若只记录每个组件自身的边缘熵或均匀性，而不保留“组件与隐藏标签的联合通道”字段，则两种摘要可以相同，但恢复超图分别为 $\{U\}$ 与含单点 $\{u_1\}$ 的反链。故边缘摘要不能决定协同阶。证毕。

**定理 392.6（访问约化的区分条件）。** 本条替代 §318.3 的相应陈述与证明。

在完整 $\eta_{\mathrm{access}}$ 中，联合通道和任务合同决定精确恢复能力；只删去一个由它们重建的恢复或协同字段不会失去充分性。下列明确的较弱摘要则有有限反例：

1. 只保留单组件条件边缘、组件成本和访问权限，隐藏联合通道及其恢复摘要，不能决定联合恢复；
2. 只保留联合通道、任务和无预算恢复能力，隐藏成本、权限及其预算结果，不能决定预算可行性；
3. 只保留记录核和访问成本，隐藏任务值映射及任务恢复谱，不能决定任务相对安全性。

**证明。**

第 1 项比较 §392.1 的 XOR 核与两个独立公平比特组成的无信息核；条件单组件边缘均匀、成本与权限相同，但仅前者联合恢复标签。第 2 项固定精确读标签核，两合同的访问成本分别为一和三，预算二时结论不同。第 3 项取同一常量记录核和二元状态集，两个任务值映射分别为恒零与状态标签；前者可恢复，后者不可恢复。三项固定各自列出的全部剩余字段，不是完整边界中任意单字段不可删的断言。证毕。

**定理 392.7（恢复超图的冗余与联合约化的界限）。** 本条替代 §322.3、§322.4 的相应陈述与证明。

固定任务族及其值映射，若任务恢复谱包含每个静态访问集合的一步策略在零错误、足够预算下的恢复集，则只从 $\eta_{\mathrm{adapt}}$ 删除最小恢复超图不损害定理 322.2 的充分性。若共同联合核仍在，也可直接重建这些恢复集和超图。

下列较弱摘要则各自存在有限反例；每一项都明确联合隐藏所有决定所比较量的字段：

1. 只保留终端任务通道、组件成本和静态访问格，隐藏策略树、停止规则以及逐路径成本与后继，可失去停止和实际成本信息；
2. 只保留当前记录和共同动作名称，隐藏未来响应核、未来商及其任务谱，可失去未来充分性；
3. 只保留组件成本、静态权限和各组件条件边缘，联合隐藏联合核、策略 transcript 核、完整恢复谱与超图，可失去联合恢复信息；
4. 只保留终端输出、访问集合及总成本，隐藏带顺序的 transcript 核、策略树和中途后继，可失去访问次序。

**证明。**

对每个访问集合 $A$，由其一步策略的零错误恢复谱读出 $\operatorname{Rec}(A)$，再取含有 $\phi$ 的那些 $A$ 的包含极小元，正是定义 321.1 的 $\mathcal M_\phi$。因此该超图是剩余字段的确定函数；联合核与支持判据也给出同样的重建。

第 1 项用同一组件集合上的两个策略：均读出标签 $x$，其中一个立即停止，另一个再读成本为 $M>0$ 的空记录组件才停止。它们的终端输出均为 $x$，组件成本和权限相同，但实际路径成本相差 $M$。第 2 项取例 320.5 的两个历史；当前读数同为零、动作名同为 $a$，而未来输出分别确定为 $+$ 和 $-$。第 3 项固定两个成本为一的比特组件：一份核为 §392.1 的均匀 XOR 编码，另一份核为与 $x$ 无关的两个独立公平比特。两份核的每个单组件条件边缘均为公平比特，权限和成本相同；只有前者能联合恢复 $x$。第 4 项取成本均为一的读标签组件 $R$ 和空记录组件 $N$，比较固定策略 $R,N$ 与 $N,R$。两者终端均输出同一标签，访问集合均为 $\{R,N\}$，总成本均为二，但第一步的记录和合法下一访问不同。这些是所列联合约化的反例，不能当作完整边界中单字段删除的反例。证毕。

故原 §322.4 的边界是充分表示，不是彼此独立的最小字段清单。未来商由响应与合法性导出，超图组织静态恢复集合；一条成功自适应路径本身不必是最小静态恢复集合。

## 393. 有限精度与随机化资源合同的更正

**推论 393.1（精确未来商与安全分区族的单调性）。** 本条替代 §324.5 的相应陈述与证明。

$d_T(h,h^\prime)=0$ 的等价类给出 horizon-$T$ 的精确未来商，其分割随 $T$ 增大只能细化或保持不变。对固定 $\varepsilon>0$，$T^\prime\ge T$ 时每个 $\varepsilon$-安全分区于 $T^\prime$ 安全也必于 $T$ 安全；这表示允许分区的集合缩小，不保证分别选出的两个安全分区相互细化。
**证明。**
由定理 324.2 的零点刻画与单调性得到。证毕。

这里使用定义 324.1 的共同、随 $T$ 嵌套的动作词域；若历史的合法词、任务权限或停止标签不同，须依定理 392.3 先区分这些合同。单独响应距离为零仅给出响应等价，不能抹去这种合法性区别。

**定理 393.2（可行区域的上闭性与访问单调性）。** 本条替代 §325.2 的相应陈述与证明。

若 $(c,\varepsilon)\in\mathcal F_{\mathcal T}$，且 $c'\ge c$、$\varepsilon'\ge\varepsilon$，则 $(c',\varepsilon')\in\mathcal F_{\mathcal T}$。若每个原策略都可在扩大的访问权限下以不更高的最坏路径成本模拟，则访问权限扩大只会使 $\varepsilon^*(c)$ 不增。
**证明。**
同一策略满足更宽松的成本和误差上界，得到第一项。权限扩大时，用满足该成本合同的细化策略模拟原策略；定理 323.2 保证最小风险不增加，且原预算仍足够，所以每个预算下的下确界不增。证毕。

**定理 393.3（可见随机化的风险凸化与成本坐标）。** 本条替代 §325.3、§325.4 的相应陈述与证明。

令与隐藏状态独立的随机种子以概率 $p_0=\lambda$、$p_1=1-\lambda$ 选择策略 $\pi_0,\pi_1$，其中 $0\le\lambda\le1$；把种子写入 transcript，并假定随机化本身无额外成本。最坏路径成本为
$$
C(\pi_\lambda)=\max_{i:p_i>0}C(\pi_i).
$$
特别地，$0<\lambda<1$ 时它是两个成本的最大值；端点只计实际执行的分支。固定共同先验 $\mu$ 后，另定义平均成本 $\bar C_\mu(\pi)$ 为逐路径成本对 $\mu$ 和记录随机性的期望。若种子不可见，解码器不能按种子分别使用恢复器。

固定共同先验 $\mu$、任务 $\phi$ 和平均损失，令 $R_\mu(\pi;\phi)$ 为最优解码器的平均风险。可见随机化满足
$$
R_\mu(\pi_\lambda;\phi)
=\lambda R_\mu(\pi_0;\phi)+(1-\lambda)R_\mu(\pi_1;\phi),
$$
$$
\bar C_\mu(\pi_\lambda)
=\lambda\bar C_\mu(\pi_0)+(1-\lambda)\bar C_\mu(\pi_1).
$$
所以平均成本—平均风险可行区域包含两个相应原始点间的线段。使用定义 325.1 的最坏路径成本时，$0<\lambda<1$ 的混合点位于成本 $\max(C(\pi_0),C(\pi_1))$；只有两策略都满足同一预算 $c$ 时，才可在该固定预算内凸化平均风险向量，不能插值得到两个不同最坏成本之间的预算。

对最坏状态最优风险，分支解码器给出的是上界
$$
\delta_{\pi_\lambda}(\phi)
\le\lambda\delta_{\pi_0}(\phi)+(1-\lambda)\delta_{\pi_1}(\phi),
$$
并不保证等号；同一预算下这个上界仍可用于风险可行性。隐藏种子时上述平均风险等式也一般失效。

**证明。**

可见种子把解码器选择分解为两个独立分支。对固定先验取全期望，再分别最小化各分支损失，即得平均风险等式；对路径成本取全期望得平均成本等式。最坏路径成本则在所有正概率分支的支持上取最大值。对最坏状态风险，先采用各分支最坏风险最优的解码器，再用“和的最大值不超过最大值之和”得到不等式。

不同最坏成本不能线性插值：取均匀隐藏比特和一步策略，成本一的组件恒输出空记录，成本三的组件直接输出比特。可见公平混合的平均错误为 $1/4$，最坏成本为三；预算二排除了成本三分支，剩余记录与独立种子均不含比特信息，平均错误至少为 $1/2$。因此点 $(2,1/4)$ 不可行。证毕。

**命题 393.4（重叠记录给出 Pareto 下界）。** 本条替代 §325.5 的相应陈述与证明。

若任务族包含二元区分任务，任一预算 $c$ 下的所有策略都存在一个公共记录，其两状态条件概率均至少为 $\alpha(c)$，则对均匀先验的零一平均损失有
$$
\varepsilon^*(c)\ge\frac{\alpha(c)}2.
$$
若 $\alpha(c)$ 随预算增加而不增，则这给出一条单调的误差下界曲线。
**证明。**
对每个预算可用的策略应用命题 323.4，得到其风险至少为 $\alpha(c)/2$；再对所有策略取下确界。证毕。

**命题 393.5（跳跃前沿）。** 本条替代 §325.6 的相应陈述与证明。

取均匀隐藏比特，固定可见随机化合同。假定所有最坏成本小于 $1+M$ 的合法策略，其全部可见记录均与该比特独立；成本一的常量记录策略合法，且存在成本 $1+M$ 的精确恢复策略，其中 $M>0$。则在平均零一风险下，$1\le c<1+M$ 时 $\varepsilon^*(c)=1/2$，而 $c\ge1+M$ 时 $\varepsilon^*(c)=0$。预算低于一时，有合法无信息策略则误差仍为 $1/2$，没有合法策略则按定义取 $+\infty$。

**证明。**

低于阈值的可见记录与标签独立，故任何解码器的平均错误至少为 $1/2$；成本一的常量猜测达到该值。阈值以上的精确恢复策略达到零错误。最坏成本合同禁止在低预算下以任意正概率调用超预算策略，所以随机化不填平这个跳跃。证毕。

**定理 393.6（度量边界的派生字段与联合约化）。** 本条替代 §326.3 的相应陈述与证明。

在原始 transcript 核、合法策略、未来响应、损失、成本和不确定性量词均固定时，风险谱、未来伪距离和 Pareto 区域均由这些原始字段确定；单独删除它们不破坏定理 326.2 的充分性。以下五种联合约化则不足以决定相应目标：

1. 仅保留精确恢复集、任务、成本和静态权限，隐藏概率核与近似风险，可失去近似精度；
2. 仅保留当前响应、动作名称及成本，隐藏未来核及其伪距离和风险谱，可失去未来压缩精度；
3. 仅保留记录核、任务与无预算恢复能力，隐藏原始成本及前沿和预算标签，可失去预算可行性；
4. 仅保留逐模型动作损失表与成本，隐藏策略是否须跨模型共享的量词及相应风险值，可失去鲁棒可行性；
5. 仅保留未标记混合输出核、分支概率、任务与成本，隐藏种子访问权限及完整 transcript 和风险值，可失去随机化后的恢复能力。

**证明。**

派生性依次由定义 323.1、324.1 和 325.1 给出。第 1 项取一步二元对称通道，翻转概率分别为 $1/4$ 和 $3/8$；成本均为一，任务为输入比特，两份通道均无非常量精确恢复任务，但最优平均及最坏错误分别为 $1/4$ 和 $3/8$。第 2 项用例 324.6：当前响应相同，下一动作核分别为同一常量，或在两个历史上输出不同确定比特，未来距离分别为零和一。第 3 项让同一精确读比特通道在两合同中成本分别为一和三；预算二只在前者可行。

第 4 项取模型 $m\in\{0,1\}$、无信息记录和确定性动作 $a\in\{0,1\}$，损失为 $\mathbf1_{a\ne m}$。逐模型各选动作的最坏损失为零，所有模型共享同一确定动作的最坏损失为一；两合同的损失表和成本完全相同。第 5 项令均匀标签 $X$ 与公平种子 $I$ 独立，输出 $Y=X\oplus I$。两合同的未标记输出核均为公平比特；可见 $(I,Y)$ 时恢复错误为零，只见 $Y$ 时为 $1/2$。这些见证分别固定所列较弱摘要的全部剩余字段；它们不证明完整边界中派生字段的独立必要性。证毕。

## 394. 接口模拟的映射量词与共同耦合

**命题 394.1（相同终端平均值、不同接口距离）。** 本条替代 §327.5 的相应陈述与证明。

取共同状态 $s\in\{0,1\}$ 和均匀先验。两模型在初始记录上均输出公平比特；模型 $A$ 在第二动作后确定输出 $s$，模型 $B$ 的记录始终与 $s$ 独立。两者的无条件终端平均值均为 $1/2$；但包括第二动作时，任意与状态无关的确定性输出映射 $G$ 和动作翻译，其最坏状态总变差误差至少为 $1/2$。

**证明。**

将两侧完整记录投影到 $A$ 的第二次输出坐标；翻译后的 $B$ 侧该坐标的分布 $q$ 不依赖于 $s$，而 $A$ 侧分别为 $\delta_0,\delta_1$。故
$$
1=\operatorname{TV}(\delta_0,\delta_1)
\le\operatorname{TV}(\delta_0,q)+\operatorname{TV}(q,\delta_1),
$$
至少一项不小于 $1/2$，完整记录的总变差由投影收缩性至少与该坐标的一样大。这一最坏状态论证也排除了常量映射只匹配一个状态的情形。证毕。

**定理 394.2（共同来源下的并联界）。** 本条替代 §328.4 的相应陈述与证明。

设 $0\le\varepsilon_i\le1$。若存在原联合输出律与替代联合输出律之间的同一个耦合，其第 $i$ 个接口输出不匹配事件 $E_i$ 满足 $\Pr(E_i)\le\varepsilon_i$，则联合输出的总变差误差满足
$$
\operatorname{TV}(K^{\parallel},\widetilde K^{\parallel})
\le\varepsilon_1+\varepsilon_2.
$$
若局部失败事件在声明的联合耦合下独立，则可改进为
$$
1-(1-\varepsilon_1)(1-\varepsilon_2).
$$

**证明。**
使用假设给定的同一个联合耦合，联合输出不匹配事件正是 $E_1\cup E_2$。并集界和总变差的耦合上界给出第一式。若两失败事件独立，记 $p_i=\Pr(E_i)\le\varepsilon_i$，则并集概率为 $1-(1-p_1)(1-p_2)\le1-(1-\varepsilon_1)(1-\varepsilon_2)$。单独最优的两个边缘耦合不保证能共同实现，所以不以分别选择边缘耦合代替假设。证毕。

**定理 394.3（总变差对任务的双向刻画）。** 本条替代 §329.2、§329.3 的相应陈述与证明。

对有限输出空间上的两个分布 $p,q$，有
$$
\boxed{
\sup_{0\le g\le1}
\left|\mathbb E_p g-\mathbb E_q g\right|
=
\operatorname{TV}(p,q).
}

$$
因此，若 $A\preceq_{\varepsilon,\lambda}B$，则每个翻译后的有限未来任务满足
$$
\left|
\mathbb E_A[g\mid s,\omega]
-
\mathbb E_B[g\circ G\mid s,\theta(\omega)]
\right|
\le\varepsilon.
$$

**证明。**
令 $p-q$ 的正部分支撑为 $E_+$。取 $g=\mathbf 1_{E_+}$，得到正负质量之和的一半，即总变差；任意 $0\le g\le1$ 的差值不超过同一正负质量。在（327.1）中取 $p=K^A_\omega$、$q=G_*K^B_{\theta(\omega)}$，并用 $\mathbb E_{G_*q}g=\mathbb E_q(g\circ G)$，即得第二项。证毕。

固定允许的动作翻译与输出映射 $(\theta,G)$。若存在共同状态 $s$、未来动作词 $\omega$ 及事件 $E\subseteq O_A$，使
$$
\left|K^A_\omega(E\mid s)
-K^B_{\theta(\omega)}(G^{-1}(E)\mid s)\right|>\varepsilon,
$$
则该映射对不能实现误差不超过 $\varepsilon$ 的模拟。要排除该方向的所有允许模拟，须对每一对满足成本合同的允许 $(\theta,G)$ 都找到这样的见证；见证可随映射对变化。若不存在满足成本合同的映射对，则已由成本条件排除模拟。

**证明。**

对固定映射对取 $g=\mathbf1_E$；$B$ 侧对应 $g\circ G=\mathbf1_{G^{-1}(E)}$，定理 394.3 给出超过 $\varepsilon$ 的总变差。有限输出空间上，总变差又由某个事件达到，因此逐对的事件判据也能检测各对是否满足误差合同。只有量化所有允许映射对，才能推出全方向的不存在性。证毕。

**定理 394.4（模拟边界的组合充分性）。** 本条替代 §330.2 的相应陈述与证明。

两个关系体若具有相同的 $\eta_{\mathrm{sim}}$，则在声明的有限组合合同内具有相同的：
1. 可接受的关系体替代前序及其误差/成本传播；
2. 任意有限串联和并联组合的终端误差上界；
3. 全部有界未来任务的期望差上界；
4. 由事件任务反向检测出的最小模拟误差。

**证明。**
第 1 项由定理 327.2；第 2 项由定理 328.2、定理 394.2 及其联合耦合字段；第 3 项由定理 394.3 和有限 horizon 逐步界；第 4 项先由定理 394.3 对每对满足成本合同的允许映射求最大事件误差，再在所有这些映射对上取下确界。沿组合树归纳，每个节点的翻译、增益和联合耦合字段确定其父节点的误差合同。证毕。

本条所用模拟一律携带定义 327.1 的共同来源对应；不同来源须提供明确状态映射或耦合，复合时这些对应也须相容。输出任务用 $g\circ G$，并联误差用同一个联合耦合；最优模拟误差对全部满足成本合同的允许映射对取下确界，空可行族按无可行模拟处理。

**定理 394.5（模拟摘要的约化与映射合同）。** 本条替代 §330.3 的相应陈述与证明。

完整响应核、允许映射对、成本与任务合同已给定时，逐任务误差和最优模拟误差由 §§327、329 的定义决定，单独删除这些派生数值不损害充分性。反之，只保留原始输出核而隐藏允许映射族及其模拟误差，不能决定接口替代；只保留各组件边缘而联合隐藏联合核、耦合和联合任务值，也不能决定并联替代。固定模拟的误差而联合隐藏实际成本、成本倍率及预算结果，同样不能决定资源可行性。

**证明。**

派生性由对固定映射对计算总变差，再对允许映射对取下确界得到。第一个约化取单状态、单动作、同成本模型 $K_A=\delta_0$、$K_B=\delta_1$：只允许恒等输出映射时误差为一，允许比特翻转时误差为零，原始核与成本相同。第二个约化取公平比特对，一个联合律只支持 $00,11$，另一个只支持 $01,10$；两边缘相同，联合总变差却为一，而恒等联合律与自身的误差为零。成本约化可固定同一个零误差模拟，把调用成本分别设为一和三，预算二时只有前者可行。这些是明确联合约化的反例；原始联合核仍在时，不能声称单独删除耦合或任务值就失去相应分布信息。证毕。

## 395. 归一化相干效果与完整联合态

**定理 395.1（去相干模拟误差的精确值）。** 本条替代 §332.1、§332.2、§332.3、§332.6 的相应陈述与证明。

对任意 Hermitian 算子 $F$，定义
$$
\boxed{\chi_Z(F)=\|F-\Delta_Z^*(F)\|_\infty.}

$$
实际概率任务的效果满足 $0\le F\le I$。设允许控制为酉算子、终端效果满足 $0\le E\le I$，记实际允许的拉回效果集合为
$$
\mathfrak F_{\mathcal U,\mathcal E}
=\{U^\dagger EU:U\in\mathcal U,\ E\in\mathcal E\},
\qquad
\chi_Z(\mathfrak F)=\sup_{F\in\mathfrak F}\chi_Z(F).
$$
空任务族约定残差为零。对每个这样的效果，$0\le\Delta_Z^*(F)\le I$，故 $-I\le F-\Delta_Z^*(F)\le I$，从而 $0\le\chi_Z(\mathfrak F)\le1$。§331.1 的实线性空间仍是 $\mathcal V_{\mathcal U,\mathcal E}=\operatorname{span}_{\mathbb R}\mathfrak F_{\mathcal U,\mathcal E}$；它不用于有限概率误差的上确界。若其中有非零残差，任意实数倍缩放会使该空间上的残差上确界为 $+\infty$。

对任意 Hermitian $F$，
$$
\boxed{
\sup_\rho\left|\operatorname{Tr}(F\rho)-\operatorname{Tr}(F\Delta_Z(\rho))\right|
=\chi_Z(F).
}

$$
因此，对实际允许的归一化效果族 $\mathfrak F_{\mathcal U,\mathcal E}$，所有任务的统一经典模拟误差恰为 $\chi_Z(\mathfrak F_{\mathcal U,\mathcal E})$。

**证明。**

迹配对自伴性给出
$$
\operatorname{Tr}(F\rho)-\operatorname{Tr}(F\Delta_Z(\rho))
=\operatorname{Tr}\bigl((F-\Delta_Z^*F)\rho\bigr).
$$
Hermitian 算子的该绝对期望在密度矩阵上的上确界等于其算子范数，取最大绝对本征值的本征纯态即可达到。再对实际效果族取上确界得到统一误差。证毕。

$\chi_Z(\mathfrak F_{\mathcal U,\mathcal E})=0$ 当且仅当定理 331.2 的经典因子化条件成立。

**证明。**

残差为零等价于每个实际生成效果都由 $\Delta_Z^*$ 固定；由线性性，这又等价于整个实线性张成空间被固定。应用定理 331.2。证毕。

**命题 395.2（小残差只控制声明效果族）。** 本条替代 §332.5 的相应陈述与证明。

若受限归一化效果族 $\mathfrak F_0$ 满足 $\chi_Z(\mathfrak F_0)\le\varepsilon$，该界只控制此族的任务。扩大控制族加入 Hadamard 拉回效果后，可出现残差恰为 $1/2$ 的相位见证；当原族全为对角效果时，残差便从零变为至少 $1/2$。

**证明。**

对原族应用定理 395.1。例 331.4 的拉回效果为 $F=|\psi_+\rangle\langle\psi_+|$，且
$$
F-\Delta_Z^*(F)=\frac12\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$
其本征值为 $\pm1/2$，故残差为 $1/2$。两个相位态之间的任务概率差为一；单个态与其去相干态之间的最坏概率差为 $1/2$，二者是不同的比较。证毕。

**定理 395.3（相干访问与经典访问的严格区别）。** 本条替代 §333.2 的相应陈述与证明。

若存在效果 $E$ 使
$$
E\ne\Gamma_R^*(E),
$$
则存在两个联合态 $X_0,X_1$ 具有相同经典化摘要
$$
\Gamma_R(X_0)=\Gamma_R(X_1),
$$
但给出不同的 $E$ 任务概率。因而只访问经典化参考的边界不能模拟该相干任务。

**证明。**
令 $D=E-\Gamma_R^*(E)\ne0$，直接取 $\Delta=D$。由于 $\Gamma_R$ 是迹配对下自伴且保迹的幂等投影，$\Gamma_R(D)=0$、$\operatorname{Tr}D=0$，且 $\operatorname{Tr}(ED)=\operatorname{Tr}(D^2)>0$。取 $0<t<1/(\dim(\mathcal H\otimes\mathcal R)\|D\|_\infty)$，使
$$
X_\pm=\frac{I}{\dim(\mathcal H\otimes\mathcal R)}\pm t\Delta
$$
仍为密度矩阵。由 $\Gamma_R(\Delta)=0$，两态经典摘要相同；而
$$
\operatorname{Tr}(E X_+)-\operatorname{Tr}(E X_-)
=2t\operatorname{Tr}(D\Delta)\ne0.
$$
证毕。

**命题 395.4（相干边界对实际任务的适用条件）。** 本条替代 §§334.1–334.4 的相应陈述与证明。

原定义 334.1 的“未来拉回效果空间”改为实际归一化拉回效果族 $\mathfrak F$ 及其线性张成：张成用于精确因子化，$\mathfrak F$ 用于统一概率误差。原定理 334.2 的第一项依旧由定理 331.2 决定，第二项使用定理 395.1 的实际效果族，第三项使用完整联合态上的参考访问合同，第四项使用声明方向、允许映射及成本的模拟前序。

对给定态的概率任务，输入是完整联合态 $X$，概率是 $\operatorname{Tr}(EX)$；若比较所有输入的统一误差，须在相同的联合输入域上取上确界。只有系统或参考的边缘相同，不足以代替共同联合态合同，也不能由相同效果族推出两个未指定输入的实际概率相同。

原 §334.3 第 2 项的“残差为一”不作为此相位反例的结论：定理 332.4 的两个态之间概率差为一，而命题 395.2 的单态去相干残差为 $1/2$。在实际效果族和去相干映射保留时，残差按定义可重算，单独删除其缓存没有不充分性见证。其第 1、3、4、5 项分别只针对联合隐藏效果生成数据、参考访问权限、模拟方向或任务量词的约化；由其决定的任务值也须同时隐藏。

具体的同摘要对取 $F_0=I/2$、$F_1=|\psi_+\rangle\langle\psi_+|$，其中 $|\psi_+\rangle=(|0\rangle+|1\rangle)/\sqrt2$。约化只保留共同模式基、$\Delta_Z$、任务标签、经典拉回效果 $\Delta_Z^*F_i=I/2$、参考权限及成本/错误合同；同时隐藏完整效果及其张成空间、残差、相干模拟误差、相干任务值，以及任何能重建效果的控制/终端数据。两者的残差分别为 $0$ 与 $1/2$，约化余项逐项相同。§334.4 因而只以实际效果族中的非对角方向判断经典落点能否精确模拟声明任务；可重算的残差缓存不是额外独立信息。

**证明。** 迹配对从联合态和效果计算当前概率；定理 395.1 从实际效果计算统一误差，定理 395.3 给出相同经典联合摘要而相干效果不同的两态。定理 331.2 的精确判据只用生成效果的线性张成。命题 395.2 的矩阵残差本征值为 $\pm1/2$，其缓存无独立自由度。参考可见性、模拟方向和任务量词则按所声明合同确定可用实验；只有删去相关决定数据的约化才适用这些反例。证毕。

## 396. 合法过程差、受控 tester 与访问概念闭包

**定理 396.1（tester 残余与合法通道切空间）。** 本条替代 §336.2 的相应陈述与证明。

设输入、输出 Hilbert 空间的维数均为正。采用定义 336.1 的未归一化 Choi 约定，合法通道满足 $J\ge0$、$\operatorname{Tr}_B J=I_A$。令
$$
\mathcal L_{\mathrm{ch}}=\{D=D^\dagger:\operatorname{Tr}_B D=0\}.
$$
两个合法通道 $\mathcal E,\mathcal F$ 对所有允许 tester 给出相同概率，当且仅当
$$
\boxed{J_{\mathcal E}-J_{\mathcal F}\in\mathcal V_{\mathfrak T}^{\perp}\cap\mathcal L_{\mathrm{ch}}.}

$$
在全部同型通道组成的模型类上，tester 概率唯一确定通道，当且仅当 $\mathcal V_{\mathfrak T}^{\perp}\cap\mathcal L_{\mathrm{ch}}=\{0\}$。因此 tester 张成整个 Hermitian 空间是充分条件，但不是必要条件。

**证明。**

令 $D=J_{\mathcal E}-J_{\mathcal F}$。合法通道的差必在 $\mathcal L_{\mathrm{ch}}$ 内；概率差为 $\operatorname{Tr}(TD)$，它对所有 $T\in\mathfrak T$ 为零正好等价于 $D\perp\mathcal V_{\mathfrak T}$。交集为零遂给出唯一性。

反之，若交集中有 $D\ne0$，取完全去极化通道的满秩 Choi 矩阵
$$
J_0=I_A\otimes I_B/d_B,\qquad d_B=\dim\mathcal H_B.
$$
选 $0<t<1/(d_B\|D\|_\infty)$，则 $J_\pm=J_0\pm tD$ 均正定，且 $\operatorname{Tr}_B J_\pm=I_A$。它们是不同的合法通道，所有允许 tester 概率却相同。只有正交性而没有切空间条件不足以保证这一构造：二比特情形的 $D=Z_A\otimes I_B$ 与 $I_A\otimes I_B$ 正交，但 $\operatorname{Tr}_B D=2Z_A\ne0$，任意非零扰动都违反通道归一化。证毕。

对受限通道子类，须直接检查该子类的可实现差集合；对多时 comb 或其他过程，须先声明其全部仿射归一化约束以及相应可行差方向，不能直接沿任意 Hermitian 正交方向作扰动。

**推论 396.2（经典 tester 与相干 tester 的区别）。** 本条替代 §336.3、§336.6 的相应陈述与证明。

控制块对角 tester 的张成与纯控制交叉块正交。若某个新增合法相干 tester 与一个可实现过程差的交叉块有非零迹配对，则它区分原对角 tester 无法区分的这对过程；仅有一个形式上的非对角效果，不保证它能区分任意指定的交叉块。

**证明。**

对角块与非对角块的迹配对为零。对新增 tester，非零配对正是这对过程的非零概率差；合法过程差还须满足 §396.1 的相应约束。例 335.4 的受控实现给出严格区别的具体见证。证毕。

因此过程类的可实现盲区是 tester 正交空间与合法过程差方向的交集。对受限类使用其实际差集合，不将全部 Hermitian 正交空间自动称为可实现过程残余。

**定理 396.3（tester 误差的对称支持函数）。** 本条替代 §336.4 的相应陈述与证明。

在有限维 Hermitian 空间中，给定非空有界合法 tester 集 $\mathfrak T$，定义
$$
\|D\|_{\mathfrak T}
=\sup_{T\in\mathfrak T}|\operatorname{Tr}(TD)|,
\qquad
\mathcal C=\overline{\operatorname{conv}}(\mathfrak T\cup-\mathfrak T).
$$
则 $\|D\|_{\mathfrak T}=h_{\mathcal C}(D)$ 是半范数，其零空间是 $\mathcal V_{\mathfrak T}^\perp$。对两个合法过程之差，它恰为所有允许 tester 的绝对概率差上确界；若集合列尽声明合同内的合法二元实验事件，这就是该合同内的最坏事件概率差。

**证明。**

对称化把绝对值上确界化为普通线性泛函上确界；取凸包和闭包不改变该上确界。绝对齐次性和三角不等式逐项成立，有界性保证有限；零点恰与全部 tester 正交。概率解释来自 $p_T(\mathcal E)-p_T(\mathcal F)=\operatorname{Tr}(TD)$。通道 tester 有输入归一化约束，任意差算子的谱投影未必是合法 tester，因此这里不以无约束谱投影替代允许实验。证毕。

**定理 396.4（相干控制产生非对角 tester 的条件）。** 本条替代 §337.4 的相应陈述与证明。

固定控制基 $\{|i\rangle_C\}$，其余过程空间记为 $\mathcal K$，并使用该控制分块的投影与去相干映射
$$
P_i=|i\rangle\langle i|_C\otimes I_{\mathcal K},
\qquad
\Delta_C(T)=\sum_iP_iTP_i.
$$
设原普通 tester 闭包中每个 $T$ 都满足 $\Delta_C(T)=T$。允许加入控制酉 $U_C$ 的后置操作，并记 $U=U_C\otimes I_{\mathcal K}$，其 tester 拉回为 $T'=U^\dagger TU$。若存在原来允许的 tester $T$，使这个合法后继满足
$$
P_iT'P_j\ne0
\quad\text{对某个 }i\ne j,
$$
则扩大后的闭包含有原闭包之外的非对角方向。这里要求该 tester 与旋转的组合合法且在声明深度内；仅有一个非平凡相干旋转不够。

若另有两个合法过程 $J_1,J_2$，满足 $\Delta_C(J_1-J_2)=0$ 且 $\operatorname{Tr}(T'(J_1-J_2))\ne0$，则只保存对角块的边界对该后继合同不充分。这个合法过程对条件不能仅由 tester 非对角性替代；过程差须满足 §396.1 中相应过程类的仿射归一化约束与可实现性要求。

**证明。**
非零的 $P_iT'P_j$ 说明 $T'\ne\Delta_C(T')$，故 $T'$ 不在原对角闭包中，却由允许的拉回属于新闭包。对 $D=J_1-J_2$，定义块 $T'_{ij}=(\langle i|_C\otimes I)T'(|j\rangle_C\otimes I)$，并同样定义 $D_{ij}$。当 $D$ 的对角块为零时，精确配对律为
$$
\operatorname{Tr}(T'D)
=\sum_{i\ne j}\operatorname{Tr}(T'_{ij}D_{ji})
=2\operatorname{Re}\sum_{i<j}\operatorname{Tr}(T'_{ij}D_{ji}).
$$
若此数非零，两个相同对角边界的合法过程给出不同后继概率，由定理 337.2 得不充分性。

一个可直接检验的充分条件是双块 tester
$$
T=
\begin{pmatrix}T_0&0\\0&T_1\end{pmatrix},
\qquad T_0\ne T_1,
$$
以及合法的 Hadamard 控制
$$
H=\frac1{\sqrt2}
\begin{pmatrix}1&1\\1&-1\end{pmatrix}.
$$
逐块相乘得
$$
(H^\dagger\otimes I)T(H\otimes I)
=\frac12
\begin{pmatrix}
T_0+T_1&T_0-T_1\\
T_0-T_1&T_0+T_1
\end{pmatrix},
$$
所以非对角块恰为 $(T_0-T_1)/2\ne0$。

反之，若 $\mathcal V=\operatorname{span}_{\mathbb R}\{I_C\otimes T_0\}$，则对每个控制酉都有
$$
(U_C^\dagger\otimes I)(I_C\otimes T_0)(U_C\otimes I)
=I_C\otimes T_0.
$$
即使允许全部控制酉，该空间也不扩大。有限例子是二维控制、$\mathcal K=\mathbb C$、$T_0=1$，tester 只有恒真效果 $I_C$ 及零效果：加入 Hadamard 仍不能产生非对角 tester。证毕。

**命题 396.5（同一当前记录、不同可继续性）。** 本条替代 §337.5 的相应陈述与证明。

取输入一维、输出为二维控制的两个态准备通道，其 Choi 算子为
$$
J_\pm=|\pm\rangle\langle\pm|
=\frac12
\begin{pmatrix}1&\pm1\\\pm1&1\end{pmatrix}.
$$
当前允许 tester 为 $P_0=|0\rangle\langle0|$ 和 $P_1=|1\rangle\langle1|$。合同 $M_1$ 只允许对角控制酉作为后继，合同 $M_2$ 还允许相对于此固定基的 Hadamard 后置操作。两个通道的当前概率都为 $(1/2,1/2)$；$M_1$ 的后继仍不可区分它们，$M_2$ 的一次后继则可区分。

**证明。**
两矩阵正且迹为一，故是合法态准备通道。对角酉共轭保持 $P_0,P_1$，而
$$
H^\dagger P_0H=|+\rangle\langle+|,
\qquad
\operatorname{Tr}(H^\dagger P_0H J_+)=1,
\quad
\operatorname{Tr}(H^\dagger P_0H J_-)=0.
$$
这里 $P_0$ 的两个标量块为 $1,0$，满足定理 396.4 的不等块条件，且合法过程差与新 tester 的配对非零。因此相同当前记录不能决定允许 Hadamard 后的区分任务；两合同的后继闭包也确实不同。证毕。

**定理 396.6（高阶边界的条件充分性）。** 本条替代 §338.2 的相应陈述与证明。

两个过程关系体若具有相同的 $\eta_{\mathrm{higher}}$，则在声明的有限控制深度和 tester 合同内，具有相同的：
1. 普通黑箱任务与相干控制任务的可辨识性；
2. 当前与后继 tester 的正交空间及其可实现过程差残余；
3. 过程替代、串联和控制组合的误差/成本界；
4. 粒子式终端事件与过程级相干任务之间的可恢复映射。

**证明。**
第 1 项由定义 335.1 和定理 396.1；第 2 项由定理 337.2 的闭包正交判据及推论 337.3。定理 396.4 在其非对角拉回条件成立时给出抽象 tester 闭包的严格扩大，非平凡控制酉本身不保证扩大；要进一步得到合法过程的实际可区分性，还须存在该定理所要求的合法过程对，其差满足 §396.1 的相应约束，并与新增 tester 有非零配对。第 3 项由接口模拟的误差传播和过程交叉块字段；第 4 项由终端效果 tester 与控制 tester 的联合张成关系。对有限控制深度按组合树归纳即可。证毕。

**定理 396.7（高阶边界的派生闭包与约化）。** 本条替代 §338.3 的相应陈述与证明。

若当前 tester 族和允许组合操作及深度均保留，后继闭包由定义 337.1 确定，单独删除闭包字段不影响充分性。若完整 Choi 数据和合法 tester 均保留，所有当前概率及 tester 残余也可重建。

相反，只保留普通通道与控制对角记录、联合隐藏交叉块及其相干任务值的摘要，不足以决定相干控制任务。若只保留当前概率而隐藏未来允许操作、参考访问权限、后继闭包及其任务值，也不能决定未来可辨识性。若只保留过程和 tester 的无预算概率而隐藏调用成本及预算结果，也不能决定预算可行性。

**证明。**

前两项由闭包的生成定义和迹配对直接得到。第一个约化取例 335.4 的两组实现；普通通道和控制对角块完全相同，在共同允许的相干 tester 下概率分别为一和零。第二个约化固定同一对实现与当前经典 tester，比较只允许对角控制和还允许 Hadamard 后继的两个权限合同；当前概率相同，而后者有上述区分任务。参考访问权限决定新增的相干操作是否可用，适用同一约化。对成本约化，固定一个可区分上述实现的 tester，在两合同中给它分别指定成本一与二；无预算概率相同，预算一的可行性不同。若剩余字段仍包含决定被删量的完整操作、成本或 Choi 数据，这些约化反例就不适用。证毕。

**定理 396.8（完整访问列表重构概念字段）。** 本条替代 §§339.5–339.6、340.7、342.3 的相应信息损失断言，并限定 §§342.1–342.4 的字段与消费者合同。

固定有限访问偏序 $(\mathfrak A,\preceq)$、任务全集 $\mathfrak T$ 及其标签。每个访问的完整索引列表

$$
\operatorname{Rec}(A)=\{\phi\in\mathfrak T:A\,I\,\phi\}
$$

等价于完整 incidence。对任意访问族 $\mathcal X$ 和任务族 $\Phi$，

$$
\mathcal X'=\bigcap_{A\in\mathcal X}\operatorname{Rec}(A),
\qquad
\Phi'=\{A\in\mathfrak A:\Phi\subseteq\operatorname{Rec}(A)\}.
$$

空访问族的交集取 $\mathfrak T$，空任务族的导出取 $\mathfrak A$。两侧导出、双重闭包、形式概念、伴随任务内涵及 $\operatorname{MinAcc}(\Phi)=\min_{\preceq}\Phi'$ 均可重算，不须各自另存缓存。若每个任务的充分访问集向上闭合，保留每个任务的全部极小访问列表 $\mathcal M_\phi$ 及该有限偏序，也有

$$
A\,I\,\phi
\quad\Longleftrightarrow\quad
\exists M\in\mathcal M_\phi,\ M\preceq A.
$$

不可恢复任务的列表为空。这一逐任务、带标签的完整族仍确定全部 incidence；只保留一个最便宜方案或不完整列表才可能遗漏替代访问。若全部阈值 incidence 与成本也保留，阈值概念及成本—误差前沿同样可重算；用极小访问计算最小成本还须成本随细化不减，空可行族成本为 $+\infty$。

以下约化联合删除决定数据及其派生答案，才有固定余项下的反例：

1. 只保留访问/任务标签、偏序、单位成本和每行任务数量，隐藏具体 incidence、完整列表、实际读取映射、最小访问及所有闭包/概念。取全部二比特来源、任务 $\phi=s_1,\psi=s_2$ 和两个在声明权限偏序中不可比的访问 $A_1,A_2$。模型 M 的两访问都只读取 $s_1$；模型 N 的 $A_1$ 读取 $s_1$、$A_2$ 读取 $s_2$。每行任务数均为一，但 $\{A_1,A_2\}'$ 在 M 为 $\{\phi\}$，在 N 为空。声明的权限偏序相同，不把模型 M 中额外存在的读数等价误作不同的权限偏序。
2. 只保留精确 incidence、单位访问成本和共同损失合同，隐藏通道核、正误差风险、阈值 incidence、阈值概念及成本—误差前沿。对均匀隐藏比特、单次二元对称读出和零一损失，翻转率分别为 $1/4$ 与 $1/3$ 的两模型均不能精确恢复；在阈值 $3/10$ 下只有前者足够。
3. 只保留当前 incidence、当前概率、成本与共同预算/终止规则，隐藏未来允许操作及其 tester 闭包、可继续性标签和任务值。固定例 331.4 的相位二态及当前模式测量：一合同只允许继续模式测量，另一合同还允许 Hadamard 后测量。两者当前读数相同，后者可精确区分两态而前者不能。保留的终止规则只规定共同的一步预算，不含已删除的动作权限。

**证明。** $\phi\in\operatorname{Rec}(A)$ 恰为 $A I\phi$，故两个导出公式直接给出定义 339.1，迭代得到双重闭包及概念。有限上闭集的每个元素都位于某个极小元之上，证明逐任务最小列表的重构式；对阈值逐一应用同一公式，再依成本合同取最小值即可。第 1 对模型的两行分别为 $(\{\phi\},\{\phi\})$ 与 $(\{\phi\},\{\psi\})$，行数摘要相同而交集不同。第 2 对模型中，给定读数的后验正确概率为 $1-p>1/2$，最优判决复述读数，风险分别为 $1/4$、$1/3$，位于 $3/10$ 两侧。第 3 对模型的模式读数均为公平比特，Hadamard 后对应概率为一与零。故 §§339.5–339.6、340.7、342.3 中针对完整列表或仅删闭包缓存的笼统损失结论不成立；§342.2 的充分性使用完整决定数据和明确的未来合同。证毕。

**命题 396.9（联合任务反链不同于逐任务超图）。** 本条替代 §340.6，并限定 §§342.1–342.3 的“最小访问反链”。取全部二比特来源 $(s_1,s_2)\in\{0,1\}^2$，组件全集 $U=\{u_1,u_2\}$，其中 $u_i$ 读取 $s_i$。令 $\phi=s_1\mathbin{\mathrm{XOR}}s_2$、$\psi=s_1$。则

$$
\operatorname{MinAcc}(\{\phi\})=\{U\},\qquad
\operatorname{MinAcc}(\{\psi\})=\{\{u_1\}\},\qquad
\operatorname{MinAcc}(\{\phi,\psi\})=\{U\}.
$$

逐任务索引的超图可以分别给 $\phi$ 标记 $U$、给 $\psi$ 标记 $\{u_1\}$；二者属于不同任务。由于 $\{u_1\}\subsetneq U$，把这两条边合并后不是一个访问反链，更不是联合任务族的最小访问反链。一般的联合充分访问先取各任务充分访问集的交，再取其中极小元，不能直接合并各任务的极小元。

**证明。** 真子集访问遗漏至少一个比特；固定已读比特并翻转遗漏比特会改变 parity，所以 $\phi$ 只由 $U$ 恢复。$\psi$ 恰由包含 $u_1$ 的访问恢复。联合任务必须满足 parity 的全集要求，而 $U$ 也恢复 $\psi$，故联合极小族仍是 $\{U\}$。这保留了 §340.6 的单 parity 结论，替代其关于加入 $\psi$ 后出现两条不可比访问的断言。§342 的逐任务字段使用有任务标签的超图；联合任务字段使用所选任务族的极小访问，两者都由定理 396.8 的 incidence 重建。证毕。

## 397. 下降、树规范与曲率路径的更正

**定理 397.1（下降字段的可重构性与分组约化）。** 本条替代 §346.3 的相应陈述与证明。

设局部可行截面集为 $\mathcal S_i$，重叠限制为 $R_{ij}$，覆盖神经为 $\mathcal N$。定义

$$
\mathcal G
=\left\{(s_i)_i\in\prod_i\mathcal S_i:
R_{ij}s_i=R_{ji}s_j\ \text{对所有重叠 }(i,j)\right\},
$$

在限制数据给出可沿路径复合的运输合同中，把每条闭路复合 $R_{\ell}$ 的残差记为 $\mathsf{LoopRes}_{\ell}$。则 $\mathcal G$ 的非空性、拼接数目和所有闭路残差，都是
$(\{\mathcal S_i\},\{R_{ij}\},\mathcal N)$ 的确定函数；在固定边误差、路径增益和度量后，误差传播也由同一组数据逐路径计算。依定义 384.2 的固定余项合同，单独删除缓存的“全局拼接集合”或“循环障碍”不能改变答案。

真正的字段约化必须删除限制映射或其他决定数据。取两个覆盖片、重叠 $W=\{*\}$ 上的取值空间为 $\{0,1\}$，$\mathcal S_1=\mathcal S_2=\{0,1\}$，并固定局部截面 $s_1=s_2=0$。模型 A 取 $R_{12}=R_{21}=\mathrm{id}$，给定局部族 $(0,0)$ 相容；模型 B 取 $R_{12}=\mathrm{id}$、$R_{21}(x)=1-x$，同一给定局部族不相容。这里比较的是固定局部族的拼接见证集合 $\mathcal G\cap\{(0,0)\}$，分别为单点与空集；模型 B 在不固定局部值时的 $\mathcal G$ 仍含 $(0,1),(1,0)$。约化摘要只保留共同覆盖神经、重叠 $W$ 与取值空间、局部集合、给定元组 $(0,0)$、离散度量，以及任务“$\mathcal G\cap\{(0,0)\}$ 是否非空”、零误差合同、单位查询成本和查询后停止规则；联合隐藏限制映射、相容性答案、$\mathcal G$ 及其拼接见证、闭路残差和任何编码该答案的缓存。每个保留分量在 A、B 中都相同，而给定局部族的拼接可行性不同。若限制映射仍保留，这些集合与残差只是可重算字段；本例不声称模型 B 的整个 $\mathcal G$ 为空。

未来 tester 与资源/停止后继则属于另一组独立合同：固定上述下降数据而只把 tester 的下一步允许动作改为“可继续”或“停止”，即可得到不同的未来任务树。

**证明。**

$\mathcal G$ 是限制相容方程的解集，闭路复合是这些方程沿 $\mathcal N$ 的有限复合；因此它们由保留的限制映射和覆盖神经确定。路径误差界是边误差与路径增益的有限合成，适用定义 384.2 的固定余项原则。两片覆盖的两个显式模型给出固定局部族的非空与空拼接见证集；删除组包含限制映射及其全部相容性派生答案，所列余项逐项相同。最后一项只改变未来合同，保持当前下降数据不变。证毕。

**推论 397.2（最坏根值下的必要边误差）。** 本条替代 §348.1、§348.3 的相应陈述与证明。

沿用原定义 348.1 的 $r_C(x)=\|x-H_Cx\|$。只有在线性等距作用下才使用算子残差 $\chi_C=\|I-H_C\|_{\mathrm{op}}$。

设 $F$ 是非零有限维赋范空间，群作用由线性等距算子给出，则
$$
\max_{\|x\|=1}r_C(x)=\chi_C.
$$
设闭路长度为 $m>0$。对每个单位根值 $x$，在所有根值固定为 $x$ 的顶点赋值中优化平均边误差，仍有
$$
\sup_{\|x\|=1}\ \inf_{(x_i):x_{i_0}=x}
\frac1m\sum_{e\in C}\delta_e
\ge\frac{\chi_C}{m}.
$$
这是最坏根值所需误差的下界；对一个具体根值只有 $r_C(x)/m$ 的下界。即使 $\chi_C>0$，holonomy 的单位固定向量也可满足 $r_C(x)=0$。

**证明。**

单位球面的紧性使算子范数由某个根值达到。对每个固定根值，定理 348.2 给出所有顶点赋值的平均误差至少为 $r_C(x)/m$；先取下确界，再对根值取上确界即得。证毕。

**定理 397.3（树规范与定向基本闭路）。** 本条替代 §348.4、§351.1 的相应陈述与证明。

对连通有限图及一棵根为 $r$ 的生成树，采用 §347.4 的规范 $g'_{ij}=h_i g_{ij}h_j^{-1}$，可把所有树边化为恒等。固定根坐标后，每条定向非树边 $i\to j$ 的新运输等于从根沿树到 $i$、经该边到 $j$、再沿树返回根的基本闭路 holonomy。反向该边得到逆元；改变根坐标使全部根闭路 holonomy 同时共轭。

**证明。**

显式递推
$$
h_r=1,\qquad h_j=h_i g_{ij}
\quad\text{当 }i\text{ 是 }j\text{ 的树父节点时}.
$$
故 $h_i$ 是沿根到 $i$ 的有向树路径按序相乘的运输，且
$$
g'_{ij}=h_i g_{ij}(h_i g_{ij})^{-1}=1
$$
对所有树边成立。若 $i\to j$ 是非树边，则 $g'_{ij}=h_i g_{ij}h_j^{-1}$ 正是上述定向根闭路的原 holonomy。若改令 $h_r=a$，递推所得 $h_i$ 同时左乘 $a$，全部非树边元变为 $a g'_{ij}a^{-1}$。任意闭路可由这些基本闭路及其逆元组合，所以它们在固定树与根坐标下保存全部运输信息，剩余规范自由度是同时共轭。证毕。

原 §351.1 的约定 $g_e^h=h_{s(e)}^{-1}g_eh_{t(e)}$ 使用这里规范参数的逆元；其面 holonomy 变为 $h_{v_0}^{-1}H_fh_{v_0}$，描述的是同一规范轨道。树递推必须与所用约定成对使用，不能把两套参数混用。

**定理 397.4（闭路任务的最小运输信息）。** 本条替代 §349.5 的相应陈述与证明。

对固定覆盖图和群作用，若未来任务只依赖规范不变量的闭路运输，则保存生成树规范后的非树边运输元足以恢复全部闭路任务；若某条非树边可独立取两个被声明闭路任务区分的值，则联合隐藏该边及其派生 holonomy 和任务值后，会产生不可识别的运输对。

**证明。**
充分性由定理 397.3：所有闭路运输由基本闭路生成。在附加的可区分性假设下，令该边取所述两个值，其余树规范边元不变；约化摘要只保留其余边元与共同任务合同，故摘要相同而该任务结果不同。若群平凡、作用不忠实或允许任务不区分这两个值，不能推出必要性；保留该边的 holonomy 派生字段时也不构成信息删除。证毕。

**定理 397.5（运输派生字段与联合约化）。** 本条替代 §350.3 的相应陈述与证明。

固定图、完整边运输、群作用、纤维范数及任务合同时，基本闭路 holonomy、规范轨道和 holonomy 残差均为派生量。单独删去其中一个缓存字段，定理 350.2 的充分性仍成立。若仅保留局部事件核、图、群作用及共同闭路任务，而联合隐藏边运输与其派生量，则存在相同约化摘要、不同闭路任务的关系体。

**证明。**

holonomy 是边运输的有序乘积，规范轨道由规定的群作用确定，残差由该乘积及范数计算，故相同原始字段决定相同派生字段。对联合约化取三角图、$G=\{1,-1\}$ 的一维作用、恒输出零的局部事件核和任务“闭路乘积是否为一”。一份运输的三条边均为一，另一份只有一条边为负一；约化摘要完全相同，闭路任务却不同。这一见证同时隐藏了决定 holonomy 的边运输，不能用于证明完整边界中单独 holonomy 字段的必要性。证毕。

**定理 397.6（非平凡表示下的拓扑 holonomy 见证）。** 本条替代 §352.4、§353.7 的相应陈述与证明。

设 $K$ 是有限连通二维复形，并假定存在表示 $\rho:\pi_1(K,v_*)\to G$ 和根闭路 $c$ 满足 $\rho([c])\ne1$。则存在两个 flat 边运输 $g,g'$，其所有面 holonomy 都为单位元，而
$$
T_g(c)\ne T_{g'}(c).
$$
仅有 $\pi_1(K)$ 非平凡不足以推出给定 $G$ 上的这种见证。

**证明。**

分别取平凡表示与假设给定的 $\rho$，由定理 352.2 实现为 flat 边运输。每个面边界在基本群中为单位元，所以两份面 holonomy 相同；闭路 $c$ 的运输分别为 $1$ 和 $\rho([c])\ne1$，且单位元不与非单位元共轭。

若 $G=\{1\}$ 或 $\operatorname{Hom}(\pi_1(K),G)$ 只有平凡表示，则这样的运输对不存在。特别地，映到 $U(1)$ 的表示经基本群的阿贝尔化分解；不能由基本群非平凡就断言存在非平凡 $U(1)$ 特征。例 352.3 的环面基本群为 $\mathbb Z^2$，环带基本群为 $\mathbb Z$，在这些具体情形才可按其关系选择所述非平凡相位。证毕。

原说明 353.7 的拓扑例外因此只在上述非平凡表示假设下成立。定理 353.3 仍控制由面填充的闭路：面残差沿填充给出上界；相应非可缩闭路的 holonomy 不由这些面残差单独控制。

**定义 397.7（曲率感知边界）。** 本条替代 §§354.1、354.4–354.5 的相应合同。

固定有限二维复形 $K$、群 $G$、双不变度量 $d$、局部纤维的群作用和声明的事件任务；各连通分支分别选根，根值与基本群任务按分支解释。沿用 §§347.1、397.3 的下标与规范约定，$x_i=g_{ij}\cdot x_j$，路径边词 $p=e_1\cdots e_m$ 的乘积为

$$
\operatorname{Hol}_g(p)=g_{e_1}\cdots g_{e_m},\qquad
\operatorname{Hol}_{g^h}(p)
=h_{s(p)}\operatorname{Hol}_g(p)h_{t(p)}^{-1},
\quad h=(h_v)_{v\in V}\in\mathcal G_K:=G^V.
$$

这里 $s(p),t(p)$ 是该有序边词的首尾顶点，与 $g_{ij}$ 的左右下标一致。$[\operatorname{Hol}_{\mathrm{path}}(g)]$ 表示所有路径在同一组 $h_v$ 下的联合规范类，等价于完整 $[g]$，不是各条路径分别取轨道后的列表。闭路受根处共轭，开路径受两个端点的左右作用；后者不指定原始群元。

$\mathsf E$ 保存事件所需的当前态/截面或任务相对充分数据、效果、记录—后继核及读取运输代表的协变规则，不重复存储 $g$ 的数值。记录字母和任务标签固定；状态、截面、效果与事件核须随 $g$ 使用同一个 $h$。以 $D$ 表示可测后继集合，这一合同要求

$$
\mathsf K_{g^h,\mathsf E^h}(y,h\cdot D\mid h\cdot x)
=\mathsf K_{g,\mathsf E}(y,D\mid x).
$$

因此采用联合运输—事件类

$$
\mathsf Q_{\mathrm{curv}}
=[(\operatorname{Hol}_{\mathrm{path}}(g),\mathsf E)]_{\mathcal G_K},
\qquad
\boxed{\eta_{\mathrm{curv}}
=\left(K,\mathsf Q_{\mathrm{curv}},\{[H_f]\}_{f\in F},
\mathsf{Err},\mathsf{Stop}\right).}
$$

边界相等由同一个顶点规范同时识别运输及事件数据；分别选择两个字段的轨道代表不满足该合同。$\mathsf{Err},\mathsf{Stop}$ 和所报告的数值任务均须对共同作用不变，坐标化后继只报告规范类。面共轭类由联合路径字段重算；完整边运输保留时，路径字段也是可重算缓存。

在曲率不为零时保留联合路径类。只有所有面满足 $H_f=1$ 或另有明确的基本群因子化合同时，才定义 $\rho_g([c])=\operatorname{Hol}_g(c)$，并报告其表示共轭类 $[\rho_g]$。原 §354.4 的事件链也按这一共同规范合同解释。若任务要求开路径原始群元，须额外保留端点坐标框架，或把允许规范限制为固定这些框架的子群；该带框架任务不由上述无框架边界提供。若 $\mathsf E$ 复制了运输数值，则它是决定数据，在删除运输的约化中必须一并隐藏。

**定理 397.8（曲率感知边界的条件充分性）。** 本条替代 §354.2 的相应陈述与证明。

若两个有限关系体具有相同的 $\eta_{\mathrm{curv}}$，且局部事件、有限运输、面约束、路径/基本闭路检验和误差/停止任务满足定义 397.7 的共同规范合同，则它们给出相同的不变量结果及规范等价的后继：

1. 面 flatness 与近似 flatness 判定；
2. 全局截面存在性、根值解集的对应与多重性及规范不变的失败原因；
3. 可缩闭路的曲率残差上界与边修正下界；
4. 声明路径族的联合 holonomy 规范类及任务指定的不变量值；在 flat 或显式因子化 sector 中，进一步给出基本群表示的共轭类；
5. 沿合法路径运输的事件记录概率及条件后继的规范类；
6. 在不变预算与停止规则内可继续的合法任务树。

**证明。** 同一联合类给出一个同时识别全部运输、状态与事件数据的 $h$。沿路径相邻规范因子相消，给出定义 397.7 的端点公式；面残差因双不变度量而不变，故第 1 项成立。第 2 项一般使用定理 347.2 的全部根闭路固定点条件，$x_i\mapsto h_ix_i$ 把解截面双射到另一模型；仅在 flat 的单纯连通情形才使用定理 351.3，在其余 flat 情形按定理 352.2 的表示合同处理。第 3 项由定理 353.3、353.6 及同一不变度量。第 4 项直接使用联合路径规范类；满足因子化假设时由定理 351.2 得到 $[\rho_g]$。第 5 项由共同协变核的等式求和/积分得记录概率相同，正概率记录下的归一化后继相互推前；零概率记录无须选择条件态。第 6 项沿有限策略树归纳，每步使用相同不变量记录、协变后继与不变的合法性/停止规则。证毕。

原始开路径值不下降到此边界。取填充三角形、$G=\{+1,-1\}$，按边 $12,23,31$ 排列，

$$
g=(1,1,1),\qquad g'=(-1,-1,1),\qquad h=(1,-1,1).
$$

逐边有 $g'_{ij}=h_i g_{ij}h_j^{-1}$，面乘积均为一。取共同的单点事件状态、恒定事件核与不变误差/停止合同，两者的联合边界相同，但边词 $12$ 的原始值分别为 $1$ 与 $-1$。这直接排除从无框架轨道读取唯一原始开路径值；有端点框架时才可提出这样的数值任务。

**定理 397.9（曲率字段的可重构性与真实约化）。** 本条替代 §354.3 的相应陈述与证明。

由边路径字段有恒等式

$$
H_f=\operatorname{Hol}_g(\partial f),\qquad
\rho_g([c])=\operatorname{Hol}_g(c)\quad\text{（仅在 flat/因子化 sector）}.
$$

两式先在同一运输代表上计算，下降后给出面共轭类、联合路径规范类及 flat sector 的 $[\rho_g]$。保留定义 397.7 的运输—事件联合类时，删除这些派生缓存不改变其声明的不变量任务结果；这不从轨道重构原始开路径群元。

一个真正的约化必须删除路径运输字段并固定其余摘要。取环面模型 $G=U(1)$，一顶点两边 $a,b$ 和一面 $aba^{-1}b^{-1}$。两组边运输

$$
(g_a,g_b)=(1,1),\qquad
(g'_a,g'_b)=(e^{i\alpha},1),\quad \alpha\notin2\pi\mathbb Z
$$

都有相同的面 holonomy $H_f=1$、相同的 $K$、单点事件状态、恒定事件核和不变的 $\mathsf{Err},\mathsf{Stop}$，但基本闭路 $a$ 的 holonomy 分别为 $1$ 与 $e^{i\alpha}$；在阿贝尔群中这是规范不变量。因此，联合隐藏运输—事件类中的运输部分、完整边/路径数据、$[\rho_g]$ 及相关任务值，只保留上述面缓存和相同事件/资源合同，便得到同余项而全局任务不同的两个实现。

事件—运输核、误差合同和停止后继仍是独立字段：分别固定路径数据而改变接口运输核、允许修正半径或继续预算，就得到相同当前局部数据而不同的相应任务后继。

**证明。**

两式中的第一式是路径乘积沿面边界的定义，第二式由定理 351.2 的 flatness 因子化条件给出。完整联合路径规范类固定时，面共轭类与因子化 sector 的基本群表示共轭类都是其函数。环面两组运输因 $U(1)$ 阿贝尔而均 flat，面词乘积为 $1$，但 $a$ 环路值不同；这保持了删除路径字段后的所有列明摘要而改变了全局任务。其余三项只改变各自明确的未来合同。证毕。

## 398. 三维曲率与 Hodge 当前数据

**定义 398.1（三维曲率全息边界）。** 本条替代 §§358.1、358.4–358.5 的相应合同。

固定有限三维 CW 复形 $K$、阿贝尔系数群 $A$ 及上链映射 $d$，满足 $d_2d_1=d_1d_0=0$；另有边运输群 $G$ 时也须声明其与系数的对应。$\mathsf{SurfEvt}$ 保存表面事件所需的当前数据、效果、读出规则、钟标签与记录后继，并继承定义 397.7 的共同规范协变合同。取

$$
\mathsf Q_3=[(g,\mathsf{SurfEvt})]_{\mathcal G_K}.
$$

它保留运输与事件数据在同一顶点规范下的联合类；不提供无端点框架的原始开路径值。事件规则不另存这些运输数值，数值任务、误差和停止规则均为共同规范不变量。

测量上链 $F_{\mathrm{cur}}\in C^2(K;A)$ 保存在固定胞腔定向与系数坐标中，作为顶点规范不变数据。对任意这样的 $F$，定义带标签字段

$$
\mathsf{Coh}_2(F)=
\begin{cases}
(\mathrm{closed},[F]_{H^2}),&d_2F=0,\\
(\mathrm{nonclosed},d_2F),&d_2F\ne0,
\end{cases}
\qquad H^2=\ker d_2/\operatorname{im}d_1.
$$

非闭合分支只记录 Bianchi 残差，不定义 $[F]_{H^2}$。三维边界为

$$
\boxed{
\eta_{\mathrm{3curv}}
=\left(K,A,d,\mathsf Q_3,F_{\mathrm{cur}},d_2F_{\mathrm{cur}},
\mathsf{Coh}_2(F_{\mathrm{cur}}),H^1,
\mathsf{Err}_3,\mathsf{Stop}\right),
\qquad H^1=\ker d_1/\operatorname{im}d_0.
}
$$

只有明确声明当前测量等于实际阿贝尔边运输曲率，即 $g\in C^1(K;A)$ 且 $F_{\mathrm{cur}}=d_1g$ 时，才有

$$
d_2F_{\mathrm{cur}}=0,\qquad
\mathsf{Coh}_2(F_{\mathrm{cur}})=(\mathrm{closed},0).
$$

独立测量不必等于 $d_1g$，也不必闭合；即使它可由某个边势实现，也未必是当前 $g$ 的曲率。若 $G$ 非阿贝尔，仅对明确声明的阿贝尔系数或中心部分使用这一上链模型；不能把一般非阿贝尔面值直接当作 $d_1g$，也不能用这里的 $H^1$ 分类非阿贝尔运输解。

非闭合的有限见证：给 $S^2$ 沿度一恒等映射附加一个三胞腔，得到闭三维球 $D^3$ 的 CW 结构。取实系数，则 $C^1=0$、$C^2=C^3=\mathbb R$、$d_1=0$、$d_2=\mathrm{id}$。测量 $F_{\mathrm{cur}}=1$ 的字段为 $(\mathrm{nonclosed},1)$；实际 $d_1g$ 只能为零。虽然 $H^2=0$，非闭合测量 $1$ 仍没有 $H^2$ 类，因为它不属于 $\ker d_2$。

§§358.4–358.5 的表面事件链及其全息解释据此使用“先判闭合，再判可实现性，有解后再分类”的分支，事件概率与后继分别按不变量与联合规范类报告。

**定理 398.2（三维曲率边界的条件充分性）。** 本条替代 §358.2 的相应陈述与证明。

若两个有限关系体具有相同的 $\eta_{\mathrm{3curv}}$，且有限运输、面/表面事件、三胞腔闭合、误差和停止任务遵守定义 398.1 的共同规范合同，则其不变量结果相同，后继规范等价。上同调可实现性与解族分类专指下列阿贝尔方程，不向一般非阿贝尔边运输外推：

$$
\mathcal S_F=\{a\in C^1(K;A):d_1a=F\}/\operatorname{im}d_0.
$$

具体任务为：

1. 测量面上链与三胞腔 Bianchi 残差；
2. 测量曲率的阿贝尔可实现性：非闭合时不可实现，闭合后才按 $H^2$ 类是否为零判定；
3. 不可实现时的空解集，或可实现时解集模规范的 $H^1$ 仿射残余；
4. 实际边运输的表面边界不变量，以及独立测量在不同填充上的配对与 Bianchi 残差；
5. 表面事件沿合法路径运输后的不变量记录概率及条件后继规范类；
6. 在不变误差预算内的修正下界与可继续任务树。

**证明。** 第 1 项由 $F_{\mathrm{cur}}$ 和 $d_2$ 直接计算。若 $d_2F\ne0$，由 $d_2d_1=0$ 得方程无解；若 $d_2F=0$，$[F]_{H^2}=0$ 恰表示 $F\in\operatorname{im}d_1$。有解时选一个 $a_0$，全部解为 $a_0+\ker d_1$，再模 $\operatorname{im}d_0$ 得 $H^1$ 挠集；不选 $a_0$ 就没有指定原点的同构，无解时也不赋予非空 $H^1$ 残余。这给出第 2、3 项。只有明确满足 $F_{\mathrm{cur}}=d_1g$ 的 sector，才可从当前 $[g]$ 重算该测量字段。

第 4 项中实际运输的路径任务由联合类给出。对阿贝尔测量和同边界的两条二链 $S,S'$，配对差是 $\langle F,S-S'\rangle$；若 $S-S'=\partial V$，它等于 $\langle d_2F,V\rangle$。只有 $F=d_1g$ 时，才将 $\langle F,S\rangle$ 认作实际边运输的 $\langle g,\partial S\rangle$；独立测量的非零 Bianchi 残差不能被这一身份抹去。第 5 项用定义 397.7 的共同协变核，同一规范同时运输状态、效果和后继，记录概率不变；正概率条件后继相互推前。第 6 项使用不变误差/停止合同沿有限树归纳；涉及 $H^2$ 距离的任务只在闭合分支定义，非闭合分支先报告 Bianchi 残差或声明的闭合修正任务。证毕。

**定理 398.3（三维字段的重构与真实约化）。** 本条替代 §358.3 的相应陈述与证明。

保留 $K,A,d$ 和实际测量 $F_{\mathrm{cur}}$ 时，$d_2F_{\mathrm{cur}}$、带标签的 $\mathsf{Coh}_2(F_{\mathrm{cur}})$ 与 $H^1$ 均可重算，只有闭合分支产生 $H^2$ 类。只有在明确声明 $F_{\mathrm{cur}}=d_1g$ 时，才可改从完整 $[g]$ 重算曲率字段；独立测量不能由 $[g]$ 代替。删除这些派生缓存不会改变定义 398.1 的任务。

真正的约化须固定余项并删除决定数据。取环面与三维球面的楔和这一有限三维 CW 模型、$A=\mathbb R/2\pi\mathbb Z$，并固定

$$
F_{\mathrm{cur}}=0,\qquad d_2F_{\mathrm{cur}}=0,\qquad
\mathsf{Coh}_2(F_{\mathrm{cur}})=(\mathrm{closed},0),\qquad
H^1\cong A\oplus A.
$$

用 $t\mapsto e^{it}$ 把运输写成乘法记号，两组边运输 $(g_a,g_b)=(1,1)$ 与 $(e^{i\alpha},1)$，$\alpha\notin2\pi\mathbb Z$，具有相同的这些字段、单点事件状态、恒定 $\mathsf{SurfEvt}$ 以及不变的 $\mathsf{Err}_3,\mathsf{Stop}$，但基本闭路 $a$ 的 holonomy 不同。联合隐藏 $\mathsf Q_3$ 中的运输部分、完整 $[g]$、边路径数据、当前 $H^1$ 解族中的实际点及相关任务值，只保留上述共同曲率/上同调数据和事件/资源合同，便丢失了这一全局边运输任务。保留 $H^1$ 群或其秩不等于保留其中的当前运输类。

表面事件核、三维误差合同和停止后继仍是独立合同：固定曲率/运输数据而分别改变它们，可以得到不同记录、修正下界或继续树；每次约化须连同被删合同的派生任务值一起隐藏。

**证明。** 第一段逐项按 $d_2$、定义 398.1 的分支以及上链核/像计算；度一附胞腔的例子说明非闭合输入不能进入 $H^2$ 商。楔和中的三胞腔不改变环面的一维上同调，两组阿贝尔运输均有零曲率；其闭路 $a$ 的值分别为 $1$ 与 $e^{i\alpha}$，在顶点规范下不变。因此同一列明余项不能恢复被删的当前运输类。其余约化分别改变事件、误差或资源合同，不以删除可重算缓存充作见证。证毕。

**定义 398.4（Hodge 感知边界）。** 本条替代 §362.1 的相应陈述与证明。

固定有限胞腔复形 $K$、实系数上链、正定上链内积 $\mathbf G=(\langle\cdot,\cdot\rangle_k)_k$、满足 $d_{k+1}d_k=0$ 的上链映射及允许的曲率和事件接口。定义

$$
\boxed{
\eta_{\mathrm{Hodge}}=
\left(
K,\mathbf G,d,\delta,\Delta,\operatorname{spec}\Delta,
F_{\mathrm{cur}},\mathcal C^1,\mathcal H^1,\Pi,p_{\mathrm{cur}},
\mathsf{Event},\mathsf{Err},\mathsf{Stop}
\right).
}
$$

其中：

1. $d$ 与 $\mathbf G$ 决定伴随 $\delta=d^*_{\mathbf G}$、$\Delta=d\delta+\delta d$、谱和 Hodge 分解；
2. $F_{\mathrm{cur}}\in C^2(K;\mathbb R)$ 是当前测量曲率数据；若它来自实际边状态 $g_{\mathrm{cur}}$，须声明 $F_{\mathrm{cur}}=d_1g_{\mathrm{cur}}$。独立测量不预设闭合或属于 $\operatorname{im}d_1$，即使可实现也不自动等于当前 $g_{\mathrm{cur}}$ 的曲率；
3. $\mathcal C^1=\operatorname{im}\delta_2$、$\mathcal H^1=\ker\Delta_1$ 可由算子/内积重算，$\Pi:\mathcal H^1\to\mathbb R^r$ 是声明的线性周期接口映射。记 $P_{\mathcal H}$ 为到 $\mathcal H^1$ 的正交投影，本条周期约束指 $\Pi(P_{\mathcal H}g)=p$；若接口测的是完整 $g$ 的闭路积分，须在有曲率解后扣除 coexact 部分的相应读数，才能用作这里的 harmonic 周期数据；
4. $p_{\mathrm{cur}}\in\operatorname{im}\Pi$ 是该接口的当前实际周期数据，不能与映射 $\Pi$ 混为一项，也不能由 $\Pi$ 单射凭空提供。若声称恢复实际 $g_{\mathrm{cur}}$ 的规范类，须同时有 $F_{\mathrm{cur}}=d_1g_{\mathrm{cur}}$ 和 $p_{\mathrm{cur}}=\Pi(P_{\mathcal H}g_{\mathrm{cur}})$；独立测量只定义满足所给约束的候选解集。若任务要求实际具体代表而非规范等价类，还须另列规范选择和该当前状态；
5. $\mathsf{Event},\mathsf{Err},\mathsf{Stop}$ 分别保存事件核、误差/最小范数任务合同和未来资源后继。它们须区分无解报告与有解后的状态任务；对不一致测量可以有诊断事件、残差、修正任务或停止标签，但这些输出不能制造一个满足原约束的重构状态。

对 $F=F_{\mathrm{cur}}$、$p=p_{\mathrm{cur}}$，置 $\mathcal E^1=\operatorname{im}d_0$、$H^2=\ker d_2/\operatorname{im}d_1$，并定义

$$
\mathcal S_F=\{g:d_1g=F\},\qquad
\mathcal S_{F,p}=\{g\in\mathcal S_F:\Pi(P_{\mathcal H}g)=p\}.
$$

曲率/周期重构使用同一个带标签响应类型：

$$
\mathsf{Rec}(F,p)=
\begin{cases}
(\mathrm{no\ solution},\mathrm{Bianchi},d_2F),&d_2F\ne0,\\
(\mathrm{no\ solution},H^2,[F]_{H^2}),&d_2F=0,\ [F]_{H^2}\ne0,\\
(\mathrm{solved},g_{\mathrm{coex}},\mathcal S_{F,p}/\mathcal E^1),
&F\in\operatorname{im}d_1.
\end{cases}
$$

末支中 $g_{\mathrm{coex}}$ 由定理 360.2 定义，$p\in\operatorname{im}\Pi$ 保证周期纤维非空。前两支均有 $\mathcal S_F=\mathcal S_{F,p}=\varnothing$，不附加代表或非空的 $H^1$ 残余；非闭合支不形成 $H^2$ 类。

**定理 398.5（Hodge 边界的条件充分性）。** 本条替代 §362.2 的相应陈述与证明。

采用定义 398.4 的显式内积、当前数据与分支合同；具体规范代表的选择须声明，事件律须通过同一当前数据及响应分支因子化。若两个有限关系体具有相同的 $\eta_{\mathrm{Hodge}}$，且未来任务限于边界声明的有限曲率重建、规范固定、周期观测、局部事件、误差合同和停止规则，则二者给出以下同类型响应的相等性，包括相同的无解报告：

1. Hodge 正交分解与 harmonic 维数；
2. $\mathsf{Rec}(F_{\mathrm{cur}},p_{\mathrm{cur}})$ 的相同分支及其数据；仅在 $F_{\mathrm{cur}}\in\operatorname{im}d_1$ 时，给出唯一 coexact 曲率解和仅固定曲率的最小范数解；
3. 仅在有解分支，给出曲率解模规范的 $H^1$ 仿射分类和给定实际周期后的相容类集合。$\Pi$ 单射且 $p_{\mathrm{cur}}\in\operatorname{im}\Pi$ 时，该非空相容集合恰有一个规范类；仅固定曲率与同时固定周期的最小范数任务分别计算；
4. 各分支合法事件的记录分布和正概率条件后继；需重构状态的事件只在有解分支及其状态/规范合同内执行，无解分支只能调用声明的诊断或修正接口；
5. 该分支上有定义的曲率、周期和重建误差下界；无解时报告障碍，若合同采用扩展实数，可把原精确约束空集上的代价下确界记为 $+\infty$，但不称其有最小范数代表；
6. 遵守同一分支合法性、误差和停止合同的有限预算任务树。

**证明。** 第 1 项由 §§359.1–359.3 的有限维正定 Hodge 分解给出。若 $d_2F\ne0$，则 $d_2d_1=0$ 排除 $d_1g=F$；若 $d_2F=0$ 而 $[F]_{H^2}\ne0$，则 $F\notin\operatorname{im}d_1$，仍无解。只有闭合且 $[F]_{H^2}=0$，即 $F\in\operatorname{im}d_1$ 时，才调用定理 360.2–360.3：

$$
\mathcal S_F=g_{\mathrm{coex}}+\mathcal E^1+\mathcal H^1,
\qquad
\|g_{\mathrm{coex}}+e+h\|_1^2
=\|g_{\mathrm{coex}}\|_1^2+\|e\|_1^2+\|h\|_1^2.
$$

因此仅固定曲率时唯一最小范数解是 $g_{\mathrm{coex}}$，模 $\mathcal E^1$ 的解集以 $\mathcal H^1\cong H^1$ 为仿射方向。$\Pi(g)$ 在这里不作未定义的使用：周期约束作用于 harmonic 分量 $h=P_{\mathcal H}g$。由于 $p\in\operatorname{im}\Pi$，取任意 $h_0\in\mathcal H^1$ 满足 $\Pi h_0=p$，则

$$
\mathcal S_{F,p}=g_{\mathrm{coex}}+h_0+\ker\Pi+\mathcal E^1,
\qquad
\mathcal S_{F,p}/\mathcal E^1
\cong g_{\mathrm{coex}}+h_0+\ker\Pi.
$$

其中 $\ker\Pi\subseteq\mathcal H^1$。单射时 $\ker\Pi=0$，才得到定理 360.5 的唯一相容规范类；所有满足同一曲率与周期约束的边上链可相差 $\mathcal E^1$，Coulomb 条件选其中唯一的 $g_{\mathrm{coex}}+h_0$，并不宣称未固定规范的边上链相同。

对任意这样的 $\Pi$，在非空仿射纤维 $\Pi^{-1}(p)$ 中置 $h_p^{\min}=h_0-P_{\ker\Pi}h_0$，其中 $P_{\ker\Pi}$ 是内积诱导的正交投影。它是该纤维中唯一垂直于 $\ker\Pi$ 的元素；其他元素为 $h_p^{\min}+k$，$k\in\ker\Pi$，故由勾股关系它唯一最小化范数。非单射时相容规范类仍有 $\ker\Pi$ 仿射自由度。曲率加指定周期任务的唯一最小范数解及其代价为

$$
g_{F,p}^{\min}=g_{\mathrm{coex}}+h_p^{\min},\qquad
\|g_{F,p}^{\min}\|_1^2=\|g_{\mathrm{coex}}\|_1^2+\|h_p^{\min}\|_1^2.
$$

这是全体相容类中的最小范数选择，不把非单射的周期读数升级为唯一实际规范类。它仅在 $p=0$ 时等于曲率单独任务的 $g_{\mathrm{coex}}$；一般非零周期不能在曲率单独最小化时被保留。以上完成第 2、3 项，且没有在空集上选择代表。

同一 $K,d,\mathbf G,F,p$ 给出相同响应标签、障碍或相容解集。第 4–6 项再使用同一当前数据及声明的 $\mathsf{Event},\mathsf{Err},\mathsf{Stop}$：无解时可以读取测量、报告诊断和停止，也可以按另行声明的修正合同产生新数据，但须对新数据重新判分支；近似解或投影后的曲率不能充作原 $F$ 的精确解。有解时，事件若依赖某个实际相容类或具体代表，必须由已列数据及选择合同确定，否则这里只返回相容集合，不提供该事件的无条件单一状态律。每条合法后继继承相应分支与预算，以相同核及正概率条件化沿有限树归纳，即得相同的记录分布、条件后继、误差响应与合法任务树。证毕。

**有限反例（闭合仍不保证存在）。** 取只有一个零胞腔和一个二胞腔的 CW 球面 $S^2$，实系数下 $C^1=0$、$C^2=\mathbb R$、$C^3=0$，$d_1=d_2=0$，各层取正定内积。令 $F_{\mathrm{cur}}=1$，则 $d_2F_{\mathrm{cur}}=0$，但 $[F_{\mathrm{cur}}]_{H^2}=1\ne0$。同时 $H^1=\mathcal H^1=0$，$\Pi:\{0\}\to\mathbb R$ 单射，$p_{\mathrm{cur}}=0\in\operatorname{im}\Pi$；取相同的平凡 $\mathsf{Event},\mathsf{Err},\mathsf{Stop}$ 合同。方程 $d_1g=1$ 仍无解，两份相同边界给出相同的 $H^2$ 障碍报告，绝不给出“唯一相容规范类”。这只能是独立测量；实际唯一边上链 $g=0$ 的曲率为零。定义 398.1 的 $D^3$ 模型则给出非闭合分支：$C^1=0$、$C^2=C^3=\mathbb R$、$d_2=\mathrm{id}$、$F_{\mathrm{cur}}=1$，其障碍为 Bianchi 残差 $1$，而不是一个 $H^2$ 类。

**定理 398.6（Hodge 字段的重构与真实约化）。** 本条替代 §362.3、§362.5 的相应陈述与证明。

1. 在 $K,d,\mathbf G$ 固定时，$\delta,\Delta,\operatorname{spec}\Delta,\mathcal C^1,\mathcal H^1$ 和 Hodge 投影都是确定函数；删除其中任一缓存不会在相同决定数据下产生不同 Hodge 空间或谱。保留 $F_{\mathrm{cur}},\Pi,p_{\mathrm{cur}}$ 后可按定义 398.4 重算完整带标签响应，包括无解报告；无解分支没有可重算的重构状态。
2. 周期映射与周期数据是不同对象。取标准 CW 环面 $C^1=\mathcal H^1\cong\mathbb R^2$、$d_0=d_1=0$、$\Pi=\mathrm{id}$，固定 $K,d,\mathbf G,F_{\mathrm{cur}}=0$ 和所有事件合同；$p_{\mathrm{cur}}=(0,0)$ 与 $p'_{\mathrm{cur}}=(1,0)$ 都在 $\operatorname{im}\Pi$ 中，且曲率可实现，却给出不同的 harmonic 代表。故删除实际周期数据会改变有解分支的当前重建，即使保留 $\Pi$；只保留数据而删除 $\Pi$ 则没有周期语义。
3. 内积坐标不能被默认为由拓扑数据决定。作一个两维边空间 $C^1=\mathbb R^2$、$d_1(x,y)=x+y$、$F_{\mathrm{cur}}=1$ 的固定代数例子；对仅固定曲率的任务，权重 $\mathbf G_1=\operatorname{diag}(1,1)$ 的最小范数解为 $(1/2,1/2)$，权重 $\mathbf G_1'=\operatorname{diag}(4,1)$ 的最小范数解为 $(1/5,4/5)$，最小平方范数分别为 $1/2$ 与 $4/5$。若把内积包 $(\mathbf G,\delta,\Delta,\operatorname{spec}\Delta,\mathcal C^1,\mathcal H^1)$ 一起从约化摘要删去，只保留 $K,d,F_{\mathrm{cur}}$，这是一对相同剩余字段而精度/代价不同的实现；单独删除由它们决定的谱或分解缓存则不是反例。附加周期约束时须改用定理 398.5 的 $g_{F,p}^{\min}$，不能沿用曲率单独最小化的数值。
4. 删除事件核：固定同一响应分支及 Hodge 数据而取不同的合法探测接口，可得不同记录后继；无解分支的诊断事件不表示恢复了边状态；
5. 删除停止合同：固定同一响应分支及当前数据而改变预算，可得不同继续树；涉及重构状态的后继须先通过存在性判定，修正后须重新判分支。

**证明。** 第 1 项由 §§359.1–359.3 的定义性公式及定理 398.5 的分支判定。第 2 项在 $F=0$ 可实现且给定 $p\in\operatorname{im}\Pi$ 后调用定理 360.5，$\Pi$ 的单射只把实际给定的 $p$ 映到 harmonic 分量，不会凭空提供数据或消除曲率障碍。第 3 项直接最小化 $w_1x^2+w_2y^2$ 约束 $x+y=1$ 得到两组数值；它保持拓扑/代数约束而只改变坐标内积，未把这一曲率任务与附加周期任务混同。第 4、5 项只改变明确的事件或资源合同，并保持其分支合法性。证毕。

因而原 §362.5 只称所声明任务上的充分边界；不由这些相互决定的字段推出独立最小清单。独立测量的障碍报告也是该充分性的有效输出，不能为保留“重建”措辞而预设一个不存在的状态。

## 399. 谱、Gramian 与统计几何的决定数据

**定义 399.1（谱—事件全息边界）。** 本条替代 §366.1 的相应陈述与证明。

固定有限 Hodge 空间、合法动力学和有限事件策略。定义

$$
\boxed{
\eta_{\mathrm{spec\text{-}event}}
=
\left(
\Delta,
A_\tau,
\tau,
\{Q_j,\zeta_j\},
\{C_a\},
\mathcal O_N^\pi,
W_N^\pi,
\mathsf{Clock},
\mathsf{Event},
\mathsf{Err},
\mathsf{Stop}
\right).
}
$$

在声明的 normal/self-adjoint 谱 sector 中写成

$$
A_\tau=\sum_j\zeta_jQ_j,\qquad
\sum_jQ_j=I,\qquad
Q_iQ_j=0\ (i\ne j).
$$

于是 $A_\tau$ 决定其谱值和谱投影（重复谱值只确定相应总投影）；对固定策略和接口序列，

$$
W_N^\pi=(\mathcal O_N^\pi)^*\mathcal O_N^\pi,\qquad
\lambda_{\min}(W_N^\pi)\ \text{由 }W_N^\pi\text{ 决定}.
$$

这些是可重算缓存。若动力学不在 normal/self-adjoint sector，必须另列 Jordan/广义谱数据，不能套用上述投影表述。各字段保存的独立合同是：钟校准、允许接口、事件核、误差预算和停止后继。

**定理 399.2（谱—事件边界的条件充分性）。** 本条替代 §366.2 的相应陈述与证明。

若给定状态的事件任务还具有相同的当前状态或任务相对充分摘要，两个有限关系体具有相同的 $\eta_{\mathrm{spec\text{-}event}}$，且未来任务限于边界声明的有限时间采样、谱模式重建、局部或周期事件、误差合同和停止规则，则二者给出相同的：

1. 采样谱相位、混叠类与 horizon 观察秩；
2. 事件策略的可见子空间与暗子空间；
3. 无噪声重建结果和带噪稳定误差界；
4. 有限事件词的概率、条件后继与停止结果；
5. 改变采样步长或探测动作后的合法任务树。

**证明。**

第 1 项由 $A_\tau,\tau$ 的声明谱分解和 $\mathcal O_N^\pi$ 决定；第 2 项由定理 365.2 的 Gramian 核；第 3 项由 $W_N^\pi=(\mathcal O_N^\pi)^*\mathcal O_N^\pi$、其最小特征值和 $\mathsf{Err}$ 决定；第 4、5 项由 $\mathsf{Event},\mathsf{Clock},\mathsf{Stop}$ 对有限策略树作归纳。证毕。

**定理 399.3（动态字段的重构与真实约化）。** 本条替代 §366.3 的相应陈述与证明。

1. 在 $A_\tau$ 处于 normal/self-adjoint sector 且 $\mathcal O_N^\pi$ 保留时，$Q_j,\zeta_j,W_N^\pi$ 及 $\lambda_{\min}(W_N^\pi)$ 都是确定函数；删除这些缓存本身不会改变谱、可见性或误差界。
2. 若约化摘要只保留谱值/整数时间标签而同时删除 $A_\tau$ 的谱投影和连续钟校准，便可能混叠不同接口方向或不同连续相位；例 364.4 的 $\lambda_0=0,\lambda_1=2\pi/\tau$ 在采样标签上相同而连续相位不同。
3. 一个真实的接口约化必须同时删除 $\{C_a\}$、$\mathcal O_N^\pi$ 及其 Gramian、最小特征值和可见性结果，并只保留 $A_\tau,\tau$ 及谱数据，同时把事件、误差和停止合同固定为相同的外部合同。取一维 $A_\tau=1$，两模型分别为 $C=0$ 与 $C=1$；它们具有相同的动力学谱和钟标签，但前者的 Gramian 为 $0$，后者的 Gramian 为 $N$，可见性任务不同。
4. 事件后继：固定当前振幅与 Gramian，改变记录仪器的结果后继，可得到不同未来边界；
5. 停止合同：固定有限样本和全部当前观测，改变资源预算，可得到不同继续树。

**证明。**

第 1 项是定义性等式和谱分解；第 2 项是采样相位例。第 3 项的两模型在删去接口与观察算子后剩余字段逐项相同，而 $W_N^0=0$、$W_N^1=N$。第 4、5 项只改变明确的未来合同。证毕。

**定理 399.4（信息字段的重构与真实约化）。** 本条替代 §370.3 的相应陈述与证明。

在 §§367—368 的可微、正概率及参数无关策略合同下，对固定参数坐标约定，完整条件模型 $p_n(x\mid a,h,\theta)$ 直接给出

$$
J_n(h,a;\theta)
=
\sum_x
\frac{
\nabla_\theta p_n(x\mid a,h,\theta)\,
\nabla_\theta p_n(x\mid a,h,\theta)^{\mathsf T}
}{
p_n(x\mid a,h,\theta)
},
\qquad
I_{T_N}(\theta)=\sum_{n=0}^{N-1}\mathbb E_\theta[J_n(H_n,A_n;\theta)].
$$

因此，在完整模型、参数化和策略保留时，删除 $\{I_n\}$ 或 $I_{T_N}$ 的缓存不会改变局部可识别性；这些量不能在相同的决定模型下独立变化。

可以成立的约化必须删除决定模型或独立合同：

1. 删除共同参数来源或参数坐标约定：相同的未标定边缘分布可以对应不同参数方向和估计目标；
2. 删除历史策略：固定动作集合而改变 $q_n(a\mid H_n)$，由定理 368.2 得到不同的自适应信息累积；
3. 把完整 $p_n$ 约化为只保留一个点上的总 Fisher：在参数区间 [0,1/2]、$\theta_0=0$ 附近取二元模型
   $p^{(A)}_\theta(1)=\tfrac12+\tfrac12\theta$ 与
   $p^{(B)}_\theta(1)=\tfrac12+\tfrac12\theta+\tfrac14\theta^2$。两者在 $\theta_0$ 的分布、导数和 Fisher 都相同（均为 $1$），但在 $\theta=1/2$ 的分布分别为 $3/4$ 与 $13/16$，后续概率任务不同；
4. 删除 Cramér–Rao/重复资源合同：同样的可识别模型在不同 $M$ 或风险阈值下有不同认证误差；
5. 删除事件后继或停止规则：当前信息相同而下一步动作、风险和可继续 transcript 不同。

**证明。**

前两式分别是条件 Fisher 的定义和定理 368.2。第 3 项在 $\theta_0=0$ 有 $p=1/2,p'=1/2$，故 $I=(p')^2/[p(1-p)]=1$；但两模型在 $\theta=1/2$ 的概率不同，所以只保留点 Fisher 不能决定完整模型的未来分布。第 1、2、4、5 项分别由参数约定、策略链式法则和独立的风险/后继合同给出。证毕。

**命题 399.5（完整分布决定局部与全局信息几何）。** 本条替代 §374.1 的相应陈述与证明。

Fisher 公式采用 §§367、371 的可微及正概率合同；亲和度与 Hellinger 的有限和也允许零概率。对固定参数坐标，Fisher、亲和度与 Hellinger 几何量由完整分布逐项确定：

$$
\mathsf I_\theta
=\sum_z \mathsf P_\theta(z)\,\nabla_\theta\log\mathsf P_\theta(z)\,
\nabla_\theta\log\mathsf P_\theta(z)^{\mathsf T},
$$

$$
\mathsf A(\theta,\theta')=\sum_z\sqrt{\mathsf P_\theta(z)\mathsf P_{\theta'}(z)},
\qquad
\mathsf H^2(\theta,\theta')=1-\mathsf A(\theta,\theta').
$$

所以在 $\mathsf P_\theta$ 保留时，$\mathsf I_\theta,\mathsf H,\mathsf A$ 是可重算缓存。

**定理 399.6（信息几何字段的重构与真实约化）。** 本条替代 §374.3 的相应陈述与证明。

在完整 $\mathsf P_\theta$ 和固定参数坐标保留时，$\mathsf I_\theta,\mathsf H,\mathsf A$ 由上面的求和公式确定；因此单独删除 Fisher、Hellinger 或亲和度缓存不能改变其余字段所决定的任务。

可成立的约化必须删除完整分布或独立通道合同。取参数区间 [0,1/2]、$\theta_0=0$ 附近的二元分布族

$$
P^{(A)}_\theta(1)=\tfrac12+\tfrac12\theta,\qquad
P^{(B)}_\theta(1)=\tfrac12+\tfrac12\theta+\tfrac14\theta^2.
$$

在 $\theta_0$ 两者的 $P$、导数和 Fisher 都相同，均为 $I(\theta_0)=1$；但在 $\theta=1/2$ 时分别为 $3/4$ 与 $13/16$，故从只保留局部 Fisher 的约化摘要不能恢复相同的全局 Hellinger/亲和度。其余真实独立约化为：

1. 删除事件通道：固定原始来源分布而取严格收缩的不同通道，得到不同的可见记录距离；
2. 删除粗粒化映射：固定通道而合并或保留时间/路径标签，得到不同的后处理距离；
3. 删除成本/风险合同：固定记录距离而改变 $c,\delta$ 或重复上限，定理 373.4 给出不同认证结论；
4. 删除事件后继：固定当前区分而改变下一步允许接口和停止树。

**证明。**

前一对模型的局部计算同定理 399.4：$p(0)=1/2,p'(0)=1/2$，所以 Fisher 为 $1$，而有限点概率不同，进而
$\mathsf A(P_0,P_{1/2})$ 和 $\mathsf H(P_0,P_{1/2})$ 不同。第 1—4 项分别由数据处理收缩、粗粒化、定理 373.4 和独立后继合同给出。证毕。

**命题 399.7（Hellinger 二阶展开的加法更正）。** 本条替代 §371.3 的陈述与证明，并替代 §371.4 零方向推论及 §374.2 第 1 项对旧二阶展开的调用；这两处消费者均以本命题为有效依据。旧 §371.3 首个框内公式在小 $o$ 项之前漏写加号，平方根 Taylor 式在常数项、线性项与余项之间漏写加号；这些旧式不再用作推导前提。

设 $X$ 为固定的非空有限集合，$U\subset\mathbb R^d$ 为开集，$p:U\to(0,\infty)^X$ 为 $C^2$ 映射，且对每个 $\vartheta\in U$ 有 $\sum_{x\in X}p_\vartheta(x)=1$。固定 $\theta\in U$，记 $p_x=p_\theta(x)$、$\nabla p_x=\nabla_\theta p_\theta(x)$，并取欧氏范数。定义

$$
I(\theta)=\sum_{x\in X}\frac{\nabla p_x\,\nabla p_x^{\mathsf T}}{p_x},
\qquad
\mathsf A(p,q)=\sum_{x\in X}\sqrt{p(x)q(x)},
$$

$$
\mathsf H^2(p,q)
=\frac12\sum_{x\in X}\bigl(\sqrt{p(x)}-\sqrt{q(x)}\bigr)^2
=1-\mathsf A(p,q),
\qquad \mathsf H(p,q)=\sqrt{\mathsf H^2(p,q)}.
$$

则当 $h\to0$ 且 $\theta+h\in U$ 时，正确的两式为

$$
\boxed{\sqrt{p_{\theta+h}(x)}
=\sqrt{p_x}+\frac{(\nabla p_x)^{\mathsf T}h}{2\sqrt{p_x}}
+O(\|h\|^2),}
$$

$$
\boxed{\mathsf H^2(p_\theta,p_{\theta+h})
=\frac18 h^{\mathsf T}I(\theta)h+o(\|h\|^2).}
$$

**证明。** 两个分布均归一化，故展开平方即得 $\mathsf H^2=1-\mathsf A$。在 $U$ 内取以 $\theta$ 为中心的充分小闭球；由有限性、正性与连续性，各 $p_\vartheta(x)$ 在该球上具有共同正下界。每个 $\sqrt{p_\vartheta(x)}$ 在此为 $C^2$，其 Hessian 有界，故 Taylor 定理给出第一式，余项可对有限个 $x$ 一致写成 $r_x(h)=O(\|h\|^2)$。代入定义可得

$$
\begin{aligned}
\mathsf H^2(p_\theta,p_{\theta+h})
&=\frac12\sum_{x\in X}
\left(\frac{(\nabla p_x)^{\mathsf T}h}{2\sqrt{p_x}}+r_x(h)\right)^2\\
&=\frac18\sum_{x\in X}\frac{((\nabla p_x)^{\mathsf T}h)^2}{p_x}
+O(\|h\|^3)\\
&=\frac18 h^{\mathsf T}I(\theta)h+o(\|h\|^2).
\end{aligned}
$$

这里交叉项为 $O(\|h\|^3)$，余项平方为 $O(\|h\|^4)$，有限求和保持这些估计。证毕。

**零方向与直接消费者。** 在本命题的假设下，对固定 $v\in\ker I(\theta)$，代入 $h=\varepsilon v$ 得 $\mathsf H^2(p_\theta,p_{\theta+\varepsilon v})=o(\varepsilon^2)$；由非负性开平方即得 §371.4 的 $\mathsf H(p_\theta,p_{\theta+\varepsilon v})=o(|\varepsilon|)$，$v=0$ 时恒为零。§374.2 第 1 项在同一参数坐标和上述有限、正概率、开邻域 $C^2$ 合同下，使用 §399.5 的完整分布重构及本命题的二阶展开；不再调用旧 §371.3 的缺号公式。这是固定基点的局部渐近式，不是对任意有限扰动的精确二次等式。

**有限验算。** 取 $X=\{0,1\}$、$U=(-1,1)$、$p_\theta(1)=(1+\theta)/2$、$p_\theta(0)=(1-\theta)/2$。在 $\theta=0$，

$$
I(0)=\frac{(1/2)^2}{1/2}+\frac{(-1/2)^2}{1/2}=1,
\qquad
A_\varepsilon=\mathsf A(p_0,p_\varepsilon)
=\frac{\sqrt{1+\varepsilon}+\sqrt{1-\varepsilon}}2.
$$

对 $0<|\varepsilon|<1$，由 $A_\varepsilon^2=(1+\sqrt{1-\varepsilon^2})/2$ 两次有理化，精确得到

$$
\frac{\mathsf H^2(p_0,p_\varepsilon)}{\varepsilon^2}
=\frac{1-A_\varepsilon}{\varepsilon^2}
=\frac{1}{2(1+\sqrt{1-\varepsilon^2})(1+A_\varepsilon)}
\longrightarrow\frac18.
$$

## 400. 更正后的直接适用关系

**命题 400.1（直接消费者的适用合同）。** 下列旧条目中的相应假设、证明调用和必要性断言由本节列明的更正替代；相冲突的旧子句不再是这些结论的前提。未改动的结果只在其原有假设及下列新增限定共同成立时使用。

| 原条目或直接消费者 | 替代后的有效条件与推导 |
| --- | --- |
| §§253.3–253.5、387.1–387.2；§254 的顺序解释 | 使用定理 390.1 的完整合法词、原始来源、共同前缀和后缀；局部交换子不独自证明顺序可见。 |
| §§257.1–257.4、258.1–258.4、389.1、389.3 | 使用定理 390.2 的基准加增量任务；定理 258.2 的注入步骤据此成立。定理 390.3 的完整反馈元组允许冗余，定理 390.4 的不足只针对列明约化，§388 的截断与失配范围继续适用。 |
| §§260.1–260.3、261.1–261.3、262.1–262.4、270.1–270.4、282.2–282.4 | 使用 §391 的决定数据、记录与动作合同。§261 的原公式限定为自治更新；§262.2 在共同已知且已记录的控制下使用 §391.1 的先更新后观测仿射递归，未知状态依赖控制须有联合可行关系，噪声须有另行声明的滤波合同。§282.2 中顺序暴露还须满足定理 390.1 的上下文条件；观测商、增益裕量、纤维交和交换关系可重算时，不再分别声称删除必然失效。 |
| §§308.2、310.2；§§317.2、318.2–318.4、319.1、319.3、320.1–320.4、321.2–321.5、322.1–322.4 | 联合权重区别依定理 390.5 分别投影为记录质量与候选后验。访问和策略树使用 §392 的归一化联合核、重复读取合同、完整合法性与停止标签；商因子只在实际值域唯一，空恢复族成本为 $+\infty$，超图由静态恢复集重建。 |
| §§324.1–324.5、325.2–325.6、326.2–326.4 | 使用 §393 的共同嵌套词域、合法性分层、正误差分区族包含，以及保持预算的访问模拟。平均风险的凸组合配平均成本；最坏成本取正概率种子支持上的最大值。跳跃前沿以阈值以下所有合法策略无信息为前提。 |
| §§327.5、328.4、329.2–329.3、330.2–330.4 | 使用 §394 的共同来源对应、$g\circ G$、同一联合耦合及全部允许映射对上的量词；指定映射的事件反例只排除该映射，最优距离先取各映射最大误差再取下确界。 |
| §§332.1–332.3、332.5–332.6、333.2、334.1–334.4 | 使用 §395 的实际归一化效果族及完整联合输入合同。线性张成只判精确因子化，相位例的单态残差为 $1/2$、两态概率差为一；保留效果与去相干映射时，残差为可重构量。§395.4 的 $F_0,F_1$ 同摘要对只针对联合隐藏全部相干决定数据的约化，§334.4 不再要求独立残差缓存。 |
| §§336.2–336.4、336.6、337.2–337.5、338.2–338.4 | 使用 §396 的合法过程差约束和绝对 tester 误差。闭包严格扩大须有合法非对角拉回；实际区分还须有非零配对的合法过程对。当前 tester、操作和深度决定闭包，不能以删除其缓存证明不足。 |
| §§339.5–339.6、340.6–340.7、342.1–342.4 | 定理 396.8 从带标签的完整逐访问任务列表，或有限上闭合同下的完整逐任务最小访问列表，重构 incidence、两侧导出与闭包；行计数约化才有该条的同摘要反例。阈值与未来合同的约化须联合隐藏其决定数据及派生值。命题 396.9 区分逐任务索引超图与联合任务族极小访问，§342 不将 $U$ 与 $\{u_1\}$ 并成联合反链。 |
| §§346.2–346.4、348.1、348.3–348.4、349.5、350.2–350.4、351.1、352.4、353.7、354.1–354.5 | 使用 §397 的给定局部族拼接、线性等距作用与最坏根值量词、相容规范约定、可区分边值与非平凡表示假设。§397.1 比较固定族 $\mathcal G\cap\{(0,0)\}$，联合隐藏限制及其相容性缓存，不断言 $\mathcal G_B$ 为空。§§354.1–354.5 使用 §§397.7–397.9 的运输—事件联合规范类，同一个顶点规范必须识别状态、效果和事件核，数值任务不变、后继按类报告；无框架轨道不提供原始开路径值。§354.2 的截面判据一般使用定理 347.2，仅在相应 flat 假设下调用定理 351.3 或 352.2。 |
| §§358.1–358.5、362.1–362.5 | §§398.1–398.3 以运输—表面事件联合规范类和显式 closed/nonclosed 字段替代旧三维元组：非闭合记录 Bianchi 残差且无解，闭合后才取 $H^2$ 类，零类有解时才给 $H^1$ 挠集；这是阿贝尔上链分类。独立测量不由当前 $[g]$ 重算，只有明确 $F_{\mathrm{cur}}=d_1g$ 时可如此使用；§§358.4–358.5 的事件链与解释继承同一分支及共同规范合同。Hodge 消费者按 §§398.4–398.6 使用实系数、显式正定内积、实际周期映射及 $p_{\mathrm{cur}}\in\operatorname{im}\Pi$：非闭合或闭合非恰当的测量均无解，只给相应障碍报告；仅 $F_{\mathrm{cur}}\in\operatorname{im}d_1$ 时才调用 §§360.2–360.5，区分曲率单独与曲率加指定周期的最小范数解。§362.2 的唯一相容规范类还须 $\Pi$ 单射及实际相容周期数据，非单射时给非空相容类集合；恢复实际状态的类须曲率与周期都来自该状态，具体代表还须相应规范/状态合同。事件、误差和停止规则继承同一存在性分支；诊断或修正不能制造原约束的解。相同边界保证相同类型的响应，包括无解报告。 |
| §§366.1–366.4、370.2–370.4、371.3–371.4、374.1–374.4 | 使用 §399 的 normal 谱合同、完整观察算子、可微正概率模型及参数无关历史策略。§371.3 的陈述与证明由命题 399.7 替代；§371.4 的零方向推论及 §374.2 第 1 项均引用该命题的有限、正概率、开邻域 $C^2$ 二阶展开。§374.2 由完整分布计算 Fisher、亲和度与 Hellinger，并按其成本、风险、事件与停止合同继续。给定状态的实际事件律须提供同一当前状态或其任务相对充分摘要，参数化模型本身只给条件律。 |

**证明。** 完整执行词的差由定理 390.1 计算；反馈任务逐个由基准与限制解析子计算；访问 transcript 由同一联合律推前，未来商的判别同时包含合法性和停止标签。其余消费者分别使用 §393 的成本/风险量词、§394 的映射与耦合、§§395–396 的迹配对、完整 incidence 与任务族极小访问、§397 的联合路径—事件规范类、§398 的闭合分支及当前曲率与周期数据，以及 §399 的算子和概率模型。每个派生量都是列明决定数据的函数；每个不足反例则隐藏全部决定被比较量的数据，并固定所列余项。在这些合同下，原充分性证明可逐任务计算，再沿有限策略或组合树归纳；任何遗漏这些条件的旧必要性或充分性句子不构成该归纳的合法步骤。证毕。

## 追加锚（本行以下为增补区）
## 401. 来源似然、未来条件族与相容残差的联合观察商

**定义 401.1（固定 Gaussian 记录模型与三项任务）。** 取 §§359–361、398 的有限实系数上链空间与正定内积，记 $\mathcal H^1=\ker d_1\cap\ker d_0^{\mathsf T}$，其中转置相对于这些内积。固定线性接口 $\Pi:\mathcal H^1\to\mathbb R^p$，不要求单射；在数据空间 $E=C^2\oplus\mathbb R^p\cong\mathbb R^m$ 固定正交坐标，令

$$
Ag=(d_1g,\Pi P_{\mathcal H}g),\qquad
y=Ag+\Sigma^{1/2}\xi,\qquad
z=\Sigma^{-1/2}y=Bg+\xi,\qquad B=\Sigma^{-1/2}A.
$$

这里 $g$ 遍历整个 $C^1$，实际来源是其中固定但未知的一点；$\Sigma\succ0$ 已知，平方根取对称正定平方根。$y$ 是实际记录，允许在 $\operatorname{im}A$ 外。固定线性映射 $C:C^1\to\mathbb R^q$，未来块是一个已声明、可联合读取的经典随机向量

$$
Y_f=Cg+\zeta\in\mathbb R^q,\qquad
\begin{pmatrix}\xi\\\zeta\end{pmatrix}
\sim\mathcal N\!\left(0,
\begin{pmatrix}I_m&K^{\mathsf T}\\K&\Gamma\end{pmatrix}\right),\qquad
\begin{pmatrix}I_m&K^{\mathsf T}\\K&\Gamma\end{pmatrix}\succeq0.
$$

所有空间、内积、接口、协方差及联合 Gaussian 假设均在读数之前固定；只有协方差相同而联合律非 Gaussian 的模型不在此假设内。未来块不表示非对易量子反事实的共同测量。若 $g$ 按顶点规范类解释，另要求 $Cd_0=0$；否则固定来源代表，$C$ 是对该代表声明的接口。

置

$$
S=\operatorname{im}B,\quad P=P_S,\quad R=I-P,\quad
M=\operatorname{im}((KR)^{\mathsf T}),\quad
N=S^\perp\cap\ker K,
\qquad r=\dim S,\ k=\dim M,\ \ell=\dim N.
$$

$M,N$ 是白化数据空间中的子空间，不是来源空间的 harmonic/coexact 分量。记 $P_M,P_N$ 为相应正交投影。令 $p_g(z)=(2\pi)^{-m/2}\exp(-\|z-Bg\|^2/2)$，$\lambda_g(z)=p_g(z)/p_0(z)$，$Q(z)=\|Rz\|^2$，并指定对每个 $g$、每个 $z$ 的核

$$
\mathcal F_g(z,\cdot)
=\mathcal N\!\left(Cg+K(z-Bg),\Psi\right),\qquad
\Psi=\Gamma-KK^{\mathsf T}.
$$

对半正定 $\Psi$，此记号指 $Cg+K(z-Bg)+\Psi^{1/2}U$ 的分布，$U\sim\mathcal N(0,I_q)$；允许 $\Psi$ 奇异甚至为零。三项任务是保留全部 $g$ 的 $\lambda_g$、保留同一来源索引下的整族 $\mathcal F_g$、保留实际数值 $Q$。不把这份条件核族认作已知实际 $g$，也不把旧原始读数、完整 Bianchi 残差、上同调坐标或操作权限列入这三项任务。读取安排自适应、估计协方差或扩大任务族，均须另给决定数据与假设。

**定理 401.2（三项任务的精确商与正交轨道）。** 在定义 401.1 下，$\mathcal F_g$ 是定义于每个 $z$ 的弱连续条件分布版本，且 $S^\perp=M\oplus N$ 为正交直和。对任意 $z,z'\in\mathbb R^m$，有

$$
\begin{aligned}
&\bigl[\ \forall g:\lambda_g(z)=\lambda_g(z'),\quad
\forall g:\mathcal F_g(z,\cdot)=\mathcal F_g(z',\cdot),\quad
Q(z)=Q(z')\ \bigr]\\
&\hspace{25mm}\Longleftrightarrow\quad
\eta(z)=\eta(z'),\qquad
\eta(z)=\bigl(Pz,KRz,\|P_Nz\|^2\bigr).
\end{aligned}
$$

$\eta$ 的纤维恰为 $O(N)$ 在 $\mathbb R^m=S\oplus M\oplus N$ 上恒等作用于 $S\oplus M$ 所得的轨道；这里 $O(N)$ 包含反射。这是所列三项任务的观察商，不是对来源 $g$ 的恢复断言。

**证明。** 先在这个商的推导中使用经典多元 Gaussian 条件化法，参见 T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 第三版，第 2 章，以及本系列主卷《RECURSIVE_RELATIONAL_OBSERVATION》§128.7 的创新分解。令 $\varepsilon=\zeta-K\xi$，直接计算

$$
\operatorname{Cov}(\varepsilon)=\Psi\succeq0,\qquad
\operatorname{Cov}(\varepsilon,\xi)=0.
$$

半正定性也可由联合协方差作用于 $(-K^{\mathsf T}t,t)$ 得到：相应二次型是 $t^{\mathsf T}\Psi t\ge0$。$(\xi,\varepsilon)$ 的联合特征函数为

$$
\mathbb E\exp\bigl(iu^{\mathsf T}\xi+iv^{\mathsf T}\varepsilon\bigr)
=\exp(-\|u\|^2/2)\exp(-v^{\mathsf T}\Psi v/2),
$$

故两者独立，奇异 $\Psi$ 也不例外。由 $Y_f=Cg+K(z-Bg)+\varepsilon$，对任意 Borel 集 $D\subseteq\mathbb R^m$、$H\subseteq\mathbb R^q$ 有

$$
\mathbb P_g(z\in D,Y_f\in H)
=\int_D\mathcal F_g(x,H)p_g(x)\,dx.
$$

这给出条件核版本，而非把概率零的单点事件当作正概率条件事件。对任意有界连续 $f$，$\int f\,d\mathcal F_g(z)$ 是固定随机向量 $\Psi^{1/2}U$ 的连续平移积分，由支配收敛随 $z$ 连续；这里的连续性是弱连续，不要求奇异 Gaussian 平移在全变差距离下连续。

展开当前 Gaussian 密度得到

$$
\log\lambda_g(z)=\langle z,Bg\rangle-\tfrac12\|Bg\|^2
=\langle Pz,Bg\rangle-\tfrac12\|Bg\|^2.
$$

因此全部似然比相同等价于 $z-z'\perp\operatorname{im}B$，即 $Pz=Pz'$。未来协方差固定，Gaussian 概率测度相等必有相等的有限均值，反向由同一均值与协方差也成立；故全部同索引条件核相同等价于 $K(z-z')=0$。已有 $Pz=Pz'$ 时，这恰为 $KRz=KRz'$。这个判据比较的是每个给定 $g$ 的核，不需要从观察估计或选择一个 $g$。

由于 $(KR)^{\mathsf T}=RK^{\mathsf T}$，$M\subseteq S^\perp$，并且对 $v\in S^\perp$，

$$
v\perp M\quad\Longleftrightarrow\quad KRv=Kv=0.
$$

所以 $S^\perp=M\oplus N$，$m=r+k+\ell$。若 $v\in M$ 且 $Kv=0$，则 $v\in M\cap N=\{0\}$；因此 $K|_M$ 单射。又 $KRz=KP_Mz$，故 $K|_M:M\to\operatorname{im}(KR)$ 为双射。记其逆为 $D_K$，包括零维空间间的唯一逆映射，则

$$
P_Mz=D_K(KRz),\qquad
Q(z)=\|D_K(KRz)\|^2+\|P_Nz\|^2.
$$

于是三项任务相等先确定 $Pz,KRz$，再由 $Q$ 确定 $N$ 分量的平方范数；反向由这三个量重构全部任务，得到所述等价。

正交作用保持 $Pz,KRz$ 及 $N$ 范数。反向设 $\eta(z)=\eta(z')$，写 $u=P_Nz,v=P_Nz'$，则 $\|u\|=\|v\|$，且两记录的 $S,M$ 分量相同。若 $u=v$，取恒等映射；否则在 $N$ 上令 $w=u-v$ 并取

$$
H_wx=x-2\frac{\langle x,w\rangle}{\|w\|^2}w.
$$

展开内积可知 $H_w$ 正交，而 $2\langle u,w\rangle=\|w\|^2$ 给出 $H_wu=v$。把它在 $S\oplus M$ 上延拓为恒等即把 $z$ 送到 $z'$。当 $\ell=0$ 时只有零向量和恒等作用；当 $\ell=1$ 时非零半径纤维的两点由符号反射交换；半径零时纤维在 $N$ 中只有一点。$r=0$ 或 $k=0$ 时相应分量为空，以上推导仍成立。

残差在这里有明确的最小二乘含义。经典广义最小二乘采用协方差逆作权重，参见 A. C. Aitken, *On Least Squares and Linear Combination of Observations*, DOI [10.1017/S0370164600014346](https://doi.org/10.1017/S0370164600014346)。对任意 $a\in C^1$，直接正交分解得

$$
(y-Aa)^{\mathsf T}\Sigma^{-1}(y-Aa)
=\|Pz-Ba\|^2+\|Rz\|^2,
\qquad
\min_a(y-Aa)^{\mathsf T}\Sigma^{-1}(y-Aa)=Q(z).
$$

最小值存在，因为 $Pz\in\operatorname{im}B$。所以 $Q=0$ 当且仅当原数据 $y\in\operatorname{im}A$；拟合并不改变原精确 Hodge 方程的可解性。该正交残差方法的 Hodge 先例是 Jiang–Lim–Yao–Ye, *Statistical ranking and combinatorial Hodge theory*, [arXiv:0811.1067v2](https://arxiv.org/abs/0811.1067v2), §§4–5，尤其定理 5.1，期刊 DOI [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x)；这里的数据子空间取所声明的曲率与周期联合像 $S$。

在中心零假设 $g=0$ 下，于 $S,M,N$ 中分别选正交基。$z=\xi$ 的特征函数在这三个坐标块上分解为独立标准正态的乘积，因此

$$
\|P_Nz\|^2\sim\chi^2_\ell,\qquad
Q(z)\sim\chi^2_{m-r},\qquad
\|P_Nz\|^2\ \text{独立于}\ (Pz,KRz).
$$

$\chi^2_0$ 指零点质量。这是 Cochran 正交二次型分解在本模型中的直接坐标证明；历史参照为 W. G. Cochran, *The distribution of quadratic forms in a normal system, with applications to the analysis of covariance*, 1934, DOI [10.1017/S0305004100016595](https://doi.org/10.1017/S0305004100016595)。小残差不认证实际来源为真，也不排除像内偏移：任取 $b\in S$ 都有 $Q(z+b)=Q(z)$。

最后，若另行给定与 $(\xi,\zeta)$ 独立的来源概率先验 $\mu$，无需假设其 Gaussian，则对每个 $z$ 定义

$$
\mu_z(dg)=\frac{\lambda_g(z)\mu(dg)}{\int\lambda_a(z)\mu(da)},\qquad
\mathcal F_\mu(z,H)=\int\mathcal F_g(z,H)\mu_z(dg).
$$

分母处处严格为正且有限，因为 $0<\lambda_g(z)\le\exp(\|Pz\|^2/2)$。联合模型的积分恒等式与 Bayes 公式证明这是后验及混合预测的版本；$\eta$ 相同就给相同的两者。对有界连续测试函数，在 $z$ 的任意紧邻域上用上述共同上界作支配收敛，还得到混合预测的弱连续性。先验是额外给定的共同输入，不能从噪声协方差推出；一个固定先验下的混合相等也不反推全部来源索引核相等。

这个商与 §398.4 的原始闭路校正相容。具体地，设 $L:C^1\to\mathbb R^p$ 满足 $Ld_0=0$、$\Pi=L|_{\mathcal H^1}$；由既有有限 Hodge 分解，取

$$
J=\left(d_1|_{\operatorname{im}d_1^{\mathsf T}}\right)^{-1}P_{\operatorname{im}d_1},\qquad
A_{\mathrm o}g=(d_1g,Lg),\qquad
T(F,l)=(F,l-LJF).
$$

这里 $d_1$ 在 coexact 空间上到 $\operatorname{im}d_1$ 为双射：满射由 Hodge 分解得到；若 $c=d_1^{\mathsf T}v$ 且 $d_1c=0$，则 $\|c\|^2=\langle v,d_1c\rangle=0$，故单射，像空间为零也包括在内。将 $g$ 分解为 $d_0u+h+c$，即有 $Jd_1g=c$、$Lg-LJd_1g=Lh=\Pi P_{\mathcal H}g$。因此 $TA_{\mathrm o}=A$，且 $T^{-1}(F,p)=(F,p+LJF)$。$J$ 的投影扩展使 $T$ 定义于不相容记录，也不把这些记录变成原 Hodge 方程的解。

同时运输实际数据和噪声，令

$$
y_{\mathrm n}=Ty_{\mathrm o},\quad
\Sigma_{\mathrm n}=T\Sigma_{\mathrm o}T^{\mathsf T},\quad
O=\Sigma_{\mathrm n}^{-1/2}T\Sigma_{\mathrm o}^{1/2},\qquad
\Sigma_{\mathrm o}\succ0.
$$

则 $OO^{\mathsf T}=I$，因为中间乘积 $T\Sigma_{\mathrm o}T^{\mathsf T}$ 正是 $\Sigma_{\mathrm n}$。所以 $z_{\mathrm n}=Oz_{\mathrm o}$、$B_{\mathrm n}=OB_{\mathrm o}$、$\xi_{\mathrm n}=O\xi_{\mathrm o}$。保持同一实际未来块，由交叉协方差定义得到

$$
K_{\mathrm n}=K_{\mathrm o}O^{\mathsf T},\qquad
\Gamma-K_{\mathrm n}K_{\mathrm n}^{\mathsf T}
=\Gamma-K_{\mathrm o}K_{\mathrm o}^{\mathsf T},\qquad
K_{\mathrm n}(z_{\mathrm n}-B_{\mathrm n}g)
=K_{\mathrm o}(z_{\mathrm o}-B_{\mathrm o}g).
$$

未白化的 $H_{\mathrm o}=\operatorname{Cov}(\zeta,y_{\mathrm o}-A_{\mathrm o}g)$ 也同时变为 $H_{\mathrm o}T^{\mathsf T}$。由正交性，$S_{\mathrm n}=OS_{\mathrm o}$、$P_{\mathrm n}=OP_{\mathrm o}O^{\mathsf T}$、$R_{\mathrm n}=OR_{\mathrm o}O^{\mathsf T}$，进而 $M_{\mathrm n}=OM_{\mathrm o}$、$N_{\mathrm n}=ON_{\mathrm o}$。因此

$$
\eta_{\mathrm n}(Oz)
=\left(OP_{\mathrm o}z,\ K_{\mathrm o}R_{\mathrm o}z,
\ \|P_{N_{\mathrm o}}z\|^2\right).
$$

这逐项运输三项任务与半径，$O(N)$ 的作用由 $O$ 共轭运输；$r,k,\ell$ 与线性摘要的单射性保持。只校正读数而保留旧协方差不满足这些等式。原始精确可解性由可逆性给出的 $y_{\mathrm o}\in\operatorname{im}A_{\mathrm o}\Longleftrightarrow Ty_{\mathrm o}\in\operatorname{im}A$ 保持，不由统计拟合替换。证毕。

## 402. 精确残差的线性压缩障碍与有限 Hodge 实现

**命题 402.1（任意解码器下的线性障碍与显式非线性坐标）。** 在定义 401.1 的全部观察空间上，设线性摘要 $L:\mathbb R^m\to\mathbb R^d$ 配有任意函数 $a,b$，满足

$$
a(Lz)=Pz,\qquad b(Lz)=Q(z)\qquad(\forall z\in\mathbb R^m).
$$

则 $L$ 必须单射，故 $d\ge m$；对解码器不要求线性、连续或可测。相反，在 $S$ 与 $\operatorname{im}(KR)$ 各固定一组基，$\eta$ 有 $r+k+1$ 个实坐标的显式表示（$\ell>0$），或 $r+k$ 个实坐标的表示（$\ell=0$）。$\ell\ge2$ 时前者严格少于 $m$。这些是所给表示的坐标数，不是任意可测编码的维数下界。只保留 $(Pz,Q(z))$ 能同时保留未来条件核族，当且仅当 $KR=0$。

**证明。** 若 $v\in\ker L$，比较实际向量 $v$ 与 $0$，得 $Pv=a(Lv)=a(0)=0$，且 $\|Rv\|^2=b(Lv)=b(0)=0$。所以 $v=Pv+Rv=0$，由秩定理得维数结论。该论证要求对所有观察成立，不用“几乎处处”的解码条件替换量词。

由定理 401.2，$\dim\operatorname{im}(KR)=k$，其坐标与 $Pz$ 的 $r$ 个坐标再加 $\|P_Nz\|^2$ 就给所述表示。若 $\ell>0$，值域恰为 $S\times\operatorname{im}(KR)\times[0,\infty)$：给定 $(s,t,u)$，在 $N$ 取单位向量 $n$，$z=s+D_Kt+\sqrt u\,n$ 即实现它。若 $\ell=0$，末项恒零，可省去，且 $m=r+k$；若 $\ell=1$，该表示仍有 $m$ 个坐标，但非零半径纤维有两个点。由 $m=r+k+\ell$，$\ell\ge2$ 时坐标减少量为 $\ell-1$。

若 $KR=0$，$Kz=KPz$，故未来族由 $Pz$ 决定。若 $KR\ne0$，存在 $v\in S^\perp$ 满足 $Kv\ne0$；取 $z=v,z'=-v$，则 $Pz=Pz'=0$、$Q(z)=Q(z')$，但每个 $g$ 的未来条件均值之差均为 $2Kv\ne0$。所以精确的总残差平方不能替代预测所需的残差方向。证毕。

**命题 402.2（圆盘、圆与三个球面的四坐标边界）。** 存在有限 CW 复形

$$
\mathcal X=D^2\vee S^1\vee S^2\vee S^2\vee S^2
$$

及标准上链内积，使 $C^1=\mathbb R^2$、$C^2=\mathbb R^4$，以 $g=(c,h)$ 为坐标时

$$
d_0=0,\qquad d_1(c,h)=(c,0,0,0),\qquad
\mathcal H^1=\{(0,h)\},\qquad \Pi(0,h)=h,
\qquad Ag=(c,0,0,0,h).
$$

取 $\Sigma=I_5$，未来标量为 $Y_f=c+\beta\xi_2+\eta_0$，其中 $\beta\ne0$，$\eta_0\sim\mathcal N(0,1)$ 独立于 $\xi\sim\mathcal N(0,I_5)$。三项任务的精确商可表示为

$$
\widehat\eta(z)=(z_1,z_5,z_2,z_3^2+z_4^2),
$$

而任何精确保留来源似然比及 $Q$ 的线性摘要至少需要五个实坐标。这个商合并 $(z_3,z_4)$ 的全部正交轨道，却不能删除 $z_2$ 的符号，也不保留测量曲率的全部 $H^2$ 坐标。

**证明。** 取一个零胞腔、两条闭合一胞腔 $a,b$；圆盘的二胞腔沿 $a$ 以度一附着，三个球面的二胞腔各以常值映射附着。于是 $\partial_1=0$，$\partial_2$ 的第一列为 $(1,0)^{\mathsf T}$，其余三列为零，转置给上述 $d_0,d_1$。标准度量下 $d_1^{\mathsf T}d_1=\operatorname{diag}(1,0)$，故 $\mathcal H^1$ 及 $A$ 如述。此模型没有非零 exact 一上链，规范作用平凡。

在数据标准基中，

$$
S=\operatorname{span}\{e_1,e_5\},\quad
K=\beta e_2^{\mathsf T},\quad \Gamma=\beta^2+1,\quad\Psi=1,
\quad M=\operatorname{span}\{e_2\},\quad
N=\operatorname{span}\{e_3,e_4\}.
$$

联合正半定协方差由实际构造 $(\xi,\beta\xi_2+\eta_0)$ 保证。相应公式为

$$
\lambda_{(c,h)}(z)=\exp\!\left(cz_1+hz_5-\tfrac12(c^2+h^2)\right),\quad
\mathcal F_{(c,h)}(z,\cdot)=\mathcal N(c+\beta z_2,1),\quad
Q(z)=z_2^2+z_3^2+z_4^2.
$$

$\beta$ 固定且非零，所以 $\beta z_2$ 与 $z_2$ 相互确定；定理 401.2 给出 $\widehat\eta$ 的精确性及 $O(2)$ 纤维。命题 402.1 给出线性摘要的五维障碍。对任意 $a\ne0$，记录 $(0,a,0,0,0)$ 与 $(0,-a,0,0,0)$ 有相同的全部来源似然比和 $Q=a^2$，但同一 $(c,h)$ 的未来条件均值分别为 $c+\beta a,c-\beta a$。这是处处定义的连续核的比较，不声称某个精确单点具有正概率。

另一方面，$(0,0,a,0,0)$ 与 $(0,0,0,a,0)$ 有相同 $\widehat\eta$。因 $d_2=0$，它们的曲率测量均闭合，而 $H^2=C^2/\operatorname{im}d_1\cong\mathbb R^3$ 中的坐标分别为 $(0,a,0)$ 与 $(0,0,a)$，并不相等；两份曲率均不可由 $d_1g$ 实现。所保留的 $Q=a^2$ 正确报告非零相容残差，却不报告障碍的全部坐标。增加这些坐标任务就必须细分该商。预测公式仍是未知 $(c,h)$ 索引的条件族，不能把 $z_1,z_5$ 当作已恢复的实际来源。证毕。

## 追加锚（本行以下为增补区）
