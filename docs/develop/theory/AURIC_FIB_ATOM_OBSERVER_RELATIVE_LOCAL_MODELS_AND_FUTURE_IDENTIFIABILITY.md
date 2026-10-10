# 观察者相对的 Auric FIB–ATOM：局部模型、接口与未来可辨识性

## 1. 条件模型与局部观察者

**约定 1.1（数学条件与物理解释）。** 本卷在通常的集合、实线性代数和概率论框架内讨论有限局部模型。“不预设全局物理对象”表示不把全局物理场、绝对时钟或共同物理状态空间作为模型前提；不表示数学不使用逻辑基础，也不表示这些物理对象不存在。以下条件命题的对象是明确给定的候选状态、合法操作和记录律，物理解释须另给实现与校准关系。

**定义 1.2（观察者的有限候选模型）。** 一个局部观察者 $o$ 的模型数据包含非空有限候选状态集 $S_o$、当前输出集 $Y_o$、观察映射 $\Pi_o:S_o\to Y_o$、边界接口 $B_o$、已取得历史 $\eta_o$、控制器数据 $C_o$ 和合法续接合同 $\mathcal L_o$。候选状态可以包含未被当前输出区分的变量；$Y_o$ 才是当前观察映射区分的输出标签。

边界接口指定实际可用的端口、标签和访问范围；控制器指定动作选择与更新；历史指定已保留的记录以及遗漏项；合法性合同指定启用条件、失败响应和终止语义。这些都是数据或约束，单独给它们命名不提供相应内容。

采用列向量约定，定义

$$
H_o=\mathbb R^{S_o},\qquad
\Delta_o=\{p\in H_o:p_s\ge0,\ \mathbf1_o^{\mathsf T}p=1\},\qquad
T_o=\{q\in H_o:\mathbf1_o^{\mathsf T}q=0\}.
$$

$H_o$ 是带符号质量空间，不是历史对象，也不是状态到数值的读出函数。两个概率律的差属于 $T_o$；一般带符号向量未必能作为两个可行律的差。

**定义 1.3（观察的律提升）。** 确定观察 $\Pi_o$ 提升为线性推前

$$
R_o:H_o\to\mathbb R^{Y_o},\qquad
(R_op)_y=\sum_{s:\Pi_o(s)=y}p_s.
$$

因此 $R_o$ 非负且保持总质量。更一般的已校准传感器给出列随机矩阵 $R_o(y,s)=\Pr(y\mid s)$。数值测试 $f:S_o\to\mathbb R$ 的期望为 $f^{\mathsf T}p$；期望摘要和完整输出概率律是不同读出。

**假设 1.4（已知共同模型）。** 每次比较 $p,p'$ 时，固定同一组状态标签、转换、记录核、控制器、合法性和校准数据。未知模型参数属于另一个反演问题，不随初始律比较而任意变化。不同观察者可以有不同的 $S_o,Y_o,H_o$，比较其读数时须给出共同来源或显式传输。

**定义 1.5（带类型的转换）。** 从 $o$ 到 $o'$ 的无输出转换为非负线性映射 $U_e:H_o\to H_{o'}$，满足

$$
\mathbf1_{o'}^{\mathsf T}U_e=\mathbf1_o^{\mathsf T}.
$$

带输出动作 $a$ 使用子核 $U_{a,b}:H_o\to H_{o(a,b)}$，其中 $b$ 是实际输出标签，且

$$
\sum_b\mathbf1_{o(a,b)}^{\mathsf T}U_{a,b}=\mathbf1_o^{\mathsf T}.
$$

$U_{a,b}p$ 保留输出 $b$ 与后继状态的联合质量，通常是次概率向量。除非明确改为条件问题，不把它除以分支概率。失败、Stop 或漏失质量须属于声明的输出或次概率合同。

**命题 1.6（有限记录不确定候选扩展）。** 当前输出全为一个标签的模型，不能仅由这些输出唯一确定其隐藏状态数或下一次传感器。例如一个单态模型和一个两态模型均可令当前 $R_o=\mathbf1_o^{\mathsf T}$；两态模型的下一输出可以读取隐藏比特，也可以继续只输出常数。

**证明。** 三种合同给出相同当前概率律 $\delta_*$，而状态集及下一读出口不同。因此当前输出不足以选出其中一个合同。对任意固定有限截止，也可在此前输出常数、截止后才启用新传感器；其相容构造见命题 7.2。故无限未来规则须作为候选模型数据给定并接受校准，不能由有限局部记录直接推出。$\square$

## 2. 细化、提升与共同来源

**定义 2.1（限制方向的观察细化）。** 普通细化由从细状态到粗状态的满射

$$
r:S_f\to S_c
$$

给出，其质量推前为 $r_*:H_f\to H_c$。若当前细、粗记录满足

$$
R_c r_*=Q R_f,
$$

其中 $Q$ 是指定的输出后处理，则粗记录可从细记录得到。该式比较的是同一个细律 $p_f$ 的两种读出，不能把不同制备的粗、细记录直接拼接。

**定义 2.2（动态细化合同）。** 在细、粗观察者图的每个对应顶点给出限制 $r_o$，在对应边给出动作与输出标签的映射。对应无输出边须满足

$$
(r_{o'})_*U_e^f=U_e^c(r_o)_*.
$$

对应分支采用相同输出标签时，对每个子核要求同一等式；合并输出时，对相应细子核求和后要求等式。状态边的端点必须按 $r_o,r_{o'}$ 对应。限制映射满足恒等与复合相容，且实际合法词、启用条件、失败记录、策略与终止记录按声明的对应保留。

这是动态 lumping／模拟的额外条件，不是由集合映射的类型自动得到的性质。经典 Markov lumping 的来源见数学引文 13.2；这里还保留观察输出与合法性数据。

**定义 2.3（随机提升）。** 若只有粗律 $p_c$，一个细扩展需要额外给出列随机映射 $L:H_c\to H_f$，满足

$$
r_*L=I_{H_c}.
$$

$Lp_c$ 是选择的细律。确定截面 $j:S_c\to S_f$ 只是这种选择的特殊情况。一般的 $S_c\to S_f$ 映射既不定义限制细化，也不确定被合并状态如何分裂。

**命题 2.4（局部扩展选择影响新读口）。** 取 $S_c=\{c\}$、$S_f=\{0,1\}$，$r$ 为常数映射。对任意 $\theta\in[0,1]$，

$$
L_\theta(1)=(1-\theta,\theta)^{\mathsf T}
$$

都是随机右逆；细读口 $R_f=I_2$ 区分这些扩展，而粗读口不能确定 $\theta$。

**证明。** $r_*=(1,1)$，故 $r_*L_\theta=1$。令 $R_c=(1)$、$Q=(1,1)$，观察细化等式成立；但 $R_fL_\theta$ 随 $\theta$ 变化。因而细化关系没有选出唯一提升。即使两边动力学都是恒等，也没有新增约束来确定 $\theta$。$\square$

**定义 2.5（拉回当前来源）。** 选定起始观察者 $o$ 后，其他观察者的读口通过声明的传输 $U:H_o\to H_{o'}$ 比较为

$$
A=R_{o'}U:H_o\to Z_{o'}.
$$

也可使用共同来源 $H$ 及 $L_o:H\to H_o$，比较 $R_oL_o$。相同维数、相同状态名称或相同输出数值都不代替这些映射。

**命题 2.6（同源细化的响应条件）。** 对固定细律，$R_c r_*=Q R_f$ 蕴含 $\ker R_f\subseteq\ker(R_c r_*)$。对固定粗来源和选定提升 $L$，一个粗差分 $q$ 在细读口可见恰当且仅当 $R_fLq\ne0$；细空间中另一个差分的非零响应不足以证明此式。

**证明。** 第一项对 $R_fq=0$ 左乘 $Q$。第二项直接比较 $R_fLp$ 与 $R_fLp'$，差为 $R_fL(p-p')$。必须测的是这条传入方向；命题 12.2 给出新四角响应非零而传入方向仍盲的五态应用。$\square$

## 3. 抽象载体与相容局部截面

**定义 3.1（限制图上的截面）。** 设 $I$ 为集合指标的图式，每个顶点给出 $S_i$，每条限制箭头 $e:i\to j$ 给出 $r_e:S_i\to S_j$，并遵守声明的复合关系。相容截面集合为

$$
\Gamma(S,r)=\{(s_i)\in\prod_iS_i:\ r_e(s_i)=s_j\text{ 对每条 }e:i\to j\}.
$$

若研究概率律而非状态，则另定义 $\Gamma(\Delta,r_*)$。这两个截面问题不同，状态截面不存在不必导致概率截面不存在。

**命题 3.2（载体存在不等于相容实现）。** 任何集合指标的局部状态族都可置于抽象载体 $\bigsqcup_iS_i$。但下述两箭头图式有不同的状态相容性：两个顶点均取 $\{0,1\}$，两条平行箭头均为恒等时有两个截面；一条恒等、另一条取补时没有状态截面。

**证明。** 不交并通过 $(i,s)$ 保留每个局部状态，但不保证限制方程。两条恒等要求 $s_j=s_i$，可取零或一。恒等与取补同时要求 $s_j=s_i=1-s_i$，二值状态无解。不过均匀概率律在恒等和取补推前下均不变，所以第二图式仍有概率截面。$\square$

该应用区分三个问题：是否能造一个集合载体、指定接口是否相容、这些接口是否有共同物理实现。前一个问题的肯定答案不解决后两个；模型不声明全局物理来源也不否定它。

**假设 3.3（使用粘合的条件）。** 若局部对象实际构成拓扑空间上的集合层，限制满足层合同，则相容局部截面的唯一粘合采用 Stacks Project，Definition 6.7.1，Tag 006S。这里把层粘合作为已知中间工具，不由“局部观察者”这一名称推出层合同，也不把任意图式称为层。

对本卷的未来比较，只要所有 $R_hU_h$ 已拉回一个起始 $H_o$，就不需要另造跨所有观察者的全局来源。它是一个固定局部模型的联合反演问题，不是本体论结论。

## 4. 完整五态窗口与概率纤维

**定义 4.1（输入索引、输出标签与坐标）。** 长度三的禁相邻窗口为

$$
\Sigma_3=\{\varnothing,\{1\},\{2\},\{3\},\{1,3\}\}.
$$

索引 $1,2,3$ 是输入位点；FIB 输出字典分别为

$$
F(\varnothing)=\mathrm{null},\quad F(\{1\})=[2],\quad
F(\{2\})=[3],\quad F(\{3\})=[5],\quad F(\{1,3\})=[2,5].
$$

$[2,5]$ 是联合标签，不是乘积。写 $s_0,s_1,s_2,s_3,s_{13}$ 表示上述输入状态，并定义 $x=\mathbf1_{1\in I}$、$z=\mathbf1_{2\in I}$、$y=\mathbf1_{3\in I}$。几何坐标采用 $(x,z,y)$，概率分量采用 $(p_0,p_1,p_2,p_3,p_{13})$：

| 输入状态 | 输出标签 | 几何坐标 $(x,z,y)$ |
| --- | --- | --- |
| $\varnothing$ | $\mathrm{null}$ | $(0,0,0)$ |
| $\{1\}$ | $[2]$ | $(1,0,0)$ |
| $\{2\}$ | $[3]$ | $(0,1,0)$ |
| $\{3\}$ | $[5]$ | $(0,0,1)$ |
| $\{1,3\}$ | $[2,5]$ | $(1,0,1)$ |

五点凸包是以 $z=0$ 的单位正方形为底、$s_2$ 为顶点的四角锥。这一几何及其概率反解采用 [基础公式卷](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md) §§二–四作为本卷应用的中间结果，不另宣称发现一种新凸体。

**定义 4.2（保留的三均值）。** 固定局部观察者 $o$，令其完整候选集为 $\Sigma_3$，定义

$$
Pp=(X,Z,Y)^{\mathsf T},\qquad
P=\begin{pmatrix}0&1&0&0&1\\0&0&1&0&0\\0&0&0&1&1\end{pmatrix},\qquad
\kappa=p_{13}=\mathbb E_p[xy].
$$

$P$ 仅保留三个期望，不是逐样本 $(x,z,y)$ 的完整联合律。若实际仪器逐样本取得这个三元组，其五种取值已区分全部状态，该仪器的完整输出律不具有下面的盲纤维。

**命题 4.3（局部五态纤维的适用域）。** 使用上述既有五态反解，固定 $(X,Z,Y)$ 的可行概率律为

$$
\begin{aligned}
p_\kappa&=(1-X-Z-Y+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa)^{\mathsf T},\\
I(X,Z,Y)&=[\kappa_-,\kappa_+],\\
\kappa_-&=\max(0,X+Z+Y-1),\qquad \kappa_+=\min(X,Y).
\end{aligned}
$$

存在可行律恰要求 $X,Z,Y\ge0$ 且 $\kappa_-\le\kappa_+$。归一化三均值映射的带符号核为

$$
\ker\begin{pmatrix}\mathbf1^{\mathsf T}\\P\end{pmatrix}
=\operatorname{span}\{d\},\qquad d=(1,-1,0,-1,1)^{\mathsf T}.
$$

但可行纤维的仿射维数为一恰要求 $\kappa_-<\kappa_+$；两端相等时为零。

**证明。** 令 $p_{13}=\kappa$，三均值依次给出 $p_1=X-\kappa$、$p_2=Z$、$p_3=Y-\kappa$，总质量给出 $p_0$。五项非负恰给区间端点。对带符号质量使用总质量零的同一消元，得到任意核向量为 $td$。归一化加三个均值的秩为四；只有区间实际含两个点时，形式方向才产生概率纤维的一维变化。$\square$

不带总质量行的 $\ker P$ 是二维，例如 $e_0$ 也在其中。限制支持集可能去掉 $d$ 所需的角点而使纤维为零维；去掉顶点 $s_2$ 则仍可保留底面方向。概率边界 $X=0$ 强制 $\kappa=0$，所以完整五态字典本身也不保证每条可行纤维非退化。

**数学引文 4.4（最小窗口的限定）。** 对完整禁相邻集合 $\Sigma_n$，既有独立集计数递推给出 $|\Sigma_n|=\operatorname{Fib}_{n+2}$，其中 $\operatorname{Fib}_0=0,\operatorname{Fib}_1=1$。总质量和 $n$ 个占位均值在空集与各单点上独立，故带符号盲空间维数为 $|\Sigma_n|-n-1$。于是 $n=1,2,3$ 分别为零、零、一；这里的最小性只相对于这组完整窗口和一阶摘要，不是对所有观察者或物理结构的普遍最小性。相关归属见基础公式卷 §§二–四及输出闭包卷 §14；可行概率纤维还受支持面与边界限制。

## 5. 所有合法未来与完整记录质量

**定义 5.1（起始观察者的路径合同）。** 固定 $o$，$\mathcal L_o$ 包含从 $o$ 出发的全部允许有限动作—输出历史，包括空词 $\varepsilon$。每个历史 $h=e_1\cdots e_n$ 的转换具有正确的端点类型，且

$$
U_h=U_{e_n}\cdots U_{e_1}:H_o\to H_{o_h},\qquad U_\varepsilon=I.
$$

历史可以指定一个输出分支，此时 $U_h$ 保留该分支的联合次概率质量。端点状态必须足以定义后续合同；若当前状态不保留过去输出，须显式增加历史／记录状态，或在路径核中保留该联合记录。只观察终点状态不是完整历史观察。

**定义 5.2（路径记录的拉回）。** 每条 $h$ 给出已校准的线性记录映射 $R_h$，其输出包含合同要求的整份记录、分支概率及实际末端测试。令

$$
A_h=R_hU_h:H_o\to Z_h.
$$

若端点状态已经增广，$R_h$ 是该增广状态的记录推前；若 $h$ 固定了输出前缀，读出的是此前缀与剩余测试的联合质量。不同 $Z_h$ 可以有不同维数，所有 $A_h$ 的来源仍是 $H_o$。

Stop、未完成前缀和不终止结局按合同保留。若存在一致的无限记录概率律且观察事件由有限柱集生成，所有有限记录律确定该无限律；这是 [局部时钟核卷](AURIC_FIB_ATOM_LOCAL_CLOCK_KERNEL_AND_OUTPUT_RESOLVED_SEAM_VISIBILITY.md) Q6–Q7 所用的测度唯一性中间步骤。存在性、相容性和事件空间合同不能省略。

**假设 5.3（合法策略与共同实现）。** 每个允许策略只依赖已取得记录和已声明的控制器状态，并在该观察节点的全部可能状态上有合法动作，或把动作拒绝作为实际输出。记录族保留策略的全部分支，不为不同隐藏状态分别选有利动作，不删除失败或零成功率分支。若模型含外部输入、等待、环境或状态守卫，其联合核和更新规则属于合同。

**定义 5.4（累计盲空间）。** 在五态应用中保留基线 $P$，一般模型可将其替换为指定的当前线性摘要。定义

$$
\begin{aligned}
K_m&=\ker P\cap\bigcap_{h\in\mathcal L_o,\ |h|\le m}\ker A_h,\\
K_\infty&=\bigcap_{m\ge0}K_m.
\end{aligned}
$$

空词读口 $A_\varepsilon$ 计入 $K_0$；$P$ 的保留不假定它在每个未来端点都能重新测量。由累计族的包含关系，$K_{m+1}\subseteq K_m$，与端点维数是否变化无关。

**命题 5.5（共同起点的记录等价）。** 两个同模型概率律 $p,p'$ 的基线及全部长度不超过 $m$ 的精确记录律相同，恰当且仅当 $p-p'\in K_m$。全部声明的有限未来记录律相同，恰当且仅当 $p-p'\in K_\infty$。

**证明。** 对每个共同起点的线性读口，等式 $A_hp=A_hp'$ 等价于 $A_h(p-p')=0$，基线同理。对相应路径族取交即得结论。该证明不能用于来源域不同而未拉回的核。$\square$

**命题 5.6（末态重置不删除已发射记录）。** 在五态窗口定义两个子核

$$
U_1e_s=xy(s)e_0,\qquad U_0e_s=(1-xy(s))e_0.
$$

总转换将所有状态重置到 $s_0$，所以 $(U_0+U_1)d=0$；完整输出记录却满足 $\Pr_{p_\kappa}(1)=\kappa$。

**证明。** 每个输入恰发射一个二值输出并到达 $s_0$，故总核保持质量。$\mathbf1^{\mathsf T}d=0$ 给出平均重置湮灭 $d$，而 $\mathbf1^{\mathsf T}U_1d=xy^{\mathsf T}d=1$。这是输出闭包卷 §16 和局部时钟核卷 Q12 的既有例子在带类型路径合同中的应用：平均后继核不能代替逐输出记录核。$\square$

## 6. 概率律、受限族与取得界限

**命题 6.1（局部概率识别的正确空间）。** 将既有线性识别判据应用于定义 5.4，整个 $\Delta_o$ 的精确记录律识别条件为

$$
K_\infty\cap T_o=\{0\}.
$$

等价地，在读口族中增加总质量行后，其共同线性核为零。若只比较给定族 $\mathcal P\subseteq\Delta_o$，精确条件为

$$
(\mathcal P-\mathcal P)\cap K_\infty=\{0\}.
$$

**证明。** 记录碰撞的差分来自 $\mathcal P-\mathcal P$。对完整单纯形，若非零 $q\in K_\infty\cap T_o$，在严格正的均匀律 $p$ 附近取足够小 $t\ne0$，$p+tq$ 仍为概率律，且记录相同。反之任意不同概率律的差分都在 $T_o$，零交排除碰撞。增加总质量行就是额外与 $T_o$ 取交。$\square$

**命题 6.2（环境核不必为零）。** 两态概率律可由线性统计 $A(p)=p_1-p_2$ 唯一识别，但 $\ker A=\operatorname{span}\{(1,1)^{\mathsf T}\}$ 非零。

**证明。** $p_1+p_2=1$ 给 $p_1=(1+A(p))/2$、$p_2=(1-A(p))/2$。其核方向改变总质量，不是归一化概率律的可行差分。这里 $A$ 是允许的有符号期望摘要，不称其自身为非负输出律。$\square$

**命题 6.3（受限族不要求整个差分张成空间无盲点）。** 取 $\mathcal P=\{e_1,e_2,e_3\}$，$A=(0,1,2)$。$A$ 在该族上单射，但在 $\operatorname{span}(\mathcal P-\mathcal P)$ 上有非零核向量 $(1,-2,1)^{\mathsf T}$。

**证明。** 三个读数为零、一、二，故实际点对没有碰撞。所示向量总质量为零、被 $A$ 湮灭，并属于差分张成的二维切空间，但它不是这三个点之间的差分。

一般而言，$\operatorname{span}(\mathcal P-\mathcal P)\cap K_\infty=\{0\}$ 是充分条件。若 $\mathcal P$ 在其仿射包内包含一个相对开邻域，则每个足够小的张成方向可以实现为两可行点的差，因而该条件也必要；没有这一条件不能用张成空间替代实际差分集。$\square$

**命题 6.4（精确律分离不等于有限样本无误识别）。** 对非退化五态纤维 $X=Y=1/2,Z=0$，命题 5.6 的读口在概率律层面识别 $\kappa$，但任何固定有限个独立重复输出均不能无误确定所有 $0<\kappa<1/2$。

**证明。** 每次输出是 Bernoulli$(\kappa)$。任意长度 $n$ 的二值样本词在每个内点参数下都有严格正概率。因而同一样本词兼容两个不同参数，任何只依赖该词的确定估计不能同时精确等于二者。记录律的单射性不提供路径状态确定性、精确概率取得或固定样本预算。$\square$

**定义 6.5（存在、可取得与有效认证）。** 有限分离实验的存在指某个合法路径的精确律对所比较参数不同；可取得要求实际执行、制备和读口可用；有效认证还要求已知有效表示、完整合法路径生成、精确判等或误差界及终止准则。搜索、计算、样本、记忆、时间和校准成本分别属于指定资源合同。有限维的存在性结论不自动满足后两种要求。

## 7. 固定起点的有限见证与长度界

**命题 7.1（观察者变化不破坏有限线性见证）。** 固定 $D=\dim H_o<\infty$，即使端点观察者和记录维数变化，仍存在有限路径子族 $h_1,\ldots,h_k$ 和某个有限 $M$，使

$$
K_\infty=\ker P\cap\bigcap_{i=1}^k\ker A_{h_i}=K_M.
$$

因此完整声明族能识别局部概率律时，某个有限最大路径长度已经提供同样的线性识别条件。

**证明。** 使用标准有限维行空间／消去法作为中间步骤。从 $\ker P$ 开始，若当前交空间严格大于 $K_\infty$，取其中不属于 $K_\infty$ 的 $q$。存在某个有限 $h$ 满足 $A_hq\ne0$；加入该核使维数严格下降。最多 $D$ 次下降后达到 $K_\infty$。所选有限路径的长度最大值为 $M$，累计交空间夹在所得交空间与 $K_\infty$ 之间，故相等。若不需任何路径，可取 $M=0$。这个论证只证存在，不给路径搜索的有效终止证书。$\square$

**命题 7.2（任意路径依赖读口没有只依赖 $D$ 的长度界）。** 对任意 $N\ge1$，存在起始 $H_o=\mathbb R^2$ 的相容记录族，在长度 $N$ 前不区分两个隐藏状态，在长度 $N$ 区分。

**证明。** 令隐藏比特 $s\in\{0,1\}$ 不变，唯一动作逐次运行。条件完整记录为

$$
r_n(s)=
\begin{cases}
0^n,&n<N,\\
0^{N-1}s0^{n-N},&n\ge N.
\end{cases}
$$

取 $A_n$ 为 $r_n$ 的律推前，基线为总质量。前缀投影满足 $r_{n+1}|_n=r_n$，故记录相容。对 $q=(1,-1)^{\mathsf T}$，$A_nq=0$ 恰在 $n<N$，在 $N$ 时非零。这里读口显式依赖路径长度，或由外部已声明的日程启用。把日程实现为齐次内部控制时必须增加控制器状态；该例不是固定两态齐次仪器的任意延迟例。$\square$

因此一般的 $K_m=K_{m+1}$ 只表示当前两层相同，可以在很晚的深度再收缩。不能仅靠当前平台或已用采样时长认证完整闭包。

**假设 7.3（固定齐次仪器闭包）。** 若实际完整表示采用固定 $D$ 维状态、固定子核族 $B_{a,b}$ 和固定可用末端测试 $G$，合法性与控制都已正确编码，采用输出闭包卷 §15、定理 15.1 及其有限状态长度界。对本卷列质量约定，其测试递推为

此处完整记录词由该生成族的全部乘积给出；不合法续接以零质量或真实拒绝记录编码，不在递推之外另按长度或未编码权限剪枝。固定的反馈控制器若需要内部状态，该状态计入 $D$。

$$
V_0=\operatorname{span}(G),\qquad
V_{m+1}=V_m+\operatorname{span}\{B_{a,b}^{\mathsf T}f:f\in V_m\}.
$$

$G$ 包含常数一；一般实测试给期望，事件指示函数或 $[0,1]$ 随机测试才给概率。若 $V_{m+1}=V_m$，所有生成算子保持 $V_m$，所以平台即稳定。未稳定时维数至少增加一，因此

$$
V_{D-\dim V_0}=V_\infty.
$$

这是已知有限维闭包方法的应用，不另作为新一般定理；概率自动机线性等价算法的文献先例为 Tzeng，见数学引文 13.2。算法的具体表示与算术条件不由一个抽象有限起点保证。

五态 record-only 仪器取 $G=\{\mathbf1\}$，有响应时存在长度至多四的输出见证。若 $1,x,z,y$ 在每个端点都是实际允许的末端测试，则 $\dim V_0=4$，新增方向有响应时一步即可；仅在起点保留 $P$ 不满足这个末端测试假设。局部时钟核卷 Q9–Q11 明确了这些边界。

**定义 7.4（最小响应长度）。** 对起始带符号方向 $q$，定义

$$
\ell_*(q)=\min\{|h|:h\in\mathcal L_o,\ A_hq\ne0\},
$$

检测集合为空时取 $\ell_*(q)=\infty$。空词响应允许给出零；单点概率纤维无需估计参数，不把这种目标已知情形等同于形式方向的响应深度。此长度不是物理秒数或一次执行无误恢复的时间。

## 8. 空间稀疏化与未来模拟

**定义 8.1（质量推前与函数拉回）。** 局部稀疏化给出 $D:S_f\to S_t$。其质量映射与函数映射分别为

$$
(D_*p)_u=\sum_{s:D(s)=u}p_s,\qquad
(D^*f)(s)=f(D(s)),\qquad D^*=D_*^{\mathsf T}.
$$

二者满足配对关系

$$
f^{\mathsf T}D_*p=(D^*f)^{\mathsf T}p.
$$

所以稀疏化后的律读口拉回原来源为 $A_t=R_tD_*$；不能把函数拉回 $D^*$ 当作作用于原概率列向量的稀疏化。

**命题 8.2（同源读口后处理的单调性）。** 若原读口 $A_f$ 和拉回的稀疏读口 $A_t$ 满足

$$
A_t=Q A_f,
$$

则 $\ker A_f\subseteq\ker A_t$，故后处理不会增加这两个同源读口的分辨力。

**证明。** $A_fq=0$ 蕴含 $A_tq=QA_fq=0$。这正是目标恢复的后处理原则在局部稀疏接口中的应用。$\ker R_t\subset H_t$ 与 $\ker R_f\subset H_f$ 本身处在不同空间，未给共同来源时无此包含式。$\square$

**命题 8.3（稀疏映射不约束任意新传感器）。** 取 $S_f=\{0,1,2\}$、$S_t=\{a,b\}$，令 $D(0)=D(1)=a$、$D(2)=b$。原传感器只输出常数，稀疏传感器读取 $a,b$，则稀疏读口可区分原传感器忽略的方向。

**证明。** 两个同源矩阵为

$$
A_f=(1,1,1),\qquad
A_t=I_2D_*=\begin{pmatrix}1&1&0\\0&0&1\end{pmatrix}.
$$

取 $q=e_0-e_2$，有 $A_fq=0$、$A_tq=(1,-1)^{\mathsf T}\ne0$。因此不存在 $A_t=QA_f$ 的后处理。新传感器改变了合同，不能仅由 $D$ 合并状态就断言任意读口单调。$\square$

**假设 8.4（全部合法未来的模拟）。** 起始限制为 $D_0$，每个稀疏合法历史 $h$ 都有对应的完整历史 $\phi(h)$、端点限制 $D_h$ 及记录后处理 $Q_h$，满足

$$
U_h^t(D_0)_*=(D_h)_*U_{\phi(h)}^f,\qquad
R_h^t(D_h)_*=Q_hR_{\phi(h)}^f.
$$

对应须保留全部合法词和策略分支，包括失败与终止；逐边 intertwining 和复合相容可提供第一式。输出合并时允许 $\phi(h)$ 表示完整分支记录的相应集合，此时将其端点质量空间取直和，把各分支转换和记录合为一个正确类型的映射，再采用求和后处理。基线也要求相同来源的后处理关系。

**命题 8.5（未来单调性与被消除方向）。** 在假设 8.4 下，每个稀疏未来读口满足

$$
A_h^t(D_0)_*=Q_hA_{\phi(h)}^f.
$$

完整未来盲方向仍对稀疏未来盲。若 $(D_0)_*q=0$，此方向对任何只使用稀疏初态及其固定后续合同的读口永久盲。

**证明。** 依次代入转换与记录的两条相容式。若完整对应读口全部湮灭 $q$，后处理仍湮灭它；若 $(D_0)_*q=0$，直接有 $R_h^tU_h^t(D_0)_*q=0$。因此准确 intertwining 且没有额外输入时，稀疏动力学不能复活已经被 $D_*$ 合并的区别。$\square$

一个当前读口的核可在后续缩小，因为状态或环境仍保留区别；这不等于 $D_*q=0$ 后能在同一稀疏合同中复活。新边界输入、保留环境或额外传感器可能改变来源和合同，须重新声明其联合关系。

## 9. 局部等待核与联合响应

**定义 9.1（状态条件等待核）。** 固定局部五态模型，给出同一有限等待标签集 $W$ 上的已校准概率列 $K_s$。等待读口为

$$
C_Kp=\sum_s p_sK_s,\qquad
\Delta_{13}K=K_0-K_1-K_3+K_{13}=C_Kd.
$$

若使用实等待时间，$K_s$ 改为同一可测空间上的概率测度；包含无限等待、Stop 和不返回时明确扩张标签。其四角差是总质量为零的符号测度。等待核、输出与后继联合核、平均等待和初始危险率各有不同合同。

**命题 9.2（已知局部时钟的非退化响应）。** 固定一个非退化五态纤维以及可行基点 $\kappa_0\in I$，则

$$
C_Kp_\kappa=C_Kp_{\kappa_0}+(\kappa-\kappa_0)\Delta_{13}K.
$$

等待律在此纤维上单射恰要求 $\Delta_{13}K\ne0$；非零响应事件 $E$ 给出

$$
\kappa=\kappa_0+
\frac{C_Kp_\kappa(E)-C_Kp_{\kappa_0}(E)}{\Delta_{13}K(E)}.
$$

**证明。** 概率差为 $(\kappa-\kappa_0)d$，对其应用 $C_K$。非零有限向量或符号测度有非零坐标／事件响应，该坐标的仿射式单射；响应全零时任意两个可行参数记录相同。这里直接应用局部时钟核卷定理二的 Q1–Q4 限定，不把它作为新的固定核反演定理。$\square$

使用可行基点避免把 $p_0$ 当作一定非负的概率律。若该事件概率的估计误差为 $\epsilon$，且基线和核精确已知，反演误差至多 $\epsilon/|\Delta_{13}K(E)|$；没有响应下界就没有统一稳定性或样本成本结论。

**命题 9.3（平均等待可盲而等待律有响应）。** 取

$$
K_0=\tfrac12\delta_0+\tfrac12\delta_2,\qquad
K_1=K_2=K_3=K_{13}=\delta_1.
$$

所有状态条件均值为一，但 $\Delta_{13}K\ne0$，所以精确等待律可识别非退化 $\kappa$，均值不能。

**证明。** 均值四角差为 $1-1-1+1=0$，完整差为 $\tfrac12\delta_0+\tfrac12\delta_2-\delta_1$。这应用局部时钟核卷 Q5 的例子；它不是把一个平均速率替换成完整等待核。$\square$

**命题 9.4（未知响应强度与初始律会混淆）。** 固定 $X=Y=1/2,Z=0$，令除 $s_{13}$ 外的等待核均为 $\delta_0$，而

$$
K_{13}^{\alpha}=(1-\alpha)\delta_0+\alpha\delta_1,\qquad 0<\alpha\le1.
$$

则输出一的概率为 $\alpha\kappa$；不同 $(\alpha,\kappa)$ 可给相同基线和等待律。

**证明。** $(\alpha,\kappa)=(1/2,1/4)$ 与 $(1,1/8)$ 均给 $1/8$。每个固定 $\alpha$ 的四角差非零，但共同反演不能同时确定二者。此为局部时钟核卷 Q2 的校准反例，说明假设 1.4 不可省略。$\square$

## 10. 路径钟、作用量与接口同步

**定义 10.1（非负路径长度）。** 对局部状态图的实际合法边 $e:s\to t$，给定数值读出 $g_o:S_o\to\mathbb R^k$ 和范数，令

$$
\lambda_o(e)=\|g_o(t)-g_o(s)\|,\qquad
\tau_o(e_1\cdots e_n)=\sum_{i=1}^n\lambda_o(e_i).
$$

$\tau_o$ 是可加路径长度或选定的钟约定，单位由 $g_o$ 决定。独立给出每步作用量 $a_o(e)$ 后定义 $\mathcal A_o(\gamma)=\sum_ea_o(e)$，其单位由作用量合同决定。称 $a_o$ 为物理或热力学作用量需要相应物理模型，不由可加性得到。

物理速率还需独立校准的正时长 $\Delta t(e)$，例如 $\lambda_o(e)/\Delta t(e)$。没有这种校准，非负变化范数既不是每秒变化率，也不自动是经过的秒数。

**命题 10.2（可逆边的长度不是非零势增量）。** 若 $e$ 和反向边 $\bar e$ 均合法，非负对称长度 $\lambda(e)=\lambda(\bar e)$ 不可能同时等于某个状态势 $t$ 的增量，除非该边长度为零。

**证明。** 势增量满足 $t(e^+)-t(e^-)=-[t(\bar e^+)-t(\bar e^-)]$，而两个长度相等且非负，所以只能都为零。路径积分、状态势和不同钟图之间的有符号偏移是三种不同数据。观察者时空卷定义 6.3 已区分路径钟与状态势。$\square$

**定义 10.3（共同尺度的指定钟接口）。** 给每个观察者实际事件域 $X_o$ 和已换算到共同单位的钟标签 $t_o:X_o\to\mathbb R$。在给定重叠事件及配对合同上，接口边 $o\to o'$ 的常数偏移定义为

$$
c_{oo'}=t_{o'}(x)-t_o(x),\qquad x\in X_o\cap X_{o'},
$$

并要求该差与选定重叠事件无关。反向使用 $c_{o'o}=-c_{oo'}$。常数同步指存在 $a_o$ 及共同事件标签 $T$，使

$$
t_o(x)=T(x)+a_o,\qquad c_{oo'}=a_{o'}-a_o.
$$

重叠识别、共同尺度和偏移常数性均是额外条件；无这些条件的钟读数不进入此模型。

**命题 10.4（指定钟同步的闭走法条件）。** 在连通底层无向接口图上，指定偏移存在势 $a_o$ 恰当且仅当每条有限有符号闭走法的偏移和为零。非零闭和只排除这些钟在定义 10.3 下的常数同步。

**证明。** 必要性为势增量沿闭走法望远镜相消。充分性采用观察者时空卷定义 6.3 的已知图积分方法：选根 $o_0$，令 $a_o$ 为从根到 $o$ 的有符号路径和。任意两条路线构成闭走法，零和使定义与路线无关，每条边的差正是指定偏移。于是调整后的 $t_o-a_o$ 在声明的重叠上相等；若这些重叠完整覆盖共同事件域，即按已知集合粘合得到 $T$。若只提供部分接口，则结论只同步这些接口。$\square$

只检查有向环不够。例如有向无环菱形 $r\to a\to t$、$r\to b\to t$，前一路总偏移为零，后一路总偏移为一，就有底层有符号闭走法障碍。缺少有向环不消除两条同端点路线的不一致。

**命题 10.5（两个钟接口应用）。** 三角形偏移 $c_{01}=1,c_{12}=1,c_{20}=-2$ 可同步；改为 $c_{20}=1$ 则不能在共同尺度加常数模型中同步。

**证明。** 第一组取 $(a_0,a_1,a_2)=(0,1,2)$。第二组闭和为三，与任何势差相消矛盾。结论不排除重新定义钟、引入不同尺度、使用另一个时间参数或另一个空间模型；没有关于所有全局时间的否定，也没有关于广义相对论的排除。$\square$

## 11. 同源投影与目标恢复

**定义 11.1（候选关系源的多读口）。** 给定一个局部候选关系对象 $\mathbf T_o$，可定义空间摘要 $h_o$、钟读口 $\rho_o$、因果核选择和引力候选读口 $G_o$ 为其函数。共同来源使联合合同可以被明确讨论，但不自动证明统计依赖、函数依赖或独立物理场数减少。

**命题 11.2（同源可容纳独立读口）。** 令 $\mathbf T=(B_1,B_2)$ 为两个独立公平比特，$h(\mathbf T)=B_1$、$\rho(\mathbf T)=B_2$。两者来自同一对象而独立，且不存在 $\rho=f(h)$。

**证明。** 四个源点均有概率 $1/4$，联合概率等于边缘乘积。在每条固定 $B_1$ 的纤维上，$B_2$ 仍可为零或一，故不可能为 $B_1$ 的函数。把变量打包成一个元组不减少其统计自由度。$\square$

**命题 11.3（FIB 空间摘要不确定响应钟）。** 对完整五态非退化纤维，取 $h(p)=Pp$、$\rho(p)=p_{13}$，则 $\rho$ 不能由 $h$ 唯一恢复。取命题 9.2 的等待读口且 $\Delta_{13}K\ne0$ 时，同样不能由 $P$ 恢复完整等待律。

**证明。** 应用观察者时空卷定义 1.3 的既有纤维恒定／实际像因子化判据：$\rho=f\circ h$ 当且仅当 $\rho$ 在每条 $h$ 纤维上恒定。这里 $Pd=0$，但 $\rho(d)=1$；两个不同可行 $\kappa$ 给同一 $P$ 和不同 $\rho$。等待律的差为 $(\kappa-\kappa')\Delta_{13}K$，故同样失败。

对完整线性来源，因子化为线性读口等价于 $\ker h\subseteq\ker\rho$；对概率或受限来源须使用实际差分，而不是无条件套用环境核。这里的钟或引力标签仍是候选数值读口，没有建立物理身份。$\square$

**定义 11.4（原生计数的三种目标）。** 对声明的实际计数函数 $n:S_o\to\mathbb N$，区分期望目标 $n^{\mathsf T}p$、计数律目标 $C_np$，以及一次实现的隐藏计数 $n(s)$。其中 $C_n$ 是 $n$ 的概率推前。识别初始概率律不等于在一次非单射随机观测后确定隐藏状态。

**命题 11.5（五态期望计数可以不需要 seam）。** 对输出标签的加和计数

$$
n(s)=2x(s)+3z(s)+5y(s),
$$

其值依概率次序为 $(0,2,3,5,7)$，期望为 $2X+3Z+5Y$，与 $\kappa$ 无关；计数律则在此五态上确定全部初始律。

**证明。** $n^{\mathsf T}d=-2-5+7=0$，故期望在纤维上恒定。五个计数值互异，$C_n$ 只是给状态律重新标记，其中 $\Pr(n=7)=\kappa$。所以“恢复 Fibonacci 计数”必须声明是哪个目标，不能统一改写为全部状态识别。这个加和计数到具体树上的原生 Read 计数仍需接口桥；基础公式卷 §一提供组成与 Fibonacci 数的已知对应，不自动识别任意未来仪器的 Read 数。$\square$

**命题 11.6（可见计数与不可见扰动位）。** 取 $S=\Sigma_3\times\{0,1\}$，所有传感器和后续核仅依赖第一分量，且读口给出命题 11.5 的计数。则计数律可恢复，完整局部律未必可恢复。

**证明。** 第一分量相同、第二分量分别为零和一的点质量给出相同计数及全部声明的未来记录，但完整律不同。可见目标和不可见扰动位可共存；目标充分性弱于完整状态律充分性。$\square$

**命题 11.7（未来目标的差分条件）。** 对给定概率族 $\mathcal P$ 和线性目标 $T$，声明的全部未来读数能够确定 $Tp$，恰要求

$$
(\mathcal P-\mathcal P)\cap K_\infty\subseteq\ker T.
$$

在完整五态固定纤维上，若 $Td=0$，目标已由基线固定；若 $Td\ne0$ 且纤维非退化，则恢复该目标恰要求某条合法路径响应 $A_hd\ne0$。

**证明。** 先采用既有实际像因子化判据：记录碰撞不能给不同目标。命题 5.5 把碰撞改写为所示差分集合，便得第一式。在五态纤维中所有差分均为 $(\kappa-\kappa')d$。$Td=0$ 给目标恒定；$Td\ne0$ 时两个不同参数目标不同，故需要且足够使未来记录在参数上单射。$\square$

**假设 11.8（取得核变化与初始纤维的桥）。** [取得核盲方向卷](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_KERNEL_BLIND_DIRECTIONS_AFTER_PAIRED_CALIBRATION.md) Conventions 1.1–2.5、§§5、7–9 比较的是省略了取得核的模型参数族。其未来算子随参数变化，完整控制、Stop、风险次序及资源合同均保留。把那里的参数变化等同于这里固定算子的初始差分 $d$，须给出共同实现、参数映射和全部记录律相等的证明；本卷不假定已有此桥。该卷的固定核反演引用与未知核障碍是不同问题，增长状态数的延迟族也不反驳固定五态齐次闭包界。

## 12. 五态来源上的观察者接口综合

**定义 12.1（固定局部综合合同）。** 固定起始观察者 $o$，取完整五态 $S_o=\Sigma_3$、一个非退化可行区间 $I(X,Z,Y)$、已知基线 $P$ 和一套固定校准的全部合法路径族 $\mathcal L_o$。每条路径使用定义 5.1–5.3 的同源联合记录映射，令

$$
v_h=A_hd,\qquad h\in\mathcal L_o.
$$

$v_h$ 是这个起始纤维对该路径记录的响应，不是端点任意形式 seam 的响应。不同观察者之间能否比较，已经由 $U_h$ 的类型、共同实现和合法性承担。

**命题 12.2（细提升存在但新响应未接上来源）。** 取细状态 $S_f=\Sigma_3\times\{0,1\}$，限制 $r(s,b)=s$，提升 $Le_s=e_{(s,0)}$。细读口保留粗基线，并加入事件测试 $g(s,b)=xy(s)b$。在 $b=1$ 层的四角响应为一，但新增读口沿提升来源 $Ld$ 的响应为零。

**证明。** $r_*L=I$，故这是确实满足右逆条件的提升。在细读口中把粗摘要写为 $Pr_*$，粗读口由投影后处理得到。$b=1$ 层上 $g$ 的四角值为 $0,0,0,1$，四角差为一；但 $g^{\mathsf T}Le_s=0$ 对所有 $s$ 成立，所以 $g^{\mathsf T}Ld=0$，且 $Pr_*Ld=Pd=0$。取恒等动力学与这些固定读口可得动态相容例。非零新 seam 属于另一细方向，没有接到被选择的粗来源扩展。$\square$

**命题 12.3（边缘钟与作用标签均盲，联合记录可见）。** 在 $X=Y=1/2,Z=0$ 的纤维上，给出两个二值候选记录标签 $(w,a)$ 的同源联合核。令

$$
\begin{aligned}
J_0=J_{13}&=\tfrac12\delta_{(0,0)}+\tfrac12\delta_{(1,1)},\\
J_1=J_3&=\tfrac12\delta_{(0,1)}+\tfrac12\delta_{(1,0)},
\end{aligned}
$$

$J_2$ 可取任意具有相同公平边缘的核。则两个单独边缘都不依赖 $\kappa$，而 $\Pr_{p_\kappa}(w=1,a=1)=\kappa$。

**证明。** 各状态核的两个边缘均为公平二值律，故边缘响应为零。此纤维有 $p_0=p_{13}=\kappa$、$p_1=p_3=1/2-\kappa$、$p_2=0$，所以联合事件 $(1,1)$ 的质量为 $(p_0+p_{13})/2=\kappa$，响应为一。若稀疏化只保留其中一个边缘，它是联合律的有效后处理，恰删除这个响应。该例的标签可用作时钟—作用量候选接口，但未给出秒、能量或物理作用量校准。$\square$

**命题 12.4（观察者相对五态未来响应综合）。** 在定义 12.1 的完整合同下，任意 $\kappa,\kappa'\in I$ 和全部合法 $h$ 满足

$$
A_hp_\kappa-A_hp_{\kappa'}=(\kappa-\kappa')v_h.
$$

因此同一基线纤维中的两个参数拥有相同全部声明记录律，恰当且仅当

$$
(\kappa-\kappa')v_h=0\qquad\forall h\in\mathcal L_o.
$$

由此得到以下局部应用条件：存在一个非零 $v_h$，就足以在非退化已知纤维上识别初始概率律；全部 $v_h$ 为零，则整个纤维对该声明族永久盲。后处理型稀疏化不能增加这条纤维的分辨力；增加观察者或细化读口，只有实际拉回响应非零才缩小该纤维。

**证明。** 先用既有五态仿射反解，$p_\kappa-p_{\kappa'}=(\kappa-\kappa')d$；再将每个正确类型的联合记录映射应用于差分，得到首式。基线 $P$ 对该差分为零，总质量也为零，所以全部记录相等正是第二式。此步骤把静态纤维接到所有可变端点观察者，未把其各自核直接混合。

若 $v_{h_*}\ne0$，选记录事件或允许测试 $E$ 使响应 $c\ne0$，并选可行基点 $\kappa_0$，则

$$
(A_{h_*}p_\kappa)(E)=(A_{h_*}p_{\kappa_0})(E)+(\kappa-\kappa_0)c.
$$

两个不同可行参数不能给相同精确律，逆式由除以 $c$ 得到；其统计与校准条件仍按命题 6.4、9.2 保留。非退化条件使必要性有实质内容：若所有响应为零，至少两个不同可行参数确实无法区分；若区间是单点，参数本已固定，不能以形式响应是否非零判定待恢复信息。

若有效稀疏模拟满足假设 8.4，则沿原五态来源的响应为

$$
\widetilde v_h=A_h^t(D_0)_*d=Q_hv_{\phi(h)}.
$$

原来相同的完整记录仍给相同稀疏记录；若 $(D_0)_*d=0$，所有稀疏响应为零。若 $Q_hv_{\phi(h)}\ne0$，该稀疏接口保留一个分离见证；若每个后处理响应都为零，原模型可以可见而稀疏接口不可见。命题 12.3 明确实现了后一种情况。

对于另一观察者 $o'$ 的提升或边界扩展 $L:H_o\to H_{o'}$，相应新路径响应为 $R_{h'}U_{h'}Ld$。这个量非零才提供当前纤维的新区别；随机右逆、图式相容或端点四角差非零各自都不足以代替它，命题 12.2 给出直接反例。反之只要它非零，就应用相同的事件响应逆式，无须另假设全局物理来源。

固定五维起点还由命题 7.1 得到有限路径子族见证，尽管端点模型可以变化。任意路径依赖族没有统一最大长度；若另满足固定齐次完整仪器条件，才使用假设 7.3 的已知闭包界。这些是同一综合合同下不同假设的后果，不是所有有限观察者需要实际无限数据的结论。$\square$

**定义 12.5（联合物理目标的开放条件）。** 时间—作用量和空间—引力的经验候选可分别写为：对实际同源路径记录和已校准单位，检验某个明确给定的联合核 $J_o^{\tau,\mathcal A}$；对实际空间读口变化 $\delta h_o$，检验 $G_o=\mathcal G_o(\delta h_o)$ 或相应带误差的预测关系。$\rho_o=\mathcal R_o(\delta h_o)$ 也须说明 $\rho_o$ 是长度、速率、等待统计还是钟偏移。

这些关系的物理实现与经验成立性为 open：缺少所需来源桥、传感器／控制动力学、单位校准和观测误差合同。命题 12.4 给出候选接口应满足的分离判据，不证明物理身份，也不否定存在其他全局时空描述。局部 FIB seam 的作用是指出该观察者基线遗漏的联合概率方向；其可见性、目标用途和取得成本由实际声明的接口分别决定。

## 13. 数学来源与适用范围

**数学引文 13.1（仓内中间结果）。** 本卷把以下既有数学散文作为具名中间原料，保留其条件；引用不把散文升级为内核证明，也不以综合改写取得原创性。

| 来源 | 本卷直接复用的范围 |
| --- | --- |
| [观察者相对时空的因果—相容—恢复理论](OBSERVER_RELATIVE_SPACETIME_CAUSAL_COMPATIBILITY_RECOVERY.md) | 定义 1.3 的实际像因子化；定义 2.2、假设 2.3 的相容视图；定义 6.3 的路径钟与势；§16 的物理桥；§20 的固定线性可观测接口 |
| [FIB-ATOM 金字塔基础公式](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md) | §§一–四的输入、组成计数、五模式函数与概率反解；其坐标次序在本卷显式换为 $(x,z,y)$ |
| [局部时钟核与输出分辨 seam 可见性](AURIC_FIB_ATOM_LOCAL_CLOCK_KERNEL_AND_OUTPUT_RESOLVED_SEAM_VISIBILITY.md) | 定理二及 Q1–Q5 的已知核纤维响应；Q6–Q11 的完整记录、无限律与齐次闭包；Q12、Q16 的平均重置及跨模型条件 |
| [静态隐藏纤维与输出分辨仪器闭包](AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md) | §15 定理 15.1 的全部输出词闭包及有限状态长度界；§16 的平均核抵消；§19 的五态响应条件；行质量约定在本卷转置为列质量 |
| [配对校准后的取得核盲方向](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_KERNEL_BLIND_DIRECTIONS_AFTER_PAIRED_CALIBRATION.md) | Conventions 1.1–2.5 和 §§5、7–9 的未知核、完整停止记录、延迟及资源边界；不把其参数方向认作本卷的初始律方向 |

**数学引文 13.2（经典合同与归属）。** 以下已知方法仅作为局部接口应用的中间工具。

| 文献 | 精确使用范围 |
| --- | --- |
| John G. Kemeny、J. Laurie Snell，*Finite Markov Chains*，Springer 重印本，§6.3，Theorem 6.3.2，[出版社书目](https://link.springer.com/book/9780387901923) | `literature-attested`：分块转移质量对块内状态相同的 Markov lumpability 合同；本卷使用的 intertwining 式还需另保留输出和合法性 |
| Wen-Guey Tzeng，*A Polynomial-Time Algorithm for the Equivalence of Probabilistic Automata*，SIAM Journal on Computing 21(2)，216–227，[DOI:10.1137/0221017](https://doi.org/10.1137/0221017) | `literature-attested`：有限线性表示上的概率自动机等价方法；不向任意路径依赖传感器或未知实数模型移植多项式复杂度 |
| The Stacks Project，Section 6.7，Definition 6.7.1，[Tag 006S](https://stacks.math.columbia.edu/tag/006S) | `literature-attested`：实际层合同下相容截面的唯一粘合；任意观察者图式不自动满足该合同 |

**约定 13.3（综合的内容边界）。** `repo-derived` 指本卷在固定五态起始纤维上组合带类型观察者传输、全合法路径、概率切空间、稀疏模拟和局部联合读口的应用推导，尤其命题 12.2–12.4。它不表示一般线性代数、概率识别、层粘合、Markov lumping 或仪器闭包的方法原创。本卷的物理候选保留定义 12.5 的 open 条件，模型反例仅反驳所指接口推断。

## 追加锚（本行以下为增补区）
## 14. Exact \(m=1\) common-teacher quotient certificate

This appendix compares deterministic actions on an independent four-window source with deterministic actions that use only the pair of priority-teacher labels. Loss factorization, literal action factorization, and existence of an optimal quotient replacement are distinct properties. The statements concern the ordinary finite probability model defined below.

### 14.1 Fixed source, teachers, record, and action classes

Let
\[
W=(\mathrm{zero},\mathrm{low},\mathrm{middle},\mathrm{ends},\mathrm{high})
 \cong(\varnothing,\{1\},\{2\},\{1,3\},\{3\}).
\]
For \(0<s\leq 1/5\), put
\[
p_s(\mathrm{zero})=p_s(\mathrm{middle})=(1-3s)/2,\qquad
p_s(\mathrm{low})=p_s(\mathrm{ends})=p_s(\mathrm{high})=s,
\quad \mu_s=p_s^{\otimes4}=\operatorname{extremal}(s)^{\otimes4}.
\]
The four coordinates are independent complete windows; this is not a seam-conditioned concatenation. Write \(L_j\) and \(H_j\) for the first and last endpoint bits of \(w_j\). Thus
\[
(\mathrm{zero},\mathrm{low},\mathrm{middle},\mathrm{ends},\mathrm{high})
\mapsto(0,0),(1,0),(0,0),(1,1),(0,1).
\]
With the original priority retained, define
\[
 A(w)=\begin{cases}1&H_0L_1=1,\\2&H_0L_1=0,\ H_1L_2=1,\\0&\text{otherwise},\end{cases}
\quad
 B(w)=\begin{cases}1&H_0L_2=1,\\2&H_0L_2=0,\ H_2L_3=1,\\0&\text{otherwise}.\end{cases}
\]
Here \(A\) is the \((0,1,2)\) teacher and \(B\) is the \((0,2,3)\) teacher. The available record is the deterministic postprocessing
\[
Q(w)=(A(w),B(w))\in\{0,1,2\}^2.
\]
The complete input is already available; forming \(Q\) is postprocessing of that input. A full-word action is a deterministic \(f:W^4\to\{0,1,2\}\); a quotient action is a deterministic \(g:\{0,1,2\}^2\to\{0,1,2\}\), consumed as \(g\circ Q\). Both risks use the same \(\mu_s\):
\[
R_A(f)=\mu_s[f\ne A],\quad R_B(f)=\mu_s[f\ne B],\quad
V_{\rm full}=\min_f\max(R_A(f),R_B(f)),\quad
V_Q=\min_g\max(R_A(g\circ Q),R_B(g\circ Q)).
\]

The full-word supplier `SharpRisk.sharp_risk_full`, with \(n=4,q=1,r=2,v=3\) (so \(m=q.\mathrm{val}=1\)), and the common majority/exterior-capacity construction `CommonSelector.uniform_mass_balanced` give, under exactly these independent-window and priority hypotheses (scientific sources in §14.6),
\[
V_{\rm full}(s)=T(1,s)=8s^2-18s^3+4s^4,\qquad 0<s\leq1/5.
\]
The supplier provides one deterministic full-word classifier with both individual risks equal to this threshold.

### 14.2 The six disagreement fibers

The endpoint probabilities needed for a direct expansion are
\[
\Pr(H_j=1)=\Pr(L_j=1)=2s,\quad
\Pr(H_j=L_j=1)=s,\quad
\Pr(H_j=L_j=0)=1-3s.
\]
Expanding the two priority tests over the independent coordinates gives the six nonempty disagreement fibers in the order
\[
(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)
\]
with masses \(4s^2b_i\), where
\[
(b_1,\ldots,b_6)=
(1-3s,\ 1-2s,\ 1-2s-2s^2,\ 2s^2,\ 1-3s+2s^2,\ s). \tag{14.1}
\]
Conditioning on \(H_0\) gives the expansion. If \(H_0=0\), the only disagreements are \((0,2)\) and \((2,0)\), each of mass
\(4s^2(1-3s+2s^2)\). If \(H_0=1\), the contributions to
\((0,1),(0,2),(1,0),(1,2),(2,1)\) are respectively
\[
4s^2(1-3s),\quad4s^3(1-2s),\quad
4s^2(1-2s-2s^2),\quad8s^4,\quad4s^3.
\]
These disjoint cases sum to (14.1). Hence the total disagreement mass is
\[
D=4s^2\sum_i b_i=16s^2-36s^3+8s^4=2T(1,s). \tag{14.2}
\]

### 14.3 Whole-fiber criterion and the finite lower certificate

On a diagonal fiber \((a,a)\), output \(a\) weakly improves both losses. On an off-diagonal fiber \((a,b)\), a third label is weakly dominated by either \(a\) or \(b\). Thus, after these pointwise improvements, a deterministic quotient rule selects a set \(S\) of complete off-diagonal fibers on which it outputs \(A\), and outputs \(B\) on the other disagreement fibers. If
\[
x=4s^2\sum_{i\in S}b_i,
\]
then
\[
(R_A,R_B)=(D-x,x). \tag{14.3}
\]
Consequently, the exact deterministic realization criterion is global:
\[
V_Q=V_{\rm full}=D/2
\quad\Longleftrightarrow\quad
\text{some union of entire disagreement fibers has mass }D/2. \tag{14.4}
\]
Indeed every action has \(R_A+R_B\ge D\); equality at the lower bound forces no diagonal or third-label error, and then (14.3) forces \(x=D/2\). Conversely such a union gives both risks \(D/2\). This is one half of the total disagreement mass, not one half inside every fiber.

It remains to solve the six-term subset problem. Put
\[
h=\frac{D}{8s^2}=2-\frac92s+s^2.
\]
Call \(1,2,3,5\) in (14.1) large and \(4,6\) small. For a subset with at most one large term,
\[
\sum_{i\in S}b_i\le 1-s+2s^2,\qquad
h-\sum_{i\in S}b_i\ge1-\frac72s-s^2\ge\frac{13}{50}. \tag{14.5}
\]
For three large terms, the three-smallest direct comparison is
\(b_1+b_3+b_5=3-8s\), giving the same lower bound in (14.5); four large terms give a larger sum and the bound remains valid. The subset \(\{2,3\}\) has distance at most \(s/2\), so no minimizer has zero, one, three, or four large terms.

For exactly two large terms, substituting the four possibilities for adding \(b_4\) and \(b_6\) gives the complete table
\[
\begin{array}{c|c}
\text{large pair}&\min_{E\subseteq\{4,6\}}
\left|\sum_{i\in\mathrm{pair}\cup E}b_i-h\right|\\ \hline
\{1,2\},\{3,5\}&s(1/2-s)\\
\{1,3\},\{1,5\},\{2,3\},\{2,5\}&s|1/2-3s|.
\end{array}
\]
Since \(|1/2-3s|\le1/2-s\) on \(0<s\le1/5\), (14.5) and this table prove
\[
\min_{S\subseteq\{1,\ldots,6\}}
\left|\sum_{i\in S}b_i-h\right|=s|1/2-3s|. \tag{14.6}
\]
Multiplying (14.6) by \(4s^2\) yields the exact quotient value
\[
\boxed{V_Q(s)=T(1,s)+2s^3|1-6s|}. \tag{14.7}
\]

A single common rule attaining (14.7) for every allowed \(s\) is
\[
g_\ast(a,b)=
\begin{cases}
a,&(a,b)\in\{(0,2),(1,0)\},\\
b,&\text{otherwise}.
\end{cases} \tag{14.8}
\]
It selects \(b_2+b_3=2-4s-2s^2\), so the two risks from this one action are
\[
R_A(g_\ast Q)=8s^2-20s^3+16s^4,\qquad
R_B(g_\ast Q)=8s^2-16s^3-8s^4. \tag{14.9}
\]
Their maximum is (14.7). Since \(s>0\), (14.7) equals the full-word threshold exactly at \(s=1/6\). This is an attainment statement for the deterministic quotient on this product law; it does not assert that every full-word minimizer factors through \(Q\).

### 14.4 Uniform atomic obstruction and a fine-word witness

At \(s=1/5\), every state in \(W\) has mass \(1/5\), so every word has mass \(1/625\). Direct endpoint splitting gives
\[
625\,\mu_s[A=a,B=b]=
\begin{pmatrix}
345&40&60\\
52&40&8\\
48&20&12
\end{pmatrix}_{a,b}. \tag{14.10}
\]
The six off-diagonal fiber counts are \(40,60,52,8,48,20\), all divisible by \(4\), and total \(228\). After the dominance reductions, each quotient-side error count is a multiple of \(4\), while their sum is \(228\); hence one is at least \(116\). For any unreduced quotient rule, correcting a diagonal output replaces the loss pair \((1,1)\) by \((0,0)\), and replacing a third label on an off-diagonal fiber replaces \((1,1)\) by \((0,1)\) or \((1,0)\). These replacements remain constant on each record fiber and weakly decrease each risk. The original rule therefore has maximum error count at least that of its reduced rule, hence at least \(116\). Rule (14.8) selects \(60+52=112\) atoms for \(A\), giving error counts \((116,112)\), so
\[
V_Q(1/5)=116/625,\qquad V_{\rm full}(1/5)=T(1,1/5)=114/625. \tag{14.11}
\]

The full-word lower bound \(R_A+R_B\ge D\) is attained by a single fine action: start with \(g_\ast Q\), then on exactly
\[
(\mathrm{high},\mathrm{zero},\mathrm{low},\mathrm{zero}),\qquad
(\mathrm{high},\mathrm{middle},\mathrm{low},\mathrm{zero})
\]
change the output on record \((0,1)\) from \(B=1\) to \(A=0\). Each word has mass \(1/625\); the resulting one classifier has error counts \((114,114)\). Thus the full-word optimum exists on the original source while no deterministic \(Q\)-action reaches it. The obstruction is literal whole-fiber divisibility, not a failure of loss measurability.

### 14.5 Loss factorization, action factorization, and randomized comparison

For a fixed action label \(c\), the pair of loss functions factors through \(Q\):
\[
\ell(w,c)=\bigl(\mathbf1_{c\ne A(w)},\mathbf1_{c\ne B(w)}\bigr)
=\bar\ell(Q(w),c),\qquad
\bar\ell((a,b),c)=\bigl(\mathbf1_{c\ne a},\mathbf1_{c\ne b}\bigr).
\]
A specified full-word action \(f\) factors literally as \(g\circ Q\) if and only if it is constant on every \(Q\)-fiber: necessity follows from composition, and sufficiency defines \(g(y)\) by the common value on that fiber, arbitrarily off the image. Every word has positive mass for the stated parameter range, so an almost-sure factorization is also a pointwise factorization here. Existence of some optimal quotient replacement is the different condition (14.4); it does not require a specified full-word minimizer to descend.

For any full-word action \(f\), conditional averaging on the actual record gives
\[
\pi(c\mid y)=
\frac{\mu_s\{w:Q(w)=y,\ f(w)=c\}}{\mu_s\{w:Q(w)=y\}}
\]
when the denominator is positive. Because both teacher labels are functions of \(y=Q(w)\), the randomized record action \(\pi\) has exactly the same pair \((R_A,R_B)\) as \(f\). This is the finite same-source content of Blackwell-style randomized comparison. It is a randomized consumer and therefore does not define \(V_Q\).

A non-atomic purification theorem (Dvoretzky--Wald--Wolfowitz type) cannot be invoked for this source: \(W^4\) is finite and every atom is positive. The record fibers impose the finite partition condition (14.4), with the exact subset-sum discrepancy (14.6). Conditional averaging preserves the two risks but need not select a single label on each fiber. Equality of marginal risks, an abstract record compatibility, or a randomized kernel does not make \(f\) literally constant on \(Q\)-fibers.

The consumer in (14.8) is one deterministic \(g_\ast\) applied to the original record \(Q\), under the same source law for both risks. No extra read, conditional resampling, external coin, omitted branch, change of source, or separate teacher-wise optimizer is part of this action class. Since \(D>0\) throughout \(0<s\le1/5\), no action has both teacher risks zero; equality at \(s=1/6\) is attainment of the positive full-word minimax value.

### 14.6 Scientific sources and applicability

| Scientific source | Mathematical role |
| --- | --- |
| [CommonPredictionWordCounts.lean](https://github.com/the-omega-institute/trureturing/blob/8e70a655ae3dc1965637bfc070169d7405526887/D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts.lean); [mathematical statement](https://github.com/the-omega-institute/trureturing/blob/8e70a655ae3dc1965637bfc070169d7405526887/Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts.md) | `TeacherLabels.actual_left_label`, `actual_right_label` and `MajorityGeometry.aLabel`, `bLabel` specify the priority tests; `Capacity.integer_split_positive` supplies the integer reservoir capacity for the full-word construction. |
| [CommonPredictionExteriorCapacity.lean](https://github.com/the-omega-institute/trureturing/blob/8e70a655ae3dc1965637bfc070169d7405526887/D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionExteriorCapacity.lean); [mathematical statement](https://github.com/the-omega-institute/trureturing/blob/8e70a655ae3dc1965637bfc070169d7405526887/Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionExteriorCapacity.md) | `CommonSelector.uniform_mass_balanced` supplies one deterministic pointwise majority classifier balancing all teachers in each rare-count class; the reservoir split concerns complete words. |
| [CommonPredictionSharpRisk.lean](https://github.com/the-omega-institute/trureturing/blob/8e70a655ae3dc1965637bfc070169d7405526887/D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionSharpRisk.lean); [mathematical statement](https://github.com/the-omega-institute/trureturing/blob/8e70a655ae3dc1965637bfc070169d7405526887/Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionSharpRisk.md) | `SharpRisk.lawMass`, `gappedRisk`, `T` and `sharp_risk_full` supply the independent product law and the simultaneous full-word attainment and lower bound, specialized here to \(n=4,q=1,r=2,v=3\). |
| [Static seams, transition circulation and Fibonacci toggle cycles](https://github.com/the-omega-institute/trureturing/blob/900686d5e22f6d576c37a7884d823260b6e251b1/docs/develop/theory/AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md) | §§1–2 and 4 distinguish five-state probability fibers, edge chains and complete future records. |
| [Signed factorial kernel and golden compatibility](https://github.com/the-omega-institute/trureturing/blob/900686d5e22f6d576c37a7884d823260b6e251b1/docs/develop/theory/AURIC_FIB_ATOM_SIGNED_FACTORIAL_KERNEL_AND_GOLDEN_COMPATIBILITY.md) | §§5–6 distinguish signed analytic responses and Gram-vector realizations from probability laws and acquisition operations. |
| [Symmetric seam, path defect and Fibonacci hierarchy](https://github.com/the-omega-institute/trureturing/blob/900686d5e22f6d576c37a7884d823260b6e251b1/docs/develop/theory/AURIC_FIB_ATOM_SYMMETRIC_SEAM_PATH_DEFECT_AND_FIBONACCI_HIERARCHY.md) | Q1–Q4, Q6–Q7 and Q10–Q14 specify carrier, feasible-difference, complete-record and physical-interpretation conditions. |
| [Observer-relative local models and future identifiability](https://github.com/the-omega-institute/trureturing/blob/900686d5e22f6d576c37a7884d823260b6e251b1/docs/develop/theory/AURIC_FIB_ATOM_OBSERVER_RELATIVE_LOCAL_MODELS_AND_FUTURE_IDENTIFIABILITY.md) | §§1–2, 5–8 and 11–12 supply the same-source, typed-operation and literal-factorization setting of this appendix. |
| [Local source splitting and readout geometry](https://github.com/the-omega-institute/trureturing/blob/900686d5e22f6d576c37a7884d823260b6e251b1/docs/develop/theory/AURIC_FIB_ATOM_LOCAL_SOURCE_SPLITTING_AND_READOUT_GEOMETRY.md) | §§1–3, 5 and 9–11 distinguish state laws, actual feasible fibers, readouts, complete records and source transport. |

The quotient \(Q\) supplies no acquisition operation or native read port. Its deterministic postprocessing presupposes the complete input and does not identify a state law with an edge flow, a signed/spectral or golden vector, or a paid stopped-observer carrier. Equal means, ranks or names, record packing, and randomized comparison supply no operation, clock, reset or resource bridge. Physical realization, calibration and resource accounting require their own source, operation and readout contracts. The finite certificate concerns only the specified two teachers and \(W^4\) law; it makes no assertion about unrestricted \(j_c\), \(155\), COMPLETE, all triples, all \(m\), all times, or the whole pyramid.

## 追加锚（本行以下为增补区）
