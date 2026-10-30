<a id="auric-v21"></a>

# 静态量子历史与内生观察者

**AURIC 三读出、基底递归与关系时钟**

**定义、定理与完整纸面证明**

**v21.0　2026 年 10 月 29 日（UTC）**

> **转换说明（编者）。** 本文完整转换作者的 v21.0 XeLaTeX 稿件，保留每节共享陈述编号、全局公式 (1)–(10)、全部证明、表格、引用与条件。源稿的项目快照、十九份定向源码审计、历史与研究推进报告均归属于作者，本次转换没有重新执行这些历史审计，也不作 Lean、数学数值、CAS、模拟、门搜索、硬件或原生托管 GitHub MathJax 认证。字体、分页、页眉和自动目录由 Markdown 排版与锚点替代，数学宏按 TeX 参数规则显式展开；正文未作实质数学修订。

> **公式排版说明（编者）。** 源稿编号 `align` 按原行拆为显示公式；五原子公式首行不编号、次行标 (2)，带权历史的三行依次标 (5)、不编号、(6)。矩阵内部换行、原有指数及未加花括号的宏参数均保留。

<a id="sec-abstract"></a>

## 摘要

本文把“固定整体量子态中的内生观察者”发展为一套有明确前件的关系模型。三个 AURIC 二值占位读出生成五原子的交换代数，其完整记录顺序无关；三个均值却仍遗忘一个联合概率方向和模式间相干。我们证明：基底本身可以由量子程序承载，三项读出引用同一程序时，即使程序保持相干，兼容性仍严格成立。相反，原生黄金门改变基底后，一对读出已出现精确顺序差 $\varphi^{-3}$。完整记录的等距递归可以嵌入静态直接极限；有限过程还可写成带权历史态，恰为传播残差的零最小元。时钟是可读记录之间的校准关系，门序列、历史权重和秒数不能互相替代。两路径共同端点的最小平方残差恰为干涉负端口概率的两倍，给出“递归相融、变分、可读谱”之间的具体等式。最后以未来效果闭包定义最小预测摘要，说明稳定三读出何时充分、何时必须保留隐藏关系和基底程序。全部结果保留 Hilbert 结构、Born 赋值、实际仪器与门接口；它们是一套一致的条件理论，未将五点图本身等同于完整量子公理的唯一来源。

<strong>结果身份。</strong>本文提供自足纸面证明与固定源码定位，不报告 Lean 验证、数学数值模拟、门枚举或硬件实现。直接极限、历史态、尖锐读出的兼容性及精确程序化限制均有既有来源；本轮的推进是其 AURIC 接口、内生基底构造、原生黄金数反例及路径残差与干涉的连接，不作这些经典原理的原创优先权声明。

## 目录

1. [最新项目快照、来源身份与本轮问题](#sec-1)
2. [三个稳定读出怎样生成五模式金字塔](#sec-2)
3. [投影次序无关的判据与黄金门反例](#sec-3)
4. [基底可以是观察者内部的量子程序](#sec-4)
5. [观察者增长、记录保留与静态直接极限](#sec-5)
6. [带权历史态：递归等价于一个明确的变分约束](#sec-6)
7. [本地时钟是记录关系，不是无参照的叠加速度](#sec-7)
8. [两条预测路径的变分误差就是一个干涉读数](#sec-8)
9. [观察者究竟必须记住多少：固定黄金菜单的六参数定理](#sec-9)
10. [预测、递归、变分与最优化：可以怎样严格等同](#sec-10)
11. [综合结论：一个可检验的静态观察者模型](#sec-11)

[文献与项目来源](#sec-bibliography)

<a id="sec-1"></a>

## 1. 最新项目快照、来源身份与本轮问题

研究分支为 `dev`，本轮固定不可变提交

`ce2773bd014df637336d2e89f83f220d8535c5be`。

提交时间为 2026-10-29 20:17:49 UTC，即 2026-10-30 04:17:49 UTC+08；合并 PR #23861，题为 <em>theory: classify the complete bipartite energy-game core for a>=5</em>。相对 v20 的 `837df9a7…`，比较接口报告 28 个提交、全仓 12 条变更路径；完整理论子树从 1019 增至 1021 个文件，有 2 新增、3 修改。固定链接见文献 [[1](#ref-snapshot)]。

五条理论变化分别涉及 CDSO 容量、环的 Fiedler 边界、$K_{3,m}$ 优化器、完全二部图能量博弈以及非二元 abelian-border 联合极限。这个区间没有直接修改 AURIC、观察者、局部时钟、测量或黄金门来源。本稿核对十九份定向源码与对应 Git blob；这是范围明确的源码审计，不是对全库证明的认证。

与本轮最相关的已有材料是：

1. 量子原则卷 [[2](#ref-qprinciples)] 的命题 3.4、定理 11.2、11.4：三种正交关系的区别、完整记录的静态直接极限、未来效果闭包。
2. 金字塔公式卷 [[3](#ref-pyramid)] 的五个事件幂等元，以及三均值下剩余的 $\kappa$ 纤维。
3. 三轴接口 [[4](#ref-threeaxis)] 关于几何坐标、Bloch 坐标与保留环境的区别；局部模型卷 [[5](#ref-localmodels)] 关于时钟校准与同步条件的限制。
4. v16、v18 的递归变分与静态切面结果 [[8](#ref-v16), [9](#ref-v18)]，以及前稿 v20 的固定黄金门与递归编译接口。

仓内 v16、v18 明确是前稿转录，不能作为独立验证。两份局部时钟汇编 [[6](#ref-clockvolume), [7](#ref-clockkernel)] 也注明混合用户材料的来源身份；其编辑限定优先于源稿。本文引用其中具体命题，不把收入仓库解释为物理实证。

<a id="statement-1-1"></a>

#### 定义 1.1（本文的条件理论）

取复 Hilbert 空间、正内积、线性等距操作、给定因子分解与 Born 读出规则。除另行讨论的极限与理想计数时钟外，各有限层使用有限维载体和有限输出仪器。观察者的完整载体包含系统 $S$、程序或参考框 $B$、记录 $R$、时钟 $C$，以及仍会影响未来的环境 $E$。门与仪器须来自明确声明的合法菜单。下标 $n,t$ 默认表示逻辑切面或记录地址，不预设外部物理秒数。

这些前件明确回答“在哪个理论内证明”。静态有向图也可承载经典随机模型，裸五标签不唯一决定复标量、张量复合或 Born 平方。接下来的目标是证明用户图景中的哪些联系在上述前件下成立，并给出不能同时成立的精确条件。

<a id="sec-2"></a>

## 2. 三个稳定读出怎样生成五模式金字塔

<a id="statement-2-1"></a>

<a id="def-modes"></a>

#### 定义 2.1（模式与占位读口）

令

$$
\Sigma=(0,1,2,3,13)\ \longleftrightarrow\
(000,100,010,001,101),\qquad H_5=\mathbb C ^\Sigma,
\qquad \Pi_s=\lvert s\rangle \langle s\rvert .
$$

定义三个二值尖锐读出

<a id="eq-N"></a>

$$
N_1=\Pi_1+\Pi_{13},\qquad N_2=\Pi_2,\qquad
N_3=\Pi_3+\Pi_{13}.
\tag{1}
$$

原项目的坐标记号为 $N_x=N_1,N_y=N_3,N_z=N_2$。数值标签 $(0,2,3,5,25)$ 与这里的逻辑标签 $(0,1,2,3,13)$ 对应。

<a id="statement-2-2"></a>

<a id="thm-five"></a>

#### 定理 2.2（五原子交换代数）

设三个对易自伴投影 $x,y,z$ 满足 $xy=yz=0$。它们生成的含单位交换代数由

$$
I,\ x,\ y,\ z,\ xz
$$

张成，维数至多为五。其可能非零的联合原子为

$$
\begin{aligned}
E_0&=I-x-y-z+xz,&E_1&=x-xz,&E_2&=y,
\end{aligned}
$$

<a id="eq-atoms"></a>

$$
\begin{aligned}
E_3&=z-xz,&E_{13}&=xz.&&
\end{aligned}
\tag{2}
$$

若五者均非零，该代数同构于 $\mathbb C ^5$。在定义 [2.1](#def-modes) 的最小五维表示中，$x=N_1,y=N_2,z=N_3$，且 $E_s=\Pi_s$，均为秩一。

**证明。**

对易投影的联合本征值取值于 $\{0,1\}^3$。关系 $xy=yz=0$ 排除同时出现第一、第二位或第二、第三位为一，剩下恰为

$$
000,\quad100,\quad010,\quad001,\quad101.
$$

每个联合谱原子由三个投影及其补投影的乘积给出；利用两条排斥关系化简，即得式 [(2)](#eq-atoms)。它们两两正交、和为 $I$。任意多项式在这至多五个联合谱点上仅取五个值，等于相应 $E_s$ 的线性组合。五个非零正交投影线性无关，所以五者均出现时维数为五，同构由五点上的函数值给出。最小表示中的本征值表直接给出 $E_s=\Pi_s$。

∎

这里的“原子”首先是生成代数内的最小非零投影；在较大表示里可以具有重数，不能从抽象五原子自动推出载体只有五维。本文选用 $H_5$ 才固定其秩为一。

| 模式 | $N_1$ | $N_2$ | $N_3$ | $(N_x,N_y,N_z)$ |
| --- | --- | --- | --- | --- |
| $0$ | 0 | 0 | 0 | $(0,0,0)$ |
| $1$ | 1 | 0 | 0 | $(1,0,0)$ |
| $2$ | 0 | 1 | 0 | $(0,0,1)$ |
| $3$ | 0 | 0 | 1 | $(0,1,0)$ |
| $13$ | 1 | 0 | 1 | $(1,1,0)$ |

这五个经典响应向量的凸包正是一个方底金字塔。这里的三维是读出坐标空间的维数，尚未等同于物理空间维数。并且

$$
[N_i,N_j]=0,\qquad N_1N_2=N_2N_3=0,\qquad
N_1N_3=\Pi_{13}\ne0.
$$

所以三个读口兼容，却不是三个互斥的秩一基态投影。

<a id="statement-2-3"></a>

<a id="prop-kappa"></a>

#### 命题 2.3（三均值与完整联合记录）

设 $\rho$ 为 $H_5$ 上的密度矩阵，记

$$
X=\operatorname{Tr} (\rho N_1),\quad Y=\operatorname{Tr} (\rho N_3),\quad
Z=\operatorname{Tr} (\rho N_2),\quad R=1-Z.
$$

具有这些均值的全部对角概率分布恰为

<a id="eq-fiber"></a>

$$
p_\kappa=(R-X-Y+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
\tag{3}
$$

其中

$$
\max(0,X+Y-R)\le\kappa\le\min(X,Y),\qquad
\kappa=\operatorname{Tr} (\rho N_1N_3).
$$

完整三位联合记录在一次试验中识别本次模式；完整联合概率律确定五个人口 $p_s$。这两者均不能解释成三个均值已确定完整量子态。

**证明。**

从 $X=p_1+p_{13},Y=p_3+p_{13},Z=p_2$ 以及 $\sum_sp_s=1$ 解出式 [(3)](#eq-fiber)。五项非负恰给所列区间。表中的五个响应向量互不相同，故完整样本识别其模式，完整联合律识别所有 $p_s$；任何对角测量都不读取 $\rho_{st}$（$s\ne t$），所以模式间相干仍未确定。

∎

“三个分量”还可能表示另外两件事。第一，三维向量的正交分解 $\psi=P_1\psi+P_2\psi+P_3\psi$，其中 $P_iP_j=0$，其坐标没有先算谁的问题；但对同一标本连续要求不同两个肯定投影，会得到零。第二，量子比特的三个 Bloch 坐标来自 Pauli 算符：它们在算符内积下正交，却不对易，不能据此获得同时尖锐读出。三种类型应在建模时明确选择，不能互换。

<a id="sec-3"></a>

## 3. 投影次序无关的判据与黄金门反例

<a id="statement-3-1"></a>

#### 定义 3.1（指定 Lüders 仪器）

对于正交投影 $P$，二值读出的分支映射为

$$
\rho\longmapsto P\rho P,\qquad
\rho\longmapsto(I-P)\rho(I-P).
$$

分支迹是概率，非零分支除以其迹得到条件态。讨论次序时保留操作及结果标签，不能只比较丢掉记录后的平均通道。

<a id="statement-3-2"></a>

<a id="thm-order"></a>

#### 定理 3.2（全输入顺序无关当且仅当对易）

对正交投影 $P,Q$，下列四条等价：

1. 对所有输入，两次肯定的联合概率与先后次序无关；
2. $PQP=QPQ$；
3. $[P,Q]=0$；
4. 两个 Lüders 读出的全部带标签分支映射与次序无关。

有限多个这种读出的任意排列都给相同完整记录律，当且仅当它们两两对易。

**证明。**

两种次序的肯定概率分别为 $\operatorname{Tr} (\rho PQP)$ 与 $\operatorname{Tr} (\rho QPQ)$。所有密度态上的期望相同等价于自伴算符相同，故前两条等价。设 $C=PQP=QPQ$，则

$$
0=(I-P)C(I-P)
=(I-P)QPQ(I-P)
=[PQ(I-P)]^\dagger[PQ(I-P)].
$$

于是 $PQ(I-P)=0$，即 $PQ=PQP$；取伴随得 $QP=PQP$，从而对易。对易也立即推出第二条。写 $P_1=P,P_0=I-P$ 以及 $Q_1=Q,Q_0=I-Q$，对易使

$$
Q_bP_a\rho P_aQ_b=P_aQ_b\rho Q_bP_a
$$

对每个分支成立，完成四者等价。多读出时两两对易保证任意排列相同；反之将任意一对置于最前，对后续全部结果求和，即退化到两读出的结论。

∎

该结论的尖锐兼容性背景见 [[12](#ref-joint)]。若只固定 PVM，却允许各结果之后附加任意条件酉，便没有指定本定理的仪器；顺序无关不再自动成立。

<a id="statement-3-3"></a>

<a id="cor-copy"></a>

#### 推论 3.3（一个 AURIC 原子内的记录无先后）

给三个独立指针比特，定义

$$
C_i=(I-N_i)\otimes I_{R_i}+N_i\otimes X_{R_i},
$$

在其余指针因子上补单位。则 $C_i$ 为两两对易的酉算子。指针从 $\lvert 000\rangle$ 出发，任意次序给同一个等距记录

$$
V\lvert s\rangle =\lvert s\rangle \lvert n_1(s)n_2(s)n_3(s)\rangle .
$$

**证明。**

每个 $C_i$ 在两个正交系统扇区上分别作用为 $I$ 与 $X$，故酉。不同指针上的 $X$ 对易，系统控制 $N_i$ 也对易，所以所有乘积可换序。对五个模式逐一作用即得等距式。

∎

平均通道可掩盖顺序。例如单比特 $X,Z$ 去相干通道的两种复合都给 $I/2$，但输入 $\lvert 0\rangle$ 时，先 $Z+$ 后 $X+$ 的概率为 $1/2$，反序为 $1/4$。因而完整记录是本判据的必要接口。

<a id="statement-3-4"></a>

<a id="prop-gold"></a>

#### 命题 3.4（原生黄金门的精确跨基底顺序差）

令 $\varphi=(1+\sqrt5)/2$、$\omega=e^{3\pi i/5}$。项目原生门写为

$$
K=\omega[I+(\omega-1)\mathcal P],\qquad \mathcal P^2=\mathcal P=\mathcal P^\dagger.
$$

在活动扇区 $(000,010)$ 中，

$$
\mathcal P|_{\mathrm{act}}=
\begin{pmatrix}\varphi^{-1}&\varphi^{-3/2}\\
\varphi^{-3/2}&\varphi^{-2}\end{pmatrix}.
$$

其余模式 $100,001$ 上 $\mathcal P=0$，模式 $101$ 上 $\mathcal P=1$。令

$$
P=N_2=\lvert 010\rangle \langle 010\rvert ,\qquad Q=K^\dagger P K.
$$

则

<a id="eq-goldoverlap"></a>

$$
\lambda:=\operatorname{Tr} (PQ)=\varphi^{-2},\qquad
\left\lVert [P,Q]\right\rVert =\varphi^{-3/2}>0.
\tag{4}
$$

对输入 $\lvert 010\rangle$，两次肯定的概率为

$$
p_{P\to Q}=\varphi^{-2},\qquad
p_{Q\to P}=\varphi^{-4},\qquad
\boxed{p_{P\to Q}-p_{Q\to P}=\varphi^{-3}}.
$$

**证明。**

活动块迹为一、行列式为零且自伴正定于其像，故确为秩一投影。设 $a=\varphi^{-2}$。由 $|\omega-1|^2=\varphi^2$ 与 $1-a=\varphi^{-1}$，

$$
\lambda=|1+(\omega-1)a|^2
=1-\varphi^2a(1-a)=1-\varphi^{-1}=\varphi^{-2}.
$$

两个秩一投影交叠 $\lambda$ 时，在其支撑平面中取合适相位，可以写为

$$
P=\begin{pmatrix}1&0\\0&0\end{pmatrix},\quad
Q=\begin{pmatrix}\lambda&\sqrt{\lambda(1-\lambda)}\\
\sqrt{\lambda(1-\lambda)}&1-\lambda\end{pmatrix}.
$$

直接相乘得交换子范数为 $\sqrt{\lambda(1-\lambda)}=\varphi^{-3/2}$，并有 $PQP=\lambda P,Q PQ=\lambda Q$。在 $P$ 的单位本征向量上取期望，分别给 $\lambda,\lambda^2$，其差 $\lambda(1-\lambda)=\varphi^{-3}$。

∎

这里计算的是 $Q$ 的指定 Lüders 仪器。其原生实现须先执行 $K$，读取 $P$ 的二值结果，再对两个结果分支都执行返回门 $K^\dagger=K^9$。肯定分支的 Kraus 算子于是为 $K^\dagger P K=Q$，否定分支为 $I-Q$。只做 $K$ 后测 $P$ 而不返回，虽有相同效果 $Q$，却是不同后态的仪器；不能套用本命题的顺序概率。原生门已提供真实的非交换关系，因此“同一原子的三读口无先后”不推出“所有不同基底读出都无先后”。

<a id="sec-4"></a>

## 4. 基底可以是观察者内部的量子程序

<a id="statement-4-1"></a>

#### 定义 4.1（共同的基底程序）

设 $B$ 有正交程序标签 $\lvert b\rangle$，每个标签指定一个已知酉矩阵 $U_b\in\operatorname{U} (H_5)$，定义

$$
W=\sum_b\lvert b\rangle \langle b\rvert \otimes U_b,\qquad
\widetilde N_i=W(I_B\otimes N_i)W^\dagger.
$$

一次完整原子内使用同一个 $B$、同一个 $W$，不在三个读口之间另行改写或重新抽取程序。测量本身仍可使程序与指针相关；这里要求固定的是共同读出算符，并非程序的约化态必须完全不变。

<a id="statement-4-2"></a>

<a id="thm-program"></a>

#### 定理 4.2（内生共同基底保持严格兼容）

无论 $B$ 处于确定标签、相干叠加，还是与数据已纠缠，都有

$$
[\widetilde N_i,\widetilde N_j]=0.
$$

因此三个指定 Lüders 读出的全部记录与排列无关。令

$$
E_s=W(I_B\otimes\Pi_s)W^\dagger,\qquad
V_{\mathrm{read}}=\sum_s E_s\otimes\lvert s\rangle _R,
$$

则 $V_{\mathrm{read}}^\dagger V_{\mathrm{read}}=I$。若前一层预测以等距映射 $T$ 生成程序与数据，$V_{\mathrm{read}}T$ 仍是等距映射。

**证明。**

共同酉共轭保持乘法，故

$$
[\widetilde N_i,\widetilde N_j]
=W(I_B\otimes[N_i,N_j])W^\dagger=0.
$$

定理 [3.2](#thm-order) 不依赖输入态，故也适用于纠缠输入。$\{E_s\}$ 是完备正交投影族，因而
$V_{\mathrm{read}}^\dagger V_{\mathrm{read}}=\sum_sE_s^\dagger E_s=I$。
再乘以 $T^\dagger,T$ 即得复合映射的等距性。

∎

这是“预测产生基底，基底成为下一层门控制”的直接实现。操作上可以先用 $W^\dagger$ 转到共同参考模式，复制该模式，再用 $W$ 转回。这里给定已知 $U_b$ 及共同受控实现；没有假定任意未知黑箱酉都可免费加控制，也没有把归一化后验更新当作无条件的非线性量子门。

<a id="statement-4-3"></a>

<a id="cor-approx"></a>

#### 推论 4.3（共同近似基底与独立近似基底）

任何共同酉 $V$，即使只近似理想 $U$，都使 $\{VN_iV^\dagger\}$ 精确对易。若各读口独立使用 $V_i$，则只保证

$$
\left\lVert [V_iN_iV_i^\dagger,V_jN_jV_j^\dagger]\right\rVert 
\le4\left\lVert V_i-V_j\right\rVert .
$$

**证明。**

第一条直接用共同共轭。第二条中 $V_iN_iV_i^\dagger$ 与 $V_iN_jV_i^\dagger$ 对易；减去后者后，使用
$\left\lVert [A,D]\right\rVert \le2\left\lVert A\right\rVert \left\lVert D\right\rVert$ 及
$\left\lVert V_jN_jV_j^\dagger-V_iN_jV_i^\dagger\right\rVert \le2\left\lVert V_i-V_j\right\rVert$ 即得。

∎

所以有限精度不必破坏原子内部的相容性；共享参考框比把三个基底分别逼近更能保留代数关系。前稿 v20 在指定编码上给出的黄金字编译可服务于这类已知操作，但其单比特稠密性不能直接替换成“任意五维 $U_b$ 均已由单原子精确实现”。

<a id="statement-4-4"></a>

<a id="prop-povm"></a>

#### 命题 4.4（忽略基底程序后的读出）

若输入为 $\sigma_B\otimes\rho$，记 $p_b=\langle b\rvert \sigma_B\lvert b\rangle$，忽略 $B$ 后联合模式读出的数据效果为

$$
F_s=\sum_b p_b U_b\Pi_sU_b^\dagger,\qquad
F_s\ge0,\qquad \sum_sF_s=I.
$$

三个占位边缘是该联合 POVM 的粗粒化，所以兼容；它们不必仍为尖锐投影，也不必两两对易。

**证明。**

对 $\sigma_B\otimes\rho$ 与 $E_s$ 取迹，程序扇区的正交性消去 $b\ne c$ 项，给 $\operatorname{Tr} (\rho F_s)$。正性和完备性逐项保持。三个边缘分别按位值求和，因此来自同一联合读出。

∎

若程序和数据起初相关，通常不能只由 $\rho_S$ 定义一套与来源无关的固定 $F_s$，应保留联合态。即使程序经典随机，共享和重新抽取也不同：最大混合比特以各半概率选 $Z$ 或 $X$ 基，连续两次肯定，复用同一基底的概率为 $1/2$，每次独立重抽则为 $3/8$。后者在相同基底的总概率 $1/2$ 下贡献 $1/2$，不同基底的总概率 $1/2$ 下贡献 $1/4$，即 $(1/2)(1/2)+(1/2)(1/4)$。单步边缘相同不足以替代完整程序来源。

<a id="statement-4-5"></a>

<a id="prop-monomial"></a>

#### 命题 4.5（两套完整尖锐基底何时共同兼容）

设 $U,V\in\operatorname{U} (5)$，考虑两套秩一 PVM：

$$
P_s=U\Pi_sU^\dagger,\qquad Q_t=V\Pi_tV^\dagger.
$$

所有交叉投影 $P_s,Q_t$ 对易，当且仅当 $U^\dagger V$ 是带相位的置换矩阵。

**证明。**

两个秩一投影若对易，其像要么相同，要么正交：对易使一个一维像在另一投影下不变，其限制只能为零或一。固定第二套任一基向量，其与第一套所有投影相容，完备性迫使它等于第一套某基向量的相位倍。正交性使这些对应形成置换。反向的相位与置换显然给同一族投影。

∎

<a id="statement-4-6"></a>

<a id="thm-noprogram"></a>

#### 定理 4.6（不同精确尖锐程序必须正交）

固定同一个处理器、指针测量和结果标签，不允许程序依赖的免费后处理。若纯程序 $\lvert p\rangle ,\lvert q\rangle$ 精确、确定性地实现两套不同 PVM $\{P_i\},\{Q_i\}$，则 $\langle p|q\rangle=0$。因此 $d_B$ 维纯程序空间最多容纳 $d_B$ 套这样的不同精确 PVM。

**证明。**

取处理器的共同等距扩张。对 $x\in\operatorname{ran}P_i$ 与 $y\in\operatorname{ran}Q_j$、$i\ne j$，指针结果不同且确定，输出相互正交，故保内积性给
$0=\langle p|q\rangle\langle x|y\rangle$。若程序内积非零，则 $P_iQ_j=0$ 对全部 $i\ne j$ 成立。由两套投影的完备性，

$$
P_i=P_i\sum_jQ_j=P_iQ_i,\qquad
Q_i=\sum_jP_jQ_i=P_iQ_i,
$$

故 $P_i=Q_i$，与不同矛盾。维数界由非零正交向量数给出。

∎

这是既有精确可观测量程序化定理的有限维证明 [[13](#ref-program)]。它允许有限菜单、近似编译和随精度增长的程序资源，也说明“基底还在预测”必须有承载其差异的资源，不能把连续所有精确基底压进一个有限程序而保持上述全部条件。

<a id="sec-5"></a>

## 5. 观察者增长、记录保留与静态直接极限

<a id="statement-5-1"></a>

<a id="def-observer"></a>

#### 定义 5.1（内生的预测与记录原子）

在记录历史 $h$ 下，观察者利用已经保留的信息选择合法仪器
$\{M_{a|h}\}_a$，其中 $\sum_aM_{a|h}^\dagger M_{a|h}=I$。
程序的生成、共同基底的读取和反馈控制均可包含在该仪器的完整扩张中。观察者不是无载体的门名字串，而是承载程序、记录与仍相关环境的一组接口及其递归约束。

<a id="statement-5-2"></a>

<a id="thm-tree"></a>

#### 定理 5.2（完整记录的等距递归）

令不同历史标签正交，定义

$$
T_t(\lvert h\rangle \otimes\psi)
=\sum_a\lvert ha\rangle \otimes M_{a|h}\psi .
$$

则 $T_t^\dagger T_t=I$。从空记录及单位输入 $\psi$ 出发，深度 $t$ 的完整状态为

$$
\Phi_t=\sum_{h=a_1\cdots a_t}\lvert h\rangle \otimes M_h\psi,\qquad
M_h=M_{a_t|a_1\cdots a_{t-1}}\cdots M_{a_1|\varnothing},
$$

并且 $\left\lVert \Phi_t\right\rVert =1$。记录概率为 $\left\lVert M_h\psi\right\rVert ^2$；非零记录的条件态为 $M_h\psi/\left\lVert M_h\psi\right\rVert$。

**证明。**

不同父历史 $h,k$ 的全部延伸标签互相正交。同一父历史内，

$$
\langle T_t(h\otimes\phi),T_t(h\otimes\psi)\rangle
=\sum_a\langle\phi,M_{a|h}^\dagger M_{a|h}\psi\rangle
=\langle\phi,\psi\rangle .
$$

所以映射等距。反复代入得到有序积与单位范数；记录分支的范数平方和归一化给最后两式。

∎

每个有限深度的此类等距过程都能在预备空白辅助寄存器、保留全部输出的较大空间中延拓为酉网络：将等距像的正交基补为全空间正交基即可。增长等距自身若非满射，不能直接称为同一空间上的酉算子。其条件分支的归一化则是非线性的描述更新，不能用它替代完整等距。

<a id="statement-5-3"></a>

#### 推论 5.3（可区分记录的容量）

若完整保留 $N$ 条精确可区分历史，记录空间维数至少为 $N$，二能级记录载体至少需 $\lceil\log_2N\rceil$ 个。

**证明。**

完全可区分的纯记录必须两两正交，故其数量不超过空间维数。

∎

这给“预测成为自身增长”一个可核对的含义：未来所需的程序或记录自由度增加。它不保证每一步都获得新信息，也没有在未给热学模型时推导能耗或熵的单调增加。

<a id="statement-5-4"></a>

<a id="thm-nodisturb"></a>

#### 定理 5.4（全态不扰动的精确限制）

若等距 $V:H\to H\otimes E$ 满足

$$
\operatorname{Tr} _E(V\rho V^\dagger)=\rho
$$

对每个输入密度态都成立，则存在与输入无关的单位向量 $e$，使 $V\psi=\psi\otimes e$。环境不能获得任何关于输入的可区分信息。

**证明。**

基态 $\lvert j\rangle$ 的系统输出仍纯，故 $V\lvert j\rangle =\lvert j\rangle \lvert e_j\rangle$。对 $(\lvert j\rangle +\lvert k\rangle )/\sqrt2$，系统非对角元保持原值要求
$\langle e_k|e_j\rangle=1$。单位向量的此内积迫使 $e_j=e_k$。由线性性得到所有输入上的结论。

∎

这是信息扰动关系的精确零扰动情形 [[14](#ref-disturb)]。推论 [3.3](#cor-copy) 的模式复制允许得到信息，是因为它只保持五个模式的经典人口。对一般 $\rho$ 忽略指针后得到

$$
\Delta(\rho)=\sum_s\Pi_s\rho\Pi_s,
$$

其模式相干可以变化。保留所有指针则仍有完整等距信息。固定总历史作为一种描述，与对未知输入实际施加测量耦合时保持完整输入态，是两个不同的命题。

<a id="statement-5-5"></a>

<a id="thm-limit"></a>

#### 定理 5.5（完整递归的静态直接极限）

给 Hilbert 空间链及等距 $T_n:H_n\to H_{n+1}$，存在 Hilbert 空间 $H_\infty$ 和等距嵌入 $\iota_n$，使

$$
\iota_{n+1}T_n=\iota_n,\qquad
\overline{\bigcup_n\iota_nH_n}=H_\infty.
$$

它在保持嵌入的酉同构意义下唯一。若 $\psi_{n+1}=T_n\psi_n$，则所有 $\iota_n\psi_n$ 是同一向量 $\Psi$。

**证明。**

把 $(n,\psi)$ 与 $(m,\phi)$ 在某个共同后继中像相同的代表等同。任意两个代表都可推进到共同后继，并在那里定义线性组合与内积。等距性保证不依赖后继或代表，得到内积空间；取其完成即为 $H_\infty$。自然嵌入满足所列关系且代数并稠密。任意另一实现上的对应在此稠密并中保内积，延拓后为唯一满射酉。对递归态应用嵌入关系即得最后一条。

∎

这是项目已有定理 11.2 的自足重述 [[2](#ref-qprinciples)]。它精确容纳“整体表示固定而内部记录增长”，但仍需说明观测算符如何进入极限。

<a id="statement-5-6"></a>

<a id="prop-effectlimit"></a>

#### 命题 5.6（固定态、固定效果与不同切面）

设各切面效果满足 $0\le E_n\le I$。存在固定极限效果 $0\le E_\infty\le I$，其压缩满足
$E_n=\iota_n^\dagger E_\infty\iota_n$，当且仅当

$$
E_n=T_n^\dagger E_{n+1}T_n .
$$

这种 $E_\infty$ 唯一；沿同一递归态，

$$
\langle\psi_n,E_n\psi_n\rangle
=\langle\Psi,E_\infty\Psi\rangle
$$

严格恒定。

**证明。**

必要性来自嵌入关系。充分性时，将两向量推到共同后继，用该层 $E_n$ 定义半正定有界 sesquilinear 形式；压缩相容保证独立于所选层。$0\le E_n\le I$ 给统一界，因此形式在完成空间上定义唯一效果 $E_\infty$。最后一式由压缩恒等式立即得到。

∎

所以局部经验的变化必须由不同的切面效果、不同记录条件或不同相对参照来表达；不能同时固定 $\Psi$、固定同一个 $E_\infty$，却令其期望自行变化。这一限定使静态说法成为可计算的理论，而不只是更换叙述词汇。

<a id="sec-6"></a>

## 6. 带权历史态：递归等价于一个明确的变分约束

内部时钟条件化的标准背景可追溯到 Page–Wootters [[10](#ref-pw)]；门历史及传播 Hamiltonian 是历史态方法的基本构造 [[11](#ref-history)]。v16 已使用均匀版本。这里保留任意正权重，并把哪些东西随权重改变写清。

<a id="statement-6-1"></a>

<a id="thm-history"></a>

#### 定理 6.1（带权静态历史与零残差）

在同一有限维完整载体 $H$ 上给酉门 $G_1,\ldots,G_T$，记
$U_0=I,\ U_t=G_t\cdots G_1$。选择 $\pi_t>0$、$\sum_{t=0}^T\pi_t=1$。定义

<a id="eq-hist"></a>

$$
\begin{aligned}
J_\pi\psi&=\sum_{t=0}^T\sqrt{\pi_t}\lvert t\rangle \otimes U_t\psi,
\end{aligned}
\tag{5}
$$

$$
\begin{aligned}
D_t&=\pi_t^{-1/2}\langle t\rvert \otimes I
-\pi_{t-1}^{-1/2}\langle t-1\rvert \otimes G_t,
\end{aligned}
$$

<a id="eq-hprop"></a>

$$
\begin{aligned}
H_\pi&=\sum_{t=1}^T a_tD_t^\dagger D_t,\qquad a_t>0.
\end{aligned}
\tag{6}
$$

则 $J_\pi^\dagger J_\pi=I$，$H_\pi\ge0$，且

$$
\ker H_\pi=\operatorname{im}J_\pi .
$$

固定单位 $\psi$ 后，$\Omega_\psi=J_\pi\psi$ 的时钟概率为 $\pi_t$，条件数据态为 $U_t\psi$。任意 $\Xi=\sum_t\lvert t\rangle x_t$ 的残差为

<a id="eq-action"></a>

$$
\langle\Xi,H_\pi\Xi\rangle
=\sum_{t=1}^T a_t
\left\lVert \frac{x_t}{\sqrt{\pi_t}}
-G_t\frac{x_{t-1}}{\sqrt{\pi_{t-1}}}\right\rVert ^2 .
\tag{7}
$$

**证明。**

正交时钟使 $J_\pi^\dagger J_\pi=\sum_t\pi_tU_t^\dagger U_t=I$。式 [(7)](#eq-action) 是 [(6)](#eq-hprop) 的平方和展开。正系数使其为零恰等价于每个 $D_t\Xi=0$。令 $y_t=x_t/\sqrt{\pi_t}$，则 $y_t=G_ty_{t-1}=U_ty_0$，故 $\Xi=J_\pi y_0$；反向代入同样成立。时钟投影得到未归一化数据向量 $\sqrt{\pi_t}U_t\psi$，给出概率与条件态。

∎

因此，固定门、权重与边界之后，

$$
\boxed{\text{递归相容解}\ =\ \text{传播残差的零最小元}\ =\ \text{满足该边界的静态历史}.}
$$

加上 $H_{\rm in}=\lvert 0\rangle \langle 0\rvert \otimes(I-\lvert \psi_0\rangle \langle \psi_0\rvert )$，归一化零能态在整体相位之外唯一；若直接固定 $y_0=\psi_0$，向量也唯一。没有固定非零边界时，零向量总是残差零点，不能用它证明非平凡预测已成功。

更换 $\pi$ 同时更换 $D_t,H_\pi$。不能说同一个已经固定的传播 Hamiltonian 任意容纳所有权重。虽然
$e^{-isH_\pi}\Omega_\psi=\Omega_\psi$，这里的 $H_\pi$ 是为相容关系构造的算子；该事实没有认定它就是宇宙真实 Hamiltonian，也没有证明这些历史态能由某个固定门菜单免费精确制备。

把定理 [5.2](#thm-tree) 的有限记录网络作酉扩张后，即可用本定理编码。若 $P_t$ 是时钟投影、$Q_h$ 是另一个因子上的记录投影，则二者对易。在非零共同事件上，先按时钟后按记录或反序条件化都给

$$
\rho_{t,h}=
\frac{P_tQ_h\rho Q_hP_t}{\operatorname{Tr} (P_tQ_h\rho)}.
$$

使用同一 $\rho$ 计算所有条件描述，不要求实际条件态等于原始 $\rho$。这一点与三读口的次序无关一样，都来自明确的兼容代数。

<a id="statement-6-2"></a>

<a id="prop-infinite"></a>

#### 命题 6.2（全部门历史的叠加需要权重）

给正交历史标签 $\lvert w\rangle$ 与单位历史向量 $\Psi_w$，则

$$
\Omega=\sum_w c_w\lvert w\rangle \otimes\Psi_w
$$

是通常 Hilbert 空间中的单位向量，当且仅当 $\sum_w|c_w|^2=1$。无限非零等权和不能归一化。均匀有限时钟历史

$$
\Omega_T=\frac1{\sqrt{T+1}}\sum_{t=0}^T\lvert t\rangle \otimes\psi_t,\qquad \left\lVert \psi_t\right\rVert =1,
$$

在该共同空间中也没有向量范数极限。

**证明。**

标签正交使部分和的范数平方为系数平方和，Cauchy 条件恰为平方可和。对 $S\ge T$，
$\langle\Omega_T,\Omega_S\rangle=\sqrt{(T+1)/(S+1)}$。取 $S+1=4(T+1)$，两单位向量距离恒为一，故不是 Cauchy 序列。

∎

因此可以谈加权门历史、有限窗口，或满足一致性条件的局部代数态极限；这些是不同的精确定义。若丢弃正交程序标签，数据通常成为混合；若希望不同历史相干干涉，还须保留并重组路径参考。单独说“全部序列的叠加”尚未选定其中一种对象。

<a id="sec-7"></a>

## 7. 本地时钟是记录关系，不是无参照的叠加速度

<a id="statement-7-1"></a>

#### 定义 7.1（关系时钟）

在同一整体态上给两个可读时钟 $C,D$。其联合律
$p(n,m)$ 及条件律 $p(m|n)$ 描述两个内部读数的关系。赋予读数已校准实值 $x_n,y_m$ 后，非零读数差之间的比率才定义相对钟速率。单独的门名字串、幅度权重或整数标签不自带秒的单位。

<a id="statement-7-2"></a>

<a id="thm-coarseclock"></a>

#### 定理 7.2（粗时钟下的条件混合）

设 $\psi_t=U_t\psi$ 为单位向量，$f$ 给另一时钟的读数地址，取

$$
\Omega_f=\sum_t\sqrt{\pi_t}\lvert t\rangle _C\lvert f(t)\rangle _D\psi_t .
$$

则 $p(t,s)=\pi_t\mathbf1_{\{f(t)=s\}}$。若 $q_s=\sum_{f(t)=s}\pi_t>0$，仅按 $D=s$ 条件化并忽略细时钟 $C$ 后，

$$
\rho_{S|s}=\frac1{q_s}\sum_{f(t)=s}\pi_t\lvert \psi_t\rangle \langle \psi_t\rvert .
$$

该态纯，当且仅当这条纤维上的全部 $\psi_t$ 共线。

**证明。**

两时钟投影给联合律。按 $D=s$ 条件化后，对 $C$ 取偏迹消去不同 $t$ 的交叉项，即得凸组合。纯态支持为一维；正权重和的支持包含每一项的支持，所以和纯恰要求全部分量支持于同一直线。反向显然。

∎

因此同一个整体纯态可以给粗时钟下的混合经验。若 $f$ 单射，两个时钟只是对同一细历史的不同标签。选择读数刻度后，可定义

$$
v_t=\frac{x_{t+1}-x_t}{y_{f(t+1)}-y_{f(t)}} ,
$$

前提是分母非零。改变单位会改变数值比率，重新校准后才可比较。$\pi_t$ 本身只是历史态的时钟 Born 权重；将它解释成驻留时间比，还需采样或流量模型。本地模型卷已经明确要求独立的时间标定 [[5](#ref-localmodels)]。

<a id="statement-7-3"></a>

<a id="prop-tick"></a>

#### 命题 7.3（数据周期与实际计数时钟不同）

原生门满足 $K^{10}=I$。令双向计数时钟上的酉移位为
$S\lvert n\rangle =\lvert n+1\rangle$，$n\in\mathbb Z$，定义一次带记录的门
$\widetilde K=S\otimes K$。则

$$
\boxed{\widetilde K^{10}=S^{10}\otimes I\ne I.}
$$

有限循环时钟维数 $N>10$ 时，十步结论也成立。

**证明。**

$\mathcal P$ 的零、一两个扇区上 $K$ 的本征值分别为 $\omega,\omega^2$；因 $\omega^{10}=1$，故 $K^{10}=I$。双向移位把正交基双射到自身，故酉。不同因子相乘给
$(S\otimes K)^{10}=S^{10}\otimes K^{10}$，而 $\lvert n+10\rangle \ne\lvert n\rangle$。循环时钟中 $10\not\equiv0\pmod N$，同样不为单位。

∎

对只读数据边界的任务，插入 $K^{10}$ 不改变边界通道；每次门实际留下计数时，十次插入却产生不同观察者记录。纯粹增加无可读记录的数学切面又是第三种情形。数据变换、事件计数和物理单位必须分别指定。

<a id="statement-7-4"></a>

<a id="prop-clockpotential"></a>

#### 命题 7.4（全局钟势的图判据）

给底层连通图的有向边增量 $a_e\in\mathbb R$。存在顶点钟势 $\tau$ 满足
$\tau(v)-\tau(u)=a_e$ 对每条 $e:u\to v$ 成立，当且仅当每个底层有符号闭走的增量和为零。钟势若存在，在加常数之外唯一。图为 DAG 本身不足以保证该条件。

**证明。**

钟势差沿闭走求和必望远镜消去。反之固定根 $r$ 的钟值，对任意 $v$ 沿一条底层路径加增量，反向经过边时取负号。两个路径之差是闭走，零和保证定义无关路径并满足所有边差。两个解之差在每条边上恒定，连通性给全局常数。一个菱形 DAG 的两条根到顶点路径若总增量不同，即不满足条件。

∎

该修正正是项目时钟卷的优先限定 Q2 [[6](#ref-clockvolume)]。不要求外部绝对时间，仍然需要内部同步的相容条件。图无有向循环、几何路径长度为正以及每步有记录，均不能单独替代此条件。

<a id="sec-8"></a>

## 8. 两条预测路径的变分误差就是一个干涉读数

<a id="statement-8-1"></a>

#### 定义 8.1（共同端点完成问题）

给从同一输入接口到同一候选输出接口的酉路径 $A,B$ 及单位输入 $\psi$。把共同端点作为变量 $z$，定义

$$
E_\psi(z)=\left\lVert z-A\psi\right\rVert ^2+\left\lVert z-B\psi\right\rVert ^2.
$$

这是两条单位权重的有效约束。默认 $z$ 是变分场变量，未额外要求单位范数。

<a id="statement-8-2"></a>

<a id="thm-interference"></a>

#### 定理 8.2（残差与干涉的精确桥）

若实际保留共同校准的相干路径程序

$$
\Xi_\psi=\frac{\lvert 0\rangle  A\psi+\lvert 1\rangle  B\psi}{\sqrt2},
$$

并在路径寄存器的 $\lvert \pm\rangle =(\lvert 0\rangle \pm\lvert 1\rangle )/\sqrt2$ 基读出，记负端口概率为 $p_-$，则

<a id="eq-interference"></a>

$$
\boxed{
\min_z E_\psi(z)
=\tfrac12\left\lVert (A-B)\psi\right\rVert ^2
=1-\operatorname{Re}\langle\psi,A^\dagger B\psi\rangle
=2p_- .}
\tag{8}
$$

唯一最小元为 $z_*=(A+B)\psi/2$。若改为约束 $\left\lVert z\right\rVert =1$，则

$$
\min_{\left\lVert z\right\rVert =1}E_\psi(z)=4\bigl(1-\sqrt{1-p_-}\bigr).
$$

**证明。**

记 $a=A\psi,b=B\psi$。配方给

$$
\left\lVert z-a\right\rVert ^2+\left\lVert z-b\right\rVert ^2
=2\left\lVert z-\frac{a+b}{2}\right\rVert ^2+\frac12\left\lVert a-b\right\rVert ^2.
$$

酉性给 $\left\lVert a\right\rVert =\left\lVert b\right\rVert =1$，故第二项等于 $1-\operatorname{Re}\langle a,b\rangle$。负端口的未归一化数据向量是 $(a-b)/2$，所以 $p_-=\left\lVert a-b\right\rVert ^2/4$。若要求 $\left\lVert z\right\rVert =1$，则
$E_\psi(z)=4-2\operatorname{Re}\langle z,a+b\rangle$，Cauchy–Schwarz 使最大实部为 $\left\lVert a+b\right\rVert =2\sqrt{1-p_-}$，得后一式。$a+b=0$ 时所有单位 $z$ 都达最小值四。

∎

对固定输入，零残差等价于 $A\psi=B\psi$；对所有输入，等价于 $A=B$。若两种局部推进为 $U,V$，取 $A=VU,B=UV$，则全输入的零残差恰要求 $[U,V]=0$。固定输入则只需 $(VU-UV)\psi=0$。

这并不要求所有量子多路径都零残差。非零 $p_-$ 是完全合法的干涉现象；只有把两条路径声明为同一个唯一端点向量的两种描述，才要求零相容。若 $A=e^{i\theta}B$，数据射线单独看相同，路径干涉却给 $p_-=\sin^2(\theta/2)$。因此受控路径的相位参考须保留，不能把单独门的整体相位在控制接口内随意删掉。

<a id="statement-8-3"></a>

<a id="thm-graphaction"></a>

#### 定理 8.3（静态有根图的相容与变分）

给底层连通的有限图、等维有限维顶点载体及边酉 $U_e$，正边权 $a_e$。固定根向量 $x_r=b$，定义

$$
\mathcal S(x)=\sum_{e:u\to v}a_e\left\lVert x_v-U_ex_u\right\rVert ^2 .
$$

则固定根后的最小元唯一。零最小值存在，当且仅当每个以根为基点的底层闭走传输固定 $b$；存在时零完成唯一。对所有根输入都零相容，当且仅当所有此类闭走传输为 $I$。

**证明。**

反向经过一条边时用 $U_e^\dagger$ 作代数传输。零残差使每条边递归成立，因此任意闭走必须将 $b$ 送回自身。反之沿根到顶点的任一路径运输 $b$；闭走条件使不同路径给同一向量，且满足所有边，得到唯一零完成。

对固定根的差场 $\delta x_r=0$，若齐次平方和为零，边上的可逆传输与底层连通性迫使全部 $\delta x_v=0$。故对自由顶点变量的 Hessian 正定，有限维二次型存在唯一全局最小元；不满足闭走条件时，该最小值严格为正。对所有 $b$ 均被某闭走固定等价于该传输为 $I$。

∎

反向传输在这里是检验相容的代数工具，未许可物理因果倒流。一个 DAG 仍可能有底层闭走。所有顶点零场在未固定非零边界时总可用，因此根边界不可省略。

<a id="statement-8-4"></a>

<a id="prop-weights"></a>

#### 命题 8.4（长路径的有效权重）

对于两条内部互不相交、无额外耦合边的路径，分别具有完整传输 $A,B$，定义

$$
k_A=\left(\sum_{e\in p_A}a_e^{-1}\right)^{-1},\qquad
k_B=\left(\sum_{e\in p_B}a_e^{-1}\right)^{-1}.
$$

固定根 $\psi$ 后，先消去内部顶点，再对共同端点最小化，得到

$$
\min\mathcal S
=\frac{k_Ak_B}{k_A+k_B}\left\lVert (A-B)\psi\right\rVert ^2
=\frac{4k_Ak_B}{k_A+k_B}p_-.
$$

**证明。**

沿一条路径用累计酉变换将所有边运输化为普通差分 $d_e$。其和固定为运输回根后的端点差 $d$。加权 Cauchy–Schwarz 给

$$
\left\lVert d\right\rVert ^2=\left\lVert \sum_e d_e\right\rVert ^2
\le\left(\sum_ea_e^{-1}\right)\sum_ea_e\left\lVert d_e\right\rVert ^2,
$$

等号可由 $d_e$ 取为 $a_e^{-1}$ 比例的同向分量实现。所以消元后为 $k_A\left\lVert z-A\psi\right\rVert ^2$，另一条同理。两路径内部不交使两个消元可独立进行；再次配方得系数 $k_Ak_B/(k_A+k_B)$，再用 $p_-$ 公式。

∎

例如两条各有两条单位权边的菱形，$k_A=k_B=1/2$，完整图最小残差为 $p_-$。式 [(8)](#eq-interference) 的 $2p_-$ 只对应两个单位权的有效端点约束。边权与切面细分会改变变分的数值，故不能把某个残差常数直接认定为普遍物理能量。

<a id="statement-8-5"></a>

<a id="prop-gauge"></a>

#### 命题 8.5（共同参考框变换不改变可读关系）

在各顶点选择酉参考框 $W_v$，同时令

$$
x_v'=W_vx_v,\quad
U_e'=W_vU_eW_u^\dagger,\quad
E_v'=W_vE_vW_v^\dagger.
$$

则边残差范数及总残差泛函、同一顶点的 Born 概率和闭走固定向量条件全部不变。

**证明。**

每条新残差为 $W_v(x_v-U_ex_u)$，酉性保持范数。迹的循环性保持读出概率。沿闭走的中间 $W^\dagger W$ 消去，只剩根处的酉共轭，故固定向量条件等价。

∎

这精确表达“系统与尺子都内生”的一部分：共同换坐标是冗余；只改变仪器相对系统的基底则一般改变概率。命题 [3.4](#prop-gold) 正是后者的例子。

<a id="sec-9"></a>

## 9. 观察者究竟必须记住多少：固定黄金菜单的六参数定理

“稳定的三个读数”是否足以预测以后，不由三个这个数目决定，而由许可的后继操作决定。项目已有未来效果闭包判据 [[2](#ref-qprinciples)]；下面给出完整证明，再将其算到固定原生菜单。

<a id="statement-9-1"></a>

#### 定义 9.1（未来效果空间）

在固定 $d$ 维完整载体上，声明共同合法的仪器分支
$\{\Phi_{a,o}\}$ 与含 $I$ 的末端效果族 $\mathcal G$。定义

$$
W_0=\operatorname{span}_{\mathbb R} \mathcal G,\qquad
W_{n+1}=W_n+\sum_{a,o}\Phi_{a,o}^*W_n,\qquad
W_\infty=\bigcup_n W_n.
$$

对偶由 $\operatorname{Tr} (\Phi(\rho)E)=\operatorname{Tr} (\rho\Phi^*(E))$ 定义。使用有限菜单即可；任意同载体菜单也可将求和解释为全部像的实张成。所有仍会返回的程序和环境必须已计入载体。

<a id="statement-9-2"></a>

<a id="thm-future"></a>

#### 定理 9.2（最小仿射预测摘要）

若 $r_0=\dim_\mathbb R W_0$，则闭包至多发生 $d^2-r_0$ 次严格增维。两态对全部许可有限记录同律，当且仅当
$\rho-\sigma\perp W_\infty$（迹内积）。在全密度态来源上，保存全部这些概率的最小实仿射摘要维数恰为

$$
\boxed{\dim_\mathbb R  W_\infty-1.}
$$

**证明。**

有限历史的概率是末端效果经分支对偶有序拉回后的迹配对。归纳得 $W_n$ 正是长度不超过 $n$ 的全部词效果的实张成。一旦某层不增维，它已经被每个对偶保持，以后不再增长；$\operatorname{Herm} _d$ 的实维数为 $d^2$，得增维界。全部词效果配对相同恰等价于所有有限记录概率相同；反馈选择也可按相同已得前缀逐分支应用此事实。

取 $W_\infty$ 的实基 $I,E_1,\ldots,E_{r-1}$，其 $r-1$ 个期望构成充分仿射摘要。若某摘要秩更小，则在迹零 Hermitian 方向空间中，其核包含一个未被 $W_\infty$ 消去的 $D$。在 $I/d$ 附近取足够小的 $\varepsilon>0$，两态 $I/d\pm\varepsilon D$ 合法且摘要相同，却有未来效果区分它们，矛盾。

∎

这个参数下界限定于仿射统计和含内部开集的全态来源，不是对任意不连续编码、受限来源或增长联合空间的普遍数字结论。闭包稳定也不表示态随切面收敛，更不表示有限样本已经知道精确概率。

<a id="statement-9-3"></a>

<a id="thm-six"></a>

#### 定理 9.3（同一地址原生门的精确六参数预测）

在 $H_5$ 上只允许同一固定地址的原生 $K$、其有限正向幂，以及共同五模式 PVM 的指定 Lüders 读取。可保留经典结果并依结果选择后续同菜单操作，但不加入混合不同扇区的额外地址、外供换基或重制备。则

<a id="eq-seven"></a>

$$
W_\infty=\operatorname{Herm} (H_{0,2})\oplus\mathbb R \Pi_1
\oplus\mathbb R \Pi_3\oplus\mathbb R \Pi_{13},\qquad
\dim_\mathbb R  W_\infty=7,
\tag{9}
$$

其中 $H_{0,2}=\operatorname{span}_\mathbb C \{\lvert 0\rangle ,\lvert 2\rangle \}$。全态来源上的最小仿射预测摘要恰为六个实数，例如

<a id="eq-six"></a>

$$
\boxed{(X,Y,Z,\kappa,\operatorname{Re}\rho_{02},
\operatorname{Im}\rho_{02}) .}
\tag{10}
$$

**证明。**

门 $K$ 保持分解 $H_{0,2}\oplus H_1\oplus H_3\oplus H_{13}$，模式投影也保持此分解。因此所有分支对偶保持右侧的块对角实空间，给出 $W_\infty$ 的七维上界。完整三读口联合记录提供全部 $\Pi_s$，所以所有对角方向已经可得。

令 $a=\varphi^{-1},d=\varphi^{-2},b=\varphi^{-3/2}$，$P=\Pi_2$。两个合法词效果为
$Q_+=K^\dagger PK$ 与 $Q_-=KPK^\dagger$；后者由正向 $K^9$ 的拉回实现。在活动块中，

$$
Q_+=\begin{pmatrix}a&b\bar\omega\\b\omega&d\end{pmatrix},
\qquad
Q_-=\begin{pmatrix}a&b\omega\\b\bar\omega&d\end{pmatrix}.
$$

例如 $(Q_+)_{12}=b[(\bar\omega-1)+|\omega-1|^2d]=b\bar\omega$，因为 $|\omega-1|^2d=1$；其对角元由命题 [3.4](#prop-gold) 给出。设 $\theta=3\pi/5$，

$$
D=a\Pi_0+d\Pi_2,\quad
X_{02}=\lvert 0\rangle \langle 2\rvert +\lvert 2\rangle \langle 0\rvert ,\quad
Y_{02}=-i\lvert 0\rangle \langle 2\rvert +i\lvert 2\rangle \langle 0\rvert .
$$

则

$$
Q_\pm=D+b\cos\theta\,X_{02}\pm b\sin\theta\,Y_{02}.
$$

$\sin\theta,\cos\theta$ 均非零，故 $Q_\pm$ 的和差连同对角方向给出 $X_{02},Y_{02}$。七维上界遂取等，得式 [(9)](#eq-seven)。定理 [9.2](#thm-future) 给六维最小值；式 [(3)](#eq-fiber) 用 $X,Y,Z,\kappa$ 恢复全部人口，另两实数恢复唯一可见的活动块相干，故式 [(10)](#eq-six) 达到此下界。

∎

这一定理进一步把三个稳定分量背后的隐藏信息分成一项经典关联与一项复相干。若想显式读回它们，记
$q_\pm=\operatorname{Tr} (\rho Q_\pm)$、$d_0=a p_0+d p_2$，则

$$
\operatorname{Re}\rho_{02}
=\frac{q_++q_--2d_0}{4b\cos\theta},
\qquad
\operatorname{Im}\rho_{02}
=\frac{q_--q_+}{4b\sin\theta}.
$$

这些是理想概率律的线性逆式，未省略估计这些概率所需的重复来源与样本成本。其余跨扇区相干在这个菜单下永远不能返回读口；加入新地址或新基底之后，应重新计算闭包。

<a id="statement-9-4"></a>

#### 推论 9.4（全五维换基的另一极限）

若明确额外允许同一 $H_5$ 上的全部酉换基和模式读取，则
$W_\infty=\operatorname{Herm} _5$，最小全来源仿射摘要为二十四维。

**证明。**

任意秩一投影均为某模式投影的酉共轭。它们实张成全部 Hermitian 矩阵，故闭包维数为二十五，再用定理 [9.2](#thm-future)。

∎

六维与二十四维属于两个不同菜单。一个逻辑编码上的通用性定理，不能不经接口证明就替换成这个原子 $H_5$ 上的全酉菜单。

<a id="sec-10"></a>

## 10. 预测、递归、变分与最优化：可以怎样严格等同

<a id="statement-10-1"></a>

#### 定义 10.1（预测问题的数据）

一个可比较的预测问题至少指定：候选模型或门菜单、输入与可保留记录、待预测事件、读取规则、证据评分，以及资源成本。固定这些数据后，预测策略可以由历史 $h$ 递归生成程序 $b(h)$；其记录扩张按定理 [5.2](#thm-tree) 实现。

本稿已给出一个完全成立的等价：固定模型与非零边界时，逐边递归相容、残差为零和同一静态历史的构造刻画同一解。两路径定理还把指定残差接到了 Born 干涉概率。这里的“最优化”是对已声明泛函求全局最小；每套候选门各自都可构造自己的零历史，因此内部自洽不能单独选出预测实际数据最好的模型。

前稿 v20 使用的有成本编译问题提供另一条明确路线。设已知目标 $R$、有限合法字母表、每门正成本 $c_g$、有限非负边界误差 $b$，则

$$
F_\eta(R)=\inf_w\bigl[b(U_w^\dagger R)+\eta C(w)\bigr],
\qquad C(w)=\sum_{g\in w}c_g,\quad\eta>0,
$$

可按左端矩阵因子 $U_w=gU_v$ 分解成

$$
F_\eta(R)=\min\left\{b(R),\min_g\left[\eta c_g+F_\eta(g^\dagger R)\right]\right\}.
$$

递归与该变分目标表达同一个已定义问题。$b,\eta,c_g$ 仍然是所选评分与资源合同；相容本身没有唯一决定它们。若目标或原生门也未知，应把其信息或后验纳入完整观察者状态，再定义同源风险；不能先给每种未知关系各自一个编译解，就宣称存在同一个对全部关系都成功的程序。

<a id="statement-10-2"></a>

#### 命题 10.2（原生周期排除普遍严格下降）

不存在一个实函数 $L$，使所有态每次应用原生 $K$ 都满足
$L(K\psi)<L(\psi)$。

**证明。**

若存在，连续十次严格下降给
$L(K^{10}\psi)<L(\psi)$，而 $K^{10}\psi=\psi$，矛盾。

∎

观察者的带记录状态可以增长，某个求解器也可以逐次降低残差；这些不等于无记录的原生酉门对全部数据都严格降低同一个能量。带权路径的最小值随边权和残差归一化改变，也不能仅由零解决定物理作用量的单位。

<a id="statement-10-3"></a>

<a id="prop-diagonal"></a>

#### 命题 10.3（固定稳定读出与通用门的分工）

若酉门 $U$ 对所有输入都保持三个固定 $N_i$ 的期望，则 $U$ 在五模式基中对角。只由这类门生成的电路不能稠密生成 $\operatorname{SU} (5)$。

**证明。**

全输入期望保持给 $U^\dagger N_iU=N_i$。因此 $U$ 与三个 $N_i$ 对易，继而与定理 [2.2](#thm-five) 中所有多项式原子 $\Pi_s$ 对易。每个原子秩一，故 $U$ 对角。对角酉子群是闭真子群，其乘积仍对角，不能稠密覆盖 $\operatorname{SU} (5)$。

∎

因此可以把一个可递归的 AURIC 观察原子组织为：预测生成基底程序；同一程序下读取三个兼容位并保留完整模式记录；更新后续程序和时钟。原子内部的记录顺序可以无关，不同基底原子之间则必须满足实际的操作依赖、对易或其它已证明的相容恒等式。固定黄金门提供换基与非交换的资源，稳定读出代数提供可重复的经典记录；两者共同参与门网络。

<a id="sec-11"></a>

## 11. 综合结论：一个可检验的静态观察者模型

<a id="statement-11-1"></a>

<a id="thm-synthesis"></a>

#### 定理 11.1（有限观察协议的静态实现）

给有限深度的内生预测协议，各层数据、程序、记录与辅助载体均有限维。设完整初态纯；混态时将其净化计入完整载体。每层由既有记录和合法等距过程生成程序，三读口引用共同程序并采用第 4 节指定的 Lüders／相干复制仪器，读口之间无额外后态扰动；整体历史保留指针及全部扩张辅助输出，即使某些输出以后不再返回，并给定时钟权重与校准。则可构造一个固定的整体历史向量，满足：

1. 每个原子内部的三项完整记录与排列无关；
2. 条件于时钟与历史，得到该协议相应的递归分支状态；
3. 完整过程可酉扩张，整体历史属于一个正传播约束的零空间；
4. 基底改变后跨原子读出不必对易，且原生 $K$ 已给命题 [3.4](#prop-gold) 的精确反例；
5. 在声明的固定有限载体与菜单上，所需预测摘要由未来效果闭包决定。

**证明。**

共同程序的兼容性和记录等距由定理 [4.2](#thm-program) 给出。将各层组成定理 [5.2](#thm-tree) 的完整记录递归，并对有限深度作酉扩张；在共同载体上应用定理 [6.1](#thm-history) 即得固定历史向量与零约束。时钟、记录投影的联合条件化给各分支状态。第四条使用显式黄金门反例，第五条使用定理 [9.2](#thm-future)。

∎

这是一套构造性一致模型，不是对宇宙本体已被唯一确定的断言。它对用户直觉给出以下具体解释：

1. <strong>整体不随外部参数改变：</strong>可以用静态历史态或完整等距的直接极限表达；需要同时定义切面观测与条件事件。
2. <strong>观察者内生：</strong>程序、参考框、记录和仍相关的环境位于模型内部；门序列描述其变换，但不能省掉这些载体。
3. <strong>预测成为增长：</strong>预测产生下一层程序和可区分记录；是否真的新增信息、是否能持续保留，需要实际记录容量与后继菜单。
4. <strong>三个稳定读出：</strong>是五模式交换代数的三个生成元。它们可无先后地读取，但三个均值不是完整量子状态。
5. <strong>所有量和尺子都可能未知：</strong>共同参考框的改变具有规范冗余；相对参考框的不确定性则进入程序及联合态。基底可以处于叠加，但不能无资源地精确程序化无限多尖锐测量。
6. <strong>递归、变分与最优：</strong>在固定边界、约束和评分之后可以描述同一问题；相容性没有单独选择唯一评分，也没有证明每次可逆门都严格优化。

最直接的后续数学对象已经明确：扩大实际黄金门地址菜单时，计算 $W_\infty$ 如何从本稿的七维块空间增长；当基底程序也未知且需要在线生成时，保留共同来源，比较其可达测量误差、程序维数及记录成本。本稿的六参数定理、精确顺序差和路径干涉等式给出可以逐项检验的起点。

<a id="sec-bibliography"></a>

## 文献与项目来源

<a id="ref-snapshot"></a>

<strong>[1]</strong> the-omega-institute/trureturing.
[固定提交 ce2773bd（dev，2026-10-29 UTC）](https://github.com/the-omega-institute/trureturing/commit/ce2773bd014df637336d2e89f83f220d8535c5be)；
[相对 v20 的固定比较](https://github.com/the-omega-institute/trureturing/compare/837df9a7545012a9e669c61716dac078f5552d96...ce2773bd014df637336d2e89f83f220d8535c5be)。
本文使用定向源码阅读与完整 theory 子树对照。

<a id="ref-qprinciples"></a>

<strong>[2]</strong> 项目：[量子原则与相干重构](https://github.com/the-omega-institute/trureturing/blob/ce2773bd014df637336d2e89f83f220d8535c5be/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md)。
命题 3.4；定义及定理 11.1–11.5；公理接口 12.1–12.2。

<a id="ref-pyramid"></a>

<strong>[3]</strong> 项目：[AURIC FIB 金字塔基础公式与关系](https://github.com/the-omega-institute/trureturing/blob/ce2773bd014df637336d2e89f83f220d8535c5be/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)。
第 2–4 节：五个事件幂等元、三坐标及 $\kappa$ 纤维。

<a id="ref-threeaxis"></a>

<strong>[4]</strong> 项目：[观察者内生三轴几何与预测接口](https://github.com/the-omega-institute/trureturing/blob/ce2773bd014df637336d2e89f83f220d8535c5be/docs/develop/theory/AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md)。
第 3、7–9 节：投影残差、第三响应、未来充分性、Pauli 坐标和保留环境。

<a id="ref-localmodels"></a>

<strong>[5]</strong> 项目：[观察者相对局部模型与未来可辨识性](https://github.com/the-omega-institute/trureturing/blob/ce2773bd014df637336d2e89f83f220d8535c5be/docs/develop/theory/AURIC_FIB_ATOM_OBSERVER_RELATIVE_LOCAL_MODELS_AND_FUTURE_IDENTIFIABILITY.md)。
第 9–10 节：来源校准、物理速率与钟势。

<a id="ref-clockvolume"></a>

<strong>[6]</strong> 项目：[局部时钟、因果场与纤维动力学](https://github.com/the-omega-institute/trureturing/blob/ce2773bd014df637336d2e89f83f220d8535c5be/docs/develop/theory/AURIC_FIB_ATOM_LOCAL_CLOCK_CAUSAL_FIELD_AND_FIBER_DYNAMICS.md)。
混合参考输入；优先限定 Q2、Q13、Q14。

<a id="ref-clockkernel"></a>

<strong>[7]</strong> 项目：[局部时钟核与输出分辨接缝可见性](https://github.com/the-omega-institute/trureturing/blob/ce2773bd014df637336d2e89f83f220d8535c5be/docs/develop/theory/AURIC_FIB_ATOM_LOCAL_CLOCK_KERNEL_AND_OUTPUT_RESOLVED_SEAM_VISIBILITY.md)。
混合参考输入及后续条件论证；假设 18、定理 19–21 明确保留相位与等待标定。

<a id="ref-v16"></a>

<strong>[8]</strong> 项目：[预测、递归、最优化与变分 v16](https://github.com/the-omega-institute/trureturing/blob/ce2773bd014df637336d2e89f83f220d8535c5be/docs/develop/theory/AURIC_PREDICTION_RECURSION_OPTIMIZATION_AND_VARIATION_V16.md)。
前稿 XeLaTeX 的仓内转录；传播残差、历史态及有成本递归。

<a id="ref-v18"></a>

<strong>[9]</strong> 项目：[三角剖分、塌缩与递归酉门 v18](https://github.com/the-omega-institute/trureturing/blob/ce2773bd014df637336d2e89f83f220d8535c5be/docs/develop/theory/AURIC_TRIANGULATION_COLLAPSE_AND_RECURSIVE_UNITARY_GATES_V18.md)。
前稿 XeLaTeX 的仓内转录；固定黄金数据、三读口保持的 Schur 通道及静态切面。

<a id="ref-pw"></a>

<strong>[10]</strong> D. N. Page and W. K. Wootters.
<em>Evolution without evolution: Dynamics described by stationary observables</em>.
Physical Review D 27, 2885–2892 (1983).
[doi:10.1103/PhysRevD.27.2885](https://doi.org/10.1103/PhysRevD.27.2885).
本文核对公开摘要，作为内部时钟条件描述的历史来源。

<a id="ref-history"></a>

<strong>[11]</strong> D. Aharonov, W. van Dam, J. Kempe, Z. Landau, S. Lloyd and O. Regev.
<em>Adiabatic Quantum Computation is Equivalent to Standard Quantum Computation</em>.
SIAM Journal on Computing 37, 166–194 (2007).
[arXiv:quant-ph/0405098](https://arxiv.org/abs/quant-ph/0405098).
历史态与传播约束的标准背景；本文自足证明带权版本。

<a id="ref-joint"></a>

<strong>[12]</strong> T. Heinosaari, D. Reitzner and P. Stano.
<em>Notes on Joint Measurability of Quantum Observables</em>.
Foundations of Physics 38, 1133–1147 (2008).
[arXiv:0811.0783](https://arxiv.org/abs/0811.0783).
尖锐测量与一般 POVM 的兼容性区别。

<a id="ref-program"></a>

<strong>[13]</strong> T. Heinosaari and M. Tukiainen.
<em>Notes on Deterministic Programming of Quantum Observables and Channels</em>.
Quantum Information Processing 14, 3097–3114 (2015).
[arXiv:1412.0419](https://arxiv.org/abs/1412.0419)，Proposition 4。
固定后处理合同下不同尖锐可观测量的程序正交。

<a id="ref-disturb"></a>

<strong>[14]</strong> D. Kretschmann, D. Schlingemann and R. F. Werner.
<em>The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation</em>.
IEEE Transactions on Information Theory 54, 1708–1717 (2008).
[arXiv:quant-ph/0605009](https://arxiv.org/abs/quant-ph/0605009).
本文仅使用并自足证明全态精确零扰动的特例。
