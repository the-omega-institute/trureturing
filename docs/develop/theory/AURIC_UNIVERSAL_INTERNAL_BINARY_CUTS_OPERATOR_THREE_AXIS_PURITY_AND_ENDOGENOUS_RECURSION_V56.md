**原稿编译、字体与版式信息。** XeLaTeX；编译两次；11pt、A4 的 article，页边距 23mm，页眉高度 16pt。未安装 CJK 字体时定义 AURICFontPath。若已定义，主字体从该路径读取 NotoSerifCJKsc-Regular.otf，粗体及粗斜体读取 NotoSerifCJKsc-Bold.otf，斜体读取 Regular。否则优先 Noto Serif CJK SC（斜体同正体，粗斜体用 Bold）；该字体不存在时回退 FandolSong-Regular.otf，粗体及粗斜体为 FandolSong-Bold.otf，斜体为 Regular。等宽字体 Latin Modern Mono；中文断行区域 zh，断行伸缩 0pt plus 1pt。

原稿加载 geometry、fontspec、amsmath、amssymb、amsthm、mathtools、bm、mathrsfs、booktabs、array、tabularx、enumitem、fancyhdr、xcolor、needspace、hyperref；链接支持 Unicode，链接、网址与引文均用 auricblue（RGB 24,53,79）。PDF 标题：AURIC：唯一本体的观察者互补与算子三轴纯性；作者：AURIC research continuation；主题：Universal internal binary cuts, operator-valued Bloch purity, coherent recursion and observer-relative dynamics。

原稿采用 definition 样式，定义、定理、命题、推论、说明按节共享编号；证明名“证明”，摘要名“摘要”，文献名“固定来源与阅读范围”。首行缩进 1.8em，段间距 2pt，紧急伸缩 3em，列表无额外间距且左缩进 2em；fancy 页眉左为“AURIC：内生观察者、互补与算子三轴”，右为“v56 / 2026-11-01”，页脚居中页码；允许显示公式分页（级别 2）。标题、第二标题、版本行后间距依次为 7pt、8pt、5pt。数学宏在下文逐项展开，项目链接固定到所给提交。

# AURIC：唯一本体的观察者互补

## 算子三轴纯性与内生递归

**定义、定理与纸面证明　v56.0**

2026 年 11 月 1 日　Asia/Singapore

<!-- v56-note:N0 -->

**编者注（Markdown 编者，N0）。** 下文保留原稿的全部断言及作者第一人称报告。“本轮／上一轮”、HEAD 请求 403、十份保留源、阅读与几何审读、文稿编译及未执行数学程序等均是原稿作者的报告，不是 Markdown 编者追认的执行记录。独立编者补充均单独署名；本文的数学结论为所列模型前提下的纸面推导。

<!-- /v56-note -->

## 摘要

本文将“观察者与非观察者均在同一本体内，一切内部二分都适用同一结构”写成全称命题。
任意归一整体向量与任意正交投影产生至多二维的相干支撑；非退化时有纯态 Bloch 三轴、
内部 Pauli 角代数及酉延拓，完整信息由二元态与其内部嵌入共同保留。
固定二元记录等距则对全部输入同时有效，并将分支内态与跨分支相干保存在同一个整体中。
在项目既有算子值 $S,X,Y,Z$ 分块上，令 $m=\operatorname{Tr} R$，证明新的组织公式
$D_m=2mS-S^2-X^2-Y^2-Z^2=2\operatorname{Tr}_2(mR-R^2)\succeq0$。
对非零正迹类 $R$，$D_m=0$ 当且仅当整体秩一；归一时另得纯性反对易与交换子恒等式。
归一纯整体的标量局部球面缺额等于内部外积范数平方的四倍，并等于两侧共同线性熵的两倍；
正性与全部联合关系必须保留。
进一步给出混合的算子缺额分解、近纯稳定界、固定接口的漏出守恒、随动观察切口的协变导数、
有限相干记录树与质量递乘，以及观察商上补事件可判定的饱和条件。
所有参照、标签、记录和余下自由度均属同一个整体。数学表示的普遍性与实际读口、门权限、
概率标定、无限极限拓扑分别陈述，不把三个算子误作三个普通实数。

## 1. 本体约定、固定来源与本轮推进

本文按字面采用一个总态模型：整体载体为复 Hilbert 空间 $\mathcal{H}$，本体纯态为单位向量
$\Omega\in\mathcal{H}$ 的射线。观察者、非当前观察部分、相位参照、记忆与控制均在同一整体中。
“非观察者”相对于某个内部观察结构定义，不指宇宙之外的第二个本体。
项目的事件配置对象也记作 $\Omega$；为避免类型混淆，本文的 $\Omega$ 始终专指总态向量。

本轮唯一一次活动 HEAD 请求返回 HTTP 403，未取得新 SHA，随后没有再查询活动版本。
因此全部项目引用沿用上一轮已核验的不可变提交

`74d3fbdb768819e31f736d1e2e5686e3f03f6a12`，

 其提交时刻为 2026-10-31 23:59:17，新加坡。
本轮不能认证它仍为最新，也没有可认证的后续增量。十份保留源的 Git blob 身份与该固定树一致，
旧文件的有界阅读范围见文末；来源身份不等于整库数学认证。［[1](#ref-head)］

项目 V24 已有纯整体的局部 Gram 缺额；V37、V51、V52 已有完整算子值三轴及递归；
V52 已有带相位与零标记的纯态树图册、固定可恢复压缩下界。
本文的推进集中于算子正缺额 $D_m$、整体纯性的等价判据、内部二分的全称量词、
同一本体中的接口对齐和动态漏出。标准 Pauli、外积、有限算子代数等不作数学史首次发现声明。
［[4](#ref-v24), [5](#ref-v37), [6](#ref-v51), [7](#ref-v52), [10](#ref-klv), [11](#ref-zanardi)］

约定内积对第二变量线性，$P_a=aa^\dagger$ 对单位 $a$ 表示纯态，
$T(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$。
二分向量与正迹类算子的主恒等式适用于任意 Hilbert 载体；涉及矩阵代数分类、有限门延拓和
参数计数时明确使用有限维。微分公式在有限维给出，以免隐去无界生成元的定义域。

<!-- v56-note:N1 -->

**编者注（Markdown 编者，N1）。** 任意 Hilbert 范围中的投影及酉均为全空间有界算子，向量使用 Hilbert 张量积；未要求载体可分。有限秩支撑上的门加正交补恒等可在任意 Hilbert 空间延拓。有限维分类、有限因子参数展开与微分公式保持各自明示限制，不把它们推广到无界生成元。

<!-- /v56-note -->

## 2. 任意内部正交二分的纯态三轴接口

#### 定义 2.1（内部二元切口）

给定 $P=P^\dagger=P^2$，令 $Q=I-P$。定义

$$
\Omega_0=P\Omega,\quad \Omega_1=Q\Omega,\qquad
 p=\|\Omega_0\|^2,\quad q=\|\Omega_1\|^2.
$$

该定义描述同一整体向量的两个互补振幅部分；它本身没有把两个张量子系统的约化态相加。

#### 定理 2.2（普遍内部二分）

对每个单位 $\Omega$ 和每个正交投影 $P$，

$$
\boxed{\Omega=\Omega_0+\Omega_1,\quad
 \langle\Omega_0,\Omega_1\rangle=0,\quad p+q=1},
 \qquad \dim\operatorname{span}\{\Omega_0,\Omega_1\}\le2.
$$

若 $p,q>0$，令 $u=\Omega_0/\sqrt p$、$v=\Omega_1/\sqrt q$，定义

$$
J_{\Omega,P}:\mathbb{C}^2\to\mathcal{H},\quad J\lvert 0\rangle=u,\ J\lvert 1\rangle=v.
$$

则 $J^\dagger J=I_2$，且

$$
\Omega=J\chi,\qquad
 \chi=\begin{pmatrix}\sqrt p\\\sqrt q\end{pmatrix},\qquad
 r_\chi=(2\sqrt{pq},0,p-q)\in S^2.
$$

**证明。**

$PQ=0$ 给正交性，$P+Q=I$ 给分解与平方守恒。
两条非零分支归一后正交，故 $J$ 等距。
$4pq+(p-q)^2=(p+q)^2=1$ 给球面式。

∎

对一般单位逻辑向量 $\chi=(\alpha,\beta)^{\mathsf T}$，二元线性关系
$\alpha\xi_1-\beta\xi_0=0$ 的核为 $\mathbb{C}\chi$。
其正残差行 $\ell_\chi=(-\beta,\alpha)$ 满足

$$
\ell_\chi^\dagger\ell_\chi=I-P_\chi.
$$

所以本定理确实回到“线性关系、正平方残差、归一化纯态三轴”的同一格式。
这里的关系由所给整体态与切口确定；该表达能力不等于凭空指定了本体的实际取值。

#### 命题 2.3（内部相位参照与零边界）

对实数 $\theta_0,\theta_1$ 及 $D=\operatorname{diag}(e^{i\theta_0},e^{i\theta_1})$，完整数据具有等价

$$
(J,\chi)\sim(JD,D^\dagger\chi),\qquad J\chi=(JD)(D^\dagger\chi).
$$

在新参照下，逻辑三轴为

$$
(2\sqrt{pq}\cos(\theta_0-\theta_1),\,
 2\sqrt{pq}\sin(\theta_0-\theta_1),\,p-q).
$$

若 $p=0$ 或 $q=0$，占据支撑只有一维，分别记作球面的南极或北极；零分支方向不作归一化。

**证明。**

相位式由 $D^\dagger\chi$ 及 $r_y=2\Im(\bar\chi_0\chi_1)$ 计算。
零范数分支为零向量，故只剩另一条单位分支。

∎

自适应选取 $u,v$ 使 $r_y=0$，是把相位纳入了 $J$。
例如 $(\lvert 0\rangle\pm\lvert 1\rangle)/\sqrt2$ 在各自分支规范下逻辑系数相同，但第二基向量分别为
$\lvert 1\rangle$ 与 $-\lvert 1\rangle$。完整重构需要同时保留 $J$。
若 $P=0$，不能声称同一 $\mathcal{H}$ 内总有满足 $PJ=J\lvert 0\rangle\langle 0\rvert$ 的完整二元等距；
“至多二维”和零标记已经涵盖这个边界。

#### 推论 2.4（接口的内部酉门）

非退化时令 $\Pi=JJ^\dagger$、$\Sigma_j=J\sigma_jJ^\dagger$，则

$$
\Sigma_j\Sigma_k=\delta_{jk}\Pi+i\sum_l\epsilon_{jkl}\Sigma_l.
$$

对任意 $U\in U(2)$，

$$
\widetilde U=JUJ^\dagger+(I-\Pi)
$$

为 $\mathcal{H}$ 上的酉算子，且 $\widetilde UJ=JU$。

**证明。**

用 $J^\dagger J=I_2$ 代入 Pauli 乘法；酉算子在
$\operatorname{Ran} J\oplus(\operatorname{Ran} J)^\perp$ 上分别执行 $U$ 与恒等。

∎

因此每个非退化二分都有一个内部 $M_2(\mathbb{C})$ 角代数。
它的单位元是支撑投影 $\Pi$，不是自动等于全部载体的 $I$。

## 3. 观察者子系统、内部代数与三轴对齐

#### 定义 3.1（观察者的内部代数模型）

若以可用可观测量描述观察者，另给含幺 $*$-子代数 $\mathcal{A}\subseteq B(\mathcal{H})$。
其交换子代数为

$$
\mathcal{A}'=\{B\in B(\mathcal{H}):BA=AB\text{ 对全部 }A\in\mathcal{A}\}.
$$

总态在观察者上的限制为 $A\mapsto\langle\Omega,A\Omega\rangle$。
$\mathcal{A}'$ 的定义不等于集合补集，也不删除交互关系。

当整体 $\mathcal{H}$ 有限维时，含幺 $*$-子代数的标准表示给出

$$
\mathcal{H}\cong\bigoplus_\lambda
 (\mathbb{C}^{n_\lambda}\otimes\mathbb{C}^{m_\lambda}),\quad
 \mathcal{A}\cong\bigoplus_\lambda(M_{n_\lambda}\otimes I_{m_\lambda}),\quad
 \mathcal{A}'\cong\bigoplus_\lambda(I_{n_\lambda}\otimes M_{m_\lambda}).
$$

这是共同载体内部的分解，二者有共同中心；多个中心块时，块间相干仍可存在于更大的
$B(\mathcal{H})$ 中。该结构可见 Knill–Laflamme–Viola 定理 5、Zanardi–Lidar–Lloyd
的可观测量诱导张量结构；项目 RRO 也明确援引它，同时没有把实际实效果空间
$\mathcal W$ 自动宣称为含幺代数。［[10](#ref-klv), [11](#ref-zanardi), [9](#ref-rro)］

<!-- v56-note:N2 -->

**编者注（Markdown 编者，N2）。** 上段文献对应限于有限维含幺、伴随封闭代数。Knill–Laflamme–Viola 的 Theorem 5 在有限维系统空间上给直和及交换子重数分解；其 Subsystems 段不自动供应实际读口、无噪声性或纠错服务。Zanardi–Lidar–Lloyd 的 General framework / Proposition 1 另需声明有限维代码空间上的局部可取得性、子代数两两对易以及共同生成完整算子代数；一般含中心直和只在指定块中诱导张量结构。nested subalgebras 与 TPS morphing 同样依赖所给代数链或可调控制，不能由一个实效果空间的张成单独取得。

<!-- /v56-note -->

#### 命题 3.2（矩阵单位产生内部张量因子）

若 $e_{ij}\in B(\mathcal{H})$ 满足 $e_{ij}^\dagger=e_{ji}$、
$e_{ij}e_{kl}=\delta_{jk}e_{il}$、$\sum_i e_{ii}=I$，令 $\mathcal{K}=e_{11}\mathcal{H}$。
<!-- v56-note:N3 -->

**编者注（Markdown 编者，N3）。** 本命题的指标为 $1\le i,j,k,l\le n$，其中 $n$ 是正整数；$\mathcal{H}$ 和闭子空间 $\mathcal{K}=e_{11}\mathcal{H}$ 仍可为任意 Hilbert 空间。此时张量积是 $n$ 个闭子空间的有限正交和；$e_{i1}$ 是初支撑 $e_{11}$、末支撑 $e_{ii}$ 的有界部分等距，故内积及满射论证无无限求和缺口。

<!-- /v56-note -->

映射

$$
T:\mathbb{C}^n\otimes\mathcal{K}\to\mathcal{H},\qquad T(\lvert i\rangle\otimes k)=e_{i1}k
$$

为酉，且 $T^\dagger e_{ij}T=\lvert i\rangle\langle j\rvert\otimes I_\mathcal{K}$。

**证明。**

$e_{1i}e_{j1}=\delta_{ij}e_{11}$ 保持内积；$\sum_i e_{ii}=I$ 给满射。
对基向量直接作用即得交织式。与全部矩阵单位对易的算子只能为 $I_n\otimes B$，
所以剩余内部角色在重数因子中。

∎

#### 命题 3.3（两个互补投影何时给固定完整三轴）

给正交投影 $P_0,P_1$，$P_0+P_1=I$。若存在内部部分等距 $L=P_0LP_1$，满足
$LL^\dagger=P_0$、$L^\dagger L=P_1$，则

$$
A_x=L+L^\dagger,\quad A_y=-i(L-L^\dagger),\quad A_z=P_0-P_1
$$

满足 Pauli 乘法，其生成代数给 $\mathcal{H}\cong\mathbb{C}^2\otimes\mathcal{K}$。
反向，一个以 $A_z=P_0-P_1$ 为第三轴的完整 Pauli 表示给
$L=(A_x+iA_y)/2$，满足上述条件。

**证明。**

$L^2=(L^\dagger)^2=0$，两种乘积分别为 $P_0,P_1$，代入即得
$A_jA_k=\delta_{jk}I+i\epsilon_{jkl}A_l$。
反向用相同关系验证 $L$ 的初末支撑，再应用矩阵单位命题。

∎

有限维中这种 $L$ 存在当且仅当两块等秩。切口只确定第三轴，横向的相干比较还需要内部对齐。
两块不等秩时，可保留原矩形关系块，或用下一节的固定记录等距。

若观察者是内部因子 $\mathcal{H}_O$，剩余部分是 $\mathcal{H}_N$，则
$\rho_O=\operatorname{Tr}_N P_\Omega$ 与 $\rho_N=\operatorname{Tr}_O P_\Omega$ 各自迹一。
它们不是范数平方分别为 $p,q$ 的两条整体振幅。任取 $P_O$，令
$P=P_O\otimes I_N$，上一节的普遍二分便完全适用。
例如 $(\lvert 00\rangle+\lvert 11\rangle+\lvert 22\rangle)/\sqrt3$ 的两个边缘均为 $I_3/3$，
选 $P=\lvert 0\rangle\langle 0\rvert\otimes I$ 后却仍只有两条整体分支，质量为 $1/3,2/3$；
第二分支继续保留 $(\lvert 11\rangle+\lvert 22\rangle)/\sqrt2$ 的内部关系。

## 4. 对全部输入固定有效的内部记录表示

#### 定理 4.1（二元记录等距与全态恢复）

对任意 $P_0+P_1=I$ 的正交二分，定义

$$
V_P\psi=\lvert 0\rangle\otimes P_0\psi+\lvert 1\rangle\otimes P_1\psi.
$$

则 $V_P^\dagger V_P=I$。对任意密度态 $\rho$，

$$
R=V_P\rho V_P^\dagger
 =\begin{pmatrix}P_0\rho P_0&P_0\rho P_1\\P_1\rho P_0&P_1\rho P_1\end{pmatrix},
 \qquad V_P^\dagger R V_P=\rho.
$$

特别地，原态纯当且仅当 $R$ 纯。

**证明。**

正交标签使 $V_P^\dagger V_P=P_0+P_1=I$，相乘给重构。
等距在其像上保持密度矩阵非零谱。

∎

标签和原载体均属于同一个整体；上述也可只视作整体的一个等距代码表示。
若实际增加可操控的记录槽，须已有该内部槽的初始化。
在记录与待记录载体的联合空间 $\mathbb{C}^2\otimes\mathcal{H}$ 上，酉完成为

$$
U_P=I_2\otimes P_0+\sigma_x\otimes P_1,\qquad
 U_P(\lvert 0\rangle\otimes\psi)=V_P\psi,\qquad U_P^2=I.
$$

原载体上的完整态没有被复制成两个独立副本。

#### 推论 4.2（记录标签的标量轴与完整相干）

有 $\operatorname{Tr}_\mathcal{H} R=\operatorname{diag}(p,q)$，其中 $p=\operatorname{Tr}(P_0\rho)$、$q=\operatorname{Tr}(P_1\rho)$。
其标量 Bloch 向量仅为 $(0,0,p-q)$，但 $P_0\rho P_1$ 仍保存在联合态中。

**证明。**

$\operatorname{Tr}(P_0\rho P_1)=\operatorname{Tr}(P_1P_0\rho)=0$。

∎

这与前节支撑上的纯逻辑三轴不矛盾：纯逻辑接口的横向算子耦合完整分支方向，
记录标签的局部横向算子是 $\sigma_x\otimes I$ 或 $\sigma_y\otimes I$。
它们属于不同的内部读口。

#### 命题 4.3（一般二元效果及内部酉完成）

对 $0\preceq E\preceq I$，令 $A=\sqrt E$、$B=\sqrt{I-E}$。
则

$$
V_E\psi=\lvert 0\rangle\otimes A\psi+\lvert 1\rangle\otimes B\psi,
 \qquad U_E=\begin{pmatrix}A&-B\\B&A\end{pmatrix}
$$

分别为等距与酉，且 $U_E(\lvert 0\rangle\otimes\psi)=V_E\psi$。

**证明。**

$A^2+B^2=I$ 且 $AB=BA$，故直接相乘得到全部恒等式。

∎

该选择是指定的平方根仪器；效果 $E$ 本身不唯一确定仪器或相干相位。
此选择的分支内积为 $\langle\psi,AB\psi\rangle\ge0$，故其记录 $y$ 轴为零。
每分支仅有一个 Kraus 算子时，应保留 $K_0,K_1$ 及
$K_0^\dagger K_0+K_1^\dagger K_1=I$。
一般有限多 Kraus 情形保留全部 $K_{b\alpha}$ 与内部指标 $\alpha$，使用

$$
V\psi=\sum_{b,\alpha}\lvert b\rangle\otimes\lvert \alpha\rangle\otimes K_{b\alpha}\psi,
 \qquad \sum_{b,\alpha}K_{b\alpha}^\dagger K_{b\alpha}=I.
$$

标签仍然二元，附加指标留在内部上下文中，范数守恒由同一完备式得到。

## 5. 算子值三轴的整体纯性：主定理

#### 定义 5.1（完整二元关系块）

令 $R\succeq0$ 为 $\mathbb{C}^2\otimes\mathcal{K}$ 上的非零正迹类算子，$m=\operatorname{Tr} R>0$。
按同一 $\mathcal{K}$ 写

$$
R=\begin{pmatrix}A&C\\C^\dagger&B\end{pmatrix},\quad
 S=A+B,\quad X=C+C^\dagger,\quad Y=i(C-C^\dagger),\quad Z=A-B.
$$

则 $S=\operatorname{Tr}_2 R$，$\operatorname{Tr} S=m$，且

$$
\boxed{R=\tfrac12(I\otimes S+\sigma_x\otimes X+
 \sigma_y\otimes Y+\sigma_z\otimes Z).}
$$

有界块压缩保持迹类，因此这些关系算子、其平方及有限二元偏迹均良定义。
这一可逆分块是项目 V37/V51/V52 的既有结构。
$X,Y,Z$ 是 Hermitian 关系算子，不必为正，不能直接各自当概率态归一化。［[5](#ref-v37), [6](#ref-v51), [7](#ref-v52)］

<!-- v56-note:N4 -->

**编者注（Markdown 编者，N4）。** 上述块都是迹类理想中的有界压缩。迹类算子乘有界算子仍迹类，故这些自伴块的平方及有限乘积均迹类；$\operatorname{Tr}_2$ 是两个对角压缩之和，正且保迹。任意载体上的正迹类算子是紧算子，非零谱至多可数，谱展开在迹范数下收敛，总和为 $m$，且 $0\le R\le mI$。因此 $mR-R^2$ 正且迹类，有限 Pauli 分块无需交换不收敛的级数；正迹类迹的忠实性给迹零即零。该论证保留任意 Hilbert／迹类范围，并未以有限维截断代替原命题。

<!-- /v56-note -->

#### 定理 5.2（正锥中的算子球面与纯性）

定义

$$
\boxed{D_m=2mS-S^2-X^2-Y^2-Z^2.}
$$

则

$$
\boxed{D_m=2\operatorname{Tr}_2(mR-R^2)\succeq0.}
$$

而且下列条件等价：

$$
D_m=0\quad\Longleftrightarrow\quad \operatorname{Tr} D_m=0
 \quad\Longleftrightarrow\quad R=mP_\Psi
 \text{ 对某单位 }\Psi.
$$

特别地，$m=1$ 时整体纯态恰好满足

$$
\boxed{X^2+Y^2+Z^2=2S-S^2.}
$$

**证明。**

Pauli 迹正交性给

$$
\operatorname{Tr}_2R^2=\tfrac12(S^2+X^2+Y^2+Z^2),
$$

故得到等式。正迹类 $R$ 的每个特征值在 $[0,m]$ 内，因此 $mR-R^2\succeq0$，
其偏迹也正。
若 $\operatorname{Tr} D_m=0$，则正算子 $mR-R^2$ 迹零，必为零；非零特征值于是只能为 $m$。
由于总迹恰为 $m$，只能有一个这样的特征值。反向对秩一 $mP_\Psi$ 直接代入。
正迹类算子迹零当且仅当算子零，完成全部等价。

∎

$m=0$ 时正性只给 $R=0$，并无可归一的纯态。
当 $\dim\mathcal{K}=1$，$S=m$ 为数，本式准确成为 $x^2+y^2+z^2\le m^2$，
非零纯态为等号。一般情形的右侧是 $2mS-S^2$，不是 $S^2$。

#### 推论 5.3（纯性中的关系之关系）

归一正态 $R$ 纯时还满足

$$
\begin{aligned}
 \{S,X\}+i[Y,Z]&=2X,\\
 \{S,Y\}+i[Z,X]&=2Y,\\
 \{S,Z\}+i[X,Y]&=2Z.
 \end{aligned}
$$

**证明。**

展开 $R^2=R$。恒等 Pauli 分量给主定理的球面等式；三个 Pauli 分量依次给上述式子。
例如 $\sigma_y\sigma_z=i\sigma_x$ 与反序项合并为 $i[Y,Z]$。

∎

这些式子将归一化算子、三个关系轴以及轴间的非交换关系同时约束。
在正迹一前提下，主定理的单一算子球面已足以判纯；三条向量式随之成立。

#### 命题 5.4（近纯稳定界）

对归一正态 $R$，令 $D=D_1$、$\epsilon=\frac12\operatorname{Tr} D=1-\operatorname{Tr} R^2$。
则

$$
\inf_{\|\Psi\|=1}T(R,P_\Psi)=1-\lambda_{\max}(R)\le\epsilon.
$$

**证明。**

对任意纯态 $P_\Psi$，效果检验给
$T(R,P_\Psi)\ge1-\langle\Psi,R\Psi\rangle\ge1-\lambda_{\max}$。
取最大特征向量，其迹距离恰为 $1-\lambda_{\max}$。
又 $\operatorname{Tr} R^2=\sum_j\lambda_j^2\le\lambda_{\max}\sum_j\lambda_j=\lambda_{\max}$。

∎

<!-- v56-note:N5 -->

**编者注（Markdown 编者，N5）。** 近纯命题中的非零正紧算子确有最大特征值及单位特征向量。对该向量的纯投影，差算子在该方向和其正交补上分别有特征值 $\lambda_{\max}-1$ 及其余非负特征值，总绝对迹为 $2(1-\lambda_{\max})$。谱和的收敛来自迹类；不要求环境有限维。

<!-- /v56-note -->

#### 命题 5.5（混合的关系平方缺额）

给同一二元接口上的有限族归一正态 $R_i$ 和权重 $p_i\ge0$、$\sum_i p_i=1$。
记 $R=\sum_i p_iR_i$，则

$$
\boxed{D(R)=\sum_i p_iD(R_i)
 +2\sum_{i<j}p_ip_j\operatorname{Tr}_2[(R_i-R_j)^2].}
$$

**证明。**

非交换平方仍满足
$\sum_i p_iR_i^2-R^2=\sum_{i<j}p_ip_j(R_i-R_j)^2$。
将它代入 $D(R)=2\operatorname{Tr}_2(R-R^2)$。每个 Hermitian 差的平方为正，故第二项正。

∎

若 $D\ne0$，它又是内部 $\mathcal{K}$ 上的正迹类对象，可以保留其质量并归一为
$D/\operatorname{Tr} D$，再对其作同一二元分析。$D=0$ 用零标记。
这是描述层的递归：$R\mapsto D(R)$ 非线性，且 $D$ 本身不包含恢复 $R$ 的全部数据。

#### 命题 5.6（内部旋转协变）

对 $U\in SU(2)$ 和 $\mathcal{K}$ 上酉 $V$，令
$R'=(U\otimes V)R(U^\dagger\otimes V^\dagger)$。
若 $U\sigma_kU^\dagger=\sum_jO_{jk}\sigma_j$，则

$$
S'=VSV^\dagger,\qquad X'_j=\sum_kO_{jk}VX_kV^\dagger,\qquad
 D_m'=VD_mV^\dagger.
$$

**证明。**

Pauli 共轭给实正交 $O$。展开重构式即可；求平方和时用
$\sum_jO_{jk}O_{jl}=\delta_{kl}$，不需要假设各 $X_j$ 对易。

∎

## 6. 标量球面缺额是仍在本体内部的关系

<!-- v56-note:N6 -->

**编者注（Markdown 编者，N6）。** 此处使用诱导外积范数：$u\wedge v=(u\otimes v-v\otimes u)/\sqrt2$，相应平方范数为 Gram 行列式。若以未除 $\sqrt2$ 的反对称张量记外积，范数常数需相应换算。两侧约化态都有相同非零谱，且本节直接给 $\operatorname{Tr}\rho_2^2=\operatorname{Tr}S^2$；有限秩不超过二，任意 Hilbert 环境中这些迹均收敛。

<!-- /v56-note -->

#### 定理 6.1（纯整体的两侧纯度与外积）

设 $\Psi=\lvert 0\rangle\otimes u+\lvert 1\rangle\otimes v$ 为单位向量，
$R=P_\Psi$，$S=uu^\dagger+vv^\dagger$。
令 $p=\|u\|^2$、$q=\|v\|^2$、$c=\langle u,v\rangle$。
二元约化态为

$$
\rho_2=\operatorname{Tr}_\mathcal{K} R=\begin{pmatrix}p&\bar c\\c&q\end{pmatrix},
 \qquad r=(2\Re c,2\Im c,p-q).
$$

于是

$$
\boxed{1-\|r\|^2=4(pq-|c|^2)=4\|u\wedge v\|^2
 =2(1-\operatorname{Tr} S^2).}
$$

标量球面等号当且仅当 $u,v$ 线性相关，包含一个为零的情形。

**证明。**

偏迹给显示矩阵。$(p+q)^2-(p-q)^2-4|c|^2=4(pq-|c|^2)$。
外积的标准诱导范数给 $\|u\wedge v\|^2=pq-|c|^2$，
而 $\operatorname{Tr} S^2=p^2+q^2+2|c|^2$。
Cauchy–Schwarz 的等号条件完成判别。

∎

首个 Gram 缺额恒等式已见项目 V24 命题 3.4；这里将其续接到 v55 外积残差与两侧纯度。
整体纯性与当前局部球内读出同时成立，剩余关联仍在同一本体中。［[4](#ref-v24)］

对 $\Phi^+=(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$，

$$
S=I/2,\quad X=\sigma_x/2,\quad Y=-\sigma_y/2,\quad Z=\sigma_z/2.
$$

三个标量轴均为零，但

$$
X^2+Y^2+Z^2=3I/4=2S-S^2.
$$

所以完整算子三轴恰在纯性球面，当前标量接口却在球心。
项目早已用此例反对机械套用 $\sum X_j^2\preceq S^2$；本轮给出了正确的普遍右侧。
［[5](#ref-v37), [6](#ref-v51)］

在固定投影记录编码中，$u=P_0\Omega$、$v=P_1\Omega$ 正交，故
$1-\|r\|^2=4pq$。与之相对，支撑上的纯逻辑接口直接使用两个完整分支为基。
观察者局部的横向算子与全局分支间的横向算子不同，二者都属于本体。

## 7. 全局正性必须包含联合关系

#### 命题 7.1（算子球面及全部乘积正性仍不替代全局正性）

在 $\mathbb{C}^2\otimes\mathbb{C}^2$ 上令交换算子 $F(x\otimes y)=y\otimes x$，取 $R=F/2$。
则 $R$ Hermitian、$\operatorname{Tr} R=1$，其算子三轴满足 $D=0$，且全部乘积向量期望非负，
但 $R\not\succeq0$。

**证明。**

有

$$
F=\tfrac12(I\otimes I+\sigma_x\otimes\sigma_x+
 \sigma_y\otimes\sigma_y+\sigma_z\otimes\sigma_z).
$$

故 $S=I/2$、$X_j=\sigma_j/2$，直接代入给 $D=0$。
乘积向量满足
$\langle a\otimes b,R(a\otimes b)\rangle=|\langle a,b\rangle|^2/2\ge0$。
但反对称 Bell 向量为 $F$ 的 $-1$ 特征向量，所以 $R$ 有特征值 $-1/2$。

∎

甚至对每个局部方向 $n\in S^2$，条件块
$(S+n\cdot X)/2=(I+n\cdot\sigma)/4$ 都正。
这说明主定理的 $R\succeq0$ 前件不可删除。乘积效果可以线性张成联合矩阵空间，
仍不意味着仅检查这些效果的非负响应就已经检查了完整正锥；联合纠缠方向是另一类正性检验。

在假设 195.2 的正实际质量分支及已给共同切口上，项目 Quantum IV 定理 196.1 使用
实际效果的实关系一致性 RC、各实际列的非负性、每个完整标签行的归一化，
以及各块实际秩一方向的稠密性，得到可测正迹一块密度场，且其在共同零集以外唯一。
稠密性需要所声明的整个块方向，不能用仅有局部乘积方向代替。
共同实际切口、历史映射和实际核仍是来源前提，粗 Born 行与记录质量也未由此自动选出。
本轮这个反例说明为何“关系也在整体中”应包括联合正性。［[8](#ref-qiv)］

## 8. 整体酉性、内部漏出与随动观察切口

#### 定理 8.1（固定二元接口的结果与漏出守恒）

令 $J_0,J_1:\mathbb{C}^2\to\mathcal{H}$ 等距，$\Pi_i=J_iJ_i^\dagger$，$U$ 为整体酉。
定义

$$
B=J_1^\dagger UJ_0,\qquad L=(I-\Pi_1)UJ_0.
$$

则

$$
\boxed{B^\dagger B+L^\dagger L=I_2,\qquad
 \|B\chi\|^2+\|L\chi\|^2=\|\chi\|^2.}
$$

$B$ 为二元酉门当且仅当 $U\operatorname{Ran} J_0=\operatorname{Ran} J_1$。

**证明。**

插入 $\Pi_1+(I-\Pi_1)=I$ 即得平方守恒。
$B^\dagger B=I$ 等价于 $L=0$，即旧二维像被送入新二维像；两者维数相同，故包含即相等。

∎

漏出仍是整体内部振幅，可以继续二分。只知道某一个实际向量被送入新接口，
不足以推出整个二元态族上的 $L=0$。
若同时运输 $\Omega'=U\Omega$ 与 $P'=UPU^\dagger$，则非退化规范下

$$
J_{\Omega',P'}=UJ_{\Omega,P},\qquad p'=p,\quad q'=q.
$$

这是参考与被参考部分共同内生的精确协变形式。

<!-- v56-note:N7 -->

**编者注（Markdown 编者，N7）。** 微分命题中 $\rho(t)$ 按本文密度态约定为正且迹一，并可微；所有等式按导数存在的时刻理解，$\hbar>0$。有限维保证循环迹及块范数运算无无界定义域问题。$p=0$ 或 $p=1$ 时密度态支撑落在一个投影块内，非对角期望为零，故变化率界的两个端点也包括在内。

<!-- /v56-note -->

#### 定理 8.2（内部切口的相对变化率）

在有限维中，设 $H(t)=H(t)^\dagger$、$\hbar>0$、$\dot\rho=-i[H,\rho]/\hbar$，
$P(t)$ 为可微正交投影，
$p(t)=\operatorname{Tr}(\rho(t)P(t))$。定义

$$
\mathcal D_tP=\dot P+\frac{i}{\hbar}[H,P].
$$

则

$$
\boxed{\dot p=\operatorname{Tr}(\rho\mathcal D_tP),\qquad
 |\dot p|\le2\|\mathcal D_tP\|\sqrt{p(1-p)}.}
$$

若 $U(t)$ 酉、$P(t)=U(t)P(0)U(t)^\dagger$ 且 $i\hbar\dot U=HU$，则 $\mathcal D_tP=0$。
若 $P$ 固定，则 $\|\mathcal D_tP\|=\|(I-P)HP\|/\hbar$。

**证明。**

对 $p$ 求导并循环移项得首式。
对 $P^2=P$ 求导，得到 $P\dot PP=0$ 与 $(I-P)\dot P(I-P)=0$；
交换子项也纯非对角，所以 $\mathcal D_tP$ 为 Hermitian 非对角块算子。
纯态分解 $\psi=P\psi+(I-P)\psi$ 给

$$
|\langle\psi,\mathcal D_tP\psi\rangle|
\le2\|\mathcal D_tP\|\|P\psi\|\|(I-P)\psi\|
$$

。
混态谱分解后用 Cauchy–Schwarz，得同一界。
随动投影的导数为 $-i[H,P]/\hbar$，两项抵消。
固定投影时交换子的两个非对角块为 $\pm(I-P)HP$ 及其伴随，给算子范数式。

∎

这将当前读出变化率归于相对切口及内部耦合。
给定 $H$ 与参数 $t$ 是本定理的前提；事件计数时钟、物理时间和滤波参数尚不能因此互换。
项目 $\Omega$ 定义 1.2 对这些量也作了明确区分。［[2](#ref-omega)］

## 9. 完整递归：算子、记录、质量与非交换关系

#### 定理 9.1（有限算子三轴递归）

给有限维 $d\ge1$，令 $n=\lceil\log_2d\rceil$，将 $\mathbb{C}^d$ 固定等距嵌入
$(\mathbb{C}^2)^{\otimes n}$。对编码态逐因子作完整 $S,X,Y,Z$ 分块，等价于

$$
R=2^{-n}\sum_{\alpha\in\{0,x,y,z\}^n}
 r_\alpha\,\sigma_{\alpha_1}\otimes\cdots\otimes\sigma_{\alpha_n},\quad
 r_\alpha=\operatorname{Tr}(R\sigma_{\alpha_1}\otimes\cdots\otimes\sigma_{\alpha_n}).
$$

它唯一恢复完整态；$r_{0\cdots0}=1$，正性施加在重构的完整 $R$ 上。

**证明。**

Pauli 张量基的迹正交性给展开与唯一性。$d=1$ 时取零个因子、空张量及唯一标量态。

∎

这一递归已见 V37/V51/V52。本轮纯性约束可在每个被明确保留为正态的二元关系块应用；
对仅为 Hermitian 系数的 $X,Y,Z$ 继续线性分块时，不把它们误称为密度态。
只保留每个前缀节点的标量条件三轴仍可遗漏相干：Bell $\Phi^\pm$ 在计算基前缀上的
全部质量与下一位条件标量态相同，但根的交叉算子块相反。［[5](#ref-v37), [6](#ref-v51), [7](#ref-v52)］

<!-- v56-note:N8 -->

**编者注（Markdown 编者，N8）。** 上一定理的 $\sigma_0=I_2$。本记录树的每个 $A_{wb}$ 为同一工作 Hilbert 空间上的有界算子；完备式也给 $\|A_{wb}\|\le1$。对每个有限层仅作有限和，$p_\varnothing=\operatorname{Tr}\rho=1$；沿正质量路径的乘积从根开始，零节点不定义条件比。这里不主张无限树的相干极限或无条件的可执行取得。

<!-- /v56-note -->

#### 定理 9.2（有限相干记录树与质量递乘）

在同一内部工作空间上，每个节点 $w$ 给二元算子
$A_{w0}^\dagger A_{w0}+A_{w1}^\dagger A_{w1}=I$。
设 $K_\varnothing=I$、$K_{wb}=A_{wb}K_w$。则每层

$$
\sum_{|w|=n}K_w^\dagger K_w=I,\qquad
 V_n\psi=\sum_{|w|=n}\lvert w\rangle\otimes K_w\psi
$$

为等距表示。对密度态 $\rho$ 定义 $p_w=\operatorname{Tr}(K_w\rho K_w^\dagger)$，则

$$
p_w=p_{w0}+p_{w1},\qquad
 q(b\mid w)=p_{wb}/p_w\quad(p_w>0),
$$

并且沿正质量路径 $p_w$ 等于各层条件质量之积。

**证明。**

逐父节点使用二元完备性，归纳得第一式；正交标签给等距。
取迹给加法式，条件比值沿路径约消给乘法式。

∎

零质量节点的全部后继也零，不定义其归一条件态。
整体中的字标签是正交记录，但压回工作空间的效果 $F_w=K_w^\dagger K_w$ 一般不对易。
例如首层 $A_0=I/\sqrt2,A_1=H_2/\sqrt2$，其中 $H_2$ 是 Hadamard；第二层均读 $Z$。
则 $F_{00}=P_{z+}/2$、$F_{10}=P_{x+}/2$ 不对易。
因此记录事件的 Boolean 结构不能未经检查压成原空间上同一组投影补集。

每个有限层的经典前缀质量相容，不等于带工作空间的全部相干前缀态在后续操作后保持不变。
若采用全部时刻的加权直和历史向量，需要另给可求和时间权重；
一般无限延拓须声明相容嵌入、完成空间与拓扑。
V51 已给出加权正常纯历史以及局部极限可能混合的两类明确结果；本轮不省略这些条件。
［[6](#ref-v51)］

## 10. 观察商中的互补与内部关系返回

#### 定理 10.1（二元事件下降到观察商的条件）

设 $q:\mathscr X\to B$ 满射，$A\subseteq\mathscr X$。
则下列条件等价：

$$
A=q^{-1}(q(A));\qquad
 q(A)\cap q(A^c)=\varnothing;\qquad
 q(A^c)=B\setminus q(A).
$$

它们也等价于存在 $\widehat A\subseteq B$ 使 $A=q^{-1}(\widehat A)$。

**证明。**

第一式表示每个与 $A$ 相交的商纤维都包含于 $A$，恰等价于第二式。
满射使 $q(A)\cup q(A^c)=B$，故第二、三式等价。
取 $\widehat A=q(A)$ 得一个方向；逆方向由同纤维成员具有同一 $q$ 值得到。

∎

所以整体上的每个事件都有补事件，而某个当前观察商只对饱和事件保留可判定的互补。
这是一条基础集合论连接，不把它冒称为已在 $\Omega$ 稿中定位的现成命题。

<!-- v56-note:N9 -->

**编者注（Markdown 编者，N9）。** “可判定的互补”在本节指集合事件在观察纤维上恒定、因而下降为商上的事件；未声明可计算判定算法，也未另赋予商集可测结构。实际判读或可测取得需要相应接口。

<!-- /v56-note -->

项目 $\Omega$ 命题 32.2 给了具体量子接口：在同一已达记录纤维、只读第一块五模式、
所声明完整合法未来菜单及假设 30.2 下，局部门菜单的商恰为第一块约化态；
加入指定耦合门后的商恰为联合密度态。
这不是一次末读取得未知态；如果原菜单已经允许完备联合乘积读出，也不能再声称只有耦合门
才使联合态可识别。［[2](#ref-omega)］

内部关系返回的一个直接例子来自项目 Observer 定义 9.3。
同一内部 CNOT 将 $\lvert \pm\rangle\lvert 0\rangle$ 分别送到 $\Phi^\pm$；当前第一位状态都为 $I/2$。
再作用同一个 CNOT，分别回到 $\lvert \pm\rangle\lvert 0\rangle$，第一位 $X$ 读出恢复为 $\pm1$。
如果每步改成独立新初始化的内部槽，得到的是不同的过程。
因此非当前读口并未离开本体，它保留的关系可以在合法未来重新成为可读差异。［[3](#ref-observer)］

## 11. 同一个本体态与固定无损压缩的量词

#### 命题 11.1（唯一总态的所有内部条件分支可张成全空间）

固定单位 $\Omega$。全部 $P\Omega\ne0$ 的归一化条件分支的线性包为 $\mathcal{H}$。

**证明。**

对任意单位 $e\perp\Omega$，取 $v=(\Omega+e)/\sqrt2$，则
$P_v\Omega=v/\sqrt2$。条件分支中有 $\Omega$ 和 $v$，故其线性包包含
$e=\sqrt2v-\Omega$，从而包含整个 $\Omega^\perp$ 与 $\Omega$。

∎

这与每个切口的支撑至多二维同时成立。
若实际只给一个投影菜单，条件态族应限于该菜单，而不能擅用全部 $P$。

#### 定理 11.2（固定可恢复纯态族的载体下界）

在有限维中，若固定 CPTP 编码 $\mathcal E$ 到 $\mathbb{C}^m$ 与固定 CPTP 解码 $\mathcal R$
恢复纯态族 $\mathcal F$ 的每个成员，则

$$
m\ge\dim\operatorname{span}\{\psi:P_\psi\in\mathcal F\}.
$$

**证明。**

取族中 $r$ 个线性无关向量 $\psi_i$。将 $\mathcal E(P_{\psi_i})$ 谱分解，
纯输出的极端性保证其中任一正权重谱向量 $v_i$ 都满足
$\mathcal R(P_{v_i})=P_{\psi_i}$。
写解码器 Kraus 等距 $Wv=\sum_\alpha K_\alpha v\otimes\lvert \alpha\rangle$，纯输出给
$Wv_i=\psi_i\otimes\eta_i$，$\|\eta_i\|=1$。
若这些乘积向量线性相关，在第一因子上逐个作用于 $\psi_i$ 的对偶线性泛函，就使每个系数为零。
故它们和 $v_i$ 均线性无关，得到 $m\ge r$。

∎

这一强下界已见 V52 定理 8.3。结合上一命题，即使只给一个本体态，允许全部内部切口时，
其条件态族也不一般地拥有同一个可恢复 qubit 编码。
逐切口的 $J$、标签与相位若保留在解码端，就须计入完整表示数据。［[7](#ref-v52)］

## 12. 接回五模式与本轮总定理

对每个真正二元接口，项目已有固定 $J_F:\mathbb{C}^2\to\mathbb{C}^5$，$J_F^\dagger J_F=I$。
完整上下文的编码使用

$$
\widehat R=(J_F\otimes I_\mathcal{K})R(J_F^\dagger\otimes I_\mathcal{K}).
$$

它保留非零谱、纯性、完整相干与质量；逆为在编码像上的伴随压缩。
二元酉门的编码仍为
$\widetilde U=J_FUJ_F^\dagger+(I_5-J_FJ_F^\dagger)$。
这保留了五模式格式，同时保留 $\mathcal{K}$ 中所有内部关系。
归一化由单位效果与 $\operatorname{Tr} S=m$ 承担；不能凭模式名称把 $F[\mathrm{null}]$ 当成总质量。
［[5](#ref-v37), [7](#ref-v52)］

#### 定理 12.1（唯一本体的普遍内部二分闭合）

在所给复 Hilbert 总态模型内：

1. 任意单位总态与任意内部正交切口，都有至多二维的相干支撑；非退化时有纯态三轴与内部酉扩张。
1. 完整状态依赖图册由逻辑二元态和内部嵌入组成；固定记录等距则对全部输入共同保真。
1. 完整算子三轴在正锥中满足 $\sum X_j^2\preceq2mS-S^2$；非零整体纯当且仅当等号成立。
1. 局部标量球面缺额可由内部外积平方和另一侧约化纯度精确表示，不需要第二个外部本体。
1. 所有保留的算子、记录与分支可以继续二元分解；质量、相位和联合正性在递归中一并传递。
1. 整体酉性在固定接口上分成可见输出与内部漏出的平方守恒；接口整体随动时保持关系质量。

**证明。**

分别应用第 2、4、5、6、9、8 节的定理。每条结论保持其正性、归一化、维数或定义域前提。

∎

这给“没有例外”一个明确全称语义：对模型内每个态与每个内部切口，使用同一完备二元格式。
标量三轴描述二元接口；完整高维关系由其内嵌方向或算子值轴保留。
它不把三个普通实数与三个携带全部内部自由度的算子混为同一信息容量。

项目 $\Omega$ 假设 1.3 已明确把复 Hilbert、张量复合、PSD 迹一态、Born 迹配对与 CP 仪器
列为附加量子表示。本文是在这个结构及其明确推广内证明普遍闭合；
没有把既有量子表示重新说成由静态性独自导出。
若要继续减少公理，实际共同切口与 RC 的原生来源仍是 Quantum IV 指出的具体桥梁。
观察者为何选择某个 $P$、$\mathcal{A}$、内部对齐和实际控制菜单，也需要来源来确定。［[2](#ref-omega), [8](#ref-qiv)］

全文数学采用符号推导，没有执行数学程序、数值近似、CAS、候选枚举、Lean 或门搜索。
工具只用于公开来源核对、文字与身份账目、文稿编译和版式检查。

## 固定来源与阅读范围

<a id="ref-head"></a>

**[1]**

the-omega-institute/trureturing，
[固定提交 74d3fbdb76<wbr>8819e31f73<wbr>6d1e2e5686<wbr>e3f03f6a12](https://github.com/the-omega-institute/trureturing/commit/74d3fbdb768819e31f736d1e2e5686e3f03f6a12)。
上一轮核验快照；本轮活动 HEAD 请求 403，未取得后续版本。

<a id="ref-omega"></a>

**[2]**

[AURIC $\Omega$ Static Compatibility–Fiber Theory](https://github.com/the-omega-institute/trureturing/blob/74d3fbdb768819e31f736d1e2e5686e3f03f6a12/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。
本轮来源阅读第 1、7、32 节相应段落；主文核读定义 1.1–1.2、假设 1.3、命题 32.2 的设置与证明。
实际控制密度的上游证明未在本轮重新认证。

<a id="ref-observer"></a>

**[3]**

[AURIC Observer Internal Three-Axis Geometry and Predictive Interface](https://github.com/the-omega-institute/trureturing/blob/74d3fbdb768819e31f736d1e2e5686e3f03f6a12/docs/develop/theory/AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md)。
来源阅读 1–180、395–507 行；主文核读定义 9.3 的同一内部环境返回例。

<a id="ref-v24"></a>

**[4]**

[AURIC V24：两基态、三通道、相位手性与递归平方律](https://github.com/the-omega-institute/trureturing/blob/74d3fbdb768819e31f736d1e2e5686e3f03f6a12/docs/develop/theory/AURIC_TWO_BASIS_STATES_THREE_CHANNELS_PHASE_CHIRALITY_AND_RECURSIVE_SQUARE_LAW_V24.md)。
本轮核读命题 3.3–3.4；纯整体的局部 Gram 缺额为已有结果。

<a id="ref-v37"></a>

**[5]**

[AURIC V37：二元关系、酉表示与黄金门普适性](https://github.com/the-omega-institute/trureturing/blob/74d3fbdb768819e31f736d1e2e5686e3f03f6a12/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)。
本轮核读第 6 节完整算子值分块、递归、门块归一及联合 Gram 正性；第 3–4 节固定编码沿用前轮核验。

<a id="ref-v51"></a>

**[6]**

[AURIC V51：约束递归、纯态对偶与内生静态历史](https://github.com/the-omega-institute/trureturing/blob/74d3fbdb768819e31f736d1e2e5686e3f03f6a12/docs/develop/theory/AURIC_CONSTRAINT_RECURSION_PURE_STATE_DUALITY_AND_ENDOGENOUS_STATIC_HISTORY_V51.md)。
本轮核读第 9 节；来源复核第 11–12 节历史与极限的指定范围。

<a id="ref-v52"></a>

**[7]**

[AURIC V52：纯态商几何、二次关系生成与无损递归](https://github.com/the-omega-institute/trureturing/blob/74d3fbdb768819e31f736d1e2e5686e3f03f6a12/docs/develop/theory/AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)。
本轮核读第 7–8 节的算子分块、零 Schur 余量、五模式及固定恢复下界；树图册由来源与几何审读复核。

<a id="ref-qiv"></a>

**[8]**

[AURIC Quantum Principles and Coherent Reconstruction, Continuation IV](https://github.com/the-omega-institute/trureturing/blob/74d3fbdb768819e31f736d1e2e5686e3f03f6a12/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md)。
沿用同 SHA 前轮第 195–200 节有界阅读；RC、共同切口、实际列及块内稠密前提均保留。

<a id="ref-rro"></a>

**[9]**

[Recursive Relational Observation: Fibonacci Native Terminal Certification](https://github.com/the-omega-institute/trureturing/blob/74d3fbdb768819e31f736d1e2e5686e3f03f6a12/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FIBONACCI_NATIVE_TERMINAL_CERTIFICATION.md)。
本轮来源阅读 900–997 行，特别是约定 17.2（第 17 节文献对应表）的有限代数归属与实际效果空间边界。

<a id="ref-klv"></a>

**[10]**

E. Knill, R. Laflamme, L. Viola,
*Theory of Quantum Error Correction for General Noise*,
Phys. Rev. Lett. 84, 2525–2528 (2000), DOI:10.1103/PhysRevLett.84.2525。
[作者预印本 quant-ph/9908066](https://arxiv.org/pdf/quant-ph/9908066)，
核读 Theorem 5 与 Subsystems 段；不引申为全部噪声编码结论的本轮认证。

<a id="ref-zanardi"></a>

**[11]**

P. Zanardi, D. A. Lidar, S. Lloyd,
*Quantum Tensor Product Structures are Observable Induced*,
Phys. Rev. Lett. 92, 060402 (2004), DOI:10.1103/PhysRevLett.92.060402。
[作者预印本 quant-ph/0308043](https://arxiv.org/pdf/quant-ph/0308043)，
核读 General framework、Proposition 1、irreducible representations、nested subalgebras 及 TPS morphing 对应段。
