<a id="auric-v22"></a>

# 相对门历史与观察商

**AURIC 的共同背景消去、关系核与递归闭合**

**定义、定理与完整纸面证明**

**v22.0　 2026 年 10 月 30 日　 Asia/Singapore**

<a id="sec-abstract"></a>

## 摘要

若待测态与测量基底分别由门历史 $U,V$ 生成，其读出可写为相对门 $R=V^\dagger U$ 对种子态的作用。本文证明共同左酉或完整等距输运可严格消去，并以轨道商给出这一消去的普遍性质；共同初态则通常仍通过状态泛函参与赋值。进一步区分射线与基底的双商、当前读出纤维商、正核零范数商和投影的线性商，证明它们保留的信息与递归条件不同。固定绝对后接门下降到相对商，当且仅当其相对差位于门群中心；协变控制或内生相对增量可恢复递归闭合。原生 AURIC 门给出两项精确结果：两个可达历史当前模式概率相同，却被同一后继门分离；两组历史的全部两两投影概率相同，却分别具有 $\varphi^{-4}\omega$ 和 $\varphi^{-4}\bar\omega$ 的三历史 Bargmann 量。两两模长与足够的闭路相位可重构完整相干关系核，进而在酉同构意义下重构最小 Hilbert 实现。最新项目的四能级矩阵乘积态见证显示，共同虚参考可从迹配对消去，同时二字完整振幅仍唯一恢复整个边界矩阵。本文保留复 Hilbert、Born 赋值、同源性、程序及实际读出条件，不把坐标消去解释为全部物理状态信息消失。

**结果身份。** 本文给出条件明确的纸面证明，不运行数学数值程序、CAS、门枚举或 Lean。群作用、Gram 核重构、Bargmann 不变量与 MPS 表示变换均有既有背景；本文的推进是它们在 AURIC 相对门、原生精确反例、递归下降与最新源码接口上的具体联结，不作经典结果的原创优先权声明。项目报告的机器证明状态与本文实际复核的纸面内容分别归属。

> **转换说明（编者）。** 本文完整转换用户提供的 v22.0 XeLaTeX 稿件。陈述沿用各节共享编号；自动编号公式沿用全局 (1)–(11)，其余显示公式不编号。相位距离的两行按源稿拆为显示公式：首行无编号，末行标 (5)。排版宏已展开；字体、分页与页眉由 Markdown 排版替代，目录与引用使用显式锚点。项目快照、历史核对和机器证明状态的报告保留原作者归属；本次转换不构成这些报告或数学结论的独立认证。未作实质数学修订。

## 目录

1. [固定快照与“商”的对象](#sec-1)
2. [两套门历史的相对化与种子依赖](#sec-2)
3. [共同输运的轨道商与递归下降](#sec-3)
4. [完整等距消去、投影商与记录](#sec-4)
5. [基底与射线的双商，以及变分的精确位置](#sec-5)
6. [以相干关系核取代绝对表示](#sec-6)
7. [原生黄金门：两两概率相同，三历史相位不同](#sec-7)
8. [只有对未来闭合的观察商才能继续预测](#sec-8)
9. [基底也不确定时：把程序纳入共同来源](#sec-9)
10. [最新项目的 MPS 实例：约去虚参考，保留边界](#sec-10)
11. [本轮得到的正式结构与尚未消去的前件](#sec-11)

[附录 A. 术语、约定与复核范围](#sec-A)

[文献与项目来源](#sec-bibliography)

<a id="sec-1"></a>

## 1. 固定快照与“商”的对象

本轮研究分支 `dev` 固定于

`f76bcb791c34c35b622417c0d446251425e9faaf`。

提交时间为 2026-10-30 04:39:58（新加坡），即 2026-10-29 20:39:58 UTC；合并 PR #23807，主题为四物理能级的 $U(1)$ 对称可注入矩阵乘积态。相对前稿 v21 的 `ce2773bd…`，有 69 个提交、220 个全仓变更路径；理论目录由 1021 增至 1022 个文件，四条路径变化。固定来源见 [[1](#ref-snapshot)]。

四条理论变化是：新增 CDSO 容量交叉卷；修改 CDSO 容量卷、FIB 合法边负载与可观测依赖卷，以及递归关系观察的联合核与最小预测核心卷。最后一卷新增第 15–23 节，本轮直接使用其任务商与完整未来律的区别、同源配对要求和只读来源的记录增长障碍 [[2](#ref-jointkernel)]。新合并 MPS 见证说明位于 Problem 与 Blueprint，形式化模块位于 `D5/S3/Quantum/SpinChains`；第 [10](#sec-mps) 节自足证明其与参考框商的联系。

本轮定向核对十九个当前 Markdown 快照与三个旧快照的 Git blob。此前相对商卷含用户文本转录，量子重构卷也明示复数正核等输入假设；收入仓库不构成新的独立证明。当前项目已有的响应商、未来同余和正核构造分别见 [[3](#ref-omega), [4](#ref-reconstruction), [5](#ref-quotients)]。

<a id="statement-1-1"></a>

<a id="def-premises"></a>

#### 定义 1.1（共同工作前件）

除特别声明的核完成外，使用有限维复 Hilbert 空间 $H=\mathbb{C} ^d$，$d\ge2$，右侧算子最先作用。固定带标签秩一 PVM
$\Pi_s=\lvert s\rangle \langle s\rvert$、种子密度矩阵 $\rho_0$，以及明确合法的门菜单。纯种子写作 $\rho_0=\lvert \psi_0\rangle \langle \psi_0\rvert$。Born 规则、复内积、正性、同源制备和保留哪些记录是本稿使用的前件。

“态由门序列生成”总需连同种子、作用地址与求值规则。固定有限字母表的有限字至多可数，不能精确覆盖 $d\ge2$ 的全部纯态；稠密逼近、连续参数及无限极限须另行声明。酉门作用纯种子仍给纯态；混态需要包含净化或指定遗忘操作。

| 对象 | 被识别的差异 | 必须检验的条件 |
| --- | --- | --- |
| 共同参考框轨道商 | 同时左作用的酉参考框 | 种子、读口与控制的相对关系仍保留 |
| 当前响应纤维商 | 当前查询族无法区分的状态 | 后继操作能否下降到商 |
| 相干核零范数商 | 所有交叉内积都为零的线性冗余 | 复正核与有界／等距递归 |
| 投影的线性商 | $\ker P$ 中的向量分量 | 仅描述该投影的未归一化输出 |
| 矩阵去相干的商 | 被删掉的非对角方向 | 一般只是向量空间商，非代数商 |

参考框可以作为物理量子系统，属于既有量子参考框研究的主题 [[8](#ref-qrf)]。本文以下定理是有限维接口上的自足论证，不把它们冒认为该文的原定理。

<a id="sec-2"></a>

## 2. 两套门历史的相对化与种子依赖

<a id="statement-2-1"></a>

<a id="def-relative"></a>

#### 定义 2.1（态历史、基底历史及相对门）

令 $U,V$ 为同一载体上的酉门字求值。待测态与完整基底为

$$
\rho_U=U\rho_0U^\dagger,\qquad
P_s(V)=V\Pi_sV^\dagger.
$$

定义相对门

$$
R(U,V)=V^\dagger U.
$$

一条基底射线 $V\psi_0$ 与整套基底 $\{V\lvert s\rangle \}_s$ 是不同对象。

<a id="statement-2-2"></a>

<a id="thm-relative"></a>

#### 定理 2.2（读出的相对门公式）

在上述前件下，

<a id="equation-1"></a>

<a id="eq-relative"></a>

$$
p_s(U,V;\rho_0)
=\operatorname{Tr} [P_s(V)\rho_U]
=\operatorname{Tr} [\Pi_sR\rho_0R^\dagger].
\tag{1}
$$

纯种子时 $p_s=|\langle s\rvert R\lvert \psi_0\rangle |^2$。若只比较两条同种子射线 $U\Omega,V\Omega$，其转移概率为

<a id="equation-2"></a>

<a id="eq-seedoverlap"></a>

$$
q_\Omega(U,V)=|\langle\Omega,V^\dagger U\Omega\rangle|^2.
\tag{2}
$$

**证明。**

将定义代入迹，并循环移动 $V$，得到
$\operatorname{Tr} (V\Pi_sV^\dagger U\rho_0U^\dagger)= \operatorname{Tr} (\Pi_sV^\dagger U\rho_0U^\dagger V)$。
纯态投影的迹等于内积模平方，得到其余两式。

∎

相对门取代了两套绝对历史，但式 [(1)](#eq-relative) 保留 $\rho_0$，式 [(2)](#eq-seedoverlap) 保留状态泛函
$\omega_\Omega(A)=\langle\Omega,A\Omega\rangle$。向量不能作为普通非零数从内积两侧相除。

<a id="statement-2-3"></a>

<a id="thm-seed"></a>

#### 定理 2.3（种子独立的精确判据）

对于固定效果 $0\le E\le I$，$\operatorname{Tr} (\rho E)$ 对全部密度态 $\rho$ 为常数，当且仅当 $E=cI$。对于酉 $R$，

$$
f_R(\Omega)=|\langle\Omega,R\Omega\rangle|^2
$$

在全部单位向量上为常数，当且仅当 $R=e^{i\theta}I$，此时常数为一。

**证明。**

第一条中，对基向量取期望给全部对角元为 $c$；对
$(e_j+e_k)/\sqrt2$ 和 $(e_j+ie_k)/\sqrt2$ 取期望，迫使非对角元实部与虚部均零，故 $E=cI$。反向显然。

第二条中，酉矩阵本征向量的 $f_R$ 均为一，故常数只能为一。取任意两个正交本征向量的等幅叠加，得到
$|(\lambda_j+\lambda_k)/2|=1$。两个单位复数的平均模为一要求二者相同，故全部本征值相同，酉可对角化性给标量相位。反向直接代入。

∎

若来源仅限于集合 $\mathcal S$，正确的种子无关条件是
$\operatorname{Tr} [(\rho-\sigma)E]=0$ 对全部 $\rho,\sigma\in\mathcal S$ 成立。
“实际种子未知”不自动等于“全部种子给相同结果”，也不自动供应均匀先验。

<a id="statement-2-4"></a>

<a id="prop-calibration"></a>

#### 命题 2.4（独立生成的射线不自动形成测量基底）

给 $d$ 个单位向量 $\beta_s=V_s\Omega$，它们组成完整正交基，当且仅当

$$
\langle\Omega,V_s^\dagger V_t\Omega\rangle=\delta_{st}.
$$

不存在两个固定酉 $V_1,V_2$，能对每个未知单位种子 $\Omega$ 都生成互相正交的两条射线。

**证明。**

第一条就是 $d$ 个向量的 Gram 矩阵为 $I_d$；这也等价于它们的秩一投影之和为 $I_d$。第二条若成立，就有
$\langle\Omega,V_1^\dagger V_2\Omega\rangle=0$ 对全部 $\Omega$ 成立。取相对酉的本征向量，内积却为非零单位本征值，矛盾。

∎

因此“基底也由门生成”可以成立，但需供给正交校准关系。整套 $V\lvert s\rangle$ 自动继承标准基的正交性；任意独立选择的 $V_s\Omega$ 则没有这种自动保证。

<a id="sec-3"></a>

## 3. 共同输运的轨道商与递归下降

<a id="statement-3-1"></a>

#### 定义 3.1（门群与共同左作用）

令 $G\le\operatorname{U} (d)$ 为声明的门群。对有限门字，先用求值映射得到实际酉；只有已经供应逆元或证明逆元能由正字实现，才能将其像视为群。定义
$W\cdot(U,V)=(WU,WV)$。

<a id="statement-3-2"></a>

<a id="thm-orbit"></a>

#### 定理 3.2（相对门完整分类共同参考框）

映射

$$
[(U,V)]\longmapsto V^\dagger U
$$

给出轨道商双射

<a id="equation-3"></a>

<a id="eq-orbit"></a>

$$
\boxed{G\backslash(G\times G)\cong G.}
\tag{3}
$$

在自然拓扑下它也是同胚。共同后接的 $W$ 严格消去：
$(WV)^\dagger(WU)=V^\dagger U$。

**证明。**

最后一式给出不变性。任意 $R\in G$ 来自 $(R,I)$，故满射。
若 $V^\dagger U=V'^\dagger U'$，取 $W=V'V^\dagger$，则
$WV=V'$、$WU=U'$，故同一相对门恰是同一轨道。公式及逆映射
$R\mapsto[(R,I)]$ 连续，得拓扑结论。

∎

这是轨道空间的结论，并未声称非交换群中的对角子群正规、逐项乘法自动下降为商群乘法。后续递归要另作检验。

<a id="statement-3-3"></a>

<a id="prop-right"></a>

#### 命题 3.3（共同过去通常留下共轭）

若两历史共同右乘 $W$，即 $U'=UW,V'=VW$，则

$$
R'=W^\dagger RW.
$$

两条同种子射线的重叠变为
$|\langle W\Omega,RW\Omega\rangle|^2$，共同过去可转移到种子，却一般没有消失。

**证明。**

直接相乘即得。反例取 $U=Z,V=I,\Omega=\lvert 0\rangle$，原重叠为一。共同先行 Hadamard 门后，二态为 $\lvert -\rangle$、$\lvert +\rangle$，重叠为零。

∎

对完整基底，右乘 $W$ 还改变其参考列。只要求 $W\psi_0$ 与 $\psi_0$ 同射线，不足以保证全部带标签概率保持；读口须同时稳定或一起协变。

<a id="statement-3-4"></a>

<a id="thm-descent"></a>

#### 定理 3.4（固定绝对后接门的商上递归判据）

给 $A,B\in G$，按
$(U,V)\mapsto(AU,BV)$ 更新。其相对输出为

$$
R'=V^\dagger(B^\dagger A)V R.
$$

这一输出对同一 $R$ 的所有代表无关，当且仅当

<a id="equation-4"></a>

<a id="eq-center"></a>

$$
\boxed{B^\dagger A\in Z(G).}
\tag{4}
$$

全群 $G=\operatorname{U} (d)$ 时，中心是标量相位。

**证明。**

乘法给第一式。令 $C=B^\dagger A$。若 $C$ 在中心，$V^\dagger CV=C$，所以 $R'=CR$。反之考察所有 $R=I$ 的代表 $(V,V)$；输出独立于 $V$ 要求 $V^\dagger CV=C$ 对全部 $V\in G$ 成立，正是中心条件。

∎

例如取 $A=Z,B=I$。$(I,I)$ 与 $(H,H)$ 原来都给 $R=I$，更新后却分别给 $Z$ 与 $HZH=X$，用 $\lvert 0\rangle$ 和标准读口即可区分。因此删去共同框架后，不能无说明地继续调用原来固定的绝对门。

有两种明确的修复。共同换框架时，把控制菜单也协变：
$A\mapsto WAW^\dagger,B\mapsto WBW^\dagger$；或保留内生相对增量
$D=V^\dagger B^\dagger AV$，使 $R'=DR$。若接口直接供应右侧增量
$U'=Ua,V'=Vb$，则

$$
R'=b^\dagger Ra
$$

自动闭合；这只是声明的参考接口乘法，不能悄悄改称物理最先施加的门。

<a id="statement-3-5"></a>

#### 命题 3.5（原生黄金字的相对编译）

在同一合法载体上，若每个原生地址门满足 $K_a^{10}=I$，则全部有限正字的像构成群。长度为 $m,n$ 的两个已知字 $U,V$，其相对门 $V^\dagger U$ 可由至多 $m+9n$ 次正向原生调用实现。

**证明。**

每个逆门为 $K_a^9$。按相反次序替换 $V$ 中的各门，得到 $V^\dagger$，再接到 $U$ 的输出；调用数相加即得。共同左因子若已声明为同一个完整酉，可先代数消去。

∎

这是可实现上界，不是最短字证明。若每门另推动真实记录时钟，完整操作可能是 $S\otimes K_a$，它的十次幂并不为单位；必须在完整载体上检查消去。已知程序的相干控制也与任意未知黑箱加控制不同。

<a id="sec-4"></a>

## 4. 完整等距消去、投影商与记录

<a id="statement-4-1"></a>

<a id="thm-isometry"></a>

#### 定理 4.1（共同等距输运与滤波的区别）

设 $J:H\to\widetilde H$ 为等距嵌入，即 $J^\dagger J=I_H$。即使 $J$ 不满射，也有

$$
(JV)^\dagger(JU)=V^\dagger U,\qquad
\langle JVx,JUy\rangle=\langle Vx,Uy\rangle.
$$

若两侧使用不同的嵌入 $J_V,J_U$，剩余项为
$V^\dagger J_V^\dagger J_UU$，一般不消失。

更一般地，设线性 $L:H\to\widetilde H$ 对非零向量均不为零。它保持所有归一化射线的转移概率，当且仅当

$$
L^\dagger L=cI,\qquad c>0.
$$

**证明。**

等距部分直接插入 $J^\dagger J=I$。对线性 $L$，记正定 $G=L^\dagger L$。若它保持全部射线转移概率，特别保持正交性。取 $G$ 的正交本征基 $e_i$，本征值 $\lambda_i>0$。两向量 $e_i+e_j$ 与 $e_i-e_j$ 原本正交，变换后内积为 $\lambda_i-\lambda_j$，故所有本征值相等，$G=cI$。反之公共因子 $c$ 在归一化内积的分子、分母相消。

∎

非满射等距属于保内积的嵌入接口，不直接是前节同一载体的群轨道作用。共同滤波 $L$ 若非标量等距，则留下关系度量 $G=L^\dagger L$；若作为成功分支，其成功概率也不能只因条件态归一化而删除。合法 Kraus 分支还要求 $L^\dagger L\le I$；即使 $G=cI$，分支发生率仍为 $c\le1$。

<a id="statement-4-2"></a>

<a id="thm-projection"></a>

#### 定理 4.2（投影的线性商）

对正交投影 $P$，映射

$$
H/\ker P\longrightarrow\operatorname{ran}P,
\qquad [\psi]\longmapsto P\psi
$$

是 Hilbert 空间的等距同构，其中商范数为

$$
\left\lVert [\psi]\right\rVert =\inf_{\eta\in\ker P}\left\lVert \psi+\eta\right\rVert =\left\lVert P\psi\right\rVert .
$$

**证明。**

正交分解 $\psi=P\psi+(I-P)\psi$ 表明每个商类的唯一最短代表为 $P\psi$。投影的核恰为被商去的子空间，且其像为 $\operatorname{ran}P$，给出良定义、单射与满射。

∎

所以“投影是一种商”在线性输出上严格成立。但对归一化输入 $\psi$，一次有标签的选择性测量还包含

$$
p=\left\lVert P\psi\right\rVert ^2,\qquad \psi_{\mathrm{cond}}=\frac{P\psi}{\sqrt p}\quad(p>0).
$$

条件化不是线性商。只留条件态会丢发生率：取 $P=\Pi_0$，输入 $\lvert 0\rangle$ 与 $\lvert +\rangle$ 的肯定条件态相同，概率却分别是一与 $1/2$。

<a id="statement-4-3"></a>

<a id="prop-record"></a>

#### 命题 4.3（保留完整指针时测量仍为等距）

给完整 PVM $\{\Pi_s\}$，映射

$$
T\psi=\sum_s\Pi_s\psi\otimes\lvert s\rangle
$$

满足 $T^\dagger T=I$，故为单射。丢弃指针才得到数据通道

$$
\Delta(\rho)=\sum_s\Pi_s\rho\Pi_s.
$$

**证明。**

指针正交使 $\langle T\phi,T\psi\rangle=\sum_s\langle\phi,\Pi_s\psi\rangle=\langle\phi,\psi\rangle$。对 $T\rho T^\dagger$ 对指针取偏迹，只有同标签项留下。

∎

<a id="statement-4-4"></a>

<a id="prop-dephase"></a>

#### 命题 4.4（去相干商一般不保持乘法）

对带标签秩一 PVM，$\Delta:M_d(\mathbb{C} )\to M_d(\mathbb{C} )$ 是 Hilbert–Schmidt 正交投影到对角代数，且

$$
M_d(\mathbb{C} )/\ker\Delta\cong\operatorname{ran}\Delta
$$

作为向量空间成立；一般不能沿原算符乘法将其视为代数商。

**证明。**

PVM 完备性给 $\Delta^2=\Delta$，迹循环性给 Hilbert–Schmidt 自伴性。取 $A=\lvert 0\rangle \langle 1\rvert$、$B=\lvert 1\rangle \langle 0\rvert$，则
$\Delta(A)=\Delta(B)=0$，却有 $\Delta(AB)=\Pi_0\ne0$。所以核不是双边理想，乘法不下降。

∎

完整记录的等距嵌入、丢记录的通道、选分支后归一化与共同框架商，对应不同的数学操作。将它们全部叫作“约去”，会隐藏下一次递归所需的信息。

<a id="sec-5"></a>

## 5. 基底与射线的双商，以及变分的精确位置

<a id="statement-5-1"></a>

#### 定义 5.1（种子和带标签基底的稳定子）

本节取固定单位纯种子 $\psi_0$。在 $G\le\operatorname{U} (d)$ 内定义

$$
H_{\psi_0}=\{h:h\psi_0=e^{i\alpha}\psi_0\},\qquad
T=\{t:t\Pi_st^\dagger=\Pi_s\text{ 对全部 }s\}.
$$

满酉群中 $T$ 是对角相位群。这里标签固定，不把结果置换自动视为同一测量。

<a id="statement-5-2"></a>

<a id="thm-double"></a>

#### 定理 5.2（射线与基底的相对双商）

将态历史中不改种子射线的右作用、基底历史中不改每个投影的右作用也识别后，有集合双射

$$
G\backslash\bigl((G/H_{\psi_0})\times(G/T)\bigr)
\cong T\backslash G/H_{\psi_0}.
$$

当 $G=\operatorname{U} (d)$ 时，该双商又与概率单纯形

$$
\Delta_{d-1}=\{(p_s):p_s\ge0,\ \sum_sp_s=1\}
$$

一一对应，具体对应为 $R\mapsto(|\langle s\rvert R\lvert \psi_0\rangle |^2)_s$。

**证明。**

改变代表 $U\mapsto Uh$、$V\mapsto Vt$ 使相对门变为 $t^\dagger Rh$；共同左作用仍消去。这给出双商描述，反向可取代表 $(R,I)$。

满酉群时，任意概率向量对应单位向量 $z_s=\sqrt{p_s}$，可将 $\psi_0$ 酉送到 $z$，故满射。若 $R\psi_0=z$、$R'\psi_0=z'$ 模长逐项相同，可选对角相位 $D$ 使 $z'=Dz$，零分量处相位任意。于是 $h=R^\dagger D^\dagger R'$ 固定 $\psi_0$，且 $R'=DRh$。所以同概率恰为同双商类。

∎

这是*一个纯态相对于一套完整带标签基底的当前读出*之分类。它不是一切未来干涉任务的分类。限制到原生黄金字群时，允许的 $D,h$ 未必在该群，以上到完整单纯形的单射和满射都不能直接照搬。

<a id="statement-5-3"></a>

<a id="thm-hellinger"></a>

#### 定理 5.3（消去列相位的变分距离）

给单位向量 $z,z'\in\mathbb{C} ^d$，令 $p_s=|z_s|^2$、$q_s=|z'_s|^2$。对全部对角相位 $D$ 优化，有

$$
\min_D\left\lVert z'-Dz\right\rVert ^2
=\sum_s(\sqrt{q_s}-\sqrt{p_s})^2
$$

<a id="equation-5"></a>

<a id="eq-phasevar"></a>

$$
=2-2\sum_s\sqrt{p_sq_s}.
\tag{5}
$$

**证明。**

每个分量的相位独立可选。复平面三角不等式给
$|z'_s-e^{i\theta_s}z_s|\ge\bigl||z'_s|-|z_s|\bigr|$，对齐两相位时达到等号。逐项相加，再用 $\sum p_s=\sum q_s=1$ 即得。

∎

这个公式将“关系相位的商”“概率几何”和一个确切的最优化问题接在一起。平方根来自已经声明的 $p_s=|z_s|^2$；它说明这些结构相容，不是由优化一词独立导出 Born 平方律。若只允许公共整体相位，则优化值改为
$2-2|\langle z,z'\rangle|$，两种相位群对应不同的商。

<a id="statement-5-4"></a>

<a id="prop-choi"></a>

#### 命题 5.4（用完整输入探针比较两门）

额外供应校准的最大纠缠探针
$\lvert \Phi_d\rangle =d^{-1/2}\sum_j\lvert j\rangle \lvert j\rangle$，定义
$\lvert U\rangle \!\rangle=(U\otimes I)\lvert \Phi_d\rangle$。则

$$
\langle\!\langle V\rvert  U\rangle\!\rangle=\frac{\operatorname{Tr} (V^\dagger U)}d,
\qquad
\min_{\theta}\frac{\left\lVert U-e^{i\theta}V\right\rVert _{\mathrm{HS}}^2}{2d}
=1-\frac{|\operatorname{Tr} (V^\dagger U)|}{d}.
$$

**证明。**

第一式展开 $\Phi_d$，得到 $d^{-1}\sum_j\langle j\rvert V^\dagger U\lvert j\rangle$。第二式展开范数平方为
$2d-2\Re(e^{-i\theta}\operatorname{Tr} (V^\dagger U))$；选择相位使该实部为迹的模。

∎

这种门比较与纠缠保真度的标准方法相联系 [[11](#ref-nielsen)]，但它增添了辅助载体、校准探针与相干接口。它通过对所有输入方向编码得到迹，没有证明任意未知本体种子都能直接约去。

<a id="sec-6"></a>

## 6. 以相干关系核取代绝对表示

<a id="statement-6-1"></a>

<a id="def-kernel"></a>

#### 定义 6.1（门历史的复关系核）

设 $\mathcal W$ 为合法门历史的标签集，$U_w$ 为其酉求值。定义

$$
K_\rho(v,w)=\operatorname{Tr} (\rho U_v^\dagger U_w).
$$

它比两两概率 $|K_\rho(v,w)|^2$ 保留更多信息。

<a id="statement-6-2"></a>

<a id="thm-kernel"></a>

#### 定理 6.2（正性与共同背景相消）

$K_\rho$ 是归一化 Hermitian 正半定核。其一个特征表示是

$$
\xi_w=U_w\sqrt\rho\in\operatorname{HS}(H),\qquad
K_\rho(v,w)=\langle\xi_v,\xi_w\rangle_{\mathrm{HS}}.
$$

若所列串接均合法，且求值满足 $U_{gv}=U_gU_v$、$U_{vg}=U_vU_g$，则

$$
K_\rho(gv,gw)=K_\rho(v,w),\qquad
K_\rho(vg,wg)=K_{U_g\rho U_g^\dagger}(v,w).
$$

**证明。**

对任意有限系数 $c_w$，令 $A=\sum_wc_wU_w$，则

$$
\sum_{v,w}\bar c_vc_wK_\rho(v,w)
=\operatorname{Tr} (\rho A^\dagger A)=\left\lVert A\sqrt\rho\right\rVert _{\mathrm{HS}}^2\ge0.
$$

酉性给对角为一，取伴随给 Hermitian 对称。两种续接分别消去 $U_g^\dagger U_g$，或以迹循环性将共同右因子吸收到来源。

∎

纯来源时，$K_\rho$ 是 $U_w\psi_0$ 的 Gram 核。混态时 $|K_\rho|^2$ 一般不是局部混态间的保真度：$\rho=I/2,U_v=I,U_w=Z$ 给相同局部输出 $I/2$，却有 $K_\rho(v,w)=0$。保留同一净化参考后，核才是联合纯态的重叠；已知受控相对门也可通过干涉读取 $\operatorname{Tr} (\rho U_v^\dagger U_w)$ [[10](#ref-ekert)]。这两种接口都比只给两个局部混态更丰富。

<a id="statement-6-3"></a>

<a id="thm-gram"></a>

#### 定理 6.3（关系核的最小 Hilbert 重构）

给任意集合 $\mathcal W$ 上的归一化复正半定核 $K$，在形式历史的有限复线性组合上设

$$
\left\langle\sum_va_v[v],\sum_wb_w[w]\right\rangle_K
=\sum_{v,w}\bar a_vb_wK(v,w).
$$

令 $\mathcal N_K$ 为零范数子空间，则

<a id="equation-6"></a>

<a id="eq-gns"></a>

$$
\boxed{\mathcal H_K=\overline{\mathbb{C} _{\mathrm{fin}}[\mathcal W]/\mathcal N_K}}
\tag{6}
$$

是 Hilbert 空间，标签像 $\xi_w$ 的内积正是 $K(v,w)$，且线性张成稠密。该最小实现唯一到保持每个标签向量的酉同构。

**证明。**

正半定二次型满足 Cauchy–Schwarz 不等式，故每个零范数向量与所有向量正交；商上内积因此良定义且正定。取完备化得到所需空间。若另有最小实现 $\eta_w$，映射
$\sum c_w\xi_w\mapsto\sum c_w\eta_w$
保持范数，所有零关系对应零关系，故良定义。它延拓为等距，最小性使其满射；标签的稠密张成给唯一性。

∎

相同构造与唯一性证明适用于非归一化正半定核；零对角标签给零向量。这个推广将在分支核中使用。

这里可以严格说：**共同本体的坐标表示可由完整相干关系核替代，而该核又重构历史所生成的最小部分。** 来源信息进入核，没有变成无关量；永不参与任何声明历史的正交补不受核确定。复数域与正性是输入，实正核同样能构造实 Hilbert 空间。

<a id="statement-6-4"></a>

<a id="thm-kernelrec"></a>

#### 定理 6.4（核相容的递归与完整分支）

若共同续接满足 $K(gv,gw)=K(v,w)$，则 $L_g\xi_w=\xi_{gw}$ 在零范数商上良定义并延拓为等距；逆续接也合法时为酉。

更一般地，给有限分支集 $O$、允许次归一化及零对角的后继正核 $K_+$ 和标签更新 $r_o$，假设对*全部*标签对成立

<a id="equation-7"></a>

<a id="eq-crossconservation"></a>

$$
K(v,w)=\sum_{o\in O}K_+(r_ov,r_ow).
\tag{7}
$$

则 $M_o\xi_w=\xi^+_{r_ow}$ 定义收缩算子，满足

$$
\sum_oM_o^\dagger M_o=I,\qquad
T\xi=\sum_oM_o\xi\otimes\lvert o\rangle
$$

为等距嵌入。

**证明。**

核不变使任意有限线性组合续接前后的范数相等，所以零范数空间被保持，等距延拓存在，有合法逆时满射。
对分支情形，将式 [(7)](#eq-crossconservation) 乘 $\bar c_vc_w$ 并求和，得到

$$
\left\lVert \sum_wc_w\xi_w\right\rVert ^2
=\sum_o\left\lVert \sum_wc_w\xi^+_{r_ow}\right\rVert ^2.
$$

左边为零时右边每项为零，故每个分支映射都下降到商；每项又不超过左边，给统一收缩界并允许完备化。恒等式延拓并极化后得到 $\sum M_o^\dagger M_o=I$，正交记录给 $T^\dagger T=I$。

∎

这正是项目相干重构卷第 6.1–6.2 节所强调的交叉项条件 [[4](#ref-reconstruction)]。仅有每个单独标签的总概率守恒，不能保证线性零关系在递归后仍为零。例如当前两个标签给同一单位向量，后继却指定两个正交单位向量；各标签范数都未变，但原来的零关系 $\xi_a-\xi_b=0$ 被送到非零，映射不能下降。归一化的条件态更新也不能直接代替这里的线性 $M_o$。

<a id="statement-6-5"></a>

<a id="prop-leftideal"></a>

#### 命题 6.5（来源零空间通常只给左模商）

设 $\mathcal A\subseteq M_d(\mathbb{C} )$ 为含单位的 $*$ 代数，则

$$
\mathcal N_\rho=\{A:\operatorname{Tr} (\rho A^\dagger A)=0\}
=\{A:A\sqrt\rho=0\}
$$

是左理想。内积 $\langle[A],[B]\rangle=\operatorname{Tr} (\rho A^\dagger B)$ 与左作用
$\pi(X)[A]=[XA]$ 在 $\mathcal A/\mathcal N_\rho$ 上良定义。它一般不是按原乘法的双边代数商。

**证明。**

$A\sqrt\rho=0$ 蕴含 $XA\sqrt\rho=0$，故左作用良定义；映射 $[A]\mapsto A\sqrt\rho$ 验证内积和范数，且
$\left\lVert XA\sqrt\rho\right\rVert _{\mathrm{HS}}\le\left\lVert X\right\rVert _{\mathrm{op}}\left\lVert A\sqrt\rho\right\rVert _{\mathrm{HS}}$。
反例取 $\rho=\Pi_0,A=\Pi_1,B=\lvert 1\rangle \langle 0\rvert$，则 $A\in\mathcal N_\rho$，但 $AB=B\notin\mathcal N_\rho$。

∎

若 $\mathcal A=M_d(\mathbb{C} )$、$\operatorname{rank} \rho=r$，此循环表示的复维数为 $dr$：$A\sqrt\rho$ 在来源支持的 $r$ 个列方向上任意，其余为零。因此纯来源给 $d$，忠实混态给 $d^2$；最小关系表示不自动等于原局部载体。

<a id="sec-7"></a>

<a id="sec-golden"></a>

## 7. 原生黄金门：两两概率相同，三历史相位不同

采用五个合法模式 $0,1,2,3,13$，分别对应 $000,100,010,001,101$。三个占位读口为

$$
N_1=\Pi_1+\Pi_{13},\qquad N_2=\Pi_2,\qquad N_3=\Pi_3+\Pi_{13}.
$$

它们是三个对易效果，而不是五维载体的一组完整三向量基。原生黄金门的活动块及相关精确恒等式与项目量子原则续卷的合法块相同 [[7](#ref-gate)]；以下结果只用所列矩阵作纸面证明。

<a id="statement-7-1"></a>

#### 定义 7.1（黄金活动块）

令

$$
\varphi=\frac{1+\sqrt5}{2},\quad \omega=e^{3\pi i/5},\quad
a=\varphi^{-1},\quad \delta=\varphi^{-2},\quad b=\varphi^{-3/2}.
$$

在 $H_{0,2}=\operatorname{span}\{\lvert 0\rangle ,\lvert 2\rangle \}$ 上取

$$
\mathcal P=\begin{pmatrix}a&b\\b&\delta\end{pmatrix},\qquad
K=\omega[I+(\omega-1)\mathcal P].
$$

完整五模式上，$\mathcal P$ 在模式 $1,3$ 为零、模式 $13$ 为一。

<a id="statement-7-2"></a>

<a id="lem-gold"></a>

#### 引理 7.2（黄金谱与正字逆元）

$\mathcal P$ 是正交投影；$K$ 酉，$K^{10}=I$，$K^{-1}=K^9$，且对全部整数 $n$ 有

$$
K^n=\omega^n[I+(\omega^n-1)\mathcal P].
$$

另外

$$
\delta=a^2=1-a,\quad a\delta=a-\delta,\quad
\omega^2+a\omega+1=0,\quad |1-\omega|^2=\varphi^2.
$$

**证明。**

活动块自伴、迹一、行列式 $a\delta-b^2=0$，正对角元给正性，所以本征值为零与一。其余块也为投影。$K$ 在两投影扇区的本征值为 $\omega,\omega^2$，给幂公式及十次单位。
$\varphi^2=\varphi+1$ 给前三个实代数恒等式。又 $2\cos(3\pi/5)=-a$，故 $\omega+\omega^{-1}=-a$，乘以 $\omega$ 即得二次式；$|1-\omega|^2=2+a=\varphi^2$。

∎

<a id="statement-7-3"></a>

#### 定义 7.3（有向闭路关系量）

对单位向量历史 $\psi_i$，记 $K_{ij}=\langle\psi_i,\psi_j\rangle$、$p_{ij}=|K_{ij}|^2$。定义

$$
B(i_1,\ldots,i_m)=K_{i_1i_2}\cdots K_{i_mi_1}.
$$

三标签情形为 Bargmann 不变量。共同酉和单个标签的相位重选都保持 $B$。

这类闭路量与几何相位的联系，以及无零锚定边时用三点量分解更长闭路，已有标准文献 [[9](#ref-bargmann)]。本节的内容是黄金原生历史中的精确实例。

<a id="statement-7-4"></a>

<a id="thm-goldbarg"></a>

#### 定理 7.4（全部两两黄金概率仍不确定相干关系）

对两种种子 $s=0,2$，取历史 $\psi_j^{(s)}=K^j\lvert s\rangle$。设
$t=\langle s\rvert \mathcal P\lvert s\rangle$，分别为 $a,\delta$，并记

$$
k_t(n)=\langle s\rvert K^n\lvert s\rangle =\omega^n[(1-t)+t\omega^n].
$$

两族全部带标签的两两转移概率相同：

<a id="equation-8"></a>

<a id="eq-allpairs"></a>

$$
|k_t(n)|^2=1-t(1-t)|1-\omega^n|^2,
\qquad t(1-t)=a\delta.
\tag{8}
$$

但三历史 $0,1,2$ 的闭路量满足

<a id="equation-9"></a>

<a id="eq-goldbarg"></a>

$$
\boxed{B_\delta=\varphi^{-4}\omega,\qquad
B_a=\varphi^{-4}\bar\omega,}
\qquad B_t=k_t(1)^2k_t(-2).
\tag{9}
$$

所以保持全部历史标签的共同酉与射线相位重选，不能把两族相互变换。

**证明。**

引理 [7.2](#lem-gold) 的幂公式给 $k_t$，直接展开模平方给式 [(8)](#eq-allpairs)。两种种子满足 $a+\delta=1$，故右侧完全相同。

令 $z=\omega$。由 $z^2+az+1=0$ 得 $z^{-2}=a(z-1)$。三个指数之和为零，整体相位消去，且

$$
B_\delta=(a+\delta z)^2(a+\delta z^{-2}).
$$

用 $\delta=a^2=1-a$ 逐项化简得

$$
(a+\delta z)^2=\delta(a+z),\qquad
a+\delta z^{-2}=\delta(1+az),
$$

$$
(a+z)(1+az)=z.
$$

所以 $B_\delta=\delta^2z=\varphi^{-4}\omega$。再记
$h_t(n)=1-t+tz^n$，则 $h_{1-t}(n)=z^n\overline{h_t(n)}$。对指数 $1,1,-2$ 相乘给 $B_a=\overline{B_\delta}$。因 $\omega$ 非实，两者不同；闭路量在所述变换下不变，得到结论。

∎

这是对*全部两历史投影接口*的反例；它没有说两种初态在一切读口下都不可区分，固定模式 PVM 在起点就能区分 $\lvert 0\rangle$ 和 $\lvert 2\rangle$。所有整数历史都可由 $K^9=K^{-1}$ 表为有限正向原生字，故没有隐藏调用任意连续相位门。

<a id="statement-7-5"></a>

<a id="prop-triangle"></a>

#### 命题 7.5（三历史的相融约束）

任意三个单位向量满足

$$
|B(0,1,2)|^2=p_{01}p_{12}p_{20},\qquad
1-p_{01}-p_{12}-p_{20}+2\Re B(0,1,2)\ge0.
$$

若三者的线性张成维数至多二，第二式取等号。

**证明。**

第一式逐项取模平方。第二式左侧为三向量 Gram 矩阵的行列式，正半定性给非负；秩至多二时行列式为零。

∎

因此相位不能任意乱猜：它受正性、秩及其他闭路共同约束。但即使秩为二，这些两两概率通常仍只能锁定实部，不能单独锁定虚部的取向。黄金反例正保留了这一对共轭可能性。

<a id="statement-7-6"></a>

<a id="thm-cyclemeasure"></a>

#### 定理 7.6（三副本接口读取闭路量）

若可重复制备三个历史并控制循环置换

$$
C(x_0\otimes x_1\otimes x_2)=x_1\otimes x_2\otimes x_0,
$$

则对 $\chi=\psi_0\otimes\psi_1\otimes\psi_2$ 有
$\langle\chi,C\chi\rangle=B(0,1,2)$。辅助比特从 $\lvert +\rangle$ 出发并控制 $C$ 后，

$$
\langle X\rangle=\Re B,
\qquad \langle Y\rangle=\Im B.
$$

**证明。**

张量内积给三个相邻重叠之积。受控后的纯态是
$(\lvert 0\rangle \chi+\lvert 1\rangle C\chi)/\sqrt2$，辅助约化矩阵为
$\tfrac12\bigl(\begin{smallmatrix}1&\bar B\\B&1\end{smallmatrix}\bigr)$，与 $X,Y$ 取迹即得。

∎

该构造需要三副本制备、受控循环和校准读出。它与标准循环干涉方法相容 [[10](#ref-ekert)]，没有声称单地址原生菜单已免费供应全部接口，更不需要复制未知单份量子态。

此处比较的是所声明的数据向量 $K^j\lvert s\rangle$。若完整历史还带永久正交时钟 $\lvert j\rangle$，则不同 $\lvert j\rangle \otimes K^j\lvert s\rangle$ 的完整内积为零。非零闭路量应由上述数据因子上的循环接口读取，不能把数据 Gram 核与保留全部正交记录的全局 Gram 核混为一物。

<a id="statement-7-7"></a>

<a id="thm-cycles"></a>

#### 定理 7.7（模长和闭路相位重构规范类）

给有限标签上的两个归一化 Hermitian 核 $K,L$，假设零模式与非零边模长相同。以下等价：

1. 存在顶点相位 $\alpha_i$ 使 $L_{ij}=e^{i(\alpha_j-\alpha_i)}K_{ij}$；

2. 非零重叠图上每条有向闭路的边乘积在两核中相同。

若有锚点 $0$ 与所有标签非正交，可选 $K_{0i}>0$，此时

<a id="equation-10"></a>

<a id="eq-anchor"></a>

$$
\boxed{K_{ij}=\frac{B(0,i,j)}{|K_{0i}|\,|K_{0j}|}.}
\tag{10}
$$

**证明。**

第一条到第二条为顶点相位沿闭路消去。反向在每个连通分量选择生成树，沿树固定相位，使全部树边相同。任何非树边与树路径构成闭路；闭路乘积相同且树边非零，迫使该非树边相同。锚点公式直接由 $B(0,i,j)=K_{0i}K_{ij}K_{j0}$ 得到。

∎

零重叠时三角量未必够。例如四点核对角为一，四条循环边模长 $r\in(0,1/2)$，两条弦为零，仅一条循环边带相位 $e^{i\theta}$。对任意 $x$，由 $2|x_ix_j|\le|x_i|^2+|x_j|^2$ 得

$$
x^\dagger Kx\ge(1-2r)\sum_i|x_i|^2>0\quad(x\ne0).
$$

故任意 $\theta$ 都给合法正核。不同三个标签的三角乘积全部为零，四边闭路却为 $r^4e^{i\theta}$。选择一条三角剖分的弦，不等于已获得那条弦的非零相干关系。

若历史还处于受控叠加中，顶点相位重选须伴随程序系数的反向变换才是同一表示。不能只删除程序中可干涉的相位，而仍声称后续相干操作未变。

<a id="sec-8"></a>

<a id="sec-future"></a>

## 8. 只有对未来闭合的观察商才能继续预测

<a id="statement-8-1"></a>

#### 定义 8.1（当前响应商与合法递归）

在真实来源集合 $X$ 上给响应映射 $q:X\to Y$，定义
$x\sim_qx'\iff q(x)=q(x')$。给允许操作 $T_a:D_a\to X$，其中 $D_a\subseteq X$ 是其合法域。

<a id="statement-8-2"></a>

<a id="thm-obsquot"></a>

#### 定理 8.2（观察商的因子化与更新判据）

目标 $F:X\to Z$ 能写成 $F=\bar F\circ q$，当且仅当 $F$ 在每个 $q$ 纤维上常值。操作 $T_a$ 能成为商上的部分操作，当且仅当

$$
D_a\text{ 是等价类的并},\qquad
x\sim_qx'\Longrightarrow T_ax\sim_qT_ax'\quad(x,x'\in D_a).
$$

**证明。**

因子化若存在，同一 $q$ 值必给同一 $F$ 值。反向定义 $\bar F(q(x))=F(x)$，纤维常值保证良定义，实际像上唯一。对部分操作，相同类首先必须同为合法或非法，其次输出必须属于同一类；这两条也显然足以定义 $[x]\mapsto[T_ax]$。

∎

这是项目共同来源响应商、未来同余与消费者核商原则的直接应用 [[3](#ref-omega), [6](#ref-csa)]。将查询只取当前三均值、完整模式概率或全部未来程序，得到的等价关系会不同。

<a id="statement-8-3"></a>

<a id="thm-goldfuture"></a>

#### 定理 8.3（原生当前人口商不能递归闭合）

从同一个种子 $\lvert 2\rangle$ 出发，两个合法历史

$$
\psi_+=K\lvert 2\rangle ,\qquad \psi_-=K^9\lvert 2\rangle =K^\dagger\lvert 2\rangle
$$

当前完整五模式概率完全相同：

$$
(p_0,p_1,p_2,p_3,p_{13})=(a,0,\delta,0,0).
$$

但共同再施加一个原生门 $K$ 后，

<a id="equation-11"></a>

<a id="eq-futurecounter"></a>

$$
\boxed{p_2(K\psi_+)=\varphi^{-4},\qquad
p_2(K\psi_-)=1.}
\tag{11}
$$

因此不存在仅以当前五模式人口为状态、能对这些历史给出正确下一步人口的自治更新函数。

**证明。**

$\mathcal P$ 在模式基中实对称，所以 $K$ 与 $K^\dagger$ 对实基向量给共轭输出，模平方相同。由式 [(8)](#eq-allpairs)，$p_2=1-a\delta\varphi^2=\delta$；活动块总概率一给 $p_0=a$。
对负历史，$KK^9=I$。对正历史，

$$
a+\delta\omega^2=(a-\delta)-a\delta\omega
=a\delta(1-\omega),
$$

故
$|\langle 2\rvert K^2\lvert 2\rangle |^2=(a\delta)^2\varphi^2=\varphi^{-4}$。
同一输入人口向量却要求两个不同后继，排除自治函数。

∎

这比“未知相位可能有用”更具体：被当前投影消去的差别，会被同一个合法原生后继重新变成可读概率。三个稳定占位均值更粗，当然也无法区分这两个历史。

<a id="statement-8-4"></a>

<a id="thm-futureclosure"></a>

#### 定理 8.4（未来效果闭包给最粗可递归观察商）

在有限维载体上，固定全部处处合法的酉菜单 $\mathcal U$ 以及当前效果族 $\mathcal E$。令 $U_h$ 遍历有限合法字，包含空字，定义

$$
W_\infty=\operatorname{span}_{\mathbb{R}} \{U_h^\dagger E U_h:E\in\mathcal E,\ h\text{ 合法}\}.
$$

则

$$
\rho\sim_\infty\sigma
\iff \operatorname{Tr} [(\rho-\sigma)A]=0\quad\forall A\in W_\infty
$$

是既保持当前读出、又在所有共同合法后继下稳定的*最粗*等价关系。

**证明。**

空字包含当前效果。对任一 $U\in\mathcal U$，$U^\dagger W_\infty U\subseteq W_\infty$，故 $\rho\sim_\infty\sigma$ 蕴含 $U\rho U^\dagger\sim_\infty U\sigma U^\dagger$。反之，任何保持当前读出且对每个后继稳定的等价关系，按字长归纳必保持所有未来字后的每个效果期望，因而包含于 $\sim_\infty$。对实线性张成的等价式由迹线性性给出。

∎

如果允许带结果的仪器，可将每条记录分支的 Kraus 乘积和结束效果纳入同样的联合概率测试；若允许部分操作，则必须把非法性也作为可区别输出。只要求完成某个任务时，最粗充分边界可能更粗，不能把该任务商冒认为完整未来律商。最新联合核卷第 19–21 节正将这两种合同分开 [[2](#ref-jointkernel)]。

<a id="statement-8-5"></a>

<a id="prop-staticrecord"></a>

#### 命题 8.5（静态来源不自动等于完整动态边界）

设不可变来源 $T$ 的只读查询不改变 $T$。若整个内部编码仅为 $\iota(T)$，则无法将一次查询同时表示为档案中插入新鲜事件 $e\notin\iota(T)$。

**证明。**

来源未变要求查询后编码仍为 $\iota(T)$；新鲜插入要求它成为 $\iota(T)\cup\{e\}$。两者相等与 $e\notin\iota(T)$ 矛盾。

∎

这是最新联合核卷定理 23.2 的接口障碍 [[2](#ref-jointkernel)]。将状态改为“静态来源加当前记录”可避开矛盾，但记录的合法增长与查询对应还需明示。用户的静态本体图景可以容纳增长的观察者切面；共同背景的消去不能同时删掉区分这些切面的记录。

<a id="sec-9"></a>

## 9. 基底也不确定时：把程序纳入共同来源

<a id="statement-9-1"></a>

#### 定义 9.1（量子承载的门历史程序）

取有限组正交程序标签 $\lvert u\rangle ,\lvert v\rangle$，其关联矩阵为已知酉 $U_u,V_v$。在程序与数据联合载体上定义

$$
\widehat R=\sum_{u,v}\lvert uv\rangle \langle uv\rvert \otimes V_v^\dagger U_u.
$$

联合来源 $\Sigma$ 可包含程序之间、程序与数据之间的相关和纠缠。

<a id="statement-9-2"></a>

<a id="prop-program"></a>

#### 命题 9.2（程序化相对读出不要求独立种子）

只读数据标签 $s$ 的概率为

$$
p_s=\operatorname{Tr} \!\left[\Sigma\,\widehat R^\dagger
(I_{\rm prog}\otimes\Pi_s)\widehat R\right].
$$

除非另行给出来源的独立性，不能将其改写为分别选取两个门边缘分布与一个种子态的自由乘积。

**证明。**

$\widehat R$ 在正交程序扇区上酉，故是联合酉。Born 迹循环性给公式。该效果的 $(u,v)$ 对角块作用于 $\Sigma$ 的对应条件数据块；一般相关态的这些块并非同一固定密度矩阵乘两边缘概率，故所述因子化没有根据。

∎

若再允许程序的相干读出，程序非对角块也能影响结果，所需关系核随之扩展。于是“所有概念连同尺子都在预测中”可被具体化为扩大联合来源和查询族，而不是把相容约束一并删除。正交的已知程序标签是此构造的前件；任意未知非正交基态样本不是同一种资源。

<a id="statement-9-3"></a>

<a id="prop-swap"></a>

#### 命题 9.3（基态样本给重叠探针，不自动给尖锐读口）

对独立制备的参考与数据输入 $\sigma\otimes\rho$，标准受控 SWAP 测试的肯定概率为

$$
p_+=\frac{1+\operatorname{Tr} (\sigma\rho)}2.
$$

因此它对数据的肯定效果是 $E_+=(I+\sigma)/2$。即使
$\sigma=\lvert \beta\rangle \langle \beta\rvert$，一般也不是 $\lvert \beta\rangle \langle \beta\rvert$ 本身。

**证明。**

矩阵单位展开给
$\operatorname{Tr} [\mathrm{SWAP}(\sigma\otimes\rho)]=\operatorname{Tr} (\sigma\rho)$，辅助干涉公式给 $p_+$。在 $\beta$ 的正交补上，$E_+$ 的本征值仍为 $1/2$，尖锐投影的本征值则为零。

∎

一般相关联合输入 $\tau$ 的公式应为 $p_+=(1+\operatorname{Tr} (\mathrm{SWAP}\,\tau))/2$，不能把 $\tau$ 自动换成其两个边缘的乘积。

重复实验可由 $2p_+-1$ 估计独立输入的 Born 重叠，单次原始事件概率却不同。该区别可直接从标准重叠测量公式核对 [[10](#ref-ekert)]。已知制备门 $V$ 且能反演时，执行 $V^\dagger$ 后读标准基可以实现相应尖锐 PVM；只有一个未知基态样本时，上述公式没有供应这项能力。

<a id="sec-10"></a>

<a id="sec-mps"></a>

## 10. 最新项目的 MPS 实例：约去虚参考，保留边界

固定快照的新合并给出四物理能级、虚维数三的 $U(1)$ 对称可注入 MPS 见证。问题说明、蓝图和源模块分别可定位到 [[12](#ref-mpsproject), [13](#ref-mpsblueprint)]；MPS 边界映射及对称性背景见 [[14](#ref-sanz)]。这里直接复核与本轮“商”有关的矩阵内容，不把项目报告的机器状态说成本文重新执行的验证。

<a id="statement-10-1"></a>

#### 定义 10.1（四能级见证及边界振幅）

本节重新局部记 $c=3/5,e=4/5$，矩阵单位 $E_{ij}$ 的索引为 $0,1,2$。令

$$
A_0=c(E_{01}+E_{12}),\quad A_1=e(E_{10}+E_{21}),\quad
A_2=eE_{02},\quad A_3=cE_{20}.
$$

定义

$$
\Gamma_2:M_3(\mathbb{C} )\longrightarrow\mathbb{C} ^{16},\qquad
X\longmapsto\bigl(\operatorname{Tr} (XA_iA_j)\bigr)_{i,j=0}^3.
$$

这里 $X$ 是边界矩阵，输出是*完整复振幅*。

<a id="statement-10-2"></a>

<a id="prop-mpsnorm"></a>

#### 命题 10.2（规范归一与荷协变）

该见证满足 $\sum_kA_kA_k^\dagger=I_3$，也满足 $\sum_kA_k^\dagger A_k=I_3$。令

$$
V(\theta)=\operatorname{diag} (1,\exp(i\theta),\exp(2i\theta)),
\qquad (\lambda_0,\lambda_1,\lambda_2,\lambda_3)=(-1,1,-2,2),
$$

则 $V(\theta)A_kV(\theta)^{-1}=\exp(i\theta\lambda_k)A_k$。

**证明。**

两种归一和的每个对角元均为 $c^2+e^2=1$，非对角元为零。共轭矩阵单位满足
$V E_{ij}V^{-1}=\exp(i(i-j)\theta)E_{ij}$，逐项给四个荷。

∎

归一方向在原问题中规定的是第一式，第二式是此具体见证的额外性质。这些 $A_k$ 不是四个酉门；若作 Kraus 操作还需声明相应的记录接口，不能仅凭矩阵乘积就与黄金门一一等同。

<a id="statement-10-3"></a>

<a id="thm-mpsinject"></a>

#### 定理 10.3（二字完整振幅辨识全部边界）

$\Gamma_2$ 在整个 $M_3(\mathbb{C} )$ 上单射。

**证明。**

由 $E_{ij}E_{kl}=\delta_{jk}E_{il}$ 得

$$
\begin{array}{lll}
A_0^2=c^2E_{02},&A_1^2=e^2E_{20},&A_0A_3=c^2E_{10},\\
A_3A_0=c^2E_{21},&A_1A_2=e^2E_{12},&A_2A_1=e^2E_{01},\\
A_2A_3=ceE_{00},&A_3A_2=ceE_{22},&A_0A_1-A_2A_3=ceE_{11}.
\end{array}
$$

$c,e$ 非零，故长度二的乘积张成全部矩阵单位。如果 $\Gamma_2(X)=0$，线性性给所有
$\operatorname{Tr} (XE_{ij})=X_{ji}=0$，故 $X=0$。对 $X-Y$ 应用同一论证得到单射。

∎

<a id="statement-10-4"></a>

<a id="thm-mpsgauge"></a>

#### 定理 10.4（共同虚参考消去与边界可辨识并存）

对任意 $S\in\operatorname{GL}_3(\mathbb{C} )$，同时变换

$$
A_i'=SA_iS^{-1},\qquad X'=SXS^{-1},
$$

全部边界振幅不变：

$$
\operatorname{Tr} (X'A_i'A_j')=\operatorname{Tr} (XA_iA_j).
$$

但在固定已知的 $A_i$ 下，边界 $X$ 仍由完整二字振幅唯一确定。

**证明。**

乘积中相邻的 $S^{-1}S$ 消去，迹循环性再消去外层共轭，得到第一式。第二条正是定理 [10.3](#thm-mpsinject)。

∎

这里被约去的是共同虚坐标。边界信息没有同时消失。一般 $\operatorname{GL}$ 变换不必酉，此处用于 MPS 的被动表示变换，也未必保持所选规范归一；酉 $S$ 则保持上述两种归一。将 $\Gamma_2$ 换成逐项模平方后，不能继续援用该单射证明，最直接地 $X$ 与 $\exp(i\alpha)X$ 已给相同模平方。

新见证使用一般非零荷 $(-1,1,-2,2)$；它不是通常 spin-$3/2$ 的 $J_z$ 谱，也没有据此改写不可约 $SU(2)$ 结论或证明哈密顿量隙、唯一基态等额外命题。四物理能级、三虚维数与 AURIC 的五模式、三占位读口是不同接口。本文建立的是共同参考消去与边界辨识的数学联系。

<a id="sec-11"></a>

## 11. 本轮得到的正式结构与尚未消去的前件

<a id="statement-11-1"></a>

<a id="def-model"></a>

#### 定义 11.1（可递归的相对观察模型）

一个本稿意义的模型由以下资料组成：合法历史及其续接；归一化复正核 $K$；满足共同续接不变或完整交叉项守恒的更新；明确的记录与效果接口；以及对所声明全部未来测试闭合的观察等价关系。若使用可变基底，程序、来源配对和控制菜单也属于这些资料。

<a id="statement-11-2"></a>

<a id="thm-combined"></a>

#### 定理 11.2（相对表示、相干重构和递归商的联合结论）

在定义 [11.1](#def-model) 及各相关前件下：

1. 两门历史的共同左酉表示由相对门完全分类，共同完整等距保持全部关系核；

2. 完整复正核唯一重构历史生成的最小 Hilbert 表示，核相容的递归下降为等距或带记录的分支操作；

3. 一个观察摘要能承接全部声明后继，恰当且仅当其纤维关系满足合法域与更新稳定性；

4. 当前两两概率或模式人口都可能是过粗摘要；黄金原生反例分别保留未被这些摘要记录的闭路相位与后继概率差。

**证明。**

第一条合并定理 [3.2](#thm-orbit)、[4.1](#thm-isometry)、[6.2](#thm-kernel)；第二条由定理 [6.3](#thm-gram)、[6.4](#thm-kernelrec)；第三条为定理 [8.2](#thm-obsquot)，量子效果接口的最粗版本由定理 [8.4](#thm-futureclosure) 给出；第四条由定理 [7.4](#thm-goldbarg)、[8.3](#thm-goldfuture)。

∎

由此，用户直觉最强的可证版本是：**量子观察能够以门历史之间的关系描述；共同表示可被约去，且关系数据可以反向重构最小表示。但只有保留相干信息、来源泛函和合法后继作用的商，才支持递归预测。** 

“本体被约去”可以有清楚的含义：不再需要指定某套绝对坐标，或不再保存永远不被许可测试区分的冗余。它一般不意味着读出与来源无关，不意味着两两概率决定全部复关系，也不意味着所有后继都在任意商上良定义。

本轮没有从“商”或“递归”单独推出复数域、Born 标定、任意态制备、量子门普适性或唯一宇宙本体。可以继续研究的具体任务已经收紧为：对选定原生菜单和内生程序，确定最小未来效果空间；找出可由该菜单实现的闭路相位接口；在扩大载体、保留时钟和记录后验证同一套商的稳定性。这些是可写成数学条件和读出差的目标。

<a id="sec-A"></a>

## 附录 A. 术语、约定与复核范围

本文的“基底态”指一套已校准测量基底中的射线，不自动指哈密顿量的最低能态。“共同过去”与“共同末端输运”按算子左右作用区分，是组合次序的声明，不预设宇宙有一个外部绝对时间。“商”指明确的等价类或线性零空间，不指两个未知向量的数值除法。

当前固定仓库事实来自不可变提交及经 Git blob 核对的文本。全部证明以符号代数与线性代数给出，未使用数学数值、CAS、枚举、模拟或 Lean 执行。排版构建和文件哈希仅核对交付物。本文是条件理论研究，原生精确反例、核重构与 MPS 桥各自的范围在相应定理后给出。

<a id="sec-bibliography"></a>

## 文献与项目来源

<a id="ref-snapshot"></a>

1. the-omega-institute/trureturing.
[固定提交 f76bcb79（dev，2026-10-29 UTC / 10-30 Singapore）](https://github.com/the-omega-institute/trureturing/commit/f76bcb791c34c35b622417c0d446251425e9faaf)；
[相对 v21 固定版本的比较](https://github.com/the-omega-institute/trureturing/compare/ce2773bd014df637336d2e89f83f220d8535c5be...f76bcb791c34c35b622417c0d446251425e9faaf)。

<a id="ref-jointkernel"></a>

2. 项目：[递归关系观察：联合核与最小预测核心桥](https://github.com/the-omega-institute/trureturing/blob/f76bcb791c34c35b622417c0d446251425e9faaf/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_JOINT_KERNEL_MINIMAL_PREDICTIVE_CORE_BRIDGE.md)，新增第 15–23 节，尤其第 19–21 节与定理 23.2。普通理论文本；不等同于新的 Lean 声明。

<a id="ref-omega"></a>

3. 项目：[AURIC Ω 静态相容纤维理论](https://github.com/the-omega-institute/trureturing/blob/f76bcb791c34c35b622417c0d446251425e9faaf/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，第 1.3、4.1–4.2、5.2 节。

<a id="ref-reconstruction"></a>

4. 项目：[AURIC FIB ATOM 量子原则与相干重构](https://github.com/the-omega-institute/trureturing/blob/f76bcb791c34c35b622417c0d446251425e9faaf/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md)，第 6.1–6.2 节。

<a id="ref-quotients"></a>

5. 项目：[关系商与物理候选](https://github.com/the-omega-institute/trureturing/blob/f76bcb791c34c35b622417c0d446251425e9faaf/docs/develop/theory/AURIC_FIB_ATOM_RELATIONAL_QUOTIENTS_AND_PHYSICAL_CANDIDATES.md)。该卷开头标明混合用户供稿来源；历史快照与转录的主张按原归属处理。

<a id="ref-csa"></a>

6. 项目：[语境时空算术](https://github.com/the-omega-institute/trureturing/blob/f76bcb791c34c35b622417c0d446251425e9faaf/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC.md)，第 42.4 节命题 QI-P3：固定实际来源与消费者的准确观察商。

<a id="ref-gate"></a>

7. 项目：[量子原则与相干重构续卷](https://github.com/the-omega-institute/trureturing/blob/f76bcb791c34c35b622417c0d446251425e9faaf/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION.md)，第 64–68 节的合法黄金块与读出条件。本文所需黄金块完整列于第 [7](#sec-golden) 节。

<a id="ref-qrf"></a>

8. F. Giacomini, E. Castro-Ruiz, C. Brukner.
*Quantum mechanics and the covariance of physical laws in quantum reference frames*.
Nature Communications 10, 494 (2019).
[arXiv:1712.07207](https://arxiv.org/abs/1712.07207)；
[DOI:10.1038/s41467-018-08155-0](https://doi.org/10.1038/s41467-018-08155-0)。

<a id="ref-bargmann"></a>

9. E. M. Rabei, Arvind, N. Mukunda, R. Simon.
*Bargmann invariants and geometric phases: A generalized connection*.
Physical Review A 60, 3397 (1999).
[arXiv:quant-ph/9907080](https://arxiv.org/abs/quant-ph/9907080)。参见式 (2.8)、(6.1)；零分母时不能直接使用锚定三角分解。

<a id="ref-ekert"></a>

10. A. K. Ekert, C. Moura Alves, D. K. L. Oi, M. Horodecki, P. Horodecki, L. C. Kwek.
*Direct estimations of linear and nonlinear functionals of a quantum state*.
Physical Review Letters 88, 217901 (2002).
[arXiv:quant-ph/0203016](https://arxiv.org/abs/quant-ph/0203016)。参见式 (1)–(4)；本文显式固定三循环的方向与虚部符号。

<a id="ref-nielsen"></a>

11. M. A. Nielsen.
*A simple formula for the average gate fidelity of a quantum dynamical operation*.
Physics Letters A 303, 249–252 (2002).
[arXiv:quant-ph/0205035](https://arxiv.org/abs/quant-ph/0205035)。

<a id="ref-mpsproject"></a>

12. 项目：[四物理能级、一般非零荷的 U(1) 可注入 MPS 问题与见证](https://github.com/the-omega-institute/trureturing/blob/f76bcb791c34c35b622417c0d446251425e9faaf/Problems/sanz-wolf-perez-garcia-cirac-2009-spin-three-halves-u1-injective-mps.md)。范围、报告证据和非结论分别见该文相应段落。

<a id="ref-mpsblueprint"></a>

13. 项目：[FourLevelU1SymmetricInjectiveMPS 蓝图](https://github.com/the-omega-institute/trureturing/blob/f76bcb791c34c35b622417c0d446251425e9faaf/Blueprint/D5/S3/Quantum/SpinChains/FourLevelU1SymmetricInjectiveMPS.md)；
[对应 Lean 模块路径](https://github.com/the-omega-institute/trureturing/blob/f76bcb791c34c35b622417c0d446251425e9faaf/D5/S3/Quantum/SpinChains/FourLevelU1SymmetricInjectiveMPS.lean)。本轮未执行该模块。

<a id="ref-sanz"></a>

14. M. Sanz, M. M. Wolf, D. Pérez-García, J. I. Cirac.
*Matrix Product States: Symmetries and two-body Hamiltonians*.
Physical Review A 79, 042308 (2009).
[arXiv:0901.2223](https://arxiv.org/abs/0901.2223)。本文使用其 MPS 边界映射与对称性背景，不据此主张已复核原论文的全部问题或新颖性。

