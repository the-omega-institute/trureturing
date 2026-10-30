<a id="auric-v18"></a>

# 三角剖分、塌缩与递归酉门

**AURIC 隐藏关系的完成、记录与谱相容**

**定义、定理与完整纸面证明**

**v18.0 · 2026 年 10 月 30 日 · Asia/Singapore**

<a id="sec-abstract"></a>

## 摘要

三角剖分选择隐藏关系的完成方式，何时能够成为一次量子测量的条件分支？门矩阵中的复数参数，何时能够提升为下一层量子门？本文在同一五模式概率纤维上证明：两种底面三角剖分选择相反的关联端点；端点选择不是一般的仿射量子通道，但可由指定测量仪器在已知来源上实现，并在平衡底面上恰由偶奇测量实现。若固定通道对所有输入保持三个占位投影，则它必为模式基上的 Schur 通道，保持全部占位概率，却仍可改变隐藏相位。随后构造复参数的酉算符提升，证明完整黄金门的朴素自代入保持酉性却破坏编织；相对相位的受控递归则在明确谱集合中闭合。辅助谱的凸包决定一次记录耦合能否完全去相干，递归记录重叠的乘积决定可见相干何时消失。有限层级可相容、特定读出可稳定，而全算符极限仍可能不存在。这些结果把几何完成、相干变换、实际记录与观察者条件化放在一套有明确接口的静态理论中。

<strong>结论身份。</strong>本文使用有限维复 Hilbert 空间、张量结构、完全正通道与概率标定作为明示前提；不声称仅由五个标签推出全部量子公理。证明为自足纸面证明与现有数学在指定模型上的推论，未运行 Lean、CAS、数学数值程序、模拟或门搜索，也不主张一般量子仪器、Stinespring 扩张或编织理论的原创性。

> **转换说明（编者）。** 本文完整转换作者提供的 v18.0 XeLaTeX 稿件，保留各节共享陈述编号、全局公式 (1)–(10)、证明、引用及资源条件。源稿关于项目快照、历史审计、研究连续性和原创性的报告均归属于作者；转换不构成独立认证。字体、分页、页眉由 Markdown 排版替代，数学宏显式展开，目录及交叉引用使用锚点。

> **公式排版说明（编者）。** 源稿编号 `align` 按原行拆为显示公式；相干通道公式的第一行保持不编号，仅第二行标 (9)。未编号对齐式保留为对齐块。正文未作实质数学修订。

## 目录

1. [项目快照、连续性与本轮问题](#sec-1)
2. [三角剖分到底完成了什么](#sec-2)
3. [三个读出稳定时，什么隐藏关系仍能改变](#sec-3)
4. [三角剖分何时真正成为测量分支](#sec-4)
5. [矩阵中的系数如何升级为内部操作](#sec-5)
6. [复相位成为门：两种递归与相位参照](#sec-6)
7. [黄金编织允许哪一些下一层门](#sec-7)
8. [子门如何成为记录：谱凸包与三点条件](#sec-8)
9. [递归会不会终于定格：两种相反的精确结论](#sec-9)
10. [静态切面中的观察者与相容扩展](#sec-10)
11. [本轮得到的理论结构与下一步判别](#sec-11)

[文献与固定项目来源](#sec-bibliography)

<a id="sec-1"></a>

## 1. 项目快照、连续性与本轮问题

本轮核对的公开 `dev` 快照为
`23a4ae6f843d1635869b7656fb6bd681121447a8`。
该提交时间为 2026-10-30 02:29:21（Asia/Singapore），标题为“消化 Fibonacci 解析接口与统一联合律桥接追加内容”（#23795）。相对 v17 的 `d3c5bc7…`，理论目录有七条路径变化：四新增、三修改，当前理论树含 1010 个文件。五模式金字塔、黄金门及相干重构的相关定义没有因这次提交而改变。

新增的 [v16《预测、递归、最优化与变分》](https://github.com/the-omega-institute/trureturing/blob/23a4ae6f843d1635869b7656fb6bd681121447a8/docs/develop/theory/AURIC_PREDICTION_RECURSION_OPTIMIZATION_AND_VARIATION_V16.md)是此前文稿的项目转录，属于研究连续性，不构成独立验证。[合法边载荷文档](https://github.com/the-omega-institute/trureturing/blob/23a4ae6f843d1635869b7656fb6bd681121447a8/docs/develop/theory/FIB_LEGAL_EDGE_LOAD_RENEWAL_CLOSURE_SEPARATION_AND_OBSERVABLE_DEPENDENCE.md)新增 §§31--32 研究规定平稳标记律中的严格不达性，其中的离散相位不是本篇的量子相位。本轮核对的相关来源仍未提供本题所需的“塌缩等于剖分”或“整门自代入保编织”定理。

本轮重新深入读取、且与问题直接相关的已有来源是
[《五模式最小纯记录扩张》](https://github.com/the-omega-institute/trureturing/blob/23a4ae6f843d1635869b7656fb6bd681121447a8/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MINIMAL_RECORD_DILATIONS.md)。其 §§1--6 区分完整输入上的共同等距实现、后继辅助的精确边记录，以及环境单独识别边的记录任务；在它规定的十五正边模型中，三个最小环境维数分别为 $2,4,15$。该模型的配置顺序是 $(0,1,13,3,2)$，并带一个二维内部因子；不能直接当成本文顺序 $(0,1,2,3,13)$ 下的同一个 $5\times5$ 标量矩阵。

“临界矩阵”在本轮检索的相关关键文件中没有一个已经确认的统一定义。本文采用以下具体解释继续推进：研究黄金门矩阵及其非平凡二维块中的复参数 $\zeta$，把它提升为内部酉算符。若以后引入另一种临界矩阵，必须重新核对它的输入输出空间与相容方程。

本文的核心路线是：<em>先固定隐藏关系的纤维，再问什么仪器能够产生它的条件分支；先固定门的算符结构，再问递归替换保持哪些恒等式。</em>这使“全部由相融递归决定”的思想成为可检查的数学条件。

<a id="sec-2"></a>

## 2. 三角剖分到底完成了什么

<a id="statement-2-1"></a>

#### 定义 2.1（五模式纤维）

取模式

$$

\Sigma=(0,1,2,3,13)=(000,100,010,001,101),

$$

其中位串按左、中、右排列。几何坐标按左、右、中排列：

$$

v_0=0,\quad v_1=e_x,\quad v_2=e_z,\quad
v_3=e_y,\quad v_{13}=e_x+e_y.

$$

对概率律 $p$，记

$$

X=p_1+p_{13},\quad Y=p_3+p_{13},\quad Z=p_2,
\quad R=1-Z,\quad\kappa=p_{13}.

$$

给定可行 $(X,Y,Z)$，所有完成构成闭区间纤维

<a id="eq-fiber"></a>

$$

p_\kappa=(R-X-Y+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
\tag{1}

$$

<a id="eq-endpoints"></a>

$$

\kappa_-=\max(0,X+Y-R),\qquad
\kappa_+=\min(X,Y).
\tag{2}

$$

其中 $0\le Z\le1$、$0\le X,Y\le R$。$R=0$ 时只有模式 $2$，纤维退化。

<a id="statement-2-2"></a>

<a id="thm-triangulation"></a>

#### 定理 2.2（两种底面剖分选择两个关联端点）

对固定金字塔均值点，使用底面对角线 $0$--$13$ 的三角剖分，再向顶点 $2$ 作锥，用所含单形的重心坐标完成五模式律，所得为 $p_{\kappa_+}$。使用底面对角线 $1$--$3$，所得为 $p_{\kappa_-}$。在每一种剖分内部，相邻单形在公共面上的完成一致。

**证明。** 
底面对角线 $0$--$13$ 的两个三角形分别省略 $3$ 或 $1$。相应四面体完成满足 $p_3=0$ 或 $p_1=0$，由[(1)](#eq-fiber)得到 $\kappa=Y$ 或 $X$；非负性选择两者的较小值。另一剖分的两个底面三角形分别省略 $13$ 或 $0$，得到 $\kappa=0$ 或 $X+Y-R$，非负性选择较大值。边界上相应被省略的概率同时为零，故两侧计算相同。
 ∎

这一定理所说的“选择”，是选择均值映射 $p\mapsto(X,Y,Z)$ 的一个分段仿射截面。它还没有给出一个物理仪器、一次实际记录或分支概率。尤其，$p_{\kappa_\pm}$ 通常仍是多个模式的混合律；到达纤维端点不等于到达一个纯量子态。

<a id="statement-2-3"></a>

<a id="prop-nonaffine"></a>

#### 命题 2.3（端点截面不是全局仿射通道）

以输入的三个均值为参数，把任意 $p$ 送到 $p_{\kappa_+}$ 或 $p_{\kappa_-}$ 的规则，一般不是仿射映射。因此不能直接作为一个固定、非选择、确定性的量子通道在对角态上的作用。

**证明。** 
记 $\delta_s$ 为模式 $s$ 的点质量。上端点规则在 $\delta_1,\delta_3$ 上分别固定它们，但将

$$

\tfrac12(\delta_1+\delta_3)
\longmapsto\tfrac12(\delta_0+\delta_{13}).

$$

下端点规则则固定 $\delta_0,\delta_{13}$，却将它们的等权混合送到 $\tfrac12(\delta_1+\delta_3)$。两者均不保持混合。量子通道的线性限制到对角态必然保持混合，故不可能。
 ∎

选择一个三角剖分也可以只是改变坐标表达。若在另一个给定的融合空间中，用 $F$ 矩阵改变融合树基底，这是可逆的相干基变换；还需要真实的测量仪器，才能称为条件测量。Fibonacci 融合矩阵与编织矩阵的这种区别在原始文献 （[3](#ref-hg)） 中是明确的。本文的概率金字塔底面翻转，并未自动提供一个融合范畴的 $F$ 符号或五边形恒等式。

<a id="sec-3"></a>

## 3. 三个读出稳定时，什么隐藏关系仍能改变

<a id="statement-3-1"></a>

#### 定义 3.1（占位投影与通道稳定）

在 $H_5=\mathbb{C}^\Sigma$ 中，令

$$

N_x=\operatorname{diag}(0,1,0,0,1),\quad
N_y=\operatorname{diag}(0,0,0,1,1),\quad
N_z=\operatorname{diag}(0,0,1,0,0).

$$

它们两两对易，且 $N_xN_y=\lvert 13\rangle\langle 13\rvert$。固定 CPTP 通道 $\Lambda$ 对所有输入保持三读出，是指

$$

\Lambda^\dagger(N_a)=N_a\quad(a=x,y,z),

$$

等价于对每个密度算符 $\rho$ 都保持对应期望。这里不是只对某个已知 $\rho$ 成立。

<a id="statement-3-2"></a>

<a id="thm-schur"></a>

#### 定理 3.2（三投影稳定的完整通道分类）

对 $H_5$ 上的 CPTP 通道，下列两条等价：

1.  对所有输入保持 $N_x,N_y,N_z$；

2.  存在正半定矩阵 $C$，$C_{ss}=1$，使

$$

\Lambda(\rho)=C\odot\rho,

$$

其中 $\odot$ 是模式基上的逐项乘积。

因此这样的通道保持全部 $p_s=\rho_{ss}$，尤其保持 $\kappa$。它仍可以改变非对角相干。

**证明。** 
写 $\Lambda(\rho)=\sum_aL_a\rho L_a^\dagger$，$\sum_aL_a^\dagger L_a=I$。对任意固定投影 $N$，由 $\Lambda^\dagger(N)=N$ 得

$$

\begin{aligned}
\sum_a[N,L_a]^\dagger[N,L_a]
&=\Lambda^\dagger(N)-\Lambda^\dagger(N)N
 -N\Lambda^\dagger(N)+N\\
&=0.
\end{aligned}

$$

每项均正半定，故每个 $L_a$ 都与 $N$ 对易。对三个 $N$ 同时应用此结论。五个模式的三元联合本征值各不相同，联合本征空间均一维，因此每个 $L_a$ 在模式基上对角。若对角元为 $\ell_{a,s}$，则

$$

C_{st}=\sum_a\ell_{a,s}\overline{\ell_{a,t}},\qquad C\ge0,\quad C_{ss}=1,

$$

且通道恰为上述 Schur 形式。反之，对 $C$ 作 Gram 分解给出这样的对角 Kraus 算子，立即得到 CPTP 与三读出稳定。
 ∎

这个结果并不禁止测量。精确测量全部五模式、仅测某种占位关系、或只泄漏部分记录，都可给出此类通道。它禁止的是：一个固定非选择操作在<em>对所有输入都保持三读出</em>的同时，普遍修改 $\kappa$。

<a id="statement-3-3"></a>

<a id="cor-robust"></a>

#### 推论 3.3（稳定性带有限误差时的边界）

若 $\Lambda$ 为 CPTP，且

$$

\left\lVert \Lambda^\dagger(N_x)-N_x\right\rVert\le\varepsilon_x,
\qquad\left\lVert \Lambda^\dagger(N_y)-N_y\right\rVert\le\varepsilon_y,

$$

则

$$

\boxed{\left\lVert \Lambda^\dagger(N_xN_y)-N_xN_y\right\rVert
\le\sqrt{\varepsilon_x}+\sqrt{\varepsilon_y}.}

$$

从而任意输入的 $|\Delta\kappa|$ 服从同界。该常数不声称最优。

**证明。** 
取等距表示 $V$，使 $\Lambda^\dagger(A)=V^\dagger(A\otimes I)V$。对投影 $N$ 置

$$

E_N=\Lambda^\dagger(N)-N,\qquad
D_N=(N\otimes I)V-VN.

$$

直接展开得 $D_N^\dagger D_N=E_N-E_NN-NE_N$。相对 $\operatorname{Ran}N\oplus\ker N$，此算符是 $\operatorname{diag}(-E_{11},E_{00})$，故 $\left\lVert D_N\right\rVert\le\sqrt{\left\lVert E_N\right\rVert}$。再用

$$

(N_xN_y\otimes I)V-VN_xN_y
=(N_x\otimes I)D_{N_y}+D_{N_x}N_y,

$$

左乘 $V^\dagger$ 并取范数即得。
 ∎

这回答了“尺子也测不准”的一个有限模型版本：若连读出操作也仅近似稳定，必须把误差放进假设。仅对一态的三次期望近似相同，不足以提供本推论要求的对全部态的算子范数保证。

<a id="statement-3-4"></a>

<a id="prop-phase"></a>

#### 命题 3.4（稳定概率与活动的相位）

所有保持三占位投影的酉通道都由模式基上的对角酉矩阵实现。对

$$

\lvert \psi\rangle=\sum_s\alpha_s\lvert s\rangle,\qquad
\Omega=\frac{\alpha_0\alpha_{13}}{\alpha_1\alpha_3},

$$

假设四个底面振幅均非零。对角相位门 $D=\operatorname{diag}(e^{i\chi_s})$ 给出

$$

\Omega'=
e^{i(\chi_0+\chi_{13}-\chi_1-\chi_3)}\Omega.

$$

所有占位概率、三均值和 $|\Omega|$ 均不变，但四角关系的相位可以改变。

**证明。** 
酉通道稳定投影等价于 $D^\dagger N_aD=N_a$，从而 $D$ 与三个 $N_a$ 对易，联合谱简单迫使其对角。逐个代入 $\alpha'_s=e^{i\chi_s}\alpha_s$ 即得。
 ∎

例如

$$

\lvert \Psi_\pm\rangle=\frac{\lvert 000\rangle+\lvert 100\rangle+\lvert 010\rangle+\lvert 001\rangle\pm\lvert 101\rangle}{\sqrt5}

$$

具有同一概率律。条件于中位为 $0$ 后，$\Psi_+$ 的两个端点是乘积态，$\Psi_-$ 的端点是最大纠缠纯态：其归一振幅矩阵分别为

$$

\tfrac12\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad
\tfrac12\begin{pmatrix}1&1\\1&-1\end{pmatrix}.

$$

前者秩一，后者的约化态为 $I/2$。这是给定复 Hilbert 与两端张量分割下的例子，不额外声称这些精确态或相位门可由有限原生黄金门词制备。

<a id="sec-4"></a>

## 4. 三角剖分何时真正成为测量分支

<a id="statement-4-1"></a>

#### 定义 4.1（操作意义的条件塌缩）

有限量子仪器是完全正映射族 $\{\mathcal I_o\}$，其和为迹保持通道。读得实际记录 $o$ 后，若

$$

q_o=\operatorname{Tr}\mathcal I_o(\rho)>0,

$$

条件态为 $\rho_o=\mathcal I_o(\rho)/q_o$。本文把这一<em>有实际记录的条件化</em>称为操作意义的塌缩；不由此选择一种关于客观波函数塌缩的解释。遗忘记录时，态为 $\sum_o\mathcal I_o(\rho)$。

<a id="statement-4-2"></a>

<a id="thm-endpointinstrument"></a>

#### 定理 4.2（给定来源的端点仪器）

给定 $p=p_\kappa$，且 $\kappa_-<\kappa<\kappa_+$。令

$$

w_+=\frac{\kappa-\kappa_-}{\kappa_+-\kappa_-},\qquad
w_-=1-w_+.

$$

存在二结果对角仪器，其在输入 $\rho=\operatorname{diag} p$ 上，以概率 $w_\pm$ 产生条件态 $\operatorname{diag} p_{\kappa_\pm}$。两个条件态分别实现两种三角剖分完成，并且各自具有原来的三个均值。

**证明。** 
纤维对 $\kappa$ 仿射，所以

$$

p=w_+p_{\kappa_+}+w_-p_{\kappa_-}.

$$

对 $p_s>0$，定义

$$

(M_\pm)_{ss}=\sqrt{\frac{w_\pm(p_{\kappa_\pm})_s}{p_s}}.

$$

上式的两个平方相加为 $1$。若 $p_s=0$，则两个加权端点概率也为 $0$；可在该未占据分量定义 $(M_+)_{ss}=1,(M_-)_{ss}=0$，使完备关系在全空间成立。于是 $M_+^\dagger M_++M_-^\dagger M_-=I$，且

$$

M_\pm\operatorname{diag}(p)M_\pm^\dagger=w_\pm\operatorname{diag}(p_{\kappa_\pm}).

$$

这同时证明分支概率及条件态结论。
 ∎

该仪器由<em>给定的来源</em> $p$ 标定。它作为固定仪器可作用于任意态，但在别的未知输入上不再保证选择该输入的两个纤维端点。端点处只剩一个有正概率的目标分支；纤维宽度为零时不存在非平凡二完成。

同样的 Kraus 算子作用于具有相同对角 $p$ 的相干态时，分支<em>对角</em>仍为这些端点，分支的非对角元则由仪器决定。特别是，不能从 $p=w_+p_++w_-p_-$ 推出任意同对角纯态也等于那两个对角态的混合。

理由很直接：若 $\lvert \psi\rangle\langle \psi\rvert=\sum_oq_o\rho_o$ 且 $q_o>0$，对每个 $v\perp\psi$ 有 $\sum_oq_o\langle v,\rho_ov\rangle=0$。正性使每项为零，故每个 $\rho_o$ 的支撑都在 $\operatorname{span}\{\psi\}$ 中，只能等于原纯态。一个纯态不能在保持非选择态不变时拆成不同后态。

五个模式全部出现的具体例子是 $p_s=1/5$。此时两个 Kraus 算子可取

$$

M_+=\operatorname{diag}(1,0,1/\sqrt2,0,1),\qquad
M_-=\operatorname{diag}(0,1,1/\sqrt2,1,0).

$$

两结果各以 $1/2$ 出现，其条件对角分别为

$$

p_+=(\tfrac25,0,\tfrac15,0,\tfrac25),\qquad
p_-=(0,\tfrac25,\tfrac15,\tfrac25,0).

$$

它们各自仍有 $(X,Y,Z)=(2/5,2/5,1/5)$，而隐藏关系取相反端点。这是抽象仪器的精确构造，未附加有限原生黄金门词的精确实现结论。

<a id="statement-4-3"></a>

<a id="thm-parity"></a>

#### 定理 4.3（平衡底面上，偶奇测量恰实现两种剖分）

在 $Z=0,X=Y=1/2$ 的整个纤维上，

$$

p_\kappa=(\kappa,\tfrac12-\kappa,0,\tfrac12-\kappa,\kappa),
\quad0\le\kappa\le\tfrac12.

$$

固定投影

$$

E=\lvert 0\rangle\langle 0\rvert+\lvert 13\rangle\langle 13\rvert,\qquad O=I-E

$$

的 Lüders 测量，在其正概率分支中，给出

$$

\begin{aligned}
\Pr(E)&=2\kappa,&p_{\mid E}&=(\tfrac12,0,0,0,\tfrac12)=p_{\kappa_+},\\
\Pr(O)&=1-2\kappa,&p_{\mid O}&=(0,\tfrac12,0,\tfrac12,0)=p_{\kappa_-}.
\end{aligned}

$$

因此在这个明确受限来源类上，两种剖分完成确实是一次固定测量的两个可能条件结果。

**证明。** 
偶子空间只保留 $0,13$，奇子空间在该输入支撑中只保留 $1,3$。分别求迹并归一化即得。若某概率为零，该条件分支不定义，也不会被读到。
 ∎

对相干态 $\lvert +\rangle\lvert +\rangle$ 的两个端点（中位固定 $0$），同一偶奇测量给出 Bell 态 $(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$ 或 $(\lvert 10\rangle+\lvert 01\rangle)/\sqrt2$，各以概率 $1/2$。若先分别测量两端再只公布偶奇，条件态则是对角混合。<strong>相同端点概率、相同剖分标签，可以对应不同的量子仪器与不同纠缠。</strong>

<a id="statement-4-4"></a>

<a id="prop-dilation"></a>

#### 命题 4.4（记录扩张与可逆的全局描述）

若 $\sum_oM_o^\dagger M_o=I$，则

$$

V\lvert \psi\rangle=\sum_oM_o\lvert \psi\rangle\otimes\lvert o\rangle

$$

是等距映射，可扩张为系统加纯准备记录上的酉作用。读取记录得到对应仪器，遗忘记录得到其非选择通道。

**证明。** 
记录正交给 $V^\dagger V=\sum_oM_o^\dagger M_o=I$。在有限维扩展空间中把正交像补成一组正交基，即得到酉扩张。取记录的矩阵元或偏迹分别给出选择分支与非选择通道。
 ∎

因此，“局部条件态变了”和“系统、记录的整体保持酉性”完全相容。这个数学描述未从整体酉性独自推导出某一次唯一记录为何实际发生；记录取得仍是操作接口的一部分。一般仪器及扩张的有限维基础见 （[2](#ref-watrous)）。

<a id="sec-5"></a>

## 5. 矩阵中的系数如何升级为内部操作

<a id="statement-5-1"></a>

#### 定义 5.1（带内部操作与记录的配置核）

令 $T_{ji}\ge0$ 是从输入配置 $i$ 到输出配置 $j$ 的权重，$U_{ji}$ 为共同内部空间 $K$ 上的酉算符，$e_{ji}$ 为共同记录空间中的单位向量。定义

$$

V(\lvert i\rangle\otimes\psi)
=\sum_j\sqrt{T_{ji}}\lvert j\rangle\otimes U_{ji}\psi\otimes e_{ji}.

$$

所有边使用同一个内部空间、同一个记录空间，以及同一套相位约定。

<a id="statement-5-2"></a>

<a id="thm-blocks"></a>

#### 定理 5.2（递归系数的完整相容方程）

上述映射在任意相干输入及任意内部向量上等距，当且仅当对全部 $i,k$ 有

<a id="eq-blockcondition"></a>

$$

\boxed{\sum_j\sqrt{T_{ji}T_{jk}}
\langle e_{ji},e_{jk}\rangle U_{ji}^\dagger U_{jk}
=\delta_{ik}I_K.}
\tag{3}

$$

逐列概率归一化只检验了 $i=k$；把每个系数独立替换成某个酉门，不保证 $i\ne k$ 的交叉条件。

**证明。** 
计算 $\langle V(\lvert i\rangle\psi),V(\lvert k\rangle\phi)\rangle$，输出配置正交使两重求和只剩同一 $j$。所得为 $\langle\psi,A_{ik}\phi\rangle$，其中 $A_{ik}$ 恰为框中左侧。要求其等于 $\delta_{ik}\langle\psi,\phi\rangle$ 对任意 $\psi,\phi$ 成立，等价于该算符恒等式。
 ∎

这一条件正是项目《最小纯记录扩张》式 (1.5) 的同一结构，其中本文 $T_{ji}$ 对应原文的源行矩阵 $P_{ij}$。该来源证明一个共同二维记录构造可在全十维输入上等距，并非仅在五个基输入上概率归一。它的两个记录结果对应两种整体酉变换；取得记录并施加相应逆门，可以恢复输入及其参考纠缠。记录标签的含义必须由这套共同构造决定。

<a id="statement-5-3"></a>

#### 命题 5.3（黄金归一块可以含有下一层门）

设 $a,b\in\mathbb{R}$，$a^2+b^2=1$，$W$ 为酉算符，则

$$

F_W=\begin{pmatrix}aI&bW\\bW^\dagger&-aI\end{pmatrix}

$$

满足 $F_W^\dagger=F_W$、$F_W^2=I$。特别可取 $a=\varphi^{-1},b=\varphi^{-1/2}$。

**证明。** 
两对角块的平方和均为 $(a^2+b^2)I$，非对角块分别是 $abW-abW$ 及其伴随，故为零。
 ∎

这给出一种字面上的递归替换，但两个非对角块必须彼此伴随。如果把 $a,b$ 也提升为自伴算符，块 $\bigl(\begin{smallmatrix}A&B\\B&-A\end{smallmatrix}\bigr)$ 的平方非对角元是 $[A,B]$；此形式保酉需要 $A^2+B^2=I$ 与 $[A,B]=0$。任意替换会损坏相消关系。

模小于 $1$ 的标量系数本身也不是一个确定性酉门：$(cI)^\dagger(cI)=|c|^2I$。它可以是较大酉门的一块或某个测量分支。对同一有限维空间上的任意收缩算符 $A$，一个明确的完成是

$$

J(A)=\begin{pmatrix}
A&(I-AA^\dagger)^{1/2}\\
(I-A^\dagger A)^{1/2}&-A^\dagger
\end{pmatrix}.

$$

此矩阵酉。证明可将 $A=L\Sigma R^\dagger$ 作奇异值分解，左右酉变换后得到逐奇异值的实二维块 $\bigl(\begin{smallmatrix}s&\sqrt{1-s^2}\\\sqrt{1-s^2}&-s\end{smallmatrix}\bigr)$。这是标准的 Halmos 酉扩张，亦见 （[5](#ref-robinson)）。被补上的通道就是保留总范数所必需的自由度。

<a id="sec-6"></a>

## 6. 复相位成为门：两种递归与相位参照

<a id="statement-6-1"></a>

<a id="def-lifts"></a>

#### 定义 6.1（相对相位提升与整门提升）

设 $P$ 为父系统上的正交投影，$W$ 为子系统上的酉算符，定义

<a id="eq-controlled"></a>

$$

\mathcal C_P(W)=(I-P)\otimes I+P\otimes W,
\tag{4}

$$

<a id="eq-wholelift"></a>

$$

\mathcal L_P(W)=(I-P)\otimes W+P\otimes W^2.
\tag{5}

$$

取一维子空间及标量 $W=z$，$|z|=1$，有

$$

\mathcal C_P(z)=I+(z-1)P,\qquad
\mathcal L_P(z)=z[I+(z-1)P].

$$

因此 $\mathcal L_P(\zeta)$ 正好还原黄金门的整体系数形式。

<a id="statement-6-2"></a>

<a id="thm-lifts"></a>

#### 定理 6.2（酉递归成立，但组合律不同）

两种提升均为酉算符，且对整数 $m$ 有

$$

\mathcal C_P(W)^m=\mathcal C_P(W^m),\qquad
\mathcal L_P(W)^m=\mathcal L_P(W^m).

$$

若 $W^{10}=I$，两者均为十周期或十周期的约数。另有

$$

\mathcal C_P(UV)=\mathcal C_P(U)\mathcal C_P(V)

$$

对任意酉 $U,V$ 成立；当 $P\ne0$ 时，

$$

\mathcal L_P(UV)=\mathcal L_P(U)\mathcal L_P(V)
\quad\Longleftrightarrow\quad UV=VU.

$$

**证明。** 
$P$ 与 $I-P$ 为互相正交的控制扇区；分别在两扇区检查即得酉性与幂公式。$\mathcal C$ 的两个扇区分别乘出 $I$ 与 $UV$。$\mathcal L$ 在 $I-P$ 扇区没有差异，在非零 $P$ 扇区则要求 $(UV)^2=U^2V^2$；左乘 $U^{-1}$、右乘 $V^{-1}$ 后等价于 $VU=UV$。
 ∎

这就是“相位也可以是一段门过程”的一个严格版本。它作用在更大的张量空间；下一层自由度没有凭空消失。即使子门是确定的，父系统与子系统也可因控制扇区的相干叠加而纠缠。

<a id="statement-6-3"></a>

<a id="thm-phase-reference"></a>

#### 定理 6.3（整体相位在下一层变成相对相位）

对任意实数 $\chi$，

$$

\begin{aligned}
\mathcal C_P(e^{i\chi}W)
&=[(I-P+e^{i\chi}P)\otimes I]\,\mathcal C_P(W),\\
\mathcal L_P(e^{i\chi}W)
&=e^{i\chi}[(I-P+e^{i\chi}P)\otimes I]\,\mathcal L_P(W).
\end{aligned}

$$

若 $0\ne P\ne I$ 且 $e^{i\chi}\ne1$，右侧新增的受控相位一般可观测。因此提升规则不能只由子门的射影酉等价类 $[W]\in PU(H)$ 唯一定义。

**证明。** 
分别代入两个控制扇区即可。新增因子在 $I-P$ 与 $P$ 扇区有不同本征值。对同时具有两扇区分量的纯态，它改变相对相位；不是整个父子系统上的统一标量。
 ∎

所以，某个相位在一个观察切面上是不可见的，在把该过程相干嵌入另一过程后可能成为关系的一部分。这与“关系也需要预测和标定”的直觉直接相连：相位参照是递归接口的数据。

抽象地给出 $\mathcal C_P(W)$，不等于可从一个完全未知、只定义到整体相位的黑箱免费制造该受控门。原始不可控未知操作定理 （[4](#ref-araujo)） 正是检验这一点；已知的门分解、已知谱向量或物理旁路可以提供额外结构。这里的构造使用已给定的 $W$ 及其相位约定，不把这一实现问题藏在符号替换中。

<a id="sec-7"></a>

## 7. 黄金编织允许哪一些下一层门

<a id="statement-7-1"></a>

#### 定义 7.1（黄金投影与相对编织）

置

$$

\varphi=\frac{1+\sqrt5}{2},\qquad
\lambda=\varphi^{-2},\qquad \zeta=e^{3\pi i/5}.

$$

在同一父空间上取不同的非零正交投影 $P,Q$，满足

$$

PQP=\lambda P,\qquad QPQ=\lambda Q.

$$

这里“正交投影”指自伴幂等；不指 $PQ=0$。项目的相邻投影关系须在已指定的合法路径或融合扇区上使用，不能无条件推广到任意物理位串空间。

在项目的五模式顺序中，具体原子投影为

$$

\lvert v\rangle=\varphi^{-1/2}\lvert 000\rangle+\varphi^{-1}\lvert 010\rangle,\qquad
P_A=\lvert v\rangle\langle v\rvert+\lvert 101\rangle\langle 101\rvert,

$$

其中 $\langle v,v\rangle=\varphi^{-1}+\varphi^{-2}=1$，黄金门为

$$

K_A=\zeta(I-P_A)+\zeta^2P_A.

$$

下面的算符参数定理应用于这种两谱形式。编织投影 $P,Q$ 也不能与第三节的占位投影 $N_x,N_y,N_z$ 混同：后者两两对易，并不自动满足本节非平凡的相邻重叠关系。

<a id="statement-7-2"></a>

<a id="thm-braidspectrum"></a>

#### 定理 7.2（算符参数的精确编织谱条件）

更一般地取 $0<\lambda<1$，在上述投影关系下，使用<em>同一个</em>子算符 $W$ 的两提升门满足

$$

\mathcal C_P(W)\mathcal C_Q(W)\mathcal C_P(W)
=\mathcal C_Q(W)\mathcal C_P(W)\mathcal C_Q(W)

$$

当且仅当

<a id="eq-braidpoly"></a>

$$

\boxed{(W-I)\,[W+\lambda(W-I)^2]=0.}
\tag{6}

$$

将全部 $\mathcal C$ 换成 $\mathcal L$，条件相同。黄金 $\lambda=\varphi^{-2}$ 时，等价条件为

<a id="eq-allowed"></a>

$$

\boxed{\operatorname{spec}(W)\subseteq\{1,\zeta,\bar\zeta\}.}
\tag{7}

$$

**证明。** 
令 $A=W-I$。按 $I+P\otimes A$、$I+Q\otimes A$ 展开两边的三重乘积，二阶共同项相消，得到

$$

(P-Q)\otimes(A+A^2+\lambda A^3).

$$

因 $P-Q\ne0$，张量积为零等价于第二因子为零。$A+A^2+\lambda A^3=(W-I)[W+\lambda(W-I)^2]$，即得。又

$$

\mathcal L_P(W)=(I\otimes W)\mathcal C_P(W),

$$

公共因子与全部提升门对易且可逆，两边均有 $(I\otimes W^3)$，故条件不变。

有限维酉 $W$ 可谱分解，算符多项式为零当且仅当每个本征值满足相应标量方程。非平凡根由

$$

z+\lambda(z-1)^2=0

$$

给出。黄金情况下，除以 $\lambda z$ 得

$$

z+z^{-1}=2-\lambda^{-1}=2-\varphi^2=-\varphi^{-1},

$$

故根为 $e^{\pm3\pi i/5}$；另外保留首因子的根 $1$。不能在含 $1$ 的谱扇区上约掉 $W-I$。
 ∎

这一结论是指定共享算符参数形式的完整分类。允许的非标量 $W$ 可以有多个谱扇区，但在其谱基上是平凡编织与两种共轭手性的直和。它不是所有可能非交换算符值编织的分类；若不同边使用不同、非交换的子参数，必须重新求解完整 Yang--Baxter 型方程。

<a id="statement-7-3"></a>

<a id="cor-wholefails"></a>

#### 推论 7.3（整块黄金门直接自代入不保持编织）

设子投影 $R_0$ 满足 $0\ne R_0\ne I$，原生门为

$$

K_{R_0}=\zeta(I-R_0)+\zeta^2R_0.

$$

则 $\mathcal L_P(K_{R_0})$ 是酉门且十次为恒等，但将同一个 $K_{R_0}$ 作为相邻黄金父门的参数时，编织关系不成立。

**证明。** 
子门的两个本征值为 $\zeta,\zeta^2$，均为十次单位根，故用定理[6.2](#thm-lifts)得到酉性与周期性。因 $\zeta$ 为本原十次单位根，$\zeta^2$ 既不是 $1$，也不是 $\zeta$ 或 $\zeta^{-1}$，违反[(7)](#eq-allowed)。
 ∎

因此，“每层都是酉门”与“每层都满足同一黄金编织逻辑”是两个不同的可检验命题。这个反例是后续递归理论必须满足的约束，而不是把递归本身否定掉。

<a id="statement-7-4"></a>

<a id="thm-closedrecursion"></a>

#### 定理 7.4（相对相位的保编织递归）

若 $\operatorname{spec}(W)\subseteq\{1,\zeta,\bar\zeta\}$，则

$$

\operatorname{spec}\mathcal C_P(W)\subseteq\{1,\zeta,\bar\zeta\}.

$$

故相对相位提升在该谱类中闭合。特别令一维初值 $W_0=\zeta$，每层增加一个新父因子与投影 $P_n$，定义 $W_n=\mathcal C_{P_n}(W_{n-1})$，则

<a id="eq-productrecursion"></a>

$$

\boxed{W_n=I+(\zeta-1)E_n,\qquad
E_n=P_n\otimes\cdots\otimes P_1.}
\tag{8}

$$

任意有限层级均酉，并可作为下一对合法黄金父投影的编织参数。

**证明。** 
相对提升在父 $I-P$ 扇区为恒等，在父 $P$ 扇区为 $W$，故谱至多添上 $1$。将 $W_{n-1}=I+(\zeta-1)E_{n-1}$ 代入，得到 $I+(\zeta-1)P_n\otimes E_{n-1}$，归纳即得。
 ∎

这条递归有非常简单的含义：只有全部控制条件同时成立时才施加相位。若始终固定这些局部控制投影，这些门属于对易控制结构；本定理没有证明任意量子计算的普适性。

另可取一个递归生成的子投影 $R_0$，构造

$$

W_\chi=\zeta(I-R_0)+\bar\zeta R_0.

$$

它同样满足允许谱条件，而且代数上

$$

W_\chi=\zeta^3K_{R_0}^{8}.

$$

两个谱扇区分别给出指数 $11$ 与 $19$，模 $10$ 为 $1$ 与 $9$，即得该式。这里的相位校正、控制与投影构造仍需作为资源给出；不能在下一层把 $\zeta^3$ 当作无关整体相位随意删除。

<a id="sec-8"></a>

## 8. 子门如何成为记录：谱凸包与三点条件

<a id="statement-8-1"></a>

<a id="thm-moment"></a>

#### 定理 8.1（一个谱矩控制父系统的相干）

设父投影 $0\ne P\ne I$。父输入为 $\rho$，子输入为 $\sigma$，两者初始为乘积态。令

$$

m=\operatorname{Tr}(\sigma W).

$$

施加 $\mathcal C_P(W)$ 或 $\mathcal L_P(W)$ 并对全部子系统取偏迹，父系统得到同一通道

$$

\Lambda_m(\rho)={}(I-P)\rho(I-P)+P\rho P

$$

<a id="eq-coherence"></a>

$$

+\bar m(I-P)\rho P+mP\rho(I-P).
\tag{9}

$$

特别 $|m|\le1$；$m=0$ 时恰为 $P$ 的非选择 Lüders 通道；$|m|=1$ 时该父通道只是两扇区间的酉相位变换。

**证明。** 
按父投影的四个块展开。对 $\mathcal C$ 的交叉块，偏迹系数分别为 $\operatorname{Tr}(\sigma W^\dagger)$ 与 $\operatorname{Tr}(W\sigma)$。对 $\mathcal L$，系数变为 $\operatorname{Tr}(W\sigma W^{\dagger2})=\bar m$ 及其共轭，故相同。$|m|\le1$ 由酉算符的谱分解及概率凸组合得到。其余结论直接代入。
 ∎

<a id="statement-8-2"></a>

<a id="prop-recordpurity"></a>

#### 命题 8.2（去相干与可读记录的区别）

若 $\sigma=\lvert \chi\rangle\langle \chi\rvert$ 为纯态，则 $\mathcal C$ 的两个条件指针为 $\lvert \chi\rangle,W\lvert \chi\rangle$，$\mathcal L$ 的两个指针为 $W\lvert \chi\rangle,W^2\lvert \chi\rangle$；两组的重叠均为 $m$。因此 $m=0$ 当且仅当这两个纯指针正交，此时可读指针测量给出 $P\rho P$ 与 $(I-P)\rho(I-P)$ 两支。

若 $\sigma$ 混合，$m=0$ 只保证父通道去相干，不保证子系统自身携带可区分的指针。

**证明。** 
纯态结论由内积与正交投影测量直接得到。反例取 $\sigma=I_2/2$、$W=\operatorname{diag}(1,-1)$，则 $m=0$，但两个条件子态都为 $I_2/2$，不能由子系统单独区分。把纯化参考一起计入记录后，两条件纯化态的重叠才由 $m$ 描述。
 ∎

<a id="statement-8-3"></a>

<a id="prop-internalvariance"></a>

#### 命题 8.3（有效复系数的勾股分解）

对 $m=\operatorname{Tr}(\sigma W)$，有

$$

\boxed{1=|m|^2+\operatorname{Tr}\!\left[\sigma(W-mI)^\dagger(W-mI)\right].}

$$

因而 $|m|=1$ 当且仅当 $\operatorname{supp}\sigma$ 完全位于 $W$ 的同一个本征值 $m$ 的谱空间中。每个 $|m|\le1$ 都能成为某个内部酉门的这种有效系数；当 $|m|<1$ 时，最小一般子空间维数为 $2$。

**证明。** 
展开迹，利用 $W^\dagger W=I$、$\operatorname{Tr}\sigma W=m$，得到右侧第二项为 $1-|m|^2$。该项也是 $\left\lVert (W-mI)\sqrt\sigma\right\rVert_{\mathrm{HS}}^2$，故等号饱和等价于 $(W-mI)\sqrt\sigma=0$。任意单位盘内的 $m$ 可取

$$

W_m=\begin{pmatrix}
m&\sqrt{1-|m|^2}\\
\sqrt{1-|m|^2}&-\bar m
\end{pmatrix},\qquad\sigma=\lvert 0\rangle\langle 0\rvert.

$$

这是上一节收缩块的酉完成，且 $\langle0,W_m0\rangle=m$。一维酉算符的期望模恒为 $1$，故严格内部点至少要求二维，以上构造达到界。
 ∎

所以，一个复系数确实可以压缩一段内部酉过程。若要求这个系数<em>恰好</em>仍是模一的黄金相位，则在所给准备上，子过程不能同时留下区分父控制扇区的记录；这种记录需要非零的内部变差。一般的 $W_m$ 也不自动满足黄金编织谱条件，下面必须再检验其谱。

<a id="statement-8-4"></a>

<a id="thm-hull"></a>

#### 定理 8.4（谱凸包的记录判据）

在有限维子空间上，存在某个输入 $\sigma$ 使 $\operatorname{Tr}(\sigma W)=0$，当且仅当

$$

0\in\operatorname{conv}\operatorname{spec}(W).

$$

只要此条件成立，也存在纯输入达到它。

**证明。** 
写 $W=\sum_jz_j\Pi_j$，则 $m=\sum_jq_jz_j$，其中 $q_j=\operatorname{Tr}(\sigma\Pi_j)\ge0$、$\sum_jq_j=1$，故必要。反之，若 $\sum_jq_jz_j=0$，在每个对应谱空间取单位向量 $u_j$，令 $\lvert \chi\rangle=\sum_j\sqrt{q_j}u_j$，即可得到同样谱权重及 $m=0$。
 ∎

这把复平面的几何与实际可读记录接上了：是否能形成正交记录，取决于可访问的谱点是否能够用正权围住原点。它比“参数是复数”或“矩阵酉”更强。

<a id="statement-8-5"></a>

<a id="thm-goldenrecord"></a>

#### 定理 8.5（黄金允许谱的一层最小记录维数）

设父投影 $0\ne P\ne I$。在共享参数、黄金编织条件[(7)](#eq-allowed)及单次提升[(4)](#eq-controlled)或[(5)](#eq-wholelift)的形式下，存在纯子输入，使全部父输入都实现 $P/(I-P)$ 间的非选择 Lüders 通道并具有正交指针，当且仅当子谱同时包含

$$

1,\quad\zeta,\quad\bar\zeta.

$$

因此在这个受限形式中子空间的最小维数为 $3$。实现 $m=0$ 的三个总谱权重唯一，为

<a id="eq-goldenweights"></a>

$$

\boxed{q_1=\varphi^{-3},\qquad q_\zeta=q_{\bar\zeta}=\varphi^{-2}.}
\tag{10}

$$

**证明。** 
三个允许点的任意两个均不互为对径点，其线段不含原点。故谱若缺一个点，定理[8.4](#thm-hull)排除完全去相干。若三个点齐全，虚部为零迫使 $q_\zeta=q_{\bar\zeta}=q$。由

$$

\zeta+\bar\zeta=-\varphi^{-1}

$$

及归一化，得 $q_1=q/\varphi$、$q_1+2q=1$，解出[(10)](#eq-goldenweights)。这些数为正；取相应三个本征向量的纯叠加即实现。三个非零谱扇区至少要求三维，而三维对角 $W$ 足够。
 ∎

这不是一般二结果测量需要三维的定理。普通受控 $X$ 配一个纯比特已能测量投影，但 $\{1,-1\}$ 不是这里的黄金编织允许谱。项目的 $d_{\mathrm{un}}=2$ 也对应另一种配置核与另一个记录任务，和此处没有冲突。这里的“三点”更不能被直接认作物理空间三维或三个占位读出。

<a id="statement-8-6"></a>

<a id="cor-thresholds"></a>

#### 推论 8.6（编织存在与单层记录的两个阈值）

在定理[7.2](#thm-braidspectrum)的同一共享参数形式中，令 $0<\lambda<1$。非平凡单位模编织参数存在当且仅当 $\lambda\ge1/4$。允许谱可以在一次耦合中实现 $m=0$，当且仅当

$$

\frac14\le\lambda\le\frac12.

$$

最小子空间维数在两个端点为 $2$，在开区间内为 $3$。开区间内三个总谱权重为

$$

(q_1,q_+,q_-)=(1-2\lambda,\lambda,\lambda).

$$

**证明。** 
非平凡根 $e^{\pm i\theta}$ 满足

$$

\cos\theta=1-\frac1{2\lambda}.

$$

右侧在 $[-1,1]$ 中当且仅当 $\lambda\ge1/4$。在 $1/4<\lambda<1$ 时，虚部与归一化迫使零谱矩的权重为上述三数，其非负性等价于 $\lambda\le1/2$。严格内区间三个权重均正且三个谱点不同，故最小维数为三。$\lambda=1/4$ 时两个非平凡根合并为 $-1$，$\{1,-1\}$ 等权可达；$\lambda=1/2$ 时根为 $\pm i$，两者等权可达。$\lambda>1/2$ 时全部允许谱点实部严格正，不可能凸合成零；$\lambda<1/4$ 时酉参数只剩 $I$。
 ∎

这里确实出现两个可严格命名的阈值：编织的单位圆根在 $1/4$ 出现，而单层正交记录在超过 $1/2$ 后不再可行。这是本文<em>特定算符形式</em>的阈值，不是未经定义的普遍量子临界矩阵。黄金值 $\varphi^{-2}$ 恰位于这个三谱区间内。

<a id="statement-8-7"></a>

<a id="prop-arcbounds"></a>

#### 命题 8.7（两个相关的精确下界）

若 $\operatorname{spec}(W)\subseteq\{\zeta,\zeta^2\}$，则任意 $\sigma$ 都满足

$$

|\operatorname{Tr}(\sigma W)|\ge\cos\frac{3\pi}{10}>0.

$$

若 $\operatorname{spec}(W)\subseteq\{\zeta,\bar\zeta\}$，则

$$

|\operatorname{Tr}(\sigma W)|\ge\frac1{2\varphi}>0.

$$

**证明。** 
第一个凸包是圆上夹角 $3\pi/5$ 两点之间的弦，旋转到关于实轴对称后，弦的实部恒为 $\cos(3\pi/10)$，最短模在中点取得。第二条弦的实部恒为 $\cos(3\pi/5)=-1/(2\varphi)$，同理得界。若谱只含其中一点，模为 $1$，仍满足界。
 ∎

<a id="fig-spectral-hulls"></a>

> **图形表示适配（编者）。** 源稿 TikZ 图改绘为下列等宽双面板示意图；点状轮廓表示单位圆，箭头表示复平面坐标轴，实线表示谱凸包。谱点的角位置、原点与凸包的内外关系沿用源图；字符图形不作为精密量尺。

```text
                       ↑ Im                                                   ↑ Im                        
              ζ  ●     │     ·                                       ζ  ●╲    │     ·                     
            ·   ╱      │          ·                                ·    │░╲╲╲ │          ·                
         ·      ╱      │             ·                          ·       │░░░░╲╲             ·             
       ·       ╱       │               ·                      ·         │░░░░░│╲╲╲            ·           
     ·        ╱        │                 ·                  ·           │░░░░░│░░░╲╲╲           ·         
    ·         ╱        │                  ·                ·            │░░░░░│░░░░░░╲╲╲         ·        
   ·         ╱         │                   ·              ·             │░░░░░│░░░░░░░░░╲╲╲       ·       
  ·          ╱         │                    ·            ·              │░░░░░│░░░░░░░░░░░░╲╲      ·      
  ·         ╱          │                    ·            ·              │░░░░░│░░░░░░░░░░░░░░╲╲╲   ·      
 ·         ╱           │                     ·          ·               │░░░░░│░░░░░░░░░░░░░░░░░╲╲╲ ·1    
───────────╱───────────●─────────────────────────→     ─────────────────│─────●────────────────────╱●───→ 
  ·       ╱            │0                   ·  Re        ·              │░░░░░│0░░░░░░░░░░░░░░░░╱╱╱·  Re  
  ·      ╱             │                    ·            ·              │░░░░░│░░░░░░░░░░░░░░╱╱╱   ·      
   ·     ╱             │                   ·              ·             │░░░░░│░░░░░░░░░░░╱╱╱     ·       
    ·   ╱              │                  ·                ·            │░░░░░│░░░░░░░░╱╱╱       ·        
     ·  ╱              │                 ·                  ·           │░░░░░│░░░░╱╱╱╱         ·         
   ζ²  ●               │               ·                      ·         │░░░░░│░╱╱╱           ·           
         ·             │             ·                          ·       │░░░░╱╱╱            ·             
            ·          │          ·                                ·    │░╱╱╱ │          ·                
                 ·     │     ·                                      ζ̄  ●╱    │     ·                     
                       │                                                      │                           
                       │                                                      │                           

          原生两谱的凸包                                        允许的三谱围住原点
        一次不能形成正交记录                                    黄金权重给出正交记录
```

**图形标签与位置说明（编者，按源图转写）。** 左面板为 $\zeta$、$\zeta^2$、$0$；右面板为 $1$、$\zeta$、$\bar\zeta$、$0$。左面板的谱点在单位圆的 $108^\circ$、$216^\circ$ 处，右面板在 $0^\circ$、$108^\circ$、$252^\circ$ 处；左弦不含原点，右三角形包含原点。

**图 1：** 谱的几何只在指定耦合、准备及读出接口下成为测量结论。图中的点是子门本征值，不是五模式金字塔的顶点。

<a id="sec-9"></a>

## 9. 递归会不会终于定格：两种相反的精确结论

<a id="statement-9-1"></a>

<a id="thm-fresh"></a>

#### 定理 9.1（新记录的乘积律与可见去相干极限）

对同一个父投影 $P$，每个有限段的初态为 $\rho\otimes\sigma_1\otimes\cdots\otimes\sigma_n$，各 $W_j,\sigma_j$ 预先固定，不依记录自适应选择。每层作相应提升后不再相干访问旧子系统。第 $j$ 层的重叠为 $m_j=\operatorname{Tr}(\sigma_jW_j)$。则 $n$ 层之后[(9)](#eq-coherence)中的交叉系数为

$$

\Gamma_n=\prod_{j=1}^nm_j.

$$

对具有非零 $P\rho(I-P)$ 的输入，约化态趋于非选择 Lüders 态，当且仅当 $|\Gamma_n|\to0$。若所有 $m_j\ne0$，此条件等价于

$$

\sum_{j=1}^{\infty}-\log|m_j|=+\infty.

$$

若某个 $m_j=0$，之后已完全去相干。

**证明。** 
每层保留两个对角块，仅把同一交叉块乘 $m_j$，归纳得到乘积。令 $B=P\rho(I-P)$，差态只含两个互为伴随的块 $\Gamma_nB$ 与 $\bar\Gamma_nB^\dagger$，其奇异值给出

$$

\left\lVert \Lambda_{\Gamma_n}(\rho)-\Lambda_0(\rho)\right\rVert_1
=2|\Gamma_n|\left\lVert B\right\rVert_1.

$$

对 $B\ne0$ 即得充要条件。对数把非零模的乘积转成上述和。
 ∎

若 $|m_j|\le r<1$，则相干上界按 $r^n$ 衰减，可以定义何时低于某个分辨率。但递归本身没有保证 $r<1$。取 $m_j=1$，根本不会去相干；若因子过快趋于模一，它们的无限乘积也可以为正。这里的“新准备且不再访问”是实际独立与记录保留条件。

<a id="statement-9-2"></a>

<a id="thm-revival"></a>

#### 定理 9.2（同一记录复用：第五次分辨，第十次复归）

取子门

$$

W=\zeta(I-R_0)+\zeta^2R_0,

$$

在其两个非零谱扇区各取单位向量，子初态为二者的等权纯叠加。对同一个非平凡父投影，重复同一个 $\mathcal C_P(W)$，或始终重复同一个 $\mathcal L_P(W)$；<em>相干复用同一个子系统</em> $n$ 次，且不做中间记录测量或向外转存，交叉系数为

$$

m_n=\langle\chi,W^n\chi\rangle
=\frac{\zeta^n+\zeta^{2n}}2.

$$

于是

$$

|m_1|=\cos\frac{3\pi}{10}>0,\qquad m_5=0,\qquad m_{10}=1.

$$

第五次两个纯指针正交，第十次整体耦合精确回到恒等。

**证明。** 
同一子系统上的提升幂由定理[6.2](#thm-lifts)给出，故相关内积为 $W^n$ 的谱矩。$\zeta^5=-1$、$\zeta^{10}=1$，代入即得；$W^{10}=I$ 给出整个提升的十次复归。
 ∎

这个例子直接表明：在一个更大的静态酉网络中，某个切面可有完全可区分的记录，另一个切面又可有相干复归。第五次若真的把结果转存到另一个未逆转的观察者中，第十次复归结论不再适用于只包含原父子系统的模型。可读记录、已读取记录及所有记录的共同逆演化必须区分。

<a id="statement-9-3"></a>

<a id="thm-nonconvergence"></a>

#### 定理 9.3（读出稳定不等于全算符极限存在）

在[(8)](#eq-productrecursion)中，假设每个 $P_n$ 及 $I-P_n$ 非零，以 $A\mapsto I\otimes A$ 识别相邻层。则

$$

\boxed{\left\lVert W_{n+1}-I\otimes W_n\right\rVert=|\zeta-1|.}

$$

因此这列门不在算符范数下形成 Cauchy 列。然而，在给定乘积态

$$

\rho^{(n)}=\rho_n\otimes\cdots\otimes\rho_1

$$

中，若 $r_j=\operatorname{Tr}(\rho_jP_j)$ 且 $\prod_{j=1}^nr_j\to0$，则

$$

\operatorname{Tr}(\rho^{(n)}W_n)
=1+(\zeta-1)\prod_{j=1}^nr_j\longrightarrow1.

$$

**证明。** 
相邻差为 $-(\zeta-1)(I-P_{n+1})\otimes E_n$，其中两个投影因子均非零，范数各为 $1$。期望公式由张量乘积迹及[(8)](#eq-productrecursion)直接得到。
 ∎

因此可以同时严格说：指定观察者的一项预测在分辨率下定格；全部可能输入上的门仍没有范数极限。若要使用其他极限，如强算符极限、局部态极限或某个测量距离，必须连同空间嵌入、允许状态与误差尺度一起定义。

<a id="sec-10"></a>

## 10. 静态切面中的观察者与相容扩展

<a id="statement-10-1"></a>

#### 定义 10.1（内生观察者的有限接口）

在给定联合空间中，观察者由可访问的子代数、记录载体、允许的仪器及保留规则描述。若记录投影为 $\{\Pi_o\}$，系统算符为 $A$，联合态为 $\rho_{SR}$，则已取得记录 $o$ 下的预测为

$$

\omega(A\mid o)=
\frac{\operatorname{Tr}[\rho_{SR}(A\otimes\Pi_o)]}
{\operatorname{Tr}[\rho_{SR}(I\otimes\Pi_o)]},

$$

限于分母正的事件。观察者、被观察系统与参照可同属更大的联合状态；这里没有放置一个不受模型描述的外部观察实体。

这是一种接口定义，不是从物理上把观察者的所有性质等同于单个投影。若它继续观察自己的记录设备，只需把新的设备与记录纳入联合空间，并再次指定可访问代数。有限次扩展不需要预先解开一个无限自指循环。

<a id="statement-10-2"></a>

#### 命题 10.2（静态酉网络的切面相容）

给定有限因果偏序网络，各局部门是其输入输出空间间的酉映射，且不可比较的操作作用于互不相交的因子。则沿任意拓扑序收缩网络，得到同一个边界算符。保留全部开放输入与输出时，该算符酉；若固定某些辅助输入为纯准备态，则得到等距映射。读取或遗忘某些输出载体，可进一步得到相应仪器或通道，而不必额外引入一个绝对外部时钟。

**证明。** 
任意两个有限偏序的线性扩展可用相邻不可比较元素的交换连接。它们的算符作用于不交因子，因而对易，每次交换不改变积。酉算符复合仍酉；仪器与通道由命题[4.4](#prop-dilation)的记录读出和偏迹给出。
 ∎

若两条变化路径作用于重叠因子，则需要额外的编织、五边形或其他相容恒等式，不能仅凭“没有绝对时间”而删去非交换次序。父门与子门的递归也可看作同一个静态张量网络的不同分组，但分组必须保留全部开放指标及相位约定。

<a id="statement-10-3"></a>

<a id="thm-stateextension"></a>

#### 定理 10.3（一致切面态的静态延拓）

设 $H^{(n+1)}=H^{(n)}\otimes K_{n+1}$，给定密度算符 $\rho_n$ 满足

$$

\operatorname{Tr}_{K_{n+1}}\rho_{n+1}=\rho_n.

$$

则在局部矩阵代数按 $A\mapsto A\otimes I$ 嵌入形成的并集上，

$$

\omega(A)=\operatorname{Tr}(\rho_nA),\qquad A\in\mathcal B(H^{(n)}),

$$

定义唯一一致的正归一化线性泛函，并唯一连续延拓到该并集的算符范数完备化。

**证明。** 
偏迹条件保证同一个局部算符在不同切面上有同样期望，因此定义良好。每个有限层上都有线性、正性、$\omega(I)=1$ 及 $|\omega(A)|\le\left\lVert A\right\rVert$，这些性质在并集上保持。故泛函连续，能唯一延拓到完备化；正性由有限层平方元的逼近保持。
 ∎

该定理要求真正的边界一致性。只给每层一个酉矩阵，并不自动给出相容的 $\rho_n$；加入新层时若改变了旧边界态，便不满足这个延拓条件。有限递归酉性、无限态的一致存在、单项读出收敛，以及全算符范数收敛是四个不同命题。

### 回到项目的实际记录反例

项目《最小纯记录扩张》§5 在指定五配置模型中取

$$

t=p+q,\quad B=1-t,\quad A=B-r,\qquad p,q,r>0,\ p+q+r<1.

$$

对同一等距构造 $V_2$，从根配置 $0$ 开始，两次使用新环境而不测中间后继时，回到 $0$ 的概率为 $B^2+4pq$；实际逐步测量后继的 Markov 回返概率则为 $A^2+r^2+2pq$。两者之差为

$$

2Ar+2pq>0.

$$

本文不重复该源完整输运模型的证明，而保留其精确接口：新环境本身并不保证已测量历史的乘积律；还要看哪些路径在环境中被区分，哪些中间量真的读过。

同源 §6 的另一构造保留 $N$ 个有序四维记录与最终后继，可在末端联合读取时恢复有限路径；记录部分的载体维数为 $4^N$，另计最终五维配置与二维内部因子。这些结果说明“图中有一条路径”“酉演化保持了路径间相干”“观察者实际取得了某条路径的记录”，在项目内已经是不同的命题。本篇的相位提升与端点仪器正可以接到这种实际记录接口上。

<a id="sec-11"></a>

## 11. 本轮得到的理论结构与下一步判别

原先的等号可以精确修订为：

$$

\boxed{\text{三角剖分端点完成}
+\text{实现它的仪器}
+\text{实际取得记录}
\ \Longrightarrow\ \text{条件测量完成}.}

$$

定理[4.3](#thm-parity)给出一个固定仪器在整条受限纤维上成立的例子。命题[2.3](#prop-nonaffine)与定理[3.2](#thm-schur)则说明为何这个结论不能无条件外推。

“门里的参数仍然是门”也有明确的正面形式：

$$

\boxed{\text{标量相位}\longrightarrow\text{子系统酉算符}
\longrightarrow\text{相容的算符块网络}.}

$$

它需要定理[5.2](#thm-blocks)的交叉列条件、定理[6.3](#thm-phase-reference)的相位参照，以及定理[7.2](#thm-braidspectrum)的谱约束。相对相位递归闭合，整块黄金门直接自代入则不保留同一编织。

| 问题 | 本文的精确对象 | 结论与范围 |
| --- | --- | --- |
| 隐藏关系完成 | 固定三均值的 $\kappa$ 纤维 | 两种剖分取相反端点 |
| 保持三个读出 | 对全部输入稳定三个投影 | 所有占位概率不变，相位仍可变 |
| 条件塌缩 | 仪器、正概率分支、实际记录 | 指定模型中可等于端点完成 |
| 复参数递归 | $\mathcal C_P(W),\mathcal L_P(W)$ | 均酉，组合律和编织闭合不同 |
| 一次黄金记录 | 允许谱的凸包含零 | 三谱、三维及唯一总谱权重 |
| 递归稳定 | 新记录重叠乘积趋零 | 给约化相干极限；复用可出现复归 |
| 无限静态对象 | 指定嵌入与一致边界态 | 可有态延拓，却无门的范数极限 |

继续推进时，有三项具体研究任务。其一，在原生 AURIC 许可操作中，找出哪些状态准备、谱扇区和记录读口真正可取得，从而把本文的抽象三谱仪器变成可执行协议。其二，放开共享参数形式，研究不同边的非交换子门及其完整相容方程，检验是否得到超过直和谱扇区的编织。其三，选择实际记录距离和容量约束，证明特定递归对内生观察者的预测收敛，保留同一记录复用的反例。

目前已有的定理支持一个清晰的图景：<strong>一个观察切面上被压缩成复系数的内部过程，在更精细切面中可以展开为门、辅助自由度和记录；可读条件分支由这些记录的相容结构决定。</strong>复系数的展开需要具体相位与算符关系，稳定需要可证明的记录条件。它们给量子操作的逻辑约束一个可研究的模型，同时没有把复 Hilbert 结构、Born 标定或单次实际结果的起源宣告为已完成的推导。

<a id="sec-bibliography"></a>

## 文献与固定项目来源

<a id="ref-project"></a>

[1] 
<em>trureturing</em>, `dev` 固定提交
[`23a4ae6f843d1635869b7656fb6bd681121447a8`](https://github.com/the-omega-institute/trureturing/commit/23a4ae6f843d1635869b7656fb6bd681121447a8),
2026-10-30。主要固定来源：
[金字塔基础公式](https://github.com/the-omega-institute/trureturing/blob/23a4ae6f843d1635869b7656fb6bd681121447a8/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)；
[读出与记录三角形，定理 9](https://github.com/the-omega-institute/trureturing/blob/23a4ae6f843d1635869b7656fb6bd681121447a8/docs/develop/theory/AURIC_FIB_ATOM_READOUT_CLOSURE_AND_RECORD_TRIANGLE.md)；
[固定黄金门，§§2--4、8](https://github.com/the-omega-institute/trureturing/blob/23a4ae6f843d1635869b7656fb6bd681121447a8/docs/develop/theory/AURIC_FIXED_GOLDEN_GATE_AND_BRAID_COMPATIBILITY_ZH.md)；
[最小纯记录扩张，§§1--7](https://github.com/the-omega-institute/trureturing/blob/23a4ae6f843d1635869b7656fb6bd681121447a8/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MINIMAL_RECORD_DILATIONS.md)；
[相干重构续卷，§67](https://github.com/the-omega-institute/trureturing/blob/23a4ae6f843d1635869b7656fb6bd681121447a8/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION.md)。

<a id="ref-watrous"></a>

[2] 
J. Watrous, <em>The Theory of Quantum Information</em>, Cambridge University Press, 2018.
[作者托管第 2 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，有限维通道、Kraus 与等距表示、量子仪器。

<a id="ref-hg"></a>

[3] 
L. Hadjiivanov and L. S. Georgiev, <em>Braiding Fibonacci anyons</em>,
[arXiv:2404.01778v4](https://arxiv.org/abs/2404.01778v4), 2024，§3 的 $F$ 与 $R$ 矩阵。

<a id="ref-araujo"></a>

[4] 
M. Araújo, A. Feix, F. Costa and C. Brukner,
<em>Quantum circuits cannot control unknown operations</em>,
New Journal of Physics 16 (2014), 093026.
[arXiv:1309.7976](https://arxiv.org/abs/1309.7976)。

<a id="ref-robinson"></a>

[5] 
P. L. Robinson, <em>Julia operators and Halmos dilations</em>,
[arXiv:1803.09329](https://arxiv.org/abs/1803.09329), 2018，定理 2。
