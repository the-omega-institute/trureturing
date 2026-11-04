# 从二元失败见证到整体量子关系

AURIC v78 后续研究：定义、定理与证明

研究续稿

2026 年 11 月 2 日

## 摘要

本稿继续 v78 及前轮历史圆弧研究，把“撤去公理，找出受影响的两个元”落实为三个可证明步骤：在固定线性接口中，以残差因子化判定一条约束是否已由其余约束推出；以内部参考流与运输的相容关系构造共同复结构及薛定谔形式；以递增历史表的可求和重叠误差与消失的正性残差构造同一个整体正核。平方读出、完整正性和同根 Born 校准使用项目已有结果，并补足二元失败见证。

这里“内生化”的可核验含义是：每个关系、参考、读出及证明前件都属于同一已声明的内部结构；可以推出的条件移入定理，无法推出的条件保留为明确的结构约束。仅把条件重命名为定义不产生唯一性证明。本稿逐节给出白话图景，并区分有限三维诊断、整个载体的维数以及实际原生控制的取得范围。

## 目录

- [1. 接续位置：哪些已有，哪些是本轮推进](#section-1)
- [2. 公理先落到两个元：身份、读出与三维见证](#section-2)
- [3. 反着推的精确形式：删除一条约束会怎样](#section-3)
- [4. 复数从哪里进入：内部参考与运输的关系](#section-4)
- [5. 平方读出：拆开再合回，与保留参考能否一致](#section-5)
- [6. 完整正性：撤去保留参考，会漏掉哪一对关系](#section-6)
- [7. 有限三维检查怎样拼成同一个整体](#section-7)
- [8. 把外加公理压成定义之间的相容条件](#section-8)

<a id="section-1"></a>

## 1. 接续位置：哪些已有，哪些是本轮推进

本稿继承已读取的 v78 原对话，以及前轮《历史圆弧、椭圆读出与内生关系闭合》。v78 的关键基线是完整历史正核、同一根来源、可逆保核续接与完整标架相容；Born 读出还保留效果细分相容、同根校准和准备协变。前轮已区分球面圆与其平面椭圆读出，并以二阶 Schur 残差检验整段历史是否留在同一个二态载体中。

本轮固定核对的公开提交为

`d6cb695cddf0229369d07065719603d8784235f6`。

本次核对的 V59、V62、V63、V64、V65、V68、OMEGA 总稿，以及目标恢复、最小预测摘要两份源码，与前轮快照的对应文件逐字节相同。此结论只覆盖上述九份文件。

| 位置 | 已有结果 | 本轮接续工作 |
| --- | --- | --- |
| 项目一般商判据 | 一个问题能否由某概念回答，等价于该问题在概念纤维上常值 | 用同一思想检验固定线性约束的冗余、失败见证与最优残差界 |
| V63 | 原生实二维纤维中的共同复结构；共享锚正核近似 | 给出任意有限实维中的共同参考流路线，及循环根频率残差 |
| V64、v78 | 三端口平方标定；同根效果概率表示 | 明确两类标定各自解决的关系问题，保留必要前件 |
| V38、V65 | Choi、Kraus、内部忠实参考的过程判据 | 把非正候选压成最小二元报告中的球外见证 |
| V63、V68、OMEGA | 有限证书、条件量子重构、精确局部态拼合 | 证明带误差的递增历史表收敛到一个整体正核，并继承秩与续接 |

全文先在有限维实或复内积空间中进行。复内积对第二变量线性。符号 $\Omega$ 在讨论整体时指全部内部结构；在向量公式中使用 $\Omega_0$ 表示选定的单位根向量。把整体结构与其一个表示向量分开，可以避免把观察者、记录与参考条件误缩成单个向量符号。

本稿给出解析证明，未新增仓库提交，也未执行新增结果的 Lean 形式化验证。它不把标准谱论、因子化或 Choi 判据认领为新的基础数学发现。

**白话图景。**现在已有一张关系图，也已有沿图移动的历史。继续向前，要逐项问：哪条规则只是这张图中其他关系的结果？哪条规则若删去，真的会让两条历史在同一个读口上冲突？这轮把这个问题写成可证明、可反驳的数学判据。

<a id="section-2"></a>

## 2. 公理先落到两个元：身份、读出与三维见证

### 2.1 定义能回答什么，取决于它保留哪些关系

<a id="statement-2-1"></a>

#### 定义 2.1（概念纤维与缺陷对）

设 $S$ 为非空内部来源集合，$c:S\to C$ 是一个概念或摘要，$q:S\to Q$ 是待回答的目标。定义

$$
\Delta(c,q)=\{(s,t):c(s)=c(t),\ q(s)\ne q(t)\}.
$$

它收集“概念认为相同，目标却要求不同”的二元来源对。

<a id="statement-2-2"></a>

#### 定理 2.2（概念可回答性；项目既有判据）

存在 $f:c(S)\to Q$ 使 $q=f\circ c$，当且仅当 $\Delta(c,q)=\varnothing$。

**证明。**

若已有 $f$，则 $c(s)=c(t)$ 立即给 $q(s)=f(c(s))=f(c(t))=q(t)$。
反向，缺陷对为空时定义 $f(c(s))=q(s)$；任取同一 $c(s)$ 的另一来源，目标值相同，所以定义良定。这一函数显然给所需分解。

□

这正是项目 `answerability_criterion` 与目标恢复判据的基础结构[1](#ref-repo-factor)、[2](#ref-repo-recovery)。如果某种局部状态漏掉会影响未来的历史，两个被局部状态合并的来源可能在同一个后继测试中产生不同结果。此时应扩大状态描述，直到未来问题能沿该描述下降。给概念加一个名字，不会消灭缺陷对。

**白话图景。**两段历史看上去一样，是因为当前概念把它们压成了同一个标签。如果接上同一个后续过程却得到不同结果，矛盾就落在这两个元上。补入能区分它们的内部关系后，目标才真正成为这个概念的函数。

### 2.2 同一来源的两条路由

<a id="statement-2-3"></a>

#### 定义 2.3（路由残差及二元 Gram 见证）

在已建立的线性接口中，取同源、同靶映射 $L,R:V\to W$，令

$$
D=L-R,\qquad a=Lx,\quad b=Rx,\quad s=\left\lVert a\right\rVert ^2+\left\lVert b\right\rVert ^2.
$$

当 $s>0$ 时，定义

$$
X=\frac{2\operatorname{Re}\langle a,b\rangle }{s},\qquad
Y=\frac{2\operatorname{Im}\langle a,b\rangle }{s},\qquad
Z=\frac{\left\lVert a\right\rVert ^2-\left\lVert b\right\rVert ^2}{s}.
$$

实接口中暂取 $Y=0$；第[4](#section-4)节建立共同复方向后，$Y$ 有相应实交叉比较的含义。

<a id="statement-2-4"></a>

#### 定理 2.4（三维关系球与准确失败量）

上述坐标满足

<a id="eq-ball"></a>

$$
1-X^2-Y^2-Z^2
=\frac{4(\left\lVert a\right\rVert ^2\left\lVert b\right\rVert ^2-|\langle a,b\rangle |^2)}{s^2}\ge0, \tag{1}
$$

<a id="eq-failure"></a>

$$
\boxed{\left\lVert Dx\right\rVert ^2=s(1-X).} \tag{2}
$$

因此 $a=b$ 当且仅当 $X=1$。若 $s=0$，则 $a=b=0$，直接标记该关系成立，不作除法。

**证明。**

第一式展开三坐标平方即得，非负性是二元 Gram 行列式非负，等价于 Cauchy--Schwarz 不等式。第二式由

$$
\left\lVert a-b\right\rVert ^2=\left\lVert a\right\rVert ^2+\left\lVert b\right\rVert ^2-2\operatorname{Re}\langle a,b\rangle
$$

直接得到。

□

这里得到一般是闭球，落在球面恰当且仅当 $a,b$ 线性相关。它无损记录这一个归一二元 Gram 表；总尺度 $s$、历史身份、路由及靶空间仍须另行保留。它不把任意高维整体无损压成三个实数，也不声称三维由事件数二自动唯一推出。

**白话图景。**把同一个输入分别沿两条路送出去，再把两个结果放在一起比较。它们的强弱差、同向关系和正交相位关系组成三个坐标。两条路完全重合时，坐标到达 $X=1$ 的点；偏离多少，正好等于那一对结果的残差除以总尺度。

<a id="section-3"></a>

## 3. 反着推的精确形式：删除一条约束会怎样

### 3.1 冗余、因子化与失败见证

<a id="statement-3-1"></a>

#### 定义 3.1（固定接口上的相容空间）

给定有限条固定线性路由对 $L_i,R_i:V\to W_i$，令

$$
D_i=L_i-R_i,\qquad
\mathcal C=\bigcap_i\ker D_i.
$$

对某一条 $j$，把其余残差堆叠为

$$
B_jx=(D_ix)_{i\ne j},\qquad M_j=B_j^*B_j.
$$

第 $j$ 条在这个接口上冗余，指 $\ker B_j\subseteq\ker D_j$。

<a id="statement-3-2"></a>

#### 定理 3.2（删除约束判据）

以下三项等价：

<a id="eq-kernel"></a>

$$
\ker B_j\subseteq\ker D_j; \tag{3}
$$

<a id="eq-factor"></a>

$$
\text{存在固定线性 }F_j\text{，使 }D_j=F_jB_j; \tag{4}
$$

<a id="eq-domination"></a>

$$
\text{存在有限 }c\ge0\text{，使 }D_j^*D_j\preceq cB_j^*B_j. \tag{5}
$$

若它们不成立，则存在单位 $x$ 满足

$$
\boxed{D_ix=0\ (i\ne j),\qquad D_jx\ne0.}
$$

这恰是删除第 $j$ 条后，所有其他关系仍成立而这一条失败的见证。

**证明。**

若核包含成立，在 $\operatorname{ran}  B_j$ 上定义 $F_j(B_jx)=D_jx$。若 $B_jx=B_jy$，则 $x-y\in\ker B_j\subseteq\ker D_j$，所以定义良定且线性。令其在 $\operatorname{ran}  B_j$ 的正交补上为零，即得全域因子。

若已有因子，则

$$
\left\lVert D_jx\right\rVert ^2\le\left\lVert F_j\right\rVert ^2\left\lVert B_jx\right\rVert ^2,
$$

给算子不等式。反向，若不等式成立，$B_jx=0$ 迫使 $D_jx=0$。

若核包含不成立，按定义有 $x_0\in\ker B_j\setminus\ker D_j$。这个向量非零，除以其范数即得单位失败见证。

□

这是一般纤维因子化的线性定量版本。它处理*固定载体与固定路由中，某条状态约束是否由其他状态约束推出*。若要证明在所有可变模型中一个算子公理 $D_j=0$ 的逻辑独立性，还须让模型本身变化，并给出相应反模型，量词不能互换。

物理应用还须保留一个非零实际相容根或非空合法输入集合。若 $\ker B_j=0$，其余约束已经没有单位共同解，冗余只是空真。数学失败向量是否原生可制备，则由实际控制菜单决定。

**白话图景。**先让其余关系全部成立，再问被删掉的这一条会不会自行成立。如果它的残差总能由其他残差加工出来，其他残差归零时它也只能归零，可以移入定理。如果做不到，就找得到一个具体输入：其余路都接上了，只有这一对结果分开。这才是“为什么需要它”的精确回答。

### 3.2 约束之间的关系还有强弱

<a id="statement-3-3"></a>

#### 命题 3.3（最优残差传导常数）

记 $M^{+1/2}=(M^+)^{1/2}$ 为 Moore--Penrose 逆的正平方根。在定理[3.2](#statement-3-2)的等价条件成立时，最小的 $c$ 是

$$
\boxed{c_{\min}=\left\lVert D_jM_j^{+1/2}\right\rVert _{\rm op}^2.}
$$

条件不成立时不存在有限 $c$。

**证明。**

简记 $D=D_j,M=M_j$。核包含给 $D|_{\ker M}=0$，故

$$
D=(DM^{+1/2})M^{1/2}.
$$

这证明所示常数可用。反向，任一可用常数满足

$$
\left\lVert Dx\right\rVert ^2\le c\langle x,Mx\rangle .
$$

对 $y\in\operatorname{ran}  M$ 取 $x=M^{+1/2}y$，得
$\left\lVert DM^{+1/2}y\right\rVert ^2\le c\left\lVert y\right\rVert ^2$。该算子在 $\ker M$ 上为零，因此其全算子范数平方不超过 $c$。

□

若 $M=0,D=0$，最小常数为零；若 $M=0,D\ne0$，则最小常数为无穷，不能机械代入伪逆公式。

**白话图景。**有些关系虽然能由其他关系推出，却对它们的误差特别敏感。这个最优常数衡量的正是误差放大：其他关系只错一点，这条关系最多会被带偏多少。逻辑上可推出，不等于数值上容易确认。

<a id="statement-3-4"></a>

#### 定理 3.4（整体相容空间与距离界）

定义约束算子

$$
\mathcal L=\sum_iD_i^*D_i,\qquad
\mathcal E(x)=\langle x,\mathcal Lx\rangle =\sum_i\left\lVert D_ix\right\rVert ^2.
$$

则

$$
\ker\mathcal L=\mathcal C.
$$

若 $\mathcal L\ne0$，令 $\lambda_+$ 为其最小正特征值，则

$$
\boxed{\operatorname{dist} (x,\mathcal C)^2\le\frac{\mathcal E(x)}{\lambda_+}.}
$$

若 $\mathcal L=0$，则 $\mathcal C=V$，距离恒为零。

**证明。**

非负项之和为零，恰好等价于每一项为零，给核等式。把 $x=x_0+x_\perp$ 正交分解到 $\ker\mathcal L$ 及其正交补。在后者上 $\mathcal L\succeq\lambda_+ I$，故

$$
\mathcal E(x)\ge\lambda_+\left\lVert x_\perp\right\rVert ^2
=\lambda_+\operatorname{dist} (x,\mathcal C)^2.
$$

取最小正特征值的单位特征向量可取等。

□

若 $\mathcal L_\epsilon=\operatorname{diag}(0,\epsilon^2)$，取 $x=e_2$，则残差能量趋零而到相容空间的距离恒为一。因此一族接口上的统一稳定性需要统一谱隙。$\mathcal L$ 在这里是诊断约束的算子，尚未被认定为物理时间演化的 Hamiltonian。

**白话图景。**把所有成对失配放在一起，就得到一个整体的零残差空间。关系全部接上的状态都在其中；有谱隙时，总残差还告诉我们离它多远。这把分散的规则放进了同一个可检验结构，但若结构接近退化，小残差就未必意味着真正接近整体相容。

<a id="section-4"></a>

## 4. 复数从哪里进入：内部参考与运输的关系

本节从实内积开始，不使用复正核作为前件。项目 V63 已经在其原生实二维纤维、保范数响应和根钟标定中推出共同复结构[3](#ref-repo-v63)；下面给另一组明确的充分条件，处理任意有限实维。

### 4.1 共同参考流强迫单频率

<a id="statement-4-1"></a>

#### 定义 4.1（共同内部参考）

设 $(V,g)$ 是非零有限维实内积空间，$G\le O(V,g)$ 实不可约，即没有非零真 $G$ 不变实子空间。给定非平凡连续一参数群

$$
R:\mathbb R \to O(V,g),\qquad R_{s+t}=R_sR_t,
$$

并要求

$$
\boxed{UR_t=R_tU\quad(U\in G,\ t\in\mathbb R ).}
$$

这个等式比较“先运输再转参考”与“先转参考再运输”的两条内部历史。

<a id="statement-4-2"></a>

#### 定理 4.2（共同四分之一周与复结构）

存在 $\omega>0$ 和正交复结构 $J$，使

$$
J^2=-I,\quad J^*=-J,\quad UJ=JU\ (U\in G),
$$

$$
\boxed{R_t=\cos(\omega t)I+\sin(\omega t)J.}
$$

参考流自动光滑，其最小正周期为 $2\pi/\omega$，并有
$J=R_{\pi/(2\omega)}$。正时间方向固定后 $\omega,J$ 唯一。

**证明。**

任何与 $G$ 对易的实自伴算子，其特征空间均为 $G$ 不变空间，因此必为标量。
于是

$$
\tfrac12(R_t+R_t^*)=c(t)I.
$$

若所有 $c(t)$ 都属于 $\{1,-1\}$，连续性及 $R_0=I$ 给 $c(t)=1$，正交性进而给 $R_t=I$，违反非平凡性。因此可选 $t_0$ 使 $|c(t_0)|<1$。

令 $c_0=c(t_0)$、$s_0=\sqrt{1-c_0^2}$，并定义

$$
J=\frac{R_{t_0}-c_0I}{s_0}.
$$

由 $R_{t_0}+R_{t_0}^{-1}=2c_0I$ 得
$(R_{t_0}-c_0I)^2=-(1-c_0^2)I$，所以 $J^2=-I,J^*=-J$。它与 $G$ 以及所有 $R_t$ 对易。

写 $R_t=c(t)I+B_t$，其中 $B_t^*=-B_t$。$JB_t$ 自伴且与 $G$ 对易，故为标量，即 $B_t=s(t)J$。正交性给 $c(t)^2+s(t)^2=1$。群律使 $c(t)+is(t)$ 成为从加法实数到单位圆的连续同态。

在零点附近取连续小角 $\theta(t)$；群律保证在足够小的邻域内 $\theta(s+t)=\theta(s)+\theta(t)$。连续可加函数为 $\omega t$，再用整数分段把结果延伸到全部实数。非平凡性给 $\omega\ne0$，必要时把 $J$ 换成 $-J$，取得 $\omega>0$。余下结论由公式直接得到。

□

若已经知道 $R$ 为 $C^1$，证明更短：$A=R'_0$ 满足 $A^*=-A$、$AU=UA$；$A^2$ 自伴且对易，故为标量；非平凡性给 $A^2=-\omega^2I$，所以 $J=A/\omega$。这里自伴算子的不可约标量性质是标准表示论工具[8](#ref-woit)。

**白话图景。**若内部运输不能分裂成互不交流的独立块，一个对全部运输都通用的参考转动，就不能在不同方向使用不同转速。它只剩一个共同圆周。转四分之一周的实际操作平方为负恒等，这个操作就成为乘 $i$ 的含义。

### 4.2 不先给复核，先给两种实比较

<a id="statement-4-3"></a>

#### 推论 4.3（复内积与正历史核）

定义 $(a+ib)x=ax+bJx$，以及

$$
\boxed{h(x,y)=g(x,y)+i\,g(Jx,y).}
$$

则 $h$ 是对第二变量线性的复内积，全部 $G$ 为复酉运输。若历史向量为 $x_a$，则

$$
K(a,b)=g(x_a,x_b)+i\,g(R_{\pi/(2\omega)}x_a,x_b)
$$

是复正核。

**证明。**

$J^*=-J,J^2=-I$ 给

$$
h(x,Jy)=ih(x,y),\quad h(Jx,y)=-ih(x,y),\quad
h(y,x)=\overline{h(x,y)},\quad h(x,x)=g(x,x).
$$

正定性因此保留。对 $U\in G$，正交性与 $UJ=JU$ 给 $h(Ux,Uy)=h(x,y)$。最后

$$
\sum_{a,b}\overline c_ac_bK(a,b)
=h\left(\sum_ac_ax_a,\sum_bc_bx_b\right)\ge0.
$$

□

**白话图景。**一次比较读出同向部分；另一次先把参考转四分之一周，再比较。两个实读数合成一个复数。复核由这些共同内部比较构造出来，平方范数在这里仍是几何量，尚未自动等同于实验频率。

### 4.3 参考本身也是运输时，复方向还可唯一化

<a id="statement-4-4"></a>

#### 定理 4.4（内部中央参考的交换子代数）

若进一步 $R_t\in G$，则

$$
\boxed{\operatorname{End}_G(V)=\mathbb R  I\oplus\mathbb R  J.}
$$

与全部运输对易的正交复结构恰为 $J,-J$。

**证明。**

任取与 $G$ 对易的 $T$。因 $G$ 正交，$T^*$ 也对易，故 $T$ 的自伴部分为 $aI$。写 $T=aI+B$，$B^*=-B$。由于 $R_t\in G$，$B$ 与 $R_t$ 以及 $J$ 对易。于是 $JB$ 自伴且与 $G$ 对易，故 $JB=bI$，即 $B=-bJ$。反向包含显然。若 $aI+bJ$ 为正交复结构，反对称性给 $a=0$，平方为 $-I$ 给 $b=\pm1$。

□

这个额外前件有实际工作。取实四维 $V=\mathbb H$、$G$ 为单位四元数左乘，则作用不可约，所有右乘 $x\mapsto xe^{ti}$、$xe^{tj}$、$xe^{tk}$ 都与它对易。三个候选 $J$ 并不唯一。把选定的一个右参考流也加入全部运输后，其他右方向不再与全部运输对易，交换子代数才降为对应的复数。

**白话图景。**有一个方向可以充当 $i$，还不等于全部内部关系只认可这一个方向。把参考本身也放进同一组运输中检查，才能进一步排除与它不相容的其他参考轴。唯一性来自这项关系约束。

### 4.4 把“不可约”换成根上的具体残差

<a id="statement-4-5"></a>

#### 定理 4.5（同根零频率残差的传播）

不要求 $G$ 不可约。设 $A^*=-A$，对所有 $U\in G$ 有 $AU=UA$，且单位根 $\Omega_0$ 的轨道张成 $V$。令

$$
\omega^2=\left\lVert A\Omega_0\right\rVert ^2>0,\qquad
Q_{\Omega_0}=\left\lVert (A^2+\omega^2I)\Omega_0\right\rVert ^2.
$$

则

$$
\boxed{Q_{\Omega_0}=0\iff A^2=-\omega^2I\text{ 在 }V\text{ 上成立}.}
$$

若 $-A^2=\sum_k\lambda_kP_k$，$w_k=\left\lVert P_k\Omega_0\right\rVert ^2$，则

$$
Q_{\Omega_0}=\sum_kw_k\left(\lambda_k-\sum_\ell w_\ell\lambda_\ell\right)^2.
$$

它是频率平方的加权方差。

**证明。**

令 $B=A^2+\omega^2I$。若 $B\Omega_0=0$，则 $B(U\Omega_0)=UB\Omega_0=0$。轨道张成整个载体，故 $B=0$；反向显然。谱分解与 $\sum_kw_k=1$ 给方差表达。若根未归一，右边须乘 $\left\lVert \Omega_0\right\rVert ^2$，且 $w_k$ 与 $\omega^2$ 均相应除以该量。

□

这里被比较的两个元是 $A^2\Omega_0$ 与 $-\omega^2\Omega_0$。单独的速度标定 $\left\lVert A\Omega_0\right\rVert =\omega$ 不足以约束方差。例子

$$
R_t=\operatorname{diag}(\operatorname{Rot}(t),\operatorname{Rot}(\sqrt2t)),\qquad
\Omega_0=(e_1,e_1)/\sqrt2
$$

在 $SO(2)\times SO(2)$ 下有循环根，却有两个不同频率，且 $Q_{\Omega_0}=1/4$。

**白话图景。**只测根转得多快，可能把两个不同转速平均在一起。还要比较参考转动的二阶变化，是否恰好按同一个比例指回根。这个二元残差为零，并且能沿所有内部运输传过去，才锁住共同频率。

### 4.5 撤去哪些关系，会发生什么

| 撤去条件 | 明确例子 | 失去的结论 |
| --- | --- | --- |
| 不可约或零频率残差 | 两个转动块频率为 $1,\sqrt2$ | 一个共同频率与公共周期 |
| 参考与运输对易 | $SO(3)$ 及绕固定轴的参考转动 | $A^2$ 为标量、共同 $J$ |
| 一参数群律 | $R_t=\operatorname{Rot}(t^3)$ | 非平凡曲线的零点导数可为零，不能据此取 $J=A/\omega$ |
| 正交性 | $R_t=e^tI$ | 得到实膨胀，$A^2=I$，不再为负平方 |
| 参考也属于全部运输 | 四元数左乘及三个右参考方向 | 交换子代数恰为 $\mathbb C$ 的唯一化结论 |

这些反例只标明各条件在本定理中的作用，不宣称每项都是所有可能量子重构路线的必要条件。在不可约背景下，存在非平凡共同参考流与存在相容正交复结构实际上可以互相构造；推进在于把抽象输入改写成两条内部历史可比较、可失败的条件。

**白话图景。**反着推以后，每个条件的工作都看得见：哪项排除多频率，哪项保证参考不被运输扭转，哪项把变化限制成转动。它们可以由更大的原生结构进一步证明，但不能因为改叫“定义”就假装已经没有内容。

### 4.6 薛定谔形式是两种内部变化描述的相等

<a id="statement-4-6"></a>

#### 推论 4.6（平滑门流的 Hermitian 生成元）

设 $U(t)$ 是 $C^1$ 实正交门流，且 $U(t)J=JU(t)$。令

$$
A(t)=\dot U(t)U(t)^{-1},\qquad H(t)=JA(t).
$$

则 $H(t)$ 对 $h$ 自伴，并且

$$
\boxed{\dot U(t)=-iH(t)U(t).}
$$

**证明。**

正交性求导给 $A^*=-A$，对易关系求导给 $AJ=JA$。故

$$
H^*=A^*J^*=AJ=JA=H,
$$

且 $HJ=JH$。因此它也对 $h$ 自伴。以 $i=J$ 作用时，$-iH=-J(JA)=A$，代入即可。

□

这里先取演化参数单位，使生成元公式不另写 $\hbar$；物理能量及单位还需时钟标定。若只给射线过程而换提升 $U\mapsto e^{i\theta(t)}U$，则 $H\mapsto H-\dot\theta I$。

共同参考流 $e^{\omega tJ}$ 只改变一个向量的共同相位；在纯态射线或 Bloch 球上，它保持同一点。前轮球面圆弧由真正改变射线的门轨迹给出，不能与这个参考相位圆混同。门生成元连续，才给相应切向连续；本节的代数相容本身不自动供应平滑控制。

**白话图景。**有了共同的 $i$，每个门的瞬时旋转就能唯一改写成一个 Hermitian 生成元，薛定谔形式因此出现。参考的圆周确定“如何计相位”，实际门序列确定“态怎样走”；历史圆弧的平滑性仍来自这些实际变化的连续接续。

### 4.7 共同复方向也有明确的二元失败见证

已取得共同 $J$ 后，对待检查的正交门 $U$ 与非零 $x$ 比较

$$
a=UJx,\qquad b=JUx,\qquad D=UJ-JU.
$$

两条路的范数相同。定理[2.4](#statement-2-4)立即给

$$
X=\frac{g(a,b)}{\left\lVert x\right\rVert ^2},\qquad
\boxed{\left\lVert Dx\right\rVert ^2=2\left\lVert x\right\rVert ^2(1-X).}
$$

若进一步定义 $U_-=(U+JUJ)/2$，直接展开得到
$U_-J=-JU_-$ 以及

$$
D=2U_-J,\qquad \left\lVert D\right\rVert =2\left\lVert U_-\right\rVert .
$$

所以缺陷准确位于 $U$ 的反复线性部分。检查一组张成输入足以检验整个算子；只在一个输入上为零并不足够。反复线性等距门可给 $a=-b$：两者射线相同，完整相对关系却相反，因此需要保留相干参考来比较。

**白话图景。**让同一个输入先经过门再转参考，另一路先转参考再经过门。如果回来的完整关系不同，这个门就没有保存共同的复方向。三维关系坐标直接记录了差多少；只看两个结果各自的强度或射线，会漏掉这种先后顺序的差别。

<a id="section-5"></a>

## 5. 平方读出：拆开再合回，与保留参考能否一致

本节复用 V64 的三端口标定，并保留 v78 的同根概率绑定。两者承担不同任务：前者锁定标量权重指数，后者把整个效果概率赋给同一个历史根[4](#ref-repo-v64)。

### 5.1 先限定可比较的权重类

<a id="statement-5-1"></a>

#### 定义 5.1（可乘标量权重）

令 $w:\mathbb C \to[0,\infty)$ 有限值，满足

$$
w(0)=0,\quad w(1)=1,\quad w(zz')=w(z)w(z'),
$$

其中 $z,z'$ 为任意复数。再要求 $w$ 在单位圆盘上有界。

<a id="statement-5-2"></a>

#### 命题 5.2（上述权重必为模的幂）

存在 $p\ge0$，使所有 $z\ne0$ 满足 $w(z)=|z|^p$。

**证明。**

若 $z\ne0$，$w(z)w(z^{-1})=1$，所以 $w(z)>0$。当 $|z|\le1$ 时，单位圆盘上的界及 $w(z^n)=w(z)^n$ 给 $w(z)\le1$。若 $|u|=1$，同时对 $u,u^{-1}$ 使用此结论，得到 $w(u)=1$，故权重仅依赖模。

对 $0<r\le s$，$w(r)=w(r/s)w(s)\le w(s)$，所以径向权重单调。于是 $F(t)=\log w(e^t)$ 可加且单调。它在有理数上等于 $pt$，用上下有理逼近延伸到实数，得到 $F(t)=pt$，且 $p\ge0$。

□

**白话图景。**串联同类幅度变化时，权重相乘；相位转一圈不应让有限读数无限膨胀。这些关系先把所有候选压成一个简单问题：幅度的几次方才与后续拆分和合并一致？

### 5.2 第三端口留下共同标尺

<a id="statement-5-3"></a>

#### 定理 5.3（三端口同源标定锁定平方；V64 结果）

取 $a,b\ne0$，$\psi=(a,0,b)^T$，并定义

$$
H_0=\begin{pmatrix}1&1\\1&-1\end{pmatrix},\qquad
G_\lambda=(\lambda H_0)\oplus1.
$$

在同一个幅度参考中连续使用该操作，不在两次之间任意重新标定。要求：

1. 两次操作后完整射线返回：$[G_\lambda^2\psi]=[\psi]$；

2. 一次操作前后，前两个端口构成的粗事件权重比例不变，其中

   $$
   \Pi_w(C\mid v)=\frac{\sum_{j\in C}w(v_j)}{\sum_jw(v_j)}.
   $$

则 $w(z)=|z|^2$。

**证明。**

因 $H_0^2=2I$，

$$
G_\lambda^2\psi=(2\lambda^2a,0,b)^T.
$$

第三端口 $b\ne0$ 迫使射线返回的比例常数为一；$a\ne0$ 再给 $2\lambda^2=1$，故 $|\lambda|=1/\sqrt2$。

一次操作后为 $(\lambda a,\lambda a,b)$。记 $A=w(a)>0,B=w(b)>0$，粗事件一致性为

$$
\frac{2w(\lambda)A}{2w(\lambda)A+B}=\frac{A}{A+B}.
$$

交叉相乘即得 $2w(\lambda)=1$。由上一命题 $w(\lambda)=|\lambda|^p$，所以

$$
2\left(\frac1{\sqrt2}\right)^p=1,
$$

唯一给 $p=2$。

□

若删去第三端口而只保留 $(a,0)$，两次操作的共同比例会被射线归一消掉；该返回条件无法标定幅度尺度。若仅要求最后端口概率返回，也检测不到 active 块相对于旁观端口的符号翻转。单位圆盘有界性亦不可无声删除：缺少它，可加函数的非连续延拓能给满足少数标定点而非统一幂律的乘法权重。

**白话图景。**一条分支拆成两条，再合回去，必须与原来的同一条分支一致。旁边保留一条不动的内部参考，拆分过程就不能靠整体重新归一来掩盖比例变化。幅度每支变成原来的 $1/\sqrt2$，两支合起来仍是原事件，于是权重只能按幅度平方计算。

### 5.3 平方形式还必须绑定到同一个根

<a id="statement-5-4"></a>

#### 定理 5.4（全效果细分与同根 Born 绑定；v78 基线）

在有限维复 Hilbert 空间上，令根读出 $p_0$ 定义于全部效果 $0\preceq E\preceq I$，非负、$p_0(I)=1$，并在 $E+F\preceq I$ 时满足

$$
p_0(E+F)=p_0(E)+p_0(F).
$$

再给单位根 $\Omega_0$ 以及已取得的酉历史运输 $U_a$，要求

$$
p_0(P_{\Omega_0})=1,
\qquad p_a(E)=p_0(U_a^*EU_a).
$$

则

$$
\boxed{p_a(E)=\langle U_a\Omega_0,E\,U_a\Omega_0\rangle .}
$$

**证明。**

细分可加性与非负性给单调性。先由等份细分得到有理齐次性，再由单调性夹逼得到实齐次性。对正算子 $A$，取 $t>0$ 且 $t\ge\left\lVert A\right\rVert$，定义

$$
\ell(A)=t\,p_0(A/t).
$$

齐次性使它与 $t$ 无关，细分关系使它在正锥上可加。由正算子之差延伸到 Hermitian 空间，再复线性延伸。有限维迹对偶给唯一 $\rho\succeq0$、$\operatorname{Tr} \rho=1$，使 $p_0(E)=\operatorname{Tr} (\rho E)$。这是全效果概率表示的有限维论证[9](#ref-busch)。

同根校准给 $\operatorname{Tr} (\rho(I-P_{\Omega_0}))=0$。正算子
$\rho^{1/2}(I-P_{\Omega_0})\rho^{1/2}$ 的迹为零，故为零，迫使 $\rho$ 的支撑包含于一维根子空间。归一性给 $\rho=P_{\Omega_0}$。最后代入准备协变即得公式。

□

若删去同根校准，任意密度矩阵都满足第一组效果条件。例如 $\rho=I/d$ 可给合法概率，却一般不等于指定根的纯态概率。若只有固定小菜单，也不能直接把全效果域的结论移植过去；须使用项目有限覆盖和稳定性证书。

**白话图景。**合法的概率规则先只说明“有某个态在回答”。还要在同一个根上校准，并沿同一条门历史搬运读出，才能确认回答的正是这段历史。否则公式外形已经是 Born 形式，来源却可能绑到了另一个态上。

<a id="section-6"></a>

## 6. 完整正性：撤去保留参考，会漏掉哪一对关系

本节已经使用复态、张量接口及读出标定，故不是从完全未指定的关系集合再次推出这些前件。项目 V65 已有忠实内部参考的 Choi 判据[5](#ref-repo-v65)；以下把过程失败精确显示成二元关系。

### 6.1 任何负方向都能变成两个事件的矛盾

<a id="statement-6-1"></a>

#### 定理 6.1（最小二元正性见证）

令 $X=X^*$、$\operatorname{Tr}  X=1$。对秩一投影 $P$ 定义

$$
\mathcal B_P(X)=\begin{pmatrix}p&0\\0&1-p\end{pmatrix},\qquad p=\operatorname{Tr} (PX).
$$

则

$$
X\succeq0
\iff\mathcal B_P(X)\succeq0\text{ 对所有秩一 }P
\iff (0,0,2p-1)\in\overline B^3\text{ 对所有 }P.
$$

若 $\lambda<0$ 是负特征值，取对应 $P$，则三维报告坐标为
$(0,0,2\lambda-1)$，越出球面距离为 $-2\lambda$。

**证明。**

若 $X\succeq0$，则 $0\le\operatorname{Tr} (PX)\le1$，结论直接成立。反向，全部秩一方向非负意味着 $\langle v,Xv\rangle \ge0$ 对任意单位 $v$ 成立，即 $X\succeq0$。负谱情况直接代入即可。

□

报告映射本身是合法的二元测量通道：分别取 $\operatorname{ran}  P$ 及其正交补的基，以 $|0\rangle\langle a_j|$ 和 $|1\rangle\langle b_k|$ 为 Kraus 算子即可。球外结果表示候选预测自相矛盾，并非合法测量实际产生负概率。

一个结果的完整测量只有 $\{I\}$，总是报告一；两个结果已经足以暴露任意负谱。这是结果数的最小性。该见证仅占三维球的一条直径，未证明全体信息的最小表示维数为三。

**白话图景。**把总量归一成一，还可能把负数藏在某个事件里。取出这个事件，再把剩余事件合成另一个，两个权重就会变成“一负、一大于一”。三维球的那条直径已经能把矛盾画出来。

### 6.2 单体与两个边缘都正常，联合关系仍会失败

<a id="statement-6-2"></a>

#### 命题 6.2（转置的内部参考反例）

转置 $T(X)=X^{\mathsf T}$ 复线性、保迹且正，但不完全正。对同一个整体内部的两个角色，令

$$
|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2,
\qquad X=(\operatorname{id}\otimes T)(P_{\Phi^+}).
$$

则

$$
X=F/2,\qquad \operatorname{Tr}  X=1,\qquad
\operatorname{Tr} _A X=\operatorname{Tr} _R X=I/2,
$$

其中 $F|ij\rangle=|ji\rangle$。但对 $|\Psi^-\rangle=(|01\rangle-|10\rangle)/\sqrt2$，

$$
\operatorname{Tr} (P_{\Psi^-}X)=-\tfrac12,
\quad
\mathcal B_{P_{\Psi^-}}(X)=\operatorname{diag}(-\tfrac12,\tfrac32),
\quad Z=-2.
$$

**证明。**

正矩阵转置仍正，且转置保持迹。展开 $P_{\Phi^+}$ 并对第二因子转置，得到 $F/2$。交换算子在反对称向量上特征值为 $-1$，故给负权重。迹与边缘由矩阵单位展开直接得到。

□

只读计算基时，该候选报告 $(1/2,0,0,1/2)$，仍完全正常。因此必须能取得负方向效果，或取得足够联合层析信息。不能把迹为零的 $\{|01\rangle,|10\rangle\}$ 子块除以迹强行归一；完整二元事件报告没有这种问题。

**白话图景。**操作单独作用在一个角色上时看不出问题，连两个角色各自的边缘也都正常。一旦保留它与另一个内部角色的相干关联，某个联合事件就变成负权重。缺的关系正位于“这个过程与仍被保留的参考之间”。

### 6.3 一个忠实输入类型承载完整过程检查

<a id="statement-6-3"></a>

#### 定理 6.3（Choi--Kraus 结构；项目已有结果的复用）

设 $\Phi:M_d(\mathbb C )\to M_m(\mathbb C )$ 复线性，定义归一 Choi 矩阵

$$
C_\Phi=(\operatorname{id}_d\otimes\Phi)(P_{\Phi_d}),\qquad
|\Phi_d\rangle=d^{-1/2}\sum_i|ii\rangle.
$$

则下列条件等价：$\Phi$ 完全正；$\operatorname{id}_d\otimes\Phi$ 正；$C_\Phi\succeq0$；存在 $K_\alpha$ 使

$$
\Phi(X)=\sum_\alpha K_\alpha X K_\alpha^*.
$$

并且

$$
\Phi\text{ 保迹}\iff\operatorname{Tr} _B C_\Phi=I_d/d.
$$

在上述完全正性的等价条件成立时，保迹亦等价于
$\sum_\alpha K_\alpha^*K_\alpha=I_d$。

**证明。**

完全正显然推出前两项正性。若 $C_\Phi\succeq0$，写成 $\sum_\alpha|v_\alpha\rangle\langle v_\alpha|$，并按

$$
v_\alpha=d^{-1/2}\sum_i|i\rangle\otimes K_\alpha|i\rangle
$$

定义 $K_\alpha$。比较 $(i,j)$ 块得到矩阵单位上的 Kraus 公式，线性延伸给全部矩阵。任意参考张量后，每一项仍为正矩阵的共轭，所以完全正。

参考边缘的 $(i,j)$ 元为 $\operatorname{Tr} \Phi(E_{ij})/d$。它等于 $I_d/d$，恰当且仅当全部矩阵单位满足保迹条件。Kraus 形式下同一条件正是 $\sum_\alpha K_\alpha^*K_\alpha=I_d$。

□

标准来源见 Choi 原始论文与 Watrous 作者公开稿[10](#ref-choi)、[11](#ref-watrous)。对保 Hermitian、保迹而非 CP 的候选，$C_\Phi$ Hermitian 且迹一；定理[6.1](#statement-6-1)于是给一个球外二元报告。

保迹不能仅检查 $\operatorname{Tr}  C_\Phi=1$。例如 $K=\operatorname{diag}(\sqrt2,0)$，$\Phi(X)=KXK^*$，有 $C_\Phi=|00\rangle\langle00|$，却不保迹。完整矩阵边缘条件保留了对所有输入的归一关系。

实际应用中，须已经取得同一个 $\Phi$、完整张量作用 $\operatorname{id}\otimes\Phi$、满 Schmidt 秩探针及所需读出。只准许产品准备时，转置可以通过那些受限测试。一个输入态*类型*足够承载信息，不等于一次实验结果返回全部 Choi 矩阵。

**白话图景。**完整正性在这里成为“同一操作接上任何仍被保留的内部参考，联合报告仍合法”的定义约束。忠实输入把这项检查集中到一张共同关系表；若有缺陷，一个二元事件就能指给我们看。总量守恒则还须逐输入成立，所以落在参考边缘的整个矩阵上。

### 6.4 丢弃记录不等于整体信息消失

保迹 Kraus 形式给等距表示

$$
V\psi=\sum_\alpha K_\alpha\psi\otimes|\alpha\rangle,
\qquad V^*V=I,
\qquad \Phi(X)=\operatorname{Tr} _E(VXV^*).
$$

等距性由 $\sum_\alpha K_\alpha^*K_\alpha=I$ 直接得到，偏迹公式由记录基正交性得到。它说明数学上可以把局部过程写为保留记录的共同等距过程；实际角色、初始记录和控制是否可得，还须原生构造。

CP 保证含参考时的*合法性*，并不保证每个关系值不变。抹除通道也 CP，却可使局部输入不可区分。若完整记录保留在 $\Omega$ 内，关系可以转移到记录与其余部分中。

**白话图景。**窗口里看见的关系可以减少，因为窗口没有继续读取全部记录。把记录放回共同结构，等距过程保留的是整体内积；把记录忘掉后，剩下的是一个合法但可能丢失局部区分能力的通道。

<a id="section-7"></a>

## 7. 有限三维检查怎样拼成同一个整体

V63 已有共享锚的有限正核证书，OMEGA 已有精确相容局部态的无限延拓。这里补上一段带误差的连接：每层整张候选表甚至不必正半定，只要负谱残差消失，且旧历史关系的修订可控制。

### 7.1 共享锚把成对剩余关系放进同一张表

<a id="statement-7-1"></a>

#### 命题 7.1（共享锚修复；V63 结果）

设

$$
\Gamma=\begin{pmatrix}A&B\\B^*&C\end{pmatrix},\quad A>0,
\qquad S=C-B^*A^{-1}B.
$$

假定每个“同一组完整锚加任意至多两个新记录”的主块正半定，并有 $0\le S_{jj}\le\eta_j$。则

$$
G=\begin{pmatrix}A&B\\B^*&B^*A^{-1}B\end{pmatrix}\succeq0,
\qquad \operatorname{rank}  G=\dim A,
$$

$$
\boxed{\left\lVert \Gamma-G\right\rVert _{\rm op}\le\sum_j\eta_j.}
$$

**证明。**

共享锚块的 Schur 补给每个二阶残差块正性，因此
$|S_{jk}|\le\sqrt{\eta_j\eta_k}$。对任意 $z$，

$$
|z^*Sz|\le\left(\sum_j\sqrt{\eta_j}|z_j|\right)^2
\le\left(\sum_j\eta_j\right)\left\lVert z\right\rVert ^2.
$$

因 $S$ Hermitian，得到其算子范数界。$G$ 是
$\binom{A^{1/2}}{B^*A^{-1/2}}$ 与其伴随的乘积，因此正且有所述秩。$\Gamma-G$ 只有右下 $S$ 块，结论成立。

□

这不声称原矩阵 $\Gamma$ 已经正；也不容许每一对记录使用互不一致的锚身份或相位。它把所有局部二元证书放进一个共享参照下。

**白话图景。**分别画得通的两条关系，还可能属于彼此不一致的坐标图。让每一对新增记录都带上同一组锚，才能知道它们在比较同一个整体。未被锚解释的残差加起来，精确给出这张表离共同正核有多远。

### 7.2 带误差的整体核闭合

<a id="statement-7-2"></a>

#### 定理 7.2（递增历史表的稳定闭合）

设有限历史集 $S_1\subseteq S_2\subseteq\cdots$，$S=\bigcup_nS_n$，包含关系保留同一历史身份与相位约定。每层给 Hermitian 候选核 $K_n$，且 $K_n(a,a)=1$。假设

<a id="eq-overlap"></a>

$$
\sup_{a,b\in S_n}|K_{n+1}(a,b)-K_n(a,b)|\le\epsilon_n,
\qquad\sum_n\epsilon_n<\infty; \tag{6}
$$

<a id="eq-repair"></a>

$$
\text{存在 }G_n\succeq0\text{，使 }\left\lVert K_n-G_n\right\rVert _{\rm op}\le s_n,
\qquad s_n\to0. \tag{7}
$$

记 $E_n=\sum_{j\ge n}\epsilon_j$。则给定整条证据链有唯一逐点极限核 $K$，满足

$$
\boxed{|K(a,b)-K_n(a,b)|\le E_n\quad(a,b\in S_n).}
$$

该核归一且全部有限 Gram 块正半定，故有最小 Hilbert 实现

$$
\mathcal H_K=\overline{\mathbb C ^{(S)}/\mathcal N_K},\qquad
\langle \xi_a,\xi_b\rangle =K(a,b),
$$

唯一到保持历史标签的酉等价。若 $\operatorname{rank}  G_n\le r$ 统一成立，则 $\dim\mathcal H_K\le r$。

**证明。**

固定 $a,b\in S_N$。对 $m>n\ge N$，

$$
|K_m(a,b)-K_n(a,b)|\le\sum_{j=n}^{m-1}\epsilon_j,
$$

故该复数序列为 Cauchy 列，得到极限与尾界。共轭对称与单位对角在极限中保留。

任取有限个不同历史及系数 $c$。在所有包含该族的层上，把 $c$ 以零扩展，正修复给

$$
c^*K_nc\ge-s_n\left\lVert c\right\rVert ^2.
$$

令 $n\to\infty$，得 $c^*Kc\ge0$。因此可在有限形式线性组合上用 $K$ 定义半内积，商去零范数空间再完成，即得实现。任何另一最小实现的标签对应保持全部有限 Gram 和，所以延拓为酉。

若修复秩统一不超过 $r$，其任意固定有限块与 $K_n$ 有相同极限。所有 $(r+1)$ 阶子式逐层为零，连续性使极限子式也为零，因此任意有限极限 Gram 块秩不超过 $r$。生成空间维数于是至多 $r$。

□

在命题[7.1](#statement-7-1)中逐层取得 $s_n\le\sum_j\eta_{n,j}\to0$，即可供应正性修复前件。相容性检查作用于原候选 $K_n$，无需假定任意选出的修复 $G_n$ 彼此完全相容。

对同一层中的 $m$ 个历史，另有

$$
\left|c^*(K-K_n)c\right|
\le E_n\left(\sum_{i=1}^m|c_i|\right)^2
\le mE_n\left\lVert c\right\rVert ^2.
$$

所以有限 Gram 块的算子误差至多 $mE_n$。记录数增加时，不能把逐项尾界直接当成维数无关的整体算子误差。

**白话图景。**每次增加细节时，旧历史仍是那些旧历史，旧关系的修订总量也有控制。这样逐层得到的图才会趋向同一张图。共享锚留下的负谱残差逐渐消失，极限图便真正成为整体正核；表示空间由这张图长出来。

### 7.3 合法续接在极限中成为酉

<a id="statement-7-3"></a>

#### 推论 7.3（消失续接缺陷的传递）

设 $T:S\to S$ 是同一双射。对每个固定 $a,b$，在包含 $a,b,Ta,Tb$ 的各层上，若

$$
|K_n(Ta,Tb)-K_n(a,b)|\le\delta_n(a,b),\qquad\delta_n(a,b)\to0,
$$

则 $K(Ta,Tb)=K(a,b)$，且 $U_T\xi_a=\xi_{Ta}$ 唯一延拓为酉。

**证明。**

两次使用尾界给

$$
|K(Ta,Tb)-K(a,b)|\le2E_n+\delta_n(a,b)\to0.
$$

保核使有限组合的标签续接保持范数，因此零关系仍映到零关系，映射良定且等距。$T$ 满射使其像包含所有生成标签，等距像又闭，故延拓为满射等距，即酉。

□

若 $T$ 仅在部分合法域 $D$ 上定义，同一证明只给 $\overline{\operatorname{span} }\{\xi_a:a\in D\}$ 与像载体之间的等距。它不自动取消原生命令守卫或给出全部载体上的同一个物理酉门。若所有历史另外已证明可从根 $e$ 到达，才可进一步写 $\xi_a=U_a\xi_e$。

**白话图景。**同一续接越来越精确地保存同一批历史间的关系，极限中就得到精确保关系的门。门的合法范围仍由它实际能接在哪些历史后面决定；局部可以接，不会自动变成处处都能接。

### 7.4 撤去整体合同后的反例

每层都正，仍可能对同一对历史反复给冲突答案：

$$
K_n=\begin{pmatrix}1&(-1)^n/2\\(-1)^n/2&1\end{pmatrix}.
$$

每层特征值为 $1/2,3/2$，却无极限。甚至相邻误差趋零仍不够，取

$$
q_n=\tfrac12\sin\log(n+1),\qquad
K_n=\begin{pmatrix}1&q_n\\q_n&1\end{pmatrix}.
$$

有 $|q_{n+1}-q_n|\le1/(2(n+1))\to0$，但沿接近
$e^{\pi/2+2\pi k}$ 与 $e^{3\pi/2+2\pi k}$ 的整数子列分别趋向 $1/2,-1/2$。可求和是保证收敛的一项充分条件；它并非必要，例如 $q_n=(-1)^n/(n+2)$ 收敛而相邻绝对差之和发散。

没有统一秩界时，$S_n=\{1,\ldots,n\},K_n=I_n$ 的重叠误差全为零，极限载体却为 $\ell^2(\mathbb N)$。因此每个二元检查有限三维，不限制整个 $\Omega$ 的表示维数。若缺少跨层身份与相位对应，式[(6)](#eq-overlap)本身甚至尚未定义。

**白话图景。**每一张局部图都漂亮，不保证它们说的是同一个整体；每次改动很小，也可能一直缓慢漂移。身份、相位和累计误差把这些图接在一起。局部三维负责看清一对关系，整体维数则由所有关系共同需要的秩决定。

<a id="section-8"></a>

## 8. 把外加公理压成定义之间的相容条件

### 8.1 一套可继续审计的紧凑结构

本轮可把重构任务写成三组相互引用的定义约束，而不重复列一串互相独立的量子口号：

1. **共同来源与身份。** 历史、参考、记录、合法续接和读出都取自同一个内部结构；概念只合并在指定后续目标上不可区分的来源。有限表必须使用共同标签和相位，并具备能收敛的相容证据。

2. **相容运输与参考。** 实正几何保存交叉关系；参考与运输顺序相容；不可约扇区或同根零频率残差供应共同复方向。由此可构造复正核，平滑门流给 Hermitian 生成元。

3. **同源细分与保留参考的读出。** 粗事件与细分事件相容，幅度标定使用同一旁观参考；效果读出绑到同一根；局部过程接上实际保留参考仍合法，完整过程保持参考边缘。

这三组不是已经证明独立且最少的三条宇宙公理。每组含有可继续拆解的条件。定理[3.2](#statement-3-2)在固定线性接口中判定哪些关系可以删除；具体反例检验本轮推导缺少哪些前件。用三个标题打包，并不会减少真实信息量。

| 传统表述 | 本稿中的内部关系位置 | 推出的结构 |
| --- | --- | --- |
| 状态要保留历史 | 被当前概念合并的两来源，后续目标仍须相同 | 纤维下降与可恢复目标 |
| 采用复数 | 参考转动与运输相容，加上单频率来源 | $J^2=-I$、复内积与复正核 |
| 酉演化 | 同一可逆续接保存完整历史核 | 最小表示上的酉映射 |
| 薛定谔方程 | 平滑正交门流与共同 $J$ 相容 | $H=J\dot U U^{-1}$、$\dot U=-iHU$ |
| Born 平方 | 同参考下的合回与粗细事件一致；同根读出绑定 | 平方标量权重与指定历史的效果概率 |
| 完全正性 | 同一过程与保留参考组成的联合关系仍合法 | Choi 正性、Kraus 与等距记录表示 |
| 一个整体表示 | 递增关系表共身份、误差受控、正性残差消失 | 全局正核、最小 Hilbert 载体与相容续接 |

**白话图景。**只有一个整体，观察者、参考、门和记录都在里面。每个概念是对这张关系网的一种保留方式。要求两种定义描述同一个东西时，就让两条内部路由在共同读口上相遇；相遇不了，便找出具体缺失关系。能由其余关系保证的规则进入定理，仍能失败的规则保留为待解释的结构条件。

### 8.2 这一轮推进到的准确结论

现在可以证明的不是“只说一切都在 $\Omega$，复量子理论便唯一出现”，而是以下有明确前件的构造链：

$$
\begin{gathered}
\text{共同来源的内部关系与实正几何}\\
\Downarrow\quad\text{共同参考相容与单频率条件}\\
\text{复结构与有限正核证书}\\
\Downarrow\quad\text{共标定、重叠收敛与消失残差}\\
\text{整体正核及其最小表示}\\
\Downarrow\quad\text{保核续接、平滑性、同根细分与参考接口}\\
\text{酉门、Hermitian 生成元、Born 读出与 CP 局部过程}.
\end{gathered}
$$

该链条包含可选的不同入口：若已有 v78 的完整复正核，可直接从相应层开始；若从实关系出发，则本轮参考流定理提供另一条入口。二者不应循环引用。各箭头均保留所引定理的全部前件：本文 Born、Choi 和微分生成元的结论用于已声明的有限维接口，整体 Hilbert 载体则可以无限维。

剩余的真正研究问题，是让实正几何、参考可取得性、单频率相容、完整效果菜单及复合接口继续成为原生结构的结果。项目 V63 已在一个具体模型中完成其中部分工作，本稿给出其他充分条件与可反驳见证。理论的简洁性应以减少独立前件和增强可检验联系衡量。

**白话图景。**整个图景可以这样看：根的内部变化留下历史，历史之间可以互相比；共同参考让“转四分之一周”在各处含义一致，形成复方向；分支拆开又合回时，旁观参考锁住平方权重；保留另一部分的关联后，局部操作必须仍给合法事件；新增细节不断补图，旧关系受控地收敛，最终构成同一个整体。圆弧、门、概率和公理，都在这张内部关系图上各有一个可定义、可证明的位置。

## 资料与可复核位置

<a id="ref-repo-factor"></a>

1. 项目固定源码：[AnswerabilityCriterion.lean](https://github.com/the-omega-institute/trureturing/blob/d6cb695cddf0229369d07065719603d8784235f6/D5/S0/Rewriting/Quotients/AnswerabilityCriterion.lean)，`answerability_criterion`；直接使用 Mathlib 的函数纤维因子化判据。

<a id="ref-repo-recovery"></a>

2. 项目固定源码：[TargetRecoveryCriterion.lean](https://github.com/the-omega-institute/trureturing/blob/d6cb695cddf0229369d07065719603d8784235f6/D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean)。最小预测摘要的范围另见[MinimalPredictiveSummary.lean](https://github.com/the-omega-institute/trureturing/blob/d6cb695cddf0229369d07065719603d8784235f6/D5/S3/Quantum/Fibers/MinimalPredictiveSummary.lean)。

<a id="ref-repo-v63"></a>

3. 项目 V63：[原生复结构、稳定组装与有限 Born 读出证书](https://github.com/the-omega-institute/trureturing/blob/d6cb695cddf0229369d07065719603d8784235f6/docs/develop/theory/AURIC_NATIVE_COMPLEX_STRUCTURE_STABLE_ASSEMBLY_AND_FINITE_BORN_READOUT_CERTIFICATES_V63.md)，尤其 §§2.1--2.4、5.2--5.5、6。

<a id="ref-repo-v64"></a>

4. 项目 V64：[近似关系刚性、平方标定与读出稳定性](https://github.com/the-omega-institute/trureturing/blob/d6cb695cddf0229369d07065719603d8784235f6/docs/develop/theory/AURIC_APPROXIMATE_RELATIONS_RIGIDITY_SQUARE_CALIBRATION_AND_QUANTUM_READOUT_STABILITY_V64.md)，§2。

<a id="ref-repo-v65"></a>

5. 项目 V65：[忠实内部关系与量子过程重构](https://github.com/the-omega-institute/trureturing/blob/d6cb695cddf0229369d07065719603d8784235f6/docs/develop/theory/AURIC_FAITHFUL_INTERNAL_RELATIONS_AND_QUANTUM_PROCESS_RECONSTRUCTION_V65.md)，定理2.2、命题2.3--2.4、§10.5。

<a id="ref-repo-v68"></a>

6. 项目 V68：[可见关系秩、相容约束与量子公理](https://github.com/the-omega-institute/trureturing/blob/d6cb695cddf0229369d07065719603d8784235f6/docs/develop/theory/AURIC_VISIBLE_RELATION_RANK_COMPATIBLE_CONSTRAINTS_AND_QUANTUM_AXIOMS_V68.md)，§7。

<a id="ref-repo-omega"></a>

7. 项目 OMEGA：[静态相容纤维理论](https://github.com/the-omega-institute/trureturing/blob/d6cb695cddf0229369d07065719603d8784235f6/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，§12.2 的精确局部态相容与 GNS 延拓。

<a id="ref-woit"></a>

8. P. Woit, *Quantum Theory, Groups and Representations*, 作者公开稿，2025年10月20日更新。[作者 PDF](https://www.math.columbia.edu/~woit/QMbook/qmbook.pdf)。用于表示论背景；本稿参考流推导已自足证明。

<a id="ref-busch"></a>

9. P. Busch, *Quantum States and Generalized Observables: A Simple Proof of Gleason's Theorem*, Phys. Rev. Lett. 91, 120403 (2003). [arXiv:quant-ph/9909073](https://arxiv.org/abs/quant-ph/9909073)。

<a id="ref-choi"></a>

10. M.-D. Choi, *Completely positive linear maps on complex matrices*, Linear Algebra Appl. 10 (1975), 285--290. [DOI:10.1016/0024-3795(75)90075-0](https://doi.org/10.1016/0024-3795(75)90075-0)。本轮核对出版社元数据与摘要；直接全文访问受限。

<a id="ref-watrous"></a>

11. J. Watrous, *The Theory of Quantum Information*, Chapter 2，Theorems 2.22、2.26，及转置映射讨论。[作者公开章节](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)。

## 源稿前言与排版元数据

```tex
% !TEX program = xelatex
% Compile twice with XeLaTeX. Fallback font: fonts/NotoSerifCJKsc-Regular.otf.
\documentclass[11pt,a4paper]{article}
\usepackage[margin=24mm,headheight=16pt]{geometry}
\IfFileExists{ctex.sty}{\usepackage[UTF8,fontset=auto]{ctex}}{
  \usepackage{fontspec}
  \IfFontExistsTF{Noto Serif CJK SC}{\setmainfont{Noto Serif CJK SC}[AutoFakeBold=1.7]}{\setmainfont{NotoSerifCJKsc-Regular.otf}[Path=fonts/,AutoFakeBold=1.7,AutoFakeSlant=.15]}
  \XeTeXlinebreaklocale "zh"
  \XeTeXlinebreakskip=0pt plus 1pt
}
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage{xcolor,booktabs,array,tabularx,longtable}
\usepackage{fancyhdr,enumitem,hyperref,needspace}
\definecolor{ink}{HTML}{17384A}
\definecolor{accent}{HTML}{007D86}
\hypersetup{colorlinks=true,linkcolor=ink,urlcolor=accent,citecolor=ink,pdftitle={AURIC v78 后续研究：从二元失败见证到整体量子关系}}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small AURIC / v78 后续研究}
\fancyhead[R]{\small 内部关系、约束与量子表示}
\fancyfoot[C]{\thepage}
\setlength{\parindent}{1.8em}
\setlength{\parskip}{4pt}
\setlength{\emergencystretch}{3em}
\setlist{nosep,leftmargin=2em}
\renewcommand{\baselinestretch}{1.10}
\renewcommand{\contentsname}{目录}
\renewcommand{\abstractname}{摘要}
\renewcommand{\refname}{资料与可复核位置}
\renewcommand{\proofname}{证明}
\theoremstyle{definition}
\newtheorem{definition}{定义}[section]
\newtheorem{theorem}[definition]{定理}
\newtheorem{proposition}[definition]{命题}
\newtheorem{corollary}[definition]{推论}
\newtheorem{remark}[definition]{说明}
\newcommand{\ip}[2]{\langle #1,#2\rangle}
\newcommand{\norm}[1]{\left\lVert #1\right\rVert}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\tr}{\operatorname{Tr}}
\newcommand{\Span}{\operatorname{span}}
\newcommand{\ran}{\operatorname{ran}}
\newcommand{\dist}{\operatorname{dist}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\plain}[1]{\par\noindent\textbf{白话图景。}#1\par}
\newcommand{\repo}[2]{\href{https://github.com/the-omega-institute/trureturing/blob/d6cb695cddf0229369d07065719603d8784235f6/#1}{#2}}
\title{\color{ink}\bfseries 从二元失败见证\protect\\到整体量子关系\protect\\[5pt]\large AURIC v78 后续研究：定义、定理与证明}
\author{研究续稿}
\date{2026 年 11 月 2 日}
```

```tex
\begin{document}
\maketitle
\setcounter{tocdepth}{1}
{\small\setlength{\parskip}{0pt}\tableofcontents}
\newpage
\begin{center}\small
\end{center}
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.16\textwidth}XX@{}}
\toprule
\midrule
\bottomrule
\end{tabularx}
\end{center}
\Needspace{8\baselineskip}
\Needspace{12\baselineskip}
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}p{.18\textwidth}XX@{}}
\toprule
\midrule
\bottomrule
\end{tabularx}
\end{center}
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}p{.18\textwidth}XX@{}}
\toprule
\midrule
\bottomrule
\end{tabularx}
\end{center}
\clearpage
\begin{thebibliography}{99}
\small\raggedright
\end{thebibliography}
\end{document}
```
