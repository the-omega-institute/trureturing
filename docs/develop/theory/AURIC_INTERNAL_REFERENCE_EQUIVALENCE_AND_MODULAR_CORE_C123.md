AURIC 量子关系研究工作稿

# C123

**内部参照等价 与模相容核**

从两份参照的回接关系，
,到有限噪声闭包、

三维几何与可恢复内容的完整分类

**本轮唯一候选。**对于同一条内部读出过程，两份参照定义同一条反向二元规则，当且仅当其中一份的回推能完整接回另一份。参照可以改变可恢复内容的状态与权重，而未读部分的条件状态保持不变。

**本轮推进。**将上一轮的指定参照回推，推进为参照等价类；证明这些类的块结构，找出某份参照能够准确恢复的最大代数，并把看似无穷的模相容要求化成有限个二元交换关系。

**理论地位。**这是一个有明确对象前件的关系理论候选。Petz 充分性、算子代数纠错与模不变性是已知数学；本稿将它们组织成可核查的内部参照理论，并自足证明所需有限维结果。候选本身也容纳经典模型，量子对象的选择条件另外写明。

2026 年 11 月 4 日（新加坡时间）

仓库固定快照 `5ccf20964da0a6695170f80f89e8383c92913a6c`

提交时间：2026-11-03 16:57:05 UTC / 2026-11-04 00:57:05 SGT

完整自含 TeX 源码；使用 XeLaTeX 编译


> 参考输入：AI-authored source supplied in the current Codex session; date 2026-11-04 (Asia/Singapore). Lean, not this prose, is the repository truth source.

一个内部观察者必须用已经供应的参照来解释一次读出，但这一参照是否带入了不必要的偏向，不能仅凭“所有东西都在 $\Omega$ 中”回答。本文提出本轮唯一的定义相容候选：对于同一过程 $\mathcal N$，两份满秩内部参照 $\rho,\sigma$ 给出同一反向规则，当且仅当 $\mathcal R_\sigma\mathcal N(\rho)=\rho$。

在有限复矩阵部门，二元配对确定

$$
\mathcal R_\sigma(Y)=\sigma^{1/2}\mathcal N^*\!\left(
 [\mathcal N(\sigma)]^{-1/2}Y[\mathcal N(\sigma)]^{-1/2}\right)\sigma^{1/2},
$$

其中逆只在共同输出支持上使用。本文证明参照等价，给出等价类的完整形状
$\rho=\bigoplus_\alpha R_\alpha\otimes\omega_\alpha$：可恢复部分 $R_\alpha$ 可以改变，条件余量 $\omega_\alpha$ 固定。

若 $E_i$ 为 $\mathcal N$ 的 Kraus 算子，则过程本身的最大准确可恢复代数为
$\mathfrak A_{\mathcal N}=\{E_i^*E_j\}'$；特定参照的回接固定代数则为

$$
\mathfrak F_\sigma=
 \bigcap_{t\in\mathbb R}\sigma^{it}\mathfrak A_{\mathcal N}\sigma^{-it}
 =\left\{(\operatorname{ad}_{\log\sigma})^k(E_i^*E_j):
 i,j,\ 0\le k\le d^2-1\right\}'.
$$

因此“关系的关系”落实为有限噪声配对与参照生成的闭包。二元 qubit 中，这一闭包由噪声轴、参照横向方向及其叉积构成清楚的三维图像。

有限二元判别可以在已声明且饱和的维数内构造接近中性参照的准备；但未被控制触及的自由度和中心权重不会自动消失。精确固定代数的维数还可能随任意小的参照变化跳变，而任意固定次数的回接仍连续。本文给出该现象的精确 diamond 距离，并区分有限实验误差、数学支持和实际操作供应。

最后自足列出从实二元块到复原子、Born 规则、仪器、完全正性、张量积、酉过程及连续动力学的条件推导。本文建立的是有限量子关系理论与内部参照的完整接口；具体标准模型场、物理时钟与唯一宇宙态并不由这一候选决定。

**白话。**两个观察者可以拿不同的起点看同一条过程。真正该比较的，不是起点的名字是否一样，而是换了起点之后，往回读的规则有没有变。如果新起点本来就能被旧规则完整接回，它们其实在使用同一套未读关系，只是把可恢复部分的内容和权重改了。如果改动碰到了未读部分怎样依附于内容的结构，回推规则就会改变。把每一对过程的相互影响与参照放在一起检查，能接回的部分就成为一个可计算的代数；在最小量子块中，它呈现为球里的轴、平面和第三个旋转方向。

## 目录

- [1. 最新项目进展与本轮唯一候选](#section-1)
- [2. 参照等价：同一反向规则的完整有限维分类](#section-2)
- [3. 读口能保住什么：二元噪声关系与参照的模相容核](#section-3)
- [4. 一个读口、一份参照，以及它们生成的三维几何](#section-4)
- [5. 内部参照的有限证书：能制备什么，能稳定认证什么](#section-5)
- [6. 三份参照、多个观察者与内生关系的边界](#section-6)
- [7. 候选与通常有限量子力学的完整推导接口](#section-7)
- [8. 有限量子原子的实关系选择：前提与完整证明](#section-8)
- [参考文献](#references)

<a id="section-1"></a>

## 1. 最新项目进展与本轮唯一候选

<a id="sec-c123-scope"></a>

### 1.1 本轮实际核读的仓库增量

本轮以公开仓库 `dev` 分支的固定提交
`5ccf20964da0a6695170f80f89e8383c92913a6c` 为证据边界。
该提交于 2026-11-03 16:57:05 UTC 合并 PR
#26143，题为
*positive calibration rank*。相对其首父提交，改动为理论文件
*AURIC Internal Balanced Calibration and Filter Composition Geometry C113*
新增 381 行，集中在 §§20–22。本文核读了这部分全文，以及其依赖的有限设计、正分支和精确端点定义。 [1](#ref-repo-c123)

新增结果研究一个*固定的*正复线性成功分支 $T$，其成功效果为
$E=T^*(I)$，读回由指定等距 $J$ 给出。供应精确有限复射影二阶设计后，
记饱和缺口为 $\delta=Q-R\ge0$，并令

$$
D=d(d+1)\delta,\quad r=\operatorname{rank} E,\quad
 M=\|E\|,\quad t=\operatorname{Tr} E,\quad k=\dim K.
$$

它给出不含最小正本征值倒数的界

<a id="eq-c123-repo-bound"></a>

$$
\|T-J\sqrt E(\,\cdot\,)\sqrt E J^*\|_\diamond
 \le\min\{t+M,\sqrt{2kMD},2\sqrt{dMD},(\sqrt{2r}+3)\sqrt{MD}\}.
\tag{1}
$$

此处 $\|\cdot\|_\diamond$ 不带 $1/2$。界包括奇异效果、矩形输出及目标支持外的泄漏；其数学参考范数量词不额外供应实际参考系统。

项目同时保留一个决定性的边界：任意小的正饱和缺口都不能单独保证原映射恰好完全正。例如在一个至少二维支持中，恒等映射与转置的任意非零小凸混合仍可非完全正，其缺口却趋于零。新增文本还明确保留设计、效果与读口的精确标定前件，不能把同一个误差界当作全部装置漂移的总误差预算。

这一进展对本轮的作用很具体：内部比较应当写清所作用的*实际支持与实际关系*。选中某一分支、确定某一参照或恢复某一代数，都不自动覆盖未被比较的自由度。下文会以同样方式区分：过程本身可保留的内容、特定参照可回接的内容，以及有限数据能够认证的范围。

### 1.2 将“无外部参照”变成可检查的问题

设 $\Omega$ 表示全部内部对象、历史及其接续关系。本文不预先把 $\Omega$ 等同于一个 Hilbert 向量。有限观察窗口的代数记为 $\mathcal A$，其当前准备或评价记为 $\omega$；在矩阵表示中用密度矩阵 $\sigma$ 表示某一满秩内部参照。

“内生”在这里有两层严格含义。第一，准备、控制、读口与参照运输都属于同一实际关系系统；证明不从外部免费加装复位、联合参考或任意门。第二，一个约束必须比较已定义量的两种构造，使同一记录不会得到冲突的解释。它并不意味着只写出“所有东西都在内部”就能唯一选出全部数学结构。

令 $\mathcal N:M_d(\mathbb C)\to\mathcal B(K_0)$ 为同一条通道，
$K_0=\operatorname{supp}\mathcal N(I)$，$\sigma>0$、$\operatorname{Tr}\sigma=1$，
$\tau=\mathcal N(\sigma)>0$。已有二元配对为

<a id="eq-c123-binary-pair"></a>

$$
b_{\sigma,\mathcal N}(A,B)
 =\operatorname{Tr}\!\left[B\mathcal N(\sigma^{1/2}A\sigma^{1/2})\right].
\tag{2}
$$

$A,B$ 是两端效果。平方根夹乘来自已选定的内部滤片语义；若要由有限校准选出它，使用上节提及的精确饱和结果。不能在证明 Born 或量子对象之前，把式 [(2)](#eq-c123-binary-pair) 当作无结构前件的概率定义。

反向规则 $\mathcal R_\sigma$ 由交换两端的配对条件

<a id="eq-c123-reciprocity"></a>

$$
b_{\sigma,\mathcal N}(A,B)
 =b_{\tau,\mathcal R_\sigma}(B,A)
\tag{3}
$$

确定。下一节证明它是 Petz 回推，并给出完整有限维分类。

### 定义 1.1（反向规则等价）

两份满秩参照 $\rho,\sigma$ 称为对同一 $\mathcal N$ 反向等价，记为
$\rho\sim_{\mathcal N}\sigma$，若对每个输出准备 $\eta$ 与源端效果 $A$，

$$
\operatorname{Tr}[A\mathcal R_\rho(\eta)]
 =\operatorname{Tr}[A\mathcal R_\sigma(\eta)].
$$

这是两个过程在二元“准备–读口”关系上的等价，等价于
$\mathcal R_\rho=\mathcal R_\sigma$ 在整个 $\mathcal B(K_0)$ 上成立。
若有实际供应的张成准备族和张成效果族，精确检验可缩为有限个比较。

### 定义 1.2（唯一候选 C123：参照更新的二元回接相容律）

在同一内部过程、共同输出支持及前述配对语义内，要求

<a id="eq-c123-candidate"></a>

$$
\boxed{\quad
 \rho\sim_{\mathcal N}\sigma
 \quad\Longleftrightarrow\quad
 \mathcal R_\sigma\mathcal N(\rho)=\rho.
 \quad}
\tag{4}
$$

右侧也只需比较所有源端二元效果的概率。相容律要求：一次可完整接回的内部参照更换，与保持同一反向规则，是同一件事的两种定义。

该候选不要求任意两份参照都等价。它只确定等价的条件及其后果。
在本文明列的有限量子对象中，式 [(4)](#eq-c123-candidate) 是可证明的相容定理；在更原始的 $\Omega$ 关系语言中，它可作为需要被满足或被反例否定的选择条件。本文不把这一数学定理重新宣称为尚未发现的物理规律。

### 1.3 反着推：哪些删除会让理论失效

以下反例分别定位承重的关系，后文逐项展开。

1. **删掉不同过程分支之间的比较。**
   对 $E_0=I/\sqrt2,E_1=Z/\sqrt2$，两个自比较
   $E_i^*E_i=I/2$ 都看不出噪声，但交叉比较 $E_0^*E_1=Z/2$ 排除了 $X,Y$ 的准确保留。只看“每个门自己是否合法”会错误地宣布整块可恢复。

2. **删掉参照相容。**
   同一个 $Z$ 读出保留对角内容；横向偏置参照却使它的 Petz 回接无法原样返回整条 $Z$ 轴。物理过程保住了信息，不保证某份参照定义的回推也保住它。

3. **把“允许更换”改成“所有参照都可任意更换”。**
   若全部满秩态共用一个回推，则它与 $\mathcal N$ 的复合固定全部满秩态。由这些态张成自伴空间，复合必须为恒等映射。这会排除通常的有损读出，而不是解释它。

4. **删掉共同支持或实际维数声明。**
   支持外的逆没有定义；未触及的重数部门也可能保留任意偏向。局部测试不能凭空认证一个观察者已经包含全部相关结构。

5. **用近似零代替精确零。**
   固定代数维数可因任意小参照偏置而改变。有限误差应控制恢复概率或距离，不能直接宣告某个精确代数已被实验唯一识别。

**白话。**如果只检查每个过程自己，就看不到两个过程之间泄漏了什么；如果只看过程能保住什么，又会漏掉参照在回读时带来的偏向。真正要锁住的是两份定义：一份参照能否被完整接回，以及它是否仍在使用同一套反向关系。允许这两份定义互相校验，起点就不必被指定成唯一特权状态；能换什么、不能换什么，都有了可证明的边界。

<a id="section-2"></a>

## 2. 参照等价：同一反向规则的完整有限维分类

<a id="sec-c123-reference-equivalence"></a>

本章在已选定的有限复矩阵、完全正过程与迹概率语义内证明候选。
这里的 Petz 充分性、模不变条件期望和可恢复代数属于已有理论；下文给出适合本轮问题的有限维证明，尤其把“两个回推相同”的范围写成*整个共同输出支持*。相关原始结果见 Petz、Takesaki，以及关于 Petz 对偶与量子充分性的现代论述。 [2](#ref-petz1986)、[3](#ref-takesaki1972)、[5](#ref-furuya2022)、[6](#ref-ahmad2025)

### 2.1 共同支持、二元配对与唯一回推

设 $H\simeq\mathbb C^d$，$\mathcal N:\mathcal B(H)\to\mathcal B(K)$ 为通道，

$$
\mathcal N(X)=\sum_iE_iXE_i^*,\qquad \sum_iE_i^*E_i=I_H.
$$

令 $K_0=\operatorname{supp}\mathcal N(I_H)$。由于
$\mathcal N(I_H)=\sum_iE_iE_i^*$，有
$K_0=\operatorname{span}_iE_iH$；以下所有输出算子均限制到 $K_0$。
若 $\sigma>0$，则存在 $a,b>0$ 使 $aI\le\sigma\le bI$，故
$a\mathcal N(I)\le\mathcal N(\sigma)\le b\mathcal N(I)$。
因此所有忠实参照共用同一个输出支持，且
$\tau=\mathcal N(\sigma)>0$ 在 $K_0$ 上可逆。

写 $\Gamma_\sigma(X)=\sigma^{1/2}X\sigma^{1/2}$。
上节二元配对的互易条件，经迹对偶成为
$\mathcal R_\sigma\Gamma_\tau=\Gamma_\sigma\mathcal N^*$，因而唯一给出

<a id="eq-c123-petz"></a>

$$
\boxed{\quad
 \mathcal R_\sigma(Y)
 =\sigma^{1/2}\mathcal N^*(\tau^{-1/2}Y\tau^{-1/2})\sigma^{1/2}.
 \quad}
\tag{5}
$$

这一步只用效果的实线性包包含全部自伴算子，以及迹配对非退化。
令

<a id="eq-c123-petz-kraus"></a>

$$
L_i=\sigma^{1/2}E_i^*\tau^{-1/2}.
\tag{6}
$$

则 $\mathcal R_\sigma(Y)=\sum_iL_iYL_i^*$，并且
$\sum_iL_i^*L_i=\tau^{-1/2}\mathcal N(\sigma)\tau^{-1/2}=I_{K_0}$。
故 $\mathcal R_\sigma$ 完全正且保迹，同时
$\mathcal R_\sigma(\tau)=\sigma$。

定义回接与其 Heisenberg 固定空间

<a id="eq-c123-fixed-definition"></a>

$$
\mathcal T_\sigma=\mathcal R_\sigma\mathcal N,
 \qquad
 \mathfrak F_\sigma=\operatorname{Fix}(\mathcal T_\sigma^*).
\tag{7}
$$

直接取迹伴随得到

<a id="eq-c123-weighted-symmetry"></a>

$$
\mathcal R_\sigma^*=\Gamma_\tau^{-1}\mathcal N\Gamma_\sigma,
 \qquad
 \mathcal T_\sigma\Gamma_\sigma
 =\Gamma_\sigma\mathcal T_\sigma^*.
\tag{8}
$$

第二个等式把“固定效果”与“固定状态”联系起来，但尚未说它们在通常乘法下是同一个代数。

### 2.2 从正性等号到有限模结构

### 引理 2.1（Schwarz 等号的可检验形式）

<a id="lem-c123-schwarz"></a>

设 $\Phi(Y)=W^*(Y\otimes I)W$ 为含幺完全正映射，$W^*W=I$。
则

$$
\Phi(Y^*Y)-\Phi(Y)^*\Phi(Y)
 =W^*(Y^*\otimes I)(I-WW^*)(Y\otimes I)W\ge0.
$$

等号等价于 $(Y\otimes I)W=W\Phi(Y)$。
若对 $Y$ 和 $Y^*$ 均取等号，则对任意 $Z$，

$$
\Phi(YZ)=\Phi(Y)\Phi(Z),\qquad
 \Phi(ZY)=\Phi(Z)\Phi(Y).
$$

**证明。**
展开右侧即得差式；该式是
$((I-WW^*)(Y\otimes I)W)^*((I-WW^*)(Y\otimes I)W)$。
其为零当且仅当相应向量映射为零。再对 $Y^*$ 使用同一结论并取伴随，即可在 $\Phi(YZ)$ 和 $\Phi(ZY)$ 中插入 $WW^*$，得到乘法等式。

### 定理 2.2（有限 Takesaki 条件：参照与子代数的三种等价描述）

<a id="thm-c123-finite-takesaki"></a>

设 $\mathcal A\subseteq\mathcal B(H)$ 为含幺 $*$-子代数，$\sigma>0$ 为
$\operatorname{Tr}\sigma=1$ 的密度矩阵。
存在正交分解

<a id="eq-c123-algebra-blocks"></a>

$$
H=\bigoplus_\alpha L_\alpha\otimes R_\alpha,
 \qquad
 \mathcal A=\bigoplus_\alpha\mathcal B(L_\alpha)\otimes I_{R_\alpha}.
\tag{9}
$$

在该分解下，下列条件等价：

1. 存在含幺完全正投影 $\mathcal E:\mathcal B(H)\to\mathcal A$，满足
    $\operatorname{Tr}\sigma\mathcal E(X)=\operatorname{Tr}\sigma X$。

2. 存在 $S_\alpha>0$ 与忠实密度矩阵 $\omega_\alpha$，使


   <a id="eq-c123-reference-blocks"></a>

   $$
   \sigma=\bigoplus_\alpha S_\alpha\otimes\omega_\alpha,
     \qquad \sum_\alpha\operatorname{Tr} S_\alpha=1.
   \tag{10}
   $$

3. 对所有 $t\in\mathbb R$，
    $\sigma^{it}\mathcal A\sigma^{-it}=\mathcal A$。

若这些条件成立，保持 $\sigma$ 的条件期望唯一，且为

<a id="eq-c123-conditional-expectation"></a>

$$
\mathcal E(X)=\bigoplus_\alpha
 \bigl[(\operatorname{id}_{L_\alpha}\otimes\varphi_{\omega_\alpha})(P_\alpha XP_\alpha)\bigr]
 \otimes I_{R_\alpha},\qquad
 \varphi_{\omega}(B)=\operatorname{Tr}(\omega B).
\tag{11}
$$

这里 $P_\alpha$ 是相应中心块的投影。

**证明。**
先说明分解 [(9)](#eq-c123-algebra-blocks) 的有限代数来源。
以中心的最小投影分开各块；每个块中心只有标量。
在一块内取正交最小投影 $p_1,\ldots,p_n$，其和为该块单位。
最小性和谱分解给 $p_i\mathcal A p_i=\mathbb C p_i$。
若 $0\ne X\in p_i\mathcal A p_j$，则
$X^*X=\lambda p_j$、$XX^*=\lambda p_i$，故归一化后给连接两投影的部分等距。
“能够连接”是等价关系：两个相接的部分等距之积仍连接端点；
每个等价类中投影之和与 $\mathcal A$ 交换，因而中央。
中心只有标量，故所有 $p_i$ 均相连。
取 $v_i^*v_i=p_1$、$v_iv_i^*=p_i$，置 $e_{ij}=v_iv_j^*$。
这些是矩阵单位，且
$p_i\mathcal A p_j=\mathbb C e_{ij}$，因为
$v_i^*Xv_j\in p_1\mathcal A p_1$。
令 $R=p_1H$，映射 $\lvert i\rangle\otimes\xi\mapsto v_i\xi$ 给
$H\simeq\mathbb C^n\otimes R$，$\mathcal A=M_n\otimes I_R$。
对各中心块重复即可。

假定条件1。对 $A\in\mathcal A$，$A,A^*A,AA^*$ 都被 $\mathcal E$ 固定；引理~[2.1](#lem-c123-schwarz) 给出
$\mathcal E(AXB)=A\mathcal E(X)B$。
故跨中心块被消去。在一块内，$\mathcal E(I\otimes B)$ 既属于
$\mathcal B(L)\otimes I$，又与其中每个元素交换，因而等于
$\varphi(B)I$。正性和含幺性给出唯一密度矩阵 $\omega$，使
$\varphi(B)=\operatorname{Tr}\omega B$。双模性质遂给
$\mathcal E(A\otimes B)=\varphi(B)A\otimes I$。
保持 $\sigma$ 的条件先迫使 $\sigma$ 没有跨中心块，再由

$$
\operatorname{Tr}\sigma_\alpha(A\otimes B)
 =\operatorname{Tr}\sigma_\alpha(A\otimes I)\,\operatorname{Tr}\omega_\alpha B
$$

迫使 $\sigma_\alpha=S_\alpha\otimes\omega_\alpha$。
忠实性使两个因子都正定。这也证明唯一性。
反过来，式~[(11)](#eq-c123-conditional-expectation) 由正泛函、压缩与直和组成，完全正、含幺、幂等且保持 [(10)](#eq-c123-reference-blocks)，故条件2推出条件1。

条件2推出条件3可直接对每个乘积块取幂。反过来，连续的模作用必须逐点固定有限个最小中心投影，故 $D=\log\sigma$ 分块。
在一块上，取重数空间的自伴基 $I,F_1,\ldots$，其中 $F_\mu$ 无迹，写
$D=H_0\otimes I+\sum_{\mu>0}H_\mu\otimes F_\mu$。
模不变的零点导数给
$[D,A\otimes I]\in\mathcal B(L)\otimes I$，所以
$[H_\mu,A]=0$ 对一切 $A$ 成立。
于是 $\mu>0$ 的 $H_\mu$ 全是标量，
$D=H_L\otimes I+I\otimes H_R$。
指数化并归一化第二因子得到条件2。

### 定理 2.3（回接的固定代数与全部固定状态）

<a id="thm-c123-fixed-blocks"></a>

$\mathfrak F_\sigma$ 是含幺 $C^*$-子代数，在 $\sigma$ 的模作用下不变。
在它的分解 [(9)](#eq-c123-algebra-blocks) 中，$\sigma$ 具有乘积块
[(10)](#eq-c123-reference-blocks)，并且

<a id="eq-c123-fixed-states"></a>

$$
\operatorname{Fix}(\mathcal T_\sigma)
 =\Gamma_\sigma(\mathfrak F_\sigma)
 =\left\{\bigoplus_\alpha Q_\alpha\otimes\omega_\alpha:
 Q_\alpha\in\mathcal B(L_\alpha)\right\}.
\tag{12}
$$

其中的密度矩阵恰由 $Q_\alpha\ge0$、$\sum_\alpha\operatorname{Tr} Q_\alpha=1$ 给出；忠实性等价于每个 $Q_\alpha>0$。

**证明。**
记 $\Psi=\mathcal T_\sigma^*$。若 $\Psi(A)=A$，则
$D=\Psi(A^*A)-A^*A\ge0$，而
$\operatorname{Tr}\sigma D=0$，因为 $\mathcal T_\sigma(\sigma)=\sigma$。
$\sigma>0$ 迫使 $D=0$，对 $AA^*$ 也一样。
由引理~[2.1](#lem-c123-schwarz)，固定元素可与任意乘积穿过 $\Psi$；故固定空间对乘法、伴随封闭，并含单位。

有限维 Ces
`aro 平均
$\mathcal E=\lim_{n\to\infty}n^{-1}\sum_{k=0}^{n-1}\Psi^k$
存在且投影到固定空间：含幺完全正性给 $\|\Psi^k\|\le1$，所以单位圆上的特征值没有非平凡 Jordan 块；除特征值1以外的平均均趋于零。
$\mathcal E$ 是保持 $\sigma$ 的含幺完全正投影。
定理~[2.2](#thm-c123-finite-takesaki) 给出模不变性及乘积块。
最后由 [(8)](#eq-c123-weighted-symmetry) 和 $\Gamma_\sigma$ 可逆，得到固定空间等式；块内
$\Gamma_\sigma(A_\alpha\otimes I)
=S_\alpha^{1/2}A_\alpha S_\alpha^{1/2}\otimes\omega_\alpha$，即得全部分类。

### 2.3 恢复等号迫使两端关系交织

### 引理 2.4（准确可恢复代数的共同输出表示）

<a id="lem-c123-output-representation"></a>

设 $\mathcal Q:\mathcal B(K_0)\to\mathcal B(H)$ 为通道，且某含幺
$*$-子代数 $\mathcal A$ 满足
$\mathcal N^*\mathcal Q^*(A)=A$ 对所有 $A\in\mathcal A$ 成立。
则 $\beta=\mathcal Q^*|_{\mathcal A}$ 是忠实含幺 $*$-表示，且

<a id="eq-c123-intertwiners"></a>

$$
\beta(A)E_i=E_iA,\qquad
 AM_j=M_j\beta(A),
\tag{13}
$$

其中 $M_j$ 为 $\mathcal Q$ 的任一组 Kraus 算子。
特别地

<a id="eq-c123-bimodule"></a>

$$
\mathcal N(AXB)=\beta(A)\mathcal N(X)\beta(B),\qquad
 \mathcal N^*\beta(A)=A\quad(A,B\in\mathcal A).
\tag{14}
$$

**证明。**
置 $Y=\mathcal Q^*(A)$。两次 Schwarz 不等式形成夹链

$$
A^*A\le\mathcal N^*(Y^*Y)
 \le\mathcal N^*\mathcal Q^*(A^*A)=A^*A.
$$

因此两次取等号。第二次的正缺陷在 $\mathcal N^*$ 下为零；若 $D\ge0$ 且 $\mathcal N^*(D)=0$，则
$\operatorname{Tr}\tau D=\operatorname{Tr}\sigma\mathcal N^*(D)=0$，$\tau>0$ 强制 $D=0$。
故 $\mathcal Q^*$ 在 $A$ 及 $A^*$ 处都满足 Schwarz 等号，限制到 $\mathcal A$ 成为 $*$-同态。其左逆 $\mathcal N^*$ 保证忠实性。
把引理~[2.1](#lem-c123-schwarz) 分别用于两条通道的 Kraus 等距表示，即得 [(13)](#eq-c123-intertwiners)；代入 Kraus 求和给出双模等式。

### 引理 2.5（模作用与加权配对的交织）

<a id="lem-c123-modular-intertwining"></a>

若 $\mathcal A$ 在 $\sigma$ 的模作用下不变，且表示 $\beta$ 满足
[(14)](#eq-c123-bimodule)，则对 $A\in\mathcal A$、$z\in\mathbb C$，

<a id="eq-c123-modular-intertwining"></a>

$$
\begin{aligned}
\tau^z\beta(A)\tau^{-z}
 &=\beta(\sigma^zA\sigma^{-z}),
\end{aligned}
\tag{15}
$$

<a id="eq-c123-weighted-intertwining"></a>

$$
\begin{aligned}
\mathcal N(\Gamma_\sigma(A))
 &=\Gamma_\tau(\beta(A)).
\end{aligned}
\tag{16}
$$

**证明。**
模不变性给 $\operatorname{ad}_{\log\sigma}(\mathcal A)\subseteq\mathcal A$，所以其复参数指数仍保持 $\mathcal A$。
双模等式对 $\mathcal N(\sigma A)
=\mathcal N((\sigma A\sigma^{-1})\sigma)$ 的两种计算给出
$\tau\beta(A)\tau^{-1}=\beta(\sigma A\sigma^{-1})$。
算子空间上的 $\operatorname{Ad}_\sigma$、$\operatorname{Ad}_\tau$ 可对角化，特征值都是正数。
在两者的有限特征值集合上，以一个多项式插值 $x\mapsto x^z$，将上述交织逐次迭代后线性组合，即得 [(15)](#eq-c123-modular-intertwining)。
最后

$$
\mathcal N(\sigma^{1/2}A\sigma^{1/2})
 =\beta(\sigma^{1/2}A\sigma^{-1/2})\tau
 =\tau^{1/2}\beta(A)\tau^{1/2}.\qedhere
$$

### 2.4 主定理：可完整接回的参照，恰好保留整个反向规则

### 定理 2.6（忠实参照等价）

<a id="thm-c123-reference-equivalence"></a>

对同一 $\mathcal N$ 及两份忠实状态 $\rho,\sigma$，下列条件等价：

1. $\rho\sim_{\mathcal N}\sigma$，即
    $\mathcal R_\rho=\mathcal R_\sigma$ 在*全部* $\mathcal B(K_0)$ 上成立。

2. $\mathcal T_\sigma(\rho)=\rho$。

3. $\rho=\Gamma_\sigma(a)$，其中 $a\in\mathfrak F_\sigma$ 正定，且
    $\operatorname{Tr}\sigma a=1$。

4. 在定理~[2.3](#thm-c123-fixed-blocks) 的分解中，


   <a id="eq-c123-equivalent-reference-class"></a>

   $$
   \rho=\bigoplus_\alpha Q_\alpha\otimes\omega_\alpha,
     \qquad Q_\alpha>0,\quad\sum_\alpha\operatorname{Tr} Q_\alpha=1.
   \tag{17}
   $$

因此条件2虽然只说一个状态能被恢复，却强制两个由各自参照定义的回推在共同输出角上完全相同。

**证明。**
条件1给
$\mathcal R_\sigma\mathcal N(\rho)
=\mathcal R_\rho\mathcal N(\rho)=\rho$。
条件2、3、4的等价已由定理~[2.3](#thm-c123-fixed-blocks) 给出。
只需证明条件4推出条件1；这里必须核对全部输出算子。

取 $\mathcal A=\mathfrak F_\sigma$，并置
$\beta=\mathcal R_\sigma^*|_{\mathcal A}$。
引理~[2.4](#lem-c123-output-representation) 与
[2.5](#lem-c123-modular-intertwining) 均适用。
乘积块保证

<a id="eq-c123-relative-filter"></a>

$$
C=\rho^{1/2}\sigma^{-1/2}
 =\bigoplus_\alpha Q_\alpha^{1/2}S_\alpha^{-1/2}\otimes I
 \in\mathfrak F_\sigma,
\tag{18}
$$

且 $C$ 在该代数内可逆。
令 $\gamma=\mathcal N(\rho)$。因为 $\rho=C\sigma C^*$，双模关系给
$\gamma=\beta(C)\tau\beta(C)^*$。
要取其正平方根，不能任意交换 $\beta(C)$ 与 $\tau$。
注意

$$
D=\sigma^{-1/4}C\sigma^{1/4}
   =\sigma^{-1/4}\rho^{1/2}\sigma^{-1/4}>0,
 \qquad D\in\mathfrak F_\sigma.
$$

模交织遂给

$$
\beta(C)\tau^{1/2}
 =\tau^{1/4}\beta(D)\tau^{1/4}>0.
$$

这个正算子的平方等于
$\beta(C)\tau\beta(C)^*=\gamma$，所以

<a id="eq-c123-output-root"></a>

$$
\gamma^{1/2}=\beta(C)\tau^{1/2},\qquad
 \gamma^{-1/2}=\tau^{-1/2}\beta(C)^{-1}.
\tag{19}
$$

于是，以同一组 $E_i$ 写出的新参照 Petz Kraus 算子逐项满足

$$
\rho^{1/2}E_i^*\gamma^{-1/2}
 =C\bigl(\sigma^{1/2}E_i^*\tau^{-1/2}\bigr)\beta(C)^{-1}
 =CL_i\beta(C)^{-1}=L_i.
$$

最后一步是 [(13)](#eq-c123-intertwiners)。
所以两条完全正映射在每个 $Y\in\mathcal B(K_0)$ 上相等；证明没有把量词缩到 $\mathcal N$ 的像。

### 推论 2.7（一个参照类中的可变与不变）

<a id="cor-c123-reference-class"></a>

同类忠实参照共用 $\mathcal T_\sigma$、$\mathfrak F_\sigma$ 及每块的余量态
$\omega_\alpha$。其全部自由度是

$$
Q_\alpha=p_\alpha\rho_\alpha^L,
 \qquad p_\alpha>0,\quad\sum_\alpha p_\alpha=1,
 \qquad \rho_\alpha^L>0,\quad\operatorname{Tr}\rho_\alpha^L=1.
$$

所以中心权重 $p_\alpha$ 与块内逻辑态 $\rho_\alpha^L$ 均可改变；固定的是各块条件余量态。该类是固定状态凸集的忠实部分，实维数为
$\sum_\alpha(\dim L_\alpha)^2-1$。

**证明。**
同一回推给同一回接与固定代数。结论随即来自
[(17)](#eq-c123-equivalent-reference-class)，其中每个正定逻辑矩阵贡献
$(\dim L_\alpha)^2$ 个实参数，总归一化减去一个参数。

忠实性与共同输出角是定理的明确前件。若原来还有 $K_0^\perp$，可人为补全为
$\widetilde{\mathcal R}_\sigma(Y)
=\mathcal R_\sigma(P_0YP_0)+\operatorname{Tr}[(I-P_0)Y]\,\xi$，
其中 $\xi$ 是任意密度矩阵。两次任意选取不同的补全态，当然可能得到不同的环境外延；上述等价没有认证不可达输入。
参照降秩时，$C^{-1}$ 和共同支持也可能消失，不能把忠实类的边界未经重证便纳入同一定理。

**白话。**把一份参照看成“我怎样给读到的结果补上其余部分”。如果新参照经过同一读口后，旧的补全办法能够把它原样接回，那么新参照自己算出的补全办法也完全一样。能自由换的是已经保住的逻辑内容，以及不同逻辑块出现的比例；每个块里被省略的那份条件余量不能随意换。起点因此可以不唯一，但允许怎样换起点已有一条精确规则。

<a id="section-3"></a>

## 3. 读口能保住什么：二元噪声关系与参照的模相容核

<a id="sec-c123-modular-core"></a>

上一章给出“参照能否更换”的完整分类。本章再回答：其中的固定代数来自哪里？
答案分成两个可分别计算的对象。二元分支比较决定*过程本身*能够准确保留的内容；参照的模作用再选出其中可被该 Petz 回推一致接回的部分。算子代数量子纠错中的最大可恢复代数是已有结果。 [4](#ref-beny2007)、[5](#ref-furuya2022)
这里把它与上一章的参照等价定理接成同一条有限证明链。

### 3.1 交叉关系决定最大可恢复代数

### 定义 3.1（过程的二元噪声关系与内禀可恢复代数）

记 $K_{ij}=E_i^*E_j$，并定义

<a id="eq-c123-intrinsic-algebra"></a>

$$
\mathfrak A_{\mathcal N}
 =\{K_{ij}:i,j\}'
 =\{A\in\mathcal B(H):[A,E_i^*E_j]=0\ \text{对所有 }i,j\}.
\tag{20}
$$

撇号表示交换子代数。因 $K_{ij}^*=K_{ji}$，这是含幺 $C^*$-子代数。
某子代数 $\mathcal A$ 称为可准确恢复，若存在一条通道 $\mathcal Q$，使
$\mathcal N^*\mathcal Q^*(A)=A$ 对全部 $A\in\mathcal A$ 成立。
这同时要求代数内所有效果的读数被恢复，且使用同一条 $\mathcal Q$。

### 定理 3.2（最大可恢复代数与规范输出表示）

<a id="thm-c123-maximal-correctable-algebra"></a>

$\mathcal A$ 可准确恢复，当且仅当
$\mathcal A\subseteq\mathfrak A_{\mathcal N}$。
而且存在唯一含幺 $*$-表示
$\beta_{\mathcal N}:\mathfrak A_{\mathcal N}\to\mathcal B(K_0)$ 满足

<a id="eq-c123-canonical-beta"></a>

$$
\beta_{\mathcal N}(A)E_i=E_iA,
 \qquad
 \beta_{\mathcal N}(A)
 =S^{-1/2}\mathcal N(A)S^{-1/2},
 \quad S=\mathcal N(I)>0.
\tag{21}
$$

它满足 $\mathcal N^*\beta_{\mathcal N}(A)=A$，且由最大混合参照
$\pi=I/d$ 的 Petz 回推实现：
$\beta_{\mathcal N}=\mathcal R_\pi^*|_{\mathfrak A_{\mathcal N}}$。

**证明。**
若 $\mathcal Q$ 恢复 $\mathcal A$，引理~[2.4](#lem-c123-output-representation) 给
$\beta(A)E_j=E_jA$ 及 $E_i^*\beta(A)=AE_i^*$。
因此 $AE_i^*E_j=E_i^*E_jA$，证明必要性。

反过来，设 $A\in\mathfrak A_{\mathcal N}$。
在 $K_0=\operatorname{span}_iE_iH$ 上定义

<a id="eq-c123-beta-span"></a>

$$
\beta_{\mathcal N}(A)\left(\sum_iE_i\xi_i\right)
 =\sum_iE_iA\xi_i.
\tag{22}
$$

核对良定义：令 $W(\xi_i)_i=\sum_iE_i\xi_i$，则
$W^*W=[E_i^*E_j]_{ij}$。
对角作用 $D_A(\xi_i)_i=(A\xi_i)_i$ 与该 Gram 矩阵交换，故保持
$\ker W=\ker W^*W$；因此零表示仍映为零。
乘法、单位关系直接来自 [(22)](#eq-c123-beta-span)；
$D_A$ 与 Gram 矩阵交换还给
$\beta_{\mathcal N}(A)^*=\beta_{\mathcal N}(A^*)$，所以它为 $*$-表示。
由于这些向量张成 $K_0$，交织关系也保证唯一性。
Kraus 求和给

$$
\mathcal N^*\beta_{\mathcal N}(A)=A,\qquad
 \beta_{\mathcal N}(A)S=\mathcal N(A)=S\beta_{\mathcal N}(A).
$$

这证明忠实性及 [(21)](#eq-c123-canonical-beta)。
最后 $\mathcal N(\pi)=S/d$，代入 Petz 伴随公式即得
$\mathcal R_\pi^*(A)=S^{-1/2}\mathcal N(A)S^{-1/2}$。
故同一条完全正保迹 $\mathcal R_\pi$ 恢复整个
$\mathfrak A_{\mathcal N}$，也恢复其每个子代数。

这个操作刻画说明 $\mathfrak A_{\mathcal N}$ 不依赖 Kraus 表示的选择。
式~[(20)](#eq-c123-intrinsic-algebra) 中所有 $i,j$ 都必需：只检查
$E_i^*E_i$ 会漏掉不同分支之间的相干比较。
例如 $E_0=I/\sqrt2,E_1=Z/\sqrt2$ 时，自比较都是 $I/2$，却有
$E_0^*E_1=Z/2$；真实可恢复代数是 $\operatorname{span}\{I,Z\}$。
这些 Kraus 分支是该通道的一种数学表示，不能由存在一种表示便推定每个分支已经被观察者单独供应。

### 3.2 参照只保留二元关系中模闭合的部分

定义参照的模作用

$$
\alpha_t^\sigma(A)=\sigma^{it}A\sigma^{-it},\qquad t\in\mathbb R.
$$

它是已给定矩阵代数内的权重比较变换；参数 $t$ 尚不等同于实验时间。
这里的“模相容”精确指一个子代数在这整族作用下保持闭合。

### 定理 3.3（模相容核定理）

<a id="thm-c123-modular-core"></a>

<a id="eq-c123-modular-core"></a>

$$
\boxed{\quad
 \mathfrak F_\sigma
 =\bigcap_{t\in\mathbb R}
 \sigma^{it}\mathfrak A_{\mathcal N}\sigma^{-it}.
 \quad}
\tag{23}
$$

因此 $\mathfrak F_\sigma$ 是
$\mathfrak A_{\mathcal N}$ 中最大的 $\sigma$-模不变含幺子代数。
在它上面，Petz 回推的 Heisenberg 作用总是同一个规范表示：

<a id="eq-c123-reference-independent-logical-read"></a>

$$
\mathcal R_\sigma^*(A)=\beta_{\mathcal N}(A),
 \qquad A\in\mathfrak F_\sigma.
\tag{24}
$$

**证明。**
定理~[2.3](#thm-c123-fixed-blocks) 说明 $\mathfrak F_\sigma$ 模不变，
而 $\mathcal R_\sigma$ 恢复该代数；最大性定理故给
$\mathfrak F_\sigma\subseteq\mathfrak A_{\mathcal N}$。
再施以所有 $\alpha_t^\sigma$，得到式~[(23)](#eq-c123-modular-core) 的正向包含。

为证反向，取任一模不变子代数
$\mathcal B\subseteq\mathfrak A_{\mathcal N}$。
规范表示 $\beta_{\mathcal N}|_{\mathcal B}$ 满足双模关系
[(14)](#eq-c123-bimodule)，所以引理~[2.5](#lem-c123-modular-intertwining) 给

$$
\mathcal N(\Gamma_\sigma(A))
 =\Gamma_\tau(\beta_{\mathcal N}(A)),\qquad A\in\mathcal B.
$$

两侧施以 $\Gamma_\tau^{-1}$，得到
$\mathcal R_\sigma^*(A)=\beta_{\mathcal N}(A)$，进而
$\mathcal N^*\mathcal R_\sigma^*(A)=A$。
故 $\mathcal B\subseteq\mathfrak F_\sigma$。
式~[(23)](#eq-c123-modular-core) 的右侧本身为含幺 $*$-子代数，且
$\alpha_s^\sigma$ 只将交集中参数 $t$ 平移为 $t+s$，所以它模不变。
取其作为 $\mathcal B$ 即得反向包含，也同时证明
[(24)](#eq-c123-reference-independent-logical-read)。

### 推论 3.4（给定目标代数的正确量词）

<a id="cor-c123-target-algebra"></a>

对任意含幺子代数 $\mathcal A$，以下三者等价：

<a id="eq-c123-target-criterion"></a>

$$
\mathcal R_\sigma\text{ 恢复 }\mathcal A
 \quad\Longleftrightarrow\quad
 \mathcal A\subseteq\mathfrak F_\sigma
 \quad\Longleftrightarrow\quad
 \alpha_t^\sigma(\mathcal A)\subseteq\mathfrak A_{\mathcal N}
 \quad(\forall t\in\mathbb R).
\tag{25}
$$

不要求 $\mathcal A$ 自身模不变，只要求它的整个模轨道仍在可恢复内容内。

**证明。**
第一等价是固定代数的定义，第二等价由
[(23)](#eq-c123-modular-core) 及将 $t$ 换成 $-t$ 得到。

这一区别确有实质：若 $\mathcal N=\operatorname{id}$，所有参照的回推都是恒等通道，每个子代数都被恢复；一个任意选取的子代数却未必对一般 $\sigma$ 的模作用不变。
只有当目标是整个 $\mathfrak A_{\mathcal N}$ 时，
[(25)](#eq-c123-target-criterion) 才等价于该最大代数自身的模不变性。

### 3.3 中心权重与余量态：两种不同的参照自由度

### 推论 3.5（哪些参照保住全部内禀可恢复内容）

<a id="cor-c123-full-intrinsic-reference"></a>

将 $\mathfrak A_{\mathcal N}$ 分块为
$\bigoplus_\alpha\mathcal B(L_\alpha)\otimes I_{R_\alpha}$。
则 $\mathfrak F_\sigma=\mathfrak A_{\mathcal N}$，当且仅当

<a id="eq-c123-fully-compatible-reference"></a>

$$
\sigma=\bigoplus_\alpha S_\alpha\otimes\omega_\alpha,
 \qquad S_\alpha>0,\quad \omega_\alpha>0,\quad
 \operatorname{Tr}\omega_\alpha=1,\quad\sum_\alpha\operatorname{Tr} S_\alpha=1.
\tag{26}
$$

这些参照在全部可恢复逻辑效果上的回读都是 $\beta_{\mathcal N}$。
固定各 $\omega_\alpha$ 而改变 $S_\alpha$，还会保持整个 Petz 回推不变；
若改变某个 $\omega_\alpha$，则落入不同的整个回推等价类。

**证明。**
由模核定理，$\mathfrak F_\sigma=\mathfrak A_{\mathcal N}$ 等价于该代数模不变；有限 Takesaki 定理将它化为
[(26)](#eq-c123-fully-compatible-reference)。
规范输出表示的结论来自
[(24)](#eq-c123-reference-independent-logical-read)。
最后两句由参照等价定理的完整固定状态分类给出。

例如 $\mathcal N=\operatorname{Tr}_R$ 时，
$\mathfrak A_{\mathcal N}=\mathcal B(L)\otimes I_R$。
产品参照 $\sigma_L\otimes\omega_R$ 给

$$
\mathcal R_\sigma(Y)=Y\otimes\omega_R.
$$

更换 $\sigma_L$ 完全不改变回推；更换 $\omega_R$ 会改变如何填回余量，
但两种回推都准确恢复逻辑代数。
因此“恢复同一份逻辑内容”比“整个反向规则相同”弱，二者不能混用。

**白话。**同一条通道先划出它原本能够保住的内容。参照再问：这些内容在按我的权重重新比较时，是否还留在这块范围内？留下来的就是模相容核。改一份已经保住的逻辑记录，或改不同逻辑块出现的比例，可以仍用同一个回推；改被省去部分的条件状态，就会改整套补全办法，哪怕逻辑读数仍然一样。

### 3.4 无限模参数可以由有限线性步骤消去

令

$$
\delta_\sigma(X)=i[\log\sigma,X],\qquad
 \alpha_t^\sigma=e^{t\delta_\sigma}.
$$

模核并不要求实际扫描全部实参数。下面两种算法均只使用有限矩阵数据。

### 定理 3.6（模核的有限判定）

<a id="thm-c123-finite-modular-algorithm"></a>

令 $d=\dim H$。首先有有限交换子证书

<a id="eq-c123-noise-derivative-certificate"></a>

$$
\mathfrak F_\sigma
 =\left\{\delta_\sigma^k(E_i^*E_j):
       i,j,\ 0\le k\le d^2-1\right\}'.
\tag{27}
$$

也可从内禀代数执行下降迭代

<a id="eq-c123-finite-descent"></a>

$$
V_0=\mathfrak A_{\mathcal N},\qquad
 V_{k+1}=\{X\in V_k:\delta_\sigma(X)\in V_k\}.
\tag{28}
$$

每个 $V_k$ 均为含幺 $*$-子代数；一旦 $V_{k+1}=V_k$，就有
$V_k=\mathfrak F_\sigma$。至多发生
$\dim_\mathbb C\mathfrak A_{\mathcal N}-1$ 次严格维数下降。

**证明。**
由模核公式与酉共轭保持交换子，

$$
\mathfrak F_\sigma
 =\{\alpha_t^\sigma(E_i^*E_j):i,j,t\in\mathbb R\}'.
$$

若某个 $A$ 与每条轨道交换，则对 $t=0$ 逐次求导，得到它与所有
$\delta_\sigma^k(E_i^*E_j)$ 交换。
反过来，$\delta_\sigma$ 作用在 $d^2$ 维复算子空间上；
Cayley–Hamilton 定理将其所有高次幂化为前 $d^2$ 次的线性组合。
因此与式~[(27)](#eq-c123-noise-derivative-certificate) 中的有限集合交换，就与指数轨道交换，证明该式。

对下降算法，$\delta_\sigma$ 是保持伴随的导子：

$$
\delta_\sigma(XY)=\delta_\sigma(X)Y+X\delta_\sigma(Y),\quad
 \delta_\sigma(X^*)=\delta_\sigma(X)^*,\quad
 \delta_\sigma(I)=0.
$$

所以若 $V_k$ 为含幺 $*$-代数，满足下一步条件的元素也对乘法与伴随封闭。
归纳还给
$V_k=\{X:\delta_\sigma^j(X)\in\mathfrak A_{\mathcal N},\ 0\le j\le k\}$，
故 $\mathfrak F_\sigma\subseteq V_k$。
若相邻两步相等，则 $\delta_\sigma(V_k)\subseteq V_k$，其指数保持 $V_k$。
该代数位于 $\mathfrak A_{\mathcal N}$ 内且模不变，最大性遂给反向包含。
最后 $I$ 始终保留，每次严格包含至少降一维，故得到次数界。

实际计算每一步只需选取 $V_k$ 的矩阵基，求
$(I-\Pi_k)\delta_\sigma(X)=0$ 在 $V_k$ 内的线性解空间；
$\Pi_k$ 是 Hilbert–Schmidt 正交投影。
这里只认证*所声明有限矩阵模型*的精确代数。
有限数据不能把极小但非零的交换子自动替换成零；相应的统计与扰动边界另章处理。
算法也不要求模作用作为一条实际量子门已被供应。

### 3.5 若不限制参照更换，为什么局部内容会退化

### 命题 3.7（全部忠实参照共同保护的内容）

<a id="prop-c123-all-reference-intersection"></a>

若数学上允许 $\sigma$ 遍历全部忠实状态，则

<a id="eq-c123-unrestricted-reference-intersection"></a>

$$
\bigcap_{\sigma>0,\,\operatorname{Tr}\sigma=1}\mathfrak F_\sigma
 =\begin{cases}
   \mathcal B(H),&\mathfrak A_{\mathcal N}=\mathcal B(H),\\
   \mathbb C I,&\mathfrak A_{\mathcal N}\ne\mathcal B(H).
  \end{cases}
\tag{29}
$$

**证明。**
每个酉矩阵可写成 $U=e^{iD}$，$D=D^*$；取
$\sigma=e^D/\operatorname{Tr} e^D$，则 $\operatorname{Ad}_{\sigma^i}=\operatorname{Ad}_U$。
因此左侧等于 $\bigcap_U U\mathfrak A_{\mathcal N}U^*$。
这是在所有酉共轭下不变的含幺子代数 $\mathcal C$。
若 $\mathcal C$ 含非标量自伴元素，先将其对角化，再交换两个不同本征值；
两者相减给非零倍数的 $E_{ii}-E_{jj}$。
置换共轭与单位矩阵进一步给各 $E_{ii}$；任意酉共轭遂给所有秩一投影，
其复线性包是整个 $\mathcal B(H)$。
所以 $\mathcal C$ 只能为标量或全矩阵代数，而后者仅可能在
$\mathfrak A_{\mathcal N}=\mathcal B(H)$ 时发生。

这里的全称量词是数学比较，不声称一个有限观察者实际能准备全部忠实态。
命题的作用是排除过强的“所有起点都等价”：对一个真正有损的过程，它会把共同保护内容压到标量。
本轮候选采用的范围恰是可完整回接的内部参照类；在类内允许变化，在类间明确记录余量或回推规则的改变。

**白话。**若硬要求所有可能的起点都用同一套保护规则，通常最后只剩“单位”这一个谁都不会弄错的读数。真正有内容的内生性，是允许起点改变，同时由系统自己的可恢复关系划定哪些改变只是重新描述、哪些改变已经换了补全方式。二元分支关系给出可保留范围，参照与这些关系反复组合，有限几步就能找出闭合的那一块。

<a id="section-4"></a>

## 4. 一个读口、一份参照，以及它们生成的三维几何

<a id="sec-c123-three-dimensional-geometry"></a>

本章把同一个参照等价候选画成最小可计算的图像。简记前文的过程为
$N=\mathcal N$、Petz 反向为 $R_\sigma=\mathcal R_\sigma$，回接为 $T_\sigma=R_\sigma N$，并记

$$
\mathcal C_\sigma
 =\{\rho>0:\operatorname{Tr}\rho=1,\ R_\rho=R_\sigma\},\qquad
 \mathfrak F_\sigma=\operatorname{Fix}T_\sigma^*.
$$

这里比较的是*整个反向通道*是否相同。两份参照都能被某一个二元读数接受，远不足以推出它们属于同一类。

### 4.1 模流在 qubit 上就是绕参照轴旋转

令 $X,Y,Z$ 为 Pauli 矩阵，$\boldsymbol s=(X,Y,Z)$。忠实 qubit 参照写成

$$
\sigma=\frac{I+\boldsymbol r\cdot\boldsymbol s}{2},\qquad
 r=|\boldsymbol r|<1.
$$

当 $r>0$ 时，置 $\boldsymbol n=\boldsymbol r/r$。直接对两个本征值取对数，得到

$$
\log\sigma=\frac12\log\frac{1-r^2}{4}\,I
       +b\boldsymbol n\cdot\boldsymbol s,
 \qquad b=\operatorname{arctanh}r.
$$

因此模生成元 $L_\sigma(A)=i[\log\sigma,A]$ 满足

<a id="eq-c123-bloch-modular-generator"></a>

$$
L_\sigma(\boldsymbol a\cdot\boldsymbol s)
 =-2b(\boldsymbol n\times\boldsymbol a)\cdot\boldsymbol s.
\tag{30}
$$

证明只用
$(\boldsymbol u\cdot\boldsymbol s)(\boldsymbol v\cdot\boldsymbol s)
=(\boldsymbol u\cdot\boldsymbol v)I+
i(\boldsymbol u\times\boldsymbol v)\cdot\boldsymbol s$。
于是 $\operatorname{Ad}_{\sigma^{it}}$ 对 Bloch 向量作绕 $\boldsymbol n$、角度 $-2bt$ 的旋转；$r=0$ 时模流恒等。
这个三维空间是 qubit 的无迹 Hermitian 算子空间，尚未被识别为空间中的三个位置方向。

### 命题 4.1（一个 $Z$ 读口的完整判别）

<a id="prop-c123-z-modular-core"></a>

取完全退相位读口

$$
N=\Delta_Z,\qquad
 \Delta_Z(A)=P_0AP_0+P_1AP_1,\quad P_i=\lvert i\rangle\langle i\rvert.
$$

它的双元噪声积生成对角代数，因而
$\mathfrak A_N=\operatorname{span}\{I,Z\}$。其模相容核为

$$
\mathfrak F_\sigma=
 \begin{cases}
   \operatorname{span}\{I,Z\},&[\sigma,Z]=0,\\
   \mathbb C I,&[\sigma,Z]\ne0.
 \end{cases}
$$

**证明。**
若 $[\sigma,Z]=0$，整个对角代数在模流下逐点不变。否则
$\boldsymbol n\times\boldsymbol e_z\ne0$。任何
$A=\alpha I+\beta Z$ 若属于模相容核，模流的零点导数也必须留在
$\operatorname{span}\{I,Z\}$。由式~[(30)](#eq-c123-bloch-modular-generator)，
$L_\sigma(A)$ 的无迹部分沿垂直于 $\boldsymbol e_z$ 的方向；故只能
$\beta=0$。这已在有限降链算法的第一步给出 $\mathbb C I$，无需扫描全部模参数。

若参照轴不平行于读口轴，定义

$$
\boldsymbol u=\boldsymbol n-(\boldsymbol n\cdot\boldsymbol e_z)\boldsymbol e_z,
 \qquad \boldsymbol v=\boldsymbol e_z\times\boldsymbol n.
$$

三向量 $\boldsymbol e_z,\boldsymbol u,\boldsymbol v$ 彼此正交，Gram 矩阵为
$\operatorname{diag}(1,|\boldsymbol u|^2,|\boldsymbol u|^2)$。模生成元首先产生
$L_\sigma(Z)=2b\boldsymbol v\cdot\boldsymbol s$，再由

$$
[Z,\boldsymbol v\cdot\boldsymbol s]
       =-2i\boldsymbol u\cdot\boldsymbol s
$$

得到第三个方向。故噪声积及其模旋转生成的含幺 $*$ 代数成为整个 $M_2$，
它的交换子只剩标量。
这正是一个有限的“关系再与关系组合”：二元 Kraus 噪声积确定读口代数，
第三份已供应的参照用 $[\log\sigma,\,\cdot\,]$ 检查它能否保持闭合。
这里利用了已继承的 Pauli 乘法；这个计算本身没有从无结构关系中再次证明复数域或三维物理空间。

### 4.2 参照等价类：整条轴是一类，轴外每点各是一类

### 命题 4.2（退相位读口的参照类）

<a id="prop-c123-z-reference-classes"></a>

在忠实 qubit 态的开 Bloch 球内，$N=\Delta_Z$ 的参照等价类恰为：

1. 开 $Z$ 轴上的全部对角态构成同一类；其共同反向为 $\Delta_Z$。

2. 每个轴外态单独构成一个类。

**证明。**
写 $\sigma_{ii}=\langle i\rvert\sigma\lvert i\rangle>0$。由 Petz 公式，

$$
R_\sigma(A)=\sum_{i=0}^1\langle i\rvert A\lvert i\rangle\,Q_i^\sigma,
 \qquad
 Q_i^\sigma=
 \frac{\sigma^{1/2}P_i\sigma^{1/2}}{\sigma_{ii}}.
$$

$Q_i^\sigma$ 是秩一密度矩阵，且它对应的单位列向量
$\sigma^{1/2}\lvert i\rangle/\sqrt{\sigma_{ii}}$ 的第 $i$ 个分量严格为正。
若 $R_\rho=R_\sigma$，两个 $Q_i$ 分别相同；上述正分量同时固定了每列的相位，所以

$$
\rho^{1/2}=\sigma^{1/2}\operatorname{diag}(d_0,d_1),\qquad d_0,d_1>0.
$$

当 $\sigma$ 非对角时，$\sigma^{1/2}$ 的非对角元也非零。
右端必须 Hermitian，迫使 $d_0=d_1$；再由归一化得到 $d_0=d_1=1$，即
$\rho=\sigma$。当 $\sigma$ 对角时，同式迫使 $\rho$ 对角；反之所有对角忠实态都给
$Q_i=P_i$，故反向都等于 $\Delta_Z$。

<a id="fig-c123-reference-classes"></a>

```latex
\begin{tikzpicture}[>=Latex,font=\small,scale=0.95]
  \begin{scope}
    \fill[teal!3] (0,0) circle (1.48);
    \draw[gray!60] (0,0) circle (1.48);
    \draw[->,gray!70] (-1.7,0)--(1.8,0) node[right] {$x$};
    \draw[->,gray!70] (0,-1.68)--(0,1.78) node[above] {$z$};
    \draw[teal!75!black,line width=2pt] (0,-1.43)--(0,1.43);
    \fill[white] (0,-1.48) circle(0.045);
    \draw[teal!75!black] (0,-1.48) circle(0.045);
    \fill[white] (0,1.48) circle(0.045);
    \draw[teal!75!black] (0,1.48) circle(0.045);
    \fill[orange!85!black] (0.75,0.6) circle(0.055);
    \fill[orange!85!black] (-0.7,-0.6) circle(0.055);
    \node[anchor=west,align=left,text=orange!70!black] at (0.88,0.64) {轴外：\!单点类};
    \node[anchor=east,text=teal!75!black] at (-0.10,0.85) {同一类};
    \node at (0,-2.02) {$\mathcal C_\sigma$ 的 $xz$ 截面};
  \end{scope}
  \begin{scope}[shift={(5.1,-0.7)}]
    \draw[->,very thick,teal!75!black] (0,0)--(0,2.25)
       node[above] {$\boldsymbol e_z$};
    \draw[->,thick] (0,0)--(1.75,0) node[right] {$\boldsymbol u$};
    \draw[->,thick] (0,0)--(-0.95,-0.75) node[above left] {$\boldsymbol v$};
    \draw[->,very thick,orange!85!black] (0,0)--(1.35,1.55)
       node[above right] {$\boldsymbol n$};
    \draw[dashed,gray] (1.35,1.55)--(1.35,0);
    \draw[dashed,gray] (1.35,1.55)--(0,1.55);
    \node[align=center] at (0.35,-1.32) {参照横向分量非零时，\\三个算子方向闭合成 $M_2$};
  \end{scope}
\end{tikzpicture}
```

**图 1。**左图只画开 Bloch 球的一个截面；两端纯态不在忠实参照域内。
右图是三个正交算子方向的平面投影，箭头长度作示意。

这个分类的精确性也带来一个边界：
$\sigma_r=(I+rX)/2$ 在每个 $r\ne0$ 时都属于单点类，但 $r\to0$ 时其反向通道连续趋近
$R_{I/2}$。有限误差定理~[5.6](#thm-c123-finite-horizon)给出确切距离和有限次回接公式。
不能把精确核的维数跳变，解释成有限精度观察者已经读到了一个有限大小的不连续效应。
另外，模参数 $t$ 用来表达参照所定义的代数一致性；本章没有将它指定为实验室时间，
也没有从 $\log\sigma$ 推出系统的物理 Hamiltonian。

**白话。**同一个二元读口，像一根只能分上下的轴。参照只改变这根轴上两端的权重时，反向接法没有变；参照若含有横向关系，就会把这根轴转出原来的读口。把转出的方向和原轴继续相乘，第三个方向也出现了。这里读到的是“这份参照和这个读口是否合得起来”，不是凭一个旁观者宣布所有参照都等价。

### 4.3 有限换架怎样实际供应一份无偏参照

选取参照属于同一候选的*供给条件*。假设观察者已经拥有有限组实际幺正换架，
其共轭通道组成有限群 $G$。定义有限平均

$$
\mathcal E_G(A)=\frac1{|G|}\sum_{g\in G}U_gAU_g^*.
$$

允许 $U_gU_h$ 与 $U_{gh}$ 相差全局相位，因为此处实际组合的是共轭通道。

### 命题 4.3（有限换架平均）

<a id="prop-c123-finite-twirl"></a>

$\mathcal E_G$ 是到交换子代数 $\{U_g:g\in G\}'$ 的迹保持条件期望。
若这个交换子代数仅为 $\mathbb C I$，则

$$
\mathcal E_G(A)=\operatorname{Tr}(A)I/d,
$$

且 $I/d$ 是唯一同时保持全部已供应换架的密度矩阵。

**证明。**
有限平均显然完全正、保迹、含幺。用左乘群元重排求和，输出与全部 $U_g$ 对易；
反之与全部 $U_g$ 对易的算子在平均下不变，故平均幂等且范围就是该交换子代数。
若 $B,C$ 属于此代数，则
$\mathcal E_G(BAC)=B\mathcal E_G(A)C$，给出条件期望性质。
范围为 $\mathbb C I$ 时，由保迹性确定输出只能是 $\operatorname{Tr}(A)I/d$。

把这份参照代入本轮主定理，模流变为恒等，因而

$$
\mathfrak F_{\pi_d}=\mathfrak A_N,\qquad
 \mathcal C_{\pi_d}=\{\rho\in\mathfrak A_N:\rho>0,\ \operatorname{Tr}\rho=1\}.
$$

这给出有限换架与参照等价候选的准确接点：无偏参照保留整个已供应噪声可恢复代数，
但那个代数本身可能只是标量或一个真子代数。

qubit 只需四个共轭操作 $I,X,Z,XZ$：$Z$ 不变性先消去 $x,y$，
$X$ 不变性再消去 $z$。更一般地，已供应的位移门
$U\lvert j\rangle=\lvert j+1\pmod d\rangle$ 与相位门
$V\lvert j\rangle=e^{2\pi ij/d}\lvert j\rangle$，通过 $d^2$ 个 $U^aV^b$ 给出同一有限构造：
先平均相位消去非对角元，再平均位移等化对角元。
均匀权重也有有限内部表述：若一个有限标签分布在群的左平移下不变，
则任意两个标签的概率相等。但*标签寄存器、均匀混合和条件控制仍须实际供应*；
一个平均公式不会自动制造这些操作，也没有使用外部 Haar 积分。

保留标签还可以精确说明原信息去了哪里。定义

$$
\mathcal J(\rho)=\frac1{|G|}\sum_g\lvert g\rangle\langle g\rvert\otimes U_g\rho U_g^*,
 \qquad
 \mathcal D(A)=\sum_gU_g^*\langle g\rvert A\lvert g\rangle U_g.
$$

直接代入得 $\mathcal D\mathcal J=\operatorname{id}$。不可约情形下，系统边缘恒为 $I/d$，
标签边缘恒为均匀分布，输入内容仍保存在二者的联合关系中。
这是已知的有限随机幺正加密机制 [7](#ref-amtw2000)，在这里用来解释内部参照供给：
“任何输入都给出同一个局部参照”可以成立；不能据此把整个可逆结构说成已经抹掉任意输入。

### 4.4 隐藏重数与中心权重不能被换架中性掩盖

若实际门只作用成 $U_g\otimes I_m$，即使它们在第一个因子上不可约，
所有 $(I_d/d)\otimes\omega$ 都保持这些门。观察者看见的换架完备性因此必须相对于已声明的代数；
它不能证明尚未被读口触及的重数因子也已无偏。

更一般地，设有限可观测代数为
$\mathcal A=\bigoplus_\alpha M_{n_\alpha}$。

### 命题 4.4（中性只固定块内，中心仍有自由度）

<a id="prop-c123-center-weights"></a>

在 $\mathcal A$ 的全部内部幺正共轭下不变的态，恰为

$$
\omega(A)=\sum_\alpha q_\alpha
      \frac{\operatorname{Tr} A_\alpha}{n_\alpha},\qquad
 q_\alpha\ge0,\quad\sum_\alpha q_\alpha=1.
$$

即使再要求选择同构协变、并在张量复合下相乘，仍不能唯一确定 $q_\alpha$。

**证明。**
在每个块内，对角相位共轭使态密度的非对角元为零，置换共轭使其对角元相等。
块的单位是中心投影，其期望值就是 $q_\alpha$；内部共轭不改变这些投影，故不能固定这些权重。
反过来，上式显然满足不变性。
对第二句，任取一个实数 $p$，令

$$
q_\alpha^{(p)}=\frac{n_\alpha^p}{\sum_\gamma n_\gamma^p}.
$$

这个选择不随同构改变，而对另一个代数的块维数 $m_\beta$ 有

$$
\frac{(n_\alpha m_\beta)^p}
 {\sum_{\gamma,\delta}(n_\gamma m_\delta)^p}
 =q_\alpha^{(p)}q_\beta^{(p)}.
$$

不同 $p$ 在含不同大小矩阵块时给出不同答案，证明非唯一性。

若代数实际嵌入为
$\bigoplus_\alpha(M_{n_\alpha}\otimes I_{m_\alpha})\subset M_D$，
环境 $I_D/D$ 限制给它的权重是
$q_\alpha=n_\alpha m_\alpha/D$。这份权重来自具体包含关系，不能冒充抽象代数自身已经决定的数据。
同样，有限换架选出的 $\pi$ 是否与已有参照 $\sigma$ 属于同一个
$\mathcal C_\sigma$，仍须由模相容核检验；qubit 轴外参照已经给出失败实例。

### 4.5 沿过程运输参照，不能在每个节点重新归零

下面用一个完全经典的二元过程反推这个条件为何不可删除。
采用列随机矩阵，输入概率列向量左乘 $N$。设

$$
N=\begin{pmatrix}1&1/2\\0&1/2\end{pmatrix},\qquad
 \pi=\binom{1/2}{1/2},\qquad \tau=N\pi=\binom{3/4}{1/4}.
$$

对于先验 $s$，经典 Petz 反向就是 Bayes 反向

$$
(R_{s,N})_{ij}=\frac{s_iN_{ji}}{(Ns)_j}.
$$

从同一源参照 $\pi$ 计算，得到

$$
R_{\pi,N}=\begin{pmatrix}2/3&0\\1/3&1\end{pmatrix},\qquad
 R_{\pi,N^2}=\begin{pmatrix}4/7&0\\3/7&1\end{pmatrix}.
$$

若中间节点擅自把已到达的 $\tau$ 重置为它自己的 $\pi$，逐段反向就变成

$$
R_{\pi,N}^2=\begin{pmatrix}4/9&0\\5/9&1\end{pmatrix}
       \ne R_{\pi,N^2}.
$$

真正继承中间参照则给出

$$
R_{\tau,N}=\begin{pmatrix}6/7&0\\1/7&1\end{pmatrix},\qquad
 R_{\pi,N}R_{\tau,N}=R_{\pi,N^2}.
$$

因此“每个节点都局部无偏”与“同一个过程拥有相容的反向”不是同一约束。
在声明的源窗口可以用有限换架供应 $\sigma$；沿箭头随后必须运输为 $N\sigma$。
若要中途改用新参照，应明确检验相应反向是否同类，或把改参照本身作为额外过程。

### 4.6 跨包含与无限极限的两个边界

### 命题 4.5（不存在对所有包含都自然的中性选择）

<a id="prop-c123-no-universal-neutral-section"></a>

不存在给每个有限含幺 $C^*$ 代数选择一个态的规则，既在每个 $M_d$ 上选择
归一化迹，又与*全部*含幺 $*$ 嵌入的限制相容。

**证明。**
考虑同一对代数 $\mathbb C^2$ 与 $M_3$ 的两个嵌入

$$
\iota(z,w)=\operatorname{diag}(z,w,w),\qquad
 \jmath(z,w)=\operatorname{diag}(z,z,w).
$$

$M_3$ 的归一化迹沿两条包含限制，分别要求 $\mathbb C^2$ 的同一个态具有权重
$(1/3,2/3)$ 与 $(2/3,1/3)$，矛盾。

所以无上帝视角的做法是保留实际提供的包含及其权重。
在较窄但有用的情形中，兼容性确实成立：含幺嵌入
$M_d\hookrightarrow M_{dk}$ 等价于 $A\mapsto U(A\otimes I_k)U^*$，
因为一组矩阵单位的对角投影具有相同秩。归一化迹显然沿这种嵌入相容。
这个受限结论不能替代对任意子代数的结论。

无限维也必须说明具体代数。
在可数无限维 $B(\ell^2)$ 中，不仅没有归一化的 $I/d$ 密度矩阵，甚至不存在任何归一化迹态。
取将标准基分别送入偶数与奇数位置的两个等距算子 $S_0,S_1$，则

$$
S_i^*S_i=I,\qquad S_0S_0^*+S_1S_1^*=I.
$$

若 $\omega$ 是归一化迹态，就有

$$
1=\omega(I)=\sum_i\omega(S_iS_i^*)
   =\sum_i\omega(S_i^*S_i)=2,
$$

矛盾。这个证明没有假设该态正常，因而比“$I$ 的通常迹无穷大”更强。

另一方面，有限张量窗口
$M_2\subset M_4\subset M_8\subset\cdots$，包含为 $A\mapsto A\otimes I_2$，
具有相容的归一化迹。它们在代数并上定义一个正、归一化且有界的泛函，
因 $|\omega(A)|\le\|A\|$ 而唯一延拓到该并的范数闭包。
因此某些无限代数有中性迹态，只是不能把那个代数等同于整个 $B(\ell^2)$，
也不能把延拓误写成一张无限维归一化单位密度矩阵。
角包含 $A\mapsto A\oplus0$ 则不含幺；把限制后不足一的权重重新归一化是条件化，
不是上述相容延拓。

**白话。**观察者可以用自己真的拥有的有限换架，把一个局部窗口调到没有偏向的参照；若换架只碰到一部分结构，剩下的权重就仍须保留。参照一旦进入过程，就要随着过程一起走，不能到下一站又凭空换成均匀。两份参照能否视为同一份，不看名字，也不靠外面的共同坐标，而看它们对这个过程给出的全部反向接法是否相同。三维 qubit 图把这一点画得很直接：顺着读口轴挪动仍可同类，横着挪动通常改变反向关系；扩大窗口或走向无限时，则必须把真实的包含关系一并带上。

<a id="section-5"></a>

## 5. 内部参照的有限证书：能制备什么，能稳定认证什么

<a id="sec-c123-finite-certificates"></a>

前面的模相容核回答了给定参照后保住哪些关系。本节进一步问：能否用已经供应的二元准备和读口，实际得到一份不偏向某个源方向的参照？答案在已声明的有限来源中是肯定的；但准确代数的维数与有限误差保证必须分开。

全节 $H\cong\mathbb C^d$、$d\ge2$ 是同一个已声明来源。其*维数上界*以及所用准备确实位于 $H$，是前件，不由下面的有限数据自动产生。过程若被称为通道，仍须具有前文的完整参考相容性；本节不把近正校准误差改称准确完全正性。

### 5.1 不先指定纯态坐标，也能认证一份接近均匀的参照

### 定义 5.1（有限准备的二元证据）

原菜单已供应 $d$ 个准备，其实际状态记为
$\rho_1,\ldots,\rho_d\in\mathfrak S(H)$；不预先要求它们为纯态或正交态。
对每一对 $i<j$，供应同一个二元效果 $0\le F_{ij}\le I$，把结果 $F_{ij}$ 判为 $i$，把另一结果判为 $j$。其条件错误为

$$
e_i^{ij}=1-\operatorname{Tr}(F_{ij}\rho_i),\qquad
 e_j^{ij}=\operatorname{Tr}(F_{ij}\rho_j).
$$

同一对不能在先知道未知标签后换读口。不同对可以使用不同效果。另供应均匀选择准备标签的混合操作，产生

$$
\bar\sigma=\frac1d\sum_{i=1}^d\rho_i,
 \qquad \pi=I_H/d.
$$

这里的概率指真实模型概率，或具有明示置信保证的区间界。

### 引理 5.2（二元错误约束混合态重叠）

<a id="lem-c123-binary-overlap"></a>

对任意两个态 $\rho,\omega$ 和实际效果 $F$，记
$e_\rho=1-\operatorname{Tr}(F\rho)$、$e_\omega=\operatorname{Tr}(F\omega)$，则

<a id="eq-c123-overlap-bound"></a>

$$
\operatorname{Tr}(\rho\omega)
 \le\left[\sqrt{(1-e_\rho)e_\omega}
          +\sqrt{e_\rho(1-e_\omega)}\right]^2.
\tag{31}
$$

特别地，两项错误都不超过 $\varepsilon\le1/2$ 时，右端至多为
$4\varepsilon(1-\varepsilon)$。

**证明。**
在 $\sqrt\rho\sqrt\omega$ 中插入 $F+(I-F)$。Schatten 范数的乘积不等式给出

$$
\begin{aligned}
\|\sqrt\rho\sqrt\omega\|_1
 &\le\|\sqrt\rho F^{1/2}\|_2\|F^{1/2}\sqrt\omega\|_2\\
 &\quad+\|\sqrt\rho(I-F)^{1/2}\|_2
       \|(I-F)^{1/2}\sqrt\omega\|_2,
\end{aligned}
$$

即括号内的上界。又
$\operatorname{Tr}(\rho\omega)=\|\sqrt\rho\sqrt\omega\|_2^2
\le\|\sqrt\rho\sqrt\omega\|_1^2$。
最后写 $e_\rho=\sin^2\alpha,e_\omega=\sin^2\beta$，括号等于
$\sin(\alpha+\beta)$；在两个错误均不超过 $\varepsilon\le1/2$ 时，它至多为
$2\sqrt{\varepsilon(1-\varepsilon)}$。

### 定理 5.3（有限二元准备认证均匀参照）

<a id="thm-c123-neutral-reference"></a>

若全部条件错误均不超过 $0\le\varepsilon\le1/2$，则

<a id="eq-c123-neutral-reference-error"></a>

$$
\boxed{\quad
 \|\bar\sigma-\pi\|_1
 \le\min\{2,\,2\sqrt{(d-1)\varepsilon(1-\varepsilon)}\}.
 \quad}
\tag{32}
$$

令 $\eta=2\sqrt{\varepsilon(1-\varepsilon)}$，还成立谱下界

<a id="eq-c123-reference-faithful-gap"></a>

$$
\bar\sigma\succeq\frac{1-(d-1)\eta}{d}\,I_H.
\tag{33}
$$

所以 $(d-1)\eta<1$ 时，已制备的 $\bar\sigma$ 被认证为忠实态。
若 $\varepsilon=0$，各 $\rho_i$ 必为一组完整正交纯态投影，并且
$\bar\sigma=\pi$。

**证明。**
记 $Y=\bar\sigma-I/d$。每个态满足 $\operatorname{Tr}\rho_i^2\le1$，上一引理则给
$\operatorname{Tr}(\rho_i\rho_j)\le\eta^2$。因此

$$
\begin{aligned}
\operatorname{Tr} Y^2
 &=\frac1{d^2}\left(\sum_i\operatorname{Tr}\rho_i^2
                 +\sum_{i\ne j}\operatorname{Tr}(\rho_i\rho_j)\right)-\frac1d\\
 &\le\frac{d-1}{d}\eta^2.
\end{aligned}
$$

由 $\|Y\|_1\le\sqrt d\,\|Y\|_2$，即得式
[(32)](#eq-c123-neutral-reference-error)。
又 $Y$ 为去迹 Hermitian 矩阵。对其任一特征值 $y_r$，

$$
y_r^2=\left(\sum_{s\ne r}y_s\right)^2
 \le(d-1)\sum_{s\ne r}y_s^2,
 \qquad
 |y_r|\le\sqrt{\frac{d-1}{d}\operatorname{Tr} Y^2}
 \le\frac{d-1}{d}\eta.
$$

这给出谱下界。

当错误为零时，$\operatorname{Tr}(\rho_i\rho_j)=0$。
正性意味着 $\rho_i^{1/2}\rho_j^{1/2}=0$，故 $d$ 个非零支持两两正交。
它们在 $d$ 维空间中，因而每个支持恰为一维，且直和为整个 $H$。
归一化迫使每个 $\rho_i$ 是对应秩一投影，和为 $I_H$。

更一般地，每对有自己的括号上界 $\eta_{ij}=\eta_{ji}$ 时，同一证明给出

$$
\|\bar\sigma-\pi\|_1
 \le\min\left\{2,\sqrt{\frac1d\sum_{i\ne j}\eta_{ij}^2}\right\}.
$$

这些是维数明确的充分保证；除后面的 qubit 取等号实例外，不宣称一般常数最优。
若实际混合权重为 $q_i$，则只需再加
$\sum_i|q_i-1/d|$，因为 $\|\sum_i(q_i-1/d)\rho_i\|_1$ 不超过这项。准备若在校准后漂移，也须把实际制备误差另行计入。

准确的 $\pi$ 不需要给这些正交原子指定外部方向。任意共同酉变换都保持 $I/d$；其模流为标量共轭，所以前面的主定理给出

$$
\mathfrak F_\pi=\mathfrak A_N.
$$

这里得到的是该通道*能够准确保存的完整代数*，不是说任意通道都能恢复整个 $M_d$。混合标签仍可以作为记录留在 $\Omega$ 内；本定理只描述所声明来源上的边际态，没有声称它与所有内部记录独立。

**白话。**先不猜每份准备到底朝哪个方向。只检查这 $d$ 份内容能否两两分清；如果它们确实填满一个只有 $d$ 个正交位置的来源，零错误就迫使它们正好各占一个位置。把这些已供应的准备等权混合，得到的参照不偏向任何方向。有小错误时，混合态离均匀参照还有多远，也能由二元错误直接算出来。

### 5.2 维数饱和不能由有限局部读数免费取得

### 例 5.4（隐藏的重数部门）

<a id="ex-c123-hidden-multiplicity"></a>

令真实来源是 $H'=\mathbb C^d\otimes\mathbb C^m$，$m>1$，并准备

$$
\rho_i=\lvert i\rangle\langle i\rvert\otimes\omega,
 \qquad F_{ij}=\lvert i\rangle\langle i\rvert\otimes I_m\quad(i<j).
$$

所有二元错误都为零，但均匀混合只得到

$$
\bar\sigma=\frac{I_d}{d}\otimes\omega,
 \qquad
 \left\|\bar\sigma-\frac{I_{dm}}{dm}\right\|_1
 =\left\|\omega-\frac{I_m}{m}\right\|_1.
$$

取 $\omega=(1-\zeta)\lvert 0\rangle\langle 0\rvert+\zeta I_m/m$，$0<\zeta<1$，它甚至忠实，而右端为
$2(1-\zeta)(1-1/m)$，可接近最大值。

如果全部实际控制和效果只在第一个因子上作用，那么任何有限或无限长的这类实验都无法区分不同的 $\omega$。前一因子的完美判别证书，没有认证后一因子不存在。

因此观察到 $d$ 份准确可区分内容，只给出来源容量的下界；要使用定理
[5.3](#thm-c123-neutral-reference)，还需已给定的 $d$ 维源编码、完整角代数或其他真实的维数上界证书。它可以是观察者内部已构造的一块有限逻辑来源，不必是对整个 $\Omega$ 的维数宣称。有限抽样给出的则是概率区间，不是准确的零错误陈述。

### 5.3 准确模核会跳变，有限次回接却可以连续

下面使用一个完整可算的例子，将两种稳定性分开。令

$$
N=\mathcal D_Z,\qquad
 \mathcal D_Z(X)=\lvert 0\rangle\langle 0\rvert X\lvert 0\rangle\langle 0\rvert+\lvert 1\rangle\langle 1\rvert X\lvert 1\rangle\langle 1\rvert,
 \qquad \sigma_r=\frac{I+rX}{2},\quad |r|<1.
$$

本小节的 $X,Y,Z$ 表示 Pauli 矩阵。记
$a=\sqrt{1-r^2}$，$S_r=\mathcal R_{\sigma_r}N$。

### 引理 5.5（完整参考态已足以计算 diamond 范数）

<a id="lem-c123-diamond-states"></a>

若线性映射 $\Delta$ 保持取伴随，则其 diamond 范数等于
$\sup_{R,\rho}\|(\Delta\otimes\operatorname{id}_R)(\rho)\|_1$，其中 $R$ 遍历有限参考空间，$\rho$ 遍历联合密度矩阵。

**证明。**
对定义中的任意算子输入 $A$，在参考端增加一个二元标志，取

$$
H_A=\frac12\begin{pmatrix}0&A\\mathcal A^*&0\end{pmatrix}.
$$

有 $\|H_A\|_1=\|A\|_1$；因 $\Delta$ 保持取伴随，映射后的两个迹范数也相等。将 $H_A=H_+-H_-$ 作 Jordan 分解，则 $H_\pm\ge0$ 且
$\operatorname{Tr} H_++\operatorname{Tr} H_-=\|A\|_1$。分别归一化非零的 $H_\pm$，再用三角不等式，任意参考态上的统一上界就成为全部 $A$ 上的相同范数上界。反向不等式因密度矩阵本来就是允许输入而直接成立。

### 定理 5.6（有限回接次数的精确全参考误差）

<a id="thm-c123-finite-horizon"></a>

对 $n\ge1$，$S_r^n$ 的 Bloch 作用为

$$
(x,y,z)\longmapsto(r,0,a^n z).
$$

其固定可观测量代数满足

$$
\operatorname{Fix}S_0^*=\operatorname{span}\{I,Z\},\qquad
 \operatorname{Fix}S_r^*=\mathbb C I\quad(r\ne0).
$$

然而对包含任意参考的、未除二的 diamond 距离，有精确公式

<a id="eq-c123-finite-horizon-distance"></a>

$$
\boxed{\quad
 \|S_r^n-\mathcal D_Z\|_\diamond
 =\sqrt{r^2+(1-a^n)^2}
 \le |r|+nr^2.
 \quad}
\tag{34}
$$

**证明。**
$N(\sigma_r)=I/2$，所以
$\mathcal R_{\sigma_r}(W)=2\sigma_r^{1/2}\mathcal D_Z(W)\sigma_r^{1/2}$。
写 $\sigma_r^{1/2}=uI+vX$，有
$u^2+v^2=1/2$、$2uv=r/2$、$u^2-v^2=a/2$。
于是 $\sigma_r^{1/2}Z\sigma_r^{1/2}=aZ/2$，从而一次回接把 Bloch 向量送到 $(r,0,az)$。继续迭代得到所述公式。

在可观测量侧，

$$
S_r^*(I)=I,\quad S_r^*(X)=rI,\quad
 S_r^*(Y)=0,\quad S_r^*(Z)=aZ.
$$

当 $r=0$ 时 $a=1$；当 $r\ne0$ 时 $a<1$，逐项比较系数即得两个固定代数。

为证明 diamond 等式，记 $P_\pm=(I\pm Z)/2$，以及

$$
\omega_\pm^{(n)}=\frac{I+rX\pm a^n Z}{2},\qquad
 D_\pm=\omega_\pm^{(n)}-P_\pm
       =\frac{rX\pm(a^n-1)Z}{2}.
$$

两个 $D_\pm$ 的迹范数均为
$c_n=\sqrt{r^2+(1-a^n)^2}$。任意源–参考态 $\rho_{HQ}$ 在源的 $Z$ 基中的对角块 $\rho_{++},\rho_{--}$ 为正，迹之和为 $1$；两通道均先读出同一个 $Z$ 标签，因此

$$
[(S_r^n-\mathcal D_Z)\otimes\operatorname{id}_Q](\rho_{HQ})
 =D_+\otimes\rho_{++}+D_-\otimes\rho_{--}.
$$

三角不等式给范数至多为 $c_n$。输入 $P_+$ 已达到 $c_n$，所以参考不能再把它增大，得到等式。最后
$1-a^n\le n(1-a)=nr^2/(1+a)\le nr^2$，并使用
$\sqrt{x^2+y^2}\le|x|+|y|$。

这里比较的是退相干本来保留下来的 $Z$ 对角内容；对该来源代数，$\mathcal D_Z$ 就是准确目标。没有把失去的全部相位说成已经恢复。

### 推论 5.7（任何正的二元容差都不能认证准确核维数）

<a id="cor-c123-no-exact-threshold"></a>

即使来源维数准确知道为 $2$，任意小的正二元准备误差，也不能推出所制备参照的模相容核与 $\mathfrak F_\pi$ 相同。

**证明。**
准备两个纯态

$$
\rho_\pm=\frac{I+rX\pm aZ}{2},\qquad
 a=\sqrt{1-r^2},\quad r\ne0.
$$

同一个 $Z$ 二元效果对它们的两个错误均为

$$
\varepsilon_r=\frac{1-a}{2}\longrightarrow0,
 \qquad \frac{\rho_++\rho_-}{2}=\sigma_r.
$$

但定理 [5.6](#thm-c123-finite-horizon) 已给出每个 $r\ne0$ 的准确核只是 $\mathbb C I$，而均匀参照的核为 $\operatorname{span}\{I,Z\}$。同时

$$
\|\sigma_r-\pi\|_1=|r|
 =2\sqrt{\varepsilon_r(1-\varepsilon_r)},
$$

所以定理 [5.3](#thm-c123-neutral-reference) 的 qubit 误差界在此还取得等号。

固定任意有限 $n$ 时，式 [(34)](#eq-c123-finite-horizon-distance) 随 $r\to0$ 趋零。长期极限却为

$$
\lim_{n\to\infty}S_r^n=\mathcal S_{\sigma_r}\quad(r\ne0),
 \qquad \lim_{n\to\infty}S_0^n=\mathcal D_Z.
$$

因而

$$
\lim_{r\to0}\lim_{n\to\infty}S_r^n=\mathcal S_\pi
 \ne\mathcal D_Z
 =\lim_{n\to\infty}\lim_{r\to0}S_r^n,
 \qquad \|\mathcal S_\pi-\mathcal D_Z\|_\diamond=1.
$$

非平凡方向的谱隙是 $1-a=r^2/(1+a)\sim r^2/2$；它可以很小，却在足够多次回接后累积成有限损失。本章的次数 $n$ 是操作次数，不是从这些公式另外推导出的物理时间。

**白话。**参照只偏一点，短时间内的回接也可以只偏一点；但“永远准确不变”是更苛刻的问题。这个例子里，任意小的横向偏置都会让原来稳定的对角关系慢慢衰减。有限次操作仍有明确的小误差界，反复无限多次却会把那份区别磨掉。因此准确代数有几维，不能只凭一个很小的实验误差就宣布。

### 5.4 自洽校准也有无法由相同数据区分的自由度

门集层析同时估计准备、测量与门，避免把其中一项先当成完美设备；它也明确保留相同概率描述之间的 gauge 自由度 [8](#ref-gst2021)。在线性坐标中，若序列概率为

$$
p(w)=\langle E,G_{w_n}\cdots G_{w_1}\rho\rangle,
$$

则任何可逆线性 $B$ 所给的变换

$$
\rho\mapsto B\rho,\quad E\mapsto(B^{-1})^*E,
 \quad G_j\mapsto BG_jB^{-1}
$$

保持全部序列概率。并非每个 $B$ 都保住物理性；但下面的反例在两套描述中都使用合法状态、效果与相同的酉门。

### 例 5.8（准备纯度与读口对比度之间的精确歧义）

<a id="ex-c123-contrast-gauge"></a>

对 qubit 取 $0<r,s<1$，供应状态
$\rho_r=(I+rZ)/2$、效果 $F_s=(I+sZ)/2$，以及任意一组酉控制，甚至全部酉控制。若 $t>0$ 满足 $tr\le1$、$s/t\le1$，则将准备和效果换成

$$
\rho_{tr}=\frac{I+trZ}{2},\qquad F_{s/t}=\frac{I+(s/t)Z}{2}
$$

会保持所有任意长酉门序列的读数，而状态纯度通常改变。

**证明。**
任意序列合成某个酉 $U$。设其 Bloch 旋转为 $O_U$，则

$$
\operatorname{Tr}(F_sU\rho_rU^*)
 =\frac{1+rs\,e_z^{\mathsf T}O_Ue_z}{2}.
$$

变换后乘积 $(tr)(s/t)$ 不变，所以所有概率相同。
状态纯度分别为 $(1+r^2)/2$ 和 $(1+t^2r^2)/2$；两套描述均物理，却不能靠这些数据选出其中一套。

这种歧义不是单纯共同酉坐标变换，因为共同酉不会改变纯度。另一方面，它与零误差维数饱和定理不矛盾：那里的准确判别已把支持和纯度同时锁住。增加任意多次同类读数，不等于增加一种能打破歧义的新关系。

### 5.5 三态闭环能补什么：相位关系而非外部绝对方向

两两转移概率也不足以保留所有复相位关系。定义三态的 Bargmann 闭环量

$$
B_{123}=\operatorname{Tr}(\rho_1\rho_2\rho_3).
$$

对 qubit $\rho_j=(I+n_j\cdot\boldsymbol\sigma)/2$，直接使用 Pauli 乘法得到

<a id="eq-c123-bargmann-triple"></a>

$$
B_{123}=\frac14\left[1+n_1\cdot n_2+n_2\cdot n_3+n_3\cdot n_1
                +i\,n_1\cdot(n_2\times n_3)\right].
\tag{35}
$$

例如 $+X,+Y,+Z$ 三个纯态与其共同复共轭，所有二元转移概率都为 $1/2$，三态闭环量却分别为 $(1+i)/4$ 和 $(1-i)/4$。

若实际供应三份独立准备、受控循环置换以及同一辅助 qubit 的 $X,Y$ 读口，这个额外关系可以被读出。取
$C\lvert a,b,c\rangle=\lvert b,c,a\rangle$，则展开基指标给出

$$
\operatorname{Tr}\bigl[C(\rho_1\otimes\rho_2\otimes\rho_3)\bigr]=B_{123}.
$$

把控制位准备为 $\lvert +\rangle$，按控制值 $1$ 运行 $C$，其约化矩阵为
$\frac12\left(\begin{smallmatrix}1&B_{123}^*\\B_{123}&1\end{smallmatrix}\right)$。
所以辅助位的 $X,Y$ 期望分别为 $\operatorname{Re} B_{123},\operatorname{Im} B_{123}$。这类循环测试及关系不变量已有系统研究 [9](#ref-relational2021)。

读出虚部需要实际的共同相位控制；它不是从匿名的二元概率自动出现。若把所有准备、门和读口一并复共轭，整体描述仍可给相同概率。因此三态实验补充的是相对于已供应读口的闭环关系，不是宇宙的绝对方向；它也不消除前面例子的隐藏重数部门。

**白话。**没有上帝视角，并不意味着什么关系都不能确认。观察者可以先声明一块确实掌握的有限来源，用实际二元比较制备并检验其中的参照；也可以加入真正供应的三态闭环，读出原先两两概率没有包含的相位。每增加一种结论，都要指出是哪条新关系让它变得可识别。准确模核描述永远保住的内容，有限证书描述在给定次数和误差下能保住多少；把这两件事接起来，才得到可执行、可检验的内部参照。

<a id="section-6"></a>

## 6. 三份参照、多个观察者与内生关系的边界

<a id="sec-c123-observers"></a>

### 6.1 同类参照的三元接续

主定理把参照等价类写成

$$
H=\bigoplus_\alpha H^L_\alpha\otimes H^R_\alpha,
 \qquad \rho=\bigoplus_\alpha R_\alpha\otimes\omega_\alpha.
$$

$R_\alpha>0$，$\sum_\alpha\operatorname{Tr} R_\alpha=1$，而所有 $\omega_\alpha$ 固定、满秩且迹为一。
因此等价类是一个有限维凸状态族的相对内部，实维数为

<a id="eq-c123-class-dimension"></a>

$$
\dim_{\mathbb R}[\sigma]_{\mathcal N}
 =\sum_\alpha(\dim H^L_\alpha)^2-1.
\tag{36}
$$

这里的闭包可以包含非满秩态；把闭包中的态重新用作全支持参照时，必须重新处理支持，不能自动延用满秩等价定理。

### 命题 6.1（同类参照的有限接缝）

对同一等价类中的满秩 $\sigma,\rho,\eta$，定义

$$
C_{\rho,\sigma}=\rho^{1/2}\sigma^{-1/2}.
$$

这些可逆元属于共同的固定代数 $\mathfrak F$，满足

$$
\begin{aligned}
\rho&=C_{\rho,\sigma}\sigma C_{\rho,\sigma}^*,
\end{aligned}
\tag{37}
$$

<a id="eq-c123-reference-cocycle"></a>

$$
\begin{aligned}
C_{\eta,\rho}C_{\rho,\sigma}&=C_{\eta,\sigma},
 & C_{\sigma,\rho}&=C_{\rho,\sigma}^{-1}.
\end{aligned}
\tag{38}
$$

令 $\beta=\mathcal R^*|_{\mathfrak F}$ 为输出端的保星表示，
$\tau_\sigma=\mathcal N(\sigma)$。则

$$
\tau_\rho^{1/2}\tau_\sigma^{-1/2}
 =\beta(C_{\rho,\sigma}),
$$

故输出接缝也满足同一个三元复合式。

**证明。**
在上述分块中，$\sigma=\bigoplus S_\alpha\otimes\omega_\alpha$，
故 $C_{\rho,\sigma}=\bigoplus R_\alpha^{1/2}S_\alpha^{-1/2}\otimes I$，
属于 $\mathfrak F$。夹乘及三元式由相邻的正平方根与逆相消直接得到。
参照等价定理证明中的 Kraus 交织给
$\mathcal N(\rho)^{1/2}=\beta(C_{\rho,\sigma})\mathcal N(\sigma)^{1/2}$，
右乘逆平方根即得输出式。$\beta$ 保乘法，所以保留三元接续。

式 [(38)](#eq-c123-reference-cocycle) 的形式对于任意满秩矩阵都可写出；本定理的实质是这些接缝*属于同一个可恢复代数，并被同一过程保乘法地运输*。这一额外事实不能由一个形式上的三角相消代替。
一般 $C_{\rho,\sigma}$ 不是酉矩阵，也未必是收缩。它是参照变化的关系坐标，不是已经免费供应的确定性量子门。要物理执行相应滤片，必须缩放成合法成功分支，并核对实际可用性与成功权重。

**白话。**三份参照如果都只改变同一片可恢复内容，从第一份换到第二份、再换到第三份，与直接换过去给出同一条接缝。这个三角能闭合，是因为三次变化没有改动同一份未读条件结构。写出一个能相消的公式还不够；公式中的变化必须实际落在同一片可恢复关系里。

### 6.2 观察者共同内容的条件化定义

设 $\mathcal N_A,\mathcal N_B,\mathcal N_C$ 是同一已声明源部门的三个读出。
各自使用源参照 $\sigma$ 的实际运输
$\tau_A=\mathcal N_A(\sigma)$ 等，并按前文定义 $\mathcal R_A$ 等。
定义观察者之间的预测接口

$$
\mathcal T_{BA}=\mathcal N_B\mathcal R_A.
$$

它将 A 的记录通过同一参照解释为源内容，再给出 B 的预测。

### 命题 6.2（共同可恢复状态上的三角接续）

若 $\rho$ 属于 A、B 都能准确回接的同一状态族，即
$\mathcal R_A\mathcal N_A(\rho)=\rho$ 且
$\mathcal R_B\mathcal N_B(\rho)=\rho$，则

$$
\mathcal T_{CB}\mathcal T_{BA}\mathcal N_A(\rho)
 =\mathcal T_{CA}\mathcal N_A(\rho)=\mathcal N_C(\rho).
$$

若在完整声明源部门上有
$\|\mathcal R_B\mathcal N_B-\operatorname{id}\|_\diamond\le e_B$，则

$$
\|\mathcal T_{CB}\mathcal T_{BA}-\mathcal T_{CA}\|_\diamond\le e_B.
$$

**证明。**
精确式把两个回接依次替换成 $\rho$ 即得。
近似式的差为
$\mathcal N_C(\mathcal R_B\mathcal N_B-\operatorname{id})\mathcal R_A$；
通道的 diamond 范数为一，次乘性给出结论。该误差前件覆盖整个声明源部门，不能仅以单个参照被返回代替。

这是一条条件的共同来源定理。它没有赋予任何单个观察者对全 $\Omega$ 的访问。要在内部使用它，所需来源接口、支持和回接关系必须被该观察者已有的证据覆盖。

### 命题 6.3（没有上帝模式时的可知性判准）

令 $\mathcal M$ 为与内部规则相容的可能模型集合，$r_A(m)$ 为观察者 A 在模型 $m$ 的全部现有记录。某个关于交集的命题 $q(m)$ 可由现有记录唯一确定，当且仅当

$$
r_A(m)=r_A(m')\ \Longrightarrow\ q(m)=q(m')
 \qquad(m,m'\in\mathcal M).
$$

**证明。**
若 $q=f\circ r_A$，同一记录自然给同一值。
反之，在每个已出现的记录上取任意相容模型定义 $f$；条件保证选哪一个都一样，所以 $q=f\circ r_A$。

这里说的是记录的逻辑确定性。这个集合意义的 $f$ 未必可计算；有限时间内能否识别，还需要实际算法和资源条件。

因此，完整包含另一个观察者的结构是某些任务的充分证据，但不是知道*任何有限共同关系*的必要条件。例如两边都保存一份同源校验位，并有内部来源凭证，已足以确认这一个共同位，无须包含对方的全部状态。反过来，两个全局模型可以给 A 完全相同的记录，却给不同的完整交集；此时 A 确实无法判定那个完整交集。

### 6.3 从有限窗口到同一全局状态：需要什么条件

### 命题 6.4（兼容局部评价的延拓）

设含幺 $C^*$-代数形成嵌套链
$\mathcal A_1\subseteq\mathcal A_2\subseteq\cdots$，
且归一化正泛函满足 $\omega_{n+1}|_{\mathcal A_n}=\omega_n$。
则它们唯一确定 $\overline{\bigcup_n\mathcal A_n}$ 上的一个状态。

**证明。**
在代数并上定义 $\omega(a)=\omega_n(a)$，兼容性保证良定义。
正性和单位归一化给 $|\omega(a)|\le\|a\|$，
所以它唯一连续延拓到范数闭包。对正元可用平方根的稠密近似，或正锥的范数闭性，得到延拓仍正，且单位值仍为一。

只有当这些窗口的并在目标全局代数中稠密时，才确定该目标上的状态。若观察者只覆盖一个真子代数，其他部分仍可能有多个延拓。不同门词若要“逼近同一个 $\omega$”，至少需要明确的兼容性与覆盖性；仅仅让两条序列都不断增长并不强制它们收敛到同一个状态。

### 6.4 自指准备、未读关系与场的范围

把任意输入都送成同一个观察者原子态是合法的*局部准备通道*，但不可能是整个封闭系统上的酉门。若一个完整等距实现满足

$$
V\lvert \psi\rangle=\lvert s\rangle\otimes W\lvert \psi\rangle,
$$

则 $V^*V=I$ 强制 $W^*W=I$：输入之间的全部内积都转移到未读记录中。若没有该记录，两个正交输入会得到同一个输出，违背等距性。内容与地址相同可以约束门词的编码和固定点，却不撤销这个内积关系。

这与“局部看起来生成或消失，完整关系仍保留”的图像相容。有限门群平均也有同样性质：平均后的量子子系统可能为 $I/d$，但保存控制标签的联合记录仍能恢复输入。它不等价于从无中产生一对具有相反电荷的光子。光子是中性的自共轭场量子；产生算子与湮灭算子的互伴关系也不是两种带相反电荷的粒子。 [16](#ref-tongqed)

关于场，本文提供的是一个可以接到局部可观测代数、状态与探针仪器上的有限关系接口。量子涨落可以由方差及非平凡关联函数表征，不能把它们简单定义成“找不到线性关系”：例如 $\omega(A)=0$ 与 $\omega(A^2)>0$ 完全可以同时成立，而二点函数本身已经是明确的关系。有限维理论也不能精确实现
$[a,a^*]=I$，因为取迹会得到 $0=d$。
电子的费米统计、光子的规范结构以及标准模型的具体群和表示，都还需要额外的局域性、对称性、谱与动力学输入。内部场测量的一种成熟严格接口是系统–探针耦合及其诱导仪器。 [15](#ref-fewsterverch2018)

### 6.5 经典反模型与“公理内生”的逻辑限度

在有限经典样本空间中，$\mathcal N$ 是随机矩阵 $N(y|x)$，参照为严格正概率 $\sigma(x)$。同一二元配对的反向规则为

$$
R_\sigma(x|y)=\frac{\sigma(x)N(y|x)}{\sum_z\sigma(z)N(y|z)}.
$$

这里 $y$ 限于共同的非零输出支持。
若两份参照给同一反向规则，则 $R_\sigma N\rho=\rho$。
反向也成立：$R_\sigma N$ 是以 $\sigma$ 为可逆分布的有限 Markov 链，固定概率只能改变互不连通类的权重；这些权重在 Bayes 比值中相消。也可把经典模型作为本文矩阵定理的对角部门，直接获得同一结论。

所以参照相容候选并不单独排除经典世界。它回答“在既定关系对象中如何内生地更换参照”，而量子与经典的区分还落在对象的非交换结构与实际组合条件上。下一节和附录将这些条件逐一明列，而不借用“定义”一词把它们隐藏。

**白话。**没有上帝模式，意味着只能对已有证据覆盖的共同部分下结论。一个观察者不必吞下另一个观察者的全部结构，才能核对一条共同关系；但几条已经对上的关系，也不能证明整个交集已经穷尽。本理论使用的参照必须有内部准备或评价来源；哪一份参照、哪些门、哪些独立部分真实存在，仍要由内部历史来给出。把公理变成定义间的相容条件，减少的是外部任意指定；它不会让尚未给出的物理内容凭空出现。

<a id="section-7"></a>

## 7. 候选与通常有限量子力学的完整推导接口

<a id="sec-c123-qm"></a>

本节明确列出通常有限量子力学各条规则的推导入口。C123 的参照相容律分类同一回推的允许参照；它单独并不强迫对象必须非交换。要重构整个有限量子理论，还要消费附录的对象选择，以及本节列出的概率、参考、复合与可逆运动条件。以下证明全部在本稿中给出，不把这些条件隐写成参照等价公式的后果。

### 7.1 状态也是一个读口：正关系、Hilbert 空间与 Born 规则

### 命题 7.1（从关系核构造振幅空间）

设历史标签集合 $S$ 带复核 $K$，满足所有有限矩阵 $[K(s_i,s_j)]\succeq0$。在有限形式和 $\sum c_s[s]$ 上定义

$$
\left\langle\sum c_s[s],\sum d_t[t]\right\rangle
 =\sum_{s,t}\overline{c_s}d_tK(s,t).
$$

商去零范数向量并完备化，得到 Hilbert 空间 $H_K$ 与向量 $v_s$，满足 $\langle v_s,v_t\rangle=K(s,t)$；以这些向量的闭线性包为全部空间时，该实现唯一到一个酉同构。

**证明。**
有限正性给出非负半内积。对 $u+t v$ 的范数平方使用判别式得到 Cauchy–Schwarz 不等式，所以零范数向量与全部向量正交，商内积良定义。若另一组 $w_s$ 有同一核，映射 $\sum c_sv_s\mapsto\sum c_sw_s$ 保持范数，因而良定义；稠密线性包上的等距延拓给出所述酉映射。

若历史来自有限 $*$-代数 $\mathcal A$，$\omega$ 为正归一化泛函，且 $K(a,b)=\omega(a^*b)$，则商空间还保留左作用 $\pi(a)[b]=[ab]$。在 $C^*$-对象中，$a^*a\le\|a\|^2I$ 保证此作用有界，单位向量 $\xi=[I]$ 满足 $\omega(a)=\langle \xi,\pi(a)\xi\rangle$。这就是有限 GNS 构造的具体形式。它重建某个状态的循环表示，不把 $\Omega$ 宣告为该单个向量，也不把满秩混合态的 $d^2$ 维 GNS 空间误当成 $M_d$ 的 $d$ 维不可约振幅空间。

### 定理 7.2（效果概率的 Born 表示）

在 $M_d(\mathbb C)$ 的所有效果上，若 $w(I)=1$、$w(F)\ge0$，且

$$
w(F+G)=w(F)+w(G)\qquad(F,G\ge0,\ F+G\le I),
$$

则存在唯一密度矩阵 $\rho\succeq0$、$\operatorname{Tr}\rho=1$，使

$$
w(F)=\operatorname{Tr}(\rho F).
$$

反向每个密度矩阵给出这样的赋值。极端状态恰好是秩一投影，纯态间的射线测试概率为 $|\langle \phi,\psi\rangle|^2$。

**证明。**
细分可加性给 $w(F/n)=w(F)/n$，继而给有理尺度齐次性；正性给单调性。用有理数从两侧逼近 $t\in[0,1]$，即得 $w(tF)=t w(F)$，无须另假设连续。
对任意 $A\ge0$，取 $n$ 使 $A/n\le I$，定义 $f(A)=n w(A/n)$；齐次性保证不依赖 $n$。再定义 $f(A-B)=f(A)-f(B)$，利用正锥上的可加性验证其良定义，得到自伴部分上的实线性正泛函，再唯一复线性延拓。有限维迹配对给唯一 $\rho$；测试所有秩一投影保证 $\rho\ge0$，$f(I)=1$ 给迹归一化。
若 $\rho$ 至少有两个正本征值，可向两方向转移一个足够小权重，写成两不同状态的平均，故非极端。秩一态若是两正状态的平均，则其正交补在两态中均有零期望，强制两态都支撑于同一条射线，因而相同。

这是效果版 Gleason 论证的有限形式 [12](#ref-busch2003)。作为映射 $\omega:\mathcal A\to\mathbb C$，一个状态正是候选的标量终端读口；其二元比较核是 $K(a,b)=\omega(a^*b)$。复数域和全部效果的可加语义已经列入接口，不能称它们也由“归一化”独自推得。

### 7.2 观测、一般测量及状态更新

经典结果集合含 $m$ 个标签时，其代数为 $\mathbb C^m$。一个合法测量读口 $\Phi:\mathbb C^m\to M_d$ 由 $F_j=\Phi(e_j)$ 给出，满足

$$
F_j\succeq0,\qquad\sum_jF_j=I,\qquad
 p(j|\rho)=\operatorname{Tr}(\rho F_j).
$$

因此 POVM 是同一读口定义的交换输出特例。反向任意这样的效果族都给合法读口：若 $[c_{ij}]\in M_n(\mathbb C^m)$ 为正，则每个标签处的数值矩阵都正，故 $[\sum_j c_{ab}(j)F_j]$ 为正。

锐测量取彼此正交的投影 $P_j$，并给各结果一个实读数 $a_j$，便得到自伴算符 $A=\sum_j a_jP_j$，平均读数为 $\operatorname{Tr}(\rho A)$。反向，有限维自伴算符的谱分解给出这种锐测量。因此“可观测量由自伴算符表示”是效果与实读数的这一对应，而不是把每个一般测量都限制成投影测量。

若同时保留测量后的量子输出，则结果 $j$ 对应完全正分支

$$
\mathcal I_j(\rho)=\sum_rK_{jr}\rho K_{jr}^*,\qquad
 \sum_{j,r}K_{jr}^*K_{jr}=I.
$$

完整输出可以写成 $\bigoplus_j\mathcal I_j(\rho)$，它仍是一条通道。读到 $j$ 后的条件态为 $\mathcal I_j(\rho)/p_j$，前提是 $p_j>0$。这个归一化公式描述已取得记录后的条件化；它不声称选中分支本身仍是线性保迹过程。不同仪器可以给同一个 POVM，因而仅知道概率不能唯一决定扰动。

### 定理 7.3（理想锐读出为何给出 Lüders 更新）

设完全正分支 $\mathcal I$ 的效果是投影 $P$，即 $\operatorname{Tr}\mathcal I(\rho)=\operatorname{Tr}(P\rho)$。再要求对每个单位 $\psi\in\operatorname{Ran} P$，$\mathcal I(\lvert \psi\rangle\langle \psi\rvert)=\lvert \psi\rangle\langle \psi\rvert$。则

$$
\mathcal I(\rho)=P\rho P.
$$

**证明。**
写 $\mathcal I(\rho)=\sum_rK_r\rho K_r^*$。效果等式给 $\sum K_r^*K_r=P$，所以每个 $K_r$ 在 $\ker P$ 上为零。对 $\psi\in\operatorname{Ran} P$，一组正秩一项之和支撑于 $\mathbb C\psi$，迫使每个 $K_r\psi$ 均与 $\psi$ 共线。一个线性映射若保持子空间内每一条射线，就在该子空间上为标量：比较任意两个独立向量及其和即可。故 $K_r=c_rP$，且 $P\ne0$ 时 $\sum|c_r|^2=1$。代回即得结论；$P=0$ 时所有 $K_r=0$。

这里没有预设单 Kraus 算子。额外的理想性条件是“不改变该结果子空间内部的每条射线”；只要求结果可重复，还允许在子空间内作非平凡酉旋转，并不足以指定 Lüders 仪器。

### 7.3 与仓库新增校准结果的接点：平方根夹乘可以被选出

本轮配对使用的 $\Gamma_\sigma(A)=\sigma^{1/2}A\sigma^{1/2}$ 不是任意写入的更新公式。
仓库的有限饱和条件为它提供了一条明确的条件选择路径。以下重证所需的精确端点；近似端点则使用式 [(1)](#eq-c123-repo-bound) 的新增支撑秩界。

### 定理 7.4（有限二元平均选出平方根分支）

<a id="thm-c123-calibrated-filter"></a>

在同一 $H=\mathbb C^d$、有限 $K$ 和指定等距 $J:H\to K$ 上，令
$T:\mathcal B(H)\to\mathcal B(K)$ 为正复线性映射，
$T^*(I)=E\in[0,I]$。供应同一有限正权纯态设计

$$
\sum_s w_s p_s\otimes p_s=\frac{I+\mathsf{Swap}}{d(d+1)},
 \qquad \sum_s w_s=1,
$$

以及它们通过同一 $T$ 后的同向读口 $Jp_sJ^*$。定义

$$
R=\sum_s w_s\operatorname{Tr}[Jp_sJ^*T(p_s)],\qquad
 Q=\sum_s w_s\bigl(\operatorname{Tr}[p_s\sqrt E]\bigr)^2.
$$

则 $R\le Q$，且

$$
R\ge Q\quad\Longleftrightarrow\quad
 T(A)=J\sqrt E A\sqrt E J^*\quad\text{对全部 }A.
$$

所选分支的完全正性在这里是结论，无需作为这条定理的前件。

**证明。**
使用成熟正锥引理：对每个积向量非负的自伴矩阵 $G$，有
$\|G\|_{\rm HS}\le\operatorname{Tr} G$。它是 Gurvits–Barnum 可分球界的对偶形式，
包括两因子维数不同的情形。 [10](#ref-gb2002)、[11](#ref-swz2008)

令 $P=\operatorname{supp} E$、$A=\sqrt E$。
对输出效果 $0\le B\le I$，$0\le T^*(B)\le E$，故
$T^*(B)=PT^*(B)P$。效果张成和复线性给出 $T(X)=T(PXP)$。
$E=0$ 时已经得到 $T=0$。其余情形选支持本征基 $Ae_i=a_i e_i$、$a_i>0$，
令 $s=\sum_i a_i$，并采用输入因子在前的未归一化 Choi 矩阵 $C_T$。
正性使它块正，而不要求它正半定。设

$$
G=(A_P^{-1/2}\otimes I)C_T(A_P^{-1/2}\otimes I),\qquad
 v=\sum_i\sqrt{a_i}\,e_i\otimes Je_i.
$$

正确效果保证 $\operatorname{Tr} G=s$，且 $\|v\|^2=s$。令
$z=\langle v,Gv\rangle$、$\ell=\operatorname{Tr}[(I-JJ^*)T(I)]\ge0$。
设计等式在第一因子转置后，逐块取迹即得

$$
d(d+1)Q=\operatorname{Tr} E+s^2,
 \qquad d(d+1)R=\operatorname{Tr} E-\ell+z.
$$

Hilbert–Schmidt Cauchy–Schwarz 与上述块正界给 $z\le s^2$。
所以 $d(d+1)(Q-R)=\ell+s^2-z\ge0$。
若饱和，则 $z=s^2$，从而

$$
\|G-vv^*\|_{\rm HS}^2
 =\|G\|_{\rm HS}^2+s^2-2z\le0.
$$

撤去合同变换得到
$C_T=|a_J\rangle\langle a_J|$，$a_J=\sum_i a_i e_i\otimes Je_i$。
比较矩阵单位并使用输入支持，即得 $T(X)=JAXAJ^*$。
反向直接代入设计矩公式给出饱和。

取 $E=\sigma$、$J=I$ 就得到主文所用参照滤片；取 $E=P$ 是 Lüders 成功分支。
设计等式的张量记号是有限二阶矩，不要求复制未知输入态。
所有设计准备、读口、同一分支和成功效果都须来自实际供应；一般物理通道并不被要求达到这个专门滤片的最优端点。
如果完整菜单还包含别的箭头，只认证这些滤片完全正不等于认证全部菜单完全正。

### 7.4 复合系统、纠缠及可逆运动

### 命题 7.5（独立全矩阵部门的复合）

设 $M_d(\mathbb C)$、$M_m(\mathbb C)$ 以含幺复线性 $*$-嵌入进入同一个非零结合 $*$-代数；两个像彼此交换并生成该代数。则所生成代数为 $M_{dm}(\mathbb C)$。

**证明。**
映射 $a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 由交换性成为满射 $*$-同态。矩阵单位的张量乘积是 $M_{dm}$ 的矩阵单位，且 $M_{dm}$ 为单代数：任一非零双边理想中的非零矩阵元，通过左右矩阵单位可生成所有矩阵单位。因此该含幺非零同态的核为零。

“共同复中心、独立子代数、生成性”承担张量复合的输入。不是任意两个内部窗口都独立。由一个二元块反复独立复合得到 $M_{2^n}$，允许秩 $d$ 的角落即可得到任意 $M_d$。张量正态包含纠缠态；例如 Bell 态不能写成产品态的凸和，因为纯态若可凸分解，各分量必须沿同一射线，而该射线不是产品向量。

在下一小节，完整参考相容给出 Kraus 与等距表示；同维的双向合法可逆过程进一步成为酉共轭。任意 Petz 回推不保证具有这样的双向恢复性质。

若进一步*供应一个*连续的完整酉群 $U(t+s)=U(t)U(s)$、$U(0)=I$，有限维下所有 $U(t)$ 交换且正规，可同时对角化。每个对角元是实加法群的连续单位模特征，故为 $e^{-i\omega_jt}$；由局部连续辐角和加法性可直接证明。于是存在自伴 $H$，

$$
U(t)=e^{-itH/\hbar},\qquad
 i\hbar\,\frac{d}{dt}\psi(t)=H\psi(t).
$$

时间参数、连续群的供应、具体 $H$ 与作用量单位 $\hbar$ 均没有由静态比较关系决定。静态内生关系与具体动力学选择不可互换。

### 7.5 完整参考相容、Kraus 表示及酉运动

### 定理 7.6（内部参考的相容性给出完整扩张）

<a id="thm-c123-kraus"></a>

设 $N:M_d(\mathbb C)\to M_k(\mathbb C)$ 复线性、保迹。对全部有限参考，
$(N\otimes\operatorname{id})(X)\ge0$ 当 $X\ge0$，当且仅当

$$
N(X)=\sum_a K_aXK_a^*,\qquad \sum_aK_a^*K_a=I.
$$

这也等价于存在有限记录空间 $E$ 及等距
$V:H\to K\otimes E$，使 $N(X)=\operatorname{Tr}_E(VXV^*)$。

**证明。**
取 $\lvert \Gamma\rangle=\sum_re_r\otimes e_r$。完整参考相容给正矩阵

$$
C_N=(\operatorname{id}_d\otimes N)\lvert \Gamma\rangle\langle \Gamma\rvert
 =\sum_{r,s}\lvert r\rangle\langle s\rvert\otimes N(\lvert r\rangle\langle s\rvert)\ge0.
$$

谱分解 $C_N=\sum_aw_aw_a^*$，写
$w_a=\sum_re_r\otimes K_ae_r$。
比较矩阵块即得 Kraus 公式；迹对偶给归一化。
反向，每项联合夹乘 $(K_a\otimes I)X(K_a^*\otimes I)$ 都为正。
定义 $V\psi=\sum_aK_a\psi\otimes\lvert a\rangle$，
归一化给 $V^*V=I$，偏迹给 $N$；反向把等距在记录基下展开即可。

这是有限 Choi–Stinespring 构造。 [13](#ref-choi1975)、[14](#ref-stinespring1955)
它的输入是完整参考相容，不是普通单系统二元概率正性。
转置 $\Theta(X)=X^{\mathsf T}$ 保持单系统正性及迹，
但

$$
(\Theta\otimes\operatorname{id})\lvert \Phi^+\rangle\langle \Phi^+\rvert=\tfrac12\mathsf{Swap}
$$

在反对称向量上有本征值 $-1/2$，所以不合法。
它说明即使单系统比较与某些回推几何都成立，也不能删除联合参考条件。

### 定理 7.7（同维双向合法可逆过程是酉共轭）

若 $N,R:M_d(\mathbb C)\to M_d(\mathbb C)$ 均为通道，且 $RN=\operatorname{id}$，
则存在酉 $U$，$N(X)=UXU^*$、$R(X)=U^*XU$。

**证明。**
同维有限线性空间上的左逆也是双向逆，故 $NR=\operatorname{id}$。
令 $\Phi=N^*$、$\Psi=R^*$，都是保单位完全正映射。
Kraus 等距表示给 Schwarz 不等式
$\Phi(A^*A)\ge\Phi(A)^*\Phi(A)$；
再施加 $\Psi$ 并对 $\Psi$ 使用同一不等式，可得

$$
A^*A\ge\Psi(\Phi(A)^*\Phi(A))
 \ge\Psi(\Phi(A))^*\Psi(\Phi(A))=A^*A.
$$

因为 $\Psi$ 可逆，原 Schwarz 余量为零。
将 $A+tB$ 代入并分别比较实、虚交叉项，得
$\Phi(A^*B)=\Phi(A)^*\Phi(B)$。
所以 $\Phi$ 是含幺 $*$-自同构。

取矩阵单位 $E_{ij}$。$\Phi(E_{ii})$ 是两两正交且总和为 $I$ 的最小投影；
它们秩均为一。取各自单位像向量 $u_i$，
$\Phi(E_{ij})$ 的初始及终止空间给
$\Phi(E_{ij})=c_{ij}\lvert u_i\rangle\langle u_j\rvert$，
乘法与伴随给 $c_{ij}c_{jl}=c_{il}$、$c_{ji}=\bar c_{ij}$、
$|c_{ij}|=1$。调整 $u_i$ 的相位可使全部 $c_{ij}=1$，
得到 $\Phi=\operatorname{Ad}_W$。取迹伴随即得 $N=\operatorname{Ad}_{W^*}$。

因此，在已经供应连续可逆时间参数的条件下，前面的指数形式和
Schrödinger 方程成立。一般有损过程的 Petz 双反向性
$(N^\sharp)^\sharp=N$ 则是*反推指派的对合*，
不等于 $N^\sharp N=\operatorname{id}$；不能用前者替代本定理的假设。

### 7.6 两项直接可算的量子约束

### 命题 7.8（不确定关系来自二元正比较）

对自伴 $A,B$ 与任意状态 $\omega$，有

$$
\operatorname{Var}_\omega(A)\operatorname{Var}_\omega(B)
 \ge\left|\omega\bigl((A-\omega(A)I)(B-\omega(B)I)\bigr)\right|^2
 \ge\frac14|\omega([A,B])|^2.
$$

**证明。**
令 $X=A-\omega(A)I$、$Y=B-\omega(B)I$。状态的二元 Gram 矩阵
$\left(\begin{smallmatrix}\omega(X^2)&\omega(XY)\\\omega(YX)&\omega(Y^2)\end{smallmatrix}\right)$ 为正，行列式非负给出第一项。又 $\omega(YX)=\overline{\omega(XY)}$，所以 $2i\operatorname{Im}\omega(XY)=\omega([A,B])$，给出第二项。

### 命题 7.9（独立两端的 CHSH 约束）

若 $A_0,A_1$ 与 $B_0,B_1$ 分别为两独立量子部门的自伴反射，即平方均为 $I$，则

$$
S=A_0\otimes(B_0+B_1)+A_1\otimes(B_0-B_1)
 \quad\text{满足}\quad \|S\|\le2\sqrt2.
$$

该界在两个量子比特中可以达到。

**证明。**
直接展开得 $S^2=4I-[A_0,A_1]\otimes[B_0,B_1]$；每个交换子范数至多为 $2$，故 $\|S^2\|\le8$。取 $A_0=Z,A_1=X$、$B_0=(Z+X)/\sqrt2,B_1=(Z-X)/\sqrt2$，并在 Bell 态 $(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$ 上求期望，得到 $2\sqrt2$。若四个结果预先取定为局部数值 $\pm1$，同一表达式绝对值只能为 $2$；对这样的赋值作概率混合仍不超过 $2$。

这些是本稿明列结构条件所重构的通常量子理论的约束，不是新的实验偏离预言。要声称不同于现有量子力学的物理预测，还须修改明确的结构输入并计算其可区分后果。

### 7.7 可复用的推导清单

| 通常的量子结构 | 本稿的推导入口 | 仍然承重的输入 |
|---|---|---|
| Hilbert 振幅与射线 | 全有限正核的商空间；$M_d$ 不可约模块 | 复对象选择、可叠加历史语义 |
| 密度矩阵、Born 规则 | 效果的正、归一化及细分可加 | 所有相关效果的同一赋值 |
| POVM 与仪器 | 交换结果代数与带记录的完全正分支 | 实际结果标签与门供应 |
| 完全正性及 Kraus 形式 | 本节的参考相容与有限 Choi 构造 | 全部必要有限参考兼容 |
| 张量复合及纠缠 | 共同复中心上的交换生成关系 | 独立性与复合供应 |
| 可逆门 | 双向合法可逆性、全矩阵自同构 | 同一完整通道、同维时为酉 |
| Lüders 更新 | 锐效果加每条内部射线不受扰动 | 理想测量条件 |
| Schrödinger 方程 | 连续完整酉群的谱分解 | 时间、群、$H$ 及单位选择 |

**白话。**状态是一种读口，测量是一种把问题送到结果标签的读口，运动也是一种把后面的问题回拉到前面的读口。要求同一来源的全部比较在参考接续后仍合法，再要求内部参照的二元比较能相互对读，就把概率、完整记录和参考回推接进同一套定义。要得到具体的物理世界，还必须说哪些对象、哪些复合、哪些钟和哪些门实际存在；这部分不会因为把公理改叫定义就自动消失。

<a id="section-8"></a>

## 8. 有限量子原子的实关系选择：前提与完整证明

<a id="sec-local-core"></a>

本附录自足重述前轮实球形二元块的局部选择步骤，说明主文复矩阵部门的一种来路。它是继承的对象接口，不是本轮另提一个候选。其范围是实球形二元正锥及下列动力标签条件；它没有证明这些条件由一般正核自动强制成立。这里由三方向乘积形成的中心单位记为 $\jmath$，以区别一般线性算子的符号。

### 8.1 实锥与规范对称变化

### 定义 8.1（二元比较块）

令 $W$ 为有限维实欧氏空间，$V=\mathbb R e\oplus W$、$e=(1,0)$。未归一化的正关系为

$$
C=\{(s,r):s\ge\|r\|\},\qquad
 \langle (s,r),(t,u)\rangle_E=st+r\cdot u.
$$

规范滤片是把 $e$ 送到给定严格正元 $x=(s,r)$ 的欧氏正定、自伴、双向保锥线性变换。双向保锥指变换及其逆都保持 $C$。

### 引理 8.2（规范滤片及其导数）

令 $\delta=\sqrt{s^2-\|r\|^2}>0$。唯一的规范滤片是

$$
P_x=\begin{pmatrix}
 s&r^{\mathsf T}\\
 r&\delta I+rr^{\mathsf T}/(s+\delta)
 \end{pmatrix}.
$$

其一阶响应定义对称乘法

$$
(\alpha,a)\circ(\beta,b)
 =\left.\frac{d}{dt}P_{e+t(\alpha,a)}(\beta,b)\right|_{0}
 =(\alpha\beta+a\cdot b,\alpha b+\beta a).
$$

特别地，$L_a(\beta,b)=(a\cdot b,\beta a)$。

**证明。**
写 $\eta=\operatorname{diag}(1,-I)$。保锥可逆变换 $T$ 保持锥边界，所以对所有单位 $n$，$Q(T(1,n))=0$。将 $T^{\mathsf T}\eta T$ 分块，比较 $n,-n$ 消去非对角块，再比较正交基与它们的二元和，得 $T^{\mathsf T}\eta T=c\eta$；$Te$ 在锥内部给 $c>0$。

若 $T=T^{\mathsf T}\succ0$ 且 $Te=x$，写其右下块为 $B$，便有 $c=\delta^2$、$B^2=\delta^2 I+rr^{\mathsf T}$。正定 $B$ 是右侧唯一正平方根，在 $r^\perp$ 上为 $\delta I$、在 $r$ 方向为 $s$，即显示公式。反过来，该公式的特征值为 $s\pm\|r\|$ 及 $\delta$，全为正；直接相乘验证 $P_x\eta P_x=\delta^2\eta$，且 $P_xe=x$，从而双向保锥。对 $s=1+t\alpha,r=ta$ 求导即得乘法。该乘法满足 Jordan 恒等式，因为 $L_{z^2}$ 是 $L_z$ 的线性组合；其平方锥恰为 $C$，可用互补幂等元 $p_\pm=(1,\pm n)/2$ 对正元分解并开平方验证。

这一构造仍承担球形正锥、欧氏标尺和规范滤片的定义。若赋予它物理实现，还要保留成功权重；双向保正滤片不等于确定性的可逆通道。

### 8.2 二元回路为何强制三维

### 定义 8.3（旁观方向条件）

每个实方向 $a$ 产生 $D_a\in\mathfrak{so}(W)$，$a\mapsto D_a$ 实线性，$D_a a=0$，且 $D\ne0$。要求对全部标签及其线性合成，

<a id="eq-c123-local-spectator"></a>

$$
\boxed{[D_a,D_b]z=0\quad(z\perp a,b).}
\tag{39}
$$

这是完整向量等式。只比较 $z\cdot[D_a,D_b]z$ 没有约束力，因为反对称算子的该自比较总是零。

### 定理 8.4（三维选择）

<a id="thm-c123-local-three"></a>

上述条件强制 $\dim W=3$，且存在 $\kappa>0$，使

<a id="eq-c123-local-loop"></a>

$$
\begin{aligned}
[D_a,D_b]&=-\kappa[L_a,L_b],
\end{aligned}
\tag{40}
$$

<a id="eq-c123-local-square"></a>

$$
\begin{aligned}
D_a^2x&=\kappa\bigl((a\cdot x)a-\|a\|^2x\bigr),
\end{aligned}
\tag{41}
$$

<a id="eq-c123-local-triple"></a>

$$
\begin{aligned}
D_aD_bx&=\kappa\bigl((a\cdot x)b-(a\cdot b)x\bigr),
\end{aligned}
\tag{42}
$$

<a id="eq-c123-local-bracket"></a>

$$
\begin{aligned}
D_{D_a b}&=[D_a,D_b].
\end{aligned}
\tag{43}
$$

按 $D$ 选择取向后，$D_ab=\sqrt\kappa\,a\times b$。

**证明。**
标签线性及 $D_aa=0$ 给 $D_ab=-D_ba$，故 $x\cdot D_ab$ 是交替三形式。令

$$
B(a,b)x=(b\cdot x)a-(a\cdot x)b=[L_a,L_b]x.
$$

交换子 $[D_a,D_b]$ 反对称。式 [(39)](#eq-c123-local-spectator) 使它在 $\operatorname{span}(a,b)^\perp$ 上为零，并保持 $\operatorname{span}(a,b)$；二维反对称算子只有一个方向，所以它是 $B(a,b)$ 的实倍数。

这个倍数不能逐对自由选。取正交基 $e_i$，写 $[D_{e_i},D_{e_j}]=\lambda_{ij}B(e_i,e_j)$。在二元合成标签

$$
a=\sum_i e_i,\qquad b=\sum_i\left(i-\frac{n+1}{2}\right)e_i
$$

上展开，其每个基对系数都是非零的 $j-i$。合成对也必须有一个共同平面比例，比较基系数便得全部 $\lambda_{ij}=\lambda$。双线性将它扩到任意 $a,b$。

将交换子等式作用于 $a$ 并使用反对称性，得

$$
\|D_ab\|^2=-\lambda\bigl(\|a\|^2\|b\|^2-(a\cdot b)^2\bigr).
$$

非平凡性排除 $\lambda=0$，故 $\lambda=-\kappa<0$，并得 [(41)](#eq-c123-local-square)。极化该平方式，加上交换子式，给 [(42)](#eq-c123-local-triple)；再由 $D_{D_ab}x=-D_xD_ab$ 得 [(43)](#eq-c123-local-bracket)。

取正交单位 $u,v$，令 $w=D_uv/\sqrt\kappa$。上式说明 $u,v,w$ 正交归一，且

$$
D_w=\sqrt\kappa(vu^{\mathsf T}-uv^{\mathsf T}),\qquad
 D_w^2=-\kappa(P_u+P_v).
$$

另一方面，式 [(41)](#eq-c123-local-square) 给 $D_w^2=\kappa(P_w-I)$。因此

$$
\boxed{I=P_u+P_v+P_w,}
$$

恰好三个方向覆盖整个 $W$。三维交替三形式只有一个尺度，范数式将其大小固定为 $\sqrt\kappa$；取向由其符号决定。

若去掉 $D\ne0$，任意维度都容许 $D=0$。若只查坐标对，模型 $W=\mathbb R^3\oplus\mathbb R$、$D_ab=(a'\times b',0)$ 会通过；但对 $a=e_1+e_4,b=e_2,z=e_1-e_4$，有 $z\perp a,b$ 而 $[D_a,D_b]z=e_2$。这说明必须检验合成标签。此规则只作用于二元球块，不能把它逐字施加到一般高维系统的全部自伴元。

### 8.3 三方向的有向体积成为内部复数

这里把继承对象接口中的“由该块生成的结合保星闭包”说精确：它是非零含幺实结合
$*$-代数 $\mathcal B$，带实线性映射 $\iota:V\to\mathcal B$，满足

$$
\iota(e)=1,\qquad \iota(x)^*=\iota(x),\qquad
 \frac{\iota(x)\iota(y)+\iota(y)\iota(x)}2=\iota(x\circ y),
$$

且 $\iota(V)$ 生成整个 $\mathcal B$。结合性、保星与生成性是这里明确保留的闭包条件；以下证明所有这样的非零闭包都给出同一个代数，不先假设它的维数。

作为实结合闭包的显式构造，用实数对构造 $\mathbb C_\jmath=\{s+\jmath t\}$，其中 $\jmath^2=-1$。记 $\mathcal A=\mathbb C_\jmath\oplus\mathbb C_\jmath^3$，在其上定义

<a id="eq-c123-local-product"></a>

$$
(\alpha,a)(\beta,b)
 =(\alpha\beta+a\cdot b,\alpha b+\beta a+\jmath(a\times b)).
\tag{44}
$$

这里的点积、叉积作复双线性延伸。

### 定理 8.5（内部复代数及最小振幅）

<a id="thm-c123-local-complex"></a>

式 [(44)](#eq-c123-local-product) 给出实八维结合 $*$-代数，伴随为逐分量复共轭，自伴部恰为原来的 $V$。对于正向正交基，

$$
e_ie_j+e_je_i=2\delta_{ij}1,
 \qquad \jmath=e_1e_2e_3,
 \qquad \jmath^2=-1.
$$

因此 $\jmath$ 实际属于三个实方向生成的闭包；该闭包是 $\operatorname{Cl}_{3,0}\cong M_2(\mathbb C)$，最小左理想为 $H\cong\mathbb C^2$。

**证明。**
由三线性，只需在三个实向量上核对结合律。两个括号方式的标量项相同，向量差为

$$
(a\cdot b)c-(b\cdot c)a-(a\times b)\times c+a\times(b\times c)=0,
$$

这是定理 [8.4](#thm-c123-local-three) 的三重积恒等式。共轭将 $\jmath$ 变号，交换向量次序也使叉积变号，故 $(xy)^*=y^*x^*$。直接计算得 $e_1e_2=\jmath e_3$，从而 $e_1e_2e_3=\jmath$，没有再添独立复方向。

映射

$$
\alpha1+z\cdot e\longmapsto
 \begin{pmatrix}\alpha+z_3&z_1-iz_2\\z_1+iz_2&\alpha-z_3\end{pmatrix}
$$

保持乘法与伴随，且每个复二阶矩阵唯一具有这种展开，所以是同构。

还须排除其他闭包把这个代数进一步压小。令 $\operatorname{Cl}_{3,0}$ 为由
$e_i^*=e_i$、$e_ie_j+e_je_i=2\delta_{ij}1$ 定义的含幺实结合 $*$-代数。
反交换关系把全部词约到
$1,e_1,e_2,e_3,e_1e_2,e_1e_3,e_2e_3,e_1e_2e_3$，故其维数至多为八。
上述显式模型由三个 $e_i$ 生成，且实维数为八，所以从这个定义代数到模型的满射必为同构。

任意容许闭包 $\mathcal B$ 的三个生成元也满足这些关系，因而是
$\operatorname{Cl}_{3,0}\cong M_2(\mathbb C)$ 的非零含幺商。$M_2(\mathbb C)$ 作为*实*代数仍然简单：
若双边理想含非零矩阵 $A$，选取非零条目 $a_{ij}$，则
$E_{pi}AE_{jq}=a_{ij}E_{pq}$ 属于该理想；再左乘 $(a_{ij}^{-1})I$，得到每个矩阵单位
$E_{pq}$。左乘 $iI$ 又得到全部 $iE_{pq}$，这些矩阵的实线性张成就是整个代数。
所以商映射的核只能为零或全体；非零含幺目标排除后者。
因此任意容许的生成闭包都与显式模型保星同构，不存在更小的非零商。

令 $p=(1+e_3)/2,q=e_1p$。左理想 $\mathcal A p$ 在中心 $\mathbb C_\jmath$ 上由 $p,q$ 张成，且对 $x=\alpha p+\beta q,y=\gamma p+\delta q$，

$$
x^*y=(\bar\alpha\gamma+\bar\beta\delta)p.
$$

这个系数给正定复内积。矩阵表示说明它是二维且为最小左理想，代数在其上忠实作用。

自伴元 $sI+r\cdot\sigma$ 的特征值是 $s\pm\|r\|$，所以构造后的矩阵正锥恰好恢复原来的 $C$。其归一化截面是三维球，极点是球面；概率与纯态的严格对应见第 [7](#sec-c123-qm) 节。

**白话。**先规定两份方向怎样比较，再比较沿它们前后运动的小回路。回路不能暗中推动和这两个方向都垂直的完整参考；对合成方向也这样要求，两个方向就会带出第三个，而且三个已经覆盖整个二元块。把三个方向按顺序相乘，会得到一个再乘自己就反号的内部关系，它承担复数的作用。这样的复结构有了明确来路；观察者的记录守恒接下来才有可用的物理振幅空间。

有限系统类还允许独立复合以及非零投影支持的角代数。由第 [7](#sec-c123-qm) 节的复合定理，$N$ 个二元原子给 $M_{2^N}(\mathbb C)$。对任意 $d\le2^N$，取秩 $d$ 的投影 $p$，角代数 $pM_{2^N}(\mathbb C)p$ 同构于 $M_d(\mathbb C)$，单位为 $p$。因此在这项系统闭包约定下，全部有限复量子系统均得到构造。支持限制与观察窗口的保单位嵌入是两类接口，不能把改变单位的角嵌入误作同一个共同来源接缝。

<a id="references"></a>

## 参考文献

<a id="ref-repo-c123"></a>

### [1]

The Omega Institute, *AURIC Internal Balanced Calibration and Filter Composition Geometry C113*，
§§15–22，特别是本轮新增 §§20–22。
固定提交 `5ccf20964da0a6695170f80f89e8383c92913a6c`，
2026-11-03 16:57:05 UTC，合并 PR
#26143。
[不可变理论源码](https://github.com/the-omega-institute/trureturing/blob/5ccf20964da0a6695170f80f89e8383c92913a6c/docs/develop/theory/AURIC_INTERNAL_BALANCED_CALIBRATION_AND_FILTER_COMPOSITION_GEOMETRY_C113.md)。
核读重点为同一正分支、精确有限设计、正确效果、目标支持泄漏、无谱底近饱和界与非 CP 反例。
本轮新增为理论文稿；本报告中的普通数学证明不冒充已完成的 Lean 形式核验，也未重新运行项目全量构建。

<a id="ref-petz1986"></a>

### [2]

D. Petz, “Sufficient subalgebras and the relative entropy of states of a von Neumann algebra”,
*Communications in Mathematical Physics* **105**, 123–131 (1986).
[作者保存的论文全文](https://math.bme.hu/~petz/pdf/29suff.pdf)；
[doi:10.1007/BF01212345](https://doi.org/10.1007/BF01212345)。
另见 “Sufficiency of channels over von Neumann algebras”,
*Quarterly Journal of Mathematics* **39**(1), 97–108 (1988),
[doi:10.1093/qmath/39.1.97](https://doi.org/10.1093/qmath/39.1.97)。
本文的参照相容等价属于既有充分性理论的有限维内容。

<a id="ref-takesaki1972"></a>

### [3]

M. Takesaki, “Conditional expectations in von Neumann algebras”,
*Journal of Functional Analysis* **9**(3), 306–321 (1972).
[doi:10.1016/0022-1236(72)90004-3](https://doi.org/10.1016/0022-1236(72)90004-3)。
本稿直接证明有限矩阵情形所需的模不变、块乘积与保参照条件期望的等价。

<a id="ref-beny2007"></a>

### [4]

C. B
'eny, A. Kempf and D. W. Kribs, “Quantum Error Correction of Observables”,
*Physical Review A* **76**, 042303 (2007).
[arXiv:0705.1574v1](https://arxiv.org/html/0705.1574v1)；
[doi:10.1103/PhysRevA.76.042303](https://doi.org/10.1103/PhysRevA.76.042303)。
算子代数纠错的源结论；本文只需完整源角上的噪声积交换子判准，并给出相应证明。

<a id="ref-furuya2022"></a>

### [5]

K. Furuya, N. Lashkari and S. Ouseph, “Real-space RG, error correction and Petz map”,
*Journal of High Energy Physics* **2022**(1), 170 (2022).
[arXiv:2012.14001v4](https://arxiv.org/html/2012.14001v4)；
[doi:10.1007/JHEP01(2022)170](https://doi.org/10.1007/JHEP01(2022)170)。
附录 C 说明模相容条件和恢复代数的关系；本文不给它附加“已从门词导出物理时空”的含义。

<a id="ref-ahmad2025"></a>

### [6]

S. Ali Ahmad and M. S. Klinger, “Emergent geometry from quantum probability”,
*Physical Review D* **111**, 105015 (2025).
[论文全文](https://journals.aps.org/prd/pdf/10.1103/PhysRevD.111.105015)；
[doi:10.1103/PhysRevD.111.105015](https://doi.org/10.1103/PhysRevD.111.105015)。
§III C 列出 Petz 充分性、反向规则相同及互相恢复的等价。
这里只核对所用既有定理的归属，不采用其量子引力解释作为本稿的已证结果。

<a id="ref-amtw2000"></a>

### [7]

A. Ambainis, M. Mosca, A. Tapp and R. de Wolf, “Private Quantum Channels”,
*Proceedings of FOCS 2000*, 547–553 (2000).
[作者论文全文](https://homepages.cwi.nl/~rdewolf/publ/qc/AMTW00.pdf)。
本文复用随机 Pauli／有限幺正平均及保留控制标签的恢复机制，不把它称作新物理。

<a id="ref-gst2021"></a>

### [8]

E. Nielsen, J. K. Gamble, K. Rudinger, T. Scholten, K. Young and R. Blume-Kohout,
“Gate Set Tomography”, *Quantum* **5**, 557 (2021).
[arXiv:2009.07301v2](https://arxiv.org/abs/2009.07301v2)；
[doi:10.22331/q-2021-10-05-557](https://doi.org/10.22331/q-2021-10-05-557)。
自洽估计与 gauge 自由度；本文的对比度反例直接计算证明。

<a id="ref-relational2021"></a>

### [9]

M. Oszmaniec, D. J. Brod and E. F. Galvão,
“Measuring relational information between quantum states, and applications”,
[arXiv:2109.10006v1](https://arxiv.org/abs/2109.10006v1) (2021).
本文只用三态 Bargmann 关系量及有限循环测试，并明列其实际联合控制前件。

<a id="ref-gb2002"></a>

### [10]

L. Gurvits and H. Barnum, “Largest separable balls around the maximally mixed bipartite quantum state”,
*Physical Review A* **66**, 062311 (2002).
[arXiv:quant-ph/0204159v2](https://arxiv.org/html/quant-ph/0204159v2)；
[doi:10.1103/PhysRevA.66.062311](https://doi.org/10.1103/PhysRevA.66.062311)。
定理 1 的可分球给出本文校准端点所需块正 Hilbert–Schmidt 范数界。

<a id="ref-swz2008"></a>

### [11]

S. J. Szarek, E. Werner and K.
.{Z}yczkowski,
“Geometry of sets of quantum maps: a generic positive map acting on a high-dimensional system is not completely positive”,
*Journal of Mathematical Physics* **49**, 032113 (2008).
[arXiv:0710.1571v2](https://arxiv.org/html/0710.1571v2)；
[doi:10.1063/1.2841325](https://doi.org/10.1063/1.2841325)。
推论 3 后明确给出块正矩阵满足 $\operatorname{Tr} G^2\le(\operatorname{Tr} G)^2$。

<a id="ref-busch2003"></a>

### [12]

P. Busch, “Quantum states and generalized observables: a simple proof of Gleason's theorem”,
*Physical Review Letters* **91**, 120403 (2003).
[arXiv:quant-ph/9909073v3](https://arxiv.org/abs/quant-ph/9909073v3)。
效果可加而非仅锐投影可加；本文的有限证明包括 qubit。

<a id="ref-choi1975"></a>

### [13]

M.-D. Choi, “Completely positive linear maps on complex matrices”,
*Linear Algebra and its Applications* **10**(3), 285–290 (1975).
[doi:10.1016/0024-3795(75)90075-0](https://doi.org/10.1016/0024-3795(75)90075-0)。

<a id="ref-stinespring1955"></a>

### [14]

W. F. Stinespring, “Positive functions on $C^*$-algebras”,
*Proceedings of the American Mathematical Society* **6**(2), 211–216 (1955).
[doi:10.1090/S0002-9939-1955-0069403-4](https://doi.org/10.1090/S0002-9939-1955-0069403-4)。
本文直接给出所需有限 Kraus 与等距构造。

<a id="ref-fewsterverch2018"></a>

### [15]

C. J. Fewster and R. Verch, “Quantum fields and local measurements”,
[arXiv:1810.06512v3](https://arxiv.org/abs/1810.06512v3) (2020).
系统–探针耦合、完全正诱导读口、条件仪器与因果顺序相容。

<a id="ref-tongqed"></a>

### [16]

D. Tong, *Quantum Field Theory*, Chapter 6, “Quantum Electrodynamics”.
[作者课程原文](https://davidtong.org/pdfs/teaching/quantum-field-theory/qft6.pdf)。
用于电磁场量子化、物理偏振及中性场的基本区分，不据此推断本稿已经重构标准模型。
