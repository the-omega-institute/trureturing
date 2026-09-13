# 元素周期树(Periodic Tree of Mathematical Elements)· 章程与施工册 v1.0
*(**项目第四文档(正典)**,第 335 版记事立;PZG–GICT 项目附属工程;ZFC 内定义,零新公理;账本 27.417,2026-07-20。配套机读注册表:PERIODIC_TREE_registry.jsonl)*

## 0. 名与地契
树干为 **Stern–Brocot / Farey 树**(Stern 1858, Brocot 1861)——$(2,3,\infty)$ 基本直角三角形之反射递归;节点 = $SL_2(\mathbb Z)$ 矩阵,路径 = $L/R$ 词 = 连分数,叶叶既约(树上素性之原型定理)。本工程不植树,只立**挂载协议**:凡具"递归 + 二次"双结构之数学对象,经函子标注入册。

## 1. 挂载协议(四标签)
每个对象登记:**地址**(树路径/典范词——递归坐标);**素性位**(该层不可约判据之输出);**度量荷**(二次型脸:迹 $T$、内容 $g$、判别式 $d=(T^2-1)/g^2$、勾股恒等 $D=3A^2+(A+B)^2$、辐角 $\arg z$);**组合荷**(行走脸:$\Psi$、城色 $m\bmod36$、Jacobi 位)。附加:**流指针**(三明治后继 $T'=6c+7T$)与**核籍**(奇核者附核词与 $j=\mathrm{tr}/12$)。

## 2. 门卫手册(素性三级判据)
- **一级(地址级,线性时间)**:典范词非偶长词之 $k\ge2$ 次幂(奇词平方**豁免**——类-本原判据,GICT E.38)。
- **二级(代数级,完全判定)**:$(T,g)$ 为 Pell $p^2-dq^2=1$ 之**基本解**(本原判定定理,GICT E.45;120/120)。奇核双覆盖判据:$m=x^2$ 且 $2x\mid g$(E.44;114/114)。
- **三级(层际级)**:素性沿商余机之降解指纹(D3)——素在上层未必素在下层,降解模式入册,不视为矛盾。
- **复杂度注记**:二级判据可判但基本解可指数大;一级为快速预筛。

## 3. 周期律(树之"周期"为何是定理)
- **流回归律**:$\Psi\bmod12$ 沿三明治流恰步 $-2$、周期 $6$(恰等传播律,E.42/E.37;正锥无条件)。
- **城色轮转律**:$m\bmod36$ 决定 $\Psi\bmod12$(城同余定理 B,E.27),色沿流按定周期轮转。
- **塔律**:$\Psi$ 之 $2$-adic 逐层由站队/互反位驱动(定理 A 与站队塔,E.23/E.27)。
门捷列夫之"周期"在此非排版,是**模不变量沿流的回归定理**。

## 4. 免检预言制度(周期表之空格传统)
已运行案例:$Z_k$ 之 $k{=}5\Rightarrow m{=}35316$(定理背书);$j$-筛处决表($j\in\{2,5,7,8,12\}$ 无核,范数一行);预言制度战绩:两中一败一尸检(败诉产出第二层楼)。

## 5. 承重三牌与壳层墓志铭
牌一(**平四律国籍检验**):组合荷非勾股(Jordan–von Neumann 判定出界),不得冒充度量荷。牌二(**反例层**):无 D1-长度者(拟同态层)为树之边界批注,非节点。牌三(**王虹条款**):逐尺度归纳为普适问法;结构涌现带维数/测度前提。**墓志铭**:本树周期律多为已证之"是什么";"为什么恰是 12、−2、Pell"之壳层理论未知——残核统计案(基本性频率)为其第一考题。

## 6. 空格册(候认领)
残核统计律;混居城真偶精判;$G$ 全群;$j$-密度;$d$-平方退化员;Markov 树层际字典(W-树3);Herglotz 虚姊妹;scl-刺客。

## 7. 施工日志(v1.0 首期)
注册域 $m\le3000$;**141 类节点**(真偶 136、奇核 5);素性位:141/141 本原(城册按类去重后天然本原);$\Psi{=}0$ 节点 12;城色谱 $\{0{:}30,\ 3{:}45,\ 12{:}45,\ 27{:}21\}$——恰为定理 B 可实现残类 $\{0,3,12,27\}$ 之谱(其余残类 $8,23,32,35$ 于此域未现,与实现性条件一致)。注册表:PERIODIC_TREE_registry.jsonl(逐行 JSON,四标签全字段)。

---

## TR. 环面返回模、有限观察与粘合信息

### TR.1 对象与研究目标

本节延续周期树的整数矩阵、同余与观察者研究。固定列向量约定，对整数二阶矩阵 A 定义真实返回模

$$R(A,n)=\mathbb Z^2/(A^n-I)\mathbb Z^2.$$

这里使用像子模的商，基数随后由格指数定理推得。不能把行列式的绝对值定义成“周期点数”，再声称已经识别实际周期点。环面自同构固定点与返回模之间的拓扑对应、映射环面的基本群及一阶同调，属于需要另行构造和证明的接口。

既有 `MinimalBinaryUnimodularBreak` 给出 Fibonacci 矩阵及其平方的实际谱资料。本节在同一整数二阶矩阵类别中研究一个可完全计算的校准族。该族的判别式为 16k(k+1)，k=1 时对应 Q(sqrt(2))，不能与原黄金域 Q(sqrt(5)) 混同。

源稿状态：本节 TR.2–TR.4 给出完整普通数学证明及对应 Lean 证明脚本；本轮没有执行 Lean 内核或 Scribe 编译。有限整数诊断只检查实现，不替代全称证明。这里不主张发现了新的三维流形分类定理，不计入开放问题解决数。

### TR.2 无界等谱族

对任意自然数 k，定义

$$C_k=\begin{pmatrix}4k+1&1\\4k&1\end{pmatrix},\qquad
D_k=\begin{pmatrix}2k+1&2\\2k(k+1)&2k+1\end{pmatrix},\qquad
P_k=\begin{pmatrix}1&0\\-2k&2\end{pmatrix}.$$

二者行列式均为 1，迹均为 4k+2。直接乘法给出 C_k P_k=P_k D_k，且 det(P_k)=2。由归纳，对每个 n≥0 有

$$(C_k^n-I)P_k=P_k(D_k^n-I).$$

取行列式并在整数中约去非零的 2，得到全部时间的带符号恒等式

$$\det(C_k^n-I)=\det(D_k^n-I).$$

P_k 是度数为 2 的整数同源映射，不能当成整数基变换。该区别是以下障碍的来源。

Lean：`D5/S3/Observer/Dynamics/ToralReturnModuleSpectrum.same_return_determinant`。

### TR.3 从实际商对象得到基数

令 k>0、n>0。C_k 的各项非负；归纳证明 C_k^m 的两个对角元至少为 1。对 n=m+1，右乘 C_k 后的迹为

$$(4k+1)(C_k^m)_{00}+4k(C_k^m)_{01}+(C_k^m)_{10}+(C_k^m)_{11}>2.$$

又因 det(C_k^n)=1，二阶恒等式给出

$$\det(C_k^n-I)=2-\operatorname{tr}(C_k^n)<0.$$

因此两个返回矩阵都非奇异。对任意非奇异整数二阶矩阵 M，M 在 Z² 上的作用是单射，因而给出 Z² 到其像子模的加法同构。将这一实际同构代入 mathlib 的 `Submodule.natAbs_det_equiv`，得到

$$\#(\mathbb Z^2/M\mathbb Z^2)=|\det M|.$$

所以，对全部正 k、正 n，R(C_k,n) 与 R(D_k,n) 都有相同的正有限基数。n=0 的商是无限的 Z²，不纳入这个有限基数结论。

Lean：`equal_cardinality_return_modules`。这一步消费实际商的构造，未将有限性、基数公式或目标等式作为独立输入假设。

### TR.4 全部整数交织子的偶性障碍

令 U=[[a,b],[c,d]] 为任意整数矩阵。如果 C_k U=U D_k，则第一行的两个方程强制

$$c=2k((k+1)b-a),\qquad d=2(a-kb).$$

因此

$$\det U=2\bigl[a(a-kb)-kb((k+1)b-a)\bigr]$$

一定为偶数。特别地，不存在行列式为 ±1 的整数交织子。这个结论覆盖任意整数 U、任意 k，包括 k=0；与 TR.3 联立时取 k>0。

结论：完整的正时间返回商基数序列，无法确定这个类别中的整数共轭类。增加观测时间不会消除此处的信息损失；需要增加观测的结构类型。

Lean：`intertwiner_determinant_even`、`spectrum_does_not_determine_integral_conjugacy`。此处尚未将整数非共轭自动提升为未构造的三维流形不同胚。

### TR.5 从等谱障碍继续推导的精确目标

下一项应直接计算同一个 R(A,1) 的群结构，而非引入与矩阵没有证明关系的抽象群。候选坐标为

$$\pi_C(x,y)=y\pmod{4k},$$

$$\pi_D(x,y)=\bigl(x\pmod2,\; y-kx\pmod{2k}\bigr).$$

需证明每个映射满射且其核分别恰为 (C_k-I)Z²、(D_k-I)Z²。这样才能从第一同构定理得到循环群与乘积群的分类，并通过实际商上的湮灭子区别二者。更强的后续目标是在任意有限模数上给出共轭的准确判据，并保留矩阵诱导的返回作用。

这些目标属于经典 Bowen–Franks 理论内的完整可核验实例。研究价值在于刻画具体观察丢失了什么，并提供最少结构性修复；并不把“有无限数据”当成“足够识别”的替代条件。

### TR.6 文献边界与外部问题

[TR1] P. Martins Rodrigues; J. Sousa Ramos. *Bowen-Franks groups as conjugacy invariants for T^n automorphisms*. arXiv:math/0303185 (2003). https://arxiv.org/abs/math/0303185 。广义 BF 群及拓扑共轭背景；本节采用列向量，与原文行向量约定区分。

[TR2] L. F. Bakker; P. Martins Rodrigues. *Generalized Bowen-Franks Groups and Profinite Conjugacy for Hyperbolic Toral Automorphisms*. arXiv:2207.00922v1 (2022). https://arxiv.org/abs/2207.00922 。论文已给出 principal BF R-modules 对相似双曲环面自同构 profinite 共轭的完整性结论。不能将它重列为未解问题，也不能把 R-module 改为基数或无标记阿贝尔群后沿用结论。

[TR3] X. Xu. *Profinite almost rigidity in 3-manifolds*. Advances in Mathematics 480 (2025), 110505; arXiv:2410.16002v4. https://arxiv.org/abs/2410.16002 。研究 profinite completion 对紧致可定向、空或环面边界三维流形的有限歧义识别。该结果与本节的标量返回序列不是相同数据。

[TR4] X. Xu. *Profinite rigidity in lattices of PSL(2,C)*. arXiv:2608.07350v1，2026-08-07. https://arxiv.org/abs/2608.07350 。本轮新检索到的预印本摘要声称证明全部 PSL(2,C) 格在该类别内的 profinite 刚性。尚未取得全文审阅或独立认可证据，故不把它当作已核定的 Lean 依赖；但足以阻止沿用旧文献中“该一般猜想尚无人提出证明”的口径。

[TR5] A. Klukowski. *Congruence Subgroup Property for nilpotent groups and subsurface subgroups of Mapping Class Groups*. arXiv:2411.06867v2 (2024)，Conjectures 1、13，Definition 3、Lemma 14. https://arxiv.org/html/2411.06867v2 。外部目标是高亏格映射类群 CSP，以及其简单闭曲线轨道的合同子群控制：给定有限指数 Gamma 与曲线 alpha，构造合同子群 Delta 使 Delta.alpha 包含于 Gamma.alpha。检索未发现该全称轨道结论已解决的来源；此为有界检索结论，不是穷尽优先权证明。本节的环面线性实例不属于亏格至少 3 的证明，也没有闭合这个猜想。

面向该外部目标，后续必须保留真实群作用、有限特征商与曲线轨道。仅靠二维阿贝尔化、相同迹、相同返回计数都没有足够信息。可先形式化 TR5 的已知组合引理作为真实消费者的基础，再推进明确受限的曲线轨道分离情形。若仅完成线性校准，应据实报告其范围，不把它计作 CSP 或庞加莱定理的解决。


### TR.7 实际返回群的结构恢复

TR.5 的核与满射目标现有对应 Lean 证明脚本，位于 `ToralReturnModuleStructure.lean`，并配套同名 Scribe。原返回模定义直接复用，不更换载体。

对任意 k≥0，pi_C 满射，其核等于 (C_k-I)Z²。若 y=4ka，则 (a,x-4ka) 是 (x,y) 的原像。pi_D 同样满射；给定两个剩余类的整数代表 a,b，可取 (a,b+ka)。若 (x,y) 位于 pi_D 的核，写 x=2a、y-kx=2kb，则 (b,a-kb) 是其在 D_k-I 下的原像。这同时证明两项像与核的双向包含。

第一同构定理因此在同一个实际商上给出

$$R(C_k,1)\cong\mathbb Z/(4k),\qquad
R(D_k,1)\cong\mathbb Z/2\times\mathbb Z/(2k).$$

k=0 也纳入分类：按 ZMod 0=Z 的约定，左边对应 Z，右边对应 Z/2×Z。有限性及以下分离结论取 k>0。

第二个商的每个元素都被 2k 湮灭。第一个商中，将剩余类 1 经构造出的同构逆像拉回，得到不被 2k 湮灭的实际商元素；否则 4k 整除 2k，与正 k 矛盾。于是不存在两个返回商之间的加法同构。

联合 TR.3，得到无界参数、全部正时间的结论：两个系统的所有返回模基数相同，单个时间的群结构却已足够区分这两个备选。这里的附加信息是同一个原对象上的湮灭性质，未定义人为标签或外加分类分数。

主要声明：`companion_image_eq_kernel`、`balanced_image_eq_kernel`、`one_step_return_module_classification`、`balanced_return_annihilated`、`companion_return_not_annihilated`、`one_step_return_modules_not_isomorphic`、`scalar_spectrum_and_structural_separation`。

本组继续停留在普通证明与候选 Lean 源码层，未宣称已执行内核。该结构恢复是指定校准族的完整分类，不推广为任意环面自同构的单步分类。矩阵 P_k 的行列式提示下一项可证明的问题：在所有模数中，2 是否是唯一检测这一共轭差异的素数？应在实际 ZMod 作用上构造可逆交织子，并证明偶数模数的精确障碍。

### TR.8 完整交织子范数与精确模数判据

TR.7 提出的素数定位现在有全称证明脚本 `ToralReturnPrimeTwoCriterion.lean` 及对应 Scribe。系数从原整数矩阵经标准环同态输运，未引入一个只在名称上对应原系统的新模型。

对任意交换环 R、自然数 k，所有满足 C_k U=U D_k 的矩阵都恰好具有形式

$$U(a,b)=\begin{pmatrix}a&b\\2k((k+1)b-a)&2(a-kb)\end{pmatrix},\qquad a,b\in R.$$

证明的正向来自两个第一行方程；反向将该表达式代入四个矩阵元即可。推导不除以 2，因此在特征 2 中也成立。随即有精确恒等式

$$\det U(a,b)=2\bigl(a^2-k(k+1)b^2\bigr).$$

该公式把偶性障碍提升为二次范数说明。整数情形，非零交织子的格指数受这个范数控制；a=1、b=0 实现行列式 2。这里的“非零”应精确理解为行列式非零，单纯非零矩阵仍可能奇异。对应二次域随 k 变化，k=1 给出 Q(sqrt(2))。

在 ZMod(m) 上，用存在 P,Q 满足 PQ=QP=I 且 C_k P=P D_k 定义实际可逆矩阵共轭。对所有 k,m≥0：

$$C_k\text{ 与 }D_k\text{ 在 }\mathbb Z/m\text{ 上共轭}\quad\Longleftrightarrow\quad m\text{ 为奇数}.$$

充分性：写 m=2r+1，令 u=-r mod m，则 2u=1。取

$$P=\begin{pmatrix}1&0\\-2k&2\end{pmatrix},\qquad
Q=\begin{pmatrix}1&0\\k&u\end{pmatrix}.$$

直接乘法证明 PQ=QP=I 及 C_kP=PD_k。

必要性：若 2 整除 m，标准环同态 ZMod(m)→ZMod(2) 存在。任何假设的可逆交织子都必须满足 det(P)det(Q)=1。将范数公式代入再通过该同态，左侧为 0，右侧为 1，矛盾。m=0 对应整数环，亦在排除范围；m=1 为零环，满足奇数侧结论。

主要声明：`intertwiner_normal_form`、`intertwiner_quadratic_norm`、`modular_conjugacy_iff_odd`。

本族的结论非常具体：所有正时间返回商基数相同；一步返回群结构已可区分；所有奇数模数的可逆线性观察仍等价；模 2 足以检测差异。无须增加时间长度，也无须提高奇素数精度。该结论只针对已定义的族，并不推广为一般局部到整体共轭判定。

### TR.9 此后真正需要闭合的对象接口

源稿继续维持“普通数学证明及候选 Lean 脚本，未执行内核或 Scribe 编译”的层级。三个阶段实际进行了符号恒等式、整数 Smith 数据、有限模矩阵与显式逆矩阵的诊断；有限诊断不替代文件中全部参数的证明。

下一个优先任务是建立实际环面固定点与原返回模的对应。设 M=A^n-I 在实向量空间可逆，固定点群是 M^{-1}Z²/Z²。其候选同构为

$$[x]\longmapsto[Mx]\quad\text{从}\quad M^{-1}\mathbb Z^2/\mathbb Z^2\quad\text{到}\quad\mathbb Z^2/M\mathbb Z^2.$$

要完成该桥，须在真实商拓扑或 AddCircle² 状态空间上构造 A 的作用，证明固定点对象正好是左侧群，证明同构良定义、满射、单射，最后消费本节已有基数和结构定理。该对应属于经典数学，不能作为新的开放问题解决；但它是把本轮算术结果称作环面周期点结果前不可跳过的一步。

随后可以保留返回自同构及覆盖层间的作用，研究具有真正 R-module 标记的广义 BF 系统。TR2 已有的完备性定理应作为复用目标，其作用域和相似性前提必须保留。对实际三维映射环面，还需先构造基本群与同调接口，不能从某个整数矩阵的非共轭直接跳到一般三维几何结论。

外部未闭合方向维持 TR5 的高亏格映射类群 CSP 与曲线轨道合同控制。今后若尝试具体受限情形，必须增加非阿贝尔基本群的有限特征商、真实曲线轨道及已知 CSP 组合定理。这里已经证明的二维线性例子用于测量观察数据的不足及修复，尚未构成该高亏格猜想的一个证明步骤。研究推进应以能实际消费的定理依赖为依据，不以共同名称或主题相似性计数。
