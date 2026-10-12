# Auric FIB ATOM：对称混合变化、路径缺陷与 Fibonacci 隐藏层级

## 参考输入、来源与读法

**开放参考输入，不是数学或物理真源。** 本卷完整保留用户提供的第六份、共两部分的混合来源稿件。原作者、原始生成模型和各段贡献者未知；不把它归给本卷编辑者。来源的“当前”“最新”“这一轮”“机器检查”“可证明版本”“可以冻结”等表述均作为来源快照中的自述保留，不表示本卷对当前项目状态的认证。两部分中的断言、证明、例子、表格、重复总结和各自编号全部保留。

**适用顺序。** 下列独立的编者限定 Q1–Q14 是本卷引用原稿时的适用条件与纠正；与原稿的推断冲突时，限定明确优先。原稿中不满足这些条件的定理化、动力学、物理、生物学及优先权推断仅作为来源提出的主张保留，不能依其原措辞作为本卷结论。散文出版不增加 Lean 证明、冻结、覆盖、定理认证或新颖性认证。

**来源身份。** 完整输入为 2641 行 UTF-8 文本，SHA-256 为 `fd199b93a6987c1327b3d420baca22ffb177ef0d9ec3ecf52fae6ae483542100`。限定中的行号指这个原始输入；第一部分止于附接第二标题之前，第二部分从该标题开始。第一部分的“定理一”至“定理四”与第二部分的“定理 1”至“定理 11”、候选 A–F 使用原来的局部编号，互不重编号。

**结构性整理。** 两个原题全文保留为二级标题，各部分主节、子节和证明标题按层级整理，仅改变标题标记。原输入将第二标题接在第一部分最后一句 `这两者共同组成了“只有变化”的可证明版本。` 之后；本卷只在句末与第二标题间插入空行，使第二标题独立。行内数学外壳由 `\(...\)` 改为 `$...$`（含字面星号时使用美元号加反引号），块数学外壳由 `\[...\]` 改为 `math` 围栏；全部 LaTeX 公式载荷保持原字节与顺序，包括独行等号。正文措辞、原有公共链接、表格内容和重复段落不作改写，没有替换来源引用。

**编辑与证据边界。** 编辑遵循 `formal-thinking-and-answer` 的条件与证据分离原则及 `theory-volume-template` 的理论卷写法。采用已提供的来源专项研究限定，并补充下列有界文献定位；不另设共识席。原稿的数学应用保留为普通散文，本文没有当前 Lean 编译或 kernel 核验；引用不可自动填补动作实现、记录完备性、统计取得或物理对应的证明义务。

## 编者限定（优先于冲突的来源推断）

### Q1：共同线性载体与分解唯一性的准确对象

对应第一部分 §一、定理一（原行 32–156），§三、定理三及 §八；第二部分 §§九–十。

固定一个实或复的带符号状态律向量空间 $H$，取 $U_a,U_b\in\operatorname{End}(H)$，以及共同线性读出 $R:H\to Y$。更一般的系数域须使 $2$ 可逆。概率单纯形本身不是向量空间。确定性状态映射用概率律推前得到线性算子，随机核延拓到带符号律；这不意味着任意概率向量更新都线性。不同输出或时钟载体的联合核必须先给出共同载体延拓，才有 $U-I$ 和复合。归一化后验、分支条件化及任意非线性更新不能直接代入这些线性证明。

唯一性针对整个有序对双线性族 $B(X,Y)=XY$ 在参数交换下的分解。令 $(\tau B)(X,Y)=B(Y,X)$，则 $\tau^2=I$，且

$$
\Pi_\pm=\frac{I\pm\tau}{2},\qquad
\Pi_\pm^2=\Pi_\pm,\qquad
\Pi_+\Pi_-=0,\qquad
\Pi_++\Pi_-=I.
$$

因此 $S=\Pi_+B$、$H_{\mathrm{pair}}=\Pi_-B$ 给出参数交换时唯一的对称与反对称部分，评价于 $(D_a,D_b)$ 才得到原稿的 $S_{a,b},H_{a,b}$。动作标签无需有线性结构；保留整个标签对族即可。该结论不保证一个孤立固定乘积的任意拆分唯一，也不是矩阵转置、自伴或斜自伴分解，不保证正性。Conrad《Bilinear Forms》定理 1.7 给出标准标量双线性形式版本；这里的算子值族用同一交换投影论证。

### Q2：带符号混合差不等于实际两步响应

对应第一部分 §§一–三（原行 47–93、513–608）及定理四（1038–1058）。

$D_a$、$D_aD_b$、$S_{a,b}$ 和 $H_{a,b}$ 是带符号响应算子，不是随机转移或概率。保质量的 $U$ 满足 $(U-I)p$ 总质量为零；分支子核还可以改变总质量。明确区分

$$
D_aD_b=U_aU_b-U_a-U_b+I
$$

这个四实验混合差与实际复合 $U_aU_b$。写 $s=R(S_{a,b}d)$、$h=R(H_{a,b}d)$，恒等式是

$$
R(U_aU_b d)=R(d)+R(D_a d)+R(D_b d)+s+h.
$$

只有零阶和一阶项都消失，或用同一初始律、共同读口和实际合法控制作明确校准扣除，实际响应才能等同于 $s+h$。两项二阶响应为零并不排除实际两步读出经低阶项可见；混合差非零也不自动说明某个实际顺序的净响应非零。四项代数减法不能赋予重置、复制或未执行分支的操作权。$R$ 必须作用于带符号延拓；分支归一化和条件化的非线性另需论证。

### Q3：静态乘法、seam 泛函与动态次序缺陷的桥梁

对应第一部分 §二（原行 227–319）、§五（769–776）及结论（1144–1154）；第二部分 §十（2314–2371）。

逐点乘法 $M_xM_y=M_{xy}$、标量泛函 $J(f)=f(13)-f(1)-f(3)+f(\varnothing)$、双线性形式 $\Omega(f,g)=J(fg)$ 与任意动态变化的反对易乘积是不同类型的对象。同用“混合”或“seam”不构成对象相等。明确的静态桥只是

$$
M_xM_y1=xy,\qquad \kappa=\langle p,M_xM_y1\rangle.
$$

乘法算子作用于状态函数，$U_a,U_b$ 作用于带符号状态律；识别两者需要明确的对偶、来源/载体对应、实际动作和读出桥。静态例子有交换的乘法算子及非零联合观测，不能提供任意 $U_a,U_b$，也不认证物理曲率。交换子是带符号次序缺陷；称为闭路 holonomy 还必须指定相容合法路径、输运、闭路构造及所需可逆性，不能仅靠加性交换子命名。

### Q4：两顺序斜率、相消与记忆边界

对应第一部分 §三（原行 480–509、612–648）、定理四（1002–1058）；第二部分 §十（2333–2347）。

两种混合顺序沿隐藏方向的斜率分别为 $s+h$ 和 $s-h$。指定顺序敏感当且仅当其对应斜率非零；$s=-h\ne0$ 会使第一顺序相消。在两个测量都合法、校准、读口相同时，至少一个斜率非零当且仅当 $(s,h)\ne(0,0)$，两顺序对比为 $2h$。在固定模型与非退化五态纤维上，变化只有

$$
t\longmapsto t(s+h,s-h),
$$

秩至多一；两项是已知系数乘同一个隐藏标量，不是两个独立隐藏状态坐标。增加预测记忆要有实际增广或历史相关载体，不能由非交换自动推出。

具体反例使用状态顺序 $(0,2,3,5,25)$，确定性映射像列表分别为 $U_a:(2,2,3,5,5)$、$U_b:(0,2,3,2,25)$，并用线性推前作用于律。取 $d=(1,-1,0,-1,1)$、$v=e_5-e_2$、$R(q)=q_5$，则 $U_a d=0$、$D_b d=v$、$D_a v=0$。因此 $D_aD_b d=0$、$D_bD_a d=-v$，给出 $s=-1/2$、$h=1/2$，但 $R U_aU_b d=1$。这是抽象五态随机核反例，不声称是已取得的 native FIB 操作。

非零算子交换子只说明存在某个输入见证，可以湮灭选定 $d$ 或初始 $p$，也可以被 $R$ 湮灭；必须检查实际测试的 $R[U_a,U_b]d$ 或 $R[U_a,U_b]p$ 非零。交换性与某次边际读数相同彼此都不能推出。延迟可见也不需要非交换：只用一个确定性动作，像列表 $U:(3,3,3,5,0)$，取 $R(q)=q_3$，有 $Ud=e_0-e_5$、$U^2d=e_3-e_5$，所以 $Rd=RUd=0$、$RU^2d=1$。全部动作词都是 $U$ 的幂，彼此交换。

### Q5：Novak 反例的实际不可变来源范围

对应第一部分引言（原行 5–7）、§五（717–747）；第二部分引言（1172–1174）和 §十。

`96e0ba0` 只用来定位 Krishna Conjecture 4.3 的特定 $C^\ast$-代数值 Novak 正性反驳。不可变 Lean 来源中的声明为 `D5.S3.Quantum.Algebra.CStarNovak.result : ¬ claim`；`claim` 涉及幺复 $C^\ast$-代数及所述相容序，不是“边际性质不能推出交换”的一般定理。Krishna 原文 §2 使用左模正性约定，Conjecture 4.3 取 $n,d\ge2$、自伴输入和有序余弦因子乘积减去 $1/n$ 的矩阵正性；交换代数的 Theorem 4.4 在此反驳之外。

见证代数是 $M_2(\mathbb C)$，外层参数是 $n=3,d=2$，使用三个自伴矩阵和重复坐标，不是两态 FIB 转移。标量平方差给出原始 `ncos` 的 $I$ 或 $-I$，归一化因子 $(I+\mathrm{ncos})/2$ 才是 $I$ 或 $0$。三类非对角原始余弦为 $I,I,-I$，得到系数矩阵

$$
\frac13
\begin{pmatrix}2&2&2\\2&2&-1\\2&-1&2\end{pmatrix}\otimes I,
$$

在 $(-2,1,1)\otimes I$ 上二次型为 $-2I$。这些事实来自提供的指定不可变声明及证明阅读范围，不是本卷重新编译的结果。该数学反例没有固定 FIB、随机动作、时钟或物理交换性桥，不能据它推断真实物理非交换性。

### Q6：取得核变化与固定有限载体的 horizon

对应第一部分 §四（原行 651–713）；第二部分 §九（2303–2310）。

`4da8b2e` 在同一个停止来源上改变安装的取得核 $B_\theta=C+\theta zb^{\mathsf T}$，固定相应发射、其他取得核和粗接口；不是在一套固定 FIB 动力学内改变 $\kappa$。其 $q\ge3$ 构造每个 phase 有 $N=2q+2$ 个私有标签，配置后的 $p$ 前缀在前 $N-1$ 次 Reads 相同，第 $N$ 次有一个完成词分离；要求任意有限延迟时，状态规模随之增长。Proposition 6.2 的共同程序仍增加了实际内部符号配置。迁移到原来的固定 $d$ 需另证实现。

模型比较可以经成熟的线性直和桥表示为方向比较：共享字母和读数合同的两套有限表示取 $M_o=\operatorname{diag}(M_o^+,M_o^-)$、行向量 $q=(p^+,-p^-)$ 和末列 $g=(g^+,g^-)^{\mathsf T}$，则 $qM_wg$ 正好是两模型读数之差。这增加载体维数，不保留“还是原五态 $d$”。

对于固定 $m$ 维、时间齐次线性仪器，固定全部输出分辨子核与末端测试空间 $V_0$，令 $r=\dim V_0$，并定义

$$
V_{j+1}=V_j+\sum_a U_a^*V_j.
$$

如果某一步相等，$V_j$ 已对所有 $`U_a^*`$ 不变，后来全部相等；否则维数严格增长，所以最迟在 $m-r$ 步稳定，每个可见方向都有长度至多 $m-r$ 的词/末端测试见证。完整五态质量加三均值测试为 $m=5,r=4$，一步要么暴露缺失方向，要么测试空间已不变；只有记录概率、$V_0=\operatorname{span}\{1\}$ 时对应上界为四步。此界要求合法性、所有输出、guard、Stop 和实际记忆都已编码在同一个载体。任意另设的逐词 $R_w$、变化核、无限/变化载体或未编码的合法性不满足此前提。有限前缀不同于全部未来的现象不能不加这些条件地用于固定五态任意长延迟，非交换也不是延迟可见的必要条件。

### Q7：仿射观测、线性核与边界纤维

对应第一部分定理三（原行 515–527）、定理四（984–999）；第二部分 §四（1524–1643）、§九（2221–2227）和候选 D（2544–2551）。

归一化概率上的 $T_1(p)=(1,\mu_1,\ldots,\mu_n)$ 是仿射写法，本身没有所写的线性核。所有核及隐藏差异应指质量增广延拓

$$
\widetilde T_1(q)=
\left(\sum_Iq_I,\sum_Iq_Ix_1(I),\ldots,\sum_Iq_Ix_n(I)\right)
\quad(q\in\mathbb R^{\Sigma_n}).
$$

三个均值的 $P$ 在整个 $\mathbb R^5$ 上核为二维；$\operatorname{span}\{d\}$ 是它在质量零差异上的核，或质量增广 $P$ 的核。定理四写出的 $P:H\to\mathbb R^4$ 须明确为这一质量增广映射。

秩为 $n+1$ 给出全局隐藏维数 $\operatorname{Fib}_{n+2}-n-1$；包含全支撑律的纤维达到该维数。只有边界点的纤维可能更小或单点。$n\ge3$ 指全局非单射，不是每个观测均值都含歧义：$n=3$ 时 $X=Y=Z=0$ 仅有 $\kappa=0$。若实际可取得律仅是单纯形子集，还须限制到实际可行差异；这些维数不是物理实体数、记忆比特数或样本量，也不证明所有抽象状态律都有 native FIB 实现。

### Q8：自然数域、完整 monomial 基与成熟数学应用

对应第二部分 §§一–四（原行 1180–1643）、§七和定理八（1989–2101），以及候选 A–D。

取 $n,r\in\mathbb N_0$，其中 $n$ 是位置数，不是合法状态数。$\Sigma_0=\{\varnothing\}$、$a_0=1$、$a_1=2$、$h_0=0$，且 $\dim V_0^{(r)}=1$。递推 $a_n=a_{n-1}+a_{n-2}$ 只用于 $n\ge2$。

独立集计数为

$$
N(n,k)=\begin{cases}
\binom{n-k+1}{k},&0\le k\le\lfloor(n+1)/2\rfloor,\\
0,&\text{其余大小 }k.
\end{cases}
$$

不在可用范围隐含负上指标的二项式。$i_j\mapsto i_j-(j-1)$ 给出不相邻位置与普通子集的双射。故

$$
\dim V_n^{(r)}=\sum_{k=0}^{\min(r,\lfloor(n+1)/2\rfloor)}\binom{n-k+1}{k}.
$$

$r\ge\lfloor(n+1)/2\rfloor$ 时单项式空间已完整。相应 $h_{n,r}$ 是全局线性核维数，在全支撑纤维达到；边界限制仍适用。

按包含关系排序，评价矩阵 $x_A(I)=\mathbf1_{A\subseteq I}$ 为对角线全一的三角矩阵，故这些单项式成基。每个区间 $[A,I]$ 是 Boolean 区间，Möbius 系数为 $(-1)^{|I|-|A|}$，既给出原稿的函数展开，也给出概率反演

$$
p_I=\sum_{J\supseteq I}(-1)^{|J|-|I|}\kappa_J,\qquad
\kappa_J=\sum_{I\supseteq J}p_I.
$$

路径独立集计数、向下封闭集合的包含关系/Möbius 反演、独立集 monomial 基及 Fibonacci/Zeckendorf 唯一性均为成熟数学。Rota 原文 §3 是反演的经典定位；本稿给出其应用，不是已证明的优先权或新增形式定理。

### Q9：补全最大权重归纳与编码范围

对应第二部分 §六、定理七（原行 1863–1941）及候选 E。

令 $w_i=\operatorname{Fib}_{i+2}$，最大合法权重和记为 $M_r$。完整初值是 $M_0=0<w_1=2$、$M_1=2<w_2=3$；对 $r\ge2$，

$$
M_r=\max(M_{r-1},M_{r-2}+w_r).
$$

归纳给出 $M_{r-1}<w_r<w_{r+1}$，以及

$$
M_{r-2}+w_r<w_{r-1}+w_r=w_{r+1}.
$$

两候选都小于 $w_{r+1}$，所以 $M_r<w_{r+1}$，包括最大对称差位置 $m=1$ 所需的 $M_0<w_1$。

还可明确最大值：令奇数 $r$ 的 $c_r=1$、偶数的 $c_r=2$，则 $M_r=\operatorname{Fib}_{r+3}-c_r$，包含 $r=0$。初值如上；对 $r\ge2$，第二候选为 $\operatorname{Fib}_{r+3}-c_r$，减去第一候选为 $\operatorname{Fib}_{r+1}+c_{r-1}-c_r>0$，故取第二候选即完成归纳。

对不同合法集合，取最大对称差位置 $m$，较小位置一侧最多 $M_{m-1}<w_m$，不能抵消另一侧的位置 $m$，所以加权和单射。这里权重从 $2$ 开始，而经典 Zeckendorf 使用 $1,2,\ldots$；可复用唯一性，不能搬用全自然数表示存在性，本篇编码不能表示 $1$。所称单射是在合法子集上，不是到全部自然数的满射。完整加权输出律可恢复 $p$，其均值或一次样本不能自动恢复未知律。

### Q10：共同带符号测度与可识别条件

对应第二部分 §八（原行 2105–2205），特别是定理九。

所有 $K_I$ 是同一个可测等待/输出空间上固定已知的概率核；全部 $\Delta_AK$ 和 Möbius 恒等式在共同的有限带符号测度空间内成立。基项 $C_K^{(0)}$ 可以是带符号测度，不必是概率律；只有可行混合 $C_K(p)$ 必须是概率律。定理九中“测度除以测度”未定义，以此替代其反解步骤：非退化可行 $\kappa$ 区间、固定已知核及精确混合律下，写 $C_K(p)=A+\kappa B$；$B\ne0$ 时存在可测事件 $E$ 使 $B(E)\ne0$，于是

$$
\kappa=\frac{C_K(p)(E)-A(E)}{B(E)}.
$$

这是标量反解。若 $B=0$，同一非退化纤维上全部律观察相同；若纤维单点，$\kappa$ 已经确定，即使 $B=0$ 也不用再识别。公式要求精确律或精确事件概率，不是单个等待样本或有限噪声样本的精确恢复。

多维隐藏空间不能只检查每个 $\Delta_AK\ne0$。需 $q\mapsto\sum_Iq_IK_I$ 在低阶矩固定的可行差异上单射；包含全支撑律时等价于剩余带符号测度系数映射在整个隐藏空间单射，即相应系数线性无关。不同非零系数可以相消。

明确例子取 $n=4$，$K_I$ 为 $\{0,1\}$ 上 Bernoulli 律，成功概率为 $1/4+(x_{13}(I)+x_{14}(I)+x_{24}(I))/8$。三个二阶系数都是 $(\delta_1-\delta_0)/8\ne0$，观察只含 $\kappa_{13}+\kappa_{14}+\kappa_{24}$。取 $q=e_4-e_3+e_{13}-e_{14}$，则 $\widetilde T_1q=0$、$\sum_Iq_IK_I=0$。均匀八态律 $p$ 附近，$0<|\varepsilon|<1/8$ 的 $p+\varepsilon q$ 合法且与 $p$ 不可区分。

### Q11：完整合法观测族、特定差异与历史相容性

对应第一部分 §四（原行 670–677）、定理四（1058）；第二部分 §九（2213–2310）、§十二（2504–2510）和候选 F。

固定一个模型、原始来源和共同实现，为所有 $U_w$、线性 $R_w$ 指定完整合法控制合同。包括实际控制、输出标签/末端事件、active/pending/delivered Stop，以及任务所需的非完成结果；选取测试子族只证明该子族的盲性。实值测试给期望，值在 $[0,1]$ 的测试才直接给概率。记录不一定能从末端状态恢复：例如先输出初始状态标签，再把内部状态重置为 $0$，末端 $Uq=0$ 仍不抹除已输出记录。要用 $O_w=R_wU_w$ 表示完整记录，须把实际记录编码进载体。

对实际允许的律族 $\mathcal C$，定义

$$
D_{\mathcal C}=\{p'-p:p,p'\in\mathcal C,\ \widetilde T_1p'=\widetilde T_1p\}.
$$

准确的律级可识别判据是

$$
D_{\mathcal C}\cap\bigcap_w\ker(O_w)=\{0\}.
$$

只有允许整个单纯形、在全支撑点沿任意隐藏方向作小扰动时，才能把实际可行差异替换为全局 $\ker\widetilde T_1$。这判定精确观察律族的单射，不是单条随机记录或有限噪声样本的精确恢复，也不自动给出无需重置的通用实验或可执行记忆更新。

共同核非零只说明某些歧义存在；特定射线或差异 $q$ 永久盲，当且仅当该可行差异在施加当前观测后仍属于每一个合法未来测试的核。恢复是分离差异，不是抹去差异。$U_wq=0$ 只针对指定的当前状态载体，不删除已输出历史或未建模环境差异。

有限历史律须具有投影相容性，Stop 用明确终止/墓地标签及吸收延拓编码。在共同标准 Borel 路径空间、其 $\sigma$-代数由有限柱集生成时，所有有限律相等由 $\pi$–$\lambda$ 唯一性推出无限历史律相等；没有额外自动可见的“纯无限阶差异”。不相容历史核、漏记停止事件或柱集外附加信息不在这个结论内。

某条更长非零词只是见证，不自动是最短词；分辨阶为对全部合法词与测试取最小长度，无见证时为 $\infty$，固定有限载体的适用上界见 Q6。

### Q12：等待概率核不是加性时钟增量

对应第一部分 §六.1（原行 780–813）；第二部分 §十一（2375–2454）。

原始概率等待核不是标量增量；未指定标量/加性响应映射前，$K\sim T(v)-T(u)$、对 $K$ 的积分或核 holonomy 均未定义。可选在依赖已明确的路径律下取有限均值并证明可加性，或另给联合路径律复合；不能从边际核自动获得复合依赖。概率核质量为一，将其反向取负会离开概率锥，沿正向周期相加质量也不为零。

势定理适用于底层图每个连通分量上的实值（或交换群值）加性边增量，形式反向指定为负，并测试全部底层带符号闭路。必要性由望远镜相消；充分性由根到顶点的任意底层路径积分定义势，闭路条件保证路径无关。势在每个连通分量相差一个常数。形式反向不等于实际合法的反向等待过程。

只查有向因果周期不够，尤其 DAG 上没有有向周期。菱形 DAG 两条起终点相同的路径累计量可以为 $2$ 与 $3$，无有向环却无实现这些增量的势，同时仍有按层递增的全局时标。非零带符号环量只排除实现该组指定增量的势，不排除任何全局坐标时间、拓扑排序或其他场；恢复的势也不必是物理时间。

### Q13：信息比较与可维护性需要明确合同

对应第一部分 §七（原行 941–976）；第二部分 §十二（2458–2502）。

断言两条信息不等式前，须定义目标族、可恢复性泛函或观察偏序及其假设。数据处理只适用于同一目标的明确通道链：若 $E'=L\circ E$，后处理 $L$ 不依赖未知目标，则固定先验与损益下，$E'$ 的最优决策价值不超过 $E$，因为任意 $E'$ 策略都可在 $E$ 后先执行 $L$ 模拟。固定粗观测 $O$ 后的任意 $U$ 不自动满足此前提，Q4 的交换延迟例即能让原先隐藏方向可见。

扩展观测至少不减，要求在同一载体上从新观测能恢复旧观测；严格改进还需对所选泛函与律有相关的新增分离。添常量或重复读数不保证严格改进。$RUd\ne0$ 只是律级灵敏度，不是生命定理。

一次 $U_ap\in K$ 不证明无限维持。必须指定合法、仅依赖实际观测的策略、全部可能后继、反馈/记忆及不变安全或 viability 条件，使策略在每次合法后继下仍保持可维护区。能量、实现及有限样本性能仍是独立义务；增加可识别性不自动满足它们。

### Q14：本体解释、几何候选与六项冻结建议

对应第一部分 §§五–七（原行 749–976）、结论（1126–1154）；第二部分 §§十一–十三及结论（2375–2641）。

单一关系场、变化优先本体、局部时钟解释、因果几何、物质/辐射分解、生物解释及将漂移 $G$ 作为引力候选均保留为来源提议。漂移 $G(e)=\sum_{e'}\Pr(e'\mid e)\delta(e,e')$ 需指定概率转移律，所有增量属于共同线性空间且可积；它不是引力定理，梯度、时钟关系、物理维数及作用桥另需结构与证据。

非负路径代价的有向路径下确界给出扩展有向代价，允许不可达时为 $\infty$；成为有限度量还需可达性、对称、分离等条件。三个占据坐标不证明三维物理空间。矩阵值 $\Phi$ 及其 $U_a$ 作用需要载体/作用定义，不能从统一名称取得。

第二部分原有六项 A–F 全部保留为来源建议；其计数、基、维数、seam、编码和未来可识别性分别受 Q7–Q11 的域、质量增广、可行差异与精确律条件限制。原文“最值得冻结”“目前可以冻结”等不构成本卷冻结请求或已冻结状态。正文最终“已经证明”的泛化句只作为来源自述，不能把上述散文应用升级为当前形式证明、新颖性、动力学等价、探测器实现、物理或生物认证。

## 完整来源正文的两部分

以下依原始顺序保留两部分；每部分以原题全文开头，所有编号属于该部分。

## Auric FIB ATOM 续篇：隐藏 seam 是对称混合变化，动态因果则产生反对称路径缺陷

这一轮最新项目状态出现了一个很有价值的变化：

- [`96e0ba0`](https://github.com/the-omega-institute/trureturing/commit/96e0ba0ecebaa879b1e01d4789272761d506186c) 新增了一个机器检查的 $2\times2$ 复矩阵反例，用来否定一个过强的 $C^\ast$-代数 Novak 猜想。它直接说明：一旦变化对象是算子，不能默认所有变化都彼此交换。
- [`4da8b2e`](https://github.com/the-omega-institute/trureturing/commit/4da8b2e9c9c6439548fbbc5bea42df65ec2ae2ba) 继续推进取得核的盲方向：有限校准和有限前缀相同，不等于完整未来律相同。
- [`60ebb51`](https://github.com/the-omega-institute/trureturing/commit/60ebb51c87e6496e0cab67c899c3b687ef8fd001) 则把 AURIC FIB 的静态 seam、输出仪器和未来闭包放在同一理论框架中。

仓库公开定位本身也是“可检查的定义、计算和证明”，而不是只依靠接口绑定或概念命名。[github.com](https://github.com/the-omega-institute/trureturing?utm_source=chatgpt.com)

这使前面“只有一个场，其他都是变化”的观点可以进一步严格化：

```math
\boxed{
\text{FIB 的静态隐藏量 }\kappa
\text{ 是对称混合变化；}
}
```

```math
\boxed{
\text{动态路径中的新隐藏量则来自变化算子的非交换性。}
}
```

这两者都属于“变化”，但它们不是同一个二阶对象。

---

### 一、统一变化代数

令 $\mathcal H$ 为局部状态律的线性空间。

对每个合法局部动作 $a$，定义变化转移：

```math
U_a:\mathcal H\longrightarrow\mathcal H.
```

这里 $U_a$ 可以是：

- 确定状态转移；
- 随机转移核；
- 输出分支的子核；
- 局部时钟和状态的联合核。

定义变化算子：

```math
D_a=U_a-I.
```

因此：

```math
D_a p
```

表示状态律 $p$ 在动作 $a$ 下相对于自身发生的变化。

对于两个动作 $a,b$，有：

```math
D_aD_b.
```

它描述先发生 $b$-变化，再发生 $a$-变化的二阶变化。

将它拆成对称部分与反对称部分：

```math
S_{a,b}
=
\frac12(D_aD_b+D_bD_a),
```

```math
H_{a,b}
=
\frac12(D_aD_b-D_bD_a).
```

其中：

- $S_{a,b}$：两个变化的对称混合；
- $H_{a,b}$：两个变化的次序缺陷，也就是离散 holonomy 或动态路径曲率。

于是恒有：

```math
\boxed{
D_aD_b=S_{a,b}+H_{a,b}.
}
```

---

#### 定理一：二阶变化分解定理

对任意两个变化算子 $D_a,D_b$，有唯一分解：

```math
D_aD_b
=
\frac12(D_aD_b+D_bD_a)
+
\frac12(D_aD_b-D_bD_a).
```

并且：

```math
S_{a,b}=S_{b,a},
```

```math
H_{a,b}=-H_{b,a}.
```

##### 证明

直接相加：

```math
S_{a,b}+H_{a,b}
=
\frac12(D_aD_b+D_bD_a)
+
\frac12(D_aD_b-D_bD_a)
=
D_aD_b.
```

交换 $a,b$：

```math
S_{b,a}
=
\frac12(D_bD_a+D_aD_b)
=
S_{a,b},
```

而：

```math
H_{b,a}
=
\frac12(D_bD_a-D_aD_b)
=
-H_{a,b}.
```

唯一性来自对称部分和反对称部分的直接投影分解。

证毕。

---

这个定理非常关键，因为它把两个容易混淆的结构分开了：

```math
\boxed{
\begin{aligned}
\text{静态联合关系}
&\sim \text{对称混合变化},\\
\text{动态路径依赖}
&\sim \text{反对称次序变化}.
\end{aligned}
}
```

FIB 五态中的 $\kappa$ 主要属于第一类。

最新非交换代数进展则提醒我们：动态转移一般不能假设属于第一类，第二类也必须单独检查。

---

### 二、FIB 五态中的 seam 是对称混合，不是交换子

仍然使用：

```math
F[\mathrm{null}]=\mathrm{null},
```

```math
F[1]=[2],
```

```math
F[2]=[3],
```

```math
F[3]=[5],
```

```math
F[1,3]=[2,5].
```

记：

```math
s_0=F[\mathrm{null}],
\qquad
s_1=F[1],
\qquad
s_2=F[2],
\qquad
s_3=F[3],
\qquad
s_{13}=F[1,3].
```

定义状态函数：

```math
x=\mathbf 1_{\{1\}},
\qquad
y=\mathbf 1_{\{3\}},
\qquad
z=\mathbf 1_{\{2\}}.
```

在静态状态函数代数中，乘法是逐点乘法，所以：

```math
xy=yx.
```

定义乘法算子：

```math
M_xf=xf,
\qquad
M_yf=yf.
```

那么：

```math
M_xM_y=M_yM_x=M_{xy}.
```

所以静态 FIB 代数中的交换子为：

```math
[M_x,M_y]
=
M_xM_y-M_yM_x
=
0.
```

但是对称乘积不为零：

```math
\frac12(M_xM_y+M_yM_x)=M_{xy}.
```

因此：

```math
\boxed{
\kappa=E[xy]
}
```

不是静态交换子，而是对称混合项的期望。

---

#### 定义：FIB 混合变化算子

对任意状态函数 $f$，定义端点混合变化：

```math
\Delta_{13}f
=
f(s_{13})-f(s_1)-f(s_3)+f(s_0).
```

这就是：

```math
\Delta_{13}f=J(f).
```

它衡量：

```math
\text{“两个端点同时发生”}
```

与：

```math
\text{“两个端点分别发生再相加”}
```

之间的差异。

当：

```math
\Delta_{13}f=0,
```

说明该读数对两个端点变化是可加的。

当：

```math
\Delta_{13}f\neq0,
```

说明读数中存在联合变化。

---

#### 定理二：FIB 五态的二阶变化分解

任意函数 $f:\Sigma\to\mathbb R$ 都能唯一写成：

```math
f
=
a_0+a_1x+a_2z+a_3y+\eta_{13}xy,
```

其中：

```math
a_0=f(s_0),
```

```math
a_1=f(s_1)-f(s_0),
```

```math
a_2=f(s_2)-f(s_0),
```

```math
a_3=f(s_3)-f(s_0),
```

```math
\eta_{13}
=
f(s_{13})-f(s_1)-f(s_3)+f(s_0).
```

并且：

```math
\eta_{13}=\Delta_{13}f.
```

##### 证明

令：

```math
g=a_0+a_1x+a_2z+a_3y+\eta_{13}xy.
```

在 $s_0,s_1,s_2,s_3$ 四个状态上，直接代入可得：

```math
g(s_i)=f(s_i)
\qquad
(i=0,1,2,3).
```

在 $s_{13}$ 上：

```math
\begin{aligned}
g(s_{13})
&=
a_0+a_1+a_3+\eta_{13}\\
&=
f(s_0)
+\bigl(f(s_1)-f(s_0)\bigr)
+\bigl(f(s_3)-f(s_0)\bigr)\\
&\quad+
\bigl(f(s_{13})-f(s_1)-f(s_3)+f(s_0)\bigr)\\
&=f(s_{13}).
\end{aligned}
```

所以 $g=f$。

唯一性来自：

```math
\{1,x,z,y,xy\}
```

在五个状态上的取值矩阵可逆。

证毕。

---

对于概率律：

```math
p=(p_0,p_1,p_2,p_3,p_{13}),
```

定义：

```math
X=p_1+p_{13},
\qquad
Y=p_3+p_{13},
\qquad
Z=p_2,
\qquad
\kappa=p_{13}.
```

于是：

```math
\boxed{
E[f]
=
a_0+a_1X+a_2Z+a_3Y+\eta_{13}\kappa.
}
```

这说明：

- $X,Y,Z$ 是一阶变化读数；
- $\eta_{13}$ 是读数对二阶混合变化的响应；
- $\kappa$ 是该二阶变化的状态强度。

因此：

```math
\boxed{
\kappa \text{ 不是第五个场，}
\quad
\kappa \text{ 是混合变化的共轭坐标。}
}
```

---

### 三、静态 seam 与动态 holonomy 必须区分

在静态 FIB 代数中：

```math
[M_x,M_y]=0,
```

但：

```math
M_xM_y=M_{xy}\neq0.
```

因此静态隐藏 seam 是：

```math
\boxed{
\text{对称混合存在，反对称路径缺陷不存在}.
}
```

但动态变化算子不一定是逐点乘法。

设 $U_a,U_b$ 是两个真实因果动作。即使它们在当前状态上分别产生相同的边缘读数，也可能有：

```math
U_aU_b\neq U_bU_a.
```

这时：

```math
H_{a,b}
=
\frac12[U_a,U_b]
\neq0.
```

这表示：

```math
\text{先发生 }a\text{ 再发生 }b
```

与：

```math
\text{先发生 }b\text{ 再发生 }a
```

得到的结果不同。

这是一种新的隐藏关系，它不是静态 $\kappa$，而是动态路径序关系。

---

#### 定理三：二阶隐藏响应定理

令：

```math
N=\ker P=\operatorname{span}\{d\},
```

其中：

```math
d=(1,-1,0,-1,1)
```

是当前三均值读数的隐藏方向。

设 $R$ 是一个未来读出。对两个动作 $a,b$，定义：

```math
\Sigma_{a,b}
=
R(S_{a,b}d),
```

```math
\mathcal H_{a,b}
=
R(H_{a,b}d).
```

则对于两个同一 $(X,Y,Z)$ 但参数不同的状态律：

```math
p_{\kappa'}-p_\kappa
=
(\kappa'-\kappa)d,
```

有：

```math
\boxed{
R(D_aD_b p_{\kappa'})
-
R(D_aD_b p_\kappa)
=
(\kappa'-\kappa)
\left(
\Sigma_{a,b}+\mathcal H_{a,b}
\right).
}
```

##### 证明

由：

```math
D_aD_b=S_{a,b}+H_{a,b},
```

以及：

```math
p_{\kappa'}-p_\kappa
=
(\kappa'-\kappa)d,
```

得到：

```math
\begin{aligned}
&R(D_aD_b p_{\kappa'})
-
R(D_aD_b p_\kappa)
\\
&=
R\bigl(D_aD_b(p_{\kappa'}-p_\kappa)\bigr)
\\
&=
(\kappa'-\kappa)R(D_aD_bd)
\\
&=
(\kappa'-\kappa)
R\bigl((S_{a,b}+H_{a,b})d\bigr)
\\
&=
(\kappa'-\kappa)
\left(
\Sigma_{a,b}+\mathcal H_{a,b}
\right).
\end{aligned}
```

证毕。

---

这个定理给出三种可能：

##### 1. 只存在静态联合变化

```math
\Sigma_{a,b}\neq0,
\qquad
\mathcal H_{a,b}=0.
```

此时 $\kappa$ 可由联合读出恢复，但路径次序本身不产生额外信息。

##### 2. 只存在动态路径缺陷

```math
\Sigma_{a,b}=0,
\qquad
\mathcal H_{a,b}\neq0.
```

此时单步边缘和静态联合读数都可能看不见隐藏关系，但动作次序会把它暴露出来。

##### 3. 两种结构同时存在

```math
\Sigma_{a,b}\neq0,
\qquad
\mathcal H_{a,b}\neq0.
```

此时未来读出同时包含：

- 状态联合信息；
- 路径次序信息。

因此，单独保留 $\kappa$ 可能还不够，还需要保存动态路径的 holonomy 坐标。

---

### 四、这解释了最新项目的“有限前缀盲方向”

在最新取得核盲方向构造中，有限前缀、有限配置数组和配对校准可以相同，但完整未来律仍在更晚的回流词上分离。

用当前记号表示，就是存在一族路径 $w$，使：

```math
R_wU_wd=0
```

对于所有短路径 $w$，但存在某条较长路径 $w_\ast$：

```math
R_{w_\ast}U_{w_\ast}d\neq0.
```

因此：

```math
\ell_\ast
=
\min\{
|w|:R_wU_wd\neq0
\}
```

是第一次暴露隐藏方向的未来深度。

这说明：

```math
\boxed{
\text{有限观测等价}
\neq
\text{完整因果律等价}.
}
```

更进一步，如果动态动作不交换，还可能有两个不同路径：

```math
w_1=ab,
\qquad
w_2=ba,
```

虽然它们包含同样的动作，却满足：

```math
R_{w_1}U_{w_1}d
\neq
R_{w_2}U_{w_2}d.
```

此时隐藏信息不仅依赖“发生了什么”，还依赖：

```math
\boxed{
\text{变化以什么顺序发生}.
}
```

这正是时间方向在变化优先理论中的更严格来源。

---

### 五、最新非交换代数进展对 FIB 的意义

最新的 [`96e0ba0`](https://github.com/the-omega-institute/trureturing/commit/96e0ba0ecebaa879b1e01d4789272761d506186c) 通过显式矩阵构造，机器检查地展示了一个算子值命题在 $2\times2$ 复矩阵中失败。

这里最值得迁移到 FIB 的不是该猜想本身，而是方法论：

```math
\boxed{
\text{只知道每个局部变化的边缘性质，}
\quad
\text{不能推出变化算子整体可交换。}
}
```

对 FIB 来说，这意味着必须区分：

```math
M_xM_y=M_yM_x
```

这一静态逐点代数事实，和：

```math
U_aU_b=U_bU_a
```

这一动态路径事实。

二者完全不同。

静态状态函数 $x,y$ 可以交换，但两个真实因果动作 $a,b$ 可能不交换。

因此统一场若要成为真正的算子值场，应当写成：

```math
\Phi:\mathcal E\longrightarrow\mathcal A,
```

其中 $\mathcal A$ 不一定是交换代数。

不同物理或观察概念都可以是：

```math
\Phi_\lambda=L_\lambda\Phi,
```

而不同变化是：

```math
D_a\Phi=(U_a-I)\Phi.
```

这时：

- “一个场”对应 $\Phi$；
- “不同场”是不同投影 $L_\lambda\Phi$；
- “不同力”是不同变化算子 $D_a$；
- “时间方向”是变化算子的可允许排列；
- “路径曲率”是 $[U_a,U_b]$；
- “FIB seam”是对称混合项 $S_{a,b}$ 的一个最小离散实例。

---

### 六、空间、时间和引力在单一变化场中的位置

#### 1. 时间

时间不是独立实体，而是局部变化边上的核：

```math
K_{e,e'}.
```

若存在一个全局势 $T$，满足：

```math
K_{e,e'}\sim T(e')-T(e),
```

则可以把局部变化压缩成全局时间坐标。

如果存在路径环量：

```math
\oint K\neq0,
```

则不能这么做。

所以：

```math
\boxed{
\text{全局时间是局部变化可积时的压缩表示。}
}
```

#### 2. 空间

空间可以由变化之间的可达性、代价和可交换性派生。

例如定义：

```math
d(e,e')
=
\inf_{w:e\leadsto e'}
\sum_{a\in w}c(a).
```

但当：

```math
U_aU_b\neq U_bU_a,
```

路径的实际结果会依赖顺序，空间就不再是单纯的静态距离，而会带有路径结构。

因此：

```math
\boxed{
\text{空间是变化关系的几何化，}
}
```

而不是先验放置变化的容器。

#### 3. 引力

在单一变化场中，引力可以被定义为某种系统性变化偏置。

设局部状态 $e$ 的平均变化为：

```math
G(e)
=
\sum_{e\to e'}
\Pr(e'\mid e)\,
\delta(e,e').
```

如果某一类变化会系统性地把状态推向另一类状态，那么 $G(e)$ 就表现为一种漂移场。

因此，引力的候选数学定义是：

```math
\boxed{
\text{引力}
=
\text{变化场中的系统性方向偏置}.
}
```

但要把它等同于局部时钟变化率，还需要额外假设：

```math
K_e=F(G(e))
```

或：

```math
G(e)=\nabla \Psi(e)
```

之类的关系。

仅仅因为引力和时钟都属于变化，还不能证明它们是同一个可观测量。

---

### 七、衰变、辐射和生命的统一形式

#### 衰变

衰变是某个状态闭包在变化算子下失去稳定：

```math
U_{\mathrm{decay}}\mathcal M
\not\subseteq
\mathcal M.
```

这里 $\mathcal M$ 是原有物质模式的状态集合。

所以衰变不是“时间把物质推走”，而是：

```math
\boxed{
\text{原有变化闭包不再保持自身}.
}
```

#### 辐射

辐射是变化被输出到某个外部因果分支：

```math
\Phi
\longmapsto
\Phi_{\mathrm{remain}}
\oplus
\Phi_{\mathrm{out}}.
```

如果当前观察者的读出满足：

```math
R_{\mathrm{observer}}(\Phi_{\mathrm{out}})=0,
```

则辐射携带的变化对该观察者不可见。

如果辐射被吸收，则变化进入另一个局部节点：

```math
\Phi_{\mathrm{out}}
\longmapsto
\Phi_{\mathrm{absorber}}.
```

所以被遮挡不等于自动恢复，也不等于自动湮灭。

#### 生命

生命则是能够根据局部读出选择变化算子的结构：

```math
\pi:
\mathcal Y_{\mathrm{local}}
\longrightarrow
\mathcal A.
```

它选择动作 $a$，使未来状态持续位于可维护区域 $K$：

```math
U_a p\in K.
```

因此更严格的表达是：

```math
\boxed{
\text{生命}
=
\text{对变化路径的选择性控制}.
}
```

“生命是逆衰变”可以被保留为一种直觉，但数学上应改写为：

```math
\boxed{
\text{生命通过控制变化维持局部结构的未来闭包}.
}
```

它不是让所有变化倒退，而是让系统能够持续选择不会立即离开可维护区域的变化。

---

### 八、最终统一定理

#### 定理四：FIB 单一变化场统一定理

对于五态 FIB ATOM，设：

```math
\mathcal H=\mathbb R^\Sigma,
```

```math
P:\mathcal H\to\mathbb R^4,
```

```math
\ker P=\operatorname{span}\{d\},
```

```math
d=(1,-1,0,-1,1).
```

则隐藏关系的未来可见性由两个独立的二阶响应决定：

```math
\Sigma_{a,b}
=
R(S_{a,b}d),
```

```math
\mathcal H_{a,b}
=
R(H_{a,b}d).
```

其中：

```math
S_{a,b}
=
\frac12(D_aD_b+D_bD_a),
```

```math
H_{a,b}
=
\frac12(D_aD_b-D_bD_a).
```

对于任意同一 $(X,Y,Z)$ 纤维中的两个概率律：

```math
p_\kappa,
\qquad
p_{\kappa'},
```

有：

```math
\boxed{
R(D_aD_b p_{\kappa'})
-
R(D_aD_b p_\kappa)
=
(\kappa'-\kappa)
\left(
\Sigma_{a,b}+\mathcal H_{a,b}
\right).
}
```

因此：

1. 若 $\Sigma_{a,b}\neq0$，则静态联合 seam 被读出；
2. 若 $\mathcal H_{a,b}\neq0$，则动态路径次序被读出；
3. 若二者都为零，则二阶未来读出仍然无法区分 $\kappa$；
4. 若某个更长路径中响应变为非零，则该路径长度是隐藏 seam 的分辨阶。

##### 证明

已由二阶变化分解和：

```math
p_{\kappa'}-p_\kappa
=
(\kappa'-\kappa)d
```

直接得到。

证毕。

---

#### 最终压缩

现在可以把 Auric FIB ATOM 的核心写成：

```math
\boxed{
\text{单一关系场}
\longrightarrow
\text{一阶变化}
\longrightarrow
\text{对称混合变化}
\longrightarrow
\text{反对称路径变化}
\longrightarrow
\text{未来读出}.
}
```

在五态金字塔中：

```math
X,Y,Z
```

是三个一阶边缘变化；

```math
\kappa=E[xy]
```

是对称联合变化；

```math
[U_a,U_b]
```

是动态路径次序变化；

```math
K_{e,e'}
```

是局部变化的等待结构；

```math
R_wU_wd
```

是隐藏关系在未来中的实际可见性。

所以更准确的最终命题是：

```math
\boxed{
\text{不是“存在一个时间场和一个空间场”，}
}
```

而是：

```math
\boxed{
\text{存在一个关系变化场；}
\quad
\text{空间、时间、物质、辐射和生命都是它的不同变化结构。}
}
```

并且：

```math
\boxed{
\text{FIB 的隐藏 seam 是对称混合变化，}
\quad
\text{动态因果的隐藏结构是变化算子的非交换性。}
}
```

这两者共同组成了“只有变化”的可证明版本。

## Auric FIB–ATOM 金字塔的推广：从唯一隐藏缝到 Fibonacci 隐藏层级

这次可以把三态窗口

```math
F[\mathrm{null}]=\mathrm{null},\qquad
F[1]=[2],\qquad
F[2]=[3],\qquad
F[3]=[5],\qquad
F[1,3]=[2,5]
```

看成一个更一般结构的最小实例，而不是孤立的五态例子。

本轮分析只使用可读的状态定义、观测映射、转换算子、显式反例和可验证定理；不把任何绑定登记类信息当作数学事实。项目主页本身也把“定义、假设、可检查证明和开放问题”区分开来。[GitHub](https://github.com/the-omega-institute/trureturing?utm_source=chatgpt.com)

目前与这个方向最相关的项目进展有三类：

- [96e0ba0](https://github.com/the-omega-institute/trureturing/commit/96e0ba0ecebaa879b1e01d4789272761d506186c) 给出了一个机器核对的 $2\times2$ 复矩阵反例。这提醒我们：静态的 FIB 单项式代数可以是交换的，但动态转换算子不能默认交换。
- [4da8b2e](https://github.com/the-omega-institute/trureturing/commit/4da8b2e9c9c6439548fbbc5bea42df65ec2ae2ba) 研究了同一有限观测前缀下仍然不同的完整未来律。它直接支持“有限历史相同，不等于完整因果律相同”。
- [60ebb51](https://github.com/the-omega-institute/trureturing/commit/60ebb51c87e6496e0cab67c899c3b687ef8fd001) 将静态 FIB seam、输出可分辨的未来商结构和后续延拓放到同一框架中。

下面给出一个可以继续形式化的定理系统。

---

### 一、Auric FIB–ATOM 的基本定义

设

```math
\operatorname{Fib}_0=0,\qquad
\operatorname{Fib}_1=1,\qquad
\operatorname{Fib}_{k+2}=\operatorname{Fib}_{k+1}+\operatorname{Fib}_{k}.
```

定义第 $n$ 个 Fibonacci 窗口的合法索引集合为

```math
\Sigma_n
=
\left\{
I\subseteq \{1,\ldots,n\}
:
\text{若 }i\in I,\text{则 }i+1\notin I
\right\}.
```

也就是说，合法集合中不允许相邻索引同时出现。

将用户给定的 FIB 记号推广为

```math
F[I]
=
\left[
\operatorname{Fib}_{i+2}
\right]_{i\in I}^{\uparrow},
```

其中列表按索引递增排列。于是

```math
F[\mathrm{null}]=\mathrm{null},
```

```math
F[1]=[\operatorname{Fib}_3]=[2],
```

```math
F[2]=[\operatorname{Fib}_4]=[3],
```

```math
F[3]=[\operatorname{Fib}_5]=[5],
```

```math
F[1,3]=[\operatorname{Fib}_3,\operatorname{Fib}_5]=[2,5].
```

在这个定义中：

- $I$ 是真正的组合状态；
- $F[I]$ 是 Auric/FIB 标签；
- 状态之间的关系由索引集合决定；
- Fibonacci 数值是状态编码，不直接等于状态的全部观测内容。

定义一个抽象 ATOM 为

```math
\mathsf{ATOM}_n
=
(\Sigma_n,\mathcal U_n,\mathcal O_n),
```

其中：

- $\Sigma_n$ 是状态集合；
- $\mathcal U_n$ 是局部变化或因果转换；
- $\mathcal O_n$ 是所有实际可读取的局部观测。

这里没有引入全局时间坐标。一个“时间读数”只属于 $\mathcal O_n$，即它是状态的局部函数，或者是状态变化过程的局部统计量。

---

### 二、Fibonacci 窗口的状态数

#### 定理 1：状态数满足 Fibonacci 递推

设

```math
a_n=|\Sigma_n|.
```

则

```math
a_0=1,\qquad a_1=2,
```

并且

```math
a_n=a_{n-1}+a_{n-2}.
```

因此

```math
|\Sigma_n|=\operatorname{Fib}_{n+2}.
```

##### 证明

对于任意 $I\in\Sigma_n$，分两种情况。

第一种情况是 $n\notin I$。此时 $I$ 完全是前 $n-1$ 个位置上的合法集合，因此有 $a_{n-1}$ 种。

第二种情况是 $n\in I$。由于不能有相邻索引，必有 $n-1\notin I$。去掉 $n$ 后，剩余部分是前 $n-2$ 个位置上的合法集合，因此有 $a_{n-2}$ 种。

两类互不相交且覆盖全部状态，所以

```math
a_n=a_{n-1}+a_{n-2}.
```

初值为

```math
a_0=1,\qquad a_1=2,
```

这正是 Fibonacci 数列向前平移两位，因此

```math
a_n=\operatorname{Fib}_{n+2}.
```

证毕。

---

#### 低阶状态数

| 窗口长度 $n$ | 状态数 $ |\Sigma_n| $ | 一阶隐藏维数 $h_n$ |
|---:|---:|---:|
| $1$ | $2$ | $0$ |
| $2$ | $3$ | $0$ |
| $3$ | $5$ | $1$ |
| $4$ | $8$ | $3$ |
| $5$ | $13$ | $7$ |
| $6$ | $21$ | $14$ |

三态窗口的五个状态正好是

```math
\Sigma_3
=
\{
\varnothing,\{1\},\{2\},\{3\},\{1,3\}
\}.
```

因此 Auric 金字塔不是任意画出来的图形。它是第一个出现非平凡隐藏联合关系的 Fibonacci 窗口。

---

### 三、FIB 状态函数的完整基

对于每个位置 $i$，定义占据指示函数

```math
x_i(s_I)=
\begin{cases}
1,&i\in I,\\
0,&i\notin I.
\end{cases}
```

对于任意合法集合 $A\in\Sigma_n$，定义单项式

```math
x_A
=
\prod_{i\in A}x_i.
```

约定

```math
x_{\varnothing}=1.
```

注意：

```math
x_A(s_I)=1
\quad\Longleftrightarrow\quad
A\subseteq I.
```

它表示“$A$ 中所有位置都被占据”，不一定表示状态恰好等于 $A$。

例如在五态窗口中，

```math
x_{\{1,3\}}(s_{13})=1,
```

但在更长窗口中，若状态为 $\{1,3,5\}$，仍有

```math
x_{\{1,3\}}(s_{135})=1.
```

所以在 $n\geq5$ 时，$\mathbb E[x_{\{1,3\}}]$ 不再等于某一个状态概率，而是多个状态概率之和。

---

#### 定理 2：FIB 单项式构成全部状态函数的基

函数族

```math
\{x_A:A\in\Sigma_n\}
```

构成向量空间

```math
\mathbb R^{\Sigma_n}
```

的一组基。

##### 证明

首先证明线性无关。假设

```math
\sum_{A\in\Sigma_n}c_Ax_A=0.
```

在状态 $s_I$ 上取值，得到

```math
\sum_{A\subseteq I}c_A=0.
```

当 $I=\varnothing$ 时，

```math
c_{\varnothing}=0.
```

假设所有真子集 $A\subsetneq I$ 的系数都已经为零，则在 $s_I$ 上有

```math
c_I+\sum_{A\subsetneq I}c_A=0,
```

因此

```math
c_I=0.
```

按 $|I|$ 归纳可得所有 $c_A=0$，所以这些函数线性无关。

另一方面，

```math
|\Sigma_n|=\dim\mathbb R^{\Sigma_n},
```

而基函数的个数也是 $|\Sigma_n|$。因此它们构成一组基。

证毕。

---

#### Möbius seam 展开

对于任意状态函数

```math
f:\Sigma_n\to\mathbb R,
```

定义其 $A$-阶混合差分

```math
\Delta_Af
=
\sum_{B\subseteq A}
(-1)^{|A|-|B|}
f(s_B).
```

其中 $A$ 必须是合法集合，因此 $A$ 的所有子集也都合法。

则有反演公式

```math
f(s_I)
=
\sum_{A\subseteq I}\Delta_Af.
```

这说明任意局部观测都可以分解成：

- 零阶部分：$\Delta_{\varnothing}f$；
- 一阶部分：$\Delta_{\{i\}}f$；
- 二阶 seam：$\Delta_{\{i,j\}}f$；
- 三阶 seam：$\Delta_{\{i,j,k\}}f$；
- 更高阶 seam。

在三态窗口中，唯一非平凡的高阶项是

```math
\Delta_{\{1,3\}}f
=
f(s_{13})-f(s_1)-f(s_3)+f(s_{\varnothing}).
```

这正是先前出现的四角混合量。

---

### 四、一阶观测为什么在三态时第一次失效

设概率分布为

```math
p=(p_I)_{I\in\Sigma_n}.
```

定义一阶占据均值

```math
\mu_i
=
\mathbb E_p[x_i]
=
\sum_{I\in\Sigma_n}p_Ix_i(s_I).
```

一阶观测映射为

```math
T_1(p)
=
\left(
1,\mu_1,\ldots,\mu_n
\right).
```

定义一阶观测空间

```math
V_n^{(1)}
=
\operatorname{span}
\{1,x_1,\ldots,x_n\}.
```

#### 定理 3：一阶观测空间维数为 $n+1$

```math
\dim V_n^{(1)}=n+1.
```

##### 证明

若

```math
a_0+\sum_{i=1}^{n}a_ix_i=0
```

对所有状态成立，那么在空状态 $s_{\varnothing}$ 上取值，得到

```math
a_0=0.
```

再在单点状态 $s_{\{j\}}$ 上取值，得到

```math
a_j=0.
```

因此

```math
1,x_1,\ldots,x_n
```

线性无关，共有 $n+1$ 个函数，所以

```math
\dim V_n^{(1)}=n+1.
```

证毕。

---

#### 定理 4：一阶不可见分布的维数

在概率分布的内部区域，即所有 $p_I>0$ 的区域中，保持归一化和全部一阶均值不变的分布纤维，其局部维数为

```math
h_n
=
|\Sigma_n|-(n+1)
=
\operatorname{Fib}_{n+2}-n-1.
```

##### 证明

概率向量有 $|\Sigma_n|$ 个坐标。

归一化条件

```math
\sum_Ip_I=1
```

提供一个线性约束。

每个一阶均值

```math
\mu_i=\sum_Ip_Ix_i(s_I)
```

再提供一个约束，共 $n$ 个。

因此总约束数为 $n+1$。由定理 3，这些约束独立，所以剩余维数为

```math
|\Sigma_n|-(n+1).
```

再代入

```math
|\Sigma_n|=\operatorname{Fib}_{n+2},
```

得到

```math
h_n=\operatorname{Fib}_{n+2}-n-1.
```

证毕。

---

这个公式给出一个非常重要的结论：

> $n=1,2$ 时，一阶占据数据可以确定整个分布；从 $n=3$ 开始，一阶数据必然存在隐藏联合关系。

因此三态窗口是最小的非平凡 Auric seam。

---

### 五、Auric 金字塔的唯一隐藏方向

三态窗口的五个状态按顺序排列为

```math
\varnothing,\quad 1,\quad 2,\quad 3,\quad 13.
```

在占据坐标

```math
(x_1,x_2,x_3)
```

中，它们对应于

```math
v_{\varnothing}=(0,0,0),
```

```math
v_1=(1,0,0),
```

```math
v_2=(0,1,0),
```

```math
v_3=(0,0,1),
```

```math
v_{13}=(1,0,1).
```

四个点

```math
v_{\varnothing},v_1,v_3,v_{13}
```

都位于平面

```math
x_2=0
```

上，并且满足

```math
v_{\varnothing}+v_{13}
=
v_1+v_3.
```

它们构成一个正方形的仿射结构。点 $v_2$ 位于外部，成为顶点。因此其凸包是一个四角锥。

---

#### 定理 5：三态 Auric 金字塔只有一个一阶隐藏方向

概率坐标顺序取为

```math
(p_{\varnothing},p_1,p_2,p_3,p_{13}).
```

则保持总概率和一阶均值不变的唯一方向，除去整体倍数，是

```math
d=(1,-1,0,-1,1).
```

##### 证明

需要验证：

```math
1-1+0-1+1=0,
```

所以总概率不变。

对 $x_1$：

```math
0\cdot1+1\cdot(-1)+0\cdot0+0\cdot(-1)+1\cdot1=0.
```

对 $x_2$：

```math
0.
```

对 $x_3$：

```math
0\cdot1+0\cdot(-1)+0\cdot0+1\cdot(-1)+1\cdot1=0.
```

因此 $d$ 位于一阶观测映射的核中。

由

```math
h_3=\operatorname{Fib}_5-3-1=5-4=1,
```

该核是一维的，所以所有隐藏方向都是 $d$ 的倍数。

证毕。

---

设

```math
X=\mu_1,\qquad
Y=\mu_3,\qquad
Z=\mu_2.
```

定义二阶联合量

```math
\kappa
=
\mathbb E[x_1x_3].
```

在三态窗口中，$x_1x_3$ 只在状态 $13$ 上为 $1$，因此

```math
\kappa=p_{13}.
```

完整分布可以写成

```math
p_{\kappa}
=
\left(
1-X-Y-Z+\kappa,\,
X-\kappa,\,
Z,\,
Y-\kappa,\,
\kappa
\right).
```

非负性要求

```math
\max(0,X+Y+Z-1)
\leq
\kappa
\leq
\min(X,Y).
```

因此：

- $X,Y,Z$ 给出一阶可见部分；
- $\kappa$ 给出唯一隐藏 seam；
- $d$ 是沿着 $\kappa$ 改变时的方向。

---

### 六、FIB 标签本身是无损的，隐藏来自观测压缩

这是 Auric 结构中一个容易忽略的关系。

#### 定理 6：完整 FIB 列表是单射

映射

```math
I\longmapsto F[I]
```

在 $\Sigma_n$ 上是单射。

##### 证明

由于 Fibonacci 数列

```math
\operatorname{Fib}_3,\operatorname{Fib}_4,\operatorname{Fib}_5,\ldots
```

严格递增，按递增顺序排列的标签列表唯一确定其索引集合。

例如

```math
[2,5]
```

唯一对应索引集合

```math
\{1,3\}.
```

证毕。

事实上，甚至可以进一步压缩为一个 Fibonacci 加权和

```math
W(I)
=
\sum_{i\in I}\operatorname{Fib}_{i+2}.
```

#### 定理 7：Fibonacci 加权和在合法窗口上也是单射

若 $I,J\in\Sigma_n$ 且

```math
W(I)=W(J),
```

则

```math
I=J.
```

##### 证明

设

```math
w_i=\operatorname{Fib}_{i+2}.
```

令

```math
M_r
=
\max\left\{
\sum_{i\in I}w_i:
I\subseteq\{1,\ldots,r\},\ I\in\Sigma_r
\right\}.
```

由于最后一个位置要么不取，要么取，所以

```math
M_r=\max(M_{r-1},M_{r-2}+w_r).
```

由 Fibonacci 递推可归纳证明

```math
M_r<w_{r+1}.
```

现在假设 $I\neq J$，取最大对称差位置 $m$，不妨设

```math
m\in I\setminus J.
```

所有大于 $m$ 的共同位置在两边相消。集合 $J\setminus I$ 只包含小于 $m$ 的位置，因此

```math
\sum_{i\in J\setminus I}w_i
\leq M_{m-1}
<w_m.
```

而 $I\setminus J$ 至少包含 $m$，所以

```math
\sum_{i\in I\setminus J}w_i
\geq w_m.
```

于是

```math
W(I)>W(J),
```

与 $W(I)=W(J)$ 矛盾。因此

```math
I=J.
```

证毕。

---

这说明：

> FIB 编码本身可以是无损的；信息损失不是发生在“状态编码”这一步，而是发生在只观察一阶均值、单一能量、单一局部时钟或有限历史之后。

例如三态窗口中：

```math
W(\varnothing)=0,
```

```math
W(1)=2,
```

```math
W(2)=3,
```

```math
W(3)=5,
```

```math
W(1,3)=7.
```

完整的 $W$ 分布可以恢复五态概率。但它的均值只有

```math
\mathbb E[W]
=
2X+3Z+5Y,
```

其中不含 $\kappa$。因此所有 $p_\kappa$ 都有相同的加权平均值。

这给出了一个精确的区分：

- 完整 FIB 输出分布：可以识别状态律；
- FIB 输出的单一均值：可能完全看不见联合 seam；
- 局部时钟的单一平均速率：也可能只看到一阶投影。

---

### 七、隐藏 seam 的 Fibonacci 层级

定义 $r$ 阶观测空间

```math
V_n^{(r)}
=
\operatorname{span}
\left\{
x_A:
A\in\Sigma_n,\ |A|\leq r
\right\}.
```

它表示所有至多 $r$ 阶联合占据量都可以测量。

#### 定理 8：$r$ 阶观测空间的维数

长度为 $n$ 的路径上，大小为 $k$ 的合法集合个数为

```math
N(n,k)
=
\binom{n-k+1}{k}.
```

因此

```math
\dim V_n^{(r)}
=
\sum_{k=0}^{\min(r,\lfloor (n+1)/2\rfloor)}
\binom{n-k+1}{k}.
```

相应的隐藏维数为

```math
h_{n,r}
=
\operatorname{Fib}_{n+2}
-
\sum_{k=0}^{\min(r,\lfloor (n+1)/2\rfloor)}
\binom{n-k+1}{k}.
```

##### 证明

设合法集合为

```math
A=\{i_1<i_2<\cdots<i_k\}.
```

合法性要求

```math
i_{j+1}\geq i_j+2.
```

定义平移后的索引

```math
j_r=i_r-(r-1).
```

则

```math
1\leq j_1<j_2<\cdots<j_k\leq n-k+1.
```

因此选择 $k$ 个不相邻位置等价于从 $n-k+1$ 个位置中选择 $k$ 个普通子集，所以个数为

```math
\binom{n-k+1}{k}.
```

再对 $k\leq r$ 求和即可。

证毕。

---

低阶结果如下：

| 窗口 | 总状态函数维数 | 一阶观测维数 | 一阶隐藏维数 | 二阶隐藏维数 |
|---:|---:|---:|---:|---:|
| $n=3$ | $5$ | $4$ | $1$ | $0$ |
| $n=4$ | $8$ | $5$ | $3$ | $0$ |
| $n=5$ | $13$ | $6$ | $7$ | $1$ |
| $n=6$ | $21$ | $7$ | $14$ | $4$ |

这揭示了一个层级结构：

- 三态窗口只有一个二阶 seam；
- 四态窗口有三个二阶 seam；
- 五态窗口的一阶和二阶数据仍不足，还剩一个三阶 seam；
- 窗口越长，需要的联合观测阶数越高。

例如 $n=5$ 时，最大合法集合之一是

```math
\{1,3,5\}.
```

对应的三阶混合项为

```math
\Delta_{\{1,3,5\}}f.
```

如果一个局部时钟只包含零阶、一阶和二阶响应，那么它仍然无法看到这个三阶关系。

---

### 八、局部时钟与隐藏 seam

令每个状态 $s_I$ 携带一个局部等待核

```math
K_I
\in
\operatorname{Prob}(\mathbb R_{\geq0}).
```

混合后的局部时钟分布为

```math
C_K(p)
=
\sum_{I\in\Sigma_n}p_IK_I.
```

由于 FIB 单项式构成函数基，可以把它展开为

```math
C_K(p)
=
\sum_{A\in\Sigma_n}
\Delta_AK\,
\kappa_A(p),
```

其中

```math
\kappa_A(p)
=
\mathbb E_p[x_A].
```

因此：

- 若 $\Delta_AK=0$，这个局部时钟对 $A$-阶 seam 不敏感；
- 若 $\Delta_AK\neq0$，这个局部时钟可以对该 seam 产生响应；
- 若所有 $|A|\geq2$ 的混合差都为零，则该时钟完全是一阶观测。

在三态窗口中，

```math
\Delta_{\{1,3\}}K
=
K_{\varnothing}-K_1-K_3+K_{13}.
```

因此

```math
C_K(p_\kappa)
=
C_K^{(0)}(X,Y,Z)
+
\kappa
\left(
K_{\varnothing}-K_1-K_3+K_{13}
\right).
```

#### 定理 9：局部时钟恢复隐藏参数的判据

在固定 $(X,Y,Z)$ 的条件下，一个局部时钟能够唯一恢复 $\kappa$，当且仅当

```math
K_{\varnothing}-K_1-K_3+K_{13}\neq0.
```

##### 证明

上式表明

```math
C_K(p_\kappa)
=
A+B\kappa,
```

其中

```math
B=
K_{\varnothing}-K_1-K_3+K_{13}.
```

若 $B=0$，所有 $\kappa$ 给出同一时钟分布，因此无法恢复。

若 $B\neq0$，则

```math
\kappa
=
\frac{C_K(p_\kappa)-A}{B},
```

所以 $\kappa$ 唯一确定。

证毕。

这可以把“时间是否包含隐藏结构”改写成严格问题：

> 一个局部时间场是否能测到联合关系，不取决于它是否被叫作时间，而取决于它的混合差分是否非零。

---

### 九、有限历史与完整因果律

设状态分布的变化由算子 $U_w$ 描述，$w$ 表示一段局部操作词。设最后的读出为 $R_w$，则完整观测为

```math
O_w=R_wU_w.
```

定义一阶隐藏空间

```math
\mathcal H_n^{(1)}
=
\ker T_1.
```

对于某个隐藏差异 $q\in\mathcal H_n^{(1)}$，有三种情况：

```math
U_wq=0
```

表示隐藏差异在真实状态演化中已经被抹去；

```math
U_wq\neq0,
\qquad
R_wU_wq=0
```

表示差异仍存在，但当前读出看不见；

```math
R_wU_wq\neq0
```

表示该历史终于将隐藏差异转化成可观测信号。

定义所有未来记录的共同盲核

```math
\mathcal K_{\mathrm{future}}
=
\bigcap_{w\in\mathcal W}
\ker(R_wU_w).
```

#### 定理 10：完整未来观测的可识别判据

一阶隐藏律可以由完整未来记录唯一识别，当且仅当

```math
\mathcal H_n^{(1)}
\cap
\mathcal K_{\mathrm{future}}
=
\{0\}.
```

##### 证明

若存在

```math
0\neq q\in
\mathcal H_n^{(1)}
\cap
\mathcal K_{\mathrm{future}},
```

则对所有未来词 $w$ 都有

```math
R_wU_wq=0.
```

于是两个足够接近的内部概率分布

```math
p
\quad\text{和}\quad
p+\varepsilon q
```

具有相同的一阶观测和相同的全部未来读出，因此不可区分。

反过来，如果交集只有零向量，那么任意非零隐藏差异都至少会被某个未来词 $w$ 映射为非零读出，因此可以被完整观测区分。

证毕。

这正好解释了 [4da8b2e](https://github.com/the-omega-institute/trureturing/commit/4da8b2e9c9c6439548fbbc5bea42df65ec2ae2ba) 中的现象：有限观测前缀的盲核可以非零，而加入更长的返回词以后，盲核变小，甚至变成零。

所以“射线没有被当前探测器看到”不能直接推出“信息已经不存在”。严格地说，要区分：

1. 信息在完整状态中真的被 $U_w$ 消灭；
2. 信息转移到未观测的吸收体或环境；
3. 信息仍在系统中，但当前 $R_w$ 对它无响应；
4. 只有当全部允许未来观测的交集仍为盲核时，才可以说它对该观测体系永久不可恢复。

---

### 十、静态 seam 与动态非交换性的区别

FIB 单项式满足

```math
x_Ax_B
=
\begin{cases}
x_{A\cup B},&A\cup B\in\Sigma_n,\\
0,&A\cup B\notin\Sigma_n.
\end{cases}
```

因此静态 FIB 代数是交换的：

```math
x_Ax_B=x_Bx_A.
```

但是动态转换算子不必交换。对两个局部变化 $U_a,U_b$，定义

```math
H_{a,b}
=
\frac12(U_aU_b-U_bU_a).
```

若

```math
H_{a,b}\neq0,
```

则操作顺序会影响最终状态，这是一种动态路径记忆或 holonomy。

因此必须区分两种隐藏关系：

##### 静态联合 seam

```math
\Delta_Af
```

描述同一状态内部多个位置的联合占据关系。

##### 动态路径 seam

```math
[U_a,U_b]
=
U_aU_b-U_bU_a
```

描述不同局部变化顺序之间的差异。

三态 FIB 中的 $\kappa$ 属于第一类。它不是由于算子不交换造成的，而是由于一阶观测没有记录 $x_1x_3$。

项目中机器核对的 $2\times2$ 矩阵反例正好提醒我们：不能把静态交换结构自动推广为所有动态算子的交换结构。[96e0ba0](https://github.com/the-omega-institute/trureturing/commit/96e0ba0ecebaa879b1e01d4789272761d506186c)

---

### 十一、没有全局时间时的场论表达

如果坚持“不使用 $3+1$ 的全局时间”，可以把基本对象定义为局部事件图

```math
\mathcal G=(V,E).
```

每条有向边

```math
e:u\to v
```

携带一个局部变化量

```math
\delta(e).
```

它可以是：

- 状态变化；
- 局部时钟增量；
- 衰变概率；
- 信息可恢复性；
- 辐射或吸收事件；
- 观测核的变化。

全局标量势 $\Phi$ 只是一个派生对象。如果存在

```math
\delta(u\to v)=\Phi(v)-\Phi(u),
```

则局部变化可以被整合为一个标量场。

#### 定理 11：局部变化可整合为全局势的充要条件

存在 $\Phi:V\to\mathbb R$ 使得

```math
\delta(u\to v)=\Phi(v)-\Phi(u)
```

当且仅当每个闭合回路 $C$ 满足

```math
\sum_{e\in C}\varepsilon_e\delta(e)=0.
```

##### 证明

若存在 $\Phi$，沿闭环相加时每个顶点势值都会抵消，因此闭环和为零。

反过来，若所有闭环和为零，固定参考点 $v_0$，定义 $\Phi(v)$ 为从 $v_0$ 到 $v$ 的任意路径上的边变化量之和。由于任意两条路径的差形成闭环，闭环和为零，所以 $\Phi(v)$ 与路径选择无关。于是对边 $u\to v$ 有

```math
\Phi(v)-\Phi(u)=\delta(u\to v).
```

证毕。

因此：

- 若闭环和全部为零，可以事后构造一个全局时间样标量；
- 若存在非零闭环和，则基本对象只能是局部变化和路径依赖；
- 这不需要预设全局线性时间。

在这个框架中，“时间场”不是额外的第四维坐标，而可以被定义成一族局部观测核

```math
K_I
```

以及局部转换边上的变化量

```math
\delta(e).
```

---

### 十二、对“生命是逆衰变”的严格重述

如果把衰变定义为某种不可逆的观测压缩，可以定义一个信息可恢复性函数

```math
\mathcal R(p;\mathcal O)
```

表示在观测族 $\mathcal O$ 下，分布 $p$ 还能被区分到什么程度。

于是“被动衰变”可以形式化为：

```math
\mathcal R(U p;\mathcal O)
\leq
\mathcal R(p;\mathcal O)
```

即转换后可恢复的信息不增加。

所谓“生命的逆衰变”则不应直接写成违反物理定律的反向衰变，而应定义为：

```math
\mathcal R(U_{\mathrm{life}}p;\mathcal O_{\mathrm{expanded}})
>
\mathcal R(p;\mathcal O_{\mathrm{restricted}}),
```

也就是生命通过内部记忆、反馈、复制、主动测量和环境耦合，扩大了有效观测族，使原本隐藏的 seam 重新变得可区分。

在 FIB–ATOM 模型中，这意味着生命系统不是简单地把

```math
p_\kappa
```

沿着 $d$ 方向被动推进，而是主动构造新的读出 $R$ 或新的转换 $U$，使

```math
RUd\neq0.
```

这就是“逆衰变”的数学版本：

> 不是让已经离开系统的信息超光速返回，而是通过增加记忆和观测结构，把原来对当前读出不可见的内部差异转换为新的可见差异。

这一区分也适用于辐射问题。一个光子离开当前观测区域，并不自动意味着其携带的信息在整个宇宙状态中消失；它可能只是进入了当前模型没有包含的自由度。只有在扩展后的完整观测族中仍满足

```math
\bigcap_w\ker(R_wU_w)\neq\{0\}
```

时，才可以严格称为对该观测体系永久不可恢复。

---

### 十三、目前可以冻结的核心定理集

如果把这一阶段正式写入 Auric FIB–ATOM 项目，最值得冻结的是以下六条：

#### 定理 A：Fibonacci 状态计数

```math
|\Sigma_n|=\operatorname{Fib}_{n+2}.
```

#### 定理 B：FIB 单项式基

```math
\{x_A:A\in\Sigma_n\}
```

构成

```math
\mathbb R^{\Sigma_n}
```

的基。

#### 定理 C：一阶隐藏维数

```math
h_n=\operatorname{Fib}_{n+2}-n-1.
```

#### 定理 D：三态唯一 seam

```math
\ker T_1
=
\operatorname{span}
\{(1,-1,0,-1,1)\}.
```

#### 定理 E：FIB 权重单射

```math
I\mapsto
\sum_{i\in I}\operatorname{Fib}_{i+2}
```

在合法 Fibonacci 窗口上是单射。

#### 定理 F：未来可识别性

```math
\mathcal H_n^{(1)}
\cap
\bigcap_{w}\ker(R_wU_w)
=
\{0\}
```

当且仅当完整未来记录能够消除一阶观测留下的所有隐藏差异。

这六条把原来的五态金字塔提升成了一个完整层级：

```math
\text{FIB 编码}
\longrightarrow
\text{状态函数基}
\longrightarrow
\text{一阶投影}
\longrightarrow
\text{隐藏 seam}
\longrightarrow
\text{动态未来分辨}
\longrightarrow
\text{局部因果场}.
```

---

#### 最终结论

Auric FIB 金字塔的真正核心不是“五个点”，而是以下事实：

```math
\boxed{
\text{三态窗口是第一个使一阶局部观测失去完整性的窗口}
}
```

它的唯一隐藏量是

```math
\kappa
=
\mathbb E[x_1x_3],
```

其唯一隐藏方向是

```math
d=(1,-1,0,-1,1).
```

推广到长度 $n$ 后，隐藏维数变为

```math
\boxed{
h_n=\operatorname{Fib}_{n+2}-n-1
}
```

并且高阶 seam 的数量由

```math
\binom{n-k+1}{k}
```

控制。

因此：

- FIB 标签可以是无损编码；
- 一阶局部时钟可以丢失联合信息；
- 隐藏关系不是神秘的额外实体，而是观测映射的核；
- 动态变化可以进一步暴露或抹去这些隐藏方向；
- “时间”可以被建模为局部变化核，而不必预设全局线性参数；
- “逆衰变”可以被形式化为主动扩大观测族、恢复原先不可区分的状态差异。

至于“空间引力与时间引力是否是同一个物理场”，上述定理还没有证明这一点。它们已经证明的是更基础、也更可检验的一层：任何所谓局部时间、衰变、辐射或生命过程，都可以先被翻译为状态、转换和观测三者之间的关系，然后通过隐藏维数、seam 系数和未来盲核来判断哪些信息真的消失，哪些信息只是暂时没有被读取。


## 来源与文献范围

来源快照与数学参考只支持表中列出的范围；不支持任何未经桥接的 FIB 动作、物理时钟、引力或生命解释。不可变来源范围采用已提供的专项阅读结论，阅读证明源码与当前编译核验是两件事。

| 参考 | 精确范围与适用边界 |
| --- | --- |
| [CStarNovak.lean，96e0ba0 不可变来源](https://github.com/the-omega-institute/trureturing/blob/96e0ba0ecebaa879b1e01d4789272761d506186c/D5/S3/Quantum/Algebra/CStarNovak.lean)；blob `ab31823846492be7ab55a0eac5faad76e2467f71` | 提供的源码阅读覆盖 `ncos`、`novakEntry`、`IsPositiveMatrix`、`claim`、私有标量平方/余弦及见证辅助项、`result : ¬ claim`。只承担 Q5 的特定反驳范围；没有当前重编译。 |
| K. Mahesh Krishna，[arXiv:2108.06662v1](https://arxiv.org/pdf/2108.06662v1)，§2、p. 10 Conjecture 4.3 与 Theorem 4.4；[不可变来源说明](https://github.com/the-omega-institute/trureturing/blob/96e0ba0ecebaa879b1e01d4789272761d506186c/Library/QuantumBounds/krishna2021cstarnovak.md)，blob `909b173785b0734ecfd0af546bd47e1bcfeb85d7` | `literature-attested`：幺 $C^\ast$-代数值正性猜想及交换情形的余弦差/Schur 乘积证明。不能作为 FIB 或物理转移定理。 |
| [取得核盲方向来源，4da8b2e](https://github.com/the-omega-institute/trureturing/blob/4da8b2e9c9c6439548fbbc5bea42df65ec2ae2ba/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_KERNEL_BLIND_DIRECTIONS_AFTER_PAIRED_CALIBRATION.md)；blob `245489ffba0928a620ac3299c563214e75671848`，约定、Definition 3.1、Theorems 4.2/5.1、Corollary 5.2、Proposition 6.2、§8 | 开放理论散文中的来源专项构造；改变取得核且状态规模增长，范围见 Q6，不是固定五态 kernel 定理。 |
| [静态 seam 与未来商来源，60ebb51](https://github.com/the-omega-institute/trureturing/blob/60ebb51c87e6496e0cab67c899c3b687ef8fd001/docs/develop/theory/AURIC_FIB_ATOM_SEAM_BILINEAR_CURVATURE_AND_OUTPUT_FUTURE_QUOTIENT.md)；blob `1933b03dfb8963a1f0a16cb867cc8850d7d74cec`，参考边界 Q1–Q9、§4、§9 | 有限定的开放参考；拟议 `FIBNativeBridge.lean` 是实现义务，不是已有声明或动作等价。 |
| [输出分辨仪器来源，60ebb51](https://github.com/the-omega-institute/trureturing/blob/60ebb51c87e6496e0cab67c899c3b687ef8fd001/docs/develop/theory/AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md)，编者限定 Q1–Q13、有限状态 horizon 上界 | 提供的独立阅读定位输出子核、完整记录及固定有限载体条件；适用边界见 Q6、Q11。 |
| Keith Conrad，[Bilinear Forms](https://kconrad.math.uconn.edu/blurbs/linmultialg/bilinearform.pdf)，§1 定理 1.7，p. 3 | `literature-attested`：特征不为二的双线性形式对称/反对称唯一分解，适用对象及推广见 Q1。 |
| Gian-Carlo Rota，[On the Foundations of Combinatorial Theory I. Theory of Möbius Functions](https://doi.org/10.1007/BF00531932)，§3 | `literature-attested`：已提供独立文献阅读定位的包含关系反演与 Boolean 区间系数；书目定位不替代 Q8 的应用条件与散文推导。 |
| Connor Ahlbach、Jeremy Usatine、Nicholas Pippenger，[Efficient Algorithms for Zeckendorf Arithmetic，arXiv:1207.4497v1](https://arxiv.org/pdf/1207.4497v1)，§1 | `literature-attested`：从 $\operatorname{Fib}_2=1$ 起的经典非相邻表示唯一性。本卷从 $2$ 起的子集编码范围与归纳见 Q9，不声称全自然数满射或原创。 |

**核验与未决边界。** 本卷保留的输入没有内容删节；数学外壳和标题层级整理不改变公式载荷。编者限定给出普通数学适用条件、反例与补全散文论证，不提供当前 kernel 认证。没有新增 Lean/Blueprint/Reg/Frozen、消化记录、实验材料或判官；正文不结算项目状态。真实来源/动作/读口实现、完整合法观测合同、能量与样本资源、物理及生物桥仍待相应证据。

## 追加锚（本行以下为增补区）
