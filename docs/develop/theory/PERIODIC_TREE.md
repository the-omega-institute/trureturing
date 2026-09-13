# 元素周期树(Periodic Tree of Mathematical Elements)· 章程与施工册 v1.0
*(**项目第四文档(正典)**,第 335 版记事立;PZG–GICT 项目附属工程;ZFC 内定义,零新公理;账本 27.417,2026-07-20。配套机读注册表:PERIODIC_TREE_registry.jsonl)*

## 0. 名与地契
树干为 **Stern–Brocot / Farey 树**(Stern 1858, Brocot 1861)——$(2,3,\infty)$ 基本直角三角形之反射递归;节点 = $SL_2(\mathbb Z)$ 矩阵,路径 = $L/R$ 词 = 连分数,叶叶既约(树上素性之原型定理)。本工程不植树,只立**挂载协议**:凡具"递归 + 二次"双结构之数学对象,经函子标注入册。

## 1. 挂载协议(四标签)
每个对象登记:**地址**(树路径/典范词——递归坐标);**素性位**(该层不可约判据之输出);**度量荷**(二次型脸:迹 $T$、内容 $g$、判别式 $d=(T^2-1)/g^2$、勾股恒等 $D=3A^2+(A+B)^2$、辐角 $\arg z$);**组合荷**(行走脸:$\Psi$、城色 $m\bmod36$、Jacobi 位)。附加:**流指针**(三明治后继 $T'=6c+7T$)与**核籍**(奇核者附核词与 $j=\mathrm{tr}/12$)。

## 2. 门卫手册(素性三级判据)
- **一级(地址级,线性时间)**:典范词非偶长词之 $k\ge2$ 次幂(奇词平方**豁免**——类-本原判定,GICT E.38)。
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

## 附录 T：WSS 的素数下标迹障碍与幂复合多项式

### T.1 与周期树主线的准确联系

固定原黄金单位 $\varphi$、其共轭 $\psi=1-\varphi$，以及原载体
$\mathcal O=\mathbb Z[\varphi]$。$\varphi^2=\varphi+1$，范数为 $-1$。
现役 `goldenLucas(n)=trace(phi^n)` 满足 $L_n=\varphi^n+\psi^n$。
Fibonacci 矩阵 $Q$ 与此单位的乘法是同一整数线性递推；$Q^2$ 是周期树的一对左右生成矩阵之积。

对这个固定对象改变模观察 $p,p^2,\ldots$，即得到 WSS 问题卡的研究对象。
模 $p$ 下回归，不保证模 $p^2$ 下回归。WSS 问的是某个素数上是否恰好没有
第一次额外周期增长。它与黄金单位、共轭、范数、回归和层级观察直接相关。
实圆周上的无理黄金旋转则没有非零整数周期；有限模回归与该实动力系统
不能由“黄金”这个共同名称推成共轭关系。5040的约数资源选择也不蕴含 WSS 的存在。

### T.2 从外部数域结果选定实际多项式

Jones [T-ref1] 对 $k$-WSS 证明：在其参数条件下，$p$ 为 $k$-WSS 素数当且仅当
$X^{2p}-kX^p-1$ 关于指定根的幂基不是整个数域整数环的整基。
黄金特化 $k=1$、判别式5满足参数条件。其定理1.1及引理3.4–3.5
同时连接模 $p^2$ 的多项式取值与整数环指标。

这里必须保留“指定根的幂基”的含义。若 $K_p=\mathbb Q(\theta_p)$ 且
$\theta_p^{2p}-\theta_p^p-1=0$，比较的是
$\mathbb Z[\theta_p]\subseteq\mathcal O_{K_p}$。
这个给定幂基失败，不等于该数域不存在任何其他幂整基。

该文献等价已经被证明，不能再计为新解决的开放问题。本附录只将其具体
多项式输入接回现役黄金载体，并给出精确的迹障碍；没有假设或形式化
Dedekind指标判据、不可约性、整数环构造或 Jones 的完整定理。

### T.3 准确恒等式及保留整除性的证明

定义实际整数多项式及其取值

$$
\mathcal P_n(X)=X^{2n}-X^n-1,
\qquad E_n=\mathcal P_n(\varphi)\in\mathcal O.
$$

**定理 T1。** 对每个奇数 $n$，

$$
\boxed{E_n=(L_n-1)\varphi^n.}\tag{T1}
$$

证明：任意 $x\in\mathcal O$ 满足
$x^2-\operatorname{Tr}(x)x+\operatorname{N}(x)=0$，逐个整数坐标展开即可验证。
取 $x=\varphi^n$。奇数 $n$ 保证 $\operatorname{N}(x)=-1$，故
$x^2-x-1=(\operatorname{Tr}(x)-1)x$。

更进一步，$x(-\overline x)=1$，给出原黄金环中的显式逆。因此对任意整数 $q$：

$$
\boxed{q\mid E_n\text{ 于 }\mathcal O
\iff q\mid L_n-1\text{ 于 }\mathbb Z.}\tag{T2}
$$

正向先在原环乘以 $-\overline x$，再取整数坐标；反向直接乘以 $x$。
该证明不在模 $q$ 的环中非法约去零因子。它包括复合标量及零标量。

对全部自然模数 $q$，现役 `GoldenMod.reduce` 还给出

$$
\boxed{E_n=0\pmod q\iff L_n=1\pmod q.}\tag{T3}
$$

范数则为

$$
\boxed{\operatorname N(E_n)=-(L_n-1)^2.}\tag{T4}
$$

因而在每个奇素数 $p$ 上，$\mathcal P_p(\varphi)$ 的局部模 $p^2$ 障碍
完全等于 $p^2\mid L_p-1$。T1–T4 的证明脚本量化于全部奇数下标，
不依赖未合并的 WSS 周期塔模块，也没有给未知的 WSS 素数提供存在性见证。

### T.4 与现有周期商及两实嵌入的关系

经典 WSS 等价表述包括 $L_p\equiv1\pmod{p^2}$；Jones 的局部取值判据加上
T3也恢复这个表述。PR #7446 给出的标准商桥与高次周期脚本在本轮读取时
仍为未编译 Draft，不作为本模块已获核验的依赖。

若 $\epsilon=(5/p)$、$n=p-\epsilon$，则两个经典规范化商满足

$$
\ell_p=(L_p-1)/p\bmod p,
\quad q_p=F_n/p\bmod p,
\qquad 2\ell_p=5q_p\pmod p\quad(p\ne2,5).
$$

该标量比例作为本节数学背景和有限诊断，未在本模块中新增其 Lean 声明。
核心已交付内容是实际多项式取值、原 Lucas 迹与所有标量模整除之间的 T1–T4。

在实嵌入下，T1 的两个面分别为 $(L_n-1)\varphi^n$ 和
$(L_n-1)\psi^n$。它们的乘积就是T4。WSS关注的是同一个整数因子
$L_p-1$的精确 $p$-整除性；实嵌入的指数增长或收缩不决定这个因子模 $p^2$ 是否为零。

### T.5 向存在性推进时仍缺少的算术信息

本轮没有新增已解决的开放问题。新写入的是已有数论路线在本库的一个
精确接口。若仍以WSS存在性为目标，下一条应当引入关于实际整数环指标
$I_p=[\mathcal O_{K_p}:\mathbb Z[\theta_p]]$或素数迹商的跨素数约束，
而不能把再次改写 $q_p=0$ 的判据算成存在性进展。

文献给出的 $\operatorname{disc}(\mathcal P_p)=p^{2p}5^p$（奇素数 $p$）
和 $\operatorname{disc}(\mathcal P_p)=I_p^2\operatorname{disc}(K_p)$，
本身都不能强制 $I_p>1$。必须增加实际整数环、局部整性或跨素数分布的信息。
同样，改变二次域来构造某个固定 $p$ 的例外，不会证明固定黄金域
$\mathbb Q(\sqrt5)$ 中存在所需素数。McConnell [T-ref2] 的量词是固定一组素数、
改变域判别式；与当前目标保持区分。

高次周期规律、黄金单位范数及一阶迹约束均允许初始商为零或非零。
它们描述两个分支的后果，没有挑出哪一个素数必须处于零分支。
当前有意义的验收结果应是：实际给出且验证一个WSS素数；证明某个此前
未解决的无穷素数族的排除/存在结果；或找到并证明能约束初始商的新条件。
局部恒等式和有限回归测试只作为这些目标的工具。

### T.6 交付与来源

源：`D5/S1/Recurrence/GoldenTrinomialTraceObstruction.lean`。
配套：同名 `Blueprint/D5/S1/Recurrence/GoldenTrinomialTraceObstruction.scribe.cs`。
普通数学推导及源码逻辑复核完成；未执行 Lean/lake、Scribe 编译或kernel冻结。
独立整数诊断覆盖501个奇数下标、50100组模数关系，并用301个小素数检查
文献中的迹商/标准商关系。后者不计作新搜索界或WSS存在性证据。

[T-ref1] Lenny Jones, *A new condition for k-Wall-Sun-Sun primes*, Taiwanese Journal of Mathematics 28 (2024), 17–28; arXiv:2302.10357v4. Theorem 1.1, Proposition 2.5, Lemmas 3.4–3.5. https://arxiv.org/abs/2302.10357

[T-ref2] Gary McConnell, *Some new infinite families of non-p-rational real quadratic fields*, arXiv:2406.14632. https://arxiv.org/abs/2406.14632

[T-ref3] Richard J. McIntosh and Eric L. Roettger, *A search for Fibonacci-Wieferich and Wolstenholme primes*, Mathematics of Computation 76 (2007), 2087–2094. DOI 10.1090/S0025-5718-07-01955-2. Classical quotient characterizations are background, not a novelty claim in this appendix.

[T-ref4] 本仓 `D5/S1/Scale/Lucas.lean`、`D5/S0/Carrier/Norm.lean`、`Conj.lean`、`D5/S3/Arith/GoldenApparition.lean`；钉版 mathlib `Mathlib/Algebra/Polynomial/Eval/Defs.lean`，revision `db584cd6d46c92f209a44c0f1c829460d327499d`。
