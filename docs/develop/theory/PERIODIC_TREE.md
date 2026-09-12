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

## 8. 黄金连分数支：复位格点、镜面收缩与层际交换缺陷

### 8.1 对象与现有结果的衔接

本节挂载的是连分数 $[0;1,1,1,\ldots]$ 对应的黄金二次支。令

$$
\alpha=\frac{\sqrt5-1}{2},\quad \psi=-\alpha,\quad
\alpha^2+\alpha=1,\quad 0<\alpha<1,
$$

$$
A_L=F_{L+3},\quad B_L=F_{L+2},\quad C_L=F_{L+1},\quad
M_L=\begin{pmatrix}A_L&B_L\\B_L&C_L\end{pmatrix},\quad
d_L=\psi^{L+2},\quad \delta_L=|d_L|=\alpha^{L+2}.
$$

$L$ 遍历全部自然数。$M_L=Q^{L+2}$，其中
$Q=\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$。
Cassini 恒等式给出 $\det M_L=(-1)^L$。因此完整族在
$GL_2(\mathbb Z)$ 中，偶数层属于 $SL_2(\mathbb Z)$，奇数层反转定向。
不能把每个奇数层都写成行列式一的矩阵。

仓库已有 `D5/S1/Scale/FibonacciEigen.lean`，以及 mathlib 的
`Real.goldenConj_mul_fib_succ_add_fib`。本节复用这些黄金数和 Fibonacci
事实。复位问题的自然数定义及普通证明见
`CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md` 第 413–417 节；
第 419–431 节进一步研究有限观察与完整未来。以下新增 Lean 模块直接证明
Beatty 整数格点与相位窗口的双向关系，没有把未导入的数位后继定理装成假设字段。

来源定位：$T_L$ 属于广义 Beatty 序列族。
Allouche–Dekking 的 *Generalized Beatty sequences and complementary triples*
研究了 $p\lfloor n\varphi\rfloor+qn+r$ 及其互补划分。
这里确有

$$
T_L(m):=A_Lm+B_L\lfloor m\alpha\rfloor
=B_L\lfloor m\varphi\rfloor+C_Lm.
$$

因此本节不把标准 Fibonacci 恒等式、广义 Beatty 结构或纯点谱现象宣称为全新发现。
新增工作的目的，是把本项目指定的复位语义、全部分辨率、整数端点和观察损失
连接成可复用的证明链。

### 8.2 全整数格点与定向相位窗口的精确双向桥

对 $m,k\in\mathbb Z$，设

$$
\binom e h=M_L\binom m k.
$$

则

$$
\boxed{e\alpha-h=d_L(m\alpha-k).}\tag{GC1}
$$

证明：黄金共轭公式分别给
$B_L\alpha-C_L=-d_L$ 与 $A_L\alpha-B_L=\alpha d_L$。
展开线性组合即得等式。对应 `lattice_phase_identity`。

整数逆映射为

$$
\boxed{
 m=(-1)^L(C_Le-B_Lh),\qquad
 k=(-1)^L(A_Lh-B_Le).
}\tag{GC2}
$$

证明：乘回 $M_L$，用 $A_LC_L-B_L^2=(-1)^L$。
对应 `lattice_inverse`。保留 $h$ 是本桥的必要组成部分。

定义

$$
\operatorname{Hits}_L(e)
\iff \exists h\in\mathbb Z:\quad
0<\frac{e\alpha-h}{d_L}<1.
$$

则对全部 $L\ge0,e\in\mathbb Z$，

$$
\boxed{
\operatorname{Hits}_L(e)
\iff \exists m\in\mathbb Z\setminus\{0\}: e=T_L(m).
}\tag{GC3}
$$

证明：从右侧取 $k=\lfloor m\alpha\rfloor$。
无理性使 $0<m\alpha-k<1$，再用 GC1。反向用 GC2 恢复整数 $m,k$，
严格区间条件强制 $k=\lfloor m\alpha\rfloor$；$m=0$ 会要求一个整数
严格位于 $(-1,0)$，故被排除。对应 `hits_iff_entry`。

这是一条真实的双向表示定理。把它连接到原来的低位 Zeckendorf
额外复位，还须形式化第 415.2 节的数位模式到 $T_L(m)-1$ 的桥。
本节没有将这个尚未导入的桥标记为已机器闭合。

### 8.3 任意分辨率的收缩、奇偶与钟摆类比

有

$$
\boxed{d_{L+1}=-\alpha d_L,\qquad d_{L+2}=\alpha^2d_L.}\tag{GC4}
$$

任意固定间隔 $r>0$ 的有符号层际差
$D_{L,r}=d_L-d_{L+r}$ 满足

$$
\boxed{D_{L,r}\ne0,\qquad D_{L+1,r}=-\alpha D_{L,r}.}\tag{GC5}
$$

非零性来自 $|d_{L+r}|=|d_L|\alpha^r<|d_L|$。
对应 `relativeSeparation_ne_zero` 和 `relativeSeparation_succ`。
这覆盖全部 $L,r$，不依赖选择六、七、八位窗口。

这里与摆动有关的是一个在分辨率轴上交替变号、几何收缩的模式。
它没有断言自然时间满足单摆微分方程，也没有断言存在非零周期。
事实上，无理性给出

$$
\boxed{p\ne0\Longrightarrow p\alpha\notin\mathbb Z,\qquad p\in\mathbb Z.}\tag{GC6}
$$

对应 `no_nonzero_clock_period`。任意固定有限周期，包括 60 与 64，
均不可能成为完整黄金旋转的精确回归周期。

### 8.4 跨层事件覆盖及负时间端点

写 $u=(e\alpha-h)/d_L$。直接代数给

$$
\frac{e\alpha-h}{d_{L+2}}=\frac{u}{\alpha^2},\qquad
\frac{(e+B_L)\alpha-(h+C_L)}{d_{L+1}}=\frac{1-u}{\alpha}.
\tag{GC7}
$$

因此 $0<u<\alpha^2$ 属于 $L+2$ 层，
$\alpha^2<u<1$ 经 $B_L$ 位移属于 $L+1$ 层。
中间端点 $u=\alpha^2$ 不能略去。它强制

$$
\boxed{e=-F_{L+4}=T_L(-1).}\tag{GC8}
$$

证明：$u=\alpha^2$ 与第 $L+1$ 层黄金误差等式合并，得到
$(e+F_{L+4})\alpha=h+F_{L+3}$。无理性强制两个整数系数为零。
另外 $\lfloor-\alpha\rfloor=-1$，直接给出 $T_L(-1)=-F_{L+4}$。
对应 `seam_forces_negative_time` 与 `negative_one_entry`。

于是对每个 $e\ge0$，

$$
\boxed{
\operatorname{Hits}_L(e)
\iff\operatorname{Hits}_{L+2}(e)
\ \lor\ \operatorname{Hits}_{L+1}(e+B_L).
}\tag{GC9}
$$

对应 `resolution_cover_nonnegative`。在整数全域，同一等价式的
现有声明明确排除 $e=-F_{L+4}$。
Lean 的 GC9 声明是准确覆盖；事件不交性需要另一个声明，不从名称中推断。
既有 `hits_two_steps` 与 `hits_preceding_boundary` 还分别给出
同奇偶层的包含与相邻层的定向前驱。

这修正了把自然时间图直接延伸成双向时间图时容易遗漏的端点。
对 $L=6$，入时刻端点为 $e=-89$，相应出时刻为 $-90$；
不要把入时刻与出时刻混写。

### 8.5 嵌套时钟的精确组合与非交换缺陷

令

$$
c_L=\begin{cases}0,&d_L>0,\\1,&d_L<0.\end{cases}
$$

$d_L\ne0$，所以两分支完备。$c_0=0$ 且 $c_{L+1}=1-c_L$，
从而 $c_L$ 是分辨率的奇偶位。对于每个非零整数 $m$，

$$
\boxed{
\lfloor T_L(m)\alpha\rfloor
=B_Lm+C_L\lfloor m\alpha\rfloor-c_L.
}\tag{GC10}
$$

证明：GC1 的剩余量为 $d_L\{m\alpha\}$。
正向时它严格位于 $(0,1)$，反向时严格位于 $(-1,0)$。
取整因此恰损失 $c_L$。对应 `floor_entry`。

完整格点变换满足

$$
M_KM_L=M_{K+L+2}.
$$

源码 `lattice_composition` 用 GC1、幂乘法与残余映射的整数单射性证明该式。
其后代入 GC10，得到

$$
\boxed{
T_K(T_L(m))=T_{K+L+2}(m)-B_Kc_L,
\qquad m\ne0.
}\tag{GC11}
$$

对应 `entry_compose`。交换两个层级的顺序便有

$$
\boxed{
T_K(T_L(m))-T_L(T_K(m))=B_Lc_K-B_Kc_L.
}\tag{GC12}
$$

对应 `entry_commutator` 与 `entry_commute_iff`。
右侧独立于非零输入 $m$，所以一个有限的整数表达式决定全部非零输入上的交换性。
两层均为偶数时交换；一奇一偶时产生非零缺陷；两层均为奇数时，
缺陷是两个 Fibonacci 边界大小之差。$m=0$ 的辅助原点满足
$T_L(0)=0$，不能把 GC11 的非零域省略。

这里非交换的是带取整的嵌套返回映射。普通圆周平移仍然交换。
完整二维整数格点的组合、丢掉整数坐标后的取整，以及最终可见序列
是不同的层次。GC10–GC12 精确度量了这次投影留下的操作顺序信息。

### 8.6 实际 Fourier 积分、镜像与相对相位

对实数角频率 $\omega\ne0$，定义实际区间积分

$$
\mathcal F_\omega(a,b)=\int_a^b e^{-i\omega x}\,dx.
$$

所有公式使用负指数约定；$a>b$ 时使用定向积分。
mathlib 的 `integral_exp_mul_complex` 给出端点公式。由该公式证明

$$
\boxed{
\mathcal F_\omega(-b,-a)=\overline{\mathcal F_\omega(a,b)},\qquad
|\mathcal F_\omega(-b,-a)|^2=|\mathcal F_\omega(a,b)|^2.
}\tag{GC13}
$$

平移满足

$$
\mathcal F_\omega(a+t,b+t)=e^{-i\omega t}\mathcal F_\omega(a,b).
$$

定义交叉系数 $\mathcal C(z,w)=z\overline w$，共同平移的两个因子相消，
而共同反射使交叉系数取共轭：

$$
\boxed{
\mathcal C(z_t,w_t)=\mathcal C(z,w),\qquad
\operatorname{Im}\mathcal C(z^{\rm mir},w^{\rm mir})
=-\operatorname{Im}\mathcal C(z,w).
}\tag{GC14}
$$

对应 `coefficient_reflect`、`reflection_power_equal`、
`cross_common_translate`、`cross_reflect_im`。
此处零或实交叉系数不会分离镜像；GC14 没有假定它在每个频率都非零。

黄金触发区间的有符号实代表中心是 $d_L/2$。
GC5 证明，任意两个不同分辨率的中心都不能被同一个实平移同时吸收反射，
对应 `no_common_center_translation`。
相应未绕回的几何相位差 $-\omega(d_L-d_{L+r})/2$ 非零且逐层乘以 $-\alpha$。
这不是把一个实相位差未经模 $2\pi$ 检查就当作复振幅可分离的证明。

从这些空间积分走到自然时间的无限采样谱，仍须完成：
区间指示函数的轨道均值、端点约定、模式非零性以及可观测的有限样本误差。
现有 `D5/S1/Phase/CharacterAverage.lean` 证明的是每个非零单模的平均趋零，
不能单靠该文件就声称不连续脉冲的完整谱已经形式化。
Lenz–Spindeler–Strungaru 对纯点衍射与不同意义的概周期性作了系统区分，
这里也保持同样的收敛层级区别。

### 8.7 60、64与 Fibonacci 窗口各自的结构

必须同时给出载体及其操作，才有可检验的联系。

$$
R=\operatorname{Fin}(5)\times\operatorname{Fin}(3)
 \times\operatorname{Fin}(2)\times\operatorname{Fin}(2),\qquad |R|=60;
$$

$$
W_6=\{0,1\}^6,\quad |W_6|=64;\qquad
X_6=\{w\in W_6:w_jw_{j+1}=0\},\quad |X_6|=21.
$$

$60\to64$ 有明确的静态编码：

$$
\rho(x,y,z,w)=12x+4y+2z+w\in\{0,\ldots,59\}.
$$

商余恢复依次为 $w=\rho\bmod2$、$z=\lfloor\rho/2\rfloor\bmod2$、
$y=\lfloor\rho/4\rfloor\bmod3$、$x=\lfloor\rho/12\rfloor$。
把 $\rho$ 写成六位二进制，未使用的四个码为 60、61、62、63。
这四个余码没有被赋予新的生物学类别，也没有被当成时钟的四个动力方向。

$64\to21$ 则涉及指定 Fold 或合法语法选择；64 个字中有43个不满足
无相邻11的约束。34 是 $|X_7|$，也是 $|X_8|-|X_6|$，
不能充当该43的别名。诸如 $60/64$ 的静态利用率无法决定黄金旋转的周期或频谱。
GC6 对全部非零整数周期的排除，形式化了容量数与动力回归数之间的边界。
本节没有新增孤立的有限正例 Lean 模块来把这些计数包装成一般科研结果。

### 8.8 交付声明与继续研究的具体目标

四个 Lean 源模块与同路径 Blueprint Scribe 对应如下。

| 源模块 | 提供的全称证明目标 |
|---|---|
| `GoldenClockLattice` | 整数逆、双向 Hits/Beatty 等价、任意层收缩、前驱、无非零周期 |
| `GoldenClockResolutionCover` | 负端点定位、非负时间准确覆盖 |
| `GoldenClockComposition` | 完整格点复合、取整进位、全部非零输入的组合与交换判据 |
| `GoldenClockFourier` | 实际区间积分的镜像、功率、共同平移、交叉系数与实中心分离 |

路径统一在 `D5/S3/Observer/GoldenPrimeCircle/`；Scribe 在
`Blueprint/D5/S3/Observer/GoldenPrimeCircle/`。
源码提供证明项的构造，不把普通文档、有限数值检查或待编译的源文件标为 kernel 结论。

后续首先补齐真实 Zeckendorf 后继到 $T_L$ 的证明，使 GC9 与 GC12 能直接作用于
现役数位对象。第二个目标是从 GC10 的显式进位进一步推导多层组合的修正项，
检验哪些规范化仍保留顺序信息。第三个目标是针对一个固定的双层可观测量，
证明某个非零频段上的镜像分离与有限样本误差，不能只展示一张谱图。

更一般的二次无理数延伸，应保留其连分数矩阵及逐层共轭收缩系数。
黄金情况的一位取整修正不能无条件移植到任意二次族；需要重新证明剩余区间及取整范围。
这些都是带明确成功与失败条件的数学目标。

### 8.9 参考与形式化来源

1. J.-P. Allouche and F. M. Dekking, *Generalized Beatty sequences and complementary triples*,
   arXiv:1809.03424, 2018. https://arxiv.org/abs/1809.03424
2. D. Lenz, T. Spindeler and N. Strungaru, *Pure point diffraction and almost periodicity*,
   arXiv:2312.12825. https://arxiv.org/abs/2312.12825
3. D. Lenz, T. Spindeler and N. Strungaru, *Pure Point Diffraction and Mean, Besicovitch and Weyl
   Almost Periodicity*, arXiv:2006.10821. https://arxiv.org/abs/2006.10821
4. Mathlib, `Mathlib.NumberTheory.Real.GoldenRatio`, especially
   `goldenConj_mul_fib_succ_add_fib`; `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`,
   especially `integral_exp_mul_complex`.
5. 本仓 `D5/S1/Scale/FibonacciEigen.lean`、`D5/S1/Phase/CharacterAverage.lean`；
   `CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md` 第 413–431 节。
   PR #7288 与 #7326 的新增理论均明确区分普通证明和新增 Lean/kernel 认证。
