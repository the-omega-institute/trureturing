# 三读闭合与可见复几何

> 参考输入：AI 撰写的工作稿，由用户提供于本会话（2026-11-04，Asia/Singapore）。Lean 是仓库的数学真源；本文仅为参考文稿，未作形式化认证。

AURIC C133

将时钟关系从原历史移到二元读口

一个候选、完整等价定理、三维反例与量子规则的条件重构

固定源码：`4008fb9289d8`；提交时间：2026 年 11 月 4 日 20:30:01（新加坡）

**本轮结论。**
C132 把实二元预算与原空间的椭圆时钟关系结合，推出正性、对称性及复相容。
本轮进一步放宽原空间：不预给时钟可逆、周期或二次递推。
只要求在一次互读中，加入任意多份三时合计，仍然不超过原有预算。
它会迫使三时合计在全部比较读口中为零，复结构才在可见商上出现。
原始历史和档案仍可不同，甚至按非周期、不可逆的规则变化。

取实向量空间 $V$、任意实线性 $U$、任意实双线性 $R$，定义

$$
Q(f)=R(f,f),\qquad D=I+U+U^2.
$$

本轮唯一候选为

$$
\boxed{\quad
 2R(f,Ug+nDg)\le Q(f)+Q(g),
 \qquad f,g\in V,\ n\in\mathbb N.
 \quad}
$$

其中 $\mathbb N$ 包含零。若系统有多个内部读口，同一原则逐一作用于它们；
完整测试的分支合计关系则保留原来源的定义。

**一句白话。**
第二份内容向前挪一格，再添上多少份三读合计，与第一份互读时都不能多花预算；
如果某个合计仍有东西可读，反复添入它就一定会在某个比较方向上超支。

本稿证明：候选恰好选择代数商 $W=V/DV$ 上 Hermitian 正半定形式实部的全部拉回。
商上有

$$
\bar U^2+\bar U+I=0,\qquad
 J=\frac{I+2\bar U}{\sqrt3},\qquad J^2=-I.
$$

再去掉读数自身的根空间并完成，得到复 Hilbert 空间。
有限维时，若 $\dim_\mathbb R W=2k$，全部合法原始读数恰组成 $\operatorname{Herm}_k^+(\mathbb C)$ 的一个线性同构像。
因此不仅有一个构造，还可完整分类全部解及零边界。

**简化的准确含义。**
原全空间的时钟等式被放宽为读口中的零差关系；用等权三时合计时不需要预先写复数或选定实转角。
不过，所选三时关系仍决定复数类型。公式中的无界 $n$ 承担了新的代表检验，
因此没有证明独立约束数凭空减少，也没有把全部检验变成有限预定菜单。
三项是连续等权正向闭合菜单中首次产生非实二次类型的长度，未作跨所有语言的最小性断言。

**与最新项目的对应。**
最新相关新增 Lean 文件证明了成功、失败两帧上的统一动力学旋转。
原成功效果通常不与该旋转交换，不能直接把它当作所有效果共用的相位参照。
本稿给出具体预算违例，并保留活动平面、可读固定参考与完整档案的区别。
这是一项条件明确的数学重构；原程序是否满足候选仍有准确的来源义务。

## 目录

- [1. 固定来源与反向检验：动力学钟的适用范围](#section-1)
- [2. 三读零差预算：只约束读口，不预定原时钟](#section-2)
- [3. 可见商的完整分类与三维几何](#section-3)
- [4. 从内部读口重建效果，再接回量子规则](#section-4)
- [5. 定义关系、完整档案与观察者的可见范围](#section-5)
- [6. 本轮究竟回溯了什么，下一项来源证明是什么](#section-6)
- [参考文献](#references)

<a id="section-1"></a>

## 1. 固定来源与反向检验：动力学钟的适用范围

<a id="c133-source"></a>

### 1.1 本轮快照与实际新增内容

本轮仅核对一次默认分支 `dev`，固定于
[`4008fb9289d8`](https://github.com/the-omega-institute/trureturing/commit/4008fb9289d85582c68b23a5810474e4463c64ea)，
提交时间为 2026 年 11 月 4 日 12:30:01 UTC，即新加坡时间 20:30:01。
相对 C132 续篇的 `30817972a543`，
[固定两端比较](https://github.com/the-omega-institute/trureturing/compare/30817972a5439293f77c86f4a0aea3d45731083b...4008fb9289d85582c68b23a5810474e4463c64ea)
有 122 个新增可达提交，第一父链为 6 次合并。
关闭重命名推断后的真实整树净差分为 319 个路径：168 新增、148 修改、3 删除。
提交数由两页完整比较响应及父链核对，路径数取自 Git 树差分；
未把浅缓存的祖先日志或 API 的 300 文件上限当成完整计数。

`docs/develop/theory` 正文没有变化，概念动力学子树也没有变化；
Quantum 子树新增六份 Lean 文件。
其中与本轮最相关的是
[统一相干放大源码](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/D5/S3/Quantum/Recovery/CoherentUniformAmplification.lean)。
其余五份分别给
[单模 Rényi 函数的 Stieltjes 表示](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/D5/S3/Quantum/Analysis/BosonicRenyiStieltjes.lean)、
[其 Poisson 权重变换](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight.lean)、
[物理 Gaussian 协方差的 Rényi 强次可加性](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity.lean)、
[周期格上的有标签 bubble 放置计数](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy.lean)及
[rank-four 周期 MPS 的边界拼接与相位恢复](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection.lean)。
强次可加声明要求 $0<\alpha\le2$、$\alpha\ne1$ 及物理协方差；
bubble 模块不承担 Hamiltonian 本征态识别；MPS 的 raw Gram 已由复幅度形成。
这些结果均未给出本稿未预设正性的实读口 $R$。

### 1.2 新增两帧旋转：二次式成立在哪里

上述放大源码的 `frame_rotation` 与
`uniform_operator_rotation` 分别始于第 108、214 行。
其输入是有限复矩阵：等距源嵌入 $\iota$、酉 $C$、正交投影 $P$，以及

$$
U_0=C\iota,\qquad U_0^*U_0=I,\qquad
 (PU_0)^*(PU_0)=pI.
$$

在严格 $0<p<1$ 时，定义成功、失败两帧及同一反射乘积

$$
W=p^{-1/2}PU_0,\quad
 B=(1-p)^{-1/2}(I-P)U_0,\quad
 \mathsf Q=(2U_0U_0^*-I)(I-2P).
$$

记 $\theta=\arcsin\sqrt p$、$c=\cos2\theta=1-2p$、
$s=\sin2\theta=2\sqrt{p(1-p)}>0$。源码证明

$$
\begin{aligned}
W^*W=B^*B&=I, & W^*B&=0,\\
 \mathsf QW&=cW-sB, & \mathsf QB&=sW+cB.
\end{aligned}
$$

因此在活动空间 $M=\operatorname{ran}W\oplus\operatorname{ran}B$ 上，

$$
(\mathsf Q^2-2c\mathsf Q+I)|_M=0.
$$

这是全部源列共同的旋转，不是逐输入挑选一个反射；源码还证明全部幂及参考张量上的同一等式。
第 520 行的精确放大定理另用 coin、源逆调用和两种反射构造有限词。
这些条件模型不能替代原七地址菜单的实际供应，活动空间的多项式也不能直接覆盖完整档案。

**保留原成功读口，立即出现预算反例。**

由 $P^2=P$ 有 $PW=W$、$PB=0$，所以

$$
[P,\mathsf Q]W=sB,\qquad [P,\mathsf Q]B=sW.
$$

若源非零，两帧等距给 $[P,\mathsf Q]\ne0$。
这里必须写明非零源：Lean 的有限指标类型本身没有排除空源。
取源中单位向量 $\xi$，保留原效果 $P$ 的实读口

$$
R_P(u,v)=\operatorname{Re}\langle u,Pv\rangle,
 \qquad q_P(u)=R_P(u,u).
$$

令 $f=sW\xi$、$g=B\xi$，直接得到

$$
\boxed{\quad
 2R_P(f,\mathsf Qg)=2s^2>s^2=q_P(f)+q_P(g).
 \quad}
$$

这已经违反本稿预算的 $n=0$ 情形，与后来选择哪一个残差无关。
两帧在 $\xi$ 上也由 $U_0\xi,\mathsf QU_0\xi$ 的实线性组合张成，
换基行列式非零；这里无需增添免费的成功、失败制备。
若配方限于有理系数，严格违例可由有理逼近保留，再清分母成为整数配方。

故这份动力学门 $\mathsf Q$ 不能直接充当全部合法效果共用的中央相位钟。
对这个读口要求共同 $\mathsf Q$ 不变，等价于
$\mathsf Q^*P\mathsf Q=P$，也就是 $[P,\mathsf Q]=0$，与上式冲突。
不能为维持预算而删除原成功效果。
$p=1$ 是另一个退化端点：源码单列 $U_0=W$，不沿用非零失败帧及上述二维反例。

### 1.3 旧来源中不能省去的条件

**常数模式与未知读数。**

[V24 引理 7.2](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/docs/develop/theory/AURIC_TWO_BASIS_STATES_THREE_CHANNELS_PHASE_CHIRALITY_AND_RECURSIVE_SQUARE_LAW_V24.md)
对已给二谱门与二次读出得到

$$
a_t=a+b\zeta^t+\overline b\zeta^{-t},\qquad
 \zeta=e^{3\pi i/5},\qquad
 (z-1)(z^2+\phi^{-1}z+1).
$$

最后一式是完整序列的三次消去多项式；二阶因子只负责旋转部分。
故三时中心化必须说明如何保存固定部分。
本稿 $I+U+U^2$ 的 $120^\circ$ 可见商是本轮的选择，
不等于原黄金门已经换成三阶门；一般加权残差中的 $\lambda=\phi^{-1}$ 才对应上述系数。

[C117 定义 17.1–17.3、18.2 及第 29 节](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md)
另要求未知响应在全部合法前后文、原完整标签和实际可访问旧记录上保持方向充分性、连续性与四时关系。
方向矩阵满足恒等式，不会自动使未知读数保持它。
命题 16.7 的原七地址四前缀表还证明：任意做 $2p-1$ 中心化可能破坏 Gram 正性。
这与已经建立正核后的正交分解不同。
其第 25 节的共同正性修复仍要求整个原图的固定有限非负正字生成，
不能由一只有限菜单或少数准确样本补出。

**已有零接触与复结构路线。**

[C123 定义 35.2、定理 36.1](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)
已有 $\alpha(x)=0\Rightarrow\alpha(D_ax)=0$ 的 Z 条件。
其等价证明保留有限 EJA、P/G、完整正对偶包和实际参考；
这是正锥边界的零接触，不是未正定 $R$ 中三时配方归零的证明。
[C115 的同空间结合闭包](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/docs/develop/theory/AURIC_BINARY_SQUARE_TWO_COMPONENT_COMPOSITION_AND_INTERNAL_COMPLEX_STRUCTURE_C115.md)与
[V62 的忠实六方向校准](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/docs/develop/theory/AURIC_REAL_THREE_AXIS_POSITIVE_REFINEMENTS_AND_COMPLEX_QUANTUM_INTERFACE_V62.md)
虽已内生 $J$，仍分别保留实正几何、乘法表示或忠实正校准。
[V74 定理 3.2](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/docs/develop/theory/AURIC_SMOOTH_QUANTUM_HISTORIES_COTANGENT_DYNAMICS_AND_ENDOGENOUS_MOTION_V74.md)
则从全域光滑、有限秩复正核及共同平移开始。
因此，后文 raw 关系预算的推导是 C133 的证明责任，不能归于这些源码已证的原生接口。

**比较商与完整档案。**

C123 定义 1.1 只对全语境响应取商，原装置身份、记录和合法性保留。
[History Records 第 144、148、191–194 节](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/docs/develop/theory/AURIC_FIB_HISTORY_RECORDS_TIME_ARROW.md)
进一步区分可追回的追加档案、任务信息和有限窗口。
固定读口中的零差不能抹去未来仍可读出的档案区别；日志追加也不唯一选择旋转手性。
本轮若在可见商中得到周期，完整隐藏档案仍须按原合同保留。

**核读范围。**

第一阶段 15 份原文均核对固定 Git blob；其中新增放大 Lean 全文核读，
其余六份 Lean 按定义、主声明及相关局部证明核读，八份理论文稿只复核指定区间。
第六节另补核三份数字与缺口 Lean 全文，确认其在 C132 前后和本轮固定版本的 blob 完全相同；
累计 18 份原文，范围仍按各文件所列区间限定。
未运行新的 Lean 构建，未访问私人证书库，也未认证全仓库或全部实际物理接口。

<a id="section-2"></a>

## 2. 三读零差预算：只约束读口，不预定原时钟

<a id="c133-core"></a>

本轮撤去原空间上的时钟二次式。原历史可以保留不可读的分量，原推进也可以不可逆、没有周期；递推关系只在当前读口的零差商中成立。代价是检查全部重写倍数，不能把公式写成一行就宣称独立条件的数量消失。

### 定义 2.1（唯一候选）

<a id="c133-data"></a>

给定实向量空间 $V$、任意实双线性读数 $R$ 及任意实线性推进 $U$。只定义
$Q(f)=R(f,f)$、$D=I+U+U^2$，不预设 $D=0$。
本轮的**三读零差预算**为

<a id="c133-axiom"></a>

$$
\boxed{\quad
 2R(f,Ug+nDg)\le Q(f)+Q(g)
 \quad(f,g\in V,\ n\in\mathbb N=\{0,1,\dots\}).\quad}
 \tag{C133}
$$

其中 $f,g$ 独立；$Dg=g+Ug+U^2g$ 是三时配方的合计，$n$ 是有限的重写倍数。

这仍保留实数、双线性与有限配方聚合。形式配方不自动等于可制备状态，$Dg$ 也不是三个概率之和。候选量化的是一个固定二元读口对不同配方的比较。

### 定理 2.2（原始读数的完整等价）

<a id="c133-equivalence"></a>

条件 [(C133)](#c133-axiom) 等价于：$R$ 对称半正定，$Q(Uf)=Q(f)$，并且

$$
D(V)\subset\mathcal N,\qquad
 \mathcal N=\{f:Q(f)=0\}=\{f:R(f,g)=0\ \forall g\}.
$$

因此原始 $U$ 不必可逆或满足 $U^3=I$；这些结论只对可见商上的推进成立。

**证明。**
**先迫出二元零差。**固定 $f,g$，令 $n\to\infty$，预算给
$R(f,Dg)\le0$；将 $f$ 换成 $-f$ 得反向，故 $R(f,Dg)=0$。
取 $g=0$ 又得 $Q(f)\ge0$。令 $L=D(V)$。若 $h\in L$，则
$R(f,h)=Q(h)=0$，所以
$Q(f+th)=Q(f)+tR(h,f)\ge0$ 对所有实 $t$ 成立，迫使 $R(h,f)=0$。
因此 $L$ 已是双侧读数零空间，而非仅仅自读为零。

**只在源关系商中使用三步闭合。**因为 $UD=DU$，$L$ 对 $U$ 稳定。读数与推进都下降到 $W=V/L$，记为 $r,T$，自读记为 $q$。此时才有
$I+T+T^2=0$，从而 $T^3=I$。
预算的 $n=0$ 项仍成立；取第一配方为 $Tg$，得 $q(Tg)\le q(g)$。三步给

<a id="c133-three-cycle"></a>

$$
q(g)=q(T^3g)\le q(T^2g)\le q(Tg)\le q(g),
\tag{1}
$$

故每步都等距。

**取等位置附近迫使对称。**在预算中取 $f=Tg+tv$，其余量为

<a id="c133-symmetry"></a>

$$
t\bigl[r(Tg,v)-r(v,Tg)\bigr]+t^2q(v)\ge0.
\tag{2}
$$

任意正负 $t$ 使一次项为零；$T$ 可逆，所以 $r$ 对称。因此原 $R$ 也对称半正定，且 $Q\circ U=Q$。正半定形式中，$Q(h)=0$ 由
$Q(h+tg)\ge0$ 迫出 $R(h,g)=0$，故完整零差恰为所述 $\mathcal N$，且包含 $L$。

反向，$R$ 正半定使 $Dg\in\mathcal N$ 成为所有读口的零差；因 $U$ 等距，预算余量为

<a id="c133-deficit-square"></a>

$$
Q(f)+Q(g)-2R(f,Ug+nDg)=Q(f-Ug)\ge0.
\tag{3}
$$

等价成立。

原空间仅有恒等式

$$
U^3-I=(U-I)D,\qquad
 J_0=\frac{I+2U}{\sqrt3},\qquad J_0^2+I=\frac43D.
$$

不能在取商前将右端写成零。另一方面，预算证明后，三份自读之和是
$Q(g)+Q(Ug)+Q(U^2g)=3Q(g)$；三读合计成为零差，绝不表示三份非负概率相加为零。

### 2.1 可见复结构、完整零差与模型分类

### 定理 2.3（内积表示与完成）

<a id="c133-hilbert"></a>

在 $V/\mathcal N$ 上，推进 $T=[U]$ 是等距同构，且
$J=(I+2T)/\sqrt3$ 满足 $J^2=-I$。以 $if=Jf$ 定义复数乘法后，唯一实部为原读数的复内积由

<a id="c133-complex-reading"></a>

$$
B(f,g)=R(f,g)+iR(J_0f,g)
\tag{4}
$$

下降得到。其完成 $\mathcal H$ 有实线性稠密表示 $\iota:V\to\mathcal H$，满足

$$
R(f,g)=\Re\langle\iota f,\iota g\rangle,\qquad
 \iota(Ug)=\zeta\,\iota(g),\quad
 \zeta=-\tfrac12+i\tfrac{\sqrt3}{2},\quad\operatorname{ker}\iota=\mathcal N.
$$

保持原配方稠密像的完成唯一到酉等价。

**证明。**
$Q\circ U=Q$ 使 $\mathcal N$ 对 $U$ 稳定；商上 $I+T+T^2=0$，所以 $T^{-1}=-I-T$。实极化先给 $T$ 保持内积。将
$r(Tf,g)=r(f,T^{-1}g)$ 代入 $J$，得到
$r(Jf,g)=-r(f,Jg)$ 与 $r(Jf,Jg)=r(f,g)$。
因此式 [(4)](#c133-complex-reading) 第一槽共轭线性、第二槽线性，且 Hermitian，自读为 $Q$。其虚部被实部唯一固定为 $R(J_0f,g)$。

若 $Q(g)>0$，在该商空间的 $Q(f+tg)\ge0$ 中取复数
$t=-\overline{B(f,g)}/Q(g)$；若 $Q(g)=0$，则用根空间结论。两种情形均给

<a id="c133-cauchy-schwarz"></a>

$$
|R(f,g)|^2\le |B(f,g)|^2\le Q(f)Q(g).
\tag{5}
$$

因此商内积可完成。原配方在任意两个完成中的对应等距，因稠密而唯一延伸为酉映射。

### 推论 2.4（全部模型的精确范围）

<a id="c133-classification"></a>

固定原 $V,U$，先作代数商 $W=V/D(V)$，其复结构由 $(I+2[U])/\sqrt3$ 给出。所有合格 $R$，恰是 $W$ 上任意 Hermitian 半正定形式的实部拉回。若 $\dim_\mathbb C W=k<\infty$，该模型族与 $\operatorname{Herm}_k^+$ 一一对应。

**证明。**
正向由上述证明。反向在任一这样的复形式中，$[Ug+nDg]=\zeta[g]$，预算就是平方范数非负。正形式还可有自身的零空间；再商去它，才是完整的 $V/\mathcal N$。

零形式始终合格，概率归一没有被偷偷加入。严格弱化也有具体模型：在一个正二维旋转平面旁接任意不可读空间，令 $R$ 只读前者，$U$ 在后者上任意作用。取后者上的 $U=0$，原推进不可逆且原 $D\ne0$，预算依然成立。数学商只表达这个读口看不出的差别，不删除原历史或封闭日志。

### 2.2 两个不可省去的检查条件

**自读零不能代替全部二元读口零。**
取 $V=\mathbb R^2\oplus\mathbb R^2$，$A$ 为前一个平面上的 $120^\circ$ 旋转，并令

$$
R((w,a),(v,b))=w\cdot v+a_1b_2-a_2b_1,\qquad
 U(w,a)=(Aw,0).
$$

此时 $Q(w,a)=\|w\|^2$，原单移位预算全部成立，且
$D(w,a)=(0,a)$，所以 $Q(Dg)=R(g,Dg)=0$ 对所有 $g$ 成立。
然而 $R$ 在第二个平面仍是非零交替形式。取 $f=(0,e_1)$、$g=(0,e_2)$、$n=1$，本轮预算立即变成 $2\le0$。仅测自读，会把仍能交叉读出的关系误当成零。

**有限重写菜单不能认证精确递推。**
给任意 $N\ge0$，在实平面上取点积，用复坐标计算该平面的实算子。令
$\varepsilon=(2+4N^2)^{-1}$、$r=1-\varepsilon$，$U$ 为乘 $r\zeta$。
对 $0\le n\le N$，$U+nD$ 的乘数 $a_n$ 满足

$$
\zeta^{-1}a_n
 =r-\tfrac n2\varepsilon^2
 -i\tfrac{\sqrt3}{2}n(1-r^2),\qquad
 |a_n|^2\le1-2\varepsilon+(1+4N^2)\varepsilon^2<1.
$$

所以这些算子全部严格收缩，每个有限菜单预算都对任意两份配方成立。
但 $D(U)\ne0$，因为 $r\zeta$ 不在单位圆上。无界 $n$ 因而确有承重作用；若某个 $R(f,Dg)\ne0$，选择 $f$ 的符号再取有限大的 $n$，就能取得严格失败见证。

### 2.3 三读的限定最小性与黄金来源桥

### 命题 2.5（等权连续时点菜单中的最早复结构）

<a id="c133-minimal-menu"></a>

只在预先限定的菜单
$D_m=I+U+\cdots+U^{m-1}$ 中比较同一预算的闭合项，则：$m=1$ 迫 $R=0$；$m=2$ 只选出实正形式；$m=3$ 首次在非零可见商上强制复时钟代数。

**证明。**
同样令重写倍数无界，得到 $D_m(V)$ 为双侧零差。
$m=1$ 时全部读数为零。
$m=2$ 时商上 $U=-I$，预算经 $g\mapsto-g$ 成为普通实二元预算；它迫出对称半正定，却允许实一维模型 $R(f,g)=fg$。
$m=3$ 时，商上时钟多项式为不可约的 $t^2+t+1$，其非零时钟代数是 $\mathbb R[t]/(t^2+t+1)\cong\mathbb C$，前述定理给出兼容内积。

这个最小性不覆盖别的菜单。若允许跳过中间时点，两个非零项 $I+U^2$ 就能指定四分之一转动；因此不能宣称三个项是所有量子重构的全局最少原语。

同一证明还有一个加权来源桥：把闭合项写成
$D_\lambda=I+\lambda U+U^2$，$|\lambda|<2$，则先在零差商上得到相应二次式，随后

<a id="c133-weighted-bridge"></a>

$$
c=-\frac\lambda2,\qquad
 J=\frac{2[U]+\lambda I}{\sqrt{4-\lambda^2}}.
\tag{6}
$$

此时以两平面恒等式
$q(Tv)+q(TJv)=q(v)+q(Jv)$ 代替三步回路：它由
$T=cI+sJ$、$TJ=-sI+cJ$ 展开得到，再与两条收缩不等式合用便迫等距。其余证明不变。这是同一预算结构的参数桥，正文唯一选定的是 $\lambda=1$ 的等权三读。

旧黄金前端对应 $\lambda=\alpha=1/\phi$，其中 $\phi=(1+\sqrt5)/2$。若原来源另给
$c=1-2p$，则 $\lambda=4p-2$，椭圆范围为 $0<p<1$，主三读对应 $p=3/4$。这里的 $p$ 只按其来源定义使用，不能未经概率接口就称为 Born 概率。
复数类型仍被所选闭合模式编码；本轮撤去的是原日志整体必须服从该递推的要求。

**白话。**先保留全部历史，不规定整个世界必须三步返回。拿一份历史和它的两次推进组成三读合计，把这份合计反复加进一次推进的写法里；无论另一个读口怎么比较，互读都不能超过两份自读预算的平均值。只要三读合计还能被某个读口读出，选好比较方向、重复足够多次就会超支，所以它必须成为这个读口的零差。只有在这些零差合并后的可见层，三步才闭合、每步才等距，实读数才拼成复内积。原来的日志仍在，三份单独读数也没有消失。

<a id="section-3"></a>

## 3. 可见商的完整分类与三维几何

<a id="c133geo-section"></a>

记 $D=I+U+U^2$，$\pi:V\to W:=V/DV$ 为代数商映射。定理~[2.2](#c133-equivalence) 使合法读数先下降到 $W$，再商去自身的零差。以下始终保留原始载体 $V$；在读数中识别两个代表，不删除它们原有的记录标签。

### 3.1 全部有限维模型恰是一族复正锥

### 定理 3.1（有限维完整分类）

<a id="c133geo-classification"></a>

设 $V$ 有限维，$U$ 任意。商算子 $\bar U$ 在 $W$ 上满足

$$
I+\bar U+\bar U^2=0,\qquad
 J=\frac{I+2\bar U}{\sqrt3},\qquad J^2=-I.
$$

因此

<a id="c133geo-visible-dimension"></a>

$$
\dim_{\mathbb R}W=2k,\qquad
 k=\frac{\dim_{\mathbb R}V-\operatorname{rank}_{\mathbb R}D}{2}.
\tag{7}
$$

选取由 $J$ 定义的复坐标 $\ell:V\to\mathbb C^k$，使
$\operatorname{ker}\ell=DV$、$\ell U=\omega\ell$，其中 $\omega=e^{2\pi i/3}$。
则满足候选~[(C133)](#c133-axiom) 的全部 $R$ 恰为

<a id="c133geo-all-readings"></a>

$$
R(f,g)=\Re\!\left(\ell(f)^*H\ell(g)\right),
 \qquad H=H^*\succeq0.
\tag{8}
$$

这个对应一一成立，且

<a id="c133geo-rank"></a>

$$
\operatorname{rank}_{\mathbb R}R=2\operatorname{rank}_{\mathbb C}H\le2k.
\tag{9}
$$

特别地，$D$ 可逆当且仅当唯一合法读数是 $R=0$。

**证明。**
$DV$ 对 $U$ 稳定，而 $D$ 在商上为零；直接平方给 $J^2=-I$。于是令 $iw=Jw$，$W$ 成为 $k$ 维复空间，$\bar U$ 是乘 $\omega$。内部复化的标准构造见  [7](#ref-moretti2017)。
主等价定理把合法 $R$ 与 $W$ 上的 Hermitian 正半定形式一一对应，选复基后正好得到式~[(8)](#c133geo-all-readings)。
复正半定形式的每个非零方向给两个非零实方向；拉回所用的 $\ell$ 满射，故实秩为复秩的两倍。
若 $k=0$，只剩零形；若 $k>0$，取 $H=I$ 即得非零解。

所以指定原时钟后，并非任意方向都能被这个读口读取。$D$ 可逆的源根本没有非零合法读口；若 $k>0$，全部选择恰组成 $\operatorname{Herm}_k^+(\mathbb C)$。实际零空间为
$\mathcal N=\ell^{-1}(\operatorname{ker} H)\supseteq DV$；只有 $H$ 正定时才恰为 $DV$。
这给出了完整模型族，同时保留了源是否供应非零读口这一问题。

### 3.2 商不是原空间里的特征平面

### 例 3.2（有旋转商，却没有不变补空间）

<a id="c133geo-jordan"></a>

令

$$
A=\begin{pmatrix}-\tfrac12&-\tfrac{\sqrt3}2\\
                  \tfrac{\sqrt3}2&-\tfrac12\end{pmatrix},
 \qquad
 V=\mathbb R^2\oplus\mathbb R^2,\qquad
 U(x,y)=(Ax+y,Ay).
$$

由于 $I+A+A^2=0$，直接计算得

<a id="c133geo-jordan-residual"></a>

$$
D(x,y)=((I+2A)y,0),\qquad
 \operatorname{ker} D=\operatorname{Ran} D=\mathbb R^2\oplus\{0\}.
\tag{10}
$$

这里 $I+2A$ 可逆。取
$R((x,y),(x',y'))=y\cdot y'$，便得到合法读数；第一平面全部不可读，可见商由第二坐标 $y$ 表示，商上的时钟为 $A$。

这个例子的 $\operatorname{ker} D$ 恰是全不可读的第一平面，因此不能用 $\operatorname{ker} D$ 代替 $V/DV$。甚至不存在与第一平面互补的 $U$ 不变空间：若某个补空间写成 $x=Ty$，不变性要求
$TA-AT=I$，取迹却得到 $0=2$。第二坐标只是商坐标，并非原空间中的不变旋转平面。原过程仍可满足
$U^3(x,y)=(x+3A^2y,y)$，同时可见商严格三步闭合。

### 3.3 三条原始记录怎样读成一个三角形

继续使用上例的 $120^\circ$ 旋转矩阵 $A$，取更易画出的三维模型

<a id="c133geo-three-dimensional-source"></a>

$$
V=\mathbb R^2\oplus\mathbb R,\qquad U(x,z)=(Ax,2z),\qquad
 R((x,z),(y,w))=x\cdot y.
\tag{11}
$$

其 $D(x,z)=(0,7z)$ 对当前读口不可见，而 $U^3(x,z)=(x,8z)$。取 $v=(1,0,1)$，则

$$
v=(1,0,1),\qquad
 Uv=(-\tfrac12,\tfrac{\sqrt3}2,2),\qquad
 U^2v=(-\tfrac12,-\tfrac{\sqrt3}2,4).
$$

原始三向量不合为零：它们留下 $Dv=(0,0,7)$。在当前读数商中，三者等长、两两夹角 $120^\circ$，比较表为

<a id="c133geo-triangle-gram"></a>

$$
G=\begin{pmatrix}
 1&-\tfrac12&-\tfrac12\\
 -\tfrac12&1&-\tfrac12\\
 -\tfrac12&-\tfrac12&1
 \end{pmatrix}\succeq0,\qquad
 \operatorname{spec}G=\{0,\tfrac32,\tfrac32\}.
\tag{12}
$$

<a id="c133geo-source-visible-figure"></a>

```latex
\begin{tikzpicture}[font=\small,>=Latex]
 \path[use as bounding box] (-0.10,-0.25) rectangle (12.10,4.95);
 \node at (2.18,4.65) {原始三维：第三坐标仍在变化};
 \begin{scope}[xshift=2.08cm,yshift=1.13cm,
   x={(1.20cm,0cm)},y={(0.45cm,0.45cm)},z={(0cm,0.59cm)}]
  % Every curve below lies exactly on x^2+y^2=1.
  \draw[teal!25,domain=0:360,samples=121,variable=\ang]
   plot ({cos(\ang)},{sin(\ang)},0);
  \draw[teal!16,domain=0:360,samples=121,variable=\ang]
   plot ({cos(\ang)},{sin(\ang)},4.35);
  \draw[teal!16] (1,0,0)--(1,0,4.35);
  \draw[teal!16] (-1,0,0)--(-1,0,4.35);
  \draw[black!40,->] (0,0,0)--(1.58,0,0) node[below] {$x$};
  \draw[black!40,->] (0,0,0)--(0,1.58,0) node[right] {$y$};
  \draw[black!45,->] (0,0,0)--(0,0,4.80) node[above] {$z$};
  \foreach \h in {1,2,4}{
    \draw[black!45] (-0.035,0,\h)--(0.035,0,\h);
    \node[font=\scriptsize,anchor=east] at (-0.065,0,\h) {$\h$};
  }
  \coordinate (vzero) at (1,0,1);
  \coordinate (vone) at (-0.5,{sqrt(3)/2},2);
  \coordinate (vtwo) at (-0.5,{-sqrt(3)/2},4);
  \draw[blue!55,densely dashed] (1,0,0)--(vzero);
  \draw[orange!65!black,densely dashed] (-0.5,{sqrt(3)/2},0)--(vone);
  \draw[purple!60,densely dashed] (-0.5,{-sqrt(3)/2},0)--(vtwo);
  \draw[blue!70!black,thick,->] (0,0,0)--(vzero);
  \draw[orange!80!black,thick,->] (0,0,0)--(vone);
  \draw[purple!75!black,thick,->] (0,0,0)--(vtwo);
  \fill[blue!70!black] (vzero) circle[radius=1.6pt];
  \fill[orange!80!black] (vone) circle[radius=1.6pt];
  \fill[purple!75!black] (vtwo) circle[radius=1.6pt];
  \node[anchor=west,blue!70!black] at (1.04,0,1.04) {$v$};
  \node[anchor=west,orange!80!black,fill=white,inner sep=1pt]
   at (-0.38,{sqrt(3)/2},2.07) {$Uv$};
  \node[anchor=east,purple!75!black] at (-0.56,{-sqrt(3)/2},4.05) {$U^2v$};
 \end{scope}
 \node[font=\footnotesize] at (2.18,0.34) {$Q=1:\ x^2+y^2=1$};
 \node[font=\footnotesize] at (2.18,-0.03) {$Dv=(0,0,7)$};

 \draw[black!55,->,thick] (4.47,2.43)--(7.06,2.43);
 \node[font=\footnotesize,align=center] at (5.76,3.11)
  {$\pi(x,y,z)=(x,y)$};
 \node[font=\footnotesize] at (5.76,1.94) {当前读数的商};

 \node at (9.45,4.65) {可见二维：三角形与相位圆};
 \begin{scope}[xshift=9.45cm,yshift=2.43cm,x=1.42cm,y=1.42cm]
  \fill[teal!5] (0,0) circle[radius=1.42cm];
  \draw[teal!55!black] (0,0) circle[radius=1.42cm];
  \draw[black!28,->] (-1.18,0)--(1.35,0);
  \draw[black!28,->] (0,-1.18)--(0,1.21);
  \coordinate (pzero) at (1,0);
  \coordinate (pone) at (-0.5,{sqrt(3)/2});
  \coordinate (ptwo) at (-0.5,{-sqrt(3)/2});
  \draw[teal!65!black,thick] (pzero)--(pone)--(ptwo)--cycle;
  \draw[blue!65!black,->] (0,0)--(pzero);
  \draw[orange!75!black,->] (0,0)--(pone);
  \draw[purple!70!black,->] (0,0)--(ptwo);
  \fill[blue!70!black] (pzero) circle[radius=1.6pt];
  \fill[orange!80!black] (pone) circle[radius=1.6pt];
  \fill[purple!75!black] (ptwo) circle[radius=1.6pt];
  \node[anchor=west,blue!70!black] at (1.06,0.09) {$\pi v$};
  \node[anchor=south east,orange!80!black] at (-0.55,0.92) {$\pi Uv$};
  \node[anchor=north east,purple!75!black] at (-0.55,-0.92) {$\pi U^2v$};
  \node[anchor=north west,font=\scriptsize] at (0.035,-0.025) {$0$};
 \end{scope}
 \node[font=\footnotesize] at (9.45,0.34) {$\pi v+\pi Uv+\pi U^2v=0$};
 \node[font=\footnotesize] at (9.45,-0.03) {$\|\pi v\|=\|\pi Uv\|=\|\pi U^2v\|=1$};
\end{tikzpicture}
```

**图 1。**精确模型~[(11)](#c133geo-three-dimensional-source)。左侧三个高度 $1,2,4$ 是原始记录的第三坐标；浅色线位于自读单位柱面。右侧只画当前读口保留的两坐标。三时关系在右侧闭合，左侧保留非零余项；图中没有删除原始记录。

自读单位面在原空间是柱面 $x^2+y^2=1$，商中才是单位圆。对可见非零 $u$，二元配方满足

$$
\|au+b\bar Uu\|^2
 =\|u\|^2(a^2-ab+b^2)
 =\|u\|^2\bigl((a-b/2)^2+3b^2/4\bigr).
$$

这里的交叉系数是 $-1$；改用实正交坐标就得到圆。若另一读口能读第三坐标，本次商便不能直接沿用。

### 例 3.3（可读的固定轴不能借中心化删除）

<a id="c133geo-visible-fixed-axis"></a>

将原时钟改为 $U=A\oplus1$，并把 $R$ 改成全三维欧氏内积。这个 $U$ 已经满足 $U^3=I$，普通单移位预算也成立；但固定轴可读，$De_3=3e_3$。取 $f=g=e_3,n=1$，候选给

$$
2R(e_3,Ue_3+De_3)=8>2=Q(e_3)+Q(e_3).
$$

因此本轮候选明确拒绝这个读口。有限周期本身不保证三时余项不可读，投影前必须核验该余项确实没有当前读数。

### 3.4 一个相位平面怎样扩大为量子比特几何

上图三条可见向量属于同一复线，只有一复维，尚不是量子比特。在非退化可见空间中记实内积为 $g$。给非零 $u$ 与另一方向 $v$，令
$p=g(u,u)$、$q=g(v,v)$、$x=g(u,v)$、$y=g(Ju,v)$，则

$$
G_{\mathbb R}(u,Ju,v)=
 \begin{pmatrix}p&0&x\\0&p&y\\x&y&q\end{pmatrix}\succeq0.
$$

令 $w=v-(x/p)u-(y/p)Ju$。若 $w=0$，仍只有一复维；若 $w\ne0$，由 $J^*=-J$、$J^*J=I$ 得
$Jw\perp u,Ju,w$ 且 $\|Jw\|=\|w\|$。所以三实方向窗口须再补第四方向，最小闭合为
$\operatorname{span}_{\mathbb R}\{u,Ju,w,Jw\}\cong\mathbb C^2$。它描述关系方向，不指定物理空间维数。

在这个两复维窗口中，二阶 Hermitian 正锥的迹一截面为

$$
\rho=\frac12
 \begin{pmatrix}1+Z&X-iY\\X+iY&1-Z\end{pmatrix},
 \qquad \rho\succeq0\iff X^2+Y^2+Z^2\le1.
$$

本征值为 $(1\pm\sqrt{X^2+Y^2+Z^2})/2$，故球面是秩一，内部是秩二；零表仍是不可归一的原锥顶 [11](#ref-arrighi2002)。
单位二分量 $(\xi,\eta)$ 的球面坐标为
$(2\Re(\bar\xi\eta),\,2\Im(\bar\xi\eta),\,|\xi|^2-|\eta|^2)$。
这些坐标固定两模与相对相位，包含两极在内只剩公共相位圆的纤维，因此给出
$S^3/U(1)=S^2$ [10](#ref-mosseri2001)。这里是几何分类；物理读数的接口由后文另行核验。

**白话。**原来的三条记录可以一边转、一边留下越来越不同的第三坐标。我们没有让它们在原世界里强行相等，只要求当前这个读口确实看不见三条记录合计留下的方向。这样，读出来的三条边才闭成等边三角形，三角形所在的平面给出复相位。如果那根第三轴本来可以读到，就不能抹去它。一份相位平面还只有一个复方向；第二份独立内容进来后，才需要四个实方向，并出现量子比特的球面几何。

<a id="section-4"></a>

## 4. 从内部读口重建效果，再接回量子规则

<a id="c133-quantum"></a>

主定理处理任意一个实双线性读口。要发展完整理论，须让同一原则覆盖实际读口族，
并保留完整事件的合计关系。本节先从读口重建效果算子，再给出有限维概率、过程、复合与时间的条件链。
实际可调用的读口或控制仍可能只是数学允许类的一个子集。

### 4.1 完整分支如何自己产生效果算子

### 定义 4.1（读口族与完整测试）

设 $\mathcal E$ 为原事件读口集合，包含总读口 $1$ 与空读口 $0$。
每个 $e$ 给实双线性 $R_e$；$R_0=0$。本节的完整测试和仪器分支族均为有限。
实际完整测试 $\{e_j\}$ 满足

$$
\sum_jR_{e_j}=R_1.
$$

若 $e$ 与其补读口 $\bar e$ 形成完整测试，则 $R_e+R_{\bar e}=R_1$。
相同事件在合法细分、合并中的读数对应沿用原定义，不通过删去失败支获得归一化。
对每个 $R_e$ 都要求同一候选~[(C133)](#c133-axiom)，并使用同一个 $U$。

### 定理 4.2（效果由二元读口重建）

<a id="c133-effects"></a>

以总读口 $R_1$ 的完整零差商及完成为 $\mathcal H$，实内积记为 $g$。
若 $e$ 有完整补读口，则存在唯一的有界实线性算子 $E_e$，使

$$
R_e(f,h)=g(\iota f,E_e\iota h),\qquad
 E_e=E_e^*,\quad 0\le E_e\le I,\quad E_eJ=JE_e.
$$

因此 $E_e$ 自动为该内部复结构下的复线性效果。
空、总、补与完整合计分别成为 $0,I,I-E_e$ 与 $\sum_jE_{e_j}=I$。

**证明。**
各读口的主定理给对称正性和共同 $U$ 不变。记 $Q_e(f)=R_e(f,f)$。
由完整补关系得 $0\le Q_e(f)\le Q_1(f)$。
若 $Q_1(f)=0$，则 $Q_e(f)=0$；正性使此 $f$ 对 $R_e$ 的全部二元比较均为零。
所以 $R_e$ 保持总读口的零差，并能下降到同一商。

Cauchy–Schwarz 给

$$
|R_e(f,h)|^2\le Q_e(f)Q_e(h)\le Q_1(f)Q_1(h),
$$

故该形式唯一连续延伸到 $\mathcal H$。实 Hilbert 空间的 Riesz 表示给唯一有界 $E_e$；
对称性给自伴，$0\le Q_e\le Q_1$ 给 $0\le E_e\le I$。
总读口已使可见 $\bar U$ 酉，$R_e(Uf,Uh)=R_e(f,h)$ 给
$\bar U^*E_e\bar U=E_e$，故 $E_e\bar U=\bar UE_e$，进而 $E_eJ=JE_e$。
对任意有限完整测试，$\sum_jQ_{e_j}=Q_1$ 与每支非负直接给
$Q_{e_j}\le Q_1$，所以即使其补事件没有单独标签，同一证明也为每支构造 $E_{e_j}$。
各合计关系由表示唯一性传递到算子，结论成立。

这里没有先假定原读口已经是复矩阵。复线性算子与 $J$ 交换的判据是标准内部复化结构 [7](#ref-moretti2017)；
本稿由全部实际读口共用同一候选取得这项相容性。
若某个实际效果不满足它，就应记录这个相位参照不能覆盖该效果域，不能删掉效果来保留结论。
第~[1](#c133-source) 节的新放大门正给出这样的具体测试。

### 4.2 平方读数、干涉与 Born 评价

对 $Q_1(f)>0$，定义归一读数

$$
p_f(e)=\frac{Q_e(f)}{Q_1(f)}
 =\frac{\langle\iota f,E_e\iota f\rangle}{\|\iota f\|^2}.
$$

完整测试使其非负且合计为一；总自读为零时不作这个除法。
若单位向量 $v$ 的整个相位平面投影 $P_v$ 是实际允许的效果，
对单位 $u$ 有

$$
p_u(P_v)=g(v,u)^2+g(Jv,u)^2
 =|\langle v,u\rangle|^2.
$$

因此 Born 平方形式已是归一二元读数的几何公式。
把这些数认定为实验频率或概率，需要原读口确实表示相应事件权重；
该来源对应不由重命名 $p_f$ 自动完成。

对固定事件 $e$，其未归一权重满足

$$
Q_e(f+h)=Q_e(f)+Q_e(h)+2R_e(f,h).
$$

三份配方的三阶包含排除量恒为零：

$$
\begin{aligned}
 &Q_e(f+h+k)-Q_e(f+h)-Q_e(f+k)-Q_e(h+k)\\
 &\qquad+Q_e(f)+Q_e(h)+Q_e(k)=0.
 \end{aligned}
$$

这是预给双线性合计的精确后果；不能把这一部分说成没有使用叠加结构的独立发现。

### 定理 4.3（全效果评价的密度态形式）

<a id="c133-born"></a>

在有限复维数 $d$ 的窗口中，若原评价覆盖全部 $0\le E\le I$，对同一效果赋同值，
满足非负、$p(I)=1$，以及 $E+F\le I$ 时 $p(E+F)=p(E)+p(F)$，
则存在唯一 $\rho\ge0,\operatorname{Tr}\rho=1$，使 $p(E)=\operatorname{Tr}(\rho E)$。
其凸极点恰为秩一态。

**证明。**
可加性给有理齐次，非负性给单调，有理夹逼给实齐次。
对正算子 $A$ 取 $t\ge\|A\|$、$t>0$，以 $t\,p(A/t)$ 延伸到正锥；
齐次性使定义与 $t$ 无关，公共缩放给可加性。
再取正负分解，得到自伴矩阵空间上的实线性泛函。
有限迹配对给唯一自伴 $\rho$；对所有秩一投影非负和 $p(I)=1$ 分别给正性与迹一。
秩至少二的态可微调两个正本征权，故非极点；秩一正分解只能支持同一射线，故为极点。

这是全效果版本的表示定理，包括二维 [8](#ref-busch2003)。
实际日志的完整事件划分可以由计数定义给出有限频率可加性与归一性；
跨不同测试的同一效果识别、一致评价的存在及全效果域仍需来源证明。
不能只检查一组固定基底的频率便应用此定理。

### 4.3 同一关系如何选择完全正过程

以下给出有限量子过程的一套闭合接口，而不把任意原程序预先认作这种过程。
在已重建的复空间上取全矩阵代数 $M_d(\mathbb C),M_m(\mathbb C)$。
若只给自伴读口上的实线性作用，可用
$\Phi(A+iB)=\Phi(A)+i\Phi(B)$ 作唯一复线性延拓；
这要求原作用的整个自伴域已供应，并且该域上的关系得到保留。

### 定义 4.4（过程的来源比较）

对仅给复线性的 $\Phi:M_d(\mathbb C)\to M_m(\mathbb C)$，定义

$$
K_\Phi((a,u),(b,v))=\langle u,\Phi(a^*b)v\rangle.
$$

在这些标签的自由复线性包络上以该表定义半双线性 $B_\Phi$，
令 $R_\Phi=\Re B_\Phi$，参考移位取乘 $\omega=e^{2\pi i/3}$。
不先要求 $\Phi$ 正、保伴随、完全正或归一。

### 定理 4.5（来源预算、Choi 与 Kraus）

<a id="c133-cp"></a>

以下等价：$R_\Phi$ 通过本轮候选；固定一行 $p$ 的有限标签
$((E_{pi},e_\mu))_{i,\mu}$ 上全部两份配方通过候选；$\Phi$ 完全正。
成立时有 $d\times m$ 矩阵 $A_\nu$，使

$$
\Phi(x)=\sum_\nu A_\nu^*xA_\nu.
$$

**证明。**
所选参考满足 $D=0$，故主等价定理使候选恰为原复形式的 Hermitian 正性；
这里利用半双线性形式由其实部和同一复结构唯一确定。
有限标签表的块元是 $\langle e_\mu,\Phi(E_{ij})e_\nu\rangle$，正是 Choi 表
$C_\Phi=[\Phi(E_{ij})]$。
若它正，将其分解成 $\sum_\nu w_\nu w_\nu^*$，并写
$w_\nu=\sum_i e_i\otimes A_\nu^*e_i$；比较各块便得所述 Kraus 式。
该式的全部矩阵放大保持正性，故 $\Phi$ 完全正。
反向对任意正块表 $[a_i^*a_j]$ 应用完全正性，再用向量族评价，
得到整个 $K_\Phi$ 为正核；于是所有配方满足候选。

这与标准有限 Choi–Kraus–Stinespring 表示一致 [9](#ref-watrous2018)。
若从核商构造 $\pi(x)[a,u]=[xa,u]$、$Vu=[I,u]$，零关系由正性和
$x^*x\le\|x\|^2I$ 保持，直接得到 $\Phi(x)=V^*\pi(x)V$。
单位未归一时 $V$ 不必等距；零映射允许零比较空间。

### 4.4 完整仪器、更新与不确定界

若原事件族 $\Phi_j:M_{d_j}\to M_m$ 各满足来源预算，并且全部原记录满足
$\sum_j\Phi_j(I)=I$，则态方向

$$
\mathcal T_j(\rho)=\sum_\nu A_{j\nu}\rho A_{j\nu}^*,\qquad
 \sum_{j,\nu}A_{j\nu}^*A_{j\nu}=I
$$

构成完全正仪器。各支迹不增，总带标签输出保迹；
$p_j=\operatorname{Tr}(\rho E_j)$，$E_j=\Phi_j(I)$。
只有 $p_j>0$ 时定义条件态 $\rho_j=\mathcal T_j(\rho)/p_j$。

若同空间某支效果为投影 $P$，并保持 $\operatorname{Ran} P$ 中每条纯射线，则
$A_\nu(I-P)=0$；逐射线保持又迫使 $A_\nu v$ 与 $v$ 共线。
对基向量及两两和应用，得 $A_\nu=c_\nu P$。
若 $P\ne0$，效果归一给 $\sum_\nu|c_\nu|^2=1$，因而
$\mathcal T(\rho)=P\rho P$。$P=0$ 时所有 Kraus 项为零。
仅有结果可重复性仍允许结果子空间内的旋转，不能单独推出 Lüders 更新。

有限锐测量由正交投影族与实结果构成，自伴算符由有限谱分解表示。
对自伴 $A,B$ 中心化为 $A_0,B_0$，算符历史正形式
$\Gamma_\rho(X,Y)=\operatorname{Tr}(\rho X^*Y)$ 的二阶 Gram 正性给

$$
\operatorname{Var}_\rho(A)\operatorname{Var}_\rho(B)\ge|\operatorname{Tr}(\rho A_0B_0)|^2
 \ge\tfrac14|\operatorname{Tr}(\rho[A,B])|^2.
$$

位置、动量、具体交换常数及无限维无界算符的定义域不由本轮预算选定。

### 4.5 独立联合、可逆与连续时间

若两个全矩阵代数以保单位的星代数嵌入映入一个非零联合代数
（包括保乘法与线性），两像交换并共同生成，则
$a\otimes b\mapsto\iota_A(a)\iota_B(b)$ 为满的保单位星同态。
定义域 $M_d\otimes M_m\cong M_{dm}$ 简单，故该同态为同构，得到张量联合。
Kraus 表示使过程串接与并接闭合；完整局部保迹过程不改变另一侧边缘。
实际空间分离是否提供这种独立接口，仍需物理来源说明。

### 命题 4.6（有限可逆过程与时间生成元）

同维 CPTP 过程若有 CPTP 左逆，则为酉共轭。
若再给连续一参数 CPTP 群，则存在自伴 $H$，使

$$
\mathcal T_t(\rho)=e^{-itH/\hbar}\rho e^{itH/\hbar},
 \qquad i\hbar\dot\rho=[H,\rho].
$$

**证明。**
两过程的 Kraus 族记为 $A_i,B_j$。恒等通道的 Choi 秩一给
$B_jA_i=c_{ji}I$。对非零 $A_i$，左逆保迹保证某个乘积非零；
同维使相应 $B_j$ 可逆，因而全部 $A_i$ 共线。
合并成一个 $A$ 后，保迹给 $A^*A=I$，方阵即酉。
有限维连续群具有生成元 $\mathcal L$；各映射为星自同构，故 $\mathcal L$ 是保星导子。
令 $D_0=\sum_k\mathcal L(E_{k1})E_{1k}$，导子律给
$[D_0,E_{ij}]=\mathcal L(E_{ij})$；保星性使 $D_0+D_0^*$ 为中心。
换成反自伴部分并写为 $-iH/\hbar$ 即得结论。

选定纯态相位代表后有 $i\hbar\dot\psi=H\psi$。
三读的公共相位参照与一般 Hamiltonian 时间演化承担不同作用；
本轮没有由 $U$ 唯一决定实际 $H$、时间单位或 $\hbar$。

**白话。**先让每个真实读口都遵守同一条比较关系。完整分支合起来等于总读口，所以任何分支都不能比总量更大；在重建空间中，它自然成为介于零和一之间的正效果。投到一个完整相位平面的读数，就是两根实轴投影平方之和。若这些读数确实表示原事件权重，完整记录就给归一概率；过程的来源乘法再给完全正更新，独立联合与可逆时间分别给张量和酉演化。这些接口一旦供应，理论就闭合；没有供应的接口仍要由原过程证明。

<a id="section-5"></a>

## 5. 定义关系、完整档案与观察者的可见范围

<a id="c133-observers"></a>

### 5.1 把已供应的定义锁进二元关系

主定理以后，定义关系可以精确写成零差，但正性建立之前不能仅凭自读零这样做。
在已重建的复配方空间上，给有限关系
$r=\sum_jc_jh_j$，其二元表记为 $B$。

### 定理 5.1（定义零差与保表延拓）

<a id="c133-relation-extension"></a>

以下三者等价：$B(r,r)=0$；$\iota r=0$；$B(k,r)=0$ 对全部比较配方 $k$ 成立。
若更大的正核保留原有限关系涉及的全部旧表条目，则该零差对全部新比较标签也为零。

**证明。**
第一等价由完整零差商给出。Cauchy–Schwarz 给
$|B(k,r)|^2\le B(k,k)B(r,r)$，故自读零迫出每一个二元对照为零；
反向取 $k=r$ 即得自读零。正延拓保留 $B(r,r)=0$，再用同一不等式即得新标签结论。

例如定义 $h_3=ah_1+bh_2$，相容条件可写成
$Q(h_3-ah_1-bh_2)=0$。这个写法把已供应的关系固定在全部保表正延拓中，
不要求在定义之外再指定一个独立的 Hilbert 空间。
它没有证明原程序一定供应这个合成操作，也没有证明满足所有关系的非零模型一定存在。
若只知 $Q(r)\le\varepsilon$，则
$|B(k,r)|\le\sqrt{Q(k)\varepsilon}$；近似相容需要同时控制比较配方的尺度。

### 命题 5.2（程序何时可以作用于同一可见商）

<a id="c133-descent"></a>

对原空间上的实线性操作 $T$，存在良定义的商操作
$[f]\mapsto[Tf]$ 当且仅当 $T\mathcal N\subseteq\mathcal N$。
它与本轮复结构相容当且仅当
$(TJ_0-J_0T)V\subseteq\mathcal N$。
它能延伸为完成空间上的有界实线性操作，当且仅当存在有限 $C$ 使
$Q(Tf)\le C Q(f)$ 对全部 $f$ 成立。

**证明。**
两个代表之差属于 $\mathcal N$；它们的像仍表示同一对象，恰要求第一条件。
复线性等价于商上与 $J$ 交换，直接给第二条件。
第三条件正是稠密商上范数有界；有界操作唯一连续延伸，反向取其范数平方即可。

候选已经证明特定推进 $U$ 具备这些性质，但没有使全部未来程序自动具备它们。
项目 C117 保留合法后缀与原记录，C123 以全语境响应定义等价，
正是为了不把一个来源上的输出一致误当成全部程序等价 [3](#ref-repo-c117)、[4](#ref-repo-c123)。
这也限定“内容等于地址”：编码同一性、当前读数相同和全语境操作相同，是需要分别证明的关系。

### 5.2 三步相位返回，为什么不要求档案返回

### 命题 5.3（严格增长的可读档案与周期分离）

设完整原始历史 $h,Uh,U^2h,\ldots$ 带实际可读长度 $L$，并且每一步使
$L(Uh)>L(h)$。则在包含这个长度读口的全语境等价中，$U^3h$ 不可能等价于 $h$。

**证明。**
严格增长给 $L(U^3h)>L(h)$。若两历史全语境等价，长度这个实际读口又要求二者相等，矛盾。

本轮只推出 $\iota U^3h=\iota h$。因此完整档案若确实可读，必须保留在原层，
或选择足够大的共同来源表示，不能把当前相位商说成包含全部档案的同一个可见商。
第~[3](#c133geo-section) 节的第三坐标 $1,2,4,8,\ldots$ 正给出严格的分层模型。
若另一个读口能读到它，新读口就不满足当前这组三读共同相位关系。

也不能把改变旧读口称为保表延拓。两个正表

$$
G_{\mathrm{old}}=\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad
 G_{\mathrm{new}}=\begin{pmatrix}1&1\\1&2\end{pmatrix}
$$

分别把第二标签减第一标签读成零与一。
新表改变了旧的第二个自读条目，因而不满足定理~[5.1](#c133-relation-extension) 的保表前件。
“以前看不见”和“在保留整张表的正延拓里永远为零”是两个不同断言。

日志单调是可以明定的档案协议，并非所有封闭系统中每一个局部寄存器的信息都只能增长。
在可逆的两位映射 $(a,b)\mapsto(a,b\mathbin{\mathrm{xor}}a)$ 中，从 $(a,0)$ 写入一位记录后再作用一次，
辅助位回到零，而原位仍保留信息。这是严格可逆的局部消记例。
若要求每次动作永久可查，必须把追加档案及其读权限纳入模型 [5](#ref-repo-records)。
同时，换用 $J\mapsto-J$、共轭全部复表并不破坏正性和日志增长；
追加方向不能单独选定绝对相位手性或空间手性。

### 5.3 两个观察者没有共同读数时，保留未知交叉项

观察者各自得到的表不能凭空填满另一份历史的交叉读数。
若两者各自只知道一个单位自读，全部候选交叉表为

$$
G_z=\begin{pmatrix}1&z\\\bar z&1\end{pmatrix},\qquad |z|\le1.
$$

这是正性给出的完整圆盘；$z=0$ 允许正交，$|z|=1$ 允许同一复线。
单独的两份自读无法辨认这些情况。
实际共同比较可以缩小该圆盘，甚至确定 $z$，不必先包含另一观察者的全部结构。
因此可证的是缺少交叉证据时的不确定，不能升级成永远不可知的结论。

### 定理 5.4（实际兼容有限窗口的有向拼接）

<a id="c133-directed-gluing"></a>

设一族有限读数窗口由非空有向偏序索引，大窗口在小窗口上的限制严格等于旧表。
若每个窗口都是复正核，且共同定义关系和时钟限制相容，
则并集上存在唯一保留这些条目的正核，其最小表示为局部零差商的等距有向极限再完成。

**证明。**
任何有限标签族都有共同上界。两种窗口给出的条目在更大窗口中相同，故并集表定义良好且唯一。
每个有限配方同处某一窗口，其自读非负，故并集正。
保表性使各局部零差和内积相容，产生等距嵌入；并集在最小表示中稠密，取完成即可。

定理不要求任何观察者已掌握整个并集，但需要实际的兼容数据。
仅有两两窗口不足：$2I_3-\mathbf1\mathbf1^T$ 的每个二阶主块都是正半定，
全表在全一方向却给负自读 $-3$。
三元提升能揭示这个特定失败，不能代替所有更大有限表的检查。
事实上对任何固定 $r\ge1$，表
$(2r+1)I_{r+1}-2\mathbf1\mathbf1^T$ 的每个至多 $r$ 阶主块正定，
整个表仍有特征值 $-1$。

### 命题 5.5（顺序读取的逼近目标）

在一个已经相容的共同表示中，令可见闭子空间递增为
$H_1\subseteq H_2\subseteq\cdots$，对应正交投影为 $P_n$。
对任意 $v$，有

$$
\|v-P_nv\|^2-\|v-P_{n+1}v\|^2
 =\|(P_{n+1}-P_n)v\|^2\ge0,
 \qquad P_nv\longrightarrow P_\infty v,
$$

其中 $P_\infty$ 投到 $\overline{\bigcup_nH_n}$。

**证明。**
嵌套性给误差的正交分解，直接得到平方差。
同一分解使 $\|P_nv\|^2$ 单调有界并使 $P_nv$ 为 Cauchy；
极限属于闭并集，而误差与该并集正交，所以是所述投影。

两位观察者都逼近同一个 $v$，还需各自的闭并集都包含 $v$。
任意合法门作为起点、任意门序列，并不足以保证这个稠密性条件。
原先设想“任意输入都送到自己”的门也不能是非平凡酉门：酉门单射，不能把两个不同输入合一。
允许环境承接区别时，取固定单位向量 $r$，可以使用 $u\mapsto r\otimes u$ 的等距重置；
原输入的区别保留在环境，并没有由自指消失。

因此本稿可定义关系整体
$\Omega_{\mathrm{rel}}=(\text{历史标签、实际读表、已供应定义关系})$。
它不自动是一条归一量子态，也没有由候选唯一选出。
零读数、不同 $k$、不同 $H\succeq0$ 都属于主定理允许的模型；
实际 $\Omega$ 的非零性、完整控制和物理意义仍需要来源。

**白话。**观察者保留自己的原记录，只把这个读口确实处处看不出的区别视作同一种读数。后来如果只是添上新比较而不改旧表，已经证明的零差会一直成立；如果开放了以前遮住的档案，原来的商就可能需要更换。两个人没有共同读数时，就把交叉关系留空，不替他们造一个全知视角。取得共同证据后再拼接，两条读取路径只有各自足够丰富时，才会逼近同一个目标。

<a id="section-6"></a>

## 6. 本轮究竟回溯了什么，下一项来源证明是什么

<a id="c133-ledger"></a>

### 6.1 从 C132 到 C133：准确的弱化关系

在同一个加权参数 $\lambda$ 下比较：C132 的原空间关系
$I+\lambda U+U^2=0$ 与一步预算，蕴涵 C133 对应的代表预算，因为加入的残差本来为零。
反向不成立：在合法旋转平面旁接任何不可读的原始分量，其推进可以非周期、不可逆；
旧的全空间关系失败，新候选仍然通过。
因此弱化发生在*原历史本体必须满足的关系*上。
本轮等权主式选择 $\lambda=1$，与旧黄金 $\lambda=\phi^{-1}$ 的数值不同，
两者之间不能只凭换参数就宣称逻辑蕴涵。

本轮的两项关键变化是：原递推改为可读的定义零差，效果算子改由完整二元读口重建。
但实线性配方、双线性聚合、全部代表检验与同一相位参照仍在输入端。
无界 $n$ 使任何非零残差都能被有限失败见证发现，却不能由预定有限菜单认证精确零。
这是一项可反驳的数学条件，不是无需来源即可成立的世界描述。

| 目标 | 已证明的结果 | 仍需保留的来源接口 |
|---|---|---|
| 正性、对称性 | 单一代表预算迫出正半定实读数 | 实配方空间、双线性 $R$ |
| 复 Hilbert 空间 | 三时零差商、内部 $J$、完整根空间商及完成 | 所选闭合模式；非零读数并非必然 |
| 效果与测量 | 每个完整分支重建 $0\le E\le I$，合计为 $I$ | 实际事件族、补事件和同一相位参照 |
| Born 与密度态 | 投影平方；全效果可加评价等于 $\operatorname{Tr}(\rho E)$ | 权重的事件意义；全效果与同值识别 |
| 过程与更新 | 来源核预算等价 CP，得到 Kraus 与仪器 | 来源乘法、参考输入、完整记录归一 |
| 投影更新 | 保持结果子空间每条纯射线给 $P\rho P$ | 强于仅可重复性的无扰动条件 |
| 联合与时间 | 独立矩阵接口给张量；可逆连续群给酉与 $H$ | 联合代数、连续参数、实际单位 |

候选本身仍允许经典读口子域：取 $\mathcal H=\mathbb C^d$、$U=\omega I$，
实际效果全部取同一基底下的对角正矩阵，则各 $R_e$ 都通过候选，
可读态却只是一组经典概率权。非交换读口或全部效果的实际供应，不能由复表示的存在代替。
在上述接口齐备的有限窗口中，态、效果、复合、仪器与可逆时间形成一套封闭量子理论。
本稿没有从该一行预算推出粒子种类、规范群、时空维数、Hamiltonian、耦合常数或 Planck 常数。
因此它给出的是量子形式的条件重构，而非已经完成标准模型或量子场的起源论。

### 6.2 Zeckendorf 余差在哪一层起作用

用户提出的 $\beta(a)+\beta(b)-\beta(a+b)\in\{-1,0,1\}$，
在项目中属于具体数字与规范化定义下的三值缺口定理 [6](#ref-repo-beta)。
设 $\delta(a,b)=\beta(a)+\beta(b)-\beta(a+b)$，单凭定义即可逐项消去得到

$$
\delta(a,b)+\delta(a+b,c)
 =\delta(b,c)+\delta(a,b+c).
$$

它使三份内容按不同括号聚合时，总缺口相同。
三值性质进一步限制单次缺口的范围；它没有自动给出一个比较核的正性或复数结构。

具体地，给同一份 $\beta$ 算术旁接一个实空间、$U=I$ 和普通正点积 $R$，
全部算术等式仍成立，但 $D=3I$；非零 $f=g$、$n=1$ 使本轮预算成为
$8Q(f)\le2Q(f)$，直接失败。
因此缺少的不是再给缺口取一个名称，而是原进位、位移或相位操作到读口的来源桥。
要建立这座桥，必须证明那些原操作诱导同一 $U$，并使全部相关原读口满足
$R_e(f,D_\lambda g)=0$ 与一步预算；这两项足以推出该参数的代表预算。
黄金路线使用 $\lambda=\phi^{-1}$，不能偷换成本轮等权的 $\lambda=1$。

同样，$a^2+xab+b^2=1$ 在实 $(a,b)$ 平面中，$x=0$ 是单位圆，
$|x|<2$ 是椭圆，$x=2$ 是两条平行直线 $a+b=\pm1$。
$ab$ 是双线性项，并不是 $(a,b)$ 的线性函数。
有用的直觉是二元交叉读数改变自读几何；它不能替代相应二次型的退化检查。
本轮的三读给 $x=-1$，对应一个确定的正二次型，转到正交坐标才成为圆。

### 6.3 继续回溯时，应当针对哪一个可失败的命题

最清楚的下一项来源命题可以不先提 Hilbert 空间：
*对于项目保留完整身份、记录和合法后缀的某一原读口域，找出同一个实际参照操作，
证明所有原读口的三时残差与每一份原历史互读都为零，并证明原二元预算及完整分支的合计关系。*
如果证明成立，主定理与完整读口定理自动供应复正几何及效果。
如果失败，应留下具体的两份历史、原事件和有限倍数，不更换读口或删去原记录来消除反例。

新增相干放大的 $P$ 已给出这样的失败证书：成功和失败都真实可读，
而动力学旋转把它们混合，所以不能把这一旋转作为全部效果共有的标量相位。
这不会否定该模块的量子正确性；它精确排除了一个不适合的原参照选择。
下次应寻找保留实际效果的共同参照，或证明它只存在于一个明确受限的比较域。

还有一个不可绕过的逻辑界限：把“$\Omega$ 是满足这些关系的整体”作为定义，
可以使候选成为模型类的内部条件，却不能单靠定义保证原物理世界属于这个类。
本轮已经刻画全部数学模型并给出非零例，消除了内部矛盾和空泛的存在猜测；
具体原生接口是否满足候选，仍是能被源码、实验或失败见证回答的问题。

### 6.4 本轮完整白话

**白话。**先把全部历史和档案留下，不要求整个世界三步回到原样。拿两份历史互相读：先由原第二份及其两次推进组成三读合计，再把这份合计添加到它的一次推进上，添多少份都不能比原来两份自读的平均预算更多。如果这个合计还藏着一个能被读出的方向，找准另一份历史去比较、再多添几次，它就一定超支；所以三读合计必须在这个读口里成为零差。零差合并以后，三次读数才闭成一个等边三角形，每次推进都保量，三角形所在的实平面便自带左右相位，组成一个复方向。完整分支把这套几何变成效果和概率，原过程的完整来源把它延伸成量子更新。原始档案可以继续增长，两个观察者也只拼接已经取得的共同读数；任何仍能读到的方向，都不能为了让三角形闭合而抹掉。

<a id="references"></a>

## 参考文献

<a id="ref-repo-c133-pin"></a>

### [1]

The Omega Institute, *trureturing*, 本轮固定版本
[`4008fb9289d8`](https://github.com/the-omega-institute/trureturing/commit/4008fb9289d85582c68b23a5810474e4463c64ea)。
默认分支 `dev`，2026-11-04 12:30:01 UTC，20:30:01 Asia/Singapore。
相对 `30817972a543` 的两端差分与有界核读范围见第~[1](#c133-source) 节。
本轮阅读不等同于重新运行 Lean 或认证整个仓库。

<a id="ref-repo-amplification"></a>

### [2]

The Omega Institute,
[*CoherentUniformAmplification.lean*](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/D5/S3/Quantum/Recovery/CoherentUniformAmplification.lean)。
`frame_rotation`、`uniform_operator_rotation`、`exact_coherent_amplification`。
固定文件全文核读。统一源旋转、参考扩张与精确放大的实际前件保留；
本文针对成功效果的反例由这些式子直接推导。

<a id="ref-repo-c117"></a>

### [3]

The Omega Institute,
[*Common Source, Self-Reference and Observer Sequences C117*](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md)。
本轮复核第 8、16.7、17–18、25、29 节指定内容；完整身份、原记录、合法后缀、方向充分性与共同正生成均保留前件。
未把有界阅读或文稿定理陈述当作全卷形式验证。

<a id="ref-repo-c123"></a>

### [4]

The Omega Institute,
[*Native Reciprocal Comparison and Finite Endpoint Quantum C123*](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/docs/develop/theory/AURIC_NATIVE_RECIPROCAL_COMPARISON_AND_FINITE_ENDPOINT_QUANTUM_C123.md)。
定义 1.1、35.2，定理 36.1；全语境响应等价与已有 EJA 正几何中的零接触条件。
本轮仅复核记录所列区间。

<a id="ref-repo-records"></a>

### [5]

The Omega Institute,
[*Fibonacci History Records and Time Arrow*](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/docs/develop/theory/AURIC_FIB_HISTORY_RECORDS_TIME_ARROW.md)。
本轮复核追加档案、任务读口、档案可访问性及观察者窗口相关区间；
原日志身份与特定相位商分开保留。

<a id="ref-repo-beta"></a>

### [6]

The Omega Institute,
[*WDigits.lean*](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/D5/S0/Conventions/WDigits.lean)，
[*DeficitInteger.lean*](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/D5/S1/Deficit/DeficitInteger.lean)，
[*DeficitThreeValued.lean*](https://github.com/the-omega-institute/trureturing/blob/4008fb9289d85582c68b23a5810474e4463c64ea/D5/S1/Deficit/DeficitThreeValued.lean)。
沿用 C132 已全文核读的固定算术来源，本轮确认三份文件在 `d9880e9f2c32`、`30817972a543` 与 `4008fb9289d8` 的 blob 一致并补读全文：
`betaDigits`、`betaReal`、`deficit_integer`、`deficit_three_valued`。
本稿只使用其三值缺口结论；余循环等式在正文由定义直接证明。

<a id="ref-moretti2017"></a>

### [7]

V. Moretti and M. Oppio, *Quantum theory in real Hilbert space:
How the complex Hilbert space structure emerges from Poincaré symmetry*,
*Reviews in Mathematical Physics* **29**, 1750021 (2017).
[arXiv:1611.09029v4](https://arxiv.org/pdf/1611.09029)，第 2.5 节，Propositions 2.21、2.23。
这里只使用已给正交复结构后的内部复化及算子交换判据；
不移用另有 Poincaré 前件的物理起源结论。

<a id="ref-busch2003"></a>

### [8]

P. Busch, *Quantum states and generalized observables: a simple proof of Gleason's theorem*,
*Physical Review Letters* **91**, 120403 (2003).
[arXiv:quant-ph/9909073v3](https://arxiv.org/pdf/quant-ph/9909073)。
全效果一致可加评价的密度算符表示，包括二维。

<a id="ref-watrous2018"></a>

### [9]

J. Watrous, *The Theory of Quantum Information*, Cambridge University Press (2018).
[作者公开第 2 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，Theorem 2.22。
有限完全正映射的 Choi、Kraus 和 Stinespring 等价表示。

<a id="ref-mosseri2001"></a>

### [10]

R. Mosseri and R. Dandoloff,
*Geometry of entangled states, Bloch spheres and Hopf fibrations* (2001).
[arXiv:quant-ph/0108137v1](https://arxiv.org/pdf/quant-ph/0108137)，第 2 节。
单量子比特单位态球的相位圆纤维；全文中的 Hilbert 空间应与单位态球严格区分。

<a id="ref-arrighi2002"></a>

### [11]

P. Arrighi and C. Patricot,
*A note on the correspondence between qubit quantum operations and special relativity*,
预印本 2002，修订版 2003。
[arXiv:quant-ph/0212135v3](https://arxiv.org/pdf/quant-ph/0212135)，第 I 节、Lemma 1。
二阶 Hermitian 正锥的四维 Lorentz 坐标；本文不据此推断物理时空。
