# 相容预测波与关系谱：AURIC FIB ATOM 的条件表示

波在这里指指定模式或观察接口上的可复合振幅及其接续关系。保留不同预测的全部交叉关系，并要求接续无损保持这些关系，给出 Hilbert 空间中的等距；有限维闭合或满射时得到酉相位演化，重合读出产生干涉。谱清单仍需模态嵌入、初态和读出，才能决定波形。

本文采用第一变量共轭线性、第二变量线性的内积。所有模型、效果、参考和控制都有明确的类型与供应条件。正文是普通数学论证；条件表示不等于自然界唯一性的经验结论。项目原始供应版本固定为 `d5e7fbecb49c0e928696f6857b331b3dbd54d128`，相关完整伴篇的供应版本固定为 `ee1728e4f0c42ea4017a6ba12e2abb63210248f3`；引用的具体数学用途在相应证明内说明。

## 1. 先确定“谱”“波”与“相融”分别是什么

“相融的预测得到的谱实际上就是波”可以成为严肃的研究纲领。
最有力量的部分，是把波看成预测之间能够持续接续的关系结构，
而不仅是一个额外附着在粒子上的形状。
要将它变成定理，必须说明哪些关系被保存、什么操作能读取它们。

**定义 1.1（五模式与本稿的命名）。**
取三位置路径的无相邻占据模式

$$
\Sigma=(0,1,2,3,13)=(000,100,010,001,101).
$$

它们对应项目的

$$
(F[\mathrm{null}],F[1],F[2],F[3],F[1,3])
=(N,[2],[3],[5],[2,5]).
$$

下标 $1,2,3$ 指逻辑位置，不把数值标签 $2,3,5$ 当作边长或频率。
三位串按位置 $(1,2,3)$ 排列。
$|0\rangle$ 是范数一的模式向量，不是零向量，也不是停止符。

同一组五标签可以支持不同理论。
概率单纯形、实 Hilbert 模型、复 Hilbert 模型都能用它作结果集。
选择哪个模型，要看额外供应的组合和读出规律。
项目的量子相关卷也明确将复 Hilbert、Born 效果和完全正通道列为模型规则
[static]、[wave]、[second]。

| 对象 | 它记录什么 | 它单独没有记录什么 |
| --- | --- | --- |
| 合法模式谱／计数 | 哪些模式允许、各有多少 | 复振幅、物理时间、门矩阵 |
| Gram 矩阵的谱 | 相干比较核的主轴权重 | 主轴相对结果标签的嵌入 |
| 密度算子谱 | 混合程度及本征权重 | 本征向量、读出方向 |
| Hamiltonian 谱 | 选定时间标定下的能量／频率 | 初态、矩阵元及读出耦合 |
| 功率谱 | Fourier 分量的模平方 | Fourier 相位、一般的完整波形 |

因此，一个 $\lambda$ 表列不能同时替代上述五种不同对象。
本稿把“波”定义为一个在指定模式或观察接口上可复合的振幅场，
及其随接续参数变化的关系；是否能进一步解释成三维空间中的波，
要另给空间嵌入和尺度极限。

**定义 1.2（三种不同的相容）。**
*逻辑相容*指某组限制有共同模型；
*拼接相容*指不同分解方式给出同一操作的相同预测；
*相干相容*还要求不同备选过程的交叉振幅属于同一个正核，
并能在共同参考下比较、重合。
它们均不等同于“全部量子可观测量彼此对易”。

特别地，退相干历史中不同事件之间的交叉项消失，会恢复普通概率加法。
若把“相融”定义成所有交叉项都为零，就恰好删掉了本文要解释的干涉。
本文的相融是共同的表示、比较与拼接规则；它允许可测的非零交叉项。

**命题 1.3（特征值清单不决定波）。**
即使初态与读出固定，两个具有相同特征值的 Hamiltonian
也可以给出不同的时间读出。

证明。
在两维子空间取 $X=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$、$H_1=\operatorname{diag}(1,-1)$、$H_2=X$，
初态与终端效果都取 $|0\rangle$。
两者谱均为 $\{1,-1\}$，但

$$
|\langle 0|e^{-\mathrm i tH_1}|0\rangle|^2=1,\qquad
|\langle 0|e^{-\mathrm i tH_2}|0\rangle|^2=\cos^2t.
$$

缺少的是谱投影相对制备与读出的方向。
∎

## 2. 相融预测的真正约束：正核与整体一致性

### 从可重合关系到 Hilbert 表示

**定义 2.1（相干预测核）。**
设 $\mathscr P$ 是同一输入输出类型的预测描述集。
给 Hermitian 核
$\mathcal K:\mathscr P\times\mathscr P\to\mathbb C$。
称它强正，若对任意有限描述 $p_1,\ldots,p_m$ 及任意 $c\in\mathbb C^m$，

$$
\boxed{Q(c;p)=\sum_{i,j}\overline c_i c_j\mathcal K(p_i,p_j)\ge0.}
\tag{P}
$$

这里 $c$ 的可操作含义，是在共同参考下对备选预测作相干重组的系数。
只建立形式线性张成，不等于已经实现所有这样的制备。

**定理 2.2（预测核的最小振幅表示）。**
每个强正核都有 Hilbert 表示

$$
\mathcal K(p,q)=\langle v_p,v_q\rangle,\qquad
H=\overline{\operatorname{span}_{\mathbb C}\{v_p:p\in\mathscr P\}}.
$$

该最小表示在保持每个 $v_p$ 标签的酉同构意义下唯一。
对有限描述集，$\dim H$ 等于其 Gram 矩阵的秩。这里是该有限集所生成的最小空间，不是另一个更大描述域的维数。

证明。
在自由复向量空间 $\mathbb C[\mathscr P]$ 上定义

$$
\left\langle\sum_i c_i[p_i],\sum_jd_j[q_j]\right\rangle
=\sum_{ij}\overline c_i d_j\mathcal K(p_i,q_j).
$$

正性给半内积。对任意 $u,v$，
$\left\lVert u+zv\right\rVert^2\ge0$ 的二次式给 Cauchy--Schwarz 不等式；
故零范数向量与全部向量正交，零空间 $\mathcal N$ 为线性子空间。
商去 $\mathcal N$ 再完备化，令 $v_p=[p]+\mathcal N$ 即得。
任意另一最小表示把有限和映到相同标签的有限和，内积相同；
零关系保持，所以它下降为稠密子空间的等距，并延拓成满酉。
有限时商掉 Gram 零空间，维数即为矩阵秩。
∎

此证明使用 [recursive] §2、[quantum] §6 的同一零关系商接口及正核／GNS 标准构造，
不是由五点外形新创的 Hilbert 定理。
历史方法中从强正 decoherence functional 作同类构造，
可见 Dowker--Johnston--Sorkin 的原文 [djs]。
关键输入是整个 $\mathcal K$，不能只给对角线后宣称内积已经被推导。

**命题 2.2a（有限容量与无限维边界）。** 对任意描述集，所有有限 Gram 矩阵的秩都不超过有限整数 $d$，当且仅当最小表示的维数不超过 $d$。无界的有限 Gram 秩排除任何有限维、保留全部组合权重的线性摘要，但不决定任意无限 Hilbert 空间的基数维数。

证明。若 $H$ 至多 $d$ 维，任意有限组向量的 Gram 秩当然至多 $d$。反向，若生成向量的线性张成超过 $d$ 维，就能从其中选出 $d+1$ 个线性无关的生成向量，产生正定的 $(d+1)$ 阶 Gram 矩阵，矛盾。有限维子空间已经完备，所以闭包也不增维。保留全部组合权重的线性摘要经四相位极化保留内积，故必是等距，不能降低有限 Gram 秩。另一方面，对每个无限集合 $I$，取描述集为 $\ell^2(I)$ 的标准正交基；其有限 Gram 秩均无界，而 Hilbert 维数为 $|I|$。这些同样的“有限秩无上界”读数不能区分不同无限基数。只有另加可数稠密生成等条件，才可进一步得可分性。∎

**命题 2.3（同权重可以有完全不同的相干）。**
令 $p_i>0$ 且 $\sum_i p_i=1$。
矩阵

$$
G_{\rm cl}=\operatorname{diag}(p_i),\qquad
G_{\rm coh}=aa^\dagger,\quad a_i=\sqrt{p_i}e^{\mathrm i\theta_i}
$$

都有相同对角线，且均为正半定。
前者秩为 $m$，后者秩为一；一般相干重组权重不同。

证明。
两矩阵的对角元均为 $p_i$。
第一矩阵对角正定，第二矩阵是非零向量外积。
对任意 $c$，其二次型分别是
$\sum_i p_i|c_i|^2$ 与 $|a^\dagger c|^2$；
第二式包含第一式没有的交叉项。
∎

固定正交结果的概率没有指定这些结果在某个其他比较接口下的相干。
矩阵正核也不自动宣布其每一对索引是同一个测量中的互斥结果。
描述集、重合接口和实际结果标签必须保持类型区别。

**命题 2.4（交叉关系的四相位恢复）。**
对共同 Hilbert 表示中的 $u,v$，若四种重组可执行，则

$$
\langle u,v\rangle
=\frac{Q(u+v)-Q(u-v)}4
-\frac{\mathrm i}{4}\bigl(Q(u+\mathrm i v)-Q(u-\mathrm i v)\bigr).
$$

其中 $Q(w)=\left\lVert w\right\rVert^2$，内积对第二变量线性。

证明。
前一差为 $4\Re\langle u,v\rangle$，
后一差为 $-4\Im\langle u,v\rangle$，代入即得。
∎
这是“边上有隐含信息”的可实验版本：比较两种预测时，
除了各自的强度，还需取得两种正交相位的响应。
若参考相位或重组控制不存在，就不能把这个反演当作现成能力。

### 两两可行不保证整体可行

**定理 2.5（三个预测的闭合限制）。**
使用 [second] §68 的共同 Gram 判据，三个归一化预测向量的候选 Gram 矩阵写为

$$
G=\begin{pmatrix}
1&a&b\\ \overline a&1&c\\ \overline b&\overline c&1
\end{pmatrix}.
$$

它可实现为共同 Hilbert 空间中的三个单位向量，当且仅当

$$
|a|,|b|,|c|\le1,\qquad
1-|a|^2-|b|^2-|c|^2+2\Re(ac\overline b)\ge0.
\tag{2.1}
$$

若三向量属于二维复空间，则还必须有 $\det G=0$。

证明。
存在表示等价于 $G\ge0$。
三阶 Hermitian 矩阵正半定等价于所有主子式非负；
一阶子式为一，二阶分别为 $1-|a|^2,1-|b|^2,1-|c|^2$。
展开三阶行列式得到式 (2.1)。
二维表示使秩不超过二，故行列式为零。
反之主子式条件使 $G\ge0$，定理 2.2 给表示；
若行列式为零，最小表示的维数不超过二。
∎

**例 2.6（局部全对而整体冲突）。**
取 $a=b=c=-3/4$。每个二阶块均正定，
但向量 $(1,1,1)^T$ 对应特征值 $-1/2$，
故三者没有共同正核实现。
“每对都猜得通”仍可在三者合并时失败。

量 $ac\overline b$ 在三个向量各自重相位时不变。
它给三预测的关系相位，而不属于任何一个单点。
当三种非零重叠模长与秩二条件给定时，式 (2.1) 的等号会约束这个相位的余弦；
一般仍有共轭取向等剩余选择。
若三个预测向量真正两两正交，则 $a=b=c=0$，
并没有一个非零三角相位被“锁定”。
几何三正交轴、三个互斥结果和三个不对易读出不能互相替换。

### 为什么“存在新增为正”还不是强正性

**定义 2.7（有限历史权重与参考复合）。**
令 $D=D^\dagger$ 为有限历史标签上的矩阵，归一化为
$\mathbf1^\dagger D\mathbf1=1$。
事件 $A$ 的权重定义为

$$
\mu_D(A)=\sum_{i,j\in A}D_{ij}.
$$

弱正性只要求全部 $\mu_D(A)\ge0$。
独立参考的复合规则若给为张量积，则联合事件 $E$ 的权重使用 $D\otimes R$。
未退相干事件的 $\mu_D(A)$ 不是一组共同测量中各互斥结果的普通概率；
其值也不要求对每个任意事件都不超过一。

**定理 2.8（完整相位参考把事件正性提升为强正性）。**
设 $D=D^\dagger\in M_m(\mathbb C)$。如果对每个向量
$z\in\mathbb C^{m+1}$、$\sum_\alpha z_\alpha=1$，
都允许与归一化秩一参考 $R=zz^\dagger$ 复合，
并要求每个联合事件的权重非负，那么 $D\ge0$。
反之若 $D\ge0$，与任意正半定参考复合都满足这一非负条件。

证明。
任取 $c\in\mathbb C^m$，置

$$
z=(\overline c_1,\ldots,\overline c_m,
           1-\sum_{i=1}^m\overline c_i).
$$

取联合事件 $E=\{(i,i):1\le i\le m\}$，则

$$
\mu_{D\otimes R}(E)
=\sum_{ij}D_{ij}z_i\overline z_j=c^\dagger Dc\ge0.
$$

这对全部 $c$ 成立，正是 $D\ge0$。
反向由张量积保持正半定，且事件权重是其在指示向量上的二次型。
∎

额外标签用于保证参考的总历史权重归一化。
本定理供应的是全部这类相位参考和联合事件测试；
它不把它们当作从一个裸五点图自动得到的操作。
这一有限证明说明，正性最有力量的来源是*与其他预测共同使用时仍然非负*。

**命题 2.9（只要求任意次自我复合仍不足）。**
弱正、归一化及任意张量幂的事件非负，不蕴含 $D\ge0$。

证明。
取

$$
D=\frac16\begin{pmatrix}1&2\\2&1\end{pmatrix}.
$$

全部元素非负，总和为一，故全部事件权重非负，
任意张量幂也保留这两项性质。
但特征值为 $1/2,-1/6$，不是正半定。
∎

Dowker--Wilkes 关于复合与强正性的工作提供了更一般的背景 [dw]；
其 Theorem 3 要求弱正系统类同时张量闭合且 Galois 自对偶，才唯一得到强正系统类；Theorem 4 单靠张量闭合只得该类包含于强正类，或包含于元素非负实值类。这里的“或”不排除两者相交。Galois 对偶指与该类每个成员张量复合仍弱正的系统全体。
不能将它缩成“递归可重复，所以强正性自动成立”。

**定理 2.10（一个相位种子的递归复合足以测试强正性）。**
固定两历史参考

$$
z=\frac{(1,\mathrm i)^T}{\sqrt2},\qquad R=zz^\dagger.
$$

对任意有限 Hermitian 矩阵 $D\in M_k(\mathbb C)$，下列条件等价：

$$
D\ge0
\quad\Longleftrightarrow\quad
\mathbf1_E^\dagger(D\otimes R^{\otimes m})\mathbf1_E\ge0
\quad\text{对所有 }m\ge0,\quad
E\subseteq\{1,\ldots,k\}\times\{0,1\}^m .
\tag{2.2}
$$

参考满足 $\operatorname{tr} R=1$ 和 $\mathbf1^\dagger R\mathbf1=1$。

证明。
若 $D\ge0$，张量积正性立即给右侧。
反向写 $z^{\otimes m}$ 的路径分量为
$2^{-m/2}\mathrm i^{|a|}$，其中 $|a|$ 为二进制串中一的个数。
当 $m=3$，四种相位 $1,\mathrm i,-1,-\mathrm i$ 的数量分别为 $(1,3,3,1)$。
若第 $m$ 级各类数目为 $n_r(m)$，则
$n_r(m+1)=n_r(m)+n_{r-1}(m)$，下标模四；
故四类的最少数量至少为 $2^{m-3}$，可以任意增大。

任给 Gaussian 整数向量 $d\in\mathbb Z[\mathrm i]^k$，
对足够大的 $m$，可选互不相交的参考历史子集 $A_i$，
按实部、虚部的正负分别取对应相位，使

$$
\sum_{a\in A_i}(z^{\otimes m})_a
       =2^{-m/2}\overline d_i.
$$

取 $E=\bigcup_i\{i\}\times A_i$，右侧假设便给
$2^{-m}d^\dagger Dd\ge0$。
先用齐次性扩到 Gaussian 有理向量，
再用有限二次型的连续性和其稠密性扩到全部 $c\in\mathbb C^k$，
得到 $c^\dagger Dc\ge0$。
最后两种归一化分别由 $\left\lVert z\right\rVert^2=1$、
$|\sum_i z_i|^2=1$ 得到。
∎

这使“相融、递归”的直觉得到进一步推进：
不一定要预置无限多种相位参考，
一个已经校准的四分之一相位种子，配合任意次数的独立复合与共同事件非负，
就能要求整个核强正。
但这里有三个不能省去的条件：
种子相位、张量独立复合以及历史振幅的相干合并。
若各路径已经留下不能重合的正交记录，
对事件粗粒化只会加概率，而不会产生证明中的复数子集和。

该种子可放在 AURIC 的任意两个已支持相干制备的模式中，
例如 $0$ 和 $13$。
定理在两模式已经成立，所以它不证明五模式是所有量子理论的绝对最小单元。量词中的参考深度 $m$ 任意大：每次测试只用有限载体，但并没有一个事先固定的有限联合载体覆盖全部 $m$。高斯有理近似依赖被测试的负方向和误差裕量；上述等价是精确的全域判据，不是有限样本、有限精度下的取得算法。
它也不等价于“能复制一个普通两维密度矩阵，就能直接测得式 (2.2) 的全部历史权重”；
物理实现这些联合事件需要另外的干涉合同。

**推论 2.11（相位种子的普通状态测试版本）。**
另取迹一 Hermitian 候选状态 $D\in M_k(\mathbb C)$；
这里的归一化是 $\operatorname{tr} D=1$，不沿用历史总和归一化。
若供应任意 $R^{\otimes m}$ 和每个非空集合 $E$ 对应的联合投影

$$
F_E=|u_E\rangle\langle u_E|,\qquad
|u_E\rangle=|E|^{-1/2}\sum_{a\in E}|a\rangle,
$$

则全部测试读数
$\operatorname{tr}[(D\otimes R^{\otimes m})F_E]\ge0$
当且仅当 $D\ge0$。

证明。
读数恰为式 (2.2) 左侧联合二次型除以正数 $|E|$，
故符号不变，应用定理 2.10。
∎
若换成普通基测量粗粒化
$P_E=\sum_{a\in E}|a\rangle\langle a|$，读数只有对角项，结论不成立。
$F_E$ 则需要对集合内标签作共同相干比较；
一些 $u_E$ 在系统与参考的划分上还是纠缠向量。
这精确指出该桥梁使用了什么联合操作资源。

## 3. 两分量预测为何可以迫使复数乘法

上一节直接写复核，留下了“为什么是复数”的问题。
本节给一条更接近正交读出直觉的局部路线：
先给一个实二维的校准平面，考察其权重与串联规律。
两个实分量、欧氏正交和可用的组合是本节的输入，
不是先前五个标签已经证明的结论。

**定义 3.1（局部预测平面的操作条件）。**
令 $A$ 为二维实内积空间，给单位向量 $1$。
允许备选振幅作向量加法，并给强度 $W:A\to[0,\infty)$，要求：

1.  $W(0)=0,\ W(1)=1$，且 $W$ 在平面旋转下不变；

1.  若 $a\perp b$，则 $W(a+b)=W(a)+W(b)$；

1.  串联为双线性运算 $a\cdot b$，$1$ 是双侧单位；

1.  对所有 $a,b\in A$，
      $W(a\cdot b)=W(a)W(b)$。

第三条表达串联对备选合并的相容；
第四条是该全域代数模型中指定中间条件的标量串联规律，
不把未读取的多条路径当成独立概率事件。

**定理 3.2（正交可加与旋转相容决定平方权重）。**
定义 3.1 的前两条推出
$W(a)=\left\lVert a\right\rVert^2$。不需要另假设 $W$ 连续或可微。

证明。
旋转不变使 $W(a)=g(\left\lVert a\right\rVert^2)$，其中
$g(s)=W(\sqrt s\,1)$，$s\ge0$。
取长度为 $\sqrt s,\sqrt t$ 的两个正交向量，
得到 $g(s+t)=g(s)+g(t)$。
非负性使 $g$ 单调，归一化使 $g(1)=1$。
可加性先给非负有理数 $r$ 上 $g(r)=r$；
用递增、递减的有理数夹住任意实数 $s\ge0$，得到 $g(s)=s$。
∎

这里真正有内容的正性是全部校准输入的非负权重。
“新增记录数大于等于零”只约束整数计数，并不供应本定理的正交可加律。
同样，正交的两种*校准分量*不自动是两次可同时无扰动读取的物理结果。

**定理 3.3（二维正乘法唯一成为复乘法）。**
定义 3.1 的全部条件下，
存在与 $1$ 正交的单位向量 $u$，使

$$
u^2=-1,\qquad
(x+yu)(s+tu)=(xs-yt)+(xt+ys)u.
$$

因此 $A$ 作为带乘法及强度的实空间与 $\mathbb C$ 同构，
而 $W(x+yu)=|x+\mathrm i y|^2$。
反向定向选择 $-u$ 给复共轭约定。

证明。
在正交基 $(1,u)$ 中写 $u^2=a+bu$，$a,b\in\mathbb R$。
由上一条定理和乘性，对所有 $t\in\mathbb R$，

$$
W((t+u)u)=a^2+(t+b)^2=W(t+u)W(u)=t^2+1.
$$

比较系数得 $b=0,\ a^2=1$。
若 $a=1$，则双线性与双侧单位给
$(1+u)(1-u)=0$，但两因子的强度均为二，
与乘性要求 $0=4$ 矛盾。因此 $a=-1$。
再将一般乘积双线性展开，便得到复数乘法。
这个结果还证明该乘法结合、交换；
在此二维情形无需先把结合律另当公理。
∎

这个定理给出一个明确理由：
若每条局部预测需要两个正交实分量，强度不依赖平面方向，
且串联与备选合并能共同成立，那么虚单位的平方被迫为负一。
它比“画出了平面，因此自然是量子复平面”更精确。
几何平面本身没有规定双线性串联和强度乘性，必须补证这些接口。

Goyal--Knuth--Skilling 的操作重建同样以实数对及串并联一致性研究复振幅
[gks]。本文采用另一个全域有限充分条件及自含证明，
不声称复述了该论文全部公理的等价最小形式。
若只给一个实分量，实数仍满足对应条件；
若不固定维数，本文的二维证明不能排除其他代数。

**推论 3.4（备选相加与串联相乘的地位）。**
在上述接口中，复加法描述可相干重合的备选，
复乘法描述指定中间条件的串联。
这两种运算由任务组合方式选择，不是五标签数值之间任意运算的穷尽表。

证明。
备选的表示按定义为平面向量加法；
串联的表示由定理 3.3 恰为复乘法。
其他几何或数值任务可另有其他运算，定理没有量化到那些任务。
∎

**定理 3.5（完整正交读出给出的 Born 数值形式）。**
若 $d$ 个结果端口彼此正交，每个端口的振幅为
$a_s\in A\simeq\mathbb C$，且 $\sum_s|a_s|^2>0$，总强度按正交端口相加，
则归一化结果权重为

$$
p_s=\frac{|a_s|^2}{\sum_r|a_r|^2}.
$$

对归一化 $\psi\in\mathbb C^d$，在任意实际供应的正交基 $(e_s)$ 中，
$p_s=|\langle e_s,\psi\rangle|^2$。

证明。
每个端口的强度由定理 3.2 为 $|a_s|^2$。
用非零总强度归一化即得第一式；
取 $a_s=\langle e_s,\psi\rangle$，Parseval 恒等式使总强度为一。
∎

这是数值形式的条件推导。把强度解释为重复记录的发生概率，
仍需要实际制备、读出与频率的标定合同。
它也不宣布任意正交基或任意 POVM 都已可实现。
既有条件表示的全效果版本属于 Busch 型定理 [busch]；
该版本需要全效果赋值域及非情境合并一致性。

## 4. 递归什么时候必然表现为相位波

### 有限闭合预测的主定理

**定义 4.1（平稳相干递归）。**
给强正核 $(\mathscr P,\mathcal K)$ 与接续 $r:\mathscr P\to\mathscr P$，
要求每对预测满足

$$
\mathcal K(rp,rq)=\mathcal K(p,q).
\tag{R}
$$

称式 (R) 为交叉关系守恒。
它远强于只检查 $\mathcal K(rp,rp)=\mathcal K(p,p)$。

**定理 4.2（相容递归的离散波表示）。**
在定义 4.1 下，沿 [recursive] §2 与 [quantum] §6 的保核下降接口，接续唯一诱导一个等距
$U:H\to H$，满足 $Uv_p=v_{rp}$。
如果 $H$ 有限维，或接续像的线性张成稠密，则 $U$ 为酉。
有限维时存在两两正交谱投影 $P_j$ 和相位 $\theta_j$，使

$$
U=\sum_j e^{-\mathrm i\theta_j}P_j,\qquad
U^n\psi=\sum_j e^{-\mathrm i n\theta_j}P_j\psi.
\tag{4.1}
$$

对固定读出向量 $e_s$，

$$
a_s(n)=\sum_j e^{-\mathrm i n\theta_j}
              \langle e_s,P_j\psi\rangle
$$

就是由该递归产生的预测振幅波。

证明。
先在自由有限和上令 $[p]\mapsto[rp]$ 并线性延拓。
式 (R) 使每个有限组合的范数保持，因此零关系保持，
该映射下降到定理 2.2 的商并连续延拓为等距。
有限维等距单射必满射；一般情形若像稠密，
又因等距像闭，则仍满射。
有限维酉矩阵由谱定理正交对角化，本征值模为一，
给式 (4.1) 及其指定坐标。
∎

这个结论没有先要求空间中存在连续正弦曲线。
离散的递归层数 $n$ 已足以产生相位因子和相互抵消。
连续画出的波形可以是其插值表示，但插值本身仍有选择。

**命题 4.3（单独保留每个预测的权重不够）。**
存在对两个生成描述各自保范数的接续，却不能下降为共同空间上的等距。

证明。
取两正交单位向量 $v_1,v_2$，把二者都送到同一个单位向量 $w$。
每个生成元范数均保持，但 $v_1-v_2$ 的平方范数从二变成零，
而 $v_1+v_2$ 的平方范数从二变成四。
缺失的约束是交叉内积。
∎

**定理 4.4（一般有限递归可以变成保范数波的判据）。**
对复矩阵 $T$，存在正定 Hermitian 度量 $G$ 满足
$T^\dagger GT=G$，当且仅当 $T$ 可对角化且全部特征值模为一。

证明。
若存在 $G$，则 $S=G^{1/2}TG^{-1/2}$ 满足 $S^\dagger S=I$，
所以 $S$ 酉并可正交对角化，$T$ 与它相似。
反向若 $T=V\Lambda V^{-1}$ 且 $\Lambda^\dagger\Lambda=I$，
取 $G=(V^{-1})^\dagger V^{-1}>0$，直接相乘得所需恒等式。
∎

因此“具有递归”与“具有保相位的波”之间有明确代数边界。
增长、衰减或非平凡 Jordan 块一般不会满足这个判据。
另一方面，满足判据也不独属于量子系统；
经典周期置换的 Koopman 表示同样可以是酉。

### 一个预测自身的关系谱

**定理 4.5（有限秩平稳相关的正谱分解）。**
设 $U$ 为有限维酉，$\left\lVert \psi\right\rVert=1$，
令 $c(n)=\langle\psi,U^n\psi\rangle$，$n\in\mathbb Z$。
则

$$
c(n)=\sum_{j=1}^r w_j e^{-\mathrm i n\theta_j},
\qquad w_j>0,\quad \sum_jw_j=1,
\tag{4.2}
$$

不同 $\theta_j$ 按模 $2\pi$ 合并，只保留有非零权重的项。
反之任何这样的有限正谱和都给一个强正平稳核
$\mathcal K(m,n)=c(n-m)$。
其最小空间维数恰为 $r$。

证明。
取 $w_j=\left\lVert P_j\psi\right\rVert^2$ 并删除零项，谱展开给第一式。
反向在 $\mathbb C^r$ 取
$\psi=(\sqrt{w_j})$、$U=\operatorname{diag}(e^{-\mathrm i\theta_j})$，
则 $\mathcal K(m,n)=\langle U^m\psi,U^n\psi\rangle$，故强正。
不同特征相位的 Vandermonde 矩阵可逆，
所以 $\psi,U\psi,\ldots,U^{r-1}\psi$ 张成全部 $r$ 个方向，
由最小表示的秩结论即得。
∎

式 (4.2) 的权重是*指定循环向量的谱权重*，
不是不经标定便自动等于五个模式的点击概率。
完整相关核决定这一个循环系统到酉等价，
但没有给出实验中每个结果端口的位置。

**推论 4.6（有限预测波的精确递归阶数）。**
设式 (4.2) 中 $z_j=e^{-\mathrm i\theta_j}$ 互异，
$p(z)=\prod_{j=1}^r(z-z_j)=\sum_{k=0}^r b_kz^k$。
则

$$
\sum_{k=0}^r b_k c(n+k)=0\quad(n\in\mathbb Z).
$$

在全部 $w_j>0$ 时，不存在次数小于 $r$ 的非零多项式给出同样恒等式。

证明。
将谱和代入，内层为 $p(z_j)=0$。
若更低次数多项式也成立，指数序列 $z_j^n$ 的线性独立性
使该多项式在每个 $z_j$ 上为零，不可能。
∎

这为“递归结构决定波”提供有限的精确形式：
递归系数决定允许的相位根，初始条件决定谱权重和相位组合。
但从若干有限、带误差的样本估计这些对象，
还需要可识别性、阶数上界和稳定性分析。

**命题 4.7（概率波动与量子相干不是同一个判据）。**
有复特征值、周期或正相关核，均不足以区分量子与经典模型。

证明。
三个经典状态的确定循环置换有谱
$1,e^{2\pi\mathrm i/3},e^{-2\pi\mathrm i/3}$，其状态仍是三点概率分布。
对任意经典平方可积随机变量族 $X_p$，核
$\mathcal K(p,q)=\mathbb E(\overline X_pX_q)$ 也强正，
因为其二次型是 $\mathbb E|\sum c_pX_p|^2$。
这些性质没有供应物理相干重组、非交换测量和复合量子操作。
∎

### 向前增长、连续时间与能量零点

**命题 4.8（单侧无限递归只先给等距）。**
在 $\ell^2(\mathbb N)$ 上的移位 $Se_n=e_{n+1}$ 保持全部内积，
但不是满射。它可以嵌入 $\ell^2(\mathbb Z)$ 的双侧酉移位。
因此不应由“只向前增加一个记录”直接推出当前载体上已有可逆时间群。

证明。
基向量的内积保持，而 $e_0$ 不在 $S$ 的像中。
在双侧整数基上令 $Ve_n=e_{n+1}$，逆为 $V^{-1}e_n=e_{n-1}$；
限制到非负整数生成的子空间即恢复单侧移位。
∎

一般等距也有同类最小酉扩张：取其迭代嵌入的直接极限，
将新副本视作旧副本的前驱，使移位取得逆。
这个构造是在更大空间上补足表示；
不能将补出的负层数当成观察者实际已取得的历史。

一般等距的扩张可以明确构造。取副本 $H_n=H$，以 $U:H_n\to H_{n+1}$ 作嵌入，等同 $[x,n]=[Ux,n+1]$。两代表的内积先搬到共同较大层计算，因 $U$ 等距而不依赖该层。商后完备化得到 $\widetilde H$。定义

$$
\widetilde U[x,n]=[Ux,n],\qquad
\widetilde U^{-1}[x,n]=[x,n+1],\qquad Jx=[x,0].
$$

这些定义保持等价关系、保内积且互逆，因此给酉；并且 $\widetilde UJ=JU$。各 $[H,n]=\widetilde U^{-n}JH$ 的并稠密，给最小扩张。扩张载体与已获得记录仍是不同对象。

**定理 4.9（可微时间标定给 Schrödinger 形式）。**
固定 $\hbar>0$。在有限维 Hilbert 空间上，若已供应可微一参数酉群 $U(t)$，
则存在唯一 Hermitian $H$ 使
$U(t)=e^{-\mathrm i tH/\hbar}$，
且 $\mathrm i\hbar\,\dot\psi=H\psi$。
反之任意 Hermitian $H$ 定义这种群。
单个离散酉 $U$ 不唯一决定 $H$。

证明。
令 $A=U'(0)$。对 $U(t)^\dagger U(t)=I$ 求导得
$A^\dagger=-A$；群律给 $U'(t)=AU(t)$。
取 $H=\mathrm i\hbar A$，常系数微分方程给所述指数。
反向直接求导验证。
固定采样间隔 $\Delta t>0$。若 $U=\sum_j e^{-\mathrm i\theta_j}P_j$，任意整数 $k_j$ 给

$$
H=\frac{\hbar}{\Delta t}\sum_j(\theta_j+2\pi k_j)P_j
$$

都满足 $e^{-\mathrm i\Delta tH/\hbar}=U$，所以离散采样无法唯一选定频率分支。
∎

有限维连续一参数酉群也自动可微：其成员彼此对易，
可共同对角化，连续的一维群字符为 $e^{-\mathrm i\omega t}$。
连续时间群是额外标定，尚未由五个离散标签推出。
$\hbar$ 则连接相位速率和能量单位，纯图结构不能给出其数值。

**命题 4.10（读出波通常看到能级差）。**
若 $\psi(t)=\sum_j e^{-\mathrm i E_jt/\hbar}P_j\psi$，
则固定效果 $E$ 的读数为

$$
p_E(t)=\sum_{jk}e^{\mathrm i(E_j-E_k)t/\hbar}
                 \langle P_j\psi,E P_k\psi\rangle.
$$

$H\mapsto H+cI$ 不改变任何这种未受相干控制的系统内读数。

证明。
直接展开 $\langle\psi(t),E\psi(t)\rangle$。
公共能量平移只给所有振幅同一个相位，乘共轭后消失。
∎

若把不同实现路径与外部参考作相干控制，原先的“整体相位”可能成为相对相位；
那是扩大的操作合同，不能在原来的系统内读出中凭空加入。

## 5. 项目五模式上的具体预测波

### 金字塔关系与实际耦合图的区分

五模式金字塔的几何图示与项目实际等待 Hamiltonian 的耦合图不是同一张图。
后者由合法单位置翻转给定，按 $(0,1,2,3,13)$ 排列为

$$
K=\begin{pmatrix}
0&1&1&1&0\\
1&0&0&0&1\\
1&0&0&0&0\\
1&0&0&0&1\\
0&1&0&1&0
\end{pmatrix},\qquad U(\tau)=e^{-\mathrm i\tau K}.
\tag{5.1}
$$

这是项目已经供应的动力学，见 [second]、[qmb]。
若另给物理时钟，可写 $H=\hbar\Omega K$、$\tau=\Omega t$；
在 $t\ge0,\ \tau\ge0$ 的等待合同中须取 $\Omega>0$。

合法翻转图的边集为 $\{0\! -\!1,1\! -\!13,13\! -\!3,3\! -\!0,0\! -\!2\}$：一个四环和一条叶边。

它有五条边。把它直接当作欧氏四棱锥的全部棱，
或把它当作已经展开时间层的 DAG，都会改变对象。
相同模式在不同递归层出现时，应使用顶点 $(n,s)$；
时间展开图的边从第 $n$ 层到第 $n+1$ 层，依然可以无有向环。
不同展开路径可以在共同终点干涉，并不要求 DAG 自己含有有向闭环。

[static] §1 的原菜单在同一个 $\mathbb C^5$ 上允许全部复密度输入；控制仅含固定 $K$ 的非负等待、完整秩一 Lüders 仪器 $\mathcal J_s(X)=P_sXP_s$、Stop 和有限记录反馈及输入无关经典随机化。经典合并完整读取结果不等于保留粗块相干的另一种 Lüders 仪器。被动实帧 $D=\operatorname{diag}(1,i,i,i,1)$ 中 $D^\dagger U(\tau)D$ 实正交；这不限制未知输入为实态，也不增加独立相位控制。

**定理 5.1（原子双频谱与暗态：项目结果的复算）。**
令

$$
r=\sqrt{17},\qquad
\omega_\pm=\sqrt{\frac{5\pm r}{2}}.
$$

则

$$
\det(\lambda I-K)=\lambda(\lambda^4-5\lambda^2+2),
\qquad
\operatorname{Spec} K=\{0,\pm\omega_+,\pm\omega_-\}.
$$

零模为
$d=(|1\rangle-|3\rangle)/\sqrt2$。

证明。
将二部顺序改为 $(0,13)\mid(1,2,3)$，则

$$
K=\begin{pmatrix}0&B\\B^\dagger&0\end{pmatrix},\qquad
B=\begin{pmatrix}1&1&1\\1&0&1\end{pmatrix},\qquad
BB^\dagger=\begin{pmatrix}3&2\\2&2\end{pmatrix}.
$$

后一个矩阵的迹为五、行列式为二，
故其两个正特征值是 $\omega_\pm^2$。
$B$ 的每个奇异值给 $K$ 一对正负本征值；
$B$ 秩二，核为右侧的 $(1,0,-1)$ 方向，给唯一零模。
∎

这两种频率、两个实旋转平面及暗线，
已出现在项目《实际等待读出下的近似单份量子边界》定理 4.1 的证明中
[qmb]；亮暗态的直接动力学见《二阶关系完成》定理 63.2
[second]。
这里复算它们是为了连接新问题，而非提出首次发现的主张。

**定理 5.2（从空模式出发的明确波形）。**
设初态为 $|0\rangle$，定义

$$
w_\pm=\frac{1\pm1/\sqrt{17}}2.
$$

返回振幅和对角模式振幅分别为

$$
\begin{aligned}
c_0(\tau)&=\langle 0|U(\tau)|0\rangle
   =w_+\cos(\omega_+\tau)+w_-\cos(\omega_-\tau),\\
a_{13}(\tau)&=\langle 13|U(\tau)|0\rangle
   =\frac2{\sqrt{17}}
      \bigl[\cos(\omega_+\tau)-\cos(\omega_-\tau)\bigr].
\end{aligned}
\tag{5.2}
$$

该初态的循环子空间恰为四维。

证明。
令 $Q=BB^\dagger$。
矩阵指数的偶次项给左上块 $\cos(\tau\sqrt Q)$。
其两个谱投影为

$$
P_+=\frac{Q-\omega_-^2I}{\sqrt{17}},\qquad P_-=I-P_+.
$$

取 $(0,0)$ 与 $(13,0)$ 项即得式 (5.2)。
暗态与 $|0\rangle$ 正交；
四个非零频率的谱权重分别为 $w_+/2,w_+/2,w_-/2,w_-/2$，
全部严格为正，因此循环空间维数为四。
∎

五个合法结果不意味着每个初态都激发五个可见频率。
零模在这个初态中没有权重，不能把它缺席解读为该模式不存在。
而 $p_0(\tau)=|c_0(\tau)|^2$ 的振荡包含
$2\omega_+,2\omega_-,\omega_++\omega_-,\omega_+-\omega_-$ 等频差。
项目另一个加权读出算子的谱也不是 $K$ 的谱，尽管都来自同一原子。

这里的四维是连续时间族 $\{U(\tau)|0\rangle:\tau\in\mathbb R\}$ 的循环维数。四个不同能量 $\pm\omega_\pm$ 的投影均非零；四个投影向量是正交的。对连续指数求前四阶导数所得 Vandermonde 矩阵可逆，因而这四个投影都在循环张成中。若固定间隔 $\Delta\tau$ 采样，则相位 $e^{\mp i\omega_\pm\Delta\tau}$ 可能重合，样本相关的最小递归阶数只等于合并后的不同相位数。例如 $\Delta\tau=\pi/\omega_+$ 时，$+\omega_+$ 与 $-\omega_+$ 的相位都为 $-1$，不再给四阶。连续循环秩四不意味着每个采样酉都有循环秩四。

**推论 5.3（有限相融原子不必定格，也不必严格周期）。**
从 $|0\rangle$ 出发，任意 $\tau>0$ 都没有精确返回原射线；
但存在趋于无穷的一列时刻使态任意接近初态。

证明。
因为

$$
\frac{\omega_+^2}{\omega_-^2}
=\frac{21+5\sqrt{17}}4
$$

无理，$\alpha=\omega_+/\omega_-$ 也无理。
若返回同一射线，返回概率必须为一。
式 (5.2) 是两个余弦的严格正凸组合，
其绝对值为一只能是两个余弦同时为一，或同时为负一。
对 $\tau>0$，这使两频率之比为两个非零整数之比，矛盾。

对近似返回，在 $0,\alpha,\ldots,N\alpha$ 的小数部分中用抽屉原理，
可得 $1\le n\le N$ 使 $n\alpha$ 距某整数至多 $1/N$。
沿 $N\to\infty$ 可选无界子列，否则无理数有某固定非零整数倍恰为整数。
取 $\tau_n=2\pi n/\omega_-$，
四个有权频率的相位都趋于一，故 $U(\tau_n)|0\rangle\to|0\rangle$。
∎

因此两面镜子的比喻应区分：逻辑闭合、有限分辨率不可区分、
振幅递归回归，以及真实耗散收敛。
本例的精确递归保持相干，产生准周期波；它没有要求最后停住。

### 从底面的两条路到唯一闭路相位

**定义 5.4（边连接与顶点坐标）。**
在同一图上给 Hermitian 边耦合
$H_{ab}=w_{ab}e^{\mathrm i A_{ab}}$，
$w_{ab}>0,\ A_{ba}=-A_{ab}$。
被动坐标变换为

$$
\psi'=D_\chi\psi,\quad H'=D_\chi HD_\chi^\dagger,
\quad E'=D_\chi ED_\chi^\dagger,\quad
D_\chi=\operatorname{diag}(e^{\mathrm i\chi_a}).
$$

于是 $A'_{ab}=A_{ab}+\chi_a-\chi_b$。

**定理 5.5（闭路保留的关系信息）。**
有限连通图的非零 Hermitian 边相位在顶点重相位下，
可以消去一棵生成树上的全部相位；
剩下 $|E|-|V|+1$ 个独立环相位。
对五模式翻转图恰有一个，可取

$$
\varphi=\arg\!\left[
H_{13,3}H_{3,0}\,
\overline{H_{13,1}H_{1,0}}\right].
\tag{5.3}
$$

叶边 $0$--$2$ 的相位不提供额外环不变量。

证明。
固定根相位，沿生成树逐个选择子顶点相位，
使每条树边变为正实数。
每条非树边与唯一树路径构成一个基本环，
其相位不能再由保持树规范的顶点变换改变。
沿环乘积中的中间顶点相位两两抵消。
连通图生成树有 $|V|-1$ 条边，故剩余数目如上。
本图五顶点五边，所以只有一个；式 (5.3) 是两条共同端点路径的相对相位。
∎

这里的“关系不可删除”是精确规范命题。
它不要求 $\varphi$ 非零，也没有给出它的数值分布。
所有边取正实数就是合法的 $\varphi=0$ 模型。
若要求存在沿每条边都平行不变的非零标量截面，
则该截面必须被所有环 holonomy 固定；在本图上要求 $e^{\mathrm i\varphi}=1$。
但一般量子态不需要是这种全局平行截面。
非零环相位仍可定义完全正常的 Hermitian Hamiltonian
[wave]。

既有条件表示及项目关系丛接口中的态关系角 [bundle]

$$
\Phi_{\rm state}=\theta_0+\theta_{13}-\theta_1-\theta_3
$$

与式 (5.3) 也不同。
它对整体和单位置相位不变，但不对任意五个顶点的独立重相位不变；
边环相位则是连接的规范不变量。
将二者联系起来，需要另给动力学方程，不能因为都由四角写成便认成同一变量。

与 [tunnel] §5 的失谐族比较时，必须使用同一矩阵对应：该篇 $(13,3)$ 元为 $Je^{-i\phi_{\rm T}}$，这里为 $e^{i\varphi}$，所以在无量纲矩阵中取 $J=g=1$、$\phi_{\rm T}=-\varphi$，并把该篇共同内部失谐置为零。该篇模型声明 $\Delta>0$，故不能直接援引只在正失谐下陈述的估计；零失谐在下面从完整矩阵另算。若使用物理能量矩阵，应取 $J=g=\hbar\Omega$、$\Delta=0$、$\tau=\Omega t$、$\Omega>0$。其奇异值分解机制与下证相同，环取向与参数域已分别声明。[second] §63.3 使用 $\arg(a\overline b)$，这里式 (5.3) 则使用 $\arg(b\overline a)$，两者相差一个负号。

**定理 5.6（单环相位的精确谱与全时间干涉）。**
另允许一个复边耦合模型：保留单位边模长与零对角，
令 $(K_\varphi)_{13,3}=e^{\mathrm i\varphi}$，
其 Hermitian 共轭边为 $e^{-\mathrm i\varphi}$，其余非零边为一。
设

$$
\delta_\varphi=\sqrt{9+8\cos\varphi},\qquad
\nu_\pm=\sqrt{\frac{5\pm\delta_\varphi}{2}}.
$$

则

$$
\det(\lambda I-K_\varphi)
=\lambda\bigl[\lambda^4-5\lambda^2+4-2\cos\varphi\bigr],
\tag{5.4}
$$

$$
\langle 13|e^{-\mathrm i\tau K_\varphi}|0\rangle
=\frac{1+e^{\mathrm i\varphi}}{\delta_\varphi}
   \bigl[\cos(\nu_+\tau)-\cos(\nu_-\tau)\bigr].
\tag{5.5}
$$

特别地，$\varphi=\pi$ 时全部时刻的 $0\to13$ 转移振幅严格为零。

证明。
在二部顺序中有

$$
B_\varphi=
\begin{pmatrix}1&1&1\\1&0&e^{\mathrm i\varphi}\end{pmatrix},
\quad
Q_\varphi=B_\varphi B_\varphi^\dagger
=\begin{pmatrix}3&1+e^{-\mathrm i\varphi}\\1+e^{\mathrm i\varphi}&2\end{pmatrix}.
$$

$Q_\varphi$ 的迹为五，行列式为 $4-2\cos\varphi$，
故特征值为 $\nu_\pm^2$，由奇异值分解得到式 (5.4)。
因 $\delta_\varphi\ge1$，谱投影
$(Q_\varphi-\nu_-^2I)/\delta_\varphi$ 总有定义。
按定理 5.2 的矩阵余弦方法取 $(13,0)$ 项，即得式 (5.5)。
$\varphi=\pi$ 时 $Q_\varphi=\operatorname{diag}(3,2)$，该非对角项恒为零。
∎

全部相位端点也可以从这同一个块证明中读出。$\delta_\varphi\in[1,\sqrt{17}]$、$\det Q_\varphi=4-2\cos\varphi\in[2,6]$，故 $B_\varphi$ 对所有相位均秩二，$\nu_+>\nu_->0$，$K_\varphi$ 始终秩四、零模恰一维，可取

$$
d_\varphi=\frac{-e^{i\varphi}|1\rangle+(e^{i\varphi}-1)|2\rangle+|3\rangle}
{\sqrt{4-2\cos\varphi}}.
$$

直接乘 $B_\varphi$ 得零，范数为一，所以没有遗漏隐藏的秩端点。$|0\rangle$ 的两余弦权重是

$$
w_\pm(\varphi)=\frac{1\pm1/\delta_\varphi}{2}.
$$

$\varphi\not\equiv\pi$ 时两者严格正，连续循环维数为四；$\varphi\equiv\pi$ 时 $w_-=0$，$|0\rangle$ 只激发 $\pm\sqrt3$，循环维数为二，虽然整个 $K_\pi$ 仍秩四。此时暗线为 $(|1\rangle-2|2\rangle+|3\rangle)/\sqrt6$，$|13\rangle$ 的独立频率为 $\sqrt2$，全时不可达是分块正交导致的。$\varphi\equiv0$ 时恢复 $\delta=\sqrt{17}$ 及定理 5.1–5.2；暗线只差一个无意义的整体符号。这里的相位同余均按模 $2\pi$。一般采样仍要合并同相位的谱根，不能用矩阵秩代替采样递归阶数。

因此转移概率为

$$
p_{13}(\tau\mid0)
=\frac{2+2\cos\varphi}{9+8\cos\varphi}
  \bigl[\cos(\nu_+\tau)-\cos(\nu_-\tau)\bigr]^2.
\tag{5.6}
$$

短时展开给
$p_{13}(\tau\mid0)=\tau^4\cos^2(\varphi/2)+O(\tau^6)$，
与项目定理 63.3 的两最短路径公式一致 [second]。
式 (5.4)--(5.6) 是在该文已经允许的复边扩展上作的显式计算；
并不是原菜单不经增添相位控制就能自由扫描的实验。

全消干涉不是删掉了两条路。它表示两条路的相位关系，
使所有路径重求和后的该终端振幅恰好为零。
这正是“边决定对角模式的预测”能够有具体含义的地方：
不是 $F[2]$ 的一个数值自行选出加法或乘法，
而是共同耦合、串联乘积和备选重合一起确定结果。

**命题 5.7（限制基态制备时的环相位取向盲性）。**
对于固定 $\varphi$ 与 $-\varphi$，
基态制备、等待、完整模式 Lüders 读出及经典自适应停止组成的全部协议，
产生相同的记录分布。
但若将这一受限制备域扩为允许固定相位参考的初态
$(|13\rangle+|3\rangle)/\sqrt2$，
则在无量纲时间中

$$
\left.\frac{d}{d\tau}p_{13}(\tau)\right|_{\tau=0}
=\sin\varphi,
$$

一般可以区分两种符号。

证明。
置 $C=\operatorname{diag}(1,-1,-1,-1,1)$。
二部结构给 $CK_\varphi C=-K_\varphi$，
而 $K_{-\varphi}=\overline{K_\varphi}$。
故

$$
U_{-\varphi}(\tau)
=\overline{U_\varphi(-\tau)}
=C\,\overline{U_\varphi(\tau)}\,C.
$$

所有矩阵元模平方相等。
完整读出后的条件态是所读基态；
沿任意同一记录历史，下一等待的条件转移概率相同。
逐层相乘并对经典随机选择求平均，得到全部记录律相同。
对于额外初态，直接用
$\dot p_{13}=2\Im(\overline{\psi_{13}}(K_\varphi\psi)_{13})$，
在零时刻得到 $\sin\varphi$。
∎

所以“关系大致确定”应进一步问：相对于哪个未来操作集合确定？
上述限制基态制备的相位扩展实验无法判断环相位的取向；
允许所列相干制备后，同一个差异就成为可读信息。
这里的限制不能冒充项目全部输入域的限制：
项目原模型的量子输入合同允许一般复密度态，
而整个 $K_\varphi$ 家族本来就是对固定 $K$ 的额外动力学扩展。

## 6. 边是预测时，幅度、相位与隐藏势怎样共同演化

### 图上的连续性与幅相方程

**定理 6.1（有限图上精确的概率流）。**
设 $\mathrm i\hbar\,\dot\psi=H\psi$，$H=H^\dagger$，
$p_a=|\psi_a|^2$。定义

$$
J_{b\to a}=\frac2\hbar
\Im\bigl(\overline{\psi_a}H_{ab}\psi_b\bigr).
$$

则

$$
\dot p_a=\sum_bJ_{b\to a},\qquad
J_{b\to a}=-J_{a\to b},\qquad
\sum_a\dot p_a=0.
\tag{6.1}
$$

在全部有关 $p_a>0$ 的坐标区间，
写 $\psi_a=\sqrt{p_a}e^{-\mathrm i\theta_a}$，
$H_{ab}=w_{ab}e^{\mathrm i A_{ab}}$，$H_{aa}=\epsilon_a$，则

$$
\begin{aligned}
\dot p_a&=\frac2\hbar\sum_{b\ne a}
 w_{ab}\sqrt{p_ap_b}\sin(A_{ab}+\theta_a-\theta_b),\\
\hbar\dot\theta_a&=\epsilon_a+
 \sum_{b\ne a}w_{ab}\sqrt{\frac{p_b}{p_a}}
                 \cos(A_{ab}+\theta_a-\theta_b).
\end{aligned}
\tag{6.2}
$$

证明。
对 $p_a=\overline{\psi_a}\psi_a$ 求导并代入 Schrödinger 方程，
得到第一式。Hermitian 性使对换端点后括号取共轭，虚部变号，
求和即守恒。
再将极坐标代入
$\mathrm i\hbar\,\dot\psi_a/\psi_a$，
分别比较实部与虚部，得到式 (6.2)。
∎

这里采用负指数相位 $\psi_a=\sqrt{p_a}e^{-i\theta_a}$，与 [bundle] 定义 3.4 的约定相同；该篇定理 3.5 的关系角 $\chi=\theta_0-\theta_1-\theta_3+\theta_{13}$ 就是此处的 $\Phi_{\rm state}$，角度均按模 $2\pi$ 理解。该篇命题 10.3 的联合占位相位门 $e^{-i\alpha N_xN_y}$ 只对模式 $13$ 乘以 $e^{-i\alpha}$，故 $\theta_{13}$ 增加 $\alpha$，此处同样有 $\Phi_{\rm state}\mapsto\Phi_{\rm state}+\alpha$，全部概率不变；该门的可用性是另供的操作条件。被动规范下 $\theta'_a=\theta_a-\chi_a$，于是 $A'_{ab}+\theta'_a-\theta'_b=A_{ab}+\theta_a-\theta_b$，概率流不变。态关系角只在所用四个分量全非零的支撑区间内定义；环通量描述连接，两者的类型没有合并。

式 (6.2) 给“稳定可见的占据下面，变化藏在关系上”的精确表达：
只知道所有 $p_a$，仍不一般知道各条边的流。
相位差与连接一起决定下一刻概率怎样变化。
在某些时刻全部概率导数为零，也不保证以后概率不变。
当某个 $p_a=0$ 时，相位坐标失效，原线性方程却仍然正常。

**命题 6.2（对角相位可在概率完全不变时增长）。**
对 $H=\operatorname{diag}(\epsilon_a)$，每个 $p_a(t)$ 恒定，
而 $\theta_a(t)=\theta_a(0)+\epsilon_at/\hbar$。
若随后加入一个实际允许的非对角比较，
这些相位差可以转化为不同的结果概率。

证明。
解为 $\psi_a(t)=e^{-\mathrm i\epsilon_at/\hbar}\psi_a(0)$。
对两非零分量使用效果
$|+\rangle\langle +|$，$|+\rangle=(|a\rangle+|b\rangle)/\sqrt2$，
其概率包含 $\Re(\overline{\psi_a(t)}\psi_b(t))$，
所以依赖相位差。这个效果的可用性是所述后续比较的前提。
∎

**命题 6.3（时间相关的坐标规范改变局域势）。**
若 $\psi'=D_{\chi(t)}\psi$，则相同物理预测的生成元为

$$
H'=D_\chi HD_\chi^\dagger
       -\hbar\operatorname{diag}(\dot\chi_a).
\tag{6.3}
$$

因此单个对角能量的坐标值并非独立于时间相位参考的绝对量。

证明。
对 $\psi'=D_\chi\psi$ 求导：
$\mathrm i\hbar\dot\psi'
=[\mathrm i\hbar\dot D_\chi D_\chi^\dagger+D_\chi HD_\chi^\dagger]\psi'$。
又 $\dot D_\chi D_\chi^\dagger=\mathrm i\operatorname{diag}(\dot\chi_a)$。
∎

这是一条有限维规范协变公式，尚不是电磁场或引力的推导。
只有把具体耦合与实际时空、作用量及测量连接后，
才可讨论它们是否对应已知物理势。

### 隐藏模式被消去时，首先出现的是记忆

**定理 6.4（隐藏叶的精确消元）。**
保留四环为可见部分 $v(t)\in\mathbb C^4$，
把模式 $2$ 写为隐藏振幅 $q(t)\in\mathbb C$。
取 $\hbar=1$，给实耦合 $g$、实隐藏能量 $\epsilon$，
以及 $K_\square=K_\square^\dagger$：

$$
\mathrm i\dot v=K_\square v+g e_0q,\qquad
\mathrm i\dot q=g e_0^\dagger v+\epsilon q.
$$

则可见振幅精确满足

$$
\begin{aligned}
\mathrm i\dot v(t)={}&K_\square v(t)
 +g e_0e^{-\mathrm i\epsilon t}q(0)\\
&-\mathrm i g^2\int_0^t e^{-\mathrm i\epsilon(t-s)}
                     P_0v(s)\,ds,\qquad P_0=e_0e_0^\dagger.
\end{aligned}
\tag{6.4}
$$

对定态能量 $E\ne\epsilon$，相应方程为

$$
\left[K_\square+\frac{g^2}{E-\epsilon}P_0\right]v=Ev.
\tag{6.5}
$$

证明。
对隐藏分量的一阶线性方程用积分因子：

$$
q(t)=e^{-\mathrm i\epsilon t}q(0)
 -\mathrm i g\int_0^t e^{-\mathrm i\epsilon(t-s)}e_0^\dagger v(s)\,ds.
$$

代入可见方程得到式 (6.4)。
定态方程的第二行给
$q=g e_0^\dagger v/(E-\epsilon)$；
代入第一行即得式 (6.5)。
∎

在极点 $E=\epsilon$ 处，不能使用式 (6.5)。必须回到两块原方程：若 $g\ne0$，有 $e_0^\dagger v=0$ 及 $(K_\square-\epsilon I)v+g e_0q=0$，由它们决定是否存在本征态；若 $g=0$，可见系统已经独立，隐藏叶是单独的能量 $\epsilon$ 本征方向。$E$ 接近极点时，自能范数是 $g^2/|E-\epsilon|$；只有给出分母下界，才可使用相应有界估计。初始强迫 $ge_0e^{-i\epsilon t}q(0)$ 与卷积项有不同来源，不能通过删初始叶态同时删掉记忆。式 (6.4) 的连续积分与初始强迫采用 [tunnel] 定理 5.3 的变常数消元步骤，式 (6.5) 的定态自能采用该篇定理 5.2 的 Schur 消元步骤。该篇以两边界／三内部划分写公式；这里按四环／单叶划分取 $x=v,y=q,A=K_\square,B=ge_0,D=\epsilon,\hbar=1$，同样的积分因子及代回计算给出本定理。[recursive] 定理 5.3 直接供应 $\epsilon=0,g\ne0$ 时的四环／单叶积分与初始项，该篇 §4 供应静态匹配与离散驱动记忆接口。两种公式分别是时间域和定态域的同一全矩阵结果。

即使 $q(0)=0$，积分记忆项通常也不消失。
可见四模式的范数可以与隐藏叶交换，不能未经处理便将其当作闭合酉系统。
式 (6.5) 的能量依赖自能与式 (6.4) 的历史记忆，
是“未读关系影响未来”的两种精确形式。
要进一步用一个瞬时、与能量无关的有效势替代它，
需另有尺度分离与误差界。

[sharp] 定理 13.1 的严格作用域是既定等距 $B:\mathbb C^3\to\mathbb C^5$、原始有序字 $Q_h$、全五维实际效果、共同的复线性 CPTP 解码器以及全部复 qutrit 密度输入。它把该篇五个平均任务方程等价于 $\overline\Phi(X)=BXB^\dagger$，并进而得到每个原始正权分支 $\Phi_{h,a}(X)=BXB^\dagger$。最后这步使用秩一 Choi 支撑：

$$
|B\rangle\!\rangle\langle\!\langle B|
 =\sum_{h,a}p_{h,a}J(\Phi_{h,a}),\qquad p_{h,a}=2^{-n}r(a\mid h).
$$

正权项的支撑都只能在右侧这一条线上，且各 CPTP Choi 迹均为三，所以每项的无权 Choi 矩阵恰等于嵌入通道的 Choi 矩阵。有限或可数记录时正项和都按迹范数收敛。这保留的是原始正分支，不能先重分组再换条件概率。解码器因此只在实际角块 $BM_3B^\dagger$ 上满足相应的 $Q_h^\dagger$ 校正；在角块之外以及跨角块相干上的作用没有被分类。该矩形全输出结果是这里关于共同未来的实例供应，不把方形无扰动定理直接套到 $M_3\to M_5$。

这也给内生观察者一条实际原则：
如果以后还可能访问某个记忆、路径参考或环境相关，
它就属于预测边界需要保存的对象。
只保留三个稳定边缘分量，不能一般代表完整未来。
项目矩形通道刚性结果也强调实际全空间操作、
全部输入以及原始正概率分支的重要性 [sharp]；
其结论是在已供应的量子操作模型中成立，并非从遗漏信息自身推出量子论。

## 7. 预测波怎样给出概率与观察者的记录增长

### 相干接续与记录仪器

**定义 7.1（带结果的交叉守恒）。**
给第 $n$ 层强正预测核 $\mathcal K_n$，
一个实际动作的有限结果集 $O$ 及接续 $r_o$，要求

$$
\mathcal K_n(p,q)
=\sum_{o\in O}\mathcal K_{n+1}(r_op,r_oq)
\quad\text{对所有共同合法的 }p,q.
\tag{7.1}
$$

失败、停止也纳入 $O$；不能通过删去它们实现归一化。
本节 $H_n$ 专指本动作共同合法描述域的闭线性张成；
若要把结论用于更大的原空间，须另证明这些描述张成整个原空间。

**定理 7.2（观察的增长是保相干的记录嵌入）。**
式 (7.1) 诱导线性收缩 $M_o:H_n\to H_{n+1}$，且

$$
\sum_oM_o^\dagger M_o=I,\qquad
V\psi=\sum_oM_o\psi\otimes|o\rangle
$$

为等距。对有限维态 $\rho$，

$$
p_o=\operatorname{tr}(M_o\rho M_o^\dagger),\qquad
\rho_o=\frac{M_o\rho M_o^\dagger}{p_o}\quad(p_o>0)
\tag{7.2}
$$

给记录权重与条件后继；
未选择结果时 $\rho\mapsto\sum_oM_o\rho M_o^\dagger$ 完全正且保迹。

证明。
将式 (7.1) 乘以任意 $\overline c_i c_j$ 并求和，得到
$Q_n(v)=\sum_oQ_{n+1}(r_ov)$。
非负性使每个零关系经每支接续仍为零，
所以接续能下降到商空间，且每支范数不增。
极化给 $\sum_oM_o^\dagger M_o=I$，
正交记录内积使 $V^\dagger V=I$。
对任意辅助空间，每项
$(I\otimes M_o)X(I\otimes M_o^\dagger)$ 都保正；
求和为完全正，迹循环和归一恒等式给保迹。
取分支迹并在正迹时归一化，得到式 (7.2)。
∎

这个定理把“预测行为成为观察者自己的增长”落实为一个等距：
新记录不是外部魔法添加，而是总状态接续的一部分。
条件态的归一化含除法，因而对初态一般非线性；
未选择结果的仪器仍然线性。
它不证明主观意识创造结果，也没有仅靠静态关系解释经验中为何呈现唯一记录。
它确定的是所声明记录接口的统计与后继。

同一结果不必只有一个 Kraus 算子。一般仪器的实际分支为

$$
\mathcal J_o(\rho)=\sum_\mu K_{o\mu}\rho K_{o\mu}^\dagger,\qquad
\sum_{o,\mu}K_{o\mu}^\dagger K_{o\mu}=I.
$$

复用 [static] §§6–7 与 [wave] §4 的仪器表示，可以在数学扩张中细化 $(o,\mu)$，令 $\widetilde V\psi=\sum_{o,\mu}K_{o\mu}\psi\otimes|o,\mu\rangle$，同样有 $\widetilde V^\dagger\widetilde V=I$。迹掉不可读的 $\mu$ 恰得原分支；$\mu$ 的数学存在不授予读取权限。正迹时的条件态为 $\mathcal J_o(\rho)/\operatorname{tr}\mathcal J_o(\rho)$，零权分支只有未归一化零态。定理 7.2 的每结果一个 $M_o$ 是保留了纯后继或足够环境的特殊表示，不能将一般混合分支误写成一个系统算子。

在单 Kraus 表示中，记录化后的相干整体为

$$
V\rho V^\dagger=\sum_{o,o'}M_o\rho M_{o'}^\dagger\otimes|o\rangle\langle o'|.
$$

普通选择记录或忽略记录只用对角块；若未来允许相干访问记录，非对角块仍属于共同状态。式 (7.1) 保证总等距所需的同结果交叉守恒，不额外固定不同结果块的全部实现相位。每支改为 $e^{i\gamma_o}M_o$ 保持普通仪器，却改变跨记录块；相干擦除实验必须指定实际的 $V$ 及参考。这与 [quantum] §6、[bundle] §8 的完整未来接口一致。

**定理 7.3（何时可以只加概率）。**
对两个末端预测向量 $u,v$，以下等价：

$$
\left\lVert u+e^{\mathrm i\phi}v\right\rVert^2=\left\lVert u\right\rVert^2+\left\lVert v\right\rVert^2
\quad\text{对所有 }\phi;
\qquad \langle u,v\rangle=0.
$$

只在一个相位上满足概率加法，不足以推出正交。

证明。
交叉项为 $2\Re(e^{\mathrm i\phi}\langle u,v\rangle)$。
它对全部相位消失当且仅当复内积为零。
若内积纯虚，则在 $\phi=0$ 可消失，而在其他相位不必消失。
∎

所以普通概率加法可以看成一个条件结论：
不同预测保留了互相正交、不能在当前接口重合的记录。
若记录后来能够相干重合，必须回到包含它们的振幅描述。
纯粹删掉档案中的路径名称不会完成这种物理重合。

**定理 7.4（可见波与路径记录的精确互补）。**
取等振幅双路径纯态

$$
|\Psi\rangle=
\frac{|L\rangle|m_L\rangle+e^{\mathrm i\phi}|R\rangle|m_R\rangle}{\sqrt2},
\qquad \left\lVert m_L\right\rVert=\left\lVert m_R\right\rVert=1,\quad
\kappa=\langle m_L,m_R\rangle.
$$

只读路径的 $|\pm\rangle=(|L\rangle\pm|R\rangle)/\sqrt2$，有

$$
p_\pm=\frac{1\pm\Re(e^{\mathrm i\phi}\kappa)}2.
$$

其干涉可见度为 $\mathcal V=|\kappa|$；
两纯记录的半迹距离为
$\mathcal D=\sqrt{1-|\kappa|^2}$，故
$\mathcal V^2+\mathcal D^2=1$。

证明。
投影到 $|+\rangle$ 后记录向量为
$(m_L+e^{\mathrm i\phi}m_R)/2$，范数平方给第一式。
相位扫描的极大、极小为 $(1\pm|\kappa|)/2$，
其差除以和给可见度。
在两记录张成的至多二维空间中，
两秩一投影之差迹为零，非零特征值为
$\pm\sqrt{1-|\kappa|^2}$；取半迹范数即得。
∎

这里的量化是等先验、等振幅、纯记录模型的准确结果，
也是项目已经采用的记录重叠机制 [wave]。
一般双路径不等式的经典原始论文为 Englert [englert]。
观察者一旦把路径差异写入可保持的正交记录，局部波纹消失；
整体关系并未因此变为一组互不相关的局部概率。

### 内生观察者不能只保留自己的边缘

**命题 7.5（相同局部知识仍可有不同共同未来）。**
存在两态，使系统和观察者记忆各自的边缘态都完全相同，
但同一个后续共同操作给确定且相反的结果。

证明。
在两个二模系统上取
$|\Phi_\pm\rangle=(|00\rangle\pm|11\rangle)/\sqrt2$。
两侧边缘均为 $I_2/2$。
这里共同空间明确为 $\mathbb C^2\otimes\mathbb C^2$。供应的门为 $\mathrm{CNOT}|a,b\rangle=|a,b\mathbin{\oplus}a\rangle$，以及第一位的 $H_2=\frac1{\sqrt2}\left(\begin{smallmatrix}1&1\\1&-1\end{smallmatrix}\right)$。对两态都先作用 CNOT，再作用 $H_2\otimes I$，
分别得到 $|00\rangle$ 与 $|10\rangle$。
读第一位即可确定区分。
差异存在于共同相干，所有单侧边缘都没有保留它。
∎

这个例子只使用明确供应的两个逻辑位和共同门，
没有宣称任意两个邻接 AURIC 原子都自动有独立张量编码。
在具体系统中，独立复合、接缝约束与实际控制仍须分别检查。
它说明观察者位置的不确定可以与系统存在关系性关联，
但“我不知道自己是什么”本身不等于已经证明纠缠或隧穿。

## 8. 没有外部流动的静态图如何编码波

### 传播约束与历史态

**定义 8.1（有限钟与静态传播约束）。**
给整数 $N\ge0$ 及同一非零有限维 $H$ 上的酉 $U_0,\ldots,U_{N-1}$，
令 $V_0=I,\ V_n=U_{n-1}\cdots U_0$，
并取钟空间 $\mathbb C^{N+1}$。
对 $\Psi=\sum_{n=0}^N|n\rangle\otimes\psi_n$ 定义

$$
L_n\Psi=\psi_{n+1}-U_n\psi_n,\qquad
H_{\rm hist}=\sum_{n=0}^{N-1}L_n^\dagger L_n.
\tag{8.1}
$$

这里 $H_{\rm hist}$ 是传播一致性的非负约束算子，
不预先把它认作系统的物理能量生成元。

**定理 8.2（静态零空间恰好是递归波的历史）。**
定义

$$
W\psi=\frac1{\sqrt{N+1}}\sum_{n=0}^N|n\rangle\otimes V_n\psi.
\tag{8.2}
$$

则 $W^\dagger W=I$，
$\ker H_{\rm hist}=\operatorname{ran}W$。
在 $W\rho W^\dagger$ 上读取钟 $n$ 的概率为 $1/(N+1)$，
对应系统条件态为 $V_n\rho V_n^\dagger$。

证明。
因为钟标签正交、$V_n$ 酉，
$W^\dagger W=(N+1)^{-1}\sum_nV_n^\dagger V_n=I$。
$\langle\Psi,H_{\rm hist}\Psi\rangle=\sum_n\left\lVert \psi_{n+1}-U_n\psi_n\right\rVert^2$，
所以零空间恰为满足 $\psi_{n+1}=U_n\psi_n$ 的序列；
递推得 $\psi_n=V_n\psi_0$，即式 (8.2) 的像。
取第 $n$ 个钟对角块得到
$V_n\rho V_n^\dagger/(N+1)$，取迹并归一化即得条件态。
∎

该证明消费 [static] §7 与 [wave] §3 的 Feynman–Kitaev 历史等距；本处同时明确其整个核／像等式。这是该历史表示的有限形式，
项目《波粒整体》已给相同传播接口；
原始论文例见 Aharonov 等 [wave]、[historypaper]。
静态整体不需要在外部再播放一遍，
内部钟条件之间仍保留原来的有序门积。
因此“没有额外外部时间”与“所有操作没有先后差别”是不同命题。约束谱隙不是受测系统的能隙，也没有给出实际制备零空间的能量、时间或算法成本。

**定理 8.3（历史约束的谱隙随长度缩小）。**
若 $H\ne\{0\}$ 且 $N\ge1$，式 (8.1) 的非零最小本征值为

$$
\gamma_N=2\left(1-\cos\frac{\pi}{N+1}\right).
\tag{8.3}
$$

任意单位向量 $\Psi$ 满足

$$
\left\lVert (I-P_{\rm hist})\Psi\right\rVert^2
\le\frac{\langle\Psi,H_{\rm hist}\Psi\rangle}{\gamma_N},
\tag{8.4}
$$

其中 $P_{\rm hist}$ 是精确历史零空间投影。

证明。
以酉
$\mathcal V=\sum_n|n\rangle\langle n|\otimes V_n$
作共同坐标变换，$\psi_n=V_n\xi_n$，
每项误差变为 $\left\lVert \xi_{n+1}-\xi_n\right\rVert^2$。
故 $H_{\rm hist}$ 酉等价于长度 $N+1$ 的路径图 Laplacian 与 $I_H$ 的张量积。
令 $q=N+1$。其第 $k$ 个钟本征向量可取
$\xi_n^{(k)}=\cos[\pi k(n+1/2)/(N+1)]$，
$k=0,\ldots,N$。
代入内部二阶差分及两端的一阶边界式，
得到本征值 $2[1-\cos(\pi k/(N+1))]$。
最小非零者为式 (8.3)。
谱分解给
$H_{\rm hist}\ge\gamma_N(I-P_{\rm hist})$，
在 $\Psi$ 上取二次型便得式 (8.4)。
∎

当 $N=0$ 时 $H_{\rm hist}=0$，整个载体是历史核，没有非零最小本征值；不能用式 (8.3) 作除数。当 $H=\{0\}$ 时也没有非零谱，且不存在单位历史向量。

这个误差界也提示“任何镜像尺度都达到相同终点”需要额外控制：
$\gamma_N$ 约为 $\pi^2/(N+1)^2$，
更长历史中相同的绝对约束能量不保证相同的整体历史误差。
如果要论证分辨率自适应且跨尺度稳定，
必须给出误差如何随长度缩小的定量规律。
本定理也没有证明求得约束零空间的计算成本很低。

### 路径求和是切面相容，不是每条路已经发生

**定理 8.4（共同切面的振幅拼接）。**
对已供应的线性接续 $U_n$，任意初末模式有

$$
\begin{aligned}
\langle x_N|V_N|x_0\rangle
&=\sum_{x_1,\ldots,x_{N-1}}
\prod_{n=0}^{N-1}\langle x_{n+1}|U_n|x_n\rangle,\\
A_{N:0}(x_N,x_0)
&=\sum_{x_k}A_{N:k}(x_N,x_k)A_{k:0}(x_k,x_0).
\end{aligned}
\tag{8.5}
$$

不同合法切面上的求和给同一最终振幅。

证明。
在有序乘积中插入模式完备关系
$I=\sum_x|x\rangle\langle x|$，逐项展开即得第一式。
按第 $k$ 个中间标签分组，利用矩阵乘法结合律得到第二式。
∎

这种“在不同层从哪里开始都能拼回同一预测”，
是用户尺度相融直觉中可以直接定型的一部分。
它只保证同一有限操作的不同计算分解一致，
不保证每次粗粒化后都能只用较少变量完成后续预测。
若丢掉了以后仍参与干涉的变量，拼接就会改变。
Feynman 的振幅规则提供这一串并联图景的标准来源 [feynman3]。

**命题 8.5（没有操作次序限制的逻辑相容仍不够）。**
一个静态关系模型可以同时容纳 $UV$ 和 $VU$，
而它们未必是同一通道。

证明。
取两维酉 $U=Z=\operatorname{diag}(1,-1)$、$V=H_2=\frac1{\sqrt2}\left(\begin{smallmatrix}1&1\\1&-1\end{smallmatrix}\right)$。
作用于 $|0\rangle$，
$UV|0\rangle=|-\rangle$，
$VU|0\rangle=|+\rangle$，二者可由同一个 $|+\rangle\langle +|$ 效果区分。
把两种有序路径同时画在静态图中，不会使其矩阵积自动相等。
∎

只有当合同明确要求某个交换菱形的两条路径等价，
相应算子才必须满足那个菱形的交换关系。
这与项目静态相容理论的路径运输条件一致 [static]。

## 9. 由谱恢复波：项目中的相位恢复提供了什么启发

项目《金字塔基础公式》§16 对其指定的轮筛信号，
已经明确区分功率谱、三点相关和绝对原点 [foundation]。
其数学接口在这里的作用是：
单点强度遗漏的关系，可以通过共同比较约束回来；
但这些关系必须真的被提供，而不能由“有一个谱”代替。

**定义 9.1（循环信号的功率谱与关系双谱）。**
给正整数 $N$。对 $f:\mathbb Z/N\mathbb Z\to\mathbb C$，固定 Fourier 约定

$$
F_k=\sum_{x=0}^{N-1}f(x)e^{-2\pi\mathrm i kx/N}.
$$

功率谱为 $|F_k|^2$。
给带共轭的三点相关和双谱

$$
C_f^{(3)}(s,t)=\sum_x\overline{f(x)}f(x+s)f(x+t),
\qquad
B_f(k,\ell)=F_kF_\ell\overline{F_{k+\ell}}.
\tag{9.1}
$$

对 $(s,t)$ 作 Fourier 变换，前者恰变为后者。

**命题 9.2（功率谱可以完全相同而波不同）。**
在 $N=2$ 时，取 $F=(1,1)$、$G=(1,\mathrm i)$。
两者功率谱相同，其反变换分别为

$$
f=(1,0),\qquad
g=\left(\frac{1+\mathrm i}{2},\frac{1-\mathrm i}{2}\right).
$$

它们不互为循环平移，且在原坐标上强度不同。

证明。
两个频域向量的每项模均为一；
直接逆变换得到所列结果。
任何平移后的 $f$ 都只有一个非零分量，而 $g$ 有两个。
∎

**定理 9.3（完整非零双谱锁定波到一个原点平移）。**
设 $F_k\ne0$ 对所有 $k$ 成立。
若任意复信号 $g$ 满足 $B_g=B_f$，则存在唯一 $t\in\mathbb Z/N\mathbb Z$ 使
$g(x)=f(x-t)$。
若再给定有原点参考的第一 Fourier 系数 $G_1=F_1$，
则 $g=f$。

证明。使用 [foundation] 定理 16.2 的完整复共轭字符论证，取其循环长度 $W=N$，其 $F_k,J_k$ 分别对应这里的 $F_k,G_k$。本定理直接假设全频率非零，故不需重复轮筛的算术非消失证明。
记 $G_k$ 为 $g$ 的 Fourier 系数。
由
$B_f(0,0)=|F_0|^2F_0$，
以及 $z\mapsto|z|^2z$ 的单射性，得 $G_0=F_0\ne0$。
再由 $B_f(k,0)=F_0|F_k|^2$ 得
$|G_k|=|F_k|>0$。
置 $r_k=G_k/F_k$，则
$|r_k|=1$ 且
$r_kr_\ell\overline{r_{k+\ell}}=1$，
所以 $r_{k+\ell}=r_kr_\ell$。
因此 $r_k=r_1^k$、$r_1^N=1$，
存在唯一 $t$ 使 $r_k=e^{-2\pi\mathrm i kt/N}$。
Fourier 反演给循环平移。
若 $G_1=F_1\ne0$，则 $r_1=1$，所以 $t=0$。
∎

实函数和集合的三点相关背景见 Keleti–Kolountzakis [keleti]；[foundation] 还为其平方自由轮筛验证了所需非消失前提。这一 Fourier 恢复的对象是循环信号，不等同于五模式量子态层析。

若某些 Fourier 系数为零，比值递归可能断开，
结论需按实际频率支撑另作分析。
即使都非零，也没有保证逆问题条件数统一有界：
递推式

$$
F_{k+1}=\overline{\frac{B_f(k,1)}{F_kF_1}}
$$

会除以可能很小的数。
“唯一可恢复”不自动等于“有限分辨率下稳定可恢复”。

这里的三点相关是同一个信号的高阶统计结构，
不是量子三路径的独立三阶干涉。
后者在二次振幅模型中仍有

$$
\begin{aligned}
I_3={}&\left\lVert a+b+c\right\rVert^2-\left\lVert a+b\right\rVert^2-\left\lVert a+c\right\rVert^2-\left\lVert b+c\right\rVert^2\\
&+\left\lVert a\right\rVert^2+\left\lVert b\right\rVert^2+\left\lVert c\right\rVert^2=0,
\end{aligned}
$$

因为展开后每个单项和两两交叉项恰好抵消。
这个标准二次结构与量子测度层次相关 [sorkin]。
相位可由三点关系恢复，与 $I_3=0$ 并不矛盾；
两个“三阶”量属于不同定义。

## 10. 连续空间的波如何成为离散关系的有效描述

### 一个可证明的连续极限

有限模式上的振幅波不需要连续空间。
若要进一步得到熟悉的 Schrödinger 空间方程，
必须给出一族空间图、局部耦合和尺度标定。
晶格振幅与连续波的联系可参见 Feynman 的晶格传播论述
[feynman13]；以下给一个带明确误差的条件版本。

**定义 10.1（独立供应的空间图族）。**
取整数 $d\ge1$、$N\ge1$ 和 $L>0$，使用 $d$ 维周期空间 $\mathbb T_L^d$，
格距 $a=L/N$，使用 $N^d$ 个格点及加权范数

$$
\left\lVert u\right\rVert_a^2=a^d\sum_x|u(x)|^2.
$$

定义

$$
\Delta_a u(x)=\sum_{j=1}^d
 \frac{u(x+ae_j)-2u(x)+u(x-ae_j)}{a^2},
\qquad
H_a=-\frac{\hbar^2}{2m}\Delta_a+V(x),
\tag{10.1}
$$

其中 $\hbar>0,\ m>0$，$V$ 是实值周期势。
这是另给的最近邻、$a^{-2}$ 标度图族，不是单个五模式图的同义改写。

**定理 10.2（局域图演化的有限时间连续近似）。**
设 $\psi(t,x)$ 是 $0\le t\le T$ 上的光滑周期解，

$$
\mathrm i\hbar\partial_t\psi
=\left[-\frac{\hbar^2}{2m}\Delta+V(x)\right]\psi,
$$

并令
$M_j=\sup_{t,x}|\partial_j^4\psi(t,x)|<\infty$。
以 $H$ 表示该连续方程右侧的空间算子。
采样算子记为 $S_a$。
令 $u_a$ 解格点方程
$\mathrm i\hbar\dot u_a=H_au_a$，
$u_a(0)=S_a\psi(0)$。
则

$$
\sup_{0\le t\le T}\left\lVert u_a(t)-S_a\psi(t)\right\rVert_a
\le\frac{\hbar T\,a^2L^{d/2}}{24m}\sum_{j=1}^d M_j.
\tag{10.2}
$$

证明。
对每个坐标，四阶 Taylor 余项给

$$
\left|\frac{f(x+ae_j)-2f(x)+f(x-ae_j)}{a^2}
           -\partial_j^2f(x)\right|
\le\frac{a^2}{12}\sup|\partial_j^4f|.
$$

因此残差
$r_a=H_aS_a\psi-S_aH\psi$ 满足

$$
\left\lVert r_a(t)\right\rVert_\infty
\le\frac{\hbar^2a^2}{24m}\sum_jM_j.
$$

周期差分自伴，实势也自伴，故格点传播酉且保持 $\left\lVert \cdot\right\rVert_a$。
误差 $e=u_a-S_a\psi$ 满足
$\mathrm i\hbar\dot e=H_ae+r_a$、$e(0)=0$。
变常数公式给
$\left\lVert e(t)\right\rVert_a\le\hbar^{-1}\int_0^t\left\lVert r_a(s)\right\rVert_a\,ds$。
格点总体积为 $L^d$，故
$\left\lVert r_a\right\rVert_a\le L^{d/2}\left\lVert r_a\right\rVert_\infty$；
代入即得式 (10.2)。
∎

这是一个充分条件下的近似定理：
在平滑低频、有限时间范围，连续方程可以是离散图的高精度描述。
它没有证明本体上连续一定不存在，也没有证明任意递归图都具有这个极限。
空间维度 $d$、欧氏邻接、势、耦合标度、质量和时钟是明确的新增数据。
尤其三条几何正交读出并不自动推出整个真实空间就是这样的晶格极限。

**命题 10.3（晶格相位色散的低频极限）。**
在 $V=V_0$ 常数时，对周期许可的
$k\in(2\pi/L)\mathbb Z^d$，格点平面模 $e^{\mathrm i k\cdot x}$ 的能量为

$$
E_a(k)=V_0+\frac{2\hbar^2}{ma^2}
                 \sum_{j=1}^d\sin^2\frac{k_ja}{2}.
\tag{10.3}
$$

当各 $|k_j a|\ll1$，其主项为
$V_0+\hbar^2|k|^2/(2m)$。
格点频率按每个方向的 $2\pi/a$ 混叠；
低频展开使用选定的低频代表元。

证明。
将平面模代入二阶差分，
每个方向贡献 $(2\cos k_ja-2)/a^2=-4\sin^2(k_ja/2)/a^2$。
乘动能系数得到式 (10.3)，再展开正弦平方。
∎

同样的空间 Laplacian 也可生成经典扩散方程，
其 Fourier 模按实指数衰减；
量子方程中它生成相位旋转。
图的邻接和递归本身没有决定选择哪一种生成规律。
另外，Schrödinger 方程一阶时间、二阶空间的形式
不同于经典无色散波方程；
把所有“波”写成一个词不能替代具体色散关系。

### 共轭读出、不确定性与有限原子的边界

**定理 10.4（预测读出的 Robertson 界）。**
对有限维归一化 $\psi$ 和 Hermitian $A,B$，

$$
\langle A\rangle_\psi=\langle\psi,A\psi\rangle,\qquad
\Delta_\psi A=\left\lVert (A-\langle A\rangle_\psi I)\psi\right\rVert,
$$

并对 $B$ 同样定义，则

$$
\Delta_\psi A\,\Delta_\psi B
\ge\frac12|\langle\psi,[A,B]\psi\rangle|.
\tag{10.4}
$$

证明。
令 $a=(A-\langle A\rangle)\psi$、
$b=(B-\langle B\rangle)\psi$。
Cauchy--Schwarz 给
$\Delta A\,\Delta B\ge|\langle a,b\rangle|
\ge|\Im\langle a,b\rangle|$。
而 $2\mathrm i\Im\langle a,b\rangle=\langle\psi,[A,B]\psi\rangle$。
∎

这里的下界来自模型内两种读出的非交换作用。
这个不等式本身并不足以排除带额外结构的经典模拟：
经典波的内积表示也能满足同型的 Cauchy--Schwarz 界。
量子模型还可以同时包含普通统计不确定性。
式 (10.4) 只有在实际读出 $A,B$ 以及状态已给定后才有物理内容。

**定理 10.5（有限 Fourier 读出的支撑不确定性）。**
对非零 $\psi\in\mathbb C^d$ 和归一化离散 Fourier 变换

$$
(\mathcal F\psi)_k=\frac1{\sqrt d}
           \sum_{x=0}^{d-1}e^{-2\pi\mathrm i kx/d}\psi_x,
$$

令 $s=|\operatorname{supp}\psi|$、
$r=|\operatorname{supp}\mathcal F\psi|$，则 $sr\ge d$。

证明。
对每个 $k$，
$|(\mathcal F\psi)_k|\le\sqrt{s/d}\,\left\lVert \psi\right\rVert$，
由 Cauchy--Schwarz 得到。
平方后在 $r$ 个非零位置求和，并用 Fourier 酉性：
$\left\lVert \psi\right\rVert^2\le rs\,\left\lVert \psi\right\rVert^2/d$。
因 $\psi\ne0$，约去范数即得。
∎

五模式可以在额外供应 Fourier 比较时取 $d=5$，
但该读出不由原来的固定等待与完整模式读取自动授权。
另在 $L^2(\mathbb R^d)$ 的公共不变 Schwartz 域 $\mathscr S(\mathbb R^d)$ 上，
位置乘法 $X_j$ 和平移生成元
$P_j=-\mathrm i\hbar\partial_j$ 满足
$[X_j,P_k]=\mathrm i\hbar\delta_{jk}I$，
这是对乘积求导直接得到的条件关系。
这一步已经换到非紧空间及其指定算子域，
不把周期环面上有边界问题的位置坐标当作同一个算子。

**命题 10.6（单个有限原子不能精确满足正则交换关系）。**
若 $d\ge1$ 是整数，$X,P$ 是有限 $d\times d$ 矩阵，$\hbar>0$，
则不可能有 $[X,P]=\mathrm i\hbar I$。

证明。
有限矩阵迹循环给 $\operatorname{tr}[X,P]=0$，
而 $\operatorname{tr}(\mathrm i\hbar I)=\mathrm i\hbar d\ne0$。
∎

所以从有限原子到连续量子位置与动量，需要扩大载体、
选定尺度极限及算子定义域；不能在五维内部偷偷完成这一跨越。
类似地，本稿的环相位本身不推出相对论、三维空间的唯一性、
电磁场动力学或某一类基本粒子。

## 11. 一套可审查的“预测波”起源体系

### 五项操作条件及其定理后果

**定义 11.1（预测波条件体系）。**
以下条件均指实际声明的共同输入、输出和参考类型。

1.  **P1：两分量校准。**
局部标量预测满足定义 3.1 的实二维旋转、正交可加、
全域双线性串联和权重乘性。

2.  **P2：整体参考相融。**
不同预测的候选交叉关系为 Hermitian 核；
对其每个有限子矩阵，允许定理 2.10 的固定相位种子独立复合，
并要求全部指定联合相干测试非负。

3.  **P3：递归保关系。**
同一动作的有结果接续满足式 (7.1)；
无结果损失的平稳接续满足式 (R)。
如果宣称当前载体内可逆，则供应满射性或有限维闭合。

4.  **P4：结果标定。**
正交记录是声明的互斥完备结果，
其归一化二次权重对应实际读出概率。
混合制备按其真实混合系数合并预测。

5.  **P5：观察边界完整。**
未来还可能作用的记忆、共同来源、路径参考、记录和控制，
纳入共同的预测载体。
只有已经供应独立复合合同时，才用张量积表示不同系统。

可微时钟、空间晶格族及任意完整操作菜单不是上述五条的自动内容，
须在使用相应结论时另行声明。

**定理 11.2（预测波的条件重建）。**
在定义 11.1 下：

1.  局部标量预测的算术是复数算术，强度为模平方；

1.  共同预测关系有最小复 Hilbert 表示；

1.  无损平稳递归在有限闭合或满射条件下为酉，
      有限维时振幅为有限谱相位的重组；

1.  带结果的递归是记录等距，其记录分支为量子仪器，
      在有限维统计表示中给出 Born 型权重、归一化条件后继
      及完全正保迹的总更新；

1.  共同末端的不同路径先在振幅层重合，
      产生两两干涉；保留正交路径记录时相应概率相加；

1.  在有限维载体上额外供应可微时钟时得到 Schrödinger 生成元；
      额外供应第十节空间标度族时得到该连续极限误差界。

这些是该操作域中的表示与预测定理，
不自动证明所有数学态、效果和控制都已物理可执行。

证明。
第一项由定理 3.2、3.3。
第二项先对每个有限核用定理 2.10 得强正，
再用定理 2.2 作共同商与完成。
第三项由定理 4.2 及有限维谱展开。
第四项由定理 7.2；
纯制备在结果端口的权重由定理 3.5，
混合制备按凸线性得到密度算子迹表达。
第五项由定理 8.4、
7.3 及记录内积计算。
最后一项分别为定理 4.9 和 10.2。
∎

这里较深的推进是：可以把某些量子结构放到*推理在共同未来中不能互相矛盾*
这一要求之下。
例如强正性不再只是任意矩阵限制，而可被一个相位参考的反复复合检测；
酉性也不是单独给定的矩阵形状，而是所有交叉关系都能无损接续的结果。
但 P1 的二维校准、P2 的联合相干测试以及 P4 的概率解释，
仍是有内容且可质疑、可检验的操作条件。
本稿没有证明这些条件相互独立或是逻辑上的最小公理。

| 量子概念 | 本文中的理由 | 不能省略的条件 |
| --- | --- | --- |
| 复振幅 | 正交平方权重与串联乘性迫使 $u^2=-1$ | 两实维校准和全域双线性串联 |
| Hilbert 空间 | 全部有限共同测试要求强正核，商去零关系 | 相干参考与联合测试确实可用 |
| 叠加 | 备选过程在同一接口作线性重组 | 物理相干重组，不只是形式记号 |
| Born 形式 | 旋转、正交可加、非负与归一化给平方权重 | 权重和记录概率的标定 |
| 酉演化 | 无损递归保留全部交叉内积 | 满射性或有限维闭合 |
| 测量与后态 | 等距把结果写入正交记录，再条件化 | 完整仪器，而非只有一个效果 |
| 干涉／暗态 | 路径振幅合并的交叉项相长或相消 | 共同初末端与相位参考 |
| 不确定性 | 同一正核中不同读出的不对易作用 | 实际读出及其算子已指定 |
| 连续波方程 | 局部格点相位传播在平滑尺度下近似 | 空间、耦合标度、时钟与正则性 |

### 另外两条基础原则如何跟随这个结构

**定理 11.3（相干预测不允许无条件复制任意未知态）。**
若一个共同物理等距对两纯输入 $\psi,\phi$ 都产生两份精确副本，
允许另有输入相关环境态，则两输入的重叠模只能为零或一。

证明。
初始机器与辅助态相同。精确纯副本使最终整体纯态可写为

$$
\psi\otimes\psi\otimes e_\psi,\qquad
\phi\otimes\phi\otimes e_\phi,
$$

环境态均归一化。
等距保持内积，故
$\langle\psi,\phi\rangle
=\langle\psi,\phi\rangle^2\langle e_\psi,e_\phi\rangle$。
取模并用环境重叠不超过一，得到 $r\le r^2$。
$0\le r\le1$，故 $r=0$ 或 $r=1$。
∎

因此观察者递归增加记录，并不意味着它能把任意未读相干内容无损复制任意多次。
定理 2.10 复制的是一个*已知且可重新制备的参考*，
不是对任意未知量子态使用克隆器，两者没有冲突。

**定理 11.4（局部完整记录不能改变另一侧边缘）。**
若已供应独立张量复合 $H_A\otimes H_B$，
在 $A$ 上施加满足 $\sum_oM_o^\dagger M_o=I_A$ 的未选择结果仪器，
则 $B$ 的所有局部效果概率保持。

证明。
对任意 $B$ 的效果 $E$，

$$
\begin{aligned}
\sum_o\operatorname{tr}[(M_o\otimes I)\rho(M_o^\dagger\otimes I)(I\otimes E)]
&=\operatorname{tr}\!\left[\rho\left(\sum_oM_o^\dagger M_o\otimes E\right)\right]\\
&=\operatorname{tr}[\rho(I\otimes E)].
\end{aligned}
$$

局部效果分离边缘态，故边缘态相同。
∎

已选取某个结果的条件态可以改变，
但对方没有该记录就只能使用未选择结果的平均。
这个无信号结论以张量局域性和完整分支守恒为条件，
不是仅靠五个模式名称决定真实空间的因果结构。

### 哪些强主张尚未成为定理

**命题 11.5（同一合法递归图容许无穷多种概率规律）。**
五模式的合法翻转支撑与观察者内部记录，
不唯一决定任何一套转移概率，更不唯一决定复振幅。

证明。
在图中每个有多个邻点的顶点，
任取一组严格正、和为一的邻边权重作转移概率；
叶节点的唯一转移取概率一。
这些选择构成无穷多个经典 Markov 规则，合法支撑相同。
将当前状态、执行程序和迄今记录并入配置，
每种规则都有内部观察者和按步展开的静态 DAG。
它们的概率不同，却均满足所述组合和记录结构。
∎

因此“一切概率实际上都是逻辑递归”可以作为一种研究解释，
但若要成为唯一数值定理，就必须指定哪种逻辑、哪种复合、哪个核与哪种标定。
单说“不是乱猜”还未给出这些量词。
同样，存在相容波表示没有决定量子解释中的所有本体论问题。

原生实现仍需满足以下四个桥梁：

1.  AURIC 的观察操作能否实际构成 P1 的二维串并联接口，
      而不仅是在图旁附加一个欧氏平面；

1.  是否原生支持固定四分之一相位种子，以及定理
      2.10 或推论 2.11 所需的共同相干测试；

1.  递归接续是否对全部相干交叉关系守恒，
      或者只是对若干人口统计守恒；

1.  多个原子的实际接缝能否实现所声明的独立复合，
      并保留后续任务仍能读取的观察者与环境关系。

这些问题都有明确对象与可失败条件。
只有逐项完成，才可以把“这个原子能够承载量子规则”
推进到“这个原生观察协议要求这些量子规则”。
五模式的价值在于它为这些检验提供了小而具体的关系系统：
三位置排斥、端点共同占据、四环干涉与隐藏叶记忆同时在场。

## 12. P1–P5 的一个共同相容实现

**定义 12.1（同一复表示与明确的资源族）。** 标量取 $A=\mathbb C$，作为实空间用内积 $\operatorname{Re}(\overline zw)$、单位 $1$、复结构 $Jz=iz$、强度 $W(z)=|z|^2$ 和普通复乘法。系统固定为 $H_S=\mathbb C^5$，基为 $(0,1,2,3,13)$，等待矩阵就是式 (5.1) 的 $K$，读取就是完整仪器 $P_s(\cdot)P_s$。为每个有限参考深度 $m$、有限记录长度及有限钟长度，另供应相应的有限维联合空间。每个有限描述清单的系数标签也可用一个单独的 $\mathbb C^k$ 参考寄存器，或嵌入足够大的二进制参考载体；它不是五模式系统的另一组结果基。不同系统的独立并置使用复张量积。

共同相干描述域在每个这样的载体 $H$ 上取 $\mathscr P_H=H$，包括未归一化向量，核为

$$
\mathcal K_H(p,q)=p^\dagger q.
$$

这里“忠实”指 $\mathcal K_H(p,p)=0$ 当且仅当 $p=0$；不声称任意有线性依赖的描述清单都有严格正定 Gram 矩阵。物理制备状态为 $\rho\ge0,\operatorname{tr}\rho=1$，效果为明确供应的 $0\le F\le I$，概率为 $\operatorname{tr}(\rho F)$。混合制备按实际概率作凸组合。为验证 P2，扩充菜单明确供应种子 $z=(1,i)/\sqrt2$、任意有限幂参考态 $R^{\otimes m}$ 以及式 (2.2) 对应的全部 $F_E$ 相干投影；每个投影的补效果 $I-F_E$ 同时是一个完备二结果测量。这个扩充菜单包含原菜单，却不把这些资源归给原菜单。

**定理 12.2（五条件可在一个实际数学模型中同时满足）。** 定义 12.1 的同一表示满足 P1–P5，并同时容纳式 (5.1) 的五模式等待、完整分支、记录、参考与任意有限长度的静态历史。它给出五条件的非空共同模型。

证明。P1 的旋转是乘 $e^{i\alpha}$，保 $|z|^2$；若 $\operatorname{Re}(\overline zw)=0$，则 $|z+w|^2=|z|^2+|w|^2$。乘法在实标量上完全双线性、双侧有单位，并有 $|zw|^2=|z|^2|w|^2$，所以满足定义 3.1 的全部条件。所有载体上的 $J_Hp=ip$ 都使用这同一个标量 $i$；在复张量积中 $(ip)\otimes q=p\otimes(iq)$，故没有为不同端口另选互不相容的复单位。

对 P2，任意有限描述 $p_j$ 的 Gram 二次型是

$$
\sum_{i,j}\overline c_i c_j\mathcal K_H(p_i,p_j)
=\Bigl\|\sum_jc_jp_j\Bigr\|^2\ge0.
$$

同一表示中的密度矩阵和这些 Gram 矩阵也相容：若 $D\ge0$ 是任意有限矩阵，取 $v_i=D^{1/2}e_i$，则 $D_{ij}=\langle v_i,v_j\rangle$。这一步使用该清单自己的有限系数载体。特别对种子投影 $R=zz^\dagger$，取 $v_\alpha=R^{1/2}e_\alpha$，得到的核矩阵恰为 $R$，不是改变了共轭约定的另一个矩阵。参考的复张量积在这些 Gram 中正好给 $D\otimes R^{\otimes m}$。因此历史事件量为

$$
\mu_{D\otimes R^{\otimes m}}(E)
=\Bigl\|\sum_{(i,a)\in E}v_i\otimes v_a\Bigr\|^2\ge0.
$$

当使用普通状态解释时，同一个矩阵及同一个参考给

$$
\operatorname{tr}[(D\otimes R^{\otimes m})F_E]
=\frac{\mathbf1_E^\dagger(D\otimes R^{\otimes m})\mathbf1_E}{|E|},
\qquad
|u_E\rangle=\frac1{\sqrt{|E|}}\sum_{(i,a)\in E}|i,a\rangle.
$$

若 $\operatorname{tr}D=1$，这个读数及其补读数是合法概率；任意非零 Gram 矩阵可先除以其迹，再把已知的正尺度单独保留。零 Gram 只表示零描述，不强行为它制备迹一状态。若采用历史总和归一化，则要求 $\|\sum_iv_i\|^2=1$，而不是强加 $\sum_i\|v_i\|^2=1$。这两个归一化在种子上恰好同时成立，在一般 $D$ 上分别声明。$\mu(E)$ 本身没有被冒充为一个共同正交测量中每个事件的概率。普通对角粗粒化 $\sum_{(i,a)\in E}|i,a\rangle\langle i,a|$ 的迹只加对角项，仍是不同操作。

对 P3，取任何明确供应的有限 Kraus 族 $M_o:H\to H'$，满足 $\sum_oM_o^\dagger M_o=I$，令 $r_op=M_op$。于是同一核满足

$$
\sum_o\mathcal K_{H'}(r_op,r_oq)
=p^\dagger\Bigl(\sum_oM_o^\dagger M_o\Bigr)q
=\mathcal K_H(p,q).
$$

原生完整读就是 $M_s=P_s$；平稳接续就是 $r p=U(\tau)p$。它们分别给真实的分支概率和实际酉，而不是只匹配对角强度。一般多 Kraus 结果按第七节的扩张处理，有限维环境保留其内部指标。选定的记录等距 $V=\sum_oM_o\otimes|o\rangle$ 也使用同一复标量与同一内积，所有跨记录块由这一实际 $V$ 固定。

P4 中，各完备读取的效果和为 $I$，故 $\sum_op_o=\operatorname{tr}\rho=1$，$p_o\ge0$。纯态时这正是 $\|M_o\psi\|^2$；混态时用谱分解或凸混合得到同一个迹公式。所有条件后继都仅在 $p_o>0$ 时归一化。相干投影测试使用它自己完整的二结果测量，不把不相容的多个 $F_E$ 拼成一个 POVM。

对 P5，把以后可用的参考、控制记忆和已产生记录留在联合载体；只在任务明确永不再访问时迹掉环境。有限深度协议的所有记录数和 Kraus 数有限，因此它的共同环境可以选为有限维。有限历史的载体为 $\mathbb C^{N+1}\otimes H$，其核／像由定理 8.2 给出；不要求把无限多个历史正交存入固定 $H_S$。这些构造已经在 [recursive] §6、[quantum] §§6、12 的共同仪器模型中供应，这里将标量、核与相位种子接到该同一实现。

最后，每个 $m$ 的种子参考维数为 $2^m$，每个有限协议的系数寄存器、记录载体和钟载体也按需增长。任意大但有限的 $m,N,k$ 给一族有限模型；固定系统维数五与不断增长的联合维数是两个不同陈述。这里没有一个固定有限总载体同时包含任意多个正交记录，也没有从有限秩读数推断无限载体基数维数。故五项条件在共同对象上同时成立，结论是条件模型的相容性。∎

这个模型没有证明 P1–P5 相互独立、逻辑最小或已经被原生设备全部实现。它把数值标量、状态与效果、核、分支、记录和参考的接口放进同一个明确实现；原菜单、扩充菜单、物理时间和空间桥梁仍有各自的供应条件。与仅有经典 Markov 递归图的反例相比，决定不同预测的正是相干比较、参考与完备结果标定这些额外关系。

## 13. 数学来源与适用范围

下表给出被实际消费的项目结果；每个引用都受其输入域、操作域和联合来源条件限制。原始供应文献的固定版本为 `d5e7fbecb49c0e928696f6857b331b3dbd54d128`；伴篇供应版本为 `ee1728e4f0c42ea4017a6ba12e2abb63210248f3`。

| 项目数学来源 | 所供应的数学内容 | 本文的消费范围 |
| --- | --- | --- |
| [static] §§1、3–7 | 一般复输入；受限的非负等待／完整读／反馈；配置、运输、交换条件；仪器与历史等距 | 原菜单与新增相干资源分开；保留真实门次序、共同来源和正概率条件态 |
| [second] §§61–65 | 五模式复实现、亮暗分离、两条最短路径环相位、实际效果空间 | 固定 $K$ 的双频与暗线、占位和相干的类型区别；复边是额外动力学 |
| [qmb] §4 | 两实旋转平面、暗线、同一等待轨道的加权平均谱 | 双频矩阵证明；轨道 Cesàro 闭包只作平均，不授予独立相位控制；加权效果算子的谱不等于 $K$ 的谱 |
| [wave] §§0–10、347–348 | 量子模型前提、历史态、记录干涉、局部边缘不足、holonomy 及其残差 | 历史、记录与共同未来；环相位不能由顶点坐标删除，平行截面须由 holonomy 固定 |
| [foundation] §16 | 平方自由轮筛的 Fourier 非消失、完整复共轭双谱字符证明、生成元行恢复、原点与条件数界限 | 完整复证明的直接复用；不把它认作新的复扩展或五态层析 |
| [bundle] §§3、7–8、10 | 态关系角与概率纤维、读出核的下降、全未来分支效果闭包、联合占位相位门 | 态角和连接通量分型；同一负指数约定与相位门增量；保留未来能访问的环境关系 |
| [sharp] §13，定理 13.1 | 实际全五维输出、全部复 qutrit 输入的矩形 $M_3\to M_5$ 刚性；每个原始正分支相同嵌入 | 只在实际角块上分类解码器；不分类角块外及跨块相干，不从裸图推出 CP |
| [recursive] §§2、4–8 | 正核商、原生两帧记忆、内部消元、记录和完整未来闭包 | 保核接续及隐藏记忆的真实接口；相干最小维数不冒充取得成本 |
| [unordered] §§6、14 | 二次权重、全效果赋值与共同相容模型 | 旋转正交权重与一般 Born 赋值的条件区分 |
| [tunnel] §§5、7–8 | 正失谐图的奇异通道、相位与电流、隐藏关系对未来读出的作用 | $\phi_{\rm T}=-\varphi$、零失谐单独全矩阵证明；不外推正失谐估计 |
| [quantum] §§4–7、9、11–12 | 统一复角块与矩阵单位、核与仪器、复合、全未来闭包和共同条件模型 | 本文各标准机制的供应者；增长参考／记录与固定五维系统分开 |

正核构造、谱定理、Schrödinger 群、Born 数值形式、历史编码、记录互补、Fourier 恢复、不确定性及不可克隆均使用已有数学。它们在本文中是带明确参数对应的消费步骤。相位种子、环通量、历史谱隙和连续误差界也只按所列普通证明的条件承担结论，不提出全球原创性、物理完备性或证明助理认证主张。

### 项目文献

1. **[static]** the-omega-institute/trureturing，*AURIC Omega Static Compatibility Fiber Theory*，[固定原文][static]，§1 及 §§3–7。
2. **[second]** the-omega-institute/trureturing，*AURIC FIB Second Order Relation Completion*，[固定原文][second]，§§61–65。
3. **[qmb]** the-omega-institute/trureturing，*Recursive Relational Observation: Measurement Relative Quantum Boundary*，[固定原文][qmb]，§4、定理 4.1 的谱分解。
4. **[wave]** the-omega-institute/trureturing，*波粒整体的关系全息表示*，[固定原文][wave]，§§0–10、347–348。
5. **[foundation]** the-omega-institute/trureturing，*AURIC FIB ATOM 金字塔基础公式与关系*，[固定原文][foundation]，§16。
6. **[bundle]** the-omega-institute/trureturing，*AURIC FIB Relational Bundle and Predictive Closure Theory*，[固定原文][bundle]，态相位、核与全未来接口。
7. **[sharp]** the-omega-institute/trureturing，*Recursive Relational Observation: Sharp Task Retained Environment Memory*，[固定原文][sharp]，§13、定理 13.1。
8. **[recursive]** the-omega-institute/trureturing，*AURIC 递归预测与边界几何*，[固定原文][recursive]。
9. **[unordered]** the-omega-institute/trureturing，*AURIC 无序相融原子与量子表示理论*，[固定原文][unordered]。
10. **[tunnel]** the-omega-institute/trureturing，*AURIC 内生原点不确定性与关系隧穿*，[固定原文][tunnel]。
11. **[quantum]** the-omega-institute/trureturing，*AURIC FIB ATOM 与量子基本原则：相干递归的条件综合*，[固定原文][quantum]。

### 经典文献及具体引用边界

12. **[djs]** F. Dowker、S. Johnston、R. D. Sorkin，*Hilbert Spaces from Path Integrals*，Journal of Physics A: Mathematical and Theoretical **43** (2010), 275302，[arXiv:1002.0589v3][djs]，§§2.2–2.3。强正性是输入；自由复空间、零范数商与完成给历史 Hilbert 空间，不由弱正事件权重直接得到。
13. **[dw]** F. Dowker、H. Wilkes，*An Argument for Strong Positivity of the Decoherence Functional in the Path Integral Approach to the Foundations of Quantum Theory*，[arXiv:2011.06120v2][dw] (2021)，[DOI:10.1116/5.0073587](https://doi.org/10.1116/5.0073587)。Theorem 3 的唯一性需要张量闭合且 Galois 自对偶；Theorem 4 只有“强正类或元素非负类”的分界，不能只凭复合闭合消去后者。
14. **[gks]** P. Goyal、K. H. Knuth、J. Skilling，*Origin of Complex Quantum Amplitudes and Feynman's Rules*，Physical Review A **81** (2010), 022109，[arXiv:0907.0909v3][gks]。该文实数对操作重建的串并联对称性包含结合、分配和连续性条件；本文二维全域范数乘法证明使用自己的明确条件，结合律由结论得到。
15. **[busch]** P. Busch，*Quantum States and Generalized Observables: A Simple Proof of Gleason's Theorem*，Physical Review Letters **91** (2003), 120403，[arXiv:quant-ph/9909073v3][busch]。对象是全效果域上的非负、归一化、效果可加赋值；无限维正态表示还使用其可数可加性。本文只援引有限维版本的归属，不能把仅三个局部读出当成全效果域。
16. **[feynman3]** R. P. Feynman、R. B. Leighton、M. Sands，*The Feynman Lectures on Physics*，Vol. III，Chapter 3: *Probability Amplitudes*，[Caltech 官方页面][feynman3]。
17. **[feynman13]** 同上，Vol. III，Chapter 13: *Propagation in a Crystal Lattice*，[Caltech 官方页面][feynman13]。这两章仅作主题背景书目，不承担本文任何具体定理的文本核验；串并联公式与晶格近似所需全部步骤已在正文独立给出。
18. **[historypaper]** D. Aharonov、W. van Dam、J. Kempe、Z. Landau、S. Lloyd、O. Regev，*Adiabatic Quantum Computation is Equivalent to Standard Quantum Computation*，SIAM Journal on Computing **37**(1) (2007), 166–194，[arXiv:quant-ph/0405098v2][historypaper]；初稿 2004，所引修订版 2005。只消费历史态及相邻传播约束背景；本文路径 Laplacian 采用未乘 $1/2$ 的式 (8.1)，不援引该论文复杂度等价结论或其他归一化下的精确隙常数。
19. **[keleti]** T. Keleti、M. N. Kolountzakis，*On the Determination of Sets by Their Triple Correlation in Finite Cyclic Groups*，Online Journal of Analytic Combinatorics，Issue 1 (2006), article 4，[arXiv:math/0603415v1][keleti]。使用非消失 Fourier 支撑下的平移恢复原理；不将其关于集合、实函数及不同有限循环群的更广分类替代本处全支撑假设。所需带共轭复字符证明由 [foundation] §16 完整供应。
20. **[englert]** B.-G. Englert，*Fringe Visibility and Which-Way Information: An Inequality*，Physical Review Letters **77** (1996), 2154–2157，[DOI:10.1103/PhysRevLett.77.2154][englert]。一般双路径互补背景；这里严格只证明等先验、等振幅、纯记录条件下的 $\mathcal V^2+\mathcal D^2=1$，不将等式外推到一般混合记录。
21. **[sorkin]** R. D. Sorkin，*Quantum Mechanics as Quantum Measure Theory*，Modern Physics Letters A **9** (1994), 3119–3128，[arXiv:gr-qc/9401003v2][sorkin]。干涉层次使用同一测度下互不相交的备选事件；本文 $I_3=0$ 对固定振幅 $a,b,c$ 展开，不能在开闭路径同时改变其他耦合时直接当作经验无三阶干涉结论。

[static]: https://github.com/the-omega-institute/trureturing/blob/d5e7fbecb49c0e928696f6857b331b3dbd54d128/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md
[second]: https://github.com/the-omega-institute/trureturing/blob/d5e7fbecb49c0e928696f6857b331b3dbd54d128/docs/develop/theory/AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md
[qmb]: https://github.com/the-omega-institute/trureturing/blob/d5e7fbecb49c0e928696f6857b331b3dbd54d128/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md
[wave]: https://github.com/the-omega-institute/trureturing/blob/d5e7fbecb49c0e928696f6857b331b3dbd54d128/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_WAVE_PARTICLE_EVENTS.md
[foundation]: https://github.com/the-omega-institute/trureturing/blob/d5e7fbecb49c0e928696f6857b331b3dbd54d128/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md
[bundle]: https://github.com/the-omega-institute/trureturing/blob/d5e7fbecb49c0e928696f6857b331b3dbd54d128/docs/develop/theory/AURIC_FIB_RELATIONAL_BUNDLE_AND_PREDICTIVE_CLOSURE_THEORY.md
[sharp]: https://github.com/the-omega-institute/trureturing/blob/d5e7fbecb49c0e928696f6857b331b3dbd54d128/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SHARP_TASK_RETAINED_ENVIRONMENT_MEMORY.md
[recursive]: https://github.com/the-omega-institute/trureturing/blob/ee1728e4f0c42ea4017a6ba12e2abb63210248f3/docs/develop/theory/AURIC_RECURSIVE_PREDICTION_AND_BOUNDARY_GEOMETRY.md
[unordered]: https://github.com/the-omega-institute/trureturing/blob/ee1728e4f0c42ea4017a6ba12e2abb63210248f3/docs/develop/theory/AURIC_UNORDERED_COMPATIBLE_ATOM_AND_QUANTUM_REPRESENTATION_THEORY.md
[tunnel]: https://github.com/the-omega-institute/trureturing/blob/ee1728e4f0c42ea4017a6ba12e2abb63210248f3/docs/develop/theory/AURIC_ENDOGENOUS_ORIGIN_UNCERTAINTY_AND_RELATIONAL_TUNNELING.md
[quantum]: https://github.com/the-omega-institute/trureturing/blob/ee1728e4f0c42ea4017a6ba12e2abb63210248f3/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md
[djs]: https://arxiv.org/abs/1002.0589v3
[dw]: https://arxiv.org/abs/2011.06120v2
[gks]: https://arxiv.org/abs/0907.0909v3
[busch]: https://arxiv.org/abs/quant-ph/9909073v3
[feynman3]: https://www.feynmanlectures.caltech.edu/III_03.html
[feynman13]: https://www.feynmanlectures.caltech.edu/III_13.html
[historypaper]: https://arxiv.org/abs/quant-ph/0405098v2
[keleti]: https://arxiv.org/abs/math/0603415v1
[englert]: https://doi.org/10.1103/PhysRevLett.77.2154
[sorkin]: https://arxiv.org/abs/gr-qc/9401003v2

## 追加锚（本行以下为增补区）
