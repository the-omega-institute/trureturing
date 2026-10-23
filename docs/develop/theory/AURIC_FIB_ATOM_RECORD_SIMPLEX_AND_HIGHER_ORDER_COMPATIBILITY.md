# Auric FIB-ATOM：记录单纯形与高阶相容

**来源与范围。** 本卷固定读取项目 `dev` 快照 `162432b`，记录最新相关合并 #14802 关于共享深度、停止协议和有限 COMPLETE 观察者的边界；原文中的风险常数记为 $\delta_*$。本文由本次会话提供的用户理论文本整理而成；作者类型为 mixed，原作者/模型身份未指定，整理者为 Codex；来源标识为本次会话，日期为 2026-10-10。本文是参考输入，Lean 才是仓库数学真值来源；本文不声称 Lean 已验证。风险定理只作为外部背景，不在本卷重新证明。经典读口、记录几何和量子四面体测量均是明确声明的附加模型。

## 1. 五模式来源与有限记录实验

沿用

$$
\Sigma=\{\mathsf F[\varnothing],\mathsf F[1],\mathsf F[2],\mathsf F[3],\mathsf F[1,3]\}.
$$

令

$$
x=\mathbf1_{\{1\text{ 被选}\}},\qquad y=\mathbf1_{\{3\text{ 被选}\}},\qquad z=\mathbf1_{\{2\text{ 被选}\}},
$$

满足 $xz=yz=0$。五模式概率按

$$
p=(p_{\varnothing},p_1,p_2,p_3,p_{13})
$$

排列，记 $X=\mathbb E[x]$、$Y=\mathbb E[y]$、$Z=\mathbb E[z]$ 和 $\kappa=\mathbb E[xy]$。完整概率仍为

$$
\begin{aligned}
p_{\varnothing}&=1-X-Y-Z+\kappa,&p_1&=X-\kappa,\\
p_2&=Z,&p_3&=Y-\kappa,&p_{13}&=\kappa.
\end{aligned}
$$

三个均值构成金字塔 $\mathcal P=\{X,Y,Z\ge0:X+Z\le1,\;Y+Z\le1\}$，但一般来源还需要 $\kappa$。

### 定义 1.1：不改变模式的经典条件读口

固定严格正来源律 $p$。读口返回有限结果 $O$，条件似然为

$$
L(o\mid s)=\Pr(O=o\mid s),\qquad \sum_oL(o\mid s)=1.
$$

结果概率和后验为

$$
q_o=\sum_sp_sL(o\mid s),\qquad p_s^o=\frac{p_sL(o\mid s)}{q_o},
$$

只讨论 $q_o>0$ 的实际结果。

### theorem 1.2: 后验必须保持同一来源的重心

**Claim status: open.** 对任意有限条件读口，

$$
\boxed{\sum_oq_op^o=p.}
$$

反过来，若 $q_o>0$、$\sum_oq_o=1$，并且候选后验满足 $\sum_oq_op^o=p$，则可取

$$
\boxed{L(o\mid s)=\frac{q_op_s^o}{p_s}}
$$

实现这份后验分解。

**证明。** 第一式直接由 Bayes 公式消去分母。反向式非负，并由重心条件保证每个模式上的似然和为一，代回即可。证毕。

这只是经典有限 Bayes plausibility；它不自动授予原生 FIB 读者任意查询权限。只检查 $\sum_oq_o(X_o,Y_o,Z_o)=(X,Y,Z)$ 仍然不够，还必须有

$$
\boxed{\sum_oq_o\kappa_o=\kappa}
$$

才能保证候选后验来自同一个五模式来源。

## 2. 记录容量与均值变化方向

取目标函数 $F=(f_1,\ldots,f_d)^{\mathsf T}$，令

$$
m=\mathbb E[F],\qquad m_o=\mathbb E[F\mid O=o].
$$

记录分离矩阵定义为

$$
B=\sum_oq_o(m_o-m)(m_o-m)^{\mathsf T}.
$$

它记录不同结果使目标均值发生的方向。

### theorem 2.1: $m$ 个结果最多承载 $m-1$ 个独立变化方向

**Claim status: open.** 若有 $m$ 个正概率结果，则

$$
\boxed{\operatorname{rank}B\le m-1.}
$$

**证明。** 把列向量 $\sqrt{q_o}(m_o-m)$ 排成矩阵 $A$，则 $B=AA^{\mathsf T}$。重心条件给出

$$
A(\sqrt{q_1},\ldots,\sqrt{q_m})^{\mathsf T}=0,
$$

故 $A$ 至少有一条核方向，$\operatorname{rank}A\le m-1$。证毕。

因此，两结果最多给线段方向，三结果最多给三角形的二维方向，四结果最多给四面体的三维方向；一般 $d+1$ 个结果才可能满秩承载 $d$ 个变化方向。这里的维数是目标读口和记录分离的维数，不是预设的物理空间维数。

## 3. 独立关系与记录正交性

设 $b_1,\ldots,b_d$ 在观察前相互独立，$0<u_i=\Pr(b_i=1)<1$。结果 $o$ 后记

$$
u_i(o)=\Pr(b_i=1\mid o).
$$

称第 $i$ 项被非平凡读取，是指

$$
\nu_i=\operatorname{Var}_O(u_i(O))>0.
$$

### theorem 3.1: 保持每个后验独立时的结果数下界

**Claim status: open.** 若观察前 $b_1,\ldots,b_d$ 相互独立，每个正概率结果下它们仍相互独立，并且所有 $\nu_i>0$，则

$$
\boxed{m\ge d+1.}
$$

**证明。** 总协方差公式给出，对 $i\ne j$，

$$
\operatorname{Cov}(b_i,b_j)=\mathbb E[\operatorname{Cov}(b_i,b_j\mid O)]+\operatorname{Cov}(u_i(O),u_j(O)).
$$

前后独立使前两项中的总协方差和条件协方差都为零，故记录均值变化两两正交。于是 $B=\operatorname{diag}(\nu_1,\ldots,\nu_d)$ 的秩为 $d$，再用定理 2.1 即得。证毕。

这里的“正交”来自同一份实际结果概率下的内积，而不是预先放置的坐标轴。在 FIB 链上，把偶数位固定为零、只让 $1,3,\ldots,2d-1$ 变化，就得到一份合法的 $d$ 位独立子来源；$d=2$ 时正是单窗金字塔底面。

## 4. $d+1$ 结果的可达构造

### 定义 4.1：逐位首次返回一的读口

依次读取 $b_1,\ldots,b_d$。每次使用明确的二结果读口

$$
\Pr(Y_i=1\mid b_i=0)=\frac14,\qquad \Pr(Y_i=1\mid b_i=1)=\frac34,
$$

各次读口内部随机性按模型独立。最终记录为第一次返回一的位置，若全部返回零则记为 $d+1$。

### theorem 4.2: 首次返回协议达到 $d+1$ 结果下界

**Claim status: open.** 结果 $i\le d$ 的似然为

$$
L_i(b)=\left[\prod_{j<i}(1-\ell_j(b_j))\right]\ell_i(b_i),
$$

最后结果的似然为

$$
L_{d+1}(b)=\prod_{j=1}^{d}(1-\ell_j(b_j)).
$$

这些似然之和为一，且每个都是单位置因子的乘积。因此任何严格正乘积先验在每个结果下仍为乘积后验；所有结果概率严格为正，并且每个方向的后验均值都发生非零变化。

**证明。** 似然表达式由首次返回事件直接得到，行和由互斥穷尽性得到。乘积先验乘以单位置因子后仍为乘积律。对第 $i$ 位，结果 $i$ 与全零结果对该位的因子不同，故其后验均值不恒定。证毕。

在均匀先验 $u_i=1/2$ 下，

$$
q_i=2^{-i}\ (1\le i\le d),\qquad q_{d+1}=2^{-d},
$$

且

$$
m_i=(\underbrace{1/4,\ldots,1/4}_{i-1},3/4,\underbrace{1/2,\ldots,1/2}_{d-i}),
\qquad m_{d+1}=(1/4,\ldots,1/4).
$$

以最后一点为原点，差向量矩阵为对角线全为 $1/2$ 的三角矩阵，故

$$
\boxed{V_d=\frac1{2^d d!}}.
$$

特别地，$d=1$ 为长度 $1/2$ 的线段，$d=2$ 为面积 $1/8$ 的三角形，$d=3$ 为体积 $1/48$ 的四面体。这里的几何来自真实结果的后验分离。

## 5. 高阶共同来源相容性

### theorem 5.1: 乘积后验的完整共同来源条件

**Claim status: open.** 设先验是 $d$ 个独立 Bernoulli 变量，均值为 $u_i$；候选后验也都是乘积律，均值为 $u_i(o)$。它们能由某个有限随机读口从原先验产生，当且仅当对每个子集 $A\subseteq\{1,\ldots,d\}$ 都有

$$
\boxed{\sum_oq_o\prod_{i\in A}u_i(o)=\prod_{i\in A}u_i.}
$$

**证明。** 左侧是候选后验混合中事件“$A$ 内全部为一”的概率，右侧是原乘积先验对应事件的概率。所有共同事件概率确定整个二元联合分布：对未选位置展开 $\prod(1-b_i)$ 可恢复每个精确配置概率。因此它们等价于完整重心条件，定理 1.2 给出读口实现。证毕。

两变量只需一阶和二阶条件；三变量还必须检查三阶条件。

### theorem 5.2: 正四面体的一阶二阶正确不保证共同来源

**Claim status: open.** 取三个独立公平位，候选四个等概率乘积后验的均值为

$$
u(o)=\frac12(1,1,1)+\varepsilon s_o,
$$

其中 $0<\varepsilon<1/2$，且

$$
s_o\in\{(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)\}.
$$

这四点构成正四面体，满足一阶平均 $\mathbb E[u_i]=1/2$ 和二阶平均 $\mathbb E[u_iu_j]=1/4$（$i\ne j$），但

$$
\boxed{\mathbb E[u_1u_2u_3]=\frac18+\varepsilon^3\ne\frac18.}
$$

所以它们不能来自原来的独立公平先验。取 $\varepsilon=1/4$ 时，候选混合给 $111$ 的概率 $9/64$，而原概率是 $8/64$。

**证明。** 对四个符号向量逐项平均，一阶和二阶符号积均为零，而三阶符号积恒为一；展开乘积即得。三阶共同事件不相容，所以定理 5.1 排除该分解。证毕。

对称性和漂亮的外形不自动保证共同来源；上一节的递归四面体之所以可行，是因为它逐步由同一读口生成。

## 6. 记录不足时的条件关联预算

仍取观察前独立的 $b_i$，但不再要求后验独立。令

$$
B_{ij}=\operatorname{Cov}_O(u_i(O),u_j(O)),\qquad \nu_i=B_{ii}>0,
$$

以及平均条件协方差

$$
S_{ij}=\mathbb E_O[\operatorname{Cov}(b_i,b_j\mid O)].
$$

总协方差给出 $S_{ij}=-B_{ij}$（$i\ne j$）。

### theorem 6.1: 结果不足强制留下非零条件关联

**Claim status: open.** 若 $2\le m\le d$，则

$$
\boxed{
\sum_{i\ne j}\frac{S_{ij}^2}{\nu_i\nu_j}
\ge\frac{d(d-m+1)}{m-1}.
}
$$

**证明。** 令 $R_{ij}=B_{ij}/\sqrt{\nu_i\nu_j}$。矩阵 $R$ 正半定、对角元为一，故 $\operatorname{tr}R=d$；定理 2.1 给出 $\operatorname{rank}R\le m-1$。对非零特征值使用 Cauchy–Schwarz，得 $\operatorname{tr}(R^2)\ge d^2/(m-1)$。扣除对角平方并代入 $S_{ij}=-B_{ij}$ 即得。证毕。

当 $d=m=2$ 时还精确满足

$$
\boxed{|\mathbb E[\operatorname{Cov}(b_1,b_2\mid O)]|=\sqrt{\nu_1\nu_2}.}
$$

记录空间不足以容纳全部正交方向时，一部分关系必然转移到后验耦合中；这仍是经典条件化，不是量子纠缠。

## 7. 完整五模式的四结果更新四面体

取五模式均匀先验 $p_s=1/5$，所以 $(X,Y,Z)=(2/5,2/5,1/5)$。先读取 $z$：若 $z=1$ 就记录中间被选并停止；若 $z=0$，再对 $x,y$ 采用逐位首次返回一协议。四种结果为

| 记录 | 概率 | 后验 $(X_o,Y_o,Z_o)$ | $\kappa_o$ |
| --- | ---: | --- | ---: |
| 中间被选 | $1/5$ | $(0,0,1)$ | $0$ |
| 低端读口首次返回一 | $2/5$ | $(3/4,1/2,0)$ | $3/8$ |
| 低端返回零、高端返回一 | $1/5$ | $(1/4,3/4,0)$ | $3/16$ |
| 两次都返回零 | $1/5$ | $(1/4,1/4,0)$ | $1/16$ |

后三个底面后验仍为两端乘积律；中间结果是确定模式。零概率支撑按表单独处理。

### theorem 7.1: 四结果后验形成非退化记录四面体

**Claim status: open.** 上表四个后验金字塔均值形成体积

$$
\boxed{V_{\mathrm{rec}}=\frac1{24}}
$$

的非退化四面体；其记录分离矩阵满足

$$
\boxed{\det B=\frac1{5000}.}
$$

**证明。** 三个底面点围成面积 $1/8$ 的三角形，顶点距底面高度为一，故体积为 $(1/3)(1/8)=1/24$。对一般 $d+1$ 个仿射独立记录点，齐次矩阵分解给出

$$
\det B=(d!)^2V_d^2\prod_oq_o.
$$

代入四个概率得到 $36(1/24)^2(1/5)(2/5)(1/5)(1/5)=1/5000$。证毕。

四个结果能在三个平均方向上产生满秩分离，但不等于一次结果识别五个真实模式；后三种结果仍含多个正后验模式。

## 8. 平均记录熵与最坏资源的区别

逐位首次返回协议的结果概率为 $q_i=2^{-i}$（$i\le d$）和 $q_{d+1}=2^{-d}$，对应记录词 $1,01,001,\ldots,0^{d-1}1,0^d$。

### theorem 8.1: 协议平均读取少于二次但最坏深度增长

**Claim status: open.**

$$
\boxed{\mathbb E[\text{读取次数}]=\sum_{i=1}^d2^{-(i-1)}=2(1-2^{-d})<2,}
$$

并且 $H(O)=2(1-2^{-d})$ 比特；但最坏读取次数为 $d$，结果种类为 $d+1$。第 $j$ 个方向的记录变化强度为

$$
\boxed{\nu_j=2^{-j-3}.}
$$

**证明。** 到达第 $j$ 次读取的概率为 $2^{-(j-1)}$，该方向的后验均值相对 $1/2$ 只变为 $1/4$ 或 $3/4$，所以 $\nu_j=2^{-(j-1)}(1/4)^2$；其余结论由几何级数和记录词长度得到。证毕。

平均熵小并不表示用不到两比特保存任意多份等强信息：越后面的方向取得越弱、越罕见的信息。结果种类、平均熵、最坏读取次数、程序位置和每方向强度是不同资源指标。

## 9. 动态预测变化的正交分解

设 $\mathcal H_n$ 是第 $n$ 次实际操作后保留的完整记录，令 $m_n=\mathbb E[F\mid\mathcal H_n]$，并记 $\delta_n=m_{n+1}-m_n$。

### theorem 9.1: 逐步预测变化具有正交增量分解

**Claim status: open.**

$$
\boxed{\mathbb E[\delta_n\mid\mathcal H_n]=0}
$$

且对固定有限 $T$，

$$
\boxed{\mathbb E[(m_T-m_0)(m_T-m_0)^{\mathsf T}]=\sum_{n=0}^{T-1}\mathbb E[\delta_n\delta_n^{\mathsf T}].}
$$

**证明。** 第一式是条件期望的塔式性质。若 $i<j$，则 $\delta_i$ 已包含在 $\mathcal H_j$ 中，故 $\mathbb E[\delta_i\delta_j^{\mathsf T}]=\mathbb E[\delta_i\mathbb E[\delta_j^{\mathsf T}\mid\mathcal H_j]]=0$。展开总变化的外积即可。证毕。

单个二结果节点的条件分离矩阵秩至多一，多步二元读取却可逐步积累多个方向。若实际读口的反向作用读取了当前没有保存的函数，就必须扩充边界；五模式中读取 $x$ 后继续预测 $y$ 正是需要补上 $xy$ 的情形。

在 #14802 的共享深度来源中，$r_k=F_{k+1}/F_{k+3}$。若当前后验为 $\nu_h$，$m_h=\mathbb E_{\nu_h}[r]$，实际取得 $\alpha$ 后

$$
\nu_{h\alpha}(k)=\frac{\nu_h(k)r_k}{m_h},\qquad
\boxed{m_{h\alpha}-m_h=\frac{\operatorname{Var}_{\nu_h}(r)}{m_h}>0}
$$

只要当前支撑含有不同的 $r_k$。这是来源后验计算，不是把后验向量当成设备免费持有的寄存器；有限 COMPLETE 观察者的风险移动要求仍需单独使用 #14802 的合同和定理。

## 10. 量子四面体测量是另一种明确实现

另行供应一个两能级接口，态写成

$$
\varrho=\frac12(I+r_xX+r_yY+r_zZ),\qquad \|\mathbf r\|\le1.
$$

取四个单位向量

$$
n_a\in\frac1{\sqrt3}\{(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)\},
$$

满足 $\sum_an_a=0$、$\sum_an_an_a^{\mathsf T}=4I/3$，定义

$$
E_a=\frac14(I+n_a\cdot\sigma).
$$

### theorem 10.1: 四结果概率反演两能级态的三个参数

**Claim status: open.** 每个 $E_a\ge0$ 且 $\sum_aE_a=I$，结果概率为

$$
\boxed{q_a=\operatorname{tr}(\varrho E_a)=\frac{1+n_a\cdot\mathbf r}{4},}
$$

并且

$$
\boxed{\mathbf r=3\sum_aq_an_a.}
$$

**证明。** $n_a\cdot\sigma$ 的特征值为 $\pm1$，所以 $E_a$ 的特征值为 $0,1/2$；归一化与反演分别使用两个向量恒等式。证毕。

不是任意四个概率都对应允许态，还需

$$
\boxed{\sum_aq_a^2=\frac14+\frac{\|\mathbf r\|^2}{12}\le\frac13.}
$$

这是标准对称信息完备测量的应用，不是本卷声称的新量子发现。经典乘积后验的正四面体与该量子测量的四面体对象不同，前者仍受共同来源三阶条件约束。

## 11. 结论与边界

本卷的三条核心关系是

$$
\boxed{\operatorname{rank}\operatorname{Cov}_O(\mathbb E[F\mid O])\le m-1,}
$$

$$
\boxed{\sum_oq_o\prod_{i\in A}u_i(o)=\prod_{i\in A}u_i\quad\text{对全部共同事件 }A,}
$$

以及

$$
\boxed{\det B=(d!)^2V_d^2\prod_oq_o.}
$$

第一式是记录容量下界，第二式检验候选后验是否来自同一来源，第三式把记录概率和其单纯形体积联系起来。

因此，$d$ 项独立而非零的记录变化至少需要 $d+1$ 个结果；达到这个维数仍不保证共同来源，三阶及更高共同事件必须继续检查。少记结果会把不能容纳的方向转为后验条件关联。平均熵很小也不代表最坏深度、记录标签、精度和每方向强度都小。量子四面体测量需要另行声明正性和实际仪器，不能替代经典共同来源或相干历史。

本卷是普通数学参考输入，未执行 Lean 验证，也未重复验证仓库整卷的风险定理。

## 追加锚（本行以下为增补区）

## 12. 原生风险背景与文献来源

本卷供应文本报告：#14802 在原共享深度、停止协议和有限 COMPLETE 观察者合同下给出

$$
240e(M)+30\mathcal A(M)>\delta_*>0.
$$

其中 $e$ 是两项完整未来配置风险的超额，$\mathcal A$ 是同一次实际 suspended-$\alpha$ 更新前后，下一次 $\alpha$ 发射概率的平均绝对变化。这里的 $\delta_*$ 不同于五模式共同参数 $\kappa$。该背景结论不声称共同最优者存在，也不把一般误差下界与禁止更新子类的下界混为一谈；本卷没有重新验证其整卷风险证明，也没有把它的资源下界转移到新增随机读口。

有限后验重心条件的经典来源是 [Kamenica–Gentzkow, Bayesian Persuasion](https://web.stanford.edu/~gentzkow/research/BayesianPersuasion.pdf)。两能级四面体效果属于既有对称信息完备测量，见 [Renes–Blume-Kohout–Scott–Caves, Symmetric Informationally Complete Quantum Measurements](https://arxiv.org/abs/quant-ph/0310075)。本卷不重新宣称这些结果为原创。

## 13. 供应文本的实验声明

供应文本报告以精确有理数和符号代数检查 84 份有限读口和 323 个正概率分支，其中有 28 份一般乘积先验的最小结果构造、7 个单纯形体积与成本公式、40 组记录不足的关联下界，以及完整金字塔四结果构造、三阶不相容反例和四面体量子测量；另报告 21 组共享深度的 $\alpha$ 条件更新。原报告的脚本名为 `fib_record_simplex_checks.py`，结果名为 `fib_record_simplex_checks.json`。对应 sandbox 链接没有供应本次工作树可读取的文件字节，因此本次摄入没有复跑这些实验，不把作者报告的计数当成新的程序验证。一般结论由本卷普通数学论证承担，未执行 Lean 验证。

## 追加锚 2（本行以下为增补区）

## 14. 占位仿射记录的四角核与同源二阶读口

沿用 §1 的五模式次序 $(0,1,2,3,13)$、占位 $(x,z,y)$ 和概率族

$$
p_\kappa=(1-X-Y-Z+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
\qquad d=\partial_\kappa p_\kappa=(1,-1,0,-1,1).
$$

固定 $X,Y,Z$，要求可行 $\kappa$ 区间非退化。另行供应一个经典记录模型

$$
R=xu+yv+zw+\Xi,\qquad u,v,w\in\mathbb R^D,\quad D\ge1,
\qquad (\mu_0,\mu_1,\mu_2,\mu_3,\mu_{13})=(0,u,w,v,u+v),
$$

其中噪声 $\Xi$ 独立于标签，概率律不随 $\kappa$ 变化；共同平移已减去。这是占位仿射编码假设，不由原生来源的存在自动推出。读出对象为完整 $\mathbb R^D$ 记录律，未先量化或只保留均值。

**定理 14.1（四角方向被完全消去的准确条件）。** 对任意共同加性噪声概率律，$\mathcal L_\kappa(R)$ 与 $\kappa$ 无关，当且仅当 $u=0$ 或 $v=0$。若 $u,v\ne0$，任意两个不同可行参数给出不同的记录律。

证明。记噪声特征函数为 $\widehat\nu(t)$。记录律对参数的有符号变化具有特征函数

$$
\widehat\nu(t)\left(1-e^{it^{\mathsf T}u}\right)
\left(1-e^{it^{\mathsf T}v}\right).
\tag{14.1}
$$

任一方向为零即使其恒零。反之，两个真超平面不能覆盖 $\mathbb R^D$，可取 $a$ 使 $a^{\mathsf T}u,a^{\mathsf T}v$ 均非零。由 $\widehat\nu(0)=1$ 及连续性，它在零的一个邻域不为零；对足够小的非零 $s$，取 $t=sa$，两个括号也非零。特征函数的唯一性使有符号变化非零。记录律对 $\kappa$ 仿射，故不同参数的差等于这个非零变化乘以参数差。此论证不要求噪声有矩，也不要求其特征函数在整个空间非零。$\square$

若噪声零均值且有有限二阶矩，则直接按五模式求和给

$$
\mathbb E_\kappa R=Xu+Yv+Zw,\qquad
\partial_\kappa\mathbb E_\kappa RR^{\mathsf T}
=\partial_\kappa\operatorname{Cov}_\kappa R
=uv^{\mathsf T}+vu^{\mathsf T}.
\tag{14.2}
$$

这是定理14.1在有限二阶矩模型中的显式读口：同一个 $a$ 满足
$\partial_\kappa\mathbb E(a^{\mathsf T}R)^2=2(a^{\mathsf T}u)(a^{\mathsf T}v)\ne0$，尽管一阶均值恒盲。完整分布的可识别不等于从有限随机样本精确恢复参数。

共同来源身份也能决定这个二阶读口是否合法。另供 $R_x=x+\xi$、$R_y=y+\eta$，噪声相互独立、零均值且独立于标签，并有可积乘积。各边缘分别仅依赖 $X,Y$。若来自同一标签，$\mathbb E R_xR_y=\mathbb E xy=\kappa$；若分别抽取独立标签，则 $\mathbb E R_xR_y=XY$。因此两个各自失明的完整边缘报告，只有在保留配对来源时才能通过交叉矩读取四角关系。这与 §5 的共同来源条件相接，不把任意两份边缘事后拼成同一来源。

## 15. 合法关系方向的观察阶数与高斯 Fisher 系数

给长度 $n\ge1$ 的合法集合族

$$
\mathcal B_n=\{I\subseteq\{1,\ldots,n\}:I\text{ 不含相邻位置}\},
$$

选择非空合法集合 $T=\{t_1,\ldots,t_r\}$。定义零总质量的基本方向

$$
d_T(I)=\begin{cases}(-1)^{r-|I|},&I\subseteq T,\\0,&I\not\subseteq T.\end{cases}
\qquad p_\theta=p^0+\theta d_T.
\tag{15.1}
$$

在一个固定、全正的参考参数点估计 $\theta$；其他概率坐标和所有读出向量已知。所有 $I\subseteq T$ 均合法，故该方向确实留在指定支持内。另供白化高斯记录

$$
R_\varepsilon=\varepsilon m_I+G,\qquad
m_I=\sum_{i\in I}a_i,\quad a_i\in\mathbb R^D,\quad
G\sim\mathcal N(0,I_D),\qquad \varepsilon>0.
\tag{15.2}
$$

这些是有限经典混合实验。有限差分的低阶消去在《隐藏关系、统计、相位与接缝》C-22.2 已用于指定原生数量；此处新增的是对合法关系方向的高斯似然及信息尺度的组合。低信噪比与矩层级的文献背景见 Katsevich–Bandeira, [*Likelihood maximization and moment matching in low SNR Gaussian mixture models*](https://arxiv.org/abs/2006.15202)；不把一般矩匹配或 Hermite 方法作为新工具。

**定理 15.1（关系阶数、读出核与 permanent 系数）。** 在上述单参数实验中，完整记录律消去 $\theta$ 当且仅当某个 $a_i=0$，$i\in T$。对任意 $b\in\mathbb R^D$，

$$
\begin{aligned}
\partial_\theta\mathbb E(b^{\mathsf T}R_\varepsilon)^q&=0 &&(0\le q<r),\\
\partial_\theta\mathbb E(b^{\mathsf T}R_\varepsilon)^r
&=r!\,\varepsilon^r\prod_{i\in T}b^{\mathsf T}a_i.
\end{aligned}
\tag{15.3}
$$

令 $f_{\varepsilon,\theta}$ 为密度，$\Gamma_T=(a_{t_i}^{\mathsf T}a_{t_j})_{i,j=1}^r$。单份新标签记录的 Fisher 信息为

$$
\begin{aligned}
\mathcal J_T(\varepsilon)
&:=\int\frac{(\partial_\theta f_{\varepsilon,\theta})^2}{f_{\varepsilon,\theta}}
=\varepsilon^{2r}\operatorname{per}(\Gamma_T)+O(\varepsilon^{2r+2}),\\
\operatorname{per}(\Gamma)&:=\sum_{\pi\in S_r}\prod_{i=1}^r\Gamma_{i,\pi(i)}.
\end{aligned}
\tag{15.4}
$$

若所有参与向量均非零，则该系数严格正。这里的余项在固定实验及固定内部参数点取 $\varepsilon\to0$，不是对增长的 $n,r$ 或趋向概率边界的统一界。

证明。有限差分与高斯特征函数给出精确式

$$
\partial_\theta\widehat f_{\varepsilon,\theta}(\xi)
=e^{-\|\xi\|^2/2}\prod_{i\in T}
\left(e^{i\varepsilon\xi^{\mathsf T}a_i}-1\right).
\tag{15.5}
$$

按定理14.1的避超平面论证，乘积恒零恰好要求某个参与向量为零。对次数 $q$ 的条件矩作 $r$ 次有限差分，$q<r$ 时消去；$q=r$ 时只有每个方向各出现一次的项留下，给（15.3）。若所有方向非零，可取同时不垂直于它们的 $b$，因此首次可见矩阶确为 $r$。

为求首项，记 $\phi$ 为标准高斯密度，用经典 Hermite 生成函数定义

$$
H_T(x)=\left.\partial_{s_1}\cdots\partial_{s_r}
\exp\left(x^{\mathsf T}\sum_i s_i a_{t_i}
-\tfrac12\left\|\sum_i s_i a_{t_i}\right\|^2\right)\right|_{s=0}.
$$

有限差分展开使 $\partial_\theta f_{\varepsilon,\theta}(x)
=\phi(x)[\varepsilon^rH_T(x)+O_x(\varepsilon^{r+1})]$。
对两个生成函数取同一个标准高斯期望得到 $\exp(s^{\mathsf T}\Gamma_T t)$；对全部 $s_i,t_i$ 各求一次导数，便有

$$
\mathbb E H_T(G)^2=\operatorname{per}(\Gamma_T).
\tag{15.6}
$$

这使用成熟的高斯 Hermite 配对，只保留跨两份生成函数的配对，并非未正规排序的全部 Wick 配对。最高次齐次项为 $\prod_{i\in T}a_i^{\mathsf T}x$；各向量非零时它不是零多项式，所以平方积分严格正。

积分余项可如下控制。写 $f_{\varepsilon,\theta}=\phi F_\varepsilon$、$\partial_\theta f_{\varepsilon,\theta}=\phi D_\varepsilon$。空集合均值为零且质量 $p_\theta(\varnothing)>0$，故 $F_\varepsilon\ge p_\theta(\varnothing)$。在任意固定小区间 $|\varepsilon|\le\varepsilon_0$，有限均值集的所有所需阶导数被常数乘 $(1+\|x\|)^K e^{c\|x\|}$ 支配。对 $D_\varepsilon^2/F_\varepsilon$ 作有限次求导，分母的负幂仍由该正质量控制，乘 $\phi$ 后均可积。于是信息积分有至 $2r+2$ 阶的连续导数并可逐项 Taylor 展开；$D_\varepsilon$ 的前 $r-1$ 阶导数为零，首系数为（15.6）。最后 $f_{-\varepsilon,\theta}(x)=f_{\varepsilon,\theta}(-x)$ 使信息为偶函数，排除 $2r+1$ 次项，得到（15.4）。$\square$

§14 的四角方向是 $T=\{1,3\}$、$r=2$、$a_1=u,a_3=v$，中位向量 $w$ 不进入有符号差。因此

$$
\mathcal J_\kappa(\varepsilon)
=\varepsilon^4 C_2+O(\varepsilon^6),\qquad
C_2=\|u\|^2\|v\|^2+(u^{\mathsf T}v)^2,
\tag{15.7}
$$

且首阶似然方向为 $H_{u,v}(x)=(u^{\mathsf T}x)(v^{\mathsf T}x)-u^{\mathsf T}v$。它读取关系而不要求先反演全部占位坐标。

维数与关系阶数不能互换：若所有 $i\in T$ 都有 $a_i=a\ne0$，则 $\Gamma_T$ 秩一而 $\operatorname{per}(\Gamma_T)=r!\|a\|^{2r}>0$。这仍只是其余参数固定时的单方向结论。例如五位合法历史中 $S=\{1,3\}$、$T=\{1,5\}$，所有位置取同一非零向量 $a$，则两个方向产生相同的密度变化
$\phi(x)-2\phi(x-\varepsilon a)+\phi(x-2\varepsilon a)$。二参数族 $p^0+\alpha d_S+\beta d_T$ 仅通过 $\alpha+\beta$ 进入记录，不能分别恢复。各方向单独可见不保证联合参数可识别。

## 16. 四角方向的显式二次估计量

在 §14 的五模式和白化记录 $R_\varepsilon=\varepsilon\mu_C+G$ 下，固定全正概率点，已校准 $X,Y,Z,u,v,w$，只估计 $\kappa$。设 $u,v\ne0$，写

$$
\begin{aligned}
A&=\|u\|^2,&B&=\|v\|^2,&C&=u^{\mathsf T}v,&C_2&=AB+C^2,\\
L_0&=C(XA+YB)+Z(u^{\mathsf T}w)(v^{\mathsf T}w),&&&
H(r)&=(u^{\mathsf T}r)(v^{\mathsf T}r)-C.
\end{aligned}
$$

**定理 16.1（新来源样本上的无偏读取及首阶效率）。** 对 $N$ 份独立重新抽取标签的记录，估计量

$$
\widehat\kappa=\frac{N^{-1}\sum_{a=1}^N H(R_a)/\varepsilon^2-L_0}{C_2}
\tag{16.1}
$$

在每个 $\varepsilon>0$ 精确无偏，且固定实验下

$$
\operatorname{Var}(\widehat\kappa)
=\frac1{N\varepsilon^4C_2}[1+O(\varepsilon^2)].
\tag{16.2}
$$

证明。对标签 $s$ 写 $\alpha_s=u^{\mathsf T}\mu_s$、$\beta_s=v^{\mathsf T}\mu_s$。高斯二阶及四阶矩给

$$
\begin{aligned}
\mathbb E[H(R)\mid C=s]&=\varepsilon^2\alpha_s\beta_s,\\
\operatorname{Var}(H(R)\mid C=s)
&=C_2+\varepsilon^2(B\alpha_s^2+A\beta_s^2+2C\alpha_s\beta_s).
\end{aligned}
$$

代入五个均值及 $p_\kappa$ 得 $\mathbb E\alpha_C\beta_C=L_0+\kappa C_2$，故（16.1）无偏。全方差公式给精确式

$$
\operatorname{Var}H(R)=C_2
+\varepsilon^2\mathbb E(B\alpha_C^2+A\beta_C^2+2C\alpha_C\beta_C)
+\varepsilon^4\operatorname{Var}(\alpha_C\beta_C).
$$

新标签样本独立，样本均值方差除以 $N$，即得（16.2）。与（15.7）的单参数 Cramér–Rao 下界 $1/(N\mathcal J_\kappa)$ 比较，二者首项相同。此处只称弱信号首阶有效，不称任意有限信号下达到界；估计量可落在可行区间之外，截断后不再保持这条精确无偏式。若其他均值、噪声或方向未知，应重新计算带干扰参数的模型。$\square$

## 17. 同标签记录的饱和与关系阶数的资源交换

对 §15 同一个有限标签概率族，另行供应分组实验：每组抽取一个标签 $C\sim p_\theta$，条件于该标签取得 $\ell$ 份独立记录 $R_b=\varepsilon m_C+G_b$；不同组重新独立抽取标签。共同标签、条件独立制备和已知协方差都是额外实验结构，不由反复测量一个会改变的对象自动获得。

令 $\mathcal J_\ell(\varepsilon)$ 为一组关于 $\theta$ 的 Fisher 信息。使用经典的观察得分条件期望方法，即 Louis, [*Finding the Observed Information Matrix when Using the EM Algorithm*, §3](https://doi.org/10.1111/j.2517-6161.1982.tb01203.x) 的缺失信息框架：潜在得分 $S(C)=d_T(C)/p_\theta(C)$ 均值零，而实际得分是 $\mathbb E[S(C)\mid R_1,\ldots,R_\ell]$。因此在本实验中

$$
\begin{aligned}
\mathcal J_\ell(\varepsilon)
&=\operatorname{Var}(\mathbb E[S(C)\mid R_1,\ldots,R_\ell]),\\
0\le\mathcal J_1(\varepsilon)&\le\mathcal J_2(\varepsilon)\le\cdots
\le\mathcal I_T:=\sum_I\frac{d_T(I)^2}{p_\theta(I)}.
\end{aligned}
\tag{17.1}
$$

这里条件期望是同一无限条件独立记录序列中的有界 $L^2$ 鞅。样本均值几乎必然识别真实均值簇；同簇的条件记录律完全相同，后验比例始终为其原概率比例。不同簇的高斯似然比由大数律趋于零。故固定 $\varepsilon>0$ 时，若 $\mathscr G$ 是相同 $m_I$ 的标签簇，

$$
\lim_{\ell\to\infty}\mathcal J_\ell(\varepsilon)
=\sum_{G\in\mathscr G}
\frac{(\sum_{I\in G}d_T(I))^2}{\sum_{I\in G}p_\theta(I)}.
\tag{17.2}
$$

该式保留原标签概率，未把簇变为等先验标签。它说明读清一次标签的份数可以无限多，但单组信息仍至多为一次潜在标签的信息。

**定理 17.1（固定分组族内的最优记录效率）。** 固定 §15 中 $r\ge2$ 的一个未被消去的关系方向、一个全正设计参考点及所有读出参数。每份记录计费一，制备、保持标签身份、校准和计算暂不计费。令

$$
\Gamma_\varepsilon=\sup_{\ell\in\mathbb N_{\ge1}}
\frac{\mathcal J_\ell(\varepsilon)}\ell.
$$

则有有限正数

$$
M_*:=\max_{t>0}\frac{\mathcal J_1(\sqrt t)}t>0,
\qquad
\lim_{\varepsilon\to0}\frac{\Gamma_\varepsilon}{\varepsilon^2}=M_*.
\tag{17.3}
$$

每个 $\varepsilon>0$ 存在最优整数分组；所有最优选择在 $\varepsilon\to0$ 时均满足 $\ell_{\rm opt}=\Theta(\varepsilon^{-2})$。

证明。共同协方差高斯似然的经典样本均值充分性在这里给出精确缩放：将 $\ell$ 份记录正交变换为 $\sqrt\ell\,\bar R$ 和残差，残差是与标签及参数独立的标准高斯，而

$$
\sqrt\ell\,\bar R\mid C\sim\mathcal N(\sqrt\ell\,\varepsilon m_C,I_D),
\qquad
\mathcal J_\ell(\varepsilon)=\mathcal J_1(\sqrt\ell\,\varepsilon).
\tag{17.4}
$$

令 $H(t)=\mathcal J_1(\sqrt t)/t$。有限高斯混合、全正概率和（15.4）的积分主控给连续性，且

$$
H(t)=\operatorname{per}(\Gamma_T)t^{r-1}+O(t^r)\to0\quad(t\downarrow0),
\qquad 0\le H(t)\le\mathcal I_T/t\to0\quad(t\to\infty).
$$

未消去方向的密度导数在每个正信号下非零，故信息严格正。于是 $H$ 在远离两端的某个紧区间取得正最大值。由（17.4），
$\Gamma_\varepsilon=\varepsilon^2\sup_{\ell\ge1}H(\ell\varepsilon^2)$。
正网格间距趋零，连续性使网格上确界趋于 $M_*$。对每个固定网格，尾部值趋零而存在正值，故最大值由某个整数取得。两端趋零又使所有小 $\varepsilon$ 的最优网格点留在一个共同紧区间 $[c,C]\subset(0,\infty)$，从而 $c\le\ell_{\rm opt}\varepsilon^2\le C$。$\square$

对四角方向，（17.4）还给 $\ell\varepsilon^2\to0$ 时

$$
\mathcal J_\ell(\varepsilon)
=\ell^2\varepsilon^4 C_2+O(\ell^3\varepsilon^6).
$$

条件独立不等于未条件化后的独立，故不是 $\ell\mathcal J_1(\varepsilon)$。若每个新标签只取一份，单份信息为 $\Theta(\varepsilon^{2r})$；在上述分组族中适当重复同一标签、再抽新标签，最优单份效率为 $\Theta(\varepsilon^2)$。独立组之间信息相加，单组内部则遵守（17.1）的饱和。这一交换使用额外供应的共同标签结构，不能把同一批独立标签样本免费改造成同标签组。

以上是有限经典读出模型中的普通数学推导：新增内容是五模式四角核、合法关系的高斯信息系数、显式估计量及指定分组合同的组合。特征函数唯一性、有限差分、Hermite 配对、缺失信息和高斯充分统计均为成熟中间方法；未建立全局文献优先权。此处没有给出任意原生自适应策略的最优时间、在线记忆、全部物理费用或原子编码的实现，也未作 Lean 内核认证。仿射模型对五标签判别平台的限制见《五态分类决策失明》§17。

## 追加锚 2（本行以下为增补区）
