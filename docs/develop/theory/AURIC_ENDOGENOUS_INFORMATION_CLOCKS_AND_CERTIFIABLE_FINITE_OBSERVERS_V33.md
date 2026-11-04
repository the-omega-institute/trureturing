# AURIC：内生信息钟与可认证的有限观察者

从原生响应稳定性到有限停时与全未来概率保证

定义、定理与纸面证明　v33.0

2026 年 10 月 31 日　Asia/Singapore

> 编者说明：本文为作者稿的完整 Markdown 转写。数学陈述、纸面证明及有关固定快照、来源核读和项目历史的陈述均归于作者；转写不构成新增的 Lean 内核认证、原生仪器实现或物理认证。第 8 节两则明确署名的编者注仅补明所引固定来源的参数域，不替换作者原文。前篇的两个私人资料库链接按作者引文原样保留，不表示编者取得其访问权限。

## 摘要

本稿沿用单一静态整体及全部观察角色内生的解释，并继续严格区分原生矩阵、
概率响应、条件后继和实际取得成本。项目量子续卷 II 新增第 115–116 节，
给原完整响应类最优偏差的平方根首项外界；本文先从其迭代式推出一个显式的
带残差射线振荡界，再证明全输入概率校准仍不能单独决定重复仪器的长期行为。
在明确给定的双扇区 QND 仪器中，平方根后验杂质的期望精确等于逐层似然重叠之积。
由此定义加性内部信息钟，并证明其无界性与几乎必然极化的等价；
黄金读口的每轮增量恰为 $\log\varphi$。弱读口给出累积信息平方和判据，
而可求和平均漂移与相对信息误差趋零给出实际仪器的稳健消费者。
随后构造带尾漂移预算的有限停时证书，分别控制最终选支错误和全部未来反转。
对于 v32 中不容许全历史高精度有限记忆的正支持读口，
本文给出固定概率律下全未来成功概率至少 $1-\delta$ 的有限状态预测器，
状态数至多 $N(N+1)/2+2$，并把有限位输出、近似比较、时钟计数和安装表分别计费。
这些结果不免费供应原生编译、准备、概率标定或完整历史档案，
也不把信息钟等同于已经重建的物理固有时。

> **编者注（摘要中重叠乘积的归一化）。** 在定理 3.4 所设的内点初态、确定逐层似然及指定双扇区 QND 更新下，摘要中的重叠乘积对应按初始杂质归一化的期望：$\mathbb{E}U(q_n)/U(q_0)=R_n$。未归一化的期望包含初始因子，即 $\mathbb{E}U(q_n)=U(q_0)R_n$，如[（10）](#eq-affinityexact)所示。作者摘要原句保留。

<a id="section-1"></a>

## 1. 固定来源、继承前件与研究对象

本轮固定 `dev` 提交为

`9b2366610a50c2bf7e2b09cda7004b94224202ee`，

时间为 2026-10-31 01:15:52（新加坡）。
比较基线为 v32 的

`d81fb8920f72f3d5f46221f6655627e7df791d3f`。

本轮相关理论新增为量子续卷 II §§115–116、Typed cocycle §25、
Periodic clock §§28–29 和 Actual cut continuation §§37–39。
量子新增是响应稳定性的数学结果，没有新增任意输入的实际重复仪器取得。
Output-resolved instrument closure、History records time arrow 及
$\Omega$ 静态兼容主源在这次比较中未变。[head](#ref-head) [quantum](#ref-quantum) [typed](#ref-typed) [cut](#ref-cut) [clock](#ref-clock)

D5 确有变化；其中新增 HigherOrderEPRTightness 处理有限占据支持的高阶 EPR
近似，不供应本文原生读口的准备与更新接口。
新入库的 v31 作者稿亦明确区分转写与独立认证。
本稿不把这两种入库动作作为新量子仪器证明；未运行 Lean、CAS、
数学数值程序或门字枚举。[epr](#ref-epr) [archived](#ref-archived)

整体仍取固定正归一态 $(\mathcal{A},\omega)$。
所有系统、记录、辅助坐标和程序均为整体内部的角色；
张量表示用于区分内部接口，不引入本体之外的环境。
正质量历史的条件读出为

$$
\omega_h(A)=\frac{\omega(P_hAP_h)}{\omega(P_h)}.
$$

条件序列索引由内部记录细化和程序执行提供。
下文需要密度矩阵、Born 概率和 CP 更新时，均明确将它们作为已给接口；
仅凭静态整体的存在不推导这些结构。

v32 已证明：全态锐投影平均守恒等价于逐 Kraus 扇区保持；
可求和平均漂移加渐近统一信息性推出后验极化；
理想单侧黄金读口具有尖锐的有限精度预测状态数，
而在其非退化模型 $0<s<x$、$0<q_0<1$ 中，
阈值 $(x-s)/2$ 以下的全历史有限状态预测不可能。
本轮推进两点：把信息增益变成可计算的内部钟；
把全历史不可能性与固定概率律下的可靠有限观察者严格接合。[v32](#ref-v32)

<a id="section-2"></a>

## 2. 项目新稳定界的消费者及其仪器边界

记

$$
x=\frac{\sqrt5-1}{2},\quad \varphi=x^{-1},\quad
 \zeta=e^{3\pi i/5},\quad \sigma=x^2,\quad
 \kappa_0=\frac{|1-\zeta^3|}{2}.
$$

射线空间为 $X=\mathbb P(\mathbb C^{13})$，距离
$d([a],[b])=\sqrt{1-|\langle a,b\rangle|^2}$。
对实连续射线函数 $f$，令

$$
\rho(f)=\sup_{\Pi,\psi}
 \left|f(J_\Pi^3\psi)+\sigma f(J_\Pi\psi)
       -f(\psi)-\sigma f(J_\Pi^2\psi)\right|,
 \quad J_\Pi=I+(\zeta-1)\Pi,
$$

其中 $\Pi$ 遍历数学上的秩五正交投影。
源命题 115.2 证明：若 $d(A,B)\le\kappa_0\sigma^{m-1}$，则

<a id="eq-sourceosc"></a>

$$
|f(A)-f(B)|
 \le \rho(f)\frac{1-\sigma^m}{1-\sigma}
       +2\|f\|_\infty\sigma^m.                         \tag{1}
$$

这些数学共轭由原密度与每个固定响应的连续性延拓，不是新增执行菜单。[quantum](#ref-quantum)

<a id="statement-2-1"></a>

### 推论 2.1（带残差的显式射线振荡界）

对全部 $A,B\in X$，

<a id="eq-modulus"></a>

$$
\boxed{|f(A)-f(B)|
 \le\varphi\rho(f)+\frac{2\|f\|_\infty}{\kappa_0}d(A,B).}
                                                               \tag{2}
$$

特别地，对原概率响应坐标 $F_w$，

<a id="eq-probmod"></a>

$$
|F_w(A)-F_w(B)|\le\varphi\mathcal R(F)+2d(A,B)/\kappa_0.
                                                               \tag{3}
$$

<a id="proof-1"></a>

**证明。** 
距离零时显然。若 $0<d\le\kappa_0$，取满足
$d\le\kappa_0\sigma^{m-1}$ 的最大整数 $m\ge1$。
最大性给 $\kappa_0\sigma^m<d$。
在 [（1）](#eq-sourceosc) 中用 $(1-\sigma)^{-1}=\varphi$ 即得。
若 $d>\kappa_0$，平凡界 $2\|f\|_\infty$ 已小于第二项。
概率坐标有 $\|F_w\|_\infty\le1$，源合同给
$\rho(F_w)\le\mathcal R(F)$，故得到第二式。

∎

固定正残差时，该界含不可删除的加性地板；
它没有给整个未知函数类一个趋于零的共同连续模。
其全域残差前件亦不能由有限抽样自动取得。

源定理 116.1 进一步给原完整响应类的最优偏差

<a id="eq-sourceasym"></a>

$$
1\le\liminf_{\varepsilon\downarrow0}\frac{M(\varepsilon)}{\sqrt\varepsilon}
 \le\limsup_{\varepsilon\downarrow0}\frac{M(\varepsilon)}{\sqrt\varepsilon}
 \le\sqrt\varphi.                                               \tag{4}
$$

该类保留全部十三维输入、七门、全正向有限字、1024 标签、全状态非负归一连续性、
同射线终端充分性和完整基底标定。
式 [（4）](#eq-sourceasym) 是渐近夹界；不宣称极限存在、锐常数为 $\sqrt\varphi$，
也不等于一个已经给出全小尺度阈值的逐点有限误差公式。[quantum](#ref-quantum)

<a id="statement-2-2"></a>

### 命题 2.2（全输入单轮概率校准不决定重复后继）

即使两个完整 CP 仪器对全部输入有完全相同的单轮结果概率，
其重复条件后继仍可一个极化、另一个几乎必然不收敛。

<a id="proof-2"></a>

**证明。** 
在共同载体上取非平凡投影 $P$、$E=I-P$，
以及单位向量 ${\lvert e\rangle}\in E\mathcal{H}$、${\lvert p\rangle}\in P\mathcal{H}$。
理想黄金仪器为

<a id="eq-gold"></a>

$$
M_0=\sqrt x E,\qquad M_1=xE+\zeta^{-3}P.
                                                               \tag{5}
$$

另定义完整的测量后制备仪器

$$
\widetilde{\mathcal I}_0(\rho)=\operatorname{Tr}(xE\rho){\lvert p\rangle}{\langle p\rvert},\qquad
 \widetilde{\mathcal I}_1(\rho)=\operatorname{Tr}((x^2E+P)\rho){\lvert e\rangle}{\langle e\rvert}.
$$

两者的效果均是 $xE$ 与 $x^2E+P$，故全部输入概率一致。
理想仪器的极化已由 v32 的直接乘积公式证明。
替代仪器则在结果零后令 $q=1$，结果一后令 $q=0$。
从 $q=1$ 下一步必到 $0$；从 $q=0$ 每步以概率 $x>0$ 到 $1$。
每次处于 $0$ 后永久不离开的条件概率为
$\lim_m(1-x)^m=0$。因此两端点几乎必然出现无穷多次，$q_n$ 不收敛。

∎

本命题是单轮概率信息与仪器信息的逻辑分离；
它不保持任意接续后的完整终端响应或多轮联合记录律，
也不声称替代仪器已由原生门实现。
要消费后文长期定理，仍需完整后继、结果保留、失败处理及重复准备。

<a id="section-3"></a>

## 3. 双扇区信息钟：黄金读口的精确累计信息

<a id="statement-3-1"></a>

### 定义 3.1（给定的标量双扇区 QND 接口）

在同一有限维内部接口固定非平凡投影 $P$ 和 $E=I-P$。
第 $n$ 层有有限结果集 $Y_n$、两组概率 $a_{n,y},b_{n,y}$，以及相位 $\theta_{n,y}$。
给定完整仪器

<a id="eq-qnd"></a>

$$
M_{n,y}=\sqrt{a_{n,y}}E
       +e^{i\theta_{n,y}}\sqrt{b_{n,y}}P,\qquad
 \sum_ya_{n,y}=\sum_yb_{n,y}=1.
                                                               \tag{6}
$$

全部结果坐标保留；失败若存在，须在该完整接口内表示。
本文将这一更新作为前件，不从标量响应律单独导出。

记实际条件态为 $\rho_n$，$q_n=\operatorname{Tr}(P\rho_n)$，并令

$$
U(q)=\sqrt{q(1-q)},\qquad
 r_n=\sum_y\sqrt{a_{n,y}b_{n,y}}\in[0,1].
$$

结果概率与后验为

<a id="eq-bayes"></a>

$$
\pi_{n,y}=(1-q_n)a_{n,y}+q_nb_{n,y},\qquad
 q_{n+1}=\frac{q_nb_{n,y}}{\pi_{n,y}}.                           \tag{7}
$$

零质量结果不参与条件期望。这是指定读口的量子条件权重恒等式；
不要求全部不相容读口具有共同经典值。

<a id="statement-3-2"></a>

### 引理 3.2（平方根杂质的精确一步律）

对给定当前历史，

<a id="eq-affinitystep"></a>

$$
\mathbb{E}[q_{n+1}\mid\mathcal F_n]=q_n,\qquad
 \boxed{\mathbb{E}[U(q_{n+1})\mid\mathcal F_n]=r_nU(q_n).}
                                                               \tag{8}
$$

<a id="proof-3"></a>

**证明。** 
$PE=0$ 使交叉块对概率和指针质量的迹贡献为零，得到 [（7）](#eq-bayes)。
后验乘结果概率后求和给均值守恒。另一方面，逐结果有

$$
\pi_{n,y}U(q_{n+1})
 =\sqrt{q_n(1-q_n)}\sqrt{a_{n,y}b_{n,y}}.
$$

求和即得。端点或零概率项按零延拓成立。

∎

<a id="statement-3-3"></a>

### 定义 3.3（内部信息钟）

在确定的逐层似然序列下，置

<a id="eq-clock"></a>

$$
R_n=\prod_{j<n}r_j,\qquad
 \mathcal T_n=-\log R_n=\sum_{j<n}-\log r_j,
                                                               \tag{9}
$$

取 $-\log0=\infty$。先将 $R_n$ 视为两扇区记录律的剩余重叠，
对数只是把乘法组合转成加法的刻度。

这一刻度量化可辨别性，不等于 Shannon 熵、已保存的位数或执行费用。
一次完全分离的有限读出即可使它取无穷，表示重叠为零，而非使用了无穷物理时间。

<a id="statement-3-4"></a>

### 定理 3.4（信息钟与极化的精确等价）

<a id="thm-information"></a>

设 $0<q_0<1$，逐层似然确定，并采用 [（6）](#eq-qnd)。
则

<a id="eq-affinityexact"></a>

$$
\boxed{\mathbb{E} U(q_n)=U(q_0)R_n=U(q_0)e^{-\mathcal T_n}.}
                                                               \tag{10}
$$

而且

<a id="eq-clockiff"></a>

$$
\boxed{
 q_n\longrightarrow q_\infty\in\{0,1\}\ {\rm a.s.}
 \quad\Longleftrightarrow\quad R_n\to0
 \quad\Longleftrightarrow\quad\mathcal T_n\to\infty.}
                                                               \tag{11}
$$

成立时 $\mathbb{P}(q_\infty=1)=q_0$。
若 $R_\infty>0$，则内点极限具有正概率，不能宣称几乎必然选支。

<a id="proof-4"></a>

**证明。** 
迭代 [（8）](#eq-affinitystep) 得 [（10）](#eq-affinityexact)。
有界鞅 $q_n$ 几乎必然及 $L^1$ 收敛到 $q_\infty$。
$U$ 连续且有界，所以
$\mathbb{E} U(q_\infty)=U(q_0)R_\infty$。
因 $U(q_0)>0$ 且 $U(q)=0$ 恰当 $q\in\{0,1\}$，
该期望为零等价于二值极限几乎必然成立。
均值守恒和有界收敛给选择概率。若期望严格正，$U(q_\infty)>0$ 的事件有正概率。

∎

<a id="statement-3-5"></a>

### 推论 3.5（黄金每轮的信息增量）

对 [（5）](#eq-gold)，两似然为 $(x,x^2)$ 与 $(0,1)$，
所以 $r=x$，并有

<a id="eq-goldclock"></a>

$$
\boxed{\mathcal T_n=n\log\varphi,\qquad
 \mathbb{E} U(q_n)=U(q_0)x^n.}                                         \tag{12}
$$

<a id="proof-5"></a>

**证明。** 
重叠为 $\sqrt{x\cdot0}+\sqrt{x^2\cdot1}=x$，代入前一定理。

∎

这里的增量按一次完整读出协议计量，不等于一次原生门调用的成本。
信息钟依赖已指定的扇区、似然与记录合同，尚未被证明是物理固有时。

<a id="statement-3-6"></a>

### 命题 3.6（连续单调的加性刻度）

若 $t:(0,1]\to[0,\infty)$ 连续，满足
$t(r_1r_2)=t(r_1)+t(r_2)$，则 $t(r)=c(-\log r)$，$c\ge0$。

<a id="proof-6"></a>

**证明。** 
置 $f(u)=t(e^{-u})$，$u\ge0$。
它连续且满足加法关系。整数与有理数的关系先给 $f(u)=uf(1)$，
再由连续性推广到全部非负实数。

∎

这只刻画所选重叠组合律的刻度；不从中推出空间维度、钟同步或引力方程。

<a id="statement-3-7"></a>

### 命题 3.7（信息获得与平均退相干的关系）

在 [（6）](#eq-qnd) 下，非选择通道的跨扇区块乘以

$$
c_n=\sum_y\sqrt{a_{n,y}b_{n,y}}e^{-i\theta_{n,y}},
 \qquad |c_n|\le r_n.
$$

所以 $R_n\to0$ 足以使跨块消失；逆向不成立。

<a id="proof-7"></a>

**证明。** 
逐 Kraus 直接计算 $E\Phi_n(\rho)P=c_nE\rho P$，三角不等式给界。
逆向反例取 $M_0=I/\sqrt2$、$M_1=(E-P)/\sqrt2$。
两扇区似然相同，$r=1$，实际记录不改变 $q$；
但 $c=0$，平均跨块一步消失。
黄金读口则有 $c=x\zeta^3$，恰满足 $|c|=r=x$。

∎

<a id="section-4"></a>

## 4. 弱读口、累计信息及实际误差的消费者

<a id="statement-4-1"></a>

### 定理 4.1（弱对称读口的平方和判据）

取确定的 $0\le g_n<1$，两扇区结果零的似然分别为
$(1-g_n)/2$ 和 $(1+g_n)/2$。若 $0<q_0<1$，则

<a id="eq-weakcriterion"></a>

$$
r_n=\sqrt{1-g_n^2},\qquad
 \boxed{\text{几乎必然极化}\iff\sum_ng_n^2=\infty.}
                                                               \tag{13}
$$

若另允许某一步 $g_n=1$，则该步已经精确区分扇区，须作为额外的成功情形。

<a id="proof-8"></a>

**证明。** 
两个交叉平方根相同，求和给 $r_n$。
由定理 [3.4](#thm-information)，问题等价于
$\sum_n-\log(1-g_n^2)=\infty$。
对 $0\le u<1$ 有 $-\log(1-u)\ge u$；
若 $\sum g_n^2<\infty$，则最终 $g_n^2\le1/2$，
此时 $-\log(1-g_n^2)\le2g_n^2$，故对数和亦有限。
若某步为一，重叠立即为零。

∎

因此，无穷门层数本身不保证无穷可辨别信息。
例如 $g_n=1/(n+2)$ 的信息总量有限；
$g_n=1/\sqrt{n+2}$ 的信息总量无界。这些是级数的纸面比较。

<a id="statement-4-2"></a>

### 命题 4.2（历史自适应读口的充分条件）

在 [（6）](#eq-qnd) 中容许似然随已得历史变化，令 $r_n$ 为其可预测重叠。
若沿实际路径 $\sum_n(1-r_n)=\infty$ 几乎必然，则 $q_n$ 几乎必然极化。

<a id="proof-9"></a>

**证明。** 
一步恒等式给

$$
\mathbb{E}\sum_{j<n}(1-r_j)U(q_j)
 =U(q_0)-\mathbb{E} U(q_n)\le U(q_0).
$$

因此正项级数几乎必然有限。
有界鞅 $q_n$ 收敛；若其极限在内部，则 $U(q_n)$ 最终有正下界，
与假设的发散矛盾。

∎

这里没有把随机的重叠乘积移出期望，也不声称确定序列的双向等价原样适用于任意反馈模型。

<a id="statement-4-3"></a>

### 定义 4.3（实际漂移与可变信息比较）

对实际条件权重 $q_n$，取确定 $d_n\ge0$，使

$$
|\mathbb{E}(q_{n+1}\mid\mathcal F_n)-q_n|\le d_n,\qquad
 D_*=\sum_nd_n<\infty.
$$

在每个实际输入上给平均保 $P$ 的完整参考仪器，
其后验条件方差至少为
$\kappa_n[q_n(1-q_n)]^2$，其中 $\kappa_n>0$ 可预测。
实际与参考的完整旗标半迹距离至多 $e_n$。

<a id="statement-4-4"></a>

### 定理 4.4（累计信息与相对仪器误差）

<a id="thm-variableinfo"></a>

若在上述条件下

$$
\sum_n\kappa_n=\infty,\qquad e_n/\kappa_n\to0
 \quad\text{几乎必然},
$$

则 $q_n\to q_\infty\in\{0,1\}$ 几乎必然及 $L^1$，且

<a id="eq-actualpolar"></a>

$$
|\mathbb{P}(q_\infty=1)-q_0|\le D_*.
                                                               \tag{14}
$$

不要求 $d_n/\kappa_n\to0$，也不要求 $\sum_ne_n<\infty$。

<a id="proof-10"></a>

**证明。** 
记 $b_n=\mathbb{E}(q_{n+1}\mid\mathcal F_n)-q_n$，
$q_n-\sum_{j<n}b_j$ 是有界鞅，所以 $q_n$ 收敛。
写 $V(q)=q(1-q)$ 和 $A_n=\operatorname{Var}(q_{n+1}\mid\mathcal F_n)$。
完整旗标后验杂质对半迹距离为 1-Lipschitz：
对未归一输出 $\tau$，令 $a=\operatorname{Tr}(P\tau),p=\operatorname{Tr}\tau$，

$$
a-a^2/p
 =\min_{0\le z\le1}\operatorname{Tr}[((1-2z)P+z^2I)\tau],
$$

其中效果特征值为 $(1-z)^2,z^2\in[0,1]$；
当 $p=0$ 时左侧按零延拓。
在归一的结果直和上取各块最小值便给所述 Lipschitz 性。
由参考信息增益以及 $V$ 的 1-Lipschitz 性，

$$
A_n\ge\kappa_nV(q_n)^2-e_n-d_n,\qquad
 \mathbb{E}\sum_nA_n\le V(q_0)+D_*.
$$

若极限在内部，则最终 $V(q_n)^2\ge c>0$。
相对误差趋零给 $A_n\ge(c/2)\kappa_n-d_n$，求和与条件方差总和有限矛盾。
有界收敛与漂移求和给 [（14）](#eq-actualpolar)。

∎

这是 v32 统一正信息隙消费者的加强。
对各层均有 $g_n>0$ 的精确对称弱读口可取 $\kappa_n=4g_n^2$；
对一般原生近似，守恒缺陷与完整仪器距离仍须各自取得，
不能从概率响应界 [（4）](#eq-sourceasym) 直接替换。

<a id="section-5"></a>

## 5. 有限停时证书：内部何时可以可靠地宣布一个分支

<a id="statement-5-1"></a>

### 定义 5.1（尾漂移预算与出证过程）

取 $q_n\in[0,1]$，适应于内部记录过滤，并给定确定的非负包络 $d_n$，使

$$
|\mathbb{E}(q_{n+1}\mid\mathcal F_n)-q_n|\le d_n,\qquad
 D_n=\sum_{j\ge n}d_j<\infty.
$$

假设另由前述信息条件取得
$q_n\to B\in\{0,1\}$ 几乎必然。
检查器的停时表示首次保留一个证书，不改变其所检查的既定后续仪器序列。

<a id="statement-5-2"></a>

### 引理 5.2（两个超鞅与极限分支的条件概率）

<a id="lem-tail"></a>

过程 $q_n+D_n$ 与 $1-q_n+D_n$ 均为非负超鞅。
对任意几乎必然有限的停时 $\tau$，

<a id="eq-tailposterior"></a>

$$
\boxed{|\mathbb{P}(B=1\mid\mathcal F_\tau)-q_\tau|\le D_\tau.}
                                                               \tag{15}
$$

<a id="proof-11"></a>

**证明。** 
记条件漂移 $b_n$，有 $|b_n|\le d_n$，且 $D_{n+1}=D_n-d_n$。
因此
$\mathbb{E}(q_{n+1}+D_{n+1}\mid\mathcal F_n)\le q_n+D_n$，
另一过程同理。对确定 $n$，条件化望远镜求和并令终点趋无穷，
有界收敛与绝对漂移预算给

$$
\mathbb{E}(B\mid\mathcal F_n)-q_n
 =\sum_{j\ge n}\mathbb{E}(b_j\mid\mathcal F_n),
$$

绝对值至多 $D_n$。
在每个 $\{\tau=n\}$ 上应用该条件式再拼合，得到停时结论。

∎

<a id="statement-5-3"></a>

### 定理 5.3（选支与全未来反转的不同风险）

<a id="thm-certificate"></a>

任取几乎必然有限的停时 $\tau$ 及 $\mathcal F_\tau$ 可测的证书
$C_\tau\in\{0,1\}$。令

$$
R_\tau=(1-C_\tau)(q_\tau+D_\tau)
             +C_\tau(1-q_\tau+D_\tau).
$$

则

<a id="eq-certwrong"></a>

$$
\boxed{\mathbb{P}(B\ne C_\tau\mid\mathcal F_\tau)
       \le \min(1,R_\tau),}
                                                               \tag{16}
$$

并对任意 $0<r\le1$ 有

<a id="eq-anytime"></a>

$$
\boxed{\mathbb{P}\!\left(
       \sup_{m\ge\tau}|q_m-C_\tau|\ge r\mid\mathcal F_\tau
       \right)\le\min(1,R_\tau/r).}
                                                               \tag{17}
$$

<a id="proof-12"></a>

**证明。** 
第一式由引理 [5.2](#lem-tail) 分证书为零与一两种情形得到。
若证书为零，则 $q_m\ge r$ 蕴含 $q_m+D_m\ge r$；
非负超鞅的条件最大不等式给上界 $(q_\tau+D_\tau)/r$。
对证书为一使用 $1-q_m+D_m$。
先在有限未来区间应用，再令区间终点趋无穷；
必要时从阈值 $r-\eta$ 逼近 $r$，涵盖上确界恰为 $r$ 的情形。

∎

<a id="statement-5-4"></a>

### 推论 5.4（有认证区间的有限出证）

设内部取得有理数 $\widehat q_n$ 与有理认证半径 $\nu_n\to0$，满足
$|\widehat q_n-q_n|\le\nu_n$；另给可计算的有理尾上界
$\overline D_n\ge D_n$，$\overline D_n\to0$。
各层认证数据只依赖已得记录，均为 $\mathcal F_n$ 可测。
固定有理数 $0<\alpha<1/2$，在首个满足下列任一条件的层出证：

$$
\widehat q_n+\nu_n+\overline D_n\le\alpha\quad\Rightarrow\quad C_n=0,
$$

<a id="eq-stop"></a>

$$
1-\widehat q_n+\nu_n+\overline D_n\le\alpha\quad\Rightarrow\quad C_n=1.
                                                               \tag{18}
$$

该停时几乎必然有限，且出证时的条件最终误判概率至多 $\alpha$。
未来权重越过相反半区的条件概率至多 $2\alpha$；
以后出现一个相反的 $\alpha$ 证书的条件概率至多 $\alpha/(1-\alpha)$。

<a id="proof-13"></a>

**证明。** 
$q_n\to B$、$\nu_n\to0$、$\overline D_n\to0$，所以对应端点的不等式最终成立。
两证书条件互斥，并且均推出 $R_\tau\le\alpha$。
应用 [（16）](#eq-certwrong) 与 [（17）](#eq-anytime)，分别取 $r=1/2$ 和
$r=1-\alpha$。相反证书必使真实权重到达后一阈值，故得到末界。

∎

数学上的 $\sum d_n<\infty$ 不自动供应可计算的尾模量。
推论使用有理上界和有理比较，避免将任意实数的精确比较设为内部原语；
这个尾上界的取得仍须另行证明。
同样，$\widehat q_n$ 的正确区间来自已取得参数、过滤器和误差传播，
不能仅由一个实现记录宣布为精确概率。
以上反转界控制累计后验或其解码证书，不控制原始噪声结果逐次相同。
出证后若真正改变或停止量子读出，须重新定义后续完整过程与尾预算。

<a id="statement-5-5"></a>

### 命题 5.5（零错误确认与允许风险的区别）

采用式 [（6）](#eq-qnd) 的固定精确 QND 更新，其正支持读口为
$\ell_E=(x,x^2)$、$\ell_P=(s,1-s)$，其中 $0<s<x$、$0<q_0<1$，
任何几乎必然有限的、仅使用该记录的出证器，其最终误判概率都严格正。
但任意 $0<\alpha<1/2$ 的数学阈值停时证书均存在。
将其实现成式 [（18）](#eq-stop) 的内部有理程序，还须取得该式要求的认证数据。

<a id="proof-14"></a>

**证明。** 
每条有限历史在两个扇区下均有正质量，所以 $0<q_n<1$。
固定信息性给 $q_n=\mathbb{P}(B=1\mid\mathcal F_n)$。
在有限停时上仍严格位于内部；无论选择哪个证书，条件错误概率严格正，
故其期望严格正。允许 $\alpha>0$ 时，精确权重的双阈值停时及极化给数学存在性；
认证数据可得时，再应用前一推论给内部实现。

∎

<a id="statement-5-6"></a>

### 推论 5.6（固定读口的等待尾与理想黄金的确定上界）

对 $0<q_0<1$、固定重叠 $0<r<1$ 的精确 QND 读口，令
$\tau_\alpha=\inf\{n:\min(q_n,1-q_n)\le\alpha\}$，
$C_0=\sqrt{q_0(1-q_0)}$，则

<a id="eq-stoptail"></a>

$$
\mathbb{P}(\tau_\alpha>n)
 \le\min\left\{1,\frac{C_0r^n}{\sqrt{\alpha(1-\alpha)}}\right\}.
                                                               \tag{19}
$$

若 $N_\alpha$ 使分式不超过一，则
$\mathbb{E}\tau_\alpha\le N_\alpha+(1-r)^{-1}$。
理想黄金读口更有确定上界

<a id="eq-goldstop"></a>

$$
\tau_\alpha\le
 \max\left\{0,\left\lceil
 \frac{\log\!\bigl((1-q_0)(1-\alpha)/(\alpha q_0)\bigr)}
 {2\log\varphi}\right\rceil\right\}.                            \tag{20}
$$

<a id="proof-15"></a>

**证明。** 
若尚未停止，则当前 $U(q_n)>\sqrt{\alpha(1-\alpha)}$。
Markov 不等式与 [（10）](#eq-affinityexact) 给尾界，尾和给期望界。
理想黄金中，任何零结果立即确认 $E$；否则全一后验为
$q_0/[q_0+(1-q_0)x^{2n}]$，解其不小于 $1-\alpha$ 即得确定上界。

∎

<a id="section-6"></a>

## 6. 正支持读口的全未来高概率有限状态预测

v32 的全历史结论是：对正支持读口，任何固定确定有限状态预测器的
最小可达统一误差阈值为 $(x-s)/2$。本节改用一个明确的概率合同，
保留同一读口、同一初态与全部未来时刻。

<a id="statement-6-1"></a>

### 定义 6.1（固定概率律下的全未来保证）

固定 $0<s<x$、$0<q_0<1$，采用

<a id="eq-positive"></a>

$$
M_0^{(s)}=\sqrt x E+\sqrt s P,\qquad
 M_1^{(s)}=xE+\sqrt{1-s}\,\zeta^{-3}P.
                                                               \tag{21}
$$

记 $g=x-s>0$、$p_n=x-gq_n$，它是下一次零的真实条件概率。
有限确定性预测器使用完整状态集 $S$、固定初始化、总更新及概率输出。
目标是

<a id="eq-pac"></a>

$$
\boxed{\mathbb{P}_{q_0,s}\left\{
       \sup_{n\ge0}|\widehat p_n-p_n|\le\epsilon
       \right\}\ge1-\delta,}
 \quad 0<\epsilon<g/2,\quad 0<\delta<1.                        \tag{22}
$$

所有深度、计数和持续控制相位均计入 $S$，没有免费时钟。
概率始终属于这一个固定初始记录律。

定义

<a id="eq-rpositive"></a>

$$
C_0=\sqrt{q_0(1-q_0)},\qquad
 r=\sqrt{xs}+x\sqrt{1-s}.
                                                               \tag{23}
$$

两个平方根似然向量均为单位向量，且因 $s\ne x$ 不相同，所以 $0<r<1$。
定理 [3.4](#thm-information) 给
$\mathbb{E}\sqrt{q_n(1-q_n)}=C_0r^n$。

<a id="statement-6-2"></a>

### 引理 6.2（固定深度后选择预测端点的风险）

<a id="lem-freezerisk"></a>

在深度 $N$ 选择一个 $\mathcal F_N$-可测端点 $C_N\in\{0,1\}$，令
$a_N=(1-C_N)q_N+C_N(1-q_N)$。
对 $b>0$，事件
$\{\sup_{n\ge N}[(1-C_N)q_n+C_N(1-q_n)]>b\}$
的条件概率至多 $\min(a_N/b,1)$；该事件包括冻结当刻。
若按后验较大的扇区精确选择端点，则 $a_N=m_N:=\min(q_N,1-q_N)$，
并对 $0<b\le1/2$ 有

<a id="eq-freezerisk"></a>

$$
\boxed{\mathbb{P}(\text{某个未来时刻离所选端点超过 }b)
       \le\frac{C_0r^N}{\sqrt{b(1-b)}}.}                       \tag{24}
$$

<a id="proof-16"></a>

**证明。** 
对 $q_n$ 或 $1-q_n$ 应用非负鞅最大不等式，得到条件界。
当 $0\le m\le1/2$，

$$
\min(m/b,1)\le
 \frac{\sqrt{m(1-m)}}{\sqrt{b(1-b)}}.
$$

若 $m\le b$，平方后等价于 $m\le b$；若 $m\ge b$，
则 $m(1-m)\ge b(1-b)$。
取期望并使用精确杂质律即得。

∎

<a id="statement-6-3"></a>

### 引理 6.3（有限精度端点判定）

若使用 $|\widetilde q_N-q_N|\le\xi$ 的有理近似，
按 $\widetilde q_N\le1/2$ 选择零端点，否则选择一端点，则

$$
a_N\le m_N+2\xi,
$$

因而 [（24）](#eq-freezerisk) 的右侧只需增加 $2\xi/b$。

<a id="proof-17"></a>

**证明。** 
选对较大后验扇区时 $a_N=m_N$。
选错时，真实 $q_N$ 距 $1/2$ 至多 $\xi$，
故错误扇区质量比 $m_N$ 多至多 $2\xi$。
函数 $\min(u/b,1)$ 为 $1/b$-Lipschitz，代入前一引理即可。

∎

<a id="statement-6-4"></a>

### 定理 6.4（显式有限表预测器）

<a id="thm-finitepac"></a>

假设 $q_0,s$ 是已经合法取得并给出算法的可计算常数，
$\epsilon,\delta$ 为给定正有理精度。置

$$
b=\frac{\epsilon}{2g},\qquad
 \xi=\frac{\delta b}{4},
$$

并取整数 $N\ge0$ 使

<a id="eq-Ncondition"></a>

$$
\frac{C_0r^N}{\sqrt{b(1-b)}}\le\delta/2.
                                                               \tag{25}
$$

则存在所有输出均为有限二进制有理数的确定预测器，满足 [（22）](#eq-pac)，且

<a id="eq-stateupper"></a>

$$
\boxed{|S|\le\frac{N(N+1)}2+2.}                               \tag{26}
$$

一个数学上的充分阈值为

<a id="eq-Nstar"></a>

$$
N_*=\max\left\{0,\left\lceil
 \frac{\log\!\bigl(2C_0/(\delta\sqrt{b(1-b)})\bigr)}
      {\log(1/r)}\right\rceil\right\}.                         \tag{27}
$$

式 [（26）](#eq-stateupper) 是构造上界，不宣称状态数最优。

<a id="proof-18"></a>

**证明。** 
瞬态状态为 $(n,k)$，$0\le n<N$、$0\le k\le n$，
其中 $k$ 是已经见到的零的个数。另有两个吸收状态 $A_E,A_P$。
在该计数状态，后验为

<a id="eq-countposterior"></a>

$$
q_{n,k}
 =\frac{q_0s^k(1-s)^{n-k}}
 {(1-q_0)x^{2n-k}+q_0s^k(1-s)^{n-k}},
 \qquad p_{n,k}=x-gq_{n,k}.                                   \tag{28}
$$

预先将每个 $p_{n,k}$ 计算为误差不超过 $\epsilon/2$ 的有限有理输出。
读入结果时递增 $n$，零时再递增 $k$。
到达深度 $N$，使用误差至多 $\xi$ 的有理 $\widetilde q_{N,k}$ 选择
$A_E$ 或 $A_P$。这两个状态在两种输入下都保持。
分别输出 $x$ 与 $s$ 的有限有理近似，误差亦不超过 $\epsilon/2$。
$N=0$ 时直接安装相应初始吸收状态。

深度 $n<N$ 的预测确定满足误差界。
进入 $A_E$ 后，只要全部未来 $q_n\le b$，就有

$$
|\widehat p_n-p_n|
 \le|\widehat x-x|+gq_n\le\epsilon/2+gb=\epsilon.
$$

进入 $A_P$ 同理。前两个引理给全部未来失败概率至多

$$
\frac{C_0r^N}{\sqrt{b(1-b)}}+\frac{2\xi}{b}
 \le\delta/2+\delta/2=\delta.
$$

瞬态状态数为 $\sum_{n=0}^{N-1}(n+1)=N(N+1)/2$，
加两个吸收状态即得所列上界。

∎

<a id="statement-6-5"></a>

### 命题 6.5（有限编译无需精确实数相等判定）

在定理 [6.4](#thm-finitepac) 的参数合同下，可以可计算地取得满足
[（25）](#eq-Ncondition) 严格版本的 $N\le N_*+1$，
并构造上述有限有理表，不需要决定某个真实 $q_{N,k}$ 是否恰为 $1/2$。

<a id="proof-19"></a>

**证明。** 
令 [（27）](#eq-Nstar) 的未取整对数商为 $A$。
计算有理上界 $U$，使 $A\le U<A+1/2$，再取
$N=\max(0,\lfloor U\rfloor+1)$。
它严格大于 $A$，并至多为 $N_*+1$。
因 $r<1$、$q_0,s$ 严格处于声明区间，相关对数与除法在该给定表示下可计算。
若用逐候选搜索，须并行细化其严格证书，不能在恰等号的一个候选上永久等待。

所有深度不超过 $N$ 的后验分母都严格正，因此可以计算到要求精度。
也可使用

$$
\log\frac{q_{n,k}}{1-q_{n,k}}
 =\log\frac{q_0}{1-q_0}
   +k\log\frac{s}{x}
   +(n-k)\log\frac{1-s}{x^2}.
$$

logistic 函数导数至多 $1/4$，所以给定对数项的有限精度足以供应后验区间。
端点选择只比较有理 $\widetilde q_{N,k}$ 与 $1/2$；相等时固定选一侧即可。

∎

该证明给有限算法存在性；时间仍依赖参数表示的实际计算复杂度，
没有得到统一多项式原生编译器。

<a id="statement-6-6"></a>

### 命题 6.6（活动状态与完整安装表的不同位成本）

取 $B_{\rm out}=\lceil\log_2(2/\epsilon)\rceil$，
可把每个概率输出写成分母为 $2^{B_{\rm out}}$ 的有理数，
每项使用 $B_{\rm out}+1$ 位。
若完整状态数为 $M$，$L=\lceil\log_2M\rceil$，
直接安装表的描述成本至多

<a id="eq-tablebits"></a>

$$
2ML+M(B_{\rm out}+1)+L+O(\log M+\log B_{\rm out}).              \tag{29}
$$

<a id="proof-20"></a>

**证明。** 
先把每个真实输出算到 $\epsilon/4$，将所得有理近似截断到 $[0,1]$，
再四舍五入到上述二进制网格。截断不增加误差。
网格间距至多 $\epsilon/2$，故总误差至多 $\epsilon/2$。
两个输入各需一个 $L$ 位目标状态编号，输出表每状态一项，
再加初始状态编号及尺寸编码，得到式 [（29）](#eq-tablebits)。

∎

固定 $q_0,s$ 时，

$$
N=O\!\left(\log\frac1\delta+\log\frac1\epsilon\right),\quad
 M=O\!\left(\log^2\frac1{\delta\epsilon}\right).
$$

活动状态位数为 $O(\log\log(1/(\delta\epsilon)))$，
而安装表还有式 [（29）](#eq-tablebits) 的成本。
常数包含 $1/\log(1/r)$，不对 $s\uparrow x$ 一致。
参数取得、编译、物理控制、连续记录供应与输出解码也仍另计。

<a id="section-7"></a>

## 7. 界的必要性、条件化与量词边界

<a id="statement-7-1"></a>

### 命题 7.1（固定深度冻结方案的读出下界）

在 [（21）](#eq-positive) 下，任何读到固定深度 $N$ 后永久冻结输出的方案，
若 $\epsilon<g/2$ 且满足 [（22）](#eq-pac)，则

<a id="eq-Nlower"></a>

$$
\boxed{N\ge
 \frac{[\log(C_0^2/\delta)]_+}{2\log(1/r)}.}                   \tag{30}
$$

该下界限于这一冻结架构，不是全部有限状态预测器的最小状态数定理。

<a id="proof-21"></a>

**证明。** 
对长度 $N$ 的记录 $h$，令 $A_h$、$B_h$ 为其 $E$ 与 $P$ 的带先验质量，
则 $\sum_h(A_h+B_h)=1$。
在这一个读口的记录代数上，两扇区混合表示给
$\sum_h\sqrt{A_hB_h}=C_0r^N$，
历史 $h$ 与极限 $B=0,1$ 的联合质量分别是 $A_h,B_h$。
真实下一次概率的极限分别是 $x,s$。
因两个半径 $\epsilon$ 邻域不交，冻结输出成功必须正确区分这两个极限，
失败概率至少为 Bayes 错误
$e_N=\sum_h\min(A_h,B_h)$。
Cauchy–Schwarz 给

$$
C_0r^N
 \le\sqrt{\Bigl(\sum_h\min(A_h,B_h)\Bigr)
              \Bigl(\sum_h\max(A_h,B_h)\Bigr)}
 =\sqrt{e_N(1-e_N)}.
$$

故 $e_N\ge C_0^2r^{2N}$。由 $e_N\le\delta$ 取对数即得。

∎

<a id="statement-7-2"></a>

### 命题 7.2（联合误差到条件误差的有限接口）

给两组归一完整 cq 状态

$$
\Omega=\bigoplus_h p_h\rho_h,\qquad
 \widetilde\Omega=\bigoplus_h\widetilde p_h\sigma_h.
$$

设 $\varepsilon=\tfrac12\|\Omega-\widetilde\Omega\|_1$，
$e_h=\tfrac12\|\rho_h-\sigma_h\|_1$。
对正质量历史有

<a id="eq-conditioning"></a>

$$
p_he_h\le\varepsilon,\qquad
 \sum_hp_he_h\le2\varepsilon,\qquad
 \mathbb{P}_{p}(e_H>\eta)\le2\varepsilon/\eta.
                                                               \tag{31}
$$

若记录边缘相同，则平均误差恰为 $\varepsilon$，末界改善为 $\varepsilon/\eta$。
在参考零质量块可任选一个条件态补全；这不把零质量条件事件变成实际参考后验。

<a id="proof-22"></a>

**证明。** 
三角不等式给

$$
p_he_h
 \le\tfrac12\|p_h\rho_h-\widetilde p_h\sigma_h\|_1
       +\tfrac12|p_h-\widetilde p_h|.
$$

补事件的全部块范数至少为 $|p_h-\widetilde p_h|$，所以固定块右侧至多
完整半迹距离 $\varepsilon$。求和的上界为
$\varepsilon+\operatorname{TV}(p,\widetilde p)\le2\varepsilon$，
Markov 不等式给坏历史概率。边缘相同时直和范数直接给等式。

∎

仅有记录概率的 TV 误差而未保留后继状态时，不能应用这一条件态结论；
第 2 节反例已经显示后继可完全不同。
式 [（31）](#eq-conditioning) 也没有免费给全部深度同时成立的界，
若要作这种升级，仍需尾预算、最大不等式或统一路径耦合。

定理 [6.4](#thm-finitepac) 与 v32 的全历史不可能性并不矛盾：
前者是在固定起始概率律下允许质量 $\delta$ 的坏路径，
后者量化每一条正概率有限历史。
若要求每个前缀之后，对包含当前时刻的全未来都有条件成功概率至少 $1-\delta$，
且 $\delta<1$，那么当前预测一旦已经错误，条件成功概率就是零；
这种要求重新迫使逐历史准确，仍受 v32 的阈值阻碍。

吸收的是预测器的控制状态，真实后验和内部读出仍可继续变化。
有限表的多对一更新不是已证明的固定有限自主酉实现；
旧记录重置与 v32 的酉复现障碍均保留。
此外，一维 $q_n$ 只足以预测本节这个固定读口；
任意相干后续门可能读取额外相位与扇区内部信息。

<a id="section-8"></a>

## 8. 项目资源接口与原生执行钟的接合

Typed cocycle 新定理 25.5 在固定二 token、单位步时、
全闭区间钟支持和最终真实源商点输入的合同下，构造 $X_N$，使

$$
C_{\rm stat}(X_N)=2,\qquad F(X_N)=N,\qquad
 C_{\rm on}(X_N)\le2N.
$$

这里 $F$ 是忠实跟踪完整源端点时的最小最大投影纤维宽度。
它不是量子维数，也不是本篇预测状态数；
其意义是静态二值充分性不能提供源无关的忠实在线宽度上界。
后一个 $2N$ 仍是上界，未证在线最小值等于它。[typed](#ref-typed)

> **编者注（Typed 25.2、25.5 的参数域）。** 所引固定来源先在定义 25.2 规定 $N$ 为整数且 $N\ge3$，定理 25.5 在同一范围内给出上述结论；本段沿用该范围。这里的 $N$ 是该来源族的索引，与第 6 节有限预测器允许取 $N\ge0$ 的预测深度不同。[typed](#ref-typed)

Actual cut 新 §§37–39 给更直接的取得边界。
在只知公开阶界 $d\ge1$、未知但固定成熟切 $n$、零源更新、
仅准付费完整根字 presence Read 的原入口上，
答案 $f(s)=U_s(2)=c(s_0)$ 只需两个保留值。
但每条确定性 total-correct 执行都必须满足

$$
M(s,n)>n/2,\qquad W(s,n)>n/2,
$$

其中 $M$ 是实际提交的最大完整字长，$W$ 是所有提交字的总长度。
若整个控制器还有统一 $M\le\kappa n+\lambda$，则

$$
Q(s,n)>
 \log_{2\kappa}\left(
 1+\frac{(2\kappa-1)n}{2(\kappa n_0(d)+\lambda)}
 \right).
$$

该价格来自特定取得入口，不能直接移作本篇 QND 读口的物理时间下界。
它严格说明：小的最终答案不能退还此前取得、安装与记录成本。[cut](#ref-cut)

> **编者注（Actual cut 38.1、38.3 的统一包络）。** 所引固定来源要求固定实常数 $\kappa\ge1$、$\lambda\ge0$，使包络对全部合资格来源 $s\in\mathscr R_d$ 和全部成熟整数切 $n\ge n_0(d)$ 同时成立。常数可依赖这个固定的公开控制器及公开阶界 $d$，但独立于实际来源、实际切和执行记录（transcript）；仅在所选实际输入上成立的字长界不足以应用该结论。[cut](#ref-cut)

若第 $j$ 次完整读口实际消耗原生字长 $L_j$，执行钟标签为

$$
G_n=\sum_{j<n}L_j.
$$

对于理想黄金读口，信息标签是 $\mathcal T_n=n\log\varphi$。
若每轮字长恰为 $L$，两标签的比为 $\log\varphi/L$；
若为提高精度而使 $L_j$ 增长，则比值须按实际字长重新核算。
信息标签、事件轮数、执行字长和已标定的物理钟是不同的内部读出合同。
这没有在整体外增添时间变量，也没有由一个信息率推出物理引力。

本轮形成了以下可复用消费者：

| 已经取得的前件 | 可以推出的结论 |
| --- | --- |
| 原全域四时残差 | 带加性残差的射线响应振荡界 |
| 完整双扇区 QND 更新 | 精确重叠乘积与信息钟极化判据 |
| 可求和漂移、发散累计信息、相对误差趋零 | 实际后验二值极限及选择质量预算 |
| 可认证后验区间和尾漂移上界 | 有限出证及全部未来反转风险界 |
| 固定正支持读口、可计算参数、给定 $\epsilon,\delta$ | 有限有理表的全未来高概率预测 |
| 实际原生调用与安装记录 | 执行、取得、保留成本的可审计计费 |

下一条原生证明义务，是在同一个实际协议中同时供应这些前件：
初态质量的合法标定、重复 ready、完整后继、守恒缺陷的可计算尾预算、
累计信息以及有限表的内部实现。单次概率函数的逼近不能替代这些联合义务。

## 固定来源与前篇

<a id="ref-head"></a>

**[head]** 
The Omega Institute, *trureturing*,
[固定 dev 提交 9b2366610a50c2bf7e2b09cda7004b94224202ee](https://github.com/the-omega-institute/trureturing/commit/9b2366610a50c2bf7e2b09cda7004b94224202ee)，
2026-10-31 01:15:52 Asia/Singapore。

<a id="ref-quantum"></a>

**[quantum]** 
项目，[《AURIC FIB ATOM 与量子基本原则：续卷 II》](https://github.com/the-omega-institute/trureturing/blob/9b2366610a50c2bf7e2b09cda7004b94224202ee/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md)，
本轮新增 §§115–116；黄金目标继承 §111。
新增证明全文读取，旧共同一阶紧性与原类合同按明示依赖消费；
未将纸面源推演宣称为新内核认证。

<a id="ref-typed"></a>

**[typed]** 
项目，[《Typed Residual Cocycle Reconstruction》](https://github.com/the-omega-institute/trureturing/blob/9b2366610a50c2bf7e2b09cda7004b94224202ee/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TYPED_RESIDUAL_COCYCLE_RECONSTRUCTION.md)，
新增 §25，尤其定义 25.1 与定理 25.5。

<a id="ref-cut"></a>

**[cut]** 
项目，[《Actual Cut Reinstatement Continuation》](https://github.com/the-omega-institute/trureturing/blob/9b2366610a50c2bf7e2b09cda7004b94224202ee/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACTUAL_CUT_REINSTATEMENT_CONTINUATION.md)，
新增 §§37–39，尤其定义 37.1、定理 38.2–38.3 和 39.1。
零源更新、完整根字请求、确定性 total correctness 及统一字长包络均保留。

<a id="ref-clock"></a>

**[clock]** 
项目，[《Periodic Clock Rigidity》](https://github.com/the-omega-institute/trureturing/blob/9b2366610a50c2bf7e2b09cda7004b94224202ee/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PERIODIC_CLOCK_RIGIDITY.md)，新增 §§28–29。
实际祖先菜单的付费核验、发现与精确保留仍采用其各自入口；
本稿没有将它们当作 QND 读口的免费概率取得。

<a id="ref-epr"></a>

**[epr]** 
项目，[HigherOrderEPRTightness](https://github.com/the-omega-institute/trureturing/blob/9b2366610a50c2bf7e2b09cda7004b94224202ee/D5/S3/Quantum/FockSpace/HigherOrderEPRTightness.lean)。
固定树中新增的高阶 EPR 文件与本文原生读口之间未给出实现接口。

<a id="ref-archived"></a>

**[archived]** 
项目，[《内生预测、非交换黄金递归与信息几何》v31 作者稿归档](https://github.com/the-omega-institute/trureturing/blob/9b2366610a50c2bf7e2b09cda7004b94224202ee/docs/develop/theory/AURIC_ENDOGENOUS_PREDICTION_NONCOMMUTING_GOLDEN_RECURSION_AND_INFORMATION_GEOMETRY_V31.md)。
按其编者声明，转写不构成新增独立认证。

<a id="ref-v32"></a>

**[v32]** 
前篇，*AURIC：原生黄金读口、内部守恒与预测记忆*，v32。
[完整 LaTeX 源稿](https://chatgpt.com/library?file_id=libfile_1ab5416dc6ac8191ba4160fa33682212&account_id=personal)；
[PDF 版](https://chatgpt.com/library?file_id=libfile_61676624ddc48191bee8f3b9f6c21975&account_id=personal)。
本篇的主要新推论在正文给出证明，不主张文献优先权。
