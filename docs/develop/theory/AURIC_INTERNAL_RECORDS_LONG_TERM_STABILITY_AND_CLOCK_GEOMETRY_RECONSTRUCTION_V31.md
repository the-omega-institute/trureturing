# AURIC：内生记录、长期稳定

## 与时钟几何重建

### 从未知记录质量到稳定读出，再到内部度规的条件恢复

**定义、定理与纸面证明 · v31.0**

2026 年 10 月 30 日 · Asia/Singapore

## 摘要

本文承接“量子关系分析”与 v30：整体仍为同一个固定代数态，
观察者、控制程序、测量、记录、环境坐标和时钟均是其内部关系。
新工作分成三个可独立核对的部分。
第一，消费项目最新未知正记录质量分类，精确计算分支响应传递的全域误差，
证明其只在已取得分类后才可由十三个基输入确定，并给出黄金记录权重的锐误差区间；
同时将原先子序列的质量收敛提升为整列收敛。
第二，对反复信息性量子读出，证明完整仪器的可求和误差足以保证实际条件态
几乎必然极化到一个指针扇区；证明采用后验杂质的变分表示，
不假设一个预存且永不改变的经典扇区。
得到中间区域的期望驻留次数、极限选择权重偏差及递归精度调度，
并给出固定误差和仅趋零误差的反例。
第三，在明确的四维方向、共同标定和二次钟律前件下，
以十种类时钟探测恢复点态 Lorentz 度规，给出误差放大和有限 tick 分辨率条件，
并证明因果锥加体积的唯一性及方向丛到切丛的必要接口。
这些是模型内的数学结论，不把静态本体、原生门密度或单个概率重构
当作完整量子仪器、四维连续时空或引力动力学的无条件起源。

# 1. 承接对象与已核对的项目增量

本轮承接的原句是：宇宙只取一个整体本体态；观察者、其思考计算、
门控制、环境、限制和纠缠都在同一结构内；观察者经验的增长由内部门历史和记录给出。
本文接受这个研究前提，不加入本体外的操作者或物理时钟。
数学上选定一个整体态，并不等于已证明局部约束只有唯一宇宙解。

前篇 v30 已包含整体态与 GNS、持久记录鞅、等距直接极限、
精确无编程、黄金参数谱、门字抵消与带记录时钟的区别、
闭路同步与 holonomy、不充分的静止钟率以及条件性引力接口。
本篇以这些为前史，主证明放在其后续缺口。[v30](#ref-v30)

本轮核对的默认分支是 `dev`，固定提交为
`bd2207586c3c64e1a4ebcfa23f53b974a2700385`
提交时间为 2026-10-30 23:41:32（新加坡）。比较基线是 v30 的
`75c5f3c4aea976b089df5070a2f9f24f2905ee3a`。
完整 theory 子树比较有八个变化路径；没有把比较接口截断的前 300 个文件当作全量。
量子续卷 II 新增 §§104--110，旧稿全部字节仍为新稿前缀；
$\Omega$相融纤维与 v21 静态历史文件在该比较中不变。
Typed cocycle 新增 §23，周期时钟新增 §27，V28 二态读出与 E8 条件桥新入库。
本篇读取当前来源并作纸面推演，未运行 Lean，未作数值门字搜索。[head](#ref-head) [quantum](#ref-quantum) [typed](#ref-typed) [clock](#ref-clock) [v28](#ref-v28)

| 已核对的新内容 | 本篇消费及边界 |
| --- | --- |
| 量子续卷 II §104 | 未知正记录质量下，旧响应成为 Born，另一分支保留$cq+d$。 |
| §§105--106 | ready 初始化付费；完整失败质量保留；有限原生取得接到条件极限。 |
| §107 | $c<1$反模型沿有限取得仍存在，黄金权重尚需分支传递。 |
| §§109--110 | 残差的平方根尺度与二阶一致非紧性，不能用一阶紧性跳过更高阶。 |
| Typed cocycle §23 | 当前读出恒定仍有$(C_{\rm stat},C_{\rm on})=(2,2^k)$的条件分离。 |

本次还存在三个 Quantum Lean 文件的变化：
`OutcomeCommunicationChainedInequality`、
`LaplacianTwoLevelTreeSharpTransferDecay` 和
`LaplacianTwoLevelTreeSpectralBound`。
本篇没有审查或重跑这些证明，不能由它们的存在声称新 §§104--110 已形式化。

# 2. 单一本体内的条件、干预与程序相干

### 定义 2.1（整体与内部观察协议）

取含单位复$C^*$代数$\mathcal{A}$及正归一态$\omega$。
全部物理角色是同一$\mathcal{A}$的元素、子代数、控制关系和记录条件。
一组内部持久记录投影满足

$$
P_h=\sum_yP_{hy},\qquad P_hP_{h'}=0\quad(|h|=|h'|,\ h\ne h'),
 \qquad \sum_{|h|=n}P_h=I.
$$

在$\omega(P_h)>0$时，相应读出为

$$
\omega_h(A)=\frac{\omega(P_hAP_h)}{\omega(P_h)}.
$$

记录深度$n$表示内部包含次序。任何物理速率必须和另一组内部校准记录比较。

### 命题 2.2（内部程序可满足后续设置独立性）

设先前记录投影$R_i$与内部程序投影$C_f$共同可读，且

$$
\omega(R_iC_f)=\omega(R_i)\omega(C_f),\qquad \omega(C_f)>0.
$$

则$\mathbb{P}(i\mid f)=\omega(R_i)$。
若以$C_f$控制的后续酉保留$R_i$，该先前记录质量不因执行哪个后续程序改变。

**证明。**

第一式由条件概率相除。若后续$U_f$与$R_i$对易，则$U_f^*R_iU_f=R_i$，故该记录的权重保持。
整个论证只使用同一个态中的交换记录和内部控制。

∎

项目称“记录之后外生选择接续”的条件，可以在闭合本体内落实为
子协议中可独立控制的程序坐标。它并不要求宇宙外的操作者。
但只说所有东西都在同一个整体中，并不证明上述独立性。
例如把未来程序复制成先前记录$f=i$，就有
$\mathbb{P}(i=0\mid f=0)=1$、$\mathbb{P}(i=0\mid f=1)=0$。
从相关总体中条件化到观察到的设置，不能替代源定理的全部干预选项。
上述命题只给固定协议的一种内部实现；要消费源合同，还须实际供应相应控制族。

### 命题 2.3（经典程序逐支相同不保证相干程序相同）

同一内部二维程序与数据上，令

$$
G=\ket0\bra0\otimes I+\ket1\bra1\otimes I,
 \qquad
 \widetilde G=\ket0\bra0\otimes I-\ket1\bra1\otimes I.
$$

每个计算基程序上，二者给完全相同的数据通道；
但对程序$\ket+=(\ket0+\ket1)/\sqrt2$，其完整输出正交。

**证明。**

两个程序块只差各自的整体相位，因此每支数据共轭通道相同。
相干输入却分别变成$\ket+\otimes\psi$与$\ket-\otimes\psi$。
二者内积为零，以程序$X$基测量即可完全区分。

∎

所以相干控制必须保留不同分支间的相位。
这正是项目 §105 不允许把受控$D$替成受控$K_0$后任意丢弃相位的原因之一。
内部化程序并不取消相干比较所需的信息。[quantum](#ref-quantum)

# 3. 项目的新概率分类：保留其完整前件

本节引用源结论，下一节另给新推论。
置
$$
x=\frac{\sqrt5-1}{2},\qquad x+x^2=1,
 \quad H=V_8^{\mathbf{1}},\quad \dim H=13.
$$

完整终端标签为$\Omega_{10}=\{0,1\}^{10}$；其中合法标签集$J$有十三项，
其余 1011 项不被删除。令$e_j$为合法基，
$$
q_j(\psi)=|\langle e_j,\psi\rangle|^2\ (j\in J),\qquad
 q_w(\psi)=0\ (w\notin J).
$$

同一扩大载体$\mathcal K=V_{12}^{\mathbf{1}}$有 89 维，
含$J_{\mathrm{emb}}(H\otimes\mathbb{C}^2)$的 26 维代码和 63 维补空间。
为避免混淆，下文用$J$表合法标签集，$J_{\rm emb}$表等距嵌入。

> 编辑说明：作者源此处的嵌入记号存在跨行笔误，以下代码块逐字保留原始两行拼写（`J_{` 后为实际换行，原始两行均无反斜杠）：

```tex
J_{
m emb}
```

> 紧接其后的作者定义明确用 `J` 表合法标签集、`J_{\rm emb}` 表等距嵌入。据此，上文的 `J_{\mathrm{emb}}` 是一处有据的局部记号修复。

<a id="eq:classification"></a>
### 定理 3.1（所消费的项目定理 104.3）

沿用源的完整七门、全部有限制备与接续、同一个固定连续相位不变扩大响应，
并满足：旧记录的 ready 锚和全部旧基底校准；实际纯分支更新与历史充分性；
全部终端标签的设置隔离；指定制备上的两记录正质量；
后续程序的干预不改变已经产生的记录质量。
则两个记录分支的终端响应$F,G$及该制备的质量满足

$$
F=q,\qquad a_0=a_1=a\in(0,x],
$$

$$
G=cq+d,\qquad c=\frac{ax}{1-a}\in(0,1],\qquad
 d_w\ge0,\quad\sum_wd_w=1-c.
 \tag{1}
$$

而且$G=F$当且仅当$a=x$，即该制备的质量为$(x,x^2)$。

该结论的证明归属源 §104。其承重关系是对全部原接续$f$的
$$
a_0F(K_f\eta)+(1-a_0)G(K_fD\eta)
 =a_1F(K_fD^4\eta)+(1-a_1)G(K_fD^3\eta).
$$

密度与连续性把它延拓到数学酉参数。
源在连续函数空间先用紧群特征积分投影到各不可约调和分量，
避免对任意$L^2$展开直接取点值。
高于一次的分量要求一个四次多项式在
$\zeta^{-2},\zeta^{-1},1,\zeta,\zeta^2$五个互异点为零，
故全部高次分量消失；旧基底校准和正性固定$F=q$，
一次分量确定相同的$a$与式 [式 eq:classification](#eq:classification)。
本文不把这一依赖链冒充从“整体唯一”独立推出的概率公理。[quantum](#ref-quantum)

源 §107 对每个$0<c<1$构造了保持其余合同的响应。
因而第二分支剩余自由是真实的数学自由，
不是可以用术语“相融”直接消去的未写步骤。
旧终端 Born 律也没有自动确定所有记录读口的概率与更新。

# 4. 新推论：分支校准的锐误差与黄金质量

### 定义 4.1（分支传递缺陷）

在已经取得式 [式 eq:classification](#eq:classification) 的模型类内，令

$$
t=1-c\in[0,1),\qquad
 \Delta=\sup_{\|\psi\|=1}\operatorname{TV}(G(\psi),F(\psi)),
 \qquad \operatorname{TV}(p,r)=\frac12\sum_w|p_w-r_w|.
$$

求和覆盖全部 1024 个标签。

<a id="thm:calibration"></a><a id="eq:delta"></a><a id="eq:sharpdelta"></a>
### 定理 4.2（十三基输入决定已分类响应的全域误差）

有精确公式与锐界

$$
\boxed{\Delta=\max_{j\in J}\operatorname{TV}(G(e_j),\delta_j)
              =t-\min_{j\in J}d_j,}
 \tag{2}
$$

$$
\boxed{\frac{12}{13}t\le\Delta\le t.}
 \tag{3}
$$

**证明。**

$q(\psi)$遍历合法十三标签的概率单纯形，因为可取$\psi=\sum_j\sqrt{p_j}e_j$实现任意概率向量$p$。
故目标为凸函数$p\mapsto\frac12\|d-tp\|_1$在该单纯形上的最大值。
任意$p=\sum_jp_j\delta_j$，凸性给该值不超过各顶点值的最大值；顶点本身可取。
在顶点$j$，用$0\le d_j\le t$和$\sum_wd_w=t$得

$$
\frac12\|d-t\delta_j\|_1
 =\frac12\left(t-d_j+\sum_{w\ne j}d_w\right)=t-d_j.
$$

这证明精确式。又合法标签上的最小$d_j$不超过$t/13$，给下界；
非负性给上界。
将全部$t$均匀分配到合法标签达到下界；
使任一合法$d_j=0$达到上界。非法标签的质量在证明中始终计入。

∎

<a id="cor:goldmass"></a><a id="eq:goldmass"></a><a id="eq:goldinterval"></a>
### 推论 4.3（黄金质量的精确缺陷和误差区间）

$$
\boxed{x-a=\frac{x^3t}{1-xt}.}
 \tag{4}
$$

令$\bar t=\min\{1,13\Delta/12\}$，则

$$
\frac{x^3\Delta}{1-x\Delta}
 \le x-a\le\frac{x^3\bar t}{1-x\bar t}.
 \tag{5}
$$

若只知$\Delta\le\delta<12/13$，特别有

$$
0\le x-a\le
 \frac{(13/12)x^3\delta}{1-(13/12)x\delta}.
$$

**证明。**

$a=c/(x+c)=(1-t)/(x+1-t)$。
利用$x+x^2=1$，整理得到式 [式 eq:goldmass](#eq:goldmass)。
函数$t\mapsto x^3t/(1-xt)$在$[0,1]$严格递增，
再用$\Delta\le t\le\bar t$即得。

∎

这里“十三个基输入足够”只发生在全域源假设已经把响应限制到$cq+d$之后。
有限个测试不能独立认证全部未知连续函数满足源假设；
尤其不能把这条结论反向用于证明密度、设置隔离或完整历史充分性。

<a id="thm:fullsequence"></a>
### 定理 4.4（项目有限取得质量的整列收敛）

在源 §106.1 的全部条件下，设$a_{ns}=m_{n,s0}(p_*,\epsilon)$。
则存在唯一$a\in(0,x]$，使

$$
(a_{n0},a_{n1})\longrightarrow(a,a).
$$

此处不只有某条子序列收敛。

**证明。**

源 §106.7 的残差为

<a id="eq:source-residual"></a>
$$
\sigma_n+2\nu(\kappa_n)+\gamma_n+2\beta_n\longrightarrow0,
 \tag{6}
$$

其中失败、射线、成功质量与设置隔离误差均保留各自含义。
持久正性使系数对最终落在某个紧方块$[h_*,1-h_*]^2$。
任一收敛子序列都由源 §104.3 得到$F=q,G=cq+d,a=c/(x+c)$。
但固定的$G$对任意不同合法基标签$j,k$都给

$$
c=G_j(e_j)-G_j(e_k),
$$

所以$c$、进而$a$不依赖所取子序列。
若整列不收敛，就存在与$(a,a)$保持固定正距离的子序列，
紧性再取收敛子列，与已证唯一极限矛盾。

∎

固定连续性不给速度，式 [式 eq:source-residual](#eq:source-residual) 也不是
有限$n$时任意未知终端律到 Born 律的数值误差界。

# 5. 概率响应与状态更新须分别取得

### 命题 5.1（相同即时 Born 响应不决定相同未来）

在内部二维代码上令$P_i=\lvert i\rangle\langle i\rvert$、$X\lvert i\rangle=\lvert 1-i\rangle$。
两仪器

$$
\mathcal I_i(\rho)=P_i\rho P_i,
 \qquad \mathcal J_i(\rho)=XP_i\rho P_iX
$$

对每个输入给相同结果概率$\operatorname{Tr}(P_i\rho)$，却有不同的条件后继。
重复使用时，第一仪器的后续标签保持不变，第二仪器的标签严格交替。

**证明。**

酉共轭保持迹，所以两概率相同。
正质量分支的归一状态分别为$\lvert i\rangle\langle i\rvert$和$\lvert 1-i\rangle\langle 1-i\rvert$。
再次测量计算标签分别得到$i$与$1-i$，归纳给结论。

∎

因此，下一节的 CP 仪器与归一更新是明确增加的有效结构前件。
它们仍可全部内生；但源中旧终端响应的 Born 结论并不供应这些前件。
源 §109 的标量终端缺陷，也不能直接替换下节完整仪器的迹距离误差。
此区分使概率重构和长期动态稳定的推理没有循环。

# 6. 新主定理：可求和仪器误差下的长期极化

<a id="eq:instrumenterror"></a>
### 定义 6.1（内部信息性读口和实际完整误差）

在有限维内部代码$\mathcal{H}$上取非平凡投影$P$，令$P_0=I-P$。
固定有限结果集$Y$及

$$
M_y=\alpha_yP_0+\beta_yP,
 \quad\sum_y|\alpha_y|^2=\sum_y|\beta_y|^2=1,
 \quad\mathcal I_y^0(\rho)=M_y\rho M_y^*.
$$

记$\ell_0(y)=|\alpha_y|^2$、$\ell_1(y)=|\beta_y|^2$，假设两似然向量不同。
从固定初始条件态$\rho_0$开始，实际第$n+1$层的仪器可随过去记录$h_n$自适应变化；
各$\mathcal I_{y|h_n}$完全正，其和保持迹。
这里$\mathcal{H}$是本节闭合的量子预测接口，不是整个宇宙。
若未来还需访问额外量子记忆，须将它计入接口或先证明所用 CP 约化成立。
令实际条件状态为$\rho_n$，并要求

$$
d_n(h_n):=\frac12\sum_{y\in Y}
 \|\mathcal I_{y|h_n}(\rho_n)-\mathcal I_y^0(\rho_n)\|_1
 \le\epsilon_{n+1},
 \qquad E_*:=\sum_{n\ge1}\epsilon_n<\infty.
 \tag{7}
$$

比较的是结果旗标与全部保留后继的联合态。
若有失败标签，须纳入共同结果集；若有泄漏空间，须纳入共同载体。
此时$\mathcal{H},P$和理想比较仪器均须在该共同载体上定义。
不得先删除失败或后选择回码，再声称满足本式。

定义指针权重、杂质及已观察记录过滤为

$$
q_n=\operatorname{Tr}(P\rho_n),\qquad V(q)=q(1-q),\qquad
 \mathcal F_n=\sigma(h_n).
$$

零概率历史不参与条件论断。

式 [式 eq:instrumenterror](#eq:instrumenterror) 只须对实际可达条件态成立，
对全部状态的统一半 diamond 界是更强的充分条件。
反过来，只在理想 ready 输入上取得的一次向量误差，
不自动控制被扰动后的所有实际状态。

<a id="eq:gain"></a><a id="eq:general-gain"></a>
### 引理 6.2（一次理想读出的信息增益）

令$q=\operatorname{Tr}(P\rho)$。
理想结果概率与后验指针权重为

$$
p_y(q)=(1-q)\ell_0(y)+q\ell_1(y),\qquad
 q_y^0=\frac{q\ell_1(y)}{p_y(q)}.
$$

只对$p_y>0$使用比值，零质量项取零。
则

$$
\sum_yp_yq_y^0=q,
$$

$$
v(q):=\sum_yp_y(q_y^0-q)^2
 =q^2(1-q)^2\sum_{y:p_y>0}
 \frac{(\ell_1(y)-\ell_0(y))^2}{p_y(q)}.
 \tag{8}
$$

因此

$$
\sum_yp_yV(q_y^0)=V(q)-v(q),\qquad
 v(q)\ge c_*V(q)^2,
 \quad c_*:=\sum_y(\ell_1(y)-\ell_0(y))^2>0.
 \tag{9}
$$

**证明。**

$M_y^*M_y=\ell_0(y)P_0+\ell_1(y)P$，
且$M_y^*PM_y=\ell_1(y)P$，给概率与后验式。
平均式由$\sum\ell_1=1$。
对$0<q<1$，

$$
q_y^0-q=\frac{q(1-q)(\ell_1(y)-\ell_0(y))}{p_y(q)}.
$$

平方求和给式 [式 eq:gain](#eq:gain)；端点两侧均为零。
用$p_y\le1$得下界。展开$q_y^0-(q_y^0)^2$给杂质式。

∎

<a id="lem:impurity"></a><a id="eq:impurity-lip"></a>
### 引理 6.3（后验杂质是完整输出迹距离的 1-Lipschitz 泛函）

对非归一正算子$\tau$，令

$$
g(\tau)=\operatorname{Tr}(P\tau)-\frac{\operatorname{Tr}(P\tau)^2}{\operatorname{Tr}\tau},\qquad g(0)=0.
$$

若两组$\{\tau_y\},\{\sigma_y\}$均有总迹一，则

$$
\left|\sum_yg(\tau_y)-\sum_yg(\sigma_y)\right|
 \le\frac12\sum_y\|\tau_y-\sigma_y\|_1.
 \tag{10}
$$

**证明。**

写$a=\operatorname{Tr}(P\tau)$、$p=\operatorname{Tr}\tau$，则$0\le a\le p$，且

$$
g(\tau)=\min_{0\le z\le1}\operatorname{Tr}(E_z\tau),
 \qquad E_z=(1-2z)P+z^2I.
$$

当$p>0$，二次式$a-2za+z^2p$在$z=a/p$取最小值；$p=0$时显然成立。$E_z$在$P$与$P_0$上的特征值分别为$(1-z)^2,z^2$，故$0\le E_z\le I$。
把各结果作直和，$\Gamma=\bigoplus_y\tau_y$、$\Sigma=\bigoplus_y\sigma_y$都是态，
且$\sum_yg(\tau_y)=\min_{(z_y)}\operatorname{Tr}[(\bigoplus_yE_{z_y})\Gamma]$。
每个块对角算子都是效果，故对迹零的$\Gamma-\Sigma$，
其期望差绝对值不超过$\frac12\|\Gamma-\Sigma\|_1$。
同一族效果的下确界保留这个界，直和迹范数相加即得。

∎

<a id="thm:polarization"></a><a id="eq:collapse"></a><a id="eq:weightdefect"></a><a id="eq:occupancy"></a>
### 定理 6.4（实际条件态的几乎必然极化）

在上述条件下，存在$q_\infty\in\{0,1\}$，使

$$
\boxed{q_n\longrightarrow q_\infty\quad\text{几乎必然及 }L^1.}
 \tag{11}
$$

极限选择质量满足

$$
\boxed{|\mathbb{P}(q_\infty=1)-q_0|\le E_*.}
 \tag{12}
$$

对每个$0<\eta<1/2$，有驻留次数界

$$
\boxed{\sum_{n=0}^{\infty}\mathbb{P}(\eta\le q_n\le1-\eta)
 \le\frac{q_0(1-q_0)+E_*}{c_*\eta^2(1-\eta)^2}.}
 \tag{13}
$$

这控制的是中间区域总访问数的期望，不是最后离开时间的期望。

**证明。**

实际和理想完整旗标态的差迹为零。
以效果$I_Y\otimes P$读它，式 [式 eq:instrumenterror](#eq:instrumenterror) 给

$$
b_n:=\mathbb{E}[q_{n+1}\mid\mathcal F_n]-q_n,
 \qquad |b_n|\le\epsilon_{n+1}.
$$

因此$Z_n=q_n-\sum_{j=0}^{n-1}b_j$是鞅，且$|Z_n|\le1+E_*$。有界鞅几乎必然并在$L^2$收敛；
绝对可求和的漂移也收敛，所以$q_n$几乎必然收敛。
这里使用的鞅事实可由$L^2$正交增量和 Doob 最大不等式证明：
二阶矩有界使增量平方期望总和有限，给$L^2$Cauchy；
选尾误差快速下降的子序列，最大不等式和 Borel--Cantelli 再给整列几乎必然 Cauchy。

由引理 [lem:impurity](#lem:impurity) 与理想信息增益，

<a id="eq:lyapunov"></a>
$$
\mathbb{E}[V(q_{n+1})\mid\mathcal F_n]
 \le V(q_n)-c_*V(q_n)^2+\epsilon_{n+1}.
 \tag{14}
$$

取期望并从$n=0$加到$N-1$，用末项杂质非负，得

$$
c_*\sum_{n=0}^{N-1}\mathbb{E} V(q_n)^2
 \le V(q_0)+\sum_{n=1}^N\epsilon_n.
$$

单调收敛给$\mathbb{E}\sum_nV(q_n)^2<\infty$，
故该非负级数几乎必然有限，$V(q_n)\to0$。
结合$q_n$的收敛，极限只能为零或一。
有界收敛给$L^1$收敛和

$$
\mathbb{P}(q_\infty=1)-q_0
 =\lim_N\sum_{n=0}^{N-1}\mathbb{E} b_n,
$$

从而得到式 [式 eq:weightdefect](#eq:weightdefect)。
最后，中间区域上$V(q_n)^2\ge\eta^2(1-\eta)^2$，
代入已证级数界即可。

∎

<a id="thm:conserved"></a>
### 定理 6.5（精确平均守恒可以弱化误差条件）

在同一信息性仪器模型中，改为假设每个实际历史上

$$
\sum_y\operatorname{Tr}\bigl(P\mathcal I_{y|h_n}(\rho_n)\bigr)=q_n,
 \qquad d_n(h_n)\longrightarrow0\quad\text{几乎必然}.
$$

则不需要误差可求和，仍有$q_n\to q_\infty\in\{0,1\}$几乎必然，且

$$
\mathbb{P}(q_\infty=1)=q_0.
$$

对全部状态的算子条件$\sum_y\mathcal I_{y|h_n}^*(P)=P$是平均守恒的充分条件。

**证明。**

精确平均守恒使$q_n$为有界鞅，故几乎必然及$L^2$收敛。
令$A_n=\mathbb{E}[(q_{n+1}-q_n)^2\mid\mathcal F_n]$。
正交鞅增量给

$$
\mathbb{E}\sum_{n\ge0}A_n
 =\mathbb{E} q_\infty^2-q_0^2\le q_0(1-q_0)<\infty,
$$

所以$\sum_nA_n<\infty$几乎必然。
精确均值使

$$
A_n=V(q_n)-\mathbb{E}[V(q_{n+1})\mid\mathcal F_n]
 \ge c_*V(q_n)^2-d_n(h_n),
$$

其中最后一步使用引理 [lem:impurity](#lem:impurity)。
若$V(q_\infty)>0$，因$q_n$收敛且$d_n(h_n)\to0$，
右侧最终大于一个严格正的常数，违反$\sum_nA_n<\infty$。
故极限二值；有界鞅保均值给精确选择质量。

∎

这条定理给另一条取得稳定读出的路线：
先由内部对称或守恒关系证明平均指针权重精确保留，再只要求实际仪器渐近精确。
本证明不提供式 [式 eq:occupancy](#eq:occupancy) 那样的显式驻留次数界；
它也不把任意小的非守恒误差当作精确守恒。

<a id="cor:goldport"></a>
### 推论 6.6（黄金信息性读口）

若二元似然为

$$
\ell_0=\left(\frac{1+\gamma}{2},\frac{1-\gamma}{2}\right),
 \qquad
 \ell_1=\left(\frac{1-\gamma}{2},\frac{1+\gamma}{2}\right),\quad0<\gamma\le1,
$$

则定理中可取更强常数$c_*=4\gamma^2$。
v30 的信息性黄金读口对应

$$
\gamma^2=\frac{5+\sqrt5}{10}.
$$

这个似然反差与第 4 节指定制备的质量$(x,x^2)$是不同协议中的不同量。

**证明。**

两似然之差为$\pm\gamma$，两结果概率之和为一。
对$0<q<1$，

$$
v(q)=\frac{\gamma^2q^2(1-q)^2}{p_+(q)p_-(q)}
 \ge4\gamma^2q^2(1-q)^2,
$$

因为$p_+p_-\le1/4$。端点由连续或直接计算处理。

∎

### 推论 6.7（态局域到扇区，但不要求扇区内收敛）

在事件$q_\infty=1$上，最终$q_n>0$，且

$$
D\left(\rho_n,\frac{P\rho_nP}{q_n}\right)
 \le\sqrt{1-q_n}\longrightarrow0,
 \qquad D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1.
$$

在$q_\infty=0$上有对应的$P_0$结论。

**证明。**

在内部纯化坐标上取$\Psi$纯化$\rho_n$。
正规化投影向量$(P\otimes I)\Psi/\sqrt{q_n}$与原向量内积为$\sqrt{q_n}$，
两纯态的半迹距离为$\sqrt{1-q_n}$。
部分迹收缩给所列界。

∎

对于秩五扇区，其内部仍可有永不停止的相位旋转或其他变化。
定理证明的是指针扇区稳定，未证明整个条件向量、所有观测或世界整体停止变化。

# 7. 误差条件为什么不能省略

### 命题 7.1（任意小的固定仪器误差可以阻止极化）

设$\dim\mathcal{H}=d$、$\operatorname{rank}P=r\in\{1,\ldots,d-1\}$。
对任意$0<\lambda<1$，定义实际仪器

$$
\widetilde{\mathcal I}_y(\rho)
 =(1-\lambda)M_y\rho M_y^*
   +\lambda\operatorname{Tr}(M_y\rho M_y^*)I/d.
$$

它与理想完整仪器的半迹距离逐步至多$\lambda$，
但每次正质量更新后

$$
\lambda r/d\le q_n\le1-\lambda(1-r/d).
$$

因而不可能趋于$\{0,1\}$。

**证明。**

第二项是先取理想结果再作固定替换的 CP 仪器，全部结果和保持迹。
每个结果的概率不变，归一后继为$(1-\lambda)\rho_y^0+\lambda I/d$，给所列范围。
逐块半迹距离不超过$\lambda p_y$，求和得$\lambda$。

∎

该混合可以来自同一本体内未被当前观察者读出的辅助记录和酉扩张，
不需要物理上的外部噪声源。

### 命题 7.2（逐步误差趋零仍不保证稳定选择）

在二维空间先做计算基投影测量，再做内部实旋转$R_{\theta_n}$，其中$\sin^2\theta_n=1/(n+2)$。
第$n$次仪器相对理想投影测量的统一完整误差为$\epsilon_n=|\sin\theta_n|\to0$。
然而$q_n$几乎必然既有趋零子列，也有趋一子列。

**证明。**

正质量输出是$R_{\theta_n}\lvert Y_n\rangle$。
它与理想输出的纯态迹距离为$|\sin\theta_n|$，各块求和给相同值。
下一次读数与$Y_n$不同的条件概率是$1/(n+2)$。
从任一确定层$N$起永不再翻转的概率为$\prod_{n\ge N}(1-1/(n+2))=0$；对可数个$N$取并，知翻转无穷多次。
因此两个标签都出现无穷多次，而对应$q_n$分别为$1/(n+2)$和$1-1/(n+2)$，给结论。

∎

此反例区分趋近两个扇区的并集与最终固定到其中一个扇区。
可求和是本篇给出的充分条件，没有被声称为所有可能协议的必要条件。

# 8. 内部递归精度、静态表示与记忆成本

### 推论 8.1（黄金递归精度的可求和调度）

另假设一个已验证的完整仪器编译器，以内部精细度$m$保证

$$
\epsilon(m)\le C\varphi^{-2m},\qquad C>0,
 \qquad\varphi=(1+\sqrt5)/2.
$$

对总误差预算$\delta>0$，取

$$
m_n=\max\left\{0,
 \left\lceil\frac{\log(Cn(n+1)/\delta)}{2\log\varphi}\right\rceil\right\},
 \qquad n\ge1.
$$

则$\epsilon_n\le\delta/[n(n+1)]$，故$\sum_n\epsilon_n\le\delta$，
定理 [thm:polarization](#thm:polarization) 全部结论成立。

**证明。**

若对数为正，向上取整给所需指数界；若为非正，$m_n=0$已满足。
用$1/[n(n+1)]=1/n-1/(n+1)$望远镜求和。

∎

这给精细度$m_n=O(\log n+\log(1/\delta))$，
尚不给原生门字长的同阶界。v30 的单参数指数逼近不自动成为
完整自适应仪器的编译定理；项目 §105 的射影密度也只给每个精度的有限存在性。
若另外证明每层字长$L(m)=O(m)$，才可把前$N$层门调用估成
$O(N\log N+N\log(1/\delta))$。
内部辅助容量、可重复 ready 关联和全部失败界也都须实际供应。[v30](#ref-v30) [quantum](#ref-quantum)

### 命题 8.2（上述随机记录可以属于一个静态整体态）

对满足统一仪器合同的无限协议，其每个有限前缀可用内部等距扩张保存全部结果和
Kraus 指标，形成一列等距 Hilbert 嵌入。
若整体具有这些相容扩张的容量，其直接极限中存在固定向量$\Omega$，
所有记录前缀的概率均为$\langle\Omega,P_h\Omega\rangle$。
定理 [thm:polarization](#thm:polarization) 的事件$\{q_\infty=1\}$属于完整记录代数。

**证明。**

每层用 Kraus 表示定义$V_h\psi=\sum_{y,\alpha}M_{y\alpha|h}\psi\otimes\lvert y,\alpha\rangle$。
归一性给等距，旧记录控制且被保留。
连同初态的内部纯化，得到相容等距链。
其直接极限嵌入满足$\iota_{n+1}V_n=\iota_n$，
故全部递归向量代表同一个$\Omega$。
前缀记录投影相容，延拓为固定空间中的$P_h$，其质量等于仪器树质量。
每个$q_n$是前缀记录函数；几乎处处极限的二值事件由完整记录可测，
在相应交换 von Neumann 记录代数中给投影。

∎

这不要求本体自己在某个外部时钟下改变。
同时，这个极限事件一般不等于一个从未受扰动的初始隐藏扇区；
式 [式 eq:weightdefect](#eq:weightdefect) 正明确允许累计误差改变选择权重。

### 命题 8.3（未来共同接续给在线记忆下界）

设一个确定性观察者按实际操作名更新完整内部状态。
若$N$个历史$p_i$中任意两条都存在同一个后缀$z$，
使两条延长历史须给不同答案，而解码时其余已供应信息完全相同，
则观察者至少要有$N$个不同的内部状态。

**证明。**

若$p_i,p_j$后内部状态相同，同一个后缀的确定性更新仍给相同状态。
其余解码信息也相同，故不能给不同答案，矛盾。

∎

项目新 Typed cocycle §23 构造了$N=2^k$的完整实例：
当前读出恒为一个符号，每次成功记录只有操作名、单位时长与共同成功标记，
仍有$C_{\rm stat}=2,C_{\rm on}=2^k$。
这里后一项是状态数，即需要$k$位；前者二值回顾补充只需一位。
其证明明确供应最终真实未来响应商端点与钟值，取得该端点的成本另计。
因此瞬时读数很少不代表内生观察者保持未来区分所需记忆很小，
但这也不是关于总计算复杂度或 P 与 NP 的结论。[typed](#ref-typed)

# 9. 新几何接口：十种内部类时钟读数

前篇已经反证“全部静止钟率决定曲率”。本节增加运动方向之间的内部比较，
给一个正面的恢复定理，仍保持其有效模型前件。

### 定义 9.1（可校准的局部方向钟模型）

在一个内部事件标签$x$，假设门历史的可比较方向形成四维实向量空间$V_x$；
短段钟读数经共同内部单位标定后满足

$$
m_x(v)=-g_x(v,v),
$$

其中$g_x$是符号$(-+++)$的非退化对称双线性形式。
四维性、线性方向结构和二次钟律均为本节显式假设。
FIB 的三个稳定读口尚未由此被等同为三个空间切向量。

<a id="thm:tomography"></a><a id="eq:metric"></a>
### 定理 9.2（十类时探测的点态度规恢复与最小性）

取基$e_0,e_1,e_2,e_3$，其中$e_0$类时。
对充分小的$\varepsilon>0$，十个方向

$$
e_0;\qquad e_0\pm\varepsilon e_i\ (i=1,2,3);
 \qquad e_0+\varepsilon(e_i+e_j)\ (i<j)
$$

均类时。记其平方钟读数为$m_0,m_i^\pm,m_{ij}$，令$G=-g$，则

$$
\boxed{\begin{aligned}
 G_{00}&=m_0,\\
 G_{0i}&=\frac{m_i^+-m_i^-}{4\varepsilon},\\
 G_{ii}&=\frac{m_i^++m_i^--2m_0}{2\varepsilon^2},\\
 G_{ij}&=\frac{m_{ij}-m_i^+-m_j^++m_0}{2\varepsilon^2}\quad(i<j).
 \end{aligned}}
 \tag{15}
$$

在不预先固定某些分量或单位归一的任意四维 Lorentz 二次型类内，
少于十个固定方向的标量读数一般不能唯一恢复该形式。

**证明。**

类时锥开且上述方向在$\varepsilon\to0$时都趋于$e_0$，故可共取一个正$\varepsilon$。
展开

$$
m_i^\pm=G_{00}\pm2\varepsilon G_{0i}+\varepsilon^2G_{ii},
$$

两式相减、相加给前两组恢复；另外

$$
m_{ij}=G_{00}+2\varepsilon(G_{0i}+G_{0j})
 +\varepsilon^2(G_{ii}+G_{jj}+2G_{ij}),
$$

给最后一式，十个分量全部确定。
对最小性，$\operatorname{Sym}^2(V_x^*)$的维数为十。
少于十个线性评价$G\mapsto G(v_i,v_i)$有非零共同核$H$。
充分小的$G+tH$保持非退化符号和已有方向的类时性，但所有读数相同。

∎

<a id="eq:metricerror"></a>
### 定理 9.3（显式测量误差与符号稳定）

若十个平方钟读数每个误差至多$\delta$，恢复形式$\widetilde G$满足

$$
\boxed{\|\widetilde G-G\|_F
 \le\delta\sqrt{1+\frac{3}{2\varepsilon^2}+\frac{36}{\varepsilon^4}}.}
 \tag{16}
$$

若右侧小于$\mu=\min_j|\lambda_j(G)|$，则恢复形式保持同一 Lorentz 符号。

**证明。**

式 [式 eq:metric](#eq:metric) 分别给$|\Delta G_{00}|\le\delta$、$|\Delta G_{0i}|\le\delta/(2\varepsilon)$、$|\Delta G_{ii}|,|\Delta G_{ij}|\le2\delta/\varepsilon^2$。
Frobenius 平方中对角项各计一次、非对角项各计两次，得到公式。
若误差小于$\mu$，则对$0\le t\le1$，$\|tG^{-1}(\widetilde G-G)\|_{\rm op}<1$，
所以$G+t(\widetilde G-G)$从不退化。
连续路径上的惯性指数不变。

∎

让方向无限聚拢会按$\varepsilon^{-2}$放大空间分量误差。
可区分的方向关系是资源，重复测同一钟方向不能替代它。

### 命题 9.4（十个读数不能证明二次钟律本身）

即使十个读数无误差，也有在可探测的非零类时锥上正、二次齐次的非二次钟律与之相同。

**证明。**

在类时方向的单位球面上取一个非零光滑函数$f$，
其支撑避开全部十个探测射线；还可取偶函数以同时处理反向。
对充分小$\eta$令

$$
m_\eta(v)=m(v)\left[1+\eta f\left(\frac v{\|v\|}\right)\right].
$$

它正、对正伸缩二次齐次，且十个读数不变。
它在一个方向开集上等于原二次型、在另处不同，故不能是二次型：
两个二次多项式若在开集相等就处处相等。

∎

# 10. 有限门 tick 与连续几何极限

<a id="eq:tick"></a>
### 定理 10.1（有限钟段到点态二次型的误差）

另假设内部事件图已给局部坐标及 Lipschitz 度规场，$\|g_y-g_x\|_{\rm op}\le L\|y-x\|$。
沿全部类时的短直段$x+sv$、$0\le s\le h$，$\|v\|\le V$，令

$$
\tau_h(v)=\int_0^h\sqrt{-g_{x+sv}(v,v)}\,ds.
$$

若实际门钟读数有$|\widetilde\tau_h-\tau_h|\le\zeta$，
且$\tau_h/h\le B$，则

$$
\boxed{\left|\left(\frac{\widetilde\tau_h}{h}\right)^2+g_x(v,v)\right|
 \le LV^3h+\frac{2B\zeta}{h}+\left(\frac\zeta h\right)^2.}
 \tag{17}
$$

**证明。**

记$a(s)=-g_{x+sv}(v,v)>0$，则$|a(s)-a(0)|\le Ls\|v\|^3\le LV^3h$。$\tau_h/h$是$\sqrt{a(s)}$的平均值，其平方位于$a$的最大和最小值之间，
所以与$a(0)$相差至多$LV^3h$。
再用$|\widetilde\tau_h^2-\tau_h^2|\le2\tau_h\zeta+\zeta^2$并除以$h^2$。

∎

固定方向分离$\varepsilon$时，保证式 [式 eq:metricerror](#eq:metricerror) 的恢复误差趋零，
一个充分的有效极限条件是$h\to0$且$\zeta/h\to0$。
若同时令$\varepsilon\to0$，则一个充分条件是所列总平方钟误差为$o(\varepsilon^2)$。
在只有这项有界误差保证而 tick 分辨率固定时，不能保证任意短尺度的精确恢复。
这不是断言所有带固定 tick 的特殊精确模型都不能有连续表示；
它指出现有误差合同不足以统一保证该极限。

这里的$s,h$是由内部事件坐标提供的比较参数。
它们之所以可以积分、微分，来自本节的有效连续模型前件，
没有被重新解释为本体外的绝对时间。

# 11. 传播锥、体积与从方向丛到时空的接口

<a id="thm:cone"></a>
### 定理 11.1（同一因果锥加体积标定确定点态度规）

在四维实向量空间中，若两个 Lorentz 形式$g,h$具有相同零锥和类时侧，
则$h=cg$，其中$c>0$。
若在同一内部单位下四维体积密度相同，则$c=1$。

**证明。**

取$g=\operatorname{diag}(-1,1,1,1)$的基。$e_0\pm e_i$是共同零向量，给$h_{00}+h_{ii}\pm2h_{0i}=0$，故$h_{0i}=0,h_{ii}=-h_{00}$。
再代入$e_0+(e_i+e_j)/\sqrt2$，给$h_{ij}=0$。
所以$h=cg$；共同类时侧使$c=-h_{00}>0$。
四维密度按$\sqrt{|\det(cg)|}=c^2\sqrt{|\det g|}$缩放，
相等使$c^2=1$，故$c=1$。

∎

因果顺序尚须被证明提供上述局部零锥；记录计数尚须被证明提供所用体积。
本定理是 Lorentz 模型类内的点态唯一性，不从任意偏序推出光滑流形。

### 定理 11.2（方向丛的纤维几何需要位置变化的对应）

假设内部方向构成秩四光滑向量丛$E\to M$，纤维上有 Lorentz 形式$G$。
若另取得光滑丛同构$e:TM\to E$，则唯一诱导

$$
g_M(X,Y)=G(eX,eY).
$$

两个这样的同构$e,e'$给同一度规，当且仅当$e'=\Lambda e$，其中$\Lambda$逐点属于$O(1,3;G)$。

**证明。**

拉回保对称、非退化和符号，给唯一公式。
若拉回相同，置$\Lambda=e'e^{-1}$，则$G(\Lambda u,\Lambda v)=G(u,v)$，故为纤维 Lorentz 变换。
逆向直接代入。

∎

同构$e$承担“内部方向如何对应可以重叠、拼接的位置变化”。
没有这个关系，读口恢复的只是内部纤维形式。
取得它之后，才可将相容的光滑纤维数据解释为事件流形上的度规。
曲率还涉及空间变化及至少相应阶的正则性；点态十读数本身不测二阶导数。

# 12. 综合结论与下一条可证明的研究目标

本轮得到的主链有三个明确层次：
1. 在项目给出的完整全域相容合同下，未知记录质量仍固定旧 Born 响应； 第二分支的剩余自由可由十三基输入的传递误差精确控制，黄金质量随之有锐界。
1. 在另行取得的完整 CP 仪器模型中，可求和误差足以使实际条件态长期稳定到一个指针扇区； 该结论有明确驻留次数与选择权重界，且固定误差及仅趋零误差都存在反例。
1. 若内部钟历史进一步取得四维方向、二次钟律、单位和事件拼接， 则可以有限探测恢复度规并控制误差；因果锥与体积提供另一条唯一性途径。

### 定理 12.1（单一静态整体下的条件组合）

若同一$(\mathcal{A},\omega)$同时实现第 3 节的响应合同、
第 6 节的可求和完整仪器误差、以及第 9--11 节的方向与几何前件，
则分支校准、稳定内部记录与点态几何恢复的全部结论可以同时成立，
没有任何证明步骤需要引入本体外时间或外部物理环境。

**证明。**

第 4 节在既有响应分类内计算全部质量；
第 6 节只用实际记录树的条件态、迹距离与正性；
第 8 节将这些记录与相容扩张置于同一固定向量；
第 9--11 节只对同一内部记录已经取得的方向和钟读数作代数恢复。
故在共同实现其前件的整体模型中，各结论相容。

∎

这是一条条件组合，不证明任意独立指定的局部数据必可共同实现。

对用户提出的“观察者自身增长就是时间”，本轮更精确的表述是：
观察者的持久记录与程序接续给关系次序；
信息性读口和受控误差给某些记录的长期稳定；
可标定的运动方向和传播关系把这种时钟数据接到几何。
“时钟内生”因此进入可计算、可反驳的数学对象，而非只停在一个钟速函数。

最直接的下一项项目任务是：在同一原生门族上，构造可反复供应的内部记录仪器，
对全部实际可达态证明式 [式 eq:instrumenterror](#eq:instrumenterror) 的可求和界，
同时给出初始化、泄漏、失败和字长成本。
几何线则须从原生历史证明方向组合与二次钟律，并验证不同内部钟实现之间的标定一致性。
完成这些桥接之前，本篇不宣称从五模式推出四维时空、从门计数推出 Einstein 方程，
也不把条件概率重构说成完整量子公理的起源。

## 固定来源与前篇

<a id="ref-head"></a>

**[head]** The Omega Institute, *trureturing*, [固定 dev 提交 bd2207586c3c64e1a4ebcfa23f53b974a2700385](https://github.com/the-omega-institute/trureturing/commit/bd2207586c3c64e1a4ebcfa23f53b974a2700385)， 2026-10-30 23:41:32 Asia/Singapore。

<a id="ref-v30"></a>

**[v30]** 此前对话源稿，*AURIC：唯一静态本体、内生观察者与黄金递归时钟*，v30.0，2026-10-30。 [已读取的原 LaTeX 源稿](https://chatgpt.com/library?file_id=libfile_47e07a3dbbcc8191b42ece3369704c7b&account_id=personal)。 本轮核对原稿的定义、定理与后续缺口；前篇状态是纸面理论，不视为机器证明。

<a id="ref-quantum"></a>

**[quantum]** 项目，[《AURIC FIB ATOM 与量子基本原则：续卷 II》](https://github.com/the-omega-institute/trureturing/blob/bd2207586c3c64e1a4ebcfa23f53b974a2700385/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md)，固定版本，尤其新增 §§104--110， 及 §§100、103 的被引用原生接口。新增全文本轮已读取；源中的调和与门密度结果作为标明的依赖消费。

<a id="ref-omega"></a>

**[omega]** 项目，[《AURIC$\Omega$静态相融纤维理论》](https://github.com/the-omega-institute/trureturing/blob/bd2207586c3c64e1a4ebcfa23f53b974a2700385/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。相对 v30 的固定源不变。

<a id="ref-v21"></a>

**[v21]** 项目，[《静态量子历史、内生观察者与关系时钟》](https://github.com/the-omega-institute/trureturing/blob/bd2207586c3c64e1a4ebcfa23f53b974a2700385/docs/develop/theory/AURIC_STATIC_QUANTUM_HISTORIES_ENDOGENOUS_OBSERVERS_AND_RELATIONAL_CLOCKS_V21.md)，v21。相对 v30 固定源不变。

<a id="ref-typed"></a>

**[typed]** 项目，[《Typed Residual Cocycle Reconstruction》](https://github.com/the-omega-institute/trureturing/blob/bd2207586c3c64e1a4ebcfa23f53b974a2700385/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TYPED_RESIDUAL_COCYCLE_RECONSTRUCTION.md)，新增 §23，尤其定理 23.3。 条件容量中的最终真实响应商取得与资源范围保留原合同。

<a id="ref-clock"></a>

**[clock]** 项目，[《Periodic Clock Rigidity》](https://github.com/the-omega-institute/trureturing/blob/bd2207586c3c64e1a4ebcfa23f53b974a2700385/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PERIODIC_CLOCK_RIGIDITY.md)，新增 §27。本篇只记录其版本增量，未消费该节为主证明依赖。

<a id="ref-v28"></a>

**[v28]** 项目，[《二态读出、全框架相融与 E8 黄金门条件桥》](https://github.com/the-omega-institute/trureturing/blob/bd2207586c3c64e1a4ebcfa23f53b974a2700385/docs/develop/theory/AURIC_BINARY_READOUT_FULL_FRAME_COMPATIBILITY_AND_E8_GOLDEN_GATE_BRIDGE_V28.md)，v28。本篇只记录新入库事实，不把其条件桥当作无条件 E8 起源。
