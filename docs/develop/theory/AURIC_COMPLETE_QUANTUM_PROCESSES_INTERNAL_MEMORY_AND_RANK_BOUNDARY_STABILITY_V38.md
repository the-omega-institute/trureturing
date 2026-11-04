<a id="title"></a>

# AURIC：完整量子过程与内部记忆

# 从三轴闭合到秩边界稳定性

**定义、定理与纸面证明　v38.0**

2026 年 10 月 31 日　Asia/Singapore

> 原稿元数据：PDF 标题「AURIC：完整过程、内部记忆与秩边界稳定性」；作者「AURIC research continuation」；主题「Complete quantum processes, endogenous memory, native readout-compatible dilations and rank-conditioned statistical stability」。页眉「AURIC：完整过程、内部记忆与秩边界稳定性」；版本「v38 / 2026-10-31」。

> 转写来源：所供 v38.0 XeLaTeX 原稿，SHA-256 <code>1476b658<wbr>54510bc1<wbr>9e252d70<wbr>64dc009a<wbr>86569f8f<wbr>cca099d0<wbr>289fe941<wbr>8c396748</code>。正文中的“本轮”“当前树”、文件盘点、源码阅读及未运行声明均保留作者原有叙述，指原稿的来源轮次。

<a id="abstract"></a>

## 摘要

v37 已给固定五模式的完整 qubit 编码及原生黄金门逼近。
本稿把该编码提升为过程接口：任意保 Hermitian、保迹线性过程对应三轴仿射变换，
并有保留五矩关系、恒等元及复合的真实五维线性表示。
任意内部参考上的完整正性由 Choi 矩阵控制；四个四面体输入的十二个均值
完整确定过程，并给精确参数误差恒等式及参考稳定界。
随后区分普通酉扩张、保持旧五读口的统一记录编码和最终经典记录：
给出逐模式秩判据，在原十三维载体实现全部一次五概率，在同族八十九维载体
构造保留四个相干记录的二十路径编码，仍只使用旧十位终端。
完整相干记录可恢复全部输入；只保留经典分支可恢复的充要条件是各分支为标量乘酉。
另一方面，若一个全局酉对全部内部联合态都能仅由当前约化态自治更新，
该酉必须分解成两个内部角色上的乘积。
本轮新增源码给精确有限事件比较及秩二概率识别。
在此基础上，本稿推导条件数为最小 Gram 特征值的概率稳定界、
固定输入的三个有限原生见证，以及跨越秩一边界的连续模误差界。
全部结论保留具体输入、操作、统计及完整失败质量的前件；不以数学存在替代实际取得。

<a id="section-1"></a>

## 1 固定版本与真正新增的供应

本轮固定公开提交为

`621108f17bf2a141b2605ddad479f28ed6ac4bbd`，

提交时间为 2026-10-31 05:15:55（新加坡）。
比较基线为 v37 的

`3f98ae45e29bd5fb6ef8dd7d1e5bf39c2723520e`。

theory 与 D5 子树分别完整返回 1079、12797 项，均未截断；
比较得到 14 个理论文件、22 个 D5 路径变化。
相关当前与基线下载的 38 份文件及 17 份未变关键供应均按 Git blob 核对。
这只是来源完整性检查，不是数学证明或形式编译。[[1](#bib-head)]

本轮直接相关增量如下。

1. 续卷 II 严格追加 §§126–131：全八十九维上的二十调用投影转送；
   两个各两调用的精确同签名事件；一次黄金混合下的秩二权重识别及秩一盲区。
   旧 §77、§100、§§121–125 与黄金门核心未改。[[2](#bib-continuation)]

2. 新增 `FinitePreparationChannel.lean`：
   有限密度矩阵族的制备通道及带内部参考的完整矩阵公式。
   本轮读取公开声明与证明源码，未执行 Lean。[[3](#bib-prepare)]

3. 关系递归文稿进一步区分列随机精化、保历史的酉扩张与可继续复合的观察商；
   历史恢复的新噪声界也明确需要同一来源、原始切面及联合误差合同。[[6](#bib-refinement), [8](#bib-rooted)]

本轮导入的 v35、v36 文件明示为既有稿件转换，不计作独立重新认证。
当前树中尚未导入 v37；本稿对 v37 的引用指本对话已交付的数学构造。

继续固定唯一静态整体 $(\mathcal A,\omega)$。系统、参考、记录与准备角色均在该整体内部；
字长只是声明操作的组合索引，不引入整体外的时钟。
主线过程定理明确采用复 Hilbert、线性及 CPTP 接口；
第 [10](#sec:rank) 节则回到来源的未知记录概率模型，只消费已重构的条件终端，
不预先把正在识别的记录质量定义为 Born 权重。
本轮全部数学为纸面推导；未运行数学数值、CAS、Lean、枚举或门字搜索。

<a id="section-2"></a>

## 2 承接的固定 AURIC 编码

原五模式顺序为
$(0,2,3,5,25)=(000,100,010,001,101)$。
三个占据依次读低端、高端、中位，即位位置 $1,3,2$。
置

$$
\nu=(1+2\sqrt3+\sqrt{11})^{-1},\qquad
a_\nu=\nu(\sqrt3+\sqrt{11})/2,\qquad c=(a_\nu,a_\nu,\nu)^T.
$$

承接 v37 的五个秩一效果

$$
\begin{aligned}
E_{25}&=\frac\nu2(\sqrt3 I-\sigma_x-\sigma_y-\sigma_z),&
E_0&=3E_{25},\\
E_2&=\frac\nu2(\sqrt{11}I+3\sigma_x+\sigma_y+\sigma_z),\\
E_5&=\frac\nu2(\sqrt{11}I+\sigma_x+3\sigma_y+\sigma_z),&
E_3&=\nu(I+\sigma_z).
\end{aligned}
$$

它们和为 $I$，可写 $E_s=|\eta_s\rangle\langle\eta_s|$。
固定
$J\psi=\sum_s|s\rangle\langle\eta_s,\psi\rangle$，
则 $J^*J=I$。
对 $\rho=(I+r\cdot\sigma)/2$，

$$
u(\rho)=\bigl(\operatorname{Tr}(J\rho J^*N_x),\operatorname{Tr}(J\rho J^*N_y),
\operatorname{Tr}(J\rho J^*N_z)\bigr)^T=c+\nu r.
$$

这只是所声明的固定码；原五模式全体状态不都属于这个 qubit 球。

对未归一关系 $G=(NI+v\cdot\sigma)/2\succeq0$，
五矩写为 $\mu=(N,u,\varkappa)$，其中 $u=cN+\nu v$、
$\varkappa=\operatorname{Tr}(GE_{25})$。它们满足

$$
\ell(\mu):=N-\mathbf1^Tu-2\varkappa=0,\qquad
N\ge0,\quad |v|\le N.
$$

原三轴对两个逻辑态的距离标尺为

$$
D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1
=\frac{\|u(\rho)-u(\sigma)\|_2}{2\nu}.
$$

这些关系是后续过程定理的固定接口，不是新增自由控制菜单。

<a id="section-3"></a>

## 3 从状态三轴提升到完整过程

<a id="statement-3.1"></a>

#### 定义 3.1（固定线性逻辑过程）

令 $\Phi:M_2(\mathbb C)\to M_2(\mathbb C)$ 为复线性、保 Hermitian、保迹映射。
同一 $\Phi$ 必须用于所比较的全部输入；实际准备改变了未保留的内部记忆时，
不能预先把不同试验当作同一个过程。

<a id="thm:lift"></a>

#### 定理 3.2（三轴仿射表示与五矩线性复合）

存在唯一 $T\in M_3(\mathbb R)$、$t\in\mathbb R^3$，使

$$
\Phi\!\left(\frac{NI+v\cdot\sigma}{2}\right)
=\frac{NI+(Tv+tN)\cdot\sigma}{2}.
$$

设 $b=c+\nu t-Tc$，定义整个五维实坐标空间上的线性映射

$$
\boxed{\begin{aligned}
N'&=N,\\
u'&=Tu+bN,\\
\varkappa'&=\varkappa-\tfrac12\mathbf1^Tb\,N
+\tfrac12\mathbf1^T(I-T)u.
\end{aligned}}
$$

则 $\ell'=\ell$，恒等过程给 $I_5$，并且过程复合严格对应五矩矩阵相乘。

**证明。**

$I,\sigma_x,\sigma_y,\sigma_z$ 是 Hermitian 空间的实基。
保迹给 $\Phi(I)=I+t\cdot\sigma$、
$\Phi(\sigma_j)=\sum_iT_{ij}\sigma_i$，保 Hermitian 给全部系数实。
代入 $u=cN+\nu v$ 得 $u'=Tu+bN$。
最后一式恰使 $N'-\mathbf1^Tu'-2\varkappa'=\ell$。
可逆坐标 $(N,u,\varkappa)\leftrightarrow(N,v,\ell)$ 中，该映射就是

$$
(N,v,\ell)\longmapsto(N,Tv+tN,\ell).
$$

因此恒等元准确为恒等，复合为
$(T_2,t_2)\circ(T_1,t_1)=(T_2T_1,t_2+T_2t_1)$。

□

这个 $5\times5$ 实矩阵作用于关系矩，不是 $\mathbb C^5$ 振幅上的酉矩阵；
它也不必逐项非负。物理正性应在上述编码正锥上检验。
在不相容数据上保留 $\ell$ 是一个明确的线性延拓约定，不赋予这些数据物理态含义。

<a id="statement-3.3"></a>

#### 定义 3.3（完整正性与 Choi 矩阵）

$\Phi$ 完全正，是指对每个有限内部参考 $\mathcal R$，
$\Phi\otimes\operatorname{id}_{\mathcal R}$ 都保持整体正半定性。
令 $|\Omega\rangle=(|00\rangle+|11\rangle)/\sqrt2$，定义归一 Choi 矩阵

$$
C_\Phi=(\Phi\otimes\operatorname{id})(|\Omega\rangle\langle\Omega|)
=\frac14\left[
(I+t\cdot\sigma)\otimes I+
\sum_{i,j}T_{ij}\sigma_i\otimes\sigma_j^{\mathsf T}
\right].
$$

<a id="thm:choi"></a>

#### 定理 3.4（AURIC 过程的完整正性判据）

上述保迹映射为 CPTP，当且仅当 $C_\Phi\succeq0$。
此时可写

$$
\Phi(X)=\sum_{a=1}^rK_aXK_a^*,\qquad
\sum_aK_a^*K_a=I,\qquad r=\operatorname{rank} C_\Phi\le4.
$$

其中 $r$ 是最小 Kraus 数。

**证明。**

完全正显然给 $C_\Phi\succeq0$。
反向分解 $C_\Phi=\sum_{a=1}^r|w_a\rangle\langle w_a|$，
由向量化唯一确定 $K_a$，使 $(K_a\otimes I)|\Omega\rangle=w_a$。
所得 Kraus 映射与 $\Phi$ 具有相同 Choi 矩阵；逐矩阵单位比较给两者相等。
保迹条件 $\operatorname{Tr}_{\rm out}C_\Phi=I/2$ 给 $\sum_aK_a^*K_a=I$。
张量任意内部参考后，每项仍为正算子的共轭，故完全正。
任意 $s$ 项 Kraus 分解给至多 $s$ 个秩一 Choi 项，因此 $s\ge\operatorname{rank} C_\Phi$。

□

这是标准 Choi–Kraus 表示的有限维证明，本稿把它作为过程接口的供应，
不声称该表示是 AURIC 新发现。[[9](#bib-watrous)]
Choi 的第二个二维因子首先是数学判据中的参考；
若解释为实际内部联合试验，须另行供应同一 $(\mathcal A,\omega)$ 内的二维角色、
联合编码及 Bell 输入。只检查某个更小的既有参考域，不等同于标准完全正性。

<a id="statement-3.5"></a>

#### 推论 3.5（酉过程的三个等价刻画）

对 qubit CPTP 过程，以下等价：$\Phi=\operatorname{Ad}_U$；
$\operatorname{rank} C_\Phi=1$；$t=0$ 且 $T\in SO(3)$。

**证明。**

单 Kraus 加保迹给 $K^*K=I$，同维有限空间中 $K$ 酉。
酉共轭在 Pauli 空间上为正向旋转。
反向任意三维旋转用其轴 $n$ 与角 $\theta$ 写成
$U=\cos(\theta/2)I-i\sin(\theta/2)n\cdot\sigma$ 的共轭作用。

□

即使严格收缩与单体归一，也不能代替完整正性。
令

$$
\Phi_\lambda(X)=\lambda X^{\mathsf T}
+(1-\lambda)\operatorname{Tr}(X)I/2,\qquad 1/3<\lambda<1.
$$

其 Bloch 作用为 $\lambda\operatorname{diag}(1,-1,1)r$，
严格收缩且保持全部单体态；但

$$
C_{\Phi_\lambda}=\lambda F/2+(1-\lambda)I_4/4
$$

在反对称向量上的特征值为 $(1-3\lambda)/4<0$，其中 $F$ 为交换算子。
它无法作为对任意内部参考一致的量子过程。

<a id="section-3.1"></a>

### 3.1 保留内部上下文的算子值五矩

写联合态

$$
\Omega=\frac12\left(I\otimes S+\sum_j\sigma_j\otimes V_j\right)\succeq0.
$$

定义算子值读数

$$
N=S,\qquad u_j=c_jS+\nu V_j,\qquad
\varkappa=\frac\nu2(\sqrt3S-V_x-V_y-V_z).
$$

这些仍满足 $N-\sum_ju_j-2\varkappa=0$。
定理 [3.2](#thm:lift) 按相同实系数作用，给

$$
S'=S,\qquad V'_i=\sum_jT_{ij}V_j+t_iS.
$$

故标量层正锥保持刻画普通正性，全部内部参考层的完整重组矩阵正性刻画 CP。
五个读数分别正并不足以替代整体重组矩阵正；关系算子也不必各自成为归一态。
这种提升保留了纠缠上下文，而不是只把它们取迹丢掉。

<a id="section-4"></a>

## 4 四个输入与十二个读数：过程的完整、稳定重建

取四面体向量

$$
\begin{aligned}
r_0&=(1,1,1)/\sqrt3,&r_1&=(1,-1,-1)/\sqrt3,\\
r_2&=(-1,1,-1)/\sqrt3,&r_3&=(-1,-1,1)/\sqrt3.
\end{aligned}
$$

它们满足 $\sum_ar_a=0$、$\sum_ar_ar_a^T=4I/3$。
输入态为 $\rho_a=(I+r_a\cdot\sigma)/2$，
输出三轴表为 $u_a=c+\nu s_a$，其中 $s_a=t+Tr_a$。
新 `FinitePreparationChannel` 以平方根 Kraus 构造证明，
有限密度矩阵族有制备通道
$\mathsf P(X)=\sum_aX_{aa}\rho_a$，并给带内部参考的完整矩阵公式。[[3](#bib-prepare)]
它保留参考角色的相干块，不保留被读取标签之间的全部相干；
也未自动供应实际原生准备。

<a id="thm:tetra"></a>

#### 定理 4.1（完整过程表及最少输入数）

四个输入的十二个均值唯一恢复任意上述线性保迹过程：

$$
\boxed{
t=\frac14\sum_as_a,\qquad
T=\frac34\sum_as_ar_a^T,\qquad
s_a=(u_a-c)/\nu.
}
$$

若要辨认一般 qubit CPTP 过程，少于四个固定输入不足。

**证明。**

将 $s_a=t+Tr_a$ 分别求和、右乘 $r_a^T$ 再求和，即得公式。
少于四个输入的 Hermitian 张成空间维数小于四，
故存在非零实线性泛函 $f$ 在全部这些输入上为零。
取非零无迹 Hermitian $H$，令 $\Delta(X)=f(X)H$ 并复线性延拓。
它保 Hermitian 且迹为零。
完全退极化过程的 Choi 矩阵为严格正的 $I_4/4$，
所以足够小的正负扰动 $\Phi_{\rm dep}\pm\epsilon\Delta$ 仍 CPTP。
二者在所有给定输入上相同，却是不同过程。

□

最少四个输入的结论针对一般过程；事先限定为酉过程可以使用更少参数。
这里的四个输入也不是前轮五矩中的“四推一”，两者的对象不同。

<a id="thm:tomostability"></a>

#### 定理 4.2（精确参数误差及物理拟合）

两张四输入表之差记为 $e_a=\widetilde u_a-u_a$，相应参数差为 $\delta t,\delta T$。
则

$$
\boxed{
\|\delta t\|^2+\frac13\|\delta T\|_F^2
=\frac1{4\nu^2}\sum_a\|e_a\|^2.
}
$$

若原始测量表距某个真实 CPTP 表的欧氏误差至多
$E=(\sum_a\|e_a\|^2)^{1/2}$，
把整张表正交投影到 CPTP 表集合后，得到的 $\widehat\Phi$ 满足

$$
\sup_\rho D(\widehat\Phi(\rho),\Phi(\rho))\le\frac E{2\nu},
\qquad
d_{\rm ref}(\widehat\Phi,\Phi)\le\frac{\sqrt3E}{2\nu}.
$$

右侧可与一取最小值。这里
$d_{\rm ref}=\tfrac12\|\widehat\Phi-\Phi\|_\diamond$，参考均为内部角色。

**证明。**

展开 $\sum_a\|\delta t+\delta Tr_a\|^2$，
交叉项由 $\sum_ar_a=0$ 消去，二次项由四面体二阶矩给出。
CPTP 表集合是 Choi 正锥的仿射截面在该可逆表映射下的像，
闭、凸且有界。正交投影不会增加到任何真实集合点的距离，故仍可用 $E$。

对 $|r|\le1$，加权 Cauchy–Schwarz 给
$|\delta t+\delta Tr|\le E/\nu$，故单体迹距离至多 $E/(2\nu)$。
Choi 差满足

$$
\|\delta C\|_F^2
=\tfrac14(\|\delta t\|^2+\|\delta T\|_F^2),
\qquad
\|\delta C\|_1\le2\|\delta C\|_F.
$$

任意纯输入连同内部参考，经过 Schmidt 表示可写成
$(I\otimes A)|\Omega\rangle$，其中 $\|A\|_{\mathrm{op}}^2\le2$；
因此参考输出半迹距离至多 $\|\delta C\|_1$。
代入参数恒等式得到 $\sqrt3E/(2\nu)$；混态由凸性覆盖。

□

必须投影整张过程表：四个单独合法输出不保证存在共同 CP 过程，
转置映射就是反例。实际理想四面体准备的误差，可在已声明 CPTP 前件下
由收缩性计入输出预算；无需假装原有限门字能精确准备全部理想顶点。
若输入或记录上下文随试验改变，过程表拟合只能给一个候选，不能证明“同一过程”前件。
同样，$U$ 与 $e^{i\theta}U$ 的全部状态过程表相同；
相干受控程序的相位仍须用额外的关系接口保留。
本节误差界针对指定逻辑过程及校准后的三轴效果。
若实际物理输出含未预算的码外分量，三轴表的接近并不能控制整个物理输出；
必须另给代码支持、恢复接口或完整泄漏预算。

<a id="section-5"></a>

## 5 分支归一化：过程质量必须一同保留

<a id="statement-5.1"></a>

#### 定义 5.1（完整分支过程）

一个保 Hermitian 的线性分支不必保迹，其实坐标一般为

$$
\begin{pmatrix}N'\\v'\end{pmatrix}
=
\begin{pmatrix}\alpha&\beta^T\\t&T\end{pmatrix}
\begin{pmatrix}N\\v\end{pmatrix}.
$$

对归一输入，$N'$ 是分支质量；仅在 $N'>0$ 时，条件态才有
$r'=v'/N'$。一个完整仪器是有限 CP 映射族 $\{\Phi_a\}$，
其和保迹，等价于

$$
C_a\succeq0,\qquad \sum_a\operatorname{Tr}_{\rm out}C_a=I/2.
$$

失败、弃权及泄漏若是实际结果，都应作为完整族的分支保留。

<a id="statement-5.2"></a>

#### 命题 5.2（四输入的分支识别）

同样四个四面体输入的未归一输出 $(N'_a,v'_a)$
唯一确定任意保 Hermitian 线性分支的十六个实系数。
只提供各输入的条件归一三轴，一般不能确定该分支。

**证明。**

四个输入关系是四维 Hermitian 空间的一组基，
故它们的完整线性像确定映射。反之，任取效果 $0\preceq F\preceq I$，

$$
\Phi_0(\rho)=\operatorname{Tr}(F\rho)|0\rangle\langle0|,\qquad
\Phi_1(\rho)=\operatorname{Tr}((I-F)\rho)|0\rangle\langle0|
$$

形成完整 CP 仪器。所有正质量分支的条件后继都相同，
但质量随 $F$ 改变；归一后三轴无法辨认 $F$。

□

因此五模式中的 $N$ 不是可随意删除的记账量。
对物理关系 $\ell=0$，每个分支仍可用 $(N,u,\varkappa)$ 表达；
无需把第 [3.2](#thm:lift) 定理在非物理残差方向的延拓约定强加给仪器求和。
新制备模块给出的
$\Phi(X)=\sum_iX_{ii}\rho_i$
是这类 CP 构造的具体供应：带内部参考时保留参考的非对角矩阵块，
但先取制备标签的对角块，并不保留不同标签间的原相干。
这说明“准备一个族”“保留相干程序”和“得到完整过程”有不同的前件。
[[3](#bib-prepare)]

<a id="section-6"></a>

## 6 原生实现：相干记录、五个读口与旧终端

本节消费既有原生射影密度和具体载体，不把任意数学等距视为新增按钮。
原十三维载体为

$$
\mathcal H_{13}=\operatorname{span}
\{|10\,abcde\,010\rangle:abcde\text{ 无相邻 }11\}.
$$

取固定逻辑输入等距 $R:\mathbb C^2\to\mathcal H_{13}$，
例如映入合法内串 $00100,10100$。
同族完整八十九维载体为

$$
\mathcal H_{89}=\operatorname{span}
\{|10\,\gamma_1\cdots\gamma_9\,010\rangle:
\gamma\text{ 无相邻 }11\}.
$$

原地址 $0,\ldots,6$ 与新增地址 $7,\ldots,10$ 均按来源解释。
$R_0:\mathcal H_{13}\to\mathcal H_{89}$ 是已声明 ready 嵌入；
原十位终端 $N_w$ 仍只读 $b_{-1},\ldots,b_8$，含全部 $1024$ 个标签。
它在 $\mathcal H_{89}$ 上一般不是秩一终端。
[[4](#bib-golden), [2](#bib-continuation)]

<a id="lem:native"></a>

#### 引理 6.1（相位准确的原生等距逼近）

在上述 $d=13,89$ 载体，若原生字在 $PU(d)$ 稠密，
且各原生门行列式生成有限根群，则正字闭包含 $SU(d)$。
若 $R,A:\mathbb C^2\to\mathcal H_d$ 为等距，任意 $\epsilon>0$
存在正原生字 $w$，满足

$$
\|K_wR-A\|_{\mathrm{op}}<\epsilon.
$$

**证明。**

令 $G$ 为正字的紧闭包。对任意 $g\in G$，
选收敛的幂子列 $g^{n_k}$，并进一步令 $n_{k+1}-n_k\to\infty$，
则 $g^{n_{k+1}-n_k}\to I$，
故 $g^{n_{k+1}-n_k-1}\to g^{-1}\in G$；因此 $G$ 是群。
置 $H=G\cap SU(d)$，有限行列式像使 $H$ 在 $G$ 中有限指数。
射影像 $\pi(H)$ 是 $PU(d)=\pi(G)$ 的闭有限指数子群，
由 $PU(d)$ 连通，$\pi(H)=PU(d)$。
任意 $S\in SU(d)$ 因而写成 $S=zh$，
其中 $h\in H$、$z^d=1$；
故 $H$ 又是 $SU(d)$ 的闭有限指数子群。
由 $SU(d)$ 连通，$H=SU(d)$，即 $SU(d)\subseteq G$。
将 $R$、$A$ 的两列分别补成正交基，得到把 $R$ 送到 $A$ 的酉；
在非零正交补上调一个相位即可令行列式为一且不改变这两列。
由闭包取得所需正字。

□

这里的行列式有限性由已给黄金局部门的根单位谱得到；
不把射影逼近误写为任意未校准的相干相位。
引理只给存在及逼近，不给最短字或制备成本界。

<a id="section-6.1"></a>

### 6.1 普通扩张与固定读口的不同空间要求

若 $\Phi$ 的最小 Kraus 数为 $r\le4$，取

$$
W_\Phi\psi=\sum_{a=1}^{r}K_a\psi\otimes|a\rangle,\qquad
W_\Phi^*W_\Phi=I.
$$

输出逻辑与相干记录总空间维数为 $2r\le8$，
因此作为一个等距嵌入，它已经能放进 $\mathcal H_{13}$，并由引理逼近。
不过任意选择的数学嵌入，并不自动把原五个读口变成所需逻辑读口，
也不自动给出一个实际中途记录仪器。

<a id="thm:rankports"></a>

#### 定理 6.2（统一记录编码的逐读口秩判据）

设 $\{\Pi_s\}_{s=0,2,3,5,25}$ 是物理载体的正交投影分解，
$E_s=|\eta_s\rangle\langle\eta_s|\ne0$ 为固定 AURIC 效果。
存在等距
$F:\mathbb C^2\otimes\mathbb C^r\to\mathcal H$，使

$$
F^*\Pi_sF=E_s\otimes I_r\qquad\text{对所有 }s
$$

的充要条件为

$$
\operatorname{rank}\Pi_s\ge r\qquad\text{对所有 }s.
$$

因此保持这一固定读口接口的统一载体至少需要 $5r$ 维，
而 $5r$ 维足够。

**证明。**

左侧秩不超过 $\operatorname{rank}\Pi_s$，右侧秩为 $r$，得必要性。
充分性：对每个 $s$ 选等距
$B_s:\mathbb C^r\to\operatorname{Ran}\Pi_s$，令

$$
F=\sum_s B_s(\langle\eta_s|\otimes I_r).
$$

不同 $s$ 的像正交，故
$F^*F=\sum_s E_s\otimes I_r=I$，并逐项满足要求。
取五个秩 $r$ 扇区即可达到 $5r$。

□

这个界控制的是同一编码对所有逻辑–记录联合态都保持固定五效果；
它不是所有量子通道扩张的普遍 $5r$ 下界。
若仪器要求保留的经典标签超过四个，也不能仅凭合并通道的 Choi 秩不超过四，
就把指定标签压缩成四个。

在 $\mathcal H_{13}$ 中，以前三位 $abc$ 的五模式分组，
扇区秩为 $(3,3,3,2,2)$；纸面上逐个固定末尾位，
由“无相邻 $11$”的 Fibonacci 递推即得。
因而它能统一携带 $r\le2$ 个记录。
一个达到接口的二记录嵌入是

$$
L_{13}|s,a\rangle=|10\,abc\,0a\,010\rangle,\qquad
F_{13}=L_{13}(J\otimes I_2),
$$

其中 $abc$ 是 $s$ 的固定三位串。

<a id="section-6.2"></a>

### 6.2 八十九维中的二十路径与旧十位终端

在 $\mathcal H_{89}$ 上，同样五个前缀扇区的秩为
$(21,21,21,13,13)$。
将四个记录标为 $a=(a_1,a_2)\in\{0,1\}^2$，定义

$$
L_{89}|s,a_1a_2\rangle
=|10\,abc\,0a_1\,0a_2\,00\,010\rangle,\qquad
F=L_{89}(J\otimes I_4).
$$

所有二十条路径都无相邻 $11$，所以这是等距。
其旧十位前缀为

$$
w_{s,a}=10\,abc\,0a_1\,0a_2\,0,
$$

二十个前缀互不相同。直接读矩阵元得到

$$
\boxed{
F^*\Pi_sF=E_s\otimes I_4,\qquad
F^*N_{w_{s,a}}F=E_s\otimes|a\rangle\langle a|.
}
$$

<a id="thm:89"></a>

#### 定理 6.3（相干过程与原旧终端的统一实现）

对任意 qubit CPTP 映射 $\Phi$，将 Kraus 数补至四，
置 $A_\Phi=FW_\Phi$。对任意 $\epsilon>0$，
存在使用上述十一地址的正原生字 $w$，满足

$$
\|K_wR_0R-A_\Phi\|_{\mathrm{op}}<\epsilon.
$$

对全部逻辑输入及任意内部参考，其相干输出半迹距离不超过 $\epsilon$；
在已声明完整终端 Born 统计接口下，旧 $1024$ 标签分布的总变差也不超过
$\epsilon$。理想输出概率为

$$
q_{s,a}=\operatorname{Tr}(E_sK_a\rho K_a^*).
$$

**证明。**

$A_\Phi$ 与 $R_0R$ 都是二列等距，应用引理 [6.1](#lem:native)。
对纯输入连同参考，两个输出向量差不超过 $\epsilon$，
其纯态迹距离也不超过 $\epsilon$；混态由凸性覆盖。
完整测量的迹距离收缩给总变差界。
最后一式由刚得到的终端压缩恒等式计算。

□

对每个分支记录 $a$，定义

$$
\begin{gathered}
N_a=\sum_s q_{s,a},\quad
u_{x,a}=q_{2,a}+q_{25,a},\quad
u_{y,a}=q_{5,a}+q_{25,a},\quad u_{z,a}=q_{3,a},\\
\varkappa_a=q_{25,a}.
\end{gathered}
$$

于是 $q_{0,a}=3q_{25,a}$，并且
$N_a-u_{x,a}-u_{y,a}-u_{z,a}-2\varkappa_a=0$。
这些是未归一分支的 AURIC 关系；只有 $N_a>0$ 才做条件归一化。
若实际完整终端分布距理想分布的总变差至多 $\Delta$，
则保守地有 $|p_{0,a}-3p_{25,a}|\le4\Delta$。

设 $P$ 为二十路径的量子代码投影。
由 $(I-P)A_\Phi=0$，
量子代码泄漏质量至多 $\epsilon^2$。
然而旧十位终端有简并：另一些代码外路径可能与代码内路径共用旧标签，
所以“标签不在二十前缀内”的质量不等于全部量子泄漏。
而本构造中 $a_2=0$ 的路径虽位于旧二十六维来源代码之外，
却是新二十路径代码的有意组成部分，应当计为正常输出。
旧七地址在旧代码上的 $K_f\otimes I$ 恒等式，
也不能直接搬到这个新代码；后续逻辑操作须重新按完整载体编译。
[[2](#bib-continuation)]

终端实际读取 $(s,a)$ 后再忘记 $s$，不会撤销已发生的 $s$ 读出。
因此本定理的结论是相干扩张和最终联合统计；
若需要只读 $a$ 并把 $K_a\rho K_a^*$ 保留下来继续运行，
还须供应相应实际中途仪器。
数学压缩恒等式与原生逼近，也不补足来源中尚未声明的任意输入实际准备或未知读者统计。

<a id="section-6.3"></a>

### 6.3 只要求最终五概率时，十三维已经足够

<a id="statement-6.4"></a>

#### 命题 6.4（全部通道五概率的十三维实现）

对任意 qubit CPTP 映射 $\Phi$，存在等距
$A:\mathbb C^2\to\mathcal H_{13}$，使

$$
A^*\Pi_sA=\Phi^*(E_s)\qquad\text{对所有 }s.
$$

因此这些最终五概率可由原十三维正原生字任意逼近。

**证明。**

令 $F_s=\Phi^*(E_s)\succeq0$；则 $\sum_sF_s=I$、$\operatorname{rank} F_s\le2$。
每个物理扇区至少二维，选
$B_s:\mathbb C^2\to\operatorname{Ran}\Pi_s$ 为等距，
令 $A=\sum_sB_s\sqrt{F_s}$。
正交性给 $A^*A=I$ 和 $A^*\Pi_sA=F_s$，再应用原生等距逼近。

□

该命题确定一次最终概率，不声称保留逻辑输出、四维相干记录或全部未来关系。
因此“十三维足够”与“固定四记录统一编码需要更大载体”分别有精确而相容的量词。

<a id="section-7"></a>

## 7 相干记录与经典结果：何时仍可逆

<a id="statement-7.1"></a>

#### 定理 7.1（保留完整相干记录的可恢复性）

对等距 $W_\Phi$，所有输入及内部参考的迹距离原样保持。
其完整输出上存在 CPTP 左逆

$$
\mathcal R(X)=W_\Phi^*XW_\Phi
+\operatorname{Tr}\!\left[(I-W_\Phi W_\Phi^*)X\right]\tau,
$$

其中 $\tau$ 是任意固定逻辑密度矩阵。

**证明。**

等距左右乘不改变非零奇异值，故连同内部参考的迹距离保持。
第一项为 CP，第二项为正效果后制备 $\tau$ 的 CP 映射，
二者迹之和为 $\operatorname{Tr} X$。
在 $X=W_\Phi\rho W_\Phi^*$ 上第二项为零，第一项等于 $\rho$。

□

因此局部通道的不可逆性可与整体酉性相容，
但恢复所需信息可能在系统与记录的联合关系中；
不能推断它一定完整存在于记录的单独边缘。
当实际将 Kraus 记录去相干为经典标签时，恢复条件更强。

<a id="thm:classicalrecover"></a>

#### 定理 7.2（完整输入域上经典分支可恢复的充要条件）

设每个细分支含一个 Kraus 算子，

$$
\mathcal I(\rho)=\sum_aK_a\rho K_a^*\otimes|a\rangle\langle a|,
\qquad \sum_aK_a^*K_a=I.
$$

从该经典–量子输出对全部 qubit 输入精确恢复，存在 CPTP 左逆的充要条件是

$$
\boxed{K_a^*K_a=p_aI\quad\text{对所有 }a,\qquad
p_a\ge0,\quad\sum_ap_a=1.}
$$

非零分支等价于 $K_a=\sqrt{p_a}\,U_a$，$U_a$ 酉。

**证明。**

充分性由读取 $a$ 后施加 $U_a^*$ 得到。
必要性：设 $\mathcal R\mathcal I=\operatorname{id}$，
对每个块定义 CPTP 映射
$\mathcal R_a(X)=\mathcal R(X\otimes|a\rangle\langle a|)$。
于是 $\sum_a\mathcal R_a\circ\operatorname{Ad}_{K_a}=\operatorname{id}$。
各项 Choi 矩阵均正，而其和是恒等通道的秩一 Choi 矩阵，
所以每项必为该矩阵的非负标量倍，
即 $\mathcal R_a(K_a\rho K_a^*)=p_a\rho$。
取迹，得 $\operatorname{Tr}(\rho K_a^*K_a)=p_a\operatorname{Tr}\rho$，
对全部 Hermitian $\rho$ 成立，故 $K_a^*K_a=p_aI$。
方阵极分解给非零分支为标量乘酉。

□

这把“经典结果加门序列仍保持酉性”拆成可检验的陈述：
完整相干实现保持可恢复性；只留下经典结果与量子后继，
能恢复整个输入空间的恰是已知标签的随机酉情形。
一般测量与阻尼不满足此条件。
若继续在静态整体中保留负责去相干的其他内部角色，
整体描述仍可酉；但这些角色正是必须计入的关系与资源。

<a id="section-8"></a>

## 8 未来闭合：三轴何时是自治状态

来源 v22 的未来商条件指出，某个观察量要承载合法递归，
同一观察纤维中的历史必须有相同的可执行域，
并在每个允许操作后仍落入同一后继观察纤维。
同一当前读数一般不足；还要保留全部允许未来能够区分的关系。
[[5](#bib-v22)]
下面给出量子联合态上的一个刚性版本。

<a id="thm:autonomy"></a>

#### 定理 8.1（全联合态自治迫使乘积酉）

设 $\mathcal H_S,\mathcal H_E$ 有限维，$U$ 是固定的全局酉。
若存在一个仅依赖当前系统边缘的更新 $\Phi$，使

$$
\operatorname{Tr}_E(U\rho_{SE}U^*)=\Phi(\operatorname{Tr}_E\rho_{SE})
\qquad\text{对所有联合密度矩阵 }\rho_{SE},
$$

则存在酉 $W,V$，使

$$
\boxed{U=W\otimes V,\qquad \Phi(\rho)=W\rho W^*.}
$$

**证明。**

先固定一个内部数学状态 $\tau_E$，得到
$\Phi(\rho)=\operatorname{Tr}_E[U(\rho\otimes\tau_E)U^*]$，
故该更新必为线性 CPTP 映射。
由对全部联合态的恒等式及线性张成，Heisenberg 形式为

$$
U^*(A\otimes I)U=\Phi^*(A)\otimes I
\qquad\text{对所有 }A.
$$

左侧是保持乘积与伴随的单射，因而 $\Phi^*$ 是
$M_{\dim S}(\mathbb C)$ 的保单位、单射 $*$ 同态。
有限维同维性使其为自同构。
由矩阵单位可直接选取一个正交基，使该自同构写成
$\Phi^*(A)=W^*AW$。
于是 $U(W^*\otimes I)$ 与每个 $A\otimes I$ 对易；
全矩阵代数的交换子为 $I\otimes M_{\dim E}$，
故它等于 $I\otimes V$，且酉性给 $V$ 酉。

□

本定理的承重词是“所有联合态”。
如果只声明固定 ready 角色上的输入 $\rho\otimes\tau_E$，
并供应足够大的记录空间及适当纯 ready 态，便允许任意 CPTP 通道，
完全不会强迫乘积酉。
因此，固定三轴可完整表达当前 qubit 态，
但要把它作为耦合整体中所有历史的自治递归状态，
必须进一步证明所保留的记忆关系足够，或明确限制可取得输入族。

<a id="statement-8.2"></a>

#### 命题 8.2（ready 复位的内部成本）

若一个酉对每个纯输入均把同一纯 ready 角色送回同一个纯 ready 态，
则诱导的系统通道为酉。

**证明。**

纯全局输出具有纯记录边缘，所以必为
$V|\psi\rangle\otimes|0\rangle$。
整体线性与保内积给 $V$ 线性且 $V^*V=I$；
同维输出使 $V$ 酉。

□

例如内部交换
$|\psi\rangle|0\rangle\mapsto|0\rangle|\psi\rangle$
使系统严格复位，却把信息保留到另一角色；
第二次使用同一交换会把信息送回。
若每步都想表现为同一复位通道，必须补充新的 ready 资源、
合法的记录回收，或足够大的已保留历史。

<a id="thm:recurrence"></a>

#### 定理 8.3（固定有限内部记忆不能永久生成严格收缩半群）

设 $\dim\mathcal H_S\ge2$，$U$ 是固定有限维 $S\otimes E$ 上的酉，
初始内部记录为同一个 $\tau_E$。
不存在严格迹距离收缩系数 $0\le\eta<1$ 的系统通道 $\Phi$，
使对全部 $m\ge0$ 与全部系统输入都有

$$
\operatorname{Tr}_E[U^m(\rho\otimes\tau_E)U^{-m}]=\Phi^m(\rho).
$$

**证明。**

紧性保证存在趋于无穷的整数子列 $m_k$，使 $U^{m_k}\to I$。
具体地，在幂序列中取一个收敛子列并使相邻指标差趋于无穷，
则相邻两项之商趋于 $I$；有限周期情况直接取周期的倍数。
选两个不同系统态 $\rho,\sigma$。
左侧两输出的迹距离沿该子列趋于 $D(\rho,\sigma)>0$，
右侧却不超过 $\eta^{m_k}D(\rho,\sigma)\to0$，矛盾。

□

它只排除固定有限 $U$、同一初始记忆、所有幂次数的同时精确表示。
它不排除有限轮逼近、改变程序、扩张内部记录，
或只为最终通道 $\Phi^m$ 单独编译一个新扩张。
如果必须保留全部 $m$ 个独立 $r$ 标签的完整历史，记录维数至少为 $r^m$；
若只保留最终 qubit 通道，Choi 秩仍不超过四，
二者不能混为同一资源问题。

<a id="section-9"></a>

## 9 两种递归误差：局部收缩与整体相干

<a id="statement-9.1"></a>

#### 命题 9.1（三轴收缩系数与受迫误差级数）

对 qubit CPTP 映射 $r\mapsto Tr+t$，
单体系迹距离收缩系数恰为 $\eta=\|T\|_{\mathrm{op}}\le1$。
若实际已供应可复合的同一逻辑过程，且第 $j$ 步附加逻辑输出误差至多 $\delta_j$，
则

$$
e_{j+1}\le\eta e_j+\delta_j,\qquad
e_m\le\eta^me_0+\sum_{j=0}^{m-1}\eta^{m-1-j}\delta_j.
$$

特别地，$\eta<1$ 且 $\delta_j\le\delta$ 时，

$$
e_m\le\eta^me_0+\frac{\delta(1-\eta^m)}{1-\eta}.
$$

**证明。**

两个 qubit 迹距离是 Bloch 差长度的一半，平移项相消，
故比值的上确界为 $\|T\|_{\mathrm{op}}$。
任意方向都可由两个球内态的差实现；CPTP 收缩给上界一。
三角不等式给一步误差递推，逐次代入得到几何卷积。

□

这给出了用户所说“递归类似级数”的一个精确版本：
稳定性取决于同一过程接口、收缩率及驱动误差的累积。
但该 $\eta$ 是系统边缘上的系数。
如果内部参考可独立携带信息，$\Phi\otimes\operatorname{id}$ 对全部联合态不可能
以同一严格系数缩小所有距离；
相干整体更保持输入区别。

另一条稳定链来自原生等距或酉逼近。
若每个完整实现相对理想步骤的算子误差为 $\epsilon_j$，
望远镜展开给

$$
d_{\rm ref}(\mathcal U_{m:1},\widetilde{\mathcal U}_{m:1})
\le\sum_{j=1}^m\epsilon_j.
$$

若理想完整路径一直留在指定代码内，
实际初始振幅误差为 $\epsilon_0$，则最终代码外质量至多

$$
\left(\epsilon_0+\sum_{j=1}^m\epsilon_j\right)^2.
$$

没有额外去相干或独立性前件时，不得把相干误差改写为
$\sum_j\epsilon_j^2$。
若误差范数可求和，在固定载体上令
$Z_m=(U_m\cdots U_1)^*(\widetilde U_m\cdots\widetilde U_1)$，
则 $\|Z_{m+1}-Z_m\|\le\epsilon_{m+1}$，
所以相对酉乘积由 Cauchy 性得到极限；
酉性本身只给等距稳定，不替代可求和性。

新版精化稿的列随机更新与
$1-\prod_j(1-\epsilon_j)$ 的递归预算，
以及平方根振幅加正交历史后的酉实现，
都应在各自完整条件下使用。
[[6](#bib-refinement), [7](#bib-errorrecursion)]
仅从当前三个均值拟合出一个 CPTP 候选，
不能自动得到独立准备、无隐藏记忆的逐步复合合同。

<a id="sec:rank"></a>

## 10 最新秩边界结果的稳定版本

前面采用声明的 CPTP/Born 接口来表示过程。
本节切换到续卷 II 的另一问题：条件系统终端已经重构，
但记录分支的实际质量 $m_{Si}$ 仍未知。
不能把正在证明的 $m_{Si}=t_{Si}$ 预先放入仪器定义。

<a id="section-10.1"></a>

### 10.1 源码的新有限比较与额外统计前件

续卷 II 的 §126 给出原生正字

$$
C=(K_1K_2\cdots K_{10})(K_0K_1\cdots K_9),
$$

右端先执行，恰为二十次调用，并在完整 $\mathcal H_{89}$ 上证明

$$
C^*N_{\{b_1=i\}}C=M_i.
$$

这是记录投影到旧终端投影的精确转送；没有给最短字结论。
§127 又给两个各两调用的事件

$$
\mathsf R(99,\epsilon),\quad \{i=0\}\times\Omega_{10},
\qquad
\mathsf T(77),\quad \{b_7=1\},
$$

其 ready 压缩签名都严格等于
$\varphi^{-4}I_{\mathcal H_{13}}$。
这些精确矩阵相等并不自动把两种取得程序的实际未知概率判为相等；
来源同时保留了能区分这些事件的非 Born 读者模型。
[[2](#bib-continuation)]

<a id="def:rankcontract"></a>

#### 定义 10.1（两个设置的未知记录质量合同）

设实际供应的同一个内部相干代码输入为

$$
\chi=J_{\rm src}(z_0,0)+J_{\rm src}(z_1,1),\qquad
X=(z_0\ z_1),\quad \operatorname{Tr}(X^*X)=1.
$$

$J_{\rm src}$ 是来源的系统–记录等距，区别于本稿 qubit 五模式码 $J$。
取两个实际设置 $S=I,B$，其中 $B$ 是一次黄金记录混合。
约定

$$
X_S=XS^{\mathsf T},\quad
t_{Si}=\|z_{Si}\|^2,\quad m_{Si}\ge0,\quad \sum_i m_{Si}=1.
$$

实际 $m_{Si}$ 在选择系统后续 $f$ 之前固定；
$t_{Si}=0$ 时要求 $m_{Si}=0$。
正质量分支保留记录的完整代码后继指定为
$J_{\rm src}(z_{Si}/\sqrt{t_{Si}},i)$，
因而其系统条件态为 $z_{Si}/\sqrt{t_{Si}}$，
其条件终端沿用已重构的完整系统终端规则 $q$。
定义忽略记录后的系统关系

$$
A_S=\sum_{i:t_{Si}>0}
m_{Si}\frac{|z_{Si}\rangle\langle z_{Si}|}{t_{Si}}.
$$

本节精确合同明确没有失败分支，两个质量之和即为无条件总质量。
若实际还有失败、弃权或代码外后继，应另列分支并给无条件误差预算，
不能先条件化去掉失败再直接使用后面的定理。

这是额外的实际输入、后继与统计合同。
它不是由任意数学向量 $X$ 的存在、或由有限准备通道源码，自动供应出来的。
在满列秩时，全部 $t_{Si}>0$，可写

$$
D_S=\operatorname{diag}(m_{S0}/t_{S0},m_{S1}/t_{S1}),\qquad
A_S=XS^{\mathsf T}D_S\overline S X^*.
$$

黄金记录块可按来源的相位规范写为

$$
B=
\begin{pmatrix}
-x&y\zeta^{-1}\\
y\zeta^{-1}&-x\zeta^3
\end{pmatrix},\qquad
x=\varphi^{-1},\quad y=\sqrt{x},\quad \zeta=e^{3\pi i/5}.
$$

置

$$
\beta=|B_{00}B_{10}|=xy=\varphi^{-3/2}>0.
$$

完整未来系统终端的精确隔离，结合原生密度，
在来源 §128 中给出 $A_B=A_I$。
以下定理直接处理带误差的关系版本。

<a id="section-10.2"></a>

### 10.2 最小 Gram 特征值控制权重误差

<a id="thm:rankstable"></a>

#### 定理 10.2（秩二记录权重稳定界）

在定义 [10.1](#def:rankcontract) 的合同下，设

$$
G=X^*X,\qquad \kappa_X=\lambda_{\min}(G)>0,
\qquad \|A_B-A_I\|_{\mathrm{op}}\le\eta.
$$

则对 $S=I,B$ 与 $i=0,1$，

$$
\boxed{
|m_{Si}-t_{Si}|
\le \min\left\{1,\frac{\eta}{4\beta\kappa_X}\right\}.
}
$$

其中初始设置还有较细界

$$
|m_{Ii}-t_{Ii}|
\le \frac{t_{I0}t_{I1}\,\eta}{\beta\kappa_X}.
$$

$\eta=0$ 时恢复来源的精确秩二结论。

**证明。**

令 $L=G^{-1}X^*$，则 $LX=I$，且
$LL^*=G^{-1}$，所以 $\|L\|_{\mathrm{op}}^2=1/\kappa_X$。
对关系差左右乘 $L,L^*$，再作酉共轭，得

$$
\left\|D_B-\overline B D_I B^{\mathsf T}\right\|_{\mathrm{op}}
\le\frac{\eta}{\kappa_X}.
$$

令 $D_I=\operatorname{diag}(d_0,d_1)$。
由于 $D_B$ 对角，而 $B$ 的两行正交，
右侧被减矩阵的非对角元为
$\overline{B_{00}}B_{10}(d_0-d_1)$。
故

$$
|d_0-d_1|\le\frac{\eta}{\beta\kappa_X}.
$$

利用 $\sum_i m_{Ii}=\sum_i t_{Ii}=1$，

$$
m_{I0}-t_{I0}
=t_{I0}t_{I1}(d_0-d_1)
=-(m_{I1}-t_{I1}).
$$

由于 $t_{I0}t_{I1}\le1/4$，得初始设置界。

对 $B$ 设置，把基矩阵换为 $X'=XB^{\mathsf T}$，
并在代数中用逆设置 $B^*$ 返回 $X$。
$X'^*X'$ 的最小特征值仍为 $\kappa_X$；
二阶酉矩阵有 $|B_{01}|=|B_{10}|$，逆混合的系数仍为 $\beta$。
重复同一估计即可。这里只交换两个已存在设置的代数角色，
不要求额外供应一个实际逆操作。
概率差至多一给截断。

□

这是一个可识别性稳定定理：两列越接近平行，
系统边缘对未知记录权重越不敏感。
它不以“结果归一了”替代条件数。

<a id="statement-10.3"></a>

#### 推论 10.3（AURIC 球到秩边界的距离）

将已知 Gram 关系写为 $G=(I+r_G\cdot\sigma)/2$，
并用固定数学编码 $u_G=c+\nu r_G$，则

$$
\boxed{
\kappa_X=\frac{1-|r_G|}{2}
=\frac{\nu-\|u_G-c\|}{2\nu}.
}
$$

因此秩二非退化量恰对应 AURIC 球心到其表面所剩的径向余量。
若独立校准给 $\|\widehat u-u_G\|\le\delta$，并且

$$
\underline\kappa
=\frac{\nu-\|\widehat u-c\|-\delta}{2\nu}>0,
$$

可在定理中用 $\underline\kappa$ 替代 $\kappa_X$，得到可靠上界。

**证明。**

迹一 $2\times2$ 正矩阵特征值为 $(1\pm|r_G|)/2$。
最后一式由三角不等式。

□

这里 $G=X^*X$ 是输入列关系的数学 Gram 矩阵。
它不是仍未知的实际记录概率表；
若要把 $u_G$ 当成实验读数，必须另有可靠的输入编码和读口校准。
因此该推论不会循环地使用所要证明的 Born 质量。

<a id="section-10.3"></a>

### 10.3 固定输入的三个有限原生见证

<a id="thm:threewitness"></a>

#### 定理 10.4（三个系统投影见证足以控制隔离残差）

在同一秩二输入合同下，设 $Q=XG^{-1/2}$，
它是从 $\mathbb C^2$ 到 $\operatorname{Ran}X$ 的等距。
置

$$
P_j=(I+\sigma_j)/2,\qquad F_j=QP_jQ^*,\quad j=x,y,z.
$$

则对 $\Delta A=A_B-A_I$，

$$
\boxed{
\|\Delta A\|_{\mathrm{op}}
=\sqrt{\sum_j|\operatorname{Tr}(F_j\Delta A)|^2}.
}
$$

若每个 $F_j$ 用一个原生后续的终端效果 $\widetilde F_j$ 实现，
其算子误差至多 $2\tau_j$；
且两个设置的该完整终端事件概率差已可靠界定为 $r_j$，
则可取

$$
\boxed{
\eta=\sqrt{\sum_j(r_j+4\tau_j)^2}
}
$$

代入定理 [10.2](#thm:rankstable)。

**证明。**

$\Delta A$ 支撑在 $\operatorname{Ran}X$，且 $\operatorname{Tr}\Delta A=0$，
故 $Q^*\Delta A Q=h\cdot\sigma$，$h\in\mathbb R^3$。
$\operatorname{Tr}(P_jh\cdot\sigma)=h_j$，而
$\|h\cdot\sigma\|_{\mathrm{op}}=|h|$，得第一式。

$F_j$ 是 $\mathcal H_{13}$ 上的秩一投影，可选一个数学酉 $U_j$
使固定旧秩一终端效果 $E_w$ 满足 $U_j^*E_wU_j=F_j$。
由原生射影密度，选实际有限后续 $f_j$，使
$\|K_{f_j}-e^{i\theta_j}U_j\|\le\tau_j$；
于是 $\|\widetilde F_j-F_j\|\le2\tau_j$。
两个 $A_S$ 都是密度矩阵，故 $\|\Delta A\|_1\le2$，
从而

$$
|\operatorname{Tr}(F_j\Delta A)|
\le|\operatorname{Tr}(\widetilde F_j\Delta A)|+4\tau_j
\le r_j+4\tau_j.
$$

代入第一式。

□

“有限”指每个已经指定的实际输入、支持与精度下，
只需三个有限原生字的存在性见证；
没有在本轮搜索门字，也没有给调用复杂度。
$r_j$ 是真实概率差的证书，不能直接拿未经置信控制的有限频率充当。
输入准备误差、分支后继误差、码外支撑或丢失质量都需要额外预算；
若 $\operatorname{Tr}\Delta A\ne0$，还需恢复质量坐标，三个无迹见证已不充分。
这也没有把有限测试升级为对任意未知读者规律的无前件证明。

<a id="section-10.4"></a>

### 10.4 无非退化条件时，统一趋零界不存在

<a id="thm:nouniform"></a>

#### 定理 10.5（接近秩一的近似隔离反例）

仅从两个设置的系统终端近似隔离，
不能得到与输入 $\kappa_X$ 无关、且随隔离误差趋零而趋零的
统一记录权重偏差界，即使每个被测输入都具有秩二。

**证明。**

取 $\psi,\psi'$ 为系统正交单位向量，
$r=(|0\rangle+|1\rangle)/\sqrt2$、
$r'=(|0\rangle-|1\rangle)/\sqrt2$。
对 $0<\varepsilon\le1/\sqrt2$，
令 $a=\sqrt{1-\varepsilon^2}$，供应输入

$$
\chi_\varepsilon
=J_{\rm src}(a\psi\otimes r+\varepsilon\psi'\otimes r').
$$

其两列为

$$
z_0=(a\psi+\varepsilon\psi')/\sqrt2,\qquad
z_1=(a\psi-\varepsilon\psi')/\sqrt2.
$$

因此 $t_{I0}=t_{I1}=1/2$，
$G$ 的特征值为 $1-\varepsilon^2,\varepsilon^2$，
故 $\kappa_X=\varepsilon^2>0$。

在未知质量合同内指定 $m_I=(1,0)$、$m_B=t_B$。
它们归一、符合支撑要求，并在后续选择前固定；
正质量分支仍取已声明的投影归一后继。
于是

$$
\begin{aligned}
A_I&=|a\psi+\varepsilon\psi'\rangle
       \langle a\psi+\varepsilon\psi'|,\\
A_B&=XX^*
=a^2|\psi\rangle\langle\psi|
+\varepsilon^2|\psi'\rangle\langle\psi'|.
\end{aligned}
$$

两者差仅有大小为 $a\varepsilon$ 的非对角项，故

$$
\|A_B-A_I\|_{\mathrm{op}}
=\tfrac12\|A_B-A_I\|_1
=\varepsilon\sqrt{1-\varepsilon^2}\longrightarrow0.
$$

对每个旧原生后续，完整系统终端分布的总变差都不超过这个量，
无需乘 $1024$ 标签数；
但 $|m_{I0}-t_{I0}|=1/2$ 始终不变。
任何仅依赖上述隔离误差且趋零的统一界，均与此矛盾。

□

该反例属于所列未知读者合同，
不是普通 Born/Lüders 仪器内的反例；
也不声称保留来源全部旧校准族或其固定反模型的全部条件。
它排除了完全删除退化参数的做法，
但不证明充分上界中的 $1/\kappa_X$ 阶或常数最优。
退化来自系统边缘对记录权重的失敏；
仅说“连续”而不给共同输入域、隔离预算与连续模，也不会自动提供统一定量界。

<a id="section-10.5"></a>

### 10.5 跨越秩一边界的定量连续桥

<a id="thm:bridge"></a>

#### 定理 10.6（可取得邻域与连续模下的边界稳定）

设秩一目标输入为
$\chi_0=J_{\rm src}(\psi\otimes r)$。
同一实际记录规则在下列可取得输入族上满足

$$
|m_0(\chi_\tau)-m_0(\chi_0)|\le\omega(\tau),
$$

其中

$$
\chi_\tau
=J_{\rm src}\!\left(
\sqrt{1-\tau^2}\,\psi\otimes r+\tau\psi'\otimes r'
\right),\qquad 0<\tau\le1/\sqrt2,
$$

$\psi'\perp\psi$、$r'\perp r$，且都为单位向量。
每个 $\chi_\tau$ 的 $I,B$ 两设置都须满足
定义 [10.1](#def:rankcontract) 的全部合同，并共用同一重构条件终端 $q$。
若该输入的关系隔离残差不超过 $\eta_\tau$，
则

$$
\boxed{
|m_0(\chi_0)-t_0(\chi_0)|
\le\omega(\tau)+\tau^2+\frac{\eta_\tau}{4\beta\tau^2}.
}
$$

若 $\omega(\tau)\le L\tau$、$\eta_\tau\le\eta$，
且 $0<\eta\le2^{-3/2}$，
取 $\tau=\eta^{1/3}$ 得

$$
\boxed{
|m_0(\chi_0)-t_0(\chi_0)|
\le\left(L+\frac1{4\beta}\right)\eta^{1/3}+\eta^{2/3}.
}
$$

**证明。**

该 Schmidt 形式给
$\kappa_{X_\tau}=\tau^2$，
且纯联合态迹距离 $D(\chi_\tau,\chi_0)=\tau$。
其记录约化关系为
$(1-\tau^2)|r\rangle\langle r|+\tau^2|r'\rangle\langle r'|$，
所以指定记录投影的平方质量改变至多 $\tau^2$。
在满秩输入处用定理 [10.2](#thm:rankstable)，
再沿
$m_0(\chi_0)$、$m_0(\chi_\tau)$、
$t_0(\chi_\tau)$、$t_0(\chi_0)$
用三角不等式，得到第一式。
代入 $\tau=\eta^{1/3}$ 得第二式，精度范围保证 $\tau\le1/\sqrt2$。

□

若 $\eta_\tau=0$ 且 $\omega(\tau)\to0$，
令 $\tau\downarrow0$ 即恢复来源的秩一延拓。
若有统一非零误差，上式给一个明确可行的边界率；
并未宣称指数最优。
实际可取得输入族、同一规则的连续模及制备可靠性，
都是该桥的独立前件。
来源 §§129–130 已给出终端连续而记录规则不连续的完整反模型，
因此不能从终端的连续性替代这里的记录连续性。
[[2](#bib-continuation)]

<a id="section-11"></a>

## 11 可证明的统一语义与下一条闭合链

<a id="statement-11.1"></a>

#### 定义 11.1（可复合的 AURIC 过程接口）

一个可复合接口须同时声明：
正的二元输入关系及其固定编码；线性过程与全部内部参考上的正性；
实际可取得的准备、原生操作及读出；
完整分支质量、后继和内部记忆；以及这些对象上的可靠误差界。
对允许的后续，当前保留关系还须满足未来商的一致性。

<a id="statement-11.2"></a>

#### 定理 11.2（条件性的通用过程表示）

对一个已经声明的 qubit CPTP 过程，固定 AURIC 码给出
三轴仿射表示与保关系的五矩线性复合；
四个独立输入的三轴表完整确定它。
其最小相干记录维数为 Choi 秩，至多为四。
在既有原生密度、适当 ready 输入和完整终端统计接口下，
该过程的相干扩张及分支五概率可由上述八十九维二十路径代码任意逼近。
酉门恰为其中 Choi 秩一的子类。

**证明。**

依次应用定理 [3.2](#thm:lift)、[3.4](#thm:choi)、[4.1](#thm:tetra)
以及 [6.3](#thm:89)；Choi 秩一的判据已在第 3 节证明。

□

这一语义覆盖的是已给定正关系、过程与取得接口的二元量子模型。
“任何概念都由宇宙本体门序列读出”仍是待给出编码和经验接口的整体解释前件；
不能从两个语言标签的存在直接推出复线性、完全正性、
任意输入供应或实际 Born 统计。

| 要保存的对象 | 已证明的控制量 | 仍须供应的接口 |
| --- | --- | --- |
| 单个逻辑态 | 三轴球、质量与关系式 | 固定码和读口校准 |
| 固定逻辑过程 | $(T,t)$ 与 Choi 正性 | 同一输入上下文、完整参考域 |
| 相干记录的过程 | 等距、原生逼近误差 | ready 资源、具体记录编码 |
| 经典分支后的恢复 | $K_a^*K_a=p_aI$ | 标签保留与条件恢复操作 |
| 逐步未来预测 | 观察纤维后继一致性 | 内部记忆或受限可取得域 |
| 秩二记录权重 | $\eta/(4\beta\kappa_X)$ | 投影后继、隔离、因果质量 |
| 秩一边界的权重 | 连续模与邻域误差平衡 | 实际邻域输入、同一规则的可靠连续模 |

<a id="bibliography"></a>

## 固定来源与证据范围

<a id="bib-head"></a>

**[1]** 
The Omega Institute.
[本轮固定公开提交：621108f17bf2a14](https://github.com/the-omega-institute/trureturing/commit/621108f17bf2a141b2605ddad479f28ed6ac4bbd)。
当前分支快照与 v37 基线之间的文件比较、下载和 Git blob 核对，
属于来源检查，未执行库内数学程序。

<a id="bib-continuation"></a>

**[2]** 
[AURIC：量子原则与相干重构续卷 II](https://github.com/the-omega-institute/trureturing/blob/621108f17bf2a141b2605ddad479f28ed6ac4bbd/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_II.md)。
消费未变的 §77、§100、§§121–125；
本轮新增重点为 §§126–131。
完整阅读新增正文、前件、证明及来源边界。
这些新增结果自行标明为普通数学条件论证，并非本轮 Lean 编译。

<a id="bib-prepare"></a>

**[3]** 
[FinitePreparationChannel.lean](https://github.com/the-omega-institute/trureturing/blob/621108f17bf2a141b2605ddad479f28ed6ac4bbd/D5/S3/Quantum/Foundation/FinitePreparationChannel.lean)。
完整阅读有限制备与带参考局部制备两个声明及证明源码。
未运行 Lean；代码中的通道存在不等于原生操作菜单的实际供应。

<a id="bib-golden"></a>

**[4]** 
[固定黄金门与辫群相容性](https://github.com/the-omega-institute/trureturing/blob/621108f17bf2a141b2605ddad479f28ed6ac4bbd/docs/develop/theory/AURIC_FIXED_GOLDEN_GATE_AND_BRAID_COMPATIBILITY_ZH.md)；
[黄金门通用性与算术边界 v15](https://github.com/the-omega-institute/trureturing/blob/621108f17bf2a141b2605ddad479f28ed6ac4bbd/docs/develop/theory/AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md)。
与续卷 II 的具体载体密度供应共同使用；
v37 已给的固定五效果编码由本稿第 2 节完整重述。

<a id="bib-v22"></a>

**[5]** 
[相对门历史、观察商与递归闭合 v22](https://github.com/the-omega-institute/trureturing/blob/621108f17bf2a141b2605ddad479f28ed6ac4bbd/docs/develop/theory/AURIC_RELATIVE_GATE_HISTORIES_OBSERVATION_QUOTIENTS_AND_RECURSIVE_CLOSURE_V22.md)，特别是 §8。
当前状态读数相同不等于未来可继续商化；
本轮重读其合法域、纤维条件及未来效果张成的界限。

<a id="bib-refinement"></a>

**[6]** 
[保守三轴精化、最优素数修复与进展链](https://github.com/the-omega-institute/trureturing/blob/621108f17bf2a141b2605ddad479f28ed6ac4bbd/docs/develop/theory/AURIC_CONSERVATIVE_THREE_AXIS_REFINEMENT_OPTIMAL_PRIME_REPAIR_AND_ROBIN_PROGRESS_CHAINS.md)，§§1–4。
仅消费三轴精化及误差预算的接口，
不把其中的列随机更新称为同维酉门。

<a id="bib-errorrecursion"></a>

**[7]** 
[三轴最优误差递归与扩展素数判据](https://github.com/the-omega-institute/trureturing/blob/621108f17bf2a141b2605ddad479f28ed6ac4bbd/docs/develop/theory/AURIC_THREE_AXIS_OPTIMAL_ERROR_RECURSION_AND_EXPANDED_PRIME_ROBIN_CRITERION.md)，§§1–3。
消费误差乘积与平方根振幅、正交历史扩张的区别。

<a id="bib-rooted"></a>

**[8]** 
[递归关系观察与有根边界历史恢复](https://github.com/the-omega-institute/trureturing/blob/621108f17bf2a141b2605ddad479f28ed6ac4bbd/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ROOTED_BOUNDARY_HISTORY_RECOVERY.md)。
新增噪声恢复条款需要深度与联合误差合同；
本稿不把它替代为一般量子过程闭合定理。

<a id="bib-watrous"></a>

**[9]** 
John Watrous.
[The Theory of Quantum Information，作者公开预出版稿](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)，2018。
标准背景为 §2.2.2、定理 2.22 与 2.26。
本文采用归一 Choi 约定，所有所需有限维步骤均已在正文写出。
作者正文是标准量子通道背景，不是本项目新增结论的认证。
