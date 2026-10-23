# AURIC FIB：可取得预测丛、加权恢复与证书成本

## 1. 许可实验、资源与既有预测商

### 可取得预测系统的基本数据


**定义 1.1（带资源的预测系统）。** <a id="def:system"></a>
一个有限维带资源预测系统包括以下数据：


-  参数空间 $B$，以及其上秩为 $d$ 的 Hermitian 向量丛
$\mathscr H\to B$；固定参数时状态为
$\rho\succeq0,\ \operatorname{tr}\rho=1$。

-  许可协议族 $\mathcal L_b$。每个协议必须指定动作顺序、可见输出、
允许的反馈和停止规则。量子协议用完全正的输出解析映射表示，
每一完整仪器的各分支之和保持迹。

-  每个协议 $\pi$ 的记录空间，以及事件 $A$ 的效果
$E_{\pi,A}(b)$，满足

$$

0\preceq E_{\pi,A}\preceq I,\qquad
\mathbb P_\rho^\pi(A)=\operatorname{tr}(\rho E_{\pi,A}).

$$

该效果由协议的对偶映射合成得到，不是额外的免费测量。

-  动作、准备、读出与存储的成本规则 $c$，以及明确的资源供给规则
$\mathcal R$：例如是否能复位、是否能独立重备同一未知来源、
能否使用辅助系统及相位参考。

-  所需预测量或任务 $\mathcal T$；涉及统计估计时，还要给出噪声模型、
精度、失败概率及样本分配。


成本比较仅在相同资源合同下进行。某个数学效果属于线性包络，
并不自行提供取得其期望值的实验。


所有未来效果的实线性空间以及其无迹部分分别记为

$$

\mathcal W_b=\operatorname{span}_{\mathbb R}
  \bigl(\{I\}\cup\{E_{\pi,A}(b):\pi\in\mathcal L_b\}\bigr),
\qquad
W_b=\left\{E-\frac{\operatorname{tr}E}{d}I:E\in\mathcal W_b\right\}.

$$

令 $V_b=\operatorname{Herm}_0(\mathscr H_b)$，赋予
$\langle X,Y\rangle=\operatorname{tr}(XY)$，并定义
$N_b=W_b^\perp$。下文 $W_b$ 的维数总指无迹方向数；
$\mathcal W_b$ 的维数比它多一，不能混用。


**假设 1.2（既有全未来商的对应）。** <a id="prop:exactquotient"></a>
采用 [关系丛卷定理 8.4、8.6](AURIC_FIB_RELATIONAL_BUNDLE_AND_PREDICTIVE_CLOSURE_THEORY.md#obs-thm-predictive) 的全未来商、最小仿射摘要和常秩像核丛。该卷未中心化效果空间 $W_\infty$ 在这里记为 $\mathcal W_b$；其 $W^0$ 在这里记为 $W_b$，故若 $\dim W_b=r$，则 $\dim\mathcal W_b=r+1$。具体地，全部记录律相等等价于 $\rho-\sigma\in N_b$，投影 $\rho\mapsto P_{W_b}(\rho-I/d)$ 是最小仿射充分摘要。

仿射维数的必要性取来源类为全部密度态，或在声明的实际仿射包络内含相对开集的来源类；任意受限来源子集不自动继承同一维数下界。对全部有限反馈协议，必须包含每个记录事件的效果。分支逐项闭合才允许商更新；归一化后验只在该分支概率严格正时定义。数学投影联络不供应可执行控制。

### 从局部矩阵回到真正的向量丛

在 $\mathscr H$ 的局部酉标架中，把有限个中心化效果写成列矩阵 $C$。
更换酉标架时，$V$ 上的变换是实正交变换 $R$，
于是

$$

C\longmapsto RC,\quad G\longmapsto RGR^{\mathsf T},
\quad W\longmapsto RW,\quad N\longmapsto RN.

$$

因此恒秩域上的像与核、正交投影及 Gramian 的谱都能按丛的方式粘合。
不同局部坐标不改变它们的数学对象身份。
若 $\mathscr H$ 本来带有酉联络，则可把诱导联络投影到 $W$；
在这里的平凡环境丛实例中，它就是 $\nabla=P\,d$。

以下三种数据仍须分别保留：

$$

\underbrace{\dim W}_{\text{精确可分方向}},
\qquad
\underbrace{\lambda_{\min}^{+}(G)}_{\text{给定读出与噪声下的稳定性}},
\qquad
\underbrace{c(\pi),\ \mathcal R}_{\text{取得这些读出的资源}}.

$$

后文给出严格反例，证明其中任何一个都不能无条件替代另外两个。


## 2. 有限许可面板的加权预测与具体秩几何

<a id="obsq:sec"></a>

有限未来闭包回答哪些状态差异能够被允许实验分辨。本节在这个代数问题上增加三个明确结构：效果坐标的噪声度量、实验的重复制备合同，以及参数变化的正则性。由此得到稳定重建、任务误差和样本代价的可证明界。这里的 Gramian 特征值与任务相对逃逸风险是两种对象；前者须先声明算子内积和数据度量，后者还依赖任务与来源分布，不能只凭名称相同而等同。


### 效果矩阵、常秩子丛与观测谱隙


**应用 2.0（弱量子读口、球面菜单与 FIB 面板的加权恢复）。** 对命题 2.9 的弱量子读口、命题 2.13 的球面菜单及定理 3.3 的 FIB 面板，按定义 2.1 指定权重与概率基线。它们的目标 $T$ 的精确可恢复性由 $f\in W$ 决定；含自由截距的仿射最坏误差是计算 2.6 的残差算子范数加噪声对偶范数；同源独立准备时的方差、尾界与谱截断误差分别由计算 2.7、2.8 给出。若这些列张成所有未来事件的中心化空间，则计算 2.3 的总变差界适用于该菜单的全部单次有限反馈记录。具体来源、效果、秩损失与拓扑分别在命题 2.9、2.10、2.13 和第 3 节给出；计算 3.7 把目标风险与采样常数代入指定 FIB 面板。

以下各项是这些具体应用的支持计算，采用经典 Moore–Penrose 逆与 SVD 的有限维方法 [Penrose](#ref-penrose)、固定秩广义逆的局部正则性 [Golub–Pereyra](#ref-golub)，以及独立有界变量的浓缩方法 [Hoeffding](#ref-hoeffding)。显示的推导保留应用所需的参数与归一化，不把这些经典工具另算为新的独立结果。

**定义 2.1（中心化效果矩阵与加权 Gramian）。**
<a id="obsq:def:gramian"></a>
固定 $H=\mathbb C^d$，令

$$

 V_0=\operatorname{Herm}_0(H),\qquad
 \langle X,Y\rangle=\operatorname{Tr}(XY),\qquad D=d^2-1.

$$

固定 $V_0$ 的一个实正交规范基。设 $E_1(b),\ldots,E_m(b)$ 是在参数 $b$ 处允许执行的有限实验的事件效果，满足 $0\le E_j(b)\le I$。定义

$$

 F_j=E_j-\frac{\operatorname{Tr}E_j}{d}I,\qquad
 C=[F_1\ \cdots\ F_m]:\mathbb R^m\longrightarrow V_0,
 \qquad p_j^0=\frac{\operatorname{Tr}E_j}{d}.

$$

这里沿用效果作为列的约定。因此对 $x=\rho-I/d$，实际概率向量满足

$$

 p(\rho)-p^0=C^{\mathsf T}x.

$$

给定正定实对称矩阵 $\Omega$，定义

$$

 G=C\Omega C^{\mathsf T},\qquad
 W=\operatorname{ran}C,\qquad N=\ker C^{\mathsf T}=W^\perp,
 \qquad P=\text{到 }W\text{ 的正交投影}.

$$

$G^+$ 表示 Moore--Penrose 逆。在 $\operatorname{rank}C>0$ 时，记

$$

 \lambda_+=\lambda_{\min}^{+}(G),\qquad \sigma=\sqrt{\lambda_+}.

$$

$\lambda_{\min}^{+}$ 只取严格正的特征值；跨越秩变化处时，它不必连续。


一个列可以对应一条有许多实际输出分支的完整实验；它不要求各列属于同一个联合 POVM。也不能把一个在数学上存在、但在权限或控制合同下无法取得的效果加入 $C$。若有限词闭包证明了这些列张成全部允许未来效果的中心化部分，$W$ 才具有全未来充分性。

$\Omega$ 指定的是数据尺度。例如，独立重复数给出一种自然选择。效果重新编码后，必须同时变换噪声度量才能比较同一个统计问题。只有秩与核不依赖任意正定权重；非零特征值及其条件数依赖已声明的度量。


**计算 2.2（常秩预测子丛与平滑广义逆）。**
<a id="obsq:thm:bundle"></a>
设 $B$ 为光滑流形，$C(b)$、$\Omega(b)$ 光滑，且 $\Omega(b)\succ0$。在开域 $U\subset B$ 上，若 $\operatorname{rank}C(b)=r$ 恒定，则 $W_b,N_b$ 是秩分别为 $r,D-r$ 的光滑实子丛，$P_b,G_b^+$ 光滑。若 $r>0$，则 $\sigma(b)$ 连续且严格正；对每个紧集 $K\subset U$，存在 $\sigma_K>0$ 使 $\sigma(b)\ge\sigma_K$。


**证明。**
在任一点附近选取 $r$ 个独立列，组成 $D\times r$ 矩阵 $B_0$。常秩保证其余列均在这些列的张成中；令

$$

 H_0=B_0^{\mathsf T}B_0,\qquad
 R=H_0^{-1}B_0^{\mathsf T}C,\qquad S=R\Omega R^{\mathsf T}.

$$

于是 $C=B_0R$，$R$ 满行秩，$S\succ0$，并且

$$

 P=B_0H_0^{-1}B_0^{\mathsf T},\qquad
 G^+=B_0H_0^{-1}S^{-1}H_0^{-1}B_0^{\mathsf T}.

$$

直接相乘得 $GG^+=G^+G=P$；这些矩阵对称，故满足广义逆的四个定义等式。公式证明局部光滑性，且不同局部公式均等于唯一的正交投影或广义逆，因此拼接一致。$P$ 与 $I-P$ 的像分别给出两个子丛。

实对称矩阵按大小排列的特征值连续；常秩使最小正特征值始终是同一序号的特征值，故连续且正。紧集上的正连续函数有正的最小值。$r=0$ 时 $P=G^+=0$，子丛结论仍成立，但不定义正谱隙。


证毕。


**计算 2.3（定量可观测性与全未来统计的稳定性）。**
<a id="obsq:thm:frame"></a>
固定参数并假设 $r>0$。对任意 $x\in V_0$，有


<a id="obsq:eq:frame"></a>
$$

 \lambda_+\|Px\|_{\mathrm{HS}}^2
 \le\|\Omega^{1/2}C^{\mathsf T}x\|_2^2
 \le\lambda_{\max}(G)\|Px\|_{\mathrm{HS}}^2.


$$

若数据为 $y=C^{\mathsf T}x+\eta$，则线性重建

$$

 \widehat x=G^+C\Omega y

$$

满足


<a id="obsq:eq:inverse"></a>
$$

 \|\widehat x-Px\|_{\mathrm{HS}}
 \le\frac{\|\Omega^{1/2}\eta\|_2}{\sigma}.


$$

右侧常数 $1/\sigma$ 是这一线性逆的精确算子范数。

另假设 $W+\mathbb RI$ 包含每个允许的有限反馈协议的全部记录事件效果。对任意两态 $\rho,\rho'$ 和任意这样的协议 $\pi$，其完整记录律满足


<a id="obsq:eq:future-tv"></a>
$$

 \operatorname{TV}(\mathbb P_\rho^\pi,\mathbb P_{\rho'}^\pi)
 \le\min\left\{1,
 \frac{\sqrt d}{2\sigma}
 \|\Omega^{1/2}C^{\mathsf T}(\rho-\rho')\|_2\right\}.


$$

这里比较的是同一系统输入下的单次允许协议；任意增加独立副本的统计实验不自动包含在这个合同内。


**证明。**
令 $A=\Omega^{1/2}C^{\mathsf T}$，则 $A^{\mathsf T}A=G$，$\ker A=N$。在 $W$ 上对 $G$ 用谱定理即得式（[2.3](#obsq:eq:frame)）。又有

$$

 \widehat x=G^+Gx+G^+A^{\mathsf T}\Omega^{1/2}\eta
 =Px+A^+\Omega^{1/2}\eta.

$$

$A$ 的非零奇异值平方恰为 $G$ 的正特征值，所以 $\|A^+\|=1/\sigma$；沿最小奇异值对应的左奇异向量选择噪声可取等号。这是线性逆的精确噪声放大陈述，不等于声称非物理的任意算子扰动都能作为密度态输入。

对任一记录事件 $S$，协议给出效果 $0\le E_S\le I$。分支效果对叶求和仍属于所声明的效果空间，所以 $E_S^0=E_S-\operatorname{Tr}(E_S)I/d\in W$。若 $\mu=\operatorname{Tr}(E_S)/d$，则

$$

 \|E_S^0\|_{\mathrm{HS}}^2
 =\operatorname{Tr}(E_S^2)-d\mu^2
 \le d\mu(1-\mu)\le d/4.

$$

以 $\Delta=\rho-\rho'$，有

$$

 |\operatorname{Tr}(E_S\Delta)|
 =|\langle E_S^0,P\Delta\rangle|
 \le\frac{\sqrt d}{2}\|P\Delta\|_{\mathrm{HS}}.

$$

再用式（[2.3](#obsq:eq:frame)），并对所有记录事件取上确界，即得总变差界。


证毕。


**计算 2.4（可取得的差异读口）。**
<a id="obsq:cor:witness"></a>
在计算[2.3](#obsq:thm:frame)的条件下，设各权重 $w_j>0$，且

$$

\Omega=\operatorname{diag}(w_1,\ldots,w_m).

$$

则对每个迹零 $\Delta$，

$$

 \max_j|\operatorname{Tr}(E_j\Delta)|
 \ge\sqrt{\frac{\lambda_+}{\sum_jw_j}}\,\|P\Delta\|_{\mathrm{HS}}.

$$

因此，若有限候选失败对均满足 $\|P\Delta\|_{\mathrm{HS}}\ge s>0$，且
$2\varepsilon<s\sqrt{\lambda_+/\sum_jw_j}$，每对都有一个合法读口，其概率差严格超过 $2\varepsilon$。


**证明。**
由式（[2.3](#obsq:eq:frame)）及加权最大值界，

$$

 \lambda_+\|P\Delta\|^2
 \le\sum_jw_j|\operatorname{Tr}(E_j\Delta)|^2
 \le\left(\sum_jw_j\right)\max_j|\operatorname{Tr}(E_j\Delta)|^2.

$$

严格阈值结论随即成立。若某个失败对满足 $P\Delta=0$，本推论不产生证书，必须增加实际可取得的信息。


证毕。


### 目标效果的精确预测与鲁棒误差


**计算 2.5（目标预测的核判据及最小噪声放大）。**
<a id="obsq:thm:target"></a>
给定 Hermitian 目标 $T$，记 $f=T-\operatorname{Tr}(T)I/d$。以下条件等价：



-  存在某个函数，能由 $p(\rho)$ 对全部密度态精确决定 $\operatorname{Tr}(T\rho)$；

-  $f\perp N$；

-  $f\in\operatorname{ran}C$；

-  存在系数 $\alpha$，使 $C\alpha=f$，从而以仿射公式精确预测目标。


在这些条件成立时，若中心化数据噪声满足 $\|\Omega^{1/2}\eta\|_2\le\delta$，所有精确仿射公式中的最小最坏噪声误差为


<a id="obsq:eq:target-opt"></a>
$$

 \delta\sqrt{f^{\mathsf T}G^+f},\qquad
 \alpha_* =\Omega C^{\mathsf T}G^+f


$$

是唯一具有最小加权系数范数的选择。


**证明。**
若 $X\in N$，取足够小的 $t>0$，使 $\rho_\pm=I/d\pm tX$ 均为密度态。二者全部当前读出相同。任何精确函数必须给相同目标，因此 $2t\langle f,X\rangle=0$，得到 $f\perp N$。有限维正交补恒等式给 $N^\perp=\operatorname{ran}C$，而 $C\alpha=f$ 直接给

$$

 \operatorname{Tr}(T\rho)
 =\frac{\operatorname{Tr}T}{d}+\alpha^{\mathsf T}(p(\rho)-p^0).

$$

这也证明允许非线性解码不能越过该核障碍。

固定 $\alpha$ 时，噪声球上的精确最坏误差为 $\delta\|\Omega^{-1/2}\alpha\|_2$。式（[2.5](#obsq:eq:target-opt)）满足 $C\alpha_*=GG^+f=f$。任一其他解可写为 $\alpha_*+h$，其中 $Ch=0$，且

$$

 \alpha_*^{\mathsf T}\Omega^{-1}h=(G^+f)^{\mathsf T}Ch=0.

$$

加权勾股恒等式证明唯一极小性；最后
$\alpha_*^{\mathsf T}\Omega^{-1}\alpha_*=f^{\mathsf T}G^+GG^+f=f^{\mathsf T}G^+f$。


证毕。


**计算 2.6（包含截距的精确鲁棒风险公式）。**
<a id="obsq:thm:risk"></a>
测得 $\widehat p=p(\rho)+\eta$，仍假设 $\|\Omega^{1/2}\eta\|_2\le\delta$。对固定仿射预测器 $\widehat t=\beta+\alpha^{\mathsf T}\widehat p$，有


<a id="obsq:eq:robust"></a>
$$

 \sup_{\rho\in\mathcal D(H),\,\|\Omega^{1/2}\eta\|\le\delta}
 |\operatorname{Tr}(T\rho)-\widehat t|
 =\left\|T-\sum_j\alpha_jE_j-\beta I\right\|_{\mathrm{op}}
  +\delta\|\Omega^{-1/2}\alpha\|_2.


$$

固定 $\alpha$ 而优化截距时，第一项的最小值为

$$

 \frac12\left(\lambda_{\max}\left(T-\sum_j\alpha_jE_j\right)
 -\lambda_{\min}\left(T-\sum_j\alpha_jE_j\right)\right).

$$

若明确把预测器在 $I/d$ 上的值固定为 $\operatorname{Tr}(T)/d$，则截距被固定，式（[2.6](#obsq:eq:robust)）化为

$$

 \|f-C\alpha\|_{\mathrm{op}}+\delta\|\Omega^{-1/2}\alpha\|_2.

$$

一般 $d\ge3$ 时，中心化残差的算子范数与其半谱直径不能互换。


**证明。**
令 $R=T-\sum_j\alpha_jE_j-\beta I$。误差为 $\operatorname{Tr}(R\rho)-\alpha^{\mathsf T}\eta$。密度态上线性泛函的最大绝对值是 $\|R\|_{\mathrm{op}}$，由对应极端本征态达到；噪声球上 $|\alpha^{\mathsf T}\eta|$ 的最大值是 $\delta\|\Omega^{-1/2}\alpha\|$。噪声球关于零对称，可以选择噪声符号使二者相加，所以三角上界恰可达到。

若 $a,b$ 是 $T-\sum_j\alpha_jE_j$ 的最小、最大特征值，则对截距的优化为
$\min_\beta\max\{|a-\beta|,|b-\beta|\}=(b-a)/2$，由 $\beta=(a+b)/2$ 达到。固定在最大混态的预测值则强制
$\beta=\operatorname{Tr}(T)/d-\sum_j\alpha_jp_j^0$，残差正好是 $f-C\alpha$。


证毕。


这一等式同时处理可见方向中的噪声放大与目标在不可见方向中的偏差。它是一个声明噪声球后的最坏风险公式；若要计算仓库式的 Bayes 风险，还须指定来源先验、任务损失以及噪声分布。


### 独立重备样本与阈值谱正则化


**计算 2.7（独立副本下的方差、尾界与可见态均方误差）。**
<a id="obsq:thm:sampling"></a>
对每个 $j$，在 $n_j\ge1$ 个独立新制备的同一来源副本上测量二元 POVM $(E_j,I-E_j)$，且各组相互独立。记经验概率为 $\widehat p_j$，并定义

$$

 D_n=\operatorname{diag}(n_1,\ldots,n_m),\qquad G_n=CD_nC^{\mathsf T}.

$$

若 $f\in W$，用 $\alpha_*=D_nC^{\mathsf T}G_n^+f$ 作无偏目标估计，则

$$

 \operatorname{Var}(\widehat t)\le\frac14 f^{\mathsf T}G_n^+f,
 \qquad
 \mathbb P(|\widehat t-\operatorname{Tr}(T\rho)|\ge u)
 \le2\exp\left(-\frac{2u^2}{f^{\mathsf T}G_n^+f}\right),\quad u>0.

$$

若分母为零，则估计误差恒为零。对线性可见态估计

$$

 \widehat x=G_n^+CD_n(\widehat p-p^0)

$$

还有

$$

 \mathbb E\widehat x=Px,\qquad
 \mathbb E\|\widehat x-Px\|_{\mathrm{HS}}^2
 \le\frac14\operatorname{Tr}(G_n^+).

$$

上述界适用于无约束线性估计；不要求输出本身是密度态。


**证明。**
令 $\eta=\widehat p-p(\rho)$。独立性给

$$

 \mathbb E\eta=0,\qquad
 \operatorname{Cov}(\eta)
 =\operatorname{diag}\left(\frac{p_j(1-p_j)}{n_j}\right)
 \preceq\frac14D_n^{-1}.

$$

故 $\operatorname{Var}(\alpha^{\mathsf T}\eta)\le\frac14\alpha^{\mathsf T}D_n^{-1}\alpha$。上一条最小范数结论给 $\alpha_*^{\mathsf T}D_n^{-1}\alpha_*=f^{\mathsf T}G_n^+f$。同理，可见态估计的协方差满足

$$

 \operatorname{Cov}(\widehat x)
 \preceq\frac14G_n^+CD_nC^{\mathsf T}G_n^+
 =\frac14G_n^+.

$$

取迹给均方界。

为使尾界自足，设 $B$ 是参数为 $p$ 的 Bernoulli 变量，$h(t)=\log\mathbb E e^{t(B-p)}$。有 $h(0)=h'(0)=0$，而 $h''(t)$ 是倾斜 Bernoulli 分布的方差，不超过 $1/4$，所以 $h(t)\le t^2/8$。目标误差为各独立变量
$\alpha_j(B_{j,k}-p_j)/n_j$ 的和，其矩母函数至多为

$$

 \exp\left(\frac{t^2}{8}\sum_j\frac{\alpha_j^2}{n_j}\right).

$$

对 $t>0$ 用 Markov 不等式并在 $t$ 上优化，得到单侧界
$\exp[-2u^2/(\sum_j\alpha_j^2/n_j)]$；负侧相同，两侧相加即得结论。


证毕。


这里的 $n_j$ 是新副本数，不是对同一个未知系统连续作用 $n_j$ 次的门数。中途测量造成的后验依赖、跨组相关噪声、参数校准误差或未知的制备漂移，均须另给合同后才能改变此定理。


**计算 2.8（阈值可见空间与偏差--噪声分解）。**
<a id="obsq:thm:threshold"></a>
固定 $\tau>0$。定义

$$

 P_\tau=\sum_{\lambda\ge\tau}P_\lambda,
 \qquad G_\tau^+=\sum_{\lambda\ge\tau}\lambda^{-1}P_\lambda,
 \qquad \widehat x_\tau=G_\tau^+C\Omega y,

$$

其中 $P_\lambda$ 是 $G$ 的正交谱投影。若 $y=C^{\mathsf T}x+\eta$ 且
$\|\Omega^{1/2}\eta\|\le\delta$，则


<a id="obsq:eq:threshold"></a>
$$

 \|\widehat x_\tau-x\|_{\mathrm{HS}}^2
 \le\|(I-P_\tau)x\|_{\mathrm{HS}}^2+\frac{\delta^2}{\tau}.


$$

若只比较真正可见部分 $Px$，第一项可换成 $\|(P-P_\tau)x\|^2$。

在一个光滑参数域上，若阈值两侧存在共同开缝，即某个 $a>0$ 满足
$\operatorname{spec}G(b)\cap(\tau-a,\tau+a)=\varnothing$，则 $P_\tau$ 与 $G_\tau^+$ 光滑，$\operatorname{ran}P_\tau$ 在各连通分支上有固定秩。没有这个谱缝时，截断投影可以在特征值穿过阈值时跳变。


**证明。**
有 $G_\tau^+G=P_\tau$，从而

$$

 \widehat x_\tau-x
 =-(I-P_\tau)x+G_\tau^+C\Omega\eta.

$$

右边两项分别属于 $\ker P_\tau$ 与 $\operatorname{ran}P_\tau$，故正交。算子 $G_\tau^+C\Omega^{1/2}$ 的非零奇异值为被保留的 $\lambda^{-1/2}$，均不超过 $\tau^{-1/2}$；勾股恒等式给式（[2.8](#obsq:eq:threshold)）。

在任一点的足够小邻域，选复平面中的闭曲线包围阈值上方的特征值而避开其余谱。有限维谱定理逐项验证

$$

 P_\tau=\frac{1}{2\pi i}\oint(zI-G)^{-1}\,dz,
 \qquad
 G_\tau^+=\frac{1}{2\pi i}\oint z^{-1}(zI-G)^{-1}\,dz.

$$

积分中矩阵逆光滑依赖参数，故两者光滑。连续投影的秩是连续整数，因而局部恒定。共同谱缝保证这些局部描述选择同一侧的谱并一致拼接。


证毕。


阈值空间可表达给定噪声尺度下有效保留的信息，但阈值、权重与损失均是建模选择。它不是取代精确核的绝对拓扑不变量。


### 小量子位秩跃迁与有限样本不可分辨性


**命题 2.9（合法弱读口中的秩损失）。**
<a id="obsq:ex:qubit"></a>
存在合法光滑三效果菜单，具有下述秩损失、投影跳变和条件数。

**证明。** 取 $H=\mathbb C^2$，$|t|\le1$，终端效果为

$$

 E_x(t)=\frac{I+t\sigma_x}{2},\qquad
 E_y=\frac{I+\sigma_y}{2},\qquad
 E_z=\frac{I+\sigma_z}{2}.

$$

动力学只包含恒等动作，故这些效果与 $I$ 张成全部声明的未来空间。以
$(\sigma_x,\sigma_y,\sigma_z)/\sqrt2$ 为 HS 正交基，取 $\Omega=I$，有

$$

 C(t)=\frac1{\sqrt2}\operatorname{diag}(t,1,1),\qquad
 G(t)=\frac12\operatorname{diag}(t^2,1,1).

$$

$t\ne0$ 时可见秩为 $3$，$t=0$ 时为 $2$。当 $0<|t|\le1$ 时，

$$

 \sigma(t)=\frac{|t|}{\sqrt2},\qquad
 \operatorname{cond}C(t)=|t|^{-1},\qquad
 \operatorname{cond}G(t)=t^{-2}.

$$

然而在 $t=0$，最小正特征值重新成为 $1/2$。真正连续的是包含零在内、按固定序号排列的特征值，不能把 $\lambda_{\min}^+$ 跨秩损失误读为连续量。

还可以直接计算

$$

 P_t=I_3\quad(t\ne0),\qquad
 P_0=\operatorname{diag}(0,1,1),\qquad
 \|P_t-P_0\|=1.

$$

因此效果本身光滑，并不保证其像空间投影跨越秩损失连续。目标强 $X$ 概率在 $t\ne0$ 时等于
$1/2+(p_x-1/2)/t$，所以其噪声放大正是 $1/|t|$。

证毕。


**定理 2.10（允许适应选取读口的有限副本歧义下界）。**
<a id="obsq:thm:ambiguity"></a>
在命题 [2.9](#obsq:ex:qubit) 的三种二元测量菜单中，取两个候选来源

$$

 \rho_\pm=\frac{I\pm a\sigma_x}{2},\qquad 0<a\le1.

$$

考虑至多 $n$ 步的实验：每步使用一个独立新副本，允许根据已有记录选取三种测量之一，也允许使用与来源无关的经典随机性。令完整记录律为 $P_+,P_-$。则


<a id="obsq:eq:twopoint"></a>
$$

 \operatorname{TV}(P_+,P_-)
 \le\sqrt{1-(1-a^2t^2)^n}
 \le\min\{1,\sqrt n\,|at|\}.


$$

对任意 Bloch $x$ 坐标估计器 $\widehat r_x$，有

$$

 \max_{\pm}P_\pm(|\widehat r_x\mp a|\ge a)
 \ge\frac12[1-\sqrt n\,|at|]_+.

$$

特别地，若 $na^2t^2\le1/4$，至少一个来源的该失败概率不小于 $1/4$。固定 $a$ 的分辨任务因此需要 $n=\Omega(t^{-2})$；对于固定误差水平，这个阶由独立弱 $X$ 采样的上界达到。


**证明。**
在弱 $X$ 测量下，两候选的成功概率为 $(1\pm at)/2$；在 $Y,Z$ 下均为 $1/2$。采用经典亲和量与总变差比较 [Fuchs–van de Graaf](#ref-fuchs)，定义离散分布的 affinity

$$

 \mathcal A(P,Q)=\sum_h\sqrt{P(h)Q(h)}.

$$

两种弱 $X$ Bernoulli 分布的 affinity 为 $\sqrt{1-a^2t^2}$，另两种为 $1$。在同一历史处，策略使用同一条件选择规则；将实际选择也记入记录，其下一步条件 affinity 至少为 $\sqrt{1-a^2t^2}$。逐层对历史求和，得到
$\mathcal A(P_+,P_-)\ge(1-a^2t^2)^{n/2}$。提前停止可补上与来源无关的虚拟结果，不改变结论。

Cauchy--Schwarz 不等式给

$$

 \operatorname{TV}(P,Q)
 =\frac12\sum_h|\sqrt{P(h)}-\sqrt{Q(h)}|
                    (\sqrt{P(h)}+\sqrt{Q(h)})
 \le\sqrt{1-\mathcal A(P,Q)^2}.

$$

再用 $(1-u)^n\ge1-nu$，即得式（[2.10](#obsq:eq:twopoint)）。

任何等先验二分类规则的两种错误概率之和至少为 $1-\operatorname{TV}(P_+,P_-)$：若判为正的事件为 $A$，该和为 $1-P_+(A)+P_-(A)$。由估计器构造以零为中点的分类规则；分类错误时估计与相应真值的距离至少为 $a$。因此两个估计失败概率之和至少为上述量，最大值至少为其一半。

反向上界只需总是选择弱 $X$，按经验频率在 $1/2$ 的哪一侧判别，并按 $t$ 的符号交换标签。前述 Bernoulli 尾界给错误概率至多 $\exp(-na^2t^2/2)$。固定目标错误率时，上下界具有相同的 $t^{-2}$ 阶。


证毕。


本下界不包括任意新增强 $X$ 门、任意集体测量或未经声明的相干累积。若菜单允许在一次副本上积累弱门，所需副本数与相干深度必须分别计费，不能把上述样本下界直接移植为门数下界。


### 光滑秩集的边界与解析附加条件


**命题 2.11（秩下半连续并不产生光滑分层）。**
<a id="obsq:prop:ranklocus"></a>
连续矩阵族只保证 $\{b:\operatorname{rank}C(b)\ge r\}$ 是开集。即使效果全部光滑且物理合法，固定秩的参数集合也不必是流形，甚至不必容许局部有限的光滑分层。


**证明。**
秩至少为 $r$ 等价于至少一个 $r$ 阶子式非零，非零条件是开条件，证明第一句。

为证明第二句，取标准紧 Cantor 集 $K\subset\mathbb R$。补集可由可数个开区间覆盖，其闭包仍落在补集中。选非负紧支撑光滑函数 $\phi_j$，使这些正值区域覆盖 $\mathbb R\setminus K$，而每个支撑均与 $K$ 不交。令

$$

 a_j=\frac{2^{-j}}{1+\max_{0\le k\le j}\|\phi_j^{(k)}\|_\infty},
 \qquad \varepsilon(t)=\sum_{j\ge1}a_j\phi_j(t).

$$

对任一固定阶导数，去掉有限个首项后，导数级数逐项被 $2^{-j}$ 控制，因而一致收敛。于是 $\varepsilon\in C^\infty$，$0\le\varepsilon\le1$，且零集恰为 $K$。将命题 [2.9](#obsq:ex:qubit) 的 $t$ 替换为 $\varepsilon(t)$，所得仍是合法光滑量子效果族，其低秩集正好为 $K$。

若该低秩集有局部有限、连通光滑层组成的分层，Cantor 集不含区间，故每一层只能是单点。局部有限性与 $K$ 的紧性则迫使只有有限层与 $K$ 相交，与 $K$ 无穷矛盾。因此不能仅从光滑性和秩下半连续性推出所需分层。


证毕。


**计算 2.12（解析秩集合的经典细分与距离界）。**
<a id="obsq:rem:analytic"></a>
若参数流形与 $C$ 都实解析，则秩恰为 $r$ 的集合由所有 $(r+1)$ 阶子式为零、至少一个 $r$ 阶子式非零描述，所以是半解析集。有限个秩集合是一族局部有限的半解析集；[Bierstone–Milman，推论 2.11](#ref-bierstone_milman) 给出与它们相容的局部有限半解析分层，每层为解析子流形。[Trotman，第 0 章](#ref-trotman) 所述 Whitney 细分存在定理再给其解析 Whitney 细分；细分仍与各秩集合相容。这两项是经典存在输入，不是下半连续性的推论。同秩集合本身仍可能奇异：把上述弱读口强度换成局部参数 $xy$，低秩集合就是两坐标轴的十字，需要进一步细分。

还可在实解析假设下引用 Lojasiewicz 距离不等式[bierstone_milman，定理6.4及附注6.5](#ref-bierstone_milman)。具体地，设局部最大秩为 $r>0$，令

$$

 \Delta_r(b)=\sum_{|I|=|J|=r}\det(C_{I,J}(b))^2,
 \qquad Z=\{\Delta_r=0\}.

$$

若没有秩缺陷，紧子集上的正谱隙已由计算[2.2](#obsq:thm:bundle)处理。以下在非空缺陷集的一点附近讨论：选取解析定义域内的闭坐标球 $K_0$，令 $Z=\{b\in K_0:\Delta_r(b)=0\}\ne\varnothing$，再限制到内部的较小闭坐标球 $K_1$。$K_0$ 上的 $\Delta_r$ 是连续次解析函数，$Z$ 是紧次解析集，距离函数 $b\mapsto\operatorname{dist}(b,Z)$ 也连续次解析；把两函数限制到 $K_1$ 后，其图均紧，且前者的零集包含于后者的零集。因而所引定理的紧图与零集条件均成立，给出
$\Delta_r(b)\ge c\,\operatorname{dist}(b,Z)^N$，其中 $c,N>0$。
在秩为 $r$ 的点，Cauchy--Binet 公式或奇异值分解给
$\Delta_r=\prod_{j=1}^{r}s_j(C)^2$。其余奇异值局部有共同上界 $M$，因此

$$

 s_r(C)\ge\frac{\sqrt c}{M^{r-1}}\operatorname{dist}(b,Z)^{N/2}.

$$

若权重 $\Omega\succeq\mu I$ 在该邻域一致正定，$\mu>0$，则
$C\Omega C^{\mathsf T}\succeq\mu CC^{\mathsf T}$，两者的像同为 $W$。
在 $W$ 上取最小 Rayleigh 商，得到
$\sigma\ge\sqrt\mu\,s_r(C)$，即加权最小奇异值的多项式距离下界。
这个推论只讨论最大秩域趋近其缺陷集，不把不同秩上的最小正特征值硬拼为连续函数。

解析条件有实际内容。把命题 2.9 的弱读口强度换为光滑函数
$\varepsilon(t)=e^{-1/t^2}$（$t\ne0$），$\varepsilon(0)=0$，
强 $X$ 目标概率的逆噪声放大恰为 $e^{1/t^2}$，超过任意 $|t|^{-N}$。
对定理 2.10 中固定 $a$、固定常数判别错误率的任务，
独立副本代价为 $\Theta(e^{2/t^2})$。
因此仅有 $C^\infty$ 不能保证秩损失附近的多项式稳定性。


### 良态但非平凡的可见向量丛


**命题 2.13（球面上的一致良态量子可见丛）。**
<a id="obsq:prop:tangent"></a>
令参数 $n\in S^2\subset\mathbb R^3$，$P_n=I_3-nn^{\mathsf T}$。对 $j=1,2,3$ 定义终端效果

$$

 E_j(n)=\frac12\bigl[I+(P_ne_j)\cdot\boldsymbol\sigma\bigr],
 \qquad \boldsymbol\sigma=(\sigma_x,\sigma_y,\sigma_z),

$$

并只允许恒等动力学。取 $\Omega=I$，则

$$

 C(n)=\frac1{\sqrt2}P_n,\quad
 G(n)=\frac12P_n,\quad
 W_n=n^\perp\cong T_nS^2,\quad N_n=\mathbb R n.

$$

所有非零奇异值恒为 $1/\sqrt2$，但可见丛 $W\cong TS^2$ 非平凡。其投影联络 $\nabla=P\,d$ 在自然复结构 $J_nz=n\times z$ 下是复线丛的 Hermitian 联络，并满足

$$

 F_\nabla=-i\,\omega_{S^2},\qquad
 \frac{i}{2\pi}\int_{S^2}F_\nabla=2,

$$

其中 $\omega_{S^2}$ 取向外取向的单位球面积形式。


**证明。**
因 $\|P_ne_j\|\le1$，效果 $E_j$ 的两个特征值为 $(1\pm\|P_ne_j\|)/2$，均在 $[0,1]$。中心化并在 HS 基 $\boldsymbol\sigma/\sqrt2$ 中取坐标，即得 $C$ 和 $G$。$P_n$ 的两个非零特征值都是 $1$，给一致谱隙。隐线有处处非零截面 $n$，而可见平面正是球面的切平面。

对切向量 $u$，有 $dP(u)=-un^{\mathsf T}-nu^{\mathsf T}$。在切向量 $z$ 上计算投影联络曲率，得到

$$

 F_\nabla(u,v)z
 =P\bigl(dP(u)dP(v)-dP(v)dP(u)\bigr)z
 =u\langle v,z\rangle-v\langle u,z\rangle.

$$

又有 $J_n^2=-I$。若 $z$ 为切截面，$dn\times z$ 法向，故
$P\,d(Jz)=J(P\,dz)$；联络保持 $J$ 及内积，是 Hermitian 联络。在正向正交切基 $u,v$ 中，$J u=v$，上述曲率将 $u$ 送到 $-v$、将 $v$ 送到 $u$，所以 $F=-J\omega_{S^2}=-i\omega_{S^2}$。单位球面积为 $4\pi$，曲率积分为 $2$。

若可见丛存在全局非零截面，归一化后它与其 $J$ 像给全局酉标架；联络可写为全局 $i\mathbb R$ 值一形式 $A$，曲率即 $dA$。Stokes 定理会使曲率积分为零，与刚才的计算矛盾。因此丛非平凡，也不可能选择两条全局处处独立的可见截面。三个效果列能够全局光滑生成该丛，不等于存在两个全局基向量。


证毕。


这个例子的可见丛是实算子空间内的统计子丛；所加的复结构由 $n$ 与球面取向给出。它不是自动的 Hamiltonian 本征态 Berry 丛，投影联络的存在也没有自动提供原项目允许的驱动门。另一方面，命题 [2.9](#obsq:ex:qubit) 在 $t\ne0$ 上有 $P=I$、投影曲率为零，却在 $t\to0$ 时任意病态。因而丛的非平凡性、联络曲率与稳定可观测性是三个需分别检验的性质。


## 3. 五模 FIB：弱中间门的维数跃迁与资源律
<a id="sec:fib"></a>


### 同一来源、三种观察合同

固定五模 Hilbert 空间

$$

\mathcal H=\operatorname{span}_{\mathbb C}
 \{|000\rangle,|001\rangle,|010\rangle,|100\rangle,|101\rangle\}.

$$

取

$$

c_0=|000\rangle,\quad c_1=|001\rangle,\quad
c_2=|100\rangle,\quad c_3=|101\rangle,\quad a=|010\rangle,
\qquad \mathcal C=\operatorname{span}\{c_0,c_1,c_2,c_3\}.

$$

于是 $\mathcal H=\mathcal C\oplus\mathbb Ca$。
记 $P_v=|v\rangle\langle v|$，端点占位及中点占位为

$$

N_x=P_{c_2}+P_{c_3},\qquad
N_y=P_{c_1}+P_{c_3},\qquad N_z=P_a.

$$

这里物理位串的次序已固定；$x,y$ 指左右端点，$z$ 指中点。


**定义 3.1（本节操作合同）。** <a id="def:fibmenu"></a>
每个实验先作许可酉控制，最后从 $N_x,N_y,P_a$ 中选一个作二元测量。
不默认在同一来源上依次取得多个占位的联合结果。
端点菜单 $\mathcal M_{\mathrm{end}}$ 允许

$$

\widetilde U=U\oplus1_a,\qquad U\in SU(\mathcal C).

$$

这是前卷端点连续脉冲与固定受控相位门的代码控制结论所供应的理想菜单
[repo_relational](#ref-repo_relational)；它保持 $\mathcal C$ 并固定 $a$。
扩充菜单再加入一个已知并经校准的固定门

$$

V_\epsilon=e^{-i\epsilon H_2},\qquad
H_2=|a\rangle\langle c_0|+|c_0\rangle\langle a|.

$$

所有有限酉词都可执行，然后只进行一次终端测量。
$\epsilon$ 是模型参数，不把其估计成本隐含在重构公式中。


无控制时，当前三个占位均值只给
$\operatorname{span}\{I,N_x,N_y,P_a\}$，维数为 $4$。
若另行允许中途联合占位测量，初始效果空间已经改变；
因此不能把两种观察合同的维数混写。


**定理 3.2（完整未来的 $17\longrightarrow25$ 跃迁）。** <a id="thm:fibjump"></a>
在定义 [3.1](#def:fibmenu) 下，取全部五维密度态为来源类。此时

$$

\mathcal W_{\mathrm{end}}
 =\operatorname{Herm}(\mathcal C)\oplus\mathbb RP_a,
\qquad \dim_{\mathbb R}\mathcal W_{\mathrm{end}}=17.

$$

扩充菜单的未来效果空间满足

$$

\mathcal W_\epsilon=
\begin{cases}
\mathcal W_{\mathrm{end}},&\sin\epsilon=0,\\
\operatorname{Herm}(\mathcal H),&\sin\epsilon\ne0.
\end{cases}

$$

因此最小仿射预测维数为 $16$ 或 $24$。
消失的八个隐藏方向恰为 $a$ 与四维代码之间的实、虚相干。


**证明。**
所有端点控制和终端效果都对 $\mathcal C\oplus\mathbb Ca$ 块对角，
所以未来效果不可能出现交叉块。反过来，$N_x|_{\mathcal C}$ 是秩二投影，
它的 $SU(4)$ 轨道包含全部代码秩二投影。
这些投影张成 $\operatorname{Herm}(\mathcal C)$：
标准投影 $P_{c_i}+P_{c_j}$ 张成全部对角矩阵；
例如对不同 $i,j,k$，

$$

2P_{c_i}=(P_{c_i}+P_{c_j})+(P_{c_i}+P_{c_k})-(P_{c_j}+P_{c_k}).

$$

投影

$$

P_{(c_i+c_j)/\sqrt2}+P_{c_k},\qquad
P_{(c_i+i c_j)/\sqrt2}+P_{c_k},\quad k\notin\{i,j\},

$$

再分别给出每个非对角元的实部与虚部。
$U(4)$ 与 $SU(4)$ 的投影共轭轨道相同，
因为可以给酉矩阵乘一个标量相位来调整行列式。
加入 $P_a$ 即得第一个等式。

令 $c=\cos\epsilon,\ s=\sin\epsilon$。
$V_\epsilon$ 在 $\operatorname{span}\{a,c_0\}$ 上为
$\left(\begin{smallmatrix}c&-is\\-is&c\end{smallmatrix}\right)$，
在其他代码向量上为恒等。
当 $s=0$ 时，它仍然块对角，故闭包不变。
当 $s\ne0$ 时，对 $j\in\{1,2,3\}$ 的代码相干

$$

B_j=|c_0\rangle\langle c_j|+|c_j\rangle\langle c_0|

$$

有

$$

V_\epsilon^\dagger B_jV_\epsilon
=cB_j+is\bigl(|a\rangle\langle c_j|-|c_j\rangle\langle a|\bigr).

$$

以虚相干代替 $B_j$ 同样得到另一实相干。
旧空间已经含 $B_j$，故减去 $cB_j$ 后获得两种 $a$--$c_j$ 相干。
再用代码 $SU(4)$ 共轭把 $c_j$ 送到任意代码单位向量，
即可得到全部八个实交叉方向。
加上原有的 $17$ 维块对角部分，得到 $25$ 维全部 Hermitian 空间。
这里即使 $c=0$ 也成立；不能只靠
$V_\epsilon^\dagger P_aV_\epsilon$ 中的 $\sin(2\epsilon)$ 项来证明全局结论。
最后应用假设 [1.2](#prop:exactquotient) 中的既有商定理。


证毕。


连续控制菜单并不意味着无限个读口必须同时取得。
有限维空间中总能从轨道选出有限生成族；
但这种存在性本身不提供任意精度下的统一成本界。
下一定理明确给出所用的有限族。


### 一个有限探针族的精确退化谱


令

$$

\mathcal B=\{X\in\operatorname{Herm}_0(\mathcal H):
             X\text{ 对 }\mathcal C\oplus\mathbb Ca\text{ 块对角}\},

$$

并令 $\mathcal X=\mathcal B^\perp$。
其维数分别为 $16$ 与 $8$。


**定理 3.3（新方向的 Gramian 恰为 $\sin^2(2\epsilon)I_8$）。** <a id="thm:fibgram"></a>
先选一个固定的旧效果生成族，其中心化列矩阵为 $C_0$，
在 $\mathcal B$ 上的 Gramian $G_0=C_0C_0^{\mathsf T}$ 满足
$\lambda_0=\lambda_{\min}(G_0|_{\mathcal B})>0$。
对八个向量

$$

\mathcal V=\{c_j,i c_j:j=0,1,2,3\}

$$

分别执行两个协议：选 $\widetilde U$ 使
$U^\dagger c_0=v$ 或 $-v$，再施加 $V_\epsilon$，最后测量 $P_a$。
把这十六个效果与旧族一起中心化，并把全部权重取为一，
所得 $G_\epsilon$ 对 $\mathcal B\oplus\mathcal X$ 块对角，且

$$

G_\epsilon|_{\mathcal B}\succeq G_0|_{\mathcal B},\qquad
G_\epsilon|_{\mathcal X}=\sin^2(2\epsilon)I_{\mathcal X}.

$$

在 $0<|\epsilon|$ 足够小、使 $\sin^2(2\epsilon)<\lambda_0$ 时，

$$

\lambda_{\min}(G_\epsilon)=\sin^2(2\epsilon),\qquad
\|(\text{加权线性读出})^+\|=\frac1{|\sin(2\epsilon)|}.

$$


**证明。**
旧族可以具体选为全部六个 $P_{c_i}+P_{c_j}$、
对六个 $i<j$ 各选上一定理证明中的两个秩二投影，再加入 $P_a$。
它们都是真实许可的终端效果，并生成 $\mathcal B$ 的中心化空间，
故 $\lambda_0>0$。

设

$$

Y_{av}=-i|a\rangle\langle v|+i|v\rangle\langle a|.

$$

每对新效果是

$$

E_v^\pm=c^2P_a+s^2P_v\pm csY_{av}.

$$

二者都是秩一投影。中心化后令
$b_v=c^2P_a+s^2P_v-I/5\in\mathcal B$，
对应列为 $b_v\pm csY_{av}$。
在实 Hilbert--Schmidt 空间中，这一对的外积和为

$$

2b_vb_v^{\mathsf T}+2c^2s^2Y_{av}Y_{av}^{\mathsf T};

$$

混合块精确相消。八个 $Y_{av}/\sqrt2$ 是 $\mathcal X$ 的正交规范基，
故交叉块之和等于
$4c^2s^2I_{\mathcal X}=\sin^2(2\epsilon)I_{\mathcal X}$。
旧块只增加半正定项。比较两块最小特征值即可；
最后一个等式由奇异值分解或可观测性定理得到。


证毕。


这是给定有限探针族、给定权重的精确谱。
当 $\cos\epsilon=0$ 时，这个特定族没有读出交叉方向，
但定理 [3.2](#thm:fibjump) 的全部菜单仍然完备；
换用代码相干的终端轨道即可看见它们。
因此“某套校准探针退化”和“全部许可未来不可分”也须分开。

若取固定阈值 $0<\tau<\lambda_0$，此族的有效秩恰为

$$

r_\tau(\epsilon)=16+
 8\,\mathbf 1_{\{\sin^2(2\epsilon)\ge\tau\}}.

$$

这给出了精确秩与给定噪声尺度下有效秩的明确差别。


### 同一隐藏相干的深度与副本数


**定义 3.4（可检验的二点任务）。** <a id="def:fibpair"></a>
来源以相等先验准备两个纯态之一：

$$

|\psi_\pm\rangle=\frac{|a\rangle\pm i|c_0\rangle}{\sqrt2}.

$$

它们对端点菜单完全同律。
对固定整数 $q\ge1$，协议先施加 $q$ 个 $V_\epsilon$，再测 $P_a$。
重复 $N$ 次指实际取得 $N$ 个独立新制备副本，
每份执行这个协议；不指把同一未知态无损复制。


**定理 3.5（固定协议的深度--副本数权衡）。** <a id="thm:fibsamples"></a>
令 $s_q=\sin(2q\epsilon)$。
定义 [3.4](#def:fibpair) 的一次记录分布为

$$

p_\pm=\frac{1\pm s_q}{2}.

$$

其最优等先验错误率 $e_N^*$ 满足

$$

e_N^*\ge
\frac{1-\sqrt{1-(1-s_q^2)^N}}2
\ge\frac{[1-\sqrt N\,|s_q|]_+}{2}.

$$

因此，要达到 $e_N^*\le1/4$，必有

$$

Nq^2\epsilon^2\ge\frac1{16}.

$$

另一方面，多数判决在已知 $s_q$ 符号后满足

$$

e_N\le \exp(-Ns_q^2/2).

$$

当 $0<|q\epsilon|\le\pi/4$ 时，

$$

N\ge\frac{\pi^2}{8q^2\epsilon^2}\log\frac1\eta

$$

足以使错误率不超过 $\eta$。
对固定 $q$、固定目标错误率 $0<\eta<1/2$，
所需副本数随 $\epsilon\to0$ 为 $\Theta(\epsilon^{-2})$。


**证明。**
$V_\epsilon^q=V_{q\epsilon}$，其在 $a$ 方向的振幅为
$(\cos q\epsilon\pm\sin q\epsilon)/\sqrt2$，故概率公式成立。
两态的块对角部分相同，所以端点菜单不能区别它们。

令单次 Bernoulli 分布为 $P,Q$。
它们的 Hellinger 亲和量是

$$

A(P,Q)=\sum_z\sqrt{P(z)Q(z)}=\sqrt{1-s_q^2}.

$$

独立乘积的亲和量为 $A^N$。
对任意有限分布，Cauchy--Schwarz 给

$$

\begin{split}
2\operatorname{TV}(P,Q)
&=\sum_z|\sqrt{P(z)}-\sqrt{Q(z)}|
            (\sqrt{P(z)}+\sqrt{Q(z)})\\
&\le\sqrt{(2-2A)(2+2A)}.
\end{split}

$$

故乘积律的 TV 至多 $\sqrt{1-(1-s_q^2)^N}$。
最优二点错误率为 $(1-\operatorname{TV})/2$；
再用 $1-(1-u)^N\le Nu$ 得第二个下界。
若错误率至多 $1/4$，必要有 $Ns_q^2\ge1/4$，
而 $|s_q|\le2q|\epsilon|$，给出常数 $1/16$。

多数判决把经验均值与 $1/2$ 比较，并按 $s_q$ 的符号调整标签。
独立 Bernoulli 的指数矩界给每侧错误概率至多
$\exp[-2N(|s_q|/2)^2]$。
该指数矩界也可直接由 Bernoulli 对数矩母函数的二阶导数
$\le1/4$，在零点积分两次得到。
最后，$0\le u\le\pi/2$ 上 $\sin u\ge2u/\pi$，
于是 $|s_q|\ge4|q\epsilon|/\pi$，代入即可。
对于任意固定 $\eta<1/2$，下界同样给
$Nq^2\epsilon^2\ge(1-2\eta)^2/4$，从而得到双边阶数。


证毕。


上面的样本下界针对这个明确实验族。
它没有声称对带有任意新辅助系统、任意集体测量的所有量子实验同样成立。
单次实验若允许更深的控制，则有下一个更一般的结论。


**定理 3.6（单次来源的相干深度律）。** <a id="thm:fibdepth"></a>
仍取上述两态，允许任意代码 $SU(4)$ 控制穿插在 $q$ 个弱门之间，
末端允许任意块对角 POVM，过程中无中间测量、复位或新增辅助系统。
若一次实验的最优错误率不超过 $1/4$，必有

$$

q|\epsilon|\ge\frac14.

$$

反过来，当 $0<|\epsilon|\le\pi/4$ 时，取
$q$ 为 $\pi/(4|\epsilon|)$ 的最近整数，仅重复弱门再测 $P_a$，
便有

$$

e_1\le\frac{1-\cos|\epsilon|}{2}\le\frac{\epsilon^2}{4}.

$$

因此，在这个操作合同中达到固定常数错误率的弱门深度为
$\Theta(|\epsilon|^{-1})$。


**证明。**
把任意给定控制词中的每个 $V_\epsilon$ 替换为恒等，记两个总酉为
$W_\epsilon,W_0$。逐个替换的 telescoping 求和给

$$

\|W_\epsilon-W_0\|_{\mathrm{op}}
\le q\|V_\epsilon-I\|_{\mathrm{op}}\le q|\epsilon|.

$$

对任意密度态，两个酉输出的迹距离不超过
$\|W_\epsilon-W_0\|_{\mathrm{op}}$；这从把态差拆成两项并用
$\|A\rho B\|_1\le\|A\|_{\mathrm{op}}\|\rho\|_1\|B\|_{\mathrm{op}}$
直接得到。任何 POVM 的记录 TV 不大于此迹距离。
$W_0$ 是块对角控制，两态在它之后的块对角读出相同。
由三角不等式，$W_\epsilon$ 后两记录律的 TV 至多 $2q|\epsilon|$。
错误率至多 $1/4$ 要求 TV 至少 $1/2$，故得到必要条件。

对所选最近整数，$|2q|\epsilon|-\pi/2|\le|\epsilon|$，
所以 $|\sin(2q\epsilon)|\ge\cos|\epsilon|$。
使用精确单次错误率 $(1-|\sin(2q\epsilon)|)/2$，
再用 $1-\cos t\le t^2/2$ 即得构造上界。


证毕。


这两个定理把成本分配写成可检查的两种实验：
固定深度消耗更多独立准备，或在单一准备上累积更深的相干控制。
它们都没有把小但非零的代数可见性当作免费信息。

**计算 3.7（指定 FIB 面板上的目标风险与采样常数）。**
在定理 3.3 的单位权重面板中，取 $v=c_0$、
$Y=Y_{ac_0}$、目标效果 $T=(I+Y)/2$，并记 $s=\sin(2\epsilon)$。
若 $s\ne0$，只需该向量对应的两个实验，即可使用精确仿射公式

$$
\operatorname{Tr}(T\rho)=\frac12+\frac{p_{c_0}^+-p_{c_0}^-}{2s}.
$$

在整个面板的欧氏噪声球 $\|\eta\|_2\le\delta$ 下，
所有精确仿射公式的最小最坏噪声误差为 $\delta/(\sqrt2|s|)$。
若这两个实验各在 $n$ 个同源独立新副本上执行，且两组独立，则相应估计满足

$$
\operatorname{Var}(\widehat t)\le\frac{1}{8ns^2},\qquad
\Pr\{|\widehat t-\operatorname{Tr}(T\rho)|\ge u\}
\le2e^{-4nu^2s^2},\quad u>0.
$$

在 $s=0$ 时，这个目标不能由该面板的全部概率精确决定；
这包含 $\cos\epsilon=0$ 而完整菜单仍然完备的情形。

**证明。** $Y$ 在 $\operatorname{span}\{a,c_0\}$ 上的特征值为 $\pm1$，
在其正交补上为零，故 $T$ 是合法效果。
其中心化部分 $f=Y/2\in\mathcal X$ 满足 $\|f\|_{\mathrm{HS}}^2=1/2$。
由 $E_{c_0}^+-E_{c_0}^-=sY$ 得到显示的预测公式。
定理 3.3 的交叉块为 $s^2I$，故
$f^{\mathsf T}G_\epsilon^+f=1/(2s^2)$。
计算 2.5 给出最小噪声误差；其最小范数系数正是在这两个列上取
$1/(2s),-1/(2s)$、其余列为零。
每组 $n$ 次独立采样时，这两个系数的加权平方和为 $1/(2ns^2)$，
计算 2.7 给出方差与尾界。
若 $s=0$，面板只有块对角列，而 $Y\perp\mathcal B$，
故计算 2.5 的核判据排除精确预测。
这些结论保持实际实验与独立准备的合同；
它们没有把概率向量当作在同一份未知态上可免费取得的联合记录。证毕。


## 4. 固定协变量来源的既有输入与取得边界

**假设 4.1（固定实框架下的二次纤维输入）。** 固定定向欧氏 $\mathbb R^5$ 的基 $e_1,\ldots,e_5$，写 $\rho=S+iA$，其中 $S^\mathsf T=S$、$\operatorname{Tr}S=1$、$A^\mathsf T=-A$、$S+iA\succeq0$。记 $J_{ij}=E_{ij}-E_{ji}$、$a_A=\sum_{i<j}A_{ij}e_i\wedge e_j$，故 $\|a_A\|^2=\|A\|_F^2/2$。采用 [量子边界卷定理 8.2 的谱与 Hodge 计算](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md) 所给纤维分类，协变量对应为

$$
\mathfrak q(A)=\left(-\tfrac12\operatorname{Tr}A^2,
-A^2+\tfrac15\operatorname{Tr}(A^2)I_5,*(a_A\wedge a_A)\right)
=(\sigma,\gamma,\beta),\qquad K=-A^2=\gamma+\tfrac25\sigma I_5.
$$

该输入的 $b(A)$ 就是此处 $\beta(A)$，没有 Hodge 因子变化；$\sigma=\lambda_1^2+\lambda_2^2$、$\|\beta\|=2\lambda_1\lambda_2$，所以 $\sigma^2-\|\beta\|^2=(\lambda_1^2-\lambda_2^2)^2$。目标只取共同符号 $A\sim-A$，保持 $S$ 和实际坐标固定，不除以正交群或一般酉共轭。

零态纤维为 $\{0\}$；秩二及两个正旋转尺度不同的秩四纤维为 $\{A,-A\}$。等重秩四时，令尺度为 $\lambda>0$、$E=\operatorname{im}A$、$n=\beta/(2\lambda^2)$，以 $*_5\operatorname{vol}_E=n$ 定向 $E$。在其正向正交基中，既有纤维为

$$
\mathcal F_A=\{\lambda(u_1L_1+u_2L_2+u_3L_3):|u|=1\},\quad
L_1=J_{12}+J_{34},\ L_2=J_{13}-J_{24},\ L_3=J_{14}+J_{23}.
$$

合法纤维精确为 $\{S+iB:B\in\mathcal F_A,\ S+iB\succeq0\}$。对 $S=I_5/5$、$0<\lambda<1/5$，整个球面严格合法，态谱为 $1/5+\lambda,1/5+\lambda,1/5-\lambda,1/5-\lambda,1/5$，共同复共轭商留下 $\mathbb{RP}^2$。$\lambda=1/10$ 时的 $\lambda L_1,\lambda L_2$ 是 [结构取得卷 §15](AURIC_LANGLANDS_STRUCTURE_ACQUISITION_AND_SPECTRAL_EXTENSION_THEORY.md) 的同源碰撞。这里直接使用该分类；微分退化与三深度秩计数见 [退化与稳定恢复续卷](AURIC_LANGLANDS_DEGENERATION_RAMIFICATION_AND_STABLE_RECOVERY_THEORY.md)。

**命题 4.2（重谱来源的覆盖与取得条件）。** 在假设 4.1 的完整合法重谱球面上，仅作有限基变换或指定一个代表不能恢复任意实际来源类；需要补入在该纤维上变化的合法记录。

**证明。** 对任意 $f:\mathcal X\to Y$、$\pi:Y'\to Y$，拉回 $\mathcal X\times_Y Y'$ 在 $y'$ 上的纤维，经 $(x,y')\mapsto x$ 与 $f^{-1}(\pi(y'))$ 一一对应。这是集合拉回的直接计算，应用于 $f(A)=\mathfrak q(A)$，重谱值上仍是同一个 $S^2$。指定代表只给一个截面的选择，不能使相同旧读数对应的所有实际输入都等于所选代表。完整实二拷贝统计可以恢复 $A\otimes A$ 到共同复共轭；固定的后续线性协变量 $\mathfrak q$ 才产生上述损失 [结构取得卷 §4.2](AURIC_LANGLANDS_STRUCTURE_ACQUISITION_AND_SPECTRAL_EXTENSION_THEORY.md)。同源独立准备、校准滤波及实际带标志探测须各自供应；已选分支概率并非一。可复用的定量稳定性、残差精度和完整尝试成本取 [量子边界卷 §§13–14](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md) 的明确归一化。有限覆盖没有生成这些操作。证毕。

该来源球面是 $\mathfrak q$ 的一条纤维；[关系丛卷 §4](AURIC_FIB_RELATIONAL_BUNDLE_AND_PREDICTIVE_CLOSURE_THEORY.md) 的 $S_b$ 是固定占位矩层再除 $T^3$ 的辛约化空间。底空间、等价关系与读数不同。

## 5. 从可分辨候选到可执行取得

<a id="sec:ga-acquisition"></a>

《取得、覆盖与临界域》命题4.5给出候选覆盖上的水平选择和最小选择次数；命题4.6在另外供应可执行置换及固定锚点后，给出两两未来分离及确定性记忆下界[repo_cover](#ref-repo_cover)。下面补出一条连续作用于同一来源的完整识别协议，并用一个破坏性读出反例说明这项结论需要哪些条件。


**定义 5.1（可逆候选轨道与取得资源）。**
<a id="def:ga-orbit"></a>
令 $\Omega$ 为 $m\ge2$ 个实际候选组成的有限集合。有限动作字母表的每个动作 $a$ 供应一个已知置换 $g_a:\Omega\to\Omega$；所生成的群在 $\Omega$ 上传递，所有正向有限词均合法。固定公开锚点 $\omega_*$，允许终端读出

$$

h(\omega)=\mathbf1_{\{\omega_*\}}(\omega).

$$

该读出确定、精确，并不额外改变候选状态；锚点也不与未知来源一起输运。一个测试是执行一个正向词，再读一次 $h$。各测试继续作用于前次留下的同一个状态，动作数和终端读取数分别计费。可以根据已经取得的报告选择下一测试及停止，但没有复位或副本。


这是有限经典候选及其可逆输运的合同。它可描述明确实现的候选标签，不把任意未知量子态的无扰测量作为输入。对于每个原子强制即时报告的字面时钟模型，应另外计入全部即时报告；本定义的终端读取计数不删除那些成本。


**定理 5.2（无复位取得及精确最坏查询数）。**
<a id="thm:ga-orbit-acquisition"></a>
在定义 [5.1](#def:ga-orbit) 下，可以对每个未知初态精确确定它及协议结束时的当前态，并且最坏使用

$$

m-1\quad\text{次终端读取},\qquad
(m-1)^2\quad\text{次原子动作}.

$$

在只允许该锚点读口和已知置换的确定性精确协议类中，最坏终端读取数不可能少于 $m-1$。因而读取上界精确；动作上界仅为所构造协议的统一界，不主张最优。


**证明。**
每个生成置换的逆等于其有限正幂，所以正向可达关系与所生成群的轨道相同。任意 $u\in\Omega$ 都有通往 $\omega_*$ 的正向词；最短路径不重复顶点，故长度至多 $m-1$。

协议维护当前候选集合 $K\subseteq\Omega$，以及从初始候选到当前候选的已知累乘置换。开始时 $K=\Omega$。若 $|K|=1$，已经完成；否则选择一个 $u\in K$ 且 $u\ne\omega_*$，执行一个把 $u$ 送到锚点、长度至多 $m-1$ 的正向词 $w$。它的累乘 $g_w$ 是双射，因此 $K$ 中恰有 $u$ 的报告为一。若报告为一，当前态为 $\omega_*$，并可用已知累乘的逆在解码中恢复初态；这个逆只用于数学解码，没有执行物理逆门。若报告为零，则把候选集合更新为

$$

K\longleftarrow g_w(K\setminus\{u\}).

$$

新集合恰好保留所有仍可能的当前态，基数减一；已知累乘置换也同步更新。每次未成功的读取排除一个候选，因此至多 $m-1$ 次读取后识别完成；每次至多 $m-1$ 个原子，得到所列动作界。协议始终使用同一实际状态，不需要把它恢复到初态。

为证下界，考察任意确定性协议的全零报告分支。在每次读取前，沿这条分支已经选择的全部动作组成一个已知置换 $g$。于是这次报告为一的初始候选至多是唯一的 $g^{-1}\omega_*$；零报告最多排除一个初始候选。取得 $k<m-1$ 个零以后，仍至少有 $m-k\ge2$ 个初始候选与完整记录相容，且它们的当前态仍不同。协议若在此停止，同一输出不能正确识别二者。所以这条仍有实际候选支持的分支至少要进行第 $m-1$ 次读取。两部分合起来证明读取复杂度的精确值。


证毕。


该定理把三种不同数量具体区分：一个传递候选轨道的数学选择次数可以是 $m$，记住已识别标签需 $m$ 个记忆状态，而仅有单锚点读口时，最坏实际读取恰需 $m-1$ 次。数学覆盖的存在并不供应定义 [5.1](#def:ga-orbit) 的置换执行、固定参考和无扰读口。


**命题 5.3（两两未来分离不保证单次来源可完全取得）。**
<a id="prop:ga-destructive"></a>
存在有限确定性经典仪器，其三个可能初态两两未来可分，全部未来效果在初始三态空间上张成三维，但任何只使用一次初始来源的自适应协议都不能对三个初态同时精确识别。


**证明。**
取状态集合 $\{1,2,3,\dagger\}$，初始来源限于 $\{1,2,3\}$。动作 $a_j$（$j=1,2,3$）报告

$$

R=\mathbf1_{\{j\}}(x),

$$

然后无论报告为何，都把当前状态改为吸收态 $\dagger$。吸收态上的后续全部报告为零，且状态不再变化。这是合法有限确定性状态更新；若采用经典概率向量，逐输出分支就是相应的非负线性映射。

对初态 $i\ne j$，第一个动作 $a_i$ 的报告分别为一和零，所以二者未来不等价。三个单步报告效果在初始空间上分别是三个坐标函数，因此其线性张成等于整个 $\mathbb R^3$，已达到全未来可观测性。

然而任意确定性识别协议若不调用动作就停止，显然无法识别三个输入。它的第一个实际动作必为某个 $a_j$；另两个初态都给出零报告，随后都处于同一个 $\dagger$。从此相同记录和相同状态导致任何自适应后续完全相同，故这两个初态无法再区分。若允许与来源独立的随机种子，精确零错误要求对三个输入各自以概率一正确；有限三个概率一集合的交仍为概率一。在其中固定任一种子，就得到已经排除的确定性协议。因此随机化也不能取得零错误完全识别。


证毕。


这里的差别由量词体现：每对来源存在一个区别实验，与存在一个能在同一次来源上识别全部候选的实验，是两个任务。前卷全未来效果商刻画所有允许实验的统计可区分性[repo_relational，§8.2](#ref-repo_relational)；若要把效果列的全部数值都取得，还须另外给出独立重备、可逆控制或其他满足任务的采集合同。


### 权限、残余盲核与最小成本区别词


下面把许可传播[repo_context，§2.1](#ref-repo_context)与旧盲空间上的残余系统[repo_structure，§2.2](#ref-repo_structure)接到明确的词成本。结论针对非适应的线性词；它不把一个概率分支的可区分期望自动变为已经观测到的单次报告。


**定义 5.4（有限权限图上的残余线性词）。**
<a id="def:ga-priced-words"></a>
给定有限有向权限图。每个节点 $q$ 有有限维实线性差状态空间 $V_q$ 和旧盲子空间 $N_q\subseteq V_q$。每条边 $e:q\to q'$ 供应线性映射

$$

T_e:V_q\to V_{q'},\qquad T_eN_q\subseteq N_{q'},

$$

以及固定正成本 $c_e>0$。节点 $q$ 的新增停止读口为线性映射
$A_q:V_q\to\mathbb R^{s_q}$；不允许新增停止读取的节点取 $A_q=0$。
任意在同一节点相接的合法前缀、后缀可以拼接，且这些规则只依赖节点及边，不另依赖被删除的历史。
词 $w=e_1\cdots e_L$ 的正向作用与成本定义为

$$

T_w=T_{e_L}\cdots T_{e_1},\qquad
c(w)=\sum_{j=1}^Lc_{e_j}.

$$

空词在起点读出，成本为零。对初始隐藏差 $x\in N_{q_0}$，若
$A_{q_L}T_wx\ne0$，称 $w$ 为区别词。置

$$

B=\sum_q\dim(N_q\cap\ker A_q)
=\sum_q\left(\dim N_q-\operatorname{rank}(A_q|_{N_q})\right).

$$


**定理 5.5（最小成本区别词的统一长度界）。**
<a id="thm:ga-cost-horizon"></a>
若 $x\in N_{q_0}$ 有任一合法区别词，则存在成本最小的区别词，而且每个成本最小区别词的长度均不超过 $B$。因此对任意预算 $C\ge0$，有精确核等式


<a id="eq:ga-budget-kernel"></a>
$$


\bigcap_{\substack{w:q_0\leadsto q_L\\c(w)\le C}}
\ker(A_{q_L}T_w|_{N_{q_0}})
=
\bigcap_{\substack{w:q_0\leadsto q_L\\c(w)\le C,\ |w|\le B}}
\ker(A_{q_L}T_w|_{N_{q_0}}).

$$

所以有限列举长度至多 $B$ 的合法词，足以精确确定每个预算下的区别核，也保留每个隐藏差的最小区别成本。


**证明。**
若空词已区别，所有最廉价区别词都为空词，结论显然。否则取任一非空区别词 $w_0$；此时边集非空。有限边集的最小成本 $c_{\min}$ 严格正，因此成本不超过 $c(w_0)$ 的词，长度均不超过 $c(w_0)/c_{\min}$，数量有限。从其中选最小成本区别词 $w=e_1\cdots e_L$，存在性成立。

设 $L>0$，沿该词记

$$

x_j=T_{e_j}\cdots T_{e_1}x\in N_{q_j},
\qquad 0\le j\le L.

$$

若某个真前缀 $j<L$ 满足 $A_{q_j}x_j\ne0$，在该节点停止就得到成本严格更低的区别词，矛盾。故全部真前缀状态属于相应的 $N_{q_j}\cap\ker A_{q_j}$。把它们分别嵌入直和空间

$$

\mathcal Z=\bigoplus_q(N_q\cap\ker A_q),\qquad \dim\mathcal Z=B,

$$

得到向量 $\widetilde x_0,\ldots,\widetilde x_{L-1}$。

这些向量必须线性独立。否则存在 $j<L$，使
$\widetilde x_j$ 是较早向量的线性组合。投影到节点 $q_j$ 的直和分量，得到

$$

x_j=\sum_{\substack{i<j\\q_i=q_j}}a_i x_i.

$$

对两边作用从 $q_j$ 到终点的同一后缀，再作用末端读口，便有

$$

0\ne A_{q_L}x_L
=\sum_{\substack{i<j\\q_i=q_j}}
a_i A_{q_L}T_{e_L}\cdots T_{e_{j+1}}x_i.

$$

其中至少一项非零。相应的词先执行前 $i$ 条边，再拼接 $j$ 后面的后缀；因为 $q_i=q_j$，它合法，并仍区别 $x$。它删去了至少一条正成本边，因而比 $w$ 更便宜，矛盾。故这 $L$ 个真前缀向量独立，$L\le\dim\mathcal Z=B$。

式 （[5.5](#eq:ga-budget-kernel)） 的左侧显然包含于右侧。若某个 $x$ 不在左侧，就有预算内区别词；其最小成本区别词成本仍不超过 $C$，且长度至多 $B$，所以 $x$ 也不在右侧。反向包含由此成立。将成本最小词取于这同一个有限目录，即得最后一句。


证毕。


如果动作的合法性还依赖未编码的历史，删除中段可能破坏后缀许可；应先把该信息加入权限节点。如果边成本依赖隐藏来源或被删除的历史，也须重新核对比较。本定理没有控制测量方差、独立制备数或条件事件概率；这些统计成本应接在合法词效果的取得模型之后分析。第 3 节新增弱门破坏端点菜单的旧盲核，不能把该旧核直接代入本定理；必须选取满足 $T_eN_q\subseteq N_{q'}$ 的残余系统。此处提供的是有限权限图内线性区别成本的精确有限化，补足单纯闭包维数界尚未涉及的最廉价见证问题。


## 6. 精度约束下的白盒证书、取得成本与记忆下界

<a id="sec:robust-certificates"></a>

本章把失败超图推进到可执行的量子实验。需要同时声明三个对象：合法实验的概率律、误差容忍规则，以及取得实验记录的成本。可观测空间的维数只回答线性可辨识性；它本身既不是有限精度下的证书宽度，也不是取得证书的调用次数。


### 鲁棒失败边与加权取得设计


**定义 6.1（有限候选的区间证书合同）。**
<a id="def:interval-certificate"></a>
设 $\mathcal H$ 为有限维 Hilbert 空间，$\rho_0,\ldots,\rho_m$ 为已指定的候选密度矩阵。下标 $0$ 表示要认证的参考候选。有限集合 $D$ 编号实际许可的二元实验；实验 $j$ 的效应为 $0\le E_j\le I$，概率为

$$

 p^i_j=\operatorname{Tr}(E_j\rho_i).

$$

这里 $E_j$ 可以是输出解析的有限词效应，但必须由声明的控制菜单和记录程序实现。一个形式上可写出的 Hermitian 算子，不因此自动成为可取得的实验。

给定容忍半径 $\varepsilon_j>0$ 及正成本 $c_j>0$。对选定实验集 $C\subseteq D$，候选 $i$ 的允许记录集合为

$$

 B_i(C)=\prod_{j\in C}
 \bigl([p^i_j-\varepsilon_j,p^i_j+\varepsilon_j]\cap[0,1]\bigr).

$$

记录 $y$ 与候选 $i$ 一致，定义为 $y\in B_i(C)$。称 $C$ 为参考候选的鲁棒区间证书，若对每个 $y\in B_0(C)$，所有 $i\ge1$ 均与 $y$ 不一致。相应的严格失败边与成本为

$$

 F_i=\{j\in D:|p^i_j-p^0_j|>2\varepsilon_j\},
 \qquad c(C)=\sum_{j\in C}c_j.

$$


**定理 6.2（鲁棒证书与加权横截）。**
<a id="thm:robust-transversal"></a>
在定义 [6.1](#def:interval-certificate) 下，$C$ 是鲁棒区间证书，当且仅当

$$

 \forall i\in\{1,\ldots,m\},\qquad C\cap F_i\ne\varnothing.

$$

因此该证书规则内的最小取得成本恰为加权横截数

$$

 \tau_c=\min\left\{\sum_{j\in C}c_j:
 C\subseteq D,\ \forall i\ge1, C\cap F_i\ne\varnothing\right\}.

$$

若出现空失败边，则 $\tau_c=\infty$；若没有待排除候选，则 $\tau_c=0$。


**证明。**
两个中心位于 $[0,1]$、半径均为 $\varepsilon_j$ 的闭区间，在截到 $[0,1]$ 后仍相交，当且仅当中心距离不超过 $2\varepsilon_j$。有限直积 $B_0(C)\cap B_i(C)$ 非空，当且仅当每个坐标上的区间均相交。因此该交集为空，恰当表示存在 $j\in C$ 满足严格不等式 $|p^i_j-p^0_j|>2\varepsilon_j$。对所有候选同时应用这一等价，再取成本最小值即得结论。特别地，两个区间仅在端点接触时仍有共同记录，故严格不等式不能擅自改为非严格不等式。


证毕。


此处的最优性限于已声明的区间一致性证书。它不声称横截数等于所有似然比检验、集体量子测量或自适应统计程序的最优成本。若要从未知的有限候选中识别任意真候选，可把失败边改为所有无序候选对的
$F_{ik}=\{j:|p^i_j-p^k_j|>2\varepsilon_j\}$；同一证明给出鲁棒唯一识别的充要条件。


**推论 6.3（独立重备下的置信证书）。**
<a id="cor:sample-certificate"></a>
设 $0<\delta<1$、$D\ne\varnothing$，并先依据候选预测选定 $C$。对每个被选择的实验 $j$，能够独立重备同一个未知输入态，并执行 $N_j$ 次二元实验。取

$$

 N_j\ge
 \left\lceil\frac{\log(2|D|/\delta)}{2\varepsilon_j^2}\right\rceil.

$$

令 $\widehat p_j$ 为样本均值。若输入态为 $\rho_0$，且 $C$ 是定理 [6.2](#thm:robust-transversal) 的证书，则以至少 $1-\delta$ 的概率，$\widehat p$ 与候选 $0$ 一致，并排除全部其他候选。若一次实验 $j$ 的已声明成本上界为 $u_j$，可取 $c_j=N_ju_j$，总取得成本上界为 $\sum_{j\in C}N_ju_j$。


**证明。**
为使概率估计也自足，设 $Z$ 是均值为 $p$ 的 Bernoulli 变量。函数
$f(t)=\log\mathbb E\exp(t(Z-p))$ 满足 $f(0)=f'(0)=0$；其二阶导数是指数倾斜后的 Bernoulli 方差，故 $f''(t)\le1/4$。积分得 $f(t)\le t^2/8$。独立性和 Markov 不等式于是给出

$$

 \Pr\{\widehat p-p\ge\varepsilon\}
 \le\inf_{t>0}\exp(-tN\varepsilon+Nt^2/8)
 =e^{-2N\varepsilon^2}.

$$

负偏差同理，故两侧概率至多 $2e^{-2N\varepsilon^2}$。对 $j\in C$ 作联合界，总失败概率至多 $|C|\delta/|D|\le\delta$。在其余事件上，$\widehat p\in B_0(C)$，定理 [6.2](#thm:robust-transversal) 排除其余候选。成本逐次相加即得。


证毕。


独立重备是物理前提，不是复制未知量子态的许可。词实验的失败分支也属于一次尝试：若只统计成功后选择的样本，就改变了 $E_j$ 所描述的无条件概率。不同实验的反事实结果不能被视为同一份输入上免费取得的完整向量。上述 $u_j$ 可以计入脉冲、等待、读出和重备；若只计词长度，则应明确该成本模型的范围。若 $u_j$ 只是上界而非精确费用，以 $c_j=N_ju_j$ 求出的 $\tau_c$ 只优化这套固定样本分配下的收费上界设计，不等于全部采集协议的最小实际成本。


**计算 6.4（区间证书取得设计的加权覆盖界）。**
<a id="prop:weighted-cover-bounds"></a>
设 $m\ge1$ 且每条 $F_i$ 非空。若 $y_i\ge0$ 满足

$$

 \forall j\in D,\qquad \sum_{i:j\in F_i}y_i\le c_j,

$$

则 $\sum_i y_i\le\tau_c$。另一方面，每轮选择

$$

 \frac{c_j}{|\{i:\ i\text{ 尚未被排除且 }j\in F_i\}|}

$$

最小的实验，忽略分母为零的实验，最终得到的证书成本不超过
$H_m\tau_c$，其中 $H_m=\sum_{r=1}^m1/r$。


**证明。**
任意横截 $C$ 满足

$$

 \sum_i y_i\le\sum_{j\in C}\sum_{i:j\in F_i}y_i
 \le\sum_{j\in C}c_j,

$$

故得下界。再固定最优横截 $C_*$. 当还剩 $r$ 个未排除候选时，$C_*$ 覆盖这些候选的总重数至少为 $r$，故其中某个实验的成本除以新覆盖数量至多 $\tau_c/r$；否则求和将矛盾。贪心所选实验的比值不更大。采用经典加权覆盖贪心收费法 [Chvátal](#ref-chvatal)，把该实验成本均分给本轮新排除的候选。若本轮排除 $k$ 个，则每份收费至多 $\tau_c/r$，因而总收费至多
$\tau_c(1/r+1/(r-1)+\cdots+1/(r-k+1))$。
对各轮求和得到 $H_m\tau_c$。非空失败边保证算法能够继续，且每轮至少排除一个候选，所以有限终止。


证毕。


**命题 6.5（固定量子维数与固定容忍仍不控制证书宽度）。**
<a id="ex:rank-not-width"></a>
对任意 $m\ge2$，存在维数固定为二、容忍半径固定为 $1/8$、中心化效果秩固定为二，而证书宽度恰为 $m$ 的实验族。

**证明。** 取单 qubit，令

$$

 \theta_i=\frac{i\pi}{m}\quad(0\le i<m),\qquad
 r_m=\frac{1}{2\cos(\pi/(2m))},\qquad
 \rho_0=\frac I2.

$$

把 $m$ 个待排除候选编号为 $\sigma_i$，并取 $m$ 个许可投影实验：

$$

 \sigma_i=\frac{I+r_m(\cos\theta_iX+\sin\theta_iY)}2,
 \qquad
 E_j=\frac{I+\cos\theta_jX+\sin\theta_jY}2.

$$

这些均是合法量子对象，因为 $0<r_m\le1/\sqrt2<1$。固定所有半径为 $\varepsilon_j=1/8$。相对参考态的概率差为

$$

 \left|\operatorname{Tr}\bigl(E_j(\sigma_i-\rho_0)\bigr)\right|
 =\frac{r_m}{2}|\cos(\theta_i-\theta_j)|.

$$

当 $j=i$ 时该值为 $1/(4\cos(\pi/(2m)))>1/4$；当 $j\ne i$ 时，至多为
$\cos(\pi/m)/(4\cos(\pi/(2m)))<1/4$。
故每条严格失败边恰为 $F_i=\{i\}$，单位成本的证书宽度等于 $m$。然而全部中心化效应只张成 $\operatorname{span}_{\mathbb R}\{X,Y\}$，维数始终为二。

这一反例使用固定容忍半径；对角差异超过阈值的裕量随 $m$ 变小。它不否认可观测谱定理的带裕量结论，也不排除通过减小容忍半径、增加每项采样量而改用较小实验集。它说明认证所需的实验种类、每种实验的精度和总取得成本应分别计算。

证毕。


### 最小修复的精确累计式与离线差距


**定义 6.6（区间证书的持久修复合同）。** 在定义 6.1 的固定 $D$、候选概率律与容忍半径上，以严格失败边 $F_M$ 形成候选族 $\mathfrak M$，令 $c(R)=\sum_{d\in R}c_d$，其中全部 $c_d>0$ 固定。采用 [Persistence 定义 9.1、定理 9.2](FIB_ATOM_WHITEBOX_CERTIFICATE_PERSISTENCE.md#weighted-repair-equality) 的可行最小修复；不可行值为 $\infty$。一个集合必须同时可行并达到最小成本，只有成本或基数相等不能保证可行。

**推论 6.7（固定精度证书的在线成本）。** <a id="thm:repair-equality"></a>
若 $C_a$ 已排除 $\mathfrak M_a$，每步以可行最小修复 $R_j$ 排除 $\mathfrak M_{j+1}$，且 $C_{j+1}=C_j\cup R_j$，所有修复成本有限，则

$$
R_j\cap C_j=\varnothing,\qquad
c(C_b\setminus C_a)=\sum_{j=a}^{b-1}\rho_{\mathfrak M_{j+1},c}(C_j),\qquad
\rho^{\mathrm{off}}_{a:b,c}(C_a)\le c(C_b\setminus C_a).
$$

其中 $\rho^{\mathrm{off}}_{a:b,c}(C_a)$ 采用所引源定理的窗口联合候选族定义。最后一个不等式取等，当且仅当最终新增集为窗口残余失败边的最小成本横截。

**证明。** 定义 6.1 的区间证书等价于击中固定失败边，故正是 Persistence 定理 9.2 的 $D,F_M,c_d,C_j$ 合同。逐项代入该定理的等式和窗口结论即得。单位成本给精确基数等式；完整等式的证明仅位于该源定理。证毕。

**命题 6.8（局部最小选择产生正离线差距）。**
取 $D=\{a,b,c,d\}$、单位成本、初始边 $\{d\}$ 与 $C_0=\{d\}$。随后依次加入边 $\{a,b\}$ 和 $\{a,c\}$。这些边可由布尔目标恒为零、每个候选恰在其失败边上输出一来实现。

**证明。** 第一轮选 $a$ 或 $b$ 都是成本一的最小修复。选 $a$ 后第二轮无需新增，最终新增成本为一；选 $b$ 后第二轮须再选 $a$ 或 $c$，最终新增集为 $\{a,b\}$ 或 $\{b,c\}$，两者成本均为二。离线最优新增集是 $\{a\}$，成本一。因此第二条路径的在线差距为一，但从未重复取得同一个观察点；多花的成本来自第一轮选择对未来覆盖不足。证毕。


若目标、概率律或误差容忍随时间改变，则失败边也改变，旧记录不一定继续有效。须把实验时刻、状态制备和精度作为记录标签的一部分，重新建立可复用条件。重复采样以缩小误差条也不是原有集合合同中的免费复用；它有新增样本成本。


### 有限比较深度的一个加强


**命题 6.9（指定 FIB 四态表的候选比较深度）。** 采用 [逃逸深度卷 §4 的明确转移及 End 表](FIB_ATOM_ESCAPE_WITNESS_DEPTH_AND_ROBUST_WHITEBOX.md)，并只按该表定义参考任务。参考未来商有 $q=4$ 个状态；一个候选总确定性 Moore 模型从指定种子可达 $K\ge1$ 个状态，采用相同窗口字母与输出，并比较空词 End。若某未来响应不同，则有长度至多 $K+2$ 的区别窗口词。若同时比较四个参考种子，$K$ 取四个候选种子可达状态并集的大小。

**证明。**
采用经典 Moore 划分细化 [Berstel–Boasson–Carton–Fagnot §4.1](#ref-moore) 作为支持步骤。对一般参考商大小 $q$，取参考商与候选可达部分的不交并，得到至多 $q+K$ 个状态的总转移系统。令 $P_n$ 按所有长度至多 $n$ 的未来输出一致来划分该系统。确定性给出递推：两状态在 $P_{n+1}$ 同类，当且仅当它们当前输出相同，且对每个输入字母，其后继在 $P_n$ 同类。因此 $P_{n+1}$ 细化 $P_n$；若某一步相等，后续所有划分均相等。

令 $\ell$ 为所选初态的最短区别词长度。若 $\ell=0$，结论显然。若 $\ell>0$，在 $P_0$ 至 $P_\ell$ 之间不能有平台，否则初态不可能在第 $\ell$ 步才分开。每步故至少增加一个等价类。存在可区别状态还意味着 $P_0$ 至少有两个类：若所有状态当前输出相同，则所有未来输出也相同。因而

$$

 2+\ell\le |P_\ell|\le q+K,

$$

即得 $q+K-2$；在本命题中代入 $q=4$ 得 $K+2$。


证毕。


仓库的乘积路径证明给出 $qK-1$；上述经典划分细化方法的直接应用改进该数值界，因为差值为 $(q-1)(K-1)\ge0$。对该 FIB 四态任务，这把指定初态比较界从 $4K-1$ 加强到 $K+2$。该结论要求有限的候选可达状态数与精确读出；不从有限测试的近似一致自动推出所有未来近似一致，也不把深度界当作测试总数界。字母表含 $k$ 个字母时，枚举所有长度不超过 $L$ 的词仍可能涉及 $\sum_{r=0}^{L}k^r$ 项。[repo_escape_depth](#ref-repo_escape_depth)


### 离散未来类的零误差量子记忆提升


**命题 6.10（十一类原生联合未来的条件量子记忆下界）。** 采用 [原生联合未来的十一类分类及离散记忆输入](#ref-lean_native_memory)。另假设各类 $c$ 编为同一有限维空间 $\mathcal H$ 上的一份密度矩阵 $\sigma_c$；每个可选择查询 $t$ 都供应共同的合法 POVM $\{E_o^t\}$，以概率一返回该类的确定回复 $r_c(t)$：

$$
\operatorname{Tr}(E_o^t\sigma_c)=\mathbf1_{\{o=r_c(t)\}}.
$$

不同类有某查询的回复不同。在这些附加条件下，$\dim\mathcal H\ge11$；若记忆是 $n$ 个 qubit，则 $n\ge4$。

**证明。**
采用经典概率一完美区分的正交支撑论证 [Watrous，第3章](#ref-watrous) 作为支持步骤。一般地，对 $K$ 个这样的确定回复类，固定 $c\ne c'$，选取能区分它们的 $t$，并令 $E=E^t_{r_c(t)}$。于是 $0\le E\le I$，且 $\operatorname{Tr}(E\sigma_c)=1$、$\operatorname{Tr}(E\sigma_{c'})=0$。写 $\sigma_c=\sum_s\lambda_s|v_s\rangle\langle v_s|$，其中 $\lambda_s>0$ 且 $v_s$ 张成支撑。由

$$

 0=\operatorname{Tr}((I-E)\sigma_c)
 =\sum_s\lambda_s\langle v_s,(I-E)v_s\rangle

$$

及每项非负，知 $(I-E)^{1/2}v_s=0$，故 $Ev_s=v_s$。同理，$\sigma_{c'}$ 支撑上的每个 $w$ 均满足 $Ew=0$。因此
$\langle v_s,w\rangle=\langle Ev_s,w\rangle=\langle v_s,Ew\rangle=0$。
任意两类的支撑均正交，每个密度矩阵的支撑维数至少为一，所以总维数至少为 $K$。在指定任务中 $K=11$，故 $\dim\mathcal H\ge11$；$n$ 个 qubit 的维数为 $2^n$，于是 $n\ge\lceil\log_2 11\rceil=4$。


证毕。


对仓库原生联合未来任务的十一类分类，只有补上本命题中的单份量子记忆、可选查询的合法 POVM 以及概率一正确读出，才可进一步推出至少十一维、至少四个 qubit。该结论的附加条件不同于既有有限离散载体基数下界的条件。它不主张十一维一定足以实现全部更新，也不涵盖允许读出误差的编码。查询可以消耗记忆；证明未要求同一份记忆在测量后还能连续回答其他问题。

## 7. 任务价值：后验跨阈值与 Bayes 收益
<a id="sec:decision"></a>

仓库的任务风险卷已经证明：信息量增加不保证零一风险严格下降，
而嵌套读出满足一个平方根型信息上界 [repo_bayes](#ref-repo_bayes)。
本节继续给出收益发生位置的精确公式，并在明确的任务裕量条件下加强该界。
这些量是已取得经典记录上的决策性质；不把它们直接认作量子态的拓扑不变量。


**定义 7.1（细化读出与任务裕量）。** <a id="def:margin"></a>
设 $Y\in\{0,1\}$ 为任务标签，$R$ 为有限精细记录，
$Q=f(R)$ 为它的确定性粗化。所有概率来自同一个联合分布。
在正概率记录上定义

$$

\eta=\mathbb P(Y=1\mid Q),\qquad
\xi=\mathbb P(Y=1\mid R),\qquad
v=\xi-\eta,\qquad m=|\eta-\tfrac12|.

$$

零一损失下的最优风险为

$$

e(Q)=\mathbb E\min(\eta,1-\eta),\qquad
e(R)=\mathbb E\min(\xi,1-\xi).

$$

取 $s=1$ 当 $\eta\ge1/2$，否则 $s=-1$。
条件信息量用自然对数表示为
$\mathcal I=I(Y;R\mid Q)$；若使用比特，则
$\mathcal I=(\ln2)I_{\mathrm{bits}}$。


**定理 7.2（跨决策阈值的精确收益）。** <a id="thm:crossing"></a>
在定义 [7.1](#def:margin) 下，

$$

\Delta e=e(Q)-e(R)
=2\,\mathbb E[(-sv-m)_+]\ge0.

$$

对一个满足 $\eta>1/2$ 的粗记录纤维，细化的收益恰为
$2\mathbb E[(1/2-\xi)_+\mid Q]$；
对 $\eta<1/2$ 的纤维，则恰为
$2\mathbb E[(\xi-1/2)_+\mid Q]$。
因此在有严格粗多数的纤维上，严格收益当且仅当细后验以正概率越过原决策阈值。


**证明。**
条件期望的塔性质给 $\mathbb E[v\mid Q]=0$。
又有 $\min(z,1-z)=1/2-|z-1/2|$，所以

$$

\Delta e=\mathbb E\bigl[|\xi-\tfrac12|-|\eta-\tfrac12|\bigr].

$$

因为 $\eta-1/2=sm$，有 $|\xi-1/2|=|m+sv|$。
用 $|z|=z+2(-z)_+$ 得

$$

|\xi-\tfrac12|-m=sv+2(-sv-m)_+.

$$

第一项的条件期望为零，即得公式与非负性。
将 $\eta$ 位于阈值的哪一侧代入，得到两个条件公式。
非负随机变量的期望严格为正，当且仅当它以正概率严格为正，
给出最后的充要条件。$\eta=1/2$ 时同一公式仍成立，
此时条件收益等于 $\mathbb E[|v|\mid Q]$。


证毕。


**定理 7.3（有裕量时的信息收益加强）。** <a id="thm:marginbound"></a>
采用 [任务风险卷 §5](FIB_ATOM_TASK_INFORMATION_BAYES_RISK_GEOMETRY.md) 的同律平方根界，总有

$$

0\le\Delta e\le\sqrt{\mathcal I/2}.

$$

若还存在 $\gamma>0$，使 $m\ge\gamma$ 几乎处处，则进一步有

$$

\boxed{\quad
\Delta e\le
\min\left\{\sqrt{\frac{\mathcal I}{2}},
           \frac{\mathcal I}{4\gamma}\right\}
=
\min\left\{\sqrt{\frac{\ln2}{2}I_{\mathrm{bits}}},
           \frac{\ln2}{4\gamma}I_{\mathrm{bits}}\right\}.
\quad}

$$


**证明。**
条件互信息的定义直接给

$$

\mathcal I
=\mathbb E\,D\bigl(\operatorname{Bern}(\xi)
                 \,\|\,\operatorname{Bern}(\eta)\bigr).

$$

在 $0<\eta<1$ 时，视 $D(\operatorname{Bern}(u)\|
\operatorname{Bern}(\eta))$ 为 $u$ 的函数，
它在 $u=\eta$ 处的值及一阶导数为零，二阶导数为
$1/[u(1-u)]\ge4$。积分两次得到

$$

D(\operatorname{Bern}(u)\|\operatorname{Bern}(\eta))
\ge2(u-\eta)^2.

$$

端点由连续极限解释；若 $\eta=0$ 或 $1$，
塔性质和 $0\le\xi\le1$ 强制该纤维上 $\xi=\eta$，
所以也无额外项。因此
$\mathbb E v^2\le\mathcal I/2$。
风险函数 $u\mapsto\min(u,1-u)$ 为一 Lipschitz，
故 $\Delta e\le\mathbb E|v|\le\sqrt{\mathbb E v^2}$，
证明第一界。

对 $m>0$ 和任意实数 $z$，有

$$

(z-m)_+\le \frac{z^2}{4m}.

$$

当 $z<m$ 时显然；当 $z\ge m$ 时它等价于
$(z-2m)^2\ge0$。应用跨阈值公式，并用 $m\ge\gamma$，
得到

$$

\Delta e\le\frac{\mathbb E v^2}{2\gamma}
\le\frac{\mathcal I}{4\gamma}.

$$

两界同时成立，故可取较小者。


证毕。


**命题 7.4（弱门任务的阈值行为）。**
存在正信息零收益的细化；而定义 3.4 的弱门二点任务在首阶达到平方根信息界。

**证明。** 若只有一个粗记录，$\eta=3/4$，
而两个等概率细记录分别给 $\xi=5/8,7/8$，
则信息增量严格正，但所有细后验都在阈值同一侧，
所以 $\Delta e=0$。

对五模任务 [3.4](#def:fibpair)，取 $Q$ 为常量摘要，$R$ 为一次弱门协议的记录，
于是确有 $Q=f(R)$。端点菜单对此任务也不含标签信息，
粗后验为 $1/2$，不存在正的统一粗裕量。
一次弱门协议的精确收益和信息量则为

$$

\Delta e_q=\frac{|\sin(2q\epsilon)|}{2},\qquad
I_{\mathrm{bits},q}
=1-h_2\!\left(\frac{1-|\sin(2q\epsilon)|}{2}\right).

$$

固定 $q$ 并令 $\epsilon\to0$，得到

$$

\Delta e_q=q|\epsilon|+O(|\epsilon|^3),\qquad
I_{\mathrm{bits},q}
=\frac{2q^2\epsilon^2}{\ln2}+O(\epsilon^4).

$$

这里 $h_2$ 是二元熵。公式由均匀二点来源与对称 Bernoulli 通道直接算得。
这使平方根信息界在首阶上取等；它也解释为何仅凭 Gramian 的
$O(\epsilon^2)$ 特征值，不能把零一任务收益误读成同阶数。

证毕。


## 8. 原生递归来源：有限表示与有限时间取得
<a id="sec:time"></a>

这一节采用递归联合预测卷 [repo_joint](#ref-repo_joint) 的指定来源。
固定整数 $m\ge3$。我们使用其固定的有序二叉来源树、颜色 $q(p)\in C_m$、
深度 $d(p)$ 和单位边速率连续时间过程；颜色函数采用该卷规定的有序子节点递归，
不能替换为任意循环着色。
实际观察为 $O(p)=(q(p),d(p))$，包含精确跳时。
读出在本节保持被动，不加入新的主动门。

来源卷已经证明以下三个输入事实：


-  长度 $h$ 的祖先颜色签名
$S_h(p)=(d(p),q(p),q(\operatorname{par}p),\ldots)$
截到根或第 $h$ 个祖先。相应有限跳实验的全部律由它精确决定，
同一深度 $h$ 的 $2^h$ 个地址具有不同的完整签名。

-  给定当前颜色和深度时，$k\ge1$ 的签名可用至多
$3\cdot2^{k-1}$ 个辅助符号表示。
这是一项静态表示结论，不是从路径中取得该符号的程序。

-  若两起点具有相同 $S_k$，则其长度 $T$ 的完整观察路径律满足

$$

\operatorname{TV}(\mathsf L_p^T,\mathsf L_{p'}^T)
\le b_k(T),\qquad
b_k(T)=\mathbb P\{\operatorname{Pois}(3T)>k\}.

$$

同一速率三时钟给直接耦合，因此此式没有因子二；
虚拟根停留只属于支配时钟，不能当作实际来源跳跃。


这三条分别来自该卷定理2.1--2.2、3.2及4.1。
下面从这些已给出的来源定理推出一个新的取得成本结论。


**定理 8.1（精确未来不同的有限时间困难对）。** <a id="thm:poissoncost"></a>
取整数 $k\ge1$、深度 $h$，满足

$$

2^h>3m\,2^{k-1}.

$$

则在深度 $h$ 上存在两个不同起点 $p,p'$：
它们完整未来不同，但有相同 $S_k$。
固定任意 $T>0$。
另行供应 $N$ 条来自同一个未知起点的独立重备轨迹，
每条只观察长度 $T$；这定义本定理的样本资源。
对在 $p,p'$ 之间进行等先验判别的任何后处理，最优错误率满足

$$

e_N^*\ge\frac{(1-b_k(T))^N}{2}
       \ge\frac{[1-Nb_k(T)]_+}{2}.

$$

因此，要使 $e_N^*\le1/4$，必要有

$$

N\ge\frac{\log2}{-\log(1-b_k(T))}
\quad\text{以及}\quad
N\ge\frac{1}{2b_k(T)}.

$$

若 $k+1>3T$，还得到

$$

\boxed{\quad
N\ge\frac{e^{3T}}2
       \left(\frac{k+1}{3eT}\right)^{k+1}.
\quad}

$$

固定 $T$ 而让 $k$ 增长，这给出很快增长的最坏情形取得下界。


**证明。**
在固定深度 $h$ 上，当前颜色至多有 $m$ 种；
给定颜色的 $k$ 签名至多有 $3\cdot2^{k-1}$ 种，
所以总签名数至多为 $3m2^{k-1}$。
严格计数条件和抽屉原理给出两个不同地址共用 $S_k$。
完整深度签名的单射性及来源卷的分类定理保证它们完整未来不同。

单条路径的直接来源耦合使两条观察不一致的概率至多 $b=b_k(T)$。
取 $N$ 个独立耦合，所有路径都一致的概率至少为 $(1-b)^N$，
因此乘积观察律的 TV 至多 $1-(1-b)^N$。
任何后处理均不能增大 TV：每个输出事件的逆像是原记录事件。
二点 Bayes 公式于是给出第一个错误率下界，
再用 $(1-b)^N\ge1-Nb$ 并取非负部分得第二个。
$T>0$、有限 $k$ 时 $0<b<1$，
对 $(1-b)^N\le1/2$ 取对数给第一个必要条件；
由第二界得到 $Nb\ge1/2$。

最后令 $Z\sim\operatorname{Pois}(\lambda)$，$\lambda=3T$。
其矩母函数由级数直接计算为
$\mathbb E e^{tZ}=\exp[\lambda(e^t-1)]$。
对 $r=k+1>\lambda$，以 $t=\log(r/\lambda)>0$ 用 Markov 不等式：

$$

\mathbb P(Z\ge r)
\le\exp[-r\log(r/\lambda)+r-\lambda]
=e^{-\lambda}\left(\frac{e\lambda}{r}\right)^r.

$$

代入 $N\ge1/(2b)$，即得所列下界。


证毕。


这是存在一个困难来源对的最坏情形结论，不是说深度 $h$ 的每一对都同样难。
允许精确时间戳并未消除它，因为界已经针对完整路径。
任何仅使用这段记录的被动提前停止或解码也受此界约束；
能主动改变来源动力学的新控制不在本定理的合同内。

原文的辅助符号构造还给出至多 $h+1$ 个额外固定二进制位，
前提是当前颜色与无界深度已作为旁信息供应 [repo_joint，定理3.2](#ref-repo_joint)。
本定理说明：即使该静态表示很短，从有限时间随机轨迹中实际取得它仍可能需要大量新准备。
表示长度、供给旁信息、轨迹长度和重备次数是四个不同的成本项。


## 9. 受限高阶过程延拓的输入范围

**假设 9.1（指定超通道反例输入）。** 采用 [Daly 受限超通道最小延拓反例](#ref-lean_daly)：$\operatorname{SCPTP}(d,r)$ 为 CPTP 映射 $M_d\to M_r$ 的复线性张成；$\Gamma$ 定义在该受限空间上。延拓 $G$ 是全部线性映射空间上的超通道，并在该受限空间上一致。具体输入满足 $d_1=r_1=d_2=r_2=2$。信道的 Choi 矩阵为 $4\times4$，超映射 Choi 矩阵为 $16\times16$。

该输入给出同一 $\Gamma$ 的合法延拓族 $S_s$（$-1\le s\le1$），满足

$$
S_0=\tfrac12S_1+\tfrac12S_{-1},\qquad S_1\ne S_{-1},\qquad
\forall G\in\operatorname{Ext}(\Gamma),\quad
 e(G)=\operatorname{rank}\left(\operatorname{Tr}_{r_1}\operatorname{Tr}_{r_2}
 C_{\widetilde G}\right)=4.
$$

**命题 9.2（该输入对预测实现所给的限制）。** 受限效果空间上的一致行为及最小化上述 $e$，不足以推出延拓唯一或延拓为实凸极端点。

**证明。** $S_1,S_{-1}$ 不同但延拓同一 $\Gamma$，故唯一性不成立。全部合法延拓的 $e$ 都是四，故 $S_0$ 为最小化者；它是两个不同合法延拓的中点，故不是极端点。这里满秩的是指定的 $4\times4$ 部分迹；此计算没有要求全部 $16\times16$ Choi 矩阵满秩，也没有排除其他极端最小化者。由全未来商进一步要求唯一性、极端性、更新兼容或合法门实现，分别是额外数学条件，不能由此最小秩指标推出。证毕。


## 10. 数学来源

**约定 10.1（来源与适用范围）。** 下列仓内输入采用固定数学来源 `9f20f4efdb4c90cc1e07fa7e481ffc0dc86234c3` 的相应定义与结果；量子边界 §§13–14 的明确常数及完整记录精度取 `b84d469298a8d601e21f85bcc1d6085e3cf557f5` 的对应条目。修复结论采用 Persistence §9 与 Horizon §8。经典文献只支持各证明内明示的中间步骤。

<a id="ref-repo_relational"></a>
[关系丛与预测闭包](AURIC_FIB_RELATIONAL_BUNDLE_AND_PREDICTIVE_CLOSURE_THEORY.md)，定理 8.4、8.6、8.11：全未来商、常秩像核丛、理想保码代码控制。

<a id="ref-repo_context"></a>
[语境与谱重构](AURIC_LANGLANDS_CONTEXT_AND_SPECTRAL_RECONSTRUCTION_THEORY.md)，§2.1：许可传播。

<a id="ref-repo_structure"></a>
[结构取得与谱延拓](AURIC_LANGLANDS_STRUCTURE_ACQUISITION_AND_SPECTRAL_EXTENSION_THEORY.md)，§§2、4、15：残余线性系统、实二拷贝统计和固定协变量碰撞。

<a id="ref-repo_cover"></a>
[取得、覆盖与临界域](AURIC_LANGLANDS_ACQUISITION_COVER_AND_CRITICAL_DOMAIN_THEORY.md)，命题 4.5、4.6：选层、可执行置换与固定锚点的两两区别。

<a id="ref-repo_escape_spectrum"></a>
[定量逃逸谱](FIB_ATOM_QUANTITATIVE_ESCAPE_SPECTRUM_WHITEBOX.md)：有限确定性来源与指定损失下的风险；加性坐标损失取逐坐标正负质量之小者，完整标签零一损失取完整标签众数。

<a id="ref-repo_escape_depth"></a>
[逃逸见证深度](FIB_ATOM_ESCAPE_WITNESS_DEPTH_AND_ROBUST_WHITEBOX.md)，§4：四态明确转移表与乘积区别界。

<a id="ref-repo_cert_hypergraph"></a>
[失败证书超图](FIB_ATOM_WHITEBOX_CERTIFICATE_HYPERGRAPH.md)：静态失败边与横截。短词下界向真实递归来源传递须有逐限制保持的编码及额外测试的回译。

<a id="ref-repo_cert_persistence"></a>
[证书持久性](FIB_ATOM_WHITEBOX_CERTIFICATE_PERSISTENCE.md)，§§1–4、9：残余失败族及可行正成本最小修复。

<a id="ref-repo_cert_horizon"></a>
[证书未来窗口](FIB_ATOM_WHITEBOX_CERTIFICATE_HORIZON.md)，§§1–5、8：离线横截与在线差距；有限饱和界限制严格增长次数，不限制最后一次增长的绝对时刻。

<a id="ref-repo_bayes"></a>
[任务信息与 Bayes 风险](FIB_ATOM_TASK_INFORMATION_BAYES_RISK_GEOMETRY.md)，§§4–5：正信息零风险收益与同律平方根信息界。

<a id="ref-repo_joint"></a>
[递归来源的有限联合预测](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_FINITE_JOINT_PREDICTION.md)，定理 2.1、2.2、3.2、4.1：固定有序来源、签名分类、辅助字母表与直接同钟 Poisson 耦合。

<a id="ref-lean_accepted"></a>
[接受词效果传播](https://github.com/the-omega-institute/trureturing/blob/9f20f4efdb4c90cc1e07fa7e481ffc0dc86234c3/D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation.lean)：`propagation_eq_accepted`、`simultaneous_stabilization`、`arbitrary_chain_delay`。有限控制状态集合 $Q$、有限维空间 $E$、接受集合 $F$ 与初始效果子空间 $U$ 的共同稳定界为 $|Q|\dim E-|F|\dim U$；同时在所有控制节点稳定才推出后续稳定。恒等转移链允许初始节点效果延迟任意长度，故单节点一步平台不是闭包判据。该线性输入不包含完全正性、实验取得或采样精度。

<a id="ref-lean_native_memory"></a>
[原生联合未来记忆下界](https://github.com/the-omega-institute/trureturing/blob/9f20f4efdb4c90cc1e07fa7e481ffc0dc86234c3/D5/S3/Arith/FibonacciAtomic/Observer/FutureResponses/NativeJointFutureMemoryLowerBound.lean)：十一类分类；有限离散 $W$、满射 $\mathrm{memory}:\mathrm{Source}\to W$、全部联合未来回复经记忆重构，推出 $11\le|W|$。单份量子记忆的维数结论另需命题 6.10 的概率一查询条件。

<a id="ref-lean_daly"></a>
[Daly 超通道延拓输入](https://github.com/the-omega-institute/trureturing/blob/9f20f4efdb4c90cc1e07fa7e481ffc0dc86234c3/D5/S3/QuantumChannels/DalySuperchannelMinimalExtension.lean)：`SCPTP`、`extensions`、`e` 及 `result`，只在假设 9.1 的指定部分迹秩与凸性范围使用。文献背景为 [Daly, Axiomatic approach to quantum superchannels](../../../Library/QuantumContext/daly2022axiomatic.md)。

<a id="ref-penrose"></a>
R. Penrose, *A generalized inverse for matrices*, Proc. Cambridge Philos. Soc. 51 (1955), 406–413，[doi:10.1017/S0305004100030401](https://doi.org/10.1017/S0305004100030401)：四个 Moore–Penrose 方程及有限矩阵逆；[仓内引文](../../../Library/Analytic/penrose1955generalized.md)。

<a id="ref-golub"></a>
G. H. Golub and V. Pereyra, *The differentiation of pseudo-inverses and nonlinear least squares problems whose variables separate*, SIAM J. Numer. Anal. 10 (1973), 413–432，[doi:10.1137/0710036](https://doi.org/10.1137/0710036)：固定秩广义逆与投影的正则性；计算 2.2 使用其有限维局部矩阵公式。

<a id="ref-hoeffding"></a>
W. Hoeffding, *Probability inequalities for sums of bounded random variables*, JASA 58 (1963), 13–30，[doi:10.1080/01621459.1963.10500830](https://doi.org/10.1080/01621459.1963.10500830)：独立有界变量指数矩方法；此处每个 Bernoulli 常数由显示的二阶导数计算给出。

<a id="ref-fuchs"></a>
C. A. Fuchs and J. van de Graaf, *Cryptographic distinguishability measures for quantum-mechanical states*，[arXiv:quant-ph/9712042](https://arxiv.org/abs/quant-ph/9712042)：亲和量、总变差与二点判别的经典比较。

<a id="ref-bierstone_milman"></a>
E. Bierstone and P. D. Milman, *Semianalytic and subanalytic sets*, Publ. Math. IHÉS 67 (1988), 5–42，[推论 2.11，印刷页 14；定理 6.4、附注 6.5，印刷页 34](https://www.numdam.org/item/PMIHES_1988__67__5_0.pdf)：局部有限半解析集合族的相容解析分层；实解析流形上具有紧图的次解析函数之零集包含所给的距离幂界。

<a id="ref-trotman"></a>
D. Trotman, *Équisingularité et conditions de Whitney*，[所收 *Whitney stratifications — faults and detectors* 第 0 章，印刷页 5](https://www.numdam.org/item/BJHTUP11_1980__0097__P0_0.pdf)：半解析集的解析分层及解析 Whitney 细分存在性；只在实解析效果族的秩集合使用。

<a id="ref-chvatal"></a>
V. Chvátal, *A greedy heuristic for the set-covering problem*, Math. Oper. Res. 4 (1979), 233–235，[doi:10.1287/moor.4.3.233](https://doi.org/10.1287/moor.4.3.233)：正权覆盖的经典贪心法。计算 6.4 给出本区间证书所需的完整调和收费推导。

<a id="ref-moore"></a>
J. Berstel, L. Boasson, O. Carton and I. Fagnot, *Minimization of automata*，[§4.1，命题 4.1–4.2](https://arxiv.org/abs/1010.5318)：Moore 细化与 $n-2$ 深度；命题 6.9 使用其不交并应用。

<a id="ref-watrous"></a>
J. Watrous, *The Theory of Quantum Information*，[第 3 章，定理 3.4](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf)：Holevo–Helstrom 判别与概率一可区分性的经典支撑结论。

## 追加锚（本行以下为增补区）
