# AURIC：归一化单位与观察者原点

# 三轴平方和的精确意义

**定义、定理与纸面证明　v41.0**

2026 年 10 月 31 日　Asia/Singapore

<!-- editorial-start:metadata -->
> **转写元数据（编者说明）**  
> PDF 标题：AURIC：归一化单位、观察者原点与三轴二次不变量。  
> PDF 作者：AURIC research continuation。  
> PDF 主题：Operational units, observer reference states, Bloch geometry and five-mode purity budgets。  
> 原页眉：AURIC：归一化、观察者原点与二次不变量；v41 / 2026-10-31。原页脚为页码。  
> 源稿 SHA-256：<code>a1296780<wbr>2c636d75<wbr>624abd7f<wbr>99eaf5ac<wbr>a7a1af9e<wbr>9d89222b<wbr>d899ec45<wbr>0dc37631</code>。  
> 下文保留作者原稿及纸面证明；节内共用的陈述编号与交叉引用显式展开，无编号展示式不另加编号。正文的“本轮”、十九条变化路径、十六份来源 blob、来源读取、提交时间，以及未运行 Lean、数学数值、CAS、枚举、门字搜索和未修改项目仓库等说法，均归属于作者写作时的历史陈述，不是本次转写重新完成的历史检查或数学认证。与 v40 固定版本的比较及记忆核说明沿用原稿归属；本次不以该稿补足本文的证明。另列的编者符号说明只限定原定义已经使用的输入，不改写作者定义。
<!-- editorial-end:metadata -->

## 摘要

本文回答五模式中的 $F[\mathrm{null}]$、归一化与三轴平方和分别承担什么信息。
原生空模式是一个特定事件及其范数一的模式向量，归一化对应全部事件之和的单位元。
在有限复观测代数的完整态域上，三个线性读出可信息完备，当且仅当自伴代数维数至多四；
恰为三维的完整归一化态空间只有量子二能级球与经典四事件单纯形两类。
二元正矩阵的齐次坐标满足 $s^2-|r_{\rm hom}|^2=4\det M$：
$s=1$ 是归一化截面，Bloch 半径平方决定纯度；共同内部酉等价下的归一化 Gram 关系也由三数完整分类。
将观察者参考态作为坐标原点时，纯度需要恢复中心及读出度量。
对原五模式，本文给含联合概率的四维正定二次式，并补齐全部相干项；
对最新原生块观测代数，给块权重与块纯度分解。
最后证明内部条件归一化的误差放大界、单分支递归的行列式乘法律及全态半径守恒的酉性判据。
全部数学为纸面推导；读取、文本核对与排版不作为数学数值验证。

<a id="section-1"></a>

## 1　固定项目、对象与本轮推进

本轮固定默认分支 `dev` 提交

<code>79783aa4<wbr>9bcdbb3e<wbr>7def3499<wbr>37515a7e<wbr>9e7b4b76</code>，

 提交标记时间为 2026-10-31 15:00:08（新加坡）。
与 v40 固定的 `30933a24a1348` 比较，完整理论子树有十九条变化路径；
本轮定向核对十六份直接相关来源的 blob 身份。没有以源码导入代替独立数学认证，
没有运行 Lean、数学数值、CAS、枚举或门字搜索，也没有修改项目仓库。[[1](#bib-head)]

最直接的原定义是量子原则主卷定义 1.1–1.2：
$F[\mathrm{null}]$ 对应合法模式 $000$；
其量子表示 $\lvert N \rangle$ 是范数一向量，可在另供的几何标定中映到锚点，
但它不是零向量、空历史、停止符或代数单位。
基础公式卷已经明确区分空事件 $e_N$ 与常数一。
V24 §3 已给 Bloch、Hopf 及内部 Gram 余量的标准计算。[[2](#bib-main), [3](#bib-pyramid), [4](#bib-v24)]
本稿将这些既有结果统一到单位元、态、事件、参考原点与可见代数的不同角色中，
并推导一般读出度量、三维态域分类、五模式完整二次预算及带质量的递归公式。

最新续卷 III §151 识别原受限菜单可读的块代数，明确把归一化写为
$\ell_z(I_{\mathcal K_i})=1$；纯的全载体态在该代数上的预测代表仍可为块混合。
§146 的活动二维块先保留绝对质量 $m$，仅在 $m>0$ 时定义条件 Bloch 向量。
新增 Pauli-channel 文稿 §1 则在完整两 qubit 域中保留六个边缘坐标和九个关系坐标。
这些是本轮直接消费的最新接口；没有消费该文的熵优化或未决全域不等式。[[5](#bib-iii), [6](#bib-pauli)]

<a id="statement-1-1"></a>

#### 定义 1.1（单一本体与内部接口）

固定一个复含单位代数 $\mathcal A$ 及正归一泛函 $\omega$，即
$\omega(A^\dagger A)\ge0$、$\omega(1_{\mathcal A})=1$。
有限观察接口是一项明确给出的有限维观测代数或效果空间；
参考态、记录、控制和程序均在整体内部。下文有限维矩阵表示与复结构是所声明的输入。
涉及全态域的命题描述同一接口的响应结构；它不授予任意数学态的实际准备能力。

<!-- editorial-start:adjoint -->
> **编者符号说明（定义 1.1 的输入）**　这里的复含单位代数还须另供与代数运算相容的共轭线性对合，记作 $A\mapsto A^\dagger$；正性条件 $\omega(A^\dagger A)\ge0$ 使用这项输入。任意复含单位代数本身并不自动带有这样的对合。下文矩阵接口中的 $\dagger$ 取通常的共轭转置。
<!-- editorial-end:adjoint -->

为防符号混用，五模式占位均值写为 $X,Y,Z$，其联合概率为 $\kappa$；
二能级 Pauli 期望写为 $r=(r_1,r_2,r_3)$。把后者命名为 $x,y,z$ 时，
本文关于 $|r|^2$ 的公式就是所询问的 $x^2+y^2+z^2$。
把三个 Pauli 方向标成 $F[1],F[3],F[2]$ 需要另给算符标定；
原生三个可交换占位算子不能只凭几何名称变成 Pauli 算子。

<a id="section-2"></a>

## 2　原五模式：归一化单位与空模式

<a id="statement-2-1"></a>

#### 定义 2.1（事件与读出）

按 $(N,1,2,3,13)$ 排列五模式，分别对应原数值标签 $(N,2,3,5,25)$。
令 $\xi,\eta,\zeta$ 为位置 $1,3,2$ 的占位函数，满足
$\xi^2=\xi,\eta^2=\eta,\zeta^2=\zeta$ 和 $\xi\zeta=\eta\zeta=0$。
联合事件为 $\xi\eta$。全部实函数的基为

$$
1,\quad \xi,\quad \eta,\quad \zeta,\quad \xi\eta .
$$

其中常数一与空模式事件是不同函数。[[3](#bib-pyramid), [2](#bib-main)]

<a id="statement-2-2"></a>

<a id="thm:unit"></a>

#### 定理 2.2（归一化的精确位置）

五个互斥事件为

$$
\begin{aligned}
e_N&=1-\xi-\eta-\zeta+\xi\eta,\\
e_1&=\xi-\xi\eta,\qquad e_2=\zeta,\qquad
e_3=\eta-\xi\eta,\qquad e_{13}=\xi\eta.
\end{aligned}
$$

它们满足 $e_se_t=\delta_{st}e_s$、$\sum_s e_s=1$，而 $e_N\ne1$。
在五维量子表示中，令 $P_s=\lvert s \rangle \langle s \rvert$，则

$$
\sum_sP_s=I_5,\qquad
\sum_s p_s=\operatorname{Tr}\rho=1,\qquad p_s=\operatorname{Tr}(\rho P_s).
$$

因此归一化是状态在单位元上的条件，空窗概率 $p_N$ 是状态信息的一部分。

**证明。**

在五个合法占位点逐一代入，每个 $e_s$ 恰是对应点的指示函数，
故互斥、穷尽。$e_N$ 在空模式为一，在其余四模式为零；
常数一在五处均为一。量子式由正交基投影的和为恒等算子及迹的线性性得到。

∎

<a id="statement-2-3"></a>

#### 命题 2.3（全域归一效果的唯一性）

若有限维 Hermitian 算子 $E$ 对全部密度态满足 $\operatorname{Tr}(\rho E)=1$，
则 $E=I$。同样，在有限直和矩阵代数上，对全部状态取值一的自伴元只能是单位元。

**证明。**

逐块取所有纯向量态，得到 $\langle v \rvert (E-I)\lvert v \rangle =0$。
齐次化后，以 $e_j,e_j+e_k,e_j+i e_k$ 的二次型恢复全部矩阵元，
即得 $E-I=0$。若只知道一个固定状态的期望为一，则没有此结论。

∎

<a id="statement-2-4"></a>

<a id="thm:fiber"></a>

#### 定理 2.4（质量坐标、归一化截面与三轴纤维）

对任意非负模式质量 $w_s$，令

$$
s=\sum_s w_s,\quad X=w_1+w_{13},\quad Y=w_3+w_{13},
\quad Z=w_2,\quad \kappa=w_{13}.
$$

这五数是完整线性坐标，反解为

$$
\boxed{(w_N,w_1,w_2,w_3,w_{13})
=(s-X-Y-Z+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa).}
$$

归一化是 $s=1$。在该截面上，固定三轴的完整概率纤维为

$$
\max(0,X+Y+Z-1)\le\kappa\le\min(X,Y).
$$

三轴可行域恰为

$$
\mathcal P=\{X,Y,Z\ge0:\ X+Z\le1,\ Y+Z\le1\},
\qquad X+Y+Z=1-p_N+p_{13}.
$$

**证明。**

由定义依次恢复 $w_{13},w_2,w_1,w_3,w_N$。
当 $s=1$ 时五项非负恰给所列区间。
区间非空等价于三轴非负及两个上界；按反解即可实现每个合法点。
最后一个恒等式由概率和直接相加。

∎

例如 $\tfrac12\delta_N+\tfrac12\delta_{13}$ 与
$\tfrac12\delta_1+\tfrac12\delta_3$ 均给 $(X,Y,Z)=(1/2,1/2,0)$，
联合概率却为 $1/2$ 与零。故三维金字塔是四维概率单纯形的一个读出像。
在五个互斥事件概率中，已知任意四项和总和一确能恢复第五项；
在 $(1,X,Y,Z,\kappa)$ 这组函数读出中，常数一已经固定，
三个轴通常不恢复 $\kappa$。两种坐标的“四推一”量词不同。

<a id="section-3"></a>

## 3　何种完整归一化态确实只有三维

<a id="statement-3-1"></a>

#### 定义 3.1（有限复观测代数与信息完备性）

采用有限维复 $C^{\ast}$ 代数的块结构作为前提：

$$
\mathcal B=\bigoplus_{\alpha=1}^{k}M_{d_\alpha}(\mathbb C).
$$

其态由 $\rho_\alpha\ge0$、$\sum_\alpha\operatorname{Tr}\rho_\alpha=1$ 表示。
给定自伴读出 $E_1,E_2,E_3$，若三个期望在全部态域上唯一决定该态，
称它们在此域上信息完备。这里的读出是实线性期望，不是任意集合编码。

<a id="statement-3-2"></a>

<a id="thm:dimension"></a>

#### 定理 3.2（三读出信息完备性的分类）

记 $n=\sum_\alpha d_\alpha^2$。则归一化态空间的仿射维数为 $n-1$，
且给定三读出全域信息完备，当且仅当

$$
\operatorname{span}_{\mathbb R}\{I,E_1,E_2,E_3\}=\mathcal B_{\rm sa}.
$$

因此存在三个全域信息完备的实线性读出，当且仅当 $n\le4$。
若完整态空间恰为三维，则仅有

$$
\boxed{\mathcal B\simeq M_2(\mathbb C)\quad\text{或}\quad\mathcal B\simeq\mathbb C^4.}
$$

**证明。**

$\mathcal B_{\rm sa}$ 的实维数为 $n$，迹一超平面为 $n-1$ 维。
所有块严格正的态 $\rho_{\ast}$ 在该超平面内有相对开邻域，
因为对任意迹零自伴 $H$，充分小的 $\varepsilon$ 使
$\rho_{\ast}\pm\varepsilon H$ 都正。故态空间具有所述仿射维数。
若四个算子的实张成不是全部空间，存在非零自伴 $H$ 与它们正交；
上述两态读出相同而不相等。反之，四个期望相等与张成条件使两态之差为零。
最后 $n=4$ 的正整数平方和只能为 $2^2$ 或四个 $1^2$。

∎

该结论保证合适读出的数学存在性，不保证指定原生菜单能免费取得它们。
在 $n\le4$ 时，任意给定的三条重复或退化读出也不因此自动信息完备。

<a id="statement-3-3"></a>

#### 命题 3.3（经典二元关系的三维四面体）

对两个经典变量 $S,T\in\{-1,1\}$，定义
$a=\mathbb E S,b=\mathbb E T,c=\mathbb E(ST)$。则

$$
p_{st}=\frac{1+sa+tb+stc}{4}\quad(s,t\in\{-1,1\}),
$$

其非负域是顶点 $(s,t,st)$ 的四面体，并且

$$
\boxed{a^2+b^2+c^2=4\sum_{s,t}p_{st}^2-1\in[0,3].}
$$

**证明。**

四个符号函数 $1,s,t,st$ 在四点上正交，故上述 Fourier 反解与平方和恒等式成立。
概率单纯形的四个顶点映成 $(s,t,st)$；平方概率和在 $[1/4,1]$，
分别由均匀律和确定事件达到。

∎

因此，两个经典二元量加其联合关系，确实可用三个数完整表示；
它的极点只有四个，半径平方最大为三。下一节的量子二能级极点是整个球面，
半径平方最大为一。这两种三维几何需要由观测代数来区分。

| 对象 | 完整观测代数 | 归一化态的实维数 |
| --- | --- | --- |
| 经典二结果 | $\mathbb C^2$ | $1$ |
| 两个经典二值量的联合律 | $\mathbb C^4$ | $3$ |
| 一个复二能级态 | $M_2(\mathbb C)$ | $3$ |
| 原五模式占据统计 | $\mathbb C^5$ | $4$ |
| 完整五模式复量子态 | $M_5(\mathbb C)$ | $24$ |
| 两个 qubit 及全部关系 | $M_4(\mathbb C)$ | $15$ |

两个量子概念若实际占据两个 qubit 因子，最新 Pauli 文稿采用

$$
\rho_{AB}=\frac14\left[I+\sum_i a_i\sigma_i\otimes I+
\sum_j b_jI\otimes\sigma_j+\sum_{ij}T_{ij}\sigma_i\otimes\sigma_j\right].
$$

Pauli 迹正交性直接给

$$
\boxed{4\operatorname{Tr}\rho_{AB}^2-1=|a|^2+|b|^2+\|T\|_F^2.}
$$

这保留两个边缘及九个相互关系分量。完整正性仍须对整个矩阵检查；
该平方量的上界本身不替代正性。[[6](#bib-pauli)]

<a id="section-4"></a>

## 4　二元正锥：总量、归一化与纯度

<a id="statement-4-1"></a>

#### 定义 4.1（齐次二元坐标）

对非零正矩阵

$$
M=\begin{pmatrix}p&c\\\bar c&q\end{pmatrix},
\quad s=p+q,\quad
r_{\rm hom}=(2\Re c,-2\Im c,p-q),
$$

采用标准右手 Pauli 矩阵 $\sigma_1,\sigma_2,\sigma_3$，
于是 $M=(sI+r_{\rm hom}\cdot\sigma)/2$。
这里两个分支是基态；三个轴是算符方向，二者不能用同一“正交”概念替换。

<a id="statement-4-2"></a>

<a id="thm:cone"></a>

#### 定理 4.2（正锥截面与二次不变量）

一般 Hermitian $M$ 满足

$$
M\ge0\iff s\ge |r_{\rm hom}|,
\qquad
\boxed{s^2-|r_{\rm hom}|^2=4\det M=4(pq-|c|^2).}
$$

若 $M\ne0$ 且正，则 $s>0$，条件态 $\rho=M/s$ 的 Bloch 向量为
$r=r_{\rm hom}/s$。它满足

$$
\rho=\frac{I+r\cdot\sigma}{2},\qquad |r|\le1,
$$

$$
\boxed{|r|^2=2\operatorname{Tr}\rho^2-1=1-4\det\rho.}
$$

所以 $s=1$ 是归一化截面；$|r|=1$ 是该截面内的纯态边界。

**证明。**

Pauli 乘法给 $(v\cdot\sigma)^2=|v|^2I$，
故 $M$ 的两个特征值为 $(s\pm|r_{\rm hom}|)/2$。
正性与行列式关系随即成立。再用
$\operatorname{Tr}(\sigma_i\sigma_j)=2\delta_{ij}$ 平方取迹，得到纯度式。
迹一正矩阵秩一当且仅当行列式为零，故恰对应单位球面。

∎

上述 Bloch 背景已有于 V24 §3 及标准量子信息材料；本稿的使用是把它与
总质量和观察者参考分开，而非主张新的基础表示定理。[[4](#bib-v24), [8](#bib-ibm)]
球心 $r=0$ 是 $I_2/2$，不是零态；零算子不满足迹一。
归一化混合态也完全合法，故不能把所有合法态都强制放到球面。

<a id="statement-4-3"></a>

#### 命题 4.3（纯态的三实关系坐标）

若 $\psi=\alpha\lvert 0 \rangle +\beta\lvert 1 \rangle$ 且 $|\alpha|^2+|\beta|^2=1$，则

$$
r=(2\Re(\bar\alpha\beta),\,2\Im(\bar\alpha\beta),\,
|\alpha|^2-|\beta|^2),
\qquad |r|^2=1.
$$

三个坐标决定纯态射线，共同相位被消去；一般只知道其中两项，
还需另给剩余分量的符号或其它定向读出。

**证明。**

平方和为
$4|\alpha|^2|\beta|^2+(|\alpha|^2-|\beta|^2)^2=1$。
三数决定 $\psi\psi^\dagger$；相同秩一投影的单位向量只差共同相位。
固定 $r_1,r_2$ 时，纯态条件只给
$r_3=\pm\sqrt{1-r_1^2-r_2^2}$，在内盘有两个分支。

∎

<a id="statement-4-4"></a>

<a id="thm:gramclass"></a>

#### 定理 4.4（归一化 Gram 关系的完整三维表示）

令 $a,b$ 属于同一有限维内部记录空间，且
$\|a\|^2+\|b\|^2=1$。以
$p=\|a\|^2,q=\|b\|^2,c=\langle b,a\rangle$ 定义上面的 $M$。
则 $r$ 完整分类有序对 $(a,b)$ 在记录空间共同酉变换下的等价类。

**证明。**

相同 $M$ 给相同的两范数及复内积，故所有线性组合的范数相同。
于是 $\lambda a+\mu b\mapsto\lambda a'+\mu b'$ 良定义并保内积。
在两张成空间的正交补上补齐正交基，得到同一维记录空间上的酉扩张。
反向由酉保持内积立即成立。

∎

这给出“二元关系的整体信息可三维表示”的另一条精确版本：
完整信息是归一化的二元 Gram 关系，而且取了共同内部酉变换的商。
相对于另外的参考对象、记录标签或未来读口的方向关系，不属于这个商所保留的信息。

<a id="section-5"></a>

## 5　观察者作为原点：中心、尺度与方向标定

<a id="statement-5-1"></a>

#### 定义 5.1（一般三读出框架）

给二能级自伴读出
$E_i=a_iI+b_i\cdot\sigma$，令 $B$ 的第 $i$ 行为 $b_i^\mathsf T$，
并假设 $B$ 可逆。定义 $H=BB^\mathsf T>0$，
以及实际期望 $m_i=\operatorname{Tr}(\rho E_i)$。

<a id="statement-5-2"></a>

<a id="thm:metric"></a>

#### 定理 5.2（有中心、有度量的平方和）

上述读出满足

$$
m-a=Br,\qquad
\boxed{|r|^2=(m-a)^\mathsf TH^{-1}(m-a).}
$$

因此可行域是相应椭球，纯度由此二次式给出。
若用观察者参考态 $\rho_O=(I+r_O\cdot\sigma)/2$ 的读数作为原点，
令 $d=m-m_O$，则

$$
\boxed{|r|^2=(d+Br_O)^\mathsf TH^{-1}(d+Br_O).}
$$

而

$$
d^\mathsf TH^{-1}d=|r-r_O|^2
=2\operatorname{Tr}(\rho-\rho_O)^2
$$

描述相对参考态的距离。

**证明。**

Pauli 迹正交性给 $m_i=a_i+b_i\cdot r$。
由 $B$ 可逆，$r=B^{-1}(m-a)$，
且 $(B^{-1})^\mathsf TB^{-1}=(BB^\mathsf T)^{-1}$。
代入 $d=B(r-r_O)$ 即得全部公式。

∎

直接以未加权、未平移的三个读数平方和表示纯度，要求中心与轴尺都已正确标定。
在标准 Pauli 框架中，若观察者参考态为 $\lvert 0 \rangle \langle 0 \rvert$，
则完全混合态 $I/2$ 的相对坐标是 $(0,0,-1)$；
这个相对平方和虽为一，被观察态的纯度仍是 $1/2$。
把一个有确定方向的参考纯态放到坐标原点，需要平移球面。

<a id="statement-5-3"></a>

#### 命题 5.3（各向同性中心及参考态的剩余相位）

二能级态中，唯一在全部酉共轭下不变的态是 $I/2$。
一个参考纯态只能选定一条 Bloch 轴；它不能单独确定完整横向相位框架。

**证明。**

若 $\rho_O$ 在全部酉共轭下不变，则其 Bloch 向量在全部旋转下不变，故为零。
也可由与全部矩阵对易推出 $\rho_O$ 为标量，再由迹一得到 $I/2$。
对单位方向 $n$，$e^{-i\theta n\cdot\sigma/2}$ 保持对应纯态射线，
却转动垂直于 $n$ 的两个方向，所以还需横向标定。

∎

固定参考基 $\lvert 0 \rangle ,\lvert 1 \rangle$，在 $\langle0|\psi\rangle\ne0$ 的局部图中，
纯态可写为

$$
\psi=\frac{\lvert 0 \rangle +w\lvert 1 \rangle }{\sqrt{1+|w|^2}},\qquad
r=\frac{(2\Re w,\,2\Im w,\,1-|w|^2)}{1+|w|^2}.
$$

参考态与正交伙伴选择坐标图，复数 $w$ 编码相对关系，
分母承担归一化。与参考态正交的点须换图。
这是一种可供 $F[\mathrm{null}]$ 使用的参考角色；原事件语义与该另加字典应分别保留。

<a id="section-6"></a>

## 6　平方半径与内部关系：精确预算

<a id="statement-6-1"></a>

<a id="thm:record"></a>

#### 定理 6.1（内部记录的 Gram 预算）

设整体内部纯态为

$$
\Psi=\lvert 0 \rangle \otimes a+\lvert 1 \rangle \otimes b,\qquad
p=\|a\|^2,\quad q=\|b\|^2,\quad c=\langle b,a\rangle,\quad p+q=1.
$$

约化二能级态为 $M$。定义分支不平衡 $P=|p-q|$、
相干幅度 $V=2|c|$ 及 Gram 余量
$\mathcal G=2\sqrt{pq-|c|^2}$。则

$$
\boxed{P^2+V^2+\mathcal G^2=1,\qquad |r|^2+\mathcal G^2=1.}
$$

$\mathcal G=0$ 当且仅当 $a,b$ 线性相关，包括一个为零；
亦即该整体纯态在所选内部划分上为乘积态。

**证明。**

部分迹给 $\rho=\left(\begin{smallmatrix}p&c\\\bar c&q\end{smallmatrix}\right)$。
非负性由 Cauchy–Schwarz，且
$(p-q)^2+4|c|^2+4(pq-|c|^2)=(p+q)^2=1$。
等号分类是 Cauchy–Schwarz 的等号条件，亦等价于该二元系数矩阵的秩为一。

∎

若 $p,q>0$，写 $\eta=c/\sqrt{pq}$，则

$$
|r|^2=P^2+(1-P^2)|\eta|^2.
$$

归一化决定 $p+q$；相对记录的内积决定半径如何下降。
此关系全发生在同一整体内部，不要求外部环境。
但没有纯整体及指定内部划分时，半径缺口只能直接表述局部混合度：
$I/2$ 既可为 Bell 纯态的一侧，也可为
$(I/2)\otimes\lvert 0 \rangle \langle 0 \rvert$ 的一侧，纠缠结论不同。

<a id="statement-6-2"></a>

#### 命题 6.2（总不确定性与记录可区分度）

上述二能级态满足

$$
\sum_{i=1}^3\operatorname{Var}_\rho(\sigma_i)=3-|r|^2
=2+\mathcal G^2.
$$

另令 $D=\|\lvert a \rangle \langle a \rvert -\lvert b \rangle \langle b \rvert \|_1$，则

$$
D^2+V^2=1,\qquad D^2=P^2+\mathcal G^2.
$$

**证明。**

$\sigma_i^2=I$，故各方差为 $1-r_i^2$。
差算子支撑于 $\operatorname{span}\{a,b\}$；在至多二维支撑中补零后的两个特征值为

$$
\frac{p-q\pm\sqrt{(p+q)^2-4|c|^2}}2.
$$

它们异号或有一个为零，故迹范数为 $\sqrt{1-4|c|^2}$。
零支撑方向不改变迹范数，所列恒等式随即成立。

∎

这里 $D$ 是带先验的记录区分量，$P$ 只是概率不平衡，不能混同。
全部这些是给定复 Hilbert、约化态及概率接口后的结论，不从归一化单独起源 Born 规则。

<a id="section-7"></a>

## 7　原五模式真正的二次量

<a id="statement-7-1"></a>

<a id="prop:occupancy"></a>

#### 命题 7.1（占位半径与总方差）

令 $R^2=X^2+Y^2+Z^2$。固定 $Z\in[0,1]$，

$$
Z^2\le R^2\le Z^2+2(1-Z)^2,
$$

所有中间值可取；全域 $0\le R^2\le2$。
另有

$$
\mathbb E(\xi^2+\eta^2+\zeta^2)=X+Y+Z=1-p_N+p_{13},
$$

$$
\mathbb E(\xi^2+\eta^2+\zeta^2)-R^2
=X(1-X)+Y(1-Y)+Z(1-Z).
$$

**证明。**

由定理 [2.4](#thm:fiber)，$0\le X,Y\le1-Z$。
取 $X=Y=t(1-Z)$、$0\le t\le1$，即可连续取得所列区间。
全域最大二在 $(1,1,0)$，最小零在原点。
占位函数幂等，故二阶矩的迹为三个均值之和；相减即为总方差。

∎

五维最大混合态给 $(X,Y,Z)=(2/5,2/5,1/5)$，其 $R^2=9/25$，
不位于空窗原点。强行把非零三轴向量除以其欧氏长度会再丢信息：
$p_N=1-a,p_1=a$ 对所有 $a>0$ 都变成方向 $(1,0,0)$，
原事件质量却不同，$a=0$ 时该方向甚至未定义。

<a id="statement-7-2"></a>

<a id="thm:fivepurity"></a>

#### 定理 7.2（五模式的完整纯度二次预算）

令

$$
q=(X,Y,Z,\kappa)^\mathsf T,\quad
q_{\ast}=(2/5,2/5,1/5,1/5)^\mathsf T,\quad \delta q=q-q_{\ast},
$$

并定义

$$
H_5=
\begin{pmatrix}
2&1&1&-2\\
1&2&1&-2\\
1&1&2&-1\\
-2&-2&-1&4
\end{pmatrix}.
$$

则 $H_5>0$，任意归一化五模式概率满足

$$
\sum_s p_s^2=\frac15+\delta q^\mathsf T H_5\delta q.
$$

对完整五维量子态 $\rho$，在同一模式基中进一步有

$$
\boxed{
\operatorname{Tr}\rho^2
=\frac15+\delta q^\mathsf T H_5\delta q
+2\sum_{s<t}|\rho_{st}|^2.
}
$$

故纯五维态满足
$\delta q^\mathsf T H_5\delta q+2\sum_{s<t}|\rho_{st}|^2=4/5$。

**证明。**

由概率反解，

$$
p-\tfrac15\mathbf1=A\delta q,\qquad
A=\begin{pmatrix}
-1&-1&-1&1\\
1&0&0&-1\\
0&0&1&0\\
0&1&0&-1\\
0&0&0&1
\end{pmatrix}.
$$

直接按列配对得 $A^\mathsf TA=H_5$。列满秩：由最后、第三、第二、第四行
依次恢复 $\delta\kappa,\delta Z,\delta X,\delta Y$，故 $H_5>0$。
又有 $\mathbf1^\mathsf TA=0$，平方展开得到第一式。
Hermitian 矩阵恒等式
$\operatorname{Tr}\rho^2=\sum_s\rho_{ss}^2+2\sum_{s<t}|\rho_{st}|^2$
给第二式。

∎

这个等式把四个对角关系坐标与相干预算一起保留。
它不声称只满足该标量预算就足以保证矩阵正性。
相同三轴可以给不同纯度：在 $(X,Y,Z)=(1/2,1/2,0)$ 处，

$$
p_A=(1/2,0,0,0,1/2),\quad
p_B=(1/4,1/4,0,1/4,1/4)
$$

的对角纯度分别为 $1/2,1/4$，而三轴半径同为 $1/2$。
甚至 $\psi=(\lvert N \rangle +\lvert 13 \rangle )/\sqrt2$ 与 $\operatorname{diag}p_A$
有相同全部五占据概率，量子纯度却分别为一与 $1/2$。
因此原生 $F[13]$ 的联合概率与二能级复相干项不是同一对象。

<a id="section-8"></a>

## 8　最新原生块代数：归一化不消除中心权重

续卷 III §151.2 对其固定记录后接口证明，实际未来效果的实张成
分别是下列块代数的自伴部分 $\operatorname{Herm}(\mathcal A_i)$：

$$
\mathcal A_0\simeq M_{21}\oplus M_{21}\oplus M_{13},\qquad
\mathcal A_1\simeq M_{21}\oplus M_{13}.
$$

同型块的控制同步；旧完整标签仍能把效果支撑限定到一个块。
该结论是指定实际菜单的张成结论，不等于任意控制已经取得。[[5](#bib-iii)]

<a id="statement-8-1"></a>

<a id="thm:block"></a>

#### 定理 8.1（块质量与块纯度分解）

采用规范载体 $\mathcal H=\bigoplus_s\mathbb C^{d_s}$ 及其块代数
$\bigoplus_sM_{d_s}(\mathbb C)$，矩阵迹也取此规范表示。
每个归一化态唯一写为

$$
\bar\rho=\bigoplus_s t_s\rho_s,\qquad
t_s\ge0,\quad\sum_s t_s=1,\quad \operatorname{Tr}\rho_s=1\ (t_s>0).
$$

零质量块不定义 $\rho_s$。并且

$$
\boxed{\operatorname{Tr}\bar\rho^2=\sum_{s:t_s>0}t_s^2\operatorname{Tr}\rho_s^2.}
$$

若 $\bar\rho=\sum_sP_s\lvert u \rangle \langle u \rvert P_s$ 来自单位纯态的块压缩，
则每个非零块纯，故 $\operatorname{Tr}\bar\rho^2=\sum_st_s^2$。
该块代数上的态为极点，当且仅当恰占据一个块且该块态纯。

**证明。**

逐块取迹得唯一的 $t_s$；正质量时相除给 $\rho_s$。
不同块相乘为零，平方取迹即得预算。
纯态块压缩为 $\lvert P_su \rangle \langle P_su \rvert$，正质量时秩一。
若占据两个块，可按块质量作非平凡凸分解；若一个块内混合，也能谱分解。
反之，单块秩一投影的正凸分解必须都支撑于该一维像，
再由迹一使各项等于它自身，故为极点。

∎

在最新来源的额外正条件表示合同下，令
$S(u)=\{s:t_s=\|P_su\|^2>0\}$，
$\widehat u_s=P_su/\sqrt{t_s}$（仅对 $s\in S(u)$ 定义）。
后验态在其余块为零，且恰有

$$
\begin{gathered}
\sigma_z=\bigoplus_{s\in S(u)}\beta_s(z)
\lvert \widehat u_s \rangle \langle \widehat u_s \rvert ,\qquad \beta_s(z)\ge0,\\
\sum_{s\in S(u)}\beta_s(z)=1,\qquad
\int\beta_s(z)d\nu(z)=t_s\quad(s\in S(u)).
\end{gathered}
$$

将 $s\notin S(u)$ 的 $\beta_s$ 置零，以上均在来源给出的共同满测集上成立。
这里 $\beta_s(z)=\ell_z(P_s)$ 是中心权重；
归一化是 $\ell_z(I)=1$，不是某个指定块的权重。
来源证明完整条件未来相等恰等价于 $\beta_s=t_s$ 几乎处处，
并用实际前缀给出纯全载体态的非极端 Born 比较行。[[5](#bib-iii)]
这依赖真实共同档案切口、全块正锥上的正线性表示和粗 Born 行三个独立前件。
这些前件未由归一化或全局纯度自动取得。

<a id="section-9"></a>

## 9　内部条件归一化：质量、误差与递归

<a id="statement-9-1"></a>

#### 定义 9.1（内部角接口与结果分支）

设内部投影 $E$ 给出角代数 $E\mathcal A E$，其单位元是 $E$。
限制泛函的质量为 $s_E=\omega(E)$。若 $s_E>0$，定义

$$
\omega_E(A)=\omega(A)/s_E,\qquad A\in E\mathcal A E.
$$

更一般，若内部结果算子 $K$ 满足 $K^\dagger K\le I$，且
$s_K=\omega(K^\dagger K)>0$，定义

$$
\omega_K(A)=\frac{\omega(K^\dagger AK)}{s_K}.
$$

两者正且在其单位元上取值一。零质量分支不作除法。
当 $E=I$ 时角质量必为一；反向不成立，因为状态可以完全支撑于真子空间。

因此在固定的二能级条件接口中，完整密度数据是“分支质量 $s$ 加条件三轴 $r$”。
把 $M$ 换为 $M/s$ 只保留其正比例射线，不能恢复 $s$；
遗漏的质量仍须在其它内部结果中计入。
最新原生二维块先记 $m$ 再归一化的做法，正是这个接口。[[5](#bib-iii)]

<a id="statement-9-2"></a>

<a id="thm:normerror"></a>

#### 定理 9.2（归一化的稳定性边界）

若 $M,N\ge0$，$s=\operatorname{Tr} M>0,t=\operatorname{Tr} N>0$，令 $\delta=\|M-N\|_1$，
则

$$
\boxed{
\left\|\frac Ms-\frac Nt\right\|_1
\le\frac{\delta+|s-t|}{\max(s,t)}
\le\frac{2\delta}{\max(s,t)}.
}
$$

若分支质量统一至少为 $s_{\ast}>0$，便有上界 $2\delta/s_{\ast}$。
在质量趋零的全域没有统一有限 Lipschitz 常数。

**证明。**

写
$M/s-N/t=(M-N)/s+N(1/s-1/t)$，
得 $(\delta+|s-t|)/s$；交换两者得分母 $t$，取较小上界。
迹范数对偶给 $|s-t|\le\delta$。
取 $M_\eta=\eta\lvert 0 \rangle \langle 0 \rvert ,N_\eta=\eta\lvert 1 \rangle \langle 1 \rvert$，
输入距离为 $2\eta$，归一化后距离恒为二，证明无全域常数。
第一界可由 $M=s\lvert 0 \rangle \langle 0 \rvert$、$N=M+\delta\lvert 1 \rangle \langle 1 \rvert$ 达到。

∎

<a id="statement-9-3"></a>

<a id="thm:filter"></a>

#### 定理 9.3（单分支递归的行列式乘法律）

设二能级单分支矩阵 $K_j$ 给正质量更新

$$
t_j=\operatorname{Tr}(K_j\rho_{j-1}K_j^\dagger)>0,\qquad
\rho_j=K_j\rho_{j-1}K_j^\dagger/t_j.
$$

则

$$
\boxed{
1-|r_n|^2
=(1-|r_0|^2)
\frac{\prod_{j=1}^{n}|\det K_j|^2}
{\left(\prod_{j=1}^{n}t_j\right)^2}.
}
$$

未归一化字 $W_n=K_n\cdots K_1$ 的总分支质量为
$s_n=\operatorname{Tr}(W_n\rho_0W_n^\dagger)=\prod_jt_j$。
实际仪器解释另需各结果及失败质量的完整合同；此式不安装新的原生控制。

**证明。**

二阶行列式给
$\det\rho_j=|\det K_j|^2\det\rho_{j-1}/t_j^2$。
逐步相乘并用 $1-|r_j|^2=4\det\rho_j$。
未归一化矩阵满足
$W_j\rho_0W_j^\dagger=(\prod_{\ell\le j}t_\ell)\rho_j$，
归纳及取迹给总质量式。

∎

这是一种明确的递归关系：总量因子与条件纯度因子共同传播。
只保存球面或球内位置，会丢掉决定条件选择成本的乘积质量。

<a id="statement-9-4"></a>

#### 命题 9.4（输入无关质量与酉条件更新）

若可逆二阶矩阵 $K$ 的 $t(\rho)=\operatorname{Tr}(K\rho K^\dagger)$
对全部归一化态恒为 $c$，则且仅则
$K^\dagger K=cI$。此时 $c>0$，$K=\sqrt c\,U$，
条件更新正是 $\rho\mapsto U\rho U^\dagger$。

**证明。**

将定理 [2.2](#thm:unit) 后的全域单位判据用于 $K^\dagger K/c$；
也可直接对全部纯态检查二次型。极分解或
$U=K/\sqrt c$ 给酉性。反向直接取迹。

∎

例如 $K=\operatorname{diag}(1,\varepsilon)$、$0<\varepsilon<1$，
把每个纯态仍送到纯态，因此每个条件输出仍满足 $|r'|=1$；
但 $t(\rho)$ 依赖输入。正交态 $\lvert \pm \rangle$ 的条件输出内积为
$(1-\varepsilon^2)/(1+\varepsilon^2)\ne0$。
所以只观察纯态球面半径不变，不足以证明同一个过程酉。

<a id="section-10"></a>

## 10　何时三轴平方和真正给出酉性

<a id="statement-10-1"></a>

<a id="thm:unitary"></a>

#### 定理 10.1（全态半径守恒的 CPTP 判据）

设 $\Phi$ 是同一二能级载体上的 CPTP 映射。若对全部密度态有

$$
|r(\Phi(\rho))|^2=|r(\rho)|^2,
$$

则 $\Phi(\rho)=U\rho U^\dagger$ 为酉通道。反向显然成立。

**证明。**

迹保持与 Hermitian 保持给实仿射形式 $r\mapsto Tr+t$。
取 $r=0$ 得 $t=0$。对球内全部 $r$ 有 $|Tr|^2=|r|^2$，
由二次型极化得 $T^\mathsf TT=I$。
若 $\det T=1$，每个三维正交正向旋转可写成轴角形式；
Pauli 乘法直接验证
$U=\cos(\theta/2)I-i\sin(\theta/2)n\cdot\sigma$
实现相应旋转，故得到酉通道。
若 $\det T=-1$，令 $J=\operatorname{diag}(1,-1,1)$。
$TJ$ 为正向旋转，而 $J$ 对应矩阵转置；于是 $\Phi$ 为某酉共轭复合转置。
但转置非完全正：Bell 投影
$\lvert \Phi^+ \rangle \langle \Phi^+ \rvert$ 在一侧转置后是交换算子的一半，
在反对称向量 $(\lvert 01 \rangle -\lvert 10 \rangle )/\sqrt2$ 上有特征值 $-1/2$。
酉共轭不能消除该负特征值，矛盾。

∎

定理要求同一个全态 CPTP 过程、同一载体和完整半径守恒。
单条轨迹、只检查纯态输出，或对每个输入另行挑选映射，都不满足此前提。
例如固定纯态重置通道将全部纯态仍送到球面，却不保持球心半径。

<a id="statement-10-2"></a>

#### 命题 10.2（可操作的二能级误差界）

对两态 $\rho,\sigma$ 的 Bloch 向量 $r,u$，

$$
\|\rho-\sigma\|_1=|r-u|,\qquad
|\operatorname{Tr}\rho^2-\operatorname{Tr}\sigma^2|\le |r-u|.
$$

若同一个酉作用于两态，则三轴误差欧氏范数精确保持。

**证明。**

差矩阵为 $(r-u)\cdot\sigma/2$，特征值为 $\pm|r-u|/2$。
纯度差的绝对值是
$\tfrac12\big||r|^2-|u|^2\big|\le \tfrac12(|r|+|u|)|r-u|\le|r-u|$。
酉共轭对应正交旋转，保持差向量范数。

∎

最新活动黄金块取 $x=\varphi^{-1}$、$y=\sqrt x$，

$$
Q=\begin{pmatrix}x&xy\\xy&x^2\end{pmatrix}
=\frac{I+n\cdot\sigma}{2},\qquad
n=(2xy,0,x-x^2),\quad |n|^2=1,
$$

并有 $B=\zeta_0[I+(\zeta_0-1)Q]$、
$\zeta_0=e^{3\pi i/5}$。
在已经闭合的该块内，$B$ 酉，保留块质量、条件 Bloch 半径及两态误差距离。
原全载体门含其它块和记录；换地址后是否继续停留在同一二能级接口，
仍须检查不变性，不能由单块公式自动推出。[[5](#bib-iii), [7](#bib-golden)]

若按 v40 的固定可见投影 $P$ 压缩全载体演化，
省略关系的返回仍由记忆核 $BD_0^kC$ 控制。
本稿新增的结论是：即使每步压缩后都能重归一化，
还须保留分支质量、观测中心、读出度量及相干关系；
归一化截面本身不能替代闭合性或全态过程的酉性。

<a id="section-11"></a>

## 11　可复用的精确表述

在原生五模式语义下，适宜保留以下字典：

$$
\begin{array}{c|l}
F[\mathrm{null}]&\text{特定空模式，或另供几何中的参考锚点}\\
1_{\mathcal B}\ \text{或}\ I&\text{全部事件的归一化单位}\\
\omega|_{\mathcal B}\ \text{或}\ \rho&\text{观察接口上的状态}\\
\omega(1)=1\ \text{或}\ \operatorname{Tr}\rho=1&\text{归一化条件}\\
|r|^2&\text{已标定二能级接口的纯度坐标}\\
\kappa,\ \rho_{st},\ t_s&\text{依接口分别保留的联合、相干和块质量关系}
\end{array}
$$

因此，二元结构可有严格的三维完整表示：
它可以是单个 $M_2$ 态、两个经典二值量的联合律，
或共同酉等价下的归一化 Gram 关系。
原五模式的完整占据律则由 $(X,Y,Z,\kappa)$ 给出；
它的纯度二次式为定理 [7.2](#thm:fivepurity)，
完整量子表示还须保留相干项。
观察者作为参考态并不删除归一化；它选择参考原点，
球体中心与读出度量仍须保留和标定，而单位元上的取值一始终规定总概率。

## 固定来源与使用范围

<a id="bib-head"></a>

**[1]**　
[trureturing，本轮固定提交](https://github.com/the-omega-institute/trureturing/commit/79783aa49bcdbb3e7def349937515a7e9e7b4b76)。全部项目链接固定于此版本。

<a id="bib-main"></a>

**[2]**　
[AURIC FIB ATOM 与量子基本原则：相干递归的条件综合](https://github.com/the-omega-institute/trureturing/blob/79783aa49bcdbb3e7def349937515a7e9e7b4b76/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md)，
定义 1.1–1.2、命题 1.4、定理 2.1、2.3。

<a id="bib-pyramid"></a>

**[3]**　
[FIB-ATOM 金字塔：基础公式、原子关系与同源接续总表](https://github.com/the-omega-institute/trureturing/blob/79783aa49bcdbb3e7def349937515a7e9e7b4b76/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)，§§2–4。

<a id="bib-v24"></a>

**[4]**　
[AURIC 两基态与三通道：归一化、相位手性及递归平方律](https://github.com/the-omega-institute/trureturing/blob/79783aa49bcdbb3e7def349937515a7e9e7b4b76/docs/develop/theory/AURIC_TWO_BASIS_STATES_THREE_CHANNELS_PHASE_CHIRALITY_AND_RECURSIVE_SQUARE_LAW_V24.md)，§§2–3。

<a id="bib-iii"></a>

**[5]**　
[AURIC：原生统计守恒、读器插入与全历史记录概率](https://github.com/the-omega-institute/trureturing/blob/79783aa49bcdbb3e7def349937515a7e9e7b4b76/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md)，
§146 活动二维块及 §151 块观测代数。实际条件表示前件见本稿 §8。

<a id="bib-pauli"></a>

**[6]**　
[Pauli-channel entropy geometry](https://github.com/the-omega-institute/trureturing/blob/79783aa49bcdbb3e7def349937515a7e9e7b4b76/docs/develop/theory/PAULI_CHANNEL_ENTROPY_GEOMETRY.md)，定义 1.1、式 (1.3)。
仅使用完整两 qubit 态域与坐标定义。

<a id="bib-golden"></a>

**[7]**　
[AURIC 固定黄金门与 braid 相容性](https://github.com/the-omega-institute/trureturing/blob/79783aa49bcdbb3e7def349937515a7e9e7b4b76/docs/develop/theory/AURIC_FIXED_GOLDEN_GATE_AND_BRAID_COMPATIBILITY_ZH.md)，精确投影谱形式及酉性。

<a id="bib-ibm"></a>

**[8]**　
[IBM Quantum Learning，Bloch sphere](https://quantum.cloud.ibm.com/learning/en/courses/general-formulation-of-quantum-information/density-matrices/bloch-sphere)，标准 Pauli 与纯态球面背景。
