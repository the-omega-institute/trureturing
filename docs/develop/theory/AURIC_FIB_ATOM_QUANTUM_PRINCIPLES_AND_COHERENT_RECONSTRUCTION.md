# AURIC FIB ATOM 与量子基本原则：相干递归的条件综合

五模式金字塔指定一个关系单元。在它上面另供定向 Clifford 复合、指定复角、相干矩阵单位运输、全效果相融、参考系统一致性和递归交叉核守恒，可以建立有限维复量子操作模型。下文保留这些条件的全部量词，给出其在同一个五模式表示中的普通数学证明与反模型。

局部三轴的二维旋量块、五维系统代数和增长的完整记录载体分别定型。几何正交、结果互斥和操作反交换是不同条件；Hodge 压缩需要酉补足；原等待菜单、独立翻转、连续相位和固定相位扩展具有不同的控制范围。代数存在、合法操作、有效取得、精度与成本分别承担自己的条件。

函数代数、Clifford–Pauli 对应、矩阵单位、效果表示、核商、Choi–Kraus 表示、控制群和量子基本后果均采用已归属的数学工具。这里的消费者是从指定局部复角到五事件代数、再到共同相干记录模型的条件接合，不提出新的基础表示定理或经验性实现主张。具体来源与使用范围列于第 13 节。

## 1. 问题的精确定型：原子、表示与门

本篇研究如下关系问题：

> 一个内部保留观察者、已读结果及待完成关系的递归单元，是否能使量子规则成为继续预测必须遵守的相容性条件？

这个方向有可证明的内容。所需工作是明确“什么对象相融、在哪个操作域中相融”，
并检查相融条件究竟约束数值权重、相干关系、实际后态，还是所有复合系统。

**定义 1.1（原生五模式）。**
取三位置路径图 $1\!-\!2\!-\!3$，合法集合为其独立集：

$$
\Sigma=\{\varnothing,\{1\},\{2\},\{3\},\{1,3\}\}
       =\{0,1,2,3,13\}.
$$

逻辑位置与项目的数值标签按下表对应。

| 逻辑模式 | 三位占据 | 项目标签 |
| --- | --- | --- |
| $0$ | $000$ | $F[\mathrm{null}]$／$N$ |
| $1$ | $100$ | $F[1]=[2]$ |
| $2$ | $010$ | $F[2]=[3]$ |
| $3$ | $001$ | $F[3]=[5]$ |
| $13$ | $101$ | $F[1,3]=[2,5]$ |

数值标签不指定长度、概率或门角度。
令 $x,z,y$ 分别为位置 $1,2,3$ 的占位函数；
本文代数坐标写为 $(x,y,z)$，三位串仍按 $(x,z,y)$ 排列。

**定义 1.2（三种层次）。**
*关系原子*是合法模式及其约束。
*量子表示*还给出相干载体、效果及复合规则。
*量子门或仪器*另需指定共同输入、输出及实际允许的变换：
闭合可逆门为 $U^\dagger U=UU^\dagger=I$ 的算子；
一般测量为带输出标签的完全正分支。
一张有限图可以索引这些对象，但图形本身没有指定其矩阵元。

在已有量子表示中，$|0\rangle$ 是范数一的模式向量。
它不同于向量零、空历史、欧氏原点和停止符。
在具体几何标定里可将 $j(0)$ 放在锚点 $o$，这没有把 $|0\rangle$ 变成零向量。
这些类型区别见 [static](#ref-static)、[seams](#ref-seams)、[memory](#ref-memory)。

<a id="thm:underdetermination"></a>

**定理 1.3（裸结构的非唯一完成）。**
五个合法模式、递归更新、非负记录权重、静态历史图及观察者内生，
并不唯一决定复量子理论。
即使再要求平方型权重、连续可逆变换和非交换操作，仍不能仅凭这些选择复数域。

证明。
第一种模型取状态单纯形
$\Delta_4=\{p_s\ge0:\sum_sp_s=1\}$，
效果 $e\in[0,1]^5$，概率 $e\cdot p$，更新为列随机矩阵。
把观察者的程序和记录并入经典状态，便有内生递归；
所有有限历史构成一张静态有向无环图。
同一五标签和几何位置字典均可使用，而模型没有相位。

第二种取实五维 Hilbert 空间、实对称正半定迹一状态、
实对称效果和正交变换。它具有实叠加、模平方、连续旋转及不交换投影，
却仍不是完整的复五维量子模型。
两例都保留所列结构，故相应条件不蕴含所声称的唯一选择。
证毕。

这条定理的用途是定位一个必须回答的问题：
*新增哪条可检验的关系原则，才能排除这些完成？*
它不否定金字塔作为有效量子单元的价值。
在已知操作重建理论中，确实需要跨系统的额外原则；
Hardy 和 CDP 的代表性路线见 [hardy](#ref-hardy)、[cdp](#ref-cdp)。

**命题 1.4（相同标签数不决定状态维数）。**
五模式的经典状态、实量子状态、复量子状态的归一化实维数分别为

$$
4,\qquad 14,\qquad 24.
$$

复五维纯态射线的实维数为八。

证明。
概率有五项、一个归一化约束。
实对称矩阵有 $5\cdot6/2$ 个实参数，Hermitian 矩阵有 $5^2$ 个，
各减一个迹约束；正定态提供这些仿射空间中的开集。
复单位向量有十个实坐标，减一个范数和一个整体相位，得八。
证毕。

因此“稳定地看见三个坐标”首先描述一个读出摘要，
不能据此把整个量子态认作三个实数。
具体哪部分隐藏，要由允许的后继实验决定。

## 2. 五模式自身给出的关系代数

<a id="thm:function"></a>

**定理 2.1（唯一四角关系系数）。**
全部实读出函数构成

$$
\mathbb R^\Sigma\cong
\mathbb R[x,y,z]/(x^2-x,y^2-y,z^2-z,xz,yz).
$$

任意 $f:\Sigma\to\mathbb R$ 唯一展开为

$$
\boxed{
f=f_0+(f_1-f_0)x+(f_3-f_0)y+(f_2-f_0)z+J_fxy,
\quad
J_f=f_{13}-f_1-f_3+f_0.}
$$

特别地，$f_2-f_0$ 与 $J_f$ 是独立参数。

证明。
幂等关系把单项式化为平方自由形式，排斥关系消去所有含 $xz$ 或 $yz$ 的项，
故只剩 $1,x,y,z,xy$。
在 $0,1,3,2,13$ 上依次代入，唯一解出显示的五个系数。
五个基函数因而线性无关，商代数的评价映射为同构。
证毕。

这是项目关系丛卷 §§3、16 的有限函数代数在三位置上的形式 [bundle](#ref-bundle)。
它精确说明：顶端 $F[2]$ 能约束端点操作的想法，
需要一条把 $f_2-f_0$ 与 $J_f$ 联系起来的额外规则。
五模式排斥语法本身没有这条关系。

**例 2.2（加法与其他联合读出）。**
固定 $f_0=0,f_1=2,f_2=3,f_3=5$。
此时所有剩余读出由一个实数 $c=f_{13}$ 参数化，且 $J_f=c-7$。
$c=7$ 给零四角缺陷，$c=10$ 给缺陷三。
后者在联合模式上返回通常乘积的数值，但这些五个取值尚未定义
任意实输入上的二元运算。
若把空集的乘法值另定为一，四角缺陷也随之改变；
所以空模式和运算标定必须同时说明。

<a id="thm:fiber"></a>

**定理 2.3（稳定三均值的精确遗漏）。**
设五项概率为 $p$，令

$$
X=p_1+p_{13},\qquad Y=p_3+p_{13},\qquad Z=p_2,\qquad \kappa=p_{13}.
$$

给定 $X,Y,Z$ 的全部来源恰为

$$
p_\kappa=(1-X-Y-Z+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
$$

其中

$$
\max(0,X+Y+Z-1)\le\kappa\le\min(X,Y).
$$

其均值像为凸金字塔

$$
X,Y,Z\ge0,\qquad X+Z\le1,\quad Y+Z\le1.
$$

任意读出的期望为

$$
\mathbb E_pf=f_0+(f_1-f_0)X+(f_3-f_0)Y+(f_2-f_0)Z+J_f\kappa.
$$

故在区间非退化时，$f$ 的期望由三均值确定，当且仅当 $J_f=0$。

证明。
以 $\kappa=p_{13}$ 反解其他四项即得公式，逐项非负给区间。
区间非空恰等价于显示的金字塔不等式。
将定理 [2.1](#thm:function) 取期望得到末式，随后结论是仿射函数在非退化区间上常值的判据。
证毕。

这一遗漏已经存在于经典概率中。
固定三个单模式概率 $p_1,p_2,p_3$ 与固定三个占位均值 $X,Y,Z$ 也不同：
前者使 $p_0+p_{13}$ 固定；
后者的盲方向为

$$
(1,-1,0,-1,1),
$$

所以 $p_0,p_{13}$ 同向变化。
关于“稳定三点、隐藏两个点”的论证须先选定实际读口。

**命题 2.4（推广到有限约束图）。**
对有限简单图 $G$ 的合法独立集族 $\Sigma_G$，置
$x_A(S)=\mathbf1_{A\subseteq S}$。
则合法 $A$ 对应的 $x_A$ 构成全部函数的基，且

$$
f(S)=\sum_{A\subseteq S}c_A(f),\qquad
c_A(f)=\sum_{B\subseteq A}(-1)^{|A|-|B|}f(B).
$$

乘法满足 $x_Ax_B=x_{A\cup B}$（联合合法时），否则为零。

证明。
按集合大小排列，评价矩阵为对角全一的三角矩阵。
逆变换由
$\sum_{B\subseteq C\subseteq A}(-1)^{|A|-|C|}
=(1-1)^{|A\setminus B|}$
验证；独立集的每个子集仍合法，所以这些区间求和没有缺项。
乘法直接比较两个指示条件。
证毕。

这使五模式成为一类关系系数系统中的最小实例之一，
而不是仅凭五这个数字宣称它是所有可能物理系统的唯一原子。

## 3. 几何关系何时成为一个门

**定义 3.1（共同几何标定）。**
另给定向欧氏三维空间、锚点 $o$、独立位移 $a,b$ 和高度 $h>0$。
正交化后记有向单位标架为 $(u,v,n)$，$n=u\times v$。
使用位置字典

$$
j(0)=o,\quad j(1)=o+a,\quad j(3)=o+b,\quad
j(2)=o+hn,\quad j(13)=o+a+b.
$$

面积关系为 $B_{13}=a\wedge b$。

**命题 3.2（法向、平面与点的不同确定性）。**
上述数据确定底平面及有向单位法向。
单给底平面与法向轴，并不确定联合点 $o+a+b$。
两个不同相交平面在三维通常确定一条直线；
确定这条线上的一点还需附加标定。

证明。
底平面是 $o+\operatorname{span}_{\mathbb R}(a,b)$。
所有包含法向轴的平面可写为

$$
o+\operatorname{span}_{\mathbb R}\bigl(n,\lambda a+\mu b\bigr),
\quad [\lambda:\mu]\in\mathbb{RP}^1.
$$

其与底面的交线为 $o+\mathbb R(\lambda a+\mu b)$。
先选 $[\lambda:\mu]=[1:1]$ 才取得对角方向，再选系数一才取得联合点。
另一方面，以 $n$ 为法向、过 $o+hn$ 的平面与底面平行，$h>0$ 时不相交。
证毕。

若 $a,b$ 是单位正交向量，旋转它们可以保持 $a\wedge b$，
却改变 $a+b$。面积关系可以锁定而对角点仍变化。
接缝卷 §§31–32 给出了上述类型区分 [seams](#ref-seams)。

<a id="thm:hodge"></a>

**定理 3.3（Hodge 压缩的缺口与酉补足）。**
给外代数的标准内积和由 $(u,v,n)$ 决定的 Hodge 算子 $\star$。
在复化空间中使用实 Hodge 算子的复线性延拓。
把五模式等距编码为

$$
|0\rangle\leftrightarrow1,\quad |1\rangle\leftrightarrow u,\quad
|2\rangle\leftrightarrow n,\quad |3\rangle\leftrightarrow v,\quad
|13\rangle\leftrightarrow u\wedge v.
$$

其五维像 $S$ 的最小 $\star$-不变扩张是整个八维复化外代数。
令 $Q_S$ 为投影，$T=Q_S\star|_S$，则

$$
T|2\rangle=|13\rangle,\quad T|13\rangle=|2\rangle,\quad
T|0\rangle=T|1\rangle=T|3\rangle=0,\quad
T^\dagger T=P_2+P_{13}.
$$

另指定

$$
U_{\rm rel}=T+P_0+|3\rangle\langle 1|+|1\rangle\langle 3|
$$

则得到一个酉对合，且 $\det U_{\rm rel}=1$。
该补足不唯一。

证明。
$\star1=u\wedge v\wedge n$，
$\star u=v\wedge n$，$\star v=n\wedge u$，
$\star n=u\wedge v$，$\star(u\wedge v)=n$。
前三个像补出原五基缺少的三个基元；三维欧氏情形 $\star^2=I$，
故所需扩张恰为全八维。
压缩删除前三个像，所以得到 $T$ 的公式及秩二结论。
$U_{\rm rel}$ 是两个互不相交的换位和一个固定点，
故保内积、平方为一、行列式为一。
在 $\operatorname{span}_{\mathbb C}(|2\rangle,|13\rangle)^\perp$ 上任选酉算子均可补足同一个 $T$，
所以对偶关系未选定唯一门。
证毕。

这是 [seams](#ref-seams) 定理 31.3 的明确五模版本，
Hodge 公式见 [hodge](#ref-hodge)。
一个几何关系可以为门的某个子块提供理由；
把它延伸成闭合门，需要保存其他输入的范数与信息。

**命题 3.4（三种正交性）。**
以下三个陈述不等价：
几何向量 $a\cdot b=0$；
结果投影 $P Q=0$；
操作反交换 $AB+BA=0$。
原子的占位读口

$$
N_x=P_1+P_{13},\quad N_y=P_3+P_{13},\quad N_z=P_2
$$

两两交换，且 $N_xN_y=P_{13}\ne0$。

证明。
三个占位算子在同一个模式基中对角，故交换，乘积公式直接计算。
Pauli 矩阵 $\sigma_x,\sigma_y$ 反交换且可逆；
正交投影若乘积为零则不能同时可逆。
而两个正交 Bloch 方向的正本征投影满足
$\operatorname{tr}(P_aP_b)=1/2$，并非互斥。
证毕。

因此非交换量子读出要在关系操作中构造。
它不能由给三个位置坐标命名为“正交”直接获得。

## 4. 正交三轴、局部复单位与五模式的统一复结构

<a id="def:clifford"></a>

**定义 4.1（Clifford 复合条件）。**
给一个实欧氏三维空间 $V$。
要求表示方向的操作在含幺实结合代数中满足

$$
ab+ba=2\langle a,b\rangle1.
$$

令 $\mathrm{Cl}_{3,0}$ 为由此关系生成的普遍代数；
对合固定向量并反转乘积次序。
本条件指定了方向的复合规则，超出了单纯的点距与垂直关系。

<a id="thm:clifford"></a>

**定理 4.2（三轴关系的内生虚单位）。**
对正向正交单位标架 $(u,v,n)$，令 $\omega=uvn$。
则

$$
\omega^2=-1,\qquad \omega^\dagger=-\omega,\qquad
\omega\in Z(\mathrm{Cl}_{3,0}),\qquad
\mathrm{Cl}_{3,0}\cong M_2(\mathbb C)
$$

作为实 $*$-代数成立。
且

$$
uv=\omega n,\qquad (uv)^2=-1.
$$

平面 $\operatorname{span}_{\mathbb R}(u,v)$ 上的 $J_nx=xuv=n\times x$ 满足 $J_n^2=-I$。

证明。
正交生成元平方为一、两两反交换。
计算 $\omega^2$ 有三次负号；反转三个因子也有三次负号。
每个生成元与 $\omega$ 交换，故后者居中。
所有单词约化为
$1,u,v,n,uv,vn,nu,uvn$ 的实线性组合。
将 $(u,v,n)$ 送到 $(\sigma_x,\sigma_y,\sigma_z)$，
这八项的像在 $M_2(\mathbb C)$ 中实线性独立并张成全部空间，
给所述 $*$-同构。
右乘 $n$ 得 $uv=\omega n$；
若 $x=su+tv$，则 $xuv=sv-tu$，逐项得平面公式。
证毕。

这个定理给“复平面来自正交读出”一个精确版本：
*定向、度量及 Clifford 复合把面积关系变成平方为负一的操作。*
复数没有被预放进实代数的系数中，
但 Clifford 复合本身是需要解释或验证的输入。
三维实坐标空间不是一维复平面，也不是量子位的态空间。

**命题 4.3（局部复角）。**
令 $p=(1+n)/2$。则

$$
p\,\mathrm{Cl}_{3,0}\,p=\operatorname{span}_{\mathbb R}\{p,\omega p\}\cong\mathbb C,
\qquad \jmath:=\omega p,\quad
\jmath^2=-p,\quad \jmath^\dagger=-\jmath.
$$

左理想 $\mathrm{Cl}_{3,0}p$ 是复二维旋量空间。

证明。
在 Pauli 表示中 $p=\operatorname{diag}(1,0)$。
角代数只有左上复数项，左理想则只有第一列可非零，
分别为 $\mathbb C$ 和 $\mathbb C^2$。
证毕。

在一般系统代数中实现这个校准时，须给一个二维块投影 $q$ 及实 $*$-嵌入
$\iota:\mathrm{Cl}_{3,0}\to q\mathfrak A q$，其单位满足 $\iota(1)=q$。
此时三轴关系的右端是 $2\langle a,b\rangle q$，且

$$
p=\frac{q+\iota(n)}2,\qquad
\jmath=\iota(\omega)p,\qquad
p(q\mathfrak A q)p\supseteq\operatorname{span}_{\mathbb R}\{p,\jmath\}.
$$

后面的五事件接口只识别这个指定的复标量角与
$\operatorname{span}_{\mathbb R}\{P_0,\jmath\}\subseteq P_0\mathfrak A P_0$，
即 $p\leftrightarrow P_0$；不把块单位 $q$ 识别为 $P_0$ 或全系统单位 $I_5$。
只要另外保留的角自由度更大，也不宣称整个 $P_0\mathfrak A P_0$ 必为复数。
矩阵单位构造只需显示的复标量子角。
这里 $p$ 的秩一指局部 $M_2(\mathbb C)$ 的不可约旋量表示；
若环境带重数 $m$，它在实际载体上的秩可为 $m$，仍是该局部抽象代数的最小投影。

局部三轴得到的旋量维数二，与五个模式的维数五不同。
下面给出二者之间的一条附加桥，而不把它们直接认成同一个空间。

<a id="def:matrixunits"></a>

**定义 4.4（相融的五事件运输）。**
在非零实含幺 $*$-代数 $\mathfrak A$ 中，给非零元素 $E_{st}$，
$s,t\in\Sigma$，满足

$$
E_{st}E_{uv}=\delta_{tu}E_{sv},\quad
E_{st}^\dagger=E_{ts},\quad
\sum_sE_{ss}=1.
$$

记 $P_s=E_{ss}$。再在角 $P_0\mathfrak A P_0$ 中给
$\jmath^\dagger=-\jmath$、$\jmath^2=-P_0$。
这里 $E_{st}$ 表示相干的模式运输及其相融关系；
它不是只表示“图上存在一条边”。

<a id="thm:globalcomplex"></a>

**定理 4.5（从局部复角到统一五模复代数）。**
在定义 [4.4](#def:matrixunits) 下，置

$$
F_{st}=E_{s0}\jmath E_{0t},\qquad
J=\sum_sF_{ss}.
$$

由 $E_{st}$ 和 $\jmath$ 生成的实 $*$-子代数 $\mathfrak B$ 满足

$$
\boxed{\mathfrak B\cong M_5(\mathbb C),\quad
J^2=-1,\quad J^\dagger=-J,\quad
Z(\mathfrak B)=\operatorname{span}_{\mathbb R}\{1,J\}.}
$$

因此五个角共享一个兼容的复数乘法。

证明。
矩阵单位关系直接给

$$
\begin{aligned}
E_{st}F_{uv}&=\delta_{tu}F_{sv},&
F_{st}E_{uv}&=\delta_{tu}F_{sv},\\
F_{st}F_{uv}&=-\delta_{tu}E_{sv},&
F_{st}^\dagger&=-F_{ts}.
\end{aligned}
$$

故这些五十个实元素的张成是含所有生成元的 $*$-代数。
如果
$\sum_{st}(a_{st}E_{st}+b_{st}F_{st})=0$，
左右乘 $E_{0s},E_{t0}$ 得
$a_{st}P_0+b_{st}\jmath=0$。
若 $b_{st}\ne0$，$\jmath$ 是 $P_0$ 的实数倍，
平方不可能等于 $-P_0$；于是 $a_{st}=b_{st}=0$。
所以这些元素独立。
映射 $E_{st}\mapsto e_{st}$、$F_{st}\mapsto\mathrm{i} e_{st}$
因此是到 $M_5(\mathbb C)$ 的实 $*$-同构。
$J$ 对应 $\mathrm{i} I$；中心公式由矩阵单位的交换条件立即得到。
证毕。

这个矩阵单位应用给出本篇使用的运输桥：
局部复结构要成为所有模式共同的相位语言，
需要保持它的跨模式运输。
生成代数给出最小不可约复表示 $\mathbb C^5$；
更大系统可以有表示重数或额外不可见自由度，
不能从该代数识别排除它们。

这里运输的是指定角 $p\,\mathrm{Cl}_{3,0}\,p$ 中的 $\jmath$，
并非把全部三轴算符同时放入每个模式角。
如果每个模式角还完整保留一份 $M_2(\mathbb C)$，
矩阵单位连同这些角自由度生成的是
$M_5(M_2(\mathbb C))\cong M_{10}(\mathbb C)$。
只保留复标量结构是在选择子代数或指定角，
不能称为把整个简单代数 $M_2(\mathbb C)$ 商成 $\mathbb C$。

<a id="prop:transport"></a>

**命题 4.6（树运输与回路相容）。**
若五个正交事件 $P_s$ 的和为一，
沿连通图的树给带支撑的部分等距，取根运输 $T_0=P_0$，使根到 $s$ 的运输 $T_s$ 满足

$$
T_s=P_sT_sP_0,\quad T_s^\dagger T_s=P_0,\quad
T_sT_s^\dagger=P_s,
$$

则 $E_{st}=T_sT_t^\dagger$ 满足定义 [4.4](#def:matrixunits)。
沿不同路径运输同一个 $\jmath$ 得到同一个局部复单位，
当且仅当相应根角回路运输与 $\jmath$ 交换。

证明。
支撑正交使 $T_t^\dagger T_u=\delta_{tu}P_0$，所以矩阵单位关系成立。
同一终点的另一运输可写为 $T'_s=T_sh$，
其中 $h=T_s^\dagger T'_s$ 是根角的酉元素。
于是
$T'_s\jmath T_s'^\dagger=T_s\jmath T_s^\dagger$
当且仅当 $h\jmath h^\dagger=\jmath$，即所述交换条件。
证毕。

这里的回路判据只要求 $h\in Z_{U(P_0\mathfrak A P_0)}(\jmath)$，
即根角酉群中 $\jmath$ 的中心化子。它不要求 $h=P_0$，也不要求每条路径的运输算子相同。
表示若为 $\mathbb C^5\otimes\mathbb C^m$，这套生成代数可作用为
$M_5(\mathbb C)\otimes I_m$，五个 $P_s$ 的秩就都是 $m$；
因此“事件等价”不蕴含环境中秩一，也不蕴含无重数。
在实底层空间上的复共轭 $C$ 满足 $CJC^{-1}=-J$；若另行加入这种操作，
$J$ 便不再居于整个扩大的实操作代数的中心。它不是上述复线性生成代数中的酉元。

保持复结构不要求全部回路相位为零：
$h=\cos\theta\,P_0+\sin\theta\,\jmath$ 就保持 $\jmath$。
但若额外操作反转该虚单位，定理 [4.5](#thm:globalcomplex) 只描述生成子代数，
不能无条件宣称整个可访问代数都以 $J$ 为中心。
原 DAG 没有实际逆边时，形式伴随也不能当作已获准的反向控制。

**命题 4.7（奇数维障碍）。**
实奇数维空间不存在 $L^2=-I$；
复奇数维空间不存在两个可逆反交换算子。
所以三只处处平方为 $I$ 的 Pauli 算子不能直接充当全五维模式的三轴。

证明。
第一项取行列式得 $(\det L)^2=-1$。
第二项若 $AB=-BA$，则

$$
\det(AB)=(-1)^d\det(BA)=-\det(AB),
$$

与可逆性矛盾。
证毕。

## 5. 正性、递归细分与 Born 概率

### 哪些正性具有量子内容

“新增了一条预测记录”可定义一个非负计数。
量子正性则要求对每个复系数组合 $c$ 都有

$$
\sum_{st}\overline c_sc_tK_{st}\ge0,
$$

或者等价地在某个已确定的矩阵代数上要求 $\rho\succeq0$。
后者约束全部交叉项，强于各项计数非负。
例如矩阵
$\left(\begin{smallmatrix}1&2\\2&1\end{smallmatrix}\right)$
对角非负，在向量 $(1,-1)$ 上却给负二次型。

<a id="prop:square"></a>

**命题 5.1（旋转与正交合并强制平方律）。**
在实欧氏空间 $V$、$\dim V\ge2$ 上，设
$Q:V\to[0,\infty)$ 旋转不变、$Q(0)=0$，
且 $x\perp y$ 时 $Q(x+y)=Q(x)+Q(y)$。
则存在 $c\ge0$，使 $Q(x)=c\left\lVert x\right\rVert^2$，无需预设连续性。

证明。
旋转传递性给 $Q(x)=f(\left\lVert x\right\rVert^2)$。
取正交的 $\sqrt{s}e_1,\sqrt{t}e_2$ 得 $f(s+t)=f(s)+f(t)$。
非负性使 $f$ 单调；有理等分给 $f(q)=qf(1)$，
有理上下逼近给全部实 $s\ge0$ 的同一公式。
证毕。

实数、欧氏范数及合并规则已在前提中。
这解释了平方律的一条理由，没有从五个标签生成实数域或概率语义。

<a id="def:valuation"></a>

**定义 5.2（全效果相融赋值）。**
在定理 [4.5](#thm:globalcomplex) 的代数中取

$$
\operatorname{Eff}_5=\{E=E^\dagger:0\le E\le I\}.
$$

赋值 $\mu:\operatorname{Eff}_5\to[0,\infty)$ 满足

$$
\mu(I)=1,\qquad
\mu(E+F)=\mu(E)+\mu(F)\quad(E,F\ge0,\ E+F\le I).
$$

同一效果在不同测量细分中取同一值。
量词覆盖全部所声明的效果，而不是只覆盖五个模式投影。

<a id="thm:born"></a>

**定理 5.3（Born 形式与自动连续性）。**
对任意有限正整数 $d$，把上一定义的维数五换为 $d$，
每个赋值唯一写为

$$
\boxed{\mu(E)=\operatorname{tr}(\rho E),\quad \rho\succeq0,\quad\operatorname{tr}\rho=1.}
$$

并有

$$
|\mu(E)-\mu(F)|\le\left\lVert E-F\right\rVert_{\rm op}.
$$

极端赋值对应秩一状态；对单位 $\psi,\phi$，

$$
\rho=|\psi\rangle\langle \psi|,\quad E=|\phi\rangle\langle \phi|
\quad\Longrightarrow\quad \mu(E)=|\langle\phi,\psi\rangle|^2.
$$

证明。
可加性给 $\mu(0)=0$、单调性和有理齐次性；
有理上下夹逼给 $\mu(tE)=t\mu(E)$，$0\le t\le1$。
对 $A\ge0$ 取充分大 $c$，置
$L_+(A)=c\mu(A/c)$。
齐次性使它与 $c$ 无关，可加性传到正锥。
令 $L(A-B)=L_+(A)-L_+(B)$；
若两种正差相同，交叉移项及正锥可加性保证良定义。
于是 $L$ 为 Hermitian 空间的实线性正泛函。
迹配对给唯一 Hermitian $\rho$；
秩一投影上的非负性给 $\rho\ge0$，$L(I)=1$ 给迹一。
由 $-\left\lVert X\right\rVert I\le X\le\left\lVert X\right\rVert I$ 得连续界。

若 $\rho$ 有至少两个正本征值，可在二者间作相反小扰动，
把它写为两个不同密度态的平均。
若 $\rho=|\psi\rangle\langle \psi|$ 是两个密度态的严格凸组合，
在 $\psi^\perp$ 上的非负期望之和为零，迫使两态均支撑于 $\mathbb C\psi$，
故都等于 $\rho$。最后迹计算给平方模。
证毕。

这是 Busch 全效果版本的有限维形式 [busch](#ref-busch)。
其作用是把*已定义的效果合并逻辑*约束为唯一的权重形式，
并使赋值连续性成为结论。
全效果域和效果的操作标定仍须建立。
五结果的单个测量只确定 $\rho$ 的对角，不能据此援引全效果定理。

**例 5.4（局部三轴相融仍不足）。**
对量子位投影 $P_n=(I+n\cdot\sigma)/2$，$\left\lVert n\right\rVert=1$，令

$$
\mu(P_n)=\frac{1+n_z^3}{2},\qquad \mu(0)=0,\quad\mu(I)=1.
$$

它非负、连续，且 $\mu(P_n)+\mu(P_{-n})=1$。
对任一正交标架 $(n_1,n_2,n_3)$，
$\sum_i n_{i,z}^6\le(\sum_i n_{i,z}^2)^3=1$；取 $r=\sum_i n_{i,z}^3n_i$，
便有 $r\cdot n_i=n_{i,z}^3$、$\|r\|^2=\sum_i n_{i,z}^6\le1$，故每一组三轴都有一个拟合态。
但标准三轴迫使候选全局态的 Bloch 向量为 $(0,0,1)$；
在 $n_z=1/2$ 时该态给 $3/4$，本赋值给 $9/16$。
因此它不能扩张为全效果相融赋值。

<a id="prop:classicalrecursion"></a>

**命题 5.5（递归历史概率及其不唯一性）。**
在有限分支历史树上给 $w(\varnothing)=1$、
$w(h)\ge0$，且对每个非终端前缀
$w(h)=\sum_ow(ho)$。
比较固定深度时，把已经停止的终端记录按吸收 Stop 后继补齐，
父质量完整传给这个唯一后继。
则有限层记录具有相容概率律。
在 $w(h)>0$ 处，条件行唯一为 $q_h(o)=w(ho)/w(h)$；
零质量前缀的归一化行可任取。
反之任给这些条件行，可用乘积递归构造 $w$。

证明。
补齐后每层总质量由前一层守恒归纳为一，
删去末结果的边缘等于父质量。
正质量处比值与乘积互逆；零质量的全部孩子质量均为零，
所以任意归一化补行不会改变任何有限记录律。
证毕。

它把“概率有递归逻辑”精确化了，但同一支撑树可有无穷多套条件行。
例如每次都允许两个结果，任取 $0<q<1$ 的 Bernoulli 条件行，
所有有限字均可能，数值概率却不同。
预测的存在、递归和正性没有选择某个 $q$。

若还给独立同分布重复制备，事件样本平均 $\widehat p_n$ 满足

$$
\mathbb E(\widehat p_n-p)^2=\frac{p(1-p)}n,\qquad
\Pr(|\widehat p_n-p|\ge\varepsilon)
\le\frac{p(1-p)}{n\varepsilon^2}.
$$

这些由方差可加和 Markov 不等式直接得到，
给权重与频率的一个标定接口；独立重复也是额外条件。

## 6. 递归预测怎样产生线性接续和量子仪器

### 相干递归比概率树多保存什么

一个概率树只记录每个分支的非负数值。
相干递归还要保存：两个不同描述以后合并时的交叉关系。
项目预测记忆卷 §§12--14 正是用这类跨分支条件连接记录与仪器 [memory](#ref-memory)。

<a id="def:kernel"></a>

**定义 6.1（正核相干描述与分支守恒）。**
对每个阶段 $t$ 给共同类型的描述集 $\mathscr X_t$，
及复 Hermitian 核 $K_t$，满足对每个有限系数组合

$$
Q_t\!\left(\sum_i c_i[x_i]\right)
=\sum_{ij}\overline c_ic_jK_t(x_i,x_j)\ge0.
$$

系数的复结构可取自上一节的统一 $J$。
对某个共同合法动作 $a$ 给有限输出集 $O_a$ 和接续
$r_{a,o}:\mathscr X_t\to\mathscr X_{t+1}$，要求

$$
\boxed{K_t(x,y)=\sum_{o\in O_a}
K_{t+1}(r_{a,o}x,r_{a,o}y).}\tag{K}
$$

失败与停止均计入输出；不通过删除分支实现归一化。
若动作只在一个子域合法，则以下结论限制于该子域的线性张成。

这里正核、相干组合和全部交叉项守恒是明确的附加结构。
给每个结果一个正数不等于给了一个正核；
知道两个描述各自的范数也不等于知道它们的内积。
从实核起步只能先得到实空间；
把它接到上一节还需证明每个分支与 $J$ 相容，
即 $M_oJ_t=J_{t+1}M_o$。

<a id="thm:kernel"></a>

**定理 6.2（递归核守恒的记录等距定理）。**
将自由复线性空间商去零范数关系并完成，得到

$$
H_t=\overline{\mathbb C[\mathscr X_t]/\mathcal N_t}.
$$

定义 [6.1](#def:kernel) 的每个接续唯一下降为有界复线性映射
$M_o:H_t\to H_{t+1}$，且

$$
M_o|x\rangle=|r_{a,o}x\rangle,\qquad
\sum_oM_o^\dagger M_o=I.
$$

因而

$$
\boxed{V_a\psi=\sum_oM_o\psi\otimes|o\rangle}
$$

是一个把结果记录纳入输出的等距映射。
有限维时

$$
\mathcal I_o(\rho)=M_o\rho M_o^\dagger,\qquad
\sum_o\mathcal I_o\ \text{完全正且保迹}.
$$

证明。
正半内积的 Cauchy--Schwarz 不等式使每个零范数向量与所有向量正交，
所以 $\mathcal N_t$ 为线性子空间，商内积非退化。
在自由空间按生成元延拓接续为线性映射 $L_o$。
将式 (K) 乘以 $\overline c_ic_j$ 并求和，得到

$$
\sum_oQ_{t+1}(L_ov)=Q_t(v).
$$

若 $Q_t(v)=0$，每个非负项都为零，
故每个 $L_o$ 保持全部零关系，下降到商。
又 $\left\lVert M_ov\right\rVert\le\left\lVert v\right\rVert$，所以唯一连续延拓到完成。
显示的求和式给 $\sum_o\left\lVert M_ov\right\rVert^2=\left\lVert v\right\rVert^2$，
极化得算子恒等式及 $V_a^\dagger V_a=I$。
对任意辅助维数，每项共轭
$(M_o\otimes I)X(M_o^\dagger\otimes I)$ 保正；
循环迹和求和恒等式给总和保迹。
证毕。

**已有核下降合同在同一表示中的应用。** [memory](#ref-memory) 命题 12.2 不只检查两个描述是否相同。
对候选摘要 $S^0[x]=[s(x)]$，代数下降的充要条件是对所有有限系数族都有

$$
Q\!\left(\sum_i c_i[x_i]\right)=0
\ \Longrightarrow\
\widehat Q\!\left(\sum_i c_i[s(x_i)]\right)=0.
$$

完成后存在有界摘要的充要条件是再有一个统一的 $C<\infty$，使

$$
\widehat Q(S^0v)\le C^2Q(v)\qquad(v\text{ 为任意有限组合}).
$$

证明。第一条件恰为商的代表无关性；第二条件恰为商上的有界性，
Cauchy 序列延拓给充分性，算子范数给必要性。
仅无有限零关系不保证有界：$K(n,m)=\delta_{nm}$、
$\widehat K(n,m)=n^2\delta_{nm}$、$s(n)=n$，$n\ge1$，
两侧均无非零有限零关系，但 $|n\rangle/n$ 在源中趋零、在像中范数恒一。
全权重摘要满足 $\widehat Q(S^0v)=Q(v)$，故取 $C=1$ 并为等距。
定理 6.2 的分支也取 $C=1$；这些统一界控制完成，无需假设有限描述集。证毕。

若从实核开始，另给正交复结构 $J_t^2=-I$、$J_t^\dagger=-J_t$，
并要求 $M_oJ_t=J_{t+1}M_o$。以 $J$ 定义复数乘法后，
$\langle x,y\rangle_{\mathbb C}=(x,y)_{\mathbb R}-i(x,Jy)_{\mathbb R}$
是取第一变量共轭线性的内积，这些分支才是同一复表示中的线性分支。
单独给每阶段一个平方为负一的算子，却不保持它，不足以把实接续认作复线性接续。

这个证明中，振幅层的线性来自两步：
先用自由线性空间表示允许的相干组合，再用守恒保证所有零关系都能下降。
如果物理上不允许相干制备这些组合，
数学张成不会自动授予这种制备能力。
单独检查 $x=y$ 的范数守恒也不够；零关系涉及所有有限组合。

**命题 6.3（核秩与观察者的精确保真容量）。**
对有限描述集，最小生成空间的维数为 Gram 矩阵的秩。
任何保留全部相干权重的线性摘要
$S:H\to\widehat H$ 都为等距，
所以 $\dim\widehat H\ge\dim H$。

证明。
商空间维数是 Gram 矩阵秩。
若 $\left\lVert Sv\right\rVert^2=\left\lVert v\right\rVert^2$ 对全部 $v$ 成立，
复极化给内积保持，故 $S$ 单射并满足维数下界。
证毕。

受限任务摘要只需保留指定效果的统计，可以更小；
对任意描述集 $\mathscr X$（不要求可数），[memory](#ref-memory) 命题 13.3 给出如下有限容量判据。令

$$
d_*=\sup_{F\subseteq\mathscr X\ \mathrm{finite}}
\operatorname{rank}[K(x,y)]_{x,y\in F}
\in\mathbb N_0\cup\{\infty\},
$$

约定空 Gram 矩阵秩为零，$\infty$ 只表示有限秩无界。
若 $d_*<\infty$，则最小生成空间满足 $\dim H=d_*$，任何全权重线性摘要均满足 $\dim\widehat H\ge d_*$；
若 $d_*=\infty$，则不存在有限维全权重线性摘要。

证明。每个有限 Gram 矩阵的秩等于对应生成向量的线性张成维数。
若 $d_*<\infty$，整数秩的上确界由某个有限集 $F_0$ 取得。
其张成记为 $L$；若某个生成向量不在 $L$ 中，加入它便使秩超过 $d_*$，矛盾。
所以全部生成向量都在这个 $d_*$ 维空间内，而有限维子空间闭，完成后仍有 $H=L$。
特别地，$d_*=0$ 时全部生成向量为零，$K=0$、$H=\{0\}$，包括空描述集情形。
若有限秩无界，对每个有限整数 $n$ 都有秩大于 $n$ 的有限 Gram 矩阵，
其张成含多于 $n$ 个线性无关向量。
全权重摘要由内积保持而单射，不能把这个张成送入 $n$ 维空间，故排除每个有限目标维数。证毕。

这一判据不确定无限维完成的 Hilbert 基数维数。
例如对任意无限集 $I$，核 $K(i,j)=\delta_{ij}$ 的有限 Gram 秩为 $|F|$，上确界均为上述 $\infty$，
而完成是 $\ell^2(I)$，其标准正交基的基数为 $|I|$。
取 $I=\mathbb N$ 与 $I=\mathbb R$，便分别得到基数维数 $\aleph_0$ 与 $|\mathbb R|$。
在每个阶段取同一核、单个输出及恒等接续，就满足定义 6.1 的式 (K)；分支守恒不排除这一区别。
可数描述仍可给 $\ell^2$，不能从描述可枚举推出有限记忆。

这个全权重下界不适用于任意粗粒化任务。

<a id="thm:history"></a>

**定理 6.4（同一接续生成历史、概率与条件态）。**
在有限维仪器中令
$M_h=M_{o_n}\cdots M_{o_1}$，
动作可以由已经取得的前缀记录选择。
初态为 $\rho$ 时，令

$$
\sigma_h=M_h\rho M_h^\dagger,\qquad p(h)=\operatorname{tr}\sigma_h.
$$

则父子质量守恒；正质量处条件态为
$\rho_h=\sigma_h/p(h)$，其下一结果概率为

$$
q_h(o)=\operatorname{tr}(M_o\rho_hM_o^\dagger).
$$

对固定无反馈协议，或相应相干受控接续也已供应的反馈协议，
保留正交记录而不读取时，总演化为逐次记录等距的复合。

证明。
固定前缀后动作已确定；
$\sum_oM_o^\dagger M_o=I$ 给
$\sum_o\operatorname{tr}(M_o\sigma_hM_o^\dagger)=\operatorname{tr}\sigma_h$。
再除以正的父概率得到条件行。
在所声明的相干提升中，等距的复合仍为等距；
输出记录按不同历史取正交标签，
展开即得到各分支的 $M_h$。
证毕。

于是“观察者预测行为也是自己的增长”可精确定义为：
状态与记录按同一个分支接续关系更新。
选择某个结果后的归一化映射通常非线性，因为它要除以结果概率；
这不改变未选择的线性仪器。

<a id="prop:recordphase"></a>

**命题 6.5（同一分支概率不决定相干提升）。**
即使全部普通输出分支相同，保留相干记录的总过程仍可能不同。

证明。
取一维输入，两个普通分支均为 $X\mapsto X/2$。
两种记录等距为
$V_+z=z|+\rangle$ 与 $V_-z=z|-\rangle$。
它们在记录基 $|0\rangle,|1\rangle$ 上给相同概率，
但若允许同一个后续 $|+\rangle\langle +|$ 效果，概率分别为一和零。
普通分支只固定记录密度矩阵的对角块，没有固定交叉块。
证毕。

一般粗输出仪器为

$$
\mathcal I_o(X)=\sum_{\alpha}K_{o\alpha}XK_{o\alpha}^\dagger,
\qquad \sum_{o,\alpha}K_{o\alpha}^\dagger K_{o\alpha}=I.
$$

一个结果 $o$ 可以需要多个 Kraus 算子。定理 6.2 的单算子分支形式可用于细分记录 $(o,\alpha)$，
随后按实际仪器遗忘细分指标；不能直接断言每个粗结果都有一个 $M_o$。
细分的数学表示不授权读取或相干操纵环境指标。
若输出保留相干记录 $R$，必须另供共同 CPTP 提升 $\Lambda$，满足

$$
\Lambda_{oo'}(X)
=(I\otimes\langle o|)\Lambda(X)(I\otimes|o'\rangle),
\qquad\Lambda_{oo}=\mathcal I_o.
$$

普通分支只固定对角块。甚至单 Kraus 情形的
$V_\vartheta\psi=\sum_o e^{i\vartheta_o}M_o\psi\otimes|o\rangle$
也使交叉块乘上 $e^{i(\vartheta_o-\vartheta_{o'})}$ 而不改变任何普通分支。
对供应的两个提升及摘要 $\mathcal E$，完整接续须逐块满足
$\mathcal E_{t+1}\Lambda_{oo'}=\widehat\Lambda_{oo'}\mathcal E_t$；
只检查 $o=o'$ 不足。这是 [memory](#ref-memory) §14 的直接应用，
由记录矩阵单位的独立性逐块比较即得；若后继只访问经典记录，交叉块不参与该受限任务。

这也解释了为什么静态图的同一终点可能需要保留不同路径的相位。
若可相干选择路径 $p,q$ 并重合控制，则

$$
p_+=\frac{1+\Re\langle U_p\psi,U_q\psi\rangle}{2}.
$$

即使 $U_q\psi=e^{\mathrm{i}\phi}U_p\psi$，终态射线相同，
仍有 $p_+=(1+\cos\phi)/2$。
控制与相位参考的存在是该任务的前提。

<a id="thm:interference"></a>

**定理 6.6（干涉的二次结构与三阶消去）。**
在同一个核及固定线性接续下，令 $a,b,c$ 为三个可比较的末端振幅向量，
$q(S)=\left\lVert \sum_{v\in S}v\right\rVert^2$。
则

$$
q(\{a,b\})=q(\{a\})+q(\{b\})+2\Re\langle a,b\rangle
$$

及

$$
\begin{aligned}
I_3={}&q(\{a,b,c\})-q(\{a,b\})-q(\{a,c\})-q(\{b,c\})\\
&+q(\{a\})+q(\{b\})+q(\{c\})=0.
\end{aligned}
$$

若分支另留记录 $m_a,m_b$，忽略记录后两路径交叉项乘以
$\langle m_a,m_b\rangle$。

证明。
展开平方范数；每个单项和两两交叉项在 $I_3$ 中的总系数均为零。
带记录时将两末端向量替换成 $a\otimes m_a,b\otimes m_b$，
张量内积即给重叠因子。
证毕。

这是二次量子测度的标准特征，见 [sorkin](#ref-sorkin)。
它提供具体检验：理论若保留本节条件，就不能同时产生一个真正独立的三阶项。
不同实验中打开、关闭路径若改变了其他振幅或仪器，
则不能直接把它们代入同一个 $q$。

## 7. 混合一致性、参考系统与可逆门

**定义 7.1（制备相融）。**
若两种制备在全部允许未来测试上相同，视为同一操作态。
已标定的随机混合以凸组合表示；
合法更新必须与混合相容，不能依赖一个无法观察的制备分解。

<a id="thm:affine"></a>

**定理 7.2（状态更新的线性延拓）。**
若 $T:\mathcal D_d\to\mathcal D_e$ 保持全部凸混合，
则它唯一延拓为正、保迹的实线性映射
$\operatorname{Herm}_d\to\operatorname{Herm}_e$，继而唯一复线性延拓到矩阵空间。

证明。
对非零 $A\ge0$ 置
$\widetilde T(A)=\operatorname{tr}(A)\,T(A/\operatorname{tr} A)$，零处取零。
归一化 $A+B$ 是以两者迹为权重的混合，
所以正锥上可加；非负齐次性直接成立。
通过正差延拓，与定理 [5.3](#thm:born) 相同的交叉移项证明良定义。
最后每个复矩阵唯一写为 $A+\mathrm{i} B$，$A,B$ Hermitian，
给复线性延拓。正性、保迹及唯一性由正锥生成性得到。
证毕。

这里得到的是操作态的线性表示。
它不从无结构的五点推出物理叠加，也不选择一个时间参数。
有限维延拓自动连续，与连续时间动力学的假设不同。

**定义 7.3（未触碰参考的一致性）。**
已给定独立系统的复张量复合。
要求对任意有限参考维数 $n$，
同一个局部线性更新 $\Phi$ 满足

$$
(\operatorname{id}_n\otimes\Phi)(X)\ge0\qquad(X\ge0).
$$

这里 $X$ 量化于整个联合正锥，包括纠缠算子；仅对可分态或已制备子集保正不能替代它。
这种要求称完全正性，简称 CP。
不选择结果且保持总质量的更新还应保迹，简称 CPTP。

<a id="thm:choi"></a>

**定理 7.4（参考一致性的有限证书）。**
对复线性 $\Phi:M_d(\mathbb C)\to M_e(\mathbb C)$，以下等价：

$$
\Phi\text{ 完全正}
\quad\Longleftrightarrow\quad
C_\Phi:=\sum_{ij}e_{ij}\otimes\Phi(e_{ij})\succeq0
\quad\Longleftrightarrow\quad
\Phi(X)=\sum_\alpha K_\alpha X K_\alpha^\dagger.
$$

保迹当且仅当 $\sum_\alpha K_\alpha^\dagger K_\alpha=I$，
等价于 $\operatorname{tr}_{\rm out}C_\Phi=I$。

证明。
$C_\Phi=(\operatorname{id}_d\otimes\Phi)(|\Omega\rangle\langle \Omega|)$，其中
$|\Omega\rangle=\sum_i|i\rangle|i\rangle$ 未归一化，故 CP 蕴含其正性。
反过来正谱分解 $C_\Phi=\sum_\alpha|v_\alpha\rangle\langle v_\alpha|$，
唯一写 $v_\alpha=\sum_i|i\rangle\otimes K_\alpha|i\rangle$。
比较第一因子的各矩阵块，得到每个 $e_{ij}$ 的 Kraus 公式，
线性给全部 $X$。
Kraus 共轭在任意辅助系统上保持正性。
循环迹以及矩阵块偏迹分别给最后两个等价条件。
证毕。

这是标准 Choi--Kraus 表示的有限维证明，参见 [watrous](#ref-watrous)。
单系统正性并不足够：
维数 $d\ge2$ 时，转置 $X\mapsto X^{\mathsf T}$ 正且保迹，
但它对最大纠缠投影的部分作用为交换算子除以 $d$，
在反对称向量上有负本征值。
因此“预测结果必须非负”要升级为
“与任何未触碰参考共同使用时仍合法”，才能得到 CP。

<a id="thm:unitary"></a>

**定理 7.5（合法可逆过程必为酉）。**
设 $\Phi,\Psi:M_d(\mathbb C)\to M_d(\mathbb C)$ 都为 CPTP，
且 $\Psi\Phi=\Phi\Psi=\operatorname{id}$。则存在酉 $U$，使
$\Phi(X)=UXU^\dagger$。

证明。
取 Heisenberg 对偶 $T=\Phi^*,S=\Psi^*$，它们均含幺、CP、互为逆。
正块矩阵
$\left(\begin{smallmatrix}A^\dagger A&A^\dagger\\A&I\end{smallmatrix}\right)$
在 $\operatorname{id}_2\otimes T$ 下仍正，
Schur 补给 $T(A^\dagger A)\ge T(A)^\dagger T(A)$。
施 $S$ 并对 $S$ 再用同一不等式：

$$
A^\dagger A\ge S(T(A)^\dagger T(A))\ge A^\dagger A.
$$

故全为等号，$S$ 单射给
$T(A^\dagger A)=T(A)^\dagger T(A)$。
对 $A+B,A+\mathrm{i} B$ 极化，得
$T(A^\dagger B)=T(A)^\dagger T(B)$，故 $T$ 为 $*$-同构。

$T(e_{ii})$ 是 $d$ 个非零正交投影、和为 $I_d$，所以均秩一。
选单位 $u_0\in\operatorname{ran}T(e_{00})$，令 $u_i=T(e_{i0})u_0$。
矩阵单位关系给 $u_i$ 正交归一且
$T(e_{ij})=|u_i\rangle\langle u_j|$。
于是 $T(A)=VAV^\dagger$，$V|i\rangle=u_i$；
取对偶得 $U=V^\dagger$。
证毕。

可逆量子操作的更一般表示见 [nayak](#ref-nayak)。
这里“可逆”是物理上存在合法逆过程；
一个线性映射数学上可逆不保证其逆为正或 CP。

<a id="cor:gatecertificate"></a>

**推论 7.6（静态门的可检查证书）。**
一个双边界张量 $C$ 代表确定性量子过程，当且仅当

$$
C\succeq0,\qquad\operatorname{tr}_{\rm out}C=I_{\rm in}.
$$

若输入、输出同维且 $\operatorname{rank} C=1$，该过程恰为酉通道。

证明。
前半由定理 [7.4](#thm:choi)。
秩一给单个 Kraus 算子 $K$，保迹给 $K^\dagger K=I$；
同维时 $K$ 酉。反向直接构造 $C$。
证毕。

这为“量子门是极限静态图中的索引位置”提供一个具体数学版本：
每个索引必须连同满足上述关系的边界张量。
位置编号和边的存在本身不能代替这个证书。
形式 Choi 张量的存在也不授予将它作为物理程序读取或执行的能力。

<a id="prop:luders"></a>

**命题 7.7（效果概率不唯一决定测量更新）。**
一组效果 $E_o$ 不唯一决定产生它们的仪器。
即使要求投影结果可重复，退化投影上的后态仍可能不同。
若另规定每个分支只有一个正 Kraus 算子，
则该分支唯一为 $\rho\mapsto\sqrt{E_o}\rho\sqrt{E_o}$。

证明。
设 $P$ 秩至少二，$U$ 是保持 $\operatorname{ran}P$ 的非平凡酉。
$K=P$ 与 $K'=UP$ 都满足 $K^\dagger K=K'^\dagger K'=P$；
输出均支撑在 $\operatorname{ran}P$，所以再次测 $P$ 确定成功，
但后态通常不同。
若 $K\ge0$ 且 $K^\dagger K=E$，正平方根唯一性给 $K=\sqrt E$。
证毕。

Born 规则回答结果权重，仪器回答结果取得后如何继续。
这两项在递归观察理论中都要指定。

<a id="thm:schrodinger"></a>

**定理 7.8（连续门群的自伴生成元）。**
若 $U:\mathbb R\to U(d)$ 连续，$U(t+s)=U(t)U(s)$、$U(0)=I$，
则存在自伴 $H$，使

$$
U(t)=e^{-\mathrm{i} tH/\hbar},\qquad
\mathrm{i}\hbar\,\frac{d}{dt}\psi(t)=H\psi(t).
$$

证明。
所有 $U(t)$ 两两交换且正规，有限维中可同时酉对角化。
每个对角分量是 $\mathbb R\to U(1)$ 的连续群同态。
在零邻域选连续辐角，群律给局部可加关系，
连续性使辐角为线性函数，再由群律推广到全轴。
故各分量为 $e^{-\mathrm{i}\omega_jt}$；
取 $H=\hbar\,\operatorname{diag}(\omega_j)$ 并还原共同基，微分即得方程。
证毕。

单个离散酉门总可插值：
若 $U=\sum_je^{\mathrm{i}\theta_j}P_j$，任取 $\tau>0$ 及整数 $k_j$，

$$
H=-\frac{\hbar}{\tau}\sum_j(\theta_j+2\pi k_j)P_j
$$

都给 $U=e^{-\mathrm{i}\tau H/\hbar}$。
因此离散结构允许连续描述，却未唯一决定时间单位、能谱分支或物理 Hamiltonian。

## 8. 项目的实际五模式门：相位为什么是关键资源

### 原生耦合与原生相干见证

在 $\Sigma=(0,1,2,3,13)$ 上定义

$$
\begin{aligned}
H_1&=E_{01}+E_{10}+E_{3,13}+E_{13,3},\\
H_2&=E_{02}+E_{20},\\
H_3&=E_{03}+E_{30}+E_{1,13}+E_{13,1},\\
K&=H_1+H_2+H_3
=\begin{pmatrix}
0&1&1&1&0\\
1&0&0&0&1\\
1&0&0&0&0\\
1&0&0&0&1\\
0&1&0&1&0
\end{pmatrix}.
\end{aligned}
$$

项目原等待菜单是 $U(t)=e^{-\mathrm{i} tK}$、$t\ge0$，
以及完整秩一模式仪器 $X\mapsto P_sXP_s$ 和 Stop [static](#ref-static)。
把 $H_1,H_2,H_3$ 分别调节是一种扩大菜单。

**命题 8.1（受约束合法性）。**
在三量子位空间，令 $P_j^0=|0\rangle\langle 0|_j$，

$$
G_1=X_1P_2^0,\quad G_2=P_1^0X_2P_3^0,\quad G_3=P_2^0X_3.
$$

每个 $G_j$ 保持
$H_F=\operatorname{span}_{\mathbb C}\{|000\rangle,|100\rangle,|010\rangle,|001\rangle,|101\rangle\}$，
其限制就是 $H_j$。因此每个 $R_j(t)=e^{-\mathrm{i} tH_j}$ 不泄漏合法空间。

证明。
端点只在中位空时翻转，中位只在两端空时翻转，
故不会产生相邻 $11$。
自伴性还使正交补不变；幂和指数均保持该分解。
逐个合法基态计算得到上述矩阵。
证毕。

$H_j$ 自身一般有零特征值，不是酉门；
真正的门是指数 $R_j(t)$。
几何金字塔有八条棱，这个耦合图只有五条无向边，
二者也不能直接互换。

<a id="thm:nativewitness"></a>

**定理 8.2（原菜单已经区分相同人口的两态）。**
从 $P_0$ 出发，比较

$$
A:\ U(t),U(t),\text{末读};\qquad
B:\ U(t),\text{完整读并忽略结果},U(t),\text{末读}.
$$

中点的两态有完全相同五项人口。
但充分小的 $t>0$ 下，末读模式 $0$ 的概率满足

$$
p_A(0)=1-12t^2+O(t^4),\quad
p_B(0)=1-6t^2+O(t^4),\quad
p_B(0)>p_A(0).
$$

证明。
中点两态是
$\rho_c=U(t)P_0U(t)^\dagger$ 与
$\rho_m=\Delta(\rho_c)$，
$\Delta(X)=\sum_sP_sXP_s$，所以对角相同。
$K_{00}=0$、$(K^2)_{00}=3$，且实 $K$ 使转移模平方为偶解析函数，
故
$q(t)=|U(t)_{00}|^2=1-3t^2+O(t^4)$。
协议 $A$ 给 $q(2t)$。
协议 $B$ 给
$\sum_s|U(t)_{0s}|^2|U(t)_{s0}|^2$；
$s=0$ 项为 $q(t)^2$，其余项各为 $O(t^4)$。
差为 $6t^2+O(t^4)$，故在某个小正邻域严格为正。
证毕。

这是[memory](#ref-memory) 命题 16.2。
它给一个直接答案：
观察者若只保留三个均值，甚至保留全部五项人口，
仍可能遗漏同一原生未来任务所需的关系。
这里反驳的是*该人口摘要的充分性*，
没有据此排除所有带额外隐藏状态的经典模拟。

中间读后求和给 $\Delta$，省略中间读给恒等通道。
塔式条件概率在协议 $B$ 内成立，
不能用它把这两种物理操作认成同一个过程。

### 从旋转到全复控制

<a id="thm:so5"></a>

**定理 8.3（三个独立 PXP 控制的精确有限字范围）。**
另供应三个独立任意实角度 $R_j(t)$。
全部有限字的群恰为

$$
D\,SO(5)\,D^\dagger,\qquad D=\operatorname{diag}(1,\mathrm{i},\mathrm{i},\mathrm{i},1).
$$

证明。
暂以 $4$ 代模式 $13$，置 $A_{ab}=E_{ab}-E_{ba}$。
被动换基后

$$
L_1=A_{01}-A_{34},\quad L_2=A_{02},\quad L_3=A_{03}-A_{14},
\qquad L_j=D^\dagger(-\mathrm{i} H_j)D.
$$

故所有字在 $SO(5)$ 中。
令 $Q=e^{\pi L_2}=\operatorname{diag}(-1,1,-1,1,1)$。
则 $QL_1Q^{-1}=-A_{01}-A_{34}$；
这两个分量作用于不交坐标对并交换，所以

$$
\begin{aligned}
e^{tL_1/2}Qe^{-tL_1/2}Q^{-1}&=e^{tA_{01}},\\
e^{-tL_1/2}Qe^{-tL_1/2}Q^{-1}&=e^{tA_{34}}.
\end{aligned}
$$

对 $L_3$ 同理，得到平面 $03,14$；$02$ 已直接给定。
这些坐标对组成连通图。
沿路径用 $\pi/2$ 平面旋转共轭可搬移坐标轴，
遂取得任意坐标对旋转。
有限 Givens 消元将任意 $SO(5)$ 矩阵化成对角符号矩阵，
剩余偶数个负号由 $\pi$ 平面旋转消除。
因此每个目标都是有限字。共轭回原基完成证明。
证毕。

项目 [static](#ref-static) 命题 45 给出了相同的 Lie 代数和闭包；
其定理 64.1 已进一步给出全窗口尺寸的精确有限字结论。
这里将该既有精确控制结论的 $n=3$ 分项应用完整写出。
它没有给数字编译效率或实际角度无限精度。

<a id="thm:urel"></a>

**定理 8.4（候选几何交换的相位障碍）。**
定理 [3.3](#thm:hodge) 的 $U_{\rm rel}$，
即使乘任意整体相位，也不在定理 [8.3](#thm:so5) 的群中。
在原等待、完整读及 Stop 菜单内，
任何没有量子旁路或额外量子存储的确定性有限协议通道 $\Phi$ 都有

$$
\sup_\rho\frac12\left\lVert \Phi(\rho)-U_{\rm rel}\rho U_{\rm rel}^\dagger\right\rVert_1
\ge\frac12.
$$

证明。
$\widetilde U=D^\dagger U_{\rm rel}D$ 固定 $|0\rangle$，
交换 $|1\rangle,|3\rangle$，且
$\widetilde U|2\rangle=\mathrm{i}|13\rangle$、
$\widetilde U|13\rangle=-\mathrm{i}|2\rangle$。
若乘整体相位后为实，$00$ 项迫使该相位为实，
而 $13,2$ 项仍纯虚，矛盾。

原菜单在 $D$ 帧中所有等待、模式投影和反馈叶 Kraus 矩阵都为实；
经典随机混合后仍把实密度矩阵送到实密度矩阵。
取 $r=(|0\rangle+|2\rangle)/\sqrt2$，
目标为 $y=(|0\rangle+\mathrm{i}|13\rangle)/\sqrt2$。
对任意实密度矩阵 $\sigma$，
$\langle y,\sigma y\rangle=(\sigma_{00}+\sigma_{13,13})/2\le1/2$，
而目标纯态对 $|y\rangle\langle y|$ 的概率为一。
迹距离的效果界给下界 $1/2$，共轭回原基即可。
证毕。

这是[seams](#ref-seams) 定理 32.2 的障碍。
用于证明距离的效果不因此成为原菜单中的可调用读口。
另一算子 $DU_{\rm rel}D^\dagger$ 给相同标签置换却有不同相对相位，
并属于独立三控制群；这说明仅看模式置换不能识别完整量子门。

<a id="thm:u5"></a>

**定理 8.5（一个连续相位资源补足全部酉矩阵）。**
在独立三控制上再提供任意角度 $e^{\mathrm{i} tP_0}$，
有限字便得到全部 $U(5)$。

证明。
在 $D$ 帧，$P_0$ 不变。
$SO(5)$ 共轭取得每个实单位向量 $v$ 的 $e^{\mathrm{i} tvv^{\mathsf T}}$。
取五个坐标向量与十个 $(e_a+e_b)/\sqrt2$，
得到十五个独立实对称方向。
它们乘以 $\mathrm{i}$，连同十个实反对称方向，组成 $\mathfrak u(5)$ 的实基。
将这二十五个实际一参数群相乘，零处导数为切空间同构，
逆函数定理给单位开邻域。
有限字构成子群，故为 $U(5)$ 的开子群；
$U(5)$ 连通，因而该子群就是全群。
证毕。

<a id="thm:fixedphase"></a>

**定理 8.6（固定条件相位也足以控制全五模通道）。**
另供应固定门

$$
S_*=\exp(\mathrm{i}\pi P_{13}/2),\qquad S_*^4=I.
$$

则：

1. 仅 $R_1,R_3,S_*$ 就可精确实现
$V\oplus1$，其中任意 $V\in SU(4)$ 作用于底面

$$
C=\operatorname{span}_{\mathbb C}(|0\rangle,|1\rangle,|3\rangle,|13\rangle),
$$

旁观模式为 $|2\rangle$。
1. 再加 $R_2$ 后可精确实现所有 $SU(5)$。
完整有限字矩阵群恰为
$\{U\in U(5):\det U\in\{1,\mathrm{i},-1,-\mathrm{i}\}\}$；
故其酉通道覆盖全部五维酉通道。

证明。
以 $\iota|ab\rangle=|a0b\rangle$ 编码底面。
以下四阶码内矩阵按逻辑顺序 $(00,01,10,11)$ 排列，对应物理顺序 $(0,3,1,13)$；
五阶矩阵仍按 $(0,1,2,3,13)$ 排列。
$H_1|_C=X\otimes I$、$H_3|_C=I\otimes X$，
$S_*|_C=\operatorname{diag}(1,1,1,\mathrm{i})$。
前两个生成元在 $|2\rangle$ 上为零，故 $R_1,R_3,S_*$ 均固定 $|2\rangle$。
字

$$
R_3(-\pi/2)S_*R_3(\pi/2)S_*
$$

在码上等于 $\operatorname{diag}(1,1,\mathrm{i},\mathrm{i})$；
交换端点得到 $\operatorname{diag}(1,\mathrm{i},1,\mathrm{i})$。
两者共轭 $X$ 为 $Y$，于是每侧连续 $X,Y$ 旋转可用，
Euler 分解给全部局部 $SU(2)$。
又 $S_*^2=CZ$，且 $CZ(X\otimes I)CZ=X\otimes Z$。
局部共轭给九个 $\sigma_a\otimes\sigma_b$ 连续方向；
加六个单体 Pauli 方向共十五个，
乘以 $-\mathrm{i}$ 后构成 $\mathfrak{su}(4)$ 的实基。
其一参数群乘积在零处导数可逆，
同上开子群论证给全部 $SU(4)$，并在旁观态严格为一。

$H_2=|0\rangle\langle 2|+|2\rangle\langle 0|$。
$SU(4)$ 在码内单位向量上传递，
所以共轭可取得每个
$|v\rangle\langle 2|+|2\rangle\langle v|$ 的一参数群。
取四个码基向量及其 $\mathrm{i}$ 倍，得到八个跨块 $X,Y$ 方向。
在一个这样的二维平面内以 $\pi/4$ 共轭，
再得到对角差 $P_0-P_2$。
加上十五个码内方向共二十四个独立方向，
同一乘积映射及连通性给全部 $SU(5)$。

各 $R_j$ 行列式为一，$S_*$ 行列式为 $\mathrm{i}$，
故全部字的行列式在四次单位根中。
已有 $SU(5)$ 再乘 $S_*^k$ 覆盖每个相应陪集，
得精确群公式。任意酉通道可选择一个行列式为一的代表。
证毕。

底面通用控制对应 [bundle](#ref-bundle) 定理 8.11；
全五模结论也是 [static](#ref-static) 定理 64.1 的 $n=3$ 特例，
这里完整写出底面编码和中位耦合在该结论中的对应。
任意实角度、可重复相位门及其相位参考都是资源，
它们不会由“图上有一条关系边”自动出现。

**命题 8.7（静态相融保留操作次序）。**
$H_1,H_3$ 交换，但

$$
[H_1,H_2]=E_{12}-E_{21}\ne0.
$$

并且

$$
R_1(\pi/2)R_2(\pi/2)|0\rangle=-\mathrm{i}|2\rangle,\qquad
R_2(\pi/2)R_1(\pi/2)|0\rangle=-\mathrm{i}|1\rangle.
$$

证明。
用矩阵单位相乘得交换子。
$R_2$ 先把 $|0\rangle$ 送到 $-\mathrm{i}|2\rangle$，然后 $R_1$ 固定它；
反序先到 $-\mathrm{i}|1\rangle$，再由 $R_2$ 固定。
证毕。

整个网络可以静态定义，网络内部依然区分不同的操作路径。
约束陈述的顺序无关、张量求和的计算顺序无关，
不等于交换两个干预后结果也相同。

## 9. 关系谱、隐藏相位与复合系统

### 同一个四角系数的三种作用

<a id="thm:phase"></a>

**定理 9.1（关系系数同时控制统计与相位）。**
在五模式复表示中，另供应对角门
$U_f(t)=e^{-\mathrm{i} t\operatorname{diag}(f)}$。
定义正振幅域上的关系相位

$$
\Phi=\theta_0+\theta_{13}-\theta_1-\theta_3,\qquad
\psi_s=\sqrt{p_s}\,e^{-\mathrm{i}\theta_s}.
$$

则

$$
\frac{\partial\,\mathbb E_pf}{\partial\kappa}=J_f,\qquad
\Phi(t)=\Phi(0)+tJ_f\pmod{2\pi}.
$$

整体及单位置相位平移
$\theta_s\mapsto\theta_s+\alpha_0+\alpha_xx_s+\alpha_yy_s+\alpha_zz_s$
不改变 $\Phi$。
在底面两逻辑位上，$U_f(t)$ 为两侧局部门的张量积，
当且仅当 $tJ_f\in2\pi\mathbb Z$；
否则它把 $|++\rangle$ 变成纠缠态。

证明。
统计式来自定理 [2.3](#thm:fiber)。
门使 $\theta_s$ 增加 $tf_s$，代入四角差分得相位式；
对单位置仿射相位代入则四角差分为零。

在逻辑底面，用 $a,b\in\{0,1\}$ 写

$$
f_{ab}=f_{00}+(f_{10}-f_{00})a+(f_{01}-f_{00})b+J_fab.
$$

前三项只给整体及两侧相位。
输出 $|++\rangle$ 的系数矩阵为
$C_{ab}=\tfrac12e^{-\mathrm{i} tf_{ab}}$，
其行列式为

$$
\det C=\frac14e^{-\mathrm{i} t(f_{10}+f_{01})}
                 (e^{-\mathrm{i} tJ_f}-1).
$$

两位纯态可分当且仅当该矩阵秩一，
所以得到必要性、充分性及纠缠结论。
证毕。

这正是关系丛卷 §18 的统计与相位接口在五模式上的形式 [bundle](#ref-bundle)。
它给隐藏关系一个具体动力学作用：
一个对三均值不可见的系数，可以在已供应的相位执行器中积累可测试相位。
但函数 $f$ 存在与自然界能够执行 $e^{-\mathrm{i} t\operatorname{diag}(f)}$ 仍是两个条件。

**推论 9.2（概率完全稳定而关系变化）。**
底面纯态

$$
\psi_\phi=\frac{|00\rangle+|01\rangle+|10\rangle+e^{-\mathrm{i}\phi}|11\rangle}2
$$

对四模式始终给 $1/4$。
$\phi=0$ 时为乘积态；$\phi=\pi$ 时两侧边缘均为 $I_2/2$，
是最大纠缠纯态。

证明。
各振幅模相同。
零相位时系数矩阵是全一矩阵除以二，秩一；
相位 $\pi$ 时系数矩阵乘其伴随为 $I_2/2$。
证毕。

<a id="prop:phasewitness"></a>

**命题 9.3（隐藏相位的明确后继读出）。**
在全五模上令

$$
\psi_\theta=\frac{|0\rangle+|1\rangle+|2\rangle+|3\rangle+
 e^{-\mathrm{i}\theta}|13\rangle}{\sqrt5}.
$$

所有人口恒为 $1/5$，三均值为 $(2/5,2/5,1/5)$。
若下一步允许固定相位参考的 $R_1(\alpha)$，则

$$
\langle N_x\rangle_{\rm after}
=\frac25+\frac{\sin(2\alpha)\sin\theta}{5},\qquad
\langle N_y\rangle_{\rm after}=\frac25,\quad
\langle N_z\rangle_{\rm after}=\frac15.
$$

证明。
$R_1$ 在 $01$ 与 $3,13$ 两块均为
$\cos\alpha\,I-\mathrm{i}\sin\alpha\,X$。
第一块的模式一概率仍为 $1/5$；
第二块的模式 $13$ 振幅为
$(e^{-\mathrm{i}\theta}\cos\alpha-\mathrm{i}\sin\alpha)/\sqrt5$，
模平方为 $(1+\sin(2\alpha)\sin\theta)/5$。
两块总质量及模式二概率保持，得到其余公式。
证毕。

这个测试只读取相位的一个正弦分量，不是完整相位重建。
固定参考脉冲已经使相应相位差具有操作意义；
不能同时把它作为绝对不可观察的规范自由度删去。

**命题 9.4（一个关系量与一个关系角的辛配对）。** 在 $\mathbb {CP}^4$ 的全正人口层，
固定振幅约定 $\psi_s=\sqrt{p_s}e^{-i\theta_s}$，并以

$$
\theta_s=\theta_0+\alpha_xx_s+\alpha_yy_s+\alpha_zz_s+\Phi x_sy_s
\pmod{2\pi}
$$

为相位坐标。在单位向量的局部提升上置

$$
\alpha=i\langle\psi,d\psi\rangle=\sum_sp_s\,d\theta_s
=d\theta_0+X\,d\alpha_x+Y\,d\alpha_y+Z\,d\alpha_z+\kappa\,d\Phi,
\qquad\omega=-d\alpha.
$$

整体相位已在射影化中商去。固定均值 $(X,Y,Z)$，只在满足

$$
Z>0,\qquad
\max(0,X+Y+Z-1)<\kappa<\min(X,Y)
$$

的非空全正纤维上，再商去由 $N_x,N_y,N_z$ 生成的三维相位环面。
这个正则内部约化空间的坐标是
$(\kappa,\Phi)\in(\max(0,X+Y+Z-1),\min(X,Y))\times S^1$，且

$$
\omega_{\rm rel}=d\Phi\wedge d\kappa.
$$

以 $\iota_{X_h}\omega_{\rm rel}=dh$ 定义 Hamilton 场，便有
$\dot\Phi=\partial_\kappa h$、$\dot\kappa=-\partial_\Phi h$。

证明。五个相位的展开由 $1,x,y,z,xy$ 的基性质唯一给出，且这是整数单位三角变换，
故在模 $2\pi$ 的角上也可逆。将它代入有限和并用 $\sum_sp_s=1$ 即得 $\alpha$。
全正概率的独立坐标可取 $X,Y,Z,\kappa$；其开域正是逐项 $p_s>0$。
所以均值映射在这里秩三。相位环面在正射影层自由作用：
空模式和三个单位置模式的相位差迫使固定点的三个相位平移均为 $0\pmod{2\pi}$。
因而所述定值层的商是正则的，实维数为 $8-2\cdot3=2$。
拉回定值层后 $dX=dY=dZ=0$，$-d\alpha$ 的三个均值配对消失，
剩下 $-d\kappa\wedge d\Phi$；它沿被商去的方向为零且不随这些方向变化，故下降为显示的非退化二形式。
收缩给 $\iota_{X_h}\omega_{\rm rel}=\dot\Phi\,d\kappa-\dot\kappa\,d\Phi$，比较系数即得 Hamilton 方程。证毕。

这是 [bundle](#ref-bundle) §§4、18.3 的矩角配对在指定正支撑上的应用。
当 $h$ 的关系项为 $J_f\kappa$ 时，$\kappa$ 不变而 $\Phi$ 以速度 $J_f$ 增长，与定理 9.1 同号。
若改用 $e^{+i\widetilde\theta_s}$ 表示同一态，须同时取 $\widetilde\theta=-\theta$、$\widetilde\Phi=-\Phi$，
不能保持相位变量及二形式的显示符号都不变。
人口为零、均值位于边界或纤维退化时，相位坐标或自由作用可能失效，必须按实际支撑分层；
本命题不宣称那里仍有这个二维光滑约化空间，也不把其坐标识别为物理时空。

### 为什么张量复合必须单独处理

<a id="thm:seam"></a>

**定理 9.5（接缝决定独立编码是否存在）。**
两个直接相邻的合法三位窗口共有 $21$ 个联合合法模式，
其载体不能等距容纳全部 $\mathbb C^5\otimes\mathbb C^5$。
若另给一个初始化为零的分隔位，则

$$
\iota(|s\rangle\otimes|t\rangle)=|s\,0\,t\rangle
$$

给出完整二原子张量码的等距嵌入。

证明。
原有 $25$ 个模式对；
左块末位为一的模式有两个，右块首位为一的也有两个，
所以接缝排除四个，剩二十一。
等距映射是单射，二十五维不能等距进入二十一维。
插入零后全部接缝合法，不同基对仍映成不同正交基态，故等距。
证毕。

项目 [bundle](#ref-bundle) §17 明确区分独立拼接、保边缘相关补全、
筛选成功支和零分隔编码。
它们消耗不同资源、产生不同来源。
“原子递归自相似”不能代替独立复合规则。

<a id="thm:tomography"></a>

**定理 9.6（复矩阵层析与实模型的剩余关联）。**
在复张量模型中，全部局部乘积效果的联合概率唯一确定联合密度态。
标准实张量模型在两侧维数至少二时不满足同一性质。

证明。
复 Hermitian 空间的实基 $\{A_i\}$、$\{B_j\}$
给联合空间的实基 $\{A_i\otimes B_j\}$；
其个数为 $d^2e^2=(de)^2$。
每个 Hermitian 算子经缩放、平移是效果的实线性组合，
故乘积效果确定全部基系数。

实二维中令
$J_0=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$，
$T=J_0\otimes J_0$。
它实对称、$T^2=I$、$\operatorname{tr} T=0$，
所以 $\rho_\pm=(I\pm\varepsilon T)/4$，
$0<\varepsilon\le1$，是不同实密度态。
任意局部实对称效果 $A,B$ 满足
$\operatorname{tr}(AJ_0)=\operatorname{tr}(BJ_0)=0$，
所以全部乘积效果对两态给同一值，
而 $\operatorname{tr}(T\rho_\pm)=\pm\varepsilon$。
更高维嵌入此二维子空间即可。
证毕。

局部层析在这个候选类中排除了标准实张量完成；
它单独还不能排除经典理论和所有广义概率理论。
而分别知道两个边缘态比知道全部乘积实验的联合概率更弱。

**命题 9.7（纯化的条件量子构造）。**
给 $\rho=\sum_i\lambda_i|i\rangle\langle i|$，

$$
|\Psi_\rho\rangle=\sum_i\sqrt{\lambda_i}|i\rangle_A|i\rangle_E
$$

是一个纯化。
固定同维环境时，任意两个纯化由环境上的酉变换联系。

证明。
偏迹直接给 $\rho$。
把任一纯化写为 $\sum_i|i\rangle|v_i\rangle$，
边缘条件给 $\langle v_j,v_i\rangle=\lambda_i\delta_{ij}$。
正本征值对应的归一化环境向量为正交组；
两纯化间的对应等距可在同维环境补成酉矩阵。
证毕。

这是已经采用复量子复合后的定理。
如果要从操作公理重建复合形式，纯化的存在与本质唯一性可以成为输入原则。
“观察者在世界内部”本身并不给这条原则：
有限经典复合的纯态是点质量，其边缘仍是点质量，
无法把非平凡经典混态操作地纯化。

## 10. 量子基本原则在这条链中的位置

### 不确定性、逻辑与无扰动知识

**推论 10.1（三轴量子位的概率与半角）。**
在定理 [4.2](#thm:clifford) 的二维旋量表示中，
每个态唯一写为

$$
\rho=\frac{I+r\cdot\sigma}{2},\qquad\left\lVert r\right\rVert\le1.
$$

对单位方向 $n$，$P_n=(I+n\cdot\sigma)/2$，有

$$
p(n|r)=\frac{1+r\cdot n}{2}.
$$

若纯态方向 $m$ 与读出方向 $n$ 夹角为 $\theta$，
则 $p=\cos^2(\theta/2)$。

证明。
$I,\sigma_x,\sigma_y,\sigma_z$ 是 Hermitian 二阶矩阵的实基。
迹一固定标量项，$(r\cdot\sigma)^2=\left\lVert r\right\rVert^2I$
使本征值为 $(1\pm\left\lVert r\right\rVert)/2$。
正性给球条件；迹正交关系给概率，单位方向代入半角恒等式。
证毕。

如果三个读口确实是一个已知量子位的完整 Pauli 层析，
它们的期望固定就意味着该位的密度态固定。
仍可能变化的是联合关联、与环境的相关性或未知生成元，
而不是另有一个被完整单体层析遗漏的单体态参数。

<a id="thm:uncertainty"></a>

**定理 10.2（非交换预测的不确定界）。**
对 Hermitian $A,B$ 和密度态 $\rho$，

$$
\Delta_\rho A\,\Delta_\rho B
\ge\frac12\left|\operatorname{tr}(\rho[A,B])\right|.
$$

证明。
令 $A_0=A-\operatorname{tr}(\rho A)I$、$B_0=B-\operatorname{tr}(\rho B)I$。
对 Hilbert--Schmidt 向量 $A_0\sqrt\rho,B_0\sqrt\rho$
用 Cauchy--Schwarz 得

$$
(\Delta_\rho A)^2(\Delta_\rho B)^2
\ge|\operatorname{tr}(\rho A_0B_0)|^2
\ge\frac14|\operatorname{tr}(\rho[A,B])|^2.
$$

取平方根。
证毕。

这类不确定性来自同一正态对非交换操作的约束。
它不是因为不知道欧氏原点在哪里；
原子的三个对角占位读口交换，不直接产生这项非零下界。

**命题 10.3（从 Boolean 事件到非分配子空间）。**
五个固定模式投影及其和组成 Boolean 事件代数。
允许一般相干子空间后，事件格可非分配。

证明。
五模式投影对应五点集合的子集，交、并为集合交、并。
在二维子空间取
$A=\mathbb C e_0$、$B=\mathbb C(e_0+e_1)$、$C=\mathbb C(e_0-e_1)$，
则
$A\cap(B+C)=A$，
而 $(A\cap B)+(A\cap C)=0$。
证毕。

所以“相容逻辑”具有量子含义，取决于其允许的事件族。
在一个固定模式上下文中，确定赋值
$v_r(P_s)=\delta_{rs}$ 完全一致；
不能仅凭这个上下文证明语境性。

<a id="thm:noclone"></a>

**定理 10.4（不可克隆与无扰动知识）。**
不存在精确克隆所有未知纯态的确定性量子通道。
若等距过程原样保留两个非正交纯态，
并仅向环境写入与输入有关的纯记录，
则两记录相同。

证明。
Kraus 形式给记录环境等距。
如果输出两个副本都是指定的纯态，环境必须与它们乘积分离，
所以克隆等距可写

$$
V\psi=\psi\otimes\psi\otimes m_\psi,\quad
V\phi=\phi\otimes\phi\otimes m_\phi.
$$

令 $a=|\langle\psi,\phi\rangle|$，内积保持给
$a=a^2|\langle m_\psi,m_\phi\rangle|\le a^2$。
对 $0<a<1$ 矛盾。

若只要求保留一个副本，
$V\psi=\psi\otimes m_\psi$，
则非零内积可约去，给
$\langle m_\psi,m_\phi\rangle=1$，故归一记录相同。
证毕。

它限制内生观察者的增长方式：
可以新增记录、与来源相关、改变自己的预测状态，
但不能把未知量子信息无扰动地无限复制成独立知识。

### 纠缠、无信号与 Bell 界

<a id="thm:nosignalling"></a>

**定理 10.5（局部确定性更新保持另一侧边缘）。**
在已声明的张量复合中，对任意 $\rho_{AB}$ 和 CPTP $\Phi_A$，

$$
\operatorname{tr}_A[(\Phi_A\otimes\operatorname{id}_B)(\rho_{AB})]=\operatorname{tr}_A\rho_{AB}.
$$

证明。
对任意 $B$ 侧 Hermitian $O$，左侧期望等于
$\operatorname{tr}[\rho_{AB}(\Phi_A^*(I)\otimes O)]$。
保迹给 $\Phi_A^*(I)=I$，所以所有期望等于原边缘。
证毕。

选择并公布某个局部结果可以改变条件边缘；
这个条件过程不是上式的不选择确定性过程。

<a id="thm:bell"></a>

**定理 10.6（底面编码中的 CHSH 界）。**
给两逻辑位上的 Hermitian 对合 $A_0,A_1$ 与 $B_0,B_1$。
量子相关满足

$$
\left|\left\langle
A_0\otimes(B_0+B_1)+A_1\otimes(B_0-B_1)
\right\rangle\right|\le2\sqrt2.
$$

底面码内可达到该值。
相同四个相关若来自同一局部确定赋值的概率混合，则绝对值至多二。

证明。
记括号内算子为 $\mathcal B$。
利用 $A_i^2=B_j^2=I$ 得

$$
\mathcal B^2=4I-[A_0,A_1]\otimes[B_0,B_1].
$$

每个交换子范数不超过二，所以 $\left\lVert \mathcal B\right\rVert^2\le8$。
取 $|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$，
$A_0=Z,A_1=X$，
$B_0=(Z+X)/\sqrt2,B_1=(Z-X)/\sqrt2$，
则 $\mathcal B=\sqrt2(Z\otimes Z+X\otimes X)$，
期望为 $2\sqrt2$。
底面编码等距地保留此计算；
若制备和相应局部旋转已供应，便成为一个实际编码任务。

经典每个共同隐藏值给 $a_0,a_1,b_0,b_1\in\{-1,1\}$，
表达式 $a_0(b_0+b_1)+a_1(b_0-b_1)$ 总为正负二，
取概率平均保持界。
证毕。

这是标准 CHSH 与 Tsirelson 界在该编码中的应用 [chsh](#ref-chsh)、[tsirelson](#ref-tsirelson)。
其量子部分同时使用了态、测量和张量划分，
不能仅从五模式的图形读出。
同一个装置内部的两逻辑位也没有自动获得空间分离；
真实 Bell 实验还需独立设置及相应时空实验条件。

**例 10.7（三轴边缘稳定而联合相位变化）。**

$$
|\Phi_\phi\rangle=\frac{|00\rangle+e^{\mathrm{i}\phi}|11\rangle}{\sqrt2}
$$

对两侧均给边缘 $I_2/2$，全部单体 Pauli 期望为零。
但
$\langle X\otimes X\rangle=\cos\phi$、
$\langle X\otimes Y\rangle=\sin\phi$。
偏迹删除两分支交叉项，联合算符保留它们，直接计算即得。

这为“稳定的三轴之下仍有变化”提供严格位置：
变化可以处在跨侧关系中，即使每侧自身已经被三轴完整层析。

## 11. 内生观察者、静态极限与真正的稳定性

### 增长的等距序列可以有静态表示

**定义 11.1（完整观察者状态）。**
完整状态包括仍会影响未来的系统、记录、程序、相位参考和保留环境。
实际选择哪个动作以及某动作是否合法，应由这个完整状态中的已获资料决定。
把一项仍会返回的信息从载体删去后，局部状态未必还具有闭合更新。

<a id="thm:limit"></a>

**定理 11.2（相干增长的静态直接极限）。**
给 Hilbert 空间序列和完整记录等距
$V_n:H_n\to H_{n+1}$。
存在 Hilbert 空间 $H_\infty$ 及等距嵌入 $\iota_n$，满足

$$
\iota_{n+1}V_n=\iota_n,\qquad
\overline{\bigcup_n\iota_nH_n}=H_\infty.
$$

该构造在保持所有嵌入的酉同构意义下唯一。

证明。
把 $(n,\psi)$ 与 $(m,\phi)$ 在某个共同后继空间像相同时等同。
任意两个类都可推到共同后继，
在其中定义加法、标量乘法及内积。
等距性保证不依赖所选后继和代表，得到内积空间。
完成它即为 $H_\infty$，自然映射就是 $\iota_n$。
任何另一满足相同关系且稠密的实现，
在代数并上给唯一保内积映射，完成后为满射酉同构。
证毕。

这为静态总图与内部持续增长的共存给出数学模型。
它没有从一个未标注的 DAG 决定 $V_n$，
也没有要求每个阶段都新增可区分信息。
选择性条件态通常不按等距增长，不能把它直接代入本定理。
一般增长等距也非满射；只有同维有限闭合情形才成为酉门。

### “还需记住什么”由未来操作决定

**定义 11.3（未来效果闭包）。**
在固定有限维完整载体上，给有限仪器菜单 $\{\Phi_{a,o}\}$，
以及含 $I$ 的有限末端效果族 $\mathcal G$。
令

$$
W_0=\operatorname{span}_{\mathbb R}\mathcal G,\qquad
W_{n+1}=W_n+\sum_{a,o}\Phi_{a,o}^*W_n,\qquad
W_\infty=\bigcup_nW_n.
$$

所有分支必须在共同声明域内合法，全部相关记忆已计入载体。

<a id="thm:future"></a>

**定理 11.4（最小未来相融摘要）。**
若 $\dim H=d$、$\dim W_0=r_0$，则：

1. 至多 $d^2-r_0$ 次严格扩张后闭包稳定。
1. 两态对全部许可有限记录实验同律，当且仅当
$\rho-\sigma\in W_\infty^\perp$。
1. 在全部密度态来源上，最小仿射实坐标预测商的维数为
$\dim W_\infty-1$。

证明。
每个有限历史的概率是末端效果经分支对偶复合后的迹配对；
归纳得到 $W_n$ 是长度不超过 $n$ 的这些词效果的实张成。
一旦维数不增加，该空间已被每个分支对偶保持，
以后不再增加；环境实维数为 $d^2$。

全部词效果配对相同等价于完整有限记录律相同。
反馈时每个已得前缀确定同一后续动作，
逐前缀应用该事实即可；来源无关随机化可先固定再平均。

常数 $I$ 在闭包内，故其消去子包含于迹零空间。
规范化商的维数为
$(d^2-1)-(d^2-\dim W_\infty)=\dim W_\infty-1$。
若某仿射摘要秩更小，其核必包含一个未被 $W_\infty$ 消去的迹零方向 $D$。
在满秩态 $I/d$ 附近取 $I/d\pm\varepsilon D$，
它们给同一摘要却被某未来效果区分，矛盾。
取商坐标达到该维数。
证毕。

这使用项目关系丛卷的逐分支预测闭包 [bundle](#ref-bundle)。
闭包稳定是有限线性空间的稳定，
不是态随时间收敛，更不是有限样本已经精确知道全部概率。
仿射统计商也不自动提供一个可调用的量子压缩通道。

**有限与连续菜单的张成对应。** 定理 11.4 的有限性前提须在应用中兑现。
若改给任意一族同载体、共同合法的有限输出分支，对每层把求和写为所有分支像的实张成，
同一个证明仍给至多 $d^2-r_0$ 次严格增长。它是有限维线性代数的结论，不把连续标签改称有限菜单。

还有一个确切的有限见证：所有有限词效果的张成 $W$ 有限维，故可从实际词效果中选有限基，
连同 $W_0$ 使用；这些有限词中出现的动作标签只有有限个。
限于这些动作得到的闭包包含所选基，也包含于原闭包，所以两闭包相等。
这是存在性的张成对应，没有给选出该子菜单的有效算法或统一精度成本。
无限输出或增长载体仍需另给求和、拓扑和记忆条件，不能直接使用本段。

对全五维酉菜单，见证还可具体指定。已有五个末端投影 $P_s$；
对每对 $s<t$ 再取

$$
v_{st}^{+}=\frac{|s\rangle+|t\rangle}{\sqrt2},\qquad
v_{st}^{i}=\frac{|s\rangle+i|t\rangle}{\sqrt2}.
$$

分别选实际许可酉 $U_v$ 使 $U_v^\dagger|0\rangle=v$。
二十个这样的确定性动作加原来的末端族，就在词长一得到二十五个秩一投影，实张成为 $\operatorname{Herm}_5$：
减去对应对角项给全部实对称、虚反对称非对角方向。
若 $U_v$ 由定理 8.6 的有限控制字实现，取这二十个字中全部实际参数脉冲的有限并，
就得到与同一个全酉观察闭包相同的有限脉冲子菜单。
整体相位不影响拉回效果。这里的有限字、张成和合法读口都在同一个复表示中，未把控制闭包或无限角度集冒充已列出的有限原语。

**推论 11.5（全酉后继下三均值不会充分）。**
若五模后继允许全部酉通道和模式读出，
则 $W_\infty=\operatorname{Herm}_5$。
全来源仿射摘要需要二十四个实参数。

证明。
任意秩一投影都是某个模式投影的酉共轭。
秩一投影的实张成包含全部 Hermitian 矩阵，
故闭包维数二十五，再用定理 [11.4](#thm:future)。
证毕。

**命题 11.6（菜单仍对角时，全部记录具有经典表示）。**
若末端效果均对角，且每个分支对偶保持对角子空间，
则全部未来记录仅依赖人口。
对应经典分支为

$$
T_{a,o}(s,t)=\operatorname{tr}[P_s\Phi_{a,o}(P_t)].
$$

证明。
对偶闭包始终对角。
正性给 $T_{a,o}(s,t)\ge0$，分支和保迹给总转移列随机。
对任意输入 $\rho$，对偶保持对角使输出人口只由输入对角确定，
正是 $T_{a,o}$ 的作用。
逐步复合得到相同记录律。
证毕。

<a id="prop:realmenu"></a>

**命题 11.7（原生实帧仍隐藏一类复相干）。**
在原等待与完整模式读菜单中，所有有限协议效果在 $D$ 帧均为实对称。
因此它不能识别该帧密度矩阵的全部虚反对称部分。
特别地，原生相干见证并没有单独排除实量子描述。

证明。
等待矩阵为实正交，读投影实对称；
每个叶 Kraus 矩阵实，效果为 $L^{\mathsf T}L$，反馈事件效果为这些项之和。
对非零实反对称 $A$，取充分小 $\varepsilon>0$，

$$
\rho_\pm=I_5/5\pm\varepsilon\,\mathrm{i} A
$$

均为不同合法密度态。
任意实对称 $E$ 满足 $\operatorname{tr}(E\,\mathrm{i} A)=0$，所以全部记录同律。
一般 $\rho$ 的实部本身是实正半定迹一矩阵，
并给同样的这些效果统计。
证毕。

定义更丰富的相位与后继菜单会改变盲空间。
观察者“在哪里不确定”应表达为这个操作等价类，
而不是把全部不确定性统一解释成坐标原点的模糊。

### 镜像稳定有不同含义

本小节的迹距离记为
$D_{\rm tr}(\rho,\sigma)=\tfrac12\left\lVert \rho-\sigma\right\rVert_1$，
与前文被动相位矩阵 $D$ 区分。

<a id="thm:contraction"></a>

**定理 11.8（严格收缩与分辨率稳定）。**
设完整预测摘要空间 $(X,d)$ 非空且完备，
$T:X\to X$ 满足 $d(Tx,Ty)\le qd(x,y)$，$0\le q<1$。
则有唯一固定点 $x_*$，且从任意起点的迭代满足

$$
d(x_n,x_*)\le\frac{q^n}{1-q}d(x_1,x_0).
$$

若某个固定预算下的可区分距离 $d_R\le d$，
同一估计也控制该预算下的尾部稳定。

证明。
相邻增量不超过 $q^n d(x_1,x_0)$，几何级数给 Cauchy 及尾界。
完备性给极限，Lipschitz 性给固定点；
两个固定点的距离不超过其自身的 $q$ 倍，故相同。
用 $d_R\le d$ 即得预算结论。
证毕。

**命题 11.9（封闭酉轨道不能自动定格）。**
酉共轭保持迹距离。
一个固定酉的离散轨道如果收敛，则该轨道从起点就已固定。

证明。
酉共轭保持奇异值，所以保持迹范数。
相邻轨道点间的距离恒为
$D_{\rm tr}(U\rho U^\dagger,\rho)$；
收敛迫使它趋零，故这个常数为零，轨道恒定。
证毕。

所以镜子直觉可用于带耗散的粗粒化、学习算法或固定任务的预测摘要；
它不是所有封闭量子门序列的自动性质。

<a id="thm:readstability"></a>

**定理 11.10（边缘稳定、历史保持与标签不定格）。**
固定一次等待 $U$，每轮实际执行完整秩一模式读。
令

$$
M_{ij}=|U_{ij}|^2,\quad u=\mathbf1/5,\quad
J_5=\mathbf1\mathbf1^{\mathsf T}/5,\quad
\eta=\left\lVert M-J_5\right\rVert_{2\to2}<1.
$$

任意初态第一次读后人口为 $p_1$，则
*对全部已读结果取边缘*的非选择态
$\rho_n=\sum_i p_n(i)P_i$ 满足

$$
D_{\rm tr}(\rho_n,I_5/5)\le\eta^{n-1}\quad(n\ge1).
$$

但保留全部历史时，两初态的记录总变差恰等于其首读分布的总变差。
在相容无限记录律中，读数最终成为常数的概率为零。

证明。
$M$ 双随机，故 $MJ_5=J_5M=J_5$。
给定最后结果的条件态是对应基投影，
所以对记录取边缘后 $p_n=M^{n-1}p_1$。
$\left\lVert p_1-u\right\rVert_2\le2/\sqrt5$，结合
$\left\lVert v\right\rVert_1\le\sqrt5\left\lVert v\right\rVert_2$
给所述迹距离界。

每个完整记录的概率为

$$
p_1(i_1)\prod_{k=2}^n M_{i_k i_{k-1}}.
$$

对两初态作差，在每个固定首符号下对归一化后缀求和，
总变差恰等于首读总变差。

若某个 $M_{ii}=1$，则 $e_i-u$ 是 $M-J_5$ 的本征值一向量，
与 $\eta<1$ 矛盾。
所以从任何时刻起永远留在某 $i$ 的概率为
$p_m(i)\lim_{r\to\infty}M_{ii}^r=0$。
对有限个 $i$、可数个 $m$ 取并仍为零。
证毕。

$\eta=0$ 时约定 $\eta^0=1$；任意输入至迟第二轮边缘均匀，已对角输入一步均匀。
$t=0$ 给 $M=I$、$\eta=1$，不满足严格假设，标签反而在首读后恒定。
对原生 $U(t)=e^{-itK}$，[readrecursion](#ref-readrecursion) 的既有谱证书给
$\eta(2/3)<2/3$、$\eta(1)<23/50$，所以严格条件确有原生实例。
无限路径律由相容有限字母柱律扩张；每个实际前缀只执行有限步，并承担读出和记录资源。

这对应测量边界续卷的三种稳定性区分 [readrecursion](#ref-readrecursion)。
窗口边缘可以趋稳，完整过去依然存在，实际结果依然持续变化。
逐记录条件态仍是 $P_{i_n}$，它距 $I_5/5$ 的迹距离恒为 $4/5$；
上述趋零结论并不作用于这个条件态。

同样，递归程序本身不保证经验频率收敛：
按长度 $2^{2^k}$ 交替输出全零块和全一块，
每个新块压倒此前总长度，块末频率分别趋零、趋一。
若“所有概率都来自递归”指一种表示观点，可以用命题
[5.5](#prop:classicalrecursion) 精确表达；
若它指任何递归都唯一产生稳定数值概率，则上述反例已经否定该全称命题。

## 12. 综合条件重建及仍需完成的桥

### 一套可以逐项审查的充分条件

<a id="def:axioms"></a>

**定义 12.1（AURIC 相干观察单元的充分条件体系）。**
本篇考虑以下明确条件，而不主张其已为最小独立公理系。

1. **A1．原生合法性。** 五模式来自三位置相邻排斥；当前读口、制备和后继的共同合法域明确，失败与 Stop 不被删去。
2. **A2．方向复合与复角。** 定向欧氏三轴采用定义 4.1 的复合，在单位为 $q$ 的局部 $M_2(\mathbb C)$ 块校准；
   选 $p=(q+n)/2$ 及 $\jmath=\omega p$，把其最小复标量角与事件 $P_0$ 角识别。$q,p,I_5$ 分别定型。
3. **A3．相干运输。** 五事件具有定义 4.4 的矩阵单位；指定复角与它们生成系统代数 $\mathfrak B\cong M_5(\mathbb C)$。
   额外允许的运输保持同一 $J$，回路满足中心化子条件。关于生成子代数的结论不排除环境重数，亦不自动扩展到另行加入的反 $J$ 操作。
4. **A4．效果与制备相融。** 系统代数全部效果上的赋值非负、归一、对合法和可加且效果非语境；
   已标定随机混合由凸组合表示，共同制备分解的不可观察差异不影响合法更新。只给有限受限效果族时不援引全效果结论。
5. **A5．递归相干守恒。** 描述核、系统代数及读口属于同一个表示；供应定义 6.1 的正核、全部有限交叉关系守恒和 $J$ 相容接续。
   商映射保持全部有限零关系，并有统一有界延拓；全权重摘要保范数。记录、拒绝、Stop、相位参考和会返回的环境都计入完整载体。
   固定系统代数与增长的全记录代数分别标注，仪器若多 Kraus 则先细分再按指定合同取粗记录；可相干访问的跨记录块另供。
6. **A6．复合一致性。** 独立端口采用完整复矩阵张量复合，共享复数约定。
   对每个有限参考维数 $n$ 和整个联合正锥中的每个 $X\in M_n(\mathbb C)\otimes M_5(\mathbb C)$，
   同一个局部线性更新满足 $(\operatorname{id}_n\otimes\Phi)(X)\ge0$。
   其他窗口或完整记忆维数使用相同的全正锥量词；仅检查可分态或已制备子集不足。

真正闭合可逆的子过程另要求合法逆；
连续时间描述另要求定理 [7.8](#thm:schrodinger) 的群条件。

<a id="thm:main"></a>

**定理 12.2（条件综合重建）。**
在定义 [12.1](#def:axioms) 的条件下，有如下结论：

1. 五事件生成代数具有统一复结构，恰为 $M_5(\mathbb C)$。
1. 每个全效果相融状态唯一为密度算子，
结果权重为 Born 迹式，赋值自动连续。
1. 相干递归具有线性分支和完整记录等距；
混合相融更新具有线性表示，
参考一致性强制其完全正。
1. 闭合且具有合法逆的确定性过程为酉通道。
连续一参数门群具有 Schrödinger 形式。
1. 在明确的底面编码与条件相位操作下，
四角关系产生相位和纠缠；
已给复合中的局部确定性过程不传信号，
不确定关系与不可克隆均成立。
1. 若另供应 $R_1,R_2,R_3,S_*$ 的控制菜单，
该单元可精确实现所有五维酉通道。

证明。
第一项依次用定理 [4.2](#thm:clifford)、[4.5](#thm:globalcomplex)。
第二项为定理 [5.3](#thm:born)。
第三项分别用定理 [6.2](#thm:kernel)、[7.2](#thm:affine)、[7.4](#thm:choi)；
各表示一致性的要求确保这些结论作用于同一个操作对象。
第四项为定理 [7.5](#thm:unitary)、[7.8](#thm:schrodinger)。
第五项为定理 [9.1](#thm:phase)、[10.5](#thm:nosignalling)、
[10.2](#thm:uncertainty)、[10.4](#thm:noclone)。
第六项为定理 [8.6](#thm:fixedphase)。
证毕。

这个综合定理把“结构为基本原则提供理由”变成了逐项可核查的主张。
A2–A6 具有实质内容，不能在结论中删除。
它也没有说全部数学密度态、效果和通道已经由项目最小等待菜单可制备或执行；
若要作这项物理完备性主张，还必须证明相应操作可实现。

### 同时满足 A1–A6 的共同模型

取固定系统 $H=\mathbb C^5$，基顺序为 $(0,1,2,3,13)$，
$E_{st}=|s\rangle\langle t|$、$P_s=E_{ss}$、$\mathfrak B=M_5(\mathbb C)$。
它也可视为实十维空间上的实 $*$-代数。取

$$
q=P_0+P_1,\qquad
u=E_{01}+E_{10},\qquad
v=-iE_{01}+iE_{10},\qquad
n=P_0-P_1.
$$

三轴在 $qH$ 上是 Pauli 矩阵，在其正交补上为零，故

$$
u^2=v^2=n^2=q,\qquad uv=-vu=in,\qquad uvn=iq,
\qquad p=\frac{q+n}2=P_0,\qquad\jmath=iP_0.
$$

这实现的是单位为 $q$ 的局部 $\mathrm{Cl}_{3,0}$，并不要求三轴平方为 $I_5$。
由它运输得到 $F_{st}=iE_{st}$、$J=iI_5$，矩阵单位乘法与所有角单位逐项成立。
五模式来自声明的合法三位码；几何读出可独立取 $o=0,a=e_x,b=e_y,h=1$。
这给 A1–A3 的共同实现。若另取重数 $m$，所有这些固定系统算子张量 $I_m$ 即得带重数模型；
标准模型本身取 $m=1$，不从事件语法排除更大环境。

系统态取全部 $\rho\ge0$、$\operatorname{tr}\rho=1$，效果取全部 $0\le E\le I$，
赋值为 $\operatorname{tr}(\rho E)$；随机制备按凸组合，满足 A4。
对每个动作供应任意有限归一 Kraus 族 $\{K_{a,o,\alpha}\}$，
将结果细分为 $r=(o,\alpha)$，令 $M_{a,r}=K_{a,o,\alpha}$。
核描述集可取 $\mathscr X=H$，$K(x,y)=\langle x,y\rangle$，包含零向量描述。
于是

$$
r_{a,r}(x)=M_{a,r}x,\qquad
\sum_rK(r_{a,r}x,r_{a,r}y)
=\left\langle x,\sum_rM_{a,r}^\dagger M_{a,r}y\right\rangle
=K(x,y).
$$

任意有限零关系 $\sum_ic_ix_i=0$ 都被每个 $M_{a,r}$ 送为零；
核商的评价映射 $[x]\mapsto x$ 是满射等距，所以其完成恰为同一个 $H$。
每个分支范数至多一，且 $M_{a,r}J=JM_{a,r}$。这把 A5 的核、零关系、完成、
复结构与系统效果接在同一表示，未另造一份只共享维数的 Hilbert 空间。

固定深度的**完整记录载体**另为

$$
G_n=H\otimes R_1\otimes\cdots\otimes R_n,
\qquad R_k=\operatorname{span}_{\mathbb C}\{|r\rangle:r\text{ 为第 }k\text{ 步细分结果}\}.
$$

共同有限输出域可用零 Kraus 项补齐。无反馈时完整接续为

$$
V_n(x\otimes|h\rangle)=\sum_rM_{a_n,r}x\otimes|h\rangle\otimes|r\rangle.
$$

若动作依赖历史，用供应的相干受控实现把 $a_n$ 改为 $a(h)$；
经典策略本身不自动供应这种相干实现。在这里可显式选择它：
历史块正交，逐块的归一 Kraus 等式给 $V_n^\dagger V_n=I_{G_n}$。
$J_{G_n}=iI_{G_n}$，故完整接续同样相位相容；$G_n$ 上的核也统一为内积，
完整增长等距保存其所有有限交叉关系及完成范数。
$\mathcal L(G_n)$ 的增长并未被称为固定的 $M_5(\mathbb C)$；固定系统代数只通过 $A\mapsto A\otimes I$ 作用。
这些 $V_n$ 正是定理 11.2 使用的记录等距序列。

正交细分记录中的投影 $Q_o=\sum_\alpha|o,\alpha\rangle\langle o,\alpha|$ 给粗分支

$$
\operatorname{Tr}_{R}\!\left[(I\otimes Q_o)V\rho V^\dagger(I\otimes Q_o)\right]
=\sum_\alpha K_{o\alpha}\rho K_{o\alpha}^\dagger=\mathcal I_o(\rho).
$$

因此一般仪器与细分核模型一致；取粗记录是指定的量子操作，
不将不同 $\alpha$ 的正交向量直接识别为同一个振幅。
完整 $V$ 已指定记录相位，所以也指定交叉块；若只给 $\mathcal I_o$，它们仍不唯一。
所有相干制备和记录比较在此作为模型操作供应，不由标签可枚举推出。

对任意参考 $R'$ 及**任意** $X\ge0$，包括纠缠 $X$，

$$
(\operatorname{id}_{R'}\otimes\mathcal I_o)(X)
=\sum_\alpha(I\otimes K_{o\alpha})X(I\otimes K_{o\alpha}^\dagger)\ge0.
$$

归一 Kraus 等式又给总和保迹，故 A6 在整个正锥成立。
同样的公式作用于包含旧记录和会返回环境的完整载体，不以局部边缘替换相关记忆。
独立第二原子使用声明的 $H\otimes H$，或第 9 节的零分隔编码。
原生 $K$、完整模式读、独立 $R_j$ 以及 $S_*$ 都是本模型中的指定操作；
模式读的 Kraus 族是 $P_s$，酉动作是单个 Kraus 算子，Stop 可取吸收记录及恒等分支。
因而四种菜单、原生相干见证、条件相位和控制结论可共存于这个模型的不同已声明子菜单中。

这给 A1–A6 的一个非空共同模型及逐项验证。它是有限系统、各有限阶段有限记录的模型族；
无限增长只取定理 11.2 的 Hilbert 极限，不声称在五维中存下无限完整记录。
它也没有证明该全效果、全制备和全参考操作域由最小等待菜单取得，或自然界唯一采用这套条件。

### 推论与输入的账本

| 对象或规则 | 使其成立的具体条件 | 数学地位 |
| --- | --- | --- |
| 五种合法模式 | 三位置路径的相邻排斥 | 原生组合结果 |
| 四角关系 $J_f$ | 完整有限函数读出 | 唯一代数系数 |
| 三均值遗漏 $\kappa$ | 归一概率及给定读口 | 精确纤维定理 |
| 局部复单位 | 度量、定向、Clifford 复合 | 条件代数结果 |
| 统一 $M_5(\mathbb C)$ | 复角、相融相干运输、生成闭合 | 条件代数结果 |
| Born 与赋值连续 | 全效果域、正性、归一、可加 | 表示定理 |
| 振幅线性接续 | 正核、全部有限零关系及分支守恒 | 商空间定理 |
| 状态更新线性 | 制备混合与分解相融 | 延拓定理 |
| 完全正性 | 已有复合中任意参考的一致性 | 有限 Choi 证书 |
| 酉性 | CPTP 过程具有合法 CPTP 逆 | 可逆性定理 |
| 测量后态 | 具体仪器；Lüders 另需额外条件 | 不由效果独定 |
| 独立张量因子 | 独立端口或合法分隔编码 | 接缝条件 |
| 连续时间动力学 | 固定载体上的连续门群 | 生成元定理 |
| 全五维门控制 | 独立脉冲及附加相位资源 | 条件可达性 |
| 边缘稳定 | 收缩、退相干或明确学习条件 | 条件极限定理 |
| 物理空间、能量与场 | 独立物理编码、单位与经验标定 | 本篇未识别 |

### 与不预置 Hilbert 空间的重建路线的关系

本篇的 A2–A3 是代数路线：
它把“为什么会使用复数”缩小为可核对的几何复合和运输问题。
如果目标是完全不用 Clifford、矩阵效果或复正核作为输入，
则需要更底层的操作重建。

CDP 在其有限维操作概率、系统组合及闭包框架中，
以因果性、完美可区分性、理想压缩、局部可区分性、纯条件化及纯化
重建复量子论 [cdp](#ref-cdp)。
其 Theorem 20 给全部复密度态，Corollary 52 给全部 CP、迹不增分支。
这里援引的是原论文的完整定理，没有把它改称从五点直接得到的新证明。

这些原则须兑现为同一理论中的操作：
理想压缩应在态的整个生成面上无损；
局部区分使用乘积实验的联合概率；
纯化不仅要存在，还需固定同一个纯化系统时的可逆唯一性。
“观察者内生”“在任何尺度相融”可以启发这些原则，
但文字对应不构成对它们全部量词的证明。
项目预测记忆卷 §15 也明确保留这一缺口 [memory](#ref-memory)。

Hardy 的连续可逆性在其完整公理框架中承担重要作用 [hardy](#ref-hardy)。
有限经典单纯形的可逆仿射变换只排列极点，
因此任何从恒等出发的连续路径都为常值；
这是它不能像完整量子纯态那样连续互达的原因。
不过连续性单独仍不能排除实量子模型，
也不能省略其他复合、子空间和简约性原则。

### “基础原子”的一个可证明含义

<a id="thm:minimal"></a>

**定理 12.3（三位置是该协议的首个隐藏关系窗口）。**
在 no-$11$ 路径窗口族中，单位置均值加归一化能够确定
长度一和长度二窗口的全部模式概率。
长度三是第一个一般不能如此确定的窗口，
其遗漏恰为一个四角关系矩。
它也是该路径族第一个含完整双位逻辑立方体的窗口。

证明。
长度一合法模式为 $\varnothing,\{1\}$，
函数基为 $1,x_1$；长度二为 $\varnothing,\{1\},\{2\}$，
基为 $1,x_1,x_2$。
长度三首次出现联合合法模式 $\{1,3\}$，
完整基多出 $x_1x_3$，
定理 [2.3](#thm:fiber) 给恰一维遗漏。
前两个路径的最大独立集大小为一，
三位置的 $\{1,3\}$ 则提供
$\varnothing,\{1\},\{3\},\{1,3\}$ 四个合法子集，
恰为双位逻辑立方体。
证毕。

这提供了五模式基础性的明确理由：
*在指定排斥文法和一阶读出协议中，
它是单体读出首次遗漏联合关系、
并首次容纳双位条件相位的窗口。*
它没有宣称五维是最小可能量子系统；
量子位本身已是二维复系统。
“基础量子门”可以严谨地指这个条件下的原子控制单元。

### 下一层真正需要证明的内容

现在可以把未完成的问题缩小为四项具体数学义务：

1. **复合规则的原生理由。**
从实际允许的观察操作证明 Clifford 关系或另一个足以给复结构的规则。
仅有几何三轴和手性不足；还须说明反交换为什么是操作复合律。
1. **复结构的跨模式相融。**
构造实际相干运输，证明同一虚单位可在不同模式及回路中保持。
只取一个中心子代数时，说明未保留哪些额外旋量自由度。
1. **全效果与制备域的取得。**
证明可用测试足够支持全效果相融，或明确只对某个操作系统作受限表示。
原菜单的实帧盲方向已由命题 [11.7](#prop:realmenu) 给出，
所以不能在不扩大菜单的情况下宣称完成全部复层析。
1. **独立系统与观察者记忆。**
给出合法组合、压缩、参考扩张和返回环境的实际接口，
证明它们保持递归预测所需的交叉关系。
静态共同来源和增长的历史索引都不替代这些条件。

这些义务的完成方式可以是更底层公理、构造性定理或物理标定。
若希望达到类似 ZFC 的明确程度，
目标应是把基本对象、合法操作和推论写清楚，
让每个反模型都能指出究竟违反哪条公理；
不是通过重命名把尚未证明的条件消去。

## 13. 数学来源、归属与适用范围

函数代数、矩阵单位、Clifford–Pauli 对应、效果表示、Choi–Kraus 表示、可逆通道、
直接极限及不动点工具均为已有数学结构。上文完整证明是这些结果在指定五模式接口中的应用，
不把它们另立为新的基础理论。局部复角运输、精确控制和完整记录接续的结论，均保留相应输入条件。
标准量子后果不反向证明这些输入能由裸金字塔取得。
统计混合不自动解释为纯主观无知；静态表示也不自动解释为宇宙本体。

| 供应结果 | 本篇中的参数与消费者 |
| --- | --- |
| Static Fiber 定义 1.4、命题 43–45、§44 定理 64.1 | 逻辑顺序 $(0,1,2,3,13)$ 对应其 $(N,[2],[3],[5],[2,5])$；使用同一个 $K,D$，区分非负固定等待与独立实参数控制。精确有限字及固定相位行列式群是已有供应。 |
| Bundle §3、§4、命题 8.9–8.10、定理 8.11、§§16–18 | 五态函数与纤维、正支撑矩角配对、合法 PXP、保码控制、接缝和关系相位；第 9 节负指数与 $\omega=-d\alpha$ 使用同一约定。 |
| Seams §§31–32 | 正向标架为 $(u,v,n)$，逻辑模式顺序为 $(u,n,v)$；第 3 节 Hodge 压缩和补足、第 8 节 $U_{\rm rel}$ 的实帧障碍采用同一个位置／模式字典。 |
| Predictive Memory §§12–16 | 全部有限核零关系、有界完成、记录等距、普通分支与相干交叉块、复合输入和原生同人口见证；用于第 6 节与 A5 共同模型。 |
| Measurement Boundary Continuation I，WR1.1–WR1.3 | 同一固定原生等待与实际秩一读出，首读后转移 $M_{ij}=|U_{ij}|^2$，分别给边缘收缩、完整历史距离和无限路径不定格。 |
| Recursive Prediction、Unordered Atom、Origin/Tunneling 伴篇 | 分别提供相干／静态极限、局部表示／Born、稳定读口／隐藏相位的现有应用背景；本篇使用完整来源定义，不以伴篇摘要替代证明。 |

### 项目数学来源

<a id="ref-bundle"></a>

- **[bundle]** the-omega-institute/trureturing，[《AURIC FIB：关系丛与预测闭合理论》](https://github.com/the-omega-institute/trureturing/blob/968cc60bfa9674a58be91a10a1dd2ca72cab6581/docs/develop/theory/AURIC_FIB_RELATIONAL_BUNDLE_AND_PREDICTIVE_CLOSURE_THEORY.md)。主要使用 §3、§4、§8、§§16–18；当前对应源码为[关系丛卷](AURIC_FIB_RELATIONAL_BUNDLE_AND_PREDICTIVE_CLOSURE_THEORY.md)。

<a id="ref-seams"></a>

- **[seams]** the-omega-institute/trureturing，[《AURIC FIB ATOM：静态接缝、转移环流与 Fibonacci 翻转循环》](https://github.com/the-omega-institute/trureturing/blob/968cc60bfa9674a58be91a10a1dd2ca72cab6581/docs/develop/theory/AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md)，§§31–32；[对应源码](AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md)。

<a id="ref-memory"></a>

- **[memory]** the-omega-institute/trureturing，[《递归关系观察：自生成预测记忆》](https://github.com/the-omega-institute/trureturing/blob/968cc60bfa9674a58be91a10a1dd2ca72cab6581/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SELF_GENERATED_PREDICTIVE_MEMORY.md)，§§12–16；[对应源码](RECURSIVE_RELATIONAL_OBSERVATION_SELF_GENERATED_PREDICTIVE_MEMORY.md)。

<a id="ref-static"></a>

- **[static]** the-omega-institute/trureturing，[《AURIC $\Omega$：静态相融纤维理论》](https://github.com/the-omega-institute/trureturing/blob/968cc60bfa9674a58be91a10a1dd2ca72cab6581/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)，定义 1.4、概率与仪器接口、命题 43–45、§44 定理 64.1；[对应源码](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。

<a id="ref-readrecursion"></a>

- **[readrecursion]** the-omega-institute/trureturing，[《递归关系观察：测量相对量子边界续卷 I——等待读出递归》](https://github.com/the-omega-institute/trureturing/blob/968cc60bfa9674a58be91a10a1dd2ca72cab6581/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY_CONTINUATION_I.md)，WR1.1–WR1.3；[对应源码](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY_CONTINUATION_I.md)。

- **[companions]** [《AURIC 递归预测与边界几何》](AURIC_RECURSIVE_PREDICTION_AND_BOUNDARY_GEOMETRY.md) §§2、6–7；[《AURIC 无序相融原子与量子表示理论》](AURIC_UNORDERED_COMPATIBLE_ATOM_AND_QUANTUM_REPRESENTATION_THEORY.md) §§4–9；[《AURIC 内生原点不确定性与关系隧穿》](AURIC_ENDOGENOUS_ORIGIN_UNCERTAINTY_AND_RELATIONAL_TUNNELING.md) §8。

### 成熟数学与操作重建文献

<a id="ref-hodge"></a>

- **[hodge]** V. Bouchard，[MATH 215，Section 4.8: Hodge star](https://sites.ualberta.ca/~vbouchar/MATH215/section_hodge.html)，定义 4.8.1、三维例 4.8.4。这里使用实欧氏星号及其复线性延拓，按度量识别形式与多向量。

<a id="ref-busch"></a>

- **[busch]** P. Busch，*Quantum states and generalized observables: a simple proof of Gleason's theorem*，Physical Review Letters **91**, 120403 (2003)，[arXiv:quant-ph/9909073v3](https://arxiv.org/html/quant-ph/9909073v3)。本篇使用有限维、有限可加的全效果版本，正性导出的单调性和有理夹逼已足够给其普通证明；不把单个五结果上下文等同于全效果域。

<a id="ref-watrous"></a>

- **[watrous]** J. Watrous，*The Theory of Quantum Information*，Cambridge University Press, 2018，[作者提供的第 2 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.double.2.pdf)。完全正映射、通道与仪器的标准有限维背景；本篇所需 Choi、Kraus、保迹及仪器结论均在第 6–7 节给出矩阵证明，不依赖额外未列明定理。

<a id="ref-nayak"></a>

- **[nayak]** A. Nayak and P. Sen，*Invertible Quantum Operations and Perfect Encryption of Quantum States*，[arXiv:quant-ph/0605041](https://arxiv.org/abs/quant-ph/0605041) (2006)。该文讨论具有 CPTP 逆的量子操作；本篇只使用并完整证明同维双边可逆的酉特例，不把不同维环境附加的一般表示简化为同一个酉矩阵。

<a id="ref-cdp"></a>

- **[cdp]** G. Chiribella, G. M. D'Ariano and P. Perinotti，*Informational derivation of Quantum Theory*，Physical Review A **84**, 012311 (2011)，[arXiv:1011.6451v3](https://arxiv.org/html/1011.6451v3)。使用该文完整有限维操作概率、系统组合与闭包框架；Theorem 20 是全部复密度态，Corollary 52 是全部 CP、迹不增分支。本篇没有从局部 Clifford 或五点结构重新证明其公理前提。

<a id="ref-hardy"></a>

- **[hardy]** L. Hardy，*Quantum Theory From Five Reasonable Axioms*，[arXiv:quant-ph/0101012v4](https://arxiv.org/abs/quant-ph/0101012v4) (2001)。连续可逆性须与同文的其余公理合用；本篇只使用其完整重建路线作为对照，并直接证明有限经典单纯形的连续可逆路径只能为常值。

<a id="ref-sorkin"></a>

- **[sorkin]** R. D. Sorkin，*Quantum Mechanics as Quantum Measure Theory*，Modern Physics Letters A **9**, 3119–3128 (1994)，[arXiv:gr-qc/9401003](https://arxiv.org/abs/gr-qc/9401003)。这里的三阶消去由同一个固定二次型直接展开，不主张任意开关路径实验自动满足同一幅度标定。

<a id="ref-chsh"></a>

- **[chsh]** J. F. Clauser, M. A. Horne, A. Shimony and R. A. Holt，*Proposed Experiment to Test Local Hidden-Variable Theories*，Physical Review Letters **23**, 880–884 (1969)，[doi:10.1103/PhysRevLett.23.880](https://doi.org/10.1103/PhysRevLett.23.880)。本篇使用共同局部确定赋值的概率混合界，并给完整四符号证明。

<a id="ref-tsirelson"></a>

- **[tsirelson]** B. S. Cirel'son，*Quantum generalizations of Bell's inequality*，Letters in Mathematical Physics **4**, 93–100 (1980)，[doi:10.1007/BF00417500](https://doi.org/10.1007/BF00417500)。本篇完整证明所用二设置、二结果的 $2\sqrt2$ 算子界，并分别声明编码、态制备、测量与空间分离条件。

<a id="ref-control"></a>

- **[control]** D. D'Alessandro，*Uniform finite generation of compact Lie groups and universal quantum gates*，[arXiv:quant-ph/0111133v1](https://arxiv.org/html/quant-ph/0111133v1)。Lemma 1、Theorem 2 的实际单参数群、共轭基与逆函数方法支持第 8 节的精确有限字论证；实参数可正可负、所需逆均须可用。紧群的一般生成结论不赋予原固定非负等待菜单额外控制，也不提供本篇尚未评价的编译或硬件成本。

## 追加锚（本行以下为增补区）

## 14. 有向静态切面与内部访问的共同应用对象

**定义 14.1（配置扇区、边界与四类切面操作）。**
沿用[静态相融纤维 §§1、3](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)的配置约定：
事件集 $E$ 带有限主下集的偏序，合法配置向下闭，其有限子集须满足指定相容约束。
固定一个合法总体配置 $C_*$，令

$$
\mathcal I(C_*)=\{C\subseteq C_*:C\text{ 为有限向下闭配置}\},
\qquad C\le D\Longleftrightarrow C\subseteq D.
$$

对有类型的端口实现，$\partial C$ 包含穿越该区域边界的量子端口、未消去的输入、
环境、控制及记录。以下每个有限切面另要求只有有限个有限维端口；有限前驱性本身不保证此条件。
已供应复合规则时，$H_{\partial C}=\bigotimes_{e\in\partial C}H_e$。
无限端口使用 §15 的局部代数，不能无条件写一个未定义的无限张量积。
切面指标表示共同可实现区域的扩展或信息细化，不预置全局线性物理时间。

在同一端口模型中区分以下操作。

| 切面操作 | 保持的对象或新增条件 | 数学表示 |
| --- | --- | --- |
| 被动换表示 | 同一测试、结果、失败及资源的全部预测 | 保核等距或同时变换态与效果的酉坐标变换 |
| 移动完整边界 | 保留全部环境、记录及会返回的关联 | 有类型等距接续；有限同维时为酉 |
| 隐藏端口 | 明确遗忘环境、记录或关联 | 偏迹或 CPTP 通道 |
| 改变记录读口 | 供应新的可观测量或干预 | 可有同一非选择通道的不同仪器 |

最后一行改变条件实验；它不等于第一行的被动变基。
模式耦合图、几何五点图与协议事件 DAG 依[预测波 §5](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md)分别定型。
特别地，物理五模式、§18 的三维码及几何点集不是同一载体。

**定义 14.2（共同测试上的未知结构）。**
候选模型 $\omega$ 指定事件关系、端口分割、正核、仪器、记忆、相位参考、标定及合法测试。
对已经取得的记录 $h$，保留候选集 $\Omega_h$。
有限适应性测试 $\pi$ 必须在所比较模型中具有相同结果解释。
若合法性也未知，将不可执行、拒绝、失败及停止列为显式结果，
或先限制到共同合法域。定义集合值预测

$$
\mathcal P_h(\cdot\mid\pi)
 =\{p_\omega(\cdot\mid h,\pi):\omega\in\Omega_h\}.
$$

未给模型权重时不作概率平均。描述翻译须同时保持测试、资源、失败和结果语义；
任意重命名点或边不自动给这样的翻译。
对于固定共同测试族 $\mathfrak T$，令

$$
\omega\sim_{\mathfrak T}\omega'
\Longleftrightarrow
p_\omega(\cdot\mid\pi)=p_{\omega'}(\cdot\mid\pi)
\quad(\pi\in\mathfrak T).
$$

这里相等包括失败分布。若使用条件概率，限于共同正概率前缀；
更一般地先用未归一分支概率比较，零概率分支无需任意指定条件态。

**命题 14.3（内部访问的扇区与响应商）。**
$\mathcal I(C_*)$ 有向，所有配置的全集一般不有向。
属性 $f$ 可由共同完整响应精确确定，当且仅当 $f$ 在每个 $\sim_{\mathfrak T}$ 类上常值。
当 $\mathfrak T$ 包含全部许可有限适应性测试时，等价模型的所有这些内部记录律相同。
该响应商是语义摘要，不自动是可执行的 CPTP 压缩。

证明。
同一 $C_*$ 内两个有限向下闭配置的并仍有限、向下闭且合法，故为共同上界。
若 $a$ 有互斥后继 $b,c$，则 $\{a,b\}$、$\{a,c\}$ 没有合法共同上界；
所以有向极限限于相容扇区。跨扇区的相干叠加另需交叉核，概率混合另需权重。

令 $R(\omega)$ 为全部共同测试的响应。
若 $f=d\circ R$，同一响应必给同一 $f$；反之在达到像上定义
$d(R(\omega))=f(\omega)$ 即良定义。
这是[静态相融纤维 §4](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)响应商原理的参数对应，
源为候选模型、目标为全部指定测试的分布，包含非法结果。
固定适应性规则后，同一前缀选择同一后续测试；对未归一前缀质量按深度归纳，
得到所有有限记录律相同。输入无关随机控制可先条件化再按同一分布平均。
商能解码响应只证明集合因子化；它没有给正线性编码、任意参考合法性或物理解码器。
§20 的端口合同正保留这个区别。证毕。

## 15. 同一相容扇区中的正核、Hilbert 极限与局部态

**定义 15.1（有限相干比较与有向运输）。**
所有内积第一变量共轭线性。对边界表达式集 $X$ 给 Hermitian 核 $K$，要求

$$
\sum_{j,k=1}^m\overline c_jc_kK(x_j,x_k)\ge0
\quad(m<\infty,\ c_j\in\mathbb C).
$$

复相干组合、共轭与拼接的意义均为供应的结构。
对 $C\in\mathcal I(C_*)$ 给 $H_C$，对 $C\subseteq D$ 给全定义线性等距
$V_{DC}:H_C\to H_D$，满足

$$
V_{CC}=I,\qquad V_{FC}=V_{FD}V_{DC}.
$$

若它来自表达式运输 $r_{DC}$，则要求所有交叉项
$K_D(r_{DC}x,r_{DC}y)=K_C(x,y)$，以及接续复合一致；
仅保持每个标签的单独范数不足。

另外可以供应共享单位的有向递增 $C^*$ 代数族 $\mathcal A_C$ 及相容态
$\omega_D|_{\mathcal A_C}=\omega_C$。
这是不同类型的输入：一般非满等距给的角嵌入
$A\mapsto V_{DC}AV_{DC}^\dagger$ 把 $I$ 送到 $V_{DC}V_{DC}^\dagger$，
不能直接将它称作共享单位的代数包含。

**支撑推导 15.2（正核应用的存在、唯一性与有限证书）。**
在定义 15.1 的全部有限正性条件下，边界表达式具有唯一的最小 Hilbert 表示，
有限子集表达的独立维数等于其 Gram 秩。
相容有限 Gram 数据决定该表示；固定有限对角值并给闭的有界关系约束时，
全部有限约束共同可满足足以保证一个全局正核。
这些结论不由裸图或逐边正性替代。

证明。
所消费的是本卷定理 6.2 的核商构造与命题 6.3 的秩结论，而非另一份核重建定理。
其在此的生成标签为有限边界表达式、零关系为全部有限相干组合的零范数关系。
具体在 $\mathbb C^{(X)}$ 上置

$$
\langle\sum_xa_x[x],\sum_yb_y[y]\rangle_K
 =\sum_{x,y}\overline a_xb_yK(x,y).
$$

展开 $\|u+\lambda v\|_K^2\ge0$ 对所有复 $\lambda$ 给 Cauchy–Schwarz，
故零范数向量与全部向量正交，零空间 $N_K$ 为线性子空间。
商后完备化得到 $H_K$，$\eta(x)=[[x]]$ 满足
$K(x,y)=\langle\eta(x),\eta(y)\rangle$。
两最小表示在有限和上按同一系数对应保内积，由稠密性唯一延拓为满酉。
有限生成向量的关系空间为 Gram 核，故维数为 Gram 秩。

若每个有限 $S\subseteq X$ 给 PSD 矩阵 $G_S$，且更大矩阵限制到 $S$ 后相同，
在含 $x,y$ 的任一有限集合中定义 $K(x,y)$；共同并集给选择无关性。
每个有限二次型在某一 $G_S$ 中非负。
如果只供应未知矩阵元的闭约束，则固定 $K(x,x)=d_x<\infty$，
将 $K(x,y)$ 限于紧圆盘 $|K(x,y)|\le\sqrt{d_xd_y}$。
这些圆盘的乘积紧致；Hermitian 性、固定对角、每个有限 PSD 条件及其余闭约束均为闭集。
每有限组约束同时可满足正是有限交性质，乘积紧致性给全局解。
此步骤是标准紧致性在当前核变量上的应用，不保证有效搜索、可达制备或唯一解。
若去掉紧致性，同一 $m\in\mathbb N$ 的全部约束 $m\ge n$ 给有限可满足而全体无解。

裸图不能决定核：$n>1$ 个标签上的 $K_1(x,y)=1$ 和 $K_2(x,y)=\delta_{xy}$
都为正核，而最小维数分别为一与 $n$。
逐边也不足：对角为一、三个非对角元均为 $-3/4$ 的三阶实矩阵，
每个两点子矩阵谱为 $1/4,7/4$，整体在 $(1,1,1)$ 上却有特征值 $-1/2$。
这些反例限定了把关系图解释为 Hilbert 载体时必须保留的条件。证毕。

在上述应用中，若 $m$ 阶 Hermitian 候选 $G$ 与 $G_0$ 每个矩阵元误差至多 $\varepsilon$，则

$$
\|G-G_0\|_{\rm op}\le\|G-G_0\|_{\rm HS}\le m\varepsilon.
$$

Rayleigh 商给：$\lambda_{\min}(G_0)>m\varepsilon$ 时全部候选正定；
$\lambda_{\min}(G_0)<-m\varepsilon$ 时全部候选非 PSD。
跨过该边界的候选集尚未由此证书判定，不能以单条关系的准确性替代全矩阵证书。

**命题 15.3（有向静态表示及所选表示的边界）。**
定义 15.1 的有向等距系统具有 $H_\infty$ 和等距 $j_C$，满足

$$
j_DV_{DC}=j_C,\qquad
\overline{\bigcup_Cj_CH_C}=H_\infty,
$$

并在保持这些嵌入的酉同构下唯一。
相容局部代数态在
$\mathcal A=\overline{\bigcup_C\mathcal A_C}^{\|\cdot\|}$ 上有唯一全局态及其循环 GNS 表示；
局部 GNS 空间的有向等距极限是该全局 GNS 空间。
相容局部态不必是任意预选 $H_\infty$ 上的正常态。

证明。
第一项把本卷定理 11.2 的序列指标改为 $\mathcal I(C_*)$，
其证明唯一需要的共同后继由有向性供应。
精确地，令 $(C,x)\sim(D,y)$ 当某个共同上界 $F$ 满足 $V_{FC}x=V_{FD}y$。
若需组合两个见证上界，再取其共同上界；接续一致性和等距性给等价关系。
加法先送到共同上界，内积定义为

$$
\langle[C,x],[D,y]\rangle
 =\langle V_{FC}x,V_{FD}y\rangle_{H_F}.
$$

任意两个上界可再向前比较，故值与选择无关。
这给内积空间；完备化后 $j_Cx=[C,x]$，其像有向且并稠密。
另一实现上 $j_Cx\mapsto j'_Cx$ 是稠密保内积映射，唯一延拓为满酉。
若全部 $H_C$ 均为同一有限维 $d$，运输皆满酉，极限仍为 $d$ 维；
有限切面维数无界时极限无穷维。增加节点数不独自增加独立维数。

第二项消费[静态相融纤维 §12](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)的局部态/GNS 构造。
在当前有向族上，任何有限代数运算都可放入一个共同上界，
因此相同证明在并集上定义良好的 $\omega(a)=\omega_C(a)$。
正泛函不等式给 $|\omega(a)|^2\le\omega(a^\dagger a)\le\|a\|^2$，
故唯一连续延拓；在并集中逼近任一正元的平方根证明延拓仍正，且 $\omega(I)=1$。
令 $N=\{a:\omega(a^\dagger a)=0\}$，取

$$
\langle[a],[b]\rangle=\omega(a^\dagger b),\qquad
\pi(c)[a]=[ca],\qquad \Omega_\omega=[I].
$$

$\omega(a^\dagger c^\dagger ca)\le\|c\|^2\omega(a^\dagger a)$
使 $N$ 为左理想且 $\pi(c)$ 有界；完备化得循环表示
$\omega(a)=\langle\Omega_\omega,\pi(a)\Omega_\omega\rangle$。
局部商向量按 $[a]_C\mapsto[a]_D$ 保范数，并满足复合；
代数并集在全局 GNS 范数中稠密，故第一项的唯一性识别两种极限。
这里使用标准 GNS 中间构造，参见 [Fewster–Rejzner](https://arxiv.org/abs/1904.04051v2)；
有向 Hilbert 系统的背景亦见 [Morinelli 等 §2.2](https://arxiv.org/abs/2010.11121)。

最后给当前切面应用的所选表示反例。
令 $H_n=(\mathbb C^2)^{\otimes n}$，嵌入 $x\mapsto x\otimes|0\rangle$，极限为 $H_0$。
局部密度 $I_{2^n}/2^n$ 对偏迹相容。
$H_0$ 有以自然数有限子集 $S$ 标记的可数完整正交基，表示有限个一激发。
若存在迹类密度 $D$ 产生这些局部态，令 $P_{S,n}$ 为前 $n$ 位等于 $S$ 的投影，$n\ge\max S$。
有 $|S\rangle\langle S|\le P_{S,n}$，所以

$$
0\le\langle S,DS\rangle\le\operatorname{Tr}(DP_{S,n})=2^{-n}.
$$

令 $n\to\infty$，全部基对角均为零，正迹类性给 $\operatorname{Tr}D=0$，矛盾。
这族局部态在准局部代数上仍有态及自己的 GNS 表示。
例如在单个 $M_d$ 上，$\omega(a)=\operatorname{Tr}(\rho a)$、$\operatorname{rank}\rho=r$ 时，
$[a]\mapsto a\sqrt\rho$ 给 GNS 维数 $dr$，并非一概等于原粒子的 $d$。
交换代数也有 Hilbert 表示，故存在该载体不单独选出非交换量子论。证毕。

$\Psi\in H_\infty$ 的 $j_C^\dagger\Psi$ 未必单位范数；
一般极限向量不自动在每个粗切面给归一纯态。
同样，将所有切面另作正交标签而写无穷等权和
$\sum_C|C\rangle\otimes\psi_C$ 通常不归一化，
它不同于在归纳极限中识别同一个向量。粗读出必须另给限制映射。

## 16. 静态接续的误差、回路与 Gram 相位条件

**定义 16.1（同一过程的合法比较）。**
固定相容配置中的基本扩展给同类型全定义运输。
同一有限区域的两种线性扩张只有在属于同一实验的重新展开时才比较为同一过程。
不同干预可有不同 holonomy。部分运输另须保留实际域、失败记录、完整标签及资源合同。

全定义情形直接消费[静态相融纤维 §3](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)
与[无序原子定理 7.2](AURIC_UNORDERED_COMPATIBLE_ATOM_AND_QUANTUM_REPRESENTATION_THEORY.md)：
同端点运输相同当且仅当所有合法交换菱形交换。
证明的对应是有限差集的线性扩张：把目标排序的首元素向左移动，
跨过的元素与它不可比，再对剩余排序归纳；每步恰为合法菱形。
部分域情形消费[图册定理 4.1、命题 4.3](RECURSIVE_RELATIONAL_OBSERVATION_ATLAS_STABLE_CORE_HOLONOMY.md)：
闭路在其实际域为恒等保证图册注入，但严格路线相等还须同域、同完整标签及同后继。
基图连通也不保证每个纤维点均能运到根图册，不能据此宣称一个满的共同坐标系。

**命题 16.2（有向切面应用中的近似接续界）。**
所有运输为算子范数至多一的线性映射。
若路径 $p,q$ 经 $m$ 次合法菱形替换连接，第 $j$ 次局部复合差至多 $\delta_j$，则

$$
\|V_p-V_q\|_{\rm op}\le\sum_{j=1}^m\delta_j.
$$

若端点复合均为等距，则对任意有限旁观参考、任意联合密度输入及效果，预测差至多
$\min\{1,2\sum_j\delta_j\}$。
对单位向量的相邻 Gram 关系

$$
v_{L+1}=v_1,\qquad
\langle v_j,v_{j+1}\rangle=r_ju_j,
\quad 0<r_j\le1,\quad |u_j|=1,
$$

还必须有

$$
\left|1-\prod_{j=1}^Lu_j\right|
 \le\sum_{j=1}^L\sqrt{2(1-r_j)}.
$$

证明。
一次替换为 $LAR-LBR$，左右收缩给差至多 $\delta_j$；
沿替换链作伸缩相消即得第一式。
与任意参考张量单位不改算子范数。
设端点等距为 $V,W$，$\|V-W\|\le\delta$。
对联合密度 $\rho$ 展开

$$
V\rho V^\dagger-W\rho W^\dagger
 =(V-W)\rho V^\dagger+W\rho(V-W)^\dagger,
$$

其中已包含参考单位，迹范数至多 $2\delta$，与效果配对不超过此值；
概率差另外至多一。这是所有联合输入的界，而非在有限样本上比较。

第一变量共轭线性的约定给
$\|v_j-\overline{u_j}v_{j+1}\|^2=2(1-r_j)$。
第 $j$ 项乘以前 $j-1$ 个 $\overline{u_k}$ 后相加，左侧向量和为
$(1-\overline{\prod_ju_j})v_1$，三角不等式给第二式。
故全部 $r_j=1$ 时相位乘积必须为一。
在四环加一叶骨架上，若另将环边解释为单位模 Gram 关系，
三条相位为 $+1$、一条为 $-1$，每条边各自 PSD，整体却不可实现。
若各 $r_j\ge1-\varepsilon$，则 $2\le4\sqrt{2\varepsilon}$，必要条件为 $\varepsilon\ge1/8$。
这是该核模型的必要界，不声称最优；实际耦合强度不自动等于 Gram 内积。证毕。

对连通转换图，若边给酉 $U_{dc}$、逆边给 $U_{cd}=U_{dc}^\dagger$，
存在 $U_{dc}=W_dW_c^\dagger$ 的共同参考表示当且仅当每条闭路乘积为单位。
这一步是标准平坦运输中间事实：必要性逐因子消去；
充分性固定根点，沿路径定义 $W_c$，闭路恒等使选择无关。
若仅比较射线，可以忽略单一路径的整体相位；
但供应两路线的相干控制时，本卷 §6 的干涉式

$$
p_+=\frac{1+\Re\langle U_p\psi,U_q\psi\rangle}{2}
$$

使相对相位可测。因此非平凡 holonomy 可描述不同干预，不是量子理论矛盾。
局部误差可随区域增长；任意尺度的一致精度还需可求和误差或独立保护机制。
近似菱形本身没有构造精确归纳极限。

## 17. 完整因果单元、内部观察者与返回记忆

**定义 17.1（完整仪器和内部访问结构）。**
完整因果单元包括全部结果、失败、拒绝及停止端口。
观察者由图内可访问代数 $\mathcal A_O$、其中可稳定区分的交换记录子代数
$\mathcal D_O$，以及依记录选择许可测试的规则组成。
其记忆、程序、相位参考和未来再耦合的环境均占据图内端口。
身份由访问及接续角色确定，不要求预选一个几何点。

若 $\mathcal D_O$ 由完整正交记录投影 $R_a$ 生成，联合态为 $\varrho_{SO}$，则

$$
\begin{aligned}
p_a&=\operatorname{Tr}[(I\otimes R_a)\varrho_{SO}],\\
\rho_{S|a}&=
\frac{\operatorname{Tr}_O[(I\otimes R_a)\varrho_{SO}(I\otimes R_a)]}{p_a}
\quad(p_a>0).
\end{aligned}
$$

这在已选迹/Born 表示内给同一静态关系的条件限制；它不独立证明 Born 律。
投影或联合态未知时，把两者共同放入 $\Omega_h$ 后逐模型计算。

**支撑推导 17.2（核到仪器的完整接口及粗粒化条件）。**
设输入核 $K$、各结果核 $K_a$ 及接续 $r_a$ 满足

$$
K(x,y)=\sum_aK_a(r_ax,r_ay)
\quad\text{对全部输入 }x,y,
$$

结果有限。则每个接续在最小表示上诱导收缩线性 $M_a$，
$\sum_aM_a^\dagger M_a=I$，完整记录接续 $V\psi=\bigoplus_aM_a\psi$ 为等距。
有限维并供应到共同输出空间的等距识别后，$\mathcal I_a(X)=M_aXM_a^\dagger$ 为完整仪器。
有限无环网络在保留全部返回记忆和指定辅助输入后，对合并节点及遗忘内部结果封闭。
删除返回关联后，当前可见态一般不再闭合。

证明。
前半项精确应用本卷定理 6.2，阶段标签取当前和下一完整边界；
若各输出空间不同，先用其正交直和，再经给定等距识别。
对任意有限 $u=\sum_xc_x[x]$，全交叉守恒给

$$
\sum_a\left\|\sum_xc_x\eta_a(r_ax)\right\|^2=\|u\|_K^2.
$$

零关系逐分支消失且每一项范数不增，故线性延拓下降到商并唯一连续延拓到完成。
保范数及极化给完整关系；每个参考放大由 $M_a\otimes I$ 共轭而保持正性，求和保迹。
只检验单标签不够：两个正交单位输入都送到同一单位输出虽然逐个保范数，
却不可能为等距，因为它破坏交叉内积。

一般粗分支应为 $\mathcal I_a(X)=\sum_\alpha K_{a\alpha}XK_{a\alpha}^\dagger$。
上述单算子形式应用到细分标签 $(a,\alpha)$；遗忘 $\alpha$ 给实际粗分支。
细分的存在不授权访问环境。相干记录提升的交叉块另需供应：
即使每个普通分支相同，$\sum_ae^{i\phi_a}M_a\psi\otimes|a\rangle$
也可因相位不同而在后续相干测试中给不同结果，参见本卷命题 6.5。
反馈的完整相干提升同样须实际供应，不能从经典策略独自推出。

在有限 DAG 中，局部 Kraus 的乘积、张量积和内部标签求和仍给 CP 形式；
按逆拓扑次序消去完备关系给总归一。
独立辅助态须按原共同来源供应；相关环境不可重置成独立输入而仍称同一模型。
具体反例是未知系统态 $x$ 与环境 $|0\rangle\langle0|$ 交换：
当前系统恒为 $|0\rangle\langle0|$，环境携带 $x$；再次交换系统恢复 $x$。
不存在只从同一当前系统态输出全部不同 $x$ 的通道。
故类型封闭不等于固定五维记忆足够，也不等于最少串行门数不变。证毕。

**定义 17.3（点边识别的类型约束）。**
消费本卷 §7 的 Choi–Kraus 对应时，有限维算子 $A:H_{\rm in}\to H_{\rm out}$
对应向量

$$
|A\rangle\!\rangle=\sum_jA|e_j\rangle\otimes|\overline{e_j}\rangle
\in H_{\rm out}\otimes\overline{H_{\rm in}},
\qquad
\langle\!\langle A|B\rangle\!\rangle=\operatorname{Tr}(A^\dagger B).
$$

共轭输入空间使该对象在同时改变基时不变。
未归一 Choi 算子

$$
J_\Phi=\sum_{ij}\Phi(|e_i\rangle\langle e_j|)
 \otimes|\bar e_i\rangle\langle\bar e_j|
$$

表示确定通道当且仅当 $J_\Phi\ge0$、$\operatorname{Tr}_{\rm out}J_\Phi=I$。
具体地，$J=\sum_\mu|A_\mu\rangle\!\rangle\langle\!\langle A_\mu|$
的谱分解逆向量化给 Kraus 族，矩阵单位比较给 $\Phi(X)=\sum_\mu A_\mu XA_\mu^\dagger$；
输入坐标中的输出偏迹是 $(\sum_\mu A_\mu^\dagger A_\mu)^T$。
这是 [Watrous Theorems 2.22、2.26](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)的准确类型。
任意双系统态不一定有固定输入边际 $I/d_{\rm in}$，因而不一定表示确定门。
纯 Choi 加保迹给单 Kraus 等距；同维时才是酉。
“点还是边未知”可指这些候选类型的识别，不能删除其边际约束。

完整等距还保持任意两态的迹范数距离，包括任意旁观参考：
差算子在其像上与输入差算子酉等价，在正交补上为零，非零奇异值不变。
所以完整切面运输若固定一个平衡态，不能严格吸引其他完整态到该态。
恢复平衡必须标明约化、受限效果或条件分支。
封闭固定酉轨道若在迹范数收敛，则相邻态距离恒定又趋零，轨道从起点就已固定；
这精确消费本卷命题 11.9，而不把内部记录增长当成耗散的来源。

## 18. 五模式平衡包在静态切面中的精确供应对应

**定义 18.1（实际物理基、码和擦标签边界）。**
本节是 §19 条件记录应用的供应接口。
取[预测波 §17.1](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md)的物理正交基
$(e_0,\ldots,e_4)$，令

$$
u=\frac{e_0+e_3}{\sqrt2},\qquad
v=\frac{e_1+e_4}{\sqrt2},\qquad z=e_2,\qquad
B=(u,v,z):\mathbb C^3\to\mathbb C^5.
$$

$B^\dagger B=I_3$，$R=\operatorname{Ran}B$。
定义同一实际来源的算子

$$
\begin{aligned}
K_0&=|u\rangle\langle e_0|+|v\rangle\langle e_2|/\sqrt2+|z\rangle\langle e_4|,\\
K_1&=|u\rangle\langle e_1|+|v\rangle\langle e_2|/\sqrt2+|z\rangle\langle e_3|,\\
A_0&=\cos\theta K_0+i\sin\theta K_1,\qquad
A_1=i\sin\theta K_0+\cos\theta K_1,\qquad\theta\in\mathbb R,\\
\mathcal G(X)&=K_0XK_0^\dagger+K_1XK_1^\dagger
             =A_0XA_0^\dagger+A_1XA_1^\dagger.
\end{aligned}
$$

每个 $\theta$ 是固定已标定参数；全实参数公式不授予任意角控制。
$K_0^\dagger K_0=\operatorname{diag}(1,0,1/2,0,1)$，
$K_1^\dagger K_1=\operatorname{diag}(0,1,1/2,1,0)$，故和为单位。
系数矩阵 $\left(\begin{smallmatrix}\cos\theta&i\sin\theta\\i\sin\theta&\cos\theta\end{smallmatrix}\right)$
酉，给全 $M_5(\mathbb C)$ 上的通道恒等；线性恒等张量任意参考仍成立。
所有输出均在 $R$，但一般输入不承诺在码内。

码内令

$$
U=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\qquad
W=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix},\qquad
P_\pm=(I_3\pm W)/2,
$$

则 $K_0B=BU/\sqrt2$、$K_1B=BUW/\sqrt2$，故

$$
\mathcal T(X):=B^\dagger\mathcal G(BXB^\dagger)B
 =\tfrac12(UXU^\dagger+UWXW^\dagger U^\dagger)
 =\operatorname{Ad}_U(P_+XP_++P_-XP_-).
$$

深度 $n$ 表示所选有限静态区域内同类原子的复合数。
每次擦环境的模型使用新供应的独立环境，不将保留相关环境的模型偷换成这条齐次通道。

**定义 18.2（平衡和全输入极限的供应公式）。**
令

$$
\begin{gathered}
\xi=(1,1,1)^T/\sqrt3,\qquad P=|\xi\rangle\langle\xi|,\quad Q=I_3-P,\\
\tau_p=pP+(1-p)Q/2,\qquad\widehat\tau_p=B\tau_pB^\dagger,\quad0\le p\le1,\\
\chi=B\xi,\qquad d=(e_0-e_1-e_3+e_4)/2,\qquad
J=|\chi\rangle\langle\chi|+\tfrac23|d\rangle\langle d|.
\end{gathered}
$$

$d\perp R$，$\chi,d$ 为正交单位向量，故 $0\le J\le I_5$。
下表将[五窗口量子记忆 §§17–19](AURIC_FIB_FIVE_WINDOW_QUANTUM_MEMORY.md)的供应符号加下标 FW，
使其与当前码坐标不混淆。

| 供应符号/条目 | 当前对象 | 假设及精确对应 |
| --- | --- | --- |
| 定义 17.2 的 $\Phi_\circ,K_j^\circ,R$ | $\mathcal G,K_j,\operatorname{Ran}B$ | 同一物理基、同一 $u,v,z$，参数为 $\eta=r=1/2$ |
| 定理 18.1 的 $s,P_{\rm FW},M_{\rm FW}$ | $\chi,BPB^\dagger,BQB^\dagger/2$ | $s=B\xi$，$P_R=BB^\dagger$ |
| 定理 18.1 的 $\rho_t$ | $\widehat\tau_p$ | $t=p\in[0,1]$，包括两个端点 |
| 定理 18.3 的 $h_0,h_1,E_{\rm FW}$ | $K_0^\dagger\chi,K_1^\dagger\chi,J$ | $h_0=(e_0+e_4)/\sqrt3+e_2/\sqrt6$，$h_1=(e_1+e_3)/\sqrt3+e_2/\sqrt6$ |
| 定理 19.1 的限制 $F$ | $\mathcal T$ | 由 $X\mapsto BXB^\dagger$ 共轭识别整个 $M_3$ |
| 定理 19.2 的 $\mathcal T_{\rm FW}$ | $\mathcal E_G$ | $\mathcal E_G=(\mathcal G^2+2\mathcal G^3)/3$ |

这些是实际算子相同，不仅是谱相似。
供应的固定空间为 $\operatorname{Fix}\mathcal T=\operatorname{span}_{\mathbb C}\{P,Q\}$，
所有固定密度恰为 $\tau_p$，全五维固定密度恰为 $\widehat\tau_p$。
其机制是等 Hilbert–Schmidt 范数的两个酉共轭平均达到原范数时，两项都等于原矩阵；
$U,UW$ 生成三坐标置换群，交换子只有共同对角及共同非对角两类。
所以不是唯一平衡，而是由隐藏扇区权重 $p$ 参数化的平衡段。

供应定理 19.1 在整个复算子空间给

$$
\begin{aligned}
\operatorname{spec}\mathcal T&=\{1\ [2],-1/2\ [3],0\ [4]\},\\
\mathcal T(\mathcal T-I)(\mathcal T+I/2)&=0,\\
\chi_{\mathcal G}(t)&=t^{20}(t-1)^2(t+1/2)^3,\\
\mathcal G^2(\mathcal G-I)(\mathcal G+I/2)&=0.
\end{aligned}
$$

限制多项式无重根，故 $\mathcal T$ 可对角化；全五维多项式保留零模的二阶瞬态，
不据此断言 $\mathcal G$ 可对角化。
码内的谱投影及全部幂为

$$
\begin{gathered}
\mathcal E(X)=\operatorname{Tr}(PX)P+\tfrac12\operatorname{Tr}(QX)Q,\\
2\mathcal T^2+\mathcal T=3\mathcal E,\qquad
\mathcal T\mathcal E=\mathcal E\mathcal T=\mathcal E,\\
\mathcal T^n=\mathcal E+(-1/2)^{n-1}(\mathcal T-\mathcal E)\quad(n\ge1).
\end{gathered}
$$

这是供应限制多项式的直接代入：常数、一和负半三个特征空间上逐一计算。
置 $\mathcal C(X)=B^\dagger\mathcal G(X)B$，则
$\mathcal G^n=\operatorname{Ad}_B\mathcal T^{n-1}\mathcal C$，
$\mathcal C^\dagger(P)=J$，从而供应极限在全部复输入上为

$$
\begin{aligned}
\mathcal E_G(X)
 &=\operatorname{Tr}(JX)|\chi\rangle\langle\chi|
 +\frac{\operatorname{Tr}X-\operatorname{Tr}(JX)}2
       (BB^\dagger-|\chi\rangle\langle\chi|),\\
\mathcal E_G^2&=\mathcal E_G,\qquad
\mathcal G\mathcal E_G=\mathcal E_G\mathcal G=\mathcal E_G,\\
\mathcal G^n-\mathcal E_G
 &=(-1/2)^{n-2}(\mathcal G^2-\mathcal E_G)\quad(n\ge2),\\
\|\mathcal G^n-\mathcal E_G\|_\diamond
 &\le\tfrac43\,2^{-(n-2)}\le2^{3-n}\quad(n\ge2).
\end{aligned}
$$

采用未除二的 diamond 范数：上确界遍历任意有限参考及任意非零复测试矩阵，
不只遍历密度或 Hermitian 输入。
最后一界沿用供应定理 19.2，因为
$\mathcal G^2-\mathcal E_G=\tfrac23(\mathcal G^2-\mathcal G^3)$，
每个 CPTP 通道完全迹范数为一。
因此任意五维密度的极限为 $\widehat\tau_{\operatorname{Tr}(J\rho)}$。
上述完整范数结论并未把一般参考相关态的极限误写成两个边缘的乘积：
对于任意联合正输入 $X_{HZ}$，准确表达式是

$$
(\mathcal E_G\otimes\operatorname{id}_Z)(X_{HZ})
 =|\chi\rangle\langle\chi|\otimes Z_+
   +\frac{BQB^\dagger}{2}\otimes Z_-,
$$

其中

$$
Z_+=\operatorname{Tr}_H[(J\otimes I_Z)X_{HZ}],\qquad
Z_-=\operatorname{Tr}_H[((I_5-J)\otimes I_Z)X_{HZ}].
$$

二者为正，迹之和为 $\operatorname{Tr}X_{HZ}$；它们可保留扇区与参考的经典相关。

这些公式同时给人口盲性：码基 $(u,v,z)$ 上对角恒为 $(1/3,1/3,1/3)$，
非对角恒为 $(3p-1)/6$；原五基人口恒为

$$
(1/6,1/6,1/3,1/6,1/6).
$$

这是供应定理 18.1 的两端态有同一人口以及 $B$ 三列不交叠支撑的直接应用。
两个端点支撑正交，故 $\|\widehat\tau_1-\widehat\tau_0\|_1=2$，
效果 $|\chi\rangle\langle\chi|$ 可完美区分。
指定人口稳定与全态稳定因此不同；信息完备且已标定的全部效果不具有这个盲性。

## 19. 条件平衡、返回仪器和无界记录树

**定义 19.1（原生标签、额外读口和返回资源）。**
原生记录仪器是定义 18.1 的 $A_0,A_1$。
另供应环境相干读出时，可改读

$$
L_+=(K_0+K_1)/\sqrt2,\qquad
L_-=(K_0-K_1)/\sqrt2,\qquad L_\pm B=BU P_\pm.
$$

二者求和的通道仍为 $\mathcal G$。
若用 $K_j$ 的环境基 $f_j$，这对应 Hadamard 基；
若原标定基产生的是 $A_j$，须先按该固定 $\theta$ 校准到同一环境比较，不能把两个基静默等同。
只给黑盒 $\mathcal G$ 不供应环境访问。

[环境记录定理 2.2](AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md)给实际共同等距扩张：
$e_0\mapsto u\otimes f_0$、$e_1\mapsto u\otimes f_1$、
$e_2\mapsto v\otimes(f_0+f_1)/\sqrt2$、
$e_3\mapsto z\otimes f_1$、$e_4\mapsto z\otimes f_0$。
这五个像正交，故可补成 $\mathbb C^5\otimes\mathbb C^2$ 上的酉；
它说明读口改变的是同一完整扩张的条件分支。

在另一个明确扩大的菜单中，[同源定理 20.1](AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md)
还直接实现这套 $L$ 仪器：

$$
F=K_0^\dagger K_1+K_1^\dagger K_0,
\qquad H_\pm=(I_5\pm F)/2,
\qquad L_\pm^\dagger L_\pm=H_\pm.
$$

实际 $F$ 交换 $e_0,e_1$，交换 $e_3,e_4$，固定 $e_2$，故 $F^2=I$，
$H_+,H_-$ 为秩三、二的完整 PVM。
$L_\pm$ 在各 $H_\pm$ 像上等距，补其正交基可得全五维酉 $\widetilde U_\pm$，
$L_\pm=\widetilde U_\pm H_\pm$。
先测该 PVM 再条件施酉给同一带标签仪器；遗忘标签即供应定理中的平均通道。
这一步使用任意五级酉及该 PVM，未证明受限等待、完整秩一模式读及 Stop 菜单可实现它。

再另供应返回通道 $\mathcal E_G$，定义

$$
\mathcal J_\pm=\mathcal E_G\circ\operatorname{Ad}_{L_\pm}.
$$

$\mathcal J_++\mathcal J_-=\mathcal E_G\mathcal G=\mathcal E_G$，所以这是一套完整仪器。
$\mathcal E_G=(\mathcal G^2+2\mathcal G^3)/3$ 是 §18 的既有恒等；
若菜单实际允许权重 $1/3,2/3$ 的输入无关经典选择和相应复合，才给一个有限随机深度实现。
测量 $J,I-J$ 再制备两个固定端点是另一种实现合同。
恒等式本身不把这些资源加入原菜单，也不把 $\mathcal E_G$ 等同于一发 $\mathcal G$。
返回通道与 §21 的扰动复位 $\mathcal R_0$ 亦不同。

**定理 19.2（同一静态网络的平均平衡、条件破缺与返回记录律）。**
在 §§14–18 的有类型复表示中，完整记录保留在切面内，
对任意 $\theta\in\mathbb R$、$p\in[0,1]$ 有

$$
A_j\widehat\tau_pA_j^\dagger=\tfrac12\widehat\tau_p\quad(j=0,1).
$$

码内任意归一联合输入与任意有限旁观参考的原生标签字 $h$，长度 $n$ 的概率为 $2^{-n}$。
换成已供应的 $L$ 读口时，平衡输入的概率及正概率条件输出满足

$$
q_+=(1+p)/2,\qquad q_-=(1-p)/2,
$$

并且 $0<p<1$ 时两个条件输出 $\sigma_\pm$ 都非固定，而

$$
\mathcal G^n(\sigma_+)\longrightarrow\widehat\tau_{2p/(1+p)},
\qquad
\mathcal G^n(\sigma_-)\longrightarrow\widehat\tau_0.
$$

使用定义 19.1 的返回仪器后，每个深度都有完整柱律

$$
\begin{aligned}
\Pr(h)&=
\begin{cases}
p+(1-p)2^{-n},&h=+^n,\\
(1-p)2^{-n},&h\text{ 含 }-,
\end{cases}\\
p_{+^n}&=\frac{2^np}{1-p+2^np},\qquad
p_h=0\quad(h\text{ 含 }-,\ \Pr(h)>0).
\end{aligned}
$$

其唯一无限记录律为
$p\delta_{+^\infty}+(1-p)\operatorname{Bernoulli}(1/2)^{\otimes\mathbb N}$；
特别地全 $+$ 射线概率为 $p$。
零概率分支、端点及无穷射线分别按下述证明解释。

证明。
原生部分的供应为[环境记录定理 2.2](AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md)
和[尖锐任务保留环境记忆定义 1.1](RECURSIVE_RELATIONAL_OBSERVATION_SHARP_TASK_RETAINED_ENVIRONMENT_MEMORY.md)。
当前参数对应为 $U_0=U$、$U_1=UW$，且

$$
A_0B=\tfrac1{\sqrt2}BUe^{i\theta W},\qquad
A_1B=\tfrac1{\sqrt2}BUWe^{i\theta W}.
$$

因为 $W^2=I$，这对所有实 $\theta$ 都是两个酉分支乘 $1/\sqrt2$。
$\tau_p$ 与 $U,W$ 交换，故分支等于 $\widehat\tau_p/2$。
一般码内输入每次标签概率 $1/2$、后继仍在码内；
与参考张量单位后分支效应仍为 $I_3/2\otimes I_Z$。
长度 $n$ 的归一酉乘积前系数为 $2^{-n/2}$，给全部有限字概率 $2^{-n}$；
这里没有对未知码态或参考作现实数、纯态或无关联限制。
原生标签不含关于该码输入的信息；终端效果或相干环境访问改变了测试菜单。

条件破缺是把供应通道固定族接到新增读口的计算。
在 $Q$ 上取单位基

$$
e=(1,1,-2)^T/\sqrt6,\qquad f=(1,-1,0)^T/\sqrt2.
$$

$P_+=P+|e\rangle\langle e|$，$P_-=|f\rangle\langle f|$。
写 $b=(1-p)/2$，对所有 $p$ 直接得到

$$
\begin{aligned}
L_+\widehat\tau_pL_+^\dagger
 &=B[pP+b|Ue\rangle\langle Ue|]B^\dagger,\\
L_-\widehat\tau_pL_-^\dagger
 &=bB|Uf\rangle\langle Uf|B^\dagger.
\end{aligned}
$$

取迹给 $q_\pm$。$0<p<1$ 时，两条件态的 $Q$ 块非零且秩一，
而 §18 的固定态中非零 $Q$ 块均为二维均匀块，故两者均非固定。
码内 $J$ 压缩为 $P$，两条件输出的保护权重分别为 $p/q_+=2p/(1+p)$、零。
将 §18 全复输入幂公式作用到它们即得两极限及相同的误差界。
未选分支时 $\sum_\pm L_\pm\widehat\tau_pL_\pm^\dagger=\mathcal G(\widehat\tau_p)=\widehat\tau_p$，
最终参数也满足 $q_+\,2p/(1+p)+q_-\,0=p$。
$p=1$ 只有正分支且保持纯固定态，负分支无条件态；
$p=0$ 两分支都先离开固定态，随后返回同一个 $\widehat\tau_0$。
例如 $p=1/3$ 时两概率为 $2/3,1/3$，返回参数为 $1/2,0$。

对返回仪器，每个正概率分支已精确在平衡族内。
它在两端点上的未归一作用为

$$
\begin{array}{c|cc}
 &\widehat\tau_1&\widehat\tau_0\\\hline
\mathcal J_+&\widehat\tau_1&\widehat\tau_0/2\\
\mathcal J_-&0&\widehat\tau_0/2
\end{array}
$$

故对任意有限 $n$，若字全为正，未归一态为
$p\widehat\tau_1+(1-p)2^{-n}\widehat\tau_0$；
含负的字为 $(1-p)2^{-n}\widehat\tau_0$。
取迹及归一给全部公式，亦验证父子柱质量一致。
有限字母积空间的标准柱扩张给唯一概率律；显示的混合测度在每个柱上有同一值，
所以就是该扩张。公平积测度的全正无穷射线概率为零，
也可直接由 $\Pr(+^n)\downarrow p$ 得射线概率。
对 $p=0$，所有有限全正字的后验仍为零，不能把无定义的无穷极限式强写成一；
$p=1$ 时只存在全正字，后验恒一；$0<p<1$ 时全正后验趋一，任一负后恒零。
树的无界深度是这一相容记录律，并非有限五维端口保存全部无穷记录。
不同结果字在事件结构中属于互斥配置，不能取它们的并作为同一实际配置。
§15 的有向极限限于每个相容扇区；完整记录的相干提升则由另行供应的等距定义，
不从这些互斥配置的集合并推出。

任意参考的完整版本也由同一端点作用给出。
对返回后的一般联合态写成
$\widehat\tau_1\otimes Z_++\widehat\tau_0\otimes Z_-$，其中 $Z_\pm\ge0$、迹和为一。
全正字的未归一联合输出为

$$
\widehat\tau_1\otimes Z_+ +2^{-n}\widehat\tau_0\otimes Z_-,
$$

其他字为 $2^{-n}\widehat\tau_0\otimes Z_-$。
这证明返回记录计算保留参考相关；对任意初始联合态，先施 §18 的
$\mathcal E_G\otimes\operatorname{id}$ 即得到这些 $Z_\pm$。
标量公式只是其取迹后的特例。
柱树有一个经典隐藏扇区表示，已使用既定仪器及迹概率，故不反向证明 Born 律。证毕。

**命题 19.3（有限网络的返回近似及后选择边界）。**
把返回通道替换为 $\mathcal G^N$，$N\ge2$，并保留相同 $L$ 标签。
对任意 $m$ 块固定有限网络，包括依已获记录的许可控制及任意有限旁观参考，
完整未后选择输出的通道误差至多

$$
\min\{2,m\delta_N\},\qquad
\delta_N=\tfrac43\,2^{-(N-2)}\le2^{3-N}.
$$

它不自动给整棵无限树的同一统一界，也不给每条稀有条件分支同一界。

证明。
令带标签通道
$\Lambda_N(X)=\sum_{a=\pm}(\mathcal G^N\circ\operatorname{Ad}_{L_a})(X)\otimes|a\rangle\langle a|$，
$\Lambda_\infty$ 将 $\mathcal G^N$ 换成 $\mathcal E_G$。
二者是先做同一完整 $L$ 仪器，再在系统上做两个待比较的返回通道。
§18 的 diamond 界与复合收缩给 $\|\Lambda_N-\Lambda_\infty\|_\diamond\le\delta_N$。
按块逐个替换，各前后文都是保留记忆和记录的 CPTP 映射；
反馈在正交经典记录块上受控，仍为同一 CPTP 上下文。
伸缩相消给 $m\delta_N$，两通道距离另至多二。
此论证遍历全部复测试矩阵及所有有限参考，不以抽样替代。

若某事件的理想和近似未归一分支为 $A,B\ge0$、迹为 $p,q$，
完整误差 $\delta$ 给 $\|A-B\|_1\le\delta$、$|p-q|\le\delta$。
当 $p>\delta$ 时 $q>0$，而

$$
\left\|\frac A p-\frac B q\right\|_1
\le\frac{\|A-B\|_1+|p-q|}{p}\le\frac{2\delta}{p}.
$$

所以稀有事件的归一化会放大误差，零概率事件不能这样比较。
固定 $N$ 而令 $m$ 无界，上界不趋零；
若另安排深度相关精度并证明全路误差可求和，才有相应统一控制。
准确返回仪器仍有定理 19.2 的无限柱律，不将有限近似误差与其混同。证毕。

## 20. 端口最小性与静态量子重建的不同合同

**定义 20.1（双设置端口合同的引用实例）。**
这里的五维等待模型按[静态相融纤维定义 1.4–1.5、§§10–11](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)定型，
不与定义 18.1 的仪器共享未声明控制。
其物理基为 $(e_N,e_2,e_3,e_5,e_{25})$，实际生成元及被动实帧为

$$
\mathsf K=\begin{pmatrix}
0&1&1&1&0\\1&0&0&0&1\\1&0&0&0&0\\1&0&0&0&1\\0&1&0&1&0
\end{pmatrix},\quad
D=\operatorname{diag}(1,i,i,i,1),\quad A=-iD^\dagger\mathsf K D,\quad O(t)=e^{tA}.
$$

$A$ 是实反对称矩阵；模式 $N$ 为单位态，既非零向量也非停止结果。
两设置为 $Q_s(t)=O(t)^T|e_s\rangle\langle e_s|O(t)$，$t=0,2/3$。
$t$ 是此模型的等待参数，未指定为全图时钟或秒。
共同编码/解码在设置晚选前固定，且

$$
\operatorname{Enc}:M_5\to\bigoplus_{f\in F}M_q,\qquad
\operatorname{Dec}:\bigoplus_{f\in F}M_q\to M_5,\qquad T=\operatorname{Dec}\operatorname{Enc}.
$$

$F$ 任意有限、可有输入相关分布，每块解码在整个 $M_q$ 上 CPTP。
所有输入相关量子信息都通过端口；无副本、预共享纠缠或量子旁路，
标记不另送给解码后的晚选测试。输入遍历全部复密度，

$$
e_{\rm two}(T)=\sup_\rho\max_{t=0,2/3}
\operatorname{TV}(p_t(\rho),p_t(T\rho)),\qquad
\varepsilon_{\rm two}(q)=\inf_Te_{\rm two}(T).
$$

供应定理 2.1 在该完全相同的参数、输入、效果、端口和误差约定下给

$$
T\text{ 精确保留两设置}\Longrightarrow T=\operatorname{id}_5,
\qquad q_{\min}=5,
\qquad\varepsilon_{\rm two}(q)\ge(5-q)/102,
\qquad\varepsilon_{\rm two}(5)=0.
$$

这是既有结果的引用应用，不是由 §19 的条件破缺推出的新维数定理。
其有限有理证书为 $v=O(2/3)^Te_N$ 的全部坐标满足 $|v_j|>9/25$，
故 $\mu=\min_j|v_j|^2>1/8$。
原证书取 $M=2A/3$、$S_{12}=\sum_{k=0}^{12}M^k/k!$，
$\|e^M-S_{12}\|_\infty\le(7/6)2^{13}/13!<64/6081075$，
$S_{12}$ 的 $N$ 行为

$$
\left(\frac{107738440637}{248594813775},
\frac{490347766}{1104865839},
\frac{4899328858}{9207215325},
\frac{490347766}{1104865839},
-\frac{91371050044}{248594813775}\right).
$$

其绝对值均大于 $367/1000$，减去尾界仍大于 $9/25$。
四个基探针加 $v$ 张成且非正交图连通，供应 §10 的 Mayer–Knill 无扰动步骤强制 $T=I$。
近似部分对任意复 Kraus 矩阵 $C$ 定义

$$
L_v(C)=\sum_{j=1}^{5}(\|Ce_j\|^2-|\langle e_j,Ce_j\rangle|^2)
 +\|Cv\|^2-|\langle v,Cv\rangle|^2,
$$

其中 $e_j$ 枚举该五模式基；供应式 (11.4) 给

$$
L_v(C)\ge\frac\mu{2+\mu}
\left(\|C\|_{\rm HS}^2-\frac{|\operatorname{Tr}C|^2}{5}\right).
$$

通过 $q$ 维块的每个复合 Kraus 秩至多 $q$，故
$|\operatorname{Tr}C|^2\le q\|C\|_{\rm HS}^2$；
对 Kraus 求和并用 TP 得总泄漏至少 $\mu(5-q)/(2+\mu)$。
五个基输入和一个 $v$ 输入的生存率损失各至多 $e_{\rm two}$，
总共六项给 $(5-q)/102$。逐通道的严格界取下确界后仅保留非严格界；$q=5$ 用恒等。
这里准确消费供应全部复输入及 CP 合法性，不将有限探针误称信息完备层析，
也不主张 $q<5$ 的精确 minimax 已知。

单 Kraus 非零 CP 分支的秩一 Choi 使其位于 CP 锥极端射线；
这与端口维数及串行不可分性不同。酉门总能写成 $U=(UW^\dagger)W$。
二维量子位也能在最大混合态上先读计算基得到条件纯态，再作互补基非选择读回最大混合；
因此平均平衡、条件破缺、再平衡本身不强制五维。

**定义 20.2（此静态应用的重建前提）。**
本卷定义 12.1、定理 12.2 仍是完整的条件重建；
在不要求特殊五事件代数的有向切面应用中，将所用前提按接口写成六项。

1. Q1：局部片段、输入输出、结果、失败与停止有共同类型，合法拼接及独立并置已供应。
2. Q2：边界表达式允许复相干线性组合，正核对全部有限复系数成立；
   或供应相容的正交复结构 $J_{\rm c}^2=-I$ 及保持它的运输。
3. Q3：完整结果满足 §17 的全部交叉项守恒；记录、相位参考和返回环境均保留。
4. Q4：独立准备核因子化，复合采用完整复矩阵张量表示；
   同一局部线性映射对每个有限参考及整个联合正锥保持正性。
5. Q5：读出权重非负、归一、对合法效果和可加，且同一效果不依实现上下文改变赋值；
   权重按明确操作规则标定为概率。全效果表示要求整个 $0\le E\le I$ 的域。
6. Q6：同一物理片段的合法再展开保持完整关系；无限系统另满足 §15 的精确相容/完备条件，
   候选模型极限另满足 §21 的紧致闭约束条件。可达性不由数学表示自动供应。

这些是充分合同，不声称独立或最小。
$J_{\rm c}$ 是复结构，与 §18 的五维守恒效果 $J$ 类型不同。
三条实正交轴不单独产生全空间复结构：奇数实维中
$\det(J_{\rm c})^2=\det(-I)=-1$ 不可能。
若在实内积 $g$ 上另给正交 $J_{\rm c}$，规定 $ix=J_{\rm c}x$，则

$$
h(x,y)=g(x,y)+i g(J_{\rm c}x,y)
$$

为第一变量共轭线性的复内积；局部平面还须在交叠及回路相容。
这消费[无序原子 §§5–7](AURIC_UNORDERED_COMPATIBLE_ATOM_AND_QUANTUM_REPRESENTATION_THEORY.md)
及本卷 §§4–7 的现有结构，不从未知性推出复数域。

**支撑推导 20.3（内部切面解释所用的量子规则及条件边界）。**
在定义 20.2 的各项适用域内，§15 的 Hilbert 载体、§17 的完整仪器、§19 的条件记录树，
与本卷条件重建相容；普通概率、相干平方、完全正及酉性分别依赖以下明确中间条件。
它们不由静态裸图唯一推出。

证明。
对于平方权重，消费本卷 §5 及[无序原子定理 6.1](AURIC_UNORDERED_COMPATIBLE_ATOM_AND_QUANTUM_REPRESENTATION_THEORY.md)：
若维数至少二、$W(x)\ge0$ 只依赖范数且正交可加，置 $f(t)=W(\sqrt t\,e)$。
两正交方向给 $f(s+t)=f(s)+f(t)$；非负性给单调，
有理齐次性及两侧有理逼近给 $f(t)=ct$，其中 $c=f(1)$，
即 $W(x)=c\|x\|^2$，包括 $c=0$。
这同时适用于实与复空间，不独自选择复量子论。

对于一般 Born 赋值，消费本卷定理 5.3 的 [Busch 全效果机制](https://arxiv.org/abs/quant-ph/9909073)：
$\mu(I)=1$、$\mu(E)\ge0$、$\mu(E+F)=\mu(E)+\mu(F)$（$E+F\le I$）
在全效果域上先以有理分割及单调性给实齐次性，再对任意正算子按足够大的正倍数延拓。
两种缩放用共同放大比较，故正锥延拓良定义、可加；
写 Hermitian 算子为正负部分给唯一实线性正泛函。
有限维迹对偶得到唯一 $\rho\ge0$、$\operatorname{Tr}\rho=1$，$\mu(E)=\operatorname{Tr}(\rho E)$。
有限受限投影菜单不满足此前提，§19 也不反向证明它。

对于独立复合，要求

$$
K_{AB}((x,y),(x',y'))=K_A(x,x')K_B(y,y')
$$

并要求产品表达式的复线性包稠密。
送生成元到 $\eta_A(x)\otimes\eta_B(y)$ 保内积且张成稠密，
§15 核表示唯一性识别 $H_{AB}=H_A\otimes H_B$。
这是所选独立规则，不是画出两个图块的结果；全部联合态可制备仍是另一项可达性问题。

Q4 在已选复矩阵正锥上的全量词就是完全正定义。
取最大纠缠参考给 Choi PSD，§17 的谱分解给 Kraus 形式。
只给单系统正性不够：转置为正，但在 Bell 态一侧转置给交换算子的一半，
反对称方向的特征值为 $-1/2$。
只验证可分或已制备输入也不能代替全参考正锥合同。
混合制备的更新线性还需本卷定理 7.2 的全密度凸分解相容条件，未由标签计数给出。

完整记录保内积首先给等距。
同有限维 CPTP 映射具有 CPTP 左逆时，按本卷定理 7.5，复合恒等的秩一 Choi
迫使逆 Kraus $B_j$ 与原 Kraus $A_i$ 满足 $B_jA_i=c_{ji}I$。
某 $c_{ji}\ne0$ 使该 $B_j$ 可逆；固定这个 $j$，全部 $A_i$ 均与 $B_j^{-1}$ 成比例。
故原通道为单算子共轭，TP 给 $A^\dagger A=I$，同维时为酉。
保迹或一个态的熵不变不替代此条件。
另供应由内部记录标定的强连续一参数酉群后，Stone 定理才给自伴生成元，
在其定义域得到 Schrödinger 方程；一般切面偏序不等于该参数。

因此 Q1–Q6 接出的各数学层次可共存，但没有省去其前提。
本卷 §§11–12 的共同模型已经给出一套非空实现；
[因果量子历史](https://arxiv.org/abs/hep-th/0302111)、
[一般边界形式](https://arxiv.org/abs/hep-th/0509122)与其[正形式](https://arxiv.org/abs/1212.5571)
提供无单一全局时钟的既有背景，均不由裸图选择全部量子结构。
CDP 的操作重建另用其完整因果性、可区分性、压缩、局部区分、纯条件化及纯化框架，
参见本卷 §12 所引 [CDP](https://arxiv.org/abs/1011.6451)；
内部观察者或递归之名不构成这些量词的证明。证毕。

## 21. 关系扰动、奇异极限与有向候选宽度

**定义 21.1（额外复位扰动的合同）。**
令 $\mathcal R_0(X)=\operatorname{Tr}(X)\widehat\tau_0$，并在全部 CPTP 通道类中取

$$
\mathcal G_\varepsilon=(1-\varepsilon)\mathcal G+\varepsilon\mathcal R_0,
\qquad0<\varepsilon\le1.
$$

这是另加复位资源的关系候选，不宣称受限原生菜单可执行。
它也不承诺保留定义 18.1 原通道的全部输入人口转移律，
因而不同于[五窗口量子记忆 §23](AURIC_FIB_FIVE_WINDOW_QUANTUM_MEMORY.md)的同人口律原始扰动族。
该供应 §23 已证明其自身的唯一忠实平衡及慢模，不能把那套参数或忠实性移植到这里；
当前复位目标 $\widehat\tau_0$ 仅有秩二。

**定理 21.2（静态深度的精确扰动界与不交换极限）。**
定义 21.1 对全部 $n\ge1$、$0<\varepsilon\le1$ 有

$$
\begin{aligned}
\mathcal G_\varepsilon^n
 &=(1-\varepsilon)^n\mathcal G^n
    +[1-(1-\varepsilon)^n]\mathcal R_0,\\
\|\mathcal G_\varepsilon^n-\mathcal G^n\|_\diamond
 &=2[1-(1-\varepsilon)^n]\le2n\varepsilon.
\end{aligned}
$$

每个正 $\varepsilon$ 只有固定密度 $\widehat\tau_0$，
而 $\varepsilon=0$ 的固定密度为整段 $\widehat\tau_p$。
因此

$$
\begin{aligned}
\lim_{\varepsilon\downarrow0}\lim_{n\to\infty}
 \mathcal G_\varepsilon^n(\widehat\tau_1)&=\widehat\tau_0,\\
\lim_{n\to\infty}\lim_{\varepsilon\downarrow0}
 \mathcal G_\varepsilon^n(\widehat\tau_1)&=\widehat\tau_1.
\end{aligned}
$$

证明。
供应 §18 的固定态和 TP 给
$\mathcal G\mathcal R_0=\mathcal R_0\mathcal G=\mathcal R_0^2=\mathcal R_0$。
展开乘积或直接归纳可得第一式，其中 $\varepsilon=1$ 时每个正次幂都是 $\mathcal R_0$。
相减为 $[1-(1-\varepsilon)^n](\mathcal R_0-\mathcal G^n)$，
两个 CPTP 通道的完全迹范数差至多二，给全复输入、全有限参考的上界。
输入 $\widehat\tau_1$ 时两输出为正交支撑的 $\widehat\tau_0,\widehat\tau_1$，达到二，故为等号。
Bernoulli 不等式给最后的 $2n\varepsilon$。
固定正 $\varepsilon$ 时第一项系数趋零，所以所有密度趋向 $\widehat\tau_0$，
也证明任何固定密度均为它。取初态 $\widehat\tau_1$ 给两个相反次序的极限。

该不连续性有一个准确模式：$D_*=\widehat\tau_1-\widehat\tau_0$ 在原通道中特征值为一，
在扰动中为 $1-\varepsilon$，所以当 $\varepsilon\downarrow0$ 没有一致谱隙。
对每个固定有限深度，所有联合输入的预测可任意接近；
深度无界后仍可选择正交的不同极限。
这并非否定 §18 精确模型的收敛，而是区分两种量词顺序与两套资源合同。证毕。

**定义 21.3（有向信息候选与共同查询）。**
设 $\Omega$ 为非空紧空间，$C\in\mathcal I$ 是有向信息切面。
令 $K_C\subseteq\Omega$ 非空闭，且 $C\le D\Rightarrow K_D\subseteq K_C$。
查询 $q:\Omega\to\mathbb R$ 连续，$K_\infty=\bigcap_CK_C$。
结构、核、端口及记录类型可以共同进入 $\Omega$，但其紧拓扑、闭约束和共同查询必须分别供应。
有限维固定对角 PSD 核集合或固定输入输出的 Choi 通道集合是有界闭的具体紧载体；
任意变化的无界图类并不自动具有这些性质。

**命题 21.4（有向分辨率、残余宽度与共同概率的区别）。**
在定义 21.3 下，

$$
\begin{gathered}
K_\infty\ne\varnothing,\qquad
\min_{K_\infty}q=\sup_C\min_{K_C}q,\qquad
\max_{K_\infty}q=\inf_C\max_{K_C}q,\\
\inf_C\operatorname{diam}q(K_C)=\operatorname{diam}q(K_\infty).
\end{gathered}
$$

若极限宽度小于 $\epsilon$，存在一个有限信息切面，此后的全部相容精细化宽度均小于 $\epsilon$。
宽度极限为零等价于查询在残余纤维上常值，不要求模型唯一，亦不产生先验权重或有效停止算法。

证明。
这是[预测波命题 28.2](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md)
序列结论的有向应用；这里不假设指标有可数共尾序列，因此使用有限交证明。
对任意有限个 $C$ 取共同上界 $D$，$K_D$ 包含于其交且非空。
紧致性给 $K_\infty$ 非空紧。
令 $a=\sup_C\min_{K_C}q$。
闭集 $K_C\cap\{q\le a\}$ 非空，任意有限组也由一个共同上界中的最小点见证非空，
故存在 $x\in K_\infty$ 且 $q(x)\le a$。
反向所有 $x\in K_\infty$ 满足 $q(x)\ge\min_{K_C}q$ 对每个 $C$ 成立，
所以其最小值恰为 $a$。对 $-q$ 同理，最大值为 $b=\inf_C\max_{K_C}q$。

每层宽度为两端点差且至少 $b-a$。
给 $\delta>0$，分别选切面使最小值大于 $a-\delta$、最大值小于 $b+\delta$；
取共同上界后两者同时成立，宽度小于 $b-a+2\delta$。
令 $\delta\downarrow0$ 得所需等式。有某层宽度小于 $\epsilon$ 后，包含单调性保证全部后继同样成立。

此结论的对象是指定连续查询的宽度。
$K_n=[0,1/n]$ 的极限查询宽度为零，有限层仍未达到精确值；
无紧性时 $K_n=[n,\infty)\subset\mathbb R$ 各层非空却无交。
对无穷查询菜单，逐项趋零不保证统一：
令 $\Omega=\{0,1\}^{\mathbb N}$，产品度量为
$\sum_k2^{-k}|x_k-y_k|$，$K_n$ 固定前 $n$ 位为零。
每个固定坐标查询最终宽度零，但每个有限 $n$ 的所有坐标宽度上确界仍为一。
若需统一菜单结论，可另要求紧查询参数集 $Q_0$ 及联合连续 $F:Q_0\times\Omega\to\mathbb R$；
把同一有限交/极值论证应用到 $Q_0\times K_C^2$ 即得统一宽度等式。
仅有“全部深度”的字面菜单不能替代这些条件。

若两个候选对全部许可记录同律而事件值分别为零、一，
$(1-\lambda)\delta_{\omega_0}+\lambda\delta_{\omega_1}$ 对任意 $0\le\lambda\le1$
满足同一支持约束，却给不同事件概率 $\lambda$。
故相容性不选择概率，抽象紧致性不供应可取得的收敛速率或停止证书。证毕。

## 22. 全局相容核与反事实结果表的不同粘合问题

**支撑推导 22.1（静态切面应用不要求非上下文的局部答案表）。**
§§14–21 的全局核或相容仪器网络可以统一规定各许可实验的概率，
而不把所有不相容设置的实际结果并入一个配置。
要求四个二值局部反事实有共同经典分布是更强、且可与量子实例不相容的条件。
模型未被排除也不决定其间的相干交叉项。

证明。
本卷 §10 的 Bell/CHSH 机制及[静态相融纤维 §8](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)
已区分效果赋值与反事实联合分布；这里将它作为配置应用的边界使用。
若 $a_0,a_1,b_0,b_1\in\{-1,1\}$ 有共同分布，且每设置相关为它的边缘，
每个确定赋值满足

$$
a_0(b_0+b_1)+a_1(b_0-b_1)\in\{-2,2\},
$$

因两括号恰有一个为零、另一个为 $\pm2$，故平均绝对值至多二。
在已供应的复张量表示中取

$$
|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2,
\quad A_0=Z,\ A_1=X,
\quad B_0=(Z+X)/\sqrt2,\ B_1=(Z-X)/\sqrt2.
$$

其 Bell 算子为 $\sqrt2(Z\otimes Z+X\otimes X)$，
两个乘积算子在该态的期望均为一，给 $2\sqrt2$。
跨系统效果可交换，同一系统的不同设置无需共同锐赋值。
这正是 [Abramsky–Brandenburger](https://arxiv.org/abs/1102.0264)讨论的上下文粘合区别，
不排除一切决定论或允许上下文依赖的模型。

甚至每设置非负、归一且不信号也不足以唯一选出量子：
对设置 $x,y\in\{0,1\}$，令结果位满足 $a\oplus b=xy$，
两个满足式的结果对各赋 $1/2$，其单方边缘都均匀而 CHSH 达四。
所以全量子核条件不可削弱成这些逐上下文条件后仍称同一重建。

两个独立候选各自有单位核时，联合核仍可取

$$
\begin{pmatrix}1&z\\\overline z&1\end{pmatrix},\qquad |z|\le1.
$$

特征值为 $1\pm|z|$，全部这些 $z$ 都 PSD。
$z=0$ 为正交扇区，$|z|=1$ 为同一射线的相位关系。
两个模型都未被排除不选择 $z$，更不选择混合权重。
因此共同候选、概率混合、相干叠加及共同局部答案表是四个有不同输入的结构。证毕。

## 23. 同一实际临界态的概率与势资源读口

**定义 23.1（PDE 供应的源、状态、单位和拓扑对应）。**
本节将[全息边界几何附录 §§102–105](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX.md)
的既有实际态结果应用到静态观察者的读口区分，全部解析量沿用该源，不由五模式码构造。
其群为 $G=\mathrm H^1\times\mathbb R$，坐标 $(x,y,z,w)$，

$$
\begin{aligned}
(x,y,z,w)(x',y',z',w')
 &=(x+x',y+y',z+z',w+w'+xy'),\\
d\mu&=dx\,dy\,dz\,dw,\\
X_1&=\partial_x,\quad X_2=\partial_y+x\partial_w,\quad X_3=\partial_z,\\
L&=-\sum_{i=1}^3X_i^2,\qquad D_w=-i\partial_w.
\end{aligned}
$$

$L$ 是原非负自由实现，时钟为 $e^{-tL}$，
$\Gamma=\int_0^\infty h_t\,dt$ 是原正的 $-3$ 次齐次 Green 场，$L\Gamma=\delta_e$，单位源仍在群单位元 $e$。
$a,\eta>0$、坐标与中心谱单位固定；不作随 $n$ 改变的坐标或源重标定。
设

$$
\begin{gathered}
\mathcal E_\sigma=D(L^{1/2})\cap D(|D_w|^{\sigma/2}),\qquad
\|u\|_{\mathcal E_\sigma}^2=\|u\|_2^2+T[u]+D_\sigma[u],\\
T[u]=\sum_i\|X_i u\|_2^2,\qquad
D_\sigma[u]=\||D_w|^{\sigma/2}u\|_2^2,\qquad
V[u]=\int_G\Gamma|u|^2d\mu,\\
g_\sigma^*=
\inf_{0\ne u\in\mathcal E_\sigma}\frac{aT[u]+\eta D_\sigma[u]}{V[u]},\qquad
g_c=16\sqrt{a\eta},\quad t_c=g_c/(2a),\quad d_c=g_c/(2\eta)>0.
\end{gathered}
$$

对任意 $\sigma_n>2$ 趋于二，不要求单调，取供应定理 102.3 的任意非零实际临界零态，
仅调整振幅使 $V[u_n]=1$。
它满足全复形式域上的实际弱方程

$$
a\,t(\phi,u_n)+\eta\,d_{\sigma_n}(\phi,u_n)
 =g_{\sigma_n}^*\int_G\Gamma\overline\phi u_n\,d\mu
\quad(\phi\in\mathcal E_{\sigma_n}),
$$

其中 $t,d_\sigma$ 是对应二次型的极化形式。
不用试探态、正态假设、唯一态或另选剖面代替这些实际态。

定义读口

$$
M_n=\|u_n\|_2^2>0,\qquad v_n=u_n/\sqrt{M_n},\qquad
\mu_n=|v_n|^2d\mu,\qquad
\nu_n=M_n\Gamma\,\mu_n=\Gamma|u_n|^2d\mu.
$$

二者均为概率测度，第一项是普通位置概率，第二项为归一化势资源权重。
$M_n\Gamma$ 是同一态上的重加权，不是另一个已制备物理态，亦不是隐藏的坐标变换。

**应用接口 23.2（原读口分离结果的静态解释及适用范围）。**
对定义 23.1 的每种实际选态，原齐次范数及球为

$$
\rho(p)=\left((x^2+y^2+z^2)^2+(w-xy/2)^2\right)^{1/4},
\qquad B_\rho(p,r)=\{q:\rho(p^{-1}q)<r\}.
$$

供应定理 104.5 已同时给出每个 $n,p,r>0$ 的两个球界、全部 $1/4<\alpha<1/2$ 的移动球结论，
以及同一态两概率的 TV 趋一。
因此这些读口给出“势资源集中而普通概率不集中在同一移动球”的精确实例；
该实例与普通概率不逃向无穷远的供应定理 105.1 相容。

证明。
全部参数对应为原源 $e$、原 $d\mu,\Gamma,L,D_w,a,\eta$，
同一实际态 $u_n$，$d_n=D_2[u_n]=\|\partial_wu_n\|_2^2$，
$B_\Gamma=\sup_{q\ne e}\rho(q)^3\Gamma(q)<\infty$。
定理 103.3 供给 $M_n\to0$、$d_n\to d_c>0$；
定理 104.5 的原式为

$$
\begin{aligned}
\mu_n(B_\rho(p,r))
 &\le\min\{1,2r^2\sqrt{d_n/M_n}\},\\
\nu_n(G\setminus B_\rho(e,r))
 &\le\min\{1,6B_\Gamma\sqrt{M_nd_n}/r\}.
\end{aligned}
$$

相同供应已将 $r=M_n^\alpha$ 代入，误差幂为

$$
2\sqrt{d_n}\,M_n^{2\alpha-1/2},\qquad
6B_\Gamma\sqrt{d_n}\,M_n^{1/2-\alpha}.
$$

在该开区间两指数均正，故

$$
\mu_n(B_\rho(e,M_n^\alpha))\to0,\quad
\nu_n(B_\rho(e,M_n^\alpha))\to1,\quad
\operatorname{TV}(\mu_n,\nu_n)\to1.
$$

TV 采用概率事件差上确界，最大为一；若采用未除二的测度变差范数则极限为二。
这三个结论以及两个估计均为对供应定理的直接引用，非另一个 PDE 估计或新指数计算。
读口对应只使用同一事件在两个既定测度中的概率，未修改场或状态方程。

拓扑也沿用原供应。
$\mathcal Q_c$ 是临界 Friedrichs 空间，范数平方为
$\|u\|_2^2+\overline q_c[u]$，其中在 $\mathcal E_2$ 上
$q_c[u]=aT[u]+\eta D_2[u]-g_cV[u]$。
定理 103.3 给 $u_n$ 在原 $L^2$ 和 $\mathcal Q_c$ 中强趋零、在 $\mathcal E_2$ 中弱趋零，
却在 $\mathcal E_2$ 及 $L^2(G,\Gamma d\mu)$ 中均无强收敛子列。
这不矛盾：$V[u_n]=1$，两个动能趋于正值，而较弱临界形式范数趋零。
归一后的 $v_n$ 的概率不能从未归一 $u_n\to0$ 推出。

普通概率的无穷远边界由定理 105.1 进一步固定为

$$
\lim_{R\to\infty}\limsup_{n\to\infty}
 \mu_n\{\rho>R\}=0.
$$

在定理 104.2 的同时子列分解中，因而 $m_\infty=0$、$\|v\|_2^2+m_e=1$；
沿其弱态子列，每个固定有界且在 $e$ 邻域消失的可测截断 $\zeta$ 满足
$\zeta v_n\to\zeta v$ 在原 $L^2$ 中强收敛。
若谈测度的单点紧化极限，是对 $G\cup\{\infty\}$ 连续测试的弱收敛；
中心谱概率的窄收敛另在固定单位的 $[0,\infty)$ 上。
这些测度拓扑与态的 $L^2$、形式域或加权范数不互相替代。

不逃向无穷远没有指定 $m_e$、非零弱剖面的存在或唯一极限形状，
移动球界也没有指定 $r\asymp\sqrt{M_n}$ 的重标定资源分布。
这里不把这些尚未给定的性质加入供应结论；
同时不把已经排除的无穷远逃逸重新列作未知。
由此该例准确支持“稳定须声明读口和拓扑”的应用，
而不证明复结构、Born 律或物理空间维数。证毕。

## 24. 共同静态关系的综合条件与三项未闭合接口

**定义 24.1（应用的共同对象及来源）。**
前述构造的共同数学对象记为

$$
\mathfrak S=
\bigl(\operatorname{Conf},\{H_C,K_C,\mathcal A_C\},
\{V_{DC},\mathcal I_a\},\{\mathcal A_O,\mathcal D_O\},\Omega_h\bigr).
$$

各分量按 §§14–23 的类型、假设和共同测试识别，不要求任意这样的元组都可实现。
所用供应及其范围为：本卷 §§6、11–12 的核下降、序列等距和条件重建；
[静态相融纤维 §§1–4、10–12](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)的配置、响应商、端口界和局部态；
[无序原子 §§5–7、9](AURIC_UNORDERED_COMPATIBLE_ATOM_AND_QUANTUM_REPRESENTATION_THEORY.md)的复结构、概率和合法路径；
[图册 §§3–4](RECURSIVE_RELATIONAL_OBSERVATION_ATLAS_STABLE_CORE_HOLONOMY.md)的实际域与闭路；
[预测波 §§16–17、28](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md)的局部关系、原仪器及序列候选宽度；
[五窗口量子记忆 §§17–19](AURIC_FIB_FIVE_WINDOW_QUANTUM_MEMORY.md)的完整固定点/谱/全输入极限包；
[环境记录定理 2.2、20.1](AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md)的原生公平标签与扩大菜单下的 $L$ 仪器；
[尖锐任务保留环境记忆定义 1.1](RECURSIVE_RELATIONAL_OBSERVATION_SHARP_TASK_RETAINED_ENVIRONMENT_MEMORY.md)的全部原生有限字律；
以及[边界几何附录定理 102.3、103.3、104.5、105.1](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX.md)
的实际临界态、拓扑和两读口界。
标准正核、GNS、Choi–Kraus、效果表示、紧致性和 CHSH 只作为这些应用的中间工具，
其来源分别在使用处及本卷 §13 标注，不另作优先权主张。

**命题 24.2（内部观察的静态综合与开放接口）。**
在已供应的共同表示及相容扇区内，以下四项可以同时成立：
完整核和记录有一个有向静态表示；原生标签在整个平衡段上逐分支不变；
新增环境读口给平均不变而条件破缺的分支，新增返回仪器形成精确无界记录树；
人口读口不能区分平衡端点，而小的额外复位可选择不同的无穷深度极限。
将此对象解释为受限原生资源的完整物理重建，仍有以下三个具体数学接口。

1. 原生资源可达性：固定实际五模式等待/读出/Stop、辅助及参考限制后，
   是否可实现带标签 $X\mapsto\sum_{a=\pm}L_aXL_a^\dagger\otimes|a\rangle\langle a|$，
   或在全输入任意参考的统一范数中逼近？
   定义 19.1 的任意五级酉/PVM 扩大菜单已有精确实现；
   这并未解决原受限菜单，黑盒通道的 Kraus 改写也不授权其环境。
2. 未知关系下的保护：哪些实际可取得的有限相容测试能认证五维效果 $J$ 的保护权重
   $\operatorname{Tr}(J\rho)$，并给任意拼接尺度的统一泄漏界？
   定理 21.2 表明只有单门小误差不够；若声明更强保护关系、可求和预算或一致稳定性，须证明其覆盖全部相关接续。
3. 复结构的操作来源：原子间实际可执行的正交读出、相位比较及并置，
   是否足以排除实量子/经典子理论并强制全局相容 $J_{\rm c}$？
   仅有三个实正交方向、一般未知性或正核尚未证明这一步，
   全效果、全参考和概率标定的合同不能在结论中删去。

证明。
取本卷 §12 的同一复表示模型，将完整有限记录作为图内端口。
§14 在固定总体配置中给有向索引；§15 在明确的等距或代数相容条件下给极限，
§§16–17 保留合法比较、相干关系和返回记忆。
§18 的供应对应将同一实际五模式通道接入此表示。
定理 19.2 对全 $\theta,p$ 给原生不变、条件破缺及全部柱律，
命题 19.3 给有限网络的全参考近似边界。
§20 的双设置端口结果有独立输入和解码合同，不能由这些现象替代；
定理 21.2 的合法 CPTP 扰动又给不同的无穷极限。
故四项在同一类型化应用中相容，不能以其中一项否定另一项。

列出的三个接口分别要求受限菜单中的实现、全尺度保护证书及操作层复结构来源。
当前使用的供应和证明没有其中任何一项所需的全部量词：
扩大菜单实现不证明受限实现，有限网络界不证明无限一致界，
已有复表示不证明不预设复结构的重建。
因此它们保留为明确问题；这不削弱已声明前提内的定理，
也不要求模型在无前提情况下推出全部物理规律。
PDE 读口的已证源和拓扑由 §23 原样保留，不用其资源集中替换位置概率或量子重建。
由此，内部观察者准确地是相容静态关系中的访问、记录与接续结构；
观察到的变化、破缺和稳定由读口、保留端口及极限条件共同决定。证毕。

## 追加锚（本行以下为增补区）

## 25. 关系谱作为共同预测对象：谱值、切面与有向组合

**定义 25.1（有类型的关系描述与表示）。** 一个关系描述指定准备、输入输出边界、可接续操作、停止和失败记录、读出及其共同标定；只有输出类型与输入类型匹配的词才可复合。
在一个共同边界内，复合写成有单位复 $*$-代数 $\mathcal A_0$ 的乘法，$ab$ 表示先 $b$ 后 $a$，伴随反转词序。
在多个边界间可用矩阵角表示匹配端口；把不匹配的词强行相乘不属于本定义。
完整关系数据包含全部合法词矩、跨描述比较和分支权重，不只是某个算子的本征值及重数。
本节称其为关系谱；这不是标准单算子谱的别名，也不预设图的点边为唯一表示。
静态指这些共同关系同时被规定，不要求局部乘法可交换，也不另加全局外部钟。

**应用 25.2（同一读口下的谱值不足）。** 取 $M_2(\mathbb C)$、$\rho_0=|0\rangle\langle0|$、$\rho_+=|+\rangle\langle+|$、$|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$。
二态本征值都为 $(1,0)$，固定效果 $F=|0\rangle\langle0|$ 却给概率 $1$ 与 $1/2$。
这是[预测波 §1](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md)谱值不足机制在准备—效果关系中的直接实例。
同时以同一酉变换状态和效果，$\rho'=U\rho U^\dagger,F'=UFU^\dagger$，则 $\operatorname{Tr}(\rho'F')=\operatorname{Tr}(\rho F)$；这才是保该关系的被动表示改变。

对任意有限含单位交换 $*$-子代数 $\mathcal B\subset M_d$，令其最小非零投影为 $P_j$，则 $P_jP_k=\delta_{jk}P_j$、$\sum_jP_j=I$。
所有 $B_i\in\mathcal B$ 同时写为 $B_i=\sum_jb_{ij}P_j$，状态限制是 $\mu_j=\operatorname{Tr}(\rho P_j)$，故

$$
\operatorname{Tr}\bigl[\rho f(B_1,\ldots,B_k)\bigr]
 =\sum_j\mu_j f(b_{1j},\ldots,b_{kj}). \tag{25.1}
$$

投影的正交乘法先证明多项式公式；有限联合谱上的任意函数都由其谱值定义，给一般 $f$。
一个这样的切面有经典联合结果，不代表不同切面的结果已有同一非上下文赋值。
同步转置 $\rho\mapsto\rho^{\mathsf T},A\mapsto A^{\mathsf T}$ 保持每个自伴谱和迹配对，且在每个交换切面内保持乘法；一般却只有 $(AB)^{\mathsf T}=B^{\mathsf T}A^{\mathsf T}$。
具体取

$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
Z=\operatorname{diag}(1,-1).
$$

$XY=iZ$，而 $X^{\mathsf T}=X,Y^{\mathsf T}=-Y,Z^{\mathsf T}=Z$，所以 $(XY)^{\mathsf T}=iZ$、$X^{\mathsf T}Y^{\mathsf T}=-iZ$。
在同步不变的 $\rho_0$ 上，两种有向词矩分别为 $i,-i$。
这说明交换切面数据不规定跨切面的有向组合，并未凭空授予测量这些复词矩的读口。
转置也不能作为任意复参考下的合法量子过程：令 $|\Omega\rangle=(|00\rangle+|11\rangle)/\sqrt2$，则

$$
(\operatorname{id}_2\otimes {\mathsf T})(|\Omega\rangle\langle\Omega|)
 =\tfrac12\sum_{j,k=0}^1|j\rangle\langle k|\otimes|k\rangle\langle j|
 =\tfrac12\mathrm{Swap}.
$$

它在反对称单位向量 $(|01\rangle-|10\rangle)/\sqrt2$ 上的本征值是 $-1/2$，违反正性。
这正是本卷 §7 的“每个有限复参考、全部联合正输入”条件区别于单系统正性的用途（标准 Choi–Kraus/Watrous 完全正性准则）。

为检验把静态关系强制改为经典答案表的后果，消费标准 Mermin–Peres 方阵（Mermin，PRL 65, 3373；Cabello，[arXiv:0808.2456](https://arxiv.org/abs/0808.2456)）：

$$
\begin{array}{ccc}
X\otimes I&I\otimes X&X\otimes X\\
I\otimes Y&Y\otimes I&Y\otimes Y\\
X\otimes Y&Y\otimes X&Z\otimes Z
\end{array}. \tag{25.2}
$$

九个算子自伴、平方为单位，每行每列两两对易。三行乘积及前两列乘积均为 $I_4$，末列乘积为 $-I_4$。
例如 $(X\otimes Y)(Y\otimes X)=Z\otimes Z$，而 $(X\otimes X)(Y\otimes Y)=-Z\otimes Z$；其余四项由不同张量因子对易直接得到。
若为九格赋与上下文无关的 $\pm1$，并在每个交换上下文保持乘法，则六个约束相乘时每格出现两次，左边为 $+1$，右边为 $-1$，矛盾。
方阵本身是一致的静态量子表示；排除的是这个明确的非上下文确定赋值条件，不是所有隐变量模型。
因此 (25.1)、复合方向与 (25.2) 是关系描述必须分别保留的条件；单个谱表或“静态”一词不能替代它们。

## 26. 有界有向词矩在完整递归原子中的闭合应用

**定义 26.1（代数输入与有限生成元界）。** 在定义 25.1 的共同边界上，令 $\Gamma$ 为对伴随封闭的生成字母族，$\mathcal A_0$ 是按已声明 $*$-关系取商的有单位复代数。
给每个 $g\in\Gamma$ 一个有限的 **非负** 实数 $M_g\in[0,\infty)$；允许 $M_g=0$，不以负常数表示范数界。
给定复线性 $\ell:\mathcal A_0\to\mathbb C$，对全部 $p\in\mathcal A_0,g\in\Gamma$ 要求

$$
\ell(1)=1,\quad\ell(p^*p)\ge0,\qquad
\ell(p^*g^*gp)\le M_g^2\ell(p^*p). \tag{26.1}
$$

正性不等式指实数不等式。给定的商关系必须已被 $\ell$ 尊重；只给未指定拼接的图不构成该输入。
本节将这些全称代数假设接入 §§6、12 的完整分支与条件态接口；完整词矩并不声称已由有限样本取得。

**应用 26.2（有界表示、递归条件泛函与零分支）。** 对定义 26.1 的每个输入，可构造最小循环有界 $*$-表示 $(H_\ell,\pi,\Omega)$，满足

$$
\|\Omega\|=1,\quad \ell(a)=\langle\Omega,\pi(a)\Omega\rangle,
\quad\|\pi(g)\|\le M_g,\quad
\overline{\pi(\mathcal A_0)\Omega}=H_\ell. \tag{26.2}
$$

同一完整泛函的两个这样的最小表示有唯一保 $\Omega$、交织全部标记操作的酉同构。
这里内积第一变量共轭线性。标准 GNS 的出处是 Weber–Li–Voigt 的 [ISEM24 讲义，Lemma 5.17、Theorem 5.18](https://www.math.uni-sb.de/ag/speicher/weber/ISem24/ISem24LectureNotes.pdf)；其 $C^*$-代数假设不能直接取代 (26.1) 的代数有界性。
所需桥梁如下。

由 $\ell((p+zq)^*(p+zq))\ge0$ 对全部 $z\in\mathbb C$ 成立，先取实、虚参数极化，得到 $\ell(q^*p)=\overline{\ell(p^*q)}$，再取二次式的最小值得

$$
|\ell(p^*q)|^2\le\ell(p^*p)\ell(q^*q).
$$

所以 $\mathcal N=\{p:\ell(p^*p)=0\}$ 与所有向量半正交，并为线性空间。
(26.1) 给 $p\in\mathcal N\Rightarrow gp\in\mathcal N$。对字母的有限乘积迭代，再用线性，得 $ap\in\mathcal N$ 对每个 $a\in\mathcal A_0$ 成立；故 $\mathcal N$ 是左理想。
在商上置 $\langle[p],[q]\rangle=\ell(p^*q)$、$\pi_0(a)[p]=[ap]$，良定义且为正定内积。
对生成元，$\|\pi_0(g)[p]\|^2\le M_g^2\|[p]\|^2$；对每个有限多项式 $a=\sum_w a_ww$，还有

$$
\|\pi_0(a)\|\le\sum_w|a_w|\prod_{g\text{ in }w}M_g<\infty.
$$

故各算子延拓到商的 Hilbert 完备化。关系 $\langle[p],\pi_0(a)[q]\rangle=\langle\pi_0(a^*)[p],[q]\rangle$ 给 $*$-表示；$\Omega=[1]$ 给 (26.2) 及循环性。
两个表示间在稠密循环子空间定义 $U\pi_1(a)\Omega_1=\pi_2(a)\Omega_2$。
两边任意有限线性组合的内积都由同一 $\ell(a^*b)$ 给出，故映射良定义且等距；循环性给稠密值域，延拓后满射。
它保循环向量并交织每个 $\pi(a)$，这些性质在稠密集上也强制唯一性。
这完成代数输入到有界生成元的桥梁；只有正性而无 (26.1) 时，左乘可无界，不能称有界量子门。

现在对每个已许可前缀 $h$，供应有限结果集 $A_h$ 与有限隐藏 Kraus 下标 $\mu$，取 $m_{h,a,\mu}\in\mathcal A_0$，满足完整关系

$$
\sum_{a\in A_h,\mu}m_{h,a,\mu}^*m_{h,a,\mu}=1. \tag{26.3}
$$

成功、失败、停止都须纳入结果；停止可用一个恒等吸收分支，任意有限记录树因而仍完整。
定义未归一泛函 $L_\varnothing=\ell$，并递推

$$
L_{ha}(x)=\sum_\mu L_h(m_{h,a,\mu}^*xm_{h,a,\mu}),\quad
p(h)=L_h(1),\quad\ell_h=L_h/p(h)\quad(p(h)>0). \tag{26.4}
$$

对每个合法有限前缀，这些泛函均正，满足 $p(h)\ge0$、$p(\varnothing)=1$、$\sum_ap(ha)=p(h)$。
正概率时 $\ell_h$ 归一且满足与 (26.1) **相同** 的生成元界。
证明是对深度归纳：$L_h(m^*x^*xm)=L_h((xm)^*(xm))\ge0$；将已有的界用于 $pm$，再对 $\mu$ 求和，即

$$
L_{ha}(p^*g^*gp)\le M_g^2L_{ha}(p^*p).
$$

(26.3) 插入 (26.4) 给前缀权重相容。除以正的 $p(h)$ 保持界。
若 $p(h)=0$，正泛函的 Cauchy–Schwarz 给 $|L_h(x)|^2\le L_h(1)L_h(x^*x)=0$，故 $L_h=0$，所有后继也为零；没有可除的条件态。

展开 (26.4) 时，每个隐藏路径取有向乘积 $m_{h,\boldsymbol\mu}=m_{h_{n-1},a_n,\mu_n}\cdots m_{\varnothing,a_1,\mu_1}$，有

$$
L_h(x)=\sum_{\boldsymbol\mu}\ell(m_{h,\boldsymbol\mu}^*xm_{h,\boldsymbol\mu}),\qquad
p(h)=\sum_{\boldsymbol\mu}\|\pi(m_{h,\boldsymbol\mu})\Omega\|^2. \tag{26.5}
$$

隐藏下标是概率和，不是将 $m$ 的振幅先相加。对当前条件泛函或这些未归一向量分别作和，得到同一记录律；输入无关随机控制也按其实际权重混合。
在 (26.2) 中 $\sum_{a,\mu}\pi(m_{h,a,\mu})^*\pi(m_{h,a,\mu})=I$，故 $v\mapsto\bigoplus_{a,\mu}\pi(m_{h,a,\mu})v$ 为等距。
这将本卷定理 6.2、6.4 的分支等距与概率接口具体实例化：共同相干分支已被供应，遗忘 $\mu$ 给相应 CP 分支，遗忘全部结果给保迹更新。
有限矩阵边界上，这些 Kraus 公式张量任意有限复参考仍正；没有因条件化而删去参考或零概率边界。

最后，循环向量不保证原代数态纯。取 $\mathcal A_0=M_d$、$\ell(A)=\operatorname{Tr}(A)/d$，其表示是 Hilbert–Schmidt 空间 $M_d$ 上的左乘，$\Omega=I/\sqrt d$。
$\langle\Omega,A\Omega\rangle=\operatorname{Tr}(A)/d$，左乘轨道张成全空间，故循环且最小；$d>1$ 时原态 $I/d$ 仍是多个正交纯态的非平凡混合。
因此 (26.2) 不能把候选解释不确定性改称原系统纯叠加，(26.5) 也没有从归一正性独自推出实际频率标定。∎

## 27. 跨描述核与物理相干接口

**应用 27.1（相容内部描述到共同相干比较的缺项）。** 取两个有限描述集的内部复 Gram 核 $A\succeq0,B\succeq0$，大小分别为 $r,s$。
本卷 §§6、15 的正核表示若要包含两个描述集，尚须一个 $r\times s$ 的交叉块 $C$，使

$$
K=\begin{pmatrix}A&C\\C^\dagger&B\end{pmatrix}\succeq0.
$$

这里消费标准奇异块收缩分解：[Watrous，arXiv:1207.5726v2，Lemma 2](https://arxiv.org/abs/1207.5726v2) 给同大小正块版本，不要求正定；不同大小可补零到共同大小。
其精确参数对应为该引理的 $P=A,Q=B,X=C$（补零时同时补交叉块）。结论是

$$
C=A^{1/2}TB^{1/2},\qquad T:\mathbb C^s\to\mathbb C^r,\quad\|T\|\le1. \tag{27.1}
$$

为保留奇异边界，若 $u\in\ker A$，对全部 $z\in\mathbb C,v$ 取 $(zu,v)$ 的二次型；没有 $|z|^2$ 项使线性交叉项必须为零，故 $u^\dagger Cv=0$。
同理 $C$ 消去 $\ker B$。在两个支撑空间用逆平方根合同，得到 $\left(\begin{smallmatrix}I&T\\T^\dagger&I\end{smallmatrix}\right)\succeq0$。
取 $(-Ty,y)$ 得 $\|Ty\|\le\|y\|$，在核上补零得到 (27.1)；反之收缩性给
$\|x\|^2+2\operatorname{Re}\langle x,Ty\rangle+\|y\|^2\ge(\|x\|-\|y\|)^2\ge0$，再合同即得 $K\succeq0$。
所以两个内部核一般没有决定它们的共同表示；缺的是收缩交叉关系，而非各自再作一次 GNS。

例如 $A=B=[1]$ 时 $C=[z]$ 可取整个 $|z|\le1$ 圆盘，且 $z$ 可由同一 Hilbert 空间单位向量 $v_0,v_1$ 的内积实现。
若额外供应共同参考和实际控制准备

$$
|\Psi\rangle=(|0\rangle v_0+|1\rangle v_1)/\sqrt2,
\qquad\langle v_0,v_1\rangle=z,
$$

再另供路径效果 $|+_\phi\rangle\langle+_\phi|$、$|+_\phi\rangle=(|0\rangle+e^{i\phi}|1\rangle)/\sqrt2$，则

$$
p(+_\phi)=\|(v_0+e^{-i\phi}v_1)/2\|^2
 =\tfrac12[1+\operatorname{Re}(e^{-i\phi}z)]. \tag{27.2}
$$

这个推导区分三个资源：数学上允许的共同核、能制备该相干控制态的接口、能读取相位的效果。
相容候选的存在不提供后两者，也不提供先验权重；$1/\sqrt2$ 是此处另供的平衡准备，不由候选数推出。
若改给经典权重 $p,1-p$，它们也是额外选择，并不自动给 (27.2) 的交叉项。
故“概念也在谱中”的可用含义是将概念编码、交叉关系、实际比较及权重分别纳入共同模型；不能以多个自洽解释替代相干性。∎

## 28. 完整观察者闭包在稳定概念任务中的应用

**定义 28.1（有限控制、记忆与共同合法词）。** 取一个固定有限维完整载体 $H$、$d=\dim H$；准备、观察者存储、有限控制状态及所用参考标定都已包含其中。
每个菜单动作 $u$ 给有限结果 CP 分支 $\Phi_{u,a}:M_d\to M_d$，$\sum_a\Phi_{u,a}$ 为 CPTP；末端效果族 $\mathcal M$ 有限。
若动作合法性依赖控制状态 $c\in C$，将 $c$ 作为有限正交寄存器并入载体，分支同时更新 $c$ 与记忆。
只许依赖已记录前缀的控制；不匹配的端口不复合。需把动作延拓为全载体映射时，将非法尝试作为明确拒绝结果并声明其后继，不能从记录分布删去。
等价地可在各控制块的直和上只列实际可达的型别词；以下使用已经完成这种编译的共同菜单。
持续增长的记忆、未列入的环境再用、无限结果或不可统一的合法域不在这个有限载体假设内。

令

$$
V_0=\operatorname{span}_{\mathbb R}(\{I\}\cup\mathcal M),\qquad
V_{n+1}=\operatorname{span}_{\mathbb R}\bigl(V_n\cup
\{\Phi_{u,a}^\dagger F:F\in V_n\}\bigr),\quad V=\bigcup_nV_n. \tag{28.1}
$$

完整有限协议包括所有记录、失败、停止及末端效果的两结果测试；有限自适应树的每条叶路径都是同一合同内的词。
对仅允许经典控制块的来源，可在其块对角自伴空间内取相同闭包；以下 $d^2$ 仍是上界，仿射维数结论另需所声称的全部态来源。

**应用 28.2（从既有闭包判据到概念翻译的检验）。** 本卷定义 11.3、定理 11.4 的参数逐项取

$$
W_0=V_0,\quad\mathcal G_{11}=\{I\}\cup\mathcal M,
\quad (a,o)_{11}=(u,a),\quad\Phi_{a,o}^*=\Phi_{u,a}^\dagger.
$$

其完整载体就是定义 28.1 的 $H$，不是只保留物理系统而删去控制记忆的空间。
因此 $W_n=V_n$、$W_\infty=V$，至多 $d^2-\dim V_0$ 次严格扩张后稳定；全密度来源的预测像实仿射维数为 $\dim V-1$。
两个态在全部这些有限记录与自适应策略上同律，当且仅当

$$
\operatorname{Tr}[(\rho-\sigma)F]=0\qquad(F\in V). \tag{28.2}
$$

具体地，一条路径 $h=((u_1,a_1),\ldots,(u_n,a_n))$ 的未归一响应是
$\operatorname{Tr}[\rho\,\Phi_{u_1,a_1}^\dagger\cdots\Phi_{u_n,a_n}^\dagger(F)]$，$F=I$ 或末端效果。
这些路径效果按深度张成 (28.1)，故 (28.2) 检查的是完整前缀质量，而非仅比较各自归一后的成功态。
固定反馈规则后，相同前缀选择相同动作；叶路径响应相等，求和得到同一协议分布。反向选一条固定路径及终端测试即得必要性。
零质量前缀没有条件分母；随机反馈先条件化其输入无关的随机种子再平均。
有限维保证一旦 $V_{n+1}=V_n$ 就已被全部分支拉回保持。
$I/d$ 的邻域中任意足够小迹零自伴扰动仍为态，归一限制像因而在 $\dim V-1$ 个方向满秩；这解释既有仿射维数公式需要全来源的原因。
若实际只供一个受限准备族，不能据该公式宣称已取得这么多维的响应。
这直接消费关系丛 §8 及本卷 §11 的已有结果，不另建观察闭包生产者。

本应用给表示翻译一个具体检查：若摘要删除方向 $D$ 却存在 $F\in V$ 使 $\operatorname{Tr}(DF)\ne0$，则在 $I/d$ 附近取 $\rho_\pm=I/d\pm tD$，它们当前摘要相同而某许可未来记录不同；摘要不对该未来任务闭合。
若所有被删除差都在 $V^\perp$，则由 (28.2) 翻译保全部协议律；这只是语义充分性，尚未构造正线性压缩或物理解码器。
本卷推论 11.5 的全酉菜单给 $V=\operatorname{Herm}_5$、二十四个归一实坐标；对角保持菜单则按命题 11.6 仅看人口。
命题 11.7 的实帧盲区可持续到全部有限协议，新增相位操作会改变 $V$，并非在同一商上无条件换名字。

对共同测试族 $\mathfrak T$ 还可定义

$$
d_O(\rho,\sigma)=\sup_{\pi\in\mathfrak T}\operatorname{TV}(P_\rho^\pi,P_\sigma^\pi).
$$

删去测试只缩小上确界；对所有来源使用同一个随机后处理 $K$ 时，$\|K(p-q)\|_1\le\|p-q\|_1$，所以它也不增 $d_O$。
此结论比较共同校准的测试，不能用来源依赖译码或不合法动作来扩大区分。
它区分保全响应的同构、针对任务的有损商、以及实际扩充读口三种“切面变化”。

**应用 28.3（菜单相对的可见平衡）。** 固定同载体 CPTP $\Phi$、效果菜单 $\mathcal M$，令

$$
W_{\mathcal M}=\operatorname{span}_{\mathbb R}
\{I,(\Phi^\dagger)^nF:F\in\mathcal M,n\ge0\},\qquad
N_{\mathcal M}=W_{\mathcal M}^{\perp}
$$

采用自伴空间上的迹配对。对每个密度 $\rho$，全部菜单响应 $\operatorname{Tr}[F\Phi^n(\rho)]$ 对 $n\ge0$ 不变，当且仅当

$$
(\Phi-I)\rho\in N_{\mathcal M}. \tag{28.3}
$$

因为相邻深度差恰为 $\operatorname{Tr}[(\Phi^\dagger)^nF\,(\Phi-I)\rho]$；其全为零等价于与所有生成元正交，单位项由保迹自动为零。
有限求和把相邻差零变为每层等于初层，反向显然。故 (28.3) 是充分且必要的菜单判据，弱于全态固定。
若要求保分支记录，应以 (28.1) 的完整分支闭包检查，不能只用擦标签 $\Phi$ 的幂。

对 §29 的实际三码，取 $A_0=i(E_{12}-E_{21})$、$\rho_t=I_3/3+tA_0$、$0<|t|\le1/3$，再嵌入为 $B\rho_tB^\dagger$。
$A_0$ 的本征值为 $1,-1,0$，所以这是合法态。$WA_0W=-A_0$ 使 $\mathcal T(A_0)=0$，故该态并非固定态，一步后成为 $BI_3B^\dagger/3$。
但码人口与五个物理人口从初层起就分别恒为 $(1/3,1/3,1/3)$、$(1/6,1/6,1/3,1/6,1/6)$，因为 $A_0$ 对角零且 $B$ 的三列支撑不交叠。
因此以五个模式投影为 $\mathcal M$ 时，$(\mathcal G-I)(B\rho_tB^\dagger)\in N_{\mathcal M}$，精确实例化 (28.3)，而 $\mathcal G(\rho)\ne\rho$（此处 $\rho=B\rho_tB^\dagger$）。
若扩充终端效果以读取相应虚相干，当前层与下一层即可不同；菜单相对平衡不是不依读口的属性。

**应用 28.4（忠实固定乘法与近似概念组合）。** 当一个切面的效果转换为 UCP 映射 $\Theta:M_d\to M_d$，并 **另有** 密度 $\varrho\succ0$ 满足
$\operatorname{Tr}[\varrho\Theta(A)]=\operatorname{Tr}(\varrho A)$ 对所有复 $A$ 成立时，稳定概念可用普通乘法。
这里消费忠实不变态与乘法域的标准机制（Carbone–Girotti，[*Absorption in Invariant Domains for Semigroups of Quantum Channels*](https://doi.org/10.1007/s00023-021-01016-5)）；对本应用所需的全部条件和估计展开如下。
若 $\Theta(A)=A$，Schwarz 差 $D=\Theta(A^\dagger A)-A^\dagger A\succeq0$ 且 $\operatorname{Tr}(\varrho D)=0$，忠实性迫使 $D=0$；$AA^\dagger$ 同理。
写 $\Theta(X)=V^\dagger(X\otimes I)V$、$V^\dagger V=I$，差为

$$
D=V^\dagger(A^\dagger\otimes I)(I-VV^\dagger)(A\otimes I)V.
$$

故 $(A\otimes I)V=VA$；由 $A^\dagger$ 的同一关系也得 $V^\dagger(A\otimes I)=AV^\dagger$。
于是 $\Theta(AB)=A\Theta(B)$、$\Theta(BA)=\Theta(B)A$。
当 $B$ 也固定时乘积固定；单位、线性、伴随与有限维闭性均保持，故固定集为普通 $C^*$-子代数。
若若干 UCP 映射各自有这样的忠实不变密度，其共同固定集是这些子代数的交；不要求它们有同一个密度，但不能省略各自忠实性。

对近似稳定概念，还须定量保留密度下界及算子收缩条件：设 $\varrho\succeq mI$、$m>0$，$\|A\|,\|B\|\le1$，记 $\delta_A=\|\Theta(A)-A\|$、$\delta_B=\|\Theta(B)-B\|$。则

$$
\|\Theta(AB)-AB\|\le
\delta_A+\delta_B+\frac2m\sqrt{\delta_A\delta_B}. \tag{28.4}
$$

证明。置 $\Delta(A)=\Theta(A^\dagger A)-\Theta(A)^\dagger\Theta(A)\succeq0$。
不变性、$\|\Theta(A)\|\le\|A\|\le1$ 与 $\operatorname{Tr}\varrho=1$ 给

$$
\operatorname{Tr}[\varrho\Delta(A)]
 =\operatorname{Tr}[\varrho(A^\dagger A-\Theta(A)^\dagger\Theta(A))]
 \le2\delta_A.
$$

而 $m\operatorname{Tr}\Delta(A)\le\operatorname{Tr}[\varrho\Delta(A)]$，所以 $\|\Delta(A)\|\le2\delta_A/m$；对 $A^\dagger$ 亦然，因为 UCP 保伴随。
Stinespring 的两侧缺陷因子给

$$
\begin{aligned}
\Theta(AB)-\Theta(A)\Theta(B)
 &=V^\dagger(A\otimes I)(I-VV^\dagger)(B\otimes I)V,\\
\|\Theta(AB)-\Theta(A)\Theta(B)\|
 &\le\sqrt{\|\Delta(A^\dagger)\|\,\|\Delta(B)\|}
 \le\frac2m\sqrt{\delta_A\delta_B}.
\end{aligned}
$$

再用 $\|\Theta(A)\Theta(B)-AB\|\le\delta_A+\delta_B$ 得 (28.4)。它适用于复算子，不只自伴效果。
因此读数近似稳定还需控制乘法关系的误差；$m\downarrow0$ 时不能宣称同一个统一误差界。
下节实际五维通道没有满秩不变密度，正是不能直接应用普通固定代数结论的情形。∎

## 29. 实际五维返回系统的稳定概念及其两标量解释

**定义 29.1（同一供应的输入、码与符号对应）。** 本节完整沿用定义 18.1–18.2 的物理基 $e_0,\ldots,e_4$、等距 $B=(u,v,z)$、Kraus 算子 $K_0,K_1$、擦标签通道 $\mathcal G:M_5\to M_5$ 和码通道 $\mathcal T:M_3\to M_3$。
这里码的 $z=e_2$，且空模式 $e_0$ 范数为一。
令

$$
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\quad P=\xi\xi^\dagger,\quad Q=I_3-P,
\quad\chi=B\xi,\quad d=(e_0-e_1-e_3+e_4)/2,
$$

$$
R=BB^\dagger-\chi\chi^\dagger=BQB^\dagger,\qquad
J=\chi\chi^\dagger+\tfrac23dd^\dagger,\qquad M=R/2. \tag{29.1}
$$

本节 $R$ 是秩二投影；§18 的 $R=\operatorname{Ran}B$ 是整个三码子空间，两个类型不互换。
供应[Half-Gram 分类，Corollary 6.1、(6.1)–(6.7)](AURIC_FIB_FIVE_WINDOW_HALF_GRAM_CLASSIFICATION.md)取规范 gauge $D=I$，其参数对应为

| Half-Gram 符号 | 本节符号与类型 |
| --- | --- |
| $\Phi_\circ$ | 同一完整通道 $\mathcal G:M_5\to M_5$ |
| recurrent $F$，基 $(u,v,z)$ | 经 $B$ 识别的码通道 $\mathcal T:M_3\to M_3$ |
| $s,P,M,E$ | $\chi,\chi\chi^\dagger,R/2,J$ |
| full limit $T$ | $\mathcal E_G:M_5\to M_5$，**不是**码通道 $\mathcal T$ |

五窗口量子记忆定理 18.1、18.3、19.1–19.2 则供应 Kraus、固定族、全瞬态、幂和完全范数极限，本卷 §18 已给逐项对应。
这些是同一实际矩阵，不从“维数都等于三”推断同构。

**应用 29.2（有限分辨、输入效果与返回乘法）。** 直接消费上述供应：

$$
\begin{gathered}
\operatorname{Fix}(\mathcal T)=\operatorname{span}_{\mathbb C}\{P,Q\},\quad
\tau_p=pP+(1-p)Q/2\quad(0\le p\le1),\\
\operatorname{spec}\mathcal T=\{1\ [2],-1/2\ [3],0\ [4]\},\quad
\mathcal E(X)=\operatorname{Tr}(PX)P+\operatorname{Tr}(QX)Q/2,\\
\mathcal T^n=\mathcal E+(-1/2)^{n-1}(\mathcal T-\mathcal E)\quad(n\ge1),\\
\mathcal E_G(X)=\operatorname{Tr}(JX)\chi\chi^\dagger+
\operatorname{Tr}[(I_5-J)X]R/2\qquad(X\in M_5(\mathbb C)). \tag{29.2}
\end{gathered}
$$

$\mathcal T$ 的最小多项式无重根，故可对角化；完整 $\mathcal G$ 仅有供应多项式 $\mathcal G^2(\mathcal G-I)(\mathcal G+I/2)=0$，保留二阶零瞬态，不能从码内可对角化推出全输入可对角化。
对全部 $n\ge2$，供应给

$$
\mathcal G^n-\mathcal E_G=(-1/2)^{n-2}(\mathcal G^2-\mathcal E_G),\qquad
\|\mathcal G^n-\mathcal E_G\|_\diamond\le\tfrac43\,2^{-(n-2)}. \tag{29.3}
$$

diamond 上确界包含每个有限未触动复参考与任意复矩阵输入，采用未除二范数。
因此对态和任一效果，概率误差还可取 (29.3) 的一半；有限精度可控制，并不表示某个有限幂已经等于极限。
例如令 $D_0=\operatorname{diag}(1,-2,1)$、$\rho_\pm=I_3/3\pm tD_0$、$0<t\le1/6$。
三对角元均非负、迹一，且码通道作用是

$$
\mathcal T(\operatorname{diag}(a,b,c))
=\operatorname{diag}((a+b)/2,c,(a+b)/2),\qquad
\mathcal T(D_0)=-D_0/2.
$$

所以 $\rho_\pm$ 同趋 $I_3/3$，但效果 $F=\operatorname{diag}(0,1,0)$ 的差为 $4t2^{-n}>0$，对每个有限 $n\ge0$ 都可在精确响应上区分。
容差 $\varepsilon>0$ 下，$n\ge\max\{0,\lceil\log_2(4t/\varepsilon)\rceil\}$ 才使该响应差至多 $\varepsilon$；样本可得性与误差标定另需实验合同。
同样，$\tau_p$ 的码人口总是 $(1/3,1/3,1/3)$，完整五人口总是 $(1/6,1/6,1/3,1/6,1/6)$。
所以相同人口不能读出 $p$；不是所有状态都已等于一个平衡态。

全输入效果结论已经由 Half-Gram 6.1 证明：

$$
\operatorname{Fix}(\mathcal G^\dagger)
=\operatorname{Ran}\mathcal E_G^\dagger
=\operatorname{span}_{\mathbb C}\{I_5,J\},\qquad
\mathcal E_G^\dagger(A)=\langle\chi,A\chi\rangle J+
\tfrac12\operatorname{Tr}(RA)(I_5-J). \tag{29.4}
$$

本应用把它解释为共同的两标量读出：$A=aI_5+bJ$ 对任意密度 $\rho$ 的值是 $a+b p_\rho$，$p_\rho=\operatorname{Tr}(J\rho)$。
$J$ 在 $\chi,d$ 及其三维正交补上的本征值为 $1,2/3,0$；故 $A$ 自伴当且仅当 $a,b\in\mathbb R$，且

$$
A\succeq0\ \Longleftrightarrow\ a\ge0,\ a+b\ge0,\qquad
0\le A\le I\ \Longleftrightarrow\ 0\le a,a+b\le1. \tag{29.5}
$$

中间值 $a+2b/3$ 是两端值的凸组合。该解释包含任意复系数及其伴随；在每个矩阵放大上，对 $C_0\otimes I+C_1\otimes J$，正性也恰为 $C_0\succeq0,C_0+C_1\succeq0$，因为第三块 $C_0+2C_1/3$ 是同一凸组合。
因此两标量对应不仅保标量次序，也保每个有限参考下的矩阵次序。

普通乘法不能把稳定效果变成投影：供应已给 $J^2-J=-2dd^\dagger/9\ne0$，且 $J^2\notin\operatorname{span}\{I,J\}$。
返回规则则给已存在的 Choi–Effros 乘法 $A\circ C=\mathcal E_G^\dagger(AC)$；代入 (29.4) 有

$$
(aI+bJ)\circ(cI+eJ)=acI+(ae+bc+be)J,\qquad
J\circ J=J,\qquad aI+bJ\longmapsto(a,a+b). \tag{29.6}
$$

两端系数逐分量相乘，故是保单位、保伴随及上述全部次序的 $\mathbb C^2$ 表示。
这里使用 Half-Gram 的既有返回乘法事实和标准 Choi–Effros 机制（JFA 24, 156–209），没有另造生产者。
码内 $B^\dagger JB=P$ 是普通投影；完整输入 $dd^\dagger$ 却有 $p_\rho=2/3$，其极限是 $\widehat\tau_{2/3}$，预先投影到码会错误删除这项进料。
完整空间的不变态全在码内，故无满秩不变密度，不能套用应用 28.4 的忠实普通固定代数结论。

对任意有限参考 $Z$ 和任意复 $X\in M_5\otimes M_Z$，同一供应公式是

$$
(\mathcal E_G\otimes\operatorname{id}_Z)(X)
 =\chi\chi^\dagger\otimes X_++(R/2)\otimes X_-,\quad
X_\pm=\operatorname{Tr}_H[(J_\pm\otimes I)X],\quad J_+=J,\ J_-=I-J. \tag{29.7}
$$

对联合正输入，$X_\pm\succeq0$：部分迹中可用 $(\sqrt{J_\pm}\otimes I)X(\sqrt{J_\pm}\otimes I)$ 代替左乘式。
其迹和为总质量，归一输入遂给乘积态的凸组合，正是供应的 reference-inclusive entanglement-breaking 极限；一般复输入上 (29.7) 是线性恒等，不声称 $X_\pm$ 为态。
秩二扇区只保留一个密度 $R/2$，不是持续的 $M_2$ 量子存储。
维数五的输入、维数三的输出支撑、八维码态参数、二维固定自伴空间、一维固定态段及人口菜单零个渐近输入参数可同时成立。
擦除环境得到的 EB 极限也不表示完整等距扩张中的所有关联都已消失。∎

## 30. 原实菜单的符号纤维与相位读口的应用边界

**定义 30.1（与预测波 §29 的精确符号映射）。** 沿用 §29 的同一 $B,K_j,U,W,\xi$，令

$$
f=(1,-1,0)^{\mathsf T}/\sqrt2,\quad e=(1,1,-2)^{\mathsf T}/\sqrt6,\quad
q=(\xi+e)/\sqrt2,\quad p_0=Bq,\quad P_+=(I_3+W)/2,
$$

$$
c=(e_0+e_1-e_3-e_4)/2,\quad a=Uq,\quad g=Uf,\quad
\alpha_t=\sqrt{1-t^2},\quad w_\pm=\alpha_tc\pm itp_0,\quad0<t<1,
$$

$$
T_\pm(X)=BP_+XP_+B^\dagger+(f^\dagger Xf)w_\pm w_\pm^\dagger,
\qquad S_\pm=\mathcal G T_\pm,\qquad J_s=(\mathcal G^\dagger)^s(p_0p_0^\dagger).
\tag{30.1}
$$

[预测波定义 29.1、定理 29.2–29.3](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md)中的 $p,P,T_{t,\pm},S_\pm,J_s$ 分别就是这里的 $p_0,p_0p_0^\dagger,T_\pm,S_\pm,J_s$；其 $c$ 是本节 $c$，不是 §29 的 $d$，其 $P$ 也不是码投影 $\xi\xi^\dagger$。
原数据合同只有全部 $s\ge0$ 的完整效果算子，不含分支标签、任意后选择历史、新相位控制或全效果菜单。
该映射把既有双世界直接接入概念查询，不把有限随机读数当作已知完整效果。

**应用 30.2（同一概念数据的后继风险）。** 供应给每个实对称效果 $F$ 的完整算子相等
$T_+^\dagger(F)=T_-^\dagger(F)$，特别是全部 $J_s$；同时

$$
\|S_+-S_-\|_\diamond=4t\alpha_t,\qquad
\inf_{A:M_3\to M_5\ {\rm CPTP}}
\max_{\pm}\|A-S_\pm\|_\diamond=2t\alpha_t. \tag{30.2}
$$

其参数满足 $B^\dagger c=0$、$c,p_0$ 单位正交、$P_++ff^\dagger=I_3$；所以 (30.1) 的两个 Kraus 算子完备，通道在整个复域 CPTP。
实 $F$ 的交叉项是实数，$w_\pm^\dagger Fw_\pm=\alpha_t^2c^\dagger Fc+t^2p_0^\dagger Fp_0$，符号消失；$K_j,p_0$ 全实使 $J_s$ 对每个深度仍实。
这实例化了 §28 的盲空间：在同一个实效果族内增加深度不切开该纤维；它不证明扩大菜单后的同律。

为明确 (30.2) 的完整复参考域，供应的实际关系是 $K_jc=Bg/\sqrt2$、$K_jp_0=Ba/\sqrt2$，$g,a$ 单位正交。
置 $v_\pm=\alpha_tg\pm ita$，则

$$
(S_+-S_-)(X)=(f^\dagger Xf)BDB^\dagger,\quad
D=v_+v_+^\dagger-v_-v_-^\dagger
=\begin{pmatrix}0&-2it\alpha_t\\2it\alpha_t&0\end{pmatrix}_{(g,a)}.
$$

本征值为 $\pm2t\alpha_t$。对任意有限参考和任意复矩阵 $Z$，放大输出是 $Z_{ff}\otimes BDB^\dagger$，其中 $Z_{ff}=(I\otimes f^\dagger)Z(I\otimes f)$。
压缩的迹范数不增、张量迹范数相乘，故范数比至多 $\|D\|_1=4t\alpha_t$；输入 $ff^\dagger$ 达到它。
任意仅据共同数据给出的同一个重建 $A$，由三角不等式最坏误差至少为端点距离一半；CPTP 中点 $(S_++S_-)/2$ 达到它。
这些是定理 29.2–29.3 的同一证明接口，不将只对状态输入的计算冒充 diamond 范数证明。
对更大的完整相容纤维，(30.2) 只给风险下界；中点未必控制其余世界。

供应的新效果 $E_y=Bhh^\dagger B^\dagger$、$h=(g+ia)/\sqrt2$ 合法，因为 $Bh$ 为单位向量，并满足

$$
\operatorname{Tr}[E_yS_\pm(ff^\dagger)]=\tfrac12\pm t\alpha_t. \tag{30.3}
$$

这是 $|h^\dagger v_\pm|^2=(\alpha_t\pm t)^2/2$ 的直接代入。
$t=1/\sqrt2$ 时概率为一、零；一般 $t$ 时概率不同不等于有限样本必定判对。
$E_y$ 有虚交叉项，超出原实菜单。它证明一个新增关系如何区分这对世界；能否由原生许可原语取得该效果、参考与控制，仍是实现问题。
原菜单的效果误差 $\delta=t^2$、到基准 $S_B=\mathcal G\operatorname{Ad}_B$ 的距离 $2t$ 亦由供应给出；它们与双世界半径 $2t\sqrt{1-t^2}$ 不同，不能相互替换。
后者在 $t\uparrow1$ 趋零尤其不能解释成到基准的误差也趋零。∎

## 31. 选择、隐藏维数与可重复记录的不同合同

**应用 31.1（幸存支持与隐藏总维数）。** 一个真正的成功选择是 CP 迹不增映射 $\Lambda$，成功率 $s_\rho=\operatorname{Tr}\Lambda(\rho)$，只在 $s_\rho>0$ 时定义成功态 $\Lambda(\rho)/s_\rho$。
若来源 $i$ 的经典权重为 $p_i$、成功率为 $s_i$，则联合成功质量为 $p_is_i$，归一成功记录的权重是 $p_is_i/\sum_jp_js_j$，不是原来的 $p_i$。
§29 的 $\mathcal G$ 是保迹通道，码内输出来自 Kraus 值域，不能改称丢掉失败样本的选择。

对任意有限 $H_v$、任意态 $\rho_v$、任意有限 $H_h$ 及其任意态 $\sigma_h$，令

$$
\rho=p\rho_v\oplus(1-p)\sigma_h\quad(0<p<1),\qquad
\Lambda(X)=P_vXP_v\quad\text{在 }H_v\oplus H_h\text{ 上}.
$$

直接压缩给 $\Lambda(\rho)=p\rho_v$，成功率 $p$、成功态 $\rho_v$，与隐藏维数及隐藏态无关。
即使记录成功与失败频率从而估计 $p$，也没有识别隐藏态或总维数。
任意正整数 $r$ 都可为反复选择后的稳定支持秩：取 $d\ge r$、秩 $r$ 投影 $P_r$、初态 $I_d/d$，成功率 $r/d$，成功态 $P_r/r$ 再过滤保持不变。
因此仅“幸存且稳定”不选择数字三。

更强的非选择性隐藏扩张已有原归属：[静态相容纤维，标题 §63，定义 82.1、定理 82.2、推论 82.3](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。
其逻辑输入是 $\iota:\mathbb C^4\to\mathcal C\subset\mathcal H=\mathbb C^5$ 的 **四维** 编码，按原合同处理辅助 $|010\rangle$。
对任意有限 $K$，每个原语 $m$ 扩为 $\widetilde m=m\oplus V_m$、$V_m\in U(K)$，且 $\widetilde\iota=J_0\iota$、$J_0:\mathcal H\hookrightarrow\mathcal H\oplus K$。
若原字 $W=m_s\cdots m_1$ 每个前缀保码且 $W\iota=e^{i\gamma}\iota U$，则直接使用供应等式

$$
\widetilde W=W\oplus V_{m_s}\cdots V_{m_1},\qquad
\widetilde W\widetilde\iota=e^{i\gamma}\widetilde\iota U.
$$

它对每个前缀和脉冲中途成立，张量每个有限被动参考仍给完全相同的逻辑联合通道；效果 $\widetilde F$ 对应原效果 $J_0^\dagger\widetilde FJ_0$，迹配对相同。
参数取 $K=\mathbb C^r$ 给任意 $5+r$ 环境维数而不改变这些响应。
这个合同不是 §29 的三维码 $B:\mathbb C^3\to\mathbb C^5$；也不包含跨编码与辅助或新隐藏块的相干干涉权限，后者需另给相位资源。
由此两类不同输入任务都说明可见响应不提供隐藏总维数上界，但不能把四维编码的证明直接套给三码。

同一选择映射上的误差可定量控制。若 $\rho,\sigma$ 为态、$\operatorname{Tr}\Lambda(\rho),\operatorname{Tr}\Lambda(\sigma)\ge s_0>0$，则

$$
\left\|\frac{\Lambda(\rho)}{\operatorname{Tr}\Lambda(\rho)}-
\frac{\Lambda(\sigma)}{\operatorname{Tr}\Lambda(\sigma)}\right\|_1
\le\min\{2,\ 2\|\rho-\sigma\|_1/s_0\}. \tag{31.1}
$$

置 $X=\Lambda(\rho),Y=\Lambda(\sigma),p=\operatorname{Tr}X,q=\operatorname{Tr}Y$。
分解 $X/p-Y/q=(X-Y)/p+Y(1/p-1/q)$ 得上界 $(\|X-Y\|_1+|p-q|)/p\le2\|X-Y\|_1/s_0$。
CP 迹不增对自伴差迹范数收缩：用差的正负分解，各正部分的输出迹至多原迹，再用三角不等式。
归一态差范数至多二，得 (31.1)。这里必须是共同的 $\Lambda$；两个不同模型若有不同选择映射，还须先控制未归一输出差。
本卷命题 19.3 已供应有限网络、全参考返回误差的后选择放大；(31.1) 是同图同映射、仅初态不同这一较窄接口的显式形式。
小成功率能放大误差，但不因此把所有突变都判为新动力学。

**应用 31.2（记录正交性和条件 Bloch 三方向）。** 本卷定理 10.4 已给无扰动记录恒等式：若等距 $V$ 满足
$V(|\psi_i\rangle|r\rangle)=|\psi_i\rangle|r_i\rangle$，则

$$
\langle\psi_i,\psi_j\rangle
=\langle\psi_i,\psi_j\rangle\langle r_i,r_j\rangle. \tag{31.2}
$$

其参数是同一未改动的源纯态与共同空白记录；内积保持直接证明等式。
非正交时 $\langle r_i,r_j\rangle=1$，严格保持相位的约定下记录相同，不会新增可区分记录。
反向对任意有限正交组定义 $V|i\rangle=|i\rangle|i\rangle$，线性延拓为等距，即可留任意多个正交记录。
此机制解释记录为何筛选某些区分，未限制结果数为三；环境冗余还需子系统划分、可访问性与实际复制关联（Zurek，*Quantum Darwinism*，[arXiv:0903.5082](https://arxiv.org/abs/0903.5082)）。

若另已确定有效访问代数为 $M_2(\mathbb C)$，本卷推论 10.1 的 Pauli 参数取 §25 的 $X,Y,Z$，每个态唯一写为

$$
\rho=\tfrac12(I+r_xX+r_yY+r_zZ),\quad r\in\mathbb R^3,\quad\|r\|\le1.
$$

$I,X,Y,Z$ 是自伴空间正交基，迹一固定单位方向；$(r\cdot\sigma)^2=\|r\|^2I$ 给本征值 $(1\pm\|r\|)/2$，故正性正好是单位球。
有限维复 $C^*$-代数的最小非交换单块确为 $M_2$；这里三个方向是非交换读出坐标，不是三个互斥态，也不来自一般幸存选择。
三码系统的归一态有八个实参数，不能改称 Bloch 球或三维物理空间。∎

## 32. 可修订概念的纤维、连续查询与共同响应维数

**定义 32.1（候选世界和共同概念）。** 一个世界 $\omega$ 指定类型与代数或核、态、读口、控制、观察者记忆及记录译码；它也可把对象划分、尺子和“稳定”的标准作为候选内容。
仍须一个共同测试合同 $\mathfrak T$，使各世界的 $P_\omega^\pi$ 在相同结果语义中比较；若合法性未知，明确包含失败结果或仅取共同合法域。
证据保留非空相容集 $K_h$，概念查询为同一语义函数 $f:\Omega\to Y$，预测是集合 $f(K_h)$。
未给世界权重时，不对该集合擅自取概率平均。

**应用 32.2（概念识别与剩余宽度）。** 本卷命题 14.3 的全部共同响应取
$R_O(\omega)=(P_\omega^\pi)_{\pi\in\mathfrak T}$，其等价 $\omega\sim_O\omega'$ 就是 $R_O(\omega)=R_O(\omega')$。
概念 $f$ 由这些完整响应唯一确定，当且仅当它在每个等价类常值；此时

$$
f=\bar f\circ q,\qquad q:\Omega\to\Omega/{\sim_O},
\quad\bar f([\omega])=f(\omega). \tag{32.1}
$$

常值性恰给良定义，商映射满射给唯一性；反向由因子化立即得同响应同概念。
这应用于“点还是边”“哪个关系稳定”“有效维数”等已经对齐的查询，不表示存在有限样本算法或可实现 CPTP 压缩。
后来新增读口会细分旧纤维，必须重新检查 (32.1)，不能静默沿用旧等价。

连续查询的有限精度结论由[预测波命题 28.2](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md)直接供应。
精确参数取该命题的紧度量世界空间为本节 $\Omega$、闭非空嵌套相容集为 $K_n$、查询为连续 $f:\Omega\to(Y,d_Y)$；则

$$
K_\infty=\bigcap_nK_n\ne\varnothing,\qquad
\operatorname{diam}f(K_n)\downarrow\operatorname{diam}f(K_\infty). \tag{32.2}
$$

$Y$ 可为任意度量空间，不限实数。若菜单 $Q_0$ 本身非空紧度量，且 $F:Q_0\times\Omega\to Y$ 联合连续，供应还给

$$
\sup_{q\in Q_0}\operatorname{diam}F(q,K_n)
\downarrow\sup_{q\in Q_0}\operatorname{diam}F(q,K_\infty). \tag{32.3}
$$

在每层紧集上选达到直径的点对（及菜单点），取收敛子列，嵌套闭性使极限落在交集；连续性给等式，包含关系给反向不等式。
这个参数化应用保留了供应的完整 metric-valued 域，不将它重新列为一个新紧性定理。
特别地，任意正查询精度最终可达，当且仅当查询在极限纤维上常值；不要求世界本身唯一。
这仍是语义存在结论，没有提供可算停止层数或采样成本。

对经典窗口，使用[静态接缝定义 33.1、命题 33.2、33.4–33.5](AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md)：
参数是其独立五事件 $L(b,c)$、过滤 $e^{-sL}$、增益阈值 $\varepsilon$，不是 $\mathcal G$ 或 $\mathcal T$。
$c>b$ 时恰保三几何可见方向的区间是 $\ell/(4c+b)<s\le\ell/\max(2c+b,5b)$；$c=2b$ 给同速 $5b$ 与高率 $9b$。
对同一合法实对称 Laplacian 的 $\Delta\mathbf1=0$、$\|\Delta\|\le\eta<2b$，供应的应用结论给 $\ell/(9b-\eta)<s\le\ell/(5b+\eta)$ 和整体低簇投影差至多 $\eta/(4b-\eta)$。
合法性仍须非对角非正、零行和及对称，不能由范数界推断；常数模态始终保留，簇内命名轴可以改变。
$c=b$ 有阈值并列不能恰选三；$c<b$ 的三慢方向可含原隐藏模态而丢掉 $e_z$。
这些是指定过滤的有限分辨窗口，不是三个方向永久不衰减：有限 $s$ 的精确增益都非零，无限过滤只剩常数，硬投影还有原命题 30.12 的负概率反例。
输入须激发相应符号模态、概率实现须取均匀附近小扰动、离散许可参数须实际落入窗口，以上都由该 owner 保留。

从 (32.2) 推出“有效维数连续”仍需谱隙或离阈值裕量：阈值等号处模态数会跳变。
精确固定性、无限全称句、零振幅处的相位也未必连续，不能直接套用该命题。
在有谱隙的紧参数子类上，谱投影连续；再与本节的查询宽度配合，才能控制同一几何概念的剩余变化。
§30 的双世界则提供另一具体消费：原效果查询宽度全零，而 diamond 度量的后继查询宽度仍为 $4t\sqrt{1-t^2}$，所以原菜单不能完成该后继概念识别。

**应用 32.3（带噪共同响应排除低维实现）。** 设 $m$ 个效果 $0\le F_i\le I$ 和 $n$ 个态 $\rho_j$ 确属同一个 $d$ 维复模型，$H_{ij}=\operatorname{Tr}(F_i\rho_j)$。
在 $d^2$ 维实自伴空间取 Hilbert–Schmidt 正交基，将效果及态系数分别组成矩阵，得 $H=AB$，所以 $\operatorname{rank}_{\mathbb R}H\le d^2$。
若 $|H_{{\rm obs},ij}-H_{ij}|\le\epsilon$ 对每项成立，则

$$
\|H_{\rm obs}-H\|_{\rm op}\le\|H_{\rm obs}-H\|_F\le\epsilon\sqrt{mn},\qquad
\sigma_k(H_{\rm obs})>\epsilon\sqrt{mn}
\ \Longrightarrow\ d\ge\lceil\sqrt k\rceil. \tag{32.4}
$$

最后一步用标准奇异值极小极大扰动界 $\sigma_k(H)\ge\sigma_k(H_{\rm obs})-\|H_{\rm obs}-H\|_{\rm op}>0$。
严格大于不能换成大于等于；等号不能排除真实奇异值为零。共同实现是秩分解的必要前提，每项各找一个无关世界不产生该结论。

给这个证书一个本应用的实际数学消费者：在 §29 的同一三码 $M_3$ 上，**若另供**下述九个准备和九个效果，则共同响应可排除任何二能级共同模型。
取矩阵单位 $E_{jk}$、$1\le j,k\le3$，令 $H_1,\ldots,H_8$ 是六个 $E_{jk}+E_{kj}$、$-i(E_{jk}-E_{kj})$（$j<k$），以及 $\operatorname{diag}(1,-1,0)$、$\operatorname{diag}(1,1,-2)/\sqrt3$。
它们迹零、$\operatorname{Tr}(H_jH_k)=2\delta_{jk}$、$\|H_j\|\le2/\sqrt3$。置 $a=1/8$，

$$
\rho_0=I_3/3,\quad \rho_j=I_3/3+aH_j,\qquad
F_0=I_3,\quad F_i=I_3/2+H_i/4\quad(1\le i,j\le8). \tag{32.5}
$$

$1/3-a(2/\sqrt3)>0$ 保证准备为态，$\|H_i/4\|<1/2$ 保证效果合法；虚方向效果是额外相位资源，未声称原实菜单可达。
直接迹配对得九乘九响应

$$
H=\begin{pmatrix}1&\mathbf1^{\mathsf T}\\
\tfrac12\mathbf1&\tfrac12\mathbf1\mathbf1^{\mathsf T}+\beta I_8
\end{pmatrix},\quad\beta=a/2=1/16,
\quad H=L\operatorname{diag}(1,\beta I_8)U,
$$

$$
L=\begin{pmatrix}1&0\\\tfrac12\mathbf1&I_8\end{pmatrix},\qquad
U=\begin{pmatrix}1&\mathbf1^{\mathsf T}\\0&I_8\end{pmatrix}. \tag{32.6}
$$

减去首行一半即可见 $\det H=\beta^8\ne0$；因此真实秩九已排除 $d=2$ 的上界四。
为使证书能承受明确误差，$\|L^{-1}\|\le1+\sqrt2$、$\|U^{-1}\|\le1+2\sqrt2$，因为各自偏离单位的单块范数为 $\sqrt2,2\sqrt2$。
所以

$$
\sigma_9(H)\ge\gamma:=\frac{\beta}{(1+\sqrt2)(1+2\sqrt2)}>0.
$$

若同一响应的每项采集误差至多 $\epsilon<\gamma/18$，则 $\sigma_9(H_{\rm obs})\ge\gamma-9\epsilon>9\epsilon$，(32.4) 取 $k=9$ 给任何与该误差合同相容的共同模型 $d\ge3$。
这是一项有限准备—效果接口的充分应用，不是已取得这些准备或层析的声明。
它既不给隐藏总维上界，也不把三码的八参数等同于三根物理轴；增加直和隐藏环境仍与同一可见响应相容。∎

## 33. 实际四视图与原 PDE 读口的精确消费

**应用 33.1（准备相位上的四种表达）。** 取[原生叶边界定义 21.1、定理 21.2–21.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION.md)的实际安装、原有序材料树、单位邻接法则、源绑定、当前权利和已取得端点 onset 数据 $\sigma(t)$。
真实执行 Reset 后 Add$(1,1)$，以该 Add 完成处为原点 $o$；从 $o$ 到所考察切面无增长、Reset 或非零 Add，场只由实际 Tick 更新，Reads、Holds 可穿插。
取每个符合此条件的有限被动前缀，年龄 $k\ge2$ 是实际 Tick 链的长度，不是物理时长或全部事件计数。
切面须实际收到连续相邻被动 epoch $k-1,k$ 的两次 Read$(1)$，且第二次后无 Tick；两次同 epoch 的重复读不满足条件。
保留的预测器已同步。上述条件正是供应的 $\mathcal P_2$，不由两个数值反推出权限、准备或来源。

参数 $t$ 是已建递归项，$A_t$ 是其单位邻接，$e=e_{\ell_1}$ 是真实单位源，$x_k=A_t^ke$，$m_r=e^{\mathsf T}A_t^re$。
四个视图的对应为

| 视图 | 在实际像上暴露的供应数据 |
| --- | --- |
| Space $\mathsf S$ | 无根单位材料树、有序端点、完整当前场，模保持端点序的同构 |
| Time $\mathsf T$ | 实际带标签 LAB 出生/生命周期偏序 $E(t)$，及从 $o$ 起实际 $k$-Tick 链的序型 |
| Boundary $\mathsf B$ | 已取得的 $\sigma(t)$ 与字面末端相邻样本 $(m_{k-1},m_k)$ |
| Memory $\mathsf M$ | 在原绑定且具权利的入口保留的递归项、当前预测向量和端点序号表 |

供应定理 21.2 的同一对象 $Q$ 就是实际达到的三元组集合 $\{(t,k,x_k):\text{上述条件成立}\}$；每个观察 $V_i$ 的恢复映射 $D_i$ 在其实际像上给同一个三元组。
从 Space 用树恢复 $t$，以完整场恢复年龄；从 Time 用真实 LAB 偏序恢复 $t$，实际链长给年龄，准备与被动性再给 $A_t^ke$。
从 Boundary 用 onset 恢复 $t$、用实际相邻样本对恢复 $k$；从 Memory 的已同步向量算同一前向样本对，再恢复 $k$。
年龄逆的供应是定理 19.3：$m_{2n+1}=0,s_0=s_1=1,s_{n+1}>s_n$（$n\ge1,s_n=m_{2n}$），从而 $k\mapsto(m_{k-1},m_k)$ 在 $k\ge2$ 单射；$p_1=p_3=(1,0)$ 说明不能扩到所有正年龄。
恢复不要求 $A_t$ 可逆或单位源循环，也不恢复偏序的某个指定线性扩张。

每条转换均是供应证明中已经使用的 $C_{ji}=v_jD_i$，其中 $v_i:Q\to V_i(Q)$ 是实际视图编码，$D_iv_i=\operatorname{id}_Q$。
因此 $C_{lj}C_{ji}=v_lD_jv_jD_i=v_lD_i=C_{li}$；在实际像上 $C_{ij}C_{ji}=\operatorname{id}$。
这是供应的通路一致性在当前概念翻译中的直接消费，不新增一个泛用图册生产者。
未找到解码不证明信息丢失；反之实际非单射视图才是针对 $Q$ 的有损商。
同数值重算不执行新的 Read，也不补回丢失的原测量来源；计算链长也不重建旧物理事件。

接续用同一供应定理 21.3，而不止当前数据相等。宏 $\mathrm{Tick};\mathrm{Read}(1);\mathrm{Hold}$ 给完整 Tick 确认、字面 $m_{k+1}$ 和 Hold 确认，实际场变为 $A_tx_k$，保留对变成 $(m_k,m_{k+1})$，四个后继都恢复 $(t,k+1,A_t^{k+1}e)$。
在固定绑定与权利下，任一视图相等恰有供应 Assumption 10.2 的完整有限自适应接续核：同三元组给同回复及相应后继；异项可由 Reset 后 onset 测试分开，同项异年龄可由 Read、Tick、Read 的前向样本对分开。
非零 Add、Reset 或成功增长破坏这里的准备相位，不能继续套用这个被动年龄逆；完整原动作预测器仍按供应定理 12.2 工作。
这把“几何、时间、边界、记忆是同一预测对象的表达”限定到其真实域，并保留额外继续操作的合同。

**应用 33.2（已供应无逃逸结论与概念稳定性的拓扑）。** 原 PDE 的对象不是五事件 Laplacian，也不是 §29 的量子通道。
本卷定义 23.1、应用 23.2 已消费[全息附录原定理 105.1](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX.md)；这里保持同一个供应范围：
群 $G=\mathrm H^1\times\mathbb R$、原 Haar 测度 $d\mu$、单位元源 $e$、原 $-3$ 次 Green 权重 $\Gamma$、原自由算子 $L,D_w$ 及谱单位、固定 $a,\eta>0$。
对每个 $\sigma_n>2\to2$，任意选实际达到的非零临界零态 $u_n$，只作振幅归一 $V[u_n]=\int\Gamma|u_n|^2d\mu=1$，不以试探态或坐标重标定替代。
它们在原复形式域满足定义 23.1 的弱方程。令 $M_n=\|u_n\|_2^2>0$、$v_n=u_n/\sqrt{M_n}$，同一实际态有两个读口

$$
\mu_n=|v_n|^2d\mu,\qquad \nu_n=\Gamma|u_n|^2d\mu=M_n\Gamma\mu_n.
$$

原供应 103.3 给 $M_n\to0$，104.5 给移动球两读口分离，105.1 给

$$
\lim_{R\to\infty}\limsup_{n\to\infty}\mu_n\{\rho>R\}=0,\qquad
m_\infty=0,\qquad \|v\|_2^2+m_e=1 \tag{33.1}
$$

其中最后的分解沿原定理 104.2 的同时子列，$\rho$ 是原齐次范数。
同一弱态子列对每个固定有界、在 $e$ 邻域消失的可测截断 $\zeta$ 有 $\zeta v_n\to\zeta v$ 于原 $L^2$ 强拓扑。
本应用不把 $m_\infty$ 重新列作未知，也不从无逃逸推出 $m_e$ 的数值、非零弱剖面、唯一形状或其可达性。
单点紧化测度的弱收敛、固定中心谱单位的窄收敛、原态的 $L^2$ 或形式域收敛是不同查询拓扑；$u_n\to0$ 不自动给归一 $v_n$ 的概率结论。
因此 (33.1) 是“稳定必须指定源、态与读口拓扑”的既有实例，不是由一般观察性推出物理三维或量子原则的桥梁。∎

## 34. 完整关系重建的充分接口与开放方向

**定义 34.1（本应用的共同重建对象）。** 取

$$
\mathfrak R=(\text{合法类型与组合},\{\ell_\omega\},
\text{跨核与共同参考},\text{完整分支与标定读出},
\text{有限观察者合同},K_h).
$$

作为本卷定义 12.1、20.2、24.1 的关系表示实例，其充分接口如下；这些条件不声称逻辑独立或最小。

1. 每个输入输出类型、接续词、保留端口和记录的同一性已规定。局部复合可非交换，无全局钟不删去方向；不同表示须保相同类型与组合关系。
2. 同一边界的全部复词矩满足 (26.1)，包括伴随、正性及每个生成元有限非负界；跨描述相干须有 (27.1) 的完整正块与共同比较，而不只是各自内部权重。
3. 每个合法前缀有完整有限分支，包括失败、停止及隐藏 Kraus 下标，满足 (26.3)。分支提升保持所声称的全部交叉关系；(26.4)–(26.5) 给相容未归一柱权重，条件化只在正权重处进行。
4. 每个声明为量子过程的有限矩阵边界映射，对每个有限复参考 $M_n$ 及所有联合正输入均正，即完全正；在输入 $M_d$ 时标准 Choi 准则检查 $n=d$ 足够。各分支迹不增、分支和保迹，混合来源相融；这些形式合法性不自动授予实验参考、控制或环境资源。
5. 状态、效果和权重与实际概率采用同一归一及加权标定；全效果赋值的相容可加性按本卷定义 5.2、定理 5.3 给 Born 形式。$\|\pi(m)\Omega\|^2$ 的代数表达不以“未知”替代频率合同。
6. 观察者的控制、精度、记忆、共同测试及模型类明确；应用 28.2 的词域完整、来源量词符合所用维数结论。修订 $K_h$ 或扩充菜单后，重新检查纤维、未来闭包和查询的连续性条件。

**应用 34.2（表示、稳定与可实现性的条件综合）。** 在同一个满足定义 34.1 的模型中，(26.2) 构造有界循环表示，(26.3) 给分支等距，(26.5) 给平方权重与条件正泛函，有限矩阵及参考接口给 CP 仪器。
这是本卷 §§6、7、12 的充分重建链在有向词输入上的应用；它不是从裸图或一般不确定性无条件推出全部量子理论。
保全全部词矩与标记操作的最小表示由应用 26.2 唯一酉交织；仅保一个交换切面则只有 (25.1) 的经典限制，不能省略跨切面方向、参考或上下文条件。
(27.1) 说明为什么概念候选的共同物理相干还需新关系和控制，(28.2) 则检验给定概念译码是否保全部许可未来回复。

在其稳定子任务中，(28.3) 判菜单可见平衡；忠实不变密度下的 (28.4) 控制普通组合。
缺少忠实性时，§29 的同一实际 $\mathcal G$ 由 Half-Gram 供应返回两标量代数，不能把普通效果 $J$ 当投影，也不能将 EB 极限当任意三码量子信息的保留。
§30 的实际符号世界使全部原深度效果仍相同而后继关系有非零宽度；§32 的共同响应证书在另供准备和效果时给最低模型维数，既不提供隐藏总维上界也不宣称已经取得层析。
静态接缝 §33 的独立经典窗口给“有效三方向”一个合法概率实例，保留谱隙、阈值、扰动合法性、输入激发和参数可达性的条件。
§33 的四视图则在真实准备/被动域保同一个 $(t,k,x_k)$ 与许可接续；PDE 读口保留它自己的实际源、形式域与概率拓扑。
所有应用的组合都只在各自供应的共同实现与接口上成立，不能将分别可实现的最优值拼成未经证明的同时实现。

数学归属。§26 的新增承重点是有界生成元代数输入与完整条件泛函在该重建接口中的闭合桥梁；GNS 为已归属的中间机制。
§27 使用 Watrous 的奇异块分解定位跨候选关系及实际相干资源的缺项，未将标准分解当作新定理。
§§25、28、31 的上下文、乘法域、正交记录和 Bloch 事实分别为标准工具或本卷既有结果；此处保留其在关系概念任务中的条件及定量消费。
§29 全固定系统、非普通乘法、返回乘法和含参考 EB 皆来自 Half-Gram 6.1；§30 的双世界、距离和风险来自预测波 29.1–29.3；§32 的紧度量查询来自该卷 28.2，四视图和 PDE 来自 §33 明列的供应。
本应用的定量响应证书有 (32.5)–(32.6) 的具体共同响应消费者；经典窗口和低簇扰动推导在静态接缝 §33 归位。
这些是已归属工具的条件应用与仓内综合推导，不因符号或组织改变而主张文献首创。

本关系应用保留以下三个开放方向，它们不作为前面条件数学结果成立的附加前置。

1. **原生相位读口。** 对固定安装、许可等待/读出/Stop、辅助和参考限制，能否给一条真实可执行操作链取得 §30 的 $E_y$，并量化误差与成本？它的数学合法性和双世界响应已给；重复原实菜单不能供应虚交叉项或独立相位参考。
2. **原生窗口选择。** 原生粗粒化能否实际实现静态接缝 §33 的八棱 $L(b,c)$，取得 $c>b$ 的分离、是否进一步取得 $c=2b$ 的同速，并使允许的离散过滤参数落入严格/弱端点的窗口？已有窗口与合法扰动证明不决定这个实现桥梁。
3. **概念翻译的未来闭合。** 对候选图、谱与记忆表达，能否在同一合法控制、记录、参考和来源合同中构造满足 (28.2) 的最小观察商及可取得的翻译？匹配当前人口不够；实际四视图只解决其声明域，响应秩证书只在共同模型和误差界下给下界。

这三问分别要求新操作资源、原生过滤机制及保全未来关系的翻译，不由一般稳定、循环向量或三根可见轴替代。∎

## 追加锚（本行以下为增补区）

## 35. 符号相位效果的普适障碍与共同原生区分

**定义 35.1（有序识别下的两个实结构）。** 沿用定义 30.1 的 $B,U,f,q,g=Uf,a=Uq,S_\pm$ 和 $E_y$。
另作字面有序识别：将该仪器的物理基 $(e_0,\ldots,e_4)$ 逐项对应定义 20.1 的 $(e_N,e_2,e_3,e_5,e_{25})$，即[预测波 §5](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md)的位置标签 $m=(0,1,2,3,13)$。
这是两个数学载体的对应前提，不供应物理端口映射或 $S_\pm$ 的安装。
取定义 20.1 的固定 $K=\mathsf K$、$D=\operatorname{diag}(1,i,i,i,1)$，以 $V(s)=e^{-isK}$ 表示五维等待；$U$ 仍是三维置换，不是 $V$。

允许输入为任意复密度矩阵 $\rho\in M_5(\mathbb C)$。
原生菜单仅有 $s\ge0$ 的 $V(s)$、完整秩一读取 $\mathcal J_j(X)=P_jXP_j$（$P_j=e_je_j^\dagger$）、Stop、有限记录反馈及输入无关的可测经典随机化。
每条记录保留全部读取标签及最终 Stop；失败事件若由记录命名，其质量仍计入总质量。
经典合并记录不改成保持粗块相干的 Lüders 读取；不增加量子辅助、参考、复制、独立相位或任意正交控制，也不授予输入制备。

物理坐标实效果与 $D$ 帧实效果分别指 $F=\overline F$ 与 $D^\dagger FD=\overline{D^\dagger FD}$，二者不同。
§30 的擦除 Kraus 菜单使用前者；本原生菜单使用后者。
固定基实操作的约定见 [Wu 等的文献说明](../../../Library/Quantum/wu2021imaginarity.md)及其[伴随论文 §III](https://arxiv.org/abs/2103.01805v1)；允许全部实 Kraus 操作的资源理论不把这些操作加入这里的固定菜单。

为给出本源的精确参数对应，置

$$
x=\frac{\sqrt2+1}{\sqrt{12}},\qquad y=\frac{\sqrt2-2}{\sqrt{12}},\qquad
G=Bg=\begin{pmatrix}1/2\\0\\-1/\sqrt2\\1/2\\0\end{pmatrix},\qquad
H=Ba=\begin{pmatrix}x/\sqrt2\\y/\sqrt2\\x\\x/\sqrt2\\y/\sqrt2\end{pmatrix}.
\tag{35.1}
$$

由预测波 §17.1 的 $B=((e_0+e_3)/\sqrt2,(e_1+e_4)/\sqrt2,e_2)$ 和 $U$ 交换末两坐标，得到 (35.1)，且 $G^\dagger G=H^\dagger H=1$、$G^\dagger H=0$。
依定义 30.1 及应用 30.2，在 $0<t<1$、$\alpha_t=\sqrt{1-t^2}$ 下，

$$
\rho_{t,\pm}:=S_\pm(ff^\dagger)=\psi_{t,\pm}\psi_{t,\pm}^\dagger,
\qquad\psi_{t,\pm}=\alpha_tG\pm itH,\qquad
E_y=\tfrac12(G+iH)(G+iH)^\dagger.
\tag{35.2}
$$

**命题 35.2（同一源的普适实现障碍和参数无关测试）。** 在定义 35.1 的识别及菜单下：

1. 不存在一个许可有限协议及其记录事件，能对全部复密度输入 $\rho$ 给出 $\operatorname{Tr}(E_y\rho)$。
2. 同一个协议“等待 $\tau=1/100$，完整读取五标签，随后 Stop”，以记录 $(0,\mathrm{Stop})$ 为事件，对每个 $0<t<1$ 都满足

$$
p_{0,+}(\tau)-p_{0,-}(\tau)>
\frac3{250}\,t\sqrt{1-t^2}>0.
\tag{35.3}
$$

这里等待、事件和控制均与 $t$ 及未知符号无关。全部终端记录恰为 $r_j=(m_j,\mathrm{Stop})$、$0\le j\le4$，其质量为

$$
p_{j,\pm}(\tau)=|e_j^\dagger V(\tau)\psi_{t,\pm}|^2\ge0,
\qquad\sum_{j=0}^4p_{j,\pm}(\tau)=1.
\tag{35.4}
$$

其余四标签保留为补事件，质量 $1-p_{0,\pm}$；停止总质量为一，失败质量为零，不作后选择。

证明。普适障碍使用命题 11.7 及[静态相融纤维 §9.3](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)的完整记录闭合结果：所有许可事件效果在 $D$ 帧实对称，Stop 及完整失败事件、输入无关随机混合也保持此性质。
其首读后缀为输入无关的归一概率核；零质量前缀直接乘零，无须条件化。
本源的具体残差为

$$
(D^\dagger E_yD)_{01}
=\frac{\sqrt3-\sqrt6}{24}-i\frac{\sqrt2}{48}.
\tag{35.5}
$$

例如取 $\eta_\pm=(e_0\pm ie_1)/\sqrt2$、$\sigma_\pm=D\eta_\pm\eta_\pm^\dagger D^\dagger$。
二者均为合法密度输入，$\operatorname{Re}(D^\dagger\sigma_+D)=\operatorname{Re}(D^\dagger\sigma_-D)$，所以全部许可记录及随机事件同律；但 (35.5) 给

$$
\operatorname{Tr}\bigl[E_y(\sigma_+-\sigma_-)\bigr]=\frac{\sqrt2}{24}\ne0.
\tag{35.6}
$$

故不能在全部复输入上实现该效果。这里的全输入量词并未被限制为实态或这两个见证态。

对第二条，采用实际固定等待，而不将效果的线性张成当作可执行效果。其被动生成元为

$$
A=D^\dagger(-iK)D=
\begin{pmatrix}
0&1&1&1&0\\-1&0&0&0&-1\\-1&0&0&0&0\\-1&0&0&0&-1\\0&1&0&1&0
\end{pmatrix},\qquad O(s)=e^{sA}=D^\dagger V(s)D.
\tag{35.7}
$$

$A^{\mathsf T}=-A$，故 $O(s)$ 实正交。令

$$
M=2i(HG^{\mathsf T}-GH^{\mathsf T}),\qquad
C_0=\operatorname{Re}(D^\dagger MD),\qquad
d(s)=(O(s)C_0O(s)^{\mathsf T})_{00}.
\tag{35.8}
$$

由 (35.2)，$\rho_{t,+}-\rho_{t,-}=t\alpha_tM$，故 $p_{0,+}(s)-p_{0,-}(s)=t\alpha_td(s)$。
将 (35.1) 代入得到

$$
(C_0)_{00}=(C_0)_{03}=0,\qquad
(C_0)_{01}=\frac{\sqrt3-\sqrt6}{6},\qquad
(C_0)_{02}=\frac{\sqrt3+\sqrt6}{3},
$$

$$
d(0)=0,\qquad d'(0)=(AC_0-C_0A)_{00}
=\sqrt3+\frac{\sqrt6}{3}>2.
\tag{35.9}
$$

$M$ 的非零本征值为 $2,-2$，所以 $\|M\|_1=4$。
记 $X=D^\dagger MD$，则 $C_0=(X+\overline X)/2$，迹范数的凸性和酉不变性给 $\|C_0\|_1\le4$。
又 $\|A\|_{\mathrm{op}}^2\le\|A\|_{\mathrm F}^2=10$，从而

$$
|d''(s)|\le\|[A,[A,C_0]]\|_1
\le4\|A\|_{\mathrm{op}}^2\|C_0\|_1\le160.
$$

Taylor 余项对同一个 $\tau=1/100$ 给

$$
d(\tau)\ge\tau d'(0)-80\tau^2
>\frac2{100}-\frac{80}{10000}=\frac3{250}.
\tag{35.10}
$$

因 $t\alpha_t>0$ 得 (35.3)。$V(\tau)$ 酉且 $\psi_{t,\pm}$ 单位化，故完整五标签质量和为一，得到 (35.4)。∎

本命题只将既有实帧闭合与符号世界应用于这些固定矩阵，未将一般实操作理论重立为新定理。
$\rho_{t,+}$ 与 $\rho_{t,-}$ 在物理坐标中实部相同，但其 $D$ 帧实部之差为 $t\alpha_tC_0\ne0$；因此两菜单的区分能力不同。
§30 的坐标实菜单同律结论仍成立；§34 的 $E_y$ 取得问题在这个指定菜单上的普适精确实现由第一条排除，指定符号对的统计区分则由第二条给出。
概率差不等于有限样本必定判对，且下界在 $t\downarrow0$ 或 $t\uparrow1$ 趋零，不供应全参数统一正间隙。

这两个数学结论均不提供 $ff^\dagger$ 或输出态的原生制备、物理 $S_\pm$、端口对应、重复样本、时钟精度或资源成本；$\tau$ 仍为无量纲等待参数。
固定 $D$ 只改坐标，不授予独立相位参考。要越过第一条须改变其操作或输入合同，并另证获得的资源；第二条仅在同一已识别载体且给定相应输入时成立。
定义 34.1 的强正性、共同组合与参考相容性仍是量子重建的前提，不由这一对状态的区分推出。

## 追加锚（本行以下为增补区）

## 36. 同一被动等待的极分解与完整原生读取的不相容

**定义 36.1（物理载体、极支撑与操作下降）。** 固定定义 20.1、35.1 的同一个 $K,D,A$，物理载体仍为 $\mathcal H_{\rm phys}=\mathbb C^5$，标签顺序仍为 $(N,2,3,5,25)$。在 $D$ 帧记 $V=\mathbb R^5$，其物理像 $DV$ 是实五维子空间；物理载体的全实化 $(\mathcal H_{\rm phys})_{\mathbb R}$ 则是实十维，两者不同。只用原来的非负等待、完整读取、Stop、有限记录反馈和输入无关随机化，不增加制备、相位参考、辅助或控制。
置

$$
z=\frac{e_2-e_5}{\sqrt2},\qquad R_0=zz^T,\qquad P=I-R_0,\qquad
E=z^\perp\subset V,\qquad E_{\mathbb C}=E+iE\subset\mathbb C^5.
\tag{36.1}
$$

这里 $E_{\mathbb C}$ 使用物理表示已经供应的复数域；它不等于在实四维 $E$ 上另选 $J^2=-I_E$ 所得的内部复二维空间 $E_J$。内部射线识别单位向量 $u$ 与 $e^{\theta J}u$。若以 $E_J$ 表示同一系统，全部保留记录的概率必须在这些射线上恒定，实际分支还须保持所声明的支撑。实线性控制作为复线性控制须与 $J$ 交换；这些要求不能由等待独自保持 $J$ 替代。物理全实化已有的复结构 $J_0\psi=i\psi$ 也不等于 $V$ 上的一个算子。

**命题 36.2（实际极射线的记录分离及读后零模质量）。** 在定义 36.1 的对象与菜单中成立以下三项。

1. $\ker A=\mathbb Rz$，$A$ 的规范极分解为 $A=\widetilde J_p|A|$，其中

$$
\begin{aligned}
n&=\sqrt{5+2\sqrt2},\\
\widetilde J_p&=\frac{A\bigl((5+\sqrt2)I+A^2\bigr)}{\sqrt2\,n},\\
\widetilde J_pz&=0,\qquad \widetilde J_p^T=-\widetilde J_p,\qquad
\widetilde J_p^2=-P,\qquad [\widetilde J_p,A]=0.
\end{aligned}
\tag{36.2}
$$

故 $J_p=\widetilde J_p|_E=A|_E(-A^2|_E)^{-1/2}$ 是 $E$ 上的正交复结构，所有等待 $O(t)|_E$ 都与之交换。它不是全 $V$ 上的复结构。若改在物理全实化上对 $-iK$ 作规范极分解，其极因子是 $D\widetilde J_pD^\dagger$ 的物理复线性延拓，核为复线 $D\mathbb Cz$，支撑为 $DE_{\mathbb C}$；该支撑实八维，作为内部复空间是四维，仍非 $E_{J_p}$。

2. 取两个明确物理输入 $Dx,Dy$，其中

$$
x=e_N,\qquad y=J_px=-\frac{e_2+(1+\sqrt2)e_3+e_5}{n}.
\tag{36.3}
$$

$x,y$ 均为 $E$ 中的单位向量，在 $E_{J_p}$ 中属于同一复射线，而在原物理载体中为正交输入。协议“立即完整读取，然后 Stop”的全部记录为 $r_j=(j,\mathrm{Stop})$，其两个分布按原标签顺序恰为

$$
p_x=(1,0,0,0,0),\qquad
p_y=\frac{(0,1,(1+\sqrt2)^2,1,0)}{5+2\sqrt2},\qquad
\operatorname{TV}(p_x,p_y)=1.
\tag{36.4}
$$

每个分布总质量为一，Stop 质量为一，失败质量为零，零概率标签也保留。任何给这条内部复射线指定同一个完整记录律 $q$ 的模型均满足

$$
\max\{\operatorname{TV}(p_x,q),\operatorname{TV}(p_y,q)\}\ge\frac12.
\tag{36.5}
$$

效果层面更精确地，令 $w_j\in[0,1]$ 为一次完整读后对结果 $j$ 接受某事件的经典概率。在 $E$ 上压缩的实对称效果为 $F_w=P\operatorname{diag}(w)P|_E$。其概率下降到 $E_{J_p}$ 的复射线，当且仅当

$$
[F_w,J_p]=0
\quad\Longleftrightarrow\quad
w_N=w_3=w_{25}=\frac{w_2+w_5}{2}=:\lambda.
\tag{36.6}
$$

此时 $F_w=\lambda I_E$，概率与输入无关。特别地，五个单标签效果都不下降；确定性合并标签时，只有空事件及全事件下降。先作任何固定等待再读，(36.6) 的判据不变。

3. 对任意物理密度输入，以 $\widehat\rho=D^\dagger\rho D$ 表示，在同一帧的非选择完整读为 $\Phi(\widehat\rho)=\sum_jP_j\widehat\rho P_j$。其物理暗线质量恰为

$$
\operatorname{Tr}\bigl(R_0\Phi(\widehat\rho)\bigr)
=\frac{\widehat\rho_{2,2}+\widehat\rho_{5,5}}2\in[0,1/2].
\tag{36.7}
$$

即使输入支撑满足 $P\widehat\rho P=\widehat\rho$，上端点仍可达到：取 $f=(e_2+e_5)/\sqrt2\in E$、$\widehat\rho=ff^T$，初始暗线质量为零，而

$$
\Phi(ff^T)=\tfrac12(P_2+P_5),\qquad
\operatorname{Tr}\bigl(R_0\Phi(ff^T)\bigr)=\tfrac12,\qquad
\operatorname{Tr}\bigl(P\Phi(ff^T)P\bigr)=\tfrac12.
\tag{36.8}
$$

两个实际分支各以概率 $1/2$ 输出 $e_2$ 或 $e_5$，均离开 $E$，也离开 $E_{\mathbb C}$。原读没有质量损失；事后投回极支撑会丢掉质量 $1/2$，不是同一个完整仪器。因此删除等待的零模不能使原完整读成为极支撑内的仪器。

证明。暗线与旋转频率复用[SecondOrder 定理 63.2](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md)、[静态相融纤维命题 44](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)及[Measurement Relative Quantum Boundary 定理 4.1 的证明](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md)：$V$ 为暗线与两条正交旋转平面的直和，频率平方为 $(5\pm\sqrt{17})/2$。以下计算把该既有分解接到本源的完整读取，不另立谱或控制定理。
只为计算按 $(N,25)\oplus(2,3,5)$ 重排，仍有

$$
A=\begin{pmatrix}0&B\\-B^T&0\end{pmatrix},\qquad
B=\begin{pmatrix}1&1&1\\1&0&1\end{pmatrix},\qquad
C=BB^T=\begin{pmatrix}3&2\\2&2\end{pmatrix}.
$$

$\det C=2>0$、$C_{11}=3>0$，故 $C>0$。由 $C^2-5C+2I=0$ 得

$$
C^{1/2}=\frac{C+\sqrt2 I}{n},\qquad
C^{-1/2}=\frac1{\sqrt2 n}
\begin{pmatrix}2+\sqrt2&-2\\-2&3+\sqrt2\end{pmatrix},\qquad
Q=C^{-1/2}B=\frac1n
\begin{pmatrix}1&1+\sqrt2&1\\1+\sqrt2/2&-\sqrt2&1+\sqrt2/2\end{pmatrix}.
\tag{36.9}
$$

第一式的右端正定且平方为 $C$，第二式为其逆。于是 $QQ^T=I_2$，$Q^TQ$ 是 $(e_2-e_5)^\perp$ 在三坐标块内的投影。令

$$
\widetilde J_p=\begin{pmatrix}0&Q\\-Q^T&0\end{pmatrix},\qquad
H=\begin{pmatrix}C^{1/2}&0\\0&B^TC^{-1/2}B\end{pmatrix}.
$$

$H\ge0$，$H^2=-A^2$，$\widetilde J_pH=A$，且极因子在核上为零，故 $H=|A|$。代入 (36.9) 得 (36.2) 的多项式公式及其余恒等式。这里使用的是成熟极分解工具：[Moretti–Oppio，Theorem 2.18、Proposition 2.19](https://arxiv.org/html/1611.09029v4)明确保留核，只有单射时极因子才是酉的反自伴随算子；其复线性交换判据见 Proposition 2.23。物理全实化的结论由同一个等式的物理复线性延拓得到；原 $J_0$ 保持全部物理复线性读与等待，与把此极因子当作新标量作用是不同的命题。

由 (36.9) 第一行得到 (36.3)，$\|y\|^2=(2+(1+\sqrt2)^2)/n^2=1$，$y_2=y_5$，且 $x^Ty=0$。物理输入的读概率为 $|e_j^\dagger Du|^2=|u_j|^2$，故得 (36.4)。内部乘法 $iu=J_pu$ 却识别 $x,y$，于是三角不等式给 $1\le\operatorname{TV}(p_x,q)+\operatorname{TV}(q,p_y)$，即 (36.5)。这也在物理全实化的极支撑上给出同一射线识别的反例。

对实对称 $F$，射线不变性等价于 $e^{-\theta J_p}Fe^{\theta J_p}=F$，在零点微分得 $[F,J_p]=0$，反向由指数成立。单标签压缩均为非零实秩一效果；非零秩一实对称算子不能与正交复结构交换的既有论证见 [Measurement Relative Quantum Boundary，Corollary 25.1 的证明](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md)。本源的加权判据还可直接计算：在 $(N,25)$ 块 $F_w$ 为 $\operatorname{diag}(w_N,w_{25})$，在 $(f,e_3)$ 块为 $\operatorname{diag}((w_2+w_5)/2,w_3)$。这两个块之间的极映射为

$$
Q_E=\frac1n\begin{pmatrix}\sqrt2&1+\sqrt2\\1+\sqrt2&-\sqrt2\end{pmatrix}.
$$

$Q_E$ 的四项均非零，故两个对角块与它交织当且仅当四个对角值相等，得到 (36.6)。等待与 $J_p$ 交换，等待后效果为 $(O(t)|_E)^TF_w(O(t)|_E)$，故交换判据不变。此处只检验原生效果；没有以效果的线性张成授予额外测量。

最后 $R_0$ 仅在模式 $2,5$ 有对角元 $1/2$。完整读消去非对角项，直接给 (36.7)；正性和迹一给其区间。$f\perp z$，而 $|\langle z,e_2\rangle|^2=|\langle z,e_5\rangle|^2=1/2$，逐分支求和得 (36.8)。这些是给定合法输入的结论，不是这些输入已由原菜单制备的结论。

本命题的 `repo-derived` 承重点是同一个五模式极因子与原生效果、完整记录及读后质量的联合对应。奇数实维障碍已由本卷命题 4.7、定义 20.2 给出；[静态相融纤维 Native57/58/64](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)及 §§19–21 的独立翻转、固定相位控制仍各按其原合同，本命题不重证也不借用那些扩大的权限。§35 的符号态对与普适 $E_y$ 障碍保持原量词；(36.3) 是另一对输入，所检验的是新极射线识别。

因此此极构造供应了等待相容性，但未供应定义 20.2、34.1 所需的共同状态—效果—仪器—组合关系。若采用定义 4.4、定理 4.5 及命题 4.6 的正向路线，还须在同一个操作表示中供应非零事件角、相融矩阵单位、局部复单位及保持它的运输。Moretti–Oppio Theorem 4.3 另要求强连续、不可约且局部忠实的 Poincaré 表示及非负质量平方；两条旋转平面上的本等待没有实例化这些前提。另一条成熟充分路线 [Niestegge，§5 Definition 1、Theorem 1、Corollary 1](https://arxiv.org/html/1402.0158v2)要求在其论文的实有序可观察量空间及乘法合同上，对每个可观察量 $a$ 线性指定 skew order derivation $D_a$，满足 $[D_a,D_b]=-[R_a,R_b]$、$D_aa=0$，再以平方正性取得复 $C^*$ 表示；一只作用在向量上的 $A$ 不是这个对应。概率标定、全参考与并置的其余前提仍按定义 20.2、34.1 保留；[Symplectic 假设 35.3](SYMPLECTIC_PREDICTIVE_COMPLETION.md)的振幅及辛尺度也仍为所给前提。这里排除的是所声明的同系统极射线下降，不排除原物理 $\mathbb C^5$，也不判定另行改变编码、载体或操作合同的表示。∎

## 追加锚（本行以下为增补区）
