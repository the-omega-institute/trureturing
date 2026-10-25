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
