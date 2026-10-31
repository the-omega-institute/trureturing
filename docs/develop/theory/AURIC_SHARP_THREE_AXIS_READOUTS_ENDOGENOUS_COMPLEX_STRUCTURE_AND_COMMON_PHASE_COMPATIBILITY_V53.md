<details>
<summary>原稿元数据（作者设置）</summary>

PDF 标题：AURIC：三轴锐读出、内生复结构与共同相位相容  
PDF 作者：AURIC research continuation  
PDF 主题：Real and complex Hilbert structures, oriented Clifford readouts, phase quotients and internal composition

**原稿编译、字体、编号与页眉页脚设置**

原稿指定 XeLaTeX，编译两次；未安装 Noto CJK 字体时可定义 AURICFontPath。
文类 article，11pt、A4；geometry 页边距 23mm、页眉高度 16pt。
主字体优先 Noto Serif CJK SC；指定字体目录时使用 NotoSerifCJKsc-<wbr>Regular.otf、NotoSerifCJKsc-<wbr>Bold.otf，斜体沿用常规体、粗斜体沿用粗体。否则先查同名字体，再回退 FandolSong-<wbr>Regular.otf、FandolSong-<wbr>Bold.otf，斜体同样沿用常规体与粗体。
等宽字体 Latin Modern Mono；中文断行 locale 为 zh，断行间距 0pt plus 1pt。
数学包为 amsmath、amssymb、amsthm、mathtools、bm、mathrsfs；排版包为 booktabs、array、tabularx、enumitem、fancyhdr、xcolor、needspace，另用 fontspec、geometry、hyperref。
auricblue 的 RGB 为 (24,53,79)；Unicode、彩色链接启用，内部链接、URL、引文均为该颜色。
定义、定理、命题、推论、说明按节共用编号，theoremstyle 为 definition；证明、摘要、书目标题为“证明”“摘要”“固定来源与证明归属”。
段首缩进 1.8em，段间距 2pt，紧急伸长 3em；列表 nosep，左边距 2em。
页眉左侧“AURIC：三轴锐读出、内生复结构与共同相位”，右侧“v53 / 2026-10-31”；页脚居中页码。公式允许分页等级为 2。
标题字号 LARGE、粗体、auricblue；两行间距 7pt，标题与 large 副标题间距 8pt，副标题与日期间距 5pt。
原稿的实数、复数、整数、空间、代数、迹、秩、对角、实化和 bra–ket 简写已在公式中展开；项目链接固定为 b6adfde5e01b854660048<wbr>588c16acada1dea5805 下的 theory 路径。

</details>

# AURIC：三轴锐读出、内生复结构

# 与共同相位相容

定义、定理与纸面证明　v53.0

2026 年 10 月 31 日　Asia/Singapore

> **版本与归属（编者）**：本文是所供 v53.0 原稿的完整 Markdown 转写。原文“本轮”“本文”及 HEAD 获取、比较、亲读、核对、未执行数学程序和制作行为，均保留为原作者对其历史工作的陈述，不是编者声称重做这些行为。单列“编者核读注”为本版必要的局部条件说明。来源核读与有限纸面论证不构成形式内核、原生实现、物理、经验、全部上游或无条件量子起源认证。

## 摘要


本文研究“唯一本体、所有门序列保持酉性、三轴关系与负平方”如何构成条件重构。
正定实内积并不排斥平方为负的算子：正交复结构 $J^2=-I$ 与正范数严格相容。
复 Hilbert 空间等价于实 Hilbert 空间附带这样的 $J$，复酉门则是与 $J$ 对易的实正交门。
在三轴方向上线性、每个单位方向均为对称二值锐读出的条件下，极化推出 Clifford 关系，
其有向体积 $J=A_1A_2A_3$ 成为中心复结构；不可约最小载体为实四维、复二维。
保持该三轴定向代数的实正交门自动成为酉门。若效果域恰取该代数的相容正效果，
共同相位纤维精确为 $U(1)$；额外实效果可能缩小此纤维。
复合系统的共同复结构以实张量积中的相位对齐投影精确表达，不能由整体唯一性省略。
实化保留复理论的全部指定概率，但改变秩、载体和复合关系，故与朴素实理论须分别定型。
项目本轮新增连续生成元逆纤维，提供同一酉端点下配置、射线与精确向量历史的不同等价关系。
全文给出自足有限维证明，并保留读出线性、锐性、相容域、概率可加和实际取得条件的独立地位。


> **编者核读注（效果域与重数）**：摘要中“该代数的相容正效果”给出精确共同 $U(1)$ 纤维的断言，使用第 4 节随后明确限定的最小不可约表示 $m=1$。若 $m>1$ 而只取三轴生成代数 $M_2(\mathbb{C})\otimes I_m$ 的效果，重数因子仍不可见：例如 $m=2$ 时 $x=e_1\otimes f_1$ 与 $y=e_1\otimes f_2$ 对每个 $E\otimes I_2$ 响应相同，却不是同一复射线。第 5 节的一般共同复结构纤维定理取全部与 $J$ 相容的效果，因而不受此限制。

## 1　本轮结论、内生约定与真实项目增量


本轮能够固定的正面推导为


$$
\boxed{\begin{gathered}
\text{实正定载体上的三轴线性锐读出}\\
\Longrightarrow\text{反对易关系}\Longrightarrow J^2=-I\text{ 的中心复结构},\\
\text{再保定向读出代数的正交门}\Longrightarrow\text{复酉门}.
\end{gathered}}
$$


其中三维是*读出方向空间*的维数；最小振幅载体为 $\mathbb{R}^4\simeq\mathbb{C}^2$。
归一化只是状态或权重的一个约束，不能省略线性、交叉内积或共同复结构。
负平方指算子连续复合后的反向，不能替换为负概率或负范数平方。

所有观察者、辅助因子、相位参考、制备、时钟与记录，均属于同一个静态整体。
下文没有引入本体之外的观察者。“全体内生”与“选用哪一个表示、操作域和响应等价”
是不同问题；一个整体可以具有多种数学表示。

本轮只取得一次项目 `dev HEAD`，随后固定为


<code>b6adfde5e01b85466004<wbr>8588c16acada1dea5805</code>，


 时间 2026-10-31 22:28:02（新加坡）。相对 v52 的


<code>e42edf53c9368a5d53e7<wbr>e780da2d2244493fdfcc</code>，


 完整比较有 148 个路径；theory 树为 3 项新增、3 项修改。
真正的当前量子追加是续卷 III 的第 190–194 节，共 249 行。
V47、V48 是本轮新入库的历史来稿，内部“本轮”与旧快照归原稿；
V24、V37、V44、Ω 均未改。[[1]](#ref-head) [[2]](#ref-compare) [[9]](#ref-qiii) [[8]](#ref-v48) [[3]](#ref-v24) [[4]](#ref-v37) [[5]](#ref-v44) [[6]](#ref-omega)

项目 V24 定理 4.3 已有“三个实反对易反射生成复结构”；V48 已有 Clifford 体积元、
实化与复合边界。本文复用这些标准核心，并把上游输入改写成全方向锐读出，
补出允许门、效果纤维和复合对齐的完整条件链，不把旧结论算作本轮首次发现。


## 2　归一化、线性与酉性分别承担什么条件


#### 定义 2.1（两种“酉性”用法）


严格数学意义的复酉映射是满射复线性内积保持映射。
若只使用“实线性、可逆且保持范数”作为更基础条件，则尚未选定复标量域；
在实载体上它给出正交结构，进一步成为复酉结构还须保留相容复结构。


#### 定理 2.2（线性保范数的准确结论）


<a id="thm:norm"></a>


有限维复线性 $T:\mathbb{C}^d\to\mathbb{C}^m$ 对全部输入保持范数，当且仅当 $T^\dagger T=I$。
此时为等距；同维时为酉。实版本相应给出 $T^{\mathsf T}T=I$。


**证明。**


保范数给 $z^\dagger(T^\dagger T-I)z=0$ 对全部 $z$ 成立。
依次代入 $e_i,e_i+e_j,e_i+ie_j$，得到 Hermitian 矩阵的全部对角、实非对角和虚非对角项为零。
实对称版本用前两类即可。同维时有左逆的方阵可逆，故也是右逆。


□


“全部输入”不能替换为“某个输入”或“两列分别归一”；还须保持交叉关系。
无限维情形还要单独要求满射，单边移位就是保范数但不满射的例子。
项目 V37 第 2 节已有完整 Gram 判据与非线性归一反例。[[4]](#ref-v37)


#### 命题 2.3（可逆且处处保范数仍可非线性）


在 $\mathbb{C}^2$ 上定义


$$
F(a,b)=(e^{i\pi|a|^2}a,b).
$$


它保范数、与共同相位相容且可逆，但不是复线性。


**证明。**


相位因子模为一，逆映射把指数改为负号即可。
但 $F(e_1)=-e_1,F(e_2)=e_2$，而


$$
F((e_1+e_2)/\sqrt2)=(ie_1+e_2)/\sqrt2,
$$


不等于线性性要求的 $(-e_1+e_2)/\sqrt2$。


□


在量子比特中，几个不同的“三维”须分别识别：


| 对象 | 实维数 | 结构 |
| --- | --- | --- |
| 复振幅 $\mathbb{C}^2$ | 4 | 复线性空间 |
| 单位振幅 $S^3$ | 3 | 范数约束曲面，不封闭于线性相加 |
| 纯态 $S^3/U(1)\cong S^2$ | 2 | 射线空间 |
| 全部归一 qubit 密度态 | 3 | Bloch 闭球，凸仿射状态空间 |
| $SU(2)$ | 3 | 行列式一的门群流形 |
| $U(2)$ | 4 | 包含共同门相位的酉群 |


线性关系存在于任意维数。多项式最低次数、状态流形维数与门群维数不是同一个计数。
上一轮“平方是最低关系层”指全域共同相位不变多项式的最低非恒定次数，
不把任意一次关系或任意数学函数都排除。


## 3　正定实内积如何精确表达负平方


#### 命题 3.1（负单位平方的实二维实现）


<a id="prop:jplane"></a>


令


$$
J_0=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
$$


则 $J_0^2=-I$、$J_0^{\mathsf T}J_0=I$，同时


$$
\|J_0v\|^2=\|v\|^2\ge0,\qquad
g(v,J_0^2v)=-\|v\|^2.
$$


映射 $a+ib\mapsto aI+bJ_0$ 保持复数加法与乘法，转置对应共轭。


**证明。**


两次四分之一转给半周转，矩阵相乘也直接给各式。
利用 $J_0^2=-I$ 展开两个 $aI+bJ_0$ 的乘积即得复数乘法，且


$$
(aI+bJ_0)^{\mathsf T}(aI+bJ_0)=(a^2+b^2)I.
$$


□


所以 $i^2=-1$ 与 $\overline i i=1$ 对应两种不同乘法表达；
概率使用后者的正性，前者保留相位复合及干涉中的反向关系。


#### 定义 3.2（相容复结构）


在实内积空间 $(V,g)$ 上，实线性 $J$ 满足


$$
J^2=-I,\qquad J^{\mathsf T}J=I
$$


时称为相容复结构。


#### 定理 3.3（实度量加复结构等价于复内积结构）


<a id="thm:complex"></a>


给定 $(V,g,J)$，定义 $(a+ib)v=av+bJv$ 和


$$
\boxed{h(u,v)=g(u,v)+i\,g(Ju,v).}
$$


则 $h$ 是第一槽共轭线性的复内积。
反过来，取 $g=\operatorname{Re}h,Jv=iv$ 恢复这一结构。
该对应保持范数，故完备性同步保留；有限维时自动得到 Hilbert 空间。


**证明。**


正交性和 $J^{-1}=-J$ 给 $J^{\mathsf T}=-J$，所以
$g(Ju,v)=-g(u,Jv)$。
据此
$h(u,Jv)=ih(u,v)$、$h(Ju,v)=-ih(u,v)$，并有共轭对称性。
$g(Jv,v)=0$ 使 $h(v,v)=g(v,v)>0$。
标量乘法公理来自 $J^2=-I$。反向直接取实部核对。


□


有限维实空间存在这样的 $J$ 当且仅当维数为偶数。
奇维时行列式给 $(\det J)^2=\det(-I)=-1$，矛盾；偶维时将 $J_0$ 逐块直和即可。
所以整个 $\mathbb{R}^3$ 无此结构，但给定单位法向 $n$ 后，$J_nv=n\times v$
在 $n^\perp$ 上满足 $J_n^2=-I$，在全空间则满足
$J_n^2=n\otimes n^\flat-I$。这些也是 V48 的既有结果。[[8]](#ref-v48)


#### 定理 3.4（酉门作为共同复结构的保持群）


<a id="thm:unitary"></a>


实正交 $T$ 为相应复 Hilbert 空间的酉门，当且仅当 $TJ=JT$；
反酉条件则为 $TJ=-JT$。故


$$
\boxed{U(d)=O(2d)\cap\{T:TJ=JT\}.}
$$


**证明。**


$TJ=JT$ 恰为复线性条件。此时


$$
h(Tu,Tv)=g(u,v)+i\,g(TJu,Tv)=h(u,v).
$$


反对易时相同计算将虚部反号并给共轭线性。逆向由定义成立。


□


实正交变换也可能既不酉也不反酉。例如
$T(z_1,z_2)=(\overline z_1,z_2)$。
向量 $u=(1,i)/\sqrt2,v=(i,1)/\sqrt2$ 原来复正交，
变换后 $Tv=-iTu$，成为同一复射线。
保实长度没有保留同一复结构的全部关系。


### 3.1　负平方在动力学中的意义


#### 定理 3.5（单个实旋转生成元的复结构）


<a id="thm:polar"></a>


设有限维实算子 $L^{\mathsf T}=-L$，令 $W=(\ker L)^\perp$。
在 $W$ 上取 $\Omega=\sqrt{-L^2}>0$ 与 $J=L\Omega^{-1}$，则


$$
J^2=-I,\quad J^{\mathsf T}=-J,\quad L=J\Omega=\Omega J,
$$


且


$$
e^{tL}=\cos(t\Omega)+J\sin(t\Omega).
$$


**证明。**


$-L^2=L^{\mathsf T}L\succeq0$，其核恰为 $\ker L$。
$L$ 与其平方、谱函数及正平方根交换，故
$J^2=L^2\Omega^{-2}=-I$、$J^{\mathsf T}=-J$。
指数级数的偶奇项分组给最后一式。


□


这里的负平方产生振荡而不产生负概率。
若采用 $e^{-itH}$ 约定，此 $J$ 选择下 $H=-\Omega$；也可把 $J$ 换成 $-J$。
此构造不独自推出物理能量正性。
零模上 $L$ 不决定 $J$；可扩展到全空间还需零模维数为偶数，且扩展通常不唯一。


#### 命题 3.6（各门分别复化不保证共同复结构）


<a id="prop:no-common-j"></a>


取 $L_1=\operatorname{diag}(J_0,2J_0)$、$B=\operatorname{diag}(1,2)$，以及


$$
L_2=\begin{pmatrix}0&B\\-B&0\end{pmatrix}.
$$


两者都是可逆实反对称算子，但不存在同时与二者对易且平方为 $-I$ 的实算子。


**证明。**


与 $L_1$ 对易的候选也与 $L_1^2=\operatorname{diag}(-I,-4I)$ 对易，故保持两个二维块。
块内与 $J_0$ 对易的矩阵是 $aI+bJ_0$；其平方为 $-I$ 迫使 $a=0,b=\pm1$。
所以候选为 $J=\operatorname{diag}(sJ_0,tJ_0)$，$s,t\in\{\pm1\}$。
与 $L_2$ 对易要求 $sJ_0B=tBJ_0$，比较非零位置得 $2s=t,s=2t$，矛盾。


□


## 4　三轴锐读出怎样生成复数与酉门


#### 定义 4.1（全方向线性二值锐读出）


<a id="def:sharp"></a>


给定非零有限维实 Hilbert 空间 $V$ 和定向 Euclidean 方向空间 $\mathbb{R}^3$。
取实对称算子 $A_1,A_2,A_3$，定义


$$
A(n)=n_1A_1+n_2A_2+n_3A_3.
$$


要求对每个单位 $n$ 有 $A(n)^2=I$。
这是读出在方向上的线性与全方向二值锐性；单纯三个几何轴正交并不蕴含它。


#### 定理 4.2（锐性极化与中心复结构）


<a id="thm:sharp-clifford"></a>


在定义 [4.1](#def:sharp) 下，


$$
\{A_i,A_j\}=2\delta_{ij}I.
$$


令 $J=A_1A_2A_3$，则


$$
\boxed{J^2=-I,\quad J^{\mathsf T}=-J,\quad [J,A_i]=0.}
$$


并有


$$
A(u)A(v)=(u\cdot v)I+J A(u\times v).
$$


**证明。**


取 $n=e_i$ 得 $A_i^2=I$，取 $n=(e_i+e_j)/\sqrt2$ 得反对易关系。
三重乘积平方将三个重复生成元配对，需要三次交换，给 $J^2=-I$。
取转置反转顺序也需三次交换，给 $J^{\mathsf T}=-J$。
把任意 $A_i$ 穿过另两项有两次变号，故与 $J$ 对易。
在正向基上 $A_1A_2=JA_3$，循环同理，最后一式由双线性展开得到。


□


从反对易关系开始的这部分是 V24 定理 4.3 与 V48 定理 5.3 的既有结构。
这里明确补上它的一个上游充分条件：全方向线性与锐性。
Clifford 体积元提供复结构的思想也有标准数学文献；本文固定正平方生成元的符号约定，
不混用采用相反 Clifford 符号的分类记号。[[3]](#ref-v24) [[8]](#ref-v48) [[10]](#ref-hanson)


#### 命题 4.3（三轴的最低中心负平方性质）


对 $n$ 个平方为 $I$、两两反对易的生成元，体积元 $\omega=A_1\cdots A_n$ 满足


$$
\omega^2=(-1)^{n(n-1)/2}I,\qquad
\omega A_i=(-1)^{n-1}A_i\omega.
$$


所以 $n=3$ 是体积元同时中心且平方为 $-I$ 的最小正整数情形。


**证明。**


配对所有生成元需 $n(n-1)/2$ 次交换；将一个生成元越过另外 $n-1$ 个给第二式。
$n=1$ 平方为正，$n=2$ 虽为负但不中心，$n=3$ 同时满足。


□


更高的 $n\equiv3\pmod4$ 也有此性质，故最低性不等于证明物理位置空间只能三维。
两轴乘积平方为负却与原两轴反对易，不能使它们都成为同一复结构上的线性读出。


#### 定理 4.4（Pauli 表示与最小载体）


<a id="thm:pauli"></a>


以 $J$ 为乘 $i$ 的结构，存在复正交基，使


$$
A_1=\sigma_x\otimes I_m,\quad A_2=\sigma_y\otimes I_m,\quad
A_3=\sigma_z\otimes I_m.
$$


因此 $\dim_\mathbb{R} V=4m$；所生成实代数不可约当且仅当 $m=1$。


**证明。**


各 $A_i$ 对易于 $J$ 且实自伴，故成为复 Hermitian 算子。
$A_1$ 等距互换 $A_3$ 的正负复特征空间，二者同维 $m$。
选正空间复正交基 $e_k$，用 $f_k=A_1e_k$ 作负空间基，
得到 $A_3=\sigma_z\otimes I_m,A_1=\sigma_x\otimes I_m$。
由 $J=A_1A_2A_3=iI$ 得 $A_2=iA_1A_3=\sigma_y\otimes I_m$。
$m>1$ 时每一对基向量张成真不变子空间。
$m=1$ 时任意实不变子空间因 $J$ 属于生成代数而复线性；
Pauli 代数为全部 $M_2(\mathbb{C})$，没有非零真不变子空间。


□


上述代数的实维数为八；其自伴部分实维数为四，
由 $I,A_1,A_2,A_3$ 张成。三轴方向、八维代数与不可约情形的四维实振幅是不同对象。


#### 定理 4.5（保定向读出代数的正交门为酉门）


<a id="thm:oriented-gates"></a>


若实正交门 $T$ 满足


$$
TA(n)T^{-1}=A(R_Tn)
$$


且保持读出方向的定向，则 $R_T\in SO(3)$ 且 $TJ=JT$，故 $T$ 为复酉。
若反转方向定向，则 $TJ=-JT$，为反酉。


**证明。**


由 $A(n)^2=\|n\|^2I$ 及 $V\ne0$ 知 $A$ 单射。
共轭在三轴线性空间上线性，所以诱导的 $R_T$ 线性。
由 $A(n)^2=\|n\|^2I$ 及共轭保持平方，得到
$\|R_Tn\|^2=\|n\|^2$，所以 $R_T\in O(3)$。
正交三框架的 Clifford 三重积等于其有向体积乘 $J$，故


$$
TJT^{-1}=A(R_Te_1)A(R_Te_2)A(R_Te_3)=\det(R_T)J.
$$


使用定理 [3.4](#thm:unitary) 即得结论。


□


这里保留的是*三轴读出代数的定向*，不是只看 $T$ 的实行列式。
复二维反酉仍可保持底层实四维定向，故后者条件不够。
$m=1$ 时全部单 qubit 酉门都保持这一三轴空间；
$m>1$ 时一般纠缠门会将局部三轴送到关联算子，因此本定理只是该接口门的充分条件，
不是全部高维酉门都必须保持某个固定局部三轴的断言。


### 4.1　正读出、三维球与平方概率


#### 定义 4.6（相容效果域与归一正泛函）


在 $m=1$ 时，令 $\mathcal{A}$ 为 $A_i$ 生成的实转置封闭代数。
允许效果取其自伴部分中的 $0\preceq E\preceq I$。
一个状态读出是自伴部分上的实线性正泛函 $\varphi$，且 $\varphi(I)=1$。
这明确输入正性、分解相容和归一；不从单个门的保范数单独推出。


#### 定理 4.7（三轴正泛函恰为 Bloch 球）


<a id="thm:positive-ball"></a>


每个这样的泛函由 $r_i=\varphi(A_i)$ 唯一表示，且 $\|r\|\le1$。
对单位 $n$，


$$
E_\pm(n)=\frac12(I\pm A(n)),\qquad
\boxed{\varphi(E_\pm(n))=\frac{1\pm r\cdot n}{2}.}
$$


极端状态恰为 $\|r\|=1$，此时正向读出为 $\cos^2(\theta/2)$。


**证明。**


每个自伴元素为 $aI+A(b)$。由 $A(b)^2=\|b\|^2I$，其特征值为 $a\pm\|b\|$，
故正性等价于 $a\ge\|b\|$。
线性泛函为 $a+b\cdot r$。它对所有此类正元素非负，当且仅当 $\|r\|\le1$：
充分性用 Cauchy 不等式；若 $\|r\|>1$，取 $a=1,b=-r/\|r\|$ 得到矛盾。
单位球内部点可写成两个不同球内点的中点，球面点由严格三角等号判据为极端。
最后取 $r\cdot n=\cos\theta$。


□


在 Pauli 表示下 $\rho=(I+r\cdot\sigma)/2$，因此
$\varphi(E)=\operatorname{Tr}(\rho E)$。纯态 $\rho=\psi\psi^\dagger$ 给出
$\varphi(P_\phi)=|\langle\phi,\psi\rangle|^2$。
平方既来自振幅的共轭配对，也来自正泛函在同一效果不同分解上的一致性；
后者在此是显式统计条件。


## 5　共同 $U(1)$：精确响应纤维与内部相对相位


#### 定义 5.1（相容二次响应）


给定 $(V,g,J)$，效果取实对称 $0\preceq E\preceq I$ 且 $[E,J]=0$。
单位向量 $x$ 的二次响应为 $R_E(x)=g(x,Ex)$。
在最小三轴表示中，这正是上一节的完整效果域。


#### 定理 5.2（相容全效果的纤维恰为共同相位）


<a id="thm:phase-fiber"></a>


对单位 $x,y$，


$$
R_E(x)=R_E(y)\quad\text{对全部相容效果 }E
\iff
y=e^{\theta J}x\quad\text{对某个 }\theta\in\mathbb{R}.
$$


**证明。**


$x,Jx$ 是正交单位向量，令


$$
E_x=xx^{\mathsf T}+(Jx)(Jx)^{\mathsf T}.
$$


它是 $\operatorname{span}_\mathbb{R}\{x,Jx\}$ 的正交投影，与 $J$ 对易。
相同响应给 $g(y,E_xy)=1$，故 $y$ 属于该平面，可写为
$\cos\theta\,x+\sin\theta\,Jx$。
反向由 $EJ=JE$ 和 $e^{\theta J}$ 正交，直接保持二次响应。


□


#### 推论 5.3（最小三轴代数的精确规范群）


在 $m=1$ 时，与全部三轴对易的实正交变换恰为


$$
\boxed{\{e^{\theta J}:\theta\in\mathbb{R}\}\cong U(1).}
$$


**证明。**


与三轴对易先使它与 $J$ 对易，故复线性。
与整个 $M_2(\mathbb{C})$ 对易的复矩阵只有标量 $cI$，正交性要求 $|c|=1$。


□


效果域的限定不可省略。若允许 $\mathbb{R}^{2d}$ 上*全部*实对称效果，
则 $xx^{\mathsf T}$ 能区分 $x$ 与 $Jx$，二者读数分别为一与零。
所以三轴代数产生 $J$，还须要求全部相关读出与该结构相容，才能在整个模型上采用 $U(1)$ 商。
若只给部分读出，纤维反而可能比 $U(1)$ 更大。

在已给复空间中，若全部酉控制都可用，且存在一个秩一读出，则其共轭轨道给全部秩一投影，
从而也得到上述精确相位纤维。
“允许的门都是酉”没有自动说明所有这些门或读出都能取得。

> **编者核读注（秩一效果、锐投影与取得权限）**：上句的轨道断言在可用读出为秩一锐投影 $P$ 时成立，全部酉共轭给出全部秩一投影 $Q$。一般非零秩一效果为 $\lambda P$，其中 $0<\lambda\le1$；其共轭轨道恰为全部 $\lambda Q$。酉共轭保留谱，故 $\lambda<1$ 时这些效果不是锐投影；例如 $\lambda=1/2$ 时迹为 $1/2$，而秩一投影的迹为 $1$。固定 $\lambda>0$ 时，两向量对全部 $\lambda Q$ 的响应相等，当且仅当对全部 $Q$ 的响应相等，故仍有同一精确共同相位纤维。这一响应等价不赋予实际取得锐投影 $Q$ 的权限。


#### 命题 5.4（负号的内部相对相位意义）


整体共同乘 $-I$ 对射线无影响；在相干分支上只对一支施加 $-I$，则可改变内部读出。


**证明。**


内部控制态 $\lvert +\rangle\otimes\psi$ 经受控 $-I$ 变成 $\lvert -\rangle\otimes\psi$。
再对控制施加 Hadamard，前者得到 $\lvert 0\rangle$、后者得到 $\lvert 1\rangle$，是两个正交记录。
整个构造只使用同一整体内部的因子；其物理可执行性仍需相应控制菜单。


□


所以负平方可以有干涉意义，但无需引入负概率。原生受控门的相位边界见 V37 第 5 节。[[4]](#ref-v37)


## 6　用实数重写复理论时必须传递的结构


#### 定义 6.1（固定实化）


对复矩阵 $M=A+iB$，定义


$$
\mathscr{R}(M)=\begin{pmatrix}A&-B\\B&A\end{pmatrix},\qquad
J_d=\begin{pmatrix}0&-I_d\\I_d&0\end{pmatrix}.
$$


对向量 $z=x+iy$，取 $\iota(z)=(x,y)$。


#### 定理 6.2（实化的代数、状态与读出保持）


<a id="thm:realification"></a>


有


$$
\mathscr{R}(MN)=\mathscr{R}(M)\mathscr{R}(N),\quad
\mathscr{R}(M^\dagger)=\mathscr{R}(M)^{\mathsf T},\quad
[\mathscr{R}(M),J_d]=0.
$$


复酉变成实正交，Hermitian 正矩阵变成实对称正矩阵。
若 $\rho$ 是复密度态、$E$ 是复效果，则


$$
\boxed{
\rho_\mathbb{R}=\tfrac12\mathscr{R}(\rho),\qquad E_\mathbb{R}=\mathscr{R}(E),\qquad
\operatorname{Tr}_\mathbb{R}(\rho_\mathbb{R} E_\mathbb{R})=\operatorname{Tr}_\mathbb{C}(\rho E).
}
$$


非零态满足 $\operatorname{rank}_\mathbb{R}\rho_\mathbb{R}=2\operatorname{rank}_\mathbb{C}\rho$。


**证明。**


块乘法给乘积与伴随公式，$J_d=\mathscr{R}(iI)$ 给对易。
对 Hermitian $H$，有
$\iota(z)^{\mathsf T}\mathscr{R}(H)\iota(z)=z^\dagger Hz$，故保持正性。
再用 $\operatorname{Tr}_\mathbb{R}\mathscr{R}(M)=2\operatorname{Re}\operatorname{Tr}_\mathbb{C} M$，
以及 Hermitian $\rho,E$ 的 $\operatorname{Tr}(\rho E)$ 为实数，得到概率式。
复 Hermitian 谱分解经实化后每个实特征值重复两次，故得到迹与秩公式。


□


纯复态实化后是秩二态，并不表示原来的物理信息被混合。
若取某个固定相位的实单位代表 $x=\iota(\psi)$，它的实秩一态 $xx^{\mathsf T}$
也对全部相容效果给出相同响应；其相位平均为


$$
\frac12\bigl(xx^{\mathsf T}+J_dxx^{\mathsf T}J_d^{\mathsf T}\bigr)
=\frac12\mathscr{R}(\psi\psi^\dagger).
$$


给定效果域不同，纯性与可区分性所处的状态空间也不同。
这种实表示及多体相位编码是已有量子信息结果；本节显式核对所用公式。[[11]](#ref-mckague)

这区分三个说法：不带 $J$ 的朴素实量子理论、带共同 $J$ 的复理论实表示，
以及通常的复数记号。唯一本体允许同一对象具有等价表示，
没有要求其中只能出现某一种坐标字母。


## 7　复合系统是共同虚单位的相位对齐


#### 定义 7.1（实张量积中的对齐与反对齐扇区）


给 $(V_A,J_A),(V_B,J_B)$，实维数分别为 $2d,2e$。
在 $V_A\otimes_\mathbb{R} V_B$ 上令


$$
K=J_A\otimes J_B,\qquad
P_\pm=\tfrac12(I\pm K),\qquad \mathcal{H}_\pm=\operatorname{Ran}P_\pm.
$$


#### 定理 7.2（复张量积的精确对齐实现）


<a id="thm:tensor"></a>


$K$ 是对称对合，两个扇区实维数均为 $2de$。
在 $\mathcal{H}_-$ 上


$$
J_A\otimes I=I\otimes J_B,
$$


并定义共同复结构 $J$。映射


$$
\boxed{
\Phi(x\otimes_\mathbb{C} y)
=\frac{x\otimes_\mathbb{R} y-J_Ax\otimes_\mathbb{R} J_By}{\sqrt2}
}
$$


给复 Hilbert 空间 $V_A\otimes_\mathbb{C} V_B$ 到 $\mathcal{H}_-$ 的等距同构。
在 $\mathcal{H}_+$ 上，两局部复结构相反。


**证明。**


$K^{\mathsf T}=(-J_A)\otimes(-J_B)=K$，$K^2=I$。
$\operatorname{Tr} J_A=\operatorname{Tr} J_B=0$，所以 $\operatorname{Tr} K=0$，两个本征空间同维。
若 $Kv=-v$，左乘 $J_A\otimes I$ 得
$(I\otimes J_B)v=(J_A\otimes I)v$；$+1$ 扇区类似给负号。

显示映射的像在 $\mathcal{H}_-$，且
$\Phi(J_Ax\otimes y)=\Phi(x\otimes J_By)=J\Phi(x\otimes y)$，
故满足复张量积的平衡关系。
若 $h_A(x,u)=a+ib,h_B(y,v)=c+id$，展开两个显示向量的实内积得到
$ac-bd=\operatorname{Re}(h_A(x,u)h_B(y,v))$。
复线性再保证完整复内积相等。定义域和像空间复维数同为 $de$，故满射。


□


#### 推论 7.3（相位怎样相加）


局部门 $e^{\alpha J_A}\otimes e^{\beta J_B}$
在 $\mathcal{H}_-$ 上为 $e^{(\alpha+\beta)J}$，在 $\mathcal{H}_+$ 上为 $e^{(\alpha-\beta)J}$。


**证明。**


两个局部生成元对易；在各扇区用其相等或相反关系合并指数。


□


因此共同复结构表达了一个具体的关系传导规则：同一相位可移到任一因子，而总相位相加。
它不是从“只有一个整体”这句话自动得到的实张量积恒等式。


### 7.1　局部统计无法自行决定相位对齐


#### 定理 7.4（两个相同局部统计的相位扇区态）


<a id="thm:sectors"></a>


设 $A=\mathscr{R}(\rho)$、$B=\mathscr{R}(\sigma)$，其中 $\rho,\sigma$ 为复密度态。
独立实化态为 $\eta=A\otimes B/4$。
两扇区质量均为 $1/2$，条件态为


$$
\tau_\pm=\tfrac12P_\pm(A\otimes B)P_\pm
=\tfrac14(A\otimes B\pm J_AA\otimes J_BB).
$$


它们具有相同局部边缘 $A/2,B/2$，并对全部局部实对称效果 $E,F$ 满足


$$
\operatorname{Tr}(\tau_\pm(E\otimes F))
=\operatorname{Tr}((A/2)E)\operatorname{Tr}((B/2)F).
$$


但 $\operatorname{Tr}(K\tau_\pm)=\pm1$。


**证明。**


$A,B$ 分别对易于局部 $J$；$J_AA,J_BB$ 均反对称且迹零。
所以 $\operatorname{Tr}(K\eta)=0$，两个投影的概率均为一半。
因 $A\otimes B$ 与 $P_\pm$ 对易，展开给条件态公式。
反对称与对称矩阵的迹配对为零，故相关项对全部局部实对称效果消失，
部分迹也消失。$K$ 在两支持上各为 $\pm I$，给最后一式。


□


在同构 $\Phi$ 下，$\tau_-$ 是复积态 $\rho\otimes_\mathbb{C}\sigma$ 的一次全局实化。
即使原复态可分，这个实编码也需要共享相位结构；
事实上任何实可分态对 $K$ 的期望都是零，因为每个实局部态对反对称 $J$ 的迹为零。
所以 $\tau_\pm$ 在朴素实张量模型中不可分。
这是*编码结构*的相关，不能误称为原复积态已经物理纠缠。

最小例子只需两个实二维系统：


$$
\rho_\pm=\frac14(I\otimes I\pm J_0\otimes J_0).
$$


它们为正、迹一，全部局部实效果乘积的统计相同，而全局 $K$ 可区分。
于是局部层析相容是一个实质条件，不能由整体唯一性替代。


#### 推论 7.5（多因子递归对齐）


对 $n$ 个带 $J_i$ 的实化空间，将 $J_i$ 记为作用在第 $i$ 个因子上的算子。
互相对易的投影


$$
P=\prod_{j=2}^n\frac{I-J_1J_j}{2}
$$


选出 $J_1=J_2=\cdots=J_n$ 的共同扇区。
若原复维数为 $d_i$，此扇区实维数为 $2\prod_i d_i$，
独立实化乘积态在其中的质量为 $2^{-(n-1)}$。


**证明。**


$J_i$ 两两对易，且平方为 $-I$，故各 $J_1J_j$ 为对易对称对合。
维数可逐次使用定理 [7.2](#thm:tensor)；每次对齐减少一半实维数。
对独立实化乘积态展开 $P$，除常数项外每项都有某个 $j\ge2$ 的单个 $J_j$，
该因子的迹配对为零，所以只剩系数 $2^{-(n-1)}$。


□


这是精确代数投影与条件态公式，不自动提供免费投影、独立来源或实际后选择权限。
共享相位信息与允许的物理操作仍须计入整体内部结构。


### 7.2　关于实理论可实验区分的来源范围


McKague–Mosca–Gisin 给出保指定局部演化与测量的实模拟，包含共同相位编码。[[11]](#ref-mckague)
Renou 等 2021 年论文在具有张量积源独立条件的网络中给出实／复理论的不同预测。[[12]](#ref-renou)
2026 年 Hoffreumon–Woods 预印本明确区分张量积独立与操作独立，
并主张后者条件下有限网络与顺序协议可实模拟。[[13]](#ref-hw)
本文核对其摘要、定义性引言及所述范围，没有认证该预印本全部长证明。
本节的代数与统计结论由显示公式独立证明；
不将任何论文标题扩张为“所有实数表述都被实验排除”或“所有复合条件都无关”。


## 8　唯一本体、门序列与概率可加的准确连接


一个统一整体可以在实 Hilbert 空间上由一个单位初态和正交门序列描述，
同样可以有内部参考、记录与纯整体。因此若把“酉”理解为更基础的保内积，
唯一本体与保内积并未单独排除实模型。
若一开始严格指定复酉，复结构已经包含在前提中；
本轮三轴定理的意义是给它一个更上游、明确可检验的充分条件。


#### 定义 8.1（内部运输的共同复结构）


给连通图，顶点为同维实内积接口 $V_v$，边为正交同构 $T_e$，反向边为逆。
一族 $J_v$ 相容，指 $J_v^2=-I$、$J_v^{\mathsf T}J_v=I$，且每条边满足
$T_eJ_v=J_wT_e$。


#### 定理 8.2（共同复结构的闭环判据）


<a id="thm:holonomy"></a>


固定根接口及其正交复结构 $J_o$。能将它一致运输到全部顶点，当且仅当每条根闭环的运输乘积与 $J_o$ 对易。


**证明。**


若已有相容族，沿闭环逐边消去中间结构即得对易。
反之，对每个顶点取从根到它的路径 $p$，定义
$J_v=T_pJ_oT_p^{-1}$。
两条路径相差根闭环，所给对易条件使定义独立于路径；再沿一条边即得边相容。
正交运输同时保留 $J_v^2=-I$ 与 $J_v^{\mathsf T}J_v=I$。


□


只给一个连通整体并没有自动满足闭环判据。
若预先将所有门放在同一个复 Hilbert 空间中，该相容性已经供应；
若从局部实关系起步，则需要证明它。


#### 定理 8.3（非零正交权重选择平方）


<a id="thm:weight"></a>


在已给内积空间、至少两个正交方向的条件下，设有限非负权重 $W$ 仅依赖范数，
对正交和可加，且不恒为零。则存在 $c>0$ 使 $W(x)=c\|x\|^2$。


**证明。**


取正交单位 $e_1,e_2$，令 $F(t)=W(\sqrt t e_1)$。
径向性与正交可加性给 $F(s+t)=F(s)+F(t)$。
非负性给单调性，先在非负有理数上得 $F(q)=cq$，再用上下有理夹逼得全域式。
不恒零使 $c>0$。


□


复正交版本要求复维数至少二。V47 保留了同类平方选择条件。[[7]](#ref-v47)

单纯归一仍允许如 $p_+(n)=(1+n_z^3)/2$ 的读出，它与 $p_+(-n)$ 相加为一，
但不能在完整效果域中保持分解相容。
因此所有振幅门都保范数，仍没有替实际概率读出自动赋予可加性。


#### 命题 8.4（内部记录的平方传导）


设有限族 $K_i$ 为复线性算子，$\sum_iK_i^\dagger K_i=I$。
定义 $V\psi=\sum_i\lvert i\rangle\otimes K_i\psi$，记录槽正交。
则 $V$ 为等距；在定理 [8.3](#thm:weight) 的非零权重条件下，单位输入的记录概率为


$$
p_i=\|K_i\psi\|^2.
$$


对任一固定有限深度的全部内部历史，令 $K_h$ 为沿历史的算子复合，
则 $p_h=\|K_h\psi\|^2$，逐节点完备性使该层总质量为一。


**证明。**


$\|V\psi\|^2=\sum_i\|K_i\psi\|^2=\|\psi\|^2$。
权重定理给每个正交分支的份额，多层沿树逐层求和即可。


□


反向，若内生读出明确由同一复 Hilbert 空间上的酉门 $U$、固定内部记录初态
$\lvert 0\rangle$ 与完备正交记录基 $\{\lvert i\rangle\}$ 实现，定义


$$
K_i=(I\otimes\langle i\rvert)U(I\otimes\lvert 0\rangle),\qquad E_i=K_i^\dagger K_i.
$$


对全部记录求和，利用 $\sum_i\lvert i\rangle\langle i\rvert=I$ 与 $U^\dagger U=I$，立即得到
$\sum_iE_i=I$。每个效果是复线性正算子，实化后自动对易于共同 $J$。
因此在这个明确的门与记录生成合同中，效果相容已经由前提供应，
不必再独立假设；相应内部因子、正交记录与概率权重仍是已给结构。
纯整体与局部混态或条件读出同时存在，全部因子仍内生。
零质量分支保留零标记，不作除零归一；等距完成到酉需要相应初态槽位与维数完成。
这些是 V37、Ω 的既有内生记录结构。[[4]](#ref-v37) [[6]](#ref-omega)


## 9　真正新增的项目结果：同一酉端点的不同内部历史


续卷 III 第 190–194 节将原生连续模型中的一个逆问题明确化。[[9]](#ref-qiii)
它保留原 89 维载体、十一地址、唯一 ready、原单点／二点支撑分量、
常定单位时长 Hermitian 脉冲及相同门端点。
平方 Bell 最小率、纯分支更新、独立积分风险驱动、原因果档案与失败条件均为前件。
内部连续时刻、配置及跳数的数学比较不增加控制者实际读口。


### 9.1　谱对数的纸面机制


#### 定理 9.1（简单谱端点的生成元纤维）


<a id="thm:logs"></a>


设 $U=\sum_a e^{-i\theta_a}P_a$ 为有限维简单谱酉，其中每个 $P_a$ 秩一。
全部满足 $e^{-iH}=U$ 的 Hermitian 矩阵恰为


$$
\boxed{H=\sum_a(\theta_a+2\pi k_a)P_a,\qquad k_a\in\mathbb{Z}.}
$$


**证明。**


$H$ 与自己的指数对易，所以与 $U$ 对易。
简单谱迫使 $H$ 在每个特征线上为实标量；标量指数相等恰相差 $2\pi$ 整数。
逆向代入立即成立。


□


重复端点特征值的子空间中还可有不同特征基和整数谱自伴块，不能省略此边界。
项目新分类在固定单／二点分量内利用了相应简单谱；
全空间跨分量的重数并没有被自动消除。
上述一般谱对数事实是复用的标准工具；续卷 III 明确沿用 V17 第 13.2 节。
本轮项目新增的是在原 89 维载体、十一地址及分量保持合同下，
对实际 ready 历史建立的逆纤维分类。

例如 $H_0=0,H_1=2\pi\lvert 1\rangle\langle 1\rvert$ 都在单位时刻给 $I$。
但从 $\lvert +\rangle=(\lvert 0\rangle+\lvert 1\rangle)/\sqrt2$ 出发，半时刻一个仍是 $\lvert +\rangle$，另一个为 $\lvert -\rangle$。
二者的连续射线不同，全部演化仍酉。


### 9.2　新原生纤维及三层精细化


在源文的二点分量 $B$ 上，记原秩一投影为 $Q_B$，则所有比较生成元为


$$
\widetilde H_j|_B=H_j|_B+2\pi(m_{jB}I_B+n_{jB}Q_B),
\qquad m_{jB},n_{jB}\in\mathbb{Z}.
$$


单点只剩一个整数参数。
源定理 190.2 保持原门端点及原可读报告／档案联合律，
但没有声称连续配置路径或隐藏配置接缝联合律也相同。
191.1 的弱有限跳条件保留全部整数分支；
191.2 对每个实际有限 ready 前缀要求最后一门至多两跳，恰好选出 $n_{jB}=0$。
其必要性依赖旧 ready 轨道稠密性，利用一个避节点开集中的实际有限字，
没有供应任意输入的精确准备。

第 193 节进一步得到：


| 保留的观察 | 剩余生成元纤维 |
| --- | --- |
| 原门端点与原可读历史 | 上述全部 $m_{jB},n_{jB}$ |
| 完整配置轨迹与全部跳时 | $\widetilde H_j=H_j+2\pi\sum_Bm_{jB}P_B$ |
| 再保留连续完整向量射线 | $\widetilde H_j=H_j+2\pi m_jI$ |
| 再保留固定规范下的精确向量 | $\widetilde H_j=H_j$ |


#### 命题 9.2（分量相位到共同相位的精细化机制）


令 $S=\sum_Bm_BP_B$，$u$ 在每个分量上非零。
若 $e^{-2\pi itS}u$ 在所有邻近零的时刻都与 $u$ 为同一射线，则全部 $m_B$ 相同。
若精确向量相等，则全部 $m_B=0$。


**证明。**


任两非零分量的相对相位为 $e^{-2\pi it(m_B-m_C)}$。
在邻近零的区间恒等于一，求导即给 $m_B=m_C$。
精确向量时，每个分量自身相位恒为一，导数给 $m_B=0$。


□


在源文的配置纤维中，完整向量历史通过


$$
D_j(s)=\sum_Be^{-2\pi im_{jB}s}P_B
$$


作显式因果可逆对应。端点 $D_j(0)=D_j(1)=I$；
块内共同相位不改平方质量、非对角电流与最小率，所以配置路径可用同一驱动耦合。
这说明的是完整律经变换的推前对应，不是全部原坐标字面同律。
第 194 节明确保留复 Hilbert、平方率、复合、时钟和实际来源等条件；
本轮没有把这一有限逆分类说成全部量子起源已完成。


## 10　接回原生 AURIC 与本轮条件重构原则


V37 给固定相干等距 $J_F:\mathbb{C}^2\to\mathbb{C}^5$，$J_F^\dagger J_F=I$，
原三占据均值为 $u=u_0+\nu r$，其中


$$
\nu=(1+2\sqrt3+\sqrt{11})^{-1},\qquad
u_0=\left(\tfrac\nu2(\sqrt3+\sqrt{11}),\tfrac\nu2(\sqrt3+\sqrt{11}),\nu\right).
$$


每个数学 qubit 酉 $U$ 可相干提升为


$$
\widetilde U=J_FUJ_F^\dagger+(I_5-J_FJ_F^\dagger).
$$


编码子空间和补空间的交叉项为零，故 $\widetilde U$ 酉且 $\widetilde UJ_F=J_FU$。[[4]](#ref-v37)

原三个占据算子在五模式全空间中对易，压缩效果有偏且不尖锐；
它们的统计仿射标定不是本轮定义 [4.1](#def:sharp) 的全部方向锐读出权限。
五维载体也不能承载完整反对易可逆对合对：奇维行列式将 $AB=-BA$ 变成
$\det(AB)=-\det(AB)$，与可逆矛盾。
所以本轮 Pauli／复结构定理作用于指定二元接口，不能偷换为五标签全空间的同一个反对易代数。
V44 的多接口等距图册可以保留标签与关联，但不把任意高维态压成三个独立实数。[[3]](#ref-v24) [[5]](#ref-v44) [[8]](#ref-v48)


#### 定理 10.1（三轴内生复结构的条件重构原则）


<a id="thm:summary"></a>


给定非零有限维实正定载体、三轴线性对称读出，且每个单位方向均为二值锐读出，
则三轴生成中心正交复结构与 Pauli 表示。
若表示不可约，则振幅载体为 $\mathbb{C}^2$。
在上述不可约最小表示中，若相关效果恰为其相容正效果，
完整二次响应纤维为共同 $U(1)$，归一正线性读出给 Bloch 球与纯态 Born 平方式。
若允许的实正交接口门保持三轴方向及定向，则这些门为复酉。
多个这样的接口在共同复结构对齐的扇区按复张量积合成。


**证明。**


依次使用定理 [4.2](#thm:sharp-clifford)、[4.4](#thm:pauli)、[5.2](#thm:phase-fiber)、
[4.5](#thm:oriented-gates)、[4.7](#thm:positive-ball) 与 [7.2](#thm:tensor)。
各结论的对象和允许域已分别限定，故不需要把同一词在不同类型间替换。


□


| 直觉 | 本轮固定的准确版本 |
| --- | --- |
| 实内积不能表达负平方 | 实算子可有 $J^2=-I$；正范数与负复合平方相容 |
| 归一化就是酉性 | 全域复线性保范数给等距；有限同维或满射再给酉 |
| 复线性结构是三维 | 三维是某些读出、单位壳或群流形；qubit 线性振幅是实四维 |
| 三轴与手性给复数 | 全方向锐性给反对易；三重乘积给中心 $J$；定向协变门保留它 |
| 唯一本体决定共同相位商 | 相容完整响应精确选出 $U(1)$；更粗或更细读出有不同纤维 |
| 全部门酉就完成复合与概率 | 共同 $J$ 对齐、效果分解相容和实际读出来源仍须说明 |


本文给有限维条件证明；无限维域、无界生成元、无限图一致性及实际精度预算须单独处理。
全文未执行数学程序、数值近似、枚举、CAS、Lean 或门搜索；
来源身份核对与文稿编译／版式检查不替代数学证明，也不等于认证整个仓库。


## 附录 A　共同虚单位的实、复、四元数三种交换代数


#### 定理 A.1（有限实不可约交换代数的短分类）


设含单位、转置封闭的实代数 $\mathcal{A}\subseteq\operatorname{End}_\mathbb{R}(V)$
在非零有限维 $V$ 上不可约，令


$$
\mathcal{D}=\{T:TA=AT\text{ 对全部 }A\in\mathcal{A}\}.
$$


则 $\mathcal{D}$ 同构于 $\mathbb{R},\mathbb{C}$ 或四元数代数 $\mathbb H$。


**证明。**


转置封闭性使 $\mathcal{D}$ 也转置封闭。
其中任何自伴元素的每个谱空间都对 $\mathcal{A}$ 不变，故不可约性迫使它为实标量。
于是 $\mathcal{D}=\mathbb{R} I\oplus\mathcal{D}_0$，其中 $\mathcal{D}_0$ 为反对称部分。
对 $K,L\in\mathcal{D}_0$，$KL+LK$ 自伴并属于 $\mathcal{D}$，因此定义


$$
-\tfrac12(KL+LK)=\langle K,L\rangle I.
$$


这是正定内积，因为 $-K^2=K^{\mathsf T}K$；若其标量为零则 $K=0$。

若 $\mathcal{D}_0$ 为零，得到实数；若为一维，单位 $J$ 满足 $J^2=-I$，得到复数。
若有两个正交单位 $J_1,J_2$，它们反对易，$J_3=J_1J_2$
为第三个正交单位反对称算子，并满足四元数乘法。
若有 $L$ 与三个都正交，则 $L$ 与 $J_1,J_2$ 反对易，故与 $J_3$ 对易；
但正交条件又要求与 $J_3$ 反对易。于是 $2J_3L=0$。
$J_3^2=-I$ 使它可逆，所以 $L=0$。
反对称部分只能为 $0,1,3$ 维，得到三个代数。


□


相应地，实型没有共同虚单位；复型只有 $\pm J$ 两个相容选择；
四元数型有一个 $S^2$ 的选择族。
三轴锐读出的不可约表示属于复型。
这是一项给定代数与不可约性下的分类，并不将“唯一本体”直接等同于该不可约条件。


## 固定来源与证明归属


<a id="ref-head"></a>

**[1]**
the-omega-institute/trureturing，固定提交
[b6adfde5e01b85466004<wbr>8588c16acada1dea5805](https://github.com/the-omega-institute/trureturing/commit/b6adfde5e01b854660048588c16acada1dea5805)，
2026-10-31 22:28:02 SGT。完整来源快照而非滚动 HEAD。


<a id="ref-compare"></a>

**[2]**
[v52 至 v53 固定比较](https://github.com/the-omega-institute/trureturing/compare/e42edf53c9368a5d53e7e780da2d2244493fdfcc...b6adfde5e01b854660048588c16acada1dea5805)。
完整 diff 与比较列表均为 148 路径；未截断 theory 树 1112 项，3 新增、3 修改。
没有 Quantum Blueprint 路径变更。V47、V48 保留历史来稿身份。


<a id="ref-v24"></a>

**[3]**
[AURIC Two Basis States, Three Channels, Phase Chirality and Recursive Square Law V24](https://github.com/the-omega-institute/trureturing/blob/b6adfde5e01b854660048588c16acada1dea5805/docs/develop/theory/AURIC_TWO_BASIS_STATES_THREE_CHANNELS_PHASE_CHIRALITY_AND_RECURSIVE_SQUARE_LAW_V24.md)。
本轮亲读 325–464 行，特别定理 4.3 的实反对易三轴与相容复结构。
其核心为已有项目结果，本文补上全方向锐性的上游条件及操作／效果域的接合。


<a id="ref-v37"></a>

**[4]**
[AURIC Binary Relations and Unitary Representation V37](https://github.com/the-omega-institute/trureturing/blob/b6adfde5e01b854660048588c16acada1dea5805/docs/develop/theory/AURIC_BINARY_RELATIONS_UNITARY_REPRESENTATION_AND_GOLDEN_GATE_UNIVERSALITY_V37.md)。
本轮亲读 90–148 行；内生记录与控制相位沿用此前已读且本轮未改的 352–430 行，来源审计重新核对。
固定五模式编码与非锐压缩效果沿用第 3 节。


<a id="ref-v44"></a>

**[5]**
[AURIC Boundary Extension and Higher Dimensional Relational Atlas V44](https://github.com/the-omega-institute/trureturing/blob/b6adfde5e01b854660048588c16acada1dea5805/docs/develop/theory/AURIC_BOUNDARY_EXTENSION_AND_HIGHER_DIMENSIONAL_RELATIONAL_ATLAS_V44.md)。
沿用已核对的图册、相干等距及维数边界；本轮文件未变，来源审计重读 814–943、996–1035 行。


<a id="ref-omega"></a>

**[6]**
[AURIC Ω Static Compatibility Fiber Theory](https://github.com/the-omega-institute/trureturing/blob/b6adfde5e01b854660048588c16acada1dea5805/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。
复载体、效果、张量复合与内部记录的条件框架；本文不把全体内生替换成这些结构的无前提起源。


<a id="ref-v47"></a>

**[7]**
[AURIC Existential Quantifiers, Square Weights and Prompt Error Relations V47](https://github.com/the-omega-institute/trureturing/blob/b6adfde5e01b854660048588c16acada1dea5805/docs/develop/theory/AURIC_EXISTENTIAL_QUANTIFIERS_SQUARE_WEIGHTS_AND_PROMPT_ERROR_RELATIONS_V47.md)。
本轮新入库历史稿，源审读 97–136、267–291、334–424 行；复正交、归一幂族与平方选择条件。


<a id="ref-v48"></a>

**[8]**
[AURIC Isotropy, Chirality and Conditional Quantum Reconstruction V48](https://github.com/the-omega-institute/trureturing/blob/b6adfde5e01b854660048588c16acada1dea5805/docs/develop/theory/AURIC_ISOTROPY_CHIRALITY_AND_CONDITIONAL_QUANTUM_RECONSTRUCTION_V48.md)。
本轮亲读 1–130、265–598、955–1065 行。
历史稿新入库：定向度量、Clifford 体积、酉／反酉和复合条件均保留原归属。


<a id="ref-qiii"></a>

**[9]**
[AURIC Quantum Principles and Coherent Reconstruction, Continuation III](https://github.com/the-omega-institute/trureturing/blob/b6adfde5e01b854660048588c16acada1dea5805/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md)。
本轮完整亲读新增 4559–4806 行，特别定义 190.1、定理 190.2、191.2、193.2–193.3 与范围 194。
旧 ready 稠密性、Bell 率存在性等作为来源明确依赖，本文未重新认证其全部上游证明。


<a id="ref-hanson"></a>

**[10]**
Jason Hanson，*Complex structure of a real Clifford algebra*，
[arXiv:1104.0399v1](https://arxiv.org/html/1104.0399v1)（2011）。
亲读定义与体积元的复结构背景；该文 Clifford 符号约定与本文正平方生成元记号不同。
本文具体三轴结论另给短证。


<a id="ref-mckague"></a>

**[11]**
Matthew McKague, Michele Mosca, Nicolas Gisin，
*Simulating Quantum Systems Using Real Hilbert Spaces*，
Physical Review Letters 102, 020505（2009）；
[arXiv:0810.1923](https://arxiv.org/pdf/0810.1923)。
亲读实化、算子与连续演化、局部编码及附录中相位平均／秩二表示；本文公式独立展开。


<a id="ref-renou"></a>

**[12]**
Marc-Olivier Renou 等，*Quantum theory based on real numbers can be experimentally falsified*，
Nature 600, 625–629（2021），
[doi:10.1038/s41586-021-04160-4](https://www.nature.com/articles/s41586-021-04160-4)。
核对网络及独立来源条件；不将其范围扩张成排除全部实表示。


<a id="ref-hw"></a>

**[13]**
Timothée Hoffreumon, Mischa P. Woods，
*Quantum theory based on real numbers cannot be experimentally falsified*，
[arXiv:2603.19208v1](https://arxiv.org/html/2603.19208v1)（2026-03-19，预印本）。
仅用于核对操作独立与张量积独立的区别及作者主张；未认证全部 60 页证明。
