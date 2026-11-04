# 已证结构的内生闭合

同根有限证书、事件重编码与结果核递归

AURIC v78 后续研究：定义、定理与证明

研究续稿

2026 年 11 月 2 日

## 摘要

本稿先纠正上一轮结尾的承接遗漏：共同复结构、全部合成二元测试与整体正性的等价、同根 Born 读出、核到量子仪器的重构，以及声明模型类内的复数域选择，均已有相应证明，不应重新合称为尚未开始解决的问题。

在这些既有接口上，本轮给出两项具体前件削减。第一，在同根循环的有限实关系扇区中，一个实际正交参考门的有符号半周校准，加有限历史上的顺序相容证书，已经推出共同复结构；无需再假设不可约性或完整连续参考流。第二，非负归一事件权重只须保持二端口平衡重编码和共同四分之一转，即自动成为唯一正效果的复二次型；连续性、全部相位不变性与幅度二次齐次性同时得到。

继而把既有核到仪器定理抽取为结果核与效果的序同构，再接上指定后继的唯一下降、序贯核拉回与有限结果树。每项条件都指明其比较的两个内部元、三维失败读出及更大的相容结构。本文给解析证明，不执行数学枚举，不把表示存在等同于未声明的控制可用性，也不把这些纸面结果标为新增 Lean 验证。

## 目录

- [1. 承接修正：已经证明的链不再退回起点](#section-1)
- [2. 两个内部元、三维读出与条件所属的整体](#section-2)
- [3. 共同复方向：一个实际参考门的同根有限证书](#section-3)
- [4. 共同方向怎样沿历史拼接：允许闭路留下相位](#section-4)
- [5. 整体正性已经有二元入口：使用全部合成对象](#section-5)
- [6. 事件读出无需先给算符：两端口重编码已经锁定形式](#section-6)
- [7. 结果核就是内部效果：把既有重构抽取成一个等价](#section-7)
- [8. 指定后继锁定线性分支，完整正性成为结论](#section-8)
- [9. 关系的关系继续递归：有限结果树的闭合定理](#section-9)
- [10. 同根绑定与旧模型排除：准确保留，不再重开](#section-10)
- [11. 本轮的统一闭合：哪些性质不再需要独立列入](#section-11)
- [12. 完整白话图景](#section-12)

<a id="section-1"></a>

## 1. 承接修正：已经证明的链不再退回起点

### 1.1 固定版本与既有成果

本轮核对的公开 `dev` 提交为

`31fa401a7c17858fa323ddd0886ed580e0c57347`。

该快照已收入前轮《从二元失败见证到整体量子关系》的公开转录。
因此，上一轮末尾把共同复正核、效果结构和其他模型排除再次笼统列为待解决问题，
遗漏了此前已有推导。正确做法是保留每个定理的前件和结论，继续消去冗余前件、
接合接口，并明确什么只是既有证明的抽取。

| 已有位置 | 已经取得的结论 | 本轮如何使用 |
| --- | --- | --- |
| V53、V63；前轮相容稿 §4 | 原生响应／共同参考路线构造 $J$；两实比较合成复正核 | 保留已得 $J$，另给单个参考门的有限认证路线 |
| V77 §3 定理 3.2 | 全部可缩放的合成二元球条件等价整体正性 | 直接作为正性入口；不退回只检查原始历史对 |
| V64；V78 同根读出 | 平方标定、效果细分、根校准与准备协变 | 概率标尺和来源绑定直接继承 |
| V68 §7 定理 7.4 | 完整核守恒给线性分支、记录等距、仪器与积核表示 | 抽取结果核--效果对应，再接有限序贯树 |
| Quantum Origin Atlas §§26、29 | 内部最小饱和效果与谱分解给自对偶几何；明确复合合同选复矩阵型 | 模型排除已在声明类内完成，本轮不重新列为泛泛缺口 |
| V74 §3、V78 §12 | 有限秩正历史核、双射保核接续及 $C^1$ 锚给酉历史和生成元；自治群另需平移相容 | 本轮共同复方向与结果树使用同一表示 |

上述位置见文末固定链接[2](#ref-v53)、[3](#ref-v63)、[5](#ref-v77)、[4](#ref-v68)、[1](#ref-previous)、[8](#ref-atlas)、[6](#ref-v74)、[7](#ref-v78)。
其中 Atlas §29 的选择前件包括其 S、Sp、强对称、连通纯态传递、
秩乘法和局部层析自复合条件；正文在该类内排除了非平凡经典单纯形、
实和四元数矩阵、非三维 spin factor 及 Albert 类型。这项已完成的条件分类
不应被改写成“其他模型尚未排除”，也不应扩大成所有可能乘积嵌入的分类。

### 1.2 本轮增加的内容

本轮的主要增量是：把共同方向的全空间条件压成同根有限历史证书；
把事件算符的预设改为两条权重路由相容；把核、效果、分支与后续观测统一成
同一张正核分解树。受支配核表示、极化、等距扩张等属于标准数学工具；
新增的是这些工具在本项目内部接口中的组合与前件精化。

全文内积对第二变量线性。$\Omega$ 指完整内部结构；$\Omega_0$ 指单位根向量。
已有的实关系载体与正内积不在此重新假定为未解决：可使用 V63 原生入口，
或 Atlas 在其操作合同中已取得的几何，随后按各自类型进入相应表示。
不同入口不自动互相等同。

**白话图景。**已经搭好的部分继续保留：共同方向已经有构造，关系球怎样拼成整体已有判据，概率怎样绑定同一个根也已有校准。这一轮向前做的事，是把还分散在各处的条件接到同一张图里，检查哪些已经能由别的关系推出。

<a id="section-2"></a>

## 2. 两个内部元、三维读出与条件所属的整体

<a id="statement-2-1"></a>

#### 定义 2.1（有共同目标的两条路由）

给定两个位于同一已声明内积空间的输出 $a,b$，令
$s=\left\lVert a\right\rVert ^2+\left\lVert b\right\rVert ^2$。若 $s>0$，定义

$$
X=\frac{2\operatorname{Re}\langle a,b\rangle }{s},\qquad
Y=\frac{2\operatorname{Im}\langle a,b\rangle }{s},\qquad
Z=\frac{\left\lVert a\right\rVert ^2-\left\lVert b\right\rVert ^2}{s}.
$$

这是二元关系矩阵
$s^{-1}\left(\begin{smallmatrix}\left\lVert a\right\rVert ^2&\overline{\langle a,b\rangle }\\ \langle a,b\rangle &\left\lVert b\right\rVert ^2\end{smallmatrix}\right)$ 的一种三轴约定。
在尚未构造复方向的实接口中取 $Y=0$。

<a id="statement-2-2"></a>

#### 命题 2.2（既有三维失败读出）

<a id="eq-binary"></a>

$$
X^2+Y^2+Z^2\le1,\qquad
\boxed{\left\lVert a-b\right\rVert ^2=s(1-X).}\tag{2.1}
$$

当 $s=0$ 时，$a=b=0$，直接相容，无须归一化。

**证明。**

第一式等价于
$|\langle a,b\rangle |^2\le\left\lVert a\right\rVert ^2\left\lVert b\right\rVert ^2$；
第二式是展开差的平方范数。尺度 $s$ 仍须保留。

□

对两个非负标量权重 $A,B$，可以改用

<a id="eq-weight-sphere"></a>

$$
(X,Y,Z)=
\left(\frac{2\sqrt{AB}}{A+B},\,0,\,
\frac{A-B}{A+B}\right),\qquad A+B>0.\tag{2.2}
$$

它位于单位球面，并有 $A-B=(A+B)Z$；
$A=B$ 恰对应 $(1,0,0)$。$A=B=0$ 另行直接处理。

这里的三个坐标是局部二元关系的有限诊断，不要求整个历史载体只有三维。
若两个输出位于不同纤维，必须先有实际声明的共同目标或比较运输；
不能为了比较而暗中增加一个未给出的识别。

**白话图景。**先找出真正要相等的两个东西：两条路径的输出，或同一事件沿两种处理方式得到的权重。把它们与总尺度一起归一，偏差就进入三维关系球。随后再问，这个偏差能否沿历史传播、与别的偏差拼接；这一步才把局部诊断变成整体结论。

<a id="section-3"></a>

## 3. 共同复方向：一个实际参考门的同根有限证书

### 3.1 不预设完整连续参考流

<a id="statement-3-1"></a>

#### 定义 3.1（同根可逆历史扇区）

设 $(V,g)$ 为非零有限维实正内积空间，
$G\le O(V,g)$ 为已声明的可逆历史群。单位根 $\Omega_0$ 对 $G$ 循环，即

$$
\operatorname{span} _{\mathbb R }\{U\Omega_0:U\in G\}=V.
$$

这说明所讨论扇区由同一根的这些历史张成。给一个实际正交参考操作
$Q\in O(V,g)$，暂不要求 $Q^2=-I$ 或 $[Q,G]=0$。
定义顺序缺陷

$$
C_Q(U)=UQ-QU.
$$

<a id="statement-3-2"></a>

#### 引理 3.2（复合缺陷恒等式）

对任意 $U,W\in G$，

<a id="eq-cocycle"></a>

$$
\boxed{C_Q(UW)=U C_Q(W)+C_Q(U)W.}\tag{3.1}
$$

**证明。**

将右侧展开，两个中间项 $UQW$ 抵消。

□

<a id="statement-3-3"></a>

#### 定理 3.3（同根相容向整个循环扇区传播）

若
$C_Q(W)\Omega_0=0$ 对全部 $W\in G$ 成立，则 $Q$ 与全部 $G$ 对易。

**证明。**

由式 [(3.1)](#eq-cocycle)，

$$
C_Q(U)W\Omega_0
=C_Q(UW)\Omega_0-U C_Q(W)\Omega_0=0.
$$

这些 $W\Omega_0$ 张成 $V$，所以 $C_Q(U)=0$。

□

传播不再要求“缺陷算子本身与另一套运输代数对易”。
完整历史族对复合封闭，已经提供了传播关系。

**白话图景。**一次根上的比较只是一个方向。把同样的比较接在其他历史后面，就会检验根能够到达的其他方向。若这些历史张成整个扇区，两条路在所有这些方向上相遇，就足以让它们作为整体操作相同。

### 3.2 有限维只须有限前缀证书

<a id="statement-3-4"></a>

#### 定理 3.4（词长截断与有限锚证书）

设 $G$ 由有限对称生成集 $S=S^{-1}$ 生成，$D=\dim_{\mathbb R }V$。
若

$$
C_Q(W)\Omega_0=0\qquad(|W|\le D),
$$

则 $[Q,G]=0$。更具体地，可以选 $D$ 个词 $K_j$，
$|K_j|\le D-1$，使 $v_j=K_j\Omega_0$ 成基；
只检验这些 $K_j$ 与 $sK_j$（$s\in S$）的根缺陷就足够。

**证明。**

令
$V_\ell=\operatorname{span} \{W\Omega_0:|W|\le\ell\}$。
有
$V_{\ell+1}=V_\ell+\sum_{s\in S}sV_\ell$。
一旦 $V_{\ell+1}=V_\ell$，该空间对生成元及逆不变，因循环性必为整个 $V$。
在达到 $V$ 前，维数每步至少增一；由 $\dim V_0=1$ 得
$V_{D-1}=V$。

选择所述基。对任意 $s\in S$，

$$
C_Q(s)v_j
=C_Q(sK_j)\Omega_0-sC_Q(K_j)\Omega_0=0.
$$

所以 $C_Q(s)=0$，进而全部生成词都与 $Q$ 对易。

□

这是有限证书的存在与充分性证明，没有执行词枚举。
取得一组独立锚的实际成本与原生控制可达性仍由所声明的接口决定。

<a id="statement-3-5"></a>

#### 定理 3.5（根上半周校准推出共同复结构）

在定理 [3.4](#statement-3-4) 的全部假设及有限根证书成立时，再要求

<a id="eq-root-half-turn"></a>

$$
\boxed{Q^2\Omega_0=-\Omega_0.}\tag{3.2}
$$

则

<a id="eq-J"></a>

$$
\boxed{J:=Q,\qquad J^2=-I,\qquad J^*=-J,\qquad [J,G]=0.}\tag{3.3}
$$

定义

<a id="eq-h"></a>

$$
(a+ib)x=ax+bJx,\qquad
h(x,y)=g(x,y)+i\,g(Jx,y),\tag{3.4}
$$

便得到复内积，全部 $G$ 为复酉历史。

**证明。**

有限证书先给 $[Q,G]=0$。于是
$(Q^2+I)W\Omega_0=W(Q^2+I)\Omega_0=0$。
循环性给 $Q^2=-I$；正交性给 $Q^*=Q^{-1}=-Q$。

式 [(3.4)](#eq-h) 满足
$h(x,Jy)=ih(x,y)$、$h(Jx,y)=-ih(x,y)$、
$h(y,x)=\overline{h(x,y)}$，且 $h(x,x)=g(x,x)>0$（$x\ne0$）。
正交性及与 $J$ 对易使全部历史保持 $h$。

□

这条路线不需要实不可约性、连续参考流或预设单频谱。
实维数自动为偶数：单位 $x$ 与 $Jx$ 正交，其二维平面的正交补仍对 $J$ 不变，
逐步分解即可。
对历史 $x_h=U_h\Omega_0$，

$$
K(h,k)=g(x_h,x_k)+i\,g(Qx_h,x_k)
$$

是共同复正核，因为任意有限复系数的核二次型都是一个平方范数。

式 [(3.2)](#eq-root-half-turn) 必须是在同一内部相干参考下的有符号向量校准。
只知道 $[Q^2\Omega_0]=[\Omega_0]$ 不足：$Q=I$ 就满足该射线条件，却不给复结构。
推得 $J$ 后，$\cos\theta I+\sin\theta J$ 是数学相位群；实际门 $Q$ 的供应
不自动供应每个连续角度的门。

**白话图景。**一个内部参考操作，做两次恰把根带到有符号的反向；再核对它与一组覆盖历史的先后顺序是否一致。这些局部关系足够把“四分之一周”的含义传遍整个扇区。共同的乘 $i$ 因此由这个实际参考操作确定。

### 3.3 只测生成元上的根，为什么仍不够

在 $V=\mathbb C ^2$ 的实四维表示中取

$$
J(z_1,z_2)=(iz_1,iz_2),\quad \Omega_0=(1,0),
$$

$$
U(z_1,z_2)=(iz_2,z_1),\qquad
H(z_1,z_2)=(z_1,\overline{z_2}).
$$

二者均实正交，$U$ 与 $J$ 对易，而 $[H,J]\Omega_0=0$。
生成元及其逆的根测试都通过，且

$$
\Omega_0,U\Omega_0,U^2\Omega_0,U^3\Omega_0
=(1,0),(0,1),(i,0),(0,i)
$$

张成整个实空间。但

$$
[HU,J]\Omega_0=(0,-2i)\ne0.
$$

所以需要覆盖复合历史，不能把定理的有限词证书缩成一次生成元测试。

两个实际比较值是 $WQ\Omega_0$ 与 $QW\Omega_0$，范数都为一。
其三维读出可取 $(X,0,0)$，且
$\left\lVert C_Q(W)\Omega_0\right\rVert ^2=2(1-X)$。
半周校准同样比较 $Q^2\Omega_0$ 与 $-\Omega_0$。

**白话图景。**每道门单独在根上看起来都没有扭曲参考，接起来却可能在新方向上扭曲。反例的失败准确发生在第二段历史。有限锚证书的作用，就是让这些新方向也真正接受同一种比较。

### 3.4 有限证书的误差如何传导

<a id="statement-3-6"></a>

#### 命题 3.6（带锚条件数的稳定界）

对所选单位锚 $v_j=K_j\Omega_0$，设
$F=\sum_{j=1}^D v_jv_j^*\succeq aI$，$a>0$。
若证书中的全部根缺陷至多 $\varepsilon$，则

$$
\left\lVert [s,Q]\right\rVert \le2\varepsilon\sqrt{D/a}\quad(s\in S).
$$

对长度为 $L$ 的词，

$$
\boxed{\left\lVert [W,Q]\right\rVert \le
\min\{2,\ 2L\varepsilon\sqrt{D/a}\}.}
$$

**证明。**

复合恒等式给 $\left\lVert C_Q(s)v_j\right\rVert \le2\varepsilon$。因此
$a\left\lVert C_Q(s)\right\rVert _{\rm HS}^2 \le\sum_j\left\lVert C_Q(s)v_j\right\rVert ^2\le4D\varepsilon^2$。
算子范数不超过 Hilbert--Schmidt 范数。对词反复使用
[(3.1)](#eq-cocycle)，正交因子不放大范数；两个正交乘积之差也至多为二。

□

本界控制路由相容误差；近似半周校准要另计误差。
循环性只保证某个 $a>0$，不保证跨模型的一致下界。

**白话图景。**锚点若几乎落在同一个方向，小读数误差就可能掩盖别处的大偏差。
证书既要覆盖，也要保持足够分离。这个分离量明确出现在误差界里，
没有藏在“近似相容”四个字中。

<a id="section-4"></a>

## 4. 共同方向怎样沿历史拼接：允许闭路留下相位

<a id="statement-4-1"></a>

#### 定理 4.1（共同复结构的延拓判据）

设连通运输群胚给实正内积纤维 $V_x$ 及正交运输 $T_e$。
根纤维已取得正交复结构 $J_0$。下列条件等价：

1. $J_x=T_pJ_0T_p^{-1}$ 与根到 $x$ 的路径 $p$ 无关；

2. 所有根闭路运输 $H$ 满足 $HJ_0=J_0H$；

3. 存在唯一根值为 $J_0$ 的复结构族，满足 $T_eJ_x=J_yT_e$。

**证明。**

两条路线 $p,q$ 的差为根闭路 $H=T_q^{-1}T_p$，而两共轭结果相同恰等价于
$HJ_0H^{-1}=J_0$。路径无关时，把根到 $x$ 的路径接上 $e:x\to y$，
立即给交织关系。任何相容族沿路径都必须取上述共轭值，故唯一。

□

若该运输群胚由一张有限连通图的边及其逆生成，选生成树，令 $F_x$ 为树路线运输，并设
$H_e=F_y^{-1}T_eF_x$。则

$$
T_eJ_x-J_yT_e
=F_y(H_eJ_0-J_0H_e)F_x^{-1}.
$$

树边缺陷自动为零，检查非树边的完整算子缺陷便足够。

共同方向无歧义不等于所有闭路都为恒等。
$H=e^{\theta J_0}$ 与 $J_0$ 对易，却可以留下非零相位；
更高复维还允许一般与 $J_0$ 相容的酉闭路。
这与上一轮圆周的水平相位完全相容。

V63 定理 2.3 已有边交织，直接使用本判据即可；其命题 2.4 的平坦性
来自更强的控制关系。不能把第 3 节的循环性反过来添加为 V63 的新门槛：
平坦配置群胚的闭路群甚至可以只有恒等。

**白话图景。**参考沿两条历史搬到同一处，四分之一周的含义必须相同；
两条历史本身仍可留下相对相位。这保留了前轮圆弧与闭环相位，
同时说明共同复方向属于整个运输网络的相容结构。

<a id="section-5"></a>

## 5. 整体正性已经有二元入口：使用全部合成对象

<a id="statement-5-1"></a>

#### 定理 5.1（V77 的合成二元球判据；既有结果）

设含幺复 $*$ 代数上的响应 $\ell$ 为 Hermitian 线性泛函，
$\ell(1)=1$。整体正性
$\ell(p^*p)\ge0$ 对全部 $p$ 成立，
等价于所有正迹合成二元关系块归一后位于三维单位球。
只测试第一元为 $1$、第二元为任意可缩放合成对象，已足够。

**证明。**

正泛函使任意二元 Gram 块半正定，归一球条件随之成立。
反向，若 $\ell(p^*p)=-d<0$，取 $b=p/\sqrt{2d}$。
二元块 $(1,b)$ 的对角为 $(1,-1/2)$、迹为 $1/2$；
归一后纵坐标为 $3$，在球外，矛盾。

□

这里 $p$ 包含历史词的有限线性组合，不能缩成原始历史词。
V77 给出的反例是 $\mathbb C [\mathbb Z _3]$ 中
$g^3=1$、$g^*=g^2$、$\ell(g)=\ell(g^2)=-3/4$：
任意原始词对都给正块，但 $p=1+g+g^2$ 满足
$\ell(p^*p)=-3/2$。

任意有限相干表达式可以写成二元树：叶子为历史，内节点为带系数合并。
全程保留尺度与交叉项，树表达便覆盖上述全部 $p$。
这只是既有判据的递归表达，原生可执行树的范围仍由具体菜单给定。

同一核中的零关系
$\sum_hc_h\psi_h=0$ 定义同一输入的不同表达。
后面所有结果核和后继映射，都必须尊重这个相同概念。

**白话图景。**二元方法已经足以检查整体，但每个“元”必须允许是前面合成出的关系。
只看最初几根线，会漏掉合起来才出现的冲突。
把合成结果继续作为下一层的两个元，三维诊断就能递归覆盖完整有限关系。

<a id="section-6"></a>

## 6. 事件读出无需先给算符：两端口重编码已经锁定形式

### 6.1 同一事件沿两条内部路由读取

现在使用已经取得的共同复空间 $\mathscr H$、实内积 $g$ 与共同 $J$。
令 $D\subseteq\mathscr H$ 为稠密、实线性且 $J$ 稳定的声明相干表达式空间。
概率的平方标尺与同根绑定继承 V64、V78 及前轮结果[1](#ref-previous)。
本节研究事件对输入方向的依赖，无须重开概率标定问题。

<a id="statement-6-1"></a>

#### 定义 6.1（事件权重及两路重编码）

有限完备事件菜单 $\mathcal E$ 给未归一权重 $w_e:D\to\mathbb R$，要求

<a id="eq-normalization"></a>

$$
w_e(u)\ge0,\qquad
\sum_{e\in\mathcal E}w_e(u)=q(u):=\left\lVert u\right\rVert ^2.\tag{6.1}
$$

对一对内部路径 $u,v$，比较

$$
A_e(u,v)=w_e(u)+w_e(v),
$$

$$
B_e(u,v)=w_e\!\left(\frac{u+v}{\sqrt2}\right)
          +w_e\!\left(\frac{u-v}{\sqrt2}\right).
$$

要求同一粗事件在声明的平衡路径重编码下保持：

<a id="eq-balanced"></a>

$$
\boxed{A_e(u,v)=B_e(u,v).}\tag{6.2}
$$

再要求共同四分之一转保持同一事件：

<a id="eq-J-readout"></a>

$$
\boxed{w_e(Ju)=w_e(u).}\tag{6.3}
$$

式 [(6.2)](#eq-balanced) 比较“先分别报告再忽略路径标签”与
“先平衡混合路径再报告并忽略标签”。
它仅作用于声明为不区分这个路径地址的同一粗事件；
若事件本来就读取路径，便不是这两个路由共同表示的同一事件。
平衡混合本身也须在所讨论接口中声明，数学表达式不自动供应实际门。

式 [(6.3)](#eq-J-readout) 的 $J$ 同时作用于该输入表达式包含的全部相干分支。
只转动其中一臂、而保留内部参考臂不动，是另一个输入，
不受“共同相位不改变同一事件”约束。

**白话图景。**先有一个已经定义清楚的事件，例如只问输出是否进入某个目标，
而不问来自哪条地址。两条地址经过可逆的平衡重编码后，
这个粗事件的总权重必须相同；整个输入一起转四分之一周，
也必须仍在回答同一个问题。效果算符将从这两项关系中得到。

### 6.2 重编码给平行四边形，无需先假设齐次性

<a id="statement-6-2"></a>

#### 引理 6.2（平衡重编码推出平行四边形）

在 [(6.1)](#eq-normalization) 下，式 [(6.2)](#eq-balanced) 推出

<a id="eq-parallelogram"></a>

$$
w_e(u+v)+w_e(u-v)=2w_e(u)+2w_e(v).\tag{6.4}
$$

**证明。**

归一性和非负性给 $w_e(0)=0$、$0\le w_e(u)\le q(u)$。
在 [(6.2)](#eq-balanced) 中令 $v=0$，得到
$w_e(u/\sqrt2)=w_e(u)/2$。代回即得
[(6.4)](#eq-parallelogram)。

□

<a id="statement-6-3"></a>

#### 定理 6.3（事件重编码等价于唯一复效果）

条件 [(6.1)](#eq-normalization)、[(6.2)](#eq-balanced)、
[(6.3)](#eq-J-readout) 等价于存在唯一效果族

<a id="eq-event-effect"></a>

$$
\boxed{
0\preceq E_e\preceq I,\quad
\sum_eE_e=I,\quad
w_e(u)=h(u,E_eu)\quad(u\in D).
}\tag{6.5}
$$

无需额外假设 $w_e$ 连续、实齐次、复齐次或在全部相位下不变。

**证明。**

固定一个事件，省略下标。由平行四边形式得到
$w(-u)=w(u)$、$w(2u)=4w(u)$。
定义实极化

$$
b(u,v)=\frac{w(u+v)-w(u-v)}4.
$$

它对称。把平行四边形式分别用于 $(u+v,z)$ 与 $(u-v,z)$，相减给

$$
b(u+z,v)+b(u-z,v)=2b(u,v).
$$

令 $z=u$，得 $b(2u,v)=2b(u,v)$；
再以 $u=(x+y)/2,z=(x-y)/2$ 代入，得
$b(x+y,v)=b(x,v)+b(y,v)$。

又有

$$
|b(u,v)|\le\frac{w(u+v)+w(u-v)}4
=\frac{w(u)+w(v)}2
\le\frac{\left\lVert u\right\rVert ^2+\left\lVert v\right\rVert ^2}{2}.
$$

所以对固定 $v$，可加映射 $u\mapsto b(u,v)$ 在单位球有界，
自动连续并实线性。对称性给双线性，且
$b(u,u)=w(u)\ge0$。
由正形式的 Cauchy--Schwarz 不等式，
$|b(u,v)|^2\le w(u)w(v)\le\left\lVert u\right\rVert ^2\left\lVert v\right\rVert ^2$，
故 $b$ 唯一连续延拓到完成空间。

共同 $J$ 相容经极化给
$b(Ju,Jv)=b(u,v)$，以及
$b(Ju,v)=-b(u,Jv)$。于是

$$
k_e(u,v)=b(u,v)+i\,b(Ju,v)
$$

是 Hermitian 半双线性形式，对角为 $w(u)$。
也可先把 $b$ 表示为 $g(u,A_ev)$：
实 Riesz 表示给有界自伴 $A_e$；
$b(Ju,Jv)=b(u,v)$ 给 $A_eJ=JA_e$，所以它是复线性的 $E_e$。
$0\le w(u)\le\left\lVert u\right\rVert ^2$ 给 $0\le E_e\le I$。

全部事件权重求和等于 $q$，极化及稠密性给 $\sum_eE_e=I$。
矩阵元由极化唯一决定，故效果唯一。
反向，效果二次型直接满足三项路由条件。

□

这里使用平行四边形极化这一标准工具；Jordan--von Neumann 原始论文给出了
相应几何判据[10](#ref-jvn)。本文以上针对有界半正事件权重给出完整证明。

<a id="statement-6-4"></a>

#### 推论 6.4（自动得到的性质）

对任意 $z\in\mathbb C$、$u\in D$，

$$
w_e(zu)=|z|^2w_e(u),\qquad
w_e(e^{\theta J}u)=w_e(u).
$$

事件交叉关系也不再是另给的数据：

$$
K_e(h,k)=k_e(\psi_h,\psi_k)
=h(\psi_h,E_e\psi_k).
$$

**白话图景。**两条路径平衡混合前后的总报告一致，已经迫使权重服从平行四边形关系。
把同向比较与四分之一转后的比较合起来，就锁住一个复二次型。
连续性、平方缩放和完整相位不变性随之成立；
效果矩阵只是这项内部读出关系的唯一表示。

### 6.3 撤去哪条条件，会留下怎样的失败

在 $\mathbb C ^2$ 上取

$$
w(z_1,z_2)=
\begin{cases}
|z_1|^4/(|z_1|^2+|z_2|^2),&(z_1,z_2)\ne0,\\
0,&(z_1,z_2)=0.
\end{cases}
$$

它非负、不超过总量，补事件可取 $q-w$，并满足全部共同相位不变性，
甚至已经有 $w(zu)=|z|^2w(u)$。
但对 $u=(1,0),v=(0,1)$，

$$
A(u,v)=1,\qquad B(u,v)=\frac12.
$$

同一粗事件因路径重编码而改变，故不是任何固定效果的二次型。
平方径向缩放本身没有代替事件方向的相容。

撤去共同 $J$ 相容，则 $\mathbb C$ 上
$w(z)=(\operatorname{Re}z)^2$ 满足平行四边形和权重界，却有
$w(1)=1,w(i)=0$；它只给实二次型，不能表示声明共同复结构下的同一射线事件。

两条权重路由的失败正是 $A_e-B_e\ne0$；
用式 [(2.2)](#eq-weight-sphere) 即得有限三维见证。
非负性若撤去，$w=-q$、补权重 $2q$ 虽满足代数恒等式，
却直接给负报告，另一条定义约束随即失败。

**白话图景。**只保证每张表上数字非负、相加为一，还可能让同一事件随着地址拆法改变。
只保证实二次型，又可能偷偷依赖一个绝对相位方向。
反例把这两种失配分别落在一对权重值上，
说明每条相容条件具体排除了什么。

<a id="section-7"></a>

## 7. 结果核就是内部效果：把既有重构抽取成一个等价

<a id="statement-7-1"></a>

#### 定义 7.1（共同核中的结果核）

设 $K(h,k)=h(\psi_h,\psi_k)$ 是已有共同正核，
$\mathscr H_K=\overline{\operatorname{span} }\{\psi_h\}$ 为其最小实现。
写 $0\preceq L\preceq K$，表示 $L$ 与 $K-L$ 都对全部有限历史和系数为正。
这不是各条目的大小关系。

<a id="statement-7-2"></a>

#### 定理 7.2（正子核与效果的规范对应）

映射

$$
E\longmapsto K_E,\qquad
K_E(h,k)=h(\psi_h,E\psi_k)
$$

给序同构

<a id="eq-kernel-order"></a>

$$
\boxed{[0,I]_{\rm effect}\ \cong\ [0,K]_{\rm kernel}.}\tag{7.1}
$$

有限族还满足

$$
\sum_eK_e=K\iff\sum_eE_e=I.
$$

**证明。**

给 $0\preceq L\preceq K$。对有限表达式
$x=\sum_hc_h\psi_h$、$y=\sum_kd_k\psi_k$，
拟定义 $b_L(x,y)=\sum_{h,k}\bar c_hL(h,k)d_k$。
若 $x=0$，则
$0\le c^\dagger Lc\le c^\dagger Kc=0$。
正形式的 Cauchy--Schwarz 不等式给 $c^\dagger Ld=0$，
所以它与表达方式无关。

同一不等式又给 $|b_L(x,y)|\le\left\lVert x\right\rVert \left\lVert y\right\rVert$，
故延拓为有界半双线性形式，并有唯一 $0\le E\le I$ 使
$b_L(x,y)=h(x,Ey)$。
反向，任意效果给的核及补核显然正。
最小性保证矩阵元唯一决定算符；核差的正性恰等价效果差的正性，
故为序同构。有限求和对应由同一唯一性得到。

□

此定理是 V68 核到仪器结论的直接抽取：
把 $L$ 与 $K-L$ 当作两结果正核，即可复用其下降证明[4](#ref-v68)。
本轮不把它认领为此前效果结构的空白。

### 7.1 只检查原始历史概率为什么会漏掉冲突

取两个正交历史，令

$$
K=I_2,\qquad
L=\frac34
\begin{pmatrix}1&1\\1&1\end{pmatrix}.
$$

原始两历史的报告权重都是 $3/4$，且 $L\succeq0$。
但对 $x=(\psi_1+\psi_2)/\sqrt2$，候选权重为 $3/2$。
补事件为 $-1/2$，二元报告的 Bloch 纵坐标是
$2(3/2)-1=2$，位于球外。

一般地，$L\preceq K$ 失败意味着某个有限表达式在结果中比总量还大。
若其总量正，归一后得到 $p>1$；若总量为零，
已经出现“同一零输入在输出中不为零”的身份冲突。
再加任意小的非零输入扰动，可令总量严格正而保持超额，得到相同球外报告。

**白话图景。**事件读出就是整体关系表中可以分出的一份正关系。
它既不能有负质量，也不能比整体还大。
当某种写法把同一个零对象报告为非零，或把一份结果报告得比总量更大，
失败就落在两个可比较的内部表达式上。

<a id="section-8"></a>

## 8. 指定后继锁定线性分支，完整正性成为结论

<a id="statement-8-1"></a>

#### 定理 8.1（实际后继的唯一线性下降；既有机制的抽取）

给定实际输出空间 $\mathscr W_e$ 与次归一输出向量族 $\phi_{e,h}$，满足

$$
h(\phi_{e,h},\phi_{e,k})=K_e(h,k),\qquad
0\preceq K_e\preceq K.
$$

则存在唯一有界复线性收缩
$M_e:\mathscr H_K\to\mathscr W_e$，使

$$
M_e\psi_h=\phi_{e,h},\qquad M_e^*M_e=E_e.
$$

**证明。**

在有限表达式上定义
$M_e(\sum_hc_h\psi_h)=\sum_hc_h\phi_{e,h}$。
核序给

$$
\left\lVert \sum_hc_h\phi_{e,h}\right\rVert ^2
=c^\dagger K_ec\le c^\dagger Kc
=\left\lVert \sum_hc_h\psi_h\right\rVert ^2.
$$

零输入必给零输出，因此映射良定、线性且为收缩，唯一延拓到闭包。
比较全部历史交叉矩阵元，得到 $M_e^*M_e=E_e$。

□

这一步明确实现了定义间约束：

$$
\sum_hc_h\psi_h=0
\ \Longrightarrow\
\sum_hc_h\phi_{e,h}=0.
$$

同一个输入的两种表达，在任何指定结果分支里都不能突然分裂成不同对象。

<a id="statement-8-2"></a>

#### 推论 8.2（内部记录、Born 读出与 CP/TP）

若 $\sum_eK_e=K$，则

$$
Vx=\bigoplus_eM_ex,\qquad V^*V=I.
$$

第 $e$ 个坐标投影记为 $P_e$，有 $E_e=V^*P_eV$。
沿用已取得的同根平方标尺，

$$
p(e|h)=K_e(h,h)=\left\lVert M_e\psi_h\right\rVert ^2
=h(\psi_h,E_e\psi_h)
$$

对单位输入成立。既有密度表示中的未归一分支为

$$
\mathcal I_e(\rho)=M_e\rho M_e^*.
$$

它完全正；完整菜单保迹。

**证明。**

归一核求和给 $\sum_eM_e^*M_e=I$，所以 $V$ 等距。
概率式使用前轮已完成的权重及来源标定。
对任意有限内部参考空间和正算符 $X$，

$$
(\mathcal I_e\otimes{\rm id})(X)
=(M_e\otimes I)X(M_e^*\otimes I)\succeq0.
$$

故分支完全正。对全部结果求迹，
$\sum_e\operatorname{Tr} \mathcal I_e(\rho)=\operatorname{Tr} \rho$。

□

因此，在这条核守恒与实际后继的路线中，CP 不是另一条独立输入。
若粗结果还隐藏多个内部记录，可对细分支求和，或对内部环境求偏迹；
不能把任意粗结果一概当成单个 Kraus 算子。

条件后态 $\mathcal I_e(\rho)/\operatorname{Tr} \mathcal I_e(\rho)$ 一般非线性，
不称为 CP 映射；零概率结果不定义此条件态。
$V\rho V^*$ 保留记录间相干交叉项，分块去相干后才得到经典结果记录。
等距记录的表示若要成为可执行步骤，仍使用项目已声明的记录容量和控制。
这些算子表示的标准背景见作者公开教材[11](#ref-watrous)。

**白话图景。**一个过程给每段输入历史指定后继，所有旧的零关系必须在每个后继中继续为零。
于是门不能任意依赖表达式的写法，只能下降成同一个线性映射。
所有结果一起保存时总关系不丢，放入内部参考后也保持正性，
量子仪器和完全正性就在这项一致性中出现。

### 8.1 效果相同不等于后态已经固定

单有 $E=I$，既可取 $M=I$，也可取 $M=X$（二态翻转）。
它们给同一结果核 $K_e=K$，但在固定输出锚下，
输入 $|0\rangle$ 分别变成 $|0\rangle$ 与 $|1\rangle$，
后续读口可区分。

同核只确定最小输出向量族之间的等距同构；
若实际输出锚和后续读口已固定，就不能把任意改变后态称为不可见规范。
定理 [8.1](#statement-8-1) 的唯一性明确使用指定的 $\phi_{e,h}$。
这一边界也继承了项目 Quantum Principles 对分支与相干记录提升的区分[9](#ref-principles)。

**白话图景。**“这次事件发生多少”与“发生以后到了哪里”是两个关系。
概率相同，不代表后续历史相同。
把实际后继也放回同一整体后，输入、结果和下一步才能一起锁定。

<a id="section-9"></a>

## 9. 关系的关系继续递归：有限结果树的闭合定理

<a id="statement-9-1"></a>

#### 定理 9.1（后续结果核的拉回）

第一分支为 $M_e$，其实际输出为 $\phi_{e,h}=M_e\psi_h$。
输出上的下一效果为 $F_{f|e}$。定义联合核

$$
K_{ef}(h,k)=h(\phi_{e,h},F_{f|e}\phi_{e,k}).
$$

则其输入效果为

<a id="eq-sequential"></a>

$$
\boxed{E_{ef}=M_e^*F_{f|e}M_e.}\tag{9.1}
$$

若后续菜单完备，则
$\sum_fK_{ef}=K_e$、$\sum_fE_{ef}=E_e$。

**证明。**

代入 $\phi_{e,h}=M_e\psi_h$，即得式 [(9.1)](#eq-sequential) 的全部矩阵元，
由定理 [7.2](#statement-7-2) 唯一性成立。
对 $f$ 求和并使用 $\sum_fF_{f|e}=I$ 即得后两式。

□

反向也成立：若只给 $0\preceq K_{ef}\preceq K_e$，
可在分支的最小输出闭包
$\mathscr W_e^{\min}=\overline{\operatorname{span} }\{\phi_{e,h}\} =\overline{\operatorname{ran}  M_e}$
上重用定理 [7.2](#statement-7-2)，得到唯一后续效果的压缩。
从未被该分支到达的输出方向不由这些核决定。

<a id="statement-9-2"></a>

#### 定理 9.2（有限正核结果树）

为每个已声明的有限结果前缀 $w$ 给正核 $K_w$，每个节点的子结果集有限。
只在已声明细分的非叶节点要求父子求和：

<a id="eq-tree"></a>

$$
\boxed{K_\varnothing=K,\qquad
\sum_fK_{wf}=K_w.}\tag{9.2}
$$

则每个核的最小表示之间有规范线性收缩
$A_{f|w}:\mathscr H_{K_w}\to\mathscr H_{K_{wf}}$，
使每个节点的分支合并等距。
沿有限路径的复合，是将每个根历史向量 $\psi_h$ 送到指定规范向量
$\psi_{w,h}$ 的唯一映射。
完备有限截口指每条最大路径恰穿过一次的有限前缀无关集合；
其路径效果之和为 $I$。

**证明。**

每项 $K_{wf}\preceq K_w$，所以对核的规范历史向量定义
$A_{f|w}\psi_{w,h}=\psi_{wf,h}$，
由定理 [8.1](#statement-8-1) 得良定收缩。
节点求和给 $\sum_fA_{f|w}^*A_{f|w}=I$。
沿路径逐次复合，对每个历史都到达指定的 $\psi_{w,h}$，
最小性给唯一性。由叶向根反复使用节点恒等式，
得到任意完备有限截口的总效果为 $I$。

□

对同一根的输入历史，若父结果权重非零，则

$$
p(f|w,h)=\frac{K_{wf}(h,h)}{K_w(h,h)}.
$$

粗粒化是核相加，后续是沿实际分支拉回，完整树是这两种关系的反复组合。
本定理处理有限层级的闭合；它没有将不同门顺序判为相同，
合流仍须指定输出或公共读口相容。

**白话图景。**一次结果从整体关系表里分出一份；下一次观测继续细分这一份。
每层子份加起来恰好是父份，后续读口沿实际历史搬回同一根。
这样整棵观察树都由同一张整体关系表支撑，概率、门与记录可以逐层复用，
不必每层另加一套测量规则。

<a id="section-10"></a>

## 10. 同根绑定与旧模型排除：准确保留，不再重开

### 10.1 概率已经绑定哪一个根

前轮及 V78 已在各自声明的接口中证明同根绑定。其关键校准为

$$
p_0(P_{\Omega_0})=1,\qquad
p_h(E)=p_0(U_h^*EU_h),
$$

它锁定 $p_h(E)=h(U_h\Omega_0,E U_h\Omega_0)$[1](#ref-previous)、[7](#ref-v78)。
有限维时可以先取得密度表示，再由根校准把支撑限制在一维根子空间。
若本稿的核完成为无限维，则不必先声称每个正读出都有密度算符；
下面直接证明已校准的这个读出必为根向量态。

<a id="statement-10-1"></a>

#### 命题 10.1（纯根校准直接锁定 Born 读出）

设同一个读出 $p_0$ 定义在 $\mathscr H$ 的全部效果上，非负且 $p_0(I)=1$，
并对任意 $E,F\succeq0$、$E+F\preceq I$ 满足
$p_0(E+F)=p_0(E)+p_0(F)$。
若单位根满足 $p_0(P_{\Omega_0})=1$，则在任意 Hilbert 维数下，

$$
\boxed{p_0(E)=h(\Omega_0,E\Omega_0).}
$$

加上准备协变，便得到所有所声明历史的同根 Born 读出。

**证明。**

效果可加和非负给单调性；先用整数细分得到有理齐次，再用单调夹逼得到实齐次。
经正锥缩放和自伴差分，$p_0$ 唯一延为 $B(\mathscr H)$ 上的正归一线性泛函
$\varphi$。这一步不预设正规性。

令 $P=P_{\Omega_0}$、$Q=I-P$，则 $\varphi(Q)=0$。
正泛函的 Cauchy--Schwarz 不等式给
$|\varphi(QA)|^2\le\varphi(Q)\varphi(A^*A)=0$，
共轭对称性再给 $\varphi(AQ)=0$。
因此

$$
\varphi(A)=\varphi(PAP)
=h(\Omega_0,A\Omega_0)\varphi(P)
=h(\Omega_0,A\Omega_0).
$$

最后代入准备协变即得结论。该已标定状态的正规性由此成为结论，
并未对未经根校准的全部状态作相同声明。

□

本轮的 $w_e$ 使用这套既有标尺及来源约定。
第 6 节的工作是从两路事件相容重建其方向依赖和效果表示，
没有再把几何范数直接等同于未经标定的实验概率。

### 10.2 其他模型在什么定义类内已被排除

Atlas §26 在有限维有序操作载体上，以纯态最小饱和效果的互易性和带符号帧分解，
得到状态--效果配对的正定自对偶几何。
§29 再使用同节声明的强对称、连通纯态传递、秩乘法和局部层析自复合，
选出复 Hermitian 矩阵型[8](#ref-atlas)。

其中一个已有二元失败见证十分直观。实理论标准复合中令

$$
A_0=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\quad
B=A_0\otimes A_0,\quad
\rho_\pm=\frac{I_4\pm B}{4},\quad
P=\frac{I_4+B}{2}.
$$

有 $B^T=B$、$B^2=I$、$\operatorname{Tr}  B=0$，所以 $\rho_\pm$ 为合法实密度。
对任意实对称局部效果 $E,F$，
$\operatorname{Tr} (A_0E)=\operatorname{Tr} (A_0F)=0$，故

$$
\operatorname{Tr} (\rho_+(E\otimes F))
=\operatorname{Tr} (\rho_-(E\otimes F))
=\frac{\operatorname{Tr}  E\,\operatorname{Tr}  F}{4}.
$$

但 $\operatorname{Tr} (P\rho_+)=1$、$\operatorname{Tr} (P\rho_-)=0$。
两个整体在所有局部乘积读口上相同，在声明的整体读口上不同；
所以局部乘积概念无法回答那个整体问题。
这正是已证明的局部层析失败，不需要重新问是否存在任何排除。

**白话图景。**我们已经知道概率在回答哪一个根，也已有模型分类的明确筛选。
例如两个整体若在全部局部读数上相同，却被一个整体问题分开，
失败就落在这两个整体之间：原先的局部概念漏掉了那项关系。
分类条件的作用由这个内部冲突说明，既有排除结论继续保留。

<a id="section-11"></a>

## 11. 本轮的统一闭合：哪些性质不再需要独立列入

<a id="statement-11-1"></a>

#### 定理 11.1（给定内部接口后的关系闭合）

在前述已取得的表示、标定和合法操作范围内，使用以下相容数据：

1. 已有共同 $J$，或第 3 节的实际参考门及同根有限证书；

2. 全部合成二元对象的整体正性判据及共同最小历史表示；

3. 完备非负事件权重的平衡重编码与共同 $J$ 相容；

4. 结果核与指定实际后继核相同，并在结果前缀处求和守恒。

则效果算符、结果核、唯一指定分支、内部等距记录、
同根 Born 读出、CP/TP 与有限序贯组合，
都是这些数据的派生结构。

**证明。**

第 1 项通过既有定理或定理 [3.5](#statement-3-5) 固定共同复方向；
第 2 项由 V77 判据及既有最小核表示实现同一整体。
定理 [6.3](#statement-6-3) 从第 3 项得到唯一效果及结果核。
定理 [7.2](#statement-7-2) 给两者的规范对应，
定理 [8.1](#statement-8-1) 从第 4 项得到唯一下降。
其推论给记录等距与 CP/TP；概率使用已有同根标定。
最后用定理 [9.1](#statement-9-1)、[9.2](#statement-9-2) 递归闭合。

□

| 原先单列的性质 | 现在由哪项关系推出 | 删除该关系后的见证 |
| --- | --- | --- |
| 共同复线性 | 有符号半周校准与覆盖历史的顺序相容 | 单根生成元通过，二步历史失败 |
| 效果的 Hermitian 形式 | 平衡重编码、共同四分之一转及权重界 | 四次方向权重或绝对实轴读出 |
| 完整相位不变、齐次与连续 | 极化后的有界复二次型 | 不必另列为本路线前件 |
| 整体结果合法性 | 结果核及补核的全有限正性 | 合成输入给 $p>1$ 或零输入非零输出 |
| 门的分支线性 | 指定后继保持全部输入零关系 | 同一输入两种表达给不同后继 |
| 完全正与完整保迹 | 实际线性分支及前缀核守恒 | 保留内部参考后出现关系冲突 |
| 后续事件组合 | 核拉回与父子求和 | 同一联合事件因分层写法改变 |

这里的简化有具体内容：某些全空间条件被有限证书替代，
某些算符性质由更基本的读出路由关系推出，既有核到仪器结论被统一复用。
并未宣称这四个条目是在所有可能逻辑语言中的绝对最少公理数。

在图形直觉上，所有条件都在询问同一件事：
两个被定义为同一对象的内部表达，沿共同读口或共同后继，
是否继续保持相同。不同种类的相同必须保留各自的类型：
射线相同、带相干参考的向量相同、同一效果、同一后继和同一完整历史，
不能互相替代。

**白话图景。**把“公理内生”落实以后，复数、测量和量子门都不是图外单独悬着的物件。
共同参考由内部路线校准；事件由同一对象在不同重编码下的稳定读出定义；
门由旧关系在指定后继里继续成立定义。
这些定义彼此约束，迫使其表示具有共同复结构、正效果和线性仪器。

<a id="section-12"></a>

## 12. 完整白话图景

把 $\Omega$ 想成一张包含全部内部历史、参考、读口和记录的关系网。
根走过不同历史，会到达不同方向；在根上校准过的四分之一周操作，
只要与一组覆盖这些方向的路线相容，就能沿整张网保持同一个含义。
这个共同操作成为乘 $i$。

观察者在网内提出一个事件。两条地址先分别报告，
或先经过平衡重编码再忽略地址，都仍然在问同一个事件，
所以总权重必须一致。把这项一致性与共同参考结合，
事件的权重就被锁成一个复二次型；效果算符是它的表示。

每个事件从整体关系表里分出一份正关系。
实际后继必须保存输入原有的全部相同关系，
于是后继自动成为同一个线性分支。
所有结果加回去仍是原整体，便得到内部等距记录、同根概率和完全正的过程。
下一次观测继续细分这一份，整棵结果树始终留在同一张关系网内。

此前取得的圆弧、椭圆读出和周期也接在这里：
共同参考保证各处相位方向可比较，实际门决定轨迹，
内部读口决定保留哪部分关系，记录决定是否仍能区分走过的历史。
已经证明的结构继续向前工作；本轮把它们之间的接口锁得更紧，
并把能够由相容推出的性质从独立前件中移出。

## 资料与可复核位置

<a id="ref-previous"></a>

**[1]**
[从二元失败见证到整体量子关系：v78 后续研究](https://github.com/the-omega-institute/trureturing/blob/31fa401a7c17858fa323ddd0886ed580e0c57347/docs/develop/theory/AURIC_BINARY_FAILURE_WITNESSES_AND_GLOBAL_QUANTUM_RELATIONS_V78_CONTINUATION.md)。
§4 共同参考、复结构与同根残差；§5 平方及同根 Born 绑定；§7 稳定核闭合。
本轮明确承接其已证结果。
<a id="ref-v53"></a>

**[2]**
[V53：Sharp Three-Axis Readouts, Endogenous Complex Structure and Common Phase Compatibility](https://github.com/the-omega-institute/trureturing/blob/31fa401a7c17858fa323ddd0886ed580e0c57347/docs/develop/theory/AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md)。
§4 三轴构造复结构；§8 运输相容及内部记录生成效果。
<a id="ref-v63"></a>

**[3]**
[V63：Native Complex Structure, Stable Assembly and Finite Born Readout Certificates](https://github.com/the-omega-institute/trureturing/blob/31fa401a7c17858fa323ddd0886ed580e0c57347/docs/develop/theory/AURIC_NATIVE_COMPLEX_STRUCTURE_STABLE_ASSEMBLY_AND_FINITE_BORN_READOUT_CERTIFICATES_V63.md)。
定理 2.3 已给原生共同复结构；命题 2.4 另给配置平坦性。
<a id="ref-v68"></a>

**[4]**
[V68：Visible Relation Rank, Compatible Constraints and Quantum Axioms](https://github.com/the-omega-institute/trureturing/blob/31fa401a7c17858fa323ddd0886ed580e0c57347/docs/develop/theory/AURIC_VISIBLE_RELATION_RANK_COMPATIBLE_CONSTRAINTS_AND_QUANTUM_AXIOMS_V68.md)。
§7 定义 7.1--7.3、定理 7.4 及编者范围说明。
<a id="ref-v77"></a>

**[5]**
[V77：Reverse Location of Quantum Axioms, Binary Witnesses and Internal Compatibility](https://github.com/the-omega-institute/trureturing/blob/31fa401a7c17858fa323ddd0886ed580e0c57347/docs/develop/theory/AURIC_REVERSE_LOCATION_OF_QUANTUM_AXIOMS_BINARY_WITNESSES_AND_INTERNAL_COMPATIBILITY_V77.md)。
§3 定理 3.2；§6 完整参考；§7 粗细读出；§8 共同定向。
<a id="ref-v74"></a>

**[6]**
[V74：Smooth Quantum Histories, Cotangent Dynamics and Endogenous Motion](https://github.com/the-omega-institute/trureturing/blob/31fa401a7c17858fa323ddd0886ed580e0c57347/docs/develop/theory/AURIC_SMOOTH_QUANTUM_HISTORIES_COTANGENT_DYNAMICS_AND_ENDOGENOUS_MOTION_V74.md)。
§3 平移不变正历史核与自治演化。
<a id="ref-v78"></a>

**[7]**
[V78：Gate Manifolds, Integrable Relations, Tangent Kernels and Recursive Error](https://github.com/the-omega-institute/trureturing/blob/31fa401a7c17858fa323ddd0886ed580e0c57347/docs/develop/theory/AURIC_GATE_MANIFOLDS_INTEGRABLE_RELATIONS_TANGENT_KERNELS_AND_RECURSIVE_ERROR_V78.md)。
§12 完整核、共同根、锚点光滑及同根读出。
<a id="ref-atlas"></a>

**[8]**
[Quantum Origin：Endogenous Cut Atlas and Discrete Reconstruction Boundaries](https://github.com/the-omega-institute/trureturing/blob/31fa401a7c17858fa323ddd0886ed580e0c57347/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md)。
§5 初等切分选型；§26 定理 26.2 的无预设内积入口；§29 定理 29.2 的模型排除及明确前件；§30 统计相干与组合路径。
<a id="ref-principles"></a>

**[9]**
[AURIC FIB Atom：Quantum Principles and Coherent Reconstruction](https://github.com/the-omega-institute/trureturing/blob/31fa401a7c17858fa323ddd0886ed580e0c57347/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md)。
§6、§17 核到仪器、唯一下降与相干记录提升的区分。
<a id="ref-jvn"></a>

**[10]**
P. Jordan and J. von Neumann,
*On Inner Products in Linear, Metric Spaces*,
Annals of Mathematics 36(3), 719--723 (1935).
[DOI: 10.2307/1968653](https://doi.org/10.2307/1968653)；
[原文扫描公开副本](https://www.mathematik.uni-muenchen.de/~michel/jordan-von_neumann_-_parallelogram_identity.pdf)。
本次核读定理 I 及证明。本文重编码到事件效果的论证给出自足推导。
<a id="ref-watrous"></a>

**[11]**
J. Watrous, *The Theory of Quantum Information* (2018)，
[作者公开稿第 2 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)，
完全正映射、测量、等距记录表示与量子仪器相关部分。
本稿不复制该书文本；上述算子性质均给直接证明。

## 源稿前言与排版元数据

```tex
% !TEX program = xelatex
% Compile twice with XeLaTeX; optional fallback font in fonts/.
\documentclass[11pt,a4paper]{article}
\usepackage[margin=24mm,headheight=16pt]{geometry}
\IfFileExists{ctex.sty}{\usepackage[UTF8,fontset=auto]{ctex}}{
  \usepackage{fontspec}
  \IfFontExistsTF{Noto Serif CJK SC}{\setmainfont{Noto Serif CJK SC}[AutoFakeBold=1.7]}{\setmainfont{NotoSerifCJKsc-Regular.otf}[Path=fonts/,AutoFakeBold=1.7,AutoFakeSlant=.15]}
  \XeTeXlinebreaklocale "zh"
  \XeTeXlinebreakskip=0pt plus 1pt
}
\usepackage{amsmath,amssymb,amsthm,mathtools,mathrsfs}
\usepackage{xcolor,booktabs,array,tabularx,longtable}
\usepackage{fancyhdr,enumitem,hyperref,needspace}
\definecolor{ink}{HTML}{17384A}
\definecolor{accent}{HTML}{007D86}
\hypersetup{colorlinks=true,linkcolor=ink,urlcolor=accent,citecolor=ink,
pdftitle={AURIC v78 后续研究：已证结构的内生闭合与约束削减}}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small AURIC / v78 后续研究}
\fancyhead[R]{\small 同根证书、内部读出与递归闭合}
\fancyfoot[C]{\thepage}
\setlength{\parindent}{1.8em}
\setlength{\parskip}{4pt}
\setlength{\emergencystretch}{3em}
\setlist{nosep,leftmargin=2em}
\renewcommand{\baselinestretch}{1.10}
\renewcommand{\contentsname}{目录}
\renewcommand{\abstractname}{摘要}
\renewcommand{\refname}{资料与可复核位置}
\renewcommand{\proofname}{证明}
\numberwithin{equation}{section}
\theoremstyle{definition}
\newtheorem{definition}{定义}[section]
\newtheorem{theorem}[definition]{定理}
\newtheorem{lemma}[definition]{引理}
\newtheorem{proposition}[definition]{命题}
\newtheorem{corollary}[definition]{推论}
\newtheorem{remark}[definition]{说明}
\newcommand{\ip}[2]{\langle #1,#2\rangle}
\newcommand{\norm}[1]{\left\lVert #1\right\rVert}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\Z}{\mathbb Z}
\newcommand{\tr}{\operatorname{Tr}}
\newcommand{\Span}{\operatorname{span}}
\newcommand{\ran}{\operatorname{ran}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\plain}[1]{\par\noindent\textbf{白话图景。}#1\par}
\newcommand{\repo}[2]{\href{https://github.com/the-omega-institute/trureturing/blob/31fa401a7c17858fa323ddd0886ed580e0c57347/#1}{#2}}
\title{\color{ink}\bfseries 已证结构的内生闭合\protect\\[5pt]
\large 同根有限证书、事件重编码与结果核递归\protect\\[5pt]
AURIC v78 后续研究：定义、定理与证明}
\author{研究续稿}
\date{2026 年 11 月 2 日}
```

```tex
\begin{document}
\maketitle
\setcounter{tocdepth}{1}
{\small\setlength{\parskip}{0pt}\tableofcontents}
\newpage
\begin{center}\small
\end{center}
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.21\textwidth}XX@{}}
\toprule
\midrule
\bottomrule
\end{tabularx}
\end{center}
\Needspace{10\baselineskip}
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.24\textwidth}XX@{}}
\toprule
\midrule
\bottomrule
\end{tabularx}
\end{center}
\clearpage
\begin{thebibliography}{99}
\end{thebibliography}
\end{document}
```
