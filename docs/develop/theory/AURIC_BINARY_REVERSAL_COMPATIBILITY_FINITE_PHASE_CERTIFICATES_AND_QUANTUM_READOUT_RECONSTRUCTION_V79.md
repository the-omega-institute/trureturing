# 二元反向相容公理

从相干反向与有限相位证书推出量子读出

AURIC v79：一个完整候选及其边界

项目连续研究稿

2026 年 11 月 2 日

## 摘要

本轮推进一个完整候选：对同一内部事件，两段历史的交叉余量，在其中一段相干反向时必须反号。
继承 v78 已建立的共同实正内积、复方向与总强度标尺，本文从这条纯二元条件证明：
非负性自动给出整体反向不变；范数支配与极化自动给出有界实二次形式；
随后只需 $d(d+1)$ 个固定相位差锚，即可认证与共同 $J$ 相容，得到唯一复效果与 Born 读出。

与 V49 直接要求交叉关系实双线性相比，本轮把这项前件降为二元反向条件。
与 v78 完整平衡重编码条件相比，本轮是严格证明的等价重组，未声称整体逻辑更弱。
全相干三阶余项为零、任意有限历史的二元展开及高阶差分消失均成为结论。
有限相位证书在声明的固定单标量探针类中达到所证下界，并有
$(2d-1)\varepsilon$ 的算符修复界。

事件二元关系的归一表示落在三维球中，强度尺度另行保留；
完整菜单给出这些球内向量的加权守恒，较大结构为共同核的序区间 $[0,K]$。
本文还给出两极与赤道的非 Born 反例、原始两两正而整体不正的失败见证，
以及小相干缺陷不保证跨全部强度尺度一致逼近的解析反例。
所有推导均为纸面证明；文献检索、排版与图形渲染不承担数学验证。

## 目录

- [1. 本轮只推进一个候选](#section-1)
- [2. 原始接口与二元交叉关系](#section-2)
- [3. 从二元反向相容推出实二次形式](#section-3)
- [4. 有限相位证书：从实效果到共同复效果](#section-4)
- [5. 一个完整的 v79 候选与表示定理](#section-5)
- [6. 从关系的关系推出任意多历史的闭合](#section-6)
- [7. 二元三维提升及完整菜单的球内守恒](#section-7)
- [8. 圆与周期在本候选中的更精确位置](#section-8)
- [9. 反着推：删去条件以后，哪两个元发生冲突？](#section-9)
- [10. 有限相位校准有明确的稳定修复界](#section-10)
- [11. 近似反向相容的跨尺度障碍](#section-11)
- [12. 接回既有理论：从事件关系到实际后继](#section-12)
- [13. 把“公理内生”锁成可检验的定义间约束](#section-13)
- [14. 版本、核查范围与证明归属](#section-14)

<a id="section-1"></a>

## 1. 本轮只推进一个候选

本轮版本递增为 v79。候选的核心句是：

> **对同一个内部事件，两段可合成历史之间的交叉余量，
> 在其中一段作相干反向时必须反号。**

“反向”指同一相干表达空间中的 $v\mapsto-v$，不是倒放时间，
也不是把事件结果由“是”改成“否”。
在已取得共同 $J$ 的空间中，它与 $J^2v=-v$ 相容；
但反向一条干涉支路与共同转动整个输入，仍是两种不同操作。

上轮已经在各自明确的前件下，接通共同复结构、效果、同根概率、实际后继、
声明的张量复合，以及光滑保核历史的连续动力学表示。
本轮聚焦其中“读出为何必须成为二次形式”这一接口，
把原来常写成平衡重编码的条件，改写成直接作用于两段历史的内部关系。
所得结果继续接回已有仪器与复合理论，不把那些完成的部分重新列为未解决问题。

### 1.1 继承内容与本轮增量

| 来源或层次 | 本轮处理方式 |
| --- | --- |
| 共同 $g,J$ 与强度标尺 | 继承已证供应；不从“全在 $\Omega$”单独重造 |
| V49/V76 双线性闭合 | 已有“非负＋交叉实双线性 $\Rightarrow$ 二次型”；本轮削减其中双线性前件 |
| v78 平衡重编码 | 本轮证明二元反向条件与它在完整接口下等价 |
| 全相干 $I_3=0$ | 原综合稿已有正向推论；本轮给反向刻画及更小的反向对消族 |
| 有限共同相位 | 构造 $d(d+1)$ 个锚的充分证书、限定的数量下界及稳定修复界 |
| 三维有限提升 | 保留每个事件的尺度，证明完整菜单的加权球内守恒 |
| 近似边界 | 区分有限相位校准的稳定性与全强度尺度二次逼近的障碍 |

V49 已明确指出，“能写成二元函数”不等于“双线性”[1](#ref-v49)。
这条区别本轮继续保留。我们的推进是给出足以推出双线性的具体二元恒等式，
而非用“二元”一词代替证明。
原公开 v78 综合稿的 $I_3=0$ 命题是从效果形式正向展开[4](#ref-synthesis)；
本稿补足相应逆向链。

**白话图景。**本轮只问一件事：两段历史合在一起多出来的那份关系，怎样才算同一份关系？
把一段转成相反的相干方向后，加强应转成抵消，抵消应转成加强。
若这项要求在所有合法合成历史上相容，概率的二次形式便可以被推出来。

<a id="section-2"></a>

## 2. 原始接口与二元交叉关系

<a id="statement-2-1"></a>

#### 定义 2.1（继承的有限相干截口）

令 $(V,g)$ 为实维数 $2d$ 的正内积空间，$d\ge1$。
实际共同参考已经给出正交复结构

$$
J^2=-I,\qquad J^*=-J.
$$

以 $(a+ib)x=ax+bJx$ 定义复标量，并令

$$
\langle x,y\rangle =g(x,y)+i\,g(Jx,y).
$$

内积对第二变量线性。记 $N(x)=g(x,x)=\left\lVert x\right\rVert ^2$。
$V$ 是所声明有限相干表达的空间；负号、实缩放与合成均具有已经指定的内部含义。

这项表示可由上一轮的实历史核商及实际参考有限根证书取得[3](#ref-closure)。
整个 $\Omega$ 不必有限维；这里是一个具体有限截口。
共同正性、相干表达的供应、同根强度校准仍是明确继承的前件。

<a id="statement-2-2"></a>

#### 定义 2.2（同一事件的权重）

有限结果菜单 $\mathcal E$ 对每个 $e\in\mathcal E$ 给同一个函数
$w_e:V\to[0,\infty)$，并满足

<a id="eq-menu"></a>

$$
\sum_{e\in\mathcal E}w_e(x)=N(x).\tag{2.1}
$$

因此 $w_e(0)=0$ 且 $0\le w_e(x)\le N(x)$。
结果标签、读出装置及归一化口径在比较中保持同一。
本轮不先要求 $w_e$ 连续、偶、齐次或为二次型。

<a id="statement-2-3"></a>

#### 定义 2.3（二元交叉余量与反向缺陷）

对同一事件，定义

<a id="eq-C"></a>

$$
C_e(u,v)=w_e(u+v)-w_e(u)-w_e(v).\tag{2.2}
$$

它是合并后超出两项分别权重之和的带符号交叉余量。
本稿的 $C_e$ 不含 V49 定义中的 $1/2$，以便直接对应实际权重差。
定义二元反向缺陷

<a id="eq-Delta"></a>

$$
\Delta_e(u,v)=C_e(u,v)+C_e(u,-v).\tag{2.3}
$$

每次比较只有两个输入对象；$u,v$ 本身可以是许多原始历史的相干合成。
这正是从原始标签的两两检验推进到全部合成二元检验的地方。

<a id="statement-2-4"></a>

#### 定义 2.4（二元反向相容）

一个事件称为二元反向相容，当且仅当

<a id="eq-reversal"></a>

$$
\boxed{C_e(u,-v)=-C_e(u,v)\qquad(u,v\in V).}\tag{2.4}
$$

等价地，$\Delta_e(u,v)=0$。

这个定义有可识别的后果：它要求“把同一条支路作相干反向”只反转该支路的交叉贡献。
若不成立，原先赋给两段历史的交叉比较就不能作为对该反向操作相容的关系来接续。

**白话图景。**先分别读两段历史，再把它们合起来，差出来的部分就是它们的关系。
现在只把第二段的相干方向反过来。
候选要求这份关系也随之反过来；它不预先规定每个结果的概率公式。

<a id="section-3"></a>

## 3. 从二元反向相容推出实二次形式

<a id="statement-3-1"></a>

#### 引理 3.1（非负性自动消去整体反向差）

设 $w:V\to[0,\infty)$、$w(0)=0$，并满足[(2.4)](#eq-reversal)。
则 $w(-v)=w(v)$ 对全部 $v$ 成立。
此结论不需要范数上界、连续性或相位不变。

**证明。**

在反向条件中取 $u=v$，展开得

$$
w(2v)=3w(v)+w(-v).
$$

再将 $v$ 换成 $-v$。令

$$
s(v)=w(v)+w(-v),\qquad a(v)=w(v)-w(-v),
$$

则

$$
s(2v)=4s(v),\qquad a(2v)=2a(v).
$$

在 $v/2^n$ 上使用非负性 $|a(v/2^n)|\le s(v/2^n)$，得到

$$
|a(v)|\le 2^{-n}s(v)
$$

对所有 $n$ 成立。令 $n\to\infty$，有 $a(v)=0$。

□

<a id="statement-3-2"></a>

#### 引理 3.2（反向条件产生平行四边形关系）

在引理[3.1](#statement-3-1)的条件下，

<a id="eq-parallel"></a>

$$
w(u+v)+w(u-v)=2w(u)+2w(v).\tag{3.1}
$$

特别地，$w(2u)=4w(u)$。

**证明。**

直接展开 $\Delta(u,v)=0$，右侧原为 $2w(u)+w(v)+w(-v)$，
再使用已证偶性。取 $v=u$ 得后一式。

□

<a id="statement-3-3"></a>

#### 定理 3.3（受共同标尺支配的实效果表示）

若 $0\le w(x)\le N(x)$ 且满足二元反向相容，则存在唯一实自伴算符 $A$，

$$
0\le A\le I,\qquad w(x)=g(x,Ax).
$$

交叉余量为

<a id="eq-bilinear"></a>

$$
C(u,v)=2g(u,Av).\tag{3.2}
$$

因此，偶性、实二次齐次性、连续性以及 $C$ 的实双线性全部是结论。

**证明。**

定义极化

$$
b(u,v)=\frac14\{w(u+v)-w(u-v)\}.
$$

偶性使它对称，并对任一变量为奇函数。
把平行四边形式用于 $(u+z,v)$、$(u-z,v)$ 后相减，可得

$$
b(u+v,z)+b(u-v,z)=2b(u,z).
$$

取 $v=u$ 得 $b(2u,z)=2b(u,z)$；再令
$u=(a+c)/2,v=(a-c)/2$，得到 $b(a+c,z)=b(a,z)+b(c,z)$。
因此 $b$ 对两变量可加。

范数支配给

$$
|b(u,z)|
\le\frac{\left\lVert u+z\right\rVert ^2+\left\lVert u-z\right\rVert ^2}{4}
=\frac{\left\lVert u\right\rVert ^2+\left\lVert z\right\rVert ^2}{2}.
$$

固定 $z$，这个加性函数在单位球有界，故在零处连续：
若界为 $M$，取整数 $n>M/\varepsilon$，则 $\left\lVert u\right\rVert <1/n$ 时
$|b(u,z)|=|b(nu,z)|/n<\varepsilon$。
加性与连续性给实线性，对称性给实双线性。

又 $b(u,u)=w(u)\ge0$，对所有实 $t$ 的 $b(u+tv,u+tv)\ge0$ 给

$$
|b(u,v)|^2\le w(u)w(v)\le\left\lVert u\right\rVert ^2\left\lVert v\right\rVert ^2.
$$

实 Riesz 表示于是给唯一自伴 $A$，$b(u,v)=g(u,Av)$，
而对角界给 $0\le A\le I$。
最后展开 $w(u+v)$ 得[(3.2)](#eq-bilinear)。

□

<a id="statement-3-4"></a>

#### 推论 3.4（完整菜单保持同一标尺）

若每个事件都满足上述条件，则 $\sum_e A_e=I$。

**证明。**

由[(2.1)](#eq-menu)得 $g(x,(\sum_eA_e-I)x)=0$ 对全部 $x$ 成立，
实极化使该自伴算符为零。

□

V49 已有“非负＋交叉实双线性 $\Rightarrow$ 二次形式”[1](#ref-v49)、[2](#ref-v76)。
这里的增量在其前面：*二元反向相容＋共同支配界*自动供应所需双线性。
在现有标尺下，这条路线与 v78 的平衡重编码路线相接，而非重新认领极化定理。

**白话图景。**反向差若还偷偷留下一个单边偏置，把同一输入不断缩小以后，
它会压过应有的非负权重。非负性因此先把偏置消掉。
随后正反两次合并的关系必须对称，极化便把全部读出锁成一个正二次形式。

<a id="section-4"></a>

## 4. 有限相位证书：从实效果到共同复效果

只有实二次形式还不够：实效果可能把共同复方向当成额外可区分轴。
本轮用有限内部锚来认证读出对共同 $J$ 的相容。

选择实际可用的实正交基

$$
e_1,\ldots,e_d,\quad f_1=Je_1,\ldots,f_d=Je_d.
$$

所有锚均取单位长度。定义

<a id="eq-probes"></a>

$$
\begin{split}
\mathcal S_J={}&\{e_i:1\le i\le d\}\\
&{}\cup\{(e_i+e_j)/\sqrt2: i<j\}\\
&{}\cup\{(e_i+f_j)/\sqrt2:i\le j\}.
\end{split}\tag{4.1}
$$

它有 $d+d(d-1)/2+d(d+1)/2=d(d+1)$ 个锚。

<a id="statement-4-1"></a>

#### 定义 4.1（有限共同相位校准）

对每个事件只要求

<a id="eq-phase"></a>

$$
w_e(v)=w_e(Jv)\qquad(v\in\mathcal S_J).\tag{4.2}
$$

这里 $J$ 共同作用于整个输入表达，不是仅转动一条相对干涉支路。
这些锚与参考操作均须属于声明的内部接口。

<a id="statement-4-2"></a>

#### 定理 4.2（有限锚认证共同复方向）

在定理[3.3](#statement-3-3)已得实效果 $A$ 后，
有限校准[(4.2)](#eq-phase)当且仅当 $AJ=JA$。
因此 $A$ 是唯一复效果 $E$，且

$$
w(x)=\langle x,Ex\rangle ,\qquad 0\le E\le I.
$$

全部 $x$ 的 $w(Jx)=w(x)$ 及全部共同相位不变随之成立。

**证明。**

按 $(e_1,\ldots,e_d,f_1,\ldots,f_d)$ 分块写

$$
A=\begin{pmatrix}P&B\\B^{\mathsf T}&Q\end{pmatrix},
\qquad
J=\begin{pmatrix}0&-I\\I&0\end{pmatrix},
$$

其中 $P,Q$ 实对称。$AJ=JA$ 等价于

$$
P=Q,\qquad B=-B^{\mathsf T}.
$$

$e_i$ 锚先给 $P_{ii}=Q_{ii}$。
实和桥 $(e_i+e_j)/\sqrt2$ 再给 $P_{ij}=Q_{ij}$。
混合桥 $(e_i+f_j)/\sqrt2$ 的 $J$ 像为 $(f_i-e_j)/\sqrt2$，
利用已经相等的对角项，校准等式给 $B_{ij}+B_{ji}=0$，包括 $i=j$。
所以所需两项全部成立。

反向，对易立即给全域 $w(Jx)=w(x)$。
实自伴且与 $J$ 对易，使 $A$ 对共同复内积复线性、自伴且为正收缩。
$g(Jx,Ax)=0$，故 $\langle x,Ax\rangle =g(x,Ax)=w(x)$。

□

<a id="statement-4-3"></a>

#### 定理 4.3（固定单标量相位差探针的数量下界）

考虑如下限定认证任务：事先选定若干 $v_j$，
只利用标量等式 $w(v_j)-w(Jv_j)=0$，
要求对全部实效果 $0\le A\le I$ 保证 $AJ=JA$。
任何这样的通用证书至少需要 $d(d+1)$ 个标量等式。

**证明。**

令 $\tau(A)=J^*AJ$。实对称算符空间中，$\tau$ 的反不变子空间由

$$
D=\begin{pmatrix}S&T\\T&-S\end{pmatrix},
\qquad S=S^{\mathsf T},\quad T=T^{\mathsf T}
$$

组成，其实维数为 $d(d+1)$。
每个相位差探针在该空间上只是一个实线性泛函。
若等式数量不足，存在非零反不变 $D$ 通过全部检验。
取足够小 $t>0$，令
$A=\tfrac12I+tD$，则 $0\le A\le I$，
全部被选探针仍通过，但 $\tau(A)\ne A$。
以 $I-A$ 作补事件，反例也能组成完整二结果菜单。

□

最小性只针对上述固定单标量探针任务，不扩张到任意其他测量、额外先验或资源协议。
它与 V77 在*已经复线性*的前提下认证等距的 $d^2$ 探针任务不同[5](#ref-v77)。
若每个锚一次读取完整菜单，最后一个事件的校准由其他事件与总权守恒自动得到。

**白话图景。**先认出读出是一张实二次关系表，再问它会不会把大家共用的相位尺当成额外方向。
有限锚分别检查两组对应轴，以及连接这些轴的相干桥。
这些比较全部一致，整张表就只能按共同复方向读数；不必再把每个输入逐一校准。

<a id="section-5"></a>

## 5. 一个完整的 v79 候选与表示定理

<a id="statement-5-1"></a>

#### 定义 5.1（v79 候选：二元反向相容的完整读出）

在第 2 节继承的 $(V,g,J)$、同一事件身份和总强度标尺上，声明：

1. 各事件非负，完整菜单满足 $\sum_e w_e=N$；

2. 每个事件的交叉余量满足 $C_e(u,-v)=-C_e(u,v)$，对全部声明的 $u,v$ 成立；

3. 每个事件在有限锚族 $\mathcal S_J$ 上满足 $w_e(v)=w_e(Jv)$。

这是一组完整候选条件；其中真正替换 v78 平衡重编码前件的是第 2 项，
第 3 项把读出对共同 $J$ 的相容缩成有限证书。

<a id="statement-5-2"></a>

#### 定理 5.2（v79 量子读出表示）

上述候选当且仅当存在唯一一族复效果

<a id="eq-born"></a>

$$
\boxed{
0\le E_e\le I,\qquad \sum_eE_e=I,\qquad
w_e(x)=\langle x,E_ex\rangle .
}\tag{5.1}
$$

因此对非零输入

$$
p_e(x)=\frac{\langle x,E_ex\rangle }{\left\lVert x\right\rVert ^2},
$$

这给出数学上的归一 Born 形式；在继承的同根校准与声明准备范围内，
它就是该输入的实际读出概率。

**证明。**

定理[3.3](#statement-3-3)逐事件给实效果，菜单守恒给其和为 $I$。
定理[4.2](#statement-4-2)使每个效果与 $J$ 对易，得到[(5.1)](#eq-born)。
极化与历史张成保证唯一性。
反向，复效果的二次式非负、完备，并且
$C_e(u,v)=2\operatorname{Re}\langle u,E_ev\rangle$，所以相干反向使它反号；
效果复线性使所有共同相位不变，当然通过有限锚。

□

概率来源仍继承上一轮的同根读出合同：同一个 $p_0$ 定义在全部效果上，
非负、满足 $p_0(I)=1$，并对 $E,F\ge0$、$E+F\le I$ 的合法效果和可加。
单位根满足 $p_0(P_{\Omega_0})=1$，声明准备运输满足
$p_h(E)=p_0(U_h^*EU_h)$。
项目的同根定理因而给出
$p_h(E)=\langle U_h\Omega_0,EU_h\Omega_0\rangle$[3](#ref-closure)。
当 $x/\left\lVert x\right\rVert =U_h\Omega_0$ 是声明的准备历史时，上式就是相应 Born 读出。
平方总强度、共同 $J$、合法效果读出的同一性及实际准备供应继续继承原合同。

<a id="statement-5-3"></a>

#### 定理 5.3（几种内部表述的精确等价）

固定 $0\le w\le N$，以下条件等价：

1. 二元反向相容；

2. 平行四边形关系；

3. 交叉余量对合成槽可加：

   $C(u+v,z)=C(u,z)+C(v,z)$；
4. 全相干表达的三阶差分 $I_3(u,v,z)=0$；

5. $w(x)=g(x,Ax)$，其中 $0\le A\le I$；

6. v78 的平衡重编码关系

   $$
   w(u)+w(v)=w((u+v)/\sqrt2)+w((u-v)/\sqrt2).
   $$

加上共同 $J$ 相容的全域条件或本稿有限证书，得到同一个复效果类。

**证明。**

前述定理给 $1\Rightarrow2\Rightarrow5$；实二次展开给 $5\Rightarrow1,3,6$。
定义

$$
\begin{split}
I_3(u,v,z)={}&w(u+v+z)-w(u+v)-w(u+z)-w(v+z)\\
&+w(u)+w(v)+w(z)-w(0).
\end{split}
$$

由于 $w(0)=0$，直接展开得

$$
I_3(u,v,z)=C(u+v,z)-C(u,z)-C(v,z),
$$

所以 $3\Leftrightarrow4$。
槽加性在 $v+(-v)=0$ 上给反向相容。
若有第 6 项，取 $v=0$ 得 $w(u/\sqrt2)=w(u)/2$，
代回即得平行四边形式。第 2 项在 $u=0$ 给偶性，
所以展开后也直接给第 1 项。

□

这里比较的是同一声明接口上权重约束的等价；实际平衡门的供应，
以及同一粗事件忽略路径标签的约定，仍按 v78 保留。

<a id="statement-5-4"></a>

#### 推论 5.4（只需反向对消族）

在相同前件下，不必先要求全部三元组的 $I_3=0$。
仅要求

$$
I_3(u,v,-v)=0\quad\text{对全部 }u,v
$$

已经足够，因为

$$
I_3(u,v,-v)=-\Delta(u,v).
$$

因此候选确实能够写成二元条件。它所涉及的相干表达仍须允许有符号合成与缩放；
这项量词不能缩成有限张普通概率表。

**白话图景。**本轮把同一件事找到了几种等价说法：
反向一条历史，关系反号；合并历史，关系按组成部分相加；
三路合并不再额外产生独立余项；最后读出必为正二次形式。
简化发生在定义的表达和校准接口上，不是把应保留的物理前件悄悄删掉。

<a id="section-6"></a>

## 6. 从关系的关系推出任意多历史的闭合

<a id="statement-6-1"></a>

#### 定理 6.1（全部有限历史只需单项与二元项）

在 v79 条件下，对同一事件及任意有限输入族 $x_1,\ldots,x_n$，

<a id="eq-finite"></a>

$$
\boxed{
w\!\left(\sum_{j=1}^n x_j\right)
=
\sum_{j=1}^n w(x_j)+\sum_{j<k}C(x_j,x_k).
}\tag{6.1}
$$

右侧与合成二元树的括号选择无关。

**证明。**

由实二次表示，$C$ 对两变量实双线性。
$n=2$ 是定义。若已对 $n$ 成立，再加 $x_{n+1}$，新增交叉项为

$$
C\!\left(\sum_{j=1}^n x_j,x_{n+1}\right)
=\sum_{j=1}^n C(x_j,x_{n+1}),
$$

所以归纳得结论。该展开只依赖同一最终输入族，故不依赖括号。

□

<a id="statement-6-2"></a>

#### 推论 6.2（全部高阶相干差分消失）

定义

$$
I_n(x_1,\ldots,x_n)
=
\sum_{S\subseteq\{1,\ldots,n\}}
(-1)^{n-|S|}w\!\left(\sum_{j\in S}x_j\right).
$$

则对 $n\ge3$，$I_n=0$。

**证明。**

将[(6.1)](#eq-finite)代入。每个单项的交错系数为 $(1-1)^{n-1}=0$；
每个二元项的系数为 $(1-1)^{n-2}=0$。
这是符号恒等式，不使用数值枚举。

□

这与 Sorkin 的干涉层级相联系，但输入合同不同：
其集合层级先使用互斥历史集合的并；本稿在已供应的线性相干域上，
要求同一函数对全部有符号、可缩放、可重复的表达成立[12](#ref-sorkin)。
“没有三阶历史振幅余项”也不限制复合系统只能有两方；
三方及更多方纠缠完全可以存在。

**白话图景。**一个合成对象再和别的对象比较时，它带来的关系就是各组成部分带来关系之和。
于是无论先把哪两段接起来，最终都能合成同一张完整关系表。
任意多条历史可以有复杂整体效果，但在这个读出接口中，不需要再添加独立的三元幅度规则。

<a id="section-7"></a>

## 7. 二元三维提升及完整菜单的球内守恒

定义已经重建的完整事件核

<a id="eq-eventkernel"></a>

$$
k_e(u,v)=\langle u,E_ev\rangle
=\frac12\{C_e(u,v)+iC_e(Ju,v)\}.\tag{7.1}
$$

其中第一项是同向交叉读数，第二项是参考四分之一转后的交叉读数。
这项复合并未引入新外部参照，使用的正是同一个内部 $J$。

<a id="statement-7-1"></a>

#### 定理 7.1（事件二元关系的带尺度三维表示）

对两个输入 $u,v$，令

$$
a_e=w_e(u),\quad b_e=w_e(v),\quad z_e=k_e(u,v),\quad s_e=a_e+b_e.
$$

若 $s_e>0$，定义

$$
R_e=\frac1{s_e}
\begin{pmatrix}a_e&\overline{z_e}\\z_e&b_e\end{pmatrix}
=\frac12(I+\mathbf r_e\cdot\boldsymbol\sigma).
$$

则

$$
\mathbf r_e=
\left(\frac{2\operatorname{Re}z_e}{s_e},
\frac{2\operatorname{Im}z_e}{s_e},
\frac{a_e-b_e}{s_e}\right),
$$

且

<a id="eq-ball"></a>

$$
\boxed{1-\left\lVert \mathbf r_e\right\rVert ^2
=\frac{4(a_eb_e-|z_e|^2)}{s_e^2}\ge0.}\tag{7.2}
$$

完整二元事件数据为 $(s_e,\mathbf r_e)$。若 $s_e=0$，整个事件二元核为零，不赋予球方向。

**证明。**

以 $E_e^{1/2}u,E_e^{1/2}v$ 的 Cauchy--Schwarz 不等式得
$|z_e|^2\le a_eb_e$。上式矩阵为 Gram 矩阵的转置，仍为正，
迹为一。直接展开三个坐标给[(7.2)](#eq-ball)。
若 $s_e=0$，两项非负使 $a_e=b_e=0$，交叉项亦为零。

□

<a id="statement-7-2"></a>

#### 定理 7.2（父关系是事件关系的加权合成）

设 $s=N(u)+N(v)>0$，$R_K,\mathbf r_K$ 为父核 $K(u,v)=\langle u,v\rangle$ 的同类归一表示。
令 $\tau_e=s_e/s$，忽略 $s_e=0$ 的零项。则

<a id="eq-barycenter"></a>

$$
\boxed{
\sum_e\tau_e=1,\qquad
R_K=\sum_e\tau_eR_e,\qquad
\mathbf r_K=\sum_e\tau_e\mathbf r_e.
}\tag{7.3}
$$

**证明。**

效果完备性给 $\sum_e k_e(u,v)=K(u,v)$，对角同样相加。
因此未归一的二元矩阵逐项相加为父矩阵。
除以共同 $s$ 即得矩阵式；Pauli 坐标线性，给向量式。

□

这指出候选所属的较大结构：

<a id="eq-kernelinterval"></a>

$$
\boxed{0\le k_e\le K,\qquad\sum_e k_e=K.}\tag{7.4}
$$

核序指全部有限相干系数上的正性，不是逐元素大小。
在最小历史表示中，$[0,K]$ 与效果区间 $[0,I]$ 的序同构已由项目建立[3](#ref-closure)。
本轮给出该结构在每个二元三维截面上的加权守恒解释。
各个球必须共享同一历史身份、同一合成规则和同一核；不能各自随意拼造。

**白话图景。**一个三维球内点记录两条历史怎样相合，但还要记住这份关系有多大。
完整结果把同一关系分成若干份，各份的球内点按其强度加权，又回到原来的父关系点。
所以多个局部球并不是散开的图画，它们是同一张整体关系表的相容截面。

<a id="section-8"></a>

## 8. 圆与周期在本候选中的更精确位置

<a id="statement-8-1"></a>

#### 命题 8.1（相对相位的圆周读出）

在 v79 条件下，对固定 $u,v$，令 $v_\theta=e^{i\theta}v$。
若相应输入族属于声明域，则

$$
k_e(u,v_\theta)=e^{i\theta}k_e(u,v),\qquad
w_e(v_\theta)=w_e(v).
$$

在 $s_e>0$ 时，事件关系的 $(X_e,Y_e)$ 绕圆转动，$Z_e$ 与 $s_e$ 保持不变。
若 $s_e=0$，整个事件二元核始终为零，不使用归一坐标。
同一幅度标尺上的事件权重为

<a id="eq-phasecircle"></a>

$$
w_e(u+e^{i\theta}v)
=w_e(u)+w_e(v)
+2\operatorname{Re}(e^{i\theta}k_e(u,v)).\tag{8.1}
$$

**证明。**

这是事件核的复半双线性及对角式的直接展开。
实部与虚部按
$(X,Y)\mapsto(X\cos\theta-Y\sin\theta,X\sin\theta+Y\cos\theta)$ 旋转。

□

于是半周 $\theta\mapsto\theta+\pi$ 反转交叉余量，全周返回。
候选从半周反向相容出发，结合全部合成输入的约束，推出完整余弦、正弦读出。
只观察某一条相位曲线有半周反号仍然不够，因为 $\sin3\theta$ 也有此性质；
本定理使用的是对*全部可合成输入*的一致条件。

式[(8.1)](#eq-phasecircle)首先是未归一权重恒等式，允许半径为零的退化圆。
若每个 $\theta$ 都另行把 $u+e^{i\theta}v$ 归一化，令

$$
d(\theta)=\left\lVert u+e^{i\theta}v\right\rVert ^2
=s+2\operatorname{Re}(e^{i\theta}K(u,v)),\qquad s=N(u)+N(v).
$$

它满足 $s-2|K(u,v)|\le d(\theta)\le s+2|K(u,v)|$。
概率只在 $d(\theta)>0$ 时定义，且为

$$
p_e(\theta)=\frac{a_e+b_e+2\operatorname{Re}(e^{i\theta}z_e)}{d(\theta)}.
$$

分母固定时，例如 $u\perp v$，直接得到一阶正弦型概率曲线。
分母变化时一般是两个一阶谐波的比值，特殊情况下也可因分子分母成比例而成为常数。
若 $d(\theta)=0$，所有事件权重均为零，此处条件概率未定义。
分母改变造成的比值非线性不等于出现新的高阶幅度关系。

实际时间周期仍需内部钟的推进规律。有限圆形相位读口不自动保证完整历史返回，
也不自动供应任意连续相位控制。
v78 已完成的历史切向圆、椭圆投影及返回群定理继续保持其原有前件[6](#ref-arcs)、[7](#ref-periods)。

**白话图景。**现在圆不只是一个比喻。
二元关系有两项正交交叉读数，改变相对相位时它们沿圆旋转；
半圈把加强换成抵消，一圈回到原来的比较。
是否用同样的时间完成一圈，还要看内部时钟；是否整个档案都回到原来，还要看记录是否增长。

<a id="section-9"></a>

## 9. 反着推：删去条件以后，哪两个元发生冲突？

### 9.1 正、连续、完备与共同相位不变仍不够

在 $\mathbb C ^2$ 上写 $z=(z_1,z_2)$、$s=|z_1|^2+|z_2|^2$，并定义

<a id="eq-nonborn"></a>

$$
w_0(z)=\frac{(|z_1|^2-|z_2|^2)^2}{s},\qquad
w_1(z)=s-w_0(z)\quad(s>0),\tag{9.1}
$$

在零点两项都定义为零。
它们非负、和为 $s$、连续、对复缩放二次齐次，并且共同相位不变。
因为 $0\le(|z_1|^2-|z_2|^2)^2\le s^2$，这些性质直接成立。

取 $u=(1,0),v=(0,1)$。有

$$
w_0(u)=w_0(v)=w_0(-v)=1,\qquad
w_0(u+v)=w_0(u-v)=0.
$$

因此

<a id="eq-nonbornfailure"></a>

$$
C_0(u,v)=C_0(u,-v)=-2,\qquad
\Delta_0(u,v)=-4,\qquad I_3(u,v,-v)=4.\tag{9.2}
$$

把第二段反向以后，交叉余量依然抵消，没有改成加强。
冲突已经定位在二元组 $(u,v)$ 上，而不是某个遥远的整体条件。

归一纯态的 Bloch 高度是 $Z=(|z_1|^2-|z_2|^2)/s$，该规则给 $p_0=Z^2$。
两极概率都是 $1$，赤道概率却是 $0$。
若它来自某个效果 $0\le E\le I$，则
$\langle u,Eu\rangle =\langle v,Ev\rangle =1$ 使 $I-E$ 在一组正交基上均为零，因而 $E=I$。
这与赤道概率零矛盾。故它确实不是 Born 效果。

还可尝试把两种相位的交叉读数填进同一张 Hermitian 二元关系表。
因为 $w_0(Ju+v)=0$，有 $C_0(Ju,v)=-2$。
按照候选所需的重建式，表中交叉元将被迫取为 $z=-1-i$，而 $a=b=1$。
其三维坐标为

$$
\mathbf r=(-1,-1,0),\qquad \left\lVert \mathbf r\right\rVert ^2=2>1.
$$

这是*失败规则被强行放进同一正核表示后的不一致表*，不是一个合法量子态。
它显示同一个事件的两项交叉读数无法同时装进正二元关系。
这里给出具体失败见证；并不声称任意非二次函数都必以这一对输入产生同一种越球现象。

<a id="figure-1"></a>

**图 1。**

```latex
\begin{figure}[htbp]
\centering
\begin{tikzpicture}[>=Latex,font=\small]
\begin{scope}[xshift=-3.5cm]
\draw[ink,thick] (0,0) circle (1.35);
\draw[ink!40,dashed] (-1.35,0)--(1.35,0);
\draw[->,ink!65] (0,-1.7)--(0,1.8) node[above] {$Z$};
\fill[accent] (0,1.35) circle (2pt);
\fill[accent] (0,-1.35) circle (2pt);
\fill[warm] (1.35,0) circle (2pt);
\node[anchor=west,align=left] at (.18,1.38) {$p_0=1$};
\node[anchor=west,align=left] at (.18,-1.38) {$p_0=1$};
\node[anchor=north,align=center] at (1.38,-.15) {$p_0=0$};
\node[align=center,text width=4.8cm] at (0,-2.15) {输入纯态球的经线截面\\失败读出 $p_0=Z^2$};
\end{scope}
\begin{scope}[xshift=3.5cm]
\fill[accent!8] (0,0) circle (1.35);
\draw[ink,thick] (0,0) circle (1.35);
\draw[->,ink!65] (-1.8,0)--(1.8,0) node[right] {$X$};
\draw[->,ink!65] (0,-1.8)--(0,1.8) node[above] {$Y$};
\draw[->,warm,thick] (0,0)--(-1.35,-1.35);
\fill[warm] (-1.35,-1.35) circle (2.3pt);
\node[anchor=east,align=right,text=warm] at (-1.4,-1.28) {$(-1,-1)$};
\node[align=center,text width=5.3cm] at (0,-2.15) {事件二元关系的 $Z=0$ 截面\\失败表超出单位圆盘};
\end{scope}
\end{tikzpicture}
\caption{同一反例的两层表示。左侧是输入纯态球上的读出规则；右侧是尝试重建的事件关系表。
二者不是同一个球。右侧横纵轴以单位半径标度，所示失败表不属于量子效果。}
\end{figure}
```

**白话图景。**如果只要求概率非负、总和为一、变化平滑，还能造出这样的规则：
两种完全可区分的输入各自都必然触发事件，可它们的均匀相干合成却绝不触发。
把其中一条支路反向，仍然绝不触发。
真正坏掉的是同一对历史的加强与抵消无法相互转换；装入同一张关系表时便发生正性冲突。

### 9.2 删去共同相位校准，留下实效果而非共同复效果

在 $\mathbb C \cong\mathbb R ^2$ 上取

$$
w_0(z)=(\operatorname{Re}z)^2,\qquad
w_1(z)=(\operatorname{Im}z)^2.
$$

这是完整正实二次菜单，全部二元反向条件成立。
但 $w_0(1)=1$、$w_0(i)=0$，故不与共同 $J$ 相容。
复一维中的复效果只能为实数 $\lambda I$，不能产生此读出。
所以二元反向相容负责二次性，有限相位证书负责共同复方向；二者作用不同。

非负性和共同支配界也各有作用。
若去掉非负性，非零实线性函数本身有 $C=0$，却不是二次权重。
若只保留非负而去掉共同范数上界，可以取不连续的加性函数
$\ell:\mathbb R \to\mathbb R$，令 $w(x)=\ell(x)^2$。
它满足反向条件，但一般不为实二次型。
例如在一组含 $1,\sqrt2$ 的 Hamel 基上规定
$\ell(1)=0,\ell(\sqrt2)=1$，再作有理线性延拓即可。
完整菜单的 $w\le N$ 排除这类病态；本稿没有另添一个连续性公理。

**白话图景。**反向相容把读出锁成二次形式，共同相位校准再把它锁到大家共用的复方向。
总强度还提供统一的上界，使相干表达越接近，读出也越接近。
这三件事分别承担工作，不能拿“都在内部”一句话把其中任何一件省略。

### 9.3 原始两两合法与集合式三阶消失，不保证整体合法

考虑实对称关系表

<a id="eq-weakmatrix"></a>

$$
D=\begin{pmatrix}
1&3/4&3/4\\
3/4&1&-3/4\\
3/4&-3/4&1
\end{pmatrix},\qquad
\mu(A)=\frac29\sum_{i,j\in A}D_{ij},
\quad A\subseteq\{1,2,3\}.\tag{9.3}
$$

它给空集 $0$、各单元 $2/9$、三对分别 $7/9,7/9,1/9$、全集 $1$。
这些集合权重均处于 $[0,1]$，且互斥集合并上的三阶差分为零，
因为式[(9.3)](#eq-weakmatrix)关于指标函数是二次式。
每个原始 $2\times2$ 主块的特征值都是 $1\pm3/4>0$。

然而 $c=(-1,1,1)^{\mathsf T}$ 给

$$
c^{\mathsf T}Dc=-\frac32<0.
$$

所以这不是正核。
问题在合成二元组上直接显现：令 $u=e_2+e_3,v=e_1$，则相应未缩放二元数据为

$$
a=\frac12,\qquad b=1,\qquad z=\frac32.
$$

故三维归一给

$$
\mathbf r=(2,0,-1/3),\qquad \left\lVert \mathbf r\right\rVert ^2=\frac{37}{9}>1.
$$

共同乘以 $2/9$ 不改变该归一结果。
这张表只是一项*较弱集合合同*下的反例，不能当作满足本稿全相干非负菜单的模型。
它正好说明为何本稿的“二元”量词必须包括合成历史，不能只检验最初的两两标签。
项目此前已区分弱集合正性与强正核[1](#ref-v49)、[8](#ref-atlas)；本例把失败位置具体画成一个合成二元截面。

文献中的普通“没有高阶干涉”也不会单独选出复量子理论。
Barnum、Müller、Ududec 的重建在所述单系统条件下仍保留实、复、四元数及若干其他模型，
并使用额外的能量可观测性条件作进一步选择[13](#ref-barnum)。
本稿有限相位证书的前件是*已经实际取得共同 $J$*，不能拿该证书代替共同 $J$ 的起源证明。

**白话图景。**每两张原始卡片都能放进球里，不代表把卡片合成以后还放得进去。
把第二、第三条历史先连成一个对象，再与第一条比较，原先藏着的冲突就露出来。
因此三维提升是一种局部看清整体约束的方法；整体相容仍由共享的核和全部合成输入负责。

<a id="section-10"></a>

## 10. 有限相位校准有明确的稳定修复界

本节保持二元反向相容*精确成立*，所以已得到正实效果 $A$。
只让有限相位锚有测量误差。

<a id="statement-10-1"></a>

#### 定理 10.1（有限锚误差到共同复效果）

若 $0\le A\le I$ 且对所有 $v\in\mathcal S_J$ 有

$$
|w(v)-w(Jv)|\le\varepsilon,
$$

令

$$
\tau(A)=J^*AJ,\qquad E=\frac12(A+\tau(A)).
$$

则 $E$ 是与 $J$ 对易的正效果，且

<a id="eq-stability"></a>

$$
\boxed{\left\lVert A-E\right\rVert \le
\min\{1/2,(2d-1)\varepsilon\}.}\tag{10.1}
$$

若整个实效果菜单满足 $\sum_eA_e=I$，同样逐事件平均后仍有 $\sum_eE_e=I$。

**证明。**

$\tau$ 是保正、保单位的对合，故平均 $E$ 正、被 $I$ 支配，并满足 $\tau(E)=E$。
写

$$
D=A-\tau(A)=\begin{pmatrix}S&T\\T&-S\end{pmatrix},
\qquad S=S^{\mathsf T},\quad T=T^{\mathsf T}.
$$

单轴锚给 $|S_{ii}|\le\varepsilon$。
实和桥读出
$(S_{ii}+S_{jj})/2+S_{ij}$，故 $|S_{ij}|\le2\varepsilon$。
混合桥读出 $(S_{ii}-S_{jj})/2+T_{ij}$，故 $|T_{ij}|\le2\varepsilon$；
$i=j$ 时有更强的 $|T_{ii}|\le\varepsilon$。
每行绝对值之和至多

$$
\varepsilon+\varepsilon+(2d-2)\,2\varepsilon
=(4d-2)\varepsilon.
$$

实对称矩阵的算符范数不超过最大行绝对和，因此
$\left\lVert A-E\right\rVert =\left\lVert D\right\rVert /2\le(2d-1)\varepsilon$。
同时 $0\le A,\tau(A)\le I$ 给 $-I\le D\le I$，产生 $1/2$ 上界。
最后 $\sum_eE_e=(I+\tau(I))/2=I$。

□

于是对任意 $x$，

$$
|w(x)-\langle x,Ex\rangle |\le
\min\{1/2,(2d-1)\varepsilon\}\left\lVert x\right\rVert ^2.
$$

该界对正菜单同时保持完备性；未主张常数最优。
平均给出相容效果的数学修复，不自动供应一个可实现的实验控制，
也不自动修改既有事件的实际后继。

**白话图景。**只要二次关系已经精确成立，有限相位锚稍有误差，就能把整张读出表修到同一复方向，
并且知道每个输入最多改动多少。修复后的各个结果仍合成原来的总关系。
这是一条有误差预算的关系定理；让某个实际装置执行这张修复表，仍需它自己的控制供应。

<a id="section-11"></a>

## 11. 近似反向相容的跨尺度障碍

上一节只近似共同相位校准。若把二元反向条件本身也改为近似，
不能直接承诺在全部非零强度尺度上一致接近某个二次效果。
以下是解析反例，不依赖离散数值检验。

<a id="statement-11-1"></a>

#### 命题 11.1（任意小相干缺陷与固定跨尺度距离并存）

对任意 $\delta>0$，在任一非零有限复 Hilbert 空间上定义

<a id="eq-logweight"></a>

$$
w_\delta(x)=\left\lVert x\right\rVert ^2
\left[\frac12+\frac14\sin\!\left(\delta\log\left\lVert x\right\rVert ^2\right)\right]
\quad(x\ne0),\qquad w_\delta(0)=0.\tag{11.1}
$$

它与 $N-w_\delta$ 构成非负完整菜单，连续且共同相位不变。
记 $S=\left\lVert u\right\rVert ^2+\left\lVert v\right\rVert ^2+\left\lVert z\right\rVert ^2$，则

<a id="eq-i3small"></a>

$$
|I_3(u,v,z)|\le\frac{15}{4}\delta S\le4\delta S.\tag{11.2}
$$

但是

<a id="eq-farallscales"></a>

$$
\boxed{\inf_{0\le E\le I}\ \sup_{x\ne0}
\frac{|w_\delta(x)-\langle x,Ex\rangle |}{\left\lVert x\right\rVert ^2}=\frac14.}\tag{11.3}
$$

**证明。**

权重处于 $[N/4,3N/4]$，所以非负、完备且在零处连续，其余连续性与相位不变显然。
若 $S=0$，全部输入为零，式[(11.2)](#eq-i3small)成立。
设 $S>0$，把 $I_3$ 的七个非空项对应平方范数记为 $t$，符号记为 $\pm$。
范数平方是二次型，所以 $\sum\pm t=0$。
利用 $\sin$ 的 Lipschitz 界，可减去共同的 $\sin(\delta\log S)$ 而得

$$
|I_3|\le\frac\delta4\sum t\,|\log(t/S)|,
$$

其中 $t=0$ 的项按极限取零。
三个输入之和的 $t\le3S$，三项双输入之和各有 $t\le2S$，
三项单输入各有 $t\le S$。
对 $0<r\le1$，有 $-r\log r\le1-r\le1$；
对 $1\le r\le a$，有 $r\log r\le r(r-1)\le a(a-1)$。
所以三类上界可依次取 $6,2,1$，从而

$$
\sum t|\log(t/S)|\le (6+3\cdot2+3\cdot1)S=15S.
$$

这证明[(11.2)](#eq-i3small)。

固定一个单位向量 $\psi$，令 $x=r\psi,r>0$。
由于 $\delta\log r^2$ 遍历实数，
$w_\delta(r\psi)/r^2$ 遍历 $[1/4,3/4]$。
任何固定效果 $E$ 沿该射线只给常数 $\langle \psi,E\psi\rangle$，
到区间两端的最大距离至少 $1/4$。
因此左侧不小于 $1/4$；取 $E=I/2$ 则达到该界。

□

由恒等式 $I_3(u,v,-v)=-\Delta(u,v)$，这个例子还满足

$$
|\Delta(u,v)|\le 8\delta(\left\lVert u\right\rVert ^2+\left\lVert v\right\rVert ^2).
$$

所以令 $\delta\to0$ 确实能使相对反向缺陷任意小，
而全部强度尺度上的相对二次逼近距离保持 $1/4$。

这项边界必须准确阅读：

1. 在单位球面上，该例恰好为 $w_\delta=1/2$，已经是 Born 读出。

   它不否定只讨论归一态的稳定性结论。
2. 它不满足精确二次齐次性；若额外保留了这项跨尺度约束，反例便被排除。

   本节检验的是近似反向闭合、正菜单与共同相位的组合。
3. 一个固定尺度锚并不足以排除它，因为它在尺度 $\left\lVert x\right\rVert ^2=1$ 已完全正确。

4. 对这个例子，在有限对数范围

   $|\log(\left\lVert x\right\rVert ^2/s_0)|\le L$ 内，取

   $$
   E_0=\left[\frac12+\frac14\sin(\delta\log s_0)\right]I
   $$

   即有相对误差至多 $\delta L/4$。这只是该解析族的范围界，
   不是已经证明任意近似规则都满足同样的通用稳定定理。

**白话图景。**每次局部比较只偏一点，偏差仍可能随着总强度缓慢积累。
在一个固定尺度看，它完全正常；走过无限多尺度以后，它却能偏到另一边。
因此“精确相容推出二次读出”已经证明，“近似相容在所有尺度都可靠”还需要额外的尺度控制。
这个区别让新候选的适用边界保持清楚。

<a id="section-12"></a>

## 12. 接回既有理论：从事件关系到实际后继

本轮已供应事件正核 $k_e$ 和效果 $E_e$。
现在沿用 v78 已完成的实际后继接口，展示这项结果在整个理论中如何被使用。

<a id="statement-12-1"></a>

#### 定理 12.1（同一事件核锁定实际后继的线性表示）

设声明历史向量 $x_h$ 复张成输入空间，事件 $e$ 后的*实际*输出向量为 $y_{e,h}$，
并满足已经声明的 Gram 匹配

$$
\langle y_{e,h},y_{e,g}\rangle =k_e(x_h,x_g).
$$

则存在唯一线性映射 $M_e$ 到实际输出的张成空间，使

$$
M_ex_h=y_{e,h},\qquad M_e^*M_e=E_e.
$$

其最小输出表示满足

$$
M_e=V_eE_e^{1/2},
$$

其中 $V_e$ 在 $E_e^{1/2}$ 的像上等距。

**证明。**

先令 $M_e(\sum_hc_hx_h)=\sum_hc_hy_{e,h}$。
若输入线性组合为零，则

$$
\left\lVert \sum_hc_hy_{e,h}\right\rVert ^2
=\sum_{h,g}\overline{c_h}c_gk_e(x_h,x_g)
=\langle \sum_hc_hx_h,E_e\sum_gc_gx_g\rangle =0.
$$

所以定义无歧义。相同等式给
$\left\lVert M_ex\right\rVert ^2=\langle x,E_ex\rangle \le\left\lVert x\right\rVert ^2$。
由极化得到 $M_e^*M_e=E_e$，张成性保证唯一。
令 $V_e(E_e^{1/2}x)=M_ex$；两个输入代表同一个左侧时，它们的差也有零输出范数，
故 $V_e$ 良定义，且由同一范数恒等式为等距。

□

这重述了项目中已经证明的实际后继桥[3](#ref-closure)，以显示 v79 怎样供应它的输入。
效果只固定读出与输出之间的内积几何；实际后继决定等距方向 $V_e$。
所以 $E_e$ 不是完整测后态的唯一指定：不同实际装置可以有同一效果，而有不同输出方向。

若记录结果 $e$ 的实际分支为 $M_e$，则

$$
\mathcal I_e(\rho)=M_e\rho M_e^*,\qquad
\Pr(e\mid\rho)=\operatorname{Tr} (\rho E_e).
$$

当该概率非零时，再除以它得到条件后态。
完整菜单给 $\sum_eM_e^*M_e=I$。
若各结果输出空间不同，带结果标签的完整输出取
$\bigoplus_e M_e\rho M_e^*$，其总迹保持不变；
若已声明共同输出空间及相应嵌入，才可在该空间直接求和得到无选择映射。
对任意辅助空间与正 $X$，

$$
(\mathcal I_e\otimes\operatorname{id})(X)
=(M_e\otimes I)X(M_e^*\otimes I)\ge0,
$$

故其表示完全正。
若粗事件包含实际声明的细结果 $\alpha$，且这些细分支已嵌入同一声明输出空间，
相应求和得到 $\mathcal I_e(\rho)=\sum_\alpha M_{e\alpha}\rho M_{e\alpha}^*$；
否则先保留带细结果标签的直和输出。
这些结论表述已有操作的结构，不授予任意数学完全正映射的可实现性。

**白话图景。**读出关系先告诉我们每个结果分到了多少、保留了哪些相干比较。
实际后继再告诉我们这份关系被送到哪个内部记录或输出对象。
两者的内积表必须一致，于是线性量子操作和测后态公式接上了。
同一种结果概率可以由不同装置产生，因为装置送往的后继方向仍可能不同。

### 12.1 三维球还可看作内部二标签记录

在数学表示上，引入正交标签 $|0\rangle ,|1\rangle$，并写

$$
|\Psi\rangle =\frac{|0\rangle \otimes u+|1\rangle \otimes v}{\sqrt{s}},
\qquad s=N(u)+N(v)>0.
$$

标签端的约化态恰为前文 $R_K$。
另一端施加完整事件仪器后，对 $s_e>0$，结果 $e$ 对应的标签未归一态是

$$
\frac1s
\begin{pmatrix}
w_e(u)&\overline{k_e(u,v)}\\
k_e(u,v)&w_e(v)
\end{pmatrix}
=\tau_eR_e.
$$

若 $s_e=0$，标签未归一态直接记为零，不定义 $R_e$。
忽略结果时，省略这些零项便有 $\sum_e\tau_eR_e=R_K$。
因此球内加权守恒也是“分辨结果后再合并，仍恢复同一个内部标签边缘态”的关系。
这是张量表示中的等式；若要作为实际过程，二标签载体、该准备和该仪器须属于实际声明资源。

**白话图景。**用两张内部标签记住“从哪条历史来”，它们的关系就是球里的那个点。
每个读出结果给这两张标签一个条件关系。
结果全部重新合在一起，标签原来的关系仍然保留。
这样，球上的关系本身也能成为整体内部可记录、可继续比较的对象。

### 12.2 与现有量子公理的接口地图

本轮不是让一个反向恒等式独自供应整套物理结构。
它替换已有理论中的一个读出前件，再与其他已完成接口组合。

| 通常的量子形式 | 在项目中的来源与本轮位置 |
| --- | --- |
| 复 Hilbert 状态空间 | 已有共同正历史核、零核商、实际共同 $J$；v79 继承 |
| 正效果与 POVM | 本轮反向相容推出实二次形式，有限相位证书推出复效果，菜单给 $\sum E_e=I$ |
| Born 概率 | 本轮效果形式，接既有全效果可加读出、同根校准与声明准备运输 |
| 密度算符读出 | 已有混合与读出等价结构；$\rho=\sum_jp_j\|\psi_j\rangle \langle \psi_j\|$ 给 $\operatorname{Tr} (\rho E)$ |
| 量子仪器与条件后态 | 已有实际后继 Gram 匹配，本轮事件核作为其输入；推得 $M^*M=E$ 与 Kraus 形式 |
| 复合与纠缠 | 已有共同复积核与产品历史张成性给张量表示；一般整体向量不要求分解 |
| 可逆与连续动力学 | 已有保核历史给酉表示；光滑推进给 $H(t)=i\hbar\dot U(t)U(t)^*$ 与薛定谔式 |
| 圆、椭圆与周期 | 既有历史弧、投影及返回群定理；本轮补二元事件核中的相位圆与半周反号 |

表中动力学结论依赖实际声明的 $C^1$ 酉族；若再有一参数群条件，才进一步得到自治生成元。
$\hbar$ 在这一表示中是时间与生成元的单位常数，本稿没有预测其物理数值。
有限维谱定理可以把声明的锐测量写成自伴可观测量；任意谱测量的实际供应仍不是纯表示定理的结论。
相关完整前件与证明见 v78 综合稿及其来源[4](#ref-synthesis)、[11](#ref-v78)。

N1 的相干桥相容、N2 的共享历史充分性与最小内部完成继续保持已证地位[9](#ref-n1)、[10](#ref-n2)。
本轮补强的是它们所使用的读出关系供应，没有将它们重新改列为待解问题。

<a id="section-13"></a>

## 13. 把“公理内生”锁成可检验的定义间约束

“一切都在 $\Omega$”可以要求表达、参考、读出与记录都来自同一个整体。
它本身不蕴含任意选定的代数恒等式。
本轮把这项纲领落实成以下同一性约束：

1. 同一个事件 $e$ 在分别读、合并读和反向读时必须由同一个 $w_e$ 表示；

2. 同一个相干反向 $v\mapsto-v$ 在所有合成上下文中保持同一含义；

3. 同一个共同参考 $J$ 在各事件和锚态之间保持一致；

4. 各结果使用同一个总强度 $N$，并分解同一个父核 $K$；

5. 结果后的实际历史，以同一个 $k_e$ 接续，而非另换一套无关比较。

公理因此不是漂在整体外面的额外数值，而是这些内部定义能否共同成立的条件。
但定义一种相容结构，与证明现实一定采用该结构，是两个层次。
式[(9.1)](#eq-nonborn)已经给出另一种正、连续、完备的读出模型；它不能满足本候选，
却不会仅因“属于 $\Omega$”而产生形式逻辑矛盾。

<a id="statement-13-1"></a>

#### 定理 13.1（本轮完成的条件式重建）

在已经供应的有限正相干域、共同复方向及同根读出接口上，
v79 的完整候选与唯一复效果菜单一一对应。
它同时强制：

1. 交叉关系的实双线性、全相干 $I_3=0$ 与全部有限二元展开；

2. 同一事件的正核及核区间分解 $0\le k_e\le K$、$\sum_ek_e=K$；

3. 每个二元截面的带尺度三维球表示及完整菜单加权守恒；

4. 声明相位域上的圆周交叉读出、半周反号与全周返回；

5. 在已供应实际后继的接口上，唯一线性后继表示、量子仪器及其概率公式。

其与 v78 平衡重编码条件的等价，限于同一个完整接口。
有限相位证书的最小性，限于固定单标量相位差探针。

**证明。**

依次应用定理[5.2](#statement-5-2)、[5.3](#statement-5-3)、有限二元展开、
定理[7.1](#statement-7-1)、[7.2](#statement-7-2)、相位圆命题及定理[12.1](#statement-12-1)。
所有桥接前件均已在各节明确列出。

□

从有限检验角度也要区分：$d(d+1)$ 个锚仅在二次结构已经取得以后认证共同相位。
本稿没有宣称以有限样本就能认证任意未知非线性函数在全部输入上满足反向恒等式。
一个完整候选的逻辑简洁性，与有限实验检验的充分性，不是同一个命题。

### 13.1 本轮完整白话

> **量子在本轮理论中的图景是：整体内部的历史可以相干地连接，
> 同一个结果要同时比较各条历史及它们之间的关系。**
> 两条历史合起来时，可能加强，也可能抵消。
> 如果把其中一条转过半圈，那份交叉关系就应反号；
> 而无论历史此前怎样合成，这个规则都必须是同一条规则。
> 
> 非负结果和共同总强度使这种反向相容无法夹带额外偏置，
> 最后把读出锁成一张正二次关系表。
> 再用有限内部锚确认所有结果共用同一相位方向，这张表就成为复量子效果，
> Born 公式从中出现。
> 
> 任意两条历史的关系可以压缩成三维球里的一个点，同时保留它的强度。
> 改变相对相位，交叉坐标沿圆转动：半圈加强变抵消，一圈恢复。
> 各结果只是把同一个父关系分成若干份；按强度把这些份重新合起来，
> 仍回到原来的关系。结果后的实际记录继续携带这些比较，
> 因而可以再次参与合成、读出和下一轮关系约束。
> 
> 所以这一候选把“量子读出为何二次”归到一个具体内部要求：
> **同一对历史的交叉关系，在相干反向与任意内部合成中必须保持相容。**
> 它不是从空无中宣布所有物理规律；它是在已经明确的整体接口上，
> 把一项外写的读出公理改成了可以定位冲突、证明等价、给出反例的内部关系定义。

<a id="section-14"></a>

## 14. 版本、核查范围与证明归属

本稿版本为 v79，承接 v78。项目文本固定于提交：

`b70843ac423b4be12fda256a7924f0e4695b8bac`

（提交时间 2026 年 11 月 1 日 20:45:53 UTC），用于核查的 24 项项目源均校验了 Git blob 身份。
该快照的公开 v78 综合 Markdown 为 21 节文本；
它与此前本地扩充的 v78 综合稿不是逐字相同的版本，本文不把本地扩充稿声称为已公开提交。
本轮未写入或发布远端仓库。

证明归属具体如下：

1. V49 已有双线性交叉闭合、非负消除线性漂移及极化路线；V76 对此作综合[1](#ref-v49)、[2](#ref-v76)。

   本稿所推进的是以反向条件供应双线性，并与完整 v78 权重条件作精确等价连接。
2. 共同 $g,J$、有限根参考、核区间效果、同根读出、实际后继与复合供应链沿用项目已有证明[3](#ref-closure)、[4](#ref-synthesis)。

3. 本稿构造的有限相位锚、限定探针数量下界、误差修复界及反例均在文内给出解析证明。

   对已核查项目源中的相对增量作此定位，不构成对全部数学文献的学术首创声明。
4. Sorkin 干涉层级与一般重建文献提供背景边界，不能替代本稿更强的全相干域量词[12](#ref-sorkin)、[13](#ref-barnum)。

5. 文中计算均为解析等式、不等式与线性代数证明。

   未使用数学数值实验、枚举或计算机代数作为证明；文献检索、PDF 编译与可读性检查仅服务于资料及呈现。

## 来源与证明归属

<a id="ref-v49"></a>

**[1]** AURIC 项目，
[V49：和积幂、二次关系闭合与归一提升](https://github.com/the-omega-institute/trureturing/blob/b70843ac423b4be12fda256a7924f0e4695b8bac/docs/develop/theory/AURIC_SUM_PRODUCT_POWERS_QUADRATIC_RELATION_CLOSURE_AND_NORMALIZED_LIFTING_V49.md)，尤见第 4、8 节。
<a id="ref-v76"></a>

**[2]** AURIC 项目，
[V76：和积生成、二次关系网络与内生量子结构](https://github.com/the-omega-institute/trureturing/blob/b70843ac423b4be12fda256a7924f0e4695b8bac/docs/develop/theory/AURIC_SUM_PRODUCT_GENERATION_QUADRATIC_RELATION_NETWORKS_AND_ENDOGENOUS_QUANTUM_STRUCTURE_V76.md)，尤见第 6 节。
<a id="ref-closure"></a>

**[3]** AURIC 项目，
[V78 续稿：内生闭合、有限根证书与结果核递归](https://github.com/the-omega-institute/trureturing/blob/b70843ac423b4be12fda256a7924f0e4695b8bac/docs/develop/theory/AURIC_ENDOGENOUS_CLOSURE_FINITE_ROOT_CERTIFICATES_AND_OUTCOME_KERNEL_RECURSION_V78_CONTINUATION.md)，尤见第 3、6--8、10 节。
<a id="ref-synthesis"></a>

**[4]** AURIC 项目，
[V78 综合稿：内生关系量子理论与统一关系公理](https://github.com/the-omega-institute/trureturing/blob/b70843ac423b4be12fda256a7924f0e4695b8bac/docs/develop/theory/AURIC_ENDOGENOUS_RELATIONAL_QUANTUM_THEORY_UNIFIED_RELATIONAL_AXIOMS_V78_SYNTHESIS.md)，尤见第 8、10、13 节。
<a id="ref-v77"></a>

**[5]** AURIC 项目，
[V77：量子公理反向定位、二元见证与内部相容](https://github.com/the-omega-institute/trureturing/blob/b70843ac423b4be12fda256a7924f0e4695b8bac/docs/develop/theory/AURIC_REVERSE_LOCATION_OF_QUANTUM_AXIOMS_BINARY_WITNESSES_AND_INTERNAL_COMPATIBILITY_V77.md)，尤见第 5 节。
<a id="ref-arcs"></a>

**[6]** AURIC 项目，
[V78 续稿：历史弧、椭圆读出与内生关系闭合](https://github.com/the-omega-institute/trureturing/blob/b70843ac423b4be12fda256a7924f0e4695b8bac/docs/develop/theory/AURIC_HISTORY_ARCS_ELLIPTIC_READOUT_AND_ENDOGENOUS_RELATIONAL_CLOSURE_V78_CONTINUATION.md)。
<a id="ref-periods"></a>

**[7]** AURIC 项目，
[V78 续稿：圆、周期与内生时钟](https://github.com/the-omega-institute/trureturing/blob/b70843ac423b4be12fda256a7924f0e4695b8bac/docs/develop/theory/AURIC_CIRCLES_PERIODS_AND_ENDOGENOUS_CLOCKS_V78_CONTINUATION.md)。
<a id="ref-atlas"></a>

**[8]** AURIC 项目，
[量子起源的内生切面图谱与离散重建边界](https://github.com/the-omega-institute/trureturing/blob/b70843ac423b4be12fda256a7924f0e4695b8bac/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md)，尤见第 28--29 节。
<a id="ref-n1"></a>

**[9]** AURIC 项目，
[V78 候选 N1：相干桥、无损相容与有效电阻](https://github.com/the-omega-institute/trureturing/blob/b70843ac423b4be12fda256a7924f0e4695b8bac/docs/develop/theory/AURIC_COHERENT_BRIDGES_LOSSLESS_COMPATIBILITY_AND_EFFECTIVE_RESISTANCE_N1_V78_CONTINUATION.md)。
<a id="ref-n2"></a>

**[10]** AURIC 项目，
[V78 候选 N2：共享历史充分性、最小内部完成与维数预算](https://github.com/the-omega-institute/trureturing/blob/b70843ac423b4be12fda256a7924f0e4695b8bac/docs/develop/theory/AURIC_SHARED_HISTORY_SUFFICIENCY_MINIMAL_INTERNAL_COMPLETION_AND_DIMENSION_BUDGET_N2_V78_CONTINUATION.md)。
<a id="ref-v78"></a>

**[11]** AURIC 项目，
[V78：门流形、可积关系、切向核与递归误差](https://github.com/the-omega-institute/trureturing/blob/b70843ac423b4be12fda256a7924f0e4695b8bac/docs/develop/theory/AURIC_GATE_MANIFOLDS_INTEGRABLE_RELATIONS_TANGENT_KERNELS_AND_RECURSIVE_ERROR_V78.md)。
<a id="ref-sorkin"></a>

**[12]** R. D. Sorkin,
*Quantum Mechanics as Quantum Measure Theory*,
Modern Physics Letters A 9 (1994), 3119--3128.
[arXiv:gr-qc/9401003](https://arxiv.org/abs/gr-qc/9401003);
[doi:10.1142/S021773239400294X](https://doi.org/10.1142/S021773239400294X).
<a id="ref-barnum"></a>

**[13]** H. Barnum, M. P. Müller, C. Ududec,
*Higher-order interference and single-system postulates characterizing quantum theory*,
New Journal of Physics 16 (2014), 123029.
[arXiv:1403.4147](https://arxiv.org/abs/1403.4147);
[doi:10.1088/1367-2630/16/12/123029](https://doi.org/10.1088/1367-2630/16/12/123029).

## 源稿前言与排版元数据

```latex
% !TEX program = xelatex
\documentclass[11pt,a4paper]{article}
\usepackage[margin=24mm,headheight=16pt]{geometry}
\IfFileExists{ctex.sty}{\usepackage[UTF8,fontset=auto]{ctex}}{
  \usepackage{fontspec}
  \IfFontExistsTF{Noto Serif CJK SC}{\setmainfont{Noto Serif CJK SC}[AutoFakeBold=1.7]}{\setmainfont{NotoSerifCJKsc-Regular.otf}[Path=fonts/,AutoFakeBold=1.7,AutoFakeSlant=.15]}
  \XeTeXlinebreaklocale "zh"
  \XeTeXlinebreakskip=0pt plus 1pt
}
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage{xcolor,booktabs,array,tabularx,longtable}
\usepackage{fancyhdr,enumitem,hyperref,needspace,tikz}
\usetikzlibrary{arrows.meta,calc,positioning}
\definecolor{ink}{HTML}{17384A}
\definecolor{accent}{HTML}{007D86}
\definecolor{warm}{HTML}{B75B39}
\hypersetup{colorlinks=true,linkcolor=ink,urlcolor=accent,citecolor=ink,
pdftitle={AURIC v79：二元反向相容公理与量子读出重建}}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small AURIC / v79 / 二元反向相容}
\fancyhead[R]{\small 定义、定理、证明与白话}
\fancyfoot[C]{\thepage}
\setlength{\parindent}{1.8em}
\setlength{\parskip}{4pt}
\setlength{\emergencystretch}{3em}
\setlist{nosep,leftmargin=2em}
\renewcommand{\baselinestretch}{1.10}
\renewcommand{\contentsname}{目录}
\renewcommand{\abstractname}{摘要}
\renewcommand{\figurename}{图}
\renewcommand{\refname}{来源与证明归属}
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
\newcommand{\tr}{\operatorname{Tr}}
\newcommand{\Span}{\operatorname{span}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\ran}{\operatorname{ran}}
\newcommand{\ket}[1]{|#1\rangle}
\newcommand{\bra}[1]{\langle#1|}
\newcommand{\plain}[1]{\par\noindent\textbf{白话图景。}#1\par}
\newcommand{\repo}[2]{\href{https://github.com/the-omega-institute/trureturing/blob/b70843ac423b4be12fda256a7924f0e4695b8bac/#1}{#2}}
\title{\color{ink}\bfseries 二元反向相容公理\\[6pt]
\large 从相干反向与有限相位证书推出量子读出\\[4pt]
AURIC v79：一个完整候选及其边界}
\author{项目连续研究稿}
\date{2026 年 11 月 2 日}
```

```latex
\begin{document}
\maketitle
\clearpage
\setcounter{tocdepth}{1}
{\small\setlength{\parskip}{0pt}\tableofcontents}
\newpage
\begin{quote}
\end{quote}
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.21\textwidth}X@{}}
\toprule
\midrule
\bottomrule
\end{tabularx}
\end{center}
\begin{center}\small
\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{.23\textwidth}X@{}}
\toprule
\midrule
\bottomrule
\end{tabularx}
\end{center}
\begin{quote}
\end{quote}
\begin{center}\small\texttt{b70843ac423b4be12fda256a7924f0e4695b8bac}\end{center}
\begin{thebibliography}{99}
\small
\end{thebibliography}
\end{document}
```
