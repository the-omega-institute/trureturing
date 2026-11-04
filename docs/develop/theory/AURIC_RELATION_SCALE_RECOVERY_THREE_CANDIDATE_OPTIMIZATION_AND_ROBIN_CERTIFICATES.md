# AURIC：关系恢复尺度、三候选整数优化与 Robin 证书（编者描述性标题）

可以把你的判断推进成一个严格的表示原理，而且这次能得到更强的结果：

> **两个读出加一个关系，不仅可以放在三个正交坐标轴上；在适当的关系约束下，归一化通常会消去的尺度，也可以被关系本身唯一恢复。**

例如，对正数 $a,b$，将

$$
(a,b,ab)
$$

归一化为

$$
(X,Y,Z)=\frac{(a,b,ab)}{a+b+ab},
$$

仍能精确反解

$$
\boxed{a=\frac ZY,\qquad b=\frac ZX.}
$$

这为 AURIC 分析提供了一张真正保留算术信息的坐标图。继续接到 Robin 后，还可以证明：**对全部较大素数，完整的整数指数优化只需要比较 $0,1,2$ 三个候选；这三个候选能够稳定地放入三轴，并且剩余误差有统一上界。**

下面从通用表示到具体数论估计，逐步定义和证明。本轮沿用项目固定提交 [`98d92f3c…`](https://github.com/the-omega-institute/trureturing/tree/98d92f3c4013a4c4fba51ece2d8cd9d84aafc7fa)，主要衔接金字塔概率纤维、三轴任务保持条件，以及 Robin 的连续与整数价格接口。

---

## 一、把“任何二元读出加关系”写成精确命题

### 定义 1：指定的三元读出

设研究对象集合为 $\Omega$，给定

$$
A:\Omega\to I_A,\qquad
B:\Omega\to I_B,\qquad
C:\Omega\to I_C,
$$

其中 $A,B$ 是两个实标量读出，$C$ 是一个实标量关系读出。

$C$ 可以是：

- 已知关系 $C=\mathscr R(A,B)$；
- 实际取得的联合量；
- 误差、损失或约束余量。

指定保留所需信息的归一化

$$
\nu_A:I_A\to[0,1],\qquad
\nu_B:I_B\to[0,1],\qquad
\nu_C:I_C\to[0,1],
$$

并要求它们在所用范围上可逆。记

$$
(\alpha,\beta,c)
=
(\nu_A(A),\nu_B(B),\nu_C(C)).
$$

项目的金字塔坐标域为

$$
\mathcal P
=
\{(X,Y,Z):
X,Y,Z\ge0,\ X+Z\le1,\ Y+Z\le1\}.
$$

这是已有五模式占位凸体的精确定义。[项目基础公式文档，§3](https://github.com/the-omega-institute/trureturing/blob/98d92f3c4013a4c4fba51ece2d8cd9d84aafc7fa/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)

<!-- editorial-note:start readout-scope -->
**【编者局部说明：指定读出与稳定性的范围】** 定义 1 中三个归一化在实际使用范围上的可逆性是前提；没有假定任意取值域都存在保留全部信息的归一化，也没有假定这些逆映射具有统一稳定常数。定理 1 的精确缩放针对归一化后的三元组及其仿射嵌入；它保存所声明的三个标量，不自动恢复对象的其余信息。
<!-- editorial-note:end readout-scope -->

### 定理 1：任意这样的归一化三元读出，都能稳定嵌入金字塔

定义

$$
\boxed{
E(\alpha,\beta,c)
=
\left(
\frac18+\frac\alpha4,\,
\frac18+\frac\beta4,\,
\frac18+\frac c4
\right).
}
\tag{1}
$$

则

$$
E([0,1]^3)\subset\operatorname{int}\mathcal P,
$$

而且

$$
\boxed{
(\alpha,\beta,c)
=
4(X,Y,Z)-\left(\frac12,\frac12,\frac12\right).
}
\tag{2}
$$

对任何范数，

$$
\boxed{
\|E(u)-E(v)\|=\frac14\|u-v\|.
}
\tag{3}
$$

**证明。**

每个坐标都在 $[1/8,3/8]$ 中，因此

$$
X+Z\le\frac34<1,\qquad
Y+Z\le\frac34<1.
$$

逆公式由仿射表达式直接得到；距离公式来自统一缩放。证毕。

所以，你提出的通用性确实可以成立：**三个已指定的标量信息能够完整进入同一座金字塔，并在归一化坐标中具有明确的稳定性。**

这里保存的是声明的三元读出。若还要求它决定所有后续操作，则需要任务保持条件。

### 定理 2：运算能够下降到三轴上的充要条件

设三轴读出为 $\Phi:\Omega\to\mathcal P$，操作为 $T:\Omega\to\Omega$。

存在良定义的三轴操作 $\widetilde T$，使

$$
\Phi(T\omega)=\widetilde T(\Phi(\omega)),
$$

当且仅当

$$
\boxed{
\Phi(\omega)=\Phi(\omega')
\Longrightarrow
\Phi(T\omega)=\Phi(T\omega').
}
\tag{4}
$$

**证明。**

必要性由代入立即得到。

反过来，若式 $(4)$ 成立，就在每个像点上选任一原像 $\omega$，定义

$$
\widetilde T(\Phi(\omega)):=\Phi(T\omega).
$$

式 $(4)$ 保证结果不依赖原像选择。证毕。

<!-- editorial-note:start induced-image -->
**【编者局部说明：诱导操作的定义域】** 定理 2 中自然且唯一的诱导操作是 $\widetilde T:\Phi(\Omega)\to\Phi(\Omega)$。式 (4) 保证在像集上良定义；证明没有规定整个 $\mathcal P$ 上像集以外的值。若要处理一组后续操作，须分别核对它们保持该读出纤维，不能仅由三轴坐标的存在推出任务保持。
<!-- editorial-note:end induced-image -->

这与项目“联合来源的稳定商”接口一致：三轴能够承担整个任务，取决于操作是否保持读出纤维。[观察者三轴文档，§8](https://github.com/the-omega-institute/trureturing/blob/98d92f3c4013a4c4fba51ece2d8cd9d84aafc7fa/docs/develop/theory/AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md)

---

## 二、关系的更强作用：恢复被归一化消去的尺度

一般的单位和归一化

$$
N(a,b,r)=\frac{(a,b,r)}{a+b+r}
$$

会把同一正射线上的三元组识别起来：

$$
N(\lambda a,\lambda b,\lambda r)=N(a,b,r).
$$

但加入关系以后，允许对象可能只在每条射线上出现一次。

### 定理 3：关系与归一化纤维的交点判据

设 $M\subset(0,\infty)^3$ 是满足指定关系的三元组集合。

则 $N|_M$ 单射，当且仅当每条正射线与 $M$ 至多相交一次。

**证明。**

$$
N(v)=N(w)
$$

当且仅当 $w=\lambda v$，其中 $\lambda>0$。因此归一化能否反解，恰好取决于同一射线上是否存在多个合法对象。证毕。

### 定理 4：乘法关系使归一化完全可逆

取

$$
r=ab,\qquad a,b>0.
$$

令

$$
S=a+b+ab,
\qquad
(X,Y,Z)=\frac{(a,b,ab)}S.
$$

则

$$
X,Y,Z>0,\qquad X+Y+Z=1,
$$

并且

$$
\boxed{
a=\frac ZY,\qquad
b=\frac ZX,\qquad
S=\frac Z{XY}.
}
\tag{5}
$$

因此，正数二元组与开三角形

$$
\mathcal T=\{X,Y,Z>0:X+Y+Z=1\}
$$

一一对应。而

$$
\mathcal T\subset\operatorname{int}\mathcal P,
$$

因为

$$
X+Z=1-Y<1,\qquad Y+Z=1-X<1.
$$

**证明。**

正向的三个反解式直接约分即可。

反向给定 $X,Y,Z>0$、和为一，按式 $(5)$ 定义 $a,b,S$，则

$$
a+b+ab
=
\frac ZY+\frac ZX+\frac{Z^2}{XY}
=
\frac{Z(X+Y+Z)}{XY}
=
\frac Z{XY}=S.
$$

所以归一化公式确实恢复。证毕。

<!-- editorial-note:start chart-boundary -->
**【编者局部说明：反解与边界】** 式 (5) 的反解只在三个坐标严格为正的开三角形上使用；当分母坐标趋于零时，反解没有全域统一的稳定常数。下表的运算是在这张指定乘法关系图中恢复的算术量，原生同窗的端点共同选择所表示的加法与乘法关系是不同的定义。
<!-- editorial-note:end chart-boundary -->

### 加法、乘法、除法都能从同一个点读出

| 算术量 | 三轴读出 |
|---|---|
| $a$ | $Z/Y$ |
| $b$ | $Z/X$ |
| $a+b$ | $Z(X+Y)/(XY)$ |
| $ab$ | $Z^2/(XY)$ |
| $a/b$ | $X/Y$ |

例如

$$
(a,b)=(2,5)
$$

对应

$$
(X,Y,Z)=\left(\frac2{17},\frac5{17},\frac{10}{17}\right).
$$

原生首窗的隐藏加法 $2+5=7$，在这张乘法关系坐标图中由

$$
\frac{Z(X+Y)}{XY}
$$

恢复；乘法 $2\times5=10$ 则由

$$
\frac{Z^2}{XY}
$$

恢复。

**同一个归一化点确实同时保存了这两种运算。**

### 对数解释

令

$$
U=\log a,\qquad V=\log b,\qquad W=\log(ab).
$$

关系是

$$
\boxed{W=U+V.}
$$

归一化写成

$$
(X,Y,Z)=
\frac{(e^U,e^V,e^W)}{e^U+e^V+e^W}.
$$

它一般遗忘共同平移

$$
(U,V,W)\mapsto(U+t,V+t,W+t).
$$

但共同平移保持 $W=U+V$ 的条件是

$$
W+t=U+V+2t,
$$

所以必须 $t=0$。

这说明：**乘法关系与归一化纤维相交一次，因此能够恢复尺度。**

作为比较，关系 $r=a+b$ 对整体缩放不变，故单独归一化 $(a,b,a+b)$ 只保留比例。选择哪种关系参与归一化，是表示定义中的实质内容。

更一般地，若 $\mathscr R$ 是正的 $d$ 次齐次函数，且 $d\ne1$，则

$$
r=\mathscr R(a,b),\qquad
(X,Y,Z)=\frac{(a,b,r)}S
$$

给出

$$
\boxed{
S=
\left(
\frac Z{\mathscr R(X,Y)}
\right)^{1/(d-1)}.
}
\tag{6}
$$

<!-- editorial-note:start homogeneous-images -->
**【编者局部说明：齐次公式的适用像】** 式 (6) 取正实数幂，适用于所声明正齐次关系的实际合法像。由 $a=SX$、$b=SY$、$r=SZ$ 及齐次性，有 $SZ=S^d\mathscr R(X,Y)$；因 $S>0$、$\mathscr R(X,Y)>0$ 且 $d\ne1$，正尺度唯一。一次齐次关系在正射线上保持成立，因而不能用这种归一化恢复尺度。
<!-- editorial-note:end homogeneous-images -->

这是“关系恢复尺度”的一般形式。

---

## 三、直接把 Robin 放进这张归一化三轴图

<!-- editorial-note:start arithmetic-log-domains -->
**【编者局部说明：算术记号与对数定义域】** 下文 $n$ 为正整数，$p$ 总表示素数，$\mathbb N_0=\{0,1,2,\ldots\}$；$v_p(n)$ 是素数 $p$ 在 $n$ 中的指数，$\sigma(n)=\sum_{d\mid n,\ d>0}d$ 是正约数和，特别地 $\sigma(1)=\mathcal Z(1)=1$。所有 $\log$ 均为自然对数，$\gamma=\lim_{M\to\infty}(\sum_{j=1}^M1/j-\log M)$ 为 Euler 常数。涉及 Robin 比值及其对数时采用

$$
R(n)=\frac{\sigma(n)}{e^\gamma n\log\log n}
=\frac{\mathcal Z(n)}{e^\gamma\log\log n},\qquad n\ge3.
$$

此时 $T=\log n>1$，$R(n)>0$，且 $\log\log T$ 有定义。Robin 的目标范围仍是 $n>5040$；第七、八节含 $\log R(n)$ 的式子均在这个对数定义域内使用。保存这些算术读出及整数尺度，不等于已证明 Robin，也不等于完成原生五模式来源的实现。
<!-- editorial-note:end arithmetic-log-domains -->

为避免与金字塔坐标 $Z$ 混淆，这一节记

$$
\mathcal Z(n)=\frac{\sigma(n)}n.
$$

取两个读出及其乘法关系：

$$
a=n,\qquad b=\mathcal Z(n),\qquad ab=\sigma(n).
$$

定义

$$
(X_n,Y_n,Z_n)
=
\frac{(n,\mathcal Z(n),\sigma(n))}
{n+\mathcal Z(n)+\sigma(n)}.
$$

那么

$$
\boxed{
n=\frac{Z_n}{Y_n},
\qquad
\mathcal Z(n)=\frac{Z_n}{X_n}.
}
\tag{7}
$$

Robin 不等式成为

$$
\boxed{
\frac{Z_n}{X_n}
<
e^\gamma
\log\log\left(\frac{Z_n}{Y_n}\right),
\qquad
\frac{Z_n}{Y_n}>5040.
}
\tag{8}
$$

所以三轴归一化没有丢掉 Robin 所需的尺度。

下一步的任务是证明：**实际整数形成的像集全部落在式 $(8)$ 的安全区域。** 为此，需要从素数幂的整数结构取得定量估计。

---

## 四、一个新的全域推进：较大素数只需要三个整数候选

这一步把“三轴表示”变成一个真正的全整数优化工具。

### 定义 2：局部价格目标

对素数 $p$，定义

$$
S_p(a)=1+p^{-1}+\cdots+p^{-a},
\qquad a\in\mathbb N_0,
$$

以及连续延拓

$$
h_p(u)
=
\log\frac{1-e^{-u}/p}{1-1/p},
\qquad u\ge0.
$$

在整数格点上，

$$
h_p(a\log p)=\log S_p(a).
$$

固定价格参数

$$
H>2,\qquad \eta=\frac1{H-1},
$$

并定义

$$
g_{p,H}(u)=h_p(u)-\eta u.
$$

这里的 $H$ 是价格参数，与上一轮由总尺度定义的 $K(n)$ 分开使用。

项目已有的价格优化目标正是

$$
\frac{\mathcal Z(n)}{n^\eta}
=
\frac{\sigma(n)}{n^{1+\eta}}.
$$

下面继续发展其整数与连续接口。[项目 FULL_STOCK 文档，§§455–458](https://github.com/the-omega-institute/trureturing/blob/98d92f3c4013a4c4fba51ece2d8cd9d84aafc7fa/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION_ROBIN_FULL_STOCK.md)

<!-- editorial-note:start full-integer-local-max -->
**【编者局部说明：完整整数局部最大值】** 为使第五、六节的记号覆盖全部素数，统一定义

$$
m_p(H):=\max_{a\in\mathbb N_0}
\bigl[\log S_p(a)-\eta a\log p\bigr].
$$

对每个 $p$，括号内随 $a\to\infty$ 趋于负无穷，故最大值取得。引理 1 的相邻整数结论 (9) 用于 $p<H$ 的活动情形；若 $p\ge H$，严格凹性及零点右侧的负导数给出唯一整数最优指数 $a=0$，此时 $m_p(H)=0$，包括 $p=H$。第五节的三候选坐标图及公式 (13) 只用于严格范围 $H^{1/3}<p<H$，不是小素数的定义。
<!-- editorial-note:end full-integer-local-max -->

### 引理 1：连续最大点及相邻整数候选

求导得

$$
g'_{p,H}(u)
=
\frac1{pe^u-1}-\eta,
$$

$$
g''_{p,H}(u)
=
-\frac{pe^u}{(pe^u-1)^2}<0.
$$

若 $p\ge H$，最大点是 $u=0$。

若 $p<H$，连续最大点为

$$
u_p^*=\log\frac Hp.
$$

令

$$
\beta_p=\frac{\log(H/p)}{\log p}.
$$

则整数最大指数只可能是

$$
\boxed{
a\in\{\lfloor\beta_p\rfloor,\lceil\beta_p\rceil\}.
}
\tag{9}
$$

**证明。**

函数严格凹，在 $u_p^*$ 左侧增加、右侧减少，因此整数格点最大值只能在连续最大点两侧相邻格点取得。证毕。

### 定理 5：对 $p>H^{1/3}$，三个候选已经完备

令

$$
X=H^{1/3}.
$$

若

$$
X<p<H,
$$

则

$$
0<\beta_p<2.
$$

因此

$$
\boxed{
\max_{a\ge0}
\left[\log S_p(a)-\eta a\log p\right]
=
\max_{a\in\{0,1,2\}}
\left[\log S_p(a)-\eta a\log p\right].
}
\tag{10}
$$

<!-- editorial-note:start three-candidate-endpoints -->
**【编者局部说明：严格端点】** 此处 $\beta_p=\log H/\log p-1$，严格条件 $H^{1/3}<p<H$ 正好给出 $0<\beta_p<2$；与引理 1 合用便排除了全部更高整数指数。若某素数恰等于 $H^{1/3}$，它在式 (18) 中归入小素数部分；$p\ge H$ 的情形由零指数单独处理。
<!-- editorial-note:end three-candidate-endpoints -->

这不是把高指数忽略掉。它证明了：**在这段素数范围内，更高指数不可能成为最优者。**

---

## 五、三个候选可以忠实、稳定地归一化到 AURIC 三轴

对 $X<p<H$，定义

$$
w_0=1,
$$

$$
w_1=S_p(1)p^{-\eta},
$$

$$
w_2=S_p(2)p^{-2\eta}.
$$

令

$$
W=w_0+w_1+w_2,
\qquad
\pi_i=\frac{w_i}{W}.
$$

因为基准 $w_0=1$ 已知，

$$
\boxed{
w_i=\frac{\pi_i}{\pi_0}.
}
\tag{11}
$$

所以这次归一化也完整保留了尺度。

选择三轴坐标

$$
\boxed{
(X_p,Y_p,Z_p)=(\pi_1,\pi_2,\pi_0).
}
\tag{12}
$$

它们严格正、和为一，因此位于金字塔内部的三角截面。

局部整数最大值是

$$
\boxed{
m_p(H)
=
\log\max\{X_p,Y_p,Z_p\}-\log Z_p.
}
\tag{13}
$$

这里 $0,1,2$ 指候选素数指数；三个归一化权重是为价格比较定义的读出。

### 定理 6：这个读出具有统一稳定常数

因为 $p\ge2$、$\eta>0$，

$$
w_1\le\frac32,\qquad
w_2\le\frac74.
$$

因此

$$
W\le\frac{17}{4},
\qquad
\boxed{Z_p=\pi_0\ge\frac4{17}.}
\tag{14}
$$

若两份合法归一化候选点满足

$$
\|P-P'\|_\infty\le\varepsilon,
$$

则

$$
\boxed{
|m_p(P)-m_p(P')|
\le\frac{17}{2}\varepsilon.
}
\tag{15}
$$

**证明。**

最大值函数对最大范数是 $1$-Lipschitz。式 $(13)$ 中两个对数的自变量都至少为 $4/17$，因此每个对数的变化至多为 $17\varepsilon/4$。相加即得。证毕。

<!-- editorial-note:start legal-candidate-stability -->
**【编者局部说明：合法候选点上的稳定性】** 定理 6 比较的是按本节正权重构成的两份合法候选点；两份点的第三坐标及各自最大坐标均至少为 $4/17$。对数在这些自变量之间的区间上导数至多为 $17/4$，这才给出式 (15)。该常数没有扩展到任意金字塔点或任意趋近边界的归一化点。三个候选权重是辅助价格读出，不能仅由它们位于三角截面就把它们识别为任意原生五模式律。
<!-- editorial-note:end legal-candidate-stability -->

这一步提供了三项明确保证：

- 归一化可逆；
- 最优候选可恢复；
- 误差放大有统一上界。

---

## 六、三个候选能够逼近完整全整数最优值，并给出严格误差

定义

$$
C_{\mathbb Z}(\eta)
=
\max_{n\ge1}\frac{\mathcal Z(n)}{n^\eta}.
$$

记局部连续最大值为

$$
c_p(H)=\max_{u\ge0}g_{p,H}(u).
$$

对于 $p<H$，

$$
c_p(H)
=
\log\frac{1-1/H}{1-1/p}
-
\frac{\log(H/p)}{H-1}.
\tag{16}
$$

对于 $p\ge H$，它等于零。

Euler 分解与局部独立最优化给出

$$
\boxed{
\log C_{\mathbb Z}(\eta)
=
\sum_{p<H}m_p(H).
}
\tag{17}
$$

这个最大值确实取得：只有有限个 $p<H$ 可能出现，将各局部最大指数相乘，就形成一个实际整数最大点。

### 定义 3：三候选上界

令 $X=H^{1/3}$，定义

$$
\boxed{
\begin{aligned}
A_2(H)
={}&
\sum_{p\le X}c_p(H)\\
&+
\sum_{X<p<H}
\max_{a\in\{0,1,2\}}
\left[
\log S_p(a)-\eta a\log p
\right].
\end{aligned}
}
\tag{18}
$$

小素数部分暂用连续最大值；其余部分已经是完整的整数最大值。

### 定理 7：全域统一误差界

对每个 $H>2$，

$$
\boxed{
0\le
A_2(H)-\log C_{\mathbb Z}(\eta)
\le
\frac{\vartheta(H^{1/3})}{H-1},
}
\tag{19}
$$

其中

$$
\vartheta(x)=\sum_{p\le x}\log p.
$$

特别地，

$$
\boxed{
A_2(H)-\log C_{\mathbb Z}(\eta)
\le
\frac{H^{1/3}\log H}{3(H-1)}.
}
\tag{20}
$$

### 证明

令

$$
\delta_p=c_p(H)-m_p(H)\ge0.
$$

取连续最优指数上方的整数候选

$$
a_p^+=\lceil\beta_p\rceil.
$$

由于 $h_p$ 递增，

$$
\begin{aligned}
\delta_p
&\le
g_{p,H}(u_p^*)
-g_{p,H}(a_p^+\log p)\\
&=
h_p(u_p^*)-h_p(a_p^+\log p)
+\eta(a_p^+\log p-u_p^*)\\
&\le
\eta(a_p^+-\beta_p)\log p\\
&\le
\eta\log p.
\end{aligned}
$$

对 $X<p<H$，三候选比较已经精确，所以误差只来自 $p\le X$：

$$
A_2(H)-\log C_{\mathbb Z}(\eta)
=
\sum_{p\le X}\delta_p
\le
\eta\vartheta(X).
$$

再用

$$
\vartheta(X)\le X\log X
$$

即得式 $(20)$。证毕。

<!-- editorial-note:start empty-sums-asymptotics -->
**【编者局部说明：全整数优化与误差端点】** 式 (17) 使用完整的 $m_p(H)$；每个活动素数独立选一个最大指数后，有限乘积给出同一个实际最大整数，非活动素数都取零。式 (18) 仅松弛 $p\le X$ 的部分，且 $X=H^{1/3}<H$。若 $X<2$，这些小素数和为空，约定为零。对 $X>1$，每项 $\log p\le\log X$ 且素数个数至多为 $X$，得到所用的初等界。式 (21) 的大小阶与小 $o$ 均指 $H\to\infty$，没有使用 RH，也没有给出中心表达式的正号。
<!-- editorial-note:end empty-sums-asymptotics -->

### 这条定理的意义

我们已经把无限整数集合上的价格最大化，压缩为：

$$
\boxed{
\text{小素数连续部分}
+
\text{较大素数的三个整数候选}
+
\text{明确的误差区间}.
}
$$

而且误差满足

$$
\frac{H^{1/3}\log H}{3(H-1)}
=
O(H^{-2/3}\log H)
=
o\left(\frac1{\sqrt{H\log H}}\right).
\tag{21}
$$

这个估计只用了初等界 $\vartheta(X)\le X\log X$，没有使用 RH。

---

## 七、把上述结果变成 Robin 的严格证书

令

$$
T=\log n,\qquad
f(T)=\gamma+\log\log T.
$$

于是

$$
-\log R(n)=f(\log n)-\log\mathcal Z(n).
$$

定义

$$
\boxed{
Q_2(n;H)
=
f(\log n)-\eta\log n-A_2(H).
}
\tag{22}
$$

由全局价格最优性，

$$
\log\mathcal Z(n)
\le
\eta\log n+\log C_{\mathbb Z}(\eta)
\le
\eta\log n+A_2(H).
$$

所以

$$
\boxed{
-\log R(n)\ge Q_2(n;H).
}
\tag{23}
$$

因此得到一个真正的充分条件：

$$
\boxed{
Q_2(n;H)>0
\Longrightarrow
R(n)<1.
}
\tag{24}
$$

更精确地，定义

$$
E(n;\eta)
=
\log C_{\mathbb Z}(\eta)
-
\bigl(\log\mathcal Z(n)-\eta\log n\bigr)
\ge0,
$$

以及

$$
\epsilon_2(H)
=
A_2(H)-\log C_{\mathbb Z}(\eta).
$$

则

$$
\boxed{
-\log R(n)
=
Q_2(n;H)+\epsilon_2(H)+E(n;\eta),
}
\tag{25}
$$

其中

$$
0\le\epsilon_2(H)
\le\frac{\vartheta(H^{1/3})}{H-1}.
$$

<!-- editorial-note:start extremal-log-domain -->
**【编者局部说明：极值整数的对数范围】** 全局价格最大值允许在任意正整数上取得；式 (26) 还要求所选极值整数 $N\ge3$，使 $\log R(N)$ 与 $Q_2(N;H)$ 有定义。作为 Robin 目标的证书使用时进一步取 $N>5040$。式 (25) 中两个非负修正均对应正在检验的同一个 $n$ 与同一个价格。
<!-- editorial-note:end extremal-log-domain -->

如果 $N$ 本身就是该价格下的整数最大点，那么 $E(N;\eta)=0$，从而

$$
\boxed{
Q_2(N;H)
\le
-\log R(N)
\le
Q_2(N;H)+
\frac{\vartheta(H^{1/3})}{H-1}.
}
\tag{26}
$$

这给出了价格极值整数的 Robin 余量区间。

### 选择与 Robin 曲线匹配的价格

<!-- editorial-note:start matched-price-domain -->
**【编者局部说明：匹配价格的范围】** 以下导数要求 $T>1$；要继续使用前文的 $H>2$，还须 $T\log T>1$。Robin 目标范围 $n>5040$ 同时满足这两个条件。式 (27) 是 $T\to\infty$ 的渐近式，此时 $H\sim T\log T$、$\log H\sim\log T$；近似误差的衰减不决定有符号中心项。
<!-- editorial-note:end matched-price-domain -->

可以取

$$
\eta=f'(T)=\frac1{T\log T},
\qquad
H=1+T\log T.
$$

此时

$$
\epsilon_2(H)
=
O\left(T^{-2/3}(\log T)^{1/3}\right)
=
o\left(\frac1{\sqrt T\log T}\right).
\tag{27}
$$

因此，三候选近似的误差已经被控制到很小的尺度。**剩下要证明的是中心表达式的有符号估计；误差小本身不决定中心值为正。**

---

## 八、二元局部观察还可以高精度保留完整整数损失

另一条推进直接使用你说的“二元读出＋关系＋归一化”。

<!-- editorial-note:start same-integer-envelope -->
**【编者局部说明：继承量的独立定义】** 为在本文内明确“上一轮”分解，设同一实际整数的指数为 $a_p=v_p(n)$，并置

$$
\mathcal T_0(K):=\sum_{p<K}\log\frac Kp,\qquad
B(K):=\sum_{p<K}\log\frac{1-1/K}{1-1/p},\qquad
\eta_K:=\frac1{K-1}.
$$

对 $n\ge2$，方程 $\mathcal T_0(K)=\log n$ 唯一确定 $K>2$：$\mathcal T_0$ 在 $K=2$ 为零，在 $(2,\infty)$ 连续严格递增且无界；穿过素数时新增项从零开始，区间内导数为 $\#\{p:p<K\}/K>0$。在含 $\log R$ 的范围 $n\ge3$，定义

$$
G(K):=B(K)-\gamma-\log\log\mathcal T_0(K),\qquad
\Delta_K(n):=B(K)-\log\mathcal Z(n),
$$

$$
U_K(n):=\sum_{\substack{p\ge K\\p\mid n}}
\bigl[\eta_K a_p\log p-\log S_p(a_p)\bigr].
$$

这里 $K$ 始终由该 $n$ 的总尺度决定，$G$ 只在 $\mathcal T_0(K)>1$ 时使用；它与任意独立选择的价格 $H$ 不可混同。尾和保留同一实际整数的全部大素因子，包括等号 $p=K$ 的可能情形；非因子贡献为零。
<!-- editorial-note:end same-integer-envelope -->

沿用上一轮的精确分解。对实际 $n$，令 $K$ 满足

$$
\log n=\sum_{p<K}\log\frac Kp.
$$

设

$$
r=\frac1K,\qquad
s_p=p^{-v_p(n)-1},
\qquad
L_p=\operatorname{kl}(r\Vert s_p),
$$

其中

$$
\operatorname{kl}(r\Vert s)
=
r\log\frac rs+(1-r)\log\frac{1-r}{1-s}.
$$

上一轮已经证明

$$
\boxed{
\log R(n)=G(K)-\Delta_K(n),
}
$$

以及

$$
\boxed{
\Delta_K(n)
=
\frac K{K-1}\sum_{p<K}L_p+U_K(n),
\qquad U_K(n)\ge0.
}
\tag{28}
$$

<!-- editorial-note:start same-integer-decomposition -->
**【编者局部说明：分解与非负尾项的核对】** 以第四节的 $h_p$ 记 $g_{p,K}(u)=h_p(u)-\eta_Ku$。Euler 分解在同一整数上给出 $\log\mathcal Z(n)=\sum_{p\mid n}h_p(a_p\log p)$ 及 $\log n=\sum_{p\mid n}a_p\log p$。对 $p<K$，连续极大点 $u_p^*=\log(K/p)$ 对应 $r=1/K$，而实际点对应 $s_p=e^{-a_p\log p}/p$，故

$$
\begin{aligned}
g_{p,K}(u_p^*)-g_{p,K}(a_p\log p)
&=\log\frac{1-r}{1-s_p}
  +\frac1{K-1}\log\frac r{s_p}\\
&=\frac K{K-1}\operatorname{kl}(r\Vert s_p).
\end{aligned}
$$

对 $p\ge K$，$g_{p,K}(0)=0$ 且在非负半轴上非增，故尾和 $U_K(n)$ 的每项均非负。再由尺度相等，

$$
\begin{aligned}
B(K)-\eta_K\mathcal T_0(K)
&=\sum_{p<K}g_{p,K}(u_p^*),\\
\Delta_K(n)
&=\frac K{K-1}\sum_{p<K}L_p+U_K(n),\\
G(K)-\Delta_K(n)
&=\log\mathcal Z(n)-\gamma-\log\log\log n
=\log R(n).
\end{aligned}
$$

这说明式 (28) 包含非活动的实际大素数，并没有删除它们来取得非负性。每个 $r,s_p$ 均严格在零与一之间，$L_p\ge0$ 是二元 KL 的非负性；例如将 $-\log t\ge1-t$ 分别用于两项即可得到。
<!-- editorial-note:end same-integer-decomposition -->

这里全部 $s_p$ 来自同一个整数 $n$，而 $K$ 由同一个总尺度确定。

### 定义 4：两个素数方向组成一个三结果观察

对一组有序素数，令其参数为 $s_1,s_2$。只记录三个结果：

1. 第一个二元坐标出现 $1$；
2. 第一个为 $0$，第二个出现 $1$；
3. 两个都为 $0$。

对应两个归一化向量：

$$
P_B=
\bigl(r,(1-r)r,(1-r)^2\bigr),
$$

$$
Q_B=
\bigl(s_1,(1-s_1)s_2,(1-s_1)(1-s_2)\bigr).
\tag{29}
$$

两者都是严格正的三结果概率律，可以放到三个稳定顶点的一个指定混合子族中。

<!-- editorial-note:start auxiliary-kl-carrier -->
**【编者局部说明：辅助概率载体与散度】** 定义 4 可在两个独立 Bernoulli 坐标的辅助乘积律上理解：参考参数为 $(r,r)$，比较参数为 $(s_1,s_2)$，再按所列三种事件合并；这些参数全部取自上述同一整数与同一 $K$。这里独立性是辅助载体的定义，不是声称实际素数事件独立。对严格正的有限概率向量，$D(P\Vert Q):=\sum_iP_i\log(P_i/Q_i)$。若三种结果依次放在模式 $[2],[5],[3]$，其五模式权重按 $[null],[2],[3],[5],[25]$ 排序为 $(0,P_1,P_3,P_2,0)$，轴均值为 $(P_1,P_2,P_3)$；这是指定子族及指定次序，不能消除任意五模式律的联合纤维。
<!-- editorial-note:end auxiliary-kl-carrier -->

### 定理 8：三结果观察具有精确关系损失

令

$$
I_B=D(P_B\Vert Q_B).
$$

则

$$
\boxed{
I_B=L_1+(1-r)L_2.
}
\tag{30}
$$

**证明。**

第一层区分“第一个为 $1$”与“第一个为 $0$”，贡献 $L_1$。

只有进入第二条分支才读取第二个坐标；参考律进入该分支的概率为 $1-r$，其条件损失为 $L_2$。由对数比的链式分解，得到式 $(30)$。也可以直接展开三项验证。证毕。

若每组将较大的局部损失放在第一位，则

$$
I_B
=
L_1+L_2-r\min(L_1,L_2)
\ge
\left(1-\frac1{2K}\right)(L_1+L_2).
$$

<!-- editorial-note:start singleton-convention -->
**【编者局部说明：配对与单点约定】** 每对先放较大的 $L_p$；式 (30) 的损失是 $r\min(L_1,L_2)$，至多为 $r(L_1+L_2)/2$。若留有单点组 $B=\{p\}$，定义 $I_B:=L_p$，即保留该二元观察的完整散度。各组不重叠且覆盖全部 $p<K$，所以可以直接求和得到式 (31)。记该总损失和为 $S_L=\sum_{p<K}L_p$，观察和为 $S_I=\sum_BI_B$，则 $S_I\le S_L\le2KS_I/(2K-1)$。乘以 $K/(K-1)$ 并只加一次同一个 $U_K(n)$，就是式 (32)，从而得到 (33)–(34)。
<!-- editorial-note:end singleton-convention -->

把所有 $p<K$ 分成两两一组，必要时留一个单点组，得到

$$
\boxed{
\left(1-\frac1{2K}\right)
\sum_{p<K}L_p
\le
\sum_B I_B
\le
\sum_{p<K}L_p.
}
\tag{31}
$$

这是一条统一的保真界，没有额外的素数个数因子。

### 推论：三轴局部观察给出很窄的 Robin 判定区间

令

$$
J_K(n)=\frac K{K-1}\sum_B I_B,
\qquad
F_K(n)=J_K(n)+U_K(n).
$$

则

$$
\boxed{
F_K(n)
\le
\Delta_K(n)
\le
F_K(n)+\frac{J_K(n)}{2K-1}.
}
\tag{32}
$$

所以

$$
\boxed{
G(K)-F_K(n)-\frac{J_K(n)}{2K-1}
\le
\log R(n)
\le
G(K)-F_K(n).
}
\tag{33}
$$

特别地，

$$
\boxed{
F_K(n)>G(K)
\Longrightarrow
R(n)<1.
}
\tag{34}
$$

这给出了一个明确答案：**二元局部读出确实可以递归组织全素数关系，而且能够证明它保留了多少与 Robin 相关的信息。**

上述概率律是为算术证明定义的辅助载体。将三结果映射到三个稳定纯模式时，明确选择空窗与对角模式权重为零；在这个选定子族中，三个轴均值完整确定三结果律。项目中任意五模式律的联合参数仍按其原来的纤维公式处理。[项目基础公式文档，§§2、4](https://github.com/the-omega-institute/trureturing/blob/98d92f3c4013a4c4fba51ece2d8cd9d84aafc7fa/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)

---

## 九、现在还差哪一步才能完成 RH？

这轮已经解决了几项具体问题：

| 问题 | 本轮结果 |
|---|---|
| 三元读出能否进入同一金字塔？ | 给出显式、稳定、可逆的嵌入 |
| 归一化是否必然丢失尺度？ | 乘法关系及一般非一次齐次关系可恢复尺度 |
| 三个候选是否遗漏高指数？ | 对 $p>H^{1/3}$，证明 $0,1,2$ 已经完备 |
| 连续化小素数带来多大误差？ | 至多 $\vartheta(H^{1/3})/(H-1)$ |
| 二元局部观察会丢失多少整数损失？ | 排序配对后至多损失 $1/(2K)$ 的比例 |
| 能否直接得到 Robin 证书？ | 得到 $Q_2>0$ 和 $F_K>G(K)$ 两类严格充分条件 |

剩下的核心是对**全部实际算术配置**证明这些证书足够强。

在价格路线中，需要控制

$$
\boxed{
Q_2(n;H)
=
\gamma+\log\log\log n
-\frac{\log n}{H-1}
-A_2(H)
}
$$

的符号，或者结合式 $(25)$ 的两个非负修正。

在关系损失路线中，需要证明

$$
\boxed{
\Delta_K(n)>G(K)
\qquad(n>5040),
}
$$

并可利用式 $(32)$ 将其转化为三轴局部观察的精确估计。

**因此，你提出的通用表示原则已经可以承担真实的数学工作：关系恢复尺度，归一化保留候选，三轴局部观察保留联合损失，递归组合覆盖全部素数。** 本轮仍未证明 RH 的全称严格不等式；但现在需要攻克的已经是明确的有符号数论估计，而不是“三轴能否容纳这些运算与关系”这一表示问题。
