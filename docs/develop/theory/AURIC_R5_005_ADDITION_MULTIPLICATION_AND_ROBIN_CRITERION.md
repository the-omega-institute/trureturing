# 加法、乘法与 Robin 判据

> 来源：用户于 2026-11-06（Asia/Singapore）在本会话提供的 AURIC R5-005 LaTeX 研究工作稿；原稿未另署作者或模型。本文为参考输入，Lean 是仓库的数学真源；本次仅转换 Markdown，未作形式化认证。正文中的固定快照、项目核读叙述与理论结论均保留原稿口径；原生 TikZ 数值图转换为 Mermaid 曲线，并附原图全部十个近似数据点、分区标记和图注。

<span class="sans-serif">AURIC / R5-005</span>

二元关系与三元提升方案的正确性检验

定义、反例、局部定理与完整保留的全局缺口

2026年11月5日（UTC）

## 摘要

把上一轮的“内部参考与隐藏关系组成二元，归一化后给三个实读数”落实到普通算术，所得结论是有条件的肯定：保留单位锚或总量、运算身份及共同素因子关系后，可以得到准确的加乘表示和 Robin 缺口递推。纯态平方恒等式确实能推出二元算术的 AM–GM 不等式；但同一恒等式对 Robin 缺口的正负两侧都成立，不能代替有向比较。

本文先给出完整整数的有界归一编码及其加乘公式，再说明矩阵相加、权重相加、振幅相加和逐项相乘的区别。随后证明约数密度的共同素因子修正、Robin 的精确二元增量式，以及每个合法素数乘法步不必改善缺口的明确反例。

本轮直接证明一个局部定理：固定素数与其余因子后，绝对 Robin 缺口沿素数幂链至多先降后升一次，并有纯整数停止证书。因此每条无限链可化为有限检查。最后接回项目已有的全支撑余量分解、分层 Jensen 校正及七光滑数结论，精确指出尚未得到的统一估计。本轮未证明全整数 Robin 不等式，也未进行新的 Lean 编译。

**判定** 方案可以保持算术并组织证明；“归一化稳定，所以 Robin 缺口为正”的推论不成立。可保留的推进是准确递推、必要信息的反例检验，以及固定余因子链的有限检查定理。

项目固定版本：[the-omega-institute/trureturing，dev](https://github.com/the-omega-institute/trureturing/tree/e1a186b8a02e8f4e4ce3289b09d32c715cf68cde)。

提交：`e1a186b8a02e8f4e4ce3289b09d32c715cf68cde`；2026-11-05 16:06:32 UTC，亦即新加坡时间 2026-11-06 00:06:32。

本文的“证明”指下文给出的数学证明；引用 Lean 声明时仅报告已阅读的源码内容，不将源码阅读写成新的内核验证。

## 1　最简单的入口：和、积与有向差

本轮的目标是检验上一轮方案能否正确作用于已有的普通自然数加乘，而不是仅从五个角色的名称重新推出自然数系统。以下始终令 $\log=\ln$，并显式区分加法零元 $0$ 与乘法单位 $1$。

#### 定义 1.1：二元算术关系

对正整数 $a,b$，记

$$
S=a+b,\qquad P=ab,\qquad D=a-b.
$$

这里 $S$ 是总量，$P$ 是乘积关系，$D$ 是带顺序的差。

#### 定理 1.2：算术提升与可逆性

恒有

$$
\boxed{D^2+4P=S^2.}
\tag{1}
$$

保留 $S,D$ 后唯一恢复

$$
a=\frac{S+D}{2},\qquad b=\frac{S-D}{2}.
$$

反过来，整数 $S,D$ 满足 $S>|D|$ 且 $S\equiv D\pmod 2$ 时，这两个式子给出正整数。

**证明。**

展开 $(a+b)^2-(a-b)^2=4ab$ 得恒等式。恢复公式是两条一次方程的解；严格不等式给正性，同余条件给整性。

$\square$

若只给 $S,P$，二次方程 $x^2-Sx+P=0$ 给出无序根集 $\{a,b\}$，但有序接口还需 $D$ 的符号。取 $Q=2\sqrt P$，才得到 Euclidean 圆锥关系 $D^2+Q^2=S^2$；不能未经平方根变换就把 $P$ 当作正交长度。

#### 推论 1.3：一次真正的算术推论

由 $D^2\ge0$ 得

$$
(a+b)^2\ge4ab,\qquad \frac{a+b}{2}\ge\sqrt{ab},
$$

等号恰在 $a=b$ 时成立。

这说明平方恒等式可以证明恰当方向的不等式。它不能证明 $a\ge b$，因为交换两者仍保持同一恒等式。这一差别正是后面 Robin 检验的关键。

### 1.1　与上一轮三元读口的准确接法

#### 定义 1.4：权重提升

把 $a,b$ 作为权重，定义

$$
G(a,b)=
\begin{pmatrix}a&\sqrt{ab}\\ \sqrt{ab}&b\end{pmatrix}
=\binom{\sqrt a}{\sqrt b}
\begin{pmatrix}\sqrt a&\sqrt b\end{pmatrix}.
$$

它正半定、秩一且迹为 $S$。归一化后令

$$
x_1=\frac{2\sqrt{ab}}S,\qquad x_2=\frac{a-b}S,\qquad x_3=0.
$$

则 $x_1^2+x_2^2+x_3^2=1$。

这只使用球面的一个实半圆。若另取非零相位 $c=\sqrt{ab}\,e^{-i\theta}$，则产生横向旋转，但 $\theta$ 是另行保留的关系参数，不是两个正整数自动给出的新算术量。普通算术还选定单位、正序和运算，因而不能仅凭球面图像宣称全部算术具有任意三维旋转对称性。

沿用 R5-004 的读口次序，

$$
\frac{G}{\operatorname{Tr}G}
=\frac12\begin{pmatrix}1+x_2&x_1-i x_3\\x_1+i x_3&1-x_2\end{pmatrix}.
$$

$F[1],F[2],F[3]$ 对应这三个实读数；内部参考 $F[\mathrm{null}]$ 和带来源的未展关系 $F[1,3]$ 是生成、解释和继续更新此表的对象。五个角色不是五个独立实数，也不表示任意长的递归只需固定总信息量。

例如 $a=2,b=5$ 时，$S=7,P=10,D=-3$，有

$$
49=9+40,\qquad
(x_1,x_2,x_3)=\left(\frac{2\sqrt{10}}7,-\frac37,0\right).
$$

这里负号本来就是关系的一部分；把它改成正根会交换有序角色。

**白话对应。** 两个数放到一起，和给总量，积给共同关系，差给方向。三者确实受同一条平方关系约束。归一化后可以画成一个圆上的点，但“差朝哪边”和“总量是多少”仍要有明确记录。

## 2　内部单位锚可以保留完整加法与乘法

### 2.1　归一化不必丢失整数

若只把任意 $(a,b)$ 除以 $a+b$，共同缩放 $(a,b)\mapsto(\lambda a,\lambda b)$ 不改变读口，故一般会丢失尺度。不过，用户提出的“观察者也在整体中”允许把参考本身作为内部对象保留。选用明确的乘法单位 $1$，即可得到可逆编码。

#### 定义 2.1：内部单位归一编码

对 $n\in\mathbb N_0$，令

$$
q(n)=\frac{n}{1+n},\qquad
\mathcal Q=\left\{\frac n{1+n}:n\in\mathbb N_0\right\}.
$$

#### 定理 2.2：归一坐标中的完整加乘

映射 $q:\mathbb N_0\to\mathcal Q$ 为双射，逆为 $n=q/(1-q)$。 若 $x=q(a),y=q(b)$，定义

$$
\boxed{x\oplus y=\frac{x+y-2xy}{1-xy},\qquad
x\otimes y=\frac{xy}{1-x-y+2xy}.}
\tag{2}
$$

则

$$
q(a+b)=x\oplus y,\qquad q(ab)=x\otimes y.
$$

因此 $(\mathcal Q,\oplus,\otimes)$ 与自然数半环同构，其加法零元为 $0$，乘法单位为 $1/2$。

**证明。**

从 $x=n/(1+n)$ 直接解得逆。将 $a=x/(1-x)$、$b=y/(1-y)$ 分别代入 $q(a+b)$ 与 $q(ab)$，通分得到式 (2)。 在 $0\le x,y<1$ 上，$1-xy>0$，而 $1-x-y+2xy=(1-x)(1-y)+xy>0$，故公式有定义。 结合律、交换律和分配律由双射将原算术运算搬运过来。

$\square$

这给出一套完整、准确而简洁的递归。必须使用新坐标上的 $\oplus,\otimes$，不能未经计算就把它们替换为坐标的普通加法、普通乘法。单位 $1$ 可以是 $\Omega$ 内部明确指定的单位对象；它不需要是整体外部的观察者，但也不能与加法零元合并。

同一编码可写成上一轮的三元：

$$
G_n=\begin{pmatrix}1&\sqrt n\\\sqrt n&n\end{pmatrix},\quad
x_1=\frac{2\sqrt n}{1+n},\quad
x_2=\frac{1-n}{1+n},\quad x_3=0.
$$

有限 $n$ 时 $x_2>-1$，且 $n=(1-x_2)/(1+x_2)$。这说明“有限维读口”与“可以编码所有有限整数”并不矛盾。

### 2.2　有界坐标不等于统一有限精度

#### 命题 2.3：恢复精度随数值增长

$$
q(n+1)-q(n)=\frac1{(n+1)(n+2)},\qquad
\frac{d}{dq}\frac q{1-q}=\frac1{(1-q)^2}.
$$

在 $q=q(n)$ 处，后一导数为 $(n+1)^2$。

**证明。**

分别作差、求导即可。

$\square$

因此，整数全体可以放进一个有界坐标，但精确识别任意大整数需要不断提高精度或保留离散来源。坐标维数有限，不意味着全部递归信息、计算量或证明义务都有统一有限上界。

**白话对应。** 让数值一直和内部的“一个单位”比较，就能把所有整数放进一段有限区间，而且还能完整恢复加法和乘法。但大整数挤得越来越近；画面变紧凑，并不表示辨认这些数所需的信息也变少。

## 3　同一张正关系表中，哪些加乘真正封闭

### 3.1　权重、振幅和矩阵的类型不能交换

若 $a,b$ 是权重，使用的总量为 $a+b$；若把它们当成振幅而取向量 $(a,b)$，Gram 表的总量为 $a^2+b^2$。两种模型都可定义，但不能在证明中偷偷更换类型。

#### 命题 3.1：纯态提升通常不保持分量加法

通常有

$$
G(a+c,b+d)\ne G(a,b)+G(c,d).
$$

特别地，

$$
G(1,4)+G(4,1)=
\begin{pmatrix}5&4\\4&5\end{pmatrix},
\quad
G(5,5)=\begin{pmatrix}5&5\\5&5\end{pmatrix}.
$$

前者行列式为 $9$，后者为 $0$。

**证明。**

一般地，

$$
\det\bigl(G(a,b)+G(c,d)\bigr)
=(\sqrt{ad}-\sqrt{bc})^2.
$$

它仅在两对正权重具有相同比例时为零。分量相加后重新取 $\sqrt{(a+c)(b+d)}$，一般比原非对角元之和 $\sqrt{ab}+\sqrt{cd}$ 大，故重建纯态增加了新的相干关系。

$\square$

与此相应，振幅相加满足

$$
\|u+v\|^2=\|u\|^2+\|v\|^2+2\Re\langle u,v\rangle;
$$

只有交叉项为零时，才退化为权重直接相加。项目 V17 已把直和、张量积与相干和分别处理。[\[3\]](#ref-v17)

### 3.2　正表的加法与逐项乘法

#### 定理 3.2：二阶正关系表的闭合加乘

所有二阶复 Hermitian 正半定表在矩阵加法 $G+H$ 与逐项乘法 $G\circ H$ 下封闭，构成交换半环。零元为零表，逐项乘法单位为全 $1$ 表 $J$。对权重提升，

$$
G(a,b)\circ G(c,d)=G(ac,bd).
$$

**证明。**

正表之和显然仍正。设 $G=\bigl(\begin{smallmatrix}a&c\\\bar c&b\end{smallmatrix}\bigr)$、 $H=\bigl(\begin{smallmatrix}A&C\\\bar C&B\end{smallmatrix}\bigr)$。 其逐项积对角元非负，且

$$
\det(G\circ H)=aAbB-|cC|^2\ge0,
$$

因为 $|c|^2\le ab$、$|C|^2\le AB$。二阶 Hermitian 正性判据给出封闭性。代数律由逐项运算给出，最后一个公式直接代入验证。

$\square$

这里的乘法不是普通矩阵乘法。后者甚至不保持 Hermitian 性，例如

$$
\begin{pmatrix}1&1\\1&1\end{pmatrix}
\begin{pmatrix}1&0\\0&2\end{pmatrix} =
\begin{pmatrix}1&2\\1&2\end{pmatrix}.
$$

设 $G=S\rho,H=T\tau$ 均有正质量，Bloch 向量分别为 $x,y$，记 $z=x_2,w=y_2,\zeta=x_1+i x_3,\eta=y_1+i y_3$。 加法的完整更新为

$$
S'=S+T,\qquad x'=\frac{Sx+Ty}{S+T}.
$$

逐项乘法的更新为

$$
\boxed{S'=\frac{ST}{2}(1+zw),\quad
z'=\frac{z+w}{1+zw},\quad
\zeta'=\frac{\zeta\eta}{1+zw}.}
\tag{3}
$$

这些公式由表的对角元及左下元直接相乘得到。若 $S'=0$，输出为零表，不能再除以质量；非零输出时才使用归一坐标。

这套递归准确封闭，但加法通常进入球内部，不能要求每步都仍在纯态球面。其算术意义还依赖固定的接口基底；任意旋转并不自动保持逐项乘法。

### 3.3　加法相对乘法的隐藏对数项

对正数 $a,b$ 恒有

$$
\log(a+b)=\log a+\log b+\log\frac{a+b}{ab}.
$$

因此一个由正叶子、加法节点和乘法节点组成的二叉表达树，其根值满足

$$
\log(\text{根值})
=\sum_{\text{叶}}\log(\text{叶值})
+\sum_{\text{加法节点}}\log\frac{\text{左值}+\text{右值}}
{\text{左值}\,\text{右值}}.
$$

证明对树逐节点归纳：乘法节点直接加对数，加法节点补上所示项。隐藏项必须使用真实子树值，给它命名不等于已独立算出它。

项目 V19 的 $2,5,7$ 模式正体现这一点：$[2+5]$ 与 $[2][5]$ 分别为 $7,10$，隐藏对数系数为 $\log(7/10)$。若计数为 $(u,v,w,\kappa)$，则

$$
n=2^{u-\kappa}3^v5^{w-\kappa}7^\kappa,
\quad
\log n=u\log2+v\log3+w\log5-\kappa\log(10/7).
$$

把 $\kappa$ 丢掉，三项可见计数一般不能恢复原数。[\[4\]](#ref-v19)

**白话对应。** 加法、乘法都能进入这张关系表，但必须告诉表“这一步做了什么”。把权重相加、把振幅相加、把两张表相加，得到的关系不同。隐藏关系首先记录这些实际差别，不能用一个统一的“提升”名字把它们抹掉。

## 4　进入约数和：必须保存共同素因子的关系

#### 定义 4.1：约数密度

对正整数 $n$，定义

$$
\sigma(n)=\sum_{d\mid n}d,\qquad
Z(n)=\frac{\sigma(n)}n=\sum_{d\mid n}\frac1d.
$$

若 $n=\prod_{p\mid n}p^{a_p}$，则令

$$
S_p(a)=\sum_{j=0}^ap^{-j}
=\frac{1-p^{-a-1}}{1-p^{-1}},\qquad
Z(n)=\prod_{p\mid n}S_p(a_p).
$$

最后一个乘积式来自唯一素因数分解：每个约数恰对应一个指数选择。

### 4.1　共同素因子的精确修正

#### 定理 4.2：乘法的重叠修正

对正整数 $m,n$，

$$
Z(mn)=Z(m)Z(n)\,C(m,n),
$$

其中

$$
C(m,n)=
\prod_{p\mid\gcd(m,n)}
\frac{(1-p^{-1})(1-p^{-\alpha_p-\beta_p-1})}
{(1-p^{-\alpha_p-1})(1-p^{-\beta_p-1})},
\quad
\alpha_p=v_p(m),\ \beta_p=v_p(n).
$$

有 $0<C(m,n)\le1$，等号恰在 $\gcd(m,n)=1$ 时成立。

**证明。**

没有重叠的素数方向完全乘法化；重叠方向的修正正是 $S_p(\alpha+\beta)/(S_p(\alpha)S_p(\beta))$。 令 $q=1/p$，则该比值分母与分子的差为

$$
(1-q^{\alpha+1})(1-q^{\beta+1})
-(1-q)(1-q^{\alpha+\beta+1})
=q(1-q^\alpha)(1-q^\beta)>0.
$$

各因子严格为正且小于 $1$，给出结论。

$\square$

所以仅有一个“有重叠”标签还不够。甚至同一个最大公因数也不确定修正：

$$
C(2,2)=\frac79,\qquad C(2,4)=\frac57,\qquad
\gcd(2,2)=\gcd(2,4)=2.
$$

实际需要各共同素数在两端的阶数。另有准确恒等式

$$
Z(m)Z(n)=Z(\gcd(m,n))Z(\operatorname{lcm}(m,n)),
$$

因为每个素数方向的两阶数只被重新排列为最小值和最大值。

普通加法则无这样的乘积结构。例如

$$
\sigma(2+5)=8\ne9=\sigma(2)+\sigma(5),\qquad
\sigma(2\cdot5)=18=\sigma(2)\sigma(5),
$$

但 $\sigma(2^2)=7\ne9=\sigma(2)^2$。 加法差额 $\delta_+(a,b)=\sigma(a+b)-\sigma(a)-\sigma(b)$ 可以定义，也会变号：$(2,5)$ 给 $-1$，$(1,1)$ 给 $1$。把这个差额叫作“隐藏关系”，仍需另外计算或估计它。

#### 命题 4.3：加法需要单位部分的余数关系

对正整数 $a,b$ 与素数 $p$，乘法总有 $v_p(ab)=v_p(a)+v_p(b)$。对于加法，若 $v_p(a)\ne v_p(b)$，则

$$
v_p(a+b)=\min\{v_p(a),v_p(b)\}.
$$

若二者都等于 $\alpha$，写 $a=p^\alpha u,b=p^\alpha v$，则

$$
v_p(a+b)=\alpha+v_p(u+v).
$$

**证明。**

不同阶数时提出较小的 $p$ 幂，括号中一项被 $p$ 整除而另一项不被整除，所以括号是 $p$ 的单位。相同阶数时提出共同幂，剩余阶数就是 $u+v$ 的阶数。

$\square$

例如 $1+(p^k-1)=p^k$：两输入的 $p$ 阶数均为零，和的阶数却可以任意大。因此相同旧阶数后的新深度，需要实际单位余数的相消关系，不能只由旧阶数及归一化决定。

### 4.2　只保留归一读数时，递归会直接失去单值性

#### 定理 4.4：读口何时可以独立递推

给定来源状态集 $X$、读口 $\pi:X\to Y$ 和原始更新 $T:X\to X$。在实际读口集 $\pi(X)$ 上存在函数 $\bar T$，使 $\pi\circ T=\bar T\circ\pi$，当且仅当

$$
\pi(x)=\pi(x')\quad\Longrightarrow\quad
\pi(Tx)=\pi(Tx')\qquad(x,x'\in X).
$$

对二元操作，同样要求两端分别有相同旧读口时，输出有相同新读口；这就是投影的纤维等价关系与该操作相容。

**证明。**

若 $\bar T$ 存在，对相同读口施加同一函数必得相同结果。 反之定义 $\bar T(\pi(x))=\pi(Tx)$，所述条件恰好保证不依赖代表元。 二元操作的证明相同，对每个输入分别选择代表元即可。

$\square$

这把递归要求锁定为定义间的最小一致性约束：如果当前读口被宣称为下一步的全部状态，同一个读口就必须给出同一个后继读口。单位锚编码因可逆而满足此条件；下面的约数归一读口则不满足。

#### 命题 4.5：归一约数读口不足以更新

将状态压缩为 $(n,\sigma(n))/(n+\sigma(n))$，不能在该状态上定义适用于所有整数的单值“加 $1$”或“乘 $2$”更新。

**证明。**

完全数 $6,28$ 都给出 $(1/3,2/3)$。但

$$
Z(7)=\frac87\ne\frac{30}{29}=Z(29),
\qquad
Z(12)=\frac73\ne\frac{15}{7}=Z(56).
$$

同一旧读口在同一操作下有不同后继，故该压缩不是这两个操作的充分状态。

$\square$

这一障碍也发生在 Robin 的量词域内。令 $k=29^2=841$，则 $6k=5046>5040$、$28k=23548>5040$，并且

$$
Z(6k)=Z(28k)=2Z(k),
$$

却有

$$
Z(12k)=\tfrac73Z(k),\qquad Z(56k)=\tfrac{15}{7}Z(k).
$$

这是压缩递归的反例，不是 Robin 不等式的反例。恢复单位锚或总量可恢复整数；保留素因子阶数则直接支持局部素数更新。

### 4.3　平方读出可以实现约数和，但相位标签不能合并

项目 V19 和约数尺度几何文稿给出

$$
A_n(\boldsymbol\theta)=
\prod_{p\mid n}\left(\sum_{j=0}^{a_p}p^{-j/2}e^{ij\theta_p}\right).
$$

各素数方向使用独立的均匀圆周相位，字符正交性给出

$$
\int |A_n(\boldsymbol\theta)|^2\,dm(\boldsymbol\theta)=Z(n).
\tag{4}
$$

**证明。**

每个方向展开平方，积分将 $j\ne k$ 的项清除，仅留下 $\sum_jp^{-j}$。有限个独立方向的积分相乘即得。

$\square$

如果把全部 $\theta_p$ 合并为一个相位，就会保留总指数相同的跨素数交叉项。对 $n=6$，同相位平均变成

$$
1+\left(\frac1{\sqrt2}+\frac1{\sqrt3}\right)^2+\frac16
=2+\frac2{\sqrt6},
$$

而 $Z(6)=2$。[\[4\]](#ref-v19), [\[5\]](#ref-divisor)

所以平方表示是一个准确的数学接口，但必须保留正确的正交标签。它不把任意多个素数方向自动压缩成三个独立算术方向，也不凭平方形式单独推出量子力学。

## 5　Robin 判据：球面表达正确，正半球结论仍须证明

#### 定义 5.1：三个等价的缺口读数

对 $n>1$，令

$$
B(n)=e^\gamma\log\log n,\qquad
\Delta(n)=B(n)-Z(n),
$$

其中 $\gamma$ 为 Euler–Mascheroni 常数。 当整数 $n\ge3$ 时 $B(n)>0$，另定义

$$
R(n)=\frac{Z(n)}{B(n)},\qquad
\mu(n)=\log\frac{B(n)}{Z(n)}.
$$

经典 Robin 定理是

$$
\boxed{\mathrm{RH}\iff
\forall n\in\mathbb N,\ n>5040:\quad
\Delta(n)>0.}
\tag{5}
$$

在此域内，也等价于 $R(n)<1$ 或 $\mu(n)>0$。这里引用的是既有定理，不是本轮从归一化推出的事实。[\[1\]](#ref-lagarias), [\[2\]](#ref-choie)

### 5.1　正确编码与循环论证的分界

记 $A=B(n)>0,C=Z(n)>0$，构造

$$
G_{\rm enc}(n)=
\begin{pmatrix}A&\sqrt{AC}\\\sqrt{AC}&C\end{pmatrix}.
$$

则

$$
x_1=\frac{2\sqrt{AC}}{A+C},\qquad
z=\frac{A-C}{A+C},\qquad x_1^2+z^2=1.
$$

Robin 恰好是 $z>0$。但对 $A>C,A=C,A<C$，此表都正半定且秩一。球面恒等式只给 $z^2$，不确定 $z$ 的符号。

#### 命题 5.2：正根分支不能代替有向比较

$$
+\sqrt{1-x_1^2}=\frac{|A-C|}{A+C}.
$$

因此直接令 $F[2]$ 等于这一正根，并再把它解释为原有向缺口，会丢掉需要证明的符号。

**证明。**

平方恒等式给出绝对值；交换 $A,C$ 保持 $x_1$ 与正表条件不变，却使有向差变号。

$\square$

还有一种更隐蔽的循环：若定义

$$
M_n=\begin{pmatrix}A&C\\C&C\end{pmatrix},
\qquad \det M_n=C(A-C),
$$

则 $M_n\succeq0$ 恰等价于 $A\ge C$，而正定恰等价于 $A>C$。 要用此表证明 Robin，必须独立构造出其正定性；仅称它为“关系 Gram 表”已经把待证不等式放进了前提。

### 5.2　5040 是被排除的越界点，不是等号点

下表的约数密度是精确值，缺口小数只是便于阅读的近似值。相应严格符号已见项目约数尺度几何文稿第 7 节的级数界。[\[5\]](#ref-divisor)

|     $n$ | $Z(n)$（精确） | $B(n)$（近似） | $\Delta(n)$（近似） |
|----------:|:----------------:|:----------------:|:---------------------:|
|  $5040$ |   $403/105$    | $3.816877288$  |   $-0.021217950$    |
| $10080$ |    $39/10$     | $3.956103032$  |    $0.056103032$    |
| $55440$ |   $1612/385$   | $4.258323018$  |    $0.071310031$    |

$5040=2^4 3^2 5\,7$ 本身不满足该严格不等式，故不可把它当作安全端点或几何等号来启动归纳。项目对 $5040$ 的资源最优定理也需要保留其准确目标；见第 10 节。

**白话对应。** 把“允许多少”与“实际多少”放进两栏，Robin 就是问前一栏是否更大。两栏无论谁大都能画在同一个圆上。圆说明两者怎样关联，却不会替我们选出胜的一边；选正平方根会恰好丢掉这个问题。

## 6　Robin 的精确二元递推，以及每步改善的反例

#### 定理 6.1：素数乘法的准确更新

设 $p$ 为素数，$n=p^a m>1$，其中 $a\ge0$、$p\nmid m$。则

$$
\sigma(pn)=p\sigma(n)+\sigma(m),\qquad
Z(pn)=Z(n)+\frac{\sigma(m)}{pn}.
\tag{6}
$$

从而

$$
\boxed{\Delta(pn)=\Delta(n)+T(n,p)-U(n,p),}
\tag{7}
$$

其中

$$
T(n,p)=e^\gamma\log\left(1+\frac{\log p}{\log n}\right)>0,\qquad
U(n,p)=\frac{\sigma(m)}{pn}>0.
$$

**证明。**

有限几何和给 $\sigma(p^{a+1})=p\sigma(p^a)+1$。 乘以 $\sigma(m)$，利用 $p\nmid m$，得到第一个式子；除以 $pn$ 得第二个。另一方面，

$$
B(pn)-B(n)
=e^\gamma\log\frac{\log n+\log p}{\log n}
=T(n,p).
$$

相减即得 (7)。

$\square$

现在可以不含歧义地实行一次二元归一：

$$
S=T+U,\qquad
x_1=\frac{2\sqrt{TU}}S,\quad
x_2=\frac{T-U}S,\quad x_3=0.
$$

于是本轮最简递推是

$$
\boxed{\Delta(pn)=\Delta(n)+Sx_2.}
\tag{8}
$$

内部参考需保留当前 $n$、操作 $p$、旧缺口及单位；未展关系需保留实际阶数 $a$、余因子 $m$ 及来源。三元是这次比较的读口，而不是替代全部来源。若删掉 $S$，就不能恢复缺口增量的大小；若删掉 $x_2$ 的方向，就不能恢复增量的正负。

#### 定理 6.2：每个素数步都改善缺口的想法不成立

对任意奇整数 $n>64$，都有

$$
\boxed{\Delta(2n)<\Delta(n).}
$$

**证明。**

此时 $a=0,m=n$，故 $U(n,2)=Z(n)/2\ge1/2$。 利用 $0<\gamma<1$、$e<3$、$\log(1+x)<x$，以及 $\log n>6\log2$，有

$$
T(n,2)
<\frac{3\log2}{\log n}<\frac12.
$$

所以 $T-U<0$，由定理 6.1 得结论。

$\square$

例如 $n=6561=3^8>5040$，数值上

$$
\Delta(6561)\approx2.371218174,\qquad
\Delta(13122)\approx1.756458719.
$$

两者仍为正，但乘 $2$ 后缺口下降。这反驳的是“局部每步变好”的证明策略，并不构成 Robin 反例。

普通加法 $n\mapsto n+1$ 也有恒等更新

$$
\Delta(n+1)-\Delta(n)
=e^\gamma\log\frac{\log(n+1)}{\log n}
-\bigl(Z(n+1)-Z(n)\bigr).
$$

不过 $n+1$ 的素数分解一般不能由 $n$ 的约数读口直接得到。加法是完整算术中合法的操作；是否能由当前压缩状态高效局部更新，是另外一个需要证明的性质。

**白话对应。** 每乘进一个素数，有两笔增量在竞争：Robin 门槛涨了多少，约数密度涨了多少。我们的二元方案恰好能记录这场竞争。它能告诉我们怎样算下一步，却不能承诺每一步都更安全；旧缺口必须一起带下去。

## 7　一个可以完整保留的推进：每条固定余因子链只有一个谷底

### 7.1　单谷定理

固定素数 $p$ 和正整数 $m$，要求 $p\nmid m$。设

$$
\Delta_a=e^\gamma\log\log(p^a m)
-Z(m)\sum_{j=0}^{a}p^{-j},\qquad a\ge1.
$$

这就是实际整数 $p^a m$ 的绝对 Robin 缺口。定义

$$
t=\frac{\log m}{\log p}\ge0,\qquad
H_a=p^{a+1}\log\left(1+\frac1{a+t}\right).
$$

#### 定理 7.1：固定余因子的单谷性质

$H_a$ 在 $a\ge1$ 上严格增加且趋于无穷，并且

$$
\boxed{\Delta_{a+1}-\Delta_a
=p^{-a-1}\bigl(e^\gamma H_a-Z(m)\bigr).}
\tag{9}
$$

因此差分至多一次由负转正：$\Delta_a$ 先下降后上升，允许开头即上升，或最低处有两个相邻等值点。

**证明。**

式 (9) 由定理 6.1 直接代入得到。 令 $s=a+t\ge1$。计算

$$
s(s+2)^2-(s+1)^3=s^2+s-1>0,
$$

故

$$
2\log\frac{s+2}{s+1}>
\log\frac{s+1}{s}.
$$

由于 $p\ge2$，乘上相应的 $p^{a+1}$ 得 $H_{a+1}>H_a$。 此外，对于 $s>0$，

$$
\log\left(1+\frac1s\right)
=\int_s^{s+1}\frac{dx}{x}>\frac1{s+1}.
$$

所以

$$
H_a>\frac{p^{a+1}}{a+t+1}\longrightarrow\infty.
$$

式 (9) 的符号因而由严格增加、最终为正的序列 $e^\gamma H_a-Z(m)$ 决定。它至多取一次零，且只能先负后正，给出结论。

$\square$

这里证明的是**差分符号** 的单次转变，不是差分数值本身严格增加。因为式 (9) 前面还有衰减因子 $p^{-a-1}$，不应据此宣称整个序列离散凸。

### 7.2　只用整数比较的停止证书

#### 定理 7.2：无限素数幂链的有限检查

令

$$
A=\min\{a\ge1:p^a m>5040\},\qquad
u=\min\{j\ge0:p^j\ge m\}.
$$

选择任意 $B\ge A$ 满足纯整数不等式

$$
\boxed{m p^{B+1}\ge \sigma(m)(B+u+1).}
\tag{10}
$$

这样的 $B$ 必存在，并且

$$
\boxed{
\bigl(\forall a\ge A,\ \Delta_a>0\bigr)
\iff
\bigl(\forall a\in\{A,\ldots,B\},\ \Delta_a>0\bigr).
}
\tag{11}
$$

**证明。**

固定 $m,p,u$ 后，式 (10) 左边指数增长，右边线性增长，因此最终成立。由定义 $t\le u$，再用 $e^\gamma>1$ 和前一证明的严格积分下界，

$$
e^\gamma H_B > \frac{p^{B+1}}{B+t+1}
\ge\frac{p^{B+1}}{B+u+1}
\ge\frac{\sigma(m)}m=Z(m).
$$

所以 $\Delta_{B+1}>\Delta_B$。由 $H_a$ 严格增加，此后所有差分都严格为正。因此有限段全部为正即推出整个后续段为正；反向蕴含显然。

$\square$

如果 $m>5040$，还希望连 $a=0$ 一起覆盖，可把该起点另作一次检查。上述定理不依赖 $a=0$ 的差分比较。

停止证书只定位了有限检查范围；有限段的缺口正性仍需严格界，而不是仅凭浮点小数。也不能把“每个 $m$ 都有一个有限上限 $B(m)$”换成“所有 $m$ 的检查已经完成”。

### 7.3　以 5040 所在链作具体检验

取 $p=2,m=315=3^2\cdot5\cdot7$，则

$$
\sigma(315)=624,\qquad u=9,\qquad A=5.
$$

因为 $2^4\cdot315=5040$ 被排除，域中首点是 $10080$。 取 $B=5$，有

$$
315\cdot2^6=20160\ge624(5+9+1)=9360.
$$

因此从 $10080$ 的一个严格正性检查即可推出

$$
\forall a\ge5:\quad \Delta(315\cdot2^a)>0.
$$

该起点正性已由项目的严格界及七光滑数结论供应。[\[5\]](#ref-divisor), [\[7\]](#ref-seven) 本例用于说明新证明的机制；这一族的安全性已有项目结果覆盖，不作为新增覆盖域宣称。

```mermaid
xychart-beta
    title "Δ(315·2^a)"
    x-axis "a" [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    y-axis "Δ(315·2^a)" -0.09 --> 0.63
    line [0.3474508334, 0.0341274918, -0.0484473483, -0.0212179501, 0.0561030322, 0.1542778074, 0.2591966109, 0.3642279267, 0.4664114156, 0.5645679254]
```

原图分界线为 $a=4.5$；左侧阴影区标记 $n\le5040$，右侧标记“$n>5040$：从 $a=5$ 起严格上升”；低点标记“谷底附近”。原图数据点如下（近似值）：

| $a$ | $\Delta(315\cdot2^a)$ |
|------:|:-----------------------:|
|     1 |      0.3474508334       |
|     2 |      0.0341274918       |
|     3 |      -0.0484473483      |
|     4 |      -0.0212179501      |
|     5 |      0.0561030322       |
|     6 |      0.1542778074       |
|     7 |      0.2591966109       |
|     8 |      0.3642279267       |
|     9 |      0.4664114156       |
|    10 |      0.5645679254       |

**图 1：** 固定余因子链的缺口示意。点值采用近似数，仅作图；单谷性质与停止证书来自解析证明，起点严格符号另有来源。

**白话对应。** 固定其余因子以后，继续加同一个素数的幂，新增约数密度衰减得足够快。门槛开始可能落后，但双方的比较次序至多翻转一次，所以缺口最多只有一个谷底。我们能算出一个整数停止条件：过了那里，整条尾链只会上升。真正还要解决的，是所有不同余因子的谷底是否都在零以上。

## 8　放回整体：关系的关系要保留哪些余量

### 8.1　全支撑 Robin 缺口的精确分解

对 $n\ge3$，记 $P=P^+(n)$ 为最大素因子，定义

$$
M(P)=\prod_{p\le P}(1-p^{-1})^{-1},\qquad
\varepsilon(P)=\log\frac{M(P)}{e^\gamma\log P},
$$

$$
D_{\rm miss}(n)=-\sum_{\substack{p\le P\\p\nmid n}}\log(1-p^{-1}),
\qquad
D_{\rm cap}(n)=-\sum_{p\mid n}\log(1-p^{-a_p-1}).
$$

#### 定理 8.1：全部实际关系上的余量恒等式

$$
\boxed{\mu(n)=D_{\rm miss}(n)+D_{\rm cap}(n)
+\log\frac{\log\log n}{\log P}-\varepsilon(P).}
\tag{12}
$$

**证明。**

Euler 因子给出

$$
\log Z(n)=\log M(P)-D_{\rm miss}(n)-D_{\rm cap}(n).
$$

将 $\log M(P)=\gamma+\log\log P+\varepsilon(P)$ 代入 $\mu(n)=\gamma+\log(\log\log n)-\log Z(n)$，整理即得。

$\square$

这是项目 V19 及约数尺度几何文稿已明确建立的全支撑分解。[\[4\]](#ref-v19), [\[5\]](#ref-divisor) 其中前两项非负，但尺度项 $\log((\log\log n)/\log P)$ 可正可负；也未预先假设 $\varepsilon(P)$ 的符号。 所以不能仅凭“两个损失都是正的”推出整个和为正。

这里所有量都来自**同一个实际整数**。最大素因子、缺失方向、指数深度与总尺度不能分别选择各自有利的值，再冒充一个共同可实现状态。 完整剩余目标就是

$$
\forall n>5040:\quad
D_{\rm miss}+D_{\rm cap}
+\log\frac{\log\log n}{\log P} > \varepsilon(P).
$$

这仍是一条需要严格数量控制的全局不等式。

### 8.2　二叉或三叉归一树可以精确记账

令

$$
t_p=(a_p+1)\log p>0,\qquad
\psi(t)=-\log(1-e^{-t}).
$$

有

$$
\psi''(t)=\frac{e^t}{(e^t-1)^2}>0,\qquad
D_{\rm cap}=\sum_{p\mid n}\psi(t_p).
$$

在实际素数叶子上建立任意有限分组树。节点 $v$ 覆盖 $r_v$ 个叶子，令 $\bar t_v$ 为这些叶子的算术平均。每个内部节点定义

$$
\mathcal J_v
=\sum_{\text{子节点 }c}r_c\psi(\bar t_c)
-r_v\psi(\bar t_v)\ge0.
$$

#### 定理 8.2：关系树的完整校正

$$
\boxed{D_{\rm cap}
=r_{\rm root}\psi(\bar t_{\rm root})
+\sum_{\text{内部节点 }v}\mathcal J_v.}
$$

**证明。**

子节点叶数之和为 $r_v$，其加权平均为 $\bar t_v$。 $\psi$ 的凸性给每个 $\mathcal J_v\ge0$。 将定义逐节点相加，所有非根内部节点的 $r_v\psi(\bar t_v)$ 正负抵消，只剩叶子和减去根项，移项即得。

$\square$

项目的分层损失文稿已有这一精确结构。[\[6\]](#ref-hier) 本轮方案可以在这里获得实际作用：二元或三元递归负责组织比较，隐藏记录保留每层的 $\mathcal J_v$。若只使用根节点给出的 Jensen 下界，舍去全部校正，便得到更弱的估计，不能把它当作完整损失。

#### 命题 8.3：根 Jensen 下界会漏掉固定正量

令 $n_r=p_1p_2\cdots p_r$ 为前 $r$ 个素数的乘积。则

$$
D_{\rm cap}(n_r)\ge\log(4/3)>0,
$$

而根均值下界

$$
J_r=-r\log(1-n_r^{-2/r})\longrightarrow0.
$$

**证明。**

素数 $2$ 的叶项已为 $-\log(1-2^{-2})=\log(4/3)$。 另一方面 $p_i\ge i$ 给

$$
\log n_r\ge\log(r!)\ge\int_1^r\log x\,dx=r\log r-r+1.
$$

记 $K_r=n_r^{2/r}$，则 $K_r\ge r^2/e^2$。由 $-\log(1-x)\le x/(1-x)$，对 $r>e$ 有

$$
0<J_r\le\frac r{K_r-1}
\le\frac{e^2r}{r^2-e^2}\longrightarrow0.
$$

$\square$

这正是一条按用户要求反推的检验：若将根 Jensen 下界当作完整截断损失，一块固定大小的真实正量便不会出现在所用下界中。失败发生在不等式替代，不能据此宣称精确根数据本身不可逆。事实上，若保留 $r$ 与精确均值，则

$$
\exp(r\bar t_{\rm root})=n\,\operatorname{rad}(n),
\qquad \operatorname{rad}(n)=\prod_{p\mid n}p.
$$

对右侧整数作唯一分解，每个正指数减去 $1$，仍可恢复 $n$。但这种精确解码需要重新展开算术结构；有界或少量读数能编码整数，并不等于它给出的简单下界足以证明 Robin。

### 8.3　不存在统一正的归一安全间隙

经典 Gronwall 定理给

$$
\limsup_{n\to\infty}\frac{\sigma(n)}{n\log\log n}=e^\gamma,
\qquad\text{即}\qquad \limsup_{n\to\infty}R(n)=1.
$$

此结果及 Robin 等价关系可见 Lagarias 的原论文。[\[1\]](#ref-lagarias) 因此存在整数子序列使 $R(n_k)\to1$，从而

$$
z(n_k)=\frac{1-R(n_k)}{1+R(n_k)}\longrightarrow0.
$$

所以不能期待某个固定 $\epsilon>0$ 对全部 $n>5040$ 都给出 $z(n)\ge\epsilon$。 即使最终全部严格为正，其归一差也可能任意接近零。全局证明必须能处理这种接近边界的情况。

**白话对应。** 把所有素数关系层层合起来是可行的，但证明中必须算上合并产生的校正。只用平均值给出的粗下界，会漏掉足以影响最终比较的量；这与精确平均值能否编码原整数是两件事。到了全体整数，安全余量还会任意接近零，所以“看起来稳定”无法替代精确的不等式。

## 9　更大几何结构：乘法上包络与 Robin 凹边界

三元球面适合表达一次二元比较；对于全部整数的联合估计，更直接的几何是对数平面。令

$$
x_n=\log n,\qquad y_n=\log Z(n),\qquad
\Phi(x)=\gamma+\log\log x,\quad x>1.
$$

则 Robin 等价于 $y_n<\Phi(x_n)$，且

$$
\Phi''(x)=-\frac{\log x+1}{x^2(\log x)^2}<0.
$$

因此 Robin 边界严格凹，弦在曲线下方，切线在曲线上方。

#### 定理 9.1：真实极值端点供应的区间证明

给定 $\eta>0$，若正整数 $u<v$ 都是

$$
\log Z(k)-\eta\log k,\qquad k\ge1
$$

的全局最大化点，则对每个 $u\le n\le v$，记

$$
\theta=\frac{\log n-\log u}{\log v-\log u},
$$

有

$$
\log Z(n)\le(1-\theta)\log Z(u)+\theta\log Z(v).
$$

若另有 $u>5040$ 且 $\mu(u),\mu(v)>0$，则区间内所有整数满足 Robin，并且

$$
\begin{aligned}
\mu(n)\ge{}&(1-\theta)\mu(u)+\theta\mu(v)\\
&+\Phi(\log n)-(1-\theta)\Phi(\log u)-\theta\Phi(\log v)>0.
\end{aligned}
$$

**证明。**

两端同为最大化点，故有常数 $c$ 使 $\log Z(u)=\eta\log u+c$、$\log Z(v)=\eta\log v+c$，而对全部 $n$， $\log Z(n)\le\eta\log n+c$。该直线就是端点弦，给出第一式。 再以凹性得到 $\Phi(\log n)\ge(1-\theta)\Phi(\log u)+\theta\Phi(\log v)$，相减即得。

$\square$

这与项目约数尺度几何第 11 节的区间桥梁一致，并明确给出何种乘法极值条件足以供应所需的全点弦上界。[\[5\]](#ref-divisor) 仅检查两个普通端点安全，不保证中间整数在弦下；证明位于切线下，也不保证位于 Robin 曲线下。全局使用此法，仍须证明所选区间覆盖所有目标整数及其端点安全性。

对任意固定有限素数集 $S$，另有一个简单的尾部控制：

$$
Z(n)<C_S:=\prod_{p\in S}(1-p^{-1})^{-1}
\quad(\operatorname{supp}(n)\subseteq S,\ n>1).
$$

因此当

$$
n\ge\exp\!\left(\exp(C_S/e^\gamma)\right)
$$

时，$B(n)\ge C_S>Z(n)$。每个固定支撑由此只剩有限危险区间。但任意整数允许不断加入新素数，不能把固定支撑结论直接升格为全支撑结论。

## 10　与项目当前进展的对照

本轮固定到提交 `e1a186b8`，避免把持续变化的分支当成不可复核来源。与 R5-004 固定提交相比，本轮检查到的相关更新没有供应全整数 Robin 的新证明。直接相关的加乘、Robin 及七光滑数来源在本轮最后一次版本更新中保持不变。

| 来源 | 本轮应保留的准确结论 |
|:---|:---|
| V17 加乘与平方几何 | 直和的平方范数相加，张量平方范数相乘，相干和另有交叉项；这些是明示结构下的结果。[\[3\]](#ref-v17) |
| V19 算术谱 | 五模式隐藏对数项、真正素数方向、独立相位平方平均以及全 Robin 余量已存在，不能把本轮重述视为新增证明。[\[4\]](#ref-v19) |
| 约数尺度几何 | 几何尺度、约数配置盒、独立相位平均都接到同一 $Z(n)$；5040 真正越界；全支撑严格余量仍是共同目标。[\[5\]](#ref-divisor) |
| 分层损失 | 根 Jensen 下界不足，逐层校正可精确恢复截断损失；这正是二元递归应保存的关系。[\[6\]](#ref-hier) |
| 七光滑数源码 | $\texttt{robin\_seven\_smooth}$ 声明：对所有 $a,b,c,d\in\mathbb N_0$，若 $n=2^a3^b5^c7^d>5040$，则 Robin 成立。这里没有指数上限，也不以 RH 为前提。[\[7\]](#ref-seven) |
| 5040 资源最优源码 | $\texttt{golden\_resource\_unique\_optimum}$ 给全部正整数上的 $Z(n)/n^{1/25}\le Z(5040)/5040^{1/25}$，等号恰在 $5040$。 这是固定价格的幂函数上支撑，不等于双对数 Robin 上界。[\[8\]](#ref-resource) |

最新量子相关追加把固定正二次效果、归一化、端点守恒和指定基底校准等前提接到对角性及既有核分类。正二次表示仍为其前件；该更新没有给出新的 Robin 全支撑数量界。[\[10\]](#ref-continuation)

CSA 的有理数商接口也已区分读出与来源，并给相应加乘读出定理；这是“归一化读出须与运算相容”的项目内实例。[\[9\]](#ref-rational) 以上 Lean 内容属于固定源码审阅，本轮没有重新编译它们。

本轮直接证明的固定余因子单谷与整数停止证书，适合标作本轮的局部引理。这里不作历史首创声明。它不同于固定价格 $\eta$ 下的素数边际收益递减：本轮比较的是随 $n$ 改变的实际 Robin 门槛。

## 11　本轮修正后的完整方案与最终判定

### 11.1　把候选写成定义间约束

若要继续把“五角色递归”作为算术研究方案，可以采用以下完整版本：

1.  **参考与对象明确。** 输入是同一整体内带单位、来源和运算标签的对象；普通加法零元与乘法单位分别保存。归一化需保留总量，或给出如 $q(n)$ 的内部单位锚。

2.  **二元表与三元严格对应。** 使用已明确构造的正关系表，并保留质量。球内、球面及正负半球分别对应不同条件；不把正平方根当作有向差的证明。

3.  **递推必须与实际运算相容。** 读口必须满足定理 4.4 的代表元无关性。对坐标加乘使用式 (2)；对表加乘使用定理 3.2；对约数更新保存共同素数阶数并使用式 (6)。不把来源合并、振幅相加与权重相加互换。

4.  **隐藏关系可被进一步展开并核对。** 未展记录承载真实重叠、有限截断、分层校正或操作历史；下一轮可将这些关系重新作为二元对象。递归不准丢掉会改变后继或目标符号的差额。

5.  **比较结论由独立估计供应。** Robin 每步使用 $\Delta_{\rm new}=\Delta_{\rm old}+Sx_2$；固定链用单谷定理及停止证书，全支撑用式 (12) 的严格共同估计。归一化恒等式本身不被当作目标正性。

这些约束把“如何表示”“如何运算”“如何证明”接在同一套对象上。它们允许内部参考，也保留参考的选择和类型。把所有定义写进 $\Omega$ 能明确相容关系；单靠“内生”一词不能替代唯一因子分解、正性、运算相容或全支撑估计的具体数学内容。

### 11.2　反向检验清单

| 删去的条件 | 已证明的后果 |
|:---|:---|
| 单位锚与总量都删去 | 共同缩放不可区分，普通算术值不能一般恢复。 |
| 把正表加法当纯态重建 | $G(1,4)+G(4,1)\ne G(5,5)$，凭空增加相干项。 |
| 删去共同素数阶数 | 同一归一约数读口无法单值更新乘 $2$。 |
| 用正平方根替代有向读数 | 得到绝对值，Robin 的待证方向被抹掉。 |
| 假定所有乘法步改善缺口 | 任意奇数 $n>64$ 都给 $\Delta(2n)<\Delta(n)$。 |
| 用根下界替代全部层间校正 | 原始截断损失有固定正下界，而根下界趋零。 |
| 要求统一正归一间隙 | 与 Gronwall 的 $R(n_k)\to1$ 子序列矛盾。 |

**最终判定：** 作为保持信息、产生准确递推和组织局部证明的方法，修正后的方案成立；作为“只凭归一化与三维稳定性就推出 Robin”的证明，方案不成立。固定余因子链现在有完整的有限归约定理；全体余因子的谷底正性或等价的全支撑联合余量，仍是明确保留的未完成部分。

**白话对应。** 两个数比较时，和保留总量，积保留共同关系，差保留方向；内部的一个单位让归一坐标仍能认出原来的数。进入 Robin 后，每乘进一个素数，都比较门槛的增加与约数密度的增加，再把有方向、有大小的结果加回旧缺口。固定其他因子，这个缺口最多先降后升一次，所以一条无限链能压成有限检查。继续递归是可行的，但各层产生的差额必须一起保留；要完成全体整数的证明，还需统一保证所有这些链的谷底都在零以上。

## 来源与参考

<a id="ref-lagarias"></a>

\[1\] Jeffrey C. Lagarias. *An Elementary Problem Equivalent to the Riemann Hypothesis*. [arXiv:math/0008177，v2](https://arxiv.org/pdf/math/0008177). Robin 等价关系及定理 2.2 的 Gronwall 结果。本文采用其定理陈述，不以数值检验代替全称证明。

<a id="ref-choie"></a>

\[2\] Y. Choie, N. Lichiardopol, P. Moree, P. Solé. *On Robin’s criterion for the Riemann hypothesis*. Journal de Théorie des Nombres de Bordeaux 19 (2007), 357–372. [原论文 PDF](https://www.numdam.org/article/JTNB_2007__19_2_357_0.pdf). Robin 判据、异常小整数及受限家族。

<a id="ref-v17"></a>

\[3\] 项目固定版本： [V17：加乘、对数与量子勾股几何](https://github.com/the-omega-institute/trureturing/blob/e1a186b8a02e8f4e4ce3289b09d32c715cf68cde/docs/develop/theory/AURIC_SUM_PRODUCT_LOGARITHMS_AND_QUANTUM_PYTHAGOREAN_GEOMETRY_V17.md)， 尤其第 2、8 节。直和、张量积、相干和及其前提。

<a id="ref-v19"></a>

\[4\] [V19：加乘、对数与算术谱](https://github.com/the-omega-institute/trureturing/blob/e1a186b8a02e8f4e4ce3289b09d32c715cf68cde/docs/develop/theory/AURIC_SUM_PRODUCT_LOGARITHMS_AND_ARITHMETIC_SPECTRA_V19.md)， 尤其第 2–4 节。隐藏对数项、算术素数、相位平均与 Robin 余量。

<a id="ref-divisor"></a>

\[5\] [FIB–Robin 约数尺度几何](https://github.com/the-omega-institute/trureturing/blob/e1a186b8a02e8f4e4ce3289b09d32c715cf68cde/docs/develop/theory/AURIC_FIB_ROBIN_DIVISOR_SCALE_GEOMETRY.md)， 尤其第 3–12 节。5040 的严格越界、素数乘法、全支撑余量及区间弦上界。

<a id="ref-hier"></a>

\[6\] [Robin 分层损失、连续包络与联合层补全](https://github.com/the-omega-institute/trureturing/blob/e1a186b8a02e8f4e4ce3289b09d32c715cf68cde/docs/develop/theory/AURIC_ROBIN_HIERARCHICAL_LOSS_CONTINUOUS_ENVELOPE_AND_JOINT_LAYER_COMPLETION.md)， 尤其定理 1、2。根 Jensen 下界的不足和层间校正的望远镜恒等式。

<a id="ref-seven"></a>

\[7\] [D5/S3/Arith/Robin/SevenSmooth.lean](https://github.com/the-omega-institute/trureturing/blob/e1a186b8a02e8f4e4ce3289b09d32c715cf68cde/D5/S3/Arith/Robin/SevenSmooth.lean)。 声明 `D5.S3.Arith.Robin.SevenSmooth.robin_seven_smooth`。 本轮阅读声明与证明源码，未重新编译。

<a id="ref-resource"></a>

\[8\] [GoldenResourceOptimalInteger.lean](https://github.com/the-omega-institute/trureturing/blob/e1a186b8a02e8f4e4ce3289b09d32c715cf68cde/D5/S3/Arith/GoldenResourceOptimalInteger.lean)。 声明 `golden_resource_unique_optimum`。 固定 $1/25$ 价格的全整数最优点；本轮未重新编译。

<a id="ref-rational"></a>

\[9\] [RichRational.lean](https://github.com/the-omega-institute/trureturing/blob/e1a186b8a02e8f4e4ce3289b09d32c715cf68cde/D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational.lean)； [RationalQuotient.lean](https://github.com/the-omega-institute/trureturing/blob/e1a186b8a02e8f4e4ce3289b09d32c715cf68cde/D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.lean)。 加乘读出、商结构与来源类型。此处仅报告源码结构。

<a id="ref-continuation"></a>

\[10\] [FIB 原子量子原则与相干重构，续卷 X](https://github.com/the-omega-institute/trureturing/blob/e1a186b8a02e8f4e4ce3289b09d32c715cf68cde/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_X.md)，第 16 节。 本轮固定提交的最新相关追加；其既有正效果前件与有限校准范围需完整保留。
