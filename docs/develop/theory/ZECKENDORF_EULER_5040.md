# 黄金分层算术观察理论

## Zeckendorf 规范化、观察纤维、信息预算与 Robin 临界界

### 摘要

本文构造一套以正整数为状态、以素数指数为坐标、以 Zeckendorf 表示为规范语言的算术观察理论。

理论的核心不是假定“黄金比例天然最优”，而是建立三个可以分别证明、再精确连接的结构：

$$
\boxed{
\text{规范表示}
\quad\longrightarrow\quad
\text{观察纤维}
\quad\longrightarrow\quad
\text{加权信息预算}.
}
$$

首先，证明每个正整数具有唯一的素数—Zeckendorf 表；黄金分辨率进一步将全部正整数划分为互不重叠的有限算术单元。其次，建立观察者、条件熵、碰撞逃逸率与隐藏算术权重之间的精确关系。再次，证明有限黄金窗口的配分函数趋近 ζ 函数，并区分指数深度与素数范围这两种观察资源。

在此基础上，将 Robin 判据翻译为黄金单元上的统一严格上界，并建立可逐单元使用的非渐近证书。作为完整实例，证明：

$$
\boxed{
\mathscr C_{5040}
=
\{5040,10080,15120,20160,30240,60480\},
}
$$

而且：

$$
\boxed{
\Delta(n)>0.0047
\qquad
\forall n\in\mathscr C_{5040}\setminus\{5040\},
}
$$

其中 \(\Delta\) 为下文定义的 Robin 对数余量。

最后，构造一个连续资源分配模型，将其与整数配置之间的差额分解为非负的相对熵之和，并明确指出：**局部规范化、零碰撞逃逸、有限最大熵和连续松弛最优性，都不能单独替代全局 Robin 不等式。**

本文不以 RH 的真假为假设。Robin、Mertens 与 Gronwall 定理作为注明来源的经典输入；其余主要构造与结论在正文中证明。

---

# 第一章　基本对象与逻辑层次

## 1.1 算术状态

记：

$$
\mathbb P=\{2,3,5,7,\ldots\},
\qquad
\mathbb N_+=\{1,2,3,\ldots\}.
$$

任意正整数唯一写为：

$$
n=\prod_{p\in\mathbb P}p^{a_p(n)},
$$

其中：

$$
a_p(n)=v_p(n)\in\mathbb N,
$$

且只有有限多个 \(a_p(n)\) 非零。

定义整数的对数规模：

$$
\boxed{
E(n)=\ln n=\sum_pa_p(n)\ln p.
}
$$

对复数 \(s\)，定义有限因数配分函数：

$$
\boxed{
Z_n(s)=\sum_{d\mid n}d^{-s}.
}
$$

在 \(s=1\) 时，简记：

$$
Z(n)=Z_n(1),
\qquad
W(n)=\ln Z(n).
$$

由于因数配对 \(d\leftrightarrow n/d\)：

$$
\boxed{
Z(n)=\sum_{d\mid n}\frac1d=\frac{\sigma(n)}n.
}
\tag{1.1}
$$

全文用 \(\ln\) 表示自然对数，用 \(\log_2\) 表示二进制对数；熵若不注明，均以自然对数为单位。

## 1.2 三种不同的问题

本理论区分：

**表示问题：** 能否唯一恢复一个整数？

**观察问题：** 一个读出遗漏了哪些状态差异？

**目标估计问题：** 遗漏的差异是否足以影响某个指定不等式？

这三者并不等价。一个观察者可以无法恢复完整状态，却仍足以证明某个性质；一个编码也可以完全可逆，却不提供关于 Robin 余量的新上界。

后文将分别建立相应定理，而不把三者统称为“信息完整”。

---

# 第二章　黄金语言与规范算术表示

## 定义 2.1　黄金权重与合法字串

令：

$$
G_0=1,\qquad G_1=2,\qquad
G_{L+2}=G_{L+1}+G_L.
$$

定义长度为 \(L\) 的合法语言：

$$
\mathcal W_L
=
\left\{
(b_0,\ldots,b_{L-1})\in\{0,1\}^L:
b_jb_{j+1}=0
\right\}.
$$

其中 \(\mathcal W_0\) 只含空字串。

定义数值映射：

$$
V_L(b)=\sum_{j=0}^{L-1}b_jG_j.
$$

## 定理 2.2　完整黄金窗口

对每个 \(L\ge0\)，数值映射给出双射：

$$
\boxed{
V_L:\mathcal W_L
\overset{\sim}{\longrightarrow}
\{0,1,\ldots,G_L-1\}.
}
\tag{2.1}
$$

特别地：

$$
|\mathcal W_L|=G_L.
$$

### 证明

当 \(L=0,1\) 时直接成立。

设结论对 \(L-1,L-2\) 成立。按最高位分类。

若 \(b_{L-1}=0\)，数值恰好覆盖：

$$
[0,G_{L-1}-1]\cap\mathbb Z.
$$

若 \(b_{L-1}=1\)，合法性强制 \(b_{L-2}=0\)，其余部分恰好覆盖：

$$
G_{L-1}+[0,G_{L-2}-1].
$$

第二部分就是：

$$
[G_{L-1},G_L-1]\cap\mathbb Z.
$$

两段互不相交，且并为所需完整区间。每段内部由归纳假设具有唯一表示，因此整体也是双射。证毕。

## 推论 2.3　Zeckendorf 唯一性

每个 \(a\in\mathbb N\) 都具有唯一的有限支撑表示：

$$
\boxed{
a=\sum_{j\ge0}b_jG_j,
\qquad
b_j\in\{0,1\},
\qquad
b_jb_{j+1}=0.
}
\tag{2.2}
$$

### 证明

由于 \(G_L\to\infty\)，任意 \(a\) 落入某个区间 \([0,G_L-1]\)。

定理 2.2 给出存在性。两个有限表示可以补零至同一长度，再由该定理得到唯一性。证毕。

这是经典 Zeckendorf 定理的有限窗口证明；mathlib 已有对应的规范表示与等价构造。([Lean社区][1])

---

## 定义 2.4　素数—黄金表

定义 \(\mathcal B\) 为所有数组：

$$
b=(b_{p,j})_{p\in\mathbb P,\ j\ge0}
$$

组成的集合，满足：

$$
b_{p,j}\in\{0,1\},
\qquad
b_{p,j}b_{p,j+1}=0,
$$

并且整张表只有有限多个非零元素。

令：

$$
a_p(b)=\sum_jb_{p,j}G_j,
$$

$$
N(b)=\prod_pp^{a_p(b)}.
$$

## 定理 2.5　规范算术双射

$$
\boxed{
N:\mathcal B\overset{\sim}{\longrightarrow}\mathbb N_+.
}
\tag{2.3}
$$

### 证明

任意整数首先具有唯一的素数指数族 \(a_p\)，再由推论 2.3 将每个指数唯一编码成一行。

反过来，有限支撑保证乘积为正整数。

若两张表解码相同，唯一素因数分解保证全部指数相同；Zeckendorf 唯一性保证全部行相同。证毕。

### 推论 2.6　乘法的规范实现

若 \(b,c\) 编码 \(m,n\)，则逐素数相加指数、再逐行规范化，得到 \(mn\) 的编码。

因为：

$$
v_p(mn)=v_p(m)+v_p(n).
$$

项目中的 `PrimeAxisEncoding.lean` 已包含这一双射及规范加法对应整数乘法的形式化结构。

**注意：因数关系不是逐位删除 \(1\)。**

例如：

$$
4=3+1,
\qquad
2=2.
$$

虽然 \(2\le4\)，指数 \(2\) 的黄金表示并不是指数 \(4\) 表示的位子集。因此，对应因数时必须比较指数数值，而不能直接比较数位包含关系。

---

# 第三章　黄金比例的分辨率与熵率

## 定理 3.1　离散增长与连续分辨率

有：

$$
\varphi^L\le G_L\le\varphi^{L+1},
\qquad
\varphi=\frac{1+\sqrt5}{2}.
$$

因而：

$$
\boxed{
\lim_{L\to\infty}\frac{\ln|\mathcal W_L|}{L}
=
\ln\varphi.
}
\tag{3.1}
$$

另外，对无限合法序列定义：

$$
x(b)=\sum_{j\ge0}b_j\varphi^{-(j+1)}.
$$

若 \(b,c\) 的前 \(L\) 位相同，则：

$$
\boxed{
|x(b)-x(c)|\le\varphi^{-L}.
}
\tag{3.2}
$$

### 证明

增长界由初值及恒等式：

$$
\varphi^{L+2}=\varphi^{L+1}+\varphi^L
$$

归纳得到。结合 \(|\mathcal W_L|=G_L\)，得到式（3.1）。

对连续读出，合法尾串的最大值由交替序列实现：

$$
\varphi^{-1}+\varphi^{-3}+\varphi^{-5}+\cdots
=
\frac{\varphi^{-1}}{1-\varphi^{-2}}
=1.
$$

共同前缀之后的尾部多出因子 \(\varphi^{-L}\)，故式（3.2）成立。证毕。

因此：

$$
\boxed{
\text{可区分的离散状态数}\asymp\varphi^L,
\qquad
\text{连续读出的误差}\lesssim\varphi^{-L}.
}
$$

这是本理论中连续与离散之间的明确联系。

不过，连续读出不自动唯一。例如：

$$
\varphi^{-1}
=
\varphi^{-2}+\varphi^{-4}+\varphi^{-6}+\cdots.
$$

因此，无限实数展开的唯一性需要额外的边界约定。

## 定理 3.2　合法语言的最大熵率

长度 \(L\) 的合法字串上，任意概率分布的熵不超过：

$$
\ln G_L.
$$

并且存在一个平稳合法过程，其熵率为：

$$
\boxed{\ln\varphi.}
$$

### 证明

有限集合上，熵不超过集合基数的对数，因此：

$$
H(B_0,\ldots,B_{L-1})\le\ln G_L.
$$

上界除以 \(L\) 后趋于 \(\ln\varphi\)。

为证明可达性，取转移矩阵：

$$
P=
\begin{pmatrix}
\varphi^{-1}&\varphi^{-2}\\
1&0
\end{pmatrix}.
$$

该链不允许 \(1\to1\)。令 \(t=\varphi^{-2}\)，其平稳分布为：

$$
\pi_0=\frac1{1+t},
\qquad
\pi_1=\frac{t}{1+t}.
$$

每一步的条件熵为：

$$
\begin{aligned}
h
&=
\pi_0
\left(
-\varphi^{-1}\ln\varphi^{-1}
-\varphi^{-2}\ln\varphi^{-2}
\right)\\
&=
\frac{\varphi^{-1}+2\varphi^{-2}}{1+\varphi^{-2}}\ln\varphi\\
&=\ln\varphi.
\end{aligned}
$$

所以熵率达到上界。证毕。

这里最大化的是**合法字串过程的熵率**，不是某个整数的因数熵，也不是 Robin 比值。

---

# 第四章　黄金算术观察者与有限单元

## 定义 4.1　指数层级

对 \(a\ge0\)，定义唯一整数 \(\lambda(a)\)，满足：

$$
G_{\lambda(a)}
\le a+1
<
G_{\lambda(a)+1}.
$$

再定义：

$$
b(a)=G_{\lambda(a)}-1,
$$

$$
r(a)=a-b(a).
$$

记层宽为：

$$
w_L=G_{L+1}-G_L.
$$

于是：

$$
0\le r(a)<w_{\lambda(a)}.
$$

## 定义 4.2　黄金观察映射

对正整数 \(n\)，定义：

$$
\boxed{
\mathcal G(n)
=
\prod_pp^{b(a_p(n))}.
}
\tag{4.1}
$$

称满足：

$$
\mathcal G(m)=m
$$

的整数为**黄金满窗整数**，其集合记为 \(\mathscr M\)。

这些整数恰好具有形式：

$$
m=\prod_pp^{G_{L_p}-1}.
$$

“黄金满窗”是本文定义的术语，指每个因数指数区间恰好对应一个完整合法语言。

## 定理 4.3　黄金观察的基本性质

对全部 \(n,m\ge1\)：

$$
\mathcal G(n)\mid n,
$$

$$
\mathcal G(\mathcal G(n))=\mathcal G(n),
$$

并且：

$$
n\mid m\Longrightarrow\mathcal G(n)\mid\mathcal G(m).
$$

### 证明

第一式来自 \(b(a)\le a\)。

当 \(a=G_L-1\) 时，\(a+1=G_L\)，所以再次应用分层仍返回 \(G_L-1\)，得到幂等性。

最后，\(n\mid m\) 意味着每个素数指数满足：

$$
a_p(n)\le a_p(m).
$$

函数 \(b(a)\) 单调不减，因此观察后的指数仍逐项有序。证毕。

## 定理 4.4　有限纤维分解

对：

$$
m=\prod_pp^{G_{L_p}-1}\in\mathscr M,
$$

定义：

$$
\mathscr C_m=\mathcal G^{-1}(\{m\}).
$$

则：

$$
\boxed{
\mathscr C_m
=
\left\{
m\prod_pp^{r_p}:
0\le r_p<w_{L_p}
\right\},
}
\tag{4.2}
$$

且：

$$
\boxed{
|\mathscr C_m|=\prod_pw_{L_p}.
}
\tag{4.3}
$$

于是：

$$
\boxed{
\mathbb N_+
=
\bigsqcup_{m\in\mathscr M}\mathscr C_m.
}
\tag{4.4}
$$

### 证明

观察结果等于 \(m\)，等价于每个指数仍位于：

$$
G_{L_p}-1
\le a_p
\le G_{L_p+1}-2.
$$

令 \(r_p=a_p-(G_{L_p}-1)\)，便得到式（4.2）。

未出现在 \(m\) 中的素数具有 \(L_p=0\)，而 \(w_0=1\)，所以其偏移只能为零。故纤维只涉及有限个素数。

唯一素因数分解保证不同偏移向量对应不同整数，由此得到基数公式。每个整数有唯一观察结果，故这些纤维构成不交分割。证毕。

**这个观察者不是固定有限输出范围的观察者。** 每个纤维有限，但所有可能的观察结果有无穷多个。

---

## 定理 4.5　满窗因数语言

若：

$$
m=\prod_pp^{G_{L_p}-1},
$$

则：

$$
\boxed{
\operatorname{Div}(m)
\cong
\prod_p\mathcal W_{L_p}.
}
\tag{4.5}
$$

### 证明

因数 \(d\mid m\) 的每个素数指数满足：

$$
0\le v_p(d)<G_{L_p}.
$$

定理 2.2 将这个区间与 \(\mathcal W_{L_p}\) 双射。对有限个活跃素数取直积即可。证毕。

对 5040：

$$
\boxed{
\operatorname{Div}(5040)
\cong
\mathcal W_3\times\mathcal W_2\times\mathcal W_1\times\mathcal W_1.
}
$$

因而：

$$
|\operatorname{Div}(5040)|=5\cdot3\cdot2\cdot2=60.
$$

与此同时：

$$
\boxed{
\mathscr C_{5040}
=
\{5040,10080,15120,20160,30240,60480\}.
}
$$

前者是 60 个因数状态；后者是 6 个具有同一观察结果的整数状态。两者是不同的数学对象。

---

# 第五章　配分函数、熵与观察者

## 定理 5.1　局部生成函数恒等式

定义：

$$
P_L(z)=\sum_{b\in\mathcal W_L}z^{V_L(b)}.
$$

则：

$$
\boxed{
P_L(z)=\sum_{a=0}^{G_L-1}z^a.
}
$$

当 \(z\ne1\) 时：

$$
\boxed{
P_L(z)=\frac{1-z^{G_L}}{1-z}.
}
\tag{5.1}
$$

并且，对 \(L\ge2\)：

$$
P_L(z)=P_{L-1}(z)+z^{G_{L-1}}P_{L-2}(z).
$$

### 证明

第一式来自完整窗口双射。第二式是有限几何级数。

第三式按最高位为零或一分类；最高位为一时，相邻位必须为零。证毕。

代入 \(z=p^{-s}\)，得到：

$$
\boxed{
\sum_{b\in\mathcal W_L}p^{-sV_L(b)}
=
\frac{1-p^{-sG_L}}{1-p^{-s}}.
}
$$

因此，对任意整数：

$$
\boxed{
Z_n(s)
=
\prod_{p\mid n}
\left(
1+p^{-s}+\cdots+p^{-a_p(n)s}
\right).
}
\tag{5.2}
$$

---

## 定义 5.2　因数 Gibbs 分布

对实数 \(s\)，在有限因数集合上定义：

$$
\mu_{n,s}(d)=\frac{d^{-s}}{Z_n(s)}.
$$

所有概率都严格为正。

## 定理 5.3　有限自由能变分公式

对因数集合上的任意概率分布 \(\nu\)：

$$
\boxed{
H(\nu)-s\,\mathbb E_\nu[\ln d]
\le
\ln Z_n(s),
}
\tag{5.3}
$$

等号成立当且仅当：

$$
\nu=\mu_{n,s}.
$$

### 证明

展开相对熵：

$$
\begin{aligned}
\operatorname{KL}(\nu\Vert\mu_{n,s})
&=
\sum_d\nu(d)\ln\frac{\nu(d)}{\mu_{n,s}(d)}\\
&=
-H(\nu)+s\mathbb E_\nu[\ln d]+\ln Z_n(s).
\end{aligned}
$$

相对熵非负，且仅在分布相同时为零，因此结论成立。证毕。

令：

$$
W_n(s)=\ln Z_n(s).
$$

有限求和可以直接求导：

$$
W_n'(s)=-\mathbb E_{\mu_{n,s}}\ln d,
$$

$$
W_n''(s)=\operatorname{Var}_{\mu_{n,s}}(\ln d).
$$

因而：

$$
\boxed{
\frac{d}{ds}H(\mu_{n,s})
=
-s\,\operatorname{Var}_{\mu_{n,s}}(\ln d).
}
\tag{5.4}
$$

特别地，在 \(s\ge0\) 上，熵随 \(s\) 非增。

这是一种离散状态集合上的连续权重变化，不意味着有限系统发生了奇异相变。

---

## 定理 5.4　精确粗粒化保持配分函数

设 \(X\) 是有限集合，能量为 \(e:X\to\mathbb R\)，观察者为：

$$
q:X\to Y.
$$

对每个非空纤维定义：

$$
Z_y(s)=\sum_{x:q(x)=y}e^{-se(x)}.
$$

则：

$$
\boxed{
Z(s)=\sum_ye^{-s e_q(y)},
\qquad
e_q(y)=-\frac1s\ln Z_y(s)
}
\tag{5.5}
$$

对 \(s>0\) 成立。

### 证明

只需按观察纤维重新分组：

$$
\sum_xe^{-se(x)}
=
\sum_y\sum_{x:q(x)=y}e^{-se(x)}
=
\sum_yZ_y(s).
$$

再用有效能量的定义即可。证毕。

**因此，粗粒化本身不必损失总权重。** 若纤维权重被精确保留，配分函数不变；只有在遗漏、近似或错误合并纤维权重时，才出现相应误差。

---

## 定理 5.5　隐藏算术权重公式

固定 \(n\)，把其素因子划分为观察部分和隐藏部分：

$$
n=n_Jn_T,
\qquad
\gcd(n_J,n_T)=1.
$$

每个因数唯一写为：

$$
D=D_JD_T.
$$

令观察者读出 \(D_J\)，或等价地读出观察部分的全部素数指数。则：

$$
\boxed{
\ln Z_{n_T}(s)
=
H(D\mid D_J)-s\,\mathbb E[\ln D_T].
}
\tag{5.6}
$$

这里的分布为 \(\mu_{n,s}\)。

### 证明

由互素乘法性：

$$
Z_n(s)=Z_{n_J}(s)Z_{n_T}(s),
$$

并且：

$$
\mu_{n,s}(d_Jd_T)
=
\mu_{n_J,s}(d_J)\mu_{n_T,s}(d_T).
$$

所以 \(D_J,D_T\) 独立，从而：

$$
H(D\mid D_J)=H(D_T).
$$

再由：

$$
-\ln\mu_{n_T,s}(d_T)
=
s\ln d_T+\ln Z_{n_T}(s),
$$

取期望得到结论。证毕。

这使“隐藏信息”与“隐藏算术影响”得到严格区分：

$$
\boxed{
\text{隐藏算术权重}
=
\text{条件熵}
-
\text{平均隐藏规模成本}.
}
$$

项目的商—纤维熵分解提供了这一结构的信息论基础；式（5.6）另外使用了本问题的乘法分解与对数规模。

---

# 第六章　信息逃逸率的准确含义

## 定义 6.1　有限碰撞逃逸率

设有限状态集合 \(X\) 的大小为 \(N>1\)，观察者为 \(q:X\to Y\)。

定义：

$$
\boxed{
\varepsilon(q)
=
\frac{
|\{(x,x'):x\ne x',\ q(x)=q(x')\}|
}{
N(N-1)
}.
}
\tag{6.1}
$$

这与项目 `ExactRate.lean` 中使用的归一化有序不同状态对计数一致。

## 定理 6.2　逃逸率、纤维大小与条件熵

假设 \(X\) 上使用均匀分布。令：

$$
k_y=|q^{-1}(y)|.
$$

则：

$$
\boxed{
\varepsilon(q)
=
\frac{\sum_yk_y(k_y-1)}{N(N-1)},
}
$$

$$
\boxed{
H(X\mid q(X))
=
\sum_y\frac{k_y}{N}\ln k_y,
}
$$

并且：

$$
\boxed{
H(X\mid q(X))
\le
\ln\bigl(1+(N-1)\varepsilon(q)\bigr).
}
\tag{6.2}
$$

若所有非空纤维大小都等于 \(R\)，则：

$$
\boxed{
\varepsilon(q)=\frac{R-1}{N-1},
\qquad
H(X\mid q(X))=\ln R,
}
$$

且式（6.2）取等号。

### 证明

每个大小为 \(k_y\) 的纤维含有 \(k_y(k_y-1)\) 个不同有序状态对，得到第一式。

给定观察结果后，条件分布在相应纤维上均匀，得到第二式。

再由对数的凹性：

$$
\begin{aligned}
H(X\mid q(X))
&=
\sum_y\frac{k_y}{N}\ln k_y\\
&\le
\ln\left(\sum_y\frac{k_y^2}{N}\right).
\end{aligned}
$$

而：

$$
\frac{\sum_yk_y^2}{N}
=
1+(N-1)\varepsilon(q).
$$

因此得到上界。等大纤维时直接取等。证毕。

## 推论 6.3　小逃逸率不保证小隐藏熵

取：

$$
X_m=\{1,\ldots,m\}^2,
\qquad
q(x,y)=x.
$$

则：

$$
\varepsilon(q)=\frac1{m+1}\to0,
$$

但：

$$
H(X_m\mid q(X_m))=\ln m\to\infty.
$$

所以，控制信息逃逸率时不能删除状态规模 \(N\)。

## 定理 6.4　精化与重命名

若 \(q\) 可由更精细的观察 \(q'\) 计算，即：

$$
q=r\circ q',
$$

则：

$$
\varepsilon(q')\le\varepsilon(q),
$$

以及对任意有限源分布：

$$
H(X\mid q'(X))\le H(X\mid q(X)).
$$

若只对状态和输出作双射重命名，并同步搬运概率分布，则这些量保持不变。

### 证明

\(q'\) 不可区分的状态对必然也被 \(q\) 混同，得到逃逸率单调性。

条件熵满足：

$$
H(X\mid q(X))
=
H(q'(X)\mid q(X))
+
H(X\mid q'(X)),
$$

第一项非负。重命名不改变纤维与概率，因此不改变各项。证毕。

**所以，整数换成 Zeckendorf 坐标，不会仅因改名而降低信息逃逸。真正产生改进的是新增观察、合法约束或目标估计。**

---

# 第七章　ζ 观察窗口与两种资源

## 定义 7.1　全整数 ζ 分布

对实数 \(s>1\)，定义：

$$
P_s(n)=\frac{n^{-s}}{\zeta(s)}.
$$

Euler 乘积在这一范围内绝对收敛：

$$
\zeta(s)=\prod_p(1-p^{-s})^{-1}.
$$

以下全局乘积均在相应收敛域内使用。([DLMF][2])

选择有限素数集合 \(S\)，以及每个方向的窗口深度 \(L_p\)，令：

$$
M=\prod_{p\in S}p^{G_{L_p}-1}.
$$

窗口保留事件为：

$$
A_M=\{n:n\mid M\}.
$$

## 定理 7.2　保留质量与遗漏分解

$$
P_s(A_M)=\frac{Z_M(s)}{\zeta(s)}.
$$

定义：

$$
\mathcal E_{S,L}(s)
=
-\ln P_s(A_M).
$$

则：

$$
\boxed{
\mathcal E_{S,L}(s)
=
\sum_{p\notin S}-\ln(1-p^{-s})
+
\sum_{p\in S}-\ln(1-p^{-sG_{L_p}}).
}
\tag{7.1}
$$

此外：

$$
\boxed{
\operatorname{KL}\bigl(P_s(\,\cdot\,\mid A_M)\Vert P_s\bigr)
=
\mathcal E_{S,L}(s).
}
\tag{7.2}
$$

### 证明

第一式直接由概率定义成立。

将有限乘积：

$$
Z_M(s)
=
\prod_{p\in S}
\frac{1-p^{-sG_{L_p}}}{1-p^{-s}}
$$

与 Euler 乘积相除、取对数，得到式（7.1）。

条件分布在 \(A_M\) 上满足：

$$
\frac{P_s(n\mid A_M)}{P_s(n)}
=
\frac1{P_s(A_M)}.
$$

其对数为常数，对条件分布取期望便得到式（7.2）。证毕。

式（7.1）严格区分：

$$
\boxed{
\text{未加入的素数方向}
\quad+\quad
\text{已加入方向中的指数截断}.
}
$$

## 定理 7.3　黄金纵向深度的误差界

对固定素数 \(p\)、固定 \(s>1\)：

$$
-\ln(1-p^{-sG_L})
\le
\frac{p^{-sG_L}}{1-p^{-sG_L}}.
$$

从而其衰减至多具有：

$$
\boxed{
O_{p,s}\!\left(
e^{-s(\ln p)\varphi^L}
\right)
}
\tag{7.3}
$$

的上界。

### 证明

对 \(0<u<1\)：

$$
-\ln(1-u)=\int_0^u\frac{dt}{1-t}\le\frac{u}{1-u}.
$$

代入 \(u=p^{-sG_L}\)，再用 \(G_L\ge\varphi^L\)。证毕。

黄金深度可以非常快地压低**固定素数内部**的尾项，但不能代替新增素数方向。

---

## 定理 7.4　显式有限窗口充分条件

令 \(X\ge2\) 为整数，并取：

$$
S=\{p:p\le X\}.
$$

则：

$$
\boxed{
\mathcal E_{S,L}(s)
\le
\frac1{1-2^{-s}}
\left[
\frac{X^{1-s}}{s-1}
+
\sum_{p\le X}p^{-sG_{L_p}}
\right].
}
\tag{7.4}
$$

### 证明

对所有相关 \(u\le2^{-s}\)：

$$
-\ln(1-u)\le\frac{u}{1-2^{-s}}.
$$

所以遗漏的素数方向满足：

$$
\sum_{p>X}-\ln(1-p^{-s})
\le
\frac1{1-2^{-s}}
\sum_{p>X}p^{-s}.
$$

用全部整数上界素数：

$$
\sum_{p>X}p^{-s}
\le
\sum_{n>X}n^{-s}
\le
\int_X^\infty t^{-s}\,dt
=
\frac{X^{1-s}}{s-1}.
$$

有限指数尾项同理。证毕。

因此，对固定 \(s>1\) 和任意 \(\epsilon>0\)，先增大 \(X\)，再增大各 \(L_p\)，可保证：

$$
\mathcal E_{S,L}(s)<\epsilon.
$$

这是有效的充分条件，不声称其资源开销最优。

---

## 定理 7.5　临界极限不交换

取：

$$
M_k=\prod_{j=1}^kp_j^{G_k-1}.
$$

则：

$$
\boxed{
\lim_{s\downarrow1}\lim_{k\to\infty}
\frac{Z_{M_k}(s)}{\zeta(s)}
=1,
}
$$

但：

$$
\boxed{
\lim_{k\to\infty}\lim_{s\downarrow1}
\frac{Z_{M_k}(s)}{\zeta(s)}
=0.
}
\tag{7.5}
$$

### 证明

每个正整数最终都整除 \(M_k\)。因此对固定 \(s>1\)，非负级数单调收敛给出：

$$
Z_{M_k}(s)\uparrow\zeta(s).
$$

故第一种次序的内层极限为 1。

对固定 \(k\)，有限和满足：

$$
Z_{M_k}(s)\to Z_{M_k}(1)<\infty.
$$

另一方面，积分比较给出：

$$
\frac1{s-1}
\le\zeta(s)\le1+\frac1{s-1},
$$

所以 \(\zeta(s)\to\infty\)。第二种次序的内层极限为零。证毕。

---

## 定理 7.6　临界保留质量要求横向扩窗

设 \(s\downarrow1\) 时，窗口仅使用不超过 \(x(s)\) 的素数，并且存在 \(\eta>0\)，使：

$$
\frac{Z_{M(s)}(s)}{\zeta(s)}\ge\eta
$$

最终成立。则：

$$
\boxed{
\liminf_{s\downarrow1}(s-1)\ln x(s)
\ge
\eta e^{-\gamma}.
}
\tag{7.6}
$$

### 证明

首先 \(x(s)\to\infty\)。否则存在有界子序列，其有限 Euler 乘积有统一上界，无法与趋于无穷的 \(\zeta(s)\) 保持正比例。

其次：

$$
Z_{M(s)}(s)
\le
\prod_{p\le x(s)}(1-p^{-1})^{-1}.
$$

Mertens 定理给出：

$$
\prod_{p\le x}(1-p^{-1})^{-1}
\sim e^\gamma\ln x.
$$

这是本节使用的经典算术输入。([arXiv][3])

结合：

$$
(s-1)\zeta(s)\to1,
$$

以及保留质量下界：

$$
\eta(s-1)\zeta(s)
\le
(s-1)e^\gamma\ln x(s)(1+o(1)).
$$

取下极限得到结论。证毕。

因此，\(\varphi\) 与 \(\gamma\) 承担不同角色：

$$
\boxed{
\varphi:\text{指数方向的分辨率增长};
\qquad
\gamma:\text{全素数权重的临界尺度}.
}
$$

---

# 第八章　编码的存在性与最优信息预算

## 定义 8.1　Fibonacci 前缀码

若：

$$
n=\sum_{j=0}^hb_jG_j,
\qquad b_h=1,
$$

定义：

$$
\mathsf F(n)=b_0b_1\cdots b_h1.
$$

额外的最后一个 \(1\) 用作终止位。

## 定理 8.2　自定界性与码长

\(\mathsf F\) 是前缀码，且：

$$
\boxed{
\log_\varphi n<L_{\mathsf F}(n)
\le\log_\varphi n+2.
}
\tag{8.1}
$$

### 证明

合法数据内部没有 `11`，而最高位为 \(1\)，因此第一个 `11` 恰好出现在结尾。扫描到它即可确定消息边界。

最高位为 \(h\) 意味着：

$$
G_h\le n<G_{h+1}.
$$

结合第二章的增长界及 \(L_{\mathsf F}(n)=h+2\)，得到长度界。证毕。

令：

$$
\alpha=\frac{\ln2}{\ln\varphi}.
$$

标准 Fibonacci 码的首项长度为 \(\alpha\log_2n\)。若要避免对大整数载荷支付这一首项系数，可以只用它编码二进制长度。

令：

$$
b(n)=\lfloor\log_2n\rfloor+1,
$$

$$
\mathsf B(n)
=
\mathsf F(b(n))
\Vert
\operatorname{tailbin}(n).
$$

解出 \(b(n)\) 后，再读取恰好 \(b(n)-1\) 位，即可恢复 \(n\)。于是：

$$
\boxed{
L_{\mathsf B}(n)
\le
\log_2n+
\alpha\log_2(1+\log_2n)+2.
}
\tag{8.2}
$$

这证明全部正整数都可用该语言的自定界字段唯一编码，但不宣称它对所有源分布都最优。

---

## 定理 8.3　给定黄金观察结果的最优残差长度

双方已知 \(m\in\mathscr M\)，仅需发送：

$$
n\in\mathscr C_m.
$$

令：

$$
K_m=|\mathscr C_m|.
$$

则最优的最坏前缀码长为：

$$
\boxed{
\left\lceil\log_2K_m\right\rceil.
}
\tag{8.3}
$$

### 证明

偏移向量 \(r_p\) 可以按混合进制排序成 \(K_m\) 个序号，统一使用 \(\lceil\log_2K_m\rceil\) 位即可。

反过来，若所有码长至多 \(L\)，Kraft 不等式给出：

$$
1\ge\sum_{n\in\mathscr C_m}2^{-L(n)}
\ge K_m2^{-L}.
$$

所以 \(L\ge\lceil\log_2K_m\rceil\)。证毕。

对 5040 单元，条件残差的最坏长度为 3 比特。

**这里必须预先知道 \(m\)。若还需发送观察结果本身，它的描述成本不能删除。**

---

## 定理 8.4　因数状态的最优分块额外预算

固定整数 \(n\)，发送 \(r\) 个因数状态：

$$
\mathbf d=(d_1,\ldots,d_r)\in\operatorname{Div}(n)^r.
$$

定义最优最坏额外开销：

$$
\mathcal R_r(n)
=
\inf_C
\max_{\mathbf d}
\left[
L_C(\mathbf d)
-
\sum_{i=1}^r\log_2d_i
\right],
$$

其中下确界遍历二进制前缀码。

则：

$$
\boxed{
r\log_2Z(n)
\le
\mathcal R_r(n)
<
r\log_2Z(n)+1.
}
\tag{8.4}
$$

因而：

$$
\boxed{
\mathcal R_\infty(n)
=
\lim_{r\to\infty}\frac{\mathcal R_r(n)}r
=
\log_2Z(n).
}
\tag{8.5}
$$

### 证明

若某编码的最坏额外开销为 \(u\)，则：

$$
L_C(\mathbf d)
\le
\sum_i\log_2d_i+u.
$$

Kraft 不等式给出：

$$
\begin{aligned}
1
&\ge\sum_{\mathbf d}2^{-L_C(\mathbf d)}\\
&\ge2^{-u}\sum_{\mathbf d}\prod_i d_i^{-1}\\
&=2^{-u}Z(n)^r.
\end{aligned}
$$

所以 \(u\ge r\log_2Z(n)\)。

反过来，取：

$$
\ell(\mathbf d)
=
\left\lceil
\sum_i\log_2d_i+r\log_2Z(n)
\right\rceil.
$$

则：

$$
\sum_{\mathbf d}2^{-\ell(\mathbf d)}\le1.
$$

满足 Kraft 条件的有限整数长度可以构造为前缀码：按长度排列，在单位区间中依次分配相应长度的二进制区间即可。

取整损失不足 1，比特长度上界成立。除以 \(r\) 后用夹逼定理得到极限。证毕。

这使 \(Z(n)\) 不再只是形式上的“配分函数”，而具有明确的最优编码预算解释。

---

# 第九章　Robin 临界界及其黄金翻译

## 经典输入：Robin 定理

记欧拉–马歇罗尼常数为：

$$
\gamma=\lim_{N\to\infty}(H_N-\ln N).
$$

Robin 定理指出：

$$
\boxed{
\mathrm{RH}
\iff
Z(n)<e^\gamma\ln\ln n
\qquad\forall n>5040.
}
\tag{9.1}
$$

Gronwall 定理则无条件给出：

$$
\boxed{
\limsup_{n\to\infty}
\frac{Z(n)}{\ln\ln n}
=e^\gamma.
}
\tag{9.2}
$$

这两个经典结果分别承担逐点判据与极限标尺的作用。([arXiv][4])

## 定义 9.1　Robin 对数余量

对 \(n\ge3\)，定义：

$$
\boxed{
\Delta(n)
=
\gamma+\ln\ln E(n)-W(n).
}
\tag{9.3}
$$

由于 \(E(n)=\ln n\)，也就是：

$$
\Delta(n)
=
\gamma+\ln\ln\ln n-\ln\frac{\sigma(n)}n.
$$

## 定理 9.2　黄金状态、自由能与编码预算的等价判据

以下三个全称命题均等价于 RH。

对每个规范表 \(b\)，令 \(n=N(b)>5040\)，则：

$$
\boxed{
\sum_{c:\,N(c)\mid N(b)}e^{-E(N(c))}
<
e^\gamma\ln E(n).
}
\tag{9.4}
$$

对 \(\operatorname{Div}(n)\) 上每个概率分布 \(\nu\)：

$$
\boxed{
H(\nu)-\mathbb E_\nu[\ln d]
<
\gamma+\ln\ln E(n).
}
\tag{9.5}
$$

对最优分块开销：

$$
\boxed{
\mathcal R_\infty(n)
<
\frac{\gamma+\ln\ln E(n)}{\ln2}.
}
\tag{9.6}
$$

### 证明

式（9.4）的左边等于 \(Z(n)\)，因此是 Robin 判据的规范坐标表达。

式（9.5）的左边最大值由定理 5.3 等于 \(\ln Z(n)\)，所以其对全部 \(\nu\) 的严格上界，等价于 Robin 判据取对数。

式（9.6）由定理 8.4 等价于：

$$
\log_2Z(n)
<
\log_2(e^\gamma\ln\ln n).
$$

故三者均与式（9.1）等价。证毕。

### 推论 9.3　不存在统一的正余量

由 Gronwall 定理：

$$
\boxed{
\liminf_{n\to\infty}\Delta(n)=0.
}
\tag{9.7}
$$

### 证明

令：

$$
u_n=\frac{Z(n)}{e^\gamma\ln\ln n}.
$$

则 \(\limsup u_n=1\)，而 \(\Delta(n)=-\ln u_n\)。由对数连续性和单调性得到结论。证毕。

所以，即使 RH 成立，也不能期待存在统一的 \(\epsilon>0\)，使所有 \(n>5040\) 都满足 \(\Delta(n)\ge\epsilon\)。

---

# 第十章　黄金单元上的统一证书

这部分不是单纯的坐标改写，而是为一整个有限观察纤维提供可计算上界。

## 定义 10.1　局部收益

对素数 \(p\) 和整数 \(a\ge0\)，定义：

$$
f_p(a)
=
\ln\left(1+p^{-1}+\cdots+p^{-a}\right).
$$

因此：

$$
W(n)=\sum_pf_p(a_p(n)).
$$

对于实数 \(x\ge0\)，先取解析延拓：

$$
f_p(x)
=
\ln\frac{1-p^{-(x+1)}}{1-p^{-1}}.
$$

直接计算：

$$
f_p'(x)=\frac{\ln p}{p^{x+1}-1},
$$

$$
f_p''(x)
=
-\frac{(\ln p)^2p^{x+1}}{(p^{x+1}-1)^2}<0.
$$

所以整数增量：

$$
f_p(a+1)-f_p(a)
$$

严格递减。

---

## 定理 10.2　一般矩形单元证书

固定 \(m\ge3\)，其指数为 \(b_p\)。考虑有限矩形：

$$
\mathscr Q
=
\left\{
m\prod_pp^{r_p}:
0\le r_p\le R_p
\right\},
$$

其中仅有限多个 \(R_p>0\)。

令：

$$
E=\ln m,
\qquad
U=\sum_pR_p\ln p,
$$

$$
c=\frac1{(E+U)\ln(E+U)}.
$$

则对所有 \(n\in\mathscr Q\)：

$$
\boxed{
\Delta(n)
\ge
\Delta(m)
+
\sum_p
\left[
cr_p\ln p
-
f_p(b_p+r_p)+f_p(b_p)
\right].
}
\tag{10.1}
$$

因而：

$$
\boxed{
\min_{n\in\mathscr Q}\Delta(n)
\ge
\Delta(m)
+
\sum_p
\min_{0\le r\le R_p}
\left[
cr\ln p-f_p(b_p+r)+f_p(b_p)
\right].
}
\tag{10.2}
$$

### 证明

令：

$$
u=\ln(n/m)=\sum_pr_p\ln p.
$$

有：

$$
\Delta(n)-\Delta(m)
=
\ln\ln(E+u)-\ln\ln E
-
\sum_p[f_p(b_p+r_p)-f_p(b_p)].
$$

由于：

$$
\frac{d}{dt}\ln\ln t=\frac1{t\ln t}
$$

在 \(t>1\) 上递减，并且 \(0\le u\le U\)，所以：

$$
\ln\ln(E+u)-\ln\ln E
=
\int_E^{E+u}\frac{dt}{t\ln t}
\ge cu.
$$

代入得到式（10.1）。随后分别对每个坐标取最小值，得到式（10.2）。证毕。

## 推论 10.3　局部最小化只需寻找边际交叉

对固定 \(p\)，令：

$$
h_p(r)=cr\ln p-f_p(b_p+r)+f_p(b_p).
$$

则：

$$
h_p(r)-h_p(r-1)
=
c\ln p-
[f_p(b_p+r)-f_p(b_p+r-1)]
$$

随 \(r\) 严格增加。

因此，最小者位于边际收益跨过 \(c\) 的位置；至多有两个相邻的并列最小者。

这把一个高维单元的充分证书，分解为有限个一维离散凹收益比较。

---

## 推论 10.4　简化的统一斜率证书

对所有 \(R_p>0\) 的方向，定义：

$$
\kappa_p=
\frac{f_p(b_p+1)-f_p(b_p)}{\ln p},
\qquad
\kappa=\max_p\kappa_p.
$$

则：

$$
\boxed{
\Delta(n)\ge\Delta(m)+(c-\kappa)\ln(n/m).
}
\tag{10.3}
$$

### 证明

由递减增量：

$$
f_p(b_p+r_p)-f_p(b_p)
\le
r_p[f_p(b_p+1)-f_p(b_p)]
\le
\kappa r_p\ln p.
$$

代入式（10.1）。证毕。

---

# 第十一章　5040 的完整局部分析

## 定理 11.1　5040 是指定资源成本下的唯一最优整数

定义：

$$
J_\lambda(n)=W(n)-\lambda E(n).
$$

当：

$$
\lambda=\frac1{25}
$$

时：

$$
\boxed{
\operatorname*{arg\,max}_{n\ge1}J_\lambda(n)=5040.
}
\tag{11.1}
$$

### 证明

增加 \(p\) 的第 \(a\) 层指数，单位规模收益为：

$$
r(p,a)
=
\frac{
\ln\left(
\frac{1-p^{-(a+1)}}{1-p^{-a}}
\right)
}{\ln p}.
$$

它随 \(a\) 严格递减。

以下严格比较决定每个方向的最优层数：

| 素数    | 最后一层 \(r(p,a)>1/25\) | 下一层 \(r(p,a+1)<1/25\) |
| ----- | -------------------: | --------------------: |
| \(2\) |              \(a=4\) |               \(a=5\) |
| \(3\) |              \(a=2\) |               \(a=3\) |
| \(5\) |              \(a=1\) |               \(a=2\) |
| \(7\) |              \(a=1\) |               \(a=2\) |

而：

$$
r(11,1)=\frac{\ln(12/11)}{\ln11}<\frac1{25}.
$$

函数：

$$
p\longmapsto\frac{\ln(1+1/p)}{\ln p}
$$

随 \(p\ge2\) 严格递减，所以更大的素数也不采用。

因此，每个局部目标：

$$
f_p(a)-\lambda a\ln p
$$

具有指定的唯一整数最大者。有限支撑求和后，全局唯一最优配置为：

$$
2^4\,3^2\,5\,7=5040.
$$

上述有限对数比较已用附录的有理数区间方法核验。证毕。

这证明的是收益与规模成本之间的最优性，不是普通熵或任意压缩器的普遍最优性。

---

## 定理 11.2　5040 单元的严格 Robin 证书

$$
\boxed{
\Delta(5040)<0,
}
$$

而：

$$
\boxed{
\Delta(n)>0.0047
\quad
\forall n\in\mathscr C_{5040}\setminus\{5040\}.
}
\tag{11.2}
$$

### 证明

该单元的偏移为：

$$
0\le r_2\le2,
\qquad
0\le r_3\le1,
\qquad
r_5=r_7=0.
$$

所以：

$$
E=\ln5040,
\qquad
U=\ln12,
\qquad
E+U=\ln60480.
$$

两个可能增加指数的方向满足：

$$
\kappa_2=\frac{\ln(63/62)}{\ln2},
$$

$$
\kappa_3=\frac{\ln(40/39)}{\ln3}.
$$

严格比较给出 \(\kappa_2>\kappa_3\)。令：

$$
\beta
=
\frac1{\ln60480\cdot\ln\ln60480}
-
\frac{\ln(63/62)}{\ln2}.
$$

有理数区间证书给出：

$$
-\frac{5544}{10^6}
<
\Delta(5040)
<
-\frac{5543}{10^6},
$$

$$
\beta>\frac{14779}{10^6},
$$

$$
\ln2>\frac{693147}{10^6}.
$$

对单元内 \(n\ne5040\)，有：

$$
\ln(n/5040)\ge\ln2.
$$

因此，由式（10.3）：

$$
\begin{aligned}
\Delta(n)
&\ge\Delta(5040)+\beta\ln2\\
&>
-\frac{5544}{10^6}
+
\frac{14779}{10^6}\frac{693147}{10^6}\\
&=
\frac{4700019513}{10^{12}}\\
&>
\frac{47}{10000}.
\end{aligned}
$$

证毕。

这里的符号结论来自严格区间，而不是把浮点近似当作证明。

## 命题 11.3　黄金单元基点不总是最危险状态

$$
60060=2^2\,3\,5\,7\,11\,13
$$

与：

$$
120120=2^3\,3\,5\,7\,11\,13
$$

属于同一黄金单元，但：

$$
\Delta(120120)<\Delta(60060).
$$

这一严格比较也由附录证书核验。

所以，不能未经证明就将“检查整个黄金单元”缩减为“只检查其基点”。

此外，不能只研究基点 \(m>5040\) 的单元。例如：

$$
\mathcal G(8640)=720<5040,
$$

但 \(8640>5040\)。全局判据必须保留所有与区间 \((5040,\infty)\) 相交的单元。

---

# 第十二章　连续资源分配与相对熵差额

黄金单元是精确的离散分割。为了分析其收益，还可以引入一个明确的连续松弛，但不能把这种松弛当作唯一可能的连续模型。

## 定义 12.1　连续最优值

对 \(T>0\)，定义：

$$
\Phi(T)
=
\max
\left\{
\sum_pf_p(x_p):
x_p\ge0,\ 
\sum_px_p\ln p\le T,\ 
x\text{ 有限支撑}
\right\}.
$$

## 定理 12.2　连续最优解

存在唯一 \(y>2\)，满足：

$$
\boxed{
T=\sum_{p<y}\ln\frac yp.
}
\tag{12.1}
$$

最优指数为：

$$
\boxed{
x_p^*
=
\max\left\{0,\frac{\ln y}{\ln p}-1\right\}.
}
\tag{12.2}
$$

### 证明

右边作为 \(y>2\) 的函数连续、严格递增且无界；素数进入求和时其新增项为零，因此不存在跳跃。故 \(y\) 存在唯一。

令：

$$
\lambda=\frac1{y-1}.
$$

对活跃方向：

$$
\frac{f_p'(x_p^*)}{\ln p}
=
\frac1{p^{x_p^*+1}-1}
=\lambda.
$$

对非活跃方向 \(p\ge y\)，有：

$$
\frac{f_p'(0)}{\ln p}
=
\frac1{p-1}\le\lambda.
$$

严格凹性说明每个：

$$
f_p(x)-\lambda x\ln p
$$

均在所给 \(x_p^*\) 处唯一最大。对有限支撑配置求和，再使用预算约束，得到全局最优性与唯一性。证毕。

其最优值为：

$$
\boxed{
\Phi(T)
=
\ln\prod_{p<y}(1-p^{-1})^{-1}
+
\pi_{<}(y)\ln(1-y^{-1}),
}
\tag{12.3}
$$

其中 \(\pi_{<}(y)=|\{p:p<y\}|\)。

---

## 定理 12.3　连续—整数差额的 KL 分解

固定 \(n>1\)，取 \(T=\ln n\)，令 \(y,\lambda\) 如上。定义：

$$
\mathfrak D(n)=\Phi(\ln n)-W(n).
$$

记：

$$
a_p=v_p(n),
\qquad
v_p^*=p^{-(a_p+1)}.
$$

对于 \(p<y\)，令：

$$
\mathfrak D_p(n)
=
\frac{
D_{\mathrm{Ber}}(y^{-1}\Vert v_p^*)
}{
1-y^{-1}
}.
$$

对于 \(p\ge y\)，令：

$$
\mathfrak D_p(n)
=
\frac{
D_{\mathrm{Ber}}(p^{-1}\Vert v_p^*)
}{
1-p^{-1}
}
+
\left(\lambda-\frac1{p-1}\right)a_p\ln p.
$$

其中：

$$
D_{\mathrm{Ber}}(u\Vert v)
=
u\ln\frac uv
+
(1-u)\ln\frac{1-u}{1-v}.
$$

则：

$$
\boxed{
\mathfrak D(n)=\sum_p\mathfrak D_p(n),
\qquad
\mathfrak D_p(n)\ge0.
}
\tag{12.4}
$$

### 证明

定义：

$$
g_p(x)=f_p(x)-\lambda x\ln p.
$$

连续最优性保证：

$$
g_p(x_p^*)-g_p(a_p)\ge0.
$$

又因为连续配置与整数配置具有相同总规模：

$$
\sum_px_p^*\ln p=\sum_pa_p\ln p,
$$

所以：

$$
\mathfrak D(n)
=
\sum_p[g_p(x_p^*)-g_p(a_p)].
$$

对 \(p<y\)，令 \(u=y^{-1}\)、\(v=v_p^*\)。利用：

$$
p^{-(x_p^*+1)}=u,
\qquad
\lambda=\frac u{1-u},
$$

展开得到：

$$
g_p(x_p^*)-g_p(a_p)
=
\ln\frac{1-u}{1-v}
+
\frac u{1-u}\ln\frac uv
=
\frac{D_{\mathrm{Ber}}(u\Vert v)}{1-u}.
$$

对 \(p\ge y\)，最优值为 \(x_p^*=0\)，相同展开给出第二种表达。此时：

$$
\lambda-\frac1{p-1}\ge0.
$$

所有项非负。只有 \(p<y\) 或 \(p\mid n\) 的方向可能非零，因此求和实际有限。证毕。

## 推论 12.4　RH 的连续超额—离散损失表达

对 \(T>1\)，定义：

$$
\mathfrak Q(T)
=
\Phi(T)-\gamma-\ln\ln T.
$$

则：

$$
\boxed{
\Delta(n)
=
\mathfrak D(n)-\mathfrak Q(\ln n).
}
\tag{12.5}
$$

所以：

$$
\boxed{
\mathrm{RH}
\iff
\sum_p\mathfrak D_p(n)>
\mathfrak Q(\ln n)
\quad\forall n>5040.
}
\tag{12.6}
$$

### 证明

由定义直接相减，随后应用 Robin 判据。证毕。

这个等价形式并未证明右边成立。尤其是：

$$
\mathfrak D_p(n)\ge0
$$

不能自动推出其总和大于指定的 \(\mathfrak Q\)。

## 命题 12.5　松弛差额依赖连续模型

若不用解析延拓，而在整数点间线性插值：

$$
\bar f_p(a+t)
=
(1-t)f_p(a)+tf_p(a+1),
\qquad0\le t\le1,
$$

则在预算 \(T=\ln5040\) 下，其连续最优值等于 \(W(5040)\)，松弛差额为零。

### 证明

定理 11.1 中，每个整数局部目标：

$$
f_p(a)-\frac1{25}a\ln p
$$

在 5040 对应指数处唯一最大。

线性插值不会在相邻端点之间创造更大的值，因此同一配置也最大化插值后的局部目标。

对任何总规模不超过 \(\ln5040\) 的连续配置求和，即得总收益不超过 \(W(5040)\)。证毕。

因此，KL 分解是一种精确的分析工具，但不是已经证明唯一的物理信息损失。真正不依赖松弛选择的是 \(\Delta(n)\)。

---

# 第十三章　有限观察、对角化与全局边界

## 定理 13.1　有限状态完全分离可抽取有限证书

设 \(X\) 有限，一族观察者 \(\{q_i\}_{i\in I}\) 满足：

$$
x\ne y
\Longrightarrow
\exists i,\ q_i(x)\ne q_i(y).
$$

则存在有限 \(J\subseteq I\)，使联合读出：

$$
x\longmapsto(q_i(x))_{i\in J}
$$

单射。

### 证明

对每个无序不同状态对 \(\{x,y\}\)，选择一个区分它们的观察者。由于不同状态对只有有限多个，所选观察者也只有有限多个。其联合读出区分全部状态对。证毕。

这与项目有限层析定理的核心有限性机制一致。

## 定理 13.2　固定有限素数窗口不分离全部整数

设观察者只依赖有限素数集合 \(S\) 的指数信息。则它不可能在全部正整数上单射。

### 证明

取素数 \(q\notin S\)。对任何 \(n\)：

$$
v_p(nq)=v_p(n)
\qquad(p\in S).
$$

所以观察者不能区分 \(n\) 与 \(nq\)。证毕。

全部素数指数共同可以唯一恢复整数，但任何固定有限子族不能。

## 命题 13.3　对角化是另一种结构

设：

$$
F:A\to Y^A,
$$

以及无不动点映射：

$$
\tau:Y\to Y.
$$

定义：

$$
d(a)=\tau(F(a)(a)).
$$

则 \(d\) 不属于 \(F\) 的像。

### 证明

若 \(d=F(a_0)\)，则在 \(a_0\) 处取值：

$$
F(a_0)(a_0)
=
\tau(F(a_0)(a_0)),
$$

与 \(\tau\) 无不动点矛盾。证毕。

这与“有限素数窗口遗漏一个新素数方向”不是同一个定理。二者都揭示表达或观察的边界，但都不能单独推出 RH 为假或不可证明。

---

## 定理 13.4　有限因数配分函数的零点位置

若 \(n>1\)，有限函数：

$$
Z_n(s)=\sum_{d\mid n}d^{-s}
$$

的全部零点都满足：

$$
\boxed{\Re s=0.}
$$

### 证明

若某个局部因子为零，令 \(z=p^{-s}\)，则：

$$
1+z+\cdots+z^a=0.
$$

因此：

$$
z^{a+1}=1,\qquad z\ne1.
$$

于是 \(|z|=1\)，而：

$$
|p^{-s}|=p^{-\Re s},
$$

故 \(\Re s=0\)。有限乘积没有其他零点。证毕。

另一方面，满窗序列只在 \(\Re s>1\) 中由绝对收敛直接逼近 ζ。ζ 在其他区域的定义涉及解析延拓。([DLMF][5])

所以，不能把有限 \(Z_n\) 的零点位置直接搬到 ζ 的临界带。需要额外的解析控制定理，而不是只靠有限模型的正性。

---

# 第十四章　全局归约定理与尚需证明的命题

## 定义 14.1　黄金单元的临界余量

对满足：

$$
\mathscr C_m^+
=
\mathscr C_m\cap\{n:n>5040\}
\ne\varnothing
$$

的黄金满窗整数 \(m\)，定义：

$$
\boxed{
\delta_{\mathrm{cell}}(m)
=
\min_{n\in\mathscr C_m^+}\Delta(n).
}
\tag{14.1}
$$

每个单元有限，所以最小值存在。

## 主定理 14.2　黄金观察临界判据

以下命题等价：

$$
\mathrm{RH};
$$

$$
\Delta(n)>0
\qquad\forall n>5040;
$$

$$
\boxed{
\delta_{\mathrm{cell}}(m)>0
\quad
\text{对全部 }\mathscr C_m^+\ne\varnothing;
}
\tag{14.2}
$$

以及对全部 \(n>5040\)：

$$
\mathcal R_\infty(n)
<
\frac{\gamma+\ln\ln E(n)}{\ln2}.
$$

### 证明

第一、第二个命题由 Robin 定理等价。

黄金单元构成全部正整数的不交分割，所以所有整数余量为正，等价于每个相关有限单元的最小余量为正。

最后一个命题由定理 8.4 等价于第二个。证毕。

---

## 定理 14.3　有限单元证书的完备性

固定一个有限黄金单元。

若其所有相关整数均满足 \(\Delta(n)>0\)，则允许把单元细分为单点时，存在有限组严格有理数区间证书，验证这些正性。

### 证明

\(\gamma\) 与正实数对数均可由带显式误差界的有理数逼近计算。

对固定 \(n\)，若 \(\Delta(n)>0\)，就可以继续提高精度，直到包含 \(\Delta(n)\) 的有理区间完全位于正半轴。

单元内相关整数只有有限多个，因此为每个整数取得一个有限精度证书后，全部证书仍然有限。证毕。

这个定理说明每个正性有限单元都可获得证书；它没有证明所有单元都正，也没有给出统一的有限资源上界。

**本理论中尚未建立的全局命题，准确地是：**

$$
\boxed{
\delta_{\mathrm{cell}}(m)>0
\quad
\text{对每一个相关黄金单元成立。}
}
\tag{G}
$$

第十章给出一类充分证书，第十一章完成了 5040 单元的完整实例。要继续推进，需要证明这些证书或更强的估计，如何统一覆盖随素数范围和指数深度增长的全部单元。

---

# 附录　5040 证书的有理数基础

数值正性不依赖未注明误差的浮点计算。

对有理数 \(x>0\)，先写成：

$$
x=2^ky,\qquad1\le y<2.
$$

令：

$$
t=\frac{y-1}{y+1},
\qquad0\le t<\frac13.
$$

则：

$$
\ln y
=
2\sum_{j=0}^{K-1}\frac{t^{2j+1}}{2j+1}
+
R_K,
$$

其中：

$$
\boxed{
0\le R_K
\le
\frac{2t^{2K+1}}{(2K+1)(1-t^2)}.
}
$$

由此得到对数的上下有理界。

对欧拉常数，有：

$$
\boxed{
\frac1{2(N+1)}
<
H_N-\ln N-\gamma
<
\frac1{2N}.
}
\tag{A.1}
$$

证明可由：

$$
H_N-\ln N-\gamma
=
\sum_{k=N}^{\infty}
\left[
\ln\left(1+\frac1k\right)-\frac1{k+1}
\right]
$$

以及逐项积分估计得到：

$$
\frac1{2(k+1)^2}
<
\ln\left(1+\frac1k\right)-\frac1{k+1}
<
\frac1{2k(k+1)}.
$$

对这些上下界求和即可。

本轮使用 \(N=1000\)、带显式尾界的对数级数和向外舍入的有理数区间，验证了第十一章的全部严格比较。证书只使用 Python 标准库的整数与分数运算。

[下载可复核的有理数证书、程序与运行结果](sandbox:/mnt/data/golden_arithmetic_certificates.zip)

这属于可复核的有限计算证书，不等于本轮已经生成 Lean 内核证明。现有仓库为规范编码、观察核和熵分解提供了可复用部件；本文的黄金单元、统一余量证书与全局组合定理仍需分别接入形式化。

---

# 理论结论

现在建立的并不是“黄金比例、5040、熵之间存在某种神秘必然性”，而是一个确定的数学体系：

$$
\boxed{
\begin{aligned}
\text{Zeckendorf 合法语言}
&\longrightarrow
\text{完整指数窗口};\\
\text{完整指数窗口}
&\longrightarrow
\text{黄金算术观察者};\\
\text{观察者}
&\longrightarrow
\text{有限纤维与残差信息};\\
\text{因数 Gibbs 权重}
&\longrightarrow
\text{熵—规模平衡};\\
\text{Kraft 约束}
&\longrightarrow
\text{最优分块信息预算};\\
\text{Robin 定理}
&\longrightarrow
\text{全部黄金单元的严格临界界}.
\end{aligned}
}
$$

其中：

$$
\boxed{
\varphi
\text{ 决定规范语言与分辨率的增长；}
}
$$

$$
\boxed{
\gamma
\text{ 决定算术权重的尖锐极限标尺；}
}
$$

$$
\boxed{
5040
\text{ 是一个可完整分析的有限最优配置及边界实例。}
}
$$

**理论的实质目标，不是证明所有信息都能由少数符号表达——这一点已有规范双射；而是证明，在全部尺度上，可表达状态的加权总量与观察纤维的最坏影响，始终满足指定的严格预算。**

这个全局任务已经被准确定位为命题 \((G)\)。它不再是未定义的“最高压缩率”或“最大熵”，而是一个具有明确状态空间、观察映射、目标函数、局部证书和完整等价关系的数学问题。

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Fib/Zeckendorf.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Fib/Zeckendorf.html"
[2]: https://dlmf.nist.gov/27.4 "https://dlmf.nist.gov/27.4"
[3]: https://arxiv.org/html/2002.03361v3 "https://arxiv.org/html/2002.03361v3"
[4]: https://arxiv.org/html/1211.2147v3 "https://arxiv.org/html/1211.2147v3"
[5]: https://dlmf.nist.gov/25.2 "https://dlmf.nist.gov/25.2"
