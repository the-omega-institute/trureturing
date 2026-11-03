# Zeckendorf 算术下降、最优 KL 损失递归与 Robin 证书（编者描述性标题）

<!-- editorial-note:start provenance -->
**【编者说明】** 以下保留原稿的完整论述、证明、公式与结尾。原稿中的“本轮”“项目已经证明”等表述归于原稿及其所引固定版本来源；新增推论按原稿声明属于纸面推导，不表示本文进行了新的 Lean 核验。各处“编者局部说明”明确记号、适用条件和证明桥梁，保留所针对的原文。有限层关系损失恢复与全体整数的严格 Robin 不等式分别承担不同的证明义务；式（48）所需的统一严格下界仍未证明。

[第一节](#section-1) · [第二节](#section-2) · [第三节](#section-3) · [第四节](#section-4) · [第五节](#section-5) · [第六节](#section-6) · [第七节](#section-7) · [第八节](#section-8) · [未决式（48）](#eq-48)
<!-- editorial-note:end provenance -->

<!-- original-manuscript:start -->
可以。现在可以把这条路线落实成一套**有明确递归规则、进度量和证书传递条件的证明体系**：

$$
\boxed{
\text{Zeckendorf 贪心遍历}
\;\longrightarrow\;
\text{算术分类}
\;\longrightarrow\;
\text{整数下降与证书继承}
\;\longrightarrow\;
\text{AURIC 关系损失的递归读取}.
}
$$

这轮能严格推进两件关键事情：

1. **误差本身可以继续递归处理。** 对项目中的 Robin 关系损失，能够构造同一来源上的嵌套三结果观察；采用适当的贪心配对，每层剩余至多缩小为上一层的 $1/(2K)$，而且有限层后精确恢复全部损失。
2. **分类可以直接产生数论证明。** 能证明：若一个整数缺少某些明确要求的素数幂，它就满足 Robin 不等式；另外，一些整数可以把证明义务传给更小整数，再沿下降链回传证书。

<a id="source-1"></a>

<a id="source-2"></a>

下面把这些内容完整写出来。项目依据包括你指出的 [Zeckendorf 贪心排列定理](https://github.com/the-omega-institute/trureturing/blob/9ceb721e13c64eb4b1c71a43238a2b2fc4770093/Blueprint/D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.md)，以及本轮读到的固定提交 `3f98ae45…` 中新合并的 [《关系恢复尺度、三候选整数优化与 Robin 证书》](https://github.com/the-omega-institute/trureturing/blob/3f98ae45e29bd5fb6ef8dd7d1e5bf39c2723520e/docs/develop/theory/AURIC_RELATION_SCALE_RECOVERY_THREE_CANDIDATE_OPTIMIZATION_AND_ROBIN_CERTIFICATES.md)，特别是其第八节。

以下新增推论是纸面证明；本轮没有运行数学枚举，也没有把这些新增推论重新编译进 Lean。

---

<a id="section-1"></a>

## 一、先固定整个递归要证明什么

<!-- editorial-note:start note-1 -->
**【编者局部说明：独立阅读的记号与定义域】** 全文整数变量取正整数，$p,q$ 表示素数；$\sigma(n)=\sum_{d\mid n,\ d>0}d$ 是正约数和，$v_p(n)$ 是 $p$ 在 $n$ 中的指数，$\gamma=\lim_{M\to\infty}(\sum_{j=1}^M1/j-\log M)$ 是 Euler–Mascheroni 常数。所有 $\log$ 均为自然对数；$Z(n)>0$ 对正整数有定义，本文的 $R(n)$ 及 $\log R(n)$ 用于 $n>5040$，此时 $T>1$、$\Lambda>0$。$\operatorname{lcm}$ 表示最小公倍数，$p^a\parallel n$ 表示 $v_p(n)=a$；$\omega(n)$ 是不同素因子个数，$P^+(n)$ 是 $n>1$ 的最大素因子。后文 $m$ 在不同节中分别表示下降后的整数或局部损失的项数，均按所在节的定义使用。
<!-- editorial-note:end note-1 -->

对 $n>5040$，定义

$$
Z(n)=\frac{\sigma(n)}n,
\qquad
R(n)=\frac{Z(n)}{e^\gamma\log\log n}.
$$

记

$$
T=\log n,\qquad \Lambda=\log T.
$$

目标是

$$
R(n)<1.
$$

Robin 判据说明：

<a id="eq-1"></a>

$$
\boxed{
\mathrm{RH}
\iff
\forall n>5040,\quad R(n)<1.
}
\tag{1}
$$

<a id="source-3"></a>

这个严格不等式是最终必须保留的任务。[来源：Axler 论文中的 Robin 判据及相关定理](https://arxiv.org/pdf/2110.13478v3)。

外层使用项目已经证明的排列：

$$
a_1=1,
$$

<a id="eq-2"></a>

$$
a_{t+1}
=
\min\left\{
m\ge1:
m\notin\{a_1,\ldots,a_t\},\
|S(m)\cap S(a_t)|=1
\right\}.
\tag{2}
$$

它保证每个正整数恰好被访问一次。

<!-- editorial-note:start note-2 -->
**【编者局部说明：式（2）的准确约定】** $S(m)$ 是 $m$ 的唯一规范 Zeckendorf 展开所占用的 Fibonacci 下标集合：$F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$，仅用下标 $j\ge2$，权重为 $1,2,3,5,\ldots$，相邻下标不能同时占用。这里要求交集的基数恰为一，排除的是从第一项起的全部已用整数，最小化的是候选整数的数值。所引固定版本 ZeckendorfGreedyPermutation 的定义 1.1–1.5 和定理 1.6 同时给出 $a_1=1$、每步存在最小合格后继、正指标上的单射与对所有正整数的覆盖；引用该既有结论不表示本文重新编译了它。
<!-- editorial-note:end note-2 -->

**外层按这个顺序提交整数；每个整数内部再进行算术分类和贪心归约。** 内层的归约不会改变式（2）的定义。

---

<a id="section-2"></a>

## 二、第一种真正有证明作用的分类：缺少指定素数幂，就直接通过

这一部分先给递归系统一个可以一次认证整类整数的规则。

<a id="definition-1"></a>

### 定义 1：局部 Euler 缺损

对素数 $p$ 和整数 $a\ge0$，定义

$$
d_p(a)=-\log(1-p^{-a-1}).
$$

它记录实际指数 $a$ 与该素数方向完全饱和之间的对数差。

再定义

$$
A_0=0.0094243,
$$

<a id="eq-3"></a>

$$
q(n)=\frac{A_0}{(\log\log n)^3}
+\frac3{\log n}.
\tag{3}
$$

这里使用的解析输入是 Axler 的无条件上界：

<a id="eq-4"></a>

$$
R(N)<1+\frac{A_0}{(\log\log N)^3},
\qquad N>5040.
\tag{4}
$$

<a id="source-4"></a>

原论文定理 1.3 的有限例外全部不超过 $5040$，所以式（4）适用于当前全部目标整数。[来源：Axler，Theorem 1.3](https://arxiv.org/pdf/2110.13478v3)。

<!-- editorial-note:start note-3 -->
**【编者局部说明：所用版本与严格范围】** 此处编号专指 Christian Axler《On Robin’s Inequality》的 arXiv:2110.13478v3，PDF 第 2 页 Theorem 1.3，不以其他发表版本的定理编号替代。该定理的例外集为 $A$ = {1, 2, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24, 30, 36, 48, 60, 72, 84, 120, 180, 240, 360, 840, 2520, 5040}，对 $n\notin A$ 给出常数 $0.0094243$ 的严格上界。因此所有整数 $n>5040$ 均在式（4）的范围内；PDF 第 1 页 Proposition 1.1 给出式（1）的严格 Robin 判据。
<!-- editorial-note:end note-3 -->

<a id="theorem-1"></a>

### 定理 1：单素数缺损证书

对任意 $n>5040$ 和素数 $p\le\log n$，有

<a id="eq-5"></a>

$$
\boxed{
\log R(n)
<
q(n)-d_p(v_p(n)).
}
\tag{5}
$$

因此

<a id="eq-6"></a>

$$
\boxed{
d_p(v_p(n))\ge q(n)
\Longrightarrow R(n)<1.
}
\tag{6}
$$

#### 证明

令 $a=v_p(n)$。取最小整数 $k\ge1$，使

$$
p^k\ge T.
$$

于是

$$
T\le p^k<pT.
$$

记

$$
s=k\log p.
$$

因为 $p\le T$，

<a id="eq-7"></a>

$$
s<\log T+\log p\le2\Lambda.
\tag{7}
$$

令 $N=np^k$。Euler 因子给出精确关系

$$
\log Z(n)
=
\log Z(N)-d_p(a)+d_p(a+k).
$$

因此

<a id="eq-8"></a>

$$
\log R(n)
=
\log R(N)
+\log\frac{\log(T+s)}{\log T}
-d_p(a)+d_p(a+k).
\tag{8}
$$

分别控制三个正向代价。

第一，由式（4），

$$
\log R(N)
<
\frac{A_0}{\Lambda^3}.
$$

第二，

$$
\begin{aligned}
\log\frac{\log(T+s)}{\log T}
&=
\log\left(
1+\frac{\log(1+s/T)}{\Lambda}
\right)\\
&\le\frac{s}{T\Lambda}
\le\frac2T.
\end{aligned}
$$

第三，因为

$$
p^{-a-k-1}\le\frac1{2T},
$$

由 $-\log(1-x)\le x/(1-x)$，得到

$$
d_p(a+k)
\le\frac1{2T-1}
\le\frac1T.
$$

代入式（8）即得式（5）。∎

<!-- editorial-note:start note-4 -->
**【编者局部说明：饱和估计的端点】** 最小 $k\ge1$ 的存在来自 $p\ge2$，且 $p^{k-1}<T$，包括 $k=1$ 的情形，因为 $T>1$。这保证式（7）的严格号。$N>n>5040$ 且 $\log\log N\ge\Lambda>0$，故 $\log R(N)<\log(1+A_0/(\log\log N)^3)<A_0/\Lambda^3$。另外 $p^{-a-k-1}\le1/(2T)<1$，$T>1$ 保证 $1/(2T-1)\le1/T$；全部正向代价在同一个 $N=np^k$ 上估计，最终仍有严格的式（5），即使式（6）以等号触发也足够。
<!-- editorial-note:end note-4 -->

---

<a id="definition-2"></a>

### 定义 2：必须包含的素数幂集合

令

$$
K_*(n)=\frac1{q(n)},
\qquad
M(n)=\lfloor K_*(n)\rfloor,
$$

并定义

<a id="eq-9"></a>

$$
\boxed{
D(n)=\operatorname{lcm}(1,2,\ldots,M(n)).
}
\tag{9}
$$

当 $M(n)<2$ 时，取 $D(n)=1$。

<a id="theorem-2"></a>

### 定理 2：最小公倍数分类证书

<a id="eq-10"></a>

$$
\boxed{
D(n)\nmid n
\Longrightarrow R(n)<1.
}
\tag{10}
$$

等价地，任何潜在反例都必须满足

<a id="eq-11"></a>

$$
\boxed{
R(n)\ge1
\Longrightarrow D(n)\mid n.
}
\tag{11}
$$

#### 证明

首先，由 $q(n)>3/T$，

<a id="eq-12"></a>

$$
K_*(n)<T/3<T.
\tag{12}
$$

若 $D(n)\nmid n$，必存在素数幂

$$
p^e\le M(n)
$$

使 $v_p(n)<e$。令 $a=v_p(n)$，则

$$
p^{a+1}\le p^e\le M(n)\le K_*(n),
$$

所以

$$
p^{-a-1}\ge q(n).
$$

又因为 $-\log(1-x)>x$，

$$
d_p(a)>p^{-a-1}\ge q(n).
$$

同时 $p\le M(n)<T$，可以使用定理 1，得到 $R(n)<1$。∎

#### 这一步怎样用于分类

访问整数 $n$ 后，先检查它是否具备式（9）要求的全部素数幂。

只要缺少一个，就得到一个严格的 Robin 证书。证书中只须保留：

$$
n,\quad p,\quad v_p(n),\quad
d_p(v_p(n))\ge q(n).
$$

这是真正能够关闭证明分支的分类规则。

#### 还可以一次认证一个区间中的绝大多数整数

因为 $q(n)$ 随 $n$ 递减，所以 $M(n)$ 非递减。

固定 $N>5040$，记

$$
D_N=\operatorname{lcm}(1,\ldots,M(N)).
$$

则对所有 $n\ge N$，

$$
R(n)\ge1\Longrightarrow D_N\mid n.
$$

因此

<a id="eq-13"></a>

$$
\boxed{
\#\{N\le n<2N:R(n)\ge1\}
\le \frac N{D_N}+1.
}
\tag{13}
$$

而且有初等界

<a id="eq-14"></a>

$$
\operatorname{lcm}(1,\ldots,M)
\ge\frac{2^M}{M+1}.
\tag{14}
$$

证明式（14）只须注意：每个二项式系数 $\binom Mj$ 都整除该最小公倍数。对任意素数 $p$，其 $p$-进指数由若干个 $0$ 或 $1$ 的进位项组成，总数至多为 $\lfloor\log_p M\rfloor$。于是

$$
D_M\ge\max_j\binom Mj
\ge\frac1{M+1}\sum_j\binom Mj
=\frac{2^M}{M+1}.
$$

所以式（13）进一步给出

<a id="eq-15"></a>

$$
\boxed{
\frac1N\#\{N\le n<2N:R(n)\ge1\}
\le
(M(N)+1)2^{-M(N)}+\frac1N.
}
\tag{15}
$$

这已经把大量整数整体归入已证明类别。剩下的候选虽然越来越稀疏，仍须继续逐类证明。

<!-- editorial-note:start note-5 -->
**【编者局部说明：最小公倍数、端点与计数的范围】** $q(n)>0$ 且在 $n>5040$ 递减，所以 $M(n)$ 非递减，$D_N\mid D(n)$ 对整数 $n\ge N$ 成立；缺失素数幂时 $p\le M(n)<T$，定理 1 的范围没有遗漏。式（13）对实数或整数 $N>5040$ 都可按区间内的整数计数：不同 $D_N$ 的倍数相隔 $D_N$，长度为 $N$ 的半开区间至多含 $N/D_N+1$ 个，端点取整不会增大此界。式（14）用于整数 $M\ge1$；由阶乘的素数指数公式，$v_p\binom Mj=\sum_{k\ge1}(\lfloor M/p^k\rfloor-\lfloor j/p^k\rfloor-\lfloor(M-j)/p^k\rfloor)$，每项为零或一且 $p^k>M$ 后为零，故不超过 $\lfloor\log_pM\rfloor=v_p(\operatorname{lcm}(1,\ldots,M))$。空最小公倍数按原定义取一。候选密度上界不能推出候选不存在。
<!-- editorial-note:end note-5 -->

---

<a id="section-3"></a>

## 三、第二种递归：把证明义务传给更小的整数

分类之后，对留下的整数使用实际素因子结构。

<a id="definition-3"></a>

### 定义 3：删除一层素数幂的精确代价

<!-- editorial-note:start note-6 -->
**【编者局部说明：式（17）与证书边的定义域】** 以下原定义与原式保留。式（16）作为 $Z$ 的比值对正整数 $m=n/p$ 成立，但本文未在 $m=1$ 定义 $R(m)$；不能在该点使用式（17）。本节使用 $\delta(n,p)$、$\log R(m)$、式（17）、下降链或 Robin 证书传递时，均另加守卫 $m=n/p>5040$，并使链上每个节点仍大于 $5040$。定理 3 已明确含有这一守卫；整数下降到不能满足守卫时停止，不以越过边界本身作为终点证书。
<!-- editorial-note:end note-6 -->

设

$$
p^a\parallel n,\qquad a\ge1,
\qquad m=n/p.
$$

定义

$$
B_p(a)=p+p^2+\cdots+p^a.
$$

Euler 因子给出

<a id="eq-16"></a>

$$
\frac{Z(n)}{Z(m)}
=
1+\frac1{B_p(a)}.
\tag{16}
$$

因此，这条删除边的 Robin 增益为

<a id="eq-17"></a>

$$
\boxed{
\delta(n,p)
=
\log R(m)-\log R(n)
=
\log\frac{\log\log n}{\log\log m}
-\log\left(1+\frac1{B_p(a)}\right).
}
\tag{17}
$$

这个局部关系中，Euler 常数 $\gamma$ 完全消掉了。

<a id="theorem-3"></a>

### 定理 3：可证明的删除条件

若

$$
m=n/p>5040
$$

且

<a id="eq-18"></a>

$$
\boxed{
B_p(a)\log p
\ge
(\log n)\log\log n,
}
\tag{18}
$$

则

<a id="eq-19"></a>

$$
\boxed{
R(n)<R(n/p).
}
\tag{19}
$$

所以，只要 $n/p$ 已经有证书，$n$ 也得到证书。

#### 证明

令

$$
f(t)=\gamma+\log\log t,\qquad t>1.
$$

有

$$
f'(t)=\frac1{t\log t},
\qquad f''(t)<0.
$$

记 $T=\log n$、$h=\log p$。于是

$$
f(T)-f(T-h)
=
\int_{T-h}^{T}\frac{du}{u\log u}
>
\frac h{T\log T}.
$$

另一方面，

$$
\log\left(1+\frac1{B_p(a)}\right)
<
\frac1{B_p(a)}
\le
\frac h{T\log T}.
$$

代入式（17），得到 $\delta(n,p)>0$。∎

特别地，由 $B_p(a)\ge p$，得到一个简单分类：

<a id="eq-20"></a>

$$
\boxed{
p\ge\log n,\quad n/p>5040
\Longrightarrow R(n)<R(n/p).
}
\tag{20}
$$

---

### 贪心规则与有限终止

在所有已经证明满足式（18）的删除边中，选择认证增益下界最大的一条，进行

$$
n\longmapsto n/p.
$$

每一步至少把当前整数除以 $2$，所以删除过程有限终止。

这里的“最大增益”是当前节点上的局部贪心选择；有限终止来自整数下降，不需要假设 RH。

对下降链

$$
n_0>n_1>\cdots>n_s,
$$

有精确恒等式

<a id="eq-21"></a>

$$
\boxed{
-\log R(n_0)
=
-\log R(n_s)+\sum_{j=0}^{s-1}\delta(n_j,p_j).
}
\tag{21}
$$

因此，终点的证书可以沿整条路径传回。

---

### 这个传证过程本身就可以递归放入 AURIC 三轴

假设终点有可靠上界

$$
R(n_s)\le C.
$$

若已经累计得到正增益下界 $d_1,\ldots,d_k$，令

$$
q_k=1-\exp\left(-\sum_{j=1}^k d_j\right).
$$

那么

$$
R(n_0)\le C(1-q_k).
$$

加入一条新的正增益下界 $d$，定义

$$
b=1-e^{-d}.
$$

则

<a id="eq-22"></a>

$$
\boxed{
q_{k+1}=q_k+(1-q_k)b.
}
\tag{22}
$$

对应的三个归一化读出是

<a id="eq-23"></a>

$$
\boxed{
\left(
q_k,\,
(1-q_k)b,\,
(1-q_k)(1-b)
\right).
}
\tag{23}
$$

三项分别表示已累计衰减、本步新增衰减、尚存比例，并且总和严格为 $1$。

只要

$$
C(1-q_k)<1,
$$

原整数就取得 Robin 证书。

这里同时保留了你关心的两种运算：

$$
1-q_k=\prod_j e^{-d_j},
$$

$$
-\log(1-q_k)=\sum_jd_j.
$$

**乘法积累、对数加法与三轴守恒，在同一份实际证明账本中相容。**

<!-- editorial-note:start note-7 -->
**【编者局部说明：增益下界和终点的条件】** 式（18）只提供充分删除条件，局部贪心在当前已取得的有限个合法边下界中比较，不声称全局最优；严格整数下降已足以保证每条下降链有限。式（21）是同一条链的对数差逐项消去。式（22）–（23）以已经取得的 $C>0$ 及相应边的可靠正下界 $0<d_j\le\delta(n_j,p_j)$ 为条件；未计入的合法边增益为正，可以忽略而维持上界。$q_0=0$，$0\le q_k<1$，$0<b<1$，所以三项非负、和为一。终点上界的取得以及各下界的严格认证是额外证据义务，三轴归一化本身不取得它们。
<!-- editorial-note:end note-7 -->

#### 一个直接得到的无限安全类

若 $m>5040$ 已有 Robin 证书，素数 $p\ge2\log m$，则

$$
\log(mp)=\log m+\log p
\le p/2+p/2=p.
$$

所以式（20）给出

$$
R(mp)<R(m)<1.
$$

项目还证明了：在 $\log m\ge3$ 时，一条通过测试的首层素数边，可以认证整条素数幂方向。因此可进一步得到

<a id="eq-24"></a>

$$
\boxed{
R(m)<1,\quad p\ge2\log m
\Longrightarrow
R(mp^k)<1\quad\forall k\ge0.
}
\tag{24}
$$

<a id="source-5"></a>

这使一个已证明节点能够扩展成无穷多个已证明节点。[来源：项目 PrimeFiberPropagation，定理 1.4—1.5](https://github.com/the-omega-institute/trureturing/blob/9ceb721e13c64eb4b1c71a43238a2b2fc4770093/Blueprint/D5/S3/Arith/Robin/PrimeFiberPropagation.md)。

<!-- editorial-note:start note-8 -->
**【编者局部说明：整条素数方向所需的首层测试】** 式（24）沿用本段 $m>5040$ 的条件。固定版本的 PrimeFiberPropagation 定理 1.4–1.5 要求 $\log m\ge3$、$R(m)<1$ 和首层的 $\operatorname{EdgeTest}(m,p)$，并不要求 $p\nmid m$；不能仅从 $R(mp)<R(m)$ 倒推首层测试。这里令 $L=\log m$、$h=\log p$、$B=B_p(v_p(mp))$。由 $\log p\le p/2$ 和 $p\ge2L$ 得 $L+h\le p$，所以 $Bh\ge(L+h)\log(L+h)$。于是

$$
\left(\frac{Z(mp)}{Z(m)}-1\right)\log L
=\frac{\log L}{B}
\le\frac{h\log L}{(L+h)\log(L+h)}
<\frac h{L+h}
<\log(1+h/L).
$$

这正是该来源的首层测试，且 $m>5040$ 保证 $L>3$，从而可以对所有 $k\ge0$ 引用整条素数方向定理。$B$ 使用 $mp$ 中的实际指数，所以 $p\mid m$ 也在范围内。
<!-- editorial-note:end note-8 -->

---

<a id="section-4"></a>

## 四、关键推进：误差可以在同一来源上继续递归，而且贪心配对具有全层最优性

现在处理尚未被前两类证书解决的整数。

项目新文档第八节已经给出一个精确的 Robin 关系损失分解。我们把它继续发展成有限终止的递归。

<a id="definition-4"></a>

### 定义 4：由实际整数确定尺度

固定同一个 $n>5040$，以

<a id="eq-25"></a>

$$
\boxed{
\log n=\sum_{p<K}\log\frac Kp
}
\tag{25}
$$

唯一确定 $K>2$。

令

$$
r=\frac1K,
\qquad
s_p=p^{-v_p(n)-1},
$$

以及二元 KL 损失

$$
L_p=
\operatorname{kl}(r\Vert s_p)
=
r\log\frac r{s_p}
+(1-r)\log\frac{1-r}{1-s_p}.
$$

记

$$
S=\sum_{p<K}L_p,
\qquad
c_K=\frac K{K-1}.
$$

再定义

$$
B(K)=
\sum_{p<K}
\log\frac{1-1/K}{1-1/p},
$$

$$
G(K)=B(K)-\gamma-\log\Lambda,
$$

$$
U_K(n)=
\sum_{\substack{p\ge K\\p\mid n}}
\left[
\frac{v_p(n)\log p}{K-1}
-\log\left(\sum_{j=0}^{v_p(n)}p^{-j}\right)
\right].
$$

项目给出

$$
U_K(n)\ge0
$$

和精确恒等式

<a id="eq-26"></a>

$$
\boxed{
\log R(n)=G(K)-c_KS-U_K(n).
}
\tag{26}
$$

因此真正需要证明的是

<a id="eq-27"></a>

$$
c_KS+U_K(n)>G(K).
\tag{27}
$$

<a id="source-6"></a>

这些量全部来自同一个实际整数及其真实素因子指数。[来源：新理论卷，第八节，式（28）及其推导](https://github.com/the-omega-institute/trureturing/blob/3f98ae45e29bd5fb6ef8dd7d1e5bf39c2723520e/docs/develop/theory/AURIC_RELATION_SCALE_RECOVERY_THREE_CANDIDATE_OPTIMIZATION_AND_ROBIN_CERTIFICATES.md)。

<!-- editorial-note:start note-9 -->
**【编者局部说明：尺度与固定来源分解的对应】** 设 $\mathcal T_0(K)=\sum_{p<K}\log(K/p)$。它在 $K=2$ 为零，在 $K>2$ 连续严格递增且无界；每跨过一个素数，新项从零开始，相邻素数之间导数为 $\#\{p:p<K\}/K>0$。故式（25）的 $K>2$ 唯一，活动素数有限且至少一个，$0<r,s_p<1$。固定来源第八节的 $\mathcal Z$ 就是本文 $Z$，$\mathcal T_0(K)=T$，所以其中 $G=B-\gamma-\log\log\mathcal T_0$ 正好是本文 $B-\gamma-\log\Lambda$。其尾项使用全部实际 $p\ge K$ 的因子，包含可能的 $p=K$。

具体令 $a_p=v_p(n)$、$u_p=a_p\log p$、$h_p(u)=\log((1-e^{-u}/p)/(1-1/p))$、$g_{p,K}(u)=h_p(u)-u/(K-1)$。对 $p<K$，$u_p^*=\log(K/p)$，且

$$
g_{p,K}(u_p^*)-g_{p,K}(u_p)
=\log\frac{1-r}{1-s_p}+\frac1{K-1}\log\frac r{s_p}
=c_KL_p.
$$

对 $p\ge K$，$g_{p,K}(0)=0$ 且 $g'_{p,K}(u)=1/(pe^u-1)-1/(K-1)\le0$，故尾项的每一项非负。再由同一整数的 $\sum_pu_p=T=\sum_{p<K}u_p^*$ 及 $\log Z(n)=\sum_ph_p(u_p)$，相加得到 $B(K)-\log Z(n)=c_KS+U_K(n)$，即式（26）。二元 KL 的非负性保证 $L_p\ge0$；此对应不把独立选择的尺度或不同整数的最优值拼在一起。
<!-- editorial-note:end note-9 -->

---

<a id="definition-5"></a>

### 定义 5：两个损失组成一个 AURIC 三结果观察

对两个素数方向 $i,j$，采用三结果参考律和比较律

$$
P_{ij}=
\bigl(r,(1-r)r,(1-r)^2\bigr),
$$

<a id="eq-28"></a>

$$
Q_{ij}=
\bigl(s_i,(1-s_i)s_j,(1-s_i)(1-s_j)\bigr).
\tag{28}
$$

它们各自都是归一化的三结果概率律，因而可以放入金字塔的指定三顶点混合子族。

直接展开对数，得到

<a id="eq-29"></a>

$$
\boxed{
D(P_{ij}\Vert Q_{ij})
=
L_i+(1-r)L_j.
}
\tag{29}
$$

于是原总损失分成

<a id="eq-30"></a>

$$
L_i+L_j
=
\underbrace{L_i+(1-r)L_j}_{\text{本次已经读取}}
+
\underbrace{rL_j}_{\text{剩余}}.
\tag{30}
$$

若 $L_i\ge L_j$，剩余就是较小损失的 $r$ 倍。

**现在可以把 $rL_j$ 送入下一轮，继续使用同一个关系。**

<!-- editorial-note:start note-10 -->
**【编者局部说明：三结果载体与散度】** 对严格正的有限概率向量，$D(P\Vert Q)=\sum_xP(x)\log(P(x)/Q(x))$；$\operatorname{Bern}(t)$ 约定 $\Pr(X=1)=t$。式（28）的三个事件可取 $X_i=1$、$X_i=0,X_j=1$、$X_i=X_j=0$，参考和比较坐标分别采用参数 $(r,r)$ 与 $(s_i,s_j)$ 的辅助乘积律。它们互斥且穷尽，归一化后直接按 KL 链式展开得到式（29）；这是指定三顶点子族的表示，未从实际素因子推出随机独立性，也不把任意原生联合律识别成这一子族。
<!-- editorial-note:end note-10 -->

---

<a id="theorem-4"></a>

### 定理 4：递归损失读取有限终止

设共有

$$
m=\#\{p:p<K\}
$$

个局部损失。每一层执行：

- 将活动项尽可能两两配对；
- 每对先读取较大的损失；
- 把较小损失乘以 $r$，送到下一层；
- 若有一个单点，完整读取它。

记第 $h$ 层后累计读取量为 $J_h$，剩余为 $E_h$。则

$$
S=J_h+E_h,
$$

<a id="eq-31"></a>

$$
\boxed{
E_{h+1}\le\frac1{2K}E_h,
}
\tag{31}
$$

因而

<a id="eq-32"></a>

$$
\boxed{
E_h\le(2K)^{-h}S.
}
\tag{32}
$$

而且当

$$
H=\lfloor\log_2m\rfloor+1
$$

时，

<a id="eq-33"></a>

$$
\boxed{
E_H=0,\qquad J_H=S.
}
\tag{33}
$$

#### 证明

一对活动损失 $A\ge B$ 只留下 $rB$，而

$$
rB\le\frac r2(A+B).
$$

单点则全部读取，不留剩余。对全部配对求和，得到式（31）。

另一方面，每层活动项数量满足

$$
m_{h+1}=\lfloor m_h/2\rfloor,
$$

所以

$$
m_h=\left\lfloor\frac m{2^h}\right\rfloor.
$$

在上述 $H$ 层后活动项为零，故剩余精确为零。∎

这里得到的是两种独立的进度保证：

$$
\text{剩余量几何缩小},
\qquad
\text{活动项数量至少减半}.
$$

---

<a id="theorem-5"></a>

### 定理 5：大小两半配对，在每一个深度都最优

将原始损失按升序排列：

$$
L_{(1)}\le L_{(2)}\le\cdots\le L_{(m)}.
$$

每层把较小的一半分别与较大的一半配对；若为奇数，从较大部分取一个单点完整读取。

则第 $h$ 层的剩余恰为

<a id="eq-34"></a>

$$
\boxed{
E_h=
r^h
\sum_{i=1}^{\lfloor m/2^h\rfloor}L_{(i)}.
}
\tag{34}
$$

而且在所有采用相同“每层尽可能配对、单点完整读取”规则的方案中，它同时最小化每个深度的剩余量。

#### 证明

任何一层配对，都会从每对中留下一个活动项。因此，第 $h$ 层必留下

$$
q_h=\lfloor m/2^h\rfloor
$$

个不同的原始损失，每项都乘以 $r^h$。

它们的总和不可能小于原始 $q_h$ 个最小损失之和。

上述贪心方案第一层留下最小的 $\lfloor m/2\rfloor$ 项，第二层留下其中最小的 $\lfloor m/4\rfloor$ 项，依次归纳，恰好取得这个下界。∎

这给你的“分类、贪心、递归”一个精确结论：

> **在这一关系损失任务上，贪心配对有完整的最优性证明，并且同一套选择在所有递归深度上同时最优。**

这个最优性有明确的操作范围；它不是对任意证明方法的全局最优性宣称。

<!-- editorial-note:start note-11 -->
**【编者局部说明：共同权重与最优性的操作范围】** 取 $E_0=S,J_0=0,m_0=m\ge1$。第 $h$ 层每个活动项都有共同权重 $r^h$，故继续比较原始 $L_i$ 与比较加权项相同；零损失和相等损失可任意固定次序。每次配对留下一个不同的原始坐标，单点完全读取，所以 $m_h=\lfloor m/2^h\rfloor$，并且 $H=\lfloor\log_2m\rfloor+1$ 对 $m=1$ 也成立。定理 5 只比较每层尽可能配对、每对留一个坐标并乘 $r$、单点全读的操作类；任意该类方案的 $q_h$ 个存活者都给出最小 $q_h$ 项之和这个下界，所述大小两半策略在全部深度同时取得它。配对和打破平局由固定参数决定，不依据尚未读取的随机取值。
<!-- editorial-note:end note-11 -->

---

<a id="section-5"></a>

## 五、这套递归确实可以来自同一个固定来源，而不是只对数值做形式拆分

这一点值得单独证明。

把 $p<K$ 的素数方向编号为 $1,\ldots,m$。取固定有限来源

$$
\Omega=\{0,1\}^m,
$$

以及两个概率律

<a id="eq-35"></a>

$$
\mathbb P
=
\bigotimes_{i=1}^m\operatorname{Bern}(r),
\qquad
\mathbb Q
=
\bigotimes_{i=1}^m\operatorname{Bern}(s_i).
\tag{35}
$$

这是根据同一个整数参数定义的辅助概率来源；其独立性属于模型定义。

有

$$
D(\mathbb P\Vert\mathbb Q)=\sum_iL_i=S.
$$

<a id="theorem-6"></a>

### 定理 6：存在嵌套观察，精确实现上述递归损失

可以构造观察记录

$$
O_0\preceq O_1\preceq\cdots\preceq O_H,
$$

使得

<a id="eq-36"></a>

$$
\boxed{
J_h=D(\mathbb P_{O_h}\Vert\mathbb Q_{O_h}),
}
\tag{36}
$$

并且

<a id="eq-37"></a>

$$
\boxed{
S-J_h
=
r^h\sum_{i\text{ 在第 }h\text{ 层仍活动}}L_i.
}
\tag{37}
$$

#### 证明

维护以下不变量：

每个活动块中，除一个活动坐标 $X_i$ 外，其他坐标都已完全读取。$X_i$ 仅在一个触发事件 $A_i^{(h)}$ 下保持隐藏；该事件由 $h$ 个已经读取的祖先坐标均为 $1$ 构成，所以

$$
\mathbb P(A_i^{(h)})=r^h.
$$

不同活动块包含互不相交的原始坐标。

初始时每块只有一个坐标，触发事件是整个空间，不变量成立。

现在配对两个活动块 $i,j$：

1. 完全揭示 $X_i$；
2. 当 $X_i=0$ 时，揭示此前隐藏的 $X_j$；
3. 当 $X_i=1$ 时，继续保留 $X_j$ 原来的隐藏状态。

于是新隐藏事件为

$$
A_j^{(h+1)}
=
A_j^{(h)}\cap\{X_i=1\}.
$$

由于两个旧块不交，

$$
\mathbb P(A_j^{(h+1)})=r^{h+1}.
$$

所有旧记录都被保留，所以这确实是观察的细化。

最后，用有限概率空间的 KL 链式分解：

$$
D(\mathbb P\Vert\mathbb Q)
=
D(\mathbb P_{O_h}\Vert\mathbb Q_{O_h})
+
\mathbb E_{\mathbb P}
D\bigl(\mathbb P(\cdot\mid O_h)\Vert
\mathbb Q(\cdot\mid O_h)\bigr).
$$

每个仍隐藏的 $X_i$ 在其触发事件中贡献 $L_i$，触发概率是 $r^h$。因此条件损失就是式（37）。∎

<!-- editorial-note:start note-12 -->
**【编者局部说明：定理 6 的观察纤维与条件律】** 上述原证明保留；仅有触发概率还不足以得出条件 KL，所需的加强不变量如下。把读出掩码、已读坐标的取值以及全部旧记录都纳入 $O_h$。对每个可达记录 $o$，隐藏集合 $H(o)$ 由该记录确定，纤维 $O_h^{-1}(o)$ 恰好固定所有已读坐标，而允许 $H(o)$ 中的坐标自由取值。初始常值记录满足此性质。合并时先完全读取 $X_i$，再由已读的 $X_i$ 和旧掩码决定是否读取 $X_j$；其决策不检验仍隐藏坐标的取值，旧纤维仅被实际揭示的坐标切分。因此归纳后仍是这种坐标柱体，而非仅知道其总概率的事件。

两个乘积律均全支撑，所以可达记录及其纤维在两律下相同。分别条件于同一个 $o$，固定坐标给出相同的点质量，自由坐标仍分别服从参数为 $r$ 和 $s_i$ 的独立 Bernoulli 因子，故

$$
\mathbb P(\cdot\mid O_h=o)=\delta_{x_{H(o)^c}}\otimes\bigotimes_{i\in H(o)}\operatorname{Bern}(r),\qquad
\mathbb Q(\cdot\mid O_h=o)=\delta_{x_{H(o)^c}}\otimes\bigotimes_{i\in H(o)}\operatorname{Bern}(s_i).
$$

条件 KL 因而等于 $\sum_{i\in H(o)}L_i$。各活动块的坐标集合不交，新触发条件为原来的 $h$ 个不同已读祖先均为一，再加来自另一个块、现在已完全读取的 $X_i=1$；它独立于仍隐藏的 $X_j$。所以对每个第 $h$ 层活动坐标，$\mathbb P(i\in H(O_h))=r^h$。$\mathbb Q$ 下相应触发概率是祖先参数 $s$ 的乘积，一般不是 $r^h$；KL 链式分解的外层平均使用的是 $\mathbb P$。于是

$$
\mathbb E_{\mathbb P}D\bigl(\mathbb P(\cdot\mid O_h)\Vert\mathbb Q(\cdot\mid O_h)\bigr)
=\sum_{i\text{ 第 }h\text{ 层活动}}\mathbb P(i\in H(O_h))L_i
=r^h\sum_{i\text{ 第 }h\text{ 层活动}}L_i.
$$

这补足式（37）所需的条件律论证。$O_h$ 累计保存各块和各层的记录，整个记录的值域不受三个值限制；“三结果”指局部观察规则，不是整个累计历史的字母表大小。
<!-- editorial-note:end note-12 -->

**所以，递归剩余量是同一来源的真实条件信息损失。每一层都增加已取得信息，最终完整恢复。**

### 酉记录实现

由于每个 $O_h$ 是有限来源上的确定函数，可以将其编码为固定长度位串，并定义

<a id="eq-38"></a>

$$
\boxed{
U_h|x,z\rangle
=
|x,z\oplus O_h(x)\rangle.
}
\tag{38}
$$

它是正交基上的置换，而且自身为逆，因此

$$
U_h^\dagger U_h=I.
$$

这里原始位串与读出记录都保留在同一个状态中。于是，上述递归观察能够得到一个真实的酉记录实现；读出残差的减少来自记录增多，来源信息没有被擦除。

<!-- editorial-note:start note-13 -->
**【编者局部说明：有限编码与实现结论的范围】** 有限来源上的累计记录也只有有限多个值，选取足够长的单射位串编码即可；未用编码位置也照样执行 XOR。对每个 $x$，两次异或同一编码恢复 $z$，所以式（38）在完整正交基上是自逆置换，线性延拓为酉算子。各层旧历史保留在记录中；此为有限维数学实现的存在陈述，不包含原生控制权、物理制备、获取成本或具体设备实现的结论。
<!-- editorial-note:end note-13 -->

---

<a id="section-6"></a>

## 六、把每一层递归直接变成 Robin 区间证书

令

$$
q_h=\left\lfloor\frac m{2^h}\right\rfloor,
\qquad
\theta_h=r^h\frac{q_h}{m}.
$$

因为最小若干项的平均值不超过全体平均值，式（34）给出

$$
E_h\le\theta_h S.
$$

由 $J_h=S-E_h$，得到

<a id="eq-39"></a>

$$
\boxed{
J_h\le S\le\frac{J_h}{1-\theta_h},
\qquad h\ge1.
}
\tag{39}
$$

代入项目的精确 Robin 分解，得到

<a id="eq-40"></a>

$$
\boxed{
G(K)-U_K(n)-\frac{c_KJ_h}{1-\theta_h}
\le
\log R(n)
\le
G(K)-U_K(n)-c_KJ_h.
}
\tag{40}
$$

因此，每一层都有一个可以立即使用的停止条件：

<a id="eq-41"></a>

$$
\boxed{
c_KJ_h+U_K(n)>G(K)
\Longrightarrow R(n)<1.
}
\tag{41}
$$

一旦通过，就不必继续读取剩余项。

最终 $h=H$ 时，$\theta_H=0$，区间退化为精确恒等式

$$
\log R(n)=G(K)-U_K(n)-c_KJ_H.
$$

**这一轮已经证明了你提出的递归机制的一段核心内容：对误差继续做 AURIC 分析，可以有统一收缩率、最优贪心选择和有限终止。**

有限终止在这里意味着关系损失被完整恢复；恢复出来的算术值是否严格为负，仍由式（41）所表达的真实不等式决定。

<!-- editorial-note:start note-14 -->
**【编者局部说明：区间与精确性的界限】** 式（39）–（40）使用定理 5 的配对策略。$h\ge1$ 时 $0\le\theta_h\le r^h/2<1$；$q_h=0$ 时残差为零，其余情形由最小 $q_h$ 项的平均值不超过全体平均值推出 $E_h\le\theta_hS$。所以 $J_h\le S$，且 $J_h=S-E_h\ge(1-\theta_h)S$；乘以 $-c_K<0$ 后上下界方向正好得到式（40）。式（41）需要严格大于；等号不足以认证严格 Robin。最终恢复是有限个观察层后的符号恒等式，不意味着机器可在有限精度下精确计算超越量、判定所有相等情形，或总能取得所需严格符号。
<!-- editorial-note:end note-14 -->

---

<a id="section-7"></a>

## 七、把三部分拼成一套完整的递归证明规则

现在每个外层整数 $a_t>5040$ 都按以下规则处理。

| 阶段 | 操作 | 已证明的作用 |
|---|---|---|
| 遍历 | 按项目序列提交 $a_t$ | 每个正整数最终被处理 |
| 整类分类 | 检查 $D(a_t)\mid a_t$ | 不整除时立即取得 Robin 证书 |
| 已有类别 | 复用项目的已证支撑、素数方向和指数模式 | 一份证书可覆盖一类整数 |
| 贪心下降 | 删除满足式（18）的素因子，或执行有证据的指数交换 | 将证明义务传给更小整数 |
| 三轴递归 | 对剩余目标按式（34）读取 KL 损失 | 每层给出式（40）的可靠区间 |
| 回传 | 沿式（21）累计裕量 | 认证下降链上的全部祖先 |

<a id="source-7"></a>

项目已有的指数标准形还可以用于分类：每个正整数都有一个不更大的、素数支撑为初始段且指数非增的代表，其 $Z$ 值不小于原整数；只要该代表大于 $5040$，它的 Robin 证书就能传回原整数。[来源：PrefixNormalForm，定理 1.1](https://github.com/the-omega-institute/trureturing/blob/9ceb721e13c64eb4b1c71a43238a2b2fc4770093/Blueprint/D5/S3/Arith/ExponentExchange/PrefixNormalForm.md)。

<!-- editorial-note:start note-15 -->
**【编者局部说明：标准形与调度的条件】** 所引固定版本定理给出 $1\le m\le n$、$\omega(m)=\omega(n)$、对所有素数 $p<q$ 有 $v_q(m)\le v_p(m)$ 及 $Z(n)\le Z(m)$；非增指数也排除了素数支撑的空缺。只有取得 $m>5040$ 及其严格 Robin 证书后，才有 $Z(n)\le Z(m)<e^\gamma\log\log m\le e^\gamma\log\log n$。表中的指数交换须有其自身的合法下降和传证依据，不能把任意交换当作已认证边。下面的交错调度以每次推进能完成为条件，保证已提交任务不被一个难节点阻断；覆盖访问和公平推进均不证明每个任务最终取得严格符号证书。
<!-- editorial-note:end note-15 -->

调度上需要让每个尚未结束的任务持续得到推进。例如，第 $t$ 轮提交 $a_t$，并给前 $t$ 个未完成任务各推进一步。这样，一个难以判定的节点不会阻止后续整数被访问。

每个节点保留实际整数、指数剖面、尺度 $K$、读出记录和证书。AURIC 三轴负责对指定任务进行归一化读出；这些实际来源保证各层仍在证明同一个算术命题。

---

<a id="section-8"></a>

## 八、继续逼近全局证明：最小反例会被压到怎样的剩余类别？

这里还可以证明一个具体的归约定理。

假设 Robin 有反例，取数值最小的一个 $n_*$。

项目已经证明：大于 $5040$、不同素因子个数至多 $8$ 的整数都满足 Robin。因此

$$
\omega(n_*)\ge9.
$$

<a id="source-8"></a>

这是复用项目既有定理；它的来源说明包含核验枚举，本轮没有重做该枚举。[来源：FewDistinctPrimes，定理 1.1](https://github.com/the-omega-institute/trureturing/blob/9ceb721e13c64eb4b1c71a43238a2b2fc4770093/Blueprint/D5/S3/Arith/Robin/FewDistinctPrimes.md)。

于是，从 $n_*$ 删除一个素因子后，仍至少保留八个不同素因子，所得整数必大于 $5040$。所以全部删除边都可以应用前面的守卫条件。

<!-- editorial-note:start note-16 -->
**【编者局部说明：最小反例的全部小整数守卫】** FewDistinctPrimes 的固定版本定理 1.1 针对全部整数 $n>5040$ 和任意指数、任意素数支撑，只要求 $\omega(n)\le8$；其历史核验枚举是来源所述的证明组成，本文不重做也不新增该枚举。于是弱反例 $R(n_*)\ge1$ 必有 $\omega(n_*)\ge9$。任何有至少八个不同素因子的正整数，都至少包含六个不同素数的乘积，且 $2\cdot3\cdot5\cdot7\cdot11\cdot13>5040$，所以删除一个素因子后的整数仍大于 $5040$。下文交换 $m=n_*p/q$ 时，若 $p$ 原先缺失，去掉 $q$ 的一层最多失去一个旧素因子，却增加 $p$；若 $p$ 原已出现，只可能失去 $q$ 这一个素因子。因此交换后的 $m$ 也至少含八个不同素因子，必有 $5040<m<n_*$，才可引用最小性。
<!-- editorial-note:end note-16 -->

<a id="theorem-7"></a>

### 定理 7：最小反例的必要结构

若最小反例 $n_*$ 存在，则它必须同时满足：

<a id="eq-42"></a>

$$
\boxed{D(n_*)\mid n_*;}
\tag{42}
$$

<a id="eq-43"></a>

$$
\boxed{
B_p(v_p(n_*))\log p
<
(\log n_*)\log\log n_*
\quad\text{对每个 }p\mid n_*;
}
\tag{43}
$$

<a id="eq-44"></a>

$$
\boxed{
P^+(n_*)<\log n_*,
}
\tag{44}
$$

其中 $P^+(n_*)$ 为最大素因子。

此外，其素因子必须是一个初始素数段，且指数非增。

#### 证明

式（42）由定理 2。

若式（43）对某个 $p$ 不成立，定理 3 给出

$$
R(n_*)<R(n_*/p).
$$

但 $n_*/p$ 位于 $5040$ 与 $n_*$ 之间，由最小性满足 Robin，矛盾。因此式（43）成立。

若某个 $p\ge\log n_*$，则式（20）同样产生矛盾，得到式（44）。

最后，取素数 $p<q$、$q\mid n_*$，记

$$
a=v_p(n_*),\qquad b=v_q(n_*),
\qquad m=n_*\frac pq<n_*.
$$

若

$$
B_p(a+1)\le B_q(b),
$$

则

$$
\frac{Z(m)}{Z(n_*)}
=
\frac{1+1/B_p(a+1)}
{1+1/B_q(b)}
\ge1.
$$

又因 $m<n_*$，其双对数分母更小，所以 $R(m)>R(n_*)\ge1$，违反最小性。

因此必须有

<a id="eq-45"></a>

$$
\boxed{
B_p(v_p(n_*)+1)>B_q(v_q(n_*))
\quad(p<q,\ q\mid n_*).
}
\tag{45}
$$

若 $p$ 缺失，左侧为 $p$，而右侧至少为 $q>p$，矛盾；所以素数支撑无空缺。

若较小素数的指数小于较大素数的指数，则逐项比较又违反式（45）。故指数非增。∎

<!-- editorial-note:start note-17 -->
**【编者局部说明：交换比值与式（45）的严格性】** $p<q$、$q\mid n_*$ 保证 $m=n_*p/q$ 为正整数且严格更小。加一层 $p$ 的 $Z$ 因子为 $1+1/B_p(a+1)$，删一层 $q$ 的因子为 $1/(1+1/B_q(b))$，故原文比值成立。在上述 $m>5040$ 守卫下，$\log\log m$ 为正且严格小于 $\log\log n_*$；即使 $Z(m)=Z(n_*)$，也仍有 $R(m)>R(n_*)$。若 $p$ 缺失则 $a=0$，$B_p(1)=p<q\le B_q(b)$；若 $a<b$ 则 $a+1\le b$，且 $\sum_{j=1}^{a+1}p^j<\sum_{j=1}^{a+1}q^j\le B_q(b)$。两种情况均与式（45）矛盾，从而得到无空缺支撑和非增指数。
<!-- editorial-note:end note-17 -->

---

### 对最小反例，项目分解中的大素数尾项甚至完全消失

由式（25），有一个初等估计：

<a id="eq-46"></a>

$$
\begin{aligned}
T
&=\sum_{p<K}\log(K/p)\\
&\le\sum_{2\le j\le\lfloor K\rfloor}\log(K/j)\\
&\le\int_1^K\log(K/x)\,dx\\
&=K-1-\log K<K.
\end{aligned}
\tag{46}
$$

因此，对上述最小反例，

$$
P^+(n_*)<T<K.
$$

所有实际素因子都小于 $K$，所以

<!-- editorial-note:start note-18 -->
**【编者局部说明：式（46）的非整数端点】** 对固定实数 $K>2$，函数 $f(x)=\log(K/x)$ 在 $[1,K]$ 非负递减。每个 $2\le j\le\lfloor K\rfloor$ 都有 $f(j)\le\int_{j-1}^jf(x)\,dx$，而剩余区间 $[\lfloor K\rfloor,K]$ 的积分非负；若 $K$ 恰为整数，新增的端点项 $f(K)=0$。因此式（46）对非整数与整数 $K$ 都成立。由式（44）的 $P^+(n_*)<T<K$ 得尾和无实际素因子项，严格得到式（47）。
<!-- editorial-note:end note-18 -->

<a id="eq-47"></a>

$$
\boxed{U_K(n_*)=0.}
\tag{47}
$$

剩余的核心不等式变成

<a id="eq-48"></a>

$$
\boxed{
\frac K{K-1}
\sum_{p<K}
\operatorname{kl}\!\left(
\frac1K\Big\Vert p^{-v_p(n_*)-1}
\right)
>
G(K).
}
\tag{48}
$$

而且这里的整数已经受到式（42）—（45）的全部约束。

这比对所有任意指数配置直接讨论，更集中：**只需要排除这一类没有可用下降边、素数支撑连续、指数有序、满足强制素数幂整除条件的候选。**

---

### 本轮到达的位置

现在已经严格证明：

- 贪心排列保证外层无遗漏；
- 单素数修复给出整类 Robin 正性证书；
- 实际整数下降给出有限证据链和可累计的裕量；
- 关系损失可以在同一来源上继续递归；
- 大小两半配对同时最小化各层剩余；
- 读出残差以明确比例收缩，并在有限层精确归零；
- 整个观察过程可以通过保留来源的酉记录实现；
- 潜在最小反例被归约到式（42）—（48）所描述的严格类别。

**还没有证明的是：这个剩余类别中的每个实际整数都满足式（48）。** 观察误差归零，使我们准确取得左侧；算术分类与下降使候选范围显著缩小。要完成 RH，还需要给这类候选的左侧建立一个统一、严格超过 $G(K)$ 的下界。

因此，下一步的证明对象已经可以固定为式（48）：在式（42）—（45）的共同约束下，继续用 AURIC 递归把每层取得的正损失累计起来，并证明它必在某一层越过 $G(K)$。这才是把目前已经闭合的遍历、分类、贪心和酉记录机制，接成完整 RH 证明所需的最后一种算术进展。
<!-- original-manuscript:end -->
