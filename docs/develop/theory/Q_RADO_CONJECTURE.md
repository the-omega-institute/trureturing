# Saaltink 的精确 $q$-Rado 判据

设 $F$ 为任意有限域，$V$ 为有限维 $F$-向量空间，$\mathcal L(V)$ 为其子空间格。设 $M=(V,r)$ 为任意 $q$-拟阵，即 $r:\mathcal L(V)\to\mathbb Z$ 满足
$$
0\le r(U)\le\dim U,\qquad U\le W\Longrightarrow r(U)\le r(W),
$$
以及
$$
r(U+W)+r(U\cap W)\le r(U)+r(W).
$$
子空间 $C$ 称为 $M$-独立的，如果 $r(C)=\dim C$；$M$ 的基是极大独立子空间。记 $n=\dim V$、$R=r(V)$。

给定任意有限指标集 $I$ 及允许重复的子空间族 $(X_i)_{i\in I}$，记 $k=|I|$，并令
$$
X(J)=\bigcap_{j\in J}X_j,\qquad X(\varnothing)=V,\qquad
\overline n(U)=\min_{B\text{ 为 }M\text{-基}}\dim(B\cap U).
$$
称 $T\le V$ 为该族的满 $q$-横截，如果 $\dim T=k$，且 $T$ 的每一个向量基都能双射标号为 $(t_i)_{i\in I}$，使得 $t_i\notin X_i$。这些定义取自 [S, §3、Definition 14 及 Conjecture 1 前的 bar nullity 定义]。

**定理。** 对上述任意 $F,V,M,I,(X_i)$，存在一个既是 $M$-独立又是满 $q$-横截的 $T$，当且仅当
$$
\overline n\bigl(X(J)\bigr)+|J|\le\overline n(V)
\qquad\text{对每个 }J\subseteq I. \tag{1}
$$
这是 [S, Conjecture 1] 的原式判据。

**证明。** 先使用 $q$-拟阵的闭包性质 [JP, Propositions 2.5--2.6、Definition 9.5]。对同一 $V$ 上的任意 $q$-拟阵 $P$ 及子空间 $C$，其闭包可写为
$$
H_P(C)=\sum\{A:C\le A,\ r_P(A)=r_P(C)\}.
$$
具体地，若 $A,A'$ 为求和中的子空间，次模性和 $C\le A\cap A'$ 给出
$$
r_P(A+A')\le 2r_P(C)-r_P(A\cap A')\le r_P(C).
$$
单调性给出反向不等式。有限次迭代便得到 $r_P(H_P(C))=r_P(C)$；有限维性保证整个和由有限子族生成。因此，若 $C$ 独立且 $d=\dim C<r_P(V)$，则 $H_P(C)$ 为真子空间；任意 $v\notin H_P(C)$ 都使 $C+\langle v\rangle$ 独立。确实，$v\notin C$，而若这个 $d+1$ 维空间不独立，其整数秩由单调性只能等于 $d$，从而它包含于 $H_P(C)$，矛盾。逐维扩张说明，每个独立子空间均包含于一个维数 $r_P(V)$ 的 $P$-基，且所有 $P$-基都具有该维数。

若 $C$ 同时在两个 $q$-拟阵 $P,Q$ 中独立，且 $\dim C<\min(r_P(V),r_Q(V))$，则两个闭包都是真子空间。两个真子空间的并不能覆盖 $V$：包含情形取较大者外的向量；互不包含时，取 $a\in H_P(C)\setminus H_Q(C)$、$b\in H_Q(C)\setminus H_P(C)$，则 $a+b$ 在两者之外。因此可选
$$
v\notin H_P(C)\cup H_Q(C),
$$
使 $C+\langle v\rangle$ 同时在 $P,Q$ 中独立。从 $0$ 逐维迭代，所得共同独立子空间的维数可达到 $\min(r_P(V),r_Q(V))$。

对每个固定的 $U\le V$，上述闭包论证还给出
$$
\overline n(U)=\max\{0,R-\operatorname{codim}_V U\}. \tag{2}
$$
设 $c=\operatorname{codim}_V U$。任意 $M$-基 $B$ 都满足 $\dim(B\cap U)\ge\max\{0,R-c\}$。为达到下界，从 $C=0$ 开始构造与 $U$ 相交为零的独立子空间。若 $d=\dim C<\min(R,c)$，则 $H_M(C)$ 和 $U+C$ 都是真子空间，后者的维数为 $n-c+d<n$。取 $v$ 在两者之外，得到独立的 $C'=C+\langle v\rangle$，且 $C'\cap U=0$：否则某个 $a+\lambda v\in U$，其中 $a\in C$、$\lambda\ne0$，会推出 $v\in U+C$。这样得到维数 $\min(R,c)$ 的 $C$。若 $R\le c$，它已是与 $U$ 相交为零的 $M$-基；若 $R>c$，则 $V=C\oplus U$，将 $C$ 扩张为 $M$-基 $B$ 后，$B+U=V$，所以 $\dim(B\cap U)=R-c$。这就证明了 (2)。各个 $U$ 分别取得其最小值，并不要求同一个基同时取得所有最小值。

特别地，$\overline n(V)=R$。由 (2)，条件 (1) 等价于
$$
k\le R,\qquad \dim X(J)+|J|\le n\quad(J\subseteq I). \tag{3}
$$
事实上，对每个 $J$，(1) 等价于同时有 $|J|\le R$ 和 $\dim X(J)+|J|\le n$；所有前一类不等式等价于 $k\le R$。

先证必要性。设 $T$ 是 $M$-独立的满 $q$-横截，则 $k=\dim T=r(T)\le R$。对任意 $J\subseteq I$，取 $T\cap X(J)$ 的向量基并扩张为 $T$ 的向量基。在该基的避让双射中，属于 $X(J)$ 的向量均不能标号到 $J$，故
$$
\dim(T\cap X(J))\le k-|J|.
$$
另一方面，维数公式给出
$$
\dim(T\cap X(J))\ge k+\dim X(J)-n.
$$
合并即得 $\dim X(J)+|J|\le n$，所以 (3) 及 (1) 成立。

反过来，设 (1) 成立，因而 (3) 成立。若 $k=0$，取 $T=0$ 及空双射即可；以下设 $k>0$。条件 (1) 对 $J=\{i\}$ 排除了 $X_i=V$。

将 $I$ 双射重标号为 $\{1,\ldots,k\}$，使用 Saaltink 的横截 $q$-拟阵 $N$ [S, Theorem 15 及其证明]：它的独立子空间恰为每一个向量基都有注入避让标号的子空间。其诱导秩公式 [S, §3.1；CJ, Theorem 25、Remark 26、Proposition 27] 为
$$
r_N(U)=\min_{Y\le U}\bigl(f(Y)+\dim U-\dim Y\bigr),\qquad
f(Y)=|\{i\in I:Y\nleq X_i\}|.
$$
$f$ 是以各 $X_i$ 为 loop space 的秩一 $q$-拟阵秩函数之和，因而是非负、整数值、单调且次模的，并满足 $f(0)=0$，符合该诱导秩公式的假设。为求 $r_N(V)$，对每个 $Y\le V$ 令 $J_Y=\{i\in I:Y\le X_i\}$。则 $Y\le X(J_Y)$、$f(Y)=k-|J_Y|$，由 (3) 得
$$
f(Y)+n-\dim Y
 =k-|J_Y|+n-\dim Y\ge k.
$$
而取 $Y=V$ 得到 $r_N(V)\le f(V)\le k$，因此 $r_N(V)=k$。这也直接给出 [S, $q$-Hall 定理] 在这里所需的结论。

现在 $k=r_N(V)\le R$。将共同独立扩张应用于 $M,N$，得到维数 $k$ 的共同独立子空间 $T$。它在 $M$ 中独立；它在 $N$ 中独立意味着 $T$ 的每一个向量基都有到 $I$ 的注入避让标号。由于该基和 $I$ 都有 $k$ 个元素，该注入是双射。因此 $T$ 是所需的满 $q$-横截。

当 $R=0$ 时，(3) 强制 $k=0$，而零空间是唯一独立子空间；当 $V=0$ 时亦然。若某个 $X_i=V$，(1) 对单元素 $J$ 不成立，且任何向量都不能避让该指标。重复的子空间仍按其不同指标参与所有集合和标号。证明中的真子空间并论证对每个有限域均成立，包括二元域。以上覆盖空族、零秩、零维空间及所有 $J$ 的情形。$\square$

[S] M. Saaltink, [“A theory of $q$-transversals”, arXiv:2503.12201v1](https://arxiv.org/abs/2503.12201v1), §3--4；Definition 14、Theorem 15、$q$-Hall 定理、Conjecture 1。原始 TeX 的秩与独立性定义在 303--328 行，每个向量基的横截定义在 398--418 行，诱导横截拟阵及 $q$-Hall 论证在 422--496 行，bar nullity 与 Conjecture 1 在 498--508 行。

[JP] R. Jurrius and R. Pellikaan, [“Defining the $q$-analogue of a matroid”, arXiv:1610.09250v1](https://arxiv.org/abs/1610.09250v1), Propositions 2.5--2.6、§9.2 Definition 9.5。

[CJ] M. Ceria and R. Jurrius, [“The direct sum of $q$-matroids”, arXiv:2109.13637v1](https://arxiv.org/abs/2109.13637v1), §4 Theorem 25、Remark 26、Proposition 27。

## 追加锚（本行以下为增补区）
