# Saaltink 的精确 $q$-Rado 判据

设 $F$ 为有限域，$V$ 为有限维 $F$-向量空间，且 $M=(V,r)$ 为 $q$-拟阵。这里 $r$ 定义在 $V$ 的子空间格上，并满足
$$

0\le r(U)\le\dim U,\qquad U\le W\Longrightarrow r(U)\le r(W),

$$
以及
$$

r(U+W)+r(U\cap W)\le r(U)+r(W).

$$
子空间 $C$ 称为 $M$-独立的，如果 $r(C)=\dim C$；$M$ 的基是极大独立子空间。记
$$

R=r(V).

$$
每个 $M$-基的维数都是 $R$。

给定有限指标集 $I$ 以及允许重复的子空间族 $(X_i)_{i\in I}$，令
$$

X(J)=\bigcap_{j\in J}X_j,\qquad X(\varnothing)=V,

$$
并定义
$$

\overline n(U)=\min_{B\text{ 为 }M\text{-基}}\dim(B\cap U).

$$
称 $T\le V$ 为该族的满 $q$-横截，如果 $\dim T=|I|$，并且 $T$ 的每一个向量基都能双射标号为 $(t_i)_{i\in I}$，满足 $t_i\notin X_i$。这是 Saaltink 在 arXiv:2503.12201v1，TeX 398--418 的定义；其 $q$-拟阵和独立性的定义见 TeX 303--328。

**定理（Saaltink 精确 $q$-Rado 判据）。** 对上述任意 $F,V,M,I,(X_i)$，存在一个既是 $M$-独立又是满 $q$-横截的 $T$，当且仅当
$$

\overline n\bigl(X(J)\bigr)+|J|\le \overline n(V)
\qquad\text{对每个 }J\subseteq I.

$$

**引理（共同独立扩张）。** 若 $P,Q$ 是同一 $V$ 上的两个 $q$-拟阵，且 $C$ 同时在 $P,Q$ 中独立，$\dim C<\min(r_P(V),r_Q(V))$，则存在 $v\in V$ 使 $C+\langle v\rangle$ 同时在 $P,Q$ 中独立。

证明如下。对 $P$ 定义
$$

H_P(C)=\sum\{A:C\le A,\ r_P(A)=\dim C\}.

$$
若 $A,A'$ 是求和中的两个子空间，次模性和 $C\le A\cap A'$ 给出
$$

r_P(A+A')\le 2\dim C-r_P(A\cap A')\le\dim C.

$$
单调性及 $C\le A+A'$ 遂给出等号。有限次迭代（或取该和的一组有限生成子族）说明 $r_P(H_P(C))=\dim C$。于是当 $\dim C<r_P(V)$ 时，$H_P(C)$ 是真子空间；同理 $H_Q(C)$ 也是真子空间。两个真子空间的并不能覆盖 $V$：若一方不包含另一方，取各自差集中的向量相加；若可包含，则取较大者外的向量。因此可取
$$

v\notin H_P(C)\cup H_Q(C).

$$
若 $C+\langle v\rangle$ 在 $P$ 中不独立，则其秩仍为 $\dim C$，从而它包含于 $H_P(C)$，矛盾；对 $Q$ 同理。逐维迭代即得共同独立子空间，维数可达到 $\min(r_P(V),r_Q(V))$。取 $Q$ 为零空间即可得到每个独立子空间都能扩张为 $M$-基。

证明定理。先证必要性。设 $T$ 满足结论，令 $k=|I|$。由共同扩张引理把 $T$ 扩张为 $M$-基 $B$，故 $\dim B=R$。固定 $J\subseteq I$，取 $T\cap X(J)$ 的向量基并扩张为 $T$ 的向量基。满 $q$-横截的避让双射中，这些属于 $X(J)$ 的向量不能标号到 $J$，所以
$$

\dim(T\cap X(J))\le k-|J|.

$$
因为 $T\le B$，商映射 $B\to B/T$ 给出
$$

\dim(B\cap X(J))-\dim(T\cap X(J))
 \le\dim(B/T)=R-k.

$$
于是
$$

\overline n(X(J))
 \le\dim(B\cap X(J))
 \le R-|J|.

$$
另一方面 $\overline n(V)=R$，所需不等式成立。

反过来假设所有不等式成立。先记 $n=\dim V$。对任意 $U\le V$，任取 $M$-基 $B$，维数公式给出
$$

\dim(B\cap U)\ge R+\dim U-n,

$$
因而
$$

\overline n(U)\ge R+\dim U-n.

$$
代入 $U=X(J)$ 和假设，得到
$$

\dim X(J)+|J|\le n\qquad(J\subseteq I). \tag{1}

$$
这只使用每个 $U$ 的逐项下界，没有交换不同 $U$ 的最小化基。

令 $N$ 为 Saaltink 的族 $(X_i)$ 所定义的横截 $q$-拟阵：其独立子空间正是每个向量基都有部分避让标号的子空间（Saaltink，TeX 422--456）。Saaltink 的 $q$-Hall 定理（TeX 464--483）断言，族有满 $q$-横截当且仅当对每个非空 $J$ 有 $\dim X(J)+|J|\le n$，故由 (1) 其秩为 $r_N(V)=k$。等价地，也可从其诱导秩公式
$$

r_N(V)=\min_{Y\le V}\bigl(f(Y)+n-\dim Y\bigr),\qquad
f(Y)=|\{i:Y\nleq X_i\}|

$$
直接看出：令 $J_Y=\{i:Y\le X_i\}$，则 $Y\le X(J_Y)$，且 (1) 给出
$$

f(Y)+n-\dim Y
 =k-|J_Y|+n-\dim Y\ge k.

$$
取 $Y=V$ 得上界 $r_N(V)\le k$，所以等号成立。

现在 $k=r_N(V)\le R$。从 $0$ 开始应用共同独立扩张引理，得到维数 $k$ 的子空间 $T$，同时在 $M,N$ 中独立。$M$-独立给出所需的 $M$-独立性；$N$-独立按 $N$ 的定义给出 $T$ 的每一个向量基都有到 $I$ 的注入避让标号。由于两边均有 $k$ 个元素，该注入必为双射，故 $T$ 是满 $q$-横截。定理得证。

上述论证也给出一个有用的恒等式：
$$

\overline n(U)=\max\{0,\ R-\operatorname{codim}_V U\}. \tag{2}

$$
确实，前面的维数公式给出下界。若 $c=\operatorname{codim}_V U$，用共同扩张引理（只取 $M$）逐维构造与 $U$ 相交为零的独立子空间，直到维数 $\min(R,c)$。当 $R\le c$ 时把它取为 $M$-基，得到交为零；当 $R>c$ 时，构造出的 $c$ 维子空间到 $V/U$ 的投影是同构，任意包含它的 $M$-基 $B$ 满足
$$

\dim(B\cap U)=R-c.

$$
这证明了 (2)，且没有要求所有 $U$ 共享同一个最小化基。

当 $I=\varnothing$ 时，$T=0$ 及空双射给出结论；当 $R=0$ 时共同扩张只产生零空间，假设中的 $J=I$ 强制 $I=\varnothing$。零维 $V$、某个 $X_i=V$ 以及族中重复的指标都已包含在同一证明中。

Saaltink 的来源为：M. Saaltink, “A theory of $q$-transversals”, arXiv:2503.12201v1, Theorem 15、其 $q$-Hall 定理和 Conjecture 1（TeX 498--508）。$q$-拟阵独立空间和扩张公理的相容形式亦见 Ceria--Jurrius, “Alternatives for the $q$-matroid axioms of independent spaces, bases, and spanning spaces”, arXiv:2207.07324v5, §3.2；闭包与基的基本性质见 Jurrius--Pellikaan, “Defining the $q$-analogue of a matroid”, arXiv:1610.09250v1。

## 追加锚（本行以下为增补区）
