# Weak coset obstructions in divisible partition lattices

## 1. Definitions and the family assertion

**Definition 1.1 (Divisible partition lattice).** For a positive integer $m$, put $[m]=\{1,\ldots,m\}$. A set partition of $[m]$ is a collection of nonempty, pairwise disjoint subsets, called blocks, whose union is $[m]$. The refinement order is $x\leq y$ when every block of $x$ is contained in a block of $y$.

For integers $d\geq2$ and $n\geq1$, write

$$
L(d,n)=\Pi_{dn}^{d}
$$

for the finite lattice whose nonbottom elements are all set partitions of $[dn]$ with every block cardinality divisible by $d$, ordered by refinement. Adjoin a fresh element $\widehat0$ below every such partition. Its top $\widehat1$ is the partition with the single block $[dn]$. This is the divisible partition lattice of [1, Section 5.2]; the artificial bottom is distinct from every set partition.

In a lattice, $a\vee b$ denotes the least upper bound of $a,b$. A nonbottom element $j$ is join-irreducible when, for all elements $a,b$, the equality $j=a\vee b$ implies $j=a$ or $j=b$. Put

$$
J=J(L)=\{j\in L:j\neq\widehat0\text{ and }j\text{ is join-irreducible}\},
\qquad
J_x=\{j\in J:j\leq x\}.
$$

An atom is an element $a>\widehat0$ with no element strictly between $\widehat0$ and $a$.

**Definition 1.2 (Möbius function and probabilistic zeta function).** For a finite partially ordered set, the incidence Möbius function is determined on comparable pairs by

$$
\mu(x,x)=1,
\qquad
\sum_{x\leq z\leq y}\mu(z,y)=0\quad(x<y).
$$

For a positive real number $q$ and any $s\in\mathbb C$, use the convention

$$
q^{-s}=\exp(-s\log q),
$$

where $\log q$ is the real logarithm. For $L=L(d,n)$ define, as in [1, equation (3.1)],

$$
P(d,n;s)=P_L(s)
=\sum_{\substack{x\in L\\x\neq\widehat0}}
\mu(x,\widehat1)
\exp\!\left(-s\log\frac{|J|}{|J_x|}\right).
\tag{1.1}
$$

The counts in item 2.1 below show that $J$ and every $J_x$ appearing here are nonempty, so every base in (1.1) is a positive rational number. The bottom contributes no term. Formula (1.1) defines a function on the entire complex plane.

**Definition 1.3 (Weak and strong coset-likeness).** Following [1, Definition 5.2 and the opening of Section 5], $L$ is weakly coset-like when there exist an integer $N\geq1$ and complex numbers $a_1,\ldots,a_N$ such that

$$
\forall s\in\mathbb C,\qquad
P_L(s)=\sum_{k=1}^{N}a_k\exp(-s\log k).
\tag{1.2}
$$

Thus the coefficients in a finite ordinary Dirichlet representation are allowed to be arbitrary complex numbers. Following [1, Definition 5.1], strong coset-likeness means $|J_x|\mid |J|$ for every nonbottom $x$. The results below establish weak nonrepresentability by examining grouped coefficients in (1.1).

**Boundary 1.4 (Quantified family assertion).** The second sentence of [1, Question 7.4] asks whether the $d$-divisible partition lattice is weakly coset-like, without explicitly printing outer parameter quantifiers. The family assertion considered here is the explicit statement

$$
\forall d\in\mathbb Z_{\geq2}\ \forall n\in\mathbb Z_{\geq1},
\qquad \Pi_{dn}^{d}\text{ is weakly coset-like}.
\tag{1.3}
$$

This specifies a universal-family interpretation of that sentence. Theorems 3.3, 4.1 and 5.1 respectively give an exact criterion at $n=4$, a counterexample to (1.3), and an infinite negative subfamily. No classification for $n\neq4$ is asserted.

## 2. Counting identities and uniqueness of finite exponential sums

**Counting identity 2.1 (Join-irreducible counts).** The join-irreducibles of $L(d,n)$ are exactly its atoms, the partitions into $n$ blocks of size $d$ [1, Section 5.2]. For a positive integer $m$, write

$$
A_m=\frac{(dm)!}{(d!)^m m!}.
\tag{2.1}
$$

This is the number of partitions of a fixed $dm$-element set into $m$ blocks of size $d$. Indeed, list all $dm$ labels in order and cut the list into $m$ successive groups of $d$. Each unordered partition is obtained $(d!)^m m!$ times: the labels within each block and the blocks themselves can be ordered independently.

Consequently, if $x$ has block sizes $dp_1,\ldots,dp_k$, where each $p_i\geq1$ and $\sum_i p_i=n$, the source's characterization of $J$ gives

$$
|J|=A_n,
\qquad
|J_x|=\prod_{i=1}^{k}A_{p_i}.
\tag{2.2}
$$

For the second identity, an atom refines $x$ exactly when each block of $x$ is partitioned into blocks of size $d$. The choices in distinct blocks are independent. These are the counting facts from [1, Section 5.2] used below; in particular each factor in (2.2) is a positive integer.

**Counting identity 2.2 (Ratios for four normalized blocks).** Fix $d\geq2$ and set

$$
B=\binom{4d}{2d},\qquad
C=\binom{2d}{d},\qquad
H=\binom{4d}{d},\qquad
D_m=\binom{dm-1}{d-1}\quad(m=2,3,4).
\tag{2.3}
$$

The factorial expression (2.1) gives $A_1=1$ and

$$
\begin{aligned}
\frac{A_m}{A_{m-1}}
&=\frac{(dm)!}{d!\,m\,(d(m-1))!}\\
&=\frac1m\binom{dm}{d}
=\binom{dm-1}{d-1}=D_m
\qquad(m=2,3,4).
\end{aligned}
\tag{2.4}
$$

In the last equality, $\binom{dm}{d}=m\binom{dm-1}{d-1}$. Hence

$$
\frac{A_4}{A_3}=D_4,\qquad
\frac{A_4}{A_2}=D_3D_4,
\qquad
\frac{A_4}{A_2^2}
=\frac{(4d)!}{(2d)!^2}\frac{(2!)^2}{4!}
=\frac B6.
\tag{2.5}
$$

Thus the first two ratios in (2.5) are positive integers, while the last is integral exactly when $6\mid B$.

**Standard fact 2.3 (Finite exponential independence).** Distinct positive real bases $q_1,\ldots,q_t$ give linearly independent functions $s\mapsto\exp(-s\log q_i)$ over $\mathbb C$.

Proof. Suppose

$$
\sum_{i=1}^{t}c_i\exp(-s\log q_i)=0
\qquad\text{for every }s\in\mathbb C,
\tag{2.6}
$$

with $c_i\in\mathbb C$. Order the bases so that $q_1<\cdots<q_t$. Restrict to real $s=u\geq0$ and multiply (2.6) by $q_1^u$. This gives

$$
c_1+\sum_{i=2}^{t}c_i(q_1/q_i)^u=0.
$$

Each ratio in the sum is strictly between zero and one. Letting $u$ tend to infinity therefore gives $c_1=0$, also for complex coefficients. Remove this term and repeat on the remaining finitely many bases. Every coefficient is zero. $\square$

In particular, consider a finite sum of such exponentials and combine all terms with the same base. If a noninteger base $q$ has a nonzero grouped coefficient, the sum cannot satisfy (1.2). Indeed, subtract a proposed representation (1.2) and group the union of its integer bases with the original bases. The coefficient at $q$ stays nonzero, contradicting (2.6). This uniqueness argument is the elementary intermediate step that excludes cancellation by arbitrary complex Dirichlet coefficients.

## 3. The exhaustive calculation at n = 4

**Calculation 3.1 (Upper Möbius values).** Let $x\neq\widehat0$ in $L(d,4)$ have $k$ blocks. Its upper interval $[x,\widehat1]$ is the ordinary partition lattice on those $k$ blocks. Indeed, a coarsening groups whole blocks of $x$, and every union of such blocks still has size divisible by $d$. This gives an order-preserving bijection in both directions. Since $x$ is nonbottom, the artificial bottom is outside the interval.

The Möbius function on an interval is determined by its order and the recurrence in Definition 1.2. Write $f_k$ for $\mu(x,\widehat1)$ in this interval. If $S(k,r)$ denotes the number of partitions of a $k$-element set into $r$ nonempty groups, the recurrence is

$$
f_1=1,\qquad
\sum_{r=1}^{k}S(k,r)f_r=0\quad(2\leq k\leq4).
\tag{3.1}
$$

Here a coarsening with $r$ blocks contributes $f_r$. The required counting rows are

$$
\begin{array}{c|rrrr}
k\backslash r&1&2&3&4\\ \hline
1&1&0&0&0\\
2&1&1&0&0\\
3&1&3&1&0\\
4&1&7&6&1
\end{array}
$$

For three labels, a partition into two groups is specified by its unique two-element group, giving three choices. For four labels, the number of two-group partitions is $(2^4-2)/2=7$, since either of the two nonempty complementary groups can be selected first. A three-group partition of four labels has one two-element group, giving $\binom42=6$ choices. The one-group and all-singleton counts are one, which accounts for all entries. Substitution in (3.1) yields

$$
f_1=1,\qquad
f_2=-1,\qquad
f_3=2,\qquad
f_4=-6.
\tag{3.2}
$$

**Calculation 3.2 (All five block-size types).** For $x\in L(d,4)\setminus\{\widehat0\}$, divide its block sizes by $d$. Their unordered list is an integer partition of $4$. The only possibilities are

$$
(4),\quad(3,1),\quad(2,2),\quad(2,1,1),\quad(1,1,1,1).
$$

To see exhaustiveness, the largest part is either $4$, $3$, $2$, or $1$. The first two force the first two listed types; largest part $2$ leaves either another $2$ or two $1$'s; largest part $1$ forces four $1$'s. Equations (2.2), (2.5) and (3.2) give the following full defining sum.

| Normalized block sizes | Number of labeled partitions | $\lvert J_x\rvert$ | $\mu(x,\widehat1)$ | Base $\lvert J\rvert/\lvert J_x\rvert$ |
| --- | ---: | ---: | ---: | ---: |
| $(4)$ | $1$ | $A_4$ | $1$ | $1$ |
| $(3,1)$ | $H$ | $A_3$ | $-1$ | $D_4$ |
| $(2,2)$ | $B/2$ | $A_2^2$ | $-1$ | $B/6$ |
| $(2,1,1)$ | $BC/2$ | $A_2$ | $2$ | $D_3D_4$ |
| $(1,1,1,1)$ | $A_4$ | $1$ | $-6$ | $A_4$ |

For type $(4)$ there is only the top. For type $(3,1)$, choosing the unique $d$-element block specifies the partition, so the multiplicity is $\binom{4d}{d}=H$. For type $(2,2)$, select a $2d$-element block and divide by two because either complementary block gives the same partition, obtaining $B/2$.

For type $(2,1,1)$, first choose its unique $2d$-element block in $B$ ways. Partition its complement into two unordered $d$-element blocks in $C/2$ ways, obtaining $BC/2$. The all-$1$ type consists precisely of the atoms, counted by $A_4$. This establishes each multiplicity without selecting any preferred ordering of equally sized blocks.

Multiplying each row's multiplicity by its Möbius value in (1.1) gives, for every $s\in\mathbb C$,

$$
\begin{aligned}
P(d,4;s)
={}&1-H\exp(-s\log D_4)
-\frac B2\exp\!\left(-s\log\frac B6\right)\\
&+BC\exp(-s\log(D_3D_4))
-6A_4\exp(-s\log A_4).
\end{aligned}
\tag{3.3}
$$

All five terms come from nonbottom partitions. In particular $-6A_4$ in the last term is a scalar coefficient.

**Theorem 3.3 (Exact criterion at n = 4).** For every integer $d\geq2$,

$$
\Pi_{4d}^{d}\text{ is weakly coset-like}
\quad\Longleftrightarrow\quad
6\mid\binom{4d}{2d}.
\tag{3.4}
$$

Equivalently, the criterion is $3\mid\binom{4d}{2d}$.

Proof. Use the notation (2.3). Every base in (3.3) other than $B/6$ is a positive integer: this holds for $1$, $D_4$, $D_3D_4$ by their definitions, and for $A_4$ by its counting interpretation.

If $6\nmid B$, the base $B/6$ is noninteger, and so it is distinct from every other base in (3.3). Its grouped coefficient is therefore exactly $-B/2$, which is nonzero. The uniqueness argument in item 2.3 excludes every finite ordinary Dirichlet representation with complex coefficients. Thus $\Pi_{4d}^{d}$ is not weakly coset-like.

If $6\mid B$, all the bases in (3.3) are positive integers. Let $N$ be their maximum. For each $1\leq k\leq N$, let $a_k$ be the sum of the coefficients of those displayed terms whose base equals $k$, taking the sum to be zero if there are no such terms. This gives (1.2) for every complex $s$, including any coincidences among the integer bases. Thus $\Pi_{4d}^{d}$ is weakly coset-like, proving both directions of (3.4).

Finally, $B$ is even. Complementation pairs the $2d$-element subsets of $[4d]$, and no subset equals its complement: a label cannot be both in a set and outside it. Hence the $B$ subsets occur in disjoint pairs. Since $2\mid B$ and $2,3$ are coprime, $6\mid B$ is equivalent to $3\mid B$. $\square$

## 4. The exact obstruction on the even-block lattice of eight labels

**Theorem 4.1 (A nonordinary base in Pi_8^2).** Let $L=\Pi_8^2$ consist of all partitions of $[8]$ into even-sized blocks together with a fresh artificial bottom, ordered by refinement. For every complex $s$,

$$
\begin{aligned}
P_L(s)={}&1-28\exp(-s\log7)
-35\exp\!\left(-s\log\frac{35}{3}\right)\\
&+420\exp(-s\log35)-630\exp(-s\log105).
\end{aligned}
\tag{4.1}
$$

This function has no finite ordinary Dirichlet representation with complex coefficients. In particular, the family assertion (1.3) is false.

Proof. Set $d=2$ and $n=4$. From (2.1) and (2.3),

$$
\begin{gathered}
A_1=1,\qquad A_2=3,\qquad A_3=15,\qquad A_4=105,\\
B=\binom84=70,\qquad C=\binom42=6,\qquad H=\binom82=28,\\
D_4=\binom71=7,\qquad D_3=\binom51=5.
\end{gathered}
$$

Thus the five types in Calculation 3.2 have multiplicities $1,28,35,210,105$, respectively. Their Möbius values are $1,-1,-1,2,-6$, and their bases are $1,7,35/3,35,105$. Substituting gives exactly (4.1).

The base $35/3$ is noninteger and distinct from $1,7,35,105$, so its grouped coefficient is $-35\neq0$. If (4.1) admitted a representation (1.2), subtracting that representation and grouping equal positive real bases would leave coefficient $-35$ at $35/3$. This contradicts finite exponential independence from item 2.3. The nonrepresentability holds for arbitrary complex coefficients and equality on all of $\mathbb C$.

The parameters $d=2,n=4$ satisfy the quantifiers in (1.3), so this single lattice disproves that explicitly stated universal-family assertion. $\square$

## 5. An infinite negative subfamily

**Theorem 5.1 (Powers of three).** For every integer $r\geq0$,

$$
\binom{8\cdot3^r}{4\cdot3^r}\equiv1\pmod3,
\qquad
\Pi_{8\cdot3^r}^{\,2\cdot3^r}
\text{ is not weakly coset-like}.
\tag{5.1}
$$

Proof. Work in $\mathbb F_3[X]$, the polynomial ring over the field of three elements. The binomial theorem and $3=0$ give

$$
(1+X)^3=1+X^3.
$$

Induction on $r$ yields

$$
(1+X)^{3^r}=1+X^{3^r}.
\tag{5.2}
$$

For $r=0$ this is the identity $1+X=1+X$. If (5.2) holds for $r$, cubing it gives $(1+X)^{3^{r+1}}=1+X^{3^{r+1}}$, proving the induction step.

Raise (5.2) to the eighth power to obtain

$$
(1+X)^{8\cdot3^r}=(1+X^{3^r})^8.
\tag{5.3}
$$

The coefficient of $X^{4\cdot3^r}$ on the left is the residue class of $\binom{8\cdot3^r}{4\cdot3^r}$. On the right, the binomial expansion is

$$
\sum_{j=0}^{8}\binom8jX^{j3^r}.
$$

Since $3^r$ is positive, exactly the term $j=4$ has exponent $4\cdot3^r$. Its coefficient is $\binom84=70\equiv1\pmod3$. Comparing coefficients in (5.3) proves the congruence for every $r\geq0$.

Now take $d=2\cdot3^r\geq2$ and $n=4$. Then

$$
B=\binom{4d}{2d}=\binom{8\cdot3^r}{4\cdot3^r}
$$

is not divisible by $3$, and hence not by $6$. Theorem 3.3 proves the asserted failure of weak coset-likeness. More explicitly, in (3.3) the noninteger base $B/6$ has the nonzero grouped coefficient $-B/2$, while every other displayed base is an integer.

The integers $2\cdot3^r$ are strictly increasing as $r$ increases, so this gives infinitely many distinct parameter pairs within (1.3), all with $n=4$. $\square$

## 6. Reference

**Reference 6.1.** [1] Besfort Shala, *The Probabilistic Zeta Function of a Finite Lattice*, [arXiv:2112.13766v6](https://arxiv.org/html/2112.13766v6). Equation (3.1) gives (1.1); the opening of Section 5 and Definitions 5.1–5.2 give the complex-coefficient ordinary Dirichlet convention and coset-likeness definitions; Section 5.2 gives the divisible partition lattice and its join-irreducible counts; Question 7.4 supplies the question discussed in Boundary 1.4.

## 追加锚（本行以下为增补区）
