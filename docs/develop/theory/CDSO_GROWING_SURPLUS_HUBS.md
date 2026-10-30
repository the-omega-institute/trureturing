# CDSO growing surplus hubs

## 1. Joint laws with a growing number of labels

**Definition 1.1 (The unrestricted integer-mean problem).** Let $a\ge4$ and $h\ge1$ be integers and put $s=a+1+h$. Let $\mathcal X(a,h)$ be the set of probability laws

$$
x=(x_T)_{\varnothing\ne T\subseteq[s]},\qquad
x_T\ge0,\qquad \sum_Tx_T=1,\qquad
\sum_T|T|x_T=a,
$$

whose actual marginals satisfy

$$
y_i=\sum_{T\ni i}x_T>0\qquad(i\in[s]).
$$

For the random nonempty subset $T$ with this one law, write

$$
K=|T|,\qquad U_T=\sum_{i\in T}\frac1{y_i},\qquad
H(x)=\mathbb E_x\left[K^2\sum_{i\in T}\frac1{y_i^2}\right],
$$

$$
B_0(a)=a(a+1)^2,\qquad
M(a,h)=\inf_{x\in\mathcal X(a,h)}H(x).
\tag{1.1}
$$

These are the profiles of [*CDSO incidence moments and capacity phases*, Definition 1.1](CDSO_INCIDENCE_MOMENTS_AND_CAPACITY_PHASES.md), with $q=a$ and $H=2J_s$. Every marginal, cardinality and expectation in (1.1) is determined by $x$; none can be optimized independently. Type masses may vanish, every cardinality $1\le K\le s$ is allowed, and the positive-mass types need not form a connected incidence support. Positivity imposes no uniform lower bound on $y_i$ over this class. The uniform law on the $a$-element subsets of $[s]$ belongs to $\mathcal X(a,h)$, so the class is nonempty and $M(a,h)$ is finite. The notation is an infimum and does not assert attainment.

**Definition 1.2 (The growing-surplus scale).** A sequence in the growing-surplus regime consists of integers $(a_n,h_n)$ such that

$$
a_n\ge4,\qquad h_n\ge1,\qquad a_n\longrightarrow\infty,
\qquad \frac{h_n}{\sqrt{a_n}}\longrightarrow\kappa\in(0,\infty).
\tag{1.2}
$$

The normalized infimum along it is

$$
D_n=\frac{M(a_n,h_n)-B_0(a_n)}{a_n^2}.
\tag{1.3}
$$

Subscripts are suppressed when no ambiguity results. Bounds for $\liminf D_n$ and $\limsup D_n$ do not presume convergence, or that different sequences with the same $\kappa$ have a common limit.

## 2. A shared marginal budget at every integer mean

**Theorem 2.1 (An all-cardinality affine certificate).** Let $a\ge2$ be an integer and $s\ge a$ a finite integer. Let $x$ be any probability law on the nonempty subsets of $[s]$ with $\mathbb E K=a$ and every actual marginal positive. Define $H$ as in Definition 1.1 and put

$$
\beta_a=4(a-1)\sqrt{a+1}-2a+4.
\tag{2.1}
$$

Then

$$
H(x)\ge a^3+\beta_a(s-a),\qquad
\frac{\beta_a}{a^{3/2}}\longrightarrow4.
\tag{2.2}
$$

This holds for all such laws, including zero type masses, arbitrarily small positive marginals, arbitrary cardinality layers and disconnected incidence support.

**Proof.** The shared-budget inequality in [*CDSO incidence moments and capacity phases*, Theorem 2.2, (2.2)](CDSO_INCIDENCE_MOMENTS_AND_CAPACITY_PHASES.md) gives $U_T\ge K^2/a$. Its common-law calculation is

$$
\sum_i y_i=\mathbb E K=a,\qquad
K^2\le\left(\sum_{i\in T}y_i\right)U_T\le aU_T.
$$

Moreover, summing over the actual inclusion events and using Cauchy–Schwarz within each realized $T$ gives

$$
\mathbb E U_T=\sum_i\frac{\mathbb P(i\in T)}{y_i}=s,
\qquad
K^2\sum_{i\in T}y_i^{-2}\ge K U_T^2.
\tag{2.3}
$$

Thus it suffices to bound $\mathbb E(KU_T^2)$ using this same pair $(K,U_T)$.

Write $\beta=\beta_a$ and set

$$
\lambda=5a^2-2\beta,\qquad \nu=4a^3-a\beta,
\qquad k_0=(a\beta/2)^{1/3}.
$$

The inequalities $2a\le\beta\le2a^2$ follow respectively from

$$
\beta-2a=4(a-1)(\sqrt{a+1}-1)\ge0
$$

and $2\sqrt{a+1}\le a+2$, whose square is $4a+4\le a^2+4a+4$. Consequently $\lambda>0$, $\nu>0$ and $1\le k_0\le a$. We prove the pointwise inequality

$$
P(k,u):=ku^2-\lambda k-\beta u+\nu\ge0
\qquad(k\ge1,\ u\ge k^2/a),
\tag{2.4}
$$

where $k$ is allowed to be real.

For $k\ge k_0$, the derivative $2ku-\beta$ is nonnegative on $u\ge k^2/a$, since $2k^3/a\ge\beta$. Hence the minimum on this half-line is at its boundary. With $t=k/a\ge0$, direct factorization gives

$$
P(k,k^2/a)
=a^3(t-1)^2\left(t^3+2t^2+3t+4-\frac\beta{a^2}\right)\ge0,
\tag{2.5}
$$

because $\beta/a^2\le2$.

For $1\le k\le k_0$, the unconstrained minimizing point $u=\beta/(2k)$ is feasible. Four times $k$ times its value is

$$
Q(k)=4\nu k-4\lambda k^2-\beta^2.
$$

This is a concave quadratic. The explicit value (2.1) satisfies

$$
\beta^2+4(a-2)\beta=16a^3-20a^2,
$$

so $Q(1)=0$. At $k=k_0$, the unconstrained minimizing point equals $k_0^2/a$, and (2.5) gives $Q(k_0)\ge0$. A concave function lies above the chord joining its endpoint values; therefore $Q(k)\ge0$ throughout $[1,k_0]$. Since $k>0$, this proves (2.4) on the remaining interval.

Apply (2.4) to $(k,u)=(K,U_T)$ and take expectations. By (2.3),

$$
\begin{aligned}
H(x)&\ge\mathbb E(KU_T^2)
\ge\lambda\mathbb E K+\beta\mathbb E U_T-\nu\\
&=\lambda a+\beta s-\nu
=a^3+\beta(s-a).
\end{aligned}
$$

Finally,

$$
\frac{\beta_a}{a^{3/2}}
=4(1-a^{-1})\sqrt{1+a^{-1}}
 -2a^{-1/2}+4a^{-3/2}\longrightarrow4.
$$

All expectations used the original law. No support reduction or lower bound on its positive marginals was imposed. ∎

## 3. Actual enlarged-core constructions

**Theorem 3.1 (An integer enlargement of the core).** For integers $a\ge2$, $j\ge1$ and $h\ge j$, put

$$
m=a+j,\qquad n=h+1-j,\qquad s=m+n=a+1+h.
$$

Partition $[s]=C\mathbin{\dot\cup}D$ with $|C|=m$ and $|D|=n$. The single law

$$
p=\frac{j}{a+j-1},\qquad
x_C=1-p,\qquad x_{\{d\}}=\frac pn\quad(d\in D),
\qquad x_T=0\text{ for every other }T
\tag{3.1}
$$

has mean cardinality $a$, positive actual marginals and energy

$$
H_j(a,h)
=\frac{(a+j)^3(a+j-1)}{a-1}
 +\frac{(h+1-j)^2(a+j-1)}j.
\tag{3.2}
$$

For every fixed positive integer $j$ and every sequence (1.2), this law is admissible eventually and

$$
\frac{H_j(a_n,h_n)-B_0(a_n)}{a_n^2}
\longrightarrow F_j(\kappa):=\frac{\kappa^2}j+4j-2.
\tag{3.3}
$$

**Proof.** The integers $m,n$ are positive and $0<p<1$. The masses sum to one, and

$$
\mathbb E K=(1-p)m+p=a.
$$

Every core marginal is $y_i=1-p=(a-1)/(a+j-1)>0$ and every tail marginal is $y_d=p/n>0$. On the core event the contribution to $H$ is $m^3/(1-p)$; the singleton events contribute $n^2/p$ in total. This proves (3.2), directly from one law.

For fixed $j$,

$$
\frac{(a+j)^3(a+j-1)}{a-1}
=(a+j)^3\left(1+\frac j{a-1}\right)
=a^3+4ja^2+O_j(a).
$$

Also $n/\sqrt a\to\kappa$ and $(a+j-1)/a\to1$, whence the second term of (3.2), divided by $a^2$, tends to $\kappa^2/j$. Subtract $B_0(a)=a^3+2a^2+a$ to obtain (3.3). Since (1.2) implies $h_n\to\infty$, the condition $h_n\ge j$ holds eventually. The core and the tail singletons lie in separate support components, which are permitted by Definition 1.1. ∎

**Proposition 3.2 (A continuous core mean on a finite core).** Fix a positive integer $j$ and a real number $v$ with $0<v\le j$. For every integer $a\ge2$ and $h\ge j$, use the partition of Theorem 3.1 and put

$$
p=\frac v{a+v-1},\qquad \ell=\lfloor v\rfloor,\qquad
\theta=v-\ell\in[0,1).
$$

Give each singleton $\{d\}$, $d\in D$, mass $p/n$. Conditional on the remaining mass $1-p$, choose uniformly a subset of $C$ of size $a+\ell$ with probability $1-\theta$, and uniformly a subset of size $a+\ell+1$ with probability $\theta$. A branch of probability zero is omitted: in particular, when $v=j$ the second branch is absent and no subset of size $a+j+1$ is requested. All unspecified type masses are zero.

This is one mean-$a$ law with positive marginals. With

$$
M_3=(1-\theta)(a+\ell)^3+\theta(a+\ell+1)^3,
$$

its exact energy is

$$
H_{j,v}(a,h)
=\frac{(a+j)^2 M_3}{(1-p)(a+v)^2}
 +\frac{(h+1-j)^2}{p}.
\tag{3.4}
$$

For every sequence (1.2),

$$
\frac{H_{j,v}(a_n,h_n)-B_0(a_n)}{a_n^2}
\longrightarrow \frac{\kappa^2}{v}+2v+2(j-1).
\tag{3.5}
$$

**Proof.** If $\theta>0$, then $\ell+1\le j$, so both requested subset sizes are at most $|C|$. If $\theta=0$, only size $a+\ell\le|C|$ is used. These sizes are positive. The conditional core mean is $a+v$ and its inclusion probability for each label in $C$ is $(a+v)/(a+j)$. Thus

$$
y_i=\frac{(1-p)(a+v)}{a+j}>0\quad(i\in C),\qquad
y_d=\frac pn>0\quad(d\in D),
$$

and $(1-p)(a+v)+p=a$. Conditional uniformity and the common core marginal give core contribution $(1-p)M_3/y_i^2$, which is the first term of (3.4). The singleton contribution is again $n^2/p$.

Since $j,v$ are fixed,

$$
M_3=a^3+3va^2+O_{j,v}(a),\qquad
(1-p)(a+v)^2=a^2+va+O_{j,v}(1).
$$

Consequently the first term in (3.4) equals $a^3+(2j+2v)a^2+O_{j,v}(a)$. Since $n/\sqrt a\to\kappa$ and $p=v/(a+v-1)$, the second term divided by $a^2$ tends to $\kappa^2/v$. This proves (3.5). At $v=j$, the conditional core is the full set $C$, so the law is exactly (3.1). ∎

## 4. Global bounds and matching even-ratio limits

**Definition 4.1 (A constructive upper envelope).** For $\kappa>0$, define

$$
U(\kappa)=
\begin{cases}
2\sqrt2\,\kappa,&0<\kappa\le\sqrt2,\\
\displaystyle\min_{j\in\mathbb Z_{\ge1}}
\left(\frac{\kappa^2}j+4j-2\right),&\kappa\ge\sqrt2.
\end{cases}
\tag{4.1}
$$

The two values agree at $\kappa=\sqrt2$. The discrete minimum exists since $F_j(\kappa)\to\infty$ as $j\to\infty$ for fixed $\kappa$.

**Theorem 4.2 (Unrestricted lower and upper asymptotic bounds).** For every $\kappa\in(0,\infty)$ and every sequence (1.2),

$$
\max\{0,4\kappa-2\}
\le\liminf_{n\to\infty}D_n
\le\limsup_{n\to\infty}D_n
\le U(\kappa).
\tag{4.2}
$$

The infimum defining $D_n$ is over the entire class $\mathcal X(a_n,h_n)$.

**Proof.** Apply Theorem 2.1 with $s=a+1+h$. For every admissible $x$,

$$
\frac{H(x)-B_0(a)}{a^2}
\ge\frac{\beta_a(h+1)}{a^2}-2-\frac1a.
\tag{4.3}
$$

This bound is uniform over $\mathcal X(a,h)$, so it holds with $H(x)$ replaced by $M(a,h)$. Along (1.2) its right side tends to $4\kappa-2$.

For the other lower bound, reuse [*CDSO incidence moments and capacity phases*, Theorem 11.3](CDSO_INCIDENCE_MOMENTS_AND_CAPACITY_PHASES.md). Its hypotheses hold with $r=a+1\ge5$, $q=a=r-1$ and $s=a+1+h\ge r$. In the notation of that theorem, $2F_{a+1}(a)=a(a+1)^2=B_0(a)$, and $H=2J_s$. Thus $H(x)\ge B_0(a)$ throughout this class, giving $D_n\ge0$. Together these prove the left side of (4.2).

If $0<\kappa\le\sqrt2$, use Proposition 3.2 with $j=1$ and $v=\kappa/\sqrt2\in(0,1]$. Its limiting normalized gap is

$$
\frac{\kappa^2}{v}+2v=2\sqrt2\,\kappa.
$$

Since $M(a,h)$ is bounded above by the energy of this actual law, this gives the first upper branch. If $\kappa\ge\sqrt2$, Theorem 3.1 bounds $\limsup D_n$ by $F_j(\kappa)$ for every fixed positive integer $j$. Taking the minimum over these constants proves the second branch. The constructions are available eventually on every sequence (1.2). ∎

**Proposition 4.3 (Integer core phases of the upper bound).** On $\kappa\ge\sqrt2$, the minimizing integer branch in (4.1) is $j=1$ for

$$
\sqrt2\le\kappa\le2\sqrt2,
$$

and, for each $j\ge2$, branch $j$ minimizes precisely on

$$
2\sqrt{j(j-1)}\le\kappa\le2\sqrt{j(j+1)}.
\tag{4.4}
$$

At a shared endpoint the two adjacent branches tie; in each open interval the branch is unique. These are phases of the constructive upper bound $U$.

**Proof.** The adjacent difference is

$$
F_{j+1}(\kappa)-F_j(\kappa)
=4-\frac{\kappa^2}{j(j+1)}.
$$

For fixed $\kappa$, this difference increases strictly with $j$. A minimizing branch $j\ge2$ therefore has nonpositive incoming difference and nonnegative outgoing difference, which are exactly (4.4). For $j=1$ only the outgoing condition is needed. Strictness away from the adjacent crossing points proves uniqueness and the asserted ties. This compares the displayed constructions; it does not identify unrestricted minimizers. ∎

**Theorem 4.4 (Matching global limits at every positive even ratio).** For every fixed positive integer $j$ and every sequence of integers with $a_n\to\infty$ and $h_n/\sqrt{a_n}\to2j$,

$$
\lim_{n\to\infty}
\frac{M(a_n,h_n)-a_n(a_n+1)^2}{a_n^2}
=8j-2.
\tag{4.5}
$$

In particular this is a limit of the infimum over all actual laws, independent of the chosen sequence at that ratio.

**Proof.** The universal lower bound in Theorem 4.2 is $4(2j)-2=8j-2$. The single law (3.1) with this same fixed $j$ has, by (3.3), limiting normalized gap

$$
F_j(2j)=\frac{4j^2}{j}+4j-2=8j-2.
$$

It supplies a matching upper bound for the unrestricted infimum. Squeezing proves (4.5); no finite minimizer is required. ∎

## 5. The cap of a specified singleton family and its failure as a global bound

**Definition 5.1 (The one-extra-core-label singleton family).** For integers $a\ge2$, $h\ge1$, partition $[a+1+h]=C\mathbin{\dot\cup}D$ with $|C|=r=a+1$, $|D|=h$. For the actual parameter domain

$$
0<\varepsilon\le1/a,
$$

define

$$
x_{\{d\}}=\frac\varepsilon h\quad(d\in D),\qquad
x_C=(a-1)\varepsilon,\qquad
x_{C\setminus\{i\}}=\frac{1-a\varepsilon}{a+1}\quad(i\in C),
\tag{5.1}
$$

and set all other masses to zero. Denote this family by $\mathcal S(a,h)$. At $h=1$ it is the family of [*CDSO incidence moments and capacity phases*, Theorem 10.1](CDSO_INCIDENCE_MOMENTS_AND_CAPACITY_PHASES.md); the tail singleton mass is now split equally over $h$ labels. Its actual marginals and mean are

$$
y_i=\frac{a-\varepsilon}{a+1}\quad(i\in C),\qquad
y_d=\frac\varepsilon h\quad(d\in D),\qquad
\mathbb E K=a.
$$

Indeed the masses sum to $\varepsilon+(a-1)\varepsilon+1-a\varepsilon=1$, and the mean is $\varepsilon+(a+1)(a-1)\varepsilon+a(1-a\varepsilon)=a$. The parameter domain is exactly the one giving nonnegative displayed masses and positive marginals. Its endpoint $\varepsilon=1/a$ is called the cap. At that endpoint the missing-one types have zero mass, as permitted in Definition 1.1.

**Proposition 5.2 (A sufficient and necessary cap criterion within this family).** For $a\ge2$ and $h\ge1$, set

$$
\Gamma_a=\frac{2a^3+2a^2+2a+1}{(a-1)^2}.
$$

The scalar minimum over the entire actual family $\mathcal S(a,h)$ is at its cap if and only if $h^2\ge\Gamma_a$. In that case it is unique in the parameter and has energy

$$
\min_{x\in\mathcal S(a,h)}H(x)
=\frac{a(a+1)^3}{a-1}+ah^2.
\tag{5.2}
$$

For every sequence (1.2) with $\kappa>\sqrt2$, the cap condition holds eventually and

$$
\frac{\min_{x\in\mathcal S(a_n,h_n)}H(x)-B_0(a_n)}{a_n^2}
\longrightarrow\kappa^2+2.
\tag{5.3}
$$

**Proof.** Direct summation in (5.1) gives energy

$$
\phi_{a,h}(\varepsilon)=C_a(\varepsilon)+\frac{h^2}\varepsilon,
\qquad
C_a(\varepsilon)=\frac{a^2r^2}{a-\varepsilon}
 +\frac{V\varepsilon}{(a-\varepsilon)^2},
\qquad V=(2a+1)(a-1)r^3>0.
\tag{5.4}
$$

For example the equivalent expression

$$
C_a(\varepsilon)
=\frac{r^2[a^3+(2a^3-2a-1)\varepsilon]}{(a-\varepsilon)^2}
$$

follows by expansion and is the core term in the energy of Theorem 10.1 cited above. Only the singleton term changes from $1/\varepsilon$ to $h^2/\varepsilon$.

On $0<\varepsilon\le1/a$, all denominators in (5.4) are positive and

$$
\phi_{a,h}''(\varepsilon)
=\frac{2h^2}{\varepsilon^3}
 +\frac{2a^2r^2}{(a-\varepsilon)^3}
 +\frac{V(4a+2\varepsilon)}{(a-\varepsilon)^4}>0.
$$

Thus the derivative is strictly increasing. At the cap, differentiation of (5.4) gives

$$
\phi_{a,h}'(1/a)=a^2(\Gamma_a-h^2).
\tag{5.5}
$$

If this is nonpositive, the derivative is negative everywhere to the left of the cap, so the cap is the unique minimum. If it is positive, values immediately to the left are smaller, so the cap cannot minimize. In this latter case $\phi_{a,h}'(\varepsilon)\to-\infty$ as $\varepsilon\downarrow0$, and strict convexity gives a unique interior minimum. This also establishes existence of the scalar minimum on its half-open actual domain.

At the cap the core is the full set of size $a+1$ with probability $(a-1)/a$, giving core energy $a(a+1)^3/(a-1)$ and tail energy $ah^2$. This proves (5.2). Since $\Gamma_a/a\to2$ and $h_n^2/a_n\to\kappa^2>2$, the cap criterion holds eventually along the sequences under consideration. Finally

$$
\frac{a(a+1)^3/(a-1)-a(a+1)^2}{a^2}
=\frac{2(a+1)^2}{a(a-1)}\longrightarrow2,
\qquad \frac{ah^2}{a^2}\longrightarrow\kappa^2,
$$

which proves (5.3). ∎

**Theorem 5.3 (A two-label enlargement beats the entire specified family).** Let $\kappa>2\sqrt2$ and take any sequence (1.2). For all sufficiently large $n$, the actual law

$$
|C|=a_n+2,\qquad |D|=h_n-1,\qquad
x_C=\frac{a_n-1}{a_n+1},\qquad
x_{\{d\}}=\frac{2}{(a_n+1)(h_n-1)}\quad(d\in D),
\tag{5.6}
$$

with all other masses zero, has strictly smaller energy than every member of $\mathcal S(a_n,h_n)$. Its limiting normalized gap is $\kappa^2/2+6$, strictly below the family minimum limit $\kappa^2+2$.

**Proof.** The conditions $a\ge2$, $h\ge2$ make (5.6) precisely (3.1) with $j=2$, so its mean, positive actual marginals and exact energy follow from Theorem 3.1. The normalized energy difference between it and the minimum of $\mathcal S(a,h)$ tends, by (3.3) and Proposition 5.2, to

$$
\left(\frac{\kappa^2}{2}+6\right)-(\kappa^2+2)
=4-\frac{\kappa^2}{2}<0.
$$

The difference is therefore strictly negative eventually, proving comparison against the entire explicitly defined family, including its interior parameters. This conclusion concerns the growing-surplus regime and does not assert a failure of any fixed-$h$ endpoint theorem. ∎

**Proposition 5.4 (Two explicit ratio sequences).** Along $a=b^2$, $h=3b$, with integers $b\to\infty$, the law (5.6) has normalized gap tending to $21/2$, whereas the minimum in $\mathcal S(a,h)$ has normalized gap tending to $11$. Along $a=b^2$, $h=4b$, the unrestricted infimum has normalized gap tending to $14$, whereas the minimum in $\mathcal S(a,h)$ has normalized gap tending to $18$.

**Proof.** In the first sequence $\kappa=3$; apply Theorem 3.1 at $j=2$ and Proposition 5.2. In the second sequence $\kappa=4$; apply Theorem 4.4 at $j=2$ and Proposition 5.2. All laws in these comparisons are in the original positive-marginal domain. ∎

## 6. Unresolved global values

**Open problem 6.1 (Ratios outside the matching set).** For $\kappa\in(0,\infty)\setminus\{2,4,6,\ldots\}$, determine whether $D_n$ converges along every sequence (1.2), whether its limit is independent of that sequence, and, if so, its value. Theorems 4.2 and 4.4 establish only the bounds (4.2) and the exact values at positive even ratios. In particular, the integer core phases of Proposition 4.3 are upper bound phases; equality of $U(\kappa)$ with a global limit at other ratios is not established.

The admissible class still permits partially occupied dense cores, several tail labels in one event, mixed core cardinalities and general joint supports. A lower bound matching (4.1), or an actual law improving it, must account for their marginals and event probabilities within the same law. The minimum of the selected family $\mathcal S(a,h)$ supplies no such lower bound for $M(a,h)$.

No classification or attainment of the finite infimum, stability assertion, realization by connected finite graphs at prescribed budgets, or uniform sharp asymptotic for $h=o(\sqrt a)$ follows from the results here. The parameter regime (1.2) has fixed positive limiting ratio; the constants and errors for fixed $j,v$ in Section 3 are used only in that regime. The cited repository comparisons supply the baseline and shared marginal relation, while the original graph-index literature supplies no input theorem for the array extremum proved here. No assertion of literature priority is made.

## 追加锚（本行以下为增补区）

## 7. The unrestricted square-root surplus value

**Lemma 7.1 (A core and tail certificate from one law).** Fix constants $C\ge1$ and $0<L\le R<\infty$. There are constants $A,E<\infty$, depending only on $C,L,R$, with the following property. For every pair of integers $a\ge A$, $h\ge1$ with $L\le h/\sqrt a\le R$, and every law $x\in\mathcal X(a,h)$ satisfying

$$
H(x)\le a^3+Ca^2,
\tag{7.1}
$$

there are an integer $j$ and a real number $v$ such that

$$
1\le j\le4C,\qquad \frac{L^2}{8C}\le v\le j+Ea^{-1/2},
\tag{7.2}
$$

and

$$
\frac{H(x)-B_0(a)}{a^2}
\ge \frac{(h+1-j)^2}{av}+2v+2j-2-Ea^{-1/2}.
\tag{7.3}
$$

More precisely, $a+j$ is the number of labels in a set $\mathcal C$ determined by the actual marginals of $x$, and $v=a\mathbb P_x(T\cap\mathcal D\ne\varnothing)$ for its complement $\mathcal D=[s]\setminus\mathcal C$. Thus the integer and the probability in (7.2)–(7.3) belong to the same law.

**Proof.** All constants implicit in $O(\cdot)$ in this proof depend only on $C,L,R$; the estimates hold uniformly over (7.1). Put $I_i=\mathbf1_{\{i\in T\}}$ and $V=\operatorname{Var}(K)$. Since $y_i\le1$,

$$
H\ge\mathbb E K^3,\qquad
\mathbb E K^3-a^3
=\mathbb E[(K-a)^2(K+2a)]\ge2aV.
\tag{7.4}
$$

The identity follows by expanding and using $\mathbb E K=a$. Consequently

$$
V\le Ca/2,\qquad p_*:=\mathbb P(K<a/2)\le2C/a.
\tag{7.5}
$$

The second inequality follows by bounding $(K-a)^2$ below by $a^2/4$ on that event. The nonnegative residual is

$$
\mathcal R=H-\mathbb E K^3
=\sum_i\mathbb E[K^2I_i](y_i^{-2}-1)\le Ca^2.
$$

Set $z_i^*=\mathbb P(i\in T,K\ge a/2)$. Restricting the nonnegative summands to $K\ge a/2$ yields

$$
\sum_i z_i^*(y_i^{-2}-1)\le4C.
\tag{7.6}
$$

Take $b=4C$ and define

$$
\mathcal C=\{i:y_i\ge b/a\},\qquad
\mathcal D=[s]\setminus\mathcal C.
$$

For $i\in\mathcal C$, (7.5) gives $z_i^*\ge y_i-p_*\ge y_i/2$. Hence

$$
\sum_{i\in\mathcal C}(y_i^{-1}-y_i)\le8C,
\qquad y_i\ge c:=(8C+1)^{-1}\quad(i\in\mathcal C).
\tag{7.7}
$$

Indeed each nonnegative summand in the sum is at most $8C$, so $1/y_i\le8C+y_i\le8C+1$. This produces a fixed positive lower bound on core marginals from (7.1), without assuming one in the original domain.

Write

$$
m=|\mathcal C|,\qquad n=|\mathcal D|,\qquad
t=\sum_{i\in\mathcal D}y_i,\qquad
\delta=\sum_{i\in\mathcal C}(1-y_i).
$$

Since $y^{-1}-y\ge2(1-y)$ on $(0,1]$, (7.7) implies $\delta\le4C$. The common marginal budget gives

$$
a=m-\delta+t,\qquad n=h+1-\delta+t,
\qquad t\le\frac{bn}{a}.
\tag{7.8}
$$

Thus, for $a>b$,

$$
h+1-4C\le n\le\frac{h+1}{1-b/a}=O(\sqrt a),
\qquad t=O(a^{-1/2}).
\tag{7.9}
$$

The integer $j=m-a=\delta-t$ therefore satisfies $0\le j\le4C$ for all sufficiently large $a$: its lower bound follows from $j\ge-t>-1$. In particular

$$
m=a+j,\qquad n=h+1-j,\qquad n\ge L\sqrt a/2>0
\tag{7.10}
$$

once $a$ is sufficiently large.

Consider the actual event

$$
A=\{T\cap\mathcal D\ne\varnothing\},\qquad
p=\mathbb P(A),\qquad e=\mathbb E[K\mathbf1_A],
$$

and the tail energy

$$
H_D=\mathbb E\left[K^2\sum_{i\in T\cap\mathcal D}y_i^{-2}\right].
$$

Positivity of every marginal and $n>0$ imply $p>0$. For $i\in\mathcal D$ one has $y_i<b/a$, so the tail contribution to $\mathcal R$ gives

$$
(1-b^2/a^2)H_D\le\mathcal R,\qquad H_D\le2Ca^2
\tag{7.11}
$$

for sufficiently large $a$. If $K_D=|T\cap\mathcal D|$, then $K_D\ge1$ on $A$. Therefore

$$
\mathbb E[K^2\mathbf1_A]
\le\mathbb E[K^2K_D]
\le\frac{b^2}{a^2}H_D\le Q:=2Cb^2.
\tag{7.12}
$$

Cauchy–Schwarz gives $e\le\sqrt{Qp}$. On $A^c$ one has $T\subseteq\mathcal C$ and $K\le m$, whence the mean constraint implies

$$
a\le m(1-p)+e,\qquad mp\le j+e\le j+\sqrt{Qp}.
$$

Using $\sqrt{Qp}\le mp/2+Q/(2m)$ gives

$$
p\le\frac{2j}{m}+\frac Q{m^2}=O(a^{-1}),\qquad
e=O(a^{-1/2}).
\tag{7.13}
$$

Put $v=ap$. As $j\ge0$ and $m=a+j$, the preceding mean inequality also gives

$$
v\le mp\le j+O(a^{-1/2}).
\tag{7.14}
$$

To bound the tail energy sharply using this same probability, put

$$
U_D(T)=\sum_{i\in T\cap\mathcal D}y_i^{-1}.
$$

The actual marginal identity gives $\mathbb E U_D=n$. Pointwise Cauchy–Schwarz and $K_D\le K\le K^2$ give

$$
U_D^2\le K_D\sum_{i\in T\cap\mathcal D}y_i^{-2}
\le K^2\sum_{i\in T\cap\mathcal D}y_i^{-2}.
$$

Since $U_D=0$ on $A^c$, another application of Cauchy–Schwarz gives

$$
H_D\ge\mathbb E U_D^2\ge\frac{n^2}{p},\qquad
v\ge\frac{n^2}{2Ca}\ge\frac{L^2}{8C}.
\tag{7.15}
$$

Combining this positive lower bound with (7.14) excludes $j=0$ for all sufficiently large $a$. This proves (7.2), after enlarging the uniform constant.

It remains to retain the core contribution to order $a^2$, including the change of marginals under conditioning. The following elementary estimate will be applied to the conditional law. Suppose a law on nonempty subsets of $[m]$ has mean $q=m-d$ and marginals $u_i\ge\gamma>0$. With its own energy denoted by $H_m$ and $Z_T=\sum_{i\in T}u_i^{-2}$, one has

$$
\sum_i u_i^{-1}\ge m+d,\qquad
\sum_i u_i^{-2}\le m+2d/\gamma^2.
$$

The first inequality is $u^{-1}\ge2-u$ summed over $i$; the second follows from $u^{-2}-1\le2(1-u)/\gamma^2$. The exact identity and pointwise bound

$$
H_m=m^2\sum_i u_i^{-1}-\mathbb E[(m^2-K^2)Z_T],
\qquad 0\le m^2-K^2\le2m(m-K)
$$

therefore imply

$$
H_m\ge m^2(m+d)-2md(m+2d/\gamma^2)
=m^2q-4md^2/\gamma^2.
\tag{7.16}
$$

For each $i\in\mathcal C$, set

$$
r_i=\mathbb P(i\in T,A),\qquad z_i=y_i-r_i,\qquad \pi=1-p.
$$

By (7.13), $\pi>0$ for sufficiently large $a$. The conditional law $x^0=\mathcal L(T\mid A^c)$ is a law on nonempty subsets of $\mathcal C$ with

$$
y_i^0=z_i/\pi,\qquad q_0=(a-e)/\pi,\qquad
d_0=m-q_0=\frac{j+e-mp}{\pi}\ge0.
\tag{7.17}
$$

Here $d_0=O(1)$ and $r_i\le p=O(a^{-1})$. By (7.7), $z_i\ge c/2$ eventually, so $y_i^0\ge c/2$. Applying (7.16) to this actual conditional law yields

$$
H_0\ge m^2q_0-O(a),
\tag{7.18}
$$

where $H_0$ uses the conditional marginals $y_i^0$. The original and conditional denominators must be compared: the derivative of $u^{-2}$ on $u\ge c/2$ gives

$$
0\le z_i^{-2}-y_i^{-2}\le16c^{-3}r_i,
\qquad \sum_{i\in\mathcal C}r_i=\mathbb E[K-K_D;A]\le e.
$$

Let $H_C=H-H_D$. Restricting its nonnegative integrand to $A^c$, where $K\le m$, gives

$$
\begin{aligned}
H_C
&\ge\mathbb E\left[K^2\sum_{i\in T}y_i^{-2};A^c\right]\\
&\ge\mathbb E\left[K^2\sum_{i\in T}z_i^{-2};A^c\right]
       -16c^{-3}m^2e\\
&=\frac{H_0}{\pi}-16c^{-3}m^2e\\
&\ge\frac{m^2(a-e)}{(1-p)^2}-O(a^{3/2})\\
&\ge a^3+(2j+2v)a^2-O(a^{3/2}).
\end{aligned}
\tag{7.19}
$$

The equality uses $y_i^0=z_i/\pi$: $H_0=\pi\mathbb E[K^2\sum_{i\in T}z_i^{-2};A^c]$. For the last inequality, $m=a+j$, $p=v/a$, and boundedness of $j,v$ give

$$
\frac{m^2a}{(1-p)^2}
\ge(a+j)^2a(1+2v/a)
\ge a^3+(2j+2v)a^2,
$$

while $m^2e/(1-p)^2=O(a^{3/2})$. Adding (7.15) and (7.19), and using $B_0(a)=a^3+2a^2+a$, proves (7.3).

All divisions involve positive actual marginals or the positive event probabilities just established. The Cauchy–Schwarz inequality used here is the finite inner-product inequality; see S. Boyd and L. Vandenberghe, *Convex Optimization*, Appendix A.1 ([author-hosted text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf)). No independence of inclusion events, support connectedness, or restriction on the cardinalities was used. ∎

**Theorem 7.2 (Full positive-ratio limit and uniform error).** In the unrestricted domain of Definition 1.1, for every $0<L\le R<\infty$ there are finite constants $A_{L,R}$ and $C_{L,R}$ such that all integers $a\ge A_{L,R}$ and $h\ge1$ with $L\le h/\sqrt a\le R$ satisfy

$$
\left|\frac{M(a,h)-B_0(a)}{a^2}
             -U\!\left(\frac h{\sqrt a}\right)\right|
\le C_{L,R}a^{-1/2}.
\tag{7.20}
$$

In particular, for every sequence (1.2),

$$
\lim_{n\to\infty}D_n=U(\kappa).
\tag{7.21}
$$

For $0<\kappa\le\sqrt2$, the value is $2\sqrt2\,\kappa$. On $\kappa\ge\sqrt2$, the value is $F_1(\kappa)$ on $[\sqrt2,2\sqrt2]$, and is $F_j(\kappa)$ on

$$
[\,2\sqrt{j(j-1)},\ 2\sqrt{j(j+1)}\,]
\qquad(j\ge2).
\tag{7.22}
$$

At $2\sqrt{j(j+1)}$ the adjacent formulas $F_j,F_{j+1}$ agree, and no other integer branch attains the value. In the interior of each displayed integer interval its integer branch is unique. The linear formula and $F_1$ agree at $\sqrt2$.

Thus (7.21) determines every ratio in Open problem 6.1, and (7.22) identifies the upper-bound phases of Proposition 4.3 as phases of the unrestricted asymptotic value. The earlier bounds and even-ratio limits remain valid; the description of the other fixed positive ratios as unresolved is replaced by (7.21). This assertion concerns values and does not classify finite minimizers or all laws attaining a limiting value.

**Proof.** Introduce, only as an intermediate variational quantity,

$$
\mathcal V(k)=\inf_{\substack{j\in\mathbb Z_{\ge1}\\0<v\le j}}
\left(\frac{k^2}{v}+2v+2j-2\right)\qquad(k>0).
\tag{7.23}
$$

This infimum is attained in these scalar parameters. Indeed the choice $j=v=1$ has value $k^2+2$, whereas the objective is at least $2j-2$ and at least $k^2/v$. Thus a minimizing sequence has bounded $j$ and has $v$ bounded away from zero, after discarding terms above $k^2+3$; compactness for the finitely many remaining integers proves attainment. Uniformly for $L\le k\le R$, any scalar minimizer has

$$
j\le(R^2+4)/2,\qquad v\ge L^2/(R^2+2),\qquad v\le j.
\tag{7.24}
$$

These scalar assertions make no attainment claim for $M(a,h)$.

Take $C=R^2+10$ in Lemma 7.1 and put $k=h/\sqrt a$. For every law in its sublevel, (7.3) and boundedness of $j$ give

$$
\frac{H-B_0(a)}{a^2}
\ge\frac{k^2}{v}+2v+2j-2-O_{L,R}(a^{-1/2}).
\tag{7.25}
$$

Here $((h+1-j)^2/a)-k^2=2k(1-j)/\sqrt a+(1-j)^2/a$, and $v$ has the positive lower bound (7.2). If $v>j$, replace $v$ by $j$. By (7.2) the change is $O_{L,R}(a^{-1/2})$: the derivative $-k^2/v^2+2$ is bounded uniformly on the interval between $v$ and $j$, since $j\ge1$ and $v\ge L^2/(8C)$. Hence (7.25) is at least $\mathcal V(k)-O_{L,R}(a^{-1/2})$.

A law outside the sublevel already has

$$
\frac{H-B_0(a)}{a^2}>C-2-1/a>R^2+2\ge\mathcal V(k).
$$

The same lower bound therefore holds for every original law, with one uniform constant. Taking its infimum gives

$$
\frac{M(a,h)-B_0(a)}{a^2}
\ge\mathcal V(k)-O_{L,R}(a^{-1/2}).
\tag{7.26}
$$

In particular there is no assumption that an optimal law exists, nor any replacement of the original laws by independent marginal and moment data.

For the upper bound, use exactly the actual law of Proposition 3.2, choosing $j,v$ to minimize (7.23). By (7.24), for sufficiently large $a$ one has $h\ge j$, uniformly over $L\le k\le R$, so these laws are admissible. To make its error estimate uniform, write $\mu=a+v$ and use its notation $\ell=\lfloor v\rfloor$, $\theta=v-\ell$. The core third moment in (3.4) has the exact expansion

$$
M_3=\mu^3+3\mu\theta(1-\theta)
                 +\theta(1-\theta)(1-2\theta)
=\mu^3+O_{L,R}(a).
$$

Since $p=v/(a+v-1)$ and $1/(1-p)=1+v/(a-1)$, (7.24) and (3.4) yield

$$
\frac{(a+j)^2M_3}{(1-p)(a+v)^2}
=a^3+(2j+2v)a^2+O_{L,R}(a),
$$

$$
\frac{(h+1-j)^2}{p}
=\frac{(h+1-j)^2(a+v-1)}v
=\frac{k^2}{v}a^2+O_{L,R}(a^{3/2}).
$$

All constants are uniform also when $v$ crosses an integer, since $0\le\theta<1$. Subtracting $B_0(a)$ and using that $M(a,h)$ is bounded above by each constructed energy proves

$$
\frac{M(a,h)-B_0(a)}{a^2}
\le\mathcal V(k)+O_{L,R}(a^{-1/2}).
\tag{7.27}
$$

Finally evaluate the scalar quantity in (7.23), without interpreting it as a restriction of the original domain. For fixed $j$, the minimizing $v$ is $\min(j,k/\sqrt2)$. Put $w=k/\sqrt2$. If $w\le1$, all $j\ge1$ permit $v=w$; the smallest $j=1$ gives $4w=2\sqrt2\,k$. If $w>1$, the integers $j\le w$ give the endpoint values $F_j(k)$. For $j>w$ the optimized value is $4w+2j-2$, increasing with $j$. When $w$ is not an integer and $r=\lfloor w\rfloor\ge1$, the smallest of these latter values exceeds $F_r(k)$ by

$$
4w+2r-F_r(k)=2-\frac{2(w-r)^2}{r}>0.
$$

When $w$ is an integer, each $j>w$ likewise gives $4w+2j-2>F_w(k)$. Thus no interior choice $v<j$ is globally minimizing when $k>\sqrt2$. Every endpoint choice is available in (7.23), so

$$
\mathcal V(k)=U(k).
\tag{7.28}
$$

Equations (7.26)–(7.28) prove (7.20). The adjacent branch comparison in Proposition 4.3 now applies to the unrestricted value and gives (7.22) and its ties. The function $U$ is continuous: on any compact positive interval only finitely many integer branches can minimize, their values agree at adjacent crossings, and the linear branch agrees with $F_1$ at $\sqrt2$. Every sequence (1.2) eventually lies in such a compact interval, so (7.20) gives (7.21). ∎

**Open problem 7.3 (Finite values and other scales).** Determine the exact finite infimum $M(a,h)$ and all equality or near-equality laws for the range where $a,h$ both vary. Determine the least thresholds for any eventual exact formulas, and sharp uniform estimates when $h/\sqrt a$ tends to zero or to infinity. Determine which optimizing or asymptotically optimizing laws admit connected finite-graph realizations at prescribed budgets. Theorem 7.2 supplies a uniform value estimate only on fixed compact subintervals of $(0,\infty)$; neither its integer label counts nor its constructed laws constitute such an equality classification or graph realization theorem.

The CDSO normalization is the one cited in Definition 1.1 through the parent volume: A. M. Albalahi, S. Das, A. Ali, J. Barman and A. E. Hamza, *On the hyperbolic Sombor index and its counterpart*, Discrete Math. Lett. 16 (2025), 108–115, DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176), p.109. No finite-graph extremal assertion from that source is a premise of Lemma 7.1 or Theorem 7.2. Their lower certificate is a deduction for the common-law domain (1.1), using the existing constructions solely for the matching upper bound. The relation to K. Zhao and X. Zhao, *Extremal values with respect to vertex-degree-based topological indices in unicyclic and bicyclic graphs*, DOI [10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26), is undetermined without its full text; its metadata and abstract supply no mathematical premise here.

## 追加锚（本行以下为增补区）

## 8. Diverging surplus ratios and the transition scale

**Definition 8.1 (Scale and error conventions).** In this section $a\ge4$ and $h\ge1$ are integers, $s=a+1+h$, and $M(a,h)$ and $B_0(a)$ retain Definition 1.1. In particular, the infimum is over all laws in $\mathcal X(a,h)$, with arbitrary nonempty cardinalities, zero type masses, arbitrarily small positive actual marginals and possibly disconnected support. Put

$$
\rho_a=\frac{h}{a^{3/2}}.
\tag{8.1}
$$

Every sequential limit below is asserted for every sequence of these integers with $a\to\infty$ and the displayed scale assumptions. For a fixed compact interval $I=[\rho_-,\rho_+]\subset(0,\infty)$, an error $O_I(a^{-1})$ has a constant and a starting value of $a$ depending only on $I$, uniformly over all integers $h$ with $\rho_a\in I$.

**Theorem 8.2 (The surplus between the square-root and transition scales).** For every integer sequence with

$$
\frac{h}{\sqrt a}\longrightarrow\infty,
\qquad \frac{h}{a^{3/2}}\longrightarrow0,
$$

one has

$$
\frac{M(a,h)-B_0(a)}{a^{3/2}h}\longrightarrow4.
\tag{8.2}
$$

**Proof.** Theorem 2.1 is a lower bound for every original law, so

$$
M(a,h)-B_0(a)
\ge\beta_a(h+1)-2a^2-a.
$$

Here $\beta_a/a^{3/2}\to4$, $h\to\infty$ and $\sqrt a/h\to0$. Division by $a^{3/2}h$ gives the lower limit at least $4$.

For a matching upper bound choose

$$
j=\left\lceil\frac{h}{2\sqrt a}\right\rceil.
$$

Then $j\to\infty$, $j/a\to0$, $j/h\to0$ and $j\sqrt a/h\to1/2$. In particular $1\le j\le h$ eventually. Use the exact law of Theorem 3.1 at this varying integer $j$, rather than its fixed-$j$ asymptotic formula. Its feasibility for each such integer can also be read directly: with $m=a+j$, $n=h+1-j$ and $p=j/(m-1)$, the core mass $1-p=(a-1)/(m-1)$ and the $n$ singleton masses $p/n$ sum to one, their actual marginals are respectively $1-p>0$ and $p/n>0$, and

$$
\mathbb E K=(1-p)m+p=m-p(m-1)=a.
$$

Thus, for every $1\le j\le h$, not just fixed $j$, the unrestricted infimum is at most the exact energy

$$
H_j(a,h)=\frac{(a+j)^3(a+j-1)}{a-1}
       +\frac{(h+1-j)^2(a+j-1)}j.
\tag{8.3}
$$

For $1\le j\le a/2$, expansion of its first term has a uniform remainder:

$$
\begin{aligned}
\frac{(a+j)^3(a+j-1)}{a-1}
 &=a^3+4a^2j+R_{a,j},\\
R_{a,j}
 &=\frac{a^2j+3a(2a-1)j^2+(4a-1)j^3+j^4}{a-1}
 =O(aj^2+aj).
\end{aligned}
\tag{8.4}
$$

The constant is absolute, as follows by bounding $j/a\le1/2$ in the displayed expression. Our choice of $j$ eventually lies in this range. The contribution of $4a^2j$ divided by $a^{3/2}h$ tends to $2$, while the remainder divided by the same quantity is

$$
O\!\left(\frac{h}{a^{3/2}}+\frac1a\right)=o(1).
$$

For the other term of (8.3), the exact normalized expression is

$$
\frac{(h+1-j)^2(a+j-1)}{j a^{3/2}h}
=\left(\frac{h+1-j}{h}\right)^2
 \frac{a+j-1}{a}\,\frac{h}{j\sqrt a}
\longrightarrow2.
$$

Finally $(B_0(a)-a^3)/(a^{3/2}h)=(2a^2+a)/(a^{3/2}h)\to0$. This actual law gives the upper limit at most $4$, proving (8.2). No law attaining $M$ was used. ∎

**Definition 8.3 (Transition profile).** For $\rho>0$, let $t(\rho)>1$ be the unique solution of

$$
\rho=2(t-1)t^{3/2},
\qquad F(\rho)=t(\rho)^4\bigl(4t(\rho)-3\bigr).
\tag{8.5}
$$

Uniqueness and existence follow because $t\mapsto2(t-1)t^{3/2}$ is continuous on $(1,\infty)$, has derivative $\sqrt t(5t-3)>0$, and has endpoint limits $0$ and $\infty$.

**Theorem 8.4 (Full-law transition value and uniform first correction).** For every $I=[\rho_-,\rho_+]\subset(0,\infty)$ there are constants $C_I<\infty$ and $A_I$ such that all integers $a\ge A_I$, $h\ge1$ with $\rho_a=h/a^{3/2}\in I$ satisfy

$$
\left|\frac{M(a,h)}{a^3}-F(\rho_a)
           +\frac{2\rho_a t(\rho_a)}{\sqrt a}\right|
\le\frac{C_I}{a}.
\tag{8.6}
$$

The profile also has the variational representation

$$
F(\rho)=\min_{0<p<1}\left\{(1-p)^{-4}+\frac{\rho^2}{p}\right\}.
\tag{8.7}
$$

Consequently every integer sequence with $\rho_a\to\rho\in(0,\infty)$ has $M(a,h)/a^3\to F(\rho)$. The normalization in (8.6) uses $h$, with $s=a+1+h$ still exact.

**Proof.** First, under $t=(1-p)^{-1}$ the objective in (8.7) becomes

$$
f_\rho(t)=t^4+\rho^2\frac{t}{t-1},\qquad t>1.
$$

It diverges at both endpoints, and

$$
f_\rho'(t)=4t^3-\frac{\rho^2}{(t-1)^2},\qquad
f_\rho''(t)=12t^2+\frac{2\rho^2}{(t-1)^3}>0.
$$

Its unique minimum is at the solution of (8.5); substitution gives $f_\rho(t)=t^4(4t-3)$. This proves (8.7). The inverse defining $t(\rho)$ is continuous. Thus, for $\rho\in I$, its values lie in an interval $[1+\delta,T]$ with $\delta>0$ and $T<\infty$ depending only on $I$.

For the full-law lower bound, reuse the pointwise certificate underlying Theorem 2.1 with a movable real contact parameter. The necessary scaled calculation is as follows. For any real $c\ge2$, put

$$
\begin{aligned}
b(c)&=4c(c-1)\sqrt{c+1}-2c^2+4c,\\
L_c&=5c^4-2b(c)c,\qquad N_c=4c^5-b(c)c^2,\\
W_c(k,v)&=kv^2-L_ck-b(c)v+N_c.
\end{aligned}
\tag{8.8}
$$

We claim $W_c(k,v)\ge0$ for all real $k\ge1$, $v\ge k^2$. Write $b=b(c)$. The inequalities

$$
\begin{aligned}
b-2c^2&=4c(c-1)(\sqrt{c+1}-1)\ge0,\\
2c^3-b&=2c(c-1)(c+2-2\sqrt{c+1})\ge0
\end{aligned}
$$

follow from $c\ge2$ and $(c+2)^2-4(c+1)=c^2\ge0$. In particular $2c^2\le b\le2c^3$, $L_c\ge c^4>0$, and $k_0=(b/2)^{1/3}$ lies in $[1,c]$.

If $k\ge k_0$, then $\partial_vW_c=2kv-b\ge2k^3-b\ge0$ on $v\ge k^2$. Its minimum there is at $v=k^2$, and the exact factorization is

$$
W_c(k,k^2)
=(k-c)^2\bigl(k^3+2ck^2+3c^2k+4c^3-b\bigr)\ge0,
\tag{8.9}
$$

since the factor in parentheses is at least $2c^3$.

If $1\le k\le k_0$, the unconstrained minimizer $v=b/(2k)$ is feasible. Its value multiplied by $4k$ equals the concave quadratic

$$
Q_c(k)=4N_ck-4L_ck^2-b^2.
$$

The formula for $b$ gives the exact identity

$$
b^2+4(c^2-2c)b=16c^5-20c^4,
$$

and hence $Q_c(1)=0$. At $k=k_0$ the minimizing $v$ is $k_0^2$, so (8.9) gives $Q_c(k_0)\ge0$. A concave quadratic lies above the chord between these two endpoint values. It follows that $Q_c\ge0$ throughout $[1,k_0]$, proving the claim on the remaining interval as well.

For any law in Definition 1.1, the common-law identities (2.3) give

$$
\mathbb E K=a,\qquad \mathbb E U=s,\qquad
 aU\ge K^2,\qquad H\ge\mathbb E(KU^2).
$$

They are necessary relations for that same law, with no assumption on the shape of its support. Taking the expectation of $W_c(K,aU)\ge0$ therefore gives

$$
H(x)\ge G_c(a,s):=\frac{aL_c+ab(c)s-N_c}{a^2}.
\tag{8.10}
$$

One can retain the full nonnegative remainder in this step:

$$
\begin{aligned}
H(x)-G_c(a,s)
 &=\mathcal D(x)+\frac1{a^2}\mathbb E W_c(K,aU),\\
\mathcal D(x)
 &=\mathbb E\left[K\sum_{\substack{i<j\\i,j\in T}}
                  (y_i^{-1}-y_j^{-1})^2\right]\ge0.
\end{aligned}
\tag{8.11}
$$

Indeed $K\sum_{i\in T}y_i^{-2}-U^2=\sum_{i<j,\,i,j\in T}(y_i^{-1}-y_j^{-1})^2$, and multiplying by $K$ proves the identity. For a proposed energy bound $E_0$, any actual law with $H(x)\le E_0$ must consequently satisfy

$$
\mathcal D(x)+a^{-2}\mathbb E W_c(K,aU)
\le E_0-G_c(a,s)\qquad(c\ge2).
\tag{8.12}
$$

These are necessary residual constraints, not a sufficiency statement for realizability or an equality classification. All expectations are finite because $[s]$ is finite and the actual marginals are positive. At $c=a$, $b(a)/a=\beta_a$ and (8.10) is exactly Theorem 2.1. Thus the certificate is its continuous-contact version, used here to obtain the moving-scale lower bound. Taking expectations of a pointwise bound is the weak-duality principle in D. Bertsimas and I. Popescu, *Optimal inequalities in probability theory: A convex optimization approach*, SIAM J. Optim. 15(3) (2005), 780–804, Theorem 2.1, pp.784–785, DOI [10.1137/S1052623401399903](https://doi.org/10.1137/S1052623401399903) ([author-hosted text](https://www.mit.edu/~dbertsim/papers/MomentProblems/Optimal-inequalities-in-probability-theory-A-convex-optimization-approach-SIAM15.pdf)). Only this elementary direction is used; neither strong duality nor a reduction of the actual-law domain to finitely many cardinalities is required.

Now set $t=t(\rho_a)$ and choose $c=at$ in (8.10). Keeping the exact relation $s=a+1+h$, elementary rearrangement yields

$$
\frac{G_{at}(a,s)}{a^3}
=t^4(5-4t)+\frac{b(at)}{a^{5/2}}
 \left(\rho_a+\frac{(t-1)^2}{\sqrt a}+\frac1{a^{3/2}}\right).
\tag{8.13}
$$

Uniformly for $t\in[1+\delta,T]$, the formula for $b$ gives

$$
\frac{b(at)}{a^{5/2}}
=4t^{5/2}-\frac{2t^2}{\sqrt a}+O_I(a^{-1}).
\tag{8.14}
$$

For example, write the radical part as $4(at)^{5/2}(1-(at)^{-1})\sqrt{1+(at)^{-1}}$; its difference from $4(at)^{5/2}$ is $O_I(a^{3/2})$, while the remaining terms are $-2a^2t^2+4at$. This proves (8.14) with a uniform bound. Multiplying (8.13) out gives

$$
\begin{aligned}
\frac{G_{at}(a,s)}{a^3}
={}&t^4(5-4t)+4\rho_a t^{5/2}\\
 &+\frac{-2\rho_a t^2+4t^{5/2}(t-1)^2}{\sqrt a}
 +O_I(a^{-1})\\
={}&F(\rho_a)-\frac{2\rho_a t}{\sqrt a}+O_I(a^{-1}).
\end{aligned}
\tag{8.15}
$$

The last equality uses $\rho_a=2(t-1)t^{3/2}$ separately in the leading term and in the coefficient of $a^{-1/2}$. Since (8.10) holds for every original law, (8.15) bounds their infimum from below, uniformly on $I$ and without attainment.

For the upper bound, choose the integer

$$
j=\lfloor a(t-1)\rfloor,\qquad z=\frac{a+j}{a}.
$$

Uniformly on $I$, for all sufficiently large $a$ one has $j\ge1$, $j\le a(T-1)\le h$, $|z-t|\le a^{-1}$ and $z-1\ge\delta/2$. Thus the actual law in (8.3) is admissible. Its energy has the exact normalized expression

$$
\frac{H_j(a,h)}{a^3}
=\frac{z^3(z-a^{-1})}{1-a^{-1}}
 +\left(\rho_a-\frac{z-1}{\sqrt a}+\frac1{a^{3/2}}\right)^2
       \frac{z-a^{-1}}{z-1}.
\tag{8.16}
$$

The second factor retains the full number $h+1-j$ of singleton labels. On $\rho_a\in I$, $z\in[1+\delta/2,T+1]$, all denominators in (8.16) stay uniformly away from zero, and expansion gives

$$
\frac{H_j(a,h)}{a^3}
=f_{\rho_a}(z)-\frac{2\rho_a z}{\sqrt a}+O_I(a^{-1}).
\tag{8.17}
$$

Explicitly, the first term in (8.16) is $z^4+O_I(a^{-1})$, and the other is $\rho_a^2z/(z-1)-2\rho_a z/\sqrt a+O_I(a^{-1})$. The derivatives of $f_{\rho_a}$ on the displayed compact set are uniformly bounded, so $|z-t|\le a^{-1}$ gives $f_{\rho_a}(z)=F(\rho_a)+O_I(a^{-1})$. Also $2\rho_a(z-t)/\sqrt a=O_I(a^{-3/2})$. Hence the actual-law upper bound is

$$
\frac{M(a,h)}{a^3}\le\frac{H_j(a,h)}{a^3}
=F(\rho_a)-\frac{2\rho_a t(\rho_a)}{\sqrt a}
 +O_I(a^{-1}).
$$

Together with (8.15) this proves (8.6). All upper bounds use actual probabilities, their own actual marginals and the exact mean $a$; the scalar minimum (8.7) supplies no substitute for the full-law lower bound. Continuity of $F$ gives the sequential limit asserted in the theorem. ∎

**Theorem 8.5 (The supercritical label-square value).** For every integer sequence with $a\to\infty$ and $h/a^{3/2}\to\infty$,

$$
\frac{M(a,h)}{(a+1+h)^2}\longrightarrow1.
\tag{8.18}
$$

**Proof.** For every actual law, the identities (2.3), $K\ge1$ and Cauchy–Schwarz give the elementary lower bound

$$
H(x)\ge\mathbb E(KU^2)\ge\mathbb E U^2
       \ge(\mathbb E U)^2=s^2.
\tag{8.19}
$$

This uses the same actual marginals and puts no restriction on their positive values or on the cardinality layers. Thus $M(a,h)/s^2\ge1$.

For the matching upper bound put $\rho=h/a^{3/2}$ and choose

$$
j=\lceil a\rho^{2/5}\rceil.
$$

Then $j/(a\rho^{2/5})\to1$, $j/a\to\infty$, and

$$
\frac jh=O\!\left(a^{-1/2}\rho^{-3/5}+h^{-1}\right)\longrightarrow0.
$$

Consequently $1\le j\le h$ eventually, so (8.3) again is the energy of an actual admissible law. With $m=a+j$ and $n=h+1-j$, one has $m=O(a\rho^{2/5})$, and its core contribution satisfies

$$
\frac{m^3(m-1)}{(a-1)h^2}
=O(\rho^{-2/5})\longrightarrow0.
$$

Its singleton contribution satisfies

$$
\frac{n^2(m-1)}{jh^2}
=\left(\frac nh\right)^2\left(1+\frac{a-1}{j}\right)
\longrightarrow1.
$$

Here $n/h\to1$, while $s/h=1+(a+1)/h\to1$. Therefore $H_j(a,h)/s^2\to1$, supplying the matching upper bound for the unrestricted infimum. Combining it with (8.19) proves (8.18). ∎

**Open problem 8.6 (Finite values, residual regimes and realizations).** Theorems 8.2, 8.4 and 8.5 resolve the following parts of the diverging-ratio request in Open problem 7.3: the leading surplus for $\sqrt a\ll h\ll a^{3/2}$, the leading value and uniform first correction for $h/a^{3/2}$ in any fixed compact positive interval, and the leading value for $h\gg a^{3/2}$. Theorem 7.2 already determines all fixed positive limits of $h/\sqrt a$. The remaining mathematical questions include:

1. Determine the exact finite values $M(a,h)$, whether they are attained, and any least thresholds for eventual exact formulas.
2. Classify equality and near-equality laws, and establish quantitative stability in the relevant scales. The necessary residual constraints (8.11)–(8.12) do not establish such a classification or stability theorem.
3. Obtain sharp uniform estimates when $h/\sqrt a\to0$, and sharper remainders or uniform matching estimates in the moving regimes not specified by (7.20), (8.2), (8.6) or (8.18). In particular, the constant in (8.6) is not asserted to remain bounded when its compact interval approaches $0$ or $\infty$.
4. Determine which optimizing or asymptotically optimizing laws admit connected finite-graph realizations at prescribed budgets, and the corresponding graph extremal values. The array-law upper bounds above do not impose the graph realization constraints.

The graph normalization remains the one in Definition 1.1 and the Albalahi–Das–Ali–Barman–Hamza source cited after Open problem 7.3. It does not transfer (8.2), (8.6) or (8.18) to graph extrema. The relation of these array-law statements to the Zhao–Zhao article cited there remains undetermined without its full text; no literature-priority assertion is attached to them.

## 追加锚（本行以下为增补区）

## 9. Finite actual two-layer graphs at square-root surplus

The preceding sections optimize the common incidence law. This section keeps the
same law on the same finite graph and records the finite-budget interface. The
only new issue is that a law with a core and singleton tail must be rounded to
integer source counts while the graph remains simple, connected, and strictly
degree-oriented.

**Definition 9.1 (The finite graph class).** Fix integers $a\ge4$, $h\ge1$ and
put $s=a+1+h$. For $N\ge1$, let $\mathfrak G_N(a,h)$ be the class of finite
simple connected graphs $G=(S\mathbin{\dot\cup}T,E)$ with

$$
|S|=N,\qquad |T|=s,\qquad |E|=m=aN,\qquad |V(G)|=N+s,\qquad
\ell=m-|V(G)|+1=(a-1)N-s+1,
$$

such that both sides are independent, every edge joins $S$ to $T$, and

$$
 d_G(u)<d_G(v)\qquad(uv\in E,\ u\in S,\ v\in T).
\tag{9.1}
$$

Thus the vertices in $S$ and $T$ are the actual degree-oriented sources and
sinks. Define

$$
V_N(a,h)=\inf_{G\in\mathfrak G_N(a,h)}2N E(G),\qquad
E(G)=\sum_{uv\in E}\left(\sqrt{1+\left(\frac{d_G(u)}{d_G(v)}\right)^2}-1\right).
\tag{9.2}
$$

The infimum is a minimum whenever the class is nonempty, since the class has
only finitely many labelled simple graphs.

**Lemma 9.2 (The common-law quadratic bridge).** Let $G\in\mathfrak G_N(a,h)$,
write $k_u=d_G(u)$ for $u\in S$, $d_i=d_G(i)$ for $i\in T$, and let $x_T$ be
the law which assigns mass $1/N$ to the neighborhood of each source. Put
$y_i=d_i/N$. Then $x$ belongs to $\mathcal X(a,h)$, its mean is $a$, and

$$
H(x)=N\sum_{ui\in E}\left(\frac{k_u}{d_i}\right)^2.
\tag{9.3}
$$

For $0\le t<1$,

$$
 t^2-\frac{t^4}{4}\le2(\sqrt{1+t^2}-1)\le t^2.
\tag{9.4}
$$

Consequently, with $Q(G)=H(x)$,

$$
Q(G)-\frac N4\sum_{ui\in E}\left(\frac{k_u}{d_i}\right)^4
 \le 2NE(G)\le Q(G).
\tag{9.5}
$$

**Proof.** The neighborhood of a source is a nonempty subset of $[s]$,
$\sum_Tx_T=1$, and
$\mathbb E_xK=N^{-1}\sum_{u\in S}d_G(u)=m/N=a$. Its actual marginal at
sink $i$ is $y_i=d_i/N>0$. Substitution into Definition 1.1 gives (9.3).
The orientation condition gives $t=k_u/d_i<1$. The function
$\sqrt{1+z}$ has the alternating Taylor bounds
$1+z/2-z^2/8\le\sqrt{1+z}\le1+z/2$ for $0\le z\le1$;
putting $z=t^2$ and multiplying by $2$ proves (9.4), and summing proves
(9.5). Every quantity in (9.3) uses the degrees of this same graph. ∎

**Lemma 9.3 (Integer balanced realization with one connecting source).** Fix
$0<L\le R<\infty$ and put

$$
J=\left\lceil\frac{R^2+4}{2}\right\rceil,\qquad
v_0=\min\left\{1,\frac L{\sqrt2}\right\},\qquad
K_0=1+R+J+v_0^{-1}.
\tag{9.6}
$$

Set $c_0=2^{12}K_0^6$ and
$A_0=\max\{4,64K_0^2,16(J+1)^2/L^2\}$. If $a\ge A_0$,
$L\le k=h/\sqrt a\le R$, and $(j,v)$ satisfies

$$
j\in\mathbb Z,\qquad 1\le j\le J,\qquad v_0\le v\le j,\qquad
p=\frac v{a+v-1},\qquad \theta=v-\lfloor v\rfloor,
\tag{9.7}
$$

then for every integer $N\ge c_0a^5$ there is a graph
$G=G(a,h,N;j,v)$ in $\mathfrak G_N(a,h)$ with

$$
2NE(G)\le H_{j,v}(a,h)+c_0\left(a^{3/2}+\frac{a^6}{N}\right),
\tag{9.8}
$$

where $H_{j,v}$ is the exact law energy in (3.4). This includes integer $v$
and $v=j$.

**Proof.** Set $M=N-1$, $r=a+j$, and $n=h+1-j$. The threshold gives
$h\ge4(J+1)$, so $n\ge1$. Partition the sinks into a core $C$ of size $r$
and a tail $D$ of size $n$. Throughout the proof,

$$
r\le2a,\quad s\le2a,\quad n\le K_0\sqrt a,\quad
\frac1{2K_0a}\le p\le\frac14,\quad M\ge N/2.
$$

First choose the number of singleton sources, and then choose their
complement's degrees from the exact remaining edge budget. Specifically put

$$
T=\lfloor pM\rfloor,\qquad Q=M-T,\qquad
w=\frac{(a-1)T}{Q},\qquad b=\lfloor w\rfloor.
\tag{9.9}
$$

Here $Q\ge3M/4$ and $T\ge pM/2\ge M/(4K_0a)>0$. Since
$v=(a-1)p/(1-p)$, one has

$$
0\le w\le v\le j,\qquad
0\le v-w=\frac{(a-1)(p-T/M)}{(1-p)(1-T/M)}\le\frac{2a}{M}.
$$

Define integer source counts

$$
q_1=(a-1)T-bQ,\qquad q_0=Q-q_1.
\tag{9.10}
$$

Then $0\le q_1<Q$ and $q_0+q_1=Q$. Give $q_0$ core sources degree
$a+b$ and $q_1$ core sources degree $a+b+1$, omitting a zero-count branch.
If $b=j$, then $w=j$ and $q_1=0$; otherwise $b+1\le j$.
Thus every positive count requests at most $r$ distinct neighbors, including
at $v=j$. The core memberships and the total memberships are exactly

$$
(a+b)q_0+(a+b+1)q_1=aM-T,\qquad
(a+b)q_0+(a+b+1)q_1+T=aM.
\tag{9.11}
$$

For a balanced core assignment, label $C$ cyclically and write an infinite
periodic word containing these $r$ labels in order. Read a consecutive block
of length $a+b$ or $a+b+1$ for each core source, continuing immediately after
the preceding block. Each positive-count block has length at most $r$, so its
labels are distinct. In the resulting prefix of length $aM-T$, each label
occurs either $\lfloor(aM-T)/r\rfloor$ or
$\lceil(aM-T)/r\rceil$ times. These are the actual core incidence degrees
$D_i^C$. Give the $T$ singleton sources balanced tail neighborhoods, with
counts $t_d\in\{\lfloor T/n\rfloor,\lceil T/n\rceil\}$ and
$\sum_dt_d=T$. In particular,

$$
t_d+1\ge\frac Tn\ge\frac{M}{4K_0^2a^{3/2}}.
\tag{9.12}
$$

These assignments are simple: each source uses distinct labels, and sources
with repeated neighborhoods are different vertices.

Choose one core source and delete $h+1$ of its core memberships. Its degree
before deletion is at least $a$, and $h+1<a/2$ under $a\ge A_0$, so its
neighborhood remains nonempty. Add one new source adjacent to all $s$ sinks.
There are now exactly $N$ sources and

$$
[a(N-1)-(h+1)]+s=aN
\tag{9.13}
$$

edges. The new source makes the graph connected. Both sides are independent
and the graph is simple. At a core sink the deletion subtracts at most one
and the new source adds one; hence its final degree satisfies
$d_i\ge D_i^C\ge M/2-1\ge M/3$. At a tail sink the final degree is $t_d+1$.
By (9.12) and $M\ge c_0a^5/2$, every sink has degree strictly greater than
$2a\ge s$. Every source has degree at most $s$, so (9.1) holds with these
actual degrees. This proves membership in the full graph class.

For the energy estimate let $f(z)$ be the piecewise linear interpolation of
the integer cubes on $[a,r]$. For $a\le z\le r$ it satisfies
$0<f(z)\le8a^3$ and has Lipschitz constant at most $12a^2$. The ideal law in
Proposition 3.2 has core marginal $y_C=(a-p)/r\ge1/2$. Write

$$
\mu^*=My_C,\qquad S^*=M(1-p)f(a+v),\qquad
S=q_0(a+b)^3+q_1(a+b+1)^3=Qf(a+w).
\tag{9.14}
$$

The ideal core and tail energies are
$H_C=M S^*/(\mu^*)^2\le32a^3$ and $H_D=n^2/p\le2K_0^3a^2$,
so $H_{j,v}=H_C+H_D$. Since $|Q-M(1-p)|<1$ and $|w-v|\le2a/M$,

$$
|S-S^*|\le32a^3,\qquad
\frac{aM-T}{r}\ge\mu^*\ge M/2,\qquad d_i\ge\mu^*-1\quad(i\in C).
\tag{9.15}
$$

Deleting memberships only lowers the chosen source's squared degree and
removes nonnegative summands. The contribution to $Q(G)$ of the original
core sources is therefore at most $NS/(\mu^*-1)^2$. Using
$(1-1/\mu^*)^{-2}\le1+16/M$ and $M\ge16$ gives

$$
\begin{aligned}
\frac{NS}{(\mu^*-1)^2}
&\le\frac NM\left(1+\frac{16}{M}\right)H_C
       +\frac{32Na^3}{(\mu^*-1)^2}
 \le H_C+2^{11}\frac{a^3}{M},\\
N\sum_{d\in D}\frac{t_d}{(t_d+1)^2}
&\le\frac{Nn^2}{T}
 \le H_D+20K_0^4\frac{a^3}{M},\\
Ns^2\sum_{i\in C\cup D}\frac1{d_i^2}
&\le\frac{N}{M^2}\left(72a^3+64K_0^5a^{11/2}\right)
 \le272K_0^5\frac{a^{11/2}}{M}.
\end{aligned}
\tag{9.16}
$$

For the first line, $\mu^*-1\ge M/4$, $N/M=1+1/M$, and the multiplicative
factor on $H_C$ is at most $1+20/M$; the additive term is at most
$1024a^3/M$. For the second, $t_d+1\ge T/n$ gives the first inequality,
and $pM-T<1$, $T\ge pM/2$ give
$N p/T\le1+5/(pM)$. Multiplication by
$H_D\le2K_0^3a^2$ and $p^{-1}\le2K_0a$ gives the stated error.
The last line is the new source's contribution, using $d_i\ge M/3$ on the
$r\le2a$ core labels and (9.12) on the $n\le K_0\sqrt a$ tail labels.
Thus all three lines concern this single graph with its final degrees.

Since $K_0\ge4$, $a\ge1$ and $M\ge N/2$, their sum gives

$$
Q(G)=N\sum_{ui\in E(G)}(k_u/d_i)^2
 \le H_{j,v}(a,h)+2^{12}K_0^6\frac{a^6}{N}.
\tag{9.17}
$$

Indeed $2(2^{11}+20K_0^4+272K_0^5)\le2^{12}K_0^6$.
The upper inequality of (9.5) proves (9.8). No divisibility condition on $N$
or positive lower bound on either ideal core type mass was used. ∎

**Theorem 9.4 (Uniform finite-budget graph interface).** Fix
$0<L\le R<\infty$. Choose constants $A_7\ge4$, $C_7\ge0$ supplied by
Theorem 7.2, enlarging $C_7$ so that $C_7\ge2^8K_0^6$, and define

$$
\Gamma_{L,R}=R^2+2+2\sqrt2\,R,\qquad
K=1+R+J+v_0^{-1}+A_7+C_7+\Gamma_{L,R},
\tag{9.18}
$$

$$
A=\max\{A_7,\,64K^2,\,4C_7^2,\,16\Gamma_{L,R}^2,
          \,16(J+1)^2/L^2\},\qquad
D=2^{20}K^{12},\qquad C=2^{22}K^{12}.
\tag{9.19}
$$

For every integer $a\ge A$, every integer $h\ge1$ with
$L\le h/\sqrt a\le R$, and every integer

$$
N\ge\left\lceil Da^5\right\rceil,
\tag{9.20}
$$

$\mathfrak G_N(a,h)$ is nonempty and

$$
\left|\frac{V_N(a,h)-a(a+1)^2}{a^2}
       -U\!\left(\frac h{\sqrt a}\right)\right|
 \le C\left(a^{-1/2}+\frac{a^4}{N}\right).
\tag{9.21}
$$

The constants are deliberately nonminimal and depend only on $L,R$. In
particular, (9.20) is one explicit sufficient polynomial condition; no claim
is made about the least exponent or the least coefficient.

**Proof.** Write $k=h/\sqrt a$ and $B_0=a(a+1)^2$. By (7.23)--(7.28), a
minimizing pair $(j,v)$ for the scalar envelope satisfies (9.7): if
$k\le\sqrt2$ choose $j=1$, $v=k/\sqrt2$, and otherwise a minimizing integer
branch has $v=j$. The bound on $j$ is (7.24). The threshold $A$ in (9.19)
is at least $A_0$, and $D\ge c_0$.

With $r=a+j$, $p=v/(a+v-1)$, and the core and tail energies $H_C,H_D$
as in Lemma 9.3, put $\mu=a+v$ and $\theta=v-\lfloor v\rfloor$. The
interpolated third moment is
$f(\mu)=\mu^3+3\mu\theta(1-\theta)+\theta(1-\theta)(1-2\theta)$, so
$0\le f(\mu)-\mu^3\le\mu$. Since $r\le2a$, $p\le1/4$,
$1/(1-p)=1+v/(a-1)$ and $j,v,v^{-1},R\le K_0$, expansion of the two
terms of (3.4) gives the explicit bounds

$$
0\le H_C-[a^3+(2j+2v)a^2]\le64K_0^4a,\qquad
\left|H_D-\frac{k^2}{v}a^2\right|\le8K_0^3a^{3/2}.
$$

For the first bound expand $(a+j)^2(a+v)(1+v/(a-1))$; the interpolation
adds at most $6a$. For the second expand
$(h+1-j)^2(a+v-1)/v$ and use $|1-j|\le K_0$ and $h\le K_0\sqrt a$.
Consequently $C_7\ge2^8K_0^6$ and the scalar minimizing identity give

$$
H_{j,v}(a,h)\le B_0+a^2U(k)+C_7a^{3/2}.\tag{9.22}
$$

Lemma 9.3 therefore supplies an actual graph, proving nonemptiness and

$$
V_N(a,h)\le B_0+a^2U(k)+2^{13}K^{12}
       \left(a^{3/2}+\frac{a^6}{N}\right).\tag{9.23}
$$

For the lower bound, let $G\in\mathfrak G_N(a,h)$ and let $Q(G)$ be (9.3).
Theorem 7.2 applied to its actual profile gives

$$
Q(G)\ge M(a,h)\ge B_0+a^2U(k)-C_7a^{3/2}.\tag{9.24}
$$

Set $W=2NE(G)$ and $\gamma=2/(\sqrt2+1)$. For every edge ratio
$0\le t<1$,
$2(\sqrt{1+t^2}-1)=2t^2/(\sqrt{1+t^2}+1)\ge\gamma t^2$.
Thus $W\ge\gamma Q(G)$. The fixed threshold $4a^3$ separates all comparison
graphs into two cases. Since $U(k)\le\Gamma_{L,R}$ and $a\ge64K^2$,

$$
B_0+a^2U(k)\le a^3\left((1+1/a)^2+\Gamma_{L,R}/a\right)<2a^3.
$$

If $W\ge4a^3$, the required lower bound follows immediately. If $W<4a^3$,
then $Q(G)\le4a^3/\gamma$. The elementary inequality
$\sum_e t_e^4\le(\sum_e t_e^2)^2$ and (9.5) now give

$$
W\ge Q(G)-\frac{Q(G)^2}{4N}
 \ge Q(G)-\frac{4a^6}{\gamma^2N}
 \ge Q(G)-\frac{6a^6}{N}.
\tag{9.25}
$$

The last inequality uses $4/\gamma^2=3+2\sqrt2<6$. The estimate depends
only on the energy sublevel and the ratios of this graph.
Combining (9.24) with either case, and $C\ge C_7+6$, gives for every graph
in the original class, and hence for its infimum,

$$
V_N(a,h)\ge B_0+a^2U(k)-C\left(a^{3/2}+\frac{a^6}{N}\right).\tag{9.26}
$$

Together with (9.23), division by $a^2$ proves (9.21). The lower estimate used
all graphs in $\mathfrak G_N(a,h)$ through their own actual profiles and made
no support, symmetry, minimum-marginal, or cardinality restriction. ∎

**Corollary 9.5 (Common realized normalized limits).** Let
$a_r,h_r,N_r$ be integers with $a_r\to\infty$,
$h_r/\sqrt{a_r}\to\kappa\in(0,\infty)$, and
$N_r\ge Da_r^5$ eventually for some $0<L<\kappa<R<\infty$, where $D$ is
the constant in (9.19) for this interval. Then

$$
\frac{V_{N_r}(a_r,h_r)-a_r(a_r+1)^2}{a_r^2}\longrightarrow U(\kappa).\tag{9.27}
$$

**Proof.** Eventually $L\le h_r/\sqrt{a_r}\le R$ and $a_r\ge A$.
The graph class is then nonempty by Theorem 9.4, and its error bound tends
to zero because $a_r^4/N_r\le1/(Da_r)$. Continuity of $U$, proved in
Theorem 7.2, gives (9.27). Every quantity is taken from the finite graph
class at that same $(a_r,h_r,N_r)$, with no divisibility subsequence.
The construction includes integer $v$ and $v=j$, since a branch that would
exceed the core capacity has zero count. ∎

This theorem resolves the square-root-surplus finite graph interface requested
in Open problems 7.3 and 8.6. It does not determine finite equality cases,
least thresholds, graph isomorphism classes, other sink counts, other edge
budgets, moving intervals with $h/\sqrt a\to0$ or $\infty$, or global extrema
outside the two-layer class. The normalization is the CDSO normalization of
Definition 1.3 in *CDSO incidence moments and capacity phases* and of
Albalahi--Das--Ali--Barman--Hamza, DOI 10.47443/dml.2025.176, p.109. No
priority claim is made for the Zhao--Zhao article cited in Open problem 7.3;
its full text was not used.

## 追加锚（本行以下为增补区）

## 10. Quantitative actual-law stability at the transition scale

**Theorem 10.1 (Cardinality and singleton reciprocal stability).** Fix
$I=[\rho_-,\rho_+]\subset(0,\infty)$. There are finite constants $A_I,C_I$,
depending only on $I$, with the following property. For every pair of integers
$a\ge A_I$, $h\ge1$ such that $\rho_a=h/a^{3/2}\in I$, put $s=a+1+h$ and
$t=t(\rho_a)>1$, where

$$
\rho_a=2(t-1)t^{3/2}.
$$

For every actual law $x\in\mathcal X(a,h)$ of Definition 1.1 and every
$\epsilon\in[0,1]$, if

$$
H(x)\le M(a,h)+\epsilon a^3,
\tag{10.1}
$$

then all three estimates hold simultaneously:

$$
\mathbb E_x\left[\left(\frac Ka-t\right)^2
                   \mathbf1_{\{K\ge2\}}\right]
\le C_I\left(\epsilon+\frac1a\right),
\tag{10.2}
$$

$$
\left|\mathbb P_x(K=1)-\left(1-\frac1t\right)\right|
\le C_I\sqrt{\epsilon+\frac1a},
\tag{10.3}
$$

$$
\mathbb E_x\left[\left(\frac{U_T}{a^{3/2}}-2t^{5/2}\right)^2
                   \mathbf1_{\{K=1\}}\right]
\le C_I\left(\epsilon+\frac1a\right).
\tag{10.4}
$$

Here $K=|T|$, $\mathbb E_xK=a$, and $U_T=\sum_{i\in T}y_i^{-1}$ uses the
actual positive marginals of that same law. The assertions allow arbitrary
nonempty-subset support, zero type masses, arbitrarily small positive
marginals and disconnected support. They require neither a symmetry
assumption nor attainment of $M(a,h)$.

**Proof.** Retain $b(c),L_c,N_c,W_c$ from (8.8) and put
$k_0(c)=(b(c)/2)^{1/3}$. We first strengthen the nonnegativity calculation
in the proof of Theorem 8.4. There is an absolute finite $c_*\ge2$ such that,
for every real $c\ge c_*$ and all real $k\ge2$, $v\ge k^2$,

$$
W_c(k,v)\ge\frac12c^3(k-c)^2.
\tag{10.5}
$$

At the singleton contact there is also the exact identity

$$
W_c(1,v)=\left(v-\frac{b(c)}2\right)^2
\qquad(v\in\mathbb R).
\tag{10.6}
$$

To prove these claims, write $b=b(c)$ and $k_0=k_0(c)$. The identity
$Q_c(1)=0$ from the proof of Theorem 8.4 is
$N_c-L_c=b^2/4$, which gives (10.6). From the explicit formula (8.8),

$$
\frac{b(c)}{c^{5/2}}\longrightarrow4,\qquad
\frac{k_0(c)}c\longrightarrow0
\qquad(c\longrightarrow\infty).
$$

Choose $c_*$ large enough that, for all $c\ge c_*$,

$$
b(c)^2\ge8c^5,\qquad k_0(c)\le\frac c{10}.
\tag{10.7}
$$

Also $0<L_c\le5c^4$, as follows from $0<b(c)\le2c^3$ and (8.8).
If $k\ge k_0$, then $2kv-b\ge2k^3-b\ge0$ on $v\ge k^2$.
By the factorization (8.9) and $b\le2c^3$,

$$
\begin{aligned}
W_c(k,v)&\ge W_c(k,k^2)\\
&=(k-c)^2\bigl(k^3+2ck^2+3c^2k+4c^3-b\bigr)\\
&\ge2c^3(k-c)^2.
\end{aligned}
\tag{10.8}
$$

For $2\le k\le k_0$, completing the square, using
$N_c=L_c+b^2/4$, and then (10.7) gives

$$
\begin{aligned}
W_c(k,v)
&\ge N_c-L_ck-\frac{b^2}{4k}\\
&=\frac{b^2}{4}\left(1-\frac1k\right)-L_c(k-1)\\
&\ge\frac{b^2}{8}-5c^4k_0
\ge\frac12c^5.
\end{aligned}
\tag{10.9}
$$

In this range $0\le k\le c$, so $(k-c)^2\le c^2$. Thus (10.9) proves
(10.5) here, while (10.8) proves it on the rest of the range. In particular,
no intermediate integer cardinality between $2$ and the bulk contact is
omitted. The distinction between $k=1$ and $k\ge2$ is essential to this
uniform bound.

Now fix $I$ and the parameters in the theorem. Definition 8.3 gives
$t\in[t_-,t_+]$ with $1<t_-\le t_+<\infty$ depending only on $I$.
Set $c=at$ and enlarge $A_I\ge4$ so that $c\ge c_*$ and the uniform estimates
of Theorem 8.4 apply. For this actual law the identities (2.3) give

$$
\mathbb E_xK=a,\qquad \mathbb E_xU_T=s,\qquad aU_T\ge K^2.
\tag{10.10}
$$

The residual identity (8.11), with $\mathcal D(x)\ge0$, gives

$$
0\le\frac{\mathbb E_xW_{at}(K,aU_T)}{a^2}
\le H(x)-G_{at}(a,s).
\tag{10.11}
$$

Theorem 8.4 and (8.15) have the same uniform leading term and the same
$a^{-1/2}$ correction. Consequently, for some finite $B_I$ depending
only on $I$,

$$
0\le M(a,h)-G_{at}(a,s)\le B_Ia^2.
\tag{10.12}
$$

The first inequality follows because $G_{at}$ bounds every original law
from below, and hence bounds their infimum; it does not require a
minimizing law. Combining (10.1), (10.11) and (10.12), and writing
$\eta=\epsilon+a^{-1}$ and $D_I=\max\{1,B_I\}$, yields

$$
\frac{\mathbb E_xW_{at}(K,aU_T)}{a^5}
\le\epsilon+\frac{B_I}{a}\le D_I\eta.
\tag{10.13}
$$

By (10.5), (10.6), and the fact that $K$ is a positive integer, the stronger
pointwise estimate on all realized types is

$$
\begin{aligned}
W_{at}(K,aU_T)\ge{}&
\left(aU_T-\frac{b(at)}2\right)^2\mathbf1_{\{K=1\}}\\
&+\frac12(at)^3(K-at)^2\mathbf1_{\{K\ge2\}}.
\end{aligned}
\tag{10.14}
$$

After division by $a^5$ and expectation, (10.13) gives

$$
S:=\mathbb E_x\left[\left(\frac Ka-t\right)^2
                       \mathbf1_{\{K\ge2\}}\right]
\le\frac{2D_I}{t^3}\eta\le2D_I\eta
\tag{10.15}
$$

and

$$
\mathbb E_x\left[\left(\frac{U_T}{a^{3/2}}-
                         \frac{b(at)}{2a^{5/2}}\right)^2
                       \mathbf1_{\{K=1\}}\right]
\le D_I\eta.
\tag{10.16}
$$

Formula (8.14), uniformly for $t\in[t_-,t_+]$, implies

$$
\frac{b(at)}{2a^{5/2}}
=2t^{5/2}-\frac{t^2}{\sqrt a}+O_I(a^{-1}),
\qquad
\left|\frac{b(at)}{2a^{5/2}}-2t^{5/2}\right|^2
\le\frac{E_I}{a}
\tag{10.17}
$$

for a finite $E_I$. Applying $(u+v)^2\le2u^2+2v^2$ to (10.16) and
(10.17) proves (10.4) with constant $2D_I+2E_I$.

It remains to determine the singleton mass from the same exact mean, rather
than from a putative mixture. Write $q=\mathbb P_x(K=1)$, $p=1-q$, and

$$
e=\mathbb E_x\left[\left(\frac Ka-t\right)
                       \mathbf1_{\{K\ge2\}}\right].
$$

Cauchy--Schwarz gives $|e|\le\sqrt{pS}\le\sqrt S$. Equation (10.10) gives
$1=q/a+tp+e$, whence

$$
\left|q-\left(1-\frac1t\right)\right|
=\left|\frac{q}{at}+\frac et\right|
\le\frac1{at}+\frac{\sqrt S}{t}
\le\bigl(1+\sqrt{2D_I}\bigr)\sqrt\eta.
\tag{10.18}
$$

Here $t>1$, $q\le1$, and $a^{-1}\le\sqrt\eta$ were used. Enlarging a
single $C_I$ to cover (10.15), (10.17)--(10.18) proves all three assertions.
Every expectation is finite for each law because $[s]$ is finite and each
actual marginal is positive. No constant in this argument depends on the
least marginal, the positive-mass types, or their incidence components. ∎

**Corollary 10.2 (Sequential two-point limit and singleton concentration).**
Let $a_n\to\infty$, $h_n\ge1$ be integers with $a_n\ge4$ and
$\rho_n=h_n/a_n^{3/2}\to\rho\in(0,\infty)$. Let
$\epsilon_n\in[0,1]$ tend to zero, and let $x_n\in\mathcal X(a_n,h_n)$
satisfy

$$
H(x_n)\le M(a_n,h_n)+\epsilon_n a_n^3.
$$

With $K_n,U_n$ computed from the actual law $x_n$ and its actual marginals,
and $t=t(\rho)$, one has

$$
\frac{K_n}{a_n}\ \Rightarrow
\left(1-\frac1t\right)\delta_0+\frac1t\delta_t,
\qquad
\mathbb P_{x_n}(K_n=1)\longrightarrow1-\frac1t.
\tag{10.19}
$$

Moreover,

$$
\mathbb E_{x_n}\left[\left(\frac{U_n}{a_n^{3/2}}-2t^{5/2}\right)^2
                       \mathbf1_{\{K_n=1\}}\right]\longrightarrow0,
\tag{10.20}
$$

and, since $1-1/t>0$, also

$$
\mathbb E_{x_n}\left[\left(\frac{U_n}{a_n^{3/2}}-2t^{5/2}\right)^2
                       \,\middle|\, K_n=1\right]\longrightarrow0.
\tag{10.21}
$$

**Proof.** Choose a fixed compact $I\subset(0,\infty)$ containing $\rho_n$
eventually. Continuity in Definition 8.3 gives $t_n=t(\rho_n)\to t$.
Theorem 10.1 gives $q_n=\mathbb P_{x_n}(K_n=1)\to1-1/t$ and

$$
\mathbb E_{x_n}\left[\left(\frac{K_n}{a_n}-t\right)^2
                       \mathbf1_{\{K_n\ge2\}}\right]\longrightarrow0,
\tag{10.22}
$$

using $(u+v)^2\le2u^2+2v^2$ and $t_n\to t$ in (10.2). For a bounded
continuous function $f$, the singleton contribution is
$q_nf(1/a_n)\to(1-1/t)f(0)$. On $K_n\ge2$, (10.22) implies that the
mass outside any fixed neighborhood of $t$ tends to zero. Continuity at
$t$, boundedness of $f$, and $1-q_n\to1/t$ therefore give

$$
\mathbb E_{x_n}\left[f(K_n/a_n)\mathbf1_{\{K_n\ge2\}}\right]
\longrightarrow\frac1t f(t).
$$

This proves weak convergence in (10.19), in addition to the separately
proved singleton-event mass convergence. Applying the same square
inequality to (10.4) and $2t_n^{5/2}\to2t^{5/2}$ proves (10.20).
Division by $q_n$, which is eventually bounded away from zero, proves
(10.21). ∎

Theorem 10.1 is a repo-derived quantitative consequence of the actual-law
certificate (8.8)--(8.15) and the value estimate in Theorem 8.4; those value
and residual statements are reused here. The conclusion concerns only the
three observables displayed in (10.2)--(10.4) on a fixed compact positive
transition interval. It supplies neither a partition of the labels nor a
total-variation reconstruction of the full subset law, and does not assert
finite exact equality, infimum attainment or a graph realization. It does
not cover intervals approaching $0$ or $\infty$, other scales, or the
remaining classification questions in Open problem 8.6. No external
priority assertion is attached to these deductions.

## 追加锚（本行以下为增补区）

## 11. Prescribed finite budgets at the transition scale

Write $W(G)=2NE(G)$ for the graph energy in Definition 9.1 and
$Q(G)=H(x_G)$ for the quadratic energy of its actual neighborhood law in
Lemma 9.2. All constants in this section may depend on a fixed compact
interval $I=[\rho_-,\rho_+]\subset(0,\infty)$, and on no other parameters.

**Theorem 11.1 (Prescribed-budget transition realization).** There are
finite positive constants $A,D,C$, depending only on $I$, such that the
following holds for every integer $a\ge A$, every integer $h\ge1$ with
$\rho_a=h/a^{3/2}\in I$, and every integer $N\ge\lceil Da^6\rceil$.
Put $s=a+1+h$, $t=t(\rho_a)$ as in Definition 8.3, and

$$
j=\lfloor a(t-1)\rfloor,\quad m=a+j,\quad n=s-m=h+1-j,
\quad \alpha=\frac{a-1}{m-1},\quad p=\frac{j}{m-1}=1-\alpha.
\tag{11.1}
$$

Then $1\le j\le h$, and there exists
$G_N\in\mathfrak G_N(a,h)$ such that

$$
\left|Q(G_N)-H_j(a,h)\right|
\le C\frac{a^{15/2}}N,
\qquad
H_j(a,h)=\frac{m^3}{\alpha}+\frac{n^2}{p}.
\tag{11.2}
$$

Here $H_j$ is exactly the actual-law energy (8.3). The graph has exactly
$N$ sources and $aN$ edges; there is no divisibility condition on $N$.

**Proof.** By Definition 8.3, $t\in[1+\delta,T]$ for some
$\delta>0$ and $T<\infty$ depending only on $I$. The parameter estimates
in the upper-bound proof of Theorem 8.4 show, after increasing $A$, that
$1\le j\le h$. They also allow a constant $K\ge4$, depending only on $I$,
such that throughout the domain

$$
\begin{gathered}
K^{-1}\le\alpha,p\le1-K^{-1},\qquad
 a\le m\le Ka,\qquad
 K^{-1}a^{3/2}\le n\le Ka^{3/2},\qquad
 s\le Ka^{3/2}.
\end{gathered}
\tag{11.3}
$$

Indeed $m/a=t+O_I(a^{-1})$,
$p=(t-1)/t+O_I(a^{-1})$, $\alpha=1/t+O_I(a^{-1})$, and
$n/a^{3/2}=\rho_a+O_I(a^{-1/2})$; the displayed limiting quantities
range in compact positive intervals, with $p,\alpha$ bounded away from
one. Fix such $K,A$, and take $D\ge64K^6$.

Partition the $s$ sink labels into a core of size $m$ and a tail of size
$n$. Reserve one source whose neighborhood is all $s$ sink labels. To
choose the other neighborhoods, use integer division:

$$
R=(a-1)N-(s-1),\qquad
q=\left\lfloor\frac{R}{m-1}\right\rfloor,\qquad
r=R-q(m-1),\qquad 0\le r\le m-2,
\tag{11.4}
$$

and put $e=\mathbf1_{\{r>0\}}$ and $L=N-1-q-e$.
Since $m-1\ge a$, (11.3) gives

$$
|q-\alpha N|\le\frac{s-1}{m-1}+1\le2K\sqrt a,
\qquad |L-pN|\le4K\sqrt a.
\tag{11.5}
$$

Our lower bound on $N$ implies $N\ge16K^2\sqrt a$, so (11.5) implies
$q\ge\alpha N/2>0$ and $L\ge pN/2>0$. In particular all source counts
below are nonnegative integers, and their sum is $N$.

Use $q$ sources with the entire core as neighborhood. If $r>0$, use one
additional source with any $r+1$ distinct core neighbors; this is feasible
because $2\le r+1\le m-1$. Use the remaining $L$ sources as singletons
on the tail. Distribute them as evenly as possible: for tail label $i$,
choose an integer $\ell_i\in\{\lfloor L/n\rfloor,\lceil L/n\rceil\}$
with $\sum_{i\in\mathrm{tail}}\ell_i=L$, and give precisely $\ell_i$
sources the neighborhood $\{i\}$. Such integers exist by the remainder
of the integer division of $L$ by $n$.

The edge count is exactly

$$
\begin{aligned}
s+qm+e(r+1)+L
 &=s+N-1+q(m-1)+r\\
 &=s+N-1+R=aN.
\end{aligned}
\tag{11.6}
$$

All neighborhoods consist of distinct sink labels, so this is a simple
bipartite graph even though distinct sources may have equal neighborhoods.
The reserved source connects every sink, and every other source has a
nonempty neighborhood; hence the graph is connected.

For core label $i$, let $\delta_i\in\{0,1\}$ indicate incidence with the
additional source, setting every $\delta_i=0$ when $r=0$. The actual sink
degrees and actual marginals are

$$
\begin{array}{lll}
d_i=q+1+\delta_i,& y_i=(q+1+\delta_i)/N,& i\in\mathrm{core},\\
d_i=\ell_i+1,& y_i=(\ell_i+1)/N,& i\in\mathrm{tail}.
\end{array}
\tag{11.7}
$$

Every core degree is at least $N/(2K)$, and every tail degree is at least
$L/n\ge N/(2Kn)$. Thus every sink degree is at least $N/(2Kn)>s$:
indeed $2Kns\le2K^3a^3<N$ by the choice of $D$. Every source degree
is at most $s$. Consequently the strict orientation condition (9.1)
holds for every edge, and the constructed graph belongs to
$\mathfrak G_N(a,h)$.

It remains to control its actual quadratic energy, including the reserved
source. Equations (11.5)--(11.7) give

$$
\begin{aligned}
|q/N-\alpha|&\le2K\sqrt a/N,\\
|y_i-\alpha|&\le4K\sqrt a/N,
 & y_i&\ge\alpha/2 &&(i\in\mathrm{core}),\\
|y_i-p/n|&\le6K^2/N,
 & y_i&\ge p/(2n) &&(i\in\mathrm{tail}).
\end{aligned}
\tag{11.8}
$$

For the tail error, explicitly,
$|\ell_i+1-pN/n|\le2+4K\sqrt a/n\le6K^2$, using (11.3).
All these are estimates on the marginals in (11.7), rather than on
separately chosen marginal data.

Let $C_K$ denote finite constants depending only on $K$. The contribution
of the $q$ full-core sources is

$$
Q_C=\frac qN m^2\sum_{i\in\mathrm{core}}y_i^{-2},
\qquad
\left|Q_C-\frac{m^3}{\alpha}\right|
\le C_K\frac{a^{7/2}}N.
\tag{11.9}
$$

For completeness, for each core label the difference of the coefficients
is bounded by

$$
\left|\frac{q/N}{y_i^2}-\frac1\alpha\right|
\le \frac{|q/N-\alpha|}{y_i^2}
 +\alpha\left|y_i^{-2}-\alpha^{-2}\right|
\le C_K\frac{\sqrt a}{N}.
$$

The last step follows either by factoring the difference of squares or by
the derivative of $z^{-2}$ on $z\ge1/(2K)$. Summing over $m$ labels and
multiplying by $m^2\le K^2a^2$ proves (11.9).

The $L$ singleton sources contribute

$$
Q_D=\sum_{i\in\mathrm{tail}}\frac{\ell_i/N}{y_i^2}
=\sum_{i\in\mathrm{tail}}\left(\frac1{y_i}-\frac1{Ny_i^2}\right).
\tag{11.10}
$$

By (11.8), for each tail label,

$$
\left|\frac1{y_i}-\frac np\right|
\le\frac{|y_i-p/n|}{y_i(p/n)}\le C_K\frac{n^2}{N},
\qquad \frac1{Ny_i^2}\le C_K\frac{n^2}{N}.
$$

Therefore

$$
\left|Q_D-\frac{n^2}p\right|
\le C_K\frac{n^3}{N}\le C_K\frac{a^{9/2}}N.
\tag{11.11}
$$

The additional source, when present, has at most $m$ core neighbors, so
its contribution $Q_R$ satisfies

$$
0\le Q_R\le C_K\frac{m^3}{N}\le C_K\frac{a^3}{N}.
\tag{11.12}
$$

Finally the reserved source has degree $s$ and meets all labels. Its
contribution is bounded, using both lower bounds in (11.8), by

$$
\begin{aligned}
0\le Q_*&=\frac{s^2}N\sum_{i=1}^s y_i^{-2}\\
&\le C_K\frac{s^2}N(m+n^3)
\le C_K\frac{a^{15/2}}N.
\end{aligned}
\tag{11.13}
$$

The identity $Q(G_N)=Q_C+Q_D+Q_R+Q_*$ and (11.9)--(11.13) prove
(11.2), after enlarging one constant. This construction works separately
for every integer $N$ in the stated range. ∎

**Theorem 11.2 (Transition graph value and stability for all comparison
graphs).** For every fixed $I=[\rho_-,\rho_+]\subset(0,\infty)$ there
exist finite positive constants $A,C,D$, depending only on $I$, such that
for every integer $a\ge A$, every integer $h\ge1$ with
$\rho_a=h/a^{3/2}\in I$, and every integer $N\ge\lceil Da^6\rceil$,
$\mathfrak G_N(a,h)$ is nonempty, its infimum $V_N(a,h)$ is a minimum,
and, with $t=t(\rho_a)$,

$$
\left|\frac{V_N(a,h)}{a^3}-F(\rho_a)
               +\frac{2\rho_a t}{\sqrt a}\right|\le\frac Ca.
\tag{11.14}
$$

Furthermore, for every $G\in\mathfrak G_N(a,h)$ and every
$\epsilon\in[0,1]$ satisfying

$$
W(G)\le V_N(a,h)+\epsilon a^3,
\tag{11.15}
$$

choose a source $u$ uniformly from its $N$ actual sources, and put
$K=k_u$, $y_i=d_i/N$, $U_u=\sum_{i\in N_G(u)}y_i^{-1}$. Then
simultaneously

$$
\mathbb E\left[\left(\frac Ka-t\right)^2
                      \mathbf1_{\{K\ge2\}}\right]
\le C\left(\epsilon+\frac1a\right),
\tag{11.16}
$$

$$
\left|\mathbb P(K=1)-\left(1-\frac1t\right)\right|
\le C\sqrt{\epsilon+\frac1a},
\tag{11.17}
$$

$$
\mathbb E\left[\left(\frac{U_u}{a^{3/2}}-2t^{5/2}\right)^2
                      \mathbf1_{\{K=1\}}\right]
\le C\left(\epsilon+\frac1a\right).
\tag{11.18}
$$

The expectations, marginals, mean and energy in these assertions all
belong to the same actual graph $G$. The comparison class has exactly the
conditions of Definition 9.1; it has no extra marginal floor, symmetry,
cardinality-support restriction or attainment assumption for the law
infimum $M(a,h)$.

**Proof.** Use Theorem 11.1 and Theorem 8.4 on the same compact interval,
increasing $A,D$ when necessary. Their constants are uniform in the
integer parameters. In the notation (11.1), the upper-bound calculation
(8.16)--(8.17) gives

$$
\frac{H_j(a,h)}{a^3}
=F(\rho_a)-\frac{2\rho_a t}{\sqrt a}+O_I(a^{-1}),
\qquad 0\le H_j(a,h)-M(a,h)\le C_Ia^2.
\tag{11.19}
$$

The second inequality uses both the admissibility of that exact law and
the full-law value estimate (8.6). By (9.5) and (11.2),

$$
V_N(a,h)\le W(G_N)\le Q(G_N)
\le H_j(a,h)+C_I\frac{a^{15/2}}N.
\tag{11.20}
$$

In particular the graph class is nonempty. The finite number of labelled
simple graphs on the two fixed sides implies attainment of $V_N$.

We next give a lower bound on the entire graph class. Put
$\gamma=2/(\sqrt2+1)>0$. For every actual edge ratio $0\le z<1$,

$$
2(\sqrt{1+z^2}-1)
=\frac{2z^2}{\sqrt{1+z^2}+1}\ge\gamma z^2.
$$

Thus $W(G)\ge\gamma Q(G)$ for every comparison graph. Also, (9.5) and
$\sum_e z_e^4\le(\sum_e z_e^2)^2$ give

$$
0\le Q(G)-W(G)\le\frac{Q(G)^2}{4N}.
\tag{11.21}
$$

Choose $B_I\ge1$ so large that, for all parameters in the domain,
$M(a,h)\le H_j(a,h)\le B_Ia^3$ and the right side of (11.20) is at most
$B_Ia^3$. Such a constant exists by (11.19), compactness of $I$, and
$a^{15/2}/N\le a^{3/2}/D\le a^3/D$.
If $W(G)\ge B_Ia^3$, then $W(G)\ge M(a,h)$. Otherwise
$Q(G)\le B_Ia^3/\gamma$, and (11.21) and Lemma 9.2 give

$$
W(G)\ge Q(G)-\frac{B_I^2a^6}{4\gamma^2N}
\ge M(a,h)-C_I\frac{a^6}{N}.
$$

This proves, on the full class and hence for its minimum,

$$
M(a,h)-C_I\frac{a^6}{N}
\le V_N(a,h)
\le H_j(a,h)+C_I\frac{a^{15/2}}N.
\tag{11.22}
$$

Combining (11.22), (11.19) and (8.6), before absorbing the budget errors,
one obtains

$$
\left|\frac{V_N(a,h)}{a^3}-F(\rho_a)
                +\frac{2\rho_a t}{\sqrt a}\right|
\le C_I\left(\frac1a+\frac{a^{9/2}}N\right).
\tag{11.23}
$$

Here $a^3/N\le a^{9/2}/N$ also absorbs the lower-bound error. Since
$N\ge Da^6$, (11.23) implies (11.14). Neither the energy sublevel
argument nor its complementary high-energy case used any construction
property as a hypothesis on comparison graphs.

Now let $G$ satisfy (11.15). Equations (11.20) and (11.19) show
$W(G)\le(B_I+1)a^3$. Consequently $Q(G)\le(B_I+1)a^3/\gamma$, and
(11.21), followed by (11.20), gives for its actual law $x_G$

$$
\begin{aligned}
H(x_G)=Q(G)
&\le W(G)+C_Ia^6/N\\
&\le M(a,h)+\epsilon a^3
       +C_I\left(a^2+\frac{a^{15/2}}N+\frac{a^6}N\right)\\
&\le M(a,h)+\epsilon a^3+C_Ia^2.
\end{aligned}
\tag{11.24}
$$

The last line uses the stated budget. This is a same-law estimate:
Lemma 9.2 identifies $x_G$, $y_i=d_i/N$, $K=k_u$ and $U_u$ and gives
$\mathbb E K=a$ and $\mathbb E U_u=s$ exactly.

Apply the residual argument already proved in Theorem 10.1. In its
notation, (10.11)--(10.12) and (11.24) give

$$
0\le\frac{\mathbb E W_{at}(K,aU_u)}{a^5}
\le\epsilon+\frac{C_I}{a}
\le C'_I\left(\epsilon+\frac1a\right).
\tag{11.25}
$$

The implication from the residual bound (10.13) to (10.2)--(10.4), proved
in (10.14)--(10.18), applies directly to (11.25), with
$\eta=\epsilon+a^{-1}$. Those steps use only this bound, the exact mean
of this law, and the uniform singleton-contact estimate (10.17).
In particular they impose no upper bound on the coefficient multiplying
$\eta$; there is no need to insert $\epsilon+C_I/a$ as a parameter in
$[0,1]$ into the statement of Theorem 10.1. They give precisely
(11.16)--(11.18), after increasing one common $C$. Thus the three rates
are applications of the established actual-law stability estimates to
the actual graph law. ∎

The new realization estimate (11.2) supplies the prescribed-budget bridge
in the transition part of Open problem 8.6(4). The value and stability
conclusions reuse the full-law value and first correction of Theorem 8.4,
the same-law graph identity and quadratic bridge of Lemma 9.2, and the
three-observable remainder estimates proved in Theorem 10.1. The balanced
integer allocation and the single remainder source above are elementary
incidence constructions. No fixed-$s$ graph limit or square-root-regime
realization estimate is needed for this joint-growth conclusion.

The CDSO normalization remains the one cited in Section 7 from
Albalahi--Das--Ali--Barman--Hamza, DOI
[10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176), p.109.
The weak-duality input is only the expectation of the pointwise
certificate already proved in Section 8, with the Bertsimas--Popescu
source and its scope specified there. These deductions carry no global
priority claim. Their relation to the full results of Zhao--Zhao, DOI
[10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26),
and Smirnov, DOI
[10.47443/dml.2026.164](https://doi.org/10.47443/dml.2026.164), remains
undetermined; neither article is a premise here.

The constants are uniform only for $\rho_a$ in a fixed compact positive
interval. The budget $Da^6$ is sufficient; no least exponent or coefficient
is asserted. These results do not determine finite exact values or
extremizers, reconstruct the complete neighborhood law, classify its
label partition, or settle the other scales in Open problem 8.6.

## 追加锚（本行以下为增补区）

## 12. Exact laws throughout the first fixed-width square-root strip

**Definition 12.1 (The strip and the scalar comparison).** Fix $W>0$. The
parameters in this section are integers

$$
a\ge4,\qquad h\ge1,\qquad |h^2-2a|\le W,\qquad r=a+1.
\tag{12.1}
$$

The domain $\mathcal X(a,h)$, the actual positive marginals, $H$, $M(a,h)$
and $B_0=ar^2$ are exactly those of Definition 1.1. In particular every
nonempty subset of $[r+h]$ remains an allowed type, type masses may be zero,
and there is no connectedness condition. Write $d=H-B_0$. Use the function
$\Phi_{a,h}$ of [Incidence Definition 13.2](CDSO_INCIDENCE_MOMENTS_AND_CAPACITY_PHASES.md),
which is also the function in (5.4), and put

$$
\begin{aligned}
m_{a,h}&=\min_{0<u\le1/a}\Phi_{a,h}(u),\\
S_{a,h}&=\Phi_{a,h}(1/a)
       =\frac{ar^3}{a-1}+ah^2,\\
\Gamma_a&=\frac{2a^3+2a^2+2a+1}{(a-1)^2},\qquad
P_{a,h}=a^2\max\{h^2-\Gamma_a,0\}.
\end{aligned}
\tag{12.2}
$$

Proposition 5.2 proves existence and uniqueness of the scalar minimizer;
denote it by $u_{a,h}$. Its statement concerns the specified actual family
$\mathcal S(a,h)$, and does not supply a lower bound for other laws. The
cap law in Definition 5.1 is an actual law also when its missing-one masses
vanish. Every $O_W(\cdot)$ below is uniform over all pairs in (12.1), all
laws on the indicated sublevel and all label choices. Thresholds depend
only on $W$.

The normalization inherited from Definition 1.1 uses the CDSO definition
in A. M. Albalahi, S. Das, A. Ali, J. Barman and A. E. Hamza, *On the
hyperbolic Sombor index and its counterpart*, Discrete Math. Lett. 16
(2025), 108–115, DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176),
p.109: the denominator is the maximum endpoint degree and the factor
$1/\sqrt2$ is omitted. Its graph extremal assertions are not hypotheses
of the actual-law problem here.

**Lemma 12.2 (A uniformly separated core on the cap sublevel).** For every
fixed $W>0$ there are $A_W,b_0,c_0>0$ such that all pairs (12.1) with
$a\ge A_W$ and all $x\in\mathcal X(a,h)$ satisfying

$$
H(x)\le S_{a,h}
\tag{12.3}
$$

have exactly $r$ marginals at least $b_0/a$. Each of these is at least
$c_0$, and the other $h$ marginals are less than $b_0/a$. These define a
unique partition $[r+h]=C\mathbin{\dot\cup}D$, with $|C|=r$ and $|D|=h$,
into the largest and smallest marginals. Moreover

$$
S_{a,h}-B_0=2\sqrt2\,h a^{3/2}+O_W(a).
\tag{12.4}
$$

**Proof.** Write $\zeta=h^2-2a$, so $|\zeta|\le W$. The exact cap value
in (12.2) gives

$$
S_{a,h}-B_0
=\frac{2ar^2}{a-1}+ah^2
=4a^2+(\zeta+6)a+8+\frac8{a-1}.
\tag{12.5}
$$

Taylor's formula for $\sqrt{1+\zeta/(2a)}$, with a remainder bounded
uniformly for $|\zeta|\le W$ and sufficiently large $a$, gives

$$
2\sqrt2\,h a^{3/2}
=4a^2\sqrt{1+\frac{\zeta}{2a}}
=4a^2+\zeta a+O_W(1).
$$

This proves (12.4). In particular, taking $C_*=10$ and sufficiently large $a$ depending only
on $W$, (12.3) implies $H\le a^3+C_*a^2$ and
$1\le h/\sqrt a\le2$.

Apply Lemma 7.1 with $(C,L,R)=(C_*,1,2)$. Use its partition, constructed
in its proof by the threshold $b_0/a$, where $b_0=4C_*$. That proof gives
the uniform floor $c_0=(8C_*+1)^{-1}$ on the threshold core. If its core
has $a+j$ labels, its tail has $n=h+1-j$ labels, and with
$v=a\mathbb P(T\text{ meets that tail})$ one has

$$
1\le j\le4C_*,\qquad v\ge\frac1{8C_*},\qquad
\frac d{a^2}\ge\frac{(h+1-j)^2}{av}+2v+2j-2-O_W(a^{-1/2}).
\tag{12.6}
$$

All of these are within the compact positive-ratio hypotheses of that
lemma. In particular $n>0$ eventually. Arithmetic–geometric mean on the
first two terms of its last bound gives

$$
\frac d{a^2}
\ge\frac{2\sqrt2 h}{\sqrt a}+2j-2-O_W(a^{-1/2}),
$$

because $j$ is uniformly bounded and $n=h+1-j$. Equations (12.3)–(12.4)
give the opposite upper bound $d/a^2\le2\sqrt2 h/\sqrt a+O_W(a^{-1})$.
The integer $j$ must therefore equal one once $a$ is sufficiently large.
Thus the threshold core has $r$ labels and its complement has $h$.
Increasing the threshold so that $b_0/a<c_0$ proves the strict gap and
uniqueness of the partition. ∎

**Lemma 12.3 (Uniform marginal control and retained payment).** On the
sublevel of Lemma 12.2 define, from its one actual law,

$$
\begin{gathered}
t_j=y_j\ (j\in D),\quad u=\sum_{j\in D}t_j,\quad
\delta=\max_{j\in D}t_j,\quad c=\min_{i\in C}y_i,\\
B=|T\cap D|,\quad L=|T\cap C|,\quad K=L+B,\quad
A=\{B>0\},\quad e=\mathbb E[(K-1);A],\\
\alpha=a(a+1)(2a+1),\quad \beta=3a^2+3a+1,\quad
\Lambda=\frac3{\delta^2}-\frac{\max\{\alpha,\beta\}}{c^2}.
\end{gathered}
\tag{12.7}
$$

Uniformly on that entire sublevel, for sufficiently large $a$,

$$
\begin{aligned}
\mathbb P(A,K\ge2)&=O_W(a^{-2}),\\
c&\ge1-O_W(a^{-1/2}),\\
\delta&\le\frac{1+O_W(a^{-1/4})}{\sqrt2\,a^{3/2}},\\
\Lambda&\ge a^3.
\end{aligned}
\tag{12.8}
$$

**Proof.** Lemma 12.2 gives $t_j<b_0/a$, $u\le b_0h/a=O_W(a^{-1/2})$,
and every core marginal is at least $\delta\ge u/h$. Put

$$
\begin{aligned}
Q(l)&=(r-l)(a-l)(2a+1+l)=\alpha-\beta l+l^3,\\
\mathcal A_a(u)&=\frac{r^2(a^2+3a+1+au)}{(a-u)^2},\\
f_u(y)&=\frac{a^2}{y}-\frac{(2a+1)u}{y^2},\qquad
\bar y=\frac{a-u}{r},\\
\mathcal S_f&=\sum_{i\in C}f_u(y_i)-r f_u(\bar y),\\
H_D&=\mathbb E\!\left[K^2\sum_{j\in T\cap D}t_j^{-2}\right].
\end{aligned}
\tag{12.9}
$$

The polynomial is nonnegative for every integer $0\le l\le r$. The
algebraic certificate of Incidence Lemma 13.4, valid whenever
$a^2\ge3h(2a+1)$, reads

$$
d\ge H_D-u\mathcal A_a(u)+\mathbb E Q(L)+\mathcal S_f.
\tag{12.10}
$$

Its hypotheses hold uniformly in (12.1), since $h=O_W(\sqrt a)$. In fact
$a^2\ge6h(2a+1)$ eventually, and on $u/h\le y\le1$,

$$
f_u''(y)=\frac{2(a^2y-3(2a+1)u)}{y^4}\ge a^2.
$$

The actual $r$ core marginals have sum $a-u$, so strong Jensen yields

$$
\mathcal S_f\ge\frac{a^2}{2}\sum_{i\in C}(y_i-\bar y)^2\ge0.
\tag{12.11}
$$

Only the algebraic certificate is used from that fixed-$h$ section; no
fixed-$h$ limiting statement is applied to growing $h$.

The bound on $u$ gives $\mathcal A_a(u)=O_W(a^2)$. Thus

$$
\eta=\sqrt{\alpha-\mathcal A_a(u)}>0,\qquad
\eta=\sqrt2\,a^{3/2}+O_W(\sqrt a).
\tag{12.12}
$$

For a realized type in $A$ set

$$
V_T=\sum_{j\in T\cap D}t_j^{-1},\qquad
Z_T=K^2\sum_{j\in T\cap D}t_j^{-2},\qquad
F_T=Z_T+Q(L)-\mathcal A_a(u)B-2\eta V_T.
\tag{12.13}
$$

For a tail singleton $T=\{j\}$ the exact identity is
$F_T=(t_j^{-1}-\eta)^2$. There is also $\kappa>0$, independent of the law
and parameters after a threshold depending only on $W$, such that

$$
F_T\ge\kappa a^3\qquad\text{on }A\cap\{K\ge2\}.
\tag{12.14}
$$

Indeed, when $2\le K\le\sqrt a$, completing each square gives

$$
Z_T-2\eta V_T\ge-\frac{B\eta^2}{K^2}\ge-\frac{\eta^2}{2},
$$

and therefore

$$
F_T\ge\alpha-(\beta+\mathcal A_a(u))\sqrt a-\frac{\eta^2}{2}
\ge\frac{a^3}{2}
$$

eventually. If $K>\sqrt a$, every reciprocal $z=t_j^{-1}$ in the type
satisfies $z>a/b_0$. Hence $K^2z\ge a^2/b_0>4\eta$ for large $a$, so
$K^2z^2-2\eta z\ge K^2z^2/2$. It follows that

$$
F_T\ge\frac{Ba^3}{2b_0^2}-\mathcal A_a(u)B
\ge\frac{Ba^3}{4b_0^2},
$$

using $Q(L)\ge0$. This proves (12.14) with
$\kappa=\min\{1/2,1/(4b_0^2)\}$. These two ranges exhaust all actual
nonsingleton types; no relation among their incidences has been relaxed.

Since $\mathbb E V_T=h$ when $V_T$ is set to zero off $A$, and
$\mathbb E B=u$, (12.10) becomes

$$
d\ge2\eta h+\mathbb E[F_T;A]+\mathbb E[Q(L);A^c]+\mathcal S_f.
\tag{12.15}
$$

All three terms after $2\eta h$ are nonnegative. Equations
(12.3)–(12.4) and (12.12), with $h=O_W(\sqrt a)$, show that their sum is
$O_W(a)$. Thus (12.14) proves the first estimate in (12.8).
Equation (12.11) gives $\sum_{i\in C}(y_i-\bar y)^2=O_W(a^{-1})$.
Since $\bar y=1-O_W(a^{-1})$, this proves the estimate for $c$.

To control the largest tail marginal, put $q=\mathbb P(A,K\ge2)$ and
$x_j=x_{\{j\}}$. For every $j\in D$,

$$
0\le t_j-x_j\le q=O_W(a^{-2}),\qquad
\eta q=O_W(a^{-1/2}).
$$

If $t_j\ge1/\eta$, then $x_j\ge t_j/2$ eventually. Set $w=\eta t_j\ge1$.
The singleton square in (12.13) and the $O_W(a)$ bound in (12.15) give

$$
\frac\eta2\frac{(w-1)^2}{w}
\le x_j(t_j^{-1}-\eta)^2\le O_W(a),\qquad
\frac{(w-1)^2}{w}=O_W(a^{-1/2}).
$$

For $w\ge1$ this implies $w-1=O_W(a^{-1/4})$: writing $z=w-1\ge0$,
$z^2/(1+z)\le\epsilon$ implies $z\le\epsilon+\sqrt\epsilon$.
If $t_j<1/\eta$ the same upper bound is automatic. Taking the maximum
and using (12.12) proves the estimate for $\delta$. Finally,

$$
\frac3{\delta^2}\ge(6-o_W(1))a^3,\qquad
\frac{\max\{\alpha,\beta\}}{c^2}=(2+o_W(1))a^3.
$$

Their difference is at least $a^3$ for sufficiently large $a$, uniformly
over the whole comparison sublevel. ∎

**Lemma 12.4 (Finite cap payment on one actual law).** Let $a\ge4$ and
$h\ge1$ be integers, let $x\in\mathcal X(a,h)$, and choose any partition
$C\mathbin{\dot\cup}D=[a+1+h]$ with $|C|=a+1$ and $|D|=h$. Define
$u,\delta,c,B,L,A,e,\alpha,\beta,\Lambda$ by (12.7) and $P_{a,h},m_{a,h}$
by (12.2). If

$$
\Lambda>\frac{a+1}{a}P_{a,h},
\tag{12.16}
$$

then

$$
H(x)\ge m_{a,h}
 +\left(\Lambda-\frac{a+1}{a}P_{a,h}\right)e.
\tag{12.17}
$$

In particular equality with $m_{a,h}$ forces all tail-containing types
to be singletons and $u=u_{a,h}\le1/a$.

**Proof.** The following refinement retains the surplus in the strict
payment argument of Incidence Lemma 13.7:

$$
H(x)\ge\Phi_{a,h}(u)+\Lambda e.
\tag{12.18}
$$

Here $0<u<a$ follows from positivity of all tail and core marginals and
their common sum $a$. For completeness put $I_i=\mathbf1_{\{i\in T\}}$,
$c_a=a(2a+1)$ and

$$
\begin{gathered}
\rho_i=(1-I_i)(2a+1)(a-L)+I_i(r-L)(r-L-1),\\
R_i=\mathbb E\rho_i,\qquad
\Delta_i=\mathbb E[(K^2-L^2)I_i]\ge0,\\
Z=\mathbb E\!\left[(K^2-1)\sum_{j\in T\cap D}t_j^{-2}\right],\qquad
b_a=(a-1)(2a+1).
\end{gathered}
$$

Each $\rho_i\ge0$: when $I_i=0$, $L\le a$; when $I_i=1$, its last two
factors are consecutive integers with nonnegative product. Expanding
and using $\mathbb E L=a-u$ gives the exact identity from Incidence (13.20),
written with its nonnegative terms retained:

$$
H=\sum_{j\in D}\frac1{t_j}+Z
 +\sum_{i\in C}\left(\frac{a^2}{y_i}
 -\frac{(2a+1)u}{y_i^2}+\frac{R_i+\Delta_i}{y_i^2}\right).
\tag{12.19}
$$

On $A$, all deficits $c_aB-\rho_i$ are nonnegative. For $I_i=0$ they are
$(2a+1)[a(B-1)+L]$. For $I_i=1$ they are
$c_a(B-1)+a^2+(2a+1)L-L^2\ge0$, since $L\le a+1\le2a+1$.
Also $\sum_i\rho_i=Q(L)$, so on this same type

$$
\sum_{i\in C}(c_aB-\rho_i)
=\alpha(B-1)+\beta L-L^3
\le\max\{\alpha,\beta\}(K-1).
\tag{12.20}
$$

Only after establishing these signs may one bound each weight by $c^{-2}$.
Off $A$ the $\rho_i$ are nonnegative, and $\mathbb E B=u$, whence

$$
\sum_{i\in C}\frac{R_i-c_au}{y_i^2}
\ge-\frac{\max\{\alpha,\beta\}}{c^2}e.
$$

On $A$, the integrand of $Z$ is at least
$B(K^2-1)/\delta^2\ge3(K-1)/\delta^2$; it is zero off $A$.
Substituting into (12.19) and discarding only the nonnegative $\Delta_i$
proves

$$
H\ge\sum_{j\in D}\frac1{t_j}
 +\sum_{i\in C}\left(\frac{a^2}{y_i}+\frac{b_au}{y_i^2}\right)
 +\Lambda e.
\tag{12.21}
$$

Cauchy on the actual $h$ tail marginals and strict Jensen for
$g_u(y)=a^2/y+b_au/y^2$, on the actual $r$ core marginals of sum $a-u$,
give (12.18). No marginal has been independently prescribed.

The mean constraint provides the missing control of the cap. On $A^c$,
$L\le r$, and therefore

$$
a=\mathbb E K\le r\mathbb P(A^c)+\mathbb E[L+B;A].
$$

Rearrangement, with $u=\mathbb E B$, gives

$$
au-1\le r\mathbb E[B-1;A]+\mathbb E[L;A]\le r e.
\tag{12.22}
$$

The last inequality uses $K-1=(B-1)+L$ on $A$. Consequently
$(u-1/a)_+\le(r/a)e$, where $z_+=\max\{z,0\}$.

Strict convexity of $\Phi_{a,h}$ on $(0,a)$, and the exact cap derivative
$\Phi_{a,h}'(1/a)=a^2(\Gamma_a-h^2)$ from Proposition 5.2, imply for every
$0<u<a$ that

$$
\Phi_{a,h}(u)\ge m_{a,h}-P_{a,h}(u-1/a)_+.
\tag{12.23}
$$

Indeed, if that derivative is nonnegative, its unique unconstrained
minimizer is at or below the cap, so $P_{a,h}=0$ and the assertion is its
global minimum property. If the derivative is negative, $m_{a,h}$ is the
cap value. For $u\le1/a$ use the constrained minimum property; for
$u>1/a$ use the supporting tangent at the cap, whose slope is $-P_{a,h}$.
This proves (12.23) in all cases, including zero cap derivative.
Combining (12.18), (12.22) and (12.23) proves (12.17).
Under (12.16), equality forces $e=0$. Nonnegativity and integrality of
$K-1$ on $A$ then force $K=1$ on every positive-mass tail-containing type.
Equation (12.22) gives $u\le1/a$, and (12.18) and uniqueness of the scalar
minimum give $u=u_{a,h}$. ∎

**Theorem 12.5 (Unrestricted exact minimum and every equality law in the
strip).** For every fixed $W>0$ there is an integer $A_W\ge14$ such that
for every integer pair (12.1) with $a\ge A_W$,

$$
M(a,h)=\min_{0<u\le1/a}\Phi_{a,h}(u)=\Phi_{a,h}(u_{a,h}).
\tag{12.24}
$$

The infimum is attained. Up to arbitrary permutations of all $s=a+1+h$
labels, all equality laws, and only those laws, are

$$
\begin{gathered}
|C|=a+1,\qquad D=[s]\setminus C,\qquad |D|=h,\\
x_{\{j\}}=\frac{u_{a,h}}h\quad(j\in D),\qquad
x_C=(a-1)u_{a,h},\qquad
x_{C\setminus\{i\}}=\frac{1-au_{a,h}}{a+1}\quad(i\in C),\\
x_T=0\quad\text{for every other nonempty }T.
\end{gathered}
\tag{12.25}
$$

These are precisely the actual laws of Incidence Definition 13.2. The
scalar cap criterion of Proposition 5.2 is thus also the unrestricted
criterion in this strip. More explicitly, for these integer pairs,

$$
\begin{cases}
0<u_{a,h}<1/a,&h^2-2a\le6,\\
u_{a,h}=1/a,&h^2-2a\ge7.
\end{cases}
\tag{12.26}
$$

In the second case every missing-one mass in (12.25) is zero and the
exact value is $ar^3/(a-1)+ah^2$. All actual marginals remain positive.

**Proof.** Increase one threshold depending only on $W$ so that Lemmas
12.2–12.3 hold. Since

$$
\Gamma_a-2a=6+\frac{12a-5}{(a-1)^2}>0,
$$

(12.1) gives $0\le P_{a,h}\le Wa^2$. Hence on the entire sublevel
$H\le S_{a,h}$, Lemma 12.3 gives

$$
\Lambda\ge a^3>\frac ra Wa^2\ge\frac ra P_{a,h}
$$

after increasing that threshold again. Lemma 12.4 therefore proves
$H\ge m_{a,h}$ for every actual law in this sublevel. Every law above it
has $H>S_{a,h}\ge m_{a,h}$. Thus every original law is bounded below by
$m_{a,h}$, with no support or symmetry premise. Definition 5.1, equivalently
Incidence Definition 13.2, supplies a law with energy $m_{a,h}$, proving
(12.24) and attainment.

Suppose an arbitrary law attains this value. It lies on the cap sublevel,
so Lemma 12.4 forces $e=0$, only tail singletons, and $u=u_{a,h}\le1/a$.
In (12.21) the tail Cauchy remainder and the core Jensen remainder are
nonnegative and have sum zero. Hence

$$
t_j=\frac{u_{a,h}}h\quad(j\in D),\qquad
y_i=\frac{a-u_{a,h}}r\quad(i\in C).
\tag{12.27}
$$

For completeness, with only tail singletons, $Z=0$ and $\Delta_i=0$ in
(12.19), and $\rho_i=c_a$ on every tail singleton. The exact remaining
payment remainder is therefore

$$
H-\sum_{j\in D}t_j^{-1}-\sum_{i\in C}g_u(y_i)
=\sum_{i\in C}\frac{\mathbb E[\rho_i;A^c]}{y_i^2}.
\tag{12.28}
$$

It vanishes only if every $\rho_i$ vanishes on every positive-mass core-only
type. Their sum is $Q(L)$. On $A^c$, $T$ is nonempty and $1\le L\le r$;
the only integer zeros of $Q(L)$ are $a$ and $r$. Thus the only possible
remaining types are $C$ and the $r$ types $C\setminus\{i\}$.
Writing their masses as $z$ and $b_i$, normalization and the same mean give

$$
z+\sum_i b_i=1-u,\qquad rz+a\sum_i b_i=a-u,
$$

so $z=(a-1)u$ and $\sum_i b_i=1-au$. Equation (12.27) now gives
$1-u-b_i=(a-u)/r$, hence $b_i=(1-au)/r$ for every $i$. This proves
necessity of (12.25), including its zero-mass boundary. Conversely those
nonnegative masses sum to one, have mean $a$ and induce the positive
marginals in (12.27), by Definition 5.1. Their energy is $\Phi_{a,h}(u)$,
so every displayed relabeling attains (12.24).

Finally, for $a\ge14$,

$$
0<\frac{12a-5}{(a-1)^2}<1,
$$

because $(a-1)^2-(12a-5)=a^2-14a+6>0$. Thus
$2a+6<\Gamma_a<2a+7$. Since $h^2-2a$ is an integer, Proposition 5.2
gives exactly (12.26); there is no omitted equality case
$h^2=\Gamma_a$ in this range. At the cap the core marginal is $(a-1)/a$
and each tail marginal is $1/(ah)>0$, despite the vanished missing-one
masses. Every estimate above is uniform over (12.1), so the one threshold
covers every admissible integer pair, not merely a chosen sequence.

This is a repo-derived unrestricted comparison and equality classification.
The finite identities, scalar value and construction from Sections 5 and 7
and Incidence Section 13 are reused; the extra cap payment is (12.22)–(12.23)
combined with the uniform surplus in (12.8). The threshold $A_W$ is
existential; its least value, exceptional small parameters, strips of
unbounded width, other growing-surplus phases, and prescribed connected
graph realizations remain undetermined by this theorem. N. Smirnov,
*Bicyclic Graphs with Maximum Complementary Diminished Sombor Index*,
Discrete Math. Lett. 18 (2026), 100–106, DOI
[10.47443/dml.2026.164](https://doi.org/10.47443/dml.2026.164), Theorem 2.1,
concerns maxima on finite simple connected bicyclic graphs; it is not a
lower-bound premise for this actual-law minimum. The full text of K. Zhao
and X. Zhao, *Extremal values with respect to vertex-degree-based topological
indices in unicyclic and bicyclic graphs*, DOI
[10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26), is not
an input and its possible overlap is unassessed. No literature-priority
claim is attached to (12.24). ∎

## 追加锚（本行以下为增补区）

## 13. Uniform exact laws up to the second square-root boundary

**Definition 13.1 (The full first-phase range and a comparison law).** Fix
$0<R<2\sqrt2$ and put $R_*=\max\{1,R\}$. The domain, actual marginals,
energy and infimum are exactly $\mathcal X(a,h)$, $y_i$, $H$ and $M(a,h)$
of Definition 1.1, with integers $a\ge4$, $1\le h\le R\sqrt a$ and
$r=a+1$. Use $\Phi_{a,h}$, $u_{a,h}$, $m_{a,h}$, $\Gamma_a$ and
$P_{a,h}$ from (12.2) and Proposition 5.2, without imposing the
fixed-width hypothesis (12.1). Thus $u_{a,h}$ is the unique constrained
scalar minimizer, whose existence holds for every $a\ge4$, $h\ge1$.
For the compact part $\sqrt a\le h\le R_*\sqrt a$, set

$$
q=\frac h{\sqrt a},\qquad
v_0=\min\{q/\sqrt2,1\},\qquad u_0=\frac{v_0}a,
\qquad U_{a,h}=\Phi_{a,h}(u_0),
$$

$$
\psi(q)=
\begin{cases}
2\sqrt2\,q,&q\le\sqrt2,\\
q^2+2,&q\ge\sqrt2.
\end{cases}
\tag{13.1}
$$

Here $U_{a,h}$ is the energy of the actual law of Definition 5.1, not
an assumed description of an optimizing law. Uniformly for
$1\le q\le R_*$,

$$
U_{a,h}-B_0=a^2\psi(q)+O_R(a).
\tag{13.2}
$$

Indeed $1/\sqrt2\le v_0\le1$. In (5.4), substituting $u=v/a$ with
$1/\sqrt2\le v\le1$ gives the uniform expansion
$C_a(v/a)-B_0=2v a^2+O(a)$; the singleton contribution is exactly
$h^2/(v/a)=q^2a^2/v$. Every $O_R$ in this section has a constant and a
threshold depending only on $R$, independent of the law, integer pair
and label choices. Increasing such a threshold never restricts the
allowed types or the actual positive marginals.

**Lemma 13.2 (Uniformly separated core below the second boundary).** There
are constants $A_R,b,c_0>0$ such that every integer pair
$\sqrt a\le h\le R_*\sqrt a$, $a\ge A_R$, and every actual law satisfying

$$
H(x)\le U_{a,h}
\tag{13.3}
$$

has precisely $r$ marginals at least $b/a$, each at least $c_0$. All
other $h$ marginals are less than $b/a<c_0$. Thus these sets are uniquely
the largest and smallest actual marginals.

**Proof.** By (13.2) choose $C_0\ge1$, depending only on $R$, such that
(13.3) implies $H\le a^3+C_0a^2$. Apply Lemma 7.1 with
$(C,L,R)=(C_0,1,R_*)$. Its threshold construction uses
$b=4C_0$ and gives the floor $c_0=(8C_0+1)^{-1}$. If its threshold core
has $a+j$ labels, its complement has $n=h+1-j$ labels. The lemma gives

$$
1\le j\le4C_0,\qquad v>0,\qquad
\frac{H-B_0}{a^2}
\ge\frac{(h+1-j)^2}{av}+2v+2j-2-O_R(a^{-1/2}).
\tag{13.4}
$$

The integer $j$, the tail probability $v/a$ and the marginal partition
all come from the same law. In particular $n>0$ eventually, since
$h\ge\sqrt a$ and $j$ is bounded. Arithmetic--geometric mean gives

$$
\frac{H-B_0}{a^2}
\ge2\sqrt2\,q+2j-2-O_R(a^{-1/2}).
\tag{13.5}
$$

On the other hand,

$$
0\le\psi(q)-2\sqrt2\,q=(q-\sqrt2)_+^2
\le (R_*-\sqrt2)_+^2<2.
\tag{13.6}
$$

The strict gap between the last bound and $2$ depends only on $R$.
Equations (13.2)--(13.3) therefore exclude every $j\ge2$ once $a$ is
sufficiently large. Hence $j=1$, and the threshold core and tail have
sizes $r$ and $h$. Finally increase $A_R$ until $b/a<c_0$. This proves
both strict separation and uniqueness. Only the uniform compact-ratio
certificate of Lemma 7.1 is used; no fixed-$h$ or fixed-width limiting
statement is applied to varying parameters. ∎

**Lemma 13.3 (A cap-adjusted square certificate for every actual type).**
On the entire sublevel (13.3), let $C,D$ be the partition of Lemma 13.2
and define

$$
\begin{gathered}
t_j=y_j\ (j\in D),\quad u=\sum_{j\in D}t_j,\quad
\delta=\max_{j\in D}t_j,\quad c=\min_{i\in C}y_i,\\
B=|T\cap D|,\quad L=|T\cap C|,\quad K=L+B,\quad A=\{B>0\},\\
\alpha=a(a+1)(2a+1),\quad \beta=3a^2+3a+1,\quad
Q(l)=\alpha-\beta l+l^3,\\
\mathcal A=\mathcal A_a(u)
=\frac{r^2(a^2+3a+1+au)}{(a-u)^2},\qquad
\eta=\max\{\sqrt{\alpha-\mathcal A},ah\},\\
\gamma=\eta^2-\alpha+\mathcal A\ge0,\qquad
f_u(y)=\frac{a^2}{y}-\frac{(2a+1)u}{y^2},\qquad
\bar y=\frac{a-u}{r},\\
\mathcal S_f=\sum_{i\in C}f_u(y_i)-r f_u(\bar y).
\end{gathered}
\tag{13.7}
$$

For sufficiently large $a$, the square root is positive. On $A$ put

$$
V_T=\sum_{j\in T\cap D}t_j^{-1},\qquad
Z_T=K^2\sum_{j\in T\cap D}t_j^{-2},
$$

$$
G_T=Z_T+Q(L)-\mathcal A B-2\eta V_T+\gamma B
-\frac\gamma a\bigl(r(B-1)+L\bigr).
\tag{13.8}
$$

There is $\kappa_R>0$ such that, uniformly over all these laws,

$$
\begin{aligned}
G_{\{j\}}&=(t_j^{-1}-\eta)^2\quad(j\in D),\\
G_T&\ge\kappa_Ra^3\quad(B>0,\ K\ge2),\\
\mathcal S_f&\ge\frac{a^2}{2}\sum_{i\in C}(y_i-\bar y)^2,\\
H-B_0&\ge 2\eta h-\frac\gamma a
 +\mathbb E[G_T;A]+\mathbb E[Q(L);A^c]+\mathcal S_f.
\end{aligned}
\tag{13.9}
$$

**Proof.** Separation gives $t_j<b/a$, $u\le bh/a=O_R(a^{-1/2})$
and $y_i\ge u/h$ on $C$. In particular

$$
\mathcal A=a^2+O_R(a),\qquad
\alpha-\mathcal A=2a^3+O_R(a^2),\qquad
\eta=O_R(a^{3/2}),\quad \gamma=O_R(a^3).
\tag{13.10}
$$

These estimates follow directly from the rational expression in (13.7)
for $0\le u\le bR_*a^{-1/2}$, where $a-u\ge a/2$ eventually. In
particular $\alpha-\mathcal A\ge a^3$ eventually. The polynomial
$Q(l)=(r-l)(a-l)(2a+1+l)$ is nonnegative for every integer
$0\le l\le r$.

The finite certificate of Incidence Lemma 13.4, equivalently (12.10),
is applicable because $|C|=r$, $D$ consists of the $h$ smallest actual
marginals and $a^2\ge3h(2a+1)$ eventually. In fact the stronger condition
$a^2\ge6h(2a+1)$ holds uniformly for $h\le R_*\sqrt a$. It gives

$$
f_u''(y)=\frac{2(a^2y-3(2a+1)u)}{y^4}\ge a^2
\quad(u/h\le y\le1).
$$

Apply Jensen to $f_u(y)-a^2y^2/2$ at the actual $r$ core marginals, whose
sum is $a-u$. This gives the third assertion of (13.9) and the retained
form of that finite certificate,

$$
H-B_0\ge H_D-u\mathcal A+\mathbb E Q(L)+\mathcal S_f,
\qquad H_D=\mathbb E[Z_T;A].
\tag{13.11}
$$

This is only an algebraic use of Incidence Lemma 13.4, not an application
of its section's fixed-$h$ asymptotics.

The mean constraint supplies a pointwise-weighted cap correction.
Since $K=L\le r$ on $A^c$,

$$
a\le r\mathbb P(A^c)+\mathbb E[L+B;A],\qquad
au-1\le r\mathbb E[B-1;A]+\mathbb E[L;A].
\tag{13.12}
$$

The second inequality follows by rearranging the first and using
$u=\mathbb E B$; no bound on $u$ by $1/a$ has been assumed. Also
$\mathbb E[V_T;A]=h$, because each actual positive $t_j$ is the
probability of its own inclusion event. Substitute (13.8) into
(13.11) and use (13.12) with the nonnegative multiplier $\gamma/a$.
This proves the last line of (13.9).

It remains to prove the pointwise signs for every type, rather than for
a selected support. A tail singleton has $L=0$, $B=K=1$; its cap
correction in (13.8) is zero and
$Q(0)-\mathcal A+\gamma=\eta^2$. This proves its exact square identity.
For $K\ge2$, completing the square in each reciprocal gives
$K^2z^2-2\eta z\ge-\eta^2/K^2$. As

$$
\gamma B-\frac\gamma a\bigl(r(B-1)+L\bigr)
=\gamma\left(1-\frac{K-1}{a}\right),
$$

we obtain the finite lower bound

$$
G_T\ge\eta^2\left(1-\frac B{K^2}\right)
-\mathcal A(B-1)-\beta L+L^3-\frac\gamma a(K-1).
\tag{13.13}
$$

If $2\le K\le\sqrt a$, then $B/K^2\le1/2$ and $B,L\le\sqrt a$.
Equations (13.10) and (13.13) therefore give

$$
G_T\ge\frac{a^3}{2}-O_R(a^{5/2})\ge\frac{a^3}{4}
$$

for all sufficiently large $a$. If $K>\sqrt a$, each reciprocal
$z=t_j^{-1}$ is greater than $a/b$, so
$K^2z\ge a^2/b>4\eta$ eventually. Thus

$$
Z_T-2\eta V_T\ge\frac12 Z_T
\ge\frac{BK^2a^2}{2b^2},
$$

$$
G_T\ge\frac{BK^2a^2}{2b^2}-\mathcal A B
+\gamma\left(1-\frac{K-1}{a}\right),
\tag{13.14}
$$

where only $Q(L)\ge0$ has been discarded. For
$\sqrt a<K\le r=a+1$ the last term is nonnegative, and (13.14) is at
least $Ba^3/(4b^2)$ eventually. For $K>r$, the original domain still
has $K\le r+h$, so that last term is at least
$-\gamma h/a=-O_R(a^{5/2})$. In this case the first term is at least
$Ba^4/(2b^2)$, and hence (13.14) is again at least
$a^3/(4b^2)$ for all sufficiently large $a$, since $B\ge1$ and
$\mathcal A=O_R(a^2)$. These ranges exhaust every nonempty type meeting
$D$, including cardinalities larger than the core. One may therefore
choose $\kappa_R=\min\{1/4,1/(4b^2)\}$ after increasing the uniform
threshold. All incidences, reciprocals and cardinalities in the
argument belong to the original one law. ∎

**Lemma 13.4 (Uniform marginal control and strict cap payment).** On the
sublevel (13.3), with the notation above, uniformly

$$
\begin{aligned}
\mathbb P(A,K\ge2)&=O_R(a^{-2}),\\
c&\ge1-O_R(a^{-1/2}),\\
\delta&\le\frac{1+O_R(a^{-1/4})}{\eta},\qquad
\frac{\eta^2}{a^3}=\max\{2,q^2\}+O_R(a^{-1}),\\
\Lambda-\frac raP_{a,h}&\ge a^3>0,
\qquad \Lambda=\frac3{\delta^2}-\frac{\max\{\alpha,\beta\}}{c^2},
\end{aligned}
\tag{13.15}
$$

for sufficiently large $a$.

**Proof.** Put $t=\eta/a^{3/2}$ and
$w=(\alpha-\mathcal A)/a^3=2+O_R(a^{-1})$. Then
$t=\max\{\sqrt w,q\}$ and the baseline in (13.9) is exactly

$$
\frac{2\eta h-\gamma/a}{a^2}=2qt-t^2+w.
\tag{13.16}
$$

The right side is $2q\sqrt w$ if $q\le\sqrt w$, and $q^2+w$ otherwise.
The functions $\sqrt w$ and $\max\{\sqrt w,q\}$ are uniformly Lipschitz
in $w$ near $2$ for $1\le q\le R_*$. Consequently (13.16) equals
$\psi(q)+O_R(a^{-1})$, including when $q$ crosses $\sqrt2$. Comparing
(13.9) with (13.2)--(13.3) gives a constant $C_R$ such that

$$
0\le\mathbb E[G_T;A]+\mathbb E[Q(L);A^c]+\mathcal S_f\le C_Ra.
\tag{13.17}
$$

All summands are nonnegative by Lemma 13.3. Its nonsingleton lower
bound proves the first line of (13.15), and strong Jensen gives

$$
\sum_{i\in C}(y_i-\bar y)^2\le\frac{2C_R}{a}.
$$

Since $\bar y=(a-u)/r=1-O_R(a^{-1})$, this proves the asserted core
floor tending to one.

For each $j\in D$ write $x_j=x_{\{j\}}$ and
$p_2=\mathbb P(A,K\ge2)$. Actual inclusion probabilities give
$0\le t_j-x_j\le p_2$ and $\eta p_2=O_R(a^{-1/2})$. If
$t_j\ge1/\eta$, it follows that $x_j\ge t_j/2$ eventually. Setting
$z=\eta t_j\ge1$ and using its singleton square in (13.17) yields

$$
\frac\eta2\frac{(z-1)^2}{z}
\le x_j(t_j^{-1}-\eta)^2\le C_Ra,
\qquad \frac{(z-1)^2}{z}=O_R(a^{-1/2}).
$$

For $z\ge1$, the inequality $(z-1)^2/z\le\epsilon$ implies
$z-1\le\epsilon+\sqrt\epsilon$. Thus
$t_j\le(1+O_R(a^{-1/4}))/\eta$. The same bound is automatic when
$t_j<1/\eta$. Taking the maximum proves the bound on $\delta$;
(13.10) gives the stated uniform formula for $\eta^2/a^3$.

Finally $\max\{\alpha,\beta\}=(2+O(a^{-1}))a^3$. The core and tail
bounds imply

$$
\frac\Lambda{a^3}\ge3\max\{2,q^2\}-2-O_R(a^{-1/4}).
$$

The exact identity
$\Gamma_a=2a+6+(12a-5)/(a-1)^2>2a$ gives

$$
0\le\frac{P_{a,h}}{a^3}
=\left(q^2-\frac{\Gamma_a}{a}\right)_+
\le(q^2-2)_+.
$$

Since $r/a=1+1/a$ and $q\le R_*$,

$$
\frac{\Lambda-(r/a)P_{a,h}}{a^3}
\ge3\max\{2,q^2\}-2-(q^2-2)_+-O_R(a^{-1/4})
\ge4-O_R(a^{-1/4}).
$$

The middle expression before its error is $4$ for $q^2\le2$, and
$2q^2\ge4$ for $q^2\ge2$. Increasing one threshold proves the last
line of (13.15). In particular this estimate does not treat
$P_{a,h}$ as $O(a^2)$ in the capped phase. ∎

**Theorem 13.5 (The full first phase: finite value and every equality law).**
For every fixed $0<R<2\sqrt2$ there is an integer $A_R\ge14$ such that
all integers $a\ge A_R$ and $1\le h\le R\sqrt a$ satisfy

$$
M(a,h)=m_{a,h}
=\min_{0<u\le1/a}\left\{
\frac{h^2}{u}+\frac{a^2r^2}{a-u}
+\frac{(a-1)(2a+1)r^3u}{(a-u)^2}\right\}
=\Phi_{a,h}(u_{a,h}).
\tag{13.18}
$$

The infimum over the original full actual-law domain is attained.
Up to arbitrary permutations of all $s=a+1+h$ labels, every minimizing
law, and only a minimizing law, has the following masses:

$$
\begin{gathered}
|C|=r,\qquad D=[s]\setminus C,\qquad |D|=h,\\
x_{\{j\}}=\frac{u_{a,h}}h\ (j\in D),\qquad
x_C=(a-1)u_{a,h},\qquad
x_{C\setminus\{i\}}=\frac{1-au_{a,h}}r\ (i\in C),\\
x_T=0\quad\hbox{for every other nonempty }T.
\end{gathered}
\tag{13.19}
$$

The parameter is the unique constrained scalar minimizer. Its exact
integer split and capped value are

$$
\begin{cases}
0<u_{a,h}<1/a,&h^2-2a\le6,\\
u_{a,h}=1/a,&h^2-2a\ge7,
\end{cases}
\qquad
m_{a,h}=\frac{a(a+1)^3}{a-1}+ah^2
\quad\hbox{in the second case}.
\tag{13.20}
$$

In particular all missing-one masses vanish at the cap, without losing
positivity of any actual marginal.

**Proof.** First consider $1\le h\le\sqrt a$. Incidence Theorem 14.4
applies with its fixed upper ratio $1<\sqrt2$: its domain has the same
$s=a+1+h$, $\mathbb E K=a$, actual positive $y_i$ and $H$, and its
scalar expression is exactly the one in (13.18). It proves (13.18),
attainment and (13.19) uniformly on this entire portion, including
bounded $h$ and $h/\sqrt a\to0$. Its fixed threshold is independent of
$h$. This is direct reuse, not a fixed-$h$ extrapolation.

For the remaining $\sqrt a\le h\le R\sqrt a$, use Lemmas 13.2--13.4
with $R_*$. A law with $H>U_{a,h}$ already has $H>m_{a,h}$, because
$U_{a,h}$ is one actual member of the scalar family. Any other law
has the separated partition and satisfies the finite hypothesis
$\Lambda>(r/a)P_{a,h}$ of Lemma 12.4 by (13.15). That lemma is a finite
statement for arbitrary integers $a\ge4$, $h\ge1$ and any partition of
sizes $r,h$; its proof has no fixed-width premise. With
$e=\mathbb E[(K-1);A]\ge0$, it gives

$$
H\ge m_{a,h}+\left(\Lambda-\frac raP_{a,h}\right)e
\ge m_{a,h}+a^3e.
\tag{13.21}
$$

Thus the lower bound holds for every original law, with arbitrary
cardinalities and zero type masses. Definition 5.1 at $u=u_{a,h}$
supplies an actual attaining law, proving the value and attainment.
There is no need to infer attainment from compactness of the
positive-marginal domain.

For completeness the equality argument from Theorem 12.5 is finite
once strict payment holds, and applies here with precisely these
parameters. If $H=m_{a,h}$, (13.21) forces $e=0$. Since $K-1$ is a
nonnegative integer on $A$, every positive-mass type meeting $D$ is a
tail singleton. The mean cap relation (13.12) then gives $u\le1/a$.
The retained identity (12.19) and its Cauchy and strict Jensen steps
in (12.21) give, with $b_a=(a-1)(2a+1)$,

$$
H\ge\sum_{j\in D}t_j^{-1}
+\sum_{i\in C}\left(\frac{a^2}{y_i}+\frac{b_au}{y_i^2}\right)
\ge\Phi_{a,h}(u)\ge m_{a,h}.
\tag{13.22}
$$

All inequalities must be equalities. Uniqueness of the constrained
scalar minimum, tail Cauchy and strict convexity of
$g_u(y)=a^2/y+b_au/y^2$ imply

$$
u=u_{a,h},\qquad t_j=u_{a,h}/h,\qquad
y_i=(a-u_{a,h})/r\quad(i\in C).
\tag{13.23}
$$

With only tail singletons, the exact residual (12.28) is a sum of
$\mathbb E[\rho_i;A^c]/y_i^2$, where

$$
\rho_i=(1-I_i)(2a+1)(a-L)+I_i(r-L)(r-L-1)\ge0,
\qquad \sum_{i\in C}\rho_i=Q(L).
$$

The sum vanishes only when every positive-mass core-only type has
$Q(L)=0$. On such a type $1\le L\le r$; its only integer zeros are
$a$ and $r$. Consequently the only remaining masses are $z=x_C$ and
$b_i=x_{C\setminus\{i\}}$. Normalization and the same mean constraint
force

$$
z+\sum_i b_i=1-u,\qquad rz+a\sum_i b_i=a-u,
\qquad z=(a-1)u,\quad \sum_i b_i=1-au.
$$

Equation (13.23) then gives
$1-u-b_i=(a-u)/r$, so $b_i=(1-au)/r$ for each $i$. This proves
necessity of every mass and zero in (13.19). Conversely, for every
$0<u\le1/a$ these masses are nonnegative, sum to one and have mean
$u+r(a-1)u+a(1-au)=a$. They induce precisely the positive marginals
$u/h$ and $(a-u)/r$, and their energy is $\Phi_{a,h}(u)$ by (5.4).
Taking $u=u_{a,h}$ proves sufficiency, including the boundary where
some type masses vanish.

Take $A_R$ to be at least $14$ and the maximum of the finitely many
thresholds above and the one from Incidence Theorem 14.4 at upper
ratio $1$. Every one depends only on $R$. For $a\ge14$,

$$
2a+6<\Gamma_a
=2a+6+\frac{12a-5}{(a-1)^2}<2a+7.
$$

Proposition 5.2 and integrality of $h^2-2a$ now give exactly (13.20);
no zero cap derivative occurs. At the cap, (13.19) has
$x_C=(a-1)/a$, $x_{\{j\}}=1/(ah)$, all missing-one masses zero,
and actual marginals $(a-1)/a$ on $C$ and $1/(ah)>0$ on $D$.
Thus neither a strict-support premise nor a nondegeneracy premise
has been inserted.

This is a repo-derived extension of the finite all-law comparison,
not a literature minimum theorem. The scalar identities and actual
family are those of Section 5 and Incidence Definition 13.2; the
uniform compact-ratio core certificate is Lemma 7.1; the finite
common-law and cap-payment identities are Incidence Lemma 13.4 and
Lemma 12.4. The new bridge is the uniform separation gap (13.6) and
the cap-adjusted certificate (13.8)--(13.17). The bounded strip of
Theorem 12.5 and the fixed subcritical ranges of Incidence Theorem
14.4 do not themselves supply this bridge. The other CDSO volumes
on universal vertices, sink incidences, higher-capacity profiles and
moving-mean crossovers address different graph budgets or numbers
of extra labels and are not used as this growing-$h$ theorem.

The CDSO normalization is the maximum-endpoint-degree denominator
without a factor $1/\sqrt2$ in A. M. Albalahi, S. Das, A. Ali,
J. Barman and A. E. Hamza, *On the hyperbolic Sombor index and its
counterpart*, Discrete Math. Lett. 16 (2025), 108--115, p.109,
DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176),
[original](https://www.dmlett.com/archive/v16/DML25_v16_pp108-115.pdf).
The finite Jensen inequality and supporting-line principle used in
the cited certificates are the classical convexity statements in
S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University
Press, §§3.1.3, 3.1.8, pp.69, 77--78,
[author-hosted text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf).
Strong Jensen above follows by applying that inequality to
$f_u-a^2y^2/2$, with its second derivative checked explicitly; no
additional external stability theorem is a premise.
N. Smirnov, *Bicyclic Graphs with Maximum Complementary Diminished
Sombor Index*, Discrete Math. Lett. 18 (2026), 100--106,
DOI [10.47443/dml.2026.164](https://doi.org/10.47443/dml.2026.164),
[original](https://www.dmlett.com/archive/v18/DML26_v18_pp100-106.pdf),
Theorem 2.1 concerns finite connected bicyclic maximization and is
not a premise of (13.18). The relation to the full text of K. Zhao
and X. Zhao, *Extremal values with respect to vertex-degree-based
topological indices in unicyclic and bicyclic graphs*,
DOI [10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26),
remains unassessed; it supplies no premise. No literature-priority
or Lean-kernel-verification assertion accompanies this prose theorem.
Its threshold is existential, with no assertion of the least one,
small exceptional parameters, subsequent phases or prescribed finite
connected-graph extrema. ∎

**Corollary 13.6 (Every sublinear moving-width first strip).** Let
$W:\mathbb N\to[0,\infty)$ satisfy $W(a)/a\to0$. There is an integer
$A_W$ such that for every integer $a\ge A_W$ and every integer $h\ge1$
with $|h^2-2a|\le W(a)$, the value, attainment and exhaustive equality
classification (13.18)--(13.20) hold.

**Proof.** Eventually $W(a)\le a$, so every such pair satisfies
$h^2\le3a$ and therefore $1\le h\le\sqrt3\sqrt a$. Apply Theorem 13.5
with the one fixed ratio bound $R=\sqrt3<2\sqrt2$, and take the maximum
of its threshold and the threshold for $W(a)\le a$. This covers all
pairs at each sufficiently large $a$, not just a chosen sequence.
No monotonicity, integrality or boundedness of $W$ is needed. In
particular the assertion is not obtained by varying the constant
$W$ inside Theorem 12.5. ∎

**Proposition 13.7 (An obstruction to a common threshold at the second
boundary).** The thresholds in Theorem 13.5 cannot be chosen bounded
as $R$ increases to $2\sqrt2$. Its strict upper-ratio condition also
cannot be replaced by $h\le2\sqrt2\sqrt a$ with an eventual threshold.
Both assertions fail already by comparison with an actual law on
$a+2$ core labels and $h-1$ singleton labels.

**Proof.** For $h\ge2$ the law (5.6) is actual, with positive marginals,
and Theorem 3.1 gives its energy

$$
H_2(a,h)=\frac{(a+2)^3(a+1)}{a-1}
+\frac{(a+1)(h-1)^2}{2}.
$$

Its exact difference from the cap value $S_{a,h}$ in (12.2) is

$$
H_2(a,h)-S_{a,h}
=4a^2+\frac{39a+77}{2}+\frac{46}{a-1}
-\frac{(a-1)h^2}{2}-(a+1)h.
\tag{13.24}
$$

For integers $b\ge8$, first take $a=2b^2+1$, $h=4b$. Then
$h^2=8a-8<8a$, $h/\sqrt a\to2\sqrt2$ from below, and (13.24) is

$$
-8b^3+55b^2-8b+62+\frac{23}{b^2}<0.
$$

Indeed its first two terms sum to at most $-9b^2$, and the remaining
terms are less than $63$. Also $h^2>\Gamma_a$ since $a\ge14$ and
$\Gamma_a<2a+7$, so $S_{a,h}=m_{a,h}$ is the minimum of the entire
scalar family, not merely one member. For each such pair there is
an $R_b<2\sqrt2$ strictly above $h/\sqrt a$. If all thresholds for
$R<2\sqrt2$ had a common finite bound, these arbitrarily large pairs
would contradict (13.18). Thus no such uniform bound exists.

At the second boundary take instead $a=2b^2$, $h=4b$ with $b\ge8$.
Then $h^2=8a$ exactly, and (13.24) equals

$$
-8b^3+47b^2-4b+\frac{77}{2}+\frac{46}{2b^2-1}<0.
$$

Here the first two terms sum to at most $-17b^2$, while the remaining
terms are less than $39$. Again $h^2>\Gamma_a$, so this actual law
beats the entire family (13.19) at arbitrarily large boundary pairs.
These comparisons neither determine the unrestricted minimizer at
those pairs nor prescribe a connected graph realization. They are
repo-derived finite comparisons using the already actual construction
of Theorem 3.1; no asymptotic expansion with varying fixed parameters
is needed. ∎

## 追加锚（本行以下为增补区）

## 14. The full second transition and its exact two-family envelope

**Definition 14.1 (The two finite scalar branches).** Retain exactly
Definition 1.1. Write $m_1(a,h)=m_{a,h}$ for the constrained scalar
value in (13.18), whose definition is valid for every $a\ge4$, $h\ge1$.
For $h\ge2$ put $m=a+2$, $n=h-1$ and

$$
\begin{aligned}
G_2(p)&=\frac{n^2}{p}+\frac{(m-1)^2m^2}{a-p}
 +\frac{(2m-1)m^3(ap-1)}{(a-p)^2},\\
m_2(a,h)&=\min_{1/a\le p\le2/(a+1)}G_2(p).
\end{aligned}
\tag{14.1}
$$

Set $m_2(a,1)=+\infty$. For unified notation, when $j\in\{1,2\}$
and $h\ge j$, define

$$
\begin{gathered}
m=a+j,\quad r=m-1,\quad n=h+1-j,\quad d=2m-1,\\
\ell_j=\frac{j-1}{m-2},\qquad u_c=\frac jr,\qquad
b_j(u)=d\bigl((m-2)u-(j-1)\bigr),\\
F_j(u)=\frac{n^2}{u}+\frac{r^2m^2}{a-u}
                    +\frac{m^3b_j(u)}{(a-u)^2}.
\end{gathered}
\tag{14.2}
$$

The scalar interval is $(0,u_c]$ for $j=1$ and $[\ell_2,u_c]$
for $j=2$. Thus $F_1=\Phi_{a,h}$, $F_2=G_2$ and their minima are
$m_j(a,h)$. Denote their minimizing parameters by $p_j$.
The second family is the portion $1\le v\le2$ of Proposition 3.2:
the substitution $u=v/(a+v-1)$ gives, on a partition $C\dot\cup D$
of sizes $m,n$,

$$
\begin{gathered}
x_{\{k\}}=u/n\quad(k\in D),\qquad
x_C=1-j+(m-2)u,\\
x_{C\setminus\{i\}}=\frac{j-ru}{m}\quad(i\in C),
\qquad x_T=0\quad\hbox{otherwise}.
\end{gathered}
\tag{14.3}
$$

For $j=1$ these are exactly the published laws (13.19), with an
arbitrary legal scalar parameter. The cap member has energy

$$
S_j=\frac{m^3r}{a-1}+\frac{n^2r}{j}.
\tag{14.4}
$$

All these are comparison laws, without any support restriction on
$\mathcal X(a,h)$. In the compact range $5/2\le q=h/\sqrt a\le R$,
put $U=\min\{S_1,S_2\}$. Every constant and threshold indexed by $R$
below is independent of the actual law, the integer pair and the
labeling. Here $2\sqrt2<R<2\sqrt6$ is fixed.

**Lemma 14.2 (Only the two adjacent core sizes survive).** There are
$A_R,b,c_0>0$ such that, for $a\ge A_R$, $5/2\le q\le R$, every
$x\in\mathcal X(a,h)$ with $H(x)\le U$ has a unique partition
$C\dot\cup D=[a+1+h]$ with

$$
\begin{gathered}
|C|=a+j,\quad |D|=h+1-j,\quad j\in\{1,2\},\\
y_i\ge c_0\quad(i\in C),\qquad 0<y_k<b/a<c_0\quad(k\in D).
\end{gathered}
\tag{14.5}
$$

If $A=\{T\cap D\ne\varnothing\}$ and $v=a\mathbb P(A)$, then

$$
\begin{cases}
q\le2\sqrt2+O_R(a^{-1/2}),&j=1,\\
q\ge2\sqrt2-O_R(a^{-1/2}),\quad
v=2+O_R(a^{-1/4}),&j=2.
\end{cases}
\tag{14.6}
$$

In particular, with $u=\sum_{k\in D}y_k$, the second case has
$au\ge3/2$ eventually.

**Proof.** The cap laws (14.4) give, uniformly for each $j=1,2$,

$$
\frac{S_j-B_0}{a^2}=\frac{q^2}{j}+4j-2+O_R(a^{-1/2}).
\tag{14.7}
$$

Consequently $H\le U$ implies $H\le a^3+C_Ra^2$ for some fixed
$C_R\ge1$. Apply Lemma 7.1 with $(C,L,R)=(C_R,5/2,R)$.
Its actual-marginal threshold construction gives $b=4C_R$,
$c_0=(8C_R+1)^{-1}$, a bounded positive integer $j$, and a positive
$v\le j+O_R(a^{-1/2})$. Its lower bound, including the lower bound
on $v$ there, implies

$$
\frac{H-B_0}{a^2}\ge\frac{q^2}{v}+2v+2j-2-O_R(a^{-1/2}).
\tag{14.8}
$$

Replacing $v$ by $\min\{v,j\}$ changes this expression by at most
$O_R(a^{-1/2})$. For each positive integer $k$, let

$$
\varphi_k(q)=\min_{0<w\le k}\{q^2/w+2w+2k-2\}.
$$

The scalar evaluation (7.23)--(7.28) shows that on
$[5/2,R]$ only $k=1,2$ can attain
$\min_k\varphi_k(q)=\min\{q^2+2,q^2/2+6\}$.
Since $R<2\sqrt6$, no $k\ge3$ attains it, even at an endpoint of
this compact interval. The bounded set of possible integers from
Lemma 7.1 is finite. Continuity therefore gives a strictly positive
uniform gap for its integers $k\ge3$. Equations (14.7)--(14.8)
exclude all of them for sufficiently large $a$. This proves (14.5),
after increasing the threshold until $b/a<c_0$.

For $j=1$, $\varphi_1(q)=q^2+2$ throughout this range.
If $q\ge2\sqrt2$, its excess over $q^2/2+6$ is $q^2/2-4$.
Comparison with (14.7)--(14.8) bounds that excess by
$O_R(a^{-1/2})$, giving the first line of (14.6).
For $j=2$ and $5/2\le q\le2\sqrt2$,
$\varphi_2(q)=2+2\sqrt2 q$ and

$$
\varphi_2(q)-(q^2+2)=q(2\sqrt2-q).
$$

The same comparison gives the lower bound on $q$ in (14.6).
To obtain the asserted control of $v$, put $w=\min\{v,2\}$.
Using $H\le S_2$ in (14.8) gives

$$
\frac{q^2}{w}+2w-\left(\frac{q^2}{2}+4\right)
=(2-w)\left(\frac{q^2}{2w}-2\right)
\le O_R(a^{-1/2}).
\tag{14.9}
$$

The lower bound already proved for $q$ gives $q^2\ge8-O_R(a^{-1/2})$.
The positive lower bound on $w$ from Lemma 7.1 therefore bounds the
left side of (14.9) below by
$2(2-w)^2/w-O_R(a^{-1/2})$. Hence
$2-w=O_R(a^{-1/4})$; also $v\le2+O_R(a^{-1/2})$.
Finally $u=\mathbb E|T\cap D|\ge\mathbb P(A)=v/a$.
All these are identities or estimates for the original common law. ∎

**Lemma 14.3 (A mean-aware residual on every actual type).** On the
entire sublevel of Lemma 14.2, use its $j,m,r,n,C,D$ and put

$$
\begin{gathered}
t_k=y_k\ (k\in D),\quad u=\sum_{k\in D}t_k,\quad
\delta=\max_{k\in D}t_k,\quad c=\min_{i\in C}y_i,\\
B=|T\cap D|,\quad L=|T\cap C|,\quad K=L+B,\quad A=\{B>0\},\\
\alpha=mr(2m-1),\quad \beta=3m^2-3m+1,\\
Q(l)=(m-l)(r-l)(2m-1+l)=\alpha-\beta l+l^3,\\
f_u(y)=\frac{r^2}{y}-\frac{d(j-1+u)}{y^2},\quad
\bar y=\frac{a-u}{m},\quad
\mathcal S_f=\sum_{i\in C}f_u(y_i)-m f_u(\bar y),\\
\mathcal B_j(w)=\frac{r^2m^2}{a-w}
             -\frac{d(j-1+w)m^3}{(a-w)^2},\quad
\mathcal A_j(u)=\frac{\mathcal B_j(0)-\mathcal B_j(u)}{u},\\
\eta_0=\sqrt{\alpha-\mathcal A_j(u)},\quad
\eta_c=\frac{rn}{j},\quad \eta=\max\{\eta_0,\eta_c\},\quad
\gamma=\eta^2-\alpha+\mathcal A_j(u)\ge0.
\end{gathered}
\tag{14.10}
$$

The square root is positive for sufficiently large $a$.
On $A$ define

$$
\begin{gathered}
V_T=\sum_{k\in T\cap D}t_k^{-1},\qquad
Z_T=K^2\sum_{k\in T\cap D}t_k^{-2},\\
\mathcal G_T=Z_T+Q(L)-\mathcal A_j(u)B-2\eta V_T+\gamma B
 -\frac\gamma r\bigl(m(B-1)+L\bigr).
\end{gathered}
\tag{14.11}
$$

There are $\kappa_R,C_R>0$ such that, uniformly on this sublevel,

$$
\begin{aligned}
\mathcal G_{\{k\}}&=(t_k^{-1}-\eta)^2\quad(k\in D),\\
\mathcal G_T&\ge\kappa_Ra^3\quad(B>0,\ K\ge2),\\
\mathcal S_f&\ge\frac{a^2}{2}\sum_{i\in C}(y_i-\bar y)^2,\\
0\le\mathbb E[\mathcal G_T;A]+\mathbb E[Q(L);A^c]
 +\mathcal S_f&\le C_Ra.
\end{aligned}
\tag{14.12}
$$

In particular

$$
\begin{gathered}
\mathbb P(A,K\ge2)=O_R(a^{-2}),\qquad
c\ge1-O_R(a^{-1/2}),\qquad
\delta\le\frac{1+O_R(a^{-1/4})}{\eta},\\
\frac{\eta^2}{a^3}=\max\left\{2,\frac{n^2}{j^2a}\right\}
                         +O_R(a^{-1}).
\end{gathered}
\tag{14.13}
$$

**Proof.** The threshold partition gives $u\le bn/a=O_R(a^{-1/2})$.
On $0\le w\le u$, differentiation of (14.10) gives

$$
\mathcal B_j'(w)=\frac{r^2m^2}{(a-w)^2}
 -\frac{dm^3(a+w+2j-2)}{(a-w)^3}
=-a^2+O_R(a).
\tag{14.14}
$$

Thus $\mathcal A_j(u)=a^2+O_R(a)$,
$\alpha-\mathcal A_j(u)=2a^3+O_R(a^2)$,
$\eta_0=\sqrt2\,a^{3/2}+O_R(\sqrt a)$ and
$\eta,\gamma^{1/2}=O_R(a^{3/2})$. These follow from rational
expressions with $a-w\ge a/2$, uniformly for both possible $j$.
They give the last assertion of (14.13).

For $i\in C$, let $I_i=\mathbf1_{\{i\in T\}}$ and set

$$
\rho_i=(1-I_i)d(r-L)+I_i(m-L)(m-L-1),\qquad R_i=\mathbb E\rho_i.
\tag{14.15}
$$

Every $\rho_i\ge0$: when $I_i=0$ one has $L\le r$;
when $I_i=1$ the last two factors are consecutive integers.
Their sum is $Q(L)$, nonnegative at every integer $0\le L\le m$.
The exact expansion

$$
\rho_i=I_i(L^2-r^2)+d(r-L)
$$

gives, using $\mathbb E L=a-u$,

$$
R_i=\mathbb E[L^2I_i]-r^2y_i+d(j-1+u).
\tag{14.16}
$$

The term $j-1$ here retains the difference between the original
mean $a$ and the adjacent lower core size $r$.
Since $K^2\ge L^2$ and $0<y_i\le1$, (14.16) yields

$$
H\ge H_D+\mathcal B_j(u)+\mathbb E Q(L)+\mathcal S_f,
\qquad H_D=\mathbb E[Z_T;A].
\tag{14.17}
$$

On the interval $c_0\le y\le1$,

$$
f_u''(y)=\frac{2\{r^2y-3d(j-1+u)\}}{y^4}\ge a^2
\tag{14.18}
$$

for sufficiently large $a$: the subtracted term is $O_R(a)$,
whereas $r^2y\ge r^2c_0$, and eventually it is at most half of
$r^2y$. Jensen applied to $f_u(y)-a^2y^2/2$ proves the third line
of (14.12), including nonnegativity of $\mathcal S_f$.

The original mean gives the cap correction without assuming the cap:

$$
a\le m\mathbb P(A^c)+\mathbb E[L+B;A],\qquad
ru-j\le m\mathbb E[B-1;A]+\mathbb E[L;A].
\tag{14.19}
$$

Also $\mathbb E[V_T;A]=n$, by the actual inclusion probability of
each tail label. Substituting (14.11) into (14.17), and applying
(14.19) with multiplier $\gamma/r\ge0$, gives

$$
H\ge E_j+\mathbb E[\mathcal G_T;A]+\mathbb E[Q(L);A^c]
                 +\mathcal S_f,\qquad
E_j=\mathcal B_j(0)+2\eta n-\frac{j\gamma}{r}.
\tag{14.20}
$$

For a tail singleton, $L=0$, $B=K=1$, so (14.11) is exactly the
square in (14.12). For every other type meeting $D$, completing
each reciprocal square gives

$$
\mathcal G_T\ge
\eta^2\left(1-\frac B{K^2}\right)
-\mathcal A_j(u)(B-1)-\beta L+L^3-\frac\gamma r(K-1).
\tag{14.21}
$$

If $2\le K\le\sqrt a$, then $B/K^2\le1/2$ and $B,L\le\sqrt a$.
Since $\eta^2\ge a^3$ eventually, (14.21) is at least
$a^3/2-O_R(a^{5/2})\ge a^3/4$.
If $K>\sqrt a$, every reciprocal $z=t_k^{-1}$ exceeds $a/b$.
Consequently $K^2z>4\eta$ eventually and

$$
Z_T-2\eta V_T\ge\tfrac12 Z_T
\ge\frac{BK^2a^2}{2b^2},\qquad
\mathcal G_T\ge\frac{BK^2a^2}{2b^2}-\mathcal A_j(u)B
                 +\gamma\left(1-\frac{K-1}{r}\right).
\tag{14.22}
$$

For $K\le m=r+1$ the last term is nonnegative, giving at least
$Ba^3/(4b^2)$ eventually. If $K>m$, then $K\le m+n$ and that term
is at least $-\gamma n/r=-O_R(a^{5/2})$, while the first term is
at least $Ba^4/(2b^2)$. Thus (14.22) is again at least
$a^3/(4b^2)$ eventually. This proves the second line of (14.12)
with $\kappa_R=\min\{1/4,1/(4b^2)\}$, for every allowed actual type.

It remains to bound the residual in (14.20). Direct expansion gives

$$
\mathcal B_j(0)=a^3+2ja^2+O(a),\qquad
S_j=a^3+4ja^2+\frac{n^2a}{j}+O_R(a).
\tag{14.23}
$$

If $\eta=\eta_c$, then

$$
E_j=\mathcal B_j(0)+\frac{rn^2}{j}
                 +\frac{j\eta_0^2}{r}=S_j+O_R(a).
\tag{14.24}
$$

For $j=1$ the inequality $q\ge5/2$ ensures $\eta_c>\eta_0$
eventually. For $j=2$, (14.6) implies
$n/\sqrt a\ge2\sqrt2-O_R(a^{-1/2})$, and hence
$(\eta_0-\eta_c)_+=O_R(a)$. Completing the scalar square in
$2\eta n-(j/r)(\eta^2-\eta_0^2)$ shows that if $\eta_0>\eta_c$,
its value at $\eta_0$ is its value at $\eta_c$ minus
$(j/r)(\eta_0-\eta_c)^2=O_R(a)$. Thus (14.24) remains true in
both cases. Since $H\le U\le S_j$, (14.20) proves the last line
of (14.12); all its residuals are nonnegative by the signs just proved.

The nonsingleton bound and strong Jensen now give
$\mathbb P(A,K\ge2)=O_R(a^{-2})$ and
$\sum_{i\in C}(y_i-\bar y)^2=O_R(a^{-1})$.
As $\bar y=1-O_R(a^{-1})$, this proves the assertion about $c$.
For a tail label $k$, put $x_k=x_{\{k\}}$ and
$p_2=\mathbb P(A,K\ge2)$. Actual marginals satisfy
$0\le t_k-x_k\le p_2$ and $\eta p_2=O_R(a^{-1/2})$.
If $t_k\ge1/\eta$, then $x_k\ge t_k/2$ eventually. Writing
$z=\eta t_k\ge1$, its singleton square in (14.12) gives

$$
\frac\eta2\frac{(z-1)^2}{z}
\le x_k(t_k^{-1}-\eta)^2\le C_Ra,
\qquad \frac{(z-1)^2}{z}=O_R(a^{-1/2}).
$$

For $z\ge1$, this implies $z-1=O_R(a^{-1/4})$.
Labels with $t_k<1/\eta$ already satisfy the asserted upper bound.
Taking the maximum proves the remaining assertion of (14.13).

The expectation step is the elementary pointwise-certificate form of
weak duality, as in D. Bertsimas and I. Popescu, *Optimal inequalities
in probability theory: A convex optimization approach*, SIAM J. Optim.
15(3), 780--804, DOI [10.1137/S1052623401399903](https://doi.org/10.1137/S1052623401399903),
Theorem 2.1, p.785. The particular residual (14.11), its signs and its
common-law cap correction are repo-derived here; no strong-duality or
independent moment-realizability assertion is used. Strong Jensen is
finite Jensen applied to the function with its displayed quadratic
subtracted, in the sense of S. Boyd and L. Vandenberghe, *Convex
Optimization*, §3.1.8, pp.77--78,
[author text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf). ∎

**Lemma 14.4 (Strict payment to the correct constrained branch).** On
the same sublevel, put

$$
e=\mathbb E[K-1;A],\qquad
\Lambda=\frac3{\delta^2}-\frac{\max\{\alpha,\beta\}}{c^2},\qquad
P_j=\bigl(-F_j'(u_c)\bigr)_+.
\tag{14.25}
$$

For sufficiently large $a$, uniformly,

$$
\Lambda-\frac mrP_j\ge a^3,\qquad
H(x)\ge m_j(a,h)+\left(\Lambda-\frac mrP_j\right)e
       \ge m_j(a,h)+a^3e.
\tag{14.26}
$$

Equality with $m_j(a,h)$ forces every positive-mass tail-containing
type to be a singleton and forces $u=p_j$.

**Proof.** Retain the nonnegative terms in (14.16), and put

$$
\Delta_i=\mathbb E[(K^2-L^2)I_i],\quad c_m=rd,\quad
Z=\mathbb E\left[(K^2-1)\sum_{k\in T\cap D}t_k^{-2}\right].
$$

The exact identity is

$$
H=\sum_{k\in D}t_k^{-1}+Z+
\sum_{i\in C}\left\{\frac{r^2}{y_i}
 -\frac{d(j-1+u)}{y_i^2}+\frac{R_i+\Delta_i}{y_i^2}\right\}.
\tag{14.27}
$$

On $A$ every deficit $c_mB-\rho_i$ is nonnegative.
For $I_i=0$ it is $d\{r(B-1)+L\}$; for $I_i=1$ it is
$c_m(B-1)+r^2+dL-L^2\ge0$, since $L\le m\le d$.
Their sum is

$$
\alpha(B-1)+\beta L-L^3
\le\max\{\alpha,\beta\}(K-1).
\tag{14.28}
$$

Off $A$, the $\rho_i$ are nonnegative. Weighting these signed
inequalities only after establishing the signs yields

$$
\sum_{i\in C}\frac{R_i-c_mu}{y_i^2}
\ge-\frac{\max\{\alpha,\beta\}}{c^2}e.
$$

The tail integrand in $Z$ is at least
$B(K^2-1)/\delta^2\ge3(K-1)/\delta^2$ on $A$ and is zero off $A$.
Discarding only the nonnegative $\Delta_i$ in (14.27) gives

$$
H\ge\sum_{k\in D}t_k^{-1}+
\sum_{i\in C}\left\{\frac{r^2}{y_i}+\frac{b_j(u)}{y_i^2}\right\}
+\Lambda e\ge F_j(u)+\Lambda e.
\tag{14.29}
$$

For $j=1$, $b_j(u)>0$. For $j=2$, Lemma 14.2 gives
$au\ge3/2$, so $b_2(u)=d(au-1)>0$. Thus the last step is Cauchy
on the actual tail marginals and strict Jensen on the actual core
marginals, whose sum is $a-u$. No convexity of $H$ in $x$ is assumed.

On $[\ell_j,a)$, with zero excluded when $j=1$, one has $b_j(u)\ge0$
and

$$
F_j''(u)=\frac{2n^2}{u^3}+\frac{2r^2m^2}{(a-u)^3}
 +\frac{4m^3d(m-2)}{(a-u)^3}
 +\frac{6m^3b_j(u)}{(a-u)^4}>0.
\tag{14.30}
$$

This proves uniqueness of each constrained scalar minimizer;
existence follows from compactness for $j=2$ and the divergence at
zero for $j=1$. Our actual $u$ is in this interval: $0<u<a$ by the
common marginal budget, and $u>\ell_2=1/a$ when $j=2$.
The mean inequality (14.19) gives

$$
(u-u_c)_+\le\frac mr e.
\tag{14.31}
$$

Convexity and the supporting tangent at $u_c$ give, for every such $u$,

$$
F_j(u)\ge m_j(a,h)-P_j(u-u_c)_+.
\tag{14.32}
$$

Indeed, if $F_j'(u_c)\ge0$, the minimum on the extended interval is
already on its constrained part. If $F_j'(u_c)<0$, the constrained
minimum is $F_j(u_c)$ and its supporting tangent has slope $-P_j$.
This is the first-order convexity inequality of Boyd--Vandenberghe,
§3.1.3, p.69; its hypotheses here are (14.30).

To check strict payment with the entire cap derivative retained,
write $z=n^2/(j^2a)$. Exact differentiation gives

$$
\begin{gathered}
F_j'(u_c)=-\frac{n^2r^2}{j^2}+D_j,\\
D_1=\frac{a^2(2a^3+2a^2+2a+1)}{(a-1)^2},\qquad
D_2=\frac{(a+1)^2(2a^3+8a^2+12a+7)}{(a-1)^2}.
\end{gathered}
\tag{14.33}
$$

Hence $P_j/a^3=(z-2)_++O_R(a^{-1})$.
By (14.13), $\max\{\alpha,\beta\}/a^3=2+O(a^{-1})$ and

$$
\frac\Lambda{a^3}\ge3\max\{2,z\}-2-O_R(a^{-1/4}).
$$

Since $m/r=1+O(a^{-1})$ and $z$ is bounded uniformly,

$$
\frac{\Lambda-(m/r)P_j}{a^3}
\ge3\max\{2,z\}-2-(z-2)_+-O_R(a^{-1/4})
\ge4-O_R(a^{-1/4}).
\tag{14.34}
$$

Increase the threshold to obtain the first assertion of (14.26).
Combining (14.29), (14.31) and (14.32) proves its lower bound.
Equality forces $e=0$. The nonnegative integer $K-1$ then vanishes
on every positive-mass type meeting $D$, and (14.31) gives $u\le u_c$.
Equation (14.29) and uniqueness of the scalar minimum give $u=p_j$. ∎

**Theorem 14.5 (Exact value and every actual equality law through the
second transition).** For every fixed $2\sqrt2<R<2\sqrt6$ there is an
integer $A_R$ such that every integer pair $a\ge A_R$,
$1\le h\le R\sqrt a$ satisfies

$$
M(a,h)=\min\{m_1(a,h),m_2(a,h)\}.
\tag{14.35}
$$

The infimum on the full domain of Definition 1.1 is attained.
Up to arbitrary permutations of the labels, every minimizing law is
(13.19) at $p_1$ when $m_1$ attains this minimum, or, when $h\ge2$,

$$
\begin{gathered}
|C|=a+2=m,\quad |D|=h-1=n,\qquad
x_{\{k\}}=p_2/n\quad(k\in D),\\
x_C=ap_2-1,\qquad
x_{C\setminus\{i\}}=\frac{2-(a+1)p_2}{m}\quad(i\in C),\\
x_T=0\quad\hbox{for every other nonempty }T,
\end{gathered}
\tag{14.36}
$$

when $m_2$ attains the minimum. These conditions are necessary and
sufficient. At an exact tie the two classes are both included and
there are no further minimizing laws. A nontrivial convex combination
of distinct minimizing laws is not a minimizing law.
The scalar parameters are unique within each branch.
All actual marginals in these laws are positive, including the
endpoint degeneracies.

**Proof.** The existing comparisons (14.3) are actual mean-$a$ laws.
For completeness their total tail mass is $u$, their full-core mass
is $z=1-j+(m-2)u$, and their total missing-one mass is $w=j-ru$.
The scalar intervals in Definition 14.1 give $z,w\ge0$, and

$$
u+z+w=1,\qquad u+mz+rw=a.
\tag{14.37}
$$

Every tail marginal is $u/n>0$, and every core marginal is
$1-u-w/m=(a-u)/m>0$. The energy is

$$
\frac{n^2}{u}+\frac{m^3z+r^3w}{((a-u)/m)^2}=F_j(u).
\tag{14.38}
$$

The scalar minima exist, by Proposition 5.2 for $j=1$ and by the
closed interval in (14.1) for $j=2$; uniqueness also follows from
(14.30). Thus these laws prove the upper bound in (14.35) with
actual attainment of each scalar branch.

For $1\le h\le(5/2)\sqrt a$, use Theorem 13.5 with its fixed upper
ratio $5/2<2\sqrt2$. It proves $M=m_1$ and every equality law there.
When $h\ge2$, an attaining second-family law cannot be one of those
first-family laws: for sufficiently large $a$, exactly $a+2$ of
its marginals exceed $1/2$, whereas exactly $a+1$ first-family
marginals do. Therefore $m_2>m_1$ in this portion. When $h=1$ its
defined value is $+\infty$. This proves all claims on this portion
by direct reuse of the published theorem, uniformly also for bounded
$h$ and for $h/\sqrt a\to0$.

Now take $5/2\le q\le R$. If $H(x)>U$, it already exceeds the
minimum in (14.35), since $m_j\le S_j$ for each $j$.
Otherwise Lemmas 14.2--14.4 apply to this same actual law, with
$j=1$ or $j=2$, and give

$$
H(x)\ge m_j(a,h)+a^3e
\ge\min\{m_1(a,h),m_2(a,h)\}.
\tag{14.39}
$$

This proves the lower bound for every law on every nonempty subset;
no existence of a global optimizer was assumed in deriving it.
Together with (14.38) it proves (14.35) and attainment.

Suppose equality holds. Then (14.39) forces $m_j$ to attain the
minimum and $e=0$. Every positive-mass type meeting $D$ is a tail
singleton; $u=p_j$. Equality in the Cauchy and strict Jensen steps
of (14.29) forces

$$
t_k=p_j/n\quad(k\in D),\qquad y_i=(a-p_j)/m\quad(i\in C).
\tag{14.40}
$$

With only tail singletons, $\Delta_i=0$ and the part of $R_i$ on
$A$ is exactly $c_mp_j$. Consequently the exact identity (14.27)
reduces to the expression before Jensen in (14.29) plus

$$
\mathbb E\left[\sum_{i\in C}\frac{\rho_i}{y_i^2};A^c\right]\ge0.
\tag{14.41}
$$

Equality makes this term zero. On a nonempty core-only type, the
only integer zeros of $\sum_i\rho_i=Q(L)$ are $L=r$ and $L=m$.
Thus the only remaining possible types are $C$ and the
$C\setminus\{i\}$. If their masses are $z,b_i$, normalization and
the original mean force

$$
z=1-j+(m-2)p_j,\qquad \sum_i b_i=j-rp_j.
$$

Their equal marginals (14.40) give
$1-p_j-b_i=(a-p_j)/m$, hence $b_i=(j-rp_j)/m$ individually.
This is precisely (13.19) or (14.36), including every asserted zero.
Conversely (14.38) proves sufficiency whenever the branch attains
the smaller value. The partition is recovered from the large and
small actual marginals, so no additional equality partition or law
is lost by relabeling.

For the endpoint assertions in the second family, at $p=1/a$ the
full-core mass vanishes and the missing-one masses are
$(a-1)/(am)>0$; at $p=2/(a+1)$ the missing-one masses vanish and the
full-core mass is $(a-1)/(a+1)>0$. The tail and core marginals just
computed remain positive at both endpoints. The first family's cap
and its positive marginals are already described in (13.19)--(13.20).
The second scalar minimum is at its lower endpoint if
$G_2'(1/a)\ge0$, at its upper endpoint if
$G_2'(2/(a+1))\le0$, and otherwise at the unique zero of $G_2'$ in
between. Strict convexity (14.30) includes the cases of zero endpoint
derivative, so these degeneracies introduce no extra scalar minima.

Finally, every winning second-family law is in the compact-ratio
portion, and Lemma 14.2 applied to it gives $ap_2\ge3/2$.
In particular it has a positive full-core mass of cardinality $a+2$.
A mixture that is a first-family minimizing law cannot contain such
a component, because the first-family support has no type of that
cardinality. A mixture that is a second-family minimizing law cannot
contain a first-family component: that component has positive
singleton masses at $h$ distinct labels, whereas the second-family
law has singleton masses only at $h-1$ labels. Among components in
the same family, positivity of every tail singleton forces their
tail sets to be contained in the resulting law's tail set; equality
of their cardinalities forces the tail sets to agree. The scalar
parameter is unique, so all such components are the identical law.
This proves the assertion excluding nontrivial mixtures, also at a tie.

The new lower bound, mean-aware residual and equality reconstruction
are repo-derived consequences of the common-law model. The reused
suppliers are Lemma 7.1 and the scalar phase evaluation in Theorem
7.2, the actual comparison families in Section 3 and (13.19), and
Theorem 13.5 on the lower portion. The adjacent-incidence polynomial
in (14.15)--(14.17) extends the identity of Incidence Lemma 13.4 to
a core whose lower adjacent size need not equal the original mean.
The finite graph reductions and realizations in the universal-vertex,
sink-incidence and higher-capacity volumes, and the moving-mean
phases in *CDSO capacity crossovers and rare phases*, have different
parameter domains and do not supply this growing-surplus equality
classification. The elementary weak-duality and convexity principles
are literature-attested only in the intermediate roles cited in
Lemmas 14.3--14.4.

The normalization is the maximum-degree denominator without
$1/\sqrt2$ in Albalahi--Das--Ali--Barman--Hamza, *On the hyperbolic
Sombor index and its counterpart*, DOI
[10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176),
§1, p.109. Its Conjecture 4.1 supplies historical graph motivation.
Albalahi, *On Two Conjectures Concerning the Hyperbolic Sombor Index
and Its Counterpart*, DOI
[10.47443/dml.2026.217](https://doi.org/10.47443/dml.2026.217),
Proposition 2.1, treats connected graphs of order $5\ell+7$ and
cyclomatic number $\ell$; its Theorem 2.2 is a graph maximum theorem.
Smirnov, *Bicyclic Graphs with Maximum Complementary Diminished
Sombor Index*, DOI
[10.47443/dml.2026.164](https://doi.org/10.47443/dml.2026.164),
Theorem 2.1, is also a finite connected-graph maximum theorem.
Neither is a premise for (14.35). The full text of Zhao--Zhao,
DOI [10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26),
is not an input; its possible overlap remains unassessed. No worldwide
priority assertion is made.

The range stops strictly below $2\sqrt6$; no assertion includes
that third boundary, growing core index, a least threshold, a
small-parameter classification, or an extremal connected finite
graph with prescribed budgets. The finite-value and equality parts
of Open problem 7.3 are resolved here only on the stated range. ∎

## 追加锚（本行以下为增补区）

## 15. Uniform exact laws through every fixed square-root phase

**Definition 15.1 (All adjacent-core branches).** Retain exactly
Definition 1.1. For $1\le j\le h$ put

$$
\begin{gathered}
m=a+j,\quad r=m-1,\quad n=h+1-j,\quad d=2m-1,\\
\ell_j=\frac{j-1}{m-2},\quad u_j=\frac jr,\qquad
I_1=(0,1/a],\quad I_j=[\ell_j,u_j]\ (j\ge2),\\
b_j(p)=d((m-2)p-(j-1)),\\
F_j(p)=\frac{n^2}{p}+\frac{r^2m^2}{a-p}
                    +\frac{m^3b_j(p)}{(a-p)^2},\qquad
\mu_j=\min_{p\in I_j}F_j(p),\\
S_j=F_j(u_j)=\frac{m^3r}{a-1}+\frac{n^2r}{j}.
\end{gathered}
\tag{15.1}
$$

Here $F_j$ denotes the finite-parameter function in (15.1), rather
than the leading-value function with the same letter in Section 7.
Write $p_j$ for the constrained minimizer. Thus $\mu_1=m_1$ and
$\mu_2=m_2$ in Definition 14.1; a missing second branch has value
$+\infty$. On a partition $C\dot\cup D=[s]$ of sizes $m,n$, let
$x^{j,p}$ be the law

$$
x^{j,p}_{\{k\}}=p/n\ (k\in D),\quad
x^{j,p}_C=1-j+(m-2)p,\quad
x^{j,p}_{C\setminus\{i\}}=\frac{j-rp}{m}\ (i\in C),
\tag{15.2}
$$

with all other masses zero. These are comparison laws, not a
restriction of the original domain.

**Lemma 15.2 (Uniform finite-index localization with a strict cap
margin).** Fix $R\ge4$, set $C_R=R^2+10$ and
$J=\lceil4C_R\rceil$. For all sufficiently large $a$, uniformly over
$7/2\le q=h/\sqrt a\le R$, one has $h\ge J$. Put
$U=\min_{1\le k\le J}S_k$. Every actual law with $H\le U$ has the
threshold partition of Lemma 7.1, with

$$
\begin{gathered}
|C|=a+j,\quad |D|=h+1-j,\quad 2\le j\le J,\\
y_i\ge c_0=(8C_R+1)^{-1}\ (i\in C),\qquad
0<y_k<b/a\ (k\in D),\quad b=4C_R,\\
\frac{q^2}{j^2}>\frac52,\qquad
v:=a\mathbb P(T\cap D\ne\varnothing)=j+O_R(a^{-1/2}).
\end{gathered}
\tag{15.3}
$$

For $u=\sum_{k\in D}y_k$ this implies $u>\ell_j$ and
$u=O_R(a^{-1/2})$. The threshold partition is unique. Constants in
this section depend only on the fixed $R$, not on the law or labels.

**Proof.** For bounded $k$, direct expansion of (15.1) gives

$$
\frac{S_k-B_0(a)}{a^2}
=g_k(q)+O_R(a^{-1/2}),\qquad g_k(q)=q^2/k+4k-2.
\tag{15.4}
$$

The choice $k=1$ gives $U\le a^3+C_Ra^2$ eventually. Lemma 7.1
with lower ratio $7/2$ gives its actual partition, $1\le j\le J$,
$v$ bounded below, $v\le j+O_R(a^{-1/2})$, and

$$
\frac{H-B_0(a)}{a^2}
\ge q^2/v+2v+2j-2-O_R(a^{-1/2}).
\tag{15.5}
$$

Its threshold construction gives the displayed $b,c_0$ and
$u\le bn/a=O_R(a^{-1/2})$. In particular these sets are recovered
from the actual marginals, with $b/a<c_0$ eventually.

Let $\phi_j(q)=\min_{0<w\le j}(q^2/w+2w+2j-2)$, and denote the
leading value in Theorem 7.2 by $\mathcal U(q)$. That theorem's scalar
evaluation says $\min_j\phi_j(q)=\mathcal U(q)$, and, since
$q\ge7/2>\sqrt2$, this is also $\min_k g_k(q)$. Its minimizing
integers obey (7.24), hence are at most $J$. Therefore (15.4) gives
$U\le B_0+a^2\mathcal U(q)+O_R(a^{3/2})$. Replacing $v$ by
$w=\min(v,j)$ in (15.5) costs $O_R(a^{-1/2})$, so

$$
0\le\phi_j(q)-\mathcal U(q)\le O_R(a^{-1/2}).
\tag{15.6}
$$

At an exact scalar minimum in this compact ratio interval, the
phase description (7.22) excludes $j=1$. For $j=2$ it gives
$q^2/j^2\ge49/16$, and for $j\ge3$ it gives
$q^2/j^2\ge4(j-1)/j\ge8/3$. Thus none of the compact sets

$$
\{(q,1):7/2\le q\le R\},\qquad
\{(q,j):7/2\le q\le R,\ 2\le j\le J,\ q^2/j^2\le5/2\}
$$

contains a zero of $\phi_j(q)-\mathcal U(q)$. Its continuity and
the finite index range give a positive gap on their union, ignoring
empty sets. Equation (15.6) excludes that union eventually. This
proves the index and strict-margin assertions in (15.3).

For this same actual $j$, $H\le U\le S_j$. Comparing (15.4)--(15.5)
after clipping $v$ gives

$$
0\le q^2/w+2w-(q^2/j+2j)\le O_R(a^{-1/2}).
$$

On $0<w\le j$ the derivative $2-q^2/w^2$ is at most $-1/2$.
Consequently $j-w=O_R(a^{-1/2})$, proving the assertion about $v$.
Finally $au\ge v=j+O_R(a^{-1/2})$, whereas
$a\ell_j=j-1+O_R(a^{-1})$. Hence $u>\ell_j$ eventually. ∎

**Lemma 15.3 (Uniform residual bootstrap for all surviving indices).**
On the sublevel in Lemma 15.2, write

$$
\begin{gathered}
t_k=y_k\ (k\in D),\quad \delta=\max_{k\in D}t_k,\quad
c=\min_{i\in C}y_i,\quad \bar y=(a-u)/m,\\
B=|T\cap D|,\quad L=|T\cap C|,\quad K=L+B,\quad A=\{B>0\},\\
\alpha=mr(2m-1),\quad \beta=3m^2-3m+1,\\
Q(l)=(m-l)(r-l)(2m-1+l)=\alpha-\beta l+l^3,\\
f_u(y)=r^2/y-d(j-1+u)/y^2,\quad
\mathcal S_f=\sum_{i\in C}f_u(y_i)-m f_u(\bar y),\\
\mathcal B_j(w)=\frac{r^2m^2}{a-w}
                    -\frac{dm^3(j-1+w)}{(a-w)^2},\qquad
\mathcal A_j(u)=\frac{\mathcal B_j(0)-\mathcal B_j(u)}u,\\
\eta=rn/j,\qquad \gamma=\eta^2-\alpha+\mathcal A_j(u).
\end{gathered}
\tag{15.7}
$$

For sufficiently large $a$, $\gamma\ge0$, and there are positive
constants $\kappa_R,K_R$ for which the following hold. On $A$ put

$$
\begin{gathered}
V_T=\sum_{k\in T\cap D}t_k^{-1},\quad
Z_T=K^2\sum_{k\in T\cap D}t_k^{-2},\\
\mathcal G_T=Z_T+Q(L)-\mathcal A_j(u)B-2\eta V_T+\gamma B
           -\frac\gamma r\{m(B-1)+L\}.
\end{gathered}
\tag{15.8}
$$

Then

$$
\begin{gathered}
\mathcal G_{\{k\}}=(t_k^{-1}-\eta)^2,\qquad
\mathcal G_T\ge\kappa_Ra^3\quad(B>0,K\ge2),\\
\mathcal S_f\ge\frac{a^2}{2}\sum_{i\in C}(y_i-\bar y)^2,\\
0\le\mathbb E[\mathcal G_T;A]+\mathbb E[Q(L);A^c]+\mathcal S_f
\le K_Ra,\\
\mathbb P(A,K\ge2)=O_R(a^{-2}),\quad
c\ge1-O_R(a^{-1/2}),\quad
\delta\le\frac{1+O_R(a^{-1/4})}{\eta}.
\end{gathered}
\tag{15.9}
$$

**Proof.** The incidence identity and cap correction in Section 14
can be retained with arbitrary bounded $j$; their uniform signs are
proved here. Throughout, $2\le j\le J$, $n=O_R(\sqrt a)$,
$c\ge c_0$, $t_k<b/a$ and $0<u=O_R(a^{-1/2})$. Differentiation gives

$$
\mathcal B_j'(w)=\frac{r^2m^2}{(a-w)^2}
 -\frac{dm^3(a+w+2j-2)}{(a-w)^3}
=-a^2+O_R(a)\quad(0\le w\le u).
\tag{15.10}
$$

Thus $\mathcal A_j(u)=a^2+O_R(a)$. Set $z=n^2/(j^2a)$.
Lemma 15.2 gives $z=q^2/j^2+O_R(a^{-1/2})>5/2-O_R(a^{-1/2})$.
Consequently

$$
\eta^2/a^3=z+O_R(a^{-1}),\quad
(\alpha-\mathcal A_j(u))/a^3=2+O_R(a^{-1}),\quad
\gamma\ge a^3/4,\quad \eta=O_R(a^{3/2}),\quad\gamma=O_R(a^3).
\tag{15.11}
$$

For a core label put $I_i=\mathbf1_{\{i\in T\}}$ and

$$
\rho_i=(1-I_i)d(r-L)+I_i(m-L)(m-L-1),\qquad R_i=\mathbb E\rho_i.
$$

Each $\rho_i$ is nonnegative at every actual type, including $L=m$:
when $I_i=0$, $L\le r$, and otherwise the last factors are consecutive
integers. Expansion and the original mean give

$$
\sum_{i\in C}\rho_i=Q(L)\ge0,\qquad
R_i=\mathbb E[L^2I_i]-r^2y_i+d(j-1+u).
\tag{15.12}
$$

Since $K^2\ge L^2$ and $0<y_i\le1$, the core contribution implies

$$
H\ge H_D+\mathcal B_j(u)+\mathbb E Q(L)+\mathcal S_f,
\qquad H_D=\mathbb E[Z_T;A].
\tag{15.13}
$$

On $c_0\le y\le1$,
$f_u''(y)=2\{r^2y-3d(j-1+u)\}/y^4\ge a^2$ eventually,
uniformly in $j\le J$. Jensen applied after subtracting $a^2y^2/2$
gives the asserted strong bound for $\mathcal S_f$.

The same law's mean and actual marginal identities give

$$
ru-j\le m\mathbb E[B-1;A]+\mathbb E[L;A],\qquad
\mathbb E[V_T;A]=n.
\tag{15.14}
$$

Indeed $a\le m\mathbb P(A^c)+\mathbb E[L+B;A]$ proves the first
inequality. Substituting (15.8) into (15.13), using
$\mathcal B_j(u)=\mathcal B_j(0)-u\mathcal A_j(u)$ and (15.14), yields

$$
H\ge E_j+\mathbb E[\mathcal G_T;A]+\mathbb E[Q(L);A^c]+\mathcal S_f,
\qquad E_j=\mathcal B_j(0)+2\eta n-j\gamma/r.
\tag{15.15}
$$

For $B=K=1,L=0$, (15.8) is exactly the singleton square in (15.9).
For other types on $A$, completing each reciprocal square gives

$$
\mathcal G_T\ge\eta^2(1-B/K^2)-\mathcal A_j(u)(B-1)
 -\beta L+L^3-\frac\gamma r(K-1).
\tag{15.16}
$$

If $2\le K\le\sqrt a$, then $B/K^2\le1/2$, and all negative
terms other than $-\eta^2 B/K^2$ are $O_R(a^{5/2})$.
By (15.11), this bounds (15.16) below by $a^3/4$ eventually.
If $K>\sqrt a$, every $t_k^{-1}>a/b$ and
$K^2t_k^{-1}>4\eta$ eventually. Using $Q(L)\ge0$ gives

$$
\mathcal G_T\ge\frac{BK^2a^2}{2b^2}-\mathcal A_j(u)B
                  +\gamma\left(1-\frac{K-1}{r}\right).
\tag{15.17}
$$

For $K\le m$ the last term is nonnegative, so this is at least
$Ba^3/(4b^2)$. For $K>m$, its negative part is at most
$\gamma n/r=O_R(a^{5/2})$, while $K^2a^2\ge m^2a^2$ has order
$a^4$. The same lower bound $a^3/(4b^2)$ follows after increasing
the threshold. This covers every cardinality up to $s=m+n$.

Uniformly for bounded $j$, (15.10) and elementary expansion give

$$
\mathcal B_j(0)=a^3+2ja^2+O_R(a),\qquad
\frac{j(\alpha-\mathcal A_j(u))}{r}=2ja^2+O_R(a),\qquad
\frac{m^3r}{a-1}=a^3+4ja^2+O_R(a).
$$

Since $\eta=rn/j$, equation (15.15) has

$$
E_j=\mathcal B_j(0)+\frac{rn^2}{j}
                +\frac{j(\alpha-\mathcal A_j(u))}{r}
=S_j+O_R(a).
\tag{15.18}
$$

Now $H\le U\le S_j$. All three residuals in (15.15) are
nonnegative by the signs just proved, so their sum is $O_R(a)$.
The nonsingleton bound gives $p_2:=\mathbb P(A,K\ge2)=O_R(a^{-2})$,
and strong Jensen gives
$\sum_{i\in C}(y_i-\bar y)^2=O_R(a^{-1})$.
Since $\bar y=1-O_R(a^{-1})$, this proves the bound for $c$.

For each tail label let $x_k=x_{\{k\}}$. Actual marginals satisfy
$0\le t_k-x_k\le p_2$ and $\eta p_2=O_R(a^{-1/2})$.
If $t_k\ge1/\eta$, then $x_k\ge t_k/2$ eventually. Put
$w=\eta t_k\ge1$. Its singleton square in (15.15) implies

$$
\frac\eta2\frac{(w-1)^2}{w}
\le x_k(t_k^{-1}-\eta)^2\le K_Ra,
\qquad \frac{(w-1)^2}{w}=O_R(a^{-1/2}).
$$

It follows that $w-1=O_R(a^{-1/4})$. Labels with $t_k<1/\eta$
already obey the desired upper bound, proving (15.9) for their
maximum as well. No positive marginal was assumed bounded below
on the tail. ∎

**Lemma 15.4 (Strict payment to a capped branch, uniformly in the
surviving index).** On the same sublevel define

$$
e=\mathbb E[K-1;A],\quad
\Lambda=\frac3{\delta^2}-\frac{\max\{\alpha,\beta\}}{c^2},\quad
P_j=(-F_j'(u_j))_+.
$$

For sufficiently large $a$, $p_j=u_j$ and

$$
\Lambda-\frac mrP_j\ge a^3,\qquad H(x)\ge S_j+a^3e.
\tag{15.19}
$$

Equality $H=S_j$ holds exactly for the cap law $x^{j,u_j}$ on this
partition.

**Proof.** Put $c_m=rd$,
$\Delta_i=\mathbb E[(K^2-L^2)I_i]\ge0$ and
$Z=\mathbb E[(K^2-1)\sum_{k\in T\cap D}t_k^{-2}]$.
Equation (15.12) gives the exact identity

$$
H=\sum_{k\in D}t_k^{-1}+Z+
\sum_{i\in C}\left\{\frac{r^2}{y_i}
 -\frac{d(j-1+u)}{y_i^2}+\frac{R_i+\Delta_i}{y_i^2}\right\}.
\tag{15.20}
$$

On $A$, $c_mB-\rho_i\ge0$. For $I_i=0$ this is
$d\{r(B-1)+L\}$, and for $I_i=1$ it is
$c_m(B-1)+r^2+dL-L^2\ge0$. Summing gives

$$
\sum_{i\in C}(c_mB-\rho_i)
=\alpha(B-1)+\beta L-L^3
\le\max\{\alpha,\beta\}(K-1).
$$

Off $A$ all $\rho_i\ge0$. Weighting only these signed inequalities
by $y_i^{-2}\le c^{-2}$ yields
$\sum_i(R_i-c_mu)/y_i^2\ge-\max\{\alpha,\beta\}e/c^2$.
Also $Z\ge3e/\delta^2$, since on $A$,
$B(K^2-1)\ge3(K-1)$. Thus (15.20) gives

$$
H\ge\sum_{k\in D}t_k^{-1}
 +\sum_{i\in C}\{r^2/y_i+b_j(u)/y_i^2\}+\Lambda e
\ge F_j(u)+\Lambda e.
\tag{15.21}
$$

Here $b_j(u)>0$ by Lemma 15.2. Cauchy for the actual tail
marginals, and strict Jensen for the core marginals of total $a-u$,
prove the last inequality.

On $\ell_j\le p<a$, excluding zero when $j=1$,

$$
F_j''(p)=\frac{2n^2}{p^3}+\frac{2r^2m^2}{(a-p)^3}
 +\frac{4m^3d(m-2)}{(a-p)^3}
 +\frac{6m^3b_j(p)}{(a-p)^4}>0.
\tag{15.22}
$$

The exact derivative at the cap is

$$
F_j'(u_j)=-\frac{n^2r^2}{j^2}
 +\frac{r^2\{2m r^2+2m-1\}}{(a-1)^2}.
\tag{15.23}
$$

Its second term is $2a^3+O_R(a^2)$, whereas the first term divided
by $a^3$ is $-z+O_R(a^{-1})$, with
$z>5/2-O_R(a^{-1/2})$. Hence $F_j'(u_j)<0$, so strict convexity
forces the unique constrained minimum to be $p_j=u_j$ and
$\mu_j=S_j$. Moreover $P_j/a^3=z-2+O_R(a^{-1})$.

The mean inequality (15.14) gives
$(u-u_j)_+\le(m/r)e$. Convexity and its supporting tangent at
$u_j$ therefore give $F_j(u)\ge S_j-P_j(u-u_j)_+$, including
$u\le u_j$ by the constrained minimality just established.
By (15.9), $c^{-2}=1+O_R(a^{-1/2})$ and
$\delta^{-2}\ge\eta^2(1-O_R(a^{-1/4}))$. Consequently

$$
\frac{\Lambda-(m/r)P_j}{a^3}
\ge3z-2-(z-2)-O_R(a^{-1/4})
=2z-O_R(a^{-1/4})\ge1
\tag{15.24}
$$

eventually. This proves (15.19) from (15.21).

If $H=S_j$, then $e=0$, so every positive-mass type meeting $D$
is a singleton, and $u\le u_j$. The strict scalar minimum and
(15.21) force $u=u_j$, equal tail marginals $t_k=u_j/n$, and equal
core marginals $y_i=(a-u_j)/m$. With only tail singletons,
$\Delta_i=0$ and the contribution to $R_i$ on $A$ is $c_mu_j$.
The remaining nonnegative term in (15.20) is
$\mathbb E[\sum_i\rho_i/y_i^2;A^c]$, which must vanish.
The only integer zeros of $Q(L)$ on a nonempty core type are
$L=r,m$. Thus the core types are $C$ and $C\setminus\{i\}$.
Normalization and the original mean force their total masses to be
$1-j+(m-2)u_j$ and $j-ru_j=0$, respectively. The full-core mass is
$(a-1)/r=1-u_j>0$. These are exactly (15.2) at the cap.
Conversely this law has energy $S_j$, as verified below. ∎

**Theorem 15.5 (The unrestricted uniform finite envelope and every
equality law).** For every fixed finite $R>0$ there is $A_R$ such
that for all integers $a\ge A_R$, $1\le h\le R\sqrt a$,

$$
M(a,h)=\min_{1\le j\le h}\mu_j.
\tag{15.25}
$$

This value is attained. Every attaining law, up to arbitrary label
permutations, is exactly $x^{j,p_j}$ from (15.2) for a branch $j$
attaining the displayed minimum. Each $p_j$ is unique. There are
no other equality laws, and no nontrivial convex combination of
distinct minimizing laws is minimizing.

One may take the finite active-index bound
$J_R=\lceil4((\max\{R,4\})^2+10)\rceil$. Every winning $j$ is at
most $J_R$, and every winning $j\ge3$ satisfies $p_j=u_j$.
Equivalently, with the minimum of an empty set interpreted as $+\infty$,

$$
M(a,h)=\min\left\{m_1(a,h),m_2(a,h),
                 \min_{3\le j\le\min(h,J_R)}S_j\right\}.
\tag{15.26}
$$

The following two exact descriptions overlap:

$$
\begin{array}{ll}
1\le h\le4\sqrt a:&M=\min\{m_1,m_2\},\\
(7/2)\sqrt a\le h\le R\sqrt a:&M=\min_{1\le j\le J_R}S_j.
\end{array}
\tag{15.27}
$$

The second line is used only when its range is nonempty; then
$h\ge J_R$ for the chosen threshold. On the overlap the unique
winning index is $2$, and $m_2=S_2<m_1$. Below it the first two
branches retain exactly their published constrained competition.

**Proof.** For every $1\le j\le h$, $\ell_j<u_j<1$, with
$u_j-\ell_j=(a-1)/(r(m-2))$ for $j\ge2$. The masses in (15.2)
are nonnegative on their stated intervals. If $z_0$ is its full-core
mass and $w_0$ its total missing-one mass, then

$$
p+z_0+w_0=1,\qquad p+mz_0+rw_0=a,\qquad
y_k=p/n\ (k\in D),\quad y_i=(a-p)/m\ (i\in C).
$$

All these actual marginals are positive. Its energy is
$n^2/p+(m^3z_0+r^3w_0)/((a-p)/m)^2=F_j(p)$.
Equation (15.22) proves strict convexity on every branch. Compactness
for $j\ge2$, and divergence at zero for $j=1$, prove existence and
uniqueness of $p_j$. Thus every $\mu_j$ is attained by an original
admissible law, giving all required upper bounds.

Apply Lemmas 15.2--15.4 with $R$ replaced by $\max\{R,4\}$ and
$J=J_R$. On their high-ratio range, a law outside $H\le U$ already
has $H>U$. A law inside it has a surviving $j$ and satisfies
$H\ge S_j+a^3e\ge U$. The comparison laws attain $U$, so $M=U$.
Equality forces $S_j=U$ and the exact cap law by Lemma 15.4.
Conversely every cap law with $S_j=U$ attains $M$.

For $1\le h\le4\sqrt a$, Theorem 14.5, with fixed upper ratio
$4<2\sqrt6$, gives the first line of (15.27) and every equality law
there. The intervals $[1,4\sqrt a]$ and $[(7/2)\sqrt a,R\sqrt a]$
leave no gap, including bounded $h$ and $h/\sqrt a\to0$.
Together these arguments classify every equality law on the full
range without assuming the existence of a global optimizer.

For completeness this also excludes hidden winners of the longer
envelope. Uniformly over every $j\le h\le R\sqrt a$ and $p\in I_j$,
the comparison laws have core marginals at least
$(a-1)/(a+h)>1/2$ and tail marginals at most
$p\le h/(a+h-1)<1/2$, eventually. Thus their number of marginals
exceeding $1/2$ is exactly $a+j$. If any $\mu_j=M$, its attaining
comparison law must be one of the equality laws already classified.
On the lower interval this forces $j=1,2$; on the higher interval
it forces $j\le J_R$ and the cap parameter, which is also fixed by
its total singleton mass. This proves (15.25), the index bound and
the cap assertion. All terms in (15.26) are admissible comparison
energies, and the classified law occurs among them, proving its
equivalence. The overlap assertion follows also from the ordered
crossings in Proposition 15.6: its first crossing is below
$(7/2)\sqrt a$ and its second above $4\sqrt a$ eventually.

At $p=u_j$ every missing-one mass vanishes, while the full-core mass
is $(a-1)/r>0$. At $p=\ell_j$ for $j\ge2$, the full-core mass
vanishes and each missing-one mass is $(a-1)/(m(m-2))>0$.
Both endpoint laws have positive actual marginals, so none was
discarded from comparison. A winning $j=2$ cannot be at the lower
endpoint: in the lower window Theorem 14.5 gives $ap_2\ge3/2$
whenever it wins, and in the higher window it is capped. No
$j\ge3$ lower endpoint wins either. For $j=1$, $p=0$ is excluded
and its full-core mass $(a-1)p$ is positive. The unique scalar
minimum is at an allowed lower endpoint if its derivative is
nonnegative there, at the cap if its derivative is nonpositive
there, and otherwise at its unique interior derivative zero.
Zero derivative at an endpoint introduces no additional scalar
minima. These statements include all vanishing type masses.

The lower-window exclusion of nontrivial minimizing mixtures is
already part of Theorem 14.5. In the higher window every minimizing
law has positive singleton masses exactly on its tail and one
positive nonsingleton mass, exactly its full core. If a convex
combination of minimizing laws were itself minimizing, every
component with positive weight would have its full-core type in
the resulting support. The resulting law has just one nonsingleton
type, so all such cores must be that same set. Their index and cap
parameter then agree, and their singleton masses agree individually.
All components are the identical law. This also treats mixtures
of the two cap classes at an exact tie. Arbitrary permutations of
labels are included, since all partitions were allowed, and every
equality partition is recovered from its actual marginals. ∎

**Proposition 15.6 (Ordered exact cap competition and its crossings).**
Let $t=h+1$, $a\ge4$ and, for an integer $j\ge1$, set

$$
\begin{gathered}
D_j(a)=\frac{4(a+j)^3+3(a+j)^2+(a+j)}{a-1}+a+2j,\\
\tau_j(a)=\frac{j(j+1)}{a-1}
 \left(\sqrt{1+\frac{(a-1)D_j(a)}{j(j+1)}}-1\right)-1.
\end{gathered}
\tag{15.28}
$$

The polynomial continuation of the cap energies has signed adjacent
differences

$$
\Delta_j:=S_{j+1}-S_j
=D_j(a)-2t-\frac{(a-1)t^2}{j(j+1)}.
\tag{15.29}
$$

For $h\ge0$, this difference is positive, zero or negative as
$h<\tau_j$, $h=\tau_j$ or $h>\tau_j$, respectively. The thresholds
are strictly increasing in $j$. The cap sequence is strictly convex
in its integer index. Therefore its minimum on any consecutive
finite index interval has either one winning index or exactly two
adjacent winning indices; at $h=\tau_j$ those indices are $j,j+1$
whenever both belong to that interval. There are no triple ties.

For each fixed finite index range, uniformly in that range,

$$
\frac{\tau_j(a)}{\sqrt a}=2\sqrt{j(j+1)}+O(a^{-1/2}).
\tag{15.30}
$$

In the high-ratio interval of Theorem 15.5, this is the exact
competition for $M$. More explicitly, set $\tau_0=-\infty$ and
$\tau_{J_R}=+\infty$ only as endpoint conventions for this finite
competition. Index $j$ wins exactly when
$\tau_{j-1}\le h\le\tau_j$, with the natural endpoint omissions.
Each real crossing $\tau_j$, $2\le j<J_R$, lying in the claimed
high-ratio interval is an actual crossing of the full unrestricted
value whenever $h=\tau_j$ is an admissible integer. If it is not an
integer, the same threshold gives the exact switch between integer
budgets. A threshold outside the interval makes no assertion of a
crossing inside it. On the lower interval all winning indices are
$1,2$ as in Theorem 14.5, so globally there are still at most two
adjacent winning indices, with all their equality classes included.

**Proof.** Write the tail term as

$$
\frac{(t-j)^2(a+j-1)}j
=\frac{(a-1)t^2}{j}-2(a-1)t+(a-1)j+t^2-2tj+j^2.
$$

The adjacent difference of the core term, with $m=a+j$, is
$\{(m+1)^3m-m^3(m-1)\}/(a-1)=(4m^3+3m^2+m)/(a-1)$.
Their sum is (15.29). Since $D_j(a)>0$, the quadratic in $t$ is
strictly decreasing for $t\ge0$ and has one positive root, precisely
$t=\tau_j+1$. Its sign gives the asserted comparison for $h\ge0$.
Moreover

$$
\Delta_{j+1}-\Delta_j
=\frac{12m^2+18m+8}{a-1}+2
 +\frac{2(a-1)t^2}{j(j+1)(j+2)}>0.
\tag{15.31}
$$

This proves strict convexity and shows that the positive roots in
$t$ strictly increase: at the root of $\Delta_j$, $\Delta_{j+1}>0$
and has its zero later. At a root, differences before it are strictly
negative and those after it strictly positive. This proves the
global finite-sequence tie and winner assertions, not merely equality
of the two compared terms.

For fixed $j$, $D_j(a)=4a^2+O_j(a)$. Inserting this into the positive
root in (15.28) gives (15.30), with a bounded error before division
by $\sqrt a$. All constants are uniform for finitely many indices.
In particular $\tau_1/\sqrt a\to2\sqrt2<7/2$ and
$\tau_2/\sqrt a\to2\sqrt6>4$. This proves the overlap assertion in
Theorem 15.5. Within its higher interval, (15.27) transfers the exact
finite competition to $M$, and the endpoint conventions give its
winner test. Every cap used there is admissible because $h\ge J_R$.
For bounded indices, the thresholds themselves also exceed the
corresponding indices eventually, by (15.30). The restrictions on
which thresholds lie in the interval therefore preserve both the
original integer domain and the fixed upper ratio. ∎

**Corollary 15.7 (Scope of the uniform conclusion).** The finite-value
and exact-equality parts of Open problem 7.3 are resolved on every
fixed range $1\le h\le R\sqrt a$ for sufficiently large $a$ depending
on that fixed $R$. The result does not assert uniformity for a
growing $R$, a least sufficient threshold, a classification of small
$a$, a near-equality rate, or an exact connected finite-graph optimum.

**Proof.** These are precisely the quantifiers of Theorem 15.5.
Its proof uses the original common law, all nonempty cardinalities,
zero type masses, arbitrary positive marginals and arbitrary
incidence support throughout. Its new lower-bound input is the
uniform active-index margin (15.3), which makes the bounded-index
residual (15.8) and strict payment (15.19) simultaneous over every
fixed number of higher phases. Theorem 7.2 supplies the scalar
localization, and Theorem 14.5 supplies the overlapping lower window;
the cap evaluations alone would not yield this conclusion.

The theorem and residual estimates here are repo-derived. Finite
Jensen and its supporting-tangent inequality are used only after
the explicit second derivatives (15.22) and $f_u''$ establish their
hypotheses; see S. Boyd and L. Vandenberghe, *Convex Optimization*,
§§3.1.3 and 3.1.8,
[author text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf).
The expectation certificate in (15.15) is proved directly and uses
no strong duality or convexity of $H$ in the law. The graph sources
and normalization cited in Section 14 remain as stated there;
none supplies the unrestricted growing-surplus equality theorem.
The possible full-text overlap with Zhao--Zhao, DOI
[10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26),
remains unassessed. No worldwide priority assertion is made. ∎

## 追加锚（本行以下为增补区）
