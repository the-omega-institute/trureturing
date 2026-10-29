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
