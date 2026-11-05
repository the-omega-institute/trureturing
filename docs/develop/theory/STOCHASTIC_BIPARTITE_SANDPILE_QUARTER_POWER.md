# A quarter-power law for labelled stochastic bipartite sandpiles

## 1. The counting measure and its geometric reference

**Definition 1.1 (Labelled configurations).** Let $m\ge2$, $n\ge1$, and $k=m-1$ be integers. The two parts of $K_{m,n}$ are $\{s,a_1,\ldots,a_k\}$ and $\{b_1,\ldots,b_n\}$; $s$ is the sink. Fix any $p\in(0,1)$. In the stochastic sandpile model, an unstable vertex sends a grain independently to each neighbour with probability $p$, retaining the other grains; grains reaching $s$ disappear. Grain additions have positive probability at every non-sink vertex. Write $\operatorname{Sto}(K_{m,n})$ for the recurrent stable configurations of this model. In the zero-based height convention a stable configuration is

$$
(A,B)\in\{0,\ldots,n-1\}^{k}\times\{0,\ldots,k\}^{n}.
$$

Define its uniform labelled counting proportion by

$$
\rho_{m,n}=\frac{|\operatorname{Sto}(K_{m,n})|}{n^{k}(k+1)^n}.
\tag{1.1}
$$

Equivalently, sample all $A_i$ uniformly from $\{0,\ldots,n-1\}$ and all $B_j$ uniformly from $\{0,\ldots,k\}$, independently. Then $\rho_{m,n}$ is the probability of recurrence. This is a counting probability on stable configurations.

The conventions in (1.1) are those of Alofi and Dukes, *A note on the lacking polynomial of the complete bipartite graph*, [arXiv:2411.02667v1](https://arxiv.org/abs/2411.02667v1), Definition 1, Theorem 2, and Proposition 4. In the positive height convention of Chan, Marckert, and Selig, *A natural stochastic extension of the sandpile model on a graph*, [arXiv:1209.2038v1](https://arxiv.org/abs/1209.2038v1), Theorem 3.2 and its proof in Section 4.1, the change is $\eta(v)=c(v)+1$. Their stability range $1\le\eta(v)\le d(v)$ becomes $0\le c(v)<d(v)$, and their compatibility inequality becomes $\operatorname{in}_O(v)\ge d(v)-c(v)$. Existence of such an orientation characterizes recurrence for every $0<p<1$; thus the set counted in (1.1) is independent of the particular $p$ in this interval.

**Definition 1.2 (Reference polytope).** For $1\le r\le k$ put

$$
f_r=\frac{r(r+1)}{2(k+1)},\qquad
P_k=\left\{u\in[0,1]^k:
 \sum_{i\in I}u_i\ge f_{|I|}\text{ for every }\varnothing\ne I\subseteq[k]\right\},
\qquad w_k=\operatorname{Vol}_k(P_k),
\tag{1.2}
$$

where $\operatorname{Vol}_k$ is Euclidean Lebesgue volume. In particular,

$$
\frac{f_r}{r}\le\frac12,\qquad
[1/2,1]^k\subseteq P_k,\qquad w_k\ge2^{-k}>0.
\tag{1.3}
$$

The [bipartite half bound](../../../D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.lean), with equality exactly at $m=2$, concerns the same counting measure (1.1). The comparison below estimates that measure relative to (1.2) when both dimensions vary.

## 2. A finite relative comparison in the original labelled model

**Theorem 2.1 (Actual-count transfer).** For all integers $k\ge1$ and $n\ge4096$, with the sink and stochastic parameter as in Definition 1.1,

$$
1-\frac{8k}{\sqrt n}-\frac{2k}{n}
\ \le\ \frac{\rho_{k+1,n}}{w_k}
\ \le\ \exp\left(\frac{8k}{\sqrt n}+\frac{k^2}{2n}\right).
\tag{2.1}
$$

Consequently the following comparison holds with the same universal quantifiers:

$$
1-\frac{8k}{\sqrt n}-\frac{2k}{n}
\ \le\ \frac{\rho_{k+1,n}}{w_k}
\ \le\ \exp\left(\frac{16k}{\sqrt n}+\frac{2k^2}{n}+\frac{4k}{n}\right)
       +\exp\left(k\log 2-\frac n{32}\right).
\tag{2.2}
$$

**Proof.** The forbidden-subconfiguration characterization of Selig and Zhu, *Abelian and stochastic sandpile models on complete bipartite graphs*, [arXiv:2409.11811v1](https://arxiv.org/abs/2409.11811v1), Theorem 2.1, gives

$$
(A,B)\in\operatorname{Sto}(K_{k+1,n})
\quad\Longleftrightarrow\quad
\sum_{i\in I}A_i+\sum_{j\in J}B_j\ge |I|\,|J|
\quad(I\subseteq[k],\ J\subseteq[n]).
\tag{2.3}
$$

Their graph $K^0_{a,n}$ has $a$ non-sink top vertices and one additional top sink. Here $a=k$, so $K^0_{k,n}=K_{k+1,n}$, $c^t_i=A_i$, and $c^b_j=B_j$. The degrees are $n$ and $k+1$, respectively. Their Theorem 2.1 is a statement for labelled configurations; the sorted formulation in their Theorem 2.2 is an equivalent test, not a replacement counting space. Alternatively, (2.3) is Selig's induced-subgraph criterion, *The stochastic sandpile model on complete graphs*, [arXiv:2209.07301v2](https://arxiv.org/abs/2209.07301v2), Theorem 6(iii): the induced non-sink graph on $I\cup J$ has exactly $|I||J|$ edges. Selig uses compatible orientations with in-degrees bounded above by the heights; reversing every edge gives the out-degree convention equivalent to Definition 1.1. Only this general-graph criterion, not a complete-graph enumeration, is used here.

Fix $I$ of cardinality $r$. Maximizing $r|J|-\sum_{j\in J}B_j$ over all $J$ includes precisely the positive summands $r-B_j$; summands equal to zero are immaterial. Thus (2.3) is equivalent to

$$
\sum_{i\in I}A_i\ge H_r(B),\qquad
H_r(B):=\sum_{j=1}^{n}(r-B_j)_+,
\quad\varnothing\ne I\subseteq[k],\ r=|I|.
\tag{2.4}
$$

The empty sets in (2.3) impose only nonnegativity. Since $B_j$ is uniform on $\{0,\ldots,k\}$,

$$
\mathbb E(r-B_j)_+
=\frac{1}{k+1}\sum_{b=0}^{r-1}(r-b)=f_r.
\tag{2.5}
$$

No multiplicities have been removed: each labelled configuration has probability $n^{-k}(k+1)^{-n}$, and (2.4) is an event, irrespective of the number of its compatible orientations.

Let

$$
F_n(t)=\frac1n\sum_{j=1}^{n}\mathbf1_{\{B_j<t\}},\qquad
F(t)=\frac{t}{k+1},\qquad
D=\max_{t\in\{0,1,\ldots,k+1\}}|F_n(t)-F(t)|.
\tag{2.6}
$$

The identity $(r-b)_+=\sum_{t=1}^{r}\mathbf1_{\{b<t\}}$ yields the simultaneous bounds

$$
\left|\frac{H_r(B)}n-f_r\right|\le rD
\quad(1\le r\le k).
\tag{2.7}
$$

All these thresholds depend on the same vector $B$.

We will use the classical symmetrization, maximal, and bounded-difference estimates, with their constants justified here. They are intermediate probability tools; see Doob, *Stochastic Processes*, Chapter VII; Hoeffding, *Probability inequalities for sums of bounded random variables*, [DOI:10.1080/01621459.1963.10500830](https://doi.org/10.1080/01621459.1963.10500830); and McDiarmid, *On the method of bounded differences*, [DOI:10.1017/CBO9781107359949.008](https://doi.org/10.1017/CBO9781107359949.008).

Take independent copies $B'_1,\ldots,B'_n$ and independent uniform signs $\varepsilon_1,\ldots,\varepsilon_n$. Conditional Jensen, followed by independent exchanges of $B_j$ and $B'_j$, and then the triangle inequality, gives

$$
\begin{aligned}
\mathbb E D
&\le \mathbb E\max_t\left|\frac1n\sum_j
 (\mathbf1_{\{B_j<t\}}-\mathbf1_{\{B'_j<t\}})\right|\\
&=\mathbb E\max_t\left|\frac1n\sum_j\varepsilon_j
 (\mathbf1_{\{B_j<t\}}-\mathbf1_{\{B'_j<t\}})\right|\\
&\le2\mathbb E\max_t\left|\frac1n\sum_j\varepsilon_j\mathbf1_{\{B_j<t\}}\right|
\le\frac4{\sqrt n}.
\end{aligned}
\tag{2.8}
$$

For the last step, condition on $B$, order its coordinates, and break ties by labels. Each threshold selects a prefix of this order. Conditional on $B$, the reordered signs remain independent uniform signs. Writing $S_j=\sum_{i=1}^{j}\varepsilon_i$ and $M=\max_{0\le j\le n}|S_j|$, their maximal inequality gives $\mathbb E M^2\le4n$, whence $\mathbb EM\le2\sqrt n$. For completeness, the stopping-time inequality for the submartingale $|S_j|$ is

$$
t\,\Pr(M\ge t)\le\mathbb E\bigl[|S_n|\mathbf1_{\{M\ge t\}}\bigr].
$$

It follows by partitioning $\{M\ge t\}$ according to the first crossing time and using $\mathbb E(|S_n|\mid\varepsilon_1,\ldots,\varepsilon_j)\ge|S_j|$. Integrating over $t>0$ gives $\mathbb EM^2\le2\mathbb E(M|S_n|)\le2\sqrt{n\mathbb EM^2}$, proving the stated bound. Ties in $B$ merely restrict the prefixes over which the maximum is taken.

Changing one $B_j$ changes $D$ by at most $1/n$. Its Doob martingale obtained by revealing the independent $B_j$ therefore has each conditional increment in an interval of length at most $1/n$: the conditional expectations corresponding to any two values of that coordinate differ by at most $1/n$. Hoeffding's elementary conditional exponential estimate gives, for $\lambda\ge0$,

$$
\mathbb E e^{\lambda(D-\mathbb ED)}\le e^{\lambda^2/(8n)}.
\tag{2.9}
$$

Indeed, if a centered variable is in an interval of length $c$, the second derivative of its log moment generating function is its variance under an exponential tilt, at most $c^2/4$. The latter follows by bounding squared distance from the interval midpoint by $c^2/4$. Integrate twice from zero to obtain the log moment bound $\lambda^2c^2/8$. Apply it conditionally to each martingale increment and iterate, summing $n$ terms with $c=1/n$. Markov's inequality and optimization at $\lambda=4nt$ also yield

$$
\Pr(D-\mathbb ED\ge t)\le e^{-2nt^2}\qquad(t\ge0).
\tag{2.10}
$$

We next compare the actual conditional count, rather than a different distribution of heights, with $w_k$. Define

$$
q(B)=\Pr\bigl((A,B)\in\operatorname{Sto}(K_{k+1,n})\mid B\bigr).
\tag{2.11}
$$

Let $U_1,\ldots,U_k$ be independent uniform variables in $[0,1)$, independent of $B$, and set $A_i=\lfloor nU_i\rfloor$. This gives exactly the uniform labelled heights of Definition 1.1. Therefore $q(B)$ is the Lebesgue measure of the set of $u\in[0,1)^k$ for which the integer inequalities (2.4) hold with $A_i=\lfloor nu_i\rfloor$.

For any $\delta\ge0$ put

$$
R_\delta=\left\{u\in[0,1]^k:
\sum_{i\in I}u_i\ge f_{|I|}-|I|\delta
\quad(\varnothing\ne I\subseteq[k])\right\}.
$$

By (2.7) and $\lfloor nu_i\rfloor/n\le u_i$, the set measured by $q(B)$ is contained in $R_D$. The affine map

$$
T_\delta(u)=\frac{u+2\delta\mathbf1}{1+2\delta}
$$

maps $R_\delta$ into $P_k$. To see this, it maps the cube into the cube and, for $r=|I|$,

$$
\sum_{i\in I}T_\delta(u)_i
\ge\frac{f_r+r\delta}{1+2\delta}\ge f_r,
$$

where the final inequality is $r\ge2f_r$. Its determinant is $(1+2\delta)^{-k}$. Consequently, for every $B$, without an exceptional set,

$$
q(B)\le\operatorname{Vol}_k(R_D)
\le(1+2D)^k w_k\le e^{2kD}w_k.
\tag{2.12}
$$

For the lower comparison put $\delta=D+1/n$. If $2\delta<1$, the map

$$
L_\delta(u)=(1-2\delta)u+2\delta\mathbf1
$$

maps $P_k$ into the cube and satisfies

$$
\begin{aligned}
\sum_{i\in I}L_\delta(u)_i
&\ge f_r+2\delta(r-f_r)\ge f_r+r\delta,\\
\frac1n\sum_{i\in I}\lfloor nL_\delta(u)_i\rfloor
&\ge f_r+rD\ge\frac{H_r(B)}n.
\end{aligned}
\tag{2.13}
$$

Thus its image belongs to the event defining $q(B)$, up to the cube boundary of Lebesgue measure zero. The floor loses at most $r/n$, which accounts for the entire rounding term. The determinant gives

$$
q(B)\ge(1-2\delta)^k w_k\ge(1-2k\delta)w_k.
$$

At $2\delta=1$ the same lower bound follows from nonnegativity; when $2\delta>1$, $1-2k\delta\le0$, so nonnegativity again suffices. Hence for every $B$,

$$
\frac{q(B)}{w_k}\ge1-2kD-\frac{2k}{n}.
\tag{2.14}
$$

Now $\rho_{k+1,n}=\mathbb E_B q(B)$. Averaging (2.14) and applying (2.8) proves the lower bound in (2.1). Averaging (2.12), and using (2.9) at $\lambda=2k$, proves

$$
\frac{\rho_{k+1,n}}{w_k}
\le\mathbb E e^{2kD}
\le\exp\left(2k\mathbb ED+\frac{k^2}{2n}\right)
\le\exp\left(\frac{8k}{\sqrt n}+\frac{k^2}{2n}\right).
\tag{2.15}
$$

In particular, the larger exponent and positive extra term on the right of (2.2) imply (2.2).

One can also account explicitly for the exceptional-event term in that bound. For $E=\{D>1/4\}$, $n\ge4096$ gives $\mathbb ED\le1/16$, so (2.10) implies

$$
\Pr(E)\le \exp\left(-2n(3/16)^2\right)
\le e^{-n/32}.
$$

Since $q\le1$ and $w_k\ge2^{-k}$,

$$
\frac{\mathbb E[q(B)\mathbf1_E]}{w_k}
\le\exp\left(k\log2-\frac n{32}\right).
\tag{2.16}
$$

The contribution from $E^c$ is at most the right side of (2.15), by the same global bound (2.12). Thus this decomposition also proves (2.2) in the original labelled model. No conditional relative limit for each fixed $B$ is needed. $\square$

## 3. The simultaneous count asymptotic and its constant

**Theorem 3.1 (Quarter-power count).** For every sequence of integer pairs $(m_\ell,n_\ell)$ satisfying

$$
m_\ell\ge2,\quad n_\ell\ge1,\quad
k_\ell:=m_\ell-1\longrightarrow\infty,\qquad
\frac{n_\ell}{k_\ell^2}\longrightarrow\infty,
$$

and for every $0<p<1$,

$$
\rho_{m_\ell,n_\ell}\sim Ck_\ell^{-1/4},\qquad
C=\frac{e^{-1/2}\Gamma(3/4)}{2^{1/4}\sqrt\pi}.
\tag{3.1}
$$

Equivalently, in the same simultaneous limit,

$$
|\operatorname{Sto}(K_{m_\ell,n_\ell})|
=(C+o(1))\,n_\ell^{k_\ell}(k_\ell+1)^{n_\ell}k_\ell^{-1/4}.
\tag{3.2}
$$

**Proof.** We first evaluate the deterministic geometric intermediate input $w_k$. Write $\mathcal P(d,N)$ for the partial permutohedron, the convex hull of vectors in $\{0,\ldots,N\}^d$ with distinct nonzero entries. The inequality description in Behrend, Castillo, Chavez, Diaz-Lopez, Escobar, Harris, and Insko, *Partial permutohedra*, [arXiv:2207.14253v3](https://arxiv.org/abs/2207.14253v3), Proposition 2.8, identifies

$$
\mathcal P(k,k)=\left\{x\in\mathbb R_{\ge0}^{k}:
 \sum_{i\in I}x_i\le\frac{r(2k+1-r)}2,
 \quad\varnothing\ne I\subseteq[k],\ r=|I|\right\}.
\tag{3.3}
$$

At $(d,N)=(k,k)$, their facet list includes every nonempty cardinality: $r\le k-1$ and the total-set cardinality $r=k$. For $k=1$ (3.3) is simply $[0,1]$.

The affine substitution $x_i=(k+1)(1-u_i)$ takes (1.2) to (3.3), because

$$
r(k+1)-(k+1)f_r=\frac{r(2k+1-r)}2.
$$

Conversely, the singleton inequalities in (3.3) imply $x_i\le k$, so $u_i=1-x_i/(k+1)$ is in $[0,1]$; this proves equality of the two transformed sets, including their cube constraints. The absolute determinant is $(k+1)^k$, and hence

$$
w_k=\frac{\operatorname{Vol}_k(\mathcal P(k,k))}{(k+1)^k}.
\tag{3.4}
$$

There is no restriction of these volumes to a sorted chamber, and no division by a permutation orbit. Hanada, Lentfer, and Vindas-Melendez, *Generalized parking function polytopes*, [arXiv:2212.06885v2](https://arxiv.org/abs/2212.06885v2), Proposition 3.16 and its vertex-translation proof, give the further identification

$$
\mathcal P(k,k)+\mathbf1=X_k(2,1).
\tag{3.5}
$$

For $k=1$ this is the interval $[1,2]$. Here $X_k(2,1)$ uses parking parameters $(2,1,\ldots,1)$. In their general correspondence $\mathcal P(d,N)+\mathbf1=X_d(N-d+2,1)$, it is $(d,N)=(k,k)$, not $(k,n)$: the sandpile large-part size is unrelated to the bound $N$.

We use the proved finite volume formula of *Partial permutohedra*, Theorem 4.5, equation (4.3), with its proof in Sections 4.1–4.2. In that formula $v(d,N)$ is normalized volume, so $v(d,N)=d!\operatorname{Vol}_d(\mathcal P(d,N))$. The hypothesis $N\ge d-1$ holds at $(k,k)$. Specializing the formula and dividing by $k!$ gives

$$
\operatorname{Vol}_k(\mathcal P(k,k))
=-\frac1{2^k}\sum_{j=0}^{k}\binom{k}{j}(2j-3)!!(2k+1)^{k-j},
\tag{3.6}
$$

where $(-3)!!=-1$ and $(-1)!!=1$. These are cited finite geometric inputs inside the count proof.

Here is a direct integral evaluation of their asymptotic, avoiding subtraction of nearly equal asymptotic expressions. Put $a=k+1/2$. The $j=0$ term in (3.6) is $a^k$; for $j\ge1$,

$$
\frac{(2j-3)!!}{2^j}
=\frac{\Gamma(j-1/2)}{2\sqrt\pi}.
$$

Use the Gamma integral on the finite sum over $j\ge1$ to obtain

$$
\operatorname{Vol}_k(\mathcal P(k,k))
=a^k-\frac1{2\sqrt\pi}\int_0^\infty
 e^{-t}\bigl((a+t)^k-a^k\bigr)t^{-3/2}\,dt.
\tag{3.7}
$$

Each term is integrable at both endpoints. Integration by parts gives

$$
\int_0^\infty(1-e^{-t})t^{-3/2}\,dt
=2\int_0^\infty e^{-t}t^{-1/2}\,dt=2\sqrt\pi.
$$

Combining this identity with (3.7) and (3.4) yields the exact positive integral

$$
w_k=\frac{(a/(k+1))^k}{2\sqrt\pi}
 \int_0^\infty\left[1-e^{-t}(1+t/a)^k\right]t^{-3/2}\,dt.
\tag{3.8}
$$

The bracket is nonnegative since $k\log(1+t/a)\le kt/a<t$. After $t=\sqrt{k}\,x$, define

$$
h_k(x)=\sqrt{k}\,x-k\log(1+\sqrt{k}\,x/a).
$$

For each fixed $x>0$, Taylor's formula gives $h_k(x)\longrightarrow x^2/2$. Explicitly, with $y=\sqrt{k}\,x/a$, the linear remainder is $\sqrt{k}\,x/(2a)\to0$, the quadratic term is $k^2x^2/(2a^2)\to x^2/2$, and the remaining term is $O_x(k^{-1/2})$. Also, $\log(1+y)\ge y-y^2/2$ for $y\ge0$; this follows by differentiating the difference, whose derivative is $y^2/(1+y)\ge0$. Therefore

$$
0\le h_k(x)\le\frac{x}{2\sqrt{k}}+\frac{x^2}{2}
\le\frac{x+x^2}{2}.
$$

It follows that

$$
0\le(1-e^{-h_k(x)})x^{-3/2}
\le\min\{1,(x+x^2)/2\}\,x^{-3/2}.
$$

The right side is integrable near zero and infinity. Dominated convergence thus proves

$$
\begin{aligned}
k^{1/4}\int_0^\infty
 \left[1-e^{-t}(1+t/a)^k\right]t^{-3/2}\,dt
&\longrightarrow\int_0^\infty(1-e^{-x^2/2})x^{-3/2}\,dx\\
&=2\int_0^\infty x^{1/2}e^{-x^2/2}\,dx
=2^{3/4}\Gamma(3/4).
\end{aligned}
\tag{3.9}
$$

The first equality on the second line is integration by parts; both boundary terms vanish. The second follows from $y=x^2/2$. Finally,

$$
\left(\frac{k+1/2}{k+1}\right)^k
=\left(1-\frac1{2(k+1)}\right)^k\longrightarrow e^{-1/2}.
$$

Equations (3.8)–(3.9) give

$$
w_k\sim\frac{e^{-1/2}\Gamma(3/4)}{2^{1/4}\sqrt\pi}\,k^{-1/4}.
\tag{3.10}
$$

The finite volume formula, parking-polytope correspondence, Gamma identities, and this ordinary asymptotic evaluation are intermediate inputs to (3.1); the additional inference about actual counts is supplied by Theorem 2.1.

Indeed, along every sequence in the theorem, $n_\ell\to\infty$, so eventually $n_\ell\ge4096$, and

$$
\frac{k_\ell}{\sqrt{n_\ell}}\longrightarrow0,\qquad
\frac{k_\ell^2}{n_\ell}\longrightarrow0,\qquad
\frac{k_\ell}{n_\ell}\longrightarrow0.
$$

The two bounds in (2.1) squeeze $\rho_{m_\ell,n_\ell}/w_{k_\ell}$ to $1$. Combining this with (3.10) proves (3.1), and multiplying by the exact denominator in (1.1) proves (3.2). If one uses (2.2) instead, its exceptional term also tends to zero, since $k_\ell\log2-n_\ell/32\to-\infty$. Every limit here is along the given pair sequence. $\square$

## 4. Exact residual counts and boundary instances

**Definition 4.1 (Histogram residual).** For integers $k,n\ge1$ and a vector $h=(h_0,\ldots,h_k)\in\mathbb Z_{\ge0}^{k+1}$ with $\sum_bh_b=n$, define

$$
Q_{k,n}(h)=\frac1{n^k}\sum_{a\in\{0,\ldots,n-1\}^k}
 \prod_{\varnothing\ne I\subseteq[k]}
 \mathbf1_{\left\{\sum_{i\in I}a_i\ge
    \sum_{b=0}^{|I|-1}(|I|-b)h_b\right\}},
\tag{4.1}
$$

and the relative residual

$$
\mathcal R_{k,n}=\frac1{w_k(k+1)^n}
 \sum_{\substack{h\in\mathbb Z_{\ge0}^{k+1}\\\sum_bh_b=n}}
 \frac{n!}{\prod_{b=0}^{k}h_b!}\,Q_{k,n}(h)-1.
\tag{4.2}
$$

**Proposition 4.2 (Exact residual and nonuniform conditioning).** For all integers $k,n\ge1$,

$$
\rho_{k+1,n}=\frac1{(k+1)^n}
 \sum_{\substack{h\in\mathbb Z_{\ge0}^{k+1}\\\sum_bh_b=n}}
 \frac{n!}{\prod_{b=0}^{k}h_b!}\,Q_{k,n}(h),
\qquad
\mathcal R_{k,n}=\frac{\rho_{k+1,n}}{w_k}-1.
\tag{4.3}
$$

The conditional probabilities in (2.11) satisfy

$$
q(0,\ldots,0)=0,\qquad q(k,\ldots,k)=1.
\tag{4.4}
$$

Moreover,

$$
\rho_{k+1,1}=\frac1{k+1},\qquad
\frac{\rho_{k+1,1}}{w_k}\sim C^{-1}k^{-3/4}\longrightarrow0.
\tag{4.5}
$$

**Proof.** If $h_b$ is the number of indices $j$ with $B_j=b$, then $H_r(B)=\sum_{b=0}^{r-1}(r-b)h_b$. Conditional on this histogram, (2.4) says exactly that the probability over the labelled $A$ coordinates is (4.1). There are $n!/\prod_bh_b!$ labelled $B$ vectors with that histogram, each with probability $(k+1)^{-n}$. Summing proves (4.3), retaining every labelled multiplicity even when heights coincide.

If all $B_j=0$, the singleton constraints in (2.4) require each $A_i\ge n$, impossible for a stable height. If all $B_j=k$, every $H_r(B)=0$ for $r\le k$, and all stable $A$ satisfy (2.4). Each of these two conditioning vectors has positive probability $(k+1)^{-n}$, proving (4.4) without any uniform conditional convergence assertion.

For $n=1$ stability forces all $A_i=0$. Taking $I=[k]$ in (2.4) then forces $B_1=k$, which also suffices. There is exactly one recurrent configuration among the $k+1$ stable configurations. This proves the first equality in (4.5); the asymptotic follows from (3.10). $\square$

**Definition 4.3 (Remaining asymptotic problem).** For a sequence with $k\to\infty$ but without $n/k^2\to\infty$, the exact relative-transfer problem is the asymptotic evaluation of $\mathcal R_{k,n}$ in (4.2). Theorem 2.1 gives a vanishing bound in the sufficient regime of Theorem 3.1. Its error bounds do not determine $\mathcal R_{k,n}$ when $n\asymp k$ or, in general, when $k/\sqrt n$ does not tend to zero. Equation (4.5) rules out extending (3.1) to all sequences with $k\to\infty$ and arbitrary positive $n$. It does not assert necessity of the sufficient condition $n/k^2\to\infty$.

The geometric suppliers in (3.3)–(3.6) concern fixed polytopes. Further deterministic inequality, Minkowski-sum, lattice-point, and volume descriptions are given by Bayer et al., *Combinatorics of generalized parking-function polytopes*, [arXiv:2403.07387v1](https://arxiv.org/abs/2403.07387v1), Theorem 2.3 and Section 2.2; Liu and Thawinrak, *Parking Function Polytopes*, [arXiv:2512.14199v1](https://arxiv.org/abs/2512.14199v1), Corollaries 7.6–7.7; Behrend, *Ehrhart polynomials of partial permutohedra*, [arXiv:2403.06975v1](https://arxiv.org/abs/2403.06975v1), Theorem 1 and Section 4; and Hill, Luo, Trinh, and Vindas-Melendez, *Lattice slices, Ehrhart polynomials, and magic positivity of generalized parking-function polytopes*, [arXiv:2607.15503v1](https://arxiv.org/abs/2607.15503v1), Theorems 3.5, 4.1, 5.9, and 6.4. Positivity of such Ehrhart polynomials is also studied by Liu and Zhang, *Magic Positivity for the Ehrhart Polynomials of Partial Permutohedra*, [arXiv:2607.03854v1](https://arxiv.org/abs/2607.03854v1). In (4.3), by contrast, the defining thresholds vary with $h$, and both their multinomial weights and the labelled $A$ sum are part of the count. Identifying a single deterministic polytope or its Ehrhart polynomial supplies the geometric intermediate input, while the averaging and relative comparison remain the content of (2.1).

## 追加锚（本行以下为增补区）
