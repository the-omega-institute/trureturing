# Degree-root boundary rigidity and separation

## 1. Degree polynomials and boundary pairs

**Definition 1.1 (Degree polynomial and angular modulus).** Let $G=(V,E)$ be a finite simple undirected graph of order $n=|V|\ge4$. No connectedness hypothesis is imposed. Write

$$
D(G;X)=\sum_{v\in V}X^{\deg_G(v)},\qquad
\delta=\min_{v\in V}\deg_G(v),\qquad
\Delta=\max_{v\in V}\deg_G(v).
$$

Every vertex contributes once, including an isolated vertex. For $z\ne0$, use the principal argument $\operatorname{Arg}z\in(-\pi,\pi]$. Whenever $\operatorname{Arg}z\ne0$, put

$$
\theta=|\operatorname{Arg}z|,\qquad
B=|z|^{\pi/\theta},\qquad
N=n-1,\qquad K=n-2,\qquad
\eta_n=\frac{\pi}{4(n-2)^2\sqrt{n-1}}.
$$

Powers of positive real numbers mean $a^b=\exp(b\log a)$. The degree-polynomial definition is that of Brown and George, [J, §1, p. 164; A, §1], and George [T, §2.1].

**Definition 1.2 (Boundary class of graph-root pairs).** A pair $(G,z)$ belongs to $\mathcal E_n$ if there are integers $\delta<\Delta$ such that exactly one vertex of $G$ has degree $\Delta$, all other vertices have degree $\delta$, and, with $k=\Delta-\delta$,

$$
z=N^{1/k}\exp(\sigma i\pi/k)
\quad\text{for some }\sigma\in\{-1,1\}.
$$

This definition concerns actual graphs. It makes no assertion that an arbitrary pair of integers $(\delta,\Delta)$ is realizable as such a degree pattern. At $k=1$ the two displayed numbers coincide: both are $-N$, whose principal argument is $\pi$.

## 2. The boundary locus and a uniform gap

**Theorem 2.1 (Exclusive boundary and separation).** For every integer $n\ge4$, every finite simple graph $G$ of order $n$, and every $z\in\mathbb C$ with $z\ne0$ and $D(G;z)=0$, the principal angle satisfies $0<\theta\le\pi$. With the quantities of Definition 1.1, exactly one of the following holds:

$$
B=N,
\qquad\text{or}\qquad
B\le N-\eta_n.
\tag{2.1}
$$

Moreover,

$$
B=N\quad\Longleftrightarrow\quad(G,z)\in\mathcal E_n.
\tag{2.2}
$$

Consequently, for every such graph-root pair outside $\mathcal E_n$,

$$
|z|\le
\left(n-1-\frac{\pi}{4(n-2)^2\sqrt{n-1}}\right)^{\theta/\pi}.
\tag{2.3}
$$

The equality criterion applies to the specified roots of each actual graph with the two-degree pattern. Every other nonzero root of that same graph obeys the second alternative of (2.1).

*Proof.* We first establish the angular and analytic estimates used in the equality and separation argument.

### 2.1. Principal angles and the degree spread

For every positive real $x$, the sum $D(G;x)$ is strictly positive. Thus a nonzero root has $\operatorname{Arg}z\ne0$, so $0<\theta\le\pi$. Set $r=|z|>0$, and choose

$$
w=\begin{cases}
z,&\operatorname{Arg}z>0,\\
\overline z,&\operatorname{Arg}z<0.
\end{cases}
$$

The coefficients of $D$ are real, hence $D(G;w)=0$, $|w|=r$, and $w=r\exp(i\theta)$. Negative real roots already have principal argument $\pi$ and belong to the first case; no argument $-\pi$ is substituted for their principal argument.

If $\delta=\Delta$, then $D(G;z)=nz^\Delta\ne0$, a contradiction. Therefore $q=\Delta-\delta\ge1$. Simplicity gives $0\le\delta\le\Delta\le n-1$. Equality $q=n-1$ would require both an isolated vertex and a vertex adjacent to every other vertex, which is impossible. Hence

$$
1\le q\le K.
\tag{2.4}
$$

We use the nonnegative-coefficient sector estimate of [T, Lemma 3.16 and Corollaries 3.17–3.18, pp. 63–64]. Its elementary half-plane argument in the present notation is as follows. If $q\theta<\pi$, then

$$
\operatorname{Re}\left(
 e^{-iq\theta/2}\frac{D(G;w)}{w^\delta}
\right)
=\sum_{v\in V}r^{\deg(v)-\delta}
 \cos\left((\deg(v)-\delta-q/2)\theta\right)>0.
$$

Indeed, each cosine has its argument strictly between $-\pi/2$ and $\pi/2$, and every real weight is positive. This contradicts $D(G;w)=0$. Consequently

$$
\theta\ge\frac{\pi}{q}\ge\frac{\pi}{K}.
\tag{2.5}
$$

Neither this argument nor (2.4) requires connectedness.

### 2.2. A quantitative refinement consumed by the root argument

For $\lambda>0$ and $t\ge0$, define

$$
\begin{aligned}
H_\lambda(t)&=1+e^{-\lambda(t-\pi)}(\cos t+\lambda\sin t),\\
L(t)&=\min\{(t-\pi)^2,\pi^2/4\},\\
c_\lambda&=\min\left\{
\frac{(1+\lambda^2)e^{-\lambda\pi/2}}{\pi},
\frac{4(1-e^{-2\pi\lambda})}{\pi^2}
\right\}.
\end{aligned}
\tag{2.6}
$$

Both entries in this minimum are strictly positive. We shall use the following precise estimate inside this proof:

$$
H_\lambda(t)\ge c_\lambda L(t)\quad(t\ge0),
\qquad
H_\lambda(t)=0\quad\Longleftrightarrow\quad t=\pi.
\tag{2.7}
$$

To prove it, differentiation gives

$$
H_\lambda(\pi)=0,\qquad
H_\lambda'(t)=-(1+\lambda^2)e^{-\lambda(t-\pi)}\sin t.
$$

For $0\le u\le\pi/2$, integration on either side of $\pi$ yields

$$
\begin{aligned}
H_\lambda(\pi+u)&=(1+\lambda^2)\int_0^u e^{-\lambda s}\sin s\,ds,\\
H_\lambda(\pi-u)&=(1+\lambda^2)\int_0^u e^{\lambda s}\sin s\,ds.
\end{aligned}
$$

On $[0,\pi/2]$, concavity of sine gives $\sin s\ge2s/\pi$, while both exponential factors are at least $e^{-\lambda\pi/2}$. Thus, writing

$$
A_\lambda=\frac{(1+\lambda^2)e^{-\lambda\pi/2}}{\pi},
$$

we obtain $H_\lambda(\pi\pm u)\ge A_\lambda u^2$. This proves (2.7)'s inequality for $\pi/2\le t\le3\pi/2$.

The derivative is nonpositive on $[0,\pi]$ and nonnegative on $[\pi,2\pi]$. Therefore, on $[0,\pi/2]$ and on $[3\pi/2,2\pi]$, respectively,

$$
H_\lambda(t)\ge H_\lambda(\pi/2)\ge A_\lambda\pi^2/4,
\qquad
H_\lambda(t)\ge H_\lambda(3\pi/2)\ge A_\lambda\pi^2/4.
$$

For the remaining range, each interval $[2j\pi,(2j+2)\pi]$, $j\ge1$, has its minimum at $(2j+1)\pi$: the derivative is nonpositive on its first half and nonnegative on its second half. At that minimum,

$$
H_\lambda((2j+1)\pi)=1-e^{-2j\pi\lambda}
\ge1-e^{-2\pi\lambda}.
$$

These intervals cover $[2\pi,\infty)$. Since $L(t)\le\pi^2/4$, this proves the inequality in (2.7) there as well. Finally $c_\lambda>0$ and $L(t)>0$ for $t\ne\pi$ imply strict positivity away from $\pi$, proving its asserted zero set.

The nonquantitative consequence $H_\lambda\ge0$ is the damped-trigonometric input in [R1, `damped_trig_bound`]. Here (2.7) supplies the quantitative loss away from its equality point and is used below with the actual degree differences.

### 2.3. Normalization and an exact deficit identity

Assume for now that $r>1$. Let $m\ge1$ be the number of vertices of degree $\Delta$, put

$$
S=\{v\in V:\deg(v)<\Delta\},\qquad
k_v=\Delta-\deg(v)\quad(v\in S).
$$

Nonregularity implies $S\ne\varnothing$, $|S|=n-m$, and $1\le k_v\le q\le K$. Dividing the root equation by $w^\Delta$ gives the normalization from [R2, `inverse_degree_split`]:

$$
m+\sum_{v\in S}w^{-k_v}=0.
\tag{2.8}
$$

Set

$$
\lambda=\frac{\log r}{\theta}>0,
\qquad B=e^{\lambda\pi}.
$$

Taking real parts of (2.8) after multiplication by $1+i\lambda$ gives

$$
0=m+\sum_{v\in S}e^{-\lambda k_v\theta}
 \bigl(\cos(k_v\theta)+\lambda\sin(k_v\theta)\bigr).
$$

Multiplying this equality by $B$ and using (2.6) proves the exact identity

$$
mB+\sum_{v\in S}H_\lambda(k_v\theta)=n-m.
\tag{2.9}
$$

In particular, (2.7) implies

$$
B\le\frac{n-m}{m}\le n-1=N.
\tag{2.10}
$$

This recovers the normalized inverse-power estimate and weak Brown–George bound supplied by [R1, `normalized_escape_bound`; R2, `graph_exterior_bound` and `result`]. The refinement needed here is to retain the individual nonnegative terms in (2.9), rather than discarding them.

### 2.4. All-angle equality and its converse

If $B=N$, (2.10) forces $m=1$: for $m\ge2$ the ratio is at most $(n-2)/2<N$. With $m=1$, (2.9) becomes

$$
N-B=\sum_{v\in S}H_\lambda(k_v\theta).
\tag{2.11}
$$

At equality its left side vanishes. Every summand is nonnegative and (2.7) has a single zero, so $k_v\theta=\pi$ for every $v\in S$. Thus all $k_v$ are one integer $k$, all nonmaximal degrees equal $\delta=\Delta-k$, and $\theta=\pi/k$. Since $B=N$, we also have $r=N^{1/k}$. If the principal argument is positive, this is $z=N^{1/k}e^{i\pi/k}$; if negative, it is $z=N^{1/k}e^{-i\pi/k}$. For a negative real root $\theta=\pi$ forces $k=1$, and both displayed expressions equal $-N$. This proves the necessity in (2.2) for $r>1$.

Conversely, suppose an actual graph has the degree pattern in Definition 1.2. Then

$$
D(G;X)=X^\Delta+NX^\delta=X^\delta(X^k+N).
\tag{2.12}
$$

For each specified $z=N^{1/k}e^{\sigma i\pi/k}$, we have $z^k=-N$, so $D(G;z)=0$ and $z\ne0$. Its modulus is greater than one and its principal absolute argument is $\pi/k$; for $k=1$ this assertion uses $\operatorname{Arg}(-N)=\pi$ for both signs. Hence $B=(N^{1/k})^k=N$. This proves the converse without any additional degree-sequence realizability assertion.

The two-degree factorization and its roots are the supplied formula in [J, §1, p. 165; A, §1]. For completeness in applying (2.1) to every branch, all the nonzero roots of (2.12) are

$$
z_j=N^{1/k}\exp\left(\frac{(2j+1)\pi i}{k}\right),
\qquad 0\le j<k.
\tag{2.13}
$$

After reduction to the principal argument $\varphi_j\in(-\pi,\pi]$, the number $k\varphi_j$ is an odd multiple of $\pi$. Consequently

$$
k|\varphi_j|=h\pi
\quad\text{for a positive odd integer }h\le k,
\qquad
B=N^{1/h}.
\tag{2.14}
$$

The roots in $\mathcal E_n$ are precisely those with $h=1$. Every other branch has $h\ge3$. Thus the graph's possession of boundary roots does not assert that all its roots are boundary roots.

### 2.5. Quantitative separation

First,

$$
0<\eta_n\le\frac{\pi}{16\sqrt3}<1,
\qquad N-\eta_n>2,
\tag{2.15}
$$

since $K\ge2$ and $N\ge3$. Thus any $B\le2$ already satisfies the second alternative of (2.1).

If $r>1$ and $m\ge2$, (2.10) gives

$$
B\le\frac{n-2}{2},\qquad
N-B\ge\frac n2\ge2>\eta_n.
\tag{2.16}
$$

We may therefore assume $r>1$, $m=1$, and $B>2$. By (2.10), $2<B\le N$. In the two expressions defining $c_\lambda$, use $e^{\lambda\pi}=B$ to obtain

$$
\frac{(1+\lambda^2)e^{-\lambda\pi/2}}{\pi}
=\frac{1+\lambda^2}{\pi\sqrt B}
\ge\frac1{\pi\sqrt N},
$$

and

$$
\frac{4(1-e^{-2\pi\lambda})}{\pi^2}
=\frac{4(1-B^{-2})}{\pi^2}
\ge\frac3{\pi^2}
\ge\frac1{\pi\sqrt N}.
$$

For the last comparison, $\pi<4<3\sqrt3\le3\sqrt N$. Hence

$$
c_\lambda\ge\frac1{\pi\sqrt N}.
\tag{2.17}
$$

Suppose first that the positive integers $k_v$ are not all equal. Choose $u,v\in S$ with $k_u\ne k_v$. The integer spacing and (2.5) imply

$$
|k_u\theta-k_v\theta|\ge\theta\ge\frac\pi K.
$$

By the triangle inequality, at least one of these two arguments, say $t=k_u\theta$, satisfies $|t-\pi|\ge\pi/(2K)$. Since $K\ge2$, it follows that

$$
L(t)=\min\{(t-\pi)^2,\pi^2/4\}
\ge\frac{\pi^2}{4K^2}.
$$

Combining this single summand with (2.7), (2.11), and (2.17) gives

$$
N-B\ge H_\lambda(t)
\ge\frac1{\pi\sqrt N}\frac{\pi^2}{4K^2}
=\frac{\pi}{4K^2\sqrt N}=\eta_n.
\tag{2.18}
$$

It remains to consider the case that all $k_v$ equal $k$. The graph then has the two-degree pattern of (2.12). If $(G,z)\notin\mathcal E_n$, (2.14) gives $k\theta=h\pi$ with $h\ge3$. Thus $|k\theta-\pi|\ge2\pi$ and

$$
L(k\theta)=\pi^2/4\ge\frac{\pi^2}{4K^2}.
$$

Selecting any $v\in S$ in (2.11) and applying the same estimates as in (2.18) again yields $N-B\ge\eta_n$. This includes a negative real root of (2.12) with any odd $k\ge3$; it is not an additional equality case. If instead $(G,z)\in\mathcal E_n$, §2.4 gives $B=N$.

Finally, if $0<r\le1$, then $0<B=r^{\pi/\theta}\le1<N-\eta_n$ by (2.15). Such a pair cannot belong to $\mathcal E_n$, whose prescribed modulus is greater than one. This completes both (2.1) and (2.2) on the entire original domain, including roots on the unit circle. The two alternatives are disjoint because $\eta_n>0$. Since $\theta/\pi>0$ and $N-\eta_n>0$, raising $B\le N-\eta_n$ to the power $\theta/\pi$ proves (2.3). $\square$

## 3. Mathematical source correspondence

In the citations above, [J] denotes J. I. Brown and I. C. George, *On the roots of degree polynomials*, Australasian Journal of Combinatorics 92(2), 164–183, [journal text](https://ajc.maths.uq.edu.au/pdf/92/ajc_v92_p164.pdf); [A] denotes the same authors' [arXiv:2505.04882v1](https://arxiv.org/pdf/2505.04882v1); [T] denotes I. C. George, *On the Degree Polynomial of Graphs*, Dalhousie University, [thesis, handle 10222/82742](https://hdl.handle.net/10222/82742), [full text](https://dal.scholaris.ca/server/api/core/bitstreams/b38bd694-b1b7-4993-a49f-b0d2dc04cc0b/content).

[R1] denotes the repository's [normalized inverse-power source](https://github.com/the-omega-institute/trureturing/blob/0acdf52ecf2d680cff8b44345188dbb02034280d/D5/S3/Zeros/DegreeRoots/EscapeWitness.lean); [R2] denotes its [degree-polynomial source](https://github.com/the-omega-institute/trureturing/blob/0acdf52ecf2d680cff8b44345188dbb02034280d/D5/S3/Zeros/DegreeRoots/Result.lean). Their supplied inputs are the weak estimate $B\le(n-m)/m\le n-1$, the graph normalization, and the damped-trigonometric nonnegativity used in §2.3. Theorem 2.1 refines those inputs by the all-angle equality locus and the explicit off-boundary gap. The quantitative estimate (2.7) is an intermediate consumed in that combined refinement.

The two-degree root formula in (2.12)–(2.13) belongs to [J, p. 165; A, §1]. The star $K_{1,n-1}$ has $D(G;X)=X^{n-1}+NX$, so its roots $N^{1/(n-2)}e^{\pm i\pi/(n-2)}$ are boundary examples; this example is supplied in [J, §4, p. 180; A, §4] and in the [repository's polynomial consequences](https://github.com/the-omega-institute/trureturing/blob/0acdf52ecf2d680cff8b44345188dbb02034280d/Problems/brown-george-2025-degree-polynomial-root-bound.md). It is not an isomorphism classification of extremal graphs.

The real-axis equality specialization $k=1$, $z=-N$, $D(G;X)=X^\Delta+NX^{\Delta-1}$ is [J, Proposition 3.3, p. 178; A, Proposition 3.3; T, Proposition 3.11, p. 55]. The imaginary-axis equality specialization $k=2$, $z=\pm i\sqrt N$, $D(G;X)=X^\Delta+NX^{\Delta-2}$ is [T, Proposition 3.14, pp. 61–62]. The corresponding imaginary modulus bound is [J, Proposition 3.5, pp. 179–180; A, Proposition 3.5; T, Proposition 3.13, pp. 58–60]. The nonnegative-coefficient angular cutoff and the simple-graph degree-spread cutoff in §2.1 are [T, Lemma 3.16 and Corollaries 3.17–3.18, pp. 63–64]. These statements are intermediate antecedents of the all-angle result, rather than separate additions.

The separation in Theorem 2.1 is for finite simple graphs and the specified angular modulus $B$. It asserts neither optimality of $\eta_n$ nor an estimate in any graph metric. Its use of the bounded integer spread $k_v\le n-2$ is explicit in (2.4)–(2.5) and (2.18); the theorem makes no order-only gap assertion for multigraphs.

## 追加锚（本行以下为增补区）
