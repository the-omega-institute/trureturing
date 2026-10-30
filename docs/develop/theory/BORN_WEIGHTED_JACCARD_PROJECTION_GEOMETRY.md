# Born-weighted Jaccard geometry on projection intervals

## 1. Subspaces, weights and cited valuation inputs

**Definition 1.1 (a common faithful weight).** Let $n\ge2$ be an integer,
$H=\mathbb C^n$ with its usual inner product, and $\rho$ a positive definite
Hermitian operator with $\operatorname{Tr}\rho=1$. For every linear subspace
$X\subseteq H$, let $P_X$ be its ordinary orthogonal projection and put

$$
\mu(X)=\operatorname{Tr}(\rho P_X),\qquad f_c(X)=c+\mu(X),\qquad 0\le c<\infty.
\tag{1.1}
$$

The meet is $X\cap Z$ and the join is the actual vector-space sum $X+Z$.
For $f_c(X+Z)>0$ define

$$
d_c(X,Z)=1-\frac{f_c(X\cap Z)}{f_c(X+Z)},\qquad
\Delta_c(X,Y,Z)=d_c(X,Z)-d_c(X,Y)-d_c(Y,Z).
\tag{1.2}
$$

Set $d_0(0,0)=0$. Faithfulness makes this the only pair with zero
denominator. All weights, projections and lattice operations in a triple
use this one $\rho$ on this one $H$.

For $X\subseteq Z$, $P_Z-P_X$ is the orthogonal projection onto
$Z\cap X^\perp$, so $\mu(Z)-\mu(X)\ge0$, strictly if $X\ne Z$.
Indeed, in an orthonormal basis of a nonzero subspace $U$,
$\operatorname{Tr}(\rho P_U)$ is a sum of strictly positive quadratic forms.
Thus $0\le d_c\le1$, the distance is symmetric, and $d_c(X,X)=0$.
These elementary trace facts agree with the forward trace-weight construction
in [R2]; they do not require a representation theorem for arbitrary measures.

**Definition 1.2 (valuation hypotheses and their supplied criterion).**
For a lattice $\mathcal L$ and $f:\mathcal L\to(0,\infty)$, write

$$
\begin{aligned}
\mathrm{Mon}(f)&:\quad A\le B\Longrightarrow f(A)\le f(B),\\
\mathrm{Sup}(f)&:\quad f(A)+f(B)\le f(A\vee B)+f(A\wedge B),\\
\mathrm{Mod}(f)&:\quad f(A)+f(B)=f(A\vee B)+f(A\wedge B).
\end{aligned}
\tag{1.3}
$$

All three conditions quantify over every $A,B\in\mathcal L$, with
$A\le B$ in the first.
The supplied arbitrary-lattice criterion is

$$
\left(\forall A,B,C\in\mathcal L,\quad
 d_f(A,C)\le d_f(A,B)+d_f(B,C)\right)
\quad\Longleftrightarrow\quad
\mathrm{Mon}(f)\ \land\ \mathrm{Sup}(f)\ \land\ \mathrm{Sup}(1/f),
\tag{1.4}
$$

where $d_f(A,B)=1-f(A\wedge B)/f(A\vee B)$ and the reciprocal is pointwise.
Necessity is [B1, Theorem 4]; sufficiency is [R1,
`resultSufficiency`]. Also supplied is [B1, Theorem 1]: strict positivity,
monotonicity and modularity imply the triangle inequality on every lattice.
These are cited inputs, including the scalar inequalities in the private
proofs of [R1], rather than additional conclusions of the interval optimization.
The criterion (1.4) concerns strictly positive $f$; it does not by itself
include the zero-bottom case $c=0$ on the full subspace lattice.

**Definition 1.3 (a two-dimensional interval and its compression).**
Let $R\subseteq H$ be any subspace and let $T\subseteq R^\perp$ have dimension
two. Set

$$
S=R\oplus T,\qquad
K=(P_T\rho)|_T:T\to T,\qquad
b=c+\mu(R),\qquad
0<m\le M,\qquad s=m+M,
\tag{1.5}
$$

where $m,M$ are the eigenvalues of the Hermitian positive definite compression
$K$. Write $[R,S]=\{X:R\subseteq X\subseteq S\}$. Neither $R$ nor $T$ is
assumed invariant under $\rho$. For $x,y\in T$,
$\langle x,Ky\rangle=\langle x,\rho y\rangle$; thus $K$ is Hermitian
and $\langle x,Kx\rangle>0$ for $x\ne0$. For a line $L\subset T$, set

$$
a_L=\operatorname{Tr}_T(KP_L)=\langle u,Ku\rangle\quad(\|u\|=1,\ u\in L).
\tag{1.6}
$$

Here and below $P_L$ inside a trace over $T$ is the projection on $T$.
The spectral theorem gives $m\le a_L\le M$, $s=\operatorname{Tr}_T K=\mu(T)$,
and $b+s>0$. If $U\subseteq T$, then

$$
P_{R\oplus U}=P_R+P_U,\qquad
f_c(R\oplus U)=b+\operatorname{Tr}_T(KP_U).
\tag{1.7}
$$

To see the trace identity, extend an orthonormal basis of $T$ to $H$.
Only its $T$ diagonal block contributes to $\operatorname{Tr}(\rho P_U)$;
that block is $KP_U$. Thus off-diagonal blocks of $\rho$ do not require any
invariance assumption. Every $X\in[R,S]$ is uniquely $R\oplus U$ with
$U=X\cap R^\perp\subseteq T$: subtracting the $R$ component from an element
of $X$ leaves an element of $X$. Moreover

$$
(R\oplus U)\cap(R\oplus V)=R\oplus(U\cap V),\qquad
(R\oplus U)+(R\oplus V)=R\oplus(U+V).
\tag{1.8}
$$

These identities preserve the original meet and join, not projected
substitutes for them.

## 2. Exact optimization at fixed overlap

**Theorem 2.1 (fixed-overlap defect).** For every $n,\rho,c,R,T$ satisfying
Definitions 1.1 and 1.3, and every real $0\le r<1$, the maximum of

$$
\Delta_c(R\oplus L,S,R\oplus N)
\tag{2.1}
$$

over all ordered pairs of lines $L,N\subset T$ with
$|\langle u,v\rangle|=r$ for unit generators is

$$
\frac{r(M-m)}{b+s}.
\tag{2.2}
$$

The maximum is attained for every such $r$, including $r=0$ and $M=m$.

*Proof.* Since $r<1$, the lines are distinct, so their meet in $T$ is zero
and their join is $T$. Equations (1.7)–(1.8) give

$$
\begin{aligned}
d_c(R\oplus L,R\oplus N)&=\frac{s}{b+s},\\
d_c(R\oplus L,S)&=\frac{s-a_L}{b+s},\\
d_c(S,R\oplus N)&=\frac{s-a_N}{b+s}.
\end{aligned}
\tag{2.3}
$$

Consequently

$$
\Delta_c(R\oplus L,S,R\oplus N)
=\frac{a_L+a_N-s}{b+s}
=\frac{\operatorname{Tr}_T(K(P_L+P_N-I_T))}{b+s}.
\tag{2.4}
$$

We use the classical two-line projection spectrum explicitly. Choose the
phase of $v$ so that $\langle u,v\rangle=r$ and write
$v=ru+\sqrt{1-r^2}\,w$ with $w\perp u$, $\|w\|=1$.
In the basis $u,w$ the matrix of $B=P_L+P_N-I_T$ is

$$
B=\begin{pmatrix}
r^2&r\sqrt{1-r^2}\\
r\sqrt{1-r^2}&-r^2
\end{pmatrix},\qquad B^2=r^2 I_T.
\tag{2.5}
$$

For $r>0$ its two eigenvalues are $r,-r$ with orthonormal eigenvectors
$h_+,h_-$. Hence

$$
\operatorname{Tr}_T(KB)
=r\bigl(\langle h_+,Kh_+\rangle-\langle h_-,Kh_-\rangle\bigr)
\le r(M-m).
\tag{2.6}
$$

For $r=0$ the matrix $B$ is zero, giving the same bound.
This is a finite spectral calculation; the extra inference is its use in
the meet-over-join defect (2.4) and the simultaneous attainment below.

Choose orthonormal eigenvectors $e_M,e_m$ for $K$, taking any orthonormal
basis if $M=m$, and put

$$
\begin{aligned}
u_r&=\sqrt{\frac{1+r}{2}}\,e_M+
       \sqrt{\frac{1-r}{2}}\,e_m,\\
v_r&=\sqrt{\frac{1+r}{2}}\,e_M-
       \sqrt{\frac{1-r}{2}}\,e_m.
\end{aligned}
\tag{2.7}
$$

Both vectors are unit, $\langle u_r,v_r\rangle=r$, and their lines are
distinct because $r<1$. Their two weights both equal

$$
a_{\mathbb C u_r}=a_{\mathbb C v_r}
=\frac{s+r(M-m)}2.
\tag{2.8}
$$

Substitution in (2.4) attains (2.2). All operators used in this construction
are the actual compression and actual subspace projections from (1.5)–(1.8).
$\square$

## 3. Optimization over every ordered triple in the interval

**Theorem 3.1 (sharp interval supremum and attainment).** For every
$n\ge2$, every faithful density operator $\rho$ on $\mathbb C^n$, every
finite $c\ge0$, every $R\subseteq H$, and every two-dimensional
$T\subseteq R^\perp$, use the parameters of Definition 1.3. Then

$$
\sup_{X,Y,Z\in[R,R\oplus T]}\Delta_c(X,Y,Z)
=\frac{M-m}{b+s}.
\tag{3.1}
$$

If $M>m$, no ordered triple attains the supremum. If $M=m$, the supremum
is zero and is attained.

*Proof.* By (1.8), the interval consists exactly of its bottom $R$, its
top $S$, and the elements $E_L=R\oplus L$ indexed by lines $L\subset T$.
Put $w=b+s$ and $D=s/w$. For $a=a_L$ define

$$
\alpha_a=\frac{a}{b+a},\qquad \beta_a=\frac{s-a}{w}.
\tag{3.2}
$$

These denominators are positive even if $b=0$. Directly from (1.2) and
(1.7), including the convention $d_0(0,0)=0$, all distances are

$$
\begin{aligned}
d_c(R,S)&=D,& d_c(R,E_L)&=\alpha_{a_L},&
d_c(E_L,S)&=\beta_{a_L},\\
d_c(E_L,E_N)&=D\quad(L\ne N),&&d_c(X,X)&=0.
\end{aligned}
\tag{3.3}
$$

For every $a\in[m,M]$ one has $0<a<s$ and

$$
0\le\alpha_a\le D,\qquad 0\le\beta_a\le D,\qquad
\alpha_a+\beta_a-D
=\frac{a(s-a)}{(b+a)w}>0.
\tag{3.4}
$$

For example, $\alpha_a\le D$ is equivalent to $ab\le sb$; the last
identity remains strict at $b=0$. We now exhaust all possible endpoints
and middle elements.

If $X=Z$, then $\Delta_c(X,Y,Z)=-2d_c(X,Y)\le0$.
If $X\ne Z$ are comparable, their unordered pair has one of the forms
$\{R,S\}$, $\{R,E_L\}$, or $\{E_L,S\}$.
For endpoints $R,S$, a middle element $E_N$ gives
$D-\alpha_{a_N}-\beta_{a_N}<0$ by (3.4), and a middle endpoint gives zero.
For endpoints $R,E_L$, the middle $S$ gives
$\alpha_{a_L}-D-\beta_{a_L}\le0$; any other line element $E_N$ gives
$\alpha_{a_L}-\alpha_{a_N}-D\le0$.
For endpoints $E_L,S$, the middle $R$ gives
$\beta_{a_L}-\alpha_{a_L}-D\le0$; any other line element $E_N$ gives
$\beta_{a_L}-D-\beta_{a_N}\le0$.
Middle endpoints again give zero. Reversing endpoints leaves the defect
unchanged, so every comparable case is included.

It remains to consider distinct line endpoints $X=E_L$, $Z=E_N$.
A middle endpoint gives zero; a third, distinct line element gives $-D$.
For $Y=R$, equations (3.2)–(3.3) and $a_L,a_N\ge m$ give

$$
\begin{aligned}
\Delta_c(E_L,R,E_N)
&=D-\frac{a_L}{b+a_L}-\frac{a_N}{b+a_N}\\
&\le\frac{s}{w}-\frac{2m}{b+m}\\
&<\frac{s-2m}{w}=\frac{M-m}{w}.
\end{aligned}
\tag{3.5}
$$

Here $a/(b+a)$ is nondecreasing for $a>0$, including when $b=0$;
the strict inequality uses $w=b+m+M>b+m$ and $m>0$.
Finally, if $Y=S$, the actual overlap $r$ of $L,N$ lies in $[0,1)$,
so Theorem 2.1 gives

$$
\Delta_c(E_L,S,E_N)\le\frac{r(M-m)}w\le\frac{M-m}w.
\tag{3.6}
$$

This proves the upper bound for every ordered triple, not only for triples
whose middle is the top.

If $M>m$, all non-top cases above are either nonpositive or strictly below
$(M-m)/w$, while (3.6) is strict because $r<1$. Thus the upper bound cannot
be attained. On the other hand, choose the actual lines from (2.7) for any
sequence $r_j\in[0,1)$ tending to one. The resulting defects are
$r_j(M-m)/w$, tending to $(M-m)/w$, which proves (3.1).
If $M=m$, the exhaustive upper bound is zero, and $X=Y=Z=R$ attains it.
$\square$

**Proposition 3.2 (the coincident-line boundary).** The fixed-overlap
maximum in Theorem 2.1 cannot be extended to $r=1$ by the same expression.
For coincident lines $L=N$ the defect with middle $S$ is

$$
\Delta_c(E_L,S,E_L)=-\frac{2(s-a_L)}{b+s}<0.
\tag{3.7}
$$

For the lines (2.7) as $r\uparrow1$, the limiting line is
$\mathbb C e_M$, and at the coincident pair (3.7) equals $-2m/(b+s)$.

*Proof.* Coincidence makes $d_c(E_L,E_L)=0$, whereas for distinct lines
it is $s/(b+s)$. Formula (3.7) follows from (2.3); positivity uses
$s-a_L\ge m>0$. This change of meet accounts exactly for the discontinuity.
$\square$

## 4. Consequences of the interval theorem and existing sufficiency

**Corollary 4.1 (tracial classification).** For each integer $n\ge2$,
each faithful density operator $\rho$ on $H=\mathbb C^n$, and each finite
$c\ge0$, the function $d_c$ on the full subspace lattice satisfies the
triangle inequality for every ordered triple if and only if $\rho=I_H/n$.
In that case $d_c$ is a metric. In fact separation holds for every faithful
$\rho$, whether or not its $d_c$ satisfies the triangle inequality.

*Proof.* If $\rho$ is not scalar, choose two orthonormal eigenvectors
with unequal eigenvalues, set $T$ to their span and $R=0$, and use
Theorem 2.1 with $r=1/2$. It gives a positive defect for every finite $c$.
Thus the triangle inequality fails. Trace one makes every scalar density
operator equal to $I_H/n$.

Conversely, for $\rho=I_H/n$ the weight is
$\mu(X)=\dim(X)/n$. The dimension identity

$$
\dim X+\dim Z=\dim(X+Z)+\dim(X\cap Z)
\tag{4.1}
$$

makes $f_c$ monotone and modular. For $c>0$, [B1, Theorem 1] supplies
the triangle inequality. For $c=0$, apply that result with offsets
$c=\varepsilon>0$ and let $\varepsilon\downarrow0$ for each fixed triple.
For every pair with nonzero join the quotient converges to $d_0$;
for the pair $(0,0)$ it is identically zero. The inequalities therefore
pass to the limit, including triples containing zero.

For arbitrary faithful $\rho$, if $d_c(X,Z)=0$ and $X+Z\ne0$, equality
of numerator and denominator gives
$\mu(X+Z)-\mu(X\cap Z)=0$. The projection onto
$(X+Z)\cap(X\cap Z)^\perp$ has that trace weight. Faithfulness forces
it to be zero, so $X+Z=X\cap Z$ and $X=Z$.
If $X+Z=0$, both are zero. Symmetry, nonnegativity and the zero diagonal
were established in Definition 1.1. This proves the metric assertion.
The sufficiency and the scalar/non-scalar obstruction are applications of
existing valuation and spectral inputs; the sharp all-triple interval value
and its nonattainment are Theorem 3.1's additional conclusions. $\square$

**Corollary 4.2 (commuting Boolean event families).** Let $\mathcal B$ be
the Boolean algebra of subspaces generated by any family of pairwise
commuting orthogonal projections on $H$. For every faithful density
operator $\rho$ on $H$ and finite $c\ge0$, the restriction of $d_c$ to
$\mathcal B$ is a metric. No commutation of $\rho$ with those projections
is required.

*Proof.* Simultaneous diagonalization gives orthogonal nonzero joint
eigenspaces $H_1,\ldots,H_k$ whose direct sum is $H$.
Every event in $\mathcal B$ is the direct sum of a subset of these spaces;
if the generating family does not distinguish two coordinates, they belong
to the same joint eigenspace. The weights
$p_i=\operatorname{Tr}(\rho P_{H_i})>0$ satisfy $\sum_i p_i=1$, and

$$
\mu\left(\bigoplus_{i\in A}H_i\right)=\sum_{i\in A}p_i.
\tag{4.2}
$$

This is precisely an additive Boolean measure, with the usual set meet and
join. Its modularity also follows from
$P_{X\cap Z}=P_XP_Z$ and
$P_{X+Z}=P_X+P_Z-P_XP_Z$ for commuting projections.
The scalar weights (4.2) therefore satisfy the weighted-set hypotheses of
[K1, Theorem 3] at $c=0$, or [B1, Theorem 1] at $c>0$.
Alternatively the same positive-offset limit used in Corollary 4.1 covers
$c=0$. Separation follows from faithfulness as above.
These are inherited Boolean valuation consequences. $\square$

## 5. Arbitrary-subspace modularity and the quantum-event substitution

**Proposition 5.1 (scope of the Born substitution).** In the domain of
Definition 1.1, $\mu$ is orthogonally additive and strictly increasing on
subspace inclusions. It is modular on the full subspace lattice if and
only if $\rho=I_H/n$. For nonscalar $\rho$, its orthogonal additivity does
not imply even supermodularity on arbitrary pairs. For every nonscalar
$\rho$ with $n\ge3$ and $c=0$, there are triangle-violating interval
witnesses with $R\ne0$, and $f_0$ is strictly positive on the entire interval.

*Proof.* Orthogonal additivity follows from $P_{X\oplus Z}=P_X+P_Z$
when $X\perp Z$, and strict increase was proved in Definition 1.1.
For the scalar density operator, (4.1) proves modularity.
For a nonscalar density operator take $T$ spanned by eigenvectors with
unequal eigenvalues and use any $0<r<1$ in (2.7). Equations (1.7), (1.8)
and (2.8) give, with $E_L=R\oplus L$ and $E_N=R\oplus N$,

$$
f_c(E_L)+f_c(E_N)-f_c(S)-f_c(R)
=a_L+a_N-s=r(M-m)>0.
\tag{5.1}
$$

With $R=0$, this disproves supermodularity and hence modularity on the
full lattice. The same pair gives positive triangle defect by (2.4).
This is exactly the obstruction tested by the join-middle substitution
in the necessity proof of [B1, Theorem 4], quantitatively optimized here.

If $n\ge3$, choose a third eigenvector and let $R$ be its span, leaving
$T$ as above. Then $R\perp T$ and $\mu(R)>0$; at $c=0$ every
$X\in[R,R\oplus T]$ satisfies $f_0(X)\ge\mu(R)>0$.
Equation (5.1) and Theorem 2.1 supply the required violation wholly within
this strictly positive interval. If $n=2$, the choice $R=0$, $T=H$ still
gives the violation with an actual density matrix; no representation of
all two-dimensional probability measures is used. $\square$

**Proposition 5.2 (conditional lattice theorem and unweighted trace).**
The Born counterexamples of Proposition 5.1 leave the conditional
arbitrary-lattice criterion (1.4) and the unweighted finite trace
interpretation valid. More precisely, on the finite subspace lattice
$\operatorname{Tr}(P_X)=\dim X$ gives a Jaccard metric with the zero-pair
convention; on the full lattice an unrestricted substitution
$\operatorname{Tr}(\rho P_X)$ for that trace does not preserve the
modularity hypothesis unless $\rho=I_H/n$. Commuting event families retain
the metric conclusion of Corollary 4.2.

*Proof.* Theorem 1 of [B1] assumes strict positivity, monotonicity and
modularity; Proposition 5.1 identifies precisely the failed hypothesis
for a nonscalar density weight. For $c>0$ the weight is strictly positive
on the full lattice and the supermodularity failure is literal. For
$c=0$ strict positivity fails at zero; the interval with $R\ne0$ in
Proposition 5.1, when $n\ge3$, also exhibits the failure inside the
strictly positive domain of (1.4). Thus no assertion of (1.4) is
contradicted.

The identity $\operatorname{Tr}(P_X)=\dim X$ and (4.1) establish the
unweighted claim by the positive-offset argument of Corollary 4.1.
Multiplying a weight by a positive constant leaves its meet-over-join
quotient unchanged, so normalized trace gives the same unshifted metric.
For positive offsets the unweighted weight $c+\dim X$ similarly rescales
to $c/n+\dim X/n$.

The quantum-event discussion [B1, Section 7.1] groups projection trace
with quantum probabilities obtained via Gleason representation.
Gleason's original theorem [G1, Theorem 4.1] concerns measures additive on
mutually orthogonal subspaces in a separable real or complex Hilbert
space of dimension at least three, represented by a positive semidefinite
trace-class operator. Orthogonal additivity is weaker than the arbitrary-subspace
identity (1.3). Proposition 5.1 shows directly why the representation
alone cannot justify the latter substitution. The two-dimensional
calculation uses only the explicitly given density operator, independently
of Gleason's representation hypotheses. $\square$

**Definition 5.3 (mathematical range of the optimization).**
Theorem 3.1 optimizes all triples inside each specified interval of
rank difference two. It does not specify the supremum over the full
subspace lattice when $n>2$. Throughout, $\rho>0$, $n<\infty$ and
$c<\infty$; no singular-state or infinite-dimensional extension is
included. Formula (1.2) uses the original meet and join. No arbitrary-lattice
symmetric-difference distance is defined or classified here.

The spectral theorem, two-line projection spectrum (2.5), the scalar
valuation inputs (1.4), and the Boolean measure interpretation are classical
or supplied intermediate results. The retained additional deduction is
the exact compression-dependent optimization (2.2), the exhaustive
interval optimization (3.1), its attainment dichotomy, and the
coincident-line boundary (3.7). Corollaries 4.1–4.2 and Propositions
5.1–5.2 are applications and parameter correspondences for those inputs.

## 6. Mathematical references

[B1] C. Bădică and A. Bădică, *On the Triangle Inequality for the Jaccard
Distance in Arbitrary Lattices*, [arXiv:2608.18194v1](https://arxiv.org/abs/2608.18194v1),
Equation (17), Theorems 1 and 4, Section 7.1. The arbitrary-lattice
necessity and modular sufficiency used in (1.4) and Section 4 are its
conditional statements.

[R1] *The generalized Jaccard triangle inequality on arbitrary lattices*,
[the repository's supplied arbitrary-lattice results](https://github.com/the-omega-institute/trureturing/blob/c87db0432e50c5db00c7ca9272188def4f497f25/D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.lean),
`resultSufficiency`, `result`, and their private scalar intermediates
`scalar_ordered`, `scalar_bound`, `reciprocal_sum_le`,
`reciprocal_supermodular`. They supply the sufficiency in (1.4), including
the implication from supermodularity and log-submodularity. Their
conclusions do not specify compression eigenvalues or optimize triples
in a projection interval.

[R2] *Finite-dimensional complex matrix algebra and probability*,
[the repository's forward trace-weight construction](https://github.com/the-omega-institute/trureturing/blob/c87db0432e50c5db00c7ca9272188def4f497f25/D5/S3/Quantum/FiniteDimensional.lean),
`bornProbability` and `born_probability_skeleton`: normalization,
linearity of trace weight and nonnegativity on projections.

[K1] S. Kosub, *A note on the triangle inequality for the Jaccard distance*,
[arXiv:1612.02696v1](https://arxiv.org/abs/1612.02696v1), Lemma 1,
Corollary 2 and Theorem 3: nonnegative monotone modular set weights,
including a nonnegative constant at the empty set, yield the triangle
inequality. The distinct symmetric-difference formulation is its
Theorem 4. The journal citation is [DOI:10.1016/j.patrec.2018.12.007](https://doi.org/10.1016/j.patrec.2018.12.007);
the statements used here are those of the specified preprint.

[B2] A. Bădică, C. Bădică, D. Logofătu and I.-D. Neremzoiu,
*Generalizations and Properties of Normalized Similarity Measures for
Boolean Models*, Mathematics **13**(3), 384,
[DOI:10.3390/math13030384](https://doi.org/10.3390/math13030384),
[official full mathematical text](https://mdpi-res.com/d_attachment/mathematics/mathematics-13-00384/article_deploy/mathematics-13-00384.xml),
Proposition 8 and Propositions 9–10, including the proof-local Lemma 1.
Its additive Boolean measure and the parameter $\alpha$ in
$\mu(A\cap B)/(\mu(A\cap B)+\alpha\mu(A\mathbin\triangle B))$
are distinct from the offset $c$ in (1.1). Its Section 7 assumes a
scalar transform $g(0)=0$, which excludes $g(t)=c+t$ at $c>0$.
Those Boolean and scalar-transform statements supply no
compression-dependent value (3.1), nonattainment assertion, or
fixed-overlap optimization (2.2).

[G1] A. M. Gleason, *Measures on the Closed Subspaces of a Hilbert Space*,
[DOI:10.1512/iumj.1957.6.56050](https://doi.org/10.1512/iumj.1957.6.56050),
[original full text](https://www.iumj.indiana.edu/IUMJ/FTDLOAD/1957/6/56050/pdf),
Theorem 4.1 and the orthogonally additive measure definition in Section 1.
The representation's dimension hypothesis and its orthogonal domain of
additivity are retained in Proposition 5.2.

## 追加锚（本行以下为增补区）
