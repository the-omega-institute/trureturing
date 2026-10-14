# FIB harmonic-edge load: uniform renewal nonattainment and three-state separation

No proper stationary renewal law with a finite nonnegative hidden representation attains the original harmonic-edge growth constant. This exclusion holds in every finite hidden dimension, without an initial restriction on the renewal gap support. On the entire original exact-real domains with at most three edge-emitting hidden states, it implies

$$
C_1=0,\qquad C_2\le C_3<c_\star.
$$

The argument is ordinary handwritten mathematics relative to the explicit Universal and Direct premises below. Its increment is a uniform obstruction for the renewal class and a reduction of the complete low-dimensional domains to that class. The original alternative for arbitrary finite hidden dimension remains open. No numerical gap or finite separation pair is evaluated.

## 1. Original objective, actual laws and the full alternative

**Definition 1.1 (Complete no11 words and open-path objective).** For $n\ge1$ let

$$
B_n=\{w\in\{0,1\}^n:w_iw_{i+1}=0\ (1\le i<n)\},\qquad
\mathsf X=\{x\in\{0,1\}^{\mathbb Z}:x_ix_{i+1}=0\ (i\in\mathbb Z)\}.
\tag{1.1}
$$

The graph $\Gamma_n$ has all vertices of $B_n$ and all legal Hamming-one edges. Endpoint insertion uses $w_0=w_{n+1}=0$ as an open-boundary convention; the endpoints are not joined and no additional random bits are observed. On the entire probability simplex put

$$
\begin{aligned}
h(s,t)&=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}\\
\Phi_n(\mu)&=\sum_{\{u,v\}\in E(\Gamma_n)}h(\mu_u,\mu_v),\qquad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu),\qquad
c_\star=\lim_{n\to\infty}\frac{\kappa_n}{n}.
\end{aligned}
\tag{1.2}
$$

The existence of this last limit is part of Premise 2.1. Zero masses remove no vertices or edges. All-zero words, legal endpoint ones, forced singleton fibers and forbidden seams retain their original meanings.

**Definition 1.2 (Entire exact-real edge-emission domain).** For each finite $N\ge1$, $\Theta_N$ consists exactly of the triples $\theta=(\lambda,M_0,M_1)$ satisfying

$$
\begin{gathered}
\lambda\ge0,\quad\lambda\mathbf1=1,\quad M_0,M_1\ge0,\qquad
A=M_0+M_1,\quad A\mathbf1=\mathbf1,\quad\lambda A=\lambda,\\
\lambda M_1^2\mathbf1=0.
\end{gathered}
\tag{1.3}
$$

Here $\lambda$ is a row, $M_0,M_1$ are $N\times N$ matrices with arbitrary exact-real entries, and $\mathbf1$ is the all-one column. Structural zeros, zero stationary masses, reducibility, periodicity and nonminimal representations are allowed. The final condition is scalar stationary no11 legality; it does not impose entrywise $M_1^2=0$ on the entire matrix.

Write $[w]_a$ for the cylinder beginning at coordinate $a$, $[w]=[w]_1$, $M_w=M_{w_1}\cdots M_{w_n}$ and $M_\varepsilon=I$. The actual stationary joint law is

$$
\begin{aligned}
&J_\theta(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=x_a,\ldots,X_b=x_b)\\
&\hspace{20mm}=\lambda_{h_a}\prod_{i=a}^bM_{x_i}(h_i,h_{i+1}),\qquad
P_\theta([w]_a)=\lambda M_w\mathbf1.
\end{aligned}
\tag{1.4}
$$

**Proposition 1.3 (One common stationary realization; Universal, Proposition 4.2).** Equation (1.4) defines a normalized two-sided stationary joint law, whose visible marginal $P_\theta$ is supported on $\mathsf X$.

**Proof.** Summing the last bit and state uses $A\mathbf1=\mathbf1$, while summing the first uses $\lambda A=\lambda$. These give right and left consistency of the finite interval distributions, and their total mass is $\lambda A^{b-a+1}\mathbf1=1$. Probability extension on the finite-alphabet product space gives the joint law. Translation leaves the displayed probabilities unchanged. Summing the hidden states gives the visible formula. At each position the probability of $11$ is $\lambda M_1^2\mathbf1=0$; the union over all positions is null. Every concatenation $uv$ consequently uses the one ordered product $\lambda M_uM_v\mathbf1$, including its seam. Coordinates throughout count original emitted bits. $\square$

**Definition 1.4 (Actual density and window risk).** Let $P$ be a stationary Borel probability on $\mathsf X$, with coordinate maps $X_i(x)=x_i$ and shift $(Tx)_i=x_{i+1}$. Write $P_{[1,n]}$ for its actual marginal on coordinates $1,\ldots,n$. Set

$$
\begin{gathered}
\mathcal E_i=\sigma(X_j:j\ne i),\qquad F_i=\{X_{i-1}=X_{i+1}=0\},\qquad
q_i=q_0\circ T^i,\quad q_0=\mathbb E_P[X_0\mid\mathcal E_0],\\
\mathcal F_r=\sigma(X_{-r},\ldots,X_{-1},X_1,\ldots,X_r),\qquad
q_r=\mathbb E_P[X_0\mid\mathcal F_r],\qquad
D_r(P)=\mathbb E_P(X_0-q_r)^2,\quad r\ge1,\\
d(P)=\lim_{n\to\infty}\frac{\Phi_n(P_{[1,n]})}{n},\qquad
\ell_i(x)=(x_i-q_i(x))^2.
\end{gathered}
\tag{1.5}
$$

Choose Borel exterior-measurable posterior versions in $[0,1]$. All expectations refer to the same actual law $P$; in the finite-hidden assertions it is $P_\theta$. Premise 2.1 identifies the limit in (1.5) with the full-exterior risk. A retained neighbor one forces $q_i=0$. Null conditional fibers have zero weighted contribution and require no division.

**Definition 1.5 (Whole-domain extrema and original alternatives).** Retain

$$
C_N=\sup_{\theta\in\Theta_N}d(P_\theta),\qquad
U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta),\quad N,r\ge1.
\tag{1.6}
$$

The unchanged original problem asks which of the following holds:

$$
\exists N\ge1\ \exists\theta\in\Theta_N:\ d(P_\theta)=c_\star,
\qquad\text{or}\qquad
\forall N\ge1:\ C_N<c_\star.
\tag{1.7}
$$

By the compact attainment argument in Proposition 11.3, the second alternative is equivalent to

$$
\forall N\ge1\ \exists r,m\ge1:\quad U_{N,r}<\frac{\kappa_m}{m+1}.
\tag{1.8}
$$

All extrema and quantifiers use (1.3), including its zero-mass states. No full-support or irreducibility restriction is added to this domain.

## 2. Exact supplier premises and the conditional direct bridge

**Premise 2.1 (Universal optimization, risk and attained support).** [Universal][U], Convention 1.3, Lemma 2.1, equation (1.5), Theorem 3.1 and Proposition 7.1, supplies the following facts in the domains of §1:

$$
nc_\star\le\kappa_n\le(n+1)c_\star,\qquad
\frac{\kappa_n}{n+1}\longrightarrow c_\star,\qquad
c_\star\ge c_0:=\frac{1800}{12559}>\frac19,
\tag{2.1}
$$

$$
\begin{aligned}
D_r(P)&=\sum_{\substack{u,v\in B_r\\u_r=v_1=0}}
h(P([u0v]),P([u1v])),\\
D_r(P)&\downarrow d(P)=\mathbb E_P\ell_0\le c_\star.
\end{aligned}
\tag{2.2}
$$

For every attaining stationary law, $d(P)=c_\star$ implies, simultaneously at all integer sites,

$$
q_i=0\text{ on }F_i^c,\qquad \frac14\le q_i\le\frac12\text{ on }F_i,
\quad P\text{-almost surely},
\tag{2.3}
$$

and, for every $w\in B_n$ and every location $a$,

$$
P([w]_a)\ge2^{-(n+2)}3^{-k(w)}>0,\qquad k(w)=\sum_iw_i.
\tag{2.4}
$$

These facts retain Universal's source ownership, including its finite-optimizer square identity and the growth and stationary-risk sources underlying them. No consistency of the separate finite optimizers is assumed. The exact rational comparison in (2.1) is a supplied lower bound for the growth constant, not a computed separation gap.

**Definition 2.2 (Both actual one-sided erasures).** For $j\ge0$ define precisely the fields of [Direct][D], Definition 1.3:

$$
\begin{aligned}
\mathcal L_j&=\sigma(X_{-j},\ldots,X_{-1},X_1,X_2,\ldots),&
p_j^L&=\mathbb E_P[X_0\mid\mathcal L_j],\\
\mathcal R_j&=\sigma(\ldots,X_{-2},X_{-1},X_1,\ldots,X_j),&
p_j^R&=\mathbb E_P[X_0\mid\mathcal R_j],\\
e_L(j)&=\mathbb E_P(q_0-p_j^L)^2,&
e_R(j)&=\mathbb E_P(q_0-p_j^R)^2,\\
A_P&=\sum_{j\ge0}\bigl(\sqrt{e_L(j)}+\sqrt{e_R(j)}\bigr).
\end{aligned}
\tag{2.5}
$$

At $j=0$ the finite retained side is empty and the entire opposite half-line remains. Both zero-offset terms are included.

**Premise 2.3 (Direct attainment-to-strong-zero theorem).** [Direct][D], Theorem 1.5, gives for every stationary legal $P$

$$
d(P)=c_\star\quad\text{and}\quad A_P<\infty
\quad\Longrightarrow\quad\mathsf Z_\Delta(P).
\tag{2.6}
$$

Here $\mathsf Z_\Delta(P)$ means that one shift-invariant Borel $P$-conull set $\Omega_0$ is saturated under every legal finite modification, and for every finitely differing $x,z\in\Omega_0$ the original-law series

$$
\Delta_P(x,z)=\sum_{i\in\mathbb Z}\bigl(\ell_i(x)-\ell_i(z)\bigr)
\tag{2.7}
$$

converges absolutely and equals zero. Saturation includes every legal completion obtained by changing finitely many sites. The functions $q_i$ and $\ell_i$ at a modified configuration remain those of $P$.

Direct's Convention 2.2 retains the legal-surgery and version premises from Exterior, Theorem 3.1, and Guarded, Lemma 2.2: compatible full-exterior fibers are positive under the attained band, legal replacements are nonsingular, and two fixed original-law posterior-version collections agree on a common saturated conull domain. The nested bodies are uninspected mathematical premises; their identities and precise role are recorded in §13. Thus (2.6) is used as the stated handwritten supplier theorem, including this dependency boundary. The root sum will be proved in §5 for the actual renewal law before (2.6) is applied. No root-sum assertion for arbitrary nonrenewal hidden laws is part of this premise.

## 3. The actual renewal class and distributional resets

**Definition 3.1 (Proper stationary renewal law).** A stationary legal law $P$ is proper renewal if ones are unbounded in both directions almost surely, its intensity $\iota=P(X_0=1)$ is positive, and under the Palm probability

$$
P^1=P(\,\cdot\mid X_0=1)
\tag{3.1}
$$

the bi-infinite consecutive one-to-one distances are independent and identically distributed with a probability mass function $f$ on $\{2,3,\ldots\}$. Put $f(1)=0$. Finite supports, missing lengths and supports contained in a proper arithmetic progression are initially allowed. This is a property of the actual visible law, independent of which finite representation is used. The all-zero law is considered separately.

**Lemma 3.2 (Finite-state avoidance on the actual stationary support).** Suppose that each positive-weight closed irreducible class of $A=M_0+M_1$ has at least one edge emitting one. There exist an integer $K\ge1$ and $0<\varepsilon<1$ such that

$$
P_\theta([0^j])=\lambda M_0^j\mathbf1
\le(1-\varepsilon)^{\lfloor j/K\rfloor}\quad(j\ge0).
\tag{3.2}
$$

The same bound holds with $\lambda$ replaced by any probability row supported on those classes. Every finite representation of a proper renewal law satisfies the hypothesis.

**Proof.** A finite stationary chain has zero stationary mass on transient states and is a mixture of its closed irreducible classes, as recalled with proof in Lemma 11.1. In each positive class and from each of its states, choose a positive labeled path reaching and traversing an edge emitting one. Choose $K$ at least the largest path length and $\varepsilon$ strictly between zero and the least of their positive path probabilities, also less than one. Following the specified path ensures that a one has appeared within $K$ emitted bits; the remaining steps have total conditional probability one. Thus, with $B=M_0$, $B^K\mathbf1\le(1-\varepsilon)\mathbf1$ on these closed classes. Iterate using nonnegativity and $B\mathbf1\le\mathbf1$ to obtain (3.2). Periodicity causes no change in this argument.

If a positive stationary class had no one-emitting edge, that class would give positive mass to the all-zero visible configuration. This contradicts the defining two-sided unboundedness of ones for a proper renewal law. The original matrices and their zero-mass states are not changed. $\square$

**Lemma 3.3 (Actual finite phase-type gaps).** If $P=P_\theta$ is proper renewal for some $\theta\in\Theta_N$, put

$$
B=M_0,\qquad b=M_1\mathbf1,\qquad
\alpha=\frac{\lambda M_1}{\iota},\qquad \iota=\lambda M_1\mathbf1.
\tag{3.3}
$$

Then $\alpha$ is the actual law of $H_1$ given $X_0=1$, and

$$
\alpha\mathbf1=1,\qquad B\mathbf1+b=\mathbf1,\qquad
f(g)=\alpha B^{g-1}b\ (g\ge1),\qquad
f(1)=0,\quad\sum_{g\ge2}f(g)=1.
\tag{3.4}
$$

In particular the actual gap law has a finite nonnegative discrete phase-type representation and finite mean.

**Proof.** Formula (1.4) gives the post-emission row $\lambda M_1/\iota$. Starting from this row, a next one at distance $g$ means zeros at positions $1,\ldots,g-1$ followed by one at $g$, giving $\alpha B^{g-1}b$. Scalar legality gives $\alpha b=\lambda M_1^2\mathbf1/\iota=0$. Properness makes the next one finite almost surely, so these masses sum to one. Moreover $\lambda M_1\le\lambda A=\lambda$ entrywise, so $\alpha$ is supported on the same positive stationary classes. Lemma 3.2 bounds the chance of at least $j$ initial zero emissions after a one by $(1-\varepsilon)^{\lfloor j/K\rfloor}$. Summing this tail gives finite mean. The same bound proves transience of the zero-emission matrix on those closed classes; unused original coordinates may remain nontransient. Thus the phase-type absorption law is proper from the actual row $\alpha$. This derives $f$ from the same $J_\theta$; it does not assign a separate renewal model. $\square$

**Proposition 3.4 (Nonnegative rank-one emission gives an actual reset).** On a positive-weight closed irreducible hidden class, if $Q=M_1$ is nonzero and has rank one, its visible law is proper stationary renewal.

**Proof.** A nonzero nonnegative rank-one matrix has a factorization

$$
Q=b\alpha,\qquad b=Q\mathbf1,\qquad \alpha\ge0,\quad\alpha\mathbf1=1.
\tag{3.5}
$$

Indeed, normalize a nonzero row to obtain $\alpha$; every other nonzero row is a nonnegative multiple of it, and its row sum is that multiple. For every nonnegative past row $\eta$,

$$
\eta Q=(\eta b)\alpha.
\tag{3.6}
$$

Thus conditioning on a visible one resets the next hidden-state distribution to $\alpha$, including when this distribution is not concentrated at a single state. The class has a one-emitting edge, so Lemma 3.2 makes both entirely zero half-lines null, using stationarity for the left half-line. Ones are therefore unbounded in both directions. Its stationary intensity is positive because the stationary row is positive on the class and $Q\ne0$.

For any finite list of consecutive gaps, repeated factorization of the ordered products at the intervening $Q$ matrices gives

$$
P([1\,0^{g_1-1}1\cdots0^{g_t-1}1])
=\iota\prod_{j=1}^t\alpha B^{g_j-1}b.
\tag{3.7}
$$

The masses $f(g)=\alpha B^{g-1}b$ sum to one by the avoidance bound, and $f(1)=0$ by legality. To include gaps before a Palm one at the origin, place the earliest specified one at the negative sum of the specified preceding gaps. Stationarity and (3.7), divided by $P(X_0=1)=\iota$, give the product of $f$ over the entire specified list, on both sides of the origin. Finite-cylinder uniqueness proves the bi-infinite iid Palm gap law. This proves the distributional reset-to-renewal implication within the actual joint law. $\square$

## 4. Full-exterior split and merge, including forced and null fibers

**Proposition 4.1 (Actual nearest-anchor posterior).** Let $P$ be any proper stationary renewal law. For integers $a,b\ge1$ let $C_{a,b}\in\mathcal E_0$ specify nearest exterior ones at $-a$ and $b$: those two coordinates are one and every intervening coordinate other than coordinate $0$ is zero. Then

$$
P(C_{a,b},X_0=0)=\iota f(a+b),\qquad
P(C_{a,b},X_0=1)=\iota f(a)f(b).
\tag{4.1}
$$

Whenever $f(a+b)+f(a)f(b)>0$, the actual full-exterior posterior on this event is

$$
q(a,b)=\frac{f(a)f(b)}{f(a+b)+f(a)f(b)}.
\tag{4.2}
$$

If $a=1$ or $b=1$, a retained neighbor one forces the center to zero. If both masses in (4.1) vanish, $C_{a,b}$ is null and no ratio is required. If exactly one mass is positive, (4.2) gives the corresponding posterior zero or one.

**Proof.** Conditional on the one at $-a$, the center-zero completion is a single gap of length $a+b$, and the center-one completion consists of gaps $a,b$. The Palm iid property gives (4.1), including $f(1)=0$ in illegal center-one completions.

To identify conditioning on the entire exterior, add arbitrary finite collars to the left of $-a$ and right of $b$. Under the Palm law at $-a$, the left past gaps are independent of the specified middle gap or gaps. Conditional on either middle completion, the future after the specified one at $b$ is a fresh sequence of gaps with the same law, independent of those middle gaps and the left past. Consequently each completed collar mass has the form

$$
\iota L\,f(a+b)R\quad\text{or}\quad
\iota L\,f(a)f(b)R,
\tag{4.3}
$$

where $L,R\ge0$ are the same outer likelihoods. For a rank-one representation this is also immediate from repeated use of (3.5) in the original ordered matrix product. Zero outer likelihoods make both masses zero.

Refining an arbitrary finite exterior cylinder into such collars and summing (4.3) proves the conditional integral identity for $X_0$ and the constant (4.2) on $C_{a,b}$. Finite exterior cylinders form a generating algebra for $\mathcal E_0$; uniqueness of finite measures extends the identity to every exterior event. The countably many nearest-anchor events cover almost surely by properness. This proves the full-exterior assertion, with every supported, forced and null case included. The formula, extended arbitrarily on its null cases and outside the two-sided-anchor set, defines a Borel exterior version. Its translates give compatible versions at all sites. $\square$

**Corollary 4.2 (Attainment forces full gap support and the odds band).** If this same $P$ attains $c_\star$, then

$$
f(g)>0\quad(g\ge2),\qquad
\frac13\le\frac{f(a)f(b)}{f(a+b)}\le1\quad(a,b\ge2).
\tag{4.4}
$$

**Proof.** The legal word $1\,0^{g-1}1$ has probability $\iota f(g)$, which is positive by (2.4). Thus every $g\ge2$ has positive mass. For each $a,b\ge2$, $C_{a,b}$ is a positive-probability free-site event, and its posterior is the constant (4.2). The attained band (2.3) therefore applies to that constant. Taking its odds gives (4.4). Finite supports, missing lengths and arithmetic restrictions have been excluded by a necessary consequence of attainment, not removed from Definition 3.1. $\square$

## 5. The actual one-sided root sum and legitimate use of strong zero

**Theorem 5.1 (Both erasure sums for every finite-hidden proper renewal law).** If $P=P_\theta$ is proper renewal for any finite $N$ and $\theta\in\Theta_N$, choose $K,\varepsilon$ from Lemma 3.2. Then

$$
e_L(j),e_R(j)\le P([0^j])\le(1-\varepsilon)^{\lfloor j/K\rfloor}
\quad(j\ge1),
\tag{5.1}
$$

and, including both $j=0$ terms,

$$
A_P\le2\sum_{j\ge0}(1-\varepsilon)^{\lfloor j/K\rfloor/2}
=\frac{2K}{1-\sqrt{1-\varepsilon}}<\infty.
\tag{5.2}
$$

**Proof.** Let $G_j^L$ be the event that some retained bit among $X_{-j},\ldots,X_{-1}$ is one. It belongs to $\mathcal L_j$. On that event the nearest left exterior one is retained, and the whole right half-line, hence almost surely its nearest one, is also retained. Proposition 4.1 expresses $q_0$ using exactly those two distances, with the forced-neighbor cases included. Thus $\mathbf1_{G_j^L}q_0$ has an $\mathcal L_j$-measurable version. Since $\mathcal L_j\subseteq\mathcal E_0$, the tower identity gives

$$
p_j^L=\mathbb E_P[q_0\mid\mathcal L_j],\qquad
\mathbf1_{G_j^L}p_j^L=\mathbf1_{G_j^L}q_0.
\tag{5.3}
$$

Both predictors lie in $[0,1]$ on the complementary event, so

$$
e_L(j)\le P((G_j^L)^c)=P([0^j]).
\tag{5.4}
$$

For the right side, let $G_j^R$ be the event that some $X_1,\ldots,X_j$ is one. The field $\mathcal R_j$ retains its nearest right anchor and the entire left half-line. Proposition 4.1 makes $\mathbf1_{G_j^R}q_0$ measurable there, and the same tower identity gives equality of $p_j^R$ and $q_0$ on this event. Therefore $e_R(j)\le P([0^j])$ separately. This argument does not need reversibility.

Lemma 3.2 now gives (5.1). At $j=0$ each squared error is at most one; neither error is set to zero. For each integer $t\ge0$ there are exactly $K$ nonnegative $j$ with $\lfloor j/K\rfloor=t$. Summing the resulting geometric series proves (5.2). All fields, event probabilities and projections belong to the same actual $P$. The constants depend on that law. $\square$

**Corollary 5.2 (Strong zero under hypothetical renewal attainment).** If a finite-hidden proper renewal law $P$ attains $c_\star$, Premise 2.3 applies to the explicit posterior of Proposition 4.1.

**Proof.** Theorem 5.1 pays exactly $A_P<\infty$ from (2.5), and attainment supplies the other hypothesis. Direct's fixed-version agreement allows its strong-zero conclusion to use the explicit renewal version and its translates. The set of configurations with ones unbounded in both directions is shift invariant, conull and saturated under finite modifications. Intersecting with it retains those properties for the supplied strong-zero domain. Under attainment, (4.4) also makes (4.2) defined on every such nearest-anchor fiber, with forced neighbors interpreted as in Proposition 4.1. All subsequent insertions are therefore evaluated with the same original-law loss functions. $\square$

## 6. Legal insertion, score separation and actual reward density

For §§6–10 assume, toward a contradiction, that a proper stationary renewal law $P=P_\theta$ with some finite representation attains $c_\star$. Its gap law has (3.4), (4.4), and the strong-zero property from Corollary 5.2.

**Definition 6.1 (One-site loss and gap loss).** For $a,b,n\ge2$ put

$$
U(a,b)=(1-q(a,b))^2,\qquad
V(n)=\sum_{j=2}^{n-2}q(j,n-j)^2,
\tag{6.1}
$$

where $V(2)=V(3)=0$. At a one with adjacent gaps $a,b$, its loss is $U(a,b)$. The zeros strictly inside a gap of length $n$ have total loss $V(n)$: the neighboring zero positions have posterior zero because they adjoin a retained one. When $n=2$ this is a single zero adjoining both ones, still of loss zero. These forced sites are included through their zero contributions.

**Lemma 6.2 (Insertion identity with both boundary-one losses).** For every $h,k,a,b\ge2$,

$$
\begin{aligned}
V(a+b)+U(h,a+b)+U(a+b,k)
={}&V(a)+V(b)\\
&+U(h,a)+U(a,b)+U(b,k).
\end{aligned}
\tag{6.2}
$$

**Proof.** Specify four consecutive ones with gaps $h,a+b,k$. This finite cylinder has probability $\iota f(h)f(a+b)f(k)>0$, so it meets the saturated conull set of Corollary 5.2. In any configuration in that intersection, insert a one splitting the middle gap into lengths $a,b$. The insertion is legal since $a,b\ge2$ and remains in that set by saturation.

The changed scores are exactly the old middle-gap zeros, the new middle-gap zeros and inserted one, and the two endpoint ones of the middle gap. Their old total is the left side of (6.2); their new total is the right side. Every score outside these endpoints sees the same nearest exterior ones as before, or remains a forced zero. Thus the cocycle has finite support here, and strong zero gives (6.2). This holds for each specified quadruple, because each has positive actual probability. In particular neither boundary-one loss may be omitted.

Every finite legal modification on the two-sided-anchor set can also be realized by choosing outer ones beyond the changed region, deleting the interior ones that are to be changed, and inserting the desired ones. Each intermediate configuration is legal; if convenient all interior ones can first be deleted. Deletions invert (6.2). This explains why the insertion analysis respects the full legal finite-modification relation. $\square$

**Lemma 6.3 (Separated one scores and additive gap energy).** There are numbers $v_n$, $n\ge2$, and a constant $c$ such that

$$
\begin{gathered}
U(a,b)=v_a+v_b,\qquad v_n=\tfrac12U(n,n),\qquad
\frac18\le v_n\le\frac9{32},\\
W(n):=V(n)+2v_n=cn\quad(n\ge2),\qquad
v_2=c,\quad v_3=\frac32c.
\end{gathered}
\tag{6.3}
$$

With $\psi(t)=(1-\sqrt t)^2$ for $t>0$, one further has

$$
V(n)=\sum_{j=2}^{n-2}\psi(v_j+v_{n-j}).
\tag{6.4}
$$

**Proof.** Fix $a,b,k$ in (6.2) and vary $h$. It follows that $U(h,a+b)-U(h,a)$ is independent of $h$. Thus two columns whose indices differ by at least two differ by a constant. The graph on $\{2,3,\ldots\}$ joining such indices is connected: $2$ joins every $n\ge4$, and $3$ joins $5$. There are consequently constants $d_n$, with $d_2=0$, such that $U(h,n)=U(h,2)+d_n$. Symmetry gives $U(h,2)=U(2,2)+d_h$, so taking $v_n=d_n+U(2,2)/2$ proves separation and the diagonal formula. The band $1/4\le q\le1/2$ gives $1/4\le U\le9/16$, hence the stated bounds on $v_n$.

Substitution into (6.2) and cancellation of $v_h,v_k$ gives $W(a+b)=W(a)+W(b)$ for all $a,b\ge2$. In particular $W(6)=3W(2)=2W(3)$. Let $c=W(2)/2=W(3)/3$. The recurrence $W(n)=W(2)+W(n-2)$ for $n\ge4$ then proves $W(n)=cn$ for both parities. Since $V(2)=V(3)=0$, the formulas for $v_2,v_3$ follow. Finally $1-q(j,n-j)=\sqrt{U(j,n-j)}$ is positive, so its complementary square is exactly the summand in (6.4). $\square$

**Proposition 6.4 (The additive constant is the actual bit density).** The constant in (6.3) satisfies

$$
c=d(P)=c_\star.
\tag{6.5}
$$

**Proof.** Assign each site to its preceding visible one, including that one and stopping just before the next one. This defines a shift-compatible partition almost surely. For any nonnegative shift-compatible mass $m(i,j)$, stationarity and Tonelli give

$$
\mathbb E_P\sum_jm(0,j)=\sum_j\mathbb E_Pm(-j,0)
=\mathbb E_P\sum_im(i,0).
\tag{6.6}
$$

First send mass one from each site to its assigned one. Under the Palm law, the incoming mass at a one is its next gap $G$, so

$$
1=\iota\,\mathbb E_{P^1}G.
\tag{6.7}
$$

This is the stationary mass-transport form of the renewal intensity identity; finite mean also follows from Lemma 3.3. Next send the actual loss $\ell_i$ from each site to its assigned one. Its expected outgoing mass is $d(P)$ by (2.2). With $G_-,G_+$ the preceding and following Palm gaps, the incoming reward is $U(G_-,G_+)+V(G_+)$. The two gaps have the same actual law $f$ and are independent under $P^1$. Thus (6.3), (6.6) and (6.7) give

$$
\begin{aligned}
d(P)&=\iota\,\mathbb E_{P^1}\bigl[U(G_-,G_+)+V(G_+)\bigr]\\
&=\iota\,\mathbb E_f\bigl[V(G)+2v_G\bigr]
=\iota c\,\mathbb E_fG=c.
\end{aligned}
\tag{6.8}
$$

The rewards are nonnegative and bounded by the number of sites in the gap, so the expectations are legitimate. This computes density on the original emitted-bit clock for the same $P$. Hypothetical attainment supplies the final equality to $c_\star$. $\square$

## 7. Exponential normalization and the finite nonnegative periodic tail

**Lemma 7.1 (Normalization forced by the odds band).** There exists $0<\rho<1$ such that

$$
F_n:=\frac{f(n)}{\rho^n}\in[1/3,1]\quad(n\ge2).
\tag{7.1}
$$

**Proof.** Positivity in (4.4) allows $z_n=\log f(n)$. The same band says

$$
z_a+z_b\le z_{a+b}\le z_a+z_b+\log3\quad(a,b\ge2).
\tag{7.2}
$$

Repeat this inequality at the common multiple $mn$. The lower estimate using $n$ copies of $m$ and the upper using $m$ copies of $n$ give

$$
nz_m\le z_{mn}\le mz_n+(m-1)\log3,
\qquad
\frac{z_m}{m}\le\frac{z_n+\log3}{n}.
\tag{7.3}
$$

Hence

$$
L_0:=\sup_{m\ge2}\frac{z_m}{m}
\le L_1:=\inf_{n\ge2}\frac{z_n+\log3}{n}.
\tag{7.4}
$$

Both numbers are finite: $z_2/2$ is a lower bound for $L_0$, all $z_m\le0$, and the $n=2$ term bounds $L_1$ above. Moreover, for every $n\ge2$, $L_1-L_0\le\log3/n$. They therefore coincide at a finite $L$. Set $\rho=e^L$. From $z_n\le nL\le z_n+\log3$ one gets (7.1). Since $\sum_nf(n)=1$, the lower bound $f(n)\ge\rho^n/3$ rules out $\rho\ge1$. Positivity of $e^L$ gives the other strict inequality. $\square$

**Lemma 7.2 (Useful PF blocks and residue limits).** There exist an integer $p\ge1$ and constants $C_r\in[1/3,1]$, $r\in\mathbb Z/p\mathbb Z$, such that

$$
F_n\longrightarrow C_r\quad\text{as }n\longrightarrow\infty, n\equiv r\pmod p.
\tag{7.5}
$$

This conclusion allows reducible zero-emission matrices, periodic irreducible blocks and Jordan coupling between blocks.

**Proof.** Use the actual representation $f(n)=\alpha B^{n-1}b$ from Lemma 3.3. In its scalar path expansion only states reachable by positive $B$ paths from the support of $\alpha$ and able to reach the support of $b$ by positive $B$ paths contribute. Call these states useful. Every contributing path stays within the useful set. Thus the same scalar products can be analyzed on its principal submatrix; this is an identity for those products, with no change to the original parameter domain or actual law.

Put the useful submatrix in Frobenius block form. Its diagonal blocks are irreducible nonnegative matrices, including possible one-state zero blocks. Consider a useful irreducible block of positive spectral radius $R$. Choose fixed positive entrance and exit paths connecting $\alpha$ to a state $u$ of the block and a state $v$ of the block to $b$. The cyclic Perron–Frobenius theorem gives a period $d$ and an allowed residue of $k$ for which, for all sufficiently large $k$ in that residue,

$$
(B_{\rm block}^k)_{uv}\ge\eta R^k
\tag{7.6}
$$

with some $\eta>0$. This is the positive Perron limit for the appropriate primitive block of the $d$th power. Nonnegativity and the fixed entrance and exit paths then give $f(k+t)\ge\eta'R^k$ with fixed $t$ and $\eta'>0$. If $R>\rho$, this contradicts $f(k+t)\le\rho^{k+t}$ from (7.1). Thus every useful block has spectral radius at most $\rho$.

If every useful block had radius strictly below $\rho$, the finite-dimensional Jordan expansion of the useful submatrix, including its off-diagonal couplings, would make $\alpha B^{n-1}b/\rho^n$ tend to zero: every term is a polynomial in $n$ times a strictly decaying exponential, with zero-eigenvalue terms eventually zero. This contradicts the lower bound $F_n\ge1/3$. Therefore the largest useful spectral radius is exactly $\rho$.

For an irreducible nonnegative block of radius $\rho$, every peripheral eigenvalue is $\rho$ times a root of unity, by the cyclic Perron–Frobenius theorem. The spectrum of the Frobenius form is the union of its diagonal-block spectra. Choose $p$ divisible by the periods of all blocks of radius $\rho$. Jordan expansion of the scalar sequence now has the following form on each residue $r$ modulo $p$:

$$
F_n=P_r(n)+o(1),\qquad n\equiv r\pmod p,
\tag{7.7}
$$

where $P_r$ is a real polynomial. Indeed, peripheral phase factors are constant on that residue, their Jordan terms give a polynomial, and all remaining eigenvalues have modulus strictly below $\rho$ and give a decaying remainder even after multiplication by a polynomial. The use of $B^{n-1}$ instead of $B^n$ changes only the coefficients. The real form, or conjugate pairing, gives real $P_r$.

The scalar bounds $1/3\le F_n\le1$ force each $P_r$ to be constant; a nonconstant real polynomial is unbounded on the infinite positive residue progression. Call that constant $C_r$. Passing to the limit gives $C_r\in[1/3,1]$. This rules out nonconstant leading Jordan contributions by a bound on the exact scalar sequence, without assuming their cancellation or imposing primitivity. $\square$

## 8. Collapse of peripheral residues and the limiting score

**Lemma 8.1 (Score separation collapses every residue).** There exist $C\in[1/3,1]$ and $L\in[1/8,9/32]$ such that

$$
F_n\longrightarrow C,\qquad v_n\longrightarrow L.
\tag{8.1}
$$

Let $g(t)=(1+t)^{-2}$ for $t>0$, set $s=2L$, and let $R(t)=t^{-1/2}-1$ for $0<t<1$. Then

$$
s=g(C)\in[1/4,9/16],\qquad
F_a=R(v_a+L)\quad(a\ge2),
\tag{8.2}
$$

and

$$
\frac{F_aF_b}{F_{a+b}}=R(v_a+v_b)\quad(a,b\ge2).
\tag{8.3}
$$

**Proof.** The definition of $U$, together with (4.2) and cancellation of the powers of $\rho$, gives

$$
U(a,b)=g\left(\frac{F_aF_b}{F_{a+b}}\right),\qquad
v_n=\frac12g\left(\frac{F_n^2}{F_{2n}}\right).
\tag{8.4}
$$

Lemma 7.2 therefore gives limits $L_r$ of $v_n$ along each residue $r$; explicitly $L_r=g(C_r^2/C_{2r})/2$. Hold $a\ge2$ fixed and let $n$ tend to infinity in residue $r$ in $U(a,n)=v_a+v_n$. Then

$$
v_a+L_r=g\left(\frac{F_aC_r}{C_{r+a}}\right).
\tag{8.5}
$$

Next let $a$ tend to infinity through residue $t$. The finite set of residue indices makes the denominator index fixed in this limit, and hence

$$
L_t+L_r=g\left(\frac{C_tC_r}{C_{t+r}}\right)
\quad(t,r\in\mathbb Z/p\mathbb Z).
\tag{8.6}
$$

Take $t=0$, meaning the zero residue class, not a gap of length zero. The right side is $g(C_0)$, independent of $r$, so all $L_r$ equal $L_0=:L$. Since $g$ is injective on positive numbers, (8.6) gives

$$
\frac{C_tC_r}{C_{t+r}}=C_0.
\tag{8.7}
$$

Consequently $\chi_r=C_r/C_0$ is a positive multiplicative character of the finite cyclic group: $\chi_{t+r}=\chi_t\chi_r$ and $\chi_0=1$. Each $\chi_r^p=1$, so positivity forces $\chi_r=1$. All $C_r$ therefore have one common value $C$. With finitely many residues this proves the full limits in (8.1).

Equation (8.6) now gives $2L=g(C)$. Letting $n\to\infty$ in (8.5) yields $v_a+L=g(F_a)$; inverting $g$ gives (8.2). Inverting (8.4) and using $U(a,b)=v_a+v_b$ gives (8.3). All arguments of $R$ belong to $[1/4,9/16]\subset(0,1)$, so these inversions are legitimate. $\square$

**Proposition 8.2 (Bulk reward and derivative nondegeneracy).** For $s=2L$,

$$
c=\psi(s)=(1-\sqrt s)^2=c_\star>\frac19,
\qquad \sqrt s<\frac23.
\tag{8.8}
$$

**Proof.** In (6.4), fix a large integer $J$ so that $v_j$ is uniformly close to $L$ for all $j\ge J$. For $J\le j\le n-J$ both arguments are close to $L$, so continuity of $\psi$ makes each bulk summand uniformly close to $\psi(2L)$. At most $2J$ end terms remain; they are bounded because their arguments lie in $[1/4,9/16]$. Divide by $n$, let $n\to\infty$ with $J$ fixed, then let the closeness tend to zero. The number of summands is $n-3$ for $n\ge4$, so

$$
\frac{V(n)}n\longrightarrow\psi(2L).
\tag{8.9}
$$

Since $V(n)+2v_n=cn$ and $v_n$ is bounded, the limit is also $c$. Proposition 6.4 and (2.1) give $c=c_\star\ge1800/12559>1/9$. As $0<\sqrt s<1$, the inequality $(1-\sqrt s)^2>1/9$ implies $\sqrt s<2/3$. This exact inequality will justify a division by a second derivative in §10. $\square$

## 9. An eventually constant score tail is impossible

**Lemma 9.1 (Strict-convexity contradiction).** The sequence $v_n$ cannot be eventually equal to its limit $L$ under the hypothetical attainment assumptions.

**Proof.** If $v_n=L$ for every $n\ge2$, then $V(2)=V(3)=0$ and (6.3) give

$$
2L=W(2)=2c,\qquad 2L=W(3)=3c.
\tag{9.1}
$$

Thus $c=L=0$, contradicting $L\ge1/8$.

Otherwise let $K\ge2$ be the last index with $v_K\ne L$. For $n>2K$, all terms of (6.4) have value $c=\psi(2L)$ except for the two disjoint ends with one index in $\{2,\ldots,K\}$. Therefore

$$
V(n)=(n-3)c+2\sum_{j=2}^K\bigl[\psi(v_j+L)-c\bigr].
\tag{9.2}
$$

Since $v_n=L$ and $W(n)=cn$, the constant

$$
E_0:=2L-3c+2\sum_{j=2}^K\bigl[\psi(v_j+L)-c\bigr]
\tag{9.3}
$$

must be zero. At $n=2K$, the two end lists overlap precisely at $j=K$. Counting that one term exactly instead of as two separate end corrections gives

$$
W(2K)=2Kc+E_0+
\psi(2v_K)-2\psi(v_K+L)+\psi(2L).
\tag{9.4}
$$

The function $\psi$ is strictly convex on positive numbers, since

$$
\psi''(t)=\frac1{2t^{3/2}}>0.
\tag{9.5}
$$

Its arguments $2v_K,2L$ are positive and distinct, and their midpoint is $v_K+L$. Thus the last three terms of (9.4) have strictly positive sum. This contradicts $E_0=0$ and $W(2K)=2Kc$. The count is valid also for $K=2$, when the overlap is the only interior free site at length four; the empty sums at lengths two and three were already retained in (9.1). $\square$

## 10. Infinite deviations force an impossible analytic associativity

**Lemma 10.1 (Exact gap composition forces local associativity).** Suppose $v_n$ is not eventually $L$, and set $x_n=v_n-L$. Define near zero

$$
\phi(x)=\log R(s+x)-\log R(s),\qquad
H(x,y)=\phi^{-1}\bigl(\phi(x)+\phi(y)-\phi(x+y)\bigr),
\tag{10.1}
$$

where $s=2L$ and the inverse is the branch through zero. Then $H$ is well defined and real analytic on a neighborhood of $(0,0)$, $H(x,0)=H(0,x)=0$, and on a neighborhood of $(0,0,0)$ it must satisfy

$$
H(H(x,y),z)=H(x,H(y,z)).
\tag{10.2}
$$

**Proof.** The limits in Lemma 8.1 give $x_n\to0$. Since the sequence is not eventually zero, each tail contains infinitely many distinct values: otherwise finitely many nonzero values would be bounded away from zero, contradicting convergence. Thus every tail-value set has an accumulation point at zero.

For $0<t<1$, $R(t)>0$ is real analytic and

$$
\phi(0)=0,\qquad
A_1:=\phi'(0)=-\frac1{2s(1-\sqrt s)}\ne0.
\tag{10.3}
$$

The real-analytic inverse theorem therefore supplies the inverse branch used in (10.1). Shrink the neighborhood so that $s+x,s+y,s+x+y$ lie in $(0,1)$, the argument of the inverse lies in its domain, and both compositions in (10.2) are defined. Continuity and $H(0,0)=0$ allow such a common neighborhood. Also (10.1) directly gives $H(x,0)=0$ and its symmetric counterpart.

Equations (8.2)–(8.3) are exact identities, so for all $a,b\ge2$,

$$
R(s+x_{a+b})
=\frac{R(s+x_a)R(s+x_b)}{R(s+x_a+x_b)}.
\tag{10.4}
$$

For all sufficiently large $a,b$, every term is in the chosen inverse branch. Taking logarithms and inverting gives

$$
x_{a+b}=H(x_a,x_b).
\tag{10.5}
$$

Choose an index cutoff large enough that all tail values lie in the common neighborhood and (10.5) applies also to pairs involving $a+b$ or $b+c$. For any three indices beyond that cutoff, both sides of (10.2), evaluated at $(x_a,x_b,x_c)$, equal $x_{a+b+c}$.

The difference between the two sides of (10.2) is real analytic on a small product neighborhood. Fix $y=x_b,z=x_c$ in the tail-value set and apply the one-variable identity theorem in $x$ to its infinitely many distinct zeros $x_a$ accumulating at zero. It vanishes for every small $x$. Now fix such an $x$ and $z=x_c$ and apply the theorem in $y$, using all $x_b$. Finally apply it in $z$ for arbitrary fixed small $x,y$. This proves (10.2) throughout that product neighborhood. Exact equality on a product of three infinite sets, rather than an asymptotic fit, is what licenses this conclusion. $\square$

**Lemma 10.2 (Differentiated associativity is incompatible with this loss).** The operation in (10.1) cannot satisfy (10.2) for the value of $s$ in Proposition 8.2.

**Proof.** Put

$$
B_2=\phi''(0),\qquad D_3=\phi'''(0),\qquad
\eta(x)=\partial_2H(x,0)=1-\frac{\phi'(x)}{A_1}.
\tag{10.6}
$$

The last equality follows by differentiating

$$
\phi(H(x,y))=\phi(x)+\phi(y)-\phi(x+y)
\tag{10.7}
$$

once in $y$ at zero, using $H(x,0)=0$. In particular $\eta(0)=0$, $\eta'(0)=-B_2/A_1$ and $\eta''(0)=-D_3/A_1$.

Differentiating associativity (10.2) in its third variable at zero gives

$$
\eta(H(x,y))=\eta(x)\eta(y).
\tag{10.8}
$$

Twice differentiating (10.7) in $y$ at zero gives

$$
A_1H_{yy}(x,0)=B_2\bigl(1-\eta(x)^2\bigr)-\phi''(x).
\tag{10.9}
$$

The same differentiation of (10.8) gives

$$
-\frac{D_3}{A_1}\eta(x)^2-\frac{B_2}{A_1}H_{yy}(x,0)
=-\frac{D_3}{A_1}\eta(x).
\tag{10.10}
$$

The required division by $B_2$ is legitimate. To verify it and the contradiction explicitly, write

$$
F(t)=\log(t^{-1/2}-1),\qquad z=\sqrt t\in(0,1).
$$

Ordinary differentiation yields

$$
F'(t)=-\frac1{2z^2(1-z)},\qquad
F''(t)=\frac{2-3z}{4z^4(1-z)^2}.
\tag{10.11}
$$

Since $\phi(x)=F(s+x)-F(s)$ and $\sqrt s<2/3$ by (8.8), one has $B_2=F''(s)>0$. Thus (10.10) becomes

$$
H_{yy}(x,0)=\frac{D_3}{B_2}\bigl(\eta(x)-\eta(x)^2\bigr).
\tag{10.12}
$$

Substitute in (10.9):

$$
\phi''(x)=B_2-\frac{A_1D_3}{B_2}\eta(x)
+\left(\frac{A_1D_3}{B_2}-B_2\right)\eta(x)^2.
\tag{10.13}
$$

Because $\eta(x)$ is affine in $\phi'(x)$, this asserts that $\phi''$ is a polynomial of degree at most two in $\phi'$, with constant coefficients. No nonzero assumption on $D_3$ was used. Hence on an open interval about $s$ there would be constants $a_0,a_1,a_2$ with

$$
F''(t)=a_0+a_1F'(t)+a_2F'(t)^2.
\tag{10.14}
$$

Insert (10.11) and multiply by the positive denominator $4z^4(1-z)^2$. On an open interval in $z$ this gives the polynomial identity

$$
2-3z=4a_0z^4(1-z)^2-2a_1z^2(1-z)+a_2.
\tag{10.15}
$$

Equality on an open interval forces equality of coefficients. The degree-six coefficient first forces $a_0=0$; the degree-three coefficient then forces $a_1=0$. The remaining constant $a_2$ cannot equal $2-3z$ on an interval. This contradiction proves the lemma. $\square$

**Theorem 10.3 (Uniform finite-hidden renewal nonattainment).** For every finite $N\ge1$ and every $\theta\in\Theta_N$, if the actual visible law $P_\theta$ is proper stationary renewal in the sense of Definition 3.1, then

$$
d(P_\theta)<c_\star.
\tag{10.16}
$$

This quantifies over every gap support initially admitted by that definition and every finite nonnegative representation of the same law, including representations without a rank-one one-emission matrix.

**Proof.** The universal upper bound is (2.2). If equality held, Corollary 4.2 would give full support and the odds band; Theorem 5.1 and Premise 2.3 would give strong zero for the actual posterior. Lemmas 6.2–6.3 and Proposition 6.4 would then give separated scores and additive gap energy with $c=c_\star$. The actual phase-type representation, the band normalization, and Lemmas 7.2–8.1 give a limit $v_n\to L$, allowing all periodic and reducible cases. Proposition 8.2 identifies its score and proves the derivative nondegeneracy. Lemma 9.1 excludes an eventually constant tail. In the remaining case Lemma 10.1 gives analytic associativity, which Lemma 10.2 contradicts. Equality is therefore impossible. $\square$

The word uniform in this theorem refers to the class-wide exclusion quantifiers. The proof gives no positive gap uniform over all finite dimensions or all renewal parameters. Its avoidance constants are law dependent. Strict gaps on fixed whole domains of sizes at most three will follow separately from compact attainment.

## 11. Actual components and the entire domains with at most three states

**Lemma 11.1 (Classwise square-zero legality and actual risk affinity).** For any $\theta\in\Theta_N$, its stationary mass is a finite mixture over positive-weight closed irreducible hidden classes $C$. Let $w_C=\lambda(C)>0$, let $\lambda^C$ be the normalized restriction, and let $M_x^C$ be the restrictions of the emission matrices. Then

$$
\lambda^C>0,\qquad (M_1^C)^2=0,
\qquad P_\theta=\sum_Cw_CP_C,
\qquad d(P_\theta)=\sum_Cw_Cd(P_C),
\tag{11.1}
$$

where $P_C$ is the actual stationary visible law on that class. This is the component and affinity mechanism of [Universal][U], Theorem 5.1, with scalar legality made explicit.

**Proof.** Let $V$ be the states outside all closed irreducible classes of the finite chain $A$. From every state of $V$ there is a positive path into a closed class. Finite maxima of lengths and minima of positive path probabilities give $k\ge1$ and $\eta>0$ such that the chance of leaving $V$ within $k$ steps is at least $\eta$ from every state in $V$. A closed class cannot return to $V$. Stationarity therefore gives $\lambda(V)\le(1-\eta)\lambda(V)$, whence $\lambda(V)=0$.

A closed class has no outgoing entry of $A$. Nonnegativity implies that neither emission matrix has an outgoing entry there. Its normalized stationary row $\lambda^C$ is positive at every state: positive mass at one state propagates along positive paths by stationarity. Thus restriction gives a stationary actual joint law of the form (1.4). In the original joint law the hidden class is chosen with weight $w_C$ and stays fixed, giving the displayed actual mixture. Scalar legality decomposes as

$$
0=\lambda M_1^2\mathbf1
=\sum_Cw_C\lambda^C(M_1^C)^2\mathbf1.
\tag{11.2}
$$

Every summand is nonnegative, so each is zero. The entries of $\lambda^C$ are strictly positive, and the row sums of the nonnegative matrix $(M_1^C)^2$ must consequently all vanish. Therefore $(M_1^C)^2=0$ entrywise. No condition on the original zero-mass states has been inferred.

For completeness, the visible law of each class is ergodic under the one-step shift, including periodic classes. One may realize its hidden and visible process as the finite chain of positive emission triples $(s,x,t)$, with transition

$$
K((s,x,t),(t,y,u))=M_y^C(t,u),\qquad
\rho(s,x,t)=\lambda_s^CM_x^C(s,t).
\tag{11.3}
$$

This chain is irreducible: connect the terminal state of one triple to the initial state of another by an $A$ path, choose a positive emission on each edge, and then take the specified last triple. A finite irreducible stationary Markov chain is shift ergodic even if periodic, and its visible factor is ergodic. A direct justification of the periodic point is as follows. A shift-invariant event has a future-measurable version by approximation with finite cylinders and translating those cylinders into the future. Its conditional probability given the current state is harmonic, hence constant by irreducibility and the maximum principle. Conditioning successively on pasts through time $n$ gives that same constant by the Markov property and invariance. These fields increase to the full path field, so conditional-expectation convergence makes the event's indicator constant and its probability zero or one.

Merge classes with identical visible laws and write the remaining distinct ergodic laws as $R_1,\ldots,R_t$, with positive weights $w_1,\ldots,w_t$. For each finite word $u$, the past frequency

$$
\gamma_u(x)=\lim_{m\to\infty}\frac1m
\sum_{k=|u|}^m\mathbf1_{[u]_0}(T^{-k}x)
\tag{11.4}
$$

uses only negative coordinates. The pointwise ergodic theorem applied to $T^{-1}$ says that under $R_j$ it equals $R_j([u]_0)$ almost surely. There are countably many words, and distinct probability laws differ on some cylinder. Thus the joint frequency values determine pairwise disjoint events $E_j\in\mathcal E_0$ with $R_j(E_j)=1$; other components give them mass zero. This is an exterior-measurable actual visible label, without a mixing or aperiodicity assumption.

Let $q_0$ be the full-exterior posterior of the mixture. For every $A\in\mathcal E_0$,

$$
0=\int_{A\cap E_j}(X_0-q_0)\,dP_\theta
=w_j\int_A(X_0-q_0)\,dR_j.
\tag{11.5}
$$

So this same $q_0$ is a posterior under each $R_j$. Integrating its squared residual and using (2.2) gives affinity of $d$. Unmerging identical visible laws proves (11.1). This is an assertion about infinite-exterior risk; finite-window risk need not be affine under mixtures. $\square$

**Proposition 11.2 (Every positive renewal or zero component forces strictness).** In every finite dimension, if any positive-weight actual hidden recurrent component has a proper renewal visible law, or the all-zero visible law, then $d(P_\theta)<c_\star$. In particular a presentation whose every positive component has a rank-one one-emission matrix, or emits only zeros, is excluded.

**Proof.** The renewal component is strict by Theorem 10.3. The all-zero component has $d=0<c_\star$ by (2.1)–(2.2). Every other component has density at most $c_\star$. The actual affinity (11.1) and the positive weight of the strict component make the whole average strictly less than $c_\star$. Proposition 3.4 proves the assertion about rank-one components. $\square$

**Proposition 11.3 (Compact attainment and finite separation on the whole domain).** For every finite $N$, $C_N$ is attained and

$$
C_N=\inf_{r\ge1}U_{N,r}\le c_\star.
\tag{11.6}
$$

Moreover

$$
C_N<c_\star
\quad\Longleftrightarrow\quad
\exists r,m\ge1:\ U_{N,r}<\frac{\kappa_m}{m+1}.
\tag{11.7}
$$

These are [Universal][U], Theorem 6.2's whole-domain statements.

**Proof.** The domain $\Theta_N$ is nonempty: take $M_0=I$, $M_1=0$ and any probability row. All its coordinates lie in $[0,1]$, and its defining polynomial equalities and inequalities are closed. Hence it is compact. Each finite cylinder probability is a polynomial in the parameters by (1.4). The function $h$ is continuous even at $(0,0)$, where $0\le h(s,t)\le(s+t)/4$. Formula (2.2) therefore makes $D_r(P_\theta)$ continuous on the entire domain, including every zero-mass boundary point. Each $U_{N,r}$ is attained and the sequence decreases with $r$.

Let $U=\lim_rU_{N,r}$, choose a maximizing $\theta_r$ for each $r$, and take a convergent subsequence $\theta_{r_j}\to\theta_*$ with $r_j\to\infty$. For fixed $k$ and all sufficiently large $j$,

$$
D_k(P_{\theta_{r_j}})\ge D_{r_j}(P_{\theta_{r_j}})=U_{N,r_j}.
\tag{11.8}
$$

Continuity gives $D_k(P_{\theta_*})\ge U$ for every $k$, so (2.2) gives $d(P_{\theta_*})\ge U$. Conversely every $\theta$ satisfies $d(P_\theta)\le D_k(P_\theta)\le U_{N,k}$ for every $k$, hence $d(P_\theta)\le U$. This proves attainment and (11.6), without a continuity assumption on $d$.

If $C_N<c_\star$, choose $r$ with $U_{N,r}<c_\star$ and then $m$ with $U_{N,r}<\kappa_m/(m+1)$ by (2.1). Conversely any such pair gives $C_N\le U_{N,r}<\kappa_m/(m+1)\le c_\star$. Thus (11.7) holds. In this case the entire domain obeys the positive bound

$$
c_\star-d(P_\theta)\ge\frac{\kappa_m}{m+1}-U_{N,r}>0.
\tag{11.9}
$$

An attaining law would automatically have full visible support by (2.4). Zero stationary states allow padding a smaller presentation by adding isolated deterministic-zero self-loops with initial mass zero. Therefore the existence statements for at most $N$ states and for the complete $\Theta_N$ agree. $\square$

**Theorem 11.4 (Full-original-domain three-state separation).** On exactly the domains (1.3),

$$
C_1=0,\qquad C_2\le C_3<c_\star.
\tag{11.10}
$$

For each $N\in\{1,2,3\}$ there exist finite integers $r,m\ge1$ satisfying

$$
U_{N,r}<\frac{\kappa_m}{m+1}.
\tag{11.11}
$$

**Proof.** Let $Q$ be a nonnegative square-zero matrix on a class of size $d\le3$. Let $S$ be its nonzero-row indices and $T$ its nonzero-column indices. If $j\in S\cap T$, some $Q_{ij}>0$ and $Q_{jk}>0$, so $(Q^2)_{ik}\ge Q_{ij}Q_{jk}>0$, a contradiction. Thus $S\cap T=\varnothing$, and every nonzero entry lies in $S\times T$. If $Q\ne0$, both sets are nonempty and $|S|+|T|\le d\le3$, whence $\min(|S|,|T|)\le1$. Its rank is at most this minimum and at least one, so it is rank one with the nonnegative factorization (3.5).

Apply this to $Q=M_1^C$ in each positive hidden class of an arbitrary $\theta\in\Theta_N$ with $N\le3$, using Lemma 11.1. If $Q=0$, that component emits only zeros. If $Q\ne0$, it is rank one and Proposition 3.4 makes its actual visible law proper renewal. Proposition 11.2 consequently excludes attainment for every parameter in each entire $\Theta_N$, $N\le3$. Reducible and periodic presentations and zero-mass states are still included.

Proposition 11.3 now turns this pointwise exclusion into $C_N<c_\star$: an attained maximum equal to $c_\star$ would contradict that exclusion. Its finite separation equivalence gives (11.11). For $N=1$, normalization makes $\lambda=1$ and scalar legality is $M_1^2=0$, so $M_1=0$ and every law is all-zero. Hence $C_1=0$. Finally the zero-mass padding described in Proposition 11.3 embeds $\Theta_2$ into $\Theta_3$ without changing any visible probability, proving $C_2\le C_3$. No separation pair or numerical gap value is specified. $\square$

## 12. The four-state structural boundary and remaining original problem

**Example 12.1 (A legal irreducible four-state nonrenewal law).** Choose exact reals $0<p,q<1$ with $p\ne q$. In this example $p,q$ are parameters. Put

$$
M_0=\begin{pmatrix}
1-p&0&0&0\\
0&1-q&0&0\\
0&1&0&0\\
1&0&0&0
\end{pmatrix},\qquad
M_1=\begin{pmatrix}
0&0&p&0\\
0&0&0&q\\
0&0&0&0\\
0&0&0&0
\end{pmatrix},
\tag{12.1}
$$

$$
Z=\frac1p+\frac1q+2,\qquad
\lambda=\frac1Z\left(\frac1p,\frac1q,1,1\right).
\tag{12.2}
$$

These parameters belong to $\Theta_4$, with irreducible $A=M_0+M_1$, $M_1^2=0$ and $\operatorname{rank}M_1=2$. Their actual visible law is not renewal.

**Proof.** Every row of $A$ sums to one. The positive cycle $1\to3\to2\to4\to1$ connects all states, proving irreducibility. The four stationary coordinate equations are

$$
\begin{aligned}
(\lambda A)_1&=Z^{-1}\bigl((1-p)/p+1\bigr)=1/(pZ),\\
(\lambda A)_2&=Z^{-1}\bigl((1-q)/q+1\bigr)=1/(qZ),\\
(\lambda A)_3&=Z^{-1}(p/p)=1/Z,\qquad
(\lambda A)_4=Z^{-1}(q/q)=1/Z.
\end{aligned}
\tag{12.3}
$$

The matrix $M_1$ has nonzero rows only at states $1,2$ and nonzero columns only at states $3,4$, where its rows are zero. Thus $M_1^2=0$. Its two nonzero rows are independent, so its rank is two.

Each of the two one-emitting edges has stationary flow $1/Z$. Under the Palm law at a one, their phases therefore have equal weights. After a one along $1\to3$, the next bit is a forced zero along $3\to2$, followed by zeros in state $2$ until a one with probability $q$ at each trial. After a one along $2\to4$, the forced zero leads to state $1$, where the waiting parameter is $p$. The phases alternate at successive ones. Conditional on the phase, the successive waits use fresh Markov transitions and have gap laws

$$
f_p(g)=p(1-p)^{g-2},\qquad
f_q(g)=q(1-q)^{g-2},\qquad g\ge2.
\tag{12.4}
$$

Consequently a Palm gap has $P^1(G=2)=(p+q)/2$, whereas two successive Palm gaps satisfy

$$
P^1(G_1=2,G_2=2)=pq,
\qquad
pq-\left(\frac{p+q}{2}\right)^2=-\frac{(p-q)^2}{4}<0.
\tag{12.5}
$$

The gaps are not independent, so the visible law is nonrenewal. This is an exact symbolic dependence calculation within (1.4). It asserts no attainment or nonattainment for this example; its purpose is to show that scalar legality and classwise square-zero do not force the rank-one renewal reduction in size four. $\square$

**Corollary 12.2 (Necessary structure of a finite attainer).** If some finite $\theta\in\Theta_N$ attains $c_\star$, every positive-weight actual closed irreducible hidden component must itself attain, must have at least four states, must have $\operatorname{rank}M_1^C\ge2$, and must have a nonrenewal visible law. Zero stationary states may remain in the original presentation.

**Proof.** The affinity in Lemma 11.1 and the common upper bound force every positive component to attain. A zero-emission component is all-zero and cannot attain. A nonzero rank-one component is proper renewal by Proposition 3.4 and is excluded by Theorem 10.3; any proper renewal component is excluded regardless of the rank of its representation. Theorem 11.4 excludes class sizes at most three. These implications give all the stated necessary conditions. $\square$

**Open Problem 12.3 (All original dimensions at least four and matrix-valued continuation).** The full alternative (1.7), equivalently the all-$N$ separation alternative (1.8), is unresolved here. For a general fixed $N\ge4$, this volume proves neither $C_N<c_\star$ nor existence of an attaining parameter. The necessary conditions in Corollary 12.2 are not sufficient conditions for attainment.

Two obligations remain distinct. First, no theorem here gives $A_P<\infty$ for arbitrary finite-hidden nonrenewal laws or for every hypothetical nonrenewal attainer. Finite-state avoidance can bound the probability of a long zero word, but the localization equality (5.3) used the actual renewal posterior: a visible one does not in general erase the hidden phase. Second, even if the root sum is paid for a nonrenewal law and Direct supplies strong zero, the ensuing matrix-valued dependence across adjoining gaps has not been reduced to, or solved by, the scalar composition identity (10.4).

The existence of the finite pairs in (11.11) is nonconstructive. No values of those pairs, numerical low-dimensional gap, parameter-uniform renewal tail constant, optimizer-rank growth, or common stationary realization of the separate finite optimizers is obtained. Finite hidden memory is never identified with finite visible Markov order. The cocycle is used on its saturated conull finite-modification relation; no continuous extension to every legal configuration is asserted.

## 13. Mathematical attribution and exact supplier boundaries

The original optimization and attained-law facts belong to Universal; the conditional attainment-to-strong-zero implication belongs to Direct. Renewal supplies the credited nearest-anchor and retained-reset mechanisms in a particular three-state law. Propositions 3.4 and 4.1 and Theorem 5.1 establish the required versions for the entire renewal class. The special parameter inequalities, determinant, rank discrepancy and finite-radius comparison of that particular law are not hypotheses of Theorem 10.3 or substitutes for the original domains in Theorem 11.4.

| Canonical source | Exact mathematical use and boundary |
| --- | --- |
| **Universal:** [*FIB 合法边调和负载：普适后验缺陷与有限隐藏维数分离*][U] | Convention 1.3 and Lemma 2.1 own the original finite optimization and growth interfaces; equation (1.5) owns density as actual full-exterior risk; Theorem 3.1 gives the band and support for every attainer; Proposition 7.1 gives $c_\star\ge1800/12559$. Definition 4.1 and Proposition 4.2 fix the entire exact-real domain and actual joint law. Theorem 5.1 owns the actual-component posterior transfer and risk affinity, and Theorem 6.2 owns compact attainment and finite separation. The relevant realization, component and compactness arguments are recalled in Propositions 1.3 and 11.3 and Lemma 11.1. |
| **Direct:** [*FIB harmonic-edge load: attainment, strong-zero equivalence and finite-optimizer comparison*][D] | Definition 1.3 fixes both one-sided fields and zero-offset errors. Theorem 1.5 is consumed only after Theorem 5.1 pays its same-law root sum and only under actual attainment. Its original-posterior, saturation, surgery and version boundary is exactly Premise 2.3. The guarded converse and finite-hidden rank consumer are not additional premises of the uniform contradiction. |
| **Renewal:** [*FIB harmonic-edge load: renewal reset-variance blindness and minimal hidden dimension*][R] | Theorem 5.1 supplies the credited nearest-anchor factorization mechanism, and Theorem 10.2 the retained-reset proof of the two erasure tails including both seam terms. Their extensions are proved directly here. Its special three-state example's nonattainment does not itself prove $C_3<c_\star$. |

**Boundary 13.1 (Uninspected nested mathematical premises).** Universal's inherited dependencies are the canonical [Growth constant][Ug], [Positive unique optimizer][Uo], [Full-support stationary attainment][Us], [Ergodic full-support stationary attainment][Ue], [Finite visible memory nonattainment][Un] and [Finite visible memory completeness][Uc] sources. Their bodies remain uninspected, and their conclusions are used only through the explicitly stated Universal interfaces. The finite visible memory statements are not used as a general finite-hidden exclusion.

Direct's forward bridge retains [Exterior localization and actual loss-cocycle balance][De], Theorem 3.1, together with the general stationary-law scope in [Guarded replacement, attainment and conditional-rank obstruction][Dg], Lemma 2.2. These are the uninspected compatible-fiber positivity, nonsingular replacement, absolute cocycle and fixed-version/saturated-domain premises identified in Premise 2.3. Direct also references [Second-order loss localization and local tilt averaging obstruction][Ds] and [One-sided erasure summability and output-filter boundaries][Dt]. Their bodies are uninspected; the present application imports neither a second-order continuation nor a general filtering theorem. In particular Direct's one-sided erasure source is distinct from Renewal. Renewal's [Guarded][Dg] and [Global and local rank compatibility and the reset-variance obstruction][Rg] dependencies are likewise uninspected and supply no additional premise for the uniform proof here. These dependency statements delimit the handwritten theorem; they do not independently certify those nested results.

**Boundary 13.2 (Classical tools and the mathematical increment).** The finite nonnegative phase-type representation, Frobenius block form, cyclic Perron–Frobenius peripheral-spectrum theorem and finite-dimensional Jordan expansion are classical. Lemma 7.2 states their useful-block, periodic and reducible application explicitly; boundedness, not an assumed asymptotic cancellation, removes leading polynomial terms. Conditional expectation as projection, tower identities, uniqueness from finite cylinders, Tonelli and stationary mass transport are classical; their particular uses are proved above. Finite irreducible shift ergodicity and the pointwise ergodic theorem support the actual visible component label in Lemma 11.1, as in Universal's use of Gray's *Probability, Random Processes, and Ergodic Properties*. The real-analytic inverse and identity theorems are used with the nonzero first derivative and accumulating exact identities proved in Lemma 10.1. Strict convexity, differentiation and polynomial coefficient comparison complete the contradiction.

Conditional Brier scoring is classical, as credited in Direct and Renewal to Dawid, Lauritzen and Parry, *Proper Local Scoring Rules on Discrete Sample Spaces*, §4.2. No additional proper-scoring theorem is required here. These classical attributions do not certify external document bodies or claim a literature search or priority.

The repo-derived mathematical increment is the combination of the universal renewal contradiction in Theorem 10.3 and its exact whole-domain consequence in Theorem 11.4. It depends on the declared supplier premises, with the full support, actual erasure tails, score identities, periodic-tail collapse, derivative nondegeneracy and low-dimensional reduction proved at their stated quantifiers. It is a handwritten result, not a claim of formal verification. The general nonrenewal and all-dimension questions remain exactly those in Open Problem 12.3.

[U]: FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md
[D]: FIB_LEGAL_EDGE_LOAD_ATTAINMENT_STRONG_ZERO_EQUIVALENCE_AND_FINITE_OPTIMIZER_COMPARISON.md
[R]: FIB_LEGAL_EDGE_LOAD_RENEWAL_RESET_VARIANCE_BLINDNESS_AND_MINIMAL_HIDDEN_DIMENSION.md
[Ug]: FIB_LEGAL_EDGE_LOAD_GROWTH_CONSTANT.md
[Uo]: FIB_LEGAL_EDGE_LOAD_POSITIVE_UNIQUE_OPTIMIZER.md
[Us]: FIB_LEGAL_EDGE_LOAD_FULL_SUPPORT_STATIONARY_ATTAINMENT.md
[Ue]: FIB_LEGAL_EDGE_LOAD_ERGODIC_FULL_SUPPORT_STATIONARY_ATTAINMENT.md
[Un]: FIB_LEGAL_EDGE_LOAD_FINITE_VISIBLE_MEMORY_NONATTAINMENT.md
[Uc]: FIB_LEGAL_EDGE_LOAD_FINITE_VISIBLE_MEMORY_COMPLETENESS.md
[De]: FIB_LEGAL_EDGE_LOAD_EXTERIOR_LOCALIZATION_AND_ACTUAL_LOSS_COCYCLE_BALANCE.md
[Dg]: FIB_LEGAL_EDGE_LOAD_GUARDED_REPLACEMENT_ATTAINMENT_AND_CONDITIONAL_RANK_OBSTRUCTION.md
[Ds]: FIB_LEGAL_EDGE_LOAD_SECOND_ORDER_LOSS_LOCALIZATION_AND_LOCAL_TILT_AVERAGING_OBSTRUCTION.md
[Dt]: FIB_LEGAL_EDGE_LOAD_ONE_SIDED_ERASURE_SUMMABILITY_AND_OUTPUT_FILTER_BOUNDARIES.md
[Rg]: FIB_LEGAL_EDGE_LOAD_GLOBAL_LOCAL_RANK_COMPATIBILITY_AND_RESET_VARIANCE_OBSTRUCTION.md

## 追加锚（本行以下为增补区）
