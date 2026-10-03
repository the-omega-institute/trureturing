# Statistical Laws from FIB ATOM Recursion

## 1. Common source and observation coordinates

**Definition 1.1 (Ordered source trees and native recursion).** Let $\mathcal T$ be the nonempty free ordered full binary-tree algebra
$$
t ::= \alpha\mid\beta\mid\langle t,t\rangle .
$$
Define the substitution $\rho:\mathcal T\to\mathcal T$ by
$$
\rho(\alpha)=\beta,\qquad
\rho(\beta)=\langle\beta,\alpha\rangle,\qquad
\rho(\langle s,t\rangle)=\langle\rho(s),\rho(t)\rangle .
$$
Put $T_j=\rho^j(\alpha)$ and let $w(t)$ be the left-to-right leaf word of $t$. The leaf composition is
$$
c(\alpha)=(1,0),\qquad c(\beta)=(0,1),\qquad c(\langle s,t\rangle)=c(s)+c(t).
$$
Write
$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad q(a,b)=2a+3b .
$$
The source identities are $c(\rho t)=Mc(t)$, $M^2=M+I$, and $q(c(T_j))=F_{j+3}$ for $F_0=0,F_1=1$. The quantity $q$ is a readout of composition; it is not a probability and the iteration index $j$ is not a stochastic clock.

Citation: [*Fibonacci Atomic Relation Generation*](https://github.com/the-omega-institute/trureturing/blob/4ab7dd1d2631b0a0859643815bcc2c442ce34e32/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md), Definitions 2.1, 3.1, 3.3 and Theorems 3.2, 3.4, 5.4 and 8.2.

**Definition 1.2 (Ordered words and two languages).** Let $\tau$ be the Fibonacci word substitution
$$
\tau(\alpha)=\beta,\qquad \tau(\beta)=\beta\alpha,
$$
extended by concatenation. Then $w(\rho t)=\tau(w(t))$. Let $X_\tau\subset\{\alpha,\beta\}^{\mathbb Z}$ be the two-sided subshift whose finite factors occur in the nested words $\tau^n(\beta)$, and let
$$
X_M=\{x\in\{\alpha,\beta\}^{\mathbb Z}:\text{the factor }\alpha\alpha\text{ never occurs}\}
$$
with shift $\sigma$. Thus $X_\tau\subseteq X_M$; the inclusion is a language restriction and does not identify the two systems. For a stationary law $\nu$ on either space, write $\nu[u]$ for the cylinder probability of a word $u$ at the origin and $h(\nu)$ for entropy per symbol with natural logarithms.

Citation: [J. Berstel, *Sturmian and Episturmian Words*](https://ligm.univ-eiffel.fr/~berstel/Articles/2007SturmianThessalonique.pdf), §§2–3.

**Definition 1.3 (Three indices and empty windows).** Encode $\alpha=1$ and $\beta=0$. For a binary path $C=(C_j)_{j\in\mathbb Z}$ and integers $s\in\mathbb Z$, $n,k\ge0$, put
$$
A_{s,n}=\sum_{j=s}^{s+n-1}C_j,
\qquad
Q_{s,n}^{(k)}=qM^k\binom{A_{s,n}}{n-A_{s,n}} .
$$
The generation $k$, spatial window length $n$, and spatial position $s$ are distinct indices. When $n=0$, the sum and composition are zero; this convention introduces no empty member of $\mathcal T$.

**Hypothesis 1.4 (Sampling and dynamics contracts).** A spatial occurrence experiment chooses a leaf-window uniformly among all positions in $w(\rho^n t)$ for fixed nonempty $t$. A stationary symbolic experiment chooses a stationary law on $X_M$ or $X_\tau$ and then a cylinder at the origin. A transport experiment chooses positive edge resistances $r_\alpha,r_\beta$, a jump scale $0<\theta\le\min(r_\alpha,r_\beta)/2$, and a physical time unit $\delta>0$; it uses the Markov chain specified in Definition 5.1 below. A controlled boundary experiment uses the encoding and swaps of Definition 6.1 together with the initial law, stochastic kernel and action contract of Hypothesis 6.2. These probability laws, permissions, boundary conditions and clocks are additional hypotheses. The recursion itself selects none of them.

## 2. Fibers, measures and exact occurrence laws

**Definition 2.1 (Composition fibers).** For $a,b\ge0$ with $L=a+b\ge1$, put
$$
\mathcal F(a,b)=\{t\in\mathcal T:c(t)=(a,b)\},
\qquad
C_j=\frac1{j+1}\binom{2j}{j},
$$
and let $U(a,b)$ be the uniform law on this finite fiber. For a probability $\mu$ on a fiber, its quantity observation at generation $n$ is the random variable $q(M^n c(t))$.

**Theorem 2.2 (Exact hidden fibers and failure of uniform genealogical transport).** The fiber cardinality is
$$
N(a,b)=|\mathcal F(a,b)|=C_{L-1}\binom La .
$$
Every probability on $\mathcal F(a,b)$ has the same complete quantity trajectory $q(M^n(a,b))$. Nevertheless,
$$
\operatorname{TV}\bigl(\rho_*U(a,b),U(b,L)\bigr)
 =1-\frac{N(a,b)}{N(b,L)},
\qquad
N(b,L)=C_{L+b-1}\binom{L+b}{b}.
$$
For $L\ge2$ this is at least $1-2^{-b}$, and for $(a,b)=(1,1)$ it is $2/3$. For every nonempty initial fiber,
$$
\operatorname{TV}\bigl((\rho^n)_*U(a,b),U(M^n(a,b))\bigr)\longrightarrow1,
$$
although the two laws have identical composition and quantity observations at every generation.

**Proof.** A leaf word with $a$ occurrences of $\alpha$ and $b$ occurrences of $\beta$ has $C_{L-1}$ ordered full binary bracketings, and there are $\binom La$ choices of the $\alpha$ positions. This proves the first formula; it is the Catalan count in R. P. Stanley, [*Enumerative Combinatorics, Volume 2*](https://doi.org/10.1017/CBO9780511609589), §6.2. The identity $c(\rho t)=Mc(t)$ makes the whole quantity trajectory constant on each fiber.

The map $\rho$ is injective. No image is the leaf $\alpha$; the images $\beta$ and $\langle\beta,\alpha\rangle$ decode to $\alpha$ and $\beta$; and any other image pair decodes recursively. The image of a pair cannot equal $\langle\beta,\alpha\rangle$ because its right child is itself an image, whereas $\alpha$ is not. Hence $(\rho_*U(a,b))$ is uniform on a subset of the target fiber with exactly $N(a,b)$ elements. The total variation from the uniform law on the whole target fiber is therefore one minus the subset fraction.

For $L\ge2$, each ratio $C_{j+1}/C_j=(4j+2)/(j+2)$ with $j\ge1$ is at least $2$, and, since $a=L-b$, the binomial ratio $\binom{L+b}{b}/\binom{L}{a}=\binom{L+b}{b}/\binom{L}{b}$ is at least one. Thus the target-to-source ratio is at least $2^b$. For $(1,1)$ the source and target fibers have sizes $2$ and $6$. The two words $\alpha\alpha\beta\beta$ and $\alpha\beta\alpha\beta$, bracketed by the same ordered shape, have the same composition and all future quantity values but are separated by the occurrence of $\alpha\alpha$. Under iteration the same subset formula holds with $(a,b)$ replaced by $M^n(a,b)$. The $\beta$ coordinate eventually grows without bound, so the target-to-image ratio diverges and the variation tends to one. This is a statement about genealogical tree laws; it does not contradict convergence of spatial occurrence frequencies. $\square$

**Definition 2.3 (Occurrence law, pressure law and normalized inflation).** Let $\mu_F$ denote the stationary occurrence law obtained by choosing a spatial window uniformly in $w(\rho^n t)$ and passing to the limit. For a stationary law $\nu$ on $X_M$, put $p=\nu[\alpha]$ and define the normalized variable-length inflation
$$
(R\nu)(B)=\frac1{2-p}\int\sum_{k=0}^{|\tau(x_0)|-1}{\bf1}_B(\sigma^k\tau(x))\,d\nu(x).
$$
The denominator is $\nu[\alpha]+2\nu[\beta]=2-p$. For the alternative pressure experiment, weight each legal length-$m$ word $u$ in $X_M$ by $\exp(\vartheta N_\alpha(u))$, where $N_\alpha$ counts $\alpha$ and
$$
Z_m(\vartheta)=\sum_{|u|=m,\ u\text{ legal}}\exp(\vartheta N_\alpha(u)).
$$

**Theorem 2.4 (Occurrence law, exact short-observation fiber and incompatible pressure law).** The occurrence law $\mu_F$ exists for every fixed nonempty initial tree and is independent of that tree. Put
$$
\varphi=\frac{1+\sqrt5}{2},\qquad p=\varphi^{-2},\qquad r=\varphi^{-3}=1-2p.
$$
Then
$$
\mu_F[\alpha]=p,\quad \mu_F[\beta]=1-p,
\quad \mu_F[\alpha\beta]=\mu_F[\beta\alpha]=p,
\quad \mu_F[\beta\beta]=r,
$$
with $\mu_F[\alpha\alpha]=0$. Among all stationary laws on $X_M$ having these one- and two-letter observations, the possible triple vector, in the order
$$
(\alpha\beta\alpha,\alpha\beta\beta,\beta\alpha\beta,\beta\beta\alpha,\beta\beta\beta),
$$
is exactly
$$
(3p-1+e,\ r-e,\ p,\ r-e,\ e),\qquad 0\le e\le r.
$$
The occurrence law has $e=0$. The pressure law with transfer matrix
$$
W_\vartheta=\begin{pmatrix}0&1\\e^\vartheta&1\end{pmatrix}
$$
has pressure $P(\vartheta)=\log\lambda_\vartheta$, where
$$
\lambda_\vartheta=\frac{1+\sqrt{1+4e^\vartheta}}2.
$$
At $\vartheta=3\log\varphi$, its stationary Markov law has the same one- and two-letter observations but $e=\varphi^{-5}$ and is the unique entropy maximizer under those observations. Moreover, $h(\mu_F)=0$.

**Proof.** The ordered word recurrence is $\tau^n(\beta)=\tau^{n-1}(\beta)\tau^{n-2}(\beta)$ and its lengths are Fibonacci numbers. For any fixed word $u$ of length $m$, its occurrence count $A_n$ in these words satisfies
$$
A_n=A_{n-1}+A_{n-2}+\varepsilon_n,\qquad0\le\varepsilon_n\le m-1.
$$
After division by the corresponding lengths, the differences satisfy
$$
|d_n-d_{n-1}|\le\tfrac12|d_{n-1}-d_{n-2}|+\frac{m-1}{F_{n+2}}.
$$
The forcing term is summable, so every cylinder frequency converges. A fixed finite tree produces finitely many substituted blocks; the fraction of windows crossing their boundaries tends to zero, so the same limit is obtained for every initial tree. The Fibonacci gap-frequency calculation gives $p=\varphi^{-2}$. The forbidden factors are $\alpha\alpha$ and $\beta\beta\beta$; stationarity gives the displayed pair probabilities.

For an arbitrary stationary law with the same pairs, the factor $\beta\alpha$ must be followed by $\beta$. Balancing the incoming and outgoing pair counts gives the displayed triple vector, with $e=\nu[\beta\beta\beta]$. Positivity is exactly $0\le e\le r$. Every value occurs: the mixture of the two shifts of $(\alpha\beta)^\infty$ and the point mass on $\beta^\infty$, with weights $2p$ and $r$, has the required pairs and $e=r$; mixing this endpoint with $\mu_F$ fills the interval.

For the pressure calculation, diagonalizing $W_\vartheta$ gives the stated eigenvalue and pressure. The associated normalized kernel and stationary vector are
$$
K_\vartheta=\begin{pmatrix}0&1\\(\lambda_\vartheta-1)/\lambda_\vartheta&1/\lambda_\vartheta\end{pmatrix},
\qquad
\pi_\vartheta=\left(\frac{\lambda_\vartheta-1}{2\lambda_\vartheta-1},\frac{\lambda_\vartheta}{2\lambda_\vartheta-1}\right).
$$
At $\vartheta=3\log\varphi$ one has $\lambda_\vartheta=\varphi^2$, $\pi_\vartheta=(p,1-p)$, and $K_\vartheta(\beta,\alpha)=\varphi^{-1}$, $K_\vartheta(\beta,\beta)=\varphi^{-2}$. Thus $\nu_*[\beta\beta\beta]=(1-p)\varphi^{-4}=\varphi^{-5}$. The conditional-entropy bound
$$
h(\nu)\le H_\nu(X_1\mid X_0)=(2-3p)\log\varphi
$$
for the fixed pair table is attained only when all conditional distributions equal this kernel, proving uniqueness of the maximizer. Choose $n$ minimally with $|\tau^n(\alpha)|\ge m$. Both $|\tau^n(\alpha)|$ and $|\tau^n(\beta)|$ are then below $3m$, and every legal length-$m$ factor occurs inside at most two consecutive substituted blocks. The four possible block pairs supply at most $24m$ factors, so the block entropy is at most $\log(24m)$ and $h(\mu_F)=0$.

Finally, unweighted path counting on $X_M$ has boundary density $F_m/F_{m+2}\to p$ but stationary bulk density $1/(1+\varphi^2)$; a boundary count therefore does not identify a stationary occurrence law. The pressure and occurrence laws are two measures on the same adjacency carrier with different higher cylinders. The pressure and entropy steps use W. Parry, [*Intrinsic Markov chains*](https://doi.org/10.1090/S0002-9947-1964-0161372-1), §§3–4, as a cited Perron–Parry ingredient. $\square$

**Theorem 2.5 (Normalized inflation preserves short observations and selects the occurrence law).** For every stationary $\nu$ on $X_M$, $R\nu$ is stationary and
$$
(R\nu)[\alpha]=\frac{1-p}{2-p},
\qquad (R\nu)[\beta\beta\beta]=0.
$$
If $p=\varphi^{-2}$, $R$ preserves the singleton and pair table in Theorem 2.4. For the pressure law $\nu_*$, the triple projection of $R\nu_*$ differs from that of $\nu_*$ by total variation $2\varphi^{-5}$. For every stationary $\nu$,
$$
R^n\nu\Longrightarrow\mu_F,
$$
and $\mu_F$ is the unique stationary fixed point of $R$.

**Proof.** The defining integral has mass one because the expected output block length is $2-p$. For a bounded cylinder function $f$, the difference between the shifted and unshifted output integrals telescopes to
$$
\int\left(f(\sigma^{|\tau(x_0)|}\tau(x))-f(\tau(x))\right)d\nu(x)
=\int\left(f(\tau(\sigma x))-f(\tau(x))\right)d\nu(x)=0,
$$
so $R\nu$ is stationary. Every input $\beta$ produces exactly one output $\alpha$, proving the singleton formula. An output factor $\beta\beta\beta$ would require two adjacent input $\alpha$ symbols, which are forbidden in $X_M$, so its probability is zero. At $p=\varphi^{-2}$, the equation $(1-p)/(2-p)=p$ holds and stationarity plus exclusion of $\alpha\alpha$ fixes the pair table. Theorem 2.4 then gives the triple difference and its variation.

Inductively, descendant-position counting gives
$$
R^n\nu(B)=\frac1{D_n}\int\sum_{k=0}^{|\tau^n(x_0)|-1}{\bf1}_B(\sigma^k\tau^n(x))d\nu(x),
\qquad D_n=\mathbb E_\nu|\tau^n(x_0)|.
$$
For a fixed cylinder of length $m$, at most $m-1$ positions per substituted block cross a block boundary. All other positions lie inside a copy of $\tau^n(\alpha)$ or $\tau^n(\beta)$, whose internal frequencies converge to $\mu_F$; the boundary fraction is at most $(m-1)/\min(|\tau^n(\alpha)|,|\tau^n(\beta)|)$ and tends to zero. Thus every cylinder converges to $\mu_F$. Continuity of $R$ on stationary laws gives $R\mu_F=\mu_F$, and a fixed law must equal the limit of its iterates. $\square$

Citation: the source occurrence and gap-frequency background is [*Fibonacci Atomic Relation Generation*](https://github.com/the-omega-institute/trureturing/blob/4ab7dd1d2631b0a0859643815bcc2c442ce34e32/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md) and [*Recursive Relational Observation*](https://github.com/the-omega-institute/trureturing/blob/4ab7dd1d2631b0a0859643815bcc2c442ce34e32/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md), Theorem 20.9. In the latter source, Theorems 33.9–33.10 distinguish natural boundary and stationary maximum-entropy laws, while Proposition 71.8 supplies legal-prefix counting and natural-boundary-measure background.

## 3. Joint windows and fluctuation laws

**Hypothesis 3.1 (Common phase and anchored reconstruction).** Let $a=\varphi^{-2}$ and let $U$ be uniform on $[0,1)$. Define the Fibonacci phase path
$$
C_j(U)=\lfloor U+(j+1)a\rfloor-\lfloor U+ja\rfloor .
$$
For comparison, let $C$ have the stationary Markov law
$$
P_p=\begin{pmatrix}1-p&p\\1&0\end{pmatrix},\qquad
\pi_p=\left(\frac1{1+p},\frac p{1+p}\right),\qquad0\le p\le1.
$$
Both paths forbid $11$, but only the phase path is supported on the Fibonacci substitution language. Independently choose a fair bit $B$, let $x_0=B$ and
$$
 x_{j+1}=x_j\mathbin{\oplus}(1-C_j),\qquad S_j=(-1)^{x_j}.
$$
The common phase, path law and fair anchor are hypotheses; they are not consequences of $\rho$.

**Theorem 3.2 (Exact common-phase transport).** Put $\theta_n=\{na\}$, $J_t=[1-t,1)$ for $0<t<1$ and $J_0=\varnothing$. For the phase ensemble,
$$
A_{s,n}=\lfloor na\rfloor+{\bf1}_{J_{\theta_n}}(\{U+sa\}),
\qquad
Q_{s,n}^{(k)}=F_{k+4}n-F_{k+2}A_{s,n}.
$$
For any two windows and generations,
$$
\operatorname{Cov}\bigl(Q_{s,n}^{(k)},Q_{t,m}^{(\ell)}\bigr)
=F_{k+2}F_{\ell+2}
\left[\lambda\bigl(J_{\theta_n}\cap(J_{\theta_m}-(t-s)a)\bigr)-\theta_n\theta_m\right],
$$
where $\lambda$ is circle length. For one window the generation covariance matrix is rank at most one:
$$
\operatorname{Cov}\bigl(Q^{(k)},Q^{(\ell)}\bigr)
=F_{k+2}F_{\ell+2}\theta_n(1-\theta_n).
$$
For windows $(s_i,n_i)$ and $e_i\in\{0,1\}$, the joint probability of
$$
A_{s_i,n_i}=\lfloor n_i a\rfloor+e_i\quad(1\le i\le r)
$$
is the length of the intersection of $J_{\theta_{n_i}}-s_i a$ for $e_i=1$ and their complements for $e_i=0$. Finally,
$$
\mathbb E S_s=0,
\qquad
\mathbb E(S_sS_{s+n})=(-1)^{n-\lfloor na\rfloor}(1-2\theta_n).
$$
All these are joint laws for observables of the same phase path.

**Proof.** Flattening intertwines $\rho$ with $0\mapsto01$, $1\mapsto0$. The characteristic mechanical word of slope $a$ has its $k$th one at $\lfloor k/a\rfloor-1$ and its $k$th zero at $\lfloor k/(1-a)\rfloor-1$. Since $1/a=\varphi^2$ and $1/(1-a)=\varphi$, substitution sends the latter positions to the former; the fixed word beginning with $0$ is therefore the phase word with intercept $a$. This is the standard rotation coding described in Berstel, [*Sturmian and Episturmian Words*](https://ligm.univ-eiffel.fr/~berstel/Articles/2007SturmianThessalonique.pdf), §3, and in [*Recursive Relational Observation*](https://github.com/the-omega-institute/trureturing/blob/4ab7dd1d2631b0a0859643815bcc2c442ce34e32/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md), Theorem 20.4.

Telescoping the floor differences gives the count formula. Since $M^2=M+I$, the two atom weights after $k$ substitutions are $F_{k+3}$ and $F_{k+4}$; applying $q$ to a window with $A$ ones gives $F_{k+4}n-F_{k+2}A$. Hence the centered quantity is $-F_{k+2}(A-na)$. The common $U$ makes every joint event an intersection of the corresponding circular arcs, proving the covariance and all finite joint probabilities. Also $S_sS_{s+n}=(-1)^{n-A_{s,n}}$ and the fair anchor gives zero individual means. No independence assumption is used. $\square$

**Theorem 3.3 (Bounded discrepancy and nonmixing native fluctuations).** For every phase and every window,
$$
|A_{s,n}-na|<1.
$$
For fixed $k$ and $T<\infty$,
$$
\sup_{0\le t\le T}
\frac{\left|Q_{s,\lfloor Nt\rfloor}^{(k)}-(F_{k+4}-aF_{k+2})\lfloor Nt\rfloor\right|}{F_{k+2}\sqrt N}
\le N^{-1/2}.
$$
Thus the centered count step processes and every finite collection of centered quantity step processes, divided by $\sqrt N$, converge uniformly on $[0,T]$ to zero for every phase. In particular this is functional convergence in the Skorohod $J_1$ topology, as well as zero fluctuation at every finite collection of observation times. The unscaled variance has all subsequential limits in $[0,F_{k+2}^2/4]$, and for $j\ge2$,
$$
\operatorname{Var}(A_{s,F_j})=\varphi^{-j}(1-\varphi^{-j}).
$$
If $d_r=\{ra\}$, then
$$
\operatorname{Cov}(C_0,C_r)
=(a-d_r)_++(a+d_r-1)_+-a^2.
$$
Along $r=F_j$ this tends to $a(1-a)>0$, while $|\mathbb E(S_0S_{F_j})|\to1$; neither observed process is mixing.

**Proof.** The discrepancy and the normalized bound follow from Theorem 3.2. The irrational orbit $\{na\}$ is dense, so continuity of $t(1-t)$ gives the full interval of variance subsequential limits. Binet's identity gives
$$
F_j a=F_{j-2}+(-1)^j\varphi^{-j},
$$
which yields the displayed return variance. Intersecting two arcs of length $a$ gives the bit covariance formula; at Fibonacci returns the overlap tends to $a$. The anchored correlation formula in Theorem 3.2 then has absolute value tending to one. Mixing would force bounded centered correlations to tend to zero. The Binet identity used here is the source formula `Real.coe_fib_eq` in [Mathlib, *Real Golden Ratio*](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/Real/GoldenRatio.lean#L197). $\square$

**Theorem 3.4 (A declared Markov dynamics and its joint functional Gaussian law).** For the Markov path of Hypothesis 3.1 put
$$
 m=\frac p{1+p},\qquad v=m(1-m),\qquad r=-p.
$$
The count variance is
$$
V_n=v\left[n\frac{1-p}{1+p}+\frac{2p(1-(-p)^n)}{(1+p)^2}\right],
$$
and for $m_0\le n$ the covariance of prefix counts of lengths $m_0,n$ is
$$
V_{m_0}+\frac{vr(1-r^{m_0})(1-r^{n-m_0})}{(1-r)^2}.
$$
The pathwise quantity identity of Theorem 3.2 remains valid, so the generation covariance is $F_{k+2}F_{\ell+2}V_n$. If $0<p<1$, fix $0<T<\infty$ and generations $k_1,\ldots,k_d$. Put
$$
X_N(t)=\frac{A_{0,\lfloor Nt\rfloor}-m\lfloor Nt\rfloor}{\sqrt N},
\qquad
Y_N^{(k)}(t)=
\frac{Q_{0,\lfloor Nt\rfloor}^{(k)}-(F_{k+4}-mF_{k+2})\lfloor Nt\rfloor}{\sqrt N}.
$$
In $D([0,T],\mathbb R^{d+1})$ with the Skorohod $J_1$ topology,
$$
\bigl(X_N,Y_N^{(k_1)},\ldots,Y_N^{(k_d)}\bigr)
\Longrightarrow
\sigma_p B\,\bigl(1,-F_{k_1+2},\ldots,-F_{k_d+2}\bigr),
\qquad
\sigma_p^2=\frac{p(1-p)}{(1+p)^3}>0,
$$
where $B$ is one standard Brownian motion shared by all coordinates. In particular, centered prefix counts at finitely many nonnegative times, divided by $\sqrt N$, converge jointly to a centered Gaussian vector with covariance
$$
\sigma_p^2\min(t_i,t_j).
$$
The corresponding quantity coordinates have covariance $F_{k+2}F_{\ell+2}\sigma_p^2\min(t_i,t_j)$. The anchored spin correlations satisfy
$$
K_0=1,\qquad K_1=\frac{p-1}{p+1},\qquad
K_{n+2}=-(1-p)K_{n+1}-pK_n.
$$
At $p=0$ the path is constant zero. At $p=1$ it alternates, with $V_n=0$ for even $n$ and $V_n=1/4$ for odd $n$; both endpoints have zero square-root fluctuation limit.

**Proof.** For $f(i)=i-m$, direct multiplication gives $P_pf=-pf$. Thus the centered indicators have covariance $vr^{|i-j|}$, and summing the geometric series gives both finite formulas.

For the path limit, set $g=f/(1+p)$, so $g-P_pg=f$ and $P_pg=-pg$. With $\mathcal F_n=\sigma(C_0,\ldots,C_n)$, the process
$$
M_n=\sum_{j=0}^{n-1}\bigl[g(C_{j+1})-P_pg(C_j)\bigr],
\qquad M_0=0,
$$
is a square-integrable martingale. Telescoping gives the exact decomposition
$$
A_{0,n}-nm=M_n+g(C_0)-g(C_n).
$$
If $C_j=1$, the next state is zero and the martingale increment is zero. If $C_j=0$, that increment is $(C_{j+1}-p)/(1+p)$. Its conditional variance is therefore $p(1-p)/(1+p)^2$ at state zero and zero at state one. Hence its predictable bracket is
$$
\langle M\rangle_n
=\frac{p(1-p)}{(1+p)^2}\sum_{j=0}^{n-1}(1-C_j)
=\frac{p(1-p)}{(1+p)^2}(n-A_{0,n}).
$$
For fixed $t$, stationarity and the displayed variance formula $V_n=O(n)$ give
$$
\frac{\langle M\rangle_{\lfloor Nt\rfloor}}N
\longrightarrow t\sigma_p^2\quad\text{in }L^2.
$$
This convergence is uniform in probability on compact time intervals: the bracket is nondecreasing, so between successive points of a finite time grid its error is bounded by the largest grid error plus $\sigma_p^2$ times the grid mesh. First let $N$ tend to infinity on the grid, then let the mesh tend to zero.

The step martingale $M_{\lfloor Nt\rfloor}/\sqrt N$, with filtration $\mathcal F_{\lfloor Nt\rfloor}$, starts at zero and is locally square-integrable. Its maximum squared jump on $[0,T]$ is at most $1/((1+p)^2N)$, and the maximum jump of its predictable bracket is at most $p(1-p)/((1+p)^2N)$. These deterministic bounds also bound the expectations of the jumps. Thus the predictable-bracket and jump conditions of W. Whitt, [*Proofs of the martingale FCLT*](https://arxiv.org/pdf/0712.1929v2), Theorem 2.1(ii), apply and give convergence to $\sigma_p B$ in $J_1$. The remainder $g(C_0)-g(C_{\lfloor Nt\rfloor})$ is bounded by $1/(1+p)$ uniformly in $t$, so its division by $\sqrt N$ does not affect the limit. Finally, the exact common-path identity
$$
Y_N^{(k)}=-F_{k+2}X_N
$$
transfers this convergence to the joint count and quantity process. No stochastic assumption beyond Hypothesis 3.1 is used.

The finite-dimensional limit can also be read directly from the tilted matrix $P_p\operatorname{diag}(1,e^z)$, whose leading eigenvalue is
$$
\Lambda(z)=\frac{1-p+\sqrt{(1-p)^2+4pe^z}}2,
$$
with expansion
$$
\log\Lambda(z)=mz+\tfrac12\sigma_p^2z^2+O(z^3).
$$
The second eigenvalue is $-p$ at zero and remains smaller in modulus near zero. For successive blocks, use tilts $z_i=iu_i/\sqrt N$; the leading spectral projections tend to $\mathbf1\pi_p$, subleading products vanish, and centering cancels the linear terms. The characteristic functions converge to
$$
\exp\left(-\frac{\sigma_p^2}{2}\sum_i u_i^2(t_i-t_{i-1})\right),
$$
which is the joint law of independent Gaussian increments. The anchored parity calculation replaces $e^z$ by $-1$; the matrix polynomial is $z^2-(1-p)z+p$, giving the recurrence after multiplication by $(-1)^n$. The endpoint assertions follow directly. $\square$

**Theorem 3.5 (Density-matched counterlaw).** Set $p=a/(1-a)=\varphi^{-1}$ in Theorem 3.4. The Markov path and the Fibonacci phase path have the same atom density $a$, adjacent probabilities
$$
\Pr(11)=0,\qquad \Pr(10)=\Pr(01)=a,\qquad \Pr(00)=1-2a,
$$
and the same expected substituted quantity $(F_{k+4}-aF_{k+2})n$ at every generation. Nevertheless the Markov path has
$$
\sigma_p^2=\varphi^{-6},
$$
while the phase path has zero square-root fluctuation limit. Their lag-two covariances are respectively $\varphi^{-5}$ and $0$, and the Markov path assigns probability $\varphi^{-5}$ to $000$, which never occurs in the Fibonacci language.

**Proof.** The stationary vector of $P_p$ has one-density $p/(1+p)=a$ at $p=\varphi^{-1}$, so the adjacent table and expected quantity agree with the phase path. The variance and lag-two values follow from Theorems 3.3 and 3.4. In the phase language every length-three factor contains at least one $1$, whereas the Markov law gives
$$
\Pr(000)=\frac1{1+p}(1-p)^2=\varphi^{-5}.
$$
Thus the two laws agree on the elementary readouts and disagree on a legal word and on the fluctuation scale. The full substitution language excludes the counterlaw, but the labels, composition recurrence, means and adjacent pairs alone do not. $\square$

Citation: the arithmetic observations and anchored reconstruction are in [*Recursive Relational Observation*](https://github.com/the-omega-institute/trureturing/blob/4ab7dd1d2631b0a0859643815bcc2c442ce34e32/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md), Theorems 66.7, 66.9 and 66.11. The Perron–Parry comparison uses W. Parry, [*Intrinsic Markov chains*](https://doi.org/10.1090/S0002-9947-1964-0161372-1).

## 4. Fixed-window scale observations and entropy blindness

**Definition 4.1 (Scale response).** For a stationary law $\mu$ on $X_M$, let
$$
O_r(\mu)=\bigl(\mu[v]\bigr)_{|v|=r}
$$
be its length-$r$ cylinder vector, and let
$$
\Phi_r(\mu)=\bigl(O_r(R^n\mu)\bigr)_{n\ge0}
$$
be its complete forward scale response. The response records all iterates of the chosen spatial inflation, but only at the fixed window size $r$. For either map $H=O_r$ or $H=\Phi_r$, define its equality kernel by
$$
\ker H=\{(\mu,\eta):H(\mu)=H(\eta)\}.
$$
This is an equivalence relation on stationary laws, rather than a linear null space.

**Theorem 4.2 (Exact scale compatibility and finite-window blindness).** There is a unique stationary law $\nu$ on $X_\tau$, with letter vector
$$
\nu[\alpha]=\varphi^{-2},\qquad \nu[\beta]=\varphi^{-1}.
$$
Uniform spatial roots in $w(\rho^n t)$ converge in every fixed finite window to $\nu$, for every fixed nonempty $t$. The operator $R$ preserves stationarity, satisfies $R\nu=\nu$, and $R^n\mu\Rightarrow\nu$ for every stationary $\mu$ on $X_M$. For each $r$,
$$
\ker\Phi_r=\ker O_r.
$$
For every integer $r\ge2$ there exists an ergodic stationary law $\mu_r$ on $X_M$ such that
$$
O_r(R^n\mu_r)=O_r(\nu)\quad\text{for every }n\ge0,
$$
while
$$
 h(R^n\mu_r)=\varphi^{-n}h(\mu_r)>0=h(\nu).
$$
The quantifiers are $\forall r\,\exists\mu_r\,\forall n$, and do not assert one law works for every window length.

**Proof.** Structural induction gives $w(\rho t)=\tau(w(t))$. Let the leaves of $t$ be $x_1,\ldots,x_m$ and put $L_n(c)=|\tau^n(c)|$. Uniform selection of a descendant position assigns mass $1/\sum_jL_n(x_j)$ to each pair $(i,k)$ with $0\le k<L_n(x_i)$, so its ancestral leaf is selected with probability $L_n(x_i)/\sum_jL_n(x_j)$. This is exactly the length-biased offset integral in Definition 2.3. The telescoping calculation in Theorem 2.5 proves stationarity and the same calculation with $\tau^n$ proves the iterate formula.

For words $u,v$ of length $r$, let $A_r(v,u)$ be the number of offsets $0\le k<|\tau(u_0)|$ for which $\tau(u)[k:k+r]=v$, and let $d_r(u)=|\tau(u_0)|$. Partitioning the offset integral by the input cylinder gives
$$
O_r(R\mu)_v
=\frac{\sum_u A_r(v,u)\,\mu[u]}{\sum_u d_r(u)\,\mu[u]}.
$$
Every column sum of $A_r$ is $d_r$, and the $r=1$ transfer is the incidence matrix. Hence equal $O_r$ vectors remain equal under every iterate, while the $n=0$ coordinate gives the converse, proving $\ker\Phi_r=\ker O_r$.

Under $\beta\leftrightarrow0$, $\alpha\leftrightarrow1$, the substitution is the classical Fibonacci substitution. Its rotation coding is minimal and uniquely ergodic and has factor complexity $m+1$; these are the classical ingredients in Berstel, [*Sturmian and Episturmian Words*](https://ligm.univ-eiffel.fr/~berstel/Articles/2007SturmianThessalonique.pdf), §§2–3. Thus $\nu$ exists and has zero entropy. Since $R\nu$ is stationary and supported on $X_\tau$, unique ergodicity gives $R\nu=\nu$. Every $\tau^n(c)$ is a long legal Fibonacci block, and the proportion of length-$r$ roots crossing a boundary between substituted letters is at most $(r-1)/\min_c|\tau^n(c)|$, which tends to zero. This proves convergence from every finite tree and from every stationary input.

Fix $r\ge2$. Take the finite state space of positive-occurrence Fibonacci factors
$$
\mathcal S_r=\{u:|u|=r-1,\ \nu[u]>0\}.
$$
Give $u$ state mass $\nu[u]$. For $c\in\{\alpha,\beta\}$ with $\nu[uc]>0$, set
$$
K\bigl(u,\operatorname{suffix}_{r-1}(uc)\bigr)=\frac{\nu[uc]}{\nu[u]},
$$
and set all other transition entries to zero. Here $\operatorname{suffix}_{r-1}(uc)$ is the last $r-1$ letters of $uc$, so each supported edge joins two states in $\mathcal S_r$. Right-cylinder consistency gives row sum one, and left-cylinder consistency and stationarity give incoming mass $\nu[v]$ at every state $v$. The resulting stationary letter law $\mu_r$ has $O_r(\mu_r)=O_r(\nu)$ and is supported on $X_M$.

Minimality of the Fibonacci shift makes this support graph irreducible: starting at an occurrence of any factor $u$, uniform recurrence supplies a later occurrence of any factor $v$, and the intervening Fibonacci word gives a path of supported edges from $u$ to $v$. Thus the stationary Markov law is ergodic. Every state has one or two right extensions. Factor complexity gives $|\mathcal S_r|=r$ and exactly $r+1$ supported length-$r$ words, so precisely one state is right-special, with two positive outgoing probabilities. State paths and letter paths determine one another by their overlapping blocks and have the same entropy rate. The right-special state's positive stationary mass contributes strictly positive conditional entropy, proving $h(\mu_r)>0$. The transfer identity above preserves its length-$r$ vector at every iterate.

For entropy, form the tower
$$
\mathcal Y_\mu=\{(x,k):0\le k<|\tau(x_0)|\}
$$
with measure proportional to $\mu$ times counting measure. The output coding is invertible: every $\beta$ begins a substituted letter, and it is paired with the following $\alpha$ when present; returning to a codeword boundary recovers the parent shift. Therefore each parent information block is represented by an average of $\bar\ell(\mu)=\mu[\alpha]+2\mu[\beta]$ output symbols, and direct block counting gives
$$
 h(R\mu)=\frac{h(\mu)}{\bar\ell(\mu)}.
$$
The finite-window transfer leaves the letter vector $(\varphi^{-2},\varphi^{-1})$ unchanged, so $\bar\ell(R^n\mu_r)=\varphi$ and iteration gives the entropy formula. $\square$

**Theorem 4.3 (A sharp scale defect).** Let $\mu_2$ be the stationary Markov law in the order $(\alpha,\beta)$ with
$$
P=\begin{pmatrix}0&1\\ \varphi^{-1}&\varphi^{-2}\end{pmatrix},
\qquad
\pi=(\varphi^{-2},\varphi^{-1}).
$$
Its pair probabilities agree with $\nu$:
$$
\mu_2[\alpha\alpha]=0,
\quad\mu_2[\alpha\beta]=\mu_2[\beta\alpha]=\varphi^{-2},
\quad\mu_2[\beta\beta]=\varphi^{-3}.
$$
Nevertheless,
$$
\operatorname{TV}\bigl(O_3(\mu_2),O_3(R\mu_2)\bigr)=2\varphi^{-5}.
$$
If $C_N=\sum_{j=0}^{N-1}{\bf1}_{\alpha}(x_j)$, then
$$
|C_N-N\varphi^{-2}|\le1\quad\nu\text{-a.s.},
\qquad
\operatorname{Var}_{\mu_2}(C_N)=\varphi^{-6}N+O(1).
$$
The difference is a spatial counting law and does not determine a transport or quantum exponent.

**Proof.** Multiplying $\pi$ by $P$ gives the pair table. In the order $(\alpha\beta\alpha,\alpha\beta\beta,\beta\alpha\beta,\beta\beta\alpha,\beta\beta\beta)$, the Markov triple vector is
$$
(\varphi^{-3},\varphi^{-4},\varphi^{-2},\varphi^{-4},\varphi^{-5}).
$$
The substitution language excludes both $\alpha\alpha$ and $\beta\beta\beta$, and Theorem 2.5 preserves the pair table. Marginal consistency therefore gives
$$
O_3(R\mu_2)=(\varphi^{-4},\varphi^{-3},\varphi^{-2},\varphi^{-3},0),
$$
which also equals $O_3(\nu)$. Four coordinates differ by $\varphi^{-5}$, giving total variation $2\varphi^{-5}$. Rotation coding makes the $\alpha$ count a floor difference, proving the bounded discrepancy. For the Markov law, ${\bf1}_\alpha-\varphi^{-2}$ is an eigenfunction with eigenvalue $-\varphi^{-1}$ and variance $\varphi^{-3}$, so summing the geometric covariance yields
$$
N\varphi^{-3}\frac{1-\varphi^{-1}}{1+\varphi^{-1}}+O(1)=N\varphi^{-6}+O(1).
$$
Thus the complete forward response at window size two can agree while the triple projection and fluctuation law differ. $\square$

Citation: rotation coding is background from [*Recursive Relational Observation*](https://github.com/the-omega-institute/trureturing/blob/4ab7dd1d2631b0a0859643815bcc2c442ce34e32/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md), Theorem 20.4. Its Theorems 33.9–33.10 distinguish boundary and stationary probabilities, and Proposition 71.8 supplies legal-prefix counting and natural-boundary-measure background. The substitution-specific finite-cylinder transfer identity is proved above. The common-source comparison uses the contract in Hypothesis 13.1 and the conditional compatibility statement in Theorem 13.2 of [*FIB Relational Continuation Geometry*](https://github.com/the-omega-institute/trureturing/blob/4ab7dd1d2631b0a0859643815bcc2c442ce34e32/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md); its Theorem 2.5 supplies the distinct finite-prefix versus finite-source-realization background.

## 5. Ordered transport and passage statistics

**Definition 5.1 (Cut chain and conservative kernel).** Let $t$ have ordered leaf word $s_0\cdots s_{L-1}$. Put
$$
C_k=\sum_{i<k}e_{s_i},\qquad x_k=q(C_k),\qquad 0\le k\le L,
$$
so $x_{k+1}-x_k$ is $2$ or $3$. The cut state $(t,k)$ is an ordered position; $C_0=0$ is an empty prefix contribution and not an empty source tree.

On this fixed chain take $r_\alpha,r_\beta>0$ and $0<\theta\le\min(r_\alpha,r_\beta)/2$. At an interior state, the chain crosses each incident edge $i$ in either direction with probability $\theta/r_{s_i}$ and holds with the remaining probability; at state $0$ there is no left edge, and at $L$ the state is absorbing. Let $X_0=0$, let
$$
\tau(t)=\inf\{n:X_n=L\},
$$
and measure elapsed time by $\delta\tau(t)$ for $\delta>0$. The source generation index is not a clock tick.

**Theorem 5.2 (Currents, passage recurrence and the Cassini order correction).** Let $m_n(k)=\Pr(X_n=k)$, set $J_n(-1)=J_n(L)=0$, and define
$$
J_n(i)=\frac{\theta}{r_{s_i}}\bigl(m_n(i)-m_n(i+1)\bigr)\quad(0\le i<L-1),
\qquad
J_n(L-1)=\frac{\theta}{r_{s_{L-1}}}m_n(L-1).
$$
Then
$$
 m_{n+1}(k)-m_n(k)=J_n(k-1)-J_n(k),
\qquad\sum_{k=0}^Lm_n(k)=1,
$$
and
$$
\mathbb E[x_{X_{n+1}}-x_{X_n}]
=\sum_{i=0}^{L-1}q(e_{s_i})J_n(i).
$$
For a word $u=u_0\cdots u_{L-1}$ put
$$
R(u)=\sum_{i=0}^{L-1}r_{u_i},\qquad
A(u)=\sum_{i=0}^{L-1}(i+1)r_{u_i}.
$$
Writing $A_j=A(w(T_j))$, $R_j=R(w(T_j))$ and $L_j=|w(T_j)|$, one has
$$
\theta\,\mathbb E\tau(T_j)=A_j,
$$
$$
A_{j+2}=A_{j+1}+A_j+L_{j+1}R_j,
\qquad A_0=r_\alpha,\quad A_1=r_\beta,
$$
and, for $j\ge2$,
$$
2\theta\,\mathbb E\tau(T_j)
=(L_j+1)R_j-(r_\beta-r_\alpha)\bigl(F_{j-2}+(-1)^j\bigr),
$$
where $L_j=F_{j+1}$ and
$$
R_j=r_\alpha F_{j-1}+r_\beta F_j.
$$

**Proof.** The transition equation at each interior cut is the divergence identity for the displayed net current; at the absorbing cut only the incoming current remains. Summing over cuts cancels internal currents and leaves total mass one. Multiplying by $x_k$ and summing leaves $(x_{i+1}-x_i)J_n(i)$, which is the displacement formula with the actual increments $2$ and $3$.

Absorption has finite expectation. From every nonabsorbed state, a string of at most $L$ right crossings has probability at least
$$
\left(\frac{\theta}{\max(r_\alpha,r_\beta)}\right)^L>0,
$$
so the tail is bounded geometrically. Let $h_k=\mathbb E_k\tau$ and $d_i=h_i-h_{i+1}$. The first-step equations give
$$
\frac{\theta d_0}{r_{s_0}}=1,\qquad
\frac{\theta d_i}{r_{s_i}}-\frac{\theta d_{i-1}}{r_{s_{i-1}}}=1,
$$
whence $d_i=(i+1)r_{s_i}/\theta$ and $h_0=A(w)/\theta$.

For concatenation, direct index shifting gives
$$
A(uv)=A(u)+A(v)+|u|R(v).
$$
Since $w(T_{j+2})=w(T_{j+1})w(T_j)$, the recurrence follows. To extract the order term, let $b(u)$ count $\beta$ leaves, put $B(u)=\sum_{i:u_i=\beta}(i+1)$ and
$$
C(u)=2B(u)-(|u|+1)b(u).
$$
Then
$$
C(uv)=C(u)+C(v)+|u|b(v)-|v|b(u).
$$
For $w(T_j)$, $b_j=F_j$ and $L_j=F_{j+1}$, so
$$
C_{j+2}=C_{j+1}+C_j+F_{j+2}F_j-F_{j+1}^2.
$$
Cassini's identity makes the last term $(-1)^{j+1}$, and $C_0=C_1=0$ gives
$$
C_j=-F_{j-2}-(-1)^j\qquad(j\ge2).
$$
Finally,
$$
2A_j=(L_j+1)R_j+(r_\beta-r_\alpha)C_j,
$$
which is the asserted correction. The first-step and network-current identities are the standard finite-chain calculation; see [J. R. Norris, *Markov Chains*](https://doi.org/10.1017/CBO9780511810633), §§1.1–1.3, for the corresponding passage equations.
$\square$

**Theorem 5.3 (Quadratic passage law in the quantity coordinate).** Put
$$
\overline r=\frac{r_\alpha}{\varphi^2}+\frac{r_\beta}{\varphi},
\qquad
\widetilde r=\frac{r_\alpha}{\varphi}+\frac{r_\beta}{\varphi^2}.
$$
For the ordered source cells,
$$
\mathbb E\tau(T_j)=\frac{\overline rL_j^2+\widetilde rL_j}{2\theta}+O(1),
$$
where the remainder is bounded in $j$. Since $N(T_j)=q(c(T_j))=F_{j+3}$,
$$
\lim_{j\to\infty}\frac{\delta\,\mathbb E\tau(T_j)}{N(T_j)^2}
=\frac{\delta\,\overline r}{2\theta\varphi^4},
$$
and the mean-passage coefficient
$$
D_{\mathrm{pass},q}
=\lim_{j\to\infty}\frac{N(T_j)^2}{2\delta\,\mathbb E\tau(T_j)}
=\frac{\theta\varphi^4}{\delta\,\overline r}
$$
exists.

**Proof.** The Fibonacci two-root formula gives
$$
\frac{N(T_j)}{L_j}\to\varphi^2,\qquad
R_j=\overline rL_j+O(\varphi^{-j}),\qquad
F_{j-2}=\varphi^{-3}L_j+O(\varphi^{-j}).
$$
Insert these estimates in Theorem 5.2. Because $L_j=O(\varphi^j)$, the product of the resistance error with $L_j+1$ is bounded. The coefficient of the linear term is
$$
\overline r-(r_\beta-r_\alpha)\varphi^{-3}=\widetilde r.
$$
This proves the bounded-remainder expansion and the two limits. $\square$

**Theorem 5.4 (Composition does not determine transport or its clock).** Let
$$
O(t)=\bigl(q(c(t)),q(Mc(t))\bigr).
$$
For every positive $r_\alpha,r_\beta$, $O$ does not determine jointly the first-step quantity displacement and the mean passage time of Definition 5.1 over all source trees. On a fixed FIB cut carrier, the same static source permits an identity kernel with infinite crossing time, a deterministic right-moving kernel with crossing time $\delta L_j$, and the quadratic law of Theorem 5.3. Replacing $\theta$ by $\theta/2$ doubles the mean passage time and replacing $\delta$ rescales elapsed time without changing the source. Finally, no nonzero additive real charge $\ell c(t)$ is invariant under $\rho$ on all raw trees.

**Proof.** The trees $t=\langle\alpha,\beta\rangle$ and $t'=\langle\beta,\alpha\rangle$ both have $O=(5,8)$. Their first-step expected displacements are $2\theta/r_\alpha$ and $3\theta/r_\beta$, while their mean passage times are $(r_\alpha+2r_\beta)/\theta$ and $(r_\beta+2r_\alpha)/\theta$. Equality of the passage times requires $r_\alpha=r_\beta$, whereas equality of first-step displacements requires $r_\beta=3r_\alpha/2$; these cannot hold together for positive resistances. Thus the joint transport task is not a function of $O$.

The identity kernel never reaches a distinct right endpoint, while a kernel that takes the right edge at every step reaches it in $L_j$ steps. Both preserve the same carrier and composition observations. The declared conservative chain supplies the quadratic law. The parameters $\theta$ and $\delta$ are external time data, so the stated rescalings follow.

If $\ell=(u,v)$ were invariant under every substitution, then $\ell M=\ell$, which says $v=u$ and $u+v=v$ and hence $u=v=0$. In fact
$$
q(c(\rho t))-q(c(t))=a+2b>0
$$
for every nonempty tree with composition $(a,b)$. Therefore the quantity is a growing readout, not a conserved charge. $\square$

Citation: the source quantity bridge and ordered recurrence are in [*Fibonacci Atomic Relation Generation*](https://github.com/the-omega-institute/trureturing/blob/4ab7dd1d2631b0a0859643815bcc2c442ce34e32/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md), Theorems 3.2, 3.4, 5.4 and 8.2. The common-source and legal-operation conditions are in [*FIB Relational Continuation Geometry*](https://github.com/the-omega-institute/trureturing/blob/4ab7dd1d2631b0a0859643815bcc2c442ce34e32/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md), Hypothesis 13.1 and conditional Theorem 13.2; its Theorem 2.5 supplies finite-prefix versus finite-source-realization background.

## 6. Complementary fibers and controlled joint laws

**Definition 6.1 (Complementary-pair encoding).** Fix $k\ge1$ and a binary ordered skeleton $C_k$ with $k$ numbered slots. For $z\in\Omega_k=\{0,1\}^k$ and $n\ge0$, set
$$
P_i(n,z_i)=\left\langle T_{n+z_i},T_{n+1-z_i}\right\rangle,
$$
and let $E_n(z)$ be the tree obtained by placing these $k$ pairs into the slots of $C_k$. Define the left-child readout
$$
R_i(n,z)=q\bigl(c(\text{left child in slot }i)\bigr).
$$
On the actual image $E_n[\Omega_k]$, define
$$
D_n(t)_i=\frac{R_i(n,z)-F_{n+3}}{F_{n+2}}
\quad\text{when }t=E_n(z).
$$
For $a\in\Omega_k$, let $J_a$ exchange the two children in slot $i$ exactly when $a_i=1$. These operations are defined only on trees possessing the displayed slots.

**Hypothesis 6.2 (Controlled stochastic extension).** Let $\nu$ be a probability on $\Omega_k$ and $K$ a stochastic matrix on $\Omega_k$. Conditional on current state $z$, the next generation chooses $z'$ with probability $K(z,z')$ and returns $E_{n+1}(z')$. A physical interpretation additionally supplies an injection from a finite state space into $\Omega_k$, an initial law, transition and action kernels supported on that image, a matching generation clock, readouts, and exact legal domains for permitted actions. These data are independent of $\rho$.

**Theorem 6.3 (Exact controlled realization with unchanged aggregate recursion).** For all $n,z$,
$$
 c(E_n(z))=k(F_{n+1},F_{n+2}),
\qquad
 q(c(E_n(z)))=kF_{n+5},
\qquad D_n(E_n(z))=z.
$$
Moreover,
$$
\rho E_n(z)=E_{n+1}(z),
\qquad
J_aE_n(z)=E_n(z\oplus a),
\qquad
\rho J_aE_n(z)=J_a\rho E_n(z).
$$
Consequently every $\nu,K$ in Hypothesis 6.2 is realized by expansion followed by a lawful complementary swap, and all finite joint laws of decoded states and supplied observables agree with the specified Markov chain. The same induction applies to adaptive action kernels whose legal domains are transported. The aggregate quantities obey
$$
Q_{n+2}=Q_{n+1}+Q_n,
$$
for every such controlled law. At generation zero, $2k$ leaves are minimal among fixed-composition encodings with $k$ disjoint atomic leaf probes that realize every bit vector.

**Proof.** The source formula $q(c(T_j))=F_{j+3}$ gives
$$
R_i(n,z)=F_{n+3}+F_{n+2}z_i,
$$
so the denominator is positive and $D_n$ is an exact inverse on the image. Each complementary pair has composition
$$
 c(T_n)+c(T_{n+1})=M^n(1,1)=(F_{n+1},F_{n+2}),
$$
independently of its orientation. Summing over slots gives the two aggregate formulas. Homomorphic substitution preserves slot order, so it advances $E_n$ to $E_{n+1}$ and commutes with all lawful swaps.

For a transition $z\to z'$, use the single swap vector $a=z\oplus z'$. The probability of that swap is $K(z,z')$. Induction on history length gives
$$
\Pr(z_0,\ldots,z_N)=\nu(z_0)\prod_{j<N}K(z_j,z_{j+1}),
$$
so pushforward by any supplied readout preserves every finite joint law. The same induction with a legal-domain indicator and an adaptive kernel proves the action statement. The aggregate formula is independent of the history and inherits the Fibonacci recurrence. Finally, realizing the all-zero probe vector requires at least $k$ leaves of one atom and realizing the all-one vector at least $k$ leaves of the other atom; a fixed-composition carrier therefore has at least $2k$ leaves, attained by the displayed pairs. $\square$

**Theorem 6.4 (Sharp cross-correlation obstruction under identical marginal trajectory laws).** For $k=2$, let $Z$ have
$$
\Pr(Z=(0,0))=\Pr(Z=(1,1))=\frac{1+\lambda}{4},
$$
$$
\Pr(Z=(0,1))=\Pr(Z=(1,0))=\frac{1-\lambda}{4},
\qquad -1\le\lambda\le1,
$$
 and evolve by bare substitution $E_n(Z)=\rho^nE_0(Z)$ with no stochastic controls. Then every aggregate quantity history is identical throughout the family, and every single-probe process law is identical. Nevertheless,
$$
\operatorname{Cov}(R_1(n),R_2(m))
=\frac{\lambda}{4}F_{n+2}F_{m+2},
$$
while
$$
q(c(E_n(Z)))=2F_{n+5}.
$$
For equal generations,
$$
\varphi^{-2n}\operatorname{Cov}(R_1(n),R_2(n))
\longrightarrow\frac{\lambda\varphi^4}{20}.
$$
The fraction of $\beta$ leaves is $F_{n+2}/F_{n+3}\to\varphi^{-1}$ for every $\lambda$. Define the observation map to be the aggregate trajectory law and the two separate marginal trajectory laws:
$$
\mathcal O(\lambda)=
\left(
\operatorname{Law}_\lambda\bigl((q(c(E_n(Z))))_{n\ge0}\bigr),
\operatorname{Law}_\lambda\bigl((R_1(n))_{n\ge0}\bigr),
\operatorname{Law}_\lambda\bigl((R_2(n))_{n\ge0}\bigr)
\right).
$$
These data withhold paired sample histories and the joint trajectory law
$$
\mathsf J_\lambda=
\operatorname{Law}_\lambda\bigl((R_1(n),R_2(n))_{n\ge0}\bigr).
$$
Let $a$ range over deterministic functions of $\mathcal O$ taking values in $[0,1]$, and let $H$ range over deterministic functions of $\mathcal O$ taking values in probabilities on the joint trajectory space. Then the worst-case absolute-error and total-variation radii are
$$
\inf_a\sup_{-1\le\lambda\le1}
\left|a(\mathcal O(\lambda))-\frac{1+\lambda}{2}\right|=\frac12,
\qquad
\inf_H\sup_{-1\le\lambda\le1}
\operatorname{TV}\bigl(H(\mathcal O(\lambda)),\mathsf J_\lambda\bigr)=\frac12.
$$
Here “separate histories” means the separate marginal trajectory laws in $\mathcal O$. Paired common-source samples constitute a different observation map: at any generation the two readouts decode both seed bits and hence reveal their equality.

**Proof.** Each $Z_i$ is fair for every $\lambda$, and
$$
R_i(n,Z)=F_{n+3}+F_{n+2}Z_i.
$$
Thus each marginal trajectory law is the same equal mixture of the two deterministic trajectories, while
$$
\operatorname{Cov}(Z_1,Z_2)=\frac\lambda4
$$
proves the covariance formula. Binet's formula gives the normalized limit. The complementary pair has composition $(F_{n+1},F_{n+2})$ in each slot, proving the common aggregate history and the limiting leaf fraction. Consequently $\mathcal O(\lambda)$ is constant throughout the family, so each permitted deterministic estimator must return the same estimate for every $\lambda$. At $\lambda=1$ the joint seed is supported on the equal-bit states; at $\lambda=-1$ it is supported on the unequal-bit states. The decoder transports their disjoint supports to disjoint joint-trajectory supports. Any common event estimate has error at least $1/2$ at one endpoint and the constant estimate $1/2$ attains it. The endpoint joint trajectory laws have total variation one, so the triangle inequality gives radius at least $1/2$ for every $H$; the constant estimator $\mathsf J_0$ has distance $|\lambda|/2$ from $\mathsf J_\lambda$, attaining the bound. $\square$

Citation: the finite-fiber and lawful-operation boundary is [*Recursive Relational Observation*](https://github.com/the-omega-institute/trureturing/blob/4ab7dd1d2631b0a0859643815bcc2c442ce34e32/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md), Theorems 2.2, 2.5 and 57.9, together with [*Recursive Relational Observation Transport Memory Completion*](https://github.com/the-omega-institute/trureturing/blob/4ab7dd1d2631b0a0859643815bcc2c442ce34e32/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), §3.2. The finite-kernel semantics used inside the proof are described in Tobias Fritz, [*A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics*](https://doi.org/10.1016/j.aim.2020.107239).

## 7. Statistical and physical boundary

**Theorem 7.1 (What the recursion does and does not determine).** The native recursion determines the ordered source carrier, the composition evolution $c\mapsto Mc$, the quantity sequence $q(c(T_j))$, and the exact ordered leaf words. It does not determine any of the following without the corresponding hypotheses above: a probability on hidden composition fibers; a stationary law on $X_M$; a pressure parameter; a spatial-root convention; a Markov transition kernel; a transport resistance, boundary condition or clock; a joint coupling between separate probes; or a physical identification of trees, observables and operations. In particular:

1. the same quantity trajectory can carry tree laws whose total variation tends to one (Theorem 2.2);
2. the same one- and two-letter statistics can carry the entire triple interval of Theorem 2.4 and the pressure law with positive entropy;
3. the same fixed-window scale response can carry positive entropy (Theorem 4.2);
4. the same means and adjacent pairs can carry zero or positive square-root fluctuations (Theorem 3.5);
5. the same two separate marginal probe trajectory laws can carry every cross-correlation in $[-1,1]$ (Theorem 6.4);
6. transport and elapsed time vary while the static source and its quantity observations remain fixed (Theorem 5.4).

Therefore no universal physical law, Gibbs law, Brownian limit, heat equation, quantum transport exponent or empirical universality claim follows from the FIB ATOM recursion alone.

**Proof.** Each item is witnessed by the explicit pair of models already constructed. Theorem 2.2 supplies identical complete quantity paths with different genealogical measures. Theorem 2.4 fixes the one- and two-cylinder data and computes the full compatible triple interval, including the entropy-maximizing pressure law. Theorem 4.2 constructs, for each fixed $r$, an ergodic positive-entropy law with the same $O_r(R^n\cdot)$ for every $n$. Simultaneous equality for all $r$ instead determines the law: if $O_r(\mu)=O_r(\nu)$ for every $r$, then all contiguous cylinders agree, and stationarity and marginalization give equality on every finite-coordinate cylinder. These cylinders generate the Borel sigma-field, so $\mu=\nu$ and $h(\mu)=0$. Thus one positive-entropy law cannot meet all window constraints simultaneously. Theorem 3.5 gives the density-matched Markov counterlaw with positive diffusion coefficient and a forbidden length-three word, while Theorem 3.3 gives bounded native discrepancy. Theorem 6.4 keeps both complete marginal probe trajectory laws and the aggregate trajectory law fixed while varying the joint coupling. Theorem 5.4 keeps the source carrier fixed while changing the transition kernel, resistance and clock. These are mathematical countermodels to any inference that omits the corresponding data.

Conversely, once a sampling law, a common source, a legal operation, a joint coupling and a clock are explicitly supplied, Theorems 3.2, 5.2 and 6.3 prove the resulting finite-dimensional laws by direct calculation. The conclusions are therefore conditional statistical laws of the declared models, not laws selected by the recursion or by an external physical interpretation. $\square$

## 8. Process limits and common-source qualification

**Theorem 8.1 (Limit scope).** The native phase statements in Theorems 3.2 and 3.3 give exact joint window laws and uniform convergence of the square-root-normalized fluctuation processes to zero on compact time intervals. Under the existing stationary Markov hypotheses with $0<p<1$, Theorem 3.4 gives a Brownian functional limit in $D([0,T])$ with the $J_1$ topology for the centered prefix count and its common-path quantity multiples. The transport statement in Theorem 5.3 is a mean-passage asymptotic along the ordered finite cells, with finiteness of the mean proved in Theorem 5.2. The controlled statement in Theorem 6.3 transports the supplied finite-state history laws, which consistently extend to full trajectory laws.

The Markov Brownian limit concerns spatial prefix counts. It supplies no identification with a physical heat flow or with a diffusive scaling limit of the cut-chain transport. A continuum transport limit requires a specified family of rescaled cut-chain processes, spatial and time embeddings, boundary data and convergence target; a physical claim additionally requires a realization matching the observations, legal operations and clocks. These conclusions specify mathematical laws of the declared models without supplying those further identifications.

**Proof.** The supremum bound in Theorem 3.3 proves uniform convergence to the zero path. For the stationary Markov model, the Poisson-equation decomposition, bracket convergence and vanishing jumps in Theorem 3.4 supply tightness and the Brownian path law using Whitt's martingale FCLT; no additional stochastic hypothesis is needed. All quantity coordinates are fixed linear multiples of that same count path.

For the cut chain, the positive probability of absorption within $L$ steps from every nonabsorbed state bounds the tail geometrically and proves finite mean. The passage asymptotic then follows from the exact first-step equations and the Fibonacci estimates along $T_j$. An expectation asymptotic alone does not specify a continuum process or its convergence. The finite-state probabilities $\nu(z_0)\prod_{j<N}K(z_j,z_{j+1})$ in Theorem 6.3 are consistent under summing out the last state, so the standard cylinder extension defines their infinite trajectory law; the encoding transports this law because it transports every cylinder. This construction does not select an external physical realization. Finally, the countermodels in Theorem 7.1 vary data not selected by the native recursion; they do not refute the functional limit under the fixed $P_p$ hypotheses. The distinction is between these established mathematical process laws and the further continuum or physical identifications, which have not been specified. $\square$

## 追加锚（本行以下为增补区）

## 9. Exact discounted response to a Fibonacci terminal swap

**Definition 9.1 (Ordered finite response).** Retain the resistances, jump scale, reflecting left cut and absorbing right cut of Definition 5.1. For a nonempty word $w=w_0\cdots w_{L-1}$, let $K_w$ be the transient transition matrix on cuts $0,\ldots,L-1$, and put
$$
B_w=I-K_w,\qquad G_w=B_w^{-1},\qquad
f_w(s)=\mathbb E_0(1+s)^{-\tau_w},\qquad D_w(s)=f_w(s)^{-1},\qquad s\ge0.
$$
Here $\tau_w$ counts discrete steps; $s$ in this section is a dimensionless discount parameter. The inverse exists because absorption has a geometric tail, as in Theorem 5.2. Define
$$
W_0=\alpha,\qquad W_1=\beta,\qquad W_{j+2}=W_{j+1}W_j,
$$
so $W_j=w(T_j)$. For $j\ge1$, set
$$
U_j=W_{j+1}W_j,\qquad V_j=W_jW_{j+1},\qquad
\Delta_j=(-1)^{j+1}(r_\beta-r_\alpha).
$$
The corresponding trees $\langle T_{j+1},T_j\rangle$ and $\langle T_j,T_{j+1}\rangle$ have equal composition and equal aggregate quantity trajectories $q(M^n c)$ for every $n\ge0$. Both words have length $L=F_{j+3}$. Write $\mu_w=\mathbb E_0\tau_w$ and $m_{2,w}=\mathbb E_0\tau_w^2$.

**Theorem 9.2 (Full terminal-swap factorization and moment response).** The words $U_j,V_j$ have a common prefix $P_j$ of length $L-2$ and opposite final pairs. For odd $j$ the pairs are $\alpha\beta$ and $\beta\alpha$, respectively; for even $j$ their roles reverse. For every $s\ge0$,
$$
D_{U_j}(s)-D_{V_j}(s)
=\frac{s\Delta_j}{\theta}D_{P_j}(s),
$$
and consequently
$$
f_{U_j}(s)-f_{V_j}(s)
=-\frac{s\Delta_j}{\theta}\,
\frac{D_{P_j}(s)}{D_{U_j}(s)D_{V_j}(s)}.
$$
For $s>0$ and unequal resistances, the sign of the transform difference is $-\operatorname{sgn}(\Delta_j)$. The exact first and second moment differences are
$$
\mu_{U_j}-\mu_{V_j}=\frac{\Delta_j}{\theta},
\qquad
m_{2,U_j}-m_{2,V_j}
=\frac{\Delta_j}{\theta}
\left[2(\mu_{U_j}+\mu_{V_j}-\mu_{P_j})-1\right].
$$
These statements compare discounted responses; they assert no stochastic dominance of the passage-time tails.

**Proof.** At $j=1$ one has $U_1=\beta\alpha\beta$ and $V_1=\beta\beta\alpha$, so $P_1=\beta$. The recurrence gives
$$
U_{j+1}=W_{j+1}V_j,\qquad V_{j+1}=W_{j+1}U_j.
$$
Thus $P_{j+1}=W_{j+1}P_j$ and the final pairs reverse at every step. Their total length is $F_{j+2}+F_{j+1}=F_{j+3}$, proving the prefix and parity assertions. Equal composition gives equal aggregate trajectories by Definition 1.1.

For a fixed word let $h_i=\mathbb E_i(1+s)^{-\tau_w}$, including $h_L=1$. Put
$$
J_{-1}=0,\qquad J_i=\frac{\theta}{r_{w_i}}(h_{i+1}-h_i).
$$
The exact first-step equation is $(1+s)h_i=\mathbb E_i h_{X_1}$, hence $J_i-J_{i-1}=s h_i$. Therefore
$$
\binom{h_{i+1}}{J_i}
=\mathsf T_{r_{w_i}}(s)\binom{h_i}{J_{i-1}},\qquad
\mathsf T_r(s)=
\begin{pmatrix}1+sr/\theta&r/\theta\\s&1\end{pmatrix}.
$$
With $e=(1,0)^{\mathsf T}$ and $h_L=1$, this gives
$$
D_w(s)=e^{\mathsf T}\mathsf T_{r_{w_{L-1}}}(s)\cdots
\mathsf T_{r_{w_0}}(s)e.
$$
The order of multiplication is the reverse of the order of letters. Direct multiplication yields
$$
\mathsf T_{r_\beta}(s)\mathsf T_{r_\alpha}(s)
-\mathsf T_{r_\alpha}(s)\mathsf T_{r_\beta}(s)
=\frac{s(r_\beta-r_\alpha)}{\theta}
\begin{pmatrix}1&0\\-s&-1\end{pmatrix}.
$$
The first row of the matrix on the right is $e^{\mathsf T}$. Multiplying the appropriate signed commutator by the transfer product for $P_j$ proves the factorization. All $D_w(s)$ are positive for $s\ge0$, so inversion proves the signed transform comparison.

The same finite response has the resolvent representation
$$
(B_w+sI)h=B_w\mathbf1,\qquad
D_w(s)=\frac{\det(B_w+sI)}{\det B_w}=\det(I+sG_w).
$$
The determinant identity is the finite birth-death spectral generating-function formula of J. A. Fill, [*The passage time distribution for a birth-and-death chain: Strong stationary duality gives a first stochastic proof*](https://arxiv.org/pdf/0707.4042v4), Theorem 1.2, used here as a proof ingredient. Indeed, if $\lambda_0,\ldots,\lambda_{L-1}$ are the transient eigenvalues, its formula at $z=(1+s)^{-1}$ gives
$$
f_w(s)=\prod_{a=0}^{L-1}\frac{1-\lambda_a}{1+s-\lambda_a}.
$$
All birth probabilities and all interior death probabilities are positive in Definition 5.1; no nonnegativity assumption on the transient eigenvalues is needed for that generating-function identity.

The geometric tail permits differentiation at $s=0$. Since
$$
D_w'(0)=\mu_w,\qquad
D_w''(0)=2\mu_w^2-m_{2,w}-\mu_w,
$$
the first derivative of the factorization gives $\mu_{U_j}-\mu_{V_j}=\Delta_j/\theta$. Its second derivative gives
$$
2(\mu_{U_j}^2-\mu_{V_j}^2)
-(m_{2,U_j}-m_{2,V_j})-(\mu_{U_j}-\mu_{V_j})
=\frac{2\Delta_j}{\theta}\mu_{P_j}.
$$
Substitution of the first difference proves the second. The ordered recurrence and composition bridge used here are those in [this volume, §§1 and 5](https://github.com/the-omega-institute/trureturing/blob/82197d4bd68d6491767cb20e99d3ed8ceb5520e3/docs/develop/theory/FIB_ATOM_STATISTICAL_LAWS.md), with the underlying source identities in [*Fibonacci Atomic Relation Generation*](https://github.com/the-omega-institute/trureturing/blob/4ab7dd1d2631b0a0859643815bcc2c442ce34e32/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md), Theorems 3.2, 3.4 and 8.2. $\square$

**Theorem 9.3 (A native two-edge obstruction to a single-resistance passage model).** On $W_2=\beta\alpha$ the exact response is
$$
D_{\beta\alpha}(s)
=1+\frac{s(r_\beta+2r_\alpha)}{\theta}
+\frac{s^2r_\alpha r_\beta}{\theta^2}.
$$
Replacing the two edges by one edge of resistance $R=r_\alpha+r_\beta$ and the same $\theta$ gives a different passage transform. Even choosing a single-edge resistance to match the mean cannot preserve the full transform for positive $r_\alpha,r_\beta$.

**Proof.** The transfer product $\mathsf T_{r_\alpha}\mathsf T_{r_\beta}$ gives the displayed polynomial. A single reflecting-to-absorbing edge of resistance $R$ has geometric passage time and denominator $1+sR/\theta$. The sum $r_\alpha+r_\beta$ already gives the wrong linear coefficient. A mean-matching resistance $r_\beta+2r_\alpha$ fixes that coefficient but still has zero quadratic coefficient, whereas $r_\alpha r_\beta/\theta^2>0$. This obstruction concerns collapsing the cut carrier to one edge. It does not exclude a model retaining the extra state or a memory variable. $\square$

## 10. Literal Fibonacci Green operators and passage laws

**Definition 10.1 (Quantity-scaled finite cells).** For the literal words $W_j=w(T_j)$ with $j\ge1$, retain the fixed parameters of Definition 5.1 and put
$$
L_j=F_{j+1},\qquad N_j=F_{j+3},\qquad
\epsilon_j=\frac{\delta}{N_j^2},\qquad
\overline r=\varphi^{-2}r_\alpha+\varphi^{-1}r_\beta,\qquad
D=\frac{\theta\varphi^4}{\delta\overline r}.
$$
Thus $\epsilon_j\tau_j$ is elapsed time divided by the squared total quantity. Write $K_j=K_{W_j}$, $B_j=B_{W_j}$ and $G_j=B_j^{-1}$. Embed a transient vector $f=(f_0,\ldots,f_{L_j-1})$ as the step function with value $f_i$ on $I_{j,i}=[i/L_j,(i+1)/L_j)$. Extend $G_j(i,m)$ by zero when either index is $L_j$. For $u,v\in[0,1]$ define
$$
\iota_j(u)=\begin{cases}\lfloor L_j u\rfloor,&u<1,\\L_j,&u=1,\end{cases}
\qquad
\mathcal K_j(u,v)=\epsilon_jL_jG_j(\iota_j(u),\iota_j(v)),
$$
and
$$
(\mathcal T_j f)(u)=\int_0^1\mathcal K_j(u,v)f(v)\,dv,
\qquad
\mathcal K(u,v)=\frac{1-\max(u,v)}D,\qquad
(\mathcal T f)(u)=\int_0^1\mathcal K(u,v)f(v)\,dv.
$$
On step functions $\mathcal T_j$ is exactly $\epsilon_jG_j$. Kernel and operator estimates use the supremum norm, with the displayed endpoint extensions. The parameter $s$ used for Laplace transforms below has reciprocal rescaled-time units; $s\epsilon_j$ and $s/D$ are dimensionless.

**Theorem 10.2 (Mechanical discrepancy gives a uniform quantity-scaled Green limit).** For every $0\le a\le b\le L_j$,
$$
\left|\sum_{k=a}^{b-1}r_{(W_j)_k}-\overline r(b-a)\right|
\le |r_\alpha-r_\beta|,
\qquad
|x_k-\varphi^2k|<1\quad(0\le k\le L_j).
$$
The transient Green matrix is exactly
$$
G_j(i,m)=\frac1\theta\sum_{k=\max(i,m)}^{L_j-1}r_{(W_j)_k},
\qquad 0\le i,m<L_j.
$$
If $c_j=\epsilon_j\overline rL_j^2/\theta$, then
$$
\sup_{u,v\in[0,1]}|\mathcal K_j(u,v)-\mathcal K(u,v)|
\le |c_j-D^{-1}|+
\frac{\epsilon_jL_j}{\theta}(\overline r+|r_\alpha-r_\beta|)
=O(L_j^{-1}).
$$
Consequently $\mathcal T_j\to\mathcal T$ in operator norm on bounded measurable functions, and
$$
\sup_{0\le k\le L_j}\left|\frac{x_k}{N_j}-\frac{k}{L_j}\right|\longrightarrow0.
$$
For continuous $f$, $y=\mathcal T f$ is the solution of
$$
-D y''=f,\qquad y'(0)=0,\qquad y(1)=0.
$$
Thus the limiting kernel has the reflecting Neumann condition at $0$ and the absorbing Dirichlet condition at $1$.

**Proof.** Put $a_F=\varphi^{-2}$. For $j\ge1$ the nested words $W_j$ are prefixes of the mechanical word of Theorem 3.2 with intercept $a_F$. Its $\alpha$ indicators are
$$
C_k=\lfloor(k+2)a_F\rfloor-\lfloor(k+1)a_F\rfloor.
$$
For an interval $[a,b)$ its $\alpha$ count $A_{a,b-a}$ differs from $a_F(b-a)$ by less than one. Therefore
$$
\sum_{k=a}^{b-1}r_{(W_j)_k}-\overline r(b-a)
=(r_\alpha-r_\beta)\bigl(A_{a,b-a}-a_F(b-a)\bigr).
$$
Also $x_k=3k-A_{0,k}$ and $3-a_F=\varphi^2$, proving both discrepancy estimates for the actual ordered cells, without a random-phase hypothesis. The mechanical-prefix identification is the one in [this volume, Theorems 3.2–3.3](https://github.com/the-omega-institute/trureturing/blob/82197d4bd68d6491767cb20e99d3ed8ceb5520e3/docs/develop/theory/FIB_ATOM_STATISTICAL_LAWS.md); its rotation-coding background is J. Berstel, [*Sturmian and Episturmian Words*](https://ligm.univ-eiffel.fr/~berstel/Articles/2007SturmianThessalonique.pdf), §3.

To check the inverse, give a vector $f$ the absorbing value $f_{L_j}=0$ and define
$$
y_i=\frac1\theta\sum_{k=i}^{L_j-1}r_{(W_j)_k}\sum_{m=0}^k f_m,
\qquad y_{L_j}=0.
$$
Then $(\theta/r_{(W_j)_i})(y_i-y_{i+1})=\sum_{m=0}^i f_m$. Taking the difference of consecutive fluxes, with zero left flux at cut $0$, gives $B_jy=f$. Exchanging the two finite sums gives the stated entries of $G_j$.

For $i=\iota_j(u)$ and $m=\iota_j(v)$ with $u,v<1$, the interval bound gives
$$
\mathcal K_j(u,v)
=c_j\left(1-\frac{\max(i,m)}{L_j}\right)+E_j(u,v),\qquad
|E_j(u,v)|\le\frac{\epsilon_jL_j}{\theta}|r_\alpha-r_\beta|.
$$
Replacing $\max(i,m)/L_j$ by $\max(u,v)$ changes the expression by at most $c_j/L_j=\epsilon_j\overline rL_j/\theta$. If either argument is $1$, both kernels vanish. The two-root Fibonacci formula gives
$$
N_j=\varphi^2L_j+O(L_j^{-1}),\qquad
c_j=D^{-1}+O(L_j^{-2}),\qquad \epsilon_jL_j=O(L_j^{-1}),
$$
which proves the uniform estimate and hence the operator norm limit. The same quantity discrepancy gives
$$
\left|\frac{x_k}{N_j}-\frac{k}{L_j}\right|
\le\frac1{N_j}+\left|\frac{\varphi^2L_j}{N_j}-1\right|.
$$
Finally, differentiating the limiting integral gives $y'(u)=-D^{-1}\int_0^u f(v)\,dv$ and $y''(u)=-f(u)/D$, with the stated boundary values. $\square$

**Theorem 10.3 (Passage-law and fixed-moment continuation of the native mean law).** For initial cuts $0\le i_j\le L_j$ with $i_j/L_j\to x\in[0,1]$, and every fixed $s\ge0$,
$$
\mathbb E_{i_j}\exp(-s\epsilon_j\tau_j)
\longrightarrow
\frac{\cosh(x\sqrt{s/D})}{\cosh(\sqrt{s/D})}.
$$
In particular the transform at the reflecting cut is $\operatorname{sech}(\sqrt{s/D})$. The nonnegative passage times converge in distribution to the law specified by this transform. For each fixed integer $p\ge1$ their moments converge to
$$
M_p(x)=p!\,(\mathcal T^p\mathbf1)(x),\qquad M_0(x)=1.
$$
Equivalently, for $p\ge1$,
$$
-D M_p''=pM_{p-1},\qquad M_p'(0)=0,\qquad M_p(1)=0.
$$
In particular,
$$
M_1(x)=\frac{1-x^2}{2D},\qquad
M_2(x)=\frac{5-6x^2+x^4}{12D^2},
$$
and at $x=0$ the limiting mean, second moment and variance are
$$
\frac1{2D},\qquad \frac5{12D^2},\qquad \frac1{6D^2}.
$$
These are passage-time and Green-operator limits for the fixed-unit-speed cut chain. They specify no spatial path topology, physical heat flow or physical realization, and retain the qualification of Theorem 8.1.

**Proof.** Let $h_{j,i}(s)=\mathbb E_i e^{-s\epsilon_j\tau_j}$ and set $h_{j,L_j}=1$. The discrete first-step equation gives exactly
$$
\bigl(B_j+(e^{s\epsilon_j}-1)I\bigr)h_j=B_j\mathbf1.
$$
Writing
$$
\gamma_j(s)=\frac{e^{s\epsilon_j}-1}{\epsilon_j}\longrightarrow s,
$$
its embedded version is
$$
h_j+\gamma_j(s)\mathcal T_jh_j=\mathbf1.
$$
This uses the discrete clock itself. Since $0\le h_j\le1$, Theorem 10.2 shows that $h_j$ is uniformly close to $1-\gamma_j(s)\mathcal T h_j$. The latter functions are uniformly bounded and have a common Lipschitz bound for fixed $s$, because $| (\mathcal T h_j)' |\le D^{-1}$. They therefore have uniformly convergent subsequences. Every subsequential limit satisfies
$$
h+s\mathcal T h=1.
$$
It is continuous, and differentiating twice gives
$$
D h''=s h,\qquad h'(0)=0,\qquad h(1)=1.
$$
The unique solution is the displayed hyperbolic-cosine ratio, including $h\equiv1$ at $s=0$. Uniqueness proves uniform convergence of the embedded transforms and hence convergence at the moving cuts. The bounded scaled first moments proved below give tightness. Every weak subsequential limit has this Laplace transform; uniqueness of a nonnegative law from its Laplace transform proves convergence in distribution.

For the moment calculation, write $M_{j,p}(i)=\mathbb E_i[(\epsilon_j\tau_j)^p]$ with $M_{j,p}(L_j)=0$ for $p\ge1$. Its first-step equation, separating the constant term from lower positive moments, is
$$
B_jM_{j,p}=\epsilon_j^p\mathbf1+
\sum_{k=1}^{p-1}\binom pk\epsilon_j^{p-k}K_jM_{j,k}.
$$
Since $G_jK_j=G_j-I$, on embedded transient vectors this becomes
$$
M_{j,p}=\epsilon_j^{p-1}\mathcal T_j\mathbf1+
\sum_{k=1}^{p-1}\binom pk\epsilon_j^{p-k-1}
(\mathcal T_j-\epsilon_j I)M_{j,k}.
$$
For $p=1$ this says $M_{j,1}=\mathcal T_j\mathbf1$. The operator norms are uniformly bounded. Induction therefore gives a uniform bound for each fixed moment, and all terms other than $k=p-1$ vanish in the limit for $p\ge2$. Applying the operator norm convergence and the induction hypothesis gives uniformly
$$
M_{j,p}\longrightarrow p\mathcal T M_{p-1}=p!\mathcal T^p\mathbf1.
$$
The next-moment bound also gives uniform integrability, so these functions are the moments of the limiting passage law. In particular the exact discrete second-moment identity is
$$
M_{j,2}=2\mathcal T_j^2\mathbf1-\epsilon_j\mathcal T_j\mathbf1;
$$
the discrete correction vanishes but has not been omitted before taking the limit. Differentiating $p\mathcal T M_{p-1}$ proves the boundary recurrence. Solving it for $p=1,2$ gives the two polynomials and the variance. The value $D=\theta\varphi^4/(\delta\overline r)$ is precisely the coefficient of [this volume, Theorem 5.3](https://github.com/the-omega-institute/trureturing/blob/82197d4bd68d6491767cb20e99d3ed8ceb5520e3/docs/develop/theory/FIB_ATOM_STATISTICAL_LAWS.md); here it controls the full passage transform and every fixed moment under the same hypotheses. The general scale-and-speed framework is classical, as in C. Stone, [*Limit theorems for random walks, birth and death processes, and diffusion processes*](https://doi.org/10.1215/ijm/1255645101). The literal-prefix estimates and quantity-scaled passage calculation above provide the required source-specific bridge directly, without invoking a path-process limit from that framework. $\square$

## 11. A literal-source speed-measure obstruction

**Definition 11.1 (An extension with nonconstant speed-measure weights).** Fix $0<\kappa<1$ and use the same words $W_j$, edge resistances, quantity coordinates, $\delta$ and $\epsilon_j$ as in Definition 10.1, but choose the common jump scale to satisfy
$$
0<\theta\le\frac{(1-\kappa)\min(r_\alpha,r_\beta)}2.
$$
At the transient cuts put
$$
b_j=\lfloor L_j/2\rfloor,\qquad
v_{j,i}=1-\kappa+\kappa L_j\mathbf1_{\{i=b_j\}},\qquad
V_j^{\mathrm{spd}}=\operatorname{diag}(v_{j,0},\ldots,v_{j,L_j-1}).
$$
Replace the probability of crossing either incident edge $k$ from cut $i$ by $\theta/(v_{j,i}r_{(W_j)_k})$, and hold with the remaining probability. Cut $0$ still reflects and $L_j$ still absorbs. The $v_{j,i}$ are weights of the speed measure, rather than jump probabilities: larger weights slow the chain. This is an extension outside Definition 5.1, whose weights remain identically one. Let $\tau_j^{(\kappa)}$ denote its passage time and define its normalized speed measure by
$$
\mu_j^{(\kappa)}=\frac1{L_j}\sum_{i=0}^{L_j-1}v_{j,i}\delta_{i/L_j},
\qquad
\mu^{(\kappa)}=(1-\kappa)\,du+\kappa\delta_{1/2}.
$$
Here $\delta_a$ denotes the unit point mass at $a$, distinct from the fixed time unit $\delta$; $du$ is Lebesgue measure on $[0,1]$.

**Theorem 11.2 (Equal mean speed measure and limiting first passage mean, unequal passage law).** The extended chains are stochastic, have exactly the same source words, resistances and aggregate quantity trajectories as the unit-weight chains, and satisfy
$$
\frac1{L_j}\sum_{i=0}^{L_j-1}v_{j,i}=1,
\qquad \mu_j^{(\kappa)}\Longrightarrow\mu^{(\kappa)}.
$$
Their scaled passage times from $0$ converge in distribution to a law with
$$
\lim_j\mathbb E_0(\epsilon_j\tau_j^{(\kappa)})=\frac1{2D},
\qquad
\lim_j\mathbb E_0[(\epsilon_j\tau_j^{(\kappa)})^2]
=\frac{5+\kappa^2}{12D^2}.
$$
Thus the limiting first moment agrees with Theorem 10.3, but the second moment and the limiting passage law differ whenever $\kappa>0$. The equality of first passage means asserted here is a limit equality; finite-cell passage means need not coincide. The ordered source, global mean speed-measure weight and common clock do not determine the passage law in this enlarged class.

**Proof.** Every $v_{j,i}\ge1-\kappa$, so the sum of the two possible crossing probabilities is at most $2\theta/((1-\kappa)\min(r_\alpha,r_\beta))\le1$. The boundary has only one incident crossing. All right crossings have positive probability and each finite chain has a geometric absorption tail. The sum of the weights is $L_j(1-\kappa)+\kappa L_j=L_j$. The uniform lattice measure converges to $du$, and $b_j/L_j\to1/2$, proving convergence of the speed measures. No source tree or quantity readout is changed.

If $B_j^{(\kappa)}$ is the new transient $I-K$, row scaling gives
$$
B_j^{(\kappa)}=(V_j^{\mathrm{spd}})^{-1}B_j,
\qquad (B_j^{(\kappa)})^{-1}=G_jV_j^{\mathrm{spd}}.
$$
Its rescaled Green action on an embedded vector is therefore
$$
(\mathcal T_j^{(\kappa)} f)(u)
=\int\mathcal K_j(u,v)f(v)\,d\mu_j^{(\kappa)}(v).
$$
For continuous $f$ this converges uniformly to
$$
(\mathcal T_\kappa f)(u)
=\frac1D\int (1-\max(u,v))f(v)\,d\mu^{(\kappa)}(v).
$$
Indeed, Theorem 10.2 bounds the kernel error uniformly and the measures have total mass one. For the limiting kernel, convergence of the lattice integral is a Riemann-sum statement uniform in $u$, since $(1-\max(u,v))f(v)$ is uniformly continuous on the square; the single atomic term converges uniformly as well. Moreover, $\|\mathcal T_j^{(\kappa)}\|$ is uniformly bounded. Induction in the discrete moment recurrence of Theorem 10.3 consequently gives, for every fixed $p$,
$$
\mathbb E_i[(\epsilon_j\tau_j^{(\kappa)})^p]
\longrightarrow p!\,(\mathcal T_\kappa^p\mathbf1)(x)
\quad\text{when }i/L_j\to x,
$$
with convergence uniform over the cuts. In this induction the limiting moment functions are continuous; the uniform operator bound controls the error from the preceding finite-cell moment, and the displayed Riemann-sum convergence applies to that fixed continuous limit. This requires no operator norm convergence of atomic measures to Lebesgue measure.

For completeness, the same compactness argument as in Theorem 10.3 gives convergence of the passage transforms. The exact equation is $h_j+\gamma_j(s)\mathcal T_j^{(\kappa)}h_j=1$. Replacing $\mathcal K_j$ by $\mathcal K$ gives continuous approximants with a common Lipschitz bound, because $0\le h_j\le1$ and the speed measures have mass one. Every uniform subsequential limit solves
$$
h+s\mathcal T_\kappa h=1.
$$
This equation has at most one solution. To see this, a difference $g$ of solutions is continuous, is twice differentiable away from $1/2$, and satisfies
$$
g''=\frac{s(1-\kappa)}Dg,\qquad
g'(0)=0,\qquad g(1)=0,\qquad
g'(1/2+)-g'(1/2-)=\frac{s\kappa}Dg(1/2).
$$
Integration by parts on the two intervals gives
$$
\int_0^1|g'|^2\,du+
\frac sD\left((1-\kappa)\int_0^1g^2\,du+\kappa g(1/2)^2\right)=0,
$$
so $g=0$, also at $s=0$ using $g(1)=0$. The uniform moment bounds give tightness and uniform integrability. Uniqueness of the limiting Laplace transforms then gives a limiting passage law with the computed moments.

Put $H(u,v)=1-\max(u,v)$ and $p_\kappa=1-\kappa$. The limiting first moment function is
$$
(\mathcal T_\kappa\mathbf1)(u)
=\frac1D\left[p_\kappa\frac{1-u^2}{2}
+\kappa H(u,1/2)\right].
$$
At $u=0$, $H(0,1/2)=1/2$, so this is $1/(2D)$. The second moment at $0$ is $2\mathcal T_\kappa^2\mathbf1(0)$. Expanding the two integrations over the continuous and atomic parts gives
$$
D^2(\mathcal T_\kappa^2\mathbf1)(0)
=p_\kappa^2\frac5{24}
+p_\kappa\kappa\left(\frac{11}{48}+\frac3{16}\right)
+\frac{\kappa^2}{4}
=\frac{5+\kappa^2}{24}.
$$
Here the four coefficients are, respectively,
$$
\int_0^1(1-u)\frac{1-u^2}{2}\,du=\frac5{24},\qquad
\int_0^1(1-u)H(u,1/2)\,du=\frac{11}{48},
$$
$$
H(0,1/2)\frac{1-(1/2)^2}{2}=\frac3{16},\qquad
H(0,1/2)H(1/2,1/2)=\frac14.
$$
Multiplying by two proves the second-moment formula. Its excess over the unit-weight second moment is $\kappa^2/(12D^2)>0$. The limiting law is therefore different, despite identical aggregate source trajectories, normalized total speed mass and limiting first passage mean. This supplies the missing local speed-measure distinction within the actual Fibonacci carrier; it does not alter the fixed-unit-speed conclusion of Theorem 10.3. The speed-measure distinction is part of the classical one-dimensional framework in Stone's [*Limit theorems for random walks, birth and death processes, and diffusion processes*](https://doi.org/10.1215/ijm/1255645101); the explicit common-source construction and its two moments are calculated here. $\square$

## 追加锚（本行以下为增补区）

## 12. 路径级反射—吸收极限

**定义 12.1（单位速度路径、时钟与边界测试域）。** 取第10.1节的逐字斐波那契词 $W_j$，固定 $r_\alpha,r_\beta>0$、$0<\theta\le\min(r_\alpha,r_\beta)/2$ 与 $\delta>0$，保留

$$
L_j=F_{j+1},\qquad N_j=F_{j+3},\qquad
\epsilon_j=\frac{\delta}{N_j^2},\qquad
\overline r=\varphi^{-2}r_\alpha+\varphi^{-1}r_\beta,\qquad
D=\frac{\theta\varphi^4}{\delta\overline r}.
$$

记 $r_i=r_{(W_j)_i}$。链的每个暂态切点具有单位速度权重：内部从 $i$ 右跳的概率为 $\theta/r_i$，左跳的概率为 $\theta/r_{i-1}$，其余概率持留；$0$ 只有右跳，$L_j$ 吸收。使用定义5.1的同一转移核，允许初态为任意切点概率律，并要求

$$
\operatorname{Law}(X_0/L_j)\Longrightarrow\nu_0
\quad\text{于 }[0,1].
$$

这是对初态的扩充，单位速度、边界和转移规则均保持定义5.1的含义。定义吸收后永久保持终点的阶梯路径

$$
Z_j(t)=\frac{X_{\lfloor t/\epsilon_j\rfloor}}{L_j},\qquad
Q_j(t)=\frac{x_{X_{\lfloor t/\epsilon_j\rfloor}}}{N_j}.
$$

以 $\widehat K_j$ 表示包括吸收点的完整核，以 $K_j$ 表示第10节的暂态子核。完整生成元为 $A_j=(\widehat K_j-I)/\epsilon_j$。连续吸收过程的测试域取

$$
\mathscr D_A=
\{f\in C^2([0,1]):f'(0)=0,\ f''(1)=0\},\qquad
Af(u)=Df''(u)\ (u<1),\qquad Af(1)=0.
$$

这里 $f(1)$ 可以任意取值；$f''(1)=0$ 使生成元在吸收点连续。若使用在命中 $1$ 时被杀死的半群，则另取 $f(1)=0$，对应诺伊曼左边界与狄利克雷右边界。完整吸收过程的测试函数值条件与被杀死半群的值条件须分别使用。

**定理 12.2（精确格林逆给出的路径测试校正）。** 对任意 $f\in C^2([0,1])$ 且 $f'(0)=0$，令

$$
b_f(u)=Df''(u),\qquad
\overline b_{j,i}=L_j\int_{i/L_j}^{(i+1)/L_j}b_f(v)\,dv,
$$

并以第10.2节的精确逆定义

$$
f_{j,i}=f(1)-\epsilon_j\sum_{m=0}^{L_j-1}
G_j(i,m)\overline b_{j,m}\quad(0\le i<L_j),\qquad
f_{j,L_j}=f(1).
$$

则在固定参数下

$$
\max_{0\le i\le L_j}|f_{j,i}-f(i/L_j)|=O(L_j^{-1}),
\qquad
(A_jf_j)_i=\overline b_{j,i}\ (i<L_j),\qquad
(A_jf_j)_{L_j}=0.
$$

将 $b_f$ 在吸收点的生成元值定义为 $0$ 后，暂态点上的生成元误差不超过 $b_f$ 的连续模 $\omega_{b_f}(L_j^{-1})$，吸收点上的误差为零。特别地，对 $f\in\mathscr D_A$，此为连续测试域上的一致生成元逼近。相邻校正值还满足

$$
f_{j,i+1}-f_{j,i}
=\frac{\epsilon_jr_i}{\theta}
\sum_{m=0}^{i}\overline b_{j,m},\qquad
\max_{i<L_j}|f_{j,i+1}-f_{j,i}|
\le\frac{\epsilon_jL_j\max(r_\alpha,r_\beta)}{\theta}
\|b_f\|_\infty=O(L_j^{-1}).
$$

**证明。** 第10.2节的连续格林算子满足

$$
\mathcal T b_f=f(1)-f,
$$

因为两边的二阶导数均为 $-f''$，左端导数为零，右端值为零。单元平均使 $\epsilon_jG_j\overline b_j$ 恰为 $\mathcal T_jb_f$ 的阶梯值；第10.2节的核一致误差给出校正值的 $O(L_j^{-1})$ 误差。完整生成元作用于常数 $f(1)$ 为零，而作用于吸收端为零的暂态向量时为 $-B_j/\epsilon_j$。由 $B_jG_j=I$，得到 $A_jf_j=\overline b_j$，包括所述吸收端值。单元平均与左端采样的差由连续模控制。最后将第10.2节的累积通量公式用于 $\overline b_j$，即得相邻差；$\epsilon_jL_j^2\to\delta/\varphi^4$ 给出其量级。若 $f''(1)\ne0$，上述离散恒等式仍成立，但分段定义的 $Af$ 在吸收点不连续，不能将它直接作为连续生成元域的元素。$\square$

**定理 12.3（逐字切链的反射—吸收路径极限）。** 在定义12.1的全部假设下，对每个固定 $T<\infty$，

$$
Z_j\Longrightarrow Z
\quad\text{于 }D([0,T],[0,1])\text{ 的 }J_1\text{ 拓扑}.
$$

极限从 $\nu_0$ 出发，是扩散系数为 $D$、在 $0$ 反射、首次到达 $1$ 后永久保持 $1$ 的布朗过程。在吸收时间 $\tau=\inf\{t:Z_t=1\}$ 之前可写成

$$
dZ_t=\sqrt{2D}\,dB_t+dK_t,\qquad
K_0=0,\qquad K\text{ 连续且单调不减},\qquad
\int_0^{t\wedge\tau}\mathbf1_{\{Z_s>0\}}\,dK_s=0;
\qquad Z_t=1\ (t\ge\tau).
$$

其中 $B$ 是标准布朗运动，独立于所给初态。

**证明。** 先证明停时紧性，而不从格林收敛直接推断路径收敛。取

$$
h(u)=u^2-u^3/3,\qquad h'(0)=0,\qquad h''(1)=0.
$$

$h$ 将 $[0,1]$ 连续且严格递增地映到 $[0,2/3]$，其逆在这个紧区间上一致连续。用定理12.2构造 $h_j$。若 $\mathcal F_n$ 为切链历史，则

$$
M_{j,n}=h_{j,X_n}-h_{j,X_0}
-\epsilon_j\sum_{k=0}^{n-1}
\mathbf1_{\{X_k<L_j\}}\overline b_{h,j,X_k}
$$

是鞅。其漂移每步绝对值不超过 $\epsilon_j\|Dh''\|_\infty$。相邻校正差为 $O(L_j^{-1})$，故

$$
\mathbb E\bigl[(M_{j,n+1}-M_{j,n})^2\mid\mathcal F_n\bigr]
\le C L_j^{-2}\le C'\epsilon_j.
$$

常数与 $j$、初态和停时无关。把连续时间停时上取整至时钟格点只引入至多一跳的误差。鞅可选停止与有界漂移于是给出：对 $\sigma_j\le T$ 及 $0\le a_j\le\eta_j\to0$ 的确定增量，

$$
\mathbb E\left|h_{j,X_{\lfloor(\sigma_j+a_j)/\epsilon_j\rfloor}}
-h_{j,X_{\lfloor\sigma_j/\epsilon_j\rfloor}}\right|^2
\le C_T\bigl(\eta_j+\epsilon_j+(\eta_j+\epsilon_j)^2\bigr).
$$

这就是阿尔杜斯停时增量准则所需的控制。值域有界，$h_j-h=O(L_j^{-1})$，再由 $h^{-1}$ 的一致连续性，得到 $Z_j$ 的紧性。原路径每跳至多 $1/L_j\to0$，配合上述停时控制，任意子序列极限均为连续路径。

对 $f\in\mathscr D_A$ 使用同样的校正鞅。校正值一致趋于 $f$，生成元一致趋于连续的 $Af$，阶梯积分与格点求和的差为 $O(\epsilon_j)$。在任意收敛子序列上，对有界连续的过去历史函数乘以上述鞅增量再取期望；所有项一致有界，$J_1$ 收敛到连续路径使积分也收敛。因此极限满足

$$
f(Z_t)-f(Z_0)-\int_0^t Af(Z_s)\,ds
\quad\text{为鞅},\qquad f\in\mathscr D_A,
\qquad\operatorname{Law}(Z_0)=\nu_0.
$$

最后识别并唯一化这一边界鞅问题。对任意 $\lambda>0$ 与 $g\in C([0,1])$，其预解边值问题为

$$
\lambda f-Df''=g\quad(0\le u<1),\qquad
f'(0)=0,\qquad f(1)=g(1)/\lambda.
$$

线性二阶方程有唯一 $C^2$ 解；连续延伸给出 $f''(1)=0$，所以解属于 $\mathscr D_A$。唯一性也可由齐次差的能量恒等式

$$
\lambda\int_0^1 f^2\,du+D\int_0^1(f')^2\,du=0
$$

直接得到。该域在 $C([0,1])$ 中稠密，满足正最大值原理，而且每个 $\lambda-A$ 的值域均为整个连续函数空间；预解式的唯一性给出相应费勒生成元及鞅问题的唯一性。将反射布朗运动停在首次到达 $1$ 的时刻，由伊藤公式、$f'(0)=0$ 与吸收后的 $Af(1)=0$ 可知它解此鞅问题。因此所有子序列极限均为所述反射—吸收过程，得到整列收敛。

一维尺度与速度测度方法的文献背景见查尔斯·斯通的[《随机游走、生灭过程与扩散过程的极限定理》](https://doi.org/10.1215/ijm/1255645101)。此处连接逐字斐波那契源的具体步骤是第10.2节的精确逆、上述离散校正、停时紧性和边界鞅问题；一般扩散极限框架作为背景，不替代这些步骤。$\square$

**定理 12.4（数量嵌入、插值及缺失缩放的边界）。** 定理12.3的数量路径 $Q_j$ 在 $J_1$ 拓扑下具有同一极限。分别将 $Z_j$、$Q_j$ 在相邻时钟格点间作线性插值，所得连续路径在 $C([0,T])$ 的一致范数拓扑下弱收敛到 $Z$。初态律收敛与平方时钟缩放不能由源递归代替。

**证明。** 第10.2节给出确定性控制

$$
\sup_{t\le T}|Q_j(t)-Z_j(t)|
\le\max_{0\le k\le L_j}\left|\frac{x_k}{N_j}-\frac{k}{L_j}\right|
\longrightarrow0.
$$

这比 $J_1$ 距离控制更强。切点插值与原阶梯路径的距离不超过 $1/L_j$，数量插值与其原阶梯路径的距离不超过 $3/N_j$。极限路径连续，故紧性与这些消失的误差给出所述连续路径弱收敛；阶梯路径本身仍视为 $D([0,T])$ 的元素。

若交替取初态 $X_0=0$ 与 $X_0=L_j$，时刻零的边缘律交替为 $\delta_0$ 与 $\delta_1$，整列路径律不能收敛。若从 $0$ 出发却只保留未缩放时钟 $X_{\lfloor t/\delta\rfloor}/L_j$，则

$$
\sup_{t\le T}\frac{X_{\lfloor t/\delta\rfloor}}{L_j}
\le\frac{\lfloor T/\delta\rfloor}{L_j}\longrightarrow0.
$$

极限退化为零路径，而非定理12.3的扩散。$\square$

**定理 12.5（路径桥的结论范围）。** 定理12.3在第10.2、10.3节的格林与通过时间结论上增加了路径紧性和边界鞅问题识别；其结论是所给数学模型的路径律弱收敛。它不提供原概率空间上的逐样本一致收敛、物理热流或热力学实现，也不推出第11节一般速度测度扩展的路径极限。源生成律和多个探针的联合律须另给共同实现与耦合条件。

**证明。** 紧性与唯一鞅问题只决定路径分布；弱收敛不指定不同 $j$ 之间的样本耦合。第11.2节已有同源、同总速度质量、同左端极限均值而通过律不同的扩展，第6.4节已有边缘轨迹律相同而联合律不同的模型，第8.1节区分空间计数、输运时钟及物理实现。定理12.3补足的是单位速度切链的输运路径桥，未增添这些额外识别前提。首次命中时间泛函并非在所有连续吸收路径上都具有 $J_1$ 连续性；例如停在 $1$ 的路径可由始终低于 $1$ 的路径一致逼近。因此这里只保留第10.3节的通过时间分布与固定矩结论，不据路径收敛宣称路径和吸收时间的联合收敛。$\square$

## 13. 半群收敛的范围与负谱边界

**定义 13.1（单元嵌入、投影与被杀死半群）。** 以下始终使用第12节的固定单位速度模型及暂态子核。令

$$
(J_jv)(u)=v_i\quad\left(u\in I_{j,i}
=[i/L_j,(i+1)/L_j)\right),\qquad (J_jv)(1)=0,
$$

$$
(P_jf)_i=L_j\int_{I_{j,i}}f(u)\,du,\qquad
P_jJ_j=I,\qquad
H_j=\frac{I-K_j}{\epsilon_j},\qquad T_j=H_j^{-1}=\epsilon_jG_j.
$$

离散向量的 $p$ 范数使用质量 $1/L_j$。于是 $J_j$ 为等距嵌入，$P_j$ 为压缩投影。连续算子为 $H=-D\partial^2$，具有诺伊曼左边界和狄利克雷右边界，其逆为第10节的 $\mathcal T$。记

$$
S_j(t)=J_jK_j^{\lfloor t/\epsilon_j\rfloor}P_j,
\qquad S(t)=e^{-tH},\qquad
C_D=\{f\in C([0,1]):f(1)=0\}.
$$

$S(t)$ 是反射于 $0$、命中 $1$ 时被杀死的热半群。对 $f\in C_D$，它等于第12节完整吸收过程的期望作用；这里不把完整吸收过程在常数函数上的作用与被杀死半群混用。$S_j$ 是用阶梯时钟采样的算子族，一般不满足所有实数时刻的半群恒等式。

**定理 13.2（正预解式与原阶梯时钟的拉普拉斯公式）。** 对固定 $\lambda>0$，定义

$$
R_j(\lambda)=T_j(I+\lambda T_j)^{-1}
=(\lambda+H_j)^{-1},\qquad
\mathcal R_j(\lambda)=J_jR_j(\lambda)P_j,
\qquad R(\lambda)=(\lambda+H)^{-1}.
$$

对每个 $1\le p\le\infty$，有

$$
\|\mathcal R_j(\lambda)-R(\lambda)\|_{p\to p}
=O(L_j^{-1}).
$$

原阶梯时钟的精确公式则为

$$
\gamma_j(\lambda)=\frac{e^{\lambda\epsilon_j}-1}{\epsilon_j},
\qquad
\int_0^\infty e^{-\lambda t}S_j(t)\,dt
=\frac{\gamma_j(\lambda)}{\lambda}
\mathcal R_j(\gamma_j(\lambda)),
$$

从而该拉普拉斯算子与 $R(\lambda)$ 的范数差为 $O(L_j^{-1})+O(\epsilon_j)$。此积分按单元函数的核积分理解；$p=\infty$ 时也可逐点使用同一公式。

**证明。** 嵌入的 $J_jT_jP_j=\mathcal T_j$ 正是第10节的积分算子。其核一致误差为 $O(L_j^{-1})$，故在所有上述 $p$ 空间中都有同量级算子误差。$K_j$ 对计数测度对称且为次随机核，连续与离散的被杀死半群在这些空间中均为压缩。因此正预解式满足 $\|\mathcal R_j(\lambda)\|,\|R(\lambda)\|\le1/\lambda$，且

$$
\|(I+\lambda\mathcal T_j)^{-1}\|,
\|(I+\lambda\mathcal T)^{-1}\|\le2,
$$

这里在阶梯子空间之外，前一逆算子为恒等作用。预解式恒等式给出

$$
\mathcal R_j(\lambda)-R(\lambda)
=(I+\lambda\mathcal T_j)^{-1}
(\mathcal T_j-\mathcal T)(I+\lambda\mathcal T)^{-1},
$$

证明第一项估计。再对每个时钟区间积分并求几何级数，得到

$$
\begin{aligned}
\int_0^\infty e^{-\lambda t}S_j(t)\,dt
&=\frac{1-e^{-\lambda\epsilon_j}}{\lambda}
J_j(I-e^{-\lambda\epsilon_j}K_j)^{-1}P_j\\
&=\frac{\gamma_j(\lambda)}{\lambda}
J_j(H_j+\gamma_j(\lambda))^{-1}P_j.
\end{aligned}
$$

固定 $\lambda$ 时，$\gamma_j(\lambda)-\lambda=O(\epsilon_j)$；用正预解式恒等式控制参数误差，即得第二项估计。泊松化算子 $J_je^{-tH_j}P_j$ 的拉普拉斯算子才是 $\mathcal R_j(\lambda)$。泊松化是另一种时钟，不能把它写成原来的 $S_j(t)$。$\square$

**定理 13.3（固定初值的强收敛）。** 对任意固定 $1\le p<\infty$、任意固定 $f\in L^p([0,1],du)$ 及任意 $0<a<b<\infty$，

$$
\lim_{j\to\infty}\sup_{a\le t\le b}
\|S_j(t)f-S(t)f\|_p=0.
$$

对任意固定 $f\in C_D$，相应地有

$$
\lim_{j\to\infty}\sup_{a\le t\le b}
\sup_{u\in[0,1]}|S_j(t)f(u)-S(t)f(u)|=0.
$$

这些量词先固定初值，再令 $j\to\infty$；没有在单位球上对所有初值同时取上确界，也没有给整个 $L^\infty$ 或所有有界可测初值的强收敛结论。

**证明。** 不能仅以正预解式收敛替代离散时钟的谱控制。$\mathcal T_j$ 是非负、自伴、有限秩算子，且在 $L^2$ 算子范数下趋于紧算子 $\mathcal T$。后者的简单特征对为

$$
e_m(u)=\sqrt2\cos((m+1/2)\pi u),\qquad
\rho_m=\frac1{D(m+1/2)^2\pi^2},\qquad m=0,1,\ldots.
$$

固定 $m$，孤立简单特征值的扰动给出 $\rho_{j,m}\to\rho_m$ 及适当定向的阶梯特征函数 $e_{j,m}\to e_m$ 于 $L^2$。由核一致逼近，还具有 $\mathcal T_j\to\mathcal T$ 于 $L^2\to L^\infty$ 的算子范数；将

$$
e_{j,m}=\rho_{j,m}^{-1}\mathcal T_je_{j,m},\qquad
e_m=\rho_m^{-1}\mathcal Te_m
$$

相减，得到包括右端零值在内的一致收敛。在这个固定模态上，原离散时钟给出

$$
S_j(t)e_{j,m}
=\left(1-\frac{\epsilon_j}{\rho_{j,m}}\right)^{\lfloor t/\epsilon_j\rfloor}e_{j,m}
\longrightarrow e^{-t/\rho_m}e_m,
$$

收敛在 $[a,b]$ 上一致。$S_j(t)$ 与 $S(t)$ 的 $p$ 范数及上确界范数均不增，所以把 $e_m$ 换成 $e_{j,m}$ 的误差也一致消失。

这些余弦函数的有限线性组合在 $C_D$ 中一致稠密：把连续函数在 $0$ 偶反射、在 $1$ 反号延拓，使用保持这两种对称性的三角多项式逼近即可。$C_D$ 又在每个有限 $p$ 的 $L^p$ 中稠密。先在有限模态组合上收敛，再用压缩性控制初值逼近误差，得到两项结论。该稠密性不适用于整个 $L^\infty$，故不作相应外推。$\square$

**定理 13.4（允许端点的近负一模态阻止算子范数收敛）。** 取定义5.1允许的参数

$$
r_\alpha=r_\beta=r>0,\qquad\theta=r/2,
\qquad D=\frac{\varphi^4}{2\delta}.
$$

对长度 $L=L_j$，暂态核在 $0$ 的持留概率为 $1/2$，相邻暂态切点间的跳率均为 $1/2$，其余暂态对角元为零。令

$$
q_L=\frac{2\pi}{2L+1},\qquad
\lambda_L=-\cos q_L,\qquad
v_i=(-1)^i\sin\bigl(q_L(i+1/2)\bigr),\quad0\le i<L.
$$

则 $K_jv=\lambda_Lv$。对每个固定 $t>0$ 及每个 $1\le p\le\infty$，有

$$
\liminf_{j\to\infty}\|S_j(t)-S(t)\|_{p\to p}
\ge e^{-D\pi^2t}>0.
$$

因此原离散时钟下的全空间算子范数收敛失败，甚至固定正时间也失败；这与定理13.3对每个固定初值的强收敛相容。

**证明。** 暂态矩阵的边界可写为虚点条件 $v_{-1}=v_0$、$v_L=0$。所给向量满足

$$
v_{-1}=\sin(q_L/2)=v_0,\qquad
v_L=(-1)^L\sin\pi=0,
$$

且内部恒等式为 $(v_{i-1}+v_{i+1})/2=-\cos(q_L)v_i$，所以左端半系数和右端吸收条件也逐项成立。随着 $L\to\infty$，$\lambda_L\to-1$，并且

$$
1-|\lambda_L|=\frac{\pi^2}{2L^2}+o(L^{-2}),\qquad
\epsilon_jL_j^2\longrightarrow\frac1{2D},\qquad
|\lambda_{L_j}|^{\lfloor t/\epsilon_j\rfloor}
\longrightarrow e^{-D\pi^2t}.
$$

把 $J_jv$ 按其 $p$ 范数归一化为 $\widetilde v_j$。有限 $p$ 时归一化前的范数趋于 $(\int_0^1\sin^p(\pi u)\,du)^{1/p}>0$，$p=\infty$ 时趋于 $1$。它是逐单元交替的符号乘以一致趋于 $\sin(\pi u)$ 的振幅。对固定 $t>0$，混合边界热核在闭正方形上连续；配对相邻单元并使用核的一致连续性，得到

$$
\|S(t)\widetilde v_j\|_\infty\longrightarrow0,
\qquad S_j(t)\widetilde v_j
=\lambda_{L_j}^{\lfloor t/\epsilon_j\rfloor}\widetilde v_j.
$$

由三角不等式即得所述下界。这一初值随 $j$ 改变，所以不反驳固定初值结论。此高频模态在正预解式中的逆特征值仅为 $\epsilon_j/(1-\lambda_{L_j})=O(\epsilon_j)$，说明第10.2节的格林范数收敛与此反例可以同时成立。泊松化对该模态使用 $e^{-t(1-\lambda_{L_j})/\epsilon_j}$，也不同于原离散时钟的交替衰减。$\square$

## 14. 平滑速度校准的有限精确反例

**定义 14.1（非原子极限的局部速度扩展）。** 此节在定义5.1之外允许局部速度权重。固定 $r_\alpha=r_\beta=1$、$\theta=1/8$，保留逐字源 $W_j$、左右边界、$\delta>0$ 及 $\epsilon_j=\delta/N_j^2$。对 $L=L_j$ 和 $0\le i<L$ 定义

$$
z_i=\frac{i+1/2}{L},\qquad
a_{L,i}=6z_i^2-6z_i+1+\frac1{2L^2},\qquad
\eta=\frac9{16},\qquad v_{j,i}=1+\eta a_{L,i}.
$$

从切点 $i$ 跨越任一邻边的概率改为 $\theta/v_{j,i}$，其余概率持留；$L$ 吸收。令 $V_j=\operatorname{diag}(v_{j,i})$。单位模型的 $B_j,G_j$ 满足扩展模型关系

$$
B_j^{(v)}=V_j^{-1}B_j,\qquad
G_j^{(v)}=G_jV_j.
$$

**定理 14.2（质量、一阶矩和有限均值均相同而路径律不同）。** 定义14.1的权重满足

$$
v_{j,i}\ge\frac{23}{32},\qquad
\sum_{i=0}^{L-1}v_{j,i}=L,\qquad
\sum_{i=0}^{L-1}i v_{j,i}=\frac{L(L-1)}2.
$$

扩展链为随机核，且从 $0$ 出发的离散步数均值与单位模型在每个有限 $L$ 上精确相同：

$$
\mathbb E_0\tau_j^{(v)}=\mathbb E_0\tau_j=4L(L+1).
$$

但是在 $W_3=\beta\alpha\beta$、$L=3$ 上，扩展权重为 $(9/8,3/4,9/8)$，并有

$$
\mathbb E_0\tau_3^2=3920,\qquad
\mathbb E_0(\tau_3^{(v)})^2=3912,\qquad
\Pr_0(X_1=1)=\frac18,\qquad
\Pr_0(X_1^{(v)}=1)=\frac19.
$$

相同源、速度总质量、切点坐标的一阶矩和精确左端均值仍不识别路径律。

**证明。** 配方给出

$$
a_{L,i}=6(z_i-1/2)^2-1/2+1/(2L^2)\ge-1/2,
$$

所以 $v_{j,i}\ge1-9/32=23/32$。内部两次跳跃的总概率至多 $2\theta/(23/32)=8/23<1$。进一步展开

$$
L^2a_{L,i}=6i^2+(6-6L)i+L^2-3L+2.
$$

代入 $\sum i=L(L-1)/2$、$\sum i^2=L(L-1)(2L-1)/6$、$\sum i^3=L^2(L-1)^2/4$，得到 $\sum a_{L,i}=\sum i a_{L,i}=0$，证明两项校准恒等式。等阻抗下，第10.2节的逆为 $G_j(i,m)=8(L-\max(i,m))$，故

$$
\mathbb E_0\tau_j^{(v)}
=8\sum_{m=0}^{L-1}(L-m)v_{j,m}
=8\left(L^2-\frac{L(L-1)}2\right)=4L(L+1).
$$

$L=3$ 时，令 $\mathbf1=(1,1,1)^{\mathsf T}$，则

$$
G_3=8\begin{pmatrix}3&2&1\\2&2&1\\1&1&1\end{pmatrix},\qquad
G_3\mathbf1=(48,40,24)^{\mathsf T},\qquad
G_3V_3\mathbf1=(48,39,24)^{\mathsf T}.
$$

任意离散吸收链的二阶矩向量为 $2G^2\mathbf1-G\mathbf1$，如第10.3节的离散校正公式。代入 $G_3$ 与 $G_3V_3$，左端分量分别为

$$
2\cdot1984-48=3920,\qquad
2\cdot1980-48=3912.
$$

首步右跳概率为 $\theta/v_{3,0}=(1/8)/(9/8)=1/9$，已经与单位模型不同。这些计算均使用同一实际三边载体，无需中点原子。$\square$

**定理 14.3（平滑速度密度的通过矩边界）。** 定义14.1的归一化速度测度及其极限为

$$
\mu_j^{(v)}=\frac1{L_j}\sum_{i=0}^{L_j-1}v_{j,i}\delta_{i/L_j}
\Longrightarrow w_\eta(u)\,du,
\qquad w_\eta(u)=1+\eta(6u^2-6u+1).
$$

在此节的 $D=\varphi^4/(8\delta)$ 下，从 $0$ 出发的缩放通过时间收敛到具有下列矩的通过律：

$$
\lim_j\mathbb E_0[\epsilon_j\tau_j^{(v)}]=\frac1{2D},\qquad
\lim_j\mathbb E_0[(\epsilon_j\tau_j^{(v)})^2]
=\frac{5/12+\eta^2/210}{D^2}.
$$

这给出平滑、严格正速度密度下同均值而不同通过律的边界，不把该扩展移入第12节的单位速度路径定理。

**证明。** 权重是连续多项式的中点采样加 $O(L_j^{-2})$ 常数，且始终有正下界；将采样点由中点改到左端只引入 $O(L_j^{-1})$ 误差，所以所述测度弱收敛成立。第10.2节的核估计给出对每个连续 $f$ 的一致格林收敛

$$
(\mathcal T_\eta f)(u)
=\frac1D\int_0^1(1-\max(u,v))f(v)w_\eta(v)\,dv.
$$

这些算子范数一致有界。第11.2节的通过变换紧性和离散矩递推同样适用：变换的极限满足 $h+s\mathcal T_\eta h=1$，等价于

$$
Dh''=s w_\eta h,\qquad h'(0)=0,\qquad h(1)=1.
$$

正密度的能量恒等式给出唯一性，固定矩逐次收敛到 $p!\mathcal T_\eta^p\mathbf1$。此论证只使用通过律和连续测试格林收敛。令

$$
A_\eta(u)=\frac{1-u^2}{2}
-\frac\eta2 u^2(1-u)^2.
$$

直接求导得 $-A_\eta''=w_\eta$、$A_\eta'(0)=0$、$A_\eta(1)=0$，故 $\mathcal T_\eta\mathbf1=A_\eta/D$。其左端值为 $1/(2D)$。二阶矩为

$$
\frac2{D^2}\int_0^1(1-u)w_\eta(u)A_\eta(u)\,du
=\frac{5/12+\eta^2/210}{D^2}.
$$

展开积分时一次项为零，二次项为 $\eta^2/210$；$\eta=9/16$ 时系数为 $22481/53760$，严格大于单位密度的 $5/12$。因此无原子的平滑速度扩展也保留第11节的不可识别性机制。$\square$

**定理 14.4（所有起点精确均值的校准能力）。** 固定有限载体、阻抗、$\theta$、反射与吸收边界，在定义14.1的局部行缩放规则下，允许任意使转移核随机的正权重 $v$。令 $m=(\mathbb E_i\tau^{(v)})_{i=0}^{L-1}$ 为所有暂态起点的精确离散均值向量，则

$$
v=B_jm.
$$

因此所有起点的均值向量识别全部速度权重，并在初态律也给定时识别完整路径律。若给的是实际经过时间均值，须先用给定时钟除以 $\delta$ 得到上述步数均值。单一起点的均值在 $L\ge2$ 的一般局部速度类中不能完成这一识别。

**证明。** 首步方程为 $B_j^{(v)}m=\mathbf1$。由 $B_j^{(v)}=V_j^{-1}B_j$，得到 $B_jm=V_j\mathbf1=v$。固定阻抗与跳尺度后，每个局部权重确定该行的两次跳跃概率及持留概率，因而确定核与所给初态的所有路径分布。单一起点 $i$ 的均值仅为 $m_i=\sum_kG_j(i,k)v_k$，是一个线性约束。在具有严格持留余量的正权重内部，$L\ge2$ 时该线性泛函具有非零核，可作足够小的权重扰动并保持随机性与同一均值；定义14.1与定理14.2进一步同时保持了总质量及一阶矩。校准结论依赖完整均值向量和固定动力学参数，不把源递归或数量坐标当作这些数据的替代。$\square$

## 追加锚（本行以下为增补区）

## 15. 同轨占用二点联合律

**定义 15.1（固定单位速度模型与同轨占用量）。** 始终使用定义5.1与定义10.1的模型：固定 $r_\alpha,r_\beta>0$、$0<\theta\le\min(r_\alpha,r_\beta)/2$ 与 $\delta>0$，取逐字源

$$
W_0=\alpha,\qquad W_1=\beta,\qquad W_{j+2}=W_{j+1}W_j,
\qquad j\ge0,
$$

对 $j\ge1$ 保留

$$
\begin{aligned}
L_j&=F_{j+1},& N_j&=F_{j+3},& \epsilon_j&=\frac{\delta}{N_j^2},\\
\overline r&=\varphi^{-2}r_\alpha+\varphi^{-1}r_\beta,
&D&=\frac{\theta\varphi^4}{\delta\overline r},
&h_j&=\epsilon_jL_j.
\end{aligned}
$$

在切点 $0,\ldots,L_j$ 上，每个暂态切点的速度权重恒为一。内部从 $i$ 向右跨边的概率为 $\theta/r_{(W_j)_i}$，向左跨边的概率为 $\theta/r_{(W_j)_{i-1}}$，其余概率持留；$0$ 只有右跳而反射，$L_j$ 吸收。初态固定为 $X_0=0$，令 $\tau_j=\inf\{n\ge0:X_n=L_j\}$。以下所有联合量都由这条链的同一次随机历史读取，期望与协方差均取其初态为 $0$ 的概率律。

固定 $j$ 时暂记 $L=L_j$、$\tau=\tau_j$，对 $0\le a<L$ 定义

$$
V_a=\sum_{0\le n<\tau}{\bf1}_{\{X_n=a\}},\qquad
q_a=\frac1\theta\sum_{k=a}^{L-1}r_{(W_j)_k}.
$$

同时规定 $V_L=q_L=0$。占用计数包含 $n=0$，排除吸收步 $n=\tau$。沿用 $K_j$、$B_j=I-K_j$、$G_j=B_j^{-1}$，以及定义10.1的映射

$$
\iota_j(u)=\begin{cases}\lfloor L_j u\rfloor,&0\le u<1,\\L_j,&u=1,\end{cases}
\qquad
\ell_j(u)=h_jV_{\iota_j(u)},\qquad
\kappa(u)=\frac{1-u}{D}\quad(0\le u\le1).
$$

$u$ 是归一化切点坐标；数量缩放通过 $N_j$ 与 $\epsilon_j$ 实现，和数量位置 $x_k/N_j$ 的对应由定理10.2给出。

**定理 15.2（数量缩放的二点极限、指数边缘与一致协方差）。** 固定 $0\le u<v<1$ 及 $s,t\ge0$，则

$$
\mathbb E_0 e^{-s\ell_j(u)-t\ell_j(v)}
\longrightarrow
\left[1+\kappa(u)s+\kappa(v)t
+\kappa(v)\bigl(\kappa(u)-\kappa(v)\bigr)st\right]^{-1}.
$$

每个固定 $u<1$ 的 $\ell_j(u)$ 依分布收敛到均值为 $\kappa(u)$ 的指数随机变量；$u=1$ 时 $\ell_j(1)$ 恒为零。协方差在整个闭方形上一致满足

$$
\sup_{u,v\in[0,1]}
\left|\operatorname{Cov}_0\bigl(\ell_j(u),\ell_j(v)\bigr)
-\frac{(1-\max(u,v))^2}{D^2}\right|
=O(L_j^{-1}).
$$

此估计的常数可依赖固定的阻抗、跳尺度与时钟参数，均不随 $u,v,j$ 变化。

**证明。** 先在固定有限链上应用离散费曼—卡茨（Feynman–Kac）与卡茨（Kac）矩公式框架。以下有限二点变换与时序混合矩是这些经典框架在定义15.1模型中的具体使用。

先求有限二点变换与同点合并。对 $0\le a<b<L$ 与 $s,t\ge0$，记 $A=q_a$、$R=q_b$，则

$$
\mathbb E_0 e^{-sV_a-tV_b}
=\left[1+A(e^s-1)+R(e^t-1)
+R(A-R)(e^s-1)(e^t-1)\right]^{-1}.
$$

这里用 $R$ 表示二点公式中的右侧尾阻抗，避免与矩阵 $B_j$ 混用。同点的精确式为

$$
\mathbb E_0 e^{-sV_a-tV_a}
=\left[1+q_a(e^{s+t}-1)\right]^{-1}.
$$

若一个探针位于吸收点，其占用恒为零，变换只保留另一个探针的单点式。

给暂态切点设置非负行势 $s_i$，令

$$
H_i=\mathbb E_i\exp\left(-\sum_{0\le n<\tau}s_{X_n}\right),
\qquad H_L=1,\qquad d_i=e^{s_i}-1.
$$

$H_i$ 是首步计算所需的继续运行期望，最终读取的是 $H_0$。由于当前步也计入占用，首步式为

$$
e^{s_i}H_i=\sum_{m<L}K_j(i,m)H_m+
\left(1-\sum_{m<L}K_j(i,m)\right).
$$

右侧最后一项是下一步吸收的贡献。于是，在暂态向量上恰有

$$
\bigl(B_j+\operatorname{diag}(d)\bigr)H=B_j\mathbf1,
\qquad
H+G_j\operatorname{diag}(d)H=\mathbf1.
$$

对二点势，只令 $s_a=s$、$s_b=t$，其余为零。定理10.2给出

$$
G_j(0,a)=G_j(a,a)=A,\qquad
G_j(0,b)=G_j(a,b)=G_j(b,a)=G_j(b,b)=R.
$$

写 $d_s=e^s-1$、$d_t=e^t-1$，上式的 $a,b$ 两行为

$$
\begin{pmatrix}1+Ad_s& Rd_t\\Rd_s&1+Rd_t\end{pmatrix}
\binom{H_a}{H_b}=\binom11.
$$

其行列式为

$$
\Delta=(1+Ad_s)(1+Rd_t)-R^2d_sd_t
=1+Ad_s+Rd_t+R(A-R)d_sd_t.
$$

因 $A\ge R>0$ 且行势非负，$\Delta\ge1$。直接解得

$$
H_a=\Delta^{-1},\qquad
H_b=\frac{1+(A-R)d_s}{\Delta}.
$$

第 $0$ 行与第 $a$ 行的非零势项相同，故

$$
H_0=1-Ad_sH_a-Rd_tH_b=H_a.
$$

这也覆盖 $a=0$，给出二点式。同点时两项势必须先合成 $s+t$；唯一非零势所在行给出 $H_a[1+q_a(e^{s+t}-1)]=1$，而第 $0$ 行仍给出 $H_0=H_a$。吸收点未进入 $n<\tau$ 的求和，其势没有贡献。

再计算时序混合矩与离散对角校正。对任意暂态切点 $a,b$，有

$$
\begin{aligned}
\mathbb E_0V_a&=G_j(0,a)=q_a,\\
\mathbb E_0(V_aV_b)
&=G_j(0,a)G_j(a,b)+G_j(0,b)G_j(b,a)
-{\bf1}_{\{a=b\}}G_j(0,a),\\
\operatorname{Cov}_0(V_a,V_b)
&=q_{\max(a,b)}^2-{\bf1}_{\{a=b\}}q_a.
\end{aligned}
$$

特别地，$\operatorname{Var}_0(V_a)=q_a(q_a-1)$。按定义15.1的零延拓，协方差式也适用于吸收点。

每个暂态起点在至多 $L$ 步内连续向右到达吸收点的概率至少为 $(\theta/\max(r_\alpha,r_\beta))^L>0$。分块使用马尔可夫性质，吸收尾概率受到几何尾控制，故固定有限链的 $\tau$ 具有各阶有限矩。暂态核因此满足

$$
G_j=\sum_{n\ge0}K_j^n,
\qquad
G_j(i,a)=\mathbb E_i\sum_{0\le n<\tau}{\bf1}_{\{X_n=a\}}.
$$

这证明均值式，并使以下二阶求和可积。把 $V_aV_b$ 按两个读取时刻 $n,m$ 排序。在区域 $n\le m$，条件于时刻 $n$ 的未吸收状态，马尔可夫性质给出

$$
\begin{aligned}
&\mathbb E_0\sum_{0\le n\le m<\tau}
{\bf1}_{\{X_n=a\}}{\bf1}_{\{X_m=b\}}\\
&\qquad=\sum_{n\ge0}K_j^n(0,a)
\sum_{k\ge0}K_j^k(a,b)
=G_j(0,a)G_j(a,b).
\end{aligned}
$$

这里 $k=m-n$ 从零开始，确实包含同时刻。交换 $a,b$ 得到区域 $m\le n$ 的第二项；两个区域的交集 $n=m$ 只有在 $a=b$ 时有贡献，其期望为 $G_j(0,a)$，必须减去一次。因而得到所述混合矩，包含初始步并排除吸收步。

当 $a\le b$ 时，定理10.2给出 $G_j(a,b)=G_j(b,a)=q_b$。两个有序区域的期望和为 $q_aq_b+q_b^2$；减去同时刻项，再减去均值乘积 $q_aq_b$，便得到 $q_b^2-{\bf1}_{\{a=b\}}q_a$。交换两点处理 $a>b$；吸收点占用恒为零。

接着作数量缩放。定理10.2给出

$$
h_j=O(L_j^{-1}),\qquad
h_jq_{\iota_j(u)}=\mathcal K_j(0,u)
=\kappa(u)+O(L_j^{-1}),
$$

第二式对 $u\in[0,1]$ 一致成立，并沿用 $q_{L_j}=0$。固定 $u<v<1$ 后，两格点 $a=\iota_j(u)$、$b=\iota_j(v)$ 最终满足 $a<b$。在上述有限二点式中代入 $s h_j,t h_j$，令

$$
\gamma_j(z)=\frac{e^{z h_j}-1}{h_j}\longrightarrow z
\qquad(z\ge0\text{ 固定}).
$$

二点变换的分母精确改写为

$$
\begin{aligned}
1&+\mathcal K_j(0,u)\gamma_j(s)
+\mathcal K_j(0,v)\gamma_j(t)\\
&+\mathcal K_j(0,v)
\bigl(\mathcal K_j(0,u)-\mathcal K_j(0,v)\bigr)
\gamma_j(s)\gamma_j(t).
\end{aligned}
$$

逐项取极限得到所述式，极限分母至少为一。有限 $j$ 时若两个坐标落在同一格点，必须使用上述同点式；固定 $u<v$ 最终分格，所以不影响这个极限。

为直接识别边缘律，上述单点式给出，对 $0<z\le1$，

$$
\mathbb E_0 z^{V_a}
=\frac{z/q_a}{1-(1-q_a^{-1})z}.
$$

模型的参数界保证 $q_a\ge\min(r_\alpha,r_\beta)/\theta\ge2$。展开几何级数并比较概率生成函数的系数，得到

$$
\Pr_0(V_a=m)=q_a^{-1}(1-q_a^{-1})^{m-1}
\qquad(m\ge1).
$$

对固定 $u<1$，$h_jq_{\iota_j(u)}\to\kappa(u)>0$，因而 $q_{\iota_j(u)}\to\infty$。每个 $x\ge0$ 都满足

$$
\Pr_0\bigl(\ell_j(u)>x\bigr)
=\left(1-q_{\iota_j(u)}^{-1}\right)^{\lfloor x/h_j\rfloor}
\longrightarrow e^{-x/\kappa(u)}.
$$

当 $x>0$ 时，取对数并用 $\log(1-y)=-y+O(y^2)$：主项趋于 $-x/\kappa(u)$，余项为 $O(h_j)$；$x=0$ 时两边均为一。这是均值为 $\kappa(u)$ 的指数分布的生存函数。吸收端占用恒为零，故其边缘为零点质量。

最后，上述有限协方差式在任意 $u,v\in[0,1]$ 上给出精确恒等式

$$
\operatorname{Cov}_0\bigl(\ell_j(u),\ell_j(v)\bigr)
=\mathcal K_j(u,v)^2
-h_j{\bf1}_{\{\iota_j(u)=\iota_j(v)\}}\mathcal K_j(0,u).
$$

这是同格指示函数，即使 $u\ne v$ 也可能等于一；不能在缩放前用 $u=v$ 的指示函数替代。由定理10.2，$\mathcal K_j$ 一致有界且与 $\mathcal K$ 的一致误差为 $O(L_j^{-1})$，故

$$
\sup_{u,v}|\mathcal K_j(u,v)^2-\mathcal K(u,v)^2|
\le\|\mathcal K_j-\mathcal K\|_\infty
\bigl(\|\mathcal K_j\|_\infty+\|\mathcal K\|_\infty\bigr)
=O(L_j^{-1}).
$$

同格修正的绝对值至多 $h_j\sup_u\mathcal K_j(0,u)=O(L_j^{-1})$。合并两项，使用 $\mathcal K(u,v)^2=(1-\max(u,v))^2/D^2$，即得包含端点与同格情形的一致估计。

通用的卡茨矩公式与费曼—卡茨框架属于文献已证工具，参见 P. J. Fitzsimmons、J. Pitman，〈马尔可夫过程加性泛函的卡茨矩公式与费曼—卡茨公式〉，《随机过程及其应用》79（1999），117–134，[DOI：10.1016/S0304-4149(98)00081-7](https://doi.org/10.1016/S0304-4149(98)00081-7)。$\square$

**定理 15.3（连续探针的同轨协方差）。** 对任意连续实函数 $f,g\in C([0,1],\mathbb R)$，定义

$$
\mathcal A_j(f)=\epsilon_j\sum_{0\le n<\tau_j}f(X_n/L_j).
$$

则

$$
\operatorname{Cov}_0\bigl(\mathcal A_j(f),\mathcal A_j(g)\bigr)
\longrightarrow
\frac1{D^2}\int_0^1\int_0^1
f(u)g(v)(1-\max(u,v))^2\,du\,dv.
$$

当 $f,g$ 非负时，有限链及极限的上述协方差均非负。取 $f=g=1$，极限为 $1/(6D^2)$。

**证明。** 依切点重新排列同一历史上的占用和，并使用 $h_j=\epsilon_jL_j$，得到精确恒等式

$$
\mathcal A_j(f)
=\epsilon_j\sum_{i=0}^{L_j-1}f(i/L_j)V_i
=\frac1{L_j}\sum_{i=0}^{L_j-1}f(i/L_j)\ell_j(i/L_j).
$$

连续探针有界，固定链的 $\tau_j$ 二阶可积，故协方差可以按有限和展开为

$$
\frac1{L_j^2}\sum_{i,m=0}^{L_j-1}
f(i/L_j)g(m/L_j)
\operatorname{Cov}_0\bigl(\ell_j(i/L_j),\ell_j(m/L_j)\bigr).
$$

定理15.2证明中的有限协方差式给出上述每一项；以该定理的一致极限核替换这些项，总误差至多为 $C\|f\|_\infty\|g\|_\infty/L_j$。替换后的和是连续函数

$$
(u,v)\longmapsto\frac{f(u)g(v)(1-\max(u,v))^2}{D^2}
$$

在闭方形上的左端点黎曼和，因而趋于所述积分。这里只对核替换误差给出 $O(L_j^{-1})$；一般连续 $f,g$ 的黎曼和误差由连续性保证趋零。

由定理15.2证明中的有限协方差式，有限链的协方差矩阵逐项非负：异点项是 $q_{\max(i,m)}^2$，同点项是 $q_i(q_i-1)$，而 $q_i\ge2$。非负探针的有限和遂非负；极限积分的被积函数也非负。常数探针的积分系数可直接算为

$$
\int_0^1\int_0^1(1-\max(u,v))^2\,du\,dv
=2\int_0^1v(1-v)^2\,dv
=2\left(\frac12-\frac23+\frac14\right)=\frac16.
$$

此时 $\mathcal A_j(1)=\epsilon_j\tau_j$，积分值与定理10.3的既有通过时间方差相符；此项是连续探针协方差公式的核对，不另立通过时间结论。$\square$

**命题 15.4（共同随机历史的边界）。** 在逐字源 $W_2=\beta\alpha$ 上取 $r_\alpha=2$、$r_\beta=3$、$\theta=1/4$，并固定同一个 $\delta>0$。暂态核与格林矩阵为

$$
K=\begin{pmatrix}11/12&1/12\\1/12&19/24\end{pmatrix},
\qquad
G=\begin{pmatrix}20&8\\8&8\end{pmatrix}.
$$

一条初态为 $0$ 的链 $X$ 给出

$$
\operatorname{Cov}_0\bigl(V_0(X),V_1(X)\bigr)=64.
$$

取两个独立副本 $X,Y$，它们具有相同逐字源、核、初态与数值时钟，则

$$
\operatorname{Cov}\bigl(V_0(X),V_1(Y)\bigr)=0.
$$

这两个联合模型保留每个对应探针各自的完整轨迹边缘律，却给出不同的联合占用律。同源、同初态与同数值时钟因此不足以指定共同随机历史；此例具体核对第6.4节的边缘轨迹与联合实现边界。

**证明。** 从 $0$ 向右跳的概率为 $\theta/r_\beta=1/12$，所以持留概率为 $11/12$。从 $1$ 向左跳的概率为 $1/12$，向吸收点 $2$ 右跳的概率为 $\theta/r_\alpha=1/8$，所以暂态持留概率为 $19/24$。于是

$$
I-K=\begin{pmatrix}1/12&-1/12\\-1/12&5/24\end{pmatrix},
\qquad
\det(I-K)=\frac1{96},
$$

直接求逆即为所列 $G$。因此 $q_0=20$、$q_1=8$，定理15.2证明中的有限协方差式给出同链协方差 $q_1^2=64$；亦可从混合矩 $20\cdot8+8\cdot8=224$ 减去均值乘积 $160$ 核对。

独立副本的可积占用量相互独立，故协方差为零。具体地，对任何链 $Z$ 令

$$
\mathcal R_a(Z)=\bigl({\bf1}_{\{n<\tau(Z),\ Z_n=a\}}\bigr)_{n\ge0}.
$$

比较联合过程 $(\mathcal R_0(X),\mathcal R_1(X))$ 与 $(\mathcal R_0(X),\mathcal R_1(Y))$：第一坐标的轨迹边缘相同；第二坐标的轨迹边缘也相同，因为 $X,Y$ 的完整链律相同。保持时钟 $n\delta$ 不改变这些边缘等式。然而两种联合过程的占用协方差不同，故联合律不同。这是边界实例，未给源递归增加新的动力学或耦合条件。$\square$

全部结论依赖固定单位速度、左反射右吸收、初态 $0$、给定阻抗与时钟，以及同一条随机历史的模型条件。本节结论不推出完整多点占用律、函数空间占用场收敛、高斯极限、物理热流、物理普适性或第11、14节速度扩展的占用结论。

## 16. 固定有限多点的同轨占用联合律

**定义 16.1（有限探针与缩放变量）。** 继续使用定义 15.1 的固定单位速度、左反射右吸收链、初态 $X_0=0$、同一条随机历史及

$$
L_j=F_{j+1},\qquad N_j=F_{j+3},\qquad
\epsilon_j=\frac{\delta}{N_j^2},\qquad h_j=\epsilon_jL_j,
\qquad D=\frac{\theta\varphi^4}{\delta\overline r}.
$$

给定固定的 $m\ge1$ 个探针 $u_1,\ldots,u_m\in[0,1]$，令

$$
\ell_j(u)=h_jV_{\iota_j(u)},\qquad
\kappa(u)=\frac{1-u}{D}.
$$

若有若干探针坐标相同，先把它们的势合并；若 $u_k=1$，其占用恒为零，可以从联合变换中删去。以下结论先对剩余的互异坐标陈述。记

$$
C_{k\ell}=\kappa(\max(u_k,u_\ell)).
$$

**定理 16.2（固定有限维联合变换与非高斯极限）。** 对固定 $m$、固定互异探针坐标及任意 $z_1,\ldots,z_m\ge0$，有有限链精确式

$$
\mathbb E_0\exp\!\left(-\sum_{k=1}^m z_kV_{a_k}\right)
=\det\!\left(I_m+Q\,\operatorname{diag}(e^{z_k}-1)\right)^{-1},
\qquad
Q_{k\ell}=q_{\max(a_k,a_\ell)},
$$

其中 $a_k$ 按切点从小到大排列，$z_k\ge0$。因此，固定 $m$ 和固定空间坐标后，

$$
\mathbb E_0\exp\!\left(-\sum_{k=1}^m s_k\ell_j(u_k)\right)
\longrightarrow
\det\!\left(I_m+C\,\operatorname{diag}(s_k)\right)^{-1}.
$$

极限向量可在同一概率空间的辅助表示中写成

$$
\Lambda(u)=\frac{B_1(\kappa(u))^2+B_2(\kappa(u))^2}{2},
$$

其中 $B_1,B_2$ 是两条相互独立的标准布朗运动，并且所有探针使用同一对布朗运动。因为

$$
C_{k\ell}=\min\{\kappa(u_k),\kappa(u_\ell)\},
$$

该表示的有限维拉普拉斯变换正是上式。特别地，

$$
\mathbb E\Lambda(u)=\kappa(u),\qquad
\operatorname{Cov}(\Lambda(u),\Lambda(v))=\kappa(\max(u,v))^2,
$$

并且对 $0\le u<v<w<1$，

$$
\operatorname{cum}\bigl(\Lambda(u),\Lambda(v),\Lambda(w)\bigr)
=2\,\kappa(v)\,\kappa(w)^2>0.
$$

所以该固定有限维极限在三个非退化探针上不是高斯向量。

**证明。** 先固定一条有限链。对暂态切点设置非负行势 $z_i$，令

$$
H_i=\mathbb E_i\exp\!\left(-\sum_{0\le n<\tau}z_{X_n}\right),
\qquad H_L=1,
\qquad d_i=e^{z_i}-1.
$$

把当前步的势计入首步分解，得到

$$
\bigl(B+\operatorname{diag}(d)\bigr)H=B\mathbf1,
\qquad
H+G\operatorname{diag}(d)H=\mathbf1,
$$

其中 $B=I-K$、$G=B^{-1}$。在互异探针 $a_1<\cdots<a_m$ 上保留势，令

$$
Q_{k\ell}=G(a_k,a_\ell)=q_{\max(a_k,a_\ell)}.
$$

由于 $G(0,a_k)=G(a_1,a_k)$，第 $0$ 行与第 $a_1$ 行给出相同的非零势组合，故 $H_0=H_{a_1}$。探针行组成

$$
\bigl(I_m+Q\operatorname{diag}(d_k)\bigr)H_*=\mathbf1.
$$

写 $t_k=q_{a_k}$，则 $t_1\ge\cdots\ge t_m$。对任意非空指标集 $I=\{i_1<\cdots<i_r\}$，逐行相减给出主子式

$$
\det Q_I=t_{i_r}\prod_{h=1}^{r-1}(t_{i_h}-t_{i_{h+1}})\ge0.
$$

按列多线性展开，

$$
\det\!\left(I_m+Q\operatorname{diag}(d_k)\right)
=\sum_{I\subseteq\{1,\ldots,m\}}\det(Q_I)\prod_{k\in I}d_k,
$$

其中空集主子式取为 $1$。再以全 $1$ 列替换第一列，并从最后一行向上以原相邻行相减；第一列随即变成 $(1,0,\ldots,0)^\mathsf T$，其余子矩阵为对角元全为 $1$ 的下三角矩阵。因此 Cramer 分子为 $1$，从而

$$
H_0=\det\!\left(I_m+Q\operatorname{diag}(d_k)\right)^{-1}.
$$

这证明了有限链精确式；重复探针必须在这一步先合并势，吸收点的势没有贡献。

令 $a_k=\iota_j(u_k)$，并把 $z_k=s_kh_j$。由定理 10.2，固定 $m$ 时一致地有

$$
h_jq_{\max(a_k,a_\ell)}
\longrightarrow
\kappa(\max(u_k,u_\ell)),
\qquad
\frac{e^{s_kh_j}-1}{h_j}\longrightarrow s_k.
$$

将

$$
Q\operatorname{diag}(e^{s_kh_j}-1)
=\bigl(h_jQ\bigr)\operatorname{diag}\!\left(\frac{e^{s_kh_j}-1}{h_j}\right)
$$

代入有限式，行列式的连续性给出所述极限。非负向量的拉普拉斯变换在所有 $s_k\ge0$ 上收敛，故由拉普拉斯连续性定理得到固定有限维分布收敛。这里 $m$ 必须先固定；结论不涉及 $m=m(j)$ 的增长。

为识别极限表示，令 $T_k=\kappa(u_k)$。对 $r=1,2$，布朗向量

$$
\bigl(B_r(T_k)\bigr)_{k=1}^m
$$

的协方差矩阵为 $(\min(T_k,T_\ell))_{k,\ell}=C$。单条布朗运动的高斯二次型公式给出

$$
\mathbb E\exp\!\left(-\frac12X^\mathsf T S X\right)
=\det(I_m+CS)^{-1/2}.
$$

两条独立布朗运动平方和相乘，得到 $\det(I_m+CS)^{-1}$，因此确实得到 $\Lambda$ 的有限维律。对该变换在零点求导得到均值和协方差。三阶累积量也可由

$$
\log\mathbb E e^{-\sum s_k\Lambda(u_k)}
=-\log\det(I_m+CS)
$$

的三阶项读取：对互异坐标，其系数为

$$
2C_{12}C_{23}C_{31}
=2\kappa(v)\kappa(w)^2
$$

（按 $u<v<w$ 排序）。它严格为正，而任意高斯向量的三阶累积量为零，故排除高斯有限维极限。

本节仍只讨论固定单位速度、给定阻抗与时钟、左反射右吸收、初态 $0$ 及同一随机历史下的占用量。它不宣称 $m$ 随 $j$ 增长时的全场收敛、函数空间中的随机测度弱收敛、跨 $j$ 的路径耦合、速度扩展中的同一律，亦不推出物理热流、温度、量子输运或经验普适性。

## 追加锚（本行以下为增补区）
