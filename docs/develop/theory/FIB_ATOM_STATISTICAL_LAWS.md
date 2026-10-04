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

## 追加锚（本行以下为增补区）

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

## 17. 连续探针占用随机测度的 Fredholm 极限

**定义 17.1（占用随机测度）。** 在定义 15.1 的固定单位速度、左反射右吸收、初态 $0$ 及同一随机历史下，令

$$
\mu_j=\epsilon_j\sum_{0\le n<\tau_j}\delta_{X_n/L_j}
=\epsilon_j\sum_{i=0}^{L_j-1}V_i\,\delta_{i/L_j}.
$$

对连续函数 $f$，记 $\langle f,\mu_j\rangle=\int f\,d\mu_j$。定义连续核

$$
C(u,v)=\frac{1-\max(u,v)}{D}
=\kappa(\max(u,v)),
\qquad
\kappa(u)=\frac{1-u}{D},
$$

并令 $\mathsf C$ 为 $L^2([0,1])$ 上的积分算子

$$
(\mathsf C f)(u)=\int_0^1 C(u,v)f(v)\,dv.
$$

**定理 17.2（连续探针的随机测度弱收敛）。** 对每个非负连续函数 $f\in C([0,1])$，

$$
\mathbb E_0\exp\bigl(-\langle f,\mu_j\rangle\bigr)
\longrightarrow
\det\nolimits_F\!\left(I+\mathsf C M_f\right)^{-1},
$$

其中 $M_f$ 是乘法算子，$\det_F$ 是 Fredholm 行列式。若

$$
\Lambda(u)=\frac{B_1(\kappa(u))^2+B_2(\kappa(u))^2}{2},
\qquad
\mu(du)=\Lambda(u)\,du,
$$

且 $B_1,B_2$ 是同一对独立标准布朗运动，则

$$
\det\nolimits_F\!\left(I+\mathsf C M_f\right)^{-1}
=
\mathbb E\exp\left(-\int_0^1 f(u)\Lambda(u)\,du\right).
$$

因此

$$
\mu_j\Longrightarrow\mu
$$

于 $[0,1]$ 上有限非负 Borel 测度的弱拓扑。特别地，对任意有限个连续探针 $f_1,\ldots,f_r$，向量

$$
\bigl(\langle f_1,\mu_j\rangle,\ldots,\langle f_r,\mu_j\rangle\bigr)
$$

收敛到相应的 $\mu$ 积分向量。极限测度几乎处处具有连续密度 $\Lambda$；这仍不等同于路径过程 $X_n/L_j$ 的函数空间收敛。

**证明。** 先把全部暂态切点都作为势的支持。对 $f_i=f(i/L_j)$，令

$$
d_{j,i}=e^{f_i\epsilon_j}-1.
$$

第 16 节的首步方程与嵌套 Green 矩阵的 Cramer 计算，在支持取为全部切点时给出有限维精确式

$$
\mathbb E_0e^{-\langle f,\mu_j\rangle}
=\det\nolimits_{L_j}\!\left(I+G_j\operatorname{diag}(d_{j,i})\right)^{-1}.
$$

这里零势坐标可以先删去，再由连续性恢复；全部坐标的式子是同一行列式恒等式的全支持版本。

写

$$
g_{j,i}=\frac{e^{f_i\epsilon_j}-1}{\epsilon_j},
\qquad
\mathcal K_j(i/L_j,k/L_j)=h_jG_j(i,k).
$$

由 $h_j=\epsilon_jL_j$，上式的有限行列式可写成

$$
\det\nolimits_{L_j}\!\left(I+\mathsf T_jM_{g_j}\right)^{-1},
\qquad
(\mathsf T_j\psi)(i/L_j)
=\frac1{L_j}\sum_{k=0}^{L_j-1}
\mathcal K_j(i/L_j,k/L_j)\psi(k/L_j).
$$

由于 $f$ 连续且 $\epsilon_j\to0$，有 $g_j\to f$ 一致成立。下文把 $g_j$ 延拓为阶梯函数：在 $[i/L_j,(i+1)/L_j)$ 上取值 $g_{j,i}$，并在 $u=1$ 取右端极限。定理 10.2 给出

$$
\sup_{u,v\in[0,1]}
\left|\mathcal K_j(u,v)-C(u,v)\right|\longrightarrow0.
$$

将 $\mathsf T_j$ 嵌入 $L^2([0,1])$ 的分片常数子空间，并记其核为相应的阶梯核。Green 矩阵 $G_j(i,k)=q_{\max(i,k)}$ 对称正定，所以正对称化算子

$$
\mathsf A_j=M_{\sqrt{g_j}}\mathsf T_jM_{\sqrt{g_j}},
\qquad
\mathsf A=M_{\sqrt f}\mathsf C M_{\sqrt f}
$$

都是正自伴算子；$\mathsf A$ 为迹类。第 13.3 节给出的特征值
$\rho_m=[D(m+1/2)^2\pi^2]^{-1}$ 也直接说明了 $\mathsf C$ 的迹类性质。均匀核收敛与 $g_j\to f$ 一致收敛给出 $\|\mathsf A_j-\mathsf A\|_{\mathrm{op}}\to0$。同时，对角线的黎曼和给出

$$
\operatorname{tr}\mathsf A_j
=\frac1{L_j}\sum_{i=0}^{L_j-1}
g_{j,i}\mathcal K_j(i/L_j,i/L_j)
\longrightarrow
\int_0^1 f(u)C(u,u)\,du
=\operatorname{tr}\mathsf A.
$$

对正自伴算子，算子范数收敛与迹收敛结合有限秩谱截断给出迹范数收敛，因此

$$
\|\mathsf A_j-\mathsf A\|_1\longrightarrow0.
$$

有限维行列式的循环恒等式给出

$$
\det\nolimits_{L_j}(I+\mathsf T_jM_{g_j})
=\det\nolimits_F(I+\mathsf A_j),
$$

Fredholm 行列式对迹范数连续，因而

$$
\det\nolimits_{L_j}(I+\mathsf T_jM_{g_j})
\longrightarrow
\det\nolimits_F(I+\mathsf A)
=\det\nolimits_F(I+\mathsf C M_f).
$$

再用两条独立布朗运动的高斯二次型公式。对 $T_k=\kappa(u_k)$ 及 $r=1,2$，向量 $(B_r(T_k))_k$ 的协方差核为 $C$，故对非负 $f$

$$
\mathbb E\exp\left(
-\frac12\int f(u)B_r(\kappa(u))^2\,du
\right)
=\det\nolimits_F(I+\mathsf A)^{-1/2}.
$$

两条独立布朗运动相乘，得到 $\mu$ 的 Laplace 泛函。最后，

$$
\mathbb E_0\mu_j([0,1])
=\frac1{L_j}\sum_{i=0}^{L_j-1}
\mathcal K_j(0,i/L_j)
\longrightarrow
\int_0^1 C(0,v)\,dv
=\frac1{2D},
$$

所以总质量族紧。有限底空间上的随机有限测度由全部非负连续函数的 Laplace 泛函唯一确定，故得到所述弱收敛。$\square$

**推论 17.3（连续探针的均值、协方差与通过时间核对）。** 对连续 $f,g$，

$$
\mathbb E\langle f,\mu\rangle
=\int_0^1 f(u)\kappa(u)\,du,
$$

$$
\operatorname{Cov}\bigl(\langle f,\mu\rangle,\langle g,\mu\rangle\bigr)
=\int_0^1\int_0^1
f(u)g(v)C(u,v)^2\,du\,dv.
$$

取 $f=g=1$，得到 $\operatorname{Var}(\mu([0,1]))=1/(6D^2)$，与定理 15.3 及定理 10.3 的通过时间方差一致。 对常数探针 $f\equiv s$，Fredholm 行列式满足 $\det_F(I+s\mathsf C)=\cosh\sqrt{s/D}$，其逆为 $\operatorname{sech}\sqrt{s/D}$，恢复定理 10.3 的通过时间变换。

本节的随机测度收敛只覆盖连续测试函数的占用积分。它不推出 $\ell_j(\cdot)$ 在 $C([0,1])$ 中一致收敛、不推出 $m=m(j)$ 的逐点行列式律、不指定跨 $j$ 的样本耦合，也不延伸到第 11、14 节的速度权重扩展或物理热流、温度与经验普适性。

## 18. 反向空间的平方贝塞尔统计场

**定义 18.1（反向坐标与径向场）。** 对第 16、17 节的极限密度作反向坐标变换

$$
Y(s)=\Lambda(1-s),\qquad 0\le s\le1.
$$

令

$$
R_t=\frac{B_1(t)^2+B_2(t)^2}{2}.
$$

则 $Y(s)=R_{s/D}$，并且 $Y(0)=0$。这里的 $s$ 只是把吸收端到反射端的空间坐标反向排列，不引入新的动力学核。

**定理 18.2（平方贝塞尔/移民扩散律）。** 在同一对布朗运动耦合下，存在一条一维布朗运动 $W$ 使得

$$
dY(s)=\frac1D\,ds+\sqrt{\frac{2Y(s)}D}\,dW(s),
\qquad Y(0)=0.
$$

其生成元为

$$
\mathcal A\phi(y)=\frac1D\bigl(\phi'(y)+y\phi''(y)\bigr).
$$

对 $0\le s\le1$、$0\le h\le1-s$ 及 $z\ge0$，条件拉普拉斯变换为

$$
\mathbb E\!\left[e^{-zY(s+h)}\mid Y(s)=y\right]
=
\left(1+\frac{zh}{D}\right)^{-1}
\exp\!\left(
-\frac{yz}{1+zh/D}
\right).
$$

因此

$$
\mathbb E[Y(s+h)\mid Y(s)=y]=y+\frac hD,
$$

$$
\operatorname{Var}(Y(s+h)\mid Y(s)=y)
=\frac{2yh}{D}+\frac{h^2}{D^2}.
$$

这是归一化的维数为 $2$ 平方贝塞尔扩散在时间 $s/D$ 下的径向能量律，也等价于带常数移民项的临界 Feller 扩散。它是极限占用密度的 Markov 表示，不是递归本身选择的物理温度或热流方程。

**证明。** 对 $R_t$ 直接使用 Itô 公式：

$$
dR_t=B_1(t)\,dB_1(t)+B_2(t)\,dB_2(t)+dt.
$$

其局部鞅的二次变差为 $2R_t\,dt$，所以可重写为

$$
dR_t=dt+\sqrt{2R_t}\,dW_t.
$$

将 $t=s/D$ 代入并作布朗时间变换，得到所述随机微分方程与生成元。对固定初值 $R_0=y$，函数

$$
F(t,y)=\frac1{1+zt}\exp\!\left(-\frac{yz}{1+zt}\right)
$$

满足平方贝塞尔生成元的后向方程及初值 $F(0,y)=e^{-zy}$，由唯一性得到条件拉普拉斯变换；代入 $t=h/D$ 即得显示式。对 $z$ 在零点求一、二阶导数得到条件均值与方差。$\square$

**定理 18.3（全阶累积量与路径非单调性）。** 对互异探针 $0\le u_1<\cdots<u_r<1$，令

$$
C_{ab}=\kappa(\max(u_a,u_b)).
$$

则对 $r\ge2$，

$$
\operatorname{cum}\bigl(\Lambda(u_1),\ldots,\Lambda(u_r)\bigr)
=
\frac1r\sum_{\sigma\in S_r}
\prod_{q=1}^r C_{\sigma(q),\sigma(q+1)},
\qquad \sigma(r+1)=\sigma(1).
$$

等价地，求和可按循环旋转类进行，每个无向重复的有向循环分别计一次。所有因子均为正，所以每个 $r\ge2$ 的累积量严格为正；$r=2$ 给出 $C_{12}^2$，$r=3$ 给出第 16 节的 $2\kappa(u_2)\kappa(u_3)^2$。

虽然 $\mathbb E Y(s)=s/D$ 随 $s$ 线性增加，但 $Y$ 的样本路径不具有必然的逐样本单调性：对任意 $y>0$ 与允许的 $h>0$，二维布朗增量把当前半径移入更小半径开集的概率为正，故 $\Pr_y(Y(s+h)<y)>0$。因此不能把平均密度梯度解释为逐样本的单向输运或热流方向。

**证明。** 在 $t_1,\ldots,t_r$ 充分接近零、使谱半径 $\rho(C\operatorname{diag}(t_a))<1$ 的邻域内，展开第 16 节的联合变换：

$$
\log\mathbb E
\exp\!\left(\sum_{a=1}^r t_a\Lambda(u_a)\right)
=
-\log\det\!\left(I-C\operatorname{diag}(t_a)\right)
=
\sum_{n\ge1}\frac1n
\operatorname{tr}\!\left((C\operatorname{diag}(t_a))^n\right).
$$

取互异变量的 $r$ 阶混合导数时，只有 $n=r$ 项保留；按循环旋转合并 $r$ 次重复，得到所列公式。正性来自 $u_r<1$ 时所有 $C_{ab}>0$。平方贝塞尔扩散的非单调性也可由其非退化扩散系数看出：从任意 $y>0$ 出发，在足够小的向内开集中有正概率到达更小的值；条件方差公式给出同一结论。$\square$

本节的平方贝塞尔与 Feller 名称只描述极限随机场的统计等价结构。它依赖固定单位速度、给定阻抗与时钟、左反射右吸收、初态 $0$ 及同一随机历史；不延伸为 FIB 递归内生的物理定律，也不覆盖第 11、14 节速度权重扩展、路径过程收敛或经验普适性。

## 19. 连续速度权重下的加权径向场

**定义 19.1（连续正速度密度的扩展链）。** 取连续函数 $v\in C([0,1])$，满足

$$
0<v_*:=\min_{[0,1]}v\le \max_{[0,1]}v=:v^*<\infty,
\qquad
2\theta\le v_*\min(r_\alpha,r_\beta).
$$

在第 15 节的同一逐字源、边界、时钟与初态下，对内部暂态切点 $i$，把两条跨边概率改为

$$
\frac{\theta}{v(i/L_j)r_{(W_j)_{i-1}}},
\qquad
\frac{\theta}{v(i/L_j)r_{(W_j)_i}},
$$

并以剩余概率持留；$0$ 处仍按反射边界只保留右跳。令 $V_j^{(v)}$ 为相应的局部速度权重对角矩阵，令 $V_i^{(v)}$ 为扩展链在切点 $i$ 的占用量。于是

$$
B_j^{(v)}=(V_j^{(v)})^{-1}B_j,
\qquad
G_j^{(v)}=G_jV_j^{(v)}.
$$

**定理 19.2（加权有限维律与加权随机测度极限）。** 设互异探针 $0\le u_1<\cdots<u_m<1$，并令

$$
\ell_j^{(v)}(u)=h_jV_{\iota_j(u)}^{(v)}.
$$

则

$$
\mathbb E_0\exp\!\left(-\sum_{k=1}^m s_k\ell_j^{(v)}(u_k)\right)
\longrightarrow
\det\!\left(I_m+C\,\operatorname{diag}(v(u_k)s_k)\right)^{-1}.
$$

若

$$
\mu_j^{(v)}
=\epsilon_j\sum_{i=0}^{L_j-1}V_i^{(v)}\delta_{i/L_j},
$$

则在有限非负测度弱拓扑下

$$
\mu_j^{(v)}
\Longrightarrow
\mu^{(v)}(du):=v(u)\Lambda(u)\,du,
$$

其中 $\Lambda$ 是第 16—18 节的同一辅助平方贝塞尔统计场的密度表示。这里“同一”只指分布表示；没有给出不同速度链在原概率空间上的逐样本耦合。

特别地，

$$
\mathbb E X_v(u)=v(u)\kappa(u),
\qquad
\operatorname{Cov}(X_v(u),X_v(w))
=v(u)v(w)C(u,w)^2,
$$

其中 $X_v(u)=v(u)\Lambda(u)$。对 $r\ge2$，

$$
\operatorname{cum}\bigl(X_v(u_1),\ldots,X_v(u_r)\bigr)
=
\left(\prod_{a=1}^rv(u_a)\right)
\operatorname{cum}\bigl(\Lambda(u_1),\ldots,\Lambda(u_r)\bigr).
$$

**证明。** 固定有限链并取互异暂态切点 $a_1<\cdots<a_m$。第 16 节的首步方程适用于 $G_j^{(v)}$，而

$$
G_j^{(v)}(a_k,a_\ell)
=q_{\max(a_k,a_\ell)}\,v(a_\ell/L_j).
$$

因此探针矩阵是

$$
Q^{(v)}=Q\,\operatorname{diag}\bigl(v(a_\ell/L_j)\bigr).
$$

其任意主子式等于 $\det(Q_I)\prod_{\ell\in I}v(a_\ell/L_j)$，仍非负；第 16 节的第一列 Cramer 分子仍为 $1$，所以有限链变换为

$$
\det\!\left(I_m+
Q\,\operatorname{diag}\bigl(v(a_k/L_j)(e^{z_k}-1)\bigr)\right)^{-1}.
$$

令 $z_k=s_kh_j$，应用第 10.2 节的核极限即得固定有限维式。

对全体切点取势时，同一行列式写成第 17 节的阶梯算子，并把 $g_j$ 换为 $v_jg_j$。正对称化算子变为

$$
\mathsf A_j^{(v)}
=M_{\sqrt{v_jg_j}}\mathsf T_jM_{\sqrt{v_jg_j}},
$$

其极限为 $M_{\sqrt{vf}}\mathsf C M_{\sqrt{vf}}$。连续正性、对角线迹的黎曼和与第 17 节相同的迹范数论证给出 Fredholm 行列式收敛，因此得到 $\mu_j^{(v)}\Rightarrow v\Lambda\,du$。均值、协方差与全阶累积量由逐点乘法直接得到。$\square$

**推论 19.3（加权反向场的时间非齐次 Markov 表示）。** 令

$$
Y_v(s)=X_v(1-s)=w(s)Y(s),\qquad w(s)=v(1-s).
$$

对任意连续正函数 $v$，确定性的逐时缩放 $y\mapsto w(s)y$ 都可逆，所以 $Y_v$ 仍具有连续路径的时间非齐次 Markov 表示。具体地，对 $0\le s<s+h\le1$、$z\ge0$，其转移核满足

$$
\mathbb E\!\left[e^{-zY_v(s+h)}\mid Y_v(s)=y\right]
=
\left(1+\frac{z w(s+h)h}{D}\right)^{-1}
\exp\!\left(
-\frac{y\,z\,w(s+h)/w(s)}{1+z w(s+h)h/D}
\right).
$$

这直接由第 18.2 节的条件变换与 $Y(s)=Y_v(s)/w(s)$ 得到，不要求 $v$ 可微。

若进一步有 $v\in C^1([0,1])$，才可对乘积使用 Itô 公式，将同一辅助表示写成含 $w'/w$ 的 SDE：

$$
dY_v(s)
=
\left(\frac{w'(s)}{w(s)}Y_v(s)+\frac{w(s)}D\right)ds
+\sqrt{\frac{2w(s)Y_v(s)}D}\,dW(s),
\qquad Y_v(0)=0.
$$

当 $v\equiv c>0$ 时，该场具有同类齐次平方贝塞尔律，但有效参数为

$$
D'=\frac Dc,\qquad
dY_c(s)=\frac1{D'}\,ds+\sqrt{\frac{2Y_c(s)}{D'}}\,dW(s).
$$

只有 $c=1$ 时，这个参数及其转移律才逐字等于第 18 节。一般连续正 $v$ 的 Markov 表示仍成立；$C^1$ 假设只用于上述导数形式的随机微分方程。

**推论 19.4（速度权重的可识别性边界）。** 将初态 $0$ 下极限占用密度的单点均值记为

$$
m_{\mathrm{occ}}(u)=\mathbb E X_v(u)
=v(u)\kappa(u)=\frac{v(u)(1-u)}D.
$$

若 $D$ 与全空间的 $m_{\mathrm{occ}}$ 已知，则对 $u<1$

$$
v(u)=\frac{m_{\mathrm{occ}}(u)}{\kappa(u)},
$$

并由连续性确定 $v(1)$。所有起点的极限平均通过时间另记为

$$
T_v(x)=\int_0^1 C(x,u)v(u)\,du
=\frac1D\left[
(1-x)\int_0^xv(u)\,du+
\int_x^1(1-u)v(u)\,du
\right].
$$

这里 $x$ 是初始切点的归一化位置；$T_v$ 与占用均值函数 $m_{\mathrm{occ}}$ 是不同的读数。由连续 $v$ 对上式求导，

$$
-DT_v''(x)=v(x),\qquad T_v'(0)=0,\qquad T_v(1)=0.
$$

因此已知 $D$ 及所有起点的平均通过时间函数 $T_v$ 也能恢复速度密度。单一起点均值、总速度质量或有限个测试函数均值只给有限个线性约束，不能识别一般连续 $v$；第 14.3 节的平滑速度例子已经给出同均值而不同二阶律的具体边界。

本节是第 11、14 节外加速度模型与第 17、18 节统计场的接口，不是 FIB 递归内生的物理定律；不推出速度扩展中的路径耦合、函数空间一致收敛或经验热流解释。

## 20. 等阻抗有限链的精确谱尾与 Fibonacci 扩散尾律

**定义 20.1（等阻抗谱模型）。** 取

$$
r_\alpha=r_\beta=r>0,\qquad
p=\frac{\theta}{r}\in(0,1/2],
$$

并沿用第 10 节的长度与时钟

$$
L_j=F_{j+1},\qquad N_j=F_{j+3},\qquad
\epsilon_j=\frac{\delta}{N_j^2},\qquad
D=\frac{p\varphi^4}{\delta}.
$$

暂态切点为 $0,\ldots,L_j-1$，$0$ 处以概率 $p$ 向右跳并以概率 $1-p$ 持留；内部切点左右跳概率均为 $p$，剩余概率持留；$L_j$ 吸收。允许初始切点律 $\nu_j$，记 $\nu_{j,i}$ 为其暂态切点 $i<L_j$ 的质量；其归一化坐标律 $(i\mapsto i/L_j)_\#\nu_j$ 满足

$$
(i\mapsto i/L_j)_\#\nu_j\Longrightarrow\nu
\quad\text{于 }[0,1].
$$

**定理 20.2（精确余弦谱与扩散尾律）。** 对 $L=L_j$，令

$$
q_{L,m}=\frac{(2m+1)\pi}{2L+1},
\qquad
\lambda_{L,m}=1-2p+2p\cos q_{L,m},
\qquad 0\le m<L.
$$

则暂态核的本征函数与范数为

$$
\phi_{L,m}(i)=\cos\!\left((i+1/2)q_{L,m}\right),
\qquad
\|\phi_{L,m}\|^2=\frac{2L+1}{4}.
$$

对整数 $n\ge0$，有限链吸收尾满足精确谱式

$$
\Pr_{\nu_j}(\tau_j>n)
=\sum_{m=0}^{L-1}a_{L,m}(\nu_j)\lambda_{L,m}^{\,n},
$$

其中

$$
a_{L,m}(\nu_j)
=
\frac{2(-1)^m}{2L+1}
\cot\!\left(\frac{q_{L,m}}2\right)
\sum_{i=0}^{L-1}\nu_{j,i}
\cos\!\left((i+1/2)q_{L,m}\right).
$$

若 $t>0$，则

$$
\Pr_{\nu_j}\!\left(\epsilon_j\tau_j>t\right)
\longrightarrow
S_\nu(t):=
\sum_{m=0}^{\infty}
\frac{4(-1)^m}{(2m+1)\pi}
\left[
\int_{[0,1]}
\cos\!\left(\frac{(2m+1)\pi x}{2}\right)d\nu(x)
\right]
e^{-D\pi^2(2m+1)^2t/4}.
$$

吸收端的质量自动不贡献尾部，因为各余弦系数在 $x=1$ 为零。若

$$
b_0(\nu)=\frac4\pi\int_{[0,1]}\cos(\pi x/2)\,d\nu(x)>0,
$$

则长时间尾满足

$$
S_\nu(t)\sim b_0(\nu)e^{-D\pi^2t/4}
\qquad(t\to\infty).
$$

**证明。** 暂态核是带反射半格点边界与吸收端点的实对称 Jacobi 矩阵。令 $\phi(i)=\cos((i+1/2)q)$，内部递推给出 $\lambda=1-2p+2p\cos q$；反射边界在 $0$ 自动满足，吸收边界要求 $\phi(L)=0$，即 $q=(2m+1)\pi/(2L+1)$。离散余弦正交关系给出范数 $(2L+1)/4$，再将常数函数投影到这些本征函数上即得系数 $a_{L,m}$ 与精确尾式。

由 Fibonacci 比例

$$
\frac{N_j}{L_j}\longrightarrow\varphi^2,
\qquad
\epsilon_jL_j^2\longrightarrow\frac{\delta}{\varphi^4},
$$

对固定 $m$ 有

$$
1-\lambda_{L_j,m}
=\frac{p\pi^2(2m+1)^2}{(2L_j+1)^2}
+O_m(L_j^{-4}),
$$

从而

$$
\lambda_{L_j,m}^{\lfloor t/\epsilon_j\rfloor}
\longrightarrow
e^{-D\pi^2(2m+1)^2t/4}.
$$

同样，谱投影系数趋于

$$
\frac{4(-1)^m}{(2m+1)\pi}
\int_{[0,1]}\cos\!\left(\frac{(2m+1)\pi x}{2}\right)d\nu(x).
$$

半格点分母 $(2L_j+1)^2$ 必须保留；将其换成 $4L_j^2$ 会产生 $L_j^{-3}$ 阶修正，不能同时声称余项仍为 $O_m(L_j^{-4})$。

先固定低频截断 $M$，再令 $j\to\infty$。对 $m\le M$ 使用上述逐模态极限。对固定 $t>0$ 及充分大的 $j$，系数式与 $1-\lambda_{L,m}=4p\sin^2(q_{L,m}/2)$ 给出

$$
|a_{L,m}(\nu_j)|\le\frac{C}{m+1},\qquad
\lambda_{L,m}^{\lfloor t/\epsilon_j\rfloor}
\le e^{-c_t(m+1)^2}\quad(\lambda_{L,m}\ge0),
$$

其中 $C,c_t>0$ 不随 $j,m,\nu_j$ 变化。因此非负谱中 $m>M$ 的尾项由可求和级数控制，并随 $M\to\infty$ 消失。当 $p<1/2$ 时，负本征值的绝对值不超过 $4p-1<1$（$p\le1/4$ 时没有负本征值）；其系数绝对值之和至多为 $O(\log L)$，所以负谱贡献在扩散时标上也趋零。

当 $p=1/2$ 时，$\lambda_{L,m}=\cos q_{L,m}$。对负谱即 $q_{L,m}>\pi/2$，反向编号为

$$
m=L-1-k,\qquad
q_{L,L-1-k}=\pi-\frac{2(k+1)\pi}{2L+1},\qquad k\ge0.
$$

由 $\cot(q/2)=\tan((\pi-q)/2)$ 及起始律总质量不超过一，统一有

$$
|a_{L,L-1-k}(\nu_j)|\le\frac{C(k+1)}{L^2}.
$$

所以 $k\ge1$ 时系数为 $O(k/L^2)$；最末模态 $k=0$ 须单列为 $O(L^{-2})$，不能把 $O(k/L^2)$ 写到 $k=0$。若初态为 $0$，额外的余弦因子还给出 $O((k+1)^2/L^3)$。对固定 $t>0$ 及充分大的 $j$，在上述整个负谱范围内，

$$
|\lambda_{L,L-1-k}|^{\lfloor t/\epsilon_j\rfloor}
\le \exp\bigl(-c_t(k+1)^2\bigr)
\le \exp(-c_t k^2).
$$

这是因为 $|\lambda|=\cos(2(k+1)\pi/(2L+1))$，且 $\epsilon_jL_j^2$ 趋于严格正的常数。于是负谱的标量贡献至多为

$$
\frac{C}{L^2}\sum_{k\ge0}(k+1)e^{-c_t(k+1)^2}
\longrightarrow0.
$$

该可求和控制只用于生存函数的投影，不把靠近 $-1$ 的高频模态升级为全空间算子范数收敛。合并正、负谱后，取 $M\to\infty$ 即得所列级数。首模态与其余模态的指数率严格分离，给出长时间渐近式。$\square$

本节的谱尾律需要固定 $p>0$、$\delta>0$、等阻抗、左反射右吸收和初始律收敛；$p=0$ 时不发生该吸收扩散缩放，$p>1/2$ 时转移核不满足本定义。谱式中的高频系数可带符号，不能把每一项解释为独立概率或几何变量和。递归只提供 $W_j$、$L_j$ 与 $N_j/L_j$ 的比例；阻抗、跳率、时钟、边界和初始律仍是外加动力学。该结论不推出物理热流、量子输运、路径空间收敛或一般速度权重下的同一谱律。

## 21. 不等阻抗的固定低频谱与二字母定量同质化

**定义 21.1（逐字阻抗与低频编号）。** 沿用定义 10.1 的逐字源 $W_j$、固定单位速度、左反射右吸收边界及数量缩放时钟。固定

$$
r_\alpha,r_\beta>0,\qquad
0<\theta\le\frac{\min(r_\alpha,r_\beta)}2,\qquad
\delta>0,
$$

并令

$$
a=\varphi^{-2},\qquad
\overline r=a r_\alpha+(1-a)r_\beta,\qquad
D=\frac{\theta\varphi^4}{\delta\overline r},
$$

$$
L_j=F_{j+1},\qquad N_j=F_{j+3},\qquad
\epsilon_j=\frac{\delta}{N_j^2},\qquad
\Delta_r=|r_\alpha-r_\beta|.
$$

记暂态核为 $K_j$，$B_j=I-K_j$，$G_j=B_j^{-1}$。实对称三对角核 $K_j$ 的本征值按递减次序编号为

$$
\lambda_{j,0}>\lambda_{j,1}>\cdots>\lambda_{j,L_j-1},
$$

因此 $m=0$ 表示 $B_j$ 的最低频模态。将相应本征向量 $f_{j,m}$ 归一化为

$$
\frac1{L_j}\sum_{i=0}^{L_j-1}f_{j,m}(i)^2=1,
\qquad f_{j,m}(0)>0,
$$

并嵌入分片常数函数：在 $[i/L_j,(i+1)/L_j)$ 上取值 $f_{j,m}(i)$，在吸收端 $u=1$ 取零。以下低频极限一律先固定整数 $m\ge0$，再令 $j\to\infty$；本征对只在充分大且 $L_j>m$ 的 $j$ 上使用。

**定理 21.2（二字母阻抗的区间差异与同长度比较）。** 对每个 $0\le b\le c\le L_j$，

$$
\left|\sum_{i=b}^{c-1}r_{(W_j)_i}
-\overline r(c-b)\right|\le\Delta_r.
$$

归一化 Green 核

$$
\mathcal K_j(u,v)
=\epsilon_jL_jG_j(\iota_j(u),\iota_j(v))
$$

按定义 10.1 在吸收端取零。若

$$
C(u,v)=\frac{1-\max(u,v)}D,\qquad
c_j=\frac{\epsilon_j\overline rL_j^2}{\theta},
$$

则

$$
\|\mathcal K_j-C\|_\infty
\le |c_j-D^{-1}|
+\frac{\epsilon_jL_j}{\theta}(\overline r+\Delta_r)
=O(L_j^{-1}).
$$

这里的误差常数只依赖固定的阻抗、跳尺度与时钟。为区分极限平均与有限词的实际平均，再令

$$
\widehat r_j=\frac1{L_j}\sum_{i=0}^{L_j-1}r_{(W_j)_i},
\qquad
|\widehat r_j-\overline r|\le\frac{\Delta_r}{L_j}.
$$

对任意正数 $r_0$，记同长度 $L_j$、同 $\theta,\epsilon_j$ 的常阻抗 Green 核为

$$
\mathcal K_j^{[r_0]}(u,v)
=\frac{\epsilon_jL_j r_0}{\theta}
\bigl(L_j-\max(\iota_j(u),\iota_j(v))\bigr),
$$

并在任一参数等于 $1$ 时取零。则有两种同长度比较界：

$$
\|\mathcal K_j-\mathcal K_j^{[\overline r]}\|_\infty
\le\frac{\epsilon_jL_j}{\theta}\Delta_r,
\qquad
\|\mathcal K_j-\mathcal K_j^{[\widehat r_j]}\|_\infty
\le\frac{2\epsilon_jL_j}{\theta}\Delta_r.
$$

后一比较保持有限词的总阻抗不变；两者均为 $O(L_j^{-1})$。

**证明。** 第 3.2、10.2 节的机械词表示使任一区间的 $\alpha$ 数与 $a(c-b)$ 的差小于一。将总阻抗写为

$$
r_\beta(c-b)+(r_\alpha-r_\beta)A_{b,c-b}
$$

即得区间差异界。第 10.2 节的精确 Green 逆为

$$
G_j(i,k)=\frac1\theta
\sum_{\ell=\max(i,k)}^{L_j-1}r_{(W_j)_\ell}.
$$

将尾区间的总阻抗替换为 $\overline r$ 乘以尾长度，误差不超过 $\Delta_r$；再将格点坐标换为连续坐标，误差不超过 $\overline r$ 乘以一个格点长度。结合

$$
c_j=D^{-1}+O(L_j^{-2}),\qquad
\epsilon_jL_j=O(L_j^{-1}),
$$

即得一致核估计与第一种同长度比较。全词区间的同一界给出 $|\widehat r_j-\overline r|\le\Delta_r/L_j$。任一尾区间长度不超过 $L_j$，所以将 $\overline r$ 再换成 $\widehat r_j$ 额外损失不超过 $\Delta_r$，得到第二种比较。$\square$

**定理 21.3（不等阻抗的固定低频本征对）。** 对每个先固定的整数 $m\ge0$，在充分大且 $L_j>m$ 时，

$$
\rho_{j,m}:=\frac{\epsilon_j}{1-\lambda_{j,m}}
\longrightarrow
\rho_m:=\frac{4}{D\pi^2(2m+1)^2}.
$$

上述分片常数嵌入的本征函数满足

$$
f_{j,m}(u)\longrightarrow
\psi_m(u):=\sqrt2\cos\!\left(\frac{(2m+1)\pi u}{2}\right)
$$

于 $[0,1]$ 的一致范数，因而也于 $L^2([0,1])$。此外，令同长度实际平均阻抗链的本征值为

$$
\widehat\lambda_{j,m}
=1-2\widehat p_j+
2\widehat p_j\cos\!\left(\frac{(2m+1)\pi}{2L_j+1}\right),
\qquad
\widehat p_j=\frac{\theta}{\widehat r_j},
$$

则对这些固定 $m$ 的本征值有定量比较

$$
\left|
\frac{\epsilon_j}{1-\lambda_{j,m}}
-\frac{\epsilon_j}{1-\widehat\lambda_{j,m}}
\right|
\le\frac{2\epsilon_jL_j}{\theta}\Delta_r,
\qquad
\rho_{j,m}=\rho_m+O_m(L_j^{-1}).
$$

**证明。** 在 $L^2([0,1])$ 上令 $\mathcal T_j$ 为 $\mathcal K_j$ 的积分算子，$\mathsf C$ 为 $C$ 的积分算子。两者正自伴；$\mathcal T_j$ 在分片常数子空间上恰为 $\epsilon_jG_j$，在其正交补上为零。因此它的非零本征值是按递减次序排列的 $\rho_{j,m}$。定理 21.2 的一致核误差给出

$$
\|\mathcal T_j-\mathsf C\|_{2\to2}
\le\|\mathcal K_j-C\|_\infty=O(L_j^{-1}).
$$

对 $y=\mathsf C f$，第 10.2 节的边值关系为

$$
-Dy''=f,\qquad y'(0)=0,\qquad y(1)=0.
$$

所以 $\mathsf C$ 的非零本征对正是 $(\rho_m,\psi_m)$：诺伊曼—狄利克雷条件给出半整数频率，每个本征值严格正且单重。正紧自伴算子的极小极大原理与算子范数收敛于是给出每个固定 $m$ 的本征值收敛；孤立单重本征值的谱投影收敛给出相应本征函数在 $L^2$ 中的收敛，先允许选择符号。

为把 $L^2$ 收敛提升到一致收敛，使用本征方程

$$
f_{j,m}=\rho_{j,m}^{-1}\mathcal T_j f_{j,m},
\qquad
\psi_m=\rho_m^{-1}\mathsf C\psi_m.
$$

一致核误差使 $\mathcal T_j-\mathsf C$ 从 $L^2$ 到有界函数的一致范数趋零，而连续有界核 $C$ 使 $\mathsf C$ 从 $L^2$ 到 $C([0,1])$ 连续。由于固定 $m$ 的 $\rho_m>0$，本征方程给出一致收敛。暂态三对角矩阵的相邻非对角元非零，所以本征向量在 $0$ 的值不能为零；$f_{j,m}(0)>0$ 与 $\psi_m(0)=\sqrt2$ 最终选择同一符号。

对实际平均阻抗核应用定理 21.2 的第二种比较，所得算子范数差不超过 $2\epsilon_jL_j\Delta_r/\theta$。再次使用极小极大原理，得到显示的同长度本征值比较界。该常阻抗链满足定义 20.1 的概率条件，因为 $\widehat r_j\ge\min(r_\alpha,r_\beta)$。第 20.2 节保留半格点分母的谱式，结合 $\widehat r_j=\overline r+O(L_j^{-1})$ 与 $\epsilon_jL_j^2=\delta/\varphi^4+O(L_j^{-2})$，给出固定 $m$ 的 $O_m(L_j^{-1})$ 估计。$\square$

**命题 21.4（有限谱的转移矩阵递归与边界根）。** 对谱参数 $z$ 定义

$$
\mathsf T_r(z)=
\begin{pmatrix}
1+zr/\theta&r/\theta\\
z&1
\end{pmatrix},
\qquad
M_j(z)=
\mathsf T_{r_{(W_j)_{L_j-1}}}(z)\cdots
\mathsf T_{r_{(W_j)_0}}(z).
$$

每个矩阵的行列式为 $1$。由 $W_{j+2}=W_{j+1}W_j$，乘法次序为

$$
M_{j+2}=M_jM_{j+1}.
$$

若 $x_j(z)=\tfrac12\operatorname{tr}M_j(z)$，则

$$
x_{j+2}=2x_{j+1}x_j-x_{j-1}\qquad(j\ge1),
$$

初值为

$$
x_0=1+\frac{zr_\alpha}{2\theta},\qquad
x_1=1+\frac{zr_\beta}{2\theta},\qquad
x_2=1+\frac{z(r_\alpha+r_\beta)}{\theta}
+\frac{z^2r_\alpha r_\beta}{2\theta^2}.
$$

这给出有限词转移矩阵的半迹递归。反射—吸收本征值仍须由实际边界根判定：

$$
\bigl(M_j(\lambda-1)\bigr)_{11}=0.
$$

不能仅以半迹的某个取值替代此边界条件。

**证明。** 令 $f$ 为本征向量并设

$$
J_i=\frac{\theta}{r_{(W_j)_i}}(f_{i+1}-f_i),
\qquad J_{-1}=0,\qquad f_{L_j}=0.
$$

本征方程 $K_jf=\lambda f$ 给出 $J_i-J_{i-1}=(\lambda-1)f_i$，所以

$$
\binom{f_{i+1}}{J_i}
=\mathsf T_{r_{(W_j)_i}}(\lambda-1)
\binom{f_i}{J_{i-1}}.
$$

左反射条件固定初始向量为 $(f_0,0)^{\mathsf T}$，且非零本征向量必有 $f_0\ne0$；右吸收条件因此恰为 $M_{11}=0$。反过来，该根和初始向量 $(1,0)^{\mathsf T}$ 构造出非零本征向量，所以边界根条件是充要的。半迹递归来自 $M_{j+1}=M_{j-1}M_j$、循环迹恒等式及行列式为一时的 Cayley—Hamilton 恒等式，不另给边界谱条件。$\square$

**推论 21.5（等阻抗回接与结论边界）。** 当 $r_\alpha=r_\beta=r$，令 $p=\theta/r$，并写

$$
\lambda=1-2p+2p\cos q,\qquad 0\le q<\pi.
$$

由反射初始向量产生的解为

$$
\frac{f_i}{f_0}
=\frac{\cos((i+1/2)q)}{\cos(q/2)},
\qquad
(M_j(\lambda-1))_{11}
=\frac{\cos((L_j+1/2)q)}{\cos(q/2)}.
$$

因此边界根恰为

$$
q=\frac{(2m+1)\pi}{2L_j+1},\qquad 0\le m<L_j,
$$

回到第 20 节的精确余弦根与固定低频极限。$q=\pi$ 时分子和分母同时为零，不能只解分子零点而将其计作额外本征根；连续延拓的实际边界值为

$$
\lim_{q\to\pi}
\frac{\cos((L_j+1/2)q)}{\cos(q/2)}
=(-1)^{L_j}(2L_j+1)\ne0.
$$

故 $q=\pi$ 是该分子方程引入的伪根。转移矩阵半迹递归在本节只用于有限谱递归；固定低频的同质化由 Green 核比较与孤立本征值论证承担。

本节不主张不等阻抗的全谱极限、$m$ 随 $j$ 增长时的谱或本征函数极限、原离散时钟半群的全空间范数收敛或大偏差原理。它也不推出物理热流、温度、量子输运或经验普适性。递归提供逐字二字母阻抗排列和 Fibonacci 长度比例；单位速度、阻抗值、跳尺度、时钟及反射—吸收边界仍是外加模型条件。

## 22. 统一 Green 核的四重表征与低频接口

本节把前面各层结果接到同一个连续算子上。这里仍固定正阻抗 $r_\alpha,r_\beta$、单位速度、左反射右吸收边界、数值时钟 $\epsilon_j=\delta/N_j^2$、初态 $0$ 及逐字源 $W_j$；速度权重、不同边界和不同初始律不并入本节的统一接口。

**定义 22.1（连续 Green 算子）。** 令

$$
C(u,v)=\frac{1-\max(u,v)}D,
\qquad
(\mathsf C f)(u)=\int_0^1C(u,v)f(v)\,dv,
$$

并令 $\mathsf H$ 是带边界条件

$$
\mathsf H=-D\frac{d^2}{du^2},
\qquad
f'(0)=0,\quad f(1)=0
$$

的算子。于是 $\mathsf C=\mathsf H^{-1}$。记

$$
 k_m=\left(m+\frac12\right)\pi,
\qquad
\psi_m(u)=\sqrt2\cos(k_m u),
\qquad
\rho_m=\frac1{Dk_m^2}.
$$

**定理 22.2（统一 Green 核桥）。** 设 $\bar r=\varphi^{-2}r_\alpha+\varphi^{-1}r_\beta$，并令

$$
D=\frac{\theta\varphi^4}{\delta\bar r},
\qquad
\mathcal K_j(u,v)=\epsilon_jL_jG_j(\iota_j(u),\iota_j(v)),
$$

其中 $G_j=(I-K_j)^{-1}$ 是暂态 Green 矩阵。则

$$
G_j(i,k)=\frac1\theta\sum_{h=\max(i,k)}^{L_j-1}r_{(W_j)_h},
$$

并且

$$
\|\mathcal K_j-C\|_\infty
\le
\left|\frac{\epsilon_j\bar rL_j^2}{\theta}-\frac1D\right|
+\frac{\epsilon_jL_j}{\theta}
\bigl(\bar r+|r_\alpha-r_\beta|\bigr)
=O(L_j^{-1}).
$$

**证明。** 机械词的区间平衡给出任意区间内的 $\alpha$ 个数与 $\varphi^{-2}$ 乘区间长度之差小于一。因此该区间的阻抗和与 $\bar r$ 乘区间长度之差不超过 $|r_\alpha-r_\beta|$。首步方程的离散通量消元给出 Green 矩阵的尾和公式。将尾和中的阻抗和替换为 $\bar r$ 乘尾长度，误差至多为 $|r_\alpha-r_\beta|$；格点取整再增加至多一个格点长度的误差。最后使用 $N_j/L_j\to\varphi^2$ 及 $\epsilon_jL_j=O(L_j^{-1})$，得到所列一致估计。$\square$

**推论 22.3（同一算子的四种读法）。** 在定理 22.2 的条件下，下列对象共享同一连续核，但量词仍分别受前面各节的范围约束：

1. 对固定有限个探针，$C$ 的有限主子矩阵给出第16节的联合 Laplace 行列式。
2. 对非负连续函数 $f$，$M_{\sqrt f}\mathsf C M_{\sqrt f}$ 是正迹类算子，并给出第17节的 Fredholm Laplace 泛函

   $$
   \mathbb E\exp\left(-\int_0^1f(u)\Lambda(u)\,du\right)
   =\det_F(I+\mathsf C M_f)^{-1}.
   $$

3. 反向坐标场 $Y(s)=\Lambda(1-s)$ 是第18节的二维平方贝塞尔能量过程，满足

   $$
   dY(s)=\frac1D\,ds+\sqrt{\frac{2Y(s)}D}\,dW(s).
   $$

4. $\mathsf C$ 的非零谱为 $(\rho_m)_{m\ge0}$，本征函数为 $(\psi_m)_{m\ge0}$。因此第20、21节的固定低频本征对都回接到同一组半整数 Neumann—Dirichlet 模态。

这里“四种读法”是同一 Green 核的不同投影，不是一个新的全局收敛定理；有限探针、连续测度、Markov 表示和低频谱各自保留原有的固定量词。

**推论 22.4（Fredholm 行列式与通过时间的回接）。** 对常数探针 $f\equiv s\ge0$，有

$$
\det_F(I+s\mathsf C)
=\prod_{m=0}^{\infty}(1+s\rho_m)
=\cosh\sqrt{\frac{s}{D}}.
$$

于是极限总占用质量满足

$$
\mathbb E\exp\left(-s\int_0^1\Lambda(u)\,du\right)
=\operatorname{sech}\sqrt{\frac{s}{D}}.
$$

等价地，若 $(E_m)_{m\ge0}$ 是独立均值为 $1$ 的指数变量，则

$$
\int_0^1\Lambda(u)\,du
\ \stackrel{d}{=}\ \sum_{m=0}^{\infty}\rho_mE_m,
\qquad
\sum_{m\ge0}\rho_m=\frac1{2D},
\qquad
\sum_{m\ge0}\rho_m^2=\frac1{6D^2}.
$$

这同时回接总占用质量的极限均值与方差；它仍是分布等式，不指定不同 $j$ 之间的逐样本耦合。

该表达式与反射—吸收连续扩散从 $0$ 出发的通过时间 Laplace 变换一致，也与第10节和第15节的标量极限相接。

**证明。** 半整数本征值给出 Fredholm 行列式的乘积；Euler 乘积公式

$$
\cosh z=\prod_{m=0}^{\infty}
\left(1+\frac{4z^2}{(2m+1)^2\pi^2}\right)
$$

代入 $z=\sqrt{s/D}$ 即得。指数变量级数的 Laplace 变换是上述乘积的倒数。常数探针的占用质量是通过时间的缩放极限，所以其 Laplace 变换与连续反射—吸收问题的预解式相同。$\square$

**推论 22.5（低频生存谱接口）。** 令 $x\in[0,1)$。连续反射—吸收扩散的生存函数为

$$
S_x(t)=2\sum_{m=0}^{\infty}
\frac{(-1)^m\cos(k_mx)}{k_m}
\exp(-Dk_m^2t),
\qquad t>0.
$$

特别地，

$$
\int_0^\infty e^{-st}S_0(t)\,dt
=\frac{1-\operatorname{sech}\sqrt{s/D}}s.
$$

离散生存谱要回接到此式，必须同时满足两个条件：对每个预先固定的 $m$，离散本征缺陷与 $\epsilon_jDk_m^2$ 的比值趋于一，并且对任意 $t_0>0$，$t\ge t_0$ 时高频余项具有统一可求和控制。仅有固定模态的逐项收敛不足以推出整条生存级数的收敛。

**证明。** 连续核的边值问题给出 $\psi_m$ 和 $Dk_m^2$；常数函数在这些本征函数上的投影为 $2(-1)^m/k_m$，逐项求和得到 $S_x$。对 $x=0$ 使用

$$
\int_0^\infty e^{-st}S_0(t)\,dt
=\frac{1-\mathbb E_0e^{-s\tau}}s,
$$

再代入推论22.4。离散级数需要额外的高频尾控制，因为当 $p=1/2$ 时存在接近 $-1$ 的高频本征值；该尾控制不能由低频本征对的收敛自动得到。$\square$

本节的统一接口不改变各层边界：$f$ 必须是非负连续测试函数；Fredholm 行列式需要迹类或等价的谱尾控制；固定低频结论不延伸到 $m=m(j)$、全谱、全空间半群范数或 $t=0$ 一致生存尾；有限 Green 核的一致收敛不单独推出完整转移概率的同质化。速度权重应改写为加权算子 $\mathsf C M_v$ 或其对称化，而不能沿用原来的同一谱参数。Brownian 场与平方贝塞尔过程只是极限分布的辅助表示，不给出跨 $j$ 或跨速度模型的原概率空间耦合。递归仍不选择阻抗、跳率、边界或时钟，也不推出物理热流、温度、量子输运或经验普适性。

## 追加锚（本行以下为增补区）

## 23. Green 核的物理类比接口与识别边界

第22节的共同核可以产生若干物理术语的数学对应，但对应关系必须停留在明确的算子、概率和边界条件上。以下把可直接推出的部分与需要外加模型的部分分开。

**定义 23.1（源—响应算子）。** 对连续源 $g$，令

$$
(Tg)(x)=(\mathsf Cg)(x)=\int_0^1C(x,u)g(u)\,du.
$$

则 $Tg$ 是边值问题

$$
-D(Tg)''=g,
\qquad
(Tg)'(0)=0,
\qquad
(Tg)(1)=0
$$

的唯一 $C^2$ 解。因而 $C$ 可以严格称为该反射—吸收模型的静态源—响应核。若 $\mathsf S(t)=e^{-t\mathsf H}$ 是同一边值问题的杀死扩散半群，则

$$
\mathsf C=\int_0^\infty\mathsf S(t)\,dt
$$

在强算子意义下成立；$C$ 是零频或时间积分响应，而不是自动给定的因果物理易感率。

**命题 23.2（生成泛函的响应—涨落恒等式）。** 对非负连续源 $f$，令

$$
Z(f)=\mathbb E\exp\left(-\int_0^1f(u)\Lambda(u)\,du\right)
=\det_F(I+\mathsf C M_f)^{-1}.
$$

对连续方向 $h,k$，在零源处有

$$
\left.\frac{d}{dt}\log Z(th)\right|_{t=0}
=-\int_0^1h(u)C(u,u)\,du,
$$

以及

$$
\left.\frac{\partial^2}{\partial s\,\partial t}
\log Z(sh+tk)\right|_{s=t=0}
=\int_0^1\int_0^1h(u)k(v)C(u,v)^2\,du\,dv.
$$

左式给出占用场的均值响应，右式给出两个源方向的联合涨落；它们也分别等于

$$
\mathbb E\int h\,d\mu,
\qquad
\operatorname{Cov}\left(\int h\,d\mu,\int k\,d\mu\right).
$$

**证明。** 将

$$
\log Z(f)=-\operatorname{Tr}\log(I+\mathsf C M_f)
$$

在零源处展开。一次项为 $-\operatorname{Tr}(\mathsf C M_h)$，等于 $-\int h(u)C(u,u)du$；二次混合项由迹的循环不变性合并为 $\operatorname{Tr}(\mathsf C M_h\mathsf C M_k)$，其核为 $h(u)k(v)C(u,v)^2$。这与第17、18节的均值和协方差公式一致。$\square$

**推论 23.3（谱弛豫的数学读法）。** 连续半群的模态满足

$$
\mathsf S(t)\psi_m=e^{-Dk_m^2t}\psi_m.
$$

因此

$$
\tau_m=\frac1{Dk_m^2}=\rho_m
$$

是第 $m$ 个数学弛豫时间，最低模态给出最长时间尺度

$$
\tau_0=\frac4{D\pi^2}.
$$

这说明 Green 核、总占用质量和生存谱共享同一组弛豫模态：Green 特征值是模态时间尺度，生存函数是模态指数衰减，随机总质量是同一谱权重下的指数级数。

**推论 23.4（能量与配分函数的受限类比）。** 对非负权重 $f$，可定义抽象占用泛函

$$
E_f=\int_0^1f(u)\Lambda(u)\,du.
$$

它满足

$$
\mathbb E E_f=\int_0^1f(u)\frac{1-u}{D}\,du,
$$

$$
\operatorname{Cov}(E_f,E_g)
=\int_0^1\int_0^1f(u)g(v)C(u,v)^2\,du\,dv.
$$

常数权重下，

$$
\mathbb E E_1=\frac1{2D},
\qquad
\operatorname{Var}(E_1)=\frac1{6D^2},
$$

而 $-\log Z(s)$ 具有二次高斯系综中自由能的形式。这里的“能量”和“配分函数”只是对非负随机泛函及其 Laplace 变换的命名类比；它们没有自动取得物理单位、Gibbs 权重、熵或相变含义。

**推论 23.5（速度权重的响应重整化）。** 若额外加入连续正速度权重 $v$，则静态响应改为

$$
T_vg=\mathsf C(vg),
\qquad
-D(T_vg)''=v g,
$$

相应的对称谱问题为

$$
-D\phi''=\lambda v\phi,
\qquad
\phi'(0)=0,\quad \phi(1)=0.
$$

因此 $v$ 改变的是响应核和谱度量；它不能与单位速度模型共用同一个谱参数、平方贝塞尔参数或涨落—耗散解释。

本节给出的“静态响应”“谱弛豫”“涨落—耗散形式”“占用能量”和“配分函数”之间的关系，都是 Green 逆、正半群、Gaussian 二次泛函与平方贝塞尔表示之间的数学关系。要把它们提升为物理定律，还必须另行指定实际观测量与单位、外部扰动的耦合、因果时间协议、热浴或平衡系综、温度、耗散系数、能量守恒及详细平衡。当前模型没有这些数据，因此不能由 FIB 递归单独推出物理热流、温度、实验线性响应、涨落—耗散定律、Gibbs 熵、量子输运或经验普适性；第5、6、11、14、15节的不可识别性例子进一步说明相同部分静态读数可以对应不同通量、通过时间或联合耦合。

## 追加锚（本行以下为增补区）

## 24. 被杀死半群与物理读出的条件迁移

第22、23节使用的是被杀死半群，必须把它与在吸收端停留的完整过程分开。令 $Z_t$ 表示到达吸收端前的过程，并把吸收后的状态记为墓地点 $\partial$。其半群为

$$
(\mathsf S_t f)(x)=\mathbb E_x\bigl[f(Z_t)\,\mathbf 1_{\{t<\tau\}}\bigr],
$$

在连续区间上对应 $f(1)=0$ 的 Dirichlet 端点，因此会损失总质量。若 $X_t$ 是到达 $1$ 后永久停留的完整吸收过程，则对 $x<1$ 有

$$
\widetilde{\mathsf S}_t f(x)
=\mathsf S_t\bigl(f-f(1)\bigr)(x)+f(1),
$$

并且 $\delta_1$ 是完整过程的吸收不变律。占用测度 $\mu_j$ 与场 $\Lambda$ 记录的是吸收前的暂态占用，不能直接解释为完整过程的平衡温度或 Gibbs 状态。

**定理 24.1（物理读出的条件迁移）。** 假设在第12节的路径缩放下，离散过程 $Z_j$ 弱收敛到反射—吸收极限 $Z$。若另给物理读出映射 $\Phi_j$，并且在选定路径拓扑下

$$
\Phi_j(Z_j)\Longrightarrow\Phi(Z),
$$

其中 $\Phi$ 连续于极限路径的满概率集合，则物理读出的极限律是

$$
\operatorname{Law}\bigl(\Phi(Z)\bigr).
$$

这只是指定读出下的条件统计结论。若进一步假设一个标量场 $T$ 是该半群的线性期望状态，并另行给出守恒律、本构关系

$$
\partial_tT=D\partial_u^2T,
\qquad
J=-D\partial_uT,
$$

以及左端零通量、右端固定值的边界条件，才可以把相应的 $T$ 解释为该物理接口下的扩散温度场和 $J$ 解释为通量。若这些读出、单位、守恒和本构假设没有登记，统一 Green 核只给出数学响应与概率律。

**证明。** 第一部分是路径弱收敛与连续映射定理的直接应用。第二部分由所给守恒—本构方程和边界条件识别其生成元为 $D\partial_u^2$；这些方程是额外假设，不由 FIB 递归或占用场自动产生。$\square$

因此，反射—吸收路径极限不能单独推出物理温度、热流或热平衡；量子输运还需要 Hilbert 空间、Hamiltonian 或 Lindblad 动力学、初态密度矩阵以及 current/Kubo 观测映射。完整吸收过程、被杀死半群和任何物理读出若采用不同边界或单位，必须重新登记其映射，不能沿用本卷的 Dirichlet Green 核。

## 追加锚（本行以下为增补区）

## 25. FIB 区间平衡与响应—输运的可识别性

第22节的统一核给出宏观响应，但宏观核会压缩部分微观信息。本节记录这种压缩的精确边界。

**命题 25.1（区间平衡产生的有效响应）。** 令 $a_F=\varphi^{-2}$，并沿用

$$
\bar r=a_Fr_\alpha+(1-a_F)r_\beta,
\qquad
D=\frac{\theta\varphi^4}{\delta\bar r}.
$$

对 Fibonacci 词的任意区间 $[b,c)$，有

$$
\left|\sum_{i=b}^{c-1}r_{(W_j)_i}-\bar r(c-b)\right|
\le |r_\alpha-r_\beta|.
$$

因此对每个连续源 $f$，离散 Green 算子

$$
(\mathcal T_jf)(u)=\epsilon_j\sum_{i=0}^{L_j-1}
G_j(\iota_j(u),i)f(i/L_j)
$$

收敛到

$$
(\mathcal Tf)(u)=\frac1D\int_0^1(1-\max(u,v))f(v)\,dv,
$$

并满足

$$
-D(\mathcal Tf)''=f,
\qquad
(\mathcal Tf)'(0)=0,
\qquad
(\mathcal Tf)(1)=0.
$$

这里的 $O(L_j^{-1})$ 一致核误差来自均匀区间平衡；只有整体字母频率收敛而没有区间误差界时，不能推出这个一致响应结论。

**命题 25.2（微观阻抗的有限层识别与宏观丢失）。** 若完整有限 Green 矩阵的对角读数

$$
q_{j,i}=G_j(i,i)
$$
已知，则逐边阻抗可由

$$
 r_{(W_j)_i}=\theta(q_{j,i}-q_{j,i+1}),
\qquad q_{j,L_j}=0
$$

精确恢复。相反，连续极限核只保留 $\bar r$ 进入的组合 $D$，一般不能恢复 $r_\alpha$ 与 $r_\beta$ 各自的值。

为说明这一点，取足够小且非零的 $t$，令

$$
 r'_\alpha=r_\alpha+t(1-a_F),
 \qquad
 r'_\beta=r_\beta-ta_F.
$$

若 $t$ 足够小使两组阻抗都满足随机核条件，则

$$
 a_Fr'_\alpha+(1-a_F)r'_\beta=\bar r,
$$

所以 $D$、连续 Green 核、占用场极限和固定低频极限都不变；但只要两字母均在有限词中出现，尾和 Green 矩阵一般改变，因而有限层的完整响应不同。这是宏观同质化不可逆丢失微观阻抗对比的成对实例。

**命题 25.3（速度权重的尺度歧义）。** 连续正速度权重下，所有起点的平均通过时间满足

$$
T_v(x)=\frac1D\int_0^1(1-\max(x,u))v(u)\,du,
\qquad
-DT_v''=v.
$$

若 $D$ 已知，则完整函数 $T_v$ 或完整占用均值

$$
 m_{\mathrm{occ}}(u)=\frac{v(u)(1-u)}D
$$

可以恢复 $v$。若 $D$ 也未知，则变换

$$
(D,v)\longmapsto(cD,cv),qquad c>0
$$

保持 $T_v$、占用均值和连续输运生成元中的比值 $D/v$ 不变；观测只能恢复 $v/D$。单一起点均值或有限个测试函数均值只提供有限个线性约束，不能识别一般连续速度函数。

**推论 25.4（何时才能称为输运定律）。** 要把 $\mathcal T$ 或 $T_v$ 称为物理输运定律，至少还需固定：

1. 空间与物理长度的映射；
2. 离散时间与物理时间的映射；
3. 初始律、速率核和边界类型；
4. 指定的路径、半群或生成元收敛拓扑；
5. 位置、占用、响应到实际观测量的映射；
6. 若使用温度或热流，还需守恒方程、本构关系、单位和热浴。

第13节的近 $-1$ 高频模态说明，Green 核或零频统计收敛仍不足以推出原离散半群的全空间范数输运；第14节说明同一总速度质量和同一左端均值仍可有不同二阶通过律；第15节说明相同边缘律仍可有不同联合历史。因此有效介质类比是有条件的宏观响应结论，不是由 FIB 递归单独产生的普适输运定律。

## 追加锚（本行以下为增补区）

## 26. 物理读出与算子层级的条件修正

为避免把不同层级的极限混在一起，本节固定算子空间与读出假设。令

$$
\mathcal D(\mathsf H)=\{f\in H^2([0,1]):f'(0)=0,\ f(1)=0\},
\qquad
\mathsf Hf=-Df''.
$$

在 $L^2([0,1])$ 上，$\mathsf H$ 是正自伴算子，且 $\mathsf C=\mathsf H^{-1}$；因此第23节的半群积分是在强算子意义下理解的。对非负连续方向 $h,k$，第23节的生成泛函公式首先按右导数成立。若要使用带符号方向，必须另行声明零源邻域内的 Fredholm 行列式解析延拓及相应的可积性条件。

**定理 26.1（连续读出迁移）。** 设离散路径 $Z_j$ 在指定路径拓扑下收敛于 $Z$。若存在连续读出 $\Phi$ 以及近似读出 $\Phi_j$，满足

$$
 d\bigl(\Phi_j(Z_j),\Phi(Z_j)\bigr)\longrightarrow0
$$

依概率成立，则

$$
\Phi_j(Z_j)\Longrightarrow\Phi(Z).
$$

这里的距离和连续性必须使用同一物理读出空间；它们不能由 Green 核收敛自动替代。若要把单路径极限变成温度或密度场，还需明确取期望 $T(t,u)=\mathbb E[\Phi(Z_t)(u)]$，或给出独立粒子/经验测度的极限与归一化。

**定理 26.2（守恒—本构条件下的热方程）。** 若另行给出标量场 $T$、通量 $J$ 和源 $q$，满足

$$
\partial_tT+\partial_uJ=q,
\qquad
J=-D\partial_uT,
$$

并指定左端零通量、右端固定值及初值，则可推出

$$
\partial_tT=D\partial_u^2T+q
$$

及相应边界条件。这里热方程由守恒和本构关系推出；它们不是 FIB 递归、Green 核或单条占用路径的自动结论。

因此，缺少读出连续性、期望或经验测度构造、守恒律、本构关系和单位映射时，只能报告数学路径律、占用分布和算子响应。该条件修正也保持被杀死半群与完整吸收过程的区分；吸收端的质量是否进入场变量，必须由物理读出另行规定。

## 追加锚（本行以下为增补区）

## 27. 总占用的谱隙尾与累积量

令

$$
M=\int_0^1\Lambda(u)\,du,
\qquad
\rho_m=\frac4{D\pi^2(2m+1)^2},
\qquad
\lambda_m=\rho_m^{-1}.
$$

**定理 27.1（标量总占用的完整累积量与尾部）。** 在第22节的极限分布下，存在独立均值为 $1$ 的指数变量 $E_m$，使

$$
M\ \stackrel d=\ \sum_{m=0}^{\infty}\rho_mE_m.
$$

其矩母函数在 $t<\lambda_0=D\pi^2/4$ 时为

$$
\mathbb E e^{tM}
=\prod_{m=0}^{\infty}(1-t\rho_m)^{-1}
=\sec\sqrt{\frac tD},
$$

其中 $t\ge0$ 时的收敛域是 $0\le t<\lambda_0$。对每个整数 $n\ge1$，$M$ 的第 $n$ 阶累积量为

$$
\kappa_n(M)
=(n-1)!\sum_{m=0}^{\infty}\rho_m^n
=(n-1)!\frac{(2^{2n}-1)\zeta(2n)}{D^n\pi^{2n}}.
$$

特别地，

$$
\kappa_1(M)=\frac1{2D},
\qquad
\kappa_2(M)=\frac1{6D^2}.
$$

此外，

$$
\Pr(M>x)\sim\frac4\pi
\exp\left(-\frac{D\pi^2}{4}x\right)
\qquad(x\to\infty).
$$

**证明。** 指数变量的独立性给出

$$
\mathbb E e^{tM}=\prod_m(1-t\rho_m)^{-1}.
$$

Euler 乘积将分母化为 $\cos\sqrt{t/D}$；首个奇数模态确定收敛半径 $\lambda_0$。对数展开

$$
\log\mathbb E e^{tM}
=\sum_{n\ge1}\frac{t^n}{n}\sum_m\rho_m^n
$$

给出累积量公式；奇数倒数幂和为

$$
\sum_{m\ge0}(2m+1)^{-2n}=(1-2^{-2n})\zeta(2n).
$$

最后写 $M=\rho_0E_0+Y$，其中 $Y=\sum_{m\ge1}\rho_mE_m$ 与 $E_0$ 独立。因为 $\lambda_1=9\lambda_0$，$Y$ 在 $\lambda_0$ 右侧仍有指数矩，故

$$
\Pr(M>x)\sim e^{-\lambda_0x}\mathbb E e^{\lambda_0Y}.
$$

而

$$
\mathbb E e^{\lambda_0Y}
=\prod_{m=1}^{\infty}
\left(1-\frac{\rho_m}{\rho_0}\right)^{-1}
=\prod_{m=1}^{\infty}
\left(1-\frac1{(2m+1)^2}\right)^{-1}
=\frac4\pi.
$$
这证明了尾部常数。$\square$

**推论 27.2（通过时间的谱隙尾）。** 由于第22.4节的总占用质量与连续反射—吸收通过时间具有相同分布，连续通过时间的长时间尾为

$$
\Pr_0(\tau>t)
\sim\frac4\pi e^{-D\pi^2t/4}.
$$

这与第20节的首低频模态系数和衰减率一致。谱隙 $D\pi^2/4$ 是该模型的数学弛豫率；把它解释成激活能、温度倒数或 Arrhenius 常数，还需要额外的物理能量和温度映射。

本节只给出连续极限的一个标量尾部和累积量序列，不给出占用场的全局大偏差原理，也不把有限链的高频尾自动替换成统一的矩母函数或尾部估计。长时间渐近的顺序是先固定连续极限再令 $t\to\infty$，不能交换 $j\to\infty$ 与 $t\to\infty$，也不能把首模态指数率称为 Arrhenius 激活率。没有独立复制数、指数紧性和统一的 $j$ 依赖对数矩母函数，不能推出 Cramér 或 Gärtner—Ellis 大偏差。特别是在 $p=1/2$ 时，近 $-1$ 高频模态仍阻止原离散半群的全空间范数结论；本节的谱隙尾只适用于已经取定的连续极限或具有额外高频尾控制的标量投影。

## 追加锚（本行以下为增补区）

## 28. 初态律对标量尾部的限定

第27节的随机变量 $M=\int_0^1\Lambda(u)\,du$ 对应初态为 $0$ 的连续极限。若改用一般初态律 $\nu$，通过时间生存函数的首模态系数改为

$$
 b_0(\nu)=\frac4\pi\int_{[0,1]}\cos\left(\frac{\pi x}{2}\right)d\nu(x),
$$

并在 $b_0(\nu)>0$ 时满足

$$
\Pr_\nu(\tau>t)\sim b_0(\nu)e^{-D\pi^2t/4}.
$$

只有 $\nu=\delta_0$ 时，前因子才是 $4/\pi$，并且通过时间才与第27节的 $M$ 具有同一分布。改变初态律会改变模态投影和尾部常数；谱隙本身保持不变，但不能把初态为 $0$ 的总占用级数恒等式直接用于一般 $\nu$。

## 追加锚（本行以下为增补区）

## 29. 连续探针泛函的连通涨落层级

对非负连续探针 $f$，令

$$
E_f=\int_0^1f(u)\Lambda(u)\,du.
$$

**定理 29.1（积分观测量的累积量）。** 对任意整数 $n\ge1$，有

$$
\operatorname{cum}_n(E_f)
=(n-1)!\operatorname{Tr}\bigl((\mathsf C M_f)^n\bigr)
=(n-1)!\operatorname{Tr}\bigl((M_{\sqrt f}\mathsf C M_{\sqrt f})^n\bigr)\ge0.
$$

对非负连续探针 $f_1,\ldots,f_n$，混合累积量满足

$$
\begin{aligned}
&\operatorname{cum}(E_{f_1},\ldots,E_{f_n})\\
&=\frac1n\sum_{\sigma\in S_n}
\int_{[0,1]^n}
\prod_{q=1}^n f_{\sigma(q)}(u_q)
C(u_q,u_{q+1})\,du_1\cdots du_n,
\qquad u_{n+1}=u_1.
\end{aligned}
$$

因此所有非负连续探针的连通累积量均非负；当探针在共同的非退化区域上为正时，$n\ge2$ 的相应累积量严格为正，故这些积分观测量一般不是高斯族。

**证明。** 对足够小的参数 $t_i$，第22节的 Fredholm 公式给出

$$
\log\mathbb E\exp\left(\sum_i t_iE_{f_i}\right)
=-\operatorname{Tr}\log\left(I-\mathsf C M_{\sum_i t_if_i}\right)
=\sum_{r\ge1}\frac1r
\operatorname{Tr}\left((\mathsf C M_{\sum_i t_if_i})^r\right).
$$

取 $n$ 个互异参数的混合导数时只有 $r=n$ 项保留，得到循环迹公式。相同探针时，循环迹经过相似变换化为正自伴算子的幂迹，故非负；混合形式的积分核逐项非负。$\square$

**推论 29.2（连接到响应与物理类比）。** 一阶累积量是静态源—响应的对角读数，二阶累积量是第23节的 $C^2$ 涨落核，高阶累积量则是由同一 Green 核组成的闭合循环。它们可以作为“连通响应簇”或“非高斯涨落簇”的数学类比，但不自动构成热力学关联函数、场论图展开或局部相互作用。

本节的累积量层级是固定连续极限、固定有限探针和有限阶 $n$ 的结论。它不推出探针数、复制数或系统尺寸增长时的统一控制，不给出大偏差率函数、Gibbs 自由能或热力学相变；若要作这些外推，必须另行指定相应的随机序列、尺度和指数紧性。

## 追加锚（本行以下为增补区）

## 30. 有限链通过时间的精确预解式接口

令暂态矩阵为 $K_j$，起点为暂态切点 $i<L_j$，并记

$$
M_j=\epsilon_j\tau_j,
\qquad q=e^{-s\epsilon_j},\quad s\ge0.
$$

**命题 30.1（有限链的 Laplace—resolvent 恒等式）。** 有限链上有精确公式

$$
\mathbb E_i e^{-sM_j}
=1-(1-q)e_i^{\mathsf T}(I-qK_j)^{-1}\mathbf1.
$$

若生存函数写成

$$
\Pr_i(\tau_j>n)=\sum_m a_{j,m}(i)\lambda_{j,m}^{\,n},
$$

则相应的谱表达式为

$$
\mathbb E_i e^{-sM_j}
=1-(1-q)\sum_m\frac{a_{j,m}(i)}{1-q\lambda_{j,m}}.
$$

将 $q=e^{z\epsilon_j}$ 代入时，在有限 resolvent 的收敛域内得到有限链的正向矩母函数。相应连续模型从 $x$ 出发时，对 $0\le z<D\pi^2/4$ 有

$$
\frac{\cos(x\sqrt{z/D})}{\cos\sqrt{z/D}},
$$

其中 $x=0$ 的反射端特例才是 $\sec\sqrt{z/D}$。若 $i_j/L_j\to x$，有限链向该式收敛还需要统一指数尾控制；有限 $j$ 的 resolvent 域本身不提供该控制。

**证明。** 对整数值吸收时间，尾和恒等式为

$$
1-\mathbb E_i q^{\tau_j}
=(1-q)\sum_{n\ge0}q^n\Pr_i(\tau_j>n).
$$

而

$$
\sum_{n\ge0}q^n\Pr_i(\tau_j>n)
=e_i^{\mathsf T}(I-qK_j)^{-1}\mathbf1.
$$

代入即得第一式；对生存谱逐项求和即得第二式。特别地，若 $\tau_j=1$ 恒定，则公式给出 $\mathbb E q^{\tau_j}=q$，核对了前面的符号。$\square$

对每个固定 $s\ge0$，第10.3节的 Green 算子收敛给出 $\mathbb E_i e^{-sM_j}$ 的连续极限；对每个固定矩阶数，求导则回到第10.3节的矩递推。这个接口不提供 $s$ 随 $j$ 增长时的统一控制，也不把带符号的有限谱系数解释为独立概率。正向矩母函数在极限半径内的一致收敛仍需额外的指数尾界；近 $-1$ 高频模态和初态投影可能改变有限 $j$ 的远尾。

## 追加锚（本行以下为增补区）

## 31. 有限 resolvent 的正向域与量词修正

为把第30节的有限链接口用于正向矩母函数，令

$$
q_+(z)=e^{z\epsilon_j},
\qquad
\rho(K_j)=\max_m|\lambda_{j,m}|.
$$

则

$$
\mathbb E_i e^{z\epsilon_j\tau_j}
=1+(q_+(z)-1)e_i^{\mathsf T}
(I-q_+(z)K_j)^{-1}\mathbf1
$$

只在

$$
q_+(z)\rho(K_j)<1
$$

的有限 resolvent 域内成立。等价地，对正 $z$ 需要

$$
0\le z<-\epsilon_j^{-1}\log\rho(K_j).
$$

这个有限 $j$ 的域不自动给出连续极限域 $z<D\pi^2/4$ 上的统一收敛；若要在 $z\le D\pi^2/4-\eta$ 上交换 $j\to\infty$ 与正向 resolvent 极限，必须另加统一高频指数尾控制。

对 Laplace 方向，若起点序列满足 $i_j/L_j\to x$，则固定 $s\ge0$ 时第10.3节给出

$$
\mathbb E_{i_j}e^{-s\epsilon_j\tau_j}
\longrightarrow
\frac{\cosh(x\sqrt{s/D})}{\cosh(\sqrt{s/D})}.
$$

固定阶矩也不能仅由 Laplace 收敛和形式求导得到。必须使用第10.3节的离散矩递推

$$
B_jM_{j,p}=\epsilon_j^p\mathbf1
+\sum_{k=1}^{p-1}\binom pk\epsilon_j^{p-k}K_jM_{j,k}
$$

以及预先固定的阶数 $p$ 和一个更高阶的统一矩界，以取得均匀可积性。因而这里的合法量词是“先固定 $p$ 和 $i_j/L_j\to x$，再令 $j\to\infty$”；不覆盖 $p=p(j)$ 或 $s=s(j)$。

最后区分两种有限谱率：

$$
 g_{j,m}=\frac{1-\lambda_{j,m}}{\epsilon_j},
\qquad
 \widehat g_{j,m}=-\epsilon_j^{-1}\log|\lambda_{j,m}|.
$$

前者是生成元缺陷，后者是离散生存尾的绝对指数率；低频极限下二者趋于同一连续值，但有限 $j$ 时不能互换。近 $-1$ 模态尤其说明，零频 Green 收敛、固定低频收敛和全时域生存尾是不同命题。

## 追加锚（本行以下为增补区）

## 32. 初态律、谱投影与响应幅度

令 $\nu_j$ 是暂态切点及吸收端上的初态概率律，并假设其归一化坐标推前弱收敛到 $\nu$。记

$$
L_{j,\nu_j}(s)=\mathbb E_{\nu_j}e^{-s\epsilon_j\tau_j}.
$$

**定理 32.1（初态律的连续 Laplace 变换）。** 对每个固定 $s\ge0$，有

$$
L_{j,\nu_j}(s)\longrightarrow L_\nu(s)
=\frac{\displaystyle\int_{[0,1]}
\cosh\left(x\sqrt{\frac{s}{D}}\right)d\nu(x)}
{\displaystyle\cosh\sqrt{\frac{s}{D}}}.
$$

吸收端的质量给出分式中的恒等值 $1$，与到达吸收端后通过时间为零相容。若固定整数 $p\ge1$ 并使用第10.3节的统一高阶矩界，则

$$
\mathbb E_{\nu_j}(\epsilon_j\tau_j)^p
\longrightarrow
p!\int_{[0,1]}(\mathcal T^p\mathbf1)(x)d\nu(x).
$$

**推论 32.2（初态只改变投影幅度）。** 令 $k_m=(m+1/2)\pi$。连续生存函数可写为

$$
S_\nu(t)=\sum_{m=0}^{\infty}b_m(\nu)e^{-Dk_m^2t},
$$

其中

$$
 b_m(\nu)=\frac{2(-1)^m}{k_m}
\int_{[0,1]}\cos(k_mx)d\nu(x).
$$

因此谱率 $Dk_m^2$ 由动力学和边界决定，而 $b_m(\nu)$ 由初态准备决定。若 $b_0(\nu)>0$，则

$$
S_\nu(t)\sim b_0(\nu)e^{-D\pi^2t/4}
\qquad(t\to\infty).
$$

**证明。** 第10.3节给出的嵌入 Laplace 变换对起点坐标在 $[0,1]$ 上连续且有界；弱收敛的初态律因此可与该连续函数积分，得到第一式。固定阶矩的结论使用同一节的离散递推和统一可积性，而不是仅对 Laplace 极限形式求导。生存函数由 Neumann—Dirichlet 本征函数对初态律的投影得到；首模态与其余模态的指数率严格分离，给出尾部渐近。$\square$

这一节把“初态准备”和“动力学谱”分开：同一 FIB 词、阻抗、时钟和边界可以因初态律不同而产生不同均值、尾部幅度和有限时间响应，但不改变连续极限的本征率。该分离仍不提供物理制备协议、热浴选择或跨不同初态的共同样本耦合。

## 追加锚（本行以下为增补区）

## 33. 有限链初态混合的谱投影接口

令 $\nu_j$ 是 $\{0,1,\ldots,L_j\}$ 上的初态律，$\nu_j^{\mathrm{tr}}$ 为其在暂态集合 $\{0,\ldots,L_j-1\}$ 上的限制，并令

$$
\widehat\nu_j=\sum_{i=0}^{L_j}\nu_j(i)\,\delta_{i/L_j}.
$$

设 $\widehat\nu_j\Rightarrow\nu$ 于 $[0,1]$，并把有限链的生存谱写成

$$
\Pr_i(\tau_j>n)=\sum_m a_{j,m}(i)\lambda_{j,m}^{\,n},
\qquad
a_{j,m}(\nu_j)=\sum_{i<L_j}\nu_j(i)a_{j,m}(i).
$$

吸收端的质量不进入 $a_{j,m}(\nu_j)$；它只在连续坐标中对应 $x=1$。

**定理 33.1（逐模态投影与标量生存函数的统一接口）。** 记 $k_m=(m+\tfrac12)\pi$。假设对每个固定 $m$，当 $j\to\infty$ 时有

$$
a_{j,m}(\nu_j)\longrightarrow b_m(\nu),
\qquad
\lambda_{j,m}>0\ \text{最终成立},
\qquad
-\epsilon_j^{-1}\log\lambda_{j,m}\longrightarrow Dk_m^2,
$$

其中

$$
b_m(\nu)=\frac{2(-1)^m}{k_m}
\int_{[0,1]}\cos(k_mx)\,d\nu(x).
$$

若对任意 $0<t_0<T<\infty$ 还有标量高频尾条件

$$
\lim_{M\to\infty}\limsup_{j\to\infty}
\sup_{t\in[t_0,T]}
\sum_{m>M}|a_{j,m}(\nu_j)|
|\lambda_{j,m}|^{\lfloor t/\epsilon_j\rfloor}=0,
$$

则

$$
S_{j,\nu_j}(t):=\Pr_{\nu_j}(\epsilon_j\tau_j>t)
\longrightarrow
S_\nu(t):=\sum_{m\ge0}b_m(\nu)e^{-Dk_m^2t}
$$

在每个紧区间 $[t_0,T]$ 上一致成立。这里的级数只对 $t>0$ 作解释；在 $t=0$ 不要求绝对收敛。

**证明。** 固定 $M$ 时，有限个模态的假设给出

$$
\lambda_{j,m}^{\lfloor t/\epsilon_j\rfloor}
\longrightarrow e^{-Dk_m^2t}
$$

并且在 $[t_0,T]$ 上一致。将有限和与 $m>M$ 的尾部分开，有限和先取 $j\to\infty$，两侧尾项再由假设控制。连续级数的尾部由 $|b_m(\nu)|\le 2/k_m$ 及

$$
\sum_{m>M}\frac{2}{k_m}e^{-Dk_m^2t_0}\longrightarrow0
$$

控制，故得到一致收敛。该论证只涉及标量生存函数；它不推出转移算子或全空间范数的收敛。$\square$

**推论 33.2（端点边界层与首模态）。** 对任意概率律 $\nu$，有

$$
b_0(\nu)=\frac4\pi\int_{[0,1]}
\cos\left(\frac{\pi x}{2}\right)d\nu(x).
$$

由于被积函数在 $[0,1)$ 上严格为正，$b_0(\nu)>0$ 当且仅当 $\nu([0,1))>0$。在该条件下

$$
S_\nu(t)\sim b_0(\nu)e^{-D\pi^2t/4}
\qquad(t\to\infty).
$$

若 $\nu=\delta_1$，则通过时间恒为零，所有 $b_m(\nu)$ 均为零。更一般地，若 $\nu(\{1\})>0$，则

$$
S_\nu(0+)=1-\nu(\{1\}),
$$

而有限链在所有初态均取暂态点时仍有 $S_{j,\nu_j}(0)=1$。因此从有限链到连续极限的生存函数收敛只能先在 $t>0$ 的紧区间上陈述；$t=0$ 可能存在由吸收端质量产生的边界层。

**推论 33.3（有限时间响应的可传递形式）。** 在定理 33.1 的条件下，对任意有界连续函数 $\phi$ 和 $0<t_0<T<\infty$，有

$$
\int_{t_0}^{T}\phi(t)S_{j,\nu_j}(t)\,dt
\longrightarrow
\int_{t_0}^{T}\phi(t)S_\nu(t)\,dt.
$$

这给出初态混合下的有限时间标量响应接口。若要把 $t_0\downarrow0$ 或 $T\uparrow\infty$，还必须分别补充端点一致性或统一尾界；紧区间上的谱投影收敛本身不提供这两种交换极限。

**推论 33.4（预解式与生存尾的分层）。** 定理 33.1 的条件即使成立，也不能单独推出正向矩母函数在连续谱隙以内的一致收敛。Laplace 预解式只需固定 $s\ge0$ 的有界 Green 核和初态弱收敛；正向参数 $z>0$ 还需要在整个时间轴上的统一指数尾界。因而以下三种陈述严格分开：固定低频 $s$ 的预解式收敛、固定 $t>0$ 紧区间上的生存函数收敛、以及 $z$ 取连续谱隙以内时的正向矩母函数收敛。它们不能仅凭逐模态极限相互推出。


## 追加锚（本行以下为增补区）

## 34. 完整 Laplace 曲线对初态律的可识别性

对 $[0,1]$ 上的概率律 $\nu$，定义

$$
\mathcal L(\nu)(s)
=\frac{\displaystyle\int_{[0,1]}
\cosh\left(x\sqrt{\frac{s}{D}}\right)d\nu(x)}
{\displaystyle\cosh\sqrt{\frac{s}{D}}},
\qquad s\ge0.
$$

**定理 34.1（连续初态律的变换识别）。** 若两个概率律 $\nu$ 与 $\widetilde\nu$ 满足

$$
\mathcal L(\nu)(s)=\mathcal L(\widetilde\nu)(s)
\qquad\text{对所有 }s\ge0,
$$

则 $\nu=\widetilde\nu$。此外，

$$
\lim_{s\to\infty}\mathcal L(\nu)(s)=\nu(\{1\}).
$$

因此完整的连续 Laplace 曲线同时识别吸收端质量和暂态初态律；只给定有限个频率或有限个矩则没有这个识别性。

**证明。** 令 $a=\sqrt{s/D}$ 并置

$$
G_\nu(a)=\cosh(a)\,\mathcal L(\nu)(Da^2)
=\int_{[0,1]}\cosh(ax)\,d\nu(x).
$$

$G_\nu$ 是整函数。若两条 Laplace 曲线在 $s\ge0$ 上相同，则相应的整函数在 $a\ge0$ 上相同，恒等定理给出它们在整个复平面上相同。对 $a=0$ 作偶阶导数，得到

$$
\int_{[0,1]}x^{2r}\,d\nu(x)
=\int_{[0,1]}x^{2r}\,d\widetilde\nu(x)
\qquad(r\ge0).
$$

映射 $x\mapsto x^2$ 在 $[0,1]$ 上为双射，故两个推前律具有相同的全部幂矩。连续函数可由多项式一致逼近，因而两个推前律在所有连续测试函数上的积分相同，得到 $\nu=\widetilde\nu$。另一方面，$x<1$ 时

$$
\frac{\cosh(ax)}{\cosh(a)}\longrightarrow0,
\qquad
\frac{\cosh(a)}{\cosh(a)}=1,
$$

并且该比值始终位于 $[0,1]$，由支配收敛定理得到端点质量的极限。最后，固定 $R$ 阶导数只给出 $R+1$ 个偶阶矩。取 $R+2$ 个不同点并对矩阵 $(x_i^{2r})_{0\le r\le R}$ 求非零零空间向量，再对一个在这些点上有正质量的基准概率律作足够小的正负扰动，即得到两个不同概率律而保持这 $R+1$ 个矩不变。$\square$

**推论 34.2（统计读出的层级）。** 只观察一个固定 $s$ 的响应，或只观察有限个矩阶，不能唯一确定初态律；它们只确定相应的有限维投影。若获得全 $s\ge0$ 的连续变换曲线，并且第32节的有限链到连续变换收敛在该曲线上成立，则初态律在连续模型内可识别。这个识别结论仍只关于初态概率律，不反推出 FIB 递归本身选择了哪一个制备协议，也不把变换曲线解释为物理实验中的温度谱或热浴响应。

## 35. 未知扩散尺度与初态律的联合识别边界

对 $D>0$ 写

$$
\mathcal L_{\nu,D}(s)
=\frac{\int_{[0,1]}\cosh(x\sqrt{s/D})\,d\nu(x)}
{\cosh\sqrt{s/D}}.
$$

**定理 35.1（未知 $D$ 的联合可识别性）。** 设 $D,\widetilde D>0$，$\nu,\widetilde\nu\in\mathcal P([0,1])$。若两条曲线在任意含聚点的非退化 $s>0$ 区间上相等，则只有以下退化例外：

$$
\nu=\widetilde\nu=\delta_1,
\qquad
\mathcal L_{\delta_1,D}(s)\equiv1,
$$

此时 $D$ 与 $\widetilde D$ 任意；除此之外必有 $D=\widetilde D$ 且 $\nu=\widetilde\nu$。

**证明。** 令

$$
\Phi_\nu(q)=\int_{[0,1]}\cosh(xq)\,d\nu(x),
\qquad c=\sqrt{D/\widetilde D}.
$$

实轴上的相等性经整函数恒等定理给出

$$
\Phi_\nu(q)\cosh(cq)
=\Phi_{\widetilde\nu}(cq)\cosh(q).
$$

若 $\nu\ne\delta_1$，则

$$
\Phi_\nu(i\pi/2)=\int\cos(\pi x/2)d\nu(x)>0,
$$

因为被积函数在 $[0,1)$ 上严格为正。若 $\widetilde\nu\ne\delta_1$，在 $q=i\pi/2$ 和 $q=i\pi/(2c)$ 分别代入上式，得到 $c$ 与 $1/c$ 都是正奇整数，故 $c=1$。此时 $\Phi_\nu=\Phi_{\widetilde\nu}$，再由第34节的矩确定性得到 $\nu=\widetilde\nu$。若一方为 $\delta_1$，其曲线恒等于 $1$；对任意 $s>0$，只要另一方在 $[0,1)$ 有质量，积分核严格小于 $1$，故另一方也必须为 $\delta_1$。$\square$

**推论 35.2（谱率与尺度的边界）。** 在 $\nu([0,1))>0$ 且几何边界已归一化为 $[0,1]$ 时，最近负极点为 $-D\pi^2/4$，并且

$$
D=\frac4{\pi^2}\lim_{t\to\infty}\frac{-\log S_\nu(t)}{t}.
$$

这里的 $D$ 始终是归一化区间上的模型系数。按第37节的校准约定，物理扩散系数为 $\kappa=D\ell^2/\eta$，物理时间曲线识别的组合为 $D/\eta=\kappa/\ell^2$。若模型时间与物理时间一致，即 $\eta=1$，该组合就是 $D$；未知长度仍使 $\kappa$ 无法与 $\ell$ 分开。$\nu=\delta_1$ 时生存函数恒为零，$D$ 不可由该读出识别。

## 36. 有限频率与有限噪声下的逆问题稳定性

固定 $S>0$，令

$$
\mathcal A_S\nu=\mathcal L_{\nu,D}\big|_{[0,S]}
\in C([0,S]).
$$

**定理 36.1（精确连续逆与有限读出的不可识别）。** 在概率律空间 $\mathcal P([0,1])$ 的弱拓扑和 $C([0,S])$ 的一致范数下，$\mathcal A_S$ 是连续单射，其逆在像集上连续。可是，对任意有限频率集合 $s_1,\ldots,s_m$，存在不同的概率律 $\nu_+\ne\nu_-$ 具有相同的全部读数

$$
\mathcal L_{\nu_+,D}(s_i)=\mathcal L_{\nu_-,D}(s_i),
\qquad 1\le i\le m.
$$

**证明。** 连续性来自核 $x\mapsto\cosh(x\sqrt{s/D})/\cosh\sqrt{s/D}$ 的联合连续性。第34节的整函数论证说明在一整段 $[0,S]$ 上相等即可得到全部偶矩相等，故得到单射；$\mathcal P([0,1])$ 紧而 $C([0,S])$ Hausdorff，紧集到像集的连续双射逆连续。有限频率时，取 $m+2$ 个不同点 $x_j$，向量

$$
\left(1,\mathcal L_{\delta_{x_j},D}(s_1),\ldots,
\mathcal L_{\delta_{x_j},D}(s_m)\right)
$$

位于 $\mathbb R^{m+1}$ 中，存在非零系数 $c_j$ 使其线性组合为零。以这些点上的正基准概率律作足够小的正负扰动，得到所需的 $\nu_+,\nu_-$。$\square$

**推论 36.2（弱连续逆不蕴含总变差稳定性）。** 固定 $S,D>0$。对每个整数 $q\in\mathbb N_0$，取 $q+2$ 个不同点 $x_j$，选择非零系数 $c_j$ 使

$$
\sum_j c_jx_j^{2r}=0\quad(0\le r\le q),
\qquad
\sum_j|c_j|=1,
$$

并令 $p_j^\pm=|c_j|\pm c_j$ 以及 $\nu_\pm=\sum_jp_j^\pm\delta_{x_j}$。则 $\nu_\pm$ 是两个总质量为 $1$ 的概率律，且按半 $L^1$ 约定其总变差距离为 $1$；同时它们的 $x^{2r}$ 矩在 $0\le r\le q$ 全部相同，而其 Laplace 曲线在 $[0,S]$ 上的差异为

$$
O\left((S/D)^{q+1}\!/(2q+2)!\right).
$$

令 $q\to\infty$，输出差异趋于零而输入总变差保持为 $1$，所以不存在统一的总变差连续逆，更不存在以总变差为恢复误差的 Lipschitz 或 Hölder 界。若目标是总变差稳定恢复，必须限制可允许的初态律并证明该限制下的稳定性；有限维、解析密度或矩条件只是候选限制，名称本身不保证稳定。第36.1节在整个概率律空间上的弱连续逆仍然成立，但没有给出定量恢复速率。

这一节仍只讨论归一化连续模型中的数学逆问题，不把有限频率读数解释成温度、热浴或物理仪器的充分统计量。

## 37. 长度—时间校准与边界读出的不变性

设无量纲坐标为 $u\in[0,1]$、无量纲时间为 $t$，并把物理读出写成

$$
y=\ell u,
\qquad T=\eta t,
\qquad \ell,\eta>0.
$$

若无量纲扩散方程的系数为 $D$，则物理坐标中的扩散系数为

$$
\kappa=\frac{D\ell^2}{\eta},
$$

物理 Laplace 读出满足

$$
L_{\mathrm{phys}}(\sigma)
=\mathcal L_{\nu,D}(\eta\sigma),
$$

物理谱率为

$$
\Lambda_m^{\mathrm{phys}}
=\frac{D}{\eta}\left(m+\tfrac12\right)^2\pi^2
=\frac{\kappa}{\ell^2}\left(m+\tfrac12\right)^2\pi^2.
$$

**定理 37.1（校准不变性与可识别组合）。** 在固定 Neumann—Dirichlet 几何和归一化坐标下，谱率比

$$
\frac{\Lambda_m^{\mathrm{phys}}}{\Lambda_0^{\mathrm{phys}}}=(2m+1)^2
$$

以及 Laplace 曲线的无量纲形状保持不变。若时间校准 $\eta$ 未知，物理时间读出至多识别 $D/\eta$；若长度 $\ell$ 未知，物理扩散系数至多识别 $\kappa/\ell^2=D/\eta$。因此不能由 FIB 递归单独分离 $D,\ell,\eta$ 或物理单位下的初态位置律。

**证明。** 由 $T=\eta t$ 有 $\mathbb E e^{-\sigma T}=\mathbb E e^{-(\eta\sigma)t}$，得到第一式；由 $y=\ell u$ 有 $\partial_T=(D/\eta)\partial_u^2=(D\ell^2/\eta)\partial_y^2$，得到 $\kappa$ 和谱率表达式。对任意 $a,b>0$，变换

$$
(D,\ell,\eta)\longmapsto(aD,b\ell,a\eta)
$$

保持 $D/\eta$ 与 $\kappa/\ell^2$，故未经标定的参数不能分别识别。$\square$

若位置读出为未知单调映射 $y=\ell F(u)$，则一般不能继续使用常系数热方程。令 $G=F^{-1}$，对无量纲位置 $\bar y=F(u)$ 的标量场 $\bar v(\bar y,t)=p(G(\bar y),t)$，再令 $y=\ell\bar y$、$T=\eta t$，有

$$
\partial_T v
=\frac D\eta\left(\ell^2F'(G(y/\ell))^2\partial_y^2v
+\ell F''(G(y/\ell))\partial_yv\right).
$$

因此只有 $F$ 已知且满足 $C^2$ 严格递增正导数条件时，才可把无量纲 Green 核解释成给定物理介质的算子；若 $p$ 表示密度，还需在推前读出中加入相应 Jacobian。未知 $F$ 时，递归只确定抽象核及其推前测度，不能宣称均匀介质或常系数热流。

**推论 37.2（边界条件是独立模型输入）。** 对固定 $\rho\ge0$，考虑边值问题 $Dh''=sh$、$h'(0)=\rho h(0)$、$h(1)=1$，其中左端导数朝区间内部取正。对 $s>0$，其唯一解为

$$
h_{\rho}(x,s)=
\frac{\cosh(kx)+(\rho/k)\sinh(kx)}
{\cosh(k)+(\rho/k)\sinh(k)},
\qquad k=\sqrt{s/D}.
$$

在 $s=0$ 处的连续延拓为

$$
h_\rho(x,0)=\frac{1+\rho x}{1+\rho}.
$$

这是由通解 $A\cosh(kx)+B\sinh(kx)$ 和两个边界条件直接得到的边值结论。若另外指定左端按该 Robin 参数通过边界局部时杀死的随机模型，记其杀死时刻为 $\zeta_0$、右端命中时刻为 $\tau_1$，相应读出才解释为缺陷变换

$$
\mathbb E_x\!\left[e^{-s\tau_1}\mathbf1_{\{\tau_1<\zeta_0\}}\right].
$$

当 $\rho>0$ 且 $x<1$ 时，零频值小于 $1$，故它不是第32节必达吸收时间的普通概率 Laplace 变换。当前的 $\cosh(kx)/\cosh(k)$ 只是 $\rho=0$ 的 Neumann 特例。未知边界类型时，FIB 递归不能选择 Neumann、Robin 或 Dirichlet 的谱；对应的零点、谱隙和 Green 核均需随边界假设重新推导。物理温度、热流、容量和热浴解释还需额外的源项、通量和观测映射，不能由递归本身推出。

## 38. 非线性位置映射的坐标约定

第37节中，若 $F:[0,1]\to[0,1]$ 是严格递增的 $C^2$ 微分同胚（$F'>0$），先使用无量纲位置 $\bar y=F(u)$。对标量场或后向解 $p$，令 $\bar v(\bar y,t)=p(F^{-1}(\bar y),t)$，则

$$
\partial_t\bar v
=D\left(F'(G(\bar y))^2\partial_{\bar y}^2\bar v
+F''(G(\bar y))\partial_{\bar y}\bar v\right),
\qquad G=F^{-1}.
$$

若物理位置为 $y=\ell\bar y$、物理时间为 $T=\eta t$，则同一式在物理坐标中应写成

$$
\partial_Tv
=\frac D\eta\left(
\ell^2F'(G(y/\ell))^2\partial_y^2v
+\ell F''(G(y/\ell))\partial_yv
\right).
$$

因此第37节的常系数解释只在 $F$ 已知且为恒等映射时成立；未知 $F$ 时，最多得到推前后的抽象 Green 核。这个坐标修正不改变无量纲谱的结论，却禁止把无量纲导数直接当作物理长度导数。

## 39. 逆问题病态性的显式总变差界

沿用第36节的记号。对固定整数 $q\in\mathbb N_0$，令 $A=\sqrt{S/D}$，取 $q+2$ 个不同点 $x_j$ 和系数 $c_j$，满足

$$
\sum_jc_jx_j^{2r}=0\quad(0\le r\le q),
\qquad \sum_j|c_j|=1,
$$

并定义

$$
\nu_\pm=\sum_j(|c_j|\pm c_j)\delta_{x_j}.
$$

由 $r=0$ 得 $\sum_jc_j=0$，故 $\nu_\pm$ 是概率律。沿用第36节的距离约定

$$
\operatorname{TV}(\mu,\nu)=\sup_B|\mu(B)-\nu(B)|
=\tfrac12|\mu-\nu|([0,1]),
$$

有 $\operatorname{TV}(\nu_+,\nu_-)=1$。对 $0\le s\le S$，令 $a=\sqrt{s/D}$，Taylor 展开与前 $q$ 阶矩抵消给出

$$
\left|\sum_jc_j\cosh(ax_j)\right|
\le \cosh(A)\frac{A^{2q+2}}{(2q+2)!},
$$

从而

$$
\|\mathcal A_S\nu_+-\mathcal A_S\nu_-\|_\infty
\le 2\cosh(A)\frac{A^{2q+2}}{(2q+2)!}
\longrightarrow0.
$$

所以即使输入律在总变差意义下保持固定距离，有限频段读出也可趋于相同；任何由有限频段一致误差控制总变差的统一连续模都不存在。这一结论仍不否定第36节在弱拓扑中的精确连续逆，只说明实验噪声下不能把拓扑注入性宣传成强范数稳定性。

## 追加锚（本行以下为增补区）

## 40. 非退化初态类中的联合弱稳定性

固定 $S>0$、$0<d_-\le d_+<\infty$ 和 $0<\beta\le1$，定义

$$
a_0(\nu)=\int_{[0,1]}\cos(\pi x/2)\,d\nu(x),
$$

以及允许的参数类

$$
\mathcal Q_\beta=\left\{(D,\nu):
D\in[d_-,d_+],\
\nu\in\mathcal P([0,1]),\
a_0(\nu)\ge\beta
\right\}.
$$

这里 $\beta$ 是预先给定的首模态投影下界，排除质量全部逼近吸收端的退化。对初态律取有界 Lipschitz 距离

$$
d_{\mathrm{BL}}(\mu,\nu)=
\sup_{\substack{\|f\|_\infty\le1\\\operatorname{Lip}(f)\le1}}
\left|\int f\,d\mu-\int f\,d\nu\right|,
$$

并对参数对取距离

$$
d_*\bigl((D,\nu),(\widetilde D,\widetilde\nu)\bigr)
=|D-\widetilde D|+d_{\mathrm{BL}}(\nu,\widetilde\nu).
$$

**定理 40.1（联合识别的统一弱连续模）。** 令

$$
\mathcal A_S(D,\nu)=\mathcal L_{\nu,D}\big|_{[0,S]}.
$$

在 $\mathcal Q_\beta$ 上存在非减函数 $\omega_\beta$，满足 $\omega_\beta(\varepsilon)\to0$ 当 $\varepsilon\downarrow0$，且

$$
\|\mathcal A_S(D,\nu)-\mathcal A_S(\widetilde D,\widetilde\nu)\|_\infty
\le\varepsilon
\quad\Longrightarrow\quad
d_*\bigl((D,\nu),(\widetilde D,\widetilde\nu)\bigr)
\le\omega_\beta(\varepsilon).
$$

**证明。** 首模态积分 $a_0$ 对初态弱收敛连续，故 $\mathcal Q_\beta$ 是紧参数空间中的闭集。变换核在 $[0,S]\times[0,1]\times[d_-,d_+]$ 上联合连续，所以 $\mathcal A_S$ 对 $d_*$ 连续，输出取一致范数。第35.1节保证其在 $\mathcal Q_\beta$ 上为单射。具体定义

$$
\omega_\beta(\varepsilon)=\sup\left\{d_*(q,\widetilde q):
q,\widetilde q\in\mathcal Q_\beta,\
\|\mathcal A_S(q)-\mathcal A_S(\widetilde q)\|_\infty\le\varepsilon
\right\}.
$$

若该上确界不趋于零，可取读出差趋于零而参数距离有正下界的一列参数对；紧性给出收敛子列，连续性使两个极限有相同曲线，单射使两个极限相同，与正下界矛盾。$\square$

**推论 40.2（有限噪声的可行集合）。** 对连续观测曲线 $g$，令

$$
\mathcal U_\varepsilon(g)=\left\{q\in\mathcal Q_\beta:
\|\mathcal A_S(q)-g\|_\infty\le\varepsilon
\right\}.
$$

若此集合非空，则任意两个可行参数的 $d_*$ 距离不超过 $\omega_\beta(2\varepsilon)$。这是整个固定参数类上的弱误差控制；它不给出 $\omega_\beta$ 的计算方法、幂率、总变差界或从有限频点恢复完整曲线的算法。集合为空表示观测与给定误差和参数类不相容，不能据此任意增大误差或改写初态条件。

**命题 40.3（退化附近的扩散尺度不稳定）。** 取 $D_1\ne D_2$ 以及

$$
\nu_\varepsilon=(1-\varepsilon)\delta_1+\varepsilon\delta_0,
\qquad 0<\varepsilon<1.
$$

每个初态均有内部质量，但

$$
\mathcal L_{\nu_\varepsilon,D}(s)
=1-\varepsilon+\varepsilon\,\operatorname{sech}\sqrt{s/D},
$$

因此

$$
\sup_{s\ge0}\left|
\mathcal L_{\nu_\varepsilon,D_1}(s)
-\mathcal L_{\nu_\varepsilon,D_2}(s)
\right|\le\varepsilon,
\qquad |D_1-D_2|>0.
$$

故在只要求 $\nu([0,1))>0$ 而没有统一非退化限制的参数类上，即使观测全部非负频率，也不存在由曲线一致误差趋零保证 $D$ 误差趋零的统一连续模。这个反例不否定每个固定非退化初态的精确联合识别；它说明精确识别与统一噪声稳定具有不同的量词。

## 41. 吸收端质量的有限频段不稳定性

**命题 41.1（弱初态误差不控制端点原子）。** 固定 $S,D>0$。令 $\nu_n=\delta_{1-1/n}$、$\nu=\delta_1$，$n\ge2$。则 $\nu_n\Rightarrow\nu$，并且

$$
\sup_{0\le s\le S}\left|\mathcal L_{\nu_n,D}(s)-1\right|
\le\frac{\sqrt{S/D}\,\tanh\sqrt{S/D}}{n}
\longrightarrow0,
$$

但 $\nu_n(\{1\})=0$、$\nu(\{1\})=1$。

**证明。** 令 $a=\sqrt{s/D}$。对核 $K_s(x)=\cosh(ax)/\cosh(a)$，有

$$
0\le\partial_xK_s(x)=\frac{a\sinh(ax)}{\cosh(a)}
\le a\tanh a.
$$

在 $[1-1/n,1]$ 上应用均值定理，并利用 $a\tanh a$ 随 $a\ge0$ 单调递增，即得一致界。端点质量由两个点质量的位置直接给出。$\square$

第34节的高频极限仍能精确识别端点原子，但在本例中不能交换 $n\to\infty$ 与 $s\to\infty$：

$$
\lim_{n\to\infty}\lim_{s\to\infty}\mathcal L_{\nu_n,D}(s)=0,
\qquad
\lim_{s\to\infty}\lim_{n\to\infty}\mathcal L_{\nu_n,D}(s)=1.
$$

因此第40节的弱误差控制不能被解释成端点原子质量的稳定恢复。端点质量、总变差与弱初态距离必须各按自己的读出精度和极限顺序处理。

## 追加锚（本行以下为增补区）

## 42. 连续速度权重的广义 Sturm–Liouville 极限

第19节给出了连续正速度权重的占用场。这里把其标量通过响应和谱结构单独闭合，并区分速度权重与原坐标中的扩散系数。

**定义 42.1（连续速度 Green 算子）。** 取 \(v\in C([0,1])\) 满足
\[
0<v_-\le v(u)\le v_+<\infty.
\]
在固定的反射—吸收连续模型中定义
\[
(\mathsf T_v f)(x)
 =\frac1D\int_0^1(1-\max(x,y))v(y)f(y)\,dy,
\qquad f\in C([0,1]).
\]
相应的加权 Hilbert 空间为 \(L^2([0,1],v(y)\,dy)\)。

**定理 42.2（加权预解式与广义谱）。** \(\mathsf T_v\) 是 \(L^2(v\,dy)\) 上的紧正自伴算子。其逆算子在相应定义域上为
\[
A_v=-D\,v^{-1}\frac{d^2}{dx^2},
\qquad
f'(0)=0,\quad f(1)=0.
\]
因此存在简单离散谱
\[
0<\lambda_0(v)<\lambda_1(v)<\cdots,\qquad
\lambda_n(v)\to\infty,
\]
其特征函数满足
\[
-D\psi_n''=\lambda_n(v)v\psi_n,\qquad
\psi_n'(0)=0,\quad \psi_n(1)=0,
\]
并在 \(L^2(v\,dx)\) 中构成完备系。对任意 \(s\ge0\)，函数
\[
h_{v,s}(x)=\frac{c_v(s,x)}{c_v(s,1)}
\]
是方程
\[
D c_v''=s\,v\,c_v,\qquad c_v(s,0)=1,\quad
\partial_xc_v(s,0)=0
\]
所确定的唯一解，并满足
\[
h_{v,s}+s\mathsf T_vh_{v,s}=1,\qquad
D h_{v,s}''=s\,v\,h_{v,s},\quad
h_{v,s}'(0)=0,\quad h_{v,s}(1)=1.
\]
当 \(v\equiv1\) 时，\(\lambda_n(v)=D(n+\tfrac12)^2\pi^2\)，且
\(h_{v,s}(x)=\cosh(x\sqrt{s/D})/\cosh\sqrt{s/D}\)。

**证明。** 对 \(f,g\in H^1([0,1])\) 且 \(f(1)=g(1)=0\)，闭二次型
\[
\mathfrak a(f,g)=D\int_0^1 f'(x)g'(x)\,dx
\]
在 \(L^2(v\,dx)\) 上给出正自伴算子；一维分离边界条件使特征值简单，紧嵌入给出离散谱。对 \(u=\mathsf T_vf\)，核的二阶分布导数满足
\[
-Du''=vf,\qquad u'(0)=0,\quad u(1)=0,
\]
所以 \(A_v\mathsf T_v=I\) 且 \(\mathsf T_vA_v=I\) 在相应定义域上成立。有限链的 Feynman–Kac 首步方程在缩放后为
\[
h_{j,v,s}+\gamma_j(s)T_{j,v}h_{j,v,s}=1,\qquad
\gamma_j(s)=\frac{e^{s\epsilon_j}-1}{\epsilon_j}.
\]
离散核的一致收敛和 \(v\) 的一致连续性给出 \(T_{j,v}\to \mathsf T_v\)，从而得到积分方程和其等价的边值问题。初值与边界条件唯一确定 \(c_v\)，故整列收敛到 \(h_{v,s}\)。恒等速度时直接解常系数方程即得余弦谱和双曲余弦核。$\square$

**推论 42.3（矩递推、Fredholm 总质量与速度识别）。** 令 \(M_{p,v}(x)\) 为从 \(x\) 出发的 \(p\) 阶通过时间矩，且 \(M_{0,v}=1\)。则
\[
M_{p,v}=p!\,\mathsf T_v^p1,
\]
并满足
\[
-DM_{p,v}''=p\,v\,M_{p-1,v},\qquad
M_{p,v}'(0)=0,\quad M_{p,v}(1)=0.
\]
特别地，\(m_v=M_{1,v}=\mathsf T_v1\) 给出
\[
-Dm_v''=v,\qquad m_v'(0)=0,\quad m_v(1)=0.
\]
所以若 \(D\) 与完整均值剖面 \(m_v\) 已知，则
\[
v(x)=-D\,m_v''(x)
\]
在分布意义下唯一恢复；单一起点的均值或总质量只给有限个线性约束，不能识别一般连续 \(v\)。

令 \(\mathcal M_v:=\mu^{(v)}([0,1])=\int_0^1 v(u)\Lambda(u)\,du\)。对任意 \(S\ge0\)，Fredholm 恒等式为
\[
\det\nolimits_F(I+S \mathsf T_v)
 =c_v(S,1)
 =\prod_{n\ge0}\left(1+\frac S{\lambda_n(v)}\right).
\]
因此极限总占用质量 \(\mathcal M_v\) 的变换为
\[
\mathbb E e^{-S\mathcal M_v}
 =c_v(S,1)^{-1}
 =h_{v,S}(0).
\]
这把总质量读出、广义谱和带权 Green 算子连接起来，但不把任意有限个谱值当成速度的唯一编码。

**命题 42.4（速度扰动的定量连续性）。** 若 \(v,w\) 满足同一正下界，记
\(\eta=\|v-w\|_\infty\)，则
\[
\|\mathsf T_v-T_w\|_{\infty\to\infty}
 \le \frac{\eta}{2D}.
\]
在固定 \(S\) 的有界区间上，存在只依赖 \(S,D,v_-,v_+\) 的常数 \(C\)，使
\[
\|h_{v,S}-h_{w,S}\|_\infty
 +|c_v(S,1)-c_w(S,1)|
 \le C\eta.
\]
由带权 Rayleigh 商，谱在 \(v\) 的一致扰动下连续；这只提供连续模，不给出从单一总质量变换反演 \(v\) 的算法或总变差稳定性。

**证明。** 核的行积分满足
\[
\sup_x\int_0^1\frac{1-\max(x,y)}D\,dy\le\frac1{2D},
\]
故第一式成立。积分方程的 resolvent 恒等式和正下界给出 \(h\) 的一致估计；基本解方程的 Gronwall 估计给出 \(c_v\) 的第二项。谱连续性由同一闭二次型和权函数的有界正扰动得到。$\square$

\(v\) 在这里是数学上的局部停留权或 speed measure。它只有在额外规定物理状态空间、能量泛函和观测映射后才可作介质参数；广义 Sturm–Liouville 谱和 Fredholm 形式本身不推出温度、热流、量子输运或经验普适性。离散 FIB 词只提供长度、数量及嵌入序列，插值函数 \(v\)、边界和时钟仍是外加模型输入。

## 43. 同轨多探针的联合生成泛函与共同实现边界

**定义 43.1（同轨与边缘耦合）。** 沿用前文固定单位速度、左反射右吸收、初态 \(0\) 的逐字链。取互异探针坐标 \(0\le u_1<\cdots<u_m<1\)，令
\[
a_{j,k}=\iota_j(u_k),\qquad
V_{j,k}=\sum_{n<\tau_j}{\bf1}_{\{X_n=a_{j,k}\}},\qquad
\ell_{j,k}=h_jV_{j,k}.
\]
同轨实现指全部 \(V_{j,k}\) 从同一条 \(X^{(j)}\) 与同一停时 \(\tau_j\) 读取；边缘耦合只要求每个坐标具有给定的单探针边缘律。记
\[
Q_j=(q_{\max(a_{j,k},a_{j,\ell})})_{k,\ell},
\qquad
C_{k\ell}=\frac{1-\max(u_k,u_\ell)}D.
\]

**定理 43.2（同轨有限多点 PGF 与缩放 Laplace 律）。** 对暂态上互异的 \(a_1<\cdots<a_m\) 及 \(0<z_k\le1\)，令 \(Z=\operatorname{diag}(z_1,\ldots,z_m)\)。同轨占用满足
\[
\mathbb E_0\prod_{k=1}^m z_k^{V_{a_k}}
 =\det\!\left(I_m+Q_j\,\operatorname{diag}(z_1^{-1}-1,\ldots,z_m^{-1}-1)\right)^{-1}
 =\frac{\det Z}{\det\!\left(Z+Q_j(I_m-Z)\right)}.
\]
当某个 \(z_k=0\) 时取右侧的 \(z_k\downarrow0\) 极限；在暂态探针上占用至少一次，故单点极限为零。重复坐标必须先合并其势；吸收点坐标的占用恒为零。令 \(s_k\ge0\)、\(z_k=e^{-h_js_k}\)，则
\[
\mathbb E_0e^{-\sum_k s_k\ell_{j,k}}
 =\det\!\left(I_m+C_j\operatorname{diag}(\gamma_j(s_k))\right)^{-1},
\quad
C_j=h_jQ_j,\quad
\gamma_j(s)=\frac{e^{h_js}-1}{h_j}.
\]
由 Green 核的一致收敛，固定 \(m\) 时
\[
\mathbb E_0e^{-\sum_k s_k\ell_{j,k}}
 \longrightarrow
 \det\!\left(I_m+C\,\operatorname{diag}(s_1,\ldots,s_m)\right)^{-1}.
\tag{43.1}
\]
右侧是同一极限场的联合变换，不能换成各单点变换的乘积。

**证明。** 令 \(d_k=z_k^{-1}-1\)。离散 Feynman–Kac 方程在探针行的消元给出 \(\det(I_m+Q_j\operatorname{diag}d)^{-1}\)；利用
\[
\left(Z+Q_j(I_m-Z)\right)Z^{-1}
=I_m+Q_j(Z^{-1}-I_m)
\]
得到等价的第二式。取 \(z_k=e^{-h_js_k}\) 后 \(d_k=e^{h_js_k}-1\)，再用 \(h_jQ_j\to C\)、\(\gamma_j(s)\to s\) 得 (43.1)。对 (43.1) 的矩生成函数在零点邻域展开迹级数，取混合导数即得 (43.2)。$\square$

**推论 43.3（混合累积量与非高斯性）。** 令 \(\Lambda_k=\Lambda(u_k)\)，在 \(T=\operatorname{diag}(t_k)\) 足够小时，
\[
\log\mathbb E e^{\sum_k t_k\Lambda_k}
 =-\log\det(I_m-CT)
 =\sum_{r\ge1}\frac1r\operatorname{tr}((CT)^r).
\]
任取指标 \(i_1,\ldots,i_r\)，有
\[
\operatorname{cum}(\Lambda_{i_1},\ldots,\Lambda_{i_r})
 =\frac1r\sum_{\pi\in S_r}
 \prod_{\nu=1}^{r} C_{i_{\pi(\nu)},i_{\pi(\nu+1)}},
 \qquad i_{\pi(r+1)}=i_{\pi(1)}.
\tag{43.2}
\]
当所有 \(u_k<1\) 时 \(C_{k\ell}>0\)，故这些混合累积量为正。特别地
\[
\operatorname{Cov}(\Lambda(u),\Lambda(v))
 =C(u,v)^2
 =\frac{(1-\max(u,v))^2}{D^2},
\]
而 \(0\le u<v<w<1\) 时
\[
\operatorname{cum}(\Lambda(u),\Lambda(v),\Lambda(w))
 =2C(u,v)C(v,w)C(w,u)>0.
\]
因此有限维占用场不是非退化高斯场，单点指数边缘也不意味着多点独立。

**证明。** 离散 Feynman–Kac 方程在探针行的消元给出第一式；\(G(0,a)=G(a,a)=q_a\)、\(G(a,b)=q_{\max(a,b)}\) 使矩阵为 \(Q_j\)。取 \(z_k=e^{-h_js_k}\) 并用 \(h_jQ_j\to C\)、\(\gamma_j(s)\to s\) 得 (43.1)。对 (43.1) 的矩生成函数在零点邻域展开迹级数，取混合导数即得 (43.2)。$\square$

**定理 43.4（同轨连续占用泛函）。** 对 \(s_r\ge0\) 及 \(f_r\in C([0,1],[0,\infty))\)（\(1\le r\le p\)），令
\[
\mathcal A_j(f)=\epsilon_j\sum_{n<\tau_j}f(X_n/L_j),
\qquad
f=\sum_{r=1}^p s_r f_r.
\]
则
\[
\mathbb E_0\exp\!\left(-\sum_{r=1}^p s_r\mathcal A_j(f_r)\right)
 \longrightarrow
 \det\nolimits_F(I+\mathsf C M_f)^{-1}.
\tag{43.3}
\]
这就是同轨占用随机测度的联合生成泛函；其混合累积量由核 \(\mathsf C(u,v)=(1-\max(u,v))/D\) 的环积分给出。该式只涉及连续测试函数积分，不宣称占用密度样本路径在 \(C([0,1])\) 中一致收敛。

**定理 43.5（同边缘不确定联合律）。** 若第 \(k\) 个探针从独立副本读取，则边缘极限仍为均值 \(\kappa(u_k)\) 的指数律，而联合变换为
\[
\prod_{k=1}^m(1+\kappa(u_k)s_k)^{-1}.
\tag{43.4}
\]
同轨实现却给出 (43.1) 的非零混合累积量。更一般地，指定各坐标边缘只指定一个 coupling 纤维；没有共同历史、独立性或其他 coupling 合同，边缘信息不能决定联合变换。

**物理类比边界。** \(\mathsf C\) 是声明的反射—吸收连续模型 Green 核，(43.3) 是该模型的占用随机测度生成泛函；“共同噪声”“同一粒子历史”只是 coupling 的类比。FIB 递归本身不选择概率律、阻抗、边界、时钟、初态或跨探针 coupling，因此单点指数边缘不能推出物理相关性、热流、温度、熵产生或普适性。

## 44. Green 响应与涨落的同源条件

**定义 44.1（有限硬核 Gibbs 场与静态响应）。** 设 \(G=(V,E)\) 是有限简单图，\(\mathcal I_G(V)\) 为其独立集族。给定严格正的顶点活动
\[
\lambda_v=e^{\theta_v}>0,\qquad v\in V,
\]
定义
\[
Z(\theta)=\sum_{S\in\mathcal I_G(V)}
 \exp\!\left(\sum_{v\in S}\theta_v\right),
\qquad
p_\theta(S)=\frac{\exp(\sum_{v\in S}\theta_v)}{Z(\theta)}.
\]
令
\[
\eta_v(S)={\bf1}_{\{v\in S\}},\qquad
N_f(S)=\sum_{v\in V}f_v\eta_v(S).
\]
对任意随机变量 \(F\) 写 \(\langle F\rangle_\theta\) 和
\(\operatorname{Cov}_\theta(F,H)\) 表示在 \(p_\theta\) 下的期望与协方差。对场 \(h=(h_v)_{v\in V}\)，令
\[
N_h=\sum_{v\in V}h_v\eta_v.
\]
沿活动的对数方向定义静态响应
\[
\mathcal R^{\mathrm{stat}}_{F,h}(\theta)
 =
 \left.\frac{d}{d\varepsilon}
 \langle F\rangle_{\theta+\varepsilon h}\right|_{\varepsilon=0}.
\]

定义顶点涨落核
\[
\mathcal C_\theta(u,v)
 =\operatorname{Cov}_\theta(\eta_u,\eta_v).
\]
它诱导有限维算子
\[
(\mathcal C_\theta h)_v
 =\sum_{u\in V}\mathcal C_\theta(v,u)h_u.
\]
这里的 \(\mathcal C_\theta\) 首先是协方差核或静态易感核。只有在另行给出可逆线性算子 \(L_\theta\)、源算子 \(Q_\theta\) 以及
\[
L_\theta\mathcal C_\theta=Q_\theta
\]
时，才能把它写成 Green 表示
\[
\mathcal C_\theta=L_\theta^{-1}Q_\theta.
\]
若 \(Q_\theta=I\)，才得到通常意义的 \(L_\theta^{-1}\) Green 算子。

**定理 44.2（有限硬核场的精确涨落—响应恒等式）。** 在定义 44.1 的条件下，对任意有限构型函数 \(F\) 与场 \(h\)，有
\[
\boxed{
\mathcal R^{\mathrm{stat}}_{F,h}(\theta)
 =
\operatorname{Cov}_\theta(F,N_h).
}
\]
特别地，对 \(F=N_f\)，
\[
\left.\frac{d}{d\varepsilon}
 \langle N_f\rangle_{\theta+\varepsilon h}
\right|_{\varepsilon=0}
 =
\sum_{u,v\in V}f_v\,
\mathcal C_\theta(v,u)h_u.
\]
逐点取 \(f={\bf1}_{\{v\}}\) 得
\[
\boxed{
\frac{\partial}{\partial\theta_u}
 \langle\eta_v\rangle_\theta
 =
\mathcal C_\theta(v,u).
}
\]
因此
\[
\nabla_\theta^2\log Z(\theta)=\mathcal C_\theta,
\qquad
h^{\mathsf T}\mathcal C_\theta h
 =\operatorname{Var}_\theta(N_h)\ge0.
\]
协方差核作为矩阵是对称半正定的，但其非对角元不必逐项非负。

若所有活动相同，即 \(\theta_v=\log\lambda\)，并取 \(h_v=1\)，则
\[
\lambda\,\frac{d}{d\lambda}
 \mathbb E_{V,\lambda}|S|
 =
\operatorname{Var}_{V,\lambda}(|S|),
\]
这是有限 Gibbs 场中活动导数—方差恒等式的顶点分辨率形式。

**证明。** 直接写出
\[
\langle F\rangle_{\theta+\varepsilon h}
 =
\frac{\sum_{S\in\mathcal I_G(V)}
 F(S)e^{\sum_{v\in S}\theta_v}
 e^{\varepsilon N_h(S)}}
 {\sum_{S\in\mathcal I_G(V)}
 e^{\sum_{v\in S}\theta_v}
 e^{\varepsilon N_h(S)}}.
\]
有限和逐项可导，且
\[
\left.\frac{d}{d\varepsilon}
e^{\varepsilon N_h(S)}\right|_{\varepsilon=0}
=N_h(S).
\]
商法则给出
\[
\mathcal R^{\mathrm{stat}}_{F,h}
 =
\langle FN_h\rangle_\theta
 -\langle F\rangle_\theta\langle N_h\rangle_\theta.
\]
对 \(F=\eta_v\) 得顶点公式；对
\(\partial_{\theta_u}\partial_{\theta_v}\log Z\) 作同样计算得到协方差 Hessian。证毕。

**定义 44.3（固定动力学下的 Green 响应）。** 令
\(\Omega=\mathcal I_G(V)\) 为有限状态空间，\((P_t)_{t\ge0}\) 为保持 \(p_\theta\) 的 Markov 半群，生成元记为 \(\mathscr L\)。固定动力学，只改变初始 Gibbs 场。对 \(z>0\) 定义
\[
\mathscr G_z
 =\int_0^\infty e^{-zt}P_t\,dt
 =(zI-\mathscr L)^{-1}.
\]
对观测量 \(F\) 和场 \(h\)，定义
\[
\mathcal R_{F,h}(t)
 =
\left.\frac{d}{d\varepsilon}
 \mathbb E_{\theta+\varepsilon h}
 [F(X_t)]\right|_{\varepsilon=0}.
\]
此处 \(X_0\sim p_{\theta+\varepsilon h}\)，而 \(P_t\) 不随 \(\varepsilon\) 改变。

**定理 44.4（平衡初始扰动的动态 Green—涨落关系）。** 在定义 44.3 的条件下，
\[
\boxed{
\mathcal R_{F,h}(t)
 =
\operatorname{Cov}_\theta
 \bigl(F(X_t),N_h(X_0)\bigr).
}
\]
若以
\[
\langle A,B\rangle_\theta
 =\sum_{S\in\Omega}p_\theta(S)A(S)B(S),
\qquad
\widetilde N_h=N_h-\langle N_h\rangle_\theta,
\]
记 \(\mathscr G_z\) 的积分核表示，则
\[
\int_0^\infty e^{-zt}\mathcal R_{F,h}(t)\,dt
 =
\left\langle
 \mathscr G_zF,\widetilde N_h
\right\rangle_\theta.
\]
若半群满足详细平衡
\[
p_\theta(x)P_t(x,y)=p_\theta(y)P_t(y,x),
\]
则 \(\mathscr G_z\) 在该内积下自伴，从而
\[
\boxed{
\int_0^\infty e^{-zt}\mathcal R_{F,h}(t)\,dt
 =
\left\langle
 F,\mathscr G_z\widetilde N_h
\right\rangle_\theta.
}
\]
因此，在共同 Gibbs 状态、固定 Markov 动力学以及详细平衡条件下，响应可以严格写成 Green resolvent 作用于涨落场后的配对。这时“涨落—响应”与“Green 响应”两个名称具有同一数学等式的依据。

**证明。** 由 Markov 半群定义，
\[
\mathbb E_{\theta+\varepsilon h}[F(X_t)]
 =
\left\langle P_tF\right\rangle_{\theta+\varepsilon h}.
\]
应用定理44.2，
\[
\mathcal R_{F,h}(t)
 =
\operatorname{Cov}_\theta(P_tF,N_h)
 =
\operatorname{Cov}_\theta(F(X_t),N_h(X_0)).
\]
对 \(t\) 积分并使用
\[
\mathscr G_zF=\int_0^\infty e^{-zt}P_tF\,dt
\]
即得第一种 resolvent 配对。详细平衡使 \(P_t\) 及其积分 \(\mathscr G_z\) 自伴，得到第二种写法。证毕。

**命题 44.5（动态扰动的额外义务）。** 若活动扰动同时改变生成元
\[
\mathscr L_\varepsilon
 =\mathscr L+\varepsilon\dot{\mathscr L}_h+o(\varepsilon),
\]
则固定初始分布时
\[
\left.\frac{d}{d\varepsilon}
 P_t^{(\varepsilon)}F\right|_{\varepsilon=0}
 =
\int_0^t
 P_{t-s}\dot{\mathscr L}_hP_sF\,ds.
\]
若初始 Gibbs 分布也同时改变，还必须加上
\[
\operatorname{Cov}_\theta(P_tF,N_h)
\]
这一项。除非另行证明
\(\dot{\mathscr L}_h\) 与 \(N_h\) 满足相应的局部详细平衡或时间反演关系，否则不能把上式简化为
\[
\operatorname{Cov}_\theta(F(X_t),N_h(X_0)).
\]

**证明。** 有限维矩阵指数的 Duhamel 恒等式给出
\[
\left.\frac{d}{d\varepsilon}
 e^{t\mathscr L_\varepsilon}\right|_{\varepsilon=0}
 =
\int_0^t
 e^{(t-s)\mathscr L}
 \dot{\mathscr L}_h
 e^{s\mathscr L}\,ds.
\]
初始分布的导数由定理44.2给出。两项来源不同，不能在未给出生成元—场对应时合并。证毕。

**结论范围。** 上述活动导数、有限图协方差和固定半群的 resolvent 配对，均属于明确 Gibbs 构型与动力学假设下的数学结果。它们不自动给出时间动力学、热流、耗散、温度、KMS 条件、量子对易子或物理 Green 函数。复活动力 \(z\) 位于零自由域时，\(Z(z)\) 的导数和 Hessian 仍可作为解析响应研究，但没有正概率测度，不能把相应复数二阶导数称为概率方差。活动为零时，对数活动坐标不存在，只能使用未缩放的多项式导数。

因此，只有在以下条件同时明确时，才可使用“涨落—响应”的数学名称：响应参数属于同一归一化 Gibbs 族；涨落和响应取自同一共同概率源；若涉及时间，则给出具体半群或生成元；若称某核为 Green 算子，则另行给出其逆算子或 resolvent 方程；若扰动动力学，则证明生成元导数与扰动场的对应。没有这些条件时，应分别称为活动导数、协方差 Hessian、静态易感性或半群相关函数，不把数学类比外推成物理普遍律。

## 45. 坐标规范变换与标量吸收读出的联合不可识别性

第38节给出了非线性位置映射后的微分算子，但还需要把这种变换对完整读出的影响写清楚。下面的等价性是路径级的，因此比只比较某个低频系数更强。

**定义 45.1（坐标推前的吸收模型）。** 令 \(U\) 是区间 \([0,1]\) 上生成元为 \(D\partial_u^2\) 的左端反射、右端吸收扩散，\(D>0\)，吸收时刻记为 \(\tau=\inf\{t:U_t=1\}\)。取严格递增的 \(C^2\) 微分同胚 \(F:[0,1]\to[0,1]\)，满足 \(F(0)=0\)、\(F(1)=1\)，并令 \(Y_t=F(U_t)\)。写 \(G=F^{-1}\)。在内部坐标 \(y\in(0,1)\) 上，\(Y\) 的后向算子为

$$
(\mathcal L_F f)(y)
=D\left(F'(G(y))^2 f''(y)+F''(G(y))f'(y)\right),
$$

其反射边界条件为 \(f'(0)=0\)，吸收端为 \(y=1\)。对初态律 \(\nu\) 记 \(\nu^F=F_\#\nu\)，并定义标量边界读出

$$
H_{F,\nu}(s)=\mathbb E_{\nu^F}\!\left[e^{-s\tau_F}\right],
\qquad s\ge0,
$$

其中 \(\tau_F\) 是 \(Y\) 到达 \(1\) 的时刻。

**定理 45.2（坐标推前保持完整吸收曲线）。** 对每个 \(s\ge0\)，有

$$
H_{F,\nu}(s)=H_{\mathrm{id},\nu}(s)
=\int_{[0,1]}\frac{\cosh(x\sqrt{s/D})}{\cosh\sqrt{s/D}}\,d\nu(x).
$$

特别地，若初态固定为反射端 \(\nu=\delta_0\)，则所有满足上述条件的 \(F\) 都给出同一曲线

$$
H_{F,\delta_0}(s)=\operatorname{sech}\sqrt{s/D},
$$

但当 \(F\) 非恒等时，\(\mathcal L_F\) 的扩散系数 \(D(F'\circ G)^2\) 与漂移系数 \(D(F''\circ G)\) 一般随 \(y\) 改变。

**证明。** 由定义 \(Y_t=F(U_t)\) 且 \(F(1)=1\)，两条路径在同一时刻到达各自吸收端：

$$
\tau_F=\inf\{t:Y_t=1\}=\inf\{t:U_t=1\}=\tau
$$

逐样本成立。初态 \(Y_0\) 的律是 \(F_\#\nu\)，所以取期望立即得到 \(H_{F,\nu}(s)=\mathbb E_\nu[e^{-s\tau}]\)。恒等坐标下的后向边值问题为 \(Dh''=sh\)、\(h'(0)=0\)、\(h(1)=1\)，其解为

$$
h(x,s)=\frac{\cosh(x\sqrt{s/D})}{\cosh\sqrt{s/D}}.
$$

这给出所列积分式。对算子公式，只需对 \(f(F(u))\) 作两次链式法则：

$$
D\partial_u^2(f\circ F)(u)
=D\left(F'(u)^2 f''(F(u))+F''(u)f'(F(u))\right),
$$

再令 \(u=G(y)\)。反射条件由 \(\partial_u(f\circ F)(0)=F'(0)f'(0)\) 得到；\(F'(0)>0\)，故等价于 \(f'(0)=0\)。$\square$

**推论 45.3（可识别对象是坐标等价类）。** 只给出单一起点的完整标量曲线 \(H(s)\)，即使 \(s\ge0\) 的连续曲线无噪声可得，也不能在允许上述 \(C^2\) 坐标推前的模型类中唯一恢复空间依赖的扩散系数和漂移系数。至少所有

$$
\left(D(F'\circ G)^2,\;D(F''\circ G),\;\delta_0\right)
$$

都属于同一读出等价类。要打破此等价性，必须额外固定物理坐标、限制算子为已知无漂移的子类，或加入内部位置探针与其观测映射；增加频率范围本身不能打破路径级等价。

这里的“规范”是数学上的坐标选择，不是递归内生的物理对称性。若实验另行规定物理位置、局部通量或速度密度，必须先证明这些读出在 \(F\) 下如何变换；否则不能把同一 \(H(s)\) 宣称为同一物理扩散介质。

## 46. 分段占用势的有序半群与有限维路径律

第43节处理同一时刻的多探针联合占用；若势随时间分段改变，联合变换还保留时间顺序，不能只由各段的单段变换相乘得到。

**定义 46.1（分段势与杀死半群）。** 沿用固定单位速度、左反射右吸收的 FIB 切链，取
\[
\epsilon_j=\frac{\delta}{N_j^2},\qquad
Z_j(t)=\frac{X_{\lfloor t/\epsilon_j\rfloor}}{L_j}.
\]
令 \(0=t_0<t_1<\cdots<t_m=T\)，\(\Delta t_r=t_r-t_{r-1}\)，并取连续非负势 \(f_r\) 与终端测试函数 \(g\)，满足 \(f_r(1)=g(1)=0\)。连续极限中的 Dirichlet—Neumann 算子记为
\[
H=-D\partial_x^2,\qquad
u'(0)=0,\quad u(1)=0,
\]
并写
\[
S_f(t)=e^{-t(H+M_f)}.
\]

**定理 46.2（离散 Feynman–Kac 组合的连续极限）。** 在定义12.1的单位速度、时钟和初态收敛假设下，令
\[
n_{j,r}=\left\lfloor\frac{t_r}{\epsilon_j}\right\rfloor
-\left\lfloor\frac{t_{r-1}}{\epsilon_j}\right\rfloor,\qquad
D_{j,r}=\operatorname{diag}\!\left(
e^{-\epsilon_jf_r(i/L_j)}\right),
\]
以及 \(Q_{j,r}=D_{j,r}K_j\)，其中吸收后的转移仍由杀死核 \(K_j\) 给出。若 \(i_j/L_j\to x\)，且 \(g_j\) 是 \(g\) 的格点嵌入，则
\[
\begin{aligned}
&\mathbb E_{i_j}\!\left[
\exp\!\left\{-\sum_{r=1}^m\epsilon_j
\sum_{n=n_{j,1}+\cdots+n_{j,r-1}}^{n_{j,1}+\cdots+n_{j,r}-1}
f_r(X_n/L_j)\right\}
g_j(X_{\lfloor T/\epsilon_j\rfloor})
\right]\\
&\hspace{2cm}=
\bigl[Q_{j,1}^{\,n_{j,1}}\cdots
Q_{j,m}^{\,n_{j,m}}g_j\bigr](i_j)\\
&\hspace{2cm}\longrightarrow
\bigl[S_{f_1}(\Delta t_1)\cdots
S_{f_m}(\Delta t_m)g\bigr](x).
\end{aligned}
\tag{46.1}
\]
算子乘积按时间从左到右排列；一般 \(S_{f_r}\) 不交换，因此分段势不能被替换成只依赖各段无序集合的表达式。

**证明。** 每个 \(Q_{j,r}\) 在一步转移前乘上当前格点的势因子，逐步条件期望给出离散 Feynman–Kac 等式。将杀死核 \(K_j\) 扩充为命中 \(1\) 后保持在 \(1\) 的完整核 \(\widehat K_j\)；由于 \(f_r(1)=g(1)=0\)，完整路径与杀死路径在该表达式上的取值一致。定理12.3和定理12.4给出
\[
Z_j\Longrightarrow Z
\]
于连续路径拓扑，并且阶梯路径的分段求和与对应时间积分之差由连续性模和 \(\epsilon_j\) 的端点误差控制而趋于零。于是
\[
\omega\longmapsto
\exp\!\left(-\sum_{r=1}^m\int_{t_{r-1}}^{t_r}f_r(\omega(s))\,ds\right)g(\omega(T))
\]
是有界连续路径泛函，连续映射定理给出 (46.1) 的极限。极限的 Markov 性把该泛函写成有序半群乘积。这里段数 \(m\) 固定；不允许 \(m=m(j)\) 随链长增长。$\square$

**推论 46.3（有限维路径律的有序插入公式）。** 取 \(0<t_1<\cdots<t_q\le T\) 和有界连续状态测试函数 \(\phi_\ell\)，并令 \(M_{\phi_\ell}\) 为乘法算子。对存活至 \(T\) 的路径，有
\[
\mathbb E_x\!\left[
\prod_{\ell=1}^{q}\phi_\ell(Z(t_\ell));\tau>T
\right]
=
\left[
S(t_1)M_{\phi_1}S(t_2-t_1)M_{\phi_2}\cdots
S(t_q-t_{q-1})M_{\phi_q}S(T-t_q)1
\right](x).
\tag{46.2}
\]
离散链有完全相同的 \(K_j^{n}D_{j,\phi}\) 插入式。分离类测试函数的这些变换收敛给出有限维分布收敛；它不等于 \(Z_j\) 在路径空间中的弱收敛，后者仍需另行证明紧性。若测试函数在吸收端不为零，必须把吸收状态保留在状态空间并使用含边界状态的半群，不能直接套用 Dirichlet 杀死半群。

若采用第42节的速度权重，则把 \(H\) 换为
\[
A_v=-D\,v^{-1}\partial_x^2
\quad\text{于 }L^2(v\,dx),
\qquad
S_{f,v}(t)=e^{-t(A_v+M_f)}.
\]
时间有序性和有限维公式仍成立，但离散行缩放与速度权重的路径收敛必须另行建立，不能把单位速度结论直接冒充为速度扩展。

这里的 \(f_r\) 是数学占用势或 Feynman–Kac 权；它不自动表示温度、能量或外场。\(H\) 是声明模型的杀死扩散算子，不是已识别的物理 Hamiltonian。有限维变换收敛不提供跨 \(j\) 的共同样本耦合、逐样本收敛、命中时刻联合收敛或物理热流结论。

## 47. 吸收链的路径比值、反向协议与有限时域涨落恒等式

**定义 47.1（有限时域正向与反向路径）。** 固定 FIB 词 \(W_j=s_0\cdots s_{L-1}\)，令
\[
c_i=\frac{\theta}{r_{s_i}}\in(0,1/2],
\]
并取定义5.1的有限状态核 \(K\) 与正向初态 \(\rho_F\)。在时域 \(n\) 内，正向路径 \(\omega=(x_0,\ldots,x_n)\) 的概率为
\[
P_F^n(\omega)=\rho_F(x_0)\prod_{k=0}^{n-1}K(x_k,x_{k+1}).
\]
取反向初态 \(\rho_R\) 和核 \(R\)。令 \(\Omega_n\) 为正向路径的正质量集合，并要求反向过程在 \(\Omega_n^\leftarrow\) 上有正质量。对 \(\omega^\leftarrow=(x_n,\ldots,x_0)\) 定义
\[
P_R^n(\omega^\leftarrow)
=\rho_R(x_n)\prod_{k=0}^{n-1}R(x_{k+1},x_k),
\]
以及路径对数比
\[
\Sigma_F(\omega)=
\log\frac{P_F^n(\omega)}{P_R^n(\omega^\leftarrow)}.
\tag{47.1}
\]
若反向过程在全部路径上还有 \(\Omega_n^\leftarrow\) 之外的质量，则记
\[
\chi_n(\omega^\leftarrow)
={\bf1}_{\Omega_n^\leftarrow}(\omega^\leftarrow).
\]
只有在反向过程被限制或条件化到 \(\Omega_n^\leftarrow\) 时，\(\chi_n\) 才恒等于一。

**定理 47.2（路径反演恒等式）。** 在有限时域且每条正向支撑路径在反向测度下有正质量的条件下，对任意路径函数 \(F\)，有
\[
\mathbb E_F[F(\Sigma_F)]
=
\mathbb E_R\!\left[
e^{-\Sigma_R}\,
F(-\Sigma_R)\,
\chi_n
\right],
\tag{47.2}
\]
其中 \(\Sigma_R(\omega^\leftarrow)=-\Sigma_F(\omega)\) 是同一对路径的反向对数比。若将反向路径测度条件化到 \(\Omega_n^\leftarrow\)，则在 (47.1) 中同步把 \(P_R^n\) 换成
\[
P_{R,\mathrm{cond}}^n(\cdot)=P_R^n(\cdot\mid\Omega_n^\leftarrow)
\]
并用这个条件测度重新定义 \(\Sigma_F\)；对该重新定义的对数比才有
\[
\mathbb E_F e^{-\Sigma_F}=1,
\qquad
\mathbb E_F[\Sigma_F]
 =D_{\mathrm{KL}}\!\left(P_F^n\,\middle\|\,P_{R,\mathrm{cond}}^n\circ\mathrm{rev}\right)\ge0.
\tag{47.3}
\]
未条件化时，正确的积分式为
\[
\mathbb E_F e^{-\Sigma_F}
=P_R^n(\Omega_n^\leftarrow),
\]
而不是自动等于一。

**证明。** 对每一条 \(\omega\in\Omega_n\)，(47.1) 给出
\[
P_F^n(\omega)
=e^{\Sigma_F(\omega)}P_R^n(\omega^\leftarrow).
\]
将其乘以 \(F(\Sigma_F)e^{-\Sigma_F}\)，对可数路径求和并作双射 \(\omega\leftrightarrow\omega^\leftarrow\)，得到 (47.2)。若反向支撑恰为 \(\Omega_n^\leftarrow\)，指标为一，取 \(F\equiv1\) 得积分式；取对数比的期望即为相对熵，故非负。$\square$

**推论 47.3（对称内部边的抵消）。** 若在暂态内部每条无向边满足
\[
K(i,i+1)=K(i+1,i)
\]
且反向核在这些边及自环上逐项取相同概率，则路径比 (47.1) 的内部跳跃项和内部自环项全部抵消。剩余项只来自初态/终点律以及反射端、吸收端的边界协议。若初态律 \(\rho_F,\rho_R\) 与反向边界协议均不依赖整词（除通过最后一条标记为 \(s_{L-1}\) 的边界参数 \(c_{L-1}=\theta/r_{s_{L-1}}\) 外），FIB 词的奇偶性才只会通过该参数进入这些边界项；若边界反向协议改变，必须按该协议重新计算，不能把内部抵消外推成全路径熵产生为零。

**长度混合边界。** 本节先固定时域 \(n\)；若改用随机首达长度，必须另给正向长度律、反向桥的长度律及每个长度的条件路径协议。未声明这些数据时，不能把固定 \(n\) 的积分恒等式提升为首达时间的全局涨落式。

**物理类比边界。** \(\Sigma_F\) 是两个已声明有限路径测度的 log-likelihood ratio，(47.2)–(47.3) 是概率测度的路径反演与相对熵恒等式。它们不自动构成热力学第二定律、熵产生或物理 fluctuation theorem。FIB 递归只决定词、阻抗标签和边界位置；Markov 核、正向/反向协议、时域、初态、终点条件和桥接方式均是外加。若未指定反向核或支撑不互逆，\(\Sigma_F\) 不可定义；速度权重或非对称核下，内部项必须保留为 \(\log[K(i,j)/R(j,i)]\) 的逐边和。

## 48. Robin 边界、速度权重与内部探针的联合识别

**定义 48.1（反射—Robin Green 核与内部占用探针）。** 设 \(D>0\)、\(\rho>0\)。在区间 \([0,1]\) 上取算子
\[
\mathcal L=-D\frac{d^2}{dx^2},
\]
左端满足反射条件 \(y'(0)=0\)，右端满足 Robin 条件
\[
D y'(1)+\rho y(1)=0.
\]
其 Green 核为
\[
G_{D,\rho}(x,y)
 =\frac{1-\max(x,y)}{D}+\frac1{\rho}.
\]
记起点为 \(0\) 时的内部响应 profile
\[
g_{D,\rho}(u)=G_{D,\rho}(0,u)
=\frac{1-u}{D}+\frac1{\rho}
=\frac{r+1-u}{D},
\qquad r=\frac D\rho .
\]

取内部探针
\[
0\le u_1<\cdots<u_m<1
\]
并给每个探针一个未知正速度权重 \(w_i>0\)。假设同一条随机历史上的缩放占用量具有极限均值和二点协方差
\[
M_i=w_i g_{D,\rho}(u_i),
\]
以及对 \(i<j\)
\[
C_{ij}
 =w_iw_j\,g_{D,\rho}(u_j)^2,
\qquad
C_{ii}=M_i^2.
\]
有限格点模型中允许离散对角修正
\[
C_{ii}=M_i^2+o(1),
\]
但异点式保持不变。这里的联合量必须来自同一共同随机历史。

**定理 48.2（两点联合协方差识别 Robin 形状参数）。** 对任意 \(u_i<u_j\)，若 \(M_i,M_j,C_{ij}>0\)，则
\[
R_{ij}:=\frac{C_{ij}}{M_iM_j}
=\frac{g_{D,\rho}(u_j)}{g_{D,\rho}(u_i)}
=\frac{r+1-u_j}{r+1-u_i}.
\]
因此无量纲 Robin 形状参数 \(r=D/\rho\) 可由一对内部探针对唯一确定：
\[
r=
\frac{(1-u_j)-R_{ij}(1-u_i)}{R_{ij}-1}.
\]
可实现的观测值必须满足
\[
\frac{1-u_j}{1-u_i}<R_{ij}<1.
\]
下端点对应 \(r\downarrow0\)，上端点对应 \(r\uparrow\infty\) 的退化极限；在有限正参数模型中两端点均不取到。

**证明。** 对 \(i<j\)，共同历史的二点占用公式给出
\[
C_{ij}=w_iw_jg_{D,\rho}(u_j)^2,
\]
而
\[
M_iM_j=w_iw_jg_{D,\rho}(u_i)g_{D,\rho}(u_j).
\]
相除后未知速度权重完全消去，代入
\(g_{D,\rho}(u)=(r+1-u)/D\) 得所列比值。由于 \(u_i<u_j\)，函数
\[
r\longmapsto\frac{r+1-u_j}{r+1-u_i}
\]
在 \(r>0\) 上严格递增，值域正是所列开区间，故识别唯一。$\square$

**定理 48.3（绝对扩散尺度与 Robin 参数的联合不可识别性）。** 在未知 \(w_i\) 的模型类中，内部探针的全部均值与二点协方差不区分尺度变换
\[
(D,\rho,w_1,\ldots,w_m)
\longmapsto
(cD,c\rho,cw_1,\ldots,cw_m),
\qquad c>0.
\]
因此 \(D\) 与 \(\rho\) 不能分别从这些联合观测中识别；可识别的边界形状量是 \(D/\rho=r\)。

**证明。** 在该变换下
\[
g_{cD,c\rho}(u)=\frac1c\,g_{D,\rho}(u).
\]
所以均值和异点协方差分别保持为
\[
(cw_i)g_{cD,c\rho}(u_i)=M_i,\qquad
(cw_i)(cw_j)g_{cD,c\rho}(u_j)^2=C_{ij}.
\]
但 \(D,\rho\) 各自随 \(c\) 改变，故不能分别识别。$\square$

**推论 48.4（一个速度校准点恢复全部参数）。** 若某个探针 \(u_k\) 的速度权重 \(w_k\) 已知，则
\[
g_k=\frac{M_k}{w_k}
\]
可直接恢复。结合定理48.2得到 \(r=D/\rho\)，于是
\[
D=\frac{r+1-u_k}{g_k},
\qquad
\rho=\frac{D}{r}.
\]
其余速度权重随后由
\[
w_i=\frac{M_i}{g_{D,\rho}(u_i)}
\]
唯一确定。

若没有任何速度校准，联合协方差仍可确定 \(r\)，但只能确定每个 \(w_i/D\) 的组合，不能拆出绝对时间尺度。

**命题 48.5（共同历史是识别条件）。** 若两个内部探针分别由独立副本读取，则
\[
C_{ij}=0
\]
即使两个副本具有相同的边缘均值和边缘占用律。此时 \(C_{ij}/(M_iM_j)\) 不再提供 Green profile 比值，\(r=D/\rho\) 一般不可识别。

**范围与物理类比限制。** 这里的 \(D\) 是连续 Green 边值问题中的数学系数，\(\rho\) 是 Robin 边界系数，\(w_i\) 是内部探针的局部速度权重。它们只有在给出额外物理实现、时钟和边界耦合合同后，才可解释为扩散常数、边界泄漏率或物理速度。FIB 递归本身不选择 \(D\)、\(\rho\)、\(w_i\) 或共同随机历史。

\(\rho=0\) 时右端变为纯 Neumann 边界，常数零模使 Green 逆不再有限；\(u_i=1\) 的端点探针也不属于上述内部识别公式，必须另行处理。联合识别只说明声明模型中的参数组合可由共同探针律恢复，不推出热流、温度、耗散或物理普适性。

## 49. Composition 因子化与纤维隐藏性质的 minimax 界

**定义 49.1（完整数量轨迹与 composition 因子）。** 令
\[
\Gamma(a,b)=\bigl(q(M^n(a,b))\bigr)_{n\ge0},
\qquad
(a,b)\in\mathbb N_0^2\setminus\{(0,0)\},
\]
并定义完整数量观测
\[
\mathsf O(t)=\bigl(q(M^n c(t))\bigr)_{n\ge0}
=\Gamma(c(t)).
\]
对源律 \(\pi\) 写 \(\mu_\pi=c_\#\pi\)，并把
\(\mathsf O_\#\pi\) 视为在 \(\mathbb R^{\mathbb N_0}\) 上的观测律。

**定理 49.2（完整数量轨迹的 composition 因子化）。** 对任意源律 \(\pi\)，
\[
\mathsf O_\#\pi=\Gamma_\#\mu_\pi.
\]
因此对任意两律 \(\pi,\widetilde\pi\)，
\[
\operatorname{TV}(\mathsf O_\#\pi,\mathsf O_\#\widetilde\pi)
\le \operatorname{TV}(c_\#\pi,c_\#\widetilde\pi)
\le \operatorname{TV}(\pi,\widetilde\pi).
\]
特别地，若 \(c_\#\pi=c_\#\widetilde\pi\)，即使两条源律位于同一 composition 纤维上的不同概率律，完整数量轨迹的观测律也完全相同。这个结论已经包含全部代数代际 \(n\ge0\)；继续记录数量轨迹不能恢复被 composition 合并的纤维信息。

**证明。** 定义直接给出 \(\mathsf O=\Gamma\circ c\)，故推前满足 \(\mathsf O_\#\pi=\Gamma_\#(c_\#\pi)\)。确定性映射的推前收缩总变差距离，分别应用于 \(\Gamma\) 和 \(c\) 即得两项不等式。$\square$

**命题 49.3（composition 对隐藏性质的充分性判据）。** 设 \(h:\mathcal T\to\mathbb R\) 有界。下列条件等价：

1. \(h\) 在每个 composition 纤维 \(\mathcal F(a,b)=\{t:c(t)=(a,b)\}\) 上为常数；
2. 存在 \(\bar h\) 使 \(h=\bar h\circ c\)；
3. 对任意两条满足 \(c_\#\pi=c_\#\widetilde\pi\) 的源律，都有
\[
\int h\,d\pi=\int h\,d\widetilde\pi.
\]
当这些条件成立时，\(c_\#\pi\) 足以确定 \(h\) 的期望。若条件不成立，则存在同一纤维上的两条 Dirac 源律使 composition 推前相同而 \(h\) 期望不同。注意：这只说明 composition 是数量观测律的充分输入；完整数量观测 \(\mathsf O\) 还可能进一步合并不同 composition，因为 \(\Gamma\) 未假设单射。要由 \(\mathsf O\) 本身精确估计 \(h\)，必须另加 \(h=\widetilde h\circ\mathsf O\) 的因子化条件。

**证明。** 1 与 2 是按纤维定义的等价性；2 代入积分并使用 \(c_\#\pi=c_\#\widetilde\pi\) 得 3。若 1 失败，取同一纤维中 \(t_0,t_1\) 使 \(h(t_0)\ne h(t_1)\)，令 \(\pi_i=\delta_{t_i}\)，即得反例。$\square$

**定理 49.4（观测总变差下的两点 minimax 界）。** 令 \(h\) 有界，\(\theta_i=\int h\,d\pi_i\)，\(P_i=\mathsf O_\#\pi_i\)，并设 \(\Delta=|\theta_1-\theta_0|\)。对任意仅依赖完整数量观测的估计量 \(\widehat\theta\)（允许加入在两模型下相同的独立随机化），以
\[
R_i=\mathbb E_{\pi_i}|\widehat\theta-\theta_i|
\]
记绝对误差风险，则
\[
\max\{R_0,R_1\}
\ge \frac{\Delta}{2}\bigl(1-\operatorname{TV}(P_0,P_1)\bigr).
\]
对测试 \(\phi\in[0,1]\)（\(\phi=1\) 选择模型1），有
\[
\max\{\mathbb E_{P_0}\phi,\mathbb E_{P_1}(1-\phi)\}
\ge \frac{1-\operatorname{TV}(P_0,P_1)}2.
\]

**证明。** 把估计量的共同随机化并入观测空间；这不改变两观测律的总变差距离。对任一观测值，三角不等式给出
\[
|\widehat\theta-\theta_0|+|\widehat\theta-\theta_1|\ge\Delta.
\]
令 \(\lambda=P_0+P_1\)，\(p_i=dP_i/d\lambda\)。逐点有
\[
|\widehat\theta-\theta_0|p_0+|\widehat\theta-\theta_1|p_1
\ge \Delta\min(p_0,p_1).
\]
积分后
\[
R_0+R_1\ge \Delta\int\min(p_0,p_1)d\lambda
=\Delta(1-\operatorname{TV}(P_0,P_1)),
\]
从而得到第一式。第二式是二点测试的总变差恒等式：任意 \(\phi\) 的两类错误概率之和至少为 \(1-\operatorname{TV}(P_0,P_1)\)，再取最大值。$\square$

**推论 49.5（同 composition 纤维的不可识别下界）。** 固定任意满足 \(a,b\ge0\) 且 \(a+b\ge1\) 的 composition \((a,b)\)，令 \(\pi_0,\pi_1\) 是 \(\mathcal F(a,b)\) 上的两条概率律。则
\[
c_\#\pi_0=c_\#\pi_1=\delta_{(a,b)},\qquad
\mathsf O_\#\pi_0=\mathsf O_\#\pi_1,
\]
即观测总变差为零。若 \(\theta_i=\int h\,d\pi_i\) 不同，则任意数量轨迹估计量均满足
\[
\max_i\mathbb E_{\pi_i}|\widehat\theta-\theta_i|
\ge \frac{|\theta_1-\theta_0|}{2},
\]
且任意二点测试的最坏错误概率至少为 \(1/2\)。特别地，若纤维上有界隐藏性质 \(h\) 的振幅
\[
\operatorname{osc}_{\mathcal F(a,b)}h
=\max_{t\in\mathcal F(a,b)}h(t)-\min_{t\in\mathcal F(a,b)}h(t)
\]
为正，则
\[
\inf_{\widehat\theta(\mathsf O)}\sup_{\pi\in\mathcal P(\mathcal F(a,b))}
\mathbb E_\pi\left|\widehat\theta-\int h\,d\pi\right|
\ge \frac12\operatorname{osc}_{\mathcal F(a,b)}h.
\]
若 \(h\) 为二值且在该纤维上同时取 \(0,1\)，则绝对误差 minimax 半径至少为 \(1/2\)。若选择纤维上互不相交支持的两律，则可同时有
\[
\operatorname{TV}(\pi_0,\pi_1)=1,\qquad
\operatorname{TV}(\mathsf O_\#\pi_0,\mathsf O_\#\pi_1)=0.
\]

**范围边界。** 这些结论只针对静态源律和完整 quantity trajectory 这一观测映射；若加入叶序窗口、路径、输运时间、受控操作或跨探针 joint coupling，须重新计算观测推前，以上零总变差结论不自动延伸。结果也不声称 composition 推前可由数量轨迹反演，不把隐藏性质下界解释成物理噪声、热流或普适统计定律；它只说明在未增加能切开纤维的观测前，composition 因子化带来的信息缺口具有上述 minimax 代价。


## 50. 杀死链的准平稳谱、Yaglom 极限与 Doob 变换

本节把第12节的有限 FIB 杀死链从首达时间读出扩展到长期存活条件下的空间律。准平稳分布和条件化过程依赖杀死核与初态协议，不由源递归单独选择。

**定理 50.1（有限 FIB 杀死链的准平稳谱）。** 固定第12.1节的单位速度链，令 \(K_j\) 为暂态集合 \(\{0,\ldots,L_j-1\}\) 上的子核，
\[
\tau_j=\inf\{n\ge0:X_n=L_j\}.
\]
令 \(p_{j,i}=\theta/r_{(W_j)_i}\)，并令 \(K_j\) 的 Perron 根为 \(\lambda_{j,0}\)，取正的 Perron 向量 \(\phi_{j,0}\)，归一化为
\[
\sum_{i=0}^{L_j-1}\phi_{j,0}(i)^2=1.
\]
因为每条内部边的两个方向概率相同，\(K_j\) 对计数测度自伴；状态 \(0\) 的正持留概率使该有限连通核 primitive。取按计数内积正交归一的完整特征系
\[
(\lambda_{j,m},\phi_{j,m})_{0\le m<L_j},
\qquad
\lambda_{j,0}>\lvert\lambda_{j,m}\rvert\quad(1\le m<L_j).
\]
因此
\[
0<\lambda_{j,0}<1,\qquad
\eta_j:=
\begin{cases}
\displaystyle\max_{1\le m<L_j}\frac{|\lambda_{j,m}|}{\lambda_{j,0}},&L_j\ge2,\\[6pt]
0,&L_j=1,
\end{cases}
\quad \eta_j<1.
\]
定义
\[
\pi_j(i)=\frac{\phi_{j,0}(i)}{\sum_a\phi_{j,0}(a)}.
\]
则 \(\pi_j\) 是唯一准平稳分布，满足
\[
\pi_jK_j=\lambda_{j,0}\pi_j,\qquad
\mathbb P_{\pi_j}(X_n=i\mid\tau_j>n)=\pi_j(i),\qquad
\mathbb P_{\pi_j}(\tau_j>n)=\lambda_{j,0}^{\,n}.
\]
对任意暂态初态律 \(\mu_j\)，有
\[
\mathbb P_{\mu_j}(X_n=i,\tau_j>n)
=\sum_m\lambda_{j,m}^{\,n}
\langle\mu_j,\phi_{j,m}\rangle\phi_{j,m}(i),
\]
从而在固定 \(j\) 后令 \(n\to\infty\) 得
\[
\lambda_{j,0}^{-n}\mathbb P_{\mu_j}(\tau_j>n)
\longrightarrow
\left(\sum_a\mu_j(a)\phi_{j,0}(a)\right)
\left(\sum_i\phi_{j,0}(i)\right),
\]
且
\[
\left\|\mathcal L_{\mu_j}(X_n\mid\tau_j>n)-\pi_j\right\|_{\mathrm{TV}}
=O_{\mu_j}(\eta_j^n).
\]

**证明。** 对称性、连通性和 \(0\) 点自环给出 Perron–Frobenius 的正简单首特征值。有限维谱展开直接给出生存质量和条件分布的首项；由于 \(\mu_j\) 非负且 \(\phi_{j,0}>0\)，首项系数严格为正，余项由 \(\eta_j^n\) 控制。

**定理 50.2（准平稳测度的连续极限）。** 在第10.2节 Green 核一致收敛、固定简单模态的谱扰动以及第12.3节路径极限均成立的条件下，对每个固定 \(m\ge0\)（并取 \(j\) 足够大使 \(m<L_j\)），
\[
\frac{1-\lambda_{j,m}}{\epsilon_j}
\longrightarrow
\kappa_m=D\left(m+\frac12\right)^2\pi^2,
\]
若 \(J_j\phi\) 表示在区间 \([i/L_j,(i+1)/L_j)\) 上取值 \(\phi(i)\) 的阶梯嵌入，则归一化特征函数满足
\[
\sqrt{L_j}\,J_j\phi_{j,m}\longrightarrow
e_m(u)=\sqrt2\cos\left((m+\tfrac12)\pi u\right).
\]
因此
\[
\Pi_j:=\sum_{i=0}^{L_j-1}\pi_j(i)\,\delta_{i/L_j}
\Rightarrow
\Pi(du):=\frac\pi2\cos\left(\frac{\pi u}{2}\right)du.
\]
声明的数学连续模型是 \(0\) 反射、\(1\) 杀死、扩散系数 \(D\) 的过程。若初态律 \(\nu_0\) 在 \([0,1)\) 上有正质量，则固定 \(\nu_0\) 后令 \(t\to\infty\) 有
\[
\mathbb P_{\nu_0}(\tau>t)
\sim
\left(\int e_0\,d\nu_0\right)
\left(\int_0^1e_0(u)\,du\right)e^{-\kappa_0t},
\qquad
\kappa_0=\frac{D\pi^2}{4},
\]
以及 Yaglom 极限
\[
\mathcal L_{\nu_0}(Z_t\mid\tau>t)\Rightarrow\Pi.
\]
这里的极限顺序是先固定初态和连续模型，再令 \(t\to\infty\)；它不提供任意 \(t=t_j\) 下的离散—连续联合极限。

**推论 50.3（有限链与连续链的 Doob \(h\) 变换）。** 令 \(h_j=\phi_{j,0}\)，定义
\[
K_j^h(i,k)=\frac{K_j(i,k)h_j(k)}{\lambda_{j,0}h_j(i)}.
\]
这是暂态状态空间上的随机核，不变律为
\[
\widehat\pi_j(i)=\frac{h_j(i)^2}{\sum_a h_j(a)^2}.
\]
对固定 \(j\) 和固定路径长度 \(n\)，令 \(N\to\infty\)，则
\[
\mathcal L_{\mu_j}\bigl((X_0,\ldots,X_n)\mid\tau_j>N\bigr)
\Longrightarrow
\mu_j^h(i_0)\prod_{r=0}^{n-1}K_j^h(i_r,i_{r+1}),
\]
其中
\[
\mu_j^h(i)=\frac{\mu_j(i)h_j(i)}{\sum_a\mu_j(a)h_j(a)}.
\]
连续极限中 \(h=e_0\) 时，条件化过程的生成元为
\[
\mathcal L^h f
=h^{-1}\bigl(D(hf)''+\kappa_0hf\bigr)
=Df''-D\pi\tan\left(\frac{\pi u}{2}\right)f',
\]
其不变密度为 \(h(u)^2=2\cos^2(\pi u/2)\)。该漂移是“在长期存活条件下”的 Doob 变换项，不是 FIB 递归内生的物理外力。

FIB 递归在这里提供 \(L_j=F_{j+1}\)、\(N_j=F_{j+3}\) 及相应词序；给定外加参数 \(\delta,r_\alpha,r_\beta,\theta\) 后，所声明模型再定义 \(r_i\)、\(\epsilon_j=\delta/N_j^2\)、累计阻抗 \(\overline r\) 和 \(D=\theta\varphi^4/(\delta\overline r)\)。准平稳律、杀死边界、初态协议和条件化过程仍是外加统计模型。若允许 \(r_\alpha=r_\beta\)、\(\theta=r_\alpha/2\)，第13.4节的近负一高频模态可使 \(\eta_j\to1\)，所以不能宣称原阶梯时钟下存在 uniform-in-\(j\) 的 Yaglom 速率，也不能任意交换 \(j\to\infty\) 与 \(n\to\infty\)。

物理上可把 \(\Pi\) 类比为阻抗 FIB 链中长期幸存粒子的空间剖面，把 Doob 过程类比为把陷阱条件化为“永不命中”的路径律；这些名称不推出真实热流、势能、热浴或物理普适性。

## 51. 有限 FIB 杀死图的占用倾斜、首达压力与条件大偏差

准平稳谱描述长期存活，指数倾斜则描述在存活条件下偏好某种占用率的路径族。为避免把这种压力误读成物理自由能，本节把所有有限状态和时间假设写出。

**定理 51.1（占用倾斜—首达压力）。** 固定一个有限 FIB 状态图及其已声明转移矩阵 \(Q_m\)。取互不相交的活跃集 \(S\)、目标集 \(H\) 和杀死态 \(\dagger\)，令
\[
K=Q_m|_{S\times S},\qquad
b_H(i)=\sum_{h\in H}Q_m(i,h),
\]
并把离开 \(S\cup H\) 的质量并入 \(\dagger\)。设 \(K\) primitive、\(H\) 从 \(S\) 可达，初态律为 \(\nu\)，且 \(\nu\) 对 Perron 右向量有正投影。对有界占用 \(c:S\to\mathbb R\)，令
\[
N_T=\sum_{t=0}^{T-1}c(X_t),\quad
D_\vartheta=\operatorname{diag}(e^{\vartheta c(i)}),\quad
K_\vartheta=D_\vartheta K,\quad
h_\vartheta=D_\vartheta b_H.
\]
令
\[
\tau_\partial=\inf\{t\ge1:X_t\notin S\},\qquad
\tau_\dagger=\inf\{t\ge1:X_t=\dagger\},\qquad
\tau_H=\inf\{t\ge1:X_t\in H\}.
\]
按上述把所有离开 \(S\cup H\) 的质量并入 \(\dagger\) 的构造，有
\(\tau_\partial=\tau_H\wedge\tau_\dagger\)。
则有限时域和首达系数精确为
\[
Z_T(\vartheta):=\mathbb E_\nu[e^{\vartheta N_T};\tau_\partial>T]
=\nu^{\mathsf T}K_\vartheta^T\mathbf1,
\]
\[
p_n(\vartheta):=\mathbb E_\nu[e^{\vartheta N_{\tau_H}};\tau_H=n+1<\tau_\dagger]
=\nu^{\mathsf T}K_\vartheta^n h_\vartheta.
\]
因此
\[
G_\vartheta(z)=\sum_{n\ge0}z^{n+1}p_n(\vartheta)
=z\,\nu^{\mathsf T}(I-zK_\vartheta)^{-1}h_\vartheta,
\]
其收敛半径为 \(\rho(K_\vartheta)^{-1}\)。

令 \(\rho(\vartheta)=\rho(K_\vartheta)\)、\(\psi(\vartheta)=\log\rho(\vartheta)\)。Perron–Frobenius 理论给出
\[
\lim_{T\to\infty}\frac1T\log Z_T(\vartheta)=\psi(\vartheta),
\qquad
\lim_{n\to\infty}\frac1n\log p_n(\vartheta)=\psi(\vartheta).
\]
第二个极限使用 primitive；若 \(K\) 仅不可约而有周期，逐点首达系数可能在部分剩余类为零，只能改写为周期子列或 limsup。特别地，未倾斜生存尾的指数率是 \(\log\rho(K)<0\)；若只累计“在 \(T\) 前命中”的概率，则其对数除以 \(T\) 的极限在 \(\rho(K)<1\) 时为 \(0\)，不能直接写成 \(\log\rho(K)\)。

令 \(r_\vartheta,\ell_\vartheta>0\) 为右、左 Perron 向量，归一化 \(\ell_\vartheta^{\mathsf T}r_\vartheta=1\)，并令
\[
\widehat K_\vartheta(i,k)=
\frac{K_\vartheta(i,k)r_\vartheta(k)}
{\rho(\vartheta)r_\vartheta(i)},\qquad
\widehat\nu_\vartheta(i)=
\frac{\nu(i)r_\vartheta(i)}
{\nu^{\mathsf T}r_\vartheta}.
\]
则 \(\widehat K_\vartheta\) 是随机核，且
\[
Z_T(\vartheta)=
\rho(\vartheta)^T(\nu^{\mathsf T}r_\vartheta)
\widehat{\mathbb E}_{\vartheta,\widehat\nu_\vartheta}
[r_\vartheta(X_T)^{-1}].
\]
这说明 Doob 变换只增加有界端点修正；当 \(\vartheta=0\) 时它是条件长时存活的 Q-process，当 \(\vartheta\ne0\) 时是占用指数倾斜后的 Q-process。两者都不是原链“无限存活”这一正概率事件。

在条件律 \(\mathbb P_\nu(\,\cdot\,\mid\tau_\partial>T)\) 下，
\[
\lim_{T\to\infty}\frac1T
\log\mathbb E_\nu[e^{\vartheta N_T}\mid\tau_\partial>T]
=\overline\psi(\vartheta):=\psi(\vartheta)-\psi(0).
\]
若 \(c\) 不是 \(K\) 上的常数加 coboundary，即存在两个有向闭路具有不同的 \(c\)-平均，则有限状态压力的 Legendre 变换
\[
I(x)=\sup_{\vartheta\in\mathbb R}
\{\vartheta x-\overline\psi(\vartheta)\}
\]
给出 \(N_T/T\) 在该条件律下的完整大偏差速率函数。若 \(c\) 是常数加 coboundary，速率函数退化到相应单点；若 \(K\) 可约，压力是强连通分量压力的最大值，可能出现不可微点，必须逐分量分析。

证明链是路径展开、矩阵乘积、Perron–Frobenius 谱率、resolvent/Doob 望远镜和有限状态 Gärtner–Ellis 结论。长时域命题固定 \(m,S,H,\dagger\) 和时间齐次 \(Q_m\)；让图大小随 \(T\) 增长、让杀死集随 \(T\) 改变、或进入无限图，均需另加一致谱隙、紧性或尾控制。

FIB 递归在此只提供有限状态图的合法源和组合索引；\(Q_m\)、活跃集、目标集和占用函数是外加模型。谱半径是有限步数压力，不自动是热力学自由能；没有能量单位、温度协议和物理实现映射，不能推出真实相变、熵产生或时间箭头。

## 52. 净边流、Green 占用与共同历史鞅

本节回到第12节的有序切点链，直接把“电流—电阻—扩散”的类比拆成可验证的有限链恒等式。

**定理 52.1（净边流的连续性方程与 Green 公式）。** 固定 \(j\)，暂记 \(L=L_j\)、\(r_i=r_{(W_j)_i}\)、\(p_i=\theta/r_i\)，并约定 \(p_{-1}=p_L=0\)。从 \(X_0=0\) 出发，令 \(\tau=\inf\{n:X_n=L\}\)，并对 \(N\ge0\) 定义
\[
\mathsf L_N(k)=\sum_{0\le n<N\wedge\tau}{\bf1}_{\{X_n=k\}},
\]
\[
\mathsf J_N(i)=\sum_{0\le n<N\wedge\tau}
\left({\bf1}_{\{X_n=i,X_{n+1}=i+1\}}
-{\bf1}_{\{X_n=i+1,X_{n+1}=i\}}\right).
\]
规定 \(\mathsf L_N(L)=0\)、\(\mathsf J_N(-1)=\mathsf J_N(L)=0\)。则逐路径有
\[
{\bf1}_{\{X_{N\wedge\tau}=k\}}-{\bf1}_{\{X_0=k\}}
=\mathsf J_N(k-1)-\mathsf J_N(k),
\qquad 0\le k\le L.
\]
因而对任意边电荷 \(q_i=x_{i+1}-x_i\)，
\[
x_{X_{N\wedge\tau}}-x_{X_0}
=\sum_{i=0}^{L-1}q_i\mathsf J_N(i),
\]
并且终止于吸收端时 \(\mathsf J_\tau(i)=1\) 对每条路径成立。

令
\[
\mathcal G(k)=\mathbb E_0\mathsf L_\tau(k).
\]
则
\[
\mathcal G(k)-\mathcal G(k+1)=\frac1{p_k}=\frac{r_k}{\theta},
\qquad
\mathcal G(k)=\frac1\theta\sum_{i=k}^{L-1}r_i,
\]
其中 \(\mathcal G(L)=0\)。对任意函数 \(f:\{0,\ldots,L-1\}\to\mathbb R\)，
\[
\mathbb E_0\sum_{n<\tau}f(X_n)
=\sum_{k=0}^{L-1}f(k)\mathcal G(k)
=\frac1\theta\sum_{i=0}^{L-1}r_i\sum_{k=0}^{i}f(k).
\]
特别地 \(f\equiv1\) 给出
\[
\mathbb E_0\tau=\frac1\theta\sum_{i=0}^{L-1}(i+1)r_i,
\]
即第5.2节的均值公式；这里的占用和来自同一条历史，不能拆成独立访问。

**推论 52.2（边流鞅与条件协方差）。** 在共同历史过滤 \(\mathcal F_n=\sigma(X_0,\ldots,X_n)\) 下，令
\[
M_N^i=\mathsf J_N(i)-p_i\bigl(\mathsf L_N(i)-\mathsf L_N(i+1)\bigr).
\]
则 \(M_N^i\) 是鞅。若
\[
b_i(k)=p_i({\bf1}_{\{k=i\}}-{\bf1}_{\{k=i+1\}}),
\]
则一步条件协方差核为
\[
\Gamma^{\mathrm{edge}}_{ij}(k)
=\delta_{ij}p_i({\bf1}_{\{k=i\}}+{\bf1}_{\{k=i+1\}})
-b_i(k)b_j(k),
\]
并且
\[
\langle M^i,M^j\rangle_N
=\sum_{n<N\wedge\tau}\Gamma^{\mathrm{edge}}_{ij}(X_n).
\]
在终点 \(\tau\)，净边流本身恒为 \(1\)，所以正确的随机量是鞅终值：
\[
\operatorname{Cov}(M_\tau^i,M_\tau^j)
=\sum_{k=0}^{L-1}\mathcal G(k)\Gamma^{\mathrm{edge}}_{ij}(k)
=\operatorname{Cov}\left(
p_i(\mathsf L_\tau(i)-\mathsf L_\tau(i+1)),
p_j(\mathsf L_\tau(j)-\mathsf L_\tau(j+1))
\right).
\]
这里不能把不同边的流当成独立历史；相邻边虽无同一步双跨，却可通过同一当前位置产生条件协方差。

**定理 52.3（任意占用泛函的 Green–Doob 分解）。** 令 \(P\) 为包括吸收点 \(L\) 的完整核，并将 \(h_f(L)=0\)。对
\[
S_f(i)=\sum_{k=0}^{i}f(k),\qquad
h_f(i)=\frac1\theta\sum_{a=i}^{L-1}r_aS_f(a),
\]
有 \((I-P)h_f=f\)（在暂态点上）。于是
\[
A_N^f:=\sum_{n<N\wedge\tau}f(X_n)
=M_N^f+h_f(X_0)-h_f(X_{N\wedge\tau}),
\]
其中
\[
M_N^f=\sum_{n<N\wedge\tau}
\bigl(h_f(X_{n+1})-(Ph_f)(X_n)\bigr)
\]
是鞅。对两个探针 \(f,g\)，令
\[
\Gamma_{fg}(k)=P(h_fh_g)(k)-(Ph_f)(k)(Ph_g)(k).
\]
固定初态 \(X_0=0\) 且在 \(\tau\) 停止时，\(h_f(X_\tau)=0\)，所以
\[
\mathbb E_0A_\tau^f=h_f(0),\qquad
\operatorname{Cov}_0(A_\tau^f,A_\tau^g)
=\sum_{k=0}^{L-1}\mathcal G(k)\Gamma_{fg}(k).
\]
若初态为随机律，需另加终端校正项 \(h_f(X_0),h_g(X_0)\) 的协方差及其与鞅项的相应交叉项。

逐步至多跨一条边还给出
\[
M_N^f=\sum_{i=0}^{L-1}
\bigl(h_f(i+1)-h_f(i)\bigr)M_N^i,
\]
所以任意占用泛函的条件协方差可以由同一边流矩阵 \(\Gamma^{\mathrm{edge}}\) 组合得到。若另行给出 \(L\to\infty\) 的局部跳率、宏观时钟和预测二次变差收敛，离散鞅 FCLT 才能把该分解接到连续扩散的 Itô 鞅；这些收敛条件不由 \(\rho\) 自动提供。

“电流”“电阻”“扩散”在这里是有限链的关系名称。\(r_i,\theta,\delta\) 是外加核参数，FIB 递归不选择它们，也不由上述鞅恒等式推出物理电流、耗散或热流。

## 53. 有限时间窗口占用的 Green—鞅协方差与归一化响应

第43节的联合泛函和第46节的时间有序半群给出变换；本节进一步保留绝对时间和任意初态，给出有限窗口协方差的后向值函数分解。

**定理 53.1（窗口协方差的 Green—鞅分解）。** 在第12.3节连续反射—吸收模型中，令 \(Z\) 从概率律 \(\nu\) 出发，在 \(0\) 反射、到 \(1\) 后停留；令 \(\tau=\inf\{t:Z_t=1\}\)，杀死半群为
\[
(S_t f)(x)=\mathbb E_x[f(Z_t);t<\tau],\qquad H=-D\partial_x^2.
\]
固定 \(T<\infty\)、有限个窗口 \(I_r=[\alpha_r,\beta_r]\subset[0,T]\) 和实探针 \(f_r\in C^2([0,1])\) 满足 \(f_r(1)=0\)，定义
\[
A_r=\int_{\alpha_r}^{\beta_r}f_r(Z_s)\,ds.
\]
令
\[
U_r(t,x)=
\begin{cases}
\displaystyle\int_{\max(t,\alpha_r)}^{\beta_r}(S_{s-t}f_r)(x)\,ds,&t<\beta_r,\\[6pt]
0,&t\ge\beta_r.
\end{cases}
\]
则
\[
\mathbb E_\nu A_r=\int U_r(0,x)\,\nu(dx),
\]
并且对 \(s\le t\)，
\[
K_{r,k}(s,t)
=\nu S_s\bigl(f_r\,S_{t-s}f_k\bigr)
-\bigl(\nu S_s f_r\bigr)\bigl(\nu S_t f_k\bigr).
\]
令 \(K_{r,k}(s,t)=K_{k,r}(t,s)\)（当 \(t<s\)），则
\[
\operatorname{Cov}_\nu(A_r,A_k)
=\int_{I_r}\int_{I_k}K_{r,k}(s,t)\,dt\,ds.
\]

在该模型的共同 Brownian 历史上，\(U_r\) 满足反射边界的后向方程。对停时 \(T\wedge\tau\) 使用 Itô 公式得到
\[
A_r=U_r(0,Z_0)
+\sqrt{2D}\int_0^{T\wedge\tau}
\partial_xU_r(t,Z_t)\,dB_t.
\]
因此
\[
\operatorname{Cov}_\nu(A_r,A_k)
=\operatorname{Cov}_{X\sim\nu}(U_r(0,X),U_k(0,X))
+2D\int_0^T\mathbb E_\nu\left[
{\bf1}_{\{t<\tau\}}
\partial_xU_r(t,Z_t)\partial_xU_k(t,Z_t)
\right]dt.
\]
对任意 \(c\in\mathbb R^q\)，若 \(B=(\operatorname{Cov}(A_r,A_k))\)，则
\[
c^{\mathsf T}Bc
=\operatorname{Var}_{X\sim\nu}\left(\sum_rc_rU_r(0,X)\right)
+2D\int_0^T\mathbb E_\nu\left[{\bf1}_{\{t<\tau\}}
\left(\sum_rc_r\partial_xU_r(t,Z_t)\right)^2\right]dt\ge0.
\]
这只保证协方差矩阵半正定，非对角元可以为负。

对任意固定实向量 \(\lambda\)，定义完整停时路径律上的归一化响应
\[
F_T(\lambda)=\log\mathbb E_\nu\exp\left(\sum_r\lambda_rA_r\right).
\]
则
\[
\partial_{\lambda_r}F_T(\lambda)=\mathbb E_\lambda A_r,\qquad
\partial_{\lambda_k}\partial_{\lambda_r}F_T(\lambda)
=\operatorname{Cov}_\lambda(A_r,A_k),
\]
其中 \(d\mathbb P_\lambda/d\mathbb P_\nu=\exp(\lambda\cdot A-F_T(\lambda))\)。在 \(\lambda=0\) 时 Hessian 就是上述窗口协方差。若改用杀死半群筛选“存活至 \(T\)”的路径，归一化分母必须同步改为条件路径律；不能把完整停时响应与存活条件响应混用。

**有限 FIB 版本。** 令 \(a_{j,r}=\lfloor\alpha_r/\epsilon_j\rfloor\)、\(b_{j,r}=\lfloor\beta_r/\epsilon_j\rfloor\)、\(f_{j,r}(i)=f_r(i/L_j)\)，并定义
\[
A_{j,r}=\epsilon_j\sum_{n=a_{j,r}}^{b_{j,r}-1}f_{j,r}(X_n),
\]
吸收点的探针值为零。令 \(\widehat K_j\) 为包含吸收态的完整核，并把 \(f_{j,r}\) 在吸收态延拓为零；\(u_{j,r,n}\) 为从时间 \(n\) 到窗口终点的条件期望
\[
u_{j,r,n}(i)=
\epsilon_j\sum_{m=\max(n,a_{j,r})}^{b_{j,r}-1}
(\widehat K_j^{m-n}f_{j,r})(i)
\]
（当 \(n\ge b_{j,r}\) 置零）。则对每个固定 \(j\) 有精确协方差式
\[
\operatorname{Cov}(A_{j,r},A_{j,k})
=\operatorname{Cov}(u_{j,r,0}(X_0),u_{j,k,0}(X_0))
+\sum_{n=0}^{M_j-1}\mathbb E\,Q_{j,n}^{r,k}(X_n),
\]
其中 \(M_j=\max_r b_{j,r}\)，
\[
Q_{j,n}^{r,k}
=\widehat K_j(u_{j,r,n+1}u_{j,k,n+1})
-(\widehat K_j u_{j,r,n+1})(\widehat K_j u_{j,k,n+1}).
\]
由第12.3节路径极限和固定窗口的连续映射，\((A_{j,r})\) 的联合律、均值和二阶矩在 \(j\to\infty\) 时收敛到上述连续对象；这需要固定 \(T\)、窗口和探针，不能把 \(T\) 或窗口宽度同时推到极限。

取 \(f,g\ge0\) 为各自非零、支持在内部且互不相交的光滑探针，固定 \(t_0>0\)，并取足够小的 \(\eta>0\) 使 \(t_0+3\eta\le T\)。在相邻窗口 \(I_\eta=[t_0,t_0+\eta]\)、\(J_\eta=[t_0+2\eta,t_0+3\eta]\) 上，有
\[
\eta^{-2}\operatorname{Cov}_0\left(\int_{I_\eta}f(Z_s)ds,
\int_{J_\eta}g(Z_t)dt\right)
\longrightarrow
-(S_{t_0}f)(0)(S_{t_0}g)(0)<0
\]
沿用第12.3节的同一共同历史。因此非负探针在同一时刻的协方差矩阵虽半正定，两个足够短且不重叠的时间窗口仍可有严格负协方差。

物理类比上，\(R_h=\int_0^hS_sds\) 是声明扩散模型的有限时间源响应算子，鞅项是该随机路径模型的噪声相关，\(F_T\) 的 Hessian 是路径指数重加权的统计易感性。它们不自动等于真实外场的因果响应、Kubo 核、温度、热浴、耗散、熵产生或量子对易子；若要作这些识别，必须另给物理读出、单位和外场—生成元耦合。

## 54. Green 加权探针的秩判据与 Robin—速度不可分辨边界

第48节从一对内部探针识别 Robin 形状参数。本节把“需要多少探针”写成有限维速度族的秩条件，并给出一个新的全局尺度退化。

**定理 54.1（有限链速度族的探针秩判据）。** 固定一个有限 FIB 切链的单位速度矩阵 \(B=I-K\)、Green 矩阵 \(G=B^{-1}\)，令 \(\tau\) 为到达吸收端 \(L\) 的停时，并令
\[
q_i=G(0,i),\qquad Q=\operatorname{diag}(q_0,\ldots,q_{L-1}).
\]
允许局部速度权重属于有限维族
\[
v(\eta)=v^0+\Phi\eta,\qquad \Phi\in\mathbb R^{L\times d},
\]
并限制参数在使行缩放后的核仍为随机核的开邻域内。行缩放给出
\[
B^{(v)}=V(\eta)^{-1}B,\qquad G^{(v)}=G V(\eta).
\]
令
\[
V_{\mathrm{occ}}
=\bigl(\mathsf L_\tau(0),\ldots,\mathsf L_\tau(L-1)\bigr)^{\mathsf T}
\]
为暂态占用向量。若 \(m\) 个有符号线性占用探针写成 \(Y=F V_{\mathrm{occ}}\)，则
\[
\mathbb E_\eta Y=FQv^0+J\eta,\qquad J=FQ\Phi.
\]
因此该参数族由这些均值局部可识别，当且仅当
\[
\operatorname{rank}J=d.
\]
必有 \(m\ge d\)。若 \(\operatorname{rank}\Phi=d\) 且允许任意有符号探针，令 \(A=Q\Phi\) 并取
\[
F=(A^{\mathsf T}A)^{-1}A^{\mathsf T},
\]
则 \(FA=I_d\)，所以 \(d\) 个探针足够。若探针必须非负、局部支持或来自不同副本，则最少数和可识别方向仍由实际的 \(FQ\Phi\) 秩决定，不能沿用有符号结论。

在单位速度共同历史下，已有占用协方差给出
\[
C_{ik}=q_{\max(i,k)}^2-\mathbf1_{\{i=k\}}q_i,
\]
所以探针协方差为
\[
\Sigma=F C F^{\mathsf T}.
\]
若另有独立读出噪声协方差 \(\Gamma\succ0\)，则
\[
\mathcal I=J^{\mathsf T}(\Sigma+\Gamma)^{-1}J
\]
是协方差归一化的信息矩阵；只有在额外声明高斯读出误差时，才可称为 Fisher 信息。由于 \(\Sigma+\Gamma\) 正定，\(\mathcal I\succ0\) 当且仅当 \(\operatorname{rank}J=d\)。

**连续 Robin 扩展。** 在 \([0,1]\) 上取 \(-D\partial^2\)，右端 Dirichlet \(y(1)=0\)，左端 Robin \(y'(0)=\beta y(0)\)、\(\beta\ge0\)。其 Green 核为
\[
G_\beta(u,v)=\frac{(1+\beta\min(u,v))(1-\max(u,v))}{D(1+\beta)}.
\]
若速度密度为 \(w_\eta=w^0+\sum_{a=1}^d\eta_a\phi_a\)，并假定 \(w^0,\phi_a\in C([0,1])\)，从边界起点 \(0\) 的一阶探针均值为
\[
\mu_{\beta,\eta}(f)
=\int_0^1 f(v)\frac{1-v}{D(1+\beta)}w_\eta(v)\,dv.
\]
在给定参数点，定义灵敏度函数
\[
\psi_0(v)=-\frac{(1-v)w_\eta(v)}{D(1+\beta)^2},\qquad
\psi_a(v)=\frac{(1-v)\phi_a(v)}{D(1+\beta)}
\quad(1\le a\le d).
\]
对 \(m\) 个连续探针 \(f_r\)，参数 \(\beta,\eta\) 的均值 Jacobian 为
\[
J_{ra}=\int_0^1 f_r(v)\psi_a(v)\,dv.
\]
所以局部可识别当且仅当 \(\operatorname{rank}J=d+1\)。若 \(\psi_0,\ldots,\psi_d\) 在线性空间中独立，则至少需要且足够 \(d+1\) 个探针。取 \(a,b=0,\ldots,d\) 的 Gram 矩阵
\[
H_{ab}=\int_0^1\psi_a(v)\psi_b(v)\,dv
\]
并取 \(m=d+1\)、\(r=0,\ldots,d\) 的探针
\[
f_r=\sum_{b=0}^{d}(H^{-1})_{rb}\psi_b,
\]
即可得到 \(J=I_{d+1}\)。

若速度族允许全局缩放 \(w\mapsto cw\)，同时令
\[
\beta'=c(1+\beta)-1
\]
且 \(c\) 取在保持 \(\beta'\ge0\) 的邻域内，则
\[
\frac{1-v}{D(1+\beta')}cw(v)
=\frac{1-v}{D(1+\beta)}w(v).
\]
因此任意数量的边界起点一阶占用探针都不能同时区分 Robin 参数和全局速度尺度。施加 \(\int w=1\) 等归一化并排除全局缩放方向后，才可使用上述 \(d+1\) 维秩判据。

这些结论只针对固定源、阻抗、时钟、有限维速度族、共同随机历史和一阶均值读出；完整路径律可能携带额外信息。它们不声称任意速度函数、任意 Robin 模型或任何物理装置都可由有限探针识别；若使用非负探针、不同副本或改变边界，必须重新计算可用秩与协方差。

## 55. FIB 杀死链的更新/再生结构与极限边界

**假设 55.1（参考切点与一次更新）。** 固定第12节单位速度、左反射右吸收的 FIB 链，暂态集 \(E_j=\{0,\ldots,L_j-1\}\)，吸收点 \(L_j\)，转移核 \(K_j\)，并假设 \(\rho(K_j)<1\)。取参考态 \(a_j\in E_j\)，从 \(a_j\) 出发令
\[
\sigma_0=0,\qquad
\sigma_{r+1}=\inf\{n>\sigma_r:X_n\in\{a_j,L_j\}\}.
\]
记 \(R_j=\{X_{\sigma_1}=a_j\}\)、\(D_j=\{X_{\sigma_1}=L_j\}\)、\(\kappa_j=\mathbb P_{a_j}(D_j)\in(0,1)\)。一次段的持续时间和有界奖励分别为
\[
T_j=\sigma_1,\qquad
Y_j=\sum_{n=0}^{\sigma_1-1}g_j(X_n),\qquad
g_j:E_j\to\mathbb R_+^d.
\]
定义两个子概率测度
\[
\mu_j^R(B)=\mathbb P_{a_j}((T_j,Y_j)\in B;R_j),\qquad
\mu_j^D(B)=\mathbb P_{a_j}((T_j,Y_j)\in B;D_j).
\]
它们的总质量分别为 \(1-\kappa_j\) 和 \(\kappa_j\)。区间 \([\sigma_r,\sigma_{r+1})\) 不重复计入返回端点。

**定理 55.2（更新测度与精确首达律）。** 定义
\[
U_j=\sum_{m\ge0}(\mu_j^R)^{*m},
\qquad
U_j=\delta_{(0,0)}+\mu_j^R*U_j.
\]
则 \(U_j\) 的总质量为 \(\kappa_j^{-1}\)，且杀死前的总时长与总奖励
\[
\tau_j=\inf\{n:X_n=L_j\},\qquad
A_j=\sum_{n<\tau_j}g_j(X_n)
\]
满足精确卷积律
\[
\mathbb P_{a_j}((\tau_j,A_j)\in\cdot)
=(U_j*\mu_j^D)(\cdot).
\]
对 \(s\ge0\)、\(\lambda\in\mathbb R_+^d\)，令
\[
\phi_j^R(s,\lambda)
=\mathbb E_{a_j}[e^{-sT_j-\langle\lambda,Y_j\rangle};R_j],
\qquad
\phi_j^D(s,\lambda)
=\mathbb E_{a_j}[e^{-sT_j-\langle\lambda,Y_j\rangle};D_j].
\]
则
\[
\mathbb E_{a_j}e^{-s\tau_j-\langle\lambda,A_j\rangle}
=\frac{\phi_j^D(s,\lambda)}
{1-\phi_j^R(s,\lambda)}.
\]
分母的零点给出首达变换的极点；若允许有符号奖励，则该公式限于变换存在的参数邻域。

令
\[
\eta_j^e(k)
=\mathbb E_{a_j}\left[
\sum_{0\le n<\sigma_1}{\bf1}_{\{X_n=k\}};e
\right],
\qquad e\in\{R_j,D_j\}.
\]
则 Green 占用有精确再生分解
\[
G_j(a_j,k)=\frac{\eta_j^{R_j}(k)+\eta_j^{D_j}(k)}{\kappa_j},
\qquad
\mathbb E_{a_j}\sum_{n<\tau_j}g_j(X_n)
=\frac{\eta_j^{R_j}(g_j)+\eta_j^{D_j}(g_j)}{\kappa_j}.
\]
参考态访问次数
\[
V_{a_j}=\sum_{n<\tau_j}{\bf1}_{\{X_n=a_j\}}
\]
满足
\[
\mathbb P(V_{a_j}=m)=\kappa_j(1-\kappa_j)^{m-1},
\qquad
\mathbb E V_{a_j}=G_j(a_j,a_j)=\kappa_j^{-1}.
\]
因此 \(\kappa_j=1/G_j(a_j,a_j)\)。

**FIB 特例 55.3（参考态 \(0\) 的成功概率）。** 对 \(a_j=0\)，沿用第52节 Green 公式，
\[
G_j(0,0)=\frac1\theta\sum_{i=0}^{L_j-1}r_{(W_j)_i}.
\]
故
\[
\kappa_j=\frac{\theta}{\sum_{i<L_j}r_{(W_j)_i}},
\qquad
L_j\kappa_j\longrightarrow\frac{\theta}{\bar r},
\qquad
\bar r=\varphi^{-2}r_\alpha+\varphi^{-1}r_\beta.
\]
这里 \(L_j\)、词序和标签由 FIB 递归给出；核、阻抗、\(\theta\)、边界和初态仍是外加模型。

**定理 55.4（再生扩展中的更新奖励 CLT/FCLT）。** 这是在杀死链上增加外加重启协议后的再生扩展。令
\((T_{j,r}^R,Y_{j,r}^R)_{r\ge1}\) 为按 \(\mu_j^R/(1-\kappa_j)\) 归一化的独立同分布返回段，令
\[
S_{j,n}=\sum_{r\le n}T_{j,r}^R,\qquad
N_j(t)=\max\{n:S_{j,n}\le t\},\qquad
\mathcal R_j(t)=\sum_{r\le N_j(t)}Y_{j,r}^R.
\]
若 \(\mu_{T,j}=\mathbb E T_{j,1}^R\in(0,\infty)\)、\(\mu_{Y,j}=\mathbb E Y_{j,1}^R\) 有限，令 \(\gamma_j=\mu_{Y,j}/\mu_{T,j}\)。若
\[
\Sigma_j=\frac1{\mu_{T,j}}
\operatorname{Cov}(Y_{j,1}^R-\gamma_jT_{j,1}^R)
\]
有限，则固定 \(j\) 时
\[
\left\{
\frac{\mathcal R_j(nt)-\gamma_jnt}{\sqrt n}:0\le t\le T
\right\}
\Rightarrow
\Sigma_j^{1/2}B(t)
\]
于 \(D([0,T],\mathbb R^d)\)。若 \(j\) 随 \(n\) 变化，还需对
\(\xi_{j,r}=Y_{j,r}^R-\gamma_jT_{j,r}^R\) 另加三角阵列 Lindeberg 条件及 \(T_j\) 的统一一阶矩和非退化条件；FIB 递归不自动给出这些条件。

**定理 55.5（自然杀死机制的几何更新边界）。** 以下限于标量奖励。原杀死链只完成有限次返回。令返回段数 \(\mathcal N_j\) 满足
\[
\mathbb P(\mathcal N_j=m)=(1-\kappa_j)^m\kappa_j,\qquad m\ge0.
\]
设返回段条件均值和方差为
\[
m_j=\mathbb E Y_j^R,\qquad v_j=\operatorname{Var}(Y_j^R),
\]
终段奖励为 \(Y_j^D\)。若 \(\kappa_j\to0\)，
\[
\frac{\kappa_j\mathbb E|Y_j^D|}{m_j}\to0,
\qquad
\frac{\kappa_jv_j}{m_j^2}\to\chi\in[0,\infty),
\]
并且返回段满足相应的 Lindeberg 条件，则
\[
\frac{\kappa_j}{m_j}
\left(A_j-\frac{m_j}{\kappa_j}\right)
\Rightarrow
E-1+\sqrt{\chi E}\,Z,
\]
其中 \(E\sim\operatorname{Exp}(1)\)、\(Z\sim N(0,1)\) 独立。 \(\chi=0\) 时极限为 \(E-1\) 而非高斯；\(\chi>0\) 时为指数随机化的正态混合。终段不可忽略时，必须加入其联合极限，不能套用该式。

这些更新恒等式只需有限图和 \(\rho(K_j)<1\)。连续扩散极限、\(j\to\infty\) 与更新次数或时间同时取极限，需要一致尾界、矩界和三角阵列条件。返回段的条件律是外加再生协议，不是 FIB 递归内生的独立样本；\(\kappa_j\) 的 FIB 渐近也不能推广到任意速度权重、非对称核、Robin 边界或真实物理装置。更新奖励、Brownian 极限和混合极限均不自动代表热流、扩散噪声或普适物理涨落。

## 56. 有限 FIB 转移算子的谱测度、符号熵率与转移熵

本节固定一个外加有限状态统计模型。设第 \(m\) 层 FIB 递归给出的状态标签集合为有限集 \(\mathcal S_m\)，另给行随机核 \(Q\) 和平稳律 \(\pi\)，其中 \(\pi_i>0\)、\(\pi Q=\pi\)。递归本身不选择概率核、初态或观测通道。

**定理 56.1（可逆转移核的谱测度与协方差生成函数）。** 若 \(Q\) 对
\[
\langle f,g\rangle_\pi=\sum_i\pi_i f(i)g(i)
\]
自伴且链不可约，取正交归一特征系
\[
\phi_0\equiv1,\qquad Q\phi_a=\lambda_a\phi_a,\qquad \lambda_0=1.
\]
对中心化观测 \(\pi g=0\)，定义
\[
\mu_g=\sum_{a\ge1}|\langle g,\phi_a\rangle_\pi|^2\delta_{\lambda_a}.
\]
则
\[
C_g(n):=\operatorname{Cov}_\pi(g(X_0),g(X_n))
=\langle g,Q^ng\rangle_\pi
=\int_{[-1,1]}\lambda^n\,d\mu_g(\lambda),
\]
并且 \(C_g(0)=\mu_g([-1,1])\)。在 \(|z|<1\) 时，
\[
R_g(z):=\sum_{n\ge0}z^nC_g(n)
=\int\frac{d\mu_g(\lambda)}{1-z\lambda}.
\]
若 \(\operatorname{supp}\mu_g\subset[-1+\gamma,1-\gamma]\)，则
\[
C_g(0)+2\sum_{n\ge1}C_g(n)
=\int\frac{1+\lambda}{1-\lambda}\,d\mu_g(\lambda).
\]
若链周期导致 \(-1\) 谱质量，上式须改作 Abel 极限或不宣称收敛。谱测度是外加核作用于 FIB 状态标签后的统计对象，不是递归内生谱。

**定理 56.2（符号观测的传递矩阵与 Rényi 熵率）。** 取有限字母表 \(\mathcal A\) 及记忆无关发射通道 \(O(a\mid i)\)，满足 \(\sum_aO(a\mid i)=1\)。令
\[
D_a=\operatorname{diag}(O(a\mid i)),\qquad M_a=D_aQ.
\]
若 \(Y_t\) 条件于 \(X_t\) 独立发射，则任意词 \(a_0^{n-1}\) 的概率为
\[
p_n(a_0^{n-1})
=\pi^{\mathsf T}M_{a_0}M_{a_1}\cdots M_{a_{n-1}}\mathbf1.
\]
对整数 \(\alpha\ge2\)，定义
\[
\mathcal T_\alpha=\sum_{a\in\mathcal A}M_a^{\otimes\alpha}.
\]
则
\[
\sum_{a_0^{n-1}}p_n(a_0^{n-1})^\alpha
=(\pi^{\otimes\alpha})^{\mathsf T}
\mathcal T_\alpha^n\mathbf1^{\otimes\alpha}.
\]
若 \(\mathcal T_\alpha\) primitive 且首末向量对其 Perron 向量投影为正，则
\[
h_\alpha(Y)
=\lim_{n\to\infty}\frac1{1-\alpha}
\frac1n\log\sum_{a_0^{n-1}}p_n(a_0^{n-1})^\alpha
=\frac{\log\rho(\mathcal T_\alpha)}{1-\alpha}.
\]
\(\alpha=2\) 时 \(h_2(Y)=-\log\rho(\sum_aM_a\otimes M_a)\)。Shannon 熵率
\[
h(Y)=\lim_{n\to\infty}n^{-1}H(Y_0,\ldots,Y_{n-1})
\]
对平稳有限字母过程存在；一般隐藏 Markov 输出不能把它直接替换为 \(\alpha\to1\) 的张量谱式，除非另加可微延拓条件。若观测是状态本身，则
\[
h(X)=-\sum_i\pi_i\sum_jQ_{ij}\log Q_{ij}.
\]

**推论 56.3（互信息率的可计算差）。** 在同一定义下，
\[
H(Y_0^{n-1}\mid X_0^{n-1})
=n\sum_i\pi_iH(O(\cdot\mid i)).
\]
因此整条隐藏状态与符号输出的互信息率为
\[
I(X;Y)
=h(Y)-\sum_i\pi_iH(O(\cdot\mid i))\ge0.
\]
若初态非平稳，需另给熵率收敛条件，不能仅凭有限层 FIB 递归把该极限视为默认结论。

**定理 56.4（有限窗口转移熵的矩阵可计算式）。** 现在以同一状态链产生联合输出 \((U_t,Y_t)\)，给定 \(X_t=i\) 时按外加通道 \(O(u,y\mid i)\) 发射。令
\[
D_{u,y}=\operatorname{diag}(O(u,y\mid i)),\qquad
M_{u,y}=D_{u,y}Q.
\]
则
\[
p_n(u_0^{n-1},y_0^{n-1})
=\pi^{\mathsf T}M_{u_0,y_0}\cdots M_{u_{n-1},y_{n-1}}\mathbf1.
\]
对 \(k,\ell\ge0\)，定义有限历史转移熵
\[
T_{U\to Y}^{(k,\ell)}
=I(U_{t-k}^{t-1};Y_t\mid Y_{t-\ell}^{t-1}).
\]
由 \(p_n\) 对未涉及坐标求和即可得到所需边缘概率，因此
\[
T_{U\to Y}^{(k,\ell)}
=H(Y_t\mid Y_{t-\ell}^{t-1})
-H(Y_t\mid Y_{t-\ell}^{t-1},U_{t-k}^{t-1}).
\]
零概率项按 \(0\log0=0\) 处理。有限字母平稳过程的无限历史量
\[
T_{U\to Y}^{(\infty)}
=I(U_{-\infty}^{-1};Y_0\mid Y_{-\infty}^{-1})
\]
由条件熵极限给出；它为零当且仅当
\[
P(Y_0\mid U_{-\infty}^{-1},Y_{-\infty}^{-1})
=P(Y_0\mid Y_{-\infty}^{-1})
\quad\text{几乎处处}.
\]
即使 \(U_t,Y_t\) 在给定同一时刻状态时条件独立，\(U\) 的过去仍可能通过隐藏状态携带额外预测信息，故转移熵不自动为零。

FIB 递归只提供有限状态标签、词序和组合索引；\(Q,\pi,O\)、共同历史、平稳性和发射协议均为外加。若递归给出的图可约或周期，需按强连通分量和周期子列重写 Perron 极限与熵率。谱测度、自相关、Shannon 熵率和转移熵都不等于热力学熵、真实因果流、能量耗散、温度或热流。

## 57. 多探针联合响应的秩识别、实验设计与规范退化

本节把第54节的一阶占用均值秩判据扩展到一阶响应、二阶协方差和有限时间窗口的联合读出。所有动力学、初态、读出噪声与速度参数均为外加模型；FIB 递归只提供逐字源、切点载体及组合坐标。

**定义 57.1（有限链的联合响应数据）。** 令暂态集合为 \(I=\{0,\ldots,L-1\}\)，参数 \(\vartheta\in\Theta\subset\mathbb R^d\)，\(K_\vartheta\) 为声明的暂态子核，\(B_\vartheta=I-K_\vartheta\) 可逆，\(G_\vartheta=B_\vartheta^{-1}\)。令初态律为行向量 \(\nu\)，并写
\[
q_\vartheta=G_\vartheta^{\mathsf T}\nu^{\mathsf T}.
\]
若 \(V=(V_i)_{i\in I}\) 是杀死链占用向量，\(C_\vartheta=\operatorname{Cov}_\vartheta(V)\)，取 \(m\) 个有符号占用探针组成 \(F\in\mathbb R^{m\times L}\)，读出
\[
Y=FV+\xi,\qquad
\mathbb E\xi=0,\qquad
\operatorname{Cov}(\xi)=\Gamma,
\]
其中 \(\xi\) 与链独立且已知 \(\Gamma\)。联合响应数据为
\[
\mathcal D_F(\vartheta)=\bigl(\mu_F(\vartheta),\Sigma_F(\vartheta)\bigr),
\qquad
\mu_F=Fq_\vartheta,\qquad
\Sigma_F=FC_\vartheta F^{\mathsf T}+\Gamma.
\]
对对称矩阵用 \(\operatorname{vech}\) 收集上三角元素。

**定理 57.2（联合响应的局部秩判据）。** 若 \(K_\vartheta\) 关于 \(\vartheta\) 为 \(C^1\)，则
\[
J_F(\vartheta)=
\begin{bmatrix}
D\mu_F(\vartheta)\\
D\operatorname{vech}\Sigma_F(\vartheta)
\end{bmatrix}
\]
是联合一阶、二阶响应的 Jacobian，并满足
\[
\ker J_F
=\ker D\mu_F\cap\ker D\operatorname{vech}\Sigma_F.
\]
若 \(\operatorname{rank}J_F=d\)，则在该参数点邻域内，\(\vartheta\) 由联合均值和协方差局部唯一确定。若秩小于 \(d\)，存在非零切向量使均值和协方差均沿该方向一阶不变；这只说明一阶不可见，不推出非线性精确等价。若存在非恒定曲线 \(\vartheta(t)\) 使 \(\mathcal D_F(\vartheta(t))\) 恒定，则这些观测对该曲线精确不可辨。

**推论 57.3（探针数量与增量信息）。** 仅用均值时至少需 \(m\ge d\) 才可能正则识别；联合均值与对称协方差的输出数为
\[
M=m+\frac{m(m+1)}2,
\]
故正则识别必有 \(d\le M\)。对固定探针，
\[
\ker J_F=\ker J_\mu\cap\ker J_\Sigma.
\]
因此若 \(N=\ker J_\mu\)，则二阶读出消除均值退化，当且仅当 \(D\Sigma_F|_N\) 为单射。未知的 \(\Gamma\)、未知时钟或未知初态必须把相应参数一并加入 \(\vartheta\)，不能直接沿用已知噪声结论。

**定理 57.4（速度族的联合灵敏度公式）。** 在第54节的有限 FIB 切链中，先固定单位速度核与阻抗，令 \(q_i=G(0,i)\)、\(Q=\operatorname{diag}(q_i)\)。允许局部速度
\[
v(\eta)=v^0+\Phi\eta,\qquad \eta\in\mathbb R^d,
\]
并以行缩放得到 \(G^{(v)}=GV\)。在反射—吸收最近邻链的共同历史下，
\[
\mu_F(\eta)=FQv(\eta),
\]
且
\[
C^{(v)}_{ik}
=q_{\max(i,k)}^2v_iv_k-\mathbf1_{\{i=k\}}q_iv_i.
\]
对任意速度方向 \(z\in\mathbb R^L\)，
\[
\dot C^{(v)}[z]_{ik}
=q_{\max(i,k)}^2(z_iv_k+v_iz_k)
-\mathbf1_{\{i=k\}}q_iz_i.
\]
所以联合响应的参数 Jacobian 为
\[
J_{F,v}=
\begin{bmatrix}
FQ\Phi\\
\operatorname{vech}\!\left(F\dot C^{(v)}[\Phi]F^{\mathsf T}\right)
\end{bmatrix}.
\]
速度族在该点由一阶均值和协方差局部识别，当且仅当 \(\operatorname{rank}J_{F,v}=d\)。该式来自行缩放 Green 矩阵和共同历史的二阶占用公式。

**反例 57.5（一个总占用探针的均值退化被方差解除）。** 取两个暂态点 \(0,1\)，\(r_\alpha=r_\beta=1\)、\(\theta=1/4\)，左端反射、右端吸收。单位速度下
\[
K=\begin{pmatrix}3/4&1/4\\1/4&1/2\end{pmatrix},\qquad
G=(I-K)^{-1}=\begin{pmatrix}8&4\\4&4\end{pmatrix},\qquad
q=(8,4).
\]
取一个总占用探针 \(F=(1,1)\)，速度为 \(v=(v_0,v_1)\) 时
\[
\mathbb E Y=8v_0+4v_1,
\]
\[
\operatorname{Var}(Y)
=64v_0^2+32v_0v_1+16v_1^2-8v_0-4v_1.
\]
在 \(v=(1,1)\) 处，\((\mathbb EY,\operatorname{Var}Y)\) 对 \((v_0,v_1)\) 的 Jacobian 为
\[
\begin{pmatrix}8&4\\152&60\end{pmatrix},
\qquad
\det=-128\ne0.
\]
单独均值只有一维秩，方向 \((1,-2)\) 不可见；加入同一探针的二阶响应后满秩。若叠加已知独立读出噪声，只需在观测方差中加入常数 \(\Gamma\)，Jacobian 不变；若噪声方差未知，则它成为新的不可辨方向。

**定理 57.6（连续时间窗口的联合设计判据）。** 在第53节声明的反射—吸收扩散模型中，取有限窗口 \(I_r\) 和探针 \(f_r\)，令
\[
A_r=\int_{I_r}f_r(Z_t)\,dt,\qquad
\mu_r(\vartheta)=\mathbb E_\vartheta A_r,\qquad
\mathcal C_{rs}(\vartheta)=\operatorname{Cov}_\vartheta(A_r,A_s).
\]
若半群、初态与读出关于 \(\vartheta\) 为 \(C^1\)，定义
\[
J^{(1)}_{ra}=\partial_{\vartheta_a}\mu_r,\qquad
J^{(2)}_{(r,s),a}=\partial_{\vartheta_a}\mathcal C_{rs}.
\]
联合窗口响应局部识别当且仅当
\[
\operatorname{rank}
\begin{bmatrix}J^{(1)}\\J^{(2)}\end{bmatrix}=d.
\]
若静态均值有规范退化方向 \(h\ne0\)，即 \(J^{(1)}h=0\)，而协方差核导数在所选探针张成的张量积空间上对 \(h\) 非零，则协方差读出解除该方向的一阶退化；若同样为零，则联合一、二阶数据仍不能在一阶识别它。

**实验设计推论 57.7（双重灵敏度与稳定性）。** 对固定参数点，把 \(J_F\) 的最小奇异值记为 \(s_{\min}(J_F)\)。满秩只给局部唯一性；在有界观测噪声下，若要有统一的一阶稳定性，需要设计序列满足
\[
\inf_j s_{\min}(J_{F,j})>0.
\]
可先选探针使均值灵敏度形成对偶框架，再在均值零空间内选择使协方差灵敏度非零的时间窗或探针。若探针被限制为非负、局部支撑或来自独立副本，必须重新计算联合秩。

**反例 57.8（全局速度—跳尺度规范的精确不可辨性）。** 在原始跳率 \(\theta/(v_ir_i)\) 中，若 \(\theta\) 也未知，则对任意允许的 \(c>0\)
\[
(v,\theta)\longmapsto(cv,c\theta)
\]
保持每条边的跳跃概率、持留概率、吸收停时的完整路径律，以及所有占用探针的各阶响应不变。因此不加 \(\theta\) 或速度总量归一化时，任何数量的同链探针都不能分离这一全局尺度；固定 \(\theta\)、规定 \(\sum_i v_i\) 或校准一个局部速度，才可去掉该规范轨道。

本节的 FIB 边界是：递归仅提供合法源词、长度、组合和切点载体；\(K_\vartheta\)、初态、局部速度、阻抗、时间窗、读出噪声与物理单位均由外加模型声明。联合均值—协方差的满秩只给声明模型的局部统计识别，不给全局识别或完整路径律；同一前两阶响应可由不同高阶路径律实现。上述响应、易感性、信息矩阵和规范名称是数学类比，不推出真实物理外场、温度、热流、耗散或普适定律。

## 58. 有限 FIB 核的 Perron 谱扰动与压力曲率

前面的压力和秩判据分别固定了核或只观察一阶均值。本节把有限活跃图上的核扰动写成谱微分，区分压力可见的方向与只能由完整路径读出的方向。

**定理 58.1（简单 Perron 根的二阶响应）。** 令 \(K(\eta)\) 是有限状态上的 primitive 子随机核族，
\[
K(\eta)=K_0+\sum_{a=1}^{d}\eta_a A_a,
\]
并令 \(\rho(\eta)\) 为 Perron 根。取
\[
K_0r=\rho_0r,\qquad
\ell^{\mathsf T}K_0=\rho_0\ell^{\mathsf T},\qquad
\ell^{\mathsf T}r=1,
\]
其中 \(\rho_0=\rho(0)\)。定义 \(P=r\ell^{\mathsf T}\)，并令约化 resolvent \(R\) 满足
\[
(\rho_0I-K_0)R=R(\rho_0I-K_0)=I-P,\qquad
Rr=0,\qquad \ell^{\mathsf T}R=0.
\]
则
\[
\partial_a\rho(0)=\ell^{\mathsf T}A_ar,
\]
且
\[
\partial_{ab}\rho(0)
=\ell^{\mathsf T}
\bigl(A_aRA_b+A_bRA_a\bigr)r.
\]
令 \(\Psi(\eta)=\log\rho(\eta)\)，则
\[
\partial_{ab}\Psi(0)
=\frac{\partial_{ab}\rho(0)}{\rho_0}
-\frac{\partial_a\rho(0)\,\partial_b\rho(0)}{\rho_0^2}.
\]
若 \(K(\eta)\) 还含有非线性项 \(A_{ab}=\partial_{ab}K(0)\)，只需在 \(\partial_{ab}\rho(0)\) 右端加上 \(\ell^{\mathsf T}A_{ab}r\)。

**推论 58.2（倾斜压力与核参数的混合曲率）。** 对有界占用 \(c\) 令
\[
D_\vartheta=\operatorname{diag}(e^{\vartheta c(i)}),\qquad
K_{\vartheta,\eta}=D_\vartheta K(\eta),\qquad
\Psi(\vartheta,\eta)=\log\rho(K_{\vartheta,\eta}).
\]
在 \((0,0)\) 附近保持 primitive 时，\(\partial_\vartheta\Psi\) 是 Perron Doob 核下的长期占用均值，\(\partial_{\vartheta\vartheta}\Psi\) 是该核下的渐近占用方差；混合导数 \(\partial_{\vartheta a}\Psi\) 给出占用压力对第 \(a\) 个核参数的一阶响应。它们均由定理 58.1 的左右 Perron 向量和约化 resolvent 计算。

若参数方向 \(u\in\mathbb R^d\) 满足
\[
\ell^{\mathsf T}\Bigl(\sum_a u_aA_a\Bigr)r=0,
\]
则该方向对 Perron 压力的一阶响应为零；若同时所有给定占用倾斜的混合导数也为零，则任何只读取这些压力的一阶和混合曲率的实验都不能在该阶区分该方向。完整路径、端点分布或其他探针仍可能携带额外信息。

这里 \(A_a\)、初态、倾斜函数和读出协议都是外加模型。FIB 递归只提供状态标签、词序和允许的组合图；谱曲率不自动等于物理易感性、线性响应或能量二阶导数。

## 59. 逆向路径似然比与有限图涨落对称

本节把有限 FIB 图上的正向路径与反向路径放在同一概率空间中，得到一个纯粹的路径似然比恒等式。

**定理 59.1（有限时间逆向路径关系）。** 令 \(Q\) 是有限不可约核，\(\pi\) 是其严格正的平稳律，并假定
\[
Q(i,k)>0\quad\Longleftrightarrow\quad Q(k,i)>0.
\]
对每条有向边定义
\[
a(i,k)=\log\frac{\pi(i)Q(i,k)}{\pi(k)Q(k,i)}.
\]
令 \(X_0,\ldots,X_T\) 从 \(\pi\) 出发，并定义
\[
\mathcal S_T=\sum_{t=0}^{T-1}a(X_t,X_{t+1}).
\]
对路径 \(\omega=(x_0,\ldots,x_T)\) 和反向路径
\(\omega^\leftarrow=(x_T,\ldots,x_0)\)，有
\[
\frac{\mathbb P_\pi(\omega)}
{\mathbb P_\pi(\omega^\leftarrow)}
=e^{\mathcal S_T(\omega)}.
\]
因此对所有可取值 \(s\)，
\[
\mathbb P_\pi(\mathcal S_T=s)
=e^s\mathbb P_\pi(\mathcal S_T=-s).
\]

令
\[
M_\zeta(i,k)=Q(i,k)e^{\zeta a(i,k)},\qquad
\Lambda(\zeta)=\log\rho(M_\zeta).
\]
则
\[
\mathbb E_\pi e^{\zeta\mathcal S_T}
=\pi^{\mathsf T}M_\zeta^T\mathbf1,
\qquad
\Lambda(\zeta)=\Lambda(-1-\zeta).
\]
第二式来自
\[
M_\zeta
=\operatorname{diag}(\pi)^{-1}
M_{-1-\zeta}^{\mathsf T}
\operatorname{diag}(\pi),
\]
故两矩阵相似而有相同谱半径。若 \(Q\) 满足详细平衡，则 \(a(i,k)=0\)，上述随机量恒为零；若双向支撑条件失败，反向路径可能没有有限似然比，需改用扩展值或限制在共同支撑上。

该对称性只描述声明的有限核、平稳初态和反向路径协议。FIB 递归不单独选择 \(Q\)、\(\pi\) 或时间反演规则；\(\mathcal S_T\) 不能直接命名为真实熵产生、热力学不可逆性或任何物理涨落定律。

## 60. FIB 阻抗随机环境的 quenched/annealed Green 同质化

固定逐字斐波那契词 \(W_j\)、\(L_j=F_{j+1}\)、\(N_j=F_{j+3}\)、\(\epsilon_j=\delta/N_j^2\) 及左反射右吸收切链。令
\[
r_{\min}=\min(r_\alpha,r_\beta),
\]
在外加环境 \(\xi=(\xi_k)_{k\ge0}\) 上取独立同分布扰动，满足
\[
\mathbb E\xi_0=0,\qquad
\operatorname{Var}(\xi_0)=\sigma^2,\qquad
|\xi_k|\le\eta<r_{\min},
\qquad
\theta\le\frac{r_{\min}-\eta}{2}.
\]
定义静态环境阻抗
\[
r_{j,k}^{\omega}=r_{(W_j)_k}+\xi_k.
\]
FIB 只给 \(W_j\)、词序、长度和确定性机械不差分；\(\xi\)、核、时钟和边界均为外加。

**定义与精确恒等式。** 条件于 \(\omega\) 的暂态 Green 矩阵满足
\[
G_j^\omega(i,m)
=\frac1\theta\sum_{k=\max(i,m)}^{L_j-1}
\bigl(r_{(W_j)_k}+\xi_k\bigr).
\]
令
\[
\mathcal K_j^\omega(u,v)
=\epsilon_jL_jG_j^\omega(\iota_j(u),\iota_j(v)),
\qquad
c_j=\frac{\epsilon_jL_j}{\theta},
\]
并令 \(M_L(\omega)\) 为所有区间扰动和的最大绝对值：
\[
M_L(\omega)=\max_{0\le a\le b\le L}
\left|\sum_{k=a}^{b-1}\xi_k\right|.
\]
则
\[
\mathcal K_j^\omega(u,v)-\mathcal K_j^0(u,v)
=c_j\sum_{k=\max(\iota_j(u),\iota_j(v))}^{L_j-1}\xi_k,
\]
从而
\[
\sup_{u,v}|\mathcal K_j^\omega-\mathcal K_j^0|
\le c_jM_{L_j}(\omega).
\]
结合确定性 FIB 机械不差分估计，得到
\[
\sup_{u,v}|\mathcal K_j^\omega-\mathcal K(u,v)|
\le \frac{C_F}{L_j}+c_jM_{L_j}(\omega),
\qquad
c_j=\frac{\delta}{\theta\varphi^4L_j}+O(L_j^{-3}).
\]

**定理 60.1（quenched 极限与高概率误差）。** 独立有界扰动满足区间形式的强大数律
\[
\frac{M_L}{L}\longrightarrow0\qquad\text{几乎处处}.
\]
故对几乎所有静态环境，
\[
\mathcal K_j^\omega\longrightarrow
\mathcal K_{\mathrm{ar}}(u,v)
=\frac{1-\max(u,v)}{D},
\qquad
D=\frac{\theta\varphi^4}{\delta\bar r},
\qquad
\bar r=\varphi^{-2}r_\alpha+\varphi^{-1}r_\beta,
\]
在 \([0,1]^2\) 一致成立。若用 Hoeffding 不等式并对至多 \(L^2\) 个区间并合，则
\[
\mathbb P(M_L\ge t)
\le2L^2\exp\left(-\frac{t^2}{2L\eta^2}\right).
\]
因而以概率至少 \(1-2e^{-x}\)，随机同质化误差的环境部分为
\[
\sup|\mathcal K_j^\omega-\mathcal K_j^0|
\le c_j\eta
\sqrt{2L_j\bigl(\log(2L_j^2)+x\bigr)}.
\]
这给出 \(O(\sqrt{(\log L_j+x)/L_j})\) 的高概率量级；仅有遍历性而无区间函数极限定理的环境仍可给极限，但不自动给此速率或高斯涨落。

**定理 60.2（annealed 均值与 quenched 中心极限）。** 定义静态环境的 annealed Green 为
\[
\overline{\mathcal K}_j=\mathbb E_\omega\mathcal K_j^\omega.
\]
由于 Green 尾和对阻抗线性且 \(\mathbb E\xi_0=0\)，有精确恒等式
\[
\overline{\mathcal K}_j=\mathcal K_j^0,
\qquad
\sup|\overline{\mathcal K}_j-\mathcal K|=O(L_j^{-1}).
\]
若 \(\xi_k\) 独立同分布且有限方差，并采用线性插值，在标准紧性条件下
\[
\sqrt{L_j}\bigl(\mathcal K_j^\omega-\overline{\mathcal K}_j\bigr)
\Rightarrow
\mathscr B(u,v)
=\frac{\delta\sigma}{\theta\varphi^4}
\bigl[B(1)-B(\max(u,v))\bigr]
\]
有限维收敛；若把 \(\xi\) 的部分和作线性插值并满足 Donsker 紧性条件，则在 \(C([0,1]^2)\) 的一致拓扑下收敛。其协方差为
\[
\operatorname{Cov}(\mathscr B(u,v),\mathscr B(u',v'))
=\left(\frac{\delta\sigma}{\theta\varphi^4}\right)^2
\bigl[1-\max\{u,v,u',v'\}\bigr].
\]
该极限只描述静态环境造成的 Green 随机性，尚未加入链路径鞅噪声。

**命题 60.3（两种 annealed 操作不可混同）。** 真正静态环境的 annealed 占用均值是 \(\mathbb E_\omega G_j^\omega\)，而
\[
G(\mathbb E_\omega K_j^\omega)
\]
是先平均一步核后再求 Green 的另一模型；一般
\[
\mathbb E_\omega(I-K_j^\omega)^{-1}
\ne (I-\mathbb E_\omega K_j^\omega)^{-1}.
\]
若各边环境独立同分布，令
\[
\widetilde r_\ell
=\left(\mathbb E[(r_\ell+\xi_0)^{-1}]\right)^{-1},
\qquad
\bar r_{\mathrm{harm}}
=\varphi^{-2}\widetilde r_\alpha
+\varphi^{-1}\widetilde r_\beta.
\]
则 \(\mathbb E_\omega K_j^\omega\) 对应于阻抗 \(\widetilde r_{(W_j)_k}\) 的确定性切链，其缩放极限为
\[
\mathcal K_{\mathrm{harm}}(u,v)
=\frac{\delta\bar r_{\mathrm{harm}}}{\theta\varphi^4}
\bigl(1-\max(u,v)\bigr).
\]
由 Jensen，
\[
\widetilde r_\ell\le\mathbb E(r_\ell+\xi_0)=r_\ell,
\]
严格非退化噪声时至少一项严格，故 harmonic 模型与 arithmetic 静态平均模型在内点不同。静态环境先抽取一次再对路径积分的真正 annealed 路径一般不是 Markov；\(G(\mathbb E_\omega K_j^\omega)\) 对应的是逐步重抽或平均一步的替代模型，只有在额外重抽协议下才具有该含义。

若扰动具有长程相关或重尾，误差率和极限可能改变；若 \(\mathbb E\xi_0\ne0\) 或均值依赖字母，也必须相应修改 \(\bar r\)。Green 极限、\(D\) 及其扩散类比均属于声明模型，不推出真实物理热流、温度或普适定律。

## 61. 杀死链的极值、首达尾与稀有事件谱律

令 \(S\) 为有限活跃集，\(K\) 为 primitive 子随机核，杀死态记为 \(\partial\)，Perron 根为 \(\rho\)，左右向量 \(r,\ell\) 满足 \(\ell^{\mathsf T}r=1\)。令
\[
\widehat K(i,k)=\frac{K(i,k)r(k)}{\rho r(i)}
\]
为 Doob 核。给定观测 \(g:S\to\mathbb R\)、阈值 \(u\)，定义
\[
A_u=\{i:g(i)>u\},\qquad
S_u=S\setminus A_u,\qquad
K_u=K|_{S_u\times S_u}.
\]

**定理 61.1（有限时间极值与首达谱率）。** 令
\[
M_T=\max_{0\le t\le T}g(X_t),\qquad
\tau_\partial=\inf\{t\ge1:X_t=\partial\}.
\]
若初态律 \(\nu\) 支持于 \(S_u\)，则
\[
\mathbb P_\nu(M_T\le u,\tau_\partial>T)
=\nu^{\mathsf T}K_u^T\mathbf1,
\]
并且若
\[
b_{A_u}(i)=\sum_{a\in A_u}Q(i,a),
\]
则
\[
\mathbb P_\nu(\tau_{A_u}=n+1<\tau_\partial)
=\nu^{\mathsf T}K_u^n b_{A_u}.
\]
若 \(K_u\) primitive、\(\rho_u=\rho(K_u)\)，则
\[
\lim_{T\to\infty}\frac1T
\log\mathbb P_\nu(M_T\le u,\tau_\partial>T)
=\log\rho_u,
\]
而条件存活极值率为
\[
\lim_{T\to\infty}\frac1T
\log\mathbb P_\nu(M_T\le u\mid\tau_\partial>T)
=\log\rho_u-\log\rho.
\]
在 Doob 核下同一比值写成
\[
\widehat\rho_u=\frac{\rho_u}{\rho},
\]
即避开 \(A_u\) 的长期率为 \(\log\widehat\rho_u\)。谱隙
\[
\eta_u=\max_{m\ge1}\frac{|\lambda_{u,m}|}{\rho_u}<1
\]
还给出 Perron 首项和 \(O(\eta_u^T)\) 的相对修正；周期或可约时须改用周期子列或最大强连通分量。

**定理 61.2（稀有极值与聚簇系数）。** 在 Doob 核的平稳律 \(\widehat\pi\) 下，令稀有集合 \(A_n=\{g>u_n\}\)，
\[
\alpha_n=\widehat\pi(A_n)\longrightarrow0.
\]
记
\[
\widehat\rho_{A_n}
=\rho\!\left(\widehat K|_{A_n^c\times A_n^c}\right).
\]
若存在混合滞后 \(r_n\to\infty\) 使远程相关小于 \(o(\alpha_n)\)，且近程回返满足
\[
b_n=\sum_{t=1}^{r_n}
\mathbb P_{\widehat\pi}(X_0\in A_n,X_t\in A_n)
=o(\alpha_n),
\]
则在 \(T_n\alpha_n\to\tau\) 时，
\[
\mathbb P_{\widehat\pi}
\left(\max_{0\le t<T_n}g(X_t)\le u_n\right)
\longrightarrow e^{-\tau}.
\]
若允许近程聚簇，令
\[
\theta_n=
\mathbb P_{\widehat\pi(\cdot\mid A_n)}
\bigl(\tau_{A_n}^{+}>r_n\bigr)
\longrightarrow\theta\in[0,1],
\]
并保持远程混合条件，则
\[
-\log\widehat\rho_{A_n}
=\theta_n\alpha_n(1+o(1)),
\]
极值律改为 \(e^{-\theta\tau}\)。\(\theta<1\) 表示一次命中伴随多个近程命中。

二周期核
\[
\begin{pmatrix}0&1\\1&0\end{pmatrix}
\]
取 \(A=\{0\}\) 时没有混合，命中事件确定交替，不能套用 \(e^{-\tau}\)。若稀有态满足 \(\widehat K(a,a)=1-\varepsilon\)，则回返形成几何簇，\(\theta\) 约为 \(\varepsilon\) 而非 \(1\)。若 \(\widehat\pi_{\min}\) 或谱隙随 FIB 层数退化，也不能宣称统一极值律。

固定有限 \(S\) 和固定 \(g\) 只有有限阈值层；非平凡 \(u_n\) 必须让 \(g_n\)、阈值和图大小共同变化。FIB 递归只给词序、长度、组合和标签；\(K\)、初态、\(g\)、阈值、时钟、Doob 协议和稀有集合均为外加。极值率和聚簇系数不自动是自由能、温度、熵产生或普适物理参数。

## 62. FIB 标签观测通道的贝叶斯滤波、可预测性与隐状态可识别性

本节把 FIB 递归给出的有限状态标签送入一个声明的观测通道。FIB 只提供状态集合、词序、长度与组合索引以及状态标签函数；转移核、初态律、观测噪声、时钟和先验均为外加模型。

**定义 62.1（外加的隐状态与观测核）。** 令 \(S\) 为由有限 FIB 切点或标签索引的有限集合，\(Q(i,j)\) 为行随机核，\(\nu\) 为 \(X_0\) 的初态律。令 \(\mathcal Y\) 为有限观测字母表，\(O_i(y)\ge0\)、\(\sum_yO_i(y)=1\) 为观测核，并假定给定 \(X_{0:T}\) 时 \(Y_t\) 条件独立且
\[
\Pr(Y_t=y\mid X_t=i)=O_i(y).
\]
若 \(U_t=g(X_t)\) 是 FIB 标签读出，则 \(g\) 也是外加的可观测函数。记
\[
D_y=\operatorname{diag}(O_i(y))_{i\in S},\qquad
\mathbf1=(1,\ldots,1)^{\mathsf T}.
\]
对观测历史 \(y_{0:t}\) 定义后验行向量
\[
\alpha_t(i)=\Pr_\nu(X_t=i\mid Y_{0:t}=y_{0:t}),
\qquad
\beta_{t+1}=\alpha_tQ.
\]
在分母非零时，Bayes 更新为
\[
\alpha_{t+1}(k)
=\frac{\beta_{t+1}(k)O_k(y_{t+1})}
{\sum_j\beta_{t+1}(j)O_j(y_{t+1})}
=\frac{(\beta_{t+1}D_{y_{t+1}})_k}
{\beta_{t+1}D_{y_{t+1}}\mathbf1}.
\]
零概率历史上的后验可任意定义，不影响几乎处处结论。

**定理 62.2（滤波递归与预测充分性）。** 对任意 \(n\ge1\)，给定 \(Y_{0:t}\)，未来观测词的条件律为
\[
\Pr(Y_{t+1:t+n}=z_{1:n}\mid Y_{0:t})
=\alpha_tQD_{z_1}QD_{z_2}\cdots QD_{z_n}\mathbf1.
\]
故 \(\alpha_t\) 是未来观测的预测充分统计量：若两段历史产生同一 \(\alpha_t\)，则它们对所有有限未来词给出同一概率。一步预测分布为
\[
\bar O_{\beta_{t+1}}(y)=\sum_i\beta_{t+1}(i)O_i(y),
\qquad
\Pr(Y_{t+1}=y\mid Y_{0:t})=\bar O_{\beta_{t+1}}(y).
\]
初态似然为
\[
\Pr_\nu(Y_{0:T}=y_{0:T})
=\nu D_{y_0}QD_{y_1}\cdots QD_{y_T}\mathbf1.
\]
创新对数得分是这些预测概率的逐步和，不是 FIB 递归自身给出的量。

**定理 62.3（一步观测信息与熵分解）。** 令 \(\mathscr Y_t=\sigma(Y_0,\ldots,Y_t)\)，\(\beta_{t+1}=\Pr(X_{t+1}\in\cdot\mid\mathscr Y_t)\)，并记 \(h(p)=-\sum_y p(y)\log p(y)\)。则
\[
H(Y_{t+1}\mid\mathscr Y_t)
=\mathbb E\,h(\bar O_{\beta_{t+1}}),
\]
且
\[
\begin{aligned}
I(X_{t+1};Y_{t+1}\mid\mathscr Y_t)
&=H(Y_{t+1}\mid\mathscr Y_t)-H(Y_{t+1}\mid X_{t+1})\\
&=\mathbb E\sum_i\beta_{t+1}(i)
D_{\rm KL}\!\left(O_i\middle\|\bar O_{\beta_{t+1}}\right)\\
&=H(X_{t+1}\mid\mathscr Y_t)-H(X_{t+1}\mid\mathscr Y_{t+1})\ge0.
\end{aligned}
\]
零值当且仅当对几乎处处历史，所有 \(\beta_{t+1}(i)>0\) 的状态给出相同的观测分布。

**定理 62.4（正观测通道下的初态遗忘）。** 假定存在 \(\varepsilon>0\)，使所有 \(Q(i,j)\ge\varepsilon\)、\(O_i(y)\ge\varepsilon\)。对同一观测串，用
\[
\mathsf F_y(\alpha)=\frac{\alpha QD_y}{\alpha QD_y\mathbf1}
\]
迭代任意两个全支撑初始后验，则存在依赖于 \(\varepsilon\) 和 \(|S|\) 的 \(C<\infty\)、\(0<\kappa<1\)，使
\[
\left\|
\mathsf F_{y_t}\circ\cdots\circ\mathsf F_{y_1}(\alpha)
-\mathsf F_{y_t}\circ\cdots\circ\mathsf F_{y_1}(\alpha')
\right\|_1
\le C\kappa^t.
\]
这是正矩阵乘积的 Hilbert 距离收缩及有限维范数等价的结果。仅有可达性而无正性时，周期、零支撑和观测不可区分类必须另行处理。

**推论 62.5（观测熵率与创新得分）。** 若 \(Q\) 以平稳律 \(\pi\) 初始化且隐链遍历，则输出过程平稳；有限字母下熵率
\[
h_Y=\lim_{T\to\infty}T^{-1}H(Y_0^{T-1})
\]
存在。若再满足定理 62.4 的正性，有限历史滤波器收敛到平稳全历史滤波器；记其一步预测后验为 \(\beta_0^\infty\)，则
\[
h_Y
=\mathbb E\,h(\bar O_{\beta_0^\infty})
=\lim_{T\to\infty}\frac1T
\sum_{t=0}^{T-1}\mathbb E[-\log\bar O_{\beta_t}(Y_{t+1})].
\]
故熵率是长期贝叶斯创新的平均对数损失。

**推论 62.6（转移熵是滤波预测的 KL 差）。** 在平稳模型中，令
\[
\mathcal Y_-=\sigma(Y_{-\infty:-1}),\qquad
\mathcal U_-=\sigma(U_{-\infty:-1}),
\]
并定义
\[
\beta=\Pr(X_0\in\cdot\mid\mathcal Y_-),\qquad
\beta^U=\Pr(X_0\in\cdot\mid\mathcal Y_-,\mathcal U_-).
\]
若 \(U_t=g(X_t)\)，则
\[
T_{U\to Y}^{(\infty)}
=\mathbb E\,D_{\rm KL}
\!\left(\bar O_{\beta^U}\middle\|\bar O_\beta\right)\ge0.
\]
并且
\[
T_{U\to Y}^{(\infty)}
\le I(X_0;Y_0\mid\mathcal Y_-).
\]
等号需要 \(U\) 的过去保留 \(X_0\) 对 \(Y_0\) 的全部相关预测信息，一般不成立。

**定义 62.7（隐状态的观测等价）。** 对有限未来词 \(w=y_0\ldots y_{n-1}\)，定义从状态 \(i\) 出发的观测词概率
\[
W_n(i,w)
=e_i^{\mathsf T}D_{y_0}QD_{y_1}\cdots QD_{y_{n-1}}\mathbf1.
\]
称 \(i\sim_{\rm obs}j\) 当且仅当对所有 \(n\ge1\) 和所有 \(w\in\mathcal Y^n\)，
\[
W_n(i,w)=W_n(j,w).
\]
令 \(\mathcal V\) 为包含 \(\mathbf1\) 且对所有 \(D_yQ\) 不变的最小线性子空间，则
\[
i\sim_{\rm obs}j
\quad\Longleftrightarrow\quad
(e_i-e_j)^{\mathsf T}v=0\quad(\forall v\in\mathcal V).
\]
由于 \(\dim\mathcal V\le|S|\)，该等价性可由有限维线性代数检验。对初态 \(\nu,\nu'\)，所有未来观测律相同当且仅当
\[
(\nu-\nu')^{\mathsf T}\mathcal V=0.
\]

**推论 62.8（可观测分块与不可识别方向）。** 若分割 \(c:S\to C\) 满足对同一类内任意 \(i,j\) 及每个类 \(C'\)，
\[
\sum_{k:c(k)=C'}Q(i,k)
=\sum_{k:c(k)=C'}Q(j,k),
\]
且 \(O_i=\bar O_{c(i)}\)，则 \(c(X_t)\) 是 Markov 链，输出律仅由分块核与 \(\bar O\) 决定；类内速度、阻抗或初态重新分配无法由 \(Y\) 识别。该 lumpability 条件是充分条件，不是所有观测等价的必要条件。

**推论 62.9（Hankel 预测维数的上界）。** 对有限词 \(u,v\) 令
\[
H_{u,v}=\Pr(Y_{0:|u|+|v|-1}=uv).
\]
按前缀后的隐藏后验行向量与后缀的条件概率列向量定义 \(r_u,c_v\)，则
\[
H_{u,v}=r_uc_v,\qquad
\operatorname{rank}H\le|S|.
\]
若可达后验与观测延续空间均为全维，则线性预测维数达到 \(|S|\)；若秩更低，任何输出序列统计都不能提供同样数量的独立隐状态方向。

FIB 边界是：递归只提供可编号的状态标签、词序与组合结构；\(Q,\nu,O\)、平稳初态、正性条件、先验和噪声均由外加模型声明。贝叶斯滤波给出声明模型中的后验与预测充分性，熵率给出输出序列的长期编码量，转移熵给出加入另一段历史后的预测 KL 增益；这些量不能自动推出真实物理中的测量、温度、熵产生、因果流、能量或普适定律。

## 63. 随机环境下杀死半群的 quenched/annealed 谱与两尺度极限

本节把环境明确作为外加随机过程。FIB 递归只提供有限状态的词序、长度、组合索引和阻抗标签；环境、杀死核、初态、时钟和读出协议均不由递归决定。

**定义 63.1（quenched 与 annealed 半群）。** 令 \(S\) 为有限暂态状态集，\(K_\eta\) 为环境状态 \(\eta\) 下的非负子随机核，行和不超过一。对环境序列 \(\eta_0,\eta_1,\ldots\) 定义

\[
P_n^\eta=K_{\eta_0}K_{\eta_1}\cdots K_{\eta_{n-1}},
\qquad
Z_n^\eta(\nu)=\nu^{\mathsf T}P_n^\eta\mathbf 1,
\qquad
G_z^\eta=\sum_{n\ge0}z^nP_n^\eta .
\]

若环境平稳遍历、\(\log^+\|K_\eta\|\) 可积，并且这些核在共同锥上满足不可约性与适当正性，则次可加遍历定理给出几乎处处存在的常数

\[
\lambda_q=\lim_{n\to\infty}\frac1n\log\|P_n^\eta\|.
\]

在初态全支撑且正性足以比较 \(Z_n^\eta\) 与矩阵范数时，\(n^{-1}\log Z_n^\eta\) 具有同一极限。定义 annealed 率为

\[
\lambda_a=\limsup_{n\to\infty}\frac1n\log\mathbb E Z_n^\eta .
\]

若 \(n^{-1}\mathbb E\log Z_n^\eta\to\lambda_q\)，Jensen 不等式给出

\[
\lambda_q\le
\liminf_{n\to\infty}\frac1n\log\mathbb E Z_n^\eta,
\]

从而在 annealed 极限存在时 \(\lambda_q\le\lambda_a\)。quenched Green 矩阵的指数半径为 \(R_q=e^{-\lambda_q}\)，但它与先取环境平均再求逆的半径一般不同。

**定理 63.2（环境协议决定平均 resolvent）。** 若 \(\eta_t\) 独立同分布，令 \(\overline K=\mathbb E K_\eta\)，则

\[
\mathbb E P_n^\eta=\overline K^{\,n},
\qquad
G_a(z):=\sum_{n\ge0}z^n\mathbb E P_n^\eta
=(I-z\overline K)^{-1}
\]

在该级数收敛域内；当 \(\overline K\) primitive 时，\(\lambda_a=\log\rho(\overline K)\)。这一步使用的是逐时刻独立性。若只在初时抽取一次静态环境，则

\[
G_a^{\rm stat}(z)=\mathbb E\,(I-zK_\eta)^{-1},
\]

一般不等于 \((I-z\mathbb E K_\eta)^{-1}\)。例如标量环境 \(k_t\in\{0.1,0.9\}\) 等概率时，逐时刻独立给出

\[
\lambda_q=\tfrac12(\log0.1+\log0.9)=\log0.3,
\qquad
\lambda_a=\log0.5,
\]

而一次静态抽样给出每个实现的率 \(\log k\)、静态 annealed 生存率 \(\log0.9\)，以及

\[
G_a^{\rm stat}(z)=\tfrac12\frac1{1-0.1z}+\tfrac12\frac1{1-0.9z}.
\]

若环境是马尔可夫链，不能把 \(\mathbb E K_{\eta_t}\) 逐步相乘。给定环境转移矩阵 \(A(e,f)\)，并约定先用 \(K_e\) 从 \(i\) 到 \(j\)，再由 \(e\) 到 \(f\)，联合子核为

\[
J_{(i,e),(j,f)}=K_e(i,j)A(e,f).
\]

于是 annealed resolvent 是 \((q\otimes I)(I-zJ)^{-1}(\mathbf1\otimes I)\) 的投影；除非投影闭合，否则不存在只在 \(S\) 上的单一有效核。

**定理 63.3（快速环境的两尺度响应）。** 令环境集 \(E\) 有限，\(B\) 是不可约、具有谱隙的环境生成器，平稳律为 \(\pi\)，并令 \(L_e\) 是状态集 \(S\) 上的有界杀死生成器。环境以速率 \(B/\varepsilon\) 独立切换时，联合生成器为

\[
\mathcal L_\varepsilon=\varepsilon^{-1}B\otimes I+\operatorname{diag}_{e\in E}L_e,
\qquad
\overline L=\sum_{e\in E}\pi_eL_e .
\]

在初始环境取 \(\pi\)、有限时间窗 \([0,T]\) 和有限维有界性条件下，对任意状态探针 \(f\) 有

\[
\sup_{0\le t\le T}
\left|(\nu\otimes\pi)e^{t\mathcal L_\varepsilon}(\mathbf1_E\otimes f)
-\nu e^{t\overline L}f\right|\le C_T\varepsilon,
\]

至少有同样的无速率收敛结论。故对 \(w\in L^1[0,T]\)，窗口响应满足

\[
\int_0^Tw(t)(\nu\otimes\pi)e^{t\mathcal L_\varepsilon}
(\mathbf1_E\otimes f)\,dt
\longrightarrow
\int_0^Tw(t)\nu e^{t\overline L}f\,dt .
\]

在慢子空间的识别下，对 \(\lambda>0\) 还有投影 resolvent 收敛

\[
(\pi\otimes I)(\lambda I-\mathcal L_\varepsilon)^{-1}
(\mathbf1_E\otimes I)
\longrightarrow
(\lambda I-\overline L)^{-1}.
\]

快速平均不表示任意有限切换频率都等于简单平均。周期交替时，Baker–Campbell–Hausdorff 展开给出

\[
L_{\rm eff}=
\frac1{2\delta}\log(e^{\delta L_1}e^{\delta L_2})
=\tfrac12(L_1+L_2)+\tfrac\delta4[L_1,L_2]+O(\delta^2).
\]

静态或慢环境的极限一般是 \(\mathbb E e^{tL_\eta}\) 或联合状态空间上的半群，而不是 \(e^{t\overline L}\)；环境依赖于状态时还需条件不变律；无谱隙或重尾停留会引入记忆并可能失去确定的平稳投影。固定切换尺度的长期 quenched 率与先取快速极限的有限窗率也不能无条件交换。上述谱、resolvent 和均质化结论属于外加随机模型，不能解释为 FIB 递归自动产生的真实物理定律。

## 64. FIB 类型递归的多型计数、标记奖励与路径谱

本节先假定所讨论的 FIB 词在一个有限上下文闭包内；若上下文无限或替换不闭合，有限矩阵 Perron 结论不能直接套用。

**定理 64.1（有限类型的 Perron 计数）。** 令有限类型集为 \(\mathcal T\)，每种类型替换产生的子类型数由非负矩阵 \(A\) 给出。若 \(A\) primitive，令 \(\rho=\rho(A)\)，右、左 Perron 向量分别为 \(r,\ell\)，归一化为 \(\ell^{\mathsf T}r=1\)。从初始计数行向量 \(\nu^{\mathsf T}\) 出发，\(Z_n=\nu^{\mathsf T}A^n\)，则

\[
\rho^{-n}A^n\longrightarrow r\ell^{\mathsf T},
\qquad
\rho^{-n}Z_n\longrightarrow(\nu^{\mathsf T}r)\ell^{\mathsf T}.
\]

对任意类型奖励列向量 \(c\)，只要 \(\nu^{\mathsf T}r>0\)，有

\[
\frac{Z_nc}{Z_n\mathbf1}
\longrightarrow
\frac{\ell^{\mathsf T}c}{\ell^{\mathsf T}\mathbf1}.
\]

例如，若某个有限闭包恰为 \(\alpha\mapsto\alpha\beta\)、\(\beta\mapsto\alpha\)，则

\[
A=\begin{pmatrix}1&1\\1&0\end{pmatrix},
\qquad \rho=\varphi.
\]

从单个 \(\alpha\) 出发，总数按 \(C\varphi^n\) 增长；极限类型比例为 \(\alpha:\beta=\varphi^{-1}:\varphi^{-2}\)。这只是该闭包的计数结论，不能把任意 FIB 递归直接替换成这个矩阵。

**定理 64.2（外加多型分枝与 many-to-one）。** 令每个类型 \(i\) 的子代向量服从外加分枝律，均值矩阵为 primitive 的 \(M\)，\(\rho(M)>1\)。在标准非退化条件和 \(\mathbb E[\xi_i\log^+\xi_i]<\infty\) 条件下，若 \(Z_n\) 是第 \(n\) 代类型计数行向量，则

\[
W_n=\rho(M)^{-n}Z_nr
\]

是非负鞅并收敛到 \(W\)；在存活事件上，\(\rho^{-n}Z_n\to W\ell^{\mathsf T}\)。若对每个从 \(i\) 出发的子代边赋予奖励 \(G_{i,k}\)，定义直接的倾斜均值矩阵

\[
M_\vartheta(i,j)=
\mathbb E_i\!\left[\sum_{k:\,\mathrm{type}(k)=j}
e^{\vartheta G_{i,k}}\right],
\qquad
\psi(\vartheta)=\log\rho(M_\vartheta).
\]

这里不假定子代数目与奖励独立；直接使用联合期望才覆盖相关情形。若 \(M_\vartheta\) 在邻域内保持 primitive 且具有指数矩，\(\psi'(0)\) 是相应 spine 路径的平均奖励率，\(\psi''(0)\) 是含边奖励自协方差的长期方差，并在常规非退化条件下给出路径 CLT 与奖励大偏差的 Legendre 率函数。

倾斜后的 spine 核可写为

\[
P_\vartheta(i,j)=
\frac{M_\vartheta(i,j)r_\vartheta(j)}
{\rho_\vartheta r_\vartheta(i)},
\]

其中 \(r_\vartheta\) 是 \(M_\vartheta\) 的右 Perron 向量；其平稳律加权的边奖励给出 \(\psi'(\vartheta)\)。many-to-one 公式把期望的系谱和化为该 spine 链的路径期望，但它描述的是期望和，不是随机树中均匀粒子的典型律。

相同的均值矩阵不决定二阶系谱统计。单型时取均值 \(M=[2]\)：模型一每个个体恒生两个子代，模型二以概率一半生零个、以概率一半生四个，二者均值和 Perron 增长相同；但灭绝概率、极限变量方差、最近共同祖先分布和奖励协方差不同。因此，FIB 的确定性计数至多固定一阶矩阵谱；分枝噪声、独立性、标记和观测均是额外结构，不能由计数递归自动推出。

## 65. 不同初态与核的共同耦合、混合稳定性及不可辨识边界

本节固定有限 FIB 状态载体 \(S\)。递归只提供状态标签、词序、长度和组合索引；初态律、转移核、状态度量、共同随机源、观测通道及参数化均为外加声明。对杀死链，可把暂态子核增广到 \(S\cup\{\dagger\}\)，令 \(\dagger\) 为吸收态。

**定理 65.1（有限时域的共同源耦合界）。** 令 \(Q,\widetilde Q\) 是同一状态集上的两个核，\(\nu,\widetilde\nu\) 是初态律，并记

\[
\varepsilon_0=\operatorname{TV}(\nu,\widetilde\nu),
\qquad
\varepsilon_Q=\sup_i\operatorname{TV}(Q(i,\cdot),\widetilde Q(i,\cdot)).
\]

在初态和每个共同状态上取最大耦合，未分歧前用同一组外加随机源驱动，并令 \(\tau_c=\inf\{t:X_t\ne\widetilde X_t\}\)。则

\[
\Pr(\tau_c>T)\ge(1-\varepsilon_0)(1-\varepsilon_Q)^T,
\]

从而路径律满足

\[
\operatorname{TV}(P_{0:T}^{\nu,Q},P_{0:T}^{\widetilde\nu,\widetilde Q})
\le1-(1-\varepsilon_0)(1-\varepsilon_Q)^T
\le\varepsilon_0+T\varepsilon_Q.
\]

任意标签或噪声观测是路径律的推前，数据处理不等式保持同一上界；有界路径泛函 \(F\) 的期望差至多为 \(2\|F\|_\infty\) 乘以上述总变差界。证明只用最大耦合在每一步的条件不分歧概率至少为 \(1-\varepsilon_Q\)，再作乘法归纳。

**定理 65.2（Wasserstein 收缩与探针响应）。** 给 \(S\) 一个外加有限度量 \(d\)，假定两核均以同一 \(\kappa<1\) 满足 Wasserstein 收缩。置

\[
\eta_0=W_d(\nu,\widetilde\nu),
\qquad
\eta=\sup_iW_d(Q(i,\cdot),\widetilde Q(i,\cdot)).
\]

则 \(\delta_t=W_d(\nu Q^t,\widetilde\nu\widetilde Q^t)\) 满足

\[
\delta_t\le\kappa^t\eta_0+\eta\frac{1-\kappa^t}{1-\kappa};
\]

当 \(\kappa=1\) 时改为 \(\eta_0+t\eta\)。因此对 \(L\)-Lipschitz 探针 \(h\)，有 \(|\mathbb Eh(X_t)-\mathbb Eh(\widetilde X_t)|\le L\delta_t\)；对 \(A_T=\sum_{t=0}^Ta_th(X_t)\)，有

\[
|\mathbb EA_T-\mathbb E\widetilde A_T|
\le L\sum_{t=0}^T|a_t|\delta_t.
\]

若两核有不变律 \(\pi,\widetilde\pi\)，则令 \(t\to\infty\) 得 \(W_d(\pi,\widetilde\pi)\le\eta/(1-\kappa)\)。总变差 Dobrushin 系数 \(\alpha<1\) 下有相应的 \(\operatorname{TV}(\pi,\widetilde\pi)\le\varepsilon_Q/(1-\alpha)\)。这些是外加核的混合稳定性。

**定理 65.3（参数路径的 score 敏感性）。** 对固定支撑的 \(C^1\) 族 \((\nu_\theta,Q_\theta)\)，有

\[
\partial_a(\nu_\theta Q_\theta^T)
=\nu'_aQ^T+\sum_{s=0}^{T-1}
\nu Q^sQ'_aQ^{T-1-s}.
\]

路径分数

\[
S_a=\partial_a\log\nu_\theta(X_0)
+\sum_{t=0}^{T-1}\partial_a\log Q_\theta(X_t,X_{t+1})
\]

满足 \(\mathbb ES_a=0\)，且任意固定路径泛函 \(F\) 有

\[
\partial_a\mathbb EF=\mathbb E(FS_a)
=\operatorname{Cov}(F,S_a),
\qquad
|\partial_a\mathbb EF|
\le\sqrt{\operatorname{Var}(F)\,I_a},
\quad I_a=\mathbb ES_a^2.
\]

若支撑随参数变化或出现零转移，不能无条件使用对数 score；应回到路径密度的直接差分或总变差界。

**命题 65.4（观测推前与不可辨识）。** 对任意标签或含噪通道 \(O_T\)，令 \(P_T^O=O_{T\#}P_T\)，则

\[
\operatorname{TV}(P_T^O,\widetilde P_T^O)
\le\operatorname{TV}(P_T,\widetilde P_T).
\]

若通道对路径度量为 \(L\)-Lipschitz，则 Wasserstein 距离也至多乘以 \(L\)。一般没有逆向下界，因此观测律只确定 \((\nu,Q)\) 的观测商类。若完整状态路径可见、\(T\ge1\) 且 \(\nu(i)>0\) 对所有 \(i\) 成立，则

\[
\nu(i)=\Pr(X_0=i),
\qquad
Q(i,j)=\Pr(X_1=j\mid X_0=i)
\]

唯一恢复 \(\nu,Q\)；只观测端点、标签或未到达状态时，核行和初态方向可保持不可辨。

一个显式反例是 \(S=\{0,1,2,3\}\)，标签 \(g(0)=g(1)=A\)、\(g(2)=g(3)=B\)。取

\[
Q:\;0\to(0,2)=\tfrac12(1,1),\;1\to(1,3)=\tfrac12(1,1),
\quad 2\to(0,2)=\tfrac14(1,3),\;3\to(1,3)=\tfrac14(1,3),
\]

而 \(\widetilde Q\) 把每一行的隐藏状态对调：

\[
0\to(1,3)=\tfrac12(1,1),\;1\to(0,2)=\tfrac12(1,1),
\quad 2\to(1,3)=\tfrac14(1,3),\;3\to(0,2)=\tfrac14(1,3).
\]

取 \(\nu=\delta_0\)、\(\widetilde\nu=\delta_1\)。每个 \(A\) 类状态到 \((A,B)\) 的概率都是 \((1/2,1/2)\)，每个 \(B\) 类状态到 \((A,B)\) 的概率都是 \((1/4,3/4)\)，所以两模型的完整标签路径律相同，而隐藏初态和核不同。这个例子说明观测压缩可以把总变差距离降为零；FIB 递归本身不选择可辨识的观测通道。

## 66. 有界占用泛函的 Poisson 方程、停止鞅与非渐近浓缩

令 \(Q\) 是有限杀死链的暂态子核，假定 \(\sup_i\sum_jQ(i,j)\le q<1\)，令 \(\tau\) 为吸收时间，\(f:S\to\mathbb R\) 有界，并定义

\[
A_\tau=\sum_{t=0}^{\tau-1}f(X_t),
\qquad
h=(I-Q)^{-1}f=\sum_{n\ge0}Q^nf.
\]

于是 \(h(i)=\mathbb E_iA_\tau\)，且 \(\|h\|_\infty\le\|f\|_\infty/(1-q)\)。令 \(h(\dagger)=0\)，对 \(N\ge1\) 定义

\[
M_N=\sum_{t<\tau\wedge N}
\bigl(h(X_{t+1})-h(X_t)+f(X_t)\bigr).
\]

由 \((I-Q)h=f\)，\((M_N)\) 是停止鞅，且每个增量绝对值不超过

\[
b=2\|h\|_\infty+\|f\|_\infty.
\]

若其条件方差和为 \(V_N\)，则 Freedman 不等式给出

\[
\Pr(M_N\ge x,\;V_N\le v)
\le\exp\!\left(-\frac{x^2}{2(v+bx/3)}\right),
\]

对下尾同样成立；只用 \(|\Delta M_t|\le b\) 和 \(V_N\le Nb^2\) 即得 Azuma 型界。又因为 \(\Pr(\tau>N)\le q^N\)，有

\[
\mathbb E|A_\tau-A_{\tau\wedge N}|
\le\frac{\|f\|_\infty q^N}{1-q}.
\]

因此先对 \(A_{\tau\wedge N}\) 使用 Freedman 或 Azuma，再以概率至多 \(q^N\) 的尾事件和上式的截断偏差拼接，可得到随机首达时间的非渐近浓缩：给定 \(x>0\) 和偏差预算，取 \(N\) 使 \(q^N\) 小于该预算，剩余概率按上式的指数项衰减。精确常数随所选的中心化方式和条件方差上界而变，但其结构必含几何首达尾与鞅浓缩两项。

这个结论把三件事分开：Poisson 方程给出均值，停止鞅给出有限时域波动，几何尾把确定时域界延伸到随机吸收时刻。若 \(q=1\)、状态空间无限、\(f\) 无界或杀死尾部重尾，不能直接保留上述几何拼接；需另给 Lyapunov、截断或重尾估计。\(Q,f\) 和吸收机制均为外加声明，FIB 递归不自动产生“热噪声”或普适浓缩常数。

## 67. 有限 primitive 核经验测度的 Donsker–Varadhan 大偏差

令 \(Q\) 为有限状态集上的 primitive 随机核，令

\[
L_n=\frac1n\sum_{t=0}^{n-1}\delta_{X_t}
\]

为经验测度。对任意函数 \(f:S\to\mathbb R\)，定义压力

\[
\psi(f)=\log\rho\!\left(\operatorname{diag}(e^f)Q\right).
\]

由于 \(Q\) primitive，\(L_n\) 满足 Donsker–Varadhan 大偏差原理：对适当集合 \(A\)，

\[
\Pr(L_n\in A)\asymp
\exp\left(-n\inf_{\mu\in A}I(\mu)\right),
\qquad
I(\mu)=\sup_f\{\langle f,\mu\rangle-\psi(f)\}.
\]

等价地，在有限状态且 \(\mu\) 为概率向量时，

\[
I(\mu)=
\sup_{u>0}-\sum_i\mu_i\log\frac{(Qu)_i}{u_i}.
\]

初态只贡献次指数因子；若 \(Q\) 不可约但非 primitive，周期性需在取极限时保留相位类，不能直接套用无周期表述。

还可记录经验转移流

\[
\eta_{ij}^{(n)}=\frac1n\sum_{t=0}^{n-1}
\mathbf1_{\{X_t=i,X_{t+1}=j\}}.
\]

其极限流须满足守恒约束 \(\sum_j\eta_{ij}=\sum_j\eta_{ji}=\mu_i\)。在 \(\eta_{ij}=0\) 且 \(Q_{ij}=0\) 时采用标准零项约定，联合速率为

\[
J(\eta)=\sum_{i,j}\eta_{ij}
\log\frac{\eta_{ij}}{\mu_iQ_{ij}},
\qquad
I(\mu)=\inf_{\eta:\,\text{流守恒且边缘为 }\mu}J(\eta).
\]

因此经验占用偏离平稳律的指数代价由核的相对熵结构决定；压力的梯度给出典型测度，压力的 Hessian 在可微点给出长期协方差。这里的“压力”“自由能”只是有限 Markov 模型的谱和大偏差术语，不能据此宣称真实热力学自由能。

对 FIB 的结论边界是：只有在明确声明有限状态闭包、核 \(Q\)、初态和采样协议后，才可使用上述 LDP、Poisson 浓缩或分枝压力；递归本身不指定这些概率律，也不把词序统计自动升级成温度、熵产生、能量守恒或普适物理定律。

## 68. 外加 Markov 电流、熵产生与线性响应

**定义 68.1（有限上下文与外加核）。** 取 FIB 递归在某个有限上下文闭包上的状态集 \(\mathcal C\)，状态映射由逐字源或 ATOM 给出；另行指定有限核 \(Q=(Q_{ij})_{i,j\in\mathcal C}\)。假设 \(Q\) primitive，且 \(\pi Q=\pi\) 是唯一平稳律。FIB 只给出 \(\mathcal C\) 与标签，不给出 \(Q\)、初态或联合随机历史。以下轨迹 \(X_0,X_1,\ldots\) 均是外加核 \(Q\) 生成的平稳链；若只给定初态，所有渐近式另需说明初态边界项。

**定义 68.2（边电流与压力）。** 令 \(j_{ij}=-j_{ji}\) 为有向边电流，在 \(Q_{ij}>0\) 的边上定义。置
\[
Y_t=j_{X_tX_{t+1}},\qquad
J_n=\sum_{t=0}^{n-1}Y_t,\qquad
\bar j=\sum_{ij}\pi_iQ_{ij}j_{ij}.
\]
对实 \(\chi\) 定义倾斜矩阵
\[
Q_\chi(i,j)=Q_{ij}e^{\chi j_{ij}},\qquad
\Lambda(\chi)=\log\rho(Q_\chi).
\]
primitive 假设下，
\[
\lim_{n\to\infty}\frac1n\log\mathbb E_\pi e^{\chi J_n}
=\Lambda(\chi),
\]
且 \(\Lambda\) 在零点邻域解析。

**定理 68.3（Green–Kubo 与 Poisson—鞅表示）。** 令 \(\widetilde Y_t=Y_t-\bar j\)。有限 primitive 链的几何混合使协方差级数绝对收敛，并且
\[
\Lambda'(0)=\bar j,\qquad
\Lambda''(0)=\Gamma,
\]
\[
\Gamma=\operatorname{Var}_\pi(Y_0)
+2\sum_{m\ge1}\operatorname{Cov}_\pi(Y_0,Y_m).
\]
写
\[
b_i=\sum_jQ_{ij}j_{ij}-\bar j,\qquad
(I-Q)h=b,\qquad
\sum_i\pi_i h_i=0.
\]
令
\[
M(i,j)=j_{ij}-\bar j+h_j-h_i.
\]
则
\[
\mathbb E[M(X_t,X_{t+1})\mid X_t]=0,\qquad
\Gamma=\sum_{ij}\pi_iQ_{ij}M(i,j)^2\ge0.
\]
并且
\[
J_n-n\bar j
=\sum_{t=0}^{n-1}M(X_t,X_{t+1})
+h(X_0)-h(X_n),
\]
所以端点余项是有界边界项。若
\[
\Pi=\mathbf1\pi^{\mathsf T},\qquad
Z=\sum_{m\ge0}(Q^m-\Pi)
=(I-Q+\Pi)^{-1}-\Pi,
\]
则 \(h=Zb\)，给出有限状态 Green 算子版本的 Green–Kubo 公式。若物理时间取 \(t=n\delta\)，电流率的方差系数为 \(\Gamma/\delta\)，扩散系数约定为 \(\Gamma/(2\delta)\)。

**定义 68.4（路径熵产生）。** 在有向支持对称
\(Q_{ij}>0\Longleftrightarrow Q_{ji}>0\) 且 \(\pi_i>0\) 时，定义
\[
\sigma_{ij}
=\log\frac{\pi_iQ_{ij}}{\pi_jQ_{ji}},
\qquad
\Sigma_n=\sum_{t=0}^{n-1}\sigma_{X_tX_{t+1}}.
\]
它是正向平稳路径与时间反演路径的对数似然比。平均率为
\[
\dot s=\sum_{ij}\pi_iQ_{ij}\sigma_{ij}
=\frac12\sum_{ij}
(\pi_iQ_{ij}-\pi_jQ_{ji})
\log\frac{\pi_iQ_{ij}}{\pi_jQ_{ji}}\ge0,
\]
等号当且仅当满足详细平衡
\(\pi_iQ_{ij}=\pi_jQ_{ji}\)。对
\[
\Lambda_\sigma(\chi)
=\log\rho\!\left(Q_{ij}e^{\chi\sigma_{ij}}\right)
\]
有
\[
\Lambda_\sigma(\chi)=\Lambda_\sigma(-1-\chi),
\]
前提是支持对称且时间反演路径律具有相同的平稳边界项。一向边在对数比中给出无穷值，不能直接套用本式。这里的“熵”是路径相对熵率的无量纲名称，不能由 FIB 自动解释为热力学熵。

**定理 68.5（精确线性响应）。** 设 \(Q_\theta\) 与平稳律 \(\pi_\theta\) 在 \(\theta=0\) 附近可微，支持不变，并令
\[
s_0(i)=\left.\partial_\theta\log\pi_\theta(i)\right|_0,
\qquad
s(i,j)=\left.\partial_\theta\log Q_\theta(i,j)\right|_0.
\]
对任意有限路径泛函 \(F(X_0,\ldots,X_T)\)，路径得分
\[
S_T=s_0(X_0)+\sum_{t=0}^{T-1}s(X_t,X_{t+1})
\]
满足 \(\mathbb E_0S_T=0\) 与
\[
\left.\partial_\theta\mathbb E_\theta F\right|_0
=\operatorname{Cov}_0(F,S_T).
\]
取 \(F=J_T\) 并除以 \(T\)，在几何混合与可积条件下可得到稳态电流的响应率；没有额外假设时，响应由该 score 协方差决定，不能直接等同于同一电流的自相关。

**推论 68.6（平衡涨落—耗散的受限形式）。** 若 \(Q_0\) 满足详细平衡，外场参数是与反时间奇电流 \(j\) 共轭的无量纲力，并且路径得分的反时间奇部分满足
\[
S_T^{\mathrm{odd}}=\tfrac12J_T+o(T),
\]
同时时间对称的 frenetic 部分对所测奇电流的长期协方差为零，则
\[
L:=\left.\partial_\theta\bar j_\theta\right|_0
=\frac12\Gamma.
\]
多电流 \(j^a\) 时，
\[
L_{ab}
=\frac12\sum_{m\in\mathbb Z}
\operatorname{Cov}_0(Y_0^a,Y_m^b),
\]
并在这些平衡条件下满足 Onsager 对称性。若外场有物理量纲、熵单位取 \(k_B\)，还须由外加模型另给换算因子；FIB 不提供这些因子。脱离详细平衡、共轭得分或 frenetic 消失条件时，只保留定理 68.5 的 score 协方差式。

本节的边界是：有限上下文不闭合、\(Q\) 非 primitive、无平稳律、支持不对称、初态或环境随时间改变时，只能给有限时长或分块结论，不能无条件取谱率或 Green–Kubo 极限。FIB 递归只提供词序、长度、类型或标签及可选有限状态闭包；\(Q\)、电流、时间反演、外场、温度、\(k_B\)、物理单位和观测通道均为外加选择。因此本节得到的是指定有限 Markov 模型中的统计关系，不推出真实热流、熵、输运系数或任何物理普适定律。

## 69. 半马尔可夫重尾等待、异常 Green 响应与分数阶边界

FIB 递归在本节只提供有限状态集 \(S\)、词序、组合关系和阻抗标签。嵌入核、等待时间、杀死概率和物理时钟均为外加模型。令 \(Q\) 为 \(S\) 上的子随机嵌入核，\(\rho(Q)<1\)。在状态 \(i\) 停留的等待时间为 \(W_i\)，其 Laplace 变换记为
\[
\phi_i(s)=\mathbb E e^{-sW_i},\qquad
\Phi(s)=\operatorname{diag}(\phi_i(s)),\qquad
\overline\Phi(s)
=\operatorname{diag}\left(\frac{1-\phi_i(s)}s\right).
\]
约定先在当前状态等待，再按 \(Q\) 跳转。若 \(\nu\) 是初态行向量，则物理时间的活跃占用 Green 变换为
\[
\widehat U(s)
=\nu[I-\Phi(s)Q]^{-1}\overline\Phi(s),
\qquad
\widehat S(s)=\widehat U(s)\mathbf1,
\]
其中 \(S(t)\) 是时刻 \(t\) 尚未吸收的概率。对状态奖励 \(g\)，累计物理时间响应的变换为
\[
\widehat R_g(s)=\widehat U(s)g.
\]
因此离散嵌入步数的 resolvent 与物理时钟的 resolvent 不是同一个对象；等待协议决定它们之间的变换。

**定理 69.1（有限均值与重尾的分界）。** 若
\[
\phi_i(s)=1-\mu_i s+o(s),\qquad \mu_i<\infty,
\]
则
\[
\widehat U(0)
=\nu(I-Q)^{-1}\operatorname{diag}(\mu_i)
\]
给出有限 Green 占用和有限期望寿命。若存在 \(\alpha\in(0,1)\) 和 \(a_i>0\) 使
\[
\phi_i(s)=1-a_i s^\alpha+o(s^\alpha),
\qquad s\downarrow0,
\]
并满足非晶格与 Tauberian 条件，则
\[
\widehat S(s)\sim C s^{\alpha-1},
\qquad
C=\nu(I-Q)^{-1}a,
\]
从而
\[
S(t)\sim\frac{C}{\Gamma(1-\alpha)}t^{-\alpha},
\qquad
\int_0^tS(u)\,du
\sim\frac{C}{\Gamma(2-\alpha)}t^{1-\alpha}.
\]
于是嵌入链可有几何杀死谱，而物理时间的生存尾却是幂律，且平均寿命发散。一般奖励 \(g\) 在相同 Tauberian 条件下具有
\[
\widehat R_g(s)\sim
s^{\alpha-1}\,
\nu(I-Q)^{-1}\operatorname{diag}(a)g
\]
所决定的异常标度；常数随奖励与状态依赖等待共同改变。

若各状态共享 \(\phi(s)\)，则
\[
\widehat U(s)
=\nu[I-\phi(s)Q]^{-1}\frac{1-\phi(s)}s.
\]
若同时引入小步长族
\[
Q_\delta=I+\delta^\alpha L+o(\delta^\alpha),
\qquad
\phi_\delta(s)=1-\delta^\alpha s^\alpha+o(\delta^\alpha),
\]
则在声明的逆稳定时钟缩放下
\[
\widehat U_\delta(s)
\longrightarrow
\nu s^{\alpha-1}(s^\alpha I-L)^{-1}.
\]
这是该外加模型的分数阶 resolvent。若 \(Q\) 固定且 \(\rho(Q)<1\)，只能推出幂律生存和异常窗口，不应直接把结果写成上述分数阶生成器。

等待尾指数不一致时，最小指数、尾常数和状态访问次序共同决定主项；若 \(\rho(Q)=1\)、环境无谱隙或等待分布有更复杂的慢变因子，可能出现 aging 或 Lamperti 型极限，不能沿用 \(C\) 的简单公式。有限均值、重尾和时钟缩放必须分别声明。上述幂律、记忆核和分数阶术语属于半马尔可夫模型，不是 FIB 递归自动产生的真实异常扩散定律。

## 70. 多型系谱二阶统计与随机上下文矩阵乘积

令外加多型分枝的均值矩阵为 \(M\)，类型数有限，且 \(M\) primitive。记从类型 \(i\) 出发的第 \(n\) 代总数为 \(N_n\)，均值向量
\[
u_n(i)=\mathbb E_iN_n,\qquad
u_{n+1}=Mu_n,\qquad u_0=\mathbf1.
\]
令
\[
B_i(p,q)
=\mathbb E_i\!\left[\xi_p(\xi_q-\delta_{pq})\right]
\]
为二阶阶乘核，并令
\[
F_n(i)=\mathbb E_i[N_n(N_n-1)].
\]
则分枝独立性给出精确递推
\[
F_{n+1}=MF_n+b_n,\qquad F_0=0,
\]
其中
\[
(b_n)_i
=\sum_{p,q}B_i(p,q)u_n(p)u_n(q).
\]
展开为
\[
F_n
=\sum_{t=0}^{n-1}M^t b_{n-1-t}.
\]
深度 \(t\) 的项对应两条后代谱系最近共同祖先在该层分裂；归一化这些项得到 annealed 二粒子共同祖先的权重。对指定末端类型 \(a,b\)，同样有
\[
F_{n+1}(i;a,b)
=\sum_jM_{ij}F_n(j;a,b)
+\sum_{p,q}B_i(p,q)
(M^n)_{pa}(M^n)_{qb}.
\]
在 primitive、超临界和有限二阶矩条件下，若存在非退化可达分裂，固定 \(t\) 后 \(n\to\infty\) 的共同祖先尾部由
\[
F\text{ 的分裂项}\asymp \rho^{\,2n-t}
\]
控制；再对 \(t\) 取渐近时，可得到上下界形式
\[
c_1\rho^{-t}
\le \liminf_{n\to\infty}\Pr(T_n\ge t)
\le \limsup_{n\to\infty}\Pr(T_n\ge t)
\le c_2\rho^{-t},
\]
其中常数和适用的周期类依赖根分布与 \(B_i\)。若没有可达二阶分裂、仅在周期类中分裂或二阶矩不有限，则不能声称该几何尾。

均值矩阵 \(M\) 只决定一阶 Perron 增长，\(B_i\) 才决定方差、聚簇和共同祖先。单型 \(M=[2]\) 的两个模型——每个个体恒生两个子代，或以概率一半生零个、以概率一半生四个——有相同均值和 Perron 增长，但灭绝概率、极限变量方差和系谱共祖均不同。这一反例阻止把确定性 FIB 计数直接解释成唯一随机分枝律。

还可令有限类型上下文随外加环境变化，得到非负矩阵乘积
\[
Z_n=\nu A_0A_1\cdots A_{n-1},
\]
其中 \(A_t\) 是环境 \(\omega_t\) 下的替换或转移矩阵。若环境平稳遍历、\(\mathbb E\log^+\|A_0\|<\infty\)，并有统一正块或投影收缩，则 Furstenberg–Kesten 率
\[
\lambda_q
=\lim_{n\to\infty}\frac1n
\log\|A_0A_1\cdots A_{n-1}v\|
\]
几乎处处存在。环境独立时
\[
\mathbb E Z_n=\nu(\mathbb EA_0)^n\!,
\qquad
\log\rho(\mathbb EA_0)\ge\lambda_q
\]
在适用的初态和正性条件下成立，且一般严格不等。若 \(\log\|A_t\|\) 具有指数矩，可定义
\[
\Lambda(\theta)
=\lim_{n\to\infty}\frac1n
\log\mathbb E
\exp\!\left(
\theta\log\|A_0\cdots A_{n-1}v\|
\right).
\]
在 \(\Lambda\) 可微并满足 Gärtner–Ellis 条件时，增长率具有大偏差原理，\(\Lambda'(0)=\lambda_q\)，\(\Lambda''(0)\) 给出环境乘积的长期方差。矩阵环境、正性、独立性和范数均为外加条件，不能把 \(\lambda_q\) 或 annealed 率视为 FIB 内生的物理指数。

## 71. 路径指数倾斜的非线性响应、后验稳定性与观测商类

FIB 只提供路径载体、标签和组合索引。本节的基准路径律 \(P_0\)、路径奖励 \(A\)、观测通道和参数先验均为外加对象。对有限路径定义
\[
\frac{dP_\lambda}{dP_0}(x)
=\exp\{\lambda A(x)-\Psi(\lambda)\},
\qquad
\Psi(\lambda)=\log\mathbb E_0e^{\lambda A}.
\]
若 \(A\) 有界，则 \(\Psi\) 在全实轴上光滑，并且
\[
\Psi'(0)=\mathbb E_0A,\qquad
\Psi''(0)=\operatorname{Var}_0(A),\qquad
\Psi^{(r)}(0)=\kappa_r(A).
\]

**定理 71.1（线性与二阶响应）。** 令
\(m_F(\lambda)=\mathbb E_\lambda F\)，\(a=\mathbb E_0A\)。则
\[
m_F'(0)=\operatorname{Cov}_0(F,A),
\]
\[
m_F''(0)
=\mathbb E_0[(F-\mathbb E_0F)(A-a)^2]
=\operatorname{Cov}_0\!\left(F,(A-a)^2\right).
\]
故
\[
|m_F'(0)|
\le\sqrt{\operatorname{Var}_0(F)\operatorname{Var}_0(A)},
\]
\[
|m_F''(0)|
\le\sqrt{\operatorname{Var}_0(F)
\operatorname{Var}_0((A-a)^2)}.
\]
这些是纯粹的路径测度恒等式；若动力学本身随 \(\lambda\) 改变，还必须加入核或初态的 score 与 Hessian 项，不能把指数倾斜公式冒充一般的物理涨落—响应定律。

若 \(A_T=\sum_{t=0}^{T-1}a(X_t)\)，基准链平稳且满足
\[
|\operatorname{Cov}_0(a(X_0),a(X_k))|
\le C\rho^k,\qquad 0\le\rho<1,
\]
则
\[
\operatorname{Var}_0(A_T)
\le C\left[T+2\sum_{k=1}^{T-1}(T-k)\rho^k\right]
\le CT\frac{1+\rho}{1-\rho}.
\]
因此一阶响应的自然上界为 \(O(\sqrt T)\)，而 \(\Psi''(0)=O(T)\)。这里的 \(\rho\)、平稳初态和协方差衰减来自外加核。

**定理 71.2（似然扰动到后验的总变差界）。** 令参数空间为有限或可测空间，先验为 \(\Pi\)，观测为 \(y\)，基准似然和扰动似然分别为 \(L_\theta(y)\) 与 \(\widetilde L_\theta(y)\)。若两者在 \(\Pi\)-几乎处处的共同支撑上满足
\[
|\log\widetilde L_\theta(y)-\log L_\theta(y)|\le r,
\]
记相应后验为 \(\Pi_y,\widetilde\Pi_y\)。则
\[
\frac{d\widetilde\Pi_y}{d\Pi_y}(\theta)
=\frac{e^{\delta(\theta)}}{\mathbb E_{\Pi_y}e^\delta},
\qquad |\delta|\le r,
\]
并有
\[
e^{-2r}\le
\frac{d\widetilde\Pi_y}{d\Pi_y}
\le e^{2r},
\qquad
\operatorname{TV}(\Pi_y,\widetilde\Pi_y)
\le\frac{e^{2r}-1}{e^{2r}+1}
=\tanh r.
\]
任意有界后验泛函 \(b\) 满足
\[
|\mathbb E_{\Pi_y}b-\mathbb E_{\widetilde\Pi_y}b|
\le\operatorname{osc}(b)\tanh r.
\]
若完整路径似然来自
\[
\nu_\theta(x_0)\prod_{t<T}Q_\theta(x_t,x_{t+1}),
\]
并且共同支撑上
\[
\left|\log\frac{\widetilde\nu_\theta}{\nu_\theta}\right|\le r_0,
\qquad
\left|\log\frac{\widetilde Q_\theta(i,j)}
{Q_\theta(i,j)}\right|\le r_Q,
\]
则可取 \(r=r_0+Tr_Q\)，得到
\[
\operatorname{TV}(\Pi_y,\widetilde\Pi_y)
\le\tanh(r_0+Tr_Q).
\]
行的总变差很小并不保证对数比很小；支撑出现零点时必须先处理绝对连续性。

在 \(\nu\ll\widetilde\nu\)、\(Q(i,\cdot)\ll\widetilde Q(i,\cdot)\) 时，路径相对熵满足链式公式
\[
D_{\mathrm{KL}}(P_T^{\nu,Q}\|P_T^{\widetilde\nu,\widetilde Q})
=
D_{\mathrm{KL}}(\nu\|\widetilde\nu)
+\sum_{t=0}^{T-1}
\mathbb E_{\nu,Q}
D_{\mathrm{KL}}(Q(X_t,\cdot)\|
\widetilde Q(X_t,\cdot)).
\]
Pinsker 不等式给出
\[
\operatorname{TV}(P_T^{\nu,Q},P_T^{\widetilde\nu,\widetilde Q})
\le
\sqrt{\tfrac12D_{\mathrm{KL}}(P_T^{\nu,Q}\|
P_T^{\widetilde\nu,\widetilde Q})}.
\]
支撑不包含时相对熵为无穷，不能套用该界。

**命题 71.3（观测推前的后验不可辨识）。** 设观测通道 \(O_T\) 将完整路径律 \(P_\theta\) 推前为 \(P_\theta^O\)。则
\[
\operatorname{TV}(P_\theta^O,P_{\theta'}^O)
\le\operatorname{TV}(P_\theta,P_{\theta'}).
\]
若 \(P_\theta^O=P_{\theta'}^O\)，离散先验对两参数均为正，则对几乎所有观测 \(y\)
\[
\frac{\Pi(\theta\mid y)}{\Pi(\theta'\mid y)}
=\frac{\Pi(\theta)}{\Pi(\theta')}.
\]
无穷数据也只能识别观测等价类
\[
[\theta]=\{\theta':P_{\theta'}^O=P_\theta^O\}.
\]
若两观测律的总变差至多为 \(\delta\)，则任意二元测试的两类错误和至少为 \(1-\delta\)；因此小的观测差异不能保证后验把两个参数稳定分开。这一结论是统计不可辨识边界，不是 FIB 递归对参数的否定。

## 72. 外加多粒子平均场、传播混沌与水动力极限

令 \(E_j\) 是第 \(j\) 代 FIB 合法的有限上下文闭包。FIB 只给出 \(E_j\)、标签和组合关系。给定外加核
\[
Q_j(x,\mu)\in\mathcal P(E_j),
\]
令 \(N\) 个粒子满足
\[
\mu_t^{N,j}=\frac1N\sum_{i=1}^N\delta_{X_t^{N,i}},
\qquad
\Pr(X_{t+1}^{N,i}=y\mid\mathcal F_t)
=Q_j(X_t^{N,i},\mu_t^{N,j})(y),
\]
其中条件独立只表示给定当前经验测度后的抽样独立；初态、相互作用、边界、时间单位和 \(N\) 均为外加数据。定义
\[
\Phi_j(\mu)=\mu Q_{j,\mu},
\qquad
\mu_{t+1,j}=\Phi_j(\mu_{t,j}).
\]

**定理 72.1（固定时域传播混沌）。** 在 \(E_j\) 上取有界度量 \(d_j\le1\)，假设存在与 \(j\) 无关的 \(L\) 使
\[
\|Q_j(x,\mu)-Q_j(x,\nu)\|_{\mathrm{TV}}
\le Ld_j(\mu,\nu),
\]
且初态经验测度误差为
\[
\mathbb E d_j(\mu_0^{N,j},\mu_{0,j})
\le C_0N^{-1/2}.
\]
则对每个固定 \(T\) 存在 \(C_T\) 使
\[
\max_{0\le t\le T}
\mathbb E d_j(\mu_t^{N,j},\mu_{t,j})
\le C_TN^{-1/2}.
\]
有限状态的 Hoeffding 界还给出，对固定 \(\varepsilon>0\)
\[
\Pr\!\left(
\max_{t\le T}d_j(\mu_t^{N,j},\mu_{t,j})>\varepsilon
\right)
\le C(T,|E_j|)
\exp\!\left(-cN\varepsilon^2/C_T^2\right).
\]
令 \(Y^1,\ldots,Y^k\) 是转移核
\(Q_j(\,\cdot\,,\mu_{t,j})\) 驱动的独立非线性链，则固定 \(k,T\) 时
\[
d_{\mathrm{BL}}\!\left(
\mathcal L(X_{0:T}^{N,1:k}),
\mathcal L(Y_{0:T}^{1:k})
\right)
\le C_{T,k}N^{-1/2}.
\]
这就是有限时域传播混沌。若初态仅交换而非渐近乘积，极限需条件于其 de Finetti 变量；若有公共噪声，则只能声称条件传播混沌。

**命题 72.2（FIB 代数增长与粒子数的双尺度误差）。** 假设存在极限状态空间 \(E_\infty\)、嵌入 \(\iota_j:E_j\to E_\infty\)、极限核 \(Q_\infty\)，并且
\[
\sup_{x,\mu}
d_{\mathrm{TV}}\!\left(
(\iota_j)_\#Q_j(x,\mu),
Q_\infty(\iota_jx,(\iota_j)_\#\mu)
\right)
\le\eta_j\longrightarrow0.
\]
若 Lipschitz 常数和初态误差在 \(j\) 上统一，令 \(\mu_t^\infty\) 由极限流递推，则
\[
\max_{t\le T}
\mathbb E d\!\left(
(\iota_j)_\#\mu_t^{N,j},\mu_t^\infty
\right)
\le
C_T\bigl(N^{-1/2}+\eta_j+e_{0,j}\bigr).
\]
只有在 \(N\to\infty\)、\(j\to\infty\) 且各误差同时消失时，才可交换粒子数极限和 FIB 代数增长极限。没有统一逼近、矩界或 Lipschitz 常数时，只能逐 \(j\) 处理。

若另给位置嵌入 \(x_j:E_j\to[0,1]\)、步长 \(\epsilon_j,\delta_j\)，对光滑测试函数定义外加离散生成器
\[
(\mathcal L_{j,\mu}\varphi)(x,c)
=\delta_j^{-1}\sum_yQ_j((x,c),\mu)(y)
[\varphi(x_j(y),c(y))-\varphi(x,c)].
\]
假设在紧集上一致有
\[
\mathcal L_{j,\mu}\varphi
\longrightarrow
b_c(x,\mu)\partial_x\varphi
+\tfrac12a_c(x,\mu)\partial_{xx}\varphi
+\sum_{d\in\mathcal C}
R_{cd}(x,\mu)[\varphi(x,d)-\varphi(x,c)],
\]
并有初态紧性、二阶跳跃矩界和唯一弱解。若 \(N,j\to\infty\) 时离散误差与 \(N^{-1/2}\) 同时趋零，则经验测度的极限满足
\[
\partial_t\rho_c
=-\partial_x(b_c\rho_c)
+\tfrac12\partial_{xx}(a_c\rho_c)
+\sum_dR_{dc}(x,\rho)\rho_d
\]
的弱形式。对每个光滑 \(\varphi\)，
\[
\langle\varphi,\rho_t\rangle
=\langle\varphi,\rho_0\rangle
+\int_0^t
\langle\mathcal A_{\rho_s}\varphi,\rho_s\rangle\,ds.
\]
反射或吸收边界必须写进 \(Q_j\) 和弱问题；不能从词序递归推出。证明的鞅为
\[
M_t^{N,j}(\varphi)
=\langle\varphi,\mu_t^{N,j}\rangle
-\langle\varphi,\mu_0^{N,j}\rangle
-\sum_{s<t}\delta_j
\langle\mathcal L_{j,\mu_s^{N,j}}\varphi,
\mu_s^{N,j}\rangle,
\]
其固定宏观时间上的条件二次变差为 \(O(N^{-1})\)。若 PDE 不唯一，只能声称紧性和“任一子列极限均为弱解”。

两型 \(\mathcal C=\{\alpha,\beta\}\) 的反应—扩散特例为
\[
\partial_t\rho_\alpha
=D_\alpha\partial_{xx}\rho_\alpha
-\partial_x(b_\alpha\rho_\alpha)
-r_{\alpha\beta}(x,\rho)\rho_\alpha
+r_{\beta\alpha}(x,\rho)\rho_\beta,
\]
\[
\partial_t\rho_\beta
=D_\beta\partial_{xx}\rho_\beta
-\partial_x(b_\beta\rho_\beta)
+r_{\alpha\beta}(x,\rho)\rho_\alpha
-r_{\beta\alpha}(x,\rho)\rho_\beta.
\]
扩散系数、漂移、反应率和质量边界均由外加核确定；FIB 的 \(\alpha,\beta\) 出现频率不指定它们。

**命题 72.3（统计动力学延拓不唯一）。** 给定同一 \(E_j\) 与同一 FIB 递归关系，任意 Lipschitz 映射
\(\Psi:\mathcal P(E_j)\to\mathcal P(E_j)\) 都可令
\[
Q_\Psi(x,\mu)=\Psi(\mu).
\]
于是平均场流恰为
\[
\mu_{t+1}=\Psi(\mu_t).
\]
常值 \(\Psi\) 给出独立重采样；依赖 \(\alpha\) 占比的 \(\Psi\) 可给出合作或竞争流；选择带空间嵌入的 \(\Psi\) 可给出不同反应—扩散极限。它们共享同一 FIB 词序和计数，却有不同固定点、波速、扩散系数与反应项。因此不存在仅凭 FIB 递归唯一确定的传播混沌常数、PDE 或“物理定律”。

本节的适用边界是：有限时域不能升级成长时稳定；\(N\to\infty\) 与 \(j\to\infty\) 的次序及联合缩放必须声明；初态、核、相互作用、位置嵌入、边界、噪声和观测通道均为外加条件。缺乏统一 Lipschitz 或矩界、初态不渐近乘积、公共噪声未条件化或 PDE 不唯一时，结论相应降为条件极限、随机极限或开放边界。水动力结论是所给离散模型的弱极限，不是 FIB 自身推出的真实热力学、能量守恒、普适性或物理实在性。

## 73. FIB 状态载体上的外加量子信道、退相干与谱隙

令 \(S\) 是有限 FIB 状态集，外加 Hilbert 空间为
\(\mathcal H=\mathbb C^S\)，基态记为 \(\lvert i\rangle\)。FIB 只提供 \(S\)、标签和组合索引；密度矩阵、Hamiltonian、CP/CPTP 映射及所有速率均是外加结构。经典概率 \(p\) 可嵌入为
\[
\iota(p)=\sum_i p_i\lvert i\rangle\langle i\rvert.
\]
若标签 \(g:S\to\mathcal A\)，令
\[
P_a=\sum_{g(i)=a}\lvert i\rangle\langle i\rvert,
\qquad
\Delta_g(\rho)=\sum_{a\in\mathcal A}P_a\rho P_a.
\]
对 \(\eta\in[0,1]\) 定义 CPTP 通道
\[
\Phi_\eta=(1-\eta)\operatorname{Id}+\eta\Delta_g.
\]
若 \(X\in\ker\Delta_g\) 是跨标签相干块，则
\[
\Phi_\eta^n(X)=(1-\eta)^nX.
\]
因此离散退相干率可记为
\(\gamma_d=-\log(1-\eta)\)；\(\eta=1\) 时跨标签相干一步消失。固定点代数
\(\{\rho:\Delta_g(\rho)=\rho\}\) 通常包含多个块对角态，所以退相干率不等于唯一平衡态的混合隙。

**定理 73.1（量子通道扰动稳定性）。** 设 \(\Phi,\widetilde\Phi\) 是同一有限维空间上的 CPTP 通道，且 \(\widetilde\Phi\) 在迹零厄米空间上有收缩系数 \(\kappa<1\)。令
\[
\delta=\sup_{\rho}\|\Phi(\rho)-\widetilde\Phi(\rho)\|_1,
\qquad
\delta_0=\|\rho_0-\widetilde\rho_0\|_1.
\]
则
\[
\|\Phi^n\rho_0-\widetilde\Phi^n\widetilde\rho_0\|_1
\le
\kappa^n\delta_0+
\delta\frac{1-\kappa^n}{1-\kappa}.
\]
没有收缩假设时，望远镜估计给出
\[
\|\Phi^n-\widetilde\Phi^n\|_\diamond
\le n\|\Phi-\widetilde\Phi\|_\diamond.
\]
若两通道各有唯一不变态，则其不变态的迹距离至多为
\(\delta/(1-\kappa)\)。迹范数和 diamond 范数是外加量子模型的稳定距离，不是 FIB 内生量。

**定义 73.2（Lindblad 半群与量子谱隙）。** 在 \(\mathcal H\) 上给定外加 GKLS 生成元
\[
\mathcal L(\rho)
=-i[H,\rho]
+\sum_\ell\gamma_\ell
\left(
V_\ell\rho V_\ell^\dagger
-\tfrac12\{V_\ell^\dagger V_\ell,\rho\}
\right),
\qquad
\mathcal T_t=e^{t\mathcal L}.
\]
若存在唯一忠实不变态 \(\sigma\)，并满足相对于
\[
\langle A,B\rangle_\sigma
=\operatorname{Tr}(\sigma^{1/2}A^\dagger\sigma^{1/2}B)
\]
的量子详细平衡，定义
\[
\gamma_2
=\inf_{\operatorname{Tr}(\sigma A)=0}
\frac{-\operatorname{Re}\langle A,\mathcal L^\dagger A\rangle_\sigma}
{\|A\|_{2,\sigma}^2}.
\]
则
\[
\operatorname{Var}_\sigma(\mathcal T_t^\dagger A)
\le e^{-2\gamma_2t}\operatorname{Var}_\sigma(A),
\]
有限维范数等价进一步给出迹距离的指数收敛。无详细平衡时只能使用非零谱实部和可能的 Jordan 多项式前因子；不能无条件写成无常数的纯指数界。若另有量子对数 Sobolev 常数 \(\alpha>0\)，则
\[
D(\mathcal T_t\rho\Vert\sigma)
\le e^{-2\alpha t}D(\rho\Vert\sigma).
\]
这些谱隙、\(\sigma\)、\(H\)、\(V_\ell\) 与速率都必须由外加量子模型给定，FIB 不自动产生量子退相干、耗散、温度或热平衡。

## 74. 有限替换闭包的尺度重整化、固定点与临界谱分岔

令 \(\mathcal C=\{1,\ldots,d\}\) 是已声明有限且闭合的 FIB 上下文，给定外加非负加权替换矩阵
\(A(\theta)\in\mathbb R_+^{d\times d}\)。\(\nu\) 是外加初态，定义
\[
Z_n(\theta)=\nu^{\mathsf T}A(\theta)^n\mathbf1,
\qquad
p(\theta)=\log\rho(A(\theta)).
\]
FIB 只给出 \(\mathcal C\) 和可行边；权重、参数、尺度和观测均是外加。

对整数 \(b\ge2\)，在正标量射影类上定义块重整化
\[
R_b[A]=[A^b],
\qquad
\widetilde R_b(A)=\frac{A^b}{\rho(A)^b}.
\]
若 \(A\) primitive，Perron 根为 \(\rho\)，左右向量满足
\(\ell^{\mathsf T}r=1\)，则
\[
\widetilde R_b^k(A)=\frac{A^{b^k}}{\rho^{b^k}}
\longrightarrow r\ell^{\mathsf T}.
\]
若 \(q=|\lambda_2|/\rho<1\)，且 \(A\) 可对角化，误差为
\[
\left\|\widetilde R_b^k(A)-r\ell^{\mathsf T}\right\|
\le Cq^{b^k}.
\]
一般存在任意 \(\bar q\in(q,1)\) 使误差
\(O(\bar q^{\,b^k})\)，或带次谱 Jordan 多项式因子。尺度这里指递归块长度，不自动等于物理长度。

若参数族在阻塞后仍闭合：
\[
[A(\Phi_b\theta)]=[A(\theta)^b],
\qquad
\Phi_{b_1b_2}=\Phi_{b_1}\circ\Phi_{b_2},
\]
且 \(\theta_\ast\) 为固定点，则线性化
\(J_b=D\Phi_b(\theta_\ast)\) 满足
\[
J_{b_1b_2}=J_{b_1}J_{b_2}.
\]
沿特征方向 \(\Lambda_i(b)\) 定义
\[
y_i=\frac{\log|\Lambda_i(b)|}{\log b}.
\]
在声明的尺度律下，\(|\Lambda_i|>1\)、\(=1\)、\(<1\) 分别称为相关、边缘和无关方向。若外加观测 \(M\) 满足
\(M(\Phi_b\theta)=b^{s_M}M(\theta)\)，则相关方向可推出幂律
\(M(\theta)\asymp|\delta\theta_i|^{s_M/y_i}\)；这需要重整化闭合和观测尺度律，不能由 FIB 递归单独推出。

谱隙比
\[
q(\theta)=\frac{|\lambda_2(\theta)|}{\rho(\theta)}
\]
给出离散相关长度
\[
\xi(\theta)=-\frac1{\log q(\theta)}.
\]
块变换后 \(q\mapsto q^b\)、\(\xi\mapsto\xi/b\)。若外加临界参数满足
\(1-q(t)\sim c|t-t_c|^\gamma\)，则
\[
\xi(t)\sim c^{-1}|t-t_c|^{-\gamma}.
\]
但若 \(A_t\) 在邻域内严格正且条目解析，Perron 根简单解析，\(p(t)=\log\rho(A_t)\) 也解析；有限维本身没有真正非解析相变。非解析性必须来自失去 primitive、可约极限、维数或尺度趋于无穷，或另加奇异极限。

例：
\[
A_{t,\varepsilon}
=\begin{pmatrix}1+t&\varepsilon\\ \varepsilon&1-t\end{pmatrix},
\qquad
\rho=1+\sqrt{t^2+\varepsilon^2}.
\]
\(\varepsilon>0\) 时压力光滑；\(\varepsilon=0\) 时
\(p(t)=\log(1+|t|)\) 在 \(t=0\) 出现导数跳变，且
\[
p''(0)=\frac1{\varepsilon(1+\varepsilon)}
\]
在 \(\varepsilon\downarrow0\) 时发散。这是外加矩阵的谱分岔，不是 FIB 自身的真实相变。

## 75. 熵正则最优传输、Schrödinger 桥与信息几何梯度流

固定一代有限上下文闭包 \(E_j\)。FIB 只确定有限状态、标签、词序和可选位置嵌入；代价、参考耦合、度量、时间尺度和端点律均为外加数据。设
\(\mu_0,\mu_1\in\mathcal P(E_j)\)，\(r_j(x,y)\ge0\) 为参考耦合，\(c_j\) 为有界代价，\(\varepsilon>0\)。定义
\[
\mathsf{OT}_{\varepsilon,j}
=\inf_{\pi\in\Pi(\mu_0,\mu_1),\ \pi\ll r_j}
\left\{
\langle c_j,\pi\rangle+
\varepsilon D_{\mathrm{KL}}(\pi\Vert r_j)
\right\}.
\]
若可行集非空且 \(\varepsilon>0\)，有限单纯形的严格凸性给出唯一最优耦合。若参考支撑在允许坐标上为正，则存在 \(a_x,b_y\ge0\) 使
\[
\pi^\varepsilon_j(x,y)
=a_xb_yr_j(x,y)e^{-c_j(x,y)/\varepsilon},
\]
并满足两个边缘约束。若支撑图不具端点可达性，只能在可行分量上使用此表示。

当 \(r_j=\mu_0\otimes\mu_1\)、正质量坐标下界为 \(m>0\) 时，吸收 KL 常数后有
\[
0\le
\mathsf{OT}_{\varepsilon,j}
-\inf_{\pi\in\Pi(\mu_0,\mu_1)}
\langle c_j,\pi\rangle
\le\varepsilon\log|E_j|^2.
\]
因此固定 \(j\) 时 \(\varepsilon\downarrow0\) 的聚点是未正则化最优耦合；若未正则化解不唯一，熵项只选择其中一个聚点。

令 \(Q_j\) 为外加 Markov 核，\(R_j\) 为由初始律 \(\rho_0\) 与 \(Q_j\) 生成的路径律。给定端点律，Schrödinger 桥为
\[
\mathsf{SB}_{\varepsilon,j}
=\inf_{P:\,P_0=\mu_0,\ P_T=\mu_T}
\varepsilon D_{\mathrm{KL}}(P\Vert R_j).
\]
在端点可行且 \(R_j\) 支撑正时，最优桥唯一，并可写成 Doob 型变换
\[
Q_t^{\mathrm{SB}}(x,y)
=Q_j(x,y)\frac{\varphi_{t+1}(y)}{\varphi_t(x)},
\]
其中 \(\varphi_t\) 与其对偶势满足前向、后向 Schrödinger 方程。候选路径律的 KL 链式分解为
\[
D_{\mathrm{KL}}(P\Vert R_j)
=D_{\mathrm{KL}}(P_0\Vert\rho_0)
+\sum_{t=0}^{T-1}
\mathbb E_P
D_{\mathrm{KL}}\!\left(
P(X_{t+1}\mid X_{0:t})
\middle\Vert Q_j(X_t,\cdot)
\right).
\]
对固定端点，最优桥可由马尔可夫化取得，因而等价于逐步控制相对熵最小化。该分解不赋予 KL 热力学温度或真实耗散含义。

给定外加图迁移率和能量
\[
\mathcal F_j(\mu)
=\sum_xV_j(x)\mu_x
+\beta\sum_x\mu_x\log\frac{\mu_x}{m_j(x)}
+\frac12\sum_{x,y}W_j(x,y)\mu_x\mu_y,
\]
以及保持总质量的半正定 Onsager 算子 \(K_j(\mu)\)，定义
\[
\dot\mu_t=-K_j(\mu_t)\nabla\mathcal F_j(\mu_t).
\]
沿正坐标解有
\[
\frac{d}{dt}\mathcal F_j(\mu_t)
=-\langle\nabla\mathcal F_j,
K_j(\mu_t)\nabla\mathcal F_j\rangle\le0.
\]
若再给定外加度量 \(d_j\)，JKO 离散化为
\[
\mu_{\tau,j}^{n+1}\in
\operatorname*{argmin}_{\mu\in\mathcal P(E_j)}
\left\{
\frac{1}{2\tau}W_{2,j}^2(\mu,\mu_{\tau,j}^n)
+\mathcal F_j(\mu)
\right\}.
\]
有限状态下极小值存在；凸性、能量界、速度平方可积和极限唯一性成立时，\(\tau\downarrow0\) 给出能量耗散解，否则只能声称子列极限满足能量不等式。若同时让 \(\varepsilon\downarrow0\)、\(\tau\downarrow0\) 或 \(j\to\infty\)，必须声明联合缩放与极限次序。

同一 \(E_j\) 与 FIB 递归可选择不同的
\((c_j,r_j,Q_j,d_j,V_j,m_j)\)，从而得到不同最优耦合、桥路径、Fisher 度量和耗散率。故 FIB 只提供可承载这些模型的有限组合状态，不能单独确定 Wasserstein 距离、温度、耗散或真实物理定律。

## 76. FIB 替换词的符号动力学、频率与谱测度

取有限字母表 \(\mathcal A=\{\alpha,\beta\}\) 及外加替换
\[
\sigma(\alpha)=\alpha\beta,\qquad
\sigma(\beta)=\alpha.
\]
其按列计数的替换矩阵为
\[
M=\begin{pmatrix}1&1\\1&0\end{pmatrix}.
\]
令 \(\mathcal L(\sigma)\) 为所有 \(\sigma^n(a)\) 的有限子词，并定义双边 hull
\[
X_\sigma
=\{x\in\mathcal A^{\mathbb Z}:
\text{每个有限子块均属于 }\mathcal L(\sigma)\},
\qquad
(Tx)_k=x_{k+1}.
\]
FIB 递归 \(W_{j+2}=W_{j+1}W_j\) 只有在指定了与某个 \(X_\sigma\) 的合法嵌入、平移极限和双边延拓后，才能使用下述结论；原始有限词本身不自动给出平移不变概率律。

**定理 76.1（primitive 替换的唯一遍历性与频率）。** 若 \(\sigma\) primitive，则 \((X_\sigma,T)\) 最小，并存在唯一 \(T\)-不变概率测度 \(\mu\)。对任意连续 \(f:X_\sigma\to\mathbb C\)，
\[
\lim_{N\to\infty}\frac1N\sum_{k=0}^{N-1}f(T^kx)
=\int f\,d\mu
\]
对所有 \(x\in X_\sigma\) 一致成立。特别地，每个合法有限词 \(u\) 的圆柱频率
\[
\operatorname{freq}(u)=\mu([u])
\]
存在且与起点和相位无关。若 \(r,\ell\) 是 \(M\) 的正右、左 Perron 向量，则字母频率由 \(r\) 归一化给出；标准 Fibonacci 规范下
\[
\operatorname{freq}(\alpha)=\varphi^{-1},
\qquad
\operatorname{freq}(\beta)=\varphi^{-2}.
\]
有限 \(W_j\) 的端点只产生边界误差，前提是 \(W_j\) 确实来自该 primitive hull 的合法超词序列。

**定义 76.2（自相关与谱测度）。** 给定有界字母权重 \(w:\mathcal A\to\mathbb C\)，定义加权梳
\[
\omega_x=\sum_{n\in\mathbb Z}w(x_n)\delta_n.
\]
唯一遍历性保证自相关系数
\[
\eta(m)=\int_{X_\sigma}
w(x_0)\overline{w(x_{-m})}\,d\mu(x)
\]
存在且与 \(x\) 无关。令
\[
\gamma=\sum_{m\in\mathbb Z}\eta(m)\delta_m.
\]
\(\gamma\) 是正定测度，其 Fourier 变换 \(\widehat\gamma\) 是正测度，可称为该加权符号模型的数学衍射测度。对中心化观测
\[
f(x)=w(x_0)-\int w(x_0)\,d\mu,
\]
Koopman 谱测度 \(\sigma_f\) 由
\[
\int_{\mathbb T}z^m\,d\sigma_f(z)
=\langle f\circ T^m,f\rangle_{L^2(\mu)}
\]
确定。零频原子来自常数均值；其余峰型取决于替换、权重和位置实现。标准 Fibonacci 的纯离散结论需要另用相应模型集或替换谱定理，不能只由递归拼接式推出。

**定理 76.3（Perron 尺度分解）。** 令 \(c_n=M^nc_0\) 是替换词的字母计数向量，\(P=r\ell^{\mathsf T}/(\ell^{\mathsf T}r)\)。则
\[
c_n=\varphi^nPc_0+
(-\varphi^{-1})^n(I-P)c_0.
\]
任意字母权重和均为主尺度 \(C\varphi^n\) 加次尺度
\(D(-\varphi^{-1})^n\)，归一化频率误差为
\(O(\varphi^{-2n})\)。对局部块计数，应使用相应的高阶块替换矩阵；其次特征值不必等于 \(-\varphi^{-1}\)，所以 \(\varphi\) 的长度增长不自动是任何相关函数的临界指数。

本节的边界是：FIB 递归本身未指定 primitive 替换、双边 hull、平移不变测度、权重、格点位置或 Fourier 观测。非 primitive、上下文不闭合、单边序列或固定长度时，最多得到指定有限词的计数恒等式或子序列结论，不能宣称唯一遍历、衍射谱或物理材料结构。

## 77. 外加连续时间链的亚稳态、准平稳寿命与稀有跃迁

固定一代 \(j\)，令 \(E_j\) 为 FIB 递归产生的有限上下文集合。给定外加速率 \(r_{\varepsilon,j}(x,y)\ge0\)，定义
\[
(\mathcal L_{\varepsilon,j}f)(x)
=\sum_{y\ne x}r_{\varepsilon,j}(x,y)[f(y)-f(x)].
\]
取互不相交的亚稳井 \(A\)、目标 \(B\)，
\(D=E_j\setminus B\)，
\[
\tau_B=\inf\{t:X_t\in B\},
\]
并以杀死边界限制生成器。若 \(D\) 内核不可约，杀死半群有唯一准平稳分布 \(\nu_{\varepsilon,j}\) 与主特征值 \(\lambda_{\varepsilon,j}>0\)：
\[
\nu_{\varepsilon,j}P_t^B
=e^{-\lambda_{\varepsilon,j}t}\nu_{\varepsilon,j},
\qquad
\Pr_{\nu_{\varepsilon,j}}(\tau_B>t)
=e^{-\lambda_{\varepsilon,j}t},
\qquad
\mathbb E_{\nu_{\varepsilon,j}}\tau_B
=\lambda_{\varepsilon,j}^{-1}.
\]
出口位置的通量律为
\[
\Pr_{\nu_{\varepsilon,j}}(X_{\tau_B}=y)
=\lambda_{\varepsilon,j}^{-1}
\sum_{x\in D}\nu_{\varepsilon,j}(x)r_{\varepsilon,j}(x,y),
\qquad y\in B.
\]
若杀死算子有次主谱隙 \(\gamma_{\varepsilon,j}>0\)，任意初态在存活条件下以
\(O(e^{-\gamma_{\varepsilon,j}t})\) 收敛到 \(\nu_{\varepsilon,j}\)；只有当该混合时间远小于 \(\lambda_{\varepsilon,j}^{-1}\) 时，才称 \(A\) 为亚稳井。

**定理 77.1（可逆图的 Arrhenius 势垒）。** 另加可逆结构
\[
\pi_\varepsilon(x)=Z_\varepsilon^{-1}e^{-U(x)/\varepsilon},
\qquad
c_\varepsilon(x,y)
=\pi_\varepsilon(x)r_\varepsilon(x,y)
=Z_\varepsilon^{-1}a(x,y)e^{-H(x,y)/\varepsilon},
\]
其中 \(a(x,y)=a(y,x)\) 有统一正下上界，\(H(x,y)=H(y,x)\)，且图上 \(A\) 至 \(B\) 连通。定义
\[
\Phi(A,B)
=\min_{\gamma:A\leadsto B}
\max_{(x,y)\in\gamma}H(x,y),
\qquad
U_A=\min_{x\in A}U(x),
\qquad
\Gamma(A,B)=\Phi(A,B)-U_A.
\]
容量为
\[
\operatorname{cap}_\varepsilon(A,B)
=\inf_{h|_A=1,\ h|_B=0}
\frac12\sum_{x,y}c_\varepsilon(x,y)[h(y)-h(x)]^2.
\]
若井内混合时间为 \(e^{o(1/\varepsilon)}\)，且容量渐近确实由最小通信高度给出，则
\[
\lim_{\varepsilon\downarrow0}
\varepsilon\log\mathbb E_{\nu^A_\varepsilon}\tau_B
=\Gamma(A,B),
\qquad
\lim_{\varepsilon\downarrow0}
[-\varepsilon\log\lambda_\varepsilon]
=\Gamma(A,B).
\]
若还存在正的门 prefactor \(C_A,C_{\mathrm{cap}}\) 使
\[
\pi_\varepsilon(A)
=C_Ae^{-(U_A-U_\ast)/\varepsilon}(1+o(1)),
\qquad
\operatorname{cap}_\varepsilon(A,B)
=C_{\mathrm{cap}}
e^{-(\Phi(A,B)-U_\ast)/\varepsilon}(1+o(1)),
\]
则
\[
\lambda_\varepsilon
=\frac{C_{\mathrm{cap}}}{C_A}
e^{-\Gamma(A,B)/\varepsilon}(1+o(1)),
\qquad
\mathbb E\tau_B
=\frac{C_A}{C_{\mathrm{cap}}}
e^{\Gamma(A,B)/\varepsilon}(1+o(1)).
\]
有限图只给出门边缘和局部速率决定的 prefactor；经典 Hessian 版 Eyring–Kramers 公式还需要外加的小噪声扩散、非退化极小点和鞍点，不能由 FIB 图自动推出。

对固定 \(\varepsilon\) 的有限不可约链，连续时间经验测度
\[
\widehat\mu_T=\frac1T\int_0^T\delta_{X_s}\,ds
\]
满足 Donsker–Varadhan 形式
\[
I_\varepsilon(\mu)
=\sup_{g>0}
-\sum_x\mu(x)\frac{(\mathcal L_\varepsilon g)(x)}{g(x)},
\qquad
\Pr(\widehat\mu_T\approx\mu)\asymp e^{-TI_\varepsilon(\mu)}.
\]
只有另给 \(\varepsilon\downarrow0\) 的容量、谱或速率估计，才能从 \(I_\varepsilon\) 提取 \(\Gamma\)；大偏差符号本身不是势垒证明。

同一 \(E_j\) 可取所有跨井速率为 \(1\)，也可取跨割速率 \(e^{-c/\varepsilon}\)，从而产生完全不同的寿命指数。FIB 递归只给 \(E_j\)、词序和标签；连续时间速率、\(\varepsilon\)、井与目标、势函数、边界、时间单位和初态均为外加条件。若杀死核不可约性失败，准平稳分布可能不唯一；多门等高时 prefactor 需相加；非可逆链不能直接使用上述容量势垒。有限 \(j\)、固定 \(\varepsilon\) 无真正相变，且 \(j\to\infty\)、\(\varepsilon\to0\)、\(t\to\infty\) 的次序必须显式声明。因此这些是指定连续时间模型中的亚稳态结论，不是 FIB 自动给出的物理激活能。

## 78. FIB 上下文图的外加拉普拉斯、热核与谱维数

取 FIB 递归产生的有限上下文集 \(V_j\)，另行指定无向边集、对称导通率 \(c_{uv}=c_{vu}\ge0\)、质量 \(m_u>0\) 和可选杀死率 \(\kappa_u\ge0\)。定义
\[
(L_jf)(u)
=\frac1{m_u}\left[
\sum_{v\ne u}c_{uv}(f(u)-f(v))+\kappa_uf(u)
\right].
\]
在
\(\langle f,g\rangle_m=\sum_um_u\overline{f(u)}g(u)\) 下，
\[
\langle f,L_jf\rangle_m
=\frac12\sum_{u,v}c_{uv}|f(u)-f(v)|^2
+\sum_u\kappa_u|f(u)|^2\ge0.
\]
导通率、质量、边界和杀死率均为外加模型；FIB 只提供候选顶点、标签和可能的邻接顺序。

若
\(L_j\phi_{j,k}=\lambda_{j,k}\phi_{j,k}\)，取 \(m\)-正交归一基，令 \(H_t=e^{-tL_j}\)，则
\[
(H_tf)(u)=\sum_vp_{j,t}(u,v)m_vf(v),
\]
\[
p_{j,t}(u,v)
=\sum_ke^{-\lambda_{j,k}t}
\phi_{j,k}(u)\overline{\phi_{j,k}(v)}.
\]
热迹与根点局部谱测度分别为
\[
\Theta_j(t)=\sum_um_up_{j,t}(u,u)=\sum_ke^{-\lambda_{j,k}t},
\]
\[
\rho_{j,u}
=\sum_km_u|\phi_{j,k}(u)|^2\delta_{\lambda_{j,k}},
\qquad
m_up_{j,t}(u,u)
=\int e^{-t\lambda}\,d\rho_{j,u}(\lambda).
\]
当 \(\kappa=0\) 且图连通时，常数函数是唯一零模；有杀死或 Dirichlet 边界时零模可消失。

对图序列取归一化谱计数
\[
\nu_j=|V_j|^{-1}\sum_k\delta_{\lambda_{j,k}}.
\]
只有在指定根点或热力学极限并证明 \(\nu_j\Rightarrow\nu\) 后，才定义积分谱密度 \(N(E)=\nu([0,E])\)。若
\[
N(E)\sim CE^{d_s/2}\qquad(E\downarrow0),
\]
并满足相应 Tauberian 条件，则热迹低能端具有
\[
\Theta(t)/|V_j|\sim C't^{-d_s/2}.
\]
单个有限连通图在长时间趋向有限尺寸平台，不能直接由此定义非零扩散维数。若另加体积 \(|V_j|\asymp a^j\)、低模尺度 \(\lambda_{j+1}\asymp s^{-2}\lambda_j\) 及边界误差控制，则
\[
d_s=\frac{\log a}{\log s}.
\]
这需要外加图重整化，FIB 长度增长本身不提供 \(a,s\)。

若再把 \(m_u\) 解释为质量、\(c_{uv}\) 解释为弹簧刚度，则外加机械模型
\[
M\ddot q+Cq=0,\qquad L=M^{-1}C
\]
的正常模满足 \(\omega_{j,k}=\sqrt{\lambda_{j,k}}\)。只有平移不变局部图另有 Bloch 参数并满足 \(\lambda(k)\sim c^2|k|^2\) 时，才可称低频模为声学支；非周期 FIB 图必须使用谱测度，不能预设 Bloch 波矢。故本节不推出真实材料声子、热扩散、Weyl 普适律或物理维数。

## 79. 外加小噪声路径的大偏差、Hamilton–Jacobi 作用量与最小路径

固定 FIB 第 \(j\) 代并任选嵌入
\(\iota_j:E_j\to D_j\subset\mathbb R^d\)。给定外加漂移、噪声和小参数
\[
dX_t^{\varepsilon,j}
=b_j(X_t^{\varepsilon,j})\,dt
+\sqrt{\varepsilon}\,\sigma_j(X_t^{\varepsilon,j})\,dW_t,
\qquad
a_j=\sigma_j\sigma_j^{\mathsf T}.
\]
反射、吸收或周期边界、初态律和时间单位均需另行指定。若 \(a_j\) 可逆，对绝对连续路径 \(\phi\) 定义
\[
I_{j,T}(\phi\mid x_0)
=
\frac12\int_0^T
(\dot\phi_t-b_j(\phi_t))^{\mathsf T}
a_j(\phi_t)^{-1}
(\dot\phi_t-b_j(\phi_t))\,dt
\]
（\(\phi(0)=x_0\)，否则为 \(+\infty\)）。退化时使用控制形式
\[
I_{j,T}(\phi\mid x_0)
=
\inf_{\dot\phi=b_j(\phi)+\sigma_j(\phi)u}
\frac12\int_0^T|u_t|^2\,dt.
\]
若初态速率为 \(I_{0,j}\)，则在适当局部 Lipschitz、增长和紧性条件下，路径律以速度 \(1/\varepsilon\) 满足
\[
\limsup_{\varepsilon\downarrow0}\varepsilon\log\Pr(X^\varepsilon\in F)
\le-\inf_F I,
\qquad
\liminf_{\varepsilon\downarrow0}\varepsilon\log\Pr(X^\varepsilon\in G)
\ge-\inf_G I,
\]
其中 \(I=I_{0,j}(\phi(0))+I_{j,T}(\phi\mid\phi(0))\)。

对有界连续终点泛函 \(F\)，弱控制表示为
\[
-\varepsilon\log\mathbb E e^{-F(X^\varepsilon)/\varepsilon}
=
\inf_u\mathbb E\left[
F(X^{\varepsilon,u})+\frac12\int_0^T|u_t|^2dt
\right],
\]
\[
dX^{\varepsilon,u}
=(b_j+\sigma_ju)\,dt+\sqrt{\varepsilon}\sigma_j\,dW_t.
\]
Hamilton 量和 Lagrangian 为
\[
H_j(x,p)=p\cdot b_j(x)+\tfrac12p^{\mathsf T}a_j(x)p,
\qquad
L_j(x,v)=\sup_p\{p\cdot v-H_j(x,p)\}.
\]
有限终点代价的值函数在光滑处满足
\[
\partial_tV+b_j\cdot\nabla V
-\tfrac12\nabla V^{\mathsf T}a_j\nabla V=0,
\]
非光滑时按黏性解理解。吸引集 \(A\) 的准势
\[
V_{A,j}(x)
=\inf_{T>0,\ \phi(0)\in A,\ \phi(T)=x}I_{j,T}(\phi)
\]
在适当条件下满足
\(H_j(x,\nabla V_{A,j})=0\)，达到下确界的路径是最小作用路径；若极小值不存在，只能使用任意 \(\delta\)-最优路径。多个最小路径可同时存在，不能宣称唯一。

梯度扩散的外加特例
\[
dX_t=-D\nabla U(X_t)\,dt+\sqrt{2\varepsilon D}\,dW_t
\]
中，跨越目标集的指数代价为
\[
\Pr(\text{跨越 }B)
=\exp[-\Gamma(A,B)/\varepsilon+o(1/\varepsilon)],
\]
其中 \(\Gamma\) 是势垒差。这一结论依赖梯度结构、噪声协方差和边界，不由 FIB 递归给出。离散核若满足
\[
-\varepsilon\log P_{\varepsilon,j}(x,y)\to c_j(x,y),
\]
固定步数路径代价才可写成 \(\sum_kc_j(x_{k-1},x_k)\)；步数随 \(\varepsilon\) 或 \(j\) 增长时需另证指数紧性和连续作用量。

## 80. FIB 状态载体上的因果干预、反馈控制与 Bellman 识别

固定一代有限上下文闭包 \(E_j\)。FIB 递归只给状态、类型、词序和组合关系；动作集 \(\mathcal A\)、代价、受控核、观测、初态和时间协议均为外加数据。给定受控核 \(Q_j^a(x,y)\)、阶段代价 \(\ell_t(x,a)\) 和终端代价 \(G\)，策略 \(\pi_t(a\mid h_t)\) 产生路径律
\[
P_j^\pi(x_{0:T},a_{0:T-1})
=\mu_0(x_0)
\prod_{t<T}\pi_t(a_t\mid h_t)Q_j^{a_t}(x_t,x_{t+1}).
\]
这就是受控 g-formula；观察相关性不能自动解释为 \(do(A_t=a)\) 效应。

若 \(X_t\) 是受控 Markov 充分状态，值函数满足
\[
V_T(x)=G(x),
\]
\[
V_t(x)
=\min_{a\in\mathcal A}
\left\{\ell_t(x,a)+\sum_yQ_j^a(x,y)V_{t+1}(y)\right\}.
\]
有限时域下逐时达到最小值的确定性 Markov 策略最优。折扣 \(\gamma\in(0,1)\) 时
\[
(\mathcal BV)(x)
=\min_a\{\ell(x,a)+\gamma\sum_yQ_j^a(x,y)V(y)\}
\]
是 \(\gamma\)-压缩，故有唯一不动点；平均代价问题还需外加遍历性与通信类条件。

若加入参考动作律 \(\alpha_0(a\mid x)>0\) 和熵正则，则软 Bellman 值为
\[
V_t^\varepsilon(x)
=-\varepsilon\log\sum_a\alpha_0(a\mid x)
\exp\left[
-\frac{\ell_t(x,a)+\sum_yQ_j^a(x,y)V_{t+1}^\varepsilon(y)}
{\varepsilon}
\right],
\]
最优动作律为对应 Gibbs 权重。KL 正则是外加控制选择，不能自动等同于物理温度或耗散。

若只能观察 \(Y_t=g_j(X_t)\)，且 \(g_j\) 不满足受控 lumpability，标签过程一般不是 Markov；充分状态应改为后验信念
\[
b_{t+1}(y)
=\frac{O_j^{a_t}(y,Y_{t+1})
\sum_xb_t(x)Q_j^{a_t}(x,y)}
{\sum_{y',x}O_j^{a_t}(y',Y_{t+1})
b_t(x)Q_j^{a_t}(x,y')}.
\]
信念空间上的 Bellman 方程才给出 POMDP 控制。完整状态可见、顺序可忽略性、一致性和 positivity 成立时，观察数据才识别 \(Q_j^a\) 和有限时域策略值。若始终只观察动作 \(a=0\)，两个模型可以有相同观测律而在 \(do(a=1)\) 下给出不同终端分布；无 positivity 时反事实不可识别。

核扰动满足
\[
\sup_{x,a}\operatorname{TV}(Q_j^a(x,\cdot),
\widetilde Q_j^a(x,\cdot))\le\delta
\]
时，固定时域和有界路径代价下值差至多按 \(T\delta\) 线性累积；\(T\) 随 \(j\) 增长时必须控制 \(T\delta\)。FIB 不指定动作、干预语义、成本、可观测性或物理单位，故本节不推出真实因果律或普适控制常数。

## 81. 随机替换环境的频率、Lyapunov 率与衍射波动

确定性 FIB 拼接已经给出 primitive hull 的一个外加实现。本节考虑另一种外加延拓：每一层从有限替换族 \(\{\sigma_e:e\in E\}\) 中按平稳遍历环境 \(e_t\) 选择替换。FIB 只提供字母、合法上下文和可用的组合载体；环境律、替换族、位置实现和权重均为外加。

令 \(M_e\) 为 \(\sigma_e\) 的非负计数矩阵，并定义随机乘积
\[
C_n=M_{e_0}M_{e_1}\cdots M_{e_{n-1}}.
\]
若 \(\mathbb E\log^+\|M_{e_0}\|<\infty\)，且矩阵族在共同正锥上具有投影收缩，则 Furstenberg–Kesten 率
\[
\lambda_q
=\lim_{n\to\infty}\frac1n\log\|C_n\|
\]
几乎处处存在。若环境独立，则一阶平均计数的 annealed 率由
\(\log\rho(\mathbb E M_e)\) 给出，并满足
\[
\lambda_q\le\log\rho(\mathbb E M_e)
\]
在相应正性和初态条件下；严格不等的一般来源是矩阵乘积的次序相关性。若环境不是独立的，必须把环境状态并入联合乘积，不能逐层替换为 \(\mathbb E M_e\)。

设 \(\widehat c_n=C_nc_0/\mathbf1^{\mathsf T}C_nc_0\) 是归一化字母频率。若共同锥收缩足以使投影过程遗忘初态，则 \(\widehat c_n\) 在平稳遍历环境下收敛到由环境路径决定的平稳投影；环境本身遍历且投影观测可积时，该极限的分布不依赖初始相位。若环境退化为常值，恢复确定性 Perron 频率；若投影不收缩，则频率可能只在子序列收敛或保留初态记忆。

给定有界字母权重 \(w\)，随机替换产生的加权梳记为 \(\omega_\omega\)。在 quenched 语义下，若加权圆柱函数具有平稳自相关，则
\[
\eta_\omega(m)
=\lim_{N\to\infty}\frac1N
\sum_{n=0}^{N-1}
w(e_n)\overline{w(e_{n-m})}
\]
在适用的遍历定理下存在；其 Fourier 变换是该环境实现的衍射测度。annealed 自相关为
\[
\overline\eta(m)=\mathbb E\,\eta_\omega(m),
\]
一般不等于先把权重或替换矩阵平均后所得确定性模型的自相关。环境相关性可以把确定性纯点峰扩展为连续或奇异连续部分，具体类型需由替换族和环境谱证明，不能只由 FIB 拼接式判断。

若环境混合且中心化柱函数 \(F(T^ne)\) 的协方差绝对可和，则
\[
\frac1{\sqrt N}\sum_{n=0}^{N-1}
\bigl(F(T^ne)-\mathbb EF\bigr)
\Longrightarrow
\mathcal N(0,\sigma_F^2),
\]
\[
\sigma_F^2
=\operatorname{Var}(F)+
2\sum_{m\ge1}\operatorname{Cov}(F,F\circ T^m).
\]
这给出有限窗口频率和衍射强度估计的统计误差；若环境长记忆、协方差不可和或投影不收缩，只能保留遍历平均或标记为 open。随机替换的长度 Lyapunov 率、频率波动和谱测度是外加环境模型的结论，不是 FIB 递归自动产生的无序材料普适律。

## 82. 外加连续时间链的亚稳态、准平稳寿命与稀有跃迁

固定一代 \(j\)，令 \(E_j\) 为 FIB 递归产生的有限上下文集合。给定外加速率 \(r_{\varepsilon,j}(x,y)\ge0\)，定义
\[
(\mathcal L_{\varepsilon,j}f)(x)
=\sum_{y\ne x}r_{\varepsilon,j}(x,y)[f(y)-f(x)].
\]
对互不相交的亚稳井 \(A\)、目标 \(B\)，令 \(D=E_j\setminus B\) 和
\[
\tau_B=\inf\{t:X_t\in B\}.
\]
若 \(D\) 内核不可约，杀死半群有准平稳分布 \(\nu_{\varepsilon,j}\) 和主特征值 \(\lambda_{\varepsilon,j}>0\)：
\[
\nu_{\varepsilon,j}P_t^B
=e^{-\lambda_{\varepsilon,j}t}\nu_{\varepsilon,j},
\qquad
\Pr_{\nu_{\varepsilon,j}}(\tau_B>t)
=e^{-\lambda_{\varepsilon,j}t}.
\]
出口位置满足
\[
\Pr_{\nu_{\varepsilon,j}}(X_{\tau_B}=y)
=\lambda_{\varepsilon,j}^{-1}
\sum_{x\in D}\nu_{\varepsilon,j}(x)r_{\varepsilon,j}(x,y).
\]
次主谱隙控制从其他初态到准平稳律的条件收敛；只有井内混合时间远小于 \(\lambda_{\varepsilon,j}^{-1}\) 时，才是亚稳态。

另加可逆 Arrhenius 结构
\[
\pi_\varepsilon(x)=Z_\varepsilon^{-1}e^{-U(x)/\varepsilon},
\qquad
c_\varepsilon(x,y)
=Z_\varepsilon^{-1}a(x,y)e^{-H(x,y)/\varepsilon},
\]
其中 \(a,H\) 对称且有统一正性。定义通信高度
\[
\Phi(A,B)=\min_{\gamma:A\leadsto B}
\max_{(x,y)\in\gamma}H(x,y),
\qquad
\Gamma(A,B)=\Phi(A,B)-\min_{x\in A}U(x).
\]
容量为
\[
\operatorname{cap}_\varepsilon(A,B)
=\inf_{h|_A=1,h|_B=0}
\frac12\sum_{x,y}c_\varepsilon(x,y)[h(y)-h(x)]^2.
\]
若井内混合为 \(e^{o(1/\varepsilon)}\)，且容量确由最低通信高度控制，则
\[
\lim_{\varepsilon\downarrow0}
\varepsilon\log\mathbb E_{\nu^A_\varepsilon}\tau_B
=\Gamma(A,B),
\qquad
\lim_{\varepsilon\downarrow0}
[-\varepsilon\log\lambda_\varepsilon]
=\Gamma(A,B).
\]
Eyring–Kramers 前因子还需外加的门结构、局部几何和小噪声扩散；非可逆链不能直接使用此容量势垒。固定有限 \(j\) 和 \(\varepsilon\) 没有真正相变，且 \(j\to\infty\)、\(\varepsilon\to0\)、\(t\to\infty\) 的次序必须声明。

因此，同一 \(E_j\) 可用跨井速率 \(1\) 产生普通寿命，也可用 \(e^{-c/\varepsilon}\) 产生指数寿命。FIB 只提供状态、词序和标签，不唯一确定准势、激活能、温度或稀有跃迁律。

## 83. 分数高斯环境、非马尔可夫记忆与异常响应

取已指定的 FIB hull 或有限上下文过程 \(X_t\)，令有界观测 \(a_t=a(X_t)\)。另行加入独立分数高斯噪声 \(\xi_t\)，其协方差为
\[
R_H(k)=\frac{\sigma^2}{2}
\left(|k+1|^{2H}-2|k|^{2H}+|k-1|^{2H}\right),
\qquad 0<H<1.
\]
令 \(Y_t=a_t\xi_t\)。若 \(a_t\) 平稳且独立于 \(\xi\)，则
\[
\operatorname{Cov}(Y_0,Y_k)
=R_H(k)\,\mathbb E[a_0a_k].
\]
当 \(\mathbb E[a_0a_k]=\bar a^2+r_a(k)\) 且 \(r_a\) 可和时，长记忆主项由 \(\bar a^2R_H(k)\) 决定。部分和方差恒等式为
\[
\operatorname{Var}\left(\sum_{t=0}^{n-1}Y_t\right)
=nC_Y(0)+2\sum_{k=1}^{n-1}(n-k)C_Y(k).
\]
在精确分数高斯或残差可忽略的条件下，\(H>1/2\) 时
\[
\operatorname{Var}\left(\sum_{t<n}Y_t\right)
\sim \bar a^2\sigma^2n^{2H},
\qquad
n^{-H}\sum_{t<\lfloor ns\rfloor}Y_t
\Longrightarrow \bar a\sigma B_H(s).
\]
\(H=1/2\) 回到普通平方根标度；\(H<1/2\) 时零频抵消可能产生次扩散，但 FIB 调制的短程残差也可能重新产生平方根项。若 \(\bar a=0\)，主标度由 \(r_a\) 和联合谱决定，不能只由 \(H\) 判断。

更一般地，定义外加 Volterra 过程
\[
Z_t=\sum_{m\ge0}K_ma_{t-m}+\varepsilon_t,
\qquad
K_m\sim\kappa m^{d-1},\quad 0<d<\tfrac12.
\]
若创新谱在零频正且尾部满足线性过程的 Lindeberg 条件，则
\[
f_Z(\lambda)\asymp|\lambda|^{-2d},
\qquad
H=d+\tfrac12,
\]
并有
\[
\operatorname{Var}\sum_{t<n}Z_t\asymp n^{2H},
\qquad
n^{-H}\sum_{t<\lfloor ns\rfloor}Z_t
\Longrightarrow cB_H(s).
\]
\(\sum_m|K_m|<\infty\) 时恢复短记忆 CLT。若把该核解释为转移核，还必须另加非负性、归一化和历史条件概率一致性；线性记忆公式本身不是 Markov 核。

有限时域的粗糙响应可由
\[
U_a(t)=\int_0^t
\frac{(t-s)^{H_r-1/2}}{\Gamma(H_r+1/2)}
a_s\,dW_s,
\qquad 0<H_r<\tfrac12
\]
定义。在局部正则条件下，
\[
\mathbb E|U_a(t+h)-U_a(t)|^2\asymp h^{2H_r}.
\]
分数高斯噪声、Volterra 核、创新律、独立性和平稳测度都由外部模型指定；FIB 只提供调制状态。因此 \(H\) 和粗糙指数不是 FIB 自动推出的物理常数。

## 84. 外加多粒子平均场涨落、线性化流与 SPDE 协方差

固定 FIB 第 \(j\) 代有限上下文集 \(E_j\)，给定外加平均场核 \(Q_j(x,\mu)\)。令
\[
\mu_t^{N,j}=N^{-1}\sum_i\delta_{X_t^{N,i}},
\qquad
\Pr(X_{t+1}^{N,i}=y\mid\mathcal F_t)
=Q_j(X_t^{N,i},\mu_t^{N,j})(y),
\]
并设
\(\Phi_j(\mu)=\mu Q_{j,\mu}\)、\(\mu_{t+1,j}=\Phi_j(\mu_{t,j})\)。若 \(Q_j\) 对 \(\mu\) 可微、导数和二阶矩在固定时间窗内一致有界，初态为 iid，则
\[
\eta_t^{N,j}=\sqrt N(\mu_t^{N,j}-\mu_{t,j})
\]
收敛到高斯递推
\[
\eta_{t+1}=A_{t,j}\eta_t+\xi_{t+1,j},
\qquad
A_{t,j}=D\Phi_j(\mu_{t,j}).
\]
对测试函数 \(f,g\)，抽样噪声协方差为
\[
\Sigma_{t,j}(f,g)
=\sum_x\mu_{t,j}(x)
\sum_yQ_j(x,\mu_{t,j})(y)
[f(y)-Q_jf(x)]
[g(y)-Q_jg(x)].
\]
初态协方差为
\[
\Gamma_{0,j}(f,g)
=\mu_{0,j}(fg)-\mu_{0,j}f\,\mu_{0,j}g,
\]
并递推
\[
\Gamma_{t+1,j}
=A_{t,j}\Gamma_{t,j}A_{t,j}^{*}
+\Sigma_{t,j}.
\]
若初态仅交换而非渐近乘积，极限需条件于 de Finetti 变量，不能自动称为中心高斯。

连续时间外加速率 \(q_j(x,y;\mu)\) 给出
\[
\frac d{dt}\langle f,\mu_{t,j}\rangle
=\langle\mathcal A_{j,\mu_{t,j}}f,\mu_{t,j}\rangle,
\quad
\mathcal A_{j,\mu}f(x)
=\sum_yq_j(x,y;\mu)[f(y)-f(x)].
\]
线性化涨落满足
\[
d\eta_t(f)
=\eta_t(\mathcal A_{j,\mu_t}f)\,dt
+\langle D_\mu\mathcal A_{j,\mu_t}[\eta_t]f,\mu_t\rangle\,dt
+dM_t(f),
\]
其中
\[
d\langle M(f),M(g)\rangle_t
=\sum_x\mu_t(x)\sum_yq_j(x,y;\mu_t)
[f(y)-f(x)][g(y)-g(x)]\,dt.
\]
若水动力极限为反应—扩散密度 \(\rho_t\)，则 \(\sqrt N(\rho_t^N-\rho_t)\) 的漂移是 \(D\mathcal F(\rho_t)\)，噪声协方差由扩散梯度项和反应跳跃项共同给出。若有公共噪声，\(\rho_t\) 本身随机，CLT 必须条件于公共噪声。

若存在嵌入 \(\iota_j:E_j\to E_\infty\) 和流逼近误差 \(\eta_j\)，则
\[
\sqrt N[(\iota_j)_\#\mu_t^{N,j}-\mu_t^\infty]
=\eta_t^{N,j}
+\sqrt N[(\iota_j)_\#\mu_{t,j}-\mu_t^\infty].
\]
只有 \(\sqrt N\eta_j\to0\) 才能使用极限流作无偏 CLT 中心；若 \(\sqrt N\eta_j\to b_t\)，极限均值产生偏移。时间窗增长、网格粒子数不足或缺少统一可微性时，不能升级为统一 SPDE。所有噪声协方差和线性化系数均为外加模型数据。

## 85. FIB 多主体反馈、平均场 HJB–FP 系统与均衡不可辨识

固定有限上下文闭包 \(E_j\)，给定主体数 \(N\)、动作集 \(\mathcal A\)、受控核 \(Q_j^a(x,\mu,y)\)、相互作用代价 \(\ell_j(x,\mu,a)\) 和终端代价 \(G_j(x,\mu)\)。FIB 只给状态和组合关系。对经验测度 \(\mu\) 和动作律 \(\alpha(a\mid x)\)，定义
\[
\Phi_j(\mu,\alpha)(y)
=\sum_{x,a}\mu(x)\alpha(a\mid x)Q_j^a(x,\mu,y),
\]
\[
L_j(\mu,\alpha)
=\sum_{x,a}\mu(x)\alpha(a\mid x)\ell_j(x,\mu,a).
\]
规划者的分布值函数满足
\[
U_T(\mu)=G_j(\mu),
\qquad
U_t(\mu)
=\inf_\alpha\{L_j(\mu,\alpha)+U_{t+1}(\Phi_j(\mu,\alpha))\}.
\]
这是概率单纯形上的 HJB；统一 Lipschitz 和近乘积初态下，有限时域 \(N\)-主体值可在适当范数中以 \(O(N^{-1/2})\) 逼近该分布控制值。

给定人口流 \(m_t\)，个体最佳响应满足
\[
v_T(x)=G_j(x,m_T),
\]
\[
v_t(x)
=\min_a\left\{\ell_j(x,m_t,a)
+\sum_yQ_j^a(x,m_t,y)v_{t+1}(y)\right\}.
\]
要求前向一致性
\[
m_{t+1}(y)
=\sum_{x,a}m_t(x)\alpha_t^\ast(a\mid x;m_t)
Q_j^a(x,m_t,y)
\]
便得到有限时域 HJB–FP 均衡。有限状态下存在性可由混合策略紧性得到；唯一性仍需单调性、压缩性或严格凸势。单状态、动作 \(\{-1,+1\}\)、代价
\[
\ell(a,p)=-a(2p-1)
\]
已有至少两个纯均衡，说明 FIB 递归不能选择均衡分支。

若只有标签观察，受控核须满足 lumpability 才能在标签空间递推；否则必须使用信念状态。观察均衡流只识别动作加权核
\[
\bar Q_t(x,m_t,\cdot)
=\sum_a\alpha_t^\ast(a\mid x;m_t)Q_j^a(x,m_t,\cdot),
\]
没有动作 positivity、受控干预或已知核时，不能分解各 \(Q_j^a\)。给所有动作代价加同一状态基线也不改变 argmin，故代价本身还存在规范不可辨识。连续 HJB–FP 或 master 方程需要另加位置嵌入、生成器极限、边界和唯一性；它们不是 FIB 递归自动产生的物理均衡。

## 86. 随机导通率图的 quenched/annealed 热核同质化

令 \(V_j\) 是 FIB 上下文图的有限顶点集。边集、质量 \(m_u\) 和导通率环境 \(\omega\) 均外加；给定
\[
c_{uv}(\omega)=c_{vu}(\omega)\ge0,
\qquad
(L_j^\omega f)(u)
=\frac1{m_u}\sum_{v}c_{uv}(\omega)[f(u)-f(v)].
\]
对固定环境得到 quenched 热核
\(H_t^\omega=e^{-tL_j^\omega}\)；对环境平均得到
\[
\overline H_t=\mathbb E_\omega H_t^\omega.
\]
一般
\[
\mathbb E_\omega e^{-tL_j^\omega}
\ne e^{-t\mathbb E_\omega L_j^\omega},
\]
因为矩阵指数和环境平均不交换。只有环境在时间上快速独立切换，并满足相应谱隙和有界性时，才可在有限时间窗得到平均生成器的极限。

若 \(c_{uv}(\omega)\) 是平稳遍历随机场，且存在统一椭圆性
\[
0<c_-\le c_{uv}(\omega)\le c_+<\infty
\]
及尺度均匀的连通性，则在图序列的共同嵌入和紧性条件下，根点热核可有 quenched 同质化极限
\[
p_{j,t}^\omega(u_j,v_j)
\longrightarrow p_t^{\mathrm{eff}}(x,y)
\]
或相应的弱半群极限。有效导通率由环境的联合结构决定，通常不是边导通率的逐边算术平均；一维串联的有效系数呈调和平均，而并联结构呈算术型组合。若环境相关长度随 \(j\) 增长、统一椭圆性失效或图不具共同嵌入，只能给子列或有限窗结论。

随机热迹的涨落可写成
\[
\Theta_j^\omega(t)
=\sum_k e^{-t\lambda_{j,k}^\omega}.
\]
在环境混合且单边热迹方差可和时，中心化热迹可能满足
\[
\frac{\Theta_j^\omega(t)-\mathbb E\Theta_j^\omega(t)}
{\sqrt{|V_j|}}
\Longrightarrow\mathcal N(0,\sigma_\Theta^2(t)).
\]
若低能谱满足 quenched/annealed 两个不同的正则变分律，则其 Tauberian 热核幂律也可能不同；不能把一个平均谱密度自动当作典型环境的局部谱。

若把 \(m_u\) 与 \(c_{uv}\) 外加解释成质量和弹簧刚度，则每个环境给出不同正常模
\(\omega_k^\omega=\sqrt{\lambda_k^\omega}\)。只有另加周期或随机晶格的谱极限定理，才能讨论声子带、局域化或有效声速。FIB 递归只给候选顶点和组合关系，不决定随机导通率、有效介质、局域化长度或真实材料热传导。

## 87. 风险敏感 Bellman、非线性谱与小噪声作用量

固定有限 FIB 状态集 \(E_j\)，给定外加核 \(Q_j^a\)、阶段代价 \(\ell_j\)、终端代价 \(G_j\) 和风险参数 \(\theta>0\)。风险敏感值函数定义为
\[
V_t^\theta(x)
=\frac1\theta\log
\inf_\pi
\mathbb E_x^\pi
\exp\left[
\theta\left(
\sum_{s=t}^{T-1}\ell_j(X_s,A_s)+G_j(X_T)
\right)\right].
\]
它满足非线性 Bellman 递推
\[
V_T^\theta=G_j,
\]
\[
V_t^\theta(x)
=\frac1\theta\log\min_a
\left\{
e^{\theta\ell_j(x,a)}
\sum_yQ_j^a(x,y)e^{\theta V_{t+1}^\theta(y)}
\right\}.
\]
\(\theta\downarrow0\) 恢复普通期望代价；\(\theta>0\) 放大上尾，\(\theta<0\) 偏向下尾。若无限时域折扣或齐次核使乘法算子
\[
(\mathcal T_\theta f)(x)
=\min_a e^{\theta\ell_j(x,a)}
\sum_yQ_j^a(x,y)f(y)
\]
具有正性和原始性，则长期风险率由其非线性 Perron 根给出。动作并列、核不可约性或代价无界时，不能无条件声称唯一风险率。

对固定策略的路径奖励 \(A_T\)，有
\[
\frac1\theta\log\mathbb E e^{\theta A_T}
=\frac1\theta\Lambda_T(\theta),
\]
其一阶导数是平均奖励，二阶导数是方差；当 \(T\to\infty\) 且压力极限存在时，
\[
\Lambda(\theta)
=\lim_{T\to\infty}T^{-1}\log\mathbb E e^{\theta A_T}
\]
与奖励大偏差率函数通过 Legendre 对偶相连。此处的“自由能”只是风险敏感路径的谱量，不是热力学自由能。

若核本身由小噪声扩散或小步长 FIB 嵌入产生，令 \(\theta=1/\varepsilon\)，则风险敏感 Bellman 的对数变换在形式上趋向 Hamilton–Jacobi 方程；其 Lagrangian 由外加漂移 \(b_j\) 和扩散矩阵 \(a_j\) 决定。控制表示为
\[
-\varepsilon\log\mathbb E
e^{-F(X^\varepsilon)/\varepsilon}
=
\inf_u\mathbb E\left[
F(X^{\varepsilon,u})
+\frac12\int|u_t|^2dt
\right],
\]
但从有限状态核到连续作用量仍需统一嵌入、指数紧性和时间尺度。单步代价极限不自动给出长路径 LDP。

核扰动的风险敏感值对小的总变差并不总是稳定：指数代价会放大稀有路径，必须同时给出共同支撑、代价上界和 \(T\theta\) 的控制。故相同 FIB 状态载体上改变动作代价、风险参数或核，可产生不同非线性谱、最优策略和稀有事件偏好；FIB 递归不决定风险厌恶、温度、作用量或任何真实物理自由能。

## 88. FIB 上下文图上的渗流、随机簇与有限尺寸阈值

取 FIB 递归给出的有限上下文图 \(G_j=(V_j,E_j)\)，另行给每条边独立开通状态
\(\omega_e\sim\operatorname{Bernoulli}(p_e)\)，并令
\(u\leftrightarrow_\omega v\) 表示存在开通路径。簇为
\[
C_\omega(u)=\{v\in V_j:u\leftrightarrow_\omega v\}.
\]
边集、重复边处理、开通概率、独立性、边界和图序列均不是 FIB 递归自动确定的。

对均匀 \(p_e=p\) 和边界端集 \(B_j^-,B_j^+\)，跨越概率
\[
\Theta_j(p)=\Pr_p(B_j^-\leftrightarrow B_j^+)
\]
是 \(p\) 的单调多项式。平均易感度为
\[
\chi_j(p)
=\frac1{|V_j|}\sum_{u,v}\Pr_p(u\leftrightarrow v)
=\frac1{|V_j|}\sum_u\mathbb E_p|C_\omega(u)|.
\]
Russo 公式给出
\[
\frac d{dp}\Theta_j(p)
=\sum_{e\in E_j}
\Pr_p(e\text{ 对跨越事件为 pivotal}).
\]
单个有限图没有无限簇和严格临界点；可由
\(\Theta_j(p_{j,q})=q\) 定义依赖 \(q\)、边界和尺度的伪阈值。

若图序列在指定根点律下收敛到无限图 \(G\)，才可定义
\[
\theta(p)=\Pr_p(|C_\omega(o)|=\infty),
\qquad
p_c=\inf\{p:\theta(p)>0\}.
\]
若极限图只是无限路径，则 \(p_c=1\)，非平凡内部阈值不存在。若上下文图另加不可约多型 Galton–Watson 树结构，类型均值矩阵为 \(M\)、开边概率为 \(p_{ab}\)，则开簇均值矩阵
\[
B_{ab}=M_{ab}p_{ab}
\]
在标准二阶矩条件下以 \(\rho(B)=1\) 为生存阈值；普通词替换矩阵只有在确实实现独立树状分枝时才能充当 \(M\)。

若再假设尺度 \(L_j\)、体积 \(|V_j|\asymp L_j^{d_f}\)、相关长度
\(\xi(p)\asymp|p-p_c|^{-\nu}\)，则可条件性地写
\[
\Theta_j(p)
=\Phi((p-p_c)L_j^{1/\nu})+o(1),
\]
\[
\chi_j(p)\asymp
L_j^{\gamma/\nu}\Psi((p-p_c)L_j^{1/\nu}),
\qquad
\theta(p)\asymp(p-p_c)^\beta.
\]
这些是附加标度假设或待检验结果，不能把词长 \(|W_j|\sim\varphi^j\) 直接当图距离。相关开边、长记忆环境和重复边会改变阈值；有限图大簇不等于无限簇，FIB 不自动推出真实物理相变。

## 89. FIB 标签承载的外加动理学与碰撞极限

令 \(E_j\) 为有限 FIB 上下文，\(v\in\mathcal V\) 为外加速度或离散动量标签。给定非负碰撞核
\[
B_j((x,v),(x',v');v_1,v_1')
\]
和外加单粒子转移律，定义两粒子碰撞算子
\[
(Q_jf)(v,v')
=\sum_{v_1,v_1'}B_j(v,v';v_1,v_1')
[f(v_1,v_1')-f(v,v')].
\]
碰撞守恒的质量、动量和能量必须显式满足
\[
\sum_vQ_jf(v)=0
\]
对 \(f=1\) 以及相应的外加守恒函数成立；FIB 标签本身不赋予这些量物理含义。

若 \(N\) 粒子以弱相互作用碰撞，经验速度测度为
\[
\mu_t^{N,j}=\frac1N\sum_{i=1}^N\delta_{V_t^{N,i}},
\]
并且碰撞率按 \(N^{-1}\) 缩放、初态近似乘积、碰撞核有统一矩界，则固定时间窗内可能有
\[
\mu_t^{N,j}\Longrightarrow f_{t,j}(v)\,dv,
\]
其弱方程为
\[
\frac d{dt}\langle\varphi,f_{t,j}\rangle
=\langle\mathcal Q_j(f_{t,j},f_{t,j}),\varphi\rangle
+\langle\mathcal T_j f_{t,j},\varphi\rangle,
\]
其中 \(\mathcal Q_j\) 是由 \(B_j\) 外加定义的二次碰撞算子，\(\mathcal T_j\) 是外加输运或杀死项。非负性、质量守恒和解的唯一性需要另行证明；没有这些条件，只能声称子列弱极限。

若速度和空间同时嵌入，令 \(\varepsilon_j\) 为空间步长、\(\delta_j\) 为时间步长。只有在碰撞频率、输运尺度和二阶矩满足统一展开时，才可能得到
\[
\partial_t f+v\cdot\nabla_x f
=\mathcal Q(f,f)+\mathcal R(f)
\]
或在快碰撞极限下得到扩散、流体或反应扩散方程。碰撞不变分布的线性化给出外加 Boltzmann 型谱隙；若核具有多个守恒量，零模不唯一，衰减只在其正交补上成立。

同一 FIB 状态载体可取完全弹性核、随机重置核或带杀死的碰撞核，分别产生守恒、耗散或衰减动力学。碰撞核、粒子缩放、速度单位、空间嵌入和边界均外加，故本节不推出真实气体、温度、压强或 Boltzmann 普适律。

## 90. FIB 候选状态上的自适应实验设计、主动观测与后验收缩

固定有限上下文闭包 \(E_j\)。FIB 只给候选状态、标签和窗口结构；参数空间 \(\Theta\)、动作集 \(\mathcal A\)、受控核 \(Q_\theta^a\)、观测通道 \(O_\theta^a\)、先验 \(\Pi_0\) 和实验成本均为外加。历史 \(H_t\) 包含已选动作和观测，实验策略 \(q_t(a\mid H_t)\) 自适应选择下一动作。隐藏状态后验为 \(b_t^\theta\)，预测律为
\[
p_\theta(y\mid H_t,a)
=\sum_{x,x'}b_t^\theta(x)
Q_\theta^a(x,x')O_\theta^a(y\mid x').
\]
Bayes 更新为
\[
\Pi_{t+1}(d\theta)
=\frac{p_\theta(Y_{t+1}\mid H_t,A_t)\Pi_t(d\theta)}
{\int p_{\theta'}(Y_{t+1}\mid H_t,A_t)\Pi_t(d\theta')}.
\]
单步信息增益为
\[
IG_t(a)
=I(\Theta;Y_{t+1}\mid H_t,A_t=a)
=\mathbb E\!\left[
D_{\mathrm{KL}}(p_\Theta(\cdot\mid H_t,a)
\Vert\bar p_t(\cdot\mid H_t,a))
\mid H_t,a
\right],
\]
并有
\[
\mathbb E[H(\Pi_t)-H(\Pi_{t+1})\mid H_t,A_t=a]
=IG_t(a),
\]
\[
I(\Theta;D_T\mid H_0)
=\sum_{t<T}\mathbb E\,IG_t(A_t).
\]
高信息增益不必等于任务效用增益；带任务收益 \(R\) 时应在后验空间做 Bellman 递推，而不是只最大化 \(IG_t\)。

若 \(\Theta\) 有限、预测概率有正下界，真实参数为 \(\theta_0\)，且自适应策略满足对每个 \(\theta\ne\theta_0\)
\[
\liminf_{T\to\infty}\frac1T
\sum_{t<T}
D_{\mathrm{KL}}\!\left(
p_{\theta_0}(\cdot\mid H_t,A_t)
\Vert p_\theta(\cdot\mid H_t,A_t)
\right)>0
\quad\text{a.s.},
\]
则后验赔率 \(\Pi_T(\theta)/\Pi_T(\theta_0)\) 以正指数率趋于零。定义策略可达的观测等价
\[
\theta\sim_{\mathcal A}\theta'
\Longleftrightarrow
p_\theta(y\mid h,a)=p_{\theta'}(y\mid h,a)
\]
对所有可达 \((h,a,y)\) 成立。任何只使用动作集 \(\mathcal A\) 的实验至多把后验收缩到该等价类。

反例：两个参数在动作 \(a=0\) 下都产生
\(\operatorname{Bernoulli}(1/2)\)，在 \(a=1\) 下分别产生
\(\operatorname{Bernoulli}(0.9)\) 与
\(\operatorname{Bernoulli}(0.1)\)。若策略始终选 \(a=0\)，每步信息增益为零，后验不收缩；只有以正频率试验 \(a=1\) 才有 KL 分离。隐藏 FIB 状态被观测通道合并时，增加样本或重复同一探针不能恢复被消去的区别。信息增益、先验、动作成本、噪声和停止规则都是外加数据，不推出真实物理信息流或普适实验定律。

## 91. FIB 上下文图上的离散拓扑缺陷与上同调电荷

固定一个有限上下文闭包，构造有向图 \(G_j=(V_j,E_j)\)，再选定定向面集 \(F_j\) 将其填成有限胞腔复形 \(K_j\)。图的边、面的填充以及方向都不是 FIB 递归自动给出的。给每个顶点一个圆值相位
\(\theta:V_j\to\mathbb R/2\pi\mathbb Z\)，或更一般地给边一个圆值 \(1\)-上链
\(A\in C^1(K_j;\mathbb R/2\pi\mathbb Z)\)。沿定向边 \(e\) 取实提升
\(\Delta_e\)，满足 \(\exp(i\Delta_e)=A_e\)；顶点相位的主值差是一个特例。对定向面 \(f\) 定义
\[
q_f=\frac1{2\pi}\sum_{e\in\partial f}\Delta_e.
\]
由于边界回路的圆值相位乘积为 \(1\)，有 \(q_f\in\mathbb Z\)。当 \(q_f\ne0\) 时，称 \(f\) 为离散拓扑缺陷。改变实提升或作规范变换 \(A\mapsto A+d\chi\) 只改变分支或边界项，整数电荷与闭回路周期保持不变。

若只有图而未指定面，则可用
\(H^1(G_j;\mathbb Z)\cong\operatorname{Hom}(H_1(G_j),\mathbb Z)\)。对闭路 \(C\) 的积分周期为
\[
W_C=\frac1{2\pi}\sum_{e\in C}\Delta_e\in\mathbb Z,
\]
它描述环路绕数或 holonomy；“面涡旋”必须依赖额外的填充 \(K_j\)。若 \(A=d\theta\) 且 \(\theta\) 已在整个复形上给定，所有周期均为零；非零 \(q_f\) 需要奇异插值或外加规范场，不能归因于词序本身。

把 \(q=(2\pi)^{-1}d\widetilde A\) 视作实提升产生的整数 \(2\)-上链，则 \(dq=0\)。因此对任意 \(3\)-链 \(B\)，有
\[
\sum_{f\in\partial B}q_f=0.
\]
在闭定向二维复形上，总电荷 \(\langle q,[K_j]\rangle=0\)；有边界时内部电荷等于边界通量
\(Q_{\mathrm{int}}=\langle A,\partial K_j\rangle/(2\pi)\)。若 FIB 替换确实诱导保持边界的胞腔链映射
\(R_j:C_*(K_j)\to C_*(K_{j+1})\)，满足 \(\partial R_j=R_j\partial\)，则周期满足
\[
W_{R_jC}(A_{j+1})=W_C(R_j^*A_{j+1}).
\]
面映射度为 \(m\) 时总电荷按 \(m\) 倍传递；压缩或反向映射则可能使电荷消失或变号。仅有符号替换并未给出 \(R_j\)、面或方向，故不能推出拓扑荷守恒、量子化或缺陷数增长。

同一 FIB 词可以承载不同电荷。对词 \(\alpha\beta\alpha\beta\) 的四边形，取相位
\((0,0,0,0)\) 得 \(q=0\)；取 \((0,\pi/2,\pi,3\pi/2)\)，沿四条边取主值增量，环和为 \(2\pi\)，得 \(q=1\)。同一环图只作 \(1\)-复形时，\(H^1\) 保留一个整数周期；添加 \(2\)-胞腔填满该环后，该周期成为边界，\(H^1\) 可以降为零。这些反例说明拓扑量取决于外加相位、填充和映射，而非 FIB 词序单独决定。

若再给面场 \(q_f(\omega)\) 一个平稳遍历或有限相关的随机律，令
\[
Q_j=\sum_{f\in F_j}q_f,
\qquad
\rho_j=Q_j/|F_j|,
\qquad
\chi_j=|F_j|^{-1}\operatorname{Var}(Q_j).
\]
在面数趋于无穷、均值为 \(\mu\) 且协方差可和，并满足外加混合条件时，可能有
\[
|F_j|^{-1/2}(Q_j-|F_j|\mu)\Rightarrow N(0,\chi),
\qquad
\chi=\sum_r\operatorname{Cov}(q_0,q_r).
\]
若压力
\(p(\lambda)=\lim |F_j|^{-1}\log\mathbb E e^{\lambda Q_j}\) 存在且可微，则密度满足速率函数
\[
I(s)=\sup_\lambda\{\lambda s-p(\lambda)\}.
\]
独立的 \(\pm1\) 电荷给出 \(\chi=1\)，而严格中性约束 \(Q_j\equiv0\) 给出 \(\chi=0\)。随机相位、相关长度、边界、能量与相互作用均为外加，因此这些 CLT、易感率和大偏差结论不构成 FIB 内生的真实物理守恒律或相变定律。

## 92. FIB 词序上的转移矩阵、散射与局域化

固定有限上下文闭包或其路径子图。FIB 递归先给符号序列 \(a_n\)；若记忆阶为 \(r\)，可把
\(c_n=(a_{n-r+1},\ldots,a_n)\) 增广为状态并写成 \(c_{n+1}=\Phi(c_n)\)。再取外加势和跃迁
\(v_n=V(c_n,\eta_n)\)、\(t_n=T(c_n,c_{n+1},\eta_n)\ne0\)，定义 Jacobi 波方程
\[
t_n\psi_{n+1}+t_{n-1}\psi_{n-1}+v_n\psi_n=E\psi_n,
\qquad
\binom{\psi_{n+1}}{\psi_n}=T_n(E)\binom{\psi_n}{\psi_{n-1}},
\]
其中
\[
T_n(E)=
\begin{pmatrix}
(E-v_n)/t_n&-t_{n-1}/t_n\\
1&0
\end{pmatrix}.
\]
多通道时 \(\psi_n\in\mathbb C^d\)，转移矩阵为 \(2d\times2d\) 方块矩阵；自伴模型还需相应的辛或 \(J\)-酉结构。FIB 只决定 \(c_n\) 及允许的标签关系，不决定 \(V,T,E\) 的单位、波函数或环境。

长度 \(L\) 的乘积为 \(M_L(E)=T_{L-1}(E)\cdots T_0(E)\)。若 \((c_n,\eta_n)\) 平稳遍历且
\(\mathbb E\log^+\|T_0\|<\infty\)，Kingman 或 Furstenberg--Kesten 理论给出
\[
\gamma(E)=\lim_{L\to\infty}L^{-1}\log\|M_L(E)\|\quad\text{a.s.}
\]
在强不可约、非紧性和适当非共振条件下可进一步得到 Oseledets 分裂与指数衰减。若跃迁固定、存在积分态密度 \(N\)，则按所选归一化有 Thouless 公式
\[
\gamma(E)=\int\log|E-E'|\,dN(E')-\mathbb E\log|t_0|.
\]
一维非退化独立随机势在矩条件下通常有 \(\gamma(E)>0\)，定位长度可定义为 \(\xi(E)=1/\gamma(E)\)；对称点、相关退化和临界模型须单独检验。周期势在谱带内可有 \(\gamma=0\) 的 Bloch 波，在带隙中则有正指数。确定性 Fibonacci 型替换还可通过有序块乘积分析：若
\(\sigma(a)=ab,\ \sigma(b)=a\)，则在固定乘积约定下
\(M_{n+1}=M_{n-1}M_n\)。对 \(\det M_n=1\) 令 \(x_n=\tfrac12\operatorname{tr}M_n\)，有
\[
x_{n+1}=2x_nx_{n-1}-x_{n-2},
\]
且
\[
I=x_{n+1}^2+x_n^2+x_{n-1}^2-2x_{n+1}x_nx_{n-1}-1
\]
保持不变。这种确定性谱分析不能直接套用随机 Anderson 局域化结论。

把有限 FIB 片段接到外加无耗散引线，匹配左右行波得到散射矩阵
\(S(E)=\begin{psmallmatrix}r_L&t_R\\t_L&r_R\end{psmallmatrix}\)。自伴单通道模型满足
\(|r_L|^2+|t_L|^2=1\)，透射为 \(\mathcal T_L=|t_L|^2\)；多通道则用 \(\operatorname{Tr}(t^*t)\)，有增益或吸收时 \(S\) 不再酉。若边界阻抗有界且处于一维局域化相，通常有
\[
-\frac1{2L}\log\mathcal T_L\to\gamma(E),
\]
边界只贡献次线性项；转移乘积满足混合 CLT 时，\(L^{-1/2}(\log\|M_L\|-L\gamma)\) 可收敛到均值为零的正态分布，但方差不是普适常数。

在图而非路径上，可定义外加自伴图算子
\[
(H^\omega\psi)(u)=\sum_vt_{uv}(\omega)\psi(v)+v_u(\omega)\psi(u)
\]
及 Green 函数。若某能区满足分数矩条件
\[
\mathbb E|G^\omega(u,v;E+i0)|^s\le Ce^{-\mu d(u,v)},
\qquad 0<s<1,
\]
才可推出谱或动力学局域化。扩散标度、Thouless 时间、平均能级间距和无量纲导通数同样需要外加动力学与谱极限，不能由词长直接推出。

因此，同一 FIB 载体可以在不同外加势、跃迁、噪声、几何、边界和观测下承载 Bloch 传播、扩散、临界输运或指数局域化。FIB 递归本身只给出状态、标签、词序和组合关系，不能单独决定真实 Anderson 物理、散射定律或任何具有物理单位的普适统计律。

## 93. FIB 状态载体上的外加热力学协议、功恒等式与粗粒化不可逆性

固定有限 FIB 上下文闭包 \(S=E_j\)。递归只给状态、标签与词序；时间反演 \(\vartheta\)、能量 \(H_\lambda\)、温度 \(\beta^{-1}\)、协议 \(\lambda_0,\ldots,\lambda_T\)、初态律和转移核均是外加。正向第 \(k\) 步核为 \(P_k(x,y)\)，反向核记为 \(P_k^\dagger(\vartheta y,\vartheta x)\)，假设双向支撑相同，并以流入热浴的热量 \(q_k(x,y)\) 施加局部详细平衡
\[
\log\frac{P_k(x,y)}{P_k^\dagger(\vartheta y,\vartheta x)}=\beta q_k(x,y).
\tag{93.1}
\]
外加第一定律约定为 \(H_{\lambda_{k+1}}(y)-H_{\lambda_k}(x)=w_k(x,y)-q_k(x,y)\)。对路径 \(\omega=(x_0,\ldots,x_T)\)，令 \(\Theta\omega=(\vartheta x_T,\ldots,\vartheta x_0)\)，并设
\[
P_F(\omega)=\rho_0(x_0)\prod_{k<T}P_k(x_k,x_{k+1}),\quad
P_R(\Theta\omega)=\rho_T^\dagger(\vartheta x_T)\prod_{k<T}P_k^\dagger(\vartheta x_{k+1},\vartheta x_k).
\]
路径熵产生为
\[
\Sigma(\omega)=\log\frac{P_F(\omega)}{P_R(\Theta\omega)}
=\log\frac{\rho_0(x_0)}{\rho_T^\dagger(\vartheta x_T)}+\beta\sum_{k<T}q_k(x_k,x_{k+1}).
\tag{93.2}
\]
路径反演双射给出有限时域涨落恒等式
\[
\mathbb E_F e^{-\Sigma}=1,\qquad
\mathbb E_F\Sigma=D_{\rm KL}(P_F\Vert P_R\circ\Theta)\ge0.
\tag{93.3}
\]
若定义反向随机变量 \(\Sigma_R(\Theta\omega)=-\Sigma(\omega)\)，则共同支撑上
\[
p_F(s)=e^s p_R(-s).
\tag{93.4}
\]
零均值当且仅当正、反向路径律在反演下相同；负的单条路径熵产生可以出现，但平均值不能为负。

取两端 Gibbs 律 \(\pi_{\lambda_0},\pi_{\lambda_T}\)，其中 \(\pi_\lambda(x)=Z_\lambda^{-1}e^{-\beta H_\lambda(x)}\)，并令 \(\Delta F=-\beta^{-1}\log(Z_{\lambda_T}/Z_{\lambda_0})\)。由 (93.2) 和第一定律，\(W=\sum_{k<T}w_k\) 满足
\[
\Sigma=\beta(W-\Delta F),
\qquad
\mathbb E_F e^{-\beta W}=e^{-\beta\Delta F},
\qquad
\mathbb E_FW\ge\Delta F.
\tag{93.5}
\]
这说明功界和 Jarzynski 恒等式需能量、热浴与协议同时存在；它们不由 FIB 递归单独给出。

令 FIB 词或标签是外加映射 \(\phi:S\to\mathcal Y\)，并把逐时映射记为 \(Y=\phi^{\otimes(T+1)}(X)\)。推前正、反向路径律为 \(P_F^\phi\) 与 \(R^\phi\)，其中 \(R=P_R\circ\Theta\)。可见路径熵产生
\[
\Sigma_\phi(Y)=\log\frac{P_F^\phi(Y)}{R^\phi(Y)}
\]
满足
\[
\mathbb E_F\Sigma-\mathbb E_F\Sigma_\phi
=D(P_F\Vert R)-D(P_F^\phi\Vert R^\phi)
=\mathbb E_{Y\sim P_F^\phi}
 D\!\left(P_F(\cdot\mid Y)\Vert R(\cdot\mid Y)\right)\ge0.
\tag{93.6}
\]
故词层至多看见微观不可逆性；等号要求每个词纤维内正、反向条件路径律相同。若词映射把方向信息合并，词层可以表观详细平衡，而隐藏状态仍有正熵产生。

反例取同一三状态 FIB 载体 \(S=\{0,1,2\}\)，恒等时间反演和恒定能量。外加核为
\[
P(i,i+1\!\!\pmod3)=p,\quad P(i,i-1\!\!\pmod3)=q,\quad P(i,i)=1-p-q,
\]
其中 \(p,q>0,\ p+q<1\)，平稳律均匀。反向核交换 \(p,q\)，稳态路径熵产生率为
\[
\sigma=(p-q)\log(p/q),
\]
所以 \(p=q\) 时为零，\(p\ne q\) 时为正。若 \(\phi(0)=\phi(1)=\phi(2)\)，所有词路径都相同而 \(\Sigma_\phi=0\)；同一载体在保留方向的标签映射下又可显示正的词层熵产生。改变 \(p,q\)、能量协议或读出映射即可得到相反的可见统计，而 FIB 递归不变。

若支撑不互易、反向协议未定义或状态映射随层改变，(93.3)–(93.6)须改写为共同支撑上的扩展值相对熵；不能把有限路径恒等式无条件提升为长时熵率或真实第二定律。FIB 递归只提供组合载体，不提供温度、热量、能量、时间反演、局部详细平衡、熵单位或物理不可逆方向。

## 94. FIB 外加更新奖励的重尾稳定极限与连续时间随机游走

固定一条由 FIB ATOM 递归产生的上下文序列或再生块序列，记第 \(k\) 个块的上下文为 \(C_k\)。FIB 只给出 \(C_k\) 的组合来源、标签和词序；给定 \((C_k,C_{k+1})\) 后产生等待时间、奖励和位移的联合律
\[
K_{C_k,C_{k+1}}(dw,dy,dz)
\]
是外加的。它还必须另行指定再生协议、随机源、物理时钟和空间嵌入。令
\[
W_k>0,\qquad Y_k\in\mathbb R^m,\qquad J_k\in\mathbb R^d
\]
分别为等待、奖励和位移标记，
\[
T_n=\sum_{k=1}^nW_k,\qquad
N(t)=\max\{n:T_n\le t\},\qquad
R(t)=\sum_{k=1}^{N(t)}Y_k,\qquad
X(t)=\sum_{k=1}^{N(t)}J_k .
\]
这里采用“完成第 \(N(t)\) 个块即计入奖励”的约定；换用另一约定会改变共同跳跃处的极限版本。若 \(\mathbb EW<\infty\) 且块序列遍历，通常有 \(N(t)/t\to1/\mathbb EW\)，并在 \(\mathbb EY\) 有限时得到 \(R(t)/t\to\mathbb EY/\mathbb EW\)。

**定理 94.1（重尾更新时钟的稳定极限）。** 假设再生块独立同分布，或由具有足够混合和统一尾条件的有限型外加链调制，并且
\[
\Pr(W_1>t)\sim c_Wt^{-\alpha}L_W(t),
\qquad 0<\alpha<1,
\]
其中 \(L_W\) 慢变。取正则变换的 \(a_n\) 使得
\(n\Pr(W_1>a_n)\to1\)。在非晶格及标准域吸引条件下，存在稳定子过程 \(D_\alpha\)，使
\[
a_n^{-1}T_{\lfloor nu\rfloor}\Rightarrow D_\alpha(u),
\qquad
\mathbb E e^{-\lambda D_\alpha(u)}
=\exp\{-u\,\kappa_W\lambda^\alpha\}.
\]
其逆过程
\[
E_\alpha(t)=\inf\{u:D_\alpha(u)>t\}
\]
满足
\[
\frac{N(a_nt)}n\Rightarrow E_\alpha(t).
\]
逆过程的函数空间收敛一般须按 \(M_1\) 拓扑或有限维分布表述；常数 \(\kappa_W\) 和尺度由尾常数及 \(a_n\) 的归一化决定。\(E_\alpha\) 在固定时刻给出 Mittag--Leffler 型随机时钟，因此重尾等待造成的是随机的操作时间变换，而非一个由 FIB 词长直接确定的分数阶时钟。

**定理 94.2（更新奖励的稳定随机时间变换）。** 设奖励块在操作时间中满足域吸引条件。若 \(\mu_Y=\mathbb EY\) 存在，且存在 \(d_n\) 与 \(\beta\in(1,2]\) 使
\[
\frac1{d_n}\sum_{k=1}^{\lfloor nu\rfloor}(Y_k-\mu_Y)
\Rightarrow Z_\beta(u),
\]
其中 \(Z_\beta\) 是 \(\beta\) 稳定 Lévy 过程；并且等待和奖励的联合极限没有未声明的共同跳跃（例如二者独立，或其联合 Lévy 测度已给定），则
\[
\frac{R(a_nt)-\mu_YN(a_nt)}{d_n}
\Rightarrow Z_\beta(E_\alpha(t)).
\]
当 \(\beta=2\) 时，\(Z_2\) 是布朗运动，这给出被重尾逆时钟随机化的高斯奖励涨落。若 \(\beta\le1\)，\(\mu_Y\) 通常不存在，应改用相应的截尾中心化或直接写
\[
d_n^{-1}R(a_nt)\Rightarrow Z_\beta(E_\alpha(t));
\]
不能把有限均值公式强行延拓。等待与奖励在同一块内强相关时，联合极限一般是二维 Lévy 过程 \((D,Z)\)，共同跳跃会区分领先 CTRW、滞后 CTRW 和夹带奖励的版本；此时不能把 \(Z\) 与 \(E_\alpha\) 假设为独立。

上述表达也给出重尾更新奖励的首要量级。若奖励均值非零，则
\[
\frac{R(a_nt)}n\Rightarrow\mu_YE_\alpha(t),
\]
而不是收敛到确定的线性函数；若奖励均值为零且方差有限，则波动尺度为 \(d_n\asymp n^{1/2}\)。有限二阶、零均值且与等待独立时，令
\(\operatorname{Var}(J_1)=\sigma_J^2\)，则
\[
\mathbb E|X(t)|^2=\sigma_J^2 U_W(t),
\qquad U_W(t)=\mathbb EN(t).
\]
只有在纯幂律尾且慢变因子归一化为常数时，才可进一步写 \(U_W(t)\sim C_{\alpha,W}t^\alpha\)，从而典型位移量级为 \(t^{\alpha/2}\)。

**定理 94.3（CTRW 位移的稳定极限与异常扩散）。** 若位移标记在操作时间中满足
\[
(d_n^{(J)})^{-1}\sum_{k=1}^{\lfloor nu\rfloor}J_k
\Rightarrow A_\gamma(u),
\qquad 0<\gamma\le2,
\]
其中 \(A_\gamma\) 为对称或非对称 \(\gamma\) 稳定过程，且与等待极限的共同跳跃关系已明确，则在独立或无共同跳跃的情形
\[
\frac{X(a_nt)}{d_n^{(J)}}
\Rightarrow A_\gamma(E_\alpha(t)).
\]
有限二阶、零均值且与等待独立时给出 \(t^{\alpha/2}\) 的典型尺度；若 \(J_k\) 具有 \(\gamma\) 稳定尾，则纯幂律归一化给出量级 \(t^{\alpha/\gamma}\)，但当 \(\gamma<2\) 时二阶矩不存在，不能继续使用均方位移作定义。若等待和位移耦合，例如另加 \(J_k=vW_ke_1\)，则
\[
X(t)=vT_{N(t)}e_1
\]
与 \(t\) 同阶，极限由年龄和剩余等待的 Lamperti 型比例决定；这与独立有限方差跳步的次扩散完全不同。

**命题 94.4（FIB 类型调制只改变外加尾混合）。** 假设上下文 \(C_k\) 是一个外加不可约有限链，平稳频率为 \(\pi_i\)，且在类型 \(i\) 下
\[
\Pr(W_k>t\mid C_k=i)\sim c_i t^{-\alpha_i}L_i(t).
\]
在条件独立和足够混合下，平稳混合尾为
\[
\Pr(W_k>t)\sim
\sum_i\pi_i c_i t^{-\alpha_i}L_i(t),
\]
所以具有正频率的最小 \(\alpha_i\) 通常支配更新时钟；若频率不存在、类型团簇长记忆或尾部条件律相关，必须重新计算联合尾，不能套用该混合式。FIB 替换频率至多提供候选类型权重；\(\pi_i\)、\(c_i\)、\(\alpha_i\)、混合性和尾部相关均是外加假设。

反例保持同一 FIB 上下文序列不变：取 \(W_k\equiv1\)、独立有限方差对称 \(J_k\)，得到普通中心极限定标度 \(t^{1/2}\)；改取 Pareto-\(\alpha\) 等待而保持同一跳步，得到次扩散标度 \(t^{\alpha/2}\)；再把跳步与等待耦合为 \(J_k=vW_ke_1\)，位移变为 \(t\) 阶；改取独立的 \(\gamma\) 稳定跳步，则得到 \(t^{\alpha/\gamma}\) 的随机时间稳定过程。四种模型使用同一个 FIB 载体，却有不同甚至相反的长时统计律。若没有再生块的独立或混合条件、尾部域吸引、联合跳跃规则、初始延迟和边界约定，只能给有限时间恒等式或子列极限，不能声称稳定过程、Mittag--Leffler 时钟、CTRW 异常扩散或任何物理普适律。等待律、奖励律、随机时钟、空间嵌入、速度单位和观测协议全都外加；FIB 递归本身只提供状态、标签、词序和组合骨架。

## 95. 外加边界驱动 FIB 上下文的守恒流、熵产生与稳态大偏差

固定第 \(j\) 代 FIB 上下文图 \(E_j\)，另给内部跃迁反应 \(r\in\mathcal R_j\) 及计数状态 \(\eta\)。每个反应有化学计量向量 \(\nu_r\)、速率 \(c_r(\eta)\)；左右或多边界储库以 \(b\in\partial\) 的进出速率 \(c_b^+(\eta),c_b^-(\eta)\) 驱动。对线性守恒量 \(q\in\mathbb R^{E_j}\)，若
\[
q\cdot\nu_r=0\qquad(r\in\mathcal R_j),
\]
则内部动力学守恒；边界通量满足
\[
\frac d{dt}\langle q,\eta_t\rangle
=\sum_{b\in\partial}q\cdot\nu_b\,J_b(t),
\qquad
J_b=c_b^+-c_b^-.
\]
FIB 递归只给标签和组合图，不给 \(\nu_r\)、速率或储库化学势；守恒量必须由外加反应网络登记。若内部边表示粒子从 \(x\) 到 \(y\) 的流，经验电荷
\(m_q=\sum_xq(x)\eta(x)\) 满足离散连续性式
\[
\dot m_q=
\frac12\sum_{x,y}(q(y)-q(x))J_{xy}
+\sum_bJ_b^q.
\]

对有限不可约的外加连续时间链，给定边界速率后存在唯一稳态
\(\pi_j^{\mathrm{NESS}}\)；稳态流满足
\[
\operatorname{div}J=0\quad\text{在内部},
\qquad
J\cdot n=J_b\quad\text{在边界}.
\]
有限状态不可约性失败时，稳态可以不唯一。连续极限还需另给位置嵌入、网格宽度 \(h_j\)、密度尺度 \(K\) 和时间缩放；典型扩散尺度为 \(t\sim h_j^{-2}\)，边界速率须按 \(h_j\) 缩放以得到有限 Robin 通量。所得守恒场满足
\[
\partial_t\rho+\nabla\!\cdot j(\rho)=0,
\qquad
j(\rho)=-D(\rho)\nabla\rho+\chi(\rho)E,
\]
配以外加的 Dirichlet 储库密度、Robin 交换律
\(j\cdot n=\kappa(\rho_b-\rho)\)，或周期、零通量边界。若左右化学势不同，稳态可有非零流；相等化学势且满足详细平衡时才是平衡特例。

在离散链满足局部详细平衡记账时，稳态电流
\[
J_{xy}=\pi_j^{\mathrm{NESS}}(x)r(x,y)
-\pi_j^{\mathrm{NESS}}(y)r(y,x)
\]
的内部加边界熵产生率为
\[
\dot S_{\mathrm{prod}}
=\frac12\sum_{x,y}J_{xy}
\log\frac{\pi_j^{\mathrm{NESS}}(x)r(x,y)}
{\pi_j^{\mathrm{NESS}}(y)r(y,x)}
+\sum_bJ_b\mathcal A_b\ge0,
\]
其中 \(\mathcal A_b\) 是储库给定的化学势或热力学亲和力。若把储库状态并入总链，边界项同样包含在边求和中。连续本构满足相应 Einstein 或迁移率条件时，体熵产生可写为
\[
\sigma(\rho)=\int_\Omega
j(\rho)^{\mathsf T}\chi(\rho)^{-1}j(\rho)\,du\ge0,
\]
并须另加边界项 \(J_b\mathcal A_b\)。非平衡流、迁移率和亲和力均来自外加核，FIB 标签不自动给出热力学能、温度或熵。

令 \(K\) 为明确登记的系统尺度（可为粒子数、胞元数或体积；不能默认为 \(N\)）。在满足独立局部噪声、指数紧性和守恒连续性式的模型中，经验密度—流 \((\rho^K,j^K)\) 在固定宏观时域满足
\[
\Pr[(\rho^K,j^K)\approx(\rho,j)]
\asymp\exp[-K I_{[0,T]}(\rho,j)],
\qquad
\partial_t\rho+\nabla\!\cdot j=0,
\]
典型扩散噪声为 \(2\chi(\rho)\)，此时
\[
I_{[0,T]}
=\frac14\int_0^T\!\int_\Omega
[j-j(\rho)]^{\mathsf T}\chi(\rho)^{-1}
[j-j(\rho)]\,du\,dt
+I_{\partial}[j_b],
\]
其中 \(I_\partial\) 是外加边界储库通量的代价；若 \(\chi\) 奇异，改用受控通量表示并只在可达方向计费。稳态准势定义为
\[
V(\rho)=\inf_{\substack{T>0,\ \rho_{-T}=\bar\rho\\ \rho_0=\rho}}
I_{[-T,0]}(\rho,j).
\]
在稳态大偏差成立时，
\[
\Pr(\rho^K\approx\rho)\asymp e^{-K V(\rho)}.
\]
对应 Hamilton 泛函（含边界项）满足
\[
\mathcal H(\rho,p)=
\int_\Omega
[\nabla p\cdot j(\rho)
+\nabla p^{\mathsf T}\chi(\rho)\nabla p]\,du
+\mathcal H_\partial(\rho,p),
\qquad
\mathcal H\!\left(\rho,\frac{\delta V}{\delta\rho}\right)=0
\]
（黏性意义）。

需先固定 FIB 代数增长 \(j\)、粒子或体积尺度 \(K\)、网格宽度 \(h_j\)、时间缩放和边界速率；若要密度场而非测度值极限，通常还需每个宏观胞元的粒子数发散，例如 \(Nh_j^d\to\infty\)。在固定 \(j\)、固定 \(K\) 的有限链上只能得到有限状态 NESS；\(K\to\infty\) 的流体或大偏差极限要求统一速率、矩界、局部平衡及边界层控制。若内部反应不满足守恒、边界速率不具有限通量尺度、链不不可约，或 \(D,\chi\) 不足以保证唯一弱解，只能报告相应的子列或条件结果。改变同一 FIB 标签上的内部核或储库可把系统变成零流平衡、非零流 NESS、吸收态或多稳态；因此守恒律、熵产生、稳态准势和所谓热力学定律都不是 FIB 递归单独推出的。


## 96. FIB 词模式命中、稀有事件与外加 Poisson 簇

固定一个由 FIB 递归给出的模式 \(w^{(j)}=w_0\cdots w_{\ell_j-1}\)，并令外加读出序列 \(Y_0,Y_1,\ldots\) 取值于同一标签集。定义模式命中指标
\[
I_k^{(j)}
=\mathbf 1\{(Y_k,\ldots,Y_{k+\ell_j-1})=w^{(j)}\},
\qquad
N_n^{(j)}=\sum_{k=0}^{n-1}I_k^{(j)},
\]
以及首次命中时间
\[
\tau_j=\inf\{k\ge0:I_k^{(j)}=1\}.
\]
模式概率 \(p_j=\Pr(I_0^{(j)}=1)\)、读出序列的混合率、初态和时钟均为外加；FIB 只提供候选模式及其组合来源。

若 \(p_j\to0\)、\(n_jp_j\to\lambda\in(0,\infty)\)，读出序列满足足够强的混合和反聚簇条件，并且模式的自重叠在尺度 \(1/p_j\) 上可忽略，则模式出现点过程可能满足
\[
\sum_{k\ge0}I_k^{(j)}\,
\delta_{\,p_j k}
\ \Rightarrow\
\operatorname{Poisson}(1)
\]
的有限窗版本；相应地，在适当初态修正后
\[
p_j\tau_j\Rightarrow \operatorname{Exp}(1),
\qquad
\frac{N_{\lfloor t/p_j\rfloor}^{(j)}}{1/p_j}
\Rightarrow \operatorname{Poisson}(t).
\]
这些极限需要把模式长度、样本窗和概率尺度一起送到极限，固定有限模式的命中概率本身不会产生新的渐近律。

若模式存在自重叠，令
\[
\mathcal O_j
=\{r:1\le r<\ell_j,\
(w_r,\ldots,w_{\ell_j-1})
=(w_0,\ldots,w_{\ell_j-r-1})\}.
\]
相邻命中会形成簇，反聚簇条件被一个外加聚簇指数
\(\vartheta_j\in(0,1]\) 取代。典型形式为
\[
\Pr(p_j\tau_j>t)\longrightarrow e^{-\vartheta t},
\]
而出现点过程变成强度 \(\vartheta\) 的复合 Poisson 簇过程；簇大小的平均值在标准归一化下约为 \(1/\vartheta\)。若底层链存在周期、禁转移或长记忆，甚至不能得到 Poisson 簇极限，只能保留有限时间命中概率或在周期类内分别结算。

在外加独立标签律 \(\pi\) 下，
\[
p_j=\prod_{r=0}^{\ell_j-1}\pi(w_r);
\]
在平稳 Markov 读出核 \(Q\) 下，
\[
p_j=\pi(w_0)\prod_{r=0}^{\ell_j-2}Q(w_r,w_{r+1}).
\]
因此同一个 FIB 模式在独立公平读出、持续性 Markov 读出和带禁转移的读出下，可以分别具有不同的命中率、簇指数，甚至命中概率为零。若 \(Y_k\) 直接是确定性的 FIB 词，命中计数由词序完全决定，不存在上述随机 Poisson 结论。

模式命中可作为外加稀有成核、反应触发或报警事件的数学模型；要把命中次数换成物理速率，还需另给空间嵌入、体积、能垒、时钟和观测单位。FIB 递归本身只规定模式的组合结构，不能单独决定 Poisson 参数、等待分布、聚簇指数或任何物理成核定律。

## 97. FIB 类型队列网络的稳定性、重载反射极限与路由识别

固定一条由 FIB ATOM 递归产生的上下文序列，记第 \(j\) 层的上下文类型集合为 \(\mathcal C_j\)。给定外加类型映射
\[
\tau_j:\mathcal C_j\longrightarrow I=\{1,\ldots,d\},
\]
把标签或上下文送入一个队列、服务台或“队列—类别”坐标。FIB 只决定上下文的组合来源、词序和可观察标签；外加模型还须指定外部到达过程 \(A_i\)、服务潜势过程 \(S_i\)、服务纪律、路由矩阵 \(P=(p_{ik})\) 以及物理时钟。令 \(D_i(t)\) 为截至 \(t\) 的第 \(i\) 类服务完成数，\(T_i(t)\) 为分配给该类的服务时间，写成
\[
D_i(t)=S_i(T_i(t)),\qquad
Q(t)=Q(0)+A(t)-R D(t),\qquad R=I-P^{\mathsf T}.
\tag{97.1}
\]
若服务完成后以概率 \(p_{ik}\) 进入类别 \(k\)，则 \(R\) 扣除完成者并加入内部路由者；多台服务台时，\(T_i\) 还须满足每个资源集合的容量约束和选定的非抢占或抢占纪律。式 (97.1) 是队列守恒恒等式，不是 FIB 递归的推论。

假设在所选外加概率模型下
\[
\frac{A(t)}t\to\lambda,\qquad
\frac{S_i(t)}t\to\mu_i
\quad\text{几乎处处},
\tag{97.2}
\]
且 \(P\) 是开放路由矩阵（例如 \(\rho(P)<1\)）。名义访问率由交通方程
\[
\nu=\lambda+P^{\mathsf T}\nu,
\qquad \nu=R^{-1}\lambda
\tag{97.3}
\]
给出；单服务台集合 \(s\) 的负荷为
\[
\varrho_s=\sum_{i\in s}\frac{\nu_i}{\mu_i}.
\tag{97.4}
\]
在完全 \(S\) 型反射矩阵、可实现的非闲置纪律、不可约服务和适当的矩条件下，\(\max_s\varrho_s<1\) 是经典开放网络流体稳定性的充分条件：每个有限初值的流体轨道在统一有限时间内回到零邻域。若某一资源的负荷超过一，或 \(R\) 无法给出有限访问率，存在相应的线性工作量使轨道不能排空；这给出不稳定的证据。对任意调度纪律把 (97.4) 当作充要条件需要额外的可服务性与调度假设，不能由 FIB 类型频率单独推出。

将潜在服务写成满负荷服务减去闲置量，可得流体反射形式
\[
q(t)=q(0)+x t+R y(t),\qquad
x=\lambda-R\mu,
\tag{97.5}
\]
其中 \(q(t)\in\mathbb R_+^d\)，\(y_i\) 非减，并满足互补条件
\[
\int_0^\infty q_i(t)\,dy_i(t)=0.
\tag{97.6}
\]
若 \(R\) 是完全 \(S\) 矩阵且相应的 Skorokhod 映射 \(\Gamma_R\) 在所用路径拓扑下存在并连续，则
\[
q=\Gamma_R(q(0)+x\,\cdot).
\tag{97.7}
\]
(97.5) 将“队列不能为负”编码为边界反射；反射方向、服务容量及闲置规则均是外加结构。若反射问题不唯一、服务台共享资源形成非凸可行域，或队列可在零点继续积累内部工作，则不能直接使用单一 \(\Gamma_R\)。

**定理 97.1（有限方差重载极限的条件形式）。** 取一列外加队列网络，尺度参数为 \(n\)，并假设路由、服务纪律和反射矩阵在极限中固定。若
\[
\sqrt n\,x^{(n)}
=\sqrt n\bigl(\lambda^{(n)}-R\mu^{(n)}\bigr)\longrightarrow\theta,
\tag{97.8}
\]
且中心化的到达、服务和路由计数满足函数中心极限定理
\[
\widehat X^{(n)}(t)\Longrightarrow B_\Sigma(t),
\tag{97.9}
\]
其中 \(B_\Sigma\) 为协方差矩阵 \(\Sigma\) 的布朗运动，反射映射对这些路径连续，初始条件满足 \(Q^{(n)}(0)/\sqrt n\to q_0\)，则
\[
\widehat Q^{(n)}(t):=\frac{Q^{(n)}(nt)}{\sqrt n}
\Longrightarrow
Z(t)=\Gamma_R\bigl(q_0+B_\Sigma(t)+\theta t\bigr).
\tag{97.10}
\]
若另有完全资源汇聚和状态空间塌缩，存在工作量向量 \(\alpha\ge0\)，使主要极限可写成一维反射布朗运动
\[
W(t)=W(0)+\alpha^{\mathsf T}\theta\,t+\sigma_W B(t)+L(t),
\qquad W(t)\ge0,
\tag{97.11}
\]
其中 \(L\) 只在 \(W=0\) 时增加。漂移为负且存在平稳律时，\(W\) 的平稳尾为
\[
\Pr\{W>x\}
=\exp\!\left(-\frac{2|\alpha^{\mathsf T}\theta|}{\sigma_W^2}x\right),
\tag{97.12}
\]
在归一化成立的工作量坐标中成立。没有资源汇聚、反射矩阵连续性或函数中心极限定理时，不能把重载队列自动写成反射布朗运动；有限样本的排队波动也不由 FIB 词长决定。

若到达或服务的中心化和不属于高斯域，而满足正则变换归一化下的稳定极限
\[
\widehat X^{(n)}\Longrightarrow L_\gamma(t),
\qquad 0<\gamma<2,
\tag{97.13}
\]
则在跳路径上的反射映射可测且连续的附加条件下，候选极限是
\[
\widehat Q^{(n)}
\Longrightarrow
\Gamma_R(q_0+L_\gamma+\theta\,\cdot).
\tag{97.14}
\]
跳跃穿越边界时，左连续或右连续约定、溢出截断及路由同时跳跃会改变反射版本；若这些约定未登记，(97.14) 只有候选意义。对稳定尾原语，在一大跳、次指数和网络可达性条件下，平稳队列尾可出现
\[
\Pr\{Q_i>x\}
\sim C_i x^{-\alpha_*}L_*(x),
\qquad
\alpha_*=\min\{\alpha_A,\alpha_S,\alpha_{\rm route}\},
\tag{97.15}
\]
其中指数和慢变因子来自外加到达、服务和路由计数的联合尾；常数 \(C_i\) 由路由可达性、调度和相关结构决定。若不同重尾源相关、存在批量到达或一大跳条件失败，(97.15) 可能只给上下界或对数等价，不能将某个 FIB 频率当成普适尾指数。

**命题 97.2（聚合读出下的路由不可识别）。** 设参数为
\(\vartheta=(\lambda,\mu,P,\text{discipline})\)，观察只保留聚合队列长度、聚合到达与聚合离开及 FIB 标签 \(Y=\Psi(C,Q,D)\)。称 \(P\) 在该读出下可识别，当且仅当
\[
\mathcal L_\vartheta(Y)=\mathcal L_{\vartheta'}(Y)
\Longrightarrow
\vartheta'=\pi\vartheta
\tag{97.16}
\]
对允许的类别置换 \(\pi\) 成立。若 \(\tau_j\) 非单射且只观察总队列，则通常只能识别有效访问率 \(\nu=R^{-1}\lambda\)、总服务能力或它们的某些组合，不能分别识别 \(P\)、\(\lambda\) 和 \(\mu\)。要恢复路由，需要带类别的离开标签、受控干预、独立服务时间观测或能切开 FIB 观测纤维的额外关系。对旧读数作任何后处理不能恢复被 \(\Psi\) 合并的路径差异。

一个精确反例取同一 FIB 载体并令所有上下文映射到一个可见队列；外部到达为速率 \(\lambda\) 的 Poisson 过程。模型 A 的每个顾客只经历一次速率 \(m\) 的指数服务后离开。模型 B 每次服务尝试的时长为速率 \(m/p\) 的指数变量，完成后以概率 \(p\) 离开，以概率 \(1-p\) 沿隐藏路由返回，其中 \(0<p<1\)。模型 B 的一次顾客总服务时间是几何个数的指数和，其 Laplace 变换为
\[
\mathbb E e^{-sG}
=\frac{p(m/p)}{s+p(m/p)}
=\frac m{s+m},
\tag{97.17}
\]
故聚合队列长度和聚合离开过程与模型 A 的 \(M/M/1\) 队列完全相同；但隐藏服务尝试数、路由矩阵和内部完成计数不同。若 \(p\) 改变而不按 (97.17) 同步调整尝试率，则同一 FIB 可由稳定模型变为临界或不稳定模型；若把指数服务改为重尾服务，又可把有限方差重载极限换成稳定反射极限。因而相同 FIB 递归能够承载指数尾、重尾、平稳、临界或发散的排队统计。

队列稳定性、反射方向、重载缩放、尾部指数、路由矩阵、服务纪律、到达相关、物理时钟和观察通道全部属于外加模型。FIB 递归只提供类型、标签、词序和组合上下文；它不单独推出排队稳定定理、反射布朗运动、稳定尾或路由可识别性。

## 98. FIB 上下文图上的外加弹簧网络、线性弹性与机械涨落

令 \(G_j=(V_j,E_j)\) 是从 FIB 上下文递归抽取的有限图：顶点可以是 ATOM、上下文或经过外加映射后的等价类，边表示被选定的相邻关系或组合关系。FIB 只给出顶点的来源、标签和边的组合候选；要把 \(G_j\) 解释为弹性体或机械网络，还要外加嵌入
\(x:V_j\to\mathbb R^d\)、质量 \(m_v>0\)、弹簧常数 \(k_e\ge0\)、静止长度 \(\ell_e\)、阻尼矩阵以及物理单位。改变这些数据而保持同一 FIB 图不变，可以改变刚性、共振、应力和涨落的全部数值结论。

对每条边 \(e=(a,b)\) 设外加单位方向
\(\hat n_e=(x_b-x_a)/|x_b-x_a|\)，并令 \(B\) 为带方向的图关联矩阵。在线性化位移 \(u=(u_v)_{v\in V_j}\) 下，一维轴向伸长的线性算子可写为
\[
R u=\bigl(\hat n_e\cdot(u_b-u_a)\bigr)_{e\in E_j},
\qquad
K=R^{\mathsf T}W R,
\qquad
W=\operatorname{diag}(k_e).
\]
若保留横向位移、弯曲或超边相互作用，则 \(R\) 和 \(W\) 要按外加几何与本构律扩展；不能把简单图拉普拉斯自动当作物理刚度。在线性弹性范围内，势能为
\[
E(u)=\frac12u^{\mathsf T}Ku-f^{\mathsf T}u,
\tag{98.1}
\]
其中 \(f\) 是外加节点力。固定边界或刚性约束由矩阵 \(Cu=b\) 给出；自由平衡满足
\[
Ku-f+C^{\mathsf T}\lambda=0,
\qquad
Cu=b.
\tag{98.2}
\]
等价的 KKT 系统为
\[
\begin{pmatrix}K&C^{\mathsf T}\\ C&0\end{pmatrix}
\begin{pmatrix}u\\\lambda\end{pmatrix}
=
\begin{pmatrix}f\\b\end{pmatrix}.
\tag{98.3}
\]
只有在约束消除了刚体平移、转动及其他零能机制，并且剩余刚度在允许子空间上正定时，平衡位移才唯一。若 \(K\) 在该子空间上仍有核，则外力必须满足 Fredholm 相容条件；否则能量沿零模无界，不能声称存在有限平衡。用 Moore--Penrose 逆写出的 \(u=K^+f\) 只是在选定正交规范下的解，不能替代边界条件。

边的轴向应力（或等效内力）为
\[
\sigma_e=k_e(Ru)_e,
\qquad
\mathcal E=\frac12\sum_{e\in E_j}k_e(Ru)_e^2.
\tag{98.4}
\]
在节点、边或弹簧常数由外加随机机制生成时，\(K\) 是随机矩阵。给定固定约束空间和确定力，位移、应力与柔度成为随机变量；例如若随机力 \(f\) 有协方差 \(\Sigma_f\)，则在可逆约束子空间上
\[
\operatorname{Cov}(u)=K^{-1}\Sigma_fK^{-1},
\qquad
\operatorname{Cov}(\sigma)
=WRK^{-1}\Sigma_fK^{-1}R^{\mathsf T}W.
\tag{98.5}
\]
若 \(K\) 本身随机，式 (98.5) 只能在条件于 \(K\) 后使用，再对其随机律取平均；\(\mathbb E[K^{-1}]\) 一般不等于 \(\mathbb E[K]^{-1}\)。因此只知道 FIB 图的平均度数或平均标签频率，不能推出平均柔度、应力方差或失稳概率。稀疏边、近零弹簧常数和接近机构的几何会使最小特征值趋近零，从而放大 (98.5) 的长程响应。

在外加热浴温度 \(T>0\)、固定约束和 \(f=0\) 时，若允许位移服从谐近似的 Gibbs 分布
\[
\mathrm d\mathbb P_T(u)
\propto
\exp\!\left(-\frac{1}{2k_{\mathrm B}T}u^{\mathsf T}Ku\right)\mathrm du,
\tag{98.6}
\]
则约束子空间上的协方差为
\[
\mathbb E_T[u]=0,
\qquad
\operatorname{Cov}_T(u)=k_{\mathrm B}T\,K^{-1}.
\tag{98.7}
\]
带有静力 \(f\) 时，均值移到 \(K^{-1}f\)，协方差仍为 (98.7)。这给出外加谐网络中的涨落—响应关系：柔度矩阵就是位移对小力的导数，也是热涨落协方差除以 \(k_{\mathrm B}T\)。若存在未约束零模，(98.6) 不可归一化；必须固定规范、加边界或给零模有限体积正则化。温度、Boltzmann 权重和热浴并非 FIB 递归的内生对象。

若每个顶点有质量矩阵 \(M=\operatorname{diag}(m_vI_d)\)，无阻尼的小振动方程为
\[
M\ddot u+Ku=0.
\tag{98.8}
\]
在约束子空间上求解广义本征问题
\[
K\phi_\alpha=\omega_\alpha^2M\phi_\alpha.
\tag{98.9}
\]
其非负本征频率、零频机构和模态密度由 \(G_j\)、嵌入、\(k_e\) 与 \(m_v\) 的联合数据决定。加入外加黏性阻尼 \(C\succeq0\) 和简谐驱动 \(f(t)=\Re(f_0e^{-\mathrm i\omega t})\) 后，频率响应为
\[
\widehat u(\omega)
=\bigl(K-\omega^2M-\mathrm i\omega C\bigr)^{-1}f_0,
\tag{98.10}
\]
只在该逆存在的频率上定义。共振峰、耗散宽度、局部放大和相位滞后由外加 \(M,C\)、边界和观测向量决定；它们不是 FIB 词序的必然后果。若网络含随机 \(k_e,m_v,C\)，可以研究样本平均响应、谱测度或共振峰的尾分布，但首先必须登记这些随机变量的联合律。相同图在均匀刚度、双峰刚度和具有零刚度概率的模型下可分别得到窄谱、分裂谱和准静态软模。

对一列增大的 FIB 图，定义约束后的柔度观测
\[
J_j(a,b)=a^{\mathsf T}K_j^+b,
\qquad
\rho_j(\omega)=\frac1{|V_j|}\sum_\alpha\delta_{\omega_\alpha}(\omega).
\tag{98.11}
\]
在外加随机图模型、边参数分布、嵌入尺度、质量归一化和边界抽样规则下，\(J_j\) 或 \(\rho_j\) 才可能有概率极限、集中界或经验谱测度极限。若这些规则使最小特征值以概率趋近零，则柔度可能发散；若边界锚定、刚度下界和几何条件统一控制，则可得到有界响应。仅有 FIB 递归的上下文深度或标签频率，既不能选择哪一种极限，也不能保证极限存在。

一个不可识别性构造是：保持同一 \(G_j\) 和同一外加标签读出，模型 A 取所有 \(k_e=1\)，模型 B 取所有 \(k_e=\varepsilon\)，并同时将外力单位缩放为模型 A 的 \(\varepsilon\) 倍。两模型可以产生相同的无量纲位移标签序列，却有不同的物理力、能量和频率尺度；若不缩放外力，位移、柔度和应力则按 \(\varepsilon^{-1}\)、\(\varepsilon\) 等比例改变。再令部分边的 \(k_e=0\)，还可在不改动 FIB 递归的情况下引入机构和不可归一化的热涨落。由此，任何声称“FIB 递归推出刚度、杨氏模量、声子谱、热应力或普适弹性阈值”的陈述，都缺少外加几何、本构、质量、边界、温度和尺度假设。

结论是：FIB 上下文图可以作为弹簧、阻抗或质量—弹簧网络的组合载体；给定外加嵌入、边参数、约束、力和热浴，线性平衡、应力协方差、机械模态和频率响应可以按 (98.1)–(98.11) 推导。由 FIB 本身固定的只有候选节点、边及其组合来源；刚度矩阵、零模结构的物理解释、涨落定律、共振统计和任何单位化机械定律都属于外加模型。

## 99. FIB 上下文图上的外加接触过程、吸收相变与准平稳感染波

固定第 \(j\) 层 FIB 递归给出的上下文集合 \(V_j\)，以及由上下文相容、相邻或替换关系选出的候选有向图 \(G_j=(V_j,E_j)\)。FIB 只提供顶点的组合来源和候选关联；有向性、边权 \(a^{(j)}_{uv}\)、度归一化、时间单位、感染率和恢复率都由外加模型指定。令 \(\eta_t\in\{0,1\}^{V_j}\) 表示占据或感染状态，\(\eta^v\) 表示把顶点 \(v\) 改为占据，\(\eta_v\) 表示把它改为空，则一个外加接触过程的生成元可写成
\[
\begin{aligned}
(\mathcal L_j f)(\eta)
={}&\sum_{v\in V_j}\delta^{(j)}_v\eta(v)\,[f(\eta_v)-f(\eta)]\\
&+\sum_{(u,v)\in E_j}\lambda^{(j)}_{uv}a^{(j)}_{uv}\eta(u)(1-\eta(v))\,[f(\eta^v)-f(\eta)].
\tag{99.1}
\end{aligned}
\]
若采用按出度归一化，应将 \(a_{uv}^{(j)}\) 换成 \(a_{uv}^{(j)}/d_u^{(j)}\)；这会改变临界参数。无外加免疫、输入或自发出生时，全空状态 \(\mathbf0\) 是吸收态，\(\tau_j=\inf\{t:\eta_t=\mathbf0\}\) 是灭绝时间。式 (99.1) 是选择的粒子系统，不是 FIB 递归的推论。

在每个有限连通 \(G_j\) 上，只要恢复率为正且感染不能从空集重新产生，\(\tau_j<\infty\) 几乎处处成立；因此有限图不存在严格的正密度平稳感染态。若把所有非空状态组成瞬态集合，限制生成矩阵记为 \(Q_j^\circ\)，并设其不可约，则存在 \(\alpha_j>0\) 和概率向量 \(\nu_j\) 使
\[
\nu_jQ_j^\circ=-\alpha_j\nu_j,\qquad
\Pr_{\nu_j}(\eta_t\in\cdot\mid \tau_j>t)=\nu_j(\cdot),
\tag{99.2}
\]
且
\[
\Pr_{\nu_j}(\tau_j>t)=e^{-\alpha_jt}.
\tag{99.3}
\]
对一般初态，若瞬态半群有唯一主特征值且与其余谱分离，则在条件 \(\tau_j>t\) 下趋于 \(\nu_j\)；不可约性、谱隙或初态可达性失败时，可能出现多个准平稳极限，不能从图的大小自动推出唯一 \(\nu_j\)。\(\alpha_j\) 与 \(\nu_j\) 依赖全部外加速率和边权，而非仅依赖 FIB 词长。

要定义无限体积的生存相变，需先给出图列的极限。设带根图 \((G_j,o_j)\) 在局部弱拓扑下收敛到带根图 \((G_\infty,o)\)，并同时规定速率场的局部收敛与统一界。对从根单点感染的过程定义
\[
\lambda_c=\inf\{\lambda:\Pr_{\{o\}}^{\,G_\infty,\lambda}(\tau=\infty)>0\}.
\tag{99.4}
\]
在平移不变、遍历且过程具有适当单调耦合的模型中，\(\lambda<\lambda_c\) 时从有限初集灭绝，\(\lambda>\lambda_c\) 时有正生存概率，并可由从全占据初态所得的上不变测度 \(\bar\nu_\lambda\) 描述活动相。非齐次或非规则图上，生存概率可能依赖根和类型；弱生存与强生存的阈值也可能不同，式 (99.4) 必须逐项注明所用根、初态和极限。局部弱收敛单独不足以传递生存事件，因为生存是无限时间事件；还需尾部紧性、耦合或单调性等附加条件。

一个可检验的灭绝上界来自外加线性支配。令
\[
B_j=(\lambda^{(j)}_{uv}a^{(j)}_{uv})_{u,v},
\qquad
D_j=\operatorname{diag}(\delta_v^{(j)}).
\]
若
\[
\rho(D_j^{-1}B_j)<1
\tag{99.5}
\]
（或更强的 \(\|D_j^{-1}B_j\|_\infty<1\)），且速率有统一界，则一阶感染数被次临界多型分枝过程支配，给出有限时间存活尾界和无限图上的灭绝充分条件。均匀恢复 \(\delta_v^{(j)}=\delta\) 时，这简化为 \(\rho(B_j)/\delta<1\)。这是充分条件而非一般临界值公式；相反方向需要构造在图上嵌入的定向渗流、分枝过程或块过程，并验证相关长度、独立性和边界误差。故从 \(\rho(B_j)=\delta\) 直接断言接触过程临界点，只在额外的树状、均场或比较模型中成立。

有限尺寸的“临界点”只能是伪临界定义。例如令
\[
p_j(\lambda,t)=\Pr_{\{o_j\}}(\tau_j>t),
\qquad
\rho_j^{\rm qs}(\lambda)
=\nu_j[|\eta|/|V_j|].
\]
选择观测窗 \(T_j\) 后可定义 \(\lambda_c^{(j)}\) 为 \(p_j(\lambda,T_j)=1/2\)，或定义为响应率、方差、寿命的峰值位置。不同的 \(T_j\)、边界、根和归一化会给出不同的 \(\lambda_c^{(j)}\)。只有在指定图极限、时间窗口与统一有限尺寸估计后，才能讨论 \(\lambda_c^{(j)}\to\lambda_c\)。在活动相且满足额外准平稳混合和稀有吸收假设时，可有
\[
\mathbb E_{\nu_j}\tau_j\asymp \exp\{c_j|V_j|\},
\tag{99.6}
\]
从而在 \(1\ll t\ll\mathbb E\tau_j\) 的窗口内观察到近似稳定感染密度；(99.6) 是吸收接触过程的有限尺寸条件式，不能与一般连续时间亚稳态结论混同，也不是所有图列都成立。临界处可能是多项式寿命或无统一标度，必须由具体模型估计。

若图列是稠密、边权按总度归一化，并且初态与局部相关满足传播混沌条件，经验感染密度
\[
\rho_j(t)=|V_j|^{-1}\sum_{v\in V_j}\eta_t(v)
\]
可在有限时间上收敛到外加均场方程
\[
\dot\rho=\beta_{\rm eff}\rho(1-\rho)-\delta\rho,
\qquad
\beta_{\rm eff}=\lim_j\text{（所选归一化下的有效感染度）},
\tag{99.7}
\]
其线性化阈值为 \(\beta_{\rm eff}=\delta\)。稀疏局部树图通常保留邻居相关，(99.7) 需改成成对闭合、消息传递或随机图上的接触过程，不能把均场阈值移植到任意 FIB 图。若另加嵌入 \(x_j:V_j\to\mathbb R^d\)、网格尺度 \(h_j\) 和扩散标度，使邻居交换项收敛为 \(D\Delta u\)，并满足局部混合与界面紧性，则可得到反应—扩散近似
\[
\partial_tu=D\Delta u+ru-ku^2,
\qquad r=\beta_{\rm eff}-\delta,
\tag{99.8}
\]
其前沿速度、形状和各向异性由 \(D\)、嵌入、边界和初始感染集决定。若没有这些空间和缩放假设，“感染波”只是一组图上的占据边界，FIB 不提供物理距离或速度。

多型或带免疫的吸收粒子系统可令感染类型为 \(a\in\{1,\ldots,m\}\)，外加邻接—转移核给出下一代矩阵 \(K\)。在稀疏早期阶段，若可由多型分枝过程支配或被其支配，\(\rho(K)<1\) 给出灭绝的充分条件，\(\rho(K)>1\) 在满足嵌入和非退化条件时给出正生存的候选条件；类型转换、恢复和竞争使临界面成为矩阵而非单一标量。观测若只给 FIB 标签总数、词频或上下文聚合，则不同的 \((B,\delta,K)\) 可能诱导相同观测律，感染率、恢复率、临界点和准平稳密度不可由 FIB 结构单独识别。

结论是：FIB 递归可提供生成接触过程所需的状态索引、候选邻接和类型来源；吸收态、恢复—感染时钟、速率矩阵、图列极限、边界、观测和极限缩放均须外加。生存阈值、准平稳律、有限尺寸相变和感染波可以在这些外加条件下成立，也可以因改换同一 FIB 图上的速率、归一化或观测而消失或反向；它们不是 FIB 递归内生的普适物理定律。

## 100. FIB 标签观测族的 Fisher 信息、局部渐近正态与统计实验等价

固定第 \(j\) 个 FIB 上下文闭包 \(C_j\)。递归只给出 \(c\in C_j\) 的状态、标签、词序和可组合关系；令 \(a\) 表示外加探针或实验动作，\(\theta\in\Theta\subset\mathbb R^d\) 为连续参数，观测由外加核 \(K^a_{\theta,j}(dc,dy)\) 产生。动作可以依赖过去历史，但策略 \(q_t(a\mid H_t)\) 不显含未知参数。由该实验得到的观测律记为 \(P^{\mathsf E_j}_\theta\)，其中噪声、时钟、初态、转移核和参数化均属于外加模型。

**定义 100.1（外加观测实验与 Fisher 信息）。** 在具有密度的观测实验中，设
\[
L_{j,T}(\theta;y)=\frac{dP^{\mathsf E_j}_{\theta,T}}{d\mu}(y),
\qquad
\ell_{j,T}(\theta)=\log L_{j,T}(\theta;Y),
\]
并令 \(S_{j,T}(\theta)=\nabla_\theta\ell_{j,T}(\theta)\)。若微分与积分可交换且 \(\mathbb E_\theta S_{j,T}=0\)，则
\[
\mathcal I_{j,T}(\theta)
=\mathbb E_\theta[S_{j,T}S_{j,T}^{\mathsf T}]
=-\mathbb E_\theta[\nabla_\theta^2\ell_{j,T}(\theta)]
\tag{100.1}
\]
是该外加统计实验的 Fisher 信息矩阵。若观测由条件密度 \(p_\theta(y_t\mid H_{t-1},a_t)\) 逐步生成，且策略与 \(\theta\) 无关，则在正则条件下分数为条件得分之和，信息分解为
\[
\mathcal I_{j,T}(\theta)
=\mathbb E_\theta\!\left[
\sum_{t<T}\mathcal I_\theta(H_{t-1},a_t)
\right],
\]
\[
\mathcal I_\theta(h,a)
=\mathbb E_\theta[
\nabla\log p_\theta(Y_t\mid h,a)
\nabla\log p_\theta(Y_t\mid h,a)^{\mathsf T}
\mid h,a].
\tag{100.2}
\]
这里需要条件得分为鞅差；依赖观测、隐藏状态或自适应动作会改变条件期望与长期协方差，它们不由 FIB 递归确定。

若读出为外加高斯噪声
\[
Y_t=m_\theta(c_t,a_t)+\varepsilon_t,
\qquad
\varepsilon_t\sim N(0,\Sigma_\theta(c_t,a_t)),
\]
且条件独立，则每个观测的 Fisher 信息为
\[
\mathcal I_\theta(c,a)
=J_\theta(c,a)^{\mathsf T}\Sigma_\theta^{-1}J_\theta(c,a)
+\frac12\left[
\operatorname{tr}\!\left(
\Sigma_\theta^{-1}\partial_r\Sigma_\theta
\Sigma_\theta^{-1}\partial_s\Sigma_\theta
\right)\right]_{r,s},
\tag{100.3}
\]
其中 \(J_\theta=\nabla_\theta m_\theta\)。协方差未知时，第二项是参数信息的一部分；把它误当作已知噪声会虚增信息。若 \(J_\theta h=0\) 且 \(\partial_h\Sigma_\theta=0\)，则 \(h\) 是该观测的零信息方向。

**定理 100.2（连续 FIB 近似下的 LAN 条件形式）。** 设 \(j_n\) 为一列 FIB 上下文及其外加观测实验，真实参数为 \(\theta_0\)。令 \(r_n\to\infty\) 为有效信息尺度，并假定对每个固定 \(h\in\mathbb R^d\)，局部参数 \(\theta_n=\theta_0+h/r_n\) 仍在参数域内。若在 \(P_{\theta_0}^{\mathsf E_{j_n}}\) 概率下
\[
\Delta_n:=r_n^{-1}S_{j_n,T_n}(\theta_0)\Longrightarrow N(0,\mathcal I),
\qquad
r_n^{-2}\mathcal I_{j_n,T_n}(\theta_0)\longrightarrow\mathcal I,
\tag{100.4}
\]
且三阶余项满足局部均匀的 \(o_{P_{\theta_0}}(1)\)，则
\[
\log\frac{dP^{\mathsf E_{j_n}}_{\theta_0+h/r_n}}
{dP^{\mathsf E_{j_n}}_{\theta_0}}
=h^{\mathsf T}\Delta_n-\frac12h^{\mathsf T}\mathcal I h
+o_{P_{\theta_0}}(1).
\tag{100.5}
\]
这就是以 \(r_n^{-1}\) 为局部尺度的 LAN。若条件得分是鞅差，(100.4) 可由条件方差的稳定极限和 Lindeberg 条件验证；若观测是平稳混合序列，则 \(\mathcal I\) 还含有跨时协方差的长程和。FIB 层数趋于无穷并不自动给出 (100.4)：必须另加读出噪声、重复数、混合率和设计矩阵的极限。

在确定性标签加高斯独立噪声的特例
\[
Y_{n,k}=m_\theta(c_{n,k},a_{n,k})+\sigma_n\varepsilon_{n,k},
\qquad
\varepsilon_{n,k}\stackrel{\rm iid}{\sim}N(0,I),
\]
若 \(g_{n,k}=\nabla_\theta m_{\theta_0}(c_{n,k},a_{n,k})\) 且
\[
\frac1n\sum_{k<n}g_{n,k}g_{n,k}^{\mathsf T}\longrightarrow G,
\qquad G\succeq0,
\]
则
\[
\mathcal I_n(\theta_0)
=\sigma_n^{-2}\sum_{k<n}g_{n,k}g_{n,k}^{\mathsf T}.
\tag{100.6}
\]
当 \(G\) 满秩时，有效局部尺度为 \(r_n=\sqrt n/\sigma_n\)；若 \(G\) 奇异，只能在 \(\operatorname{ran}G\) 上作 LAN，\(\ker G\) 中的方向在该近似下不可见。故重复数、噪声缩放和 FIB 上下文的经验 Gram 矩阵共同决定连续参数极限，递归本身不决定 \(\sqrt n\) 还是其他速率。

**推论 100.3（Cramér–Rao 与零信息方向）。** 对固定外加实验和正则参数点，若估计量 \(\widehat\psi\) 无偏且估计 \(\psi(\theta)\in\mathbb R^r\)，则
\[
\operatorname{Cov}_\theta(\widehat\psi)
\succeq
D\psi(\theta)\,\mathcal I_{j,T}(\theta)^\dagger
D\psi(\theta)^{\mathsf T}
\tag{100.7}
\]
在 \(D\psi\) 消灭 \(\ker\mathcal I\) 的条件下成立；\(\dagger\) 为 Moore--Penrose 逆。满秩时退化为通常的 \(D\psi\,\mathcal I^{-1}D\psi^{\mathsf T}\)。若存在 \(h\ne0\) 满足 \(\mathcal I h=0\)，则局部似然沿 \(h\) 没有二阶变化；需要区分 \(\theta\) 与 \(\theta+th\) 的估计不可能得到有限的统一方差界。若分解 \(\theta=(\psi,\lambda)\)，其中 \(\lambda\) 为噪声、时钟或初态等 nuisance 参数，则有效信息为
\[
\mathcal I_{\psi\cdot\lambda}
=\mathcal I_{\psi\psi}
-\mathcal I_{\psi\lambda}
\mathcal I_{\lambda\lambda}^{\dagger}
\mathcal I_{\lambda\psi},
\tag{100.8}
\]
其核还包含与 nuisance 方向混合的不可辨识切向量。未知噪声不能在事后以“已知”处理而删除 (100.8) 的损失。

**定义 100.4（统计实验等价与 FIB 观测压缩）。** 两个实验
\(\mathsf E=(P_\theta:\theta\in\Theta)\) 和
\(\mathsf F=(Q_\theta:\theta\in\Theta)\) 的 Le Cam 缺陷定义为
\[
\delta(\mathsf E,\mathsf F)
=\inf_M\sup_{\theta\in\Theta}
\|MP_\theta-Q_\theta\|_{\rm TV},
\qquad
\Delta(\mathsf E,\mathsf F)
=\max\{\delta(\mathsf E,\mathsf F),\delta(\mathsf F,\mathsf E)\},
\tag{100.9}
\]
其中 \(M\) 遍历参数无关的 Markov 核。若 \(Y=\Phi(C,Z)\) 是从完整 FIB 状态或路径 \(Z\) 的参数无关观测压缩，则由数据处理不等式
\[
\mathcal I_Y(\theta)\preceq\mathcal I_Z(\theta),
\qquad
\|P^Y_\theta-P^Y_{\theta'}\|_{\rm TV}
\le\|P^Z_\theta-P^Z_{\theta'}\|_{\rm TV}.
\tag{100.10}
\]
若完整似然比对 \(Y\) 的 sigma 代数可测，即 \(Y\) 是参数族的充分统计量，则压缩不损失信息，\(\delta(\mathsf Z,\mathsf Y)=0\)；若还存在参数无关的恢复核在所有 \(\theta\) 上精确复原完整律，则两实验等价。仅有同一 Fisher 矩阵或同一前两阶矩不推出实验等价。

**命题 100.5（可达动作下的实验不可辨识）。** 令 \(\mathcal A_q\) 为策略 \(q\) 以正概率访问的动作—历史对。若存在 \(h\ne0\)，使对所有可达 \((a,H)\)
\[
\partial_h p_{\theta_0}(y\mid H,a)=0
\quad\text{几乎处处},
\tag{100.11}
\]
则 \(h\) 属于总 Fisher 信息的核；任何自适应重复仍只能识别商空间
\(\Theta/\!\sim_{\mathcal A_q}\)，其中
\[
\theta\sim_{\mathcal A_q}\theta'
\Longleftrightarrow
p_\theta(\cdot\mid H,a)=p_{\theta'}(\cdot\mid H,a)
\quad\forall(H,a)\text{ 可达}.
\tag{100.12}
\]
若一个动作的条件信息矩阵在其访问频率 \(\rho_a>0\) 下补足其余方向，则总信息可能恢复满秩；但这依赖外加策略和成本约束。始终重复同一 FIB 标签探针无法补回观测通道已合并的差异。

精确例子取两个参数 \((\theta_1,\theta_2)\)，在所有上下文上外加读出
\[
Y_k=(\theta_1+\theta_2)\phi(c_k)+\sigma\varepsilon_k,
\qquad
\varepsilon_k\sim N(0,1).
\]
此时 \(g_k=\phi(c_k)(1,1)^{\mathsf T}\)，故 Fisher 矩阵的秩至多为 \(1\)，方向 \((1,-1)\) 精确不可辨。若另加动作 \(a=1\)，读出改为 \(Y_k=\theta_1\phi(c_k)+\sigma\varepsilon_k\) 并以正频率访问，联合 Gram 矩阵可满秩；若该动作永不访问，任何样本量仍保持原不可辨识。若把 \(\sigma\) 也未知，则均值方向与噪声尺度必须同时纳入参数，Cramér–Rao 界按 (100.8) 重新计算。

若先验 \(\Pi_0\) 在 \(\theta_0\) 邻域具有正连续密度，且 (100.5) 中 \(\mathcal I\succ0\)，则标准后验局部极限为均值偏移的正态律，协方差为 \(\mathcal I^{-1}\)；先验只在一阶局部极限中提供平移项。若 \(\mathcal I\) 奇异，后验只能沿可辨识商空间收缩，零信息方向的极限由先验和更高阶项决定，不能宣称普适的正态收缩率。

FIB 边界是：FIB 递归只提供 \(C_j\) 的组合载体、标签和上下文；参数族、观测核、噪声协方差、重复尺度、动作策略、先验、时钟和连续极限均由外加模型声明。Fisher 信息、LAN、Cramér–Rao 界、Le Cam 实验距离和后验收缩只对该外加统计实验成立；相同 FIB 递归可在不同噪声和探针下产生满秩、奇异或完全等价的统计实验，因而不能单独推出任何真实物理测量定律或普适信息率。

## 101. FIB 上下文上的外加随机界面生长与 KPZ 型极限

固定第 \(j\) 层上下文图 \(G_j=(V_j,E_j)\)，另给位置嵌入、边长和边界条件，并在每个顶点放置高度 \(h_t^{(j)}(v)\)。离散梯度 \(\nabla_j\)、拉普拉斯算子 \(\Delta_j\)、沉积率、噪声强度以及时间单位都由外加模型规定。一个有限图上的随机界面可写成
\[
\mathrm dh_t^{(j)}(v)
=\left[
\nu_j\Delta_jh_t^{(j)}(v)
+\frac{\lambda_j}{2}
\left|\nabla_jh_t^{(j)}(v)\right|^2
+F_j(v,h_t^{(j)})
\right]\mathrm dt
+\sqrt{2D_j}\,\mathrm dW_t(v).
\tag{101.1}
\]
在离散跳跃模型中，(101.1) 可由外加沉积、黏附和局部重排事件的生成元近似；有限图上无需对非线性项作连续场的重整化。FIB 递归只提供顶点的组合来源和词序，不提供 \(\Delta_j\)、\(\nabla_j\)、\(\nu_j\)、\(\lambda_j\)、\(D_j\)、噪声或外力。

若存在共同空间嵌入、网格尺度 \(h_j\to0\)、统一稳定性和噪声紧性，并且离散初值和边界收敛，则可能得到外加连续模型
\[
\partial_t h
=\nu\Delta h+\frac{\lambda}{2}|\nabla h|^2+\sqrt{2D}\,\xi
\tag{101.2}
\]
的弱极限或重整化极限。取 \(\lambda=0\) 时得到 Edwards--Wilkinson 型线性高斯界面；取 \(\lambda\ne0\) 时，在一维平移型局部模型和适当短程噪声条件下，典型 KPZ 标度假设写成
\[
W(L,t)\asymp L^\alpha
f(t/L^z),
\qquad
\beta_{\rm grow}=\alpha/z.
\tag{101.3}
\]
标准一维 KPZ 模型的候选指数为
\(\alpha=1/2\)、\(z=3/2\)、\(\beta_{\rm grow}=1/3\)；这些指数属于附加模型的普适性结论，不能从任意 FIB 词序直接推出。若噪声是长程、淬火或具有强相关，或若 \(\lambda=0\)，指数和极限可能改变。

有限图上的粗糙度例如定义为
\[
W_j^2(t)=|V_j|^{-1}\sum_{v\in V_j}
\left(h_t^{(j)}(v)-\overline h_t^{(j)}\right)^2,
\qquad
\overline h_t^{(j)}=|V_j|^{-1}\sum_vh_t^{(j)}(v).
\tag{101.4}
\]
其均值、方差和生长速度取决于沉积规则、边界、初态和噪声协方差。若把同一 FIB 图置于无噪声且 \(\lambda_j=0\) 的规则下，平坦初态可保持确定性；若加入独立沉积噪声，则会产生高斯粗糙化；若加入非线性斜率增强，则可进入 KPZ 型涨落；若改为淬火障碍，则可能出现钉扎与退钉扎。FIB 词长 \(|W_j|\) 只有在另加位置嵌入、样本窗口和时间标度后才可作为界面尺寸，不能自动充当 \(L\)。

界面高度的物理单位、沉积通量、表面张力、噪声温度、边界驱动和观测方式都属于外加模型。因而 (101.1)–(101.4) 可以在声明的离散规则下产生平滑、线性高斯、KPZ 或钉扎界面，但 FIB 递归本身不决定粗糙度指数、增长速度、普适类或真实表面生长定律。

## 102. FIB 上下文图上的外加自旋 Gibbs 场、相变与相共存

固定有限上下文图 \(G_j=(V_j,E_j)\)，在每个顶点放置自旋
\(\sigma_v\in\{-1,+1\}\)。给定外加耦合 \(J_{uv}\)、外场 \(h_v\) 和逆温 \(\beta\)，定义
\[
H_j(\sigma)
=-\sum_{\{u,v\}\in E_j}J_{uv}\sigma_u\sigma_v
-\sum_{v\in V_j}h_v\sigma_v,
\qquad
\mu_j^{\beta,J,h}(\sigma)
=\frac{e^{-\beta H_j(\sigma)}}{Z_j(\beta,J,h)}.
\tag{102.1}
\]
有限图上的 \(Z_j\) 是有限和，因此对有限 \(j\) 的 \(\beta\) 和 \(h\) 依赖解析；真正的相变只能讨论一列图、边界条件和参数极限。FIB 只给出上下文和候选组合关系，不给出自旋解释、耦合、逆温、边界或极限图列。

在一列图上，若外加相互作用满足 Dobrushin 型高温条件，例如
\[
\sup_{u\in V_j}\sum_{v\ne u}
\tanh\!\bigl(\beta |J_{uv}|\bigr)<1
\tag{102.2}
\]
并且该界在 \(j\) 上一致，则可得到唯一 Gibbs 状态、边界影响的指数衰减和相关函数的统一控制。相反，若图列具有合适的可分离边界、耦合为铁磁且满足 Peierls 型低温界，则正、负边界条件可能收敛到不同的无限体积状态 \(\mu^+\) 与 \(\mu^-\)，形成相共存；这需要图的几何、割集增长和低温能垒等外加条件，不能从词频或替换矩阵直接推出。

有限图的磁化和易感率可定义为
\[
m_j=\frac1{|V_j|}\sum_{v\in V_j}
\mathbb E_{\mu_j}[\sigma_v],
\qquad
\chi_j=\frac{\beta}{|V_j|}
\operatorname{Var}_{\mu_j}\!\left(\sum_{v\in V_j}\sigma_v\right).
\tag{102.3}
\]
若只改变均匀外场 \(h\)，有限体积恒等式为
\[
\partial_hm_j=\chi_j.
\tag{102.4}
\]
在相共存极限中，先取 \(j\to\infty\) 再取 \(h\downarrow0\) 与先取 \(h=0\) 的次序可能不同；有限尺寸峰值位置只能定义伪临界参数。临界指数、关联长度和有限尺寸标度还需另加图列、边界和统一估计，不能把 FIB 代数增长率直接当作临界指数。

同一个 FIB 上下文载体可取 \(J_{uv}=0\)，得到独立自旋和零外场磁化；也可取强铁磁耦合并选择正、负边界，得到非零磁化与相共存；取反铁磁耦合或受挫边图，还可得到不同的有序或无序状态。若再给出外加 Glauber 或其他 Markov 动力学，混合时间、亚稳态和动力学相变仍由翻转率和时钟决定。故 Gibbs 权重、相变、相共存、磁化和响应均是外加统计力学模型的结论，FIB 递归本身不选择任何一种真实物理相。

## 103. FIB 词序索引上的外加 Wright–Fisher、Kingman 共祖与等位基因扩散

令第 \(j\) 个 FIB 上下文所给出的有限词集合为 \(\mathcal C_j\)，并给定外加采样映射
\(q_j:\{1,\ldots,k\}\to\mathcal C_j\)，把样本个体的标签或词序位置接到这些上下文上。\(q_j\) 只是观测索引，不把 FIB 词自动解释为个体、亲本或基因座。设外加单倍体 Wright–Fisher 群体大小为 \(N\)：每一代的 \(N\) 个后代独立、等概率选择一名亲本。对当前的 \(r\) 条祖先谱系，上一代亲本标签的碰撞给出分割过程 \(\Pi^{(N)}_g\)，且
\[
\Pr(\text{没有碰撞}\mid r)
=\frac{(N)_r}{N^r}
=1-\binom r2N^{-1}+O(N^{-2}).
\]
在固定样本数、\(N\to\infty\)、世代时间按 \(g=\lfloor Ns\rfloor\) 缩放时，任意给定的一对谱系以速率一相遇，而同一代出现两次以上独立碰撞的概率为 \(O(N^{-2})\)。因此分割过程收敛到 Kingman 共祖过程，其生成元可写为
\[
(\mathcal A f)(\pi)
=\sum_{\{a,b\}\subseteq\pi}
\bigl[f(\pi^{a\sim b})-f(\pi)\bigr],
\tag{103.1}
\]
其中 \(\pi^{a\sim b}\) 将两条块合并。这个极限依赖固定样本、均匀亲本抽样和上述时间缩放；它不是 FIB 递归的内生极限。

更一般地，若每一代的亲本权重为 \(p_{N,1},p_{N,2},\ldots\)，则二重、三重碰撞分别受
\[
c_{N,2}=\sum_i p_{N,i}^2,
\qquad
c_{N,3}=\sum_i p_{N,i}^3
\]
控制。若选取时间尺度使 \(c_{N,2}^{-1}\) 为一代单位，并且
\(c_{N,3}/c_{N,2}\to0\)，则在适当正则条件下仍得到二元 Kingman 极限；若某个亲本可携带 \(O(N)\) 个后代，使高阶碰撞在同一尺度上保留，则极限变成 \(\Lambda\)-或更一般的多重合并共祖过程。保持同一 FIB 上下文和词序，均匀亲本模型可给 Kingman 树，而横扫式繁殖或极端后代数模型可给星形或多重合并树；FIB 结构本身不能在两者之间作出选择。

在 Kingman 树 \(T_k\) 上再外加无限位点突变通道。令每个世代每个拷贝的突变率为 \(\mu_N\)，并取 \(N\mu_N\to\vartheta/2\)。条件于共祖树的边长 \(\ell_e\)（以 \(N\) 代为单位），各边突变数独立服从
\[
M_e\mid T_k\sim\operatorname{Poisson}(\vartheta\ell_e/2).
\tag{103.2}
\]
令 \(\xi_r\) 为恰好在样本中出现 \(r\) 次的衍生等位基因数，则在中性、无限位点、无重组的标准 Kingman 模型下
\[
\mathbb E[\xi_r]=\frac{\vartheta}{r},
\qquad
1\le r<k,
\qquad
\mathbb E[S]=\vartheta H_{k-1},
\tag{103.3}
\]
其中 \(S=\sum_{r=1}^{k-1}\xi_r\)。有限位点回变、选择、重组、群体结构或多重合并树都会改变这一频谱；因此 \(\vartheta\)、频谱形状和单例比例均属于外加突变及系谱模型的结果。

等位基因频率也须另加采样和突变规则。设 \(X_m^{(N)}\in\{0,1/N,\ldots,1\}\) 为第 \(m\) 代某一等位基因频率，正向突变率与反向突变率分别为 \(\mu_N=a/N\)、\(\nu_N=b/N\)，选择系数为 \(s_N=\gamma/N\)。在选择、突变后进行二项抽样时，其成功概率可写成
\[
p_N(x)=x+s_Nx(1-x)+\mu_N(1-x)-\nu_Nx+o(N^{-1}),
\]
并有转移核
\(NX_{m+1}^{(N)}\sim\operatorname{Bin}(N,p_N(X_m^{(N)}))\)。按 \(N\) 代缩放后，若初值收敛，则极限生成元为
\[
(\mathcal L f)(x)
=\frac12x(1-x)f''(x)
+\bigl[a(1-x)-bx+\gamma x(1-x)\bigr]f'(x).
\tag{103.4}
\]
在 \(a,b>0\)、\(\gamma=0\) 时，外加中性突变给出参数为 \((2a,2b)\) 的 Beta 平稳密度；在 \(a=b=0\) 时边界吸收，固定化概率取决于初始频率。选择和突变尺度若不按 \(N^{-1}\) 缩放，所得极限可能是确定性选择流、纯漂变或边界层，而不是 (103.4)。

可辨识性由观测通道决定。若只观测按共祖时间标准化的树和无限位点频谱，则 \(N\) 与 \(\mu_N\) 通常只通过 \(\vartheta=2N\mu_N\) 出现：\((N,\mu_N)=(N_0,\vartheta/(2N_0))\) 与 \((2N_0,\vartheta/(4N_0))\) 具有同一 Kingman 极限和同一式 (103.3)，只有世代钟或有限 \(N\) 碰撞修正才可能区分它们。若 \(q_j\) 合并了不同样本的 FIB 标签，只能观察分割过程的商，隐藏谱系差异无法由重复该商观测恢复。再者，只测二样本多样性可使某些 Kingman 与多重合并模型匹配同一二阶量，而三样本以上的合并概率和整个频谱仍不同。

故 FIB 递归在这里最多提供样本标签、词序和上下文的索引骨架；亲本抽样核、群体大小、世代时钟、突变通道、选择、重组、采样压缩及极限缩放均为外加数据。Wright–Fisher、Kingman、突变频谱与等位基因扩散是这些数据下的条件统计规律，而不是由 FIB ATOM 单独推出的遗传定律。

## 104. FIB 上下文图上的外加 Kuramoto 相位网络、同步阈值与有限尺寸涨落

固定第 \(j\) 层的 FIB 上下文图 \(G_j=(V_j,E_j)\)，令 \(N_j=|V_j|\)。把每个候选状态附加到圆周相位 \(\theta_v(t)\in\mathbb T\)，并另行给定实频率 \(\omega_v\)、非负边权 \(a_{uv}\)、耦合强度 \(K\)、相位滞后 \(\alpha_{uv}\) 和时间单位。一个常用的外加振子模型是
\[
\dot\theta_v
=\omega_v+K\sum_{u:\{u,v\}\in E_j}
a_{uv}\sin(\theta_u-\theta_v-\alpha_{uv}).
\tag{104.1}
\]
也可把求和除以度数或 \(N_j\)；归一化方式必须随模型声明。FIB 递归只提供候选顶点、标签、词序和上下文关系，不提供相位、频率、耦合权重、时钟、初态或相位滞后。

在无相位滞后、无噪声且耦合图为完全图的归一化特例中，定义复序参量
\[
z_j(t)=R_j(t)e^{\mathrm i\psi_j(t)}
=\frac1{N_j}\sum_{v\in V_j}e^{\mathrm i\theta_v(t)},
\qquad 0\le R_j\le1.
\tag{104.2}
\]
若每个顶点以 \(K/N_j\) 耦合到其他顶点，则 (104.1) 化为
\[
\dot\theta_v=\omega_v+KR_j\sin(\psi_j-\theta_v).
\tag{104.3}
\]
\(R_j\) 测量的是相位集中程度，而不是 FIB 标签本身的频率或物理相干性。对无穷体积极限，若外加频率具有偶对称、在零点连续且单峰的密度 \(g\)，旋转坐标中取中心频率为零，锁定振子满足 \(|\omega|\le KR\)。自洽关系为
\[
R=\int_{|\omega|\le KR}
\sqrt{1-\left(\frac{\omega}{KR}\right)^2}\,g(\omega)\,\mathrm d\omega.
\tag{104.4}
\]
在 \(R\downarrow0\) 时，(104.4) 给出
\[
1=\frac{\pi K}{2}g(0)+O(R^2),
\qquad
K_{\mathrm c}=\frac{2}{\pi g(0)}.
\tag{104.5}
\]
因此，在这些明确的连续极限、频率独立采样和归一化假设下，\(K<K_{\mathrm c}\) 的非相干分支可失稳，\(K>K_{\mathrm c}\) 可出现正的平均场序参量。若频率密度不对称，旋转频率需与 (104.4) 联立确定；若密度有多个峰、原子质量或重尾，单一的 (104.5) 可能失效，并可出现多个同步簇或非标准临界行为。\(K_{\mathrm c}\) 是外加频率分布和耦合协议的结论，不是 FIB 递归的结论。

对一般无向加权图，取任意定向关联矩阵 \(B_j\)，令 \(W_j=\operatorname{diag}(a_e)\)，加权图拉普拉斯为
\[
L_j=B_jW_jB_j^{\mathsf T}.
\tag{104.6}
\]
相位锁定解具有 \(\theta_v(t)=\Omega t+\phi_v\) 的形式，并满足
\[
\omega_\perp
=KB_jW_j\sin(B_j^{\mathsf T}\phi),
\qquad
\omega_\perp=\omega-\bar\omega\,\mathbf1,
\tag{104.7}
\]
其中 \(\bar\omega\) 要按每个连通分量的加权平均取值。若图连通、存在 \(0<\gamma<\pi/2\) 使外加谱条件
\[
\bigl\|B_j^{\mathsf T}L_j^\dagger\omega_\perp\bigr\|_\infty
<K\sin\gamma
\tag{104.8}
\]
成立，则在相应的标准单调性和小边差假设下，可由隐式固定点论证得到一个满足
\(\|B_j^{\mathsf T}\phi\|_\infty<\gamma\) 的稳定相位锁定分支；(104.8) 是充分条件而非所有图上的必要条件。它表明频率失配先通过拉普拉斯伪逆沿瓶颈边放大，再由 \(K\) 提供恢复力。若图不连通，\(L_j\) 有多个零模，只能分别讨论各分量的相位锁定，不能由一个全局序参量声称全图同步。

在锁定解附近写 \(\theta=\Omega t\mathbf1+\phi+\eta\)。线性化得到
\[
\dot\eta
=-KB_jW_j\operatorname{diag}
\bigl(\cos(B_j^{\mathsf T}\phi)\bigr)B_j^{\mathsf T}\eta.
\tag{104.9}
\]
全局相位方向 \(\mathbf1\) 是中性零模；若所有边满足
\(|(B_j^{\mathsf T}\phi)_e|\le\gamma<\pi/2\)，则在 \(\mathbf1^\perp\) 上的耗散至少受
\(K\cos\gamma\,\lambda_2(L_j)\) 控制，其中 \(\lambda_2(L_j)\) 是代数连通度。故小的 \(\lambda_2\) 或狭窄割集会使相位差恢复变慢，即使平均场序参量已经较大；谱隙只给出该外加线性化模型的稳定性尺度，不把 FIB 词长自动变成空间尺度。

有限 \(N_j\) 时不存在由 (104.5) 直接给出的锐利相变。若在非相干区初始相位独立且均匀，则
\[
\mathbb E R_j^2
=\frac1{N_j^2}
\mathbb E\left|\sum_{v=1}^{N_j}e^{\mathrm i\theta_v}\right|^2
=\frac1{N_j},
\qquad
R_j=O_P(N_j^{-1/2}).
\tag{104.10}
\]
故有限图上即使没有同步，\(R_j\) 也有不可消除的随机背景。若同步分支对初值和频率抽样具有足够混合性，并且极限序参量为 \(r>0\)，则常见的中心极限定标为 \(R_j-r=O_P(N_j^{-1/2})\)；临界窗口内的涨落通常更大，具体有限尺寸指数取决于频率样本、图谱密度、耦合归一化和观测方式。FIB 层数、词长或候选数只有在另加图列和采样规则后才可充当 \(N_j\)，不能单独推出有限尺寸标度。

若加入独立相位噪声，模型变为
\[
\mathrm d\theta_v
=\left[\omega_v+K\sum_u a_{uv}
\sin(\theta_u-\theta_v)\right]\mathrm dt
+\sqrt{2D}\,\mathrm dW_v(t).
\tag{104.11}
\]
相位锁定变成平稳概率集中，临界点由外加 Fokker–Planck 线性化算子决定。作为明确的归一化例子，在完全图、洛伦兹频率密度宽度为 \(\Delta\) 且相位扩散系数为 \(D\) 时，线性稳定分析给出 \(K_{\mathrm c}=2(\Delta+D)\)；换用一般频率密度、相关噪声或非完全图后，该公式不保持。相位滞后 \(\alpha\ne0\) 还使对称图上的流形通常不再是梯度系统，可产生旋转波、反相簇或多簇态；这些现象需要相位滞后、图模体和初态等外加条件，不能从 FIB 词序推断。

同一 FIB 上下文载体可置于相反的外加协议中：取 \(K=0\) 得到独立漂移和 \(R_j\) 的有限尺寸背景；取相同频率、连通正权图和足够大的 \(K\) 得到相位锁定；取双峰频率、弱瓶颈或非零相位滞后可得到局部同步、反相簇或持续漂移。改变频率—度数相关性还会使高连接顶点先同步，导致局部序参量与全图序参量不一致。因此，FIB 递归最多提供可承载相互作用的组合骨架；图拉普拉斯、耦合常数、频率分布、相位噪声、相位滞后、时钟、初态和极限方式均为外加。同步阈值、谱稳定性、序参量涨落和相变类只在声明这些模型条件后成立，不能被表述为 FIB 本身推出的真实物理定律。

## 105. FIB 胞腔载体上的外加离散微分形式、Maxwell–Hodge 方程与规范模态

固定第 \(j\) 层 FIB 上下文图的顶点和边，并额外选择有向胞腔、附着映射与取向，把它提升为有限胞腔复形 \(K_j\)。记
\[
C_j^k=\mathbb R^{K_j^{(k)}},
\qquad
D_{k,j}:C_j^k\to C_j^{k+1}
\]
为 \(k\)-胞腔上的实系数上链空间及其上链边界矩阵。胞腔的附着关系必须满足
\[
D_{k+1,j}D_{k,j}=0.
\tag{105.1}
\]
这一步需要外加的胞腔、取向和边界数据；FIB 词序或递归标签本身既不产生高维胞腔，也不保证给定图能按唯一方式填充。再给每个 \(C_j^k\) 一个对称正定的质量矩阵（离散 Hodge 星）\(M_{k,j}\)，定义
\[
\delta_{k,j}
=M_{k-1,j}^{-1}D_{k-1,j}^{\mathsf T}M_{k,j},
\qquad
\Delta_{k,j}
=\delta_{k+1,j}D_{k,j}+D_{k-1,j}\delta_{k,j}.
\tag{105.2}
\]
这里的长度、面积、体积、介电率、磁导率和单位全部由 \(M_{k,j}\) 或其他外加参数指定。有限维加权 Hodge 分解给出
\[
C_j^1
=\operatorname{im}D_{0,j}
\mathbin{\perp_{M_{1,j}}}
\operatorname{im}\delta_{2,j}
\mathbin{\perp_{M_{1,j}}}
\ker\Delta_{1,j}.
\tag{105.3}
\]
第一项是纯规范方向，第二项是横向（共恰）方向，最后一项是调和零模。式 (105.3) 需要 \(M_{1,j}\)，所以调和代表的具体形状不由上同调群单独决定。

给定外加介电矩阵 \(M_{1,j}^{\varepsilon}\succ0\)、磁能矩阵 \(M_{2,j}^{\mu^{-1}}\succ0\)，令 \(A(t)\in C_j^1\) 为势、\(\phi(t)\in C_j^0\) 为标势，并按一个固定的源项符号约定设
\[
\mathsf E=\partial_tA+D_{0,j}\phi,
\qquad
B=D_{1,j}A,
\]
其中物理电场可取为 \(-\mathsf E\)。对外加电荷 \(\rho(t)\in C_j^0\) 和电流 \(J(t)\in C_j^1\)，作用量取为
\[
\mathcal S=\int\!\left[
\frac12\langle\mathsf E,M_{1,j}^{\varepsilon}\mathsf E\rangle
-\frac12\langle B,M_{2,j}^{\mu^{-1}}B\rangle
+\langle A,J\rangle-\langle\phi,\rho\rangle
\right]\mathrm dt.
\tag{105.4}
\]
其 Euler–Lagrange 方程可写成
\[
\begin{aligned}
D_{1,j}\mathsf E&=\partial_tB,
&
D_{2,j}B&=0,\\
D_{0,j}^{\mathsf T}M_{1,j}^{\varepsilon}\mathsf E&=\rho,
&
\partial_t(M_{1,j}^{\varepsilon}\mathsf E)
+D_{1,j}^{\mathsf T}M_{2,j}^{\mu^{-1}}B&=J.
\end{aligned}
\tag{105.5}
\]
第一行是两个 Bianchi 恒等式，直接使用
\(D_{1,j}D_{0,j}=0\) 和 \(D_{2,j}D_{1,j}=0\)；第二行是由作用量选定的离散 Gauss–Ampère 方程。对最后一式施加 \(D_{0,j}^{\mathsf T}\) 并使用 (105.1)，得到
\[
\partial_t\rho=D_{0,j}^{\mathsf T}J.
\tag{105.6}
\]
即若把离散散度定义为
\(\operatorname{div}J=-D_{0,j}^{\mathsf T}J\)，则为
\(\partial_t\rho+\operatorname{div}J=0\)。改变取向或源项号只会改变这个约定，不改变守恒内容。

对任意 \(\lambda(t)\in C_j^0\) 作
\[
A\longmapsto A+D_{0,j}\lambda,
\qquad
\phi\longmapsto\phi-\partial_t\lambda.
\tag{105.7}
\]
则 \(\mathsf E\) 和 \(B\) 不变，因为 \(D_{1,j}D_{0,j}=0\)。源耦合在无边界通量或相容边界下的变化量由 (105.6) 消去；这说明规范不变性要求源满足连续性方程。规范轨道上的 \(A\) 代表同一电磁状态，因而不能把 \(A\) 的每个坐标自由度当作可观测模态。

在无源、时间规范 \(\phi=0\) 并取横向约束
\(D_{0,j}^{\mathsf T}M_{1,j}^{\varepsilon}A=0\) 时，方程退化为
\[
M_{1,j}^{\varepsilon}\partial_t^2A
+D_{1,j}^{\mathsf T}M_{2,j}^{\mu^{-1}}D_{1,j}A=0.
\tag{105.8}
\]
其横向模态由广义特征值问题
\[
D_{1,j}^{\mathsf T}M_{2,j}^{\mu^{-1}}D_{1,j}u_n
=\omega_{n,j}^2M_{1,j}^{\varepsilon}u_n
\tag{105.9}
\]
给出。 \(\operatorname{im}D_{0,j}\) 上的纯规范模态应先商掉；
\(\ker\Delta_{1,j}\) 上的调和模态在无耗散模型中具有零频率，可表示全局通量或环路自由度。边界条件决定哪些模态存在，介电率和磁导率决定频率尺度，源的空间投影决定哪些模态被激发。若外加阻尼项 \(\Gamma_j\partial_tA\) 或开边界辐射条件，则 (105.9) 的实频率变为带宽有限的共振；传播速度、阻抗和能量单位均由这些外加系数决定。

若 \(K_j\)、\(M_{1,j}^{\varepsilon}\)、\(M_{2,j}^{\mu^{-1}}\) 或源是随机的，可定义横向谱经验测度
\[
\nu_j=\frac1{\dim C_j^1}\sum_n\delta_{\omega_{n,j}^2}.
\tag{105.10}
\]
在随机复形具有统一度数、正定性、边界控制和局部弱收敛等外加条件时，\(\nu_j\) 可能收敛到积分密度状态；不同的权重分布、胞腔几何和边界会给出不同的极限。若在阻尼线性系统上施加协方差为 \(Q_j(\omega)\) 的随机源，频域响应的协方差为
\[
\mathbb E[\widehat A(\omega)\widehat A(\omega)^*]
=G_j(\omega)Q_j(\omega)G_j(\omega)^*,
\]
\[
G_j(\omega)=
\left[
D_{1,j}^{\mathsf T}M_{2,j}^{\mu^{-1}}D_{1,j}
-\omega^2M_{1,j}^{\varepsilon}
-\mathrm i\omega\Gamma_j
\right]^\dagger.
\tag{105.11}
\]
其中伪逆只在固定规范和去除零模后使用。若再外加热浴与耗散的涨落—耗散关系，(105.11) 可产生热噪声谱、共振峰和有限尺寸涨落；没有这些关系时，随机源并不自动代表热平衡。

本节的 Maxwell–Hodge 模型与第 91 节的拓扑缺陷结论有明确分工：第 91 节讨论上链的闭性、余边界和缺陷电荷，本节讨论在给定 Hodge 星、介质和时间动力学后，势、电场、磁通及其守恒方程；调和零模可受拓扑影响，却不等于局部缺陷。它也不同于第 92 节的词序转移矩阵：第 92 节沿一维词序相乘传输矩阵并研究 Lyapunov 指数与散射，本节使用不同次数胞腔的 incidence 矩阵和加权 Hodge 拉普拉斯，不要求一维顺序。相同 FIB 载体可分别承载两种外加模型，二者的谱和传播结论不能互相替代。

FIB 递归本身只提供状态、标签、词序和上下文关系；胞腔附着、取向、Hodge 星、介电率、磁导率、源、时间、边界、阻尼、随机律、物理单位和连续极限都必须外加。因此，(105.5)–(105.11) 所得到的规范约束、波模态、谱密度和统计响应，是声明了这些外加条件后的 Maxwell–Hodge 模型结论，而不是 FIB 递归单独推出的真实电磁定律。改变同一 FIB 载体上的胞腔填充、介质权重或源边界，即可得到不同的零模、传播速度、共振谱乃至无传播的退化系统；不存在由 FIB 基础递归唯一确定的普适 Maxwell 参数或物理统计律。

## 106. FIB 符号序列上的外加哈密顿辛动力学、KAM 与混沌边界

固定 FIB 递归产生的上下文序列 \(c_0,c_1,\ldots\)，并另给外加辛相空间 \((\mathcal M,\omega)\)。对每个上下文 \(c\) 选择一个哈密顿流或保辛离散映射 \(\Phi_c\)，例如由
\[
H_c(z)=H_0(z)+\varepsilon V_c(z)
\]
生成的周期踢映射。词序只决定复合顺序
\[
\Phi^{(n)}
=\Phi_{c_{n-1}}\circ\cdots\circ\Phi_{c_0};
\tag{106.1}
\]
辛形式、哈密顿量、扰动幅度、初态和时间单位均为外加。若每个 \(\Phi_c\) 保辛，则相空间体积在复合下保持；这一个几何事实不等于存在唯一的平稳概率律或热力学系综。

若 \(H_0\) 可积、频率向量满足 Diophantine 条件且
\(\varepsilon\|V_c\|\) 足够小并具有所需的光滑性，则 KAM 型结果可保留一族不变环面，轨道在这些环面上准周期运动。若上下文驱动含共振、扰动不小或映射在某区域一致双曲，则可出现正 Lyapunov 指数、稳定流形和混沌不变测度。对应的 Lyapunov 率
\[
\lambda(z)
=\limsup_{n\to\infty}\frac1n
\log\|D\Phi^{(n)}(z)\|
\tag{106.2}
\]
依赖 \(\omega,H_0,V_c\) 和 FIB 词序的共同实现；FIB 递归本身不决定其符号或数值。

若另有一个对复合映射不变的概率测度 \(\mu\)，并且系统对 \(\mu\) 遍历，则对可积观测量 \(A\) 有
\[
\frac1n\sum_{k=0}^{n-1}A(\Phi^{(k)}z)
\longrightarrow\int A\,\mathrm d\mu
\quad\text{对 }\mu\text{-几乎处处的 }z.
\tag{106.3}
\]
若再给出混合率和方差可和条件，中心化时间平均可能满足中心极限定理；若只知道保辛性而没有遍历或混合，(106.3) 不能从几何结构推出。时间依赖的上下文序列还可能使能量 \(H_{c_n}\) 改变，因而“能量守恒”需另加时间齐次条件或扩展相空间。

同一 FIB 词序可以承载相反动力学。取所有 \(\Phi_c\) 为同一个无扰动旋转，得到 \(\lambda=0\) 和准周期轨道；取某个上下文对应猫映射或一致双曲的保辛映射，则得到正 Lyapunov 率与指数轨道分离；加入外加随机踢又可产生扩散、熵增或随机不变测度。即使每种模型共享相同的符号序列和组合计数，其相空间几何、初态分布、可逆性和长期统计也可以完全不同。

把 FIB 标签解释为力学自由度还需给出位置、动量、质量、势能、外力和观测单位。KAM 环面、遍历平均、混沌熵率和 Lyapunov 指数因此都是声明外加辛模型后的条件结论；FIB 递归只提供时间驱动的组合顺序，不能单独推出真实哈密顿方程、能量守恒、混沌普适类或物理相空间。

## 107. FIB 图上的外加相分离、Cahn–Hilliard 梯度流与粗化

固定一个外加嵌入的 FIB 上下文图 \(G_j=(V_j,E_j)\)，在顶点放置守恒密度 \(\rho_v\in[\rho_-,\rho_+]\)。给定局部自由能 \(f\)、边权 \(w_{uv}\)、梯度系数 \(\kappa_j\) 和外加迁移率 \(M_j(\rho)\)，定义离散自由能
\[
\mathcal F_j(\rho)
=\sum_{v\in V_j}f(\rho_v)
+\frac{\kappa_j}{2}\sum_{\{u,v\}\in E_j}
w_{uv}(\rho_u-\rho_v)^2.
\tag{107.1}
\]
化学势为
\[
\mu_v=f'(\rho_v)
-\kappa_j\sum_{u:\{u,v\}\in E_j}
w_{uv}(\rho_u-\rho_v),
\tag{107.2}
\]
并以守恒梯度流
\[
\dot\rho
=\operatorname{div}_j\!\left(
M_j(\rho)\nabla_j\mu
\right)
\tag{107.3}
\]
定义外加相分离动力学。若边界通量为零，则
\[
\frac{\mathrm d}{\mathrm dt}\mathcal F_j(\rho_t)
=-\sum_{e\in E_j}
M_{j,e}(\rho_t)\,|\nabla_{j,e}\mu_t|^2
\le0,
\qquad
\sum_{v\in V_j}\rho_v(t)=\text{常数}.
\tag{107.4}
\]
守恒律和能量耗散来自所选梯度流结构，不来自 FIB 词序。

若 \(f\) 在相关密度区间严格凸，均匀态具有局部稳定性，通常不会产生自发宏观相分离；若 \(f\) 是双阱势并且平均密度落在两阱之间，均匀态可失稳，系统趋向高、低密度区域共存。对一列图给出共同空间嵌入、网格尺度和离散算子收敛，并令 \(\kappa_j\) 与 \(M_j\) 具有统一极限时，(107.3) 可能收敛到
\[
\partial_t\rho
=\nabla\!\cdot\!\left[
M(\rho)\nabla\bigl(f'(\rho)-\kappa\Delta\rho\bigr)
\right].
\tag{107.5}
\]
这是一种外加 Cahn–Hilliard 型极限；边界条件、质量归一化和空间维数必须同时声明。若加入与迁移率相容的守恒噪声，可得到随机 Cahn–Hilliard 模型；其平稳 Gibbs 律和结构因子需要额外的详细平衡与噪声—耗散关系。

线性化 (107.3) 于均匀密度 \(\rho_0\) 后，若图拉普拉斯本征值为 \(\lambda_\ell\)，模态增长率具有
\[
r_\ell
=-M(\rho_0)\lambda_\ell
\bigl(f''(\rho_0)+\kappa_j\lambda_\ell\bigr)
\tag{107.6}
\]
的形式。只有当 \(f''(\rho_0)<0\) 且某些外加谱模态落入
\(0<\lambda_\ell<-f''(\rho_0)/\kappa_j\) 时，才会出现自旋odal 失稳；增长最快的波数、界面宽度和粗化尺度由图谱、\(\kappa_j\)、迁移率及嵌入决定。若 \(f''(\rho_0)\ge0\)，同一 FIB 图在相同边界下可保持线性稳定。

在连续外加模型满足界面能量、迁移率和初态正则性时，扩散控制的粗化长度常呈
\(L(t)\asymp t^{1/3}\) 的候选标度；流体输运、长程相互作用、受限几何或守恒噪声会改变该指数。有限图上的单一大团、多个团簇和亚稳态寿命还依赖初态与边界，不能由 FIB 词长直接判定。

因此，FIB 上下文图可以承载守恒相场、相分离、界面涨落和粗化统计，但局部自由能、边权、迁移率、噪声、空间尺度、边界和物理单位均为外加。相分离阈值、失稳模态、Cahn–Hilliard 极限和粗化指数是指定这些模型后的条件结论；改变同一 FIB 递归上的 \(f\)、\(M\)、\(\kappa\) 或边界即可从均匀稳定态切换到相共存或完全不同的粗化律。

## 108. FIB 上下文图上的外加 Abelian 沙堆、自组织临界性与雪崩标度

固定由有限个 FIB ATOM 及其上下文关系得到的有限图族 \(G_j=(V_j,E_j)\)，另取一个汇点 \(\partial_j\)。FIB 只提供顶点、边、标签和词序；在此图上外加整数拓扑矩阵 \(\Delta_j\)。约定 \(\Delta_{j,vv}>0\)、\(\Delta_{j,uv}\le0\)（\(u\ne v\)），且 \(\Delta_j\) 是可逆的非奇异 \(M\)-矩阵，\(\Delta_j^{-1}\ge0\)。顶点 \(v\) 的稳定阈值取为 \(\Delta_{j,vv}\)；若 \(\eta_v\ge\Delta_{j,vv}\)，一次 \(v\)-拓扑把配置改为
\[
\eta\longmapsto\eta-\Delta_je_v.
\tag{108.1}
\]
列和 \(\delta_{j,v}:=(\mathbf1^{\mathsf T}\Delta_j)_v\ge0\) 表示一次 \(v\)-拓扑向汇点的净耗散。 \(\delta_{j,v}=0\) 的顶点是体内守恒位置，正列和集中在边界时得到边界耗散沙堆。

在 \(\Delta_j\) 为雪崩有限矩阵，即每个有限配置的所有合法拓扑都终止时，Abelian 性给出：任取同一初始配置和同一加沙向量，任何合法拓扑顺序的终态相同，且各顶点的拓扑次数向量 \(u_j\) 相同。因此稳定化算子 \(\operatorname{stab}_j\) 与加沙算子
\[
a_{j,v}(\eta)=\operatorname{stab}_j(\eta+e_v)
\tag{108.2}
\]
满足 \(a_{j,u}a_{j,v}=a_{j,v}a_{j,u}\)。这项交换性是由外加拓扑矩阵和终止性保证的组合性质；FIB 递归本身不规定阈值、边权或拓扑方向。

令每次雪崩完成后才加入一粒沙，加入点 \(A_n\) 按外加分布 \(p_j\) 抽样，得到有限状态链
\[
\eta_{n+1}=a_{j,A_n}(\eta_n).
\tag{108.3}
\]
在标准无向约化拉普拉斯情形、每个顶点均以正概率被驱动时，递归类上的平稳分布是所有 recurrent 配置的均匀分布；一般有向或非对称 \(M\)-矩阵的平稳权重由外加算子和汇点结构决定，不能从 FIB 图的顶点计数推出均匀律。若没有汇点或任何耗散列，即 \(\delta_{j,v}=0\) 对所有 \(v\)，则单粒度持续注入不能与有限平稳平均相容，稳定化也可能失败，因而不能直接宣称存在自组织临界态。

设 \(u_n(v)\) 是第 \(n\) 次加沙后的 odometer，单粒加沙满足精确守恒账式
\[
\eta_{n+1}=\eta_n+e_{A_n}-\Delta_ju_n,
\qquad
M_{n+1}-M_n
=1-\sum_{v\in V_j}\delta_{j,v}u_n(v),
\tag{108.4}
\]
其中 \(M_n=\mathbf1^{\mathsf T}\eta_n\)。在平稳分布下取期望得到
\[
\mathbb E\!\left[\sum_v\delta_{j,v}u_n(v)\right]=1.
\tag{108.5}
\]
这说明平均输入等于平均边界耗散；单次雪崩耗散不必等于一，因为它还可释放初始配置中储存的沙。若采用标准无向 recurrent 律，Green 矩阵还给出条件均值
\[
\mathbb E[u_n\mid A_n=v]=\Delta_j^{-1}e_v,
\qquad
\mathbb E[S_j]=\mathbf1^{\mathsf T}\Delta_j^{-1}p_j,
\tag{108.6}
\]
其中 \(S_j=\sum_vu_n(v)\) 是总拓扑次数。故平均雪崩规模由外加 Green 函数、谱隙和驱动分布决定；FIB 词序只决定矩阵可采用的组合索引。

对每次雪崩定义
\[
S_j=\sum_vu_n(v),
\quad
A_j=\#\{v:u_n(v)>0\},
\quad
T_j=\text{并行拓扑波数},
\quad
R_j=\max\{d_j(v,A_n):u_n(v)>0\}.
\tag{108.7}
\]
其中 \(d_j\) 是另加的图距离。若取一族尺度为 \(L\) 的上下文图，并假定只在边界耗散、慢驱动和统计稳态下考察，常用有限尺寸标度假设为
\[
\Pr_L(S=s)\simeq s^{-\tau_S}\,
\mathcal F_S\!\left(\frac{s}{s_c(L)}\right),
\qquad
s_c(L)\asymp L^{D_S},
\tag{108.8}
\]
以及
\[
\Pr_L(T=t)\simeq t^{-\tau_T}\,
\mathcal F_T\!\left(\frac{t}{L^z}\right),
\qquad
\Pr_L(R=r)\simeq r^{-\tau_R}\,
\mathcal F_R\!\left(\frac{r}{L}\right).
\tag{108.9}
\]
若 \(q+1>\tau_S\) 且标度函数具有有限相应矩，则
\[
\mathbb E_L[S^q]\asymp
L^{D_S(q+1-\tau_S)}
\tag{108.10}
\]
只在幂律区间和截止尺度假设成立时有效。没有共同的空间嵌入时，\(L\) 应替换为图直径、有效体积或由谱维、有效电阻和 Green 函数定义的尺度；直接把 FIB 词长当作物理长度会改变量纲并可能制造假幂律。

(108.8)–(108.10) 不是 FIB 递归的定理。指数和截止可随图的谱维、边界比例、驱动位置、\(\Delta_j\) 的各向异性、体内耗散、并行更新规则、随机边权及有向性改变。特别地，若加入每次拓扑均有固定体耗散 \(\delta_{j,v}\ge\varepsilon>0\)，Green 函数被截断，雪崩尾可为指数型；若撤去汇点而保持守恒注入，过程可能不终止；若将多粒沙在一次稳定化前同时加入，时间尺度分离消失，所得分布也不必具有 (108.8) 的指数。即使固定同一 FIB 上下文图，改变 \(\Delta_j\)、\(p_j\)、耗散边界或更新时钟，也能分别得到亚临界、临界候选或无稳定平稳态。

在随机 FIB 图族中还须区分先固定图再取雪崩平均的 quenched 律与先对图平均再取动力学平均的 annealed 律；两者的 Green 函数、截止和指数可能不同。若图族含长程上下文边或重尾度分布，局部拓扑仍可 Abelian，但有限尺寸幂律可能由拓扑异质性、混合多个截止或有限样本效应造成，不能仅凭直线拟合宣称普适临界指数。

因此，FIB 上下文图能够承载守恒加沙、边界耗散、Abelian 稳定化和自组织临界候选机制，并在明确的外加矩阵、驱动、时间尺度、距离和图族极限下产生雪崩大小、持续时间、面积及耗散的统计律。FIB 递归只固定组合载体和可用关系；守恒量、拓扑阈值、汇点、随机驱动、幂律指数、临界性及其物理单位均为外加。相同 FIB 载体可在不同外加模型下产生指数尾、幂律尾或不终止行为，故不能把任何一个 Abelian 沙堆指数或自组织临界律归因于 FIB ATOM 本身。

## 109. FIB 图上的外加趋化主动粒子、离散 Keller–Segel 临界性与观测不可识别

固定一个由 FIB 上下文关系给出的有限图 \(G_j=(V_j,E_j)\)，取定向关联矩阵 \(B_j:C^0(V_j)\to C^1(E_j)\)，令 \(L_j=B_j^{\mathsf T}W_jB_j\) 为带边权的非负图拉普拉斯。FIB 只提供顶点、边、标签和词序；顶点质量、边长、体积、方向、扩散常数与观测量都另行外加。令 \(\rho_v(t)\ge0\) 表示粒子密度，\(c_v(t)\) 表示趋化信号，在边上取平均密度 \(\bar\rho_e\)，外加扩散系数 \(D_e>0\) 与敏感度 \(\chi_e\ge0\)。一个保持质量的离散趋化通量可写为
\[
J_e=-D_e(B_j\rho)_e+\chi_e\bar\rho_e(B_jc)_e,
\qquad
\dot\rho=B_j^{\mathsf T}J,
\tag{109.1}
\]
并配以反应—扩散信号方程
\[
\tau_j\dot c=-D_{c,j}L_jc-\alpha_jc+\beta_j\rho.
\tag{109.2}
\]
这里采用 \(\operatorname{div}J=-B_j^{\mathsf T}J\) 的符号约定；无通量边界时
\(\mathbf1^{\mathsf T}B_j^{\mathsf T}=0\)，所以
\(M_j=\sum_{v\in V_j}\rho_v(t)\) 保持不变。若使用中心通量，需另加步长、时间步和离散最大值条件才能保持 \(\rho\ge0\)；上风或马尔可夫跳跃通量可直接保证非负性。质量守恒、正性和信号衰减均来自这些外加离散动力学，而非 FIB 递归。

在快信号极限 \(\tau_j\to0\) 且
\(K_j=(D_{c,j}L_j+\alpha_jI)^{-1}\) 存在时，
\(c=\beta_jK_j\rho\)，趋化漂移由图上的非局部核 \(K_j\) 决定。若 mobility 选为与对数熵相容的边通量，形式自由能可写成
\[
\mathcal F_j(\rho)
=D_j\sum_v\rho_v(\log\rho_v-1)
-\frac{\chi_j\beta_j}{2}\langle\rho,K_j\rho\rangle,
\tag{109.3}
\]
其第一变分为
\(D_j\log\rho-\chi_j\beta_jK_j\rho\)。该表达式显示趋化是熵扩散与信号吸引项之间的竞争；在有限 \(V_j\) 上固定总质量时，所有坐标有界，故不会出现连续 PDE 意义的有限时间密度无穷大。把图列细化并让局部质量集中，是否出现“爆聚”则取决于图的体积缩放、核的奇异性和时间尺度，不能由有限图的 FIB 结构单独决定。

对均匀态 \(\rho_0\)（当 \(\alpha_j>0\) 时
\(c_0=\beta_j\rho_0/\alpha_j\)）作线性化。若
\(L_j\varphi_\ell=\lambda_\ell\varphi_\ell\)，\(\lambda_\ell>0\)，则模态满足
\[
\dot r_\ell=-D_j\lambda_\ell r_\ell
+\chi_j\rho_0\lambda_\ell q_\ell,
\qquad
\tau_j\dot q_\ell
=-(D_{c,j}\lambda_\ell+\alpha_j)q_\ell+\beta_jr_\ell,
\tag{109.4}
\]
其特征方程为
\[
(s+D_j\lambda_\ell)
(\tau_js+D_{c,j}\lambda_\ell+\alpha_j)
-\chi_j\beta_j\rho_0\lambda_\ell=0.
\tag{109.5}
\]
因此在此线性系统中，某个模态失稳的条件为
\[
\chi_j\beta_j\rho_0
>D_j(D_{c,j}\lambda_\ell+\alpha_j)
\tag{109.6}
\]
对某个 \(\lambda_\ell>0\) 成立。有限图的首个线性阈值取决于最小非零谱、边权和顶点体积；它只是均匀态的线性起始点，不等同于非线性聚集的普适临界质量。改变同一 FIB 图的 \(W_j,D_j,D_{c,j},\alpha_j,\beta_j\) 或 \(\chi_j\) 可使所有模态稳定，也可使某一低频模态先增长。

在外加欧氏嵌入的二维细化图上，若 \(L_j\)、顶点体积和核归一化收敛到连续拉普拉斯，并取无衰减的快速信号方程
\[
-D_c\Delta c=\beta\rho,
\]
则形式极限为
\[
\partial_t\rho
=D\Delta\rho-\chi\nabla\!\cdot(\rho\nabla c),
\qquad
-D_c\Delta c=\beta\rho.
\tag{109.7}
\]
在二维全平面、牛顿核归一化为 \(-\Delta^{-1}\)、无边界通量并满足所需正则性时，经典 Keller–Segel 结论给出归一化临界质量
\[
M_c=\frac{8\pi DD_c}{\chi\beta}.
\tag{109.8}
\]
若把 \(D_c\) 或 \(\beta\) 吸收到信号定义中，则相应常数写法改变。\(M<M_c\)、\(M=M_c\) 与 \(M>M_c\) 的长期行为和爆聚判据还依赖初态、边界、核归一化及解概念；有屏蔽 \(\alpha>0\)、有界域、离散截止或非局部核时，(109.8) 不可直接套用。

趋化方程也可由外加主动粒子模型得到。令 \(p_{v,a}(t)\) 是顶点 \(v\) 上方向或内部状态 \(a\) 的粒子数，\(u_a\) 是外加方向向量，沿 FIB 边按跳跃核 \(T_j\) 运动，并令转向率依赖 \(B_jc\)。在快速转向、弱持久性和扩散缩放下，一阶矩消去可给出
\[
J\simeq-D_{\mathrm{eff}}\nabla_j\rho
+\chi_{\mathrm{eff}}\rho\nabla_jc,
\tag{109.9}
\]
从而得到 (109.1)。\(D_{\mathrm{eff}}\)、\(\chi_{\mathrm{eff}}\) 由速度、转向核、持久时间和化学感受函数决定；若转向不够快，极限保留惯性或记忆项，可能是超扩散、趋化波或各向异性张量，而非 Keller–Segel。FIB 图仅规定允许的跳跃和组合路径，不规定粒子是否有真实位置、速度或化学感受器。

观测不可识别是上述模型的结构性边界。设只能观测聚合量 \(y(t)=Q_j\rho(t)\)，其中 \(Q_j\) 是由标签或上下文选择的线性读出。若 \(Q_j\) 湮灭某个拉普拉斯模态，沿该模态的质量重新分配完全不可见；尤其 \(Q_j=\mathbf1^{\mathsf T}\) 时，\(y(t)=M_j\) 对所有无通量模型恒定，不能区分扩散、聚集或爆聚前的局部重排。即使观测完整 \(\rho\)，信号缩放
\[
c'=ac,\qquad
\beta'=a\beta,\qquad
\chi'=\chi/a
\tag{109.10}
\]
在相应初值和信号方程下保持
\(\chi'\nabla c'=\chi\nabla c\)，所以单凭 \(\rho\) 轨迹不能分别识别 \(\chi,\beta\)。

本节与第 107 节的 Cahn–Hilliard 模型分工不同：Cahn–Hilliard 直接对守恒场作四阶局部梯度流，化学势含外加自由能和梯度能；(109.1)–(109.2) 是二阶守恒输运加独立信号场，吸引作用经 \(K_j\) 形成非局部核，连续二维极限可有 Keller–Segel 型聚集。它也不同于第 99 节接触过程：接触过程使用离散感染、恢复和吸收态，趋化模型使用可分割质量、连续信号及守恒总量，没有由 \(\rho=0\) 自动形成的感染吸收态。相同 FIB 图可分别承载这些外加模型，因而其阈值、波速和长期统计不能互相推出。

总之，FIB 递归提供趋化模型的图结构、标签和组合路径；粒子质量、嵌入度量、扩散与转向、信号核、边界、噪声、临界缩放和观测通道均必须外加。离散聚集阈值、二维临界质量、主动粒子扩散极限及观测不可识别，都是明确外加条件下的 Keller–Segel 或主动输运结论，而不是 FIB ATOM 递归单独推出的普适物理定律。

## 110. FIB 上下文图上的外加离散与连续时间量子行走、谱隙和局域化

固定一个 FIB 上下文图 \(G_j=(V_j,E_j)\)，在每个顶点附加有限维内部空间 \(\mathbb C^{d_j}\)，量子态属于
\[
\mathcal H_j=\ell^2(V_j)\otimes\mathbb C^{d_j}.
\]
FIB 只给出顶点、边、标签和词序；内部自由度、边上的相位、跃迁振幅、哈密顿量、初态和测量均为外加。离散时间量子行走可写成
\[
\psi_{n+1}=U_j\psi_n,
\qquad
U_j=S_jC_j,
\qquad
U_j^*U_j=I,
\tag{110.1}
\]
其中 \(C_j\) 是顶点内部空间上的酉 coin，\(S_j\) 按有向边搬运振幅。连续时间量子行走则由自伴算子
\[
H_j=\gamma_jL_j+V_j,
\qquad
\psi(t)=e^{-\mathrm i tH_j}\psi(0),
\tag{110.2}
\]
给出；\(L_j\) 可以是外加加权图拉普拉斯，\(V_j\) 是外加势或无序项，\(\gamma_j\) 设定时间尺度。两种行走的谱和传播规律不能仅由同一个组合图确定。

设在顶点 \(v\) 上作末时刻位置测量，投影记为 \(\Pi_v\)。则
\[
p_v(n)=\langle\psi_n,\Pi_v\psi_n\rangle,
\qquad
p_v(t)=\langle\psi(t),\Pi_v\psi(t)\rangle.
\tag{110.3}
\]
有限图上的酉演化一般不会在末时刻概率上收敛。若 \(H_j=\sum_r E_rP_r\)，Cesàro 平均满足
\[
\overline p_v
=\lim_{T\to\infty}\frac1T\int_0^T p_v(t)\,\mathrm dt
=\sum_{E_r=E_s}
\langle\psi_0,P_r\Pi_vP_s\psi_0\rangle,
\tag{110.4}
\]
其中求和只保留相同能量的谱块；非简并谱时只剩各谱投影的对角项。离散时间把能量替换为酉本征值的相位，只有相位差为 \(2\pi\) 的谱块在 Cesàro 平均中保留。因而谱简并、初态和测量投影都会改变长期平均，即使图 \(G_j\) 不变。

在给定图距离 \(d_j\) 和起点 \(v_0\) 后，可定义二阶传播矩
\[
\sigma_j^2(t)
=\sum_{v\in V_j}d_j(v,v_0)^2p_v(t).
\tag{110.5}
\]
对具有平滑色散关系和相干初态的外加图列，若群速度在所考察频带内非零且无强散射，可能有 \(\sigma_j^2(t)\asymp t^2\) 的弹道传播；加入快速退相干、随机相位或马尔可夫跳跃后，在扩散缩放下可能得到 \(\sigma_j^2(t)\asymp t\)。若无序哈密顿量存在指数局域本征函数，初态的传播矩可在 \(t\) 增长时保持有界，形成动力学局域化候选。这里的三种标度分别依赖群速度、退相干核、无序和图列的极限，不能从 FIB 词长或顶点数直接推出。

连续时间行走的谱隙
\[
\Delta_j=\min\{|E_r-E_s|:E_r\ne E_s\}
\tag{110.6}
\]
控制相位去相干所需的时间尺度，离散时间则由本征相位间距控制。谱隙本身不会使封闭酉系统产生经典平稳收敛；只有加入时间平均、测量、退相干或开放边界后，才可把 \(\Delta_j^{-1}\) 与混合或弛豫时间联系起来。若外加通道给出 Lindblad 演化
\[
\dot\rho
=-\mathrm i[H_j,\rho]
+\sum_a\left(L_{j,a}\rho L_{j,a}^*
-\frac12\{L_{j,a}^*L_{j,a},\rho\}\right),
\tag{110.7}
\]
则真正控制趋近平稳态的是 Liouvillian 的谱隙；它与 \(H_j\) 的能谱隙一般不同。相同 FIB 图上的封闭行走和开放行走因此可有完全不同的扩散与混合律。

局域化须在一族图 \(G_j\) 和极限尺度中声明。例如若存在常数 \(C,\xi>0\)，使外加本征投影核满足
\[
\mathbb E\!\left[\sup_t
\bigl|\langle\delta_v,e^{-\mathrm i tH_j}\delta_w\rangle\bigr|
\right]
\le C\exp\!\left(-\frac{d_j(v,w)}\xi\right),
\tag{110.8}
\]
则可得到一致的动态局域化界；单个有限图上振幅有界只说明有限维准周期性，不能替代热力学极限中的局域化。相反，若图列的谱测度具有绝对连续部分并且退相干尺度随 \(j\) 适当缩放，则可出现弹道到扩散的交叉。交叉时间和有效扩散系数由无序强度、边权、维数及外加噪声决定。

量子测量还引入不可逆的观测协议差异。末时刻一次测量使用 (110.3) 的 \(\Pi_v\)；每一步都测量位置则把演化替换为测量后的量子操作，频繁测量在适当极限可产生量子 Zeno 抑制。更一般地，POVM \(\{E_k\}\) 只给出
\[
y_k(t)=\operatorname{Tr}(E_k\rho(t)),
\qquad
\rho(t)=U_t\rho_0U_t^*
\tag{110.9}
\]
的读出。若同时对 \(H_j,\rho_0,E_k\) 作保持读出的酉共轭，或 POVM 湮灭某些谱模态，则不同动力学落入同一观测等价类；仅凭聚合的标签信号不能分别识别边相位、内部 coin 与真实传播速度。可辨识性必须另加完整测量族、校准初态和参数化假设。

第 73 节的量子信道把噪声和测量作为完全正映射处理，第 92 节的转移矩阵描述一般的词序传播；本节的 \(U_j\) 或 \(H_j\) 只有在附加酉性、自伴性及量子测量规则后才表示量子行走。三者都可以复用 FIB 的上下文索引，却对组合、谱和观测施加不同外加结构。由此，FIB 递归能够承载量子行走的状态空间和候选跳跃图，并在给定的酉算子、哈密顿量、噪声、初态、边界和测量协议下产生谱隙、弹道、扩散或局域化统计；这些物理规律及其指数不属于 FIB ATOM 递归的内生结论。

## 111. FIB 上下文图上的外加自旋玻璃、无序 Gibbs 场与重叠统计

固定一列 FIB 上下文图 \(G_j=(V_j,E_j)\)，在顶点放置自旋
\(\sigma_v\in\{-1,+1\}\)。给定外加随机耦合 \(J^{(j)}_{uv}\)、外场 \(h_v\) 和逆温 \(\beta\)，定义
\[
H_j(\sigma)
=-\sum_{\{u,v\}\in E_j}J^{(j)}_{uv}\sigma_u\sigma_v
-\sum_{v\in V_j}h_v\sigma_v,
\qquad
\mu_j(\sigma)=Z_j^{-1}e^{-\beta H_j(\sigma)}.
\tag{111.1}
\]
FIB 只提供上下文、标签、词序和候选边；耦合的随机律、符号相关、尺度归一化、边界和温度均为外加。令两个独立 Gibbs 样本为 \(\sigma,\tau\)，定义重叠
\[
q_j(\sigma,\tau)
=\frac1{|V_j|}\sum_{v\in V_j}\sigma_v\tau_v,
\qquad
P_j(\mathrm dq)=\mathbb P(q_j\in\mathrm dq).
\tag{111.2}
\]
\(P_j\) 是否集中在零点、是否有多个重叠峰以及其极限是否存在，均取决于外加无序与图列。

定义淬火和退火自由能密度
\[
f_j^{\mathrm q}
=-\frac1{\beta|V_j|}\mathbb E_J\log Z_j,
\qquad
f_j^{\mathrm a}
=-\frac1{\beta|V_j|}\log\mathbb E_J Z_j.
\tag{111.3}
\]
Jensen 不等式给出 \(f_j^{\mathrm q}\ge f_j^{\mathrm a}\)；差值记录无序平均与热平均的非交换。若 \(J^{(j)}\) 为零或耦合足够弱，并满足外加 Dobrushin 型条件
\[
\sup_{u\in V_j}\sum_{v:\{u,v\}\in E_j}
\tanh\!\bigl(\beta|J^{(j)}_{uv}|\bigr)<1
\tag{111.4}
\]
且该界在 \(j\) 上一致，则 Gibbs 状态唯一、边界影响衰减，重叠常在适当的中心化后集中。这个高温结论需要图度、耦合和边界的统一控制。

若图列和耦合缩放满足某个外加均场或稀疏随机图模型，低温时可能出现多个纯态和非平凡重叠分布；可以用
\[
\mathbb E\bigl[q_j(\sigma,\tau)^2\bigr]
\]
检验重叠涨落，也可引入三份样本的重叠三元组区分不同的无序相。这里“自旋玻璃相”只表示所声明模型的多态、慢混合或重叠结构；没有统一图列、耦合尾界和极限交换，不能从一个有限 FIB 图断言真正的热力学相变或 replica 对称性破缺。

若再给出外加 Glauber 翻转率
\[
c_v(\sigma)
=\kappa_v\,
\exp\!\left[-\frac{\beta}{2}
\bigl(H_j(\sigma^{v})-H_j(\sigma)\bigr)\right],
\tag{111.5}
\]
则在适当归一化下保持 \(\mu_j\) 的详细平衡。谱隙、混合时间、陷阱和 aging 行为由 \(\kappa_v\)、能垒、无序实现和边界决定；同一静态 Gibbs 律也可配以非详细平衡动力学而产生不同路径熵。静态重叠不唯一决定动态响应。

保持同一 FIB 图和词序，可以选择 \(J_{uv}=0\) 得到独立顺磁模型；选择同号强耦合得到铁磁序；选择均值为零的随机正负耦合并采用相应的稀疏或均场缩放，则可能得到玻璃化重叠与慢混合。只改变耦合相关长度、边界或温度就能改变 \(P_j\)、自由能差和混合时间。故自旋、耦合、热浴、纯态分解和“玻璃相”都属于外加统计力学解释，FIB 递归本身不选定任何无序相或临界温度。

## 112. FIB 状态载体上的外加随机共振与双稳态切换

固定 FIB 上下文序列 \(c_n\)，并给每个上下文附加一维外加势 \(U_c(x)\)。在连续时间中考虑受周期驱动和噪声的动力学
\[
\mathrm dX_t
=-U'_{c(t)}(X_t)\,\mathrm dt
+A\cos(\Omega t)\,\mathrm dt
+\sqrt{2D}\,\mathrm dW_t,
\tag{112.1}
\]
其中上下文日程 \(c(t)\)、势、驱动振幅 \(A\)、角频率 \(\Omega\)、噪声强度 \(D\) 和时间单位均为外加。若 \(U_c\) 具有两个稳定井 \(x_-\)、\(x_+\) 和势垒 \(x_b\)，在小噪声、稀有跃迁条件下，Kramers 近似给出
\[
r_\pm(D)
\asymp
\frac{\sqrt{|U''_c(x_b)|\,U''_c(x_\pm)}}{2\pi}
\exp\!\left[-\frac{\Delta U_\pm}{D}\right],
\qquad
\Delta U_\pm=U_c(x_b)-U_c(x_\pm).
\tag{112.2}
\]
将连续过程约化为两态占用概率 \(p(t)=\Pr(X_t\approx x_+)\)，则可写成
\[
\dot p
=r_+(t)(1-p)-r_-(t)p,
\tag{112.3}
\]
其中弱周期驱动通过改变两侧势垒使 \(r_\pm(t)\) 周期调制。在线性响应范围内，输出在 \(\Omega\) 处的谱峰和信噪比由 \(r_\pm(D)\)、\(A\) 及驱动相位决定。

当平均跃迁时间与外加驱动的半周期同阶，例如按角频率约定满足
\[
r_+(D)+r_-(D)\asymp\frac{\Omega}{\pi},
\tag{112.4}
\]
周期驱动和噪声可能最有效地同步双稳态切换，形成随机共振峰。\(D\) 太小时跃迁稀少，\(D\) 太大时两态区分被噪声抹平；(112.4) 只是小驱动、稀有跃迁和双态约化下的匹配条件，不是普适等式。若势只有一个稳定井、\(A=0\) 或 \(D=0\)，该机制消失。

若 \(c(t)\) 由 FIB 词序切换不同势阱，切换频率还受到词块长度和外加时间映射的影响。相同 FIB 词在平坦势、深双阱和多阱随机势下可分别表现为无切换、单一随机共振峰或多峰跃迁谱。改变噪声相关性还会把 Markov 两态约化改为有记忆的半马尔可夫响应；改变观测函数 \(g(X_t,c(t))\) 则可能隐藏实际切换，只留下低信噪比边缘。

随机共振的谱峰、最优噪声强度和跃迁率因此同时依赖势垒、曲率、驱动、热噪声、上下文时钟和观测协议。FIB 递归只提供上下文序列和可能的势切换顺序，不提供势能、温度、噪声、物理时间或信号单位；同一 FIB 载体可在外加模型下有随机共振，也可完全没有共振，不能把 (112.1)–(112.4) 解释为 FIB 内生的物理定律。

## 113. FIB 上下文图上的外加反应—扩散、Turing 失稳与模式选择

固定 FIB 词 \(W_j=w(T_j)\)，以其位置或合法上下文为顶点，另取有限无向加权图
\[
\Gamma_j=(V_j,E_j,\omega^{(j)}),\qquad
(\mathcal L_jx)(i)=\sum_{k:\{i,k\}\in E_j}
\omega^{(j)}_{ik}\bigl(x(i)-x(k)\bigr).
\tag{113.1}
\]
FIB 只提供词序、标签和候选组合关系；边集、边权、空间嵌入和连续时间均为外加。设 \(\mathcal L_j\phi_{j,m}=\mu_{j,m}\phi_{j,m}\)，且 \(\mu_{j,0}=0\)。

在每个顶点配置两种外加浓度，规定
\[
\frac{\mathrm d}{\mathrm dt}\binom{u_i}{v_i}
=\gamma F(u_i,v_i)
-\begin{pmatrix}d_u&0\\0&d_v\end{pmatrix}
\binom{(\mathcal L_ju)_i}{(\mathcal L_jv)_i},
\qquad d_u,d_v,\gamma>0,
\tag{113.2}
\]
其中 \(F=(f,g)^{\mathsf T}\) 是 \(C^1\) 反应场。若 \(F(u_*,v_*)=0\)，记
\[
J=DF(u_*,v_*)=
\begin{pmatrix}a&b\\c&d\end{pmatrix},
\qquad
P=ad-bc,\qquad S=ad_v+dd_u.
\tag{113.3}
\]
对图谱模态 \(\phi_{j,m}\) 的线性块为
\[
B_{j,m}(\gamma)=\gamma J-\mu_{j,m}
\begin{pmatrix}d_u&0\\0&d_v\end{pmatrix}.
\tag{113.4}
\]
若 \(a+d<0\) 且 \(P>0\)，无扩散均匀平衡线性稳定；同时
\[
\operatorname{tr}B_{j,m}
=\gamma(a+d)-\mu_{j,m}(d_u+d_v)<0,
\]
\[
\det B_{j,m}
=\gamma^2P-\gamma S\mu_{j,m}+d_ud_v\mu_{j,m}^2.
\tag{113.5}
\]
因此有限图出现严格的线性 Turing 失稳，当且仅当某个 \(m\ge1\) 使 \(\det B_{j,m}<0\)。若
\[
S>0,\qquad S^2>4d_ud_vP,
\]
令
\[
\chi_\pm=\frac{S\pm\sqrt{S^2-4d_ud_vP}}{2d_ud_v},
\qquad 0<\chi_-<\chi_+.
\tag{113.6}
\]
则第 \(m\) 个模态的失稳条件等价于
\[
\chi_-<\frac{\mu_{j,m}}{\gamma}<\chi_+.
\tag{113.7}
\]
连通图的首次非均匀失稳阈值为
\[
\gamma_{j,\mathrm{on}}=\frac{\mu_{j,1}}{\chi_+},
\tag{113.8}
\]
而实际首先增长的图样由
\[
\operatorname*{arg\,max}_{m:\,\chi_-<\mu_{j,m}/\gamma<\chi_+}
\max\operatorname{Re}\operatorname{spec}B_{j,m}
\tag{113.9}
\]
决定。重特征值会使整个特征空间同时失稳；边权或边界改变 \(\mu_{j,m}\)，即可改变阈值和图样。

若另加图列 \(j\to\infty\) 的谱收敛 \(\mu_{j,m}\to\kappa_m\) 及特征向量插值收敛，则远离带边界的固定模态继承同一稳定性判定，且 \(\gamma_{j,\mathrm{on}}\to\kappa_1/\chi_+\)。例如外加区间 Neumann 拉普拉斯给出 \(\kappa_m=(m\pi)^2\)，但这个连续桥不是 FIB 递归的结果。非线性饱和、噪声选模、斑图唯一性以及有向或非对称图上的复谱，均需另行处理；不能把 (113.7) 宣称为 FIB 的内生定律。

## 114. FIB 上下文随机矩阵的谱测度、稀疏退化与普适性边界

固定上下文长度 \(\ell\)，令 \(\mathcal C_\ell\) 为合法 Fibonacci 因子集合，\(N_\ell=|\mathcal C_\ell|=\ell+1\)。以长度 \(\ell+1\) 合法重叠定义邻接支撑 \(J_\ell\)。该支撑只有 \(N_\ell+1=O(N_\ell)\) 条边，每行和每列至多有两个非零元。FIB 递归因此给出稀疏索引和确定性背景；它不自动产生 Wigner 所需的 \(O(N_\ell^2)\) 个随机条目。

在每条合法边上放置中心化、单位方差的外加随机权 \(\Xi_\ell\)，并令
\[
R_\ell=J_\ell\odot\Xi_\ell,\qquad
X_\ell=\frac{R_\ell}{\sqrt{N_\ell}}.
\tag{114.1}
\]
无论边权之间怎样相关，只要二阶矩存在，就有
\[
\mathbb E\!\left[\frac1{N_\ell}\|X_\ell\|_{\mathrm F}^2\right]
=\frac{N_\ell+1}{N_\ell^2}\longrightarrow0.
\tag{114.2}
\]
由 \(\sum_k|\lambda_k(X_\ell)|^2\le\|X_\ell\|_{\mathrm F}^2\)，任意固定 \(\varepsilon>0\) 的谱质量
\[
\frac1{N_\ell}\#\{k:|\lambda_k(X_\ell)|>\varepsilon\}
\]
依概率趋于零；经验特征值测度退化到 \(\delta_0\)。这说明把稠密 Wigner 的 \(N^{-1/2}\) 归一化直接套在原生 FIB 稀疏支撑上，会抹掉非退化谱。

若在另行选定的 \(N\) 个 FIB 索引上外加厄米 Wigner 矩阵 \(W_N\)，其上三角条目独立中心化、方差为 \(1/N\)，并满足统一矩条件，则条件性半圆律为
\[
\mu_{\sigma W_N}\Longrightarrow
\frac{\sqrt{(4\sigma^2-x^2)_+}}{2\pi\sigma^2}\,\mathrm dx.
\tag{114.3}
\]
加入算子范数有界且经验谱收敛到 \(\nu\) 的确定性背景 \(A_N\) 后，候选极限变为
\[
\mu_{A_N+\sigma W_N}\Longrightarrow
\nu\boxplus\mathrm{SC}_{\sigma^2}.
\tag{114.4}
\]
若随机矩阵改为非厄米、稠密且条目方差为 \(\sigma^2/N\)，在相应矩条件下得到圆律；反向条目的相关性会改成椭圆型谱域。非厄米结论还需控制小奇异值，特征值距离不能代替预解式稳定性。

按上下文种类等权计数、按来源实际出现位置加权和按谱模态等权，是三种不同的观测合同。黄金比例频率不能单独确定谱密度；合法边上的随机权也不能单独推出半圆律、圆律或局部普适性。谱隙、局部间距和混合间隙分别属于不同算子问题。故 FIB 只确定索引与支撑，随机联合律、归一化、维数极限和谱观测均为外加。

## 115. FIB 实际位置上的外加排斥粒子、守恒流与密度冲击

固定共同来源 \(w\in X_\tau\)，并取上下文长度 \(m\)。位置 \(i\) 的上下文为 \(c_i=w_i\cdots w_{i+m-1}\)；保留实际位置的提升图以 \(i\) 为顶点，即使 \(c_i=c_k\)，位置 \(i,k\) 仍不合并。FIB 只给出来源和上下文标签；粒子占用、时钟、跳率、边界和空间缩放均为外加。令 \(\eta_i(t)\in\{0,1\}\) 表示排斥占用，\(\eta_i\eta_{i+1}=1\) 时禁止相邻交换。

在整数位置上指定右跳率 \(p_i\)、左跳率 \(q_i\)。跨键 \(i,i+1\) 的瞬时净流强度为
\[
j_i(\eta)=p_i\,\eta_i(1-\eta_{i+1})
-q_i\,\eta_{i+1}(1-\eta_i).
\tag{115.1}
\]
位置占用满足路径级连续性方程
\[
\eta_i(t)-\eta_i(0)
=Q_{i-1}(t)-Q_i(t),
\tag{115.2}
\]
其中 \(Q_i\) 是跨键净跳数；减去 \(\int_0^t j_i(\eta_s)\,\mathrm ds\) 后得到鞅。守恒的是外加粒子数，不是 FIB 字母计数。

在周期均匀 ASEP 中，右率 \(p\)、左率 \(q\) 为常数，密度为 \(\rho\) 的平稳积测度给出
\[
J(\rho)=(p-q)\rho(1-\rho).
\tag{115.3}
\]
固定粒子数的有限环使用相应的均匀典范测度；有限尺寸电流需保留粒子数约束。欧拉缩放和局部平衡成立时，宏观密度满足熵解
\[
\partial_t\rho+\partial_xJ(\rho)=0.
\tag{115.4}
\]
两个常密度 \(\rho_L,\rho_R\) 的冲击速度为
\[
s=\frac{J(\rho_R)-J(\rho_L)}{\rho_R-\rho_L}
=(p-q)(1-\rho_L-\rho_R).
\tag{115.5}
\]
对称情形 \(p=q\) 的一阶流消失；在另加扩散缩放和局部平衡条件后，才得到热方程型扩散极限。

若 \(p_i,q_i\) 随上下文或位置变化，(115.1) 仍然成立，但平均电流含二点联合占用概率，不能只由类型边缘频率决定。只观察每一上下文类的占用总数会丢失位置顺序和可用空位，存在相同聚合读数对应不同跳率的成对实现。周期闭合、储库边界和反射边界也产生不同稳态与波速。该排斥模型区别于第95节的线性守恒流：非线性通量来自排斥约束，FIB 标签本身不提供粒子统计或 ASEP 参数。

## 116. FIB 类型骨架上的外加复制子—突变、准种阈值与有限群体涨落

固定窗口长度 \(r\)，令 \(\mathcal X_r\) 为合法 Fibonacci 因子类型，\(d=|\mathcal X_r|\)。FIB 提供类型集合、合法接续和组成递归；适应度、突变、群体大小和抽样律均外加。令 \(x_t\in\Delta_{d-1}\) 为频率列向量，选择矩阵和突变核为
\[
W(s)=\operatorname{diag}(e^{sf_1},\ldots,e^{sf_d}),
\qquad
Q(\mu)_{ij}=\Pr(i\to j),
\qquad
A(s,\mu)=Q(\mu)^{\mathsf T}W(s).
\tag{116.1}
\]
“先选择后突变”的确定性动力学为
\[
x_{t+1}
=\frac{A(s,\mu)x_t}
{\mathbf1^{\mathsf T}A(s,\mu)x_t}.
\tag{116.2}
\]
若突变会离开合法语言，还须另给拒绝、投影或修复核 \(R\)，实际核为 \(Q(\mu)R\)；组成矩阵的 Perron 根不能替代这个概率合同。

若 \(A(s,\mu)\) primitive，设 \(\lambda_1>|\lambda_2|\) 为 Perron 根和次大模特征值，归一化 Perron 向量为 \(v_1\)，则
\[
\Phi_{s,\mu}(v_1)=v_1,\qquad
x_t\to v_1,\qquad
\|x_t-v_1\|=O\!\left((|\lambda_2|/\lambda_1)^t\right).
\tag{116.3}
\]
谱隙闭合时，收敛速度和极限的可识别性都会恶化。选择—突变与 FIB 上下文转移的次序只有在相应矩阵可交换时才等价。

两类准种模型说明误差阈值如何出现。设主型适应度 \(\sigma>1\)，突变云适应度 \(1\)，长度为 \(L\)，逐位突变率为 \(\mu\)，主型复制保真度
\[
\eta=(1-\mu)^L.
\]
忽略突变云回流时，主型平衡频率为
\[
x_0^*=
\begin{cases}
\dfrac{\sigma\eta-1}{\sigma-1},&\sigma\eta>1,\\[1ex]
0,&\sigma\eta\le1,
\end{cases}
\qquad
\mu_c=1-\sigma^{-1/L}.
\tag{116.4}
\]
加入正回流率会把尖锐阈值平滑化。式 (116.4) 的长度、适应度和突变率均不是 FIB 递归决定的。

若群体大小为 \(N\)，采用外加 Wright–Fisher 抽样，则
\[
Z_{t+1}\mid\widehat x_t
\sim\operatorname{Multinomial}
\bigl(N,\Phi_{s,\mu}(\widehat x_t)\bigr),
\qquad
\operatorname{Cov}(\widehat x_{t+1}\mid\widehat x_t)
=\frac1N\bigl(\operatorname{diag}(p_t)-p_tp_t^{\mathsf T}\bigr),
\tag{116.5}
\]
其中 \(p_t=\Phi_{s,\mu}(\widehat x_t)\)。在稳定轨道和适当正则条件下，\(\sqrt N(\widehat x_t-x_t)\) 的固定时间窗极限是由线性化 Jacobian 驱动的高斯递推；这只是有限群体近似，不能把类型频率读数解释成内生生物适应度。只观察 FIB 标签边缘还不能区分选择、突变修复和抽样噪声。

## 117. FIB 实际位置上的外加 Lévy 跳跃、分数阶输运与首达尾

固定上下文长度 \(m\)，以合法长度 \(m\) 因子和重叠边构成有限上下文图；再固定实际来源 \(x\in X_\tau\)，位置 \(i\) 的上下文记为 \(u_m(i)\)。类型图是有限的，实际位置提升 \((i,u_m(i))\) 才提供无界空间尺度。FIB 提供合法窗口和位置标记；跳跃律、距离、速度质量、重尾指数、时间单位和边界均为外加。

在选定载体上给定正速度质量 \(\pi\) 和对称权 \(J(u,v)\)，外加连续时间生成元
\[
(\mathcal Lf)(u)
=\frac1{\pi(u)}\sum_{v\ne u}J(u,v)\bigl(f(v)-f(u)\bigr).
\tag{117.1}
\]
若 \(H\) 是非负自伴局部拉普拉斯，另取 \(0<s<1\) 与 \(\kappa>0\)，谱从属定义
\[
\mathcal L_s=-\kappa H^s
=-\frac{\kappa s}{\Gamma(1-s)}
\int_0^\infty(I-e^{-rH})\frac{\mathrm dr}{r^{1+s}}.
\tag{117.2}
\]
这会产生远距离跳跃，但 \(s,\kappa\) 和从属时钟是外加的；有向重叠图也不能未经对称化直接当作自伴分数拉普拉斯。固定有限图只有有限直径，不能在无限时间上自动产生重尾空间尺度。

若在实际位置提升上指定独立泊松时钟和对称跳长 \(K\)，满足
\[
\Pr(|K|=k)\sim c\,k^{-1-\eta},
\qquad 0<\eta<2,
\tag{117.3}
\]
则在外加尺度 \(a_j\to\infty\) 下有稳定极限
\[
\frac{I_{a_j^\eta t}}{a_j}\Longrightarrow S_t,
\tag{117.4}
\]
其中 \(S_t\) 是特征指数 \(D_\eta|\xi|^\eta\) 的对称 \(\eta\)-稳定 Lévy 过程，\(D_\eta\) 由跳跃强度、尾常数和长度单位决定。对阶数 \(r<\eta\) 的绝对矩，典型距离按 \(t^{r/\eta}\) 标度；\(r\ge\eta\) 时相应绝对矩发散，不能把稳定过程报告成有限均方扩散。

首达目标还取决于边界合同：先截断局部过程再取分数次幂、先在完整空间构造稳定过程再杀死、删去外跳或把外跳回送，都是不同生成元。长跳可以越过边界而不命中边界点，因此越界、进入集合和精确命中不能混为一个事件。固定跳长或有限位置窗口最终会出现截止；稳定律只能是经明确缩放得到的极限或中间尺度律。该模型区别于第94节的重尾更新奖励和第69节的分数高斯记忆：这里的重尾来自空间跳长与非局部生成元。FIB 递归本身不选择 Lévy 指数、分数阶数、首达尾或物理长度。

## 118. FIB 上下文图上的外加不可压流、能量与湍流统计

固定有限连通定向图 \(G=(V,E)\)，令 \(d_0:\mathbb R^V\to\mathbb R^E\) 为顶点—边差分，并给顶点、边外加正定质量矩阵 \(H_0,H_1\)。定义
\[
G_0=d_0,\qquad
\delta_0=H_0^{-1}d_0^{\mathsf T}H_1,\qquad
D=-\delta_0,\qquad
K=\ker D.
\tag{118.1}
\]
边变量 \(u\) 只有在另加空间嵌入后才可解释为速度。FIB 只提供顶点、标签、词序和候选边；质量、密度、边长、体积、边界和物理时钟均为外加。令 \(P\) 为边内积下到 \(K\) 的正交投影。

另给自伴非负耗散算子 \(A\)、外力 \(f\) 和二次对流项 \(N(u)\)，要求
\(\langle u,N(u)\rangle_{H_1}=0\)。外加离散欧拉—Navier–Stokes 模型为
\[
\dot u+N(u)=-G_0\pi-\nu Au+f,\qquad
Du=0,
\qquad \nu\ge0,
\tag{118.2}
\]
或投影后
\[
\dot u=-PN(u)-\nu PAu+Pf.
\]
在封闭边界、压力正交且对流抵消时，动能
\[
E(t)=\frac{\rho}{2}\langle u,u\rangle_{H_1}
\]
满足
\[
\frac{\mathrm dE}{\mathrm dt}
+\rho\nu\langle u,Au\rangle_{H_1}
=\rho\langle u,f\rangle_{H_1}.
\tag{118.3}
\]
因此无外力无黏模型守恒动能，黏性模型动能不增；严格衰减还需要 \(A\) 在状态空间上有谱隙。固定有限图上的有限维能量估计不能直接推出无限细化三维流体的全局正则性。

顶点—边数据没有唯一的局部涡量。若另给面集合 \(F\)、边—面差分 \(C:\mathbb R^E\to\mathbb R^F\)，满足 \(Cd_0=0\)，则可定义
\[
\omega=Cu,\qquad
\dot\omega+CN(u)=-\nu C\delta_1\omega+Cf,
\tag{118.4}
\]
其中 \(\delta_1\) 由外加面质量定义。树图或纯一维图上可能没有非平凡不可压耗散；环流、Kelvin 定律和涡量平方守恒都需额外的物质环路与离散复形相容性。

只有在外加特征长度 \(L\)、速度 \(U\) 和黏度 \(\nu\) 后，Reynolds 数才定义为
\[
\operatorname{Re}=\frac{UL}{\nu}.
\tag{118.5}
\]
FIB 迭代序号不是物理时间，词长也不是物理长度。若另加平稳初态与驱动概率律，才可研究平均注能、耗散、能谱或湍流级联；大 Reynolds 数本身不保证湍流。故 FIB 递归只提供组合流体载体，能量律和湍流标度属于外加流体实现。

## 119. FIB 有限逼近图上的外加复跃迁、拓扑能带与边缘输运

取第 \(L\) 层有限 FIB 逼近图 \(G_L=(V_L,E_L)\)，在其上另加参数环面
\[
\Theta=\mathbb T^2,\qquad \theta=(k,\phi),
\]
其中 \(k\) 是周期扭转角，\(\phi\) 是外加相位或 phason。若 FIB 只给出离散替换，连续 \(\phi\) 插值仍需单独指定。定义自伴复跃迁 Hamiltonian
\[
H_L(k,\phi)
=\sum_xv_x(\phi)|x\rangle\langle x|
+\sum_{(x,y)\in E_L}
\left[t_{xy}e^{\,\mathrm i(A_{xy}(\phi)+\nu_{xy}k)}
|x\rangle\langle y|+\mathrm{h.c.}\right].
\tag{119.1}
\]
顶点规范只改变边相位表示；回路磁通是规范不变量。树图上的相位在适当条件下可全部消去，存在回路也只是产生非平凡拓扑的必要结构，不是充分条件。

选定带群 \(I\)，若统一能隙
\[
g_{L,I}
=\inf_{(k,\phi)\in\Theta}
\min_{\substack{a\in I\\b\notin I}}
|E_{L,a}(k,\phi)-E_{L,b}(k,\phi)|>0,
\tag{119.2}
\]
则谱投影 \(P_{L,I}(k,\phi)\) 在参数环面上连续。其投影 Berry 曲率与 Chern 数为
\[
\mathcal F^{(L)}_{k\phi}
=\mathrm i\,\operatorname{Tr}
\bigl(P_{L,I}[\partial_kP_{L,I},\partial_\phi P_{L,I}]\bigr),
\qquad
C_{L,I}=\frac1{2\pi}\int_{\Theta}\mathcal F^{(L)}_{k\phi}\,\mathrm dk\,\mathrm d\phi.
\tag{119.3}
\]
在光滑投影、固定环面取向和能隙不闭合的连续变形下，\(C_{L,I}\in\mathbb Z\) 且保持不变；带内简并时只有整个投影的总 Chern 数可识别。

若 \(\phi\) 绝热绕行一周且带群保持占据，外加绝热泵浦合同给出
\[
Q_L/e=C_{L,I}.
\tag{119.4}
\]
开边界还需另定义端点势与切口删除。共同体能隙、局部边界和热力学极限成立时，边缘谱流可与 \(C_{L,I}\) 相等；有限层左右边缘杂化或局域 Tamm 态会使单个边缘峰不具有拓扑判别力。实际电导仍依赖引线、占据、散射和退相干。FIB 只提供图和层间关系，复跃迁、参数环面、能隙、边界和输运端口均为外加。

## 120. FIB 合法路径上的外加随机定向聚合物、自由能与候选标度

固定 FIB 合法有向图及其长度 \(n\) 的合法路径集合 \(\Omega_n(x,y)\)。随机环境只给合法边加权，不改变路径集合。对路径
\(\pi=(v_0,e_1,v_1,\ldots,e_n,v_n)\)，定义
\[
H_n^\xi(\pi)=\sum_{i=1}^n\xi_i(e_i),
\qquad
Z_n^\xi(x,y;\beta)
=\sum_{\pi\in\Omega_n(x,y)}
\mu_0(\pi)e^{\beta H_n^\xi(\pi)},
\qquad
Z_n^\xi(x;\beta)=\sum_yZ_n^\xi(x,y;\beta).
\tag{120.1}
\]
参考路径权 \(\mu_0\)、逆温 \(\beta\)、随机势的时间相关性和端点坐标均为外加。静态边势与分层独立环境不是同一模型。

在平稳遍历环境和相应指数矩条件下，quenched 与 annealed 自由能分别取为
\[
f_{\mathrm q}(\beta)=\lim_{n\to\infty}\frac1n
\mathbb E_\xi\log Z_n^\xi,
\qquad
f_{\mathrm a}(\beta)=\lim_{n\to\infty}\frac1n
\log\mathbb E_\xi Z_n^\xi,
\qquad
f_{\mathrm q}\le f_{\mathrm a}.
\tag{120.2}
\]
若每层环境独立同分布，\(\Lambda(\beta)=\log\mathbb E e^{\beta\xi}\)，并且 \(\mu_0\) 是行随机核，则
\[
M_n=e^{-n\Lambda(\beta)}Z_n^\xi
\]
是可用于弱无序分析的非负鞅；若路径按计数而非概率核加权，还必须除以合法骨架的 Perron 增长因子。FIB 路径熵与参考核归一化不可混用。

若合法路径具有真实横向坐标、非退化分叉和短程混合随机势，可提出 \(1+1\) 维 KPZ 候选标度
\[
\operatorname{Var}(\log Z_n)\asymp n^{2/3},
\qquad
\log Z_n-nf_{\mathrm q}=O_{\mathrm{fluc}}(n^{1/3}),
\qquad
|X_n-nv|=O_{\mathrm{fluc}}(n^{2/3}).
\tag{120.3}
\]
这些是外加几何和无序满足条件时的候选普适律；有限宽 FIB 自动机的横向尺度有界时，通常应排除 KPZ 横向指数，转而分析随机矩阵乘积的中心涨落和速度型大偏差。第101节讨论的是随机界面生长，不能自动替代本节的路径配分函数。

因此，FIB 只规定可走路径和合法性；随机势、温度、参考权、端点坐标和长度极限决定自由能、无序相及其标度。相同路径骨架可在弱无序、冻结或有限宽度模型中产生不同统计律。

## 121. FIB 上下文图上的外加 Gaussian 自由场、Green 协方差与对数相关

取有限连通上下文图 \(G_n=(V_n,E_n)\)，指定接地边界 \(B_n\subset V_n\)、内部 \(I_n\) 和正导通率 \(c_n(x,y)=c_n(y,x)\)。内部 Dirichlet 拉普拉斯记为 \(L_{n,D}\)，刚度 \(\kappa_n>0\)。零边界 Gaussian 自由场的密度为
\[
\mathrm d\mathbb P_n(h)
\propto
\exp\!\left[
-\frac{\kappa_n}{2}
\sum_{\{x,y\}\in E_n}c_n(x,y)(h_x-h_y)^2
\right]\prod_{x\in I_n}\mathrm dh_x,
\qquad h|_{B_n}=0.
\tag{121.1}
\]
于是
\[
\operatorname{Cov}(H_n(x),H_n(y))
=\kappa_n^{-1}G_n(x,y),
\qquad
G_n=L_{n,D}^{-1}.
\tag{121.2}
\]
若另给速度质量 \(m_n\)，热核积分必须按终点质量归一化；速度质量、能量导通率和 FIB 出现频率是不同数据。

有效电阻给出增量方差：
\[
\operatorname{Var}(H_n(x)-H_n(y))
=\kappa_n^{-1}
\bigl(G_n(x,x)+G_n(y,y)-2G_n(x,y)\bigr)
=\kappa_n^{-1}R_{\mathrm{eff},n}^{B_n}(x,y).
\tag{121.3}
\]
多个接地顶点的接线会改变有效电阻；不接地有限图的常数零模必须通过零均值约束或伪逆另行处理。

若图列嵌入到共同空间并满足归一化协方差的对数相关条件
\[
\widehat C_n(x,y)
=a\log\frac{\ell_0}
{d(\iota_nx,\iota_ny)\vee\varepsilon_n}
+r_n(x,y),
\tag{121.4}
\]
其中余项一致有界且微观截止 \(\varepsilon_n\to0\)，则可提出 Gaussian multiplicative chaos 候选测度
\[
\mathrm d\mathcal M_\gamma
=\lim_{n\to\infty}
\exp\!\left(
\gamma\widehat H_n
-\frac{\gamma^2}{2}
\operatorname{Var}\widehat H_n
\right)\mathrm d\mu,
\tag{121.5}
\]
但其非退化范围、紧性和边界行为需要额外证明（通常要求 \(\gamma^2a\) 低于相应临界值）。有限图 Gaussian 恒等式不自动给出无限体积场、连续版本或混沌极限。FIB 只提供组合图和标签；导通率、刚度、嵌入、接地边界及随机场归一化均为外加。

## 122. FIB 类型骨架上的外加分枝随机游走、极值前沿与 KPP 接口

FIB 替换给出两类祖先—后裔骨架：\(\alpha\) 产生一个 \(\beta\)，\(\beta\) 产生一个 \(\beta\) 和一个 \(\alpha\)，其计数矩阵为
\[
A=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
\tag{122.1}
\]
这里的世代是替换次数，不等同于叶词位置或物理时间。另给类型边 \(i\to j\) 的独立位移律 \(K_{ij}\)，根位置为零，粒子 \(u\) 的位置为路径位移和 \(S(u)\)，第 \(n\) 代最大值为 \(R_n=\max_{|u|=n}S(u)\)。位移概率与祖先树独立性均为外加合同。

令 \(H_{n,i}(x)=\Pr_i(R_n\le x)\)。在分开子树独立时，
\[
\begin{aligned}
H_{n+1,\alpha}(x)
&=\int H_{n,\beta}(x-y)K_{\alpha\beta}(\mathrm dy),\\
H_{n+1,\beta}(x)
&=\left[\int H_{n,\beta}(x-y)K_{\beta\beta}(\mathrm dy)\right]
\left[\int H_{n,\alpha}(x-y)K_{\beta\alpha}(\mathrm dy)\right].
\end{aligned}
\tag{122.2}
\]
同胞位移相关时必须改用联合律，不能用两个边缘卷积相乘。若边指数矩
\[
m_{ij}(\theta)=\int e^{\theta y}K_{ij}(\mathrm dy),
\qquad
B(\theta)=
\begin{pmatrix}
0&m_{\alpha\beta}(\theta)\\
m_{\beta\alpha}(\theta)&m_{\beta\beta}(\theta)
\end{pmatrix},
\qquad
\kappa(\theta)=\log\rho(B(\theta)),
\tag{122.3}
\]
则指数矩估计给出
\[
\Pr_i(R_n\ge cn)
\le e^{-\theta cn}[B(\theta)^n\mathbf1]_i,
\qquad
\limsup_{n\to\infty}\frac{R_n}{n}
\le \inf_{\theta>0}\frac{\kappa(\theta)}{\theta}.
\tag{122.4}
\]
把上界提升为精确速度需要多类型分枝随机游走定理、不可约性、非格点性和可积条件。若全部位移独立且服从 \(N(\mu,\sigma^2)\)，则候选线性速度为
\[
c_*=\mu+\sigma\sqrt{2\log\varphi},
\qquad
\varphi=\frac{1+\sqrt5}{2},
\tag{122.5}
\]
但这仍需相应极值定理核验。

在适用的轻尾、非格点临界条件下，最大值中心可具有
\[
a_n=c_*n-\frac{3}{2\theta_*}\log n,
\qquad
\Pr_i(R_n-a_n\le x)
\to
\mathbb E_i\!\left[
e^{-C_iD_{\infty,i}e^{-\theta_*x}}
\right],
\tag{122.6}
\]
其中 \(D_{\infty,i}\) 是需单独证明收敛的临界导数鞅极限。有限容量的分枝—选择会删除领先以外的后裔，速度一般低于无选择过程；连续 Brownian 位移和指数分枝时，还可在额外合作型条件下得到两类型 Fisher–KPP 前沿。所有位移、时钟、容量、选择和连续极限均为外加，FIB 递归本身只给出类型骨架与计数关系。

## 123. FIB 合法上下文图上的外加二聚体、随机铺砖与高度涨落

固定有限合法上下文图，并另选无向图
\[
\Gamma_\partial=(V_\partial,E_\partial)
\]
作为匹配载体。FIB 接缝只筛选候选边；无向化、完美匹配约束、铺砖几何、边界和边权均为外加。完美匹配配置为
\[
\mathcal M_\partial
=\left\{M\subseteq E_\partial:
\sum_{e\ni v}1_{\{e\in M\}}=1
\ \text{对所有 }v\in V_\partial\right\}.
\tag{123.1}
\]
若采用二分图，还须满足两侧等势与 Hall 条件；FIB 的两个字母不自动是二分颜色。给每条允许边正权 \(\omega_e\)，配分函数和概率律为
\[
Z_\partial=\sum_{M\in\mathcal M_\partial}\prod_{e\in M}\omega_e,
\qquad
\mathbb P_\partial(M)=Z_\partial^{-1}\prod_{e\in M}\omega_e.
\tag{123.2}
\]
无完美匹配时 \(Z_\partial=0\)，概率模型尚未定义；允许单体则是另一模型。

若 \(\Gamma_\partial\) 已给定平面二分嵌入并满足 Kasteleyn 符号条件，黑点为行、白点为列的 Kasteleyn 矩阵 \(K\) 给出
\[
Z_\partial=|\det K|.
\tag{123.3}
\]
平面非二分情形改用 Pfaffian；环面边界需要多个绕行扇区的扭转矩阵组合。普通邻接矩阵不能替代 Kasteleyn 矩阵，因为其行列式会发生符号抵消。

当 \(K\) 可逆时，边占用具有行列式相关核。对互不相同的边 \(e_i=(b_i,w_i)\)，
\[
\mathbb P_\partial(e_1,\ldots,e_r\in M)
=\left(\prod_i k_{e_i}\right)
\det[(K^{-1})_{w_i b_j}]_{i,j=1}^r,
\tag{123.4}
\]
并且
\[
\frac{\partial\log Z_\partial}{\partial\log\omega_e}
=\mathbb P_\partial(e\in M),\qquad
\frac{\partial^2\log Z_\partial}
{\partial\log\omega_e\,\partial\log\omega_f}
=\operatorname{Cov}(1_e,1_f).
\tag{123.5}
\]
相关核不必 Hermitian，不能仅凭形式符号断言所有边负相关。若另给平面二分取向和参考匹配，匹配差流可积成面高度；高度增量的方差由 (123.4) 的协方差双重和决定。连续液态高度极限、熵密度和高斯涨落需要额外周期图列、嵌入、权重归一化与紧性假设。FIB 只提供合法关系，不内生生成匹配、铺砖或高度场。

## 124. FIB 类型与上下文路径上的外加 Hawkes 自激、分枝簇与长时统计

固定有限类型集 \(I=\{1,\ldots,d\}\)，类型可来自 FIB 标签或上下文接口，但不因此获得概率律。给出连续时间、初始历史、移民率 \(\mu_i\ge0\) 和非负核 \(h_{ij}\)，定义
\[
\lambda_i(t)
=\mu_i+\sum_{j=1}^d\int_{(-\infty,t)}
h_{ij}(t-s)\,N_j(\mathrm ds),
\qquad
K_{ij}=\int_0^\infty h_{ij}(u)\,\mathrm du.
\tag{124.1}
\]
\(\lambda_i(t)\) 是外加历史滤过下的可预测条件强度；FIB 替换次数不是此处的物理时钟。

Hawkes 过程具有移民—分枝簇表示：每个类型 \(j\) 事件独立地产生类型 \(i\) 后代，平均直接后代矩阵为 \(K\)。若谱半径 \(\rho(K)<1\)，则
\[
R=(I-K)^{-1}=\sum_{n\ge0}K^n,
\qquad
\bar\lambda=R\mu
\tag{124.2}
\]
给出有限簇均值与平稳平均强度。对临界 \(\rho(K)=1\)，单簇可几乎必然灭绝但期望簇大小发散；持续移民下不能继续使用有限逆矩阵。对超临界 \(\rho(K)>1\)，可达类型有正概率生成无限簇；这不等同于有限时间爆炸。

若核具有统一指数尾界并满足亚临界条件，平稳计数在长时间下满足遍历大数律和中心极限定型
\[
\frac{N((0,T])}{T}\to\bar\lambda,
\qquad
\frac{N((0,Tt])-Tt\bar\lambda}{\sqrt T}
\Longrightarrow\Sigma^{1/2}W(t),
\tag{124.3}
\]
其中 \(\Sigma\) 保留同一分枝簇造成的跨类型共同涨落。只观测 FIB 类型边缘频率，不能区分移民率、触发核和共同父事件；需要完整事件时间与类型联合观测。所有 Hawkes 核、移民、时间和观测协议均为外加，FIB 关系只提供标记载体。

## 125. FIB 词序与替换层上的外加 Floquet 驱动、准能谱和子谐响应

固定 FIB 词 \(W_j=w_1\cdots w_{L_j}\)，在位置上配置自旋自由度。替换层 \(j\) 表示不同有限纹理或规模，物理时间另由外部周期 \(T\) 给出。令 \(H_{z,j}\) 是按字母选择耦合和纵向场得到的外加 Ising 算子，周期脉冲为横向旋转，则
\[
U_{F,j}
=e^{-\mathrm i\tau H_{z,j}}
e^{-\mathrm i(\pi/2+\delta)\sum_iX_i}
\tag{125.1}
\]
是一个周期 Floquet 算子。字母到耦合的映射、脉冲形状、周期、初态与采样相位均不是 FIB 递归的输出；若按 Fibonacci 词依次改变脉冲，有限词重复形成的超周期也需另行声明。

准能由
\[
U_{F,j}|\phi_a\rangle
=e^{-\mathrm i\varepsilon_aT}|\phi_a\rangle,
\qquad
\varepsilon_a\in\mathbb R/(2\pi/T)\mathbb Z
\tag{125.2}
\]
定义。在理想 \(\delta=0\) 且纵向算子与 \(H_{z,j}\) 对易时，
\[
U_{F,j}^\dagger Z_iU_{F,j}=-Z_i,
\tag{125.3}
\]
所以纵向磁化在每周期翻转、两周期恢复，并产生准能相差 \(\pi/T\) 的配对。这是精确脉冲模型的代数结论；非零误差会产生漂移包络，不能仅据此宣称稳定时间晶体。

多体子谐响应需要额外的多体局域化或预热机制、局域序、准能配对和稳定参数区域。预热正规形可写成
\[
U_F\simeq R^\dagger P e^{-\mathrm iTD}R,
\qquad
P^2=I,\qquad [D,P]=0,
\tag{125.4}
\]
但必须同时给出准局域误差和有效时间窗。固定有限一维短程链、高频或有限样本中看到的周期二信号，都不足以推出热力学时间晶体。FIB 只供给纹理与词序，周期驱动、相互作用、噪声和观测协议均外加。

## 126. FIB 上下文图上的外加离散非线性 Schrödinger、孤子与调制不稳定

固定有限无向耦合图 \(G=(V,E)\)，给顶点正权 \(m_i\) 和边权 \(w_{ij}=w_{ji}\ge0\)。加权图拉普拉斯为
\[
(L\psi)_i=\frac1{m_i}\sum_jw_{ij}(\psi_i-\psi_j).
\tag{126.1}
\]
FIB 关系的方向被对称化是新的动力学选择。给实势 \(V_i\)、三次系数 \(g_i\) 和耦合尺度 \(\kappa>0\)，Hamiltonian 与离散 NLS/Gross–Pitaevskii 方程为
\[
\mathcal H(\psi)
=\kappa\sum_{\{i,j\}}w_{ij}|\psi_i-\psi_j|^2
+\sum_im_iV_i|\psi_i|^2
+\frac12\sum_im_ig_i|\psi_i|^4,
\tag{126.2}
\]
\[
\mathrm i\dot\psi_i
=\kappa(L\psi)_i+V_i\psi_i+g_i|\psi_i|^2\psi_i.
\tag{126.3}
\]
整体相位对称性给出质量守恒
\[
\mathcal N(\psi)=\sum_im_i|\psi_i|^2,
\qquad
\frac{\mathrm d\mathcal N}{\mathrm dt}=0,
\qquad
\frac{\mathrm d\mathcal H}{\mathrm dt}=0.
\tag{126.4}
\]
这些守恒量依赖自伴图拉普拉斯和实系数，FIB 计数矩阵不承担其证明。

驻波 \(\psi_i(t)=e^{-\mathrm i\omega t}\phi_i\) 满足
\[
\omega\phi_i=\kappa(L\phi)_i+V_i\phi_i+g_i|\phi_i|^2\phi_i.
\tag{126.5}
\]
其存在、局域化和孤子形状由边权、势、非线性和边界决定。对驻波作 Bogoliubov 线性化，得到每个图谱模态的有限维块；若某块存在正实部特征值，则产生调制不稳定。均匀正则图上，线性增长率依赖 \(L\) 的特征值、背景幅度和 \(g\)，改变同一 FIB 图的边权即可在稳定、呼吸子和不稳定区间之间切换。

若另加图列嵌入与尺度，使 \(L\) 收敛到 \(-\Delta\)，并同步缩放 \(\kappa,V,g,m\)，才可得到连续 Gross–Pitaevskii 或 NLS 极限。孤子、散射、崩塌与离散呼吸子的结论需分别满足维数、符号、正则性和边界假设；FIB 上下文骨架本身不指定粒子数、相互作用或物理空间。

## 127. FIB 类型与上下文图上的外加多型 SIR/SEIR、再生数与最终规模

固定有限类型集 \(I=\{1,\ldots,d\}\)，类型可保留 FIB 标签、守卫或上下文类别。另指定传播接触矩阵 \(C\)、传播概率 \(p_{ij}\)、恢复率 \(\gamma_j>0\) 和人口比例 \(n_j\)，令
\[
\beta_{ij}=p_{ij}C_{ij}/n_j,
\qquad
B=(\beta_{ij}),
\qquad
\Gamma=\operatorname{diag}(\gamma_1,\ldots,\gamma_d).
\tag{127.1}
\]
合法上下文延拓不自动成为感染接触，FIB 组成矩阵的谱半径也不自动是再生数。

多型 SIR 方程为
\[
\dot s_i=-s_i\sum_j\beta_{ij}i_j,
\qquad
\dot i_i=s_i\sum_j\beta_{ij}i_j-\gamma_i i_i,
\qquad
\dot r_i=\gamma_i i_i,
\tag{127.2}
\]
并满足 \(s_i+i_i+r_i=n_i\)。SEIR 只需另加潜伏变量 \(e_i\) 和转出率 \(\kappa_i\)。无疫情平衡附近的下一代矩阵为
\[
K=B\Gamma^{-1},
\qquad
\mathcal R_0=\rho(K).
\tag{127.3}
\]
当 \(\mathcal R_0\le1\) 时早期多型分枝近似在适用条件下灭绝；当 \(\mathcal R_0>1\) 时存在正概率大疫情。有限人口、初始感染数和类型可达性仍会改变实际灭绝概率。

在封闭人口、无出生和无免疫衰退的确定性 SIR 合同下，最终易感比例满足隐式关系
\[
s_i(\infty)
=s_i(0)\exp\!\left[
-\sum_j\frac{\beta_{ij}}{\gamma_j}
\bigl(r_j(\infty)-r_j(0)\bigr)
\right],
\tag{127.4}
\]
再结合 \(s_i(\infty)+r_i(\infty)=n_i\) 求最终规模。多型混合矩阵的非对称性使最终规模不能只由单一平均接触率确定。随机有限人群还需外加个体接触过程、抽样和观测噪声；早期分枝的灭绝率不等于整场疫情的最终规模。

本节与第99节接触过程的区别是：SIR/SEIR 具有永久移除状态，同一个体在一次疫情中至多感染一次；接触过程通常允许恢复后再次感染。感染率、恢复率、潜伏率、混合矩阵、人口解释和观测通道均为外加，FIB 递归只提供类型或上下文骨架。

## 128. FIB 上下文上的外加离散 Boltzmann 动力学与条件流体极限

固定一个合法 FIB 上下文 \(c\)，另加有限速度集 \(V=\{v_1,\ldots,v_N\}\subset\mathbb R^d\)、周期空间 \(\Omega\) 和密度 \(f_i(t,x;c)\ge0\)。速度、物理时间和空间边界均是外加结构；五种窗口标签不能直接解释为速度或碰撞频率。

对二体碰撞率 \(K^c_{ij;k\ell}\ge0\)，假设入射交换、出射交换和碰撞反演对称，并且核只在
$$
v_i+v_j=v_k+v_\ell,\qquad |v_i|^2+|v_j|^2=|v_k|^2+|v_\ell|^2
$$
时非零。定义
$$
Q_i^c(f)=\sum_{j,k,\ell}K^c_{ij;k\ell}(f_kf_\ell-f_if_j),\qquad
\partial_t f_i^\varepsilon+v_i\cdot\nabla_xf_i^\varepsilon=\varepsilon^{-1}Q_i^c(f^\varepsilon).
\tag{128.1}
$$
对 \(1,v_i,|v_i|^2/2\) 加权求和，碰撞项分别为零，因此质量、动量和动能守恒。这个结论依赖核的对称与支撑，FIB 合法拼接本身不提供这些条件。

令 \(H(f)=\int_\Omega\sum_i(f_i\log f_i-f_i)\,dx\)。对严格正解有离散 H 定理
$$
\frac{dH}{dt}=-\frac1{4\varepsilon}
\int_\Omega\sum_{i,j,k,\ell}K^c_{ij;k\ell}
(f_if_j-f_kf_\ell)\log\frac{f_if_j}{f_kf_\ell}\,dx\le0 .
\tag{128.2}
$$
耗散为零当且仅当 \(\log f\) 属于碰撞不变量空间。若该空间恰由质量、动量和能量张成，则严格正平衡为
$$
E_i=\exp(a+b\cdot v_i+\gamma |v_i|^2/2).
\tag{128.3}
$$
一维等质量弹性碰撞可能只能交换速度，导致 \(Q\equiv0\)；因此守恒律并不保证弛豫。由 \(H\) 单调只能得到熵耗散方向，不能单独推出所有初态收敛、粒子独立或唯一流体状态方程。

若另加同一守恒类上的熵耗散下界，并令 \(\varepsilon\to0\)，再证明解的紧性、关联误差消失和碰撞算子核的闭合，极限才被迫落在式(128.3)的平衡流形上；对平衡参数取矩后，才可得到相应的 Euler 或 Navier–Stokes 型闭合。Boltzmann–Grad 稀薄尺度与 \(\mathrm{Kn}\to0\) 的流体尺度是不同极限，降低密度本身不能宣称流体极限成立。

本节结论是：FIB 提供上下文索引和组合载体；碰撞概率、熵律、关联闭合与流体极限均由外加动理学合同决定。

## 129. FIB 上下文图上的外加声子网络、无序谱与热导统计

固定有限上下文集合 \(V_N\)，另声明允许机械耦合的无向边集 \(E_N\)。在顶点附加质量 \(m_i>0\)、位移 \(q_i\)、动量 \(p_i\) 和钉扎 \(\nu_i\ge0\)，在边附加对称弹簧常数 \(k_{ij}\ge0\)。若 \(B\) 是边差分矩阵、\(M=\operatorname{diag}(m_i)\)，则
$$
H_N=\frac12p^{\mathsf T}M^{-1}p+\frac12q^{\mathsf T}Kq,\qquad
K=B^{\mathsf T}\operatorname{diag}(k_e)B+\operatorname{diag}(\nu_i).
\tag{129.1}
$$
有向 FIB 接续不自动成为双向弹簧；质量、弹簧和物理位置均需另给。Hamilton 方程为 \(M\ddot q+Kq=0\)，质量归一矩阵 \(D=M^{-1/2}KM^{-1/2}\) 的特征值满足 \(D\phi_a=\omega_a^2\phi_a\)。另行量子化后，每个正频模的激发能量为 \(\hbar\omega_a\)，这一定义中的声子不等于 FIB 叶或窗口标签。

若接入左右 Langevin 热浴，摩擦矩阵为 \(\Gamma_L,\Gamma_R\)，则在线性稳定条件下的响应与传输可写为
$$
G^r(\omega)=[K-\omega^2M-i\omega(\Gamma_L+\Gamma_R)]^{-1},\qquad
\mathcal T(\omega)=4\omega^2\operatorname{tr}(\Gamma_LG^r\Gamma_R(G^r)^*).
\tag{129.2}
$$
经典双浴稳态热流为 \(I_L=(k_{\mathrm B}(T_L-T_R)/(2\pi))\int_0^\infty\mathcal T(\omega)d\omega\)。传输严格为正需要存在同时耦合两个热浴的模态；内部谱隙、局部频率或 FIB 计数都不能单独替代这一条件。

体热导率须另加物理体积 \(\Omega_N\)，并在固定无序实现后定义
$$
\kappa_{\alpha\beta}(T)=\frac1{k_{\mathrm B}T^2}
\lim_{\eta\downarrow0}\lim_{N\to\infty}\frac1{\Omega_N}
\int_0^\infty e^{-\eta t}C_{N,\alpha\beta}(t)dt .
\tag{129.3}
$$
极限次序、相关函数体积极限和绝对可积性必须单独证明。有限封闭谐振网络保留模态能量，频率隙不自动推出局域化或有限 Fourier 热导。无序局域化还需指定无序联合律、低频窗口和传输估计；Fibonacci 准周期标签不能直接套用独立随机链的定理。

本节结论是：FIB 给出机械关系的组合支撑，质量、弹性、热浴、无序和极限共同决定声子统计与热输运。

## 130. FIB 合法上下文上的随机保边、分枝阈值与巨分量

固定有限 FIB 上下文图 \(G_N=(V_N,E_N)\)，不合法边恒不存在；对合法边 \(e\) 另加独立保留变量 \(\xi_e\)，其概率为 \(p_e\)。独立性、顶点供应和共同实现都是外加假设。最大分量 \(L_1\) 与平均簇大小
$$
\chi_N=\frac1{|V_N|}\sum_{C\in\operatorname{Comp}(H_N)}|C|^2
\tag{130.1}
$$
是不同观测；有限图中一个大分量也不等于无界尺寸巨分量。

对完整合法窗口前缀树，若接缝类型为 \(0,1\)，其平均续接矩阵可取
$$
T=\begin{pmatrix}3&2\\2&1\end{pmatrix},\qquad
\rho(T)=\varphi^3,\qquad \varphi=\frac{1+\sqrt5}{2}.
\tag{130.2}
$$
逐边以概率 \(p\) 保留并保持不同前缀为不同个体时，分枝矩阵为 \(pT\)。于是无限前缀树的根簇在 \(p\varphi^3>1\) 时具有正无限存活概率，在 \(p\varphi^3\le1\) 时几乎必然有限。该结论针对多型分枝过程；把相同接缝的不同前缀合并会改变过程。

有限稀疏随机图中，若类型比例为 \(\pi_a\)，类型间稀疏连接矩阵为 \(K_{ab}(c)=c\ell_{ab}\kappa_{ab}\pi_b\)，则存活向量满足
$$
r_a=1-\exp\!\left(-\sum_bK_{ab}(c)r_b\right).
\tag{130.3}
$$
在不可约、独立稀疏配对和共同实现条件下，\(\rho(K(c))>1\) 给出唯一巨分量，其顶点比例趋于 \(\sum_a\pi_ar_a\)；\(\rho(K(c))\le1\) 时最大分量比例趋零。谱半径判据依赖顶点供应和配对模型，不能由有限前缀树阈值直接替代。非回溯矩阵的小于一只给出路径和的上界；树、稠密小团和循环图说明其反向蕴含不成立。

本节结论是：FIB 可以提供随机图的合法支撑与类型矩阵，保边律、分枝独立性、顶点比例和巨分量极限必须外加。

## 131. FIB 上下文图上的外加运输曲率、扩散收缩与几何统计

取有限实际 FIB 对象集 \(V\)，在合法局部替换关系上构造连通无向分析图。无向化只用于分析，不授予原操作反向执行权限。给边长度 \(\ell_{xy}>0\)，以最短路定义度量 \(d\)。再附加顶点质量 \(m_x>0\) 与对称导通量 \(c_{xy}\)，令
$$
P(x,y)=\begin{cases}c_{xy}/(bm_x),&x\ne y,\\
1-\sum_{z\ne x}c_{xz}/(bm_x),&x=y,\end{cases}
\tag{131.1}
$$
其中 \(b\) 足够大使 \(P\) 非负。平稳律为 \(\pi_x=m_x/\sum_ym_y\)，并满足详细平衡；连续时间生成元为 \(\mathcal A=b(P-I)\)，半群为 \(H_t=e^{t\mathcal A}\)。扩散步数、FIB 替换代数和查询费用是不同指标。

Ollivier 曲率定义为
$$
\kappa_P(x,y)=1-\frac{W_{1,d}(P_x,P_y)}{d(x,y)},\qquad P_x=P(x,\cdot).
\tag{131.2}
$$
它取决于完整后继概率和运输成本。另定义
$$
\Gamma(f,g)(x)=\frac12\sum_y\frac{c_{xy}}{m_x}(f(y)-f(x))(g(y)-g(x)),\quad
\Gamma_2(f)=\frac12\mathcal A\Gamma(f)-\Gamma(f,\mathcal Af).
\tag{131.3}
$$
若 \(CD(K,\infty)\) 成立，即 \(\Gamma_2(f)\ge K\Gamma(f)\)，则有能量收缩 \(\Gamma(H_tf)\le e^{-2Kt}H_t\Gamma(f)\)；若所有边的运输曲率下界为 \(\kappa_*>0\)，则
$$
W_{1,d}(\mu H_t,\nu H_t)\le e^{-b\kappa_*t}W_{1,d}(\mu,\nu).
\tag{131.4}
$$
运输曲率与能量曲率不是同一判据。有限可逆图上 \(CD(K,\infty)\) 还给出谱隙至少为 \(K\)。在平稳初态下，时间平均满足
$$
\operatorname{Var}(\overline f_T)\le\frac{2\operatorname{Var}_\pi(f)}{\lambda_1T},
\tag{131.5}
$$
并在固定有限模型中具有相应中心极限定理；图规模与采样时间同时增长时须重新控制相关时间。连续图极限需要状态对应、时间重标、生成元收敛和紧性，Fibonacci 增长率不能单独决定扩散维数。

本节结论是：FIB 提供可承载度量和核的关系图，曲率、混合、中心极限及尺度极限均由外加几何和概率结构决定。

## 132. FIB 类型与上下文上的外加受激发射、随机激光与光子统计

沿用五窗类型集 \(\Sigma=\{000,100,010,101,001\}\)，在有限介质图上附加每类发射体数 \(N_a\)、泵浦率 \(P_a\)、弛豫率 \(\gamma_a\)、受激发射率 \(g_a\)、吸收率 \(h_a\) 和腔损耗 \(\kappa\)。标签可以索引这些参数，但窗口读数与 Fibonacci 增长率不自动成为能级、频率或增益。

若完整状态为光子数 \(n\) 与激发数 \(k_a\)，典型联合跃迁包括
$$
\begin{array}{c|c}
\text{事件}&\text{速率}\\ \hline
\text{泵浦 }k_a\to k_a+1&P_a(N_a-k_a)\\
\text{非选定模弛豫}&\gamma_ak_a\\
\text{选定模发射 }(n,k_a)\to(n+1,k_a-1)&g_ak_a(n+1)\\
\text{吸收}&h_a(N_a-k_a)n\\
\text{损耗}&\kappa n .
\end{array}
\tag{132.1}
$$
平均光子收支含有 \(\mathbb E[k_an]\)，因此两份边缘分布不能完成闭合。若另加有效饱和 birth–death 模型
$$
b_n=\frac{G(n+1)}{1+n/n_s},\qquad d_n=\kappa n,\qquad r=G/\kappa,
\tag{132.2}
$$
则存在唯一平稳概率
$$
\pi_n=\frac1Z\frac{r^n}{\prod_{j=0}^{n-1}(1+j/n_s)}.
\tag{132.3}
$$
有限 \(n_s\) 时稳态随 \(r\) 平滑变化；连续平均场的正强度平衡 \(I=n_s(r-1)\) 只是有效近似。撤去饱和后，几何稳态仅在 \(r<1\) 可归一化，因此小信号增益阈值、有限饱和稳态和相干性阈值是三种不同判据。

随机反馈需另加无序输运矩阵 \(A_\xi\)。去掉自发源后的线性强度方程 \(\dot I=A_\xi I\) 以谱横坐标给出增长条件；阈值由
$$
s(A_\xi)=\max_{\lambda\in\operatorname{spec}(A_\xi)}\operatorname{Re}\lambda=0
\tag{132.4}
$$
确定。局部增益、散射反馈和边界逃逸缺一不可，FIB 类型计数不能替代它们。未饱和几何分布给 \(g^{(2)}(0)=2\)，Poisson 分布给 \(g^{(2)}(0)=1\)；跨过小信号阈值不自动得到 Poisson 统计，探测过程还会改变观测到的相关函数。

本节结论是：FIB 提供介质类型和上下文索引；泵浦、发射、损耗、散射、相位与探测协议共同决定随机激光阈值和光子统计。

## 133. FIB 合法上下文上的外加首达渗流、时间常数与测地线涨落

固定长度 \(r\) 的 FIB 上下文状态集 \(S_r\)，把每个合法窗口接续展开为分层有向图。边时间场 \(\{\tau_e\}\) 是新的随机输入；同一条路径上的边时间读取同一个环境。对可达端点定义
$$
T_\omega(x,y)=\min_{\gamma:x\to y}\sum_{e\in\gamma}\tau_e(\omega).
\tag{133.1}
$$
它是首达渗流的路径耗时，与随机游走的吸收时间不同。有限层数时路径有限，最小值存在；若边时间可为零，应明确保留全部并列测地线。

假设环境在某个层平移下平稳遍历，存在一条可重复的闭上下文游走，且其连接耗时可积。次可加性
$$
T(x_0,x_{n+m})\le T(x_0,x_n)+T(x_n,x_{n+m})
$$
与次可加遍历定理给出确定时间常数
$$
\mu=\lim_{n\to\infty}\frac{T(x_0,x_n)}n
=\inf_{n\ge1}\frac{\mathbb E T(x_0,x_n)}n
$$
（几乎处处及在 \(L^1\) 中）。平稳性、遍历性和可积连接是极限条件；FIB 接缝本身不提供它们。

即使边时间边缘均值相同，联合律也能改变 \(\mu\)。恒定边时间为一时，\(\mu=1\)。各边独立且以相等概率取 \(0,2\) 时，三条候选边的层间最小值均值为 \(1/4\)，从而时间常数可严格小于一。若每层三条边共享同一个随机时钟，边缘分布仍为 \(0,2\)，但所有跨层路径费用相同，时间常数恢复为一。故边缘分布不能替代跨边相关结构和允许路径集合。

固定状态宽度只允许有限横向状态。若给状态指定有界横坐标，则任意测地线横偏有统一上界，不能产生随层数增长的二维 \(N^{2/3}\) 横向涨落。要讨论 KPZ 型指数，必须另加无界空间坐标、平移作用、边时间短程联合律、端点和边界，并证明相应形状定理与测地线唯一性。即使提出
$$
\operatorname{sd}(T_N)=N^{1/3+o(1)},\qquad
W_N=N^{2/3+o(1)},
$$
这些也只是扩展模型的待证标度，不能由 Fibonacci 增长率或上下文计数推出。

本节结论是：FIB 提供可行路径的组合支撑；首达速度、时间常数、涨落指数和测地线几何由外加边时间场、相关结构与空间嵌入决定。

## 134. FIB 类型与接缝上的守恒粒子、零程过程和凝聚

取满足接缝守卫的周期类型序列 \(s_1,\ldots,s_L\)，在站点 \(i\) 上附加无界粒子数 \(n_i\in\mathbb N_0\)，总数 \(N=\sum_i n_i\)。粒子是新增模型对象，不等同于 FIB 位值或窗口组成。给不可约路由矩阵 \(P=(p_{ij})\)，站点 \(i\) 有 \(n\) 粒子时以总速率 \(u_i(n)\) 移出一粒并按 \(P\) 选目标：
$$
\mathcal Lh(n)=\sum_{i,j}u_i(n_i)p_{ij}
\bigl[h(n-e_i+e_j)-h(n)\bigr].
\tag{134.1}
$$
这里 \(u_i(0)=0\)，且 \(u_i(n)>0\)；若迁移率依赖目标占用或改变接缝，需改写过程。

取正流量向量 \(v_j=\sum_i v_ip_{ij}\)，定义
$$
w_i(0)=1,\qquad
w_i(n)=\frac{v_i^n}{\prod_{k=1}^n u_i(k)}.
$$
固定总粒子数的平稳分布为
$$
\pi_{L,N}(n)=\frac{\mathbf1_{\{\sum_i n_i=N\}}}{Z_{L,N}}
\prod_iw_i(n_i).
\tag{134.2}
$$
乘积形式只需流量平衡，不要求详细平衡；相同平稳分布仍可能对应不同稳态循环流。

在类型比例趋于 \(q_a>0\) 的热力学极限中，令
$$
F_a(z)=\sum_{n\ge0}w_a(n)z^n,\qquad
\rho(z)=\sum_aq_a\frac{zF_a'(z)}{F_a(z)},\qquad
\rho_c=\lim_{z\uparrow z_c}\rho(z).
\tag{134.3}
$$
若 \(\rho_c<\infty\)，超出临界背景密度的质量可能凝聚到单个站点；对 \(u(n)=1+b/n\)、\(b>2\) 的齐次模型，\(\rho_c=1/(b-2)\)，当 \(N/L\to\rho>\rho_c\) 时最大占用满足
$$
\frac{M_L}{L}\xrightarrow{\mathbb P}\rho-\rho_c.
\tag{134.4}
$$
这依赖无界占用、速率尾部和 \(L\to\infty\)；固定有限 \(L\) 的大峰不是热力学相变证据。只记录类型频数和总粒子数，不能区分同一类型内部的集中与均匀分布。

本节结论是：FIB 提供站点类型和接缝载体；守恒粒子、迁移率、容量和凝聚阈值均由外加零程动力学决定。

## 135. FIB 随机导通网络上的外加均匀化与有效扩散

FIB 合法图若要讨论空间均匀化，必须另加空间嵌入、边导通 \(c_{xy}=c_{yx}>0\) 和顶点容量 \(m_x>0\)。固定静态环境时定义
$$
(Ku)(x)=\sum_{y\sim x}c_{xy}[u(y)-u(x)],\qquad
L=m^{-1}K.
\tag{135.1}
$$
扩散尺度采用空间 \(x\mapsto\varepsilon x\) 和时间 \(t\mapsto\varepsilon^{-2}t\)，得到离散椭圆或抛物方程。导通决定通量，容量决定时间尺度；FIB 计数和词长不自动具有物理长度或体积量纲。

若几何、导通和容量的联合环境平稳遍历，网络具有所需连通性、统一椭圆界和区域紧性，并且边界与初值可逼近连续对象，则可得到
$$
-\nabla\cdot(A_{\mathrm{hom}}\nabla u)=f,\qquad
\bar m\,\partial_tu=\nabla\cdot(A_{\mathrm{hom}}\nabla u),
\tag{135.2}
$$
其中 \(A_{\mathrm{hom}}\) 是整个网络的变分有效导通张量，\(D_{\mathrm{hom}}=A_{\mathrm{hom}}/\bar m\) 是有效扩散张量。它通常不能由导通系数的算术平均替代，因为微观校正势会重分配通量。

准周期背景需要指定替换规则及其平移 hull；它可由唯一遍历律产生平均，但不等同于独立随机介质。独立无序仍须满足统一椭圆或可控退化条件；低导通重尾会使一维有效扩散退化。相关无序的有限相关长度不是均匀化存在的普遍必要条件，却影响收敛速率和涨落。非遍历环境的有效张量可能依赖遍历分量。

本节结论是：FIB 只提供关系图和可允许的组合支撑；均匀化极限还需要空间几何、导通律、容量、遍历性、边界和紧性。

## 136. FIB 词序与上下文读出的相关极值、簇点过程与极值指数

令 \(X=(X_i)_{i\in\mathbb Z}\) 是平稳词源，\(Z_i\) 是外加上下文，定义窗口读出
$$
Y_{i,n}=\Psi_n(X_i,\ldots,X_{i+m_n-1},Z_i),\qquad
M_n=\max_{1\le i\le n}Y_{i,n}.
\tag{136.1}
$$
Fibonacci 替换语言与仅满足局部接缝守卫的扩展语言是不同来源；极值结论必须指定其中之一及其概率律。

取超阈事件 \(E_{i,n}=\{Y_{i,n}>u_n\}\)，令 \(p_n=\Pr(E_{0,n})\)，并设 \(np_n\to\tau\in(0,\infty)\)。边缘尾部决定归一化和尾形指数 \(\xi\)，而局部重复决定极值指数 \(\theta\)。若存在块长 \(r_n\)、间隔 \(\ell_n\) 满足
$$
\ell_n=o(r_n),\qquad r_n=o(n),\qquad r_np_n\to0,
$$
且实际超阈过程的混合误差满足 \(k_n\alpha_n(\ell_n)\to0\)，并令
$$
\theta_n=\frac{\Pr(\cup_{i=1}^{r_n}E_{i,n})}{r_np_n}\longrightarrow\theta,
\tag{136.2}
$$
则
$$
\Pr(M_n\le u_n)\longrightarrow e^{-\theta\tau}.
\tag{136.3}
$$
\(\theta=1\) 表示无聚簇损失；\(\theta<1\) 表示同一局部簇内出现多个超阈读出。

更强地，若块内超阈数在非空条件下收敛到正整数簇大小 \(K\)，并具有一致可积性，则极值点过程是复合 Poisson：
$$
\mathcal N=\sum_jK_j\delta_{T_j},
$$
簇中心是 Poisson，原始超阈次数只有在 \(K=1\) 时才是普通 Poisson。重叠窗口可在底层字母无关时制造局部簇；远距相关则可能破坏上述分块极限。

相同五窗频数和相同边缘尾部不能识别极值行为。两种词序可有完全相同的类型频率，却分别禁止或允许高值模式的重叠，从而具有不同 \(\theta\) 和不同最大值分布。固定有限窗口且读出值域有限时，最大值最终只会达到上界，非退化极值律需要增长窗口、移动阈值或无界上下文。

本节结论是：FIB 规定词序和合法局部模式；尾部、混合性、重叠结构和簇大小由外加随机读出决定。

## 137. FIB 递归观察序列上的传递熵、隐藏状态与因果边界

令递归骨架满足
$$
F_{t+1}=F_t+F_{t-1},
$$
并加入外部隐藏状态 \(H_t\)，联合状态为 \(S_t=(F_t,F_{t-1},H_t)\)。观察过程为 \(X_t=g_X(S_t,\eta_t^X)\)、\(Y_t=g_Y(S_t,\eta_t^Y)\)。给定有限历史 \(X_t^{(k)}\)、\(Y_t^{(\ell)}\) 和条件历史 \(Z_t^{(m)}\)，传递熵定义为条件互信息
$$
T_{Y\to X\mid Z}
=I\!\left(X_{t+1};Y_t^{(\ell)}\mid X_t^{(k)},Z_t^{(m)}\right).
\tag{137.1}
$$
它衡量源历史对目标下一步预测不确定性的减少，不自动等同于干预效应。

完整无噪声递归状态满足
$$
H(F_{t+1}\mid F_t,F_{t-1})=0.
$$
因此在已知完整 FIB 递归状态后，传递熵只有在源改变隐藏状态转移、观测噪声或外部输入时才可能非零。滤除递归骨架、取残差或取模运算都是新的观测合同，不能把变换前后的互信息直接视为同一量。

若给定条件历史时存在马尔可夫链 \(Y_t^-\to S_t\to X_{t+1}\)，条件数据处理不等式给出
$$
I(X_{t+1};Y_t^-\mid Q_t)
\le I(X_{t+1};S_t\mid Q_t).
\tag{137.2}
$$
共同原因 \(C_t\) 同时影响 \(Y_t\) 与 \(X_{t+1}\) 时，未条件化传递熵可以为正；把 \(C_t^-\) 加入条件集可消除该混淆，但条件化中介或碰撞点又可能切断真实效应或制造虚假依赖。故非零传递熵至多是条件预测证据，不能单独证明因果边；零传递熵也不能证明不存在因果作用。

总体传递熵在平稳、遍历和足够混合时是观测分布的函数。隐藏状态识别还需发射分布可区分、激励充分及噪声模型受限，通常只能在状态标签置换下识别。有限样本估计受历史阶数、稀疏联合格点、量化、带宽和非平稳漂移影响；随机打乱源序列会破坏时间结构，不能替代按时间块的保留自相关检验。

本节结论是：FIB 递归可作为共同历史和状态坐标；信息流、隐藏状态可识别性与因果解释均依赖外加转移核、观测通道和干预假设。

## 138. FIB 上下文图上的外加主动布朗动力学与 MIPS

将 FIB 上下文图记为 \(\mathcal G=(V,E,w,C)\)，其中 \(E\) 是允许转移，\(C\) 是另行声明的接触算子或接触超边。语义相邻不自动表示物理接触。粒子还需附加位置、推进方向和排斥势；没有空间嵌入时，空间导数改用图差分和节点转向核。

单粒子主动布朗动力学可写成
$$
\dot x_i=v_0g(C\rho)\mathbf n_i-\mu\nabla_iU+\sqrt{2D_t}\,\xi_i,
\qquad
\dot\theta_i=\sqrt{2D_r}\,\eta_i ,
\tag{138.1}
$$
其中 \(v_0\) 是自由推进速度，\(D_t,D_r\) 是平移和转动扩散，\(g(0)=1\)、\(g'(\rho)<0\) 表示拥挤导致推进减慢。节点处须另加守恒的 Kirchhoff 通量匹配和方向转移核。持续时间与持续长度为
$$
\tau_R=D_r^{-1},\qquad \ell_p=v_0\tau_R,
$$
主要无量纲量包括 \(\mathrm{Pe}_R=\ell_p/\sigma\)、\(\mathrm{Pe}_T=v_0\sigma/D_t\)、占据率以及节点转向率与 \(D_r\) 的比值。

在局部各向同性、密度变化尺度大于 \(\ell_p\)、取向一阶矩可消去的条件下，粗粒密度满足
$$
\partial_t\rho
=\nabla_{\mathcal G}\cdot\left[
D_t\nabla_{\mathcal G}\rho+
\frac{v(\rho)}{dD_r}\nabla_{\mathcal G}(v(\rho)\rho)
\right].
\tag{138.2}
$$
均匀态 \(\rho_0\) 对某个非零图模失稳的充分判据是
$$
D_{\mathrm{eff}}(\rho_0)
=D_t+\frac{v(\rho_0)}{dD_r}
\bigl(v(\rho_0)+\rho_0v'(\rho_0)\bigr)<0.
\tag{138.3}
$$
这可改写为
\(\frac{d\log v}{d\log\rho}|_{\rho_0}<-1-dD_tD_r/v(\rho_0)^2\)。它是持续自推进和接触阻塞导致主动团簇化的长波条件；两相密度、界面宽度和团簇比例仍需完整接触核。

有限 FIB 图只产生有限团簇、双稳态或亚稳态，不能独自定义热力学相变。连续极限还需图族的最大边长趋零、图 Laplace 收敛、节点转向收敛及接触算子收敛；若图谱隙、瓶颈或边长与 \(\ell_p\) 同阶，局部连续判据可能失效。

本节结论是：FIB 提供主动粒子可用的关系和接触载体；持续推进、转动噪声、拥挤反馈和相分离阈值均由外加模型决定。

## 139. FIB 类型与接缝上的化学主方程、守恒量和熵产生

设完整化学状态为 \(z=(n,\eta)\)，其中 \(n\in\mathbb N^d\) 是各物种数量，\(\eta\) 保留排列、接缝和控制态。反应通道只在 FIB 合法域中启用；令 \(q(z,z')\) 为总跳率，则
$$
Lf(z)=\sum_{z'\ne z}q(z,z')[f(z')-f(z)],
$$
$$
\dot p_t(z)=\sum_{z'\ne z}
[p_t(z')q(z',z)-p_t(z)q(z,z')].
\tag{139.1}
$$
无限状态空间还需非爆炸条件。

只保留数量 \(n\) 后，过程仍为 Markov 的必要充分条件是强可聚合性：同一数量纤维中的任意两个完整状态 \(z,\tilde z\)，对每个目标数量 \(m\) 都满足
$$
\sum_{n(z')=m}q(z,z')
=\sum_{n(z')=m}q(\tilde z,z').
\tag{139.2}
$$
若合法排列改变局部反应机会，这个条件通常失败；数量和端口读数不能代替接缝关系。

数量闭合且充分混合时，反应 \(y_r\to y'_r\) 的质量作用速率可取
$$
\lambda_r^\Omega(n)=\kappa_r\Omega^{1-|y_r|}
\prod_i(n_i)_{y_{ri}}.
\tag{139.3}
$$
若化学计量矩阵 \(S\) 满足 \(\ell^{\mathsf T}S=0\)，则 \(\ell^{\mathsf T}n\) 是逐路径守恒量。若网络存在正复平衡点 \(c_*\)，且可达类有限、闭合并不可约，则该类的平稳分布为独立 Poisson 律在可达类上的条件化：
$$
\pi_\Gamma^\Omega(n)=\frac1{Z_\Gamma}
\prod_i\frac{(\Omega c_{*i})^{n_i}}{n_i!},
\qquad n\in\Gamma.
\tag{139.4}
$$
接缝禁配或隐藏排列会改变生成元时，必须重新核对该结论。

系统尺寸极限 \(x=n/\Omega\) 在相应紧性和正则性下满足
$$
\dot x=\sum_r\nu_ra_r(x),
\qquad
H(x,p)=\sum_ra_r(x)(e^{p\cdot\nu_r}-1),
\tag{139.5}
$$
其中 \(H\) 是路径大偏差 Hamiltonian。单站数量的平均方程不决定稀有路径代价；接缝引起的相关必须保留在联合状态中。

对有向反应通道 \(e\) 与反向通道 \(\bar e\)，概率流 \(u_e=p_t(z)q_e(z,z')\) 给出总熵产生
$$
\dot S_{\mathrm{tot}}
=\frac{k_{\mathrm B}}2\sum_e
(u_e-u_{\bar e})\log\frac{u_e}{u_{\bar e}}\ge0.
\tag{139.6}
$$
平稳分布可以伴随持续环流和正熵产生；复平衡不等于逐通道详细平衡。只有另加温度、能量和化学势，才可将熵产生解释为物理热和环境熵流。

本节结论是：FIB 提供化学反应可用的类型和接缝语法；反应速率、守恒量、平稳律、大偏差和耗散均由外加 Markov 合同决定。

## 140. FIB 合法图上的外加 Anderson 局域化与输运衰减

FIB 接缝首先确定允许路径；单条合法无限链、全部合法前缀树和有限状态图是不同空间模型。选定无向图 \(X\) 后，外加紧束缚算子为
$$
(H_\omega\psi)(x)=
\sum_{y\sim x}t_{xy}\psi(y)
+[v(x)+\lambda\omega_x]\psi(x),
\qquad t_{yx}=\overline{t_{xy}}.
\tag{140.1}
$$
随机位势的独立性或准周期性必须分别声明。

谱集合、谱型和传输是不同对象。有限样本中的集中本征向量不能单独证明无限系统的 Anderson 局域化。对恒定跃迁的一维链，
$$
\binom{\psi_{n+1}}{\psi_n}
=
\begin{pmatrix}
(E-V_n)/t&-1\\1&0
\end{pmatrix}
\binom{\psi_n}{\psi_{n-1}},
$$
在平稳遍历和对数可积条件下，Lyapunov 指数为
$$
\gamma(E)=\lim_{N\to\infty}
\frac1N\log\|A_N(E)\cdots A_1(E)\|.
\tag{140.2}
$$
在非退化接触下，典型透射满足
\(\mathcal T_N(E)=e^{-2\gamma(E)N+o(N)}\)；平均透射还可能受到稀有共振影响。禁带中的 \(\gamma>0\) 是倏逝衰减，不能单独判定 Anderson 局域化。

标准一维独立非退化无序通常产生正 Lyapunov 指数和指数局域化。相反，沿合法序列嵌入的 Fibonacci 准周期势可以具有零 Lebesgue 测度的奇异连续谱与临界输运；\(\gamma=0\) 既不等于指数局域化，也不自动等于弹道传播。两者的差异来自势的联合律与空间组织，而非来自是否使用同一组窗口标签。

全部合法前缀树的分支矩阵可取
$$
B=\begin{pmatrix}3&2\\2&1\end{pmatrix},
\qquad \rho(B)=2+\sqrt5=\varphi^3.
\tag{140.3}
$$
树上单射线的衰减必须与壳层顶点数共同比较。对有界独立无序，若分数矩估计给出
$$
\mathbb E|G_\omega(x,y;E+i\eta)|^s
\le Cq_s^{d(x,y)},\qquad q_s\rho(B)<1,
\tag{140.4}
$$
则强无序下的指数衰减能够压过分支增长，构成纯点谱和指数局域化的充分条件；这不是精确临界强度。

本节结论是：FIB 决定允许路径和分支几何，Lyapunov 指数、谱型和输运衰减由外加跃迁、势的概率律及空间图决定。

## 141. FIB 递归观察下的外扰响应、涨落耗散与逆响应识别

FIB 来源生成、观察协议和外场耦合必须分别声明。令完整状态 \(Z_n\) 含来源、游标、记忆和协议状态，并假定转移算子对外场 \(h\) 可微：
$$
P_{n,h}=P_n+h_nV_n+o(h_n),\qquad V_n\mathbf1=0.
$$
对不直接依赖外场的末端读数 \(A\)，一阶响应核为
$$
\delta\mathbb E[A(Z_n)]
=\sum_{k<n}h_kR(n,k)+o(\|h\|),
$$
$$
R(n,k)=\mu_kV_kP_{k+1}\cdots P_{n-1}A.
\tag{141.1}
$$
初态或仪器随外场变化时需加入相应导数；无平稳性时响应一般依赖两个时刻。

连续时间中 \(L_h=L+h(t)V+o(h)\)，未扰动平稳态为 \(\pi\) 时，
$$
R_{AB}(t)=\mathbf1_{t\ge0}\langle Ve^{tL}A\rangle_\pi.
\tag{141.2}
$$
若系统具有 Gibbs 平衡态、外场按 \(H_h=H_0-hB\) 耦合，且动力学对平衡族满足详细平衡，则
$$
R_{AB}(t)
=-\beta\mathbf1_{t\ge0}\frac{d}{dt}
\operatorname{Cov}_\pi(B(0),A(t)).
\tag{141.3}
$$
相关积分收敛并且极限次序明确时，输运系数可写成 Green–Kubo 形式
$$
L_{ij}=\beta\int_0^\infty
\operatorname{Cov}_\pi(J_i(t),J_j(0))\,dt.
\tag{141.4}
$$
平稳性本身不能保证积分收敛；持续相关和慢尾部可能使直流系数不存在。

代数矩阵可逆不等于 FIB 来源操作合法可逆。组成矩阵
$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}
$$
虽有 \(\det M=-1\)，却可能把非负组成域映到域外。概率动力学的时间反演还需检查详细平衡和动量、磁场等反演规则。

逆响应的识别也有条件。在线性实现
$$
z_{n+1}=Az_n+Bh_n,\qquad y_n=Cz_n,
$$
响应序列为 \(R_\ell=CA^{\ell-1}B\)。有限维、无噪声且可控可观时，它至多确定最小实现的相似类；不可达或不可见状态不留下响应痕迹。输出反推外场还需要稳定因果左逆，延迟、非最小相位零点和噪声放大都可能阻断它。

相同未扰动协方差不保证相同响应：模型 \(dX_t=-\lambda X_tdt+\sqrt{2D}\,dW_t+gh(t)dt\) 对不同 \(g\) 有相同无扰路径律，却有不同响应 \(ge^{-\lambda t}\)。因此涨落、可逆性和响应耦合必须分别校准。FIB 组成观察还会遗忘树的左右顺序；若干预和读出都因子化到组成商，不断增加组成层数也不能恢复被遗忘结构。

本节结论是：FIB 提供可被扰动和观察的递归载体；响应核、涨落耗散和逆响应可识别性依赖外加平衡、耦合、初态和仪器合同。

## 142. FIB 路径约束上的外加 Schrödinger 桥与随机控制

令 \(\Omega\) 为路径空间，\(e_0,e_T\) 为端点映射，\(R\) 为参考路径律。把 FIB 允许路径记为 \(\mathcal F\subset\Omega\)，其端点支撑为
$$
E_{\mathcal F}=\{(e_0(\omega),e_T(\omega)):\omega\in\mathcal F\}.
$$
给定端点分布 \(\mu_0,\mu_T\)，FIB 约束下的可行类为
$$
\mathcal A_{\mathcal F}
=\{P\ll R:P(\mathcal F)=1,\ e_{0\#}P=\mu_0,\ e_{T\#}P=\mu_T\}.
\tag{142.1}
$$
Schrödinger 桥定义为
$$
\min_{P\in\mathcal A_{\mathcal F}}D_{\mathrm{KL}}(P\|R).
\tag{142.2}
$$

若路径空间具有紧性、可行类非空并含有限 KL 元素、成本下半连续，且受限参考律在允许支撑上严格正并满足连通性，则最优解存在；KL 的严格凸性给出唯一最优路径律。若 FIB 约束端点可测，最优律具有
$$
\frac{dP^*}{dR_{\mathcal F}}
=f(X_0)g(X_T),
\tag{142.3}
$$
其中势函数只在 \(f\mapsto cf,\ g\mapsto c^{-1}g\) 的规范变换下不唯一。支撑不连通时，各连通分量还可能有独立规范。

熵正则最优传输可写成
$$
\min_{\pi\in\Pi(\mu_0,\mu_T),\ \pi(E_{\mathcal F})=1}
\left[\int c\,d\pi+\varepsilon
D_{\mathrm{KL}}(\pi\|K_{\mathcal F})\right].
\tag{142.4}
$$
若参考扩散受漂移控制
$$
dX_t=b(X_t)dt+\sigma(X_t)(u_tdt+dW_t),
$$
则在适用的 Girsanov 条件下，相对熵转为控制能量
$$
D_{\mathrm{KL}}(P^u\|R)
=\frac12\mathbb E\int_0^T|u_t|^2dt.
\tag{142.5}
$$
这把路径约束的熵最小化与带端点分布的随机控制联系起来。

相同端点观测不保证相同隐藏路径成本。只有当 FIB 支撑、参考条件律和成本都能因子化到观测商时，路径问题与观测问题才等价。若 \(R(\mathcal F)=0\)，标准 KL 问题没有有限值；若 \(\mathcal F\) 不是端点可测集合，端点约束只是必要条件，不能替代整条路径约束。令 \(\varepsilon\to0\) 后严格凸性可能消失，唯一性也不再由 FIB 保证。

本节结论是：FIB 提供允许路径的硬支撑，参考概率、端点分布、成本、熵系数和控制动力学均需外加；桥接律与控制律是这些条件共同作用的结果。

## 143. FIB 上下文图上的外加 Kramers 逃逸与亚稳态

固定长度 \(r\) 的 FIB 上下文图只给出允许接续。若另行授权双向操作，在无向连通图上附加势 \(U_i\)、对称边势垒 \(H_{ij}=H_{ji}\)、权重 \(m_i>0\) 和噪声尺度 \(\varepsilon\)，定义
$$
q_{ij}^{\varepsilon}
=\frac{a_{ij}}{m_i}
e^{-(H_{ij}-U_i)/\varepsilon},
\qquad
(L_\varepsilon f)_i
=\sum_{j\ne i}q_{ij}^{\varepsilon}(f_j-f_i).
\tag{143.1}
$$
其平稳分布与边电导为
$$
\pi_i^\varepsilon=Z_\varepsilon^{-1}m_i e^{-U_i/\varepsilon},
\qquad
c_{ij}^\varepsilon
=Z_\varepsilon^{-1}a_{ij}e^{-H_{ij}/\varepsilon}.
\tag{143.2}
$$
原始有向 FIB 图不能直接套用此详细平衡模型；未授权边的速率必须为零。

对候选势阱 \(W\)，杀死生成元的主特征对满足
$$
\alpha_WQ_W=-\lambda_W\alpha_W,
\qquad
\Pr_{\alpha_W}(\tau_W>t)=e^{-\lambda_Wt}.
\tag{143.3}
$$
因此从准稳分布出发的离井时间是指数律，平均寿命为 \(1/\lambda_W\)。亚稳态要求井内松弛远快于逃逸；准稳分布一般不等于 Gibbs 分布在井内的简单条件化。

定义从 \(a\) 到目标集合 \(B\) 的通达高度
$$
\Phi(a,B)=\min_{\gamma:a\leadsto B}\max_{e\in\gamma}H_e.
\tag{143.4}
$$
在固定有限图、容量前因子不具指数贡献及其他陷阱已控制的条件下，
$$
\varepsilon\log\mathbb E_a\tau_B
\longrightarrow\Phi(a,B)-U_a.
\tag{143.5}
$$
这说明逃逸由势阱质量和出口瓶颈共同决定，不能只比较起点与终点势差。若空间极限另行校准为梯度扩散、井极小点和鞍点非退化且主出口唯一，才可得到 Eyring–Kramers 型前因子；多出口、退化鞍点和非梯度漂移须重新分析。

固定正噪声的有限不可约图只有一个平稳分布，亚稳态只是长寿命暂态。图规模与 \(\varepsilon\to0\) 的联合极限可能让通道数和权重贡献指数阶，不能先用固定图公式再无条件取极限。静态随机势垒还须先固定实现；对实现平均后的存活率一般是多个指数的混合，而非单指数。

本节结论是：FIB 提供可行跃迁图，势垒、噪声、时间尺度和准稳统计均由外加随机动力学决定。

## 144. FIB 类型图上的外加 Glauber 动力学、磁滞与成核

在实际无向接触图 \(G_N=(V_N,E_N)\) 上附加独立自旋 \(\sigma_i\in\{-1,+1\}\)，定义
$$
H_N(\sigma)
=-\sum_{\{i,j\}\in E_N}J_{ij}\sigma_i\sigma_j
-h\sum_i\sigma_i,
\qquad
\pi_\theta(\sigma)=Z_N^{-1}e^{-\theta H_N(\sigma)}.
\tag{144.1}
$$
类型依赖耦合 \(J_{ij}=J_{\tau_i\tau_j}\) 和接触图都是外加选择。以单点翻转率
$$
c_i(\sigma)
=\frac{a_i}{1+e^{\theta\Delta_iH}},
\qquad
\Delta_iH=2\sigma_i\left(h+\sum_jJ_{ij}\sigma_j\right)
\tag{144.2}
$$
定义连续时间 Glauber 链，则
\(\pi_\theta(\sigma)c_i(\sigma)
=\pi_\theta(\sigma^i)c_i(\sigma^i)\)。有限图上的链不可约时，Gibbs 律唯一；改变 \(a_i\) 可保留静态分布而改变驰豫。

有限系统配分函数解析，磁化双峰和长寿命不能单独证明热力学相变。无限极限须指定图序列、边界和耦合尺度。若有界度图满足
$$
\sup_i\sum_j\tanh(\theta|J_{ij}|)<1,
\tag{144.3}
$$
则 Dobrushin 条件给出 Gibbs 态唯一。相反，若另行构造分枝率为 \(\varphi\) 的铁磁树，条件 \(\varphi\tanh(\theta J)>1\) 可导致边界依赖和多 Gibbs 态；黄金率出现在这里，是因为分枝树已作为额外空间模型指定。

外场 \(h(t)\) 往返扫描时，有限速率翻转产生磁滞。若先让每段充分混合再减慢驱动，有限系统磁滞面积趋零；若先取无限体积或零温极限，混合时间可能发散，两个极限未必可交换。成核路径的能垒为
$$
\Gamma=\min_{\gamma:\sigma^-\to\sigma^+}
\max_{\eta\in\gamma}[H(\eta)-H(\sigma^-)].
\tag{144.4}
$$
在固定有限图、低温和稳定高度条件下，
\(\mathbb E_{\sigma^-}\tau_{\sigma^+}
=\exp(\theta\Gamma+o(\theta))\)。界面割边、图几何和边界决定临界核，类型频率不能替代它们。

本节结论是：FIB 可承载自旋类型和接触关系；详细平衡、相变、磁滞和成核来自能量、翻转时钟、边界与极限合同。

## 145. FIB 隐状态递归上的 Bayes 滤波与粒子近似

令完整来源状态为 \(X_n\)，其中可包含有序树、接缝、游标和控制态；FIB 组成向量或五窗类型是其可能的摘要。若转移核为 \(K\)，观测密度为 \(g(y\mid x)\)，则后验 \(\pi_n=\mathcal L(X_n\mid Y_{0:n})\) 满足预测—校正递推
$$
\pi^-_{n+1}(A)=\int K(x,A)\pi_n(dx),
$$
$$
\pi_{n+1}(dx)
=\frac{g(Y_{n+1}\mid x)\pi^-_{n+1}(dx)}
{\int g(Y_{n+1}\mid z)\pi^-_{n+1}(dz)}.
\tag{145.1}
$$
分母为零表示数据与模型条件化不相容，不能任意重置后验。控制动作若依赖隐藏信息，也必须纳入转移和观测记录。

摘要 \(\eta(x)\) 对所有初始分布形成闭合滤波模型，当且仅当同一摘要纤维内的发射律相同，并且转移到每个摘要集合的概率相同：
$$
g(\cdot\mid x)=g(\cdot\mid\tilde x),\qquad
K(x,\eta^{-1}(B))=K(\tilde x,\eta^{-1}(B)).
\tag{145.2}
$$
因此数量、类型频数或接缝类别若遗忘了影响未来的排列，就不能直接作为有限 HMM 状态。纯 FIB 替换在给定初始树时是确定转移；随机性必须另加初始律、分支概率或观测噪声。

后验是已知模型下预测未来的充分信息状态，但不等于真实来源已恢复。当前滤波、初始来源识别和整条路径平滑是不同任务；来源生成过程丢失的次序区别不能由更多同一摘要读数补回。有限维精确闭合需要额外有限商或共轭结构。

粒子滤波以 \(N_p\) 个带权粒子近似 \(\pi_n\)。在有界似然、适当混合和重采样方案下，固定时间的经验误差通常为 \(O_{\mathbb P}(N_p^{-1/2})\)；时间增长时误差常数可能随滤波稳定性、有效样本数和重采样退化增长。近似后验的置信区间不能替代模型识别，也不能证明被遗忘的树结构可恢复。

本节结论是：FIB 递归可作为隐藏状态的来源结构，Bayes 更新和粒子误差由外加转移、观测和采样方案决定；相同摘要读数不自动构成充分统计量。

## 146. FIB 合法图上的外加非厄米谱、PT 破缺与增益损耗

取有限合法构型图 \(G_F=(V_F,E_F)\)，每个合法构型对应一个正交基态，并另加复跃迁、实势和增益损耗：
$$
\mathrm i\partial_t\psi=H\psi,\qquad
H=\sum_{(v\to u)\in E_F}t_{uv}|u\rangle\langle v|
+\sum_v(\epsilon_v+\mathrm i\gamma_v)|v\rangle\langle v|.
\tag{146.1}
$$
FIB 合法性只限制非零跃迁的支撑，不决定 \(t_{uv}\)、\(t_{vu}\) 或 \(\gamma_v\)。

非厄米矩阵不必有复谱。若无增益损耗且
\(t_{uv}=Je^{a_{uv}}\)、\(a_{uv}=-a_{vu}\)，并存在 \(\phi\) 使 \(a_{uv}=\phi_u-\phi_v\)，则对角相似变换可把 \(H\) 化为实对称矩阵，谱全实。树上的此类非互易性总可消去；闭环通量非零只说明该变换失败，仍不单独推出复谱。

PT 对称要求存在置换对合 \(P\) 满足
$$
PH^*P=H.
\tag{146.2}
$$
满足此条件时，非实本征值成共轭对。两态模型
$$
H_{\mathrm{PT}}=
\begin{pmatrix}
\epsilon+\mathrm i\gamma&J\\
J&\epsilon-\mathrm i\gamma
\end{pmatrix},
\qquad
\lambda_\pm=\epsilon\pm\sqrt{J^2-\gamma^2}
\tag{146.3}
$$
在 \(|\gamma|=J\) 处出现例外点；但该阈值只属于这份双态、对称耦合模型。随机涨落和耗散还需另加噪声、浴和测量规则。

前缀树的分支增长率与一维链谱不可互换。沿一条合法链可得到一维非厄米转移矩阵；把全部合法前缀作为顶点则得到分支图，壳层增长可能压过单路径衰减。有限图复谱分裂也不等同于无限系统 PT 相变，需指定图列、边界和谱极限。

本节结论是：FIB 提供非厄米动力学的允许支撑；复谱、PT 对称、例外点和增益损耗阈值均由外加矩阵合同决定。

## 147. FIB 周期状态图上的外加随机泵浦与几何输运

在 FIB 的一个合法周期状态子域 \(O=\{\omega_i:i\in\mathbb Z/\ell\}\) 上，另加顺、逆向跃迁率 \(a_i(t),b_i(t)\)，它们以周期 \(\tau\) 重复。概率与边电流满足
$$
J_i=a_i p_i-b_i p_{i+1},\qquad
\dot p_i=J_{i-1}-J_i.
\tag{147.1}
$$
速率、外部时钟和反向动作都不是 FIB 移位自动提供的。

若所有双向边速率有统一正下界，传播矩阵 \(U(\tau,0)\) 为正随机矩阵，存在唯一周期稳态 \(p_*(t)\)。周期积分电流
$$
Q_i=\int_0^\tau J_i(t)\,dt
\tag{147.2}
$$
在环上与 \(i\) 无关；树上的周期净边流则必须为零。只有存在闭环和至少两个可区分通道时，周期驱动才可能产生绕环泵浦。

冻结生成元的环亲和力为
$$
\mathcal A(t)=\sum_i\log\frac{a_i(t)}{b_i(t)}.
\tag{147.3}
$$
瞬时详细平衡使 \(\mathcal A=0\)，但周期稳态仍可能因分布滞后产生泵浦。若控制参数沿闭路缓慢变化且冻结生成元谱隙一致正，则
$$
Q_i=\oint A_{ia}\,d\lambda^a+O(\tau^{-1}),
\tag{147.4}
$$
其中连接 \(A_{ia}\) 由瞬时稳态和零质量子空间上的伪逆构成。两参数时闭路积分可化为几何曲率通量；单参数原路往返的几何项为零。每周期输运趋于常数，而平均电流 \(Q_i/\tau\) 趋于零，二者不可混同。

反向协议必须同时倒序控制与路径律。若正、反路径相互绝对连续，熵产生
$$
\Sigma(\gamma)
=\log\frac{p_F(x_0,0)}{p_R(x_\tau,0)}
+\sum_{\text{跳跃 }i\to j}
\log\frac{k_{ij}(t)}{k_{ji}(t)}
$$
满足
$$
\langle e^{-\Sigma}\rangle_F=1,\qquad
\langle\Sigma\rangle_F\ge0.
\tag{147.5}
$$
只有再加入局部详细平衡与环境解释，\(\Sigma\) 才能称为物理总熵产。传播矩阵的代数逆通常不是随机核，也不恢复原轨迹。

隐藏方向会造成不可识别性：四相位环上的顺、逆流速率 \(a,b\) 交换后，奇偶摘要过程可以完全相同，而完整环电流变号。故周期分布或粗粒观察只确定流的散度，不能恢复全部跃迁率和熵产。

本节结论是：FIB 可提供周期状态和闭环支撑；随机泵浦、几何相位、净流与涨落关系由外加时变跃迁和反向协议决定。

## 148. FIB 合法构型上的外加 Lindblad 退相干与量子轨迹

取有限合法构型 \(x\) 为正交基 \(\{|x\rangle\}\)，量子态是密度矩阵 \(\rho\)，而不是类型标签本身。外加 Hamiltonian \(H\) 和跳跃算子 \(J_\alpha\) 给出
$$
\dot\rho=\mathcal L(\rho)
=-\mathrm i[H,\rho]
+\sum_\alpha\left(
J_\alpha\rho J_\alpha^\dagger
-\frac12\{J_\alpha^\dagger J_\alpha,\rho\}
\right).
\tag{148.1}
$$
FIB 只限制哪些构型耦合合法，不决定耦合强度、相位、环境或物理时间。若合法子空间不是演化不变的，简单投影并重新归一化属于条件选择，不能代替无条件保迹动力学。

对角退相干算子 \(J_x=\sqrt{\gamma_x}|x\rangle\langle x|\) 满足
$$
(\mathcal D\rho)_{xy}
=-\frac12(\gamma_x+\gamma_y)\rho_{xy}\quad(x\ne y),
\qquad
(\mathcal D\rho)_{xx}=0.
\tag{148.2}
$$
它抑制指定基中的相干而不直接改变占据；若 \(H\) 含非对角耦合，占据仍可演化。退相干、经典化和达到唯一稳态是不同命题。

有向递归跳转可编码为
$$
J_{yx}=\sqrt{k_{yx}}|y\rangle\langle x|.
\tag{148.3}
$$
当 \(H\) 在该基中对角时，对角元满足经典主方程；有非对角 \(H\) 时，概率演化还依赖相干项，不能只保留类型计数。量子跳轨迹中，跳跃 \(\alpha\) 的短时概率为
\(\mathrm dt\,\langle\psi|J_\alpha^\dagger J_\alpha|\psi\rangle\)，无跳跃演化由
\(H_{\mathrm{eff}}=H-\frac{\mathrm i}{2}\sum_\alpha J_\alpha^\dagger J_\alpha\) 给出；轨迹平均才恢复式(148.1)。同一 Lindblad 生成元可以有不同轨迹展开，FIB 分支不自动等于观测跳跃。

稳态满足 \(\mathcal L(\rho_*)=0\)。有限维完全正保迹半群至少有稳态，但唯一性和全局吸引需检查零特征值重数、暗子空间及其他纯虚特征值。若零特征值简单且其余谱满足
$$
g=-\max_{\lambda\ne0}\operatorname{Re}\lambda>0,
\tag{148.4}
$$
则在适当范数下获得指数趋稳；Jordan 块可能带多项式前因子。有限截断的正谱隙也不保证随 FIB 规模增长仍有统一混合速率。

若要称稳态为 Gibbs 热平衡，还需另加能量、温度和量子详细平衡；一般耗散稳态不必热平衡。FIB 递归提供配置和关系，开放量子不可逆性、退相干速率、轨迹统计与稳态谱隙由外加环境合同决定。

## 149. FIB 合法路径上的外加 Burgers 激波与熵解

FIB 接缝只决定允许边和分叉；Burgers 动力学还需外加边长、场变量、时间、通量和节点条件。在均匀细分边上，守恒离散方程可写
$$
\dot u_i
=-\frac{F(u_i,u_{i+1})-F(u_{i-1},u_i)}h
+\nu\frac{u_{i+1}-2u_i+u_{i-1}}{h^2},
\qquad f(u)=\frac{u^2}{2}.
\tag{149.1}
$$
通量需采用单调守恒格式并满足相应 CFL；分叉处还需另给共同通量规则。任意图差分不自动守恒或耗散。

连续边内方程为
$$
u_t+\partial_x(u^2/2)=\nu u_{xx},\qquad \nu>0.
\tag{149.2}
$$
无黏极限的激波速度遵循 Rankine–Hugoniot 关系
$$
s=\frac{f(u_L)-f(u_R)}{u_L-u_R}
=\frac{u_L+u_R}{2}.
\tag{149.3}
$$
压缩情形 \(u_L>u_R\) 形成熵激波，反向排列给出稀疏波。黏性过渡层厚度通常为 \(O(\nu/(u_L-u_R))\)。波抵达 FIB 分叉后如何分裂或透射取决于接点模型，不能由标签决定。

对凸熵 \(\eta\) 及 \(q'(u)=\eta'(u)u\)，有
$$
\partial_t\eta(u)+\partial_xq(u)
=\nu\partial_{xx}\eta(u)-\nu\eta''(u)u_x^2.
\tag{149.4}
$$
无黏极限需满足全部 Kružkov 熵不等式；这里的熵是守恒律的凸熵，不是路径数量或 Shannon 熵。迁移到 FIB 网络还需接点熵条件、紧性和极限唯一性。

固定网格令 \(\nu\to0\) 与同时令 \(h\to0\) 的连续极限不同；物理黏性和数值黏性必须分别控制。FIB 层数增长不等于空间网格细化，无限前缀展开还需局部质量、变差和边界流的统一估计。守恒噪声可以用关联矩阵 \(B\) 表示为 \(M\,du=-BJ\,dt+\sigma BC\,dW_t\)，但噪声相关、保正性和熵修正都需额外假设。

本节结论是：FIB 提供守恒流的组合支撑；激波速度、熵选择、黏性极限和随机扰动由外加通量、几何和接点合同决定。

## 150. FIB 接触网络上的外加堵塞、等静态与力链

FIB 图 \(H_{\mathrm{FIB}}\) 只表示候选关系。颗粒力学还需位置 \(q\)、尺寸、边界、真实接触边 \(E_c(q)\) 和接触力。球形颗粒的间隙为
$$
g_{ij}(q)=\|q_i-q_j\|-(a_i+a_j).
\tag{150.1}
$$
硬颗粒要求 \(g_{ij}\ge0\)，接触满足 \(g_{ij}=0\)；因此真实接触图是几何嵌入的函数，不能直接等同于 FIB 邻接图。

线性化接触约束形成刚性矩阵 \(R\)。其零空间给出一阶无约束运动，自应力空间为 \(\ker R^{\mathsf T}\)。Maxwell–Calladine 计数可写
$$
N_0-N_s=D-M,
\tag{150.2}
$$
其中 \(D\) 是自由度、\(M\) 是独立约束数、\(N_0\) 是非平凡零模、\(N_s\) 是独立自应力数。等静态计数 \(M=D-g\) 只是必要计数条件，不是刚性或 collective jamming 的充分条件。

力平衡为
$$
R^{\mathsf T}f+b=0,
\qquad f_{ij}\ge0
\tag{150.3}
$$
（对单边法向接触）。接触边 \(E_c\) 与承力边 \(E_f=\{e:f_e\ne0\}\) 必须分开。按力阈值和方向连续性筛出的力链依赖载荷、阈值、时间与尺度，不是纯拓扑不变量。

堵塞阈值还依赖体积分数、制备协议、颗粒势、边界和维数。过配位量
$$
\Delta z=z-z_{\mathrm{iso}}
\tag{150.4}
$$
可作控制变量，但临界指数和有限尺寸修正不是 FIB 普适量。有限样本阈值是样本变量；边界接触和盒形自由度必须进入刚性矩阵。周期边界消除部分表面效应，却不自动证明 strict jamming。

本节结论是：FIB 可分层承载候选邻接、几何接触、受力边和力链；是否等静态、刚性、堵塞及有限尺寸阈值由几何、力学和边界合同共同决定。

## 151. FIB 递归粗粒化上的外加重整化群与有限尺寸标度

Fibonacci 递归可以标记块的组成和尺度，但 RG 的数学内容是统计权重在粗粒化后的变换。若块长 \(\ell_n\propto F_n\)，尺度因子趋于 \(\varphi\)；若 \(F_n\) 表示体积，线尺度因子应为 \(\varphi^{1/d}\)。递归标签本身没有长度单位。

真正的 RG 闭合要求粗粒化核 \(B(\tau\mid\sigma)\) 满足
$$
\sum_\sigma B(\tau\mid\sigma)e^{-H_K(\sigma)}
=e^{c(K)}e^{-H_{\mathcal R(K)}(\tau)}
\tag{151.1}
$$
并且模型族、边界和尺度重置相容。消元若生成长程或多体耦合而参数族未容纳，则只是近似截断，必须给误差或相关性控制。

一个精确示例是一维 Fibonacci 键 Ising 链。对 \(u_A=\tanh K_A\)、\(u_B=\tanh K_B\)，串联消元给出
$$
u'_A=u_Au_B,\qquad u'_B=u_A.
\tag{151.2}
$$
此闭合来自内部自旋求和，而非仅来自组合增长。即便 RG 精确闭合，正温一维链仍可有有限相关长度而无有限温相变。

临界不动点 \(K_*\) 需要
\(\mathcal R(K_*)=K_*\) 及可接近的相关方向。若热标度场满足
$$
t'=\lambda_t t+O(t^2),\qquad |\lambda_t|>1,
$$
并且相关长度按尺度 \(b\) 变换，则
$$
\xi\sim |t|^{-\nu},
\qquad
\nu=\frac{\log b}{\log|\lambda_t|}.
\tag{151.3}
$$
组合矩阵的黄金特征值不是 \(\lambda_t\)。若 RG 逐步变化，应研究 Jacobian 乘积或循环变换，而不是强行使用单步特征值。

在通常标度假设下，有限尺寸自由能可写
$$
f_s(t,h,L)=L^{-d}
\mathcal F(tL^{1/\nu},hL^{y_h},\{u_iL^{y_i}\},\theta),
\tag{151.4}
$$
并得到磁化、磁化率和 \(\xi_L/L\) 的相应标度。危险不相关变量、离散尺度周期、边界和替换相位可能改变修正项；沿 Fibonacci 尺寸看到稳定斜率或数据塌缩，不足以独立证明临界点或普适指数。

本节结论是：FIB 可以提供粗粒化的层级和块序列；RG 不动点、临界指数和有限尺寸标度只有在统计权重闭合、尺度对应和极限条件都成立时才可推出。

## 152. FIB 路径上的外加随机波、相干叠加与散斑统计

FIB 路径族只规定合法传播关系，不提供波长、空间距离、复振幅、相位或介质无序。另加静态随机介质的标量波方程
$$
[\Delta+k^2n^2(x,\omega)]u(x,\omega)=0,
\qquad
n=n_{\mathrm{FIB}}+\varepsilon\eta.
\tag{152.1}
$$
其中 \(\eta\) 的均值、协方差和相关尺度须指定，并且所有路径读取同一个介质实现。

在有限通道或已受控的路径展开中，
$$
E(r,\omega)=\sum_{\gamma\in\Gamma}A_\gamma(r,\omega),
\qquad
I(r)=\left|\sum_\gamma A_\gamma(r,\omega)\right|^2.
\tag{152.2}
$$
只有落入同一可干涉模式的贡献才先相加再取模平方；正交模式的能量应分别求和。相同类型计数不足以确定相位干涉：振幅 \((1,1)\) 与 \((1,-1)\) 的总强度分别为 \(4\) 和 \(0\)。

若弱随机相位 \(X_\gamma\) 采用联合高斯模型，则
$$
\mathbb E e^{\mathrm i(X_\gamma-X_\delta)}
=\exp[-D_{\gamma\delta}/2],
\qquad
D_{\gamma\delta}=\operatorname{Var}(X_\gamma-X_\delta).
\tag{152.3}
$$
共享介质段会产生路径间相关；给每条路径独立抽相位会丢掉这种联合结构。若许多弱贡献满足无主导项和适当依赖条件，合成场才可能趋于圆对称复高斯，单模式强度才呈指数律。非零相干背景、主导路径和强相关会改变散斑对比度。

场相关函数为
$$
\Gamma_E(r,r')=\mathbb E[E(r)E(r')^*]
=\sum_{\gamma,\delta}
\mathbb E[A_\gamma(r)A_\delta(r')^*].
\tag{152.4}
$$
单点强度和类型频率不足以重建空间相关。若场确为零均值圆对称复高斯，才有 \(g^{(2)}=1+|g^{(1)}|^2\) 的 Siegert 关系；非高斯四阶相关或有限探测面积需另行修正。

弱散射、辐射输运和扩散近似对应不同尺度。弱随机扰动下首阶散射率常为 \(O(\varepsilon^2)\)，但传播距离需同时按平均自由程缩放；固定距离的 \(\varepsilon\to0\) 与长距离扩散极限不可混同。回返干涉、长程相关和强散射可能导致局域化，不能无条件套用经典扩散。

本节结论是：FIB 提供散射路径的组合支撑；波的相位、介质联合无序、相干叠加、散斑相关和散射极限均由外加波动模型决定。

## 153. FIB 路径测度上的外加多重分形与热力学形式

FIB 代换只给出合法词、递归层级和路径拼接关系。要讨论多重分形，必须另加路径空间上的概率测度、尺度度量以及把符号路径嵌入物理空间的映射。令
$$
\sigma(a)=ab,\qquad \sigma(b)=a,
$$
并令 \(X_F\) 为其移位闭包。长度为 \(n\) 的合法因子集合记为 \(L_n\)，则
$$
|L_n|=p(n)=n+1,
\qquad
h_{\mathrm{top}}(X_F)=\lim_{n\to\infty}n^{-1}\log p(n)=0.
\tag{153.1}
$$
代换矩阵的 Perron 根 \(\varphi\) 描述代换层级的长度增长，不能直接当作拓扑熵、测度熵或物理维数。

在 \(X_F\) 上给定柱集
$$
[u]=\{x\in X_F:x_1\cdots x_n=u\}
$$
及概率测度 \(\mu\)，必须满足
$$
\mu([u])\ge0,\qquad
\mu([u])=\sum_{ua\in L_{n+1}}\mu([ua]),\qquad
\mu(X_F)=1.
\tag{153.2}
$$
测度可以来自移位不变测度、Markov 转移概率或外加势函数；这些选择不是 FIB 递归本身决定的。若符号度量取
$$
d_\rho(x,y)=\rho^{N(x,y)},\qquad 0<\rho<1,
$$
其中 \(N(x,y)\) 是首个不同位置，则柱集尺度为 \(\varepsilon_n=\rho^n\)，局部维数和质量指数可写为
$$
\alpha(x)=\lim_{n\to\infty}\frac{\log\mu([x_1\cdots x_n])}{\log\varepsilon_n},
\qquad
\tau(q)=\lim_{n\to\infty}\frac{\log\sum_{u\in L_n}\mu([u])^q}{\log\varepsilon_n}.
\tag{153.3}
$$
若极限不存在，应使用上、下局部维数。Rényi 维数在 \(q\ne1\) 时为 \(D_q=\tau(q)/(q-1)\)，而信息维数需按熵率极限另行定义。

若测度是势函数 \(\psi\) 的 Gibbs 测度，且几何收缩率为 \(r_e\)，记 \(\chi(e)=-\log r_e\)。在可加性、有限平均几何势和有界畸变条件下，压力函数满足
$$
P\bigl(q\psi+\tau(q)\chi\bigr)=0.
\tag{153.4}
$$
当 \(\psi\) 已归一化为 \(P(\psi)=0\) 且 \(\chi\) 为常数时，才可化为 \(\tau(q)=-P(q\psi)/\chi\)。因此控制维数的是概率势与几何尺度势的比值，而不是 \(\varphi\) 单独决定的增长率。

令
$$
E_\alpha=\{x:\alpha(x)=\alpha\},\qquad f(\alpha)=\dim_H E_\alpha.
$$
在 Gibbs 性、准 Bernoulli 性、可微压力和适当畸变控制下，才有
$$
\alpha=\tau'(q),\qquad f(\alpha)=q\alpha-\tau(q)
$$
的 Legendre 形式。无这些条件时，Legendre 变换首先只给出上界；压力不可导时得到的往往是谱的凹包，不能自动等同于真实谱。

标准符号度量下，\(p(n)=n+1\) 只有次指数增长，所以对任意 \(s>0\)，
$$
\sum_{u\in L_n}\operatorname{diam}([u])^s
\le(n+1)\rho^{ns}\longrightarrow0,
$$
从而 \(\dim_H X_F=0\)。这只是符号度量下的结论。若把路径嵌入带有瓦片长度、局部补丁尺度或非均匀收缩率的物理集合，柱集直径改变，维数必须根据该映射重新计算；在满足精确维数条件时可出现类似
$$
\dim_H\mu=\frac{h_\mu}{\int\chi\,d\mu}
$$
的熵率与平均收缩率比值。

本节结论是：FIB 提供路径和因子复杂度的组合框架；多重分形谱、压力相变和非零物理维数由外加测度、几何尺度、编码正则性及相应极限共同决定。

## 154. FIB 递归分块上的外加纠缠熵与张量网络

FIB 的递归括号只给出有序分块和接缝关系。要定义纠缠，必须先指定每个叶对应的物理自由度、Hilbert 空间和张量分解。若第 \(j\) 层有 \(N_j\) 个叶、每个叶为 \(d\) 维站点，则可取
$$
\mathcal H_j=(\mathbb C^d)^{\otimes N_j},
$$
但叶标签的数量权重不自动等于 Hilbert 空间维数。地址投影产生的是直和
$$
\mathcal H=\bigoplus_w P_w\mathcal H,
$$
而纠缠熵要求给定 \(\mathcal H_A\otimes\mathcal H_B\) 的物理子系统分区。把 FIB 左右子树当作 \(A,B\)，还需证明两侧叶映射到互不重叠的物理自由度。

对归一化纯态的 Schmidt 分解
$$
|\psi\rangle=\sum_{r=1}^R\sqrt{p_r}\,|r_A\rangle|r_B\rangle,
\qquad
S(A)=-\sum_r p_r\log p_r,
$$
有 \(S(A)\le\log R\)。开边界 MPS 在一条切口上的 Schmidt 秩不超过键维数 \(\chi\)，故 \(S\le\log\chi\)；若区域由 \(b\) 条虚腿隔开且每条维数不超过 \(\chi\)，则
$$
S(A)\le b\log\chi,\qquad \chi\ge e^{S(A)/b}.
\tag{154.1}
$$
后一式只是必要下界。一般张量网络满足割容量上界
$$
S(A)\le\min_C\sum_{e\in C}\log\chi_e,
\tag{154.2}
$$
等号还需张量和全局相容条件。FIB 接缝上的经典标签只有经过明确量子实现才可作为虚腿，且其对数只是容量上界。

若完整子树只通过一条虚腿连接其余网络，其熵至多为 \(\log\chi\)。按叶序取连续区间时，区间边界可能穿过随树高增长的多条虚腿；树高为 \(O(\log N)\) 只给出一个可能的对数级上界，并不证明每层贡献非零纠缠。把树态改写为链式 MPS 时，链切口的键维数可能是跨割虚腿维数的乘积。

精确表示与近似表示必须区分。截取前 \(\chi\) 个 Schmidt 项的尾重为
$$
\delta_\chi=\sum_{r>\chi}p_r,
$$
全链误差还需控制不同切口的截断误差累积；单个熵值不能替代完整 Schmidt 谱。

物理面积律需要 Hamiltonian 条件，例如一维局域有限程链的唯一基态和与系统规模无关的非零谱隙。FIB 排列可调制耦合，但不提供谱隙或基态。若具体模型的低能极限是中心荷为 \(c\) 的 \(1+1\) 维共形场论，才有
$$
S(\ell)=\frac c3\log(\ell/a)+O(1)
$$
的临界标度；若物理长度取 \(\ell_j=aN_j\)，代入 Fibonacci 长度序列只能得到相应的序列取样，黄金比例不决定 \(c\)。离散尺度结构可能引入对数周期修正，但其系数和周期须由同一 Hamiltonian 与同一态求出。

对混态，约化熵同时包含局部混合与相关。Bell 态与经典混合态可以有相同单侧熵和计算基概率而具有不同纠缠，因此地址概率不能决定纠缠；应另用可分性、互信息或其他纠缠指标。MPO 键维数控制算符表示复杂度，也不能直接套用纯态 MPS 的熵解释。单粒子行走在明确的空间模式分区下 Schmidt 秩至多为二，故 \(S(A)\le\log2\)，不会仅因 FIB 块数增加而产生无界多体临界熵。

本节结论是：FIB 提供分块、接缝和多尺度组织；纠缠熵、面积律、临界对数和张量网络键维数的物理解释由外加 Hilbert 分解、态、Hamiltonian 及其谱性质决定。

## 155. FIB 关系图上的外加裂纹扩展与 crackling 统计

FIB 只提供关系图；位移、应力、刚度、损伤变量、物理嵌入和边界条件都必须外加。令节点位移为 \(u_i\)，不可逆损伤为 \(d_i\in[0,1]\)，边刚度可取
$$
k_e(d_e)=k_e^0(1-d_e)^p,
$$
外载参数为 \(\lambda\)，总势能写成
$$
\Pi(u,d;\lambda)=\tfrac12u^{\mathsf T}K(d)u-\lambda f^{\mathsf T}u+\Pi_{\rm frac}(d),
\qquad K(d)u=\lambda f.
\tag{155.1}
$$
每次微观损伤后是否重新平衡，决定了模型是准静态雪崩还是含惯性的动力学过程。损伤驱动力可取 \(Y_i=-\partial\Pi/\partial d_i\)，并与局部阻力 \(R_i\) 比较；阈值、断裂能和疲劳律均需明确。

裂纹前沿应定义为已断区与完整区之间的图割 \(\Gamma\)，不能把所有损伤节点都当作前沿。若 FIB 没有物理嵌入，必须另外规定前沿测度 \(A_\Gamma\)。对前沿边可定义离散能量释放率
$$
G_e=-\frac{\Delta\Pi}{\Delta A_e},
$$
并以 \(G_e\ge G_{c,e}\) 作为推进条件；迁移率模型可写为
$$
v_e=M_e[G_e-G_{c,e}]_+^m+\eta_e(t).
\tag{155.2}
$$
长程边会使图距离上的局部跃迁对应物理嵌入中的非局部跳跃。

分布式损伤和前沿断裂应分层记录。一次外载增量后、下一次外载施加前的连锁事件集合记为 \(\mathcal A\)，其大小可取
$$
S=\sum_{i\in\mathcal A}\Delta d_i
$$
或断键数。传感器观测到的声发射能量还经过波传播、耦合和阈值筛选，不能自动等同于潜在损伤事件大小。

随机性应区分淬火、退火和驱动三层。淬火随机性包括初始刚度、边权、拓扑以及 \(R_i,G_{c,e}\)；退火随机性包括热噪声、事件内次序和前沿扰动；驱动随机性包括外载增量和加载速率。准静态雪崩要求在固定 \(\lambda\) 下完成内部连锁后再增加外载，有限速率会使相邻雪崩重叠。

有限图上的雪崩分布至多具有截断形式
$$
P(S;N)=S^{-\tau}f\!\left(S/S_c(N)\right),
$$
其中 \(S_c\) 还受图直径、前沿长度、过程区和边界距离限制。单个有限样本不能推出无限系统普适指数；应改变 \(N\)、边界条件和无序相关长度并检验截断的共同尺度律。裂纹触及外边界的事件应单独标记，周期、自由和夹持边界不能混用，加载速率趋零与系统规模趋无穷的极限也未必可交换。

裂纹扩展、沙堆雪崩和 jamming 需要分辨。裂纹模型有弹性平衡、不可逆刚度退化、裂纹前沿和能量释放；沙堆模型通常以守恒标量的局部超阈值转移为核心；jamming 关注接触网络获得宏观刚性，接触打开可以可逆。仅凭声发射幂律或雪崩图形不能区分三者。

本节结论是：FIB 提供候选邻接与载荷传递路径；裂纹前沿、能量释放率、断裂阈值、声发射统计及其有限尺寸指数由外加弹性、损伤、随机和边界模型决定。

## 156. FIB 共振超图上的外加波湍流与能量级联

FIB 合法关系可抽象为三元超图
$$
\mathcal G=(V,\mathcal T,\omega),
$$
其中 \(V\) 是合法模态，\(\mathcal T\subset V^3\) 是允许的三波超边，\(\omega_v\) 是外加线性色散关系。普通二元边不足以记录动量闭合与共振条件。弱非线性振幅可以写为
$$
\dot a_v+i\omega_v a_v
=\varepsilon\!\!\sum_{(v,v_1,v_2)\in\mathcal T}V_{vv_1v_2}a_{v_1}a_{v_2}
+f_v-\gamma_v a_v+O(\varepsilon^2),
\qquad \varepsilon\ll1.
\tag{156.1}
$$
三波共振还需满足波数与频率条件
$$
\kappa_v=\kappa_{v_1}+\kappa_{v_2},\qquad
\sigma_0\omega_v+\sigma_1\omega_{v_1}+\sigma_2\omega_{v_2}=0,
$$
并且三元组属于 \(\mathcal T\)。有限图上严格共振可能稀疏，有限时间内需另定共振宽度 \(|\Delta\omega|\lesssim\Gamma\)。若共振超图不连通，能量只能在各分量内交换。

在弱耦合、随机相位、相位相关衰减和足够长统计时间尺度下，模态谱 \(n_v=\langle|a_v|^2\rangle\) 可近似满足三波 kinetic equation，其核包含 \(|V|^2\)、波数闭合、频率共振和组合项。典型守恒量为
$$
Q_E=\sum_v\omega_vn_v,
\qquad Q_N=\sum_v n_v,
$$
但第二个守恒量需相应相位对称。对模态子集 \(V_{\le K}\)，通量可定义为
$$
\Pi_Q(K)=-\frac{d}{dt}\sum_{v\in V_{\le K}}q_v.
$$
只有存在外部注入、耗散端、足够宽的惯性区和适当局部性时，才可能出现近似常通量与 Zakharov–Kolmogorov 型谱；指数由维数、色散齐次度、耦合系数和输运不变量共同决定。

Navier–Stokes 傅里叶空间中的三模态几何耦合不自动是三波共振；普通三维湍流通常属于强非线性。标准零背景 NLS 的基本弱湍流过程通常是四波共振，三波项需要凝聚背景、二次项、多分量或外部泵浦。因而不能把 Navier–Stokes 和 NLS 直接套用同一三波指数。

对 FIB 合法图，结论边界包括：非法超边不进入模型只是截断约定，不等于物理上无泄漏；离散频率和孤立共振可能产生准周期交换而非连续级联；相位相关、间歇性或非线性频移与线性频率同阶时，随机相位闭合失效；没有 forcing 与 dissipation 的守恒系统不能产生持续非零稳态通量。

本节结论是：FIB 提供合法模态与相互作用超图；波频率、相位、源汇、统计闭合、共振宽度和惯性区极限均由外加波动力学决定，不能由三元组合关系单独推出普适能谱。

## 157. FIB 混合动力学上的外加 tipping、滞回与预警

FIB 递归保留来源树、顺序和接缝；连续时间、随机跳转、能量与反馈必须另行指定。可取混合状态
$$
S=(T,x,m,\theta),
$$
其中 \(T\) 是递归来源，\(x\) 是连续变量，\(m\) 是运行模式，\(\theta\) 是年龄变量。跳转之间满足
$$
\dot x=f_m(T,x,u(t)),\qquad \dot\theta=1,
$$
到达守卫集合时按重置规则跳转，或由强度 \(k_j(S,u)\) 与核 \(K_j(S,dS')\) 随机触发。核必须只支持合法后继，并规定树、连续变量、模式和计时器的更新；若等待时间非指数分布，年龄变量及风险率不可省略。

没有连续扩散时，内部生成元可写为
$$
\mathcal L\psi
=f_m\cdot\nabla_x\psi+\partial_\theta\psi
+\sum_jk_j\left[\int\psi(S')K_j(S,dS')-\psi(S)\right],
\tag{157.1}
$$
守卫上的强制重置另给边界条件。仅有递归式不能选择这些概率结构，也不能把离散组成格直接当作连续流形。若跳转风险依赖最左叶，则 \(\langle\alpha,\beta\rangle\) 与 \(\langle\beta,\alpha\rangle\) 虽有相同数量却有不同未来风险；这说明数量压缩不充分，需保留顺序或历史。

矩阵特征值 \(\varphi\) 与 \(-\varphi^{-1}\) 描述组成增长及交替收缩，不是物理恢复率。各模式分别稳定也不保证切换系统稳定；扰动传播须包含连续流、重置导数和事件时间变化，随机切换则需研究传播算子的实际乘积。平均流近似还要求快切换、遍历性和尺度分离。

至少应区分三类 tipping：冻结参数后吸引结构消失的分岔诱导跃迁；吸引结构仍在但噪声或随机切换越过吸引域边界的随机诱导跃迁；每个冻结参数都稳定却因驱动过快而失去跟踪的速率诱导跃迁。混合系统还会发生守卫掠碰、边界碰撞和重置越界，不能一律归为 Kramers 越障。

给定旧区域 \(A\) 和目标区域 \(B\)，首次到达时间为
$$
\tau_B=\inf\{t:S_t\in B\}.
$$
若目标要求持久改变，还需规定在 \(B\) 中的驻留时间并把驻留计时纳入状态。参数固定、过程无爆炸且满足正则条件时，先到达 \(B\) 而非返回 \(A\) 的概率可由
$$
\mathcal Lh=0,\qquad h|_A=0,\quad h|_B=1
\tag{157.2}
$$
描述；外部驱动变化时应改用时间索引的有限视界风险。

滞回可由双阈值模式构造：上行在 \(u_\uparrow\) 切入模式一，下行在 \(u_\downarrow<u_\uparrow\) 切回模式零。该回线来自模式状态与切换规则，不需要预设双阱势能。模式回切也不等于递归来源复原；单向 FIB 替换若没有合法逆操作就不会形成树的往返周期。有限扫速造成的滞后还需与真正的准静态滞回区分，噪声、系统规模和扫速极限的次序可能改变结论。

Kramers 逃逸率 \(k\sim C\exp(-\Delta V/D)\) 只适用于固定势能、非退化势阱和小噪声等条件；一般守卫跳转、非梯度流和突发重置不由此公式决定。Glauber 动力学要求局部更新率及正反操作的详细平衡，单向 FIB 替换没有反向操作时不能在正质量来源上满足该平衡。

在局部平稳、小扰动和固定噪声强度下，若慢模态近似为
$$
dz=-\kappa z\,dt+\sigma\,dW_t,
$$
则
$$
\operatorname{Var}(z)=\frac{\sigma^2}{2\kappa},\qquad
\operatorname{Corr}(z_t,z_{t+\Delta})=e^{-\kappa\Delta}.
$$
恢复率下降会同时提高方差和自相关，但随机越障、速率诱导跃迁或守卫触发未必伴随临界减速。模式混合还满足
$$
\operatorname{Var}(Y)=\mathbb E[\operatorname{Var}(Y\mid m)]
+\operatorname{Var}(\mathbb E[Y\mid m]),
$$
两模式均值分离即可提高总方差；两态切换的自相关也可因切换速率降低而变慢，与局部失稳无关。

因此较有判别力的预警应联合使用模式内恢复率、跳转强度、驻留分布、守卫距离和有限视界到达风险，并报告提前量、漏报率、误报率及概率校准。方差或自相关上升本身不能认证 tipping 机制。

本节结论是：FIB 提供递归来源、合法接缝和模式组织；连续流、跳转核、稳定性、滞回、逃逸律、tipping 机制及预警统计均由外加混合动力学与观测模型决定。

## 158. FIB 路径上的外加反应—扩散、Turing 图样与相分离

FIB ATOM 递归只提供路径、邻接和接缝。顶点上的场变量、质量、扩散权重、反应项、噪声、边界条件与连续极限都需外加。对一条含 \(N\) 个顶点的有限路径，取关联矩阵 \(B\)、顶点容量 \(m_i>0\) 和边传导权重 \(w_e>0\)，并定义
$$
M=\operatorname{diag}(m_i),\qquad
W=\operatorname{diag}(w_e),\qquad
L=M^{-1}B^{\mathsf T}WB.
\tag{158.1}
$$
在连通且无外部通量的有限路径上，\(L\mathbf1=0\)，并且
$$
\langle x,Lx\rangle_M
=\sum_e w_e(Bx)_e^2\ge0.
$$
因而可以按 \(M\) 内积分解为特征模态
$$
0=\lambda_0<\lambda_1\le\cdots\le\lambda_{N-1}.
$$
边权是否由原子类型或接缝类型决定，属于外加物理解释；FIB 标签本身不规定传导率。

在路径上外加两个组分 \(u_i,v_i\)，考虑
$$
\dot u_i=f(u_i,v_i)-D_u(Lu)_i,\qquad
\dot v_i=g(u_i,v_i)-D_v(Lv)_i,
\qquad D_u,D_v>0.
\tag{158.2}
$$
若 \((u_*,v_*)\) 是均匀反应平衡，反应雅可比为
$$
J=\begin{pmatrix}a&b\\c&d\end{pmatrix},
$$
则无扩散局部稳定要求
$$
a+d<0,\qquad \delta:=ad-bc>0.
$$
沿空间模态 \(\lambda_k\) 的线性矩阵为
$$
J-\lambda_k
\begin{pmatrix}D_u&0\\0&D_v\end{pmatrix},
$$
其行列式为
$$
Q(\lambda)=\delta-S\lambda+D_uD_v\lambda^2,
\qquad S=aD_v+dD_u.
\tag{158.3}
$$
在局部反应稳定的前提下，只有当实际 FIB 路径谱中存在 \(k\ge1\) 使 \(Q(\lambda_k)<0\) 时，才有扩散驱动的线性失稳。必要的连续谱条件为
$$
S>0,\qquad S^2>4D_uD_v\delta,
$$
并且某个 \(\lambda_k\) 落入
$$
\lambda_\pm=
\frac{S\pm\sqrt{S^2-4D_uD_v\delta}}{2D_uD_v}
$$
之间。若 \(D_u=D_v\)，扩散只把每个反应特征值向稳定方向平移，不能产生两组分 Turing 失稳。线性失稳也不保证最终稳定图样；振幅、分岔分支和吸引域仍由非线性反应项决定。

守恒相分离需要另一套外加自由能和迁移律。给定浓度 \(c_i\)、局部自由能 \(\psi\)、界面系数 \(\kappa>0\) 和迁移率 \(\eta>0\)，定义
$$
E(c)=\sum_i m_i\psi(c_i)
+\frac{\kappa}{2}\sum_e w_e(Bc)_e^2,
\qquad
\mu=\psi'(c)+\kappa Lc.
\tag{158.4}
$$
图上的 Cahn–Hilliard 型方程为
$$
\dot c=-\eta L\mu.
\tag{158.5}
$$
无外部通量时，
$$
\frac{d}{dt}\sum_i m_ic_i=0,\qquad
\frac{dE}{dt}
=-\eta\langle\mu,L\mu\rangle_M\le0.
\tag{158.6}
$$
均匀浓度 \(\bar c\) 的第 \(k\) 个非零模态增长率为
$$
\sigma_k=-\eta\lambda_k\bigl(\psi''(\bar c)+\kappa\lambda_k\bigr).
$$
只有当
$$
\psi''(\bar c)<0,\qquad
0<\lambda_k<-\frac{\psi''(\bar c)}{\kappa}
$$
时才发生自旋odal线性失稳。路径过短、界面代价过强或边权过大都可能使全部模态避开不稳定区间。成核、粗化和长期畴尺寸还需非线性与噪声分析，不能由线性判据直接决定。

端点的无通量、固定值、储库耦合和周期闭合会产生不同的零模态与谱；周期首尾边不是 FIB 拼接自动提供的物理边。加入随机源时必须给出协方差、守恒投影和解释尺度。连续极限还需指定网格间距、权重缩放和时间缩放；固定有限路径上的图谱结论不能自动成为偏微分方程结论。

本节结论是：FIB 提供扩散网络的组合骨架；Turing 图样、相分离、自旋odal区间、自由能耗散和连续极限均由外加反应—扩散或守恒动力学决定。

## 159. FIB 加权算子的外加谱统计、输运与局域化

令 Fibonacci 单词由
$$
w_0=B,\qquad w_1=A,\qquad w_{n+1}=w_nw_{n-1}
$$
生成，长度 \(q_n=|w_n|\) 满足 FIB 递归。由字母指定局部势 \(v_j\) 和跃迁 \(t_j>0\)，有限链上的外加 Jacobi 算子为
$$
(H\psi)_j=t_{j-1}\psi_{j-1}+v_j\psi_j+t_j\psi_{j+1}.
\tag{159.1}
$$
开放边界、周期闭合和加权图 Laplacian 是不同的算子；将邻接矩阵解释为 Hamiltonian 或 Markov 转移矩阵还需另定能量尺度、守恒量和演化方程。

对定态方程，令
$$
\nu_j=
\begin{pmatrix}\psi_j\\ t_{j-1}\psi_{j-1}\end{pmatrix},
\qquad
\nu_{j+1}=T_j(E)\nu_j,
$$
其中
$$
T_j(E)=
\begin{pmatrix}
(E-v_j)/t_j&-1/t_j\\
t_j&0
\end{pmatrix},
\qquad \det T_j(E)=1.
\tag{159.2}
$$
沿完整 Fibonacci 块的有序乘积 \(M_n\) 在固定拼接约定下满足
$$
M_{n+1}=M_{n-1}M_n.
$$
半迹 \(x_n=\tfrac12\operatorname{tr}M_n\) 可满足
$$
x_{n+1}=2x_nx_{n-1}-x_{n-2}.
\tag{159.3}
$$
该迹递归依赖完整块的有序重复；只知道顶点数量递归不能推出它。若逐位置加入独立无序，同一字母块的参数不再相同，迹映射通常失去闭合。

必须区分确定性准周期模型、Fibonacci 相位系综、独立现场无序、随机跃迁无序和具有长程相关的随机替换。相同的无序强度不等于相同的联合分布；共享块相关和逐点独立噪声会产生不同的传递矩阵乘积。对于有限 Hamiltonian 的特征值 \(E_1^{(n)},\dots,E_{q_n}^{(n)}\)，归一化谱测度为
$$
\nu_n=\frac1{q_n}\sum_{j=1}^{q_n}\delta_{E_j^{(n)}},
\qquad
N_n(E)=\nu_n((-\infty,E]).
\tag{159.4}
$$
只有在指定模型、遍历性和极限方式后，才能讨论 \(\nu_n\) 或积分态密度 \(N(E)\) 的弱极限。若极限测度不绝对连续，\(\rho(E)=dN/dE\) 不是普通函数；展宽直方图只是一种分辨率依赖的表示。

沿系统尺寸增加时，开放与周期边界的有限秩差可能使归一化计数差消失，但仍可改变边界态和有限尺寸输运。确定性 Fibonacci 链的间距分布不能预先归入 Poisson 或 GOE；比较间距还需先用积分态密度展开平均密度。对一维独立现场无序，纯点谱和指数局域化需要相应的随机性、正则性和能量条件；Poisson 间距统计还需要控制近简并和局部能级概率的额外估计。实对称性也不能单独保证 GOE 统计，固定带宽的一维随机链不会因尺寸增大自动成为稠密随机矩阵。

若研究稠密随机矩阵，可另行定义
$$
H_{ij}^{(N)}
=a_{\sigma_i}\delta_{ij}
+\frac{\sqrt{s_{\sigma_i\sigma_j}}}{\sqrt N}X_{ij},
$$
其中 \(\sigma_i\) 来自 Fibonacci 词，\(X_{ij}\) 是中心化对称随机变量。此时谱密度和间距统计由随机矩阵的方差结构、矩条件和极限决定，不能与一维准周期链混同。局域化长度、系统长度、无序强度和 Fibonacci 极限的次序也会改变有限样本表现。

本节结论是：FIB 提供有序算子系数与块递归；谱测度、态密度、能级统计、输运和局域化由具体算子、随机联合律、边界及热力学极限共同决定。

## 160. FIB 递归分支上的外加种群增长、分枝与灭绝

FIB 计数递归
$$
F_{n+2}=F_{n+1}+F_n
$$
首先只是路径数或组合对象的数量关系，不自动表示个体出生、死亡、资源或观察。若把两个递归状态解释为两类个体，令
$$
Z_n=(Y_n,O_n)^{\mathsf T},
\qquad
\mathbb E[Z_{n+1}\mid Z_n]=MZ_n,
\qquad
M=\begin{pmatrix}a&b\\1&0\end{pmatrix},
\tag{160.1}
$$
则第一坐标的期望满足
$$
\mathbb E[Y_{n+2}]
=a\,\mathbb E[Y_{n+1}]
+b\,\mathbb E[Y_n].
$$
FIB 情形是 \(a=b=1\)。矩阵 Perron 根为
$$
R=\frac{a+\sqrt{a^2+4b}}2,
$$
在非负参数下，低密度线性增长阈值为
$$
R>1,\quad R=1,\quad R<1.
$$
若额外繁殖率 \(r\) 作用于新生个体，则阈值变为 \(r(a+b)>1\) 或相应的 \(r\rho(M)>1\)，取决于 \(r\) 作用的位置。

分枝随机性由概率生成函数给出。令 \(g_Y(s,t),g_O(s,t)\) 是两类个体的后代生成函数，均值矩阵由其在 \((1,1)\) 处的导数给出。第 \(n\) 代生成函数满足
$$
G_{n+1,j}(s,t)
=g_j\bigl(G_{n,Y}(s,t),G_{n,O}(s,t)\bigr).
$$
灭绝概率向量 \(q\) 是最小不动点
$$
q_Y=g_Y(q_Y,q_O),\qquad
q_O=g_O(q_Y,q_O).
\tag{160.2}
$$
在不可约、非退化和有限均值条件下，\(R<1\) 时通常必然灭绝，\(R=1\) 时仍几乎处处灭绝而尾部较慢，\(R>1\) 时存在正的存活概率但仍可能随机灭绝。确定性 FIB 递归本身没有这些随机事件，不能直接套用分枝结论。

资源竞争可令繁殖均值依赖总量 \(N_n=Y_n+O_n\) 与容量 \(K\)，例如
$$
\mathbb E[Z_{n+1}\mid Z_n=z]
=h\!\left(\frac{z_Y+z_O}{K}\right)Mz,
$$
或在标量近似中取
$$
N_{n+1}=RN_n\left(1-\frac{N_n}{K}\right).
$$
正平衡 \(N^*=K(1-1/R)\) 只是特定非线性模型的结果；离散稳定性、随机灭绝和高密度振荡还依赖 \(h\) 的具体形式。竞争主要改变高密度行为，零点附近的入侵阈值仍由线性化矩阵决定。

若环境随代变化，
$$
Z_{n+1}=M_nZ_n,
$$
长期增长由矩阵乘积的 Lyapunov 指数
$$
\gamma=\lim_{n\to\infty}\frac1n
\log\|M_{n-1}\cdots M_0\|
\tag{160.3}
$$
决定，而不是单个平均 Perron 根。标量随机繁殖率的对应量是 \(\gamma=\mathbb E[\log r_n]\)；算术平均率大于一不能保证长期增长。

有限容量或有限状态截断还会改变终态。若零状态是吸收态，且所有非零状态都有正概率到达零，则最终灭绝概率为一，即使低密度线性化为超临界；此时超临界只表示长寿命准稳态。若非吸收转移矩阵为 \(Q\)，最大特征值 \(\theta<1\) 常控制
$$
\Pr(T>n)\asymp C\theta^n.
$$
观测还需另加检测概率，例如
$$
Y_n^{\rm obs}\mid Y_n\sim\operatorname{Binomial}(Y_n,p_Y),
$$
否则观测增长率不能直接等同于真实种群增长率。

本节结论是：FIB 提供类型递归和分支计数；繁殖阈值、灭绝概率、竞争平衡、随机环境增长和观测偏差均由外加分枝或种群动力学决定。

## 161. FIB 路径上的外加信息熵、熵产生与涨落关系

FIB 路径数首先给出组合复杂度。若允许步长 \(1,2\) 且总推进为 \(N\)，则路径集合 \(\Omega_N\) 满足
$$
|\Omega_N|=F_{N+1},
\qquad
h_{\rm comb}
=\lim_{N\to\infty}\frac{\log|\Omega_N|}{N}
=\log\varphi.
\tag{161.1}
$$
这是每单位推进的组合增长率，不是每单位时间的熵率，也不是热力学熵产生。

给定路径概率测度 \(P_N\)，信息熵为
$$
H(P_N)=-\sum_{\omega\in\Omega_N}P_N(\omega)\log P_N(\omega),
$$
并满足
$$
0\le H(P_N)\le\log F_{N+1}.
\tag{161.2}
$$
同一 FIB 递归可配上均匀测度、集中测度、Markov 核或带长程相关的测度，从而产生不同熵率。概率测度不是递归计数自动给出的。

要谈物理熵产生，必须另加允许回退的状态空间、跃迁率、能量、热浴和驱动协议。对正向路径测度 \(P_F\) 与时间反演实验的反向测度 \(P_R\)，定义
$$
\Sigma_F(\omega)
=\log\frac{P_F(\omega)}{P_R(\Theta\omega)}.
\tag{161.3}
$$
离散马尔可夫过程的路径比包含初始分布与逐步转移核：
$$
\Sigma_F
=\log\frac{p_0(x_0)}{p_0^R(\vartheta x_M)}
+\sum_{t=0}^{M-1}
\log\frac{K_t^F(x_t,x_{t+1})}
{K_{M-1-t}^R(\vartheta x_{t+1},\vartheta x_t)}.
\tag{161.4}
$$
连续时间跳跃过程还必须计入停留时间和总逃逸率；不能只把反向矩阵写成正向矩阵的转置。

局部详细平衡是外加物理假设，例如
$$
\log\frac{k^{(r)}_{xy}(\lambda)}
{k^{(r)}_{yx}(\lambda)}
=\beta_r q_{\rm env}^{(r)}(x\to y;\lambda).
\tag{161.5}
$$
若正反测度在时间反演后具有相同支持且归一化，则
$$
\left\langle e^{-\Sigma_F}\right\rangle_F=1,
\qquad
\langle\Sigma_F\rangle_F
=D(P_F\Vert\Theta_*P_R)\ge0.
\tag{161.6}
$$
负熵产生轨迹可以出现，非负性约束的是平均值。若进一步满足相应平稳性与对称性，才可得到 Crooks 或 Evans–Searles 型关系；这些关系需要明确反向实验、奇时间反演变量和协议反序。

单向 FIB 替换若没有合法反向操作，会使反向测度在部分路径上为零，路径熵产生可能为 \(+\infty\)，从而不能把同一个单向核直接当作可逆热力学过程。增加后退跃迁、热浴或删除操作可以建立反向实验，但这些都是新增动力学。把词序倒置也不自动等于物理时间反演。

在平稳连续时间过程上，平均熵产生率可写为
$$
\dot S_{\rm tot}
=\frac{k_B}{2}\sum_{x,y}
(\pi_xk_{xy}-\pi_yk_{yx})
\log\frac{\pi_xk_{xy}}{\pi_yk_{yx}}
\ge0.
\tag{161.7}
$$
若 FIB 位置图存在闭合循环，循环亲和力
$$
\mathcal A
=\log\frac{k_{01}k_{12}k_{20}}
{k_{10}k_{21}k_{02}}
$$
只有在外加非保守驱动或非平衡储库时才能非零。递归的路径计数并不决定 \(\mathcal A\)。

本节结论是：FIB 提供可计数的路径集合；信息熵由概率测度决定，热力学熵产生与涨落定理由正反动力学、详细平衡、支持关系和时间反演合同决定。

## 162. FIB 图族上的外加渗流、连通相变与有限尺寸标度

FIB 递归可组织图族 \(G_n\)，但渗流研究还需给出边界 \(\partial G_n\)、占据配置概率律 \(\mathbb P_p\) 以及构造无限图时的相容嵌入。没有这些数据，就不存在唯一的 FIB 渗流阈值。一般连通、渗流和 jamming 也必须分开：渗流关注随机占据后的簇与跨越，机械 jamming 需要接触约束和刚性，吸附 jamming 需要不可再插入规则。

即使每条边的边缘占据概率均为 \(p\)，联合律仍不可省略。两条串联边同时占据的概率满足
$$
\max(0,2p-1)
\le\mathbb P(X_1=X_2=1)\le p,
\tag{162.1}
$$
独立情形为 \(p^2\)，完全正相关时为 \(p\)。所以平均占据密度和 FIB 递归不足以确定连通概率或相变。

若已给出局部有限无限图及独立边渗流，可定义
$$
\theta(p)=\mathbb P_p(o\leftrightarrow\infty),
\qquad
p_c=\inf\{p:\theta(p)>0\}.
\tag{162.2}
$$
对有限图族首先应研究指定边界之间的跨越概率
$$
R_n(p)=\mathbb P_p(A_n\leftrightarrow B_n).
$$
有限尺寸的 \(R_n\) 转变不自动等于无限图的 \(\theta\) 转变；还需证明边界观测与选定无限极限的对应。

若每级拼接的接口大小有统一上界，可追踪接口连通分割 \(\pi\)。令 \(q_n(\pi;p)\) 为第 \(n\) 级接口具有分割 \(\pi\) 的概率，在子图随机性条件独立时可写成候选递归
$$
q_{n+1}(\pi;p)
=\sum_{\alpha,\beta,\eta}
\mathbf1\{\Phi(\alpha,\beta,\eta)=\pi\}
q_n(\alpha;p)q_{n-1}(\beta;p)w_p(\eta).
\tag{162.3}
$$
\(\Phi\) 由实际拼接和接口识别定义；共享接口顶点只能采样一次。若子图相关或接口无界增长，简单乘积和有限状态闭合都需重新证明。

一个特定的串并联模型可给出可计算阈值：令 \(G_{n+1}\) 由一份 \(G_n\) 与一份 \(G_{n-1}\) 串联所得的支路再复制两份并联，所有边独立以概率 \(p\) 占据。两端连通概率满足
$$
R_0(p)=R_1(p)=p,\qquad
R_{n+1}(p)=1-\bigl(1-R_n(p)R_{n-1}(p)\bigr)^2.
\tag{162.4}
$$
其内部临界常值解为
$$
r_*= \frac{\sqrt5-1}{2},
$$
并由单调性得到两端连通阈值
$$
\lim_{n\to\infty}R_n(p)
=\begin{cases}
0,&p<r_*,\\
r_*,&p=r_*,\\
1,&p>r_*.
\end{cases}
\tag{162.5}
$$
这个黄金比例来自指定可靠性方程，不能推广到所有 FIB 图族。若采用纯串联拼接，则 \(R_{n+1}=R_nR_{n-1}\)，只要长度趋于无穷，阈值为一；相同递归骨架已经允许不同阈值。

在该串并联模型中，临界斜率可满足
$$
D_{n+1}=c(D_n+D_{n-1}),\qquad c=3-\sqrt5,
$$
其增长根
$$
\lambda_+=\frac{c+\sqrt{c^2+4c}}2
$$
控制跨越转变宽度。若最短距离 \(L_n\asymp\varphi^n\)，可定义模型特有的交叉指数
$$
\Delta p_n^{\rm lin}\asymp L_n^{-1/\nu_{\rm cross}},
\qquad
\nu_{\rm cross}=\frac{\log\varphi}{\log\lambda_+}.
\tag{162.6}
$$
这只是端点观测的有限尺寸指数，不自动等于体相相关长度指数，也不证明存在无限簇。

在局部树状近似确实成立时，若 \(B\) 是类型平均后继矩阵，独立占据给出平均后继矩阵 \(pB\)，分枝近似阈值为
$$
p\,\rho(B)=1.
\tag{162.7}
$$
短环、共享接口和长程相关会破坏该近似。簇大小生成函数还需追踪接口分割与共享簇，单个平均簇大小不能在一般拼接下闭合。

本节结论是：FIB 提供图族与接口递归；渗流阈值、无限簇、有限尺寸指数和临界标度由占据联合律、拼接规则、边界、相关性及所选无限极限共同决定，不能由 Fibonacci 数列单独推出。

## 163. FIB 图上的外加随机游走、异常扩散与首次到达

设第 \(n\) 层 FIB 结构实现为有限图
$$
G_n=(V_n,E_n,\Sigma_n),
$$
其中 \(\Sigma_n\) 记录递归拼接和接缝。FIB 只提供图、合法路径和图距离 \(d_F\)；跳转概率、连续时间尺度、随机环境、陷阱、障碍、边界以及图到物理空间的嵌入都必须外加。

给定环境 \(\omega\)，连续时间游走的跳转核 \(J_\omega(x,y)\ge0\) 定义生成元
$$
(\mathcal L_\omega f)(x)
=\sum_{y\ne x}J_\omega(x,y)[f(y)-f(x)].
\tag{163.1}
$$
若只允许沿 FIB 边跳转，则非边关系上的 \(J_\omega\) 为零；允许长程跳转时，核的支撑和尾部属于外加模型。总离开率
$$
\lambda_\omega(x)=\sum_{y\ne x}J_\omega(x,y)
$$
还决定停留时间。非指数或重尾停留时间需另加年龄变量或时间改变过程，不能仍按普通连续时间马尔可夫链处理。淬火环境先固定 \(\omega\) 再取游走平均，退火环境还对 \(\omega\) 平均；两者的扩散指数不必相同。

热核为
$$
p_t^\omega(x,y)=\bigl(e^{t\mathcal L_\omega}\bigr)(x,y).
$$
图距离下的位移可取
$$
R_F^2(t)=\mathbb E[d_F(X_t,X_0)^2].
\tag{163.2}
$$
若另有嵌入 \(\iota:V_\infty\to\mathbb R^m\)，还可取物理位移
$$
R_\iota^2(t)
=\mathbb E[\|\iota(X_t)-\iota(X_0)\|^2].
$$
这两个量只有在嵌入保持相应尺度关系时才可互相替代；长程跳转导致二阶矩发散时，应改用分位数或尾概率。

若球体积满足
$$
|B_F(x,r)|\asymp r^{d_f}
$$
且典型半径为 \(r(t)\asymp t^{1/d_w}\)，则热核可具有次高斯尺度
$$
p_t(x,y)\asymp
t^{-d_f/d_w}
\Phi\!\left(\frac{d_F(x,y)}{t^{1/d_w}}\right),
\tag{163.3}
$$
返回概率的谱维数为
$$
p_t(x,x)\asymp t^{-d_s/2},
\qquad d_s=\frac{2d_f}{d_w}.
$$
若 FIB 替换矩阵的谱半径 \(\rho(M)\) 和空间尺度因子 \(b\) 控制体积增长，在重叠受控等条件下可有
$$
d_f=\frac{\log\rho(M)}{\log b}.
$$
但 \(d_w\) 还取决于外加跳转权重和瓶颈。若有效电阻满足 \(\mathcal R_{\rm eff}(r)\asymp r^\zeta\)，并且电阻网络估计适用，则
$$
d_w=d_f+\zeta.
\tag{163.4}
$$

有限二阶矩、有限均值停留时间、遍历环境、均匀导通率、无尺度增长瓶颈以及体积加倍和 Poincaré 估计共同支持正常扩散
$$
d_w=2,\qquad R_F^2(t)\asymp t.
$$
接缝瓶颈、深陷阱、重尾等待或快速增长的有效电阻可导致次扩散
$$
R_F^2(t)\asymp t^{2/d_w},\qquad d_w>2.
$$
稳定型长程核
$$
J_\omega(x,y)\asymp d_F(x,y)^{-d_f-\alpha},
\qquad 0<\alpha<2
$$
则可能产生超扩散，典型半径为 \(t^{1/\alpha}\)，此时均方位移不再是唯一判据。FIB 多层结构还可能产生时间交叉区间；有限层数据只能给出有效指数，不能自动推出单一全局指数。

给定目标集合 \(A\subseteq V\)，首次到达时间为
$$
T_A=\inf\{t\ge0:X_t\in A\}.
$$
其拉普拉斯变换
$$
u_s(x)=\mathbb E_x[e^{-sT_A}]
$$
在 \(A^c\) 上满足
$$
(s-\mathcal L_\omega)u_s(x)=0,\qquad u_s|_A=1.
\tag{163.5}
$$
若平均首次到达时间有限，则
$$
-\mathcal L_\omega m_A(x)=1,\qquad m_A|_A=0.
\tag{163.6}
$$
有限层图还需指定外边界的吸收、反射、储库或周期条件；吸收生成元的最小 Dirichlet 特征值只在这些边界合同固定后才控制长时生存尾部。

本节结论是：FIB 提供游走的组合支撑；正常或异常扩散、谱维数、首次到达率和长时尾部由跳转核、随机环境、边界和尺度极限决定。

## 164. FIB 网络上的外加 Kuramoto 同步、相位转变与有限尺寸标度

FIB 递归规定网络生成，Kuramoto 动力学规定相位随物理时间演化。设第 \(n\) 层组合图为
$$
G_n=(V_n,E_n),\qquad N_n=|V_n|,
$$
邻接矩阵为 \(A_n\)。若接口识别 \(m_n\) 个顶点，则数量递归是
$$
N_{n+1}=N_n+N_{n-1}-m_n,
$$
而跨块接口矩阵 \(C_n\) 仍需单独给出。物理耦合矩阵 \(W_n\) 可取 \(A_n\)、按平均度归一化的矩阵、随机权重矩阵或其他外加形式。不同归一化会改变同步阈值，不能在未固定 \(W_n\) 时比较耦合常数。

考虑含噪、相移和时延的相位模型
$$
d\theta_i=
\left[
\omega_i+
K\sum_j(W_n)_{ij}
\sin\bigl(\theta_j(t-\tau_{ij})-\theta_i-\alpha_{ij}\bigr)
\right]dt
+\sqrt{2D_i}\,dB_i.
\tag{164.1}
$$
自然频率分布 \(g\)、频率与节点度或递归层级的相关性、时延历史和边界驱动均需外加。递归层数不是物理时间，组合边方向也不自动成为相位驱动力。

全局序参量与边相干度分别为
$$
r_n e^{i\psi_n}
=\frac1{N_n}\sum_{i=1}^{N_n}e^{i\theta_i},
$$
$$
q_n=
\frac{\sum_{i,j}(W_n)_{ij}\cos(\theta_i-\theta_j)}
{\sum_{i,j}(W_n)_{ij}}.
\tag{164.2}
$$
\(r_n\) 低而 \(q_n\) 高的状态可能表示局部相干而非全网同步。还需区分相位一致、频率锁定、部分同步和有噪统计同步。

在无时延、无相移、对称非负耦合及单峰对称频率分布下，非相干态沿 \(W_n\) 最大特征值的第一谐波首先失稳。设噪声强度统一为 \(D\)，则线性阈值可写为
$$
K_{c,n}^{\rm lin}
=
\frac{2}{
\lambda_{\max}(W_n)
\displaystyle\int_{\mathbb R}
\frac{D}{D^2+\nu^2}g(\nu)\,d\nu
}.
\tag{164.3}
$$
零噪声且 \(g(0)>0\) 时化为
$$
K_{c,n}^{\rm lin}
=\frac{2}{\pi g(0)\lambda_{\max}(W_n)}.
$$
Lorentz 频率分布半宽为 \(\Delta\) 时，
$$
K_{c,n}^{\rm lin}
=\frac{2(D+\Delta)}{\lambda_{\max}(W_n)}.
$$
这些是非相干态的线性失稳条件，不自动证明稳定锁频分支或非零无限体序参量。稀疏有限网络还需核对失稳模态是否局限在接口或高连接节点。

在无噪、无时延、无相移的对称吸引模型中，锁定态
$$
\theta_i(t)=\Omega t+\phi_i
$$
满足 \(\Omega=\bar\omega_n\) 和
$$
\delta\omega_i
=K\sum_j(W_n)_{ij}\sin(\phi_i-\phi_j).
$$
对任意非空真子集 \(S\subset V_n\)，必要割条件为
$$
\left|\sum_{i\in S}\delta\omega_i\right|
\le
K\sum_{\substack{i\in S\\j\notin S}}(W_n)_{ij}.
\tag{164.4}
$$
因此
$$
K\ge
\max_{\varnothing\ne S\subsetneq V_n}
\frac{\left|\sum_{i\in S}\delta\omega_i\right|}
{\sum_{i\in S,j\notin S}(W_n)_{ij}}
$$
是锁频的必要下界。充分条件还需相位差范围、图连通性和非线性固定点的具体估计。拉普拉斯谱隙只能控制某些线性扰动衰减，不能替代割条件或证明全局锁频。

有限尺寸标度必须固定 \(W_n\)、频率抽样、边界和观测量。若 \(\lambda_{\max}(W_n)\) 或谱隙随 FIB 层级变化，阈值变化可能只是归一化效应；\(r_n\) 的有限尺寸非零也可能来自有限粒子涨落。存在时延、相移、多峰频率或非对称耦合时，分岔可能是振荡、簇同步或迟滞，而非简单的连续全局同步。

本节结论是：FIB 提供网络层级和接口谱；同步阈值、锁频、簇相干及有限尺寸临界行为由物理耦合矩阵、频率分布、噪声、时延和边界决定。

## 165. FIB 细胞复形上的外加离散规范场、环流与拓扑缺陷

FIB 递归在本节只承担胞腔和接缝的组合组织。设第 \(n\) 层实现为有限细胞复形 \(K_n\)，并明确每个二维胞腔的有序边界路径。胞腔计数或邻接关系不能替代非阿贝尔边界中的输运次序。规范群、边变量、作用量、边界和连续极限均需外加。

选紧李群 \(G\)，对每条有向边 \(e:v\to w\) 赋予
$$
U_e\in G,\qquad U_{\bar e}=U_e^{-1}.
$$
顶点规范变换 \(g_v\in G\) 作用为
$$
U_e\longmapsto g_wU_eg_v^{-1}.
\tag{165.1}
$$
沿有向路径 \(p=e_1\cdots e_m\) 的有序输运为
$$
H_p=U_{e_m}\cdots U_{e_1}.
$$
闭合路径的输运只按共轭变换；在有限维酉表示 \(\rho\) 下，Wilson 回路
$$
W_\rho(p)=\frac1{\dim\rho}\operatorname{tr}\rho(H_p)
\tag{165.2}
$$
是规范不变量。

对二维胞腔 \(f\)，令
$$
H_f=H_{\partial f}.
$$
它是群值离散曲率。平坦连接满足 \(H_f=1_G\) 对所有 \(f\) 成立；但局部平坦不等于所有全局回路平凡。对连通复形，在适当边界和规范等价条件下，平坦连接的模空间可由
$$
\operatorname{Hom}(\pi_1(K_n),G)/G
$$
描述。因而 FIB 的局部接缝结构不能单独决定全局 holonomy。

可选 Wilson 型作用量
$$
S[U]=
\sum_{f\in K_n^{(2)}}\beta_f
\left(
1-\frac1{\dim\rho}\operatorname{Re}\operatorname{tr}\rho(H_f)
\right)
\tag{165.3}
$$
具有规范不变性，但 \(\beta_f\)、边界标架和动力学积分均属于外加模型。开放路径只有在端点标架或端点物质场也被指定时才可成为规范不变量。

在 \(G=U(1)\) 时写 \(U_e=e^{ia_e}\)，对主值面通量
$$
\phi_f=\operatorname{Arg}H_f\in(-\pi,\pi],
\qquad
(\delta a)_f=\phi_f+2\pi m_f,
\qquad m_f\in\mathbb Z.
\tag{165.4}
$$
对闭合二维胞腔链 \(\Sigma\)，离散 Stokes 关系给出
$$
Q(\Sigma)
=\frac1{2\pi}\langle\phi,\Sigma\rangle
=-\langle m,\Sigma\rangle\in\mathbb Z.
\tag{165.5}
$$
整数性来自紧致 \(U(1)\) 与闭合条件，不来自 FIB 计数。若复形具有三维胞腔，可定义
$$
q_c=\frac1{2\pi}(\delta\phi)_c=-(\delta m)_c\in\mathbb Z.
$$
闭合三维链上的总电荷满足相应边界平衡；若原有 FIB 结构没有三胞腔，就不存在这类电荷而无需强行引入。

环流、局部曲率和拓扑缺陷需分别定义。非零面通量不自动是涡旋，非阿贝尔曲率的迹也不自动是量子化电荷。若再加入带电复标量场和相位单值性，才能用相位绕数定义缺陷；保持整数拓扑数还需避免穿越主值分支或规定缺陷穿越规则。连续主丛、陈类或连续规范场的解释还需给出相容的几何重建。

本节结论是：FIB 提供细胞复形与有序边界的组合骨架；规范不变量、曲率、Wilson 环、拓扑电荷和缺陷统计由外加群、边变量、作用量、边界和几何极限决定。

## 166. FIB 路径上的外加随机输运、主方程与 Boltzmann—流体极限

设 FIB 原子序列的递归更新为
$$
a_{n+1}=\mathsf R(a_n,a_{n-1}),
$$
并令单粒子状态为 \(z=(n,\xi)\)，其中 \(\xi=(v,\alpha)\) 包含速度和内部类型。递归可以作为状态的一部分，但它本身不规定概率守恒、质量、动量或能量守恒。

连续时间微观跳转核 \(K_{nm}^{\varepsilon}(\xi,d\eta)\) 满足有限逃逸率
$$
\Lambda_n^\varepsilon(\xi)
=\sum_{m\ne n}\int K_{nm}^{\varepsilon}(\xi,d\eta)<\infty.
$$
单粒子分布的主方程可写为
$$
\partial_t p_n(t,\xi)
=
\sum_m\int p_m(t,\eta)K_{mn}^{\varepsilon}(\eta,d\xi)
-\Lambda_n^\varepsilon(\xi)p_n(t,\xi)
+\mathcal C_n[p](\xi)+S_n-R_n.
\tag{166.1}
$$
其中 \(\mathcal C_n\) 是碰撞项，\(S_n,R_n\) 是外部注入和移除。最近邻核、长程核、边界反射与吸收均需单独指定。

对二体碰撞的 Boltzmann—Grad 标度
$$
N\sigma^{d-1}\to\lambda,
$$
若初始传播混沌、碰撞率有限且三体同时碰撞可忽略，则单粒子极限可具有
$$
(\partial_t+v\cdot\nabla_x)f
=\mathcal L_{\rm ext}^*f+Q(f,f)+S.
\tag{166.2}
$$
若外部跳转依赖多粒子联合状态，上述闭合不再自动成立，必须保留 BBGKY 层级。

碰撞不变量 \(\phi_\alpha(v)\) 满足
$$
\phi_\alpha(v)+\phi_\beta(v_*)
=\phi_\gamma(v')+\phi_\delta(v_*')
$$
在所有允许反应上成立时，碰撞项满足
$$
\sum_\alpha\int\phi_\alpha(v)Q_\alpha(f,f)(v)\,dv=0.
\tag{166.3}
$$
质量、动量和能量只有在外部跳转核也保持相应量或显式记录外力通量时才是全系统守恒量；FIB 标签不是自动守恒量。

对任意观测量 \(\phi_n(\xi)\)，外部跳转贡献为
$$
\mathcal I_\phi^{\rm ext}
=
\sum_{n,m}\iint
f_n(\xi)K_{nm}^{\varepsilon}(\xi,d\eta)
[\phi_m(\eta)-\phi_n(\xi)].
\tag{166.4}
$$
因此矩方程还包含边界通量、碰撞矩、源汇和外部输运矩。若存在平衡测度 \(\pi\) 并满足详细平衡，则相对熵具有耗散形式
$$
\frac{d}{dt}H(f\mid\pi)
=-D_{\rm jump}-D_{\rm coll}
+\mathcal W_{\rm source}
+\mathcal W_{\rm boundary},
\tag{166.5}
$$
其中两项耗散非负；没有详细平衡时，驱动输运会贡献熵流，不能直接宣称熵单调下降。

设碰撞时间、外部跳转时间和宏观输运时间分别为 \(\tau_c,\tau_j,\tau_s\)，可用
$$
\mathrm{Kn}=\frac{\tau_c}{\tau_s},
\qquad
\mathrm{Da}_j=\frac{\tau_s}{\tau_j}
$$
描述尺度分离。典型缩放为
$$
\partial_t f^\varepsilon+v\cdot\nabla_x f^\varepsilon
=
\varepsilon^{-1}Q(f^\varepsilon,f^\varepsilon)
+\varepsilon^{-\gamma}\mathcal L_{\rm ext}^{*,\varepsilon}f^\varepsilon
+S^\varepsilon.
\tag{166.6}
$$
不同 \(\gamma\) 产生不同极限：快速碰撞可先导向局部平衡，外部跳转与碰撞同阶时会改变局部平衡，长程重尾核则可能产生分数阶输运。要得到扩散、漂移—扩散或 Euler/Navier–Stokes 型方程，还需紧性、矩界、边界层和初始层的证明。

本节结论是：FIB 提供微观可达路径与内部标签；主方程、碰撞守恒、熵耗散以及 Boltzmann—流体极限由跳转核、碰撞律、尺度分离、边界和源汇决定。

## 167. FIB 关系网络上的外加主动物质、定向运动与集体相变

FIB 递归生成关系网络
$$
G_n=(V_n,E_n),
$$
但组合路径只描述可达次序。主动速度、空间嵌入、极性记忆、排斥、容量、对齐作用、噪声和物理时间均需外加。递归层数不是时间，组合边方向也不自动成为主动驱动力。

若指定嵌入 \(\mathbf r:V_n\to\mathbb R^d\)，二维主动布朗粒子的外加模型可写为
$$
d\mathbf x_i=
\left[
v_0\mathbf p_i-\mu\nabla W_{G_n}(\mathbf x_i)
-\mu\sum_{j\ne i}\nabla U(\mathbf x_i-\mathbf x_j)
+\mu\mathbf f_i^{\rm ext}
\right]dt
+\sqrt{2D_t}\,d\mathbf B_i,
$$
$$
d\theta_i=
\left[
\kappa\sum_{j\ne i}K_{ij}\sin(\theta_j-\theta_i)
+h_i\sin(\theta_i^{\rm ext}-\theta_i)
+\omega_i^{\rm wall}
\right]dt
+\sqrt{2D_r}\,dB_i^\theta,
\tag{167.1}
$$
其中 \(\mathbf p_i=(\cos\theta_i,\sin\theta_i)\)。持续长度 \(\ell_p=v_0/D_r\) 只在无弯道、阻塞和交汇修正时具有直接意义；网络中的净漂移和长期扩散率还取决于通道几何和节点规则。

在抽象图上，也可令粒子占据节点 \(v\)，容量为 \(m_v\)，并用有向跃迁率
$$
r_i(v\to w)
=
\frac{c_{vw}}{a_v}\mathbf1_{\{n_w<m_w\}}
\exp\left[
-\frac{\beta\Delta U_i}{2}
+\frac{\chi}{2}\mathbf p_i\cdot
\frac{\mathbf r_w-\mathbf r_v}{\ell_0}
+\frac{A_{vw}}2
\right]
\tag{167.2}
$$
描述排斥、主动偏置和非保守驱动。对齐权重、主动偏置、排斥能和角噪声必须分开登记；若改变更新顺序或冲突消解规则，得到的是不同动力学。

极化序参量与网络边净流可定义为
$$
P_N=\left|\frac1N\sum_{i=1}^N\mathbf p_i\right|,
\qquad
J_{vw}=\frac{N_{v\to w}-N_{w\to v}}{NT}.
\tag{167.3}
$$
极化、净输运和局部密度聚集是不同观测量；高极化不必产生宏观净流，局部流也不必产生全网极化。

在均匀、各向同性、充分混合的近似下，连续极化场可写成
$$
\partial_t\mathbf P
=a(\rho)\mathbf P-b|\mathbf P|^2\mathbf P
-D_P\nabla^2\mathbf P+\boldsymbol\xi,
\tag{167.4}
$$
其中 \(a(\rho)\) 的符号变化给出平均场极化失稳，\(b>0\) 控制饱和。FIB 网络上的实际线性模态应由外加耦合矩阵和边界谱替代连续 Laplacian；高层接口瓶颈可能使局部群先同步而全网仍无序。有限尺寸下 \(P_N>0\) 还可能只是涨落偏置，需比较 \(N_n\)、边界和时间窗口。

主动物质相分离（MIPS）需要持续推进、排斥、密度依赖有效速度或等价的聚集机制。一个标量密度近似可写为
$$
\partial_t\rho
=-\nabla\cdot\bigl[v(\rho)\rho\,\mathbf p\bigr]
+D_\rho\nabla^2\rho+\zeta,
$$
或在消去极性后得到有效通量
$$
\mathbf J
=-D_{\rm eff}(\rho)\nabla\rho+\cdots .
$$
只有在 \(D_{\rm eff}\) 变号、有效化学势满足相容性以及噪声和边界条件合适时，才可讨论密度相分离。FIB 的节点度或递归层级不自动提供密度依赖速度。

主动物质通常破坏详细平衡。若跃迁存在有向亲和力 \(A_{vw}\)，稳态边流可非零；若所有主动偏置、对齐和外场消失，才可能退化为与容量权重相容的被动平衡。因而 flocking、MIPS、堵塞和普通渗流需要分别报告极性、密度、接触和连通观测。

本节结论是：FIB 提供主动物质的关系网络和路径约束；主动输运、极化、集体同步、MIPS 及有限尺寸相变由空间嵌入、驱动、相互作用、噪声、边界和更新规则决定。

## 168. FIB 网络上的吸收态临界与定向渗流型统计

设 FIB 给出递归图族
$$
G_N=(V_N,E_N)
$$
及其合法转移关系。递归只确定连接、允许操作和层级；转移速率、活动变量、噪声、初始分布、边界和无限系统极限都需外加。必须区分静态渗流、随时间更新的吸收态和 jamming：跨越簇、无合法运动的堵塞态以及活动最终熄灭并非同一事件。

令 \(\Omega_N\) 为合法构型空间，\(\mathcal L_N\) 为 FIB 允许的转移。外加连续时间速率
$$
q_N(x,y)\ge0,\qquad
(x,y)\notin\mathcal L_N\Longrightarrow q_N(x,y)=0
$$
给出主方程
$$
\frac{dP_N(x,t)}{dt}
=\sum_{y\ne x}
[P_N(y,t)q_N(y,x)-P_N(x,t)q_N(x,y)].
\tag{168.1}
$$
吸收集合为
$$
\mathcal A_N
=\{x:q_N(x,y)=0\ \text{对所有 }y\ne x\}.
\tag{168.2}
$$
它取决于速率和约束，不由静态 FIB 图单独决定。

一个外加活动过程可令节点变量 \(\eta_v\in\{0,1\}\)，失活率为 \(\mu_v\)，激活率为
$$
h_v+\lambda\sum_uK_{uv}\eta_u,
$$
其中 \(K\) 仅在允许传播的关系上非零，\(h_v\) 是自发激活率。\(h_v=0\) 时，全零构型是吸收态。其一阶矩满足
$$
\frac{d\langle\eta_v\rangle}{dt}
=-\mu_v\langle\eta_v\rangle
+h_v(1-\langle\eta_v\rangle)
+\lambda\sum_uK_{uv}
\langle(1-\eta_v)\eta_u\rangle.
\tag{168.3}
$$
二点相关使方程不闭合；把相关项替换为一阶矩乘积只是平均场近似，不能直接当作真实临界点。

活动密度可定义为
$$
\rho_N(t)=\frac1{|V_N|}\sum_{v\in V_N}\mathbb E[\eta_v(t)].
\tag{168.4}
$$
有限、无源系统通常最终进入吸收态，因此活动相必须通过先取无限系统再取长时间的次序定义，例如
$$
\rho_{\rm st}(\lambda)
=\lim_{t\to\infty}\lim_{N\to\infty}\rho_N(t).
\tag{168.5}
$$
交换两个极限、使用准平稳分布或使用有限种子存活概率，得到的是不同观测量。持续源 \(h_v>0\) 会破坏全零吸收性，转而定义受迫响应。

对局域、短程、单一非负活动场、连续转变且没有额外守恒慢变量或特殊对称性的模型，接触过程的随机时空路径可成为 directed percolation 型粗粒化的候选。条件性有效方程可写为
$$
\partial_t a
=D\nabla^2a+ra-ua^2+\sqrt{2\Gamma a}\,\xi,
\qquad u,\Gamma>0,
\tag{168.6}
$$
其中零活动处漂移与噪声均消失，以保持吸收性。FIB 长程边、层级瓶颈、度异质性、相关无序或多个相互作用吸收态都可能改变普适类。

若存在连续临界点 \(\lambda_c\)，令 \(\Delta=(\lambda-\lambda_c)/\lambda_c\)，可检验
$$
\rho_{\rm st}\sim\Delta^\beta,\qquad
\xi_\perp\sim|\Delta|^{-\nu_\perp},\qquad
\xi_\parallel\sim|\Delta|^{-\nu_\parallel},
\tag{168.7}
$$
以及有限尺寸形式
$$
\rho_N(\Delta)
=N^{-\beta/\nu_\perp}
\mathcal F(\Delta N^{1/\nu_\perp},tN^{-\nu_\parallel/\nu_\perp}).
\tag{168.8}
$$
这些指数只有在给定几何、边界、时间更新和极限后才有意义。静态渗流阈值、jamming 阈值和吸收态临界点不能由同一 FIB 数量递推自动识别。

本节结论是：FIB 提供活动传播的合法关系与递归图族；吸收态、定向渗流型临界、序参量和有限尺寸指数由外加更新率、噪声、边界、相关性及极限次序决定。

## 169. FIB 路径的聚合物构象统计、熵弹性与回转半径

将一条 FIB 路径解释为聚合物链时，FIB 只提供步长词
$$
w_N=(w_1,\ldots,w_N)
$$
和相邻连接关系。物理构象由
$$
\mathbf r_i-\mathbf r_{i-1}=b_i\mathbf u_i,
\qquad |\mathbf u_i|=1,
\qquad b_i=b(w_i)
\tag{169.1}
$$
给出；空间维数、键长映射、弯曲能、排斥、温度和边界均为外加。固定 Fibonacci 词的构象统计与允许词本身随机变化的退火统计也必须区分。

一个可选的链能量为
$$
H_w=\sum_{i=1}^{N-1}\kappa_i(1-\mathbf u_i\cdot\mathbf u_{i+1})
+H_{\rm ev}+H_{\rm attr}+H_{\rm conf},
\tag{169.2}
$$
其中各项分别描述弯曲、排斥、吸引和外部限制。固定 \(\mathbf r_0=0\)，在温度 \(T\) 和外力 \(\mathbf f\) 下，
$$
Z_N(\mathbf f\mid w_N)
=\int d\Gamma_w\,
e^{-\beta(H_w-\mathbf f\cdot\mathbf R)},
\qquad
\mathbf R=\sum_{i=1}^Nb_i\mathbf u_i.
\tag{169.3}
$$
自由能和平均伸长为
$$
G_N(\mathbf f)=-k_BT\log Z_N(\mathbf f),
\qquad
\langle\mathbf R\rangle_{\mathbf f}
=-\nabla_{\mathbf f}G_N.
$$
端距约束使用
$$
Z_N(\mathbf R\mid w_N)
=\int d\Gamma_w\,
\delta^{(d)}\!\left(\mathbf R-\sum_i b_i\mathbf u_i\right)e^{-\beta H_w}.
\tag{169.4}
$$
构象熵必须相对于明确的测度和参考体积定义；它不是 \(\log\) FIB 词数的自动同义词。

自由连接、各向同性且无相互作用时，令
$$
B_N=\sum_{i=1}^Nb_i^2.
$$
有精确关系
$$
\langle\mathbf R\rangle=0,\qquad
\langle R^2\rangle=B_N.
\tag{169.5}
$$
当 \(\max_i b_i^2/B_N\to0\) 时，中心区域近似高斯：
$$
p_N(\mathbf R)
\simeq
\left(\frac d{2\pi B_N}\right)^{d/2}
\exp\!\left(-\frac{dR^2}{2B_N}\right).
\tag{169.6}
$$
因而小端距的熵弹性自由能为
$$
A_N(\mathbf R)-A_N(0)
\simeq\frac{dk_BT}{2B_N}R^2,
$$
弱力下
$$
\mathbf f\simeq\frac{dk_BT}{B_N}\mathbf R.
\tag{169.7}
$$
接近完全拉直时，高斯公式失效；有限链的恒力系综和固定端距系综也不能混用。

回转半径定义为
$$
R_g^2=\frac1{N+1}\sum_{i=0}^N|\mathbf r_i-\mathbf r_{\rm cm}|^2
=\frac1{(N+1)^2}\sum_{0\le i<j\le N}|\mathbf r_i-\mathbf r_j|^2.
$$
自由连接链满足
$$
\left\langle|\mathbf r_j-\mathbf r_i|^2\right\rangle
=\sum_{k=i+1}^jb_k^2,
$$
从而
$$
\left\langle R_g^2\right\rangle
=\frac1{(N+1)^2}
\sum_{k=1}^Nk(N+1-k)b_k^2.
\tag{169.8}
$$
FIB 字母频率可以影响 \(b_i\) 的平均统计，但不单独决定自避链或半柔性链的标度指数。加入自避作用后，可能出现
$$
R_g\sim N^\nu,\qquad
\nu=\nu(d)
$$
的普适标度；其维数、排斥、弯曲、链序相关和有限尺寸修正需由具体模型确定。标准 Fibonacci 词的低因子复杂度也不能推出聚合物构象熵为零，因为固定词仍可拥有连续或指数多的空间构象。

本节结论是：FIB 提供聚合物键序列和连接骨架；配分函数、熵弹性、回转半径、自避标度和有限尺寸效应由键长、构象测度、温度及相互作用决定。

## 170. FIB 细胞复形上的外加离散曲率、测地线与几何聚焦

FIB 递归只提供细胞、邻接和接缝组合。要讨论曲率和测地线，必须另加边长、角度、面权、体积权、边界以及向连续几何收敛的细化规则。组合曲率不能在未指定度量时直接解释为物理曲率。

对二维多面体型细胞复形 \(K\)，若每条边和每个面都已赋予欧氏几何，使面角 \(\theta_{f,v}\) 有定义，则顶点角缺陷为
$$
\kappa(v)
=2\pi-\sum_{f\ni v}\theta_{f,v}.
\tag{170.1}
$$
边界顶点的定义需减去相应外角。若各面为正多边形且只使用组合数据，可得到离散组合曲率
$$
\kappa_{\rm comb}(v)
=1-\frac{\deg(v)}2+\sum_{f\ni v}\frac1{|f|},
\tag{170.2}
$$
但它只在对应的标准胞腔几何中才与角缺陷成比例。

在闭合有限二维复形上，离散 Gauss–Bonnet 为
$$
\sum_v\kappa(v)=2\pi\chi(K).
\tag{170.3}
$$
边界存在时还要加边界测地曲率项。FIB 递归改变顶点、边和面计数，可能改变 Euler 示性数；若接缝识别或边界处理不明确，不能从单纯 Fibonacci 数量递推推出总曲率。

给定边长 \(\ell_e>0\)，离散路径长度为
$$
L(\gamma)=\sum_{e\in\gamma}\ell_e,
$$
测地线是给定端点间使 \(L\) 最小的路径。组合最短路只有在所有边长相同且不存在嵌入交叉时才与物理测地线一致。等距嵌入、面内折线和跨接缝跳跃都会改变最短路径。若边权被解释为代价或折射率，需明确它是否满足三角不等式及是否允许长程边。

离散标量场的加权 Laplacian 可写为
$$
(\Delta_\ell f)(v)
=\frac1{\mu_v}\sum_{w\sim v}c_{vw}[f(w)-f(v)],
\qquad c_{vw}=c_{wv}>0.
\tag{170.4}
$$
它同时控制热核
$$
p_t=e^{t\Delta_\ell}
$$
和离散波动方程
$$
\partial_t^2u+c^2(-\Delta_\ell)u=0.
\tag{170.5}
$$
权重 \(c_{vw}\)、体积 \(\mu_v\) 与边界决定热扩散、波速和谱隙；FIB 邻接矩阵本身不足以决定它们。

在有度量收敛、局部形状正则和体积控制时，可研究 \(K_n\) 的图度量、热核和 Laplacian 是否收敛到连续流形对象。若曲率集中在递归接缝，热核可能出现瓶颈或多尺度交叉；若边长缩放不一致，有限图的组合曲率不会给出唯一连续极限。测地线偏离、热核聚焦或波前会聚只有在定义了度量、初始数据和边界后才可计算。

本节结论是：FIB 提供离散胞腔和接缝结构；曲率、Gauss–Bonnet、测地线、热核、波传播与几何聚焦由外加度量、权重、边界和连续极限决定。

## 171. FIB 网络上的外加线性响应、Green–Kubo 与涨落耗散

FIB 在本节只提供状态与通道的组合结构。时间、转移率、平衡测度、能量、外场耦合、时间反演和输运量均需外加。线性响应和涨落耗散关系来自这些结构的相容性，而不是递归关系本身。

设有限状态不可约连续时间过程的生成元为
$$
(\mathcal Lf)(x)
=\sum_{c:s(c)=x}k(c)[f(t(c))-f(x)],
\qquad P_t=e^{t\mathcal L}.
\tag{171.1}
$$
外加能量 \(H\)、温度 \(T\) 和 Gibbs 测度
$$
\pi(x)=Z^{-1}e^{-\beta H(x)},
\qquad \beta=(k_BT)^{-1}.
$$
若每条通道都有反向通道并满足
$$
\pi(s(c))k(c)=\pi(t(c))k(\bar c),
\tag{171.2}
$$
则得到详细平衡；速度等奇变量存在时还需指定时间反演映射 \(\theta\)。原 FIB 组合若没有反向通道，不能直接宣称平衡。

外场 \(\varepsilon h(t)\) 通过生成元扰动
$$
\mathcal L_{\varepsilon h(t)}
=\mathcal L+\varepsilon h(t)\mathcal V+O(\varepsilon^2)
$$
定义。对观测量 \(A\)，从平稳测度出发的一阶响应为
$$
\mathbb E_{\varepsilon h}[A(X_t)]-\langle A\rangle_\pi
=\varepsilon\int_0^th(s)R_{A,\mathcal V}(t-s)\,ds+o(\varepsilon),
\tag{171.3}
$$
其中
$$
R_{A,\mathcal V}(\tau)
=\langle g_{\mathcal V},P_\tau\delta A\rangle_\pi,
\qquad
g_{\mathcal V}=\mathcal V^\dagger1.
\tag{171.4}
$$
因此响应由实际扰动算子产生的 \(g_{\mathcal V}\) 与未扰动相关函数共同决定；不能仅凭“施加了外场”就指定响应量。

若外场与 \(B\) 共轭，\(H_h=H-hB\)，且扰动后生成元以相应 \(\pi_h\) 为平稳测度，则有
$$
R_{AB}(\tau)
=-\beta\frac{d}{d\tau}
C_{AB}(\tau),
\qquad
C_{AB}(\tau)=
\langle\delta B,P_\tau\delta A\rangle_\pi.
\tag{171.5}
$$
相关衰减时的静态易感率为
$$
\chi_{AB}^{\rm stat}
=\beta\,\operatorname{Cov}_\pi(A,B).
\tag{171.6}
$$
这些式子要求明确共轭耦合；非共轭扰动、非平衡稳态和粗粒化变量不能自动使用同一形式。

对输运通道 \(c\) 赋予反向变号的增量 \(d_\alpha(c)\)，累计流为
$$
Q_\alpha(T)=
\sum_{\text{区间 }[0,T]\text{ 内发生的 }c}
d_\alpha(c).
$$
在平衡、时间平移不变、相关函数可积且边界项消失的条件下，Green–Kubo 型输运系数为
$$
L_{\alpha\beta}
=\frac1{k_BT}
\int_0^\infty
\langle J_\alpha(t)J_\beta(0)\rangle_\pi\,dt.
\tag{171.7}
$$
有限 FIB 图的边界流、周期闭合和开放储库都会增加边界项；若相关衰减慢于可积速度，积分可能发散或需要尺寸依赖重整化。

频域中，对因果响应核和双边涨落谱
$$
\chi_{BB}(\omega)=\int_0^\infty e^{i\omega t}R_{BB}(t)\,dt,
$$
$$
S_{BB}(\omega)=\int_{-\infty}^{\infty}e^{i\omega t}
\mathbb E_\pi[\delta B(X_t)\delta B(X_0)]\,dt,
$$
在相应分部积分条件下有
$$
\operatorname{Im}\chi_{BB}(\omega)
=\frac{\beta\omega}{2}S_{BB}(\omega).
\tag{171.8}
$$
非平衡驱动、主动流、磁场反演和非平稳递归协议会增加熵流或反对称响应，必须另行写出，不能把平衡 FDT 当作普适恒等式。

本节结论是：FIB 提供状态和通道的组合骨架；响应核、Green–Kubo 输运系数和涨落耗散关系由平衡测度、详细平衡、扰动耦合、时间反演与相关衰减条件决定。

## 172. FIB 路径上的量子通道、测量退相干与信息流

FIB 路径取得量子含义，需要指定每个接口的 Hilbert 空间、节点操作、串并行规则、系统—环境分区以及环境记忆。FIB 长度、节点数和分支数不能直接解释为 Hilbert 空间维数或独立量子自由度数。图上的重复调用也不等于未知量子态复制，因为不存在对任意未知 \(\rho\) 的通用通道
$$
\rho\longmapsto\rho\otimes\rho.
$$

有限维节点操作是完全正映射
$$
\Phi:\mathcal B(\mathcal H_{\rm in})
\to\mathcal B(\mathcal H_{\rm out}),
$$
并可写成 Kraus 形式
$$
\Phi(\rho)=\sum_aK_a\rho K_a^\dagger.
\tag{172.1}
$$
保迹量子通道满足
$$
\sum_aK_a^\dagger K_a=I;
$$
若仅有 \(\le I\)，则是某个测量结果或成功分支的迹不增操作。沿串行 FIB 路径的整体 Kraus 算子为
$$
C_{\boldsymbol a}
=K^{(n)}_{a_n}\cdots K^{(1)}_{a_1},
\qquad
\Phi_p(\rho)=
\sum_{\boldsymbol a}C_{\boldsymbol a}\rho C_{\boldsymbol a}^\dagger.
\tag{172.2}
$$
并行组合使用张量积；串行复合和并行张量具有不同的维数和环境含义。

测量需要量子仪器 \(\{\mathcal I_m\}_m\)：
$$
\mathcal I_m(\rho)=\sum_aK_{ma}\rho K_{ma}^\dagger,
\qquad
\sum_m\mathcal I_m\ \text{保迹}.
\tag{172.3}
$$
结果概率与条件态为
$$
p_m=\operatorname{Tr}\mathcal I_m(\rho),
\qquad
\rho_m=\frac{\mathcal I_m(\rho)}{p_m}.
$$
保留经典记录 \(X\) 得到
$$
\rho_{XS}
=\sum_mp_m|m\rangle\langle m|_X\otimes\rho_m,
\tag{172.4}
$$
丢弃记录则只得到 \(\sum_m\mathcal I_m(\rho)\)。外部随机选择路径、测量分支和相干控制是三种不同机制，不能都按路径数平均。

环境退相干可由等距嵌入
$$
\Phi(\rho)=\operatorname{Tr}_E(V\rho V^\dagger),
\qquad V^\dagger V=I
$$
表示。若
$$
V|i\rangle=|i\rangle\otimes|e_i\rangle,
$$
则
$$
\rho'_{ij}=\rho_{ij}\gamma_{ij},
\qquad
\gamma_{ij}=\langle e_j|e_i\rangle.
\tag{172.5}
$$
指定相干项对所有输入完全消失，当且仅当相应环境态正交，即 \(\gamma_{ij}=0\)。一般退相干强度由环境重叠矩阵和路径共享环境的联合结构决定；独立环境与记忆环境不会给出相同通道。

测量记录与系统的总信息可用互信息
$$
I(X:S)=S(\rho_X)+S(\rho_S)-S(\rho_{XS})
$$
表征。完全丢弃记录可能使条件信息不可恢复；仅凭 FIB 路径频率不能确定量子互信息。若讨论纠缠，还需另给物理张量分解；地址直和分解不能替代子系统张量积。

量子通道的时间反演或恢复还需指定参考态、伴随通道或 Petz 型恢复条件。一般通道不可逆；FIB 路径倒序也不自动给出物理逆通道。若不同路径共享环境，路径混合会留下相干交叉项；若环境记录完全区分路径，交叉项被压制。两种极限的次序和环境记忆时间都属于外加参数。

本节结论是：FIB 提供量子操作的组合语法和路径组织；完全正性、测量概率、退相干、互信息、纠缠和恢复条件由 Hilbert 分解、Kraus 算子、环境、记录及时间反演实现决定。

## 173. FIB 图上的外加自旋系统、Gibbs 测度与相变

将 FIB 图记为
$$
G_{\rm FIB}=(V,E_{\rm FIB}).
$$
FIB 邻接只规定组合关系；自旋相互作用、温度、外场、边界和热力学极限均需外加。可选物理耦合图 \(G_J\) 与对称耦合
$$
J_{ij}=J_{ji},\qquad J_{ii}=0,
$$
即使取 \(J_{ij}=J_0\mathbf1_{\{\{i,j\}\in E_{\rm FIB}\}}\)，也仍是一项模型假设。行归一化、度归一化和原始边权对应不同 Hamiltonian，不能在未固定归一化时比较临界温度。

有限区域 \(\Lambda\) 上的 Ising Hamiltonian 为
$$
H_\Lambda^\tau(s)
=-\sum_{\substack{\{i,j\}\in E_J\\i,j\in\Lambda}}J_{ij}s_is_j
-\sum_{\substack{i\in\Lambda,j\notin\Lambda\\\{i,j\}\in E_J}}
J_{ij}s_i\tau_j
-\sum_{i\in\Lambda}h_is_i,
\qquad s_i\in\{-1,+1\}.
\tag{173.1}
$$
配分函数与 Gibbs 测度为
$$
Z_\Lambda^\tau
=\sum_s e^{-\beta H_\Lambda^\tau(s)},
\qquad
\mu_\Lambda^\tau(s)=\frac{e^{-\beta H_\Lambda^\tau(s)}}{Z_\Lambda^\tau},
\qquad
\beta=(k_BT)^{-1}.
\tag{173.2}
$$
Potts 模型只需把 \(s_i\) 换成 \(q\) 种颜色并将耦合项换成 \(\mathbf1_{\{\sigma_i=\sigma_j\}}\)，但 \(q=2\) 时的耦合归一化与 Ising 约定仍须区分。

磁化与连通相关为
$$
m_i=\langle s_i\rangle,\qquad
C_{ij}=\langle s_is_j\rangle-\langle s_i\rangle\langle s_j\rangle.
$$
有限体积恒等式
$$
\frac{\partial\log Z_\Lambda}{\partial h_i}=\beta m_i,
\qquad
\frac{\partial m_i}{\partial h_j}=\beta C_{ij}
\tag{173.3}
$$
把静态响应与平衡涨落联系起来。单位顶点磁化率为
$$
\chi_\Lambda=\frac{\beta}{|\Lambda|}
\sum_{i,j\in\Lambda}C_{ij}.
\tag{173.4}
$$
它不决定自旋翻转动力学或弛豫时间；后者还需指定 Glauber、Metropolis 或其他更新核。

相变须先规定系统增长：固定无限 FIB 图上的 \(\Lambda_n\uparrow V\)，或一列有限 FIB 图 \(G_n\) 及其局部极限、边界和耦合缩放。无限体积 Gibbs 测度应满足 DLR 条件，而不是把有限配分函数直接外推到无限图。跨边界耦合量
$$
B_J(\Lambda)
=\sum_{\substack{i\in\Lambda\\j\notin\Lambda}}|J_{ij}|
$$
若满足 \(B_J(\Lambda_n)/|\Lambda_n|\to0\)，则不同边界对单位体积自由能的影响可消失，但仍可能存在多个 Gibbs 态、边界依赖的磁化和自发对称性破缺。

平均场近似可由耦合矩阵最大特征值给出候选阈值。例如在均匀 Ising 线性化中，若 \(J\) 为对称耦合矩阵，则无外场高温态的候选失稳满足
$$
\beta_c\,\lambda_{\max}(J)\approx1.
\tag{173.5}
$$
这只是平均场或高连通近似；短环、低维涨落、无序和 FIB 接缝可能改变真实临界行为。有限图上的磁化尖峰、基态交叉或稳定有限尺寸相关长度不能单独证明无限体积相变。

本节结论是：FIB 提供自旋相互作用的组合候选图；Gibbs 测度、相关函数、相变阈值、临界指数和边界依赖由 Hamiltonian、温度、更新核及热力学极限共同决定。

## 174. FIB 路径上的黏弹性、记忆核、蠕变与耗散标度

FIB 只提供路径连接、方向和层级索引。应变、应力、长度、截面积、材料参数、温度、噪声和边界必须外加。对有限路径
$$
P=(v_0,e_1,v_1,\ldots,e_N,v_N),
$$
令边长为 \(a_j\)、节点位移为 \(u_j(t)\)，则
$$
x_j=\sum_{r=1}^ja_r,\qquad
\varepsilon_j(t)=\frac{u_j(t)-u_{j-1}(t)}{a_j}.
\tag{174.1}
$$
关联矩阵 \(B\) 下的动力学平衡可写为
$$
B^{\mathsf T}\boldsymbol\sigma+\boldsymbol f_{\rm ext}
=M\ddot{\boldsymbol u}.
$$

在线性小应变和时间平移不变近似下，因果本构关系为
$$
\sigma(x,t)
=\int_{-\infty}^tK(x,x';t-t')\dot\varepsilon(x',t')\,dx'
+\sigma_{\rm th}(x,t).
\tag{174.2}
$$
记局部松弛核为 \(G(t)\)。恒定应变阶跃 \(\varepsilon(t)=\varepsilon_0H(t)\) 产生
$$
\sigma(t)=\varepsilon_0G(t).
$$
单 Maxwell 元件满足
$$
\dot\sigma+\frac{\sigma}{\tau}=E\dot\varepsilon,
\qquad \tau=\frac{\eta}{E},
\tag{174.3}
$$
其松弛模量和蠕变柔量分别为
$$
G(t)=Ee^{-t/\tau},
\qquad
J(t)=\frac1E+\frac{t}{\eta}.
$$

广义 Maxwell 模型可写为
$$
\sigma=G_\infty\varepsilon+\eta_0\dot\varepsilon+\sum_mq_m,
\qquad
\dot q_m+\frac{q_m}{\tau_m}=G_m\dot\varepsilon,
\tag{174.4}
$$
因此
$$
G(t)=G_\infty+\sum_mG_me^{-t/\tau_m}.
$$
在频域中，
$$
G^*(\omega)
=G_\infty+i\omega\eta_0
+\sum_mG_m\frac{i\omega\tau_m}{1+i\omega\tau_m},
$$
其实部 \(G'\) 储存能量，虚部 \(G''\) 耗散能量。周期应变的耗散能密度为
$$
W_{\rm cyc}=\pi\varepsilon_0^2G''(\omega).
\tag{174.5}
$$

若松弛时间具有连续谱
$$
G(t)-G_\infty
=\int\rho(\tau)e^{-t/\tau}\,d\tau,
$$
且中间尺度满足 \(\rho(\tau)\propto\tau^{-1-\alpha}\)、\(0<\alpha<1\)，则有限窗口内可见
$$
G(t)-G_\infty\propto t^{-\alpha},
\qquad
G'(\omega)\sim G''(\omega)\sim\omega^\alpha.
\tag{174.6}
$$
这只是记忆谱造成的有效标度；递归层级不自动生成幂律松弛谱。

被动性要求自由能 \(\psi\) 的机械功率满足
$$
\sigma\dot\varepsilon-\dot\psi
=\eta_0\dot\varepsilon^2+\sum_m\frac{q_m^2}{G_m\tau_m}\ge0,
\tag{174.7}
$$
因此 \(G_m\ge0,\tau_m>0,\eta_0\ge0\) 是该线性模型的耗散条件。热噪声若来自局部平衡，还需满足与耗散核相容的涨落耗散关系；非平衡主动应力不能直接使用同一噪声强度。

有限路径的端点位移、牵引、接触或储库条件会改变松弛谱与长期蠕变。路径层级只提供可能的非局部记忆连接；是否存在跨层材料耦合，必须在 \(K(x,x';t)\) 中明确给出。

本节结论是：FIB 提供黏弹材料的连接与多尺度索引；记忆核、蠕变、耗散谱、热噪声和边界响应由外加本构模型与时间尺度决定。

## 175. FIB 网络上的 SIS/SIR/SEIR 传播、阈值与最终规模

FIB 图可提供传播关系，但传播率、恢复率、潜伏期、免疫、接触频率、检测和边界输入均需外加。静态渗流只研究占据配置，SIS、SIR 与 SEIR 研究时间演化，三者不能混为同一阈值。

令 \(A\) 为传播接触矩阵，节点感染概率或状态由外加随机过程更新。连续时间 SIS 模型的感染率和恢复率分别为 \(\beta A_{ij}\) 与 \(\gamma_i\)。在独立近似下，感染概率 \(p_i\) 满足
$$
\dot p_i
=-\gamma_i p_i
+\beta(1-p_i)\sum_jA_{ij}p_j.
\tag{175.1}
$$
无感染态线性化为
$$
\dot{\boldsymbol p}
=(\beta A-\Gamma)\boldsymbol p,
\qquad
\Gamma=\operatorname{diag}(\gamma_i).
\tag{175.2}
$$
候选入侵阈值是
$$
\rho(\Gamma^{-1}\beta A)=1.
\tag{175.3}
$$
它是均场或低相关近似下的阈值；短环、相关感染、同时接触和 FIB 接口共享都会修正该条件。

SIR 模型加入不可再感染的移除状态。若感染者 \(i\) 向易感者 \(j\) 的边传播概率为 \(T_{ij}\)，则在局部树状近似下，下一代矩阵可写为
$$
K_{ij}=T_{ij}C_{ij},
\tag{175.4}
$$
其中 \(C_{ij}\) 是接触次数或外加接触权重。基本再生数为
$$
R_0=\rho(K).
$$
\(R_0>1\) 只表示低密度入侵具有增长方向，并不保证有限图出现大规模流行；最终规模还依赖初始感染、边界、饱和和随机灭绝。

SEIR 模型增加潜伏状态，若潜伏率为 \(\sigma_i\)，则
$$
\dot S_i=-\beta S_i\sum_jA_{ij}I_j,\qquad
\dot E_i=\beta S_i\sum_jA_{ij}I_j-\sigma_iE_i,
$$
$$
\dot I_i=\sigma_iE_i-\gamma_iI_i,\qquad
\dot R_i=\gamma_iI_i.
\tag{175.5}
$$
潜伏期改变时间尺度和波形，但是否改变入侵阈值取决于感染性阶段的下一代算子，而非单纯由 FIB 层数决定。

有限图、无外部输入且恢复率严格为正时，长期感染通常消失；持续流行相需要无限系统极限、持续输入或免疫结构的特殊缩放。检测概率 \(p_{\rm det}\) 产生观测变量
$$
I_i^{\rm obs}\mid I_i\sim\operatorname{Binomial}(I_i,p_{\rm det}),
$$
观测峰值和真实感染峰值不能直接等同。边界隔离、旅行输入和分区策略也会改变传播算子。

若 FIB 图的度数、层级或边权存在强异质性，最大特征模态可能集中在少数枢纽；此时全局平均感染率会掩盖局部传播。相关网络、时间变化接触和行为反馈还需要时变矩阵 \(A(t)\) 或状态依赖速率，不能继续使用固定矩阵阈值。

本节结论是：FIB 提供疾病或信息传播的组合接触图；\(R_0\)、SIS 阈值、最终规模和观测统计由传播核、恢复/免疫、时间结构、检测和边界输入决定。

## 176. FIB 网络上的 XY 模型、涡旋与 BKT 型转变

FIB 在本节仅提供图 \(G=(V,E)\) 及其回路结构。相位变量、耦合、温度、二维几何、胞腔填充和边界均需外加。图中存在回路不能单独推出二维涡旋或 BKT 转变。

对每个顶点取紧致相位
$$
\theta_v\in\mathbb R/2\pi\mathbb Z,
$$
并赋予无挫折耦合 \(J_{uv}>0\)。XY Hamiltonian 为
$$
H_G(\theta)
=-\sum_{\{u,v\}\in E}J_{uv}\cos(\theta_v-\theta_u),
\tag{176.1}
$$
配分函数为
$$
Z_G(T)=
\int\prod_{v\in V}\frac{d\theta_v}{2\pi}\,
e^{-\beta H_G(\theta)}.
\tag{176.2}
$$
有限图在 \(T>0\) 时没有真正非解析相变；相变必须由指定增长图族 \(G_L\) 和长度尺度极限定义。

相位相关函数为
$$
G_{uv}=\left\langle e^{i(\theta_u-\theta_v)}\right\rangle.
$$
在具有二维短程几何、连续旋转对称性和适当均匀性的模型中，低温相可呈准长程序
$$
G(r)\sim r^{-\eta(T)},
\qquad 0<\eta(T)\le\frac14,
\tag{176.3}
$$
高温相则具有有限相关长度。图距离只有在嵌入与二维物理距离相容时才可代替 \(r\)；一般 FIB 图并不满足这一条件。

固定边方向并取主值相位差
$$
\Delta_{uv}=\operatorname{Arg}e^{i(\theta_v-\theta_u)}
$$
后，对闭合回路 \(C\) 定义绕数
$$
Q(C)=\frac1{2\pi}\sum_{(u,v)\in C}\Delta_{uv}\in\mathbb Z.
\tag{176.4}
$$
只有另行指定二维面集 \(P\)，才能把
$$
q_p=Q(\partial p)
$$
解释为局部涡旋电荷。区域边界满足
$$
Q(\partial R)=\sum_{p\subset R}q_p.
\tag{176.5}
$$
周期无边界分解通常要求总涡旋电荷为零，但仍可存在涡旋—反涡旋对和全局非收缩回路绕数。分支穿越、缺陷生成和边界孔洞会改变这些约束。

相位变化缓慢时，XY 能量的长波近似为
$$
H_{\rm sw}
=\frac12\sum_{\{u,v\}\in E}
J_{uv}(\theta_v-\theta_u)^2.
\tag{176.6}
$$
若进一步收敛到二维均匀连续几何，才可写
$$
H_{\rm sw}
=\frac{\rho_s^{(0)}}2\int|\nabla\theta|^2\,d^2x.
$$
相位刚度可由周期边界扭转 \(\Phi\) 的自由能二阶导数定义。BKT 型转变还需要涡旋对的能量—熵竞争、二维短程相互作用和无长程相关障碍；FIB 回路数量本身不足以证明其存在。

本节结论是：FIB 提供相位耦合的图与回路；XY 相关、涡旋电荷、相位刚度和 BKT 标度由二维几何、耦合、温度、边界及热力学极限决定。

## 177. FIB 通道网络上的外加热电输运、Onsager 矩阵与热噪声

FIB 通道只提供组合连接。电荷、能量、化学势、温度、接触库和时间反演规则均须另行赋予。路径数不等于电导；相干路径需先叠加振幅，非相干路径则需给出跃迁率或局域输运系数。电荷通道和热通道也可能由不同激发承载。

接触库 \(\alpha\) 由 \(T_\alpha\) 与电化学势 \(\mu_\alpha\) 描述。统一规定端口流入网络为正，稳态下满足
$$
\sum_\alpha I_\alpha=0,
\qquad
\sum_\alpha J_{E,\alpha}+P_{\rm ext}=0.
\tag{177.1}
$$
热流是
$$
J_{Q,\alpha}=J_{E,\alpha}-\mu_\alpha J_{N,\alpha},
\tag{177.2}
$$
不能直接把能量流当作热流。局部平衡、接触温度和化学势只有在指定耗散或库模型后才有意义。

在线性响应中，以共同参考态 \((\mu_0,T_0)\) 定义力
$$
X_I=\frac{\Delta V}{T_0},
\qquad
X_Q=\frac{\Delta T}{T_0^2},
$$
并写
$$
\begin{pmatrix}I\\J_Q^{(0)}\end{pmatrix}
=
\begin{pmatrix}L_{11}&L_{12}\\L_{21}&L_{22}\end{pmatrix}
\begin{pmatrix}X_I\\X_Q\end{pmatrix}.
\tag{177.3}
$$
熵产生的二次项为
$$
\dot S=X^{\mathsf T}LX,
$$
因此对被动稳定系统，\(L\) 的对称部分必须半正定。时间反演和微观可逆性还需额外给出，才能得到 Onsager–Casimir 关系
$$
L_{\alpha\beta}(B)
=L_{\beta\alpha}(-B).
\tag{177.4}
$$
无磁场或其他奇变量时才简化为对称矩阵。

若 \(L_{11}>0\)，电导、Seebeck 系数、Peltier 系数和开路热导可定义为
$$
G=\frac{L_{11}}{T_0},
\qquad
S=\frac{L_{12}}{T_0L_{11}},
\qquad
\Pi=\frac{L_{21}}{L_{11}},
$$
$$
\kappa_{\rm oc}
=\frac1{T_0^2}
\left(L_{22}-\frac{L_{21}L_{12}}{L_{11}}\right).
\tag{177.5}
$$
固定电压差为零得到的热导 \(L_{22}/T_0^2\) 与开路热导不是同一边界条件。由热导换算热导率还需长度和截面积。

若通道增量 \(d_\alpha(c)\) 在反向边上变号，累计流为
$$
Q_\alpha(T)=\sum_{\text{区间内发生的 }c}d_\alpha(c).
$$
在平衡、时间平移不变、相关可积和边界项消失时，Green–Kubo 型输运系数为
$$
L_{\alpha\beta}
=\frac1{k_BT}\int_0^\infty
\langle J_\alpha(t)J_\beta(0)\rangle\,dt.
\tag{177.6}
$$
开放储库、非平衡驱动、长时相关和主动通道会产生边界或熵流修正，不能无条件使用平衡公式。

本节结论是：FIB 提供热电通道的组合网络；电导、热导、Seebeck/Peltier 系数、Onsager 对称与噪声谱由载流子、接触库、时间反演、局部守恒和线性响应条件决定。

## 178. FIB 图上的外加界面生长、KPZ 方程与粗糙度标度

本节把 FIB 作为界面邻接结构和更新次序。沉积速率、噪声、表面张力、斜率非线性、空间尺度和边界条件均需外加。设有限界面图为 \(G_L=(V_L,E_L)\)，节点高度为 \(h_i(t)\)，节点权重为 \(\mu_i>0\)，边权为 \(c_{ij}=c_{ji}\ge0\)。定义
$$
(\Delta_Gh)_i
=\frac1{\mu_i}\sum_{j\sim i}c_{ij}(h_j-h_i),
\qquad
Q_i(h)=\frac1{2\mu_i}\sum_{j\sim i}c_{ij}(h_j-h_i)^2.
\tag{178.1}
$$
\(Q_i\) 是特定离散斜率项；不同离散化可能给出不同连续极限。

一种外加生长规则为
$$
h_i\leftarrow h_i+\Delta t
\left[F+\nu(\Delta_Gh)_i+\frac\lambda2Q_i(h)\right]
+\sqrt{\frac{2D\Delta t}{\mu_i}}\xi_{i,m}.
\tag{178.2}
$$
其中 \(F\) 是平均沉积，\(\nu\) 是平滑系数，\(\lambda\) 是斜率非线性系数，\(D\) 是噪声强度。FIB 更新次序只有在明确每轮访问频率和局部时钟后才可解释为时间；不同更新次序可能产生不同离散动力学。

若图族具有适当欧氏嵌入、局部相互作用和连续极限，候选连续方程为
$$
\partial_t h
=F+\nu\nabla^2h+\frac\lambda2|\nabla h|^2+\eta,
\tag{178.3}
$$
其中白噪声理想化为
$$
\mathbb E[\eta(\mathbf x,t)\eta(\mathbf x',t')]
=2D\delta(\mathbf x-\mathbf x')\delta(t-t').
$$
长程边、守恒噪声、冻结无序或相关沉积会改变方程。没有欧氏极限时，图上的随机演化仍可定义，但不能直接替换为普通拉普拉斯的 KPZ 方程。

扣除加权平均高度
$$
\bar h=\frac1{M_L}\sum_i\mu_i h_i,\qquad
M_L=\sum_i\mu_i,
$$
后，粗糙度定义为
$$
W^2(L,t)=
\mathbb E\left[
\frac1{M_L}\sum_i\mu_i(h_i-\bar h)^2
\right].
\tag{178.4}
$$
若存在自仿射标度，可检验 Family–Vicsek 形式
$$
W(L,t)\sim L^\alpha f(t/L^z),
\tag{178.5}
$$
从而
$$
W\sim t^\beta,\qquad
W_{\rm sat}\sim L^\alpha,\qquad
t_{\rm sat}\sim L^z,\qquad
\beta=\frac\alpha z.
$$
这些指数需要在微观截止尺度、相关长度和系统尺度之间存在清晰窗口；异常粗糙化可能要求区分局部与全局指数。

\(\lambda=0\) 时得到 Edwards–Wilkinson 型线性模型。若 \(-\Delta_G\) 的谱为
$$
0=\omega_0<\omega_1\le\cdots,
$$
则闭合连通图上的线性粗糙度满足
$$
W^2(t)=
\frac D{\nu M_L}\sum_{k\ge1}
\frac{1-e^{-2\nu\omega_kt}}{\omega_k},
\qquad
t_{\rm rel}\asymp\frac1{\nu\omega_1}.
\tag{178.6}
$$
这说明低频谱控制有限图上的弛豫和饱和粗糙度；要由谱推出 \(\alpha,z\)，还需一列不断增大的图及其低频谱标度。标准 KPZ 的 \(\alpha+z=2\) 依赖额外倾斜对称性，不由 FIB 邻接自动保证。

本节结论是：FIB 提供界面更新的组合骨架；KPZ 普适类、粗糙度指数、相关长度和有限尺寸饱和值由生长规则、噪声、连续极限与边界决定。

## 179. FIB 关系网络上的外加化学反应网络与随机反应统计

FIB 只提供关系和合法组合路径。物种、化学计量、反应速率、混合条件、热浴和物质库均需外加。设有 \(d\) 个物种和 \(m\) 个反应通道
$$
r:\quad
\sum_i y_{ir}X_i\longrightarrow
\sum_i y'_{ir}X_i,
$$
定义
$$
\nu_r=y'_r-y_r,\qquad
N=[\nu_1\ \cdots\ \nu_m].
\tag{179.1}
$$
路由映射把反应通道放置到 FIB 路径上，但同一组合骨架可承载不同反应重数和速率，不能由路径标签决定化学计量。

在充分混合、确定性质量作用模型中，令 \(x_i\) 为浓度，
$$
v_r(x)=\kappa_rx^{y_r},
\qquad
x^{y_r}=\prod_ix_i^{y_{ir}},
\qquad \kappa_r>0,
$$
则
$$
\dot x=Nv(x).
\tag{179.2}
$$
若 \(\ell^{\mathsf T}N=0\)，封闭模型中的 \(\ell^{\mathsf T}x\) 是线性守恒量；将其解释为质量、电荷或元素数还需物理赋值。开放输入输出写成
$$
\dot x=Nv(x)+b(x,t),
$$
此时
$$
\frac d{dt}\ell^{\mathsf T}x=\ell^{\mathsf T}b(x,t).
$$
稳态 \(Nv(x_*)=0\)、稳态唯一、局部稳定和全局收敛是不同结论。

有限体积 \(\Omega\) 的随机反应状态 \(n\in\mathbb N_0^d\) 以危险率
$$
a_r^\Omega(n)
=\kappa_r\Omega^{1-|y_r|}
\prod_i(n_i)_{\underline{y_{ir}}}
\tag{179.3}
$$
跳转为 \(n+\nu_r\)。生成元为
$$
(\mathcal L_\Omega g)(n)
=\sum_ra_r^\Omega(n)[g(n+\nu_r)-g(n)],
$$
主方程为
$$
\partial_tp(n,t)
=\sum_r[
a_r^\Omega(n-\nu_r)p(n-\nu_r,t)
-a_r^\Omega(n)p(n,t)].
\tag{179.4}
$$
反应计数可用随机时间变换表示，计数补偿过程为鞅；不同通道通过共同状态产生相关涨落。精确均值满足
$$
\frac d{dt}\mathbb E[n(t)]
=\sum_r\nu_r\mathbb E[a_r^\Omega(n(t))],
$$
非线性危险率通常不能替换为均值处的危险率。

复合物图的复杂平衡要求每个复合物的流入与流出相等；详细平衡则要求每一对反应通道逐通道平衡。若存在正平衡态并满足相应条件，确定性系统可具有 Lyapunov 型自由能
$$
\mathcal G(x)
=\sum_i\left[
x_i\log\frac{x_i}{x_i^*}-x_i+x_i^*
\right],
$$
其沿动力学非增；详细平衡的随机模型还可得到 Gibbs 型稳态。没有反向通道、库驱动或饱和速率时，不能强行套用平衡结论。

大体积极限需同时控制初始条件、危险率缩放、守恒量和边界；扩散限制反应还需空间随机过程，不能把充分混合质量作用律直接解释为 FIB 图上的局部反应。

本节结论是：FIB 提供反应通道的组合路由；质量作用、守恒量、稳态、随机主方程、复杂平衡与涨落由化学计量、速率常数、体积和环境交换决定。

## 180. FIB 网络上的玻璃态、冻结、老化与模式耦合

设 FIB 网络为
$$
G_{\rm FIB}=(\mathcal S,\mathcal E),
$$
其中边只规定状态之间允许直接转移。玻璃动力学还需外加能量 \(E(x)\)、势垒、跃迁速率、温度、噪声、淬火协议、观测量和系统极限。连续时间生成元可写为
$$
(Lf)(x)=\sum_yw_{xy}[f(y)-f(x)],
\qquad
w_{xy}=0\quad\text{若 }(x,y)\notin\mathcal E.
\tag{180.1}
$$
邻接只约束速率支撑。若另加对称势垒和热浴，可能得到 Gibbs 测度和详细平衡；受驱动或单向更新时则可形成非平衡稳态或吸收态。

有限不可约详细平衡过程的平衡相关函数具有谱表示
$$
C_A^{\rm eq}(\tau)
=\langle a,e^{\tau L}a\rangle_\pi
=\sum_{k\ge1}
|\langle a,\varphi_k\rangle_\pi|^2e^{-\lambda_k\tau},
\qquad a=A-\langle A\rangle_\pi.
\tag{180.2}
$$
小特征值或宽广低频谱会产生长平台和非指数松弛，但这些性质由速率加权生成元决定，而非由无权 FIB 邻接单独决定。

冻结至少有三种含义：观测窗口内未松弛、严格动力学阻塞或吸收、以及先取无限规模再取长时间后保留的非遍历极限。有限不可约系统满足
$$
\lim_{\tau\to\infty}C_A^{\rm eq}(\tau)=0,
$$
所以有限时间平台不能证明永久冻结。系统族的动态序参量可定义为
$$
q_{\rm dyn}
=\lim_{\tau\to\infty}\lim_{N\to\infty}
C_N^{\rm eq}(\tau),
\tag{180.3}
$$
但极限次序和局部观测量必须明确。

淬火后等待时间 \(s\)、观察时间 \(t=s+\tau\) 的两时间相关为
$$
C_{AB}(t,s)
=\langle A(X_t)B(X_s)\rangle
-\langle A(X_t)\rangle\langle B(X_s)\rangle.
\tag{180.4}
$$
平稳系统只依赖 \(t-s\)；依赖 \(s\) 表示非平稳老化，但还需排除温度漂移、噪声变化和观测规则变化。平衡可逆动力学满足涨落耗散关系
$$
T R_{AB}^{\rm eq}(t,s)
=\partial_sC_{AB}^{\rm eq}(t,s).
\tag{180.5}
$$
非平衡时可定义涨落耗散比
$$
X_{AB}(t,s)
=\frac{TR_{AB}(t,s)}{\partial_sC_{AB}(t,s)},
$$
但不能预设其范围或把 \(T/X\) 自动解释为有效温度。

常用老化假设是
$$
C(t,s)\simeq
C_{\rm fast}(t-s)
+C_{\rm age}\!\left(\frac{h(t)}{h(s)}\right),
\tag{180.6}
$$
简单老化取 \(h(t)\propto t\)，其他 \(h\) 可表示次老化或超老化。该标度是待检验假设；不同观测量未必共享同一老化时钟。FIB 层级可提供多尺度状态，但不自动给出势垒增长、时间重参数化或玻璃普适类。

本节结论是：FIB 提供状态邻接和可能的模式耦合；玻璃冻结、老化标度、相关平台与涨落耗散失效由能量景观、跃迁率、温度、淬火及极限次序决定。

## 181. FIB 结构上的外加非线性弹性、屈曲与断裂前失稳

设有限 FIB 骨架为
$$
G_n=(V_n,E_n),
$$
并另加节点参考嵌入 \(\mathbf r_i\in\mathbb R^d\)、杆件截面、材料本构、接头、支承和载荷。边长、厚度、弯曲刚度与组合递归彼此独立；同一骨架改变嵌入或接头即可改变失稳模态。

非线性杆能量可写为
$$
U=\sum_{e=(i,j)}A_e\ell_e^0\psi_e(\lambda_e),
\qquad
\lambda_e=\frac{|\mathbf x_j-\mathbf x_i|}{\ell_e^0}.
\tag{181.1}
$$
若需要梁屈曲，还需加入转角和弯曲能。边界与保守载荷给出总势能
$$
\Pi(q;P)=U(q)-P\mathcal L(q),
$$
平衡满足
$$
D_q\Pi(q;P)[v]=0.
$$
沿平衡支的切线刚度
$$
K_T(P)=D_q^2\Pi(q_0(P);P)
$$
首次出现零特征值时，达到线性中性门槛；零模态后的分叉类型还要由高阶能量和载荷控制方式决定。

对梁或杆边，二阶能量同时包含材料切线刚度与预应力几何刚度。压缩力可使横向几何刚度为负，材料软化则降低轴向切线刚度；这两种失稳来源不能混为一谈。若
$$
\delta^2\Pi[v,v]=\mathcal K[v]-P\mathcal Q[v],
$$
则在允许模态上
$$
P_{\rm cr}
=\inf_{\mathcal Q[v]>0}\frac{\mathcal K[v]}{\mathcal Q[v]}.
\tag{181.2}
$$
允许模态必须满足所有节点相容和支承条件，因此整体网络临界载荷一般不等于各边欧拉载荷的最小值。

单根长度 \(L\)、弯曲刚度 \(B\) 的两端铰支梁满足
$$
B w''''+Nw''=0,
\qquad
N_{\rm cr}=\frac{\pi^2B}{L^2}.
\tag{181.3}
$$
固支—固支、固支—自由等边界给出不同系数。FIB 接缝的转动约束、边内力分配和节点支承必须显式进入整体刚度算子。

连续薄板或杆理论只有在微结构尺度、有效刚度和能量收敛条件明确时才可作为 FIB 网络极限。有限样本平均模量不足以保证屈曲谱收敛；非周期递归结构还可能产生局部模态、边界模态和多尺度后屈曲分支。断裂前失稳还需另加损伤变量与能量释放条件，不能把零切线刚度直接称为裂纹。

本节结论是：FIB 提供非线性结构的连接骨架；屈曲临界载荷、模态、后屈曲路径和断裂前失稳由几何嵌入、材料能量、接头、载荷和边界决定。

## 182. FIB 量子网络上的外加 Chern 拓扑、量子霍尔响应与边缘态

FIB 只提供图、胞腔和跃迁候选。二维周期平移、轨道、复跃迁、能带占据、费米能隙和物理边界均需外加。候选图上的厄米紧束缚模型可写为
$$
\widehat H
=\sum_i\varepsilon_i c_i^\dagger c_i
+\sum_{(i,j)\in E_+}
\left(t_{ij}c_i^\dagger c_j+\overline{t_{ij}}c_j^\dagger c_i\right).
\tag{182.1}
$$
若要使用 Bloch 理论，还需外加二维周期实现和晶格位移，形成
$$
H_{\alpha\beta}(\mathbf k)
=\sum_{\mathbf R}t_{\alpha\beta}(\mathbf R)
e^{i\mathbf k\cdot\mathbf R},
\qquad \mathbf k\in T^2.
\tag{182.2}
$$
FIB 图中的回路不能单独充当布里渊环面。

取化学势 \(\mu\)，并要求统一能隙
$$
\operatorname{dist}(\mu,\operatorname{spec}H(\mathbf k))\ge\Delta>0
\quad\text{对所有 }\mathbf k.
\tag{182.3}
$$
占据投影
$$
P(\mathbf k)=\mathbf1_{(-\infty,\mu)}(H(\mathbf k))
$$
才具有固定秩并可平滑变化。占据子空间的 Berry 曲率为
$$
\Omega_{\rm occ}(\mathbf k)
=i\,\operatorname{Tr}\bigl(
P[\partial_{k_x}P,\partial_{k_y}P]\bigr),
$$
Chern 数为
$$
C_{\rm occ}
=\frac1{2\pi}\int_{T^2}\Omega_{\rm occ}(\mathbf k)\,d^2k
\in\mathbb Z.
\tag{182.4}
$$
整数性来自闭合参数空间上的占据向量丛；局部非零曲率不保证积分非零。保持能隙和正则性的连续变形不能改变 Chern 数，改变它必须经过能隙闭合或占据秩改变。

复跃迁的单边相位可能是规范选择，闭合回路乘积才是规范不变量。复跃迁不自动破坏时间反演，也不自动给出非零 Chern 数。若占据子空间满足时间反演对称性，二维电荷 Chern 数为零，但其他拓扑指标仍可能存在。

在非相互作用、零温、局域电荷守恒、二维物理准动量和统一费米能隙条件下，线性响应连接 Chern 数与霍尔电导：
$$
\sigma_H=\frac{q^2}{h}C_{\rm occ}.
\tag{182.5}
$$
这一连接还需要一致定义电流算子、电磁耦合和直流极限；不能把抽象图的回路数直接称为量子霍尔电导。

带边界的有限系统若保持体能隙并满足适当局域性，可出现与体拓扑相容的谱流边缘态。边界形状、终止方式、无序和有限宽度会改变边缘色散，不能由 FIB 接缝单独决定。若体隙关闭、有限尺寸混合占主导或存在强相互作用，简单单粒子边缘—体对应需要重新建立。

本节结论是：FIB 提供量子跃迁和胞腔的组合候选；Berry 曲率、Chern 数、量子霍尔响应及边缘态由二维周期实现、复跃迁、能隙、占据规则和边界条件决定。

## 183. FIB 递归路径上的外加确定性混沌、Lyapunov 指数与 Kolmogorov 熵

FIB 给出状态之间的允许转移和符号路径。设路径为
$$
s_0\xrightarrow{e_0}s_1\xrightarrow{e_1}s_2\longrightarrow\cdots.
$$
这只规定合法次序；连续状态空间、度量、映射、初始测度和噪声均需外加。可在每个边转移上配置
$$
F_e:M\to M,\qquad x_{n+1}=F_{e_n}(x_n),
\tag{183.1}
$$
再以移位 \(S\) 构造符号—连续纤维系统
$$
T(\omega,x)=
\bigl(S\omega,F_{e_0(\omega)}(x)\bigr).
$$
不变概率测度及其路径边缘测度不是 FIB 自动给出的。

若 \(F_e\) 为 \(C^1\)，沿固定符号路径的切向传播为
$$
A_n=DF_{e_n}(x_n),\qquad
P_n=A_{n-1}\cdots A_0,
$$
$$
\delta x_n=P_n\delta x_0+o(\|\delta x_0\|).
\tag{183.2}
$$
一般不能把各步最大特征值相乘代替 \(P_n\)，因为扩张方向会转动且矩阵通常不交换。有限时间 Lyapunov 指数为
$$
\lambda_i^{(n)}
=\frac1n\log\sigma_i(P_n),
$$
渐近指数的存在需要平稳性、可测性和可积性，例如
$$
\int\log^+\|DF_e\|\,d\mu<\infty.
\tag{183.3}
$$
正的最大指数表示某些切向方向的渐近扩张，不表示所有扰动都扩张，也不等于物理单位时间指数，除非物理时钟已明确。

Kolmogorov–Sinai 测度熵对有限分割 \(\mathcal P\) 定义为
$$
h_\mu(T,\mathcal P)
=\lim_{n\to\infty}\frac1n
H_\mu\!\left(\bigvee_{k=0}^{n-1}T^{-k}\mathcal P\right),
\qquad
h_\mu(T)=\sup_{\mathcal P}h_\mu(T,\mathcal P).
\tag{183.4}
$$
允许路径数的增长、路径概率的熵和连续纤维的 KS 熵是不同量。同一合法路径空间可支持集中于周期轨道的零熵测度，也可支持正熵测度。FIB 递归长度的指数增长不能直接当作每次转移的熵率。

在满足相应光滑、可积和绝对连续条件时，Ruelle 不等式给出
$$
h_\mu(T)
\le
h_{\rm base}
+\int\sum_{\lambda_i>0}m_i\lambda_i\,d\mu.
\tag{183.5}
$$
等式需要 Pesin 型额外条件；正 Lyapunov 指数本身不能自动证明熵等于正指数之和。若存在噪声、分支边界或非遍历分量，需分别处理路径选择和纤维指数。

本节结论是：FIB 提供符号转移与递归路径；确定性混沌、Lyapunov 指数、测度熵及其关系由外加连续映射、度量、不变测度和时间尺度决定。

## 184. FIB 链与图上的外加离散非线性 Schrödinger、孤子与调制不稳定

FIB 只提供耦合图。选无向对称权 \(w_{nm}\)、图 Laplacian
$$
(L\psi)_n=\sum_{m\sim n}w_{nm}(\psi_n-\psi_m),
$$
以及实势 \(V_n\) 和非线性系数 \(g_n\)，可定义外加 DNLS
$$
i\frac{d\psi_n}{dt}
=(L\psi)_n+V_n\psi_n+g_n|\psi_n|^2\psi_n.
\tag{184.1}
$$
在静态参数和无外部通量边界下，
$$
N=\sum_n|\psi_n|^2,\qquad
H=\sum_{\{n,m\}}w_{nm}|\psi_n-\psi_m|^2
+\sum_nV_n|\psi_n|^2+\frac12\sum_ng_n|\psi_n|^4
\tag{184.2}
$$
分别守恒。若采用邻接算子、非厄米权或开放边界，这些守恒律会改变。

对均匀周期链的平面波
$$
\psi_n=\sqrt\rho\,e^{i(qn-\omega t)},
$$
有
$$
\omega=V_0+4C\sin^2\frac q2+g\rho.
$$
扰动波数 \(Q\) 的线性频率满足
$$
\Omega_\pm(Q)
=2C\sin q\sin Q
\pm\sqrt{\varepsilon_q(Q)[\varepsilon_q(Q)+2g\rho]},
$$
$$
\varepsilon_q(Q)=4C\cos q\sin^2\frac Q2.
\tag{184.3}
$$
若存在
$$
\varepsilon_q(Q)[\varepsilon_q(Q)+2g\rho]<0,
\tag{184.4}
$$
则该模态指数增长，增长率为根号内负值的平方根。有限 FIB 环只能取离散 \(Q\)，必须逐模态检查；非周期图不能直接使用平面波公式。

一般图上若 \(L\mathbf1=0\)、\(V_n=V_0\)、\(g_n=g\)，常数背景
$$
\psi_n(t)=\sqrt\rho\,e^{-i(V_0+g\rho)t}
$$
存在。沿 \(L\) 的谱值 \(\lambda\ge0\) 线性化得到
$$
\Omega^2=\lambda(\lambda+2g\rho).
\tag{184.5}
$$
聚焦情形 \(g<0\) 的不稳定条件为
$$
0<\lambda<2|g|\rho.
\tag{184.6}
$$
因此有限图的最小正谱值和最大谱值共同决定不稳定窗口。

驻波
$$
\psi_n(t)=e^{-i\mu t}\phi_n
$$
满足
$$
\mu\phi_n=(L\phi)_n+V_n\phi_n+g_n|\phi_n|^2\phi_n.
\tag{184.7}
$$
局域孤子需要 \(\phi\in\ell^2\)，并需有线性局域模态分岔、反连续极限延拓或其他存在性条件。FIB 图的层级结构可能产生局域谱态，但不自动保证点谱、指数局域或孤子稳定性；稳定性还需线性化谱和非线性约束。

本节结论是：FIB 提供非线性波的耦合骨架；守恒量、调制不稳定、离散孤子和局域模态由线性算子、非线性、边界和谱条件决定。

## 185. FIB 关系网络上的外加食物网、共存与生态稳定性

FIB 关系只规定候选连接，不决定捕食方向、增长率、相互作用强度、容量或噪声。选定外加作用矩阵 \(A\)，可研究
$$
\dot x_i=x_i\left(r_i+\sum_jA_{ij}x_j\right),
\qquad x_i\ge0.
\tag{185.1}
$$
其中增长率、捕食/竞争/互利参数和自限项均为外加。关系相同而作用类型不同，会产生完全不同的生态动力学。

完全共存平衡满足
$$
x^*>0,\qquad r+Ax^*=0.
\tag{185.2}
$$
矩阵可逆时 \(x^*=-A^{-1}r\)，但仍需逐坐标检查正性。对支持集 \(S\) 的边界平衡，缺席物种 \(j\notin S\) 的入侵增长率为
$$
\gamma_j=r_j+A_{jS}x_S^*.
\tag{185.3}
$$
\(\gamma_j>0\) 表示该物种可在低密度入侵，但不等于全局共存。

完全共存平衡的雅可比为
$$
J^*=\operatorname{diag}(x^*)A.
\tag{185.4}
$$
全部特征值实部严格为负时才有局部渐近稳定；直接检查 \(A\) 的谱一般不足。边界平衡在居民子系统稳定之外，还必须满足所有缺席物种的 \(\gamma_j<0\)。

一个足够的全局稳定结构是存在正对角矩阵 \(Q\) 使
$$
QA+A^{\mathsf T}Q\prec0.
\tag{185.5}
$$
此时相对熵型 Lyapunov 函数
$$
\mathcal V(x)=
\sum_iq_i\left[x_i-x_i^*-x_i^*\log\frac{x_i}{x_i^*}\right]
$$
沿正轨道严格下降。该条件是充分条件，不是一般 Lotka–Volterra 系统的必要条件。无自限的经典捕食模型可能只有闭合轨道，关系图不变而渐近性质完全不同。

持久性要求所有严格正初值远离灭绝边界，例如
$$
\liminf_{t\to\infty}\min_ix_i(t)\ge\eta>0.
$$
局部平衡稳定不能替代持久性。若边界有不变测度 \(\mu\)，可用平均入侵率
$$
\lambda_i(\mu)=
\int\left(r_i+\sum_jA_{ij}x_j\right)d\mu(x)
$$
构造边界排斥条件。环境噪声下的随机灭绝和随机持久性还需随机微分方程、噪声协方差、容量和初始分布；有限系统的长寿命不等于永恒共存。

本节结论是：FIB 提供物种关系的位置；共存平衡、入侵阈值、稳定性、持久性和随机灭绝由 Lotka–Volterra 参数、边界和环境噪声决定。

## 186. FIB 路径测度上的外加最优输运、梯度流与扩散

FIB 给出离散状态和允许接续关系，但不确定路径概率、输运代价、连续时间、熵泛函和边界交换。给定外加度量 \(d\)，经典离散 Wasserstein 距离为
$$
W_{2,d}^2(\mu,\nu)
=\min_{\gamma\in\Pi(\mu,\nu)}
\sum_{x,y}d(x,y)^2\gamma(x,y).
\tag{186.1}
$$
固定有限集合上的这一距离不自动带来连续时间梯度流；需要另选图上的活动边、跃迁率和通量结构。

在无向活动边 \(E\) 上选择正参考概率 \(\pi\)、可逆速率 \(q_{xy}\) 和
$$
c_{xy}=\pi_xq_{xy},
\qquad
\pi_xq_{xy}=\pi_yq_{yx}.
$$
令 \(\rho_x=\mu_x/\pi_x\)，并用对数平均
$$
\theta(a,b)=\frac{a-b}{\log a-\log b}
$$
定义通量 \(j_{xy}=-j_{yx}\) 与连续性方程
$$
\dot\mu_x+\sum_yj_{xy}=0.
$$
动态输运作用量为
$$
\mathcal A(\mu,j)
=\frac12\sum_{x,y}
\frac{j_{xy}^2}{c_{xy}\theta(\rho_x,\rho_y)}.
\tag{186.2}
$$
在该外加图输运结构下，熵
$$
\mathcal H(\mu\mid\pi)
=\sum_x\mu_x\log\frac{\mu_x}{\pi_x}
$$
的梯度流恰好为可逆 Markov 链的前向方程
$$
\dot\mu_x=\sum_y(\mu_yq_{yx}-\mu_xq_{xy}).
\tag{186.3}
$$
沿演化，
$$
\frac d{dt}\mathcal H(\mu_t\mid\pi)
=-\frac12\sum_{x,y}
c_{xy}(\rho_x-\rho_y)
(\log\rho_x-\log\rho_y)\le0.
\tag{186.4}
$$

因此，在明确的可逆速率和迁移率下，图热方程是相对熵的梯度流；改变边速率会改变扩散时间尺度，即使 FIB 可行路径完全相同。图不连通时，各连通分量的质量分别守恒，不能宣称全局唯一平衡。

加入外加势 \(V\) 和参考测度 \(m\)，自由能可写为
$$
\mathcal F(\mu)
=\sum_x\mu_x\log\frac{\mu_x}{m_x}
+\sum_xV_x\mu_x.
\tag{186.5}
$$
相应梯度流可导向带漂移的离散 Fokker–Planck 方程。若速率不满足详细平衡，熵流包含非平衡驱动项，梯度流结构和单调性需重新证明。连续 Wasserstein 极限还需给出嵌入、尺度缩放、紧性和边界通量。

本节结论是：FIB 提供离散状态与接缝；最优输运距离、熵梯度流、热方程和 Fokker–Planck 演化由代价度量、迁移率、参考测度、势能及边界决定。

## 187. FIB 网络上的外加磁流体动力学、磁通冻结与重联

FIB 只提供关系或网格骨架。速度场 \(\mathbf u\)、密度 \(\rho\)、压力 \(p\)、磁场 \(\mathbf B\)、电阻率、边界和尺度极限均需外加。可在连续嵌入后选择电阻磁流体方程
$$
\partial_t\rho+\nabla\cdot(\rho\mathbf u)=0,
\tag{187.1}
$$
$$
\rho(\partial_t\mathbf u+\mathbf u\cdot\nabla\mathbf u)
=-\nabla p+\mathbf J\times\mathbf B+\nabla\cdot\boldsymbol\tau+\mathbf f,
$$
$$
\partial_t\mathbf B
=\nabla\times(\mathbf u\times\mathbf B-\eta\mathbf J),
\qquad
\mathbf J=\mu_0^{-1}\nabla\times\mathbf B,
\tag{187.2}
$$
并要求
$$
\nabla\cdot\mathbf B=0.
$$
状态方程、黏性应力、热方程和电阻率模型仍需明确。

若 \(\eta=0\)、流场足够光滑且边界无磁通泄漏，则感应方程为
$$
\partial_t\mathbf B=\nabla\times(\mathbf u\times\mathbf B),
$$
磁通随流体线保持，这就是磁通冻结。非零电阻、薄层奇异性、数值耗散或边界电势会破坏冻结；FIB 接缝本身不提供理想导电条件。

理想磁流体的磁能
$$
E_B=\int\frac{|\mathbf B|^2}{2\mu_0}\,dV
$$
与动能、内能共同进入总能量预算。电阻项产生
$$
P_\eta=\int\eta|\mathbf J|^2\,dV\ge0,
\tag{187.3}
$$
黏性项也产生耗散。若存在外部驱动或开放边界，能量和磁螺度还要加入边界通量；不能在驱动系统中宣称总能量守恒。

磁重联要求磁通冻结在局部失效并改变磁拓扑，通常与非理想电场、薄电流层和拓扑不同的区域相联系。仅有 FIB 回路或接缝数量不能证明重联；必须给出 \(\eta\)、电子惯性、Hall 项或其他非理想机制，以及入口、出口和磁通边界条件。重联速率还依赖层厚度、驱动、压强和三维几何。

在高磁雷诺数和外部驱动下，磁能、动能和磁螺度可出现跨尺度传递。统计谱、间歇性和耗散尺度要由具体方程、初始数据、源汇和无量纲参数（如磁雷诺数、等离子体 \(\beta\)）决定。FIB 的递归层级可以作为多尺度分块，但不能直接给出 Kolmogorov 指数或重联普适类。

本节结论是：FIB 提供磁流体通道与网格组合骨架；磁通冻结、能量预算、磁能级联和重联由 MHD 方程、导电性、边界、驱动和尺度极限决定。

## 188. FIB 网络上的外加引力 N 体、Vlasov–Poisson 动力学与 Jeans 不稳定

固定 FIB 上下文给出的有限顶点集 \(V_j\)，并把顶点 \(i\) 另行嵌入 \(\Omega\subseteq\mathbb R^3\)，位置、动量和质量记为 \(x_i(t),p_i(t),m_i>0\)。FIB 只给出顶点、标签、词序及可供选择的组合关系；位置度量、质量、引力常数、边界和时间单位均需外加。给定相互作用掩码 \(A^{(j)}_{ik}\)、软化尺度 \(\ell_j\)、势核 \(U_j\) 和外势 \(V_j^{\rm ext}\)，可定义
$$
H_j=\sum_i\frac{|p_i|^2}{2m_i}
+\frac12\sum_{i\ne k}A^{(j)}_{ik}m_im_kU_j(x_i,x_k)
+\sum_i m_iV_j^{\rm ext}(x_i,t),
\tag{188.1}
$$
$$
\dot x_i=\frac{p_i}{m_i},\qquad
\dot p_i=-\sum_{k\ne i}A^{(j)}_{ik}m_im_k\nabla_{x_i}U_j(x_i,x_k)
-m_i\nabla V_j^{\rm ext}(x_i,t).
\tag{188.2}
$$
取 \(U_j(x,y)=-G_j(|x-y|^2+\ell_j^2)^{-1/2}\) 得到软化吸引势；全对全掩码和图掩码分别给出不同的作用范围。无显含时势和无功通量边界下 \(H_j\) 守恒，阻尼、驱动和开放边界则改变能量账。

定义经验相空间测度
$$
\mu_t^N=\frac1{M_N}\sum_{i\in V_j}m_i\delta_{(x_i(t),v_i(t))},
\qquad M_N=\sum_i m_i .
\tag{188.3}
$$
在 \(N\to\infty\)、\(m_i=O(N^{-1})\)、核满足外加正则性和截断条件时，可以寻求 \(\mu_t^N\Rightarrow f_t(x,v)\,{\rm d}x{\rm d}v\)，得到
$$
\partial_tf+v\cdot\nabla_xf-\nabla_x\Phi_f\cdot\nabla_vf=0,
\qquad
\Phi_f(x)=\int U(x,y)\rho_f(y)\,{\rm d}y,
\qquad
\rho_f=\int f\,{\rm d}v .
\tag{188.4}
$$
碰撞、近距离散射或随机踢可另加 \(\varepsilon_NQ_N(f)\)。先取平均场极限还是先保留碰撞，会分别产生 Vlasov、Boltzmann 或 Landau 型极限；FIB 递归不选择极限次序。

为讨论 Jeans 失稳，还需补入均匀背景、压力闭合和边界。取
$$
\partial_t\rho+\nabla\cdot(\rho u)=0,\qquad
\partial_t(\rho u)+\nabla\cdot(\rho u\otimes u)+c_s^2\nabla\rho
=-\rho\nabla\Phi,\qquad
\Delta\Phi=4\pi G(\rho-\rho_0).
\tag{188.5}
$$
围绕 \((\rho,u)=(\rho_0,0)\) 的模态 \(e^{st+{\rm i}k\cdot x}\) 满足
$$
s^2=4\pi G\rho_0-c_s^2|k|^2.
\tag{188.6}
$$
因此在给定的三维等温无耗散模型中，
$$
|k|<k_J,\qquad
k_J=\frac{\sqrt{4\pi G\rho_0}}{c_s},\qquad
\lambda_J=\frac{2\pi}{k_J}
\tag{188.7}
$$
给出长波增长。旋转、磁场、各向异性速度弥散、碰撞、阻尼和有限边界都会改变该判据；周期 FIB 图还只允许离散波数。更一般地，若图模态的压力算子和吸引算子分别为 \(\mathsf P_j,\mathsf A_j\)，共同模态满足
$$
\ddot\xi+(\mathsf P_j-\rho_0\mathsf A_j)\xi=0,\qquad
s_{\ell,j}^2=\rho_0a_{\ell,j}-c_s^2\lambda_{\ell,j}.
\tag{188.8}
$$
其中 \(a_{\ell,j}\)、\(\lambda_{\ell,j}\) 来自外加嵌入、权重和势核，不能由图入度或递归深度代替。

在过阻尼缩放下可另得 Smoluchowski–Poisson 方程
$$
\partial_t\rho=\nabla\cdot(D\nabla\rho+\mu\rho\nabla\Phi),
\qquad
\Delta\Phi=4\pi G(\rho-\rho_0).
\tag{188.9}
$$
它与趋化方程形式相似，但这里的势由同一质量分布对称地产生；是否存在有限温度平稳律仍需外加噪声、阻尼和涨落—耗散关系。仅观测 FIB 标签聚合或总质量时，长波聚集可落在观测核的零空间；即使观测完整密度，通常也只识别 \(G\rho_0/c_s^2\) 等组合。故聚集、Vlasov–Poisson 极限、Jeans 波长和长时间弛豫都是外加模型结论，不能宣称为 FIB ATOM 递归单独推出的引力定律。

## 189. FIB 路径上的外加量子热力学、Jarzynski–Crooks 关系与耗散

固定一条 FIB 上下文路径 \(\xi_0,\ldots,\xi_N\)，另选 Hilbert 空间 \(\mathcal H\)、时间网格、参数映射 \(\lambda_k=\Lambda(\xi_k)\) 和自伴哈密顿量 \(H_{\lambda_k}\)。FIB 的词序不是物理时间协议。正向演化可写成
$$
U_F=U_{N-1}\cdots U_0,\qquad
U_k=\mathcal T\exp\!\left(-{\rm i}\int_{t_k}^{t_{k+1}}H_{\lambda(t)}\,{\rm d}t\right).
\tag{189.1}
$$
设初态为 Gibbs 态
$$
\rho_0=\frac{e^{-\beta H_{\lambda_0}}}{Z_0},\qquad
Z_0={\rm tr}\,e^{-\beta H_{\lambda_0}},\qquad
F_k=-\beta^{-1}\log Z_k .
\tag{189.2}
$$
采用两点能量测量，功 \(W=E_m^\tau-E_n^0\)，其联合概率为
$$
p_F(m,n)=\frac{e^{-\beta E_n^0}}{Z_0}
\left|\langle m,\tau|U_F|n,0\rangle\right|^2 .
\tag{189.3}
$$
第一次测量消除能量基中的相干，所以这一定义依赖测量协议。

若存在反幺正时间反演 \(\Theta\) 和微观可逆条件
$$
U_R=\Theta U_F^\dagger\Theta^{-1},
\qquad
\Theta H_{\lambda(t)}\Theta^{-1}=H_{\lambda(t)}^{\rm rev},
\tag{189.4}
$$
反向协议从 \(H_{\lambda_N}\) 的 Gibbs 态开始，则
$$
\frac{p_F(m,n)}{p_R(n,m)}
=\exp\!\left[\beta(W-\Delta F)\right],
\qquad \Delta F=F_N-F_0 .
\tag{189.5}
$$
按功值聚合得到 Crooks 关系
$$
\frac{P_F(W=w)}{P_R(W=-w)}
=e^{\beta(w-\Delta F)},
\tag{189.6}
$$
并进一步得到 Jarzynski 等式
$$
\left\langle e^{-\beta W}\right\rangle_F=e^{-\beta\Delta F},
\qquad
\langle W\rangle_F-\Delta F=: \langle W_{\rm diss}\rangle\ge0 .
\tag{189.7}
$$
这些结论要求 Gibbs 制备、反向协议、微观可逆性以及一致的时间反演和能量账；FIB 路径的反向词序不足以构成物理时间反演。

在完整跃迁样本空间上，
$$
\Sigma(m,n)=\log\frac{p_F(m,n)}{p_R(n,m)}
=\beta(W-\Delta F),
\qquad
\beta\langle W_{\rm diss}\rangle
=D_{\rm KL}(p_F\Vert p_R^\dagger)\ge0 .
\tag{189.8}
$$
若只记录粗粒结果 \(Y=g(m,n)\)，数据处理不等式给出
$$
D_{\rm KL}(P_F^Y\Vert P_R^{Y,\dagger})
\le\beta\langle W_{\rm diss}\rangle .
\tag{189.9}
$$
隐藏的能级、coin 或 FIB 标签可以携带未观测熵产生；粗粒正反向分布相同只表示该观测通道看不见耗散。强耦合热浴、初始系统—浴相关、非马尔可夫记忆、反馈测量或准概率功定义都需要改写样本空间和自由能，不能直接套用 (189.6)。

同一 FIB 路径可承载恒定哈密顿量的零功协议、非对易淬火的宽功分布、满足详细平衡的经典跳跃或含测量回馈的非平衡协议。故功分布、自由能差、熵产生和耗散率依赖外加哈密顿量、协议、温度、浴、测量和粗粒化，而非由 FIB 标签或递归深度唯一决定。

## 190. FIB 网络上的外加湍流间歇性、多重分形与粗粒化闭合

固定 FIB 图 \(G_j=(V_j,E_j)\)，并另选速度或通量场 \(u_j(t)\)、质量内积、外部尺度、时间、非线性算子、噪声和边界。外加动力学可写成
$$
\dot u_j=\mathcal N_j(u_j)-\nu_jA_ju_j+f_j .
\tag{190.1}
$$
取粗粒投影 \(P_{j,\ell}\)，令 \(u_{j,\ell}=P_{j,\ell}u_j\)，则精确投影满足
$$
\dot u_{j,\ell}
=\mathcal N_{j,\ell}(u_{j,\ell})-\nu_jA_{j,\ell}u_{j,\ell}+f_{j,\ell}
+\tau_{j,\ell}-\nu_jR_{j,\ell},
\tag{190.2}
$$
其中
$$
\tau_{j,\ell}=P_{j,\ell}\mathcal N_j(u_j)-\mathcal N_{j,\ell}(u_{j,\ell}),
\qquad
R_{j,\ell}=P_{j,\ell}A_ju_j-A_{j,\ell}u_{j,\ell}.
\tag{190.3}
$$
这两个项是未解析尺度的精确残差，不由 FIB 接缝直接给出。若粗粒非线性在所选内积下反对称，粗粒能量的通量项可写为
$$
\Pi_{j,\ell}=-\langle u_{j,\ell},\tau_{j,\ell}\rangle .
\tag{190.4}
$$
非零平均通量还需要外加源、汇、尺度局部性和统计稳态；有限图能量守恒本身不产生惯性区。

给定外部嵌入和尺度边集 \(\mathcal E_{j,\ell}\)，定义结构函数
$$
S_{j,p}(\ell)=\frac1{|\mathcal E_{j,\ell}|}
\sum_{e\in\mathcal E_{j,\ell}}\mathbb E|(\mathrm B_ju_j)_e|^p .
\tag{190.5}
$$
只有在共同图极限和幂律窗口已被外加规定时，才可写 \(S_{j,p}(\ell)\asymp\ell^{\zeta_p}\)。平坦度
$$
F_j(\ell)=\frac{S_{j,4}(\ell)}{S_{j,2}(\ell)^2}
\tag{190.6}
$$
随尺度增加可作为间歇性候选，但有限图回归不能证明幂律。若另加连续嵌入和多重分形谱 \(\mathcal D(h)\)，可提出
$$
\zeta_p=\inf_h\{ph+d-\mathcal D(h)\},
\tag{190.7}
$$
其中 \(d\) 和 \(\mathcal D\) 都是外加几何假设；图谱维不能自动替代 \(d\)。

闭合可用条件期望表示：
$$
\overline\tau_{j,\ell}(v)
=\mathbb E[\tau_{j,\ell}\mid u_{j,\ell}=v],
\qquad
\xi_{j,\ell}=\tau_{j,\ell}-\overline\tau_{j,\ell}(u_{j,\ell}),
\qquad
\mathbb E[\xi_{j,\ell}\mid u_{j,\ell}]=0 .
\tag{190.8}
$$
零条件均值不表示白噪声或无记忆。细尺度长相关时，精确消元可出现
$$
\dot u_{j,\ell}(t)=F_{j,\ell}(u_{j,\ell}(t))
+\int_0^tK_{j,\ell}(t-s,u_{j,\ell}(s))\,{\rm d}s+\eta_{j,\ell}(t),
\tag{190.9}
$$
记忆核和噪声由全状态律及初始分布决定。细尺度混合快且存在严格时间尺度分离时，才可近似局部 Markov 闭合和白噪声。

同一 FIB 层级可外加高斯 Ornstein–Uhlenbeck 场，也可外加乘法级联 \(g_{\ell/b}=W_\ell g_\ell\)，后者给出
$$
\zeta_p=-\log_b\mathbb E(W^p)
\tag{190.10}
$$
并可产生非线性标度。两种实现可共享低阶统计却有不同通量尾部和记忆。先固定图再平均的 quenched 统计与先平均图族的 annealed 统计也不必相同。因此能谱、间歇指数和闭合律均依赖外加动力学、过滤器、随机律、源汇和物理尺度，不能归因于 FIB 递归本身。

## 191. FIB 细胞复形上的外加 Regge 型曲率、离散引力与因果三角剖分统计

FIB 递归可提供胞腔附着和细化路径，但没有内禀维数、长度或因果锥。另选有限 \(n\) 维单纯复形 \(\mathcal K_j\)，为每条边 \(e\) 指定长度 \(\ell_e\)，使各单纯形非退化。曲率集中在余维二铰链 \(h\)，欧氏亏角为
$$
\delta_h=2\pi-\sum_{\sigma\supset h}\theta_h^\sigma(\ell).
\tag{191.1}
$$
给定 \(G,\Lambda\) 和边界项，Regge 作用量可写为
$$
S_R[\ell;\mathcal K_j]
=\frac1{8\pi G}\left[
\sum_hV_{n-2}(h)\delta_h-\Lambda\sum_\sigma V_n(\sigma)
\right]+S_\partial[\ell].
\tag{191.2}
$$
固定组合复形并对长度变分得到离散场方程；改变长度约束、胞腔粘合或边界变分空间，方程也随之改变。Lorentz 版本还需给每条边因果类型、离散时间函数和允许的 \((p,q)\) 单纯形；FIB 的有向边或递归先后不能代替时间函数，欧氏亏角也不能直接代替双曲因果角。

固定测度、积分域和边界后，欧氏配分函数与 Lorentz 振幅分别形如
$$
Z_E=\int_{\mathcal D}d\mu(\ell)e^{-S_{E,R}(\ell;\mathcal K)/\hbar},
\qquad
Z_L=\sum_{\mathcal K\in\mathfrak C_{\rm FIB}}\frac1{C(\mathcal K)}
\int_{\mathcal D_L(\mathcal K)}d\mu(\ell)e^{{\rm i}S_R(\ell;\mathcal K)/\hbar}.
\tag{191.3}
$$
Wick 延拓、规范固定、积分轮廓和是否求和于不同粘合都需单独证明或规定。若另加全局切片和正转移核，可定义 CDT 型统计
$$
\mathsf T(T',T)=\sum_{B:T\to T'}\frac{e^{-S_E(B)/\hbar}}{C(B)},
\qquad
Z_N(T_N,T_0)=\langle T_N|\mathsf T^N|T_0\rangle .
\tag{191.4}
$$
Lorentz 振幅本身不提供概率律；正性和归一化必须外加。

几何观测可取总体积、积分曲率和切片体积
$$
\mathcal V=\sum_\sigma V_n(\sigma),\qquad
\mathcal R=\sum_hV_{n-2}(h)\delta_h,\qquad
V(k)=\sum_{\sigma:t(\sigma)=k}V_n(\sigma).
\tag{191.5}
$$
对偶图上的扩散还可定义谱维
$$
P_{\mathcal K}(\sigma)=\frac1{|V^*|}\sum_{x\in V^*}
\langle x|e^{-\sigma\Delta_{\mathcal K}^*}|x\rangle,
\qquad
d_s(\sigma)=-2\frac{d\log P_{\mathcal K}}{d\log\sigma}.
\tag{191.6}
$$
扩散步长、对偶权重、系综平均次序和边界均为外加；谱维流动不能代替亏角曲率。

若 FIB 层级给出细化 \(q_{j+1,j}:\mathcal K_{j+1}\to\mathcal K_j\)，连续极限还需规定长度缩放、\(G_j,\Lambda_j\) 的重整化、测度和观测量推前。形式上的粗粒化权重
$$
e^{-S_j^{\rm eff}(\ell_j)/\hbar}
=\int_{q_{j+1,j}(\ell_{j+1})=\ell_j}
d\mu_{j+1}(\ell_{j+1})e^{-S_{E,R,j+1}(\ell_{j+1})/\hbar}
\tag{191.7}
$$
没有这些条件就不定义连续 Einstein 方程或普适固定点。相同组合骨架可配不同度量、签名和系综，得到平直、因果传播、不同曲率涨落或不同相结构；FIB 本身不决定离散引力统计。

## 192. FIB 网络上的外加超导 Ginzburg–Landau、磁通量子化、涡旋与 Josephson 统计

FIB 图可提供顶点、边和可选环路；面胞腔、取向和填充关系仍需外加。令 \(B_0\) 为顶点到边的关联矩阵，\(B_1\) 为边到面胞腔的关联矩阵，满足 \(B_1B_0=0\)。对顶点序参量 \(\psi_v\in\mathbb C\)、边规范势 \(A_e\in\mathbb R\) 和耦合 \(q\)，定义
$$
(D_A\psi)_e=e^{-{\rm i}qA_e}\psi_{h(e)}-\psi_{t(e)},
\qquad
B_f=(B_1A)_f .
\tag{192.1}
$$
规范变换
$$
\psi_v\mapsto e^{{\rm i}q\chi_v}\psi_v,\qquad
A\mapsto A+B_0\chi
\tag{192.2}
$$
保持 \(|D_A\psi|\) 和 \(B\) 不变。一个外加离散 Ginzburg–Landau 自由能为
$$
\mathcal F(\psi,A)
=\sum_vw_v\left[\alpha(T)|\psi_v|^2+\frac\beta2|\psi_v|^4\right]
+\frac\kappa2\sum_ew_e|(D_A\psi)_e|^2
+\frac1{2\mu}\sum_fw_f(B_f-B_f^{\rm ext})^2 .
\tag{192.3}
$$
系数、温度、磁场、边界和时间尺度不由 FIB 递归给出。可再选时间依赖梯度流；无电流边界、周期边界和 Josephson 接触会产生不同极小值与动力学。

在 \(\psi_v\ne0\) 的区域写 \(\psi_v=|\psi_v|e^{{\rm i}\theta_v}\)。沿闭环 \(C\) 的紧致相位绕数满足
$$
\sum_{e\in C}(\theta_{h(e)}-\theta_{t(e)})=2\pi n_C,\qquad
\sum_{e\in C}\varphi_e=2\pi n_C-q\Phi_C,
\tag{192.4}
$$
其中 \(\varphi_e=\theta_{h(e)}-\theta_{t(e)}-qA_e\)，\(n_C\in\mathbb Z\)，\(\Phi_C\) 是外加面胞腔定义的环路磁通。在深 Meissner 区域协变相位梯度趋于零时，
$$
\Phi_C=n_C\Phi_0,\qquad \Phi_0=\frac{2\pi}{q}\quad(\hbar=1),
\tag{192.5}
$$
物理单位下 Cooper 对给出 \(\Phi_0=h/(2e)\)。这要求紧致单值相位、闭环和没有零幅度路径；相位非紧致、环路开口或涡旋核心都会改变直接推导。故磁通量子化来自外加规范结构，不是 FIB 标签的内禀单位。

涡旋由幅度压低和非零相位绕数共同定义。相干长度与穿透深度之比 \(\kappa_{\rm GL}=\lambda/\xi\) 由 GL 系数、规范耦合和离散谱决定；连续各向同性近似下 \(1/\sqrt2\) 分界只是在特定模型中的第一类/第二类判据。有限图、各向异性边权、外磁通和面面积会改变涡旋数、间距和钉扎位置。若两个顶点簇以弱耦合结相连，可另加
$$
\mathcal F_{J,e}=-E_{J,e}\cos\varphi_e,\qquad
I_e=I_{c,e}\sin\varphi_e,\qquad
\dot\varphi_e=\frac{2e}{\hbar}V_e .
\tag{192.6}
$$
含电容、电阻、偏置和随机驱动的 RCSJ 方程可写成
$$
C_e\frac{\Phi_0}{2\pi}\ddot\varphi_e
+\frac{\Phi_0}{2\pi R_e}\dot\varphi_e
+I_{c,e}\sin\varphi_e
=I_e^{\rm bias}+\eta_e(t).
\tag{192.7}
$$
只有另加热浴温度和涨落—耗散关系时，\(\eta_e\) 才是热噪声；phase slip、Shapiro 台阶和电压分布依赖结参数、驱动、噪声和网络环路。

若图列细化、面权和 \(\xi,\lambda\) 按外加规则缩放，(192.3) 可趋向连续二维或三维 GL 泛函；先取 \(q\to0\)、强阻尼或不同热力学极限会改变量子化、动力学和涡旋统计。振幅观测可以看见 \(|\psi|^2\) 却看不见环路绕数，稀疏电流观测也可能漏掉同调环路的磁通。因此正常态、Meissner 态、涡旋晶格、随机 Josephson 相滑移及其统计均是外加参数和边界条件下的模型结论，不存在由 FIB ATOM 递归单独确定的普适超导定律。

## 193. FIB 网络上的外加超流体、Gross–Pitaevskii 动力学与量子涡旋

固定 FIB 图 \(G_j=(V_j,E_j)\)，另给顶点质量、边长、空间嵌入和面胞腔。FIB 只给顶点、边、词序和合法路径，不给 \(m,\hbar\)、相互作用、化学势、温度或物理距离。给顶点复振幅 \(\psi_v\) 和外加权重，可定义
$$
H_j(\psi)=\sum_v\left[V_{j,v}|\psi_v|^2+\frac{g_{j,v}}2|\psi_v|^4\right]
+\sum_{e=(u,v)}K_{j,e}|\psi_v-\psi_u|^2,
\tag{193.1}
$$
$$
{\rm i}\hbar\dot\psi_v=\frac{\partial H_j}{\partial\bar\psi_v}.
\tag{193.2}
$$
无泵浦、无耗散且参数静态时，全局 \(U(1)\) 对称性给出
$$
N_j=\sum_v|\psi_v|^2,\qquad \frac{{\rm d}N_j}{{\rm d}t}=0 .
\tag{193.3}
$$
稳态 \(\psi_v=e^{-{\rm i}\mu t/\hbar}\phi_v\) 满足
$$
\mu\phi_v=\frac{\partial H_j}{\partial\bar\phi_v}.
\tag{193.4}
$$
凝聚、局域集中和调制不稳定取决于 \(g\)、图谱、边界、固定 \(N\) 还是固定 \(\mu\)，以及外加耗散。沿边的质量流和相位速度可写成
$$
\mathcal J_{u\to v}=\frac{2K_{j,e}}{\hbar}{\rm Im}(\bar\psi_u\psi_v),
\qquad
v_e=\frac{\hbar}{m}\frac{\theta_v-\theta_u}{\ell_e},
\tag{193.5}
$$
其中 \(\psi_v=\sqrt{n_v}e^{{\rm i}\theta_v}\)，边长 \(\ell_e\) 仍为外加量。

若闭环 \(C\) 上振幅处处非零，单值相位给出
$$
\sum_{e\in C}{\rm unwrap}(\theta_{h(e)}-\theta_{t(e)})=2\pi n_C,
\qquad
\Gamma_C=\sum_{e\in C}\ell_ev_e=n_C\frac hm .
\tag{193.6}
$$
树图没有非平凡绕数；面填充、相位单值性和涡旋核心正则化必须另行指定。在外加细化和连续嵌入下，模型可趋向
$$
{\rm i}\hbar\partial_t\psi=
\left[-\frac{\hbar^2}{2m}\Delta+V+g|\psi|^2\right]\psi .
\tag{193.7}
$$
均匀排斥凝聚的 Bogoliubov 色散为
$$
\hbar^2\omega^2(k)=\varepsilon_k(\varepsilon_k+2g\rho_0),
\qquad
\varepsilon_k=\frac{\hbar^2|k|^2}{2m},
\tag{193.8}
$$
离散图上须用外加拉普拉斯谱替代 \(|k|^2\)。声速、愈合长度和 Landau 临界速度依赖 \(g,m,\rho_0\)、缺陷和探针；有限温度的涡旋产生湮灭还需噪声和耗散。只测 \(|\psi|^2\) 看不见环路绕数，因此超流态、涡旋晶格和正常态均不是 FIB 单独决定的。

## 194. FIB 路径上的外加辐射输运、黑体辐射与光学厚度极限

固定 FIB 路径并外加每条边的长度、方向、时间步长和光子频率 \(\nu\)。FIB 只给可拼接状态与次序；光速、频率测度、吸收/散射截面、发射源、温度和边界入射量均外加。离散输运可写成
$$
I_{k+1}(\nu,\Omega)
=\int K_k(\nu,\Omega\mid\nu',\Omega')I_k(\nu',\Omega')\,{\rm d}\nu'{\rm d}\Omega'
+S_k(\nu,\Omega).
\tag{194.1}
$$
连续嵌入中，给定 \(\kappa_\nu,\sigma_\nu,j_\nu\) 和相函数 \(p_\nu\)，比强度满足
$$
\frac1c\partial_tI_\nu+\Omega\cdot\nabla_xI_\nu
=-(\kappa_\nu+\sigma_\nu)I_\nu+j_\nu
+\sigma_\nu\int_{S^2}p_\nu(\Omega,\Omega')I_\nu(\Omega')\,{\rm d}\Omega'.
\tag{194.2}
$$
令
$$
u_\nu=\frac1c\int_{S^2}I_\nu\,{\rm d}\Omega,\qquad
F_\nu=\int_{S^2}\Omega I_\nu\,{\rm d}\Omega .
\tag{194.3}
$$
频率保持的弹性散射下，
$$
\partial_tu_\nu+\nabla\cdot F_\nu=4\pi j_\nu-c\kappa_\nu u_\nu .
\tag{194.4}
$$
若光学厚度大、角向混合充分且边界层可分离，输运消光 \(\chi_\nu^{\rm tr}=\kappa_\nu+\sigma_\nu(1-g_\nu)\) 给出
$$
F_\nu=-D_\nu\nabla u_\nu+O(\epsilon_\nu^2),
\qquad D_\nu=\frac{c}{3\chi_\nu^{\rm tr}},
\qquad \epsilon_\nu=\frac1{L(\kappa_\nu+\sigma_\nu)} ,
\tag{194.5}
$$
以及辐射扩散方程
$$
\partial_tu_\nu-\nabla\cdot(D_\nu\nabla u_\nu)
=4\pi j_\nu-c\kappa_\nu u_\nu+O(\epsilon_\nu^2).
\tag{194.6}
$$
光学薄区沿特征线自由传播；重尾自由程可产生 Lévy 超扩散，不能由 FIB 路径长度决定。

Planck 谱还要求局部热平衡、Kirchhoff 关系、各向同性腔和零光子化学势：
$$
j_\nu=\kappa_\nu B_\nu(T),\qquad
B_\nu(T)=\frac{2h\nu^3}{c^2}\frac1{e^{h\nu/(k_BT)}-1},
\tag{194.7}
$$
$$
u_\nu^{\rm eq}=\frac{4\pi}{c}B_\nu(T).
\tag{194.8}
$$
只有弹性散射而没有数目改变的发射/吸收时，平衡可带非零化学势而非必然 Planck 谱。只测总强度无法分别识别频率依赖的吸收、散射和发射。自由流、厚介质扩散、超扩散、LTE 腔和非 LTE 稳态都可由同一 FIB 接续承载，具体选择来自外加核、边界和热力学条件。

## 195. FIB 关系网络上的外加地震/断层动力学、Gutenberg–Richter 震级律与 Omori 余震统计

固定 FIB 图 \(G_j=(V_j,E_j)\)，选出可解释为断层片段的边集 \(\mathcal F_j\)。FIB 只给接缝和层级；坐标、片段面积、弹性模量、应力、摩擦、加载时钟、破裂准则、波速和观测窗均外加。给滑移 \(s_e(t)\)、剪应力 \(\tau_e(t)\) 和弹性传递矩阵 \(K_j\)，准静态模型为
$$
\tau(t)=\tau^0+\dot\tau_{\rm load}t-K_js(t).
\tag{195.1}
$$
\(K_j\) 来自外加弹性 Green 函数和边界，不能等同 FIB 邻接矩阵。库仑裕度和速率—状态摩擦可写成
$$
C_e=\tau_e-\mu_e(V_e,\theta_e)\sigma_{n,e},
\qquad
\mu_e=\mu_{0,e}+a_e\log\frac V{V_{0,e}}+b_e\log\frac{\theta V_{0,e}}{D_{c,e}} .
\tag{195.2}
$$
触发、应力更新和动态波传播由外加规则决定。

一次事件的地震矩和震级可取
$$
M_0(E)=\sum_{e\in\mathcal F_j}G_eA_e|\Delta s_e|,
\qquad
m_w(E)=\frac23\log_{10}\frac{M_0(E)}{M_\star}.
\tag{195.3}
$$
在完备区间，经验 Gutenberg–Richter 关系为
$$
\mathbb EN([m,\infty);T)\simeq C_T10^{-bm},
\qquad m_c\le m\le m_{\max}(L).
\tag{195.4}
$$
\(b\) 不由 FIB 分支数、词频或递归深度给出。给定主震与余震分类，改进 Omori 形式为
$$
r(t\mid m_0)=r_{\rm bg}+K10^{\alpha(m_0-m_c)}(t+c)^{-p}.
\tag{195.5}
$$
带空间核的 Hawkes/ETAS 过程还需震级分布、时间核和空间触发核；分支比 \(n<1\) 才给出有限平均簇，\(n\approx1\) 可产生长相关。检测概率 \(q(m,x,t)\) 使
$$
\lambda_{\rm obs}(x,t,m)=q(m,x,t)\lambda_{\rm true}(x,t,m),
\tag{195.6}
$$
早期余震拥挤、空间盲区、震级饱和、去簇和观测窗会偏移 \(b,p,c\)。断层破裂也不自动等同 Abelian 沙堆：前者通常非交换并含波传播与历史依赖，后者的交换性和守恒—耗散账式需另行证明。因此地震标度是外加接触、摩擦、应力传递和观测条件下的经验或模型结论。

## 196. FIB 路径上的外加核衰变、分支 Markov 链与放射性计数统计

固定 FIB 上下文路径，另给有限核素状态集 \(\mathcal S\)。FIB 不给质量、能级、核矩阵元、衰变通道或时间单位。对状态 \(i\) 给总衰变率 \(\lambda_i\) 和分支比 \(b_{ij}^{(c)}\)，满足
$$
\sum_{j,c}b_{ij}^{(c)}=1,\qquad
q_{ij}=\sum_c\lambda_i b_{ij}^{(c)}\mathbf1_{j\ne i},\qquad
q_{ii}=-\lambda_i .
\tag{196.1}
$$
常率 Markov 近似下，
$$
S_i(t)=e^{-\lambda_i t},\qquad
f_i(t)=\lambda_i e^{-\lambda_i t},\qquad
t_{1/2}=\frac{\log2}{\lambda_i}.
\tag{196.2}
$$
有限初始样本满足
$$
N(t)\sim{\rm Binomial}(N_0,e^{-\lambda_i t}),
\qquad
\mathbb EN(t)=N_0e^{-\lambda_i t},
\tag{196.3}
$$
所以有限样本计数不是严格 Poisson；Poisson 只在稀有事件和相应大样本极限中出现。

分支链由
$$
\frac{{\rm d}}{{\rm d}t}p(t)=p(t)Q,\qquad p(t)=p(0)e^{tQ}
\tag{196.4}
$$
描述；Bateman 级联是矩阵指数的特殊情形。量子谱下界会破坏全时指数律：
$$
S(t)=|\langle\psi|e^{-{\rm i}Ht}|\psi\rangle|^2
=1-(\Delta H)^2t^2+O(t^3),
\tag{196.5}
$$
短时可有 Zeno 抑制，中间时指数段需弱记忆，长时可出现 \(S(t)\asymp t^{-p}\)。随机环境给出
$$
S_i(t\mid\omega)=\exp\!\left[-\int_0^t\lambda_i(s,\omega)\,{\rm d}s\right],
\tag{196.6}
$$
环境平均通常产生混合指数和过度离散，不能以 \(\exp[-t\,\mathbb E\lambda]\) 代替。

级联后代数 \(K\) 的稀疏计数可有复合 Poisson 生成函数
$$
G_N(z)=\exp[\Lambda(G_K(z)-1)],
\qquad {\rm Var}N=\Lambda\mathbb EK^2,
\tag{196.7}
$$
重尾等待时间则产生更新过程而非固定半衰期。探测效率、能量响应、死时间、背景和脉冲堆积进一步改变计数；理想 Poisson 稀疏化只在独立保留且无死时间时保持 Poisson。只测总计数通常只能识别初始活度、衰变率和效率的乘积，能谱与寿命也可能在观测纤维中混淆。故指数衰减、非指数修正、级联和更新统计均需外加核物理与探测条件。

## 197. FIB 关系网络上的外加电化学离子输运、Nernst–Planck/Poisson、Butler–Volmer 与阻抗统计

固定 FIB 孔道—接触骨架 \(G_j=(V_j,E_j)\)，另指定顶点体积、边长、孔隙截面和电极。FIB 不给浓度、扩散系数、迁移率、介电常数、价态、温度、反应或电势单位。离散电化学势和通量可取
$$
\mu_{\alpha,v}=k_BT\log c_{\alpha,v}+z_\alpha F\phi_v+\mu_{\alpha,v}^{\rm ext},
\tag{197.1}
$$
$$
J_{\alpha,e}=-M_{\alpha,e}\bar c_{\alpha,e}(B\mu_\alpha)_e,
\qquad
\dot c_\alpha=B^{\mathsf T}J_\alpha+S_\alpha .
\tag{197.2}
$$
取 \(M_{\alpha,e}=D_{\alpha,e}/(k_BT)\) 得离散 Nernst–Planck 形式
$$
J_{\alpha,e}=-D_{\alpha,e}(Bc_\alpha)_e
-\frac{z_\alpha FD_{\alpha,e}}{k_BT}\bar c_{\alpha,e}(B\phi)_e .
\tag{197.3}
$$
空间电荷模型还需离散 Poisson 方程
$$
L_j^\varepsilon\phi=B^{\mathsf T}W_j^\varepsilon B\phi
=\rho_{\rm ch},\qquad
\rho_{{\rm ch},v}=F\sum_\alpha z_\alpha c_{\alpha,v}+\rho_v^{\rm fixed}.
\tag{197.4}
$$
当 Debye 长度与孔道尺度之比 \(\lambda_D/L\to0\) 时可外加电中性约束
$$
F\sum_\alpha z_\alpha c_\alpha+\rho^{\rm fixed}=0,
\tag{197.5}
$$
而 \(\lambda_D/L=O(1)\) 时双电层、空间电荷和浓差极化不可忽略。

反应接触上的 Butler–Volmer 关系为
$$
j_r=j_{0,r}\left[
\exp\!\left(\frac{\alpha_{a,r}F\eta_r}{RT}\right)
-\exp\!\left(-\frac{\alpha_{c,r}F\eta_r}{RT}\right)
\right],
\tag{197.6}
$$
$$
E_r^{\rm eq}=E_r^\circ+\frac{RT}{n_rF}\log\frac{a_{\rm ox}}{a_{\rm red}},
\qquad
\eta_r=\Delta\phi_r-E_r^{\rm eq}.
\tag{197.7}
$$
交换电流、转移系数、活度、化学计量和接触面积均外加。双电层与外部电路可加入
$$
i_r=C_{{\rm dl},r}\dot\eta_r+A_rj_r+i_r^{\rm ext}.
\tag{197.8}
$$
热噪声解释还需要温度和涨落—耗散关系。

对稳态作线性化，端电流的频域导纳和阻抗可写成
$$
\mathsf Y_j(\omega)
=\mathsf Y_{\infty,j}
+\mathsf C_j({\rm i}\omega I-\mathsf A_j)^{-1}\mathsf B_j,
\qquad
\mathsf Z_j(\omega)=\mathsf Y_j(\omega)^{-1}.
\tag{197.9}
$$
半无限连续孔道、特定谱密度和扩散边界下才出现 Warburg 型 \(\omega^{-1/2}\)；有限图、空间电荷和反应边界会产生多个时间常数或不同幂律。电中性、空间电荷和电极反应极限由 \(\lambda_D/L\)、Damköhler 数及取极限次序决定。只测总电流时，内部浓度极化和电势模态可能完全不可见；不同参数也可保持 \(L^2/D\)、\(\lambda_D/L\) 或 \(R_{\rm ct}C_{\rm dl}\) 等组合不变而产生相同有限频带阻抗。

因此 FIB 只提供孔道与接触的组合骨架。Nernst–Planck/Poisson、Butler–Volmer、电中性或空间电荷极限以及阻抗谱均依赖浓度、迁移率、介电权重、反应化学计量、温度、边界、噪声和连续极限等外加结构；同一 FIB 网络可在这些结构变化下呈现欧姆输运、空间电荷限制、反应极化或不同阻抗统计，不存在由 FIB ATOM 递归单独确定的普适电化学定律。

## 198. FIB 网络上的外加颗粒气体、非弹性碰撞、Haff 冷却与团簇不稳定

固定 FIB 关系给出的有限接触骨架 \(G_j=(V_j,E_j)\)，另指定粒子质量、位置、速度、有效截面、接触法向和边界。对接触边 \(e=(a,b)\)，法向相对速度为 \(g_n=(v_a-v_b)\cdot n_e\)，恢复系数为 \(e_e\in[0,1]\)。无切向摩擦的碰撞规则可写成
$$
v_a'=v_a-\frac{m_b}{m_a+m_b}(1+e_e)g_nn_e,\qquad
v_b'=v_b+\frac{m_a}{m_a+m_b}(1+e_e)g_nn_e,
\tag{198.1}
$$
其动能损失为
$$
\Delta E_e=-\frac12\frac{m_am_b}{m_a+m_b}(1-e_e^2)g_n^2.
\tag{198.2}
$$
接触边、法向、恢复系数和碰撞率全是外加规则，FIB 不提供物理接触或耗散。

稀薄图索引动力学可抽象为
$$
\partial_tf_v+\operatorname{div}_j\mathcal F_j[f]_v
=\sum_{e\ni v}\gamma_eQ_e^{(e_e)}(f_v,f_{v_e})
+\mathcal T_vf_v+\mathcal S_v .
\tag{198.3}
$$
Boltzmann 近似要求分子混沌；有限密度、重复邻接和图环路造成的关联需 Enskog 或更高阶闭合。对速度分布取矩后，连续嵌入下的密度、动量和温度方程含压力、黏性、热流、拖曳、驱动和冷却率；这些量没有边长和权重就没有确定物理量纲。

自由冷却、均匀密度、无驱动、无拖曳和常数 \(e<1\) 的自相似近似给出
$$
\frac{{\rm d}T}{{\rm d}t}=-\Lambda_eT^{3/2},
\qquad
T(t)=T_0\left(1+\frac t{t_H}\right)^{-2}.
\tag{198.4}
$$
\(\Lambda_e\) 依赖密度、截面、质量和 \(1-e^2\)；速度相关恢复系数、摩擦、有限密度和边界散热会改变 Haff 指数或前因子。若以外加赋权拉普拉斯 \(L_j\) 分解图模态，线性化扰动可写成
$$
\partial_\tau\widehat z_\ell
=\mathsf M_{0,j}\widehat z_\ell-\lambda_{\ell,j}\mathsf M_{1,j}\widehat z_\ell .
\tag{198.5}
$$
某模态矩阵有正实部时会形成密度团簇或剪切结构；判据依赖碰撞、压力和输运闭合，不能用图度数或递归深度代替。

驱动系统的能量账式还需外加注入、恒温器、振动边界或剪切：
$$
\frac{{\rm d}}{{\rm d}t}\left(\frac d2\sum_vn_vT_v\right)
=\mathcal P_{\rm in}-\sum_vn_v\zeta_vT_v-\mathcal D_{\rm drag}
+\mathcal F_{\rm bdry}.
\tag{198.6}
$$
自由冷却、稀薄 Boltzmann 和驱动稳态不是同一极限；非弹性颗粒气体也不自动等同沙堆、堵塞或弹性网络。只测全图平均温度通常只能识别冷却系数的组合，不能分离密度、截面、恢复系数和图结构。因此 Haff 冷却、团簇不稳定和非平衡速度统计都是外加碰撞与驱动模型的条件结论。

## 199. FIB 路径上的外加 Dicke 超辐射、集体自发辐射与光子统计

固定 FIB 上下文路径，并将每个选定上下文映射为外加二能级发射体。FIB 只给接续或耦合骨架；位置、偶极矩、能级、腔模、真空谱密度、初态、耗散和探测通道均外加。闭合发射体模型可写为
$$
H_S=\frac12\sum_i\omega_i\sigma_i^z
+\sum_{i\ne j}J_{ij}\sigma_i^+\sigma_j^-
+\sum_{i,\mu}(g_{i\mu}a_\mu\sigma_i^+
+g_{i\mu}^*a_\mu^\dagger\sigma_i^-).
\tag{199.1}
$$
在 Born–Markov、旋波和外加真空浴近似下，
$$
\dot\rho=-{\rm i}[H_{\rm eff},\rho]
+\sum_{i,j}\Gamma_{ij}\left(
\sigma_j^-\rho\sigma_i^+
-\frac12\{\sigma_i^+\sigma_j^-,\rho\}\right),
\tag{199.2}
$$
其中 \(\Gamma\) 必须半正定，其非对角元由外加 Green 函数、偶极矩和空间相位决定。辐射强度为
$$
I(t)=\sum_{i,j}\Gamma_{ij}
\langle\sigma_i^+\sigma_j^-\rangle_t .
\tag{199.3}
$$
若 \(\Gamma_{ij}=\gamma\)，唯一亮跳跃算子为
$$
L=\sqrt\gamma\,J^-,
\qquad J^-=\sum_i\sigma_i^-,
\tag{199.4}
$$
对称初态和公共浴下 \(I(t)=\gamma\langle J^+J^-\rangle\) 可在脉冲中段达到 \(O(N^2)\)，而独立辐射为 \(O(N)\)。失谐、位置无序、去相干和边界会削弱增强。

一般有限图给出
$$
\Gamma=\sum_\alpha\gamma_\alpha v_\alpha v_\alpha^\dagger,\qquad
L_\alpha=\sqrt{\gamma_\alpha}\sum_i(v_\alpha)_i\sigma_i^- .
\tag{199.5}
$$
大 \(\gamma_\alpha\) 是亮模，小或零本征值对应亚辐射或暗模；其寿命和权重由初态重叠及外加浴决定。保留单个腔模时，Tavis–Cummings 哈密顿量和腔损耗可产生 Rabi 分裂，但 \(\omega_c,g,\kappa_c\) 仍是外加量。

光子计数需要倾斜 Liouvillian
$$
\mathcal L_s=\mathcal L_0+(e^s-1)\mathcal J_d,\qquad
Z(s,T)={\rm tr}\,e^{T\mathcal L_s}\rho_0,
\tag{199.6}
$$
二阶相关可写为
$$
g^{(2)}(\tau)=
\frac{{\rm tr}[\mathcal J_d e^{\tau\mathcal L}\mathcal J_d\rho_{\rm ss}]}
{({\rm tr}\mathcal J_d\rho_{\rm ss})^2}.
\tag{199.7}
$$
超辐射脉冲、单体反聚束、暗态长尾和腔反馈会产生不同 Fano 因子与相关函数；探测孔径、偏振、背景和时间窗也会改变观测。只测总强度不能分别恢复 \(\Gamma\)、偶极矩和暗模。故独立辐射、超辐射与亚辐射均是外加量子光学和探测条件下的结论，不是 FIB 接续关系自身的定律。

## 200. FIB 区域网络上的外加气候能量平衡、温室反馈与随机统计

固定 FIB 区域图 \(G_j=(V_j,E_j)\)。顶点只表示区域或层级单元，边只表示可能交换；面积、纬度、高度、热容、辐射参数、边界位置和气候时间尺度均外加。全局一箱模型为
$$
C\frac{{\rm d}T}{{\rm d}t}
=Q(t)(1-\alpha(T))-R(T,\chi)+F_{\rm ext}(t)+\eta(t),
\tag{200.1}
$$
其中 \(R(T,\chi)\) 是外加辐射闭合，\(\chi\) 表示温室气体、云或水汽状态。平衡 \(F(T)=Q(1-\alpha(T))+F_{\rm ext}-R(T,\chi)=0\) 的稳定性由 \(F'(T_*)\) 决定；冰反照率和温室反馈可以产生多平衡、鞍结和滞回，但需要具体参数化。

在区域图上给热容 \(C_v\)、输入 \(Q_v\)、交换权 \(K_{uv}\) 和温室闭合 \(R_v\)，可写
$$
C_v\dot T_v=Q_v(1-\alpha_v)-R_v-(L_KT)_v+F_v+\eta_v,
\qquad
(L_KT)_v=\sum_uK_{uv}(T_v-T_u).
\tag{200.2}
$$
对称内部边的热量在全图求和时抵消，开放边界和海洋/冰盖通量须另加。线性化后的谱 \(A=C^{-1}(L_K+R_T+Q\alpha_T)\) 给出区域松弛时间；FIB 边数和词频只有在映射到 \(K,C\) 后才影响它。

在稳定矩阵 \(A\) 和白噪声下，
$$
{\rm d}\vartheta=-A\vartheta\,{\rm d}t+B\,{\rm d}W_t,
\qquad
A\Sigma+\Sigma A^{\mathsf T}=BB^{\mathsf T}.
\tag{200.3}
$$
有色噪声、重尾跳跃和乘法噪声会改变平稳分布与极端尾。最小恢复率下降可产生临界减速候选，但噪声增强和观测滤波也会造成方差、自相关上升；随机诱导、速率诱导和分岔诱导 tipping 需分别建模。单箱与二箱模型可在有限总平均温度窗口内给出相同响应，却有不同区域温差、海洋热含量和长期极端。

若观测 \(Y_k=HT(t_k)+\varepsilon_k\) 只记录总平均，则 \((C,K,R,\alpha,F_{\rm ext})\) 的许多组合不可区分；增加区域温度、热含量、辐射通量和独立强迫实验才可缩小观测纤维。图族的面积权、边界—体积比、交换谱隙、噪声相关和强迫归一化也必须给出，不能把 FIB 图大小直接当作行星半径。故平衡温度、温室响应、随机协方差、tipping 率和极端统计均是外加气候模型的条件结论。

## 201. FIB 网络上的外加毛细润湿、Young–Laplace 压差与液滴统计

固定 FIB 接续图并把部分顶点、边和胞腔嵌入孔道、喉道和固体表面单元。每条喉道另给半径 \(r_e\)、长度 \(L_e\)、截面和粗糙度。FIB 只给接触骨架；表面张力 \(\gamma\)、界面能、接触角、曲率、黏度、密度、压力、重力、蒸发律和边界驱动均外加。液—气界面自由能可写
$$
\mathcal F[\Sigma]=\gamma A_{\ell v}+\gamma_{\ell s}A_{\ell s}
+\gamma_{sv}A_{sv}-\Delta p\,V+\mathcal F_{\rm ext}.
\tag{201.1}
$$
法向变分给 Young–Laplace 条件
$$
\Delta p=\gamma\left(\frac1{R_1}+\frac1{R_2}\right),
\tag{201.2}
$$
固体接触线给 Young 角
$$
\gamma_{sv}-\gamma_{s\ell}=\gamma\cos\theta_e .
\tag{201.3}
$$
圆柱喉道的毛细压差和竖直高度在特定边界下为
$$
p_c=\frac{2\gamma\cos\theta}{r_e},\qquad
h=\frac{2\gamma\cos\theta}{\rho g r_e}.
\tag{201.4}
$$
非圆截面和动态接触线不能用 FIB 边数替代曲率。

接触线滞后满足 \(\theta_R\le\theta\le\theta_A\)；粗糙度、化学斑块和喉道收缩会钉扎接触线并产生跳跃。低 Reynolds 数、不可压、无蒸发且忽略惯性时，单孔浸润长度满足 Washburn 标度
$$
\ell^2(t)-\ell_0^2=\frac{r_e\gamma\cos\theta}{2\mu}\,t .
\tag{201.5}
$$
外加压力、惯性、气体压缩、蒸发和滑移会改变该标度。在网络上，给水力导通率 \(k_e\) 和毛细压差 \(p_{c,e}\)，可写
$$
q_e=-\frac{k_e}{\mu_eL_e}
[p_{v(e)}-p_{u(e)}-p_{c,e}],
\qquad
\sum_{e\ni v}\varepsilon_{ve}q_e=s_v .
\tag{201.6}
$$
串联瓶颈、并联分流、侵入阈值和残余液相均由这些外加参数决定。

热激活脱钉扎可用
$$
\zeta\dot x=-\partial_x\mathcal F(x)+\sqrt{2k_BT\zeta}\,\eta(t),
\qquad
\langle\eta(t)\eta(t')\rangle=\delta(t-t')
\tag{201.7}
$$
表示；大势垒下等待时间具有 Kramers 型指数，但前因子取决于粗糙度、摩擦和噪声相关。只观测 Washburn 前沿只能约束 \(r_e\gamma\cos\theta/\mu\) 的组合，不能分别恢复几何、表面张力、接触角和黏度；总占据率也看不见隐藏残余液相。故平衡形状、侵入团簇、接触线滞后和热涨落均是外加毛细模型的条件结论。

## 202. FIB 网络上的外加聚变等离子体、磁约束、能量增益与输运统计

固定 FIB 网格 \(G_j=(V_j,E_j)\)，把顶点解释为等离子体控制体，把边解释为外加场线或输运通道。体积、磁场、密度、温度、流速、组分和通道几何均需外加。对反应 \(a+b\to\) products，反应率为
$$
R_{ab,v}=\frac{n_{a,v}n_{b,v}}{1+\delta_{ab}}\langle\sigma v\rangle_{ab,v},
\qquad
\langle\sigma v\rangle=\iint f_af_b\sigma(v_{\rm rel})v_{\rm rel}\,{\rm d}v_a{\rm d}v_b .
\tag{202.1}
$$
Maxwell 分布、截面、非热尾和燃料比都不是 FIB 数据。聚变功率 \(P_{\rm fus}=R_{ab}E_{\rm fus}\)，α 自加热还需外加沉积分数。

对各物种粒子数 \(N_{s,v}\) 和热能 \(W_v\)，外加边通量、加热和损失给出
$$
\dot N_{s,v}=-\operatorname{div}_j\Gamma_{s,v}+S_{s,v}+R_{s,v}-L_{s,v},
\tag{202.2}
$$
$$
\dot W_v=-\operatorname{div}_jQ_v+P_{{\rm aux},v}+P_{\alpha,v}
-P_{{\rm rad},v}-P_{{\rm cx},v}-P_{{\rm wall},v}.
\tag{202.3}
$$
能量约束时间和等离子体增益可定义为
$$
\tau_E=\frac W{P_{\rm loss}},\qquad
Q_{\rm plasma}=\frac{P_{\rm fus}}{P_{\rm aux}}.
\tag{202.4}
$$
\(Q_{\rm plasma}>1\) 不等于工程净功率为正；磁体、泵浦和能量转换还需计入再循环功率。

稳态能量约束下的广义 Lawson 条件形如
$$
f_\alpha\frac{n_an_b}{1+\delta_{ab}}\langle\sigma v\rangle E_{\rm fus}
\ge \frac W{\tau_EV}+\frac{P_{\rm rad}+P_{\rm cx}+P_{\rm wall}}V .
\tag{202.5}
$$
只有在组成、温度、能量系数和损失闭合固定后，才可化为 \(n\tau_E\) 或 \(nT\tau_E\) 判据。磁约束还需场拓扑、碰撞率、漂移、湍流谱、开放场线端损失和中性粒子再循环；FIB 边只有在与场线或磁面的映射被声明后才可离散这些通量。新经典、湍流和边缘输运的分解、杂质辐射系数和电荷交换损失均是外加模型。

自加热与损失的温度导数决定局部燃烧稳定性：
$$
C_T\dot T=P_{\rm aux}+f_\alpha P_{\rm fus}(T,n)-P_{\rm loss}(T,n).
\tag{202.6}
$$
正反馈可引起热失稳或跃迁，高辐射和开放边界可使系统受限。随机磁场、加热、杂质和网格族会给出 \(Q_{\rm plasma}\)、\(\tau_E\) 和点火阈值的分布；改变离散分辨率而不改变连续参数不应被误判为物理相变。中子计数主要约束 \(\int n_an_b\langle\sigma v\rangle\,{\rm d}V\)，不能单独分离密度、温度、燃料比和有效体积；总能量与辐射功率也不能在未知 \(\tau_E\) 时分离不同输运机制。

因此 FIB 只提供磁约束通道、控制体和网格组合骨架。反应截面、等离子体状态、磁场拓扑、加热、杂质、辐射、中性粒子、边界和输运闭合均需外加；Lawson 条件、能量增益、燃烧稳定性以及湍流/新经典损失都是这些结构下的条件结论。同一 FIB 骨架可通过改变磁场、燃料、加热和边界从开放低增益状态切换到高约束或辐射受限状态，不存在由 FIB ATOM 递归单独决定的普适聚变定律。

## 203. FIB 网络上的外加声学/弹性超材料、带隙与局域共振统计

固定 FIB 连接—胞腔骨架 \(G_j=(V_j,E_j)\)，另给顶点嵌入、主质量 \(m_v\)、边刚度 \(k_e\)、阻尼和边界。为表示超材料，在顶点或胞腔上附加内部谐振器 \(q_{v,r}\)，质量、刚度和阻尼均为外加。线性模型可写成
$$
M\ddot U+C\dot U+KU=F,
\tag{203.1}
$$
普通网络模态满足
$$
K\varphi_\ell=\omega_\ell^2M\varphi_\ell .
\tag{203.2}
$$
没有内部谐振器时，这是普通声子谱；图度数不能确定声速，因为质量、刚度和长度尺度仍需外加。

对局部谐振器作谐波消元，令 \(\omega_r^2=k_r/m_r\)，可得频率依赖的有效质量
$$
m_{\rm res}^{\rm eff}(\omega)
=\frac{m_r\omega_r^2}{\omega_r^2-\omega^2-{\rm i}(\gamma_r/m_r)\omega}.
\tag{203.3}
$$
在 \(\omega\) 接近 \(\omega_r\) 时，主网络波与内部振子混合，形成不要求晶格常数与波长同阶的局域共振带隙；其中心和宽度由 \(m_r,k_r,\gamma_r\)、附着密度、主刚度和边界决定。周期外加图列若有平移群，可用动力学矩阵
$$
\mathsf D_j(k,\omega)=-\omega^2M_j(\omega)+{\rm i}\omega C_j(\omega)+K_j(k)
\tag{203.4}
$$
求传播支。有限图的传输低谷不能自动等同无限体严格带隙，强阻尼、边界反射和探针耦合也会造成空窗。

带隙内的质量或刚度缺陷可形成局域模，Green 函数在外加图距离 \(r\) 上可能满足
$$
|G_j(v,w;\omega)|\asymp
e^{-r(v,w)/\xi_{\rm loc}(\omega)}.
\tag{203.5}
$$
随机质量、刚度或缺陷还可产生 Anderson 型局域化；其态密度、群延迟和传输分布依赖无序相关与边界。只测总能量不能区分内部谐振器驻留与主网络传播，须联合频率响应、相位和模态形状。普通声子、局域共振、缺陷态和无序输运因此都是外加动力学下的条件统计，不是 FIB 词序的内生带隙定律。

## 204. FIB 路径上的外加非线性光学、参量放大与压缩光统计

固定 FIB 传播路径或耦合网络，另给边长度、模态截面、色散、偏振、边界、泵浦和损耗。FIB 只给传播次序；\(\chi^{(2)}\)、\(\chi^{(3)}\)、相位匹配和探测器均外加。慢变包络下的三波混频可写
$$
\frac{{\rm d}A_s}{{\rm d}z}
=-\frac{\alpha_s}{2}A_s+
{\rm i}\kappa A_pA_i^*e^{{\rm i}\Delta kz},
\qquad
\frac{{\rm d}A_i}{{\rm d}z}
=-\frac{\alpha_i}{2}A_i+
{\rm i}\kappa A_pA_s^*e^{{\rm i}\Delta kz}.
\tag{204.1}
$$
无损、泵浦不耗尽的简化增益含
$$
g=\sqrt{|\kappa A_p|^2-(\Delta k/2)^2},
\tag{204.2}
$$
只有相位匹配和增益超过失配时才有指数放大；四波混频还需 \(\chi^{(3)}\) 和外加有效失配。

量子化的窄带参量相互作用为
$$
H_{\rm sq}={\rm i}\hbar(\zeta a_s^\dagger a_i^\dagger-\zeta^*a_sa_i),
\tag{204.3}
$$
产生 Bogoliubov 变换
$$
a_s^{\rm out}=\cosh r\,a_s^{\rm in}
+e^{{\rm i}\phi}\sinh r\,a_i^{{\rm in}\dagger},
\tag{204.4}
$$
其中 \(r=|\zeta|t\)。双模真空输入的单模边缘为热分布，简并模式的最小正交方差为
$$
V_{\min}=\tfrac12e^{-2r},
\tag{204.5}
$$
探测效率 \(\eta\) 会把未探测真空混入方差。损耗、泵浦相位噪声、热占据和泵浦耗尽会抬高噪声并破坏线性 Bogoliubov 近似。

FIB 多边组合后可写为
$$
\mathbf a_{\rm out}=M\mathbf a_{\rm in}
+N\mathbf a_{\rm in}^\dagger+\mathbf n_{\rm loss},
\tag{204.6}
$$
无损时需满足保对易条件 \(MM^\dagger-NN^\dagger=I\)。闭合网络的参量振荡阈值由有效增益与腔损耗的谱半径决定，而非由 FIB 环长单独决定。仅测平均增益不能区分经典放大、量子压缩和高损耗补偿；需要正交层析、效率标定、暗计数和多模分解。故参量增益、压缩、四波混频和纠缠均是外加非线性光学模型的条件结论。

## 205. FIB 邻接网络上的外加成核结晶、Avrami 动力学与界面粗糙度

固定 FIB 图 \(G_j=(V_j,E_j)\)，顶点可作候选成核位置，边可作扩散或界面通道；FIB 不给晶格常数、空间嵌入、自由能、过冷度、界面张力、扩散、边界或噪声。母相与晶相的外加自由能差为 \(\Delta g>0\)，三维球核模型给
$$
\Delta G(r)=4\pi r^2\gamma-\frac43\pi r^3\Delta g,
\qquad
r_*=\frac{2\gamma}{\Delta g},
\qquad
\Delta G_*=\frac{16\pi\gamma^3}{3(\Delta g)^2}.
\tag{205.1}
$$
均匀和异质成核率可写
$$
I_{\rm hom}=I_0e^{-\Delta G_*/(k_BT)},\qquad
I_{\rm het}=I_{0,\rm het}e^{-f(\theta)\Delta G_*/(k_BT)}.
\tag{205.2}
$$
标签集合只指定候选位置，不能自动降低势垒。

晶核生长可由扩散与界面律外加为
$$
\partial_tc=D\nabla^2c,\qquad
v_n=M(\mathbf n,T)[\Delta g-\gamma(\mathbf n)\kappa]+\xi_n .
\tag{205.3}
$$
在独立 Poisson 成核、均匀各向同性生长和外加有效维数 \(d\) 下，扩展转化量与晶相比例为
$$
Y(t)=\int_0^tI(t')V_d[R(t,t')]\,{\rm d}t',
\qquad
X(t)=1-e^{-Y(t)}.
\tag{205.4}
$$
常率成核和常速生长给 \(X=1-e^{-Kt^{d+1}}\)；预置晶核则常给 \(d\) 而非 \(d+1\) 的指数。有限图边界、瓶颈、各向异性和多尺度体积增长会使有效 Avrami 指数随时间变化。只有另给图距离和体积权重，使 \(V_j(r)\sim r^{d_{\rm eff}}\)，才可把有效图维数带入该律。

若外加嵌入允许高度场 \(h(x,t)\)，界面粗糙度可写
$$
w(L,t)=\left\langle[h-\bar h_L]^2\right\rangle_L^{1/2},
\qquad
w(L,t)\sim L^\alpha f(t/L^z).
\tag{205.5}
$$
线性噪声可给 Edwards–Wilkinson 方程，斜率非线性可给 KPZ 型方程；淬火标签和杂质则可能造成钉扎与 depinning。晶粒数、取向、边界成核和粗糙度指数均取决于成核率、生长速度、界面能、噪声和观测窗口。单条 \(X(t)\) 曲线只能看到 \(I\)、\(v\)、有效维数和边界混合的积分，不能分别识别这些参数。结晶也不等同 Cahn–Hilliard 相分离：它还要求晶格取向、晶界和成核势垒。因此 Avrami 指数、晶粒分布与粗糙度标度是外加结晶模型的条件结论。

## 206. FIB 递归路径上的外加分子马达、主动输运与化学循环效率

固定 FIB 状态接续路径，另给马达状态空间 \(\mathbb Z\times\{1,\ldots,M\}\)。位置步长、构象势能、负载力、化学储库和观测坐标均外加。允许内部跃迁和位移 \(\delta\) 的主方程为
$$
\dot p_{n,i}=\sum_{j,\delta}
\left[w_{ji}^{\delta}p_{n-\delta,j}-w_{ij}^{\delta}p_{n,i}\right].
\tag{206.1}
$$
局部详细平衡可写
$$
\log\frac{w_{ij}^{\delta}}{w_{ji}^{-\delta}}
=\beta[\Delta\mu_r-(U_j-U_i)-f\delta d],
\tag{206.2}
$$
但主动驱动和非热浴需要改写该关系。周期稳态中的速度为
$$
v=d\sum_{i,j,\delta}\delta J_{ij}^{\delta},
\qquad
J_{ij}^{\delta}=w_{ij}^{\delta}\pi_i-w_{ji}^{-\delta}\pi_j .
\tag{206.3}
$$
无负载速度和失速力由 \(v(0)\) 与 \(v(f_s)=0\) 定义；多循环、漏循环和反向滑移会使失速力不等于单一化学亲和力除以步长。

机械功率、化学输入和效率为
$$
P_{\rm out}=fv,\qquad
\dot W_{\rm chem}=\sum_rJ_r\Delta\mu_r,\qquad
\eta=\frac{P_{\rm out}}{\dot W_{\rm chem}}.
\tag{206.4}
$$
等温局部详细平衡网络的熵产生满足
$$
\dot S_{\rm tot}
=\beta(\dot W_{\rm chem}-P_{\rm out})\ge0.
\tag{206.5}
$$
无负载和失速时机械功率都为零，最大效率与最大功率一般不在同一负载。位移—燃料联合路径还满足相应的熵产生涨落关系；其扩散常数、Fano 因子和异常扩散取决于障碍、门控和等待时间尾部。只测位置轨迹不能识别隐藏燃料消耗、无步耗散循环或内部构象。速度、效率、失速和涨落因此都是外加马达动力学下的条件结论。

## 207. FIB 网络上的外加生物电兴奋波、反应—扩散心电传播与随机失稳

固定 FIB 细胞连接图 \(G_j=(V_j,E_j)\)，另给边电导 \(W_j^\sigma\) 和 \(L_j^\sigma=B_j^{\mathsf T}W_j^\sigma B_j\)。顶点膜电位 \(V_v\) 与恢复变量 \(w_v\) 的外加 FitzHugh–Nagumo 模型为
$$
C_{m,v}\dot V_v=-(L_j^\sigma V)_v+f_v(V_v,w_v)+I_v^{\rm stim},
\qquad
\tau_{w,v}\dot w_v=g_v(V_v,w_v).
\tag{207.1}
$$
更详细的 Hodgkin–Huxley 门控、最大电导、反转电位和离子浓度仍需外加。网格细化并给出组织嵌入后，可趋向
$$
C_m\partial_tV=\nabla\cdot(\boldsymbol\sigma\nabla V)-I_{\rm ion}(V,y)+I^{\rm stim},
\qquad
\partial_ty=G(V,y).
\tag{207.2}
$$
仅有连接图不能定义空间梯度、波速或电缆尺度。

兴奋波的速度、前沿宽度和阈值由电导、膜电容、局部反应曲线和恢复变量决定；在特定各向同性近似下才可用
$$
c_n\simeq c_0-D_\perp\kappa
\tag{207.3}
$$
描述曲率修正。动作电位时程与舒张间隔可由
$$
D_n=T-A_n,\qquad A_{n+1}=F(D_n)
\tag{207.4}
$$
描述；固定点失稳会导致交替电位和周期倍增。再入还需非平凡组织环路、足够传导长度、恢复期和单向阻滞，树图或无恢复变量的反应—扩散模型不能自动产生持久再入。

在另加二维胞腔和复相位 \(Z(V,w)\) 后，闭环绕数可写
$$
n_C=\frac1{2\pi}\sum_{e\in C}{\rm unwrap}
\bigl(\arg Z_{h(e)}-\arg Z_{t(e)}\bigr).
\tag{207.5}
$$
非零绕数对应旋涡或转子核心；其漂移、分裂、边界钉扎和湮灭依赖各向异性、曲率、恢复时间和扰动。心电或多电极读出是外加投影
$$
y(t)=Q_jV(t)+\eta(t),
\tag{207.6}
$$
不同局部波前和相位奇点可能给出相同体表信号。通道噪声、刺激和电导随机性可触发异位动作电位、波阻滞或随机再入，也可破坏波前相干。传导速度、动作电位时程和总电压通常只能识别参数组合，不能单独恢复离子模型与隐藏恢复态。

因此 FIB 只提供细胞连接、组织图和传播路径骨架。膜电位、离子通道、兴奋阈值、传导速度、恢复期、组织几何、刺激、边界、测量投影和噪声均须外加。FitzHugh–Nagumo/电缆极限、波前、再入旋涡和随机失稳是这些结构下的条件结论；同一 FIB 图可从静息稳定态切换到单脉冲传播、波阻滞、旋涡或噪声诱发失常，不存在由 FIB ATOM 递归单独确定的普适生物电定律。

## 208. FIB 网络上的外加多组分趋化、反应—扩散斑图与聚集临界性

固定 FIB 关系给出的有限图 \(G_j=(V_j,E_j)\)，令 \(B_j\) 为关联矩阵、\(L_j=B_j^{\mathsf T}W_jB_j\) 为另行赋权的图拉普拉斯。顶点上放置 \(m\) 个种群密度 \(u=(u_1,\ldots,u_m)\) 和 \(q\) 个趋化或抑制信号 \(c=(c_1,\ldots,c_q)\)。FIB 只提供顶点、边和组合路径；体积、嵌入距离、扩散张量、趋化系数、反应网络、化学降解、边界、噪声和观测通道均外加。

对种群 \(a\)，外加守恒边通量和反应项可写成

$$
J_a=-D_aB_ju_a+\bar u_a\sum_{\ell=1}^q\chi_{a\ell}B_jc_\ell,
\qquad
\dot u_a=B_j^{\mathsf T}J_a+R_a(u,c),
\tag{208.1}
$$

信号方程为

$$
\tau_\ell\dot c_\ell
=-D^c_\ell L_jc_\ell-\alpha_\ell c_\ell
+\sum_{a=1}^m\beta_{\ell a}u_a+S_\ell.
\tag{208.2}
$$

\(\chi_{a\ell}\) 的符号分别表示吸引或排斥，\(R_a\) 可包含出生、死亡、竞争、饱和和化学反应。质量守恒只有在相应反应项和边界通量为零时成立，不能从 FIB 图结构自动推出。若 \(\tau_\ell\to0\) 且
\(K_\ell=(D^c_\ell L_j+\alpha_\ell I)^{-1}\) 存在，则
\(c_\ell=K_\ell(\sum_a\beta_{\ell a}u_a+S_\ell)\)，趋化作用成为图上的非局部交叉扩散。\(\alpha_\ell=0\) 时还需零模相容条件，\(\alpha_\ell>0\) 则给出外加屏蔽长度。

设 \((u_*,c_*)\) 是均匀稳态，令 \(L_j\varphi_{\ell,j}=\lambda_{\ell,j}\varphi_{\ell,j}\)。线性化的图模态满足

$$
\partial_tz_\ell=\mathsf A_j(\lambda_{\ell,j})z_\ell,
\qquad
\mathsf A_j(\lambda)=
\begin{pmatrix}
R_u-\lambda D_u & \lambda X\\
B_c & R_c-\lambda D_c
\end{pmatrix},
\tag{208.3}
$$

并定义

$$
s_j(\lambda)=\max\operatorname{Re}\operatorname{spec}\mathsf A_j(\lambda).
\tag{208.4}
$$

若 \(s_j(0)<0\) 而某个正特征值使 \(s_j(\lambda_{\ell,j})>0\)，均匀稳态对均匀扰动稳定而对空间扰动失稳，得到外加反应—扩散—趋化的 Turing 型斑图。最先增长的模态由

$$
\lambda_{\rm sel,j}\in\arg\max_{\lambda_{\ell,j}}s_j(\lambda_{\ell,j})
\tag{208.5}
$$

选择，其形状仍取决于边界、缺陷和特征向量。图谱只有在给定长度标度和嵌入后才可与连续波数对应；改变边权或边界会移动失稳带。

二维、单种群、无反应且信号快速无屏蔽时，外加连续极限可写

$$
\partial_tu=D\Delta u-\chi\nabla\!\cdot(u\nabla c),
\qquad
-D_c\Delta c=\beta u.
\tag{208.6}
$$

在全平面 Newton 核归一化和适当正则性下，经典临界质量为

$$
M_c=\frac{8\pi D D_c}{\chi\beta}.
\tag{208.7}
$$

这个 \(8\pi\) 只属于所列模型；屏蔽、有界域、化学反应、多个物种、非局部核和时间依赖信号都会改变或消除该分界。有限 FIB 图在固定质量和有限顶点数下没有连续 PDE 意义的有限时间无穷大，只能出现向少数顶点集中的高峰。图列体积、边权和归一化若随网格尺度改变，离散峰值是否逼近连续爆聚必须另行证明。

随机通量、信号和反应可写为

$$
\mathrm du=\mathcal F_u(u,c)\,\mathrm dt
+\Sigma_u(u,c)\,\mathrm dW_u,
\qquad
\tau\,\mathrm dc=\mathcal F_c(u,c)\,\mathrm dt
+\Sigma_c(u,c)\,\mathrm dW_c .
\tag{208.8}
$$

噪声能在确定性稳定区触发斑图成核，也能在超临界区打散聚集。若读出为

$$
y(t)=Q_u u(t)+Q_c c(t)+\eta(t),
\tag{208.9}
$$

则被 \(Q_u\) 湮灭的模态不可见，只测总质量也无法区分均匀态、条纹态和多个团簇。有限时间轨迹通常只识别 \(\chi\beta/D_c\)、屏蔽长度和反应时间等组合，不能分别恢复全部参数。

因此，FIB 递归只提供关系、图谱和路径骨架；趋化参数、化学信号、反应网络、几何尺度、边界、噪声和测量均须外加。聚集阈值、Turing—趋化斑图、模式选择、离散峰值、连续爆聚与随机切换，都是指定外加模型后的条件结论，不是 FIB ATOM 递归单独确定的普适趋化统计。

## 209. FIB 路径上的外加量子随机游走、退相干与扩散—局域化输运

固定 FIB 图 \(G_j=(V_j,E_j)\)，在顶点基 \(\{|v\rangle\}\) 上另给紧束缚 Hamiltonian

$$
H_j=\sum_vV_v|v\rangle\langle v|
-\sum_{\{u,v\}\in E_j}
\left(J_{uv}|u\rangle\langle v|+\overline{J_{uv}}|v\rangle\langle u|\right).
\tag{209.1}
$$

跃迁幅度、站点势、规范相位、距离、时间单位和边界均是外加。开放系统密度矩阵可满足

$$
\dot\rho=-{\rm i}[H_j,\rho]
+\sum_\alpha\left(L_\alpha\rho L_\alpha^\dagger
-\tfrac12\{L_\alpha^\dagger L_\alpha,\rho\}\right).
\tag{209.2}
$$

取 \(L_v=\sqrt{\gamma_v}|v\rangle\langle v|\) 表示位置退相干，取
\(L_{u\to v}=\sqrt{k_{u\to v}}|v\rangle\langle u|\) 表示有向跳跃；\(\gamma_v,k_{u\to v}\)、热浴和详细平衡关系均不由 FIB 给出。

在强而近似均匀的退相干下，绝热消去相干项可产生

$$
k_{u\to v}^{\rm eff}
\simeq\frac{2|J_{uv}|^2\gamma_\phi}
{\gamma_\phi^2+(V_u-V_v)^2},
\qquad
\dot p_v\simeq\sum_{u\sim v}
(k_{u\to v}^{\rm eff}p_u-k_{v\to u}^{\rm eff}p_v).
\tag{209.3}
$$

给定物理距离和适当图列极限后，这一主方程才可能产生 \({\rm MSD}(t)\sim2dDt\)。退相干并不单调加快输运：弱退相干可保留相干准弹道传播，强退相干又使 \(D\) 按 \(|J|^2/\gamma_\phi\) 下降，极强测量导致量子 Zeno 慢化。

若无序势外加且保持相干，一维或准一维模型可有 Anderson 局域化；有限退相干会把严格局域化改为长时间慢扩散。Liouvillian 谱隙

$$
\Delta_{\mathcal L}=-\max_{\lambda\ne0}\operatorname{Re}\lambda
\tag{209.4}
$$

只有在耗散通道、边界和稳态唯一性均明确时才给出弛豫尺度。给有向边标记位移 \(d_{uv}\)，倾斜 Liouvillian 的生成函数为

$$
Z(\chi,t)=\operatorname{tr}\!\left(e^{t\mathcal L_\chi}\rho_0\right),
\qquad
\psi(\chi)=\lim_{t\to\infty}t^{-1}\log Z(\chi,t),
\tag{209.5}
$$

其导数给出位移平均、扩散和大偏差率，但前提是测量通道和环境已纳入模型。仅记录位置均方位移不能区分相干弹道、退相干扩散和局域化平台；不同 \(H_j\)、耗散率和测量反作用可能产生同一位置边缘。

因此，FIB 递归只提供量子位置和接续关系的组合路径。Hamiltonian、跃迁幅度、势、退相干、热浴、物理距离、边界、时间尺度及测量均须外加；量子随机游走、扩散、Anderson 局域化、Zeno 慢化和输运涨落都是明确开放量子模型下的条件结论。

## 210. FIB 网络上的外加耗散粒子、自组织临界与有限尺寸幂律

固定 FIB 图族 \(G_L=(V_L,E_L)\)，在顶点放置非负粒子数 \(z_v\)，另给稳定阈值 \(c_v\)、转移核、汇点和体耗散率。一次外加稳定化可写为

$$
z^{(n+1)}=\mathsf{Stab}_{L,\varepsilon}\!\left(z^{(n)}+\xi_n\right).
\tag{210.1}
$$

FIB 只给邻接、路径和层级模板；粒子含义、阈值、驱动、耗散、几何、边界和观测规则均外加。定义 \(M_n=\sum_vz_v\)、\(I_n=\sum_v\xi_{n,v}\) 和耗散量 \(D_n\)，总有质量账式

$$
M_{n+1}-M_n=I_n-D_n.
\tag{210.2}
$$

若存在有限平稳分布，则 \(\mathbb E[D_n]=\mathbb E[I_n]\)。没有汇点和体耗散时，持续正输入不能达到有限平稳账；固定正耗散通常给出有限相关长度和截断尾。候选自组织临界极限需另加慢驱动和随 \(L\) 缩小的耗散路径。

粗粒活动密度 \(\rho_a\) 与粒子密度 \(\zeta\) 可满足

$$
\partial_t\rho_a
=a(\zeta-\zeta_c)\rho_a-b\rho_a^2
+D_a\Delta_G\rho_a+\sigma\sqrt{\rho_a}\,\eta_a,
\qquad
\partial_t\zeta=h_L-\varepsilon_L\rho_a
+D_\zeta\Delta_G\rho_a+\eta_\zeta .
\tag{210.3}
$$

若驱动期间已有活动尚未消失，雪崩重叠改变统计；若 \(h_L,\varepsilon_L\to0\) 的次序不同，也会得到不同极限。分支比

$$
R_L=\mathbb E[\text{一次活动在下一时间层产生的活动数}]
\tag{210.4}
$$

只有在近似树状且子事件近似独立时才可作为临界指标，环路、守恒和长程转移会使它不足以决定雪崩律。

雪崩规模、面积、持续时间和图距离半径可定义为

$$
S=\sum_vu_v,\qquad
A=\#\{v:u_v>0\},\qquad
T=\text{活动时间层数},\qquad
R=\max_{v:u_v>0}d_L(v,v_0).
\tag{210.5}
$$

在另给物理长度 \(L\) 和有限尺寸极限后，才可检验候选标度

$$
P_L(S=s)=s^{-\tau_s}\Phi\!\left(\frac{s}{s_c(L)}\right),
\qquad
s_c(L)\asymp L^{D_s},
\tag{210.6}
$$

以及 \(P_L(T=t)=t^{-\tau_t}\Psi(t/L^z)\)。递归深度不能直接代替物理长度；边界占比、谱维、瓶颈、方向性和图族选择都会改变截止。外加加粒若满足

$$
\Pr(I_n>x)\asymp x^{-\alpha},
\tag{210.7}
$$

即使内部动力学次临界，也能在有限窗口产生伪幂律。因此双对数直线不能单独证明 SOC 或临界分支比。

传感器映射 \(Y=Q_L(S,T,A,R)+\epsilon\) 会改变观测指数：只计受影响顶点得到 \(A\)，只计拓扑次数得到 \(S\)，粗时间采样会截短 \(T\)。淬火图族与退火图族的平均顺序也可能给出不同矩指数。故 SOC、雪崩指数、临界分支比和有限尺寸标度必须在指定驱动、耗散、拓扑核、尺度极限和观测规则下检验，不能由 FIB ATOM 递归单独推出。

## 211. FIB 递归路径上的外加更新过程、首达时间与重尾极值统计

固定一条 FIB 递归路径或有限状态接续图，记第 \(n\) 次接续所经过的状态为 \(X_n\)。FIB 只给出允许的组合关系；等待时间 \(\tau_n>0\)、奖励 \(R_n\)、外部时钟、目标集合和观测投影均需外加。令

$$
S_n=\sum_{k=1}^{n}\tau_k,\qquad
N(t)=\max\{n:S_n\le t\}.
\tag{211.1}
$$

若 \((\tau_n,R_n)\) 独立同分布且 \(\mu=\mathbb E[\tau_1]<\infty\)、\(\rho=\mathbb E[R_1]<\infty\)，更新定理给出

$$
\frac{N(t)}{t}\longrightarrow\frac1\mu,\qquad
\frac1t\sum_{n=1}^{N(t)}R_n\longrightarrow\frac{\rho}{\mu}
\quad\text{a.s.}
\tag{211.2}
$$

极限速率由等待时间和奖励律决定，不能由 FIB 路径长度或递归深度单独决定。二阶矩有限时，更新奖励的中心极限定理为

$$
\frac{\sum_{n=1}^{N(t)}R_n-(\rho/\mu)t}{\sqrt t}
\Longrightarrow
\mathcal N\!\left(0,
\frac{\operatorname{Var}(R_1-(\rho/\mu)\tau_1)}{\mu}\right).
\tag{211.3}
$$

马尔可夫调制、共享时钟或回路重访会引入协方差和遍历条件；FIB 接续关系本身不提供独立性、平稳性或协方差结构。

对 FIB 目标子集 \(A\)，首达步数和首达时间分别为

$$
H_A=\inf\{n\ge0:X_n\in A\},\qquad
T_A=S_{H_A}.
\tag{211.4}
$$

即使 \(H_A\) 的组合分布已知，\(T_A\) 仍依赖等待时间的联合律。若 \(H_A\) 与 \(\tau_n\) 相关，独立时的复合更新公式失效；吸收边界、回路和重访会改变尾部。

若外加等待时间满足

$$
\Pr(\tau_1>t)\sim c\,t^{-\alpha}L(t),
\qquad 0<\alpha<1,
\tag{211.5}
$$

其中 \(L\) 为慢变函数，则均值发散，通常不再有线性速率，更新计数呈 \(t^\alpha\) 量级并出现老化。对 \(1<\alpha<2\) 的重尾，均值有限而方差发散，高斯极限由稳定律取代。回路结构、尾指数和外加截断共同决定异常扩散、间歇性与长记忆。

对前 \(n\) 次奖励的极值 \(M_n=\max_{k\le n}R_k\)，只有在外加尾部和依赖簇满足相应条件时，才可得到 Fréchet、Gumbel 或 Weibull 型极值极限。有限 FIB 图的节点数不决定极值域；共享边、周期回路和状态门控会改变有效样本数，不能用独立观测替代。

因此，FIB 可提供更新事件的允许接续、回路和目标集合；等待时间分布、奖励律、独立性、平稳性、吸收边界、时间尺度和观测误差均须外加。更新定理、首达分布、中心或稳定极限定理、老化、异常输运与极值标度都是外加随机过程的条件结论，不存在由 FIB 递归本身确定的普适更新统计。

## 212. FIB 关系网络上的外加信息流、转移熵与响应/因果识别统计

固定 FIB 递归产生的上下文集合 \(V\) 及其关系边集 \(E\)。在每个上下文 \(v\) 上另定义随机过程 \(X_v(t)\)，并选择外加时钟、采样间隔、过滤族 \(\mathcal F_t\)、联合概率律和观测通道。FIB 只提供关系与候选路径；边的方向、时间先后、噪声独立性、干预可行性和观测精度均需外加。含环关系必须经过外加时间展开，组合相邻不能自动解释成因果箭头。

对两个离散时间过程 \(X,Y\)，有限记忆转移熵定义为

$$
T_{X\to Y}^{(\ell,m)}
=I\!\left(Y_{t+1};X_{t-\ell+1:t}\mid Y_{t-m+1:t}\right)
=\sum p(y_{t+1},x^\ell,y^m)
\log\frac{p(y_{t+1}\mid x^\ell,y^m)}
{p(y_{t+1}\mid y^m)} .
\tag{212.1}
$$

它非负且一般不对称。连续时间转移熵率若存在，可写为

$$
\mathcal T_{X\to Y}
=\lim_{\Delta t\downarrow0}
\frac1{\Delta t}
I\!\left(Y_{t+\Delta t};\mathcal F_t^X\mid\mathcal F_t^Y\right).
\tag{212.2}
$$

该极限可能发散、为零或依赖粗粒化，不能用 FIB 路径长度代替时间尺度。条件转移熵

$$
T_{u\to v\mid S}
=I\!\left(X_v(t+1);X_u^{\rm past}
\mid X_v^{\rm past},X_S^{\rm past}\right)
\tag{212.3}
$$

只有在 \(S\) 阻断已观测共同驱动且过程近似平稳时，才可解释为预测增益。隐藏变量、同步、混叠和非平稳性会使正值不等于物理因果，真实影响也可能因冗余或噪声使观测值为零。

因果响应需另给可实施的外加扰动 \(h_s\)：

$$
R_{Y\leftarrow X}(t,s)
=\left.\frac{\delta\,\mathbb E_h[Y_t]}{\delta h_s}\right|_{h=0},
\qquad t\ge s .
\tag{212.4}
$$

扰动位置、幅度极限、其余变量是否固定以及测量反作用均属于实验协议。Kubo 型相关函数还要求平衡、线性微扰、共轭力和时间反演奇偶性；非平衡或主动噪声通常含额外动力学项。

动态结构模型可写为

$$
X_v(t+1)=f_v\!\left(X_{\operatorname{pa}(v)}(\le t),U_v(t+1)\right).
\tag{212.5}
$$

父集合、噪声联合律和时间递推均为外加。对干预 \(do(X_u(s)=x)\)，因果效应为

$$
\Delta_{x,x'}^Y(t,s)
=\mathbb E[Y_t\mid do(X_u(s)=x)]
-\mathbb E[Y_t\mid do(X_u(s)=x')].
\tag{212.6}
$$

后门调整公式

$$
\mathbb P(y\mid do(x))
=\sum_z\mathbb P(y\mid x,z)\mathbb P(z)
\tag{212.7}
$$

只有在一致性、可交换性和调整集 \(Z\) 的阻断条件成立时才有效；FIB 关系边不保证这些条件。含反馈环时需时间展开或明确动态干预。

在正确指定的高斯线性模型中，转移熵等于预测残差方差的对数增益：

$$
T_{X\to Y}
=\frac12\log
\frac{\operatorname{Var}(\varepsilon_{\rm restricted})}
{\operatorname{Var}(\varepsilon_{\rm full})}.
\tag{212.8}
$$

非线性、重尾噪声、隐藏变量和正则化会破坏这一等价。观测若为 \(\widetilde X=M_X(X,\epsilon_X)\)、\(\widetilde Y=M_Y(Y,\epsilon_Y)\)，有限带宽、延迟、缺失和噪声会把潜在历史投影到观测纤维内；重复同一观测协议不能恢复未观测或未干预的方向。

同一 FIB 关系骨架可承载零转移熵、共同驱动造成的双向预测信息、有向延迟耦合造成的单向响应和反馈造成的方向分解。改变时间采样、测量带宽、干预协议或噪声模型即可改变这些统计量。因此，FIB 递归只给出关系与路径的组合载体；概率分布、时间顺序、噪声联合律、干预、响应、观测和识别条件均须外加。转移熵、响应函数、Granger 型预测增益和因果效应是这些条件明确后的结论，不是 FIB ATOM 递归单独推出的信息方向或物理因果定律。

## 213. FIB 图族上的外加随机介质、均匀化与 quenched/annealed 极限

固定一族由 FIB 关系给出的有限图 \(G_j=(V_j,E_j)\)，另行指定尺度 \(h_j\to0\)、顶点体积、边长和嵌入。边导通率 \(a_{j,e}(\omega)\)、质量密度、孔隙率和反应率组成外加随机环境 \(\omega\)。FIB 只给组合和邻接关系；尺度、度量、概率律、系综、边界、极限顺序和观测协议都不由递归关系确定。

令 \(B_j\) 为定向关联矩阵，边梯度和通量为

$$
(\nabla_j u)_e=\frac{u_{h(e)}-u_{t(e)}}{\ell_{j,e}},
\qquad
J_{j,e}^{\omega}=-a_{j,e}(\omega)(\nabla_j u)_e .
\tag{213.1}
$$

离散扩散方程可写成

$$
m_{j,v}(\omega)\dot u_{j,v}
+h_j^{-2}(B_j^{\mathsf T}A_j(\omega)B_j u_j)_v=f_{j,v}.
\tag{213.2}
$$

统一椭圆性

$$
0<a_-\le a_{j,e}(\omega)\le a_+<\infty
\tag{213.3}
$$

以及平稳遍历、共同嵌入和边界收敛等条件成立时，外加随机校正子可定义有效张量

$$
\xi^{\mathsf T}A^{\rm hom}\xi
=\inf_{\chi\ {\rm stationary}}
\mathbb E_\omega\!\left[
\sum_e a_e(\omega)
\bigl(\xi\cdot\zeta_e+\nabla\chi_e(\omega)\bigr)^2
\right].
\tag{213.4}
$$

于是固定环境的解在适当扩散时间缩放下可能趋向

$$
\partial_tu=\nabla\!\cdot(A^{\rm hom}\nabla u)+f,
\tag{213.5}
$$

但 \(A^{\rm hom}\) 通常不是边系数的算术平均；各向异性嵌入、相关无序和边界层会使它非对角或方向依赖。若开放边另带压力和渗透权重，则外加宏观极限可写为

$$
q^{\rm hom}=-K^{\rm hom}\nabla p,
\qquad
\nabla\!\cdot q^{\rm hom}=s .
\tag{213.6}
$$

低于外加渗流阈值时可能没有宏观连通簇，\(K^{\rm hom}=0\)；阈值与张量由开放边概率、权重、几何和边界共同决定。

Quenched 方案先固定 \(\omega\) 再取 \(j\to\infty\)，annealed 方案先取有限尺度平均再取极限。一般有

$$
\mathbb E_\omega[(L_j^\omega)^{-1}]
\ne
(\mathbb E_\omega[L_j^\omega])^{-1},
\tag{213.7}
$$

因此平均响应、典型样本和极端阻塞概率可以不同。长程相关、非遍历系综、重尾系数或开放簇临界会破坏通常的 \(h_j^{-2}\) 标度，产生陷阱亚扩散、时间分数阶极限或非高斯涨落。只测总流量和平均梯度通常只能识别 \(A^{\rm hom}\) 的少数投影，不能恢复边系数分布、相关长度和校正子。

因此，FIB 递归只提供可承载随机导通、扩散和渗透的组合骨架；有效张量、均匀化极限、quenched/annealed 是否相同以及异常输运，都是外加概率律、尺度、嵌入、边界和观测条件下的结论。

## 214. FIB 网络上的外加 Ising/Potts 自旋、Gibbs 测度与有限尺寸相变

固定 FIB 图 \(G_j=(V_j,E_j)\)，另给自旋状态、边耦合、外场、温度、边界和图序列。Ising Hamiltonian 可写成

$$
H_{\rm I}(\sigma)
=-\sum_{\{u,v\}\in E_j}J_{uv}\sigma_u\sigma_v
-\sum_{v\in V_j}h_v\sigma_v,
\qquad \sigma_v\in\{-1,+1\},
\tag{214.1}
$$

Potts 模型则可用

$$
H_{\rm P}(\sigma)
=-\sum_{\{u,v\}\in E_j}J_{uv}
\mathbf1_{\{\sigma_u=\sigma_v\}} .
\tag{214.2}
$$

给定边界 \(\xi\)，有限图 Gibbs 测度为

$$
\mu_{j,\beta,\xi}(\sigma)
=\frac{e^{-\beta H(\sigma)}}{Z_{j,\beta,\xi}},
\qquad
Z_{j,\beta,\xi}=\sum_{\sigma}e^{-\beta H(\sigma)} .
\tag{214.3}
$$

有限图自由能通常解析；严格相变只能在外加图序列 \(|V_j|\to\infty\) 的极限中由自由能非解析或 Gibbs 测度不唯一性定义。磁化、易感率和热容可写为

$$
m_j=\frac1{|V_j|}\sum_v\sigma_v,
\qquad
\chi_j=\beta |V_j|\operatorname{Var}(m_j),
\qquad
C_j=\frac{\beta^2}{|V_j|}\operatorname{Var}(H).
\tag{214.4}
$$

给定外加图距离 \(d_j\)，关联长度依赖

$$
C_j(u,v)=
\langle\sigma_u\sigma_v\rangle-
\langle\sigma_u\rangle\langle\sigma_v\rangle,
\qquad
\xi_j^{-1}=-\limsup_{r\to\infty}
\frac1r\log\sup_{d_j(u,v)\ge r}|C_j(u,v)|.
\tag{214.5}
$$

临界温度、相的数目和关联衰减取决于图几何、耦合、边界和随机系综。若另给外加线性尺度 \(L_j\) 和相关长度指数 \(\nu\)，有限尺寸标度可写

$$
\langle|m_j|\rangle\simeq L_j^{-\beta_{\rm ord}/\nu}
F_m(tL_j^{1/\nu}),
\qquad
\chi_j\simeq L_j^{\gamma/\nu}F_\chi(tL_j^{1/\nu}),
\tag{214.6}
$$

其中 \(t\) 是约化温度。Binder 比交叉和易感率峰值只能给伪临界位置；边界层、尺寸修正和未热化会造成漂移。

若耦合随机，quenched 自由能与 annealed 自由能分别涉及
\(\mathbb E[\log Z]\) 和 \(\log\mathbb E[Z]\)，两者一般不相等。竞争耦合、随机场和长程相关可产生挫折、Griffiths 区域或非自平均涨落。若另加 Glauber 或 Metropolis 动力学，弛豫时间还依赖更新规则、守恒量和噪声，静态 Gibbs 测度不能决定动态指数。有限窗口中的磁化和两点相关不能唯一恢复所有耦合、边界和温度。

因此，FIB 只提供邻接与层级骨架；自旋、Hamiltonian、耦合、逆温度、Gibbs 边界、随机系综、动力学和热力学极限均须外加。相变、关联长度和有限尺寸指数是这些条件明确后的模型结论，不是 FIB 递归单独推出的自旋定律。

## 215. FIB 图族上的外加渗流、连通阈值与有效输运标度

固定 FIB 图族 \(G_L=(V_L,E_L)\)，对每条边外加开闭变量 \(\omega_e\)，其联合分布为 \(\mathbb P_{L,\theta}\)。FIB 只给邻接、路径和层级模板；开闭概率、相关强度、边长、几何嵌入、权重、边界、驱动和观测均需另给。开簇定义为

$$
\mathcal C_L(v;\omega)
=\{u:\text{存在全由 }\omega_e=1\text{ 的路径从 }v\text{ 到 }u\}.
\tag{215.1}
$$

在外加无限图列中，连通阈值可定义为

$$
\theta_c=\inf\{\theta:
\mathbb P_\theta(|\mathcal C(o;\omega)|=\infty)>0\}.
\tag{215.2}
$$

有限图只有跨越概率 \(\Pi_L(\theta)\) 和最大簇占比；有限尺寸伪阈值是否收敛到 \(\theta_c\) 取决于图列、边界和相关长度。给开边再赋导通权重 \(g_e>0\)，有效导电率由

$$
G_{\rm eff}(L,\omega)
=\min_{\phi|_{A_L}=1,\ \phi|_{B_L}=0}
\sum_{(u,v)\in E_L}\omega_{uv}g_{uv}(\phi_u-\phi_v)^2
\tag{215.3}
$$

定义。几何连通不保证正导电率：窄瓶颈或重尾小权重仍可使 \(G_{\rm eff}=0\)。

在外加各向同性图列和权重条件下，可提出

$$
\mathbb E[G_{\rm eff}(L,\theta)]
\asymp(\theta-\theta_c)^t,
\qquad
G_{\rm eff}(L,\theta)
=L^{-y_G}\mathcal G((\theta-\theta_c)L^{1/\nu}),
\tag{215.4}
$$

但 \(t,\nu,y_G\) 依赖图维数、长程相关、度分布、边界和电势归一化；一般层级图不能直接套用欧氏 \(d-2\)。簇分布的候选标度为

$$
P_L(s;\theta)
=s^{-\tau}\mathcal F_s(sL^{-D_s},(\theta-\theta_c)L^{1/\nu}).
\tag{215.5}
$$

曲线交叉、双对数直线和矩指数都可能被有限样本、重尾权重、多个截止和边界层伪造。若把开放边和压力差解释为孔隙介质，还需另给面积、长度和法向，才能定义 Darcy 渗透率；“存在一条 FIB 路径”不等于存在宏观电流或流体通量。

观测下采样、阈值截断和只记录最大簇会改变可见指数；退火图平均和固定样本的 quenched 平均也可能不同。同一 FIB 骨架配上独立、相关、定向或重尾开边，可以拥有不同连通阈值、输运阈值、有效张量和异常扩散。因此，FIB 只提供渗流模型的邻接载体，连通跃迁、导电率和有限尺寸标度均是外加概率律、权重、几何、边界和极限下的条件结论。


## 216. FIB 网络上的外加断裂、损伤演化与裂纹雪崩统计

固定 FIB 图 \(G_j=(V_j,E_j)\)，可把顶点解释为外加有限元自由度，把边解释为候选承载键；但几何嵌入、面积、长度、弹性模量、泊松比、断裂能、初始缺陷、加载历史和边界均需另给。线性弹性离散能量可写为

$$
\mathcal E_j(u)=\frac12u^{\mathsf T}K_j u-f^{\mathsf T}u,
\qquad
K_j=B_j^{\mathsf T}W_jB_j+K_j^{\rm bc},
\tag{216.1}
$$

其中 \(W_j\) 和边界刚度是外加。若边损伤变量为 \(d_e\in[0,1]\)，一种准静态模型为

$$
K_j(d)=B_j^{\mathsf T}
\operatorname{diag}\!\bigl((1-d_e)w_e\bigr)B_j+K_j^{\rm bc},
\qquad
d_e\ \text{在}\ \mathcal Y_e\ge\mathcal Y_{e,c}\ \text{时增长}.
\tag{216.2}
$$

能量释放率 \(\mathcal Y_e\)、阈值 \(\mathcal Y_{e,c}\)、损伤软化律和加载控制不由 FIB 接续关系确定。若连续嵌入允许裂纹尖端，则还需外加应力强度因子 \(K_I,K_{II}\)、能量释放率 \(G\) 与断裂能 \(G_c\)；Griffith 型准则 \(G\ge G_c\) 只在这些几何和本构假设成立时适用。

在随机强度或阈值下，可令边失效时间为

$$
\tau_e=\inf\{t:\mathcal Y_e(t)\ge Y_e\},
\tag{216.3}
$$

其中 \(Y_e\) 的联合分布、空间相关、加载速率和边失效后的重分配规则均外加。独立阈值并不意味着独立失效：弹性重分配会制造条件相关；共享节点、长程约束和边界会改变失效簇。单次裂纹长度或总失效数不能区分阈值重尾、应力集中和加载历史三种来源。

准静态突发事件可用破坏边数 \(S\)、持续时间 \(T\) 和破坏半径 \(R\) 描述。若另给物理长度 \(L\) 和图族极限，才可检验

$$
P_L(S=s)=s^{-\tau_s}\Phi_s(s/L^{D_s}),
\qquad
P_L(T=t)=t^{-\tau_t}\Phi_t(t/L^z).
\tag{216.4}
$$

固定加载速率会使多个突发事件重叠；黏弹性、惯性和速率相关断裂会改变持续时间尾部。边界耗散、缺陷相关和有限过程区可能产生指数截止或多重标度，不能把一次双对数直线视作普适断裂指数。

若裂纹前沿可由外加高度场 \(h(x,t)\) 描述，其粗糙度可写

$$
w(\ell,t)=
\left\langle [h-\bar h_\ell]^2\right\rangle_\ell^{1/2}
\sim \ell^\zeta F(t/\ell^z).
\tag{216.5}
$$

\(\zeta,z\) 取决于弹性核、无序相关、驱动方式和观测方向；FIB 图的组合距离只有在给定嵌入和尺度后才能代替 \(\ell\)。同一图可在脆性准静态、黏弹性延迟或疲劳循环外加模型下呈现单裂纹、分叉裂纹、慢裂纹和重复损伤。

观测若为 \(y(t)=Q_j u(t)+\eta(t)\)，有限电极、位移采样和声发射阈值会把多个损伤场投影到同一读出。总柔度可约束 \(K_j(d)\) 的组合，却通常不能恢复每条边的损伤；裂纹图像又可能漏掉内部断裂。要区分阈值分布、应力重分配和速率效应，需联合载荷—位移、空间裂纹、声发射时间与重复试验，并固定删失规则。

因此，FIB 只提供候选连接和损伤传播的组合骨架。几何、本构、断裂能、阈值、加载、惯性、黏性、边界、无序和观测均须外加；Griffith 失效、裂纹分叉、粗糙度标度和断裂雪崩是这些外加模型下的条件统计，不是 FIB ATOM 递归单独推出的普适断裂定律。

## 217. FIB 网络上的外加黏弹性、聚合物松弛谱与时间—温度标度

固定 FIB 连接图 \(G_j=(V_j,E_j)\)，另把顶点和边嵌入为交联点、链段或承载路径。FIB 只给连接与路径骨架；空间位置、链长、构象、交联密度、模量、摩擦阻尼、温度、边界夹持和应力观测均需外加。线性因果响应的本构关系为

$$
\sigma(t)=\int_{-\infty}^{t}G(t-s)\dot\gamma(s)\,\mathrm ds,
\tag{217.1}
$$

在同一线性时间平移协议下，松弛模量 \(G\) 与蠕变柔量 \(J\) 满足拉普拉斯域互补关系

$$
\widetilde G(s)\widetilde J(s)=s^{-2}.
\tag{217.2}
$$

广义 Maxwell 模型给出

$$
G(t)=G_\infty+\sum_aG_a e^{-t/\tau_a},
\qquad G_a\ge0,\quad \tau_a>0,
\tag{217.3}
$$

而连续松弛谱可写成

$$
G(t)=G_\infty+\int_0^\infty H(\tau)e^{-t/\tau}\,\mathrm d\ln\tau .
\tag{217.4}
$$

有限 FIB 网络只有有限个非零模态；连续谱需要另取网络大小、链长分布和时间窗极限，不能把递归层数直接当成松弛时间。

若边伸长为 \(x_e\)，外加弹性能和过阻尼动力学可写

$$
U(x)=\frac12\sum_{e\in E_j}k_ex_e^2,
\qquad
\Gamma_j\dot x=-\nabla U(x)+B_j^{\mathsf T}f(t).
\tag{217.5}
$$

在可对角化的简化情形，第 \(a\) 个模态的松弛时间为 \(\tau_a=\zeta_a/\lambda_a\)，其中刚度本征值 \(\lambda_a\) 和模态阻尼 \(\zeta_a\) 均为外加。零模、交联、夹持和摩擦决定材料显示流动、刚体运动还是固体平台。

正弦加载下复模量为

$$
G^*(\omega)=G'(\omega)+\mathrm iG''(\omega)
=G_\infty+\sum_aG_a
\frac{\mathrm i\omega\tau_a}{1+\mathrm i\omega\tau_a}.
\tag{217.6}
$$

单一频率只观测松弛谱的组合；蠕变、阶跃松弛和多频率联合测量才可缩小 \(H(\tau)\) 的等价类。平衡、共轭微扰和热浴已明确时，涨落—耗散关系可联系应力自相关与 \(G(t)-G_\infty\)；主动聚合物、非平衡驱动或温度梯度下还需额外耗散项。

若材料满足时间—温度叠加，可用外加移动因子 \(a_T\) 写

$$
G(t,T)\simeq G(t/a_T,T_{\rm ref}),
\qquad
G^*(\omega,T)\simeq G^*(a_T\omega,T_{\rm ref}).
\tag{217.7}
$$

WLF 或 Arrhenius 形式只在相应温区和机制下成立；跨越玻璃化、结晶、反应或多机制松弛时，单一 \(a_T\) 会失效。观测中的边界滑移、传感器柔顺度和有限频段还会把装置响应混入材料响应。

因此，FIB 递归只提供连接与路径的组合载体；弹簧、链段、阻尼、交联寿命、热浴、温度、边界和观测时间窗均须外加。蠕变、松弛谱、储能/损耗模量和时间—温度标度是在这些条件明确后的模型结论，不是 FIB ATOM 递归单独推出的普适黏弹性定律。

## 218. FIB 图网络上的外加拓扑能带、Chern 边缘态与无序输运

固定 FIB 图族 \(G_j=(V_j,E_j)\)，在每个顶点附加轨道或内部自由度。FIB 只规定允许的邻接耦合；轨道维数、空间嵌入、跃迁振幅、复相位、磁通、对称性、边界和观测均需外加。紧束缚 Hamiltonian 可写为

$$
(H_j\psi)_{v,a}
=\varepsilon_{v,a}\psi_{v,a}
+\sum_{(v,w)\in E_j,b}
t_{va,wb}e^{{\rm i}A_{va,wb}}\psi_{w,b},
\qquad H_j=H_j^\dagger .
\tag{218.1}
$$

若另给周期嵌入和平移群，Bloch 本征方程为
\(H_j(k)u_{n,j}(k)=E_{n,j}(k)u_{n,j}(k)\)。具有完整谱隙的二维占据子空间才可定义

$$
C=\frac{{\rm i}}{2\pi}
\int_{\rm BZ}\operatorname{Tr}
\bigl(P[\partial_{k_x}P,\partial_{k_y}P]\bigr)\,{\rm d}^2k .
\tag{218.2}
$$

整数性要求闭合 Brillouin 环面、光滑投影和谱隙；FIB 环路本身不提供动量空间、磁通或 Berry 投影。时间反演或镜面对称可能迫使 \(C=0\)，复跃迁和外加磁通才可能允许非零 Chern 数。

将周期图截断为边界并保留平行方向动量时，在体隙和边界局域化条件下，净边缘谱流满足

$$
N_{\rm right}-N_{\rm left}=C .
\tag{218.3}
$$

有限图中的孤立边界峰若无体隙、局域化和方向检验，不能单独认证拓扑边态。无序样本可通过扭转边界或实空间投影定义拓扑标记；位置算子、mobility gap 和单位体积迹仍需外加。平均电导可能是非整数平滑曲线，不能把系综平均替代单一样本整数拓扑数。

在线性响应和相容填充下，理想横向电导可写
\(\sigma_{xy}=(q^2/h)C\)，但接触电阻、边界散射、并联非拓扑通道和有限频率吸收会改变实际读数。沿外加参数路径只有在体隙或 mobility gap 闭合时，Chern 数才可能跃迁。相同 FIB 邻接可通过改变复相位、质量项、边界或无序实现平凡绝缘态、Chern 相或局域化拓扑相。

因此，FIB 递归只给组合邻接和环路骨架；Hamiltonian、轨道、嵌入、对称性、无序、占据、边界和测量均须外加。Berry 曲率、Chern 数、边缘谱流和量子化输运是这些条件下的模型结论，不是 FIB ATOM 递归单独推出的普适拓扑定律。

## 219. FIB 网络上的外加主动粒子、群体迁移与 MIPS 统计

固定 FIB 图 \(G_j\)，另把顶点和边嵌入为主动粒子的可达位置和通道。推进速度、朝向、转向噪声、排斥势、密度依赖、边界驱动和观测协议均需外加。连续嵌入中的主动布朗粒子可写

$$
\dot{\boldsymbol r}_i
=v(\rho_i)\boldsymbol p_i-\mu\nabla_iU
+\sqrt{2D_t}\boldsymbol\eta_i,
\qquad
\dot\theta_i=\sqrt{2D_r}\xi_i+\tau_i .
\tag{219.1}
$$

网络占据数 \(n_v\) 与边流 \(q_e\) 还满足

$$
\dot n_v=-\sum_e(B_j)_{ve}q_e+s_v .
\tag{219.2}
$$

相同 FIB 邻接在不同跃迁率、容量和边界下可呈均匀流、瓶颈堆积、环流或局部凝聚。各向同性主动粒子的粗粒密度和极化场可满足

$$
\partial_t\rho=-\nabla\!\cdot(v(\rho)\boldsymbol p)+D_t\nabla^2\rho,
\qquad
\partial_t\boldsymbol p=-D_r\boldsymbol p-\frac1d\nabla(v\rho)
+D_p\nabla^2\boldsymbol p+\cdots .
\tag{219.3}
$$

在极化快弛豫近似下，有效扩散系数为

$$
D_{\rm eff}(\rho)
=D_t+\frac{v(\rho)}{dD_r}\bigl(v(\rho)+\rho v'(\rho)\bigr).
\tag{219.4}
$$

\(D_{\rm eff}<0\) 只表示均匀态长波失稳；要得到有界相分离，还需外加梯度正则化、有限界面宽度或非平衡闭合。速度随密度下降可产生 MIPS 候选条件，但临界密度、相边界和是否存在共同自由能取决于碰撞、转动噪声、粒径、障碍和边界。

若另加极性对齐，Toner–Tu 型场还含对流、自发极化、压力和噪声项；极性集群、MIPS、瓶颈堆积和外场聚集可以共存或互相抑制。有限图上的团簇大小、密度方差、平均极性和边流需要分别测量；只观测密度无法识别隐藏朝向或化学驱动。主动 Pe 数、长度尺度和有限尺寸标度也必须外加。

因此，FIB 递归只给路径和邻接的组合载体。推进力、相互作用、转向噪声、密度反馈、极性对齐、嵌入、边界和观测均须外加；主动输运、MIPS、群体迁移和异常涨落是在这些条件下的模型结论。

## 220. FIB 图族上的外加颗粒拥挤、jamming 转变与接触力链统计

固定 FIB 图族 \(G_L\)，把顶点暂作颗粒、边暂作候选接触只是组合映射。实际位置 \(x_i\)、粒径 \(d_i\)、接触法向、刚度、摩擦、阻尼、边界和压实协议均需外加。候选边的间隙和接触集为

$$
\delta_e=d_i+d_j-|x_i-x_j|,
\qquad
E_c=\{e:\delta_e>0\}.
\tag{220.1}
$$

软颗粒接触律可取

$$
f_e^n=k_{n,e}\delta_e^{\alpha_e},
\qquad
|f_e^t|\le\mu_e f_e^n,
\tag{220.2}
$$

而无热力平衡还需满足节点力矩平衡。FIB 邻接不是实际接触；接触集合会随位置和边界改变，甚至可能排除图中没有候选边的几何接触。

令体积分数为 \(\phi\)，剔除不承载的 rattler 后配位数为

$$
z_L=\frac{2|E_c|}{N_L}.
\tag{220.3}
$$

机械刚性还要求约束矩阵足够满秩、体模量或剪切模量为正。无摩擦一般位置颗粒的等静配位候选 \(z_c=2d\) 依赖外加欧氏维数；含摩擦、转动和完全动员切向约束时计数改变，不能把 FIB 平均度当成 \(z_c\)。

若存在外加 jamming 点 \(\phi_J\)，可提出

$$
P\asymp(\phi-\phi_J)^{\Delta_P},
\qquad
z_L-z_c\asymp(\phi-\phi_J)^{\Delta_z},
\qquad
G\asymp(\phi-\phi_J)^{\Delta_G},
\tag{220.4}
$$

其中压力 \(P\)、剪切模量 \(G\) 和指数均依赖势能、摩擦、无序、加载路径和边界。jamming 的机械刚性不等于玻璃的结构松弛；后者还要由外加自中间散射函数、四点易感性和等待时间标度定义。

给接触支撑向量 \(\ell_e\)，离散应力和 fabric 张量可写

$$
\sigma_L=\frac1{V_L}\sum_{e\in E_c}\ell_e\otimes f_e,
\qquad
F_L=\frac1{|E_c|}\sum_{e\in E_c}n_e\otimes n_e .
\tag{220.5}
$$

强力子图还需外加阈值 \(q\)，取 \(E_{>q}=\{e:f_e^n>q\langle f^n\rangle\}\)。其连通性、方向和长度随摩擦、边界、加载和成像分辨率改变；大接触簇不保证承载，少量定向强边却可能承担主要应力。有限尺寸曲线交叉、力链尾部和松弛时间都不能脱离粒径、边界和压实历史解释。

因此，FIB 只提供候选接触的邻接骨架。粒径、接触律、摩擦、压实、驱动、热噪声、边界、应力单位和观测阈值均须外加；机械 jamming、玻璃松弛、力链和有限尺寸指数是指定颗粒模型后的条件统计。

## 221. FIB 网络上的外加相位振子、同步跃迁与集体频率统计

固定 FIB 图 \(G_j\)，在顶点放置相位 \(\theta_v\) 和本征频率 \(\omega_v\)。FIB 只给连接和候选耦合路径；相位方程、耦合、频率分布、延迟、噪声、边界和观测均外加。Kuramoto 型网络为

$$
\dot\theta_v
=\omega_v+K\sum_uA_{vu}\sin(\theta_u-\theta_v)
+\sqrt{2D_v}\eta_v(t).
\tag{221.1}
$$

全局序参量为

$$
R_je^{{\rm i}\Psi_j}
=\frac1{|V_j|}\sum_{v\in V_j}e^{{\rm i}\theta_v}.
\tag{221.2}
$$

同步阈值取决于拉普拉斯谱、频率分布、度异质性、频率—度相关和噪声；全局耦合下的平均场临界公式不能直接套到局部或层级图。相位延迟、定向边和传播时间可产生旋转波、簇同步和 chimera，延迟时间不由 FIB 路径长度自动给出。

密度或资源反馈会把同步与输运耦合，造成间歇锁相、相位滑移和随机去同步。有限图上应同时记录序参量、锁相簇、频率方差和去同步时间；扫参方向、初态和等待时间会产生迟滞。只测一个宏观通道，无法区分耦合增强、频率变窄、噪声降低和观测权重改变。

因此，FIB 递归只提供振子连接与路径骨架。频率、相位动力学、耦合、延迟、噪声、资源反馈、边界和测量均须外加；同步阈值、相位波、簇统计和去同步涨落是这些条件下的模型结论。

## 222. FIB 网络上的外加化学反应网络、质量作用律、随机主方程与熵产生

固定 FIB 的顶点—接续骨架，另行指定物种、反应通道和控制体体积。反应通道 \(r\) 的输入、输出计量为 \(\nu_r^-\)、\(\nu_r^+\)，净计量为 \(\nu_r\)。FIB 只提供对象可能相连或接续；计量、级数、速率常数、体积、温度、热浴、化学势和观测均外加。浓度尺度下的质量作用律为

$$
\dot x=\mathsf S v(x),
\qquad
v_r(x)=k_r\prod_sx_s^{\nu_{r,s}^-},
\qquad
\mathsf S_{sr}=\nu_{r,s}.
\tag{222.1}
$$

线性守恒量满足 \(\ell^{\mathsf T}\mathsf S=0\)，但守恒向量由外加计量决定；平衡、周期、双稳态和 Hopf 分岔由 \(\mathsf S\)、速率和储库共同决定。有限分子数的随机主方程为

$$
\frac{{\rm d}P(n,t)}{{\rm d}t}
=\sum_r\left[
a_r^\Omega(n-\nu_r)P(n-\nu_r,t)
-a_r^\Omega(n)P(n,t)\right],
\tag{222.2}
$$

其中倾向率、体积缩放和离散吸收态均需外加。空间化 FIB 网络还要把顶点反应、边转移、源汇和边界储库一并列入通道；相同 FIB 图可承载完全不同的反应—扩散系统。

若可逆反应与共同热浴满足局部详细平衡，宏观亲和力和熵产生可写

$$
\mathcal A_r=k_BT\log\frac{v_r^+}{v_r^-},
\qquad
\dot S_{\rm tot}
=\sum_r\frac{(v_r^+-v_r^-)\mathcal A_r}{T}\ge0.
\tag{222.3}
$$

开放泵浦或化学储库会产生循环流和持续耗散；只从浓度轨迹计算的熵不一定是物理总熵。复杂平衡可能给出乘积泊松稳态，但是否成立要由速率和计量检验，FIB 接续不保证。

随机反应的稀有路径可用外加跃迁 Hamiltonian

$$
\mathcal H(x,p)
=\sum_r a_r(x)\bigl(e^{p\cdot\nu_r}-1\bigr),
\qquad
\mathcal L(x,\dot x)=\sup_p[p\cdot\dot x-\mathcal H(x,p)]
\tag{222.4}
$$

描述；体积 \(\Omega\) 下路径概率的指数尺度由 \(\Omega\int\mathcal L\,{\rm d}t\) 给出。双稳态间的跃迁时间、计数流和涨落关系依赖初始分布、反向路径、热浴和驱动协议；重尾等待或非 Markov 记忆会改变该形式。

观测若为 \(y(t)=Qn(t)+\eta(t)\)，隐藏物种、守恒类和循环流可被投影掉。不同计量、速率和体积可能产生相同有限时间浓度轨迹；未观测到跳跃不能证明稀有路径不存在。要辨识熵产生和大偏差作用量，需同时记录正逆事件、温度、驱动功和共同观测窗口。

因此，FIB 递归只给反应接续、关系和可选空间骨架；反应计量、速率、体积、化学势、热浴、边界、噪声、驱动和观测均须外加。质量作用 ODE、化学主方程、熵产生、稀有事件作用量和稳态跃迁率，都是这些条件下的模型结论，不是 FIB ATOM 递归单独确定的普适化学统计定律。
