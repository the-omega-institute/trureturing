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

**推论 19.3（加权反向场的时间非齐次扩散）。** 令

$$
Y_v(s)=X_v(1-s),\qquad w(s)=v(1-s).
$$

若 $v\in C^1([0,1])$，则在同一辅助布朗表示下

$$
dY_v(s)
=
\left(\frac{w'(s)}{w(s)}Y_v(s)+\frac{w(s)}D\right)ds
+\sqrt{\frac{2w(s)Y_v(s)}D}\,dW(s).
$$

因此只有 $v$ 为常数时，加权场本身才保持第 18 节的齐次平方贝塞尔 Markov 律；一般连续 $v$ 只保留加权随机测度与有限维分布结论。

**推论 19.4（速度权重的可识别性边界）。** 若 $D$ 与全空间单点均值 $m_v(u)=\mathbb E X_v(u)$ 已知，则对 $u<1$

$$
v(u)=\frac{m_v(u)}{\kappa(u)},
$$

并由连续性确定端点。等价地，给出所有起点的平均通过时间向量时，$-D m_v''=v$、$m_v'(0)=0$、$m_v(1)=0$ 可恢复速度密度。单一起点均值、总速度质量或有限个测试函数均值只给有限个线性约束，不能识别一般连续 $v$；第 14.3 节的平滑速度例子已经给出同均值而不同二阶律的具体边界。

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
=\frac{p\pi^2(2m+1)^2}{4L_j^2}
+O\!\left(\frac{(m+1)^4}{L_j^4}\right),
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

先固定低频截断 $M$，再令 $j\to\infty$。对 $m\le M$ 使用上述逐模态极限；对 $m>M$，当 $p<1/2$ 时高频本征值的绝对值在扩散时标上指数衰减。当 $p=1/2$ 时，靠近 $-\!1$ 的模态仍可能阻止全空间算子范数收敛，但其在生存函数上的投影系数为 $O(L_j^{-1})$，起点 $0$ 更为 $O(L_j^{-3})$；把这些模态与其余高频项分开后，固定 $t>0$ 的标量尾余项仍趋于零。于是先取 $M\to\infty$ 即得所列级数。首模态与其余模态的指数率严格分离，给出长时间渐近式。$\square$

本节的谱尾律需要固定 $p>0$、$\delta>0$、等阻抗、左反射右吸收和初始律收敛；$p=0$ 时不发生该吸收扩散缩放，$p>1/2$ 时转移核不满足本定义。谱式中的高频系数可带符号，不能把每一项解释为独立概率或几何变量和。递归只提供 $W_j$、$L_j$ 与 $N_j/L_j$ 的比例；阻抗、跳率、时钟、边界和初始律仍是外加动力学。该结论不推出物理热流、量子输运、路径空间收敛或一般速度权重下的同一谱律。

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

## 223. FIB 网络上的外加传染病传播、SIS/SIR 阈值与网络免疫

固定 FIB 接触骨架 \(G_j\)，顶点可表示个体、家庭或人口分区，边表示允许接触；人口、接触持续时间、感染率、恢复率、潜伏期、免疫、时间单位、随机事件和观测均需外加。确定性 SIS 模型为

$$
\dot i_v=(1-i_v)\sum_w\beta_{vw}A_{vw}i_w-\gamma_vi_v,
\tag{223.1}
$$

SIR 模型则加入 \(s_v,r_v\) 及相应的守恒方程。疾病自由平衡附近的增长矩阵为

$$
\dot i=(B_j-\Gamma_j)i,
\qquad
(B_j)_{vw}=\beta_{vw}A_{vw},
\qquad
\mathcal R_{0,j}=\rho(\Gamma_j^{-1}B_j).
\tag{223.2}
$$

在正矩阵和线性近似成立时，谱半径大于一表示增长模态；它依赖加权接触、人口归一化、疾病时程和时间窗，不能由 FIB 度数给出。早期 SIR 只有在树状性、独立传播和外加恢复律成立时才可近似多类型分支过程；回路、时变接触和行为反馈会破坏静态渗流对应。

有限 SIS 链没有持续输入时以全易感态为吸收态，地方病统计应解释为准平稳分布或另加外部输入。SIR 最终规模在有限图上可同时含小暴发和大暴发峰，峰权重取决于初始种子、回路和随机传播系综。网络免疫可把下一代矩阵改为

$$
K_j(q)=\Gamma_j^{-1}B_j\operatorname{diag}(q),
\qquad
\mathcal R_{0,j}(q)=\rho(K_j(q)).
\tag{223.3}
$$

免疫成本、报告漏报、潜伏期和干预延迟都是外加；只测总病例不能恢复接触矩阵和传播模态。因此，FIB 只提供接触关系，传播阈值、灭绝、准平稳律和免疫优化都是外加流行病模型的条件结论。

## 224. FIB 图上的外加随机矩阵、谱统计与局域化

固定 FIB 稀疏支撑图 \(G_j\)，定义自伴随机矩阵

$$
H_j=\sum_vV_v|v\rangle\langle v|
+\sum_{\{u,v\}\in E_j}
\bigl(t_{uv}|u\rangle\langle v|+t_{uv}^*|v\rangle\langle u|\bigr).
\tag{224.1}
$$

FIB 只决定允许的非零位置；系数分布、实/复/辛对称类、相关性、归一化、边界和极限均外加。经验谱测度

$$
\mu_j=\frac1{|V_j|}\sum_a\delta_{\lambda_a}
\tag{224.2}
$$

只有在声明图列和尺度后才可能收敛到半圆、Kesten–McKay 或其他极限。强混合系综可给 Wigner–Dyson 小间距排斥 \(P(s)\sim s^\beta\)，局域化或近独立团簇可给 Poisson 统计 \(P(s)=e^{-s}\)；单个 FIB 层的间距直方图不能证明任何普适类。

本征向量局域化可用

$$
{\rm IPR}(\psi_a)=\sum_v|\psi_a(v)|^4
\tag{224.3}
$$

随图列大小的缩放判定；迁移边、Thouless 能标和边界低秩扰动都需外加。若系数尾部和谱边缘满足 Wigner 条件，最大本征值可能有 Tracy–Widom 极限；重尾对角势、高度数离群或低秩信号则可进入其他极值域并产生 outlier。不同系数赋值可共享平均谱密度而具有不同局域化、间距和谱边缘，因此 FIB 支撑不决定随机矩阵统计。

## 225. FIB 通道网络上的外加流体力学、Poiseuille 输运与湍流转捩

固定 FIB 通道图，边只表示候选通道邻接；长度、截面、粗糙度、密度、黏度、压差、边界和节点损失均须外加。连续通道内的不可压 Navier–Stokes 方程为

$$
\rho(\partial_tu+u\cdot\nabla u)
=-\nabla p+\mu\Delta u+f,
\qquad
\nabla\cdot u=0.
\tag{225.1}
$$

充分发展层流的圆管近似给出

$$
Q_e=-\frac{\pi r_e^4}{8\mu_e\ell_e}(p_v-p_u),
\qquad
\sum_eB_{ve}Q_e=s_v.
\tag{225.2}
$$

通道水力直径和平均速度才定义

$$
{\rm Re}_e=\frac{\rho_eU_eD_{h,e}}{\mu_e};
\tag{225.3}
$$

FIB 递归层级不产生 Reynolds 数。非圆截面、节点收缩和惯性需要外加阻力与局部损失；高 Reynolds 数下 Reynolds 应力、边界层、分离和湍流闭合均依赖几何、扰动和采样协议。网络的有效压降律可呈线性 Darcy、非线性 Forchheimer 或局部转捩，存在组合路径也不保证正宏观流量。只观测总流量不能辨识内部速度、回流和耗散，因此 Poiseuille、转捩和湍流统计都是外加流体模型下的条件结论。


## 226. FIB 网络上的外加种群竞争、捕食—被捕食与灭绝统计

固定 FIB 图 \(G_j=(V_j,E_j)\)，在顶点放置种群密度 \(N_{v,a}\)，边表示可外加迁移或接触通道。FIB 只给接续关系；出生率、死亡率、竞争矩阵、捕食响应、迁移系数、环境容量、季节驱动、噪声和观测均须外加。空间化 Lotka–Volterra 型模型可写成

$$
\dot N_{v,a}
=N_{v,a}\!\left(r_{v,a}
-\sum_b C_{v,ab}N_{v,b}
+\sum_b P_{v,ab}(N_v)\right)
+\sum_{u}M_{uv,a}(N_{u,a}-N_{v,a}).
\tag{226.1}
$$

矩阵 \(C\)、捕食函数 \(P\) 和迁移 \(M\) 决定平衡、周期、混沌或灭绝；图度数不能自动给出生存条件。在线性化平衡 \(N_*\) 附近，图拉普拉斯模态的增长率来自反应 Jacobian 与迁移谱的组合，有限波长失稳、行波和空间斑图都需要外加反应参数和嵌入尺度。

若单边捕食满足 Holling II 响应，可写

$$
P(N)=\frac{aN_{\rm prey}}{1+ahN_{\rm prey}},
\tag{226.2}
$$

处理时间 \(h\)、攻击率 \(a\) 和转换效率是外加。改变这些参数可在同一 FIB 图上产生稳定共存、极限环、捕食者入侵或猎物崩溃。迁移瓶颈、源汇边界和异质容量会把局部稳定态耦合成同步振荡或相位错位；无共同嵌入时不能把图距离直接当作扩散距离。

随机出生、死亡和迁移可用 Markov 跳跃过程描述。若 \(Z_{v,a}\) 为整数个体数，事件 \(r\) 的倾向率 \(a_r(Z)\) 给出化学主方程式；大种群极限可能趋向 (226.1)，但低数量时吸收态和离散涨落主导。环境噪声可在确定性稳定区触发局部灭绝、同步崩溃或罕见入侵，灭绝时间的尾部依赖噪声协方差、初态和边界补给。

入侵阈值常由无病或无捕食者平衡的最大增长本征值决定。对 SIR 型外加接触网络，基本再生数可用下一代矩阵 \(K_{uv}\) 的谱半径表示；但 \(K\) 的接触率、持续时间、免疫和干预均需外加。有限图上的一次传播事件不能区分高感染率、长传染期和高接触度三种机制，免疫网络也可能使几何连通与传播连通分离。

空间模式的有限尺寸统计可记录占据比例、团簇半径、入侵时间和灭绝时间。只有另给图族尺度、人口归一化、随机环境系综和观测窗口，才可检验波速、临界指数或大偏差标度。只测总种群会把局部灭绝和整体低密度投影到同一读出；只测感染者数量不能恢复接触矩阵和潜伏期分布。

因此，FIB 递归只提供种群相互作用和迁移的组合骨架。生态参数、反应函数、人口尺度、迁移、季节、噪声、边界和观测均须外加；共存、振荡、传播阈值、入侵、灭绝和空间斑图是在这些条件下的模型结论，不是 FIB ATOM 递归单独推出的普适生态统计定律。

## 227. FIB 图族上的外加高斯随机场、随机偏微分方程与极值统计

固定 FIB 图族 \(G_j=(V_j,E_j)\)，另在顶点或胞腔上定义随机场 \(X_j\)。FIB 只给组合邻接和可选路径；协方差核、噪声强度、嵌入距离、边界、尺度、外力和观测均需外加。离散高斯场可由精度矩阵 \(Q_j\) 定义为

$$
\mathbb P(X_j\in{\rm d}x)
\propto
\exp\!\left(-\frac12x^{\mathsf T}Q_jx\right){\rm d}x,
\qquad
\operatorname{Cov}(X_j)=Q_j^{-1},
\tag{227.1}
$$

其中 \(Q_j\) 的稀疏支撑可沿 FIB 边，但正定性、质量项和边界条件不是图递归的内禀结论。若 \(Q_j\) 取外加图拉普拉斯加质量项，相关长度由谱隙与嵌入距离共同决定；谱隙趋零才可能出现长程相关。

加入时间噪声后，可定义 Ornstein–Uhlenbeck 型随机方程

$$
{\rm d}X_j=-Q_jX_j\,{\rm d}t+\Sigma_j\,{\rm d}W_t,
\tag{227.2}
$$

其稳态协方差 \(C_j\) 满足 Lyapunov 方程

$$
Q_jC_j+C_jQ_j^{\mathsf T}=\Sigma_j\Sigma_j^{\mathsf T}.
\tag{227.3}
$$

若边权、噪声或反应项随位置和尺度变化，(227.2) 的连续极限可能是随机热方程、带色噪声的反应—扩散方程或分数阶随机 PDE；极限类型取决于 \(h_j\)、噪声相关和系数缩放，不能由 FIB 顶点数确定。

平稳高斯场的二点相关可写

$$
C_j(u,v)=\mathbb E[X_j(u)X_j(v)].
\tag{227.4}
$$

在给定嵌入和近似平移不变的图列中，\(C_j\) 的指数衰减、幂律衰减或长程平台分别对应有限相关、临界或公共模态；同一个 FIB 图通过改变 \(Q_j\) 和边界可实现这些不同情形。若只测有限顶点或总场，协方差核与边界条件通常不可唯一识别。

场的最大值 \(M_j=\max_{v\in V_j}X_j(v)\) 受相关长度、有效样本数和尾部共同控制。短程弱相关且满足适当正则条件时，中心化后的 \(M_j\) 可趋向 Gumbel；强相关、非平稳方差或有界场则可能给出不同极值域。把 \(|V_j|\) 当作独立样本数会高估极值增长；瓶颈、边界和公共模态会改变有效样本量。

零点或阈值集合 \(Z_c=\{v:X_j(v)=c\}\) 的连通和几何统计还需外加嵌入、插值和阈值。有限图上的零点数、等高线长度和极值簇可以随网格细化发生非平凡标度，但这些指数依赖协方差正则性、边界和观测分辨率。高斯场的符号渗流与前述开边渗流也只有在联合分布和阈值映射明确后才可比较。

观测若为 \(y_a(t)=\sum_vQ_{av}X_j(v,t)+\eta_a(t)\)，有限带宽和投影会把不同协方差、噪声源和边界状态映射到同一时间序列。要辨识相关长度、极值机制或随机 PDE 系数，需联合多点协方差、时间响应、尺度序列和独立边界实验。均值、方差或单次极值都不能证明高斯性、临界性或某个普适极值域。

因此，FIB 递归只提供随机场的组合支撑；协方差、噪声、质量项、嵌入、边界、尺度、初态和观测均须外加。高斯场相关、随机 PDE 极限、零点连通、极值分布和临界涨落是在这些条件下的模型结论，不是 FIB ATOM 递归单独推出的普适随机场定律。

## 228. FIB 图上的外加格点规范场、Wilson 回路与禁闭统计

固定 FIB 图族并另行选择面胞腔、边取向、群和边界。每条有向边携带群值变量 \(U_e\in G\)，顶点规范变换为

$$
U_e\longmapsto g_{t(e)}U_eg_{h(e)}^{-1}.
\tag{228.1}
$$

FIB 只给组合邻接；群、表示、Haar 测度、面权、耦合、温度方向和边界均外加。面 Holonomy

$$
U_f=\prod_{e\in\partial f}U_e^{\varepsilon_{f,e}}
\tag{228.2}
$$

按基点共轭，\(\operatorname{Tr}_R U_f\) 才是规范不变量。Wilson 作用量可写成

$$
S_W[U]=-\beta\sum_fw_f\,\operatorname{Re}\operatorname{Tr}_R U_f.
\tag{228.3}
$$

闭回路观测 \(W_R(C)\) 的面积律、周长律或屏蔽行为，取决于群的紧致性、耦合、动态物质和热力学极限。面积律可作为禁闭候选，但有限图上的低回路值不能单独证明禁闭；动态物质会使弦断裂，Polyakov 回路还要求外加时间周期、中心对称和边界。

若有嵌入尺度 \(a\)，连续规范场极限需另给 \(U_e=\exp({\rm i}aA_e+o(a))\)、耦合重标度和重整化；FIB 关系本身没有长度、方向、光锥或积分测度。无序样本、扭转边界和不同中心群可改变 Wilson 统计和去禁闭跃迁。只测局部边变量或一条回路，无法区分规范变换、非平凡 Holonomy、面积律与强阻尼周长律。

因此，FIB 递归只提供环路与胞腔骨架；规范群、链变量、作用量、边界、温度、无序、极限和测量均须外加。通量、Wilson 谱、禁闭/去禁闭和屏蔽是这些条件下的模型结论。

## 229. FIB 网络上的外加 Boltzmann 方程、碰撞积分与流体极限

固定 FIB 碰撞/迁移图，并另定义速度空间、位置嵌入、粒子分布、截面、外力、边界和尺度。含图迁移的动力学可写成

$$
\partial_tf_v+\boldsymbol c\cdot\nabla_xf_v
=Q_v[f]+\sum_uK_{uv}f_u-\sum_uK_{vu}f_v.
\tag{229.1}
$$

弹性二体碰撞积分 \(Q\) 的散射核、角分布和碰撞后速度决定质量、动量与能量是否守恒；它们不由 FIB 接续标签给出。微观可逆时，熵泛函可能单调下降并趋向外加 Maxwellian；主动、非弹性或多热浴碰撞则可产生冷却和非平衡熵流。

Knudsen 缩放

$$
\varepsilon(\partial_tf_\varepsilon+\boldsymbol c\cdot\nabla_xf_\varepsilon)
=Q(f_\varepsilon,f_\varepsilon)
\tag{229.2}
$$

在碰撞核有局部平衡、谱隙、相容初态和边界层条件时，可能给出 Euler 极限；保留一阶修正则得到 Navier–Stokes–Fourier 结构，黏度、热导率和扩散系数由碰撞算子线性化的逆决定。各向同性高频散射还可给出图上的扩散方程，而重尾自由程、长记忆或无有限二阶矩会产生莱维或分数输运。

镜面、漫反射、吸收、注入和图边界节点对应不同边界层与通量条件；\(\varepsilon\to0\) 与图体积极限的次序也可能不交换。BGK、离散速度和格子 Boltzmann 是外加闭合，不等于识别了真实截面。宏观密度、速度和应力只约束碰撞核的少数矩，不能恢复隐藏速度分布。

因此，FIB 只提供碰撞和迁移关系的组合载体；速度空间、截面、温度、外力、Knudsen 缩放、边界与观测均须外加。Boltzmann/主方程、熵耗散、Euler/Navier–Stokes 或扩散极限都是条件模型结论。

## 230. FIB 图上的外加 Allen–Cahn/Cahn–Hilliard 相场、熟化与界面统计

固定 FIB 图族，在顶点放置序参量 \(\phi_v\)，另给双稳势 \(W\)、梯度能、迁移率、守恒律、噪声、几何和边界。离散自由能可写

$$
\mathcal F_L(\phi)
=\sum_vm_v\frac{W(\phi_v)}{\varepsilon}
+\frac{\kappa}{2}\sum_{\{u,v\}}w_{uv}(\phi_u-\phi_v)^2.
\tag{230.1}
$$

Allen–Cahn 型非守恒动力学沿自由能下降，而 Cahn–Hilliard 型边通量满足

$$
J_{uv}=-M_{uv}(\mu_v-\mu_u),
\qquad
m_v\dot\phi_v=-\sum_uJ_{vu} .
\tag{230.2}
$$

在无通量、无源条件下，后者守恒 \(\sum_vm_v\phi_v\)，但守恒与耗散都依赖对称通量、边界和迁移率，FIB 邻接不自动保证。另给连续嵌入和尖界面极限时，Allen–Cahn 可能趋向平均曲率运动，Cahn–Hilliard 可能趋向 Mullins–Sekerka 或表面扩散；图拉普拉斯存在不等于已证明这些几何极限。

域长、结构因子、界面粗糙度和熟化指数取决于守恒律、噪声、流体对流、长程力、边界和尺度窗口。常见的 \(L_c(t)\sim t^{1/2}\) 或 \(t^{1/3}\) 只在各自外加机制成立时出现；有限图、钉扎和源项会改成平台或异常标度。只观测总相比例无法区分 Allen–Cahn、Cahn–Hilliard 和随机成核。

因此，FIB 只提供相场的邻接骨架；双稳势、梯度能、迁移率、守恒、噪声、连续几何、边界和极限均须外加。界面运动、熟化和域尺度统计是条件模型结论。


## 231. FIB 网络上的外加脉冲神经元、突触可塑性与临界活动统计

固定 FIB 图 \(G_j=(V_j,E_j)\)，在顶点放置膜电位或脉冲状态，在边上放置突触通道。FIB 只给连接和候选传播路径；神经元阈值、膜时间常数、突触权重、延迟、外部刺激、噪声和观测均须外加。积分—发放模型可写成

$$
\tau_v\dot V_v=-(V_v-V_{\rm rest})+R_vI_v(t),
\qquad
V_v\ge V_{\rm th}\Rightarrow V_v\mapsto V_{\rm reset}.
\tag{231.1}
$$

突触电流、抑制/兴奋类型和延迟由外加核 \(K_{uv}(t)\) 决定。若脉冲计数 \(N_v(t)\) 作为点过程，其条件强度可写为

$$
\lambda_v(t)=\phi_v\!\left(I_v(t)+\sum_u w_{uv}(K_{uv}*{\rm d}N_u)(t)\right),
\tag{231.2}
$$

非线性 \(\phi_v\)、噪声和绝对不应期不是 FIB 递归量。线性化平均场或神经场极限可能出现静息、放电、行波和振荡，但稳定性由权重矩阵与延迟谱决定。

突触可塑性可用外加 STDP 规则描述：

$$
\Delta w_{uv}=
\begin{cases}
A_+e^{-\Delta t/\tau_+},&\Delta t>0,\\
-A_-e^{\Delta t/\tau_-},&\Delta t<0,
\end{cases}
\tag{231.3}
$$

并受权重边界、归一化、抑制平衡和稳态驱动约束。相同 FIB 图可在固定权重、Hebbian、STDP 或 homeostatic 规则下形成不同的记忆、爆发和稀疏编码统计。

若外加脉冲过程近似分支过程，平均后代数 \(R_j\) 接近一时可能出现宽活动簇和临界候选；但有限网络、抑制反馈、相关输入和不应期会改变雪崩指数。活动同步、传播速度、相关长度和爆发持续时间需随图族尺度、刺激协议和观测窗共同定义。只测总体放电率不能区分局部同步、全局同步和输入驱动爆发。

观测若为 \(y_a(t)=\sum_vQ_{av}N_v(t)+\eta_a(t)\)，电极位置、带宽、阈值和排序算法会把多种脉冲模式投影到同一信号。要辨识连接权、延迟和可塑性，需要多点脉冲、刺激响应、跨频相位和权重干预；FIB 邻接不能直接解释为突触强度或因果方向。

因此，FIB 递归只提供神经元连接和传播路径骨架；膜模型、突触、延迟、可塑性、噪声、刺激、边界和观测均须外加。放电阈值、同步、雪崩、记忆和临界活动是指定神经动力学后的条件结论，不是 FIB ATOM 递归单独确定的普适神经统计定律。

## 232. FIB 图族上的外加时空波动、随机引力波背景与探测器响应

固定 FIB 图族，把顶点解释为源、传播单元或探测器位置，把边解释为可组合传播通道。真正的时空嵌入、背景度规、因果结构、波速、场方程、源、边界、噪声和仪器均须外加。线性化度规扰动可写

$$
g_{\mu\nu}=\bar g_{\mu\nu}+h_{\mu\nu},
\qquad
h_{\mu\nu}\mapsto h_{\mu\nu}
+\bar\nabla_\mu\xi_\nu+\bar\nabla_\nu\xi_\mu.
\tag{232.1}
$$

可观测量必须由曲率、测地线偏差或探测器世界线组合得到；FIB 边上的单个应变变量不自动是物理量。若给定离散传播算子，可写

$$
\ddot h_j+2\Gamma_j\dot h_j+c_j^2L_jh_j=S_j+\xi_j,
\qquad L_j=B_j^{\mathsf T}W_jB_j,
\tag{232.2}
$$

其中阻尼、波速、源投影和随机驱动均外加。图谱不能单独产生光锥、极化或真空传播速度。

平稳高斯随机背景的频域协方差可参数化为

$$
\langle\widetilde h_A(f,\hat n)
\widetilde h_{A'}^*(f',\hat n')\rangle
=\tfrac12\delta(f-f')\delta_{AA'}\delta^2(\hat n-\hat n')S_h(f),
\tag{232.3}
$$

各向异性、偏振相关或非高斯背景则需更一般的矩阵核。第 \(I\) 个探测器的响应可写为

$$
s_I(t)=\sum_A\int R_I^A(f,\hat n)
\widetilde h_A(f,\hat n)e^{2\pi{\rm i}ft}\,{\rm d}f\,{\rm d}^2\hat n+n_I(t).
\tag{232.4}
$$

交叉谱同时包含背景协方差、重叠约化函数和仪器噪声；观测时间、频带、基线几何、极化模板和噪声独立性均是外加。单探测器功率谱不能区分随机背景、图模态共振和仪器漂移。

有限图 Green 函数、反射/开放边界、源相关和边界缺陷会制造窄带峰、复频率、长驻留或非标准色散。若先固定样本再取大图极限，与先平均源和噪声再取极限通常不同；边权退化和长记忆还可导致亚扩散传播。未知响应函数、噪声相关和极化混合会使不同 \(S_h\) 产生同一交叉谱。

因此，FIB 递归只给关系和传播骨架；度规、场方程、规范、源、极化、边界、随机协方差、探测器响应和观测协议均须外加。随机背景频谱、交叉相关和探测信噪比是在这些结构明确后的模型结论，不是 FIB ATOM 递归单独推出的普适时空波动定律。

## 233. FIB 图上的外加最优输运、Wasserstein 梯度流与拥挤输运

固定 FIB 图 \(G_j\)，另给顶点质量、边成本、长度、容量、边界和时间标度。FIB 只给邻接或通道支撑，不给距离、质量单位和代价函数。静态离散运输可写为

$$
W_{p,j}^p(\rho^0,\rho^1)
=\min_{\pi\ge0}\sum_{u,v}c_{uv}^p\pi_{uv},
\qquad
\sum_v\pi_{uv}=\rho_u^0,\quad
\sum_u\pi_{uv}=\rho_v^1 .
\tag{233.1}
$$

若只允许图边流，成本由路径、边权和容量共同诱导，通常不等于顶点标签的欧氏距离。动态质量满足

$$
\dot\rho=B_j^{\mathsf T}J,\qquad \sum_v\rho_v=M,
\tag{233.2}
$$

给定 mobility 和能量 \(\mathcal F_j\) 时，离散梯度流可写成

$$
J=-\theta(\rho)B_j\nabla_\rho\mathcal F_j,
\qquad
\frac{{\rm d}}{{\rm d}t}\mathcal F_j
=-\sum_e\theta_e(\rho)|(B_j\nabla_\rho\mathcal F_j)_e|^2\le0 .
\tag{233.3}
$$

熵能量、势能、相互作用和容量势分别产生热流、漂移、聚集或硬拥挤；耗散来自外加 mobility 和能量，不是 FIB 递归的结果。JKO 离散、扩散极限和 Fokker–Planck 极限还要求边成本、体积、网格和时间步共同缩放。若等待时间重尾或 mobility 退化，可得到分数扩散、非高斯输运或拥堵冲击。

只测端点质量、总通量或终点代价，通常不能恢复内部最优计划、通量方向和瓶颈来源。随机成本的 quenched 最优路径与先平均成本的 annealed 路径也可能不同。因此，Wasserstein 距离、梯度流、拥挤阈值和旅行时间尾部都是外加成本、容量、边界、随机环境和观测条件下的模型结论。

## 234. FIB 网络上的外加开放量子系统、量子信道与 Lindblad 谱隙

固定 FIB 耦合支撑图，另给局部 Hilbert 空间、Hamiltonian、环境、初态和测量。局部 Hamiltonian 为

$$
H_j=\sum_vh_v+\sum_{\{u,v\}\in E_j}h_{uv},
\tag{234.1}
$$

弱耦合 Markov 近似下的约化态满足

$$
\dot\rho=\mathcal L_j(\rho)
=-{\rm i}[H_j,\rho]
+\sum_\alpha\left(L_\alpha\rho L_\alpha^\dagger
-\tfrac12\{L_\alpha^\dagger L_\alpha,\rho\}\right).
\tag{234.2}
$$

\(L_\alpha\) 的支撑、速率、浴谱和测量方式均外加；只有在构造成立时，\(\Phi_t=e^{t\mathcal L_j}\) 才是 CPTP 信道。唯一稳态且零模孤立时，Lindblad 谱隙

$$
\Delta_{\mathcal L,j}
=-\max_{\lambda\ne0}\operatorname{Re}\lambda
\tag{234.3}
$$

控制渐近混合时间；非正规 Jordan 块、暗子空间和守恒量会使谱隙不能代表所有短时观测。局部耗散可破坏纠缠，集体跳跃可产生亮/暗模，工程化耗散也可把纠缠态做成暗稳态；这些行为取决于 \(H_j,L_\alpha\)、温度、初态和测量。

量子详细平衡、对数 Sobolev 混合、跳跃计数大偏差和有限尺寸耗散相变都要求外加 Gibbs 态、驱动协议、尺度极限和可观测通道。只测单体边缘或总能量，不能恢复暗模、多体跳跃相关和 Hamiltonian 相位。因此，开放量子信道、纠缠寿命、谱隙和稳态统计不是 FIB 耦合支撑单独决定的。

## 235. FIB 通道网络上的外加燃烧前沿、反应—扩散—对流与火焰不稳定

固定 FIB 通道图，另给长度、截面、热容、密度、热导率、扩散率、流速、化学反应、壁面散热和点火条件。温度 \(T\) 与燃料 \(Y_F\) 可满足

$$
\rho c_p(\partial_tT+u\cdot\nabla T)
=\nabla\!\cdot(k_T\nabla T)+Q\omega(T,Y_F)+q_{\rm ext},
\tag{235.1}
$$

$$
\partial_tY_F+u\cdot\nabla Y_F
=\nabla\!\cdot(D_F\nabla Y_F)-\nu_F\omega(T,Y_F).
\tag{235.2}
$$

Arrhenius 反应、热扩散和流速均为外加。给定特征长度、流速、扩散和化学时间后，Damköhler、Péclet 和 Lewis 数才有定义；小或大的 Damköhler 数都不单独保证自持火焰。

一维行波、点火阈值、有限通道淬熄和前沿速度还依赖热损失、入口/出口、壁面和节点混合。横向扰动、密度跃迁、Markstein 长度、浮力、剪切和随机流决定火焰不稳定；粗粒化时一般有 \(\overline{\omega(T,Y_F)}\ne\omega(\overline T,\overline{Y_F})\)，必须另给混合—反应闭合。图上存在传播路径不等于热反馈足以点火或维持前沿。

因此，FIB 只提供通道邻接和路径骨架；反应、热扩散、流速、密度、放热、边界、尺度和观测均须外加。火焰速度、点火/淬熄概率、Damköhler 标度和不稳定性是条件燃烧模型的结论，不能由 FIB ATOM 递归单独推出。

## 236. FIB 网络上的外加自旋玻璃、挫折耦合与老化统计

固定 FIB 图 \(G_j=(V_j,E_j)\)，在顶点放置自旋 \(\sigma_v\)，在边上放置带符号或随机耦合 \(J_{uv}\)。FIB 只给稀疏支撑；耦合分布、温度、外场、边界、更新规则和观测均外加。随机耦合 Ising Hamiltonian 为

$$
H_J(\sigma)=-\sum_{\{u,v\}\in E_j}J_{uv}\sigma_u\sigma_v-\sum_vh_v\sigma_v .
\tag{236.1}
$$

正负耦合造成挫折，环路乘积和、度异质性与随机场共同决定是否存在玻璃态。有限图 Gibbs 测度仍解析，严格玻璃转变需要外加图列、无序系综和热力学极限。

重叠序参量可用两份相同无序但独立热噪声的复制定义

$$
q_{12}=\frac1{|V_j|}\sum_v\sigma_v^{(1)}\sigma_v^{(2)}.
\tag{236.2}
$$

其分布、易感率和 Binder 型量只有在指定复制、边界和无序平均后才有意义。淬火自由能 \(\mathbb E_J\log Z_J\) 与退火自由能 \(\log\mathbb E_JZ_J\) 不同；长程相关、重尾耦合和稀疏瓶颈会改变相图。

若采用 Glauber 或 Metropolis 动力学，自相关函数

$$
C(t,t_w)=\frac1{|V_j|}\sum_v
\langle\sigma_v(t_w+t)\sigma_v(t_w)\rangle
\tag{236.3}
$$

可能同时依赖等待时间 \(t_w\) 与观测延迟 \(t\)，表现为老化和记忆。四点易感性、响应函数与温度循环可区分真正的玻璃动力学、有限尺寸慢混合和静态无序。只测单次磁化轨迹不能恢复能垒分布、无序相关或复制重叠。

同一 FIB 图可在铁磁、反铁磁、随机符号、随机场和非平衡驱动下呈有序、碎片化、玻璃、记忆或快速混合。因而挫折、玻璃转变、老化时间和响应—涨落关系都依赖外加耦合、温度、动力学、噪声、边界和观测协议；FIB 递归不单独决定自旋玻璃统计。

## 237. FIB 网络上的外加蛋白质折叠、能量景观与玻璃化动力学

固定 FIB 图 \(G_j=(V_j,E_j)\)，可把顶点解释为局部构象、接触片段或粗粒化状态，把边解释为允许的构象跃迁或接触重排。FIB 只提供组合状态空间和候选路径；氨基酸序列、三维嵌入、键角、溶剂、温度、摩擦、力场、边界和时间尺度均须外加。对构象 \(a\) 的能量可分解为

$$
E_j(a)=E_{\rm cov}(a)+E_{\rm contact}(a)+E_{\rm solv}(a)
       +E_{\rm elec}(a)+E_{\rm ext}(a),
\tag{237.1}
$$

各项的函数形式、参数和允许构象集合并不由 FIB 递归确定。即使两个 FIB 图具有相同度数和相同路径长度，它们也可以对应不同序列、手性约束与空间排斥，因而具有不同的天然态和折叠障碍。

在马尔可夫状态模型中，构象概率满足

$$
\dot p_a=\sum_b\bigl(k_{ba}p_b-k_{ab}p_a\bigr),
\qquad
k_{ab}=k_0 a_{ab}
\exp\!\left[-\beta\bigl(B_{ab}-E_j(a)\bigr)\right],
\tag{237.2}
$$

其中 \(a_{ab}\) 是允许跃迁指示，\(B_{ab}\) 是过渡态或有效势垒。若 \(B_{ab}=B_{ba}\)、环境满足热平衡且跃迁核满足微观可逆性，才有

$$
\frac{k_{ab}}{k_{ba}}=e^{-\beta(E_j(b)-E_j(a))},
\qquad
p_a^{\rm eq}=Z^{-1}e^{-\beta E_j(a)} .
\tag{237.3}
$$

非平衡拉伸、化学能输入、分子伴侣和主动输运会破坏该详细平衡关系。因而 FIB 上存在一条从展开态到紧致态的路径，不等于该路径具有正的折叠通量，也不等于体系会到达指定天然态。

给定序参量 \(Q(a)\)，其粗粒化自由能为

$$
F_j(q)=-\beta^{-1}\log\!\sum_{a:Q(a)=q}e^{-\beta E_j(a)} .
\tag{237.4}
$$

势垒高度、漏斗宽度、亚稳中间态和折叠时间取决于 \(Q\) 的选择、态空间分辨率和积分掉的自由度。用不同接触数、半径、二面角或实验信号作 \(Q\)，同一轨迹可能呈现单漏斗、双漏斗或多阱景观；粗粒化还会产生记忆核，使简单马尔可夫模型失效。

从未折叠集合 \(U\) 到天然集合 \(N\) 的反应坐标可用承诺概率 \(q_a\) 表示：

$$
\sum_b k_{ab}(q_b-q_a)=0\quad(a\notin U\cup N),
\qquad q_a=0\ (a\in U),\quad q_a=1\ (a\in N).
\tag{237.5}
$$

该方程需要速率、边界集合和初始分布；FIB 邻接只决定求和的候选索引。折叠时间、过渡路径系综和速率限制步骤还受溶剂摩擦、内坐标耦合、温度跳变、拉伸协议和观测死区影响。单分子 FRET、氢交换或整体圆二色信号通常只给 \(Q\) 的投影，不能唯一恢复完整的承诺概率或隐藏中间态。

若势垒和局部摩擦呈宽分布，构象相关函数可出现

$$
C_j(t)=\langle A(0)A(t)\rangle
\simeq C_0\exp\![-(t/\tau_j)^{\gamma_j}],
\qquad 0<\gamma_j<1,
\tag{237.6}
$$

或幂律尾部。拉伸指数、幂律区间和所谓玻璃化温度依赖能垒无序、链长、溶剂黏度、采样窗和有限尺寸；它们不能从 FIB 路径计数单独推出。折叠—解折叠循环中的滞后可能来自真正的非平衡驱动，也可能来自仪器卷积、慢隐变量或状态定义变化，必须用独立扰动和重复轨迹区分。

翻译速度、核糖体出口、分子伴侣、二硫键形成和拥挤环境会改变有效景观与跃迁核。相同的 FIB 组合骨架在平衡溶液、共翻译折叠、机械拉伸和主动伴侣作用下可呈现不同的折叠路径、错误聚集和老化统计。因此，天然态选择、折叠速率、过渡态位置、玻璃化慢化和记忆效应都是在序列、能量、动力学、环境、边界与观测协议均已指定后的条件结论；FIB ATOM 递归本身不单独决定蛋白质折叠统计。


## 238. FIB 细胞复形上的外加磁性斯格明子、拓扑电荷与热激活漂移统计

固定 FIB 细胞复形 \(K_j=(V_j,E_j,F_j)\)，可把顶点解释为自旋采样点、边解释为相邻耦合支撑、面解释为定向 plaquette。FIB 只提供组合邻接、入射关系和候选路径；自旋的空间嵌入、面定向、晶格尺度、三维法向、交换常数、手性相互作用、磁场、阻尼、载流子、温度、边界、极限和观测均须外加。给每个顶点一个单位磁化向量 \(\mathbf n_v\in S^2\) 后，一个可能的离散能量为

$$
E_j(\mathbf n)=-J\sum_{\{u,v\}\in E_j}\mathbf n_u\!\cdot\!\mathbf n_v
+D\sum_{\{u,v\}\in E_j}\mathbf e_{uv}\!\cdot\!(\mathbf n_u\!\times\!\mathbf n_v)
+K\sum_{v\in V_j}\bigl(1-(\mathbf n_v\!\cdot\!\hat{\mathbf z})^2\bigr)
-\mu\sum_v\mathbf B\!\cdot\!\mathbf n_v+E_{\rm demag}+E_{\rm bdry} .
\tag{238.1}
$$

其中 \(J,D,K,\mu\)、外场 \(\mathbf B\)、偶极项和边界能都来自外加磁性材料模型；\(\mathbf e_{uv}\) 需要额外的几何嵌入和键方向，不能由无向 FIB 边单独给出。改变交换符号、Dzyaloshinskii–Moriya 项、各向异性或外场，可在同一 FIB 支撑上得到均匀磁态、条纹、畴壁、孤立旋涡或斯格明子晶格。

若三角面 \((v_1,v_2,v_3)\) 的自旋像在球面上不跨越奇异分支，可用有向球面立体角定义离散拓扑荷

$$
Q_j=\frac1{4\pi}\sum_{f=(v_1,v_2,v_3)\in F_j}
\Omega(\mathbf n_{v_1},\mathbf n_{v_2},\mathbf n_{v_3}),
\tag{238.2}
$$

其中面定向、三角剖分、立体角分支和边界补面均是外加约定。只有在自旋场足够平滑、边界不泄漏且取定连续化方案时，\(Q_j\) 才近似整数；有限网格、奇异核心、开边界或强噪声可让电荷通过边界逸出或在离散重连中改变。因此，FIB 面的存在本身不保证拓扑保护，也不决定斯格明子数。

给定有效场 \(\mathbf H_v^{\rm eff}=-\partial E_j/\partial\mathbf n_v\)，外加随机 Landau–Lifshitz–Gilbert 动力学可写为

$$
\dot{\mathbf n}_v=-\gamma\,\mathbf n_v\!\times\!(\mathbf H_v^{\rm eff}+\boldsymbol\xi_v)
+\alpha\,\mathbf n_v\!\times\!\dot{\mathbf n}_v
+\boldsymbol\tau_v^{\rm STT},
\qquad |\mathbf n_v|=1 .
\tag{238.3}
$$

陀螺比 \(\gamma\)、阻尼 \(\alpha\)、自旋转移力矩、噪声协方差、温度和电流均须外加；若要求热平衡，还需另加满足涨落—耗散关系的噪声。对足够刚性的孤立纹理，集体坐标近似可能给出 Thiele 方程

$$
\mathbf G\!\times\!(\mathbf v-\mathbf u)+\alpha\mathsf D\,\mathbf v
-\beta\mathsf D\,\mathbf u+\nabla U_{\rm pin/bdry}(\mathbf R)
=\mathbf F_{\rm ext}+\boldsymbol\eta(t),
\qquad \mathbf G\propto Q_j\hat{\mathbf z},
\tag{238.4}
$$

速度 \(\mathbf v\)、漂移方向和所谓 skyrmion Hall 角同时依赖拓扑荷、耗散张量 \(\mathsf D\)、电流漂移 \(\mathbf u\)、钉扎势、边界力和随机力。FIB 路径只能列出纹理可能经过的组合通道；它不提供质量、陀螺系数、势垒、连续坐标或真实几何距离，因而不能单独推出横向漂移或无损传播。

热激活成核、湮灭和拓扑电荷翻转可在给定能量景观后用过渡率表示：

$$
\Gamma_{a\to b}(T)\simeq \Gamma_0(a,b)
\exp\!\left[-\frac{\Delta E_{a\to b}(J,D,K,\mathbf B,\text{边界})}{k_{\rm B}T}\right],
\tag{238.5}
$$

但前因子、最小鞍点、核心奇异化和边界逃逸路径都需要外加动力学与几何。淬火缺陷、随机各向异性和热噪声会把相同的 FIB 路径集合分成不同寿命与迁移率；先固定无序再取大图极限和先做无序平均再取极限也可能给出不同的纹理密度与电荷涨落。

若形成斯格明子液体或晶格，面密度 \(n_{\rm sk}\)、结构因子和电荷相关函数可写成

$$
S_Q(\mathbf k)=\frac1{|F_j|}
\mathbb E\left|\sum_{f\in F_j}q_f e^{-i\mathbf k\cdot\mathbf r_f}\right|^2,
\qquad q_f=\frac{\Omega_f}{4\pi},
\tag{238.6}
$$

其中面坐标、波矢、系综和平均方式均外加。相同组合复形可在不同温度、外场、载流子耦合与边界下表现为稀薄孤子、短程有序、六角晶格、条纹或无拓扑纹理；\(S_Q\) 的峰、关联长度和有限尺寸标度不是 FIB 递归的普适输出。

电子若绝热跟随磁化，可能测得拓扑霍尔项 \(\rho_{xy}^{\rm top}\propto P\,n_{\rm sk}\)，但自旋极化 \(P\)、载流子密度、散射机制、接触几何和普通霍尔背景都须外加。磁光、磁力显微、输运和局部探针把 \(\mathbf n\) 与 \(Q\) 投影到不同观测通道；单一总磁化或单一输运曲线不能唯一恢复隐藏的斯格明子数、核心结构与湮灭路径。

因此，FIB ATOM 递归在此只提供自旋相互作用的组合支撑、细胞接缝和候选迁移路径；几何嵌入、磁性能量、拓扑荷定义、LLG/Thiele 动力学、热噪声、外场、电流、边界、无序、尺度极限和观测协议全部为外加。斯格明子是否存在、拓扑荷是否近似守恒、热激活寿命、漂移/霍尔角、晶格统计与拓扑霍尔响应，都是在这些外加结构被明确后得到的条件结论，不能由 FIB ATOM 关系单独推出普适磁性统计定律。

## 239. FIB 网络上的外加传染病传播、免疫结构与爆发临界统计

固定 FIB 图族 \(G_j=(V_j,E_j)\)，把顶点解释为宿主、地点或粗粒化人群单元，把边解释为允许接触或传播的支撑。FIB 递归只给出这种组合支撑及其可拼接路径；人口权重、接触频率、传播率、潜伏期、恢复率、免疫、时间重连、外部输入、边界和观测均须外加。若每个单元以感染比例 \(i_v\)、恢复/免疫比例 \(r_v\) 表示，一个可能的连续时间平均场闭合为

$$
\lambda_v(t)=\lambda_v^{\rm ext}(t)+\sum_{u:(u,v)\in E_j}B_{vu}(t)i_u(t),
\qquad
\dot i_v=(1-i_v-r_v)\lambda_v-\gamma_v i_v,
\tag{239.1}
$$

$$
\dot r_v=\gamma_v i_v-\omega_v(t)r_v+\nu_v(t)(1-i_v-r_v).
\tag{239.2}
$$

其中 \(B_{vu}\) 是从 \(u\) 到 \(v\) 的有效接触—传播率，\(\gamma_v\) 是恢复率，\(\omega_v\) 是免疫衰减，\(\nu_v\) 是接种或外加免疫。FIB 只限制 \(B_{vu}\) 的零模式；其非零数值、人口归一化和平均场独立性都不是递归量。有限宿主的随机跃迁、相关接触和过度离散一般不由式 (239.1) 自动给出。

在疾病自由态附近、传播率暂时固定并忽略易感耗竭时，线性化可写成

$$
\dot{\boldsymbol i}=(B-\Gamma)\boldsymbol i,
\qquad
K=\Gamma^{-1}B,
\qquad
\mathcal R_{\rm lin}=\rho(K),
\quad \Gamma=\operatorname{diag}(\gamma_v).
\tag{239.3}
$$

只有在 Markov 恢复、线性近似和给定边界成立时，\(\mathcal R_{\rm lin}>1\) 才表示局部增长方向；它不是任意 FIB 图的普适阈值。节点人口、异质接触、边界输入或时间依赖会把阈值改为算子谱半径、Floquet 乘子或随机增长率。相同 FIB 支撑可因 \(B\)、\(\Gamma\) 或人口权重不同而处于衰减、地方病或爆发区。

若感染期为随机时长 \(D_u\)，且边接触在给定条件下近似独立，边 \(u\to v\) 的单次有效传递概率可写为

$$
T_{uv}=1-\mathbb E\!\left[\exp\!\left(-\int_0^{D_u}\!\beta_{uv}(s)\,\mathrm ds\right)\right].
\tag{239.4}
$$

在局部树状、无重复暴露相关和固定源集合等额外条件下，最终感染集合可以用有向键渗流或消息传递近似描述。令 \(m_{u\to v}\) 为删去 \(v\) 后 \(u\) 被感染的概率，初始感染概率为 \(p_u\)，则一种闭合为

$$
m_{u\to v}=1-(1-p_u)\prod_{w\in N(u)\setminus\{v\}}
\bigl(1-T_{wu}m_{w\to u}\bigr),
\qquad
m_v=1-(1-p_v)\prod_{u\in N(v)}\bigl(1-T_{uv}m_{u\to v}\bigr).
\tag{239.5}
$$

重复接触、家庭相关、时间顺序、共同暴露、有限恢复和干预会破坏该独立边映射。FIB 上存在从源到 \(v\) 的路径只说明传播可能有组合通道，不说明通道在感染期内被激活，更不说明最终感染概率为正或达到巨型可达集。

在外加参数接近某个分支或渗流临界面时，爆发规模 \(M\) 常用有限尺寸标度作诊断，例如

$$
\Pr(M=m)\approx m^{-\tau}\,\mathcal F\!\left(m/m_c(L)\right),
\tag{239.6}
$$

其中 \(L\) 是图族尺度，\(m_c(L)\) 是截断。指数 \(\tau\)、截断增长、巨型感染集和易感率取决于图族、度分布、边相关、传播核和观测窗；在固定有限图上看见幂律区间不等于证明普适临界点。重尾度、社区瓶颈、定向边和控制措施可以分别产生宽爆发分布、长尾延迟或多阶段波峰。

若接触具有记忆，感染强度更适合写成点过程卷积

$$
\lambda_v(t)=\lambda_v^{\rm ext}(t)+
\sum_u\int_0^\infty K_{uv}(s)\,\mathrm dN_u(t-s),
\tag{239.7}
$$

\(K_{uv}\) 同时携带代际间隔、接触时段、潜伏期和报告延迟。季节驱动可令 \(B_{vu}(t)=\bar B_{vu}[1+a_{vu}\cos(\Omega t+\phi_{vu})]\)，从而出现行波、准周期、多波峰或灭绝后再引入；这些现象由时间核、输入协议和免疫衰减决定。非指数恢复、分数记忆和行为反馈还可产生亚指数增长或长尾等待，不能由静态 FIB 邻接推出。

实际观测通常是带抽样和延迟的投影，例如

$$
 y_a(t)=\sum_v Q_{av}\int_0^\infty D_v(s)i_v(t-s)\,\mathrm ds+\eta_a(t),
\tag{239.8}
$$

其中 \(Q\) 是采样/空间汇总，\(D_v\) 是检测灵敏度与报告延迟，\(\eta\) 是噪声。单点病例曲线不能唯一恢复传播矩阵、无症状比例、代际间隔或免疫衰减；不同 \((B,\Gamma,K,Q,D)\) 可在有限观测窗给出同一增长率和同一总病例数。要识别边方向和干预效应，需要多点时间序列、接触调查、外部扰动或可辨识的先验，而 FIB 路径计数本身不足以提供这些信息。

因此，FIB ATOM 递归只提供接触关系、传播支撑、可达路径和可能的层级分解；感染动力学、随机时间核、免疫机制、人口异质性、干预、初始条件、边界输入及观测协议均须外加。基本再生数、爆发概率、最终规模、地方病水平、幂律或长尾统计，以及波峰和灭绝时间，都是在这些条件明确后的传染病模型结论，不是 FIB 递归单独决定的普适传播定律。

## 240. FIB 网络上的外加孔弹性、固结扩散与力—流耦合统计

固定一族 FIB 图 \(G_j=(V_j,E_j)\) 及其定向关联矩阵 \(B_j\)。FIB 只给出顶点的组合关系、可行通道、切分和递归层级；几何嵌入、孔隙体积、截面、弹性、渗透率、流体压缩性、时间单位、边界和随机源均另行给定。令 \(u\) 为节点位移，\(p\) 为孔压，\(D_j\) 为由外加几何把位移映到边伸长的算子，\(C_j\) 为边弹性矩阵，\(G_j\) 为力—压耦合矩阵，\(M_{0,j}\) 为排水储存矩阵，\(K_j\) 为边导流系数矩阵。一个准静态离散孔弹性模型可写为

$$
A_j u-G_jp=f,
\qquad A_j=D_j^{\mathsf T}C_jD_j,
\qquad L_j=B_j^{\mathsf T}K_jB_j,
\tag{240.1}
$$

$$
M_{0,j}\dot p+G_j^{\mathsf T}\dot u+L_jp=s.
\tag{240.2}
$$

这里的压力插值、法向、边长和 \(G_j\) 的构造都属于外加几何与本构；FIB 递归本身不产生应变、应力或压力。去除刚体模态并施加力学边界后，若 \(A_j\) 可逆，消去 \(u\) 得

$$
M_j\dot p+L_jp=\widetilde s,
\qquad
M_j=M_{0,j}+G_j^{\mathsf T}A_j^{-1}G_j,
\qquad
\widetilde s=s-G_j^{\mathsf T}A_j^{-1}\dot f.
\tag{240.3}
$$

恒定载荷时 \(\widetilde s=s\)。在排水边界消除压力常数模态、且 \(M_j,L_j\) 正定的条件下，广义模态满足

$$
L_j\phi_{j,r}=\lambda_{j,r}M_j\phi_{j,r},
\qquad
0<\lambda_{j,1}\le\lambda_{j,2}\le\cdots,
\qquad
\tau_{j,r}=\lambda_{j,r}^{-1}.
\tag{240.4}
$$

因而初始过压的线性衰减是这些模态的叠加，最慢固结时间由 \(\tau_{j,1}\) 控制。若另加图列、网格尺度和系数缩放，使 \(\lambda_{j,1}\asymp L_j^{-z}\)，则 \(z\) 是由孔隙几何、\(K_j\)、\(C_j\)、\(M_{0,j}\) 与边界共同确定的动态指数；FIB 路径长度或原子层数单独不能确定 \(z\)。若存在未排水边界，\(L_j\) 有零模，压力守恒模态不衰减，必须先声明总质量约束或另给泄漏项。

把外部注入和材料不确定性写成零均值噪声时，

$$
M_j\dot p+L_jp=\xi_j(t),
\qquad
\mathbb E[\xi_j(t)\xi_j(t')^{\mathsf T}]=Q_j\,\delta(t-t'),
\tag{240.5}
$$

稳定协方差 \(C_{p,j}=\mathbb E[p p^{\mathsf T}]\) 满足

$$
M_j^{-1}L_jC_{p,j}+C_{p,j}L_jM_j^{-1}
=M_j^{-1}Q_jM_j^{-\mathsf T}.
\tag{240.6}
$$

只有在 \(M_j,L_j\) 对称正定且外加噪声满足 \(Q_j=2\Theta L_j\) 时，才有简化式 \(C_{p,j}=\Theta M_j^{-1}\)；一般注入谱、相关时间和边界通量会改变压力方差及空间相关。位移协方差还要经过 \(A_j^{-1}G_j\) 投影，不能由压力协方差直接替代。

对一条 FIB 合法路径 \(\gamma\)，外加几何和导流系数给出的串联水力阻抗为

$$
R_j(\gamma)=\sum_{e\in\gamma}\frac{\ell_e}{\kappa_e A_e},
\tag{240.7}
$$

但网络的实际流量由全部路径和节点守恒共同决定；最短 FIB 路径既不必具有最小 \(R_j\)，也不必控制最大压力。若 \(\kappa_e\)、\(C_e\) 或孔隙储量为淬火随机量，固结时间和压力响应应先对每个样本求 \((M_j,L_j)\) 再平均：

$$
\mathbb E_{\rm q}\!\left[(zM_j+L_j)^{-1}\right]
\ne
\left(z\mathbb E_{\rm q}M_j+\mathbb E_{\rm q}L_j\right)^{-1}
\tag{240.8}
$$

一般不等式中的差异正是瓶颈和稀有低渗边的来源。窄系数分布且有统一谱隙时，压力脉冲具有有限个指数模态；若导流率在零附近有宽尾、储存量也重尾，样本间的 \(\tau_{j,1}\) 可无界，平均响应可能表现为拉伸指数、幂律或分数阶记忆。具体尾指数须由系数分布、图列和边界联合确定，不能从 FIB 递归推出。

若保留惯性，模型扩展为

$$
\rho_j\ddot u+\Gamma_j\dot u+A_ju-G_jp=f,
\qquad
M_{0,j}\dot p+G_j^{\mathsf T}\dot u+L_jp=s.
\tag{240.9}
$$

由此出现快、慢压弹性波以及耗散共振；波速、衰减率和模态分裂依赖密度、阻尼、弹性、孔隙率、流体黏度和排水边界。仅有 FIB 的邻接与递归层级不会产生纵横波区别、因果锥或 Biot 波速。

有限压力传感器和边界流量只观察传递函数的有限投影。例如给定观测矩阵 \(H\) 和输入 \(s\)，频域读数为

$$
\widehat y(z)=H(zM_j+L_j)^{-1}\widehat s(z)
+H_uA_j^{-1}G_j(zM_j+L_j)^{-1}\widehat s(z),
\tag{240.10}
$$

不同的内部渗透率、储存量与弹性分布可以具有相同的有限频率传递函数，却给出不同的内部压力和应力场；增加 FIB 层级不自动消除这种不可识别性。需增加内部传感器、独立载荷或已验证的本构先验，才能区分瓶颈位置、排水路径和力—流耦合强度。

因此，FIB ATOM 递归在孔弹性问题中只提供组合支撑、合法路径、切割和层级骨架；位移几何、应力—压力本构、渗透率、储存矩阵、流体参数、惯性、随机协方差、边界、观测和连续极限均须外加。固结时间、压力协方差、孔压波、瓶颈尾部和力—流响应是这些外加数据被指定后的条件统计规律，不是 FIB 递归单独推出的普适孔弹性定律。

## 241. FIB 关系网络上的外加随机食物网、稳定性谱与共同灭绝统计

第226节的空间化种群模型说明了给定相互作用参数后如何出现共存、振荡与灭绝。本节只研究这些参数本身来自随机食物网系综时的稳定性与联合灭绝边界。固定 FIB 图族 \(G_j=(V_j,E_j)\)，顶点可代表物种或斑块，边只表示相互作用或迁移候选。FIB 提供组合支撑、路径和层级索引；摄食方向、正负号、耦合强度、承载量、增长率、迁移、噪声、初态、吸收边界、时间单位及观测阈值全部外加。

令 \(X(t)=(X_i(t))_{i\in V_j}\) 为非负种群量，给定外加增长向量 \(r_j\)、相互作用矩阵 \(A_j\)、迁移矩阵 \(M_j\) 和噪声系数 \(\Sigma_j\)，可用

$$
{\rm d}X
=\left[\operatorname{diag}(X)(r_j-A_jX)+M_jX\right]{\rm d}t
+\Sigma_j(X)\,{\rm d}W_t .
\tag{241.1}
$$

其中 \(M_j\) 的非对角非负性、质量守恒或源汇边界必须另行规定，\(\Sigma_j\) 也必须配合吸收/反射规则以保持正锥。FIB 边集至多限制 \(A_{i\ell}\)、\(M_{i\ell}\) 的允许非零位置；它不决定方向、符号、数值或噪声相关。给定一个无噪声内部平衡 \(x^*>0\)，其方程与线性化矩阵分别为

$$
\operatorname{diag}(x^*)\bigl(r_j-A_jx^*\bigr)+M_jx^*=0,
\qquad
D_j^*=\operatorname{diag}(r_j-A_jx^*)
-\operatorname{diag}(x^*)A_j+M_j .
\tag{241.2}
$$

局部渐近稳定要求 \(\max\operatorname{Re}\operatorname{spec}(D_j^*)<0\)；该判据还须与边界平衡的不变面分开检查。

随机食物网可在允许边上赋予系综，例如在给定度尺度 \(d_j\) 下令

$$
(A_j)_{i\ell}={\bf1}_{\{(i,\ell)\in E_j\}}
\left(\frac{\mu_j}{d_j}+\frac{g_j}{\sqrt{d_j}}\xi_{i\ell}\right),
\qquad
\operatorname{Corr}(\xi_{i\ell},\xi_{\ell i})=\rho_j,
\tag{241.3}
$$

并另给对角自限、缺边比例、符号分布和高阶相关。这个式子只是一个外加稀疏/稠密缩放例子；若度数、尾部或相关性改变，缩放也必须改变。对每个耦合样本 \(A_j\) 先求平衡再考察 \(D_j^*\)，得到 quenched 稳定事件

$$
\mathcal S_j(A_j)=\left\{\max\operatorname{Re}\operatorname{spec}(D_j^*)<0\right\}.
\tag{241.4}
$$

其概率、谱边缘涨落和所谓 May 型阈值依赖 \(\mu_j,g_j,\rho_j\)、自限项、图列和归一化；FIB 的度数或层级不能替代这些系综。即使平均谱相同，互易捕食、反互易捕食和有向环的谱实部也可以不同。有限样本先取稳定性再平均，与先平均相互作用后分析一个平均矩阵，是两个不同的操作。

若给定灭绝阈值 \(\varepsilon>0\) 和外部补给规则，定义

$$
T_{i,j}^{\varepsilon}=\inf\{t\ge0:X_i(t)\le\varepsilon\},
\qquad
N_j(t)=\sum_{i\in V_j}{\bf1}_{\{T_{i,j}^{\varepsilon}\le t\}} .
\tag{241.5}
$$

对固定相互作用样本的噪声条件律记为 \(\mathbb P_W(\,\cdot\mid A_j)\)。共同灭绝的对象是联合量

$$
C_{ik,j}(t)=\operatorname{Cov}_{A,W}
\left({\bf1}_{\{T_{i,j}^{\varepsilon}\le t\}},
      {\bf1}_{\{T_{k,j}^{\varepsilon}\le t\}}\right),
\tag{241.6}
$$

它同时受 \(A_j\) 的共享耦合、环境噪声协方差、人口噪声、初态相关和迁移边界影响。仅知道每个物种的边缘灭绝概率不能确定 \(C_{ik,j}\) 或级联规模分布；两个联合噪声实现可以保留全部单物种边缘而给出不同的共同灭绝率。若有持续迁入，\(X_i=0\) 不再是吸收态；若观测阈值随样本大小变化，有限尺寸的“灭绝”也可能只是检测不到。

quenched 统计保留每个 \(A_j\) 的条件律后再对系综平均，annealed 统计则把相互作用随机性并入联合过程。有限 \(j\) 的边缘平均可以写成全概率分解，但典型样本、极端尾部以及 \(j\to\infty\) 与系综平均的次序一般不同。因而 \(N_j(t)\) 的尾部可能呈有限尺寸截断幂律、拉伸指数、近似指数或无稳定幂律；这些形状不能只由 FIB 路径数或层级深度推出。

观测总生物量、度数或单个时间点通常无法辨认隐藏的相互作用符号、互易相关、迁移方向和共同噪声。需要时间序列、物种替换、定向干预或额外先验，才能切开相同边缘读数对应的参数纤维。故 FIB ATOM 递归只提供食物网的组合骨架、可行路径与层级候选；随机相互作用系综、生态动力学、噪声联合实现、吸收边界、尺度极限和观测协议均为外加。稳定概率、谱阈值、共同灭绝相关和级联大偏差，只有在这些条件全部指定后才是模型结论，不能由 FIB 递归单独推出普适生态统计律。

## 242. FIB 图族上的外加宇宙学膨胀、暗物质聚集与大尺度结构统计

固定 FIB 图族 \(G_j=(V_j,E_j)\)，可把顶点解释为粗粒化空间单元、候选晕中心或观测体素，把边解释为允许的邻接、合并或信息传播关系。FIB 只提供组合支撑和路径；时空度规、尺度因子、共动坐标、物质成分、引力方程、初始扰动、观测红移和尺度极限均须外加。因而图上的距离、体积和波数不能仅由递归层数或路径长度定义。

在外加的 FLRW 背景中，尺度因子 \(a(t)\) 和 Hubble 率 \(H=\dot a/a\) 满足

$$
H^2(a)=H_0^2\left[\Omega_r a^{-4}+\Omega_m a^{-3}+\Omega_k a^{-2}+\Omega_\Lambda\right],
\tag{242.1}
$$

其中各密度参数、曲率和宇宙学常数不是 FIB 量。给定共动坐标后，线性物质密度扰动 \(\delta=\delta\rho_m/\bar\rho_m\) 的增长因子可满足

$$
\ddot\delta+2H\dot\delta-4\pi G\bar\rho_m\delta=0,
\qquad
\delta(a,\mathbf k)=D(a)\,\delta(a_\ast,\mathbf k),
\tag{242.2}
$$

但式中引力常数、平均密度、规范选择和初始扰动谱都要另行给定。若在 FIB 支撑上构造离散算子 \(L_j=B_j^{\mathsf T}W_jB_j\)，还必须指定节点位置 \(x_v\)、体积、边权及其与共动度规的对应，才能把 \(L_j\) 解释为拉普拉斯或 Poisson 算子；同一图的不同嵌入可产生不同的物理波数与增长模态。

给定原初曲率谱 \(\mathcal P_\mathcal R(k)\)、转移函数 \(T(k)\) 和观测红移，线性物质功率谱可写为

$$
P_m(k,z)=D^2(z)\,P_{\rm prim}(k)\,T^2(k),
\qquad
\langle\delta(\mathbf k,z)\delta^*(\mathbf k',z)\rangle
=(2\pi)^3\delta^{(3)}(\mathbf k-\mathbf k')P_m(k,z).
\tag{242.3}
$$

各向异性、非高斯初始条件、重子反馈、暗能量扰动和测量窗口会改变该因子化；FIB 路径计数或层级频率不自动给出 \(P_{\rm prim}\)、\(T\) 或 \(D\)。在有限图上观察到的谱应先说明是图特征值谱、嵌入后的物理波数谱，还是窗口卷积后的估计量，三者不能互换。

若以平滑尺度 \(R\) 定义质量 \(M=(4\pi/3)\bar\rho_mR^3\)，密度方差为

$$
\sigma^2(M,z)=\int_0^\infty\frac{k^2\,\mathrm dk}{2\pi^2}
P_m(k,z)\,|W(kR)|^2,
\tag{242.4}
$$

某一外加球塌缩或有效阈值模型可给出晕质量函数的形式

$$
\frac{\mathrm dn}{\mathrm dM}
=\frac{\bar\rho_m}{M}f(\nu)\left|\frac{\mathrm d\ln\sigma^{-1}}{\mathrm dM}\right|,
\qquad
\nu=\frac{\delta_c}{\sigma(M,z)}.
\tag{242.5}
$$

这里的窗函数、临界阈值 \(\delta_c\)、无序系综、晕定义、并合时间和重子选择效应全属外加模型。不同的 FIB 合并规则可以承载同一 \(f(\nu)\)，同一 FIB 图也可在不同阈值或反馈规则下产生不同质量函数；因此从图的分支数不能直接推出暗物质晕的幂律或指数尾。

重子—光子流体的声速与外加背景共同给出声学尺度

$$
r_s(z_\ast)=\int_{z_\ast}^{\infty}\frac{c_s(z)}{H(z)}\,\mathrm dz,
\qquad
c_s^{-2}=3\left(1+\frac{3\rho_b}{4\rho_\gamma}\right),
\tag{242.6}
$$

若观测相关函数 \(\xi(r)\) 或功率谱出现 BAO 峰，其位置还要经过红移空间畸变、非线性展宽、重建算法和选择函数修正。FIB 上的一条固定路径长度只有在给定嵌入、标尺和声学动力学后才可能对应 \(r_s\)；组合图的层级周期本身不产生声波、声速或 BAO 峰。

弱引力透镜等观测把三维扰动投影到视线上，例如外加 Born 近似下的收敛场可写成

$$
\kappa(\boldsymbol\theta)=\int_0^{\chi_s}\mathrm d\chi\,
W_\kappa(\chi,\chi_s)\,\delta(\chi\boldsymbol\theta,\chi),
\tag{242.7}
$$

其中共动距离、源红移分布、权函数、光线偏折和仪器噪声均不由 FIB 决定。只观测投影场的二点相关，不能唯一分离初始谱、增长率、偏置、选择函数和噪声；同一图关系可以在不同嵌入和不同源分布下给出相同的投影统计。

若先对固定无序的 FIB 嵌入、初始场和观测窗口取大尺度极限，再对这些量平均，所得 quenched 统计一般不同于先平均再取极限的 annealed 统计。有限图的最大路径、边界和节点体积会造成红外截断、窗口泄漏与伪峰；周期边界、开放边界和光锥截面也会改变大尺度方差。须明确图族增长、物理体积增长、采样红移窗以及误差协方差，才能把有限样本读数外推到宇宙学极限。

因此，FIB 递归只提供邻接、候选合并和路径骨架；尺度因子、度规、引力与流体方程、初始谱、转移函数、暗物质和重子参数、嵌入、边界、观测投影及极限程序均须外加。密度扰动增长、暗物质晕质量函数、BAO 尺度、弱透镜相关和大尺度幂律等，都是指定这些宇宙学动力学与观测条件后的模型结论；它们不能由 FIB ATOM 递归单独推出。


## 243. FIB 网络/细胞复形上的外加活性向列相、取向缺陷与拓扑湍流统计

固定一族带面接缝的 FIB 细胞复形 \(C_j=(V_j,E_j,F_j)\)，记定向关联算子为 \(\partial_{1,j}:C_1\to C_0\)、\(\partial_{2,j}:C_2\to C_1\)，于是 \(\partial_{1,j}\partial_{2,j}=0\)。FIB ATOM 递归只给出顶点、边、面之间的组合关系、可行路径、闭合边界与递归层级；节点的连续位置、度量、面积、法向、时间尺度、取向场、流体、材料系数、噪声、边界和极限过程均须外加。不能把 FIB 的边方向直接当作向列分子的物理取向，也不能把面数或回路数直接当作缺陷数。

在外加二维嵌入 \(\iota_j:V_j\to\mathbb R^2\) 上，向列取向是头尾等价的线场

$$
n(x)\equiv-n(x),\qquad n=(\cos\theta,\sin\theta),qquad \theta\in\mathbb R/\pi\mathbb Z .
\tag{243.1}
$$

可用无迹对称张量表示局部取向和标量序参量：

$$
Q=S\left(nn^{\mathsf T}-\frac12I\right)
=\frac S2\begin{pmatrix}\cos 2\theta&\sin 2\theta\\
\sin 2\theta&-\cos 2\theta\end{pmatrix}.
\tag{243.2}
$$

把 \(Q\) 放在顶点、面或经外加插值放在连续区域，得到的是不同模型；FIB 复形本身不能选择这一放置规则。一个外加 Landau–de Gennes 型自由能可以写成

$$
F[Q]=\int_\Omega\left[\frac A2\operatorname{tr}(Q^2)
+\frac C4\bigl(\operatorname{tr}(Q^2)\bigr)^2
+\frac L2\,\partial_kQ_{\alpha\beta}\partial_kQ_{\alpha\beta}\right]{\rm d}^2x
+F_{\rm anch}+F_{\rm core},
\tag{243.3}
$$

其中 \(A,C,L\)、边界锚定和缺陷核正则化都是外加参数。图上离散能量例如为

$$
F_j^{\rm disc}(Q)=\frac12\sum_{e=(u,v)\in E_j}w_e\lVert Q_v-Q_u\rVert_F^2
+\sum_{c\in F_j}a_c f_b(Q_c),
\tag{243.4}
$$

但边权 \(w_e\)、胞面面积 \(a_c\)、邻接端点取值和 \(f_b\) 并不由递归关系确定。不同连续嵌入可以把同一 FIB 图实现为各向同性、各向异性或随机弹性介质。

活性向列的流场与取向场通常需要同时指定。一个不可压缩的外加模型可写为

$$
\rho(\partial_t+u\!\cdot\!\nabla)u
=-\nabla p+\eta\Delta u-\chi u+\nabla\!\cdot\sigma^{\rm el}
-\zeta\,\nabla\!\cdot Q+\xi_u,
\qquad \nabla\!\cdot u=0,
\tag{243.5}
$$

$$
(\partial_t+u\!\cdot\!\nabla)Q-\mathcal S(\nabla u,Q)
=\Gamma H+\xi_Q,
\qquad H=-\frac{\delta F}{\delta Q}.
\tag{243.6}
$$

黏度 \(\eta\)、基底摩擦 \(\chi\)、转动耗散 \(\Gamma\)、流动取向参数、被动弹性应力和活性应力系数 \(\zeta\) 均须外加；噪声 \(\xi_u,\xi_Q\) 的时空相关也须给定。式 (243.5)–(243.6) 的主变量是头尾对称的取向应力及其与流场的反馈，不能从第219节的极性主动粒子或标量密度方程自动得到。

取向缺陷必须在连续嵌入和线场的头尾等价性确定后才有定义。令 \(\varphi=2\theta\in\mathbb R/2\pi\mathbb Z\)，对不穿过缺陷核的定向边取

$$
\Delta_e\varphi=\operatorname{Arg}\exp\!\bigl({\rm i}(\varphi_v-\varphi_u)\bigr).
$$

若面 \(f\) 的边界按一致方向排列，离散绕数和向列电荷为

$$
w_f=\frac1{2\pi}\sum_{e\in\partial f}\Delta_e\varphi\in\mathbb Z,
\qquad q_f=\frac{w_f}{2}\in\tfrac12\mathbb Z .
\tag{243.7}
$$

在光滑插值和分支选择一致时，\(q_f=+1/2\) 或 \(-1/2\) 是常见的孤立缺陷；这使用的是 \(2\theta\) 的绕数，不能把普通 XY 向量场的整数涡旋电荷直接套用到向列场，也不能把 FIB 面的组合边界本身解释成物理奇点。

对没有孔洞且内部插值正则的区域 \(R\)，拓扑守恒可写成

$$
\sum_{f\subset R}q_f
=\frac1{2\pi}\oint_{\partial R}{\rm d}\theta
=\frac1{4\pi}\oint_{\partial R}{\rm d}\varphi,
\tag{243.8}
$$

但边界锚定、非平凡周期、被移除的缺陷核和复形孔洞会增加边界或全局绕数项。周期二维环面通常要求总电荷为零；开放边界时，总电荷由外加锚定条件决定。因此 FIB 闭合回路只能给出可计算的组合边界，不能单独推出净电荷约束或缺陷密度。

在给定核心结构、摩擦和活性应力后，可用缺陷位置 \(R_a\)、电荷 \(q_a\) 以及取向 \(p_a\) 写一个有效随机动力学例子：

$$
\dot R_a=u(R_a)+\mu_{q_a}F_a
+v_{q_a}^{\rm self}p_a+\sqrt{2D_{q_a}}\,\eta_a(t),
\qquad F_a=-\nabla_{R_a}F_{\rm def}.
\tag{243.9}
$$

在常见的各向同性近似下，\(+1/2\) 缺陷可有彗星轴并被活性应力推进，而 \(-1/2\) 缺陷的最低阶自推进项可能因三重对称性消失；改变边界、极性耦合、外场或近核耗散后该结论会改变。成对产生和湮灭的粗粒记账可写为

$$
\frac{{\rm d}}{{\rm d}t}\langle n_d\rangle
=2r_{\rm cr}-2r_{\rm an}-J_{\partial},
\tag{243.10}
$$

其中产生率、湮灭率和边界净通量都由外加材料、噪声、核半径、锚定和外部驱动决定，复形中的面数不能替代这些率。

对外加物理距离定义缺陷相关函数和电荷结构因子：

$$
g_{qq'}(r)=\frac{1}{2\pi r\,n_qn_{q'}}
\left\langle\sum_{a\ne b}{\mathbf 1}_{\{q_a=q\}}{\mathbf 1}_{\{q_b=q'\}}
\delta\bigl(r-|R_a-R_b|\bigr)\right\rangle,
\tag{243.11}
$$

$$
S_q(k)=\frac1{A_\Omega}
\left\langle\left|\sum_a q_a e^{-\mathrm i k\cdot R_a}\right|^2\right\rangle .
\tag{243.12}
$$

取向相关可用 \(C_2(r)=\langle\cos 2[\theta(x+r)-\theta(x)]\rangle\) 定义，这里的因子二再次体现向列而非极性序。流场能谱、缺陷间歇性和寿命尾部可能呈指数、拉伸指数、幂律或有限尺寸截断；没有共同的尺度分离和系综假设时，不能把某个谱指数称为 FIB 普适值。

若取一族复形的网格尺度 \(h_j\to0\)，必须同时给出嵌入、度量与面积收敛、边权缩放、缺陷核心半径与 \(h_j\) 的比例、活性系数缩放以及边界和初始条件。先对固定无序图求统计再取极限，与先做 annealed 平均再取极限一般不同。实际图像还要指定平滑尺度、分支解包、核心阈值、时间采样和边界裁剪；单帧取向图不能识别活性应力符号、缺陷产生率和噪声联合实现。

因此，FIB ATOM 递归在活性向列问题中只提供组合邻接、合法路径、面接缝、闭合边界和层级骨架；向列序参量、连续嵌入和度量、弹性、活性应力、流动取向、噪声、缺陷核心、边界锚定、观测协议以及连续或统计极限均须外加。\(\pm1/2\) 缺陷的电荷守恒、成对产生与湮灭、拓扑湍流的速度/取向谱、缺陷相关和寿命尾部，都是这些外加条件明确后的模型统计结论。

## 244. FIB 图族上的玻色—爱因斯坦凝聚、量子涡旋与 Kibble–Zurek 缺陷统计

本节研究外加玻色场在 FIB 图族上经过凝聚相变和有限速率淬火时的缺陷统计。设第 \(N\) 层 FIB 原子关系给出有限图 \(G_N=(V_N,E_N)\)，闭合路径选集记为外加的 \(\mathscr C_N\)。FIB 只提供组合对象及层级映射，不自动给出物理距离、嵌入维数、面元、相位、玻色子算符或时间演化。

给定外加边权 \(J_{uv}>0\)、规范边相位 \(A_{uv}=-A_{vu}\)、局部质量项 \(r_N(t)\) 和相互作用 \(g_N>0\)，在图上定义复场 \(\psi_u=\sqrt{\rho_u}e^{{\rm i}\theta_u}\) 的能量

$$
H_N(t,\psi)=\sum_{(u,v)\in E_N}J_{uv}
\left|\psi_v-e^{{\rm i}A_{uv}}\psi_u\right|^2
+\sum_{u\in V_N}\left(r_N(t)|\psi_u|^2+\frac{g_N}{2}|\psi_u|^4\right).
\tag{244.1}
$$

可以选择耗散随机动力学

$$
\partial_t\psi_u=-(\gamma+{\rm i})\frac{\partial H_N}{\partial\overline\psi_u}+\eta_u(t),
\tag{244.2}
$$

也可以选择守恒或近似哈密顿动力学；\(\gamma\)、噪声协方差及粒子数约束均属外加数据。令临界窗口内 \(\epsilon(t)=(r_N(t)-r_c)/r_0=t/\tau_Q\)，并假定外加连续极限具有

$$
\xi(\epsilon)\asymp \xi_0|\epsilon|^{-\nu},
\qquad
\tau_{\rm rel}(\epsilon)\asymp \tau_0|\epsilon|^{-\nu z},
\tag{244.3}
$$

其中 \(\nu,z>0\) 是动力学普适类的指数，不是 FIB 递归的结论。绝热—非绝热交界由

$$
\tau_{\rm rel}(\hat\epsilon)=\tau_Q|\hat\epsilon|
\tag{244.4}
$$

给出，从而

$$
|\hat\epsilon|\asymp \tau_Q^{-1/(1+\nu z)},
\qquad
\hat\xi\asymp \tau_Q^{\nu/(1+\nu z)}.
\tag{244.5}
$$

现在才引入图的外加几何。若物理球满足 \(\operatorname{Vol}_N(B(u,\ell))\asymp c(u)\ell^d\)，且 \(\hat\xi\) 位于该尺度区间，则在有限程混合模型中

$$
\mathbb E[n_{\rm def}]\asymp C_{\rm def}\hat\xi^{-d}
\asymp C_{\rm def}\tau_Q^{-d\nu/(1+\nu z)}.
\tag{244.6}
$$

若球增长是一般函数 \(V_u(\ell)\)，正确的组合表达应为

$$
\mathbb E N_{\rm def}\asymp\sum_{c\in\mathcal D_N}\kappa_c/V_c(\hat\xi),
\tag{244.7}
$$

而不是强行使用幂律；例如指数球增长会给出不同于幂律的淬火律。FIB 只给出 \(V_N,E_N\) 及递归关系，不能保证连续体积增长或混合条件。

对有定向的闭合 FIB 路径 \(C=(u_0,\ldots,u_m=u_0)\)，取

$$
\delta_{uv}=\operatorname{Arg}\!\left(e^{{\rm i}(\theta_v-\theta_u-A_{uv})}\right)\in(-\pi,\pi].
$$

在没有相位幅度零点且规范通量外加给定时，绕数为

$$
q_C=\frac1{2\pi}\left(\sum_{j=0}^{m-1}\delta_{u_ju_{j+1}}+\Phi_C\right)\in\mathbb Z,
\qquad
\Phi_C=\sum_{j=0}^{m-1}A_{u_ju_{j+1}}.
\tag{244.8}
$$

这里整数性、规范通量、路径是否代表物理小面以及零幅度核心的定义均来自外加相位场和嵌入。若某层 FIB 关系图是树或闭路选集为空，内部没有非平凡闭路，必须另加周期识别、面元嵌入或边界闭合后才可谈涡旋数。

淬火冻结时，相邻域的相位在各自相关域内近似一致，而域间相位由外加初态和噪声抽样。因此，对电荷 \(q\) 的期望数为

$$
\mathbb E N_q=\sum_{C\in\mathscr C_N}\Pr(q_C=q),
\tag{244.9}
$$

其概率由相位分布、规范通量和域间联合律决定，不能从 FIB 路径数单独推出。若变量在距离 \(O(\hat\xi)\) 后混合，则可能有 \(\mathbb E N_q/|V_N|\sim\kappa_q\hat\xi^{-d}\) 和相应中心极限定性，但这仍是外加随机动力学的结果。

若外加区域无边界、规范通量总和为零且相位全局单值，离散 Stokes 关系给出总涡旋电荷为零；开放边界或非零通量会改变这一约束。若 \(\hat\xi\) 大于图的物理直径，独立域数至多为常数；若小于边长或噪声相关长度，连续 Kibble–Zurek 近似失效。非均匀图必须使用局部冻结尺度和局部球体积。

若外加相变是二维 XY 型的 BKT 转变，相关长度可具有

$$
\xi(\epsilon)\asymp\xi_0\exp\!\left(\frac b{\sqrt{|\epsilon|}}\right),
\qquad
\tau_0\xi(\hat\epsilon)^z=\tau_Q|\hat\epsilon|,
\tag{244.10}
$$

此时冻结尺度含对数修正，不能照搬式 (244.6) 的幂指数。因而在给定临界标度、淬火协议、物理度量和相位随机过程后，FIB 只把邻接与闭路交给外加模型，外加动力学给出 \(\hat\xi\)，外加几何把它转为域体积，外加相位接缝再转为绕数统计；凝聚温度、临界指数、涡旋概率、中和律和普适类仍不由 FIB 单独决定。

## 245. FIB 网络上的外加 DNA/高分子拓扑、超螺旋松弛与随机构象统计

固定一族 FIB 图 \(G_j=(V_j,E_j)\)。顶点和边可承载一条有序 DNA 链的序列位置、接头或粗粒化路径；FIB 递归只给出组合支撑、邻接、路径和层级。把抽象路径变成有厚度的三维链还需要外加嵌入

$$
\iota_j:|G_j|\longrightarrow\mathbb R^3,
\qquad \mathbf r:[0,L_j]\longrightarrow\mathbb R^3,
\tag{245.1}
$$

以及边长、节点体积、链的闭合/开口边界、双链材料标架、自避让规则、溶剂、盐浓度、温度和外力。递归层数或路径长度本身不定义欧氏距离、曲率、扭转、交叉的上/下关系，也不决定一条闭合路径属于哪个结或链环拓扑扇区。

对闭合双链，令 \(\mathbf d_1,\mathbf d_2,\mathbf d_3=\mathbf t\) 为材料标架，\(\boldsymbol\Omega=(\Omega_1,\Omega_2,\Omega_3)\) 为 Darboux 应变。拓扑扇区可记为 \(\mathcal T=(K,Lk,\text{边界配对})\)，其中 \(K\) 是结型或链环型，\(Lk\) 是链接数。扭转数和弯曲绕数满足

$$
\operatorname{Tw}=\frac1{2\pi}\int_0^{L_j}\Omega_3(s)\,\mathrm ds,
\qquad
Lk=\operatorname{Tw}+\operatorname{Wr}(\mathbf r).
\tag{245.2}
$$

无链穿越的连续变形保持 \(K\) 与 \(Lk\)；固定 \(Lk\) 时扭转可以转化为弯曲绕数，因而机械超螺旋能够松弛而拓扑整数不变。端点可旋转的线性链没有给定的 \(Lk\)，必须另加端点约束或参考帧。FIB 抽象边不声明自交是否允许，故既不能推出拓扑整数守恒，也不能推出链穿越必然发生。

在给定拓扑扇区内，一个外加粗粒化弹性能量可以写成

$$
E_{j,\mathcal T}[\mathbf r,\boldsymbol\Omega]
=\frac12\int_0^{L_j}\mathbf u(s)^{\mathsf T}\mathsf K_j(s)\mathbf u(s)\,\mathrm ds
+E_{\rm ev}+E_{\rm el}+E_{\rm conf},
\qquad
\mathbf u=(\Omega_1,\Omega_2,\Omega_3-\Omega_0)^{\mathsf T}.
\tag{245.3}
$$

为显出扭转—弯曲耦合，可在各向同性近似下取

$$
E_{\rm tb}=\frac12\int_0^{L_j}
\left[A(\Omega_1^2+\Omega_2^2)+C\,\delta\Omega_3^2
+2G\,\Omega_2\delta\Omega_3\right]\mathrm ds,
\qquad \delta\Omega_3=\Omega_3-\Omega_0.
\tag{245.4}
$$

若 \(A,C>0\) 且 \(AC>G^2\)，消去弯曲变量得到有效扭转刚度 \(C_{\rm eff}=C-G^2/A\)。各向异性、非均匀序列、接触和有限边界会使这一消元变成非局部响应，不能把 \(C_{\rm eff}\) 当作 FIB 递归的普适常数。

在外加温度、轴向力 \(\mathbf F\) 和扭矩 \(\tau\) 下，固定扇区的配分函数为

$$
Z_{j,\mathcal T}(\beta,\mathbf F,\tau)
=\int_{\mathcal C_{j,\mathcal T}}\!\mathcal Dq\,
\exp\!\left[-\beta\left(E_{j,\mathcal T}[q]
-\mathbf F\!\cdot\!\mathbf R[q]-2\pi\tau Lk[q]\right)\right],
\qquad \beta=(k_{\rm B}T)^{-1}.
\tag{245.5}
$$

闭环固定 \(Lk\) 时应在单一拓扑扇区内取条件配分；允许链环交换或拓扑酶作用时，才可对不同 \(Lk\) 求和。超螺旋密度 \(\sigma=(Lk-Lk_0)/Lk_0\) 需要外加参考数 \(Lk_0\)。plectoneme、扭矩平台或屈曲转变取决于刚度、力、盐、链长、排斥势及扇区熵的联合竞争。

拓扑保持的过阻尼构象动力学可抽象为

$$
\mathrm dq_t=\left[-\mathsf M(q_t)\nabla E_{j,\mathcal T}(q_t)
+k_{\rm B}T\,\nabla\!\cdot\!\mathsf M(q_t)\right]\mathrm dt
+\sqrt{2k_{\rm B}T\mathsf M(q_t)}\,\mathrm dW_t,
\tag{245.6}
$$

其中摩擦/水动力迁移率、噪声解释和碰撞反射规则须外加；该扩散只能在同一 \(\mathcal T\) 内移动。若拓扑酶或受控断链允许链穿越，则扇区概率满足

$$
\dot p_{\mathcal T}=\sum_{\mathcal T'}\left(\lambda_{\mathcal T'\to\mathcal T}p_{\mathcal T'}
-\lambda_{\mathcal T\to\mathcal T'}p_{\mathcal T}\right).
\tag{245.7}
$$

在给定扭矩且满足详细平衡时，跃迁率还需满足

$$
\frac{\lambda_{\mathcal T\to\mathcal T'}}{\lambda_{\mathcal T'\to\mathcal T}}
=\exp\!\left[-\beta\left(\Delta E-2\pi\tau\Delta Lk\right)\right],
\tag{245.8}
$$

但势垒、催化位点、断链重接顺序和速率前因子均不由该比值或 FIB 图确定。扭矩释放后的松弛既可能是固定 \(Lk\) 下 \(\operatorname{Tw}\) 与 \(\operatorname{Wr}\) 的连续重分配，也可能是拓扑酶导致的离散跳跃。松弛时间的分布依赖水动力阻力、构象能垒、扇区速率、初始扇区及观测时间窗。

若 \(O(q)\) 是端到端距离、回转半径、延伸量、绕数、结型或接触数，则在外加扇区权重 \(w_{j,\mathcal T}\) 下

$$
\Pr_j\{O\in B\}
=\frac{\displaystyle\sum_{\mathcal T}w_{j,\mathcal T}
\int_{\mathcal C_{j,\mathcal T}}\!\mathbf 1_{\{O(q)\in B\}}
 e^{-\beta E_{j,\mathcal T}[q]}\,\mathcal Dq}
{\displaystyle\sum_{\mathcal T}w_{j,\mathcal T}Z_{j,\mathcal T}}.
\tag{245.9}
$$

同一 \(Lk\) 可对应多种 \(K\)、\(\operatorname{Tw}\) 与 \(\operatorname{Wr}\) 分配，同一延伸量也可来自不同结型和扭曲链。若只记录二维投影、总延伸和单个扭矩读数，隐藏的过/下关系与材料扭转会被观测映射合并；不同三维嵌入、刚度和扇区权重可以给出相同边缘分布而具有不同结型和链穿越率。

因此，FIB ATOM 递归在 DNA/高分子拓扑问题中只提供组合骨架、合法路径、接缝和层级候选；三维嵌入、闭合与端点边界、自避让和链穿越规则、材料刚度、扭转—弯曲耦合、温度、盐、力矩、水动力、拓扑酶速率、初态、系综、观测投影和极限次序均须外加。链接数守恒、扭转—绕数转换、超螺旋松弛时间、结型概率、plectoneme 统计和随机形态联合律，只有在这些外加条件明确后才是模型结论。

## 246. FIB 图上的外加非厄米波导、异常点与皮肤效应统计

固定一族有限 FIB 合法图 \(G_n=(V_n,E_n)\)，把顶点解释为波导、谐振腔或离散场幅的载体，把有向边解释为允许的耦合候选。FIB ATOM 递归只提供组合支撑、合法路径、分支与切口；边方向、复耦合、增益/损耗、频率、边界、无序系综、激励与探测协议均须外加。本节固定非厄米与非正规演化，不把拓扑指标或材料参数当作 FIB 量。

在节点基底中令波幅满足

$$
{\rm i}\,\dot\psi=H_n\psi,
\qquad
H_n=\sum_{(u\to v)\in E_n}t_{vu}|v\rangle\langle u|
+\sum_{v\in V_n}(\omega_v-{\rm i}\kappa_v)|v\rangle\langle v| .
\tag{246.1}
$$

其中 \(t_{vu}\) 可与反向耦合不同，\(\kappa_v\) 可表示损耗或增益；FIB 只限制哪些矩阵元可非零，不决定大小、相位、方向或统计相关。即使所有本征值实部都为负，\(H_n\) 也可能非正规，因而短时场强先放大再衰减。

右、左本征向量满足

$$
H_n|R_a\rangle=E_a|R_a\rangle,
\qquad
\langle L_a|H_n=E_a\langle L_a|,
\qquad
\langle L_a|R_b\rangle=\delta_{ab}.
\tag{246.2}
$$

右向量强度、左向量强度与双正交权重是三个不同的观测对象。谱点条件数 \(\kappa_a=\|L_a\|\,\|R_a\|\) 控制小扰动下的特征值敏感度；左、右向量近乎正交时，极小的频率、边界或无序误差也可造成巨大响应，普通谱隙不能替代伪谱检验。

沿一条长 FIB 路径，另加非互易耦合 \(t_R,t_L\) 和均匀现场 \(\omega\)，有

$$
H_{\rm path}=\sum_{j=1}^{m-1}
\left(t_R|v_{j+1}\rangle\langle v_j|+t_L|v_j\rangle\langle v_{j+1}|\right)
+\omega\sum_{j=1}^{m}|v_j\rangle\langle v_j|.
\tag{246.3}
$$

周期边界与开放边界分别给出

$$
E_{\rm PBC}(k)=\omega+t_R e^{-\mathrm i k}+t_L e^{\mathrm i k},
\tag{246.4}
$$

$$
E_{\rm OBC}(q)=\omega+2\sqrt{t_Rt_L}\cos q,
\qquad
\frac{R(q)_{j+1}}{R(q)_j}\sim\sqrt{\left|\frac{t_R}{t_L}\right|}.
\tag{246.5}
$$

当 \(|t_R|\ne|t_L|\) 时，右模态向一端集中，其理想化皮肤长度满足

$$
\xi_{\rm skin}^{-1}=\frac12\left|\log\left|\frac{t_R}{t_L}\right|\right|.
\tag{246.6}
$$

这个式子只属于该路径和边界条件；同一 FIB 路径取 \(t_R=t_L\) 时没有非互易皮肤漂移，取 \(|t_R|\ne|t_L|\) 时却有有限长度尺度。一般图上的皮肤效应必须改用边界质量、参与比和图列定义，不能把一条路径的波数当作一般 FIB 图的动量。

给定边界层 \(\partial_rV_n\)，可定义

$$
B^R_{n,r}(a)=\frac{\sum_{v\in\partial_rV_n}|R_a(v)|^2}{\sum_{v\in V_n}|R_a(v)|^2},
\qquad
P_2^R(a)=\frac{\sum_v|R_a(v)|^4}{(\sum_v|R_a(v)|^2)^2}.
\tag{246.7}
$$

只有当边界质量在图列极限中保持非消失并相对于体相基线稳定时，才可称为统计皮肤效应；若边界顶点比例趋于一，必须另作归一化。右强度、左强度和双正交权重的边界质量可能给出不同结论，实际读出取决于端口耦合。

若耦合随机，令允许边上的对数非互易比为 \(g_e=\log|t_e^+/t_e^-|\)，一条增长路径的平均漂移由 \(\overline g_\gamma=|\gamma|^{-1}\sum_{e\in\gamma}\sigma_e g_e\) 给出。随机传输矩阵的 Lyapunov 指数为

$$
\Lambda_i(E)=\lim_{m\to\infty}\frac1m
\log s_i\!\left(T_{e_m}(E)\cdots T_{e_1}(E)\right),
\tag{246.8}
$$

它依赖无序分布、方向相关、闭环通量和图列。先平均耦合再求指数一般不等于先求样本指数再平均；宽尾瓶颈可产生宽分布和有限尺寸截断。

异常点要求本征向量真正合并，而不只是本征值相等。对参数族 \(H_n(\lambda)\)，若二阶 Jordan 块存在，局部本征值可有

$$
E_\pm(\lambda)=E_*\pm c(\lambda-\lambda_*)^{1/2}+O(\lambda-\lambda_*),
\tag{246.9}
$$

\(c\)、参数路径、扰动方向和无序样本均外加。异常点附近的预解式

$$
\Psi_n(z)=\|(zI-H_n)^{-1}\|,
\qquad
\omega(H_n)=\lambda_{\max}\!\left(\frac{H_n+H_n^*}{2}\right)
\tag{246.10}
$$

控制瞬态放大；即使谱实部全负，数值域为正或预解式很大也可能出现有限时增益。端口读数可写为

$$
S_n(\nu)=D+C(\nu I-H_n)^{-1}B,
\tag{246.11}
$$

零点、相消、端口选择和频率依赖均由 \(B,C,D\) 外加决定。单端强度或单一频率谱通常不能区分真正的皮肤漂移、普通边界共振、局部损耗和端口滤波；固定无序样本先求散射再平均，与先平均矩阵或强度一般不同。

因此，FIB ATOM 递归在非厄米波导问题中只提供允许耦合的组合骨架、路径方向、分支和边界候选；非正规矩阵、左/右模态、增益损耗、异常点参数族、随机传输、端口、观测和极限均须外加。开闭边界谱差、皮肤长度、Lyapunov 尾、异常点出现率、瞬态放大和散射峰统计，只有在这些外加结构全部指定后才成立。

## 247. FIB 网络上的外加基因随机开关、表观遗传记忆与细胞命运首达统计

固定 FIB 图族 \(G_j=(V_j,E_j)\)。顶点可以被外加模型解释为调控位点、细胞区室、谱系标签或观测索引，边可以被解释为候选调控联系；这些解释不是 FIB ATOM 递归的内含语义。FIB 只提供组合支撑、可行路径、接缝和层级索引。基因身份、启动子结构、染色质状态、分子数、时间尺度、调控方向和强度、细胞分裂规则、噪声以及观测通道均须另行给定。

对每个顶点引入转录开关 \(X_v(t)\in\{0,1\}\) 和较慢的表观状态 \(E_v(t)\in\{0,1,\ldots,r_v\}\)。令 \(z=(x,e)\) 为全体状态，外加连续时间跳变核为 \(q_j(z,z')\)。若只允许 FIB 边支持的局部调控，可写成

$$
q_j(z,z')=\sum_{v\in V_j}q_{v,j}^{x}(z)\mathbf 1_{\{z'=z^{v,x}\}}
+\sum_{v\in V_j}q_{v,j}^{e}(z)\mathbf 1_{\{z'=z^{v,e}\}},
\tag{247.1}
$$

一个示例参数化是

$$
q_{v,j}^{x,+}(z)=a_{v,j}^{+}(e_v,t)\exp\!\left(\sum_{u:(u,v)\in E_j}R_{uv,j}x_u\right),
\qquad
q_{v,j}^{x,-}(z)=a_{v,j}^{-}(e_v,t)\exp\!\left(-\sum_{u:(u,v)\in E_j}\widetilde R_{uv,j}x_u\right).
\tag{247.2}
$$

调控矩阵的符号、稀疏性、时变性、非局部作用和多状态跃迁不能由 FIB 边自动确定。状态概率向量满足外加主方程

$$
\frac{{\rm d}}{{\rm d}t}\pi_j(t)=\pi_j(t)Q_j(t),
\qquad
(Q_j)_{zz'}=q_j(z,z')\ (z\ne z'),
\qquad
(Q_j)_{zz}=-\sum_{z'\ne z}q_j(z,z').
\tag{247.3}
$$

若核恒定且有限状态不可约，稳态由 \(\pi_j^*Q_j=0\) 及归一化确定。单个快速开关在固定表观状态下的平衡活跃率和相关时间为

$$
\bar x_v(e)=\frac{k_{v,e}^{+}}{k_{v,e}^{+}+k_{v,e}^{-}},
\qquad
\tau_{v,e}=\bigl(k_{v,e}^{+}+k_{v,e}^{-}\bigr)^{-1}.
\tag{247.4}
$$

若表观状态慢于转录开关，观测到的自相关是条件相关的混合，常含

$$
C_v(s)\simeq A_{v,1}e^{-s/\tau_{v,1}}+A_{v,2}e^{-s/\tau_{v,2}}.
\tag{247.5}
$$

随机表观环境、分裂稀释和速率异质性可把有限指数混合变成长尾或非指数记忆；从稳态均值不能反推出开关速率。

把外加细胞命运定义为状态空间中的吸收集合 \(A_{j,1},\ldots,A_{j,m}\)，命运 \(f\) 的首达时间和首达概率为

$$
T_{j,f}=\inf\{t\ge0:Z_j(t)\in A_{j,f}\},
\qquad
h_{j,f}(z)=\Pr_z\{T_{j,f}<T_{j,g}\ \forall g\ne f\}.
\tag{247.6}
$$

在时间齐次有限链且最终吸收时，令 \(Q_{TT}\) 为暂态子矩阵、\(b_f=Q_{T A_{j,f}}\mathbf 1\)，则

$$
-Q_{TT}h_{j,f}=b_f,
\qquad
-Q_{TT}m_j=\mathbf 1,
\tag{247.7}
$$

其中 \(m_j\) 是吸收时间均值。时间依赖调控、外部脉冲或非马尔可夫表观记忆时，首达分布可能多峰、长尾或出现等待平台。所谓临界开关只有在参数族、吸收集合和观测窗口固定后才有定义。

若每个细胞的有效拷贝数为 \(N\)，噪声尺度为 \(N^{-1/2}\)，外加扩散近似可给出稀有命运跃迁律

$$
\Pr(T_{j,f}\le t)\asymp\exp[-N I_{j,f}(t)],
\tag{247.8}
$$

作用量由漂移、扩散张量、脉冲协议和吸收边界共同决定；FIB 路径长度、分支数或递归深度不提供该作用量。

细胞群体异质性可用细胞参数 \(\theta_\ell\) 表示。若细胞条件独立而 \(\theta_\ell\) 独立同分布，命运计数 \(N_f\) 满足

$$
\mathbb E[N_f]=M\bar p_f,
\qquad
\operatorname{Var}(N_f)=M\bar p_f(1-\bar p_f)
+M(M-1)\operatorname{Var}_{\theta}[p_f(\theta)],
\tag{247.9}
$$

第二项是参数异质性导致的过度离散；共享环境、母细胞状态或旁分泌输入还会加入联合协方差。姐妹细胞继承相关表观状态时，继承核直接决定姐妹命运相关；这些量不能由亲缘标签或 FIB 路径关系单独给出。固定环境后再对参数平均属于淬火统计，把参数并入快速转移核属于退火统计，二者在长记忆或稀有事件下通常不同。

荧光报告、单细胞测序和表观标记实验只给出隐藏状态的投影。例如带延迟和积分的观测可写为

$$
Y_a(t)=\sum_{v\in V_j}H_{av}\int_0^\infty D_v(s)X_v(t-s)\,\mathrm ds+\varepsilon_a(t),
\tag{247.10}
$$

其中 \(H\) 是报告通道，\(D_v\) 是成熟、降解和曝光响应核，\(\varepsilon\) 是测量噪声。只用稳态均值、单次命运比例或终点测序，无法唯一区分快速开关、慢表观记忆、细胞异质性和检测延迟；需要时间分辨的谱系追踪、脉冲—追踪、同时测量表观标记或登记的调控干预。

因此，FIB ATOM 递归在基因调控问题中只提供候选调控关系、组合路径、接缝和层级骨架；开关速率、调控符号、染色质写入/擦除、分裂继承、参数分布、噪声联合实现、命运吸收集合、首达极限和观测响应均须外加。开关稳态、记忆时间、细胞命运比例、首达时间尾部、姐妹相关和群体过度离散，只有在这些生物动力学与观测条件明确后才是条件统计规律。


## 248. FIB 复形上的外加晶体位错、塑性流动与雪崩统计

固定一族由 FIB ATOM 递归得到的有限复形 \(K_j\)，其链群和边界算子记为

$$
C_2(K_j)\xrightarrow{\partial_2}C_1(K_j)\xrightarrow{\partial_1}C_0(K_j),
\qquad \partial_1\partial_2=0 .
\tag{248.1}
$$

顶点、边和面可以被外加模型解释为晶格节点、候选滑移段和面元，但 FIB 只给组合邻接、取向、接缝和层级。把复形嵌入物理空间需要另给 \(\iota_j:|K_j|\to\mathbb R^d\)、边长和面面积；晶格平移群、晶格间距、材料标架、时间、温度、载荷和边界也都不由递归关系决定。图上有闭路不自动等于物理位错环，图距离也不自动等于位错线长度。

对每个外加滑移系 \(\mu\)，给定 Burgers 向量 \(b_\mu\)、滑移面法向 \(n_\mu\) 和方向 \(s_\mu\)。把有向位错段编码为整数一链 \(J_\mu\in C_1(K_j;\mathbb Z)\)。没有体内源汇时必须有

$$
\partial_1J_\mu=0,
\tag{248.2}
$$

即位错线在内部组成闭环或非平凡一同调类；表面逸出、位错源、沉淀钉扎或外加断链可在右端加入源项。FIB 的边界算子能表达这种组合守恒，却不提供源项是否存在、能量代价或边界吸收律。位错反应还需外加 Burgers 守恒；攀移需要空位或间隙原子通量，不能从一条图路径推出。

若每条允许滑移边带有滑移量 \(\gamma_{\mu,e}\)，外加塑性畸变可写为

$$
\beta^p_e=\sum_\mu\gamma_{\mu,e}\,b_\mu\otimes n_\mu,
\qquad
\alpha_f=\sum_{e\in\partial_2f}\varepsilon_{fe}\,\beta^p_e .
\tag{248.3}
$$

只有给定物理嵌入、单位和材料标架后，\(\alpha_f\) 才能解释为位错密度张量。不同 Burgers 格子或同一复形的不同嵌入，可以给出相同 \(J_\mu\) 而不同的位错密度、环量与拓扑扇区。

应力场必须由外加本构和边界求出。在线性小变形近似下，连续模型满足

$$
\sigma=C:(\nabla u-\beta^p),
\qquad \nabla\!\cdot\sigma=0,
\tag{248.4}
$$

而位错线方向 \(\xi_\ell\) 上的 Peach–Koehler 力和滑移分解为

$$
F_\ell=(\sigma b_\ell)\times\xi_\ell,
\qquad
\tau_\ell=s_\ell\cdot\sigma n_\ell .
\tag{248.5}
$$

弹性张量、泊松比、各向异性、核心能、长程 Green 核和边界柔度均不由 FIB 给出；同一邻接在不同嵌入下可把同一路径变成易滑移或受阻方向。

把滑移幅度作为坐标后，外加应力重分配可写成

$$
\tau_\ell=\tau_\ell^{\rm ext}+\sum_mG_{\ell m}\,\Delta\gamma_m,
\qquad
\dot\gamma^p=\sum_\ell\rho_\ell b_\ell v_\ell .
\tag{248.6}
$$

核 \(G\) 由弹性、边界和核心正则化决定，可含长程、各向异性和非对称像；FIB 局部接缝不决定它的衰减、符号或是否存在远程耦合。

热激活滑移可用

$$
 r_\ell^{\pm}=\nu_\ell\exp[-\beta\Delta G_\ell^{\pm}(\tau_\ell,\tau_{c,\ell})]
\tag{248.7}
$$

表示，势垒、尝试频率、Peierls 阈值、热浴解释、交滑移和攀移规则都须外加。固定障碍场后演化再平均属于淬火统计，把障碍更新并入跃迁核则是退火统计，二者在稀有事件和长时间极限下通常不同。

在准静态驱动中，一次内部连锁定义为雪崩 \(\mathcal A\)，可取

$$
S(\mathcal A)=\sum_{\ell\in\mathcal A}w_\ell|\Delta\gamma_\ell|,
\qquad
T(\mathcal A)=t_{\rm end}-t_{\rm start},
\qquad
\Delta\Sigma=\Sigma_{\rm before}-\Sigma_{\rm after} .
\tag{248.8}
$$

权重、事件合并规则和时间窗必须预先给定。若外加无序和弹性核使系统接近临界流动点，才可写候选有限尺寸形式

$$
P(S\mid L)=S^{-\tau}f\!\left(S/S_c(L)\right),
\qquad S_c(L)\asymp L^{d_f},
\qquad T_c(L)\asymp L^z .
\tag{248.9}
$$

指数 \(\tau,d_f,z\) 取决于应力核、空间维数、无序相关、加载控制、边界和热噪声；它们不是 FIB 递归的普适输出。有限复形只能产生有限截止，单一双对数直线不能证明无限系统的临界幂律。

闭环位错可在不改变总 Burgers 荷的条件下收缩、扩张或湮灭；非平凡同调类、表面钉扎或禁止交滑移可能阻止局部湮灭，使应力释放转为跨层级事件。相同边数和局部度数的两个图列，若一个有不可收缩环而另一个是树，可能有完全不同的屈服和雪崩尾部；相同复形在不同晶格、弹性和障碍分布下也可从平滑流动变成宽尾间歇流。

声发射、局部位移、晶体取向或总应力只是潜在雪崩的观测投影：

$$
Y_a=Q_a\bigl(S,T,\Delta\Sigma,\{\Delta\gamma_\ell\},\alpha\bigr)+\eta_a .
\tag{248.10}
$$

传感器带宽、阈值、空间卷积和时间采样会改变估计的 \(\tau\)。本节的雪崩来自位错滑移、位错反应和弹性应力重分配，不把断键、裂纹开口或接触网络刚化当作同一机制。

因此，FIB ATOM 递归在晶体塑性问题中只提供复形边界关系、候选滑移路径、环路和层级骨架；Burgers 格子、三维嵌入、滑移系、弹性本构和长程应力核、核心能、位错源汇、障碍无序、温度、加载协议、边界、事件定义、观测投影以及图列极限均须外加。屈服应力、塑性流动曲线、位错密度演化和雪崩分布都是指定外加模型后的条件统计。

## 249. FIB 细胞复形上的外加脂质膜曲率、融合颈、拓扑重连与相分离斑块统计

固定由 FIB ATOM 递归关系给出的有限二维细胞复形 \(K_j=(V_j,E_j,F_j;\partial_1,\partial_2)\)。把几何实现、膜的材料参数和时间演化另行记为外加数据：令 \(X_t:|K_j|\to\mathbb R^3\) 是分片光滑嵌入，\(\Sigma_t=X_t(|K_j|)\) 为膜中面，\(g_t,H_t,K_{G,t}\) 分别为诱导度量、平均曲率和高斯曲率。FIB 给出面、边、顶点的邻接和候选局部接缝；它本身不指定嵌入、长度、面积、法向、曲率或膜的物理时间。

令 \(\mathcal P_t=\{P_{t,i}\}\) 为膜上的相分离斑块，\(\Gamma_t=\bigcup_i\partial P_{t,i}\) 为相界线。斑块面积、边界长度和内部拓扑为

$$
A_{t,i}=\int_{P_{t,i}}{\rm d}A_t,
\qquad
L_{t,i}=\operatorname{length}_{g_t}(\partial P_{t,i}),
\qquad
\chi_{t,i}=\chi(P_{t,i}).
\tag{249.1}
$$

一个给定几何和材料模型下的局部 Helfrich—线张力能量可写成

$$
\begin{aligned}
\mathcal E_t[\Sigma,\mathcal P]
&=\int_{\Sigma_t}\left[\frac{\kappa(\phi)}2(2H-C_0(\phi))^2
+\bar\kappa(\phi)K_G+\sigma\right]{\rm d}A_t\\
&\quad+\sum_{\Gamma\subset\Gamma_t}\lambda_\Gamma\operatorname{length}_{g_t}(\Gamma)
+E_{\rm adh}+E_{\rm constraint} .
\end{aligned}
\tag{249.2}
$$

弯曲模量、Gaussian 模量、自发曲率、膜张力、线张力、黏附、面积和体积约束均为外加量。即便闭合光滑曲面满足 Gauss–Bonnet 关系，存在边界、孔洞、相界折线或空间变化的 \(\bar\kappa\) 时也会出现额外边界与材料界面贡献，不能仅用一个整数替代。

给定嵌入后可在 FIB 面上定义曲率测度，例如

$$
\mu_H(B)=\frac1{\sum_fA_f}\sum_{f\in F_j}A_f\mathbf 1_{\{H_f\in B\}},
\qquad
\mu_K(B)=\frac1{\sum_fA_f}\sum_{f\in F_j}A_f\mathbf 1_{\{K_{G,f}\in B\}} .
\tag{249.3}
$$

只给 \(K_j\) 时，连 \(A_f,H_f,L_{t,i}\) 都没有定义；这些量只能在指定嵌入和度量后读取。拓扑重连需另给允许的手术映射：FIB 面—边接缝可以枚举候选边界对，但两个边界能否在三维中相遇并发生膜融合是外加几何和化学判据。

对局部候选手术 \(r\)，从膜面删去两个小圆盘并插入半径为 \(a\)、长度为 \(\ell_r\) 的融合颈，可有反应坐标能量

$$
U_r(a)=\sigma A_r^{\rm new}(a)+\lambda_rL_r(a)
+\frac{\kappa_r}{2}\int_{N_r(a)}(2H-C_{0,r})^2{\rm d}A
+\Delta E_{G,r}+U_{{\rm adh},r}(a).
\tag{249.4}
$$

系数和颈形状随边界条件改变；它只显示曲率、张力、线张力和黏附如何共同进入障碍，并非由 FIB 递归推出的定律。给定外加阻尼、尝试频率和温度，Kramers 型速率可写成

$$
k_r=\nu_r\exp[-\beta\Delta U_r^\ddagger],
\qquad
\Delta U_r^\ddagger=\inf_{a(\cdot)}\left[\max_sU_r(a(s))-U_r(a_0)\right].
\tag{249.5}
$$

若候选手术条件独立，融合时间尾为

$$
\Pr(T_{\rm fus}>t)=\exp\!\left[-\int_0^t\sum_rk_r(s){\rm d}s\right],
\tag{249.6}
$$

相互作用、面积耗散、颈记忆或非马尔可夫噪声会改变此式，FIB 只给出候选 \(r\) 的组合索引，不给出速率或历史核。

若每次手术后仍得到可定向闭合复形，Euler 示性数为 \(\chi=|V|-|E|+|F|\)，并可在无边界、连通、可定向时写成 \(\chi=2-2g\)。融合、裂变、打孔和孔闭合分别给出不同的 \(\Delta\chi\)，斑块数也可能随颈的连通性改变。给定外加跳变生成元 \(Q\)，拓扑类型和斑块数的联合分布由

$$
\partial_tp_t(\mathbf n)=\sum_r\left[p_t(\mathbf n-\nu_r)q_r(\mathbf n-\nu_r)-p_t(\mathbf n)q_r(\mathbf n)\right]
\tag{249.7}
$$

决定；速率 \(q_r\) 是材料、几何和噪声指定后的量。单一手术计数的 Poisson 生成函数只在独立非齐次假设下成立。

存在直接的观测不可识别性。完整参数 \(\vartheta=(X_t,g_t,\kappa,\bar\kappa,C_0,\sigma,\lambda,T,\nu,q,\text{边界与观测投影})\) 的不同取值可以保留相同 FIB 面—边—顶点关联与斑块计数，却给出不同曲率、融合时间和拓扑跳变统计。例如同一可平面嵌入的复形可以实现为平面片或圆柱片，保持离散边长与面积读数而具有不同平均曲率；改变 \(C_0,\kappa\)、黏附势或颈阻尼即可改变融合率。仅看斑块边界图也无法判定局部手术是膜融合、孔闭合还是两相界线的暂时接触。

因此，本节的条件链是：FIB 提供细胞复形的组合邻接、路径和候选接缝；外加嵌入与度量提供面积、法向和曲率；Helfrich 模量、自发曲率、张力、线张力、黏附和约束提供能量；温度、阻尼、噪声和手术核提供融合颈动力学；初始测度、边界和观测映射提供曲率、拓扑及斑块统计。没有这组外加结构，不能从 FIB 单独推出膜曲率分布、融合时间尾、拓扑重连频率或相分离斑块联合律。

## 250. FIB 网络上的外加离子通道随机门控、膜电噪声与放电首达统计

固定一族有限 FIB 合法图 \(G_j=(V_j,E_j)\)。顶点可在外加模型中解释为膜片段、轴突区室或离子通道簇，边可解释为轴向电耦合候选；FIB ATOM 递归只提供组合支撑、可行路径、分支、接缝与层级索引。电容、膜面积、离子种类、反转电位、通道数、门控速率、电压嵌入、外加电流、空间耦合、温度、边界、初态和探测器均须另行给定。本节研究局部门控随机性和有限区室首达事件，不把第231节的整体脉冲神经元网络动力学当作递归内含量。

对 \(v\in V_j\) 及通道类型 \(c\)，令单个通道门状态为 \(S_{v,c,k}(t)\in\{0,\ldots,m_c\}\)。在给定膜电压 \(V\) 时，门状态是外加连续时间 Markov 链，生成矩阵满足

$$
Q_{v,c}(V)=(q^c_{rs}(V)),
\qquad q^c_{rs}(V)\ge0\ (r\ne s),
\qquad q^c_{rr}(V)=-\sum_{s\ne r}q^c_{rs}(V).
\tag{250.1}
$$

FIB 边只限制哪些门控变量可以通过外加耦合共同进入速率；它不决定生成矩阵的非零位置、数值或是否满足详细平衡。二态门 \(C\rightleftarrows O\) 的开闭速率为 \(\alpha_c(V),\beta_c(V)\) 时，

$$
p_{\infty,c}(V)=\frac{\alpha_c(V)}{\alpha_c(V)+\beta_c(V)},
\qquad
\tau_{g,c}(V)=\bigl(\alpha_c(V)+\beta_c(V)\bigr)^{-1},
\tag{250.2}
$$

而 \(N_{v,c}\) 个独立门的开态分数协方差为

$$
\operatorname{Cov}(X_{v,c}(t),X_{v,c}(0))
=\frac{p_{\infty,c}(1-p_{\infty,c})}{N_{v,c}}e^{-|t|/\tau_{g,c}}.
\tag{250.3}
$$

同一稳态开态比例可由共同缩放的开闭速率产生，但时间尺度和噪声谱不同；多态门则给出多个衰减模态。

令外加区室电压满足

$$
C_v\,dV_v=\Big[I_v^{\rm ext}(t)-g_{L,v}(V_v-E_L)
-\sum_c\bar g_{v,c}X_{v,c}(t)(V_v-E_{v,c})
+\sum_{u:(u,v)\in E_j}G_{uv}(V_u-V_v)\Big]dt
+dJ_v(t)+\sigma_v(V)\,dW_v(t).
\tag{250.4}
$$

电容、电导、反转电位、轴向耦合、事件跳跃和连续噪声均为外加量；把门状态替换成均值只是大通道数或时间尺度分离下的附加近似。若离子事件时刻为 \(T_{v,r}\)、幅度为 \(A_{v,r}\)，复合 Poisson 电流可写成

$$
J_v(t)=\sum_rA_{v,r}\delta(t-T_{v,r}),
\qquad
\mathbb E\,dJ_v=\lambda_v\mathbb E[A_v]dt,
\qquad
\operatorname{cum}_k(dJ_v)=\lambda_v\mathbb E[A_v^k]dt.
\tag{250.5}
$$

膜电容把单事件卷积为冲激响应；只保留二阶矩时，高斯噪声与复合 Poisson 噪声可能给出相同低阶读数，却在偏度、峰度和稀有首达事件上不同。

定义阈值 \(\Theta_v\) 与安全边界 \(L_v<\Theta_v\)，放电首达时间为

$$
T_{j,v}=\inf\{t\ge0:V_v(t)\ge\Theta_v\},
\qquad
\tau_{j,v}=\inf\{t\ge0:V_v(t)\notin(L_v,\Theta_v)\}.
\tag{250.6}
$$

联合状态 \((V,S)\) 的生成元包含漂移、扩散、门控跳变和 shot-noise 跳跃：

$$
\mathcal Lf=b_s(V)\partial_Vf+\frac12a_s(V)\partial_V^2f
+\sum_{s'}Q_{ss'}(V)[f(V,s')-f(V,s)]
+\lambda(V)\int[f(V+y,s)-f(V,s)]\mu_V(dy).
\tag{250.7}
$$

首达概率满足 \(\mathcal Lh=0\)，有限均值满足 \(\mathcal Lm=-1\)，边界条件由阈值、重置和竞争命运另行给定。门控速率、事件强度和电压反馈通过整个联合边值问题进入首达分布，而非只通过平均膜电流进入。

在外加亚阈值周期电流下，若有效势垒为 \(\Delta U(A)\)，扩散近似的稀有逃逸率可写成

$$
r(D,A)\simeq r_0(A)\exp[-\Delta U(A)/D].
\tag{250.8}
$$

随机共振候选峰可由 \(r(D_*)\pi/\omega\asymp1\) 定义。改变通道数会改变门控噪声幅度，改变开闭速率会改变噪声颜色，改变事件幅度分布会改变非高斯尾部；没有周期协议、噪声参数和响应定义，就没有唯一的最佳噪声。

若条件风险率近似恒定为 \(r\)，则 \(\Pr(T>t)\simeq e^{-rt}\)。状态依赖门控、阈值反馈和慢门会使风险率随历史变化；若区室参数 \(\vartheta\) 随机，边缘化后

$$
\Pr(T>t)=\int e^{-r(\vartheta)t}\,\rho(d\vartheta)
\tag{250.9}
$$

可产生多指数或长时间近似幂律尾。混合测度是外加的淬火/退火选择，不能误认成 FIB 递归的普适幂律。

实际电生理读数是隐藏电压与门状态的投影：

$$
Y_a(t)=\sum_{v\in V_j}H_{av}\int_0^\infty D_v(s)V_v(t-s)\,ds+\eta_a(t).
\tag{250.10}
$$

端口矩阵、响应核、阈值滞回、采样间隔和事件检测延迟均会改变读到的首达时间。相同的稳态平均电流或单点功率谱可由快门控小通道数、慢门控大通道数或不同 shot-noise 幅度实现，因而不能仅凭投影读数识别门控机制。

因此，FIB ATOM 递归在离子通道问题中只提供可组合的膜区室、允许耦合、路径、接缝和层级骨架；门状态空间、Markov 生成矩阵、膜电容与电导、反转电位、噪声联合实现、周期驱动、阈值/重置边界、首达极限和观测投影均须外加。开态分布、门控相关时间、shot-noise 高阶累积量、随机共振峰、放电首达时间及其尾部，只有在这些条件明确后才是模型统计结论。


## 251. FIB 网络/复形上的外加电池离子沉积、枝晶形貌与短路失效统计

固定由 FIB ATOM 递归给出的有限复形

$$
C_2(K_j)\xrightarrow{\partial_2}C_1(K_j)\xrightarrow{\partial_1}C_0(K_j),
\qquad \partial_1\partial_2=0,
\tag{251.1}
$$

并指定代表负极、正极和隔膜的边界子集 \(B_-,B_+,B_s\)。复形的面、边和顶点可以在外加模型中解释为电极—电解质界面片、候选成核接缝、枝晶可占据单元或电流收集节点；FIB 只提供组合邻接、定向路径、边界接缝和层级索引。物理嵌入、长度、面积、法向、孔隙体积、晶面取向、金属体积分数、时间单位、温度、初始界面和电池边界均须另加。图上的一条路径不自动是三维中的枝晶，图的度数也不自动是尖端曲率或电场增强因子。

本节只研究给定界面附近的沉积、形貌失稳、随机成核和贯通失效；体相浓度与电势若需要，视为由外加边界值或其他模型先行给出，不重复第197节的体输运。令 \(\eta_e(t)\) 为候选界面单元的有效过电位，可写为

$$
\eta_e=\phi_{s,e}-\phi_{\ell,e}-E_{{\rm eq},e}(c_e,T)
-\frac{\Omega_e}{zF}\bigl(\gamma_e\kappa_e+\sigma_{n,e}\bigr)-\eta_e^{\rm ohm} .
\tag{251.2}
$$

若局部反应服从给定的电荷转移律，净沉积通量为

$$
J_e^{\rm dep}=\frac{j_{0,e}}{zF}\left[
\exp\!\left(\frac{\alpha_{a,e}zF\eta_e}{RT}\right)
-\exp\!\left(-\frac{\alpha_{c,e}zF\eta_e}{RT}\right)\right].
\tag{251.3}
$$

交换电流、转移系数、活度、温度、界面能、应力耦合和膜层降落都不是 FIB 内容。尖端若因外加几何和电场边值获得较大过电位，可能比平坦段更快沉积；但尖端及其场增强本身不能从组合路径推出。

给定有效化学驱动力 \(\Delta\mu_e=zF\eta_e\)，随机成核可由条件强度表示为

$$
\lambda_e(t)=a_e\nu_e\exp\!\left[-\beta\Delta G_{*,e}
(\Delta\mu_e,\gamma_e,\theta_e,\sigma_{n,e})\right].
\tag{251.4}
$$

在各向同性三维毛细近似下，一个仅供说明的势垒为

$$
\Delta G_{*,e}=\frac{16\pi\gamma_e^3}{3(\Delta\mu_e)^2},
\tag{251.5}
$$

有限晶面、应力、SEI 缺陷、二维成核或离散单元会改变系数和幂次。固定缺陷场、温度场和局部电势后，这可以是条件 Poisson 过程；把这些场视为随机慢变量后，成核是 Cox 过程，计数协方差包含强度场的联合协方差。相同的平均成核率可以对应独立成核、空间簇发或长记忆成核。

界面形貌的尖端不稳定需要在外加嵌入上定义扰动。对局部坐标写

$$
h(x,t)=h_0(t)+\sum_q a_q(t)e^{{\rm i}qx},
\qquad
\dot a_q=\omega(q;\eta,D,\gamma,k_s,\ldots)a_q+\xi_q(t).
\tag{251.6}
$$

只有当某个波数带满足 \(\operatorname{Re}\omega(q)>0\) 时扰动才放大；最强模态、尖端半径和速度由各向异性界面能、动力学、供给、应力和边界联合决定。图上离散化可写成

$$
\dot{\mathbf h}=\mathsf A(\eta,\vartheta)\mathbf h
-\mathsf\Gamma(\vartheta)L^{(w)}\mathbf h+\boldsymbol\xi,
\tag{251.7}
$$

但加权图拉普拉斯、系数矩阵和谱均依赖外加权重、嵌入、晶面和边界；相同组合复形可嵌入成平滑平板而稳定，也可嵌入成尖角电极而进入枝晶失稳。

令 \(\mathcal D_t\) 表示已沉积单元，给定附着、脱附、表面扩散和溶解规则，边界单元的跳变率可写为

$$
r_e^+=k_e^+g_e(\eta_e,\kappa_e,\sigma_{n,e},c_e,\mathcal N_e(\mathcal D_t)),
\qquad
r_e^-=k_e^-h_e(\eta_e,\kappa_e,\sigma_{n,e},\mathcal N_e(\mathcal D_t)).
\tag{251.8}
$$

这里 \(\mathcal N_e\) 只表示由 FIB 邻接筛出的候选邻域；函数、晶向依赖和邻居协同性是外加的。由此可以产生紧致层、枝状团簇或反复溶解—再沉积。可记录质量、最大枝高和分支数

$$
M_t=\sum_{v\in\mathcal D_t}w_v,
\qquad
H_t=\max_{v\in\mathcal D_t}d(v,B_-),
\qquad
B_t=\#\{e\in\partial\mathcal D_t:r_e^+>r_e^-\},
\tag{251.9}
$$

其中权重、物理距离和事件阈值全部外加；有限复形的截断不能证明无限尺度的普适分形指数。

枝晶贯通首先是组合事件：

$$
\tau_{\rm span}=\inf\{t:\exists\ \pi\subseteq\mathcal D_t,
\ \pi:B_-\rightsquigarrow B_+\}.
\tag{251.10}
$$

但几何相遇不等于电气短路。对候选路径 \(\pi\)，外加电阻和 SEI 接触给出

$$
R_\pi(t)=\sum_{e\in\pi}\frac{\rho_e\ell_e}{A_e}+R_{{\rm SEI},\pi}(t),
\qquad
\mathcal F_t=\{\exists\pi:B_-\rightsquigarrow B_+,\ R_\pi\le R_{\rm crit},\ I_\pi\ge I_{\rm crit}\},
\tag{251.11}
$$

真正的短路时间是 \(\tau_{\rm sc}=\inf\{t:\mathcal F_t\text{ 发生}\}\)。长度、面积、电阻率、保护膜、阈值以及接触是否导通都由外加材料和电路决定；同一路径可以只产生几何贯通，也可以直接触发电流跃迁。

在有 \(N\) 个电芯或循环时，令 \(T_m=\tau_{\rm sc}^{(m)}\)，共享参数为 \(\Theta\)。条件独立时

$$
\Pr(T_{\min}^{(N)}>t\mid\Theta)=\prod_{m=1}^NS_m(t\mid\Theta),
\qquad
\Pr(T_{\min}^{(N)}>t)=\mathbb E\left[S(t\mid\Theta)^N\right],
\tag{251.12}
$$

一般不等于 \((\mathbb ES(t\mid\Theta))^N\)。共同温度、充电协议、压力或批次缺陷会改变最小首失效尾部；枝高、分支质量和局部电流的极值类也不能仅凭一张 FIB 图确定。

显微图、原位 X 射线、端电压和短路电流都是隐藏沉积过程的投影。两种模型可以有相同容量衰减和端电压，却分别由许多短枝或少数贯通枝造成；同一 FIB 复形也可在不同嵌入、晶面能和过电位协议下产生不同形貌。因此，单一质量曲线、一次短路时间或几何路径计数不足以识别枝晶机制。

因此，FIB ATOM 递归在电池沉积问题中只提供界面复形的组合邻接、候选成核接缝、枝晶可行路径、边界分类和层级骨架。过电位、界面平衡、尖端场增强、曲率与应力耦合、成核势垒、附着—溶解核、表面扩散、噪声联合律、几何嵌入、晶面各向异性、SEI 电阻、贯通阈值、充放电协议、样品异质性、极值极限和观测投影均须外加。给定这些结构后，才能得到成核率、枝晶分支形貌、贯通时间和短路首失效分布；不存在由 FIB 递归单独推出的普适电池枝晶统计定律。

## 252. FIB 网络上的外加连续量子测量、量子轨迹与测量诱导相变统计

固定 FIB 图族或细胞复形的组合支撑 \(G_j=(V_j,E_j)\)。为使它成为量子测量模型，另给每个顶点或胞腔的 Hilbert 空间、局部和边界相互作用、初态以及测量装置。FIB ATOM 递归只给出可组合的支撑、邻接、路径、接缝与层级索引；Hilbert 空间维数、算符、时间单位、测量效率、记录噪声、反馈和极限方案均为外加。本节不重复第234节的无条件 Lindblad 信道和谱隙结论。

对一个时间步，测量结果 \(r\) 对应 Kraus 算子 \(M_{a,r}\)，满足

$$
\sum_rM_{a,r}^\dagger M_{a,r}=I,
\qquad
p(r\mid\rho)=\operatorname{Tr}(M_{a,r}\rho M_{a,r}^\dagger),
\qquad
\rho\mid r=\frac{M_{a,r}\rho M_{a,r}^\dagger}{p(r\mid\rho)}.
\tag{252.1}
$$

若记录时刻之间施加外加幺正 \(U_n\)，记录 \(\omega=(r_1,\ldots,r_n)\) 的未归一化状态为

$$
\widetilde\rho_{\omega,n}=K_{\omega,n}\rho_0K_{\omega,n}^\dagger,
\qquad
K_{\omega,n}=M_{a_n,r_n}U_n\cdots M_{a_1,r_1}U_1,
\tag{252.2}
$$

其 Born 权重为 \(p(\omega)=\operatorname{Tr}\widetilde\rho_{\omega,n}\)。FIB 边可以限制测量算符或幺正的允许支撑，但不决定矩阵元、相位或结果标签。

连续极限中，若 \(Y_a\) 是扩散记录、\(N_\mu\) 是计数记录，则一类外加测量模型为

$$
\begin{aligned}
dY_a(t)&=\sqrt{\eta_a}\operatorname{Tr}[(C_a+C_a^\dagger)\rho_{c,t}]\,dt+dW_a(t),\\
\Pr\{dN_\mu(t)=1\mid\mathcal Y_t\}&=\lambda_\mu(\rho_{c,t})dt,\\
\lambda_\mu(\rho)&=\operatorname{Tr}(J_\mu^\dagger J_\mu\rho),
\end{aligned}
\tag{252.3}
$$

其中效率、Wiener 相关性和未观测通道均须外加。归一化量子滤波方程包含创新项和跳跃项；其具体补偿必须与测量仪器一致。漏检会把本来纯的轨迹变成混合轨迹，不能用同一条记录恢复丢失信息。

对任意观测量 \(O\)，条件估计为 \(\widehat O_t=\operatorname{Tr}(O\rho_{c,t})\)。有限步记录满足

$$
\Pr(\omega\mid\rho_0)=\operatorname{Tr}(K_\omega\rho_0K_\omega^\dagger),
\qquad
\operatorname{Tr}(O\rho_\omega)=\frac{\operatorname{Tr}(OK_\omega\rho_0K_\omega^\dagger)}{\operatorname{Tr}(K_\omega\rho_0K_\omega^\dagger)}.
\tag{252.4}
$$

同一无条件平均态可以由不同仪器分解产生，而条件轨迹、创新相关和后验估计不同；测量记录的联合实现是统计律的一部分，不能由边缘均值代替。

令 \(N_\mu(t)=\int_0^t dN_\mu(s)\)，给记录通道权重和扩散测试函数，定义可加量

$$
\mathcal R_t=\sum_\mu w_\mu N_\mu(t)+\sum_a\int_0^tf_a(s)\,dY_a(s).
\tag{252.5}
$$

若长时和图族极限存在，可定义

$$
\theta_j(k)=\lim_{t\to\infty}\frac1t\log\mathbb E e^{k\mathcal R_t},
\qquad
I_j(r)=\sup_k\{kr-\theta_j(k)\}.
\tag{252.6}
$$

若共同长时/无限尺寸极限出现非解析点，才可称为记录动力学相变；固定有限图上的尖峰只是交叉。跳跃计数、连续电流、等待时间和记录后选择都会改变 \(\theta_j\) 与 \(I_j\)。

记录条件的纯度与纠缠统计为

$$
P_\omega(t)=\operatorname{Tr}\rho_{\omega,t}^2,
\qquad
S_A(\omega,t)=-\operatorname{Tr}\rho_{A,\omega,t}\log\rho_{A,\omega,t}.
\tag{252.7}
$$

保留记录的平均熵与先平均后取熵不同：

$$
\mathbb E_\omega S_A(\omega,t)\le S_A(\bar\rho_t),
\qquad \bar\rho_t=\mathbb E_\omega\rho_{\omega,t}.
\tag{252.8}
$$

纯化时间、条件首达时间和纠缠熵取决于初态系综、测量效率、算符不对易性、反馈和目标态；同一 FIB 路径长度不决定它们。

为讨论测量诱导相变，取随 \(j\) 增大的图和子区域，在外加局部幺正混合与测量之间迭代。离散模型可用测量概率 \(p\)，连续模型可用 \(g_j=\gamma_{m,j}/v_j\)。在特定的一维短程模型中，轨迹熵可能呈现

$$
S_A(L_A)\sim
\begin{cases}
s_{\rm vol}(p)L_A+O(1),&p<p_c,\\
\alpha\log L_A+O(1),&p=p_c,\\
O(1),&p>p_c,
\end{cases}
\tag{252.9}
$$

但 \(p_c\)、\(\alpha\)、临界指数以及相变是否存在，都依赖幺正门系综、测量算符支撑、维数、对称性、初态和记录平均。高维图或长程边不能沿用一维公式。保留 Born 权重的淬火平均、复制/退火平均和后选择平均也可能给出不同临界点。

强测量极限可出现量子 Zeno 交叉。若投影把 Hilbert 空间分为 \(P,Q=I-P\)，跨扇区块为 \(H_{PQ}\)，测量速率为 \(\gamma_m\)，在时间尺度分离成立时有效跃迁率具有

$$
\Gamma_{P\to Q}^{\rm eff}=O\!\left(\frac{\lVert H_{PQ}\rVert^2}{\gamma_m}\right).
\tag{252.10}
$$

系数和边界修正依赖测量仪器及谱结构；有限图上的 Zeno 抑制只是交叉，要称为相变仍需共同极限和非解析性判据。

同一 FIB 支撑上，顶点可交换的局部测量与相邻边的非对易奇偶测量可以有相同测量率和相同路径，却产生不同纯化、互信息和熵增长。改变探测效率而保持无条件平均通道不变，也会改变记录创新谱和首达分布。因此，同一 FIB 图、相同边数或相同事件总率不足以识别条件量子轨迹，更不足以推出唯一的临界点、纯化时间或大偏差函数。

因此，FIB ATOM 递归在连续量子测量问题中只提供可组合的测量支撑、候选耦合路径、记录端口、接缝和层级骨架；量子仪器、Hilbert 空间、Hamiltonian、测量算符、Born 权重、探测效率、记录联合实现、过滤初态、反馈、尺度极限以及熵和轨迹的平均协议均须外加。量子滤波、跳跃/扩散轨迹、纯化与纠缠统计、记录大偏差、Zeno 交叉和测量诱导相变，只有在这些条件明确后才是外加模型的统计结论。


## 253. FIB 细胞复形上的外加组织形态发生、顶点模型与活性组织流变统计

固定一族 FIB 细胞复形

$$
\mathcal C_j=(V_j,E_j,F_j;\partial_1,\partial_2),
\qquad \partial_1\partial_2=0 .
\tag{253.1}
$$

FIB ATOM 递归只提供细胞邻接、边界接缝、可拼接路径和层级索引；二维或三维几何嵌入、面积、周长、曲率、材料系数、摩擦、温度、细胞极性、主动驱动、分裂/死亡、噪声联合律、观测尺度及极限协议均须外加。面和边的组合身份不自动给出物理长度、界面能或细胞速度。

给定外加嵌入 \(r=(r_v)_{v\in V_j}\in(\mathbb R^2)^{V_j}\)，每个面才获得面积 \(A_f(r)\)、周长 \(P_f(r)\) 和形状张量。固定拓扑扇区内，一个外加顶点模型能量可写成

$$
\begin{aligned}
E_{j,\Theta}(r)={}&\sum_{f\in F_j}\frac{K_{A,f}}2(A_f-A_{0,f})^2
+\sum_{f\in F_j}\frac{K_{P,f}}2(P_f-P_{0,f})^2\\
&+\sum_{e\in E_j}\gamma_e\ell_e(r)+E_{\rm bend}(r)+E_{\rm adh}(r).
\end{aligned}
\tag{253.2}
$$

面积/周长弹性、边张力、弯曲和黏附参数以及约束集合均为外加量。带主动应力和噪声的过阻尼动力学可写成

$$
{\rm d}r_v=M_v[-\nabla_{r_v}E_{j,\Theta}+f_v^{\rm act}+f_v^{\rm ext}+\lambda_v],{\rm d}t
+B_v(r)\,{\rm d}W_v(t),
\tag{253.3}
$$

其中迁移率、噪声、约束乘子和主动牵引由外加模型规定。只有在噪声满足热平衡关系且没有主动驱动时，才可写平衡测度

$$
\pi_{j,\Theta}(dr)=Z_{j,\Theta}^{-1}e^{-\beta E_{j,\Theta}(r)}
\mathbf 1_{\mathcal M_j}(r)\,dr .
\tag{253.4}
$$

由此得到的边长、面积和形状涨落依赖 \(K_A,K_P,\gamma,\beta\) 及几何约束，不能由 FIB 的度数频率替代。

当一条界面边低于外加阈值 \(\ell_*\) 时，四个邻近细胞可以通过 T1 过程交换邻接。FIB 复形只能给出局部四元组和候选新接缝；新边方向、耗散、能垒和发生时刻由外加跳变核决定。例如

$$
\lambda_e(r)=\lambda_0\mathbf 1_{\{\ell_e(r)<\ell_*\}}
\exp\!\left[-\beta(\Delta E_e-\chi\sigma_e^{\rm act})_+\right].
\tag{253.5}
$$

若事件是给定历史下的条件 Poisson 过程，总强度为 \(\Lambda_j(t)=\sum_{e}\lambda_e(t)\)，等待时间尾为

$$
\Pr(T_1>t\mid\mathcal F_0,\Theta)=\exp\!\left[-\int_0^t\Lambda_j(s){\rm d}s\right].
\tag{253.6}
$$

共享极性、应力或噪声会把事件变为 Cox 或一般相关点过程，式 (253.6) 的无条件指数形式随之失效。分裂、凋亡和基底附着还需另给强度与面积演化，FIB 层间映射不能替代这些生物过程。

把每个细胞的极性单位向量记为 \(p_f\)，外加主动应力可写成

$$
Q_f=p_f\otimes p_f-\frac12I,
\qquad \sigma_f^{\rm act}=\zeta_fQ_f .
\tag{253.7}
$$

极性相关长度、应力符号、旋转动力学及其传给顶点力的离散散度均须外加。组织尺度的质量平衡和过阻尼力平衡可写成

$$
\partial_t\rho+\nabla\!\cdot(\rho v)=s_{\rm div}-s_{\rm del},
\tag{253.8}
$$

$$
0=\nabla\!\cdot(\sigma^{\rm el}+\sigma^{\rm int}+\sigma^{\rm act}
-\eta\nabla^{\rm sym}v+\sigma^{\rm noise})-\xi(v-v_{\rm sub})+f^{\rm ext}.
\tag{253.9}
$$

黏性、基底摩擦、源项、噪声谱和本构均非 FIB 量。给定剪切扰动后，组织复模量

$$
G^*(\omega)=\frac{\widehat{\delta\Sigma_{xy}}(\omega)}{\widehat{\delta\gamma}(\omega)}
=G'(\omega)+{\rm i}G''(\omega)
\tag{253.10}
$$

由能量、主动应力、摩擦和重排核共同决定。主动稳态有概率流时，平衡 Green–Kubo 黏度不能直接套用。

形变或 T1 级联的大小 \(S\) 需先规定为耗散能、交换面积或应变增量。在指定外加图列、驱动、混合和边界后，才可检验有限尺寸形式

$$
\Pr(S>s)\approx s^{-\tau_\Theta}\Phi_\Theta\!\left(s/s_c(j,\Theta)\right),
\qquad s_c(j,\Theta)\sim L_j^{d_{\rm eff}} .
\tag{253.11}
$$

指数、截断和速度相关可能为指数、幂律或平台，取决于嵌入、应力传播、阻尼、驱动速率和重排规则。FIB 路径长度只是组合索引距离，不等于物理相关长度。

同一 FIB 复形在 \(\gamma=0\) 与 \(\gamma\ne0\) 或不同 \(K_A,K_P,\eta,\xi,\zeta\) 下，可具有相同邻接而产生不同的形状分布、主动概率流、T1 首达和流变谱。有限观测还把局部速度、应力和重排投影为带阈值和空间卷积的信号，不能从单帧形状或总应力唯一恢复隐藏参数。

因此，FIB ATOM 递归在组织形态发生问题中只提供组合邻接、候选接缝和层级骨架；嵌入、能量、主动应力、重排核、分裂/死亡、噪声、边界和观测均须外加。形状涨落、T1 等待时间、组织流变、速度相关和级联尾部都是条件模型结论。

## 254. FIB 网络上的外加异常热传导、声子散射与非傅里叶统计

固定一族 FIB 图或细胞复形，其一维通道支撑为 \(G_j=(V_j,E_j)\)。FIB 只提供顶点、边、可拼接接缝、切割和层级索引；连续位置、距离、截面、质量、弹簧常数、势能、温度、时间尺度、热浴、初态、噪声和观测映射均须外加。图距离不自动是声子传播距离，边数不自动是长度或体积。

一个外加带质量与势能的网络 Hamiltonian 为

$$
H_j(q,p)=\sum_{v\in V_j}\frac{p_v^2}{2m_v}
+\frac12\sum_{e=(u,v)\in E_j}k_e(q_v-q_u)^2
+\sum_vU_v(q_v)+H_{\rm anh}(q).
\tag{254.1}
$$

线性化后

$$
K_j\phi_{\nu,j}=\omega_{\nu,j}^2M_j\phi_{\nu,j},
\tag{254.2}
$$

开放边界和内部散射还需给出自能，频域响应可写成

$$
\mathcal G_j^R(\omega)=\bigl[K_j-\omega^2M_j-{\rm i}\omega\Gamma_j^\partial-\Sigma_j^R(\omega)\bigr]^{-1}.
\tag{254.3}
$$

FIB 邻接只能限制矩阵支撑，不能决定系数、频率或相位。

给定外加能量分解，跨越切割 \(\mathcal C\) 的热流可写为 \(J_\mathcal C=\sum_{e\in\mathcal C}\sigma_ej_e\)。在平衡系综、相关积分收敛且极限顺序已声明时，Green–Kubo 型热导为

$$
\kappa_j(L,T)=\frac1{k_BT^2A}\lim_{t\to\infty}\int_0^t
\langle J_\mathcal C(s)J_\mathcal C(0)\rangle_{\rm eq}\,{\rm d}s .
\tag{254.4}
$$

横截面、长度、热浴和切割方向不由 FIB 选择；先取长时再取大图极限与相反次序可能不同。模态寿命由非线性、无序、边界和热浴共同给出，例如

$$
\tau_\nu^{-1}=\tau_{\nu,\rm anh}^{-1}+\tau_{\nu,\rm dis}^{-1}
+\tau_{\nu,\rm boundary}^{-1}+\tau_{\nu,\rm bath}^{-1}.
\tag{254.5}
$$

无序还可产生局域化长度 \(\xi(\omega)\) 与逆参与率

$$
{\rm IPR}_{\nu,j}=\frac{\sum_vm_v^2|\phi_{\nu,j}(v)|^4}{(\sum_vm_v|\phi_{\nu,j}(v)|^2)^2}.
\tag{254.6}
$$

这些量依赖物理距离、无序系综、边界与平均方式，不是递归量。

若电流相关在 \(1\ll t\ll t_L\) 有外加长尾 \(C_J(t)\sim c t^{-\gamma}\)，且 \(t_L\asymp L^z\)，候选 Green–Kubo 标度为

$$
\kappa(L)\sim
\begin{cases}
L^{z(1-\gamma)},&0<\gamma<1,\\
\log L,&\gamma=1,\\
\kappa_\infty,&\gamma>1.
\end{cases}
\tag{254.7}
$$

指数与截断由外加守恒量、维数、散射和边界决定。长程跳跃或陷阱还可外加分数扩散

$$
\partial_tu=-D_\mu(-\Delta)^{\mu/2}u,
\qquad
{}^{\rm C}D_t^\beta u=D\Delta u,
\tag{254.8}
$$

其中 \(\mu\) 或 \(\beta\) 来自外加跳跃/等待时间尾部。非傅里叶本构可以写成

$$
J(t)=-\int_0^tK(t-s)\nabla T(s)\,{\rm d}s+\zeta(t),
\qquad
\tau_q\partial_tJ+J=-\kappa\nabla T+\zeta
\tag{254.9}
$$

但噪声协方差、能量守恒、初边值和核函数均需同时指定。

边界热阻、镜面/扩散反射和主动储库可以制造或遮蔽异常；有限探针的读数是

$$
Y_a(t)=\int h_a(x,\omega)u(x,t)\,dx+\int_0^tg_a(t-s)J(s)\,{\rm d}s+\eta_a(t).
\tag{254.10}
$$

未知响应核使单一端点温差—平均流量曲线无法区分体相非傅里叶本构、稀疏共振、局域化和接触阻抗。首达时间、热量大偏差与 quenched/annealed 统计也依赖共同环境和极限顺序。

因此，FIB ATOM 递归在异常热传导问题中只提供支撑、切割、路径、接缝和层级骨架；质量与刚度、声子频散、非线性和无序、散射率、局域化、热浴、边界、记忆核、分数阶指数、噪声、嵌入、尺度极限和观测滤波均须外加。傅里叶、弹道、超扩散、亚扩散和局域化统计只能是指定模型后的条件结论。

## 255. FIB 网络上的外加磁振子与自旋波输运、三波散射及非平衡凝聚统计

固定一族 FIB 图或细胞复形的组合支撑 \(G_j=(V_j,E_j)\)，并把顶点或胞腔附加为局域磁振子自由度 \(a_v\)。FIB ATOM 递归只给出支撑、邻接、路径、接缝、端口和层级索引；自旋长度、交换常数、各向异性、外磁场、陀螺磁比、阻尼、几何、晶向、温度、泵浦、储库和观测响应均须外加。

小振幅近似中的二次 Hamiltonian 为

$$
H_2=\sum_{u,v\in V_j}a_u^\dagger h^{(j)}_{uv}a_v,
\qquad [a_u,a_v^\dagger]=\delta_{uv}.
\tag{255.1}
$$

\(h^{(j)}\) 的非零支撑可受 FIB 邻接约束，但其数值、相位和方向不由邻接确定；若有反常配对，还需外加 Bogoliubov 矩阵。线性模态满足 \(h\varphi_\nu=\hbar\omega_\nu\varphi_\nu\)，谱密度为

$$
\rho_j(\omega)=\sum_\nu\delta(\omega-\omega_{j\nu}).
\tag{255.2}
$$

图上的路径长度、节点度或递归深度不能单独决定频率、群速度或局域化长度。

若若干个边界子集与外部波导或热库相连，边界自能给出

$$
G_j^R(\omega)=\left[(\omega+{\rm i}0^+)I-h^{(j)}-\sum_\alpha\Sigma_\alpha^R(\omega)\right]^{-1},
\qquad
\Gamma_\alpha={\rm i}(\Sigma_\alpha^R-\Sigma_\alpha^A).
\tag{255.3}
$$

端口透射和数流/能流可以写成

$$
\mathcal T_{\alpha\beta}(\omega)=\operatorname{Tr}[\Gamma_\alpha G_j^R\Gamma_\beta G_j^A],
\tag{255.4}
$$

$$
I_\alpha^N=\int_0^\infty\frac{{\rm d}\omega}{2\pi}\sum_\beta\mathcal T_{\alpha\beta}(n_\beta-n_\alpha),
\qquad
I_\alpha^E=\int_0^\infty\frac{{\rm d}\omega}{2\pi}\hbar\omega\sum_\beta\mathcal T_{\alpha\beta}(n_\beta-n_\alpha).
\tag{255.5}
$$

温度、化学势、注入谱和端口阻抗决定占据与自能；FIB 路径计数只是候选通道，不能直接给出导热系数、衰减长度或接触电阻。

三波过程的外加非线性顶点可写成

$$
H_3=\frac12\sum_{1,2,3}\left(V_{1;23}a_1^\dagger a_2a_3+V_{1;23}^*a_1a_2^\dagger a_3^\dagger\right),
\tag{255.6}
$$

其模态重叠、偏振、晶向、共振展宽和泵浦均为外加。弱耦合动理学可写成

$$
\dot n_1=P_1-2\gamma_1n_1+\mathcal C_1^{(3)}[n],
\tag{255.7}
$$

其中碰撞项含 \(|V_{1;23}|^2\) 和有限寿命的共振核。三波过程一般不守磁振子数；只有在反应计量关系允许且数改变过程被抑制时，才可引入有效化学势。泵浦—耗散稳态可能呈准热、幂律级联、双温尾或非 Bose 分布，单频带拟合不能推出全谱热化。

平衡凝聚的候选判据为

$$
\liminf_{j\to\infty}\frac{N_{0,j}}{N_j}>0,
\qquad
N_{0,j}=\frac1{\exp[\beta(\hbar\omega_{0,j}-\mu_j)]-1},
\tag{255.8}
$$

但是否存在临界温度取决于态密度、有效维数、红外边界、相互作用和极限次序。驱动系统中低模振幅可满足

$$
\dot\psi_0=\left[\frac{G_0-\kappa_0}{2}-{\rm i}\Omega_0\right]\psi_0
-\chi_0|\psi_0|^2\psi_0+\xi_0,
\tag{255.9}
$$

\(G_0=\kappa_0\) 只是给定泵浦、损耗和反馈后的阈值，不等同于平衡 Bose–Einstein 凝聚。空间相干性可由

$$
g^{(1)}_{uv}(t)=\frac{\langle a_u^\dagger(t)a_v(t)\rangle}{\sqrt{\langle n_u(t)\rangle\langle n_v(t)\rangle}}
\tag{255.10}
$$

表征；局部强度峰、边界增强和长程相干是不同事件。

磁光散射、微波天线、热电探针和端口功率都是内部态投影：

$$
y_a(t)=\sum_{v\in V_j}Q_{av}m_v(t)+\eta_a(t),
\qquad
S_{ab}(\omega)=\int e^{{\rm i}\omega t}\langle y_a(t)y_b(0)\rangle_c\,{\rm d}t.
\tag{255.11}
$$

不同内部占据可以有相同端口功率而具有不同低模相干；探针位置、偏振和带宽也会改变谱峰。因此，FIB 递归只提供磁振子自由度的组合支撑、传播路径和边界端口；交换/各向异性、几何、阻尼、端口自能、泵浦、散射顶点、态密度、无序、图族极限及观测响应均须外加。输运、三波散射、非平衡级联、低模凝聚和谱峰统计都是条件模型结论。


## 256. FIB 网络上的外加介观单电子输运、库仑阻塞与全计数统计

固定一族 FIB 图或细胞复形的组合支撑 \(G_j=(V_j,E_j)\)，把若干顶点或胞腔外加为量子点/金属岛，把边或接缝外加为隧穿结，把其余边界外加为电极与热库。FIB ATOM 递归只给出可拼接的支撑、邻接、路径、端口与层级索引；岛的电容矩阵、隧穿振幅、能级、库仑相互作用、引线化学势、温度、环境阻抗、初态、时间单位和探测器响应均须外加。

令 \(\mathbf n=(n_v)_{v\in V_j}\in\mathbb Z^{V_j}\) 为岛上的整数电子数，\(C_j\) 为包含互电容、对地电容和电极电容的正定约化电容矩阵，\(q_g\) 为栅极诱导电荷。一个外加静电能为

$$
E_j(\mathbf n)=\frac12(e\mathbf n-\mathbf q_g)^{\mathsf T}C_j^{-1}(e\mathbf n-\mathbf q_g)+E_j^{\rm sp}(\mathbf n).
\tag{256.1}
$$

给定隧穿结或电极 \(\alpha\) 的事件 \(r=(\alpha,\sigma)\)，\(\sigma=+1\) 表示电子从电极进入岛，\(\sigma=-1\) 表示相反方向。对电极费米函数

$$
f_\alpha(\varepsilon)=\frac1{e^{\beta_\alpha(\varepsilon-\mu_\alpha)}+1},
\tag{256.2}
$$

在顺序隧穿近似中，一种速率约定为

$$
W_{\alpha,+}(\mathbf n)=\Gamma_{\alpha,+}(\mathbf n)f_\alpha(\Delta_{\alpha,+}E(\mathbf n)),
\qquad
W_{\alpha,-}(\mathbf n)=\Gamma_{\alpha,-}(\mathbf n)[1-f_\alpha(\Delta_{\alpha,-}E(\mathbf n))].
\tag{256.3}
$$

隧穿矩阵元、态密度、透明度和自由能差的符号约定均为外加。电荷概率满足

$$
\dot p_{\mathbf n}=\sum_r\left[W_r(\mathbf n-\nu_r)p_{\mathbf n-\nu_r}-W_r(\mathbf n)p_{\mathbf n}\right],
\tag{256.4}
$$

其中 \(\nu_r\in\mathbb Z^{V_j}\) 是事件的电荷转移向量，求和只保留相应电荷态存在的事件。FIB 邻接至多限制非零转移的候选支撑，不决定速率。

库仑阻塞发生在外加条件

$$
\max_\alpha\{e|V_\alpha|,k_BT_\alpha,\hbar\Gamma_\alpha\}\ll E_C,
\qquad E_C\sim\frac{e^2}{2C_\Sigma}
\tag{256.5}
$$

下；\(E_C\) 由电容和材料决定。阻塞平台、热激活泄漏、多态通道和共隧穿区域都依赖外加能级、温度、环境 \(P(E)\) 和偏压，不能从路径数推出。

为同时记录粒子和能量，在事件上附加粒子增量 \(q_r\) 与能量 \(\varepsilon_r\)。倾斜生成元的非对角元为

$$
[\mathcal W_{\boldsymbol\chi,\boldsymbol\xi}]_{\mathbf n',\mathbf n}
=\sum_{r:\,\mathbf n'=\mathbf n+\nu_r}W_r(\mathbf n)
 e^{{\rm i}\chi_{\alpha(r)}q_r+{\rm i}\xi_{\alpha(r)}\varepsilon_r}.
\tag{256.6}
$$

若长时极限存在，累积生成率为

$$
\Theta(\boldsymbol\chi,\boldsymbol\xi)=\lim_{t\to\infty}\frac1t
\log\left[\mathbf1^{\mathsf T}e^{\mathcal W_{\boldsymbol\chi,\boldsymbol\xi}t}p(0)\right],
\tag{256.7}
$$

其一阶、二阶和更高导数分别给出平均流、shot noise 和高阶计数累积量；平均电流或零频噪声不能唯一确定完整计数律。

状态 \(\mathbf n\) 的逃逸率为 \(R(\mathbf n)=\sum_rW_r(\mathbf n)\)，无事件存活概率和下一事件条件密度为

$$
\Psi_{\mathbf n}(\tau)=e^{-R(\mathbf n)\tau},
\qquad
\psi(r,\tau\mid\mathbf n)=W_r(\mathbf n)e^{-R(\mathbf n)\tau}.
\tag{256.8}
$$

隐藏电荷态被消去后，观测等待时间分布通常是多个指数的混合，慢环境还可产生非指数尾。两结单能级、零温、单向偏压的特例给出

$$
I=e\frac{\Gamma_L\Gamma_R}{\Gamma_L+\Gamma_R},
\qquad
F=\frac{\Gamma_L^2+\Gamma_R^2}{(\Gamma_L+\Gamma_R)^2},
\tag{256.9}
$$

但陷阱、热回流、动态阻塞和共同环境会改变 \(F\) 与等待时间尾；同一低阶 \((I,F)\) 可以对应不同高阶计数统计。

热电输运需同时计数粒子和热量。在线性响应与微观可逆条件下，可写

$$
\begin{pmatrix}I/e\\ J^Q\end{pmatrix}
=\begin{pmatrix}L_{11}&L_{12}\\L_{21}&L_{22}\end{pmatrix}
\begin{pmatrix}\Delta(\mu/T)\\\Delta(1/T)\end{pmatrix},
\qquad L_{12}=L_{21}
\tag{256.10}
$$

Onsager 对称性还需注明磁场反演；热电系数依赖能级、隧穿率、温度和电容耦合，而非 FIB 路径数。

若每个反向事件满足局部详细平衡，正反轨迹的熵产生比满足

$$
\log\frac{\mathbb P[\omega]}{\mathbb P^\dagger[\widetilde\omega]}=\Delta S_{\rm tot}[\omega].
\tag{256.11}
$$

在稳态初态、反向协议、微观可逆和完整记录条件下，熵产生的 SCGF 才可能满足 Gallavotti–Cohen 对称；磁场、非热储库、反馈、隐藏态或只记录部分电极时必须改写，不能把粒子计数对称直接当作热熵定律。

实际读数是隐藏电荷态和热流的投影：

$$
Y_a(t)=\int_0^th_a(t-s)\left[\sum_\alpha c_{a\alpha}\,dN_\alpha(s)+\sum_\alpha d_{a\alpha}\,dQ_\alpha(s)\right]+\eta_a(t).
\tag{256.12}
$$

有限带宽、未分辨热流和电子噪声使不同电容、隧穿率和环境阻抗可有相同低阶读数而有不同等待时间、高阶累积量和熵产生。因此，FIB ATOM 递归在介观单电子问题中只提供量子岛、隧穿结、端口、路径、接缝和层级骨架；电容、离散电荷、能级、隧穿率、储库、计数协议、热流定义、可逆性、极限和探测器响应均须外加。

## 257. FIB 网络上的外加交通流、排队瓶颈与 stop-and-go 波统计

本节把交通对象限定为可路由车辆、链路服务和检测过程。FIB ATOM 递归只提供原子间组合关系、方向邻接、可拼接接缝、层级和允许路径。链路长度 \(L_e\)、车道数、自由速度 \(v_e\)、容量 \(C_e\)、信号相位、服务时间分布、车辆类别、OD 需求、路线选择和观测噪声均须另行给定。

对链路 \(e\) 记累计到达数和离开数为 \(A_e(t),D_e(t)\)，队列长度为 \(Q_e(t)\)。交通守恒为

$$
N_e(t)=N_e(0)+A_e(t)-D_e(t),
\qquad
Q_e(t+\Delta t)=[Q_e(t)+A_e(t,t+\Delta t)-S_e(t,t+\Delta t)]_+,
\tag{257.1}
$$

其中服务量由信号、容量和服务时间决定。节点转向矩阵 \(P_v(t)\) 把进入流分配到允许的后继链路；FIB 只决定哪些组合接合和路径存在，不给出需求、服务或路由。

随机到达可由 Poisson、更新、Markov 调制或 Cox 过程给出。若转向矩阵为 \(P\)、外部到达率为 \(\lambda\)，开放网络形式上有

$$
\alpha=(I-P^{\mathsf T})^{-1}\lambda,
\qquad \varrho_e=\alpha_e/\mu_e.
\tag{257.2}
$$

在相应队列假设和有限矩条件下，所有 \(\varrho_e<1\) 是稳定有限队列的典型充分条件；某个负载达到一时会进入持续积压或容量饱和区。阈值依赖 \(\lambda,P,\mu\) 和服务纪律，不能从 FIB 邻接推出。

单瓶颈可写成反射递推

$$
Q_{n+1}=[Q_n+X_n-C_n]_+,
\tag{257.3}
$$

负载跨过一时，有限网络的转变由需求、容量和时间尺度平滑；大系统中可出现拥堵交叉或相变。容量退化还可造成卸载滞回。任何割集的最大通过率受服务率和约束，但是否成为实际瓶颈仍取决于路线、信号和车辆优先级。

在轻尾到达和服务且稳定时，许多队列的等待尾呈指数型大偏差；重尾到达、事故或服务时间会传递次指数或幂律尾。M/G/1 特例的平均等待时间含有

$$
\mathbb E W_q=\frac{\lambda\,\mathbb E[S^2]}{2(1-\varrho)}.
\tag{257.4}
$$

路径 \(p\) 的旅行时间为

$$
T_p=\sum_{e\in p}\frac{L_e}{v_e}+\sum_{e\in p}W_e+R_p,
\tag{257.5}
$$

其中额外项收集信号、换道、事故和路线重选。车辆类别与路径混合会令 \(T_p\) 多峰；相关到达和共同事故使等待项不能按独立和处理。

连续链路的外加守恒流模型为

$$
\partial_t\rho+\partial_xf(\rho)=0,
\qquad
s=\frac{f(\rho_2)-f(\rho_1)}{\rho_2-\rho_1},
\qquad c(\rho)=f'(\rho).
\tag{257.6}
$$

瓶颈高密度区可向上游传播，低密度区向下游传播。若采用外加跟驰动力学

$$
\dot x_i=v_i,
\qquad
\dot v_i=\kappa[V(s_i)-v_i]+\eta_i(t),
\tag{257.7}
$$

线性化后若某波数带有正增长率，微小车距扰动被放大为 stop-and-go 波；波长、传播速度和寿命依赖跟驰函数、反应延迟、车辆异质性、噪声和边界。FIB 接缝只能决定波在哪些链路间组合传递，不能决定色散关系。

拥堵观测通常是检测器计数、平均速度、占有率或少量探针轨迹：

$$
y(t)=H(\rho(t),Q(t),P(t),\lambda(t),\mu(t),\vartheta)+\epsilon(t).
\tag{257.8}
$$

不同外加模型可以有相同流量—速度均值而有不同隐藏路线流、服务时间、跟驰延迟和事故机制；只看 FIB 图更不能识别这些参数。需要逐车轨迹、路径标签、队列长度、需求扰动和事故状态等外加联合观测。

因此，FIB ATOM 递归能够承载交通网络的组合闭包、允许路径、割集、接缝和层级；稳定阈值、拥堵交叉、排队尾、stop-and-go 色散和旅行时间统计由需求、服务、容量退化、路由策略、车辆动力学、几何尺度、边界与观测协议共同决定，不能由 FIB 递归单独推出。
## 258. FIB 递归上的外加更新过程、再生结构与中心极限定理/功能极限定理统计

固定一族由 FIB ATOM 递归生成的组合状态 \(\mathcal A_n\)，并记递归层之间的候选接口为 \(\iota_n\)。一次外加更新可抽象写成

$$
\mathcal A_{n+1}=\Phi_{\Theta}\bigl(\mathcal A_n,\iota_n;\,\xi_{n+1},Z_{n+1}\bigr),
\qquad
X_a(t)=\Psi_{a,\Theta}\bigl((\mathcal A_s)_{s\le t},(\iota_s)_{s\le t}\bigr)+\eta_a(t).
\tag{258.1}
$$

FIB ATOM 递归只规定可拼接的组合支撑、接口的候选身份、祖先关系和层级索引；更新等待时间 \(\xi_n\)、事件标记 \(Z_n\)、状态更新映射 \(\Phi_\Theta\)、时间单位、观测映射 \(\Psi_{a,\Theta}\) 及噪声均为外加。递归步数或深度不是物理时间，接口存在也不等于系统在接口处已经遗忘过去。

若外加模型给出一个真正的再生判据，令 \(\tau_0=0\) 为再生时刻，并令

$$
\tau_{k+1}=\tau_k+\xi_{k+1},
\qquad
N(t)=\max\{k:\tau_k\le t\}.
\tag{258.2}
$$

再生要求在适当的隐藏状态等价类上满足

$$
\mathcal L\!\left((\xi_{k+1},Y_{k+1}), (\xi_{k+2},Y_{k+2}),\ldots\mid\mathcal F_{\tau_k}\right)
=\mathcal L\!\left((\xi_1,Y_1),(\xi_2,Y_2),\ldots\right),
\tag{258.3}
$$

并且右侧与 \(\mathcal F_{\tau_k}\) 独立；\(Y_k\in\mathbb R^d\) 是一个周期内的外加奖励、通量、计数或观测增量。FIB 接缝可以被选作再生面的候选位置，但式 (258.3) 需要由外加的状态重置、Markov 分裂或条件独立机制证明，不能由组合接缝自动推出。

设 \(F_\xi\) 是等待时间分布，外加更新理论的基本测度满足

$$
U_\Theta(B)=\sum_{n\ge0}F_\xi^{*n}(B),
\qquad
U_\Theta(t)=F_\xi^{*0}([0,t])+\bigl(U_\Theta*F_\xi\bigr)(t),
\tag{258.4}
$$

其中 \(F_\xi^{*0}=\delta_0\)。这条更新方程只使用等待时间律；它既不指定等待时间律，也不指定 FIB 层级的增长速度。若奖励过程写为

$$
R(t)=\sum_{k=1}^{N(t)}Y_k+\rho(t),
\tag{258.5}
$$

则 \(\rho(t)\) 是未完成周期的边界奖励。其大小和可忽略性取决于外加奖励界、等待时间矩和观测截断。

在周期独立同分布、\(m=\mathbb E\xi_1\in(0,\infty)\)、\(\mathbb E\|Y_1\|<\infty\) 且边界项满足相应可忽略条件时，更新率和奖励率为

$$
\frac{N(t)}t\longrightarrow \frac1m,
\qquad
\frac{R(t)}t\longrightarrow r:=\frac{\mathbb E Y_1}{m}
\quad\text{几乎处处}.
\tag{258.6}
$$

若进一步有 \(\mathbb E\xi_1^2+\mathbb E\|Y_1\|^2<\infty\)，定义中心化周期奖励 \(W_1=Y_1-r\xi_1\)，则

$$
\frac{R(t)-rt}{\sqrt t}
\Longrightarrow
\mathcal N_d(0,\Sigma),
\qquad
\Sigma=\frac{\mathbb E[W_1W_1^{\mathsf T}]}{m}.
\tag{258.7}
$$

式 (258.7) 将等待时间涨落和周期奖励涨落放在同一随机量中；只知道 \(\mathbb E Y_1\) 或只知道更新次数的方差，不能确定 \(\Sigma\)。标量情形的方差为 \(\operatorname{Var}(Y_1-r\xi_1)/m\)，因此奖励与等待时间的协方差会改变中心极限定理的系数。

在 \(2+\delta\) 阶矩、再生边界项的最大偏差为 \(o_{\mathbb P}(\sqrt t)\)，并采用阶梯过程的 \(J_1\) 拓扑时，(258.7) 可提升为功能极限

$$
\left\{\frac{R(ts)-rts}{\sqrt t}:0\le s\le1\right\}
\Longrightarrow
\left\{\Sigma^{1/2}B(s):0\le s\le1\right\},
\tag{258.8}
$$

其中 \(B\) 是标准 \(d\) 维 Brownian 运动。连续插值、端点删失和检测器带宽若不满足边界可忽略条件，极限过程需要相应修正；(258.8) 不是 FIB 递归的普遍结论。

外加模型也可能只有 Markov 再生或相关周期。令 \(W_k=Y_k-r\xi_k\)，若周期序列平稳、满足足够强的混合和 \(2+\delta\) 阶矩条件，且协方差级数绝对收敛，则周期索引的长程协方差为

$$
\Gamma=\operatorname{Cov}(W_0,W_0)
+\sum_{k\ge1}\left[\operatorname{Cov}(W_0,W_k)+\operatorname{Cov}(W_k,W_0)\right],
\qquad
\Sigma=\frac\Gamma m.
\tag{258.9}
$$

此时仍可得到 Brownian 型中心极限，但 \(\Gamma\) 由外加的共同环境、状态记忆、路由和层级耦合决定。若再生只在随机返回时刻成立，需要把返回时间一并纳入 \(\xi_k\)，不能把相关块错误地当作独立样本。

等待时间或周期奖励的重尾会改变归一化。若外加

$$
\Pr(\xi_1>x)\sim L(x)x^{-\alpha},
\tag{258.10}
$$

其中 \(0<\alpha<1\)，则 \(\mathbb E\xi_1=\infty\)，式 (258.6) 的确定性更新率不存在；适当缩放后的 \(N(t)\) 可收敛到逆稳定子过程或 Mittag--Leffler 型随机时间。若 \(1<\alpha<2\)，平均等待时间有限但二阶矩发散，在 \(W_1\) 属于相同 \(\alpha\)-稳定吸引域的外加条件下，\(R(t)-rt\) 的归一化为 \(t^{1/\alpha}\) 量级并具有稳定极限，而非 (258.7) 的 \(\sqrt t\) 高斯极限。尾指数、慢变函数和奖励—等待时间耦合全部是外加数据。

另一种偏离来自长程相关。若周期中心量满足

$$
\operatorname{Cov}(W_0,W_k)\sim c k^{-\gamma},
\qquad 0<\gamma<1,
\tag{258.11}
$$

则部分和方差通常为 \(\operatorname{Var}(\sum_{k=1}^nW_k)\asymp n^{2-\gamma}\)，\(\sqrt n\) 缩放失效；在外加高斯或线性过程及适当正则条件下，\(n^{1-\gamma/2}\) 缩放可给出 Hurst 指数 \(H=1-\gamma/2\) 的分数 Brownian 极限，非线性相关则可能产生非高斯极限。FIB 的层级深度只提供相关索引的组合位置，不提供 (258.11) 的协方差尾。

对同一 FIB 递归可以构造至少两种相容的外加统计：模型 A 取 \(\xi_k\equiv1\)，取有限二阶矩且独立的中心奖励，于是得到 (258.7)--(258.8)；模型 B 保持完全相同的原子、接缝和层级，却取 Pareto 等待时间 \(\Pr(\xi>x)=x^{-\alpha}\)（\(0<\alpha<1\)）并令每周期奖励为一，更新次数没有线性确定率。两者组合支撑相同而统计极限不同，故仅凭 FIB 递归不能识别“高斯扩散”“稳定律”或“分数 Brownian”中的任何一种。

有限观测还会把再生事件删失、合并或卷积为

$$
\widehat R_a(t)=\int_0^t h_a(t-s)\,dR(s)+\eta_a(t),
\tag{258.12}
$$

其中响应核、漏检概率、阈值、采样间隔和噪声由观测协议外加。漏掉短周期会把更新律伪装成重尾，未观测的共同环境会把独立周期伪装成长程相关；因此从 \(\widehat R_a\) 的一个低阶矩反推 (258.7) 或 (258.11) 需要额外的可识别性和联合观测条件。

因此，FIB ATOM 递归在更新与再生问题中只提供可拼接的组合块、候选再生接口、路径/层级索引和边界骨架；等待时间分布、周期奖励、重置核、独立性或混合性、重尾指数、相关结构、时间尺度、极限归一化与观测协议均须外加。更新率、再生奖励率、中心极限定理、功能极限、稳定极限及分数 Brownian 统计，都是在明确外加条件下的模型结论，不能由 FIB 递归单独推出。


## 259. FIB 递归观察序列上的隐藏状态过滤、条件互信息与因果边界统计

固定一族由 FIB ATOM 递归生成的合法上下文与路径，并另给物理时钟、采样间隔、观测映射和联合概率律。递归层号或词长不是物理时间。设源区域为 \(S\)、目标区域为 \(R\)，候选分隔边界为 \(B\)；外加观测记为 \(Y_S(t)\)、\(X_R(t)\) 及边界读出 \(Q_B(t)\)。令

$$
Y^-_t=Y_S(t-\ell+1:t),\qquad
X^-_t=X_R(t-k+1:t),\qquad
Q^-_{B,t}=Q_B(t-m+1:t),
$$

并写 \(Z_{B,t}=(X^-_t,Q^-_{B,t})\)。边界条件下的有限记忆传递信息剖面定义为

$$
\mathsf T_{S\to R\mid B}^{k,\ell,m}
=I\!\left(X_R(t+1);Y^-_t\mid Z_{B,t}\right).
\tag{259.1}
$$

它是给定目标历史与边界读出后，源历史对目标下一次观测的预测增益。总有

$$
0\le \mathsf T_{S\to R\mid B}^{k,\ell,m}
\le \min\left\{H(X_R(t+1)\mid Z_{B,t}),\ H(Y^-_t\mid Z_{B,t})\right\},
\tag{259.2}
$$

但其数值仍依赖时间粗粒化、历史阶数、量化和观测噪声。FIB 只能给出 \(S\) 到 \(R\) 的合法路径、接缝和候选割集，不能把组合路径的方向解释为时间方向。

引入未观测的外加状态 \(H_t\)，它可包含未读出的分支选择、共同环境、驱动相位和探测器记忆。条件互信息的链式法则给出隐藏状态分解

$$
\begin{aligned}
\mathsf T_{\mathrm{obs}}
&=I(X_R(t+1);Y^-_t\mid Z_{B,t})\\
&=\underbrace{I(X_R(t+1);Y^-_t\mid Z_{B,t},H_t)}_{\mathsf T_{\mathrm{intr}}}
+\underbrace{I(X_R(t+1);H_t\mid Z_{B,t})
-I(X_R(t+1);H_t\mid Z_{B,t},Y^-_t)}_{\Delta_H}.
\end{aligned}
\tag{259.3}
$$

第一项是把该时刻潜在状态视为已知后的条件预测流；第二项是源历史改变目标对隐藏状态的可见程度所产生的泄漏项。\(\Delta_H\) 没有固定符号：源历史可能暴露共同原因而抬高观测传递熵，也可能提供冗余信息而降低隐藏状态不确定性。若满足外加条件马尔可夫链

$$
Y^-_t\;\longrightarrow\;(H_t,Z_{B,t})\;\longrightarrow\;X_R(t+1),
$$

则条件数据处理不等式给出

$$
\mathsf T_{\mathrm{obs}}
\le I(X_R(t+1);H_t\mid Z_{B,t}).
\tag{259.4}
$$

这只是隐藏状态信息预算，不是干预效应的上界；若该马尔可夫条件不成立，甚至该上界也不能使用。

过滤器只能从可观测历史形成后验

$$
\pi_t(h)=\Pr(H_t=h\mid\mathcal O_{\le t}),
\qquad
\Pr(X_R(t+1)=x\mid\mathcal O_{\le t})
=\sum_h\pi_t(h)\Pr(x\mid h,\mathcal O_{\le t}),
\tag{259.5}
$$

其中 \(\mathcal O_{\le t}\) 包含所选源、目标和边界读出。设 \(p_h(x)=\Pr(X_R(t+1)=x\mid h,\mathcal O_{\le t})\)，则隐藏状态对下一步预测的剩余信息为

$$
I(X_R(t+1);H_t\mid\mathcal O_{\le t})
=H\!\left(\sum_h\pi_t(h)p_h\right)-\sum_h\pi_t(h)H(p_h).
\tag{259.6}
$$

如果两个状态在全部可用观测长度上满足

$$
\Pr(\mathcal O_{0:T}\mid H_0=h)
=\Pr(\mathcal O_{0:T}\mid H_0=h')
\quad\text{对所有 }T,
\tag{259.7}
$$

则它们只能被识别为同一个观测等价类；改变潜在状态标签无法改善传递熵估计。更强的不可识别性是：两个状态空间模型可满足相同的观测路径律，却具有不同的潜在转移核和不同的干预律。因而用观测后验替代真实状态，必须把状态识别假设、激励条件和噪声联合律列为外加前提。

对 FIB 图中的候选割集族 \(\mathcal C_{S\to R}\)，定义边界残余剖面

$$
\mathcal B(B)
=I\!\left(X_R(t+1);Y^-_S(t)\mid X^-_R(t),Q^-_{B,t}\right),
\qquad B\in\mathcal C_{S\to R}.
\tag{259.8}
$$

若存在有限边界 \(B\) 使 \(\mathcal B(B)=0\)，则在当前观测协议下，边界读出对目标预测已经屏蔽源历史；这是一条条件独立陈述。可以比较两个候选边界的增益

$$
\Delta_{B_1\rightsquigarrow B_2}
=\mathcal B(B_1)-\mathcal B(B_2),
\tag{259.9}
$$

但一般不能断言随边界增大而单调下降。新增边界变量若是碰撞点、含测量选择或改变了缺失机制，条件化可能反而增加互信息。只有在外加动态结构模型、无碰撞的嵌套信息族和正确的共同原因调整条件同时成立时，\(\Delta_{B_1\rightsquigarrow B_2}\ge0\) 才可作为屏蔽增益解释。由此可定义统计意义上的最小预测边界

$$
B_*\in\underset{B\in\mathcal C_{S\to R}}{\arg\min}\ |B|
\quad\text{使}\quad
\mathcal B(B)=0,
\tag{259.10}
$$

但该最小性只针对所选观测分布和有限历史，不等于物理因果边界，也不保证对未观测干预保持稳定。

可构造两个观测等价模型 \(M_1,M_2\)，满足

$$
\Pr_{M_1}(X_{0:T},Y_{0:T},Q_{B,0:T})
=\Pr_{M_2}(X_{0:T},Y_{0:T},Q_{B,0:T})
\quad\text{对所有 }T,
\tag{259.11}
$$

从而它们的全部有限阶条件互信息、传递熵和边界剖面均相同；然而对同一外加干预却可有

$$
\Pr_{M_1}\!\left(X_R(t+1)\mid do(Y_S(t)=y)\right)
\ne
\Pr_{M_2}\!\left(X_R(t+1)\mid do(Y_S(t)=y)\right).
\tag{259.12}
$$

例如一个模型可由未观测共同原因 \(C_t\) 同时驱动源和目标，另一个模型可由源到目标的直接动力学并调整噪声得到相同观测律；没有干预、共同原因测量或结构限制，传递熵只能识别预测等价类。零传递熵也不能排除被观测投影抹去、被同步采样遗漏或被边界条件固定的实际作用。

有限 FIB 词列通常使相邻窗口重叠，样本并非独立。若外加过程满足足够的混合、正概率和有限信息矩条件，在有效样本量 \(N_{\rm eff}\) 下可使用相应的块估计；在额外正则条件下才有

$$
\sqrt{N_{\rm eff}}\left(\widehat{\mathsf T}_{S\to R\mid B}-\mathsf T_{S\to R\mid B}\right)
\Longrightarrow N(0,\sigma_{\mathsf T}^2).
\tag{259.13}
$$

递归窗口的随机打乱会破坏原有接缝和时间依赖，不能作为无条件零假设；置换必须在保留 FIB 合法块、周期结构和自相关的方案内进行。重尾隐藏状态或非平稳驱动时，\(N_{\rm eff}\) 可能没有线性增长，式(259.13)不能直接套用。

本节结论是：FIB ATOM 递归能够提供观察序列的合法组合、路径、候选分隔和边界层级；条件互信息、传递熵的隐藏状态分解、观测等价类、边界残余剖面和有限样本极限，均由外加转移核、时钟、噪声、过滤器和观测协议决定。传递熵刻画预测信息，条件边界刻画给定协议下的屏蔽程度；二者都不单独证明可干预的因果方向。共同原因、碰撞条件、隐藏状态和观测投影可使同一 FIB 骨架对应不同统计律与不同干预效应。只有另行给出结构因果模型、可实施干预、识别条件和稳定的边界观测，才能把统计预测结论提升为因果结论；FIB 本身不提供这种提升。

## 260. FIB 网络上的外加线性响应、逆问题、系统辨识与因果响应统计

本节在前述静态 Green 核与占用响应之上另行加入时间扰动、外部端口和观测协议。固定一族 FIB 图或复形的组合支撑为 \(G_j=(V_j,E_j)\)。FIB ATOM 递归只提供状态、端口和允许路径的组合支撑、接缝及层级索引；状态的物理维数、边上的传播延迟、几何嵌入、耦合系数、阻尼、噪声、温度、边界、输入协议和读出滤波均为外加。

**定义 260.1（外加线性状态空间与因果响应核）。** 令 \(x_j(t)\in\mathbb R^{n_j}\) 为外加状态，\(u(t)\in\mathbb R^m\) 为端口扰动，\(y_j(t)\in\mathbb R^p\) 为观测量，考虑

$$
\dot x_j(t)=A_jx_j(t)+B_ju(t)+\eta_j(t),\qquad
y_j(t)=C_jx_j(t)+D_ju(t)+\xi_j(t).
\tag{260.1}
$$

假定 \(A_j\) 指数稳定，且内部噪声与输入独立。矩阵的零模式可由 FIB 支撑限制：\(B_j\) 的列只在指定输入端口注入，\(C_j\) 的行只读取指定输出端口，\(A_j\) 的直接非零耦合只使用声明的局部邻接；沿 FIB 路径的间接响应由矩阵乘积产生。该支撑条件不规定任何非零系数。

从零输入开始，因果脉冲响应为

$$
R_j(t)=\mathbf 1_{\{t\ge0\}}C_je^{A_jt}B_j+D_j\,\delta_0(t),
\tag{260.2}
$$

因此对小扰动 \(\delta u\)，一阶均值响应为

$$
\delta\bar y_j(t)=\int_{-\infty}^{t}R_j(t-s)\,\delta u(s)\,{\rm d}s.
\tag{260.3}
$$

时间平移不变时，其频率响应为

$$
\chi_j(\omega)=D_j+C_j({\rm i}\omega I-A_j)^{-1}B_j.
\tag{260.4}
$$

若去掉直接项后响应核可积，因果性使 \(\chi_j(z)\) 在上半平面解析；在固定 Fourier 号约定下，各标量矩阵元满足相应的 Kramers--Kronig 主值关系。因果性只约束时间支持和解析结构，FIB 路径长度不自动给出传播延迟或响应的相位。

**命题 260.2（随机输入下的响应谱与可恢复对象）。** 令 \(u,\eta_j,\xi_j\) 平稳，内部噪声与 \(u\) 独立，记 \(S_u,S_{yu},S_y\) 为相应的交叉谱和功率谱。则

$$
S_{yu}(\omega)=\chi_j(\omega)S_u(\omega),
\tag{260.5}
$$

并且

$$
S_y(\omega)=\chi_j(\omega)S_u(\omega)\chi_j(\omega)^*
+S_{\mathrm{int},j}(\omega).
\tag{260.6}
$$

若 \(\eta_j\) 是协方差为 \(Q_j\delta(t-s)\) 的白噪声，\(H_j(\omega)=({\rm i}\omega I-A_j)^{-1}\)，则

$$
S_{\mathrm{int},j}(\omega)
=C_jH_j(\omega)Q_jH_j(\omega)^*C_j^*+S_{\xi,j}(\omega).
\tag{260.7}
$$

在目标频带上 \(S_u(\omega)\) 可逆且输入与内部噪声确实独立时，完整的二阶交叉谱给出

$$
\chi_j(\omega)=S_{yu}(\omega)S_u(\omega)^{-1}.
\tag{260.8}
$$

若只观测 \(S_y\) 而没有独立输入或交叉谱，(260.6) 只能分解为响应项与内部噪声项的和，通常不能唯一恢复 \(\chi_j\)。同一线性响应和同一二阶噪声谱还可以配上不同的高阶噪声累积量，因而有不同的三阶、四阶响应统计；均值与二阶谱不等于完整路径律。

**证明。** Fourier 变换将(260.1)写为 \(\widehat y=\chi_j\widehat u+C_jH_j\widehat\eta_j+\widehat\xi_j\)。与 \(\widehat u\) 做交叉平均时，独立性消去后两项，得(260.5)；与自身做谱平均得(260.6)，白噪声协方差给出(260.7)。若 \(S_u\) 可逆，右乘其逆即得(260.8)。不同噪声分布只要保持同一二阶谱就不改变这些二阶等式，但会改变高阶累积量。\(\square\)

**命题 260.3（涨落--耗散关系的条件）。** 取外加平衡过阻尼模型

$$
\dot x(t)=-LKx(t)+Lf(t)+\eta(t),
\qquad
\langle\eta(t)\eta(s)^{\mathsf T}\rangle=2k_BT L\,\delta(t-s),
\tag{260.9}
$$

其中 \(L=L^{\mathsf T}\succeq0\)、\(K=K^{\mathsf T}\succ0\)，静态能量为 \(H(x)=\tfrac12x^{\mathsf T}Kx-f^{\mathsf T}x\)，且初态为同一温度下的平衡系综。令 \(A=-LK\)，并以 \(f\) 作为与 \(x\) 共轭的外力，则平衡协方差为

$$
\Sigma=\langle x(0)x(0)^{\mathsf T}\rangle=k_BT K^{-1},
\tag{260.10}
$$

响应和自发相关分别为

$$
R_x(t)=\mathbf 1_{\{t\ge0\}}e^{At}L,
\qquad
C_x(t)=\langle x(t)x(0)^{\mathsf T}\rangle=e^{At}\Sigma.
\tag{260.11}
$$

因而有矩阵形式的涨落--耗散恒等式

$$
R_x(t)=-\frac1{k_BT}\,\mathbf 1_{\{t\ge0\}}\frac{{\rm d}}{{\rm d}t}C_x(t).
\tag{260.12}
$$

若观测为 \(y=Ox\)，同一外力下

$$
R_y(t)=-\frac1{k_BT}\mathbf 1_{\{t\ge0\}}
\frac{{\rm d}}{{\rm d}t}\langle y(t)x(0)^{\mathsf T}\rangle.
\tag{260.13}
$$

(260.12)--(260.13) 需要平稳平衡、详细平衡、已知温度、扰动确实以共轭力进入、读出映射已校准以及相同的时间反演约定。若存在主动泵浦、非热储库、反馈、磁场下未作时间反演、隐藏耗散通道或非平衡稳态，协方差一般不能替代响应；必须另外记录相应的耗散或动力学项。FIB 递归没有给出 \(L,K,T\)、系综或共轭耦合，故不能由其自身推出涨落--耗散定律。

**定理 260.4（端口逆问题的非唯一性）。** 设参数到观测的映射为

$$
\Theta_j=(A_j,B_j,C_j,D_j,Q_j,\ldots)
\longmapsto \bigl(\chi_j,S_{y,j},\text{高阶观测律}\bigr).
\tag{260.14}
$$

即使所有频率上的 \(\chi_j\) 都无噪声地已知，内部模型仍至少有以下不可辨识自由度。

1. 对任意可逆矩阵 \(T\)，作

$$
A'_j=T A_jT^{-1},\quad B'_j=TB_j,\quad C'_j=C_jT^{-1},\quad
Q'_j=TQ_jT^{\mathsf T},
\tag{260.15}
$$

则端口响应和相应输出概率律相同。这是状态坐标的相似变换；它不等同于 FIB 顶点、物理位置或能量坐标的唯一识别。

2. 将状态分成端口可见部分 \(b\) 与内部部分 \(i\)，并令输入只作用于 \(b\)、输出只读取 \(b\)。对 \(z\) 不在谱极点上，端口传递函数只通过 Schur 补

$$
\chi_j(z)=D_j+C_b\Bigl[zI-A_{bb}
-A_{bi}(zI-A_{ii})^{-1}A_{ib}\Bigr]^{-1}B_b
\tag{260.16}
$$

出现。任何改变内部矩阵而保持自能函数

$$
\Sigma_i(z)=A_{bi}(zI-A_{ii})^{-1}A_{ib}
\tag{260.17}
$$

不变的模型都给出相同端口响应；隐藏态的噪声和高阶统计还可在不改变端口二阶谱的情况下改变内部路径律。

3. 仅给定零频静态响应更弱。对任意 \(a,b>0\) 且 \(a\ne b\)，两套单端口模型

$$
\chi_1(z)=\frac1{z+a},
\qquad
\chi_2(z)=\frac{b}{a(z+b)}
\tag{260.18}
$$

满足 \(\chi_1(0)=\chi_2(0)=1/a\)，但其因果核分别为 \(e^{-at}\) 与 \((b/a)e^{-bt}\)（\(t\ge0\)），具有不同记忆时间和瞬态统计。故静态 Green 响应不能唯一确定时间响应。

若两套有限维有理模型都为极小实现，即 \((A,B)\) 可控且 \((C,A)\) 可观，且完整有理传递函数与直接项相同，则它们至多由(260.15)的相似变换联系；极小性本身仍没有把相似坐标映射回 FIB 的物理参数。\(\square\)

**实验设计与可识别性边界。** 在给定有限维模型阶数和目标频带时，恢复端口传递函数至少需要：

1. 各独立输入端口具有持续激励；随机设计可要求 \(S_u(\omega)\succeq cI\)（\(c>0\)）覆盖目标频带，并保存输入与输出的时间配对；
2. \((A_j,B_j)\) 在目标模态上可控、\((C_j,A_j)\) 可观，即

$$
\operatorname{rank}[B_j,A_jB_j,\ldots,A_j^{n_j-1}B_j]=n_j,
\quad
\operatorname{rank}\begin{bmatrix}C_j\\C_jA_j\\\vdots\\C_jA_j^{n_j-1}\end{bmatrix}=n_j;
\tag{260.19}
$$

3. 时间零点、端口增益、采样带宽、边界条件和读出滤波已校准，并有重复实验将内部噪声与输入相关项分开；
4. 若要检验(260.12)，需在无外驱动的同一平衡系综上同时测量自发相关与小幅共轭扰动响应，改变温度或边界后仍须重新核对平衡和详细平衡条件。

只有端口有限频率的离散读数时，响应尾、极快的直接项、隐藏极点和近似相消仍可互相混淆；只有单一静态扰动时，不能区分不同记忆核。增加端口激励、频率扫掠、内部传感器和边界切换可以缩小等价类，但若内部态始终不可控或不可观，仍只能识别端口等价类。跨图族的随机参数还需要先给出参数系综 \(\Pi_j\)；平均响应

$$
\overline\chi_j(\omega)=\int\chi_{j,\vartheta}(\omega)\,\Pi_j({\rm d}\vartheta)
\tag{260.20}
$$

不决定响应的方差、尾部或高阶联合律。FIB 提供的路径、端口和层级只能用于安排这些干预与读出，不能替代持续激励、可控可观、平衡系综或噪声模型。

**结论。** 给定外加状态方程和端口协议，FIB 网络可以承载一个因果响应核、输入--输出交叉谱以及条件性的涨落--耗散关系；在独立且满秩的输入激励下，交叉谱可恢复端口传递函数。逆问题的真可识别对象是端口观测等价类：相似坐标、隐藏内部自能、有限频带、静态压缩和未观测高阶噪声都会保留相同部分数据而改变内部动力学。因而 FIB ATOM 递归只提供支撑、路径、端口和层级骨架；物理响应、记忆时间、耗散、温度、噪声、因果观测和系统辨识结论均由外加模型与实验设计决定，不能由递归单独推出。


## 261. FIB 网络上的外加两相多孔介质渗流、毛细滞回与突破统计

固定一族 FIB 图 (G_j=(V_j,E_j))，把顶点解释为孔腔、边解释为候选喉道。FIB ATOM 递归只提供孔腔的组合邻接、接缝、可行路径、割集和层级索引；孔隙体积、喉道半径、空间嵌入、润湿性、界面张力、黏度、渗透率、重力、注入协议、边界和观测尺度均须外加。图上的边数和路径长度不自动等于孔隙长度、孔隙率或渗流时间。

对润湿相 (w) 与非润湿相 (n)，令 (S_w,S_n) 为饱和度，(phi) 为外加孔隙率，(q_alpha) 为相流量。一个外加两相守恒模型为

$$
\phi\,\partial_t S_\alpha+\nabla\!\cdot q_\alpha=s_\alpha,
\qquad S_w+S_n=1,
\qquad \alpha\in\{w,n\}.
\tag{261.1}
$$

在达西尺度，给定压力 (p_alpha)、重力势和相对渗透率 (k_{r\alpha})，可写

$$
q_\alpha=-\frac{k\,k_{r\alpha}(S_w)}{\mu_\alpha}
\bigl(\nabla p_\alpha-\rho_\alpha g\bigr),
\tag{261.2}
$$

其中绝对渗透率 (k)、相对渗透率曲线、黏度和密度是外加本构。毛细压差满足

$$
p_c(S_w)=p_n-p_w,
\qquad
p_c\ \text{由孔径分布、接触角和界面张力给定}.
\tag{261.3}
$$

因此同一 FIB 邻接可在亲水、疏水或混合润湿合同下产生不同的相占据、流量分配和压力降。

若令总流量 (q_t=q_w+q_n)，总动度与分流函数为

$$
\lambda_\alpha(S_w)=\frac{k_{r\alpha}(S_w)}{\mu_\alpha},
\qquad
\lambda_t=\lambda_w+\lambda_n,
\qquad
f_w=\frac{\lambda_w}{\lambda_t},
\tag{261.4}
$$

在一维无重力、无源项的外加极限中，饱和度可满足 Buckley--Leverett 型方程

$$
\phi\,\partial_t S_w+\partial_x\!\bigl(q_t f_w(S_w)\bigr)=0.
\tag{261.5}
$$

其特征速度为 (q_t f_w'(S_w)/\phi)，激波速度为

$$
s=\frac{q_t[f_w(S_2)-f_w(S_1)]}{\phi(S_2-S_1)}.
\tag{261.6}
$$

冲击位置、前缘展宽和残余饱和度依赖相对渗透率、色散、边界和注入历史；FIB 路径只给候选连通关系，不能给出 (f_w) 或前缘速度。

在孔喉尺度，单个界面通过半径 (r_e) 的喉道所需的毛细阈值可近似为

$$
p_{c,e}=\frac{2\gamma\cos\vartheta_e}{r_e},
\tag{261.7}
$$

其中界面张力 (gamma)、接触角 (\vartheta_e) 和半径 (r_e) 均为外加。准静态注入时，按最小可入侵阈值选择边可形成 invasion-percolation 型过程；阈值联合律、并列阈值的打破规则和入口边界决定簇形状。相同 FIB 图若把半径取为常数，前沿可能近似规则推进；若半径重尾并有相关空间组织，则可出现滞后、指进和宽突破时间尾。

令 (T_b) 为非润湿相首次到达指定出口割集的时间。对给定外加渗透率场 (omega) 与注入协议，首达分布可以写成

$$
\Pr(T_b>t)=\int \Pr_\omega(T_b>t)\,\Pi(\mathrm d\omega),
\tag{261.8}
$$

其中 (Pi) 是孔喉半径、润湿性和局部渗透率的联合系综。先固定 (omega) 再取大图极限得到 quenched 统计，先对 (Pi) 平均再取极限得到 annealed 统计；两者通常不同，且均值、分位数和稀有早突破概率不能互相替代。

动态毛细效应可由弛豫时间 (	au_c) 外加为

$$
p_c(t)=p_c^{\rm eq}(S_w(t))+\tau_c\,\partial_t S_w(t),
\tag{261.9}
$$

或以界面曲率和相场变量给出。排驱和吸入使用不同的接触角与扫描曲线时，(S_w\mapsto p_c) 具有滞回；同一饱和度在上扫和下扫可能对应不同压力、相对渗透率和有效电导。滞回不能从单个 FIB 接缝标签推出，必须声明历史、成核规则和界面耗散。

在连通孔隙上对示踪剂浓度 (c_\alpha) 另加对流—弥散—反应合同，可写

$$
\phi S_\alpha\partial_t c_\alpha
+\nabla\!\cdot(q_\alpha c_\alpha)
=\nabla\!\cdot(\phi S_\alpha D_\alpha\nabla c_\alpha)
-R_\alpha(c_w,c_n)+\zeta_\alpha.
\tag{261.10}
$$

弥散张量、吸附、反应项和噪声是外加；通道化、旁路和死端孔腔会使突破曲线多峰。只观测出口一阶矩时，机械弥散、反应衰减和未观测滞留区可以互相补偿，无法唯一确定内部流场。

若外加孔喉阈值具有重尾或长程相关，出口通量与突破时间可能满足有限尺寸形式

$$
\Pr(T_b>t\mid L,\Theta)\approx t^{-\alpha_\Theta}
\Psi_\Theta\!\left(t/t_c(L,\Theta)\right),
\qquad t_c(L,\Theta)\sim L^{z_\Theta},
\tag{261.11}
$$

但指数 (alpha_\Theta,z_\Theta) 由孔径联合律、驱动、黏性比、润湿性、边界和极限次序共同决定。轻尾独立孔喉、重尾孔喉和强相关层状孔喉可以在相同 FIB 组合图上分别给出窄峰、幂律尾和近确定性突破；因此拟合一条幂律不能证明 FIB 递归产生临界渗流。

实际传感器读数是饱和度、压力、局部电阻率和示踪剂浓度的投影，例如

$$
Y_a(t)=\int h_a(x)S_w(x,t)\,\mathrm dx
+\int_0^t g_a(t-s)q_n^{\rm out}(s)\,\mathrm ds+\eta_a(t).
\tag{261.12}
$$

探针位置、带宽、接触电阻和共同环境会改变可见的前缘、滞回面积和突破尾。两个外加模型可以具有相同平均压降与出口总流量，却具有不同的内部相占据、局部旁路和稀有早突破风险；联合压力—饱和度—示踪剂观测才可能缩小该观测等价类。

因此，FIB ATOM 递归在两相多孔介质问题中只提供孔腔与喉道的组合支撑、候选连通路径、割集和层级骨架；孔隙几何、润湿性、界面张力、相对渗透率、毛细阈值、驱动、相变历史、弥散反应、无序系综、边界及观测协议均须外加。毛细入侵、指进、滞回、突破时间、quenched/annealed 差异和幂律尾只有在这些条件明确后才是模型统计结论，不能由 FIB 递归单独推出。


## 262. FIB 光子晶格与腔量子电动力学上的外加 Purcell 辐射、光子输运及计数统计

固定一族 FIB 图或细胞复形 \(G_j=(V_j,E_j)\)，在顶点、胞腔或端口附加光学模式，并在若干位置放置两能级发射体。FIB ATOM 递归只给出组合支撑、邻接、缺陷接缝、传播路径、输入输出端口和层级索引；介电函数、磁导率、空间嵌入、晶格尺度、边界、偶极矩、失谐、泵浦、损耗和探测器响应均须外加。

离散光子模式的二次 Hamiltonian 可写为

$$
H_{\rm ph}=\hbar\sum_{u\in V_j}\omega_u a_u^\dagger a_u
+\hbar\sum_{(u,v)\in E_j}
\left(J_{uv}a_u^\dagger a_v+J_{uv}^*a_v^\dagger a_u\right).
\tag{262.1}
$$

FIB 邻接至多约束 (J) 的非零支撑；(omega_u)、(J_{uv}) 的数值和相位由材料、偏振、几何与边界决定。连续模型还需解外加 Maxwell 本征问题

$$
\nabla\times\mu^{-1}(\mathbf r)\nabla\times\mathbf E_\nu(\mathbf r)
=\frac{\omega_\nu^2}{c^2}\varepsilon(\mathbf r)\mathbf E_\nu(\mathbf r).
\tag{262.2}
$$

因此节点度、递归深度和路径条数不能单独决定带隙、群速度、模体积或腔品质因数。

开放光子网络的推迟 Green 函数与端口衰减矩阵可写成

$$
G_j^R(\omega)=\left[(\omega+{\rm i}0^+)I-h_j-sum_\alpha\Sigma_\alpha^R(\omega)\right]^{-1},
\qquad
\Gamma_\alpha={\rm i}(\Sigma_\alpha^R-\Sigma_\alpha^A).
\tag{262.3}
$$

局域态密度和弱耦合电偶极辐射率为

$$
\rho(\mathbf r,\omega)=-\frac1\pi\operatorname{Im}\operatorname{Tr}G^R(\mathbf r,\mathbf r;\omega),
\tag{262.4}
$$

$$
\Gamma_e=\frac{2\omega_e^2}{\hbar\varepsilon_0c^2}
\mathbf d_e^*\!\cdot\operatorname{Im}G^R(\mathbf r_e,\mathbf r_e;\omega_e)\!\cdot\mathbf d_e,
\qquad F_P=\Gamma_e/\Gamma_{\rm hom}.
\tag{262.5}
$$

\(F_P\) 由 Green 函数谱密度、偶极方向、失谐、模体积和参考介质共同决定；FIB 回路数不提供这些量。带边、缺陷腔和高品质因数可使态密度尖峰、辐射抑制或长记忆同时出现。

单发射体与缺陷腔在截断近似下满足 Jaynes--Cummings Hamiltonian

$$
H_{\rm JC}=\hbar\omega_c a^\dagger a+\hbar\omega_e\sigma^+\sigma^-
+\hbar g(a^\dagger\sigma^-+a\sigma^+),
\qquad g=-\frac{\mathbf d_e\cdot\mathbf E_c(\mathbf r_e)}\hbar.
\tag{262.6}
$$

若腔泄漏、辐射和纯退相干率为 \(\kappa,\gamma,\gamma_\phi\)，一个外加主方程为

$$
\dot\rho=-\frac{{\rm i}}\hbar[H_{\rm JC}+H_{\rm drv},\rho]
+\kappa\mathcal D[a]\rho+\gamma\mathcal D[\sigma^-]\rho
+\gamma_\phi\mathcal D[\sigma^+\sigma^-]\rho+\mathcal L_{\rm pump}\rho.
\tag{262.7}
$$

弱耦合、近共振且腔线宽主导时可出现 \(\Gamma_{\rm cav}\) 与 \(g^2/\kappa\) 同阶的 Purcell 增强；强耦合时则可能出现真空 Rabi 分裂。交叉位置和谱峰可分辨性依赖 \(g,\kappa,\gamma,\gamma_\phi\)、失谐及探测带宽。

多发射体的环境介导集体衰减矩阵为

$$
\Gamma_{mn}=\frac{2\omega_e^2}{\hbar\varepsilon_0c^2}
\mathbf d_m^*\!\cdot\operatorname{Im}G^R(\mathbf r_m,\mathbf r_n;\omega_e)\!\cdot\mathbf d_n.
\tag{262.8}
$$

其本征组合给出超辐射和亚辐射模。相同 FIB 邻接可以因相对位置、传播相位、偶极取向、无序和端口边界不同而产生亮模、暗模或近简并峰。

端口输入输出关系和散射矩阵可写成

$$
 b_{\alpha,\rm out}=b_{\alpha,\rm in}+\sqrt{\kappa_\alpha}a_\alpha,
\qquad
 S_{\alpha\beta}(\omega)=\delta_{\alpha\beta}
-{
m i}\sqrt{\kappa_\alpha\kappa_\beta}[G^R(\omega)]_{\alpha\beta}.
\tag{262.9}
$$

存在一条 FIB 路径只表示候选支撑，不保证非零透射、共振增强或特定群延迟；边界截断和端口自能还会反向改变腔线宽与 Purcell 因子。

若 (N_\alpha(t)) 记录端口光子数，倾斜 Liouvillian 的计数项可写为

$$
\mathcal L_{\boldsymbol\chi}\rho=\cdots+\sum_\alpha\kappa_\alpha
\left(e^{{\rm i}\chi_\alpha}a_\alpha\rho a_\alpha^\dagger
-\frac12\{a_\alpha^\dagger a_\alpha,\rho\}\right),
\tag{262.10}
$$

并定义

$$
\theta(\boldsymbol\chi)=\lim_{t\to\infty}\frac1t
\log\operatorname{Tr}\rho_{\boldsymbol\chi}(t),
\qquad
\frac{C_{\alpha_1\cdots\alpha_k}}t
=\left.\partial_{i\chi_{\alpha_1}}\cdots\partial_{i\chi_{\alpha_k}}\theta\right|_{\boldsymbol\chi=0}.
\tag{262.11}
$$

这些导数给出平均计数、shot noise 和高阶累积量；平均光强不能确定完整计数律。二阶相关函数

$$
 g_\alpha^{(2)}(\tau)=
\frac{\langle b_{\alpha,\rm out}^\dagger(0)b_{\alpha,\rm out}^\dagger(\tau)
 b_{\alpha,\rm out}(\tau)b_{\alpha,\rm out}(0)\rangle}
{\langle I_\alpha\rangle^2}
\tag{262.12}
$$

可呈现 Poisson、反聚束或聚束，但类别取决于驱动、饱和、损耗、退相干、泵浦噪声和初态。

在带边、带隙或高品质因数腔附近，发射体振幅满足外加记忆方程

$$
\dot c_e(t)=-{\rm i}\omega_e c_e(t)-\int_0^tK(t-s)c_e(s)\,\mathrm ds,
\qquad K(\tau)=\int_0^\infty J(\omega)e^{-{
m i}\omega\tau}\,\mathrm d\omega.
\tag{262.13}
$$

平坦谱密度可给出 Markov 指数衰减；带隙、van Hove 奇点或高 \(Q\) 腔可能产生束缚态、部分剩余激发和非指数尾。有限 FIB 图的谱峰不自动等于无限周期光子晶体的带边指数，图族、边界与极限次序必须另行声明。

实际计数是内部跳跃经过滤波后的投影：

$$
Y_\alpha(t)=\int h_\alpha(t-s)\,dN_\alpha(s)+\eta_\alpha(t),
\tag{262.14}
$$

其中 \(h_\alpha\) 包含滤波、死时间、时间抖动和收集效率。不同内部腔耦合与闪烁机制可在有限带宽下给出相同平均计数和二阶相关；探测端口又通过 \(\Sigma_\alpha\) 改变系统线宽。因此，Purcell 增强、非 Markov 衰减、超/亚辐射、光子反聚束和全计数统计均须在外加材料、动力学、端口和观测协议明确后解释。

因此，FIB ATOM 递归在光子晶格与腔量子电动力学中只提供光学自由度的组合支撑、候选路径、缺陷接缝、输入输出端口和层级骨架；Maxwell 参数、嵌入尺度、边界、模体积、品质因数、偶极与失谐、耦合与退相干、泵浦储库、Green 函数、计数协议及图族极限均须外加。不存在由 FIB 递归单独决定的普适光子辐射或计数定律。
## 263. FIB 网络/复形上的外加海洋重力波、非线性色散与异常巨浪极值统计

**定义 263.1（FIB 波支持与外加海洋模型）。** 令 \(\mathcal K_j=(V_j,E_j,\partial_j,\mathcal P_j)\) 为第 \(j\) 层 FIB 复形：\(V_j\) 是顶点，\(E_j\) 是有向边，\(\partial_j\) 给出边端点，\(\mathcal P_j\) 标记可连接的端口。若以端口粘合记号表示递归，则可写成

$$
\mathcal K_{j+1}=\mathcal K_j\mathop{\cup}_{\mathcal P_j}\mathcal K_{j-1},
$$

其中等式只表示组合拼接的规则；具体粘合映射由所采用的 FIB ATOM 定义给出。由 \(\mathcal K_j\) 可计算邻接、路径、割集、端口和层级关系，也可得到关联矩阵 \(B_j\)。为在其上讨论海洋波，另需给每条边赋坐标 \(x_e\)、长度 \(\ell_e\)、水深 \(h_e\)、密度 \(\rho_e\)、流速 \(U_e\)、阻尼和边界条件，并给端口指定入射谱、反射或散射规则。这些量不由 FIB 递归给出。

**线性色散的外加接口。** 在窄带、小振幅和局部均匀水深假设下，边 \(e\) 上的线性重力—毛细波色散可写为

$$
\omega_e^{\pm}(k)
=U_e k\pm\sqrt{\left(gk+\frac{\sigma_e}{\rho_e}k^3\right)\tanh(kh_e)},
$$

其中 \(g\) 是重力加速度，\(\sigma_e\) 是表面张力；若忽略毛细力则令 \(\sigma_e=0\)。因此浅水极限 \(kh_e\ll1\) 给出

$$
\omega_e^{\pm}(k)\simeq U_e k\pm\sqrt{gh_e}\,k,
$$

而深水重力极限 \(kh_e\gg1\)、\(\sigma_e=0\) 给出 \(\omega_e^{\pm}(k)\simeq U_e k\pm\sqrt{gk}\)。在给定边长和端口条件以后，带权图拉普拉斯 \(\Delta_j^{\ell}\) 的模态满足

$$
\Delta_j^{\ell}\phi_{j,r}=\mu_{j,r}\phi_{j,r},
$$

并由另外指定的边内坐标与顶点条件把 \(\mu_{j,r}\) 映射成波数 \(k_{j,r}\)。于是网络模态频率是 \(\omega_e^{\pm}(k_{j,r})\) 或其端口耦合后的共振根。FIB 只决定哪些模态可由共同路径和端口相遇；\(\ell_e,h_e,U_e,g,\rho_e,\sigma_e\) 以及 \(\mu\mapsto k\) 的实现决定实际频率。改变水深或流速而保持同一 FIB 复形，就能改变相速、群速、反射阈值和共振位置。

**定义 263.2（网络包络方程）。** 选定载波 \((k_p,\omega_p)\)，令 \(A_e(x,t)\) 为边 \(e\) 上的慢变复包络。多尺度展开只有在额外的弱非线性、窄带和尺度分离假设下才可给出

$$
 i\bigl(\partial_t+v_{g,e}\partial_x\bigr)A_e
 +P_e\partial_x^2A_e+Q_e|A_e|^2A_e
 =i\mathcal D_e[A_e]+\zeta_e,
$$

其中 \(v_{g,e}=\partial_k\omega_e(k_p)\)，\(P_e=\tfrac12\partial_k^2\omega_e(k_p)\)，\(Q_e\) 是由水深、载波、自由波与束缚谐波约化得到的非线性系数，\(\mathcal D_e\) 和 \(\zeta_e\) 分别表示阻尼、记忆项与随机风浪驱动。在顶点 \(v\) 处可选取连续性和通量条件，或直接给出

$$
A^{\mathrm{out}}_v(\omega)=S_v(\omega)A^{\mathrm{in}}_v(\omega).
$$

端口相连关系来自 \(\mathcal P_j\)，但散射矩阵 \(S_v\) 的相位、损耗、频率依赖和是否满足 \(S_v^*S_v=I\) 均需由外加流体模型或测量确定。因而不能把 FIB 的端口拼接自动解释为无损波导或能量守恒。

若暂时去掉右侧项并取均匀边，聚焦情形 \(P_eQ_e>0\) 的平面波

$$
 A=A_0\exp\!\left(iQ_e|A_0|^2t\right)
$$

对波数扰动 \(q\) 的增长率满足

$$
 \Gamma_e(q)^2
 =P_e^2q^2\left(2\frac{Q_e}{P_e}|A_0|^2-q^2\right).
$$

故当 \(0<q^2<2(Q_e/P_e)|A_0|^2\) 时存在调制不稳定性，最大增长率为 \(|Q_e||A_0|^2\)，对应 \(q^2=(Q_e/P_e)|A_0|^2\)。在以

$$
 \xi=x|A_0|\sqrt{Q_e/P_e},
 \qquad
 \tau=Q_e|A_0|^2t
$$

归一化的理想无阻尼、无限边模型中，局域聚焦解可写成

$$
 A(x,t)=A_0e^{i\tau}
 \left[1-\frac{4(1+2i\tau)}{1+4\xi^2+4\tau^2}\right],
$$

其中心包络幅度达到背景的三倍。有限 FIB 网络中的端口反射、有限长度、耗散和随机驱动会改变该解；“三倍”是上述约化方程的特定解，不是 FIB 的普适放大定律。

**线性海况的基准极值律。** 设观测协议从表面位移 \(\eta\) 提取相邻波高 \(H_r\)，并定义单边谱矩

$$
 m_n=\int_0^\infty \omega^nS_\eta(\omega)\,d\omega,
 \qquad H_s=4\sqrt{m_0}.
$$

在零均值、窄带、高斯线性海况下，波高近似服从瑞利尾

$$
 \Pr(H>h)=\exp\!\left(-\frac{h^2}{8m_0}\right),
 \qquad
 \Pr\!\left(\frac{H}{H_s}>z\right)=e^{-2z^2}.
$$

这里 \(S_\eta\) 由入射风浪谱和网络传递函数共同决定，例如

$$
 S_{\eta,j}(\omega)=|G_j(\omega)|^2S_{\mathrm{in}}(\omega),
$$

而 \(G_j\) 依赖边长、深度、阻尼、端口散射和观测位置。FIB 的递归可以改变路径干涉和候选共振的组合位置，却不能指定 \(S_{\mathrm{in}}\)、\(G_j\) 或高斯性。

对 \(Z_r=H_r/H_s\) 和 \(M_n=\max_{1\le r\le n}Z_r\)，若波列满足足够的混合条件且极值指数为 \(\vartheta\in(0,1]\)，当

$$
 n\Pr(Z_1>u_n)\longrightarrow\tau
$$

时有

$$
 \Pr(M_n\le u_n)\longrightarrow e^{-\vartheta\tau}.
$$

在线性瑞利基准且 \(\vartheta=1\) 时，取

$$
 b_n=\sqrt{\frac12\log n},
 \qquad a_n=\frac1{4b_n},
$$

则

$$
 \Pr\!\left(\frac{M_n-b_n}{a_n}\le x\right)
 \longrightarrow \exp(-e^{-x}),
$$

极值为冈贝尔型。若观测次数与 FIB 层规模成正比且 \(n_j\sim C\varphi^j\)，其中 \(\varphi\) 是相应递归的增长率，则在这些额外抽样假设下

$$
 b_{n_j}\sim\sqrt{\frac{j\log\varphi}{2}}.
$$

这个关系只说明递归增长可通过样本数量改变最大值的典型尺度；它没有说明单次波高尾一定是瑞利尾。端口回返、同一路径上的连续观测和局域共振会造成簇集，使 \(\vartheta<1\)，此时有效样本量约为 \(\vartheta n\)。

**非线性尾与异常巨浪。** 令载波陡度 \(\epsilon=k_pa_0\)，谱宽为 \(\Delta k\)，可定义外加的调制不稳定指标

$$
 \mathrm{BFI}=\frac{\epsilon}{\Delta k/k_p},
$$

以及超额峰度

$$
 \kappa_4=\frac{\mathbb E[\eta^4]-3m_0^2}{m_0^2}.
$$

\(\mathrm{BFI}\)、\(\kappa_4\) 随 \(P,Q\)、水深、风浪谱、阻尼和观测窗改变；它们升高时可能出现比瑞利基准更肥的尾，但“可能”必须由给定模型或数据检验，不能由 FIB 递归单独推出。若在阈值 \(u\) 以上只保留超额量，常用外加拟合为广义帕累托形

$$
 \Pr(Z-u\le y\mid Z>u)
 \simeq
 1-\left(1+\xi\frac y\beta\right)^{-1/\xi},
 \qquad 1+\xi y/\beta>0,
$$

其中 \(\xi\) 和 \(\beta\) 由动力学、随机场与数据估计；\(\xi=0\) 取连续极限得到指数尾。不同的 \(\xi\) 分别可产生有界、指数型或重尾极值域，FIB 的路径计数并不选择其中任何一种。

**命题 263.3（FIB 支撑的统计非唯一性）。** 存在同一 \(\mathcal K_j\) 上具有不同海洋统计律的外加模型。

**证明。** 固定 \(\mathcal K_j\)、端口和路径集合。模型甲取平坦水深、线性高斯入射谱、\(Q_e=0\) 与独立观测，得到瑞利单波高尾和冈贝尔最大值极限。模型乙保持同一组合支撑而取 \(P_eQ_e>0\)、有限端口反射、相关随机驱动及非零阻尼；调制不稳定性、簇集和非高斯峰度可以改变单波高尾、极值指数和最大值归一化。也可仅改变 \(h_e\) 或 \(U_e\)，由线性色散式立即得到不同相速与频率。两模型的 FIB 数据完全相同而统计结论不同，故 FIB 不能唯一推出海洋波速、非线性色散系数或异常巨浪尾律。\(\square\)

本节的可复用接口是：FIB 递归提供组合支撑、路径多重性、端口连接和层级增长；外加几何与水深把组合模态映射为波数，外加流体方程给出色散与非线性，外加随机场和观测协议给出谱矩、峰度、簇集与极值统计。浅水或深水极限、长时间极限、弱非线性极限、层数 \(j\to\infty\) 以及观测数趋于无穷都必须逐项声明；任何一个未指定的极限都不能由 FIB ATOM 递归补足。


## 264. FIB 网络上的外加等离子体波、Landau 阻尼、波粒共振与涨落统计

固定 FIB 图族，在边、顶点、胞腔或端口附加带电粒子和电磁场。FIB 只规定组合支撑、候选传播路径、接缝、端口和层级索引；粒子分布函数、空间尺度、背景磁场、介电参数、碰撞算子、储库、边界、噪声和观测协议均须外加。线性化动理学可概括为

$$
(∂ₜ+v·∇ₓ+q(E₀+v×B₀)·∇ᵥ/m)f₁
=−q(E₁+v×B₁)·∇ᵥf₀/m+C[f₁]+ξ,
\\
J₁=∑ₛqₛ∫v f₁ₛ,d v. \\
(264.1)
$$

介电响应的因果积分在共振分母 ω−k·v 上需要 Landau 轮廓。色散根的虚部由共振速度处的分布斜率决定：单调 Maxwell 分布通常给出阻尼，束流或鼓包分布可以给出增长。磁化系统还需满足

$$
ω−k∥v∥−nΩₛ=0,
\\
Ωₛ=qₛB₀/mₛ. \\
(264.2)
$$

回路存在不意味着某个回旋谐波必然共振；传播角、温度、极化和回旋半径都是外加。

随机相位弱波幅下，准线性速度扩散可写成

$$
∂ₜF=∂ᵥ(D∂ᵥF),
\\
D(v)=π∑ₖ(q²/m²)|Eₖ|²δ(ωₖ−k v). \\
(264.3)
$$

波粒俘获、解俘获、模间散射和端口泄漏会造成平台化、啁啾、间歇爆发及非高斯尾。有限 FIB 图的离散模若没有外加连续速度谱或耗散，通常只产生相干交换和复现；不可逆 Landau 衰减需要连续谱、粗粒化、碰撞或开放端口极限。

将路径主导模组成向量 a，可用

$$
ȧ=M a+B u+ξ,
\\
ḊΣ=MΣ+ΣM†+Q. \\
(264.4)
$$

描述线性网络的均值与协方差。FIB 邻接只限制 M 的稀疏支撑，不决定复相位、阻尼矩阵或端口自能。观测特征泛函的高阶导数给出全部相关和累积量；高斯噪声与有限粒子跳跃噪声可以有相同二阶谱而有不同偏度、峰度和稀有事件尾。故 FIB 不能单独推出 Landau 阻尼率、波粒共振分布或等离子体涨落定律。

## 265. FIB 复形上的外加云微物理、冰晶成核与相变等待时间统计

固定 FIB 复形并把胞腔或接缝作为候选微物理位置。递归只给组合邻接、路径、边界和层级；温度、压力、湿度、风场、气溶胶化学、接触角、界面能、增长和沉降律均须外加。过饱和度可定义为

$$
s=qᵥ/qᵥₛ(T,p)−1. \\
(265.1)
$$

异质冰成核率可以用势垒形式表示

$$
J(x,t;χ)=A(χ,T,p,s)\exp[−ΔG‡(χ,T,p,s)/(kᴮT)],
\\
ΔG‡=f(θ)16πγᵢw³/[3(ρᵢΔμ)²]. \\
(265.2)
$$

活性位点、接触角和化学组分的联合律不由 FIB 接缝给出。若条件于温湿度、气溶胶和相变历史后成核是条件 Poisson 过程，则总强度 Λ(t) 下的首个等待时间满足

$$
P(τ>t∣H)=\exp[−∫₀ᵗΛ(s∣Hₛ)ds],
\\
p(τ=t∣H)=Λ(t∣H)P(τ>t∣H). \\
(265.3)
$$

共享水汽库、共同温湿度脉冲和长记忆湍流会把边缘过程变为 Cox 或抑制点过程，产生多峰、伸缩指数或幂律尾。

冰晶增长、沉降、碰并和融化还需外加粒径输运方程，例如

$$
∂ₜnᵢ+∇·[(u−vₜ(r))nᵢ]+∂ᵣ[ṙ nᵢ]=Nᵢ−Lᵢ+Cᵢ,
\\
qᵢ=∫(4π/3)ρᵢr³nᵢ,d r. \\
(265.4)
$$

同一首个成核时间可以对应不同粒径谱和沉降通量。若许多候选点足够混合且单点在最早时间 t₀ 附近满足 P(τ≤t₀+u) 约为 c uᵝ，则最早事件的尺度可呈 Weibull 型

$$
P[N^(1/β)(τₘᵢₙ−t₀)>x]→\exp(−θc xᵝ). \\
(265.5)
$$

θ 是由共享环境造成的极值指数。若路径边时间 τₑ 外加，则相变传播时间是所有合法路径的最小和；其大偏差速率函数由边时间系综、相关结构和边界决定。

降温实验只有在给定降温曲线和删失规则后才能反推出成核温度分布。相机、雷达和采样器读取粒径谱的卷积投影；相同反射率可由不同数浓度和粒径组合产生。因而冰晶首达、成核极值、等待时间尾和相变大偏差都依赖外加热力学、随机环境、动力学、尺度极限和观测协议，不能由 FIB 复形递归单独推出。


## 266. FIB 网络上的外加激子—光子极化子输运、非平衡凝聚与相关统计

固定一族 FIB 图或复形，在顶点、胞腔或边界端口上附加光子模和激子模。FIB ATOM 递归只给出组合支撑、邻接、缺陷接缝、传播路径、端口和层级索引；介电材料、激子能级、光子能级、Rabi 耦合、相互作用、泵浦、损耗、温度、无序和探测器响应均须外加。

离散耦合模的二次 Hamiltonian 可写为

$$
H₂=ℏ∑ᵥωᶜᵥ aᵥ†aᵥ+ℏ∑ᵥωˣᵥ bᵥ†bᵥ
+ℏ∑ᵥΩᵥ(aᵥ†bᵥ+bᵥ†aᵥ)+ℏ∑₍ᵤ,ᵥ₎Jᵤᵥaᵤ†aᵥ. \\
(266.1)
$$

FIB 邻接至多约束 J 的非零支撑；能级、相位和 Rabi 耦合不由路径数决定。单个局部模式的混合支分裂为

$$
E±=ℏ(ωᶜ+ωˣ)/2±ℏ√[(δ/2)²+Ωᴿ²],
\\
δ=ωᶜ−ωˣ. \\
(266.2)
$$

混合系数、有效质量和群速度依赖外加色散与边界嵌入。相同 FIB 图在不同失谐和材料参数下可以从光子样态切换到激子样态。

泵浦—耗散极化子场可用随机 Gross–Pitaevskii 型方程表示

$$
ｉ∂ₜψᶜ=[ωᶜ−ｉκᶜ/2−DᶜΔ+gᶜ|ψᶜ|²]ψᶜ+Ωᴿψˣ+F+ξᶜ,
\\
ｉ∂ₜψˣ=[ωˣ−ｉγˣ/2+gˣ|ψˣ|²]ψˣ+Ωᴿψᶜ+ξˣ. \\
(266.3)
$$

泵浦 F、损耗 κ 和 γ、相互作用 g、色散 D、噪声联合律以及端口边界均为外加。稳态密度由泵浦超过损耗的条件、饱和和粒子输运共同决定；线性增益等于损耗只是局部阈值条件，不自动等同于平衡 Bose 凝聚。

在空间均匀近似中，稳态相干场 ψ₀ 的线性化谱由 Bogoliubov 矩阵决定。若某个波数的增长率 Re λ(k) 大于零，均匀态发生调制不稳定性；波数带、斑图尺度和饱和振幅由 D、g、泵浦、损耗及图谱隙共同决定。FIB 层级深度不能替代物理波数或连续空间尺度。

极化子占据的凝聚候选指标可以写成

$$
liminfⱼ N₀ⱼ/Nⱼ>0,
\\
 g¹ᵤᵥ(t)=⟨ψᵤ†(t)ψᵥ(t)⟩/[⟨nᵤ⟩⟨nᵥ⟩]¹ᐟ². \\
(266.4)
$$

非平衡有限图上的宏观低模占据、长程相干、涡旋和碎片化是不同事件；共同泵浦噪声、暗态和无序会改变它们的相关长度。

输出端口的光子计数可用倾斜 Liouvillian 或随机跳跃过程描述。若 Nₐ(t) 为端口计数，长时计数生成率 Θ(χ) 的导数给出平均流、shot noise 和高阶累积量；二阶相干函数 g²(τ) 可以表现为聚束、近 Poisson 或反聚束。均值强度和单一谱峰不能唯一确定极化子内部占据、相位扩散或暗态切换。

实际观测是内部场经过空间、频率和时间滤波的投影

$$
Yₐ(t)=∫hₐ(x,ω)ψ(x,t),dx,dω+ηₐ(t). \\
(266.5)
$$

带宽、死时间、收集效率和探针反作用会改变可见的 g¹、g²、线宽和计数尾。相同端口平均输出可以来自不同的 Rabi 耦合、无序势和泵浦噪声；增加端口、偏振和时间分辨率只能缩小观测等价类。

因此，FIB ATOM 递归在激子—光子极化子问题中只提供组合自由度、候选传播路径、端口和层级骨架；能级、色散、耦合、非线性、泵浦、耗散、温度、无序、相干和探测协议均须外加。极化子输运、非平衡凝聚、调制失稳、涡旋、相干函数和计数统计都是给定外加模型后的条件结论，不能由 FIB 递归单独推出普适定律。


## 267. FIB 网络上的外加宇宙线、高能粒子级联、随机输运与能量沉积极值统计

固定一族 FIB 复形并给出外加空间嵌入。FIB ATOM 递归只提供组合邻接、接缝、候选传播路径、输入输出端口和层级骨架；它不提供长度、时间标度、介质密度、核素组成或粒子相互作用。宇宙线初级粒子的能谱、成分、入射角、磁场偏转和边界条件均须另加。

粒子种类 a 的相空间强度 fₐ(x,E,ω,t) 可由外加输运合同表示为

$$
(∂ₜ+vₐω·∇ₓ)fₐ+∂ᴱ[Ėₐ fₐ]
=−Σₐᵗᵒᵗ fₐ+∑ᵦ∫Kᵦ→ₐ(z′→z)fᵦ(z′)dz′+Sₐ. \\
(267.1)
$$

连续能损、散射、衰变和分枝核均为外加。对一条嵌入路径 p，固定能量下的无碰撞通过概率为

$$
Pₛᵤᵣᵥ(p∣E)=\exp[−∑ₑ∈p∫₀ˡᵉΣₑ(E,s)ds]. \\
(267.2)
$$

同一组合路径在真空、稀薄大气、屏蔽层和含氢材料中可以有完全不同的穿透率；存在路径不等于物理概率非零。

一次相互作用产生随机数目的次级粒子。令 Zₙ 为第 n 代的种类计数向量，外加分枝生成函数和平均分枝算子可写为

$$
Gₐ(s;E)=E[∏ᵢ s_{Aᵢ}G_{Aᵢ}(s;XᵢE)∣a,E],
\\
Mₐᵦ(E)=E[∑ᵢ1_{Aᵢ=ᵦ}∣a,E]. \\
(267.3)
$$

在能量区间和规则近似固定时，谱半径小于一、等于一和大于一分别表示平均次临界、临界和超临界分枝；能量阈值、逃逸、有限边界和衰变会截断无限级联，故局部超临界不等于无限粒子数。

区域 B 的单次沉积簇和质量归一剂量可写为

$$
Qᵣ(B)=∑_qΔE_q1_{x_q∈B},
\\
Dᵣ(B)=Qᵣ(B)/[ρₘₑd(B)|B|]. \\
(267.4)
$$

若事例数为 Poisson 变量 N，且沉积簇独立同分布，则总沉积 Q 的生成函数满足

$$
log E[e^{θQ}]=Λ[E(e^{θQ₁})−1]. \\
(267.5)
$$

共同太阳粒子事件、天气和介质脉冲会破坏独立性，形成簇间相关和随机强度。

若单次沉积具有有限矩生成函数，则在独立近似下可有 Cramér 大偏差

$$
P(N⁻¹∑ᵣQᵣ≥q)≈\exp[−N I(q)],
\\
I(q)=sup_{θ≥0}{θq−log E(e^{θQ₁})}. \\
(267.6)
$$

重尾源谱或分枝簇使矩生成函数失效时，极端和通常由单个异常簇主导；在相应弱相关条件下

$$
P(∑ᵣQᵣ>x)∼N P(Q₁>x). \\
(267.7)
$$

若 P(Q₁>x) 约为 L(x)x⁻ᵅ，最大沉积 Mₙ 可能满足

$$
P(Mₙ/aₙ≤x)→\exp(−x⁻ᵅ),
\\
N P(Q₁>aₙ)→1. \\
(267.8)
$$

有限能量上界会转入 Weibull 类，指数尾会转入 Gumbel 类，共同源事件则由极值指数修正。FIB 节点数和路径数不决定尾指数、归一化或极值簇集。

粒子到达出口的时间也是外加边时间上的随机最小和：

$$
T(v)=min_{p:u↝v}∑ₑ∈pτₑ. \\
(267.9)
$$

独立或短程相关边权、嵌入尺度和边界稳定后，才可讨论线性尺度的大偏差；重尾自由程、长程磁场相关和吸收边界会改变甚至破坏该极限。介质先固定再取级联极限的 quenched 统计与先平均介质的 annealed 统计通常不同。

探测器读数是沉积过程的滤波投影

$$
Yₗ(t)=∫₀ᵗ∫hₗ(t−s,x,E,ω)dN(s,x,E,ω)+ηₗ(t). \\
(267.10)
$$

闪烁淬灭、饱和、阈值、死时间和脉冲堆积会改变计数极值；同一真实沉积可以产生不同读数，不能把探测器最大脉冲直接当作物理最大沉积。级联纵向极大位置的对数近似也只有在给定分枝、能损、均匀介质和阈值后成立。

因此，FIB ATOM 递归在宇宙线和高能粒子问题中只提供组合节点、接缝、候选路径、端口和层级骨架；源谱、截面、分枝核、介质、磁场、边界、能量阈值、探测器响应和极限次序均须外加。粒子级联的临界性、输运首达、大偏差、局部沉积尾以及 Gumbel、Weibull 或 Fréchet 极值类，只有在这些条件和共同实现明确后才是统计结论，不能由 FIB 递归单独推出。


## 268. FIB 网络上的外加中子输运、裂变分枝与核临界涨落统计

设第 (j) 层 FIB 递归给出有限组合骨架

$$
\mathcal G_j=(V_j,E_j,\partial V_j,\mathsf P_j),
$$

其中 (V_j) 是原子或端口状态，(E_j) 是允许的邻接，(\partial V_j) 是边界，(\mathsf P_j) 记录接缝和跨层端口。FIB 递归决定哪些路径、拼接和层级投影存在，却不指定嵌入距离、时间、能量、方向或反应概率。为此把能量分箱、方向和材料标签并入外加类型集

$$
\mathsf X_j=V_j\times\mathcal E_j\times\Omega_j\times\mathcal M_j.
$$

由截面、材料密度、能损、散射角核、边界泄漏和源谱构造下一次裂变前的输运核 (P_j(x,y))。它是次随机核；离开 (\mathsf X_j) 的概率记作 (p_j^{\mathrm{esc}}(x))。在类型 (x) 的反应处，令 (\boldsymbol\eta_x=(\eta_x(y))_y) 为裂变产生的各类型中子数向量，概率母函数为

$$
\Phi_{j,x}(z)
=\mathbb E\!\left[
\prod_{y\in\mathsf X_j}
\left(p_j^{\mathrm{esc}}(y)+\sum_{z\in\mathsf X_j}P_j(y,z)z_z\right)^{\eta_x(y)}
\right].
$$

于是 (\Phi_{j,x}) 是“裂变产生—输运到下一反应—边界泄漏”的合成母函数。其均值矩阵（按列向量约定）为

$$
M_j(x,z)=\sum_{y\in\mathsf X_j}
\mathbb E[\eta_x(y)]P_j(y,z).
$$

只要 FIB 路径不允许从 (x) 到 (z)，对应项必为零；允许路径上的数值则完全由截面、反应核、能谱、边界和输运时间决定。给定初始中子类型 (x)，第 (n) 代裂变后代向量的母函数满足

$$
G_{0,x}(z)=z_x,
\qquad
G_{n+1,x}(z)=\Phi_{j,x}\bigl(G_n(z)\bigr).
$$

因此均值递推为

$$
\mathbb E_x Z_{n+1}=M_j\mathbb E_x Z_n,
\qquad
\mathbb E_x Z_n=M_j^n e_x.
$$

### 临界判据与有限尺寸窗口

令

$$
 k_{\mathrm{eff},j}=\rho(M_j),
$$

其中 (\rho) 是谱半径。若 (M_j) 不可约且二阶矩有限，则 (k_{\mathrm{eff},j}<1) 给出次临界平均衰减，(k_{\mathrm{eff},j}>1) 给出超临界平均增长，(k_{\mathrm{eff},j}=1) 是临界面。对有源但有限的系统，(q_j) 为每代外源，期望总裂变向量为

$$
 h_j=(I-M_j)^{-1}q_j
$$

（仅在 (\rho(M_j)<1) 时有限）。若 (\rho(M_j)=1-\Delta_j) 且 (0<\Delta_j\ll1)，则主模态的衰减时间为 (\Delta_j^{-1})；当 (n\Delta_j\ll1) 时观测呈临界样涨落，当 (n\Delta_j\gg1) 时转入次临界指数尾。若 (L_j=|V_j|) 且外加参数调成 (\Delta_j\asymp cL_j^{-\alpha})，临界窗口的代数尺度为 (n\asymp L_j^{\alpha}/c)。指数 (\alpha) 不是 FIB 递归给出的量，而是泄漏、截面和源边界共同决定的调参结果。

若以 (r_j,l_j) 归一化为

$$
M_jr_j=r_j,
\qquad
l_j^{\mathsf T}M_j=l_j^{\mathsf T},
\qquad
l_j^{\mathsf T}r_j=1,
$$

并把裂变向量的条件协方差投影到 Perron 模态，记所得有效二阶系数为 (\sigma_{\mathrm{eff},j}^2>0)，则有限类型临界分枝过程的标准临界标度为

$$
\Pr_x(Z_n\ne0)\sim\frac{c_x}{n},
\qquad
\mathcal L\!\left(\frac{l_j^{\mathsf T}Z_n}{n}\,\middle|\,Z_n\ne0\right)
\Longrightarrow \operatorname{Exp}(\theta_j).
$$

常数 (c_x) 与 (\theta_j) 由初始类型、左右 Perron 向量及 (\sigma_{\mathrm{eff},j}^2) 决定。对有限方差、非退化、不可约且非周期的单一临界分支，累计裂变数

$$
T=\sum_{n\ge0}\langle\mathbf 1,Z_n\rangle
$$

具有

$$
\Pr(T>t)\asymp t^{-1/2},
\qquad
\Pr(T=t)\asymp t^{-3/2},
$$

其截断、指数因子和常数在多类型、泄漏或能量依赖情形中由相应的二阶矩和主模态修正。因而临界涨落的幂指数来自分枝极限条件，而不是来自“Fibonacci”这一名称本身。

### 空间沉积、探测统计与方差递推

给定每类反应的能量沉积向量 (d_j)，平均沉积为

$$
\bar e_j=d_j^{\mathsf T}(I-M_j)^{-1}q_j.
$$

若 (B_j(u)) 表示单个个体裂变后代向量的协方差算子，按同一列向量约定，总代际协方差满足一个离散 Lyapunov 型递推

$$
C_{n+1}=M_jC_nM_j^{\mathsf T}+B_j(\mathbb E Z_n).
$$

因此计数器、剂量计和时间门内探测器得到的 Fano 因子、二阶相关和全计数母函数，均由均值矩阵、裂变母函数、源过程和探测响应的联合选择决定。相同的期望向量不保证相同的方差；改变裂变多重性方差或探测时间门即可保持均值而改变尾部。

### FIB 支撑的可识别边界

固定同一 (\mathcal G_j) 和同一允许路径支撑，取一个次随机输运核 (P_j)，并令外加裂变产额为常数 (a>0)，则

$$
M_j^{(a)}=aP_j.
$$

若 (\rho(P_j)>0)，选择 (a_-<\rho(P_j)^{-1}<a_+)，便得到同一 FIB 支撑上的次临界、临界和超临界三种模型；再改变 (\boldsymbol\eta_x) 的二阶矩，还可在同一 (k_{\mathrm{eff}}) 下改变临界峰、Fano 因子和总裂变数尾部。故由 FIB 路径计数、接缝数量或 Fibonacci 长度比，不能单独推出 (k_{\mathrm{eff}})、临界指数、剂量分布或探测计数律。

本节只建立一个外加核输运模型如何把 FIB 组合支撑送入多类型分枝统计的接口。截面、能损、散射与裂变核、材料和几何尺度、源谱、边界泄漏、时间标度、初始分布、探测器响应及所需极限均为外加假设。没有这些假设时，FIB 仅给出零模式与路径支撑，不能宣称中子输运定律、核临界性或任何普适涨落统计。

## 269. FIB 图族上的外加随机矩阵、自由概率谱极限与线性统计涨落

固定由 FIB ATOM 递归生成的有限图族 (G_n=(V_n,E_n))，令 (A_n(u,v)=1_{\{u,v\}\in E_n}) 为邻接掩码。递归只给出矩阵元允许非零的位置、端口连接和闭合游走的组合类型；边权分布、独立性、对称类、归一化、边界及观测协议均须外加。一个外加厄米随机矩阵系综可写为

$$
(H_n)_{uv}=B_n(u,v)+A_n(u,v)w_{uv}/\sqrt{s_n},
\\
H_n=H_n^†.
\\
(269.1)
$$

其中 (B_n,w_{uv},s_n) 都不由 FIB 决定。若 (\lambda_j) 是 (H_n) 的特征值，经验谱测度和 Stieltjes 变换为

$$
\mu_n=N_n^{-1}\sum_{j=1}^{N_n}\delta_{\lambda_j},
\\
m_n(z)=\int(z-x)^{-1}\mu_n(dx)=N_n^{-1}\operatorname{Tr}(zI-H_n)^{-1}.
\\
(269.2)
$$

归一化迹矩是合法闭合 FIB 游走的加权和：

$$
N_n^{-1}\operatorname{Tr}H_n^k
=N_n^{-1}\sum_{v_0,\ldots,v_{k-1}\atop (v_r,v_{r+1})\in E_n,\;v_k=v_0}
\prod_{r=0}^{k-1}(H_n)_{v_rv_{r+1}}.
\\
(269.3)
$$

FIB 决定求和的支撑；游走在平均后是否存活、矩是否紧和极限是否自平均，则由权重中心化、独立性、尾部与归一化决定。

在致密 Wigner 型权重、矩条件和与确定性 (B_n) 渐近自由的附加假设下，可得到自由加法卷积

$$
\mu_n\Rightarrow\mu_B\boxplus\mu_{\mathrm{sc},\sigma^2},
\\
m(z)=m_B\bigl(z-\sigma^2m(z)\bigr),\qquad m(z)\sim z^{-1}.
\\
(269.4)
$$

极限密度若存在，则

$$
\rho(x)=-\pi^{-1}\lim_{\eta\downarrow0}\operatorname{Im}m(x+\mathrm{i}\eta).
\\
(269.5)
$$

自由独立性不是 FIB 递归的结果。非均匀方差剖面要改用外加 Dyson 方程，例如

$$
m_i(z)=\left(z-b_i-\sum_j s_{ij}m_j(z)\right)^{-1},
\\
m_n(z)=N_n^{-1}\sum_i m_i(z).
\\
(269.6)
$$

若图稀疏、度数有界或局部极限是随机树，自由卷积通常失效；外加腔递归可写成

$$
q_{u\to v}(z)=\left(z-\xi_u-\sum_{w\in N(u)\setminus\{v\}}|w_{uw}|^2q_{w\to u}(z)\right)^{-1}.
\\
(269.7)
$$

局部图极限和边权系综共同决定腔谱。相同 FIB 支撑在独立、相关、确定性或重尾边权下可分别出现树谱、带隙、局域化峰或非自平均涨落。

对解析或足够光滑的 (f)，线性统计

$$
L_n(f)=\sum_jf(\lambda_j)-N_n\int f\,d\mu
=\frac{1}{2\pi\mathrm{i}}\oint f(z)\left[\operatorname{Tr}(zI-H_n)^{-1}-N_nm(z)\right]dz.
\\
(269.8)
$$

在模型特定的矩和相关条件下可有高斯极限

$$
\bigl(L_n(f_1),\ldots,L_n(f_r)\bigr)\Rightarrow
\mathcal N\bigl(\mathfrak m(f_a),\mathcal V(f_a,f_b)\bigr)_{a,b\le r}.
\\
(269.9)
$$

其均值和协方差依赖对称类、四阶累积量、方差剖面、确定性扰动、边界和有限秩缺陷；重尾或强相关时可以改为非高斯极限。有限秩缺陷的离群特征值由外加缺陷强度和未扰动预解式的极点方程决定，缺陷所在 FIB 接缝只提供候选位置。

经验谱测度的大偏差只能在给定系综后陈述：

$$
\mathbb P(\mu_n\in F)\asymp
\exp\left[-a_n\inf_{\nu\in F}I(\nu)\right].
\\
(269.10)
$$

致密轻尾模型中 (a_n) 有时为 (N_n^2)，稀疏图、重尾权重和随机环境会改变速度与速率函数；先固定图取极限的 quenched 律也可能不同于先平均图的 annealed 律。有限分辨率谱仪只观测 (Y_\ell=\int h_\ell(x)\mu_n(dx)+\eta_\ell)，所以端口谱和少数迹矩通常只能确定观测等价类。

因此，FIB ATOM 递归在随机矩阵问题中只提供稀疏位置、合法闭合游走、端口和层级骨架；谱系综、自由独立性、归一化、局部图极限、线性统计涨落、大偏差速度及观测规则都须外加。自由卷积、Dyson 方程、腔谱、线性统计中心极限定理和大偏差均是给定外加假设与极限次序后的条件结论，不能由 FIB 递归单独推出普适谱律。

## 270. FIB 复形上的外加光声/热弹耦合、脉冲响应与能量涨落统计

取第 (j) 层 FIB 复形 (K_j)。节点、胞腔、入射关系、接缝、端口和父子递归只给出组合支撑；嵌入空间、度量、时间、材料系数、边界和观测协议均另行外加。令 (I(x,t)) 为光能通量，(\vartheta(x,t)) 为温升，(u(x,t)) 为位移，(\varepsilon(u)) 为小应变。吸收系数 (\mu_a)、密度 (\rho)、比热 (c)、热导率 (\kappa)、弹性张量 (\mathsf C)、热膨胀张量 (\boldsymbol\alpha)、阻尼和接触参数都不是 FIB 递归的内生量。

在线性小应变近似下，可取外加热弹系统

$$
\rho c\,\partial_t\vartheta
=\nabla\!\cdot(\kappa\nabla\vartheta)+\mu_a I-h_b(\vartheta-\vartheta_b)+\xi_T,
\qquad
\rho\,\partial_t^2u+\mathsf D\partial_tu
-\nabla\!\cdot\!\left[\mathsf C:\bigl(\varepsilon(u)-\boldsymbol\alpha\vartheta\bigr)\right]
=f+\xi_u .
\tag{270.1}
$$

若以声压 (p) 观测，快速吸收的光声源可写为

$$
\mathcal L_a p=\partial_t\!\left(\Gamma\mu_a I\right)+\xi_a,
\tag{270.2}
$$

其中波速、衰减、色散和辐射边界包含在外加算子 (\mathcal L_a) 中。FIB 只能为离散化提供组合节点、邻接块、候选路径与端口编号，不能决定上述算子。

把温度、位移和速度并入状态 (z)，给定材料和边界后写成

$$
\dot z=\mathsf A z+\mathsf Bq+\xi,
\qquad
 y_r=\mathsf C_rz+\eta_r .
\tag{270.3}
$$

端口 (\ell) 到观测端口 (r) 的因果脉冲响应为

$$
 h_{r\ell}(t)=\mathbf 1_{t\ge0}\,\mathsf C_r e^{t\mathsf A}\mathsf B_\ell,
 \qquad H_{r\ell}(\omega)=\mathsf C_r(i\omega-\mathsf A)^{-1}\mathsf B_\ell .
\tag{270.4}
$$

因此存在一条 FIB 组合路径只表示可能的连接；非零声压、到达时间、共振峰和衰减率还需要 (\mathsf A,\mathsf B,\mathsf C) 及边界共同决定。相同组合图赋予不同材料或边界即可得到不同的传递核。

吸收和热弹能量可记为

$$
E_{\mathrm{abs}}=\int\!\!\int\mu_a(x)I(x,t)\,dx\,dt,
\qquad
E_{\mathrm{th}}=\int\rho c\,\vartheta\,dx,
\tag{270.5}
$$

$$
E_{\mathrm{mech}}(t)=\frac12\int\rho|\partial_tu|^2dx
+\frac12\int\bigl(\varepsilon(u)-\boldsymbol\alpha\vartheta\bigr):\mathsf C:
\bigl(\varepsilon(u)-\boldsymbol\alpha\vartheta\bigr)dx .
\tag{270.6}
$$

能量交换和耗散还取决于边界通量、接触功、阻尼与本构；FIB 节点数、递归深度和路径数不能给出能量分配比例。脉冲宽度 (\tau_p)、热扩散时标 (\tau_{\mathrm{th}}=L^2\rho c/\kappa) 与弹性时标 (\tau_{\mathrm{el}}=L/c_s) 的相对次序决定冲激、准静态或中间响应；长度 (L) 和声速 (c_s) 也是外加量。

若冲激事件在端口 (\ell) 带随机能量 (Q_\ell)，则单次读数满足

$$
Y_r(t)=\sum_\ell h_{r\ell}(t)Q_\ell+\eta_r(t),
$$

$$
\mathbb E Y_r(t)=\sum_\ell h_{r\ell}(t)\mathbb E Q_\ell,
\qquad
\operatorname{Cov}(Y_r(t),Y_s(t'))
=\sum_{\ell,m}h_{r\ell}(t)h_{sm}(t')\operatorname{Cov}(Q_\ell,Q_m)
+\operatorname{Cov}(\eta_r(t),\eta_s(t')).
\tag{270.8}
$$

独立复合 Poisson 事件、单事件向量 (Q) 和强度 (\Lambda) 给出

$$
K_Y(\boldsymbol s;t)
=\Lambda\left[\mathbb E\exp\!\left(\sum_r s_r\sum_\ell h_{r\ell}(t)Q_\ell\right)-1\right]+K_\eta(\boldsymbol s;t).
\tag{270.9}
$$

随机强度导致 Cox 混合，脉冲间共享热源或机械模态则破坏独立复合形式。只有在线性、平衡、被动阻尼和给定温度下，才可使用外加涨落耗散关系，例如

$$
\mathbb E[\xi(t)\xi(t')^{\mathsf T}]=2k_{\mathrm B}T\,\mathsf D\,\delta(t-t').
\tag{270.10}
$$

非平衡泵浦、温度梯度和记忆耗散不满足这一白噪声式。峰值、首达时间和极值还依赖振铃、脉冲重叠、带宽、饱和与死时间；同一沉积过程经不同探测协议可产生不同尾部。

有限端口传递矩阵一般只识别输入输出等价类。不可观测或不可控的内部热弹模态可以改变材料参数而保持测量频带内的 (H(\omega)) 不变，所以端口脉冲不能唯一反演内部吸收分布或本构。取 (j\to\infty) 时还须共同指定嵌入、系数收敛、端口缩放、噪声和边界；有限方差独立脉冲可能给出中心极限，长程相关或重尾能量则可能给出非高斯稳定极限。

因此，光声脉冲、热弹能量分配、涨落耗散、协方差、复合 Poisson 或稳定极限都依赖外加吸收、扩散、弹性、阻尼、边界、噪声、源统计、探测器和尺度条件。FIB ATOM 递归只提供组合节点、邻接、接缝、候选路径、端口和层级骨架，不能单独推出任何上述物理统计律。

## 271. FIB 网络上的外加蒸发液滴、咖啡环沉积与随机干燥统计

固定第 (j) 层 FIB 网络 (G_j=(V_j,E_j))，把顶点和边映射到一个外加的基底或微流道支撑。FIB 只给出接触邻接、端口、候选流路和层级拼接；液滴的几何嵌入、接触角、表面张力、黏度、挥发通量、溶质扩散、基底粗糙度和环境湿度都必须另行指定。令 (c_e(s,t)) 表示边 (e) 上的溶质浓度，(h_e(s,t)) 为液膜厚度，(u_e(s,t)) 为沿边平均速度，则一个外加的一维润湿—蒸发模型可写成

$$
\partial_t(h_ec_e)+\partial_s(h_eu_ec_e)
=\partial_s\!\left(h_eD_e\partial_sc_e\right)-J_e^{\mathrm{evap}}c_e+R_e,
$$

$$
\partial_t h_e+\partial_s(h_eu_e)=-J_e^{\mathrm{evap}}.
\tag{271.1}
$$

其中 (D_e) 是扩散系数，(R_e) 可表示结晶、吸附或反应源项。节点处的质量守恒和接触角条件由外加耦合给出；FIB 的端口只规定哪些通量可以相互连接，并不规定通量大小。

在接触线钉扎且蒸发通量具有边缘奇异性时，可取

$$
J_e^{\mathrm{evap}}(s,t)=J_{0,e}(t)\left[1-\left(\frac{s}{a_e(t)}\right)^2\right]^{-\lambda_e},
\qquad 0<\lambda_e<1,
\tag{271.2}
$$

其中 (a_e(t)) 是外加接触半径。若蒸发诱导的径向流把溶质输向边缘，则沉积密度的准静态近似满足

$$
\sigma_e(s)\propto\int_0^{t_f}
J_e^{\mathrm{evap}}(s,t)c_e(s,t)\,dt,
\tag{271.3}
$$

并在接触线附近出现由 (\lambda_e)、扩散和钉扎历史共同决定的增强。若接触线持续回缩或扩散足够快，边缘增强可以消失，沉积可趋于中心均匀；因此“咖啡环”不是由某个组合图的边数自动推出的结论。

把沉积视为随机事件，令 (N_e(ds,dt)) 是沿边的点过程，强度取

$$
\Lambda_e(s,t)=\kappa_e h_e(s,t)c_e(s,t)\,\mathbf 1_{\{h_e>h_{\min}\}},
$$

其中 (\kappa_e)、阈值和事件大小分布均为外加。对单个颗粒质量 (W) 的复合点过程，总沉积质量为

$$
M_e(A)=\int_{A\times[0,t_f]}W_e(s,t)\,N_e(ds,dt).
$$

若条件于液滴轨道后 (N_e) 为 Poisson，累积量满足

$$
\operatorname{cum}_r\bigl(M_e(A)\mid h,c\bigr)
=\int_{A\times[0,t_f]}\Lambda_e(s,t)\,\mathbb E[W_e(s,t)^r],ds\,dt.
\tag{271.4}
$$

随机接触线、环境湿度或颗粒团聚使强度成为随机场，边缘沉积便是 Cox 混合；长程流动、相分离或重尾团聚会把高斯极限替换为稳定或极值极限。相同平均沉积量可以对应不同的粒子数方差和最大团簇尾部。

在薄膜尺度 (a) 与扩散系数 (D) 给定时，

$$
\mathrm{Pe}=Ua/D,
\qquad
\mathrm{Da}=k a/U,
\qquad
\mathrm{Oh}=\mu/\sqrt{\rho\gamma a}
$$

分别衡量对流—扩散、反应—输运和黏性—毛细竞争。干燥时间、接触线速度和颗粒沉积律取决于这些无量纲数以及蒸发边界；FIB 递归只提供可拼接的边—节点骨架，不能固定它们的数值或极限次序。

有限观测通常只给出若干端口的剩余质量、边缘—中心比和少数时间点。改变 (J_e^{\mathrm{evap}})、(D_e) 与颗粒事件强度，可以保持这些读数不变而改变内部浓度场和沉积尾部。因此由 FIB 路径数、接缝数或 Fibonacci 长度比，不能唯一反演挥发通量、咖啡环指数、干燥时间分布或团簇极值律。

本节的结论是一个外加蒸发—输运—沉积模型在 FIB 组合支撑上的条件统计接口。接触角、表面张力、蒸发和扩散系数、流变本构、边界湿度、颗粒大小和相互作用、随机事件律、观测带宽以及 (j\to\infty) 的尺度耦合都必须明确；缺少这些假设时，FIB 只能给出零模式、邻接和候选流路，不能单独推出咖啡环沉积或任何干燥统计普适律。

## 272. FIB 网络上的外加中微子输运、味振荡与探测计数统计

设 FIB 第 (j) 层给出带端口的有向骨架 (\mathcal G_j=(V_j,E_j,\partial V_j,\mathsf P_j))。其中路径只表示粒子可能经过的组合序列；中微子能量、传播距离、质量平方差、混合矩阵、介质电子密度、相干长度、源谱和探测器截面均须外加。沿一条给定嵌入路径 (x\mapsto r(x))，用味空间密度矩阵 (\varrho(x,E)) 描述传播，可写成带外加哈密顿量和退相干的方程

$$
\frac{d\varrho}{dx}
=-\mathrm i[H(E,x),\varrho]
+\mathcal D_x(\varrho),
$$

$$
H(E,x)=\frac{1}{2E}U\,\operatorname{diag}(m_1^2,m_2^2,m_3^2)U^\dagger+V_{\mathrm m}(E,x)+H_{\mathrm{new}}(E,x).
\tag{272.1}
$$

矩阵 (U)、质量平方差 (m_a^2-m_b^2)、物质势 (V_{\mathrm m})、可能的非标准项 (H_{\mathrm{new}}) 与耗散算子 (\mathcal D_x) 都不由 FIB 递归决定。无退相干、均匀真空和两味近似下，转化概率才可化为

$$
P_{\alpha\to\beta}(L,E)
=\sin^2(2\theta)\sin^2\!\left(\frac{\Delta m^2L}{4E}\right),
\qquad \alpha\ne\beta,
\tag{272.2}
$$

这只是给定外加参数后的特例。若路径穿过分段介质，传播算子是有序乘积

$$
S_j(E)=\mathcal T\exp\!\left[-\mathrm i\int H(E,x)\,dx\right],
\qquad
P_{\alpha\to\beta}=|S_{j,\beta\alpha}|^2,
\tag{272.3}
$$

节点和接缝只决定哪些段可以连接；每段长度、密度和界面匹配决定乘积中的相位与振幅。

若 FIB 分支给出多条未分辨路径 (\pi)，源的相位或生产时刻使其相干，则振幅先相加

$$
\mathcal A_{\alpha\to\beta}(E)=\sum_{\pi}a_\pi(E)\,[S_\pi(E)]_{\beta\alpha},
\qquad
P_{\alpha\to\beta}=|\mathcal A_{\alpha\to\beta}|^2.
\tag{272.4}
$$

若路径长度涨落超过相干长度，则应先按外加路径分布平均概率而非振幅；两种极限一般不同。FIB 的路径计数本身不决定相干还是非相干的取法。

给定源强度 (\Phi_\alpha(E,t))、截面 (\sigma_\beta(E))、几何接受率 (A_d(E,\Omega)) 和效率 (\epsilon_d(E))，探测器计数强度可写成

$$
\lambda_d(t)=\sum_\alpha\int
\Phi_\alpha(E,t)P_{\alpha\to\beta}(E)\sigma_\beta(E)A_d(E,\Omega)\epsilon_d(E)\,dE\,d\Omega.
\tag{272.5}
$$

在给定强度且事件独立时，时间窗计数 (N_d(T)) 为 Poisson，

$$
\Pr\{N_d(T)=n\}=e^{-\Lambda_d(T)}\frac{\Lambda_d(T)^n}{n!},
\qquad
\Lambda_d(T)=\int_0^T\lambda_d(t)\,dt.
\tag{272.6}
$$

源闪烁、束流漂移、共同介质扰动或未建模背景会令强度随机化，产生 Cox 混合、过度离散和跨探测器协方差。能谱重建还受能量分辨率核、阈值、死时间和误识别矩阵影响；同一振荡概率在不同响应协议下可得到不同计数尾部。

在恒定真空两味模型中，固定一个 FIB 路径长度 (L)，调节 (\Delta m^2L/E) 可以让转化概率接近零、接近一或处于中间值，而不改变任何 FIB 邻接和接缝。再调节退相干率可在相同平均概率下改变基线相关和方差；调节源谱与探测截面还可保持总计数均值而改变能谱形状。因此仅由 FIB 路径长度比、端口数量或 Fibonacci 层数，不能识别混合角、质量平方差、物质势、相干长度或计数统计律。

当 (j\to\infty) 时，必须同时规定嵌入路径的长度测度、介质剖面收敛、能量和角度的缩放、相干与退相干的次序以及探测器分辨率。有限事件数的中心极限、稀有转换的 Poisson 极限和随机介质下的非高斯极限对应不同外加假设。故 FIB ATOM 递归在中微子问题中只提供组合路径、端口和层级连接；振荡相位、介质效应、首达输运、源—探测联合律及其极限均须由外加物理模型给出，不能从 FIB 递归单独推出。


## 273. FIB 网络与复形上的外加反应—扩散系统、Turing 图样与模式选择统计

设第 j 层 FIB 递归给出带端口的有限骨架

$$
𝒢ⱼ=(Vⱼ,Eⱼ,∂Vⱼ,𝒫ⱼ).
$$

节点、边、接缝和层级端口只记录组合上的可连接关系；节点质量、边导通率、物理距离、反应常数、边界条件和噪声律都属于外加模型。给顶点 v 赋正质量 mᵥ，给允许边赋非负导通率 κᵥw，并以 βᵥ表示外加泄漏，则加权图扩散算子可写成

$$
(Lⱼx)ᵥ=mᵥ⁻¹[Σ_{w∼v}κᵥw(xᵥ−xw)+βᵥ1_{v∈∂Vⱼ}xᵥ].
$$

无泄漏边界保留常数零模；Robin、吸收或有向边界会改变零模和全部离散谱。若 FIB 递归还给出胞腔，可用外加定向边界算子构造 Hodge 算子 Δⱼ,p；其权重、内积和相对边界条件仍非 FIB 内生量。

令 s 个组分在所有节点上的状态为 Xⱼ，外加随机反应—扩散模型为

$$
dXⱼ=[−(Dⱼ⊗Lⱼ)Xⱼ+Fⱼ(Xⱼ;θⱼ)]dt+Σⱼ(Xⱼ;θⱼ)dWⱼ.
$$

局部反应函数 Fⱼ、扩散矩阵 Dⱼ、参数 θⱼ、噪声协方差和外部源决定动力学。若存在均匀平衡 q₊，令 J 为反应 Jacobian，Lⱼφⱼ,k=λⱼ,kφⱼ,k，则线性模态矩阵为

$$
Aⱼ,k=J−λⱼ,kDⱼ,
\qquad σⱼ,k=max Re spec(Aⱼ,k).
$$

Turing 图样需要零模稳定而某个非零空间模态失稳，即 σⱼ,0<0 且 σⱼ,k>0。对两组分、对角扩散，均匀稳定条件为 tr J<0、det J>0；连续谱的扩散失稳还要求 DᵥJ₁₁+DᵤJ₂₂>0 且

$$
(DᵥJ₁₁+DᵤJ₂₂)²>4DᵤDᵥ det J.
$$

有限 FIB 图只有在其实际离散谱落入不稳定区间时才出现线性 Turing 模态；连续判据成立而离散谱避开该区间时，有限系统仍可稳定。线性增长也不等于有限幅度图样，非线性饱和、简并模态和初始投影必须另行给出。

在线性稳定区，模态满足 Ornstein–Uhlenbeck 型方程，稳态协方差 Cⱼ,k 解

$$
Aⱼ,kCⱼ,k+Cⱼ,kAⱼ,kᵀ+Qⱼ,k=0,
$$

其中 Qⱼ,k 是噪声投影。临界模态的方差由衰减率、左右特征向量和噪声投影共同决定；噪声在临界方向上为零时不会出现方差发散。非正规扩散算子的瞬态放大还取决于奇异值和伪谱，不能只看特征值实部。

同一 FIB 支撑可取两组反应和扩散参数，使一组满足 Turing 失稳、另一组保持均匀稳定；也可固定确定性漂移而取 Σⱼ=0 或 Σⱼ≠0，从而保持均值和线性增长率相同，却改变结构因子、模式切换概率和极端振幅尾。j→∞ 时还必须指定拉普拉斯重标度、顶点测度、边界序列、噪声归一化、嵌入几何和反应时间尺度。因此图样存在性、主导模式、临界涨落和模式选择律都是外加反应—扩散模型的条件结论，不能由 FIB 递归单独推出。

## 274. FIB 网络上的外加颗粒介质、断层滑移、摩擦耗散与地震型雪崩统计

取 FIB 网络骨架 Gⱼ=(Vⱼ,Eⱼ,∂Gⱼ,𝒫ⱼ)，并在外加取向下给出边—点关联矩阵 Bⱼ。FIB 只决定节点、邻接、接缝、端口和可拼接路径；嵌入长度、面积、法向载荷、颗粒直径、应力单位、时间尺度和驱动均需另行指定。

在边 e 上引入位移 uₑ、速度 vₑ、法向应力 σₙ,ₑ、堆积率 φₑ 和摩擦状态 θₑ。一个外加网络力学模型可写成

$$
Mⱼü+Cⱼu̇+Kⱼu+T_f(v,θ,φ)=f_drive+ξ.
$$

Kⱼ 的非零块可以受 FIB 邻接支撑，但其数值由几何、材料和接触刚度决定；长程弹性或颗粒压力甚至可跨越 FIB 相邻边传递。速率—状态摩擦的一种外加形式为

$$
τ_f=σ_n[μ₀+a ln((|v|+v₀)/v₀)+b ln(θ/θ₀)]+ζ,
\qquad θ̇=1−|v|θ/D_c.
$$

摩擦功和能量收支满足

$$
W_fr(T)=Σₑ∫₀ᵀ∫ₑ τ_f|v|,ds,dt≥0,
$$

$$
ΔE_in=ΔK+ΔU+W_fr+W_comp+E_rad,
$$

但每项的定义、非负性和观测性依赖外加本构与边界；节点数或 FIB 层数不能给出耗散比例，也不能把释放能量唯一映射到震级。

令边 e 的剩余强度为 rₑ，局部滑移 Δsₑ 通过外加应力核 G 改变其他边的剩余强度，得到

$$
r′_f=r_f−G_feΔsₑ+δr_f,
\qquad e 触发 ⇔ rₑ≤0.
$$

定义触发概率矩阵 βₑf 和分支均值 mₑ=Σ_fβₑf。β 的零元位置可受 FIB 路径约束，但数值由应力核、阈值分布、滑移量、驱动速率和相关结构决定。在局部近似树状且相关足够短时，ρ(β)<1、ρ(β)=1、ρ(β)>1 分别对应外加的次临界、临界和潜在宏观失稳区间。

在给定临界动力学和有限尺寸截断时，事件大小 S 可有

$$
pⱼ(S)=CⱼS^{−τ}F(S/S_c(j)),
\qquad S_c(j)∼Lⱼ^{d_f}.
$$

然而同一 FIB 骨架也可取有界阈值与 ρ(β)<1，得到指数尾；或调节应力增益至 ρ(β)=1，得到临界分枝的 S⁻³ᐟ² 尾；重尾后代和长程相关又可给出稳定型尾。有限端口传感器只看到带宽、阈值和饱和后的投影，改变未观测应力标度或检测规则即可保持均值而改变雪崩尾部。因此摩擦耗散、地震型幂律、等待时间和极值指数均须由外加动力学、随机律、边界和观测协议共同确定。

## 275. FIB 复形上的外加拓扑波导、量子霍尔边缘输运与无序涨落

设 FIB 第 n 层递归支撑有限胞腔复形 𝒦ₙ。递归关系确定顶点、胞腔粘接、端口和允许路径；取向的物理意义、长度和时间单位、轨道维数、跃迁振幅、规范势、费米能级、无序系综以及源漏接入方式均为外加数据。没有外加二维周期方向、扭转参数或非交换导数时，复形本身没有可直接取值的 Chern 数。

在顶点轨道上取外加单粒子哈密顿量

$$
Hₙ(ω)=Σᵤcᵤ†(Mᵤ+ωᵤ)cᵤ+Σ_{⟨u,v⟩∈Eₙ}(cᵤ†tᵤᵥeⁱᴬᵤᵥcᵥ+h.c.)+H_cell.
$$

若给定两个扭转角和费米投影 Pₙ，则可定义

$$
Cₙ(ω)=(2πi)⁻¹∫∫Tr(Pₙ[∂₁Pₙ,∂₂Pₙ])dφ₁dφ₂.
$$

该整数要求统一谱隙或迁移率隙、足够正则性和明确的体态极限；FIB 路径数不能替代这些条件。若体边隙保持，体边对应给出净手性 νₙ=C_bulk−C_vac，理想相干接触下边缘电导为

$$
G_edge=(e²/h)νₙ.
$$

有限样品的真实电导仍是透射矩阵的投影，接触反射、非手性边道、有限长度、非绝热激发和相互作用都会使其偏离整数倍。递归加细只有在外加轨道嵌入、参数延拓和边界匹配形成保持隙的连续同伦时，才能比较不同层的拓扑指标。

令 𝒢ₙ 为“迁移率隙和拓扑扇区保持”的外加事件，pₙ=Pr(𝒢ₙ)。随机电导的方差分解为

$$
Var(Gₙ)=pₙVar(Gₙ|𝒢ₙ)+(1−pₙ)Var(Gₙ|𝒢ₙᶜ)+pₙ(1−pₙ)[E(Gₙ|𝒢ₙ)−E(Gₙ|𝒢ₙᶜ)]².
$$

理想接触且 𝒢ₙ 内严格量子化时，条件方差为零；非零涨落来自隙闭合、拓扑扇区改变、接触修正或非手性通道。边界传输矩阵的 Lyapunov 指数、局域长度、中心极限定理和大偏差率由其外加分布与相关结构决定，FIB 只提供零元位置和拼接次序。没有随机系综时“无序涨落”没有概率意义；没有隙保持同伦时不同层的拓扑指标不能比较。

## 276. FIB 网络上的外加量子传感、Ramsey 相位估计与 Fisher 信息涨落

固定 FIB 图 Gⱼ=(Vⱼ,Eⱼ)，把节点解释为外加的传感器、自旋或量子比特，把边解释为可能的耦合和控制连线。FIB 只给组合支撑与端口；能级、陀螺因子、场耦合、控制脉冲、退相干、初态、读出和时间单位均须外加。

对单个传感器，外加控制包络 y(t) 下的相位可写成

$$
φ=γ∫₀ᵀy(t)B(t)dt+φ₀.
$$

若噪声近似高斯且由谱密度 S_B(ω) 描述，Ramsey 对比度可写成

$$
C(T)=exp[−χ(T)],
\qquad χ(T)=π⁻¹∫₀∞S_B(ω)|Y_T(ω)|²dω,
$$

其中 Y_T 是 y 的滤波函数。二值读出概率的一般形式为

$$
P_+(ϑ)=1/2[1+C(T)cos(φ(ϑ)+φ_r)].
$$

因此经典 Fisher 信息、量子 Fisher 信息和 Cramér–Rao 下界分别依赖外加制备、控制、噪声和测量：

$$
Var(ϑ̂)≥[νF_C(ϑ)]⁻¹,
\qquad F_C(ϑ)≤F_Q(ϑ).
$$

多节点传感器的协方差矩阵可由独立、共同噪声、纠缠态或反馈产生；相同 FIB 边支撑在这些实现下可分别呈现散粒噪声标度、相关噪声放大或理想纠缠增强。节点数和路径数不决定 Heisenberg 标度，也不决定最优控制序列。

有限带宽读出得到的是观测矩阵 H 对量子轨迹的投影。改变 S_B 的频带分布并相应改变 y(t)，可以保持单次方差和平均信号不变，却改变多次测量的协方差、首达时间和大偏差尾；改变探测效率也可以保持无条件通道而改变记录统计。故由 FIB 端口计数不能唯一反演场谱、退相干率、量子 Fisher 信息或最优估计方差。

当 j→∞ 时，必须规定传感器间距、耦合强度、控制时间、噪声谱、纠缠制备成本和读出分辨率的共同缩放。只有在这些条件固定后，才能讨论量子极限、连续测量极限或空间平均的中心极限；FIB 递归本身只提供候选耦合图和端口骨架。

## 277. FIB 网络上的外加 Josephson 结阵列、相位滑移与磁通涨落统计

设 FIB 网络的顶点承载超导岛，边承载外加 Josephson 结，组合支撑为 Gⱼ=(Vⱼ,Eⱼ,∂Gⱼ,𝒫ⱼ)。结的临界电流 I_c、结电容 C、正常电阻 R、岛电容、互感、外磁通、温度和偏置协议均不由 FIB 递归决定。

在 RCSJ 外加模型中，边相位差 δₑ 满足

$$
Cₑ(Φ₀/2π)δ̈ₑ+Rₑ⁻¹(Φ₀/2π)δ̇ₑ+I_c,ₑsinδₑ=I_bias,ₑ+ξₑ.
$$

每个 FIB 闭合回路只提供可能的通量约束位置；物理环路还需外加电感和规范选择，例如

$$
Σ_{e∈cycle}δₑ+2πΦ_ext/Φ₀=2πn.
$$

在给定电流—相位势垒和热浴后，零电压态到相位滑移的逃逸率可写成

$$
Γₑ≈Aₑexp[−ΔUₑ/(k_BT_eff)].
$$

欠阻尼、过阻尼、量子隧穿、共同噪声和非平衡驱动会改变前因子、势垒和等待时间分布；这些选择不由图的度数或 Fibonacci 长度决定。

阵列电压由相位速度读出，Vₑ=(Φ₀/2π)δ̇ₑ。给定独立滑移事件时，时间窗内滑移数可为 Poisson；共同磁通、互感、偏置噪声和同步锁定会产生 Cox 混合、过度离散、Shapiro 台阶和跨边相关。相同平均电压可以由稀疏快滑移、密集慢滑移或相位锁定三种外加机制产生。

固定同一 FIB 支撑，缩放 I_c/C/R 可以把阵列置于超导、耗散或混沌相位区；改变外磁通而保持节点和边不变，可以改变涡旋数、相位绕数和磁通噪声。有限端口电压和少数频率响应只识别内部参数的等价类，不能唯一确定每条结的势垒、互感或噪声联合律。

因此 Josephson 临界电流、相位滑移等待时间、磁通量子化、同步和涨落统计都需要外加电路参数、规范约束、热浴、量子噪声、偏置和观测协议。FIB ATOM 递归只提供结阵列的组合邻接、闭合回路、端口和层级骨架，不能单独推出超导相、相位滑移指数或普适磁通统计。


## 278. FIB 网络上的系外行星凌日、引力微透镜与光变统计

设第 j 层 FIB 递归给出观测端口到源端口的合法路径集 Γⱼ。给每条路径外加权重 wⱼ,γ 和投影状态 zⱼ,γ，归一化路径测度为

$$
ηⱼ=Mⱼ⁻¹Σ_{γ∈Γⱼ}wⱼ,γδ_{zⱼ,γ},
\qquad Mⱼ=Σ_{γ∈Γⱼ}wⱼ,γ.
$$

FIB 只规定路径集合、接缝和层级地址；天空投影、恒星亮度、行星半径、透镜质量、速度、时间标定和观测噪声均须外加。给定外加响应核 h，归一化光变是

$$
Lⱼ(t;ϑ)=∫h(t,z;ϑ)dηⱼ(z).
$$

凌日核可由恒星盘与行星盘的重叠面积及肢暗强度构造，微透镜核可由

$$
A(u)=(u²+2)/(u√(u²+4)),
\qquad u(t)=√(u₀²+((t−t₀)/t_E)²)
$$

构造；二者共享 FIB 路径测度接口，却依赖不同的天体物理参数。

若 ηⱼ 弱收敛到 η，且 h 在观测时间紧集上有界等度连续，则 Lⱼ 一致收敛到 L=∫h dη。若路径权重满足外加独立性和函数型中心极限定理，则

$$
√Mⱼ(Lⱼ−L)⇒G,
$$

极限协方差由路径重叠核、权重相关和观测噪声共同决定。只有再假定有效路径数服从 Fibonacci 加法递推且权重独立时，才可把样本量写成 Mⱼ∼φʲ；这不是 FIB 递归单独给出的方差律。

光变只识别响应映射后的推前测度：若两个内部测度满足 Πϑ#η=Πϑ#η̃，则对全部观测时间给出相同曲线。小行星凌日近似中，缺口约为 k²cη(t)Ī(t)，行星半径比 k 与覆盖率 cη 可互相补偿；微透镜中源星混合比例 f_s、冲击参数 u₀ 和 Einstein 时间 t_E 也存在乘积与时间尺度退化。故 FIB 路径数、接缝数或黄金比例不能单独识别行星半径、透镜质量、光变尾部或参数后验。

## 279. FIB 复形上的外加 MRI、扩散磁共振与 Bloch–Torrey 统计

设 FIB 递归给出有限胞腔复形 Kⱼ 和外加质量矩阵 Mⱼ、扩散权重 Wⱼ。由边界矩阵 Bⱼ形成离散扩散算子

$$
Lⱼ(D)=Mⱼ⁻¹BⱼᵀWⱼ(D)Bⱼ.
$$

FIB 只给出体素、接缝、路径和细化映射；坐标、体积、扩散张量、弛豫率、磁场、梯度、射频脉冲、边界和接收机噪声均须外加。复横向磁化 mⱼ 满足离散 Bloch–Torrey 方程

$$
ṁⱼ=−[Lⱼ(D)+R₂,ⱼ+iΩⱼ(t)]mⱼ.
$$

由时间排序传播子 Eⱼ,r 和射频矩阵 Pⱼ,r，脉冲序列读数为

$$
Sⱼ(Π)=cⱼ†Pⱼ,nEⱼ,n⋯Pⱼ,1Eⱼ,1m₀,ⱼ.
$$

在固定梯度和弛豫、扩散算子可对角化时，信号是有限模态和

$$
Sⱼ(t)=Σ_aAⱼ,a exp(−λⱼ,a t),
\qquad λⱼ,a=rⱼ+dⱼμⱼ,a,
$$

其中 μⱼ,a 由复形支撑、质量和外加边权共同决定。自由各向同性扩散、已知梯度和理想重聚焦的特例给出

$$
E(B)=exp(−rT−tr(BD)),
$$

但有限复形、吸收边界、空间异质性和非交换射频会改为模态叠加或有序传播子。

若组织扩散张量 Dω 是外加随机变量，则低阶 b 张量读数满足

$$
log E(B)=−E[tr(BDω)]+½Var(tr(BDω))+⋯.
$$

接收机复高斯噪声使幅度呈 Rician 条件律；组织随机性再把该律混合。固定同一 FIB 复形，常数扩散、反射边界和独立噪声可产生单指数信号，而混合扩散、部分吸收边界和相关噪声可产生多指数、非高斯幅度和不同尾部。故路径计数、接缝层级和 FIB 细化不能单独决定 MRI 的 b 值指数、弛豫时间、噪声分布或连续极限；还须外加坐标尺度、物性收敛和观测协议。

## 280. FIB 网络上的外加野火传播、燃料异质性与极值统计

设 FIB 网络骨架为 Gⱼ=(Vⱼ,Eⱼ,∂Gⱼ,𝒫ⱼ)，并把边嵌入外加的地表或林冠通道。FIB 只给出邻接、端口、接缝和候选传播路径；燃料密度、含水率、坡度、风场、热传导、辐射、点火源和观测分辨率均须另行指定。

在边 e 上令 Tₑ 为温度、Fₑ 为剩余燃料、Mₑ 为含水率，外加热—反应—对流模型可写成

$$
∂ₜTₑ+Uₑ∂ₛTₑ=κₑ∂ₛ²Tₑ+QₑRₑ(Tₑ,Fₑ,Mₑ)-hₑ(Tₑ-Tₐ)+ξₑ,
$$

$$
∂ₜFₑ=Dₑ^F∂ₛ²Fₑ-Rₑ(Tₑ,Fₑ,Mₑ)+ξₑ^F,
\qquad
Rₑ=AₑFₑg(Mₑ)exp[−Eₐ/(R Tₑ)].
$$

节点处的热通量、燃料连续性和风场转向由外加边界条件耦合；FIB 接缝只说明哪些通量能够连接，并不确定热损失或点火阈值。

若把局部点火视为条件事件，边 e 的点火强度可取

$$
λₑ(t)=λ₀exp[a(Tₑ-T_c)+bUₑ^+−cMₑ]1_{Fₑ>F_c}.
$$

由 e 点火后使邻边 f 点火的概率组成矩阵 B。其支撑可受 FIB 路径限制，但数值依赖风向、燃料相关、坡度和余烬输运。局部近似树状且事件可分离时，ρ(B)<1 给出有限火簇和指数截断，ρ(B)=1 可进入临界雪崩窗口，ρ(B)>1 则允许宏观贯通；这些是外加随机过程的条件判据。

火场面积 S、持续时间 T 和峰值温度 H 的联合尾部还受卫星视场、云遮挡、阈值和删失影响。固定同一 FIB 支撑，降低燃料含水率或增强顺风输运可以从次临界切换到贯通传播；改变点火强度和相关长度可以保持平均面积而改变极值尾。有限观测只得到投影 Y=H_obs(T,F)+η，无法唯一反演内部燃料场、风场或点火核。

当 j→∞ 时必须同时规定图嵌入的物理面积、燃料和风场的联合收敛、边界阻隔、时间尺度和观测带宽。FIB 递归因此只提供火灾传播的组合支撑；点火概率、火线速度、面积幂律、等待时间和极值类均是外加热—流—反应模型的条件结论。

## 281. FIB 网络上的外加血流—血栓输运、脉动响应与栓塞统计

把 FIB 图 Gⱼ=(Vⱼ,Eⱼ) 外加嵌入为血管或微流道网络。顶点是分叉和储库，边是管段；FIB 只规定连接和可达路径，半径、长度、顺应性、黏度、红细胞相分离、压力边界和壁面反应均须外加。

在准稳态层流近似下，边 e 的体积流量满足

$$
Qₑ=Gₑ(p_{u(e)}-p_{v(e)}),
\qquad
Gₑ=πrₑ⁴/(8μₑℓₑ),
\qquad
BQ=s.
$$

脉动血流需要顺应性矩阵 C 和储库源项，例如

$$
C ṗ=s-BQ,
\qquad
Q=Q(p,t;R,C,\text{壁面}).
$$

这些参数决定压力波速、反射、阻尼和停滞区；相同 FIB 邻接在不同半径或黏度下可分别呈现层流、惯性分离或局部回流。

令 cₑ(s,t) 为血小板或示踪粒子浓度，外加对流—扩散—反应方程可写成

$$
∂ₜcₑ+uₑ∂ₛcₑ=Dₑ∂ₛ²cₑ−k_on cₑaₑ+k_off bₑ+ξₑ,
$$

其中 aₑ、bₑ 是活化和聚集态。血栓增长、壁面黏附和剪切脱落构成外加随机核；由一条管段脱落的栓子可沿 FIB 合法路径传播，但到达时间和堵塞概率取决于流速、尺寸、变形和分叉捕获。

若 βₑf 是栓子从 e 到 f 的条件转移矩阵，ρ(β)<1 时总通过次数通常有有限均值；接近 ρ(β)=1 时可出现长等待和多次循环，重尾粒径、共同炎症源或脉动停滞会改变尾部和跨患者相关。观察端口的压力和流量只识别传递函数的投影；不同的半径分布、壁顺应性和血栓反应可保持同一端口均值而产生不同内部栓塞风险。

因此，FIB 只能提供血管拓扑、分叉和候选栓塞路径。Poiseuille 或非牛顿本构、压力和流量边界、血细胞统计、凝血速率、壁面反应、随机源、成像分辨率及尺度极限均须外加；血流脉动、血栓形成、栓塞时间和极值风险不能由 FIB 递归单独推出。

## 282. FIB 复形上的外加雷暴闪电、流注分枝与放电极值统计

设 FIB 复形的顶点表示外加空间分辨率下的电荷单元，边和面表示候选电场与流注连接。FIB 只给出组合邻接、接缝、端口和闭合回路；介电率、导电率、湿度、背景电荷、雷暴驱动、时间单位和传感器响应均须另行指定。

外加电势 V、自由电荷密度 ρ和电流 j 可由

$$
∇·(ε∇V)=−ρ,
\qquad
j=−σ∇V,
\qquad
∂ₜρ+∇·j=S−R(ρ,V).
$$

流注在边 e 上形成的条件强度可以写成

$$
λₑ(t)=λ₀exp[α(Eₑ/E_c−1)]1_{Eₑ>E_c}g(Hₑ,σₑ),
$$

其中 Eₑ 是外加电场投影，Hₑ 表示湿度或气溶胶条件，σₑ 是导电率。流注从 e 延伸到 f 的概率矩阵 B 的零元位置可受 FIB 路径支撑，但其数值由电离、附着、空间电荷和局部场增强决定。

在分支近似下，ρ(B)<1 时放电簇有限且等待时间具有外加截断；ρ(B) 接近一时可出现长流注、雷击贯通和电流雪崩；重尾气溶胶或共同雷暴驱动会产生 Cox 混合和跨事件相关。放电电流 I(t)、辐射场和传感器峰值还经过带宽、饱和、阈值与方向性投影，同一真实流注可产生不同的极值读数。

固定同一 FIB 复形，调节湿度、背景电势或碰撞参数可以在无放电、局部辉光和贯通闪电之间切换；保持平均放电率而改变空间相关，则可改变流注长度尾和峰值电流尾。故 FIB 的面数、回路数或层级长度不能单独确定闪电阈值、放电能量、分枝维数或极值分布。

若取 j→∞，还必须规定复形嵌入的体积测度、介电和导电系数收敛、雷暴外源的共同概率空间、流注核心尺度、边界和探测器分辨率。FIB ATOM 递归在闪电问题中只提供组合电荷支撑和候选分枝路径；电场演化、放电首达、雷击计数和极值统计均是外加电磁—电离模型的条件结论。
## 283. 稀疏组成下的条件联合远频局部化

本节的来源仍为定义 1.1、2.1 的自由有序非空满二叉树，采样假设明确取固定组成纤维上的均匀律 $U(a,b)$。左右次序及每一种二叉括号化分别保留。原替换逐字为
$$
\rho(\alpha)=\beta,\qquad \rho(\beta)=\langle\beta,\alpha\rangle,
\qquad \rho(\langle s,t\rangle)=\langle\rho(s),\rho(t)\rangle.
$$
沿用[母卷](FIBONACCI_ATOMIC_RELATION_GENERATION.md) §§357、359、360 的同源观察
$W_3(t)=(E(t),E(\rho t),E(\rho^2t))$，其中 $E$ 保持叶序，且
$A^2=1$、$B^2=-1$、$AB+BA=1$。母卷定理 359.3 的唯一正规形为
$$
W_3(t)=L(u,v,w)R_{pq},\qquad
L(u,v,w)=\bigl((-1)^vS^{2u},(-1)^wS^{2v},(-1)^uS^{2w}\bigr),
\qquad S=BA,
$$
其中 $R_{00}=(1,1,1)$、$R_{10}=(A,B,S)$、$R_{01}=(B,S,A+B)$、$R_{11}=R_{10}R_{01}$，
$p=a\bmod2$、$q=b\bmod2$。令 $Z=(u,v,w)$，始终用同一个 $U(a,b)$ 定义精确有限均值
$\mu_{ab}=\mathbb E_{ab}Z$ 和完整协方差 $\Sigma_{ab}=\operatorname{Cov}_{ab}Z$。
这里的 $L(u,v,w)$ 是母卷的三元组记号，下文不带参数的 $L$ 是间隔总长度；下文的标量 $D$ 是符号长度，不是母卷的向量 $A+B$。

取整数 $k\ge64$、$M\ge3(k+1)$，置
$$
d=k+1,\qquad \delta_g=\frac{d}{M+d},\qquad
\gamma=\delta_g(2-\delta_g),\qquad \kappa=k\bmod2.
$$
用于原组成时取 $k=\min(a,b)$、$M=\max(a,b)$、$n=a+b=k+M$。$\delta_g$ 仅为辅助几何倾斜参数，与假设 1.4 的物理时间单位 $\delta$ 不同。
在未条件化的辅助概率空间上，令 $r_0,\ldots,r_k$ 独立，且
$$
\mathbb P(r_i=m)=\delta_g(1-\delta_g)^m\quad(m\in\mathbb Z_{\ge0}).
$$
定义
$$
L=\sum_{i=0}^k r_i,\qquad
\varepsilon_0=0,\qquad
\varepsilon_j=\left(\sum_{i<j}r_i\right)\bmod2\quad(1\le j\le k+1),
$$
$$
O=\sum_{\substack{1\le j\le k\\j\text{ 奇}}}\varepsilon_j,
\qquad E=\sum_{\substack{1\le j\le k\\j\text{ 偶}}}\varepsilon_j,
\qquad H=\sum_{\substack{0\le i\le k\\i\text{ 奇}}}r_i,
\qquad D=L-2H.
$$
令 $\mathbb T=\mathbb R/(2\pi\mathbb Z)$，$\operatorname{dist}_{\mathbb T}$ 为圆周距离，所有环面积分均为未归一化 Lebesgue 积分。令
$$
\chi(t,x,y)=\mathbb E\bigl[e^{i(tH+xO+yE)}\mid L=M\bigr].
$$
对实数 $R\ge1$，令 $U_R$ 为 $j=0,1$ 两个圆周盒的并：
$$
U_R=\bigcup_{j=0}^1\left\{(t,x,y)\in\mathbb T^3:
\operatorname{dist}_{\mathbb T}(t,j\pi)\le\frac{R\delta_g}{\sqrt k},\quad
\operatorname{dist}_{\mathbb T}(x,j\pi)\le\frac R{\sqrt k},\quad
\operatorname{dist}_{\mathbb T}(y,j\pi)\le\frac R{\sqrt k}\right\}.
$$
圆周半宽达到 $\pi$ 时，相应条件覆盖整个圆周。

**定理 283.1（保留精确总长度条件的联合远频尾界）。** 存在绝对常数 $C<\infty$，使全部整数 $k\ge64$、$M\ge3(k+1)$ 和全部实数 $R\ge1$ 同时满足
$$
\frac{k^{3/2}}{\delta_g}
\int_{\mathbb T^3\setminus U_R}|\chi(t,x,y)|\,dt\,dx\,dy
\le C(1+R)^{-2}.
\tag{283.1}
$$
因此对于每条 $k\to\infty$、$k/(k+M)\to0$ 的原稀疏序列，归一化远频积分的上极限再随 $R\to\infty$ 趋于零。这里的有限参数阈值和二阶尾幂都是方便的充分条件，不声称必要性、尖锐性或最优性。

**证明。** 先精确回接实际来源。由定理 2.2，每个组成 $(a,b)$ 的叶词有同一个 Catalan 括号数 $C_{a+b-1}$；只有推到叶词之后，$U(a,b)$ 才成为全部 $\binom{a+b}{a}$ 个该组成词的均匀律。以少数字母作分隔符，两个方向的词分别唯一写成
$$
b^{r_0}a b^{r_1}a\cdots a b^{r_k}\quad(a=k,b=M),
\qquad
a^{r_0}b a^{r_1}b\cdots b a^{r_k}\quad(b=k,a=M).
$$
零间隔合法，来源非空，且 $\sum r_i=M$。每个这样的弱组成在辅助层都有相同概率
$\delta_g^d(1-\delta_g)^M$。故条件于 $L=M$ 后，恰得原均匀弱组成及原实际叶词律，不是另一种平稳 Markov 律或独立边缘乘积。

在未条件化层写 $r_i=2T_i+\xi_i$，其中 $\xi_i\in\{0,1\}$。直接由几何质量函数分解得
$$
\mathbb P(T_i=m)=\gamma(1-\gamma)^m,\qquad
\mathbb P(\xi_i=1)=\nu:=\frac{1-\delta_g}{2-\delta_g},\qquad
\mathbb P(\xi_i=0)=\frac1{2-\delta_g}.
$$
所有 $T_i$、$\xi_i$ 在这一层相互独立；因为 $1-\gamma=(1-\delta_g)^2$，两质量函数的乘积正好等于 $\mathbb P(r_i=2m+\xi_i)$。条件于 $L=M$ 后不再使用这种独立性。

保留总长度、两个奇偶占据量 和奇间隔长度的完整四维特征函数为
$$
F(s,t,x,y)=\mathbb E e^{i(sL+tH+xO+yE)}.
$$
置
$$
N_e=\lfloor k/2\rfloor+1,\qquad N_o=\lceil k/2\rceil,
\qquad a_\gamma(z)=\frac\gamma{1-(1-\gamma)e^{iz}},
\qquad
\lambda_i=\begin{cases}s&i\text{ 偶},\\s+t&i\text{ 奇}.
\end{cases}
$$
独立分解给出精确等式
$$
F(s,t,x,y)=a_\gamma(2s)^{N_e}
a_\gamma(2(s+t))^{N_o}K(s,t,x,y),
\qquad
K=\mathbb E e^{i(\sum_{i=0}^k\lambda_i\xi_i+xO+yE)}.
\tag{283.2}
$$
这里 $\xi_i=\varepsilon_i+\varepsilon_{i+1}\pmod2$，末端 $\xi_k$ 和 $\varepsilon_{k+1}$ 均保留。

在各长度角上选圆周分支
$$
s=\pi h_e+u_e,\qquad s+t=\pi h_o+u_o,
\qquad h_e,h_o\in\{0,1\},\quad |u_e|,|u_o|\le\pi/2,
\qquad j=h_e+h_o\pmod2.
\tag{283.3}
$$
分支边界的重叠是零测集。由于 $\delta_g\le1/4$，$\nu\in[3/7,1/2]$，$\varepsilon$ 链的每个转移概率都在 $[1/3,2/3]$。固定全部偶位置状态及端点 $\varepsilon_0,\varepsilon_{k+1}$ 后，内部奇位置状态条件独立；固定另一种奇偶位置 时同理。这是链路径质量按相邻边乘积的直接分解：每个待积分状态只连接两个已固定邻居，其两种未归一化权重各在 $[1/9,4/9]$，故条件二点参数 $w$ 在 $[1/5,4/5]$。

翻转内部 $\varepsilon_l$ 从零到一，其相位差为
$$
\Delta_l=\theta_l+(1-2\varepsilon_{l-1})\lambda_{l-1}
+(1-2\varepsilon_{l+1})\lambda_l,
\qquad
\theta_l=\begin{cases}x&l\text{ 奇},\\y&l\text{ 偶}.
\end{cases}
$$
相邻两条边一种为偶、一种为奇，故按 (283.3)
$$
\Delta_l=\theta_l+j\pi+v_l\pmod{2\pi},\qquad
|v_l|\le|u_e|+|u_o|.
$$
对 $w\in[1/5,4/5]$，直接取模平方并用 $\sqrt{1-z}\le e^{-z/2}$ 得
$$
|1-w+we^{i\Delta}|
\le\exp\{-2w(1-w)\sin^2(\Delta/2)\},\qquad
w(1-w)\ge\frac4{25}.
$$
由正弦的 Lipschitz 界和 $(a+b)^2\le2a^2+2b^2$，
$$
\sin^2\frac{\theta+j\pi+v}{2}
\ge\frac12\sin^2\frac{\theta+j\pi}{2}-\frac{v^2}{4}
\ge\frac12\sin^2\frac{\theta+j\pi}{2}
-\frac{u_e^2+u_o^2}{2}.
$$
若 $n_o=\lceil k/2\rceil$、$n_e=\lfloor k/2\rfloor$ 是内部奇、偶状态数，先对奇状态积分再取剩余期望的模，得到
$$
|K|\le\exp\left\{-\frac{4n_o}{25}\sin^2\frac{x+j\pi}{2}
+\frac{4n_o}{25}(u_e^2+u_o^2)\right\}.
$$
偶状态给对应的 $y,n_e$ 上界。对这两个上界取几何平均，使用 $n_o,n_e\ge k/3$、$n_o+n_e=k$，便得全域估计
$$
|K|\le\exp\left\{-\frac{2k}{75}
\left(\sin^2\frac{x+j\pi}{2}+\sin^2\frac{y+j\pi}{2}\right)
+\frac{2k}{25}(u_e^2+u_o^2)\right\}.
\tag{283.4}
$$
此处固定另一奇偶位置 的条件积分完全发生在未条件化辅助层；没有把 $L=M$ 后的 $O,E,H$ 当成独立变量。

现在在全频域吸收正相位误差。精确几何模长为
$$
|a_\gamma(2u)|=(1+A_\gamma\sin^2u)^{-1/2},\qquad
A_\gamma=\frac{4(1-\gamma)}{\gamma^2}.
$$
$\gamma\le7/16$ 给 $A_\gamma\ge576/49$。对 $|u|\le\pi/2$，利用
$\sin^2u\ge4u^2/\pi^2$ 及对数凹性
$\log(1+Av)\ge v\log(1+A)$（$0\le v\le1$），得
$$
\log(1+A_\gamma\sin^2u)
\ge\frac{4u^2}{\pi^2}\log\frac{625}{49}
\ge\frac45u^2.
\tag{283.5}
$$
最后一步只需 $\pi^2<10$ 和 $\log(625/49)>2$；后者由 $e<3$、$9<625/49$ 得到。
每个几何因子的一半指数因 $N_e,N_o\ge k/2$ 至少提供 $ku^2/10$，足以吸收 (283.4) 的 $2ku^2/25$。由 (283.2) 得
$$
|F|\le
\exp\left\{-\frac{2k}{75}
\left(\sin^2\frac{x+j\pi}{2}+\sin^2\frac{y+j\pi}{2}\right)\right\}
(1+A_\gamma\sin^2u_e)^{-N_e/4}
(1+A_\gamma\sin^2u_o)^{-N_o/4}.
\tag{283.6}
$$

环面变换 $(s,t)\mapsto(s,s+t)$ 是行列式为一的整数幺模变换，保持未归一化测度。两个新长度角分别分为零、$\pi$ 分支，四个分支全部保留。在每个分支取
$$
z_e=\frac{\sqrt k\,u_e}{\gamma},\qquad
z_o=\frac{\sqrt k\,u_o}{\gamma},\qquad
z_x=\sqrt k\,\operatorname{rep}_{\mathbb T}(x-j\pi),\qquad
z_y=\sqrt k\,\operatorname{rep}_{\mathbb T}(y-j\pi),
$$
其中 $\operatorname{rep}_{\mathbb T}\in[-\pi,\pi]$，端点任取；局部 Jacobian 为 $\gamma^2/k^2$。
由 $1-\gamma\ge9/16$、$\pi^2<10$，
$$
A_\gamma\sin^2u\ge\frac{9u^2}{10\gamma^2}.
$$
对每个 $A\ge0$，函数 $v\log(1+A/v)$ 随 $v>0$ 递增，因为其导数
$\log(1+A/v)-(A/v)/(1+A/v)$ 非负。因此 $k\ge64$ 时
$$
(1+A_\gamma\sin^2u)^{-N/4}
\le\left(1+\frac{9z^2}{10k}\right)^{-k/8}
\le\left(1+\frac{9z^2}{640}\right)^{-8}
\quad(N\ge k/2).
$$
同时 $\sin^2(\theta/2)\ge\theta^2/\pi^2\ge\theta^2/10$（$|\theta|\le\pi$）。于是 (283.6) 的固定可积包络为
$$
|F|\le f(z_e)f(z_o)g(z_x)g(z_y),\qquad
f(z)=\left(1+\frac{9z^2}{640}\right)^{-8},\qquad
g(z)=e^{-z^2/375}.
\tag{283.7}
$$
$f,g$ 的零阶及二阶绝对矩有限，且与 $k,M$ 无关。

若 $|u_e|,|u_o|\le R\delta_g/(2\sqrt k)$，且两个奇偶占据量 角到 $j\pi$ 的圆周距离均不超过 $R/\sqrt k$，则
$t=j\pi+u_o-u_e\pmod{2\pi}$，所以 $(t,x,y)\in U_R$。
又 $\gamma\le2\delta_g$，故 $U_R$ 外至少发生
$$
|z_e|>R/4,\quad |z_o|>R/4,\quad |z_x|>R,\quad |z_y|>R
$$
四件事之一。对每件事用 $\int_{|z|>h}f(z)\,dz\le h^{-2}\int z^2f(z)\,dz$ 或相应的 $g$ 界，再将另外三个变量在实线上积分。合并四个分支及四种事件，$R\ge1$ 时得到
$$
\int_{\substack{s\in\mathbb T\\(t,x,y)\notin U_R}}|F(s,t,x,y)|\,ds\,dt\,dx\,dy
\le C_1\frac{\gamma^2}{k^2}(1+R)^{-2}
\le4C_1\frac{\delta_g^2}{k^2}(1+R)^{-2}.
\tag{283.8}
$$
两个长度尺度的体积在此保留，未用一个仅随 $k$ 衰减的常数取代几何平滑。

条件事件的分母是精确负二项质量。令 $N=M+d$，则
$$
p_{k,M}:=\mathbb P(L=M)
=\binom{M+k}{k}\delta_g^d(1-\delta_g)^M
=\delta_g\,\mathbb P\{\operatorname{Bin}(N,\delta_g)=d\}.
\tag{283.9}
$$
直接复用钉版 mathlib 的 [Stirling 源码](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/Stirling.lean)：
`Stirling.le_factorial_stirling` 给全局阶乘下界；`Stirling.stirlingSeq'_antitone` 和 `Stirling.stirlingSeq_one` 给正整数序列的全局上界。按其定义，这些已知结果供给全部正整数 $m$ 上的
$$
c\sqrt m\,(m/e)^m\le m!\le C_{\mathrm{St}}\sqrt m\,(m/e)^m
$$
及绝对常数 $c,C_{\mathrm{St}}>0$。在 $\delta_g=d/N$ 下将这些界代入
$$
\frac{N!}{d!M!}\left(\frac dN\right)^d\left(\frac MN\right)^M
$$
时，全部幂和指数项恰好相消，因为 $N=d+M$。因此
$$
\mathbb P\{\operatorname{Bin}(N,\delta_g)=d\}
\ge c_0\sqrt{\frac{N}{dM}}\ge\frac{c_0}{\sqrt d},
\qquad
p_{k,M}\ge c_1\frac{\delta_g}{\sqrt k},
\tag{283.10}
$$
其中用 $d=k+1\le(65/64)k$。该界对全部有限参数一致，不调用固定成功概率的二项局部极限。

整数总长度的精确 Fourier 提取为
$$
\chi(t,x,y)=\frac1{2\pi p_{k,M}}
\int_{\mathbb T}e^{-isM}F(s,t,x,y)\,ds.
\tag{283.11}
$$
这是 $\mathbf1_{\{L=M\}}=(2\pi)^{-1}\int_{\mathbb T}e^{is(L-M)}ds$ 的直接应用；被积函数有界，交换期望与有限测度积分合法。由三角不等式、(283.8) 和 (283.10)，
$$
\int_{\mathbb T^3\setminus U_R}|\chi|
\le C_2\frac{\sqrt k}{\delta_g}\frac{\delta_g^2}{k^2}(1+R)^{-2}
=C_2\frac{\delta_g}{k^{3/2}}(1+R)^{-2},
$$
即 (283.1)。下面将同一结论的来源、格和精确协方差消费者写全。

母卷引理 359.2 的全部八条增量为

| 起点 | 字母 | 终点 | $(\Delta u,\Delta v,\Delta w)$ |
|---|---|---|---|
| $00$ | $a$ | $10$ | $(0,0,0)$ |
| $00$ | $b$ | $01$ | $(0,0,0)$ |
| $10$ | $a$ | $00$ | $(0,0,1)$ |
| $10$ | $b$ | $11$ | $(0,0,0)$ |
| $01$ | $a$ | $11$ | $(1,1,-1)$ |
| $01$ | $b$ | $00$ | $(0,1,0)$ |
| $11$ | $a$ | $01$ | $(-1,-1,0)$ |
| $11$ | $b$ | $10$ | $(0,-1,0)$ |

对固定组成，实际支撑完全沿用母卷定理 360.2：
$$
X=\frac{a-p-2w+2u}{4},\qquad Y=\frac{b-q-2u+2v}{4}
$$
必须为整数，且
$$
\begin{aligned}
x_{00}&=X+w-u+p,&x_{10}&=X+w,&x_{01}&=X,&x_{11}&=X-u,\\
y_{00}&=Y+u+q(1-p),&y_{01}&=Y,&y_{10}&=Y-v+pq,&y_{11}&=Y+u-v
\end{aligned}
$$
八数全部非负，并且正重数边的端点连同起点 $00$ 构成弱连通支撑。弱组成与叶词的双射保留该完整 Euler 可实现性；条件律不向只有流量合法而支撑不连通的点分配概率，实际支撑外的概率始终为零。

在方向 $a=k,b=M$，第 $j$ 个 $a$ 之前的状态为 $(j-1\bmod2,\varepsilon_j)$。由八边表，所有 $a$ 的 $u,v$ 增量之和均为 $O-E$，$w$ 增量之和为 $\lfloor k/2\rfloor-O-E$。第 $i$ 个 $b$ 间隔对 $v$ 的贡献为
$(-1)^i(r_i+\varepsilon_i-\varepsilon_{i+1})/2$；望远镜求和给
$D/2+E-O-(-1)^kq/2$，因为 $\varepsilon_{k+1}=q$。因此精确地
$$
Z=\left(O-E,\frac{M-2H-(-1)^kq}{2},\lfloor k/2\rfloor-O-E\right)
\qquad(a=k,b=M).
\tag{283.12}
$$
在方向 $b=k,a=M$，第 $j$ 个 $b$ 前的状态为 $(\varepsilon_j,j-1\bmod2)$。奇 $a$ 间隔对 $u,v$ 的贡献均为 $\varepsilon_{i+1}-\varepsilon_i$，其总和为 $E-O+\kappa p$；所有 $b$ 对 $v$ 的贡献为 $\lfloor k/2\rfloor-2E$。第 $i$ 个 $a$ 间隔对 $w$ 的贡献为
$[(-1)^ir_i+\varepsilon_i-\varepsilon_{i+1}]/2$，总和为 $(D-p)/2$。由于 $q=\kappa$，
$$
Z=\left(E-O+pq,\lfloor k/2\rfloor-O-E+pq,\frac{M-2H-p}{2}\right)
\qquad(b=k,a=M).
\tag{283.13}
$$
两式保留末端奇偶状态，均由同一八边路径求和，不以换过程或交换独立边缘取得第二方向。

辅助层有精确模二恒等式
$$
H-O-E\equiv\kappa L\pmod2.
\tag{283.14}
$$
确实，$L\equiv\varepsilon_{k+1}$，而 $\sum_{i\text{ 奇}}\xi_i$
恰为全部内部 $\varepsilon_1,\ldots,\varepsilon_k$ 之和再加上 $\kappa\varepsilon_{k+1}$。这也说明为何不能丢去末端。
未条件化 $F$ 的真实字符，亦即 $F=1$ 的点，恰为
$$
(0,0,0,0),\qquad (\kappa\pi,\pi,\pi,\pi).
\tag{283.15}
$$
为排除遗漏，注意辅助律的每个非负间隔向量都有正质量，且零向量也有正质量。因此模长为一迫使全部相位恒为一。任意 $T_i$ 的变化先迫使
$\lambda_e=m_e\pi$、$\lambda_o=m_o\pi$。所有内部二进制状态可以独立指定，故其系数迫使
$x=y=(m_e+m_o)\pi\pmod{2\pi}$；末端系数另迫使 $m_k$ 为偶数。$k$ 偶时须 $m_e$ 偶，$k$ 奇时须 $m_o$ 偶，正好留下 (283.15) 两点。四个长度平滑分支只有两个满足末端字符条件，不能将分支数当成字符数。在 $L=M$ 后，两个 H 中心为 $(0,0,0)$、$(\pi,\pi,\pi)$，后者的未中心化相位是 $(-1)^{\kappa M}$。

H 与 D 坐标之间的关系同样精确。若
$F_D(\alpha,\beta,x,y)=\mathbb E e^{i(\alpha L+\beta D+xO+yE)}$，
$\psi_D(\beta,x,y)=\mathbb E[e^{i(\beta D+xO+yE)}\mid L=M]$，则
$$
F_D(\alpha,\beta,x,y)=F(\alpha+\beta,-2\beta,x,y),\qquad
\psi_D(\beta,x,y)=e^{i\beta M}\chi(-2\beta,x,y).
\tag{283.16}
$$
前一整数环面映射的 Jacobian 绝对值为二、覆盖度为二；后一 $\beta\mapsto-2\beta$ 也是二重覆盖。分支换元时局部测度因子 $1/2$ 与两份原像相消，故完整未归一化环面积分保持测度。H 的两个中心拉回为 D 的四个中心，长角盒半宽缩为 $R\delta_g/(2\sqrt k)$；以半宽 $R\delta_g/\sqrt k$ 选取的 D 宽盒包含该拉回。这个关系不产生额外概率格因子。

具体地，令 $\sigma_k=(-1)^k$，未条件化 D 的四个真实字符为
$$
\ell\left(\frac\pi2,-\frac{\sigma_k\pi}{2},\pi,\pi\right)
\pmod{2\pi},\qquad \ell=0,1,2,3.
$$
它们恰为 (283.15) 的原像，也对应同一个恒等式
$L-\sigma_kD-2(O+E)\equiv0\pmod4$：$k$ 偶时左侧为 $2(H-O-E)$，$k$ 奇时为 $2(L-H-O-E)$，均由 (283.14) 整除四。在 $L=M$ 后，D 中心为
$\ell(-\sigma_k\pi/2,\pi,\pi)$，相位为 $e^{-i\ell\pi M/2}$，并非一律为一。D 表示中的八个辅助长度分支、四个真实字符以及 H 的两个条件中心是不同对象。

现将条件格降到原始整数坐标。由 (283.14)，
$$
J=\frac{H-O-E-\kappa M}{2},\qquad W=(O,E,J)
$$
在条件律下为整数向量。(283.12)、(283.13) 从 $W$ 到 $Z$ 的差分矩阵分别为
$$
C_1=\begin{pmatrix}1&-1&0\\-1&-1&-2\\-1&-1&0\end{pmatrix},\qquad
C_2=\begin{pmatrix}-1&1&0\\-1&-1&0\\-1&-1&-2\end{pmatrix},
\qquad |\det C_1|=|\det C_2|=4.
$$
题定格基及其对应变换为
$$
B=\begin{pmatrix}2&0&1\\0&2&1\\0&0&1\end{pmatrix},\qquad
A_1=B^{-1}C_1=\begin{pmatrix}1&0&0\\0&0&-1\\-1&-1&0\end{pmatrix},\qquad
A_2=B^{-1}C_2=\begin{pmatrix}0&1&1\\0&0&1\\-1&-1&-2\end{pmatrix}.
\tag{283.17}
$$
$A_1,A_2$ 均为整数幺模矩阵。

母卷 360 的整数性给
$$
\Lambda_{ab}=\left\{(u,v,w)\in\mathbb Z^3:
w-u\equiv\frac{a-p}{2}\pmod2,\quad
u-v\equiv\frac{b-q}{2}\pmod2\right\}.
$$
差分满足 $w-u\equiv u-v\equiv0\pmod2$，恰为 $B\mathbb Z^3$。
这里复用旧实际支持判据，还可直接核对其充分支撑应用：组成 $(4,4)$ 下的
$0,2e_1,2e_2,2e_3,(1,1,1)$ 均实际可达。按上述八边次序
$(x_{00},x_{10},x_{01},x_{11};y_{00},y_{01},y_{10},y_{11})$，对应重数分别为
$$
\begin{array}{c|c}
0&(1,1,1,1;1,1,1,1)\\
2e_1&(0,2,2,0;2,0,0,2)\\
2e_2&(1,1,1,1;2,2,0,0)\\
2e_3&(2,2,0,0;1,1,1,1)\\
(1,1,1)&(1,2,1,0;2,1,0,1).
\end{array}
$$
每行非负且包含起点的弱支撑连通，所以定理 360.2 供应实际词及全部括号化。对 $a,b\ge4$，给这些词共同追加任一组成 $(a-4,b-4)$ 的后缀；后缀总长为零时不作追加，不引入空来源。前缀终点同为 $00$，故右乘同一个后缀窗口只加上相同整数偏移，保留全部差分。
这些差分生成 $B\mathbb Z^3$，因为 $2e_3=2(1,1,1)-2e_1-2e_2$。于是实际最大差分格恰为 $B\mathbb Z^3$，且实际支持包含仿射张成 $\mathbb R^3$ 的点。所有实际词在 $U(a,b)$ 下有正质量，故任意非零线性泛函的方差为正，$\Sigma_{ab}$ 正定。这只是旧支持结果的应用；阈值四以及另取阈值八的充分应用范围都不承担新尾界，也不互相矛盾。

取实际支持点 $z_0$，令
$$
Y=B^{-1}(Z-z_0),\qquad m=\mathbb EY,\qquad
V=B^{-1}\Sigma_{ab}B^{-T},\qquad
\Psi(\zeta)=\mathbb E e^{i\zeta\cdot(Y-m)}.
$$
中心化特征函数选定角度的实代表书写；其模不依赖代表，因而是环面上的函数。若 $\phi_W(\eta)=\mathbb E[e^{i\eta\cdot W}\mid L=M]$，则
$$
\chi(\tau,x,y)=e^{i\kappa M\tau}\phi_W(x+\tau,y+\tau,2\tau).
\tag{283.18}
$$
频率商映射
$q_H(\tau,x,y)=(x+\tau,y+\tau,2\tau)$ 的核恰为两个 H 中心，Jacobian 绝对值与覆盖度均为二。故两中心在原始格频域合为一个原点，完整积分不额外乘二。上述支持差分和 (283.17) 还说明 $W$ 的差分格是 $\mathbb Z^3$，所以条件 H 的模长一字符恰为这两个中心，没有其它条件字符。
令 $\mathcal A=A_1$ 或 $A_2$ 按稀疏方向选择，并置
$$
\Omega_R=\{\zeta\in\mathbb T^3:\mathcal A^T\zeta\in q_H(U_R)\}.
$$
$U_R$ 在加核元下不变，故 $q_H^{-1}(q_H(U_R))=U_R$。从 $W$ 到 $Y$ 是差分矩阵 $\mathcal A$ 的仿射变换，中心化仅乘模长一的相位。由两次保持测度的换元，精确地
$$
\int_{\mathbb T^3\setminus\Omega_R}|\Psi(\zeta)|\,d\zeta
=\int_{\mathbb T^3\setminus U_R}|\chi(t,x,y)|\,dt\,dx\,dy.
\tag{283.19}
$$
因此不用表面字符数猜测归一化。对于原精确协方差，
$$
\sqrt{\det V}=\frac{\sqrt{\det\Sigma_{ab}}}{4},\qquad
\phi_V(B^{-1}(z-\mu_{ab}))=4\phi_{\Sigma_{ab}}(z-\mu_{ab}),
$$
其中 $\phi_\Sigma(y)=(2\pi)^{-3/2}(\det\Sigma)^{-1/2}e^{-y^T\Sigma^{-1}y/2}$。
原目标中的四恰是 $|\det B|$；两个 H 中心、四个 D 中心或辅助长度分支均不能再乘入此因子。

最后用同一精确条件律支付实际行列式尺度，不借用协方差渐近假设。均匀弱组成具有已知 Dirichlet—多项式混合表示：先取
$(P_0,\ldots,P_k)\sim\operatorname{Dirichlet}(1,\ldots,1)$，再条件于 $P$ 做 $M$ 次多项抽样。直接积分单纯形密度给每个 $\sum r_i=M$ 的向量同一个质量
$M!(d-1)!/(M+d-1)!$，所以该表示就是已经确定的条件律。
令 $Q_j=\sum_{i<j}r_i$、$\eta_j=(-1)^{Q_j}$、$c_j=\mathbb E[\eta_j\mid L=M]$。聚合前 $j$ 个单纯形分量给
$$
c_j=\mathbb E(1-2X)^M,\qquad X\sim\operatorname{Beta}(j,d-j)
\quad(1\le j\le d-1).
$$
置 $\theta=d/(2M)\le1/6$。Beta 密度为
$\Gamma(d)x^{j-1}(1-x)^{d-j-1}/[\Gamma(j)\Gamma(d-j)]$。
将积分在 $1/2$ 分开，利用
$|1-2x|^M\le e^{-2M\min(x,1-x)}$，在前半段丢去不超过一的 $(1-x)^{d-j-1}$ 并延长到正实轴，给
$$
\frac{\Gamma(d)}{\Gamma(d-j)(2M)^j}
\le\left(\frac d{2M}\right)^j.
$$
后半段换元 $x\mapsto1-x$ 得 $\theta^{d-j}$。因此
$$
|c_j|\le\theta^j+\theta^{d-j},\qquad
\sum_{j=1}^{d-1}|c_j|\le\frac{2\theta}{1-\theta}\le\frac25.
$$
间隔交换性又给 $\mathbb E[\eta_i\eta_j\mid L=M]=c_{|i-j|}$（$i\ne j$）。两方向的两个短 $Z$ 坐标都为常数加 $\sum_{j=1}^k a_j\eta_j$，其中 $|a_j|=1/2$。保留同一联合律，使用方差不超过二阶矩，逐个得到
$$
\operatorname{Var}\left(\sum_j a_j\eta_j\right)
\le\frac k4+\frac12\sum_{h=1}^{k-1}(k-h)|c_h|
\le\frac{9k}{20}.
$$
长坐标都是常数减 $H$。混合表示中 $P_H=\sum_{i\text{ 奇}}P_i$ 服从 $\operatorname{Beta}(N_o,N_e)$，且 $H\mid P_H\sim\operatorname{Bin}(M,P_H)$。其精确均值为 $MN_o/d$；由
$\mathbb EP_H=N_o/d$、$\operatorname{Var}P_H=N_oN_e/[d^2(d+1)]$、
$\mathbb E[P_H(1-P_H)]=N_oN_e/[d(d+1)]$ 及全方差公式，
$$
\operatorname{Var}(H)=\frac{M N_eN_o(M+d)}{d^2(d+1)}
\le\frac{M^2}{3(d+1)}.
$$
最后一步用 $N_eN_o\le d^2/4$、$M+d\le4M/3$。Hadamard 不等式作用于完整协方差矩阵，给
$$
\sqrt{\det\Sigma_{ab}}
\le\frac{9k}{20}\frac{M}{\sqrt{3(d+1)}}
\le C_3M\sqrt k\le C_4\frac{k^{3/2}}{\delta_g}.
\tag{283.20}
$$
这里没有将任何交叉协方差置零。由 (283.1)、(283.19)、(283.20)，本单条尾界在原精确格坐标中的实际应用为
$$
\sqrt{\det V}\int_{\mathbb T^3\setminus\Omega_R}|\Psi(\zeta)|\,d\zeta
\le C_5(1+R)^{-2}.
$$
这只支付真实特征函数的远频部分。每条原序列最终满足 $k\ge64$、$M\ge3(k+1)$，因 $k\to\infty$ 且 $k/M\to0$，故两方向全部原速率均被保留；没有 $k\gg\log M$、固定多项式间隔或固定非退化协方差条件。纯端点 $a=0$ 或 $b=0$ 则复用八边表的点质量：分别为 $(0,\lfloor b/2\rfloor,0)$、$(0,0,\lfloor a/2\rfloor)$，协方差为零；它们不满足本节阈值，也不是稀疏目标。$\square$

数学范围与引文：来源、唯一正规形、完整八边及 Euler 支撑直接复用统计卷 2.1—2.2 和[母卷 §§357、359、360](https://github.com/the-omega-institute/trureturing/blob/520fd10f7cb6ad7cfcc2dc5dd3f76144be250fa6/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)。Catalan 消去、几何条件化、有限矩和整数格换元在证明内承担同源回接；Stirling 的已知全局界只供应条件分母。定理 283.1 的实质纸面推导是将 占据量收缩的相位误差吸收到两个长度平滑因子，再在全部有限参数上一致积分并精确条件化；它不是固定概率局部极限定理的改名应用。本文不宣称 Lean 内核核验或全球原创性。

尚未证明的全目标仍为：对每条整数组成序列 $n_j=a_j+b_j$、$k_j=\min(a_j,b_j)\to\infty$、$k_j/n_j\to0$，在同一 $U(a_j,b_j)$ 下，
$$
\sup_{z\in\Lambda_{a_jb_j}}\sqrt{\det\Sigma_{a_jb_j}}
\left|\mathbb P_{a_jb_j}(Z=z)
-4\phi_{\Sigma_{a_jb_j}}(z-\mu_{a_jb_j})\right|\longrightarrow0,
$$
其中实际 Euler 支撑外的概率为零。对于其充分 Fourier 接口，令
$$
G(\zeta)=\sum_{\ell\in\mathbb Z^3}\phi_V(\ell-m)e^{i\zeta\cdot(\ell-m)}.
$$
$G$ 与 $\Psi$ 使用相同实代表；角度加上 $2\pi h$（$h\in\mathbb Z^3$）时，两者同乘 $e^{-2\pi i h\cdot m}$，所以 $|\Psi-G|$ 是环面函数。本节没有证明 $\sqrt{\det V}\int_{\mathbb T^3}|\Psi-G|\to0$。最小剩余分析义务是同一条件四维族在保留中心附近的联合高斯比较，精确提取 $L=M$ 后匹配实际 $\mu_{ab},\Sigma_{ab}$，以及 $G$ 在 $\Omega_R$ 外的一致尾控制。有限参数正定性与 (283.20) 的上界不供应缩放协方差的统一下界。固定律、标量局部极限或弱 Cramér—Wold 收敛不能替代这项条件联合义务；充分接口失败也不自动反驳原点态目标。

文献接口的限制具体为：Dolgopyat，*A Local Limit Theorem for sums of independent random vectors*，Electron. J. Probab. **21** (2016)，paper 39，[作者接受稿](https://math.umd.edu/~dolgop/LLTHDRevEJP.pdf)，Theorem 1.2 的独立增量、统一三阶矩与逐增量协方差下界不能直接供给本条件占据量族；未缩放几何奖励没有统一三阶矩，缩放后仍须处理依赖占据量、变化格距和总长度条件。Bodini—Ponty，*Multi-dimensional Boltzmann Sampling of Languages*，[arXiv:1002.0046v3](https://arxiv.org/abs/1002.0046v3)，§5.1、Theorem 5 的固定参数高斯应用不自动延伸到 $\delta_g\to0$ 的边界族。Kugler，*Local limit theorem for the maximum of a random walk in the heavy-traffic regime*，[arXiv:1403.7372v1](https://arxiv.org/abs/1403.7372v1)，Theorem 1 及 §2 Proposition 2 的固定格标量更新估计也不供应 $(L,H,O,E)$ 的精确条件向量桥。这些限制不排除另行验证的新表示或可适用定理。Bender—Richmond—Williamson，*Central and local limit theorems applied to asymptotic enumeration. III. Matrix recursions*，DOI [10.1016/0097-3165(83)90012-2](https://doi.org/10.1016/0097-3165(83)90012-2) 的原定理假设在这里未核验，不作为证明前提。

原仿射严格预算也仍未决：$r\ge7$ 为素数、$V=F_r$、非空连续
$I\subseteq[\lceil V/10\rceil,\lfloor V/5\rfloor]$、$N=1+Vg$、$A>5040$、固定 $C_0>1$、$A\le N\le C_0A$、$s=\log A\,\log\log A$，以及原 Möbius 增量 $b_s$ 和完整成本
$$
C^*+H^*<\left(\frac{\log\log N^*}{\log\log A}\right)^s.
$$
本尾界不支付这些同整数成本，不构造实际 Robin 反例，不关闭 RH 或 Robin；母卷 §365 在其实际最小公倍数族上的既有归约也不替代这一预算义务。

## 追加锚（本行以下为增补区）

## 284. 稀疏组成下的同源完整三维局部高斯律

来源与采样沿用定义 1.1、2.1：$\mathcal T$ 是自由有序非空满二叉树代数，左右次序与全部二叉括号化均保留，$U(a,b)$ 明确取组成纤维 $\mathcal F(a,b)$ 上的均匀律。原树替换为
$$
\rho(\alpha)=\beta,\qquad
\rho(\beta)=\langle\beta,\alpha\rangle,\qquad
\rho(\langle s,t\rangle)=\langle\rho(s),\rho(t)\rangle.
$$
叶积观察保持叶序，满足 $A^2=1$、$B^2=-1$、$AB+BA=1$；三个窗口始终由同一实际树生成：
$$
W_3(t)=(E(t),E(\rho t),E(\rho^2t)).
$$
直接采用[母卷](FIBONACCI_ATOMIC_RELATION_GENERATION.md)定理 359.3 的唯一正规形 $W_3(t)=L(u,v,w)R_{pq}$，令 $Z=(u,v,w)$、$p=a\bmod2$、$q=b\bmod2$。实际有限中心与完整协方差为
$$
\mu_{ab}=\mathbb E_{U(a,b)}Z,\qquad
\Sigma_{ab}=\operatorname{Cov}_{U(a,b)}Z.
$$
令
$$
\Lambda_{ab}=\left\{(u,v,w)\in\mathbb Z^3:
w-u\equiv\frac{a-p}{2}\pmod2,\quad
u-v\equiv\frac{b-q}{2}\pmod2\right\}.
$$
实际支撑仍由母卷定理 360.2 的八个非负整数边重数及含起点 $00$ 的弱 Euler 连通条件共同决定；$\Lambda_{ab}$ 中未满足该完整判据的点取零概率。

**定理 284.1（全部稀疏速率的完整同源局部极限）。** 对任意整数组成序列 $(a_j,b_j)$，若
$$
k_j=\min(a_j,b_j)\longrightarrow\infty,\qquad
\frac{k_j}{a_j+b_j}\longrightarrow0,
$$
则 $\Sigma_{a_jb_j}$ 最终正定，且
$$
\sup_{z\in\Lambda_{a_jb_j}}\sqrt{\det\Sigma_{a_jb_j}}
\left|\mathbb P_{U(a_j,b_j)}(Z=z)
-4\phi_{\Sigma_{a_jb_j}}(z-\mu_{a_jb_j})\right|
\longrightarrow0,
\tag{284.1}
$$
其中
$$
\phi_\Sigma(y)=(2\pi)^{-3/2}(\det\Sigma)^{-1/2}
\exp\!\left(-\frac12y^T\Sigma^{-1}y\right).
$$
两个稀疏方向可任意切换；除上述两个极限外，不要求其他速率条件。四是实际来源差分格的指数。

**证明。** 固定任意满足假设的序列，以下省略下标。置
$$
M=\max(a,b),\quad d=k+1,\quad
\delta_g=\frac d{M+d},\quad t_g=1-\delta_g,\quad
\gamma=1-t_g^2=\delta_g(2-\delta_g),\quad
\nu=\frac{t_g}{1+t_g},\quad
\varrho=1-2\nu=\frac{\delta_g}{2-\delta_g}.
$$
$\varrho$ 是辅助奇偶链的标量相关参数，与原树替换 $\rho$ 不同；$\delta_g$ 是几何倾斜参数。原假设给 $k\to\infty$、$\delta_g\to0$，故最终 $k\ge64$、$M\ge3d$、$0<\delta_g\le1/4$。以下概率律记为 $\mathsf Q,\mathsf R$，频域盒半径另记 $R$。

直接复用 §283 的实际来源回接：每个组成叶词有相同 Catalan 括号数；以少数字母分隔后，它与 $d$ 部分、总数 $M$ 的均匀弱组成一一对应。辅助层的 $r_0,\ldots,r_k$ 独立，质量为 $\delta_gt_g^m$（$m\ge0$），条件于 $L=\sum r_i=M$ 后恰为该实际组成律。沿用
$$
\varepsilon_0=0,\qquad
\varepsilon_j=\left(\sum_{i<j}r_i\right)\bmod2,\qquad
O=\sum_{\substack{1\le j\le k\\j\text{ 奇}}}\varepsilon_j,\quad
E=\sum_{\substack{1\le j\le k\\j\text{ 偶}}}\varepsilon_j,\quad
H=\sum_{\substack{0\le i\le k\\i\text{ 奇}}}r_i.
$$
不带树参数的 $E$ 是偶位置占据量，与叶积函数 $E(t)$ 不同。保留所有间隔、$\xi_k$ 和实际端点 $\varepsilon_d=M\bmod2$；八边及 Euler 支撑直接沿用 §283 与母卷 §§359—360，不以流量松弛改变来源。

在未条件化层写 $r_i=2T_i+\xi_i$，则全部 $T_i,\xi_i$ 相互独立，$T_i$ 的质量为 $\gamma(t_g^2)^m$，$\xi_i\sim\operatorname{Bernoulli}(\nu)$。这一独立性只在辅助层使用。令
$$
h=\sum_{i=0}^k\xi_i,\qquad
q_d(s)=\binom{s+d-1}{d-1}\gamma^d(t_g^2)^s\quad(s\in\mathbb Z_{\ge0}),
$$
$$
p_L=\binom{M+d-1}{d-1}\delta_g^dt_g^M,\qquad
p_e=\frac{1+(-1)^M\varrho^d}{2}.
$$
$\mathsf Q$ 为完整 $d$ 位独立 $\operatorname{Bernoulli}(\nu)$ 向量条件于 $h\equiv M\pmod2$ 的律，$\mathsf R$ 为该完整向量在实际 $L=M$ 条件律下的律。辅助独立分解精确给出
$$
u(\xi):=\frac{d\mathsf R}{d\mathsf Q}(\xi)
=\frac{p_eq_d((M-h)/2)}{p_L}.
\tag{284.2}
$$
对每个合法奇偶向量，$s=(M-h)/2$ 是整数且 $s\ge(M-d)/2\ge d$。

下面同时给出全域密度界与典型窗比较。记 $\lambda=t_g^2$、$s_0=d\lambda/\gamma$，并对 $s>0$ 定义
$$
f(s)=(s+d)\log(s+d)-s\log s-d\log d
+d\log\gamma+s\log\lambda.
$$
直接微分与代入得
$$
f(s_0)=f'(s_0)=0,\qquad f''(s)=-\frac d{s(s+d)},\qquad f(s)\le0.
$$
采用正整数阶乘的 Stirling 公式及其全局上下界。由精确恒等式
$$
\binom{s+d-1}{d-1}=\frac d{s+d}\frac{(s+d)!}{s!\,d!},
$$
对整数 $s\ge1$ 得
$$
q_d(s)=\frac d{s+d}\sqrt{\frac{s+d}{2\pi ds}}\,
e^{f(s)}(1+o(1)).
\tag{284.3}
$$
当 $\min(d,s,s+d)\to\infty$ 时余项一致；全局版本把 $1+o(1)$ 换为两个绝对正常数。这里仅对正阶乘参数使用此式。

为控制全部 $s\ge0$，包括零点，用质量比
$$
\frac{q_d(s+1)}{q_d(s)}=\lambda\frac{s+d}{s+1}.
$$
可取最大点 $m_d=\lfloor(d-1)\lambda/\gamma\rfloor$；比值等于一时相邻最大点同值。$d\ge65$、$\lambda\ge9/16$、$\gamma\le7/16$ 给
$$
\frac d{2\gamma}\le m_d\le\frac d\gamma,\qquad m_d\ge1.
$$
例如下界由 $m_d\ge(d-1)9/(16\gamma)-1\ge d/(2\gamma)$ 得到。因而最大点的三个阶乘参数至少为 $d$；(284.3) 的全局版本和 $f\le0$ 给
$$
\sup_{s\ge0}q_d(s)=q_d(m_d)
\le C\sqrt{\frac d{m_d(m_d+d)}}\le C\frac\gamma{\sqrt d}.
$$
此论证没有在 $s=0$ 使用 Stirling。复用 (283.10) 的 $p_L\ge c\delta_g/\sqrt d$，且 $p_e\le1$、$\gamma/\delta_g\le2$，便有
$$
0\le u(\xi)\le C_{\mathrm{dens}}
\tag{284.4}
$$
对全部有限参数及全部合法向量同时成立。又 $\varrho\le1/7$，故 $p_e\ge(1-1/7)/2>1/3$。

固定 $A_0<\infty$，在 $|h-d\nu|\le A_0\sqrt d$ 上，精确关系
$$
2s_0+d\nu=M,\qquad
s-s_0=-\frac{h-d\nu}{2}
$$
成立。当 $d\ge\max\{65,4A_0^2\}$ 时，$|s-s_0|\le d/4$，故 $s\ge d/(4\gamma)$，$s+d\ge d$；这些最小阶乘参数均趋于无穷。沿 $s,s_0$ 间的区间，$|f''|\le C\gamma^2/d$，所以
$$
|f(s)|\le C A_0^2\gamma^2,\qquad
\frac{d}{s+d}\sqrt{\frac{s+d}{2\pi ds}}
=\frac{\gamma}{t_g\sqrt{2\pi d}}(1+o(1))
$$
在该窗上一致成立。于是
$$
q_d((M-h)/2)=\frac{\gamma}{t_g\sqrt{2\pi d}}(1+o(1)).
$$
令 $N=M+d$。精确式 $p_L=\delta_g\binom Nd(d/N)^d(M/N)^M$ 在阶乘参数 $N,d,M$ 上用 Stirling；其最小值为 $d\to\infty$，幂项全部相消，得到
$$
p_L=\frac{\delta_g}{\sqrt{2\pi d t_g}}(1+o(1)).
$$
因此典型窗内
$$
u(\xi)=p_e\frac{2-\delta_g}{\sqrt{t_g}}(1+o(1))
\longrightarrow1
\tag{284.5}
$$
一致成立。未条件 Bernoulli 总和的方差不超过 $d/4$，端点条件只除以 $p_e\ge1/3$，故
$$
\mathsf Q\{|h-d\nu|>A_0\sqrt d\}\le\frac{3}{4A_0^2}.
$$
结合 (284.4)—(284.5)，将 $\mathbb E_{\mathsf Q}|u-1|$ 分为窗内、窗外，先沿原序列取极限，再令 $A_0\to\infty$，得
$$
\|\mathsf R-\mathsf Q\|_{\mathrm{TV}}
=\frac12\mathbb E_{\mathsf Q}|u-1|\longrightarrow0.
\tag{284.6}
$$
比较律始终保留变化的 $\nu$ 和全部 $d$ 位；不使用完整路径与公平独立位的接近性。

先在未加端点条件的 Bernoulli 律下证明短坐标联合极限。令 $\eta_j=(-1)^{\varepsilon_j}$、$\mathscr F_j=\sigma(\xi_0,\ldots,\xi_{j-1})$，则
$$
\eta_j=\varrho\eta_{j-1}+\zeta_j,\qquad \eta_0=1,
$$
$$
\mathbb E(\zeta_j\mid\mathscr F_{j-1})=0,\qquad
\mathbb E(\zeta_j^2\mid\mathscr F_{j-1})=1-\varrho^2,\qquad
|\zeta_j|\le2.
$$
固定实数 $a_o,a_e$，令 $a_j$ 按 $j$ 的奇偶取这两个值。精确展开为
$$
\sum_{j=1}^k a_j\eta_j
=\sum_{j=1}^k a_j\varrho^j+\sum_{l=1}^k c_l^{(a)}\zeta_l,\qquad
c_l^{(a)}=\sum_{j=l}^k a_j\varrho^{j-l}.
$$
$c_l^{(a)}$ 是确定数，均匀有界，且 $c_l^{(a)}-a_l=O(\varrho)$。因 $\varrho\to0$，
$$
\frac{1-\varrho^2}{k}\sum_{l=1}^k(c_l^{(a)})^2
\longrightarrow\frac{a_o^2+a_e^2}{2}.
\tag{284.7}
$$
Taylor 余项由 $|\zeta_l|\le2$ 给出：
$$
\mathbb E\!\left(e^{ic_l^{(a)}\zeta_l/\sqrt k}\mid\mathscr F_{l-1}\right)
=b_l+e_l,\qquad
b_l=1-\frac{(c_l^{(a)})^2(1-\varrho^2)}{2k},\qquad
|e_l|\le C_a k^{-3/2}.
$$
最终 $0\le b_l\le1$。令
$$
\Phi_l=\mathbb E\exp\!\left(\frac i{\sqrt k}
\sum_{r=1}^l c_r^{(a)}\zeta_r\right).
$$
从最后一个增量向前逐项条件积分，$\Phi_l=b_l\Phi_{l-1}+r_l$，$|r_l|\le C_a k^{-3/2}$；故
$$
\left|\Phi_k-\prod_{l=1}^k b_l\right|\le C_a k^{-1/2}.
$$
确定乘积由 (284.7) 和 $\sum_l(1-b_l)^2=O_a(k^{-1})$ 趋于 $\exp(-(a_o^2+a_e^2)/4)$。确定起始项绝对值不超过 $\max(|a_o|,|a_e|)\varrho/(1-\varrho)$，除以 $\sqrt k$ 后趋零。Cramér—Wold 给出两类状态和的联合正态极限。

端点比较可对整个内部历史一次完成。令 $\sigma=(-1)^M$，则截至 $\eta_k$ 的全部历史在条件 $\eta_d=\sigma$ 下，相对未条件历史的精确密度为
$$
\frac{\mathbb P(\eta_d=\sigma\mid\mathscr F_k)}
{\mathbb P(\eta_d=\sigma)}
=\frac{1+\sigma\eta_k\varrho}{1+\sigma\varrho^d}
=1+O(\varrho),
\tag{284.8}
$$
误差在整个历史空间上一致。这一步只对内部历史的推前积分最后一位 $\xi_k$；在完整向量及长坐标中仍保留该位。令 $n_o=\lceil k/2\rceil$、$n_e=\lfloor k/2\rfloor$，利用
$$
O=\frac{n_o-\sum_{j\text{ 奇}}\eta_j}{2},\qquad
E=\frac{n_e-\sum_{j\text{ 偶}}\eta_j}{2},
$$
先由 (284.8) 转到 $\mathsf Q$，再由 (284.6) 转到实际 $\mathsf R$，得
$$
\left(\frac{O-n_o/2}{\sqrt k},\frac{E-n_e/2}{\sqrt k}\right)
\Rightarrow\mathcal N(0,\operatorname{diag}(1/8,1/8)).
\tag{284.9}
$$

现将长坐标接入同一实际联合律。令
$$
N_o=n_o,\quad N_e=n_e+1,\quad \alpha=\frac{N_o}{d},\quad
h_o=\sum_{i\text{ 奇}}\xi_i,\quad h_c=h_o-\alpha h,\quad
S_\xi=\frac{M-h}{2}.
$$
给定完整 $\xi$ 且 $L=M$，整个 $T$ 向量在 $\sum T_i=S_\xi$ 的各点上质量相同。独立于 $\xi\sim\mathsf R$ 取
$P\sim\operatorname{Dirichlet}(1,\ldots,1)$，再条件于 $(\xi,P)$ 做 $S_\xi$ 次多项抽样生成 $T$。对任意非负整数 $t_i$ 且 $\sum t_i=S_\xi$，以 $p_k=1-\sum_{i<k}p_i$ 写单纯形积分：
$$
(d-1)!\frac{S_\xi!}{\prod_i t_i!}
\int_{\substack{p_0,\ldots,p_{k-1}\ge0\\\sum_{i<k}p_i\le1}}
\prod_{i=0}^k p_i^{t_i}\,dp_0\cdots dp_{k-1}
=\frac{S_\xi!(d-1)!}{(S_\xi+d-1)!}.
\tag{284.10}
$$
积分值 $\prod_i t_i!/(S_\xi+d-1)!$ 由逐次 Beta 积分得到，故每个组成向量的质量正好等于均匀组成质量。再令 $r_i=2T_i+\xi_i$，便实现完整实际 $L=M$ 条件律，未引入新的来源采样。

置 $B_o=\sum_{i\text{ 奇}}P_i$、$K_o=\sum_{i\text{ 奇}}T_i$。在这个共同实现中，
$$
B_o\sim\operatorname{Beta}(N_o,N_e),\qquad
K_o\mid(\xi,B_o)\sim\operatorname{Bin}(S_\xi,B_o),\qquad
H=2K_o+h_o,
$$
并且 $B_o$ 与整个 $\xi$ 独立。特别地，实际条件均值为
$$
\mathbb E(H\mid\xi,L=M)=\alpha M+h_c.
\tag{284.11}
$$
这不是条件后的 $T,\xi$ 独立性断言。

实际均匀弱组成可交换，所以 $\mathsf R$ 下的全部 $\xi_i$ 也可交换。写
$$
h_c=\sum_i b_i\xi_i,\qquad b_i=\mathbf1_{\{i\text{ 奇}\}}-\alpha,
\qquad
\sum_i b_i=0,\qquad \sum_i b_i^2=\frac{N_oN_e}{d}.
$$
令 $v_\xi=\operatorname{Var}_{\mathsf R}\xi_0$、
$c_\xi=\operatorname{Cov}_{\mathsf R}(\xi_0,\xi_1)$。交换性给
$$
\mathbb E_{\mathsf R}h_c=0,\qquad
\operatorname{Var}_{\mathsf R}h_c
=(v_\xi-c_\xi)\frac{N_oN_e}{d}\le\frac d8,
\tag{284.12}
$$
因为 $v_\xi-c_\xi=\tfrac12\mathbb E_{\mathsf R}(\xi_0-\xi_1)^2\le1/2$、
$N_oN_e\le d^2/4$。整个推导保留实际条件相关。

为写全 Beta 极限，取独立单位指数变量 $e_0,\ldots,e_k$，令 $P_i=e_i/\sum e_i$。总和 $u=\sum e_i$ 与单纯形坐标的换元 Jacobian 为 $u^{d-1}$，联合密度为 $u^{d-1}e^{-u}$；积分 $u$ 得常数 $(d-1)!$，正是上述 Dirichlet 密度。令 $G_o=\sum_{i\text{ 奇}}e_i$、$G_e=\sum_{i\text{ 偶}}e_i$，则 $B_o=G_o/(G_o+G_e)$，两个和独立。对单位指数律直接应用有限二阶矩的普通 iid 中心极限定理：
$$
U_o=\frac{G_o-N_o}{\sqrt{N_o}}\Rightarrow\mathcal N(0,1),\qquad
U_e=\frac{G_e-N_e}{\sqrt{N_e}}\Rightarrow\mathcal N(0,1),
$$
两者联合极限独立。精确比值式为
$$
\sqrt d(B_o-\alpha)
=\frac{(1-\alpha)\sqrt{N_o/d}\,U_o
-\alpha\sqrt{N_e/d}\,U_e}{(G_o+G_e)/d}.
$$
分母在概率中趋于一，两个分子系数趋于 $1/(2\sqrt2)$，因此
$$
\sqrt d(B_o-\alpha)\Rightarrow\mathcal N(0,1/4),\qquad
\mathbb E[d(B_o-\alpha)^2]=\frac{N_oN_e}{d(d+1)}\le\frac14.
\tag{284.13}
$$
后一等式直接来自正形状参数 Beta 密度的二阶积分。

同一实现上的精确分解是
$$
\frac{\delta_g(H-\alpha M)}{\sqrt k}
=\frac{\delta_g(M-h)}{\sqrt{kd}}\sqrt d(B_o-\alpha)
+\frac{\delta_g h_c}{\sqrt k}
+\frac{2\delta_g}{\sqrt k}(K_o-S_\xi B_o).
\tag{284.14}
$$
由 $\delta_gM=dt_g$ 和 $0\le h\le d$，首项系数与一的差在全部向量上一致为 $O(\delta_g+k^{-1})$；配合 (284.13)，用一替换该系数的误差在 $L^2$ 趋零。(284.12) 给第二项二阶矩至多 $\delta_g^2d/(8k)\to0$。第三项由条件二项方差得
$$
\mathbb E\left[\left(\frac{2\delta_g}{\sqrt k}
(K_o-S_\xi B_o)\right)^2\right]
=\frac{4\delta_g^2}{k}\mathbb E[S_\xi B_o(1-B_o)]
\le\frac{\delta_g^2M}{2k}=O(\delta_g)\to0.
$$
$B_o$ 与完整 $\xi$ 独立，故 (284.9)、(284.13)—(284.14) 在同一来源实现中联合给
$$
X_0=\left(\frac{O-n_o/2}{\sqrt k},\frac{E-n_e/2}{\sqrt k},
\frac{\delta_g(H-\alpha M)}{\sqrt k}\right)
\Rightarrow\mathcal N(0,D_0),\qquad
D_0=\operatorname{diag}(1/8,1/8,1/4).
\tag{284.15}
$$

下一步用精确有限矩匹配实际中心和完整协方差。复用 §283 的
$$
c_j=\mathbb E[\eta_j\mid L=M],\qquad
\mathbb E[\eta_i\eta_j\mid L=M]=c_{|i-j|}\quad(i\ne j),
$$
$$
|c_j|\le\theta^j+\theta^{d-j},\qquad
\theta=\frac d{2M}\to0,\qquad
\sum_{j=1}^{d-1}|c_j|\le\frac{2\theta}{1-\theta}=O(\theta).
\tag{284.16}
$$
因而精确短坐标均值为
$$
\mathbb EO=\frac{n_o-\sum_{j\text{ 奇}}c_j}{2},\qquad
\mathbb EE=\frac{n_e-\sum_{j\text{ 偶}}c_j}{2}.
$$
例如奇位置集合 $\mathcal I_o$ 给
$$
4\operatorname{Var}O
=n_o+\sum_{\substack{i,j\in\mathcal I_o\\i\ne j}}c_{|i-j|}
-\left(\sum_{i\in\mathcal I_o}c_i\right)^2.
$$
每个距离至多出现 $2k$ 次，两个均值和均为 $O(\theta)$，故分别有
$$
\operatorname{Var}O=\frac{n_o}{4}+O(k\theta+\theta^2),\qquad
\operatorname{Var}E=\frac{n_e}{4}+O(k\theta+\theta^2),
$$
$$
4\operatorname{Cov}(O,E)
=\sum_{i\in\mathcal I_o,j\in\mathcal I_e}c_{|i-j|}
-\left(\sum_{i\in\mathcal I_o}c_i\right)
 \left(\sum_{j\in\mathcal I_e}c_j\right)
=O(k\theta+\theta^2).
\tag{284.17}
$$
所有期望与协方差都在实际条件律下取值。再直接复用 §283 的
$$
\mathbb EH=\alpha M,\qquad
\operatorname{Var}H=\frac{MN_oN_e(M+d)}{d^2(d+1)},\qquad
\frac{\delta_g^2\operatorname{Var}H}{k}
=\frac{t_gN_oN_e}{k(d+1)}\longrightarrow\frac14.
\tag{284.18}
$$
$O,E$ 是完整 $\xi$ 的函数，故由 (284.11)
$$
\operatorname{Cov}(O,H)=\operatorname{Cov}(O,h_c),\qquad
\operatorname{Cov}(E,H)=\operatorname{Cov}(E,h_c).
$$
Cauchy—Schwarz、(284.12)、(284.17) 分别给
$$
|\operatorname{Cov}(O,H)|\le
\sqrt{\operatorname{Var}O\,\operatorname{Var}h_c}=O(k),\qquad
|\operatorname{Cov}(E,H)|\le
\sqrt{\operatorname{Var}E\,\operatorname{Var}h_c}=O(k).
\tag{284.19}
$$
令 $X=(O,E,H)$、$\mu_X=\mathbb EX$、$R_g=\operatorname{diag}(1,1,\delta_g)$，便得
$$
C_g:=\frac1kR_g\operatorname{Cov}(X)R_g\longrightarrow D_0,\qquad
\frac1{\sqrt k}R_g(X-\mu_X)\Rightarrow\mathcal N(0,D_0).
\tag{284.20}
$$
第二式使用 (284.15) 以及短中心与 $n_o/2,n_e/2$ 的差为 $O(\theta)$、长中心恰为 $\alpha M$。第一式由 (284.17)—(284.19) 逐项取得，两个长短项乘 $\delta_g/k$ 后趋零；它不从弱收敛推断矩收敛，也不在有限参数下删去交叉协方差。

现直接消费 §283 的实际坐标与格。令 $\kappa=k\bmod2$、
$J=(H-O-E-\kappa M)/2$、$W=(O,E,J)$，则 $W$ 为整数向量，且其差分矩阵为
$$
T=\begin{pmatrix}1&0&0\\0&1&0\\-1/2&-1/2&1/2\end{pmatrix}.
$$
复用 (283.12)—(283.13) 的两个精确来源映射：
$$
Z=\left(O-E,\frac{M-2H-(-1)^kq}{2},
\lfloor k/2\rfloor-O-E\right)\quad(a=k,b=M),
$$
$$
Z=\left(E-O+pq,\lfloor k/2\rfloor-O-E+pq,
\frac{M-2H-p}{2}\right)\quad(b=k,a=M).
\tag{284.21}
$$
取实际支持点 $z_0$，复用 (283.17) 的
$$
B=\begin{pmatrix}2&0&1\\0&2&1\\0&0&1\end{pmatrix},\qquad
A_1=\begin{pmatrix}1&0&0\\0&0&-1\\-1&-1&0\end{pmatrix},\qquad
A_2=\begin{pmatrix}0&1&1\\0&0&1\\-1&-1&-2\end{pmatrix}.
$$
$A_1,A_2$ 为整数幺模矩阵。令
$$
Y=B^{-1}(Z-z_0),\qquad m=\mathbb EY,\qquad
V=\operatorname{Cov}Y=B^{-1}\Sigma_{ab}B^{-T}.
$$
按方向取 $\mathcal A=A_1$ 或 $A_2$，$K=\mathcal AT$；具体为
$$
K_1=\begin{pmatrix}1&0&0\\1/2&1/2&-1/2\\-1&-1&0\end{pmatrix},
\qquad
K_2=\begin{pmatrix}-1/2&1/2&1/2\\-1/2&-1/2&1/2\\0&0&-1\end{pmatrix},
\qquad |\det K_i|=\frac12.
$$
这些是差分关系，所有实际常量由中心化消去；精确地
$$
Y-m=K(X-\mu_X),\qquad
V=kK R_g^{-1}C_gR_g^{-1}K^T.
\tag{284.22}
$$
由 (284.20)，最终 $\|C_g-D_0\|_{\mathrm{op}}\le1/16$；此时可取 $c=1/16$、$C=5/16$，使 $cI\le C_g\le CI$，所以
$$
ckK R_g^{-2}K^T\le V\le CkK R_g^{-2}K^T,\qquad V\ge c'kI.
\tag{284.23}
$$
后一界用 $R_g^{-2}\ge I$ 和两种固定可逆 $K$ 的共同最小奇异值取得。因此 $V$ 与 $\Sigma_{ab}$ 最终正定。这些尺度界在实际变换轴中成立，不把混合的 $Y$ 轴误当作对角轴。又 $\det D_0=1/256$，故
$$
\sqrt{\det V}=\frac{k^{3/2}}{2\delta_g}\sqrt{\det C_g}
\sim\frac{k^{3/2}}{32\delta_g},\qquad
\sqrt{\det\Sigma_{ab}}=4\sqrt{\det V}
\sim\frac{k^{3/2}}{8\delta_g}.
\tag{284.24}
$$

所有环面积分继续采用 §283 的未归一化 Lebesgue 测度。定义
$$
\Psi(\zeta)=\mathbb E e^{i\zeta\cdot(Y-m)}.
$$
固定频域半径 $R\ge1$，对实提升 $\zeta\in\mathbb R^3$ 令
$$
\eta=K^T\zeta,\qquad
v=\left(\sqrt k\,\eta_1,\sqrt k\,\eta_2,
\frac{\sqrt k}{\delta_g}\eta_3\right),\qquad
\mathcal Q_R=\{\zeta:v\in[-R,R]^3\}.
$$
复用 §283 的 $q_H(\tau,x,y)=(x+\tau,y+\tau,2\tau)$ 与 $\Omega_R$。精确地
$$
T^Tq_H(\tau,x,y)=(x,y,\tau).
$$
因此 $\mathcal Q_R$ 的环面像就是 $\Omega_R$：$U_R$ 的零中心盒在 $q_H$ 下给出该像，另一个 H 中心盒相差核元，给出同一像。固定 $R$ 时，由两种 $K^{-T}$ 的共同范数界，最终 $\mathcal Q_R\subset(-\pi,\pi)^3$，所以局部代表唯一。换元 Jacobian 为
$$
d\zeta=\frac{2\delta_g}{k^{3/2}}\,dv,\qquad
\sqrt{\det V}\,d\zeta=\sqrt{\det C_g}\,dv.
\tag{284.25}
$$
并且
$$
\zeta\cdot(Y-m)=v\cdot\frac{R_g(X-\mu_X)}{\sqrt k},\qquad
\zeta^TV\zeta=v^TC_gv.
$$
(284.20) 给每个固定 $v$ 上的特征函数极限 $\exp(-v^TD_0v/2)$；高斯项由 $C_g\to D_0$ 有同一极限。两项的模均不超过一，固定盒上有界支配收敛与 (284.25) 因而给
$$
\sqrt{\det V}\int_{\Omega_R}
|\Psi(\zeta)-e^{-\zeta^TV\zeta/2}|\,d\zeta\longrightarrow0.
\tag{284.26}
$$

在同一中心代表下定义实际格高斯和
$$
G(\zeta)=\sum_{\ell\in\mathbb Z^3}
\phi_V(\ell-m)e^{i\zeta\cdot(\ell-m)}.
$$
对每个最终正定的有限 $V$，精确三维求和公式为
$$
G(\zeta)=\sum_{h\in\mathbb Z^3}e^{2\pi i h\cdot m}
\exp\!\left[-\frac12(\zeta+2\pi h)^TV(\zeta+2\pi h)\right].
\tag{284.27}
$$
为验证相位与归一化，令 $F_0=[-\pi,\pi)^3$，将右侧乘 $e^{i\zeta\cdot m}$，记所得连续周期函数为 $\mathcal H(\zeta)$。正定高斯及其整数平移级数迅速衰减，级数绝对且局部一致收敛，可逐项取整数 Fourier 系数。对任意 $\ell\in\mathbb Z^3$，换元 $u=\zeta+2\pi h$ 后有
$$
\begin{aligned}
\widehat{\mathcal H}(\ell)
&=(2\pi)^{-3}\sum_h\int_{F_0}
e^{i\zeta\cdot m+2\pi ih\cdot m-i\zeta\cdot\ell}
e^{-(\zeta+2\pi h)^TV(\zeta+2\pi h)/2}\,d\zeta\\
&=(2\pi)^{-3}\int_{\mathbb R^3}
e^{-iu\cdot(\ell-m)}e^{-u^TVu/2}\,du\\
&=\phi_V(\ell-m).
\end{aligned}
$$
整数性使 $e^{2\pi ih\cdot\ell}=1$；全部平移基本域铺满 $\mathbb R^3$。最后一个三维高斯积分由正交对角化正定 $V$，再对三个正二次系数的高斯 Fourier 积分作 Fubini 得到。另一方面，$e^{i\zeta\cdot m}G(\zeta)$ 的绝对收敛 Fourier 级数具有同样的系数；连续周期函数的 Fourier 唯一性证明 (284.27)。式中相位是正号 $e^{2\pi ih\cdot m}$。角度加 $2\pi a$ 时，$G$ 与 $\Psi$ 同乘 $e^{-2\pi ia\cdot m}$，故 $|\Psi-G|$ 是环面函数。

用 (284.27) 的非零平移项和基本域铺砌，
$$
\begin{aligned}
\sqrt{\det V}\int_{F_0}|G(\zeta)-e^{-\zeta^TV\zeta/2}|\,d\zeta
&\le\sqrt{\det V}\int_{\mathbb R^3\setminus F_0}
e^{-\zeta^TV\zeta/2}\,d\zeta\\
&\longrightarrow0.
\end{aligned}
\tag{284.28}
$$
确实，换元 $u=V^{1/2}\zeta$ 完全消去行列式；$\zeta\notin F_0$ 给 $\|\zeta\|\ge\pi$，而 (284.23) 给 $\|u\|\ge\pi\sqrt{c'k}$。右侧于是由标准三维高斯的该径向尾控制，不引入依赖未受限 $M$ 的前因子。

还要支付 $\Omega_R$ 外的格高斯尾。若环面点不在 $\Omega_R$，它的任何实提升都不在 $\mathcal Q_R$；否则该提升的投影就在 $\Omega_R$。将基本域外部的所有提升合并，(284.27)、三角不等式与 (284.25) 给
$$
\begin{aligned}
\sqrt{\det V}\int_{\mathbb T^3\setminus\Omega_R}|G(\zeta)|\,d\zeta
&\le\sqrt{\det V}\int_{\mathbb R^3\setminus\mathcal Q_R}
e^{-\zeta^TV\zeta/2}\,d\zeta\\
&=\sqrt{\det C_g}\int_{\mathbb R^3\setminus[-R,R]^3}
e^{-v^TC_gv/2}\,dv.
\end{aligned}
\tag{284.29}
$$
由 $cI\le C_g\le CI$，右侧不超过固定常数乘
$\int_{\mathbb R^3\setminus[-R,R]^3}e^{-c\|v\|^2/2}\,dv$；其上极限随 $R\to\infty$ 趋零。这里保留长短轴尺度，行列式与 Jacobian 相消，没有 $Me^{-ck}$ 或需要 $k\gg\log M$ 的余项。

直接复用定理 283.1、(283.19)—(283.20) 的真实特征函数远频消费者：
$$
\sqrt{\det V}\int_{\mathbb T^3\setminus\Omega_R}|\Psi(\zeta)|\,d\zeta
\le C_{\mathrm{tail}}(1+R)^{-2}.
\tag{284.30}
$$
在 $\Omega_R$ 上以 (284.26)、(284.28) 控制 $|\Psi-G|$，在其补集用 (284.29)—(284.30)。先沿固定的任意原序列取上极限，再令 $R\to\infty$，得到完整充分接口
$$
\sqrt{\det V}\int_{\mathbb T^3}|\Psi-G|\,d\zeta\longrightarrow0.
\tag{284.31}
$$
同一中心相位下，对每个整数 $y\in\mathbb Z^3$，
$$
\mathbb P(Y=y)-\phi_V(y-m)
=(2\pi)^{-3}\int_{F_0}
e^{-i\zeta\cdot(y-m)}(\Psi(\zeta)-G(\zeta))\,d\zeta.
$$
原律与高斯格和均绝对可和，整数字符的正交性使反演成立；取绝对值便有全整数格统一误差界。

§283 的最大实际差分格及母卷整数判据给 $\Lambda_{ab}=z_0+B\mathbb Z^3$，因此 $z\in\Lambda_{ab}$ 与 $y=B^{-1}(z-z_0)\in\mathbb Z^3$ 双射。精确换元为
$$
y-m=B^{-1}(z-\mu_{ab}),\qquad
\phi_V(y-m)=4\phi_{\Sigma_{ab}}(z-\mu_{ab}),\qquad
\sqrt{\det\Sigma_{ab}}=4\sqrt{\det V}.
$$
(284.31) 于是证明 (284.1)，包括完整 Euler 支撑外的零质量点。两个方向只选择有限集合 $\{K_1,K_2\}$ 内的矩阵，前述常数及极限证明共用；即使方向无限次切换，结论仍成立。全证明仅使用 $k\to\infty$、$\delta_g\to0$。$\square$

来源与中间工具的适用范围如下。实际有序树、均匀纤维与 Catalan 消去采用本卷定义 1.1、2.1、定理 2.2；同源正规形、八边和 Euler 判据采用[母卷 §§357、359、360 的钉定正文](https://github.com/the-omega-institute/trureturing/blob/f4d6b577d321ab7a06af770830b6945bc6173261/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)；几何条件化、两方向映射、格及精确有限矩、远频消费者采用[本卷 §283 的钉定正文](https://github.com/the-omega-institute/trureturing/blob/f4d6b577d321ab7a06af770830b6945bc6173261/docs/develop/theory/FIB_ATOM_STATISTICAL_LAWS.md)。新的同源推导是完整偏置奇偶密度的全速率比较、共同 Beta 实现及实际交叉矩桥与中央 Fourier 消费者的连接；坐标换元和既有尾界作为前置直接使用。

成熟中间工具可复用于钉版 mathlib $db584cd6d46c92f209a44c0f1c829460d327499d$：[Stirling](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/Stirling.lean) 的正整数全局阶乘界与阶乘渐近等价供给 (284.3)；[普通 iid 中心极限定理](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/CentralLimitTheorem.lean) 的独立同分布、有限二阶矩假设用于单位指数和；[Beta 密度及归一化](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/Distributions/Beta.lean) 使用正形状参数；[高斯 Fourier 积分](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean) 使用正二次实部；[Poisson 求和](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Fourier/PoissonSummation.lean) 的可和衰减接口与 (284.27) 的高斯 Fourier 系数验证相容。共同 Dirichlet—多项式表示由 (284.10) 的单纯形积分直接验证，不以经典文献的未取得正文作证明前提。这些中间工具的声明域各自保留；它们不单独给出本条件三维族的完整局部极限。

本定理的概率量词域与原仿射严格预算不同。在素数 $r\ge7$、$V_{\!F}=F_r$、非空连续 $I\subseteq[\lceil V_{\!F}/10\rceil,\lfloor V_{\!F}/5\rfloor]$、$N=1+V_{\!F}g$、$A>5040$、固定 $C_0>1$、$A\le N\le C_0A$、$s=\log A\,\log\log A$ 及原 Möbius 增量 $b_s$ 的同整数问题中，完整成本不等式
$$
C^*+H^*<
\left(\frac{\log\log N^*}{\log\log A}\right)^s
$$
仍未证明。(284.1) 不支付该完整成本，不构造实际 Robin 反例，也不推出 RH 或全 Robin 命题；母卷 §365 的既有实际最小公倍数族归约仍只适用于其原量词域。

## 追加锚（本行以下为增补区）


## 285. 总长度条件下完整间隔奇偶核的显式有限误差

**定义 285.1（实际树、完整间隔与共同记录）。** 沿用定义 1.1、2.1 的自由有序非空满二叉树代数 $\mathcal T$，叶为 $\alpha,\beta$；左右次序与全部二叉括号化分别保留。对非负整数组成 $(a,b)$、$a+b\ge1$，$U(a,b)$ 是组成纤维 $\mathcal F(a,b)$ 上的均匀律。原替换及叶积关系为

$$
\rho(\alpha)=\beta,\qquad
\rho(\beta)=\langle\beta,\alpha\rangle,\qquad
\rho(\langle s,t\rangle)=\langle\rho(s),\rho(t)\rangle,
\qquad A^2=1,\quad B^2=-1,\quad AB+BA=1.
$$

$E(t)$ 按原叶序相乘，三个窗口始终属于同一实际树：

$$
W_3(t)=(E(t),E(\rho t),E(\rho^2t))=L(u,v,w)R_{pq},
\qquad Z(t)=(u,v,w),\quad p=a\bmod2,\quad q=b\bmod2.
$$

这里直接采用[母卷](FIBONACCI_ATOMIC_RELATION_GENERATION.md)定理 359.3 的唯一正规形，置 $S=BA$，则

$$
L(u,v,w)=\bigl((-1)^vS^{2u},(-1)^wS^{2v},(-1)^uS^{2w}\bigr),
\qquad
R_{00}=(1,1,1),\quad R_{10}=(A,B,S),\quad
R_{01}=(B,S,A+B),\quad R_{11}=R_{10}R_{01}.
$$

令 $k=\min(a,b)$、$M=\max(a,b)$、$d=k+1$、$n=k+M$。当 $a\le b$ 时以 $\alpha$ 分隔，叶词唯一写成
$\beta^{r_0}\alpha\beta^{r_1}\cdots\alpha\beta^{r_k}$；当 $b<a$ 时以 $\beta$ 分隔，唯一写成
$\alpha^{r_0}\beta\alpha^{r_1}\cdots\beta\alpha^{r_k}$。全部 $d$ 个间隔满足

$$
r_i\in\mathbb Z_{\ge0}\quad(0\le i<d),\qquad \sum_{i=0}^{d-1}r_i=M.
$$

每个叶词都有同样的 $\operatorname{Cat}_{n-1}=n^{-1}\binom{2n-2}{n-1}$ 种有序二叉括号化。采用定理 2.2 及 §§283–284 的计数回接，$U(a,b)$ 在 $r$ 上诱导总和为 $M$ 的均匀弱组成律，而给定 $r$ 后仍均匀保留全部括号。定义

$$
\xi_i=r_i\bmod2,\qquad h=\sum_{i=0}^{d-1}\xi_i,\qquad
\varepsilon_0=0,\qquad
\varepsilon_j=\left(\sum_{i<j}r_i\right)\bmod2\quad(1\le j\le d).
$$

实际端点为 $\varepsilon_d=M\bmod2$；$\xi_i=\varepsilon_i\mathbin{\oplus}\varepsilon_{i+1}$，其中 $\oplus$ 表示模二加法。因此全部 $d$ 位 $\xi$ 与包含端点的全部 $d+1$ 位 $\varepsilon$ 互相唯一决定。记实际完整奇偶律为 $\mathsf R_{d,M}$。在同一个 $r$ 上定义

$$
H=\sum_{\substack{0\le i<d\\i\text{ 奇}}}r_i,\qquad
O=\sum_{\substack{1\le j\le k\\j\text{ 奇}}}\varepsilon_j,\qquad
E=\sum_{\substack{1\le j\le k\\j\text{ 偶}}}\varepsilon_j.
$$

此处标量 $E$ 与叶积函数 $E(t)$ 由参数区分。直接使用 (283.12)–(283.13) 的同源坐标：

$$
\begin{aligned}
Z&=\left(O-E,\frac{M-2H-(-1)^kq}{2},\lfloor k/2\rfloor-O-E\right)
&& (a=k,b=M),\\
Z&=\left(E-O+pq,\lfloor k/2\rfloor-O-E+pq,\frac{M-2H-p}{2}\right)
&& (b=k,a=M).
\end{aligned}
\tag{285.1}
$$

两式的证明是母卷八边增量沿实际叶词求和，不需要 $k\ge64$，也不需要协方差可逆。相应实际支撑完整保留母卷定理 360.2：令

$$
X_e=\frac{a-p-2w+2u}{4},\qquad
Y_e=\frac{b-q-2u+2v}{4},
$$

则 $X_e,Y_e$ 必须为整数，全部八个出发状态边重数

$$
\begin{aligned}
x_{00}&=X_e+w-u+p,&x_{10}&=X_e+w,&x_{01}&=X_e,&x_{11}&=X_e-u,\\
y_{00}&=Y_e+u+q(1-p),&y_{01}&=Y_e,&y_{10}&=Y_e-v+pq,&y_{11}&=Y_e+u-v
\end{aligned}
\tag{285.2}
$$

必须非负。$x_{pq}$ 是 $pq\xrightarrow{\alpha}(1-p)q$ 的次数，$y_{pq}$ 是 $pq\xrightarrow{\beta}p(1-q)$ 的次数；所有正重数边的端点连同起点 $00$，忽略方向后必须构成弱连通支撑。叶词从 $00$ 到 $(p,q)$ 的实际路径承担全部条件，不能以仅有流量方程的松弛替代。

**定义 285.2（偏置参考合同与实际条件核）。** 对整数 $d\ge1,M\ge1$，置

$$
\tau=\frac{M}{M+d},\qquad
\nu=\frac{\tau}{1+\tau}=\frac{M}{2M+d},\qquad
\eta_0=1-2\nu=\frac{d}{2M+d},
$$

并令 $\mathsf Q_{d,M}$ 为全部 $d$ 个独立 $\operatorname{Bernoulli}(\nu)$ 位条件于
$h\equiv M\pmod2$ 的律。独立性属于未条件参考采样；条件后的全部位不称为独立，也不称为原 $U(a,b)$ 的奇偶律。条件事件概率和单向量质量为

$$
p_e=\frac{1+(-1)^M\eta_0^d}{2}>0,\qquad
\mathsf Q_{d,M}(\xi)=
\frac{\nu^h(1-\nu)^{d-h}}{p_e}
\mathbf1_{\{h\equiv M\pmod2\}}.
\tag{285.3}
$$

实际弱组成计数给出

$$
\mathsf R_{d,M}(\xi)=
\frac{\displaystyle\binom{(M-h)/2+d-1}{d-1}}
{\displaystyle\binom{M+d-1}{d-1}}
\mathbf1_{\{h\equiv M\pmod2,\ h\le M\}};
\tag{285.4}
$$

指示条件不成立时质量为零，不对非整数或负参数解释组合数。对实际合法的完整 $\xi$，令 $s_\xi=(M-h)/2$。给定 $\xi$ 后，$r=2T+\xi$ 的实际条件核为

$$
\mathbb P(T=t\mid\xi)=
\frac{\mathbf1_{\{t_i\in\mathbb Z_{\ge0},\ \sum_i t_i=s_\xi\}}}
{\displaystyle\binom{s_\xi+d-1}{d-1}}.
\tag{285.5}
$$

这是 (284.2)、(284.10) 已用的奇偶分解与均匀弱组成计数。$M\ge d$ 时，每个终端合法的 $\xi$ 都有 $s_\xi\ge0$，因而可以定义参考树律 $\widetilde U(a,b)$：先抽 $\xi\sim\mathsf Q_{d,M}$，再使用同一个实际核 (285.5) 抽 $T$，置 $r=2T+\xi$，按定义 285.1 的指定方向形成原叶词，最后均匀选择全部 $\operatorname{Cat}_{n-1}$ 种原有序括号。每一步均生成 $\mathcal F(a,b)$ 中的实际树。该律仅重加权实际奇偶纤维，属于额外参考合同；它的单树质量为

$$
\widetilde U(a,b)(t)=
\frac{\mathsf Q_{d,M}(\xi(t))}
{\operatorname{Cat}_{n-1}\displaystyle\binom{s_{\xi(t)}+d-1}{d-1}}.
\tag{285.6}
$$

**命题 285.3（完整终端奇偶核的有限 TV 界及同源消费者）。** 总变差采用有限概率律的约定
$\|P-Q\|_{\mathrm{TV}}=\frac12\sum_x|P(x)-Q(x)|$。对全部整数 $d\ge2,M\ge3d$，有

$$
\|\mathsf R_{d,M}-\mathsf Q_{d,M}\|_{\mathrm{TV}}
\le \epsilon_{d,M}:=
\min\left\{1,\ 5\left(\frac{\sqrt d}{M}+\frac{d(d-1)}{M^2}\right)\right\}.
\tag{285.7}
$$

$d=1,M\ge1$ 时两律相等，取 $\epsilon_{1,M}=0$。在这些范围内，完整 $\varepsilon$ 记录的两律具有相同的 TV 距离。对任一对应组成 $(a,b)$，参考树律 (285.6) 满足

$$
\|U(a,b)-\widetilde U(a,b)\|_{\mathrm{TV}}
=\|\mathsf R_{d,M}-\mathsf Q_{d,M}\|_{\mathrm{TV}}.
\tag{285.8}
$$

因此，对由同一实际树计算的完整联合记录
$(t,r,\xi,\varepsilon,H,O,E,Z,W_3(t))$ 的任意事件 $\mathcal A$，有两方向概率界

$$
\max\{0,\mathbb P_{\widetilde U}(\mathcal A)-\epsilon_{d,M}\}
\le\mathbb P_U(\mathcal A)
\le\min\{1,\mathbb P_{\widetilde U}(\mathcal A)+\epsilon_{d,M}\}.
\tag{285.9}
$$

此处只将已有纤维等距提升及 TV 通道收缩作为 (285.7) 的消费者；承重的新增估计为完整密度的有限参数上界 (285.7)。它是本仓推导，不作全球优先权或最优常数断言。

证明。先取 $d\ge2,M\ge3d$。此时所有终端合法向量都可实现，两律在同一完整奇偶集合上均严格为正。由 (285.3)，$\mathsf Q(\xi)$ 与 $\tau^h$ 成正比；由 (285.4) 的乘积展开，$\mathsf R(\xi)$ 与
$\prod_{j=1}^{d-1}(M-h+2j)$ 成正比。故对 $0\le x\le d$ 定义

$$
\ell(x)=\sum_{j=1}^{d-1}\log(M-x+2j)-x\log\tau,
\qquad m=d\nu=\frac{dM}{2M+d},
$$

则 $d\mathsf R/d\mathsf Q$ 与 $\exp(\ell(h))$ 成正比。全部对数参数为正，$0<m<d$。$m$ 只是未条件参考 Bernoulli 总和的均值，不将它认作 $\mathsf Q$ 下的条件均值。

两个精确恒等式为

$$
M-m=\frac{2M^2}{2M+d},\qquad
M-m+2d=\frac{2(M+d)^2}{2M+d}.
$$

令 $f(y)=(M-m+2y)^{-1}$，则 $f$ 正且递减，并且

$$
I_f:=\int_0^d f(y)\,dy
=\frac12\log\frac{M-m+2d}{M-m}
=-\log\tau.
$$

采用递减函数的积分比较：

$$
\int_1^d f(y)\,dy
\le\sum_{j=1}^{d-1}f(j)
\le\int_0^{d-1}f(y)\,dy
\le I_f.
$$

因此完整离散和的端点误差满足

$$
0\le\ell'(m)=I_f-\sum_{j=1}^{d-1}f(j)
\le\int_0^1f(y)\,dy
\le\frac1{M-d}=:A_0.
\tag{285.10}
$$

这里积分中心与偏置 $\nu$ 精确相消，保留的是全部 $d-1$ 项离散和的有限端点误差。全区间曲率则为

$$
\ell''(x)=-\sum_{j=1}^{d-1}\frac1{(M-x+2j)^2},
\qquad -B_0\le\ell''(x)\le0,
\qquad B_0=\frac{d-1}{(M-d)^2}\quad(0\le x\le d).
\tag{285.11}
$$

置 $\Delta=h-m$、$X_\ell=\ell(h)-\ell(m)$。Taylor 积分余项和凹函数的切线界分别给出

$$
|X_\ell|\le A_0|\Delta|+\frac{B_0}{2}\Delta^2,
\qquad
X_\ell\le\ell'(m)\Delta\le A_0d\le\frac12.
\tag{285.12}
$$

后一个估计同时覆盖 $\Delta<0$：这时 $\ell'(m)\Delta\le0$。上述余项覆盖全部合法向量，不丢弃尾部，也没有先作任何渐近极限。

在未条件的参考 Bernoulli 律下，$h$ 的均值为 $m$、方差为 $d\nu(1-\nu)\le d/4$。由 $\eta_0\le1/7$，

$$
p_e=\frac{1+(-1)^M\eta_0^d}{2}
\ge\frac{1-\eta_0^d}{2}\ge\frac13.
$$

将非负变量 $\Delta^2$ 的无条件期望除以条件事件概率，再用 Cauchy–Schwarz，得到

$$
\mathbb E_{\mathsf Q}\Delta^2\le\frac{3d}{4},\qquad
\mathbb E_{\mathsf Q}|\Delta|\le\frac{\sqrt{3d}}2.
\tag{285.13}
$$

这不是条件独立性或条件均值等式。于是

$$
\mathbb E_{\mathsf Q}|X_\ell|\le D_{d,M}:=
\frac{\sqrt{3d}}{2(M-d)}+
\frac{3d(d-1)}{8(M-d)^2}.
\tag{285.14}
$$

$M-d\ge2d$、$d\ge2$ 给第一项至多 $\sqrt{3/2}/4<3/8$，第二项至多 $3(d-1)/(32d)<3/32$，故 $D_{d,M}<1/2$。令 $V_\ell=\exp(X_\ell)$、$c=\mathbb E_{\mathsf Q}V_\ell$；有限 Jensen 不等式给出完整归一化常数的下界

$$
c\ge\exp(\mathbb E_{\mathsf Q}X_\ell)\ge\exp(-D_{d,M}).
$$

由 $X_\ell\le1/2$ 和均值定理，$|V_\ell-1|\le e^{1/2}|X_\ell|$。精确归一化密度为
$d\mathsf R/d\mathsf Q=V_\ell/c$，且
$|c-1|\le\mathbb E_{\mathsf Q}|V_\ell-1|$，所以

$$
\begin{aligned}
\|\mathsf R-\mathsf Q\|_{\mathrm{TV}}
&=\frac1{2c}\mathbb E_{\mathsf Q}|V_\ell-c|\\
&\le\frac1c\mathbb E_{\mathsf Q}|V_\ell-1|\\
&\le\exp(1/2+D_{d,M})D_{d,M}\le eD_{d,M}.
\end{aligned}
\tag{285.15}
$$

最后 $M-d\ge2M/3$ 给

$$
D_{d,M}\le\frac{3\sqrt3}{4}\frac{\sqrt d}{M}
+\frac{27}{32}\frac{d(d-1)}{M^2}.
$$

使用 $e<3$、$9\sqrt3/4<5$、$81/32<5$，再用概率律的 TV 至多一，便得到 (285.7)。离散端点控制、全域曲率、条件二阶矩与归一化下界共同给出此有限 $L^1$ 误差；弱收敛或单点中心极限不承担任何一步定量换权。

$d=1$ 时只有一个间隔 $r_0=M$，实际奇偶位确定为 $M\bmod2$；参考合同条件于同一奇偶后也集中在这个唯一位，故 TV 为零。固定 $\varepsilon_0=0$ 和 $\varepsilon_d=M\bmod2$ 后，$\xi\leftrightarrow\varepsilon$ 是定义 285.1 的双射，TV 因而保持。

对于完整实际树，(285.5) 和均匀 Catalan 括号给共同条件核 $K_\xi(t)$，其支撑恰为奇偶记录等于 $\xi$ 的树。因而

$$
U(t)=\mathsf R(\xi(t))K_{\xi(t)}(t),\qquad
\widetilde U(t)=\mathsf Q(\xi(t))K_{\xi(t)}(t),\qquad
\sum_{t:\xi(t)=\xi}K_\xi(t)=1.
$$

纤维内的质量差同号，按纤维求绝对值即得

$$
\frac12\sum_t|U(t)-\widetilde U(t)|
=\frac12\sum_\xi|\mathsf R(\xi)-\mathsf Q(\xi)|,
$$

证明 (285.8)。这是仓内 [FiberwiseEqualDistanceLift](../../../D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift.lean) 的 `fiberwise_equal_distance_lift` 所用非空有限纤维提升的实例，参考正质量纤维的非空性由 $M\ge d$ 保证。再将同一树送入完整联合记录，采用 [DataProcessing](../../../D5/S3/TotalVariation/DataProcessing.lean) 的 `total_variation_channel_le` 对有限随机通道的收缩，任一事件的绝对概率差不超过 (285.8)，从而得到 (285.9)。这些已有中间工具不另列新增命题。

有限消费者可以保留 $H$ 与全部奇偶路径的依赖。对 $k\ge1$，令

$$
n_o=\lceil k/2\rceil,\qquad n_e=\lfloor k/2\rfloor+1,
\qquad h_o=\sum_{i\text{ 奇}}\xi_i,
\qquad K_o=\sum_{i\text{ 奇}}T_i.
$$

$n_o,n_e\ge1$ 且 $n_o+n_e=d$。给定完整 $\xi$，将 (285.5) 的弱组成按奇、偶两组计数，直接复用 (284.10) 的 Dirichlet—多项式／Beta—二项分组核，得

$$
H=2K_o+h_o,\qquad
\mathbb P(K_o=j\mid\xi)=
\frac{\displaystyle\binom{j+n_o-1}{n_o-1}
\binom{s_\xi-j+n_e-1}{n_e-1}}
{\displaystyle\binom{s_\xi+d-1}{d-1}}
\quad(0\le j\le s_\xi).
\tag{285.16}
$$

$O,E$ 是同一个完整 $\xi$ 所确定的量。以 (285.16) 给定 $H$，再用 (285.1) 得 $Z(\xi,j)$；对任意 $\mathcal B\subseteq\mathbb Z^3$，参考概率的完整有限表达为

$$
\mathbb P_{\widetilde U}(Z\in\mathcal B)
=\sum_{\substack{\xi\in\{0,1\}^d\\h\equiv M\ (2)}}
\mathsf Q(\xi)
\sum_{j=0}^{s_\xi}
\frac{\displaystyle\binom{j+n_o-1}{n_o-1}
\binom{s_\xi-j+n_e-1}{n_e-1}}
{\displaystyle\binom{s_\xi+d-1}{d-1}}
\mathbf1_{\{Z(\xi,j)\in\mathcal B\}}.
\tag{285.17}
$$

对 $(\xi,\varepsilon,H,O,E,Z,W_3)$ 的联合事件，同样在指示函数中保留整份记录；若事件还依赖完整 $T$ 或括号，则使用 (285.5) 与全部 Catalan 括号求和。两律使用完全相同的条件核，没有把 $H,O,E$ 换成独立边缘。每次抽样都先生成原叶词和原树，再由原替换生成三个窗口，故 (285.2) 的八边非负整数与含 $00$ 的弱 Euler 支撑在两律中同时成立，支撑外均为零。$\square$

本命题的退化边界可在同一证明中的精确质量上直接代入。$d=2$ 时，奇 $M$ 的合法向量只有 $01,10$，两律均各赋质量 $1/2$，故 TV 为零。偶 $M$ 的合法向量只有 $00,11$，实际与参考质量分别为

$$
\begin{aligned}
\mathsf R(00)&=\frac{M+2}{2(M+1)},&
\mathsf R(11)&=\frac{M}{2(M+1)},\\
\mathsf Q(00)&=\frac{(M+2)^2}{(M+2)^2+M^2},&
\mathsf Q(11)&=\frac{M^2}{(M+2)^2+M^2}.
\end{aligned}
$$

因此在偶 $M\ge6$ 上

$$
\|\mathsf R_{2,M}-\mathsf Q_{2,M}\|_{\mathrm{TV}}
=\frac{M(M+2)}{2(M+1)(M^2+2M+2)},\qquad
\lim_{\substack{M\to\infty\\M\text{ 偶}}}
M\|\mathsf R_{2,M}-\mathsf Q_{2,M}\|_{\mathrm{TV}}=\frac12.
\tag{285.18}
$$

这只是 (285.3)–(285.4) 的边界代入，说明不能将所有固定 $d$ 的误差统一写为只有 $O(d^2/M^2)$ 的界。$k=0$ 对应 $d=1$，只有一个叶词，窗口确定，但全部 Catalan 括号仍作为不同树保留。$k=1$ 对应 $d=2$；(285.1) 在第一方向给 $u=-w$、第二方向给 $u=v$，故三维协方差奇异，不能直接使用三维高斯密度、正定性或逆协方差。

对有界 $k$，(285.7) 给完整向量及树换权的 $O_k(M^{-1})$ 绝对误差。对 $d/M\to0$ 的参数族，令 $\delta_g=d/(M+d)$，由
$\sqrt d/M=\delta_g/((1-\delta_g)\sqrt d)$ 和
$d(d-1)/M^2\le\delta_g^2/(1-\delta_g)^2$，同一界可写为
$O(\delta_g/\sqrt d+\delta_g^2)$；无需另加 $\delta_g\sqrt d\to0$。这些是有限界的范围解释，不给固定 $k$ 的完整三维 Gaussian，也不给单点相对局部误差或条件于罕见事件后的同一误差。$d\ge2,M<3d$ 不在 (285.7) 的估计域；$M<d$ 的范围不能无条件使用实际核 (285.5)：例如 $d=3,M=1$ 时，参考律对 $\xi=(1,1,1)$ 赋正质量，但 $s_\xi=-1$，实际质量为零。

计数、几何奇偶分解、两方向坐标和 Dirichlet—多项式条件核采用本卷 §§283–284；正规形及实际支撑采用母卷 §§359–360；积分比较、Taylor 余项、Cauchy–Schwarz 与有限 Jensen 作为成熟中间工具使用。Bender–Canfield，*Locally Restricted Compositions I. Restricted Adjacent Differences*，DOI [10.37236/1954](https://doi.org/10.37236/1954)，[原文](https://mathweb.ucsd.edu/~ebender/reprints/111.pdf) Definition 1 及 Theorems 1、3 的局部限制组成、渐近计数与固定统计维数范围，不直接供应这里全部 $d$ 位、含终端条件的显式有限界；本命题也不将那些文献的渐近结论当作定量证明前提。

(285.7)–(285.9) 的概率量词仅涉及原组成纤维的均匀树律与明示重加权参考律。它们不提供原仿射整数 $N^*=1+F_r g^*$ 上、保留完整素幂及全部除数的严格预算

$$
C^*+H^*<\left(\frac{\log\log N^*}{\log\log A}\right)^s,
\qquad s=\log A\,\log\log A.
$$

该预算在原素数、连续区间、同整数和终端条件下仍为独立未决问题；统计换权不支付它，也不推出 Robin 或 RH。

## 追加锚（本行以下为增补区）

## 286. 同一非稀疏组成源的三窗口似然一致抵消

定义与来源约定。沿用定义 285.1 的实际有序非空满二叉树、组成纤维均匀律 $U(a,b)$、原替换 $\rho$ 和三窗口 $W_3$。对 $k=\min(a,b)\ge1$、$M=\max(a,b)$，置 $d=k+1$。参考律 $\widetilde U(a,b)$ 使用定义 285.2 的全部 $d$ 位奇偶律 $\mathsf Q_{d,M}$、同一个实际条件核 (285.5)、指定少数字母方向的原叶词及全部均匀 Catalan 括号；相等组成仍以 $\alpha$ 分隔。这个合同在 $M\ge d-1$ 时均有定义，边界的非空性在下面证明内核对。记

$$
D_W(a,b)=\left\|(W_3)_*U(a,b)-(W_3)_*\widetilde U(a,b)\right\|_{\mathrm{TV}},
\qquad \|P-Q\|_{\mathrm{TV}}=\frac12\sum_x|P(x)-Q(x)|.
$$

**定理 286.1（同源三窗口的非稀疏一致总变差界）。** 对每个实数 $c_0\in(0,1]$，存在有限常数 $C(c_0)>0$，使全部非负整数组成 $(a,b)$ 满足

$$
k=\min(a,b)\ge1,\qquad M=\max(a,b),\qquad c_0\le\frac{k}{M}\le1
$$

时，都有

$$
D_W(a,b)\le\min\left\{1,\ C(c_0)(k+1)^{-1/20}\right\}.
\tag{286.1}
$$

常数在组成、两个方向及所有端点奇偶之前选定。因此，任意满足同一 $c_0$ 下界且 $k\to\infty$ 的组成族，其实际三窗口总变差一致趋于零；包括 $a=b$、比例不收敛及少数字母方向任意切换的族。

证明。固定 $c_0$。下文的 $C,c>0$ 可逐式增大或减小，但只依赖 $c_0$。先对充分大的 $d$ 证明估计，最后统一处理小 $d$。使用定义 285.1 的同一个间隔向量 $r$、完整 $\xi$、累计奇偶 $\varepsilon$ 和 $X=(H,O,E)$。此处 $E$ 是占据量，与叶积 $E(t)$ 区分。合法总奇数位数的有限集合为

$$
\mathcal H_{d,M}=\{h\in\mathbb Z:0\le h\le d,\ h\le M,\ h\equiv M\pmod2\}.
$$

由 $M\ge k=d-1$，参考律的每个正质量向量都有 $h\le M$：$M\ge d$ 时显然；$M=d-1$ 时唯一可能超出者 $h=d$ 与 $M$ 奇偶相反。因此 (285.5) 在全部参考正质量纤维上都是同一个非空实际核 $K_\xi$，包括 $s_\xi=(M-h)/2=0$。均匀弱组成及全部括号的回接直接使用 §285；两树律满足

$$
U(t)=\mathsf R(\xi(t))K_{\xi(t)}(t),\qquad
\widetilde U(t)=\mathsf Q(\xi(t))K_{\xi(t)}(t).
\tag{286.2}
$$

仅在 $h\in\mathcal H_{d,M}$ 上定义正似然 $u(h)=\mathsf R(\xi)/\mathsf Q(\xi)$。由 (285.3)–(285.4)，它只依赖 $h$。记 $R_h,Q_h$ 为这两律的 $h$ 边缘，$P_R(h,X),P_{\widetilde U}(h,X)$ 为各自的同源联合质量，则

$$
R_h(h)=u(h)Q_h(h),\qquad
P_{\widetilde U}(h,X)=\frac{P_R(h,X)}{u(h)}.
\tag{286.3}
$$

这些式子由同一个 $K_\xi$ 汇总得到，不假定条件后的 $T$ 与 $\xi$ 独立。在固定组成下，(285.1) 的两个仿射式都是 $X\leftrightarrow Z$ 的双射：第一方向先由 $u,w$ 恢复 $O-E,O+E$，再由 $v$ 恢复 $H$；第二方向先由 $u,v$ 恢复 $E-O,O+E$，再由 $w$ 恢复 $H$。组成决定 $p,q$，母卷定理 359.3 又给出 $Z\leftrightarrow W_3$ 的实际像双射。因此

$$
D_W(a,b)=\frac12\sum_X|P_R^X(X)-P_{\widetilde U}^X(X)|.
\tag{286.4}
$$

母卷定理 360.2 的八边非负整数及含 $00$ 的弱 Euler 支撑仍由原路径承担；两律在实际支撑之外都为零。

为估计这个联合律，临时在辅助层独立取

$$
\mathbb P_{\mathrm{geom}}(r_i=j)=(1-\tau)\tau^j\quad(j\ge0),\qquad
\tau=\frac{M}{M+d},\quad \nu=\frac{\tau}{1+\tau},\quad
\varrho=\frac{1-\tau}{1+\tau},\quad
\mu=\frac{\tau}{1-\tau},
$$

并置 $L=\sum_i r_i$。条件于 $L=M$ 时每个间隔向量质量同为 $(1-\tau)^d\tau^M$，故恰回到原均匀弱组成；随后仍附全部原括号。这里 $\varrho$ 是标量，原树替换仍记 $\rho$；几何方差记 $\sigma_r^2$，不改变 Clifford 元 $S=BA$。实际参数属于紧集

$$
K=[1/3,\tau_+],\qquad \tau_+=\frac1{1+c_0}<1,\qquad
0<\varrho\le\frac12.
\tag{286.5}
$$

辅助层仅用于精确条件化，不引入另一树采样律。

令频率 $\theta=(s,t,z,x,y)$ 依次配对 $(L,H,h,O,E)$，定义

$$
\begin{aligned}
G(s,z)&=\frac{1-\tau}{1-\tau^2e^{2is}}
 \begin{pmatrix}1&\tau e^{i(s+z)}\\ \tau e^{i(s+z)}&1\end{pmatrix},\qquad
D(x)=\operatorname{diag}(1,e^{ix}),\\
T(\theta)&=G(s,z)D(x)G(s+t,z)D(y).
\end{aligned}
\tag{286.6}
$$

令 $e_j$ 为状态 $j\in\{0,1\}$ 的标准列向量，$\varepsilon_0=0$，并保留最后一个间隔与端点：

$$
F_d^e(\theta)=\mathbb E_{\mathrm{geom}}
 \left[e^{i\theta\cdot(L,H,h,O,E)}\mathbf1_{\{\varepsilon_d=e\}}\right].
$$

逐间隔求和偶、奇长度，得到精确的两个式子

$$
\begin{aligned}
F_{2m}^e&=e_0^{\mathsf T}T^{m-1}G(s,z)D(x)G(s+t,z)e_e,\\
F_{2m+1}^e&=e_0^{\mathsf T}T^mG(s,z)e_e.
\end{aligned}
\tag{286.7}
$$

第一个 $G$ 记录偶索引间隔，第二个记录奇索引间隔；$D(x),D(y)$ 只计内部奇、偶位置。偶数 $d$ 的末式没有 $D(y)$，所以 $\varepsilon_d$ 不被计入占据量，末间隔却仍贡献 $L,H,h$。在零点

$$
T(0)=P_\nu^2,\qquad
P_\nu=\begin{pmatrix}1-\nu&\nu\\\nu&1-\nu\end{pmatrix},
$$

特征值为 $1,\varrho^2$，谱隙至少 $3/4$。

先完整确定五维频率环面的单位模共振。实频率上逐项有 $|T(\theta)|\le P_\nu^2$，后者严格正且随机，故谱半径至多一。若 $T v=\zeta v$、$|\zeta|=1$，在模最大坐标的三角等号中，严格正性迫使 $|v_0|=|v_1|>0$。每一条正概率双间隔路径 $a\to b\to c$ 的相位也必须分别取等号，即

$$
e^{i\psi}v_c=\zeta v_a,\qquad
\psi=s(r_0+r_1)+tr_1+z(\xi_0+\xi_1)+xb+yc.
$$

把任一间隔增加二，先得 $s,s+t\in\pi\mathbb Z$，写 $s=A\pi,t=B\pi$。状态零的零长度自环给 $\zeta=1$；状态一的零长度自环给 $x+y\equiv0$。比较 $0\to1$ 的长度对 $(0,1),(1,0)$，得到 $x\equiv t$，故 $x=y=B\pi$。再用 $0\to0$ 的 $(1,1)$ 路径，得到 $2s+t+2z+x\equiv0$，即 $z=C\pi$。所有同余均模 $2\pi$。所以共振只能属于

$$
\Gamma=\{(A\pi,B\pi,C\pi,B\pi,B\pi):A,B,C\in\{0,1\}\}.
\tag{286.8}
$$

反向令 $J=\operatorname{diag}(1,-1)$。直接代入 (286.6)，对 $\gamma\in\Gamma$ 有

$$
T(\theta+\gamma)=J^{A+C}T(\theta)J^{A+C},\qquad
F_d^e(\theta+\gamma)=(-1)^{(A+C+\kappa B)e}F_d^e(\theta),
\quad \kappa=(d-1)\bmod2.
\tag{286.9}
$$

于是八点全部共振，且没有遗漏。路径上本来就有

$$
L\equiv h\equiv\varepsilon_d,\qquad
H-O-E\equiv\kappa\varepsilon_d\pmod2.
\tag{286.10}
$$

第二式由 $H\equiv\sum_{i\text{ 奇}}\xi_i$ 及 $\xi_i=\varepsilon_i\oplus\varepsilon_{i+1}$ 逐项消去得到。五维比较格为

$$
\mathcal L_d=\{(l,H,h,O,E)\in\mathbb Z^5:l\equiv h,\ H-O-E\equiv\kappa l\pmod2\},
$$

指数为四。固定 $l=M$ 后，它精确分解为

$$
(M+2\mathbb Z)\times\Lambda_X,\qquad
\Lambda_X=\{(H,O,E)\in\mathbb Z^3:H-O-E\equiv\kappa M\pmod2\}.
\tag{286.11}
$$

$h$ 格与 $X$ 格各有指数二，$X$ 的陪集不依赖 $h$。这些比较格不是实际可实现支撑的充分条件；非负间隔、八边非负和弱连通条件仍全部保留。

下面计算谱展开的二次型。置

$$
\begin{gathered}
N_o=\lfloor d/2\rfloor,\qquad n_e=\lfloor(d-1)/2\rfloor,\qquad
\alpha_o=N_o/d,\qquad J_H=H-L/2,\\
v=\frac{\tau}{(1+\tau)^2},\qquad
\sigma_r^2=\frac{\tau}{(1-\tau)^2},\qquad \chi=1-\varrho^2,\\
m_X=(\alpha_o M,N_o/2,n_e/2),\qquad
b_d=(M,\alpha_o M,d\nu,N_o/2,n_e/2).
\end{gathered}
\tag{286.12}
$$

$m_X,b_d$ 是比较中心，未声称为全部条件坐标的精确均值。几何级数给

$$
\mathbb E r_i=\mu,\quad \operatorname{Var}(r_i)=\sigma_r^2,\quad
\mathbb E\xi_i=\nu,\quad
\operatorname{Var}(\xi_i)=\operatorname{Cov}(r_i,\xi_i)=v.
$$

令 $\eta_j=(-1)^{\varepsilon_j}$，初态是 $\eta_0=1$，则

$$
\mathbb E\eta_j=\varrho^j,\qquad
\mathbb E\eta_i\eta_j=\varrho^{|i-j|},\qquad
\operatorname{Cov}(\eta_i,\eta_j)=\varrho^{|i-j|}-\varrho^{i+j}.
\tag{286.13}
$$

由独立间隔直接展开，对 $i<j$ 有

$$
\operatorname{Cov}(r_i,\eta_j)=\operatorname{Cov}(\xi_i,\eta_j)
=-2v\varrho^{j-1};
$$

$i\ge j$ 时两协方差为零。因此任何长坐标 $L,h,J_H$ 与 $O,E$ 的交叉协方差绝对值至多常数乘
$\sum_{j\ge1}j\varrho^{j-1}$，在 $K$ 上统一有界。

$J_H$ 的间隔系数为 $\pm1/2$；直接得到

$$
\begin{gathered}
\operatorname{Var}L=d\sigma_r^2,\quad \operatorname{Var}h=dv,\quad
\operatorname{Cov}(L,h)=dv,\quad \operatorname{Var}J_H=d\sigma_r^2/4,\\
\operatorname{Cov}(L,J_H)=\sigma_r^2(N_o-d/2),\quad
\operatorname{Cov}(h,J_H)=v(N_o-d/2).
\end{gathered}
$$

后两项只是统一有界的端点项。对奇内部位置集合 $I_o$ 和偶内部位置集合 $I_e$，使用 $O-N_o/2=-\frac12\sum_{j\in I_o}\eta_j$ 及相应 $E$ 式，有

$$
\begin{aligned}
\operatorname{Var}O
&=\frac14\left[N_o+2\sum_{q=1}^{N_o-1}(N_o-q)\varrho^{2q}
 -\left(\sum_{j\in I_o}\varrho^j\right)^2\right],\\
\operatorname{Var}E
&=\frac14\left[n_e+2\sum_{q=1}^{n_e-1}(n_e-q)\varrho^{2q}
 -\left(\sum_{j\in I_e}\varrho^j\right)^2\right],\\
\operatorname{Cov}(O,E)
&=\frac14\left[\sum_{\substack{1\le q<d-1\\q\text{ 奇}}}(d-1-q)\varrho^q
 -\left(\sum_{j\in I_o}\varrho^j\right)
  \left(\sum_{j\in I_e}\varrho^j\right)\right].
\end{aligned}
\tag{286.14}
$$

空集合及空和取零。有限几何和与无限和之差由 $\sum q\varrho^{2q}$、$\sum(q+1)\varrho^q$ 和 $\sum\varrho^q$ 控制。均值的偏置也只是这些几何和。因此，在坐标 $(L,h,J_H,O,E)$ 中，均值与由 $b_d$ 变换所得中心相差 $O(1)$，协方差为

$$
d\operatorname{diag}(A_\tau,C_\tau)+O(1),
\quad
A_\tau=\begin{pmatrix}\sigma_r^2&v\\v&v\end{pmatrix},\qquad
C_\tau=\begin{pmatrix}
\sigma_r^2/4&0&0\\
0&(1+\varrho^2)/(8\chi)&\varrho/(4\chi)\\
0&\varrho/(4\chi)&(1+\varrho^2)/(8\chi)
\end{pmatrix}.
\tag{286.15}
$$

各余项逐条在 $K$ 上统一有界。$\det A_\tau=\sigma_r^2v\chi>0$；$C_\tau$ 的三个特征值为
$\sigma_r^2/4,(1+\varrho)^2/(8\chi),(1-\varrho)^2/(8\chi)$。故两个矩阵一致正定。原顺序 $(L,H,h,O,E)$ 的每间隔比较协方差为

$$
\Sigma_\tau=
\begin{pmatrix}
\sigma_r^2&\sigma_r^2/2&v&0&0\\
\sigma_r^2/2&\sigma_r^2/2&v/2&0&0\\
v&v/2&v&0&0\\
0&0&0&(1+\varrho^2)/(8\chi)&\varrho/(4\chi)\\
0&0&0&\varrho/(4\chi)&(1+\varrho^2)/(8\chi)
\end{pmatrix}.
\tag{286.16}
$$

固定可逆坐标变换保持一致正定；记其在 $K$ 上的最小特征值下界为 $s_*>0$。

现在直接作解析展开及离散反演。先选共同复多圆盘半径 $R>0$，使 $\tau_+^2e^{4R}<1$。两个 $G$ 的分母在该域都离零至少 $1-\tau_+^2e^{4R}>0$；矩阵及其边界因子因而解析且统一有界。置

$$
\Delta=(\operatorname{tr}T)^2-4\det T,\qquad
\lambda=\frac{\operatorname{tr}T+\sqrt\Delta}{2},\qquad
\lambda_2=\frac{\operatorname{tr}T-\sqrt\Delta}{2},\qquad
\Pi=\frac{T-\lambda_2 I}{\lambda-\lambda_2}.
\tag{286.17}
$$

$\Delta(0)=(1-\varrho^2)^2\ge9/16$。紧参数连续性允许统一缩小多圆盘，使 $\operatorname{Re}\Delta>0$；取零点正值的平方根支。再统一缩小，使
$|\lambda-1|\le1/8$、$|\lambda_2|\le3/8$、$|\lambda-\lambda_2|\ge1/2$。于是 $\log\lambda$ 取零点值零的解析支，$\Pi$ 也解析。若这些函数在半径 $R_1$ 的闭多圆盘上的界为 $B$，多变量 Cauchy 公式在半径 $R_1/2$ 的盘内给

$$
|\partial^\beta f|\le\beta!(2/R_1)^{|\beta|}B\quad(|\beta|\le3).
$$

边界振幅的前几阶导数有同类统一界，故三阶 Taylor 余项的统一常数由已证非零分母及谱隙取得。

为确认二次项而非假设它，取奇数 $d=2m+1$，把两个端点相加。在该共同邻域由 (286.7)、(286.17) 精确写成

$$
F_d^0+F_d^1=\lambda^m A_o+\lambda_2^m B_o,\qquad A_o(0)=1.
$$

振幅导数统一有界，次谱项零点前两阶导数的模至多
$C(1+m^2)(3/8)^{m-2}$。对零点求对数前两阶导数，其值分别为实际均值乘 $i$ 与实际协方差的负值。用 (286.13)–(286.16) 的有限矩，除以 $m$ 并令 $m\to\infty$，得到

$$
\log\lambda(\theta)=i\beta_2\cdot\theta-\theta^{\mathsf T}\Sigma_\tau\theta
 +O(\|\theta\|^3),\qquad
\beta_2=(2\mu,\mu,2\nu,1/2,1/2).
\tag{286.18}
$$

这只使用精确生成式和实际有限矩，不以极限定理反推谱导数。对于所有 $\tau\in K$，同一矩推导以 $M=d\mu$ 表示中心即可成立；因此余项在整个 $K$ 上统一。

主投影在零点为 $\Pi(0)=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix}$。两类端点主振幅

$$
a_o^e=e_0^{\mathsf T}\Pi G(s,z)e_e,\qquad
a_e^e=e_0^{\mathsf T}\Pi G(s,z)D(x)G(s+t,z)e_e
$$

在零点均为 $1/2$，且 $|a_o^e(\theta)-1/2|+|a_e^e(\theta)-1/2|\le C\|\theta\|$。准确的有限端点质量仍为
$F_d^e(0)=[1+(-1)^e\varrho^d]/2$，并未改成平稳端点。令奇数 $d$ 时 $n=(d-1)/2$，偶数时 $n=(d-2)/2$。$n\beta_2-b_d$ 在奇数时等于 $(-\mu,0,-\nu,0,0)$，偶数时等于 $(-2\mu,-\mu,-2\nu,-1/2,0)$；$|n-d/2|\le1$。这些位移在 $K$ 上有界，可记 $\mu_+=\max_K\mu<\infty$。

选足够小的共同实半径 $\delta>0$，使八个共振邻域互不相交，且 (286.18) 的三阶余项小于 $s_*\|\theta\|^2/2$。于是零点邻域内 $\operatorname{Re}\log\lambda\le-s_*\|\theta\|^2/2$。利用

$$
e^U-e^V=(U-V)\int_0^1e^{(1-t)V+tU}\,dt
$$

依次比较 $n\log\lambda$ 与 $in\beta_2\cdot\theta-n\theta^{\mathsf T}\Sigma_\tau\theta$，再比较后者与 $ib_d\cdot\theta-d\theta^{\mathsf T}\Sigma_\tau\theta/2$。振幅差为 $O(\|\theta\|)$，位移差为 $O(\|\theta\|+\|\theta\|^2)$，三阶差为 $O(d\|\theta\|^3)$；次谱项由 $|\lambda_2|\le3/8$ 控制。$d\ge4$ 时 $n\ge d/4$，从而对两种端点和两类 $d$ 同时有

$$
\left|F_d^e(\theta)-\frac12
 e^{ib_d\cdot\theta-d\theta^{\mathsf T}\Sigma_\tau\theta/2}\right|
\le C(\|\theta\|+d\|\theta\|^3)e^{-cd\|\theta\|^2}+Cq^d,
\quad \|\theta\|\le\delta,\quad q<1.
\tag{286.19}
$$

其余七个邻域使用 (286.9)。远离八点的闭频率集上，由完整共振分类和紧性，$q_0=\max\operatorname{spr}T<1$。选 $q_f\in(q_0,1)$；圆 $|w|=q_f$ 上的预解式 $(wI-T)^{-1}$ 在该紧集统一有界。矩阵 Cauchy 公式

$$
T^n=\frac1{2\pi i}\int_{|w|=q_f}w^n(wI-T)^{-1}\,dw
$$

给出统一指数衰减，亦覆盖次特征值重合或不可对角化的点。边界矩阵在实频率上有界，所以远区的完整 $F_d^e$ 同样指数衰减。

令 $\phi_V$ 表示正定协方差 $V$ 的连续高斯密度；这里只在格点取值作为比较函数。五维离散反演为

$$
\mathbb P_{\mathrm{geom}}(Y=y,\varepsilon_d=e)
=(2\pi)^{-5}\int_{\mathbb T^5}e^{-i\theta\cdot y}F_d^e(\theta)\,d\theta,
\quad Y=(L,H,h,O,E).
$$

(286.19) 的一次项积分为 $O(d^{-3})$，$d$ 乘三次项积分也为 $O(d^{-3})$，因为

$$
\int_{\mathbb R^5}\|\theta\|^p e^{-cd\|\theta\|^2}\,d\theta
=C_p d^{-(5+p)/2}\quad(p=1,3).
$$

远区、次谱和延长高斯积分到 $\mathbb R^5$ 的误差均指数小，故可吸收到 $Cd^{-3}$。反演相位模为一，所以该误差对全部整数 $y$ 一致。八个中心的相位和为

$$
\sum_{A,B,C\in\{0,1\}}
(-1)^{A(l-e)+C(h-e)+B(H+O+E-\kappa e)}
=8\mathbf1_{\{l\equiv h\equiv e,\ H-O-E\equiv\kappa e\ (2)\}}.
$$

乘主振幅 $1/2$ 恰得因子四。因 $L$ 已决定端点，得到对全部 $y\in\mathcal L_d$ 的全格绝对估计

$$
\mathbb P_{\mathrm{geom}}(Y=y)
=4d^{-5/2}\phi_{\Sigma_\tau}\left(\frac{y-b_d}{\sqrt d}\right)
 +O(d^{-3}).
\tag{286.20}
$$

非法格点的真实质量严格为零，比较质量也按零延拓。合法格中不满足真实支撑的点，其真实质量仍为零；上述反演误差同样覆盖这些点，没有将其删去，也未宣称所有比较格点可实现。

条件化还须支付真实离散分母。$L$ 的单间隔特征函数是

$$
f_L(s)=\frac{1-\tau}{1-\tau e^{is}}.
$$

零、一次、二次长度均有正质量，三角等号给唯一共振 $s=0\pmod{2\pi}$。共同复邻域内

$$
\log f_L(s)=i\mu s-\frac12\sigma_r^2s^2+O(|s|^3).
$$

例如从 $\log f_L(s)=\sum_{j\ge1}\tau^j(e^{ijs}-1)/j$ 可直接界定三阶导数；取 $\tau_+e^R<1$ 时，其模至多 $r(1+r)/(1-r)^3$，$r=\tau_+e^R<1$。零点小邻域的高斯衰减与远区的统一严格模小于一，给出一维离散反演；三阶项的积分为 $d\int |s|^3e^{-cds^2}ds=O(d^{-1})$。因此

$$
p_L(M):=\mathbb P_{\mathrm{geom}}(L=M)
=d^{-1/2}a_\tau+O(d^{-1}),\qquad
 a_\tau=\phi_{\sigma_r^2}(0).
\tag{286.21}
$$

$\inf_K a_\tau>0$，所以对某个只依赖 $c_0$ 的阈值 $d_0$，$p_L(M)\ge cd^{-1/2}$，且将分母中的 $a_\tau+O(d^{-1/2})$ 换为 $a_\tau$ 的倒数误差为 $O(d^{-1/2})$。

同样，$(L,h)$ 的单间隔特征函数为

$$
f_2(s,z)=\frac{(1-\tau)(1+\tau e^{i(s+z)})}{1-\tau^2e^{2is}}.
$$

逐长度比较零、一次、二次相位，完整共振恰为 $(0,0),(\pi,\pi)$，比较格为 $l\equiv h\pmod2$，指数二。取共同小复邻域使 $|f_2-1|\le1/2$，便有统一解析的 $\log f_2$；Cauchy 公式给共同三阶余项。其前两阶导数来自单间隔的已算矩，故

$$
\log f_2(s,z)=i(\mu s+\nu z)
 -\frac12(s,z)A_\tau(s,z)^{\mathsf T}+O(\|(s,z)\|^3).
$$

一致正定性给局部高斯衰减；其余紧频率集上的模统一小于一。二维三阶项积分为
$d\int_{\mathbb R^2}\|\theta\|^3e^{-cd\|\theta\|^2}d\theta=O(d^{-3/2})$；两中心同相给

$$
\mathbb P_{\mathrm{geom}}(L=l,h=h_0)
=2d^{-1}\phi_{A_\tau}
 \left(\frac{l-M}{\sqrt d},\frac{h_0-d\nu}{\sqrt d}\right)
 +O(d^{-3/2})\quad(l\equiv h_0\pmod2).
\tag{286.22}
$$

这些一、二、五维估计均由显式函数、完整共振和离散反演产生。

置 $x_h=(h-d\nu)/\sqrt d$、$x_X=(X-m_X)/\sqrt d$。坐标变换 $(L,H,h,O,E)\mapsto(L,h,J_H,O,E)$ 的行列式绝对值一。由 (286.15)，高斯条件于 $L=M$ 时 $h$ 的 Schur 补方差为

$$
v-\frac{v^2}{\sigma_r^2}=v\chi>0;
$$

其余三维块为 $C_\tau$，$J_H$ 在 $L=M$ 下恢复的 $H$ 中心恰为 $\alpha_o M$。因此密度的精确分解为

$$
\phi_{\Sigma_\tau}(0,x_H,x_h,x_O,x_E)
=a_\tau\phi_{v\chi}(x_h)\phi_{C_\tau}(x_X).
$$

将 (286.20) 在 $l=M$ 处除以真实 (286.21)，分子误差贡献 $O(d^{-3})/p_L(M)=O(d^{-5/2})$，分母倒数误差贡献 $O(d^{-2}d^{-1/2})$。二维估计同样条件化，遂得全比较格上的两个绝对估计

$$
\begin{aligned}
P_R(h,X)&=4d^{-2}\phi_{v\chi}(x_h)\phi_{C_\tau}(x_X)+O(d^{-5/2}),\\
R_h(h)&=2d^{-1/2}\phi_{v\chi}(x_h)+O(d^{-1}).
\end{aligned}
\tag{286.23}
$$

在 $\Lambda_X$ 上定义

$$
g_d(X)=2d^{-3/2}\phi_{C_\tau}(x_X),
$$

其余整数点取零。统一正定性给 $\sup_Xg_d(X)\le G_\infty d^{-3/2}$。相乘相减得到承重的条件联合分解

$$
\sup_{\substack{h\in M+2\mathbb Z\\ X\in\Lambda_X}}
|\mathcal E_d(h,X)|\le Cd^{-5/2},\qquad
\mathcal E_d(h,X)=P_R(h,X)-R_h(h)g_d(X).
\tag{286.24}
$$

$h\notin\mathcal H_{d,M}$ 时真实 $R_h$ 和联合质量按零延拓，(286.24) 仍成立；没有在这些点求逆似然。真实不可实现的 $X$ 点也保持零质量。分解来自完整反演和真实条件化，不由零协方差单独推断独立。

$g_d$ 只是非负比较函数，不要求精确归一化。若 $c_*\le\lambda_{\min}(C_\tau)\le\lambda_{\max}(C_\tau)\le c^*$ 是 $K$ 上的共同界，则有常数 $A_g,a_g>0$ 使

$$
g_d(X)\le A_gd^{-3/2}\exp\left(-a_g\frac{\|X-m_X\|_2^2}{d}\right).
$$

对任意实中心 $t$，将单峰高斯和按中心两侧作积分比较，得
$\sum_{n\in\mathbb Z}e^{-a_g(n-t)^2/d}\le2+\sqrt{\pi d/a_g}$。即使放大到整个 $\mathbb Z^3$，三坐标相乘也给共同质量上界。再用
$u e^{-a_gu}\le[2/(a_ge)]e^{-a_gu/2}$，得到只依赖 $c_0$ 的

$$
\sum_Xg_d(X)\le G_{\mathrm{mass}}<\infty,\qquad
\sum_Xg_d(X)\frac{\|X-m_X\|_2^2}{d}\le G_{\mathrm{mom}}<\infty.
\tag{286.25}
$$

从而任意 $B>0$ 均有

$$
\sum_{\|X-m_X\|_\infty>B\sqrt d}g_d(X)\le G_{\mathrm{mom}}B^{-2}.
\tag{286.26}
$$

以上只比较格点函数与积分，不涉及离散树律对连续高斯律的总变差。

现在在同一个核上控制似然。对 $0\le x\le d$ 定义

$$
\ell(x)=\sum_{j=1}^{d-1}\log(M-x+2j)-x\log\tau,\qquad m=d\nu.
$$

$M\ge d-1$ 给全部对数参数至少一。展开 (285.3)–(285.4) 的组合数，并用 $\mathbb E_Q u=1$，精确得到

$$
u(h)=\frac{e^{\ell(h)-\ell(m)}}{c_\ell},\qquad
c_\ell=\mathbb E_Q e^{\ell(h)-\ell(m)}.
\tag{286.27}
$$

令 $A_m=M-m$，则

$$
A_m=\frac{2M^2}{2M+d},\qquad A_m+2d=\frac{2(M+d)^2}{2M+d},\qquad
\int_0^d\frac{dy}{A_m+2y}=-\log\tau.
$$

递减函数的完整离散和与积分比较给

$$
0\le\ell'(m)\le\frac1{A_m}\le\frac3d\quad(d\ge3).
\tag{286.28}
$$

最后一界可在最小 $M=d-1$ 核对，此后 $A_m$ 随 $M$ 增加。全域凹性给 $\ell(h)-\ell(m)\le3$。在 $|h-m|\le d/4$ 上，因 $m<d/2$，连接线段有 $x\le3d/4$，故

$$
-\ell''(x)=\sum_{j=1}^{d-1}(M-x+2j)^{-2}\le16/d.
$$

Taylor 积分余项因此给

$$
\ell(h)-\ell(m)\ge-3|h-m|/d-8(h-m)^2/d.
\tag{286.29}
$$

未条件 Bernoulli 总和的均值为 $m$、方差为 $dv\le d/4$。完整终端条件代价是

$$
p_e=\frac{1+(-1)^M\varrho^d}{2}\ge\frac13\quad(d\ge2).
$$

对非负平方只付出 $p_e^{-1}$，所以 $\mathbb E_Q(h-m)^2\le3d/4$。$d\ge16$ 时，$Q\{|h-m|\le\sqrt d\}\ge1/4$，该事件落在 (286.29) 内，其上 $\ell(h)-\ell(m)\ge-11$。故

$$
e^{-11}/4\le c_\ell\le e^3,\qquad
0<u(h)\le U_+:=4e^{14}\quad(h\in\mathcal H_{d,M},\ d\ge16).
\tag{286.30}
$$

这是全域正向界。逆似然只在增长窗上使用：若 $|h-m|\le r\sqrt d$、$r\sqrt d\le d/4$，则

$$
\frac1{u(h)}\le e^{3+3r/\sqrt d+8r^2}\le e^{15/4+8r^2}.
\tag{286.31}
$$

不将此式扩张到全部合法 $h$。

对一个未条件中心化 Bernoulli 位，令 $K_B(\lambda)=\log\mathbb E e^{\lambda(\xi-\nu)}$。$K_B(0)=K_B'(0)=0$，$K_B''(\lambda)$ 是倾斜 Bernoulli 方差，至多 $1/4$，所以两次积分给 $K_B(\lambda)\le\lambda^2/8$，包括负 $\lambda$。独立总和的 Chernoff 优化给未条件尾界 $2e^{-2r^2}$。付出真实终端条件代价，再由 $R_h=uQ_h$ 与全域正向界，得

$$
Q_h\{|h-m|>r\sqrt d\}\le6e^{-2r^2},\qquad
R_h\{|h-m|>r\sqrt d\}\le6U_+e^{-2r^2}\quad(d\ge16).
\tag{286.32}
$$

$m$ 不必是终端条件后的精确均值；这些尾界围绕同一个比较中心成立。

还须控制同一个实际 $X$ 的两种真实尾。未条件 Bernoulli 层由 (286.13) 直接给每个 $N\in\{N_o,n_e\}$ 的对应占据量中心二阶矩

$$
\frac14\left[N+2\sum_{q=1}^{N-1}(N-q)\varrho^{2q}\right]
\le\frac N4\frac{1+\varrho^2}{1-\varrho^2}\le\frac{5N}{12}.
$$

它以 $N/2$ 为比较中心，已包含非平稳初态偏置。对非负平方付出 $p_e^{-1}$，便得实际 $Q$ 历史上的

$$
\mathbb E_Q[(O-N_o/2)^2+(E-n_e/2)^2]\le5(d-1)/4.
\tag{286.33}
$$

用同一个 (285.16) 的 Beta—二项分组核，令 $N_a=d-N_o$、$h_o=\sum_{i\text{ 奇}}\xi_i$、$h_c=h_o-\alpha_o h$，则

$$
\mathbb E(H\mid\xi)=\alpha_o M+h_c,\qquad
\operatorname{Var}(H\mid\xi)
=\frac{4s_\xi\alpha_o(1-\alpha_o)(s_\xi+d)}{d+1}.
\tag{286.34}
$$

该式也可由正形状参数 $\operatorname{Beta}(N_o,N_a)$ 的前两阶积分矩和全方差公式取得。$d\ge2$ 时两形状参数均正；$s_\xi=0$ 时分组量恒零，(286.34) 的方差恰为零，不使用正剩余量近似。

终端条件只依赖 $h$，所以 $Q$ 的全部 $d$ 位可交换。置 $b_i=\mathbf1_{\{i\text{ 奇}\}}-\alpha_o$，有 $\sum_i b_i=0$、$\sum_i b_i^2=N_oN_a/d$。取两个不同位置的 $q_1=\mathbb E_Q\xi_0$、$q_2=\mathbb E_Q\xi_0\xi_1$，完整展开给

$$
\mathbb E_Q h_c=0,\qquad
\mathbb E_Q h_c^2=\frac{N_oN_a}{d}(q_1-q_2)
\le\frac{N_oN_a}{2d}\le\frac d8.
\tag{286.35}
$$

这里 $q_1-q_2=\frac12\mathbb E_Q(\xi_0-\xi_1)^2\le1/2$，因子不可省略；未假定条件位独立。以 (286.34) 的条件均值分解平方，交叉项条件期望为零。再用
$0\le s_\xi\le M/2\le d/(2c_0)$，得到

$$
\mathbb E_{\widetilde U}(H-\alpha_o M)^2
\le d\left(\frac1{4c_0^2}+\frac1{2c_0}+\frac18\right).
$$

结合 (286.33)，可取

$$
A(c_0)=\frac1{4c_0^2}+\frac1{2c_0}+\frac{11}{8},\qquad
\mathbb E_{\widetilde U}\|X-m_X\|_2^2\le A(c_0)d.
\tag{286.36}
$$

三个平方在同一个 $\xi,K_\xi$ 实现上求和，无须坐标独立。对同一个非负函数使用 (286.2)–(286.3) 和 $u\le U_+$，又得

$$
\mathbb E_U\|X-m_X\|_2^2\le U_+A(c_0)d.
$$

因 $\|X-m_X\|_\infty>B\sqrt d$ 蕴含 $\|X-m_X\|_2^2>B^2d$，两种真实窗口尾均有

$$
\widetilde U\{\|X-m_X\|_\infty>B\sqrt d\}\le A(c_0)B^{-2},\qquad
U\{\|X-m_X\|_\infty>B\sqrt d\}\le U_+A(c_0)B^{-2}.
\tag{286.37}
$$

最后在每一个相同窗口纤维内作有符号求和。对 $h\in\mathcal H_{d,M}$ 置 $a(h)=1-1/u(h)$。归一化给精确消去

$$
\sum_{h\in\mathcal H_{d,M}}a(h)R_h(h)
=\sum_h(R_h(h)-Q_h(h))=0.
$$

因此对每个 $X$，先在完整合法 $h$ 集上求和，才取绝对值：

$$
P_R^X(X)-P_{\widetilde U}^X(X)
=\sum_{h\in\mathcal H_{d,M}}a(h)\mathcal E_d(h,X).
\tag{286.38}
$$

取增长窗

$$
r^2=\frac{\log d}{40},\qquad B=d^{1/40}.
\tag{286.39}
$$

令 $d$ 充分大，使 (286.20)–(286.24) 和 $d\ge16$ 成立；$r\sqrt d\le d/4$ 也成立。由 (286.31)，中央 $h$ 窗内

$$
|a(h)|\le1+e^{15/4+8r^2}\le Cd^{1/5}.
$$

$|h-m|\le r\sqrt d$ 的整数点至多 $Cr\sqrt d$；$\|X-m_X\|_\infty\le B\sqrt d$ 的三维整数点至多 $CB^3d^{3/2}$。比较格取子集只减少点数。中央贡献于是由 (286.24) 支付为

$$
\sum_{\substack{|h-m|\le r\sqrt d\\\|X-m_X\|_\infty\le B\sqrt d}}
|a(h)\mathcal E_d(h,X)|
\le CrB^3d^2d^{1/5}d^{-5/2}
\le C\sqrt{\log d}\,d^{-9/40}.
\tag{286.40}
$$

补集不用局部误差乘无限点数，也不用全域逆似然界。由非负性与 (286.3)，逐点有

$$
|a(h)\mathcal E_d(h,X)|
\le P_R(h,X)+P_{\widetilde U}(h,X)
 +(R_h(h)+Q_h(h))g_d(X).
\tag{286.41}
$$

在 $h$ 尾上求全部 $X$ 和，前两项恰为真实 $R_h,Q_h$ 尾，最后一项为这两尾乘 $\sum_Xg_d(X)$；(286.25)、(286.32) 给总贡献 $Ce^{-2r^2}$。在 $X$ 尾上求全部合法 $h$ 和，前两项恰为同一实际 $U,\widetilde U$ 的 $X$ 尾，最后一项为 $2\sum_{X\text{ 尾}}g_d(X)$；(286.26)、(286.37) 给总贡献 $CB^{-2}$。两个尾的并集可用两者之和覆盖，所有实际零质量点仍保留。代入 (286.39) 后，两项分别都是 $Cd^{-1/20}$。由 (286.4)、(286.38)–(286.41)，得到

$$
2D_W(a,b)
\le C\left[\sqrt{\log d}\,d^{-9/40}+d^{-1/20}\right]
\le C'd^{-1/20}.
\tag{286.42}
$$

所有解析域、谱隙、正定性、反演余项及条件分母阈值只由紧集 $K$ 决定。故存在 $d_0(c_0)\ge16$，对全部 $d\ge d_0(c_0)$ 同时成立上述估计，不需要组成比例存在极限。对其余 $2\le d<d_0(c_0)$，直接用 $D_W\le1$，并把 $C(c_0)$ 增大到至少 $d_0(c_0)^{1/20}$，即可覆盖全部小 $d$，包括三维协方差退化的 $d=2$。两种 $d$ 奇偶、两种实际端点在 (286.7)–(286.10) 已统一处理；两个少数字母方向只在 (285.1) 的实际像双射回接处不同，$a=b$ 使用第一方向。再与 $D_W\le1$ 合并，证明 (286.1)。$\square$

数学来源与范围。实际原树、完整间隔、同一条件核、两方向仿射恢复及 Beta—二项分组直接采用本卷 §§283–285；三窗口唯一正规形与真实八边／弱 Euler 支撑直接采用[母卷](FIBONACCI_ATOMIC_RELATION_GENERATION.md) §§359–360。有限纤维提升、总变差通道收缩与纤维内同号的等号判据是已有中间供应，见 [FiberwiseEqualDistanceLift](../../../D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift.lean)、[DataProcessing](../../../D5/S3/TotalVariation/DataProcessing.lean) 和 [DataProcessingEquality](../../../D5/S3/TotalVariation/Equality/DataProcessingEquality.lean)；这里没有用它们将完整记录的误差或下界直接传给窗口。

Klein–Lagnoux–Petit，*A conditional Berry–Esseen inequality*，[arXiv:1901.09911v2](https://arxiv.org/pdf/1901.09911v2)，Proposition 1、Theorem 1、Proposition 2、Theorem 2 及均匀组成例，是标量条件分布函数估计和几何条件化的成熟背景；它们不承担上述含 $O,E$ 的五维格点质量反演。Ferré–Hervé–Ledoux，*Limit theorems for stationary Markov processes with $L^2$-spectral gap*，[arXiv:1201.4579v1](https://arxiv.org/pdf/1201.4579v1)，以及 Hervé–Ledoux，*Additional material on local limit theorem for finite Additive Markov Processes*，[arXiv:1305.5644v2](https://arxiv.org/pdf/1305.5644v2)，提供有限状态 Fourier 谱方法的背景；其中需要绝对连续部分的密度结论不用于本题纯格点律。这里的共同参数域、全部八共振、端点振幅、一／二／五维误差和条件化已由显式矩阵直接证明。[有限二项计数的模态惊讶与一致 escort 矩](PARITY_HIDDEN_ARROW_FINITE_BINOMIAL_SURPRISE.md)的定理 2.1 是实际单组质量的标量供应，也不直接给 (286.24) 与 (286.38) 的同核联合关系。

本定理的承重推导是同一实际条件联合质量的全比较格绝对分解、增长窗逆似然控制、真实两律尾界与窗口纤维内有符号抵消的组合；数学来源为仓内推导，不作全球优先权或指数最优性断言。它只控制原三窗口事件，不断言完整树或完整奇偶记录的总变差趋零，亦不改变原替换、左右次序或括号。$c_0$ 固定是统一性的条件；$c_0$ 随组成趋零的族仍须另给估计。

在原素数 $r\ge7$、$V=F_r$、连续区间、原低 $J$ 定位条件及同一整数 $N^*=1+Vg^*$ 上，保留完整素幂和所有除数的严格算术预算

$$
C^*+H^*<\left(\frac{\log\log N^*}{\log\log A}\right)^s,
\qquad s=\log A\,\log\log A
$$

仍为独立未决问题。本定理不提供它所需的低 $J$ 核心与高 $J$ 尾联合估计；已有 $H^*\le\varepsilon_A$ 只给充分条件
$`C^*+\varepsilon_A<(\log\log N^*/\log\log A)^s`$，不能把 $`C^*+\varepsilon_A<1`$ 当作必要条件。母卷 §§381–382 的实际 Fibonacci 闭包误差及有限最小公倍数族误差，均保留各自对象和范围，不替代这个原仿射整数预算；上述统计结论也不推出 Robin 或 RH。

## 追加锚（本行以下为增补区）
## 287. 原三窗口在全部组成比例上的统一正幂

**定义 287.1（原条件核与全比例缩放）。** 沿用定义 285.1–285.2 的自由有序非空满二叉树、叶 $\alpha,\beta$、组成纤维均匀律 $U(a,b)$ 和原替换

$$
\rho(\alpha)=\beta,\qquad \rho(\beta)=\langle\beta,\alpha\rangle,
\qquad \rho(\langle t_1,t_2\rangle)=\langle\rho(t_1),\rho(t_2)\rangle.
$$

叶积使用 $A^2=1,B^2=-1,AB+BA=1$，三个窗口为同一实际树的
$W_3(t)=(E(t),E(\rho t),E(\rho^2t))$；左右次序和全部括号属于来源数据。固定整数 $a,b\ge1$，记

$$
k=\min(a,b),\qquad M=\max(a,b),\qquad d=k+1\ge2,
\qquad \delta=\frac d{M+d},\quad \tau=1-\delta,
\quad \nu=\frac{\tau}{1+\tau},\quad
\varrho=\frac{\delta}{1+\tau},\quad
v=\frac{\tau}{(1+\tau)^2},\quad \chi=1-\varrho^2.
$$

此处 $\varrho$ 是标量，不是树替换 $\rho$。当 $a\le b$ 时以 $\alpha$ 分隔，当 $b<a$ 时以 $\beta$ 分隔，保留全部 $d$ 个间隔 $r_0,\ldots,r_{d-1}$，其和为 $M$。置

$$
\begin{gathered}
\xi_i=r_i\bmod2,\qquad h=\sum_{i=0}^{d-1}\xi_i,\qquad
\varepsilon_j=\sum_{i<j}\xi_i\bmod2\quad(0\le j\le d),\\
H=\sum_{i\text{ 奇}}r_i,\qquad
O=\sum_{\substack{1\le j<d\\j\text{ 奇}}}\varepsilon_j,
\qquad E=\sum_{\substack{1\le j<d\\j\text{ 偶}}}\varepsilon_j,
\qquad X=(H,O,E).
\end{gathered}
$$

标量 $E$ 由参数与叶积函数 $E(t)$ 区分。原完整奇偶律为 $\mathsf R_{d,M}$。参考律 $\mathsf Q_{d,M}$ 是全部 $d$ 个 $\operatorname{Bernoulli}(\nu)$ 位条件于 $h\equiv M\pmod2$ 的律。参考树律 $\widetilde U(a,b)$ 使用原同一个核 $K_\xi$：给定完整 $\xi$，令 $s_\xi=(M-h)/2$，在 $\sum_iT_i=s_\xi$ 的非负整数弱组成上均匀取 $T$，置 $r=2T+\xi$，恢复指定方向的叶词并均匀取全部原 Catalan 括号。终端位和末间隔均保留。记

$$
D_W(a,b)=\left\|(W_3)_*U(a,b)-(W_3)_*\widetilde U(a,b)\right\|_{\mathrm{TV}},
\qquad \|P-Q\|_{\mathrm{TV}}=\frac12\sum_x|P(x)-Q(x)|.
$$

**定理 287.2（同一实际核下全部组成的三窗口统一界）。** 存在普适有限常数 $C>0$，使全部整数 $a,b\ge1$ 同时满足

$$
D_W(a,b)\le\min\left\{1,\ C\bigl(\min(a,b)+1\bigr)^{-1/20}\right\}.
\tag{287.1}
$$

$C$ 与组成比例、少数字母方向和端点无关。因此结论包括 $a=b$、比例不收敛、方向任意切换以及 $M/k$ 以任意速度增长的组成族。

证明。以下 $c,C>0$ 可逐式减小或增大，均为绝对常数。所有邻域及大 $d$ 阈值均在
$\delta\in(0,2/3]$ 上统一选定，最后处理小 $d$ 的全部无界 $M$。由 $M\ge d-1$，有

$$
\frac13\le\tau<1,\qquad \frac14\le\nu<\frac12,
\qquad 0<\varrho\le\frac12,\qquad \frac{3}{16}\le v\le\frac14.
\tag{287.2}
$$

第一步，固定原来源、共同核与窗口映射。每个叶词具有相同的 $\operatorname{Cat}_{a+b-1}$ 个有序括号化，所以 $U$ 的间隔律正是总和为 $M$ 的均匀弱组成律，给定间隔后仍保留全部原括号。合法 $h$ 集是

$$
\mathcal H_{d,M}=\{h\in\mathbb Z:0\le h\le\min(d,M),\ h\equiv M\pmod2\}.
$$

若 $M\ge d$，参考正质量向量自动满足 $h\le M$；若 $M=d-1$，唯一可能越界的 $h=d$ 与 $M$ 奇偶相反，已被终端条件排除。因此每个参考正质量纤维都有上述同一个非空 $K_\xi$，包括 $s_\xi=0$。由 (285.3)–(285.5)，在合法向量上

$$
\begin{aligned}
\mathsf R(\xi)&=
\frac{\binom{(M-h)/2+d-1}{d-1}}{\binom{M+d-1}{d-1}},\\
\mathsf Q(\xi)&=\frac{\nu^h(1-\nu)^{d-h}}{p_e},
\qquad p_e=\frac{1+(-1)^M\varrho^d}{2}\ge\frac13.
\end{aligned}
\tag{287.3}
$$

非法向量的真实质量为零。正似然 $u(h)=\mathsf R(\xi)/\mathsf Q(\xi)$ 只依赖 $h$。记 $R_h,Q_h$ 为 $h$ 边缘，$P_R,P_{\widetilde U}$ 为 $(h,X)$ 的联合质量，同一个核给出

$$
U(t)=\mathsf R(\xi(t))K_{\xi(t)}(t),\quad
\widetilde U(t)=\mathsf Q(\xi(t))K_{\xi(t)}(t),\quad
R_h=uQ_h,\quad P_{\widetilde U}(h,X)=\frac{P_R(h,X)}{u(h)}.
\tag{287.4}
$$

这里没有将条件后的间隔或奇偶位说成独立。令 $p=a\bmod2,q=b\bmod2$；沿同一原叶词求和八边增量，直接采用 (283.12)–(283.13)：

$$
\begin{aligned}
Z&=\left(O-E,\frac{M-2H-(-1)^kq}{2},\lfloor k/2\rfloor-O-E\right)
&& (a\le b),\\
Z&=\left(E-O+pq,\lfloor k/2\rfloor-O-E+pq,\frac{M-2H-p}{2}\right)
&& (b<a).
\end{aligned}
\tag{287.5}
$$

母卷引理 359.2 和定理 359.3 的正向归纳给 $W_3=L(Z)R_{pq}$。故在两律的共同实际支撑上，$W_3$ 是同一个 $X$ 的确定函数。按该函数的每个纤维求和再用三角不等式，即有

$$
D_W(a,b)\le D_X:=\frac12\sum_X|P_R^X(X)-P_{\widetilde U}^X(X)|.
\tag{287.6}
$$

这一上界只需正向确定映射。实际叶词仍从 $00$ 出发，满足母卷定理 360.2 的八边非负整数、流量和含 $00$ 的弱连通条件；比较格不替代这些实际条件。

第二步，使用精确几何条件化并保留真实端点。只在辅助计算层独立取
$\mathbb P_{\mathrm{geom}}(r_i=j)=\delta\tau^j$，置 $L=\sum_i r_i$。条件于 $L=M$ 时每个弱组成质量同为 $\delta^d\tau^M$，因而准确回到原 $U$ 的间隔律。辅助层不改变 $\mathsf Q$ 或 $K_\xi$。频率 $\theta=(s,t,z,x,y)$ 配对 $Y=(L,H,h,O,E)$。偶、奇间隔的几何级数给

$$
\begin{aligned}
G_\delta(s,z)&=\frac{\delta}{1-\tau^2e^{2is}}
\begin{pmatrix}1&\tau e^{i(s+z)}\\ \tau e^{i(s+z)}&1\end{pmatrix},
\qquad D(x)=\operatorname{diag}(1,e^{ix}),\\
T_\delta(\theta)&=G_\delta(s,z)D(x)G_\delta(s+t,z)D(y).
\end{aligned}
\tag{287.7}
$$

以 $e_0,e_1$ 为两状态标准列向量，真实端点子概率的特征函数满足

$$
\begin{aligned}
F_d^e(\theta)&=\mathbb E_{\mathrm{geom}}
\left[e^{i\theta\cdot Y}\mathbf1_{\{\varepsilon_d=e\}}\right],\\
F_{2m}^e&=e_0^{\mathsf T}T_\delta^{m-1}G_\delta(s,z)D(x)G_\delta(s+t,z)e_e,\\
F_{2m+1}^e&=e_0^{\mathsf T}T_\delta^mG_\delta(s,z)e_e.
\end{aligned}
\tag{287.8}
$$

这就是 (286.7) 的精确接口：末间隔仍计入 $L,H,h$，末状态不计入 $O,E$。在零频处

$$
T_\delta(0)=P_\nu^2,\qquad
P_\nu=\begin{pmatrix}1-\nu&\nu\\\nu&1-\nu\end{pmatrix},
\qquad \operatorname{spec}T_\delta(0)=\{1,\varrho^2\}.
$$

先确定所有实频率共振。逐项 $|T_\delta|\le P_\nu^2$，后者严格正且随机。若 $T_\delta w=\zeta w$、$|\zeta|=1$，在模最大的坐标作三角比较，严格正性迫使 $|w_0|=|w_1|>0$。每条正概率双间隔路径 $a_0\to b_0\to c_0$ 的相位必须分别满足

$$
e^{i\psi}w_{c_0}=\zeta w_{a_0},\qquad
\psi=s(r_0+r_1)+tr_1+z(\xi_0+\xi_1)+xb_0+yc_0.
$$

任一间隔增加二，得到 $s,s+t\in\pi\mathbb Z$，写 $s=A_0\pi,t=B_0\pi$。状态零的零长度自环给 $\zeta=1$，状态一的零长度自环给 $x+y\equiv0$。比较从零到一的长度对 $(0,1)$、$(1,0)$，得 $x\equiv t$，故 $x=y=B_0\pi$。双奇长度的零到零路径再给 $2s+t+2z+x\equiv0$，所以 $z=C_0\pi$。同余均模 $2\pi$。反向直接代入确认，全部单位模点恰为

$$
\Gamma=\{(A_0\pi,B_0\pi,C_0\pi,B_0\pi,B_0\pi):A_0,B_0,C_0\in\{0,1\}\}.
\tag{287.9}
$$

令 $J=\operatorname{diag}(1,-1)$、$\kappa=(d-1)\bmod2$。逐项代入 (287.7)–(287.8)，得到

$$
T_\delta(\theta+\gamma)=J^{A_0+C_0}T_\delta(\theta)J^{A_0+C_0},\qquad
F_d^e(\theta+\gamma)=(-1)^{(A_0+C_0+\kappa B_0)e}F_d^e(\theta).
\tag{287.10}
$$

原路径上的必要同余是 $L\equiv h\equiv\varepsilon_d$ 及 $H-O-E\equiv\kappa L\pmod2$。后一式由 $H\equiv\sum_{i\text{ 奇}}\xi_i$ 和 $\xi_i=\varepsilon_i\oplus\varepsilon_{i+1}$ 消去内部位得到。因此比较格及其 $L=M$ 截面为

$$
\begin{aligned}
\mathcal L_d&=\{(l,H,h,O,E)\in\mathbb Z^5:l\equiv h,\ H-O-E\equiv\kappa l\pmod2\},\\
\mathcal L_d\cap\{l=M\}&=(M+2\mathbb Z)\times\Lambda_X,\qquad
\Lambda_X=\{(H,O,E)\in\mathbb Z^3:H-O-E\equiv\kappa M\pmod2\}.
\end{aligned}
\tag{287.11}
$$

五维格的指数为四，截面的两个因子各为指数二；$\Lambda_X$ 不依赖 $h$。

第三步，计算全参数缩放有限矩。置

$$
N_o=\lfloor d/2\rfloor,\quad n_e=\lfloor(d-1)/2\rfloor,\quad
\alpha_o=N_o/d,\quad m=d\nu,\quad J_H=H-L/2,
\quad b_d=(M,\alpha_o M,m,N_o/2,n_e/2).
$$

几何级数直接给 $\mathbb Er_i=\tau/\delta$、$\operatorname{Var}(\delta r_i)=\tau$、$\mathbb E\xi_i=\nu$、$\operatorname{Var}\xi_i=\operatorname{Cov}(r_i,\xi_i)=v$。令 $\eta_j=(-1)^{\varepsilon_j}$；独立间隔的乘积给

$$
\mathbb E\eta_j=\varrho^j,\qquad
\mathbb E\eta_i\eta_j=\varrho^{|i-j|},\qquad
\operatorname{Cov}(\eta_i,\eta_j)=\varrho^{|i-j|}-\varrho^{i+j}.
\tag{287.12}
$$

对 $i<j$，把 $(-1)^{\xi_i}=1-2\xi_i$ 从乘积提出，得到
$\operatorname{Cov}(r_i,\eta_j)=\operatorname{Cov}(\xi_i,\eta_j)=-2v\varrho^{j-1}$；$i\ge j$ 时这两协方差为零。由 $J_H$ 的间隔系数均为 $\pm1/2$，准确有

$$
\begin{gathered}
\operatorname{Var}(\delta L)=d\tau,\quad
\operatorname{Var}h=dv,\quad \operatorname{Cov}(\delta L,h)=d\delta v,
\quad \operatorname{Var}(\delta J_H)=d\tau/4,\\
\operatorname{Cov}(\delta L,\delta J_H)=\tau(N_o-d/2),\qquad
\operatorname{Cov}(h,\delta J_H)=\delta v(N_o-d/2).
\end{gathered}
\tag{287.13}
$$

后两项缩放后才统一为 $O(1)$。长量与占据量的其余交叉项由 $\sum_{j\ge1}j\varrho^{j-1}\le4$ 控制。记 $I_o,I_e$ 为内部奇、偶位置集；从 $O-N_o/2=-\frac12\sum_{j\in I_o}\eta_j$ 及相应 $E$ 式，得到完整有限和

$$
\begin{aligned}
\operatorname{Var}O&=\frac14\left[N_o+2\sum_{j=1}^{N_o-1}(N_o-j)\varrho^{2j}
-\left(\sum_{i\in I_o}\varrho^i\right)^2\right],\\
\operatorname{Var}E&=\frac14\left[n_e+2\sum_{j=1}^{n_e-1}(n_e-j)\varrho^{2j}
-\left(\sum_{i\in I_e}\varrho^i\right)^2\right],\\
\operatorname{Cov}(O,E)&=\frac14\left[
\sum_{\substack{1\le j<d-1\\j\text{ 奇}}}(d-1-j)\varrho^j
-\left(\sum_{i\in I_o}\varrho^i\right)\left(\sum_{i\in I_e}\varrho^i\right)\right].
\end{aligned}
\tag{287.14}
$$

空和取零。把有限和换成无限几何和时，线性权重误差由 $\sum j\varrho^j$、$\sum j\varrho^{2j}$ 控制；截断尾乘 $d$ 仍有统一界，因为 $d(1/2)^d$ 有界。$|N_o-d/2|\le1/2$、$|n_e-d/2|\le1$，均值偏置也由 $\sum\varrho^j$ 控制。于是缩放坐标 $(\delta L,h,\delta J_H,O,E)$ 的均值与由 $b_d$ 变换所得中心相差统一 $O(1)$，协方差为

$$
d\operatorname{diag}(\bar A_\delta,\bar C_\delta)+E_d,
\qquad \|E_d\|\le C,
\tag{287.15}
$$

其中

$$
\begin{gathered}
\bar A_\delta=\begin{pmatrix}\tau&\delta v\\\delta v&v\end{pmatrix},\qquad
\bar C_\delta=(\tau/4)\oplus V_\delta,\\
V_\delta=\begin{pmatrix}
(1+\varrho^2)/(8\chi)&\varrho/(4\chi)\\
\varrho/(4\chi)&(1+\varrho^2)/(8\chi)
\end{pmatrix}.
\end{gathered}
$$

$\det\bar A_\delta=\tau v\chi\ge3/64$、$\operatorname{tr}\bar A_\delta\le5/4$。$\bar C_\delta$ 的特征值是 $\tau/4$、$(1+\varrho)/(8(1-\varrho))$、$(1-\varrho)/(8(1+\varrho))$，均在 $[1/24,3/8]$。所以两矩阵具有共同正的上下谱界。原顺序 $(\delta L,\delta H,h,O,E)$ 的主协方差为

$$
\bar\Sigma_\delta=
\begin{pmatrix}
\tau&\tau/2&\delta v&0&0\\
\tau/2&\tau/2&\delta v/2&0&0\\
\delta v&\delta v/2&v&0&0\\
0&0&0&(1+\varrho^2)/(8\chi)&\varrho/(4\chi)\\
0&0&0&\varrho/(4\chi)&(1+\varrho^2)/(8\chi)
\end{pmatrix}.
\tag{287.16}
$$

固定剪切 $(l,H,h,O,E)\mapsto(l,h,H-l/2,O,E)$ 的行列式绝对值为一，将它化为 $\operatorname{diag}(\bar A_\delta,\bar C_\delta)$，故也具有共同正定界。有限协方差中的 $E_d$ 没有被置零。

第四步，建立 $\delta=0$ 的共同解析域及局部谱余项。在零共振处令
$s=\delta\sigma,t=\delta\omega$、$\psi=(\sigma,\omega,z,x,y)$、$D_\delta=\operatorname{diag}(\delta,\delta,1,1,1)$。正确的有限延拓对象是
$\bar G_\delta(\sigma,z)=G_\delta(\delta\sigma,z)$ 本身。将其分母除以 $\delta$，写成

$$
Q_\delta(\sigma)=1+\tau+\tau^2\frac{1-e^{2i\delta\sigma}}{\delta},\qquad
Q_0(\sigma)=2-2i\sigma,
\qquad
\bar G_0(\sigma,z)=\frac1{2(1-i\sigma)}
\begin{pmatrix}1&e^{iz}\\e^{iz}&1\end{pmatrix}.
\tag{287.17}
$$

差商的幂级数在 $\delta=0$ 可去。对复 $|\sigma|\le R$，由 $|e^w-1|\le|w|e^{|w|}$ 有
$|Q_\delta(\sigma)-(1+\tau)|\le2Re^{4R/3}$；第二长度 $|\sigma+\omega|\le2R$ 时，界为 $4Re^{8R/3}$。先取绝对小 $R$ 使后一界小于 $1/3$，而 $1+\tau\ge4/3$，两个分母就在同一复多圆盘内共同离零。矩阵与真实边界因子因此一致有界且解析，包括 $\delta=0$。这里只延拓符号族，不定义新的树概率源。

零频的判别式 $\Delta=(\operatorname{tr}T)^2-4\det T$ 满足 $\Delta(0)=(1-\varrho^2)^2\ge9/16$。上述共同界使 $\Delta(\psi)-\Delta(0)=O(\|\psi\|)$，故可统一缩小复盘，使 $\operatorname{Re}\Delta>0$。取零点为正的平方根，定义

$$
\lambda=\frac{\operatorname{tr}T+\sqrt\Delta}{2},\qquad
\lambda_2=\frac{\operatorname{tr}T-\sqrt\Delta}{2},\qquad
\Pi=\frac{T-\lambda_2I}{\lambda-\lambda_2}.
$$

再缩盘使 $|\lambda-1|\le1/8$、$|\lambda_2|\le3/8$、$|\lambda-\lambda_2|\ge1/2$。$\log\lambda$ 取零点值零的解析支，$\Pi$ 与边界振幅也共同解析。若较大盘上的界为 $B_0$，多变量 Cauchy 公式在其内半盘给
$|\partial^\beta f|\le\beta!(2/R)^{|\beta|}B_0$，特别给出统一三阶 Taylor 余项。

二次系数由有限矩确定。固定任意 $\delta>0$，取奇数间隔数 $d'=2m'+1$ 的同一辅助模型并对两个端点求和，其精确谱分解是 $\lambda^{m'}A_o+\lambda_2^{m'}B_o$，$A_o(0)=1$。振幅导数统一有界，次谱项零点前两阶导数至多 $C(1+m'^2)(3/8)^{m'-2}$。特征函数对数在零点的一、二阶导数分别是 $i$ 乘实际均值和实际协方差的负值。把 (287.12)–(287.16) 的有限矩除以 $m'$，再令 $m'\to\infty$，就得到

$$
\log\lambda(\psi)=i\beta_2\cdot\psi
-\psi^{\mathsf T}\bar\Sigma_\delta\psi+O(\|\psi\|^3),
\qquad \beta_2=(2\tau,\tau,2\nu,1/2,1/2).
\tag{287.18}
$$

求导只在未条件化辅助模型内进行，其长度均值 $d'\tau/\delta$ 不要求是整数。共同解析连续性将系数恒等式延到 $\delta=0$，没有用中心极限定理反推导数。

两类端点的主振幅分别为
$e_0^{\mathsf T}\Pi\bar G_\delta e_e$ 和
$e_0^{\mathsf T}\Pi\bar G_\delta D(x)\bar G_\delta(\sigma+\omega,z)e_e$，在零点均为 $1/2$，偏差为 $O(\|\psi\|)$。准确有限端点质量仍为 $[1+(-1)^e\varrho^d]/2$。置
$\widehat b_d=D_\delta b_d=(d\tau,N_o\tau,d\nu,N_o/2,n_e/2)$；这一中心在 $\delta=0$ 有有限延拓。奇数 $d$ 时主幂数 $n=(d-1)/2$，$n\beta_2-\widehat b_d=(-\tau,0,-\nu,0,0)$；偶数时 $n=(d-2)/2$，差为 $(-2\tau,-\tau,-2\nu,-1/2,0)$。这些偏移和 $|n-d/2|$ 均统一有界。

利用共同正定性，选共同小实半径 $r_0$，使三阶余项不超过二次衰减的一半。用
$e^U-e^V=(U-V)\int_0^1e^{(1-t)V+tU}\,dt$，先比较 $n\log\lambda$ 与其二次 Taylor 多项式，再支付上述中心和主幂修正。振幅误差贡献 $O(\|\psi\|)$，二次修正 $O(\|\psi\|^2)$ 可在小球内吸入一次项，三阶误差贡献 $O(d\|\psi\|^3)$。于是对充分大 $d$，两端点和两种 $d$ 奇偶同时有

$$
\left|F_d^e(D_\delta\psi)-\frac12
e^{i\widehat b_d\cdot\psi-d\psi^{\mathsf T}\bar\Sigma_\delta\psi/2}\right|
\le C(\|\psi\|+d\|\psi\|^3)e^{-cd\|\psi\|^2}+Cq_0^d,
\quad \|\psi\|\le r_0,
\quad q_0<1.
\tag{287.19}
$$

端点和有限协方差修正均已进入该误差；并未将有限实际协方差当作精确块对角矩阵。

第五步，完整处理远频，保留两个长度方向的 $\delta^2$ 体积。实频率上由 (287.7) 的绝对行和

$$
\|G_\delta(s,z)\|_\infty\le\gamma_\tau(s)
:=\frac{1-\tau^2}{|1-\tau^2e^{2is}|}
=\left[1+\frac{4\tau^2\sin^2s}{\delta^2(1+\tau)^2}\right]^{-1/2}.
\tag{287.20}
$$

令 $u$ 为 $s$ 到 $\pi\mathbb Z$ 的代表，$|u|\le\pi/2$。$|\sin u|\ge2|u|/\pi$ 及 $\tau\ge1/3$ 给
$\gamma_\tau(s)\le[1+u^2/(\pi^2\delta^2)]^{-1/2}$。对 $n\ge8$ 换元 $u=\delta w$：$|w|\le1$ 时 $\log(1+w^2/\pi^2)\ge c w^2$，积分至多 $C/\sqrt n$；$|w|>1$ 时拆出一个指数衰减因子，保留可积的 $(1+w^2/\pi^2)^{-2}$。故

$$
I_n:=\int_{\mathbb T}\gamma_\tau(s)^n\,ds\le C\frac{\delta}{\sqrt n}.
$$

任意预先固定 $\epsilon>0$ 和充分大 $n$，在 $|u|>\epsilon\delta$ 上将幂拆成两半，一半至多 $(1+\epsilon^2/\pi^2)^{-n/4}$，另一半的完整积分是 $I_{n/2}$，因此

$$
J_n:=\int_{\operatorname{dist}(s,\pi\mathbb Z)>\epsilon\delta}
\gamma_\tau(s)^n\,ds\le C\delta e^{-c_\epsilon n}.
\tag{287.21}
$$

尾积分自身包含 $\delta$。由精确端点式，
$|F_d^e|\le\gamma_\tau(s)^{\lceil d/2\rceil}\gamma_\tau(s+t)^{\lfloor d/2\rfloor}$。完整环面的整数幺模换元 $(s,t)\mapsto(s,s+t)$ 保持测度。在至少一个长度角到 $\pi\mathbb Z$ 的距离超过 $\epsilon\delta$ 的区域，积分至多
$J_{\lceil d/2\rceil}I_{\lfloor d/2\rfloor}+I_{\lceil d/2\rceil}J_{\lfloor d/2\rfloor}$；其余三个频率的环面体积固定。因此该区五维积分不超过 $C\delta^2e^{-cd}$，也覆盖两个长度角同时出盒的部分。

剩余两个长度角均在短盒内，须同时检查 $\delta=0$ 的谱。四个长度 $0/\pi$ 分支由 (287.10) 平移到基础分支；写 $s=\delta\sigma,s+t=\delta(\sigma+\omega)$，两个标准化长角有固定界。实 $\sigma$ 上 $|Q_\delta(\sigma)|=|1-\tau^2e^{2i\delta\sigma}|/\delta\ge1+\tau$，而 $|Q_0(\sigma)|\ge2$，故 (287.17) 在整个有界实盒上连续且有界，不只在局部复盘内有效。若 $\delta=0$ 且 $\sigma$ 或 $\sigma+\omega$ 非零，两个 $\bar G_0$ 的绝对行和分别为 $(1+\sigma^2)^{-1/2}$ 和 $(1+(\sigma+\omega)^2)^{-1/2}$，乘积严格小于一，完整矩阵的谱半径也严格小于一。若两者均零，令 $a_0=e^{iz},b_0=e^{ix},c_0=e^{iy}$，显式有

$$
\bar T_0=\frac14
\begin{pmatrix}1+a_0^2b_0&c_0a_0(1+b_0)\\
a_0(1+b_0)&c_0(a_0^2+b_0)\end{pmatrix}.
\tag{287.22}
$$

各项绝对值至多 $1/2$。$b_0\ne1$ 时两个行和都因 $|1+b_0|<2$ 而严格小于一；$b_0=1,a_0^2\ne1$ 时也严格小于一。余下 $b_0=1,a_0^2=1$ 时矩阵秩至多一，唯一可能非零特征值为 $(1+c_0)/2$，仅在 $c_0=1$ 时模为一。故基础分支只有 $z=0$ 或 $\pi$、$x=y=0$ 的共振；结合四个长度分支，正好恢复 (287.9) 的八点，没有新增边界共振。

选固定 $0<\epsilon<1/10$ 并把 $r_0$ 再缩小，使八个缩放局部球互不相交且在上述短盒内。去掉这些球后，$\delta\in[0,2/3]$、有界标准化长角与短频率环面组成紧集。刚才的边界分类与 $\delta>0$ 的完整分类已逐点排除单位模，故该集的最大谱半径 $q_*<1$。取 $q_f\in(q_*,1)$，圆 $|w|=q_f$ 上
$|\det(wI-\bar T_\delta)|\ge(q_f-q_*)^2$，伴随矩阵也一致有界，于是预解式一致有界。矩阵 Cauchy 公式

$$
\bar T_\delta^n=\frac1{2\pi i}
\int_{|w|=q_f}w^n(wI-\bar T_\delta)^{-1}\,dw
$$

给 $\|\bar T_\delta^n\|\le Cq_f^n$，包括重根和不可对角化点。真实边界因子有界，而短盒的两个物理长度角面积为 $O(\delta^2)$，所以该区完整积分也至多 $C\delta^2e^{-cd}$。此证明始终使用保留长度标量的完整 $T_\delta$；盒外由标量积分负责，盒内才使用谱隙。全远频误差没有丢失 $\delta^2$。

第六步，作五维和二维全格反演。对正定 $j$ 维矩阵 $V$，记
$\phi_V(x)=(2\pi)^{-j/2}(\det V)^{-1/2}e^{-x^{\mathsf T}V^{-1}x/2}$。五维整数反演为

$$
\mathbb P_{\mathrm{geom}}(Y=y,\varepsilon_d=e)
=(2\pi)^{-5}\int_{\mathbb T^5}e^{-i\theta\cdot y}F_d^e(\theta)\,d\theta.
$$

每个局部球换元 $\theta=\gamma+D_\delta\psi$ 的 Jacobian 是 $\delta^2$。由 (287.19)，一次振幅和三次余项的积分分别为

$$
\delta^2\int_{\mathbb R^5}\|\psi\|e^{-cd\|\psi\|^2}\,d\psi
=O(\delta^2d^{-3}),\qquad
\delta^2d\int_{\mathbb R^5}\|\psi\|^3e^{-cd\|\psi\|^2}\,d\psi
=O(\delta^2d^{-3}).
\tag{287.23}
$$

这里用 $\psi=w/\sqrt d$ 直接得到积分阶数。局部次谱积分、延长高斯积分到全空间的误差及第五步的全远频均至多 $C\delta^2e^{-cd}$。反演中的目标相位模为一，故误差对全部整数 $y$ 一致。正定高斯的 Fourier 积分经正交对角化及各轴一维高斯积分，给主项 $\delta^2d^{-5/2}\phi_{\bar\Sigma_\delta}(D_\delta(y-b_d)/\sqrt d)$，再乘端点振幅和中心相位和。该相位和准确为

$$
\sum_{A_0,B_0,C_0\in\{0,1\}}
(-1)^{A_0(l-e)+C_0(h-e)+B_0(H+O+E-\kappa e)}
=8\mathbf1_{\{l\equiv h\equiv e,\ H-O-E\equiv\kappa e\ (2)\}}.
$$

乘主振幅 $1/2$ 得因子四；$l$ 决定唯一端点。因此对所有 $y\in\mathcal L_d$，

$$
\mathbb P_{\mathrm{geom}}(Y=y)
=4\delta^2d^{-5/2}\phi_{\bar\Sigma_\delta}
\left(\frac{D_\delta(y-b_d)}{\sqrt d}\right)
+O(\delta^2d^{-3}).
\tag{287.24}
$$

格外真实质量与比较项取零。格内若八边非负或弱 Euler 条件失败，真实质量仍为零，比较密度却不擅自改零；同一个全格绝对误差已经支付其差。这里没有假设所有中央同余格点都可实现，也没有要求罕见纤维的相对误差。

二维 $(L,h)$ 的单间隔函数是

$$
f_2(s,z)=\frac{\delta(1+\tau e^{i(s+z)})}{1-\tau^2e^{2is}}.
$$

长度零、一、二的相位等号迫使 $s\in\pi\mathbb Z$、$s+z\equiv0\pmod{2\pi}$，所以仅有 $(0,0),(\pi,\pi)$ 两个共振，比较格是 $l\equiv h\pmod2$。零点缩放 $s=\delta\sigma$ 的共同解析分母仍是 (287.17)，且 $f_2(0,0)=1$。用该共同解析界缩小同一个复盘，使 $|f_2-1|\le1/2$，于是零点值为零的 $\log f_2$ 解析，其三阶导数及余项由 Cauchy 公式统一控制。其对数展开由单间隔矩准确给出

$$
\log f_2(\delta\sigma,z)
=i(\tau\sigma+\nu z)
-\frac12(\sigma,z)\bar A_\delta(\sigma,z)^{\mathsf T}
+O(\|(\sigma,z)\|^3).
$$

在 $\delta=0$ 基础分支，函数为 $(1+e^{iz})/[2(1-i\sigma)]$，模为一仅在 $\sigma=z=0$；另一分支经 $(\pi,\pi)$ 平移得到。在长度盒外，$|f_2|\le\gamma_\tau(s)$ 给积分 $C\delta e^{-cd}$；盒内去共振后，由已经完成的边界分类及紧集取得统一严格模界。共同正定的 $\bar A_\delta$ 和三阶余项给局部高斯衰减，指数差积分式将 $f_2^d$ 与其二次主项的差界为 $Cd\|\psi\|^3e^{-cd\|\psi\|^2}$。该误差的二维积分是
$\delta d\int_{\mathbb R^2}\|\psi\|^3e^{-cd\|\psi\|^2}\,d\psi=O(\delta d^{-3/2})$。精确平移 $f_2(s+\pi,z+\pi)=f_2(s,z)$ 给两中心相位和 $1+(-1)^{l+h}=2\mathbf1_{\{l\equiv h\ (2)\}}$，故全部 $l\equiv h\pmod2$ 的整数点同时满足

$$
N_2(l,h):=\mathbb P_{\mathrm{geom}}(L=l,h)
=2\delta d^{-1}\phi_{\bar A_\delta}
\left(\frac{\delta(l-M)}{\sqrt d},\frac{h-m}{\sqrt d}\right)
+O(\delta d^{-3/2}).
\tag{287.25}
$$

二维误差同样是全格绝对误差，格外取零。以上 $\phi$ 只是离散格点上的比较函数，不是将离散概率律与连续高斯律作总变差比较。

第七步，先抵消分子，再一次除同一个精确分母。令 $N=M+d$；总长度事件的真实概率为

$$
p_L=\mathbb P_{\mathrm{geom}}(L=M)
=\binom{M+d-1}{d-1}\delta^d\tau^M
=\delta\binom Nd\left(\frac dN\right)^d\left(\frac MN\right)^M.
\tag{287.26}
$$

复用 (283.9)–(283.10) 的阶乘供应。具体地，钉版 Stirling 序列
$a_n=n!/[\sqrt{2n}(n/e)^n]$ 对正整数反单调，$a_1=e/\sqrt2$，且 $a_n\ge\sqrt\pi$。因此全部正整数 $n$ 上

$$
\sqrt{2\pi n}(n/e)^n\le n!\le e\sqrt n(n/e)^n.
$$

在 (287.26) 中对 $N!$ 用下界、对 $d!,M!$ 用上界；$N=d+M$ 使全部幂和指数精确相消。$M,d,N$ 均为正整数，故

$$
p_L\ge\frac{\sqrt{2\pi}}{e^2}\delta\sqrt{\frac N{dM}}
\ge c\frac{\delta}{\sqrt d}.
\tag{287.27}
$$

该下界对任意小 $\delta$ 成立，不需要一维局部极限定理或分母倒数展开。

在 $L=M$ 截面上置

$$
x_h=\frac{h-m}{\sqrt d},\qquad
x_X=\frac{(\delta(H-\alpha_o M),\ O-N_o/2,\ E-n_e/2)}{\sqrt d},
\qquad
g_{\delta,d}(X)=2\delta d^{-3/2}\phi_{\bar C_\delta}(x_X)
\quad(X\in\Lambda_X),
\tag{287.28}
$$

格外 $g_{\delta,d}=0$，后文简记为 $g$。共同正定性给 $\sup g\le C\delta d^{-3/2}$。由 (287.16) 的行列式绝对值一剪切，在第一个中心坐标为零时，高斯密度准确分解为

$$
\phi_{\bar\Sigma_\delta}(0,x_H,x_h,x_O,x_E)
=\phi_{\bar A_\delta}(0,x_h)\phi_{\bar C_\delta}(x_X).
$$

令 $N_5(h,X)=\mathbb P_{\mathrm{geom}}(L=M,h,X)$。五维主项与 $N_2(M,h)g(X)$ 的主项完全相同，都是
$4\delta^2d^{-5/2}\phi_{\bar A_\delta}(0,x_h)\phi_{\bar C_\delta}(x_X)$。五维误差为 $O(\delta^2d^{-3})$，二维误差乘 $\sup g$ 也是此阶。先在分子层面相减，得到

$$
\sup_{\substack{h\in M+2\mathbb Z\\X\in\Lambda_X}}
|N_5(h,X)-N_2(M,h)g(X)|\le C\delta^2d^{-3}.
$$

仅除同一个精确 $p_L$ 一次，由 (287.27) 得到本证明的联合估计

$$
\sup_{\substack{h\in M+2\mathbb Z\\X\in\Lambda_X}}
|\mathcal E_d(h,X)|\le C\delta d^{-5/2},\qquad
\mathcal E_d(h,X)=P_R(h,X)-R_h(h)g(X).
\tag{287.29}
$$

非法 $h$ 的真实边缘与联合质量零延拓，实际 Euler 零点仍保留；从不在非法 $h$ 上求逆似然。该关系来自全参数反演与精确共同分母，不由零交叉协方差推断真实独立。

第八步，控制原同核似然和中央逆界。以下只在 $d\ge16$ 使用。由 (287.3) 的乘积展开与归一化，令

$$
\ell(x)=\sum_{j=1}^{d-1}\log(M-x+2j)-x\log\tau,\qquad
c_\ell=\mathbb E_Q e^{\ell(h)-\ell(m)},\qquad
u(h)=\frac{e^{\ell(h)-\ell(m)}}{c_\ell}.
$$

$0\le x\le d$ 上全部对数参数至少为一。写
$A_m=M-m=2M^2/(2M+d)$，则 $A_m+2d=2(M+d)^2/(2M+d)$，且
$\int_0^d(A_m+2y)^{-1}dy=-\log\tau$。递减函数的完整离散和满足

$$
\int_1^d\frac{dy}{A_m+2y}
\le\sum_{j=1}^{d-1}\frac1{A_m+2j}
\le\int_0^{d-1}\frac{dy}{A_m+2y}.
$$

所以 $0\le\ell'(m)\le1/A_m\le3/d$；最后一步在最小 $M=d-1$、$d\ge3$ 核对后由 $A_m$ 随 $M$ 增加得到。凹性给全部合法 $h$ 上 $\ell(h)-\ell(m)\le3$。在 $|x-m|\le d/4$ 的线段上，$m<d/2$、$M\ge d-1$ 使每个分母至少 $d/4$，从而 $-\ell''(x)\le16/d$。Taylor 积分式给

$$
\ell(h)-\ell(m)\ge-3|h-m|/d-8(h-m)^2/d
\quad(|h-m|\le d/4).
\tag{287.30}
$$

未条件 Bernoulli 总和中心平方矩为 $dv\le d/4$，对非负平方付终端代价 $p_e^{-1}\le3$ 后有 $\mathbb E_Q(h-m)^2\le3d/4$。Chebyshev 给 $Q\{|h-m|\le\sqrt d\}\ge1/4$；$d\ge16$ 时此窗在 (287.30) 内，指数差至少 $-11$。因此

$$
e^{-11}/4\le c_\ell\le e^3,\qquad
u(h)\le U_+:=4e^{14}\quad(h\in\mathcal H_{d,M}),
\qquad
\frac1{u(h)}\le e^{15/4+8r^2}\quad(|h-m|\le r\sqrt d\le d/4).
\tag{287.31}
$$

最后的逆界仅限中央窗。对一个未条件中心化 Bernoulli 位，倾斜对数矩母函数 $K_B$ 满足 $K_B(0)=K_B'(0)=0$，二阶导数是倾斜 Bernoulli 方差，至多 $1/4$。两次积分给 $K_B(\lambda)\le\lambda^2/8$，包括负 $\lambda$。独立总和的指数 Markov 界取 $\lambda=\pm4r/\sqrt d$，得未条件双尾 $2e^{-2r^2}$。再付真实终端代价并用 $R_h=uQ_h$，得到

$$
Q_h\{|h-m|>r\sqrt d\}\le6e^{-2r^2},\qquad
R_h\{|h-m|>r\sqrt d\}\le6U_+e^{-2r^2}.
\tag{287.32}
$$

$m$ 只是未条件比较中心，不被认作条件后的精确均值。

第九步，控制比较格和及同一 $K_\xi$ 的真实各向异性尾。由共同正定性，
$g(X)\le C\delta d^{-3/2}e^{-c\|x_X\|_2^2}$。对于任意平移的单峰高斯，按中心两侧积分比较，一维格距 $h_0$ 的和至多 $2+C/h_0$。$H$ 轴格距是 $\delta/\sqrt d$，$O,E$ 轴格距是 $1/\sqrt d$。放大到全部整数三格只增加非负和，三个因子与前系数配平。再用 $te^{-ct}\le Ce^{-ct/2}$，得

$$
\sum_Xg(X)\le C,\qquad
\sum_Xg(X)\|x_X\|_2^2\le C,
\qquad \sum_{\|x_X\|_\infty>B}g(X)\le CB^{-2}.
\tag{287.33}
$$

$g$ 无须精确归一化。真实参考奇偶层由 (287.12) 给占据量的未条件中心平方矩：对 $N\in\{N_o,n_e\}$，它是
$\frac14[N+2\sum_{j=1}^{N-1}(N-j)\varrho^{2j}]\le5N/12$。该中心平方已经包含初态偏置。对非负平方付 $p_e^{-1}\le3$ 后

$$
\mathbb E_Q[(O-N_o/2)^2+(E-n_e/2)^2]\le5(d-1)/4.
$$

给定同一个完整 $\xi$，置 $h_o=\sum_{i\text{ 奇}}\xi_i$、$h_c=h_o-\alpha_o h$、$K_o=\sum_{i\text{ 奇}}T_i$。直接使用 (285.16) 的同核分组，或对
$(1-tz)^{-N_o}(1-z)^{-(d-N_o)}$ 分别求一次、二次 $t$ 导数并在 $t=1$ 取 $z^{s_\xi}$ 系数，除以 $\binom{s_\xi+d-1}{d-1}$，得

$$
\mathbb E(K_o\mid\xi)=\frac{N_os_\xi}{d},\qquad
\mathbb E(K_o(K_o-1)\mid\xi)=\frac{N_o(N_o+1)s_\xi(s_\xi-1)}{d(d+1)}.
$$

两组大小均正，$s_\xi=0$ 时两矩都为零。用 $H=2K_o+h_o$ 相减，得到

$$
\mathbb E(H\mid\xi)=\alpha_o M+h_c,\qquad
\operatorname{Var}(H\mid\xi)=
\frac{4s_\xi\alpha_o(1-\alpha_o)(s_\xi+d)}{d+1}.
\tag{287.34}
$$

终端条件只依赖 $h$，所以 $Q$ 位仍可交换。令 $b_i=\mathbf1_{\{i\text{ 奇}\}}-\alpha_o$，则 $\sum b_i=0$、$\sum b_i^2=N_o(d-N_o)/d\le d/4$。设 $q_1=\mathbb E_Q\xi_0,q_2=\mathbb E_Q\xi_0\xi_1$，完整展开给
$\mathbb E_Qh_c=0$、$\mathbb E_Qh_c^2=(\sum b_i^2)(q_1-q_2)\le d/8$，因为 $q_1-q_2=\mathbb E_Q(\xi_0-\xi_1)^2/2\le1/2$。未假定条件位独立。

在同一核中按条件均值分解平方，交叉项条件期望为零。用 $s_\xi\le M/2$、$\alpha_o(1-\alpha_o)\le1/4$、$\delta M=d\tau$，得

$$
\begin{aligned}
\mathbb E_{\widetilde U}[\delta^2(H-\alpha_o M)^2]
&\le\frac{\delta^2M(M+2d)}{4(d+1)}+\frac{\delta^2d}{8}\\
&=\frac d4-\frac{d}{4(d+1)}+
\frac{\delta^2d(1-d)}{8(d+1)}\le\frac d4.
\end{aligned}
\tag{287.35}
$$

结合占据量平方矩，有 $\mathbb E_{\widetilde U}\|x_X\|_2^2\le3/2$。对同一非负函数使用同核密度 $u\le U_+$，又有 $\mathbb E_U\|x_X\|_2^2\le3U_+/2$。Markov 不等式因此给两种真实 $X$ 律的 $\|x_X\|_\infty>B$ 尾均至多 $CB^{-2}$。所有平方在同一个 $\xi,T$、叶词和原括号实现上相加，没有拼接不同实现的边缘最优值。

第十步，在每个相同窗口纤维内先抵消再取绝对值。只在有限合法 $\mathcal H_{d,M}$ 上置 $a(h)=1-1/u(h)$。归一化准确给
$\sum_h a(h)R_h(h)=\sum_h(R_h(h)-Q_h(h))=0$。故对每个相同 $X$，由 (287.4)、(287.29) 有

$$
P_R^X(X)-P_{\widetilde U}^X(X)
=\sum_{h\in\mathcal H_{d,M}}a(h)\mathcal E_d(h,X).
\tag{287.36}
$$

取 $r^2=(\log d)/40$、$B=d^{1/40}$。选一个绝对 $d_0$，使 $d\ge d_0$ 时前述全部反演阈值、$d\ge16$、$r\ge1$、$r\sqrt d\le d/4$ 同时成立。中央 $h$ 点数至多 $Cr\sqrt d$；$\|x_X\|_\infty\le B$ 的整数 $X$ 点数至多 $CB^3d^{3/2}/\delta$；中央逆界给 $|a(h)|\le Cd^{1/5}$。用 (287.29)，中央绝对和不超过

$$
C(r\sqrt d)\left(\frac{B^3d^{3/2}}{\delta}\right)
d^{1/5}(\delta d^{-5/2})
=CrB^3d^{-3/10}
\le C\sqrt{\log d}\,d^{-9/40}.
$$

$\delta$ 与实际 $H$ 长轴格点数中的 $\delta^{-1}$ 精确抵消。补集不能用全格单点误差乘无限点数。由非负性和同核恒等式，逐点有

$$
|a(h)\mathcal E_d(h,X)|
\le P_R(h,X)+P_{\widetilde U}(h,X)
+(R_h(h)+Q_h(h))g(X).
\tag{287.37}
$$

在 $h$ 尾上先求全部 $X$ 和，前两项成为真实 $R_h,Q_h$ 尾，最后一项是这两尾乘 $\sum g$；由 (287.32)–(287.33) 得 $Ce^{-2r^2}$。在 $X$ 尾上先求全部合法 $h$ 和，前两项成为第九步的两种真实 $X$ 尾，最后一项是 $2\sum_{X\text{ 尾}}g(X)$，得 $CB^{-2}$。两个尾的并集由两者之和覆盖，亦保留全部实际零支撑点。代入所选增长窗，两尾均为 $Cd^{-1/20}$。由 (287.6)、(287.36) 得

$$
2D_X\le C\left[\sqrt{\log d}\,d^{-9/40}+d^{-1/20}\right]
\le C'd^{-1/20},\qquad D_W\le D_X.
$$

全部常数和 $d_0$ 在 $\delta\in[0,2/3]$ 的解析闭包上统一选定。对 $2\le d<d_0$ 的全部 $M\ge d-1$，包括无界 $M$，直接用 $D_W\le1$，并一次增大 $C$ 至至少 $d_0^{1/20}$。再与概率律的 TV 至多一合并，证明 (287.1)。两种 $d$ 奇偶、实际端点、$M=d-1$、零剩余量、小 $d$ 协方差退化、$a=b$ 和两个方向均已包含；方向只在 (287.5) 的原确定映射处改变，所有原括号在共同核内完整保留。$\square$

数学来源附于定理 287.2。原树、均匀弱组成、完整终端奇偶、同一 $K_\xi$、两方向坐标及分组矩采用本卷 §§283、285；精确端点生成式与有限矩接口采用 §286，并在本证明中给出 $\delta\to0$ 的共同解析域、完整共振和全格余项。实际窗口的正向关系及八边／弱 Euler 支撑采用[母卷](FIBONACCI_ATOMIC_RELATION_GENERATION.md) §§359–360。确定通道的 TV 收缩是既有 [DataProcessing](../../../D5/S3/TotalVariation/DataProcessing.lean) 的 `total_variation_channel_le`；本证明只将它用于同一实际 $X$ 到 $W_3$ 的映射。

精确分母只使用钉版 mathlib [Stirling 源码](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/Stirling.lean) 中 `Stirling.le_factorial_stirling`、`Stirling.stirlingSeq'_antitone`、`Stirling.stirlingSeq_one` 的正整数阶乘界；$N,d,M$ 全部满足其条件。Cauchy 公式、有限维谱投影、高斯 Fourier 积分与指数 Markov 不等式作为成熟中间工具使用，必要的系数、相位、积分尺度和尾界均在证明内展开。全 $\delta$ 联合余项 (287.29) 及其原同核有符号消费是本仓推导；不作全球优先权或指数最优性断言。

在原素数 $r\ge7$、$V=F_r$、连续区间和低 $J$ 定位条件下，同一 $`N^*=1+Vg^*`$ 上保留完整素幂和所有除数的严格预算 $`C^*+H^*<(\log\log N^*/\log\log A)^s`$，$s=\log A\,\log\log A$，仍未决；本定理不提供该算术联合估计，$V$ 不假定为素数。

## 追加锚（本行以下为增补区）
