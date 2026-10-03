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
