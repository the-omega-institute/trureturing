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
