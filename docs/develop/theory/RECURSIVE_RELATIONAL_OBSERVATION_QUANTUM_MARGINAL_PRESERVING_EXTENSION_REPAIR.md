# Recursive relational observation: marginal-preserving extension repair

## 1. Original histories, scalar ports and the common Choi slice

**Assumption 1.1 (The unchanged five-mode preparation).** Let
$\mathcal H=\mathbb C^5$, with ordered orthonormal basis
$\mathsf S=(N,2,3,5,25)$ and $\Pi_s=e_se_s^\dagger$. Allow every
complex density input. Fix exactly

$$
K=\begin{pmatrix}
0&1&1&1&0\\
1&0&0&0&1\\
1&0&0&0&0\\
1&0&0&0&1\\
0&1&0&1&0
\end{pmatrix},\qquad U(t)=e^{-itK},\quad t\ge0.
\tag{1.1}
$$

The future menu consists of nonnegative waits, the complete five-outcome
rank-one Lüders instrument $X\mapsto(\Pi_sX\Pi_s)_s$, and Stop.
Every finite adaptive depth is included. Histories retain outcomes,
controls and stops; the two comparisons use the same policy and the
same source-independent random-control law. Grouping recorded outcomes
is classical postprocessing of the complete read. Independent mode
phases, arbitrary future unitaries, source copies, resets, probability
oracles, readable hidden Kraus records, external quantum side information
and coarse-block Lüders instruments are absent. This is QMB Assumption
1.1 and its actual menu. Quantum preparation is an independent hypothesis;
the native $\alpha/\beta$ composition source supplies no preparation
map in this assumption.

**Definition 1.2 (Fixed scalar ports and actual-history error).** Let
$\mathfrak C_1$ be the class of all composites of fixed CPTP maps

$$
\operatorname{Enc}:M_5\longrightarrow\bigoplus_{f\in F}M_1,
\qquad
\operatorname{Dec}((y_f)_f)=\sum_f\operatorname{Dec}_f(y_f),
\qquad \operatorname{Dec}_f:M_1\longrightarrow M_5,
\tag{1.2}
$$

where $F$ is finite and each decoder is CPTP on its whole block.
The design precedes the input and choice of future policy. All quantum
information traverses the declared port, without original-input retention,
entangled assistance or bypass. Finite flags are free for this quantum
dimension criterion; decoding consumes them, and the future policy
receives only the decoded state. Set

$$
e(T)=\sup_{\rho\in\mathcal D(\mathbb C^5)}
\sup_{\pi\ {\rm actual,finite}}
\operatorname{TV}(P_\rho^\pi,P_{T(\rho)}^\pi),
\qquad \varepsilon_1=\inf_{T\in\mathfrak C_1}e(T).
\tag{1.3}
$$

Replacement occurs once before the common protocol. TV is half the
$\ell^1$ distance, with its probability-measure version for random
controls. Complete positivity includes arbitrary reference extensions;
the performance criterion in (1.3) measures system histories only.
The original competitors are all complex CPTP designs, without an
initial reality, covariance, unitality or projector restriction.

**Definition 1.3 (Credited mathematical sources).** The repository
abbreviations below refer to source bytes at
`315f5dbf83a7ab871ae7026e0f5041f23834fd00`.

| Name | Source and ingredient |
| --- | --- |
| QMB | [Measurement-relative quantum boundary](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md), Theorems 2.1 and 5.1: first-read identity, rank-one Kraus/scalar-port correspondence, and finite support. |
| QPC | [Port covariance and certified frontier](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_PORT_COVARIANCE_AND_CERTIFIED_FRONTIER.md), Theorem 3.3 and §9: no-worse stationarity and the obstructions to stronger symmetry shortcuts. |
| QRC | [Real-port boundary coordinates](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_REAL_PORT_BOUNDARY_COORDINATES.md), Theorems 3.2, 4.2, 5.2 and 6.2: independent real-product replacement, exact channel coordinates, full TP marginal and all fifteen events. |
| QEC | [Classical-port exact certificates](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_CLASSICAL_PORT_EXACT_CERTIFICATES.md), Proposition 2.2: weighted actual-time survival moment for arbitrary CPTP maps. |
| QWS | [Witness slack and independent decoding](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_WITNESS_SLACK_AND_INDEPENDENT_DECODING.md), Lemmas 2.2–2.3: the retained witness kernel and complementary spectral gap. |
| QJM | [Joint marginal and attaining port](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_JOINT_MARGINAL_AND_ATTAINING_PORT.md), Theorem 2.3, Definition 5.3, Theorems 5.4 and 6.1, and Convention 6.3: the PPT TP lower, exact fourteen-flag upper, active input, and remaining global certificate. |
| NOP | [Navascués–Owari–Plenio, *The power of symmetric extensions for entanglement detection*, arXiv:0906.2731v1](https://arxiv.org/html/0906.2731v1), Definition 1, Theorems 2–3, §VI and Appendix A: Bose-support extensions, marginal-preserving separability by noise, positive decompositions and Jacobi constants. |
| HSR | [Horodecki–Shor–Ruskai, *Entanglement Breaking Channels*, quant-ph/0302031v2](https://arxiv.org/html/quant-ph/0302031v2), Theorem 4(A–D): separable Choi, measure-and-prepare and rank-one Kraus equivalences, with the separate POVM condition for TP. |

NOP and HSR are literature-attested ingredients. The containment on this
specific TP slice, its fifteen-event error transfer, the explicit finite
quadrature bound, the rational level-52 implication and the actual-port
obstruction below are `repo-derived` task-specific mathematical
applications. The
credited reductions and general separability-by-noise theorems are not
additional discoveries of these applications.

**Definition 1.4 (The selected real channel space).** Work in the passive
frame

$$
\begin{gathered}
D=\operatorname{diag}(1,i,i,i,1),\qquad A=-iD^\dagger KD,
\qquad O(t)=e^{tA}=D^\dagger U(t)D,\\
\widehat T(X)=D^\dagger T(DXD^\dagger)D,\qquad
r=\sqrt{17},\quad \mu_\pm=(5\pm r)/2,\quad \omega_\pm=\sqrt{\mu_\pm},\\
B=-A^2,\qquad
R_\pm=\frac{B(B-\mu_\mp I)}{\mu_\pm(\mu_\pm-\mu_\mp)},
\qquad R_0=I-R_+-R_-=dd^T,\quad d=(e_2-e_5)/\sqrt2,\\
u_\pm=\frac{R_\pm e_N}{\sqrt{(1\pm1/r)/2}},\qquad
v_\pm=Au_\pm/\omega_\pm,\qquad
\mathsf J=\operatorname{diag}(1,-1,-1,-1,1).
\end{gathered}
\tag{1.4}
$$

The sector dimensions in order $(0,+,-)$ are $(1,2,2)$. All transposes
refer to this fixed frame; a map dagger denotes the trace-pairing adjoint.
Put $F(a,b)=(ab^T+ba^T)/\sqrt2$ for orthogonal unit vectors and use
QRC's orthonormal basis

$$
H_0=R_0,\qquad H_+=R_+/\sqrt2,\qquad H_-=R_-/\sqrt2,
\qquad \tau=(1,\sqrt2,\sqrt2)^T,
\tag{1.5}
$$

with the following six ordered orthonormal pairs:

$$
\begin{aligned}
+ &: F(d,u_+),\ F(d,v_+),\\
- &: F(d,u_-),\ F(d,v_-),\\
2+ &: (u_+u_+^T-v_+v_+^T)/\sqrt2,\ F(u_+,v_+),\\
2- &: (u_-u_-^T-v_-v_-^T)/\sqrt2,\ F(u_-,v_-),\\
\Delta &: [F(u_+,u_-)+F(v_+,v_-)]/\sqrt2,\
[F(v_+,u_-)-F(u_+,v_-)]/\sqrt2,\\
\Sigma &: [F(u_+,u_-)-F(v_+,v_-)]/\sqrt2,\
[F(v_+,u_-)+F(u_+,v_-)]/\sqrt2.
\end{aligned}
\tag{1.6}
$$

Call these matrices $F_{\nu1},F_{\nu2}$, for
$\nu\in\mathcal N=\{+,-,2+,2-,\Delta,\Sigma\}$, and let
$P_\nu(E)=\sum_{a=1}^2\operatorname{tr}(F_{\nu a}E)F_{\nu a}$.
For $x=(M,\eta)\in M_3(\mathbb R)\times\mathbb R^6$ define

$$
\begin{aligned}
Z(x)&=\sum_{i,j}M_{ij}H_i\otimes H_j
+\sum_\nu\eta_\nu\sum_{a=1}^2F_{\nu a}\otimes F_{\nu a},
&\chi(x)&=Z(x)/5,\\
S_x(E)&=\sum_{i,j}M_{ij}\operatorname{tr}(H_jE)H_i
+\sum_\nu\eta_\nu P_\nu(E).
\end{aligned}
\tag{1.7}
$$

The action on arbitrary complex matrices is the complex-linear extension
after replacing $E$ by $(E+E^T)/2$. Choi order is output $O$ first,
input $I$ second. Thus, on all matrices,

$$
S_x(X)=5\operatorname{Tr}_I[(I_O\otimes X^T)\chi(x)].
\tag{1.8}
$$

Write $\mathcal W=\{\chi(x):x\in\mathbb R^{15}\}$ for this linear
Choi space. Its full TP condition is

$$
M^T\tau=\tau,
\qquad \operatorname{Tr}_O\chi(x)=I_I/5.
\tag{1.9}
$$

Indeed the partial trace of $Z$ is
$\sum_j(M^T\tau)_jH_j$, because the twelve $F$ matrices are
traceless. There are three independent marginal equations, not merely
one trace equation. Every element of $\mathcal W$ is invariant under
transposition of either tensor factor separately. Positive $\chi(x)$
with (1.9) gives a complex CPTP map, by finite spectral factorization of
its Choi matrix. QRC's commutant calculation makes this map stationary
and $\mathsf J$-covariant even if it is not separable. Neither
$M=M^T$ nor $M\tau=\tau$ is imposed.

**Definition 1.5 (All fifteen residuals on the same channel).** Put
$\mathcal J_{15}=\{J\subseteq\mathsf S:1\le|J|\le2\}$,
$\Pi_J=\sum_{s\in J}\Pi_s$, $t_J=(\operatorname{tr}(H_i\Pi_J))_i$,
and

$$
\begin{aligned}
\mathcal H_J(x)&=\Pi_J-S_x^\dagger(\Pi_J)\\
&=\sum_i[t_J-M^Tt_J]_iH_i
+\sum_\nu(1-\eta_\nu)P_\nu(\Pi_J),\\
f(x)&=\max_{J\in\mathcal J_{15}}\|\mathcal H_J(x)\|_{\rm op}.
\end{aligned}
\tag{1.10}
$$

The events are the five singletons and all ten pairs
$\{N,2\},\{N,3\},\{N,5\},\{N,25\},\{2,3\},\{2,5\},
\{2,25\},\{3,5\},\{3,25\},\{5,25\}$.
By QMB's first-read identity, for every positive TP $\chi(x)$,

$$
e(DS_x(D^\dagger\,\cdot\,D)D^\dagger)=f(x).
\tag{1.11}
$$

For clarity, stationarity makes the residual at wait $t$ equal to
$O(t)^T\mathcal H_J(x)O(t)$. TP gives complementary residuals of
opposite signs. After the first complete rank-one read both conditional
states are $\Pi_s$, so every common finite adaptive suffix is the
same probability kernel. This includes zero-probability branches and
source-independent random controls. Maximizing a Hermitian event
expectation over all complex density inputs gives its operator norm;
a maximizing real eigenvector, wait zero, a complete read and Stop
attain (1.11). These arguments use the adjoint, not self-adjointness
of the channel.

Let $\mathcal F$ be the positive TP elements of $\mathcal W$ that
are finite sums of independent real product projectors. QRC Theorems
3.2, 5.2 and 6.2 give the credited exact correspondence

$$
\varepsilon_1=\min_{\chi(x)\in\mathcal F}f(x).
\tag{1.12}
$$

Every original complex scalar port has a no-worse representative here,
and every point here is an original fixed scalar port. The replacement
can change the channel. Independent preparation and measurement vectors
remain independent; no restriction to $a=b$, two orbits, unital maps,
or definite-character rank-one Kraus operators follows.

## 2. Bose support, the half-PPT condition and marginal-preserving containment

**Definition 2.1 (Finite extension relaxations).** Let $n\ge1$ be an
integer and $P_n$ the orthogonal projector onto
$\operatorname{Sym}^n(O)$, where $O=\mathbb C^5$. A normalized
output Bose extension of $\chi(x)$ is an operator $\Omega$ on
$I\otimes O^{\otimes n}$ satisfying

$$
\begin{gathered}
\Omega\succeq0,\quad \operatorname{tr}\Omega=1,\quad
(I_I\otimes P_n)\Omega(I_I\otimes P_n)=\Omega,\\
\operatorname{Tr}_{O_2\cdots O_n}\Omega
=\operatorname{flip}(\chi(x)).
\end{gathered}
\tag{2.1}
$$

The flip in (2.1) only changes output-first Choi order to input-first
extension order. Define $\mathcal R_n$ to consist of $\chi(x)\in
\mathcal W$ satisfying the full marginal (1.9) and admitting such an
extension. Define $\mathcal R_n^{\rm P}$ by also imposing

$$
\Omega^{\Gamma_{O_{n-\lfloor n/2\rfloor+1}\cdots O_n}}
\succeq0.
\tag{2.2}
$$

Thus the split is $IO^{\lceil n/2\rceil}\mid
O^{\lfloor n/2\rfloor}$, exactly as in NOP. The partial transpose
is applied to the embedded extension. Positivity of the two-body
partial transpose alone is not (2.2). Bose support is stronger than
permutation invariance of a mixed operator; (2.1) requires the support
itself to lie in the symmetric subspace.

Let $L_n$ and $L_n^{\rm P}$ be the minima of $f(x)$ on these two
sets. Equivalently minimize $z\ge0$ subject to (1.9), (2.1), the
appropriate condition (2.2), and all thirty LMIs

$$
zI_5-\mathcal H_J(x)\succeq0,\qquad
zI_5+\mathcal H_J(x)\succeq0
\quad(J\in\mathcal J_{15}).
\tag{2.3}
$$

The same $x$ and marginal occur in every inequality. The extension
indices are mathematical certificate variables, not additional source
copies or future actions.

**Theorem 2.2 (Containment on the original TP slice).** Let
$\Delta(X)=\operatorname{tr}(X)I_5/5$ and
$\chi_*=I_O\otimes I_I/25=\chi(x_*)$, with
$M_* =\tau\tau^T/5$ and $\eta_*=0$. Then

$$
\mathcal F\subseteq\mathcal R_n^{\rm P}\subseteq\mathcal R_n.
\tag{2.4}
$$

For $\chi\in\mathcal R_n$, the state
$\chi_p=(1-p)\chi+p\chi_*$ belongs to $\mathcal F$ whenever
$5/(n+5)\le p\le1$. For $\chi\in\mathcal R_n^{\rm P}$ it
belongs to $\mathcal F$ whenever $p_n^{\rm P}\le p\le1$, where

$$
\begin{gathered}
p_n^{\rm P}=\frac58g_n,\qquad g_n=1-\zeta_n,\\
\zeta_n=\text{largest zero of }
\begin{cases}
P_{n/2+1}^{(3,0)},&n\text{ even},\\
P_{(n+1)/2}^{(3,1)},&n\text{ odd}.
\end{cases}
\end{gathered}
\tag{2.5}
$$

Here $P_j^{(a,b)}$ is the Jacobi polynomial orthogonal for
$(1-y)^a(1+y)^b$ on $[-1,1]$. Both repairs preserve the exact
input marginal $I_5/5$.

Proof. Write a point of $\mathcal F$ as
$\chi=\sum_fq_f a_fa_f^T\otimes b_fb_f^T$, where the vectors
are real unit vectors, $q_f\ge0$, and $\sum_fq_f=1$.
Then

$$
\Omega=\sum_fq_f b_fb_f^T\otimes(a_fa_f^T)^{\otimes n}
\tag{2.6}
$$

has exactly the required marginal and Bose support. It is positive
under partial transpose of every subcollection of output factors.
This proves (2.4).

Apply the credited NOP Theorem 2 with its $A=I$ the channel input,
its $B=O$ the channel output, and $d=5$. Its repaired operator is

$$
\frac{n}{n+5}\chi+\frac{I_O\otimes\chi_I}{n+5},
\qquad \chi_I=\operatorname{Tr}_O\chi=I_I/5.
\tag{2.7}
$$

It is complex-separable and equals $\chi_p$ for $p=5/(n+5)$.
NOP Theorem 3 under precisely (2.2) instead gives

$$
(1-5g_n/8)\chi+(g_n/8)I_O\otimes\chi_I,
\tag{2.8}
$$

which is $\chi_{p_n^{\rm P}}$. The untouched NOP marginal is
the channel's input marginal. Its exact identification makes the noise
center the fixed $\chi_*$ even for nonunital channels. Section 4
derives the positive decomposition and the Jacobi constant in (2.8)
with an explicit finite extraction.

The repaired state remains in the linear space $\mathcal W$ and
has the same full marginal. To show real-product membership, use the
separate-transpose invariance of this whole state. On a product
decomposition apply $\mathcal R(X)=(X+X^T)/2$ to each factor.
For a Hermitian positive matrix $X$, $\mathcal R(X)$ is a positive
real symmetric matrix: its quadratic form on a real vector is that of
$X$, and real symmetric positivity also implies complex positivity.
Real spectral decomposition therefore replaces each product by a finite
sum of real product projectors. The separately invariant whole state
is unchanged. This is an algebraic operation on the decomposition;
it does not assert complete positivity of $\mathcal R$ on arbitrary
entangled inputs. QRC Theorem 5.2 now gives membership in $\mathcal F$.

Finally $\chi_*\in\mathcal F$. If a repair is valid at $p_0<1$,
then for $p\in[p_0,1]$,

$$
\chi_p=\frac{1-p}{1-p_0}\chi_{p_0}
+\frac{p-p_0}{1-p_0}\chi_*.
\tag{2.9}
$$

Both coefficients are nonnegative and sum to one. This proves the
larger-noise assertions, including $p=1$. $\square$

## 3. Exact transfer to all original events and histories

**Theorem 3.1 (Eventwise transport and the original-value enclosure).**
For either containment of Theorem 2.2, use a permitted $p$ and put
$x_p=(1-p)x+px_*$. Then for every $J\in\mathcal J_{15}$,

$$
\begin{aligned}
\mathcal H_J(x_p)
&=(1-p)\mathcal H_J(x)+p(\Pi_J-|J|I_5/5),\\
\|\mathcal H_J(x_p)\|_{\rm op}
&\le(1-p)\|\mathcal H_J(x)\|_{\rm op}+p c_J,\\
c_J&=\begin{cases}4/5,&|J|=1,\\3/5,&|J|=2.\end{cases}
\end{aligned}
\tag{3.1}
$$

In particular the repaired fixed scalar port satisfies

$$
e(T_{x_p})\le(1-p)f(x)+\frac45p.
\tag{3.2}
$$

With $L$ the corresponding $L_n$ or $L_n^{\rm P}$,

$$
\boxed{L\le\varepsilon_1\le(1-p)L+\frac45p.}
\tag{3.3}
$$

Both sides concern (1.3), including every original complex competitor
for the necessary direction and every complex input and actual finite
history for the sufficient direction.

Proof. The adjoint of $\Delta$ maps $E$ to
$\operatorname{tr}(E)I_5/5$. Linearity of the adjoint gives the
first identity in (3.1). The eigenvalues of
$\Pi_J-|J|I_5/5$ are $1-|J|/5$ on its range and $-|J|/5$ on
its orthogonal complement. This gives the two constants and the norm
inequality. Taking the maximum and using (1.11) proves (3.2). The
sharper eventwise bounds in (3.1) remain simultaneous bounds on one
channel; their replacement by $4/5$ in (3.2) is only an upper estimate.

For any original $T\in\mathfrak C_1$, the credited no-worse QRC
representative has Choi state in $\mathcal F$, hence in both outer
sets by (2.4). Thus $L\le e(T)$ for every original complex competitor.
This proves the lower in (3.3), without restricting the original class
to real designs.

The feasible extension sets are compact. Normalized positive operators
on a fixed finite-dimensional support form a compact set, and the
marginal, support and partial-transpose conditions are closed.
The projected marginal determines $x$ uniquely; $f$ is continuous.
Both sets are nonempty by (2.6) applied to $\chi_*$. Hence a minimizer
exists. Repair such a minimizer by Theorem 2.2 and apply (3.2) to prove
the upper in (3.3). Its finite fixed-port realization is given in
Theorem 4.1. Neither the minimizer of the outer problem nor its
unperturbed marginal has thereby been declared a scalar port. $\square$

## 4. Finite exact extraction of the repaired channel

**Theorem 4.1 (A finite quadrature and a whole-block TP port).** Suppose
an exact feasible extension $\Omega$ in Definition 2.1 is given.
For the appropriate threshold $p_0$ in Theorem 2.2, and every fixed
$p\in[p_0,1]$, the repaired channel has a finite scalar-port description
with at most

$$
K_n+1,\qquad
K_n=(s m)^4,\quad s=\left\lceil\frac{n+2}{2}\right\rceil,
\quad m=n+2
\tag{4.1}
$$

flags. The additional flag is needed only for further depolarizing
mixing. If all entries of $\Omega$ and $p$ are algebraic, all the
port data can be algebraic. The flags in (4.1) may have mixed POVM
effects; finite spectral refinement gives rank-one composite Kraus
operators. The same repaired channel also has the credited QRC
real-product support bound of $225$ flags.

Proof. The following construction makes the finite-node assertion
independent of an unspecified finite-design order. Let $\mu$ be
normalized complex projective Haar measure on unit $z\in\mathbb C^5$.
Set $t=n+1$. For each $j=1,2,3,4$, take the $s$-node positive Gauss
rule for the probability measure

$$
(5-j)(1-x)^{4-j}\,dx\quad(0\le x\le1).
\tag{4.2}
$$

These are standard Gaussian quadrature ingredients. Their properties
needed here follow directly: the degree-$s$ orthogonal polynomial has
$s$ simple interior zeros, since otherwise multiplying its sign-changing
factors would contradict orthogonality to lower-degree polynomials.
Division by that polynomial proves exactness through degree $2s-1$.
If $\ell_a$ is a cardinal Lagrange polynomial at a node, its quadrature
weight equals the integral of $\ell_a^2$, hence is strictly positive.
Rational moments give rational orthogonal-polynomial coefficients;
the nodes and weights are algebraic. Thus all four rules have the
claimed positivity and exactness, not merely an asymptotic accuracy.

For one product node $(x_1,x_2,x_3,x_4)$ put

$$
\begin{aligned}
p_1&=x_1,&p_2&=(1-x_1)x_2,\\
p_3&=(1-x_1)(1-x_2)x_3,
&p_4&=(1-x_1)(1-x_2)(1-x_3)x_4,\\
p_5&=\prod_{j=1}^4(1-x_j),
\qquad
z_j=\sqrt{p_j}e^{2\pi i\ell_j/m}\ (j\le4),
&z_5&=\sqrt{p_5},
\end{aligned}
\tag{4.3}
$$

where each $\ell_j$ ranges from $0$ to $m-1$. Give this node weight
$q_z$ equal to the product Gauss weight divided by $m^4$. There are
$s^4m^4=K_n$ nodes, all with positive weights summing to one, and

$$
\sum_zq_z(zz^\dagger)^{\otimes l}
=\int(zz^\dagger)^{\otimes l}\,d\mu(z)
=\frac{P_l}{D_l},\qquad
0\le l\le t,\quad D_l=\binom{l+4}{4}.
\tag{4.4}
$$

To prove exactness, an entry is $z^\alpha\bar z^\beta$ with
$|\alpha|=|\beta|=l$. The four phase sums kill it unless the first
four exponent differences vanish, since each has magnitude at most
$l<m$. Equality of total degrees then forces the fifth difference
to vanish. The surviving monomial is $\prod_jp_j^{\alpha_j}$,
of degree at most $l$ in each stick variable. Since $2s-1\ge t$,
the four Gauss rules integrate it exactly. The change of variables
(4.3) sends the independent densities (4.2) to the uniform simplex
law, whose density is $4!$; its monomial moment is

$$
\int\prod_jp_j^{\alpha_j}\,d\mu
=\frac{4!\prod_j\alpha_j!}{(l+4)!}.
\tag{4.5}
$$

Together with uniform relative phases this is projective Haar measure.
The permutation-sum formula for $P_l$ has matching entry
$\prod_j\alpha_j!/l!$ and zero unmatched entries; division by
$D_l$ gives exactly (4.5). This proves both equalities in (4.4).
It also proves exactness for every balanced polynomial of bidegrees
$(l,l)$ with $l\le t$.

For use in both repairs, let $\Omega^{(l)}$ be the reduced extension
on $I\otimes O^{\otimes l}$, and define its input matrix contraction

$$
G_l(z)=(I_I\otimes\langle z^{\otimes l}|)\Omega^{(l)}
(I_I\otimes|z^{\otimes l}\rangle),\qquad G_0(z)=\chi_I.
\tag{4.6}
$$

Every reduced extension has Bose support. Consequently

$$
\begin{aligned}
\int G_l(z)\,d\mu&=\frac{\chi_I}{D_l},\\
\int zz^\dagger\otimes G_l(z)\,d\mu
&=\frac{l\chi+I_O\otimes\chi_I}{(l+5)D_l}.
\end{aligned}
\tag{4.7}
$$

The first identity follows from (4.4). For the second, expand
$P_{l+1}$ as the average of all permutations. The $l!$ permutations
fixing the prepared last slot contribute $I_O\otimes\chi_I$;
the other $l\,l!$ contribute the same one-output marginal $\chi$.
Left and right permutations of the first $l$ slots leave the
Bose-supported operator unchanged. Finally
$(l+1)D_{l+1}=(l+5)D_l$ gives the coefficient in (4.7).
For $l=0$ this reads $\int zz^\dagger\otimes\chi_I
=I_O\otimes\chi_I/5$, so the degenerate case is included.
This is the contraction behind NOP §VI, equation (64).

For the ordinary Bose repair set

$$
R_z=D_nq_zG_n(z)\succeq0.
\tag{4.8}
$$

The finite rule is exact for $G_n$ and $zz^\dagger\otimes G_n$.
Equations (4.7) therefore give

$$
\sum_zR_z=\chi_I=I_I/5,\qquad
\sum_z zz^\dagger\otimes R_z
=\frac{n\chi+I_O\otimes\chi_I}{n+5}.
\tag{4.9}
$$

For the PPT repair write $n=2k+\delta$, where
$\delta\in\{0,1\}$. Reorder the outputs as
$(O_1,O'_1,\ldots,O_k,O'_k)$ with one additional untransposed output
when $\delta=1$. Transpose the $k$ primed factors. This is (2.2),
up to a permutation, by Bose support. Put

$$
\begin{gathered}
\Phi=\sum_{j=1}^5e_j\otimes e_j,\\
\psi_i(z)=(z\otimes\bar z)^{\otimes i}
\otimes\Phi^{\otimes(k-i)}\otimes z^{\otimes\delta},
\quad 0\le i\le k,\qquad
\phi(z)=\sum_{i=0}^kc_i\psi_i(z),\\
\mathsf B_{ij}=\frac{(i+j+\delta)!}{(i+j+\delta+4)!},\qquad
\mathsf A_{ij}=\frac{(i+j+\delta)!}{(i+j+\delta+5)!}.
\end{gathered}
\tag{4.10}
$$

Choose a nonzero real vector $c$ minimizing
$\alpha=c^T\mathsf Ac/(c^T\mathsf Bc)$. The following derivation
of its value is the NOP Appendix A ingredient, specialized with all
normalizations retained. For $q(x)=\sum_{i=0}^kc_ix^i$,

$$
\begin{aligned}
c^T\mathsf Bc&=\frac16\int_0^1x^\delta(1-x)^3q(x)^2\,dx>0,\\
c^T\mathsf Ac&=\frac1{24}\int_0^1x^\delta(1-x)^4q(x)^2\,dx.
\end{aligned}
\tag{4.11}
$$

The strict inequality follows because a nonzero polynomial cannot
vanish on the open interval. Thus $\mathsf B$ is positive definite
and $\alpha$ is one quarter of the minimum weighted mean of $1-x$
over polynomials of degree at most $k$. The compression of multiplication
by $x$ to that polynomial space has eigenvalues the $k+1$ zeros
of its degree-$k+1$ orthogonal polynomial. Indeed, an eigenvector
polynomial $q$ at eigenvalue $y$ satisfies
$(x-y)q\perp\{1,x,\ldots,x^k\}$, so $(x-y)q$ is a nonzero
multiple of that orthogonal polynomial. Conversely division by any
of its simple interior zeros gives such an eigenvector. The simple
interior-root assertion follows from the same sign-change argument
used for the Gauss rules. Under $u=2x-1$ the weight becomes a positive
constant times $(1-u)^3(1+u)^\delta$. Therefore

$$
\alpha=\frac{1-\zeta_n}{8}=\frac{g_n}{8},\qquad
p_n^{\rm P}=5\alpha.
\tag{4.12}
$$

In particular $0<p_n^{\rm P}\le5/(n+5)<1$, since the quotient at
$c=e_k$ is $1/(n+5)$. The minimizing $\alpha$ and a nonzero kernel
vector of $\mathsf A-\alpha\mathsf B$ can be algebraic, because
the two matrices are rational and $\mathsf B$ is positive definite.
For $n=1$, $k=0$, $\delta=1$, one gets $\alpha=1/6$ and
$p_1^{\rm P}=5/6$, agreeing with the ordinary repair. No transposed
output is required in that case.

Define the input matrix

$$
F_z=(I_I\otimes\langle\phi(z)|)\Omega^{\Gamma_{
O'_1\cdots O'_k}}(I_I\otimes|\phi(z)\rangle)\succeq0.
\tag{4.13}
$$

There is the exact Bose contraction identity

$$
F_z=\sum_{i,j=0}^kc_ic_jG_{i+j+\delta}(z).
\tag{4.14}
$$

To verify it, move the primed transpose onto
$|\psi_j(z)\rangle\langle\psi_i(z)|$. For $i\le j$, the
first $i$ common pairs give $2i$ copies of $zz^\dagger$.
Each of the next $j-i$ pairs has one $\Phi$ factor and one
$z\otimes\bar z$ factor. Its partial transpose is a swap composed
with one $zz^\dagger$ and an identity. Every remaining
$|\Phi\rangle\langle\Phi|$ becomes a swap. The extra odd factor
gives one further $zz^\dagger$. Independent left and right
permutations remove these swaps against the Bose-supported $\Omega$,
leaving $i+j+\delta$ projectors and identities on all other outputs.
Tracing these outputs is precisely $G_{i+j+\delta}$. For $i>j$
take adjoints. This proves the matrix identity, not just its trace.

Using (4.7), $D_l^{-1}=24l!/(l+4)!$, and (4.10) gives

$$
\begin{aligned}
\int F_z\,d\mu
&=24(c^T\mathsf Bc)\chi_I,\\
\int zz^\dagger\otimes F_z\,d\mu
&=24\left[(c^T\mathsf Bc-5c^T\mathsf Ac)\chi
+(c^T\mathsf Ac)I_O\otimes\chi_I\right].
\end{aligned}
\tag{4.15}
$$

The normalization is the strictly positive number
$h=24c^T\mathsf Bc$. Entries of $F_z$ are balanced polynomials
of bidegree at most $(n,n)$, either directly from (4.10) or from
(4.14). Multiplication by $zz^\dagger$ raises this to at most
$(n+1,n+1)$. The same finite rule (4.4) therefore preserves both
integrals in (4.15) exactly. Set

$$
R_z=q_zF_z/h\succeq0.
\tag{4.16}
$$

Then

$$
\sum_zR_z=\chi_I=I_I/5,\qquad
\sum_z zz^\dagger\otimes R_z
=(1-5\alpha)\chi+\alpha I_O\otimes\chi_I
=\chi_{p_n^{\rm P}}.
\tag{4.17}
$$

This proves the needed positive decomposition, including its full
input marginal, for both even and odd levels. It is the finite
specialization of NOP §VI, equations (71)–(76); the node count here
follows from (4.2)–(4.5), rather than from an unquantified design
existence statement.

For either (4.9) or (4.17), discard nodes with $R_z=0$ and set

$$
E_z=5R_z^T,\qquad \sigma_z=zz^\dagger,\qquad
\operatorname{Enc}(X)=(\operatorname{tr}(E_zX))_z,
\qquad \operatorname{Dec}_z(y)=y\sigma_z.
\tag{4.18}
$$

Each $E_z$ is positive, $\sum_zE_z=I_5$, and
$\operatorname{tr}\sigma_z=1$. Spectral factorization of $E_z$
gives a finite sum of rectangular row sandwiches for its encoder
branch; its positivity at every reference dimension follows directly.
The decoder is a normalized column sandwich, hence is CPTP on every
complex scalar, including values outside encountered state branches.
The composite normalized Choi matrix is
$\frac15\sum_z\sigma_z\otimes E_z^T
=\sum_z\sigma_z\otimes R_z$, exactly the repaired state.
The same calculation proves the branch probability
$\operatorname{tr}(E_zX)$ before and after decoding. In physical
coordinates use effects $DE_zD^\dagger$ and preparations
$D\sigma_zD^\dagger$.

For $p>p_0$ multiply all these encoder effects by
$(1-p)/(1-p_0)$ and add the one effect
$(p-p_0)I_5/(1-p_0)$ with decoder $y\mapsto yI_5/5$.
This realizes (2.9). The endpoint $p=1$ uses just that depolarizing
branch. No division by a zero branch weight is used.

When $\Omega$ and $p$ are algebraic, all quadrature nodes, phase
roots of unity, $c$, contractions, weights and positive normalizations
above are algebraic. Finite Hermitian spectral factorization also
permits algebraic eigenvalues and eigenvectors. It gives rank-one
composite Kraus matrices because every branch factors through a scalar.
The decoder with state $I_5/5$ may have several column Kraus matrices;
each composite still has rank at most one. The effects need not be
rank one for the flag count (4.1).

Lastly, separate realification of this finite product decomposition
as in Theorem 2.2 leaves the repaired $\mathcal W$ state unchanged.
The credited QRC real-product Carathéodory bound reduces its support
to at most $225$ flags. It preserves the entire channel and its
full marginal. This existence bound and the explicit quadrature are
different descriptions of the same repaired channel. Neither gives a
decomposition of the unperturbed $\chi$. $\square$

## 5. A rational level-52 repair and its conditional endpoint consequence

**Theorem 5.1 (Exact rational containment at level 52).** Every
$\chi\in\mathcal R_{52}^{\rm P}$ satisfies

$$
\frac{63}{64}\chi+\frac1{64}\chi_*\in\mathcal F.
\tag{5.1}
$$

For $L=L_{52}^{\rm P}$,

$$
L\le\varepsilon_1\le\frac{63}{64}L+\frac1{80},
\qquad L\ge L_0:=\frac{129931}{250000}.
\tag{5.2}
$$

Proof. For $n=52$ the polynomial in (2.5) is $P_{27}^{(3,0)}$.
Its exact binomial expression is

$$
P_m^{(a,b)}(x)=2^{-m}\sum_{j=0}^m
\binom{m+a}{j}\binom{m+b}{m-j}(x-1)^{m-j}(x+1)^j.
\tag{5.3}
$$

In particular,

$$
\begin{aligned}
P_{27}^{(3,0)}(39/40)
&=\frac1{80^{27}}\sum_{j=0}^{27}
\binom{30}{j}\binom{27}{27-j}(-1)^{27-j}79^j\\
&=-\frac{3699076981653450378355112312523193564930362582897147}
{151115727451828646838272000000000000000000000000000}<0,\\
P_{27}^{(3,0)}(1)&=\binom{30}{27}=4060>0.
\end{aligned}
\tag{5.4}
$$

Thus there is a root in $(39/40,1)$. All roots are in $(-1,1)$,
by orthogonality for the positive Jacobi weight. The largest root
therefore has $0<g_{52}<1/40$, and
$p_{52}^{\rm P}=(5/8)g_{52}<1/64$. Theorem 2.2 with additional
depolarizing mixing proves (5.1), and Theorem 3.1 gives the first
two inequalities in (5.2).

For the remaining inequality, every positive state in $\mathcal W$
is separately input-transpose invariant, hence is PPT on its two-body
space. The QJM Theorem 2.3 witness bounds the entire complex PPT TP
Choi slice, not only separable points. Explicitly its credited survival
moment $\mathcal V$, marginal multiplier $Y$, witness gap
$\gamma=1/25000$ and same-plane projection $Q$ give

$$
\begin{gathered}
\operatorname{tr}(\chi(I_O\otimes Y-\mathcal V))
\ge\gamma\left(1-\tfrac12\operatorname{tr}(\chi Q)\right),
\qquad \operatorname{tr}Y/5=4803/10000,\\
Q=R_+\otimes R_++R_-\otimes R_-,\qquad
Q\preceq I_O\otimes(R_++R_-).
\end{gathered}
\tag{5.5}
$$

The same full TP marginal gives
$\operatorname{tr}(\chi Q)\le4/5$. Consequently the survival is at
most $4803/10000-3/125000$. The QEC actual-time moment inequality
$e(T)\ge1-\operatorname{tr}(\chi\mathcal V)$ holds for every
CPTP map; it does not require separability. Together with (1.11)
this yields $f(x)\ge L_0$ for every feasible relaxed point, proving
$L\ge L_0$. This use of the old lower is a credited consequence on
the correct outer slice. $\square$

**Definition 5.2 (Exact finite dual-certificate equations).** At level
$n=52$, use the natural isometric occupation-basis embeddings

$$
\begin{aligned}
V_n &: I\otimes\operatorname{Sym}^n(O)\longrightarrow
I\otimes O^{\otimes n},\\
V_h &: I\otimes\operatorname{Sym}^{26}(O)
\otimes\operatorname{Sym}^{26}(O)\longrightarrow
I\otimes O^{\otimes52}.
\end{aligned}
\tag{5.6}
$$

For a Hermitian supported extension variable $W$, let
$\mathcal B(W)$ be the output-first marginal of $V_nWV_n^\dagger$
on $O_1\otimes I$, and let

$$
\mathcal G(W)=V_h^\dagger
(V_nWV_n^\dagger)^{\Gamma_{O_{27}\cdots O_{52}}}V_h.
\tag{5.7}
$$

The support in Proposition 6.2 makes $\mathcal G(W)\succeq0$
equivalent to the embedded half-transpose condition. Adjoint maps
$\mathcal B^\dagger,\mathcal G^\dagger$ refer to the real
Hermitian trace pairing; they are fixed finite linear maps. An exact
dual certificate consists of matrices $A_J^\pm\succeq0$ of order
five, a Hermitian matrix $Q$ of order $25$, a positive matrix $R$
on the half-symmetric support, and $y\in\mathbb R^3$, satisfying

$$
\begin{gathered}
\sum_J\operatorname{tr}(A_J^++A_J^-)=1,\qquad R\succeq0,\\
P:=\mathcal B^\dagger(Q)-\mathcal G^\dagger(R)\succeq0,\\
Z_J=A_J^+-A_J^-,\qquad
\beta=\sum_J\operatorname{tr}(Z_J\Pi_J),\qquad
\mathcal L(x)=\sum_J\operatorname{tr}(Z_JS_x^\dagger(\Pi_J)),\\
\mathcal L(x)+\operatorname{tr}(Q\chi(x))
=y^TM^T\tau\quad\text{for every }x=(M,\eta)\in\mathbb R^{15},\\
a=\beta-\tau^Ty.
\end{gathered}
\tag{5.8}
$$

The linear identity in (5.8) is a finite coefficient condition:
it is checked on the fifteen coordinate basis vectors of (1.7).
The positive matrices $P$ and $R$ concern the full supported extension
and its half-transpose, respectively. This is the usual conic weak-dual
certificate specialized to (1.9), (2.1)–(2.3); no dual attainment
or numerical status is part of its definition.

**Theorem 5.3 (Conditional strict progress on the original interval).**
Let $\lambda_Q$ be the exact error of the QJM fourteen-flag port,
so the credited original interval is

$$
L_0\le\varepsilon_1\le\lambda_Q,\qquad
\frac{52417656}{10^8}<\lambda_Q<\frac{52417658}{10^8}.
\tag{5.9}
$$

Suppose there is an exact primal feasible extension for the
level-52 problem (1.9), (2.1)–(2.3) with objective $b$, and a dual
certificate (5.8) of value $a$ for that same problem, such that

$$
a\le L\le b,\qquad b-a\le\frac1{100000}.
\tag{5.10}
$$

The first inequality on $a$ follows from (5.8). Put

$$
\ell=\max(L_0,a),\qquad
u=\min\left(\lambda_Q,\frac{63}{64}b+\frac1{80}\right).
\tag{5.11}
$$

Then

$$
\ell\le\varepsilon_1\le u,\qquad
u-\ell\le\frac{140453}{32000000}
<\frac{55657}{12500000}<\lambda_Q-L_0.
\tag{5.12}
$$

Hence $\ell>L_0$ or $u<\lambda_Q$, possibly both. The upper branch
is supplied by the repaired legal fixed scalar port of Theorem 4.1;
exact algebraic primal data give its exact algebraic description.

Proof. A primal feasible point gives a relaxed upper $b$; Theorem 5.1
repairs that same point to an original legal port of error at most
$63b/64+1/80$. To give the lower direction explicitly, for any feasible
$(x,z,W)$ the dual equations imply

$$
\begin{aligned}
z-a={}&\sum_J\operatorname{tr}\left[
A_J^+(zI-\mathcal H_J(x))+A_J^-(zI+\mathcal H_J(x))\right]\\
&+\operatorname{tr}(PW)+\operatorname{tr}(R\mathcal G(W))\ge0.
\end{aligned}
\tag{5.13}
$$

Indeed the event sum is $z-\beta+\mathcal L(x)$, while the last
two terms sum to $\operatorname{tr}(Q\mathcal B(W))
=\operatorname{tr}(Q\chi(x))$. The coefficient identity in (5.8)
and $M^T\tau=\tau$ make their total
$z-\beta+\tau^Ty=z-a$. Every term is a positive-semidefinite
trace pairing. Taking the relaxed minimum gives $a\le L$; (2.4)
then makes $a$ necessary for every original complex scalar port.
Combining these facts with
(5.9) proves the first part of (5.12). Since $\ell\ge a$ and
$\ell\ge L_0$,

$$
\begin{aligned}
u-\ell
&\le\frac{63}{64}(b-\ell)+\frac1{64}\left(\frac45-\ell\right)\\
&\le\frac{63}{6400000}+\frac{70069}{16000000}
=\frac{140453}{32000000}.
\end{aligned}
\tag{5.14}
$$

On the other hand,

$$
\frac{52417656}{10^8}-L_0=\frac{55657}{12500000},\qquad
\frac{55657}{12500000}-\frac{140453}{32000000}
=\frac{50723}{800000000}>0.
\tag{5.15}
$$

If neither endpoint improved, then $\ell=L_0$ and $u=\lambda_Q$,
contradicting (5.12). The proof requires exact certificates in (5.10);
it does not supply such $a,b,\Omega$, an evaluated $L$, or a new
unconditional numerical endpoint. $\square$

## 6. The actual old-port obstruction and finite mathematical sizes

**Theorem 6.1 (Positive depolarization worsens the QJM port).** Let
$T_Q$ be exactly the legal fourteen-flag channel in QJM Definition
3.1 and Theorem 6.1, and $\lambda=\lambda_Q=e(T_Q)$. For every
$0<p\le1$,

$$
e((1-p)T_Q+p\Delta)
>\lambda+\frac{1071}{4040}p>\lambda.
\tag{6.1}
$$

This concerns the original input set and actual wait-zero full mode
read, without a larger observation menu.

Proof. The active block of the adjoint residual
$\Pi_N-\widehat T_Q^\dagger(\Pi_N)$ on $L=(N,25)$ is the
credited QJM matrix

$$
\begin{gathered}
C_N=\frac1{D_0}\begin{pmatrix}a_0&b_0\\b_0&c_0\end{pmatrix},
\quad D_0=64468731767080,\\
a_0=32710322397343+193561738103\sqrt{17},\\
b_0=1674636624370+414723353026\sqrt{17},\\
c_0=-6400945486418-13799938410\sqrt{17}.
\end{gathered}
\tag{6.2}
$$

Its positive eigenvalue is $\lambda$. Use exactly the QJM attaining
input vector

$$
v=\frac{b_0e_N+(D_0\lambda-a_0)e_{25}}
{\sqrt{b_0^2+(D_0\lambda-a_0)^2}}.
$$

The denominator is nonzero because $b_0>0$. Its eigenvector equation
follows from $\det(\lambda I-C_N)=0$; its second row gives

$$
\frac{v_{25}}{v_N}=\frac{b_0}{D_0\lambda-c_0}.
\tag{6.3}
$$

Direct integer comparisons using $4<\sqrt{17}<5$ give

$$
0<\frac{b_0}{D_0}<\frac3{50},\qquad
\frac{c_0}{D_0}<-\frac1{10}.
\tag{6.4}
$$

For example the upper-bound comparison margins at the appropriate
endpoints are respectively

$$
\frac3{50}-\frac{1674636624370+5(414723353026)}{D_0}
=\frac{4407004284}{2370173962025}>0,
\tag{6.5}
$$

and

$$
-\frac1{10}-\frac{-6400945486418-4(13799938410)}{D_0}
=\frac{927206335}{6446873176708}>0.
\tag{6.6}
$$

The credited root interval (5.9) implies
$1/2<\lambda<21/40$. Therefore
$0<v_{25}/v_N<1/10$, and $v_N^2>100/101$.
For the physical input $Dvv^TD^\dagger$, wait zero, a complete
five-outcome read and Stop, the singleton-$N$ probability difference
under $T_Q$ is exactly $v^TC_Nv=\lambda$. Under $\Delta$ it is
$v_N^2-1/5$. The same event after the repaired channel has difference

$$
(1-p)\lambda+p(v_N^2-1/5)
=\lambda+p(v_N^2-1/5-\lambda),
\tag{6.7}
$$

whose bracket satisfies

$$
v_N^2-\frac15-\lambda
>\frac{100}{101}-\frac15-\frac{21}{40}
=\frac{1071}{4040}>0.
\tag{6.8}
$$

Full-read TV is at least this positive event difference, and this
protocol belongs to the original menu. Taking the original suprema
proves (6.1). At $p=0$ the error is $\lambda$ by the credited
all-fifteen-event certificate; the strict conclusion is for $p>0$.
Thus positive repair is not an error-preserving extraction of this
actual boundary port. The proof does not exclude repairing a different
relaxed channel with enough better residuals. $\square$

**Proposition 6.2 (Unsplit extension orders and explicit node bound).**
The Bose-supported extension in Definition 2.1 can be represented by
a positive matrix of order

$$
h_n=5\binom{n+4}{4}.
\tag{6.9}
$$

Its half-transpose is supported on
$I\otimes\operatorname{Sym}^{\lceil n/2\rceil}(O)
\otimes\operatorname{Sym}^{\lfloor n/2\rfloor}(O)$, with unsplit
ambient positive-matrix order

$$
\widetilde h_n=
5\binom{\lceil n/2\rceil+4}{4}
\binom{\lfloor n/2\rfloor+4}{4}.
\tag{6.10}
$$

At $n=52$ the corresponding quantities and the quadrature parameters are

$$
\begin{gathered}
D_{52}=\binom{56}{4}=367290,\qquad h_{52}=1836450,\\
D_{26}=\binom{30}{4}=27405,\qquad
\widetilde h_{52}=5(27405)^2=3755170125,\\
t=53,\quad s=27,\quad m=54,\qquad
K_{52}=(27\cdot54)^4=4518872583696.
\end{gathered}
\tag{6.11}
$$

These are mathematical support and explicit-construction counts.
They are not lower bounds for every equivalent certificate description
or a runtime, memory, coefficient-bit-length or physical-cost estimate.

Proof. A basis of $\operatorname{Sym}^n(\mathbb C^5)$ is indexed
by the five nonnegative occupation numbers summing to $n$.
Stars and bars gives $D_n=\binom{n+4}{4}$, and tensoring with
the five-dimensional input gives (6.9). Bose support implies left and
right invariance under permutations within either half of the outputs.
The projectors onto those two symmetric subspaces are real. After
partial transpose of one half, its left and right support projectors
are interchanged and remain those same projectors. Thus (6.10) is a
valid support representation for the half-transpose PSD condition.
It need not have the same order as the original Bose matrix.
Substituting $n=52$ gives the first two lines of (6.11), and (4.1)
gives the last line.

The QRC $225$-flag support bound concerns the repaired two-body state;
it does not reduce the extension orders by itself. Further block
reductions or smaller certificates require their own exact support or
representation argument. Conversely (6.11) makes no assertion that
these unsplit arrays must be materialized to prove a useful certificate.
The finite sufficiency result in Theorem 5.3 includes its uninstantiated
primal and dual conditions at these orders. $\square$

## 7. Mathematical boundaries of the alternative certificate route

**Definition 7.1 (Exact versus noisy extraction obligations).** The
alternative in §§2–5 keeps the original $\varepsilon_1$, all fifteen
events, every complex competitor via the proved no-worse replacement,
and the full TP marginal. Its extraction premise is an exact feasible
extension and its conclusion is a decomposition of the positively
repaired channel. Bose/PPT feasibility alone supplies neither a product
decomposition of the unperturbed point nor finite-level equality with
the exact QRC cone. The only precision implication asserted at level
52 is conditional on (5.10). Exact primal data, exact dual matrices and
their same-problem feasibility remain to be supplied before that
implication becomes a new endpoint.

For an exact original optimum, the QJM Convention 6.3 alternative
still requires global $B_y(a)\succeq0$ for every real preparation
vector $a$, with all event multipliers and all three TP multipliers
on the same channel, and a legal attaining port. At equality, active
event eigenspaces and every positive-weight atom kernel must match.
A finite extension dual can give a necessary lower through (2.4);
it does not prove an unrelated proposed global $B_y$ positive or
identify its zero support. An unperturbed extraction instead requires
an independent valid separability/extraction premise. No such premise
for the outer optimizer is supplied here. The old-port obstruction
(6.1) prevents treating positive noise as a boundary-preserving
replacement for either obligation.

The genuine Bose-support and half-PPT conditions of NOP, the summed
TP marginal, and the joint walk covariance are distinct mathematical
conditions. In particular they do not impose independent fixed-point
equations or normalizations on each product factor. Low-dimensional
PPT sufficiency, an objective involving a joint reference, or a
different measurement norm cannot replace these conditions. The QPC
§9 counterexamples to full orthogonal menu invariance, real rank-one
decomposition of an unchanged real Choi matrix, and characterwise
rank-preserving Kraus decomposition remain applicable. The argument
uses separate-transpose invariance of the whole selected state and
the proved replacement, not one of those stronger shortcuts.

Finite algebraic coefficients, finitely many scalar flags, and
whole-block CPTP decoding are the resources described by the port
construction. Coefficient synthesis, finite-precision robustness,
preparation acquisition, clocks, storage duration and transport are
separate resources without bounds here. The extension tensors and
quadrature identities grant no additional future action. The exact
original value, a matching global certificate and optimal port,
the $q=2,3,4$ values, the native preparation bridge, native cofinality
and memory rates, and the broader mutual-recovery relations among
space, time, boundary and memory remain unresolved by this conditional
alternative.

## 追加锚（本行以下为增补区）
