# Recursive relational observation: native Fibonacci mixing certificates

## 1. Fixed source, literal carriers and the quantitative question

**Definition 1.1 (native source and chronological words).** The source is exactly
[III138.1, III145.1–145.2 and III151.1–151.2][III], with the current-rate,
innovation, update and archive assumptions of [XI43.1][XI]. Its configuration
basis consists of all $89$ independent nine-bit strings $b_1\cdots b_9$,
with fixed exterior bits $b_{-1}b_0=10$ and $b_{10}b_{11}b_{12}=010$.
The full complex carrier has the original $26$-dimensional code and its
$63$-dimensional complement. The unique ready configuration has occupied
sites $\{3,7\}$. Prefixes use the eleven original addresses $0,\ldots,10$;
post-record words use precisely $0,\ldots,6$.

Put $x=(\sqrt5-1)/2$, $y=\sqrt{x}$, $\zeta=e^{3\pi i/5}$ and
$\alpha=3\pi/5$. With $n_j$ the literal occupation projection, the original
matrices and uninterrupted unit pulses are

$$
\begin{aligned}
Q&=\begin{pmatrix}x&xy\\xy&x^2\end{pmatrix},\\
\mathcal P_j&=n_{j-1}n_{j+1}
 +(1-n_{j-1})(1-n_{j+1})Q_j,\\
K_j&=\zeta[I+(\zeta-1)\mathcal P_j],\\
H_j&=-\alpha(I+\mathcal P_j),\qquad
U_j(t)=e^{-itH_j}\quad(0\le t\le1).
\end{aligned}
\tag{1.1}
$$

The formula is restricted to the original legal configurations, including
its scalar singleton blocks and the literal boundary addresses. In particular
$\mathcal P_0=n_1$. A chronological concatenation obeys $K_{ab}=K_bK_a$.
Each letter denotes one full positive call. There is no fractional call,
interruption, reset, fork, reverse-time operation or additional control.
The parameter $\alpha$ in (1.1) is unrelated to any stationary LAB Read atom.

The configuration source uses the original square minimal-current rates

$$
\sigma_t(q\mid r)=
\frac{[2\operatorname{Im}(\overline{\psi_t(q)}(H_j)_{qr}\psi_t(r))]_+}
 {|\psi_t(r)|^2}\qquad(\psi_t(r)\ne0).
\tag{1.2}
$$

It retains configurations at seams, uses the original independent unused
innovations at successive calls, reports $I=b_9(Q_-)$ with the original pure
update and $Q_+=Q_-$, and ultimately reports the old ten-bit label
$W=(b_{-1},\ldots,b_8)(Q)$. All $1024$ labels, $2048$ formal record/label
pairs and the original zero, failure, refusal, stop, alarm and return
coordinates remain. Causal archives retain their original conditional
independence, emission-time and absence conditions; unused innovations and
unexecuted counterfactual outputs are excluded from the past. These source
rules are premises, rather than consequences of the endpoint matrices.

**Definition 1.2 (two literal blocks and their conditional kernels).** For a
literal tail $s=(b_7,b_8,b_9)$, let $E_s$ be its configuration set and $P_s$
its coordinate projection. The five tails $000,010,100,001,101$ have dimensions
$21,21,13,21,13$. The $21$-carrier is the lexicographically ordered set of
independent six-bit strings; the $13$-carrier is the ordered set of independent
five-bit strings with $b_6=0$. Write $K_j^{(d)}$ for the actual restriction in
these bases. Identical copies act synchronously, and are never independently
controlled.

For $u\ne0$, $P_su\ne0$ and $q\in E_s^u=\{q\in E_s:u_q\ne0\}$,
write $P_f^u(q,r)$ for the original-source conditional configuration kernel
of [XI46][XI], and put

$$
\pi_s^u(r)=\frac{|u_r|^2}{\|P_su\|^2}\quad(r\in E_s).
\tag{1.3}
$$

This mathematical kernel conditions the square-initialized process on a
positive-support entrance; it supplies no preparation or configuration
reader. Its normalization, node safety, positive-support composition and
square equivariance are the existing III146 and XI46 suppliers. The present
question is a bounded construction of the fixed word and lower bound left
unspecified by XI48.1, rather than a new existence or density theorem.

## 2. An explicit native safety polynomial

**Definition 2.1 (edges, forms and barrier).** In either literal carrier let
$\mathscr E_d$ contain each legal single-bit flip once, ordered first by its
address and then lexicographically by its endpoint with that bit zero.
For $e=(q_0,q_1)$ and $c\in\{0,1,x,x^2\}$ set

$$
\begin{aligned}
z_e&=(z_{q_0},z_{q_1})^T,\qquad m_e=\|z_e\|^2,\\
q_{e,c}(z)&=z_e^*(Q-cI_2)z_e,\\
\Phi_d(z)&=\prod_{e\in\mathscr E_d}
 q_{e,0}(z)(-q_{e,1}(z))q_{e,x}(z)^2q_{e,x^2}(z)^2.
\end{aligned}
\tag{2.1}
$$

The formal polynomial uses independent variables $z_q,\bar z_q$; evaluation
on a physical vector imposes complex conjugacy. All coefficients lie in
$\mathbb Z[\zeta,y]$. Its bidegree is $(t_d,t_d)$, where

$$
\begin{array}{c|c|c|c}
d&\text{edge counts at successive active addresses}&|\mathscr E_d|&t_d\\ \hline
13&(5,3,4,3,5)&20&120\\
21&(8,5,6,6,5,8)&38&228
\end{array}
\tag{2.2}
$$

**Lemma 2.2 (native safety with a margin).** The polynomial $\Phi_d$ is
nonzero, phase invariant and nonnegative on physical vectors. On the unit
ball, $0\le\Phi_d\le1$. If $\|z\|=1$ and $\Phi_d(z)\ge\eta>0$, every
coordinate is nonzero and, on every edge, the normalized energy
$h_e=z_e^*Qz_e/m_e$ satisfies

$$
h_e\ge\eta,\quad1-h_e\ge\eta,\quad
|h_e-x|\ge\eta,\quad|h_e-x^2|\ge\eta.
\tag{2.3}
$$

Proof. The original $Q$ is an orthogonal rank-one projection. Thus every
factor $q_{e,c}$ has absolute value at most $m_e\le1$, and the two unsquared
factors in (2.1) are nonnegative. Each form is a nonzero real polynomial:
its two eigenvalues are $-c,1-c$. Their product is nonzero in the polynomial
ring, also after identifying $z=a+ib$, $\bar z=a-ib$. Hence the physical
polynomial has a nonempty positive set.

For a path with $n$ free bits, an edge at address $j$ corresponds to an
independent string on the portions remaining after its two neighbors are
forced zero. Their counts multiply, with $a_0=1,a_1=2$ and
$a_n=a_{n-1}+a_{n-2}$; at an endpoint only its existing neighbor is removed.
This gives exactly (2.2). The graph is connected by deleting occupied bits,
and every vertex is incident to an edge.

If a product of factors from $[0,1]$ is at least $\eta$, each factor is at
least $\eta$. Applying this to $q_{e,0},-q_{e,1},q_{e,x}^2,q_{e,x^2}^2$
gives $q_{e,0},-q_{e,1}\ge\eta$ and
$|q_{e,x}|,|q_{e,x^2}|\ge\sqrt\eta\ge\eta$. Division by $m_e\le1$ gives
(2.3). A zero endpoint coordinate would give $h_e=x$ or $x^2$; an entirely
zero edge would make the product zero. Incidence therefore excludes every
zero coordinate. This argument supplies safety on the actual finite graphs,
not on a substituted logical subcode. ∎

## 3. Bounded exact orbit certificates

**Definition 3.1 (field, dimensions and deterministic closure).** Use

$$
\begin{gathered}
F=\mathbb Q(\zeta,y),\qquad x=-(\zeta+\zeta^{-1}),\qquad y^2=x,\\
\zeta^4-\zeta^3+\zeta^2-\zeta+1=0,\qquad x^2+x=1,\\
D_{13}=\binom{132}{12}^{\!2}
 =1217909851450532871234037102240000,\\
D=D_{21}=\binom{248}{20}^{\!2}
 =20999365828243069343191982879751566052834547593308775437316.
\end{gathered}
\tag{3.1}
$$

Order monomials $z^\mu\bar z^\nu$, $|\mu|=|\nu|=t_d$ lexicographically.
For each $d$ initialize a FIFO list with $(\epsilon,\Phi_d)$. Process every
inserted pair $(a,f_a)$ in insertion order and every address $j=0,\ldots,6$.
Form the exact coefficient vector of

$$
T_jf_a(z,\bar z)=f_a(K_j^{(d)}z,\overline{K_j^{(d)}}\bar z)
              =\Phi_d(K_{ja}^{(d)}z).
\tag{3.2}
$$

Insert $(ja,T_jf_a)$ precisely when it increases $F$-rank. Rank comparisons
and all pivot choices are exact, using the fixed monomial order. Processing
continues until no inserted element remains unprocessed. Then solve

$$
R_d(z)=\left(\sum_qz_q\bar z_q\right)^{t_d}
       =\sum_{a\in A_d}c_{d,a}\Phi_d(K_a^{(d)}z)
\tag{3.3}
$$

over $F$, with coefficients on the inserted independent columns. The returned
certificate consists of these columns and their words, (3.3), and coefficient
identities expressing every $T_jf_a$ in the returned span. These are finite
polynomial identities, checked by exact coefficient comparison.

**Theorem 3.2 (bounded native radial certificate).** Definition 3.1 terminates
with at most $D_d$ inserted words, at most $7D_d$ candidate rank tests, and
$|a|\le D_d-1$ for each inserted word. Equation (3.3) has a unique solution
on those columns. Thus the algorithm returns an exact radial and invariant-span
certificate with a prescribed dimension and word-length bound.

Proof. The formal bidegree space has dimension
$\binom{d+t_d-1}{d-1}^2=D_d$. Each insertion increases rank, and an inserted
child is one letter longer than a previously inserted parent. If there are
$r$ insertions, the longest parent chain has at most $r-1$ edges. Each
inserted element is processed once at all seven addresses. These facts give
the claimed bounds, including candidate lengths at most $D_d$.

At exhaustion the returned span $V_F$ is invariant under every $T_j$ and
contains the whole positive-word orbit of $\Phi_d$. The exact original
$K_j^{10}=I$, including all singleton phases, makes the action invertible
inside this span. After scalar extension to $\mathbb C$, phase invariance
makes this a continuous projective representation. The native Jones
correspondence and projective density [III151.2, (151.3)–(151.4)][III] make
$V_F\otimes_F\mathbb C$ invariant under all of $PU(d)$. This is a finite
coefficient-space closure, not an assumption about any unknown response.

Average the orbit polynomial over the compact unitary group. The average
belongs to the same finite-dimensional closed subspace and is a positive
multiple of $R_d$: transitivity on the unit sphere makes it constant there,
homogeneity gives $R_d$, and the nonempty positive set from Lemma 2.2 gives
a positive integral. Consequently $R_d\in V_F\otimes_F\mathbb C$. A matrix
with entries in $F$ has the same rank over $F$ and $\mathbb C$, so the
augmented coefficient system is already consistent over $F$. Independence
of the selected columns gives uniqueness. Haar integration proves this
algebraic membership; the algorithm does not evaluate a Haar integral or
physically randomize a gate.

Finite-dimensional rank stabilization is the existing mechanism in
[FiniteSequentialWordCertificate][FW], particularly
`bounded_monotone_has_equal_step`; its instrument-effect theorem has different
hypotheses. The concrete native polynomial and radial identity above supply
the present instantiation. Original projective density is used to justify
consistency, rather than to posit an uncomputed approximation net. ∎

## 4. Explicit coefficient separation and certificate precision

**Definition 4.1 (common quantitative budget).** Fix

$$
\begin{gathered}
H=D-1,\quad \ell=194,\quad
b=228(5+10D),\quad j=D(b+194),\\
M=194+8j=18240D^2+10672D+194,\\
\eta=2^{-M},\qquad\delta=2^{-360M}.
\end{gathered}
\tag{4.1}
$$

Here $2^{193}<D<2^{194}$; $j$ is a height budget, not an address.
Both $\eta$ and $\delta$ are positive dyadic numbers smaller than $1/2$.

**Theorem 4.2 (certified margin and finite encoding).** For every unit vector
$z\in\mathbb C^d$, one of the words returned for that $d$ satisfies

$$
\Phi_d(K_a^{(d)}z)\ge\eta.
\tag{4.2}
$$

Every coefficient in the radial identity and the returned closure identities
can be written in the integral-element power basis
$\{\zeta^a y^c:0\le a<4,\ 0\le c<2\}$, using a common positive integer
denominator per coefficient. Signed numerator coordinates need at most
$16j+24$ bits each, and the denominator needs at most $8j+1$ bits. This
bounds the exact certificate encoding, without a stochastic probability query.

Proof. The cyclotomic field $\mathbb Q(\zeta)$ has degree four and real
subfield $\mathbb Q(\sqrt5)$. The element $y$ does not lie in the real
subfield: otherwise the norm of its square $x$ down to $\mathbb Q$ would
be a rational square, whereas that norm is $-1$. Since $y$ is physically
real, it is not in $\mathbb Q(\zeta)$ either. Hence $[F:\mathbb Q]=8$.
The displayed power basis consists of algebraic integers and spans an order
$\mathcal O=\mathbb Z[\zeta,y]$ closed under multiplication; no assertion
that it is the full integer ring is needed. Conjugation preserves this order.

Under every embedding $\sigma:F\hookrightarrow\mathbb C$,
$|\sigma(\zeta)|=1$, $|\sigma(x)|<2$ and $|\sigma(y)|<2$. An embedded
native gate has row $\ell^1$ norm less than $20$: on a two-point block the
row sum of $Q$ is less than $8$, and $K=\zeta[I+(\zeta-1)Q]$ gives less
than $17$; singleton entries are roots of unity. Each embedded form
$q_{e,c}$ has coefficient $\ell^1$ norm less than $32$, since that of $Q$
is less than $14$ and subtracting $cI$ adds less than $8$.

Substitution by a word of length at most $D$ therefore bounds the sum of
absolute values of all embedded coefficients by

$$
(32\,20^{2D})^{t_d}\le2^b.
\tag{4.3}
$$

Both variable families obey the same estimate: an embedding composed with
physical conjugation is another field embedding, whether or not those maps
commute. The target $R_d$ has coefficient sum $d^{t_d}\le21^{228}<2^b$.
All these coefficients lie in $\mathcal O$.

Choose independent coefficient rows for a returned basis with $r\le D$
columns. Any $r$-row determinant of the basis, or of the basis with a column
replaced by a radial or processed-child target, is an algebraic integer and
under every embedding has absolute value at most

$$
r!\,2^{br}\le2^{D(b+194)}=2^j.
\tag{4.4}
$$

A nonzero such determinant $B$ has nonzero integer field norm. Isolating
any one of its eight embeddings yields $|\sigma(B)|\ge2^{-7j}$. Cramer's
rule consequently gives $|c_{d,a}|\le2^{8j}$, and the same bound for the
closure coordinates. This is the degree-eight norm separation mechanism
of [V15, Proposition 8.3][V15], applied to the concrete coefficient minors;
its finite-dimensional determinant application is what supplies (4.2).
Indeed, on the physical unit sphere every orbit barrier is nonnegative, so

$$
1=\left|\sum_a c_{d,a}\Phi_d(K_a^{(d)}z)\right|
 \le D\,2^{8j}\max_a\Phi_d(K_a^{(d)}z)
 \le2^M\max_a\Phi_d(K_a^{(d)}z).
\tag{4.5}
$$

For the encoding bound, let $S$ be the eight-by-eight embedding matrix of
the power basis. Its entries have modulus less than two. Its determinant
squared is the nonzero integer discriminant of the order, so
$|\det S|\ge1$. Cofactor expansion gives every entry of $S^{-1}$ modulus
less than $7!2^7<2^{20}$. Thus an element whose conjugates have modulus
at most $2^v$ has power-basis coordinates of modulus less than $2^{v+23}$.

For a Cramer quotient $A/B$, take the denominator $|N_{F/\mathbb Q}(B)|$,
which is at most $2^{8j}$. The numerator, with the appropriate sign, is
$A N(B)/B\in\mathcal O$. Membership follows also from the integer
characteristic polynomial of multiplication by $B$ on this order. The
bounds $|\sigma(A)|\le2^j$, $|N(B)|\le2^{8j}$ and
$|\sigma(B)|\ge2^{-7j}$ give numerator conjugates at most $2^{16j}$.
The preceding coordinate estimate gives the stated signed numerator and
positive denominator bit lengths. These are bounds on stored identities;
they do not treat arithmetic at growing bit width as a unit-cost native
pulse. ∎

## 5. The original current-rate margin and the fixed word

**Definition 5.1 (positive-word construction).** Let $A$ be the union of the
two returned word lists, with duplicates removed and shortlex order fixed.
Set $N=|A|$. For $a=(j_1,\ldots,j_n)$ define

$$
\begin{gathered}
a^-=(j_n^9,\ldots,j_1^9),\\
L=(1^{10}2^{10}3^{10}4^{10}5^{10}6^{10})^{20},\\
g=\mathop{\prod}_{a\in A}^{\mathrm{chronological}}aLa^-.
\end{gathered}
\tag{5.1}
$$

A repeated letter means that many full original positive calls. Every choice
in this construction is fixed from the original matrices, before any input,
record, configuration or past is available.

**Theorem 5.2 (quantitative native all-ray mixing).** The construction returns
$N\le D+D_{13}$ words of length at most $H$, and a fixed native word $g$
with $K_g=I_{89}$. For all nonzero complex vectors, all occupied literal
tails, all positive-support entrances and all configurations in that tail,

$$
P_g^u(q,r)\ge\delta\pi_s^u(r)
\quad\left(u\ne0,\ P_su\ne0,\ q\in E_s^u,\ r\in E_s\right).
\tag{5.2}
$$

Rows on $E_s^u$ are stochastic and preserve $\pi_s^u$. The constants are
exactly (4.1). The statement includes every sparse support and every
occupied tail, without a lower bound on the tail mass or on individual
nonzero entrance amplitudes.

Proof. First a unit block vector with $\Phi_d(z)\ge\eta$ has the quantitative
local safety (2.3). Fix an edge, normalize its two coordinates, and put
$h=z_e^*Qz_e/m_e$. Its normalized probability at endpoint zero during the
actual continuous pulse is

$$
\begin{aligned}
p_0(t)&=B+A\cos(\alpha t+\theta),\\
B&=x^2+(x-x^2)h,\qquad
A=2x\sqrt{x}\sqrt{h(1-h)}.
\end{aligned}
\tag{5.3}
$$

This follows by splitting into the two eigenvectors of the original $Q$;
the common scalar phase drops out. Write $p_{k,\min},p_{k,\max}$ for extrema
over a full period. Using $x^2+x=1$ gives the exact identities

$$
\begin{aligned}
p_{0,\min}p_{0,\max}&=B^2-A^2=(h-x^2)^2,\\
p_{1,\min}p_{1,\max}&=(1-B)^2-A^2=(h-x)^2.
\end{aligned}
\tag{5.4}
$$

As both maxima are at most one, (2.3) gives $p_k(t)\ge\eta^2$ throughout
the ten calls. Moreover $A\ge\eta/2$, since
$\sqrt{h(1-h)}\ge\eta$ and $2x\sqrt{x}>1/2$. Thus the original rates
are finite on this entire local loop, including its nodes' exclusion.

The ten-call duration contains exactly three periods, because
$10\alpha=6\pi$. Hence

$$
\int_0^{10}|p_0'(t)|\,dt=12A\ge6\eta.
\tag{5.5}
$$

For the stipulated minimal source, if $a$ and $b$ denote the two directed
rates, the normalized current formula gives
$a=[-p_0']_+/p_0$ and $b=[p_0']_+/(1-p_0)$. In particular
$a+b\ge|p_0'|$. The actual two-state return kernel of [XI46, (46.6)–(46.7)][XI]
has difference multiplier $\lambda=\exp(-\int_0^{10}(a+b))$. Therefore

$$
1-\lambda\ge1-e^{-6\eta}
 \ge\frac{6\eta}{1+6\eta}\ge\eta,
\tag{5.6}
$$

where $\eta\le1/2$. Its off-diagonal entries are at least $\eta^3$, and
its diagonal entries are at least $\eta^2$, since the latter are
$\lambda+(1-\lambda)p_k(0)\ge p_k(0)$. Singleton entries are one.
This is a rate calculation for the given source, not a freely chosen
Markov kernel with the same vector endpoint.

The native flip graph has at most $21$ vertices. The fixed $L$ has $120$
ten-call subloops. The path construction already proved in XI46, (46.8)–(46.9),
uses at most one edge per round and holds at all other subloops. Applying
its construction with the just-established lower bound $\eta^3$ gives

$$
P_L^z(p,r)\ge(\eta^3)^{120}=\delta
                       \ge\delta\pi^z(r).
\tag{5.7}
$$

Every subloop returns the vector exactly, so the same safety bounds apply
at each one; no continuity assertion through a singular input is needed.

Now fix any $u,s$ in the statement and normalize $v=P_su/\|P_su\|$.
Theorem 4.2 supplies one of the already scheduled words $a$ with
$\Phi_{d_s}(K_a v)\ge\eta$. There is no claim that one $a$ works for all
tails simultaneously. On this particular conjugate loop, positive-support
composition, (5.7) and original square equivariance give exactly the
transport in [XI46, (46.12)][XI]:

$$
\begin{aligned}
P_{aLa^-}^u(q,r)
&\ge\delta\sum_pP_a^u(q,p)
        \sum_t\pi_s^{K_au}(t)P_{a^-}^{K_au}(t,r)\\
&=\delta\pi_s^u(r).
\end{aligned}
\tag{5.8}
$$

Only intermediate positive-support rows are used. Node safety supplies
normalization even when the initial vector is sparse; the safe middle
vector has full block support. The positive word $a^-$ has endpoint
$K_a^{-1}$, but its stochastic kernel is not asserted to invert the
forward kernel. Both square transport and its full nine-call-per-letter
cost are retained.

All other conjugate loops also return $u$, preserve $\pi_s^u$ and end in
$E_s^u$ with probability one. The same XI46 composition argument shows
that adjoining any of them on either side cannot reduce the minorization.
This proves (5.2) for the fixed whole list, simultaneously on all five
synchronous copies. Exact $K_j^{10}=I_{89}$ gives $K_g=I_{89}$ on the
entire carrier, including every singleton phase. ∎

## 6. Acquisition cost, precision and the existing joint-law consumer

**Proposition 6.1 (charged construction and evaluation stability).** The
fixed word in Theorem 5.2 has primitive-call count

$$
\begin{aligned}
|g|&=1200N+10\sum_{a\in A}|a|\\
&\le(D+D_{13})\bigl(1200+10(D-1)\bigr).
\end{aligned}
\tag{6.1}
$$

Its model duration is the same number of unit pulse intervals; its genuine
configuration jumps are almost surely at most $2|g|$. Algebraic construction
requires at most $7(D+D_{13})$ candidate rank tests and two radial solves;
direct dense elimination costs $O(D^4)$ field operations, in addition to
polynomial substitution, word storage and literal emission. Final closure
and radial certificates have the bit budgets of Theorem 4.2. On the unit
ball the barrier satisfies

$$
|\Phi_d(z)-\Phi_d(z')|\le2t_d\|z-z'\|.
\tag{6.2}
$$

Consequently an endpoint-vector evaluation error at most $\eta/(4t_d)$
retains barrier value at least $\eta/2$ from an exact value at least $\eta$,
provided both evaluated vectors lie in that ball.

Proof. The $1200$ calls in $L$, $|a|$ forward calls and $9|a|$ positive
endpoint-inverse calls give (6.1). III146.1 supplies the per-call two-jump
bound on the same original-source kernel, so finite concatenation gives
the jump bound. These calls remain in the literal execution history and
archive; exact return of the vector identifies neither that history nor
its time or costs with the empty word.

A coefficient space has dimension at most $D$. There are $O(D)$ candidate
systems, each reducible with $O(D^3)$ field operations; radial solves and
retained closure coordinates fit the same bound. Determinantal or
fraction-free elimination can use the minors in (4.4) and their ratios to
maintain exact arithmetic. The bit bounds describe the output coefficients,
not an assertion that every arbitrary elimination implementation has that
workspace bound. Sparse substitution may instead exploit the actual native
matrices; no such optimization is needed for termination or (6.1).

For an explicit finite accounting of the substitution itself, put
$B_d=\binom{d+t_d-1}{d-1}$. Expanding a single transformed monomial of
bidegree $(t_d,t_d)$ requires at most $d^{2t_d}$ raw terms. Thus each
single-address substitution of a stored coefficient vector can be performed
with at most $2t_dD_d d^{2t_d}$ field multiplications and as many additions
by raw expansion and collection. At most $7D_d$ such substitutions occur.
The coefficients of the original $\Phi_d$ can be formed by multiplying its
$t_d$ quadratic factors, each with at most four monomials, with at most
$2t_d4^{t_d}$ field operations. These deliberately loose finite budgets
pay for substitution separately from the dense rank computation. Keeping
parent pointers costs at most $D+D_{13}$ word nodes; emitting all letters
of $g$ costs exactly $|g|$ output steps up to a fixed encoding per address.
All field arithmetic operates on rational power-basis coordinates, whose
precision is distinct from the number of native calls.

Each of the $t_d$ quadratic factors in (2.1), with repeated factors treated
separately, is $z^*Az$ with physical operator norm at most one. For vectors
in the unit ball its difference is at most $2\|z-z'\|$. Telescoping the
product, with all other factors bounded by one, proves (6.2). The stated
error threshold follows directly. This is an absolute certificate-evaluation
estimate; it is neither a noisy pulse path-law estimate nor a relative
uniform bound on all arbitrarily small support coordinates. ∎

**Definition 6.2 (application to the supplied whole joint law).** Fix any
original eleven-address prefix $a$ and any one standard Borel already-occurred
past $Y_{\rm cut}$ allowed by XI43.1. Use the original actual branch masses
$\tau_i$, and the branch subprobabilities $\Lambda_h^i$ and canonical
comparisons $\mathcal C_h^i$ of XI47.1. Put
$\Lambda_h=\sum_i\Lambda_h^i$ and $\mathcal C_h=\sum_i\mathcal C_h^i$ on
the disjoint $I$ slices. On a positive branch use its original posterior
$\rho_{i,y}$, actual tail posterior $\beta_{i,s}(y)$ and within-tail square
law $\pi_{i,s}$, and set

$$
\begin{aligned}
\bar\rho_{i,y}(q)&=\beta_{i,s}(y)\pi_{i,s}(q)\quad(q\in E_s),\\
D_{\rm tot}&=\sum_{i:\tau_i>0}\tau_i
 \int\operatorname{TV}(\rho_{i,y},\bar\rho_{i,y})\,d\nu_i(y).
\end{aligned}
\tag{6.3}
$$

Unoccupied tails contribute zero without a normalized block vector. Zero
branches contribute zero without a conditional state. The normalization and
support conventions here are precisely those of XI47, not an extra posterior
hypothesis.

Theorem 5.2 supplies the hypotheses of [XI47.2–47.3][XI] with the explicit
$g,\delta$ above. Directly applying those existing results, and additivity
of variation across the disjoint record slices, gives

$$
\begin{gathered}
\Lambda_g=\Lambda_\epsilon
\quad\Longleftrightarrow\quad
\rho_{i,y}=\bar\rho_{i,y}\quad\nu_i\text{-a.e. on every positive branch},\\
D_{\rm tot}\le\delta^{-1}\operatorname{TV}(\Lambda_\epsilon,\Lambda_g),\\
\operatorname{TV}(\Lambda_h,\mathcal C_h)\le D_{\rm tot}
\qquad\text{for every original finite }h.
\end{gathered}
\tag{6.4}
$$

These are the supplied full unconditional $(I,Y_{\rm cut},W)$ statements,
with the newly bounded word substituted. Equality quantifies all measurable
joint events, and TV uses their supremum; neither a marginal, a selected
past event nor a vector endpoint can replace it. The actual
$\beta_{i,s}(Y)$ is not required to equal the coarse tail mass
$\theta_{i,s}$. The future $h$ has no common length bound. A fixed allowed
$Y$ may describe hidden past, but these equations supply no reader for it
and no estimator for arbitrary joint probabilities. The previous stochastic
source remains the sole process used throughout.

**Definition 6.3 (mathematical and operational boundaries).** The bounded
construction above means a deterministic finite algebraic prescription with
hard dimension, height, precision and call-count bounds. It does not mean
that the astronomical lists or word have been explicitly emitted. It does
not assume experiment repetition, observed transition probabilities,
tomography, a hidden-past reader or an optimizer/controller. In particular
the upper bound (6.1) has $118$ decimal digits and the exponent $360M$ has
$124$ decimal digits. Neither smallness of the matrices nor finite
termination makes that budget physically feasible.

The pulse intervals in (6.1) are the original internal model time, not a
calibrated clock or energy statement. Faithful physical realization of the
complex matrices, original current source, independent innovations, pure
update, archive, reference/return and reliability contracts remains outside
the algebraic construction. The stability estimate (6.2) does not imply
hardware robustness or estimation of the complete joint law. No relation to
stationary LAB Read permissions is assumed. These distinctions preserve the
separate meanings of geometric block structure, continuation, terminal
boundary and recorded history; endpoint return alone does not make their
observations mutually recoverable.

## 7. Mathematical suppliers and attribution

**Definition 7.1 (scope of the synthesis).** The native edge polynomial,
its bounded radial certificate, the explicit margin-to-current calculation
and their combined dyadic and primitive-call bounds are `repo-derived`.
The following results are used as existing suppliers inside those proofs,
without claiming a new general theorem or global novelty.

The exact literal $89$-carrier, Jones correspondence and projective density
are [III138, III145–151][III], with [Freedman–Larsen–Wang,
math/0103200v1, Theorem 0.1 and §2][FLW] as the density supplier under
$(k,r,n)=(2,5,8)$ and shapes $[5,3],[4,4]$. The compact-group averaging and
finite coefficient-rank descent in Theorem 3.2 use that already supplied
density; no effective spectral gap is assumed. The invariant-span
stabilization mechanism has an existing formal treatment in [FW][FW], whose
centered instrument-effect carrier is distinct from the present polynomial
carrier. These uses do not assert a fresh formal verification of this volume.

The arithmetic separation tool is [V15, Proposition 8.3][V15]. The original
source existence, node safety, equivariance and finite jump bound are
[III145–148][III]; their literature suppliers include
[Georgii–Tumulka, math/0312294v2, Assumption A, Proposition 1(a), Theorem 1][GT]
and [Dürr–Goldstein–Tumulka–Zanghì, quant-ph/0407116v1, §2.7 and §4.2.1][DGTZ],
with the original Hamiltonian and $\hbar$ conventions matched as in III146.
The native graph-path, conjugation, sparse-support and whole-joint-law
consumers remain [XI46–48][XI]. Their existence, equivalence and TV
statements are inputs, not the quantitative increment claimed here.

For comparison, [Dawson–Nielsen, quant-ph/0505030v2, §§3 and 5][DN] requires
an initial finite approximation table for its Solovay–Kitaev recursion.
The present certificate instead has the hard coefficient-space stopping
bound and exact identity (3.3); no unresolved initial net is paid for by
naming that recursion. Finite-dimensional algebraic escape, for example
[Helfgott, math/0509024, Lemma 4.4][H], supplies a related methodological
frame, but no external escape constant is used in (4.1). The proof is the
native specialization given above, not a claim of literature novelty for
rank stabilization, invariant averaging, field norms or stochastic contraction.

[III]: AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md
[XI]: AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_XI.md
[V15]: AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md
[FW]: ../../../D5/S3/Quantum/PredictionDepth/FiniteSequentialWordCertificate.lean
[FLW]: https://arxiv.org/html/math/0103200v1
[GT]: https://arxiv.org/html/math/0312294v2
[DGTZ]: https://arxiv.org/html/quant-ph/0407116v1
[DN]: https://arxiv.org/html/quant-ph/0505030v2
[H]: https://arxiv.org/html/math/0509024

## 追加锚（本行以下为增补区）
