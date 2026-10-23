# Recursive relational observation: quantum-port covariance and a certified frontier

**Convention (Problem).** The approximate quantum-port problem is that of
[QMB, Convention 5.2](https://github.com/the-omega-institute/trureturing/blob/0bfa84f27ca531cca721a1c90d35ded2a51c0738/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md).
Its preparation, actual future protocols and fixed-port class are specified
in §1. The four nontrivial exact frontier values and minimizing Kraus tuples
remain undetermined.

## 1. Preparation, histories and fixed ports

**Assumption 1.1 (Independent quantum preparation).** Let
$\mathcal H=\mathbb C^5$ with ordered unit basis
$\mathsf S=(N,2,3,5,25)$ and projections $\Pi_s=e_se_s^\dagger$.
All complex density matrices on this space are allowed inputs. The label $N$
denotes a unit vector, not a zero vector, absence of a read, or Stop. Set

$$
K=\begin{pmatrix}
0&1&1&1&0\\
1&0&0&0&1\\
1&0&0&0&0\\
1&0&0&0&1\\
0&1&0&1&0
\end{pmatrix},\qquad U(t)=e^{-itK},\quad t\ge0.
$$

This is exactly QMB Assumption 1.1, an independent preparation hypothesis.
It is not a construction of quantum states from the native $\alpha/\beta$
tree, and it is not the different tensor-cut source.

**Definition 1.2 (Actual future protocols).** The future menu consists of
nonnegative waits $U(t)$, the complete five-outcome rank-one Lüders instrument
$\mathcal J_s(X)=\Pi_sX\Pi_s$, and Stop. Each adaptive protocol has finite
depth; all finite depths are included. Outcomes, chosen controls and stops
belong to the retained history. Initial controls and any random control
resources are independent of the source. Comparisons use the same policy.

There are no independent mode phases, arbitrary future unitaries, source
copies, resets, external quantum side information, probability oracle, or
readable hidden Kraus index. An event obtained by grouping the five recorded
outcomes is classical postprocessing of that full read. It does not authorize
a coarse-block Lüders instrument.

**Definition 1.3 (One fixed port).** For $1\le q\le5$, $\mathfrak C_q$ consists
of channels $T=\operatorname{Dec}\circ\operatorname{Enc}$ with a finite fixed
flag set $F$ and fixed CPTP maps

$$
\begin{aligned}
\operatorname{Enc}&:M_5\longrightarrow\bigoplus_{f\in F}M_q,\\
\operatorname{Dec}((Y_f)_f)&=\sum_f\operatorname{Dec}_f(Y_f),\qquad
\operatorname{Dec}_f:M_q\longrightarrow M_5.
\end{aligned}
$$

Every $\operatorname{Dec}_f$ is CPTP on its whole block. The design precedes
the unknown input and the choice of future protocol. Every quantum path goes
through this port: no original-input retention, entangled assistance or
bypass is allowed. Finite classical flags are free in the $q$ criterion;
their values can depend on the input, are used in decoding, and are not
additionally exposed to the later policy. Competitors are arbitrary complex
CPTP designs, with no assumed unitality, real Kraus operators, covariance,
projection form, or protocol dependence.

For the retained-history laws $P_\rho^\pi$, define

$$
e(T)=\sup_{\rho\in\mathcal D(\mathcal H)}\sup_{\pi\text{ actual, finite}}
\operatorname{TV}(P_\rho^\pi,P_{T(\rho)}^\pi),\qquad
\varepsilon_q=\inf_{T\in\mathfrak C_q}e(T).
\tag{1.1}
$$

The replacement occurs once, before the common future protocol. Total
variation is half the $\ell^1$ difference, or its measure-theoretic extension
for randomized controls. This is a system-menu criterion. CPTP legality is
required on all reference extensions, but the performance test includes no
joint-reference measurement and is not defined by trace or diamond distance.

**Convention 1.4 (Passive coordinates).** Use exactly the QMB frame

$$
\begin{gathered}
D=\operatorname{diag}(1,i,i,i,1),\qquad
A=-iD^\dagger KD=
\begin{pmatrix}
0&1&1&1&0\\
-1&0&0&0&-1\\
-1&0&0&0&0\\
-1&0&0&0&-1\\
0&1&0&1&0
\end{pmatrix},\\
O(t)=e^{tA}=D^\dagger U(t)D,\qquad
Q_J(t)=O(t)^T\Pi_JO(t),\qquad \Pi_J=\sum_{s\in J}\Pi_s,\\
E_J(t)=DQ_J(t)D^\dagger,\qquad
\widehat T(X)=D^\dagger T(DXD^\dagger)D.
\end{gathered}
\tag{1.2}
$$

Thus $A^T=-A$ and $O(t)$ is real orthogonal. A superscript $T$ denotes
transpose in this frame; $\dagger$ denotes adjoint, or the trace-pairing dual
when applied to a map. The frame is a coordinate identification, not a new
future control. Below channel calculations are in this frame unless stated
otherwise, so $e(\widehat T)$ means the transported original criterion.

## 2. Source results and exact correspondences

**Convention 2.1 (QMB results used).** The QMB results are used in the
following forms.

| Supplier | Exact use here |
| --- | --- |
| QMB Theorem 2.1 | $e(T)=\sup_{t\ge0}\max_{J\subseteq\mathsf S}\|Q_J(t)-\widehat T^\dagger(Q_J(t))\|_{\rm op}$. |
| QMB Theorem 3.1 | A fixed finite-flag port has error $(5-q)/7$, including all complex inputs and histories. |
| QMB Theorem 4.1 | Two rotation planes, the dark line, weighted lengths and the complete weighted observation spectrum. |
| QMB Theorem 5.1 | The legal class is exactly the channels with rank-at-most-$q$ Kraus decompositions, equivalently the TP slice of the Schmidt-number-$q$ Choi body. It is compact and has a representation with at most $625$ flags. |
| QMB Theorem 5.1 and Convention 5.2 | $b_q:=7(5-q)/68\le\varepsilon_q\le u_q:=(5-q)/7$, with an attained minimum. Exact values for $q<5$ are unresolved. |

The first-read identity uses the actual instrument: after a first rank-one
outcome $s$, the conditional quantum state is $\Pi_s$ in both comparisons.
The common suffix is consequently a probability kernel depending on $s$ and
the retained controls. It cannot increase TV. A single wait, a full read and
Stop give the reverse inequality. This explains why the supplier covers every
finite adaptive depth and source-independent randomized policy, not just
single-read protocols.

For the supplied resource correspondence, write
$\widehat T(X)=\sum_i C_iXC_i^\dagger$. Rank at most $q$ is equivalent to
factorization through a $q$-block with a whole-block CPTP decoder, as realized
explicitly in Theorem 5.2 below. For the Choi convention use output first:

$$
\begin{gathered}
\Omega=5^{-1/2}\sum_j e_j^{\rm out}\otimes e_j^{\rm in},\qquad
w(C)=\sum_{i,j}C_{ij}e_i^{\rm out}\otimes e_j^{\rm in},\\
\chi_T=(\widehat T\otimes\mathrm{id})(\Omega\Omega^\dagger)
=\frac15\sum_i w(C_i)w(C_i)^\dagger,\qquad
\operatorname{Tr}_{\rm out}\chi_T=I_5/5.
\end{gathered}
\tag{2.1}
$$

The Schmidt rank of $w(C)$ is the complex matrix rank of $C$. Moreover,

$$
\operatorname{tr}(Q\widehat T(\rho))
=5\operatorname{tr}(\chi_T(Q\otimes\rho^T)),\qquad
\widehat T^\dagger(Q)
=5\bigl[\operatorname{Tr}_{\rm out}((Q\otimes I)\chi_T)\bigr]^T.
\tag{2.2}
$$

These identities are a representation of the system objective, not an added
entangled-input performance test. The marginal condition is essential; an
arbitrary low-Schmidt-number density matrix is not necessarily a channel.

The preparation and operation conventions are those of
[AURIC §§61, 63, 65, 73, 79](https://github.com/the-omega-institute/trureturing/blob/bcf8bc4317eb78b19f2d0f5076318bf3dc5a3324/docs/develop/theory/AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md):
independent complex preparation, this $K$, actual instruments, the passive
frame, histories, and whole-block flag decoding. The exact fifteen-dimensional
effect span in AURIC §65 is not an equality of approximate measurement norms.
The native
[GraftAffineClosure.step, quantity and run](https://github.com/the-omega-institute/trureturing/blob/9e834a13e0760767641dd65bbdcc92521589baf3/D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.lean)
describe composition pairs and chronological graft/step words. They do not
derive Assumption 1.1.

The channel convention in
[QuantumChannel](https://github.com/the-omega-institute/trureturing/blob/0bfa84f27ca531cca721a1c90d35ded2a51c0738/D5/S3/Quantum/Foundation/FiniteStateChannel.lean)
is a completely positive matrix map with trace preservation;
[finite_kraus_quantum_channel](https://github.com/the-omega-institute/trureturing/blob/0bfa84f27ca531cca721a1c90d35ded2a51c0738/D5/S3/Quantum/Foundation/FiniteKrausChannel.lean)
gives the channel associated to a finite family with
$\sum_iC_i^\dagger C_i=I$.
[finite_kraus_instrument_born_marginal](https://github.com/the-omega-institute/trureturing/blob/0bfa84f27ca531cca721a1c90d35ded2a51c0738/D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal.lean)
identifies branch trace and Born weight.
[unitary_kraus_mixing_invariance](https://github.com/the-omega-institute/trureturing/blob/0bfa84f27ca531cca721a1c90d35ded2a51c0738/D5/S3/QuantumChannels/UnitaryKrausMixingInvariance.lean)
preserves a sandwich sum under column-orthogonal mixing. These citations
concern complete positivity, trace preservation, branch probabilities and
Kraus-sum invariance. In particular, arbitrary Kraus mixing need not preserve
individual Kraus ranks.

## 3. Lossless walk stationarity and fifteen actual events

**lemma 3.1 (Recurrence and tail suprema).** There are times $r_n\ge n$ with
$\|O(r_n)-I\|_{\rm op}<1/n$. For every fixed CPTP $T$ and every $u\ge0$,

$$
\sup_{t\ge u}\max_J\|Q_J(t)-T^\dagger(Q_J(t))\|_{\rm op}=e(T).
\tag{3.1}
$$

Proof. For each positive integer $n$, the infinite sequence
$O(0),O(n),O(2n),\ldots$ lies in the compact orthogonal group. Two terms
$O(kn),O(\ell n)$ with $k>\ell$ are within $1/n$. Unitary invariance of
operator norm gives $r_n=(k-\ell)n\ge n$ and
$\|O(r_n)-I\|<1/n$. For each fixed $t\ge0$, therefore,
$Q_J(t+r_n)\to Q_J(t)$, with $t+r_n\ge u$ eventually. The finitely many
event residuals are continuous in their effect. Every value before $u$ is
thus a limit of tail values. The opposite inequality follows by inclusion
of the tail. The QMB first-read identity proves (3.1). $\square$

**Definition 3.2 (Stationarity).** Put
$\operatorname{Ad}_V(X)=VXV^\dagger$ and $\mathcal L_A(X)=AX-XA$.
A channel $S$ is walk-stationary when

$$
S\mathcal L_A=\mathcal L_AS.
\tag{3.2}
$$

Equivalently it commutes with every $\operatorname{Ad}_{O(t)}$: differentiate
at zero in one direction and exponentiate the linear operator $\mathcal L_A$
in the other. This is a condition on the stored-channel design.

**theorem 3.3 (No-worse stationary design).** For every legal complex
$T\in\mathfrak C_q$ there exists a walk-stationary
$S\in\mathfrak C_q$ with $e(S)\le e(T)$. It still has a fixed realization
with at most $625$ flags and whole-block CPTP decoders. Consequently, with
$\mathcal J_{15}=\{J\subseteq\mathsf S:1\le|J|\le2\}$,

$$
\boxed{
\varepsilon_q=
\min_{\substack{S\in\mathfrak C_q\\S\mathcal L_A=\mathcal L_AS}}
\max_{J\in\mathcal J_{15}}\|\Pi_J-S^\dagger(\Pi_J)\|_{\rm op}.}
\tag{3.3}
$$

For every stationary $S$, the displayed event maximum is exactly $e(S)$,
and some full mode read at wait zero attains its worst-case TV.

Proof. The supplied class $\mathfrak C_q$ is compact. It is convex because
concatenating scaled rank-at-most-$q$ Kraus families implements any finite
mixture. The error is convex, being a supremum of norms of affine functions
of the channel. It is continuous by QMB Theorem 5.1; alternatively the
difference of two such errors is bounded by the uniform output trace-distance
difference on density inputs.

For $u\ge0$ let
$T_u=\operatorname{Ad}_{O(u)}T\operatorname{Ad}_{O(-u)}$.
Its Kraus family $O(u)C_iO(-u)$ has the same ranks and is TP. Direct duality
and conjugation by $O(-u)$ give

$$
\|Q_J(t)-T_u^\dagger(Q_J(t))\|_{\rm op}
=\|Q_J(t+u)-T^\dagger(Q_J(t+u))\|_{\rm op}.
\tag{3.4}
$$

Lemma 3.1 proves $e(T_u)=e(T)$ for the actual nonnegative-wait menu.
No negative wait has been added to a future protocol: the inverses here
appear only in allowed mathematical CPTP design transformations.

Let $\mathcal G$ be the closure of $\{O(t):t\ge0\}$ in $O(5)$.
Products remain in this closure. Recurrence gives
$O(r_n-t)\to O(-t)$ for each fixed $t\ge0$, so it contains the inverses
of the actual orbit and, by continuity, of its closure. It is a compact
group. Equation (3.4), recurrence, and continuity in the conjugating matrix
give $e(\operatorname{Ad}_gT\operatorname{Ad}_{g^{-1}})=e(T)$ for every
$g\in\mathcal G$.

Take the normalized Haar average

$$
S=\int_{\mathcal G}\operatorname{Ad}_gT\operatorname{Ad}_{g^{-1}}\,dg.
\tag{3.5}
$$

Finite convex mixtures approximate this integral in the finite-dimensional
channel space. Compactness and convexity put $S$ in $\mathfrak C_q$, and
convexity and continuity give $e(S)\le e(T)$. Haar invariance implies that
$S$ commutes with $\operatorname{Ad}_g$, hence with the walk and its
generator. The supplied finite-support theorem replaces the averaged
channel by at most $625$ rank-restricted Kraus terms. There is no continuous
flag in its realization and no requirement to implement averaging physically.

For stationary $S$, its dual commutes with the same conjugations and

$$
Q_J(t)-S^\dagger(Q_J(t))
=O(t)^T\bigl(\Pi_J-S^\dagger(\Pi_J)\bigr)O(t).
\tag{3.6}
$$

The norm is independent of $t$. Since $S^\dagger(I)=I$, complementary
events have opposite residuals; empty and full events have zero residual.
The five singletons and ten pairs therefore represent every event test.
This gives exactly the fifteen tests in (3.3), without claiming that fifteen
is a minimal necessary number of independent constraints.

The stationary class is a closed subset of the compact legal class. It is
nonempty, for the completely depolarizing channel is stationary and has
rank-one Kraus operators. Its minimum exists. The no-worse construction and
the inclusion of stationary channels in the original class prove equality
of the two minima.

Finally choose a maximizing event $J$ and a unit eigenvector $v$ of
$\Pi_J-S^\dagger(\Pi_J)$ with eigenvalue of largest absolute magnitude.
The physical input $Dvv^\dagger D^\dagger$, followed by the full read at
$t=0$ and Stop, has event-$J$ probability difference equal to that eigenvalue.
Its TV is at least its absolute value and at most $e(S)$; hence equality
holds. The event groups outcomes only after the full rank-one read.
$\square$

The quantifier is existence of a stationary design no worse than each
competitor. Neither stationarity of every competitor nor equality of every
individual error under averaging follows from this theorem.

## 4. A complete rational polynomial optimization problem

**Definition 4.1 (Variables and vectorization).** Let $N_*=625$ and introduce
unrestricted complex matrices $C_i=X_i+iY_i\in M_5$, $1\le i\le N_*$,
with $31,250$ real coordinates, and a real threshold $r$. Shorter families
are padded by zero matrices. Define

$$
\Phi_C(X)=\sum_iC_iXC_i^\dagger,\qquad
M_C=\sum_i\overline{C_i}\otimes C_i,\qquad
G=I_5\otimes A+A\otimes I_5.
\tag{4.1}
$$

Here column stacking is explicit:
$\operatorname{vec}_{\rm col}(X)_{5j+i}=X_{ij}$ for $0\le i,j<5$,
with tensor order input first, output second. It is related by a fixed tensor
flip to the output-first $w(X)$ of (2.1). Then

$$
\begin{aligned}
\operatorname{vec}_{\rm col}(CXC^\dagger)
&=(\overline C\otimes C)\operatorname{vec}_{\rm col}(X),\\
\operatorname{vec}_{\rm col}(AX-XA)
&=(I\otimes A-A^T\otimes I)\operatorname{vec}_{\rm col}(X)
=G\operatorname{vec}_{\rm col}(X).
\end{aligned}
\tag{4.2}
$$

For example the $(5j+i,5\ell+k)$ entry of $M_C$ is
$\sum_a\overline{(C_a)_{j\ell}}(C_a)_{ik}$.
The plus sign in $G$ is forced by $A^T=-A$.

For $J\in\mathcal J_{15}$ put

$$
H_J(C)=\Pi_J-\sum_i C_i^\dagger\Pi_JC_i.
\tag{4.3}
$$

**Definition 4.2 (The full polynomial system).** Let $\mathcal P_q(C,r)$ be
the following finite conjunction over the real coordinates $X_i,Y_i,r$:

$$
\begin{aligned}
&0\le r\le1,\\
&\sum_iC_i^\dagger C_i=I_5,\\
&\operatorname{Re}\det\bigl((C_i)_{R,S}\bigr)
=\operatorname{Im}\det\bigl((C_i)_{R,S}\bigr)=0
&&\bigl(i\le625,\ |R|=|S|=q+1\bigr),\\
&\operatorname{Re}(M_CG-GM_C)_{ab}
=\operatorname{Im}(M_CG-GM_C)_{ab}=0
&&\bigl(1\le a,b\le25\bigr),\\
&\det\bigl((rI_5+\sigma H_J(C))_{I,I}\bigr)\ge0
&&\bigl(J\in\mathcal J_{15},\ \sigma\in\{-1,1\},\
\varnothing\ne I\subseteq\{0,1,2,3,4\}\bigr).
\end{aligned}
\tag{4.4}
$$

The TP equality is likewise split into real and imaginary equations.
One can retain its $25$ independent real equations: five diagonal real
equations and both parts of the ten strict-upper-triangular equations.
Keeping every entry instead merely adds redundancy. Every event matrix is
Hermitian, so each displayed principal determinant is identically real in
the real variables. Its real expansion is the intended polynomial.

There are $15\cdot2\cdot(2^5-1)=930$ principal-minor inequalities, in
addition to the two bounds on $r$. Stationarity uses at most $1,250$ real
quadratic equations. The rank equations number
$1,250\binom5{q+1}^2$: respectively $125,000$, $125,000$, $31,250$ and
$1,250$ for $q=1,2,3,4$. All coefficients are rational integers before a
rational threshold is substituted. TP and stationarity have degree at most
two; rank equations have degree $q+1\le5$. A principal minor of order $k$
has total degree at most $2k$, hence at most ten in the $31,251$ variables.
These are unrestricted complex rank minors, not projector constraints or a
Schmidt-number SDP relaxation.

**theorem 4.3 (Exact feasibility and compactness).** For $q=1,2,3,4$ and
$0\le r\le1$, the following are equivalent:

1. $\exists C\ \mathcal P_q(C,r)$.
2. Some original legal fixed port has actual-history error at most $r$.
3. $\varepsilon_q\le r$.

The solution set in $(C,r)$ is nonempty and compact, and minimizing $r$ on
it gives precisely $\varepsilon_q$.

Proof. Vanishing of all $(q+1)$-minors is exactly complex rank at most $q$.
TP and the Kraus form give complete positivity and trace preservation. The
supplied $625$-term representation makes these constraints cover every
channel in $\mathfrak C_q$, before stationarity is imposed. Equation (4.2)
identifies the commutator constraints with (3.2). For a Hermitian matrix,
nonnegative principal minors are equivalent to positive semidefiniteness.
For completeness, necessity follows by restricting a positive quadratic
form. Conversely the elementary symmetric polynomials of its real
eigenvalues are the sums of principal minors of each order. If these are
nonnegative, $\det(tI+B)$ has nonnegative coefficients and a positive leading
coefficient, so it cannot vanish for $t>0$. A negative eigenvalue of $B$
would give such a zero. This proves sufficiency, including singular cases.

Consequently the last constraints in (4.4) are exactly
$\|H_J(C)\|_{\rm op}\le r$. Theorem 3.3 proves that feasible tuples yield
legal original ports with $e\le r$. Conversely a legal port with $e\le r$
has a stationary no-worse design; the supplied support bound represents
that design by $625$ Kraus matrices satisfying (4.4). The minimum in the
original class is attained, so conditions 2 and 3 are equivalent even at the
boundary $r=\varepsilon_q$.

All constraints are closed polynomial conditions. Taking a trace in TP gives
$\sum_i\|C_i\|_{\rm HS}^2=5$, so the coordinates are bounded; indeed the
diagonal TP equations imply each entry has modulus at most one. Together
with $0\le r\le1$ this gives compactness. Nonemptiness follows, for example,
from the stationary completely depolarizing channel, represented by the
$25$ rank-one matrices $|a\rangle\langle b|/\sqrt5$, and $r=1$.
$\square$

Stationarity in (4.4) does not parametrize every original competitor with
the same channel coefficients. Its validity for minimax comes from the
proved no-worse map, so the existential threshold predicate still excludes
or includes the entire original competitor class correctly.

## 5. Effective certificates, exact algebraic computation and port realization

**theorem 5.1 (Terminating two-sided and exact algorithms).** For each
$q=1,2,3,4$ and rational $\eta>0$, a terminating exact algorithm returns
rational $l,u$ and an algebraically specified fixed legal port $T$ with at
most $625$ flags such that

$$
l\le\varepsilon_q\le e(T)\le u,\qquad u-l\le\eta.
\tag{5.1}
$$

Each negative threshold decision is a lower certificate against all legal
complex competitors. Each positive decision has an exact algebraic Kraus
witness. There is also a terminating algorithm producing a real-algebraic
description of the exact $\varepsilon_q$ and an algebraic optimal port.
These are algorithm specifications and computability statements; no
evaluated frontier value or explicit optimizer tuple is specified.

Proof. Use Basu–Pollack–Roy, *Algorithms in Real Algebraic Geometry*, second
edition, Algorithm 11.14, Cylindrical Decision, with ordered domain
$\mathbb Q$ (or integer polynomials after clearing positive denominators).
Its input is a finite polynomial sentence with equalities and inequalities;
its output is its exact truth value. It invokes cylindrical decomposition
with algebraic sample points, extracts realizable cylindrical sign data,
and evaluates the finitely many quantified sign conditions. The algorithm
includes zero signs and weak inequalities, so it decides boundary cases.
Its correctness is the stated cylindrical-decision theorem, not a numerical
mesh assumption or an unproved completeness assertion for a hierarchy.

Apply it to $\exists C\ \mathcal P_q(C,m)$ at each rational threshold $m$.
Initialize $l=b_q$, $u=u_q$ from QMB. If $u-l>\eta$, test $m=(l+u)/2$.
On a true decision replace $u$ by $m$; on a false decision replace $l$ by
$m$. Theorem 4.3 maintains $l\le\varepsilon_q\le u$. Every step halves
the width. After at most the first integer $n$ with
$(u_q-b_q)2^{-n}\le\eta$, the loop ends. Every decision is finite by the
cylindrical-decision algorithm. A feasible cell at the final $u$ has an
algebraic sample $C$; if necessary make that decision once more to obtain its sample.
The associated port of Theorem 5.2 has $e(T)\le u$.

A positive certificate consists of exact algebraic coordinates and verified
equations and signs. A negative certificate can retain the exact finite
cylindrical decomposition, algebraic sample encodings and sign data showing
that no cell satisfies the conjunction. These certificate descriptions
specify finite algebraic objects, without specifying a cell decomposition
or feasible coordinates for a particular instance of (4.4).

For exact computation one may directly use BPR Algorithm 14.9, Global
Optimization, on the displayed quantifier-free semialgebraic set and the
polynomial objective $r$. This algorithm returns the infimum and a minimizer
when one exists. Its block elimination, univariate sample points, triangular
sign determination and removal of infinitesimals give finite univariate
algebraic representations. The compact nonempty set of Theorem 4.3 supplies
the attained-minimum hypothesis.

There is also a direct endpoint description: cylindrical elimination of
the $C$ variables projects (4.4) to exactly $[\varepsilon_q,1]$.
Its left endpoint is a finite real-algebraic cell endpoint over $\mathbb Q$.
Root isolation identifies it, and algebraic sampling in its nonempty fiber
returns an algebraic minimizing tuple. Thus both the value and some
minimizer are real algebraic and effectively computable, rather than merely
abstractly existent. No particular endpoint polynomial, isolating interval
or minimizing tuple is specified. $\square$

**theorem 5.2 (Algebraic fixed-port realization and actual attainment).**
Every feasible algebraic tuple in (4.4) has an effective algebraic
realization in the original coordinates by one fixed encoder and whole-block
CPTP decoders. For that stationary channel its exact worst-case error is
attained by wait zero, a full five-outcome read and Stop, on a suitable
complex algebraic pure input.

Proof. For each $C_i$, compute an algebraic orthonormal basis of its range
and extend it to $q$ orthonormal columns in $\mathbb C^5$, obtaining an
isometry $V_i$ with $V_iV_i^\dagger C_i=C_i$. Exact Gaussian elimination
detects the rank. Gram–Schmidt on independent columns followed by standard
basis vectors uses algebraic arithmetic, conjugation and positive square
roots; every required comparison or zero test is decidable for algebraic
numbers. A zero $C_i$ can be dropped, or given any fixed algebraic isometry.
Set

$$
\begin{aligned}
B_i&=V_i^\dagger C_iD^\dagger, &R_i&=DV_i,\\
\operatorname{Enc}_i(X)&=B_iXB_i^\dagger,
&\operatorname{Dec}_i(Y)&=R_iYR_i^\dagger.
\end{aligned}
\tag{5.2}
$$

Then $\sum_iB_i^\dagger B_i=I_5$ and $R_i^\dagger R_i=I_q$.
Thus the total direct-sum encoder is CPTP and each decoder is CPTP on the
entire $M_q$. Their composite has Kraus matrices
$R_iB_i=DC_iD^\dagger$, giving exactly the original-coordinate channel.
There are at most $625$ fixed flags, consumed during decoding. Nothing is
retained outside the declared port or exposed to the future policy.

The finitely many Hermitian residuals $H_J(C)$ have algebraic entries.
Exact eigenvalue isolation and algebraic linear algebra select one with
maximal absolute eigenvalue and an algebraic unit eigenvector. Theorem 3.3
then realizes its error with the actual wait $t=0$. This is an actual
finite-time worst case, not only a limiting torus point. $\square$

The coefficient descriptions, flag count, CPTP design and this exact
attainment statement are distinct from physical coefficient synthesis,
finite-precision robustness, clocks and storage duration. No practical
runtime bound is inferred from termination; the finite system has $31,251$
real variables before any elimination auxiliaries.

## 6. A rank-one moment bound retaining the TP marginal

**Convention 6.1 (The supplied rotation data).** Put $\rho_{17}=\sqrt{17}$,
$\lambda_\pm=(5\pm\rho_{17})/2$, and
$\omega_\pm=\sqrt{\lambda_\pm}$. QMB Theorem 4.1 decomposes the real
space into two rotation planes $L_+,L_-$ and the fixed dark line
$L_0=\mathbb R d$, where $d=(e_2-e_5)/\sqrt2$. Their projections
$R_0,R_+,R_-$ have ranks $1,2,2$. Explicit algebraic formulas are

$$
\begin{gathered}
B=-A^2,\qquad
R_\pm=\frac{B(B-\lambda_\mp I)}
{\lambda_\pm(\lambda_\pm-\lambda_\mp)},\qquad
R_0=I-R_+-R_-,\qquad W_\pm=AR_\pm/\omega_\pm,\\
O(\theta_+,\theta_-)=R_0+\cos\theta_+R_++\sin\theta_+W_+
+\cos\theta_-R_-+\sin\theta_-W_-.
\end{gathered}
\tag{6.1}
$$

This is orthogonal, since $W_\pm^2=-R_\pm$, and equals the actual
$O(t)$ at $\theta_\pm=\omega_\pm t$. These angle variables are mathematical
coordinates, not independent allowed controls.

We use the supplied weights $a_s=(0,1,0,1,3)$ and $w_s=a_s/5$ in the
original mode order. For $r_{sj}=\|R_je_s\|^2$, the supplied length table is

$$
\begin{array}{c|ccc}
s&r_{s0}&r_{s+}&r_{s-}\\\hline
N&0&(1+1/\rho_{17})/2&(1-1/\rho_{17})/2\\
2&1/2&(1+3/\rho_{17})/4&(1-3/\rho_{17})/4\\
3&0&(1-3/\rho_{17})/2&(1+3/\rho_{17})/2\\
5&1/2&(1+3/\rho_{17})/4&(1-3/\rho_{17})/4\\
25&0&(1-1/\rho_{17})/2&(1+1/\rho_{17})/2
\end{array}
\tag{6.2}
$$

In particular $S_{ij}:=\sum_sa_sr_{si}r_{sj}$ satisfies

$$
\begin{gathered}
S_{00}=\frac12,\quad
S_{0\pm}=\frac{1\pm3/\rho_{17}}4,\quad
S_{\pm\pm}=\frac{67}{68}\mp\frac{3}{4\rho_{17}},\quad
S_{+-}=\frac{13}{17}.
\end{gathered}
\tag{6.3}
$$

**lemma 6.2 (The same actual orbit gives the two-angle moments).** For every
continuous function on the two angle circles, its forward-time Cesàro mean
along $(\omega_+t,\omega_-t)$ is its normalized two-circle integral.
The actual nonnegative orbit, and also its rational-time suborbit, is dense
in the torus (6.1).

Proof. The ratio $\omega_+/\omega_-$ is irrational, since its square is
$(21+5\sqrt{17})/4$. For every nonzero integer pair $(k,l)$,
$k\omega_++l\omega_-\ne0$ and

$$
\frac1W\int_0^W e^{i(k\omega_++l\omega_-)t}\,dt
=\frac{e^{i(k\omega_++l\omega_-)W}-1}
{iW(k\omega_++l\omega_-)}\longrightarrow0.
\tag{6.4}
$$

This proves the assertion for trigonometric polynomials. Uniform
trigonometric approximation of continuous periodic functions proves it for
all continuous functions. A nonnegative continuous bump supported in any
nonempty open patch has positive torus integral, so the forward orbit must
enter that patch. Its preimage is open in nonnegative time and contains a
nonnegative rational time. This proves both density statements. Only
suprema and mathematical averages are being identified. $\square$

**lemma 6.3 (Fourth moment and affine majorant).** For any complex unit
vector $z$ define the unnormalized fourth moment

$$
F(z)=\lim_{W\to\infty}\frac1W\int_0^W
\sum_s a_s|v_s(t)^Tz|^4\,dt,\qquad v_s(t)=O(t)^Te_s.
\tag{6.5}
$$

It obeys the two simultaneous bounds

$$
F(z)\le m:=\frac{5556+423\sqrt{17}}{13414},\qquad
F(z)\le z^\dagger\Lambda z,
\quad
\Lambda=\frac35R_0+\frac{23}{50}R_++\frac12R_-.
\tag{6.6}
$$

The real-unit-vector maximum of $F$ is exactly $m$. This auxiliary maximum
is not asserted to be the minimax port error or a simultaneously achievable
channel survival optimum.

Proof. First let $x$ be real unit and put
$p_j=\|R_jx\|^2$, so $p_0+p_++p_-=1$ and $p_j\ge0$.
For a fixed mode the inner product in (6.5) is a constant dark component
plus two independent planar cosines in the mathematical angle average.
Their cosine second and fourth moments are $1/2$ and $3/8$, respectively;
odd terms vanish. Thus Lemma 6.2 and (6.3) give

$$
\begin{aligned}
F(x)={}&S_{00}p_0^2+\frac38S_{++}p_+^2+\frac38S_{--}p_-^2\\
&+3S_{0+}p_0p_++3S_{0-}p_0p_-+\frac32S_{+-}p_+p_-\\
={}&p^T\mathsf H p,
\end{aligned}
\tag{6.7}
$$

where

$$
\mathsf H=\frac1{544}
\begin{pmatrix}
272&204+36\rho_{17}&204-36\rho_{17}\\
204+36\rho_{17}&201-9\rho_{17}&312\\
204-36\rho_{17}&312&201+9\rho_{17}
\end{pmatrix}.
\tag{6.8}
$$

For example the mixed fourth-power term of the two planar cosines is
$6\cdot(1/2)^2r_{s+}r_{s-}p_+p_-$, giving the last coefficient in
(6.7). This also fixes the weight normalization: the measure defining $F$
has total mass five, not one.

Fix $p_+$ and vary $p_0$ with $p_-=1-p_+-p_0$. The coefficient of
$p_0^2$ is $(65+81\rho_{17})/544>0$. Hence the maximum of $F$, or of
$F$ minus any affine function of $p$, lies on one of the edges $p_0=0$
or $p_-=0$. On the first edge,

$$
\frac12-F(x)=\frac1{544}
\begin{pmatrix}p_+&p_-\end{pmatrix}
\begin{pmatrix}71+9\rho_{17}&-40\\-40&71-9\rho_{17}\end{pmatrix}
\begin{pmatrix}p_+\\p_-\end{pmatrix}\ge0.
\tag{6.9}
$$

The diagonal entries are positive and the determinant is $2064$.
On $p_-=0$ the coefficient of $p_0^2$ is
$(65-81\rho_{17})/544<0$. Completing the square, or differentiating
this single concave quadratic, gives its maximum at

$$
p_0=\frac{3+45\rho_{17}}{81\rho_{17}-65},\qquad
p_+=\frac{36\rho_{17}-68}{81\rho_{17}-65},\qquad p_-=0,
\tag{6.10}
$$

with value $m$. Both populations are positive and sum to one. Since
$m>1/2$, these two edge calculations give the global maximum. Every such
population vector is realized by a real unit vector with components in the
three orthogonal subspaces, so this is an attained moment maximum.

For the second bound let
$\lambda=(3/5,23/50,1/2)$. Since $\sum_jp_j=1$,

$$
\lambda\cdot p-p^T\mathsf Hp=p^T\mathsf Bp,\qquad
\mathsf B_{ij}=\frac{\lambda_i+\lambda_j}2-\mathsf H_{ij}.
\tag{6.11}
$$

It suffices by the same convexity argument to check the two edges just
used. In their coordinate order the two blocks are

$$
\begin{gathered}
\mathsf B_{0,+}=
\begin{pmatrix}
1/10&31/200-9\rho_{17}/136\\
31/200-9\rho_{17}/136&1231/13600+9\rho_{17}/544
\end{pmatrix},\\
\mathsf B_{+,-}=
\begin{pmatrix}
1231/13600+9\rho_{17}/544&-159/1700\\
-159/1700&71/544-9\rho_{17}/544
\end{pmatrix}.
\end{gathered}
\tag{6.12}
$$

Their determinants, respectively, are

$$
\frac{-60807+15075\rho_{17}}{680000},\qquad
\frac{-18349+7650\rho_{17}}{11560000}.
\tag{6.13}
$$

Both are positive: $41/10<\rho_{17}<5$ makes the numerators positive,
and also proves positivity of both diagonal entries of each block.
They are positive definite. Thus $F(x)\le\lambda\cdot p=x^T\Lambda x$
on both edges and hence on the entire simplex.

Finally write a complex unit vector as $z=u+iv$ with real $u,v$.
Let $t=\|u\|^2$, so $\|v\|^2=1-t$. Since the $v_s$ are real,

$$
|v_s^Tz|^2=t|v_s^T\widehat u|^2+(1-t)|v_s^T\widehat v|^2.
\tag{6.14}
$$

Convexity of the square, followed by integration, gives
$F(z)\le tF(\widehat u)+(1-t)F(\widehat v)$. Terms with zero weight
are omitted. The first real bound gives $F(z)\le m$; the second gives
$F(z)\le u^T\Lambda u+v^T\Lambda v=z^\dagger\Lambda z$.
No Kraus reality assumption is used. $\square$

**theorem 6.4 (Explicit all-complex-competitor lower bound for port one).**
Under Assumption 1.1 and Definitions 1.2–1.3,

$$
\boxed{
\varepsilon_1\ge L:=
1-\frac12\left(\frac{5556+423\sqrt{17}}{13414}+\frac{63}{125}\right)
>\frac7{17}.}
\tag{6.15}
$$

Equivalently $L=1-(m+63/125)/2$. Illustratively,
$L=0.47589348145086214355\ldots$, while the credited sufficient port still
has error $4/7$. No new sufficient channel or exact $\varepsilon_1$ is
claimed.

Proof. Every legal port-one channel has a finite rank-one Kraus family.
Omit zero terms and write
$C_i=s_i|a_i\rangle\langle b_i|$ with $s_i>0$ and complex unit vectors
$a_i,b_i$. TP gives the joint input-direction constraint

$$
\sum_i s_i^2|b_i\rangle\langle b_i|=I_5,\qquad
\sum_i s_i^2=5.
\tag{6.16}
$$

For unit $a,b$, define the unnormalized mixed moment

$$
H(a,b)=\lim_{W\to\infty}\frac1W\int_0^W
\sum_sa_s|v_s(t)^Ta|^2|v_s(t)^Tb|^2\,dt.
\tag{6.17}
$$

The pointwise inequality $2AB\le A^2+B^2$ for nonnegative $A,B$ gives
$H(a,b)\le(F(a)+F(b))/2$. For every actual finite $t$ and mode $s$,
input $E_s(t)$ followed by wait $t$, a full read and Stop originally yields
$s$ with probability one. After the replacement its survival probability is

$$
f_s(t)=\operatorname{tr}(Q_s(t)\widehat T(Q_s(t)))
=\sum_i|\operatorname{tr}(Q_s(t)C_i)|^2
=\sum_i s_i^2|v_s(t)^Ta_i|^2|v_s(t)^Tb_i|^2.
\tag{6.18}
$$

Its actual full-history TV is exactly $1-f_s(t)$. Consequently
$e(T)\ge1-S(T)$, where

$$
\begin{aligned}
S(T)&=\lim_{W\to\infty}\frac1W\int_0^W\sum_sw_sf_s(t)\,dt\\
&=\frac15\sum_i s_i^2H(a_i,b_i)\\
&\le\frac1{10}\sum_i s_i^2\bigl(m+b_i^\dagger\Lambda b_i\bigr)\\
&=\frac1{10}\bigl(5m+\operatorname{tr}\Lambda\bigr)
=\frac12\left(m+\frac{63}{125}\right).
\end{aligned}
\tag{6.19}
$$

The trace is $\operatorname{tr}\Lambda=3/5+2(23/50)+2(1/2)=63/25$;
the last equality uses the full TP marginal (6.16). This controls arbitrary
complex input and output directions of every rank-one Kraus term together.
It applies to every legal finite flag set, without stationarity, unitality,
real Kraus operators, or a projection ansatz. Taking the infimum gives the
first inequality in (6.15).

For strict improvement, $\sqrt{17}<5$ gives $m<3/5$, whence
$L>56/125>7/17$. The displayed decimal is an evaluation of the exact
expression, not a numerical premise. $\square$

## 7. A finite rational-wait family witnessing the new lower bound

**theorem 7.1 (Uniform actual tests with explicit error and horizon).**
For rational $0<\delta<1$, set

$$
h=\frac\delta{48},\qquad
N=\left\lceil\frac{153600}{\delta^2}\right\rceil,\qquad
\mathcal W_\delta=\{jh:0\le j\le N\},\qquad W=Nh.
\tag{7.1}
$$

For every legal complex port-one competitor, some $t\in\mathcal W_\delta$
and $s\in\{2,5,25\}$ have actual TV greater than $L-\delta$ when input
is $E_s(t)$ and the protocol is wait $t$, full mode read, Stop. There are at
most $3(N+1)$ such alternative tests, all rational nonnegative waits, and

$$
\frac{3200}{\delta}\le W
\le\frac{3200}{\delta}+\frac\delta{48}.
\tag{7.2}
$$

Proof. The two-angle extension of
$g(t)=\sum_sw_sf_s(t)$ is a trigonometric polynomial taking values in
$[0,1]$, for every CPTP competitor. Each $O$ entry has Fourier degree one,
each $Q_s$ degree two, and each $f_s$ degree four. Its Fourier support is
therefore contained in $|k|+|l|\le4$, which has $40$ nonconstant indices.
Every normalized Fourier coefficient has modulus at most one, since the
function is bounded by one on the whole angle torus. Its constant coefficient
is $S(T)$ by Lemma 6.2.

All nonzero frequencies in this support have modulus greater than $1/10$.
An exact elementary check is as follows. Squaring rational endpoints gives
$411/100<\sqrt{17}<33/8$, and hence

$$
\frac{213}{100}<\omega_+<\frac{214}{100},\qquad
\frac{66}{100}<\omega_-<\frac{67}{100}.
\tag{7.3}
$$

Same-sign terms or terms with a zero index have modulus at least
$\omega_->66/100$. For opposite signs with both indices nonzero,
if $|k|\ge2$ then $|l|\le2$ and
$|k|\omega_+-|l|\omega_->2(213/100)-2(67/100)>1/10$.
If $|k|=1$ then $1\le|l|\le3$, and the smallest permitted difference
is bounded below by $213/100-3(67/100)=12/100>1/10$.
These cases exhaust the support.

Integrating each nonconstant exponential as in (6.4) now gives, uniformly
over all competitors,

$$
\left|\frac1W\int_0^Wg(t)\,dt-S(T)\right|<\frac{800}{W}.
\tag{7.4}
$$

Since $W\ge3200/\delta$, (6.19) implies that the average weighted
failure is at least $L-\delta/4$. Some $t\in[0,W]$ and a mode with
$w_s>0$ have failure at least this large.

For the discretization, $Q_s'= -AQ_s+Q_sA$ and
$\|Q_s'\|_1\le2\|A\|_{\rm op}$. A CPTP map contracts the trace norm
of Hermitian inputs: split such an input into positive and negative parts,
use positivity and TP, and apply the triangle inequality. Differentiating
$f_s(t)=\operatorname{tr}(Q_s(t)\widehat T(Q_s(t)))$ consequently gives

$$
|f_s'(t)|\le4\|A\|_{\rm op}<12,
\tag{7.5}
$$

where $\|A\|=\omega_+<3$. Move the selected $t$ to a grid point in
$\mathcal W_\delta$ within $h$. The failure decreases by at most
$12h=\delta/4$. That grid test has TV at least $L-\delta/2>L-\delta$.
The ceiling in (7.1) gives (7.2). $\square$

This family gives a failing alternative experiment for each competitor;
it does not identify an unknown channel from one sample. The pure inputs
are allowed by the all-density preparation hypothesis. Their mathematical
availability is not a physical state-preparation or clock-synthesis theorem.
No protocol uses source copies, a probability oracle, or an infinite wait.

## 8. The four supplied lower endpoints are strictly excluded

**lemma 8.1 (Equality in the supplied spectral and rank bounds).** Let
$\mathcal M$ be the QMB weighted observation operator with weights $a_s$.
On the complex traceless matrix space its largest eigenvalue $33/68$ is
simple, with eigendirection

$$
Z=-4R_0+(1-5/\sqrt{17})R_++(1+5/\sqrt{17})R_-.
\tag{8.1}
$$

Equality in the QMB inequality

$$
\langle C,\mathcal M(C)\rangle_{\rm HS}
\le\frac{33}{68}\|C\|_{\rm HS}^2
+\frac{35}{68}\frac{|\operatorname{tr}C|^2}{5}
\tag{8.2}
$$

therefore forces $C\in\operatorname{span}_{\mathbb C}\{I,Z\}$.
For a nonzero rank-at-most-$q$ complex matrix, equality in
$|\operatorname{tr}C|^2\le q\|C\|_{\rm HS}^2$ forces
$C=cP$, where $c\ne0$ and $P$ is a rank-$q$ orthogonal projection.

Proof. The QMB three-dimensional rotation-invariant block has eigenvalues
$1,33/68,0$. To identify its traceless top vector without a normalization
ambiguity, a matrix $z_0R_0+z_+R_++z_-R_-$ has output coefficients
$\sum_jS_{ij}z_j/d_i$, where $(d_0,d_+,d_-)=(1,2,2)$.
Substitution of $(-4,1-5/\sqrt{17},1+5/\sqrt{17})$ into (6.3) gives
exactly $33/68$ times that vector, with trace zero.

The other nonzero eigenvalues on the traceless space, each twice, are

$$
\frac{1+3/\sqrt{17}}4,\quad
\frac{1-3/\sqrt{17}}4,\quad
\frac{67}{272}-\frac{3}{16\sqrt{17}},\quad
\frac{67}{272}+\frac{3}{16\sqrt{17}},\quad
\frac{13}{34},\quad\frac{13}{34}.
\tag{8.3}
$$

All are strictly less than $33/68$. For the first, this is equivalent to
$51<16\sqrt{17}$, verified by squaring. The larger plane-internal value
is less than $67/272+3/64<33/68$ because $\sqrt{17}>4$; the last
comparison is immediate. The remaining complex transpose-antisymmetric
space has eigenvalue zero. The QMB full spectrum thus proves simplicity on
the entire complex traceless space, not only on real symmetric matrices.
Splitting off the scalar identity in (8.2), equality leaves only its top
traceless eigenspace, proving the first equality characterization.

For the rank claim, take a singular value decomposition
$C=\sum_{j=1}^r\sigma_ju_jv_j^\dagger$ with $r\le q$ and positive
singular values. The complete chain is

$$
|\operatorname{tr}C|
\le\sum_j\sigma_j|v_j^\dagger u_j|
\le\sum_j\sigma_j
\le\sqrt r\left(\sum_j\sigma_j^2\right)^{1/2}
\le\sqrt q\|C\|_{\rm HS}.
\tag{8.4}
$$

Equality at the endpoints forces $r=q$, equal singular values, and
$u_j=e^{i\theta_j}v_j$. Equality in the triangle inequality forces the
same phase for all $j$. Hence $C=c\sum_jv_jv_j^\dagger=cP$, with the
asserted rank. This proves the characterization for arbitrary complex
matrices. $\square$

**theorem 8.2 (Strict endpoint exclusion).** For $q=1,2,3,4$,

$$
\varepsilon_q>\frac{7(5-q)}{68}.
\tag{8.5}
$$

This statement gives no explicit uniform additive gap for $q=2,3,4$.
The separate Theorem 6.4 gives a quantitative bound for $q=1$.

Proof. For any finite rank-at-most-$q$ Kraus representation of any legal
channel, QMB's proof uses the survival average $S(T)$ and the chain

$$
\begin{aligned}
e(T)&\ge1-S(T),\\
S(T)&=\frac15\sum_i\langle C_i,\mathcal M(C_i)\rangle_{\rm HS}\\
&\le\frac15\sum_i\left[
\frac{33}{68}\|C_i\|_{\rm HS}^2
+\frac{35}{68}\frac{|\operatorname{tr}C_i|^2}{5}\right]\\
&\le\frac{33}{68}+\frac{35}{68}\frac q5.
\end{aligned}
\tag{8.6}
$$

TP supplies $\sum_i\|C_i\|_{\rm HS}^2=5$. If $e(T)=b_q$,
every inequality in (8.6) must be equality. The individual spectral
deficits and individual rank-trace deficits are nonnegative, with positive
coefficients. Their finite sums vanish only when each vanishes. Lemma 8.1
therefore forces every nonzero $C_i$ both to have the form $aI+bZ$ and
to be a nonzero scalar multiple of a rank-$q$ orthogonal projection.

But $Z$ has three distinct eigenvalues
$-4,1-5/\sqrt{17},1+5/\sqrt{17}$, on subspaces of dimensions $1,2,2$.
If $b\ne0$, $aI+bZ$ has three distinct eigenvalues, also for complex
$a,b$. A nonzero scalar times a proper nonzero projection has exactly two
eigenvalues. If $b=0$, a nonzero $aI$ has rank five, again impossible for
$q<5$. Thus no nonzero Kraus term can meet both equality conditions,
contradicting TP. Every legal channel has $e(T)>b_q$.

Finally the supplied compactness and continuity give an attained minimum.
Applying the preceding contradiction to a minimizer makes the infimum
strict as well. Pointwise strict inequalities alone would not suffice for
this last step. $\square$

Theorem 5.1 can in principle find a rational lower endpoint strictly above
$b_q$: repeat its exact bisection until its lower endpoint exceeds $b_q$.
The positive attained gap proves termination of this further search. No
explicit rational additive gap for $q=2,3,4$ is specified.

## 9. Three concrete boundaries on symmetry shortcuts

**proposition 9.1 (The actual menu is not orthogonally invariant).** The
closed actual singleton-effect set is not invariant under $O(5)$. Even
restricted to real input states, replacing it by all orthogonal-basis reads
changes the operational distance for some pairs.

Proof. The dark vector $d=(e_2-e_5)/\sqrt2$ is fixed by every actual
$O(t)$ and every matrix in its closure. Therefore

$$
\operatorname{tr}(R_0Q_s(t))=|d^Te_s|^2\in\{0,1/2\},
\qquad \operatorname{tr}(R_0^2)=1.
\tag{9.1}
$$

The same invariant holds throughout the closed orbit. An orthogonal
transformation exchanging $e_N$ and $d$ sends the actual wait-zero effect
$\Pi_N$ to $R_0$, which is absent from that closed singleton orbit.
Higher-cardinality event effects have larger rank, so do not repair this
failure of set invariance.

More operationally take the frame states
$\rho=R_0$ and $\sigma=(I-R_0)/4$. They are fixed by every wait.
Their full mode distributions are

$$
(0,1/2,0,1/2,0),\qquad(1/4,1/8,1/4,1/8,1/4),
\tag{9.2}
$$

with TV $3/4$ at every wait and, by the supplied first-read theorem, over
all actual finite histories. A real orthogonal basis containing $d$ gives
TV one. Thus the larger measurement menu really changes a performance
comparison. This refutes the proposed menu-invariance premise, not the
possibility that some orthogonally covariant channel happens to minimize
the original problem. $\square$

**proposition 9.2 (Real Choi coefficients do not imply real rank-one Kraus
operators).** A legal port-one channel can have a real Choi matrix in the
passive frame and have no rank-one Kraus representation consisting of real
matrices.

Proof. On two selected coordinate modes let

$$
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\qquad
P_\pm=(I_2\pm Y)/2.
\tag{9.3}
$$

Take these two embedded rank-one projections as Kraus matrices, together
with the three other coordinate projections. Their squared-adjoint sum is
$I_5$, so this is a legal rank-one Kraus channel. The two first matrices are
complex conjugates and the other three are real. Its Choi matrix is
therefore real, and its superoperator preserves real matrix coefficients.

Let $W=Y\otimes Y$ on the selected output/input two-mode tensor block,
and zero elsewhere. If $y_\pm$ are unit $Y$ eigenvectors, then
$w(P_\pm)=y_\pm\otimes\overline{y_\pm}$. The eigenvalues of $Y$ on
these factors are opposite. Consequently, for its normalized Choi state,

$$
\operatorname{tr}(W\chi_T)=-\frac25.
\tag{9.4}
$$

In contrast a real rank-one matrix factors as $ab^T$ with real $a,b$.
Its vectorization is $a\otimes b$, and its $W$ quadratic form is
$(a^TYa)(b^TYb)=0$, using the corresponding two-mode restrictions.
Every real rank-one Kraus decomposition would thus give Choi expectation
zero, contradicting (9.4). This is the real-versus-complex product-vector
obstruction discussed by Caves–Fuchs–Rungta, here embedded into an exact
TP five-mode example. It does not assert that an optimizer must use complex
Kraus matrices. $\square$

**proposition 9.3 (Stationarity does not preserve rank under characterwise
Kraus decomposition).** A stationary channel in $\mathfrak C_1$ need not
have a rank-one Kraus representation in which every Kraus operator transforms
by one character of the walk's compact torus.

Proof. Consider

$$
S(X)=\frac{X+\operatorname{tr}(X)I_5}{6}.
\tag{9.5}
$$

It is covariant under all unitaries. It belongs to $\mathfrak C_1$ because
$S(X)=5\int PXP\,dP$, where $P=vv^\dagger$ and $v$ is uniform on the
complex unit sphere. To check the integral, coordinate phase and permutation
invariance leave two moments $u=\mathbb E|v_1|^4$ and
$c=\mathbb E|v_1|^2|v_2|^2$. Replacing the first coordinate by
$(v_1+v_2)/\sqrt2$ preserves its distribution and gives
$u=(2u+4c)/4$, so $u=2c$. Summing
$\mathbb E(\sum_i|v_i|^2)^2=5u+20c=1$ gives $c=1/30$.
The full tensor is consequently
$\mathbb E[v_i\overline v_jv_k\overline v_l]
=c(\delta_{ij}\delta_{kl}+\delta_{il}\delta_{kj})$.
Contracting with $X$ gives (9.5).
Also $5\int P\,dP=I$, so it is TP. The same finite-dimensional convex
representation used by QMB replaces its Choi integral by at most $625$
rank-one terms, preserving the channel exactly.

In a complex orthonormal eigenbasis of the two rotation planes and dark
line, the five distinct torus characters are
$0,+e_+,-e_+,+e_-,-e_-$. A zero-character Kraus matrix must be diagonal
in this basis. If it is rank one, it has at most one nonzero diagonal entry.
A nonzero-character matrix has zero diagonal, since every diagonal entry
transforms by the zero character.

In this eigenbasis write the output-first Choi vector in the conjugate
input basis; then $w(C)=\sum C_{ij}|i,j\rangle$ and the diagonal subspace
is $\mathcal D=\operatorname{span}\{|j,j\rangle\}$. The normalized
Choi matrix of (9.5) is

$$
\chi_S=\frac16|\Omega\rangle\langle\Omega|+\frac1{30}I_{25}.
\tag{9.6}
$$

Its restriction to $\mathcal D$ has off-diagonal entries $1/30$. In a
decomposition into definite-character rank-one Kraus vectors, nonzero
characters have no component in $\mathcal D$; zero-character rank-one
vectors contribute only coordinate-diagonal terms there. Their sum cannot
produce those off-diagonal entries. This contradiction proves the claim.
Stationarity is therefore imposed on the whole superoperator in (4.4),
never on individual low-rank Kraus characters. $\square$

## 10. References and unresolved mathematical boundaries

**Convention 10.1 (References and applicability).** The following primary
sources support only the indicated statements or methodological comparisons.

| Source | Correspondence and limit |
| --- | --- |
| [Bluhm–Rauber–Wolf, *Quantum Compression Relative to a Set of Measurements*, arXiv:1708.04898v4](https://arxiv.org/html/1708.04898v4), Definition 4.1, Theorem 5.1 and Lemmas 5.2–5.3 | Common CPTP encoding/decoding, all inputs, $M_d\otimes\mathbb C^n$ free classical blocks, finite $D^4$ support and compactness. Here $D=5,d=q$. The original measurement-relative seminorm uses its specified observables; our observables are the actual subset events through QMB's first-read identity. Its stability theorem does not evaluate this frontier. |
| [Terhal–Horodecki, *A Schmidt number for density matrices*, arXiv:quant-ph/9911117v4](https://arxiv.org/html/quant-ph/9911117v4), Definition 1 and Proposition 1 | Convex low-Schmidt-number states, pure decomposition and rank constraints. The TP marginal is imposed separately in (2.1); a maximally entangled overlap bound is not substituted for the present menu distance. |
| [Werner, *Optimal Cloning of Pure States*, arXiv:quant-ph/9804001](https://arxiv.org/html/quant-ph/9804001), §4, equation (4.2) | Averaging admissible channels in an invariant minimax problem. Cloning inputs, outputs and fidelity differ. Theorem 3.3 proves menu invariance and resource preservation for this problem separately. |
| [Navez–Cerf, *Cloning a real d-dimensional quantum state on the edge of the no-signaling condition*, arXiv:quant-ph/0302172v1](https://arxiv.org/html/quant-ph/0302172v1), real-state model and covariance/fidelity calculation | Comparison only: two-clone real-state fidelity and its orthogonal symmetry do not give this all-complex-input port optimum or authorize full orthogonal averaging here. |
| [Fuchs–Sasaki, *Squeezing Quantum Information through a Classical Channel: Measuring the Quantumness of a Set of Quantum States*, arXiv:quant-ph/0302092v3](https://arxiv.org/html/quant-ph/0302092v3), equation (16), §4.3 and equation (116) | Ensemble-dependent accessible fidelity and measure/prepare reasoning. Its real-Haar value $3/(d+2)$ is for another ensemble. Equations (6.7)–(6.19) calculate the present weighted actual-orbit bound instead. |
| [Caves–Fuchs–Rungta, *Entanglement of Formation of an Arbitrary State of Two Rebits*, arXiv:quant-ph/0009063](https://arxiv.org/html/quant-ph/0009063), real/complex product-state distinction | Real density coefficients do not equate real and complex separability. Proposition 9.2 supplies its own TP embedding and exact witness, so no rebit entanglement formula is needed as a premise. |
| [Basu–Pollack–Roy, *Algorithms in Real Algebraic Geometry*, second edition](https://www.maths.ed.ac.uk/~v1ranick/papers/basupollackroy.pdf), Algorithm 11.14 and correctness, printed p.422; Algorithm 14.9 and correctness, printed pp.557–558 | Exact cylindrical decision and polynomial global optimization, including algebraic sample data and an attained minimizer. Theorem 5.1 supplies the full task-specific input system and realization bridge. These algorithm statements support termination, not a measured runtime or an evaluated certificate. |

The compactness, Kraus/Schmidt-number equivalence and $625$ support bound
are the supplied QMB results of Convention 2.1.

**Convention 10.2 (Resulting frontier information).** The demonstrated
intervals and strict endpoint information are

| Port | Necessary lower information | Credited sufficient channel error |
| --- | --- | --- |
| $q=1$ | $L\le\varepsilon_1$, with $L=1-(m+63/125)/2>7/17$ | $4/7$ |
| $q=2$ | $21/68<\varepsilon_2$ | $3/7$ |
| $q=3$ | $7/34<\varepsilon_3$ | $2/7$ |
| $q=4$ | $7/68<\varepsilon_4$ | $1/7$ |
| $q=5$ | $\varepsilon_5=0$ | $0$ |

The strict all-$q<5$ result gives no explicit improved numerical lower constant
for $q=2,3,4$. The algebraic algorithm can produce such constants and
arbitrarily small certified intervals, but no such constants or intervals
are specified. The right-column ports are those of QMB Theorem 3.1.

**Definition 10.3 (Unresolved exact-frontier problem).** The exact-frontier
problem is to determine each of
$\varepsilon_1,\varepsilon_2,\varepsilon_3,\varepsilon_4$. Each value remains
unevaluated. No isolating polynomial or minimizing Kraus tuple is provided.
The original gap separates an achieved error of one real-projection channel
from necessary survival bounds. The former has no proved minimax equality
for this smaller actual orbit. The latter use scalar relaxations: the
rank-one proof uses $2AB\le A^2+B^2$ and an affine fourth-moment majorant;
the older bound uses a spectral envelope and rank/trace inequality whose
simultaneous equality is excluded in §8. An auxiliary moment maximum,
stationary design, or optimizer-existence theorem does not close these
inequalities. The complete system (4.4) preserves the intervening problem
and gives an effective way to determine it.

**Convention 10.4 (Resource and recovery limits).** The
independent all-state preparation of Assumption 1.1 has no native
$\alpha/\beta$ implementation bridge here. Exact algebraic coefficients
give finite mathematical descriptions; finite-precision CPTP realization,
physical synthesis, preparation acquisition, clock precision, storage
duration and physical transport require additional contracts and bounds.
Theoretical termination is distinct from a practical implementation or
runtime measurement. The rational-wait witnesses in §7 are mathematical
tests under the assumed menu, not a physical clock specification.

Recurrence makes time-translation of the future menu preserve the worst
error. Under Assumption 1.1 and Definitions 1.2–1.3, stationarity expresses
the fixed-memory minimax boundary through actual wait-zero tests by (3.3).
This is an equivalence of error optimizations for the specified preparation,
menu and port class. A mutual-recovery theorem for space, time, boundary and
memory, or a rate theorem for the native tree, requires additional
definitions and bridges.

## 追加锚（本行以下为增补区）
