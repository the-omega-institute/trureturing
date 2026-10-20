# AURIC FIB environment instruments and terminal record memory

## 1. Model, suppliers, and the recovery task

**Convention 1.1 (Ordinary mathematical scope).** All spaces below are
finite-dimensional complex Hilbert spaces. Adjoint is denoted by $\dagger$;
inner products are conjugate-linear in their first argument. A channel is a
complex-linear completely positive trace-preserving map. For an operator $L$,
write $\operatorname{Ad}_L(X)=LXL^\dagger$. Equality of channels means equality
on the entire complex operator algebra, and therefore after tensoring with
the identity on any untouched reference. The proofs are ordinary
finite-dimensional mathematical proofs.

An actual instrument in this volume means a specified mathematical unitary
dilation, a specified pure environment preparation, and a specified
orthonormal environment measurement whose actual outcome is supplied. It
is additional structure beyond an averaged channel or a list of possible
Kraus representations.

**Convention 1.2 (Owning sources).** The five-window space, half-parameter
channel, and invariant three-dimensional image are those of
[AURIC FIB five-window quantum memory, §§17–21][OWN]. In particular,
Definition 17.2 and Theorem 17.3 own the matrices and full-complex-input
population law, and equation (18.4) owns their restricted permutation
matrices. Sections 18–20 study fixed states, the superoperator, and finite
iterations of the discarded-environment channel. Definition 21.1 and
Theorem 21.2 concern exact codes initially contained in its image when the
labels are absent. Those are different recovery permissions from the
measured-label task below. The matrices are reused here, with their
five-input realization displayed to fix both measured instruments.

The standard one-step measured-flag inverse is already supplied by
[Minimal record dilations, Theorem 2.2 and Assumption 2.3][DIL]. Its named
random-unitary realization acts on its entire system space. Here the
correspondence is to the restricted system $R\cong\mathbb C^3$, with weights
$1/2,1/2$ and branch unitaries $U_j$ or $V_j$. It is not a correspondence
between that supplier's full system and the present $H=\mathbb C^5$:
the present five-dimensional Kraus operators are not scaled unitaries.
The additional synthesis here is the pair of actual instruments for this
same full channel, their terminal summary criterion, and the different
multi-step projective-word counts. The one-step correction principle is
used inside that synthesis.

**Definition 1.3 (Coordinates and embedding).** Set

$$
\begin{gathered}
H=\mathbb C^5,\qquad
(e_0,e_1,e_2,e_3,e_4)=(|000\rangle,|100\rangle,|010\rangle,
                       |001\rangle,|101\rangle),\\
q=2^{-1/2},\qquad u=q(e_0+e_3),\qquad
v=q(e_1+e_4),\qquad z=e_2,\\
R=\operatorname{span}\{u,v,z\},\qquad
B:\mathbb C^3\longrightarrow H,\quad B(x_0,x_1,x_2)=x_0u+x_1v+x_2z.
\end{gathered}
$$

Thus $B^\dagger B=I_3$ and $P_R=BB^\dagger$.
Use $\iota(X)=BXB^\dagger$ for the embedding of $M_3$ in $M_5$.
Reference systems will be denoted by $Z$, to distinguish them from $R$.

**Assumption 1.4 (Repeated measured-label task).** Choose one of the two
fixed instruments defined in §2 and a known integer horizon $n\ge0$.
At each step prepare a fresh environment in its specified pure ready state,
apply the same interaction, measure in the same chosen environment basis,
supply the actual binary outcome, and discard that environment. Environments
are neither reused nor retained as quantum memory. Only those supplied
labels may update a classical record. There is no intermediate quantum
feedback, no adaptive change of instrument, and no read of $Z$.

A terminal decoder is any deterministic CPTP map on all of $H$, selected by
the retained classical view. Success means that, for every reference $Z$
and every density operator $\rho$ on $\mathbb C^3\otimes Z$, the corrected
output is $(\iota\otimes\operatorname{id}_Z)(\rho)$. Success may be required
only after averaging over the record and its randomness. No success or
failure postselection is allowed. Inputs on all of $H$ are not recovery
targets. The classical processing and the terminal decoder have no
input-dependent quantum side information.

**Definition 1.5 (Counted view and separate resources).** The terminal
summary is the complete decoder-visible run-dependent classical view.
A history-dependent program, control selection, clock variation, seed,
external archive, or buffer is part of that view. Its alphabet size counts
all such information jointly; moving a history to another carrier does
not reduce it. Discarded private randomness is averaged out. A seed visible
to the decoder is included unless explicitly declared independent shared
randomness, whose conditional interpretation is treated in §3.

The $n$ label acquisitions and their measurement and communication, $n$
fresh environment preparations, calibration, the known horizon, a
deterministic clock, fixed control descriptions or tables, and the inverse
controls themselves are distinct resources. Fixed descriptions and the
clock may depend on $n$ but carry no extra run-dependent history. The
cardinality of a retained statistic is not a count of the entire apparatus
or the total cost of these operations.

## 2. Two measured instruments of the identical full five-dimensional channel

**Definition 2.1 (Full dilation and measurement bases).** Let
$E=\mathbb C^2$ with orthonormal basis $(f_0,f_1)$ and ready state $f_0$.
Specify $\mathcal V:H\to H\otimes E$ on every input basis vector by

$$
\begin{aligned}
\mathcal V e_0&=u\otimes f_0,&
\mathcal V e_1&=u\otimes f_1,&
\mathcal V e_2&=v\otimes(f_0+f_1)/\sqrt2,\\
\mathcal V e_3&=z\otimes f_1,&
\mathcal V e_4&=z\otimes f_0.
\end{aligned}
$$

The first instrument measures $(f_0,f_1)$. For a fixed real $\theta$ put
$c=\cos\theta$, $s=\sin\theta$ and measure instead

$$
g_0=cf_0-isf_1,\qquad g_1=-isf_0+cf_1.
$$

The second instrument uses this same $\mathcal V$ and ready state; only
its outgoing measurement basis differs. Its separation from the first
will be proved at $\theta=\pi/6$.

**Theorem 2.2 (Full-channel equality and unitary branches on the image).**
Definition 2.1 admits a unitary completion on $H\otimes E$. Both bases
are orthonormal and give actual instruments. Their averaged channels
coincide on every complex $M_5$ input and every spectator reference,
and equal the half-parameter owning channel $\Phi_\circ$.
Their restrictions to $R$ have the form

$$
K_jB=qBU_j,\qquad A_jB=qBV_j,
$$

where all four $3\times3$ matrices are unitary. On inputs supported in
$R$, each outcome has probability $1/2$, including inputs entangled with
an untouched reference. This fairness assertion is restricted to $R$.

Proof. The five images of $\mathcal V$ are orthonormal. Distinct system
vectors $u,v,z$ are orthogonal; repeated system vectors occur only with
orthogonal environment vectors. Hence $\mathcal V^\dagger\mathcal V=I_5$.
The map $x\otimes f_0\mapsto\mathcal Vx$ is an isometry between
five-dimensional subspaces of the ten-dimensional $H\otimes E$.
Complete an orthonormal basis in each complement and map one completed
basis to the other. The resulting unitary $\mathsf U$ satisfies
$\mathsf U(x\otimes f_0)=\mathcal Vx$. The preparation, interaction,
and measurement are thus all specified within a unitary dilation;
no outcome label is appended to an unmeasured reduced channel.

Contracting with $f_j$ gives exactly the supplier's operators

$$
\begin{aligned}
K_0&=|u\rangle\langle e_0|+q|v\rangle\langle e_2|
                              +|z\rangle\langle e_4|,\\
K_1&=|u\rangle\langle e_1|+q|v\rangle\langle e_2|
                              +|z\rangle\langle e_3|.
\end{aligned}
$$

Their full matrices, in the order of Definition 1.3, are

$$
K_0=\begin{pmatrix}
q&0&0&0&0\\0&0&1/2&0&0\\0&0&0&0&1\\
q&0&0&0&0\\0&0&1/2&0&0
\end{pmatrix},\qquad
K_1=\begin{pmatrix}
0&q&0&0&0\\0&0&1/2&0&0\\0&0&0&1&0\\
0&q&0&0&0\\0&0&1/2&0&0
\end{pmatrix}.
$$

In particular,

$$
K_0^\dagger K_0=\operatorname{diag}(1,0,1/2,0,1),\qquad
K_1^\dagger K_1=\operatorname{diag}(0,1,1/2,1,0).
$$

Their sum is $I_5$. The Kraus formula gives complete positivity and
trace preservation on $M_5$; their ranges lie in $R$.
These are the half-parameter eight-edge assignments of [OWN, (17.6)]:

$$
\alpha_0=\beta_0=f_0,\quad \alpha_1=\beta_1=f_1,\quad
\gamma_0=\gamma_1=(f_0+f_1)/\sqrt2,\quad
\delta_0=f_1,\quad\delta_1=f_0.
$$

All eight vectors have norm one. The required pairs
$(\alpha_0,\alpha_1)$, $(\beta_0,\beta_1)$ and $(\delta_0,\delta_1)$
are orthogonal; the owning model does not require the two $\gamma$
vectors to be orthogonal.

For completeness, the all-input population interface is

$$
Q_{1/2}=\begin{pmatrix}
1/2&0&0&1/2&0\\1/2&0&0&1/2&0\\
0&1/2&0&0&1/2\\0&0&1&0&0\\0&0&1&0&0
\end{pmatrix},
$$

$$
\operatorname{diag}\Phi_\circ(X)=
\begin{pmatrix}
(X_{00}+X_{11})/2\\X_{22}/2\\X_{33}+X_{44}\\
(X_{00}+X_{11})/2\\X_{22}/2
\end{pmatrix}
=Q_{1/2}^{\mathsf T}\operatorname{diag}X.
$$

Indeed the coefficients of $|u\rangle\langle u|$,
$|v\rangle\langle v|$, $|z\rangle\langle z|$ are respectively
$X_{00}+X_{11}$, $X_{22}$, $X_{33}+X_{44}$. Every cross operator between
these three vectors has zero computational diagonal, since their
computational supports are disjoint. This argument applies to arbitrary
complex $X$, with no positivity, Hermiticity, or reality hypothesis.
It verifies precisely the owning population interface, not merely its
values on diagonal densities.

The matrix

$$
C_\theta=\begin{pmatrix}c&is\\is&c\end{pmatrix}
$$

is unitary: its column norms are $c^2+s^2=1$ and their inner product
vanishes. The vectors $g_0,g_1$ are its adjoint columns in the $f$ basis
and are therefore orthonormal. Contracting $\mathcal V$ with them gives

$$
A_0=cK_0+isK_1,\qquad A_1=isK_0+cK_1.
$$

Expanding the two conjugations gives, for every complex $X$,

$$
\begin{aligned}
\sum_{j=0}^1A_jXA_j^\dagger
&=(c^2+s^2)(K_0XK_0^\dagger+K_1XK_1^\dagger)\\
&\quad+(-ics+ics)K_0XK_1^\dagger
       +(ics-ics)K_1XK_0^\dagger\\
&=\Phi_\circ(X).
\end{aligned}
$$

This is full-channel equality, stronger than the common population law.
The same algebra, with each operator tensored with $I_Z$, proves equality
on all $M_5\otimes\mathcal B(Z)$ for any spectator $Z$.

Applying the displayed $K_j$ to $u,v,z$ gives

$$
U_0=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\qquad
U_1=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix},
\qquad K_jB=qBU_j.
$$

Both $U_j$ are permutations. For the rotated branches one obtains

$$
V_0=cU_0+isU_1,\qquad V_1=isU_0+cU_1.
$$

Their unitarity requires the actual relative matrix, not just unitarity
of the summands. Direct multiplication gives

$$
W=U_0^\dagger U_1=
\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix},\qquad
W^\dagger=W,\quad W^2=I_3,\quad U_1=U_0W.
$$

The reflection identity implies

$$
cI_3+isW=e^{i\theta W},\qquad
V_0=U_0e^{i\theta W},\qquad V_1=V_0W.
$$

These are products of unitaries. Equivalently the cross terms in
$V_j^\dagger V_j$ cancel because $W^\dagger=W$. A general complex
linear combination of two unitaries need not be unitary, so the reflection
calculation is essential. We have proved $A_jB=qBV_j$ as well.

For either instrument let $L_j$ be its full operator and $Q_j$ its
normalized restricted unitary. Then

$$
B^\dagger L_j^\dagger L_jB=I_3/2,
$$

and on any qutrit-reference density $\rho$ the unnormalized branch is

$$
\frac12(BQ_j\otimes I_Z)\rho(BQ_j\otimes I_Z)^\dagger.
$$

Its trace is $1/2$ and its system output remains in $R$.
On all of $H$ the effect is not $I_5/2$: for example the first
unrotated outcome has probabilities one on $e_0$ and zero on $e_1$.
This establishes the asserted scope of fairness and recovery. $\square$

## 3. Exact summaries, arbitrary decoders, and complete classical views

**Definition 3.1 (Chronological words and projective classes).** Fix one
instrument and set $(Q_0,Q_1)=(U_0,U_1)$ or $(V_0,V_1)$ accordingly.
For a chronological history $h=(h_1,\ldots,h_n)\in\{0,1\}^n$ define

$$
Q_h=Q_{h_n}\cdots Q_{h_1},\qquad Q_{\varnothing}=I_3.
$$

Two words are projectively equivalent if $Q_h=\lambda Q_k$ for some
$|\lambda|=1$. Write $[Q_h]$ for the class, and let

$$
\mathcal P_n=\{[Q_h]:h\in\{0,1\}^n\},\qquad m_n=|\mathcal P_n|.
$$

Fresh preparations and Theorem 2.2 give probability $2^{-n}$ to every
history on every qutrit-reference input, and normalized action
$\operatorname{Ad}_{Q_h}$ in qutrit coordinates. To see the product law,
condition successively on each previous history: its normalized output
is still supported in $R$, so the next conditional probability is again
$1/2$. Thus the law follows from the measured instrument at every step.

**Definition 3.2 (Classical compression kernel).** Every finite or countable
terminal view $a$ produced from these labels by deterministic or randomized
classical updates induces numbers

$$
r(a\mid h)\ge0,\qquad\sum_a r(a\mid h)=1.
$$

The variable $a$ contains the entire counted view of Definition 1.5.
Given $R_a=\sum_h r(a\mid h)>0$, put

$$
p_a=2^{-n}R_a,\qquad w_{a,h}=r(a\mid h)/R_a,\qquad
\mathcal N_a(X)=\sum_h w_{a,h}Q_hXQ_h^\dagger.
$$

These probabilities are input-independent. Decoder-local randomness can
be absorbed into the CPTP map $\mathcal D_a:M_5\to M_5$.
No online constraint is needed for the necessity below; every online
procedure is included in this terminal-kernel description.

**Theorem 3.3 (Projective-word summary criterion).** Under Assumption 1.4,
a compression kernel admits exact terminal recovery if and only if, for
every $a$ with $p_a>0$, the set

$$
\{[Q_h]:r(a\mid h)>0\}
$$

has one member. Necessity holds even when recovery is demanded only for
the ensemble averaged over $a$, and even for arbitrary CPTP decoders on
$H$. Sufficiency recovers every qutrit-reference input. In particular,
random compression cannot merge two projective classes by using a
nonunitary decoder.

Proof. In qutrit input coordinates, the averaged requirement is the
channel identity

$$
\sum_a p_a\,\mathcal D_a\circ\iota\circ\mathcal N_a=\iota.
\tag{3.1}
$$

Equality on all densities implies this identity on the complex algebra:
Hermitian matrices are real linear combinations of densities, and every
complex matrix is a complex linear combination of Hermitian matrices.
It therefore also specifies the action on all references.

Here is the identity-channel extremality argument in the required
input-output dimensions. For a map $\Lambda:M_3\to M_5$ use its
output-first, unnormalized Choi matrix

$$
J(\Lambda)=\sum_{i,j=0}^2\Lambda(|i\rangle\langle j|)
                               \otimes|i\rangle\langle j|.
$$

Then $J(\iota)=|B\rangle\!\rangle\langle\!\langle B|$ has rank one
and trace three. Each channel
$\mathcal E_a=\mathcal D_a\circ\iota\circ\mathcal N_a$ is CPTP.
For a vector $y$ orthogonal to $|B\rangle\!\rangle$, equation (3.1)
gives

$$
0=\sum_a p_a\langle y,J(\mathcal E_a)y\rangle.
$$

Every summand is nonnegative. For each $p_a>0$ its quadratic form
vanishes on the entire orthogonal complement. A positive matrix with
zero quadratic form on a vector annihilates that vector, by its positive
square root. Hence $J(\mathcal E_a)$ is supported on the same single
line. Its trace is three by trace preservation, so
$J(\mathcal E_a)=J(\iota)$ and $\mathcal E_a=\iota$.
For square input-output coordinates this is exactly rank-one-Choi
extremality of the identity channel. In particular, different summaries
cannot compensate for an erroneous positive-probability branch.

Fix such an $a$. A Kraus family for $\mathcal N_a$ is
$F_h=\sqrt{w_{a,h}}Q_h$. Choose any Kraus family $d_\ell$ of
$\mathcal D_a$ on $H$. The composed embedding channel has Kraus operators
$d_\ell BF_h$. Its rank-one Choi matrix forces every individual
vectorized Kraus operator to lie in the line spanned by $B$:

$$
d_\ell BF_h=c_{\ell h}B.
$$

Indeed its Choi matrix is the sum of the positive rank-one matrices of
these vectors; testing an orthogonal vector gives the same nonnegativity
argument. Trace preservation of $\mathcal D_a$ now gives directly

$$
\begin{aligned}
F_h^\dagger F_k
&=F_h^\dagger B^\dagger
       \left(\sum_\ell d_\ell^\dagger d_\ell\right)BF_k\\
&=\sum_\ell\overline{c_{\ell h}}c_{\ell k}I_3.
\end{aligned}
\tag{3.2}
$$

This is the Knill–Laflamme cross-term condition with code $I_3$, or
$P_R$ in the embedded description [KL, Theorem 3.2, (19)–(20)].
Its hypotheses have been derived for the actual coarsened branch;
input-independent fine-label probabilities alone do not imply (3.2).
For positive $w_{a,h},w_{a,k}$ it follows that

$$
Q_h^\dagger Q_k=\lambda I_3.
$$

The left side is unitary, so $|\lambda|=1$. Thus every positively
weighted history in this summary lies in one projective class.
This argument uses no restriction of the decoder to $R$, no unitary
assumption about it, and no omission of complex cross terms.

Conversely, choose a representative $Q_a$ for the unique class of a
positive summary. Phases disappear under conjugation, so
$\mathcal N_a=\operatorname{Ad}_{Q_a}$. Define on all of $H$

$$
D_a=BQ_a^\dagger B^\dagger+(I_5-P_R).
\tag{3.3}
$$

The summands act on orthogonal reducing subspaces. Their products with
their adjoints sum to $P_R+(I_5-P_R)=I_5$ in both orders, so $D_a$ is
unitary. Its conjugation is a CPTP full-$H$ decoder with
$D_aBQ_a=B$. Every positive conditional branch therefore recovers
$\iota$, and summing recovers (3.1). Tensoring that identity with
$\operatorname{id}_Z$ recovers every entangled reference input.
The choice of decoder uses just the counted representative index and
fixed control specifications. $\square$

**Convention 3.4 (Seeds and non-discrete views).** The same criterion has
an almost-everywhere version for a measurable classical view. To state it
precisely, use standard Borel outcome spaces and measurable decoding
channels. Let $\nu_h$ be its conditional probability measure given $h$,
let $\lambda=\sum_h\nu_h$, and write $f_h=d\nu_h/d\lambda$.
Then $\sum_h f_h=1$ almost everywhere and the view law is
$2^{-n}\lambda$. At a view $a$ the conditional channel has weights
$f_h(a)$. The proof of Theorem 3.3 applies almost everywhere: integrate
the nonnegative Choi quadratic forms and use a finite basis of the
orthogonal complement to obtain one common full-measure set. On it,
all $h$ with $f_h(a)>0$ have the same class. A continuous view does
not constitute a finite alphabet just because its individual points
have probability zero.

In particular, a discarded private seed is already averaged into $r$ or
$\nu_h$. A visible seed correlated with $h$ is part of the counted view.
If a shared seed $S$ is explicitly independent of the labels and is
supplied separately without charge, condition on $S$. Exact averaged
recovery and the positive-Choi argument imply conditional exact recovery
for almost every $S$. Independence leaves all the finitely many histories
with probability $2^{-n}$ at each such seed. Their simultaneous
full-measure set exists because there are finitely many histories.
The same class-count lower bound holds on each conditional alphabet.
Independent shared randomness therefore cannot lower the finite
alphabet bound. A history-dependent seed does not satisfy this
independence premise.

## 4. Terminal optimality and online implementation

**Theorem 4.1 (Exact terminal alphabet and prefix bound).** For either
instrument at any known horizon $n$, the minimum finite terminal
alphabet for Assumption 1.4 is exactly $m_n$. It is attained by an online
classical procedure using at most $m_n$ register values at every prefix,
a declared deterministic clock, and fixed time-dependent tables.
The bound includes randomized compression and arbitrary CPTP recovery.

Proof. Every one of the $2^n$ histories has positive probability. At
least one terminal value receives positive weight from each history.
By Theorem 3.3, histories in different projective classes have disjoint
sets of such values. Choosing one history per class therefore requires
at least $m_n$ values. Conversely, storing its class is sufficient and
uses $m_n$ values, with inverse (3.3).

This terminal statistic can be accumulated without a larger history
register. If two prefix products differ only by a phase, left
multiplication by either $Q_j$ preserves that relation. Thus the rule

$$
[Q]\longmapsto[Q_jQ]
$$

is well-defined. Also, for $0\le t\le n$ the map

$$
\mathcal P_t\longrightarrow\mathcal P_n,\qquad
[Q]\longmapsto[Q_0^{\,n-t}Q]
\tag{4.1}
$$

is injective, since $Q_0^{n-t}$ is invertible and can be cancelled from
a projective equality. Its image consists of the histories obtained by
appending $n-t$ zeros. Consequently $|\mathcal P_t|\le m_n$.

For each $t$ choose a fixed injection
$\ell_t:\mathcal P_t\to\{1,\ldots,m_n\}$.
Initialize at $\ell_0([I_3])$. At step $t+1$ the table sends
$\ell_t([Q])$, on input $j$, to $\ell_{t+1}([Q_jQ])$.
Unreachable entries can be filled arbitrarily. The decoder table at
$t=n$ assigns (3.3) to each reachable terminal class. This realizes the
claimed register bound with no auxiliary archive. $\square$

**Definition 4.2 (Sizes separated from register cardinality).** The
construction just given can use $n$ transition tables of at most
$2m_n$ entries each, hence at most $2nm_n$ entries in total, and a
terminal table of at most $m_n$ inverse controls. The declared clock
has the deterministic prefix values $0,\ldots,n$; its value is known
from the horizon schedule and is not an extra observation of the
history. The register itself has at most $m_n$ values. These are
separate size statements. They assert neither bounded table size as
$n$ varies nor any bound on the description of an exact matrix or its
calibrated inverse. If a clock or table selection instead carries extra
history, Definition 1.5 counts it in the view and Theorem 3.3 applies
to the resulting joint variable.

## 5. Unrotated instrument: six homogeneous register values

**Theorem 5.1 (Exact unrotated counts and uniform minimum).** For the
$f$-basis instrument,

$$
m_0=1,\qquad m_1=2,\qquad m_2=4,\qquad m_n=6\quad(n\ge3).
$$

A single homogeneous six-value classical register works at every horizon,
with no horizon-dependent transition tables. Six values are necessary
for every $n\ge3$, even for randomized compression and arbitrary CPTP
terminal decoders.

Proof. Write $a=U_0=(23)$ and $b=U_1=(132)$, with permutation notation
on the three coordinates numbered $1,2,3$. They satisfy

$$
a^2=e,\qquad b^3=e,\qquad aba=b^2,
$$

and generate the faithful permutation representation of $S_3$.
Two permutation matrices that differ by a scalar phase are equal:
the nonzero entry in any chosen column is one in both, so their
locations and then the scalar must coincide. Projective classes here
are therefore ordinary group elements.

In chronological order, with the earliest factor on the right,

$$
\mathcal P_0=\{e\},\quad
\mathcal P_1=\{a,b\},\quad
\mathcal P_2=\{e,ba,ab,b^2\}.
$$

These sets have sizes $1,2,4$. At length three the following histories
already give all six elements; the column-image tuples use indices
$0,1,2$ as in the qutrit matrices.

| Chronological history | Product | Column-image tuple |
| --- | --- | --- |
| $000$ | $a$ | $(0,2,1)$ |
| $001$ | $b$ | $(2,0,1)$ |
| $010$ | $b^2$ | $(1,2,0)$ |
| $011$ | $b^2a$ | $(1,0,2)$ |
| $110$ | $ab^2=ba$ | $(2,1,0)$ |
| $111$ | $e$ | $(0,1,2)$ |

Thus $\mathcal P_3=S_3$. If $\mathcal P_n=S_3$, then
$\mathcal P_{n+1}=a\mathcal P_n\cup b\mathcal P_n=S_3$, since left
multiplication by a group element is a bijection. Induction proves
the asserted tail for all $n$, rather than extrapolating a finite list.

For the homogeneous realization initialize $g=e\in S_3$ and update
$g\leftarrow U_jg$ on the supplied label $j$. An explicit fixed table is

| Current $g$ | Next value on $0$ | Next value on $1$ |
| --- | --- | --- |
| $e$ | $a$ | $b$ |
| $b$ | $b^2a$ | $b^2$ |
| $b^2$ | $ba$ | $e$ |
| $a$ | $e$ | $ba$ |
| $ba$ | $b^2$ | $b^2a$ |
| $b^2a$ | $b$ | $a$ |

By induction $g$ is the exact accumulated permutation. At termination
use $Bg^\dagger B^\dagger+(I_5-P_R)$, whose conjugation recovers the
whole qutrit and reference. The same table has twelve transition
entries and six inverse controls for all horizons; the clock is not
needed to choose a transition. Theorem 4.1 proves six-value minimality
once $n\ge3$, hence minimality of any uniformly bounded terminal
alphabet over all horizons. A binary encoding can use three bits with
two unused codewords; this does not count the other resources of
Definition 1.5 as three bits or six states. $\square$

## 6. Rotated instrument: an unbounded same-horizon terminal alphabet

**Theorem 6.1 (Rotated lower bound at $\theta=\pi/6$).** For the
$g$-basis instrument with $c=\sqrt3/2$, $s=1/2$, write its reachable
class count as $m_n^{\mathrm{rot}}$. Then

$$
m_0^{\mathrm{rot}}=1,\qquad
n\le m_n^{\mathrm{rot}}\le2^n\quad(n\ge1).
$$

Consequently no fixed finite terminal alphabet works at every horizon
under Assumption 1.4, even with a known horizon, a clock, randomized
classical updates, and arbitrary CPTP terminal recovery. The two
instruments in this theorem and Theorem 5.1 still have exactly the
same full $M_5$ averaged channel.

Proof. In qutrit coordinates put

$$
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\qquad T=\xi^\perp.
$$

Both $U_0,U_1$ fix $\xi$, whereas

$$
W\xi=\xi,\qquad V_0\xi=V_1\xi=e^{i\theta}\xi.
\tag{6.1}
$$

The rotated branches do not fix $\xi$ pointwise. Every length-$n$
word acts on it by the same eigenvalue $e^{in\theta}$. If two such
words satisfy $Q_h=\lambda Q_k$, evaluation on $\xi$ forces
$\lambda=1$. Hence projective equality at a fixed horizon is exactly
ordinary matrix equality. This observation retains the phase in (6.1).

The unitary matrices $U_j,W,V_j$ preserve both $\mathbb C\xi$ and $T$,
so this is a common reducing decomposition. An explicit orthonormal
basis of $T$ is

$$
t_1=(1,-1,0)^{\mathsf T}/\sqrt2,\qquad
t_2=(1,1,-2)^{\mathsf T}/\sqrt6.
$$

In this basis the restrictions are

$$
U_{0,T}=\begin{pmatrix}1/2&\sqrt3/2\\\sqrt3/2&-1/2\end{pmatrix},\quad
W_T=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\quad
U_{1,T}=\begin{pmatrix}-1/2&\sqrt3/2\\-\sqrt3/2&-1/2\end{pmatrix}.
$$

It follows that

$$
V_{0,T}=U_{0,T}\begin{pmatrix}e^{-i\theta}&0\\0&e^{i\theta}\end{pmatrix}
=\begin{pmatrix}
e^{-i\theta}/2&\sqrt3 e^{i\theta}/2\\
\sqrt3 e^{-i\theta}/2&-e^{i\theta}/2
\end{pmatrix}.
\tag{6.2}
$$

In particular $\det V_{0,T}=-1$ and
$\operatorname{Tr}V_{0,T}=-i\sin\theta$.
The matrix $M=iV_{0,T}$ is therefore unitary with determinant one and
trace $\sin\theta=1/2$. Its characteristic polynomial and eigenvalues
are exactly

$$
\chi_M(x)=x^2-\tfrac12x+1,\qquad
\mu_\pm=\frac{1\pm i\sqrt{15}}4.
$$

The ratio of the eigenvalues of $M$, and equally of $V_{0,T}$, is

$$
\rho=\frac{\mu_+}{\mu_-}=\frac{-7+i\sqrt{15}}8,\qquad
\rho+\rho^{-1}=-\frac74.
\tag{6.3}
$$

This ratio is not a root of unity. Otherwise $\rho$ and $\rho^{-1}$
would be algebraic integers, and so would their sum. A rational
algebraic integer is an integer: if a reduced $a/b$ satisfies a monic
integral polynomial of degree $k$, multiplication by $b^k$ gives
$b\mid a^k$, hence $b=1$. This contradicts $-7/4\notin\mathbb Z$.

For each nonzero integer $d$, the two eigenvalues of $V_{0,T}^d$ remain
distinct, since equality would imply $\rho^d=1$. Its two eigenspaces
are the same one-dimensional eigenspaces as those of $V_{0,T}$.
Any operator commuting with $V_{0,T}^d$ preserves each of these
lines, and therefore commutes with $V_{0,T}$. This power-commutant
argument takes place on $T$, not on the entire qutrit.

Suppose now that $W$ commuted with $V_0^d$ for some nonzero $d$.
Restricting to $T$ and using the preceding paragraph would give
$[W_T,V_{0,T}]=0$. On $\mathbb C\xi$ both operators are scalars,
$1$ and $e^{i\theta}$, so they commute there as well. But (6.2) gives

$$
W_TV_{0,T}-V_{0,T}W_T
=\begin{pmatrix}
0&-\sqrt3 e^{i\theta}\\\sqrt3 e^{-i\theta}&0
\end{pmatrix}\ne0.
\tag{6.4}
$$

Equivalently on the full qutrit,
$WV_0-V_0W=(WU_0-U_0W)e^{i\theta W}\ne0$, since the two actual
transpositions do not commute and the exponential is invertible.
We conclude that

$$
[W,V_0^d]\ne0\qquad(d\in\mathbb Z\setminus\{0\}).
\tag{6.5}
$$

No simple-spectrum assertion on all three dimensions was used.
A power's eigenvalue on $\mathbb C\xi$ could coincide with one on $T$;
such a collision cannot invalidate the argument because $W$ already
preserves the two summands. Only the two eigenvalues within $T$ need
to remain distinct.

Fix $n\ge1$ and consider the $n$ chronological histories with exactly
one label $1$, at positions $k=1,\ldots,n$. Their actual products are

$$
X_k=V_0^{n-k}V_1V_0^{k-1}
    =V_0^{n-k+1}WV_0^{k-1}.
\tag{6.6}
$$

Multiplying all these words on the left by $V_0^{-n}$ gives

$$
C_{k-1}=V_0^{-(k-1)}WV_0^{k-1}.
$$

If $C_j=C_\ell$ for $j\ne\ell$, multiply the equality on the left
by $V_0^j$ and on the right by $V_0^{-\ell}$. It gives
$WV_0^{j-\ell}=V_0^{j-\ell}W$, contradicting (6.5).
Thus the $n$ words in (6.6) are pairwise distinct. Their common
$\xi$ eigenphase from (6.1) excludes any remaining projective
identification. Each is a genuine acquired history with probability
$2^{-n}$, so exact recovery cannot omit one as a zero-probability case.
Theorem 4.1 now gives $m_n^{\mathrm{rot}}\ge n$.

For the upper bound one may retain the full acquired binary history,
whose $2^n$ possible values determine the exact inverse product and
its full-$H$ extension (3.3). The empty history gives one class.
The lower bound tends to infinity and proves the claimed failure of
any uniform finite alphabet, including schemes with time-dependent
updates and an externally known horizon. The full-channel equality
was proved independently in Theorem 2.2. $\square$

**Proposition 6.2 (Infinite order is insufficient with a known horizon).**
There exist two unitary labels generating an infinite projective-order
evolution but having one reachable projective word class at every
fixed horizon.

Proof. On $\mathbb C^3$ take
$L=\operatorname{diag}(1,e^{2\pi i\alpha},1)$ with irrational $\alpha$,
and give both labels the same branch unitary $L$, each with weight
$1/2$. This is a legitimate measured pure-environment realization:
$x\mapsto Lx\otimes(f_0+f_1)/\sqrt2$, followed by the $f$ measurement,
with a unitary completion as in §2. If $L^d$ were scalar for nonzero
integer $d$, its first diagonal entry would force that scalar to be
one, and then $d\alpha$ would be integral, a contradiction. Thus its
projective order is infinite. Nevertheless every length-$n$ history
has product $L^n$, so the known $n$ determines the inverse and a
one-value summary suffices. The distinct same-horizon words of (6.6),
not infinite order alone, establish Theorem 6.1. $\square$

## 7. Resource scope and primary mathematical interfaces

**Convention 7.1 (Instrument information and recovery target).** The
unmeasured owning channel supplies no observed outcome labels.
Assumption 1.4 adds the specified measurements, result carriers and
classical communication. The outcomes are unitary-mixture flags on
$R$, not reconstructed five-window edge labels. The inverse restores
the qutrit-reference input; it does not simultaneously keep an
independent copy of the unknown input or reconstruct an original edge
archive. Conditional inversion on $R$ does not supply a full-$H$
inverse for the nonunitary effects displayed in §2.

The six-value statement of Theorem 5.1 concerns only the complete
retained terminal statistic after processing $n$ actual acquisitions.
Those acquisitions, preparations, measurement communication,
calibration, fixed tables and inverse controls remain the separate
resources of Definition 1.5. In particular no conclusion about a
different label-acquisition task or its costs follows from this
statistic. An unbounded buffer or history-dependent control description
would increase the counted view. A fixed description with a growing
amount of history-dependent working data does not evade that rule.

Retained quantum environments, a quantum summary, intermediate
system feedback, a change of later measurement bases conditioned on
earlier labels, heralded failure, approximate recovery, restricted
known inputs, and a read of the reference define other tasks.
They are not permissions in Assumption 1.4.

**Convention 7.2 (Literature-attested correction interfaces).** The
following primary results are used as the indicated intermediate
suppliers or context. The matrices and the two-instrument multi-step
synthesis in §§2–6 are repo-derived ordinary calculations; no
literature-priority classification follows from that designation.

| Primary source and fixed version | Exact hypotheses and correspondence |
| --- | --- |
| E. Knill and R. Laflamme, *A Theory of Quantum Error-Correcting Codes*, [quant-ph/9604034v1][KL], Theorems 3.1–3.2, especially (19)–(20), and the entangled-state discussion in §5.3 | The code here is all of $\mathbb C^3$, or its embedding $R$. After conditioning on a summary the errors are $F_h=\sqrt{w_{a,h}}Q_h$. Every complex cross term $F_h^\dagger F_k$ is included. Equation (3.2) derives its scalar-compression condition directly from a deterministic CPTP left inverse; references remain untouched. |
| M. Gregoratti and R. F. Werner, *Quantum Lost and Found*, [quant-ph/0209025v1][GW1], instrument equation (3), unitary Kraus recombination (6), pure-environment Theorem 1, and Proposition 2 in §II.C.1 | The fine outcomes are actual orthonormal measurements of a pure environment. On $R$, $t_j=qU_j$ or $qV_j$ and $t_j^\dagger t_j=I_3/2$, so their specified fine branches admit inverse correction. A coarsened summary generally contains several Kraus terms; the fine-branch condition alone does not certify it. Theorem 3.3 supplies the required additional necessity. The present full-$H$ map is not asserted correctable. |
| M. Gregoratti and R. F. Werner, *On quantum error-correction by classical feedback in discrete time*, [quant-ph/0403092v1][GW2], §II.2, (4)–(7), Figure 1(c), and Proposition 2, (10)–(12) | The setting allows fresh Markovian environments, specified measured decompositions and the deferred-correction special case. Here each intermediate correcting channel is identity, the instrument is fixed, and the errors are chronological products. No terminal-record optimum is imported from that paper. |
| M. A. Nielsen and I. L. Chuang, *Programmable quantum gate arrays*, [quant-ph/9703032v1][NC], (1)–(3), the stated Result and proof (6)–(10) | Its deterministic exact setting has one fixed unitary processor, pure program states initially independent of arbitrary data, and target unitaries distinct up to phase; different targets require orthogonal program states. This is contextual only. The present object is a measured classical summary with arbitrary CPTP decoding, whose lower bound was proved in §3 without replacing its hypotheses by quantum-program assumptions. |
| D. D'Angeli, E. Rodaro and J. P. Waechter, *On the Complexity of the Word Problem for Automaton Semigroups and Automaton Groups*, [1611.09541v2][DRW], §2 and adding-machine Example 1 | Its state words of finite synchronous transducers induce transformations of entire word trees. This gives contextual composition language, not a recovery criterion, a bounded exact accumulator, or an identification of the present unitary group as an automaton group. Finite transducers can generate infinite groups; no word-problem complexity result is transferred. |

The supplier [DIL, Theorem 2.2] already applies the one-step
Gregoratti–Werner criterion to its own named entire-system realization.
Its Assumption 2.3 separately requires the actual environment read,
result communication, calibrated inverse controls and their resources.
The same kind of additional permissions is explicit here, with the
system correspondence restricted to $R$. The standard correction
principle is not restated as a new general result.

**Definition 7.3 (Remaining counting problem).** Determining the exact
sequence $m_n^{\mathrm{rot}}$, or a stronger asymptotic lower bound,
is a separate open counting problem. Theorem 6.1 establishes only
$n\le m_n^{\mathrm{rot}}\le2^n$ for $n\ge1$ and unboundedness.
It supplies neither an exact rotated sequence nor an exponential
lower bound. The separation rests on the all-$n$ spectral and
same-horizon conjugacy argument, not on any finite enumeration of
rotated products.

[OWN]: https://github.com/the-omega-institute/trureturing/blob/c447c32041b270a42a625aa715088565ddfd1771/docs/develop/theory/AURIC_FIB_FIVE_WINDOW_QUANTUM_MEMORY.md
[DIL]: https://github.com/the-omega-institute/trureturing/blob/c447c32041b270a42a625aa715088565ddfd1771/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MINIMAL_RECORD_DILATIONS.md
[KL]: https://arxiv.org/html/quant-ph/9604034v1
[GW1]: https://arxiv.org/html/quant-ph/0209025v1
[GW2]: https://arxiv.org/html/quant-ph/0403092v1
[NC]: https://arxiv.org/html/quant-ph/9703032v1
[DRW]: https://arxiv.org/html/1611.09541v2

## 追加锚（本行以下为增补区）

## 8. Exact rotated growth from an integral residue invariant

**Definition 8.1 (Actual letters and integral coordinates).** In this
section fix the instrument of Definition 2.1 at $\theta=\pi/6$, so that
$c=\sqrt3/2$, $s=1/2$. Retain the actual qutrit matrices $U_0,U_1,W$
of Theorem 2.2 and set

$$
V_0=cU_0+isU_1,\qquad V_1=isU_0+cU_1=V_0W,\qquad
\zeta=e^{i\pi/6}=\frac{\sqrt3+i}{2}.
\tag{8.1}
$$

The reducing summands are $\mathbb C\xi$ and $T=\xi^\perp$ as in
Theorem 6.1. Besides its orthonormal basis $(t_1,t_2)$, use the basis

$$
b_1=(1,0,-1)^{\mathsf T},\qquad b_2=(0,1,-1)^{\mathsf T},\qquad
C=\begin{pmatrix}
1/\sqrt2&-1/\sqrt2\\
\sqrt{3/2}&\sqrt{3/2}
\end{pmatrix}.
\tag{8.2}
$$

Here $[b_1\ b_2]=[t_1\ t_2]C$ and $\det C=\sqrt3$. For an
operator $L$ preserving $T$, denote its matrix in $(b_1,b_2)$ by
$\widehat L=C^{-1}L_TC$. These are coordinates on the same subspace;
the basis $b_1,b_2$ is not asserted orthonormal. Put

$$
\tau=i\sqrt3,\qquad \mathcal O=\mathbb Z[\tau]\subset\mathbb C,
\qquad \tau^2=-3,\qquad P_j=-2i\widehat V_j.
\tag{8.3}
$$

For a chronological history $h=(h_1,\ldots,h_n)$ write
$P_h=P_{h_n}\cdots P_{h_1}$, with $P_{\varnothing}=I_2$.
Thus $P_h=(-2i)^nC^{-1}(Q_h)_TC$, where $Q_h$ retains the
chronological convention of Definition 3.1. The scalar in (8.3) is
an algebraic device for proving identities, not a replacement of an
instrument branch.

**Theorem 8.2 (All finite positive words and exact fixed-horizon growth).**
For the actual instrument of Definition 8.1, the map from finite binary
histories to qutrit projective words is injective, including between
different lengths:

$$
[Q_h]=[Q_g]\quad\Longleftrightarrow\quad h=g.
\tag{8.4}
$$

In particular,

$$
m_n^{\mathrm{rot}}=2^n\quad(n\ge0),\qquad
\lim_{n\to\infty}(m_n^{\mathrm{rot}})^{1/n}=2,\qquad
\lim_{n\to\infty}\frac{\log m_n^{\mathrm{rot}}}{n}=\log2.
\tag{8.5}
$$

This gives the exact fixed-angle sequence asked for in Definition 7.3;
the bound in Theorem 6.1 is a weaker consequence.

Proof. First verify the correspondence with the actual letters. Applying
the permutations of Theorem 2.2 to $b_1,b_2$ gives

$$
\widehat U_0=\begin{pmatrix}1&0\\-1&-1\end{pmatrix},\qquad
\widehat U_1=\begin{pmatrix}0&1\\-1&-1\end{pmatrix},\qquad
\widehat W=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\tag{8.6}
$$

For example, $U_0b_1=b_1-b_2$, $U_0b_2=-b_2$,
$U_1b_1=-b_2$, $U_1b_2=b_1-b_2$, and $W$ interchanges $b_1,b_2$.
The relation (8.2) also verifies that these are the conjugates of
the orthonormal restrictions in Theorem 6.1. Equations (8.1)–(8.3)
therefore give the integral matrices

$$
\begin{aligned}
P_0&=\widehat U_1-\tau\widehat U_0
 =\begin{pmatrix}-\tau&1\\\tau-1&\tau-1\end{pmatrix},\\
P_1&=\widehat U_0-\tau\widehat U_1
 =\begin{pmatrix}1&-\tau\\\tau-1&\tau-1\end{pmatrix}
 =P_0\widehat W,\\
\det P_0&=1-\tau^2=4,\qquad \det P_1=\tau^2-1=-4.
\end{aligned}
\tag{8.7}
$$

Both matrices are invertible over the field $\mathbb Q(\tau)$.
This is the field in which cancellation below is performed.

Every element of $\mathcal O$ has a unique expression $a+b\tau$
with $a,b\in\mathbb Z$, since $1,\tau$ are linearly independent over
$\mathbb Q$. Define

$$
\phi:\mathcal O\longrightarrow\mathbb F_2,\qquad
\phi(a+b\tau)=a+b\pmod2.
\tag{8.8}
$$

It preserves addition and the unit. For multiplication,

$$
(a+b\tau)(c+d\tau)=(ac-3bd)+(ad+bc)\tau,
$$

whose coefficient sum modulo two is
$ac+bd+ad+bc=(a+b)(c+d)$. Thus $\phi$ is a ring homomorphism.
There is no need to identify $\mathcal O$ with the full ring of
integers of its field. Applying $\phi$ entrywise gives

$$
\phi(P_0)=\phi(P_1)=E=\begin{pmatrix}1&1\\0&0\end{pmatrix},\qquad
E^2=E\ne0,\qquad
\phi(\widehat W)E=\begin{pmatrix}0&0\\1&1\end{pmatrix}\ne E.
\tag{8.9}
$$

Consequently every nonempty positive product of $P_0,P_1$, at
every length, has residue $E$: the residue of a product of length
$k\ge1$ is $E^k=E$.

Suppose two distinct words of the same length have equal $P$ products.
Read the factors from the left and cancel their common leading factors
over $\mathbb Q(\tau)$. In chronological notation this reads the
histories from the latest label backwards; reversal of binary strings
is a bijection and loses no history. At the first unequal factor,
exchange the two sides if necessary to obtain

$$
P_0X=P_1Y=P_0\widehat W Y,\qquad X=\widehat W Y.
\tag{8.10}
$$

The tails $X,Y$ are integral positive products of the same length
$k\ge0$. If $k=0$, both tails are $I_2$, and (8.10) would force
$I_2=\widehat W$, which is false. If $k\ge1$, their residues are
both $E$, and reducing the integral equality $X=\widehat W Y$
would give $E=\phi(\widehat W)E$, contradicting (8.9).
This proves same-length injectivity of the integral products.
In particular no inverse was taken modulo two: $\det P_j$ has zero
residue, but all inverses were used in $\mathbb Q(\tau)$ before
reducing the integral equality of tails.

To pass to qutrit projective words, keep the common line and its phase.
The actual permutations fix $\xi$, so (8.1) gives

$$
V_j\xi=\zeta\xi,\qquad Q_h\xi=\zeta^{|h|}\xi.
\tag{8.11}
$$

If $|h|=|g|=n$ and $Q_h=\lambda Q_g$, applying both sides to
$\xi\ne0$ forces $\lambda=1$. Restriction to $T$ and multiplication
by the common factor $(-2i)^n$ then give $P_h=P_g$. The preceding
argument forces $h=g$. This also handles $n=0$, where the sole
product is the identity.

For different lengths, assume $|h|=m>n=|g|\ge0$ and
$Q_h=\lambda Q_g$. Equation (8.11) forces
$\lambda=\zeta^{m-n}$. Restriction and the definition of $P_h$ give
an equality in $M_2(\mathcal O)$:

$$
P_h=(-2i)^{m-n}\zeta^{m-n}P_g
    =(1-\tau)^{m-n}P_g,
\qquad -2i\zeta=1-\tau.
\tag{8.12}
$$

Its left side is a nonempty product and has residue $E\ne0$.
Its right side has residue zero, since $\phi(1-\tau)=0$ and
$m-n>0$. This remains true when $g$ is empty and $P_g=I_2$.
The contradiction excludes every cross-length collision. There are
exactly $2^n$ histories at length $n$, so (8.4) implies (8.5).
The proof uses an invariant for every word, rather than an enumeration,
infinite order, density, or a group-ball estimate. $\square$

## 9. Exact retained memory and its recovery permissions

**Convention 9.1 (Restricted correction and primary correspondence).**
Use precisely Assumption 1.4 and the complete counted view of
Definition 1.5. Every binary label is actually measured and supplied;
the same fixed instrument is repeated with a fresh pure environment
at each step. Only classical record updates occur between steps.
The terminal decoder may be any CPTP map on the whole five-dimensional
$H$, while the input to be recovered is $B\mathbb C^3=R$, entangled
with any untouched finite reference $Z$. There is no reference read,
intermediate quantum feedback, adaptive instrument, input-dependent
quantum side information, or success postselection. Success may be
required only after averaging over all labels and classical randomness.

The one-step correction supplier [GW1, Proposition 2, §II.C.1] has the
criterion

$$
t_\alpha^\dagger t_\alpha=c_\alpha I,\qquad
c_\alpha\ge0,\qquad\sum_\alpha c_\alpha=1.
\tag{9.1}
$$

Its system corresponds here to the qutrit $\mathbb C^3\cong R$.
For the actual measured branches $A_j$ of §2 the correspondence is

$$
A_jB=Bt_j,\qquad t_j=V_j/\sqrt2,\qquad
t_j^\dagger t_j=I_3/2.
\tag{9.2}
$$

This is a scaled unitary on the restricted system. The full operators
$A_j:H\to H$ have range in the proper subspace $R$ and are not
scaled full-$H$ unitaries. For a history $h$, its restricted Kraus
operator is $2^{-n/2}Q_h$. The fresh-environment model and chronological
product are the deferred-correction case of [GW2, Proposition 2,
(10)–(12), Figure 1(c)], with all earlier correcting channels the
identity. That supplier allows more feedback than Assumption 1.4;
only this deferred case is used here. The named realization of
[DIL, Theorem 2.2 and Assumption 2.3] has the same one-step correction
interface on its entire system; its system is not identified with the
present full $H$.

For an arbitrary random summary $a$, use the actual conditional errors
$F_h=\sqrt{w_{a,h}}Q_h$ of Definition 3.2. The code in [KL,
Theorem 3.2, (19)–(20)] is all of $\mathbb C^3$, or $R$ after
embedding. Its cross-term condition is

$$
F_h^\dagger F_k=\gamma_{hk}I_3.
\tag{9.3}
$$

Theorem 3.3 already derives (9.3), including arbitrary full-$H$
decoders and ensemble-only success, and identifies it with one
projective class per positive view. Fine-label correction under
(9.1)–(9.2) alone would not justify merging fine labels. That existing
summary criterion, with the exact count in Theorem 8.2, supplies the
memory conclusions below.

**Theorem 9.2 (Optimal alphabet, bits, and discrete entropy).** At every
known horizon $n\ge0$ for the actual $\theta=\pi/6$ instrument,
under Convention 9.1 the following minima are attained:

$$
\begin{aligned}
\min |\text{finite terminal alphabet}|&=2^n,\\
\min \text{fixed-length binary bits}&=n,\\
\min H_{\mathrm{Sh}}(\mathsf Y)&=n.
\end{aligned}
\tag{9.4}
$$

The last minimum ranges over discrete complete decoder-visible views
$\mathsf Y$, including countable views with possibly infinite Shannon
entropy. The bounds allow random summaries and arbitrary full-$H$
CPTP decoders. More strongly, the entire chronological history is a
function of any successful discrete complete view almost surely.
Here $H_{\mathrm{Sh}}(\mathsf Y)=-\sum_y p_y\log_2p_y$, with
$0\log_2 0=0$; all entropies in this section are Shannon entropies
in bits.

Proof. Let $\mathsf H_n$ be the history variable. By Definition 3.1,
every $h\in\{0,1\}^n$ has probability $2^{-n}$ for every permitted
qutrit-reference input. If a summary value $a$ receives positive
conditional weight from histories $h,g$, Theorem 3.3 requires
$[Q_h]=[Q_g]$. Theorem 8.2 forces $h=g$. Thus the nonempty supports
$\{a:r(a\mid h)>0\}$ are disjoint for all $2^n$ histories. This
uses the existing criterion with its ensemble-only and full-$H$
decoder hypotheses; no unitary restriction on a competing decoder is
being imposed.

Every finite view consequently has at least $2^n$ values of positive
probability. On a countable view, assign to each positive-probability
value its unique history. This defines a function with
$\mathsf H_n=g(\mathsf Y)$ almost surely, so

$$
H_{\mathrm{Sh}}(\mathsf Y)=H_{\mathrm{Sh}}(\mathsf H_n)
 +H_{\mathrm{Sh}}(\mathsf Y\mid\mathsf H_n)
\ge H_{\mathrm{Sh}}(\mathsf H_n)=n.
\tag{9.5}
$$

The chain rule remains valid with the nonnegative extended entropy
of a countable view. A register of $b$ fixed-length binary bits has
at most $2^b$ values; hence $2^b\ge2^n$ requires $b\ge n$.

For attainment, initialize the integer record $r_0=0$ and, on the
supplied chronological label $h_k$, update

$$
r_k=2r_{k-1}+h_k,\qquad 0\le r_k<2^k\le2^n.
\tag{9.6}
$$

At the declared deterministic prefix $k$, $r_k$ is the length-$k$
binary history with leading zeros interpreted using that prefix.
At termination the known $n$ makes $r_n$ a bijective encoding of
the complete history. This is an online shift register with $n$
binary bits, at most $2^n$ values at every prefix, and no extra
history archive. Its terminal law is uniform, so its entropy is $n$.

Decode $r_n$ to its history $h$ and use the full-$H$ unitary of
equation (3.3), with the chronological product $Q_h$:

$$
D_h=BQ_h^\dagger B^\dagger+(I_5-P_R),\qquad
\mathcal D_h=\operatorname{Ad}_{D_h}.
\tag{9.7}
$$

On $R$ it is the inverse of the actual accumulated qutrit unitary;
on $R^\perp$ it is identity. Therefore
$D_h^\dagger D_h=D_hD_h^\dagger=I_5$ and $D_hBQ_h=B$.
For every density $\rho$ on $\mathbb C^3\otimes Z$, the normalized
conditional output is corrected by

$$
(D_h\otimes I_Z)(BQ_h\otimes I_Z)\rho
(BQ_h\otimes I_Z)^\dagger(D_h\otimes I_Z)^\dagger
=(B\otimes I_Z)\rho(B\otimes I_Z)^\dagger.
\tag{9.8}
$$

The right side is independent of $h$, so averaging also recovers it.
The block extension defines a channel on all $H$, but recovery is
asserted only for embedded qutrit inputs. At $n=0$ the register has
one value, entropy zero, and $D_{\varnothing}=I_5$. $\square$

**Theorem 9.3 (Seeds and measurable complete views).** Under the same
permissions, a successful standard Borel complete view determines
$\mathsf H_n$ measurably almost surely. If a separately supplied
shared seed $S$ is explicitly declared free and is independent of
$\mathsf H_n$, the conditional finite alphabet bound is still $2^n$
for almost every seed. For a discrete counted view $\mathsf Y$,

$$
H_{\mathrm{Sh}}(\mathsf Y\mid S)\ge n,
\tag{9.9}
$$

and the shift register, ignoring $S$, attains equality. A correlated
decoder-visible seed is part of the counted joint view instead.

Proof. Use the measures $\nu_h$, $\lambda=\sum_h\nu_h$ and densities
$f_h=d\nu_h/d\lambda$ of Convention 3.4. Its almost-everywhere summary
criterion and Theorem 8.2 imply that, outside one common null set,
at most one $f_h$ is positive. Since $\sum_h f_h=1$, exactly one is
positive there. The measurable sets where this is $h$ give a
measurable history function. Thus this conclusion does not rely on
individual continuous outcomes having positive probability.

For a free independent shared seed, the rank-one-Choi argument of
Theorem 3.3 applied to the averaged recovery identity first gives
conditional exact recovery for almost every $S$. Independence
leaves every history conditionally uniform with probability $2^{-n}$.
There are finitely many histories, so these conditions can be imposed
on one common full-measure seed set. Apply the disjoint-support and
entropy arguments of Theorem 9.2 at each such seed, then average the
conditional entropies to obtain (9.9).

Discarded private randomness is already averaged into the compression
kernel. If a visible seed is correlated with the history, its joint
value with all other visible data is the complete view to which the
criterion applies. For example, a seed equal to the history could
make an auxiliary register constant, but that joint view still
contains the whole history. For a non-discrete view the conclusion
is measurable determination of the finite history; it is not a
lower bound on differential entropy, and does not turn a continuous
alphabet into a finite one. $\square$

**Theorem 9.4 (Identical full averaged channel, different exact records).**
For the same dilation and preparation of Definition 2.1, measurement
at $\theta=0$ and at $\theta=\pi/6$ gives, under the same recovery
permissions, the following minimum terminal alphabets:

$$
\begin{array}{c|cccc}
&n=0&n=1&n=2&n\ge3\\ \hline
\theta=0&1&2&4&6\\
\theta=\pi/6&1&2&4&2^n
\end{array}
\tag{9.10}
$$

The averaged channels nevertheless coincide on every complex $M_5$
input and every untouched finite reference. The rotated $n$-bit
minimum counts the complete retained terminal statistic, rather
than the entire apparatus or all operations.

Proof. At $\theta=0$, $g_j=f_j$ and $A_j=K_j$, so Theorem 5.1
applies. At $\theta=\pi/6$, Theorem 9.2 applies. Full-channel
equality follows from Theorem 2.2, which cancels the cross terms
of the two rotated Kraus conjugations on every complex input.
Thus it is the supplied measured instrument and retained view,
in addition to the common averaged channel, that specify this
record-recovery problem.

The six-state homogeneous accumulator of Theorem 5.1 and the shift
register (9.6) process all $n$ actual labels. Both still require the
label acquisitions, measurements, communication, and fresh
environment preparations of Assumption 1.4. The declared horizon,
deterministic clock, calibration, fixed descriptions or tables,
exact matrix precision, and inverse controls are separate resources
as in Definition 1.5. A clock or control choice that varies with the
history is counted in the joint view. The generic construction of
Definition 4.2 permits $2n2^n$ transition entries and $2^n$ inverse
controls in the rotated case; neither those upper bounds nor (9.6)
assert a minimal table size, synthesis cost, or finite precision
implementation of the inverses. Equation (9.7) supplies a full-$H$
decoder for restricted inputs and does not invert the nonunitary
five-dimensional channel on arbitrary $H$ inputs. $\square$

## 10. Restricted rotation group and remaining mathematical boundaries

**Theorem 10.1 (Actual restricted group and the inverse-letter boundary).**
Let $\Gamma_T$ be the subgroup of $PU(2)$ generated by the restrictions
$[V_{0,T}],[V_{1,T}]$ in the orthonormal basis of Theorem 6.1 at
$\theta=\pi/6$. Then

$$
\Gamma_T\cong G(6,3)\cong C_6*_{C_2}D_3,
\tag{10.1}
$$

where $D_3$ has order six. The actual qutrit letters also obey

$$
V_0^{-1}V_1=W\ne I_3,\qquad (V_0^{-1}V_1)^2=I_3.
\tag{10.2}
$$

Thus injectivity of positive words in Theorem 8.2 does not assert
freeness of the group on these two generators. Identification (10.1)
concerns the restricted group; it does not identify the full qutrit
projective group, which retains relative phases between $T$ and
$\mathbb C\xi$.

Proof. Use conjugation on traceless Hermitian $2\times2$ matrices,
in Pauli order $(\sigma_x,\sigma_y,\sigma_z)$, to define
$\pi:U(2)\to SO(3)$. Its kernel is precisely the scalar unitaries:
an operator acting trivially by conjugation commutes with all three
Pauli matrices, hence with all of $M_2$, and is scalar. This realizes
$PU(2)$ faithfully as rotations. Put

$$
D=\begin{pmatrix}e^{-i\pi/6}&0\\0&e^{i\pi/6}\end{pmatrix},\qquad
F=U_{0,T}W_T
 =\begin{pmatrix}-1/2&\sqrt3/2\\-\sqrt3/2&-1/2\end{pmatrix}.
\tag{10.3}
$$

Exact conjugation of the Pauli matrices gives

$$
d=\pi(D)=\begin{pmatrix}
1/2&-\sqrt3/2&0\\\sqrt3/2&1/2&0\\0&0&1
\end{pmatrix},\qquad
r=\pi(F)=\begin{pmatrix}
-1/2&0&\sqrt3/2\\0&1&0\\-\sqrt3/2&0&-1/2
\end{pmatrix}.
\tag{10.4}
$$

They are rotations by $\pi/3$ about $z$ and $2\pi/3$ about $y$,
respectively. Their axes are perpendicular and their exact orders
are six and three. Write $w=\pi(W_T)$,
$x=\pi(V_{0,T})$, $y=\pi(V_{1,T})$. Since $D^3=iW_T$,
$U_{0,T}=FW_T$, $V_{0,T}=U_{0,T}D$, and $V_{1,T}=V_{0,T}W_T$,
the forward correspondence is

$$
w=d^3,\qquad x=rd^4,\qquad y=rd.
\tag{10.5}
$$

Conversely the actual rotation matrices satisfy
$wrw=r^{-1}$ and $r^3=1$, so

$$
w=x^{-1}y,\qquad r=wxwx^{-1},\qquad d=r^{-1}y.
\tag{10.6}
$$

For example, (10.5) gives
$wxwx^{-1}=wrwr^{-1}=r^{-2}=r$. These reverse equations prove
$\langle x,y\rangle=\langle d,r\rangle$; merely expressing $x,y$
in terms of $d,r$ would not suffice.

The primary classification used here is Radin–Sadun, *Subgroups of
SO(3) Associated with Tilings*, Journal of Algebra **202**, 611–633,
[author-hosted journal article][RS], Theorem 1(ii) and Corollary 2,
p. 613, DOI [10.1006/jabr.1997.7320][RS-DOI]. It defines $G(p,q)$
using rotations by $2\pi/p$ and $2\pi/q$ about perpendicular axes.
For even $p\ge4$ and odd $q\ge3$, it gives the faithful presentation,
with its abstract generators mapped to those actual rotations,

$$
G(p,q)\cong
\langle a,b\mid a^p=b^q=1,\ a^{p/2}ba^{p/2}b=1\rangle.
\tag{10.7}
$$

A common spatial rotation sends the paper's ordered $x,z$ axes to
the present $z,y$ axes. Thus $p=6,q=3$, $a\mapsto d$, $b\mapsto r$
satisfy its precise hypotheses. The theorem supplies injectivity of
this presentation, beyond the elementary verification that the
relators vanish. Corollary 2 identifies it as $C_6*_{C_2}D_3$,
where the common involution is $d^3$ and
$D_3=\langle r,d^3\mid r^3=(d^3)^2=1,\ d^3rd^3r=1\rangle$.
Together with (10.5)–(10.6) and the faithful adjoint map this proves
(10.1). This is an application of the cited classification; none
of it is a premise of the elementary residue proof of Theorem 8.2.

Finally $V_1=V_0W$ from the actual qutrit matrices gives (10.2)
directly. The nontrivial reduced inverse-letter word
$(0^{-1}1)^2$ is therefore a relation, despite the absence of any
collision between positive words. Restriction to $T$ discards the
relative block phase with $\mathbb C\xi$, so the restricted
identification alone makes no claim of an isomorphism for the full
$PU(3)$ subgroup. $\square$

**Convention 10.2 (Sources and unresolved extensions).** The basis
correspondence, integral residue argument, and the fixed-instrument
record consequences in §§8–9 are repo-derived ordinary deductions
from the actual owner matrices and the existing summary criterion.
The correction interfaces in Convention 9.1 and the faithful rotation
classification used inside Theorem 10.1 are literature-attested
suppliers, with their system, code, generator, and hypothesis
correspondences specified there. These are statements within the
declared finite-dimensional model.

The all-length projective assertion (8.4) is for the actual qutrit,
using its common $\xi$ eigenphase. It is not inferred merely from
the restricted $PU(2)$ group, density, a spectral gap, or infinite
order. No spectral-gap constant, mixing rate, or estimate for a
different walk enters these conclusions.

The exact sequence for other angles or parameters, other measured
realizations of the same averaged channel, approximate recovery,
quantum summaries or retained quantum environments, intermediate
feedback or adaptive label acquisition, postselected recovery,
reference access, and exact inverse-control cost are unresolved by
these results. The absent-label code problem remains the different
problem of [OWN, Definition 21.1 and Theorem 21.2]. The retained
classical memory optimum does not add a physical realization or a
finite precision implementation premise to the mathematical model.

[RS]: https://web.ma.utexas.edu/users/radin/papers/subgroups.pdf
[RS-DOI]: https://doi.org/10.1006/jabr.1997.7320

## 追加锚（本行以下为增补区）

## 11. The actual angle family and its exact equality relation

**Definition 11.1 (Angle-dependent measured words).** For every real
$\theta$, use the isometry, ready state and outgoing basis $g_0,g_1$
of Definition 2.1, with precisely the permissions of Assumption 1.4
and the complete view of Definition 1.5. Write

$$
a=V_0(\theta)=U_0e^{i\theta W},\qquad
b=V_1(\theta)=aW,\qquad
Q_h(\theta)=V_{h_n}(\theta)\cdots V_{h_1}(\theta),
\qquad m_n(\theta)=|\{[Q_h(\theta)]:|h|=n\}|.
\tag{11.1}
$$

Here $U_0,U_1,W$ are the actual qutrit matrices of Theorem 2.2;
$\xi,T$ and the orthonormal basis $(t_1,t_2)$ are those of
Theorem 6.1. Theorem 2.2 applies at every real $\theta$: these are
measured instruments of the same full complex-linear channel
$\Phi_\circ$ on $M_5$, also after adjoining any untouched finite
reference. Every length-$n$ history has probability $2^{-n}$ on
all permitted inputs. In particular, the family changes the measured
instrument, while keeping that averaged channel fixed.

On $\mathbb C\xi$ both letters act by $e^{i\theta}$. Therefore, for
histories of the same length $n$,

$$
Q_h=\lambda Q_g\quad\Longleftrightarrow\quad
Q_h=Q_g\quad\Longleftrightarrow\quad Q_h|_T=Q_g|_T.
\tag{11.2}
$$

Indeed the first equality on $\xi$ forces $\lambda=1$, and the
common reducing line has the same action for both words. Thus $m_n$
counts exact products of $a_T,b_T$ in $U(2)$. Their images in $PU(2)$
will be used to study a generated group; equality in $PU(2)$ alone
is not the equivalence relation in (11.2). Theorem 8.2 already gives
the stronger, cross-length injectivity assertion at $\pi/6$; that
special assertion is not assumed at other angles.

**Theorem 11.2 (Full-qutrit symmetries and pair equivalence).** The
actual letters satisfy

$$
V_j(\theta+\pi/2)=iV_{1-j}(\theta),\qquad
V_j(-\theta)=\overline{V_j(\theta)}.
\tag{11.3}
$$

Consequently $m_n$ is even and $\pi/2$-periodic for every $n$.
Moreover the following specified equivalences of pairs have no other
parameter identifications. Simultaneous qutrit unitary conjugation,
individual scalar phases on the two letters, and optional interchange
of their labels relate parameters $\theta,\varphi$ if and only if
$\varphi-\theta\in(\pi/2)\mathbb Z$. Allowing complex conjugation
as well gives exactly $\varphi\equiv\pm\theta\pmod{\pi/2}$.
This classifies those operations on pairs, rather than arbitrary
abstract group isomorphisms or coincidences of count sequences.

Proof. Substitution of $\cos(\theta+\pi/2)=-\sin\theta$ and
$\sin(\theta+\pi/2)=\cos\theta$ proves the first identity on the
full qutrit. The matrices $U_j$ are real, proving the second.
At a fixed horizon the first identity contributes the common scalar
$i^n$ and complements every label; conjugation preserves equality.
Both operations therefore give bijections of the counted classes.

The unique common eigenline of $a,b$ is $\mathbb C\xi$.
To see uniqueness, a common eigenvector is also an eigenvector of
$W=a^{-1}b$, and hence of $U_0=ae^{-i\theta W}$. On $T$, in the
basis of Theorem 6.1, $W_T=\operatorname{diag}(-1,1)$ and
$U_{0,T}$ has both off-diagonal entries $\sqrt3/2$. Neither
$W_T$ eigenline is invariant under $U_{0,T}$. A vector in the
$+1$ eigenspace of $W$ has the form $\alpha\xi+\beta t_2$;
the $t_1$ component of its $U_0$ image forces $\beta=0$ if
it is a common eigenvector. The $-1$ eigenspace is $\mathbb Ct_1$,
already excluded. This proves uniqueness, including mixed vectors.

Suppose a unitary $C$ satisfies
$CV_j(\theta)C^\dagger=\lambda_jV_{\sigma(j)}(\varphi)$,
where $\sigma$ is identity or label interchange. Uniqueness makes
$C$ preserve $\mathbb C\xi$ and $T$. Evaluation on $\xi$ gives
$\lambda_0=\lambda_1=e^{i(\theta-\varphi)}=\lambda$.
The actual restrictions have determinants
$\det V_{0,T}=-1$, $\det V_{1,T}=1$. Thus $\lambda^2=1$
without interchange and $\lambda^2=-1$ with interchange. These
are exactly the required multiples of $\pi/2$, with the matching
interchange parity. Iterating (11.3) proves sufficiency. Complex
conjugation first replaces $\theta$ by $-\theta$ and gives the
last assertion. $\square$

## 12. Bounded angles, homogeneous accumulation and rotation closure

**Theorem 12.1 (Complete boundedness classification).** For the
actual family (11.1),

$$
\sup_{n\ge0}m_n(\theta)<\infty
\quad\Longleftrightarrow\quad \theta\in(\pi/2)\mathbb Z.
\tag{12.1}
$$

At every such angle the exact counts are

$$
m_0=1,\qquad m_1=2,\qquad m_2=4,\qquad m_n=6\quad(n\ge3).
\tag{12.2}
$$

A homogeneous six-valued online accumulator suffices for all horizons.
At every other angle $m_{n+1}>m_n$ for all $n\ge0$, in particular
$m_n\ge n+1$.

Proof. Work first with the actual full qutrit group
$G=\langle a,W\rangle=\langle a,b\rangle$ and put

$$
S=\{a,aW\},\quad F_n=S^n,\quad
H_\theta=\langle a^kWa^{-k}:k\in\mathbb Z\rangle.
\tag{12.3}
$$

By (11.2), $|F_n|=m_n$. Left multiplication by $a$ injects $F_n$
into $F_{n+1}$, so the counts are nondecreasing. Suppose there is a
plateau $m_{N+1}=m_N$, and set $F=F_N$. Each of
$aF,aWF,Fa,FaW$ has cardinality $|F|$ and lies in $F_{N+1}$.
All four sets are therefore equal. From $aF=aWF$ follows $WF=F$;
from $aF=Fa$ follows $a^kF=Fa^k$ for every integer $k$.
Consequently $(a^kWa^{-k})F=F$ for every $k$.
The left stabilizer of the finite nonempty set $F$ is finite:
for a fixed $f\in F$, the map $g\mapsto gf$ injects it into $F$.
It contains $H_\theta$, so $H_\theta$ is finite.

Conversely $H_\theta$ is normalized by $a$, contains $W$, and is
normal in $G$. Moving the $a$ factors to the left gives
$F_n\subseteq a^nH_\theta$. Thus finite $H_\theta$ bounds every
$m_n$ by $|H_\theta|$. A bounded nondecreasing integer sequence
has a plateau. At any plateau the stabilizer argument gives
$|H_\theta|\le|F|\le|H_\theta|$, and $WF=F$ gives
$F_{N+j}=a^jF$ by induction. A plateau therefore forces permanent
stabilization. An unbounded sequence has no plateau, proving the
strict-increment and $n+1$ assertions once (12.1) is established.
This argument concerns the exact positive sets $S^n$.

The actual permutation identities give

$$
aWa^{-1}=U_0WU_0,\qquad
W(U_0WU_0)W=U_0.
\tag{12.4}
$$

Hence $W,U_0\in H_\theta$. On $T$ their simultaneous commutant
consists of scalars: commuting with diagonal $W_T$ forces a matrix
to be diagonal, and commuting with $U_{0,T}$ then equates its
diagonal entries. If $H_\theta$ is finite, conjugation defines
$G\to\operatorname{Aut}(H_\theta)$ with finite image. Its kernel
commutes with $W,U_0$, so acts by scalars on $T$. It follows that
the projective restriction of $G$ to $PU(2)$ is finite.

In fact finiteness of this projective restriction alone forces the
listed angles. In the restricted group it contains

$$
t=(U_0a)_T=e^{i\theta W_T},\qquad r=(U_0W)_T=U_{1,T}.
\tag{12.5}
$$

Both have determinant one. In a finite projective group an $SU(2)$
element has a scalar power, which is $I_2$ or $-I_2$ by its
determinant; a further square is identity. In particular the
eigenvalues $e^{i\theta},e^{-i\theta}$ of $t$ are roots of unity.
Also $rt$ has finite order, so its trace is an algebraic integer.
The actual restrictions give

$$
\operatorname{tr}(rt)=\cos\theta\operatorname{tr}U_{1,T}
+i\sin\theta\operatorname{tr}(U_1W)_T=-\cos\theta,
\tag{12.6}
$$

since $\operatorname{tr}U_{1,T}=-1$ and $U_1W=U_0$ has trace
zero on $T$. Therefore $\cos\theta$ is an algebraic integer.
Every embedding of $\mathbb Q(\cos\theta)$ extends to a cyclotomic
field containing $e^{i\theta}$, and sends $\cos\theta$ to
$(\eta+\eta^{-1})/2$ for a root of unity $\eta$. All its conjugates
are real and in $[-1,1]$. If $0<|\cos\theta|<1$, its nonzero
integer norm has absolute value strictly below one: every conjugate
factor has absolute value at most one and the identity-embedding
factor is strictly smaller. This is impossible. Thus
$\cos\theta\in\{0,1,-1\}$, exactly $\theta\in(\pi/2)\mathbb Z$.
In particular the projective group is infinite at every other angle.

For sufficiency write $\theta=k\pi/2$, $k\in\mathbb Z$, and
$\epsilon=k\bmod2$. The full qutrit identity is

$$
V_j(k\pi/2)=i^kU_{j\mathbin\oplus\epsilon},\qquad
Q_h=i^{kn}p_h,\quad p_h\in S_3.
\tag{12.7}
$$

These are common fourth-root phases times actual permutation
matrices, including the signs when $k$ is even. The label-complement
map and the common phase preserve all same-horizon classes.
Theorem 5.1 therefore proves (12.2) at every $k\pi/2$.
Initialize $p=e\in S_3$ and, on the actual acquired label $j$,
update $p\leftarrow U_{j\mathbin\oplus\epsilon}p$. This uses the
same six values and twelve fixed transition entries at every prefix
and every horizon. At termination the full-$H$ unitary

$$
D_p=Bp^\dagger B^\dagger+(I_5-P_R)
\tag{12.8}
$$

satisfies $D_pBQ_h=i^{kn}B$. Its conjugation therefore recovers
every embedded qutrit with every untouched reference. Six values
are necessary uniformly, since Theorems 3.3–4.1 and $m_3=6$
exclude fewer. This proves all the assertions. $\square$

**Theorem 12.2 (Actual restricted projective closure).** Set
$\Gamma_\theta=\langle a_T,b_T\rangle\le U(2)$, and identify
$PU(2)$ with $SO(3)$ by the adjoint action on the Pauli matrices
in the order of Theorem 10.1. If $\theta\notin(\pi/2)\mathbb Z$,
the closure of its projective image is all of $SO(3)$ and
$\Gamma_\theta$ is not virtually solvable. If
$\theta/\pi=p/q$ is reduced with $q>2$, its projective image is
precisely $G(L,3)$ of Radin–Sadun, with $L=\operatorname{lcm}(q,2)$,
and thus isomorphic to $C_L*_{C_2}D_3$.

Proof. The actual generators are recoverable in both directions.
On the full qutrit,

$$
W=a^{-1}b,\quad U_0=W(aWa^{-1})W,\quad
U_1=U_0W,\quad e^{i\theta W}=U_0a,\qquad
a=U_1We^{i\theta W},\quad b=aW.
\tag{12.9}
$$

Thus the restricted projective group is generated by $w,r,t$,
the images of $W_T,U_{1,T},e^{i\theta W_T}$, respectively.
In the fixed orthonormal basis $(t_1,t_2)$ of Theorem 6.1,

$$
W_T=-\sigma_z,\quad
U_{0,T}=\frac{\sqrt3}{2}\sigma_x+\frac12\sigma_z,\quad
U_{1,T}=e^{2\pi i\sigma_y/3},\quad
 e^{i\theta W_T}=\operatorname{diag}(e^{-i\theta},e^{i\theta}).
\tag{12.10}
$$

Their adjoint rotations are $w=R_z(\pi)$,
$r=R_y(2\pi/3)$ and $t=R_z(2\theta)$. In particular $r$ has
order three and its axis is perpendicular to those of $w,t$.
Equation (12.9) proves equality of the generated groups, beyond a
one-directional expression of the measured letters.

Let $K$ be the projective closure. Theorem 12.1's finite-projective
argument makes $K$ infinite outside the listed angles. Here is the
closed-subgroup implication needed for these actual rotations.
An infinite closed subgroup of compact $SO(3)$ has nonidentity
elements tending to identity: take a convergent subsequence of
distinct elements and their successive quotients. Write such elements
as rotations through positive angles $\delta_j\to0$ about oriented
unit axes $v_j$, and pass to $v_j\to v$. For each real $u$ choose
integers $k_j$ with $k_j\delta_j\to u$. Their powers tend to the
rotation $R_v(u)$, so $K$ contains the whole circle about $v$.
If some $g\in K$ sends the line $\mathbb Rv$ to a different line,
it also contains the circle about $w'=gv$. For nonparallel $v,w'$
choose $\alpha$ with $v,w',R_v(\alpha)w'$ linearly independent;
for example an angle with nonzero sine has this property after
resolving $w'$ into its parallel and perpendicular parts. Conjugating
its circle gives the third circle about $R_v(\alpha)w'$.
The product map of these three circle parameters has invertible
derivative at zero, under $\mathfrak{so}(3)\cong\mathbb R^3$.
The inverse function theorem gives a neighborhood of identity in
$K$. A subgroup containing that neighborhood is open; connectedness
of $SO(3)$ forces $K=SO(3)$. Thus an infinite proper closed subgroup
must preserve an axis line.

For the present $r$, its only invariant real line is the $y$ axis,
since its rotation angle is neither zero nor $\pi$. The rotation
$t=R_z(2\theta)$ preserves this line exactly when
$\sin(2\theta)=0$. No such line exists at the angles now under
consideration, proving $K=SO(3)$.

If $\Gamma_\theta$ had a finite-index solvable subgroup $J$, its
projective image would be solvable and its closure $L$ solvable:
the iterated commutator identities expressing its derived length
are continuous and persist on taking closure. Finitely many cosets
of $J$ give finitely many cosets of $L$ covering $SO(3)$. A closed
subgroup of finite index is open (its complement is a finite union
of closed cosets), hence equals connected $SO(3)$. This contradicts
non-solvability of $SO(3)$: its Lie algebra has bracket the cross
product and equals its own derived algebra. Thus
$\Gamma_\theta\le GL_2(\mathbb C)$ is not virtually solvable.

For the rational-angle identification the axial rotations $w,t$
have fractions $1/2,p/q$ of a full turn. The subgroup of
$\mathbb Q/\mathbb Z$ they generate consists exactly of multiples
of $1/L$, $L=\operatorname{lcm}(q,2)$. Indeed after denominator
$L$ their integer numerators have gcd one: for odd $q$ they are
$q,2p$, and for even $q$ they are $q/2,p$. Bézout's identity
therefore supplies $d=R_z(2\pi/L)$ in $\langle w,t\rangle$,
and conversely $w,t$ are powers of $d$. Hence the actual image is
$\langle d,R_y(2\pi/3)\rangle$. Radin–Sadun, *Subgroups of
SO(3) Associated with Tilings*, [journal article][RS], Journal of
Algebra **202** (1998), 611–633, Theorem 1(ii) and Corollary 2,
p. 613, give the faithful presentation for even $L\ge4$ and odd
second order three. Their original ordered axes are $x,z$; one
spatial rotation takes those axes to the present $z,y$ axes.
The abstract generators map to precisely $d,r$, so their theorem
identifies this actual group with $G(L,3)\cong C_L*_{C_2}D_3$.
This is the same primary interface used at $L=6$ in Theorem 10.1.
It identifies a restricted rotation group; no positive-word count
or full-qutrit group isomorphism is imported from it. $\square$

## 13. Uniform positive growth at every unbounded angle

**Theorem 13.1 (An absolute exact-horizon growth bound).** There is
one constant $\beta>1$, independent of the real angle, such that
for every $\theta\notin(\pi/2)\mathbb Z$ and every $n\ge1$,

$$
\max\{n+1,\beta^n\}\le m_n(\theta)\le2^n.
\tag{13.1}
$$

One permissible existential choice is
$\beta=1+1/(2N(2))$, where $N(2)\ge1$ is the integer supplied
by Theorem 1.1 of Breuillard's *A Strong Tits Alternative*,
[arXiv:0804.1395v1][STA], PDF p. 1. No numerical value of this
integer or of $\beta$ is specified.

Proof. Let $\alpha=a_T$, $\gamma=b_T$ be the actual restrictions,
and $\Gamma=\Gamma_\theta$. The cited theorem states that for each
$d$ there is $N(d)$ such that for every field $K$ and finite
symmetric subset $F\subseteq GL_d(K)$ containing identity,
either $F^{N(d)}$ contains two elements freely generating a
nonabelian free group, or $\langle F\rangle$ is virtually solvable.
Apply exactly this statement with $d=2$, $K=\mathbb C$ and

$$
F_{\rm sym}=\{I_2,\alpha,\gamma,\alpha^{-1},\gamma^{-1}\}.
\tag{13.2}
$$

Finiteness, symmetry, invertibility and inclusion of identity are
explicit. Theorem 12.2 excludes the virtually solvable alternative
for the generated actual group. Thus there are free subgroup
generators $x,y$, each a word of length at most $N=N(2)$ in
(13.2). Their inverses have the same length bound. These inverse
and identity letters are auxiliary to the proof; they add no
permitted label, operation or idle step to Definition 11.1.

For a finite nonempty $D\subseteq\Gamma$, the left action of
$\langle x,y\rangle$ divides $\Gamma$ into free orbits. On each
orbit its graph for $x,x^{-1},y,y^{-1}$ is a four-regular tree.
A finite induced forest with $v$ vertices and $e$ edges has
$e\le v-1$ on each nonempty component. Its directed outward edge
count is $4v-2e\ge2v$. Summing over the finitely many intersected
orbits yields

$$
\sum_{s\in\{x,x^{-1},y,y^{-1}\}}|sD\setminus D|\ge2|D|.
\tag{13.3}
$$

For a bijective translate $sD$, its cardinality equals $|D|$, so
$|sD\triangle D|=2|sD\setminus D|$. Some $s$ in (13.3)
therefore satisfies $|sD\triangle D|\ge|D|$.
For any word $g_1\cdots g_k$, repeated use of the triangle
inequality for symmetric difference and invariance under left
translation gives

$$
|(g_1\cdots g_k)D\triangle D|
\le\sum_{j=1}^k|g_jD\triangle D|.
\tag{13.4}
$$

Also $|g^{-1}D\triangle D|=|gD\triangle D|$, by translating
the first symmetric difference by $g$. Expand the selected $s$
in at most $N$ letters of (13.2). Identity contributes zero.
Equations (13.3)–(13.4) imply that some forward letter
$g\in\{\alpha,\gamma\}$ has
$|gD\triangle D|\ge |D|/N$. With
$F_+=\{I_2,\alpha,\gamma\}$ this gives

$$
|F_+D|\ge|D\cup gD|
=|D|+\tfrac12|gD\triangle D|
\ge\left(1+\frac1{2N}\right)|D|=\beta|D|.
\tag{13.5}
$$

Starting at $D=\{I_2\}$ proves $|F_+^k|\ge\beta^k$ for
every $k$. To remove the auxiliary identity and obtain each exact
forward horizon, put $S_T=\{\alpha,\gamma\}$. Equation (11.2)
identifies $|S_T^j|=m_j$. Since identity commutes with everything,

$$
F_+^k=\bigcup_{j=0}^k S_T^j,\qquad
\beta^k\le|F_+^k|\le\sum_{j=0}^k m_j\le(k+1)m_k.
\tag{13.6}
$$

The last inequality uses monotonicity from Theorem 12.1, valid
also before deciding boundedness. Every length-$(u+v)$ product
factors into a length-$u$ and a length-$v$ product, hence

$$
m_{u+v}\le m_um_v.
\tag{13.7}
$$

Fix $n\ge1$ and apply (13.6) with $k=\ell n$, then (13.7):
$\beta^{\ell n}\le(\ell n+1)m_n^\ell$ for every $\ell\ge1$.
Taking $\ell$-th roots and letting $\ell\to\infty$ proves
$m_n\ge\beta^n$. Theorem 12.1 supplies the additional $n+1$
bound, and the number $2^n$ of actual histories supplies the upper
bound. The argument has transferred the dimension-uniform theorem
to positive products of exactly the measured horizon; neither
density alone nor growth of a symmetric group ball supplies that
transfer. $\square$

## 14. Maximal binary growth from actual integral coordinates

**Theorem 14.1 (A sufficient algebraic and transcendental criterion).**
Suppose $\cos\theta\ne0$ and set $z=i\tan\theta$.
If $z$ is transcendental, or if its primitive irreducible polynomial
$f\in\mathbb Z[X]$ has even $f(1)$, then

$$
m_n(\theta)=2^n\qquad(n\ge0).
\tag{14.1}
$$

The sign choice for $f$ does not affect the condition. For algebraic
$z$, even $f(1)$ is exactly the criterion for the particular residue
map $\mathbb Z[z]\to\mathbb F_2$, $z\mapsto1$ used below;
it is a sufficient condition for (14.1), with no asserted converse.

Proof. Use the actual basis $(b_1,b_2)$ of $T$ in Definition 8.1,
with its fixed coordinate change $C$. In that basis

$$
\widehat U_0=\begin{pmatrix}1&0\\-1&-1\end{pmatrix},\quad
\widehat U_1=\begin{pmatrix}0&1\\-1&-1\end{pmatrix},\quad
\widehat W=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\tag{14.2}
$$

Dividing both actual restricted letters by the same nonzero
$c=\cos\theta$ gives matrices over $\mathbb Z[z]$,

$$
P_0=\widehat U_0+z\widehat U_1
 =\begin{pmatrix}1&z\\-1-z&-1-z\end{pmatrix},\qquad
P_1=z\widehat U_0+\widehat U_1
 =\begin{pmatrix}z&1\\-1-z&-1-z\end{pmatrix}=P_0\widehat W.
\tag{14.3}
$$

Their determinants are $z^2-1$ and $1-z^2$.
For real $\theta$ the number $z$ is purely imaginary, so both
are nonzero. At a fixed length $n$, equality of the $P$ products
is exactly equality of the actual restrictions, since their common
factor is $c^n$ and their coordinate change is invertible.
Equation (11.2) then identifies it with qutrit projective equality.

Suppose a ring map $\phi:\mathbb Z[z]\to\mathbb F_2$ sends
$z$ to one. Entrywise reduction gives

$$
\phi(P_0)=\phi(P_1)=E=\begin{pmatrix}1&1\\0&0\end{pmatrix},
\quad E^2=E\ne0,\quad
\phi(\widehat W)E=\begin{pmatrix}0&0\\1&1\end{pmatrix}\ne E.
\tag{14.4}
$$

Every nonempty positive product thus has residue $E$. Assume two
distinct words of the same length have equal $P$ products. Cancel
their common factors from the left over $\mathbb C$, until the
first unequal factor. Interchange the two sides if necessary to
write $P_0X=P_1Y=P_0\widehat W Y$. The remaining tails have the
same length $k$. Invertibility over $\mathbb C$ gives
$X=\widehat W Y$. If $k=0$, this says $I_2=\widehat W$,
which is false. If $k\ge1$, reduction gives
$E=\phi(\widehat W)E$, contradicting (14.4). All cancellations
precede reduction; no singular matrix is inverted in $\mathbb F_2$.
Chronological reversal merely reorders which end is read first and
is a bijection of the binary histories. This proves injectivity
at every length once the residue map exists.

For transcendental $z$, evaluation identifies $\mathbb Z[z]$
with the polynomial ring $\mathbb Z[X]$, and evaluation at
$X=1$ modulo two is the required map. For algebraic $z$, the
kernel of evaluation $\mathbb Z[X]\to\mathbb Z[z]$ is $(f)$.
Here $f$ need not be monic: over $\mathbb Q[X]$ every vanishing
polynomial is divisible by its minimal polynomial and therefore
by $f$, and Gauss's lemma for primitive integral polynomials makes
the quotient integral. More explicitly, write a rational quotient
as $(a/b)q_0$ with $q_0$ primitive integral and $a,b$ coprime;
primitivity of $fq_0$ forces $b=1$ when the product is integral.
The homomorphism $X\mapsto1\pmod2$ therefore descends to the
quotient exactly when $f(1)$ is even. Conversely every map with
$z\mapsto1$ must annihilate $f(z)$ and so has that same condition.
This proves precisely the stated sufficient region. $\square$

**Theorem 14.2 (All nonbounded rational angles are maximal).** If
$\theta/\pi\in\mathbb Q\setminus\tfrac12\mathbb Z$, then
$m_n(\theta)=2^n$ for every $n\ge0$.

Proof. Write $\theta/\pi=p/q$ in lowest terms, $q>0$.
The hypothesis is exactly $q>2$; in particular $\cos\theta\ne0$.
Set $\zeta=e^{2i\theta}$, a primitive $q$-th root of unity, and
$d=\varphi(q)$. For the cyclotomic polynomial $\Phi_q$ put

$$
F_q(X)=(1-X)^d\Phi_q\!\left(\frac{1+X}{1-X}\right).
\tag{14.5}
$$

Expansion shows $F_q\in\mathbb Z[X]$.
The actual parameter satisfies
$z=i\tan\theta=(\zeta-1)/(\zeta+1)$, so $F_q(z)=0$.
Its leading coefficient is $(-1)^d\Phi_q(-1)\ne0$, since $q>2$,
and its degree is $d$. The inverse fractional transformation is
$\zeta=(1+z)/(1-z)$, with nonzero denominators in both directions.
Thus $\mathbb Q(z)=\mathbb Q(\zeta)$ has degree $d$.
The primitive part of $F_q$ consequently is the primitive
irreducible polynomial of $z$, up to sign. This justifies
irreducibility rather than inferring it from one root alone.
Evaluation of (14.5) by its polynomial expansion gives

$$
F_q(1)=2^d,\qquad F_q(0)=\Phi_q(1).
\tag{14.6}
$$

To determine the content, first suppose $q$ is not a power of two.
Write $q=2^a m$ with odd $m>1$. In $\mathbb F_2[X]$,
$X^q-1=(X^m-1)^{2^a}$, and the multiplicity of $X=1$ is exactly
$2^a$ because $(X^m-1)'(1)=1$. In the integral cyclotomic
factorization, the divisors $1,2,\ldots,2^a$ already contribute
all this multiplicity after reduction: $\Phi_1=X-1$ contributes
one, and $\Phi_{2^j}=X^{2^{j-1}}+1$ contributes $2^{j-1}$
for $1\le j\le a$. Their sum is $2^a$. No other cyclotomic
divisor of $X^q-1$, in particular $\Phi_q$, can vanish at one
modulo two. Hence $\Phi_q(1)$ is odd. The positive integral
content of $F_q$ divides both values in (14.6), and therefore
is one. Its primitive part has even value $2^d$ at one.

If $q=2^a\ge4$, then $d=2^{a-1}\ge2$ and
$\Phi_q(U)=U^d+1$. Thus

$$
F_q(X)=(1+X)^d+(1-X)^d.
\tag{14.7}
$$

All coefficients are even and the constant coefficient is exactly
two. Its content is exactly two; its primitive part has value
$2^{d-1}$ at one, again even. Theorem 14.1 proves the conclusion
in both cases, for all denominators, rather than for a finite
selection of cyclotomic polynomials.

For example $\theta=\pi/4$ has $z=i$ and primitive polynomial
$X^2+1$. The angle $\pi/6$ has $z=i/\sqrt3$ and primitive
polynomial $3X^2+1$; its all-length, including cross-length,
qutrit injectivity is already Theorem 8.2. The cases
$\cos\theta=0$, excluded from (14.3), are exactly odd multiples
of $\pi/2$ and have the bounded counts of Theorem 12.1. The other
excluded rational angles are integral multiples of $\pi$, also
covered there. $\square$

## 15. An irrational collision and the support exponent

**Theorem 15.1 (A positive collision on the full qutrit).** Let

$$
s_*=(\sqrt5-1)/2,\qquad
\theta_*=\arcsin(s_*)\in(0,\pi/2).
\tag{15.1}
$$

Then $\theta_*/\pi$ is irrational. The actual letters at this
angle obey the exact full-qutrit relation

$$
a^5b=ba^5,\qquad m_6(\theta_*)\le63.
\tag{15.2}
$$

Its parameter $z_*=i\tan\theta_*$ has primitive irreducible
polynomial $X^4-X^2-1$, whose value at one is odd.

Proof. The actual formula (6.2) gives
$\det a_T=-1$ and $\operatorname{tr}a_T=-i\sin\theta$.
Consequently $M=ia_T\in SU(2)$ has trace
$s_*=2\cos(2\pi/5)$ at (15.1). The last elementary identity
follows by putting $u=e^{2\pi i/5}$ in
$1+u+u^2+u^3+u^4=0$: the number $u+u^{-1}>0$ satisfies
$X^2+X-1=0$. The two eigenvalues of $M$ are therefore
$e^{2\pi i/5},e^{-2\pi i/5}$. Unitarity diagonalizes it, so
$M^5=I_2$ and $a_T^5=(-i)^5I_2=-iI_2$.
On $\mathbb C\xi$ the full $a^5$ acts by $e^{5i\theta_*}$.
Both summands reduce $b$, so these scalar blocks imply
$[a^5,b]=0$ on the entire qutrit. The two block scalars need
not be equal; the conclusion is commutation, without discarding
the relative phase. The distinct chronological histories
$(1,0,0,0,0,0)$ and $(0,0,0,0,0,1)$ have precisely the products
in (15.2). Each has probability $1/64$ and the equality is exact.
Among the 64 histories at least this pair coincides, proving
$m_6\le63$.

If $\theta_*/\pi$ were rational, take a cyclotomic field containing
both $e^{i\theta_*}$ and $i$. Every embedding sends
$(e^{i\theta_*}-e^{-i\theta_*})/(2i)$ to a real sine or its
negative, hence to $[-1,1]$. Every embedding of
$\mathbb Q(s_*)$ extends to that field. But the irreducible
polynomial $X^2+X-1$ of $s_*$ has conjugate
$-(\sqrt5+1)/2<-1$. This contradiction proves irrationality.

Finally $s_*^2=1-s_*$ gives $\cos^2\theta_*=s_*$ and
$\tan^2\theta_*=s_*$. Thus $z_*^2=-s_*$, which implies
$z_*^4-z_*^2-1=0$. This monic quartic has no rational linear
root, since neither $1$ nor $-1$ is a root. If it factored into
monic rational quadratics, they would have the form
$(X^2+aX+b)(X^2-aX+d)$, with
$a(d-b)=0$, $bd=-1$ and $b+d-a^2=-1$.
If $a=0$, the rational numbers $b,d$ would be the irrational
roots of $U^2+U-1=0$. Otherwise $b=d$, giving $b^2=-1$ in
$\mathbb Q$. Both are impossible. These exhaust proper factors
of a quartic without a linear factor, proving irreducibility.
Its value at one is $-1$. This exhibits one actual collision
outside Theorem 14.1's sufficient region; it does not make odd
$f(1)$ a converse collision criterion. $\square$

**Definition 15.2 (Support exponent and class probabilities).** At
fixed angle write

$$
A_n=\log_2m_n,\qquad
h_0(\theta)=\lim_{n\to\infty}\frac{A_n}{n},\qquad
k_{n,C}=|\{h:|h|=n,\ [Q_h]=C\}|,
\quad p_{n,C}=2^{-n}k_{n,C}.
\tag{15.3}
$$

The following theorem proves existence of the limit. The class
variable $\mathsf C_n=[Q_{\mathsf H_n}]$ has this probability law,
where $\mathsf H_n$ is the actually measured uniform history.
The support exponent uses $\log_2m_n$; its definition does not
replace the class probabilities by a uniform distribution.

**Theorem 15.3 (All-angle support-rate classification and its boundary).**
For every real angle,

$$
h_0(\theta)=\inf_{n\ge1}\frac{\log_2m_n(\theta)}n.
\tag{15.4}
$$

It is zero at every bounded angle, and at every other angle obeys

$$
\log_2\beta\le h_0(\theta)\le1.
\tag{15.5}
$$

Moreover $h_0=1$ if and only if there is no same-horizon collision
at any finite length, equivalently $m_n=2^n$ for every $n$.
In particular the regions in Theorems 14.1–14.2 have $h_0=1$,
whereas

$$
\log_2\beta\le h_0(\theta_*)\le\frac{\log_2 63}{6}<1.
\tag{15.6}
$$

The Shannon entropy of the actual class law satisfies

$$
H_{\rm Sh}(\mathsf C_n)
=n-2^{-n}\sum_C k_{n,C}\log_2k_{n,C}\le\log_2m_n.
\tag{15.7}
$$

In the collision-free case it is exactly $n$ and the $2^n$ classes
are uniform. A collision gives strict inequality
$H_{\rm Sh}(\mathsf C_n)<n$ at its horizon, but (15.4) is a
support-rate statement and does not identify a general Shannon
entropy rate with $h_0$.

Proof. Equation (13.7) makes $A_n$ subadditive and $0\le A_n\le n$.
For any fixed $N\ge1$ write $n=qN+r$ with $0\le r<N$.
Then $A_n\le qA_N+A_r\le qA_N+N$, giving
$\limsup A_n/n\le A_N/N$. Taking the infimum over $N$ and
using $A_n/n\ge\inf_N A_N/N$ proves existence and (15.4).
Bounded counts give zero; (13.1) gives (15.5).
If there is a collision at length $N$, then $m_N<2^N$,
so (15.4) gives $h_0\le(\log_2m_N)/N<1$. If there are none,
$A_n=n$ at every length and $h_0=1$. Theorem 15.1 and
irrationality give (15.6).

The fair-history law gives $p_{n,C}=k_{n,C}/2^n$ with
$\sum_C k_{n,C}=2^n$. Substitution into
$-\sum_Cp_{n,C}\log_2p_{n,C}$ gives (15.7)'s identity.
For its upper bound, concavity of logarithm yields
$\sum_Cp_{n,C}\log_2(1/p_{n,C})
\le\log_2\sum_Cp_{n,C}/p_{n,C}=\log_2m_n$.
When every $k_{n,C}=1$ the law is uniform and its entropy is $n$;
when some $k_{n,C}\ge2$ the subtracted sum is positive.
Support counts alone do not determine that sum at colliding angles.

There is also no general symmetric-walk premise hidden here.
For example at $\theta=0$ the actual binary law is
$(\delta_{U_0}+\delta_{U_1})/2$, whereas $U_1^{-1}=U_1^2$
is neither $U_0$ nor $U_1$. Its mass at $U_1$ is $1/2$ and
at $U_1^{-1}$ is zero. Thus this law is not symmetric under
inversion. No assertion about a different symmetric walk's
spectrum or entropy is needed for any step above. $\square$

## 16. Retained terminal memory for the classified family

**Theorem 16.1 (Exact terminal resources with all declared permissions).**
Fix any real $\theta$ and known horizon $n\ge0$ in Definition 11.1.
Under Assumption 1.4 and the complete-view convention of
Definition 1.5, the minimum finite terminal alphabet and minimum
fixed-length binary register are, respectively,

$$
\min|\mathcal Y_n|=m_n(\theta),\qquad
\min b_n=\lceil\log_2m_n(\theta)\rceil.
\tag{16.1}
$$

These minima allow arbitrary randomized classical summaries and
arbitrary terminal CPTP maps on all of $H$, with success required
only after averaging. They recover every input on the embedded
qutrit $R=B\mathbb C^3$, jointly with any untouched finite
reference. A successful standard Borel complete view determines
$\mathsf C_n$ measurably almost surely. An explicitly free
independent shared seed, finite or standard Borel, preserves the
same finite-alphabet and bit lower bounds for almost every seed.

Proof. Apply the existing Theorem 3.3 to precisely the actual
$Q_h(\theta)$, not to a replacement family with the same channel.
At every positive summary value, all positively weighted histories
must have one projective class. All $2^n$ histories have positive
probability, so different classes require disjoint nonempty sets
of summary values. Choosing one history per class proves the
$m_n$ lower bound, including randomized kernels. The theorem's
necessity already covers ensemble-only success and arbitrary
full-$H$ CPTP decoders; neither possibility permits merging two
classes. This uses its rank-one Choi argument with output $M_5$
and input $M_3$ and the scalar cross terms (3.2).
The primary correspondence is [KL, Theorem 3.2, (19)–(20)]
with full qutrit code and conditional errors
$F_h=\sqrt{w_{a,h}}Q_h$; the cross terms concern all pairs with
positive conditional weight. The one-step measured-flag supplier
[GW1, Proposition 2, §II.C.1] instead concerns the actual fine
operators $t_j=V_j/\sqrt2$, for which
$t_j^\dagger t_j=I_3/2$. The deferred-correction specialization
of [GW2, Proposition 2, (10)–(12)] sets all its earlier corrections
to identity. Its system here is the qutrit, not the entire $H$.
These known correction interfaces supply intermediate principles;
they supply no count of this family's coarsened terminal classes.

Conversely store the class and choose any actual representative
$Q_C$. The full-$H$ decoder is

$$
D_C=BQ_C^\dagger B^\dagger+(I_5-P_R),\qquad
\mathcal D_C=\operatorname{Ad}_{D_C}.
\tag{16.2}
$$

Its two orthogonal blocks make it unitary. For every history in
class $C$, $D_CBQ_h$ is a scalar multiple of $B$; thus for every
qutrit-reference density $\rho$,

$$
(\mathcal D_C\otimes\operatorname{id}_Z)
\big((BQ_h\otimes I_Z)\rho(BQ_h\otimes I_Z)^\dagger\big)
=(B\otimes I_Z)\rho(B\otimes I_Z)^\dagger.
\tag{16.3}
$$

Averaging preserves this equality. There is no success
postselection, and no full-$H$ input inversion is asserted.

Theorem 4.1's online construction applies unchanged at this angle.
Left multiplication by either $V_j$ respects projective prefix
classes, and $[Q]\mapsto[V_0^{n-t}Q]$ injects the length-$t$
classes into the length-$n$ classes. Label these prefix classes
by injections into one alphabet of size $m_n$ and use the known
prefix $t$ to select fixed transition tables. This retains at
most $m_n$ values at every prefix without another history archive.
A $b_n$-bit register has at most $2^{b_n}$ values, so its lower
bound follows; an injection of these $m_n$ values into
$\{0,1\}^{\lceil\log_2m_n\rceil}$ attains it.
At $n=0$ both minima mean one value and zero bits.

For a standard Borel view let $\nu_h$ be its conditional laws and
$\lambda=\sum_h\nu_h$. The densities $f_h=d\nu_h/d\lambda$
are measurable and sum to one almost everywhere. Convention 3.4,
which integrates the nonnegative Choi quadratic forms of
Theorem 3.3, states that the positive $f_h$ at a view all have the
same class outside one common null set. Group their densities by
class: $f_C=\sum_{h:[Q_h]=C}f_h$. Almost everywhere exactly one
$f_C$ is positive. Its measurable support sets define the required
class-valued function of the view. This argument uses measures,
so no assumption about positive probabilities of individual
continuous outcomes enters.

Let $S$ now be an explicitly independent free shared seed in a
finite or standard Borel space. Regular conditional laws exist in
the latter case. Average exact recovery has rank-one Choi matrix
$J(\iota)$; positivity first forces the conditional recovery
channel to equal $\iota$ for almost every $S$. Its trace is three,
fixing the scalar on that line, just as in Theorem 3.3.
Independence leaves every one of the finitely many histories at
conditional probability $2^{-n}$ on a common full-measure seed
set. At each such seed the preceding disjoint-class argument
requires at least $m_n$ values in any finite conditional register,
hence at least $\lceil\log_2m_n\rceil$ fixed bits. The deterministic
construction attains these bounds while ignoring the seed.
Discarded private randomness is already integrated into the
summary kernel; a history-correlated visible seed is part of the
counted joint view, and is not covered by the free-seed exemption.
$\square$

**Theorem 16.2 (All-angle retained-memory consequences).** Under
Theorem 16.1's permissions, a uniformly finite exact terminal
alphabet exists if and only if $\theta\in(\pi/2)\mathbb Z$.
At those angles the exact optimal counts and bits are

$$
\begin{array}{c|cccc}
 n&0&1&2&n\ge3\\\hline
 \min|\mathcal Y_n|&1&2&4&6\\
 \min b_n&0&1&2&3
\end{array}
\tag{16.4}
$$

The single homogeneous accumulator of Theorem 12.1 realizes the
uniform six-value bound. At every other angle, for all $n\ge1$,

$$
\left\lceil\log_2\max\{n+1,\beta^n\}\right\rceil
\le\min b_n\le n,\qquad
\lim_{n\to\infty}\frac{\min b_n}{n}=h_0(\theta).
\tag{16.5}
$$

In the maximal regions of Theorems 14.1–14.2 the exact minimum is
$n$ bits and $2^n$ values. The explicit colliding angle satisfies
$\min|\mathcal Y_6|\le63$ and has asymptotic fixed-bit rate at
most $\log_2(63)/6<1$, while retaining the positive lower rate
$\log_2\beta$. The complete terminal view, and its conditional
version with an independent shared seed, determine the measured
history itself at collision-free angles. Its discrete Shannon
entropy is then at least $n$ (conditionally at least $n$ given
the seed), attained by retaining the uniform history.

Proof. Equations (16.1), (12.1)–(12.2), (13.1) and (14.1)
give the stated alphabets, fixed bits and their uniform or linear
growth. Rounding changes $\log_2m_n$ by less than one, so
(15.4) proves the limit in (16.5). At $\theta_*$,
submultiplicativity gives $m_{6k}\le63^k$ for every $k$;
(15.6) gives the full limiting rate. This is a bound on alphabets
and fixed bits, without any assertion that class probabilities
are uniform at that angle.

If there are no collisions, the finite class variable is bijective
with the history. The measurable determination in Theorem 16.1
therefore determines that history as well. For a discrete complete
view $Y$, the entropy chain rule gives
$H_{\rm Sh}(Y)\ge H_{\rm Sh}(\mathsf H_n)=n$, also when
$Y$ is countable with infinite entropy. Conditioning on a free
independent seed gives the same statement almost everywhere and
then $H_{\rm Sh}(Y\mid S)\ge n$. Storing the history by the
online shift register (9.6) attains equality and (16.2) corrects it.
A non-discrete complete view gives measurable determination of the
finite history, not a differential-entropy lower bound. At
colliding angles, (15.7) describes the actual class entropy;
no entropy optimum or Shannon rate is inferred from $m_n$ alone.

All angles still have exactly the same averaged full $M_5$ channel
by Theorem 2.2. The differing retained-record optima depend on the
actual measured instruments and the complete terminal view.
Every construction processes every supplied label in the fixed
known-horizon, fresh-environment task. Between acquisitions only
classical updates occur. Reference access, intermediate quantum
feedback, adaptive instruments, retained quantum environments,
quantum summaries and postselection are outside these hypotheses.
The $n$ acquisitions and preparations, their communication,
calibration, precision, exact inverse controls, static descriptions
and the deterministic clock are the separate resources of
Definition 1.5. The generic prefix construction can have $2nm_n$
transition entries and $m_n$ inverse controls, as in Definition 4.2;
the register minimum is not a bound on those other costs.
A history-dependent clock, control program, archive or table choice
is counted jointly in the view. The unitary extension (16.2) acts
on all of $H$, while its recovery target remains only $R$ and
untouched references. $\square$

**Definition 16.3 (Residual collision and rate problems).** The
residual algebraic collision problem is to classify same-horizon
positive equalities in (11.1) for algebraic $z=i\tan\theta$ with
odd primitive $f(1)$, outside the bounded angles and beyond
particular relations such as (15.2). Failure of the residue map
in Theorem 14.1 is not a proof of a collision. The exact sequences
and support exponents at exceptional irrational angles, including
$\theta_*$, and the general Shannon entropy rates of their actual
class laws remain undetermined here. The existential uniform bound
does not specify the best numerical $N(2)$ or the optimal uniform
$\beta$. These are finer questions about the already classified
unbounded regime; the boundedness criterion (12.1) has no remaining
angle exception.

[STA]: https://arxiv.org/pdf/0804.1395v1

## 追加锚（本行以下为增补区）

## 17. Full-input flagged simulation and the five-level primitive menu

**Definition 17.1 (Four distinct simulation tasks).** Retain exactly
$H,B,R,K_j,A_j(\theta)$ of Definitions 1.3 and 2.1 and Theorem 2.2,
for every real $\theta$. Write $\mathsf C=\mathbb C^2$ for a terminal
classical flag with distinguished basis $|0\rangle,|1\rangle$. The
full-input fine instrument is the channel

$$
\mathcal J_\theta:M_5\longrightarrow\mathcal B(\mathsf C\otimes H),
\qquad
\mathcal J_\theta(X)=\sum_{j=0}^1|j\rangle\langle j|
                         \otimes A_j(\theta)XA_j(\theta)^\dagger.
\tag{17.1}
$$

Its flag algebra is diagonal. Exact simulation requires equality on
all of $M_5$, retaining both this flag and the quantum output, also
jointly with every arbitrary untouched finite reference $Z$. Its
outcome-statistics task instead retains only the probabilities
$\operatorname{Tr}(E_j(\theta)\rho)$, where
$E_j(\theta)=A_j(\theta)^\dagger A_j(\theta)$. Its averaged-channel
task retains only $\Phi_\circ=\sum_j\operatorname{Ad}_{A_j(\theta)}$.
Its encoded-instrument task is (17.1) restricted through
$\iota(X)=BXB^\dagger$ from $M_3$, with the flag still retained.
The latter restriction includes all qutrit-reference inputs. It does
not replace the full-$M_5$ task. These simulation tasks do not alter
the repeated acquired-label recovery permissions of Assumption 1.4.

**Definition 17.2 (Same-register simulators).** A five-level protocol
uses just the original quantum register $H$, arbitrary unitaries on
$H$, and complete Lüders PVMs on $H$. A PVM is a finite family of
orthogonal projections $P_a$ with $\sum_aP_a=I_5$; outcome $a$ has
operation $X\mapsto P_aXP_a$. Zero projections can be omitted.
Classical memory, measurable input-independent classical randomness,
classical feedback selecting later operations, and terminal classical
coarsening to the two flags are permitted. The quantum output is the
remaining register. All outcomes are retained in the normalized
channel; there is no success conditioning. No extra quantum register,
reset, nonprojective Lüders operation, general nonunitary primitive,
or access to $Z$ is permitted. A primitive menu of arbitrary CPTP
postprocessors would be a different menu.

Let $\mathfrak S_{\rm fin}$ be these protocols with a finite uniform
depth bound. Let $\mathfrak S_{\rm as}$ permit unbounded depth with
almost-sure finite termination on every input. Random choices and
controls are measurable; standard Borel random kernels suffice. They
can be sampled from a probability space of independent classical
tapes before interaction with the input. Sampling at each possible
finite outcome history represents feedback-dependent random choices
without making the tape law depend on the input. Conditional on a
tape, the protocol is a deterministic finitely branching quantum
outcome tree. Finally set
$\mathfrak S_{\rm cl}=\overline{\mathfrak S_{\rm fin}}^{\diamond}$.
Only normalized channels and their diamond limits are meant here;
no meaning for an actually nonhalting infinite product is stipulated.

The norm convention throughout this supplement is unhalved:

$$
\|\Lambda\|_\diamond
=\sup_{k\ge1}\ \sup_{X\ne0}
  \frac{\|(\Lambda\otimes\operatorname{id}_{\mathbb C^k})(X)\|_1}
       {\|X\|_1},\qquad
\|X\|_1=\operatorname{Tr}\sqrt{X^\dagger X}.
\tag{17.2}
$$

**Proposition 17.3 (Actual full-input geometry at every angle).** Define
the reflection and three mutually orthogonal projections by

$$
\begin{gathered}
F=|e_0\rangle\langle e_1|+|e_1\rangle\langle e_0|
 +|e_3\rangle\langle e_4|+|e_4\rangle\langle e_3|
 +|e_2\rangle\langle e_2|,\qquad D_\theta=\cos\theta I_5+i\sin\theta F,\\
P=\operatorname{diag}(1,0,0,0,1),\qquad
Q=\operatorname{diag}(0,1,0,1,0),\qquad
S=|e_2\rangle\langle e_2|.
\end{gathered}
\tag{17.3}
$$

Then $F^\dagger=F$, $F^2=I_5$, $D_\theta$ is unitary, and

$$
\begin{gathered}
K_0F=K_1,\quad K_1F=K_0,\quad A_j(\theta)=K_jD_\theta,\qquad
\mathcal J_\theta=\mathcal J_0\circ\operatorname{Ad}_{D_\theta},\\
K_0^\dagger K_0=P+S/2,\qquad K_1^\dagger K_1=Q+S/2,\\
\operatorname{rank}A_j=3,\qquad
\operatorname{spec}(A_j^\dagger A_j)=(1,1,1/2,0,0),\qquad
\|A_j\|_F^2=5/2.
\end{gathered}
\tag{17.4}
$$

Proof. $F$ interchanges $e_0,e_1$ and $e_3,e_4$, and fixes $e_2$.
The dyadic operators displayed in Theorem 2.2 therefore give both
$K_jF$ identities. The product $D_\theta^\dagger D_\theta$ is
$(\cos^2\theta+\sin^2\theta)I_5$ because the cross terms cancel.
Multiplying $K_jD_\theta$ gives precisely that theorem's rotated
operators, including all complex phases. The effects at zero angle
are the displayed diagonal matrices. Unitary precomposition preserves
their eigenvalues and Frobenius norms. This proves all assertions;
in particular no exceptional angle is removed. $\square$

## 18. A uniform obstruction to the full flagged instrument

**Theorem 18.1 (Retained-mass bound for every finite protocol).** For
every real $\theta$ and every $\mathcal T\in\mathfrak S_{\rm fin}$,

$$
\|\mathcal J_\theta-\mathcal T\|_\diamond\ge\frac4{25}.
\tag{18.1}
$$

The same normalized full-input witness works for arbitrary independent
measurable coins, adaptive quantum-outcome feedback and terminal
coarsening in Definition 17.2.

Proof. Fix $\theta$, and vectorize output first:
$|L\rangle\!\rangle=\sum_{k=0}^4Le_k\otimes e_k$.
Use the normalized reference input
$|\Omega_5\rangle=5^{-1/2}\sum_ke_k\otimes e_k$ and put

$$
\begin{gathered}
a_j=|A_j\rangle\!\rangle/\sqrt{5/2},\qquad
\Pi_\theta=\sum_{j=0}^1|j\rangle\langle j|\otimes|a_j\rangle\langle a_j|,\\
\omega_\theta=(\mathcal J_\theta\otimes\operatorname{id}_H)
                    (|\Omega_5\rangle\langle\Omega_5|)
=\frac12\sum_j|j\rangle\langle j|\otimes|a_j\rangle\langle a_j|.
\end{gathered}
\tag{18.2}
$$

Thus $\operatorname{Tr}\omega_\theta=1$ and
$\operatorname{Tr}(\Pi_\theta\omega_\theta)=1$.
The Schmidt weights of either unit vector $a_j$ are
$(2/5,2/5,1/5)$, by (17.4).

A terminal Kraus matrix $L$ assigned flag $j$ contributes Choi mass
$t(L)$ and witness overlap $f_j(L)$ given by

$$
t(L)=\frac{\|L\|_F^2}{5},\qquad
f_j(L)=\frac{|\operatorname{Tr}(A_j^\dagger L)|^2}{5(5/2)}.
\tag{18.3}
$$

In particular $0\le f_j(L)\le t(L)$ by Cauchy–Schwarz.
For the needed weighted Schmidt truncation, let $G$ be the range
projection of a nonzero $L$ of rank at most $r$. Then $GL=L$ and

$$
|\operatorname{Tr}(A_j^\dagger L)|^2
=|\operatorname{Tr}((GA_j)^\dagger L)|^2
\le\operatorname{Tr}(GA_jA_j^\dagger)\|L\|_F^2.
\tag{18.4}
$$

To bound the trace, diagonalize $A_jA_j^\dagger$ with decreasing
eigenvalues $\lambda_k$. In this basis the diagonal entries $g_k$
of $G$ satisfy $0\le g_k\le1$ and $\sum_kg_k\le r$.
The weighted sum $\sum_k\lambda_kg_k$ is at most the sum of the
largest $r$ eigenvalues: transferring weight from a smaller
$\lambda_k$ to an unfilled larger one cannot decrease it, and
nonnegative eigenvalues permit filling up to $r$ entries. Substituting
$(1,1,1/2,0,0)$ in (18.4) gives

$$
f_j(L)\le\eta_r t(L),\qquad
\eta_1=\frac25,\quad \eta_2=\frac45,\quad
\eta_r=1\ (3\le r\le5).
\tag{18.5}
$$

This is the usual singular-value/Schmidt truncation argument, used
here with the actual nonuniform weights, rather than a maximally
entangled-state overlap formula.

Condition now on an independent classical tape. Remove identity PVMs
and zero outcomes. Before the first nontrivial PVM the single nonzero
path has only a unitary product $U$. Suppose that first PVM has an
outcome $P_a$ of rank $r_a$. All its terminal descendants have matrices
$L_t=M_tP_aU$, where $M_t$ includes all subsequent unitaries and
projections along the descendant path. Every such matrix has rank at
most $r_a$. Completeness of the entire adaptive subtree gives

$$
\sum_{t\succ a}L_t^\dagger L_t=U^\dagger P_aU,\qquad
\sum_{t\succ a}t(L_t)=\frac{r_a}{5}.
\tag{18.6}
$$

For finite trees this identity follows by backward induction: the
sum of terminal effects at a halted node is $I_5$; a unitary node
conjugates it to $I_5$; a complete PVM node sums $P_bI_5P_b$ to
$I_5$. Applying this to the subtree after outcome $a$ proves (18.6).
The choices after different outcomes can be entirely different.
There is no assumption that one common later channel is used.

The positive ranks of a nontrivial PVM sum to five and have at least
two parts. At least one part is one or two, since otherwise their sum
would be at least six. If $r_a=1$, (18.5)–(18.6) force deficit
$\sum_{t\succ a}(t(L_t)-f_{j_t}(L_t))\ge3/25$; if $r_a=2$,
they force deficit at least $2/25$. All other descendants have
nonnegative deficits even when assigned different terminal flags.
Consequently the whole tape has total witness overlap at most
$1-2/25=23/25$. Branch mass cannot be discarded to evade this step.

There is one further case: a tape with no nontrivial PVM ends with
a unitary $U$ and a definite flag $j$. A singular value decomposition
$A_j=V\operatorname{diag}(1,1,1/\sqrt2,0,0)W^\dagger$ gives

$$
|\operatorname{Tr}(A_j^\dagger U)|
\le 2+1/\sqrt2,
\qquad
f_j(U)\le\frac{(2+1/\sqrt2)^2}{5(5/2)}
=\frac{9+4\sqrt2}{25}<\frac{23}{25}.
\tag{18.7}
$$

Indeed the diagonal entries of the unitary $V^\dagger UW$ have
modulus at most one. This also includes protocols that use only
coins and unitaries; their final flag becomes definite after the
tape is fixed.

Integrate over the tapes. Terminal coarsening sums positive Choi
terms and coin integration is linear. Tonelli's theorem applies to
the nonnegative masses and deficits, also for nonatomic coin laws.
No individual tape is required to simulate the target. If
$\sigma=(\mathcal T\otimes\operatorname{id}_H)
(|\Omega_5\rangle\langle\Omega_5|)$, the conclusion is
$\operatorname{Tr}(\Pi_\theta\sigma)\le23/25$.
Both $\sigma$ and $\omega_\theta$ have trace one. Measuring
$\{\Pi_\theta,I-\Pi_\theta\}$ gives unhalved classical distance

$$
2\bigl(1-\operatorname{Tr}(\Pi_\theta\sigma)\bigr)\ge4/25.
\tag{18.8}
$$

For completeness, trace-norm contraction under this measurement on
a Hermitian $Y=Y_+-Y_-$ follows by bounding the absolute value of
each outcome trace by its value on $Y_++Y_-$ and summing. Therefore
$\|\omega_\theta-\sigma\|_1\ge4/25$. This input is an admissible
test in (17.2), which proves (18.1). The factor five is already in
the normalized Choi input, the two target branch traces are $1/2$,
and the factor two in (18.8) is retained. $\square$

**Theorem 18.2 (Almost-sure stopping and diamond closure).** The bound
(18.1) holds for every $\mathcal T\in\mathfrak S_{\rm as}$ and
every $\mathcal T\in\mathfrak S_{\rm cl}$. Moreover

$$
\mathfrak S_{\rm fin}\subseteq\mathfrak S_{\rm as}
\subseteq\mathfrak S_{\rm cl},\qquad
\overline{\mathfrak S_{\rm as}}^{\diamond}=\mathfrak S_{\rm cl}.
\tag{18.9}
$$

The infimum distance to a fixed target is the same over all three
classes. No uniform bound on the halting time or its expectation
is required.

Proof. On a fixed tape the increasing sum of terminal effects is
at most $I_5$: every finite stopped tree plus its unfinished paths
has total effect $I_5$. Its residual $R_\infty$ is positive.
Almost-sure termination on the maximally mixed input implies
$\int\operatorname{Tr}(R_\infty)/5=0$. Hence
$R_\infty=0$ for almost every tape. This conclusion follows from
nonnegativity and finite-dimensional faithfulness of the trace;
it is not an assumption of termination on every conditional
postmeasurement state. On this common full-measure set the terminal
effects sum to $I_5$, giving a normalized channel for each tape.
If a first nontrivial PVM occurs, its branch residuals are positive
and sum to zero, since the outcome effects $U^\dagger P_aU$ sum
to $I_5$. Each branch residual must be zero. Thus (18.6) holds
with its countable sum for each first outcome. If no such PVM
occurs, normalization forces that deterministic tape to halt, with
a unitary terminal matrix. The entire proof of Theorem 18.1 now
applies on almost every tape, with Tonelli for the terminal sums.
This gives the bound directly for $\mathfrak S_{\rm as}$.

Here is also a diamond-norm finite approximation. At depth $n$ let
$R_n$ be the averaged effect of all unfinished paths. Then
$0\le R_n\le I_5$, and almost-sure termination gives
$\operatorname{Tr}R_n\to0$. Stop those paths immediately, keep
their current quantum register and assign a fixed terminal flag.
Together with the already halted paths this is a legal finite-depth
channel $\mathcal T_n$. The original continuation on the unfinished
paths and this replacement are two CP maps with the same total
effect $R_n$. For a finite-dimensional CP map $\Psi$,
$\|\Psi\|_\diamond=\|\Psi^\dagger(I)\|_\infty$:
stack its Kraus operators into $V$, use
$\Psi(X)=\operatorname{Tr}_{E}(VXV^\dagger)$ and
$V^\dagger V=\Psi^\dagger(I)$ to obtain the upper bound, also
with every identity reference. Partial trace is trace-norm
contractive, by duality with $Y\mapsto Y\otimes I_E$.
A pure eigenstate for the largest eigenvalue of $V^\dagger V$
gives the reverse bound. This argument applies to the CP maps
specified by integrated histories too, since their input and output
spaces are finite-dimensional. The triangle inequality therefore gives

$$
\|\mathcal T-\mathcal T_n\|_\diamond
\le2\|R_n\|_\infty\le2\operatorname{Tr}R_n\longrightarrow0.
\tag{18.10}
$$

This proves the second inclusion in (18.9); the first is immediate.
Taking closures proves its equality. Finally
$\mathcal T\mapsto\|\mathcal J_\theta-\mathcal T\|_\diamond$
is continuous, as is the Choi functional
$\mathcal T\mapsto\operatorname{Tr}(\Pi_\theta\sigma)$.
The inequality passes to the closure, and the infima over a set,
its intermediate almost-sure class and its closure coincide.
All approximants keep the original register and all probability
mass. The argument grants no nonhalting primitive. $\square$

## 19. Angle-independent distance and an explicit attained error

**Theorem 19.1 (A common infimum and a specific simulator).** Define

$$
d_*(\theta)=\inf_{\mathcal T\in\mathfrak S_{\rm fin}}
                 \|\mathcal J_\theta-\mathcal T\|_\diamond.
\tag{19.1}
$$

The same definition using either class in Theorem 18.2 gives the
same number. It is independent of $\theta$, denoted $d_*$, and

$$
\frac4{25}\le d_*\le1-\frac1{\sqrt2}.
\tag{19.2}
$$

For every angle there is an explicit legal finite-depth simulator
$\mathcal T_\theta$ whose distance is exactly the upper value.
This equality for the displayed simulator does not identify $d_*$.

Proof. Precomposition by $\operatorname{Ad}_{D_\theta}$ is a
bijection on each simulator class, with inverse precomposition by
$D_\theta^\dagger$. It is available as one initial legal unitary
and is an isometry for the diamond norm. Equation (17.4) therefore
makes the infimum independent of the angle. The lower bound is
Theorems 18.1–18.2.

To construct the upper simulator, put $P_0=P$, $P_1=Q$ and use
the following explicit unitary polar extensions. With
$u_-=q(e_0-e_3)$ and $v_-=q(e_1-e_4)$, specify their ordered
columns by

$$
T_0=[u\ \ u_-\ \ v\ \ v_-\ \ z],\qquad
T_1=[u_-\ \ u\ \ v\ \ z\ \ v_-].
\tag{19.3}
$$

Each is an orthonormal basis, so $T_j$ is unitary, and the actual
matrices satisfy

$$
K_j=T_j(P_j+qS),\qquad q=1/\sqrt2.
\tag{19.4}
$$

At angle zero toss a fair independent coin. One value selects
PVM $\{P+S,Q\}$; the other selects $\{P,Q+S\}$. In both
cases assign flag zero to the first outcome and flag one to the
second, and apply $T_j$ conditional on that flag. The resulting
fine operations are

$$
\mathcal T_{0,j}(X)=\frac12T_j
 \big((P_j+S)X(P_j+S)+P_jXP_j\big)T_j^\dagger.
\tag{19.5}
$$

All four outcomes of the two possible PVMs are retained. Its
flag-$j$ effect is $P_j+S/2$, already exactly the target effect.
Expansion of (19.4)–(19.5) gives, on every complex input,

$$
\Delta_j(X):=K_jXK_j^\dagger-\mathcal T_{0,j}(X)
=\epsilon T_j(P_jXS+SXP_j)T_j^\dagger,\qquad
\epsilon=\frac1{\sqrt2}-\frac12>0.
\tag{19.6}
$$

Consider a unit vector $\psi$ on $H\otimes Z$, and let
$x_P=(P\otimes I_Z)\psi$, $x_Q=(Q\otimes I_Z)\psi$,
$x_S=(S\otimes I_Z)\psi$, with squared norms $p,q',s$.
These are orthogonal and $p+q'+s=1$. Each flag block in
$(\mathcal J_0-\mathcal T_0)\otimes\operatorname{id}_Z$
applied to $|\psi\rangle\langle\psi|$ is, up to its unitary,
$\epsilon(|x_{P_j}\rangle\langle x_S|
+|x_S\rangle\langle x_{P_j}|)$. Its two nonzero eigenvalues
are $\pm\epsilon\|x_{P_j}\|\|x_S\|$, with zeros allowed
at a boundary. The direct sum over flags has trace norm

$$
2\epsilon\sqrt s(\sqrt p+\sqrt{q'})
\le2\epsilon\sqrt{2s(1-s)}
\le\sqrt2\epsilon=1-\frac1{\sqrt2}.
\tag{19.7}
$$

Convexity gives the same bound for mixed states and arbitrary
reference dimension. To see that this is a diamond bound on
all operators, write $\Delta=\mathcal J_0-\mathcal T_0$.
For any reference operator input $X$, form the Hermitian block
$Y=\tfrac12\left(\begin{smallmatrix}0&X\\X^\dagger&0\end{smallmatrix}\right)$
using one more untouched reference factor. Then
$\|Y\|_1=\|X\|_1$ and
$\|(\Delta\otimes\operatorname{id})(Y)\|_1
=\|(\Delta\otimes\operatorname{id})(X)\|_1$ by Hermiticity
preservation and the singular values of an off-diagonal block.
The positive and negative parts of $Y$ have total trace
$\|Y\|_1$. Applying the state bound separately and the triangle
inequality proves the desired bound times $\|X\|_1$.
Thus no restriction to unentangled or positive test operators
has been imposed on (17.2).

Equality is attained already without a reference by

$$
\psi_*=(e_0+e_1)/2+e_2/\sqrt2.
\tag{19.8}
$$

Here $p=q'=1/4$ and $s=1/2$, so both inequalities in (19.7)
are equalities. Therefore
$\|\mathcal J_0-\mathcal T_0\|_\diamond=1-1/\sqrt2$.
For general angle set
$\mathcal T_\theta=\mathcal T_0\circ\operatorname{Ad}_{D_\theta}$.
It uses the same coin and PVMs after one initial unitary, has the
same exact error, and is saturated by $D_\theta^\dagger\psi_*$.
Equivalently its PVM projections are conjugated by
$D_\theta^\dagger$, and its conditional unitaries are
$T_jD_\theta$. This completes the construction and (19.2).
No matching optimality proof for this simulator is implied.
$\square$

## 20. Exact realizations of the three smaller tasks

**Theorem 20.1 (Statistics, averaged channel and encoded instrument).**
For every real $\theta$ all three smaller tasks of Definition 17.1
have exact finite-depth realizations in the five-level menu.
Their attainments coexist with the positive full-instrument distance
in (19.2).

Proof. For statistics, the simulator of Theorem 19.1 has effects

$$
E_j(\theta)=D_\theta^\dagger(P_j+S/2)D_\theta.
\tag{20.1}
$$

Consequently tracing out its quantum output reproduces both outcome
probabilities for every input. Equality of these quantum-to-classical
maps also holds with any untouched reference. Their quantum updates
are different: at zero angle (19.6) has coefficient
$\epsilon>0$ on the $P_j$–$S$ cross operators. Thus equality of
probabilities does not imply equality of the fine instrument.

For the averaged channel, use its angle independence from Theorem 2.2
and mix the unrotated Kraus operators in a different basis:

$$
G_+=(K_0+K_1)/\sqrt2,\qquad G_-=(K_0-K_1)/\sqrt2,
\qquad H_\pm=(I_5\pm F)/2.
\tag{20.2}
$$

The actual dyadic matrices give
$K_0^\dagger K_1+K_1^\dagger K_0=F$ and hence
$G_\pm^\dagger G_\pm=H_\pm$.
Here $H_+$ and $H_-$ are complementary projections of ranks
three and two. On the range of $H_\pm$ the map $G_\pm$ is an
isometry, and it vanishes on its orthogonal complement. Choose
orthonormal bases in the domain and image complements and map
one to the other. This extends it to a unitary $U_\pm$ on $H$
with $G_\pm=U_\pm H_\pm$. Measure the complete PVM
$\{H_+,H_-\}$, apply $U_\pm$ conditional on the outcome and
forget that outcome. Its channel is exactly

$$
\sum_{\pm}U_\pm H_\pm XH_\pm U_\pm^\dagger
=\sum_{\pm}G_\pm XG_\pm^\dagger
=K_0XK_0^\dagger+K_1XK_1^\dagger=\Phi_\circ(X).
\tag{20.3}
$$

These are complex-linear identities, so also hold with references.
The new PVM outcome is not the original fine flag. As a separate
restriction, the actual channel is not a convex mixture of full-$H$
unitary conjugations: such a mixture is unital, whereas

$$
\Phi_\circ(I_5)=2|u\rangle\langle u|+|v\rangle\langle v|
                         +2|z\rangle\langle z|\ne I_5.
\tag{20.4}
$$

Nonunitality excludes that narrower menu only, and is consistent
with the exact PVM-with-feedback realization (20.3).

For the encoded instrument, reuse the already established supplier
identity $A_jB=BV_j/\sqrt2$ from Theorem 2.2. Toss a fair coin,
report its value $j$, and apply the five-level unitary

$$
\widetilde V_j=BV_jB^\dagger+(I_5-P_R).
\tag{20.5}
$$

Its orthogonal blocks are unitary and identity respectively, and
$\widetilde V_jB=BV_j$. Therefore its flagged branch on every
qutrit-reference density $\rho$ is exactly
$\tfrac12(BV_j\otimes I_Z)\rho(BV_j\otimes I_Z)^\dagger$,
the required branch of $\mathcal J_\theta\circ\iota$.
Repeated uses remain in $R$; independent coins give the already
supplied fair iid histories and chronological products
$V_{h_n}\cdots V_{h_1}$ of Definition 3.1. These identities are
applications of the source's existing encoded coin-unitary model,
not a new correction principle. Their inputs stay in $R$.
On arbitrary $H$ inputs the coin has constant probability $1/2$,
whereas the actual effects in (20.1) have eigenvalues $1,1,1/2,0,0$.
Thus this encoded realization cannot supply the full-input task.
$\square$

## 21. Minimal extra capacity in two separately enlarged menus

**Definition 21.1 (Two enlargement classes).** In the tensor class
adjoin a pure ready ancilla $E_m\cong\mathbb C^m$, admit arbitrary
joint unitaries and complete PVMs on $H\otimes E_m$, the same
classical operations as before, and discard the ancilla at the end.
The reported quantum output is $H$. In the direct-sum class use
one register $\widehat H_N\cong\mathbb C^N$, an isometric input
embedding $J:H\hookrightarrow\widehat H_N$, arbitrary unitaries
and complete PVMs on that enlarged register, and the same classical
operations. Exactness means a flag-$j$ output
$JA_jXA_j^\dagger J^\dagger$ for every $X\in M_5$, with support
in the embedded original register. Arbitrary untouched references
are retained in both classes. There is no reset or postselection.
The enlarged-space controls are hypotheses of these two classes;
controllability on $H$ does not imply them.

**Theorem 21.2 (Tensor minimum two and direct-sum minimum six).** For
every angle, the full-input flagged instrument has minimum pure
ancilla dimension $m=2$ in the tensor class, of total dimension ten.
It has minimum total register dimension $N=6$ in the direct-sum
class. The six-dimensional construction returns all quantum output
to the embedded $R$ and leaves the extra level empty.

Proof. For the tensor upper construction reuse exactly the isometry
and unitary completion of Definition 2.1 and Theorem 2.2. Prepare
$f_0$ in $E_2$, apply the unitary $\mathsf U$ there, measure
$\{I_5\otimes|g_j\rangle\langle g_j|:j=0,1\}$, supply its
classical outcome, and discard $E_2$. The contraction
$(I_5\otimes\langle g_j|)\mathsf U(x\otimes f_0)=A_jx$
holds for every $x\in H$. It gives (17.1) on all complex operators
and with references, with system output in $R$.
Equivalently the ready-subspace map is
$x\mapsto\sum_j A_jx\otimes f_j$ with readout in the $f$ basis;
its isometry follows from $\sum_j A_j^\dagger A_j=I_5$.
Extending orthonormal bases of two five-dimensional complements
supplies a joint unitary, as in the cited theorem. This upper
construction is an existing dilation supplier. The new minimum
conclusion uses Theorem 18.1: $m=1$ leaves exactly the original
five-level menu and cannot simulate the target, even in its
almost-sure or diamond closure. Thus $m=2$ is minimal.

For the direct-sum upper construction use the orthonormal basis
$h_0,\ldots,h_5$ of $\widehat H_6$, with $Je_k=h_k$ for
$0\le k\le4$. Let $C_0,C_1:R\to\widehat H_6$ be the
isometries given by

$$
\begin{array}{c|ccc}
 &u&v&z\\\hline
 C_0&h_0&h_1&h_2\\
 C_1&h_3&h_4&h_5
\end{array},\qquad
\Gamma_j=C_jC_j^\dagger.
\tag{21.1}
$$

Their ranges are orthogonal and exhaust $\widehat H_6$.
Thus $W_\theta x=C_0A_0x+C_1A_1x$ is an isometry on the
entire five-dimensional input: orthogonality removes the cross
terms and $W_\theta^\dagger W_\theta=\sum_jA_j^\dagger A_j=I_5$.
Here $C_j$ is applied only to the known range $R$ of $A_j$.
An explicit unitary completion is

$$
\begin{gathered}
Z_0=[h_0\ \ h_3\ \ (h_1+h_4)/\sqrt2\ \ h_5\ \ h_2
                          \ \ (h_1-h_4)/\sqrt2],\\
Z_\theta=Z_0(D_\theta\oplus1),\qquad Z_\theta J=W_\theta.
\end{gathered}
\tag{21.2}
$$

Indeed the first five columns of $Z_0$ are
$C_0K_0e_k+C_1K_1e_k$ in order. The displayed sixth column is
orthogonal to them and has unit length. Hence $Z_0$ is unitary;
(17.4) proves the general-angle identity without any new dimension.

It remains to return the postmeasurement output to the original
register; just reading $\Gamma_j$ would leave different output
supports. Put

$$
\begin{gathered}
O=[Ju\ \ Jv\ \ Jz\ \ Ju_-\ \ Jv_-\ \ h_5],\qquad
E^{(0)}=[h_0\ \ h_1\ \ h_2\ \ h_3\ \ h_4\ \ h_5],\\
E^{(1)}=[h_3\ \ h_4\ \ h_5\ \ h_0\ \ h_1\ \ h_2],\qquad
R_j=O(E^{(j)})^\dagger.
\end{gathered}
\tag{21.3}
$$

All three displayed column lists are orthonormal bases, so $R_j$
is unitary and $R_jC_jy=Jy$ for every $y\in R$.
Apply $Z_\theta$, measure the complete PVM
$\{\Gamma_0,\Gamma_1\}$, retain flag $j$ and apply $R_j$.
The complete fine branch identity is

$$
R_j\Gamma_jZ_\theta J=JA_j.
\tag{21.4}
$$

Conjugating any input operator and tensoring with $I_Z$ proves
exact flagged equality, including all reference correlations.
Its output support is $JR\subset JH$; in particular its
$h_5$ component is zero after feedback. No probability is rejected.

For minimality, $N<5$ cannot isometrically embed the specified
arbitrary five-dimensional input. At $N=5$ such an embedding is
unitary onto the whole register; conjugating every protocol by
that unitary gives a protocol in the original menu. Theorem 18.1
excludes exact simulation there, including the extensions of
Theorem 18.2. Hence $N\ge6$, attained by (21.1)–(21.4).
A direct-sum extra level and a tensor qubit are different additions:
$5+1=6$, whereas $5\cdot2=10$. Neither construction transfers
the ownership or environment-access permissions of the separate
full-system model [DIL, Definition 1.1, Theorem 2.2 and Assumption 2.3].
That supplier's $\mathbb C^5\otimes\mathbb C^2$ system is not
the present five-dimensional input system. Here both constructions
are conditional single-use mathematical realizations under Definition
21.1; they provide no automatic fresh preparation or reset at a
later use. $\square$

## 22. Primary interfaces and the unresolved resource distance

**Convention 22.1 (Attribution and precise theorem scope).** The
rank-weight and Schmidt-number obstruction is an existing mechanism,
not a general principle first asserted by (18.1). Its primary
supplier is S. Khandelwal and A. Tavakoli, *Simulating quantum
instruments with projective measurements and quantum post-processing*,
[arXiv:2503.00956v2][KT17], Theorems 1–2 on PDF p. 2, equation (1) and Appendix A.
Their simulator permits classical mixtures of PVMs followed by
outcome-dependent CPTP channels; classical postprocessing is included
in their framework. With normalized Choi convention, Theorem 1 gives
positive operators $\sigma_{a|\boldsymbol r}$ satisfying

$$
\operatorname{Tr}\sigma_{a|\boldsymbol r}
 =q_{\boldsymbol r}r_a/d,\qquad
\sum_a\operatorname{Tr}_{\rm out}\sigma_{a|\boldsymbol r}
 =q_{\boldsymbol r}I_d/d,\qquad
\operatorname{SN}(\sigma_{a|\boldsymbol r})\le r_a.
\tag{22.1}
$$

Its necessity is the relevant rank-weight precedent. Its sufficiency
is Theorem 2 for qubit input, not for dimension five. General
quantum postprocessing there is broader than the permitted primitive
menu here; conversely a multi-step adaptive tree is not itself their
single-PVM specification. Equations (18.4)–(18.7) and the stopping
proof supply the needed actual-model bound with those distinctions
retained.

L. Leppäjärvi and M. Sedlák, *Post-processing of quantum instruments*,
[arXiv:2010.15816v1][LS17], §IV Definition 4, Proposition 5 (PDF p. 7) and
Proposition 8 (PDF p. 9), supply the instrument-postprocessing interface.
A nonzero operation is indecomposable exactly when its Kraus rank
is one. If $\mathcal I\to\mathcal J$ by conditional quantum
instrument postprocessing and $\mathcal J$ is indecomposable,
Proposition 8 gives reverse induced-POVM postprocessing
$A^{\mathcal J}\to A^{\mathcal I}$. Conditional quantum instruments
in that statement are not additional legal primitives here.
The target operations each have Kraus rank one but their unique
Kraus matrices have matrix rank three. Positivity of the rank-one
Choi rays and refinement into terminal Kraus terms are familiar
instances of that distinction, also used earlier in Theorem 3.3.
They must not be confused with a claim of matrix rank one.

B. M. Terhal and P. Horodecki, *A Schmidt number for density matrices*,
[quant-ph/9911117v4][TH17], Lemma 1 (PDF p. 2), bounds overlap of Schmidt-number
$k$ states on $\mathbb C^N\otimes\mathbb C^N$ with a maximally
entangled vector by $k/N$. The vectors in (18.2) instead have
weights $(2/5,2/5,1/5)$. The standard weighted singular-value
truncation in (18.4)–(18.5) gives the needed $2/5,4/5,1$ constants
directly; substituting $k/5$ would be incorrect. Orthonormal-basis
completion in Theorem 2.2 supplies the existing tensor dilation,
and the same elementary finite-dimensional completion is used
inside (20.3) and (21.2)–(21.3). These generic linear-algebra facts
are intermediate suppliers, not separate discoveries.

The following primary comparisons delimit other possible simulation
claims. G. Wang and M. Ying, *Realization of positive-operator-valued
measures by projective measurements without introducing ancillary
dimensions*, [quant-ph/0608235v3][WY17], Theorem 1 and Corollary 1 (PDF p. 4),
concern reproducing POVM statistics by sequential projective
measurements. Their commuting-projection criterion requires a
nontrivial projection: its printed exclusion $P\ne I$ must also
exclude $P=0$, since the necessity proof uses a genuine first split.
Their one-extra-dimension corollary is a statistics result and does
not specify the quantum updates in (21.4).
M. Oszmaniec, L. Guerini, P. Wittek and A. Acín,
*Simulating positive-operator-valued measures with projective
measurements*, [arXiv:1609.06139v2][OGWA17], Theorem 1 (PDF p. 3), gives
universal statistics simulation using a pure tensor ancilla of
input dimension $d$, with $d$ a worst-case minimum. It does not
supply the minimum for this particular binary instrument.
S. Sau and M. Sedlák, *Sequential realization of Quantum Instruments*,
[arXiv:2512.14588v1][SS17], Theorem 1 (PDF p. 6), decomposes a total instrument
$\mathcal T$ when $A^{\mathcal T}\to B$, with initial Lüders
operation $X\mapsto\sqrt{B_j}X\sqrt{B_j}$ and residual conditional
instruments. The initial operation is generally nonprojective;
the preceding ancilla-reuse discussion explicitly assumes reset.
Neither operation is added to Definition 17.2 by that theorem.

Within this manuscript the encoded coin-unitary identities and
chronological law are supplied by Theorem 2.2 and Definition 3.1;
the pure two-level dilation and completion are supplied by
Definition 2.1 and Theorem 2.2. The source-specific additional content
is the full-input retained-mass separation with its stopping and
closure quantifiers, the exact error of the displayed simulator,
the distinction of the smaller tasks, and the resource minima under
the two stated enlargement classes. The related use of instrument
postprocessing in [*FIB native complete continuation finite activity
frontier*, Proposition 85.1 and its primary-interface table][FA17], concerns equality
of fine composites and access restrictions, not this first-PVM
bound. These correspondences delimit a bounded comparison; they
assert no exhaustive semantic nonoverlap or literature priority.

**Definition 22.2 (Remaining mathematical and realization boundaries).**
The exact optimal common distance $d_*$ in (19.2) is unresolved.
Neither equality at $4/25$ nor equality at $1-1/\sqrt2$ is
established. An exact characterization of all simulator channels
or their closure is also unresolved; (18.9) is an inclusion and
closure result, not such a characterization. The obstruction
requires the full input algebra, terminal flag and quantum output.
Tracing out a component or restricting the input changes the task,
as the exact attainments in §20 demonstrate.

All conclusions are ordinary finite-dimensional mathematical
statements within the declared ideal operational menus. Acquisition
of controls or environment access, finite precision, calibration,
total implementation cost and physical realization are separate
questions. The enlarged-space constructions assume the respective
joint or six-level controls and specified input preparations; no
such permission follows from arbitrary five-level unitaries alone.
The repeated recovery resources and retained-record bounds of the
earlier sections remain separate from single-use simulation capacity.

[FA17]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_FINITE_ACTIVITY_FRONTIER.md
[KT17]: https://arxiv.org/pdf/2503.00956v2
[LS17]: https://arxiv.org/pdf/2010.15816v1
[TH17]: https://arxiv.org/pdf/quant-ph/9911117v4
[WY17]: https://arxiv.org/pdf/quant-ph/0608235v3
[OGWA17]: https://arxiv.org/pdf/1609.06139v2
[SS17]: https://arxiv.org/pdf/2512.14588v1

## 追加锚（本行以下为增补区）

## 23. Signed-angle six-state terminal recovery near the bounded angles

**Definition 23.1 (Signed calibration and the terminal decoder).** Use
exactly the actual measured instrument of Definitions 2.1 and 11.1 at a
fixed real angle $\theta$, with the repeated acquisitions and complete
classical view of Assumption 1.4 and Definition 1.5. For this approximate
recovery task replace exact success by an unhalved diamond error bound,
using (17.2). In particular, the supremum includes arbitrary complex
operators and every untouched finite reference, not just system density
operators. Choose a nearest integer $k$ to $2\theta/\pi$ and put

$$
\eta=\theta-k\pi/2,\qquad
\delta=|\eta|=\operatorname{dist}(\theta,(\pi/2)\mathbb Z)\le\pi/4,
\qquad \epsilon_k=k\bmod2.
\tag{23.1}
$$

Either nearest integer is permitted at a tie. The decoder uses the signed
$\eta$; $\delta$ is only the nonnegative error parameter. On each actual
supplied label $h_{t+1}$, relabel it statically as
$\widetilde h_{t+1}=h_{t+1}\mathbin\oplus\epsilon_k$ and update

$$
P_0=I_3,\qquad P_{t+1}=U_{\widetilde h_{t+1}}P_t\in S_3.
\tag{23.2}
$$

Thus the complete persistent history state has at most six values, with
at most twelve fixed transition entries. These are the actual permutation
matrices of Theorem 2.2. There is no newly sampled generator or random
choice of label. The transition requires no persistent clock.

In the orthonormal basis $(t_1,t_2)$ of $T$ from Theorem 6.1 define

$$
\begin{gathered}
J=W_T=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\qquad
H_c=\begin{pmatrix}2/3&0\\0&-2/3\end{pmatrix},\\
C=J+H_c=\begin{pmatrix}-1/3&0\\0&1/3\end{pmatrix},\qquad
A=\begin{pmatrix}0&1/\sqrt3\\1/\sqrt3&0\end{pmatrix}.
\end{gathered}
\tag{23.3}
$$

Here $A$ is a two-dimensional Hermitian matrix, distinct from the measured
five-dimensional Kraus matrices $A_j(\theta)$. For $P\in S_3$, all these
permutations preserve $\mathbb C\xi\oplus T$; define on the qutrit

$$
Y^\eta_{t,P}=e^{it\eta}\big|_{\mathbb C\xi}
 \ \oplus\ e^{i\eta H_c}P_Te^{-i\eta H_c}.
\tag{23.4}
$$

At the externally declared horizon $n$, apply exactly one unitary on $H$:

$$
D^\eta_{n,P_n}=B(Y^\eta_{n,P_n})^\dagger B^\dagger+(I_5-P_R).
\tag{23.5}
$$

The two orthogonal blocks make this unitary on all of $H$. Its recovery
target is the encoded qutrit, jointly with every untouched reference.
The intermediate $Y^\eta_{t,P}$ are coordinates for analysis, not
intermediate quantum operations. Between acquisitions only (23.2) is
performed. No ancilla for recovery, retained quantum environment,
intermediate quantum control, adaptive measurement basis, reference
access or postselection is admitted. The fresh measured environments
are exactly those already specified in Assumption 1.4.

Let $\mathcal F_{n,\theta}:M_3\to M_5$ be the channel obtained by averaging
the actual histories and applying (23.5). Signed angle calibration, the
known horizon and the at most six terminal control descriptions are
supplied separately. Their precision, synthesis and cost, and the $n$
acquisitions, preparations and communications, are not counted by six.
Any further history-dependent control description, buffer or clock value
would belong to the complete state and is absent from this construction.

**Theorem 23.2 (Finite all-reference terminal bound).** For every real
$\theta$ and every integer $n\ge0$, Definition 23.1 gives

$$
\boxed{\quad
\|\mathcal F_{n,\theta}-\iota\|_\diamond
\le\min\{2,\,2n\delta^2/3\}.
\quad}
\tag{23.6}
$$

The bound concerns the averaged corrected channel. It asserts neither
this error for each history nor a tail bound for histories. At
$\delta=0$ the construction recovers exactly at every horizon. The
operator (23.5) acts on all $H$, but (23.6) does not assert recovery of
arbitrary full-$H$ inputs.

Proof. First work at the signed angle $\eta$, so that $k=0$ and
$\widetilde h=h$. Reuse Theorem 2.2 and Definition 3.1:

$$
A_j(\eta)B=2^{-1/2}BV_j(\eta),\qquad
V_j(\eta)=U_je^{i\eta W},\qquad
A_{h_t}(\eta)\cdots A_{h_1}(\eta)B
 =2^{-t/2}BQ_h(\eta).
\tag{23.7}
$$

Each normalized conditional branch is a qutrit unitary with effect
$I_3/2$ at the next acquisition. This remains true after tensoring with
any reference, and its output remains in $R$. Consequently every actual
history has probability $2^{-t}$ independently of the encoded input.
This uses the actual measured branches, not a different realization of
the same averaged channel. Fairness is only asserted on $R$.

The matrix cancellation is in the orthonormal $T$ coordinates of
Theorem 6.1. To make its signs explicit, those restrictions give

$$
\begin{aligned}
U_{0,T}^\dagger H_cU_{0,T}
 &=\begin{pmatrix}-1/3&1/\sqrt3\\1/\sqrt3&1/3\end{pmatrix}=C+A,\\
U_{1,T}^\dagger H_cU_{1,T}
 &=J(C+A)J=C-A.
\end{aligned}
\tag{23.8}
$$

For example, the first matrix follows by multiplying
$\left(\begin{smallmatrix}1/2&\sqrt3/2\\\sqrt3/2&-1/2\end{smallmatrix}\right)$
on both sides of $H_c$. The second uses $U_1=U_0W$, $JCJ=C$ and
$JAJ=-A$. The average in (23.8), minus $H_c$, is precisely $J$.
Thus, if $F(P)=P_T^\dagger H_cP_T$ and
$(\mathsf PF)(P)=\tfrac12\sum_jF(U_jP)$, then

$$
\begin{aligned}
(\mathsf PF-F)(P)&=P_T^\dagger JP_T,\\
F(U_jP)-(\mathsf PF)(P)&=(-1)^jP_T^\dagger AP_T.
\end{aligned}
\tag{23.9}
$$

This is an additive Poisson/coboundary correction: its innovation has
conditional mean zero. The classical additive-functional use of such
corrections is literature-attested, for example Glynn–Meyn,
*A Liapounov Bound for Solutions of the Poisson Equation*, §1,
(1), (3)–(4), pp. 916–917 [GM23]. On the finite state space here,
all entries are bounded. Equation (23.9) is checked directly and
imports no recurrence, central limit, independence or quantum-product
conclusion from that supplier. The noncommutative product estimate
needed here is the following calculation.

For $P'=U_jP$, introduce a local residual on the full qutrit:

$$
L_{j,P}=(Y^\eta_{t+1,P'})^\dagger V_j(\eta)Y^\eta_{t,P}.
\tag{23.10}
$$

Its $\xi$ block is exactly
$e^{-i(t+1)\eta}e^{i\eta}e^{it\eta}=1$. For its $T$ block, write
$U=U_{j,T}$ and use $[J,H_c]=0$ to obtain, in order,

$$
\begin{aligned}
L_{j,P,T}
 &=e^{i\eta H_c}P_T^\dagger U^\dagger e^{-i\eta H_c}
       Ue^{i\eta J}e^{i\eta H_c}P_Te^{-i\eta H_c}\\
 &=S_Pe^{-i\eta(C+(-1)^jA)}e^{i\eta C}S_P^\dagger,
 \qquad S_P=e^{i\eta H_c}P_T^\dagger.
\end{aligned}
\tag{23.11}
$$

In particular this residual is independent of $t$. Both branches use
the same conjugating unitary $1\oplus S_P$, and the $\xi$ block has
not been discarded as a relative phase.

Extend $C,A$ by zero on $\mathbb C\xi$, denoting the extensions by
$\widehat C,\widehat A$, and set, for a real auxiliary variable $a$,

$$
\begin{gathered}
G(a)=\operatorname{Ad}_{e^{-i\eta(\widehat C+a\widehat A)}}
       =e^{\mathcal L(a)},\qquad
\mathcal L(a)=-i\eta[\widehat C+a\widehat A,\,\cdot\,],\\
\mathcal K=\mathcal L'(a)=-i\eta[\widehat A,\,\cdot\,].
\end{gathered}
\tag{23.12}
$$

For any reference and any complex operator $X$, left and right
multiplication by $\widehat A\otimes I$ each have trace-norm bound
$\|\widehat A\|_{\rm op}=1/\sqrt3$. Hence
$\|\mathcal K\|_\diamond\le2|\eta|/\sqrt3$. Every factor
$e^{s\mathcal L(a)}$, for real $s$, is a unitary conjugation and
has diamond norm one. Differentiating the matrix exponential once gives
$G'(a)=\int_0^1e^{(1-s)\mathcal L(a)}\mathcal K
 e^{s\mathcal L(a)}\,ds$. Differentiating again inserts the second
$\mathcal K$ at either of its two ordered positions. Reparametrizing
the two integrals yields the exact Duhamel formula

$$
G''(a)=2\int_{0\le r\le s\le1}
 e^{(1-s)\mathcal L(a)}\mathcal K
 e^{(s-r)\mathcal L(a)}\mathcal K
 e^{r\mathcal L(a)}\,dr\,ds.
\tag{23.13}
$$

Submultiplicativity and the simplex area $1/2$ therefore give
$\|G''(a)\|_\diamond\le4\eta^2/3$ for every real $a$. The
finite-dimensional integrals are ordinary integrals of linear maps,
so their norm estimates hold uniformly in reference dimension.
The exact symmetric Taylor identity is

$$
\frac{G(1)+G(-1)}2-G(0)
 =\frac12\int_0^1(1-s)\bigl(G''(s)+G''(-s)\bigr)\,ds.
\tag{23.14}
$$

It follows by applying the integral remainder separately at $1$ and
$-1$; the first derivatives cancel. Since $\int_0^1(1-s)\,ds=1/2$,
its diamond norm is at most $2\eta^2/3$.
By (23.11), the channel

$$
\Phi_P=\tfrac12\sum_{j=0}^1\operatorname{Ad}_{L_{j,P}}
\tag{23.15}
$$

is the common unitary conjugate of
$\tfrac12(G(1)+G(-1))\circ G(0)^{-1}$, where the conjugation
acts on both the input and output of the channel. Such compositions
preserve the diamond norm and send $G(0)\circ G(0)^{-1}$ to identity.
Consequently

$$
\|\Phi_P-\operatorname{id}_3\|_\diamond\le2\eta^2/3.
\tag{23.16}
$$

This is a finite inequality for every real signed $\eta$, with no
omitted small-angle remainder and no factor of one half in the norm.
Quadratic improvement by mixing unitaries is also a known general
mechanism: Campbell, *Shorter gate sequences for quantum computing by
mixing unitaries*, arXiv:1612.02689v3, §III Lemma 1, (14) [CA23],
assumes $a,b>0$, $p_j>0$, $\sum_jp_j=1$,
$\|U_j-V\|_{\rm op}\le a$ and
$\|\sum_jp_jU_j-V\|_{\rm op}\le b$, and gives
$\|\sum_jp_j\operatorname{Ad}_{U_j}-\operatorname{Ad}_V\|_\diamond
\le a^2+2b$. Its equation (2) calls half the norm a diamond distance;
(14) is the unhalved norm bound. This is a generic intermediate
precedent. Equations (23.11)–(23.16) give the needed actual matrices
and the coefficient $2/3$ directly, rather than importing a protocol
or a resource assertion from gate synthesis.

It remains to accumulate (23.16) on the same actual histories. For a
length-$t$ history define

$$
\begin{gathered}
Z_h=(Y^\eta_{t,P_h})^\dagger Q_h(\eta),\qquad
M_t(P)=2^{-t}\sum_{h:P_h=P}\operatorname{Ad}_{Z_h},\\
p_t(P)=2^{-t}|\{h:P_h=P\}|,\qquad
\mathcal C_t=\sum_PM_t(P).
\end{gathered}
\tag{23.17}
$$

Each $Z_h$ is unitary. If $p_t(P)>0$, $M_t(P)/p_t(P)$ is a
convex combination of unitary channels, so it has diamond norm one:
the upper bound follows from trace-norm invariance of each summand,
and a density input gives the lower bound by trace preservation.
If $p_t(P)=0$, $M_t(P)=0$. Thus

$$
\|M_t(P)\|_\diamond=p_t(P),\qquad \sum_Pp_t(P)=1.
\tag{23.18}
$$

Appending the actual label $j$ gives the pointwise identity
$Z_{hj}=L_{j,P_h}Z_h$. Conditional fairness from (23.7) and grouping
those same histories give the complete CP recursion

$$
M_{t+1}(P')=\frac12
 \sum_{\substack{P,j\\U_jP=P'}}
 \operatorname{Ad}_{L_{j,P}}\circ M_t(P).
\tag{23.19}
$$

No distribution of $Z_h$ has been detached from its state $P_h$.
Summing over $P'$ and then subtracting $\mathcal C_t$ gives

$$
\begin{aligned}
\mathcal C_{t+1}&=\sum_P\Phi_P\circ M_t(P),\\
\mathcal C_{t+1}-\mathcal C_t
 &=\sum_P(\Phi_P-\operatorname{id}_3)\circ M_t(P),\\
\|\mathcal C_{t+1}-\mathcal C_t\|_\diamond
 &\le\sum_P(2\eta^2/3)p_t(P)=2\eta^2/3.
\end{aligned}
\tag{23.20}
$$

This is the conditional-CP-component bookkeeping already used in
[*AURIC FIB approximate online recovery memory*, Theorem 8.4,
(8.6)–(8.7)][AP23], here with the deterministic permutation state
and the new local residual (23.11). It requires no independence between
the current frame and the accumulated residual. In particular it does
not replace the weighted sum by a product of unconditional averages.

Since $Y^\eta_{0,I}=I_3$, $\mathcal C_0=\operatorname{id}_3$.
Telescoping (23.20) gives $2n\eta^2/3$. Each $\mathcal C_t$ is a
channel, so the triangle inequality also bounds its distance from
identity by two. On the actual branch the terminal decoder obeys

$$
D^\eta_{n,P_h}BQ_h(\eta)=BZ_h,
\qquad \mathcal F_{n,\eta}=\iota\circ\mathcal C_n.
\tag{23.21}
$$

An isometry $B\otimes I$ preserves all nonzero singular values of
an operator under $X\mapsto(B\otimes I)X(B^\dagger\otimes I)$.
Thus postcomposition by $\iota$ preserves diamond norm, giving
$\|\mathcal F_{n,\eta}-\iota\|_\diamond
=\|\mathcal C_n-\operatorname{id}_3\|_\diamond$.
This proves (23.6) at signed angle $\eta$ with every reference.

For general $\theta=k\pi/2+\eta$, the full-qutrit symmetry of
Theorem 11.2 has the explicit form

$$
\begin{gathered}
e^{ik\pi W/2}=i^kW^k,\qquad U_jW=U_{j\mathbin\oplus1},\\
V_j(\theta)=i^kV_{j\mathbin\oplus\epsilon_k}(\eta),\qquad
Q_h(\theta)=i^{kn}Q_{\widetilde h}(\eta).
\end{gathered}
\tag{23.22}
$$

The relabeling is a bijection of actual histories and preserves their
fair probabilities. The phase $i^{kn}$ is common to the entire qutrit,
including both $\xi$ and $T$, so it disappears in each branch channel.
The same terminal decoder therefore gives the same averaged corrected
channel as at $\eta$. This proves (23.6) for every real angle, including
either choice at a nearest-lattice tie. At $n=0$ the state is $I_3$,
$Y^\eta_{0,I}=I_3$, and (23.5) is $I_5$. At $\eta=0$ the residual
in (23.11) is identity for every $P,j$, proving exact recovery.
All coordinate transformations used in the argument are analysis only;
the sole quantum correction is (23.5). $\square$

## 24. Calibration sign and the coefficient of the fixed gauge

**Proposition 24.1 (A wrong-sign first-order probe).** At actual angle
$-d$, $d>0$, use the state update (23.2) with $k=0$, but mistakenly
use $+d$ in the one-step decoder (23.5). Let the resulting corrected
qutrit-coordinate channel be $\widetilde{\mathcal C}_1$. As $d\to0$,

$$
\widetilde{\mathcal C}_1
 =\operatorname{id}_3-2id[W,\,\cdot\,]+O(d^2).
\tag{24.1}
$$

For $\psi=(\xi+t_1)/\sqrt2$ and $\rho=|\psi\rangle\langle\psi|$,
its unhalved output trace-norm error is $4d+O(d^2)$. Thus the
nonnegative distance $\delta$ in (23.1) cannot replace the signed
$\eta$ in the decoder. The calibration sign is static information;
retaining it does not require another history state.

Proof. Write $\widehat H_c=0\oplus H_c$. From (23.4),
$Y^d_{1,U_j}$ has $\xi$ block $e^{id}$ and $T$ block
$e^{idH_c}U_{j,T}e^{-idH_c}$. Hence the wrong-sign residual
$(Y^d_{1,U_j})^\dagger V_j(-d)$ has $\xi$ block $e^{-2id}$
and $T$ expansion

$$
I_T-id\bigl(U_{j,T}^\dagger H_cU_{j,T}-H_c+J\bigr)+O(d^2)
 =I_T-id\bigl(2J+(-1)^jA\bigr)+O(d^2).
\tag{24.2}
$$

Averaging the two conjugations cancels the $A$ term. Since
$W=1|_{\mathbb C\xi}\oplus J$, this proves (24.1), with a remainder
bounded in diamond norm by a constant times $d^2$ near zero; this also
follows directly from analyticity of the finite matrix exponentials.
On the two-dimensional span of $\xi,t_1$, $W$ has eigenvalues $1,-1$.
The matrix $-2i[W,\rho]$ there is
$\left(\begin{smallmatrix}0&-2i\\2i&0\end{smallmatrix}\right)$,
with eigenvalues $2,-2$ and trace norm four. The reverse triangle
inequality now gives $4d+O(d^2)$. The isometric embedding leaves this
error unchanged. This is an encoded input witness, not a claim about
full-$H$ recovery or a typical history. $\square$

**Proposition 24.2 (The fixed gauge has quadratic coefficient $2/3$).**
For Definition 23.1 at $k=0,n=1$, put
$\rho_a=|t_a\rangle\langle t_a|$, $a=1,2$. Its qutrit-coordinate
channel satisfies the exact identity

$$
\mathcal C_1(\rho_1)=(1-p)\rho_1+p\rho_2,\qquad
p=\frac34\sin^2(2\eta/3).
\tag{24.3}
$$

Consequently

$$
\|\mathcal C_1-\operatorname{id}_3\|_\diamond
\ge\frac32\sin^2(2\eta/3)
=\frac23\eta^2+O(\eta^4).
\tag{24.4}
$$

No constant $c<2/3$ can replace $2/3$ in a bound $cn\eta^2$ valid
for this fixed gauge at all horizons and sufficiently small signed
angles. This is not a lower bound for all six-state terminal decoders.

Proof. Directly from (23.3),
$(C+A)^2=(C-A)^2=4I_T/9$. Therefore

$$
e^{-i\eta(C\pm A)}
 =\cos(2\eta/3)I_T-\frac{3i}{2}\sin(2\eta/3)(C\pm A).
\tag{24.5}
$$

At $P=I_3$, the other factors $S_I,e^{i\eta C},S_I^\dagger$ in
(23.11) are diagonal. They only change component phases of $t_1$ and
$t_2$. The off-diagonal transition amplitude of (24.5) has squared
modulus $3\sin^2(2\eta/3)/4$. The diagonal amplitudes are the same
for the two signs and the off-diagonal amplitudes are opposite, so
the averaged off-diagonal output entries vanish. This proves (24.3).
The two orthogonal states $\rho_1,\rho_2$ give trace norm $2p$ for
the difference from $\rho_1$, proving the diamond lower bound and its
Taylor coefficient. Dividing (24.4) by $\eta^2$ and taking
$\eta\to0$ excludes every $c<2/3$ for this construction.
In contrast, at $n=1$ storing the actual binary label and applying
$BV_j(\eta)^\dagger B^\dagger+(I_5-P_R)$ recovers exactly with
two states by Theorem 2.2 and (3.3). Thus fixed-gauge sharpness does
not establish global six-state optimality or a necessary crossover.
$\square$

## 25. Exact and approximate records on the same rational-angle instance

**Corollary 25.1 (Exact $n$ bits versus at most six states).** For every
integer $n\ge1$, every $\varepsilon>0$ and every integer $k$, choose
an integer $q$ satisfying

$$
q>\max\left\{4,\,\pi\sqrt{\frac{2n}{3\varepsilon}}\right\},
\qquad \eta=\pi/q,\qquad \theta=k\pi/2+\eta.
\tag{25.1}
$$

For the one actual measured instrument at this $\theta$ and this
horizon, the following hold under the complete-view and recovery
permissions of Definition 1.5 and Assumption 1.4:

$$
\begin{gathered}
\min|\mathcal Y_n^{\rm exact}|=2^n,\qquad
\min b_n^{\rm exact}=n,\qquad
\min H_{\rm Sh}(\mathcal Y_n^{\rm exact})=n,\\
|\{P_t:|h|=t\}|\le6\quad(0\le t\le n),\qquad
H_{\rm Sh}(P_n)\le\log_2 6,\qquad
\|\mathcal F_{n,\theta}-\iota\|_\diamond<\varepsilon.
\end{gathered}
\tag{25.2}
$$

The entropy minimum is over discrete complete exact views. The exact
lower bounds permit arbitrary randomized summaries and arbitrary terminal
CPTP maps on all $H$, with success required only on the averaged
encoded channel; the six-state upper bound uses just the single
unitary (23.5). These are the same acquired-label, same-angle,
same-horizon instances and the same encoded all-reference target.

Proof. The ratio $\theta/\pi=k/2+1/q$ is rational and is not in
$\tfrac12\mathbb Z$, since $0<1/q<1/4$. Theorem 14.2 directly gives
$m_n(\theta)=2^n$, and Theorem 16.2 directly gives the three exact
minima, including the history determination and discrete entropy
conclusion. Their attainment uses the complete actual history and its
terminal inverse. No new collision-free premise or shrinking
collision-neighborhood argument is needed. For approximate recovery,
$q>4$ makes $k\pi/2$ the nearest bounded angle, so $\delta=\pi/q$.
Theorem 23.2 and (25.1) give
$2n\delta^2/3<\varepsilon$. The state bound is (23.2).
For its entropy, if $s\le6$ states have positive probabilities $p_a$,
concavity of logarithm gives
$\sum_ap_a\log_2(1/p_a)\le\log_2\sum_ap_a/p_a=\log_2s$.
This proves (25.2). The exact suppliers are reused with their stated
scope, rather than re-proving maximal word growth or exact-record
necessity. $\square$

**Definition 25.2 (Quantifiers, attribution and unresolved boundaries).**
The sufficient six-state condition is
$n\operatorname{dist}(\theta,(\pi/2)\mathbb Z)^2\le3\varepsilon/2$.
For (25.2) the angle is explicitly permitted to depend on both $n$ and
$\varepsilon$; for example the integer
$\lfloor\max\{4,\pi\sqrt{2n/(3\varepsilon)}\}\rfloor+1$ is a
valid $q$. This is an existence statement for each finite horizon and
tolerance. It does not assert six-state recovery at any fixed nonbounded
angle for arbitrarily long horizons. For fixed $\delta>0$, the upper
bound (23.6) eventually becomes only the trivial bound two; that loss
of information in an upper bound is not a recovery impossibility proof.
The coefficient limitation in Proposition 24.2 is specific to (23.4).
The optimal error over all six-state controllers, a necessary
error-memory crossover, and a uniform fixed-nonzero-angle long-horizon
construction are not determined by these statements.

The additive Poisson correction [GM23] and quadratic unitary mixing
[CA23] are literature-attested mechanisms used inside the actual-model
derivation. The conditional CP-component method is already supplied by
[AP23, Theorem 8.4][AP23]. The project-specific additional deduction is
the explicit signed gauge (23.3)–(23.5), its all-angle and all-reference
bound with correlated frame/residual bookkeeping, its calibration and
coefficient probes, and its composition with the existing exact rational
suppliers in (25.2). This is a repo-derived ordinary application with
complete derivations, without a claim of literature priority or a
kernel certificate. No physical realization is inferred from the ideal
measured-instrument and exact-control premises.

At the original fixed angle $\theta=\pi/6$, the online memory problem
of [AP23, Definitions 2.3–2.4 and Theorem 9.1][AP23] has the separate
fixed-error bounds
$c_{\gamma,\varepsilon}(n/\ln n)^{3/2}\le W_n(\varepsilon)
\le C_\varepsilon n^{3/2}$ in their stated range. The present angle
choice does not close that logarithmic gap, supply its constants or
replace its fixed-angle quantifiers. The operational resources remain
those of Definition 23.1: six counts only the persistent classical
history state, not calibrated angle precision, terminal-control
precision, acquisition cost or the externally supplied horizon.
The average-channel error gives no per-history or high-probability
guarantee. Full-$H$ input inversion, retained-environment recovery,
intermediate quantum control, additional recovery ancillas,
postselection and reference access remain outside these conclusions.

[GM23]: https://web.stanford.edu/~glynn/papers/1996/GM96.pdf
[CA23]: https://arxiv.org/html/1612.02689v3
[AP23]: https://github.com/the-omega-institute/trureturing/blob/ff06ef4d419e29fee5224ec3d78175a5144a9568/docs/develop/theory/AURIC_FIB_APPROXIMATE_ONLINE_RECOVERY_MEMORY.md

## 追加锚（本行以下为增补区）

## 26. Exact sharp tasks and common correction after history erasure

**Definition 26.1 (Whole-qutrit erasure channel and task contract).** Work
in the qutrit coordinates of Definition 11.1. Denote this entire system by
$H_q=\mathbb C^3$; it is identified with $R$ by $B$ of Definition 1.3,
and is distinct from the five-dimensional $H$ used earlier. Fix any real
$\theta$ and finite integer $n\ge0$. Retain exactly the actual letters

$$
\begin{gathered}
a=V_0(\theta)=U_0e^{i\theta W},\qquad b=V_1(\theta)=aW,\\
U_0=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\qquad
W=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix},\qquad U_1=U_0W,\\
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\qquad
P=|\xi\rangle\langle\xi|,\qquad T=\xi^\perp,\\
Q_h=V_{h_n}(\theta)\cdots V_{h_1}(\theta),\qquad Q_\varnothing=I_3.
\end{gathered}
\tag{26.1}
$$

Here the entries of $h=(h_1,\ldots,h_n)$ are chronological: $h_1$
acts first. Throughout this section $P$ means this qutrit spectator
projection. Let $p=(p_h)_{h\in\{0,1\}^n}$ be an input-independent
probability law with full support, and erase its entire history:

$$
p_h>0,\qquad \sum_h p_h=1,\qquad
\mathcal N_{n,p}(X)=\sum_h p_hQ_hXQ_h^\dagger,\qquad
K_h=\sqrt{p_h}\,Q_h.
\tag{26.2}
$$

At $n=0$ the sole weight is $p_\varnothing=1$. No factorization of $p$
is assumed. The repeated measured instrument of Definition 11.1 has
the particular law $p_h=2^{-n}$. Other full-support laws, including
correlated laws, define mixtures of the same actual word matrices;
they are an extension of that law, without an assertion that the fresh
fair instrument produces those other distributions. Each horizon may
have its own $p$; consistency between horizons is not a premise.

A complex unital star subalgebra $\mathcal A\subseteq M_3$, with unit
$I_3$, is commonly correctable if one qutrit CPTP map
$\mathcal D:M_3\to M_3$ satisfies

$$
(\mathcal D\circ\mathcal N_{n,p})^\dagger(X)=X
\qquad(X\in\mathcal A).
\tag{26.3}
$$

The dagger on a channel denotes its trace adjoint. The decoder knows
$\theta,n,p$ and the prescribed task, but has no history label or
input-dependent side information. It acts once after $\mathcal N_{n,p}$,
without postselection. All input density matrices on $H_q$ are included;
there is no encoding into a smaller input subspace.

For a prescribed orthogonal projection $E\in M_3$, its sharp binary
task is the Born probability $\operatorname{tr}(E\rho)$. Define

$$
\eta_{n,p}(E)=\inf_{\mathcal D\ {\rm CPTP}}
 \sup_{\rho\in\mathsf D(H_q)}
 \left|\operatorname{tr}\bigl(E\mathcal D\mathcal N_{n,p}(\rho)\bigr)
                  -\operatorname{tr}(E\rho)\right|.
\tag{26.4}
$$

The decoder may depend on $E$, while $E$ is fixed before the unknown
input. For a finite list $\mathscr E=(E_1,\ldots,E_m)$, $m\ge1$,
use the same infimum with the maximum of the $m$ displayed errors
and one common $\mathcal D$; write it as $\eta_{n,p}(\mathscr E)$.
Let $\operatorname{alg}^*(I_3,\mathscr E)$ be the complex unital star
algebra generated by those projections. These definitions concern
sharp tasks and observable algebras, rather than full-state recovery.

**Theorem 26.2 (Largest common-correctable algebra of the actual words).**
For every real $\theta$, every finite $n\ge0$ and every law (26.2),
the unique largest commonly correctable unital star algebra is

$$
\begin{aligned}
\mathcal C_{n,p}
&:=\{K_h^\dagger K_g:h,g\in\{0,1\}^n\}'
 =\{Q_h^\dagger Q_g:h,g\in\{0,1\}^n\}'\\
&=\begin{cases}
M_3,&n=0,\\
\{W\}'\cong M_2\oplus\mathbb C,&n=1,\\
\mathbb CP\oplus\mathbb C(I_3-P),&n\ge2.
\end{cases}
\end{aligned}
\tag{26.5}
$$

The prime denotes the simultaneous commutant in all of $M_3$.
A unital star algebra is correctable exactly when it is contained
in the corresponding algebra in (26.5). One decoder correcting
the entire displayed algebra, and therefore every one of its
subalgebras simultaneously, is respectively

$$
\mathcal D_0=\operatorname{id}_3,\qquad
\mathcal D_1=\operatorname{Ad}_{a^\dagger},\qquad
\mathcal D_n=\operatorname{id}_3\quad(n\ge2).
\tag{26.6}
$$

Proof. The general correction interface being used is
Bény–Kempf–Kribs, *Quantum Error Correction of Observables*,
[arXiv:0705.1574v1][BKK26], Definition 8, equation (7), Theorem 9
and Corollary 10. The existing [observable-correction note][NOTE26]
records that interface. In their notation the channel is
$\mathcal E=\mathcal N_{n,p}$, its operation elements are $E_h=K_h$,
the correction is $\mathcal R=\mathcal D$, and the code projection
in their equation (7) is $P_{\rm code}=I_3$. Thus their condition
is precisely (26.3), and their compressed products
$P_{\rm code}E_h^\dagger E_gP_{\rm code}$ are $K_h^\dagger K_g$.
The spectator $P$ in (26.1) is not their code projection. The
commutant criterion and its general maximality are reused literature
results. The following argument supplies the needed necessity and
explicit recoveries for these particular full-qutrit channels.

Suppose (26.3) holds for $\mathcal A$. Choose Kraus matrices $L_r$
for $\mathcal D$ and put $M_{rh}=L_rK_h$, so these are Kraus
matrices of $\mathcal T=\mathcal D\circ\mathcal N_{n,p}$ and
$\sum_{r,h}M_{rh}^\dagger M_{rh}=I_3$. For $X\in\mathcal A$,
the elements $X,X^\dagger,X^\dagger X$ all belong to $\mathcal A$.
Expansion of the Schwarz defect gives

$$
\begin{aligned}
&\sum_{r,h}(XM_{rh}-M_{rh}X)^\dagger(XM_{rh}-M_{rh}X)\\
&\quad=\mathcal T^\dagger(X^\dagger X)
 -\mathcal T^\dagger(X^\dagger)X
 -X^\dagger\mathcal T^\dagger(X)+X^\dagger X=0.
\end{aligned}
\tag{26.7}
$$

Every summand is positive. Evaluating on every vector shows that each
$XM_{rh}-M_{rh}X$ vanishes. Applying the same argument to $X^\dagger$
and taking adjoints also gives $[X,M_{rh}^\dagger]=0$. Consequently
$X$ commutes with

$$
\sum_r M_{rh}^\dagger M_{rg}
 =K_h^\dagger\left(\sum_rL_r^\dagger L_r\right)K_g
 =K_h^\dagger K_g.
\tag{26.8}
$$

This proves $\mathcal A\subseteq\mathcal C_{n,p}$ for every common
CPTP decoder, without assuming that decoder unitary. Moreover
$K_h^\dagger K_g=\sqrt{p_hp_g}\,Q_h^\dagger Q_g$.
Full support makes every scalar nonzero, proving the first line
of (26.5). No independence of the labels enters this step.

At $n=0$ the only relative is $I_3$ and the channel is identity.
At $n=1$ the relatives are $I_3$ and
$a^\dagger b=b^\dagger a=W$, because $b=aW$ and $W^2=I_3$.
Thus $\mathcal C_{1,p}=\{W\}'$. In the orthonormal basis
$S_0=[\xi,t_1,t_2]$ of Theorem 6.1,
$S_0^\dagger WS_0=\operatorname{diag}(1,-1,1)$, and its commutant is

$$
S_0^\dagger\mathcal C_{1,p}S_0
 =\left\{\begin{pmatrix}
x_{11}&0&x_{13}\\0&x_{22}&0\\x_{31}&0&x_{33}
\end{pmatrix}:x_{jk}\in\mathbb C\right\}.
\tag{26.9}
$$

This is $M_2$ on $\operatorname{span}\{\xi,t_2\}$ and $\mathbb C$
on $\mathbb Ct_1$. In particular it includes coherences between
the spectator and $t_2$. Undoing the known reference letter gives

$$
\mathcal D_1\circ\mathcal N_{1,p}
 =p_0\operatorname{id}_3+p_1\operatorname{Ad}_W.
\tag{26.10}
$$

Its adjoint fixes every element of (26.9). This proves both the
one-step attainability and its full-qutrit scope.

Now fix $n\ge2$. Three actual histories suffice for the upper
inclusion. Write $o=0^n$, $e_1=(1,0,\ldots,0)$ and
$e_2=(0,1,0,\ldots,0)$, with the nonzero entries in the first
and second chronological positions. Direct cancellation in the
actual order gives

$$
\begin{aligned}
Q_o&=a^n,\\
Q_{e_1}&=a^{n-1}b=a^nW,\\
Q_{e_2}&=a^{n-2}ba=a^{n-1}Wa,\\
Q_o^\dagger Q_{e_1}&=W,\qquad
Q_o^\dagger Q_{e_2}=a^{-1}Wa.
\end{aligned}
\tag{26.11}
$$

They all have positive probability by (26.2); hence
$\mathcal C_{n,p}\subseteq\{W,a^{-1}Wa\}'$. Reuse the actual
permutation identities (12.4), valid at every real angle:

$$
aWa^{-1}=U_0WU_0,\qquad W(U_0WU_0)W=U_0.
\tag{26.12}
$$

Conjugating the two-relative commutant by $a$ therefore gives

$$
\begin{aligned}
a\{W,a^{-1}Wa\}'a^\dagger
 &=\{U_0WU_0,W\}'\\
 &=\{U_0,W\}'=\{U_0,U_1\}'
 =\mathbb CP\oplus\mathbb C(I_3-P).
\end{aligned}
\tag{26.13}
$$

For the middle equality, commuting with $W$ and $U_0WU_0$
implies commuting with their product $W(U_0WU_0)W=U_0$;
the reverse implication follows by multiplying those matrices.
The equality with $\{U_0,U_1\}'$ uses $U_1=U_0W$ and
$W=U_0^\dagger U_1$. The last equality is the existing
three-dimensional permutation commutant in [Half-Gram classification,
§6, equation (6.4) and its proof][HG26]: in its recurrent coordinates
$(u,v,z)$ the matrices are precisely the present $U_0,U_1$, its
vector $s$ is $B\xi$, and its recurrent identity $P_{R_3}$ is
$BI_3B^\dagger$. Thus its algebra
$\operatorname{span}\{|s\rangle\langle s|,
P_{R_3}-|s\rangle\langle s|\}$ becomes the last algebra in
(26.13). This uses the full three-dimensional commutant, including
the spectator line.

The cross-block equations make that last point explicit. In
$\mathbb C\xi\oplus T$ write a commuting matrix as
$Y=\left(\begin{smallmatrix}\alpha&r\\c&C\end{smallmatrix}\right)$.
Theorem 6.1 supplies

$$
W=1\oplus J,\qquad U_0=1\oplus S,\qquad
J=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\qquad
S=\begin{pmatrix}1/2&\sqrt3/2\\\sqrt3/2&-1/2\end{pmatrix}.
\tag{26.14}
$$

Commutation forces $Jc=c$, $Sc=c$, $rJ=r$ and $rS=r$.
The $J$ equations give $c=(0,z)^{\mathsf T}$ and $r=(0,w)$;
the first coordinates of the $S$ equations give
$\sqrt3 z/2=\sqrt3 w/2=0$. Both cross blocks vanish.
The active-block calculation in Theorem 12.1 says $C$ is scalar:
$[C,J]=0$ makes it diagonal, and $[C,S]=0$ equates its two
diagonal entries. Hence no spectator-active coherence is omitted
in (26.13). A scalar commutant on $T$ alone would not establish
this full-qutrit assertion.

Both $U_0$ and $W$ fix $\xi$, so $a\xi=b\xi=e^{i\theta}\xi$.
Their unitarity makes $\mathbb C\xi\oplus T$ reducing. In
particular $a$ commutes with $P$, and conjugation by $a$ fixes
$\mathbb CP\oplus\mathbb C(I_3-P)$ pointwise. Equation (26.13)
then proves
$\mathcal C_{n,p}\subseteq\mathbb CP\oplus\mathbb C(I_3-P)$.
Conversely, every $Q_h$ commutes with $P$. Thus every
$Q_h^\dagger Q_g$ commutes with both $P$ and $I_3-P$, proving
the opposite inclusion in (26.5). Also, for
$X=\alpha P+\beta(I_3-P)$,

$$
\mathcal N_{n,p}^\dagger(X)=\sum_hp_hQ_h^\dagger XQ_h=X.
\tag{26.15}
$$

Identity is therefore one common recovery for the entire algebra
at every $n\ge2$. The necessity (26.8) excludes every algebra
not contained in it. Together with (26.9)–(26.10) and the empty
horizon, this proves uniqueness, maximality and all the stated
recoveries.

The correspondence to the fixed actual $\theta=\pi/6$ model can
also be made entrywise, without substituting different word
matrices. In (26.14) the active letter is

$$
\begin{aligned}
A_\theta=a|_T
 &=S\operatorname{diag}(e^{-i\theta},e^{i\theta}),\qquad b|_T=A_\theta J,\\
A_{\pi/6}
 &=\frac14\begin{pmatrix}
\sqrt3-i&3+i\sqrt3\\3-i\sqrt3&-\sqrt3-i
\end{pmatrix}=A,\\
A_\theta^\dagger JA_\theta
 &=\begin{pmatrix}
1/2&-\sqrt3 e^{2i\theta}/2\\
-\sqrt3 e^{-2i\theta}/2&-1/2
\end{pmatrix}.
\end{aligned}
\tag{26.16}
$$

Here $A,J$ are exactly [Purity arithmetic, Proposition 63.2,
(63.4)–(63.6)][PA26], and its $f_1,f_2$ equal the present
$t_1,t_2$. The off-diagonal entries of the second relative
are nonzero for every real $\theta$, including the bounded
angles of Theorem 12.1. At $\pi/6$ they are
$-\sqrt3/4-3i/4$ and $-\sqrt3/4+3i/4$.
To retain the spectator phase in that source's notation, put
$\lambda=e^{i\pi/6}$ and
$G_h=g_{h_n}\cdots g_{h_1}$ with $g_0=A,g_1=AJ$. Its
Definition 51.1 gives

$$
\begin{aligned}
Q_h&=\lambda^nS_0(1\oplus\lambda^{-n}G_h)S_0^\dagger,\\
Q_h^\dagger Q_g&=S_0(1\oplus G_h^\dagger G_g)S_0^\dagger
\qquad(|h|=|g|=n).
\end{aligned}
\tag{26.17}
$$

Both scalar phases cancel in the relatives; their spectator block
is still one. In particular the two relatives in (26.11) are
$S_0(1\oplus J)S_0^\dagger$ and
$S_0(1\oplus A^\dagger JA)S_0^\dagger$ at that angle.
This verifies the exact actual-parameter specialization. $\square$

**Corollary 26.3 (Exhaustion of sharp tasks and a common task decoder).**
Under Definition 26.1 the infima defining $\eta_{n,p}(E)$ and
$\eta_{n,p}(\mathscr E)$ are attained. For every finite projection
list $\mathscr E$,

$$
\eta_{n,p}(\mathscr E)=0
\quad\Longleftrightarrow\quad
\operatorname{alg}^*(I_3,\mathscr E)\subseteq\mathcal C_{n,p}.
\tag{26.18}
$$

For one prescribed projection the complete list is

$$
\eta_{n,p}(E)=0
\quad\Longleftrightarrow\quad
\begin{cases}
E\text{ is any orthogonal projection in }M_3,&n=0,\\
[E,W]=0,&n=1,\\
E\in\{0,I_3,P,I_3-P\},&n\ge2.
\end{cases}
\tag{26.19}
$$

At $n=1$ such a projection is an arbitrary projection on
$\operatorname{span}\{\xi,t_2\}$ direct-summed with either zero
or identity on $\mathbb Ct_1$. At $n\ge2$, $P$ is the only
nontrivial sharp binary task up to exchange of its two outcomes.
In every case the relevant map (26.6) corrects all the admitted
projections simultaneously, on all qutrit input states.

Proof. For any fixed CPTP $\mathcal D$ the error in (26.4) is

$$
\left\|(\mathcal D\circ\mathcal N_{n,p})^\dagger(E)-E
\right\|_{\rm op}.
\tag{26.20}
$$

Indeed the difference is Hermitian, so the supremum of the absolute
expectation over density matrices is its largest absolute eigenvalue,
attained on an eigenvector density. In output-first convention the
Choi matrices of qutrit CPTP maps form the nonempty set

$$
\{J\in M_3\otimes M_3:J\succeq0,
                   \operatorname{Tr}_{\rm out}J=I_3\}.
\tag{26.21}
$$

It is closed and bounded, since its positive elements have trace
three, hence compact in finite dimension. The expression (26.20)
is continuous in $J$; so is its maximum over a finite list. Both
infima are consequently minima. Thus zero error means one actual
CPTP decoder realizes the equality, including when the definition
is initially phrased using an infimum.

For such a decoder put $\mathcal T=\mathcal D\circ\mathcal N_{n,p}$.
Equality of Born probabilities on all density matrices is equivalent
to $\mathcal T^\dagger(E_j)=E_j$ by (26.20). For one projection,
linearity and $\mathcal T^\dagger(I_3)=I_3$ already fix its entire
algebra $\operatorname{span}\{E_j,I_3-E_j\}$. For a list, apply
the defect (26.7) to each $E_j$: its square is itself, so that
defect is zero without assuming that the generated algebra is
already fixed. It follows that every Kraus matrix $M_{rh}$ of
$\mathcal T$ and its adjoint commute with every $E_j$. They
therefore commute with all finite sums and products generating
$\operatorname{alg}^*(I_3,\mathscr E)$. For each $X$ in that algebra,

$$
\mathcal T^\dagger(X)=\sum_{r,h}M_{rh}^\dagger XM_{rh}
 =X\sum_{r,h}M_{rh}^\dagger M_{rh}=X.
\tag{26.22}
$$

Theorem 26.2 now gives the forward implication of (26.18).
Conversely, containment there lets the single explicit decoder
in (26.6) fix every $E_j$, giving zero error for the whole list.
This constructs simultaneity directly; it does not combine
separately chosen optimizing channels.

For $n\ge2$, a projection in
$\mathbb CP\oplus\mathbb C(I_3-P)$ has the form
$\alpha P+\beta(I_3-P)$. Self-adjointness and idempotence force
$\alpha,\beta\in\{0,1\}$, proving exactly the four possibilities.
The other horizons follow from (26.5) and (26.9). The invariant
$P$ task itself is the existing [Purity arithmetic, Theorem 86.2][PA26];
the exhaustion here uses the additional relative-product necessity
and full-qutrit commutant. $\square$

**Proposition 26.4 (Support sufficiency and strict counterexamples).**
Keep the actual letters, chronology, full-qutrit inputs and decoder
class of Definition 26.1, but allow zero probabilities. At $n\ge2$,
positive mass on the three histories $o,e_1,e_2$ of (26.11) is
already sufficient for the maximal algebra and sharp-task list
in (26.5) and (26.19), regardless of which other histories occur.
Full support is therefore a sufficient uniform hypothesis and is
not necessary for each individual law. If no support hypothesis
is imposed, the same fixed angle and horizon admit both of the
strictly larger maximal algebras

$$
M_3\qquad\text{and}\qquad\{W\}'\cong M_2\oplus\mathbb C.
\tag{26.23}
$$

Proof. For an arbitrary support $S_p=\{h:p_h>0\}$, omit zero
Kraus matrices. The argument (26.7)–(26.8) puts every correctable
algebra inside
$\{Q_h^\dagger Q_g:h,g\in S_p\}'$.
If $o,e_1,e_2\in S_p$, their relatives are still exactly (26.11).
Equations (26.12)–(26.14) give the same upper inclusion as before,
and (26.15) gives its attainment with identity for any law.
The sharp-task argument of Corollary 26.3 applies unchanged.
In particular a law supported on just these three histories,
each of positive mass, has the two-dimensional maximal algebra.

For the first counterexample put all mass on one known history
$h_*$. Then $\mathcal N_{n,p}=\operatorname{Ad}_{Q_{h_*}}$,
and the qutrit CPTP decoder $\operatorname{Ad}_{Q_{h_*}^\dagger}$
makes the composed channel identity. All of $M_3$ is corrected.
For an explicit additional sharp task,
$E_*=|t_1\rangle\langle t_1|$ is exactly readable with this
decoder. It is neither $0,I_3,P$ nor $I_3-P$: it has rank one
and its range is orthogonal to $\xi$.

For a genuinely random second counterexample, put $p_o=t$,
$p_{e_1}=1-t$ with $0<t<1$ and all other probabilities zero.
Since $Q_{e_1}=a^nW$, undoing $a^n$ gives

$$
\operatorname{Ad}_{(a^n)^\dagger}\circ\mathcal N_{n,p}
 =t\operatorname{id}_3+(1-t)\operatorname{Ad}_W.
\tag{26.24}
$$

It fixes $\{W\}'$ in the Heisenberg picture. The two supported
histories have relative $W$, and their Kraus weights are positive,
so (26.8) requires every correctable algebra to lie in $\{W\}'$.
Thus (26.24) attains precisely the second maximal algebra in
(26.23). It strictly contains
$\mathbb CP\oplus\mathbb C(I_3-P)$: for example
$|\xi\rangle\langle t_2|$ commutes with $W$ and lies outside
that two-dimensional algebra. A corresponding extra sharp task is

$$
E_+=|v_+\rangle\langle v_+|,\qquad
v_+=(\xi+t_2)/\sqrt2.
\tag{26.25}
$$

Because $Wv_+=v_+$, this projection belongs to $\{W\}'$ and
is exactly corrected by (26.24); its rank and its nonzero
spectator-active cross blocks exclude all four projections in
(26.19) at $n\ge2$. Both counterexamples keep the same actual
words and preserve $P$. What changes is their positive support.
They show why the full-support all-laws assertion cannot simply
be extended to every probability law. $\square$

**Definition 26.5 (Application scope).** The algebra criterion used
inside Theorem 26.2 is the literature result [BKK26, Definition 8,
Theorem 9 and Corollary 10][BKK26]. The actual matrices and their
all-angle identities are (11.1), (12.4) and Theorem 6.1; the
three-dimensional permutation commutant is also supplied by
[HG26, §6][HG26]. The fixed-angle spectator task is already
[PA26, Theorem 86.2][PA26]. The source-specific deduction here
is the full-qutrit finite-horizon algebra (26.5), its boundary
horizons, the exhaustive sharp-task and simultaneous-decoder
statements, and the support counterexamples. The equality of
averaged channels and differing record counts in §§11–16 are
separate existing results and are not an additional conclusion
of this classification.

The scope is unital star algebras and prescribed orthogonal
projections, on the entire qutrit input space, with qutrit CPTP
decoders after complete history erasure. Arbitrary unsharp effects,
operator systems, smaller input codes and different decoder menus
are not classified. These are exact statements at each finite
horizon; they provide no approximate recovery bound, critical
long-word estimate or full-state memory law uniform over unbounded
horizons. The extension to correlated laws concerns the same
word matrices with different input-independent weights. It does
not change the fair fresh-environment law of the actual instrument.
The conclusions are ordinary finite-dimensional mathematical
applications under the stated premises, without a physical
realization or literature-priority assertion.

[BKK26]: https://arxiv.org/html/0705.1574v1
[NOTE26]: ../../../Library/Quantum/benykempfkribs2007observables.md
[HG26]: https://github.com/the-omega-institute/trureturing/blob/2cd10a669fdb32fb481abd7136cac1b9ef480ee0/docs/develop/theory/AURIC_FIB_FIVE_WINDOW_HALF_GRAM_CLASSIFICATION.md
[PA26]: https://github.com/the-omega-institute/trureturing/blob/2cd10a669fdb32fb481abd7136cac1b9ef480ee0/docs/develop/theory/AURIC_FIB_ACTUAL_WORD_PURITY_ARITHMETIC.md

## 追加锚（本行以下为增补区）

## 27. Quantitative sharp tasks after fair chronological history erasure

### 27.1. Task, actual channel and attainable effects

**Definition 27.1 (One terminal task on the whole qutrit).** Use the actual
matrices and chronological words of (26.1), at any real angle $\theta$
and finite integer horizon $n\ge0$, with the fair independent law of
Definition 11.1. In this chapter set

$$
\begin{gathered}
\Delta_W(X)=\tfrac12(X+WXW),\qquad
F=\operatorname{Ad}_{U_0}\circ\Delta_W
 =\tfrac12(\operatorname{Ad}_{U_0}+\operatorname{Ad}_{U_1}),\qquad
\mathcal N_n=F^n,\\
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\quad
e=(1,1,-2)^{\mathsf T}/\sqrt6,\quad
f=(1,-1,0)^{\mathsf T}/\sqrt2,\\
E=|v\rangle\langle v|,\quad \|v\|=1,\quad
p=|\langle\xi,v\rangle|^2,\quad q=|\langle e,v\rangle|^2,\quad
r=|\langle f,v\rangle|^2,\quad p+q+r=1,\\
\eta_n(E)=\min_{\mathcal D\ {\rm CPTP}}
 \sup_{\rho\in\mathsf D(\mathbb C^3)}
 \left|\operatorname{Tr}(E\mathcal D F^n(\rho))
                   -\operatorname{Tr}(E\rho)\right|.
\end{gathered}
\tag{27.1}
$$

The decoder is a single qutrit channel, chosen for $E,n$, independent of
the unknown input. All qutrit density matrices are included. There is no
history, reference access, smaller input code, intermediate correction or
postselection. The loss is a probability error, not a diamond distance.
The symbols $p,q,r$ here are task populations, not the law $p_h$ of §26.
For each finite $n\ge1$ write

$$
s=(-1/2)^{n-1},\qquad \tau=|s|>0,\qquad
\alpha=(1+s)/2,\quad \beta=(1-s)/2,\qquad
k=\sqrt{r(1-r)}.
\tag{27.2}
$$

The horizon $n=0$ is treated separately throughout. No inverse involving
$s$ below is evaluated at an infinite horizon.

The identification $\mathcal N_n=F^n$ uses the actual all-angle law,
not a replacement instrument. Indeed, putting $R_\theta=e^{i\theta W}$,
Theorem 2.2 gives $V_0=U_0R_\theta$, $V_1=V_0W$. Since $\Delta_W(X)$
commutes with $W$,

$$
\tfrac12\sum_j V_jXV_j^\dagger
 =U_0R_\theta\Delta_W(X)R_\theta^\dagger U_0^\dagger=F(X).
\tag{27.3}
$$

Each normalized branch is unitary, so its actual next outcome has
conditional probability $1/2$ after every preceding history and on every
qutrit input. Thus the chronological history law is $2^{-n}$; summing
the products $V_{h_n}\cdots V_{h_1}$ gives $F^n$ at every angle.

We reuse the task-effect interface of [Purity arithmetic, §86][PA27]
and the [observable-correction note][NOTE26]:

$$
\begin{aligned}
\eta_n(E)&=\min_{0\le B\le I_3}\|(F^n)^\dagger(B)-E\|_{\rm op},\\
\eta_n(E)&\ge\operatorname{Tr}(YE)
                 -\operatorname{Tr}\bigl((F^n(Y))_+\bigr)
 \quad(Y=Y^\dagger,\ \|Y\|_1\le1).
\end{aligned}
\tag{27.4}
$$

Here $A_+$ is the positive part of a Hermitian matrix. To fix the decoder
for every construction below, choose any fixed densities $\sigma_1$ in
$\operatorname{ran}E$ and $\sigma_0$ in $\ker E$ and use

$$
\mathcal D_B(X)=\operatorname{Tr}(BX)\sigma_1
                      +\operatorname{Tr}((I_3-B)X)\sigma_0.
\tag{27.5}
$$

For rank-one $E$, one explicit choice is $\sigma_1=E$ and
$\sigma_0=(I_3-E)/2$. This is CPTP with $\mathcal D_B^\dagger(E)=B$.
Conversely every decoder
supplies such an effect. The all-density supremum is the operator norm
of its Hermitian residual. The second line of (27.4) follows from
trace/operator-norm duality and
$\max_{0\le B\le I}\operatorname{Tr}(AB)=\operatorname{Tr}(A_+)$,
obtained by diagonalizing $A$. These are reused general tools. The
minimum is attained because the effect interval is compact.

**Proposition 27.2 (Entire effect image and complex orientation).** For
every finite $n\ge1$, in the ordered orthonormal basis $(\xi,e,f)$,
the entire set of effects
$(F^n)^\dagger(B)$, $0\le B\le I_3$, is

$$
\begin{gathered}
C=G_s(K)=\begin{pmatrix}
x&sz&0\\s\overline z&\alpha y+\beta d&0\\
0&0&\beta y+\alpha d
\end{pmatrix},\qquad
K=\begin{pmatrix}x&z&0\\\overline z&y&0\\0&0&d\end{pmatrix},\\
0\le K_2:=\begin{pmatrix}x&z\\\overline z&y\end{pmatrix}\le I_2,
\qquad 0\le d\le1.
\end{gathered}
\tag{27.6}
$$

Each displayed $C$ is attained by the physical output effect
$B=U_0KU_0^\dagger$ and hence by (27.5). The error depends only on
$(p,r)$, with $q=1-p-r$, even for complex $v$.

Proof. In this basis the actual matrices are

$$
W=\operatorname{diag}(1,1,-1),\qquad
U_0=1\oplus\begin{pmatrix}-1/2&\sqrt3/2\\\sqrt3/2&1/2\end{pmatrix}.
$$

Thus $F^\dagger=\Delta_W\circ\operatorname{Ad}_{U_0^\dagger}$ maps
the effect interval onto its $W$-commuting part, with right inverse
$K\mapsto U_0KU_0^\dagger$. On that part, one further adjoint step
sends $z$ to $-z/2$ and sends $(y,d)$ to
$((y+3d)/4,(3y+d)/4)$, fixing $x$. It fixes $y+d$ and multiplies
$y-d$ by $-1/2$. Iterating gives exactly (27.6), including surjectivity.
By trace duality the same calculation also gives, for every Hermitian $Y$,

$$
F^n(Y)=U_0G_s(\Delta_W(Y))U_0^\dagger,
\tag{27.7}
$$

where $G_s$ is extended linearly to block Hermitian matrices.

For every diagonal unitary $\Lambda$ in $(\xi,e,f)$,
$G_s(\Lambda K\Lambda^\dagger)=\Lambda G_s(K)\Lambda^\dagger$,
and conjugation preserves both effect constraints. Taking
$v=\Lambda(\sqrt p,\sqrt q,\sqrt r)^{\mathsf T}$ therefore removes
all phases from the optimization. Primal $K$ and dual $Y$ transfer to
$\Lambda K\Lambda^\dagger$ and $\Lambda Y\Lambda^\dagger$; (27.7)
preserves the dual support value under this transfer. The physical
effect becomes $U_0\Lambda K\Lambda^\dagger U_0^\dagger$.
This is diagonal invariance of the attainable effect set; it does not
assert diagonal-unitary covariance of $F$. $\square$

The restricted polynomial and iteration supplying the factor $s$ are
already [Five-window quantum memory, §§19–20][QM27]: on $M_3$,
$F(F-I)(F+I/2)=0$, $L=(F+2F^2)/3$ and
$F^n=L+s(F-L)$ for $n\ge1$. These are reused with the qutrit restriction;
the full $M_5$ polynomial has the additional zero-mode transient described
there. Neither the polynomial nor its EB limit is a new task optimum.

### 27.2. The erased-coherence floor and the complete one-step value

**Theorem 27.3 (Empty and one-step horizons).** For every complex unit $v$,

$$
\eta_0(E)=0,\qquad \eta_1(E)=k,\qquad
\eta_n(E)\ge k\quad(n\ge1).
\tag{27.8}
$$

Proof. At $n=0$ take $B=E$. For $0<r<1$, let
$\Pi_+=(I_3+W)/2$, $\Pi_-=(I_3-W)/2$ and set
$u=\Pi_+v/\sqrt{1-r}$, $w=\Pi_-v/\sqrt r$. These are orthonormal.
The difference $E-\Delta_W(E)$ is
$k(|u\rangle\langle w|+|w\rangle\langle u|)$, with eigenvalues
$k,-k,0$. At $n=1$ choose $K=\Delta_W(E)$ and
$B=U_0KU_0^\dagger$. Equation (27.6) has $s=1$ and gives $C=K$,
so this attains error $k$.

For the matching lower certificate put

$$
Y_*=(|u\rangle\langle w|+|w\rangle\langle u|)/2.
\tag{27.9}
$$

It has trace norm one, $\Delta_W(Y_*)=0$ and
$\operatorname{Tr}(Y_*E)=k$. Hence $F^n(Y_*)=0$ at every $n\ge1$,
and (27.4) supplies the floor. If $r=0$ or $r=1$, the target already
commutes with $W$; the same one-step primal has zero error and the
lower bound is nonnegativity, with no division by zero. $\square$

### 27.3. Exact values on the active plane

**Theorem 27.4 (The boundary $p=0$ at every finite positive horizon).**
Suppose $p=0$, so $q+r=1$. Define

$$
h=q-r,\qquad \delta=\operatorname{clip}(h,-\tau,\tau),\qquad
t=\tfrac12\sqrt{4qr+(|h|-\tau)_+^2}.
\tag{27.10}
$$

Then $\eta_n(E)=t$ for every finite $n\ge1$. After phase removal,
an attaining effect in (27.6) is

$$
K=\operatorname{diag}\left(0,\frac{1+\delta/s}{2},
                              \frac{1-\delta/s}{2}\right).
\tag{27.11}
$$

Proof. Since $|\delta/s|\le1$, this is an effect. Its image is
$C=0\oplus\operatorname{diag}((1+\delta)/2,(1-\delta)/2)$.
On $(e,f)$ the residual $R=E-C$ is traceless with entries
$R_{ee}=(h-\delta)/2$, $R_{ff}=-(h-\delta)/2$,
$R_{ef}=R_{fe}=\sqrt{qr}$. Its eigenvalues are $t,-t$, because
$t^2=qr+(h-\delta)^2/4$. Thus the primal error is $t$.

If $t>0$, extend $Y=R/(2t)$ by zero on $\xi$. Its trace norm is
one. Applying (27.7) gives the exact support and task values

$$
\operatorname{Tr}\bigl((F^n(Y))_+\bigr)
 =\frac{\tau|h-\delta|}{4t},\qquad
\operatorname{Tr}(YE)=\frac{1-\delta h}{4t}.
\tag{27.12}
$$

Indeed erasure kills its $e$–$f$ entry and the two remaining active
eigenvalues after propagation are $\pm s(h-\delta)/(4t)$, up to the
physical $U_0$ conjugation. The task trace uses $h^2+4qr=1$.
Clipping gives $\delta(h-\delta)=\tau|h-\delta|$, whether $h$ lies
inside or outside the clipping interval. Consequently the difference
in (27.12) is $(1-2\delta h+\delta^2)/(4t)=t$. Equation (27.4)
proves the lower bound against every full-qutrit effect. If $t=0$,
(27.11) already attains zero, and nonnegativity completes the proof
without defining $R/(2t)$. Complex phases transfer by Proposition 27.2.
Although this witness is supported on $(e,f)$, the input domain has
not been restricted to that plane. $\square$

### 27.4. Exact values on the spectator–negative-sector plane

**Theorem 27.5 (The boundary $q=0$).** Suppose $q=0$, $p+r=1$ and
$n\ge2$ is finite. Set $a=(1+\tau)/2$, $b=(1-\tau)/2$, so
$a+b=1$, $a-b=\tau>0$ and $b\ge1/4$. Define

$$
h_\tau(w)=\begin{cases}
bw/a,&0\le w\le a,\\
(aw-\tau)/b,&a\le w\le1.
\end{cases}
\tag{27.13}
$$

With $k=\sqrt{pr}$, the exact value is

$$
\eta_n(E)=\begin{cases}
k,&h_\tau(r)\le k,\\[2pt]
\displaystyle\frac{b(\tau-ar)+a\sqrt{\tau^2p+b^2r^2}}{\tau},
 &h_\tau(r)>k.
\end{cases}
\tag{27.14}
$$

Proof. Remove phases first. Averaging an attainable effect over the
phase of $e$ preserves $E$, preserves attainability and cannot increase
the residual norm. It kills the $\xi$–$e$ entry, so it suffices to use
diagonal $K$. Write $w=C_{ff}$. Order its active controls as $(D,J)$
so that

$$
(K_{ee},K_{ff})=\begin{cases}(D,J),&s>0,\\(J,D),&s<0,
\end{cases}
\qquad C_{ee}=aD+bJ,\quad w=bD+aJ.
\tag{27.15}
$$

At fixed $w$, minimizing $C_{ee}$ over $0\le D,J\le1$ gives precisely
$h_\tau(w)$. For $w\le a$, choose $(D,J)=(0,w/a)$; for $w\ge a$,
choose $((w-a)/b,1)$. For example, eliminating $J$ gives
$C_{ee}=bw/a+(\tau/a)D$, so the least feasible $D$ is respectively
zero or $(w-a)/b$. This also proves the lower bound at fixed $w$.

Put $A=C_{\xi\xi}-p$ and $d_0=w-r$. The residual on $(\xi,f)$ has
norm

$$
\frac{|A+d_0|+\sqrt{(A-d_0)^2+4pr}}2
 \ \ge\ \sqrt{pr+d_0^2},
\tag{27.16}
$$

with equality at $A=-d_0$, that is $C_{\xi\xi}=1-w\in[0,1]$.
To see minimality, the square-root function of $A$ is 1-Lipschitz,
so its decrease away from $A=-d_0$ is at most $|A+d_0|$.
Thus both independent diagonal choices attain the exact reduction

$$
\eta_n(E)=\min_{0\le w\le1}
 \max\{h_\tau(w),\sqrt{pr+(w-r)^2}\}.
\tag{27.17}
$$

Values $w>r$ cannot improve the objective, since both entries are
nondecreasing there. If $h_\tau(r)\le k$, choose $w=r$ and obtain
the floor. Otherwise $r>a$: for $r\le a$,
$k^2-(br/a)^2=r(1-r-b^2r/a^2)\ge rb\tau/a\ge0$.
At $w=a$ the second entry is at least the first $h_\tau(a)=b$, since
$pr+(a-r)^2-b^2=\tau p\ge0$. At $w=r$ the inequality is reversed.
The first entry increases strictly and the second decreases on $[a,r]$,
so there is exactly one crossing $w$ in $[a,r)$, and it minimizes
(27.17). At the crossing $t=h_\tau(w)$ and $w=(bt+\tau)/a$.
Squaring $t^2=pr+(w-r)^2$ yields

$$
\tau t^2+2b(ar-\tau)t+2a\tau r-\tau^2-a^2r=0.
\tag{27.18}
$$

Its constant coefficient is negative: it is
$-\tau^2+a(2\tau-a)r$, whose values at $r=0,1$ are
$-\tau^2,-b^2$, respectively. Hence there is a unique positive root.
Its discriminant after dividing by four is
$a^2(\tau^2p+b^2r^2)$, giving exactly the second line of (27.14).
The crossing argument identifies this root with the admissible $t$;
no extraneous squared root is used.

In either branch the attaining $K$ is diagonal: take
$K_{\xi\xi}=1-w$ and the controls in (27.15) minimizing $C_{ee}$.
Take $w=r$ in the floor branch and $w=(bt+\tau)/a$ otherwise.
Together with $B=U_0KU_0^\dagger$ and (27.5), this specifies a
terminal CPTP decoder, including $r=0$ and $r=1$.

For a matching all-input dual in the floor branch use
$Y=(|\xi\rangle\langle f|+|f\rangle\langle\xi|)/2$.
Its trace norm is one, $F^n(Y)=0$ and $\operatorname{Tr}(YE)=k$.
In the crossing branch put $\Delta=r-w\ge0$ and

$$
\begin{gathered}
\mu=\frac{at}{at+b\Delta},\qquad
\nu=\frac{b\Delta}{at+b\Delta},\qquad
Y_0\big|_{(\xi,f)}=
 \begin{pmatrix}0&k/(2t)\\k/(2t)&\Delta/t\end{pmatrix},\\
Y_0e=0,\qquad Y=\mu Y_0-\nu|e\rangle\langle e|.
\end{gathered}
\tag{27.19}
$$

Here $t>0$ and $at+b\Delta>0$. Since $t^2=k^2+\Delta^2$,
$\|Y_0\|_1=1$, also when $k=0$; the orthogonal $e$ block gives
$\|Y\|_1=\mu+\nu=1$. To evaluate the support in the actual output
coordinates, use (27.7). Order the physical active basis as
$(U_0e,U_0f)$ if $s>0$ and $(U_0f,U_0e)$ if $s<0$.
These are exactly the coordinates whose diagonal entries in $B$ are
$(D,J)$. In that order $F^n(Y)$ has coefficients

$$
-\nu a+\mu b\Delta/t=0,\qquad
-\nu b+\mu a\Delta/t=\frac{\mu\Delta\tau}{at}\ge0,
\tag{27.20}
$$

and zero on $\xi$. Thus the chosen $J=1$ effect maximizes its support
over the entire qutrit effect interval, not merely over diagonal effects.
On $(\xi,f)$ the residual $E-C$ is
$\left(\begin{smallmatrix}-\Delta&k\\k&\Delta\end{smallmatrix}\right)$,
and its $e$ entry is $-t$. Therefore
$\operatorname{Tr}(Y_0(E-C))=(k^2+\Delta^2)/t=t$ and
$\operatorname{Tr}(Y(E-C))=\mu t+\nu t=t$.
Support attainment makes this exactly the lower expression in (27.4).
Proposition 27.2 transfers both certificates to every complex phase.
The endpoint $r=0$ is in the floor branch and the endpoint $r=1$ has
$w=a$, $\Delta=t=b$ in the crossing branch. The case $n=1$ is (27.8),
not (27.13), whose second denominator would vanish. $\square$

### 27.5. Orientation, boundary illustrations and finite-horizon limits

**Corollary 27.6 (Strict orientation dependence).** For every finite
$n\ge1$ the two tasks with $v=e$ and $v=(e+f)/\sqrt2$ both have $p=0$,
but respectively have errors

$$
\frac{1-\tau}{2},\qquad \frac12.
\tag{27.21}
$$

Their difference $\tau/2$ is strictly positive. At $n=3$ the values
are $3/8$ and $1/2$. Thus $p$ alone is insufficient at every positive
finite horizon. At $n=1$, $r$ alone suffices by (27.8); at every
$n\ge2$, $r$ alone is insufficient, since $v=\xi$ and $v=e$ both
have $r=0$ but errors zero and $(1-\tau)/2>0$.

Proof. Theorem 27.4 gives (27.21). Explicit attaining controls are
$\operatorname{diag}(0,(1+\operatorname{sgn}s)/2,
(1-\operatorname{sgn}s)/2)$ and $\operatorname{diag}(0,1/2,1/2)$.
Matching witnesses are $(|e\rangle\langle e|-|f\rangle\langle f|)/2$
and $(|e\rangle\langle f|+|f\rangle\langle e|)/2$.
Their task traces are $1/2$ and $1/2$; their propagated positive
traces are $\tau/2$ and zero. The exact $\xi$ task is the conserved
$P$ task of [PA27, Theorem 86.2][PA27], also (26.19). $\square$

At $n=2$, Theorem 27.5 has $a=3/4$, $b=1/4$ and simplifies to

$$
\eta_2(E)\big|_{q=0}=\begin{cases}
\sqrt{r(1-r)},&0\le r\le4/5,\\
1-3r/4,&4/5\le r\le1.
\end{cases}
\tag{27.22}
$$

Indeed $\sqrt{\tau^2p+b^2r^2}=(2-r)/4$; on $r\ge3/4$ the
floor inequality is $3r-2\le\sqrt{r(1-r)}$, equivalent there to
$r\le4/5$. The two values at $4/5$ are both $2/5$.
Pure $e$ and pure $f$ have error $(1-\tau)/2$ for every $n\ge1$.
For $n\ge2$ the only zero-error rank-one task is $P$. One can also
see the remaining $r=0,q>0$ obstruction directly: $C=E$ in (27.6)
would require $K_{ff}=-\beta q/s<0$ for $s>0$, or
$K_{ee}=\alpha q/s<0$ for $s<0$. The floor excludes $0<r<1$ and
pure $f$ has positive error. This recovers the zero-error boundary
of (26.19); it does not quantify the general $r=0,pq>0$ error.

The boundary formulas also give the pointwise limits

$$
\lim_{n\to\infty}\eta_n(E)=\begin{cases}
1/2,&p=0,\\
\sqrt{r(1-r)},&q=0,\ 0\le r\le1/2,\\
1/2,&q=0,\ 1/2\le r\le1.
\end{cases}
\tag{27.23}
$$

For $p=0$, use $4qr+(q-r)^2=1$ in (27.10). For $q=0$,
$h_\tau(w)\to w$ uniformly on $[0,1]$ as $\tau\to0$, since its
two differences from $w$ are $-\tau w/a$ and
$-\tau(1-w)/b$. Thus the minima in (27.17) converge to the minimum
of $\max\{w,\sqrt{r(1-r)+(w-r)^2}\}$.
If $r\le1/2$, $w=r$ attains the lower floor, since $r\le k$.
If $r\ge1/2$, $w=1/2$ gives $1/2$; $w\ge1/2$ has first entry
at least $1/2$, and $w\le1/2$ has second entry at least $1/2$.
This proves (27.23) without substituting $s=0$ into a finite-horizon
inverse. The separation (27.21) tends to zero while remaining strict
at every finite positive horizon.

### 27.6. A scalar criterion for attaining the floor

**Theorem 27.7 (Necessary and sufficient floor region).** Fix any
finite $n\ge1$ and $0<r<1$. Put $m=1-r$ and $k=\sqrt{rm}$.
Then $\eta_n(E)=k$ if and only if some real $\lambda\in[0,k]$ makes

$$
\begin{gathered}
X=p+\lambda q/m,\qquad A=q+\lambda p/m,\qquad
Z=\frac{\sqrt{pq}(1-\lambda/m)}s,\\
Y_c=\frac{\alpha A-\beta r}s,\qquad
D_c=\frac{\alpha r-\beta A}s,\\
0\le X,Y_c,D_c\le1,\qquad
Z^2\le XY_c,\qquad Z^2\le(1-X)(1-Y_c).
\end{gathered}
\tag{27.24}
$$

In that case, after phase removal an attaining effect is
$K=\left(\begin{smallmatrix}X&Z&0\\Z&Y_c&0\\0&0&D_c\end{smallmatrix}\right)$.
If (27.24) is infeasible, then $\eta_n(E)>k$.

Proof. Remove phases and write $u=(\sqrt p,\sqrt q)^{\mathsf T}/\sqrt m$.
Every attainable $C$ has the form $H\oplus d$. For $R=C-E$,
$Rf=-k u+(d-r)f$, so $\|R\|\le k$ forces $d=r$.
Then $Ru=(H-mI_2)u-kf$ forces $Hu=mu$. Hermiticity gives

$$
H=m|u\rangle\langle u|+\lambda|u_\perp\rangle\langle u_\perp|,
\qquad u_\perp=(-\sqrt q,\sqrt p)^{\mathsf T}/\sqrt m.
\tag{27.25}
$$

Effect positivity gives $\lambda\ge0$; the residual on $u_\perp$
gives $\lambda\le k$. Its entries are $X,A,sZ$ in (27.24).
Inverting the two population equations of $G_s$, whose determinant
is $s\ne0$, gives exactly $Y_c,D_c$ there. The scalar bounds and
two determinants in (27.24) are precisely $0\le K_2\le I_2$ and
$0\le D_c\le1$. Thus they are necessary. Conversely they make $K$
an effect with image (27.25) direct-summed with $r$. The residual
has eigenvalues $k,-k,\lambda$, up to overall sign; its norm is
$k$. The universal witness (27.9) gives the matching lower bound.
Compact attainment in (27.4) makes failure of the criterion imply
strict inequality, rather than an unattained infimum equal to $k$.

In particular $r=1/2$ gives $\eta_n(E)=1/2$ for every $p,q$ and
every positive horizon: $B=K=I_3/2$ attains that error. In (27.24)
this is $\lambda=m=k=1/2$. The criterion determines equality with
the floor; it is not an optimum formula outside that region.
$\square$

### 27.7. Rank-two tasks and the remaining coupled constraints

**Proposition 27.8 (Complementary sharp task).** For every finite
$n\ge0$ and every projection $E$,

$$
\eta_n(I_3-E)=\eta_n(E).
\tag{27.26}
$$

For nontrivial $E$ this includes the explicit rank-two task associated
to each rank-one task above. Indeed $(F^n)^\dagger$ is unital, so
the bijection $B\mapsto I_3-B$ negates the residual in (27.4).
In (27.5) exchange $\sigma_1,\sigma_0$ along with the two effects;
the output states then lie in the range and kernel of $I_3-E$,
respectively. This gives an attaining complementary decoder. The
trivial tasks $0,I_3$ both have zero error. This is the reused unital
complement argument applied to the present optima.

**Proposition 27.9 (Exact structural feasibility for the remaining error).**
Fix finite $n\ge1$, $0<r<1$ and $\varepsilon\in[k,1/2]$.
After removing phases put $u=(\sqrt p,\sqrt q)^{\mathsf T}$,
now unnormalized. Then $\eta_n(E)\le\varepsilon$ if and only if
there exist a real symmetric $2\times2$ matrix $H$ and a real
output population $d$ satisfying all of

$$
\begin{gathered}
|d-r|\le\sqrt{\varepsilon^2-k^2},\\
\frac{\varepsilon+d}{\varepsilon+d-r}uu^{\mathsf T}
 -\varepsilon I_2
 \ \le H\le\ \varepsilon I_2+
 \frac{\varepsilon-d}{\varepsilon+r-d}uu^{\mathsf T},\\
0\le K_2(H,d):=
\begin{pmatrix}
H_{00}&H_{01}/s\\
H_{01}/s&(\alpha H_{11}-\beta d)/s
\end{pmatrix}\le I_2,\qquad
0\le D_c(H,d):=\frac{\alpha d-\beta H_{11}}s\le1.
\end{gathered}
\tag{27.27}
$$

At $r=0$, replace the first two lines of (27.27) by

$$
\|H-uu^{\mathsf T}\|_{\rm op}\le\varepsilon,\qquad
0\le d\le\varepsilon,
\tag{27.28}
$$

and keep the same inverse-effect constraints. This boundary version is
valid for $\varepsilon\in[0,1/2]$. No Schur fractions are used at $r=0$.

Proof. The choice $B=I_3/2$ gives the universal upper bound $1/2$,
and (27.8) gives the lower floor. After phase removal,
averaging an attainable $C$ with its entrywise complex conjugate
preserves its effect constraints and cannot increase its distance to
the real target. Thus real $H$ suffices. Set $C=H\oplus d$ and
$R=C-E$. Its action on $f$ gives
$\|Rf\|^2=k^2+(d-r)^2$, proving the first line of (27.27).
Since $k>0$, this line ensures
$|d-r|\le\sqrt{\varepsilon^2-k^2}<\varepsilon$; hence both
$\varepsilon+d-r$ and $\varepsilon+r-d$ are strictly positive.
The inequalities $\varepsilon I_3+R\ge0$ and
$\varepsilon I_3-R\ge0$ have these two scalar bottom entries.
Their Schur complements are exactly the two matrix bounds on $H$
in (27.27). Conversely those bounds imply both positive matrices,
and hence $\|R\|_{\rm op}\le\varepsilon$. Inverting $G_s$ gives
the displayed $K_2(H,d),D_c(H,d)$; their effect constraints are
equivalent to attainability of $C$. They also give the explicit
effect $K=K_2(H,d)\oplus D_c(H,d)$ and decoder (27.5) whenever
a feasible tuple is specified.

If $r=0$, the residual is the block diagonal matrix
$(H-uu^{\mathsf T})\oplus d$. Its norm bound is (27.28), because
attainability already gives $d\ge0$. This proves the boundary form
without divisions that can vanish. These equivalences are structural
feasibility statements; they do not solve the coupled optimization.
$\square$

### 27.8. Sources and the unresolved quantitative target

**Definition 27.10 (Reused interfaces and remaining domains).** The
actual all-angle branches, conditional fairness and chronological law
are Theorem 2.2 and Definition 11.1 of this volume. Section 26 supplies
the exact sharp-algebra classification for all full-support laws;
the quantitative values here concern only its actual fair independent
law. [Five-window quantum memory, §§18–20][QM27] supplies the exact
$P$ sector, restricted polynomial, iteration, EB limit and all-finite
NPT statement. Those structural channel results are reused. The
general task-effect and measure-and-prepare interface is already
[Purity arithmetic, Definitions 86.1/86.3 and Theorem 86.2][PA27]
and [the observable-correction note][NOTE26]. Its Bény–Kempf–Kribs
correspondence is the one stated in §26; the norm and support-function
calculations in (27.4) are elementary general tools, not additional
observable-correction theorems. In particular the conditional errors
$1/4$ and $3/16$ in [PA27, Theorem 86.2][PA27] belong to two different
record-conditioned channels and tasks. They are not errors of $F^n$.

Relative to these suppliers, the additional deductions are the entire
orientation-sensitive effect image, all-input one-step value, the two
boundary optima with matching certificates, strict same-$p$ separation,
and the scalar equality region, with the explicit residual coupling.
Their proofs are ordinary finite-dimensional mathematics. This bounded
source correspondence makes no exhaustive literature-novelty or priority
claim.

The full quantitative target remains to determine, for every complex
unit $v$ and every finite horizon, an analytic or piecewise value, or
a sufficiently explicit fixed-degree algebraic value, together with an
attaining effect and matching lower certificate. For $n\ge2$, the family
$r=0,pq>0$ remains unsolved quantitatively, as does the interior
$p,q,r>0$ outside (27.24). Strict positivity, a scalar floor test and
the fixed-dimensional Schur conditions (27.27)–(27.28) do not discharge
those optimization problems. Complementation supplies the corresponding
rank-two tasks, but separate task decoders do not give one common
decoder for several prescribed tasks. The long-word and retained-memory
research targets, critical norm estimates and uniform unbounded-horizon
recovery remain separate and unresolved by this chapter. No physical
realization or kernel certification is inferred from these ordinary
mathematical results.

[QM27]: AURIC_FIB_FIVE_WINDOW_QUANTUM_MEMORY.md
[PA27]: AURIC_FIB_ACTUAL_WORD_PURITY_ARITHMETIC.md

## 追加锚（本行以下为增补区）
