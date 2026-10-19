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
