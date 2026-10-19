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
